"""Triton on the GAMBA MBA sets, scored like unshroud_mbaset: per line expression,groundtruth.
usage: python -I tgamba.py <set.txt> [--limit N] [--skip N] [--step K] [--modes simp,llvm,synth,llvmsynth] [--jsonl F] [--triton DIR]"""
import sys, os, time, json, argparse, random
ap = argparse.ArgumentParser(); ap.add_argument("file"); ap.add_argument("--limit", type=int, default=10**9)
ap.add_argument("--skip", type=int, default=0); ap.add_argument("--step", type=int, default=1)
ap.add_argument("--modes", default="simp,llvm,synth,llvmsynth"); ap.add_argument("--jsonl"); ap.add_argument("--triton")
ap.add_argument("--nozero", action="store_true"); ap.add_argument("--worker", action="store_true")
ap.add_argument("--jobs", type=int, default=3); ap.add_argument("--timeout", type=float, default=10); ap.add_argument("--mem", type=int, default=2048)
a = ap.parse_args()
if a.triton: sys.path.insert(0, a.triton); os.add_dll_directory(a.triton)
from triton import TritonContext, ARCH, AST_NODE
M = (1 << 64) - 1

# ---- parser: same grammar and precedence as unshroud_mbaset (unary binds tightest; * ; + - ; << >> ; & ; ^ ; |)
class P:
    def __init__(s, t): s.t = t; s.i = 0; s.ok = True
    def ws(s):
        while s.i < len(s.t) and s.t[s.i] in " \t\r\n": s.i += 1
    def pk(s, k=0): return s.t[s.i + k] if s.i + k < len(s.t) else ""
    def atom(s):
        s.ws(); c = s.pk()
        if c == "(":
            s.i += 1; r = s.orE(); s.ws()
            if s.pk() == ")": s.i += 1
            else: s.ok = False
            return r
        if c == "~": s.i += 1; return ("not", s.atom())
        if c == "-": s.i += 1; return ("neg", s.atom())
        if c == "+": s.i += 1; return s.atom()
        if c.isdigit():
            j = s.i
            if s.t[j:j+2].lower() == "0x":
                j += 2
                while j < len(s.t) and s.t[j] in "0123456789abcdefABCDEF": j += 1
                v = int(s.t[s.i:j], 16)
            else:
                while j < len(s.t) and s.t[j].isdigit(): j += 1
                v = int(s.t[s.i:j])
            s.i = j; return ("c", v & M)
        if c.isalpha() or c == "_":
            j = s.i
            while j < len(s.t) and (s.t[j].isalnum() or s.t[j] == "_"): j += 1
            n = s.t[s.i:j]; s.i = j; return ("v", n)
        s.ok = False; s.i = len(s.t); return ("c", 0)
    def bin(s, sub, ops):
        r = sub()
        while True:
            s.ws(); hit = None
            for o in ops:
                if s.t.startswith(o, s.i) and not (o == "*" and s.pk(1) == "*"): hit = o; break
            if not hit: return r
            s.i += len(hit); r = (hit, r, sub())
    def mulE(s): return s.bin(s.atom, ["*"])
    def addE(s): return s.bin(s.mulE, ["+", "-"])
    def shE(s): return s.bin(s.addE, ["<<", ">>"])
    def andE(s): return s.bin(s.shE, ["&"])
    def xorE(s): return s.bin(s.andE, ["^"])
    def orE(s): return s.bin(s.xorE, ["|"])
    def parse(s):
        r = s.orE(); s.ws()
        if s.i != len(s.t): s.ok = False
        return r

def ev(t, env):
    k = t[0]
    if k == "c": return t[1]
    if k == "v": return env[t[1]]
    if k == "not": return ~ev(t[1], env) & M
    if k == "neg": return -ev(t[1], env) & M
    x, y = ev(t[1], env), ev(t[2], env)
    if k == "+": return (x + y) & M
    if k == "-": return (x - y) & M
    if k == "*": return (x * y) & M
    if k == "&": return x & y
    if k == "|": return x | y
    if k == "^": return x ^ y
    if k == "<<": return (x << y) & M if y < 64 else 0
    if k == ">>": return x >> y if y < 64 else 0
    raise ValueError(k)

def size(t):
    """distinct subterms (hash-consed DAG count, leaves included), no rewriting"""
    seen = set()
    def go(u):
        if u in seen: return
        seen.add(u)
        for ch in u[1:]:
            if isinstance(ch, tuple): go(ch)
    go(t); return len(seen)

def vars_of(t, out):
    if t[0] == "v": out.add(t[1])
    else:
        for ch in t[1:]:
            if isinstance(ch, tuple): vars_of(ch, out)
    return out

ctx = TritonContext(ARCH.X86_64); ast = ctx.getAstContext()
SV = {}
def tvar(n):
    if n not in SV: SV[n] = ast.variable(ctx.newSymbolicVariable(64, n))
    return SV[n]
OPS = {"+": "bvadd", "-": "bvsub", "*": "bvmul", "&": "bvand", "|": "bvor", "^": "bvxor", "<<": "bvshl", ">>": "bvlshr"}
def to_t(t):
    k = t[0]
    if k == "c": return ast.bv(t[1], 64)
    if k == "v": return tvar(t[1])
    if k == "not": return ast.bvnot(to_t(t[1]))
    if k == "neg": return ast.bvneg(to_t(t[1]))
    return getattr(ast, OPS[k])(to_t(t[1]), to_t(t[2]))
class Unsup(Exception): pass
BACK = {AST_NODE.BVADD: "+", AST_NODE.BVSUB: "-", AST_NODE.BVMUL: "*", AST_NODE.BVAND: "&", AST_NODE.BVOR: "|",
        AST_NODE.BVXOR: "^", AST_NODE.BVSHL: "<<", AST_NODE.BVLSHR: ">>"}
NEGATED = {AST_NODE.BVXNOR: "^", AST_NODE.BVNOR: "|", AST_NODE.BVNAND: "&"}   # bvxnor / bvnor / bvnand (2 operands): ~(a op b)
def from_t(n, memo):
    h = n.getHash()
    if h in memo: return memo[h]
    ty = n.getType()
    if ty == AST_NODE.REFERENCE: r = from_t(n.getSymbolicExpression().getAst(), memo)
    elif ty == AST_NODE.BV: r = ("c", n.evaluate() & M)
    elif ty == AST_NODE.VARIABLE: r = ("v", n.getSymbolicVariable().getAlias())
    elif ty == AST_NODE.BVNOT: r = ("not", from_t(n.getChildren()[0], memo))
    elif ty == AST_NODE.BVNEG: r = ("neg", from_t(n.getChildren()[0], memo))
    elif ty in NEGATED:
        ch = [from_t(c, memo) for c in n.getChildren()]
        r = ch[0]
        for c in ch[1:]: r = (NEGATED[ty], r, c)
        r = ("not", r)
    elif ty in BACK:
        ch = [from_t(c, memo) for c in n.getChildren()]
        r = ch[0]
        for c in ch[1:]: r = (BACK[ty], r, c)
    else: raise Unsup(str(ty))
    if n.getBitvectorSize() != 64: raise Unsup("width")
    memo[h] = r; return r

def rnd(rs):
    rs[0] = (rs[0] + 0x9E3779B97F4A7C15) & M; z = rs[0]
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & M; z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & M; return z ^ (z >> 31)
def same(r, g, names, seed):
    rs = [seed]
    for _ in range(200):
        env = {}
        for n in names:
            x = rnd(rs); kind = rnd(rs) % 6
            env[n] = x & 0xff if kind == 0 else (~(x & 0xff)) & M if kind == 1 else 1 << (x & 63) if kind == 2 else x
        if ev(r, env) != ev(g, env): return False
    return True

modes = a.modes.split(",")
def run_modes(node):
    out = {}
    def put(m, f):
        t0 = time.perf_counter()
        try: res = f()
        except Exception as ex: res = None
        out[m] = (res, time.perf_counter() - t0)
    if "simp" in modes: put("simp", lambda: ctx.simplify(node))
    if "z3" in modes: put("z3", lambda: ctx.simplify(node, True, False))
    if "llvm" in modes or "llvmsynth" in modes: put("llvm", lambda: ctx.simplify(node, False, True))
    if "synth" in modes: put("synth", lambda: ctx.synthesize(node, True, True, False))
    if "llvmsynth" in modes and out.get("llvm", (None,))[0] is not None: put("llvmsynth", lambda: ctx.synthesize(out["llvm"][0], True, True, False))
    return out


def do(lineno, line):
    f = line.split(",")
    if len(f) < 2: return dict(line=lineno, bad=1)
    pe, pg = P(f[0]), P(f[1].strip()); e = pe.parse(); g = pg.parse()
    if not pe.ok or not pg.ok: return dict(line=lineno, bad=1)
    names = sorted(vars_of(e, set()) | vars_of(g, set()))
    nin, ngt = size(e), size(g)
    t0 = time.perf_counter(); res = run_modes(to_t(e)); dt = time.perf_counter() - t0
    best, bm, anywrong, unsup = e, "none", 0, 0
    for m, (r, _) in res.items():
        if r is None: continue
        try: tr = from_t(r, {})
        except Unsup: unsup += 1; continue
        if not same(tr, g, names, 0x1234 + lineno): anywrong = 1; continue
        if size(tr) < size(best): best, bm = tr, m
    nout = size(best)
    zero = 0
    if not a.nozero:
        for m, (r, _) in run_modes(to_t(("-", e, g))).items():
            if r is None: continue
            try:
                if from_t(r, {}) == ("c", 0): zero = 1
            except Unsup: pass
    return dict(line=lineno, i=nin, o=nout, gt=ngt, solved=int(nout <= ngt), zero=zero, wrong=anywrong, unsup=unsup, by=bm, t=round(dt, 5), r=show(best))

def show(t):
    k = t[0]
    if k == "c": return hex(t[1])
    if k == "v": return t[1]
    if k == "not": return "~" + show(t[1])
    if k == "neg": return "-" + show(t[1])
    return "(" + show(t[1]) + " " + k + " " + show(t[2]) + ")"

if a.worker:
    for l in sys.stdin:
        n, line = l.rstrip("\n").split("\t", 1)
        print(json.dumps(do(int(n), line)), flush=True)
    sys.exit(0)

import subprocess, threading, queue, psutil
work = []; seen = 0; lineno = 0
for line in open(a.file):
    lineno += 1
    if not line.strip() or line[0] == "#": continue
    seen += 1
    if seen <= a.skip or (seen - 1 - a.skip) % a.step: continue
    if len(work) >= a.limit: break
    work.append((lineno, line.strip()))
Q = queue.Queue()
for w in work: Q.put(w)
results = {}; lock = threading.Lock()
def spawn(modes=None):
    cmd = [sys.executable, "-I", os.path.abspath(__file__), a.file, "--worker", "--modes", modes or a.modes] + (["--triton", a.triton] if a.triton else []) + (["--nozero"] if a.nozero else [])
    return subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
def one(pr, n, line):
    """send a line, wait with the time and memory limits: (result or None, process still usable)"""
    pr.stdin.write("%d\t%s\n" % (n, line)); pr.stdin.flush()
    box = []
    th = threading.Thread(target=lambda: box.append(pr.stdout.readline())); th.start()
    t0 = time.time(); killed = None
    while th.is_alive():
        th.join(0.2)
        try: rss = psutil.Process(pr.pid).memory_info().rss
        except Exception: rss = 0
        if time.time() - t0 > a.timeout: killed = "timeout"
        elif rss > a.mem * 2**20: killed = "memory"
        if killed:
            pr.kill(); th.join(); break
    if killed or not box or not box[0].strip():
        try: pr.kill()
        except Exception: pass
        return dict(line=n, fail=killed or "crash"), False
    return json.loads(box[0]), True
def runner():
    pr = spawn()
    while True:
        try: n, line = Q.get_nowait()
        except queue.Empty: break
        r, alive = one(pr, n, line)
        if not alive:
            fb = spawn(FALLBACK)
            r2, ok2 = one(fb, n, line)
            if ok2: r2["fallback"] = r["fail"]; r = r2; fb.stdin.close(); fb.wait()
            pr = spawn()
        with lock: results[n] = r
    pr.stdin.close(); pr.wait()
FALLBACK = ",".join(m for m in a.modes.split(",") if m in ("simp", "llvm", "z3")) or "simp"
T0 = time.time()
ths = [threading.Thread(target=runner) for _ in range(a.jobs)]
for t in ths: t.start()
for t in ths: t.join()
wall = time.time() - T0
rows = [results[n] for n, _ in work]
jf = open(a.jsonl, "w") if a.jsonl else None
for r in rows:
    if jf: jf.write(json.dumps(r) + "\n")
nfb = sum(1 for r in rows if "fallback" in r)
ok = [r for r in rows if "i" in r]; fail = [r for r in rows if "fail" in r]; bad = [r for r in rows if "bad" in r]
n = max(1, len(rows) - len(bad))
win = {}
for r in ok:
    if r["solved"]: win[r["by"]] = win.get(r["by"], 0) + 1
print("%s: %d expressions  solved(size<=truth) %d (%.1f%%)  zero(e-gt=0) %d (%.1f%%)  wrong-candidates %d  unsupported %d  timeout/mem %d (of them without synth: %d)  parse errors %d  time %.1fs wall %.1fs  solved by %s" % (
    os.path.basename(a.file), n, sum(r["solved"] for r in ok), 100.0 * sum(r["solved"] for r in ok) / n, sum(r["zero"] for r in ok), 100.0 * sum(r["zero"] for r in ok) / n,
    sum(r["wrong"] for r in ok), sum(r["unsup"] for r in ok), len(fail) + nfb, nfb, len(bad), sum(r["t"] for r in ok), wall, win))
