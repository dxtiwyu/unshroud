"""Neutral scoring of unshroud and Triton on the GAMBA sets: one node counter (distinct subterms, no rewriting except
-const / ~const folded) for the ground truth and both engines' outputs; unshroud outputs re-checked on random inputs here.
usage: python -I rescore.py [--data DIR] [--res DIR] [sets...]   (results: DIR/x_<set>.jsonl from unshroud_mbaset --expr, DIR/t_<set>.jsonl from tgamba.py)"""
import sys, json, os
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "tgamba.py")).read()
argv = sys.argv; sys.argv = ["x", "none"]
exec(src[:src.index("ctx = TritonContext")])
exec(src[src.index("def rnd(rs):"):src.index("modes = a.modes")])
sys.argv = argv
DATA = RES = os.path.dirname(os.path.abspath(__file__)); DATA = os.path.join(DATA, "data")
args = sys.argv[1:]
while args and args[0] in ("--data", "--res"):
    if args[0] == "--data": DATA = args[1]
    else: RES = args[1]
    args = args[2:]
SETS = args or ["syntia", "qsynth_ea", "mba_obf_linear", "mba_obf_nonlinear", "mba_flatten", "neureduce", "loki_tiny"]
def fold(t):
    if t[0] in ("c", "v"): return t
    ch = tuple(fold(c) for c in t[1:])
    if t[0] == "neg" and ch[0][0] == "c": return ("c", -ch[0][1] & M)
    if t[0] == "not" and ch[0][0] == "c": return ("c", ~ch[0][1] & M)
    return (t[0],) + ch
def nsize(s):
    p = P(s); t = p.parse()
    return (size(fold(t)), fold(t)) if p.ok else (None, None)
def load(f):
    out = {}
    if os.path.exists(f):
        for l in open(f):
            j = json.loads(l); out[j["line"]] = j
    return out
print("%-18s %6s | %-34s | %-34s | %s" % ("set", "n", "unshroud: solved / zero / mean size / time", "Triton: solved / zero / mean size / time", "per line: unshroud smaller / equal / Triton smaller"))
tot = dict(n=0, xs=0, ts=0, xz=0, tz=0, xw=0, ts_fail=0)
for s in SETS:
    lines = {}
    for i, l in enumerate(open(os.path.join(DATA, "%s.txt" % s)), 1):
        if l.strip() and l[0] != "#": lines[i] = l.strip()
    X, T = load(os.path.join(RES, "x_%s.jsonl" % s)), load(os.path.join(RES, "t_%s.jsonl" % s))
    common = sorted(set(X) & set(T))
    if not common: print("%-18s no common lines yet (unshroud %d, Triton %d)" % (s, len(X), len(T))); continue
    xs = ts = xz = tz = xw = xbad = tfail = 0; xsz = tsz = 0; xt = tt = 0.0; better = [0, 0, 0]
    for n in common:
        f = lines[n].split(","); g = P(f[1].strip()).parse(); gs = size(fold(g))
        names = sorted(vars_of(P(f[0]).parse(), set()) | vars_of(g, set()))
        x, t = X[n], T[n]
        xn, xtree = nsize(x.get("r", ""))
        if xn is None: xbad += 1; xn = x["in"] * 10 ** 6
        else:
            if x["wrong"] or not same(xtree, g, names, 0x777 + n): xw += 1; xn = 10 ** 9
        if "r" in t: tn = nsize(t["r"])[0]
        else: tfail += 1; tn = size(fold(P(f[0]).parse()))
        if xn <= gs: xs += 1
        if tn <= gs: ts += 1
        xz += x["zero"]; tz += t.get("zero", 0); xsz += min(xn, 10 ** 4); tsz += tn; xt += x["t"] + x["tz"]; tt += t.get("t", 10.0) + (10.0 if "fallback" in t else 0.0)
        better[0 if xn < tn else 1 if xn == tn else 2] += 1
    k = len(common)
    print("%-18s %6d | %5.1f%% / %5.1f%% / %6.1f / %7.1fs | %5.1f%% / %5.1f%% / %6.1f / %7.1fs | %d / %d / %d   (truth mean %.1f; unshroud unparsed %d wrong %d; Triton timeouts %d)" % (
        s, k, 100.0 * xs / k, 100.0 * xz / k, xsz / k, xt, 100.0 * ts / k, 100.0 * tz / k, tsz / k, tt, *better,
        sum(size(fold(P(lines[n].split(",")[1].strip()).parse())) for n in common) / k, xbad, xw, tfail + sum(1 for n in common if "fallback" in T[n])))
