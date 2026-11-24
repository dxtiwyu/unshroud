"""Runs unshroud on a bench suite and scores it against the ground truth.

usage: python -I bench_unshroud.py <suite.json> [--time S] [--jobs N] [--out FILE] [--only NAME,...] [--limit N] [--extra ARGS]

Per function: coverage (feasible truth paths reached by the inputs unshroud generated), resolution (each reached path's output,
simplified, is no bigger than the truth's: max(1.5 * truth + 2)), correctness (each path's output and conditions evaluated in
Python agree with the truth on the path's own inputs and on random inputs which follow the same path), opaque predicates
(branch sides proven impossible, dead-arm values never produced).
"""
import argparse, json, os, random, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import unshroudpy  # noqa: E402

ap = argparse.ArgumentParser()
ap.add_argument("suite")
ap.add_argument("--time", type=float, default=10.0)
ap.add_argument("--jobs", type=int, default=8)
ap.add_argument("--out", default="")
ap.add_argument("--only", default="")
ap.add_argument("--limit", type=int, default=0)
ap.add_argument("--extra", default="")
ap.add_argument("--exe", default=os.path.join(HERE, "..", "build", "unshroud_explore.exe"))
a = ap.parse_args()

suite_path = os.path.abspath(a.suite)
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(suite_path))), "gen"))
sys.path.insert(1, os.path.join(HERE, "..", "bench", "gen"))
import truth  # noqa: E402

S = json.load(open(suite_path))
dll = os.path.join(os.path.dirname(suite_path), S["dll"])
funcs = S["functions"]
if a.only: funcs = [f for f in funcs if f["name"] in a.only.split(",")]
if a.limit: funcs = funcs[:a.limit]
M64 = (1 << 64) - 1

def run_batch(batch):
    cmd = [a.exe, dll, "--time", str(a.time), "--py"] + a.extra.split() + ["%s:%d" % (f["rva"][2:], f["nargs"]) for f in batch]
    t0 = time.perf_counter()
    res = {}
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=a.time * len(batch) * 3 + 120)
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        for line in out.splitlines():
            if line.startswith("{"):
                r = json.loads(line); res[int(r["rva"], 16)] = r
        return res, "batch timed out: " + ",".join(f["name"] for f in batch), time.perf_counter() - t0
    for line in p.stdout.splitlines():
        if line.startswith("{"):
            r = json.loads(line); res[int(r["rva"], 16)] = r
    return res, p.stderr, time.perf_counter() - t0

# one function per process call keeps a crash local; batches of a few amortize the image load
batches = [funcs[i:i + 4] for i in range(0, len(funcs), 4)]
results = {}
t0 = time.perf_counter()
with ThreadPoolExecutor(a.jobs) as pool:
    for res, err, dt in pool.map(run_batch, batches):
        results.update(res)
        if err.strip(): print("stderr:", err.strip()[:300])
wall = time.perf_counter() - t0

rng = random.Random(7)
def pad(v): return (list(v) + [0, 0, 0, 0])[:4]
rows = []
for f in funcs:
    rva = int(f["rva"], 16)
    r = results.get(rva)
    tp = [((lambda g: (lambda t: g(*t)))(truth.compile(p["cond"])), (lambda g: (lambda t: g(*t)))(truth.compile(p["out"])), p) for p in f["paths"]]
    row = {"name": f["name"], "category": f.get("category", ""), "paths": len(tp), "ok": r is not None}
    if r is None:
        row.update(covered=0, resolved=0, wrong=0, time=None, opaque=len(f.get("opaque", [])), proven=0, dead=0); rows.append(row); continue
    covered = set(); resolved = set(); wrong = 0; dead = 0
    dead_vals = set(int(o["dead_out"], 0) for o in f.get("opaque", []) if o.get("dead_out"))
    for p in r["paths"]:
        if p["stop"] != "return": continue
        args = pad([int(v, 16) for v in p["inputs"]])
        hit = [i for i, (c, o, _) in enumerate(tp) if c(args)]
        if len(hit) != 1: wrong += 1; continue
        i = hit[0]; covered.add(i)
        want = tp[i][1](args)
        if int(p["rax"], 16) != want: wrong += 1; continue
        if int(p["rax"], 16) in dead_vals: dead += 1
        # the simplified output and the path's conditions, in Python
        ns = {"op": unshroudpy.op}
        exec(p["py"], ns)
        fn = ns["f"]
        vals = fn(*args)
        if vals[0] != want or any(v != 1 for v in vals[1:]): wrong += 1; continue
        # random inputs which follow the same path must give the truth's output
        bad = False
        for _ in range(60):
            t = pad([rng.getrandbits(64) if k < f["nargs"] else 0 for k in range(4)])
            if rng.random() < 0.5:   # near the path's own inputs
                t = pad([(args[k] ^ (1 << rng.randrange(64))) if k < f["nargs"] else 0 for k in range(4)])
            v = fn(*t)
            if all(c == 1 for c in v[1:]):
                hits = [j for j, (c, o, _) in enumerate(tp) if c(t)]
                if len(hits) != 1 or tp[hits[0]][1](t) != v[0]: bad = True; break
        if bad: wrong += 1; continue
        tn = truth.nodes(tp[i][2]["out"])
        if p["out_nodes"] <= 1.5 * tn + 2: resolved.add(i)
    nop = len(f.get("opaque", []))
    row.update(covered=len(covered), resolved=len(resolved), wrong=wrong, time=r["time"], opaque=nop,
               proven=min(nop, len(r["refuted"])) if not dead else 0, dead=dead, undecided=len(r["undecided"]),
               runs=r["runs"], queries=r["queries"], stages=r["stages"], ins=r["ins"])
    rows.append(row)

def summary(rs, label):
    n = len(rs)
    if not n: return
    full_cov = sum(1 for x in rs if x["ok"] and x["covered"] == x["paths"])
    full_res = sum(1 for x in rs if x["ok"] and x["resolved"] == x["paths"])
    wrong = sum(x["wrong"] for x in rs)
    op = sum(x["opaque"] for x in rs); pr = sum(x["proven"] for x in rs)
    ts = sorted(x["time"] for x in rs if x["time"] is not None)
    med = ts[len(ts) // 2] if ts else 0
    print("%-12s functions %4d  all paths reached %5.1f%%  all outputs resolved %5.1f%%  opaque proven %d/%d  wrong %d  time median %.3fs total %.1fs" % (
        label, n, 100.0 * full_cov / n, 100.0 * full_res / n, pr, op, wrong, med, sum(ts)))

print("suite %s: %d functions, wall %.1fs" % (S["suite"], len(rows), wall))
summary(rows, "all")
for cat in sorted(set(x["category"] for x in rows)):
    summary([x for x in rows if x["category"] == cat], cat)
bad = [x for x in rows if not x["ok"] or x["covered"] < x["paths"] or x["resolved"] < x["paths"] or x["wrong"]]
for x in bad[:15]:
    print("  %-14s cov %d/%d res %d/%d wrong %d time %s stages %s" % (x["name"], x.get("covered", 0), x["paths"], x.get("resolved", 0), x["paths"], x.get("wrong", 0), x.get("time"), x.get("stages")))
if a.out:
    json.dump({"suite": S["suite"], "wall": wall, "rows": rows, "raw": {hex(k): v for k, v in results.items()}}, open(a.out, "w"))
