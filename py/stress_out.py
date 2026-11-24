"""Adversarial check of unshroud's simplified outputs against the suite's ground truth.
For every returned path: thousands of inputs (sparse/dense/small/boundary values, equal or negated variables, bit flips of the
path's own inputs); those which follow the same path (unshroud's conditions) must give the truth's output there.
usage: python -I stress_out.py <suite.json> <bench_result.json> [N per path] [jobs]"""
import json, os, random, sys
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
M64 = (1 << 64) - 1
BOUND = [0, 1, 2, 3, M64, M64 - 1, 1 << 63, (1 << 63) - 1, (1 << 63) + 1, 1 << 32, (1 << 32) - 1, 0xffffffff00000000, 0x80000000, 0x7fffffff, 0xff, 0x100, 0xffff, 0x10000, 0x5555555555555555, 0xaaaaaaaaaaaaaaaa]

def gen(rng, base, nargs):
    v = [0, 0, 0, 0]
    for k in range(nargs):
        m = rng.randrange(9)
        if m == 0: v[k] = rng.getrandbits(64)
        elif m == 1: v[k] = rng.randrange(256)
        elif m == 2: v[k] = sum(1 << rng.randrange(64) for _ in range(rng.randrange(1, 4))) & M64
        elif m == 3: v[k] = M64 ^ (sum(1 << rng.randrange(64) for _ in range(rng.randrange(1, 4))) & M64)
        elif m == 4: v[k] = rng.choice(BOUND)
        elif m == 5: v[k] = (M64 + 1 - rng.randrange(1, 256)) & M64
        elif m == 6: v[k] = base[k] ^ (1 << rng.randrange(64))
        elif m == 7: v[k] = base[k] ^ (1 << rng.randrange(64)) ^ (1 << rng.randrange(64))
        else: v[k] = (base[k] + rng.randrange(-4, 5)) & M64
    if nargs > 1 and rng.random() < 0.3:   # relations between variables
        i, j = rng.sample(range(nargs), 2)
        r = rng.randrange(4)
        v[i] = v[j] if r == 0 else (-v[j]) & M64 if r == 1 else (~v[j]) & M64 if r == 2 else (v[j] + 1) & M64
    return v

def work(item):
    import unshroudpy
    sys.path.insert(0, item["gen1"]); sys.path.insert(1, item["gen2"])
    import truth
    tp = [(truth.compile(p["cond"]), truth.compile(p["out"])) for p in item["truth"]]
    ns = {"op": unshroudpy.op}; exec(item["py"], ns); fn = ns["f"]
    rng = random.Random(item["seed"])
    base = (list(item["inputs"]) + [0, 0, 0, 0])[:4]
    followed = 0; bad = None
    for _ in range(item["n"]):
        t = gen(rng, base, item["nargs"])
        vals = fn(*t)
        if any(c != 1 for c in vals[1:]): continue
        followed += 1
        hits = [j for j, (c, o) in enumerate(tp) if c(*t)]
        if len(hits) != 1 or tp[hits[0]][1](*t) != vals[0]:
            bad = [hex(x) for x in t]; break
    return item["name"], item["k"], followed, bad, item.get("exact"), item.get("check")

if __name__ == "__main__":
    suite, res = sys.argv[1], sys.argv[2]
    N = int(sys.argv[3]) if len(sys.argv) > 3 else 5000
    jobs = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    S = json.load(open(suite)); R = json.load(open(res))
    sp = os.path.abspath(suite)
    gen1 = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(sp))), "gen"); gen2 = os.path.join(HERE, "..", "bench", "gen")
    byrva = {int(f["rva"], 16): f for f in S["functions"]}
    items = []
    for rva, r in R["raw"].items():
        f = byrva.get(int(rva, 16))
        if not f: continue
        for k, p in enumerate(r["paths"]):
            if p["stop"] != "return" or "py" not in p: continue
            items.append({"name": f["name"], "k": k, "nargs": f["nargs"], "truth": f["paths"], "py": p["py"], "inputs": [int(v, 16) for v in p["inputs"]],
                          "n": N, "seed": hash((f["name"], k)) & 0xffffffff, "gen1": gen1, "gen2": gen2, "exact": p.get("out_exact"), "check": p.get("out_check")})
    with Pool(jobs) as pool: out = pool.map(work, items, chunksize=4)
    bad = [o for o in out if o[3]]
    fol = sorted(o[2] for o in out)
    print("%s: %d paths, %d inputs each; inputs on the path: min %d median %d; WRONG %d" % (S["suite"], len(out), N, fol[0] if fol else 0, fol[len(fol) // 2] if fol else 0, len(bad)))
    for b in bad[:20]: print("   WRONG", b)
