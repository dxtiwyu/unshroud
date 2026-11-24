"""How the explored paths end, over many functions: which instructions are unsupported, which faults.
usage: python -I scan_stops.py <pe> <rva,...|@file> [--time S] [--jobs N]"""
import collections, json, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
pe, spec = sys.argv[1], sys.argv[2]
tm = sys.argv[sys.argv.index("--time") + 1] if "--time" in sys.argv else "3"
jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 2
rvas = (open(spec[1:]).read() if spec.startswith("@") else spec).replace("\n", ",").split(",")
rvas = [r.strip() for r in rvas if r.strip()]
exe = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "build", "unshroud_explore.exe")
def batch(rs):
    p = subprocess.run([exe, pe, "--time", tm] + [r + ":4" for r in rs], capture_output=True, text=True, timeout=600)
    return [json.loads(l) for l in p.stdout.splitlines() if l.startswith("{")], len(rs)
stops = collections.Counter(); infos = collections.Counter(); where = {}
got = 0
with ThreadPoolExecutor(jobs) as pool:
    for res, n in pool.map(batch, [rvas[i:i + 12] for i in range(0, len(rvas), 12)]):
        got += len(res)
        for r in res:
            for p in r.get("paths", []):
                stops[p["stop"]] += 1
                if p["stop"] not in ("return",):
                    k = p["stop"] + ": " + p["info"][:60]; infos[k] += 1; where.setdefault(k, (r["rva"], p["pc"]))
print("%d of %d functions answered" % (got, len(rvas)))
print("path ends:", dict(stops.most_common()))
for k, v in infos.most_common(25): print("  %5d  %-70s e.g. %s at %s" % (v, k, where[k][0], where[k][1]))
