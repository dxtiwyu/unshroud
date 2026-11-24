"""The exception tests (bench/exc) in unshroud against the native run of the same DLL: every result must be equal.
Then each test explored with symbolic arguments: the paths found.
usage: python -I exc_check.py <dll> [--no-native] [--explore S] [--build DIR] [--trace NAME]"""
import argparse, json, os, struct, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ap = argparse.ArgumentParser(); ap.add_argument("dll"); ap.add_argument("--no-native", action="store_true"); ap.add_argument("--explore", type=float, default=5.0)
ap.add_argument("--build", default=os.path.join(HERE, "..", "build")); ap.add_argument("--trace", default=""); ap.add_argument("--json", default="")
a = ap.parse_args()
sys.path.insert(0, a.build); os.add_dll_directory(os.path.abspath(a.build)); sys.path.insert(0, HERE)
import unshroud, exc_native
unshroud.limit_memory(3000)
native = {}
if not a.no_native:
    p = subprocess.run([sys.executable, "-I", os.path.join(HERE, "exc_native.py"), a.dll], capture_output=True, text=True, timeout=120)
    if p.returncode != 0: print("native run failed (rc %d): %s" % (p.returncode, p.stderr[-400:]))
    else: native = json.loads(p.stdout.strip().splitlines()[-1])
e = unshroud.Engine(); info = e.load_pe(a.dll, init=True)
name = os.path.basename(a.dll)
print("%s: env %s, entry point returned: %s %s" % (name, info["env"], info["init"], info.get("init_error", "")))
RET = 0xdead0000; rsp = info["stack"]
e.stop_at(RET)
pristine = e.snapshot()
def call(fn, x, y, sym=False):
    e.restore(pristine); e.clear_api_counts()
    e.write(rsp, struct.pack("<Q", RET)); e.set_reg("rsp", rsp); e.set_reg("rbp", rsp)
    e.set_reg("rcx", x); e.set_reg("rdx", y); e.set_reg("r8", 0); e.set_reg("r9", 0)
    e.rip = fn
    why, inf = e.run(50000000)
    return (e.reg("rax"), "return") if e.rip == RET else (None, "%s %s at 0x%x" % (why, inf, e.rip))
bad = 0; total = 0; rows = {}
for tname, inputs in exc_native.TESTS + exc_native.ONLY_UNSHROUD:
    fn = e.resolve(name, tname)
    if not fn: print("  %s: not exported" % tname); bad += 1; continue
    if a.trace == tname: e.env_options(trace=True)
    got = [call(fn, x, y) for x, y in inputs]
    if a.trace == tname: e.env_options(trace=False)
    want = native.get(tname)
    line = []
    for k, (x, y) in enumerate(inputs):
        g = got[k][0]; w = want[k] if want else None
        okk = w is None or g == w
        if w is not None: total += 1; bad += 0 if okk else 1
        line.append("%s(%x,%x)=%s%s" % ("" if okk else "WRONG ", x, y, ("%x" % g) if g is not None else "[" + got[k][1] + "]", "" if okk or w is None else " native %x" % w))
    rows[tname] = {"inputs": inputs, "unshroud": [g[0] for g in got], "native": want, "stops": [g[1] for g in got]}
    print("  %-24s %s %s" % (tname, "native+unshroud" if want else "unshroud only  ", "  ".join(line)))
print("%s: %d results compared with the native run, %d differ" % (name, total, bad))
if a.explore > 0:
    print("explored with symbolic arguments (%.0fs each): paths / returning / stops" % a.explore)
    for tname, inputs in exc_native.TESTS + exc_native.ONLY_UNSHROUD:
        fn = e.resolve(name, tname)
        e.restore(pristine)
        e.write(rsp, struct.pack("<Q", RET)); e.set_reg("rsp", rsp); e.set_reg("rbp", rsp)
        ins = []
        for k, r in enumerate(("rcx", "rdx")):
            e.set_reg(r, 0x1111111111111111 * (k + 1)); ins.append((e.symbolize_reg(r, "xy"[k]), "reg", (1, 2)[k], 8))
        e.rip = fn; start = e.snapshot()
        res = e.explore(start, ins, RET, a.explore, True, 20000000, [(info["base"], info["base"] + info["size"])])
        ps = res["paths"]
        outs = sorted(set("%x" % p["rax"] for p in ps if p["stop"] == "return"))
        stops = sorted(set(p["stop"] + (":" + p["info"] if p["stop"] != "return" else "") for p in ps))
        rows[tname]["explore"] = {"paths": len(ps), "returning": sum(1 for p in ps if p["stop"] == "return"), "stops": stops}
        print("  %-24s %2d paths, %2d return; %s; %d distinct results" % (tname, len(ps), rows[tname]["explore"]["returning"], stops, len(outs)))
if a.json: json.dump(rows, open(a.json, "w"))
print("DONE")
