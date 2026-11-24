"""Explores functions of a PE with unshroud inside a synthetic Windows process (winenv.py + winapi.py): TEB/PEB, the loader's
module lists, the system DLLs of this machine mapped with their export tables, API models on every import and export.
usage: python -I explore_env.py <pe> <rva[:nargs],...|@file> [--time S] [--paths] [--noenv] [--max N] [--out F] [--build DIR]"""
import argparse, json, os, struct, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
ap = argparse.ArgumentParser()
ap.add_argument("pe"); ap.add_argument("funcs")
ap.add_argument("--time", type=float, default=10.0); ap.add_argument("--paths", action="store_true")
ap.add_argument("--noenv", action="store_true"); ap.add_argument("--max", type=float, default=20e6)
ap.add_argument("--out", default=""); ap.add_argument("--build", default=os.path.join(HERE, "..", "build"))
a = ap.parse_args()
sys.path.insert(0, a.build); os.add_dll_directory(os.path.abspath(a.build)); sys.path.insert(0, HERE)
import unshroud, winenv, winapi
REGS = {"rcx": 1, "rdx": 2, "r8": 8, "r9": 9}
RET = 0xdead0000
spec = open(a.funcs[1:]).read().replace(chr(10), ",") if a.funcs.startswith("@") else a.funcs
funcs = []
for f in spec.split(","):
    if not f.strip(): continue
    r, _, n = f.strip().partition(":"); funcs.append((int(r, 16), int(n) if n else 4))

t0 = time.perf_counter()
proto = unshroud.Engine()
info = proto.load_pe(a.pe, env=False)      # the process is built by winenv.py below (the Python prototype of src/win.cpp)
env = api = None
if not a.noenv:
    img = type("Img", (), {"base": info["base"]})()
    env = winenv.Environment(winenv.TritonShim, winenv.EngineCtx(proto), img, a.pe)
    proto.gsbase = winenv.TEB
top = winenv.RSP + 0x10000
proto.map(top - winenv.STACK_SIZE, winenv.STACK_SIZE)
pristine = proto.snapshot()
print("setup %.2fs (environment: %s, modules %d)" % (time.perf_counter() - t0, not a.noenv, len(env.order) if env else 0), file=sys.stderr, flush=True)
out = open(a.out, "w") if a.out else sys.stdout
ranges = [(info["base"], info["base"] + info["size"])]
def ret0(en):
    sp = en.reg("rsp"); en.rip = struct.unpack("<Q", en.read(sp, 8))[0]; en.set_reg("rsp", sp + 8); en.set_reg("rax", 0)
def one(e, rva, nargs, ts):
    e.restore(pristine)
    if env: e.gsbase = winenv.TEB
    if api: api.calls.clear(); api.unknown.clear(); api.errors.clear(); api.init_state()
    rsp = winenv.RSP
    e.write(rsp, struct.pack("<Q", RET)); e.set_reg("rsp", rsp); e.set_reg("rbp", rsp)
    inputs = []
    for k, r in enumerate(("rcx", "rdx", "r8", "r9")[:nargs]):
        e.set_reg(r, 0x1111111111111111 * (k + 1)); idx = e.symbolize_reg(r, "xyzw"[k]); inputs.append((idx, "reg", REGS[r], 8))
    e.rip = info["base"] + rva
    start = e.snapshot()
    try:
        res = e.explore(start, inputs, RET, a.time, a.paths, int(a.max), ranges)
        paths = res["paths"]
        row = {"rva": hex(rva), "env": env is not None, "edges": res["edges"], "npaths": len(paths), "runs": res["runs"], "queries": res["queries"],
               "refuted": len(res["refuted"]), "undecided": len(res["undecided"]), "time": res["time"], "wall": time.perf_counter() - ts,
               "ins": sum(p["ins"] for p in paths), "stops": sorted(set(p["stop"] for p in paths)),
               "returned": sum(1 for p in paths if p["stop"] == "return"), "info": sorted(set(p["info"] for p in paths if p["info"]))[:5]}
        if api: row["calls"] = api.calls.most_common(12); row["unmodeled"] = api.unknown.most_common(12); row["model_errors"] = api.errors.most_common(8)
    except MemoryError:
        raise
    except Exception as ex:
        row = {"rva": hex(rva), "error": str(ex)[:200]}
    return row

e = None; used = 0
for rva, nargs in funcs:
    ts = time.perf_counter()
    if e is None or used >= 16:                    # one engine (and its hooks) for a few functions: bounded node table
        e = unshroud.Engine(); e.restore(pristine); used = 0
        if env:
            env.ctx.e = e; e.gsbase = winenv.TEB
            api = winapi.install(e, env, info["stubs"])
        else:
            for addr in info["stubs"]: e.hook(addr, ret0)
    used += 1
    try:
        row = one(e, rva, nargs, ts)
    except MemoryError as ex:                     # the engine's memory is spent: a fresh one for the next function
        row = {"rva": hex(rva), "error": "memory: " + str(ex)[:100]}; e = None
    out.write(json.dumps(row) + chr(10)); out.flush()


