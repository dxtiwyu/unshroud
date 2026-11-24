"""One concrete run of a function inside the synthetic process: the API calls in order and how the run ends.
usage: python -I runenv.py <pe> <rva> [max]"""
import os, struct, sys
HERE = os.path.dirname(os.path.abspath(__file__)); B = os.path.join(HERE, "..", "build")
sys.path.insert(0, B); os.add_dll_directory(os.path.abspath(B)); sys.path.insert(0, HERE)
import unshroud, winenv, winapi
pe, rva = sys.argv[1], int(sys.argv[2], 16); MAX = int(float(sys.argv[3])) if len(sys.argv) > 3 else 20000000
e = unshroud.Engine(); info = e.load_pe(pe, env=False)
env = winenv.Environment(winenv.TritonShim, winenv.EngineCtx(e), type("I", (), {"base": info["base"]})(), pe)
e.gsbase = winenv.TEB; top = winenv.RSP + 0x10000; e.map(top - winenv.STACK_SIZE, winenv.STACK_SIZE)
api = winapi.install(e, env, info["stubs"])
seq = []
orig = api.hook
for a, n in info["stubs"].items():
    pass
# record the order of calls: wrap the counter
class Rec(dict):
    pass
calls_before = {}
RET = 0xdead0000; rsp = winenv.RSP
e.write(rsp, struct.pack("<Q", RET)); e.set_reg("rsp", rsp); e.set_reg("rbp", rsp)
for k, r in enumerate(("rcx", "rdx", "r8", "r9")):
    e.set_reg(r, 0x1111111111111111 * (k + 1))
    if os.environ.get("SYM"): e.symbolize_reg(r, "xyzw"[k])
e.stop_at(RET); e.rip = info["base"] + rva
import collections
last = collections.deque(maxlen=12)
prev = collections.Counter()
done = 0
while done < MAX:
    why, inf = e.run(50000); done += 50000
    diff = api.calls - prev
    for n, c in diff.items(): last.append((done, n, c))
    prev = collections.Counter(api.calls)
    if why != "count": break
print("rva %x: %s %s at %x (image rva %x), ~%d instructions" % (rva, why, inf, e.rip, e.rip - info["base"], done))
print("last calls (instructions so far, name, count):", list(last))
print("unmodeled:", api.unknown.most_common(10))
