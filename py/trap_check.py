"""The trap tests (bench/exc/trap_clang.dll) in unshroud against the native run of the same DLL on this CPU and this Windows.
usage: python -I trap_check.py <dll> [--no-native] [--build DIR] [--native-json FILE] [--save-native FILE]"""
import argparse, json, os, struct, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ap = argparse.ArgumentParser(); ap.add_argument("dll"); ap.add_argument("--no-native", action="store_true")
ap.add_argument("--build", default=os.path.join(HERE, "..", "build")); ap.add_argument("--native-json", default=""); ap.add_argument("--save-native", default="")
a = ap.parse_args()
sys.path.insert(0, a.build); os.add_dll_directory(os.path.abspath(a.build)); sys.path.insert(0, HERE)
import unshroud, trap_native
unshroud.limit_memory(3000)
native = {}
if a.native_json: native = json.load(open(a.native_json))
elif not a.no_native:
    p = subprocess.run([sys.executable, "-I", os.path.join(HERE, "trap_native.py"), a.dll], capture_output=True, text=True, timeout=120)
    if p.returncode != 0: print("native run failed (rc %d): %s" % (p.returncode, p.stderr[-600:]))
    else: native = json.loads(p.stdout.strip().splitlines()[-1])
    if a.save_native and native: json.dump(native, open(a.save_native, "w"))
e = unshroud.Engine(); info = e.load_pe(a.dll, init=True)
name = os.path.basename(a.dll)
print("%s: env %s, entry point returned: %s %s" % (name, info["env"], info["init"], info.get("init_error", "")))
RET = 0xdead0000; rsp = info["stack"]
e.stop_at(RET)
fn = e.resolve(name, "trap")
fh = e.resolve(name, "hot")
f2 = e.resolve(name, "trap2"); fh2 = e.resolve(name, "hot2"); f3 = e.resolve(name, "trap3"); fh3 = e.resolve(name, "hot3")
pristine = e.snapshot()
def call(x, y, f=None, z=0):
    e.restore(pristine)
    e.write(rsp, struct.pack("<Q", RET)); e.set_reg("rsp", rsp); e.set_reg("rbp", rsp)
    e.set_reg("rcx", x); e.set_reg("rdx", y); e.set_reg("r8", z); e.set_reg("r9", 0)
    e.rip = f or fn
    why, inf = e.run(50000000)
    return (e.reg("rax"), "return") if e.rip == RET else (None, "%s %s at 0x%x" % (why, inf, e.rip))
bad = 0; total = 0
for body, cname, vals, isnat in trap_native.CASES:
    want = native.get(str(body))
    for k, b in enumerate(vals):
        g, how = call(body, b); w = want[k] if want else None
        same = w is not None and g == w
        if w is not None: total += 1; bad += 0 if same else 1
        tag = "ok   " if same else ("unshroud " if w is None else "DIFF ")
        print("  %s %-20s rax=%-4x unshroud: %-52s%s" % (tag, cname, b, trap_native.show(g) if g is not None else "[" + how + "]", "" if same or w is None else "   native: " + trap_native.show(w)))
names = {c[0]: c[1] for c in trap_native.CASES}
for k, (body, n) in enumerate(trap_native.HOT):
    g, how = call(body, n, fh); w = native["hot"][k] if "hot" in native else None
    same = w is not None and g == w
    if w is not None: total += 1; bad += 0 if same else 1
    print("  %s hot %-16s x%-4d unshroud: %s%s" % ("ok   " if same else ("unshroud " if w is None else "DIFF "), names[body], n, ("%x" % g) if g is not None else "[" + how + "]", "" if same or w is None else "   native: %x" % w))
for body, cname, vals in trap_native.CASES2:
    want = native.get("t2:%d" % body)
    for k, b in enumerate(vals):
        g, how = call(body, b, f2); w = want[k] if want else None
        same = w is not None and g == w
        if w is not None: total += 1; bad += 0 if same else 1
        tag = "ok   " if same else ("unshroud " if w is None else "DIFF ")
        print("  %s t2 %-26s b=%-3x unshroud: %-60s%s" % (tag, cname, b, trap_native.show2(g) if g is not None else "[" + how + "]", "" if same or w is None else "   native: " + trap_native.show2(w)))
names2 = {c[0]: c[1] for c in trap_native.CASES2}
for k, (body, n) in enumerate(trap_native.HOT2):
    g, how = call(body, n, fh2); w = native["hot2"][k] if "hot2" in native else None
    same = w is not None and g == w
    if w is not None: total += 1; bad += 0 if same else 1
    print("  %s hot2 %-24s x%-4d unshroud: %s%s" % ("ok   " if same else ("unshroud " if w is None else "DIFF "), names2[body], n, ("%x" % g) if g is not None else "[" + how + "]", "" if same or w is None else "   native: %x" % w))
for body, cname, vals, nat in trap_native.CASES3:
    want = native.get("t3:%d" % body)
    for j, b in enumerate(vals):
        g = []
        for k in range(14):
            r, how = call(body, b, f3, k)
            if r is None: g = None; break
            g.append(r)
        w = want[j] if want else None
        same = w is not None and g == w
        if w is not None: total += 1; bad += 0 if same else 1
        tag = "ok   " if same else ("unshroud " if w is None else "DIFF ")
        print("  %s t3 %-28s unshroud: %s" % (tag, cname, trap_native.show3(g) if g is not None else "[" + how + "]"))
        if not same and w is not None: print("        %-28s native: %s" % ("", trap_native.show3(w)))
names3 = {c[0]: c[1] for c in trap_native.CASES3}
for k, (body, n) in enumerate(trap_native.HOT3):
    g, how = call(body, n, fh3); w = native["hot3"][k] if "hot3" in native else None
    same = w is not None and g == w
    if w is not None: total += 1; bad += 0 if same else 1
    print("  %s hot3 %-28s x%-4d unshroud: %s%s" % ("ok   " if same else ("unshroud " if w is None else "DIFF "), names3[body], n, ("%x" % g) if g is not None else "[" + how + "]", "" if same or w is None else "   native: %x" % w))
print("%s: %d results compared with the native run, %d differ" % (name, total, bad))
