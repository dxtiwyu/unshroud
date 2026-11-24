"""The trap tests (bench/exc/trap_tests.cpp) run natively: prints {case: [results]} as JSON.
usage: python -I trap_native.py <dll>     (started by trap_check.py in a process of its own)
CASES: (body, name, values of rcx / rax, run natively?)"""
import ctypes, json, sys
CASES = [
 (0, "icebp", [0], 1), (1, "int 1", [0], 1), (2, "int 3 (cd 03)", [0], 1), (3, "int3", [0], 1), (4, "int 2d", [0, 1, 2, 3, 4, 5], 1), (5, "int 2c", [0], 1),
 (6, "int 4", [0], 1), (7, "int 80", [0], 1), (8, "int 2a", [0], 1), (9, "ud2", [0], 1), (10, "ud1", [0], 1), (11, "ud0", [0], 1), (12, "hlt", [0], 1),
 (13, "cli", [0], 1), (14, "sti", [0], 1), (15, "in al,dx", [0], 1), (16, "out dx,al", [0], 1), (17, "in al,40h", [0], 1), (18, "insb", [0], 1),
 (19, "rdmsr", [0], 1), (20, "wrmsr", [0], 1), (21, "mov rax,cr0", [0], 1), (22, "mov rax,dr0", [0], 1), (23, "mov cr0,rax", [0], 1), (24, "lgdt", [0], 1),
 (25, "lidt", [0], 1), (26, "invlpg", [0], 1), (27, "swapgs", [0], 1), (28, "sysretq", [0], 1), (29, "rdpmc", [0], 1), (30, "xgetbv", [0, 0x77], 1),
 (31, "lock nop", [0], 1), (32, "lock add r,r", [0], 1), (33, "clts", [0], 1), (34, "invd", [0], 1), (35, "wbinvd", [0], 1), (36, "lmsw", [0], 1),
 (37, "ltr", [0], 1), (38, "lldt", [0], 1), (39, "read non-canonical", [0], 1), (40, "trap flag", [0], 1), (41, "sidt", [0], 1), (42, "sgdt", [0], 1),
 (43, "sldt", [0], 1), (44, "str", [0], 1), (45, "smsw", [0], 1), (46, "rdtsc", [0], 1), (47, "rdtscp", [0], 1), (48, "cpuid", [0], 1),
 (49, "mov eax,cs", [0], 1), (50, "mov eax,ss", [0], 1), (51, "mov eax,ds", [0], 1), (52, "mov eax,es", [0], 1), (53, "mov eax,fs", [0], 1), (54, "mov eax,gs", [0], 1),
 (55, "lsl", [0x33, 0x2b, 0x53, 0x10], 1), (56, "lar", [0x33, 0x2b, 0x53, 0x10], 1), (57, "verr", [0x33, 0x2b, 0x10], 1),
 (58, "popfq 240cd5h", [0], 1), (59, "popfq 0", [0], 1), (60, "mov ss; icebp", [0], 1), (61, "long nop", [0], 1), (62, "prefetchw", [0x10], 1),
 (63, "cmpxchg8b reg", [0], 1), (64, "aaa", [0], 1), (65, "into", [0], 1), (66, "salc", [0], 1), (67, "0f 04", [0], 1), (68, "push es", [0], 1),
 (69, "pop ss", [0], 1), (70, "pusha", [0], 1), (71, "aam", [0], 1), (72, "far jmp", [0], 1), (73, "rdrand", [0], 1),
 (74, "vmcall", [0], 0), (75, "vmmcall", [0], 0), (76, "int 2e", [0], 0), (77, "syscall", [0], 0), (78, "sysenter", [0], 0), (79, "int 29", [0], 0),
]
# trap2: bodies which go on after their exceptions (bench/exc/trap_tests.cpp, bodies2); b: rcx, for TRACE bodies also the steps the handler keeps TF on
CASES2 = [
 (0, "TF traced", [0, 1, 2, 3, 5]), (1, "TF; ud2", [0]), (2, "popfq twice with TF", [0]), (3, "std; ud2", [0]), (4, "int3, handler sets TF", [0]),
 (5, "TF; int3", [0]), (6, "read at 0", [0]), (7, "TF; pushfq; and ~100h; popfq", [0, 1, 2]), (8, "iretq flags 8d5h", [0]), (9, "iretq with TF", [0]),
 (10, "iretq cs 2bh", [0]), (11, "TF; mov ss; nops", [0]), (12, "mov ss,[0]", [0]), (13, "mov ss,b", [0x2b, 0x23, 0, 3, 0x53, 0x10, 0x33, 0x28]),
 (14, "TF; mov ss; pushfq", [0]), (15, "int 4", [0]), (16, "int 2c", [0]), (17, "int 1 (cd 01)", [0]), (18, "icebp", [0]), (19, "hlt", [0]),
 (20, "div by 0", [0]), (21, "int 3 (cd 03)", [0]), (22, "int 2d", [0]), (23, "int3", [0]),
]
HOT2 = [(0, 200), (1, 200), (7, 200), (8, 200), (9, 200), (11, 200), (14, 200), (13, 200), (3, 200)]
KINDS = {1: "step", 2: "bp", 3: "ud", 4: "av", 5: "priv", 6: "arith", 7: "other"}
def show2(v):
    if v is None: return "-"
    n = (v >> 36) & 15
    ev = " ".join("%s@%d" % (KINDS.get((v >> (9 * i)) & 7, "?"), (v >> (9 * i + 3)) & 63) for i in range(min(n, 4)))
    f, l = (v >> 40) & 31, (v >> 45) & 3
    fl = "" if not n else " | ctx%s%s%s handler%s%s | last%s%s" % (" TF" if f & 1 else "", " DF" if f & 2 else "", " RF" if f & 4 else "",
        " TF" if f & 8 else "", " DF" if f & 16 else "", " TF" if l & 1 else "", " RF" if l & 2 else "")
    return "%d: %s%s | ax %x" % (n, ev or "-", fl, (v >> 48) & 0xffff)
# trap3: hardware breakpoints (bodies3); each case is read as 14 values (trap3(body, b, k), k = 0..13); native 0: unshroud only
CASES3 = [
 (0, "write bp len 1", [0], 1), (1, "write bp len 4, word at +2", [0], 1), (2, "write bp, a read", [0], 1), (3, "read/write bp, a read", [0], 1),
 (4, "write bp len 8, byte at +7", [0], 1), (5, "write bp len 4 at +3", [0], 1), (6, "exec bp, handler sets RF", [0], 1),
 (7, "exec bp, handler disarms", [0], 1), (8, "exec bp, handler does nothing", [0], 1), (9, "two bps, one write", [0], 1),
 (10, "TF and a write bp at once", [0], 1), (11, "global enable only", [0], 1), (12, "kernel address in DR0", [0], 1),
 (13, "DR7 555503ffh", [0], 1), (14, "DR0 without an enable", [0], 1), (15, "mov ss,[bp]; nop", [0], 1),
 (17, "SetThreadContext arms", [0], 1), (18, "bp inside rep stosb", [0], 1),
 (16, "mov ss,[bp]; int3", [0], 0),   # (not run natively by default: needs a CPU where it is safe)
]
HOT3 = [(0, 200), (3, 200), (6, 200), (9, 200), (10, 200), (15, 200), (17, 200), (18, 200)]
def rel3(x):
    return "0" if x == 0 else "other" if x == 0xffffff else ("data+%x" % (x & 0xfffff)) if x >> 20 == 1 else ("code+%x" % (x & 0xfffff)) if x >> 20 == 2 else "?%x" % x
def show3(v):
    if v is None or len(v) < 14: return "-"
    n = (v[0] >> 36) & 15
    out = ["%d events, ax %x" % (n, (v[0] >> 48) & 0xffff)]
    for i in range(min(n, 6)):
        a, b = v[1 + i], v[7 + i]
        out.append("%s@%d(addr %d)%s dr6=%x dr7=%x dr0=%s dr1=%s" % (KINDS.get(a & 7, "?"), (a >> 3) & 63, (a >> 9) & 63, " RF" if (a >> 15) & 1 else "",
            ((b & 0xffff) << 16) | ((a >> 16) & 0xffff), a >> 32, rel3((b >> 16) & 0xffffff), rel3((b >> 40) & 0xffffff)))
    if v[13]: out.append("GetThreadContext: dr0=%s dr7=%x" % (rel3(v[13] & 0xffffff), v[13] >> 32))
    return " | ".join(out)
HOT = [(58, 300), (59, 300), (40, 300), (0, 300), (4, 300), (12, 300), (13, 300), (49, 300), (9, 300), (61, 300), (44, 300)]   # (body, times): through hot code
def show(v):
    if v is None: return "-"
    if v >> 60 == 1: return "no exception" + (", eax %x" % (v & 0xffffffff) if v & 0xffffffff else "")
    return "%08x at +%d, rip +%d, %d params%s%s, %d seen" % (v & 0xffffffff, (v >> 32) & 0xff, (v >> 40) & 0xff, (v >> 48) & 0xf,
        (" [%d" % ((v >> 52) & 0xf)) + (", -1]" if (v >> 56) & 1 else ", ..]") if (v >> 48) & 0xf else "", "", (v >> 57) & 3)
if __name__ == "__main__":
    dll = ctypes.CDLL(sys.argv[1])
    f = dll.trap; f.restype = ctypes.c_uint64; f.argtypes = [ctypes.c_uint64, ctypes.c_uint64]
    out = {}
    for body, name, vals, native in CASES:
        if not native: continue
        out[str(body)] = [f(body, b) for b in vals]
        print("native %d %s done" % (body, name), file=sys.stderr, flush=True)
    h = dll.hot; h.restype = ctypes.c_uint64; h.argtypes = [ctypes.c_uint64, ctypes.c_uint64]
    out["hot"] = [h(b, n) for b, n in HOT]
    f2 = dll.trap2; f2.restype = ctypes.c_uint64; f2.argtypes = [ctypes.c_uint64, ctypes.c_uint64]
    for body, name, vals in CASES2:
        out["t2:%d" % body] = [f2(body, b) for b in vals]
        print("native trap2 %d %s done" % (body, name), file=sys.stderr, flush=True)
    h2 = dll.hot2; h2.restype = ctypes.c_uint64; h2.argtypes = [ctypes.c_uint64, ctypes.c_uint64]
    out["hot2"] = [h2(b, n) for b, n in HOT2]
    f3 = dll.trap3; f3.restype = ctypes.c_uint64; f3.argtypes = [ctypes.c_uint64, ctypes.c_uint64, ctypes.c_uint64]
    for body, name, vals, nat in CASES3:
        if not nat: continue
        out["t3:%d" % body] = [[f3(body, b, k) for k in range(14)] for b in vals]
        print("native trap3 %d %s done" % (body, name), file=sys.stderr, flush=True)
    h3 = dll.hot3; h3.restype = ctypes.c_uint64; h3.argtypes = [ctypes.c_uint64, ctypes.c_uint64]
    out["hot3"] = [h3(b, n) for b, n in HOT3]
    print(json.dumps(out))
