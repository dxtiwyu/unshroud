"""Recursive-descent instruction graph of each .pdata function (first range), cached per binary.
cfg[rva] = dict addr -> (size, kind, succs) for every instruction reachable from the entry inside [b, e):
kind: 'jcc' (succs = [fallthrough, target]), 'jmp', 'call' (succs = [next]; 'callee' kept apart), 'ijmp', 'ret', 'stop', 'bad', 'seq'.
usage (as a module): load(pe_path) -> (base, funcs, linear_jcc, cfgs)"""
import os, pickle, struct, sys
import pefile, capstone
STOPS = {"int3", "ud2", "hlt", "ret", "retf", "iretq", "iretd", "ret ", "sysret", "ud1", "ud0"}
def build(path):
    pe = pefile.PE(path, fast_load=True)
    base = pe.OPTIONAL_HEADER.ImageBase
    pd = pe.OPTIONAL_HEADER.DATA_DIRECTORY[3]
    data = pe.get_memory_mapped_image()
    funcs = []
    for off in range(pd.VirtualAddress, pd.VirtualAddress + pd.Size, 12):
        b, e, u = struct.unpack_from("<III", data, off)
        if b: funcs.append((b, e))
    funcs.sort()
    md = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    lin = {}; cfgs = {}; callees = {}
    for b, e in funcs:
        s = []
        for addr, size, mn, ops in md.disasm_lite(bytes(data[b:e]), b):
            if mn.startswith("j") and mn != "jmp" and mn not in ("jrcxz", "jecxz"): s.append(addr)
        lin[b] = s
        g = {}; work = [b]; cl = []
        while work:
            a = work.pop()
            while b <= a < e and a not in g:
                ins = next(md.disasm_lite(bytes(data[a:min(e, a + 15)]), a, 1), None)
                if ins is None: g[a] = (1, "bad", []); break
                _, size, mn, ops = ins; nx = a + size
                tgt = None
                try: tgt = int(ops, 16)
                except ValueError: pass
                if mn.startswith("j") and mn != "jmp" or mn in ("loop", "loope", "loopne"):
                    g[a] = (size, "jcc" if mn.startswith("j") and mn not in ("jrcxz", "jecxz") else "jcx", [nx, tgt])
                    if tgt is not None and b <= tgt < e: work.append(tgt)
                    a = nx; continue
                if mn == "jmp":
                    if tgt is None: g[a] = (size, "ijmp", []); break
                    g[a] = (size, "jmp", [tgt]); a = tgt; continue
                if mn == "call":
                    g[a] = (size, "call", [nx]); cl.append((a, tgt)); a = nx; continue
                if mn in ("ret", "retf", "iretq", "iretd") or mn.startswith("ret"):
                    g[a] = (size, "ret", []); break
                if mn in ("int3", "ud2", "hlt", "ud1", "ud0") or (mn == "int" and ops in ("0x29", "0x2c")):
                    g[a] = (size, "stop", []); break
                g[a] = (size, "seq", [nx]); a = nx
        cfgs[b] = g; callees[b] = cl
    return base, funcs, lin, cfgs, callees
def load(path):
    cache = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", os.path.basename(path) + ".rd.pickle")
    if os.path.exists(cache) and os.path.getmtime(cache) > os.path.getmtime(path):
        return pickle.load(open(cache, "rb"))
    r = build(path)
    pickle.dump(r, open(cache, "wb"), protocol=4)
    return r
if __name__ == "__main__":
    base, funcs, lin, cfgs, callees = load(sys.argv[1])
    nl = sum(len(v) for v in lin.values())
    nr = sum(1 for g in cfgs.values() for v in g.values() if v[1] == "jcc")
    both = sum(1 for b in cfgs for a, v in cfgs[b].items() if v[1] == "jcc" and a in set(lin[b]))
    ni = sum(len(g) for g in cfgs.values()); bad = sum(1 for g in cfgs.values() for v in g.values() if v[1] == "bad")
    print("functions %d  linear jcc %d  recursive jcc %d (in both %d)  recursive instructions %d  bad decodes %d" % (len(funcs), nl, nr, both, ni, bad))
