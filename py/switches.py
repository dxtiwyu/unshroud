"""Jump tables behind `jmp reg` (MSVC: lea rB, [rip+T]; movsxd rX, dword [rB + rI*4] (or mov eX); add rX, rB; jmp rX):
the table's entries (int32 offsets from T) while they land in the function's range and decode, at most 512, or up to a
bound found as cmp rI, N / ja just before. Writes "site target target ..." (rvas) and how much linear-only code the
targets reach. usage: python -I switches.py <pe> <out>"""
import sys, os, re, struct
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rdcfg, pefile, capstone
pe = sys.argv[1]
base, funcs, lin, cfgs, callees = rdcfg.load(pe)
img = pefile.PE(pe, fast_load=True).get_memory_mapped_image()
md = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
fe = dict(funcs)
def ins(a): return next(md.disasm_lite(bytes(img[a:a + 15]), a, 1), None)
out = []; nsw = 0; ntg = 0; newreach = 0; linonly_before = 0; linonly_after = 0
for fn, g in cfgs.items():
    end = fe[fn]
    pred = {}
    for a, (sz, kind, succ) in g.items():
        for s in succ:
            if s is not None: pred.setdefault(s, []).append(a)
    tables = {}
    for a, (sz, kind, succ) in g.items():
        if kind != "ijmp": continue
        i = ins(a); m = re.match(r"(r\w+)$", i[3].strip())
        if not m: continue
        reg = m.group(1)
        # walk back a few instructions for "add reg, rB" and "movsxd reg, dword ptr [rB + rI*4]" and "lea rB, [rip + d]"
        seq = []; w = a
        for _ in range(8):
            p = pred.get(w, [])
            if len(p) != 1: break
            w = p[0]; seq.append((w, ins(w)))
        T = None; idx = None; bound = None
        for w, x in seq:
            if x[2] == "lea" and "rip" in x[3]:
                mm = re.match(r"(\w+), \[rip ([+-]) (0x[0-9a-f]+)\]", x[3])
                if mm: T = w + x[1] + (int(mm.group(3), 16) if mm.group(2) == "+" else -int(mm.group(3), 16)); break
            if x[2] in ("movsxd", "mov") and "*4]" in x[3]:
                mm = re.search(r"\+ (\w+)\*4\]", x[3]); idx = mm.group(1) if mm else None
        for w, x in seq:
            if x[2] == "cmp" and idx and x[3].startswith(idx.replace("r", "e", 1) if idx[0] == "r" and idx[1:].isalpha() else idx):
                try: bound = int(x[3].split(",")[1], 16) + 1
                except ValueError: pass
        if T is None: continue
        tg = []
        for k in range(bound or 512):
            off = struct.unpack_from("<i", img, T + 4 * k)[0]; t = T + off
            if not (fn <= t < end) or ins(t) is None: break
            tg.append(t)
        if tg: tables[a] = sorted(set(tg)); nsw += 1; ntg += len(tables[a])
    for a, tg in tables.items(): out.append("%x %s" % (a, " ".join("%x" % t for t in tg)))
    # linear-only jcc reached once the tables' targets are followed (a recursive descent from each target)
    if tables:
        seen = set(g); work = [t for tg in tables.values() for t in tg]; extra = set()
        while work:
            x = work.pop()
            while fn <= x < end and x not in seen:
                i = ins(x)
                if i is None: break
                seen.add(x); _, sz, mn, ops = i
                if mn.startswith("j") and mn != "jmp":
                    extra.add(x)
                    try: work.append(int(ops, 16))
                    except ValueError: pass
                if mn == "jmp":
                    try: x = int(ops, 16); continue
                    except ValueError: break
                if mn.startswith("ret") or mn in ("int3", "ud2"): break
                x += sz
        newreach += len(extra & (set(lin[fn]) - set(a for a, v in g.items() if v[1] == "jcc")))
    linonly_before += len(set(lin[fn]) - set(a for a, v in g.items() if v[1] == "jcc"))
open(sys.argv[2], "w").write("\n".join(out) + "\n")
print("jump tables %d, targets %d; linear-only jumps %d, reached through the tables %d" % (nsw, ntg, linonly_before, newreach))
