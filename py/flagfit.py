"""Fits what the CPU does with flags: reads t_flags output, and for each instruction and flag says which simple rule
(unchanged, 0, 1, of the result, of an operand) holds on every trial.  usage: t_flags N hex... | python -I flagfit.py"""
import sys, collections
W = {"48": 64}
rows = collections.defaultdict(list)
for l in sys.stdin:
    p = l.split()
    if len(p) != 10: continue
    rows[p[0]].append([int(x, 16) for x in p[1:]])
names = {0: "CF", 2: "PF", 4: "AF", 6: "ZF", 7: "SF", 11: "OF"}
def par(v): return 1 - bin(v & 0xff).count("1") % 2
for ins, rs in rows.items():
    w = int(sys.argv[1]) if len(sys.argv) > 1 else 64
    widths = {}
    out = []
    for bit, nm in names.items():
        cands = {
            "unchanged": lambda r: (r[7] >> bit) & 1, "0": lambda r: 0, "1": lambda r: 1,
        }
        for wd in (8, 16, 32, 64):
            m = (1 << wd) - 1
            cands["zero(rax%d)" % wd] = lambda r, m=m: int((r[4] & m) == 0)
            cands["sign(rax%d)" % wd] = lambda r, wd=wd: (r[4] >> (wd - 1)) & 1
            cands["zero(rdx%d)" % wd] = lambda r, m=m: int((r[6] & m) == 0)
            cands["sign(rdx%d)" % wd] = lambda r, wd=wd: (r[6] >> (wd - 1)) & 1
        cands["parity(rax)"] = lambda r: par(r[4])
        cands["parity(rdx)"] = lambda r: par(r[6])
        cands["parity(rax>>8)"] = lambda r: par(r[4] >> 8)
        for k in range(0, 8):
            cands["rax bit%d" % k] = lambda r, k=k: (r[4] >> k) & 1
            cands["rax0 bit%d" % k] = lambda r, k=k: (r[0] >> k) & 1
        for wd in (8, 16, 32, 64):
            cands["top2xor(rax%d)" % wd] = lambda r, wd=wd: ((r[4] >> (wd - 1)) ^ (r[4] >> (wd - 2))) & 1
            cands["msb(rax0_%d)" % wd] = lambda r, wd=wd: (r[0] >> (wd - 1)) & 1
            cands["msb(rax0^rax %d)" % wd] = lambda r, wd=wd: ((r[0] ^ r[4]) >> (wd - 1)) & 1
            cands["msb(rax%d)^CFout" % wd] = lambda r, wd=wd: ((r[4] >> (wd - 1)) ^ r[8]) & 1
            cands["msb(rbx%d)" % wd] = lambda r, wd=wd: (r[1] >> (wd - 1)) & 1
            cands["msb(rax0^rbx %d)" % wd] = lambda r, wd=wd: ((r[0] ^ r[1]) >> (wd - 1)) & 1
        cands["(rax0^rax) bit4"] = lambda r: ((r[0] ^ r[4]) >> 4) & 1
        cands["(rax0^rbx^rax) bit4"] = lambda r: ((r[0] ^ r[1] ^ r[4]) >> 4) & 1
        ok = [n for n, f in cands.items() if all(f(r) == ((r[8] >> bit) & 1) for r in rs)]
        ones = sum((r[8] >> bit) & 1 for r in rs)
        out.append("%s: %s (set in %d of %d)" % (nm, ", ".join(ok[:6]) if ok else "?", ones, len(rs)))
    print(ins, " | ".join(out))
