"""Every jump of every .pdata function (recursive descent): is it decided by its own window (unshroud_opaque)? Writes
<out>: one line per dead side "site side kind" (side 0 fall-through / 1 taken; kind constant or opaque): the side which
the window rules out. usage: python -I deadsides.py <pe> <out> [window]"""
import sys, os, collections, subprocess
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rdcfg
pe, outp = sys.argv[1], sys.argv[2]; W = int(sys.argv[3]) if len(sys.argv) > 3 else 40
base, funcs, lin, cfgs, callees = rdcfg.load(pe)
import pefile
IMG = pefile.PE(pe, fast_load=True).get_memory_mapped_image(); BASED = set()
pairs = []
for rva, g in cfgs.items():
    pred = {}
    for a, (sz, kind, succ) in g.items():
        for s in succ:
            if s is not None: pred.setdefault(s, []).append(a)
    for a, (sz, kind, succ) in g.items():
        if kind != "jcc": continue
        st = a; k = 0
        while k < W:
            p = pred.get(st, [])
            if len(p) != 1 or g[p[0]][1] == "call" or p[0] == rva: break
            st = p[0]; k += 1
        # (a window which takes the module's own base - lea r, [rip - rva] - is decided by where the module was loaded:
        # one load address decides it one way, another the other way; such jumps are never called dead)
        w = st; based = False
        while True:
            sz = g[w][0]
            if sz == 7:
                bb = bytes(IMG[w:w + 7])
                if bb[0] in (0x48, 0x4c) and bb[1] == 0x8d and (bb[2] & 0xc7) == 0x05 and w + 7 + int.from_bytes(bb[3:7], "little", signed=True) == 0: based = True
            if w == a: break
            nx = [x for x in g[w][2] if x is not None]
            if len(nx) != 1 and g[w][1] != "jcc": break
            w = nx[0] if g[w][1] != "jcc" else None
            if w is None or w not in g: break
        if based: BASED.add(a)
        pairs.append((st, a))
pairs = sorted(set(pairs), key=lambda x: x[1])
EXE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "build", "unshroud_opaque.exe")
def run(chunk):
    r = subprocess.run([EXE, pe] + ["%x:%x" % p for p in chunk], capture_output=True, text=True, timeout=3600, env=dict(os.environ, UNSHROUD_MEM_MB="2000"))
    return r.stdout.splitlines()
res = collections.Counter(); dead = []
with ThreadPoolExecutor(3) as ex:
    for lines in ex.map(run, [pairs[i:i + 300] for i in range(0, len(pairs), 300)]):
        for line in lines:
            t = line.split()
            if len(t) < 3: continue
            res[t[2]] += 1
            if t[2] in ("constant", "opaque") and int(t[0], 16) in BASED: res["base-dependent"] += 1; res[t[2]] -= 1; continue
            if t[2] in ("constant", "opaque") and len(t) >= 4:
                site = int(t[0], 16); live = 1 if t[3] == "taken" else 0
                dead.append("%x %d %s" % (site, 1 - live, t[2]))
open(outp, "w").write("\n".join(dead) + "\n")
tot = sum(res.values())
print("jumps %d:" % tot, ", ".join("%s %d (%.1f%%)" % (k, n, 100.0 * n / tot) for k, n in res.most_common()))
