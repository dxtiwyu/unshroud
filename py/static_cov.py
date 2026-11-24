"""Static branch census against what an exploration executed.
usage: python -I static_cov.py <pe> <result.json (xrun.py --out)> [tag ...]
Per tag: own = each explored function's conditional jumps (its first .pdata range), both sides, executed by its own
exploration; image = every conditional jump of every .pdata function of the image executed by any exploration."""
import sys, json, struct, bisect, os, pickle
import pefile, capstone
path = sys.argv[1]
res = json.load(open(sys.argv[2])); tags = sys.argv[3:] or list(res["res"].keys())
cache = path + ".jcc.pickle"
if os.path.exists(cache):
    base, funcs, jcc = pickle.load(open(cache, "rb"))
else:
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
    jcc = {}
    for b, e in funcs:
        s = []
        for addr, size, mn, ops in md.disasm_lite(bytes(data[b:e]), b):
            if mn.startswith("j") and mn != "jmp" and mn not in ("jrcxz", "jecxz"): s.append(addr)
        jcc[b] = s
    pickle.dump((base, funcs, jcc), open(cache, "wb"))
starts = [f[0] for f in funcs]
allsites = set(a for s in jcc.values() for a in s)
for tag in tags:
    R = {int(k): v for k, v in res["res"][tag].items() if v}
    own_tot = own_hit = own_plain = 0; glob = set(); nf = 0; per = []; sym_hit = 0; havoc = False
    for rva, v in R.items():
        cov = v.get("cov")
        if cov is None: continue
        for k in cov: glob.add(k)
        if rva not in jcc: continue
        sites = set(jcc[rva]); nf += 1
        hit = sum(1 for k in set(cov) if (k >> 1) in sites)
        if "cov_plain" in v: havoc = True; own_plain += sum(1 for k in set(v["cov_plain"]) if (k >> 1) in sites)
        else: own_plain += hit
        own_tot += 2 * len(sites); own_hit += hit
        sym_hit += len(set((int(a, 16) - base, int(t, 16)) for a, t in v.get("edge_list", []) if (int(a, 16) - base) in sites))
        per.append((2 * len(sites) - hit, rva, len(sites), hit))
    gh = sum(1 for k in glob if (k >> 1) in allsites)
    print("%-12s functions %d  own: jcc edges %d executed %d (%.1f%%), input-dependent edges reached %d  | image: %d of %d edges (%.2f%%)  time %.1fs" % (
        tag, nf, own_tot, own_hit, 100.0 * own_hit / max(1, own_tot), sym_hit, gh, 2 * len(allsites), 100.0 * gh / max(1, 2 * len(allsites)), sum(v.get("time", 0) for v in R.values())))
    if havoc: print("%-12s   of the own sides, %d (%.1f%%) executed without leaving a call out; call sites left out %d, runs %d" % ("", own_plain, 100.0 * own_plain / max(1, own_tot), sum(v.get("havoc_sites", 0) for v in R.values()), sum(v.get("runs", 0) for v in R.values())))
    if os.environ.get("COV_GAPS"):
        per.sort(reverse=True)
        for p in per[:int(os.environ["COV_GAPS"])]: print("    missing %5d  %8x  jcc %5d executed %5d" % p)
