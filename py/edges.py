"""Which of the given edges did unshroud_explore reach / refute / block? stdin: its JSON lines. usage: edges.py src:dst,..."""
import sys, json
want = [tuple(int(x, 16) for x in e.split(":")) for e in sys.argv[1].split(",")]
for l in sys.stdin:
    if not l.startswith("{"): continue
    r = json.loads(l)
    def S(k): return set((int(a, 16), int(b, 16)) for a, b in r.get(k) or [])
    ed, rf, bl, un, lk = S("edge_list"), S("refuted"), S("blocked"), S("undecided"), S("likely")
    print("%s: time %.2f runs %d edges %d refuted %d blocked %d undecided %d likely %d stages %s" % (r["rva"], r["time"], r["runs"], r["edges"], len(rf), len(bl), len(un), len(lk), r["stages"]))
    for e in want:
        print("   %x -> %x: %s" % (e[0], e[1], "REACHED" if e in ed else "refuted" if e in rf else "blocked" if e in bl else "undecided" if e in un else "likely" if e in lk else "not seen"))
