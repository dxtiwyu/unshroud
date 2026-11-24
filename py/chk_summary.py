"""Counts of out_check verdicts (UNSHROUD_CHECK_OUT runs) per result file: proved / cex / unknown / same."""
import collections, json, sys
for f in sys.argv[1:]:
    d = json.load(open(f)); c = collections.Counter(); bad = []
    for rva, r in d["raw"].items():
        for p in r["paths"]:
            if p["stop"] != "return": continue
            k = p.get("out_check", "none"); c[k] += 1
            if k == "cex": bad.append(rva)
    print(f, dict(c), "COUNTEREXAMPLES in", bad[:10] if bad else "none")
