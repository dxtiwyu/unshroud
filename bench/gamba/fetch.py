"""Downloads the GAMBA MBA data sets (DenuvoSoftwareSolutions/GAMBA, GPLv3, not redistributed here) at a pinned commit
into data/, each file checked against its git blob hash. usage: python -I fetch.py"""
import hashlib, os, urllib.request
COMMIT = "96691c0f1c7fd1be66bd11a6f2b60ce6865ce68c"
FILES = {"syntia.txt": "cd63703000d80b005314908f39afcb9ab97f911b", "qsynth_ea.txt": "5fd66ab68e761128873ff270f1484a12497dcf7a",
         "mba_obf_linear.txt": "008e0fe17f421ab6e4c0517bc5675416315d73ab", "mba_obf_nonlinear.txt": "d6ce895fcb253de701ebf46784559837b418d200",
         "mba_flatten.txt": "9a569192acb6978ea15db88ff69376da4514cc2e", "neureduce.txt": "8ac17268c785fdf6583f9d2bbc7292b8f93b1af5",
         "bonus/loki_tiny.txt": "ca22f1901ec352be860497fabd000c74deaac333"}
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data"); os.makedirs(out, exist_ok=True)
for path, blob in FILES.items():
    url = "https://raw.githubusercontent.com/DenuvoSoftwareSolutions/GAMBA/%s/experiments/datasets/%s" % (COMMIT, path)
    data = urllib.request.urlopen(url).read()
    h = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
    if h != blob: raise SystemExit("%s: hash %s, expected %s" % (path, h, blob))
    open(os.path.join(out, os.path.basename(path)), "wb").write(data); print("ok", path)
