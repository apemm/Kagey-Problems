"""Exact winners (six faces) just below and above tau_N, from 03_task1_results.json."""
import os, json, collections
HERE = os.path.dirname(os.path.abspath(__file__))
res = json.load(open(os.path.join(HERE, "03_task1_results.json")))
cnt = collections.Counter()
bad = []
minmargin = {}
for r in res["pair"]:
    if r.get("tauN") is None:
        continue
    i, j = r["i"], r["j"]
    b, a = r["win_below"], r["win_above"]
    kb, ka = tuple(b[0]), tuple(a[0])
    cnt[(kb == (i,) or kb == (j,), ka == tuple(sorted((i, j))))] += 1
    if not (kb in [(i,), (j,)] and ka == tuple(sorted((i, j)))):
        bad.append((i, j, r["N"], b, a))
print("(below winner is singleton i or j, above winner is the pair) counts:", dict(cnt))
print("exceptions:", bad)
# winner below: which singleton?
c2 = collections.Counter((r["i"] == tuple(r["win_below"][0])[0] if len(r["win_below"][0]) == 1 else None) for r in res["pair"] if r.get("tauN"))
print("below-winner is singleton {i} (True) or {j} (False):", dict(c2))
