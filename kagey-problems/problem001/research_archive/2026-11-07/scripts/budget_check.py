"""Check the completion budget on valid boards: every black right angle (A,B,C) with
X = A + C - B in the grid has a distinct completion, and white completions are distinct.
Usage: python budget_check.py file.json [more.json]"""
import sys, json
from itertools import combinations


def board(d):
    S = set()
    for x, col in enumerate(d['word'].split(',')):
        for ch in col:
            S.add((x, int(ch)))
    return d['h'], d['w'], S


def check(h, w, S):
    pts = sorted(S)
    comp = {}
    axis = tilt = 0
    for B in pts:
        others = [P for P in pts if P != B]
        for A, C in combinations(others, 2):
            u = (A[0] - B[0], A[1] - B[1]); v = (C[0] - B[0], C[1] - B[1])
            if u[0] * v[0] + u[1] * v[1] != 0:
                continue
            X = (A[0] + C[0] - B[0], A[1] + C[1] - B[1])
            if not (0 <= X[0] < w and 1 <= X[1] <= h):
                continue
            if u[0] == 0 or u[1] == 0:
                axis += 1
            else:
                tilt += 1
            comp.setdefault(X, []).append((A, B, C))
    white = {X: L for X, L in comp.items() if X not in S}
    coll = sum(1 for L in white.values() if len(L) > 1)
    black = sum(len(L) for X, L in comp.items() if X in S)
    return axis, tilt, coll, black


for f in sys.argv[1:]:
    d = json.load(open(f))
    h, w, S = board(d)
    a, t, c, b = check(h, w, S)
    print(f, 'h', h, 'w', w, 'N', len(S), 'axis', a, 'tilted', t, 'budget', h * w - len(S) + 4,
          'white collisions', c, 'black completions', b)
