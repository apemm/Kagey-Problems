"""Check the three-black-corner laws of the "1, x, h" family on random boards.
For every violation with at most one white corner, classify the black corners (D = double cell,
S = sea cell) and test the predicted arithmetic:
  DDD   : three double corners (always fatal when the completion is in the grid)
  vertex D, one D + one S : law (D): vertex odd row r, active side, v2(d) in {tau-2, tau-3}
  vertex S, two D : law (E2): S is a middle cell, odd row r with tau = 2 on S's side, other row even
  one D + two S : impossible (Lemma 12)
Usage: py v1laws.py h trials"""
import sys, random
from cegar_board import check


def v2(n):
    n = abs(n); c = 0
    while n % 2 == 0:
        n //= 2; c += 1
    return c


def board(h, rng):
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    rng.shuffle(E)
    cols = []
    for j, e in enumerate(E):
        cols.append(set(e))
        if j < len(E) - 1:
            cols += [{1}, {rng.choice([1, h])}, {h}]
    return cols


def main():
    h, T = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(1)
    tally = {}; bad = []
    for _ in range(T):
        cols = board(h, rng)
        n, det = check(h, cols)
        for v, cs, Pw, partner in det:
            if len(Pw) > 1:
                continue
            blk = [c for c in cs if c not in set(Pw)]
            kind = lambda c: 'D' if c[0] % 4 == 0 else 'S'
            ks = ''.join(sorted(kind(c) for c in blk))
            key = (v, ks); tally[key] = tally.get(key, 0) + 1
            if v == 'hidden' or v == 'tilt-tilt':
                continue
            (X,) = Pw
            # find the right-angle vertex: the black corner opposite to X
            V = [c for c in blk if (c[0] - X[0]) ** 2 + (c[1] - X[1]) ** 2 ==
                 max((b[0] - X[0]) ** 2 + (b[1] - X[1]) ** 2 for b in blk)][0]
            others = [c for c in blk if c != V]
            if ks == 'DSS':
                bad.append(('DSS exists', cs, X))
            elif ks == 'DDS' and kind(V) == 'D':
                q = [c for c in others if kind(c) == 'D'][0]; s = [c for c in others if kind(c) == 'S'][0]
                r, rq = V[1], q[1]; d = (q[0] - V[0]) // 4
                ok = r % 2 == 1 and (r - rq) % 2 == 1
                if s[1] == 1:
                    tau = v2(r - 1); ok = ok and r % 4 == 1
                else:
                    tau = v2(h - r); ok = ok and r % 4 == 3
                gap = tau - v2(d)
                ok = ok and gap in (2, 3) and ((gap == 2) == (s[0] % 4 != 2))
                tally[('lawD', gap)] = tally.get(('lawD', gap), 0) + 1
                if not ok:
                    bad.append(('lawD fails', cs, X, V, q, s))
            elif ks == 'DDS' and kind(V) == 'S':
                p, q = others
                rows = sorted([p[1], q[1]], key=lambda r: r % 2 == 0)
                o, e = rows
                ok = V[0] % 4 == 2 and o % 2 == 1 and e % 2 == 0
                if V[1] == 1:
                    ok = ok and v2(o - 1) == 2
                else:
                    ok = ok and v2(h - o) == 2
                tally[('lawE2',)] = tally.get(('lawE2',), 0) + 1
                if not ok:
                    bad.append(('lawE2 fails', cs, X, V))
    for k in sorted(tally, key=str):
        print(k, tally[k])
    print('law failures:', len(bad))
    for b in bad[:5]:
        print(b)


if __name__ == '__main__':
    main()
