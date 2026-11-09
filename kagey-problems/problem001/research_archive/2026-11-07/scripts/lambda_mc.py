"""Monte Carlo: expected number of violated sea constraints per column for a uniformly random sea word
(rows iid uniform), pair set F = all odd/even pairs. Counts each violating rectangle (hidden, rival, or a
second rectangle repeating a presentation). Usage: python lambda_mc.py h length trials"""
import sys, random
from collections import defaultdict
from fastcheck import shapes


def main():
    h, n, T = map(int, sys.argv[1:4])
    F = {frozenset((r, s)) for r in range(1, h + 1) for s in range(1, h + 1) if (r % 2) != (s % 2)}
    S = shapes(h)
    rng = random.Random(1)
    tot = 0; cols = 0
    for t in range(T):
        w = [rng.randint(1, h) for _ in range(n)]
        seen = defaultdict(int)
        bad = 0
        for sh in S:
            span = max(dx for dx, _ in sh)
            for x0 in range(n - span):
                cs = [(x0 + dx, r) for dx, r in sh]
                P = tuple(sorted(c for c in cs if w[c[0]] != c[1]))
                if len(P) > 2:
                    continue
                seen[P] += 1
                if not P:
                    bad += 1; continue
                if len(P) == 1:
                    (x, r), = P
                    if frozenset((r, w[x])) in F:
                        bad += 1
                    continue
                (x, r), (z, s) = P
                if x == z:
                    bad += frozenset((r, s)) in F
                elif r == s:
                    bad += w[x] == w[z]
                else:
                    bad += (w[x] == s and w[z] == r)
        bad += sum(c - 1 for c in seen.values() if c > 1)
        span_max = max(max(dx for dx, _ in sh) for sh in S)
        tot += bad; cols += n - span_max
    lam = tot / cols
    import math
    print(h, 'lambda', round(lam, 4), 'h*exp(-lambda)', round(h * math.exp(-lam), 4), flush=True)


if __name__ == '__main__':
    main()
