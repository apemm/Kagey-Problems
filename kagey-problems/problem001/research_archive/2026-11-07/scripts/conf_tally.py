"""Tally violation types in uniformly random confined sea words (parity pair set F).
Usage: python conf_tally.py h m trials mode(odd|checker|all)"""
import sys, random
from collections import Counter
from fastcheck import shapes


def main():
    h, m, trials = map(int, sys.argv[1:4]); mode = sys.argv[4]
    rng = random.Random(7)
    F = lambda r, s: (r % 2) != (s % 2)
    S = shapes(h)
    tally = Counter()
    for _ in range(trials):
        if mode == 'odd':
            word = [rng.choice(range(1, h + 1, 2)) for _ in range(m)]
        elif mode == 'checker':
            word = [rng.choice([a for a in range(1, h + 1) if (a - x) % 2 == 0]) for x in range(m)]
        else:
            word = [rng.randint(1, h) for _ in range(m)]
        seen = set()
        for sh in S:
            sp = max(dx for dx, _ in sh)
            for x0 in range(0, m - sp):
                cs = [(x0 + dx, r) for dx, r in sh]
                P = tuple(sorted(c for c in cs if word[c[0]] != c[1]))
                if len(P) > 2:
                    continue
                if not P:
                    tally['hidden'] += 1; continue
                if P in seen:
                    tally['tilt-tilt %d' % len(P)] += 1
                seen.add(P)
                if len(P) == 1:
                    (x, r), = P
                    if F(r, word[x]):
                        tally['rival single'] += 1
                else:
                    (x, r), (z, s) = P
                    if x == z:
                        if F(r, s):
                            tally['rival vertical'] += 1
                    elif r == s:
                        if word[x] == word[z]:
                            tally['rival horizontal'] += 1
                    elif word[x] == s and word[z] == r:
                        tally['rival oblique'] += 1
    per = {k: round(v / (trials * m), 4) for k, v in sorted(tally.items())}
    print('h', h, mode, 'violations per column', per, 'total', round(sum(tally.values()) / (trials * m), 4))


if __name__ == '__main__':
    main()
