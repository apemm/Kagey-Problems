"""Check Lemma 8(c): in a row-1 sea at spacing 4, a double point in odd row r1 with v2(r1-1) in {2,3}
and an even row r2 > r1 in a neighbouring double give the predicted violation. Usage: python check_lemma8.py h boards"""
import sys, random
from fastcheck import violations
from anneal_row1 import build


def v2(n):
    k = 0
    while n % 2 == 0:
        n //= 2; k += 1
    return k


def main():
    h, T = int(sys.argv[1]), int(sys.argv[2])
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    M = 1 + (h - 1) ** 2 // 4 + 2
    rng = random.Random(5); pred = found = 0
    for t in range(T):
        o = E[:]; rng.shuffle(o); cols = build(h, o, M)
        v, det = violations(h, cols, detail=True)
        S = {frozenset(cs) for k, cs, P in det}
        for i in range(1, len(o) - 1):
            r1 = [r for r in o[i] if r % 2][0]
            if r1 == 1 or (r1 - 1) % 4 or v2(r1 - 1) > 3:
                continue
            for dj in (-1, 1):
                j = i + dj
                for r2 in o[j]:
                    if r2 % 2 == 0 and r2 > r1:
                        x = M + 4 * i; y = (r1 - 1) * (r2 - r1) // (4 * dj)
                        u = (x + y, 1); p = (x, r1); q = (M + 4 * j, r2)
                        X = (u[0] + q[0] - p[0], u[1] + q[1] - p[1])
                        pred += 1; found += frozenset([u, p, q, X]) in S
    print('h', h, 'predicted', pred, 'confirmed', found, flush=True)


if __name__ == '__main__':
    main()
