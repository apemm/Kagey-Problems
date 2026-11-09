"""Sequential Monte Carlo estimate of the sea-shift entropy rho_h (parity partition).
Population of valid words; each step extends every word by every allowed letter, records the mean
number of allowed extensions, and resamples N words uniformly from all extensions.
log rho ~ mean over late steps of log(mean extensions). Usage: python smc_entropy.py h N steps seed"""
import sys, random, math
from fastcheck import shapes


def main():
    h, N, steps, seed = map(int, sys.argv[1:5])
    rng = random.Random(seed)
    F = lambda r, s: (r % 2) != (s % 2)
    S = shapes(h)
    span = {sh: max(dx for dx, _ in sh) for sh in S}
    W = max(span.values())
    K = 2 * W + 1

    def allowed(word, pres):
        """word: list of letters; pres: dict presentation -> count for rectangles completed in the last
        K columns (as absolute coordinates). Returns (ok, new presentations to add)."""
        n = len(word); last = n - 1
        new = []
        for sh in S:
            sp = span[sh]
            x0 = last - sp
            if x0 < 0:
                continue
            cs = [(x0 + dx, r) for dx, r in sh]
            P = tuple(sorted(c for c in cs if word[c[0]] != c[1]))
            if len(P) > 2:
                continue
            if not P:
                return False, None
            if len(P) == 1:
                (x, r), = P
                if F(r, word[x]):
                    return False, None
            else:
                (x, r), (z, s) = P
                if x == z:
                    if F(r, s):
                        return False, None
                elif r == s:
                    if word[x] == word[z]:
                        return False, None
                elif word[x] == s and word[z] == r:
                    return False, None
            if P in pres or P in new:
                return False, None
            new.append(P)
        return True, new

    pop = [([], {})]
    logs = []
    for t in range(steps):
        ext = []
        total = 0
        for word, pres in pop:
            for a in range(1, h + 1):
                w2 = word + [a]
                ok, new = allowed(w2, pres)
                if ok:
                    total += 1
                    ext.append((w2, pres, new))
        if not ext:
            print('extinct'); return
        logs.append(math.log(total / len(pop)))
        pick = [ext[rng.randrange(len(ext))] for _ in range(N)]
        pop = []
        for w2, pres, new in pick:
            n = len(w2)
            p2 = {P: 1 for P in pres if max(c[0] for c in P) >= n - K}
            for P in new:
                p2[P] = 1
            pop.append((w2[-(K + 2):] if False else w2, p2))
        if t % 20 == 19:
            late = logs[min(len(logs) // 2, 2 * K):]
            print(t + 1, round(math.exp(sum(late) / len(late)), 4), flush=True)
    late = logs[min(len(logs) // 2, 2 * K):]
    print('RHO_EST', h, round(math.exp(sum(late) / len(late)), 4), flush=True)


if __name__ == '__main__':
    main()
