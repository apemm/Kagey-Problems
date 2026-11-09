"""Marked transfer counts on h rows, partition A|B, pair set F fixed to all of K_{A,B}.
N_S(m) = number of valid words of length m whose double letters are exactly the edges in S, each once.
Validity: as in sea_entropy (hidden, rival, tilted-tilted), with black rows B_x = the letter's rows.
Usage: python count_marked.py h A_digits M"""
import sys, json
from collections import defaultdict
from itertools import combinations
from sea_entropy import shapes


def main():
    h = int(sys.argv[1]); A = {int(c) for c in sys.argv[2]}; M = int(sys.argv[3])
    Bset = [r for r in range(1, h + 1) if r not in A]
    E = [tuple(sorted((a, b))) for a in sorted(A) for b in Bset]
    F = {frozenset(e) for e in E}
    S, W = shapes(h)
    K = 2 * W + 1
    spans = [(sh, max(x for x, _ in sh)) for sh in S]
    letters = [(r,) for r in range(1, h + 1)] + E

    def rival(P, word):
        P = sorted(P)
        if len(P) == 1:
            (x, r), = P
            return any(frozenset((r, s)) in F for s in word[x] if s != r)
        (x, r), (z, s) = P
        if x == z:
            return frozenset((r, s)) in F
        if r == s:
            return bool(set(word[x]) & set(word[z]))
        return (s in word[x]) and (r in word[z])

    memo = {}

    def ok(word):
        if word in memo:
            return memo[word]
        n = len(word); last = n - 1
        rects = []
        for sh, span in spans:
            for x0 in range(0, n - span):
                cs = [(x0 + x, y) for x, y in sh]
                P = frozenset(c for c in cs if c[1] not in word[c[0]])
                if len(P) <= 2:
                    rects.append((x0 + span, P))
        cnt = defaultdict(int)
        for end, P in rects:
            cnt[P] += 1
        res = True
        for end, P in rects:
            if end == last and (not P or rival(P, word) or cnt[P] > 1):
                res = False; break
        memo[word] = res
        return res

    # DP over (suffix of length K-1, frozenset of used doubles); track counts by used-set
    states = {((), frozenset()): 1}
    out = defaultdict(dict)
    for m in range(1, M + 1):
        new = defaultdict(int)
        for (st, used), c in states.items():
            for L in letters:
                if len(L) == 2 and (L in used or len(used) >= 1 and False):
                    continue
                if len(L) == 2 and L in used:
                    continue
                w = st + (L,)
                if not ok(w):
                    continue
                u2 = used | {L} if len(L) == 2 else used
                if len(u2) > 1 and sys.argv[4:] == []:
                    continue          # at most one double unless asked otherwise
                new[(w[-(K - 1):] if len(w) >= K - 1 else w, u2)] += c
        states = new
        tot = defaultdict(int)
        for (st, used), c in states.items():
            tot[tuple(sorted(used))] += c
        for k, v in tot.items():
            out[m][str(k)] = v
        print(m, {k: v for k, v in tot.items()}, flush=True)
    json.dump(out, open(f'marked_h{h}_{sys.argv[2]}.json', 'w'))


if __name__ == '__main__':
    main()
