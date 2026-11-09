import os
"""Entropy of the 'sea subshift': words over the rows 1..h (one black point per column) that stay valid
in the presence of far-away doubles realizing the pair set F (A|B partition). A word is allowed iff
  - no tilted rectangle inside it is hidden,
  - no tilted rectangle inside it shows P with an axis-aligned rival (Lemma 'rival', pair set F,
    black rows B_x = {w_x}),
  - no two tilted rectangles inside it show the same P (|P| <= 2).
Axis-aligned pairs are automatic (singleton columns are leaves of G_S).
Growth: count allowed words by a transfer DP over suffixes of length K-1, where K = 2*W_h + 1 covers
any two tilted rectangles that share a shown point. Usage: python sea_entropy.py h A_digits N"""
import sys
from itertools import product
from collections import defaultdict

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')))
from verify_narrow import rectangles, axis_rectangles


def shapes(h):
    W = 1 + (h - 1) ** 2 // 4
    m = W + 1
    ax = set(axis_rectangles(h, m))
    out = set()
    for r in rectangles(h, m):
        if r in ax:
            continue
        pts = [(i % m, i // m + 1) for i in range(h * m) if r >> i & 1]
        x0 = min(p[0] for p in pts)
        out.add(tuple(sorted((x - x0, y) for x, y in pts)))
    return sorted(out), W


def main():
    h = int(sys.argv[1]); A = {int(c) for c in sys.argv[2]}; N = int(sys.argv[3])
    F = {frozenset((r, s)) for r in range(1, h + 1) for s in range(1, h + 1) if (r in A) != (s in A)}
    S, W = shapes(h)
    K = 2 * W + 1

    def bad_new(word):
        """Constraints whose rectangles end at the last column of word (word length <= K)."""
        n = len(word); last = n - 1
        # rectangles inside word, with their presentations
        rects = []
        for sh in S:
            span = max(x for x, _ in sh)
            for x0 in range(0, n - span):
                cs = [(x0 + x, y) for x, y in sh]
                P = frozenset(c for c in cs if word[c[0]] != c[1])
                rects.append((x0, x0 + span, frozenset(cs), P))
        newest = [r for r in rects if r[1] == last]
        for x0, x1, cs, P in newest:
            if not P:
                return True
            if len(P) <= 2 and rival(P, word):
                return True
        # tilted-tilted: a newest rectangle against any other rectangle in the window
        byP = defaultdict(list)
        for r in rects:
            if len(r[3]) <= 2:
                byP[r[3]].append(r)
        for x0, x1, cs, P in newest:
            if len(P) <= 2 and len(byP[P]) > 1:
                return True
        return False

    def rival(P, word):
        P = list(P)
        if len(P) == 1:
            (x, r), = P
            return frozenset((r, word[x])) in F
        (x, r), (z, s) = sorted(P)
        if x == z:
            return frozenset((r, s)) in F
        if r == s:
            return word[x] == word[z]
        return word[x] == s and word[z] == r

    # DP over allowed words, state = last K-1 letters
    letters = range(1, h + 1)
    counts = {(): 1}
    hist = []
    for n in range(1, N + 1):
        new = defaultdict(int)
        for st, c in counts.items():
            for a in letters:
                w = st + (a,)
                if bad_new(w):
                    continue
                new[w[-(K - 1):] if len(w) >= K - 1 else w] += c
        counts = new
        tot = sum(counts.values())
        hist.append(tot)
        if n > 2:
            print(n, tot, round(hist[-1] / hist[-2], 6), len(counts), flush=True)


if __name__ == '__main__':
    main()
