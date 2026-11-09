"""Sea-subshift entropy via an explicit transfer graph. States: allowed words of length K-1
(K = 2 W_h + 1). Edge state -> state' by appending a letter when the new constraints (rectangles
ending at the new column, and tilted-tilted pairs involving them) hold. Entropy = Perron root,
by power iteration on the reachable strongly connected part. Usage: python sea_graph.py h A_digits"""
import sys, time
import numpy as np
from scipy.sparse import csr_matrix
from sea_entropy import shapes
from collections import defaultdict


def main():
    h = int(sys.argv[1]); A = {int(c) for c in sys.argv[2]}
    F = {frozenset((r, s)) for r in range(1, h + 1) for s in range(1, h + 1) if (r in A) != (s in A)}
    S, W = shapes(h)
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 2 * W + 1
    spans = [(sh, max(x for x, _ in sh)) for sh in S]

    def rival(P, word):
        P = sorted(P)
        if len(P) == 1:
            (x, r), = P
            return frozenset((r, word[x])) in F
        (x, r), (z, s) = P
        if x == z:
            return frozenset((r, s)) in F
        if r == s:
            return word[x] == word[z]
        return word[x] == s and word[z] == r

    def ok(word):
        n = len(word); last = n - 1
        rects = []
        for sh, span in spans:
            for x0 in range(0, n - span):
                cs = [(x0 + x, y) for x, y in sh]
                P = frozenset(c for c in cs if word[c[0]] != c[1])
                if len(P) <= 2:
                    rects.append((x0 + span, P))
        byP = defaultdict(int)
        for end, P in rects:
            byP[P] += 1
        for end, P in rects:
            if end != last:
                continue
            if not P or rival(P, word) or byP[P] > 1:
                return False
        return True

    t0 = time.time()
    # grow allowed words up to length K-1 (prefix closure), then build the graph on length K-1 states
    layer = [()]
    for n in range(1, K):
        layer = [w + (a,) for w in layer for a in range(1, h + 1) if ok(w + (a,))]
        print('len', n, len(layer), round(time.time() - t0), flush=True)
    idx = {w: i for i, w in enumerate(layer)}
    rows, cols = [], []
    for w in layer:
        for a in range(1, h + 1):
            nw = w + (a,)
            if ok(nw):
                s2 = nw[1:]
                j = idx.get(s2)
                if j is not None:
                    rows.append(idx[w]); cols.append(j)
    N = len(layer)
    M = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(N, N))
    print('states', N, 'edges', len(rows), round(time.time() - t0), flush=True)
    v = np.ones(N)
    lam = 0
    for it in range(3000):
        v2 = M.T @ v
        lam2 = v2.sum() / v.sum()
        v = v2 / v2.sum()
        if it % 200 == 0:
            print('iter', it, lam2, flush=True)
        if abs(lam2 - lam) < 1e-12 and it > 50:
            break
        lam = lam2
    print('RHO', h, sorted(A), lam2, flush=True)
    # Parry measure: left and right Perron vectors; frequency of the last letter of the state
    u = np.ones(N)
    for it in range(3000):
        u2 = M @ u
        u = u2 / u2.sum()
    mu = u * v
    mu = mu / mu.sum()
    freq = np.zeros(h + 1)
    for w, i in idx.items():
        freq[w[-1]] += mu[i]
    print('FREQ', h, [round(float(f), 4) for f in freq[1:]], flush=True)


if __name__ == '__main__':
    main()
