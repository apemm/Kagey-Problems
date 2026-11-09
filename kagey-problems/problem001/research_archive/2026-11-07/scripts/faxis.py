"""f_axis(h, m): the largest number of edges in a bipartite graph with parts of sizes h and m and
no 4- or 6-cycle (the axis-aligned-only version of the problem, m >= 3). SAT with increasing bound."""
import sys, json, time
from itertools import combinations, permutations
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType


def clauses(h, m):
    v = lambda r, c: r * m + c + 1
    cl = []
    for r1, r2 in combinations(range(h), 2):
        for c1, c2 in combinations(range(m), 2):
            cl.append([-v(r1, c1), -v(r1, c2), -v(r2, c1), -v(r2, c2)])
    for R in combinations(range(h), 3):
        for C in combinations(range(m), 3):
            # 6-cycles on K_{3,3}: r0-c_{s0}-r1-c_{s1}-r2-c_{s2}-r0, s a permutation, up to symmetry
            seen = set()
            for s in permutations(range(3)):
                edges = frozenset([(0, s[0]), (1, s[0]), (1, s[1]), (2, s[1]), (2, s[2]), (0, s[2])])
                if edges in seen:
                    continue
                seen.add(edges)
                cl.append([-v(R[a], C[b]) for a, b in edges])
    return cl


def faxis(h, m, lo):
    base = clauses(h, m)
    n = h * m
    best = None
    k = lo
    while True:
        card = CardEnc.atleast(lits=list(range(1, n + 1)), bound=k, top_id=n, encoding=EncType.seqcounter)
        # symmetry breaking: first row has its edges first (lex-leader light): row 0 degree >= others not imposed
        with Solver(name='cadical153', bootstrap_with=base + card.clauses) as s:
            if s.solve():
                best = k
                k += 1
            else:
                return best


if __name__ == '__main__':
    out = {}
    H = int(sys.argv[1]); M = int(sys.argv[2])
    for h in range(3, H + 1):
        for m in range(h, M + 1):
            t = time.time()
            val = faxis(h, m, h + m - 1)
            out[f'{h}x{m}'] = val
            print(h, m, val, f'{time.time()-t:.1f}s', flush=True)
    json.dump(out, open(f'faxis_{H}_{M}.json', 'w'))
