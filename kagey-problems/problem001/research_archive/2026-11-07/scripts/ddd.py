"""Count three-double right angles (law (i)) of an order, split by the parity of the vertex row.
Points (4j, r) for r in edge j. A right angle at (4j, rj) with legs to (4i, ri), (4k, rk), i, k != j,
is a violation when the fourth corner (4(i+k-j), ri+rk-rj) is in the grid (rows 1..h, slots 0..q-1)."""
import sys, json, random
def count(h, order, window=None):
    q = len(order); res = {'odd': 0, 'even': 0}
    pts = [(j, r) for j, e in enumerate(order) for r in e]
    L = (h - 1) ** 2 // 64 + 2
    for j, e in enumerate(order):
        for rj in e:
            for i in range(max(0, j - L), min(q, j + L + 1)):
                if i == j: continue
                for ri in order[i]:
                    for k in range(i + 1, min(q, j + L + 1)):
                        if k == j: continue
                        for rk in order[k]:
                            if 16 * (i - j) * (k - j) + (ri - rj) * (rk - rj) == 0:
                                x = i + k - j; y = ri + rk - rj
                                if 0 <= x < q and 1 <= y <= h:
                                    res['odd' if rj % 2 else 'even'] += 1
    return res
if __name__ == '__main__':
    h = int(sys.argv[1]); k = (h - 1) // 2; rng = random.Random(1)
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    for trial in range(3):
        o = E[:]; rng.shuffle(o); print('random', count(h, o))
    M = int(sys.argv[2])  # power of 2 dividing k+1
    for trial in range(3):
        # a_j = (j mod M) + M * g(j), g constant on blocks of length k*M
        perms = {}
        order = []
        for j in range(k * (k + 1)):
            a = (j % M) + M * (j // (k * M)); o_ = 2 * a + 1
            perms.setdefault(a, rng.sample(range(2, h, 2), k))
            order.append(tuple(sorted((o_, perms[a].pop()))))
        assert sorted(order) == sorted(E)
        print('a-structured M=%d' % M, count(h, order))
