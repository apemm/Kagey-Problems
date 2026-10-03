"""Run 4 (ledger G14, G15, G16): the tree of F(X) = X + lambda, G(X) = -1/X from 0 at q = 5.

lambda = 2 cos(pi/5) = (1 + sqrt 5)/2. Numbers a + b sqrt5 are pairs of Fractions, exact.
Method 1: BFS. Method 2: reduced strings, evaluated directly. Method 3: series of N_5/D_5.
Usage: python q5.py depth
"""
import sys
from fractions import Fraction as Fr

Z = (Fr(0), Fr(0))
LAM = (Fr(1, 2), Fr(1, 2))


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def sub(x, y):
    return (x[0] - y[0], x[1] - y[1])


def sign(x):
    a, b = x
    if a >= 0 and b >= 0:
        return 0 if (a == 0 and b == 0) else 1
    if a <= 0 and b <= 0:
        return -1
    # mixed signs: compare a^2 with 5 b^2
    if a > 0:
        return 1 if a * a > 5 * b * b else -1
    return 1 if 5 * b * b > a * a else -1


def G(x):
    a, b = x
    n = a * a - 5 * b * b
    assert n != 0
    return (-a / n, b / n)


def bfs(depth):
    rank = {Z: 0}
    via = {Z: set()}
    layer = [Z]
    counts = [1]
    for n in range(1, depth + 1):
        nxt = []
        for x in layer:
            kids = [(add(x, LAM), 'F')]
            if x != Z:
                kids.append((G(x), 'G'))
            for c, how in kids:
                if c not in rank:
                    rank[c] = n
                    via[c] = {how}
                    nxt.append(c)
                elif rank[c] == n:
                    via[c].add(how)
        layer = nxt
        counts.append(len(layer))
    return rank, via, counts


def strings(q, D):
    """All reduced strings of weight <= D, as (value, weight). Raises on a pole."""
    out = []
    for c1 in range(D + 1):
        out.append(((Fr(c1) * LAM[0], Fr(c1) * LAM[1]), c1))
    # build c_k, ..., c_2 then c_1; state: value Y = [c_j..c_k], weight of c_j..c_k plus their g's,
    # current left run of ones r (counting c_j), and whether all digits so far are ones (run touches c_k)
    stack = []
    for ck in range(1, D):
        y = (Fr(ck) * LAM[0], Fr(ck) * LAM[1])
        stack.append((y, ck + 1, 1 if ck == 1 else 0))
    while stack:
        y, w, r = stack.pop()
        # y is the tail [c_2..c_k]; close the word with c_1 >= 0
        assert sign(y) != 0
        gy = G(y)
        for c1 in range(0, D - w + 1):
            if c1 >= 1 and r >= q - 2:
                continue
            if c1 == 0 and r > q - 2:
                continue
            out.append((add(gy, (Fr(c1) * LAM[0], Fr(c1) * LAM[1])), w + c1))
        # extend with another interior digit c (left of the current ones)
        if r >= q - 2:
            continue  # the run is already q - 2 long, only c_1 = 0 may close it
        for c in range(1, D - w):
            nr = r + 1 if c == 1 else 0
            if nr >= q - 1:
                continue
            ny = add(gy, (Fr(c) * LAM[0], Fr(c) * LAM[1]))
            stack.append((ny, w + c + 1, nr))
    return out


def series(D):
    N = [1, 0, 1, 0, 1, 0, 1, -1]
    Dq = [1, -1, 0, -1, 0, -1, 0, -1]
    a = []
    for n in range(D + 1):
        s = N[n] if n < len(N) else 0
        for j in range(1, len(Dq)):
            if n - j >= 0:
                s -= Dq[j] * a[n - j]
        a.append(s)
    return a


def parent_steps(x):
    n = 0
    while x != Z:
        x = sub(x, LAM) if sign(x) > 0 else G(x)
        n += 1
        assert n < 10 ** 4
    return n


if __name__ == '__main__':
    D = int(sys.argv[1])
    rank, via, counts = bfs(D)
    print('BFS counts', counts)
    ser = series(D)
    print('N5/D5    ', ser)
    print('G14 counts equal:', counts == ser)
    rec = [n for n in range(7, D + 1)
           if counts[n] != counts[n - 1] + counts[n - 3] + counts[n - 5] + counts[n - 7]]
    print('recurrence fails at', rec)
    st = strings(5, D)
    vals = {}
    coll = 0
    for v, w in st:
        if v in vals:
            coll += 1
        vals[v] = w
    wrong = sum(1 for v, w in st if rank.get(v) != w)
    missed = sum(1 for x in rank if x not in vals)
    print('G15 strings', len(st), 'collisions', coll, 'wrong rank', wrong, 'missed', missed)
    bad_p = sum(1 for x, r in rank.items() if parent_steps(x) != r)
    bad_c = sum(1 for x in rank if x != Z and (via[x] != ({'G'} if sign(x) < 0 else {'F'})))
    print('G16 parent-step mismatches', bad_p, 'color mismatches', bad_c, 'points', len(rank))
