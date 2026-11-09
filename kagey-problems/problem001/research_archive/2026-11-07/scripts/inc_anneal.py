"""Incremental simulated annealing for "1, x, h" boards (spacing 4) with free transition gaps.

Layout (as in cegar_board.py, MODE hyb): W pad columns of row PL, the q doubles of K_{odd,even} at
columns W + 4j, three sea columns between consecutive doubles, then W pad columns of row PR. Gaps
j < TR and j >= q - 1 - TR have free sea cells (any row); the other gaps are 1, x, h with x in {1, h}.

The cost is exactly the violation count of fastcheck.violations (hidden rectangles + for each white
set P with n_P >= 1 rectangles of >= 2 black corners: (n_P - 1) + [P has an axis-aligned rival]),
maintained incrementally: a move changes one or two columns, and only placements with a corner in
those columns are re-evaluated. F is all pairs at odd distance (every edge of K_{odd,even} is used).

Moves: swap two doubles (optionally only within a class given by RULE), flip a middle cell, re-draw a
free transition cell. Usage:
  py inc_anneal.py h TR PL PR seconds seed [T0] [T1]
Env: RULE=mod4:j0 keeps the slot rule of Prop 18 in slots RULE_TR..q-1-RULE_TR (swaps stay inside the
residue class of the slot); OUT=file for the json of a valid board."""
import sys, os, json, time, random
import numpy as np
from numba import njit, types
from numba.typed import Dict
from fastcheck import shapes


@njit(cache=True)
def place_eval(S, s, x0, col, h):
    """Return (nblack, key) for placement s at x0. key = -1 if hidden, -2 if < 2 black."""
    nb = 0
    w0 = -1
    w1 = -1
    for k in range(4):
        x = x0 + S[s, k, 0]
        r = S[s, k, 1]
        if (col[x] >> r) & 1:
            nb += 1
        else:
            c = x * 32 + r
            if w0 < 0:
                w0 = c
            else:
                w1 = c
    if nb < 2:
        return nb, -2
    if nb == 4:
        return nb, -1
    if w1 < 0:
        return nb, w0 * 65536 + 65535
    if w1 < w0:
        w0, w1 = w1, w0
    return nb, w0 * 65536 + w1


@njit(cache=True)
def rival(key, col):
    w1 = key % 65536
    w0 = key // 65536
    x = w0 // 32
    r = w0 % 32
    if w1 == 65535:
        m = col[x]
        for t in range(1, 32):
            if (m >> t) & 1 and t != r and (t - r) % 2 != 0:
                return 1
        return 0
    z = w1 // 32
    s = w1 % 32
    if x == z:
        return 1 if (r - s) % 2 != 0 else 0
    if r == s:
        return 1 if (col[x] & col[z]) != 0 else 0
    return 1 if ((col[x] >> s) & 1) and ((col[z] >> r) & 1) else 0


@njit(cache=True)
def kcost(n, rv):
    if n <= 0:
        return 0
    return n - 1 + rv


@njit(cache=True)
def full_init(S, span, col, h, cnt, rvd):
    m = col.shape[0]
    hidden = 0
    for s in range(S.shape[0]):
        for x0 in range(0, m - span[s]):
            nb, key = place_eval(S, s, x0, col, h)
            if key == -1:
                hidden += 1
            elif key >= 0:
                if key in cnt:
                    cnt[key] += 1
                else:
                    cnt[key] = 1
                    rvd[key] = rival(key, col)
    cost = hidden
    for key in cnt:
        cost += kcost(cnt[key], rvd[key])
    return cost


@njit(cache=True)
def touch(S, span, m, cols_changed, nch, s, k):
    """placements of shape s whose corner k lies on one of the changed columns; returns list of x0
    that are not counted by an earlier (column, corner) pair."""
    pass


@njit(cache=True)
def update(S, span, col, h, cnt, rvd, chx, newv, sign_only):
    """Apply column changes chx[i] -> newv[i]; return cost delta. Placements touching several changed
    columns are processed once (first changed column, first corner on it)."""
    m = col.shape[0]
    nc = chx.shape[0]
    delta = 0
    for phase in range(2):
        if phase == 1:
            for i in range(nc):
                col[chx[i]] = newv[i]
        for i in range(nc):
            c = chx[i]
            for s in range(S.shape[0]):
                for k in range(4):
                    x0 = c - S[s, k, 0]
                    if x0 < 0 or x0 >= m - span[s]:
                        continue
                    # dedup: skip if an earlier corner of this placement is on c, or any corner on an
                    # earlier changed column
                    dup = False
                    for kk in range(k):
                        if x0 + S[s, kk, 0] == c:
                            dup = True
                    if not dup:
                        for ii in range(i):
                            for kk in range(4):
                                if x0 + S[s, kk, 0] == chx[ii]:
                                    dup = True
                    if dup:
                        continue
                    nb, key = place_eval(S, s, x0, col, h)
                    if key == -2:
                        continue
                    if key == -1:
                        delta += 1 if phase == 1 else -1
                        continue
                    if phase == 0:
                        n = cnt[key]
                        rv = rvd[key]
                        delta -= kcost(n, rv)
                        cnt[key] = n - 1
                        delta += kcost(n - 1, rv)
                    else:
                        if key in cnt and cnt[key] > 0:
                            n = cnt[key]
                            rv = rvd[key]
                        else:
                            n = 0
                            rv = rival(key, col)
                            rvd[key] = rv
                        delta -= kcost(n, rv)
                        cnt[key] = n + 1
                        delta += kcost(n + 1, rv)
    return delta


def build(h, TR, PL, PR):
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    q = len(E)
    W = int(os.environ.get('PADW', 1 + (h - 1) ** 2 // 4))
    m = 2 * W + q + 3 * (q - 1)
    return E, q, W, m


def v2(n):
    c = 0
    while n % 2 == 0:
        n //= 2; c += 1
    return c


def main():
    h, TR, PL, PR = map(int, sys.argv[1:5]); secs = float(sys.argv[5]); seed = int(sys.argv[6])
    T0 = float(sys.argv[7]) if len(sys.argv) > 7 else 2.0
    T1 = float(sys.argv[8]) if len(sys.argv) > 8 else 0.05
    rng = random.Random(seed)
    E, q, W, m = build(h, TR, PL, PR)
    rows = list(range(1, h + 1))
    RULE = os.environ.get('RULE')
    RTR = int(os.environ.get('RULE_TR', TR))
    # slot classes
    def tauw(e):
        o = e[0] if e[0] % 2 else e[1]
        if o in (1, h):
            return None
        if o % 4 == 1:
            t = v2(o - 1); return t, ((o - 1) >> t) % 4
        t = v2(h - o); return t, (-((h - o) >> t)) % 4
    def eclass(e):
        ev = e[0] if e[0] % 2 == 0 else e[1]
        tw = tauw(e)
        if tw and tw[0] == 2:
            return 0 if tw[1] == 1 else 2
        return 1 if ev % 4 == 0 else 3
    j0 = int(RULE.split(':')[1]) if RULE and ':' in RULE else 0
    ruled = (lambda j: RULE is not None and RTR <= j <= q - 1 - RTR)
    # initial order
    order = E[:]; rng.shuffle(order)
    if RULE:
        pools = {c: [e for e in order if eclass(e) == c] for c in range(4)}
        slots = [j for j in range(q) if ruled(j)]
        free = [j for j in range(q) if not ruled(j)]
        order = [None] * q
        for j in slots:
            c = (j - j0) % 4
            if pools[c]:
                order[j] = pools[c].pop()
        rest = [e for c in range(4) for e in pools[c]]; rng.shuffle(rest)
        for j in range(q):
            if order[j] is None:
                order[j] = rest.pop()
        bad = sum(1 for j in slots if eclass(order[j]) != (j - j0) % 4)
        print('rule slots', len(slots), 'violating rule at start', bad, flush=True)
    if os.environ.get('ORDERFILE'):
        order = [tuple(sorted(e)) for e in json.load(open(os.environ['ORDERFILE']))]
        assert sorted(order) == sorted(E)
    SAMEODD = os.environ.get('SAMEODD') == '1'
    PSWAP = float(os.environ.get('PSWAP', 0.5))
    col = np.zeros(m, dtype=np.int64)
    dcol = lambda j: W + 4 * j
    for x in range(W):
        col[x] = 1 << PL; col[m - 1 - x] = 1 << PR
    seadom = {}
    for j in range(q):
        a, b = order[j]; col[dcol(j)] = (1 << a) | (1 << b)
        if j < q - 1:
            for i in range(3):
                x = dcol(j) + 1 + i
                if j < TR or j >= q - 1 - TR:
                    dom = rows
                else:
                    dom = [[1], [1, h], [h]][i]
                seadom[x] = dom
                col[x] = 1 << rng.choice(dom)
    if os.environ.get('INITFILE'):
        ib = json.load(open(os.environ['INITFILE']))
        order = [tuple(e) for e in ib['order']]
        for x in range(m):
            col[x] = sum(1 << r for r in ib['cols'][x])
    S0 = shapes(h)
    S = np.array([[list(c) for c in sh] for sh in S0], dtype=np.int64)
    span = S[:, :, 0].max(axis=1).astype(np.int64)
    cnt = Dict.empty(key_type=types.int64, value_type=types.int64)
    rvd = Dict.empty(key_type=types.int64, value_type=types.int64)
    t0 = time.time()
    cost = full_init(S, span, col, h, cnt, rvd)
    print('init cost', cost, 'time', round(time.time() - t0, 1), flush=True)
    varsea = [x for x, d in seadom.items() if len(d) > 1]
    swappable = list(range(q))
    best = cost; it = 0; last = time.time(); tstart = time.time()
    while True:
        it += 1
        el = time.time() - tstart
        if el > secs:
            break
        T = T0 * (T1 / T0) ** (el / secs)
        u = rng.random()
        if u < PSWAP:
            i = rng.randrange(q); j = rng.randrange(q)
            if i == j:
                continue
            if RULE and (ruled(i) or ruled(j)):
                ci = (i - j0) % 4 if ruled(i) else None
                cj = (j - j0) % 4 if ruled(j) else None
                if ruled(i) and eclass(order[j]) != ci:
                    continue
                if ruled(j) and eclass(order[i]) != cj:
                    continue
            if SAMEODD and (order[i][0] % 2 and order[i][0] or order[i][1]) != (order[j][0] % 2 and order[j][0] or order[j][1]):
                continue
            a, b = order[i]; c, d = order[j]
            chx = np.array([dcol(i), dcol(j)], dtype=np.int64)
            nv = np.array([(1 << c) | (1 << d), (1 << a) | (1 << b)], dtype=np.int64)
            ov = np.array([col[dcol(i)], col[dcol(j)]], dtype=np.int64)
            dl = update(S, span, col, h, cnt, rvd, chx, nv, False)
            if dl <= 0 or rng.random() < np.exp(-dl / T):
                cost += dl; order[i], order[j] = order[j], order[i]
            else:
                update(S, span, col, h, cnt, rvd, chx, ov, False)
        else:
            x = rng.choice(varsea); dom = seadom[x]
            r = rng.choice(dom)
            if col[x] == (1 << r):
                continue
            chx = np.array([x], dtype=np.int64); nv = np.array([1 << r], dtype=np.int64)
            ov = np.array([col[x]], dtype=np.int64)
            dl = update(S, span, col, h, cnt, rvd, chx, nv, False)
            if dl <= 0 or rng.random() < np.exp(-dl / T):
                cost += dl
            else:
                update(S, span, col, h, cnt, rvd, chx, ov, False)
        if cost < best:
            best = cost
        if time.time() - last > 30:
            print('t', round(el), 'it', it, 'T', round(T, 3), 'cost', cost, 'best', best, flush=True); last = time.time()
        if cost == 0:
            break
    cols = [sorted(r for r in rows if (int(col[x]) >> r) & 1) for x in range(m)]
    from cegar_board import check
    n, _ = check(h, [set(c) for c in cols])
    print('final cost', cost, 'check', n, 'iters', it, flush=True)
    out = os.environ.get('OUT', 'inc_h%d_t%d_s%d.json' % (h, TR, seed))
    json.dump({'h': h, 'TR': TR, 'W': W, 'pads': [PL, PR], 'cost': int(cost), 'check': n,
               'order': order, 'cols': cols}, open(out, 'w'))


if __name__ == '__main__':
    main()
