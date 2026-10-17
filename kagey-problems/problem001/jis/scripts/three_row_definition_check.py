"""Definitional recount of the three-row optima, widths 3..10.

Rectangles of the 3 x m grid are generated from right-angle triples of
points (P, Q, R with (Q-P).(R-P) = 0 and fourth corner Q+R-P), independently
of the equal-diagonal enumerator in verify_narrow.py, against which the lists
are compared.  A blackout is valid when the visible corner sets of all
rectangles are pairwise distinct (the empty set counts as a value).  The
valid (m+2)-point blackouts are enumerated column by column with the suffix
bound f(3, j) <= j+2, which the same search proves inductively for j <= m by
finding no (j+3)-point blackout (f(3,1) = 3 and f(3,2) = 4 by exhausting all
subsets).  The optima are then converted to column words, the row reflection,
column reversal and half turn are applied directly to the point sets, the
fixed counts and orbit counts are taken, and a forbidden three-letter window
table per class is extracted from the optima of width <= 8 and tested against
every optimum found at every width.

Internal coordinates are zero-based (column, row) with bit 3*column + row;
every coordinate written to the output is one-based (column, row), (1,1) top
left, as in verify_narrow.py.
"""
import json
import os
import random
import sys
import time
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
PROBLEM = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, PROBLEM)
import verify_narrow  # noqa: E402

OUT = os.path.join(os.path.dirname(HERE), 'data', 'three_row_definition_check.json')
WALL_CAP = 19 * 60
START = time.time()
LETTER = {0: '_', 1: 'a', 2: 'b', 4: 'c', 3: 'A', 5: 'B', 6: 'C', 7: 'X'}
POP = [bin(p).count('1') for p in range(8)]


class OutOfTime(Exception):
    pass


def rectangles_by_triples(m):
    """All rectangles (tilted included) of the 3 x m grid as bitmasks."""
    pts = [(x, y) for x in range(m) for y in range(3)]
    index = {p: 3 * p[0] + p[1] for p in pts}
    found = set()
    for P in pts:
        for Q in pts:
            if Q == P:
                continue
            ux, uy = Q[0] - P[0], Q[1] - P[1]
            for R in pts:
                if R == P or R == Q:
                    continue
                vx, vy = R[0] - P[0], R[1] - P[1]
                if ux * vx + uy * vy:
                    continue
                F = (Q[0] + R[0] - P[0], Q[1] + R[1] - P[1])
                if F in index:
                    found.add((1 << index[P]) | (1 << index[Q]) | (1 << index[R]) | (1 << index[F]))
    return sorted(found)


def to_vn(mask, m):
    """Translate a mask from bit 3*col+row to verify_narrow's bit row*m+col."""
    out = 0
    b = mask
    while b:
        low = b & -b
        i = low.bit_length() - 1
        col, row = divmod(i, 3)
        out |= 1 << (row * m + col)
        b ^= low
    return out


def is_valid(S, rects):
    seen = set()
    for R in rects:
        v = R & ~S
        if v in seen:
            return False
        seen.add(v)
    return True


def search(m, target, rects, deadline):
    """All valid blackouts of exactly `target` points on the 3 x m grid.

    Uses the suffix bound f(3, j) <= j + 2 (j >= 1) for the columns not yet
    placed; the caller guarantees that bound for j < m.
    """
    by_col = [[] for _ in range(m)]
    for R in rects:
        by_col[max(i // 3 for i in range(3 * m) if R >> i & 1)].append(R)
    found = []
    seen = set()

    def rec(k, S, cnt):
        if k == m:
            if cnt == target:
                found.append(S)
            return
        if k <= 2 and time.time() > deadline:
            raise OutOfTime
        rem = m - k - 1
        low = target - (rem + 2) if rem >= 1 else target
        shift = 3 * k
        news = by_col[k]
        for p in range(8):
            c2 = cnt + POP[p]
            if c2 < low or c2 > target:
                continue
            S2 = S | (p << shift)
            added = []
            ok = True
            for R in news:
                v = R & ~S2
                if v in seen:
                    ok = False
                    break
                seen.add(v)
                added.append(v)
            if ok:
                rec(k + 1, S2, c2)
            for v in added:
                seen.discard(v)

    rec(0, 0, 0)
    return found


def word(S, m):
    return ''.join(LETTER[(S >> (3 * j)) & 7] for j in range(m))


def points_one_based(S, m):
    return [[j + 1, i + 1] for j in range(m) for i in range(3) if S >> (3 * j + i) & 1]


def reflect(S, m):
    out = 0
    for j in range(m):
        p = (S >> (3 * j)) & 7
        q = ((p & 1) << 2) | (p & 2) | ((p & 4) >> 2)
        out |= q << (3 * j)
    return out


def reverse(S, m):
    out = 0
    for j in range(m):
        out |= ((S >> (3 * j)) & 7) << (3 * (m - 1 - j))
    return out


def classify(w):
    """Class of a candidate word: 'AC', 'AB', 'BC', 'X', or None."""
    if '_' in w:
        return None
    doubles = [ch for ch in w if ch in 'ABC']
    xs = w.count('X')
    if xs == 1 and not doubles:
        return 'X'
    if xs == 0 and len(doubles) == 2 and doubles[0] != doubles[1]:
        return ''.join(sorted(doubles))
    return None


def class_alphabet(K):
    return ['a', 'b', 'c'] + (['X'] if K == 'X' else list(K))


def all_windows(K):
    need = set('X') if K == 'X' else set(K)
    out = []
    for x in class_alphabet(K):
        for y in class_alphabet(K):
            for z in class_alphabet(K):
                t = x + y + z
                if all(t.count(ch) <= 1 for ch in need):
                    out.append(t)
    return out


def count_words(K, m, forbidden):
    """Class-K words of length m avoiding the forbidden windows (DP)."""
    letters = class_alphabet(K)
    need = frozenset('X') if K == 'X' else frozenset(K)
    states = defaultdict(int)
    states[('', '', frozenset())] = 1
    for _ in range(m):
        new = defaultdict(int)
        for (p2, p1, used), cnt in states.items():
            for L in letters:
                if L in need and L in used:
                    continue
                if p2 and (p2 + p1 + L) in forbidden:
                    continue
                u = used | {L} if L in need else used
                new[(p1, L, u)] += cnt
        states = new
    return sum(cnt for (p2, p1, used), cnt in states.items() if used == need)


def main():
    random.seed(1)
    result = {
        'date': '2026-10-17',
        'python': sys.version.split()[0],
        'coordinates': 'one-based (column, row), (1,1) top left',
        'method': 'rectangles from right-angle triples; visible-set dictionary; column search with suffix bound',
        'rectangle_lists_agree_with_verify_narrow': {},
        'validity_agrees_with_verify_narrow_random': {},
        'base_cases': {},
        'widths': {},
        'window_table': None,
        'window_table_tested_through': None,
        'completed_widths': [],
        'unresolved_widths': [],
    }
    # rectangle lists against the equal-diagonal enumerator
    for m in list(range(1, 21)) + [30]:
        mine = {to_vn(R, m) for R in rectangles_by_triples(m)}
        theirs = set(verify_narrow.rectangles(3, m))
        result['rectangle_lists_agree_with_verify_narrow'][m] = (mine == theirs, len(mine))
        assert mine == theirs, m
    # base cases by exhausting every subset
    for m in (1, 2):
        rects = rectangles_by_triples(m)
        best = max(bin(S).count('1') for S in range(1 << (3 * m)) if is_valid(S, rects))
        result['base_cases'][m] = best
    assert result['base_cases'] == {1: 3, 2: 4}

    deadline = START + WALL_CAP
    windows_seen = {K: set() for K in ('AC', 'AB', 'BC', 'X')}
    table = None
    for m in range(3, 11):
        t0 = time.time()
        rects = rectangles_by_triples(m)
        rects_vn = verify_narrow.rectangles(3, m)
        # random validity cross-check against verify_narrow.collision
        agree = True
        for _ in range(3000):
            size = random.randint(m, m + 3)
            S = 0
            for i in random.sample(range(3 * m), size):
                S |= 1 << i
            mine = is_valid(S, rects)
            theirs = verify_narrow.collision(rects_vn, to_vn(S, m)) is None
            agree = agree and (mine == theirs)
        result['validity_agrees_with_verify_narrow_random'][m] = agree
        assert agree
        try:
            bigger = search(m, m + 3, rects, deadline)
            optima = search(m, m + 2, rects, deadline)
        except OutOfTime:
            result['unresolved_widths'].append(m)
            break
        assert not bigger, (m, len(bigger))
        info = {'rectangles': len(rects), 'no_valid_set_of_size_m_plus_3': True,
                'a3': len(optima)}
        words = {}
        per_class = defaultdict(int)
        for S in optima:
            w = word(S, m)
            K = classify(w)
            assert K is not None, (m, w)
            words[S] = (w, K)
            per_class[K] += 1
        info['all_optima_are_candidate_words'] = True
        info['per_class'] = dict(per_class)
        # every optimum rechecked by verify_narrow.collision (sample at large m)
        sample = optima if len(optima) <= 20000 else random.sample(optima, 20000)
        assert all(verify_narrow.collision(rects_vn, to_vn(S, m)) is None for S in sample)
        info['optima_rechecked_by_verify_narrow'] = len(sample)
        # group action on the point sets
        opt = set(optima)
        fixed = {'reflection': [], 'reversal': [], 'half_turn': []}
        reps = set()
        hist = defaultdict(int)
        for S in optima:
            r = reflect(S, m)
            v = reverse(S, m)
            h = reverse(r, m)
            assert r in opt and v in opt and h in opt
            if r == S:
                fixed['reflection'].append(S)
            if v == S:
                fixed['reversal'].append(S)
            if h == S:
                fixed['half_turn'].append(S)
            rep = min(S, r, v, h)
            if rep not in reps:
                reps.add(rep)
                hist[len({S, r, v, h})] += 1
        info['closed_under_group'] = True
        info['fixed'] = {g: len(v) for g, v in fixed.items()}
        info['orbits'] = len(reps)
        info['orbit_size_histogram'] = dict(hist)
        total = len(optima) + sum(info['fixed'].values())
        info['burnside'] = total % 4 == 0 and total // 4 == len(reps)
        if m <= 5:
            info['fixed_words'] = {g: sorted(words[S][0] for S in v) for g, v in fixed.items()}
            info['fixed_points_one_based'] = {g: {words[S][0]: points_one_based(S, m) for S in v}
                                              for g, v in fixed.items()}
        # windows for the table
        if m <= 8:
            for S, (w, K) in words.items():
                for i in range(m - 2):
                    windows_seen[K].add(w[i:i + 3])
        if m == 8:
            table = {K: sorted(set(all_windows(K)) - windows_seen[K]) for K in windows_seen}
            result['window_table'] = table
            result['window_table_sizes'] = {K: len(v) for K, v in table.items()}
        if table is not None:
            # every optimum avoids its class table, and the table DP reproduces the class counts
            avoid = all(not any(w[i:i + 3] in table[K] for i in range(m - 2))
                        for S, (w, K) in words.items())
            dp = {K: count_words(K, m, set(table[K])) for K in table}
            info['optima_avoid_table'] = avoid
            info['table_dp_counts'] = dp
            info['table_dp_matches_per_class'] = all(dp[K] == per_class.get(K, 0) for K in dp)
            assert avoid and info['table_dp_matches_per_class'], m
            result['window_table_tested_through'] = m
        info['seconds'] = round(time.time() - t0, 1)
        result['widths'][m] = info
        result['completed_widths'].append(m)
        result['elapsed_seconds'] = round(time.time() - START, 1)
        with open(OUT, 'w') as f:
            json.dump(result, f, indent=1)
        print(m, info['a3'], info['fixed'], info['orbits'], info['seconds'], flush=True)
    if table is not None:
        # retrospective check of the table at widths 3..8 by DP counts
        ok = True
        for m in range(3, 9):
            if m in result['widths']:
                dp = {K: count_words(K, m, set(table[K])) for K in table}
                ok = ok and all(dp[K] == result['widths'][m]['per_class'].get(K, 0) for K in dp)
        result['table_dp_matches_3_to_8'] = ok
    result['elapsed_seconds'] = round(time.time() - START, 1)
    with open(OUT, 'w') as f:
        json.dump(result, f, indent=1)
    print('done', result['completed_widths'], result['unresolved_widths'])


if __name__ == '__main__':
    main()
