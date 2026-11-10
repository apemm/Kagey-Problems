"""Bounded search for the equality threshold at height 8 or 9. One process, one solver at a time.

Usage:  py sat_threshold_run.py HEIGHT [TOTAL_SECONDS] [LOWER_SECONDS]

Phase 1 (lower bound). For w = q_h, q_h + 1, ... every balanced row partition
(one per vertical reflection class) is tested at width w with the exact encoder.
A width counts as excluded only when every partition returns UNSAT.

Phase 2 (upper bound). The board is: w free columns with every double among the
first b of them, then W_h columns black in row 1 only. By the finite collar
theorem a valid board of this form extends by any number of further row-1
columns, and its prefixes of width at least b are valid by restriction and keep
all doubles, so equality holds at every width from b on. The search starts from
the stored collar board (b = 46 at height 8, b = 58 at height 9), lowers b, and
warm starts the solver from the current board with singleton columns deleted.
Only the parity partition is used in this phase.

Every board that is accepted is checked with rectlib.check_board.
"""
import json, random, sys, time
from equality_sat import *
from rectlib import check_board

T0 = time.monotonic()
h = int(sys.argv[1])
TOTAL = float(sys.argv[2]) if len(sys.argv) > 2 else 2340.0
LOWER = float(sys.argv[3]) if len(sys.argv) > 3 else 480.0
q = (h * h) // 4
W = ((h - 1) ** 2) // 4 + 1
EXTRA = 3          # free singleton columns between the last allowed double column and the pad
OUT = HERE / f'sat_threshold_h{h}.json'
log = {'height': h, 'doubles': q, 'collar_W': W, 'total_budget_seconds': TOTAL,
       'lower_budget_seconds': LOWER, 'solver': 'cadical195', 'lower': [], 'upper': [], 'status': 'running'}


def elapsed():
    return time.monotonic() - T0


def save():
    log['elapsed_seconds'] = round(elapsed(), 1)
    OUT.write_text(json.dumps(log, indent=1))


CORES = {
    8: "25,3,3,36,7,3,47,7,7,58,8,8,78,8,7,27,8,7,67,6,6,56,5,5,45,4,4,34,3,2,23,3,4,38,1,1,16,2,2,14,1,1,18,8,4,12",
    9: "27,8,1,16,6,1,78,8,1,67,6,6,56,5,5,45,4,3,34,4,3,23,2,1,12,1,1,29,2,1,14,1,9,69,9,2,49,1,9,38,8,8,"
       "89,9,9,18,8,8,58,7,7,47,3,7,36,3,3,25",
}
geo = Geometry(h)
save()

# ---------------- phase 1: lower bound ----------------
parts = partitions(h)
sup_cache = {}
excluded_below = q          # equality is impossible for m < q_h (paper, small-m corollary)
w = q
stop = False
while not stop:
    rec = {'width': w, 'partitions': len(parts), 'results': [], 'complete': False}
    log['lower'].append(rec)
    for A in parts:
        if A not in sup_cache:
            sup_cache[A] = supports(geo, A)
        cl, nv = encode(h, w, A, sup_cache[A])
        cap = LOWER - elapsed()
        if cap <= 0:
            stop = True; break
        st, model, sec, stats = solve(cl, cap)
        r = {'A_rows': [x + 1 for x in A], 'status': st, 'seconds': round(sec, 2),
             'conflicts': stats.get('conflicts')}
        if st == 'SAT':
            b = board_from_model(h, w, model)
            r['word'] = word(b); r['check'] = check_board(h, b)
        rec['results'].append(r)
        save()
        if st != 'UNSAT':
            stop = True; break
    else:
        rec['complete'] = True
        rec['all_unsat'] = all(r['status'] == 'UNSAT' for r in rec['results'])
        rec['seconds'] = round(sum(r['seconds'] for r in rec['results']), 1)
        if rec['all_unsat']:
            excluded_below = w + 1
        save()
        w += 1
log['equality_impossible_below_width'] = excluded_below
sup_cache.clear()
save()

# ---------------- phase 2: upper bound ----------------
rng = random.Random(2026)
A = tuple(r for r in range(h) if r % 2 == 1)
sup = supports(geo, A)
core = [[int(ch) for ch in tok] for tok in CORES[h].split(',')]


def last_double(cols):
    return max(i for i, c in enumerate(cols) if len(c) == 2) + 1


def padded(cols):
    return cols + [[1]] * W


best = core + [[1]] * EXTRA           # free part of the current board
chk = check_board(h, padded(best))
log['start'] = {'b': last_double(best), 'word': word(best), 'padded_check': chk}
assert chk['valid']
save()


def candidate(cols, b_new):
    """Delete singleton columns before the last double until it sits at column b_new; keep length b_new + EXTRA."""
    cols = [list(c) for c in cols]
    while last_double(cols) > b_new:
        ld = last_double(cols)
        singles = [i for i in range(ld) if len(cols[i]) == 1]
        if not singles:
            return None
        del cols[rng.choice(singles)]
    cols = cols[:b_new + EXTRA]
    while len(cols) < b_new + EXTRA:
        cols.append([1])
    return cols


def phases_of(cols, wfree):
    ph = []
    for c in range(wfree + W):
        rows = cols[c] if c < len(cols) else [1]
        for r in range(h):
            v = c * h + r + 1
            ph.append(v if (r + 1) in rows else -v)
    return ph


def attempt(b_new, cap):
    from pysat.solvers import Solver
    wfree = b_new + EXTRA
    cl, nv = encode(h, wfree + W, A, sup, label_width=b_new, fixed_tail=(wfree, 0), anchor=False)
    t0 = time.monotonic(); tries = 0; res = None; model = None
    with Solver(name='cadical195', bootstrap_with=cl) as s:
        while res is None and time.monotonic() - t0 < cap:
            cand = candidate(best, b_new)
            if cand is None:
                break
            s.set_phases(phases_of(cand, wfree)); tries += 1
            t1 = time.monotonic()
            while res is None and time.monotonic() - t1 < 25 and time.monotonic() - t0 < cap:
                s.conf_budget(3000)
                res = s.solve_limited()
        if res:
            model = s.get_model()
        stats = s.accum_stats()
    st = 'SAT' if res else ('UNSAT' if res is False else 'unknown')
    rec = {'b': b_new, 'free_columns': wfree, 'pad_columns': W, 'variables': nv, 'clauses': len(cl),
           'status': st, 'warm_starts': tries, 'seconds': round(time.monotonic() - t0, 1),
           'conflicts': stats.get('conflicts')}
    board = None
    if model:
        full = board_from_model(h, wfree + W, model)
        board = full[:wfree]
        rec['word'] = word(board)
        rec['last_double_column'] = last_double(board)
        rec['padded_check'] = check_board(h, full)
    return rec, board


step = 2
b = last_double(best)
while True:
    remaining = TOTAL - 60 - elapsed()
    if remaining < 20:
        break
    target = b - step
    cap = min(remaining, 75.0) if step > 1 else remaining
    rec, board = attempt(target, cap)
    rec['step'] = step
    log['upper'].append(rec); save()
    if board is not None and rec['padded_check']['valid']:
        best = board
        b = last_double(best)            # can be smaller than the target
        log['best'] = {'b': b, 'word': word(best), 'padded_word': word(padded(best)),
                       'padded_check': rec['padded_check']}
        save()
    elif rec['status'] == 'UNSAT':
        if step == 1:
            log['parity_collar_unsat_at_b'] = target
            break
        step = 1
    else:
        if step == 1:
            break
        step = 1

if 'best' not in log:
    log['best'] = {'b': b, 'word': word(best), 'padded_word': word(padded(best)), 'padded_check': chk}
final = check_board(h, padded(best))
log['final_independent_check'] = final
log['equality_for_all_widths_from'] = last_double(best) if final['valid'] else None
log['status'] = 'done'
save()
print(json.dumps({k: log[k] for k in ('equality_impossible_below_width', 'equality_for_all_widths_from')}))
