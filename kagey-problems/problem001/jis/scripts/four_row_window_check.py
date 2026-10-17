"""Certificate for the four-row partition recurrences by a Cayley-Hamilton window.

Each partition count a_F(n) is alpha T^n w for the transfer matrix T of the
reachable part of the product automaton (N states; four_row_dp_check.py).
If Q_F is a polynomial of degree d and u(n) = sum_j q_j a_F(n-j), then
u(n) = alpha T^(n-d) M w with M = sum_j q_j T^(d-j), so by Cayley-Hamilton u
satisfies a linear recurrence of order at most N valid for n >= d + N.  Hence
if u vanishes on N consecutive widths n0, ..., n0+N-1 with n0 >= d, it
vanishes for every n >= n0.

This script computes the partition counts far enough, checks the window for
each stored partition denominator with threshold n0 = deg P_F + 1, and records
the result in jis/data/four_row_window_check.json.  It is a different
certificate from the all-coordinate annihilation at a single width.
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from four_row_dp_check import DATA, MACHINES, load_machine, count_sequence  # noqa: E402
from four_row_recurrence_check import factor_exponents, expand, mul, trim  # noqa: E402

NAMES = {'01|23': '{1,2}|{3,4}', '02|13': '{1,3}|{2,4}', '03|12': '{1,4}|{2,3}'}
CAP = 1200.0


def main():
    t0 = time.time()
    stored = json.load(open(os.path.join(DATA, 'four_row_recurrence.json')))
    out = {}
    for key, name in NAMES.items():
        if time.time() - t0 > CAP:
            out[name] = {'status': 'unresolved (time cap)'}
            continue
        exps, _ = factor_exponents(stored['per_partition'][key]['denominator_factored'])
        q = expand(exps)
        d = len(q) - 1
        alphabet, trans = load_machine(name)
        # a short run to find the numerator degree and threshold n0 = deg P + 1
        seq0, n_states, _ = count_sequence(alphabet, trans, 3 * d + 40)
        p0 = trim(mul(q, seq0)[:len(seq0)])
        n0 = max(len(p0), d)
        width = n0 + n_states + 5
        t1 = time.time()
        seq, n_states, n_acc = count_sequence(alphabet, trans, width)
        u = [sum(q[j] * seq[n - j] for j in range(d + 1)) for n in range(d, width + 1)]
        window_zero = all(u[n - d] == 0 for n in range(n0, n0 + n_states))
        before = [n for n in range(d, n0) if u[n - d] != 0]
        out[name] = {'denominator_degree': d, 'numerator_degree': len(p0) - 1,
                     'threshold_n0': n0, 'reachable_states_N': n_states,
                     'window': [n0, n0 + n_states - 1], 'counted_through_width': width,
                     'window_all_zero': window_zero,
                     'last_nonzero_residual_before_n0': max(before) if before else None,
                     'certified_for_all_widths_from_n0': window_zero,
                     'seconds': round(time.time() - t1, 1),
                     'status': 'resolved'}
        print(name, out[name], flush=True)
        json.dump(out, open(os.path.join(DATA, 'four_row_window_check.json'), 'w'), indent=1)
    out['total_seconds'] = round(time.time() - t0, 1)
    json.dump(out, open(os.path.join(DATA, 'four_row_window_check.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
