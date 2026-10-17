"""Ball-arithmetic certificate (python-flint / Arb) that the center is the unique interior minimum
of the elephant law at the crossing, for even N in a range (Proposition 3.27, label prop:center-small).

For each even N the script encloses the crossing eps_N and the whole law P_N exactly as
certify_convex.py does (it imports that script). Then it certifies one of two things.
 (A) For every index a* >= N/2 that can be a mode, with m* = N - a*, the range
     2m*+1 <= a <= N-2m*-1 contains the center N/2. By Proposition 3.25 (label
     prop:convex-certified, certified separately by certify_convex.py) the second difference is
     positive on this range, and the criterion of Lemma 3.23 (label lem:center-convex) then gives
     the claim. Test (A) does not itself check the second difference.
 (B) Otherwise, directly: the enclosure of P_N(a) - P_N(N/2) is positive for every
     1 <= a <= N-1 with a != N/2.
It prints how many N fall under (A) and under (B), the N under (B), and for (A) the smallest value
of N/2 - (2m*+1). As a second check it also reports for how many N the direct test (B) succeeds.
It also certifies, by an exact rational comparison, that the lower end lo of the enclosure of eps_N
exceeds 2/(N+2) (the hypothesis of Proposition 3.7, label prop:dip-hyp), and prints the smallest
lo*(N+2)/2.
The script exits with status 1 if any N fails, and with status 2 (before any computation) if the
range is empty, starts below 10 or contains no even N.
Usage: python -I -B certify_center.py Nlo Nhi [--witness FILE.jsonl]     (10 2000 takes about 25 minutes)
With --witness the script also writes one JSON line per even N (exact rational bracket of the
crossing, the candidate modes, the slack of test (A), the margin of the direct test and the exact
value lo*(N+2)/2), after a header line with the sha256 of the scripts and the versions of Python and
python-flint. A FILE ending in .gz is written gzipped. The printed output is the same with or
without --witness. The output of the run of October 17, 2026 is in
data/certify_center_output_2026-10-17.txt, with witnesses in data/witnesses_center_2026-10-17.jsonl."""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
from flint import arb, fmpq, ctx
import certify_convex as cc

ctx.prec = 160


def certify(N, rec=None):
    assert N % 2 == 0
    h = N // 2
    br = cc.enclose_crossing(N, h)
    if br is None:
        return None, 'crossing not enclosed'
    lo, hi, k, glo, ghi = br
    # the hypothesis of Proposition 3.7: eps_N > 2/(N+2), exact rational comparison
    margin = lo * (N + 2) / 2
    if rec is not None:
        rec.update({'N': N, 'center_bin': h, 'eps_lo': str(lo), 'eps_hi': str(hi), 'rel_halfwidth_exp10': -k,
                    'center_minus_end_at_eps_lo_upper': cc.exact(glo.upper()),
                    'center_minus_end_at_eps_hi_lower': cc.exact(ghi.lower()),
                    'lo_times_(N+2)/2': str(margin), 'lo_above_2/(N+2)': bool(lo > fmpq(2, N + 2))})
    if not lo > fmpq(2, N + 2):
        return None, f'enclosure lower end {lo} not above 2/(N+2)'
    P = cc.law(N, arb(lo).union(arb(hi)))
    best_lower = max(P[a].lower() for a in range(h, N + 1))
    cand = [a for a in range(h, N + 1) if not (P[a].upper() < best_lower)]
    slack = min(h - (2 * (N - a) + 1) for a in cand)
    gaps = [(P[a] - P[h]) for a in range(1, N) if a != h]
    direct = all(g > 0 for g in gaps)
    if rec is not None:
        excl = [a for a in range(h, N + 1) if a not in cand]
        rec.update({'best_mode_lower': cc.exact(best_lower),
                    'candidates': [{'a_star': a, 'm_star': N - a, 'slack': h - (2 * (N - a) + 1)} for a in cand],
                    'slack': slack, 'direct': bool(direct),
                    'direct_min_lower': cc.exact(min(g.lower() for g in gaps))})
        if excl:
            ae = max(excl, key=lambda a: P[a].upper())
            rec.update({'max_excluded_upper': cc.exact(P[ae].upper()), 'max_excluded_at': ae,
                        'mode_gap_lower': cc.exact((best_lower - P[ae].upper()).lower())})
    if slack >= 0:
        return 'A', (slack, direct, margin)
    if direct:
        return 'B', (slack, direct, margin)
    return None, f'neither test works, slack {slack}'


if __name__ == '__main__':
    args, Ns = cc.parse_args(sys.argv[1:], even_only=True)
    lo, hi = args.Nlo, args.Nhi
    wf = cc.open_witness(args.witness, __file__, sys.argv[1:], ['certify_convex.py', 'verify_elephant_shape.py']) \
        if args.witness else None
    t0 = time.time()
    A, B, bad, ndirect, minslack, minmargin = 0, [], [], 0, None, None
    for N in Ns:
        t1 = time.time()
        rec = {'type': 'N'} if wf else None
        kind, info = certify(N, rec)
        if wf:
            rec.update({'N': N, 'certified': kind is not None, 'test': kind,
                        'reason': None if kind else info, 'seconds': round(time.time() - t1, 3)})
            cc.write_line(wf, rec)
        if kind is None:
            bad.append((N, info))
            print('FAIL', N, info, flush=True)
            continue
        slack, direct, margin = info
        ndirect += bool(direct)
        if minmargin is None or margin < minmargin[0]:
            minmargin = (margin, N)
        if kind == 'A':
            A += 1
            if minslack is None or slack < minslack[0]:
                minslack = (slack, N)
        else:
            B.append(N)
    print(f'even N = {lo}..{hi}: (A) {A}; (B) {len(B)}, namely {B}; failures {bad}; '
          f'smallest N/2 - (2m*+1) under (A): {minslack}; direct test succeeds for {ndirect} of them; '
          f'{time.time() - t0:.0f}s', flush=True)
    mm = 'none' if minmargin is None else f'{float(minmargin[0]):.6f} at N = {minmargin[1]} (exact {minmargin[0]})'
    allpass = not any('not above 2/(N+2)' in str(i) or 'not enclosed' in str(i) for _, i in bad)
    print(f'eps_N > 2/(N+2) (lower end of the enclosure, exact rational comparison): '
          f'{"every N passed" if allpass else "FAILED for some N"}; '
          f'smallest lo*(N+2)/2: {mm}', flush=True)
    status = 1 if bad or A + len(B) != len(Ns) else 0
    if wf:
        cc.write_line(wf, {'type': 'summary', 'N_lo': lo, 'N_hi': hi, 'expected': len(Ns),
                           'certified': A + len(B), 'test_A': A, 'test_B': B, 'direct_passed': ndirect,
                           'failed': [N for N, _ in bad], 'seconds': round(time.time() - t0, 1),
                           'exit_status': status})
        wf.close()
    sys.exit(status)
