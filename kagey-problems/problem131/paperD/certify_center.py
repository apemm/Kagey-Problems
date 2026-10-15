"""Ball-arithmetic certificate (python-flint / Arb) that the center is the unique interior minimum
of the elephant law at the crossing, for even N in a range (Proposition 3.27).

For each even N the script encloses the crossing eps_N and the whole law P_N exactly as
certify_convex.py does (it imports that script). Then it certifies one of two things.
 (A) For every index a* >= N/2 that can be a mode, with m* = N - a*, the range
     2m*+1 <= a <= N-2m*-1 contains the center N/2. By Proposition 3.25 the second difference is
     positive on this range, and the criterion of Proposition 3.27(a) then gives the claim.
 (B) Otherwise, directly: the enclosure of P_N(a) - P_N(N/2) is positive for every
     1 <= a <= N-1 with a != N/2.
It prints how many N fall under (A) and under (B), the N under (B), and for (A) the smallest value
of N/2 - (2m*+1). As a second check it also reports for how many N the direct test (B) succeeds.
Usage: python -B certify_center.py Nlo Nhi     (10 2000 takes about half an hour)"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
from flint import arb, fmpq, ctx
import certify_convex as cc

ctx.prec = 160


def certify(N):
    assert N % 2 == 0
    h = N // 2
    xh = cc.xcross(N)
    eh = fmpq(int(round(xh / N * 10 ** 15)), 10 ** 15)
    for k in (11, 10, 9, 8):
        lo, hi = eh * (1 - fmpq(1, 10 ** k)), eh * (1 + fmpq(1, 10 ** k))
        Plo, Phi = cc.law(N, arb(lo)), cc.law(N, arb(hi))
        if (Plo[h] - Plo[N]) < 0 and (Phi[h] - Phi[N]) > 0:
            break
    else:
        return None, 'crossing not enclosed'
    P = cc.law(N, arb(lo).union(arb(hi)))
    best_lower = max(P[a].lower() for a in range(h, N + 1))
    cand = [a for a in range(h, N + 1) if not (P[a].upper() < best_lower)]
    slack = min(h - (2 * (N - a) + 1) for a in cand)
    direct = all((P[a] - P[h]) > 0 for a in range(1, N) if a != h)
    if slack >= 0:
        return 'A', (slack, direct)
    if direct:
        return 'B', (slack, direct)
    return None, f'neither test works, slack {slack}'


if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    t0 = time.time()
    A, B, bad, ndirect, minslack = 0, [], [], 0, None
    for N in range(lo + lo % 2, hi + 1, 2):
        kind, info = certify(N)
        if kind is None:
            bad.append((N, info))
            print('FAIL', N, info, flush=True)
            continue
        slack, direct = info
        ndirect += bool(direct)
        if kind == 'A':
            A += 1
            if minslack is None or slack < minslack[0]:
                minslack = (slack, N)
        else:
            B.append(N)
    print(f'even N = {lo}..{hi}: (A) {A}; (B) {len(B)}, namely {B}; failures {bad}; '
          f'smallest N/2 - (2m*+1) under (A): {minslack}; direct test succeeds for {ndirect} of them; '
          f'{time.time() - t0:.0f}s', flush=True)
    sys.exit(1 if bad else 0)
