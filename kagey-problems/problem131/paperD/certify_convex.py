"""Ball-arithmetic certificate (python-flint / Arb) of Conjecture 3.16 for a range of N
(Proposition 3.26). The whole range 10..2000 takes about an hour, and the output of that
run is in data/certify_convex_output.txt.
For each N:
 (1) enclose the crossing eps_N in [e-, e+] by the sign of P_N(center) - P_N(N) at the two ends
     (the ratio is strictly increasing in eps, Proposition prop:mlr);
 (2) with eps = the ball [e-, e+], enclose the whole law P_N by the forward recursion;
 (3) find every index a >= N/2 that can be a mode, put m* = N - a, and certify
       second difference > 0 at every a in [2m*+1, N-2m*-1]            (direct check)
     and also the two inequalities of the reduction theorem:
       second difference < 0 at some a0 <= m*, and > 0 at a1 = 2m*+1.
Usage: python -B certify_convex.py Nlo Nhi     (for example 10 400, half a minute)"""
import sys, time
from flint import arb, fmpq, ctx
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
from verify_elephant_shape import crossing, crossing_window, g_root


def xcross(n):
    """The crossing x_n in double precision (only a starting point for the enclosure)."""
    g = g_root(n)
    if n % 2 == 0:
        return crossing_window(n, 0.3 * g, g + 1.0)
    return crossing(n, 'A', 0.3 * g, g + 1.0)

ctx.prec = 160

def law(N, eps):
    """P(A_N = a), a = 0..N, symmetric start, eps an arb."""
    c = 1 - 2*eps
    P = [arb(1)/2, arb(1)/2]
    for t in range(1, N):
        Q = [arb(0)]*(t+2)
        ct = c/t
        for a in range(t+1):
            p = P[a]
            r = eps + ct*a                 # up-probability; r and 1-r are balls inside (0,1)
            Q[a] = Q[a] + p*(1 - r)        # two products of nonnegative balls, no cancellation
            Q[a+1] = Q[a+1] + p*r
        P = Q
    return P

def certify(N):
    xh = xcross(N); eh = fmpq(int(round(xh/N*10**15)), 10**15)
    cen = N//2 if N % 2 == 0 else (N+1)//2
    for k in (11, 10, 9, 8):
        lo, hi = eh*(1 - fmpq(1, 10**k)), eh*(1 + fmpq(1, 10**k))
        Plo, Phi = law(N, arb(lo)), law(N, arb(hi))
        if (Plo[cen] - Plo[N]) < 0 and (Phi[cen] - Phi[N]) > 0: break
    else:
        return False, 'crossing not enclosed'
    eps = arb(lo).union(arb(hi))
    P = law(N, eps)
    D = [None] + [P[a-1] - 2*P[a] + P[a+1] for a in range(1, N)]
    half = (N+1)//2
    best_lower = max(P[a].lower() for a in range(half, N+1))
    cand = [a for a in range(half, N+1) if not (P[a].upper() < best_lower)]
    info = []
    for astar in cand:
        ms = N - astar
        rng = range(2*ms+1, N-2*ms)
        if not all(D[a] > 0 for a in rng): return False, f'direct check fails m*={ms}'
        if len(rng):
            a0 = [a for a in range(1, 2*ms+1) if D[a] < 0]
            if not a0 or not (D[2*ms+1] > 0): return False, f'reduction check fails m*={ms}'
        info.append(ms)
    return True, info

if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    t0 = time.time(); bad = []; multi = []
    for N in range(lo, hi+1):
        ok, info = certify(N)
        if not ok: bad.append((N, info)); print('FAIL', N, info, flush=True)
        elif len(info) > 1: multi.append((N, info))
    print(f'N = {lo}..{hi}: certified {hi-lo+1-len(bad)} of {hi-lo+1}; failures {bad}; N with more than one candidate mode {multi}; {time.time()-t0:.0f}s')
