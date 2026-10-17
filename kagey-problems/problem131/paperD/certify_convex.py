"""Ball-arithmetic certificate (python-flint / Arb) of convexity between the humps (Definition 3.14,
the property of Conjecture 3.15) for a range of N (Proposition 3.25, label prop:convex-certified).
The whole range 10..2000 takes about an hour. The output of the run of October 17, 2026 is in
data/certify_convex_output_2026-10-17.txt, with per-N witnesses in data/witnesses_convex_2026-10-17.jsonl
(the older data/certify_convex_output.txt is the historical run of October 9).
For each N:
 (1) enclose the crossing eps_N in [e-, e+] by the sign of P_N(center) - P_N(N) at the two ends
     (the ratio is strictly increasing in eps, Proposition 2.3, label prop:mlr);
 (2) with eps = the ball [e-, e+], enclose the whole law P_N by the forward recursion;
 (3) find every index a >= N/2 that can be a mode, put m* = N - a, and certify
       second difference > 0 at every a in [2m*+1, N-2m*-1]            (direct check)
     and also the two inequalities of the reduction:
       second difference < 0 at some a0 <= 2m*, and > 0 at a1 = 2m*+1
     (Corollary 3.21, label cor:one-point, which rests on Theorem 3.20, label thm:no-holes).
The script exits with status 1 if any N fails, and with status 2 (before any computation) if the
range is empty or starts below 10, the smallest N of Proposition 3.25.
Usage: python -I -B certify_convex.py Nlo Nhi [--witness FILE.jsonl]     (for example 10 400, half a minute)
With --witness the script also writes one JSON line per N (exact rational bracket of the crossing,
the candidate modes and the certified margins), after a header line with the sha256 of the scripts
and the versions of Python and python-flint. A FILE ending in .gz is written gzipped. The printed
output is the same with or without --witness."""
import sys, time
from flint import arb, fmpq, ctx
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
from verify_elephant_shape import crossing, crossing_window, g_root

N_MIN = 10          # Propositions 3.25 and 3.27 start at N = 10


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


def enclose_crossing(N, cen):
    """Rational lo < hi with P_N(cen) - P_N(N) certified < 0 at lo and > 0 at hi, or None.
    Returns (lo, hi, k, g_lo, g_hi), where 10^-k is the relative half-width and g_lo, g_hi are
    the enclosures of P_N(cen) - P_N(N) at the two ends."""
    xh = xcross(N); eh = fmpq(int(round(xh/N*10**15)), 10**15)
    for k in (11, 10, 9, 8):
        lo, hi = eh*(1 - fmpq(1, 10**k)), eh*(1 + fmpq(1, 10**k))
        Plo, Phi = law(N, arb(lo)), law(N, arb(hi))
        glo, ghi = Plo[cen] - Plo[N], Phi[cen] - Phi[N]
        if glo < 0 and ghi > 0:
            return lo, hi, k, glo, ghi
    return None


# ---------------------------------------------------------------- witnesses (only with --witness)

def exact(x):
    """An exact arb (such as x.lower() or x.upper()) as the string 'm*2^e', with a float beside it."""
    try:
        m, e = x.man_exp()
        return {'exact': f'{m}*2^{e}', 'approx': float(x)}
    except Exception:
        return {'exact': None, 'approx': str(x)}


def sha256(path):
    import hashlib
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def open_witness(path, script, argv, extra_files):
    """Open the witness file and write its header line."""
    import gzip, json, platform, datetime, flint
    f = gzip.open(path, 'wt', encoding='utf-8', newline='\n') if path.endswith('.gz') else \
        open(path, 'w', encoding='utf-8', newline='\n')
    here = os.path.dirname(os.path.abspath(__file__))
    files = [script] + extra_files
    header = {'type': 'header', 'script': os.path.basename(script), 'argv': argv,
              'sha256': {os.path.basename(p): sha256(os.path.join(here, os.path.basename(p))) for p in files},
              'python': sys.version, 'platform': platform.platform(),
              'python_flint': flint.__version__,
              'flint': getattr(flint, '__FLINT_VERSION__', None), 'prec_bits': ctx.prec,
              'started': datetime.datetime.now().astimezone().isoformat(timespec='seconds'),
              'dyadic_format': 'm*2^e is the exact number m times 2 to the power e',
              'rational_format': 'p/q'}
    f.write(json.dumps(header) + '\n'); f.flush()
    return f


def write_line(f, rec):
    import json
    f.write(json.dumps(rec) + '\n'); f.flush()


def parse_args(argv, even_only):
    """Nlo Nhi [--witness FILE]. Exits with status 2 on an empty or unintended range."""
    import argparse
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument('Nlo', type=int)
    p.add_argument('Nhi', type=int)
    p.add_argument('--witness', metavar='FILE', default=None,
                   help='write per-N witnesses as JSON lines (gzipped if FILE ends in .gz)')
    a = p.parse_args(argv)
    if a.Nlo < N_MIN:
        p.error(f'Nlo = {a.Nlo} is below {N_MIN}, the smallest N of the certified range')
    if a.Nlo > a.Nhi:
        p.error(f'empty range: Nlo = {a.Nlo} > Nhi = {a.Nhi}')
    Ns = [N for N in range(a.Nlo, a.Nhi + 1) if N % 2 == 0 or not even_only]
    if not Ns:
        p.error(f'the range {a.Nlo}..{a.Nhi} contains no even N, and this script certifies even N only')
    return a, Ns


# ---------------------------------------------------------------- the certificate

def certify(N, rec=None):
    """(True, list of m*) if N is certified, else (False, reason). If rec is a dict it is filled
    with the witness of N."""
    cen = N//2 if N % 2 == 0 else (N+1)//2
    br = enclose_crossing(N, cen)
    if br is None:
        return False, 'crossing not enclosed'
    lo, hi, k, glo, ghi = br
    if rec is not None:
        rec.update({'N': N, 'center_bin': cen, 'eps_lo': str(lo), 'eps_hi': str(hi), 'rel_halfwidth_exp10': -k,
                    'center_minus_end_at_eps_lo_upper': exact(glo.upper()),
                    'center_minus_end_at_eps_hi_lower': exact(ghi.lower())})
    eps = arb(lo).union(arb(hi))
    P = law(N, eps)
    D = [None] + [P[a-1] - 2*P[a] + P[a+1] for a in range(1, N)]
    half = (N+1)//2
    best_lower = max(P[a].lower() for a in range(half, N+1))
    cand = [a for a in range(half, N+1) if not (P[a].upper() < best_lower)]
    info = []
    cands = []
    for astar in cand:
        ms = N - astar
        rng = range(2*ms+1, N-2*ms)
        if not all(D[a] > 0 for a in rng): return False, f'direct check fails m*={ms}'
        c = {'a_star': astar, 'm_star': ms, 'range': [2*ms+1, N-2*ms-1] if len(rng) else None}
        if len(rng):
            a0 = [a for a in range(1, 2*ms+1) if D[a] < 0]
            if not a0 or not (D[2*ms+1] > 0): return False, f'reduction check fails m*={ms}'
            if rec is not None:
                amin = min(rng, key=lambda a: D[a].lower())
                c.update({'min_D_lower_on_range': exact(D[amin].lower()), 'argmin': amin,
                          'a0': a0[0], 'D_a0_upper': exact(D[a0[0]].upper()), 'n_a0': len(a0),
                          'D_at_2m_plus_1_lower': exact(D[2*ms+1].lower())})
        info.append(ms)
        cands.append(c)
    if rec is not None:
        excl = [a for a in range(half, N+1) if a not in cand]
        rec.update({'best_mode_lower': exact(best_lower), 'candidates': cands})
        if excl:
            ae = max(excl, key=lambda a: P[a].upper())
            rec.update({'max_excluded_upper': exact(P[ae].upper()), 'max_excluded_at': ae,
                        'mode_gap_lower': exact((best_lower - P[ae].upper()).lower())})
    return True, info

if __name__ == '__main__':
    args, Ns = parse_args(sys.argv[1:], even_only=False)
    lo, hi = args.Nlo, args.Nhi
    wf = open_witness(args.witness, __file__, sys.argv[1:], ['verify_elephant_shape.py']) if args.witness else None
    t0 = time.time(); bad = []; multi = []
    for N in Ns:
        t1 = time.time()
        rec = {'type': 'N'} if wf else None
        ok, info = certify(N, rec)
        if wf:
            rec.update({'certified': bool(ok), 'reason': None if ok else info, 'seconds': round(time.time() - t1, 3)})
            if not ok: rec['N'] = N
            write_line(wf, rec)
        if not ok: bad.append((N, info)); print('FAIL', N, info, flush=True)
        elif len(info) > 1: multi.append((N, info))
    print(f'N = {lo}..{hi}: certified {hi-lo+1-len(bad)} of {hi-lo+1}; failures {bad}; N with more than one candidate mode {multi}; {time.time()-t0:.0f}s')
    status = 1 if bad or len(Ns) != hi - lo + 1 else 0
    if wf:
        write_line(wf, {'type': 'summary', 'N_lo': lo, 'N_hi': hi, 'expected': len(Ns),
                        'certified': len(Ns) - len(bad), 'failed': [N for N, _ in bad],
                        'seconds': round(time.time() - t0, 1), 'exit_status': status})
        wf.close()
    sys.exit(status)
