"""Certify the sign of f_a''(0) on whole intervals of a (Taylor models).

Covers [LO, HI] by intervals [a0 - w, a0 + w].  On each it builds the uniform
enclosure f_a''(0) in G(a - a0) +- eta of erw_tm.TaylorModel and splits the
interval into pieces where that enclosure has one sign.  An interval is
accepted when every piece has a sign; otherwise the interval is halved.  In
mode 'zero' one undecided piece is allowed in the whole cover: the output then
gives a1 < a2 with f'' < 0 on [LO, a1] and f'' > 0 on [a2, HI].

Usage (from this folder):
  py -I certify_interval.py cover LO HI SIGN     SIGN = -1 or +1
  py -I certify_interval.py zero LO HI [RHO]     RHO caps the disc radius (default 1/25)
  py -I certify_interval.py scaled LO HI         scaled variable L/sigma (Lemma 9),
                                                 for a near 1/2; certifies f'' < 0
LO, HI are decimals (exact rationals).  Exit status 1 on failure.
"""
import math
import sys
import time
from fractions import Fraction

sys.path.insert(0, ".")
from erw_cf import ERW  # noqa: E402
from erw_tm import TaylorModel, sign_cover  # noqa: E402

T2_LADDER = [Fraction(1, 2), Fraction(1), Fraction(2), Fraction(3), Fraction(4),
             Fraction(6), Fraction(8), Fraction(10), Fraction(12), Fraction(16),
             Fraction(20), Fraction(24)]
B_CACHE = {}


def b_estimate(a):
    key = round(float(a), 3)
    if key not in B_CACHE:
        B_CACHE[key] = float(ERW("%.3f" % key, N=120, prec=300).B.mid())
    return B_CACHE[key]


def params(a0, w, q, T2):
    a = float(a0) - float(w / q)
    B = 1.45 * b_estimate(a0)            # room for the square enclosure
    T3 = 2 ** (float(a0 + w)) * float(T2)
    peak = (B * T3) ** (1 / a)
    N = 300
    while N * math.log(B * T3) + 14 * math.log(N) - math.lgamma(1 + a * N) > -200:
        N += 100
    prec = int(1.45 * peak + 1100)
    return N, prec


SCALED = [False]
RHO_CAP = [Fraction(1, 25)]


def try_interval(a0, w, q, T2):
    if SCALED[0]:
        a = float(a0) - float(w / q)
        T3 = 2 ** float(a0 + w) * float(T2)
        B = 2.8
        peak = (B * T3) ** (1 / a)
        N = 600
        while N * math.log(B * T3) + 14 * math.log(N) - math.lgamma(1 + a * N) > -200:
            N += 100
        prec = int(1.45 * peak + 1100)
    else:
        N, prec = params(a0, w, q, T2)
    tm = TaylorModel(a0, w, q=q, N=N, prec=prec, scaled=SCALED[0])
    d = tm.certify(T2, Fraction(1, 32))
    if not d["boot"]:
        return None, d, N, prec
    cover = sign_cover(d["G"], d["eta"], a0, w)
    return cover, d, N, prec


def max_w(a0):
    """Largest half-width allowed at a0: the disc must stay in Re z > 1/2."""
    if SCALED[0]:
        return Fraction(1, 8), Fraction(1, 400)
    room = a0 - Fraction(1, 2)
    q = Fraction(1, 8) if room < Fraction(1, 50) else Fraction(1, 32)
    rho = min(RHO_CAP[0], room * Fraction(9, 10))
    return q, rho * q


def run(lo, hi, mode, want, log, allow_zero, start_t2=None):
    a0 = (lo + hi) / 2
    w = (hi - lo) / 2
    q, wmax = max_w(lo)
    if w > wmax:
        mid = (lo + hi) / 2
        return (run(lo, mid, mode, want, log, allow_zero, start_t2)
                and run(mid, hi, mode, want, log, allow_zero, start_t2))
    if start_t2 is None and SCALED[0]:
        fa = float(a0)
        start_t2 = 3 if fa < 0.56 else 4 if fa < 0.6 else 5 if fa < 0.63 else 6 if fa < 0.655 else 7
    if start_t2 is None:
        fa = float(a0)
        start_t2 = 0 if fa < 0.53 else 1 if fa < 0.58 else 2 if fa < 0.64 else 3 if fa < 0.665 else 4
    for i in range(start_t2, len(T2_LADDER)):
        T2 = T2_LADDER[i]
        try:
            cover, d, N, prec = try_interval(a0, w, q, T2)
        except (ValueError, AssertionError) as exc:
            print("  skip a0=%.10f T2=%s: %s" % (a0, T2, exc), flush=True)
            continue
        if cover is None:
            continue
        signs = [s for (_, _, s) in cover]
        line = ("[%.14f, %.14f] T2=%s N=%d prec=%d K=%d q=%s eta=%s G0=%s"
                % (lo, hi, T2, N, prec, d["K"], q, d["eta"].str(3), d["G"][0].str(6)))
        if mode == "cover" and all(s == want for s in signs):
            log.append((lo, hi, want, line))
            print("ok  " + line, flush=True)
            return True
        if mode == "zero" and 0 not in signs and len(set(signs)) == 1:
            log.append((lo, hi, signs[0], line))
            print("ok  " + line, flush=True)
            return True
        if mode == "zero" and allow_zero[0] and signs.count(0) == 1:
            # a single undecided piece, with - to its left and + to its right
            k = signs.index(0)
            if all(s == -1 for s in signs[:k]) and all(s == 1 for s in signs[k + 1:]):
                zlo, zhi = cover[k][0], cover[k][1]
                if zhi - zlo < Fraction(1, 10 ** 12):
                    allow_zero[0] = False
                    log.append((lo, hi, 0, line + "  zero piece [%s, %s]" % (zlo, zhi)))
                    print("ok* " + line + "  undecided piece [%.16f, %.16f]"
                          % (zlo, zhi), flush=True)
                    return True
        # an undecided part: more tail accuracy may settle it, else split
        if 0 not in signs:
            break
    if w < Fraction(1, 10 ** 9):
        print("FAIL [%.14f, %.14f]" % (lo, hi), flush=True)
        return False
    mid = (lo + hi) / 2
    return (run(lo, mid, mode, want, log, allow_zero)
            and run(mid, hi, mode, want, log, allow_zero))


def main():
    mode = sys.argv[1]
    if mode == "scaled":
        SCALED[0] = True
        mode = "cover"
        sys.argv.insert(4, "-1")
    lo, hi = Fraction(sys.argv[2]), Fraction(sys.argv[3])
    want = int(sys.argv[4]) if mode == "cover" else 0
    extra = sys.argv[5:] if mode == "cover" else sys.argv[4:]
    if extra:
        RHO_CAP[0] = Fraction(extra[0])
    t0 = time.time()
    log = []
    allow_zero = [mode == "zero"]
    ok = run(lo, hi, mode, want, log, allow_zero)
    log.sort()
    covered = all(log[i][1] == log[i + 1][0] for i in range(len(log) - 1))
    covered = covered and log and log[0][0] == lo and log[-1][1] == hi
    print("intervals: %d  contiguous cover of [%s, %s]: %s" % (len(log), lo, hi, covered))
    if mode == "zero":
        zl = [x for x in log if x[2] == 0]
        print("zero piece:", zl[0][3].split("zero piece")[-1] if zl else "none")
    print("elapsed %.1f s" % (time.time() - t0))
    sys.exit(0 if (ok and covered) else 1)


if __name__ == "__main__":
    main()
