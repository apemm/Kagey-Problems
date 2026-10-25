"""Certify the sign of f_a''(0) at exact rational values of a.

f_a is the density of the elephant random walk limit L_a (first step +1),
a = 2p - 1 in (1/2, 1).  For each a the script builds the ball enclosure of
f_a''(0) from erw_cf.ERW.certify (moment series, Taylor cells, bootstrap tail
bound of Lemma 4, exact term-by-term integral) and reports the sign only when
the bootstrap inequality R < 1 holds and the enclosure excludes 0.

Usage (from this folder):
  py -I certify_fpp.py point A1 [A2 ...]      certify at the listed decimals
  py -I certify_fpp.py bisect LO HI STEPS     certified bisection between LO, HI
  py -I certify_fpp.py scan                   certify on a grid of a in [0.501, 0.97]
Exit status 1 if any requested sign is not certified.
"""
import math
import sys
import time
from fractions import Fraction

sys.path.insert(0, ".")
from erw_cf import ERW  # noqa: E402

T2_LIST = ["1/2", "1", "2", "3", "4", "6", "8", "10", "12", "16", "24", "32", "48", "64", "96", "128", "192", "256", "384"]


def params(a_str, T2):
    """N, prec, h for a given T2.  B is estimated from a short moment run (only the
    choice of N and prec depends on it; every bound is then checked in balls)."""
    est = ERW(a_str, N=120, prec=300)
    B = float(est.B.mid())
    a = float(Fraction(a_str))
    T3 = 2 ** a * float(Fraction(T2))
    peak = (B * T3) ** (1 / a)        # log of the largest series term, roughly
    N = 400
    while N * math.log(B * T3) + 40 * math.log(N) - math.lgamma(1 + a * N) > -350:
        N += 100
    prec = int(1.45 * peak + 600)
    h = Fraction(1, 32)
    while 2 * h <= Fraction(T2) / 160:   # about 160 cells below T2
        h *= 2
    return N, prec, "%d/%d" % (h.numerator, h.denominator)


def certify(a_str, t2_list=T2_LIST):
    last = None
    for T2 in t2_list:
        N, prec, h = params(a_str, T2)
        if N > 9000:
            if last is None:
                last = ("skipped", "N > 9000", N, T2)
            break
        try:
            e = ERW(a_str, N=N, prec=prec)
            d = e.certify(T2=T2, h=h)
        except (ValueError, AssertionError) as exc:
            last = ("error", str(exc), N, T2)
            continue
        d["N"], d["prec"] = N, prec
        last = d
        if d["sign"] != 0:
            return d
    return last


def show(d):
    if isinstance(d, tuple):
        return "NOT CERTIFIED (%s)" % (d,)
    return ("a=%s  sign=%+d  f''(0) in [%s, %s]  [N=%d prec=%d T2=%s T3=%s h=%s R=%s C=%s E<=%s B=%s]"
            % (d["a"], d["sign"], d["fpp"].lower().str(8), d["fpp"].upper().str(8), d["N"], d["prec"],
               d["T2"].str(6), d["T3"].str(6), d["h"].str(4), d["R"].str(4),
               d["C"].str(3), d["E"].str(3), d["B"].str(5)))


def dec(fr, digits=15):
    q = Fraction(fr).limit_denominator(10 ** digits)
    s = "%.*f" % (digits, q.numerator / q.denominator)
    return s


def main():
    mode = sys.argv[1]
    ok = True
    t0 = time.time()
    if mode == "point":
        for a in sys.argv[2:]:
            d = certify(a)
            print(show(d), flush=True)
            ok &= not isinstance(d, tuple) and d["sign"] != 0
    elif mode == "bisect":
        lo, hi, steps = sys.argv[2], sys.argv[3], int(sys.argv[4])
        dlo, dhi = certify(lo), certify(hi)
        print(show(dlo), flush=True)
        print(show(dhi), flush=True)
        assert dlo["sign"] == -1 and dhi["sign"] == 1
        flo, fhi = Fraction(lo), Fraction(hi)
        for _ in range(steps):
            mid = (flo + fhi) / 2
            # round the midpoint to a short decimal inside (flo, fhi)
            k = 1
            while True:
                q = Fraction(round(mid * 10 ** k), 10 ** k)
                if flo < q < fhi:
                    break
                k += 1
            ms = ("%d" % (q.numerator * 10 ** k // q.denominator)).rjust(k + 1, "0")
            ms = ms[:-k] + "." + ms[-k:]
            d = certify(ms)
            print(show(d), flush=True)
            if isinstance(d, tuple) or d["sign"] == 0:
                ok = False
                break
            if d["sign"] < 0:
                flo = Fraction(ms)
            else:
                fhi = Fraction(ms)
        print("certified bracket: f''(0) < 0 at a = %s, > 0 at a = %s" % (flo, fhi))
        print("as decimals: %s  %s" % (float(flo), float(fhi)))
    elif mode == "scan":
        grid = ["0.501", "0.505", "0.51", "0.52", "0.53", "0.54", "0.55", "0.56", "0.57", "0.58", "0.59",
                "0.60", "0.61", "0.62", "0.63", "0.64", "0.65", "0.66", "0.665", "0.668",
                "0.669", "0.67", "0.675", "0.68", "0.69", "0.70", "0.72", "0.74", "0.76",
                "0.78", "0.80", "0.82", "0.84", "0.86", "0.88", "0.90", "0.92", "0.94",
                "0.95", "0.96", "0.97"]
        for a in grid:
            d = certify(a)
            print(show(d), flush=True)
            ok &= not isinstance(d, tuple) and d["sign"] != 0
    print("elapsed %.1f s" % (time.time() - t0))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
