"""Certify strict memory monotonicity of the central curvature near its zero.

This extends the reviewed real-parameter Taylor/Fourier certificate. The
parameter derivative is bounded by differentiating the smoothing equation,
not by differentiating an error bar. All acceptance checks use Arb enclosures
and raise RuntimeError on failure, including under python -O.

The fixed rational constants below deliberately leave wide margins. The
analytic reduction is proved in or_transition_proofs.tex. This is an Arb-assisted
certificate, not a claim that Arb's transcendental evaluations run in Lean.
"""

import argparse
import hashlib
import json
import platform
import sys
import time
from fractions import Fraction
from pathlib import Path

PAPER = Path(__file__).resolve().parent
sys.path.insert(0, str(PAPER))

import flint
from flint import arb, arb_poly
from threshold_pointwise import require
from threshold_taylor import TaylorModel, eval_G, fq

A0 = Fraction("0.66881286")
WIDTH = Fraction("0.00000001")
Z_MINUS = Fraction(1838418790980431, 2748779069440000)
Z_PLUS = Fraction(45960469774511, 68719476736000)


def maximum(values):
    out = arb(0)
    seen = False
    for value in values:
        seen = True
        require(value.is_finite(), "nonfinite cell enclosure")
        if value.upper() > out:
            out = value.upper()
    require(seen, "empty collection of cell bounds")
    return out


def derivative_cells(tm, endpoint, h, da, dt, order=48):
    """Enclose mixed derivatives on closed frequency cells.

    The omitted parameter polynomial is differentiated with Cauchy's
    coefficient estimate. The omitted moment series uses a Cauchy circle
    of radius rho-w. The frequency Taylor remainder bounds the actual high
    derivative on the complex-parameter square. Its bound is not a
    probability moment at a complex parameter.
    """
    require(da in (0, 1), "only zero or one parameter derivative is supported")
    require(dt >= 0 and order + dt <= tm.N, "invalid frequency derivative order")
    K, N = tm.Kser, tm.N
    w, q, rho = fq(tm.w), fq(tm.q), fq(tm.rho)
    require(0 < q and q < 1 and w < rho, "Cauchy radii are invalid")
    ncell = int((endpoint / (2*h)).upper().ceil().unique_fmpz())
    require(endpoint <= 2*ncell*h, "frequency cells do not cover endpoint")
    centers = [(2*j+1)*h for j in range(ncell)]
    vals = [[arb(0)]*ncell for _ in range(order)]
    for i in range(da, K+1):
        weight = i*w**(i-1) if da else w**i
        re, im = [arb(0)]*(N+1), [arb(0)]*(N+1)
        for n in range(N+1):
            c = tm.ccoef[n][i]
            if n % 2:
                im[n] = c if n % 4 == 1 else -c
            else:
                re[n] = c if n % 4 == 0 else -c
        pr, pi = arb_poly(re), arb_poly(im)
        for _ in range(dt):
            pr, pi = pr.derivative(), pi.derivative()
        for k in range(order):
            for j, tc in enumerate(centers):
                vr, vi = pr(tc), pi(tc)
                vals[k][j] += weight*(vr*vr+vi*vi).sqrt()
            pr, pi = pr.derivative(), pi.derivative()
    pa = [tm.Pabs]
    for _ in range(order+dt):
        pa.append(pa[-1].derivative())
    qfac = q**K*((K+1)-K*q)/(rho*(1-q)**2) if da else q**(K+1)/(1-q)
    cauchy = 1/(rho-w) if da else arb(1)
    tmax = 2*ncell*h
    remainder = cauchy*(pa[order+dt](tmax)+tm.tailS(tmax, order+dt))*h**order/arb.fac_ui(order)
    cells = []
    for j, tc in enumerate(centers):
        total = remainder
        for k in range(order):
            error = pa[k+dt](tc)*qfac+cauchy*tm.tailS(tc, k+dt)
            total += (vals[k][j]+error)*h**k/arb.fac_ui(k)
        cells.append((2*j*h, 2*(j+1)*h, total.upper()))
    return cells, remainder


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=1400)
    parser.add_argument("--moments", type=int, default=1000)
    parser.add_argument("--output", type=Path, default=Path(__file__).parent / "data/transition_derivative_certificate.json")
    args = parser.parse_args()
    start = time.monotonic()
    checks = {}

    def check(name, condition):
        require(bool(condition), name)
        checks[name] = True
        print("PASS", name, flush=True)

    check("old_zero_bracket_inside_parameter_interval",
          A0-WIDTH < Z_MINUS < Z_PLUS < A0+WIDTH)
    tm = TaylorModel(A0, WIDTH, q=Fraction(1, 10000), N=args.moments,
                     prec=args.precision)
    beta, gamma = 8, 7
    T2, T, h = arb(6), arb(10), fq(Fraction(1, 32))
    base = tm.certify(Fraction(6), Fraction(1, 32), beta=beta)
    C, R, M = fq(Fraction(17, 1000)), fq(Fraction(83, 1000)), arb(2)
    D1, Ma, Da = arb(2), arb(4), arb(4)
    a = fq(A0-WIDTH).union(fq(A0+WIDTH))
    check("base_fourier_bootstrap", base["boot"])
    check("base_tail_begins_before_ten", base["T3"] < T)
    check("base_C_below_17_over_1000", base["C"] < C)
    check("base_R_below_83_over_1000", base["R"] < R)
    check("absolute_first_moment_below_two", 2*tm.cS[2] < M*M)
    check("parameter_tail_exponent_integrable", gamma > 3 and a*gamma > 1)

    ucells, urem = derivative_cells(tm, T, h, da=0, dt=1)
    initial_u = maximum(s*r**beta for l, r, s in ucells if r >= T2)
    A1 = M*C*arb(2)**(a*(beta-1))/(a+1)
    check("frequency_derivative_initial_below_two", initial_u < D1)
    check("frequency_derivative_forcing_below_one", A1 < 1)
    check("frequency_derivative_strict_bootstrap", A1+R*D1 < D1)

    wcells, wrem = derivative_cells(tm, T, h, da=1, dt=0)
    small_w = maximum(s for l, r, s in wcells if l < T2)
    initial_w = maximum(s*r**gamma for l, r, s in wcells if r >= T2)
    check("compact_parameter_derivative_below_four", small_w < Ma)
    check("parameter_derivative_initial_below_four", initial_w < Da)
    J = 2*C*arb(2)**(a*beta)*T**(gamma-beta-1/a)
    kappa = R+J*T2**(1/a-gamma)/(a*gamma-1)
    A_small = J*Ma*T2**(1/a)
    log2 = arb(2).log()
    A_chain = M*C*arb(2)**(a*(beta-1))*(log2/(a+1)+1/(a+1)**2)
    A_chain += D1*log2*R
    A_mix = C*R/T
    A_force = A_small+A_chain+A_mix
    check("parameter_contraction_below_one_tenth", kappa < fq(Fraction(1, 10)))
    check("parameter_forcing_below_two", A_force < 2)
    check("parameter_derivative_strict_bootstrap", A_force+kappa*Da < Da)

    K, q, rho, w = base["K"], fq(tm.q), fq(tm.rho), fq(tm.w)
    coeffs = [sum(((-1 if n % 4 else 1)*tm.ccoef[n][i]*T**(n+3)/(n+3)
                   for n in range(0, tm.N+1, 2)), arb(0)) for i in range(K+1)]
    finite = -eval_G([i*coeffs[i] for i in range(1, K+1)], arb(0, w))/arb.pi()
    majorant = sum((tm.cS[n]*T**(n+3)/(n+3) for n in range(0, tm.N+1, 2)), arb(0))
    error_parameter = majorant*q**K*((K+1)-K*q)/(rho*(1-q)**2)
    error_series = T**3/3*tm.tailS(T)/(rho-w)
    error_tail = Da*T**(3-gamma)/(gamma-3)
    error = (error_parameter+error_series+error_tail)/arb.pi()
    derivative = finite+arb(0, error.upper())
    check("central_curvature_parameter_derivative_above_68_over_100", derivative > fq(Fraction(68, 100)))
    check("central_curvature_parameter_derivative_below_70_over_100", derivative < fq(Fraction(70, 100)))

    # At the unique zero, strict negativity excludes a flat central minimum.
    power = 4
    fourth_coeffs = [sum(((-1 if n % 4 else 1)*tm.ccoef[n][i]*T**(n+power+1)/(n+power+1)
                          for n in range(0, tm.N+1, 2)), arb(0)) for i in range(K+1)]
    fourth_majorant = sum((tm.cS[n]*T**(n+power+1)/(n+power+1)
                            for n in range(0, tm.N+1, 2)), arb(0))
    fourth_error = fourth_majorant*q**(K+1)/(1-q)
    fourth_error += T**(power+1)/(power+1)*tm.tailS(T)
    fourth_error += C*T**(power+1-beta)/(beta-power-1)
    fourth = eval_G(fourth_coeffs, arb(0, w))/arb.pi()+arb(0, (fourth_error/arb.pi()).upper())
    check("fourth_spatial_derivative_above_minus_9_over_100", fourth > fq(Fraction(-9, 100)))
    check("fourth_spatial_derivative_below_minus_7_over_100", fourth < fq(Fraction(-7, 100)))

    result = {
        "all_checks_passed": True,
        "parameter_interval": [str(A0-WIDTH), str(A0+WIDTH)],
        "old_zero_bracket": [str(Z_MINUS), str(Z_PLUS)],
        "adopted_bounds": {"C": "17/1000", "R": "83/1000", "M": "2", "D1": "2", "Ma": "4", "Da": "4", "beta": 8, "gamma": 7, "T2": "6", "T": "10", "kappa_upper": "1/10", "forcing_upper": "2", "curvature_parameter_derivative": ["68/100", "70/100"], "fourth_spatial_derivative": ["-9/100", "-7/100"]},
        "enclosures": {key: str(value) for key, value in {
            "base_C": base["C"], "base_R": base["R"], "base_T3": base["T3"],
            "initial_frequency_derivative": initial_u, "frequency_forcing": A1,
            "compact_parameter_derivative": small_w, "initial_parameter_derivative": initial_w,
            "parameter_kappa": kappa, "parameter_forcing": A_force,
            "frequency_cell_remainder": urem, "parameter_cell_remainder": wrem,
            "finite_frequency_parameter_derivative": finite, "parameter_tail_error": error_tail/arb.pi(),
            "parameter_Taylor_error": error_parameter/arb.pi(), "moment_series_derivative_error": error_series/arb.pi(),
            "central_curvature_parameter_derivative": derivative, "fourth_spatial_derivative": fourth,
            "fourth_spatial_derivative_error": fourth_error/arb.pi()}.items()},
        "checks": checks, "precision_bits": args.precision, "moments": args.moments,
        "parameter_polynomial_degree": K, "frequency_cell_halfwidth": "1/32", "frequency_Taylor_order": 48,
        "python": platform.python_version(), "python_flint": flint.__version__,
        "elapsed_seconds": time.monotonic()-start,
        "source_sha256": {str(path.relative_to(PAPER)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in (Path(__file__), PAPER/"threshold_taylor.py", PAPER/"threshold_pointwise.py")},
        "formal_scope": "Arb-assisted numerical certificate. The certificate's gamma, power-series and Cauchy evaluations are not kernel-checked by Lean."
    }
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print("DERIVATIVE", derivative, flush=True)
    print("FOURTH DERIVATIVE", fourth, flush=True)
    print("ALL CHECKS PASSED", args.output, flush=True)


if __name__ == "__main__":
    main()
