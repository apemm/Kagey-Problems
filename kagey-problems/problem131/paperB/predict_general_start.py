"""Predictions for the Paper B tie / general-start checks (formula evaluation only).

This script evaluates asymptotic formulas and closed forms. It does not compute any
exact probability, so it tests nothing; its output is copied into
data/ledger_B_tie.md before verify_general_start.py is run.
Standard library only.
"""
import math

LOG4PI = math.log(4 * math.pi)


def a_const(k):
    return 0.5 * LOG4PI - (k + 0.5) / (k - 1) * math.log(k)


def solve(f, lo, hi, it=200):
    flo = f(lo)
    for _ in range(it):
        mid = 0.5 * (lo + hi)
        fm = f(mid)
        if (fm > 0) == (flo > 0):
            lo, flo = mid, fm
        else:
            hi = mid
    return 0.5 * (lo + hi)


def z_second_order(L, const, c1):
    """Root z of z - L + (1/2) log z = const + c1/z."""
    return solve(lambda z: z - L + 0.5 * math.log(z) - const - c1 / z, 0.1, L + 50)


def main():
    out = []
    p = out.append
    p("# predict_general_start.py output (formula evaluation only)")
    p("")
    p("## constants")
    for k in range(2, 8):
        a = a_const(k)
        Dk = k ** (k + 0.5) / (4 * math.pi) ** ((k - 1) / 2)
        p(f"k={k}  a_k={a:+.10f}  D_k={Dk:.10f}  exp(-(k-1)a_k)={math.exp(-(k-1)*a):.10f}")
    a2, a3 = a_const(2), a_const(3)
    tef = math.log(1.5) + 2 * a3 - a2
    p(f"K3 mu=(1/2,1/2,0): t_ve = a_2 = {a2:+.10f}; t_ef = log(3/2)+2a_3-a_2 = {tef:+.10f};"
      f" (1/2)log(32pi/243) = {0.5*math.log(32*math.pi/243):+.10f}")
    p(f"  width = {tef-a2:.10f};  log(16/(9 sqrt3)) = {math.log(16/(9*math.sqrt(3))):.10f}")
    p("")
    p("## T4: K3, mu=(1/2,1/2,0), window t = z - L + (1/2) log L, z = N u, u = r/p")
    p("lower: z - L + (1/2)log z = a_2 + 1/(8z);  upper: = t_ef + 1/(12z)  [1/12 = 1/8 - 1/24];"
      "  upper_noshift: = t_ef + 1/(8z)")
    for N in [90, 1002, 10002, 100002, 1000002]:
        L = math.log(N)
        zl = z_second_order(L, a2, 1 / 8)
        zu = z_second_order(L, tef, 1 / 12)
        zu0 = z_second_order(L, tef, 1 / 8)
        tl = zl - L + 0.5 * math.log(L)
        tu = zu - L + 0.5 * math.log(L)
        tu0 = zu0 - L + 0.5 * math.log(L)
        n3 = N * (1 / 3 - 1 / (9 * zu))
        tol = 0.5 / zl ** 2 + zl ** 2 / N
        p(f"N={N:>8}  L={L:.6f}  z_low={zl:.6f} t_low={tl:+.6f}  z_up={zu:.6f} t_up={tu:+.6f}"
          f"  width={tu-tl:.6f}  [noshift t_up={tu0:+.6f} width={tu0-tl:.6f}]"
          f"  n3hat~{n3:.1f}  tol(0.5/z^2+z^2/N)={tol:.4f}")
    p("")
    p("## T3: general-start crossings, d = 4, mu = (2/5, 3/10, 1/5, 1/10)")
    cases = [("A: face {1,2,3} (k=3) vs vertex 1", 3, a3 + 0.5 * math.log(4 / 3), 4 / 3,
              [30, 300, 3000, 30000]),
             ("B: face {2,3} (k=2) vs vertex 4", 2, a2 + math.log(0.4), 0.4,
              [20, 200, 2000, 20000])]
    for name, k, a, target, Ns in cases:
        p(f"{name}: a_k(mu) = {a:+.10f}; exact identity: crossing solves S_n(u) = {target:.10f}")
        if k == 3:
            u = math.sqrt(0.4 / (0.9 * 2))
            p(f"  N=3 exact: u = sqrt(mu_1/(mu(F) 2!)) = {u:.12f}, z = {3*u:.12f}")
        else:
            p(f"  N=2 exact: u = mu_4/mu(F) = {0.2:.12f}, z = 0.4")
        for N in Ns:
            L = math.log(N)
            lL = math.log(L)
            z3 = L - 0.5 * lL + a + (0.25 * lL - 0.5 * a + 0.125) / L
            z2 = z_second_order(L, a, 1 / 8)
            p(f"  N={N:>6}  z_pred(3-term)={z3:.6f}  z_pred(implicit)={z2:.6f}"
              f"  heuristic ahat-a ~ ((k-1)/2) z^2/N = {(k-1)/2*z2**2/N:.5f}"
              f"  tol 1/z^2+z^2/N = {1/z2**2 + z2**2/N:.5f}")
    p("")
    p("## rounding (k=2, odd N): omega_big - omega_small ~ 1/(N A^2) = 1/(2N)")
    for N in [21, 201, 2001]:
        p(f"  N={N}: predicted N*(omega_big-omega_small) in [0.40, 0.60] (heuristic value 0.5(1-1/(4z)))")
    p("## omega lemma, k=2, alpha=(0.6,0.4): omega_1 -> sqrt(.6)/(sqrt(.6)+sqrt(.4)) = "
      f"{math.sqrt(.6)/(math.sqrt(.6)+math.sqrt(.4)):.6f}")
    p("")
    p("## T4' (registered after T4 was killed): add the discrete terms ((k-1)^2/2) z^2/N")
    p("lower: z - L + (1/2)log z = a_2 + 1/(8z) + (1/2) z^2/N")
    p("upper: z - L + (1/2)log z = t_ef + 1/(12z) + (3/2) z^2/N   [2 z^2/N (k=3) - (1/2) z^2/N (k=2)]")
    p("upper_noshift: same with 1/(8z) in place of 1/(12z)")
    for N in [3000, 30000, 300000]:
        L = math.log(N)

        def f(c0, c1, c2):
            return solve(lambda z: z - L + 0.5 * math.log(z) - c0 - c1 / z - c2 * z * z / N,
                         0.1, L + 50)
        zl = f(a2, 1 / 8, 0.5)
        zu = f(tef, 1 / 12, 1.5)
        zu0 = f(tef, 1 / 8, 1.5)
        tl = zl - L + 0.5 * math.log(L)
        tu = zu - L + 0.5 * math.log(L)
        tu0 = zu0 - L + 0.5 * math.log(L)
        tol = 0.2 / zl ** 2 + 3 * zl / N
        p(f"N={N:>7}  t_low={tl:+.6f}  t_up={tu:+.6f}  width={tu-tl:.6f}  [noshift t_up={tu0:+.6f}"
          f" width={tu0-tl:.6f}]  tol(0.2/z^2+3z/N)={tol:.5f}")
    print("\n".join(out))


if __name__ == "__main__":
    main()
