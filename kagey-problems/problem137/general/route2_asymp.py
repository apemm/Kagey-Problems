"""Run R2b (ledger R2-5): partial-fraction error bound for a(n) = C_q psi_q^n + error, q = 3, 4, 6.

Same code as the inline run recorded in data/route2b_run.txt. Floating point with 40 digits.
Usage: python route2_asymp.py
"""
import mpmath as mp

mp.mp.dps = 40
for q in (3, 4, 6):
    D = [mp.mpf(1), mp.mpf(-1)] + [mp.mpf(0)] * (2 * q - 4)
    for j in range(3, 2 * q - 2, 2):
        D[j] = mp.mpf(-1)
    Nn = [mp.mpf(0)] * (2 * q - 3)          # A - 1 = (1 + t) t R_q / D_q
    for i in range(q - 2):
        Nn[2 * i + 1] += 1
        Nn[2 * i + 2] += 1
    roots = mp.polyroots(D[::-1], maxsteps=200, extraprec=200)
    ev = lambda P, x: sum(c * x ** k for k, c in enumerate(P))
    dD = [k * D[k] for k in range(1, len(D))]
    res = [(r, -ev(Nn, r) / (ev(dD, r) * r)) for r in roots]
    i0 = min(range(len(res)), key=lambda i: abs(res[i][0]))
    t0, C = mp.re(res[i0][0]), mp.re(res[i0][1])
    others = [res[i] for i in range(len(res)) if i != i0]
    E = lambda n: sum(abs(c) * abs(r) ** (-n) for r, c in others)
    bad = [n for n in range(1, 80) if E(n) >= 0.5]
    print(f"q={q}: t0={mp.nstr(t0, 15)} psi={mp.nstr(1 / t0, 15)} C={mp.nstr(C, 15)}; "
          f"min other modulus {mp.nstr(min(abs(r) for r, c in others), 8)}; sum|c_i|={mp.nstr(E(0), 6)}; "
          f"n>=1 with E(n)>=1/2: {bad}")
    a = [0] * 81
    Ns = [0] * (2 * q - 2)
    for i in range(q - 1):
        Ns[2 * i] = 1
    Ns[2 * q - 3] = -1
    for n in range(81):
        s = Ns[n] if n < len(Ns) else 0
        s += sum(a[n - j] for j in [1] + list(range(3, 2 * q - 2, 2)) if n - j >= 0)
        a[n] = s
    mism = [n for n in range(1, 81) if int(mp.nint(C * (1 / t0) ** n)) != a[n]]
    print(f"   n in 1..80 where nearest integer of C psi^n != a(n) (series of N_q/D_q): {mism}; a(0..12)={a[:13]}")
