"""Paper A, the crossing at every N (Theorem thm:every-n).  Standard library only.

Checks, each with two independent methods where a number is reported:

  1. zeta_N (root of zeta + log(zeta)/2 = log N + log(pi/8)/2): Decimal Newton vs a
     float Halley iteration for Lambert W (zeta_N = W(pi N^2/4)/2).
  2. Bessel lemma: E(z) = sqrt(pi z/2) e^{-z} (I_0(z)+I_1(z)) by Decimal power series vs a
     trapezoid rule on (1/pi) int_0^pi e^{z(cos t - 1)} (1 + cos t) dt; check the bounds
       1 - 1/(8z) - 3/(128z^2) - 45/(512z^3) <= E(z) <= 1 - 1/(8z) - 3/(128z^2) + 15/(512z^3).
  3. Exact certificates for 2 <= N <= NCERT: decimals u_lo < u_hi (step 1e-9) with
     S_N(u_lo) < 1 < S_N(u_hi), each decided by exact integers computed twice
     (run-count binomial formula; integer transfer-matrix DP over words), then
       zeta + 1/(8 zeta) - zeta(zeta+1)/N - 1/(16 zeta^2) <= z(u_lo),  z(u_hi) < zeta + 1/(8 zeta)
     and the R_N bounds, with z(u) = N u/(1+u), in 60-digit Decimal.
  4. The explicit margin functions of the analytic proof (zeta >= 4) on a fine grid, and the
     exact sufficient conditions (exact Bessel function) for every N up to NSUFF.
  5. A table of z_N: run-count Decimal bisection vs float DP bisection (plus a DP sign check at
     u_N(1 -+ 1e-9) for N = 10^4).
  6. Sign pattern of z_N - zeta_N: sign of S_N(zeta/(N-zeta)) - 1, float run-count for all
     N <= NSIGN and float DP for N <= NSIGN_DP; the sign changes are certified exactly.

Output: data/every_n_output.txt (and data/every_n_certificates.csv).
"""
import math
import sys
import time
from decimal import Decimal as D, getcontext
from fractions import Fraction
from math import comb

getcontext().prec = 60
PI_STR = "3.14159265358979323846264338327950288419716939937510582097494459"
PI = D(PI_STR)
assert abs(float(PI) - math.pi) < 1e-15
C0 = (PI / 8).ln() / 2
NCERT_BOTH = 400      # certificates with both exact methods
NCERT_RUN = 1000      # run-count exact certificates (cross-check of the analytic range)
NSUFF = 3000
NSIGN = 3000
NSIGN_DP = 3000
OUT = []


def out(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    OUT.append(s)


# ---------------------------------------------------------------- zeta_N
def zeta_dec(N):
    K = D(N).ln() + C0
    z = D(max(0.5, math.log(N) - 0.5 * math.log(max(math.log(N), 0.5))))
    for _ in range(200):
        f = z + z.ln() / 2 - K
        z_new = z - f / (1 + 1 / (2 * z))
        if abs(z_new - z) < D(10) ** -55:
            z = z_new
            break
        z = z_new
    # rigorous bracket (Decimal ln is correctly rounded)
    h = D(10) ** -45
    assert (z - h) + (z - h).ln() / 2 < K < (z + h) + (z + h).ln() / 2
    return z


def zeta_lambert(N):
    """float Halley iteration for w e^w = x, x = pi N^2/4; zeta = w/2."""
    x = math.pi * N * N / 4
    w = math.log(x) - math.log(math.log(x)) if x > 3 else 0.5
    for _ in range(100):
        ew = math.exp(w)
        f = w * ew - x
        wn = w - f / (ew * (w + 1) - (w + 2) * f / (2 * w + 2))
        if abs(wn - w) < 1e-15 * max(1, abs(w)):
            w = wn
            break
        w = wn
    return w / 2


# ---------------------------------------------------------------- Bessel
def E_series(z):
    z = D(z)
    t = z / 2
    s0 = D(0)
    s1 = D(0)
    term = D(1)  # (t)^{2r}/(r!)^2
    r = 0
    while True:
        s0 += term
        s1 += term * t / (r + 1)
        term = term * t * t / ((r + 1) * (r + 1))
        r += 1
        if r > 2 * t + 10 and term < (s0 + s1) * D(10) ** -58:
            break
    return (PI * z / 2).sqrt() * (-z).exp() * (s0 + s1)


def E_trap(z, M=4000):
    tot = 0.0
    for k in range(M + 1):
        t = math.pi * k / M
        f = math.exp(z * (math.cos(t) - 1)) * (1 + math.cos(t))
        tot += f * (0.5 if k in (0, M) else 1.0)
    return math.sqrt(math.pi * z / 2) * tot / M


def Phi_dec(w):
    """Phi(w) = w (I_0(w) + I_1(w)) = sqrt(2w/pi) e^w E(w)."""
    w = D(w)
    return (2 * w / PI).sqrt() * w.exp() * E_series(w)


# ---------------------------------------------------------------- S_N exact
def runcount_coeffs(N):
    """W(N, m, j), j = 0..N-1, m = floor(N/2) (Theorem pmf of Paper A)."""
    a, b = N // 2, N - N // 2
    W = [0] * N
    for j in range(1, N):
        if j % 2 == 1:
            i = (j + 1) // 2
            W[j] = 2 * comb(a - 1, i - 1) * comb(b - 1, i - 1)
        else:
            i = j // 2
            W[j] = comb(a - 1, i) * comb(b - 1, i - 1) + comb(a - 1, i - 1) * comb(b - 1, i)
    return W


def S_int_runcount2(W, num, den):
    """sum_j W_j num^j den^(N-1-j) (exact integer), from the run-count coefficients."""
    deg = len(W) - 1
    dpows = [1] * (deg + 1)
    for k in range(1, deg + 1):
        dpows[k] = dpows[k - 1] * den
    total = 0
    npow = 1
    for j in range(deg + 1):
        if W[j]:
            total += W[j] * npow * dpows[deg - j]
        npow *= num
    return total


def S_int_dp(N, num, den):
    """Integer DP over words: weight den per repeat, num per change; returns the weighted
    count of words with m = floor(N/2) letters R (= sum_j W_j num^j den^(N-1-j))."""
    m = N // 2
    Rv = [0] * (m + 1)
    Lv = [0] * (m + 1)
    if m >= 1:
        Rv[1] = 1
    Lv[0] = 1
    for n in range(2, N + 1):
        lo = max(0, n - (N - m))
        hi = min(n, m)
        nR = [0] * (m + 1)
        nL = [0] * (m + 1)
        for k in range(lo, hi + 1):
            if k >= 1:
                nR[k] = den * Rv[k - 1] + num * Lv[k - 1]
            nL[k] = den * Lv[k] + num * Rv[k]
        Rv, Lv = nR, nL
    return Rv[m] + Lv[m]


# ---------------------------------------------------------------- S_N float
def S_float(N, u):
    """run-count by term ratios (float)."""
    a, b = N // 2, N - N // 2
    tot = 0.0
    T = 1.0
    for r in range(a):
        tot += T * (2 * u + u * u * (N - 2 - 2 * r) / (r + 1))
        T *= (a - 1 - r) * (b - 1 - r) * u * u / ((r + 1) ** 2)
        if T == 0.0:
            break
    return tot


def S_float_dp(N, u):
    m = N // 2
    Rv = [0.0] * (m + 1)
    Lv = [0.0] * (m + 1)
    if m >= 1:
        Rv[1] = 1.0
    Lv[0] = 1.0
    for n in range(2, N + 1):
        lo = max(0, n - (N - m))
        hi = min(n, m)
        nR = [0.0] * (m + 1)
        nL = [0.0] * (m + 1)
        for k in range(lo, hi + 1):
            if k >= 1:
                nR[k] = Rv[k - 1] + u * Lv[k - 1]
            nL[k] = Lv[k] + u * Rv[k]
        Rv, Lv = nR, nL
    return Rv[m] + Lv[m]


def S_dec(N, u):
    a, b = N // 2, N - N // 2
    tot = D(0)
    T = D(1)
    for r in range(a):
        tot += T * (2 * u + u * u * (N - 2 - 2 * r) / (r + 1))
        T = T * ((a - 1 - r) * (b - 1 - r)) * u * u / ((r + 1) ** 2)
        if T == 0:
            break
        if r > 10 and T < tot * D(10) ** -55 and (a - 1 - r) * (b - 1 - r) * u * u < (r + 1) ** 2 / 2:
            break
    return tot


def root_float(N, f=S_float):
    lo, hi = 0.0, 0.5
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(N, mid) < 1:
            lo = mid
        else:
            hi = mid
        if hi - lo < 1e-17:
            break
    return (lo + hi) / 2


def root_dec(N):
    lo, hi = D(0), D("0.5")
    for _ in range(170):
        mid = (lo + hi) / 2
        if S_dec(N, mid) < 1:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def zfun(N, u):
    return D(N) * u / (1 + u)


def psi(z):
    return z + z.ln() / 2


# ================================================================== run
def main():
    t0 = time.time()
    out("verify_every_n.py  (Paper A, crossing for every N)  run", time.strftime("%Y-%m-%d %H:%M"))
    out("c_0 =", f"{C0:.30f}")

    # ---------------- 1. zeta_N two ways
    out("\n[1] zeta_N: Decimal Newton vs float Lambert-W (Halley)")
    maxdiff = 0.0
    for N in list(range(2, 2001)) + [5000, 10000, 100000, 10 ** 6]:
        z1 = zeta_dec(N)
        z2 = zeta_lambert(N)
        maxdiff = max(maxdiff, abs(float(z1) - z2) / float(z1))
    out(f"  N in 2..2000 and 5e3,1e4,1e5,1e6: max relative difference = {maxdiff:.2e}")
    N4 = (D(32) / PI).sqrt() * D(4).exp()
    out(f"  N(zeta=4) = sqrt(32/pi) e^4 = {N4:.12f}  -> zeta_N >= 4 iff N >= {math.ceil(N4)}")
    for N in (174, 175):
        out(f"  zeta_{N} = {zeta_dec(N):.15f}")
    N0 = math.ceil(N4)

    # ---------------- 2. Bessel lemma
    out("\n[2] Bessel lemma: E(z) by series (Decimal) vs trapezoid (float), and the bounds")
    out("   z        E_series              E_trap      |diff|     lower-gap    upper-gap   z^3*(E-1+1/(8z)+3/(128z^2))")
    zs = ["0.01", "0.05", "0.1", "0.2", "0.5", "1", "1.25", "2", "3", "4", "5", "7", "10", "15", "20",
          "30", "50", "100", "200"]
    worst = 0.0
    for zst in zs:
        z = D(zst)
        e1 = E_series(z)
        e2 = E_trap(float(z))
        base = 1 - 1 / (8 * z) - D(3) / (128 * z * z)
        lo = base - D(45) / (512 * z ** 3)
        hi = base + D(15) / (512 * z ** 3)
        assert lo <= e1 <= hi, zst
        worst = max(worst, abs(float(e1) - e2))
        out(f"  {zst:>6} {e1:.18f} {e2:.15f} {abs(float(e1)-e2):.1e} {float(e1-lo):.3e} {float(hi-e1):.3e} {float((e1-base)*z**3):+.6f}")
    # dense grid check of the bounds (series only; the trapezoid agrees above)
    cnt = 0
    for k in range(1, 2001):
        z = D(k) / 20
        e1 = E_series(z)
        base = 1 - 1 / (8 * z) - D(3) / (128 * z * z)
        assert base - D(45) / (512 * z ** 3) <= e1 <= base + D(15) / (512 * z ** 3)
        assert e1 <= 1
        if z >= D("1.25"):
            assert e1 <= 1 - 1 / (8 * z)
        cnt += 1
    out(f"  bounds hold on the grid z = 0.05, 0.10, ..., 100 ({cnt} points); max |series - trapezoid| = {worst:.1e}")
    out("  -15/1024 = %.6f (predicted limit of the last column)" % (-15 / 1024))

    # ---------------- 3. exact certificates
    out(f"\n[3] exact certificates, N = 2..{NCERT_BOTH} (run-count and DP), N = {NCERT_BOTH+1}..{NCERT_RUN} (run-count only)")
    den = 10 ** 9
    rows = []
    min_up = (None, D(10))
    min_lo = (None, D(10))
    min_Rup = (None, D(10))
    min_Rlo = (None, D(10))
    tdp = 0.0
    trc = 0.0
    sgn_cert = {}
    for N in range(2, NCERT_RUN + 1):
        uf = root_float(N)
        a = int(math.floor(uf * den))
        W = runcount_coeffs(N)
        target = den ** (N - 1)
        # adjust so that S(a/den) < 1 < S(a1/den), a1 = a+1 (a+2 if a+1 is an exact root)
        a1 = a + 1
        for _ in range(8):
            t1 = time.time()
            vlo = S_int_runcount2(W, a, den)
            vhi = S_int_runcount2(W, a1, den)
            trc += time.time() - t1
            if vlo >= target:
                a -= 1
                continue
            if vhi < target:
                a, a1 = a1, a1 + 1
                continue
            if vhi == target:      # exact rational root on the grid (N = 2: u = 1/2)
                a1 += 1
                continue
            break
        assert vlo < target < vhi, N
        both = N <= NCERT_BOTH
        if both:
            t1 = time.time()
            dlo = S_int_dp(N, a, den)
            dhi = S_int_dp(N, a1, den)
            tdp += time.time() - t1
            assert dlo == vlo and dhi == vhi, ("DP mismatch", N)
        ulo = D(a) / den
        uhi = D(a1) / den
        zlo = zfun(N, ulo)
        zhi = zfun(N, uhi)
        zt = zeta_dec(N)
        upper = zt + 1 / (8 * zt)
        eps = zt * (zt + 1) / N + 1 / (16 * zt * zt)
        lower = upper - eps
        mu = upper - zhi
        ml = zlo - lower
        assert mu > D(10) ** -30 and ml > D(10) ** -30, N
        if mu < min_up[1]:
            min_up = (N, mu)
        if ml < min_lo[1]:
            min_lo = (N, ml)
        # R_N bounds: R increasing in z, bounds decreasing in z
        K = D(N).ln() + C0
        Rhi = psi(zhi) - K - 1 / (8 * zhi)
        Rlo = psi(zlo) - K - 1 / (8 * zlo)
        gu = 1 / (16 * zhi * zhi) - Rhi
        gl = Rlo + (zlo * zlo + zlo) / N
        assert gu > 0 and gl > 0, ("R bounds", N)
        if gu < min_Rup[1]:
            min_Rup = (N, gu)
        if gl < min_Rlo[1]:
            min_Rlo = (N, gl)
        rows.append((N, a, a1, zlo, zhi, zt, mu, ml, Rlo, Rhi, both))
        sgn_cert[N] = 1 if zlo > zt else (-1 if zhi < zt else 0)
        Ld = D(N).ln()
        # L-form of the R_N bound: z_N >= L/2 (N >= 2), z_N <= L (N >= 3)
        assert zlo >= Ld / 2 and (N == 2 or zhi <= Ld), ("L-form", N)
        lam = Ld - Ld.ln() / 2 + C0
        assert lam <= zt <= lam + (Ld.ln() - 2 * C0) / (4 * lam), ("zeta bracket", N)
        if N == N0 - 1:
            out(f"  N = 2..{N}: all certificates pass. smallest upper margin {float(min_up[1]):.6f} at N = {min_up[0]},"
                f" smallest lower margin {float(min_lo[1]):.6f} at N = {min_lo[0]}")
            out(f"     R_N: smallest gap to 1/(16 z^2) is {float(min_Rup[1]):.6f} at N = {min_Rup[0]};"
                f" smallest gap to -(z^2+z)/N is {float(min_Rlo[1]):.6f} at N = {min_Rlo[0]}")
    out(f"  N = 2..{NCERT_RUN}: all certificates pass; DP agreed exactly for N <= {NCERT_BOTH}.")
    out(f"     also checked for every N in 2..{NCERT_RUN}: L/2 <= z_N (and z_N <= L for N >= 3);"
        f" lambda_N <= zeta_N <= lambda_N + (log L - 2c_0)/(4 lambda_N), lambda_N = L - (1/2)log L + c_0")
    und = [N for N in sgn_cert if sgn_cert[N] == 0]
    chg = [N for N in range(3, NCERT_RUN + 1) if sgn_cert[N] != sgn_cert[N - 1]]
    out(f"     exact sign of z_N - zeta_N from the certificates: undecided at {und}; sign(N=2) = {sgn_cert[2]:+d}; changes at {chg}")
    out(f"     smallest upper margin {float(min_up[1]):.7f} at N = {min_up[0]}; smallest lower margin {float(min_lo[1]):.7f} at N = {min_lo[0]}")
    out(f"     time: run-count {trc:.1f}s, DP {tdp:.1f}s")
    with open("data/every_n_certificates.csv", "w") as f:
        f.write("N,u_lo_times_1e9,u_hi_times_1e9,z_lo,z_hi,zeta_N,upper_margin,lower_margin,R_lo,R_hi,dp_checked\n")
        for (N, a, a1, zlo, zhi, zt, mu, ml, Rlo, Rhi, both) in rows:
            f.write(f"{N},{a},{a1},{zlo:.12f},{zhi:.12f},{zt:.12f},{mu:.9f},{ml:.9f},{Rlo:.9f},{Rhi:.9f},{int(both)}\n")
    out("  certificates written to data/every_n_certificates.csv")
    # Paper A's Table tab:pn
    tab = {2: "0.66666667", 3: "0.70710678", 4: "0.74487450", 5: "0.76759188", 6: "0.78871211",
           7: "0.80361731", 8: "0.81759938", 9: "0.82829163", 10: "0.83840411", 11: "0.84652725",
           12: "0.85426060", 20: "0.89293837", 50: "0.94200405", 100: "0.96496633", 200: "0.97939018",
           400: "0.98812464"}
    bad = []
    for (N, a, a1, *_rest) in rows:
        if N in tab:
            p_hi = 1 / (1 + D(a) / den)
            p_lo = 1 / (1 + D(a1) / den)
            pt = D(tab[N])
            if not (p_lo - D("5e-9") <= pt <= p_hi + D("5e-9")):
                bad.append(N)
    out(f"  Paper A Table tab:pn consistent with the certified brackets (to its 8 decimals): {'yes' if not bad else bad}")

    # ---------------- 4. analytic margins and exact sufficient conditions
    out("\n[4a] margin functions of the analytic proof on zeta in [4, 60], step 0.001")

    def Nof(z):
        return math.sqrt(8 * z / math.pi) * math.exp(z)

    def margins(z):
        N = Nof(z)
        U = z + 1 / (8 * z)
        r = U / N
        tp = 1 / (8 * z) + 3 / (128 * z * z) + 37 / (512 * z ** 3) + 1 / (512 * z ** 5)
        BU = 5 / (128 * z * z) - 37 / (512 * z ** 3) - 1 / (256 * z ** 4) - 1 / (512 * z ** 5) - tp * tp / (2 * (1 - tp))
        dl = U * r / (2 * (1 - r) ** 2) + r / (1 - r)
        DU = (r / (2 * (1 - r))) * (U * (1 - 2 * r) / (1 - r) - (1 + r)) - dl * dl / (2 * (1 - dl))
        eps = z * (z + 1) / N + 1 / (16 * z * z)
        ell = U - eps
        rho = ell / N
        bl = -(3 / (128 * z * z)) * (1 - 2 * r) * (1 - 1 / (4 * z * z)) + 15 / (512 * ell ** 3) - 1 / (64 * z ** 3)
        dlw = ((ell * ell + ell / 2) / (1 - rho) + 0.125 - (z * z + 1.5 * z + 0.5)) / N
        return BU, DU, bl, dlw, z * z * BU
    prev = -1
    ok = True
    worst = [1e9, 1e9, -1e9, -1e9]
    for k in range(0, 56001):
        z = 4 + k / 1000
        BU, DU, bl, dlw, z2BU = margins(z)
        if not (BU > 0 and DU > 0 and bl < 0 and dlw < 0):
            ok = False
        if z2BU < prev - 1e-15:
            ok = False
        prev = z2BU
        worst = [min(worst[0], z2BU), min(worst[1], DU * Nof(z) / z), max(worst[2], bl * z * z), max(worst[3], dlw * Nof(z) / z)]
    out(f"  B_U>0, D_U>0, beta_l<0, delta_l<0 and zeta^2 B_U nondecreasing on the grid: {ok}")
    out(f"  min zeta^2 B_U = {worst[0]:.6f} ; min D_U N/zeta = {worst[1]:.4f} ; max beta_l zeta^2 = {worst[2]:.6f} ; max delta_l N/zeta = {worst[3]:.4f}")
    BU, DU, bl, dlw, z2BU = margins(4.0)
    out(f"  at zeta = 4: zeta^2 B_U = {z2BU:.6f}, D_U = {DU:.6f}, beta_l = {bl:.3e}, delta_l = {dlw:.3e}")
    for z in (3.0, 3.5):
        BU, DU, bl, dlw, z2BU = margins(z)
        out(f"  (outside the proof) zeta = {z}: B_U = {BU:.3e}, D_U = {DU:.3e}, beta_l = {bl:.3e}, delta_l = {dlw:.3e}")

    out(f"\n[4b] sufficient conditions evaluated per N (N = 2..{NSUFF})")
    out("     up: Phi(W)(1 - W(W+2)/(2N)) > N/2 with W = N U/(N-U), U = zeta + 1/(8 zeta)")
    out("     lo: Phi(W') <= N/2 with W' = N l/(N-l), l = U - zeta(zeta+1)/N - 1/(16 zeta^2)")
    fail = {"up_exact": [], "lo_exact": [], "up_lemma": [], "lo_lemma": []}
    pass  # keep 60 digits (zeta_dec checks a 1e-45 bracket)
    for N in range(2, NSUFF + 1):
        zt = zeta_dec(N)
        U = zt + 1 / (8 * zt)
        W = N * U / (N - U)
        dl = W * (W + 2) / (2 * N)
        PhiW = Phi_dec(W)
        if not (PhiW * (1 - dl) > D(N) / 2):
            fail["up_exact"].append(N)
        Elem = 1 - 1 / (8 * W) - D(3) / (128 * W * W) - D(45) / (512 * W ** 3)
        PhiLo = (2 * W / PI).sqrt() * W.exp() * max(Elem, D(0))
        if not (PhiLo * (1 - dl) > D(N) / 2):
            fail["up_lemma"].append(N)
        ell = U - zt * (zt + 1) / N - 1 / (16 * zt * zt)
        if ell <= 0:
            continue  # lower bound trivial
        Wp = N * ell / (N - ell)
        if not (Phi_dec(Wp) <= D(N) / 2):
            fail["lo_exact"].append(N)
        Eup = min(D(1), 1 - 1 / (8 * Wp) - D(3) / (128 * Wp * Wp) + D(15) / (512 * Wp ** 3))
        PhiHi = (2 * Wp / PI).sqrt() * Wp.exp() * Eup
        if not (PhiHi <= D(N) / 2):
            fail["lo_lemma"].append(N)
    getcontext().prec = 60
    for k, v in fail.items():
        thr = (max(v) + 1) if v else 2
        out(f"  {k:9s}: fails at {v if len(v) < 30 else str(v[:30]) + '...'} -> holds for every N in [{thr}, {NSUFF}]")

    # ---------------- 5. table
    out("\n[5] z_N = N(1-p_N): method 1 = run-count Decimal bisection; method 2 = float DP")
    out("   N      z_N (method 1)        z_N (method 2)       zeta_N        err_N=z-zeta-1/(8zeta)  heur    eps_N   R_N")
    table_N = [2, 3, 4, 5, 10, 20, 50, 100, 174, 175, 200, 400, 1000, 10000]
    for N in table_N:
        t1 = time.time()
        getcontext().prec = 50
        u1 = root_dec(N)
        z1 = zfun(N, u1)
        u2 = root_float(N, S_float_dp)
        z2s = f"{N*u2/(1+u2):.12f}"
        if N == 10000:
            uf = float(u1)
            s_lo = S_float_dp(N, uf * (1 - 1e-9))
            s_hi = S_float_dp(N, uf * (1 + 1e-9))
            assert s_lo < 1 < s_hi
        zt = zeta_dec(N)
        err = z1 - zt - 1 / (8 * zt)
        heur = -1 / (32 * zt * zt) - (zt - 1) * (2 * zt - 1) / (4 * N)
        eps = zt * (zt + 1) / N + 1 / (16 * zt * zt)
        K = D(N).ln() + C0
        R = psi(z1) - K - 1 / (8 * z1)
        out(f"  {N:>6} {z1:.15f} {z2s:>22} {zt:.10f} {float(err):+.7f} {float(heur):+.5f} {float(eps):.5f} {float(R):+.6f}   ({time.time()-t1:.1f}s)")
    getcontext().prec = 60

    # ---------------- 6. sign pattern of z_N - zeta_N
    out(f"\n[6] sign of z_N - zeta_N = sign of 1 - S_N(zeta/(N-zeta)); float run-count N <= {NSIGN}, float DP N <= {NSIGN_DP}")
    signs = {}
    mism = []
    t1 = time.time()
    for N in range(2, NSIGN + 1):
        zt = float(zeta_dec(N)) if N <= 400 else zeta_lambert(N)
        uz = zt / (N - zt)
        s1 = S_float(N, uz)
        sg = 1 if s1 < 1 else -1
        signs[N] = sg
        if N <= NSIGN_DP:
            s2 = S_float_dp(N, uz)
            if (s2 < 1) != (s1 < 1) or abs(s1 - s2) > 1e-9:
                mism.append(N)
    changes = [N for N in range(3, NSIGN + 1) if signs[N] != signs[N - 1]]
    out(f"  float methods disagree at: {mism}   ({time.time()-t1:.1f}s)")
    out(f"  sign(z_2 - zeta_2) = {signs[2]:+d}; sign changes at N = {changes} (first N with the new sign)")
    # exact certification of the sign at the change points
    for N in sorted(set(sum([[c - 1, c] for c in changes], []))):
        zt = zeta_dec(N)
        # rational just below / above zeta/(N-zeta)
        uz = zt / (N - zt)
        den2 = 10 ** 30
        aa = int((uz * den2).to_integral_value(rounding="ROUND_FLOOR"))
        # guard: both grid points clear u_zeta by more than the 1e-45 error in zeta_N
        # (added after the recorded run; checked in verify_every_n_guards.py [G2])
        assert uz - D(aa) / den2 > D(10) ** -40 and D(aa + 1) / den2 - uz > D(10) ** -40, N
        W = runcount_coeffs(N)
        tg = den2 ** (N - 1)
        v1 = S_int_runcount2(W, aa, den2)
        v2 = S_int_runcount2(W, aa + 1, den2)
        d1 = S_int_dp(N, aa, den2)
        d2 = S_int_dp(N, aa + 1, den2)
        assert v1 == d1 and v2 == d2
        # z_N > zeta  <=>  u_N > u_zeta  <=  S(u_hi) < 1 with u_hi >= u_zeta
        if v2 < tg:
            verdict = "+ (exact)"
        elif v1 > tg:
            verdict = "- (exact)"
        else:
            verdict = "undecided"
        out(f"  N = {N}: z_N - zeta_N sign {verdict}")

    # N_2: from the theorem, z_N >= zeta + 1/(8 zeta) - zeta(zeta+1)/N - 1/(16 zeta^2) > zeta once
    # N (1/(8 zeta) - 1/(16 zeta^2)) > zeta(zeta+1)
    N2 = None
    for N in range(2, 20001):
        zt = zeta_dec(N)
        if D(N) * (1 / (8 * zt) - 1 / (16 * zt * zt)) > zt * (zt + 1):
            if N2 is None:
                N2 = N
        else:
            N2 = None
    out(f"  theorem gives z_N > zeta_N for every N >= N_2 = {N2} (checked to 20000; beyond, the gap grows)")
    out(f"\ntotal time {time.time()-t0:.1f}s")
    with open("data/every_n_output.txt", "w") as f:
        f.write("\n".join(OUT) + "\n")


if __name__ == "__main__":
    main()
