"""Taylor models in a for f_a''(0): a uniform enclosure on a whole interval of a.

For an interval I = [a0 - w, a0 + w] this module returns a polynomial G and a
number eta with   f_a''(0) in G(a - a0) +- eta   for every real a in I.
The parameter a is never an interval inside the cancelling t-series:
  * the Taylor coefficients in eps = a - a0 are computed at the point a0
    (arb_series arithmetic on the moment recursion), so the cancellation in
    the t-series is resolved by working precision, as in erw_cf.py;
  * the Taylor remainder is bounded by a Cauchy estimate on the complex disc
    |z - a0| <= rho = w/q.  It uses enclosures of |c_n(z)| on a square that
    contains the disc (acb arithmetic on the recursion, one coefficient at a
    time, where nothing cancels) and the complex form of Lemma 1;
  * the tail int_T3^oo t^2 |phi_a| is bounded uniformly on I by Lemma 4. Its
    cell bounds sup_{a in I} |phi_a(t)| come from the same Taylor models
    (Taylor in t at the cell centre, Taylor in eps, Cauchy remainders).
See 02_report.md, Section 2, for the statements (Lemmas 6 to 8).
"""
from fractions import Fraction

from flint import acb, arb, arb_poly, arb_series, ctx, fmpq


def fq(x):
    x = Fraction(x)
    return arb(fmpq(x.numerator, x.denominator))


class TaylorModel:
    def __init__(self, a0, w, q=Fraction(1, 32), N=1500, prec=1200, K=None,
                 target_log=-60.0, Kmax=160, scaled=False):
        ctx.prec = prec
        self.scaled = scaled
        self.a0, self.w, self.q = Fraction(a0), Fraction(w), Fraction(q)
        rho = self.w / self.q
        self.rho = rho
        a0b = fq(a0)
        self.a0b = a0b
        self.alpha = fq(self.a0 - rho)            # Re z >= alpha on the square
        if scaled:
            assert self.alpha > arb("0.3")
        else:
            assert self.alpha > arb("0.5")
            assert (self.a0 + rho) ** 2 + rho ** 2 <= 1   # |z| <= 1 on the square
        self.N = N
        # enclosures of m_n(z) on the square S = a0 + [-rho, rho] + i[-rho, rho]
        S = acb(a0b + arb(0, fq(rho)), arb(0, fq(rho)))
        mS = [acb(1), acb(1)]
        Y = 2 * S - 1
        for n in range(2, N + 1):
            if scaled and n == 2:
                mS.append(S)
                continue
            s = acb(0)
            if n % 2:
                for j in range(1, (n + 1) // 2):
                    s += mS[j] * mS[n - j]
                s = s * (1 + S)
            else:
                for j in range(1, n // 2):
                    if j % 2:
                        s += (S * Y if scaled else S) * mS[j] * mS[n - j]
                    else:
                        s += mS[j] * mS[n - j]
                hh = n // 2
                s = 2 * s + ((S * Y if scaled else S) if hh % 2 else 1) * mS[hh] ** 2
            mS.append(s / (n * S - (S if n % 2 else 1)))
        if scaled:
            gS = (2 * S).gamma()
            self.cS = [(mS[n] * gS ** (n // 2) * (1 + n * S).rgamma()).abs_upper()
                       for n in range(N + 1)]
            Gm = gS.abs_upper()
            Gm = Gm if Gm > 1 else arb(1)
            zmax = (acb(fq(self.a0 + rho), fq(rho))).abs_upper()
            ymax = (acb(fq(2 * (self.a0 + rho) - 1), fq(2 * rho))).abs_upper()
            ymax2 = (acb(fq(2 * (self.a0 - rho) - 1), fq(2 * rho))).abs_upper()
            ymax = ymax if ymax > ymax2 else ymax2
            kappa = (zmax if zmax > 1 else arb(1)) * (ymax if ymax > 1 else arb(1))
        else:
            Gm = arb(1)
            kappa = arb(1)
        if not scaled:
            self.cS = [(mS[n] * (1 + n * S).rgamma()).abs_upper() for n in range(N + 1)]
        # complex Lemma 1 on S (Lemma 6 in 02_report.md)
        al = self.alpha
        A = ((N + 1) * al - 1) / (N * kappa)
        assert A > 0
        B = arb(0)
        for j in range(1, N + 1):
            bj = (mS[j].abs_upper() / A) ** (arb(1) / j)
            B = bj.upper() if bj.upper() > B else B
        B = (B * (1 + arb(2) ** -30)).upper()
        for j in range(1, N + 1):
            assert mS[j].abs_upper() <= A * B ** j
        r2 = fq(rho) ** 2
        self.At = (A * (r2 / (2 * al * al)).exp()).upper()
        self.Bt = (B * Gm.sqrt() * (r2 / (2 * al)).exp()).upper()
        # factor for the odd part: sqrt((2a-1) Gamma(2a)) over real a in I (scaled)
        if scaled:
            aI = fq(self.a0 - self.w).union(fq(self.a0 + self.w))
            s2 = (2 * aI - 1) * (2 * aI).gamma()
            f = s2.nonnegative_part().upper().sqrt().upper()
            self.fodd = f
            # disc version, for the Cauchy remainders of the odd part
            self.fmax = f if f > 1 else arb(1)
        else:
            self.fodd = arb(1)
            self.fmax = arb(1)
        self.Pabs = arb_poly([self.cS[n] for n in range(N + 1)])
        self.K = K
        self.target_log = target_log
        self.Kmax = Kmax

    def tailS(self, t, k=0):
        """Bound for |d^k/dt^k sum_{n>N} c_n(z) (i t)^n|, uniformly for z in S."""
        N, al = self.N, self.alpha
        t = arb(t)
        n = N + 1
        u = self.At * self.Bt ** n * arb(n) ** k * t ** (n - k) / (1 + al * n).gamma()
        r = self.Bt * t * (1 + arb(1) / n) ** k * (1 + al * n).gamma() / (1 + al * n + al).gamma()
        if not (r < 1):
            raise ValueError("tail ratio not < 1; increase N")
        return (self.fmax * u / (1 - r)).upper()

    def choose_K(self, Msup):
        if self.K is not None:
            return self.K
        lm = float(Msup.log().upper()) if Msup > 0 else 0.0
        lq = -float(fq(self.q).log().mid())
        K = int((lm - self.target_log) / lq) + 2
        return max(4, min(K, self.Kmax))

    def build_series(self, K):
        ctx.cap = K + 1
        self.Kser = K
        eps = arb_series([arb(0), arb(1)])
        z = self.a0b + eps
        one = arb_series([arb(1)])
        m = [one, one]
        y = 2 * z - 1
        g2 = (2 * z).gamma() if self.scaled else None
        for n in range(2, self.N + 1):
            if self.scaled and n == 2:
                m.append(z)
                continue
            s = arb_series([arb(0)])
            if n % 2:
                for j in range(1, (n + 1) // 2):
                    s += m[j] * m[n - j]
                s = s * (1 + z)
                d = n * z - z
            else:
                zz = z * y if self.scaled else z
                for j in range(1, n // 2):
                    s += (zz * (m[j] * m[n - j])) if j % 2 else m[j] * m[n - j]
                h = n // 2
                s = 2 * s + ((zz * m[h] * m[h]) if h % 2 else m[h] * m[h])
                d = n * z - 1
            m.append(s / d)
        if self.scaled:
            gp = [arb_series([arb(1)])]
            for k in range(1, self.N // 2 + 1):
                gp.append(gp[-1] * g2)
        self.ccoef = []
        for n in range(self.N + 1):
            if self.scaled:
                cf = (m[n] * gp[n // 2] * (1 + n * z).rgamma()).coeffs()
            else:
                cf = (m[n] * (1 + n * z).rgamma()).coeffs()
            cf = cf + [arb(0)] * (K + 1 - len(cf))
            self.ccoef.append(cf)

    def certify(self, T2, h, beta=4, Kt=12):
        T2 = fq(T2)
        h = fq(h)
        beta = arb(beta)
        q = fq(self.q)
        w = fq(self.w)
        a_lo, a_hi = fq(self.a0 - self.w), fq(self.a0 + self.w)
        aI = a_lo.union(a_hi)
        T3 = (arb(2) ** a_hi * T2).upper()
        MF = arb(0)
        for n in range(0, self.N + 1, 2):
            MF += self.cS[n] * T3 ** (n + 3) / (n + 3)
        K = self.choose_K(MF)
        self.build_series(K)
        qfac = q ** (K + 1) / (1 - q)
        # Taylor coefficients of F^N(a0 + eps) = int_0^T3 t^2 Re P_N(t) dt
        Fc = []
        for i in range(K + 1):
            s = arb(0)
            for n in range(0, self.N + 1, 2):
                term = self.ccoef[n][i] * T3 ** (n + 3) / (n + 3)
                s += term if n % 4 == 0 else -term
            Fc.append(s)
        remF = (MF * qfac).upper()
        truncF = (T3 ** 3 / 3 * self.tailS(T3, 0)).upper()
        # cells: sup over a in I of |phi_a(t)|
        n2 = int((T2 / (2 * h)).mid().floor().unique_fmpz())
        assert (2 * h * n2 - T2).is_zero()
        ncells = int((T3 / (2 * h)).upper().ceil().unique_fmpz()) + 1
        centers = [(2 * j + 1) * h for j in range(ncells)]
        vals = [[arb(0)] * ncells for _ in range(Kt)]
        for i in range(K + 1):
            re = [arb(0)] * (self.N + 1)
            im = [arb(0)] * (self.N + 1)
            for n in range(self.N + 1):
                c = self.ccoef[n][i]
                if n % 2 == 0:
                    re[n] = c if n % 4 == 0 else -c
                else:
                    im[n] = c if n % 4 == 1 else -c
            pr, pim = arb_poly(re), arb_poly(im)
            wi = w ** i
            for k in range(Kt):
                for jc, tc in enumerate(centers):
                    vr, vi = pr(tc), pim(tc)
                    vi = vi * self.fodd
                    vals[k][jc] += wi * (vr * vr + vi * vi).sqrt()
                pr, pim = pr.derivative(), pim.derivative()
        pa = [self.Pabs]
        for k in range(1, Kt):
            pa.append(pa[-1].derivative())
        fac = [arb.fac_ui(k) for k in range(Kt)]
        remKt = self.cS[Kt] * h ** Kt
        cells = []
        for jc, tc in enumerate(centers):
            tot = remKt
            for k in range(Kt):
                bk = vals[k][jc] + self.fmax * pa[k](tc) * qfac + self.tailS(tc, k)
                tot += bk * h ** k / fac[k]
            s = tot.upper()
            if s > 1:
                s = arb(1)
            cells.append((2 * jc * h, 2 * (jc + 1) * h, s))
        # Lemma 4 with T3 >= 2^a T2 for every a in I
        ia = 1 / aI
        Qn = arb(0)
        for (l, r, s) in cells[:n2]:
            wgt = (1 - (r / T2) ** ia / 2) ** (-aI * beta)
            Qn += s * wgt * (r ** ia - (l ** ia if not l.is_zero() else arb(0)))
        Qn = Qn / T2 ** ia
        C = arb(0)
        for (l, r, s) in cells[n2:]:
            v = (s * r ** beta).upper()
            C = v if v > C else C
        R = Qn + arb(2) ** (aI * beta) * C * T2 ** (-beta) / (aI * beta - 1)
        boot = bool(R.upper() < 1) and bool(aI * beta > 1) and bool(beta > 3)
        E = (C * T3 ** (3 - beta) / (beta - 3)).upper()
        pi_ = arb.pi()
        G = [-(c / pi_) for c in Fc]
        eta = ((remF + truncF + E) / pi_).upper()
        return dict(G=G, eta=eta, boot=boot, R=R, C=C, E=E, remF=remF, truncF=truncF,
                    K=K, T3=T3, MF=MF, ncells=ncells, Bt=self.Bt)


def eval_G(G, eps):
    """Enclosure of sum G_i eps^i for an arb ball eps (Horner)."""
    s = arb(0)
    for c in reversed(G):
        s = s * eps + c
    return s


def sign_cover(G, eta, a0, w, max_depth=60):
    """Split [a0-w, a0+w] into pieces on which G(a-a0) +- eta has one sign.
    Returns merged (lo, hi, sign) with sign in {-1, +1, 0}; 0 marks pieces
    left undecided at the depth limit.  lo, hi are Fractions."""
    out = []
    a0 = Fraction(a0)
    stack = [(a0 - Fraction(w), a0 + Fraction(w), 0)]
    while stack:
        lo, hi, d = stack.pop()
        e = fq(lo - a0).union(fq(hi - a0))
        v = eval_G(G, e)
        if (v + eta) < 0:
            out.append((lo, hi, -1))
        elif (v - eta) > 0:
            out.append((lo, hi, 1))
        elif d >= max_depth or (abs(v.mid()) <= eta and v.rad() <= eta):
            # undecided and splitting cannot help (or depth limit): stop here
            out.append((lo, hi, 0))
        else:
            mid = (lo + hi) / 2
            stack.append((mid, hi, d + 1))
            stack.append((lo, mid, d + 1))
    out.sort()
    merged = []
    for p in out:
        if merged and merged[-1][2] == p[2] and merged[-1][1] == p[0]:
            merged[-1] = (merged[-1][0], p[1], p[2])
        else:
            merged.append(p)
    return merged
