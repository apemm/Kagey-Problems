"""Pointwise ball-arithmetic enclosure of f_a''(0) for the fair-start limit law L_a.

Helper of certify_threshold.py (Theorem thm:threshold, Appendix app:threshold).
It works at one exact rational a, in python-flint arb ball arithmetic.
  * Moments E[L^n] = n! m_n / Gamma(1+a n), with m_0 = m_1 = 1 and
    m_n = (n a - c_n)^(-1) sum_{j=1}^{n-1} c_j m_j m_{n-j},  c_j = 1 (j even), a (j odd)
    (Guerin, Laulin and Raschel, Theorem 1.4).
  * The bound m_n <= A B^n for all n >= 1 (Lemma lem:thr-moments).
  * phi(t) = E exp(i t L) = sum_n m_n (i t)^n / Gamma(1+a n) with the truncation
    bound of Lemma lem:thr-trunc.
  * A majorant |phi(t)| <= s(t) on [0, T3] by Taylor cells (Lemma lem:thr-cells).
  * The bootstrap of Lemma lem:thr-tail, which extends |phi(t)| <= C t^-beta to t >= T3.
  * The enclosure f''(0) = -(1/pi) [ int_0^T3 t^2 Re phi(t) dt + E ] of Lemma lem:thr-fpp,
    |E| <= C T3^(3-beta)/(beta-3), with the integral done term by term.
No certified quantity uses floating point. Floats are printed only.
Every check the certificate relies on goes through require(), which raises
ValueError, so that it also runs under python -O.
certify_threshold.py uses this module only to choose the truncation order (a float
estimate of B) and for the pointwise checks of its quick mode.
"""
from flint import arb, arb_poly, ctx, fmpq


def require(cond, msg):
    """Raise ValueError unless cond holds. Used instead of assert."""
    if not cond:
        raise ValueError(msg)


def ball(x):
    """Exact ball for a decimal string or fraction."""
    if isinstance(x, str):
        return arb(fmpq(*_dec_to_frac(x)))
    return arb(x)


def _dec_to_frac(s):
    s = s.strip()
    if "/" in s:
        p, q = s.split("/")
        return int(p), int(q)
    if "." in s:
        ip, fp = s.split(".")
        return int(ip + fp), 10 ** len(fp)
    return int(s), 1


class ERW:
    def __init__(self, a_str, N=1500, prec=1000, K=40):
        ctx.prec = prec
        self.a_str = a_str
        a = ball(a_str)
        self.a = a
        require((a > arb("0.5")) and (a < 1), "a must lie in (1/2, 1)")
        self.N, self.K = N, K
        # moments m_n, n = 0..N
        m = [arb(1), arb(1)]
        for n in range(2, N + 1):
            s = arb(0)
            for j in range(1, n):
                s += (a if j % 2 else 1) * m[j] * m[n - j]
            m.append(s / (n * a - (a if n % 2 else 1)))
        self.m = m
        self.g = [(1 + a * n).gamma() for n in range(N + 2)]
        self.c = [m[n] / self.g[n] for n in range(N + 1)]
        # Lemma lem:thr-moments(a): m_n <= A B^n for all n >= 1, A = ((N+1)a - 1)/N
        A = ((N + 1) * a - 1) / N
        B = arb(0)
        for j in range(1, N + 1):
            bj = (m[j] / A) ** (arb(1) / j)
            B = bj.upper() if bj.upper() > B else B
        B = (B * (1 + arb(2) ** -30)).upper()
        # B is a rigorous upper value: m_j <= A B^j for j <= N (checked in balls)
        for j in range(1, N + 1):
            require(m[j] <= A * B ** j, "moment bound m_j <= A B^j fails at j = %d" % j)
        self.A, self.B = A, B
        # real / imaginary polynomials of the truncated series
        re = [arb(0)] * (N + 1)
        im = [arb(0)] * (N + 1)
        for n in range(N + 1):
            if n % 2 == 0:
                re[n] = self.c[n] if n % 4 == 0 else -self.c[n]
            else:
                im[n] = self.c[n] if n % 4 == 1 else -self.c[n]
        self.Pre = arb_poly(re)
        self.Pim = arb_poly(im)

    # E[L^n] for even n (equals E|L|^n)
    def moment(self, n):
        return arb.fac_ui(n) * self.m[n] / self.g[n]

    def tail(self, t, k=0):
        """Upper bound for |d^k/dt^k sum_{n>N} c_n (i t)^n| at t > 0 (Lemma lem:thr-trunc)."""
        N, a, A, B = self.N, self.a, self.A, self.B
        t = arb(t)
        n = N + 1
        u = A * B ** n * arb(n) ** k * t ** (n - k) / (1 + a * n).gamma()
        r = B * t * (1 + arb(1) / n) ** k * (1 + a * n).gamma() / (1 + a * n + a).gamma()
        if not (r < 1):
            raise ValueError("tail ratio not < 1; increase N")
        return (u / (1 - r)).upper()

    def phi(self, t):
        t = arb(t)
        return self.Pre(t), self.Pim(t), self.tail(t)

    def cell_bounds(self, h, ncells):
        """Cells [2jh, 2(j+1)h], j < ncells; returns list of (l, r, s) with |phi| <= s."""
        K = self.K
        dre = [self.Pre]
        dim = [self.Pim]
        for k in range(1, K):
            dre.append(dre[-1].derivative())
            dim.append(dim[-1].derivative())
        h = arb(h)
        rem = self.moment(K) * h ** K / arb.fac_ui(K)
        fac = [arb.fac_ui(k) for k in range(K)]
        out = []
        for j in range(ncells):
            tc = (2 * j + 1) * h
            tot = rem
            for k in range(K):
                vr = dre[k](tc)
                vi = dim[k](tc)
                mag = (vr * vr + vi * vi).sqrt() + self.tail(tc, k)
                tot += mag * h ** k / fac[k]
            s = tot.upper()
            if s > 1:
                s = arb(1)
            out.append((2 * j * h, 2 * (j + 1) * h, s))
        return out

    def integral_t2_re(self, T):
        """int_0^T t^2 Re phi(t) dt, enclosed (term by term + truncation)."""
        T = arb(T)
        s = arb(0)
        for n in range(0, self.N + 1, 2):
            term = self.c[n] * T ** (n + 3) / (n + 3)
            s += term if n % 4 == 0 else -term
        err = self.tail(T) * T ** 3 / 3
        return s + arb(0, err)

    def certify(self, T2, h, beta=4, verbose=False):
        """Return dict with enclosure of f''(0) and the bootstrap data."""
        a = self.a
        T2 = ball(T2) if isinstance(T2, str) else arb(T2)
        h = ball(h) if isinstance(h, str) else arb(h)
        T3 = arb(2) ** a * T2
        # number of cells so that 2h*ncells >= T3 and T2 is a cell boundary
        n2 = int((T2 / (2 * h)).mid().floor().unique_fmpz())
        require((2 * h * n2 - T2).is_zero(), "T2 must be a multiple of 2h")
        ncells = int((T3 / (2 * h)).upper().ceil().unique_fmpz()) + 1
        cells = self.cell_bounds(h, ncells)
        beta = arb(beta)
        # first term of Lemma lem:thr-tail(a):
        #   (1/(a T2^(1/a))) int_0^T2 s(u) (1 - (u/T2)^(1/a)/2)^(-a beta) u^(1/a-1) du,
        # bounded cell by cell with the weight at the right end (it increases in u)
        ia = 1 / a
        Qn = arb(0)
        for (l, r, s) in cells[:n2]:
            w = (1 - (r / T2) ** ia / 2) ** (-a * beta)
            Qn += s * w * (r ** ia - (l ** ia if not l.is_zero() else arb(0)))
        Qn = Qn / T2 ** ia
        # C with s <= C t^-beta on [T2, T3]
        C = arb(0)
        for (l, r, s) in cells[n2:]:
            v = (s * r ** beta).upper()
            C = v if v > C else C
        R = Qn + arb(2) ** (a * beta) * C * T2 ** (-beta) / (a * beta - 1)
        ok_boot = bool(R < 1) and bool(a * beta > 1) and bool(beta > 3)
        I = self.integral_t2_re(T3)
        E = C * T3 ** (3 - beta) / (beta - 3)
        fpp = -(I + arb(0, E.upper())) / arb.pi()
        return dict(a=self.a_str, A=self.A, B=self.B, T2=T2, T3=T3, h=h, ncells=ncells,
                    Qn=Qn, C=C, R=R, boot=ok_boot, I=I, E=E, fpp=fpp,
                    sign=(1 if fpp > 0 else (-1 if fpp < 0 else 0)) if ok_boot else 0)
