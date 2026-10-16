"""Domain walls at the crossing (Proposition 5.7 and Remark 5.8).

For N = 10^3, 10^4, 10^5 the script finds the free central crossing u_N from the exact run
polynomial (verify_allbin.ratio, 200 halvings at 50 digits), and computes
- the mean number of domain walls W_N(u_N) = u S_N'(u)/S_N(u) in the central bin, by a central
  difference in log u, and W_N(u_N) - z_N against 1/2 + 1/(8 z_N);
- the width 1/(2 W_N(u_N)) in the coupling;
- J_ord - J_N^F, where J_ord = -(1/2) log(2^(1/(N-1)) - 1) is the coupling at which the chain is
  fully ordered with probability 1/2, against (1/2) log(z_N/log 2).
It asserts every value quoted in Section 5 to the digits shown there, and the explicit bound of
Proposition 5.7 with delta = (log(N)/N)^(1/2).

Only the standard library is required. Run with python -B in this folder (a few seconds).
"""
from decimal import Decimal as D, getcontext
import math

from verify_allbin import ratio, root

getcontext().prec = 50

QUOTED = {  # N: (W - z_N, 1/2 + 1/(8 z_N), width, J_ord - J_F)
    10**3: ('0.5191', '0.5224', None, '1.046'),
    10**4: ('0.5166', '0.5162', '0.061', None),
    10**5: ('0.5132', '0.5126', '0.048', '1.330'),
}


def bessel_chi(w):
    """I_0(w)/(I_0(w)+I_1(w)) from the power series."""
    t0, t1 = D(1), w / 2
    i0, i1 = t0, t1
    k = 0
    while True:
        k += 1
        t0 = t0 * (w / 2) ** 2 / (k * k)
        t1 = t1 * (w / 2) ** 2 / (k * (k + 1))
        i0 += t0
        i1 += t1
        if t0 < i0 * D(10) ** -45:
            return i0 / (i0 + i1)


def main():
    for n, (q_gap, q_pred, q_width, q_ord) in QUOTED.items():
        a, b = n // 2, n - n // 2
        s = D(a * b).sqrt()
        u = root(lambda x: ratio(a, b, x)) / s
        h = D('1e-12')
        f = lambda t: ratio(a, b, s * u * t.exp()).ln()
        walls = (f(h) - f(-h)) / (2 * h)
        z = n * u / (1 + u)
        jf = -u.ln() / 2
        jord = -((D(2).ln() / (n - 1)).exp() - 1).ln() / 2
        gap, pred, width, dord = walls - z, D('0.5') + 1 / (8 * z), 1 / (2 * walls), jord - jf
        w = n * u
        chi = bessel_chi(w)
        lam = -(1 - w * (w + 2) / (2 * n)).ln()
        delta = (D(n).ln() / n).sqrt()
        bound = w * (delta.exp() - 1) + lam / delta
        assert abs(walls - w - chi) <= bound, n
        print(f'N={n}: W-z={gap:.4f} (1/2+1/(8z)={pred:.4f}), width={width:.3f}, '
              f'J_ord-J_F={dord:.3f} vs (1/2)log(z/log2)={math.log(float(z) / math.log(2)) / 2:.3f}, '
              f'|W-w-chi|={abs(walls - w - chi):.2e} <= {bound:.2e}')
        assert f'{gap:.4f}' == q_gap and f'{pred:.4f}' == q_pred, n
        if q_width:
            assert f'{width:.3f}' == q_width, n
        if q_ord:
            assert f'{dord:.3f}' == q_ord, n
    print('All checks passed.')


if __name__ == '__main__':
    main()
