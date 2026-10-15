"""Couplings and correlation lengths at the central crossings (Corollary 5.4, Table 3).

For each N the free and periodic central crossings are found from the exact run
polynomials (ratio of verify_allbin.py and periodic_ratio of
verify_periodic_window.py). The script prints the couplings J = -(1/2) log u, the
main terms of (eq:isingtemperature) and of its free analogue, the approximation
(2 log N - 1)/5 of Stepanyan et al. (their Eq. (16)) and their fitted line
0.3864 log N - 0.21055 (their Fig. 1(b)), the boundary shift J^F - J^P against
log 2/(2 log N), the values of N/xi at both crossings against
2 log N - log log N + 2c, and the secant slopes of the exact periodic J against
log N.

Only the standard library is required. Decimal precision 80 (numerical, not
interval arithmetic). Run with python -B in this folder. Run time is a few
seconds.
"""
from decimal import Decimal as D, localcontext
from pathlib import Path
import json

from verify_allbin import ratio as free_ratio, root
from verify_periodic_window import periodic_ratio

PI = D('3.14159265358979323846264338327950288419716939937510582097494459230781640628620899863')
NS = [10, 20, 50, 100, 1000, 10**4, 10**5, 10**6]
SECANTS = [(10, 100), (100, 1000), (10**4, 10**5)]


def central_odds(n, law):
    """Odds u at the central crossing: the root of S_{N,m_N}(u) = 1."""
    a, b = n // 2, n - n // 2
    x = root(lambda x: law(a, b, x))
    return x / D(a * b).sqrt()


def coupling(u):
    return -u.ln() / 2


def n_over_xi(n, u):
    """N/xi with xi = -1/log tanh J and tanh J = (1-u)/(1+u)."""
    return -D(n) * ((1 - u) / (1 + u)).ln()


def run():
    c0 = (PI / 8).ln() / 2
    cp = (PI / 2).ln() / 2
    log2 = D(2).ln()
    rows = {}
    for n in NS:
        uf, up = central_odds(n, free_ratio), central_odds(n, periodic_ratio)
        L = D(n).ln()
        LL = L.ln()
        row = {
            'J_free': coupling(uf),
            'J_periodic': coupling(up),
            'J_free_main_terms': (L - LL) / 2 + (LL / 4 - c0 / 2) / L,
            'J_periodic_main_terms': (L - LL) / 2 + (LL / 4 - cp / 2) / L,
            'stepanyan_eq16': (2 * L - 1) / 5,
            'stepanyan_fig1b_line': D('0.3864') * L - D('0.21055'),
            'log2_over_2logN': log2 / (2 * L),
            'N_over_xi_free': n_over_xi(n, uf),
            'N_over_xi_periodic': n_over_xi(n, up),
            'N_over_xi_free_leading': 2 * L - LL + 2 * c0,
            'N_over_xi_periodic_leading': 2 * L - LL + 2 * cp,
        }
        row['shift_free_minus_periodic'] = row['J_free'] - row['J_periodic']
        rows[n] = row

    # Checks. A failed assertion stops the script with a nonzero exit code.
    for n, row in rows.items():
        assert row['J_free'] > row['J_periodic'] > 0, n
    # The two values already quoted in Section 5 and in data/quoted_values.txt.
    assert abs(rows[100]['J_periodic'] - D('1.574115')) < D('5e-7')
    assert abs(rows[10**5]['J_periodic'] - D('4.576213')) < D('5e-7')
    slopes = []
    for lo, hi in SECANTS:
        s = (rows[hi]['J_periodic'] - rows[lo]['J_periodic']) / (D(hi).ln() - D(lo).ln())
        slopes.append(s)
    assert slopes[0] < slopes[1] < slopes[2] < D('0.5'), slopes
    for n in [1000, 10**4, 10**5, 10**6]:
        row = rows[n]
        err = abs(row['J_periodic_main_terms'] - row['J_periodic'])
        assert err < abs(row['stepanyan_eq16'] - row['J_periodic']), n
        assert err < abs(row['stepanyan_fig1b_line'] - row['J_periodic']), n
    # At N = 100 the fitted line of Stepanyan et al. is closer than the main terms.
    row = rows[100]
    assert (abs(row['stepanyan_fig1b_line'] - row['J_periodic'])
            < abs(row['J_periodic_main_terms'] - row['J_periodic']))

    def fmt(x, digits=6):
        return f'{float(x):.{digits}f}'

    print('Exact couplings at the central crossings, with the main terms of')
    print('(eq:isingtemperature) and its free analogue, and Stepanyan et al.')
    head = ('N', 'J^P exact', 'J^P main', 'Eq.(16)', 'Fig.1(b)', 'J^F exact', 'J^F main',
            'J^F-J^P', 'log2/2logN')
    print(' '.join(f'{h:>10}' for h in head))
    for n, row in rows.items():
        vals = [row['J_periodic'], row['J_periodic_main_terms'], row['stepanyan_eq16'],
                row['stepanyan_fig1b_line'], row['J_free'], row['J_free_main_terms'],
                row['shift_free_minus_periodic'], row['log2_over_2logN']]
        print(f'{n:>10} ' + ' '.join(f'{fmt(v):>10}' for v in vals))
    print('\nN/xi at the crossings against 2 log N - log log N + 2c (c = c_0 free, c_P periodic)')
    for n, row in rows.items():
        print(f'{n:>10}  free {fmt(row["N_over_xi_free"], 4):>9} vs {fmt(row["N_over_xi_free_leading"], 4):>9}'
              f'   periodic {fmt(row["N_over_xi_periodic"], 4):>9} vs {fmt(row["N_over_xi_periodic_leading"], 4):>9}')
    print('\nSecant slopes of the exact periodic J against log N')
    for (lo, hi), s in zip(SECANTS, slopes):
        print(f'  {lo} to {hi}: {fmt(s, 4)}')
    print('Fig. 1(b) slope of Stepanyan et al.: 0.3864; slope of their Eq. (16): 0.4')

    out = {
        'arithmetic': 'Decimal precision 80; numerical, not interval arithmetic',
        'rows': {str(n): {k: str(v) for k, v in row.items()} for n, row in rows.items()},
        'secant_slopes_periodic': {f'{lo}-{hi}': str(s) for (lo, hi), s in zip(SECANTS, slopes)},
    }
    dest = Path(__file__).with_name('data') / 'ising-coupling-verification.json'
    dest.write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8')
    print(f'\nAll checks passed. Data: {dest}')


if __name__ == '__main__':
    with localcontext() as ctx:
        ctx.prec = 80
        run()
