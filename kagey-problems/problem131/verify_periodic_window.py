"""Independent cyclic enumeration and numerical crossing-window checks.

Only the standard library is required. The Decimal computations are numerical,
not interval arithmetic. Run with python -B.
"""
from decimal import Decimal as D, localcontext
from itertools import product
from math import comb
from pathlib import Path
import json

from verify_allbin import bessel, ratio as free_ratio, root


def periodic_ratio(a, b, x):
    """Cyclic polynomial evaluated at u=x/sqrt(ab), using positive terms."""
    u = x / D(a * b).sqrt()
    term = D(1)
    total = D(0)
    for r in range(min(a, b)):
        add = D(a + b) * u * u * term / (r + 1)
        total += add
        multiplier = D((a - 1 - r) * (b - 1 - r)) * u * u / (r + 1) ** 2
        if multiplier == 0:
            break
        if r > 4 and multiplier < D('0.5') and add < total * D('1e-65'):
            break
        term *= multiplier
    return total


def periodic_bessel(a, b, x):
    _, i1 = bessel(x)
    return D(a + b) * x / D(a * b) * i1


def count_above(n, u, law):
    """Count all bins above endpoints by the proved strict inward ordering."""
    def value(k):
        return law(k, n-k, u * D(k * (n-k)).sqrt())
    mid = n // 2
    if value(mid) <= 1:
        return 0
    lo, hi = 1, mid
    while lo < hi:
        k = (lo + hi) // 2
        if value(k) > 1:
            hi = k
        else:
            lo = k + 1
    return n - 2 * lo + 1


def run():
    result = {'arithmetic': 'Exact integers and Decimal precision 80; not interval arithmetic'}
    count = 0
    for n in range(2, 13):
        actual = [[0] * (n+1) for _ in range(n+1)]
        for word in product((0, 1), repeat=n):
            k = sum(word)
            changes = sum(word[i] != word[(i+1) % n] for i in range(n))
            actual[k][changes] += 1
        for a in range(1, n):
            b = n-a
            expected = [0] * (n+1)
            for r in range(1, min(a,b)+1):
                numerator = n * comb(a-1,r-1) * comb(b-1,r-1)
                assert numerator % r == 0
                expected[2*r] = numerator // r
            assert actual[a] == expected, (n,a)
            count += 1
    result['cyclic_polynomials_checked_against_enumeration'] = count
    count = 0
    for a in [1,2,3,10,100,10**6]:
        for b in sorted({a,a+1,10*a,10**12}):
            for x in map(D,['0.1','0.5','1','4','10']):
                actual, approx = periodic_ratio(a,b,x), periodic_bessel(a,b,x)
                delta = 1-actual/approx
                bound = D(a+b)*x*x/(2*a*b)
                assert -D('1e-60') <= delta <= bound+D('1e-60'), (a,b,x,delta,bound)
                count += 1
    result['periodic_uniform_bound_checks'] = count
    samples, profiles = [], []
    log2 = D(2).ln()
    pi = D('3.141592653589793238462643383279502884197169399375105820974944592307816406286')
    cp = (pi/2).ln()/2
    for n in [100,101,1000,1001,10**4,10**6,10**8,10**12]:
        a,b = n//2,(n+1)//2
        scale = D(a*b).sqrt()
        xf = root(lambda x: free_ratio(a,b,x))
        xp = root(lambda x: periodic_ratio(a,b,x))
        uf,up = xf/scale,xp/scale
        assert up > uf
        L = D(n).ln()
        zp = D(n)*up
        prediction = L-L.ln()/2+cp+(L.ln()/4-cp/2+D(3)/8)/L
        diff_prediction = log2+(D(1)/4-log2/2)/L
        samples.append({'N':n,'N_u_periodic':str(zp),
                        'periodic_refined_residual':str(zp-prediction),
                        'N_times_periodic_minus_free_u':str(D(n)*(up-uf)),
                        'difference_refined_residual':str(D(n)*(up-uf)-diff_prediction)})
        if n < 1000:
            continue
        for name,law,uc in [('free',free_ratio,uf),('periodic',periodic_ratio,up)]:
            for t in map(D,['-1','1','2']):
                u = uc+t/n
                values = []
                for y in map(D,['0','0.25','0.5','1']):
                    k = int(D(n)/2 + y*D(n)/L.sqrt())
                    # All sample points are interior once N>=1000.
                    actual = law(k,n-k,u*D(k*(n-k)).sqrt())
                    limit = (t-2*y*y).exp()
                    values.append({'y':str(y),'ratio':str(actual),
                                   'limit':str(limit),'relative_error':str(actual/limit-1)})
                m = count_above(n,u,law)
                if t < 0:
                    assert m == 0
                profiles.append({'N':n,'boundary':name,'t':str(t),
                                 'scaled_bin_count':str(L.sqrt()*m/n),
                                 'limiting_count':str((2*max(t,D(0))).sqrt()),
                                 'profile':values})
    result['root_comparison'] = samples
    result['window_samples'] = profiles
    dest = Path(__file__).with_name('data') / 'periodic-window-verification.json'
    dest.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(f'Cyclic enumeration: {result["cyclic_polynomials_checked_against_enumeration"]} polynomials.')
    print(f'Uniform periodic inequality: {count} cases.')
    print(f'Root comparisons: {len(samples)}; window samples: {len(profiles)}.')
    print(f'Data: {dest}')


if __name__ == '__main__':
    with localcontext() as ctx:
        ctx.prec = 80
        run()
