"""Exploratory interval computation. Not a released certificate.

It reuses the existing, reviewed real-parameter Fourier-tail bootstrap and
changes only the Fourier weight when enclosing the fourth spatial derivative.
Parameter derivatives below are finite-frequency diagnostics, not certified
derivatives of the full density.
"""
import json
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'kagey-problems/problem131/paperD'))
from flint import arb
from threshold_taylor import TaylorModel, fq, eval_G


def main():
    a0, w = Fraction('0.669'), Fraction('0.0002')
    beta = 8
    tm = TaylorModel(a0, w, q=Fraction(1, 32), N=1500, prec=1600)
    d = tm.certify(Fraction(10), Fraction(1, 32), beta=beta)
    print('bootstrap', d['boot'], 'R', d['R'], 'C', d['C'], 'T3', d['T3'], flush=True)
    if not d['boot']:
        raise RuntimeError('Tail bootstrap failed')
    eps = arb(0, fq(w))
    out = {'interval': [str(a0-w), str(a0+w)], 'beta': beta,
           'R': str(d['R']), 'C': str(d['C']), 'T3': str(d['T3'])}
    for power in (2, 4, 6):
        T, K, q = d['T3'], d['K'], fq(tm.q)
        coeff = []
        for i in range(K+1):
            coeff.append(sum(((-1 if n % 4 else 1) * tm.ccoef[n][i]
                              * T**(n+power+1)/(n+power+1)
                              for n in range(0, tm.N+1, 2)), arb(0)))
        majorant = sum((tm.cS[n]*T**(n+power+1)/(n+power+1)
                         for n in range(0, tm.N+1, 2)), arb(0))
        err = majorant*q**(K+1)/(1-q)
        err += T**(power+1)/(power+1)*tm.tailS(T)
        err += d['C']*T**(power+1-beta)/(beta-power-1)
        value = ((-1)**(power//2)/arb.pi())*eval_G(coeff, eps)
        bound = value + arb(0, (err/arb.pi()).upper())
        out['spatial_derivative_'+str(power)] = str(bound)
        print('spatial derivative', power, 'enclosure', bound, 'error', err/arb.pi(), flush=True)
        if power == 2:
            finite_deriv = eval_G([i*coeff[i] for i in range(1,K+1)], eps)/(-arb.pi())
            out['finite_frequency_parameter_derivative_ONLY'] = str(finite_deriv)
            print('finite-frequency parameter derivative ONLY', finite_deriv, flush=True)
    Path(__file__).with_name('probe_transition_output.json').write_text(json.dumps(out, indent=2)+'\n')


if __name__ == '__main__':
    main()
