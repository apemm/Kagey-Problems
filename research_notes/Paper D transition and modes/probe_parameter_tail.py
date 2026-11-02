"""Research prototype for a differentiated-smoothing tail certificate.

This is not part of the released certificate. Mathematical constants and
the differentiated fixed-point identity are derived in transition.md.
All finite computations below use Arb balls; floats are progress displays.
"""
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'kagey-problems/problem131/paperD'))
from flint import arb, arb_poly
from threshold_taylor import TaylorModel, fq, eval_G


def maximum(values):
    out = arb(0)
    for v in values:
        u = v.upper()
        if u > out:
            out = u
    return out


def derivative_cells(tm, T3, h, da, dt, Kt=48):
    """Enclose |partial_a^da partial_t^dt phi| on real parameter and t cells.

    da is 0 or 1. Both the a remainder and the t remainder are bounded on
    the existing complex parameter square. No derivative of a real tail
    error is taken.
    """
    K, N = tm.Kser, tm.N
    w, q, rho = fq(tm.w), fq(tm.q), fq(tm.rho)
    ncell = int((T3/(2*h)).upper().ceil().unique_fmpz())+1
    centers = [(2*j+1)*h for j in range(ncell)]
    vals = [[arb(0)]*ncell for _ in range(Kt)]
    for i in range(da, K+1):
        weight = (i*w**(i-1)) if da else w**i
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
        for k in range(Kt):
            for j, tc in enumerate(centers):
                vr, vi = pr(tc), pi(tc)
                vals[k][j] += weight*(vr*vr+vi*vi).sqrt()
            pr, pi = pr.derivative(), pi.derivative()
        print('cell coefficients', da, dt, i, '/', K, flush=True)
    pa = [tm.Pabs]
    for _ in range(Kt+dt):
        pa.append(pa[-1].derivative())
    # Exact derivative of sum_{i>K} q^i, with Cauchy's coefficient bound.
    qfac = q**K*((K+1)-K*q)/(rho*(1-q)**2) if da else q**(K+1)/(1-q)
    cauchy = 1/(rho-w) if da else arb(1)
    tmax = 2*ncell*h
    rem = cauchy*(pa[Kt+dt](tmax)+tm.tailS(tmax, Kt+dt))*h**Kt/arb.fac_ui(Kt)
    print('global t remainder', da, dt, rem, flush=True)
    cells = []
    for j, tc in enumerate(centers):
        tot = rem
        for k in range(Kt):
            err = pa[k+dt](tc)*qfac+cauchy*tm.tailS(tc, k+dt)
            tot += (vals[k][j]+err)*h**k/arb.fac_ui(k)
        cells.append((2*j*h, 2*(j+1)*h, tot.upper()))
    return cells


def main():
    start = time.monotonic()
    tm = TaylorModel(Fraction('0.66881286'), Fraction('0.00000001'),
                     q=Fraction(1, 10000), N=900, prec=1300)
    T2, h, beta, gamma = arb(6), fq(Fraction(1,32)), 8, 7
    d = tm.certify(Fraction(6), Fraction(1,32), beta=beta)
    if not d['boot']:
        raise RuntimeError('Base characteristic-function bootstrap failed: '+str(d['R']))
    print('base', {k:str(d[k]) for k in ('C','R','T3','K')}, flush=True)
    C, R, T3 = d['C'], d['R'].upper(), d['T3']
    a = fq(tm.a0-tm.w).union(fq(tm.a0+tm.w))
    M = (2*tm.cS[2]).sqrt().upper()
    ucells = derivative_cells(tm,T3,h,da=0,dt=1)
    D1init = maximum(s*r**beta for l,r,s in ucells if r>=T2)
    A1 = M*C*arb(2)**(a*(beta-1))/(a+1)
    D1 = 2*maximum([D1init,A1/(1-R)])
    print('t derivative tail D1',D1,'init',D1init,'forcing',A1,flush=True)
    vcells = derivative_cells(tm,T3,h,da=1,dt=0)
    Mp = maximum(s for l,r,s in vcells if l<T2)
    Dpinit = maximum(s*r**gamma for l,r,s in vcells if r>=T2)
    factor = 2*C*arb(2)**(a*beta)*T3**(gamma-beta-1/a)
    kappa0 = factor*T2**(1/a-gamma)/(a*gamma-1)
    kappa = (R+kappa0).upper()
    if not kappa < 1:
        raise RuntimeError('Parameter linear contraction failed: '+str(kappa))
    force_small = factor*Mp*T2**(1/a)
    log2 = arb(2).log()
    force_chain = M*C*arb(2)**(a*(beta-1))*(log2/(a+1)+1/(a+1)**2)
    force_chain += D1*log2*R
    force_mix = C*R/T3
    force = force_small+force_chain+force_mix
    Dp = 2*maximum([Dpinit,force/(1-kappa)])
    print('a derivative tail Dp',Dp,'Mp',Mp,'init',Dpinit,'kappa',kappa,'forcing',force,flush=True)
    K, q, rho, w = d['K'],fq(tm.q),fq(tm.rho),fq(tm.w)
    fc=[]
    for i in range(K+1):
        fc.append(sum(((-1 if n%4 else 1)*tm.ccoef[n][i]*T3**(n+3)/(n+3)
                       for n in range(0,tm.N+1,2)),arb(0)))
    finite = -eval_G([i*fc[i] for i in range(1,K+1)],arb(0,w))/arb.pi()
    mf = sum((tm.cS[n]*T3**(n+3)/(n+3) for n in range(0,tm.N+1,2)),arb(0))
    err_a = mf*q**K*((K+1)-K*q)/(rho*(1-q)**2)
    err_series = T3**3/3*tm.tailS(T3)/(rho-w)
    err_tail = Dp*T3**(3-gamma)/(gamma-3)
    error = (err_a+err_series+err_tail)/arb.pi()
    value = finite+arb(0,error.upper())
    print('PARAMETER DERIVATIVE ENCLOSURE', value, 'tail error',err_tail/arb.pi(),flush=True)
    out={k:str(v) for k,v in dict(a=a,C=C,R=R,T3=T3,M=M,D1=D1,Mp=Mp,Dpinit=Dpinit,
         kappa=kappa,Dp=Dp,finite_frequency_derivative=finite,parameter_derivative=value,
         parameter_tail_error=err_tail/arb.pi(),elapsed=time.monotonic()-start).items()}
    Path(__file__).with_name('probe_parameter_tail_output.json').write_text(json.dumps(out,indent=2)+'\n')


if __name__=='__main__':
    main()
