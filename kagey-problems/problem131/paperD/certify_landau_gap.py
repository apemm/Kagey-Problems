"""Certify a global Landau mode gap from curvature, a finite cover and unimodality.

The analytical integral and its neglected-end bounds are described in
Appendix app:bulk-mode. Arb integration is a numerical proof input.
"""
from pathlib import Path
from fractions import Fraction
import hashlib, json, platform, time
import flint
from flint import arb, acb, ctx
from threshold_pointwise import require, ball as parse_ball

def ball(value):
    return parse_ball(str(value) if isinstance(value,Fraction) else value)

ctx.prec=160
started=time.monotonic()
delta=arb(2)**-24
T=arb(30)
lam_min=ball('-1.23')
mode=ball('-0.22278298')
mode_radius=ball('0.00000001')
kappa=ball('0.02')
checks={}

def integral(k,lam):
    require(lam>=lam_min and k in (0,1,2),'integral outside certified range')
    def fun(t,analytic):
        return (-t)**k*(-t*t.log(analytic=analytic)-acb(lam)*t).exp()*(acb.pi()*t).sin()
    small=arb.pi()*(1/arb(1).exp()-lam_min*delta).exp()*delta**(k+2)/(k+2)
    c=T.log()+lam_min
    require(c>2,'tail exponent too small')
    tail=T**2*(-c*T).exp()
    value=acb.integral(fun,acb(delta),acb(T)).real/arb.pi()
    return value+arb(0,((small+tail)/arb.pi()).upper())

# Fourier inversion gives sup |f'| <= 4/pi^3 and sup |f'''| <= 96/pi^5.
lip1=4/arb.pi()**3
lip3=96/arb.pi()**5
curvature=[]
for j in range(100):
    center=mode+ball(Fraction(-1,4)+Fraction(2*j+1,400))
    radius=ball(Fraction(1,400))+mode_radius
    upper=integral(2,center).upper()+lip3*radius
    require(upper < -2*kappa,'central curvature cover failed')
    curvature.append(str(upper))
print('PASS curvature on the quarter-unit mode neighborhood',flush=True)

fm=integral(0,mode)
cover=[]
for sign in (-1,1):
    # Closed cells cover distances [0.249,1.001] from the bracket midpoint.
    for j in range(188):
        left=Fraction(249,1000)+Fraction(j,250)
        right=left+Fraction(1,250)
        d=ball((left+right)/2)
        radius=ball(Fraction(1,500))
        lam=mode+sign*d
        upper=integral(0,lam).upper()+lip1*radius
        distance=ball(right)+mode_radius
        target=kappa*(distance**2 if distance<1 else arb(1))
        margin=fm.lower()-upper-target
        require(margin>0,'global quadratic gap cover failed')
        cover.append({'sign':sign,'left':str(left),'right':str(right),'margin':str(margin)})
    print('PASS gap cover on side',sign,flush=True)

result={'all_checks_passed':True,'kappa':'1/50','mode_bracket':['-0.22278299','-0.22278297'],
        'mode_bracket_dependency':'certify_elephant.py and the independent Lean narrow-mode certificate',
        'curvature_radius':'1/4','curvature_upper_bounds':curvature,'gap_cells':cover,
        'analytic_inputs':['real Landau integral','Fourier derivative bounds','unimodality'],
        'precision_bits':ctx.prec,'python':platform.python_version(),'python_flint':flint.__version__,
        'elapsed_seconds':time.monotonic()-started,
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}

# A sharper Fourier decay bound for the compound Poisson exponent.
# For 0 < theta <= 1/10 the existing remainder estimate gives this bound.
decay=ball('0.4')
require(arb.pi()/2-ball('0.1')*(ball('0.631')*arb(10).log()+ball('1.53'))>decay,
        'small-frequency decay bound failed')
decay_cells=[]
for j in range(305):
    lo=Fraction(1,10)+Fraction(j,100)
    hi=lo+Fraction(1,100)
    th=ball(lo).union(ball(hi))
    loss=(1-th.cos())*(2*(th/2).sin()).log()+(arb.pi()-th)*th.sin()/2
    margin=loss-decay*th
    require(margin>0,'compound Poisson decay cover failed')
    decay_cells.append({'left':str(lo),'right':str(hi),'margin':str(margin)})
require(ball(hi)>arb.pi(),'decay cover does not reach pi')
c=decay
log_constant=(arb('0.5').exp()/arb.pi())*ball('0.631')*2/c**3
constant=(arb('0.5').exp()/arb.pi())*(ball('0.631')*(6/(8*c**4)+(arb(8).log()-1)*2/c**3+1/(arb(1).exp()*c**2))+ball('1.53')*2/c**3)+4/arb.pi()**4
truncation_constant=arb('0.5').exp()*2/(arb.pi()*c)
require(constant<47 and log_constant<ball('10.4') and truncation_constant<ball('2.7'),
        'sharpened local-limit constants failed')
result['fourier_decay']={'constant':'2/5','cells':decay_cells,
                         'local_limit_constant':str(constant),'log_constant':str(log_constant),
                         'truncation_constant':str(truncation_constant)}
print('PASS Fourier decay and local-limit constants 47, 10.4, 2.7',flush=True)
result['elapsed_seconds']=time.monotonic()-started
out=Path(__file__).parent/'data/landau_gap_certificate.json'
out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('ALL CHECKS PASSED',out,flush=True)
