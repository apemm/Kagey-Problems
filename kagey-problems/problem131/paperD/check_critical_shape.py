"""Independent pointwise checks of the threshold endpoints and the critical slope.

Uses the real-parameter moment recursion in threshold_pointwise, without the
parameter Taylor models used to obtain the original threshold bracket. Arb
transcendental arithmetic remains part of the trusted base. This checks the
bracket, not the global uniqueness proof.
"""
from pathlib import Path
import argparse
import hashlib
import json
import platform
import time
import flint
from flint import arb
from threshold_pointwise import ERW, ball, require

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).parent/'data/critical_shape_check.json')
    parser.add_argument('--moments',type=int,default=1800)
    parser.add_argument('--precision',type=int,default=2000)
    args=parser.parse_args()
    started=time.monotonic()
    records=[]
    for value, expected in [('1838418790980431/2748779069440000',-1),('45960469774511/68719476736000',1)]:
        print('Checking endpoint',value,flush=True)
        e=ERW(value,N=args.moments,prec=args.precision,K=40)
        c=e.certify('11','1/64',beta=8)
        require(c['boot'],'Fourier tail bootstrap failed')
        require(c['sign']==expected,'Threshold endpoint sign failed')
        print('PASS',c['fpp'],flush=True)
        records.append({k:str(v) for k,v in c.items()})
    print('Checking conditional derivative at zero',flush=True)
    e=ERW('0.66881286',N=1200,prec=args.precision,K=40)
    c=e.certify('6','1/64',beta=8)
    require(c['boot'],'Conditional derivative tail bootstrap failed')
    T=arb(10)
    require(c['T3']<T,'Tail must start before ten')
    integral=sum(((1 if n%4==1 else -1)*e.c[n]*T**(n+2)/(n+2)
                  for n in range(1,e.N+1,2)),arb(0))
    error=e.tail(T)*T**2/2+c['C']*T**(-6)/6
    point=integral/arb.pi()+arb(0,(error/arb.pi()).upper())
    # The differentiated-smoothing certificate bounds |d_a phi| by four
    # below ten and by 4 t^-7 above it. Thus |d_a h_a'(0)| < 64.
    slope_bound=(arb(200)+arb(4)/(5*T**5))/arb.pi()
    require(slope_bound<64,'Parameter variation bound failed')
    critical=point+arb(0,ball('0.00000064'))
    require(critical>ball('0.097074') and critical<ball('0.097076'),
            'Claimed critical-slope enclosure not proved')
    print('PASS conditional slope at critical memory',critical,flush=True)
    result={'all_checks_passed':True,'endpoint_checks':records,
            'conditional_slope_point':str(point),'conditional_slope_at_threshold':str(critical),
            'parameter_variation_bound':'64','parameter_half_width':'1/100000000',
            'conditional_slope_dependency':'transition_derivative_certificate.json and the written differentiated-smoothing proof',
            'endpoint_method':'pointwise real moments and Fourier bootstrap, independent of threshold_taylor.py',
            'precision_bits':args.precision,'endpoint_moments':args.moments,
            'python':platform.python_version(),'python_flint':flint.__version__,
            'elapsed_seconds':time.monotonic()-started,
            'sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
                      [Path(__file__),Path(__file__).with_name('threshold_pointwise.py'),
                       Path(__file__).parent/'data/transition_derivative_certificate.json']}}
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('ALL CHECKS PASSED',args.output,flush=True)

if __name__=='__main__':
    main()
