"""Fourier illustrations of the limit density and its bias boundary.

These are numerical illustrations, not certificates. Characteristic functions
are evaluated with Arb moments before conversion to doubles for Simpson
quadrature. A doubled frequency grid checks discretization. The critical
parameter comes from the separate certified enclosure.
"""
from pathlib import Path
import json
import sys
import time
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from scipy.optimize import minimize_scalar
from scipy.integrate import simpson
from scipy.special import gammaln

P=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(P))
from threshold_pointwise import ERW, arb

ASTAR=0.6688128600145994
OUT=Path(__file__).parent
CACHE=P/'data/limit_phase_illustration.npz'

def cf_grid(a):
    # The decay slows near memory one. The last grid sample is checked below.
    T=16 if a<0.73 else (32 if a<0.84 else 64)
    e=ERW(str(a),N=1600,prec=2000,K=24)
    while abs(complex(float(e.Pre(arb(T)).mid()),float(e.Pim(arb(T)).mid())))>=1e-11:
        T*=2
        if T>256: raise RuntimeError('No resolved frequency cutoff')
    t=np.linspace(0,T,2049)
    z=np.empty(t.size,dtype=complex)
    worst=0.
    for j,v in enumerate(t):
        av=arb(float(v))
        re,im=e.Pre(av),e.Pim(av)
        z[j]=complex(float(re.mid()),float(im.mid()))
        worst=max(worst,float(re.rad()),float(im.rad()))
    trunc=float(e.tail(arb(T)))
    if not (worst<1e-13 and trunc<1e-13 and abs(z[-1])<1e-11):
        raise RuntimeError(f'Unresolved Fourier grid at a={a}: {worst}, {trunc}, {abs(z[-1])}')
    return t,z,{'a':a,'T':T,'evaluation_radius':worst,'series_tail_bound':trunc,'last_cf_modulus':abs(z[-1])}

def densities(t,z,u,stride=1):
    t,z=t[::stride],z[::stride]
    theta=np.outer(u,t)
    return simpson(np.cos(theta)*z.real+np.sin(theta)*z.imag,x=t,axis=1)/np.pi

def slope(t,z,u):
    return simpson(t*(z.imag*np.cos(t*u)-z.real*np.sin(t*u)),x=t)/np.pi

def boundary(t,z):
    u=np.linspace(0,2.8,701)
    theta=np.outer(u,t)
    positive=simpson(t*(z.imag*np.cos(theta)-z.real*np.sin(theta)),x=t,axis=1)/np.pi
    negative=simpson(t*(z.imag*np.cos(theta)+z.real*np.sin(theta)),x=t,axis=1)/np.pi
    ok=(positive>1e-8)&(negative>=-1e-9)&(positive+negative>1e-7)
    values=np.full(u.size,.5)
    values[ok]=negative[ok]/(positive[ok]+negative[ok])
    j=int(np.argmin(values))
    if values[j]>=.5: return .5
    def ratio(v):
        pos,neg=slope(t,z,v),slope(t,z,-v)
        return neg/(pos+neg) if pos>0 and pos+neg>1e-7 else .5
    result=minimize_scalar(ratio,bounds=(u[max(0,j-2)],u[min(len(u)-1,j+2)]),method='bounded',options={'xatol':1e-11})
    return float(np.clip(result.fun,0,.5))

def compute():
    start=time.monotonic()
    avals=np.unique(np.r_[.62,.64,.66,ASTAR,np.linspace(.675,.9,19)])
    u=np.linspace(-3.4,3.4,1001)
    bounds=[]; audit=[]; curves=[]
    selected=[.64,ASTAR,.72]
    for a in np.unique(np.r_[avals,selected]):
        print('Limit-density grid',a,flush=True)
        checkpoint=OUT/'phase_work'
        checkpoint.mkdir(exist_ok=True)
        name=checkpoint/f'{a:.16f}.npz'
        if name.exists():
            saved=np.load(name)
            t,z=saved['t'],saved['z']
            record=json.loads(str(saved['record']))
        else:
            t,z,record=cf_grid(float(a))
            np.savez(name,t=t,z=z,record=json.dumps(record))
        b=boundary(t,z)
        b_coarse=boundary(t[::2],z[::2])
        if a<=ASTAR: b=b_coarse=.5
        record.update(b=b,b_coarse=b_coarse,b_grid_difference=abs(b-b_coarse))
        if abs(b-b_coarse)>2e-5: raise RuntimeError('Unstable bias boundary')
        if a in avals: bounds.append((a,b))
        if a in selected:
            density=(densities(t,z,u)+densities(t,z,-u))/2
            coarse=(densities(t,z,u,2)+densities(t,z,-u,2))/2
            record['density_grid_difference']=float(np.max(np.abs(density-coarse)))
            if record['density_grid_difference']>2e-6: raise RuntimeError('Unstable density plot')
            curves.append((a,density))
        audit.append(record)
    bounds=np.array(bounds)
    np.savez(CACHE,a=bounds[:,0],b=bounds[:,1],u=u,curve_a=np.array([c[0] for c in curves]),density=np.array([c[1] for c in curves]))
    (P/'data/limit_phase_illustration.json').write_text(json.dumps({'scope':'illustration, not a certificate','quadrature':'composite Simpson, 2049 and 1025 frequencies','precision_bits':2000,'moments':1600,'runs':audit,'elapsed_seconds':time.monotonic()-start},indent=2)+'\n')

def draw():
    d=np.load(CACHE)
    plt.rcParams.update({'font.family':'serif','font.size':9,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
    fig=plt.figure(figsize=(6.3,5.0),layout='constrained')
    gs=fig.add_gridspec(2,3,height_ratios=[1.25,1])
    ax=fig.add_subplot(gs[0,:2])
    a,b=d['a'],d['b']
    ax.fill_between(a,b,1-b,color='#76b8c5',alpha=.65)
    ax.plot(a,b,color='#00566b',lw=1.5); ax.plot(a,1-b,color='#00566b',lw=1.5)
    ax.axvline(ASTAR,color='.3',ls=':',lw=1)
    ax.plot([ASTAR],[.5],'o',color='#ae4a27',ms=4)
    ax.text(.805,.51,'two modes',ha='center')
    ax.text(.73,.96,'one mode',ha='center',va='top')
    ax.text(.73,.04,'one mode',ha='center',va='bottom')
    ax.annotate(r'$a_*$',(ASTAR,.5),xytext=(ASTAR-.025,.65),arrowprops={'arrowstyle':'-','lw':.7})
    ax.set(xlabel=r'memory $a$',ylabel=r'initial bias $q$',xlim=(.62,.9),ylim=(0,1),title='Numerical boundary')
    # Plot the explicit theorem's inner region, without solving for b_a.
    ax=fig.add_subplot(gs[0,2])
    a1=np.linspace(.96,.99999,600)
    rho=np.expm1(2*gammaln(1+a1)-np.log(2*a1-1)-gammaln(2*a1))
    ok=rho<1/12
    a1,rho=a1[ok],rho[ok]
    bound=4*rho/(1-4*rho)
    ax.fill_between(a1,bound,1-bound,color='#afd0b0',alpha=.8,hatch='///',edgecolor='#397849',linewidth=0)
    ax.plot(a1,bound,color='#397849',lw=1.2)
    ax.plot(a1,1-bound,color='#397849',lw=1.2)
    ax.text(.985,.5,'two modes',ha='center',fontsize=8)
    ax.set(xlabel=r'memory $a$',xlim=(.96,1),ylim=(0,1),title='Proved inner region',xticks=[.96,.98,1])
    titles=['below the transition','at the transition','above the transition']
    for k,(a,y,title) in enumerate(zip(d['curve_a'],d['density'],titles)):
        ax=fig.add_subplot(gs[1,k]); ax.plot(d['u'],y,color='#00566b',lw=1.5)
        ax.axvline(0,color='.65',ls=':',lw=.7)
        ax.set(xlim=(-3.4,3.4),ylim=(0,None),xlabel=r'$u$',title=title+'\n'+(r'$a=a_*$' if k==1 else rf'$a={a:.2f}$'))
        if k==0: ax.set_ylabel(r'fair density $g_a(u)$')
    fig.savefig(OUT/'phase.pdf')
    fig.savefig(OUT/'phase.png',dpi=180)
    print('Wrote',OUT/'phase.pdf',flush=True)

if __name__=='__main__':
    if '--rebuild' in sys.argv or not CACHE.exists(): compute()
    draw()
