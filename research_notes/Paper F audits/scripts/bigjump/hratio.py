import mpmath as mp
mp.mp.dps = 30
al = mp.mpf('1.5'); p = mp.mpf('0.5')
Ka = -mp.gamma(1-al)
def cf(t):
    # W = (1-p) Z+ - p Z-, theta=1 both, equal laws
    return mp.exp(Ka*((1-p)**al)*(-1j*t)**al + Ka*(p**al)*(1j*t)**al)
def h(x):
    f = lambda t: mp.re(mp.exp(-1j*t*x)*cf(t))
    return mp.quadosc(f, [0, mp.inf], omega=x)/mp.pi if x>0 else mp.quad(f,[0,mp.inf])/mp.pi
# sanity: total mass via tail check & h symmetric
for K in [1,2,4,8,16,32,64]:
    lead = al*(1-p)**al*mp.mpf(K)**(-al-1)
    print(K, mp.nstr(h(K),10), mp.nstr(h(K)/lead,6))
# check normalization of the tail of Z+: P(Z>x) ~ x^-alpha
def g(x):
    f = lambda t: mp.re(mp.exp(-1j*t*x)*mp.exp(Ka*(-1j*t)**al))
    return mp.quadosc(f,[0,mp.inf],omega=x)/mp.pi
for x in [50,200]:
    print('g tail ratio', x, mp.nstr(g(x)/(al*x**(-al-1)),8))
