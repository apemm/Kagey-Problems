import mpmath as mp
mp.mp.dps = 30
a = mp.mpf('1.5')
Z = mp.zeta(a+1)
mu = mp.zeta(a)/Z
s = 2*mu
print('mu', mu, 's', s, 'limit C/j', 2*a*s/mu**2)
J = 1000
f = [mp.mpf(0)] + [mp.mpf(n)**(-a-1)/Z for n in range(1, J+1)]
def T(j):
    return mp.zeta(a+1, j)/Z
# renewal u, v
u = [mp.mpf(1)] + [mp.mpf(0)]*J
v = [mp.mpf(0)]*(J+1)
for j in range(1, J+1):
    u[j] = sum(f[i]*u[j-i] for i in range(1, j+1))
for j in range(1, J+1):
    v[j] = sum(u[i]*u[j-i] for i in range(0, j))
def C(j):
    return a*(j*u[j] + 2*mu*v[j] + sum(u[i] for i in range(j)))
for j in [5,10,20,40,80,160,320]:
    print('C/j', j, mp.nstr(C(j)/j, 6))
# check second form equals first
j=7
second = a*(j*u[j] + mu*v[j] + sum(u[i]*(1+mu*u[j-i]) for i in range(j)))
print('forms agree', mp.nstr(C(j)-second, 5))
for j in [40,160,640]:
    lhs = u[j]-1/mu
    rhs = j*T(j)/(mu**2*(a-1))
    print('Frenk ratio', j, mp.nstr(lhs/rhs, 5))
# table
thr = lambda N: 2*a*s/N
for N, js, iN in [(600,7,7),(1200,11,12),(2400,19,20),(4000,27,28),(8000,44,45)]:
    lead = next(j for j in range(1, 500) if T(j) < thr(N))
    ratio = N*T(js)/(2*a*s)
    # refined argmin
    vals = [(u[j] + C(j)/N, j) for j in range(0, 200)]
    ref = min(vals)[1]
    print(N, 'lead', lead, 'ratio', mp.nstr(ratio, 5), 'refined', ref)
# B_N at 5000: a(t) with t T(a(t)) -> 1 using T(x) ~ x^-a/(a Z)
N = 5000
t = N/s
B = (t/(a*Z))**(1/a)
print('B_N', B)
# golden
phi = (1+mp.sqrt(5))/2
def Calpha(al):
    K = -mp.gamma(1-al)
    return mp.pi*(K*abs(mp.cos(mp.pi*al/2)))**(1/al)/(4*(al-1)*mp.gamma(1+1/al)*mp.zeta(al)**(1+1/al))
cp = Calpha(phi)
print('C(phi)', cp, '1/C', 1/cp)
Kp = phi*mp.gamma(phi**-2)
print('K_phi check', Kp, -mp.gamma(1-phi))
bound = mp.pi*phi*(mp.sqrt(3)*phi**3/2)**(1/phi)/(4*mp.mpf('0.8856')*(phi+mp.mpf(1)/2)**phi)
print('bound', bound)
print('zeta(phi)', mp.zeta(phi), 'phi+1/2', phi+0.5, 'Gamma min', mp.gamma(mp.findroot(lambda x: mp.diff(mp.gamma,x),1.46)))
print('exponent at phi', 1-phi+1/phi)
