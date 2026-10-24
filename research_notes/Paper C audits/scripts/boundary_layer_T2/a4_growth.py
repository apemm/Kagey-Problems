# (a) closed Bessel form of Phi(z)(s) for g = 2 at complex z vs the word series (Lemma L for |G| = 2)
# (b) growth of the Theorem 2(b) error for the non-reversible cycle at x = delta T
import numpy as np, mpmath as mp, itertools
mp.mp.dps = 30

def series_Phi(q, mu, z, s1, s2, nmax=60):
    # word series for G={0,1}, i=2, with weights A(z), pi(z), e(z), times e^{-<d(z),s>}
    c = [q[0][2], q[1][2]]; cp = [q[2][0], q[2][1]]
    a12 = q[0][1] + z*c[0]*cp[1]; a21 = q[1][0] + z*c[1]*cp[0]
    p = [mu[0] + z*mu[2]*cp[0], mu[1] + z*mu[2]*cp[1]]; e = [1 + z*c[0], 1 + z*c[1]]
    d = [-q[0][0] - z*c[0]*cp[0], -q[1][1] - z*c[1]*cp[1]]
    tot = mp.mpc(0)
    for n in range(1, nmax):
        # 1(21)^n : m1=n+1? no: word 1 2 1 2 ... ; enumerate by alternating words of length L>=2
        pass
    for L in range(2, 2*nmax):
        for start in (0, 1):
            w = [(start + k) % 2 for k in range(L)]
            m = [w.count(0), w.count(1)]
            wt = p[w[0]]*e[w[-1]]
            for k in range(L-1): wt *= (a12 if w[k] == 0 else a21)
            tot += wt * mp.mpf(s1)**(m[0]-1)/mp.factorial(m[0]-1) * mp.mpf(s2)**(m[1]-1)/mp.factorial(m[1]-1)
    return mp.e**(-(d[0]*s1 + d[1]*s2)) * tot

def bessel_Phi(q, mu, z, s1, s2):
    c = [q[0][2], q[1][2]]; cp = [q[2][0], q[2][1]]
    a12 = q[0][1] + z*c[0]*cp[1]; a21 = q[1][0] + z*c[1]*cp[0]
    p = [mu[0] + z*mu[2]*cp[0], mu[1] + z*mu[2]*cp[1]]; e = [1 + z*c[0], 1 + z*c[1]]
    d = [-q[0][0] - z*c[0]*cp[0], -q[1][1] - z*c[1]*cp[1]]
    m = a12*a21; Z = 2*mp.sqrt(m*s1*s2)
    val = (p[0]*e[0]*mp.sqrt(m*s1/s2) + p[1]*e[1]*mp.sqrt(m*s2/s1))*mp.besseli(1, Z) + (p[0]*a12*e[1] + p[1]*a21*e[0])*mp.besseli(0, Z)
    return mp.e**(-(d[0]*s1 + d[1]*s2)) * val

qc = [[-3,2,1],[1,-3,2],[2,1,-3]]
mu = [mp.mpf(1)/3]*3
for z in []:
    a = series_Phi(qc, mu, z, 3.0, 2.0); b = bessel_Phi(qc, mu, z, 3.0, 2.0)
    print("g=2 closed form vs word series at z =", complex(z), ": rel diff", float(abs(a-b)/abs(b)))

# (b) exact continuum density by the contour formula (2.2) in mpmath, divided by f_G * Bessel kernel
def fF(q, mu, s1, s2, x, rho, npts):
    qi = -q[2][2]
    acc = mp.mpc(0)
    for k in range(npts):
        th = 2*mp.pi*(k + mp.mpf(1)/2)/npts
        z = rho*mp.e**(1j*th)
        acc += mp.e**(x/z) * bessel_Phi(q, mu, z, s1, s2) / z  # z^{-2} dz/(2 pi i) = z^{-1} dth/(2 pi)
    return mp.re(acc/npts) * mp.e**(-qi*x)

ab = mp.mpf('5.181981'); 
# exact ab, gamma for the cycle at beta=(1/2,1/2): J = 3 - 2z - sqrt((2+z)(1+4z))
zz = mp.mpf(0)
Jf = lambda z: 3 - 2*z - mp.sqrt((2+z)*(1+4*z))
ab = -mp.diff(Jf, 0); j2 = mp.diff(Jf, 0, 2)/2; j3 = mp.diff(Jf, 0, 3)/6
gamma = 3 + j2/ab
print("cycle: ab =", mp.nstr(ab, 10), " gamma =", mp.nstr(gamma, 10), " j3 = J'''(0)/6 =", mp.nstr(j3, 8))
for delta in [0.02, 0.05]:
    for T in [1600, 3200]:
        x = mp.mpf(delta*T); S = T - x; s1 = s2 = S/2
        Z = 2*mp.sqrt(ab*S*x); zs = mp.sqrt(x/(ab*S))
        npts = int(60 + 6*mp.sqrt(Z))*4
        num = fF(qc, mu, s1, s2, x, zs, npts)
        den = bessel_Phi(qc, mu, 0, s1, s2) * mp.e**(-gamma*x) * mp.sqrt(ab*S/x) * mp.besseli(1, Z)
        ratio = num/den
        pred = mp.e**(-S*j3*zs**3)   # leading cubic correction exp(-S j3 z*^3) (sign: J enters as e^{-S J})
        bound = mp.sqrt(x/T)*(1+x)
        print(f"delta={delta}, T={T}, x={float(x):.1f}: ratio f_F/(f_G B) = {mp.nstr(ratio,6)}, |E| = {mp.nstr(abs(ratio-1),6)}, "
              f"sqrt(x/T)(1+x) = {float(bound):.2f}, exp(-S j3 z*^3) = {mp.nstr(pred,6)}")
