"""Numerical referee check for Lemma lem:Q of paperG/sec_tools.tex (robust version).

phi(t)  := density of E = Z^{-a}, Z positive a-stable with E e^{-lam Z} = exp(-Gamma(1-a) lam^a).
Series: phi(t) = sum_n (-1)^n Gamma(1-a)^{n+1} t^n / (n! Gamma(1-a(n+1))).
Claim : phi(t) = int_0^1 p_t(x) (1-x)^{-a} dx with p_t(x) = t^{-1/a} g(x t^{-1/a}).
g via Zolotarev's integral for the standard density g_std (E e^{-lam Z_std} = e^{-lam^a}):
  g_std(x) = a/(1-a) x^{-1/(1-a)} (1/pi) int_0^pi A(th) exp(-x^{-a/(1-a)} A(th)) dth,
  A(th) = sin(a th)^{a/(1-a)} sin((1-a) th) / sin(th)^{1/(1-a)},
and g(w) = s^{-1} g_std(w/s), s = Gamma(1-a)^{1/a}.
Then q_{m+1}(k)/T(k) versus phi(mT(k)) for f(n) = n^{-1-a}/zeta(1+a), for increasing k.
"""
import mpmath as mp
import numpy as np

mp.mp.dps = 90


def phi_series(t, a):
    t = mp.mpf(t); a = mp.mpf(a); G = mp.gamma(1 - a)
    s = mp.mpf(0)
    for n in range(0, 1500):
        z = 1 - a * (n + 1)
        if z <= 0 and mp.isint(z):
            continue
        term = (-1) ** n * G ** (n + 1) * t ** n / (mp.factorial(n) * mp.gamma(z))
        s += term
        if n > 50 and abs(term) < mp.mpf(10) ** (-40):
            break
    return s


def g_std(x, a):
    x = mp.mpf(x); a = mp.mpf(a)
    if x <= 0:
        return mp.mpf(0)
    def A(th):
        return mp.sin(a * th) ** (a / (1 - a)) * mp.sin((1 - a) * th) / mp.sin(th) ** (1 / (1 - a))
    c = x ** (-a / (1 - a))
    I = mp.quad(lambda th: A(th) * mp.exp(-c * A(th)), [0, mp.pi / 2, mp.pi])
    return a / (1 - a) * x ** (-1 / (1 - a)) * I / mp.pi


def g(w, a):
    s = mp.gamma(1 - mp.mpf(a)) ** (1 / mp.mpf(a))
    return g_std(w / s, a) / s


def phi_integral(t, a):
    t = mp.mpf(t); a = mp.mpf(a)
    s = t ** (1 / a)
    f = lambda x: (1 / s) * g(x / s, a) * (1 - x) ** (-a)
    return mp.quad(f, [0, 0.3, 0.7, 0.95, 1])


with mp.workdps(20):
    print("== identification phi(t) = int_0^1 p_t(x)(1-x)^-a dx ==", flush=True)
    for a in ['0.3', '0.5', '0.7']:
        print(f"   a={a}: int g = {mp.nstr(mp.quad(lambda w: g(w, a), [0, 1, 5, 50, mp.inf]), 10)}", flush=True)
        for t in ['0.3', '0.8', '1.5']:
            ser = phi_series(t, a)
            integ = phi_integral(t, a)
            extra = f"  exp(-pi t^2/4)={mp.nstr(mp.exp(-mp.pi*mp.mpf(t)**2/4),10)}" if a == '0.5' else ""
            print(f"   a={a} t={t}: series={mp.nstr(ser,10)} integral={mp.nstr(integ,10)}{extra}", flush=True)

print("\n== Lemma Q(ii): sup_{mT(k)<=2} |q_{m+1}(k)/T(k) - phi(mT(k))| for f(n) ~ n^{-1-a} ==", flush=True)
for a in [0.3, 0.5, 0.7]:
    zeta = float(mp.zeta(1 + a))
    # phi on a grid, interpolate
    tg = np.linspace(0, 2.05, 206)
    pg = np.array([float(phi_series(mp.mpf(t), mp.mpf(a))) for t in tg])
    for k in [4000, 16000, 64000]:
        n = np.arange(1, k + 1, dtype=float)
        f = n ** (-1 - a) / zeta
        # T(j) = sum_{n>=j} f(n) = zeta(1+a, j)/zeta(1+a); compute via Hurwitz zeta at a few points + cumulative sums
        T = np.empty(k)
        T[0] = 1.0
        T[1:] = 1.0 - np.cumsum(f[:-1])
        Tk = float(mp.zeta(1 + a, k)) / zeta  # exact tail at k, avoids cancellation
        # correct the cumulative tail by the exact value at k (cancellation is small anyway)
        T = T - (T[k - 1] - Tk)
        L = 1 << int(np.ceil(np.log2(2 * k)))
        fhat = np.fft.rfft(np.concatenate(([0.0], f[:k - 1])), L)
        u = np.zeros(k); u[0] = 1.0
        mmax = int(2.0 / Tk)
        Trev = T[k - 1 - np.arange(k)]
        worst = 0.0; worst_at = None
        rows = []
        for m in range(0, mmax + 1):
            q = float(np.dot(u, Trev))
            t = m * Tk
            ph = float(np.interp(t, tg, pg))
            d = q / Tk - ph
            if abs(d) > worst:
                worst, worst_at = abs(d), (m, t, q / Tk, ph)
            if m % max(1, mmax // 6) == 0:
                rows.append((m, t, q / Tk, ph))
            u = np.fft.irfft(np.fft.rfft(u, L) * fhat, L)[:k]
            u[u < 0] = 0.0
        print(f"a={a}, k={k}, T(k)={Tk:.3e}, mmax={mmax}: sup|q/T-phi|={worst:.4f} at m={worst_at[0]}, mT(k)={worst_at[1]:.3f}, q/T={worst_at[2]:.4f}, phi={worst_at[3]:.4f}", flush=True)
        for (m, t, r, ph) in rows:
            print(f"      m={m:5d} mT(k)={t:.3f} q/T={r:.4f} phi={ph:.4f}", flush=True)
