# Independent re-implementation of the alternating-run occupation law for a zeta-type run law,
# to check the numbers quoted in the 23 Oct plan (boundary layer, antimode, big-jump zone).
import numpy as np, sys, time
from mpmath import zeta
alpha = 1.5
def law_arrays(N):
    n = np.arange(1, N+2, dtype=float)
    f = n**(-alpha-1)/float(zeta(alpha+1))          # f(1..N+1)
    T = np.zeros(N+3); T[1] = 1.0                    # T(n)=P(X>=n), exact: 1 - sum_{m<n} f(m)
    cs = np.cumsum(f)
    T[2:N+3] = 1.0 - cs[:N+1]
    return f, T
mu = float(zeta(alpha)/zeta(alpha+1)); s = 2*mu; p = 0.5
def renewal_u(f, J):
    u = np.zeros(J+1); u[0] = 1.0
    for j in range(1, J+1):
        u[j] = np.dot(f[:j], u[j-1::-1])
    return u
def occupation(N):
    f, T = law_arrays(N)
    A = [None]*(N+1); B = [None]*(N+1)   # A_t(k): plus run starts at slot t+1 with k plus among first t
    for t in range(N+1):
        A[t] = np.zeros(N+1); B[t] = np.zeros(N+1)
    A[0][0] = 1.0                        # fresh plus start
    for t in range(N):
        a = A[t]; b = B[t]
        if a.any():
            for l in range(1, N-t):      # next run must start at slot t+l+1 <= N
                B[t+l][l:N+1] += a[:N+1-l]*f[l-1]
        if b.any():
            for l in range(1, N-t):
                A[t+l] += b*f[l-1]
    P = np.zeros(N+1)
    for t in range(N):
        r = N-t                           # censored final run of length >= r
        P[r:N+1] += A[t][:N+1-r]*T[r]
        P[:N+1] += B[t]*T[r]
    return P, f, T
for N in [int(x) for x in sys.argv[1:]]:
    t0=time.time(); P, f, T = occupation(N); el=time.time()-t0
    print(f"N={N} mass={P.sum():.12f} time={el:.1f}s")
    u = renewal_u(f, 60)
    print(" boundary P(N-j)/T(N) vs u(j):", " ".join(f"{j}:{P[N-j]/T[N]:.4f}/{u[j]:.4f}" for j in [0,1,2,3,5,10,20,40]))
    half = N//2
    jstar = N - (half + int(np.argmin(P[half:N+1])))
    target = 2*alpha*s/N
    pred = int(np.argmax(T[1:] < target))  # first j with T(j) < target  (T decreasing)
    print(f" antimode j*={jstar}  predicted T^-1(2 alpha s/N)~{pred}  ratio={jstar/pred:.2f}")
    for ell in [0.2,0.5,0.9]:
        L = int(round(ell*N)); k = N - (N-L)//2  # L = 2k-N  => k=(N+L)/2
        L = 2*k-N
        G = (N-L)*f[L-1]/mu + T[L]/mu
        print(f" big-jump ell={ell}: k={k} P/G={P[k]/G:.3f}")
