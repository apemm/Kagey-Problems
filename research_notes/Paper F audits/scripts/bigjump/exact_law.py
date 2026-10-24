import sys, numpy as np, mpmath as mp
N = int(sys.argv[1]); al = 1.5
z1 = float(mp.zeta(al+1))
n = np.arange(1, N+2, dtype=float)
f = np.concatenate([[0.0], n**(-al-1)/z1])          # f[l], l=0..N+1
T = np.array([1.0] + [float(mp.zeta(al+1, m))/z1 for m in range(1, N+2)])  # T[m]=P(X>=m), T[0]=1
mu = float(mp.zeta(al))/z1; s = 2*mu; p = 0.5
# recursion, fresh plus start
A = np.zeros((N+1, N+1)); B = np.zeros((N+1, N+1))
A[0,0] = 1.0
for t in range(1, N):
    for l in range(1, t+1):
        B[t, l:t+1] += A[t-l, 0:t-l+1]*f[l]
        A[t, 0:t-l+1] += B[t-l, 0:t-l+1]*f[l]
P = np.zeros(N+1)
for jj in range(0, N+1):
    tot = 0.0
    for t in range(jj, N):
        tot += A[t, t-jj]*T[N-t]
    for m in range(1, jj+1):
        tot += B[N-m, N-jj]*T[m]
    P[N-jj] = tot
print('mass', P.sum())
# renewal u_-
u = np.zeros(N+1); u[0] = 1.0
for i in range(1, N+1):
    u[i] = np.dot(f[1:i+1], u[i-1::-1][:i])
kap = u.copy()  # plus start
gam = np.zeros(N+1)
for jj in range(1, N+1):
    gam[jj] = np.sum(kap[:jj]*(1+mu*u[jj:0:-1]))
# scale
c = 1/(al*z1)
aN = float(mp.findroot(lambda x: (N/s)*mp.zeta(al+1, x)/z1 - 1, (N/s)**(1/al)))
BN = aN
print('N', N, 'B_N', BN, 'mu', mu)
hK = {1:0.1657906283, 4:0.02779948468, 16:0.0005662518961}
for K in [1,4,16]:
    k = int(np.ceil(p*N + K*BN))
    if k > N: continue
    jj = N-k; L = (k-p*N)/(1-p); Lh = int(np.floor(L))
    G = gam[jj]*f[Lh] + T[Lh]*kap[jj]
    lead = al*(1-p)**al*K**(-al-1)
    print(K, 'k', k, 'B P/h', BN*P[k]/hK[K], 'P/G', P[k]/G, 'B G/lead', BN*G/lead, 'target h/lead', hK[K]/lead)
