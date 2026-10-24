import numpy as np, sys
sys.argv=[sys.argv[0]]
exec(open('atlas_check.py').read().split("for N in [int(x)")[0])
J=1500
f, T = law_arrays(J+5)
u = renewal_u(f, J)
v = np.zeros(J+1)
for j in range(1, J+1):
    v[j] = np.dot(f[:j], (u[j-1::-1] + v[j-1::-1]))
cu = np.concatenate([[0], np.cumsum(u[:-1])])              # cu[j] = sum_{j1<j} u(j1)
conv = np.array([sum(u[j1]*u[j-j1] for j1 in range(0,j)) for j in range(0,J+1)])
Cj = alpha*(np.arange(J+1)*u + mu*v + cu + mu*conv)         # exact fixed-j coefficient
observed = {600:7, 1200:11, 2400:19, 4000:27}
for N in [600,1200,2400,4000,8000,16000,32000]:
    g = u[1:J+1] + Cj[1:J+1]/N
    jref = 1+int(np.argmin(g))
    target = 2*alpha*s/N; jplan = int(np.argmax(T[1:] < target))
    print(f"N={N}: refined argmin_j[u(j)+C(j)/N] = {jref:4d}   plan T^-1(2 alpha s/N) = {jplan:4d}   observed = {observed.get(N,'-')}")
