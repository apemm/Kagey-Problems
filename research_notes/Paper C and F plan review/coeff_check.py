import numpy as np, sys
sys.argv=[sys.argv[0]]
exec(open('atlas_check.py').read().split("for N in [int(x)")[0])
J=400
f, T = law_arrays(J+5)
u = renewal_u(f, J)
# v(j) = sum_m m f^{*m}(j) = E[M ; renewal at j] : v = f*u + f*v  (first-renewal decomposition)
v = np.zeros(J+1)
for j in range(1, J+1):
    v[j] = np.dot(f[:j], (u[j-1::-1] + v[j-1::-1]))
def C(j):   # exact lim_N N*(P_N(N-j)/T(N) - u(j)) for the fresh plus start, equal laws
    s1 = j*u[j] + mu*v[j]                                  # censored giant run: alpha*u(j)*E[a|j]
    s2 = sum(u[j1]*(1+mu*u[j-j1]) for j1 in range(0, j))   # complete giant run, Green sums
    return alpha*(s1+s2)
print("plan coefficient 2 alpha s/mu^2 =", round(2*alpha*s/mu**2,3))
print("exact limit coefficient C(j)/j:", " ".join(f"j={j}:{C(j)/j:.3f}" for j in [1,2,5,10,20,40,80,160,320]))
for N in [1200, 2400, 4800]:
    P, fN, TN = occupation(N)
    print(f"N={N} finite-N excess*N/j:", " ".join(f"j={j}:{(P[N-j]/TN[N]-u[j])*N/j:.3f}" for j in [5,10,20,40,80]), flush=True)
