import numpy as np, sys
sys.argv = [sys.argv[0]]  # reuse module without running its loop
exec(open('atlas_check.py').read().split("for N in [int(x)")[0])
for N in [600, 1200, 2400]:
    P, f, T = occupation(N)
    u = renewal_u(f, 200)
    pred = 2*alpha*s/(mu**2)   # coefficient of j/N in the plan's second-order junction expansion
    rows = []
    for j in [5,10,20,40,80,160]:
        if j < N//4:
            ex = P[N-j]/T[N] - u[j]
            rows.append(f"j={j}: excess*N/j={ex*N/j:.3f}")
    print(f"N={N} plan coefficient 2 alpha s/mu^2={pred:.3f} ::", "  ".join(rows), flush=True)
