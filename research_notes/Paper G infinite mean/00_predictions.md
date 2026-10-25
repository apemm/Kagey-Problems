# Paper G: predictions, written before any code was run (2026-10-25)

Setting: the alternating lattice walk of Paper F, symmetric zeta run laws
f(n) = n^(-alpha-1)/zeta(alpha+1), 0 < alpha < 1, fair start (a fresh run of random sign)
unless stated. L(x) is the symmetric Lamperti density
sin(pi a)/pi * x^(a-1)(1-x)^(a-1) / (x^(2a) + (1-x)^(2a) + 2 x^a (1-x)^a cos(pi a)).

P1. The ratio N P_N(N/2) / L(1/2) at alpha = 0.5 is 1.015, 1.011, 1.007 for N = 1000, 2000, 4000
    (plan's numbers), reproduced to three decimals by an independent recursion.
P2. The number of sign changes of the first difference of P_N over 0..N is 1, 1, 3, 5 at
    alpha = 0.3, 0.5, 0.7, 0.9, for each N in {1000, 2000, 4000}.
P3. The recursion agrees with a brute-force sum over all sign strings for N <= 12 to 1e-14.
P4. The limit predicted by the renewal decomposition (an integral over the run index of a
    stable density times a covering kernel) equals L. Checked at alpha = 1/2 by quadrature to
    relative error 1e-6.
P5. L is U-shaped (one critical point) iff cos(pi alpha/2) >= alpha, i.e. alpha <= 0.5946,
    and W-shaped (three critical points) otherwise.
P6. The count 5 at alpha = 0.9 comes from the ends, not the bulk: for the fair start the end
    profile is kappa(0) = 1/2, kappa(j) = u(j) (j >= 1), and f(1) = 1/zeta(1.9) > 1/2 gives a local
    maximum at k = 1 and k = N-1. So the count is 3 + 2. The count is 3 + 2 exactly when the
    density is W-shaped and zeta(1+alpha) < 2; at alpha = 0.7, zeta(1.7) > 2, hence 3.
P7. P_N(N-j)/T(N) tends to kappa(j) for each fixed j, with error decreasing in N.
P8. P_N(N-j) / [T(N) u(j) Phi(j/N)] tends to 1 uniformly in 1 <= j <= (1-delta)N, where
    Phi(y) = (1-y)^(a-1) / ((1-y)^(2a) + y^(2a) + 2 (1-y)^a y^a cos(pi a)) (symmetric case).
P9. The mass of P_N within distance o(N) of the ends tends to 0 (it is not a positive fraction).
