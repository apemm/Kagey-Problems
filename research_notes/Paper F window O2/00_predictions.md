# O2 window: predictions written before any run (25 October 2026)

Scripts not yet written or run when this file was saved. Each prediction is
checked in `01_report.md`.

Notation as in Paper F: fresh plus start, `x = (k - pN)/B_N`, `h_N` the
profile of eq:profile, `G_N` the kernel of eq:G with `kappa = u_-`,
`tau_N(x) = alpha_+ ((1-p) theta_+)^alpha_+ x^(-alpha_+-1)`, and
`comp = h_N/B_N + G_N - tau_N/B_N` for `x >= 1`.

Derivation of the crossover (done by hand first). In the window the plus side
is reached either by one plus run of length about `L_k`, with
`B_N G_N ~ tau_N(x) = theta_+^(alpha_+ + o(1))`, or by the minus runs falling
short by `(x/p) B_N` with no giant plus run, at cost `exp(-Lambda_N(x))`, where
`Lambda_N(x) = sup_l [ l (x/p) B_N - (N/s) psi_-(l) ]` and
`psi_-(l) = log E exp(-l (X_- - mu_-))`. For a pure power tail
`Lambda_N(x) -> c_Z (x/p)^beta`, `beta = alpha_-/(alpha_- - 1)`,
`c_Z = (alpha_- - 1) alpha_-^(-beta) K_-^(-1/(alpha_- - 1))`. The two cross at
`x*_N ~ p (alpha_+ log(1/theta_+) / c_Z)^((alpha_- - 1)/alpha_-)`, which agrees
with the plan's order `(log 1/theta_+)^((alpha_- - 1)/alpha_-)`, now with the
constant.

P1 (exactness). My recursion has total mass 1 within 1e-10 at N = 2000 and 5000,
agrees with brute-force enumeration for N <= 12 to 1e-13, and with an
independent forward Markov-chain recursion (state: count, sign, age) at N = 300
to 1e-12.

P2 (plan's table, zeta laws, alpha_+ = 1.9, alpha_- = 1.3). At N = 2000 and 5000:
P/(h/B + G) lies in [0.35, 0.65] for 6 <= x <= 15; P/comp lies in [0.8, 0.97]
there and is closer to 1 at N = 5000 than at N = 2000 at every such x.

P3 (light exponent). For equal indices and theta_+ made small through the tail
constant of the plus law, in the region x < x_c (light term dominant),
-log(B_N (P_N - G_N)) / Lambda_N(x) lies in [0.7, 1.3] once Lambda_N(x) >= 4,
and moves toward 1 as Lambda_N grows. (Polynomial prefactors are the expected
error.)

P4 (crossover location). Define x_c as the smallest x > 1 with P_N <= 2 G_N
(light part equal to the big-jump part). Over theta_+ spanning at least a factor
20, x_c increases, x_c / log(1/theta_+) decreases, and
x_c / x*_N stays within [0.6, 1.4], where x*_N solves
Lambda_N(x) = log(1/(B_N G_N)).
