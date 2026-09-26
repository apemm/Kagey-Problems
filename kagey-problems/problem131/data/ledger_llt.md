# Problem 131 ledger: a uniform local limit theorem (LLT)

Date of every entry below: 2026-09-26, unless stated otherwise.

Notation (shared with Papers A-D): N steps, bin k, a = k, b = N - k, q = 1 - p, u = q/p,
T = Nq. For 2 <= k <= N-2 put n1 = a - 1, n2 = b - 1 (both >= 1).

## State before any computation

Nothing in this file has been computed yet. The only facts used below are the run-count formula
(Paper A, Theorem thm:pmf), the Bessel bound of Paper A (Theorem thm:allbin-bessel), and pencil
calculations.

Pencil observation (E). Theorem thm:pmf can be rewritten as
  P_N(k) = (q/2) [ 2 P(D = 0) + P(D = 1) + P(D = -1) ],  D = Y1 - Y2,
  Y1 ~ Bin(n1, q), Y2 ~ Bin(n2, q) independent,
because C(n1,r) C(n2,r) q^{2r} p^{N-2-2r} = P(Y1 = r) P(Y2 = r), and the even-change terms pair
r with r +- 1 in the same way. Equivalently P_N(k) = 2q P(Bin(n1,q) + Bin(n2,p) + Bin(2,1/2) = b).

Candidate approximations (all with 2 <= k <= N-2):
- U (tilted Bessel / Skellam). Tilt D by s > 0: pi1 = qs/(p+qs), pi2 = q/(ps+q),
  Lambda(s) = (p+qs)^{n1} (p+q/s)^{n2}. Take s = s* with n1 pi1 = n2 pi2 (tilted mean of D is 0),
  sigma^2 = n1 pi1(1-pi1) + n2 pi2(1-pi2), K_j = e^{-sigma^2} I_j(sigma^2). Then
  U = (q/2) Lambda(s*) [ 2 K_0 + (s* + 1/s*) K_1 ].
- G (Gaussian, same tilt): K_0 and K_1 replaced by 1/sqrt(2 pi sigma^2).
- TM (transfer-matrix Gaussian saddle point): P(X_N = x) ~ 2 c_+(t) lambda_+(t)^{N-1} e^{-tx}
  / sqrt(2 pi (N-1) kappa''(t)), kappa = log lambda_+, (N-1) kappa'(t) = x, x = 2k - N.
- B (Paper A Bessel form): (1/2) p^{N-1} T_{a,b}(u) = p^{N-1} u J_c(sqrt(ab) u).
Relative error of an approximation A: err = P/A - 1.

## Predictions (written before running anything)

P1. Identity (E) holds exactly (Fraction arithmetic) for all 2 <= N <= 40, all 1 <= k <= N-1,
    and q in {1/2, 1/3, 1/7, 2/11, 9/10}. Prediction: 0 mismatches.

P2. U at the centre, diffusive regime (Npq >> 1). Pencil Edgeworth comparison gives
    err_U(N/2) = -3/(8 n) (1 + o(1)) with n = N/2 - 1, independent of q to leading order.
    N = 100, q = 0.3: err in [-0.0100, -0.0053] (that is -0.00765 +- 30%).
    N = 1000, q = 0.3: err in [-0.00098, -0.00053] (-0.00075 +- 30%).
    Same windows for q = 0.5.

P3. U in the ballistic regime. N = 1000, q = 1/N: worst |err_U| over 2 <= k <= N-2 is < 0.02.
    N = 1000, q = 1e-5 (T = 0.01): worst |err_U| < 0.002.

P4. U near the edges, diffusive regime. Pencil limit (q fixed, N -> infinity, n1 fixed):
    err_U -> P(Poi(n1) = n1+1) / (e^{-n1} I_1(n1)) - 1, which is -0.115 (n1 = 1), -0.162 (n1 = 2),
    -0.147 (n1 = 3), -0.108 (n1 = 5), -0.062 (n1 = 10).
    N = 1000, q = 0.3: worst |err_U| over 2 <= k <= N-2 lies in [0.13, 0.18], attained at
    k in {3, N-3}, with P < U (err < 0).

P5. Uniform constant. C_emp = max over all tested (N, q <= 1/2, 2 <= k <= N-2) of
    min(n1,n2) |err_U| is at most 1.0. (Pencil: n1 |err| -> about 0.7-0.8 at the edge as n1 grows.)

P6. Obstruction for Gaussian forms. At N = 1000, q = 1e-4 (T = 0.1), centre bin:
    err_G <= -0.40 (G overshoots by a factor about 1.8), and |err_TM| >= 0.5.
    As q -> 0 at fixed N, both G/P and TM/P -> infinity at the centre.

P7. B in the diffusive regime. N = 1000, q = 0.3: worst |err_B| over bins > 0.99.
    B in the ballistic regime, N = 1000, q = 1e-4: worst |err_B| is below Paper A's bound
    N u^2/2 + u at every bin (this is a theorem; the check is a sanity check).

Two methods for every reported number:
- P_N(k): (i) the dynamic-programming recursion (eq:dp of Paper A); (ii) the run-count formula
  (Theorem thm:pmf) summed in log space; exact Fractions for N <= 40.
- e^{-x} I_j(x): (i) power series in 60-digit Decimal; (ii) trapezoid rule for
  (1/pi) int_0^pi e^{x(cos t - 1)} cos(jt) dt (DLMF 10.32.3), which converges geometrically.
- s*: (i) closed-form root of n1 p s^2 + (n1 - n2) q s - n2 p = 0; (ii) bisection on n1 pi1 - n2 pi2.

Runtime estimate: N = 1000 needs an O(N^2) = 10^6-step recursion per q in pure Python
(about 1-2 s) and O(N) work per bin for the run-count sum (about 10^6 terms per row, a few
seconds). With 10 values of q and 2 values of N the whole run is under 5 minutes.

## Results of run 1 (verify_uniform_llt.py, 13.9 s)

Verbatim output (data/uniform-llt-verification.txt):

```
P1 identity (E): 3900 (N,k,q) checked exactly, mismatches = 0
Bessel e^-x I_j(x): series vs trapezoid, max relative difference = 3.84e-10
saddle s*: closed form vs bisection, max relative difference = 5.55e-16
N=   10 q=5.0e-01 | dp/rc 0.0e+00 | centre U -6.03e-02 G -1.28e-01 TM -7.47e-02 B -9.77e-01 | worst U -9.192e-02@2 G -4.34e-01@2 TM -1.85e-01@8 B -9.77e-01@4
N=   10 q=3.0e-01 | dp/rc 0.0e+00 | centre U -5.42e-02 G -1.37e-01 TM -8.47e-02 B -6.61e-01 | worst U -8.694e-02@2 G -3.89e-01@8 TM -1.85e-01@8 B -6.61e-01@3
N=   10 q=1.0e-01 | dp/rc 0.0e+00 | centre U -2.06e-02 G -2.31e-01 TM -1.84e-01 B -1.51e-01 | worst U -2.312e-02@2 G -4.47e-01@2 TM -3.13e-01@2 B -1.51e-01@2
N=   10 q=3.0e-02 | dp/rc 0.0e+00 | centre U -2.96e-03 G -4.60e-01 TM -4.27e-01 B -3.46e-02 | worst U -3.020e-03@3 G -6.34e-01@2 TM -5.55e-01@8 B -3.46e-02@2
N=   10 q=1.0e-02 | dp/rc 0.0e+00 | centre U -3.75e-04 G -6.61e-01 TM -6.40e-01 B -1.05e-02 | worst U -3.761e-04@4 G -7.77e-01@2 TM -7.30e-01@8 B -1.05e-02@2
N=   10 q=3.0e-03 | dp/rc 0.0e+00 | centre U -3.53e-05 G -8.08e-01 TM -7.97e-01 B -3.05e-03 | worst U -3.532e-05@5 G -8.75e-01@2 TM -8.49e-01@2 B -3.05e-03@2
N=   10 q=1.0e-03 | dp/rc 0.0e+00 | centre U -3.97e-06 G -8.88e-01 TM -8.82e-01 B -1.01e-03 | worst U -3.975e-06@5 G -9.28e-01@2 TM -9.13e-01@2 B -1.01e-03@2
N=   10 q=3.0e-04 | dp/rc 0.0e+00 | centre U -3.59e-07 G -9.39e-01 TM -9.35e-01 B -3.00e-04 | worst U -3.593e-07@5 G -9.60e-01@2 TM -9.52e-01@2 B -3.00e-04@2
N=   10 q=1.0e-04 | dp/rc 0.0e+00 | centre U -4.00e-08 G -9.65e-01 TM -9.62e-01 B -1.00e-04 | worst U -3.997e-08@5 G -9.77e-01@2 TM -9.72e-01@2 B -1.00e-04@3
N=   10 q=1.0e-05 | dp/rc 0.0e+00 | centre U -4.00e-10 G -9.89e-01 TM -9.88e-01 B -1.00e-05 | worst U -4.000e-10@5 G -9.93e-01@2 TM -9.91e-01@2 B -1.00e-05@5
N=   20 q=5.0e-01 | dp/rc 0.0e+00 | centre U -3.50e-02 G -6.31e-02 TM -3.74e-02 B -9.99e-01 | worst U -1.215e-01@3 G -4.89e-01@2 TM -2.06e-01@2 B -9.99e-01@9
N=   20 q=3.0e-01 | dp/rc 0.0e+00 | centre U -3.39e-02 G -6.78e-02 TM -4.23e-02 B -8.34e-01 | worst U -1.070e-01@3 G -4.51e-01@2 TM -2.02e-01@2 B -8.34e-01@8
N=   20 q=1.0e-01 | dp/rc 0.0e+00 | centre U -2.26e-02 G -1.12e-01 TM -8.76e-02 B -1.98e-01 | worst U -4.019e-02@3 G -4.65e-01@2 TM -2.98e-01@18 B -1.98e-01@2
N=   20 q=3.0e-02 | dp/rc 0.0e+00 | centre U -5.30e-03 G -2.84e-01 TM -2.64e-01 B -3.91e-02 | worst U -5.860e-03@4 G -6.37e-01@2 TM -5.41e-01@18 B -3.91e-02@2
N=   20 q=1.0e-02 | dp/rc 0.0e+00 | centre U -7.83e-04 G -5.15e-01 TM -5.01e-01 B -1.10e-02 | worst U -7.936e-04@6 G -7.79e-01@18 TM -7.24e-01@18 B -1.10e-02@2
N=   20 q=3.0e-03 | dp/rc 0.0e+00 | centre U -7.77e-05 G -7.17e-01 TM -7.09e-01 B -3.09e-03 | worst U -7.779e-05@8 G -8.77e-01@2 TM -8.47e-01@18 B -3.09e-03@2
N=   20 q=1.0e-03 | dp/rc 0.0e+00 | centre U -8.88e-06 G -8.33e-01 TM -8.29e-01 B -1.01e-03 | worst U -8.877e-06@9 G -9.29e-01@2 TM -9.11e-01@18 B -1.01e-03@2
N=   20 q=3.0e-04 | dp/rc 0.0e+00 | centre U -8.07e-07 G -9.08e-01 TM -9.06e-01 B -3.01e-04 | worst U -8.067e-07@9 G -9.61e-01@2 TM -9.51e-01@2 B -3.01e-04@2
N=   20 q=1.0e-04 | dp/rc 0.0e+00 | centre U -8.99e-08 G -9.47e-01 TM -9.45e-01 B -1.00e-04 | worst U -8.988e-08@10 G -9.77e-01@2 TM -9.72e-01@2 B -1.00e-04@2
N=   20 q=1.0e-05 | dp/rc 0.0e+00 | centre U -9.00e-10 G -9.83e-01 TM -9.83e-01 B -1.00e-05 | worst U -8.999e-10@10 G -9.93e-01@2 TM -9.91e-01@2 B -1.00e-05@7
N=   40 q=5.0e-01 | dp/rc 0.0e+00 | centre U -1.82e-02 G -3.14e-02 TM -1.87e-02 B -1.00e+00 | worst U -1.411e-01@3 G -5.15e-01@2 TM -2.17e-01@38 B -1.00e+00@19
N=   40 q=3.0e-01 | dp/rc 0.0e+00 | centre U -1.80e-02 G -3.38e-02 TM -2.11e-02 B -9.61e-01 | worst U -1.317e-01@3 G -4.91e-01@2 TM -2.14e-01@38 B -9.61e-01@18
N=   40 q=1.0e-01 | dp/rc 0.0e+00 | centre U -1.59e-02 G -5.44e-02 TM -4.20e-02 B -2.85e-01 | worst U -6.310e-02@3 G -4.80e-01@38 TM -2.83e-01@2 B -2.85e-01@11
N=   40 q=3.0e-02 | dp/rc 0.0e+00 | centre U -7.12e-03 G -1.46e-01 TM -1.35e-01 B -4.81e-02 | worst U -1.028e-02@5 G -6.38e-01@2 TM -5.28e-01@38 B -4.81e-02@2
N=   40 q=1.0e-02 | dp/rc 0.0e+00 | centre U -1.42e-03 G -3.53e-01 TM -3.45e-01 B -1.20e-02 | worst U -1.506e-03@9 G -7.86e-01@2 TM -7.25e-01@38 B -1.20e-02@2
N=   40 q=3.0e-03 | dp/rc 0.0e+00 | centre U -1.57e-04 G -6.00e-01 TM -5.95e-01 B -3.18e-03 | worst U -1.578e-04@13 G -8.83e-01@2 TM -8.51e-01@38 B -3.18e-03@2
N=   40 q=1.0e-03 | dp/rc 0.0e+00 | centre U -1.85e-05 G -7.60e-01 TM -7.57e-01 B -1.02e-03 | worst U -1.847e-05@16 G -9.33e-01@2 TM -9.14e-01@38 B -1.02e-03@2
N=   40 q=3.0e-04 | dp/rc 0.0e+00 | centre U -1.70e-06 G -8.67e-01 TM -8.65e-01 B -3.02e-04 | worst U -1.695e-06@18 G -9.63e-01@2 TM -9.53e-01@38 B -3.02e-04@2
N=   40 q=1.0e-04 | dp/rc 0.0e+00 | centre U -1.89e-07 G -9.23e-01 TM -9.22e-01 B -1.00e-04 | worst U -1.895e-07@19 G -9.79e-01@2 TM -9.73e-01@2 B -1.00e-04@2
N=   40 q=1.0e-05 | dp/rc 0.0e+00 | centre U -1.90e-09 G -9.76e-01 TM -9.75e-01 B -1.00e-05 | worst U -1.899e-09@20 G -9.93e-01@2 TM -9.91e-01@2 B -1.00e-05@4
N=  100 q=5.0e-01 | dp/rc 1.3e-13 | centre U -7.42e-03 G -1.25e-02 TM -7.50e-03 B -1.00e+00 | worst U -1.534e-01@3 G -5.30e-01@2 TM -2.25e-01@2 B -1.00e+00@43
N=  100 q=3.0e-01 | dp/rc 8.9e-14 | centre U -7.39e-03 G -1.35e-02 TM -8.45e-03 B -9.99e-01 | worst U -1.496e-01@3 G -5.18e-01@2 TM -2.23e-01@2 B -9.99e-01@48
N=  100 q=1.0e-01 | dp/rc 8.0e-14 | centre U -7.12e-03 G -2.15e-02 TM -1.65e-02 B -4.94e-01 | worst U -9.931e-02@3 G -4.98e-01@2 TM -2.64e-01@2 B -4.94e-01@42
N=  100 q=3.0e-02 | dp/rc 6.4e-14 | centre U -5.80e-03 G -5.34e-02 TM -4.85e-02 B -7.44e-02 | worst U -2.055e-02@5 G -6.20e-01@2 TM -4.86e-01@2 B -7.44e-02@14
N=  100 q=1.0e-02 | dp/rc 3.5e-14 | centre U -2.32e-03 G -1.63e-01 TM -1.58e-01 B -1.50e-02 | worst U +4.091e-03@2 G -7.88e-01@2 TM -7.20e-01@98 B -1.50e-02@2
N=  100 q=3.0e-03 | dp/rc 1.4e-14 | centre U -3.53e-04 G -4.08e-01 TM -4.05e-01 B -3.45e-03 | worst U +7.180e-04@2 G -8.92e-01@2 TM -8.59e-01@2 B -3.45e-03@2
N=  100 q=1.0e-03 | dp/rc 4.4e-15 | centre U -4.55e-05 G -6.26e-01 TM -6.24e-01 B -1.05e-03 | worst U +9.670e-05@2 G -9.40e-01@2 TM -9.22e-01@98 B -1.05e-03@2
N=  100 q=3.0e-04 | dp/rc 1.8e-15 | centre U -4.31e-06 G -7.88e-01 TM -7.87e-01 B -3.05e-04 | worst U +9.318e-06@2 G -9.68e-01@2 TM -9.58e-01@98 B -3.05e-04@2
N=  100 q=1.0e-04 | dp/rc 1.8e-15 | centre U -4.86e-07 G -8.77e-01 TM -8.76e-01 B -1.01e-04 | worst U +1.056e-06@2 G -9.81e-01@2 TM -9.76e-01@2 B -1.01e-04@2
N=  100 q=1.0e-05 | dp/rc 1.8e-15 | centre U -4.90e-09 G -9.61e-01 TM -9.61e-01 B -1.00e-05 | worst U +1.065e-08@2 G -9.94e-01@2 TM -9.92e-01@2 B -1.00e-05@16
N= 1000 q=5.0e-01 | dp/rc 1.5e-12 | centre U -7.49e-04 G -1.25e-03 TM -7.50e-04 B -1.00e+00 | worst U -1.609e-01@3 G -5.38e-01@2 TM -2.29e-01@2 B -1.00e+00@2
N= 1000 q=3.0e-01 | dp/rc 1.4e-12 | centre U -7.49e-04 G -1.35e-03 TM -8.45e-04 B -1.00e+00 | worst U -1.606e-01@3 G -5.37e-01@2 TM -2.29e-01@998 B -1.00e+00@5
N= 1000 q=1.0e-01 | dp/rc 1.4e-12 | centre U -7.47e-04 G -2.14e-03 TM -1.64e-03 B -9.97e-01 | worst U -1.552e-01@3 G -5.31e-01@2 TM -2.37e-01@998 B -9.97e-01@492
N= 1000 q=3.0e-02 | dp/rc 1.7e-12 | centre U -7.38e-04 G -5.07e-03 TM -4.57e-03 B -3.93e-01 | worst U -9.060e-02@3 G -5.40e-01@2 TM -3.12e-01@2 B -3.93e-01@472
N= 1000 q=1.0e-02 | dp/rc 1.5e-12 | centre U -7.10e-04 G -1.36e-02 TM -1.31e-02 B -5.89e-02 | worst U +2.671e-02@2 G -6.88e-01@2 TM -5.64e-01@2 B -5.89e-02@410
N= 1000 q=3.0e-03 | dp/rc 9.6e-13 | centre U -5.80e-04 G -4.60e-02 TM -4.55e-02 B -7.49e-03 | worst U +1.626e-02@2 G -8.76e-01@2 TM -8.32e-01@2 B -7.49e-03@132
N= 1000 q=1.0e-03 | dp/rc 4.9e-13 | centre U -2.34e-04 G -1.56e-01 TM -1.56e-01 B -1.50e-03 | worst U +3.813e-03@2 G -9.49e-01@2 TM -9.31e-01@2 B -1.50e-03@2
N= 1000 q=3.0e-04 | dp/rc 1.8e-13 | centre U -3.58e-05 G -4.03e-01 TM -4.03e-01 B -3.45e-04 | worst U +4.852e-04@2 G -9.77e-01@2 TM -9.69e-01@998 B -3.45e-04@2
N= 1000 q=1.0e-04 | dp/rc 6.4e-14 | centre U -4.63e-06 G -6.23e-01 TM -6.23e-01 B -1.05e-04 | worst U +6.044e-05@2 G -9.88e-01@2 TM -9.84e-01@2 B -1.05e-04@2
N= 1000 q=1.0e-05 | dp/rc 7.1e-15 | centre U -4.95e-08 G -8.75e-01 TM -8.75e-01 B -1.01e-05 | worst U +6.381e-07@2 G -9.96e-01@2 TM -9.95e-01@998 B -1.01e-05@65
C_emp = max min(n1,n2)|err_U| = 0.6392 at (N,q,k,err) = (1000, 0.5, 27, -0.024585480842464036)
elapsed 13.9 s
```

Verdicts:
- P1 CONFIRMED. 3900 exact checks, 0 mismatches (recursion eq:dp = run-count formula = identity E).
- P2 CONFIRMED. Centre err_U: N=100: -7.39e-3 (q=0.3), -7.42e-3 (q=0.5), both in [-0.0100,-0.0053];
  N=1000: -7.49e-4 (q=0.3 and q=0.5), in [-0.00098,-0.00053]. The pencil value -3/(8n) is
  -7.65e-3 (n=49) and -7.51e-4 (n=499).
- P3 CONFIRMED. N=1000, q=1e-3: worst |err_U| = 3.81e-3 < 0.02. q=1e-5: 6.38e-7 < 0.002.
- P4 CONFIRMED. N=1000, q=0.3: worst err_U = -0.1606 at k=3 (by symmetry also k=N-3), in [0.13,0.18],
  P < U. Limit value predicted -0.162.
- P5 CONFIRMED. C_emp = 0.6392 <= 1.0, attained at N=1000, q=0.5, k=27 (n1=26, err=-0.02459).
  Note: the maximiser is not at the extreme edge, so N=1000 does not show the supremum.
- P6 CONFIRMED. N=1000, q=1e-4, centre: err_G = -0.623, err_TM = -0.623. Both tend to -1 as q -> 0
  at every N in the table (e.g. N=10, q=1e-5: -0.989 and -0.988).
- P7 CONFIRMED (first half). N=1000, q=0.3: worst |err_B| = 1.00. The Paper A bound check was not
  coded in run 1; it is added in run 2.

Unexpected, recorded for the note:
- In the ballistic regime U is far more accurate than Paper A's Bessel form B: at N=10, q=1e-4 the
  worst |err_U| is 4.0e-8 against 1.0e-4 for B; at N=1000, q=1e-4 it is 6.0e-5 against 1.05e-4.
  The centre error of U behaves like a constant times N q^2 when Nq is small
  (N=1000: -4.63e-6 at q=1e-4, -4.95e-8 at q=1e-5).
- The worst U bin is k=2 (err > 0, small) in the ballistic regime and k=3 (err < 0, about 16%) in the
  diffusive regime.

## Predictions for run 2 (written before run 2)

Proof sketch at this point (details in the note): with x = sigma^2, rho = I_1(x)/I_0(x),
V = n1 v1^2 + n2 v2^2, m = n1 pi1 = n2 pi2, M = m max(pi1, pi2),
  |err_U| <= E_int := (1/rho) [ <min(1, 4 kappa^2 V)> + <Phi^2>/2 + <|Phi| |sin t|> ]
          <= E     := (1/rho) [ (4V + (64/3) M) <kappa^2> + (1024/9) M^2 <kappa^3> ],
where kappa = 1 - cos t, <.> is the average against e^{x(cos t - 1)} on [-pi, pi], Phi is the phase
of the tilted characteristic function, <kappa^2> = 2 - 2rho - rho/x and
<kappa^3> = 4 - 4rho - 3rho/x - 2rho/x^2 + 1/x. For q <= 1/2 this gives
|err_U| <= 2.24e4 / min(n1, n2) (crude constant).

P8. Sharp constant. N = 10^4, q in {0.5, 0.3}: max over 2 <= k <= 400 of min(n1,n2)|err_U| lies in
    [0.64, 0.71]. Heuristic (Poisson edge limit plus Edgeworth): the supremum over all N, k and
    q <= 1/2 is 17/24 = 0.7083, approached only as N -> infinity and then n1 -> infinity.
    No tested point exceeds 0.7083.
P9. Consistency of the proof. At every tested (N, k, q) with q <= 1/2 and 2 <= k <= N-2:
    |err_U| <= E_int <= E. Pointwise lemmas on grids: F(pi,t) in [0, (128/(3 pi^3)) pi^2 t^3] for
    t in (0, pi); g - |psi| <= g min(1, 4 kappa^2 V); 1/rho <= 1 + 2/x; <kappa^2> <= min(3/2, 2/x^2);
    <kappa^3> <= min(5/2, 8/x^3). Prediction: 0 violations.
P10. Looseness at the centre, q = 0.5, N = 1000: E / |err_U| in [100, 1000] (pencil about 330).
P11. Paper A's bound 0 <= -err_B <= N u^2/2 + u holds at every tested bin (theorem; sanity check).
P12. Anti-persistent side (q > 1/2), where the corollary is not claimed. N = 101, q = 0.999,
    k = 50: |err_U| in [0.05, 0.5] (pencil: the tilted D is close to -1 + Poisson(1), which the
    symmetric Bessel kernel misses). N = 100, q = 0.999, k = 50 (symmetric centre): |err_U| < 0.01.

Runtime estimate for run 2: N = 10^4 restricted recursion over k <= 400 costs 4e6 steps per q
(a few seconds); E_int needs a 4000-point quadrature per bin, done only on about 200 sampled bins
(well under a minute). Total under 3 minutes.

## Results of run 2

First pass (verbatim, data/uniform-llt-verification-run2a.txt):

```
P9 lemma F: 159201 grid points, violations = 0, max F/(pi^2 t^3) = 0.4992 (cF = 1.3761)
P9 lemma M (1/rho <= 1+2/x, <k^2> <= min(3/2,2/x^2), <k^3> <= min(5/2,8/x^3)): violations = 0; max x^2<k^2> = 1.0223, max x^3<k^3> = 2.7921, Bessel vs quadrature max diff = 1.5e-12
P9 chain: 217 sampled (N,k,q): violations |err_U|>E_int: 0, E_int>E: 0; max (g-|psi|)/(g min(1,4k^2V)) = 103869.7035; Fourier representation vs run-count: max |dlogP| = 7.5e-13
   N=1000 q=0.5 k=500: |err_U|=7.492e-04  E_int=3.018e-03  E=2.501e-01  E/|err|=333.7  E_int/|err|=4.0
   N=1000 q=0.3 k=500: |err_U|=7.489e-04  E_int=3.020e-03  E=6.648e-02  E/|err|=88.8  E_int/|err|=4.0
   N=100 q=0.5 k=50: |err_U|=7.418e-03  E_int=3.112e-02  E=2.669e+00  E/|err|=359.7  E_int/|err|=4.2
   N=1000 q=0.5 k=3: |err_U|=1.609e-01  E_int=8.509e-01  E=2.195e+02  E/|err|=1364.2  E_int/|err|=5.3
   N=1000 q=0.001 k=500: |err_U|=2.343e-04  E_int=5.929e-03  E=2.183e-02  E/|err|=93.2  E_int/|err|=25.3
   N=1000 q=0.001 k=2: |err_U|=3.813e-03  E_int=1.871e-01  E=1.150e+00  E/|err|=301.6  E_int/|err|=49.1
   N=1000 q=0.0001 k=500: |err_U|=4.629e-06  E_int=1.122e-03  E=4.115e-03  E/|err|=889.0  E_int/|err|=242.4
P11 Paper A bound 0 <= -err_B <= N u^2/2 + u: 4468 bins, violations = 0
P8 N=10000 q=0.5: max_(2<=k<=400) n1|err_U| = 0.6859 at k=83 (err -8.3646e-03); err_U(k=3) = -0.1617; restricted recursion vs run-count max |dlogP| = 2.4e-11
P8 N=10000 q=0.3: max_(2<=k<=400) n1|err_U| = 0.6773 at k=60 (err -1.1479e-02); err_U(k=3) = -0.1616; restricted recursion vs run-count max |dlogP| = 2.0e-11
P12 N=101 q=0.999 k=50: err_U = +0.5776  (exact recursion vs run-count |dlogP| = 6.7e-16)
P12 N=100 q=0.999 k=50: err_U = -0.0000  (exact recursion vs run-count |dlogP| = 8.4e-16)
P12 N=101 q=0.9 k=50: err_U = -0.0070  (exact recursion vs run-count |dlogP| = 2.1e-14)
P12 N=1000 q=0.99 k=400: err_U = -0.0002
elapsed 7.7 s
```

The line "max (g-|psi|)/(g min(1,4k^2V)) = 103869.7035" looked like a violation of the modulus lemma.
Diagnosis: the check computed g - |psi| as a difference of two floats that are both close to 1
(small t, small V), so it measured rounding noise divided by a tiny min(1, 4 kappa^2 V). The check
was rewritten to compute 1 - |psi|/g = -expm1(-sum n_j ell(z_j)) with ell(z) = -(log1p(-z)+z)/2
(series for small z). No other line of the script changed. Second pass (verbatim,
data/uniform-llt-verification-run2.txt):

```
P9 lemma F: 159201 grid points, violations = 0, max F/(pi^2 t^3) = 0.4992 (cF = 1.3761)
P9 lemma M (1/rho <= 1+2/x, <k^2> <= min(3/2,2/x^2), <k^3> <= min(5/2,8/x^3)): violations = 0; max x^2<k^2> = 1.0223, max x^3<k^3> = 2.7921, Bessel vs quadrature max diff = 1.5e-12
P9 chain: 217 sampled (N,k,q): violations |err_U|>E_int: 0, E_int>E: 0; max (g-|psi|)/(g min(1,4k^2V)) = 1.0000; Fourier representation vs run-count: max |dlogP| = 7.5e-13
   N=1000 q=0.5 k=500: |err_U|=7.492e-04  E_int=3.018e-03  E=2.501e-01  E/|err|=333.7  E_int/|err|=4.0
   N=1000 q=0.3 k=500: |err_U|=7.489e-04  E_int=3.020e-03  E=6.648e-02  E/|err|=88.8  E_int/|err|=4.0
   N=100 q=0.5 k=50: |err_U|=7.418e-03  E_int=3.112e-02  E=2.669e+00  E/|err|=359.7  E_int/|err|=4.2
   N=1000 q=0.5 k=3: |err_U|=1.609e-01  E_int=8.509e-01  E=2.195e+02  E/|err|=1364.2  E_int/|err|=5.3
   N=1000 q=0.001 k=500: |err_U|=2.343e-04  E_int=5.929e-03  E=2.183e-02  E/|err|=93.2  E_int/|err|=25.3
   N=1000 q=0.001 k=2: |err_U|=3.813e-03  E_int=1.871e-01  E=1.150e+00  E/|err|=301.6  E_int/|err|=49.1
   N=1000 q=0.0001 k=500: |err_U|=4.629e-06  E_int=1.122e-03  E=4.115e-03  E/|err|=889.0  E_int/|err|=242.4
P11 Paper A bound 0 <= -err_B <= N u^2/2 + u: 4468 bins, violations = 0
P8 N=10000 q=0.5: max_(2<=k<=400) n1|err_U| = 0.6859 at k=83 (err -8.3646e-03); err_U(k=3) = -0.1617; restricted recursion vs run-count max |dlogP| = 2.4e-11
P8 N=10000 q=0.3: max_(2<=k<=400) n1|err_U| = 0.6773 at k=60 (err -1.1479e-02); err_U(k=3) = -0.1616; restricted recursion vs run-count max |dlogP| = 2.0e-11
P12 N=101 q=0.999 k=50: err_U = +0.5776  (exact recursion vs run-count |dlogP| = 6.7e-16)
P12 N=100 q=0.999 k=50: err_U = -0.0000  (exact recursion vs run-count |dlogP| = 8.4e-16)
P12 N=101 q=0.9 k=50: err_U = -0.0070  (exact recursion vs run-count |dlogP| = 2.1e-14)
P12 N=1000 q=0.99 k=400: err_U = -0.0002
elapsed 8.6 s
```

The maximum ratio printed at full precision is 1.0 (attained where |psi| = 0 and the cap
min(1, .) = 1 is active), so the lemma holds at every grid point.

Verdicts:
- P8 CONFIRMED. N = 10^4: max n1|err_U| = 0.6859 (q=0.5, k=83) and 0.6773 (q=0.3, k=60), both in
  [0.64, 0.71]; nothing exceeds 17/24 = 0.7083. err_U(k=3) = -0.1617 and -0.1616 (limit -0.162).
  The two exact methods (restricted recursion in Decimal, run-count in log space) agree to 2.4e-11
  in log P.
- P9 CONFIRMED. 0 violations of |err_U| <= E_int <= E on 217 sampled points; lemma F and lemma M
  0 violations; Fourier representation of P_N(k) agrees with the run-count formula to 7.5e-13.
  Unexpected: max F/(pi^2 t^3) = 0.4992, so the sharp constant in lemma F is 1/2, not 1.376.
- P10 CONFIRMED. E/|err_U| = 333.7 at N=1000, q=0.5, centre (pencil 330). E_int/|err_U| is only
  4.0 there, so almost all the looseness is in passing from E_int to the closed form E.
- P11 CONFIRMED. 4468 bins, 0 violations of Paper A's bound.
- P12 REFUTED as a number, confirmed in direction. N=101, q=0.999, k=50: err_U = +0.578, outside
  the predicted window [0.05, 0.5]. The symmetric kernel does fail there, by more than predicted.
  N=100, q=0.999, k=50: err_U = -0.0000 (< 0.01, confirmed). The corollary is only claimed for
  q <= 1/2, and this is the reason.

## Predictions for run 3 (written before run 3): the centre crossing from U

At the centre (N even, k = N/2) the tilt is s = 1, pi1 = pi2 = q, Lambda = 1, and
  U_N(N/2) = q e^{-x} (I_0(x) + I_1(x)),  x = (N-2) p q.
Let q_U solve 2 q e^{-x}(I_0 + I_1)(x) = p^{N-1} (U at the centre = P_N(0)), and let q_N = 1 - p_N be the
exact crossing (Paper A, Theorem thm:root). Paper A's Bessel root has u_B/u_N = 0.9761, 0.9924,
0.99769 at N = 100, 400, 1600.

P13. |q_U/q_N - 1| <= 0.2 |u_B/u_N - 1| at N = 100, 400, 1600, that is
     |q_U/q_N - 1| < 4.8e-3, 1.5e-3, 4.6e-4. Pencil: the root shift is about eps/log N with
     eps about -3/(8(N/2-1)) or smaller, so roughly 1e-3, 2e-4, 5e-5.
P14. p_N from the exact bisection reproduces Paper A's table: p_100 = 0.96496633, p_400 = 0.98812464
     (8 digits).
Methods: q_N by bisection on the exact P_N(N/2) - P_N(0) (run-count formula in 50-digit Decimal) and
compared with Paper A's table; q_U by bisection twice (series Bessel and trapezoid Bessel).
Runtime: each P_N(N/2) in Decimal costs N/2 terms; 60 bisection steps at N = 1600 is about 5e4
Decimal terms, a few seconds.

## Results of run 3 (verbatim, data/uniform-llt-verification-run3.txt)

```
N=100: p_N = 0.9649663263; q_U/q_N - 1 = -1.477e-03 (trapezoid: -1.477e-03); u_B/u_N = 0.97606 (trapezoid: 0.97606); ratio of relative errors = 0.062
N=400: p_N = 0.9881246429; q_U/q_N - 1 = -3.083e-04 (trapezoid: -3.083e-04); u_B/u_N = 0.99239 (trapezoid: 0.99239); ratio of relative errors = 0.041
N=1600: p_N = 0.9962346137; q_U/q_N - 1 = -6.469e-05 (trapezoid: -6.469e-05); u_B/u_N = 0.99769 (trapezoid: 0.99769); ratio of relative errors = 0.028
elapsed 0.9 s
```

Verdicts:
- P13 CONFIRMED. |q_U/q_N - 1| = 1.48e-3, 3.08e-4, 6.47e-5 at N = 100, 400, 1600, below the
  registered caps 4.8e-3, 1.5e-3, 4.6e-4 and close to the pencil values 1e-3, 2e-4, 5e-5.
  Compared with Paper A's u_B the error is 16, 24 and 36 times smaller (ratios 0.062, 0.041, 0.028).
  Empirically N log N |q_U/q_N - 1| = 0.68, 0.74, 0.76, which fits q_U/q_N - 1 ~ -(3/4)/(N log N).
- P14 CONFIRMED. p_100 = 0.9649663263 and p_400 = 0.9881246429 round to Paper A's table entries
  0.96496633 and 0.98812464; u_B/u_N reproduces 0.97606 (0.9761), 0.99239 (0.9924), 0.99769.
  Series and trapezoid Bessel give identical roots to the digits shown.

No hypothesis in this file has been deleted. Refuted so far: the numeric window of P12.

## Post-hoc descriptive numbers (computed after runs 1-3, not predictions)

Computed on 2026-09-26 while checking the note; recorded here so that every number in the note has a
source. None of these was pre-registered.
- Over the 217 sampled points of run 2: E_int/|err_U| ranges 1.35 to 8.68e4 (1.35 to 45.9 when
  q >= 0.1); E/|err_U| ranges 18.5 to 4.88e5. The large ratios occur in the telegraph regime.
- R(0.1) = 2/(sqrt(0.2 pi) e^{-0.1}(I_0 + I_1)(0.1)) = 2.649237908626 (series Bessel) and
  2.649237908626 (trapezoid Bessel). Run 1 gives G/P = 1/(1 - 0.623) = 2.65 at N=1000, q=1e-4.
- Centre, telegraph regime: err_U = -3.9975e-8 (N=10, q=1e-4), -4.8639e-7 (N=100, q=1e-4),
  -4.9528e-8 (N=1000, q=1e-5), against -(N-2)q^2/2 = -4.0e-8, -4.9e-7, -4.99e-8.
- Corollary 5 at N = 10^4: q_N = 7.734266e-4 (Decimal bisection on S_N), eta = 0.17441, relative
  bound 0.02732; Paper A's cor:allbin-root-bound gives 4.879e-4 relative.

## Repair pass after the read-only audit (2026-09-26)

Post-hoc corrections to lines above (the lines themselves are left as they were):
- Lemma letters. This ledger was written before the note's lemmas were relettered. Ledger "lemma F"
  (phase bound F(pi,t) <= (128/(3 pi^3)) pi^2 t^3, the line "max F/(pi^2 t^3) = 0.4992") is the
  note's Lemma E. Ledger "lemma M" (1/rho <= 1+2/x and the two moment bounds) is the note's Lemma F.
  The "modulus lemma" (g - |psi| <= g min(1, 4 kappa^2 V)) is the note's Lemma D. pi1, pi2 here are
  r1, r2 in the note; err_U is epsilon in the note.
- The P9 verdict says "so the sharp constant in lemma F is 1/2". That overstates it. What is proved:
  the sharp constant c = sup F/(r^2 t^3) satisfies 1/2 <= c <= 128/(3 pi^3). The lower bound comes from
  F/(r^2 t^3) -> (3 - 2r)/6 as t -> 0 (note, Lemma E remark). c = 1/2 is a conjecture supported by the
  grid maximum 0.4992.
- The note had written "(4+256/3)(2+2 sqrt 3) <= 488.1" and "(4+128/3)(3+sqrt 3) <= 220.8". Both were
  rounded the wrong way (488.126 and 220.829). The final constants 22334, 221 and 5825 are unchanged.
  Pencil recheck: 488.126 + 21845.33 = 22333.46 <= 22334.

## Predictions for run 4 (written before run 4): where Corollary 5 stops being vacuous

Corollary 5 uses eta = 221 q_N + 5825 q_N^2 and needs eta < 1, that is q_N < q* := the positive root
of 5825 q^2 + 221 q - 1 = 0. Pencil: q* = (-221 + sqrt(72141))/11650 = 0.0040851. For even N, the
equivalence eta < 1 <=> q_N < q* <=> u_N < u* := q*/(1-q*) <=> S_N(u*) > 1 holds because S_N (the
centre polynomial, positive coefficients) is increasing and has one root of S_N = 1 (Paper A,
thm:root). The same condition is equivalent to P_N(N/2) > P_N(0) at q = q*.

P15. q* = 0.0040851 +- 1e-7.
P16. Let N* be the smallest even N with eta < 1. Then N* is in [1420, 1480]. The sign pattern is
     monotone on the scanned range: eta >= 1 for every even 4 <= N < N*, and eta < 1 for every even
     N* <= N <= 2000. Method 1 (sign of S_N(u*) - 1, integer coefficients, 50-digit Decimal Horner)
     and method 2 (sign of P_N(N/2) - P_N(0) at q = q*, one float run of the recursion eq:dp up to
     N = 2000) disagree at 0 values of N.
P17. eta(1000) in [1.40, 1.44], eta(1400) in [1.02, 1.05], eta(1500) in [0.96, 0.98],
     eta(1600) = 0.9147 +- 0.001. Relative bound eta/((1-eta)(N-1) q_N) at N = 1600 is in
     [1.75, 1.81]. At N = N* it exceeds 10.
     Methods: q_N by Decimal bisection on S_N(u) = 1 (the run-3 routine exact_uN), then certified
     independently by a sign change of P_N(N/2) - P_N(0) from the float recursion eq:dp at
     q_N (1 - 1e-7) and q_N (1 + 1e-7).
P18. Bins 1 and N-1 in closed form: P_N(1) = P_N(N-1) = q p^{N-2} + (1/2)(N-2) q^2 p^{N-3} for N >= 2
     (from Theorem 1 with n1 = 0). Exact Fraction check against the recursion eq:dp for 2 <= N <= 40
     and q in {1/2, 1/3, 1/7, 2/11, 9/10}: 0 mismatches.

Runtime estimate: method 1 scan costs sum over even N <= 2000 of N Decimal multiply-adds (about 1e6)
plus the binomial coefficients, roughly 10-30 s. Method 2 is one recursion to N = 2000 (about 4e6 float
updates, a few seconds). P17 needs 6 Decimal bisections (about 1e6 operations) and 12 float recursions
at N <= 1600 (about 3e7 updates, under a minute). P18 takes under 5 s. Total under 2 minutes.

## Results of run 4 (verify_uniform_llt_cor5.py, verbatim, data/uniform-llt-verification-run4.txt)

```
P15 q* = 0.004085044359 (closed form, Decimal) ; 0.004085044359 (bisection, float)
P16 even 4<=N<=2000: N* (smallest even N with eta<1) = 1454; sign pattern monotone = True; method1/method2 disagreements = 0 [] (method 1 26.6 s, method 2 0.3 s)
P17 N=1000: q_N = 5.5903511670e-03; eta = 1.41751; recursion sign change across q_N(1-+1e-7): True; relative bound: none (eta >= 1)
P17 N=1400: q_N = 4.2150288651e-03; eta = 1.03501; recursion sign change across q_N(1-+1e-7): True; relative bound: none (eta >= 1)
P17 N=1452: q_N = 4.0873115306e-03; eta = 1.00061; recursion sign change across q_N(1-+1e-7): True; relative bound: none (eta >= 1)
P17 N=1454: q_N = 4.0825652351e-03; eta = 0.99933; recursion sign change across q_N(1-+1e-7): True; relative bound eta/((1-eta)(N-1)q_N) = 253.0149
P17 N=1500: q_N = 3.9765808721e-03; eta = 0.97094; recursion sign change across q_N(1-+1e-7): True; relative bound eta/((1-eta)(N-1)q_N) = 5.6044
P17 N=1600: q_N = 3.7653862984e-03; eta = 0.91474; recursion sign change across q_N(1-+1e-7): True; relative bound eta/((1-eta)(N-1)q_N) = 1.7819
P18 P_N(1)=P_N(N-1) closed form vs recursion in Fractions: 390 cases, mismatches = 0
elapsed 29.9 s
```

Verdicts:
- P15 CONFIRMED. q* = 0.004085044359 (closed form in Decimal and float bisection agree to 12 digits),
  inside 0.0040851 +- 1e-7.
- P16 CONFIRMED. N* = 1454, inside [1420, 1480]. On every even 4 <= N <= 2000 the sign pattern is
  monotone (eta >= 1 below 1454, eta < 1 from 1454 to 2000), and the two methods disagree at 0 values
  of N. Only this range was checked; for N > 2000 we do not claim monotonicity from this run.
- P17 CONFIRMED. eta = 1.41751 (N=1000), 1.03501 (N=1400), 0.97094 (N=1500), 0.91474 (N=1600), all in
  their windows. Also eta = 1.00061 at N = 1452 and 0.99933 at N = 1454. Each q_N from the Decimal
  bisection is bracketed to relative 1e-7 by a sign change of the float recursion. Relative bound at
  N = 1600: 1.7819 (window [1.75, 1.81]). At N* = 1454: 253.0 (> 10). At N = 1500: 5.60.
- P18 CONFIRMED. 390 exact cases, 0 mismatches.

No hypothesis in this file has been deleted. Refuted so far: the numeric window of P12 (run 2).
