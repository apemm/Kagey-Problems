# Ledger B-crossover: the dropped factor in thm:simplex-boundary-crossover

Paper B, frontier_boundary.tex, Theorem thm:simplex-boundary-crossover (coordinates of order
N/(log N)^2). Script: verify_crossover_factor.py. Output: data/crossover_factor_output.txt.
Note: scratchpad research131/B_crossover.md.

Notation as in the theorem: r large counts n_i with sum M, l rare counts a_j, N = M + sum a_j,
L = log N, beta_i = n_i/M, rho_j = a_j L^2/N, A = sum sqrt(beta_i), g = A^2 - 1, K = r + l - 1,
H = (r-1)/2 + 2l, u = odds r/p (Paper B), z = N u, s = sum_j a_j / N, x_j = A^2 a_j z^2/N
(the Phi arguments in the theorem). Paper B's z is the shared-notation T up to a factor
1 + O(z/N) (T = N times the switching probability to one other state, and u = r/p = r/(1-(d-1)r)).
Profile P0 = right side of eq. (simplex-boundary-profile) without the error factor.

Nothing below was computed before the entry dated 2026-09-26 (registration) was written, except
the five ratios quoted in the remark after the proof (1.05; 0.36, 0.53, 0.63, 0.70), which are
prior data from the paper, and the 2026-09-25 observation that exp(-g sum_j a_j z/N) alone makes
rho = 1 worse.

## 2026-09-26. Registration (before any exact S was computed in this task)

### Derivation done by hand before registering (to be written up in the note)

Write the exact ratio with the uniform majorant, use Bessel asymptotics for the r large
coordinates, and set w = sqrt(t), w0 = A sqrt(Y), Y = M v, v = u/(1-u). The integrand is
exp(A^2 Y - (w-w0)^2) h(w) with h(w) = w^p prod_j Phi(a_j v w^2) prod_i (1 - 3/(16 sqrt(beta_i Y) w)),
p = r/2 + 1 + 2l = H + 3/2. The Gaussian average of h is h(w0)(1 + h''(w0)/(4 h(w0)) + O(Y^-2)).
Expanding Phi as its power series, h''/h at w0 equals E[Q(Q-1)]/w0^2, where Q = p + 2 sum_j J_j and
J_j are independent with P(J_j = m) proportional to xi_j^m/(m!(m+1)!), xi_j = a_j v w0^2.
Using E[J(J+1)] = xi, write psi(x) = E[J] = x Phi'(x)/Phi(x) = sqrt(x) I_2(2 sqrt x)/I_1(2 sqrt x).
Then E[Q(Q-1)] = p^2 - p + 4 sum xi_j + 4H sum psi(xi_j) + 8 sum_{i<j} psi(xi_i) psi(xi_j).
Replacing M by N gives the factor exp(-A^2 z s); the term 4 sum xi_j/(4 A^2 Y) gives exp(+z s).
Together they give exp(-g z s): this is the factor tried on 2026-09-25. The rest of the same
order is new.

Claim C1 (complete first-order correction; to be proved for fixed R):
  log S(z/N) = log P0(z) + E1/z + kappa z^2/N + O_R(L^-2 + L/N), where
  E1 = -(g/A^2) sum_j x_j + (H/A^2) sum_j psi(x_j) + (2/A^2) sum_{i<j} psi(x_i) psi(x_j) + C0,
  C0 = (p^2 - p)/(4A^2) - (3/(16A)) sum_i beta_i^(-1/2),
  kappa = A^2 (1 - k/2) - 1/2, k = r + l.
  Note -(g/A^2) x_j / z = -g a_j z/N, so the first term of E1/z is exactly the 09-25 factor.
  Sanity check done by hand before registering: for l = 0 and balanced beta, C0 = -(k-1)/8,
  which is the known coefficient in Lemma lem:simplex-laplace. (Consistent.)

Claim C2 (M-form): the version with Y = Mv kept exactly,
  PM1 = D_r A^(2l) Y^H M^(-K) e^(A^2 Y) (1-u)^(N-1) prod_j Phi(xi_j) exp(Theta/Y) exp(-(k/2) A^2 Y v),
  xi_j = A^2 a_j Y^2/M, Theta = (1/A^2) sum xi_j + (H/A^2) sum psi(xi_j)
  + (2/A^2) sum_{i<j} psi psi + C0,
  agrees with C1 to first order but has no s*psi(x) ~ rho^(3/2)/L^2 terms, so it should be
  numerically much better at rho = 8 and moderate N.

### Predictions (numbers from hand evaluation of the formulas, r = 2 equal large counts, l = 1)

Constants: A^2 = 2, g = 1, H = 5/2, p = 4, K = 2, k = 3, C0 = 12/8 - 3/8 = 1.125, kappa = -1.5.
At z = L: x = A^2 rho = 2 rho. By hand: psi(2) = 0.7756, psi(16) = 3.277.
  E1(rho=1) = -1 + 1.25*0.7756 + 1.125 = 1.0945.
  E1(rho=8) = -8 + 1.25*3.277 + 1.125 = -2.779.

R1. Recomputed exact S/P0 at the remark's five points reproduces 1.05; 0.36, 0.53, 0.63, 0.70
    to within +-0.01, with counts a = round(rho N/L^2), n_1 = floor((N-a)/2), n_2 = N - a - n_1,
    and the actual rho = a L^2/N used in the profile. Kill: any point off by more than 0.01 under
    every reasonable rounding convention.

R2. (Main test of C1.) d0(N) = L log(S/P0) tends to E1(x): for rho = 1 the limit is 1.0945, for
    rho = 8 it is -2.779 (hand values; the script value of E1 replaces these if they differ in the
    4th digit, which would be a hand-arithmetic slip, and will be recorded). Operational test:
    d2(N) = L^2 log(S/(P0 exp(E1/z + kappa z^2/N))) stays bounded along N = 10^4, ..., 10^16:
    the values at N = 10^8, 10^12 and 10^16 differ by less than a factor 2 from each other,
    whereas L^2 log(S/P0) grows like L. Kill: d2 grows roughly linearly in L (meaning a missed
    first-order term), or d0 - E1 does not shrink roughly like 1/L (the ratio
    (d0 - E1)(10^16)/(d0 - E1)(10^8) should be 0.5 +- 0.2).

R3. The 09-25 factor alone: S/(P0 exp(-g s z)) at rho = 1, N = 2000 is further from 1 than 1.05
    (about 1.05*exp(2/7.6) = 1.37). Kill: it comes out closer to 1 than 1.05.

R4. Remark points with the first-order N-form PN1 = P0 exp(E1/z + kappa z^2/N):
    predicted S/PN1 = 0.95 +- 0.04 at (rho=1, N=2e3), and at rho = 8
    0.54, 0.71, 0.79, 0.85 (each +- 0.06) at N = 2e3, 2e4, 2e5, 2e6.
    Reason: the N-form keeps second-order terms of size s*psi(x) + (K-H)s, about -30/L^2 at
    rho = 8, so L^2 log(S/PN1) should be roughly constant, about -35 +- 10, on these four points.

R5. M-form PM1: S/PM1 closer to 1 than S/PN1 at all four rho = 8 points; predicted in
    [0.80, 1.20] at N = 2e3 and in [0.95, 1.05] at N = 2e6; at rho = 1, N = 2e3 in [0.93, 1.03].
    Kill: PM1 worse than PN1 at rho = 8, N = 2e6.

R6. Cross term check (l = 2, r = 2 equal, rho = (1, 3)): d0(N) tends to E1 including
    (2/A^2) psi(x_1) psi(x_2); the same boundedness test as R2 applies. And r = 3 with
    beta = (1,2,3)/6, l = 1, rho = 2: same test (checks C0's beta dependence and D_r).
    Kill: d2 growing like L in either case.

R7. Using z = 2L (near the crossing, c = K/g = 2) instead of z = L for rho = 1, 8: same limits
    with x = A^2 rho (z/L)^2 = 8 rho; the boundedness test of R2 passes.

R8. Roots: the root z_N of S = 1 differs from the root of the corrected profile PN1 (resp. PM1)
    by O(L^-2); predicted |z_N - z(PM1)| < 0.05 at N = 10^6 for rho = 1 and < 0.2 for rho = 8,
    both smaller than |z_N - (theorem's eq. simplex-boundary-root)|.

Methods for exact S (every number with at least two):
  (A) proper-run formula sum_j W_n(j) u^j with proper-word counts from a layer-by-layer DP
      (exact integer counts), N <= 10^8;
  (B) refresh integral (1-u)^(N-1)/v int_0^inf e^-t prod B_{n_i}(vt) dt by trapezoidal quadrature
      in double precision at two step sizes;
  (C) positive refresh sum (1-u)^(N-1) sum_M M! v^(M-1) [y^M] prod_i sum_m C(n_i-1,m-1) y^m/m!,
      Decimal with 60 digits at two cutoffs.
  Brute-force enumeration of all words for N <= 10 checks (A) and (C) exactly.
Runtime estimate: (C) and (B) under 2 s per case; (A) under 30 s per case at z <= 20; about
  40 cases in total, so under 10 minutes. Nothing longer will be started.

### 2026-09-26, addendum to the registration (still before any exact S was computed)

Ran `python -B verify_crossover_factor.py predict` (formula evaluation only). Output verbatim:

```
N=2000 counts=(982, 983, 35) rho_actual=1.0110 x=2.0221 psi(x)=0.7825 E1=1.0921 C0=1.1250 kappa=-1.5000
    PN1/P0=1.1545 PN1k/P0=1.1056 PM1/P0=1.1056 Pold/P0=0.8755
N=2000 counts=(861, 862, 277) rho_actual=8.0017 x=16.0033 psi(x)=3.2774 E1=-2.7799 C0=1.1250 kappa=-1.5000
    PN1/P0=0.6937 PN1k/P0=0.6643 PM1/P0=0.4270 Pold/P0=0.3490
N=20000 counts=(9184, 9185, 1631) rho_actual=7.9983 x=15.9967 psi(x)=3.2766 E1=-2.7776 C0=1.1250 kappa=-1.5000
    PN1/P0=0.7554 PN1k/P0=0.7499 PM1/P0=0.5642 Pold/P0=0.4459
N=200000 counts=(94630, 94631, 10739) rho_actual=7.9999 x=15.9998 psi(x)=3.2770 E1=-2.7787 C0=1.1250 kappa=-1.5000
    PN1/P0=0.7964 PN1k/P0=0.7955 PM1/P0=0.6564 Pold/P0=0.5192
N=2000000 counts=(961995, 961996, 76009) rho_actual=8.0000 x=16.0000 psi(x)=3.2770 E1=-2.7787 C0=1.1250 kappa=-1.5000
    PN1/P0=0.8257 PN1k/P0=0.8256 PM1/P0=0.7196 Pold/P0=0.5761
limit E1 (r=2 equal, l=1, z=L, x=2rho=2): 1.094544; z=2L (x=8rho): -0.225547
limit E1 (r=2 equal, l=1, z=L, x=2rho=16): -2.778753; z=2L (x=8rho): -21.796852
```

Hand values of E1 confirmed (1.0945 and -2.779). Sharpened predictions, obtained by dividing the
remark's exact/P0 values by the formula ratios above (so they assume R1 holds):
  S/PN1k at rho = 8: 0.54, 0.71, 0.79, 0.85 (+-0.03); L^2 log(S/PN1k) about -35 (+-8) at all four.
  S/PM1  at rho = 8: 0.84, 0.94, 0.96, 0.97 (+-0.03); L^2 log(S/PM1) between -12 and -4 at all four.
  S/PN1k = S/PM1 = 0.95 +- 0.02 at rho = 1, N = 2000.
  S/Pold at rho = 1, N = 2000: 1.05/0.8755 = 1.20 (R3: worse than 1.05). At rho = 8 Pold alone
  would give 1.03, 1.19, 1.21, 1.22 (it overcorrects at rho = 8 for N >= 2e4).
z = 2L, rho = 8 has x = 64 and E1/z about -1.4 at N = 2000; the expansion is not expected to be
useful there for N < 10^8. Registered expectation: the boundedness test R7 still passes by
N = 10^16, but d2 there may be large (|d2| up to 300) because the second-order constant grows
roughly like x^(3/2).

## 2026-09-26. Results of the first full run (verbatim numbers from data/crossover_factor_output.txt)

First run had a bug in method (A) (missing factor u^(k-1)); caught because (A) disagreed with
(B) and (C) by 11.1 = 2 log(1/u) in log S; fixed before any number was recorded. After the fix,
(A), (B), (C) agree to 3e-14 in log S at every point where (A) was run; (B) and (C) agree to
2e-14 at every point; brute force (155 count vectors) exact.

R1 CONFIRMED (with a note on rounding). S/P0 at (rho=1, N=2e3): 1.0445 with a = round(rho N/L^2)
  = 35, 1.0467 with a = 34 = floor(rho N/L^2), 1.0423 with a = 36. The remark's 1.05 matches the
  floor convention (1.0467); with round() it would print as 1.04. rho = 8: 0.3596 (a=277),
  0.3617 (a=276 = floor); 0.5260/0.5263; 0.6297; 0.6991. All within 0.01 of 0.36, 0.53, 0.63, 0.70.
R2 CONFIRMED. d0 - E1 = -0.1402 (1e8) -> -0.0719 (1e16) for rho = 1 (ratio 0.513) and
  -1.9158 -> -0.9756 for rho = 8 (ratio 0.509). d2 = L^2 log(S/PN1k): rho = 1: -2.58, -2.625,
  -2.648 at 1e8, 1e12, 1e16; rho = 8: -35.29, -35.71, -35.94. Bounded, not growing like L.
R3 CONFIRMED. S/Pold = 1.1931 at rho = 1, N = 2e3 (predicted 1.20). At rho = 8: 1.0304, 1.1795,
  1.2127, 1.2134 (predicted 1.03, 1.19, 1.21, 1.22).
R4 CONFIRMED. S/PN1k = 0.9448 at rho = 1 (pred. 0.95 +- 0.02); rho = 8: 0.5413, 0.7014, 0.7915,
  0.8468 (pred. 0.54, 0.71, 0.79, 0.85 +- 0.03).
R5 CONFIRMED. S/PM1 = 0.9448 (rho = 1); rho = 8: 0.8422, 0.9322, 0.9592, 0.9715
  (pred. 0.84, 0.94, 0.96, 0.97 +- 0.03). PM1 beats PN1k at all four rho = 8 points.
  z^2 log(S/PM1) at rho = 8 on 1e3..1e16: -11.9, -7.4, -6.3, -6.1, ..., -6.28 (pred. -12..-4:
  the N = 2e3 value -9.9 is inside; 1e3 is -11.9, just inside).
R6 CONFIRMED. l = 2, rho = (1,3): d0 - E1 = -1.3453 (1e8) -> -0.6965 (1e16), ratio 0.518;
  d2 = -24.78, -25.35, -25.66 (fits -26.5 + 32/L). r = 3, beta = (1,2,3)/6: d2 = -4.86, -4.93,
  -4.96. The cross term (2/A^2) psi psi and C0's beta dependence are right.
R7 CONFIRMED after correcting the diagnostic. The first run printed d0 = L log(S/P0) and compared
  it with E1, which is wrong for z = 2L (the limit of L log(S/P0) is E1 L/z). Rescaled to
  d0 = z log(S/P0): z = 2L, rho = 1: d2 = -3.46, -3.48, -3.50 (1e8, 1e12, 1e16) in L^2 units
  (first run); rho = 8 (x = 64): -66.7, -67.0, -67.1. Bounded. |d2| < 300 as registered.
R8 CONFIRMED. |z_N - root(PM1)| at N = 1e6: 0.0047 (rho = 1, pred. < 0.05), 0.0197 (rho = 8,
  pred. < 0.2). Theorem's explicit root formula eq. (simplex-boundary-root): errors 2.45 and 8.40.

SURPRISE (not registered): the explicit root formula eq. (simplex-boundary-root) is very poor at
  all tested N. z_N vs formula: rho = 1: 10.31 vs 7.22 (1e4), 17.86 vs 15.41 (1e6), 42.85 vs 41.31
  (1e12); rho = 8: 8.46 vs -1.61 (1e4), 14.99 vs 6.58 (1e6), 38.11 vs 32.48 (1e12). Solving the
  uncorrected profile equation P0 = 1 instead gives errors 0.035, 0.028, 0.009 (rho = 1) and 0.31,
  0.27, 0.21 (rho = 8). The loss is in the expansion of the root around z = cL, not in the profile:
  at these N the actual z_N/L is 1.1 to 1.55, far from c = 2, and log Phi(A^2 rho (z/L)^2) is
  evaluated at c instead of z_N/L.

## 2026-09-26. Registration for an R-dependence scan (before running it)

Second-order constants at N = 10^12, z = L, r = 2 equal, l = 1, rho in {0.25, 0.5, 1, 2, 4, 8, 16,
32}: c2N = z^2 log(S/PN1k), c2M = z^2 log(S/PM1).
Heuristic (derived before the scan): z^2 (log PM1 - log PN1k) is about -rho (H - K + psi(A^2 rho))
  = -rho (0.5 + psi(2 rho)), from (1-s)^(H-K) and Phi(x(1-s))/Phi(x).
Predictions: (a) c2N - c2M within 15% of -rho (0.5 + psi(2 rho)) for rho >= 1;
  (b) c2M roughly linear, c2M = -(0.7 + 0.7 rho) within 30% for rho <= 32;
  (c) hence c2N grows like rho^(3/2) (about -1.4 rho^(3/2) for large rho).
Kill: (a) off by more than 15% at some rho >= 1; (b) c2M(32) outside [-30, -16].

### Results of the R-dependence scan (N = 1e12, z = L), verbatim

```
rho     E1(x)      c2N        c2M      c2N-c2M     heur
0.25     1.1643     -1.050    -0.878     -0.173    -0.183
0.5      1.1664     -1.489    -1.044     -0.445    -0.467
1        1.0945     -2.625    -1.396     -1.228    -1.276
2        0.7701     -5.637    -2.117     -3.520    -3.632
4       -0.2255    -13.718    -3.524    -10.195   -10.478
8       -2.7788    -35.705    -6.214    -29.491   -30.216
16      -8.7186    -96.405   -11.374    -85.031   -86.802
32     -21.7969   -266.162   -21.416   -244.746  -248.401
```
(a) CONFIRMED: c2N - c2M within 4% of -rho(0.5 + psi(2 rho)) for every rho >= 1 (1.5% at 32).
(b) CONFIRMED: c2M is close to linear, about -(0.7 + 0.65 rho); c2M(32) = -21.4 is in [-30, -16].
(c) CONFIRMED: c2N(32) = -266, about -1.47 rho^(3/2).
Side observation: the constants depend on (rho, z) only through x = A^2 rho (z/L)^2: z = 2L with
rho = 8 (x = 64) gives z^2 log(S/PN1k) = -267.8 and z^2 log(S/PM1) = -21.8 at 1e12, against
-266.2 and -21.4 for z = L, rho = 32 (also x = 64).
Correction to the R7 entry above: those d2 values were in L^2 units (first run). In z^2 units the
rerun gives, at 1e8/1e12/1e16: rho = 1: -13.83, -13.93, -13.99; rho = 8: -266.8, -267.8, -268.5.
Still bounded; |d2| < 300 holds, narrowly.

## 2026-09-26. Registration: refined Laguerre-Bessel lemma and Bessel-law moments (before checking)

Claim L1 (proved by hand before checking): for every integer n >= 1 and w > 0,
  |B_n(w)/(w Phi(n w)) - (1 - w/2)| <= (3/4) w^2.
Claim L2: for the law P(J=m) proportional to x^m/(m!(m+1)!): E[J(J+1)] = x and
  E[J(J-1) J(J+1)] = x^2 exactly.
Prediction: both hold at n in {1,2,3,5,10,100,10^4}, w in {1e-4, 1e-2, 0.1, 0.5, 1, 2}, and
  x in {0.01, 1, 16, 64} to 50 digits; the ratio |B/(w Phi) - 1 + w/2| / w^2 stays below 0.75 and
  tends to a limit near 1/8 - 1/(6n)-ish as w -> 0 (not a registered number; only the bound is).
Kill: any violation of the bound.
Also registered: S/PMa (M-form without the majorant factor e^{-k A^2 Y v/2}) at the five remark
  points equals S/PM1 * exp(-k A^2 Y v/2), predicted about 0.88 (rho = 1, 2e3) and 0.78, 0.92,
  0.957, 0.971 (rho = 8).

### Results (2026-09-26), verbatim from the final run

L1 CONFIRMED: |B_n(w)/(w Phi(nw)) - 1 + w/2| / w^2 <= 0.75 at all 42 points; largest value
  0.16666 (n = 1, w -> 0, where the exact limit is 1/6 since 1/Phi(w) = 1 - w/2 + w^2/6 + ...).
L2 CONFIRMED: E[J(J+1)] = x and E[J(J-1)J(J+1)] = x^2 to 50 digits at x = 0.01, 1, 16, 64.
PMa (M-form without the majorant factor): 0.8671 (rho = 1, 2e3); 0.7811, 0.9197, 0.9572, 0.9712
  (rho = 8). Predicted about 0.88; 0.78, 0.92, 0.957, 0.971. Confirmed except that 0.867 is
  0.013 below the rough 0.88 (no tolerance was registered for it).
Runtime note: one intermediate run spent 433 s in the L1 check because B_n(w) for n = 10^4 was
  summed with exact binomials at 60 digits; this had not been estimated beforehand. Rewritten
  with the term ratio; the full script now runs in about 31 s.

## Status at the end of 2026-09-26

- Complete first-order correction E1 (claim C1): PROVED (note B_crossover.md, Theorem B.2) for
  fixed R, with remainder O_R(L^-2 + L^2/N), and with the extra factor exp(kappa z^2/N) the
  remainder is O_R(L^-2 + L/N) (Proposition B.4). Numerically confirmed in 7 families (above).
- M-form (claim C2): PROVED (Theorem B.1), same remainder.
- R-dependence of the O(L^-2) constant: OPEN as a proof (the proof gives only O_R). Observed:
  about -(1 + 1.5 rho^(3/2)) for the N-form and -(0.7 + 0.65 rho) for the M-form at z = L, r = 2
  equal, l = 1; depends on (rho, z) through x = A^2 rho (z/L)^2. Heuristic explanation of the
  difference confirmed to 4%.
- Explicit root formula eq. (simplex-boundary-root): correct as an asymptotic statement but with
  large constants (about 13 log L/L at rho = 1, 45 log L/L at rho = 8). Implicit root through the
  corrected profile: PROVED error O_R(L^-2 + L^2/N) (Corollary B.3); numerically 0.005/0.02 at 1e6.

## 2026-09-26. Repair after the read-only audit (registration, before any new computation)

A read-only audit of the note (verdict: minor gaps) raised nine issues. Each was checked by hand
before this entry. Accepted: all nine, two with modifications (see below). Nothing above is
deleted; corrections to earlier entries are recorded here.

Correction to the "Results of the first full run" entry above. That entry says (A), (B), (C)
agree to 3e-14 in log S wherever (A) was run and (B), (C) agree to 2e-14. Read directly from the
|A-C| and |B-C| columns of data/crossover_factor_output.txt (final run), the maxima are
4.4e-14 (A vs C; k = 3 only, N <= 1e8; attained at r = 2 equal, l = 1, rho = 1, z = 2L, N = 1e8)
and 1.6e-14 (B vs C; all families, N <= 1e16). The 3e-14/2e-14 figures were from the first run,
before the z = 2L families were rescaled. The largest spread among the three methods at the
remark points (section 1 of the output) is 1.3e-14. For N > 1e8, and for every k = 4 family
(l = 2; r = 3), only (B) and (C) were run; both evaluate the positive refresh representation, which
(A) checks for k = 3 up to 1e8 and brute force checks for 3 letters N <= 10, 4 letters N <= 7.

Renames (no number changes): the constant C0 of claim C1 is renamed gamma_0 in the note (C_0 was
also the upper end of the z-range); p = H + 3/2 is renamed alpha; the random sum Q = p + 2 sum J_j
is replaced by the moment mu_q = E[(q + 2|J|)(q + 2|J| - 1)], |J| = sum_j J_j (W would clash with
Paper B's W_n(j)). The script keeps its internal names C0 and p.

Hand check of the audit's main mathematical point (done before registering). The note's claim
"E - C_0/z has leading behaviour -(g/A^2) sum x_j/z for large x_j" is false for l >= 2: the cross
term 2 sum_{i<j} psi(x_i) psi(x_j) is about 2 sum sqrt(x_i x_j), also linear. With equal x_j = x
the linear coefficient is l(l - 1 - g)/A^2 per 1/z. Corrected statement (to be proved in the note):
  z A^2 (E - gamma_0/z) = -g sum_j x_j + 2 sum_{i<j} sqrt(x_i x_j) + O(sum_j sqrt(x_j)),
and E - gamma_0/z = O((1+R)/L).

Modification of the audit's B.6 formula. The audit proposes that c2N - c2M tends to
-sum_j rho_j (z/L)^2 (H - K + psi(x_j)). Redoing steps (a) and (c) of the proof of B.2 to second
order: xi_j = x_j (1-s)(1-z/N)^(-2) with s = sum_i a_i/N the TOTAL rare fraction, so each
log Phi(xi_j) moves by -s psi(x_j), not -(a_j/N) psi(x_j). The claim to be proved is
  z^2 (log PM - log PN) = -(z/L)^2 (sum_i rho_i)(H - K + sum_j psi(x_j)) + O(L^-1 + L^4/N).
For l = 1 the two agree (this is the "heur" column of section 4 of the output).

### Predictions for the repair check (python -B verify_crossover_factor.py repair)

Two methods for psi: (a) the series x Phi'(x)/Phi(x) in 60-digit Decimal (the script's psi);
(b) the continued fraction I_2/I_1(t) = 1/(4/t + 1/(6/t + 1/(8/t + ...))), t = 2 sqrt x,
evaluated backward in Decimal at two depths, psi = sqrt(x) I_2/I_1. (b) rests on
I_{nu-1} - I_{nu+1} = (2 nu/t) I_nu, derived by hand from the series DLMF 10.25.2 by shifting the
summation index; no other citation.

X1 (counterexample, r = 2 equal so A^2 = 2, g = 1; l = 3 equal x; H = 13/2).
  zE - gamma_0 = (1/2)[-3x + (39/2) psi(x) + 6 psi(x)^2].
  By hand (psi(16) = 3.2770 from the output file; psi(64), psi(256) from
  psi = sqrt x - 3/4 + 3/(32 sqrt x) + 3/(64 x) + ..., derived by hand from DLMF 10.40.1 with
  a_k(1), a_k(2) for k <= 3):
    x = 16: +40.2 (+-0.3); x = 64: +133.0 (+-0.5); x = 256: +463.0 (+-1).
  First term -3x/2: -24, -96, -384 exactly. Methods (a) and (b) agree to 1e-30.
  Kill: any value <= 0, or outside the tolerance, or (a), (b) disagreeing beyond 1e-30.
X2 (B.6 formula, l = 2 family r = 2 equal, rho = (1, 3), z = L; H = 9/2, K = 3, x = (2, 6)).
  By hand: psi(2) = 0.7756 (ledger), psi(6) = 1.746 (+-0.01, asymptotic series).
  Proved-form limit -(1+3)(3/2 + psi(2) + psi(6)) = -16.09 (+-0.05);
  audit's per-j form -[1(3/2 + psi(2)) + 3(3/2 + psi(6))] = -12.01 (+-0.05).
  POST-HOC comparison, not blind: the output file already holds d2 - dM for this family
  (computed earlier today, B and C): -25.349 - (-9.854) = -15.495 at 1e12 and
  -25.659 - (-10.017) = -15.642 at 1e16. I read these values before deriving the formula but did
  not form the differences until after. Expectation: relative gap to the proved form < 5% at 1e16,
  gap ratio (1e16)/(1e12) in [0.6, 0.9] (O(1/L): L ratio 0.75); the per-j form off by > 20%.
  Kill: gap to the proved form > 10% at 1e16, or not shrinking.
X3 (reproduce the l = 1 "heur" column of section 4 with both psi methods to 1e-25).
Runtime estimate: under 1 s (about 20 psi evaluations).

### Results of the repair check (2026-09-26), verbatim from data/crossover_factor_repair_output.txt

Process note, recorded before the results. My first attempt to add the repair mode failed on a
string-match assertion (a shell quoting problem), so the script was unchanged, and the same
command line then ran `python -B verify_crossover_factor.py` without the mode argument, i.e. an
unplanned repeat of the full run (50.8 s, under the cap). It overwrote
data/crossover_factor_output.txt. Every number in that file is identical, by visual comparison
with the earlier printout of the same file (the computation is deterministic), to the values
recorded above; only the timing lines
changed ("0.2 s" -> "0.4 s" for the proper-word table, "total time 30.4 s" -> "50.8 s"). The
repair mode was then added (script unchanged otherwise) and run:

```
x        psi(a)                          psi(b,600)                      |a-b|    |b300-b600|
2        0.7756355884645123157209181571  0.7756355884645123157209181571  2.0e-60  0.0e+00
6        1.7491884113699127993583477393  1.7491884113699127993583477393  3.0e-59  0.0e+00
16       3.2769976414224821703331999175  3.2769976414224821703331999175  1.0e-59  0.0e+00
64       7.2625187670460041409332426299  7.2625187670460041409332426299  1.3e-58  0.0e+00
256      15.256050423251634731478951824  15.256050423251634731478951824  1.0e-58  0.0e+00
(x = 0.5, 1, 4, 8, 32 also agree to <= 3e-59)

X1. r = 2 equal (A^2 = 2, g = 1), l = 3 equal x, H = 13/2:
x      first term   zE-gamma_0 (a)   zE-gamma_0 (b)
16          -24.0          40.1669          40.1669
64          -96.0         133.0421         133.0421
256        -384.0         462.9877         462.9877

X2. l = 2, r = 2 equal, rho = (1, 3), z = L: H - K = 3/2, x = (2, 6)
    (a) -(sum rho)(H-K+sum psi) = -16.0993   per-j form -sum rho_j(H-K+psi_j) = -12.0232
    (b) -(sum rho)(H-K+sum psi) = -16.0993   per-j form -sum rho_j(H-K+psi_j) = -12.0232
    compare (full-run output, section 2, l = 2 family): d2 - dM = -15.495 (1e12), -15.642 (1e16)

X3. rho: 0.25 0.5 1 2 4 8 16 32 -> -0.1829 -0.4666 -1.2756 -3.6322 -10.4782 -30.2160 -86.8015
    -248.4006, both methods (agree to <= 4e-57)
```

X1 CONFIRMED: 40.1669, 133.0421, 462.9877 (registered 40.2 +- 0.3, 133.0 +- 0.5, 463.0 +- 1);
  (a) and (b) agree to 1.3e-58. The note's side claim in B.2 is refuted for l = 3 (the audit's
  +40, +133, +463 reproduced); the note is corrected.
X2 CONFIRMED (post hoc, see registration): proved form -16.0993 (registered -16.09 +- 0.05;
  psi(6) = 1.7492 against the hand value 1.746 +- 0.01). Gap to the data: 0.604 (1e12), 0.457
  (1e16); ratio 0.757 (registered [0.6, 0.9]); relative gap at 1e16 2.8% (registered < 5%).
  The audit's per-j form -12.0232 is 23% off at 1e16 (registered > 20%). So the l >= 2 version
  of B.6(a) must use the total sum_i rho_i, as derived.
X3 CONFIRMED: the "heur" column of section 4 is reproduced to its printed 3 decimals by both
  methods.
Runtime: 0.01 s.

## Status after the repair (2026-09-26; supersedes nothing above, adds to it)

- Claim C1 (E, now written with gamma_0 in place of C0): PROVED, unchanged. New side results in
  the note's Theorem B.2: |E| <= C_1 (1+R)/L (PROVED); for large x the leading part of
  z A^2 (E - gamma_0/z) is -g sum x_j + 2 sum_{i<j} sqrt(x_i x_j) (PROVED). The pre-repair side
  claim "leading behaviour -(g/A^2) sum x_j/z" is REFUTED for l >= 2 (X1) and removed.
- Claim C2 (M-form): PROVED, unchanged.
- Difference of the two second-order constants: PROVED (note, Proposition B.6(a)) as
  -(z/L)^2 (sum_i rho_i)(H - K + sum_j psi(x_j)) + O(L^-1 + L^4/N). Previously "heuristic".
- R-dependence of the M-form constant c2M (and of the O(L^-2) constants): still OPEN, numerical.
- Root statements: PROVED with the z-range fixed as c_0 = K/(2(r-1)), C_0 = K/eps, so they need
  no hypothesis beyond beta_i >= eps, rho_j <= R.
- No number from the earlier runs changed.
