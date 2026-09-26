# Problem 131 Paper C, topic C4 ledger (sticky HMM priors; endpoint-only Fisher information)

Predictions are appended before the computation that tests them; outcomes are appended verbatim below, never deleted.

## 2026-09-25 | C4-F1 and C4-F2: endpoint Fisher efficiency at the center crossing

Cells: binary walk of Paper A, N = 100 and N = 400, q = q_N = 1 - p_N with p_100 = 0.96496633, p_400 = 0.98812464 (Paper A, Table 1). So N q_N = 3.503367 and 4.750144.
Quantity: e_N(q) = I_K(q) / I_path(q), where I_K is the Fisher information about q in the bin index K alone and I_path = (N-1)/(pq) is that of the full path (J = number of switches is sufficient).
No efficiency number has been computed for any N before this entry.

- C4-F1 (program.md's claim, "about 1/(2 log N) at the crossing"): e_100 ~ 0.10857, e_400 ~ 0.08345.
  Kill condition: |e_N(q_N) * 2 log N - 1| > 0.25 at either size.
- C4-F2 (my leading-order prediction before any computation): e_N(q) ~ 1/(2 N q) as Nq -> infinity, with a relative correction of order 1/(Nq) that is NOT small at these sizes. Back-of-envelope (Gaussian occupation plus a Laplace-block fourth cumulant) gives a factor (1 - 4/(Nq) + ...), i.e. the leading term overestimates.
  Prediction: 0.3 <= e_N(q_N) * 2 N q_N <= 0.9 at both sizes, and the product is larger at N = 400 than at N = 100.
  Kill condition: the product falls outside [0.3, 0.9] at either size, or is not larger at N = 400.

### 2026-09-25 | C4-F3: refined prediction, registered after a symbolic derivation and before any exact efficiency computation

Derivation run (not a test of any cell): code/C4_continuum.py computes in closed form, for the telegraph limit (N -> oo, Nq = x fixed), the squared correlation rho2(x) between J and W^2 (W = (2K-N)/N). This is a rigorous lower bound for the continuum efficiency. Its polynomial part is 4(x-1)^2 / (x(8x^2-20x+17)) = 1/(2x) + 1/(4x^2) + 1/(16x^3) + O(x^-4). The fourth cumulant of W is -3/x^3 + ..., negative. So the sign I guessed in C4-F2 was wrong, and C4-F2 is expected to die. I leave it in place as registered.
Continuum values: 2x*rho2 = 1.1163 at x = 3.503367 and 1.0979 at x = 4.750144.

- C4-F3 prediction: e_100(q_100) in [0.145, 0.185] and e_400(q_400) in [0.110, 0.130]. The band allows O(x^2/N) discrete corrections and an O(x^-3) excess of the best predictor over the quadratic one. Also e_1600(q_1600) * 2 N q_1600 in [1.06, 1.12].
  Kill condition: any of the three values falls outside its band.
- Consequence for C4-F1: if C4-F3 holds, e_N * 2 log N is about 1.47 at N = 100 and about 1.38 at N = 400, so C4-F1 (program's 1/(2 log N)) would be killed. For C4-F2 the product e * 2Nq would be about 1.12, so C4-F2 would be killed as well.

### 2026-09-25 | Outcomes for C4-F1, C4-F2, C4-F3 (code/C4_fisher_cross.py; engine cross-checked against brute force, mpmath and finite differences)

Verbatim output:
```
N=100 p_N=0.964966326319 q_N=0.0350336736809 Nq=3.503367368  e=0.1886868010  e*2Nq=1.322078  e*2logN=1.737870  1/(2logN)=0.108574
    lower bounds: atom=0.108448 (closed 0.108448) quad=0.16641908 atom+quad=0.18795178 +X^4=0.1886660155
    continuum e_inf(Nq)=0.1840885379 (mass 1.0)  e_N/e_inf=1.024979
    mpmath engine e=0.188686801038674 (mass 1.0)
    finite-difference route e=0.188686801038674
N=400 p_N=0.988124642887 q_N=0.0118753571133 Nq=4.750142845  e=0.1268115422  e*2Nq=1.204746  e*2logN=1.519574  1/(2logN)=0.083452
    lower bounds: atom=0.041153 (closed 0.041153) quad=0.11714791 atom+quad=0.12567943 +X^4=0.1267566757
    continuum e_inf(Nq)=0.1255707627 (mass 1.0)  e_N/e_inf=1.009881
    mpmath engine e=0.126811542200034 (mass 1.0)
N=1600 p_N=0.996234613702 q_N=0.00376538629839 Nq=6.024618077  e=0.0943292332  e*2Nq=1.136595  e*2logN=1.391877  1/(2logN)=0.067771
    lower bounds: atom=0.014541 (closed 0.014541) quad=0.09007281 atom+quad=0.09314819 +X^4=0.0942516698
    continuum e_inf(Nq)=0.09400044125 (mass 1.0)  e_N/e_inf=1.003498
```
- C4-F1 KILLED. e * 2 log N = 1.738 (N = 100) and 1.520 (N = 400). At these sizes the program's 1/(2 log N) is too small by a factor of 1.5 to 1.7.
- C4-F2 KILLED. e * 2Nq = 1.322 and 1.205, outside [0.3, 0.9]. The correction is positive, not negative, and the product falls toward 1 from above.
- C4-F3 KILLED (partly). N = 400 lies inside its band (0.1268 in [0.110, 0.130]). N = 100 lies outside (0.1887 > 0.185), and so does N = 1600 (1.1366 > 1.12). Cause: the band left out the information carried by the two endpoint atoms, x e^{-x} to leading order. At the crossing this is 0.108 of the 0.189 at N = 100. It decays like (log N)^{3/2}/N, so it vanishes asymptotically but dominates the second-order term at practical N. Part of the gap at N = 100 is also the discrete correction e_N/e_inf - 1 = 2.5%.

## 2026-09-25 | C4-F4, C4-F5, C4-F6: efficiency away from the crossing (registered before computing)

- C4-F4 (continuum, large x): e_inf(x) = 1/(2x) + 1/(4x^2) + O(x^-3). This is the quadratic-predictor expansion; the atom term x e^{-x} is negligible here.
  Prediction: 2x e_inf(x) in [1.020, 1.035] at x = 20 and in [1.007, 1.013] at x = 50. Kill: outside either band.
- C4-F5 (fixed q, N -> oo): e_N(q) * 2(N-1)pq -> 1.
  Prediction: at q = 0.1, the product is in [0.95, 1.10] for N = 400 and in [0.98, 1.03] for N = 1600; at q = 0.3, N = 400, it is in [0.98, 1.05]. Kill: outside any band.
- C4-F6 (continuum, small x): e_inf(x) = 1 - x/2 + O(x^2), because given one or two switches the endpoint is uniform either way.
  Prediction: e_inf(0.01) in [0.9945, 0.9955] and e_inf(0.1) in [0.945, 0.96]. Kill: outside either band.

### 2026-09-25 | Outcomes for C4-F4, C4-F5, C4-F6 (code/C4_fisher_grid.py)

Verbatim (selected rows):
```
 x       e_inf(x)        2x*e_inf    atomLB=x/(e^x-1)
0.01    0.9950083335  0.019900   0.995008
0.1     0.9508351569  0.190167   0.950833
20      0.0256883130  1.027533   0.000000
50      0.0101036937  1.010369   0.000000
q=0.1 N=  400 x=Nq=   40.0 e=0.01408074  e*2(N-1)pq=1.011279  e*2Nq=1.126459
q=0.1 N= 1600 x=Nq=  160.0 e=0.00348390  e*2(N-1)pq=1.002735  e*2Nq=1.114847
q=0.3 N=  400 x=Nq=  120.0 e=0.00597517  e*2(N-1)pq=1.001319  e*2Nq=1.434041
```
- C4-F4 SURVIVES: 1.02753 lies in [1.020, 1.035] and 1.01037 in [1.007, 1.013]. The residual e_inf - rho2 is about 0.4/x^3 at both x (5.8e-5 at x = 20, 3.3e-6 at x = 50).
- C4-F5 SURVIVES: 1.01128, 1.00274 and 1.00132 all lie in their bands. At fixed q the correct normalization is 2(N-1)pq, not 2Nq; e * 2Nq tends to 1/p (1.111 at q = 0.1, 1.43 at q = 0.3).
- C4-F6 SURVIVES: 0.99501 and 0.95084 lie in their bands. The atom lower bound x/(e^x - 1) agrees with e_inf to 6 digits at x = 0.1.

## 2026-09-25 | C4-F7: crossing efficiency at N = 800 and N = 3200 (registered before computing)

Basis: continuum e_inf at x_N (x_N taken from Paper A's third-order expansion: x_800 ~ 5.39, x_3200 ~ 6.67), plus a discrete correction e_N/e_inf - 1 ~ 0.2 x^2/N (fitted by eye to the N = 100, 400, 1600 rows above).
- Prediction: e_800(q_800) * 2N q_800 in [1.15, 1.18]; e_3200(q_3200) * 2N q_3200 in [1.10, 1.13]; and e * 2Nq decreases along N = 50, 100, 200, 400, 800, 1600, 3200.
- Kill: either value outside its band, or the sequence is not monotone.

### 2026-09-25 | Outcome for C4-F7 (code/C4_fisher_table.py)

Verbatim:
```
 N     x_N=Nq_N     e_N           e*2Nq     e*2logN   rho2_N(closed) rho2(numeric) atom+quad   two-term   (e-two)*x^3  e_inf(x_N)   e/e_inf
   50   2.899798 0.2411670949 1.398671 1.886902  0.2087271978 0.2087271978 0.24070449 0.20215650    0.9512  0.23210222  1.039056
  100   3.503367 0.1886868010 1.322078 1.737870  0.1664190790 0.1664190790 0.18795178 0.16308878    1.1007  0.18408854  1.024979
  200   4.121965 0.1524153185 1.256501 1.615089  0.1376674047 0.1376674047 0.15144230 0.13601540    1.1486  0.15003061  1.015895
  400   4.750143 0.1268115422 1.204746 1.519574  0.1171479116 0.1171479116 0.12567943 0.11633966    1.1224  0.12557076  1.009881
  800   5.384896 0.1082310459 1.165626 1.446965  0.1018666754 0.1018666754 0.10703306 0.10147384    1.0551  0.10758947  1.005963
 1600   6.024618 0.0943292332 1.136595 1.391877  0.0900728061 0.0900728061 0.09314819 0.08988062    0.9728  0.09400044  1.003498
 3200   6.668423 0.0836089446 1.115080 1.349600  0.0806994396 0.0806994396 0.08250457 0.08060228    0.8916  0.08344185  1.002003
```
- C4-F7 SURVIVES: 1.1656 lies in [1.15, 1.18], 1.1151 in [1.10, 1.13], and the sequence decreases monotonically. The closed-form rho2_N agrees with the numerically computed quadratic R^2 to 10 digits, which checks the closed forms for Var X^2 and Cov(J, X^2).

## 2026-09-25 | C4-S1 to C4-S5: sticky-prior modal occupancy (registered before any DP run)

Model: d-state chain with P_N = (1-h) I + h K, h = c log(N)/N, K a switching kernel (zero diagonal), uniform initial law. Occupancy n = visit counts over N steps. "Modal face" = support of argmax_n P(n).
First-order theory (C4.md, Prop S2, assuming C1's Theorem 1): the modal face minimizes c(1 - rho(K_F)) + |F| - 1. Vertex for c < c_- = min_{|F|>=2} (|F|-1)/rho(K_F); full for c > c_+ = max_{F != [d]} (d-|F|)/(1-rho(K_F)).
Exact finite-N reduction used below (C4.md, Prop S4): for a symmetric pair {i,j} with K_ij = K_ji = k and equal exit rates, the pair center beats the vertex exactly when h k/(1-h) > u_N (Paper A). So c_-(N) = N u_N / ((k + u_N) log N), provided no third face intervenes.

- C4-S1 (K1: d = 3, K = [[0,.9,.1],[.9,0,.1],[.5,.5,0]]; N = 60, 120, 240, 480; first order c_- = 1.111, c_+ = 10):
  (a) as c increases over [0.2, 30] the modal face goes vertex {1} or {2}, then pair {1,2}, then full; {3}, {1,3} and {2,3} are never modal;
  (b) the vertex-to-pair switch occurs at c_-(N) = 0.8248, 0.8477, 0.8673, 0.8838 (within 1e-3);
  (c) the pair-to-full switch occurs at some c_+(N) in [4, 13].
  Kill: any of (a), (b), (c) fails at any N.
- C4-S2 (K2: uniform d = 3): no pair face is ever modal. The vertex-to-full jump occurs at c*(N) within 0.03 of Paper B's k = 3 expansion: 1.3036, 1.3905, 1.4581, 1.5101 for N = 60, 120, 240, 480.
  Kill: a pair face is modal at some c, or c* misses by more than 0.03.
- C4-S3 (K3: cyclic d = 3, K_{i,i+1} = 0.9, K_{i,i-1} = 0.1, a non-uniform kernel with every pair rho = 0.3 <= 1/2): direct vertex-to-full jump (no pair face modal), with c*(N) < c*_uniform(N) at each N.
  Kill: a pair face is modal at some c, or c* >= the uniform value.
- C4-S4 (K4: d = 4, two communities {1,2}, {3,4}, K_12 = K_21 = K_34 = K_43 = 0.8, the other off-diagonal entries 0.1; N = 40, 60, 80; first order c_- = 1.25, c_+ = 10, triples never): vertex, then a community pair, then full; no triple is ever modal; vertex-to-pair at c_-(N) = 0.9030, 0.9215, 0.9337 (within 1e-3).
  Kill: a triple or a cross-community pair is modal, or the vertex-to-pair switch misses by more than 1e-3.
- C4-S5 (random kernel, sticky HDP-HMM weak limit with d = 3 and beta uniform: rows of K independent, K_{j,.} ~ Dir(alpha/3, alpha/3) on the two off-diagonal entries; "direct jump" iff every pair has K_ij K_ji <= 1/4):
  P(direct jump) is in [0.20, 0.26] at alpha = 0.01 (limit 1/4), below 0.05 at alpha = 100, and decreasing over alpha = 0.01, 0.1, 1, 10, 100.
  Kill: any of the three fails (Monte Carlo, 10^6 draws, beyond 3 standard errors).

### 2026-09-25 | Outcomes for C4-S1 to C4-S3 at N = 60, 120, 240 (code/C4_sticky.py; the DP was checked against brute-force enumeration, error 1e-17)

Verbatim:
```
K1 N=60 logN=4.0943
   modal faces along grid: ((1,), (2,), (3,)) -> ((1, 2),) -> ((1, 2, 3),)
   switch at c = 0.82483: ((1,), (2,), (3,)) -> ((1, 2),)  (new modal comps e.g. [(30, 30, 0)])
   switch at c = 4.80385: ((1, 2),) -> ((1, 2, 3),)  (new modal comps e.g. [(28, 29, 3), (29, 28, 3)])
K1 N=120 logN=4.7875
   switch at c = 0.84773: ((1,), (2,), (3,)) -> ((1, 2),)  (new modal comps e.g. [(60, 60, 0)])
   switch at c = 5.34001: ((1, 2),) -> ((1, 2, 3),)  (new modal comps e.g. [(56, 57, 7), (57, 56, 7)])
K1 N=240 logN=5.4806
   switch at c = 0.86730: ((1,), (2,), (3,)) -> ((1, 2),)  (new modal comps e.g. [(120, 120, 0)])
   switch at c = 5.77933: ((1, 2),) -> ((1, 2, 3),)  (new modal comps e.g. [(112, 112, 16)])
K2 N=60   switch at c = 1.38322: ((1,), (2,), (3,)) -> ((1, 2, 3),)  (new modal comps e.g. [(20, 20, 20)])
K2 N=120  switch at c = 1.44217: ((1,), (2,), (3,)) -> ((1, 2, 3),)  (new modal comps e.g. [(40, 40, 40)])
K2 N=240  switch at c = 1.49058: ((1,), (2,), (3,)) -> ((1, 2, 3),)  (new modal comps e.g. [(80, 80, 80)])
K3 N=60   switch at c = 1.33839: ((1,), (2,), (3,)) -> ((1, 2, 3),)  (new modal comps e.g. [(20, 20, 20)])
K3 N=120  switch at c = 1.40357: ((1,), (2,), (3,)) -> ((1, 2, 3),)  (new modal comps e.g. [(40, 40, 40)])
K3 N=240  switch at c = 1.45662: ((1,), (2,), (3,)) -> ((1, 2, 3),)  (new modal comps e.g. [(80, 80, 80)])
```
- C4-S1(a) KILLED AS WORDED. The order vertex -> {1,2} -> full holds, and {1,3} and {2,3} are never modal. But vertex {3} IS co-modal in the vertex phase: with equal exit rates and a uniform start, every vertex has probability (1/3)(1-h)^{N-1}, an exact tie. My statement "{3} never modal" was wrong. The substantive content (which faces win, and in what order) holds.
- C4-S1(b) SURVIVES: 0.82483, 0.84773, 0.86730 against predicted 0.8248, 0.8477, 0.8673. This is the exact Paper A reduction.
- C4-S1(c) SURVIVES: 4.80, 5.34, 5.78 lie in [4, 13], increasing slowly toward the first-order value 10. At the switch, the modal full-face composition hugs the pair face: n_3/N = 0.050, 0.058, 0.067, against the stationary weight pi_3 = 1/11 = 0.091.
- C4-S2 KILLED (precision part): the jump is direct (no pair face modal), as predicted. But c* = 1.3832, 1.4422, 1.4906 misses the Paper B expansion values 1.3036, 1.3905, 1.4581 by 0.080, 0.052, 0.033, beyond the 0.03 tolerance. In Paper B units, N u* = 3.127 (N = 60) against the expansion's 2.929, and 4.229 (N = 240) against 4.133. The gaps shrink like (log L)^2/L^2, which is the stated error order of that expansion; my tolerance was too tight. The DP switch is by definition Paper B's exact face-center crossing, because the modal full-face composition at the switch is the balanced center (20,20,20) etc.
- C4-S3 SURVIVES: direct jump at c* = 1.3384, 1.4036, 1.4566, below the uniform-kernel values at each N.

### 2026-09-25 | Outcome for C4-S5 (code/C4_hdp.py, 10^6 draws per alpha)

Verbatim:
```
 alpha     P(direct)    s.e.      alpha*P(direct)
   0.01  0.24735   0.00043    0.0025
    0.1  0.22516   0.00042    0.0225
      1  0.11530   0.00032    0.1153
      3  0.05339   0.00022    0.1602
     10  0.01883   0.00014    0.1883
     30  0.00663   0.00008    0.1988
    100  0.00201   0.00004    0.2006
   1000  0.00021   0.00001    0.2090
```
- C4-S5 SURVIVES: 0.2474 lies in [0.20, 0.26], 0.0020 < 0.05, and the values decrease monotonically. Empirically P(direct) ~ 0.2/alpha for large alpha.

## 2026-09-25 | C4-G1: occupancy-only Fisher efficiency for the sticky d-state chain (registered before computing)

With equal exit rates the path law is an exponential family in log(h/(1-h)), and J = number of switches ~ Bin(N-1, h) is sufficient. So e_occ = Var(E[J | n]) / ((N-1)h(1-h)) exactly (Prop F1 carries over). Gaussian heuristic: n/N ~ N(pi, Sigma/x) in d-1 dimensions with x = N h, which gives e_occ ~ (d-1)/(2x) for any kernel.
- Prediction (d = 3, kernels K1 and K2 from C4-S1/S2, N = 240): the ratio R = e_occ * 2(N-1)h(1-h)/(d-1) lies in [1.0, 1.6] at x = 5 and in [1.0, 1.15] at x = 20. It is larger at x = 5 than at x = 20 for both kernels. Check: the d = 2 version of the same code reproduces the binary engine to 1e-12.
- Kill: R outside a band, or not decreasing from x = 5 to x = 20, for either kernel.

### 2026-09-25 | Outcome for C4-G1 (code/C4_sticky_fisher.py)

Verbatim:
```
d=2 check N=20 h=0.1: e_occ=0.3729275091262 binary engine=0.3729275091262 mass=1.00000000000000 E[J] ratio=1.00000000000000
d=2 check N=60 h=0.05: e_occ=0.2303560594686 binary engine=0.2303560594686 mass=1.00000000000000 E[J] ratio=1.00000000000000
K1 N=240 x=Nh=  2: e_occ=0.51183389  R=e*2(N-1)h(1-h)/(d-1)=1.01091
K1 N=240 x=Nh=  5: e_occ=0.23216552  R=e*2(N-1)h(1-h)/(d-1)=1.13191
K1 N=240 x=Nh= 10: e_occ=0.11966266  R=e*2(N-1)h(1-h)/(d-1)=1.14199
K1 N=240 x=Nh= 20: e_occ=0.06066614  R=e*2(N-1)h(1-h)/(d-1)=1.10758
K2 N=240 x=Nh=  2: e_occ=0.58966972  R=e*2(N-1)h(1-h)/(d-1)=1.16464
K2 N=240 x=Nh=  5: e_occ=0.27574734  R=e*2(N-1)h(1-h)/(d-1)=1.34439
K2 N=240 x=Nh= 10: e_occ=0.11924573  R=e*2(N-1)h(1-h)/(d-1)=1.13801
K2 N=240 x=Nh= 20: e_occ=0.05531242  R=e*2(N-1)h(1-h)/(d-1)=1.00984
```
- C4-G1 SURVIVES as worded: every R is in its band, and R(5) > R(20) for both kernels. Caveat: for K1, R is not monotone (1.132, 1.142, 1.108) and approaches 1 more slowly. State 3 has stationary weight 1/11 and is entered only about 0.09 x times, so its count is far from Gaussian at x = 20. The Gaussian heuristic needs x times the smallest stationary flux to be large, not just x.

### 2026-09-25 | Outcome for C4-S4 (code/C4_sticky.py K4 40 60 80)

Verbatim:
```
K4 N=40 logN=3.6889
   modal faces along grid: ((1,), (2,), (3,), (4,)) -> ((1, 2), (3, 4)) -> ((1, 2, 3, 4),)
   switch at c = 0.90306: ((1,), (2,), (3,), (4,)) -> ((1, 2), (3, 4))  (new modal comps e.g. [(0, 0, 20, 20), (20, 20, 0, 0)])
   switch at c = 5.31314: ((1, 2), (3, 4)) -> ((1, 2, 3, 4),)  (new modal comps e.g. [(10, 10, 10, 10)])
K4 N=60 logN=4.0943
   switch at c = 0.92148: ((1,), (2,), (3,), (4,)) -> ((1, 2), (3, 4))  (new modal comps e.g. [(0, 0, 30, 30), (30, 30, 0, 0)])
   switch at c = 5.65042: ((1, 2), (3, 4)) -> ((1, 2, 3, 4),)  (new modal comps e.g. [(15, 15, 15, 15)])
K4 N=80 logN=4.3820
   switch at c = 0.93369: ((1,), (2,), (3,), (4,)) -> ((1, 2), (3, 4))  (new modal comps e.g. [(0, 0, 40, 40), (40, 40, 0, 0)])
   switch at c = 5.86269: ((1, 2), (3, 4)) -> ((1, 2, 3, 4),)  (new modal comps e.g. [(20, 20, 20, 20)])
```
- C4-S4 SURVIVES: the order is vertex, then community pair, then full. No triple and no cross-community pair is ever modal. The vertex-to-pair switch comes at 0.90306, 0.92148, 0.93369 against predicted 0.9030, 0.9215, 0.9337. The pair-to-full switch (5.31, 5.65, 5.86) is still far below its first-order value 10.

### 2026-09-25 | Illustration only, no prediction tested: MAP versus face mass (code/C4_sticky_mass.py, K1, N = 240)

Verbatim (abridged):
```
K1 N=240 c=0.5: modal comps [(0, 0, 240), (0, 240, 0)], P(mode)=2.142e-02; face masses: vertex=6.4274e-02, pair12=4.6452e-01, pair13/23=9.2271e-02, full=3.7893e-01
K1 N=240 c=0.8: modal comps [(0, 0, 240), (0, 240, 0)], P(mode)=4.065e-03; face masses: vertex=1.2196e-02, pair12=4.2251e-01, pair13/23=3.4077e-02, full=5.3122e-01
K1 N=240 c=3.0: modal comps [(120, 120, 0)], P(mode)=1.695e-03; face masses: vertex=4.3034e-08, pair12=1.2894e-01, pair13/23=3.2564e-06, full=8.7106e-01
K1 N=240 c=8.0: modal comps [(111, 111, 18)], P(mode)=7.555e-04; face masses: vertex=1.1500e-21, pair12=8.1309e-03, pair13/23=2.0726e-16, full=9.9187e-01
```

### 2026-09-25 | Outcome for C4-S1 at N = 480 (code/C4_sticky.py K1 480)

Verbatim:
```
K1 N=480 logN=6.1738
   modal faces along grid: ((1,), (2,), (3,)) -> ((1, 2),) -> ((1, 2, 3),)
   switch at c = 0.88383: ((1,), (2,), (3,)) -> ((1, 2),)  (new modal comps e.g. [(240, 240, 0)])
   switch at c = 6.13919: ((1, 2),) -> ((1, 2, 3),)  (new modal comps e.g. [(223, 224, 33), (224, 223, 33)])
```
- (b) SURVIVES (0.88383 against predicted 0.8838). (c) SURVIVES (6.14 in [4, 13]). (a): same as at smaller N; the order holds and all three vertices tie.

### 2026-09-25 | Outcomes for C4-S2 and C4-S3 at N = 480 (code/C4_sticky.py K2 480, K3 480)

Verbatim:
```
K2 N=480 logN=6.1738
   modal faces along grid: ((1,), (2,), (3,)) -> ((1, 2, 3),)
   switch at c = 1.53009: ((1,), (2,), (3,)) -> ((1, 2, 3),)  (new modal comps e.g. [(160, 160, 160)])
K3 N=480 logN=6.1738
   modal faces along grid: ((1,), (2,), (3,)) -> ((1, 2, 3),)
   switch at c = 1.49980: ((1,), (2,), (3,)) -> ((1, 2, 3),)  (new modal comps e.g. [(160, 160, 160)])
```
- C4-S2 at N = 480: the jump is direct, and c* = 1.5301 misses the expansion value 1.5101 by 0.020, inside the 0.03 tolerance. So the kill recorded above rests on N = 60 and 120 (N = 240 missed by 0.0325, just outside); the miss shrinks with N.
- C4-S3 at N = 480 SURVIVES: direct jump, with 1.4998 < 1.5301.

### 2026-09-25 | Note: unregistered sanity checks (proved statements only, no predictions)

code/C4_checks.py (Lemma R; the Bessel score identity; the size of the Step 1 score error) and code/C4_check_F2.py (the Prop F2 bounds) were run without a pre-registered prediction, because they check inequalities that are already proved. Results:
- Lemma R: min(R - lower bound) = 6.25e-14 >= 0, max t(1-R) = 0.609 <= 1.
- Identity beta' = 2x + B: agrees to 1e-40.
- Step 1: the true score error is 0.162 (N = 100) and 0.069 (N = 400), against proven bounds of 15.2 and 13.0. The proven bound is valid but very loose.
- F2 bounds hold on the whole grid up to 1e-14 rounding.

## 2026-09-25 | Round 2 (after two independent verifications): registrations before any new run

Context: two verifiers reported twelve minor gaps in C4.md (none of its statements wrong). Repairs that need computation are registered here before the code is run. One verifier reported values for some of these cells; I list them where they exist, so these bands are not blind to them.

- C4-R1 (proof check for Lemma F-mom, not a new cell): code/C4_fmom_proof.py computes E X^2, E X^4 and E[J X^2] exactly for N = 1..12 with q a symbol (DP over paths, polynomials in q), and compares with the closed forms of Lemma F-mom. It also checks, as rational identities in the independent symbols N, q, R (R standing for r^N), that (i) E X^4 - (E X^2)^2 = 2 N^2 p^2 V / q^2, (ii) Cov(J,X^2)^2 / (Var J Var X^2) equals the Corollary's closed form, and (iii) E X^4 / N^4 = 3p^2/x^2 - p(1+10r+r^2)/(2x^3) + r(1+2r)(2+r)(1-R)/(2x^4) - 3 p r R/x^3.
  Prediction: every difference is identically 0. By the quasi-polynomial argument added to C4.md, N = 1..10 already suffices for all N >= 1.
  Kill: any nonzero difference.
- C4-R2 (sticky HDP, d = 3, beta uniform, large alpha; new method on old cells alpha = 100, 1000 and new cells alpha = 300, 3000, 30000): code/C4_hdp_quad.py computes P(direct) by deterministic quadrature (Beta CDF in the B3 direction, adaptive quad in B2 and B1). A second parametrization (logit coordinates) is used as a cross-check at alpha = 100 and 3000. The proof now written in C4.md (S3(d)) gives alpha * P(direct) -> 3 sqrt(3)/(8 pi) = 0.2067483. One verifier reported quadrature values alpha*P = 0.20450, 0.20598, 0.20667, 0.20674 at alpha = 100, 300, 3000, 30000.
  Prediction: alpha*P lies in [0.2040, 0.2050] at alpha = 100 (my MC: 0.2006 +- 0.004), [0.2055, 0.2065] at 300, [0.2060, 0.2070] at 1000, [0.2064, 0.2070] at 3000, [0.2067, 0.2068] at 30000. The distance to 0.2067483 decreases in alpha, roughly like 1/alpha. The two parametrizations agree to 1e-8 relative.
  Kill: any value outside its band, non-monotone approach, or the two parametrizations disagreeing by more than 1e-6 relative.

### 2026-09-25 | Outcome for C4-R1 (code/C4_fmom_proof.py; output saved in code/C4_fmom_proof_out.txt)

Verbatim:
```
N= 1: mass, EJ, EX2, E[JX2], EX4, Cov differences = [0, 0, 0, 0, 0, 0]  OK
N= 2: mass, EJ, EX2, E[JX2], EX4, Cov differences = [0, 0, 0, 0, 0, 0]  OK
N= 3: mass, EJ, EX2, E[JX2], EX4, Cov differences = [0, 0, 0, 0, 0, 0]  OK
N= 4: mass, EJ, EX2, E[JX2], EX4, Cov differences = [0, 0, 0, 0, 0, 0]  OK
N= 5: mass, EJ, EX2, E[JX2], EX4, Cov differences = [0, 0, 0, 0, 0, 0]  OK
N= 6: mass, EJ, EX2, E[JX2], EX4, Cov differences = [0, 0, 0, 0, 0, 0]  OK
N= 7: mass, EJ, EX2, E[JX2], EX4, Cov differences = [0, 0, 0, 0, 0, 0]  OK
N= 8: mass, EJ, EX2, E[JX2], EX4, Cov differences = [0, 0, 0, 0, 0, 0]  OK
N= 9: mass, EJ, EX2, E[JX2], EX4, Cov differences = [0, 0, 0, 0, 0, 0]  OK
N=10: mass, EJ, EX2, E[JX2], EX4, Cov differences = [0, 0, 0, 0, 0, 0]  OK
N=11: mass, EJ, EX2, E[JX2], EX4, Cov differences = [0, 0, 0, 0, 0, 0]  OK
N=12: mass, EJ, EX2, E[JX2], EX4, Cov differences = [0, 0, 0, 0, 0, 0]  OK
identity (i)   VarX2 - 2N^2p^2V/q^2          : 0
identity (ii)  rho2 - closed form            : 0
identity (iii) EX4/N^4 - rewritten form      : 0
total mismatches: 0
```
- C4-R1 SURVIVES: every difference is identically 0 for N = 1..12 with q symbolic, and the three rational identities hold in the independent symbols N, q, R. With the quasi-polynomial lemma (C4.md, Lemma F-mom proof), this proves Lemma F-mom for all N >= 1 and q in (0,1).

### 2026-09-25 | Outcome for C4-R2 (code/C4_hdp_quad.py; output saved in code/C4_hdp_quad_out.txt)

Verbatim (scipy also printed IntegrationWarnings from the innermost quad of route 1 and the middle quad of route 2: roundoff prevented the requested epsrel = 1e-12. The two routes agree to 2e-12, which bounds the effect):
```
limit 3 sqrt(3)/(8 pi) = 0.2067483
 alpha        P(direct) route1      alpha*P     (alpha*P)/limit-1   alpha*(ratio-1)
   100   2.0449576763e-03   0.204496   -1.090e-02   -1.090
   300   6.8660494049e-04   0.205981   -3.709e-03   -1.113
  1000   2.0651651477e-04   0.206517   -1.121e-03   -1.121
  3000   6.8890297046e-05   0.206671   -3.746e-04   -1.124
 30000   6.8913527861e-06   0.206741   -3.750e-05   -1.125
route2 alpha=100: P = 2.0449576763e-03, relative difference to route1 = +3.55e-15
route2 alpha=3000: P = 6.8890297046e-05, relative difference to route1 = +2.09e-12
```
- C4-R2 SURVIVES: all five values lie in their bands (0.204496, 0.205981, 0.206517, 0.206671, 0.206741). The approach to 0.2067483 is monotone and the relative gap times alpha settles near -1.125. The two parametrizations agree to 4e-15 and 2e-12. The values match the verifier's reported 0.20450, 0.20598, 0.20667, 0.20674. Unregistered observation, not a prediction: the relative correction looks like -9/(8 alpha); not derived.

### 2026-09-25 | Correction note on the C4-F3 outcome text above (not a new computation)

The C4-F3 outcome says the atoms carry "0.108 of the 0.189 at N = 100" and "dominate the second-order term at practical N". The 0.108 is the R^2 of the atom indicator alone. R^2 values are not additive and X^2 already sees the atoms, so this overstates their share. The incremental contribution R^2(atom, X^2) - R^2(X^2), from the C4-F7 table above, is 0.0320, 0.0215, 0.0138, 0.0085, 0.0052, 0.0031, 0.0018 at N = 50, 100, 200, 400, 800, 1600, 3200, against the second-order term 1/(4 x_N^2) = 0.0297, 0.0204, 0.0147, 0.0111, 0.0086, 0.0069, 0.0056. So the atoms' increment exceeds the second-order term at N = 50, is comparable at N = 100, and is smaller from N = 200 on. The kill verdict of C4-F3 stands (the values fell outside the bands); only the explanation is corrected. C4.md is updated accordingly.

## 2026-09-25 | C4-R3: numerical check of Lemma DV on non-reversible faces (registered before running)

Lemma DV (C4.md, I.2) is proved; this guards against a sign or transpose slip. code/C4_dv_check.py draws 5 random 4-state kernels K (zero diagonal, rows Dirichlet(1,1,1), seed 20260925), keeps the non-reversible ones (Kolmogorov cycle test on F = {1,2,3} fails by more than 1e-3), computes I(mu) = sup_phi Psi_mu(phi) by BFGS on the face F = {1,2,3}, and minimizes I over the face simplex by Nelder-Mead from 5 random starts.
- Prediction: for every kernel, (a) I(mu_F) = lambda_F = 1 - rho(K_F) to 1e-8; (b) the numerical minimizer is within 1e-4 of mu_F = l o r/<l,r> (left/right Perron vectors), and the minimum value is lambda_F to 1e-7; (c) the reversible-looking alternative (normalized r^2, or normalized l) is NOT the minimizer: its I exceeds lambda_F by more than 1e-6.
- Kill: any of (a), (b), (c) fails for any kept kernel.

### 2026-09-25 | Outcome for C4-R3 (code/C4_dv_check.py; output saved in code/C4_dv_check_out.txt)

Verbatim:
```
kernel 1: cycle asym=+0.0045 lambda_F=0.5945238287 I(mu_F)=0.5945238287 |argmin-mu_F|=3.0e-09 min=0.5945238287 I(r^2)-lam=5.77e-02 I(l)-lam=2.77e-02  (a,b,c)=(True,True,True)
kernel 2: cycle asym=+0.0374 lambda_F=0.1652160451 I(mu_F)=0.1652160451 |argmin-mu_F|=4.2e-09 min=0.1652160451 I(r^2)-lam=5.21e-02 I(l)-lam=7.05e-04  (a,b,c)=(True,True,True)
kernel 3: cycle asym=+0.0484 lambda_F=0.3755202560 I(mu_F)=0.3755202560 |argmin-mu_F|=3.6e-09 min=0.3755202560 I(r^2)-lam=1.26e-01 I(l)-lam=1.56e-02  (a,b,c)=(True,True,True)
kernel 4: cycle asym=+0.0041 lambda_F=0.4612472301 I(mu_F)=0.4612472301 |argmin-mu_F|=3.5e-09 min=0.4612472301 I(r^2)-lam=1.51e-02 I(l)-lam=1.21e-02  (a,b,c)=(True,True,True)
kernel 5: cycle asym=+0.1411 lambda_F=0.2626646735 I(mu_F)=0.2626646735 |argmin-mu_F|=3.1e-09 min=0.2626646735 I(r^2)-lam=4.49e-02 I(l)-lam=1.79e-03  (a,b,c)=(True,True,True)
all predictions hold: True
```
- C4-R3 SURVIVES: for all five non-reversible faces, I(mu_F) = lambda_F to 1e-10, the numerical argmin is within 4e-9 of mu_F = l o r/<l,r>, and the alternatives r^2 and l have I above lambda_F by 7e-4 to 0.13.

### 2026-09-25 | Note on the correction note above

The increments and 1/(4 x_N^2) values in the C4-F3 correction note were typed from the C4-F7 table before code/C4_round2_arith.py was run. That script (run afterwards) prints 0.03198, 0.02153, 0.01377, 0.00853, 0.00517, 0.00308, 0.00181 and 0.02973, 0.02037, 0.01471, 0.01108, 0.00862, 0.00689, 0.00562, which match the note to its printed precision. The same script gives the K4 triple rho = 0.824264 and thresholds 5.6904 and 41.213, and checks x/(e^x-1) <= e_inf(x) <= 1 - x e^{-x}/(2+x) against Table F-2 at x = 0.01, 0.1, 0.5, 1, 2, 3, 5 (all hold). No predictions are involved.
