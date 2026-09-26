# Ledger C1: first-order face selection and the exact law (Paper C). Predictions precede computations; outcomes are appended verbatim below them and never deleted.

Notation. Chain on d states, P = I + hQ, h = T/N, N visits, initial law mu (uniform unless stated). For a face F: Q_F = Q restricted to F x F (diagonal keeps the full rate q_i), lambda_F = -(Perron root of Q_F), alpha*_F = l o r (left and right Perron vectors of Q_F, normalised), I_F = Donsker-Varadhan rate of the killed chain. Theory numbers below come from code/C1_predict.py and code/C1_lib.py (theory only, run before any test; output in code/out/C1_predict_out.txt).

Cells.
- S3a (star): centre 0, leaves 1,2,3; q01=1.0, q10=2.0, q02=0.5, q20=1.5, q03=0.8, q30=2.5. q_i = (2.3, 2.0, 1.5, 2.5).
- P4b (path 0-1-2-3): q01=3.0, q10=1.2, q12=1.5, q21=2.0, q23=1.5, q32=3.0. q_i = (3.0, 2.7, 3.5, 3.0).
- NR3 (non-reversible killed face): 4 states, face F={0,1,2} is a biased 3-cycle: q01=q12=q20=1.6, q10=q21=q02=0.2, exits q03=0.1, q13=0.5, q23=1.0 (q3j=1). lambda_F = 0.492412, alpha*_F = l o r = (0.427735, 0.325217, 0.247049). Alternatives: QSD l = (0.3666, 0.3553, 0.2781) [L1 dist 0.122], r normalised (0.3928, 0.3082, 0.2991) [0.104], r^2 normalised (0.4555, 0.2804, 0.2641) [0.090], stationary law of the conservative part (1/3,1/3,1/3) [0.189].

## 2026-09-25 L1: exact law in transition-count (Whittle/BEST) form

Prediction (identity, derived in C1.md, Proposition 2): for every composition n with support F (|F| = k),
P_N(n) = sum_{a,b in F} mu_a sum_{m in M_ab(F)} t(m^+) h^{|m|} prod_{i != j} q_ij^{m_ij}/m_ij! prod_{i in F} (n_i-1)_{(m_i-1)} (1-h q_i)^{n_i-m_i},
where m ranges over nonnegative integer arrays on ordered pairs of F with out-in = 1_a - 1_b, m^+ = m + e_{ba} (a != b) or m (a = b) is connected on F, m_i = out_i(m) + [i=b], (x)_(r) is the falling factorial and t(m^+) is the number of spanning arborescences (with multiplicity) of m^+ towards any root (matrix-tree determinant).
Cells: (a) S3a with rates as exact rationals (1, 2, 1/2, 3/2, 4/5, 5/2), h = 1/10, uniform mu, N = 6 and N = 7, all compositions; (b) NR3 with rates as rationals (8/5, 1/5, 1/10, 1/2, 1, back-rates 1), h = 1/8, mu = (1/2, 1/4, 1/8, 1/8), N = 6, all compositions; (c) d = 3, rates q01=2, q02=0, q10=1/3, q12=3/2, q20=1, q21=1/2, mu = (1/3, 1/2, 1/6), h = 1/5, N = 9, all compositions.
Kill: any mismatch with brute-force enumeration of all d^N words (exact Fractions).
L1': the float DP code/C1_dp2.py agrees with the same brute force on cells (a) and (b) to relative error <= 1e-12 on every composition. Kill: larger error.

## 2026-09-25 L2: order of winning faces on a star and a path (new cells S3a, P4b; N = 64 and N = 160)

Scan: uniform mu, T from 0.05 to 0.98 T_max (T_max = N/max q_i) on a grid of step 0.05, every change of mode support refined by bisection. Record the sequence of supports of the global mode.
First-order theory (Corollary b): winners are the minimisers of tau lambda_F + |F| - 1 over reachable faces.
- S3a: {2} (tau < 1.29509), {0,1} (1.29509 < tau < 2.13237), {0,1,3} (2.13237 < tau < 3.86263), {0,1,2,3}. The first step is not nested: the vertex {2} is dropped. Faces {0,2} and {0,1,2} never win. Third-best gaps at the crossings: 0.283, 0.273, 0.494.
- P4b: {1} (tau < 0.57036), {0,1} (< 1.73844), {0,1,2} (< 2.69190), {0,1,2,3}. Third-best gaps at the crossings: 0.095, 0.100, 0.155.
Discrete-corrected first-order crossings (lambda_F replaced by -log(1 - h lambda_F)/h, exact Perron root of P_F):
- S3a: N=64: T = 4.923, 8.298, 15.553; N=160: T = 6.285, 10.472, 19.296.
- P4b: N=64: T = 2.221, 6.727, 10.839; N=160: T = 2.802, 8.513, 13.448.

- L2a (first order). Prediction: the sequence of mode supports is exactly the one above, for both cells and both N.
  Kill: any other support is the global mode at a scanned T, a listed face never appears, or the order differs.
  Hedge written before running: for P4b the third-best gaps times log N are only 0.4 to 0.8, comparable to second-order terms, so P4b at N = 64 is the cell most likely to fail. S3a has gaps times log N of 1.1 to 2.5.
- L2b (heuristic second-order direction, not implied by Theorem 1). Prediction: every observed crossing T_obs lies below the discrete-corrected T_disc listed above, and T_obs/T_disc is larger at N = 160 than at N = 64 for each crossing.
  Kill: any violation.
- L2c (location, Corollary b). Prediction: at N = 160, at the geometric midpoint of each observed window of a non-vertex face (for the last face, the window is [T_enter, 0.98 T_max]), the mode satisfies |n/N - alpha*_F|_1 <= 0.15, with alpha*_F: S3a {0,1}: (0.4473, 0.5527); {0,1,3}: (0.4859, 0.3206, 0.1935); full: (0.4644, 0.2322, 0.1548, 0.1486). P4b {0,1}: (0.4606, 0.5394); {0,1,2}: (0.2851, 0.5472, 0.1677); full: (0.1584, 0.3960, 0.2970, 0.1485).
  Kill: any exceedance.

## 2026-09-25 L3: the star with a rare centre (uniformity fails outside the class of Theorem 1)

Cell S3a at fixed T = 4, uniform mu. Compositions n = (n_c, n_1, n_2, n_3), leaves splitting N - n_c in proportions (0.2322, 0.1548, 0.1486)/0.5356 (rounded; remainder to leaf 1). D_N := log P_N(n) + 3 log N + T I_F(n/N), F = {0,1,2,3}. P_N(n) from the star-specialised exact formula (code/C1_star.py), itself first validated against the DP (L3 validation: relative agreement <= 1e-10 at N = 64 on all compositions with support F and n_c <= 6; kill otherwise).
- (a) n_c = 1: P_N(n) = 0 exactly (N = 50, 100). Kill: nonzero.
- (b) n_c = 2 (every covering walk visits the centre twice): D_N decreases by between 2.2 and 2.4 per decade for N in {10^3, 10^4, 10^5, 10^6}, and D_N + log N changes by <= 0.05 between N = 10^5 and 10^6. Kill: otherwise.
- (c) in-class comparator n_c = round(0.4644 N): |D_{10^6} - D_{10^5}| <= 0.05. Kill: otherwise.
- (d) refined theorem (Theorem 1'): n_c = round(sqrt N) gives W = (1/2) log N + O(1), so D_N decreases by between 0.95 and 1.35 per decade for N in {10^4, 10^5, 10^6}. Kill: otherwise.

## 2026-09-25 L4: non-reversible location (cell NR3, N = 1600)

Face-{0,1,2} maximiser n(T) (support exactly F, mu uniform on 4 states) for T in {4, 8, 16, 32, 64}, computed by the 3-state substochastic DP (code/C1_dp3.py).
Prediction (Corollary a,b): |n(T)/N - alpha*|_1 is decreasing in T; at T = 64 it is <= 0.045 and n(T)/N is closer to alpha* = l o r than to l, r, r^2 or the conservative stationary law.
Kill: any failure.

## 2026-09-25 L5: bulk error term (cell NR3, N = 1600, T in {4, 8, 16, 32})

Region R: support F = {0,1,2}, min_i n_i/N >= 0.05, lattice subsampled with spacing 16 in n_0 and n_1. E_T(n) := log P_N(n) + 2 log N + T I_F(n/N).
The spread of T I_F over R at T = 32 is 47.1 (computed from theory only), so a wrong rate would show.
- L5a: spread_R(E_T) = max_R E_T - min_R E_T <= 4 for each T. Kill: larger at some T.
- L5b (heuristic prefactor T^{(k-1)/2}): the least-squares slope of median_R(E_T) against log T is in [0.5, 1.5]. Kill: outside.

### 2026-09-25 Outcome L1 and L1' (code/C1_validate.py, output code/out/C1_validate_out.txt), verbatim

```
L1(a) S3a: N=6 compositions=84 exact mismatches=0  DP max rel err=3.70e-16 (0.0s)
L1(a) S3a: N=7 compositions=120 exact mismatches=0  DP max rel err=4.24e-16 (0.1s)
L1(b) NR3: N=6 compositions=84 exact mismatches=0  DP max rel err=4.48e-16 (0.2s)
L1(c) d3: N=9 compositions=55 exact mismatches=0 (0.1s)
diag S3a: N=7 nonzero compositions=77/120 total mass=1 example P(2, 1, 1, 3)=4671/25600000
diag NR3: N=6 nonzero compositions=84/84 total mass=1 example P(2, 1, 1, 2)=6314261/1310720000
diag d3: N=9 nonzero compositions=55/55 total mass=1 example P(3, 3, 3)=2826703/84375000
```
L1 survives (exact equality on every composition of all three cells). L1' survives (max relative error 4.5e-16).

### 2026-09-25 Outcome L2a at N = 64 (code/C1_scan.py; outputs code/out/C1_scan_S3a_N64.txt, C1_scan_P4b_N64.txt), verbatim

```
cell S3a N=64 logN=4.1589 Tmax=25.600 grid=501 time=38s
  winner sequence (first grid T where it wins): [(0.05, '(2,)'), (3.5, '(0, 1)'), (5.35, '(0, 1, 3)'), (9.3, '(0, 1, 2, 3)')]
  crossing (2,) -> (0, 1) at T in [3.482278, 3.482281], tau_N = 0.83731
  crossing (0, 1) -> (0, 1, 3) at T in [5.321338, 5.321341], tau_N = 1.27951
  crossing (0, 1, 3) -> (0, 1, 2, 3) at T in [9.264072, 9.264075], tau_N = 2.22754
cell P4b N=64 logN=4.1589 Tmax=18.286 grid=358 time=29s
  winner sequence (first grid T where it wins): [(0.05, '(1,)'), (1.7, '(0, 1)'), (4.2, '(0, 1, 2)'), (6.55, '(0, 1, 2, 3)')]
  crossing (1,) -> (0, 1) at T in [1.682828, 1.682831], tau_N = 0.40463
  crossing (0, 1) -> (0, 1, 2) at T in [4.197580, 4.197583], tau_N = 1.00930
  crossing (0, 1, 2) -> (0, 1, 2, 3) at T in [6.515237, 6.515240], tau_N = 1.56658
```
At N = 64 the order is exactly as predicted for both cells (N = 160 still running; L2b and L2c are judged after it).

### 2026-09-25 Outcome L3 (code/C1_L3.py, code/C1_L3_validate_full.py; outputs code/out/C1_L3_out.txt, C1_L3_validate_full_out.txt), verbatim

```
L3 validation (full): N=64 T=4, n_c<=6: compared 8560 positive compositions, max rel err 2.708944180085382e-14 ; zero-probability compositions (both agree): 1891
(a) N=50: max DP probability over compositions with n_c=1 and all leaves >=1: 0.0
    star formula at n_c=1: log P = -inf
(a) N=100: max DP probability over compositions with n_c=1 and all leaves >=1: 0.0
    star formula at n_c=1: log P = -inf
(b) n_c = 2
   N=1e3 n=(2, 433, 288, 277) logP=-28.880091 D_N=-0.941934 D_N+logN=5.965822
   N=1e4 n=(2, 4334, 2890, 2774) logP=-38.095549 D_N=-2.729763 D_N+logN=6.480577  drop per decade=1.787830
   N=1e5 n=(2, 43352, 28902, 27744) logP=-47.306564 D_N=-4.867545 D_N+logN=6.645381  drop per decade=2.137781
   N=1e6 n=(2, 433532, 289021, 277445) logP=-56.516976 D_N=-7.117824 D_N+logN=6.697687  drop per decade=2.250279
(c) n_c = round(0.4644 N)
   N=1e3 n=(464, 232, 155, 149) logP=-18.34082799 D_N=2.382443 (xcut 30 vs 40 diff 0.0e+00)
   N=1e4 n=(4644, 2322, 1548, 1486) logP=-25.25600500 D_N=2.375016 (xcut 30 vs 40 diff 0.0e+00)  change=-0.007427
   N=1e5 n=(46440, 23220, 15480, 14860) logP=-32.16466830 D_N=2.374108 (xcut 30 vs 40 diff 0.0e+00)  change=-0.000908
   N=1e6 n=(464400, 232200, 154800, 148600) logP=-39.07251436 D_N=2.374017 (xcut 30 vs 40 diff 0.0e+00)  change=-0.000091
(d) n_c = round(sqrt N)
   N=1e4 n=(100, 4292, 2861, 2747) logP=-33.22760532 D_N=0.687867 (xcut 14 vs 20 diff 0.0e+00)
   N=1e5 n=(316, 43216, 28811, 27657) logP=-41.46346650 D_N=0.094419 (xcut 14 vs 20 diff 0.0e+00)  drop per decade=0.593448
   N=1e6 n=(1000, 433099, 288733, 277168) logP=-49.58110680 D_N=-0.698035 (xcut 14 vs 20 diff 0.0e+00)  drop per decade=0.792454
```
Verdict as registered: L3 validation survives; (a) survives; (c) survives; (b) is KILLED (drops 1.79 and 2.14 per decade lie below 2.2, and D_N + log N moved by 0.052 > 0.05 between 1e5 and 1e6); (d) is KILLED (drops 0.59 and 0.79 per decade lie below 0.95).
Diagnosis written after seeing the numbers: the tolerances ignored a correction that decays slowly at fixed T. The rate I_F has a square-root singularity at the face boundary: T I_F(n/N) contains -2T sum_l sqrt(alpha_c alpha_l q_0l q_l0), a "gain" from many short visits to the centre. The true probability only realises that gain when T^2 alpha_c >> 1 (it is the large-argument form e^{2x} of a Bessel sum I_0(2x) = sum x^{2y}/(y!)^2 over centre visits); when T^2 alpha_c << 1 the sum is about 1. So at fixed T the discrepancy is about 2T sqrt(alpha_c) * const, which is O(1) (inside the theorem's O(log T)) but decays only like N^{-1/2} for n_c = 2 and N^{-1/4} for n_c = sqrt N. In (b) the increments of D_N + log N are 0.515, 0.165, 0.052, ratios 0.32 and 0.32 = 10^{-1/2}, consistent with this. The follow-up L3' below tests the diagnosis on new sizes.

## 2026-09-25 L3' (follow-up, registered after the L3 kill and before any computation at N = 1e7, 1e8)

Same cell and compositions as L3, N = 1e7 and 1e8.
- (b') n_c = 2: D_N + log N = C - c N^{-1/2} + smaller. Prediction: the increment of D_N + log N from 1e6 to 1e7 is 0.0165 within a factor 1.3 (in [0.0127, 0.0215]) and from 1e7 to 1e8 is 0.0052 within a factor 1.3 (in [0.0040, 0.0068]).
- (d') n_c = round(sqrt N): increments of D_N + (1/2) log N were 0.558 (1e4 to 1e5) and 0.359 (1e5 to 1e6). Prediction: each later increment is between 0.45 and 0.75 times the previous one (leading ratio 10^{-1/4} = 0.562), and the drop of D_N per decade from 1e7 to 1e8 is in [0.95, 1.15] (limit (1/2) log 10 = 1.1513).
Kill: any value outside its interval.

### 2026-09-25 Outcome L3' (code/C1_L3b.py, output code/out/C1_L3b_out.txt), verbatim (the file also re-prints the L3 lines, unchanged)

```
(b') n_c = 2
   N=1e6 n=(2, 433532, 289021, 277445) logP=-56.51697567 D_N=-7.117824 D_N+logN=6.697687
   N=1e7 n=(2, 4335324, 2890216, 2774458) logP=-65.72732279 D_N=-9.403849 D_N+logN=6.714246  increment=0.016559
   N=1e8 n=(2, 43353248, 28902165, 27744585) logP=-74.93766379 D_N=-11.701196 D_N+logN=6.719485  increment=0.005238
(d') n_c = round(sqrt N)
   N=1e6 n=(1000, 433099, 288733, 277168) logP=-49.58110680 D_N=-0.698035 (xcut diff 0.0e+00) D_N+0.5logN=6.209720
   N=1e7 n=(3162, 4333954, 2889303, 2773581) logP=-57.65942575 D_N=-1.632519 (xcut diff 0.0e+00) D_N+0.5logN=6.426529  increment=0.216808 drop/decade=0.934484
   N=1e8 n=(10000, 43348913, 28899276, 27741811) logP=-65.72449222 D_N=-2.656803 (xcut diff 0.0e+00) D_N+0.5logN=6.553537  increment=0.127009 drop/decade=1.024284
```
Verdict: (b') survives (0.016559 in [0.0127, 0.0215]; 0.005238 in [0.0040, 0.0068]). (d') survives (increment ratios 0.604 and 0.586 in [0.45, 0.75]; drop 1.0243 in [0.95, 1.15]). The deficit of log N (n_c = 2) and (1/2) log N (n_c = sqrt N) predicted by Theorem 1' is confirmed, with the N^{-1/2} and N^{-1/4} corrections identified in the L3 diagnosis.

### 2026-09-25 Outcome L4 and L5 (code/C1_NR3.py, output code/out/C1_NR3_out.txt), verbatim

```
alpha* = l o r = [0.427735 0.325217 0.247049]  lambda_F = 0.49241223040592963
L4: face maximiser vs alpha*
  T=  4.0 mode=(734, 510, 356) n/N=[0.4588 0.3188 0.2225] |n/N-alpha*|_1=0.0620 dists to alternatives {'l': 0.1843, 'r': 0.1531, 'r2': 0.0831, 'pi_cons': 0.2508} (DP 351s)
  T=  8.0 mode=(706, 516, 378) n/N=[0.4412 0.3225 0.2362] |n/N-alpha*|_1=0.0270 dists to alternatives {'l': 0.1493, 'r': 0.1256, 'r2': 0.0842, 'pi_cons': 0.2158} (DP 359s)
  T= 16.0 mode=(695, 518, 387) n/N=[0.4344 0.3238 0.2419] |n/N-alpha*|_1=0.0133 dists to alternatives {'l': 0.1355, 'r': 0.1144, 'r2': 0.0867, 'pi_cons': 0.2021} (DP 351s)
  T= 32.0 mode=(689, 520, 391) n/N=[0.4306 0.325  0.2444] |n/N-alpha*|_1=0.0058 dists to alternatives {'l': 0.128, 'r': 0.1094, 'r2': 0.0892, 'pi_cons': 0.1946} (DP 369s)
  T= 64.0 mode=(687, 520, 393) n/N=[0.4294 0.325  0.2456] |n/N-alpha*|_1=0.0033 dists to alternatives {'l': 0.1255, 'r': 0.1069, 'r2': 0.0892, 'pi_cons': 0.1921} (DP 346s)
L5: E_T(n) = log P + 2 log N + T I_F(n/N) over region R (min n_i/N >= 0.05, spacing 16)
  |R| = 3741, I_F range over R: [0.4925, 1.9660]
  T= 4.0: spread E = 1.3207 (max at (1440, 80, 80), min at (528, 528, 544)), median E = 1.6312, median E - log T = 0.2449, spread of T*I_F = 5.89
  T= 8.0: spread E = 1.3809 (max at (1440, 80, 80), min at (528, 528, 544)), median E = 2.3472, median E - log T = 0.2678, spread of T*I_F = 11.79
  T=16.0: spread E = 1.2878 (max at (1440, 80, 80), min at (464, 512, 624)), median E = 2.9710, median E - log T = 0.1984, spread of T*I_F = 23.58
  T=32.0: spread E = 1.3094 (max at (1440, 80, 80), min at (128, 176, 1296)), median E = 3.3480, median E - log T = -0.1178, spread of T*I_F = 47.15
  least-squares slope of median E vs log T: 0.8330
```
Verdict: L4 survives (distance decreasing: 0.0620, 0.0270, 0.0133, 0.0058, 0.0033; at T = 64 it is 0.0033 <= 0.045, and the nearest alternative, r^2, is at 0.0892). The products T * distance are 0.25, 0.22, 0.21, 0.19, 0.21, so the displacement is about 0.2/T. L5a survives (spreads 1.32, 1.38, 1.29, 1.31 <= 4, against spreads of T I_F of 5.9 to 47.2). L5b survives (slope 0.833 in [0.5, 1.5]).

## 2026-09-25 L6: a coordinate equal to 1 inside the class (cell S3a, T = 4)

Leaf 1 of the star is visited once by the covering walk 2-0-1-0-3... no: the walk l2 c l1 c l3 visits the centre twice, but the centre is in the bulk here, so the composition is in the class N_K. Composition n = (round(0.4644 N), 1, n_2, n_3) with n_2 : n_3 = 0.1548 : 0.1486 (rounded, remainder to leaf 2). D_N := log P_N(n) + 3 log N + T I_F(n/N) (Theorem 1 predicts D_N = O(1) at fixed T; the only boundary correction is of order T/sqrt(N)).
Prediction: |D_{1e4} - D_{1e3}| <= 0.5, |D_{1e5} - D_{1e4}| <= 0.2, |D_{1e6} - D_{1e5}| <= 0.05.
Kill: any violation.

### 2026-09-25 Outcome L6 (code/C1_L6.py, output code/out/C1_L6_out.txt), verbatim

```
N=1e3 n=(464, 1, 273, 262) logP=-18.92848988 (xcut 30 vs 40 diff 0.0e+00) D_N=3.675348
N=1e4 n=(4644, 1, 2732, 2623) logP=-25.84539460 (xcut 30 vs 40 diff 0.0e+00) D_N=3.827559  change=+0.152211
N=1e5 n=(46440, 1, 27327, 26232) logP=-32.75414832 (xcut 30 vs 40 diff 0.0e+00) D_N=3.878712  change=+0.051153
N=1e6 n=(464400, 1, 273272, 262327) logP=-39.66200953 (xcut 30 vs 40 diff 0.0e+00) D_N=3.895226  change=+0.016513
```
Verdict: survives (changes 0.152 <= 0.5, 0.051 <= 0.2, 0.0165 <= 0.05; successive ratios 0.34 and 0.32, the T/sqrt(N) correction again). Note on the wording of the L6 entry above: its first sentence was garbled when written; the intended meaning is that leaf 1 (with n_1 = 1) is the only rare state, and the covering walk l2 c l1 c l3 visits it once, so n is in the class N_K. The prediction and kill condition were not changed.

### 2026-09-25 Outcome L2a at N = 160, L2b and L2c (code/C1_scan.py, code/C1_L2post.py; outputs code/out/C1_scan_*_N160.txt, C1_L2post_out.txt), verbatim

```
cell S3a N=160 logN=5.0752 Tmax=64.000 grid=1254 time=5195s
  winner sequence (first grid T where it wins): [(0.05, '(2,)'), (4.6, '(0, 1)'), (7.1, '(0, 1, 3)'), (12.35, '(0, 1, 2, 3)')]
  crossing (2,) -> (0, 1) at T in [4.572894, 4.572897], tau_N = 0.90103
  crossing (0, 1) -> (0, 1, 3) at T in [7.064606, 7.064609], tau_N = 1.39199
  crossing (0, 1, 3) -> (0, 1, 2, 3) at T in [12.313889, 12.313892], tau_N = 2.42630
cell P4b N=160 logN=5.0752 Tmax=45.714 grid=896 time=4606s
  winner sequence (first grid T where it wins): [(0.05, '(1,)'), (2.2, '(0, 1)'), (5.65, '(0, 1, 2)'), (8.7, '(0, 1, 2, 3)')]
  crossing (1,) -> (0, 1) at T in [2.158310, 2.158313], tau_N = 0.42527
  crossing (0, 1) -> (0, 1, 2) at T in [5.618463, 5.618466], tau_N = 1.10705
  crossing (0, 1, 2) -> (0, 1, 2, 3) at T in [8.694479, 8.694482], tau_N = 1.71314
L2b S3a N=64: T_obs = [3.4823, 5.3213, 9.2641]  T_disc = [4.923, 8.298, 15.553]  ratio = [0.7073, 0.6413, 0.5956]  all below: True
L2b S3a N=160: T_obs = [4.5729, 7.0646, 12.3139]  T_disc = [6.285, 10.472, 19.296]  ratio = [0.7276, 0.6746, 0.6382]  all below: True
L2b S3a: ratio larger at N=160 for each crossing: [True, True, True]
L2b P4b N=64: T_obs = [1.6828, 4.1976, 6.5152]  T_disc = [2.221, 6.727, 10.839]  ratio = [0.7577, 0.624, 0.6011]  all below: True
L2b P4b N=160: T_obs = [2.1583, 5.6185, 8.6945]  T_disc = [2.802, 8.513, 13.448]  ratio = [0.7703, 0.66, 0.6465]  all below: True
L2b P4b: ratio larger at N=160 for each crossing: [True, True, True]
L2c S3a N=160 face (0, 1): window [4.573,7.065] T_mid=5.684 global winner (0, 1) mode (71, 89, 0, 0) n/N on face [0.4438 0.5562] alpha* [0.4473 0.5527] L1 dist 0.0070
L2c S3a N=160 face (0, 1, 3): window [7.065,12.314] T_mid=9.327 global winner (0, 1, 3) mode (81, 51, 0, 28) n/N on face [0.5062 0.3188 0.175 ] alpha* [0.4859 0.3206 0.1935] L1 dist 0.0407
L2c S3a N=160 face (0, 1, 2, 3): window [12.314,62.720] T_mid=27.791 global winner (0, 1, 2, 3) mode (76, 38, 23, 23) n/N on face [0.475  0.2375 0.1438 0.1438] alpha* [0.4644 0.2322 0.1548 0.1486] L1 dist 0.0318
L2c P4b N=160 face (0, 1): window [2.158,5.618] T_mid=3.482 global winner (0, 1) mode (73, 87, 0, 0) n/N on face [0.4562 0.5438] alpha* [0.4606 0.5394] L1 dist 0.0087
L2c P4b N=160 face (0, 1, 2): window [5.618,8.694] T_mid=6.989 global winner (0, 1, 2) mode (46, 91, 23, 0) n/N on face [0.2875 0.5688 0.1438] alpha* [0.2851 0.5472 0.1677] L1 dist 0.0479
L2c P4b N=160 face (0, 1, 2, 3): window [8.694,44.800] T_mid=19.736 global winner (0, 1, 2, 3) mode (25, 65, 48, 22) n/N on face [0.1562 0.4062 0.3    0.1375] alpha* [0.1584 0.396  0.297  0.1485] L1 dist 0.0264
```
Verdict: L2a survives in both cells at both N = 64 and N = 160 (exactly the predicted order; no other support was the global mode at any of the 501 + 358 + 1254 + 896 grid points or bisection points; the non-nested first step {2} -> {0,1} of S3a is confirmed at both sizes). The hedge about P4b did not materialise. L2b survives (all 12 ratios T_obs/T_disc < 1, each larger at N = 160). L2c survives (L1 distances 0.007 to 0.048, all <= 0.15). Caveat on L2a: the grid has step 0.05 in T, so a winning window shorter than about 0.05 could be missed; none was seen in the bisection refinements either.
Remark on thresholds: the observed tau_N are 0.84/0.90, 1.28/1.39, 2.23/2.43 (S3a, N = 64/160) against tau* = 1.295, 2.132, 3.863, and 0.40/0.43, 1.01/1.11, 1.57/1.71 (P4b) against 0.570, 1.738, 2.692. They sit 25 to 40 percent below first order and move up slowly with N.

## 2026-09-26 Erratum from the audit repair (nothing above is changed; no prediction, outcome or verdict is affected)
- The "Remark on thresholds" after Outcome L2 says the observed tau_N "sit 25 to 40 percent below first order". From the tau_N and tau* printed above, the gaps are 35.3/40.0/42.3% (S3a) and 29.1/41.9/41.8% (P4b) at N = 64, and 30.4/34.7/37.2% (S3a) and 25.4/36.3/36.4% (P4b) at N = 160. So the range is 25 to 42 percent (29 to 42 at N = 64).
- In the L2 registration, three theory numbers are off in the last digit. The third-best gaps 0.273 (S3a, second crossing) and 0.155 (P4b, third crossing) were rounded twice, from the 4-digit values 0.2725 and 0.1545 in code/out/C1_predict_out.txt. T_disc = 13.448 (P4b, N = 160, third crossing) is copied as C1_predict.py printed it. The independent verifier's recomputation, which was not rerun here, gives 0.272474, 0.154474 and 13.447471, that is 0.272, 0.154 and 13.447. Neither the L2 predictions nor the L2 kill conditions depend on these digits.
