# Problem 131 Paper D, topic D3 (heavy-tailed runs, golden-ratio exponent): pre-registration ledger

Model: runs alternate direction, P(L >= k) = k^(-alpha) (k >= 1). Stationary start: first run D with P(D = k) = k^(-alpha)/zeta(alpha). Fresh start: D ~ L. Edge E_N = P(S_N = N), centre Z_N = P(S_N = N/2), R_N = E_N/Z_N. Code lives in scratchpad/research131/code/D3_*.py. Theory numbers quoted below come from D3_theory.py (leading-order constants) and D3_pa.py (resummed pole approximation, a heuristic). Neither computes a walk distribution.

## 2026-09-25  D3-P1: three independent engines agree (new cells: N <= 14 all bins; alpha in {1.3,1.5,phi,1.9,2.5} stat/fresh, {0.4,0.8} fresh)

Prediction. The two-renewal formula (D3_engine.dist, conditions on the last run), heavy.py's first-run recursion with exact Hurwitz-zeta tails (D3_recursion.dist) and brute-force summation over all 2^(N-1) run compositions in 30-digit mpmath (D3_brute.brute) give the same probability in every bin, for N in {2,3,4,5,8,11,14}. Each brute-force law sums to 1.
Kill condition: any bin with relative discrepancy > 1e-9, or any brute-force total differing from 1 by more than 1e-20.

## 2026-09-25  D3-P2: reproduce program.md's heavy.py slopes (cells already reported: alpha = 1.5 and phi, N = 100..1600)

Prediction. heavy.py, run unmodified, prints: alpha = 1.5, local slope (800 -> 1600) = 0.178 after rounding to 3 decimals; alpha = phi, local slope 0.057 at N = 200 and 0.037 at N = 1600 (3 decimals). heavy.py approximates the tail sum of k^(-alpha) beyond N+1 by an integral, so its edge values are off by a relative amount of about (alpha-1)/(2N). The exact-tail engines should therefore differ from heavy.py's slopes by less than 0.002, and agree with each other to 1e-9 relative in edge and centre at N = 100..1600.
Kill condition: heavy.py's printed slopes differ from the program.md values by more than 0.001, or the exact engines differ from heavy.py's slopes by 0.002 or more.

## 2026-09-25  D3-P3: new cells alpha = 1.3, 1.7, 1.9 at N = 100, 200, 400, 800, 1600 (stationary start)

Theory. Leading order R_N ~ C N^e with e = 1 - alpha + 1/alpha. From D3_theory.py: C(1.3) = 0.4227, C(1.7) = 0.8800, C(1.9) = 1.4390, and e = +0.4692, -0.1118, -0.3737. Convergence is slow, with relative corrections of order N^(-(2-alpha)/alpha) and N^(-(alpha-1)/alpha). The resummed pole approximation (D3_pa.py, mode 'exact') predicts:
- alpha = 1.3: R = 5.678, 7.516, 9.981, 13.294, 17.761; slopes +0.405, +0.409, +0.414, +0.418.
- alpha = 1.7: R = 0.3414, 0.3329, 0.3227, 0.3111, 0.2984; slopes -0.037, -0.045, -0.053, -0.060.
- alpha = 1.9: R = 0.09654, 0.08071, 0.06691, 0.05504, 0.04497; slopes -0.258, -0.271, -0.282, -0.292.

The pole approximation drops the ballistic (big-jump) terms, which have relative size about n^(1/alpha - alpha). That is sizable only for alpha = 1.3 at small N.

Predictions:
(a) For every N >= 400 and all three alpha, |R_N / R_N^pole - 1| < 5%. At N = 100 and 200 the bound is 15%.
(b) For N >= 400, every local slope is within 0.02 of the pole-approximation slope.
(c) Signs: at every N <= 1600 the local slopes lie below e for alpha = 1.3, and above e for alpha = 1.7 and 1.9.
(d) R_N > 1 at every N for alpha = 1.3; R_N < 1 at every N for alpha = 1.7 and 1.9.
Kill condition: a violation of any of (a) to (d).

### Outcome D3-P1 (2026-09-25, D3_brute.py, output in code/D3_brute_out.txt)
CONFIRMED. All 5 x 2 x 7 (alpha, start, N) cells, plus alpha in {0.4, 0.8} fresh at N in {4, 9, 14}, agree bin by bin. Worst relative discrepancy over all bins and both engines: 7.1e-16. Every brute-force law sums to 1.0 at 20 printed digits.

### Outcome D3-P2 (2026-09-25, heavy.py unmodified in code/D3_heavy_unmodified_out.txt; comparison in code/D3_compare1600_out.txt)
Part 1 CONFIRMED. heavy.py prints alpha = 1.5 slope(1600) = +0.1784 (0.178), and alpha = phi slopes +0.0570 (N = 200) and +0.0372 (N = 1600) (0.057 and 0.037), as in program.md.
Part 2 REFUTED as stated. The exact-tail engines differ from heavy.py's slopes by more than 0.002 at N = 200: alpha = phi +0.00213, alpha = 1.7 +0.00240, alpha = 1.9 +0.00307. At N = 1600 the differences are 0.00013 to 0.00040. Cause: my threshold was an arithmetic slip, not an engine problem. A relative edge error of (alpha-1)/(2N) changes the 100 -> 200 slope by (alpha-1)/(400 ln 2), which is 0.0022 at phi and 0.0032 at 1.9, as observed. heavy.py's edge is low by 1.5e-3 to 4.3e-3 at N = 100, halving with each doubling of N. The two exact engines (last-run formula and first-run recursion with Hurwitz-zeta tails) agree to 6.4e-15 relative in edge and centre at every N <= 1600 and every alpha.
Exact slopes at 1600: 1.3: +0.41807; 1.5: +0.17814; phi: +0.03689; 1.7: -0.06004; 1.9: -0.29157.

### Outcome D3-P3 (2026-09-25, code/D3_compare1600_out.txt)
CONFIRMED, all of (a) to (d).
Exact R_N at N = 100..1600:
- alpha = 1.3: 5.67017, 7.51076, 9.97701, 13.29148, 17.75930.
- alpha = 1.7: 0.341418, 0.332879, 0.322662, 0.311049, 0.298369.
- alpha = 1.9: 0.0965424, 0.0807090, 0.0669093, 0.0550428, 0.0449706.
(a) The largest |R/R_pole - 1| is 1.40e-3 (alpha = 1.3, N = 100). At N = 1600 it is 1.1e-4, 3.6e-7 and 1.9e-8 for 1.3, 1.7 and 1.9.
(b) The largest slope difference from the pole approximation is 0.001 (alpha = 1.3, N = 200).
(c) Every slope lies below e for 1.3 and above e for 1.7 and 1.9.
(d) Holds.

## 2026-09-25  D3-P4: edge/centre at N = 3200 for alpha = phi and alpha = 1.5 (stationary start); not yet computed by any engine

Inputs used: exact values at N <= 1600 (above), the pole approximation at N = 3200 (D3_pa.py, 'exact' mode, 600-point Gauss-Legendre per panel; quadrature change 1e-11), and the exact edges E_3200 = zeta(a,3200)/(2 zeta(a)): 0.0024647495973 (phi), 0.0067674236455 (1.5). The pole approximation overestimated R at N = 1600 by 1.17e-6 (phi) and 6.39e-6 (1.5), and that error shrank by a factor of 2.5 to 3 per doubling.
Predictions:
- alpha = phi: R_3200 = 0.676609, the pole value 0.6766088 minus about 4e-7 relative. Equivalently Z_3200 = 0.00364280 and local slope (1600 -> 3200) = +0.0320. That is 0.8718 of the limit C(phi) = 0.776132. A plain extrapolation of the exact slopes' second differences gives 0.67656 as a cross-check.
- alpha = 1.5: R_3200 = 2.422344, the pole value 2.4223501 minus about 2.6e-6 relative. Equivalently Z_3200 = 0.00279375 and slope +0.1761. That is 0.9739 of the leading-order value C N^e = 2.48735.
- The exact value lies BELOW the pole value in both cases, by a relative amount between 1e-7 and 3e-6.
- The last-run engine and the first-run recursion agree to 1e-12 relative at N = 3200.
Kill condition: |R_3200/R_pole - 1| > 2e-5 for either alpha, or the exact value above the pole value, or the engines disagreeing by more than 1e-12.

### Outcome D3-P4 (2026-09-25, code/D3_n3200.py, output code/D3_n3200_out.txt)
CONFIRMED.
- alpha = phi: R_3200 = 0.6766085722, with Z_3200 = 3.6427998384e-03 and slope +0.03201. R_exact/R_pole - 1 = -3.91e-07.
- alpha = 1.5: R_3200 = 2.4223439498, with Z_3200 = 2.7937500973e-03 and slope +0.17604. R_exact/R_pole - 1 = -2.56e-06.
- Last-run engine against first-run recursion: centre -1.0e-14 and -6.9e-15, edge -2.2e-16.
The slope extrapolation (0.67656) was less accurate than the pole value (0.67661).

## 2026-09-25  D3-P5: large N and alpha = 5/3 (1 < alpha < 2, both starts). New cells.

Cells:
- Stationary and fresh start, alpha in {1.3, 1.5, phi, 5/3, 1.7, 1.9}, N in {6400, 10^4, 2*10^4, 5*10^4, 10^5}.
- alpha = 5/3 stationary at N = 100..3200.
- Fresh start for alpha in {1.5, phi} at N = 100..1600.
Engine: D3_engine.center_all with FFT. It matched the direct convolution to 6e-14 on the already-computed cells N <= 3200.
Theory values: D3_pa_large_out.txt (pole approximation, fixed for cancellation; unchanged at N <= 10^7 from the first version).
Predictions:
(a) Stationary: |R_exact/R_pole - 1| <= 1e-5 for alpha >= 1.5 at N >= 6400, and <= 1e-4 for alpha = 1.3. For alpha = 5/3 at N = 100..3200 the bound is 1e-4.
(b) Fresh: |R_exact/R_pole - 1| <= 1e-3 in every fresh cell. The pole values are 0.01426219, 0.008423135, 0.004922442, 0.002852536, 0.001642038 (alpha = 1.5) and 0.007161938, 0.003832297, 0.002025936, 0.001060524, 0.0005507522 (phi) at N = 100..1600.
(c) Leading-constant ratios R_N/(C N^e) at N = 10^5, stationary: 1.1317 (1.3), 0.99136 (1.5), 0.93758 (phi), 0.91023 (5/3), 0.88807 (1.7), 0.62423 (1.9). Fresh, R_N/(C_fr N^(e-1)): 1.0578, 0.97598, 0.93065, 0.90518, 0.88400, 0.62323. Over N in {6400, ..., 10^5} this ratio increases with N for every alpha except 1.3, where it decreases.
(d) alpha = phi, stationary: R_N increases with N and stays below C(phi) = 0.776132 in every computed cell. R at 10^5 is 0.72769.
(e) alpha = 5/3 (heat-conduction value, e = -1/15), stationary: over N in {100, 200, ..., 3200, 6400, 10^4, ..., 10^5}, R_N is largest at N = 200 (pole: 0.42399) and decreases after that. R at 10^5 is 0.35282.
Kill condition: a violation of any of (a) to (e).

## 2026-09-25  D3-P6: crossover size N*(alpha) just below phi (stationary). New cells.

Definition: N* is the smallest even N >= 10 such that R_N' > 1 for every even N' from N up to the largest computed N.
Pole-approximation roots (D3_crossover_theory_out.txt): 25.0 (1.5), 191.0 (1.55), 2595 (1.58), 14529 (1.59), 3.727e5 (1.60). Leading order C^(-1/e) gives 13.5, 41.8, 350, 1959, 7.38e4, a factor of 2 to 7.5 too small.
Predictions:
- N*(1.5) is 26, the first even N above the pole root.
- N*(1.55), N*(1.58), N*(1.59) and N*(1.60) lie within 2% of the pole roots.
- R_N - 1 changes sign exactly once for even N in [10, N_max] at alpha in {1.55, 1.58, 1.59}.
Kill condition: a violation of any of these.

## 2026-09-25  D3-P7: alpha >= 2 (stationary). New cells: alpha in {2.0, 2.2, 2.5, 3.5}, N in {1600, 6400, 10^4, 2*10^4, 5*10^4, 10^5}.

Theory: R_N ~ C_2 N^(3/2 - alpha) for alpha > 2, with C_2 = 0.784365 (2.2), 0.388127 (2.5), 0.112223 (3.5). For alpha = 2, R_N ~ sqrt(pi log N/(8 zeta(2)^3 N)).
Predictions:
(a) For alpha in {2.2, 2.5, 3.5}, |R_exact/R_pole - 1| <= 1e-4.
(b) At N = 10^5, R_N N^(alpha - 3/2)/C_2 = 0.7896, 0.9479, 0.9981, increasing in N. Convergence is slowest near alpha = 2.
(c) For alpha = 2, the pole value comes from averaging alpha = 2 +/- 1e-5 (difference 3e-4). |R_exact/R_pole - 1| <= 1e-3, and R_N/sqrt(pi log N/(8 mu^3 N)) is 0.8849, 0.9097, 0.9164, 0.9257, 0.9363, 0.9431 at the six N values, increasing.
(d) R_N < 1 and decreasing in N in every cell.
Kill condition: a violation of any of (a) to (d).

## 2026-09-25  D3-P8: alpha <= 1 (fresh start). New cells: alpha in {0.3, 0.5, 0.55, 0.58, 0.61, 0.65, 0.7, 0.9, 1.0}, N in {1000, 4000, 16000}, plus alpha = 1 at N in {1600, 10^4, 10^5}.

Theory (Theorem 6 of D3.md): N Z_N -> f(1/2) = (2/pi) tan(pi alpha/2), the Lamperti density at 1/2, and R_N ~ (pi/(4 tan(pi alpha/2))) N^(1-alpha). The relative corrections are expected to be of order N^-(1-alpha) or N^-alpha. The Lamperti density is U-shaped (f''(1/2) > 0) for alpha < alpha_c = 0.594611644 and has a central local maximum for alpha > alpha_c.
Predictions:
(a) |N Z_N/f(1/2) - 1| at N = 16000 is below 0.05 for alpha in {0.3, 0.5, 0.55, 0.58, 0.61, 0.65}, below 0.10 for 0.7 and below 0.5 for 0.9. For every alpha < 1 this deviation decreases from N = 1000 to 4000 to 16000.
(b) R_N > 1 in every cell with alpha <= 0.7. R_N < 1 in every cell with alpha = 0.9, whose leading-order crossover is near N = 1.1e9.
(c) At N = 16000 the centre bin is a strict local minimum (P(S_N = n) < P(S_N = n +/- 1), n = N/2) for alpha in {0.3, 0.5, 0.55, 0.58}, and a strict local maximum for alpha in {0.61, 0.65, 0.7, 0.9}.
(d) For alpha = 1 (heuristic Theorem 8), R_N / (pi^2 m_n/(8n)) lies in [0.75, 1.25] at N in {1600, 10^4, 10^5}, where m_n solves m (H_{m+1} - 1) = n = N/2. The heuristic values are 0.2614, 0.1970, 0.1489. R_N < 1 and decreasing in N.
Kill condition: a violation of any of (a) to (d).

### Outcome D3-P5 (2026-09-25, code/D3_large.py P5, output code/D3_large_P5_out.txt)
CONFIRMED, all of (a) to (e).
(a) Stationary, max |R/R_pole - 1| at N >= 6400: 3.1e-5 (1.3), 1.0e-6 (1.5), 1.3e-7 (phi), 5.6e-8 (5/3), 3.1e-8 (1.7), 9.2e-10 (1.9). For alpha = 5/3 at N = 100..3200 the max is 5.4e-5.
(b) Fresh, every registered cell: max 2.0e-4 (alpha = 1.5, N = 100).
(c) R_N/(C N^e) at 10^5, stationary: 1.131653, 0.991357, 0.937584, 0.910228, 0.888070, 0.624227. Fresh: 1.057815, 0.975978, 0.930654, 0.905177, 0.883997, 0.623234. The ratios are monotone as predicted: decreasing for 1.3 (both starts), increasing otherwise.
(d) alpha = phi: R_N = 0.689728 (6400), 0.697331 (10^4), 0.707939 (2*10^4), 0.719947 (5*10^4), 0.727689 (10^5). Increasing, and below C(phi) = 0.776132 throughout.
(e) alpha = 5/3: R = 0.423807 (100), 0.423987 (200), 0.421924 (400), 0.417782, 0.411815, 0.404300, 0.395515, 0.389307, 0.378980, 0.364368, 0.352822 (10^5). The maximum is at N = 200.
Unregistered byproducts (the script printed every N for every alpha): stationary N = 3200 for 1.3, 1.7 and 1.9; fresh N <= 3200 for 1.3, 5/3, 1.7 and 1.9; fresh N = 3200 for 1.5 and phi. These are reported in the output file but are NOT counted as tests. All lie within 1.1e-3 of the pole approximation.

### Post-hoc analysis (not pre-registered): extrapolated constant (code/D3_extrapolate.py)
Fitting the exact stationary R_N N^-e at N = 6400..10^5 with the correction exponents of Heuristic 11 gives C_est = 0.422495 (1.3; rel -5e-4), 0.647970 (1.5; rel -3e-7) and 0.776132 (phi; rel +5e-7). Compare C = 0.422717, 0.647971 and 0.776132.

### Outcome D3-P6, first part (2026-09-25, code/D3_crossover.py, output code/D3_crossover_out.txt, N up to 30000)
CONFIRMED for alpha = 1.5, 1.55, 1.58 and 1.59: N* = 26, 192, 2596 and 14530 respectively. Each has exactly one sign change of R_N - 1 on even N in [10, 30000].
For comparison: R_24 = 0.987199, R_26 = 1.002302 (1.5); R_190 = 0.999602, R_192 = 1.000950 (1.55); R_2590 = 0.999824, R_2600 = 1.000122 (1.58); R_14500 = 0.999888, R_14530 = 1.000006 (1.59).
alpha = 1.60 is still running (N up to 4*10^5); its outcome is recorded below when it finishes.

### Outcome D3-P7 (2026-09-25, code/D3_large.py P7, output code/D3_large_P7_out.txt)
CONFIRMED, all of (a) to (d).
(a) max |R/R_pole - 1|: 2.4e-10 (2.2), 6.5e-12 (2.5), 4.8e-12 (3.5).
(b) At 10^5: R N^(alpha-3/2)/C_2 = 0.789618, 0.947891, 0.998076, increasing in N.
(c) alpha = 2: max |R/R_pole - 1| = 9.7e-9, and R/lead = 0.884931, 0.909652, 0.916356, 0.925694, 0.936261, 0.943097, increasing.
(d) Holds in every cell.

### Outcome D3-P8 (2026-09-25, code/D3_large.py P8, output code/D3_large_P8_out.txt)
CONFIRMED, all of (a) to (d).
(a) N Z_N/f(1/2) - 1 at N = 1000/4000/16000:
- 0.3: +0.0949/+0.0635/+0.0421
- 0.5: +0.0032/+0.0017/+0.0009
- 0.55: -0.0214/-0.0141/-0.0089
- 0.58: -0.0386/-0.0256/-0.0164
- 0.61: -0.0583/-0.0394/-0.0256
- 0.65: -0.0899/-0.0625/-0.0419
- 0.7: -0.1402/-0.1019/-0.0717
- 0.9: -0.5584/-0.5016/-0.4462
All are under their bounds, and all decrease in modulus.
(b) R_N > 1 for alpha <= 0.7 (smallest 3.697 at alpha = 0.7, N = 1000). R_N = 0.562, 0.572, 0.591 for alpha = 0.9.
(c) At N = 16000 the centre is a local MIN for 0.3, 0.5, 0.55 and 0.58, with relative second differences +2.8e-8, +1.6e-8, +9.2e-9, +4.2e-9. It is a local MAX for 0.61, 0.65, 0.7 and 0.9 (-1.9e-9, -1.2e-8, -3.0e-8, -2.1e-7).
(d) alpha = 1: R = 0.207994, 0.167379, 0.131958 at N = 1600, 10^4, 10^5. The ratios to the heuristic are 0.7956, 0.8496, 0.8860.

### D3-P6, alpha = 1.60: first attempt failed (2026-09-25)
The run D3_crossover.py 1.60 200000 died after about 100 minutes with MemoryError (std::bad_alloc inside scipy irfft). The machine is shared with other jobs using several GB; my process used about 40 MB. It produced no result. It also appears not to have reached the 1e-14 stopping tolerance, which is close to the FFT noise floor at length 2e5.
Rerun: D3_crossover_resumable.py 1.60 190000 (N up to 3.8e5), which checkpoints every 5000 steps and stops at P(S_m <= nmax) < 1e-12 (neglected tail below 1e-11 relative). The prediction is unchanged: N*(1.60) within 2% of 3.727e5.

### Outcome D3-P6, alpha = 1.60 (2026-09-25): NOT COMPLETED
The resumable rerun was stopped by me after about 2 h 15 min of wall time. The machine was at 100% load and the process got only 481 s of CPU, below the 5000 steps needed for its first checkpoint; it would have needed several hours of dedicated CPU. No exact value exists, so the alpha = 1.60 part of P6 is neither confirmed nor refuted. The pole-approximation value N* ~ 3.727e5 remains a prediction. To finish: run D3_crossover_resumable.py 1.60 190000 on an idle machine (about 1 h at 38 ms per step).
Summary of P6: confirmed for alpha = 1.5, 1.55, 1.58, 1.59; untested for 1.60.

## 2026-09-25  D3-V1 (independent verifier, independent-computation lens): exact N*(1.60), stationary start. New cell (never computed by any engine).

Engine: code/D3_verify_ind_fourier.py (damped-circle spectral evaluation of Prop 2; validated against a separate step-by-step Markov-hazard engine, code/D3_verify_ind_markov.py, to 1e-12 at N <= 3200, and against brute force to 4e-16). It does not reuse any D3_*.py script.
Inputs: my own implementation of the pole approximation (code/D3_verify_ind_pole.py) puts the continuous root of R_pole = 1 at N = 372660 for alpha = 1.60 (and at 25.52, 190.50, 2595.88, 14528.5 for 1.5, 1.55, 1.58, 1.59, where the exact N* were 26, 192, 2596, 14530, i.e. the first even integer above the pole root in every case). R_pole overestimates R_exact, so the exact crossing lies slightly above the pole root.
Predictions:
(a) The developer's registered D3-P6 prediction: N*(1.60) within 2% of 3.727e5, i.e. in [365246, 380154].
(b) Sharper (mine): N*(1.60) = 372662, the first even integer above the pole root; kill if N* is outside [372660, 372666].
(c) On a grid of about 30 even N spread over [3e4, 4.2e5], R_N - 1 < 0 at every grid point below N* and > 0 at every grid point above it (only one sign change is visible on the grid; all even N are NOT checked).
Kill condition: violation of (a), (b) or (c), each reported separately.

### Outcome D3-V1 (2026-09-25, code/D3_verify_ind_nstar160.py, output code/D3_verify_ind_nstar160_out.txt)
Exact N*(1.60) = 372660. R_372656 - 1 = -3.662e-7, R_372658 - 1 = -1.816e-7, R_372660 - 1 = +2.981e-9, R_372662 - 1 = +1.876e-7; a second (M, r) setting reproduces each R - 1 to within 2e-11.
(a) CONFIRMED: 372660 is within 2% of 3.727e5 (it is 0.01% below it). This completes the developer's D3-P6 for alpha = 1.60.
(b) Point value REFUTED, kill window not triggered. I wrote 372662, but that was a slip in reading the rounded pole root: to more digits the pole root is 372659.96 (R_pole - 1 = -8.9e-8 at 372659 and +3.3e-9 at 372660), so the rule I stated ("first even integer above the pole root") gives 372660, which is the exact value. The kill window [372660, 372666] contains 372660.
(c) CONFIRMED on the grid: 30 even N in [30000, 420000] give exactly one sign change of R_N - 1, between 350112 (-2.149e-3) and 383466 (+9.83e-4); then bisection on even N. Not every even N in [3e4, 4.2e5] was computed, so "a single sign change" is established only on the grid and bisection points.
