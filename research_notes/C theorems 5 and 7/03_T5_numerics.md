# Route T5-C: exact finite-horizon numerics and adversarial scan for Theorem 5

Base checkpoint: `6add913`. Date: October 24, 2026.

Inputs read: `00_targets.md` (all), `research_notes/Occupation novelty and compact advances/11_C_ready_to_draft_outline.md` (all; Sections 1, 3, 5 used). Nothing else from the repository was used: the chain, the face formulas and the design constants are re-derived in the scripts from the definitions in those two files. All numbers below are produced by the scripts `03_*.py` in this folder, run as `py -I script.py`; outputs are archived next to them (`03_*_output.txt`, `03_*.json`). Nothing here is a proof. Where a statement is a computational observation it is said so.

## 0. Summary

1. The exact laws are computed without approximation: singleton by closed form, pair `{a,b}` by the exact run-count formula, faces containing the third state by exact dynamic programming (full law for `N <= 300`, capped at `n_k <= L` for larger `N`) and, for compositions with exactly one visit to the suppressed state, by an exact insertion formula validated against the dynamic programme to `3e-13` (Section 1).
2. Pair-entry time. For all six ordered retained pairs of the chosen generator and `N` from 200 to `10^5` (to `10^6` for three pairs) the exact controlled maxima have exactly one crossing of the pair against the better singleton; just below it the exact winner is `{i}`, just above it is `{i,j}`, and no other face wins. `t_{ij,N}` lies below `t_ij` for every `N`, by a large margin (`0.26` to `0.39` of `t_ij` at the largest `N`), so the sign of the `log log N/(2 log N)` correction is right and its size is a small part of the total deviation at accessible `N`.
3. The residual `(t_{ij,N} - t_ij(1 - log log N/(2 log N))) log N` is bounded and moves slowly (for pair (1,2): `-7.6` at `N=200`, `-8.2` at `N=10^6`), toward the value `-t(log t /2 + kappa)` predicted by the crossing equation with a constant `kappa`. This is consistent with `O(1/log N)`.
4. The coefficient `1/2`. The literal two-regressor fit `(t - t_N)/t = a log log N/log N + c/log N` gives `a` between `0.62` and `0.99`, not `0.5`; this fit is badly conditioned and biased (explained in 2.3) and cannot be read as evidence against `1/2`. Two sharper tests both support `1/2`: (i) the implied constant `kappa_N = log N - T_N/t - (1/2) log T_N` (with `T_N = tau_N log N`) drifts by at most `0.03` over a range where `log T_N` moves by about `0.6`; the local exponent comes out `0.42` to `0.51` for `N` from `10^4`; (ii) at fixed `T`, `N` up to `10^7`, the ratio `M_pair/M_single` scales like `N^{-1} T^{1/2} e^{-T(lam_pair - lam_i)}`: the doubling ratio of the normalized amplitude is `0.99` at `T=40->80` for one pair and `0.96` for the other (a `T^1` law would give 2).
5. Singleton switch. `x_{i,N}` is available in closed form for the singleton crossing, `x_{i,N} - x_i = log(mu_1/mu_i)/(tau_0 log N) + O(log N/N)`; the exact `x_{i,N} log N` residual matches this to three digits, and the pair `{1,i}` loses by `e^{4}` to `e^{9.5}` at the switch, so `x_{i,N} = x_i + O(1/log N)` is observed with the explicit constant.
6. Reconstruction applied to the exact finite-`N` coordinates returns `Q_N` with `||Q_N - Q||_2` falling from `2.45` (`N=200`) to `0.93` (`N=10^5`); after dividing `t_{ij,N}` by `1 - log log N/(2 log N)` it is `1.92` to `0.67`, and `||.|| log N` stays between `10.2` and `7.7`, bounded and slowly decreasing.
7. Adversarial scan (six faces, exact, 10 configurations). The onset, over cells whose leading-score gap is at least `0.75`, is at most `10^3` to `3*10^4` for configurations with `mu_* = 0.3`, down to `b/R = 0.025`; it equals the trivial stochasticity threshold `N_adm ~ U q_max log N`, which grows like `b^{-2}`. It grows roughly like `1/mu_*` in the start (`10^3`, `10^4`, `10^5` for `mu_* = 0.05, 0.01, 0.001`), and reaches `3*10^5` for a configuration with both unequal stationary law and `mu_* = 0.02`. For gap threshold `0.5` the onset is larger: `3*10^3` for the base case, `> 3*10^5` at the edges. No failure was found that is not explained by a small leading gap or by a small start mass.
8. Two-state counterexample over all starts is reproduced exactly (Section 3.3), including the onset `N* = (mu_1/mu_2)^4` for fixed starts.
9. The faces containing the suppressed state: margin of the best composition with one visit to `k` against the predicted six-face winner stays positive in all computed cells, but its minimum over `N` is small near the top of the `tau` range (`1.54` in log scale at `N = 10^6`, `tau = U`, base generator, rising again to `2.35` at `N = 10^7`), and for generators with small `b` the minimum lies beyond `N = 10^6` and was not reached (Section 3.4). This is the one place where the numerics leave an unresolved quantity.

## 1. Setting, exact computations, validation

Generator (states 0,1,2 in code, written 1,2,3 here): stationary law `pi = (0.25, 0.35, 0.40)`, conductances `c_12 = 0.45`, `c_13 = 0.34`, `c_23 = 0.37`, `Q_ij = c_ij/pi_i`. Exit rates `q = (3.16, 2.34286, 1.775)`. Start `mu = (0.3, 0.3, 0.4)`. Complete graph, `m = 3`.

Class constants: `R = ||S||_2 = 4.35931`, `b = min sqrt(w_ij) = 0.98887` (edge 2-3 has `w = 0.97786`), `H = 2R = 8.7186`, `tau_0 = 1/(2R) = 0.11470`, `U = 8R/b^2 = 35.664`, `M = 4R + 4UR^2 = 2728.4`. Exit differences `d_i = q_i - q_1 = (0, -0.81714, -1.385)`. The limiting `t_ij` come from the displayed formula of C-I1 and were cross-checked against the spectral condition `tau(lam_i - lam_pair) = 1` (same value).

Exact objects (all in `03_core.py`):

* singleton: `log mu_i + (N-1) log(1 - T q_i/N) + T v_i`.
* pair `{a,b}`: for each composition `(n_a, n_b)`, sum over run counts `r` of the four start/end cases with weights `C(n_a-1, r_a-1) C(n_b-1, r_b-1) P_aa^{n_a - r_a} P_bb^{n_b - r_b} P_ab^{#a->b} P_ba^{#b->a}`, times `mu` of the start state; `K` (the largest run count kept) is `4 T max(Q_ab, Q_ba) + 14 sqrt(.) + 40`, and doubling `K` changes the maximizer value by `0.0`.
* full 3-state dynamic programme over `(current state, n_0, n_1)` for `N <= 300`, and a capped dynamic programme over `(state, n_i, n_k)` with `n_k <= L`.
* `n_k = 1` insertion formula: contract the single visit to `k`; the remaining `N-1` visits form a pair path, and the visit is inserted at the start (factor `mu_k P_{k s}/mu_s`), at the end (`P_{e k}`), or in one of the `N-2` gaps of type `x->y` (factor `P_xk P_ky/P_xy`); the sum over run counts is the pair formula with these multiplicities.

Validation (outputs `03_validate_output.txt`, `03_validate_fast_output.txt`, `03_validate_n1_output.txt`): against the full dynamic programme (`N = 60, 120`) the pair formula, the singleton formula and the capped programme agree to `1e-13` in log; the total probability of all compositions at `N = 60` is `1 - 3e-15`; the `n_k = 1` formula agrees with the capped programme to `3.6e-13` for all three choices of `k` at `N = 60, 150, 300`. The coarse-then-refine maximizer used for `N > 6000` (stride about `0.1 sqrt(N/T)`, then all compositions within three strides) agrees with the full computation to `0` at `N = 5000` and to `7.6e-6` at `N = 20000` (the reference there is itself on a stride-3 grid).

## 2. Task 1: finite-`N` coordinates

### 2.1 Pair-entry time `t_{ij,N}`

Definition used: the smallest `tau` at which `{i,j}` is the exact maximizer among the faces `{s}`, `{a,b}` (six faces), field `v_i = H`, `v_j = 0`, `v_k = -M`. It is located on an 18-point grid on `[0.25 t, min(1.25 t, stochastic cap)]` (sign of `log pair - log best singleton`), then by `brentq` to `1e-11`. For all 6 ordered pairs and all `N` the grid shows exactly one up-crossing and no down-crossing (script `03_task1_tables.py`, header line of each pair); at `tau_N -/+ 0.001 t` the six-face winner is `{i}` (below) and `{i,j}` (above) in all 90 cases (`03_task1_winners_output.txt`). Faces containing `k` are checked in 2.5.

Columns: `prediction = t (1 - log log N/(2 log N))`; `kappa_N = log N - T_N/t - (1/2) log T_N`, `T_N = t_{ij,N} log N`. If the crossing equation `T/t + (1/2) log T = log N - kappa` holds, `kappa_N -> kappa = log(K_pair/K_single)` up to the sign convention in the file (`kappa_N` is what one subtracts, not the log amplitude ratio itself).

Ordered pair (i,j) = (1,2), limiting t_ij = 3.53640

| N | t_ij,N | t_ij | prediction | (t_ij,N - prediction) log N | kappa_N |
|---:|---:|---:|---:|---:|---:|
| 200 | 1.54140 | 3.53640 | 2.97995 | -7.622 | 1.9389 |
| 500 | 1.75493 | 3.53640 | 3.01660 | -7.841 | 1.9360 |
| 1000 | 1.89370 | 3.53640 | 3.04170 | -7.930 | 1.9231 |
| 2000 | 2.01360 | 3.53640 | 3.06456 | -7.988 | 1.9089 |
| 5000 | 2.14747 | 3.53640 | 3.09170 | -8.042 | 1.8920 |
| 20000 | 2.30856 | 3.53640 | 3.12702 | -8.106 | 1.8738 |
| 100000 | 2.45155 | 3.53640 | 3.16112 | -8.169 | 1.8617 |
| 1000000 | 2.60353 | 3.53640 | 3.20034 | -8.245 | 1.8531 |

Ordered pair (i,j) = (1,3), limiting t_ij = 6.47750

| N | t_ij,N | t_ij | prediction | (t_ij,N - prediction) log N | kappa_N |
|---:|---:|---:|---:|---:|---:|
| 200 | 2.33982 | 6.47750 | 5.45826 | -16.522 | 2.1257 |
| 500 | 2.77326 | 6.47750 | 5.52541 | -17.104 | 2.1304 |
| 1000 | 3.06107 | 6.47750 | 5.57137 | -17.340 | 2.1177 |
| 2000 | 3.31250 | 6.47750 | 5.61326 | -17.488 | 2.1009 |
| 5000 | 3.59527 | 6.47750 | 5.66295 | -17.611 | 2.0790 |
| 20000 | 3.93598 | 6.47750 | 5.72766 | -17.744 | 2.0542 |
| 100000 | 4.23741 | 6.47750 | 5.79012 | -17.876 | 2.0378 |

Ordered pair (i,j) = (2,1), limiting t_ij = 4.22272

| N | t_ij,N | t_ij | prediction | (t_ij,N - prediction) log N | kappa_N |
|---:|---:|---:|---:|---:|---:|
| 200 | 1.71625 | 4.22272 | 3.55827 | -9.760 | 2.0411 |
| 500 | 1.96290 | 4.22272 | 3.60204 | -10.187 | 2.0751 |
| 1000 | 2.12671 | 4.22272 | 3.63200 | -10.398 | 2.0851 |
| 2000 | 2.27133 | 4.22272 | 3.65931 | -10.550 | 2.0882 |
| 5000 | 2.43654 | 4.22272 | 3.69171 | -10.691 | 2.0864 |
| 20000 | 2.64011 | 4.22272 | 3.73389 | -10.832 | 2.0798 |
| 100000 | 2.82411 | 4.22272 | 3.77461 | -10.943 | 2.0724 |
| 1000000 | 3.02136 | 4.22272 | 3.82143 | -11.053 | 2.0647 |

Ordered pair (i,j) = (2,3), limiting t_ij = 8.45626

| N | t_ij,N | t_ij | prediction | (t_ij,N - prediction) log N | kappa_N |
|---:|---:|---:|---:|---:|---:|
| 200 | 2.90516 | 8.45626 | 7.12566 | -22.362 | 2.1111 |
| 500 | 3.41425 | 8.45626 | 7.21332 | -23.610 | 2.1780 |
| 1000 | 3.76194 | 8.45626 | 7.27332 | -24.256 | 2.2059 |
| 2000 | 4.07694 | 8.45626 | 7.32800 | -24.711 | 2.2195 |
| 5000 | 4.44256 | 8.45626 | 7.39288 | -25.128 | 2.2260 |
| 20000 | 4.89961 | 8.45626 | 7.47735 | -25.529 | 2.2243 |
| 100000 | 5.31624 | 8.45626 | 7.55889 | -25.819 | 2.2179 |
| 1000000 | 5.76405 | 8.45626 | 7.65265 | -26.092 | 2.2097 |

Ordered pair (i,j) = (3,1), limiting t_ij = 8.83803

| N | t_ij,N | t_ij | prediction | (t_ij,N - prediction) log N | kappa_N |
|---:|---:|---:|---:|---:|---:|
| 200 | 2.87751 | 8.83803 | 7.44736 | -24.212 | 2.2111 |
| 500 | 3.40651 | 8.83803 | 7.53897 | -25.682 | 2.2930 |
| 1000 | 3.77198 | 8.83803 | 7.60168 | -26.455 | 2.3295 |
| 2000 | 4.10320 | 8.83803 | 7.65883 | -27.026 | 2.3520 |
| 5000 | 4.49087 | 8.83803 | 7.72664 | -27.560 | 2.3673 |
| 20000 | 4.98075 | 8.83803 | 7.81492 | -28.068 | 2.3731 |
| 100000 | 5.43156 | 8.83803 | 7.90015 | -28.421 | 2.3696 |

Ordered pair (i,j) = (3,2), limiting t_ij = 9.60324

| N | t_ij,N | t_ij | prediction | (t_ij,N - prediction) log N | kappa_N |
|---:|---:|---:|---:|---:|---:|
| 200 | 3.19464 | 9.60324 | 8.09217 | -25.949 | 2.1213 |
| 500 | 3.74487 | 9.60324 | 8.19172 | -27.635 | 2.2175 |
| 1000 | 4.12810 | 9.60324 | 8.25985 | -28.541 | 2.2631 |
| 2000 | 4.47794 | 9.60324 | 8.32195 | -29.218 | 2.2929 |
| 5000 | 4.89063 | 9.60324 | 8.39563 | -29.853 | 2.3149 |
| 20000 | 5.41661 | 9.60324 | 8.49156 | -30.453 | 2.3264 |
| 100000 | 5.90384 | 9.60324 | 8.58416 | -30.858 | 2.3255 |

Full tables for all `N` in {200, 300, 500, 700, 1000, 1500, 2000, 3000, 5000, 7000, 10000, 20000, 50000, 100000} (and 300000, 10^6 for pairs (1,2), (2,1), (2,3)) are in `03_task1_tables_output.txt`.

Observations.

* `t_{ij,N} < t_ij` always; the relative deficit `(t - t_N)/t` at `N=10^6` is `0.264`, `0.284`, `0.318` for pairs (1,2), (2,1), (2,3), and `0.346`, `0.385`, `0.385` at `N=10^5` for (1,3), (3,1), (3,2). It decreases slowly, as `log log N/log N` does.
* `(t_N - prediction) log N` is negative, of size 8 to 31 and slowly growing in absolute value; it is bounded in the range and approaches `-t(log t/2 + kappa_N)`: for pair (1,2) that expression is `-8.79` (with `kappa = 1.853` at `N = 10^6`) against the observed `-8.25`; the last column of the final section of `03_task1_tables_output.txt` lists these for every pair. (The limit is approached at rate `log log N/log N`, since `tau_N -> t` at that rate.)
* So the shape `t_N = t(1 - log log N/(2 log N)) + O(1/log N)` is consistent with the data, with an `O(1)` constant `-t(log t/2 + kappa)` that is not small (it is `-8` to `-33` here). A reader who compares `t_N` with `t` at `N` of a few thousand will see a deficit of more than one third, not the small correction one would picture.

### 2.2 Direct test of the `T^{1/2}` law at fixed `T`

`03_task1_scaling.py`, output `03_task1_scaling_output.txt`. For pairs (2,1) and (3,2) with `v = (H, 0)`: `X(T,N) = [M_pair/M_i] N T^{-1/2} e^{T(lam_pair - lam_i)}` for `T in {5, 10, 20, 40, 80}`, `N in {10^5, 10^6, 10^7}`. `X` is constant in `N` to 3 or 4 digits at `N >= 10^6` (e.g. pair (2,1), `T = 20`: `8.1401, 8.1432, 8.1436`), and in `T`:

| pair | X at T = 5, 10, 20, 40, 80 (N = 10^7) | X(2T)/X(T) for T = 5, 10, 20, 40 |
|---|---|---|
| (2,1) | 10.030, 8.841, 8.144, 7.893, 7.784 | 0.881, 0.921, 0.969, 0.986 |
| (3,2) | 8.778, 12.833, 12.138, 10.682, 10.210 | 1.462, 0.946, 0.880, 0.956 |

A power `T^{p}` instead of `T^{1/2}` would make these ratios `2^{p - 1/2}`; the observed ratios are within `0.12` of 1 for `T >= 10` and the deviations shrink in `T` for pair (2,1) (`-0.18, -0.12, -0.045, -0.02` in `log_2`). For pair (3,2) the sequence is not monotone, within `-0.2 .. +0.1` of zero. This supports the exponent `1/2` of `T` in `M_F` (hence the coefficient `Delta/2 = 1/2` in the crossing equation) with an `O(1/T)` correction of size of order one for `T` up to 80.

### 2.3 Is the coefficient `1/2` of `log log N/log N` supported?

Fits, all in `03_task1_tables_output.txt` (columns for `N >= 1000` and `N >= 5000`):

(a) The requested regression `(t - t_N)/t = a (log log N)/(log N) + c/(log N)`:

| pair | a (N>=1000) | a (N>=5000) | c (N>=1000) |
|---|---:|---:|---:|
| (1,2) | 0.628 | 0.619 | 2.00 |
| (1,3) | 0.660 | 0.635 | 2.37 |
| (2,1) | 0.734 | 0.682 | 2.02 |
| (2,3) | 0.831 | 0.743 | 2.25 |
| (3,1) | 0.953 | 0.826 | 2.14 |
| (3,2) | 0.992 | 0.851 | 2.04 |

These are all above `0.5`, and the value is not stable in the window. This regression is not a clean test, for two reasons that can be checked in the tables. First, the exact structure of the crossing equation is `(t - t_N)/t = [ (1/2) log T_N + kappa ]/log N`, and `log T_N = log log N + log t_N` where `log t_N` moves by `0.3` to `0.4` over the window (not constant), so the regressor `1/log N` absorbs a drifting term. Second, the two regressors are almost collinear on `N in [10^3, 10^6]` (`log log N` changes by `0.7` while `log N` changes by `6.9`), and `O(1/T)` corrections (`T = 15` to `80`) are of the size of the effect. The regression is reported because it was requested; its output is not evidence for `a = 1/2` nor against it.

(b) The structural fit `y = log N - T_N/t = p log T_N + kappa` (free exponent `p`, prediction `p = 1/2`), `N >= 1000`: `p = 0.428, 0.401, 0.477, 0.499, 0.543, 0.569` for pairs (1,2), (1,3), (2,1), (2,3), (3,1), (3,2); for `N >= 5000`: `0.442, 0.411, 0.468, 0.477, 0.504, 0.520`. Adding a `beta/T` term makes the fit unstable (`p` from `0.31` to `0.55`): it is not identifiable on this range.

(c) Local exponent from the drift of `kappa_N` between `N = 10^4` and the largest `N` computed: `p_eff = 1/2 + Delta kappa_N/Delta log T_N` equals `0.449, 0.419, 0.468, 0.473, 0.494, 0.507` for pairs (1,2), (1,3), (2,1), (2,3), (3,1), (3,2). If the true exponent were `1` the drift of `kappa_N` over this range would be about `0.3`; it is `0.003` to `0.03`.

(d) Cross-check of the crossing equation with the fixed-`T` amplitude of 2.2. If `M_pair/M_i = X(T) N^{-1} T^{1/2} e^{-T(lam_pair - lam_i)}` then `kappa_N = log N - T_N/t - (1/2) log T_N` must equal `log X(T_N)` (with `X` evaluated at `N = infinity`). Pair (2,1), `N = 10^6`: `T_N = 41.74`, `kappa_N = 2.0647`, `log X(40) = 2.066`, `log X(80) = 2.052`. Pair (3,2), `N = 10^5`: `T_N = 67.97`, `kappa_N = 2.3255`, `log X(40) = 2.369`, `log X(80) = 2.323`. Pair (2,1) agrees to `0.003`; for pair (3,2), `kappa_N` lies between `log X(40)` and `log X(80)` and nearer the latter, as `T_N = 68` is, i.e. agreement to about `0.01`. This ties the exact crossing to the face-maximum scaling `N^{-1} T^{1/2}` with no fitted parameter.

Reading: the data are consistent with `1/2` to within about `0.1` and show no sign of any other value; no value of the coefficient is excluded other than ones differing from `1/2` by more than about `0.1`. The sign is checked by the direction of every table: `t_{ij,N} < t_ij`, and the size of the leading `log T` term at `T` of order 30 (`(1/2) log T/log N` of order `0.15`) is far smaller than the amplitude term (`kappa/log N` of order `0.2`) at accessible `N`, which is why (a) is not informative.

### 2.4 Singleton switch `x_{i,N}`

At `tau_0` with retained pair `(i,1)` (`v_i = delta`, `v_1 = 0`, `v_k = -M`) the singleton crossing is exact in closed form:
`x_{i,N} = [ (N-1) log((1 - T q_1/N)/(1 - T q_i/N)) + log(mu_1/mu_i) ]/T`, `T = tau_0 log N`.
Hence `x_{i,N} - x_i = log(mu_1/mu_i)/(tau_0 log N) + O(T/N)`, with `x_i = q_i - q_1`. Checked against the exact winner over a window of `delta` (601 points, `N <= 5000`, all six faces): the only transition is `{1} -> {i}`, at the closed-form value to within the grid spacing `10^{-3}`, and the pair `{1,i}` loses throughout by at least `e^{4.1}` (`N = 200`) growing to `e^{9.6}` (`N = 10^5`, evaluated at the switch only). Table (`03_task1_tables_output.txt`, last section):

| i | N | x_{i,N} | x_i | (x_{i,N} - x_i) log N | log(mu_1/mu_i)/tau_0 |
|---:|---:|---:|---:|---:|---:|
| 2 | 200 | -0.819912 | -0.817143 | -0.0147 | 0 |
| 2 | 5000 | -0.817419 | -0.817143 | -0.0024 | 0 |
| 2 | 100000 | -0.817164 | -0.817143 | -0.0002 | 0 |
| 3 | 200 | -1.861881 | -1.385000 | -2.5267 | -2.5082 |
| 3 | 5000 | -1.679876 | -1.385000 | -2.5115 | -2.5082 |
| 3 | 100000 | -1.602890 | -1.385000 | -2.5085 | -2.5082 |

So `x_{i,N} = x_i + O(1/log N)` holds in this example with the explicit coefficient `log(mu_1/mu_i)/tau_0`; this is an identity for the singleton comparison, and the numerics add only that the pair never interferes at `tau_0`.

### 2.5 Faces containing the suppressed state at the pair-entry points

`03_task1_triple.py`, `03_task1_triple_output.txt`: at `tau_N` for each pair and `N = 200, 500, 1000, 2000`, the best composition with full support (`n_k >= 1`; full law for `N = 200`; `n_k <= L`, `L = 2` to `5`, for larger `N`) lies below the winner by `112` to `231` (`N=200`), `60` to `127` (`500`), `37` to `78` (`1000`), `22.5` to `46.7` (`2000`) in log scale; the bound `T H - M T (L+1)/N` for `n_k > L` is below the winner value in all 24 rows. The margin decays at roughly the rate `M T/N`: the field penalty `e^{-M T/N}` for a single visit to `k` is the reason. Section 3.4 shows what happens beyond `N = 2000`.

### 2.6 Reconstruction with the finite-`N` coordinates

`03_task1_reconstruct.py` (`03_task1_reconstruct_output.txt`). Edge products from `(x_{i,N}, t_{ij,N})` by `w_ij = (H - d_i + d_j)/t + t^{-2}` with `d_i = x_{i,N}`, edges (1,2), (1,3), (2,3) taken from ordered pairs (1,2), (1,3), (2,3):

| N | `||Q_N-Q||_2` raw | after `t -> t/(1 - log log N/(2 log N))` | corrected times `log N` |
|---:|---:|---:|---:|
| 200 | 2.452 | 1.923 | 10.19 |
| 1000 | 1.729 | 1.318 | 9.10 |
| 5000 | 1.326 | 0.986 | 8.39 |
| 20000 | 1.107 | 0.807 | 8.00 |
| 100000 | 0.931 | 0.667 | 7.68 |

`||Q||_2 = 4.41`, so the absolute errors are large at these `N`. Raw error divided by `log log N/log N` goes `7.8, 6.2, 5.3, 4.8, 4.4`; corrected error times `log N` goes `10.2` to `7.7`. Both are bounded and slowly decreasing, consistent with the two stated rates and with a large constant. The corrected error is smaller than the raw one by 20 to 30 percent over the range (`0.667` against `0.931` at `N = 10^5`), which is what removing the log-log part of a deficit that is mostly the amplitude constant would give.

## 3. Task 2: adversarial search

### 3.1 Design of the scan

For each configuration (a 3-state reversible generator and a start `mu`), all of the following are exact computations at each `N` of a list:

* grid of the protected rectangle: `tau` at 9 geometric points from `1/(4R)` to `U`, `delta` at 13 equispaced points on `[-3R, 3R]`, all 6 ordered retained pairs `(i,j)` with `v_i = delta`, `v_j = 0`, `v_k = -M` (702 cells per `N`, fewer for the path graph);
* predicted winner: smallest `Phi_{tau,v}(F)` over all connected faces; the leading gap is second smallest minus smallest `Phi`; cells whose predicted winner is the full triple are dropped (none occurs);
* exact winner among the six faces `{s}`, `{a,b}` (pair profiles on a stride grid of about `0.15 sqrt(N/T)` plus the 30 compositions at each end, error about `0.01` in log);
* the full triple is treated separately in Section 3.4;
* a `tau` slice is "not admissible" at `N` if `T q_max >= 0.97 N` (the matrix `I + (T/N)Q` is not stochastic enough), and "skipped" if the pair profile would exceed `4*10^8` operations; skipped slices are excluded and the number evaluated is listed;
* the onset is the smallest `N` of the list from which no evaluated cell with leading gap `>= g0` has a wrong exact winner, for `g0 = 0.75` (the theoretical gap of the suppression lemma, `3/4`) and `g0 = 0.5`. Cells with smaller gap are excluded because the onset there is unbounded by definition (it grows like `exp(c/gap)` as a cell approaches a boundary), so it cannot test boundedness.

Configurations (`03_task2_scan.py`; stationary law, conductances, start; `b/R` is the ratio of the class parameters):

* `base`: as Section 1. `path`: same `pi`, edge (1,3) removed. `weak13_a, _b`: conductance `c_13 = 0.10, 0.03` (`b/R = 0.081, 0.025`). `unequal_a`: `pi = (0.8, 0.15, 0.05)`; `unequal_b`: `pi = (0.9, 0.09, 0.01)`. `start_a, _b, _c`: base generator with `mu = (0.90, 0.05, 0.05)`, `(0.98, 0.01, 0.01)`, `(0.998, 0.001, 0.001)`. `unequal_start`: `pi = (0.9, 0.09, 0.01)`, `mu = (0.02, 0.49, 0.49)`.

### 3.2 Results

| config | pi | min mu | b/R | R | U | N_adm | tau slices evaluated at largest N | onset, gap>=0.75 | onset, gap>=0.5 |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| base | (0.25, 0.35, 0.4) | 0.300 | 0.227 | 4.36 | 36 | 1000 | 9/9 | <= 300 | 3000 |
| path | (0.25, 0.35, 0.4) | 0.300 | 0.259 | 3.82 | 31 | 1000 | 9/9 | <= 1000 | <= 1000 |
| start_a | (0.25, 0.35, 0.4) | 0.050 | 0.227 | 4.36 | 36 | 1000 | 9/9 | <= 1000 | 30000 |
| start_b | (0.25, 0.35, 0.4) | 0.010 | 0.227 | 4.36 | 36 | 1000 | 9/9 | 10000 | > 100000 |
| start_c | (0.25, 0.35, 0.4) | 0.001 | 0.227 | 4.36 | 36 | 1000 | 9/9 | 100000 | > 100000 |
| unequal_a | (0.8, 0.15, 0.05) | 0.300 | 0.121 | 4.13 | 132 | 10000 | 7/9 | <= 1000 | 100000 |
| unequal_b | (0.9, 0.09, 0.01) | 0.300 | 0.078 | 8.13 | 163 | 30000 | 7/9 | 10000 | > 300000 |
| unequal_start | (0.9, 0.09, 0.01) | 0.020 | 0.078 | 8.13 | 163 | 30000 | 7/9 | 300000 | > 300000 |
| weak13_a | (0.25, 0.35, 0.4) | 0.300 | 0.081 | 3.90 | 312 | 10000 | 7/9 | <= 1000 | 100000 |
| weak13_b | (0.25, 0.35, 0.4) | 0.300 | 0.025 | 3.84 | 3415 | 100000 | 5/9 | 30000 | 30000 |

Entries "N_adm" is the first listed `N` at which all nine `tau` slices are admissible. `N` lists: base 300 to `10^5`; others `10^3` to `10^5` or `3*10^3` to `3*10^5`. A "<=" means no wrong cell even at the smallest listed `N`, so the onset is not resolved below it. Per-slice tables (`03_task2_slices.py 0.5 <config>` and `0.75`), cell lists and counts are in the `03_task2_<config>.json` files.

Reading:

* Dependence on `mu_*`. With the base generator the onset at `g0 = 0.75` is `<= 10^3` (`mu_* = 0.3, 0.05`), `10^4` (`0.01`), `10^5` (`0.001`): a factor 10 for each factor 10 in `mu_*`; at `g0 = 0.5` it is `3*10^3`, `3*10^4`, `> 10^5`, `> 10^5`. The failing cells are those where the predicted winner is a singleton or pair other than the one the start favours, with a leading gap just above the threshold; the mechanism is the two-state one of Section 3.3: the predicted winner wins only when `N^{gap} mu_pred/mu_start` exceeds 1 (with ratios of the constants `K`), so the onset is expected to behave like `(mu_*)^{-1/gap}` (the data are consistent with this, not a fit).
* Dependence on `b/R` and on unequal `pi`. At `mu_* = 0.3` and `g0 = 0.75` all edge cases (`b/R` from `0.227` down to `0.025`, `U` up to 3415) have onset at the trivial stochasticity threshold `N_adm` or at most one list step above it (`unequal_b`: `10^4` against `N_adm = 3*10^4`, i.e. below `N_adm` because only admissible slices are tested), and at `g0 = 0.5` the onset is `10^5` for `unequal_a` and `weak13_a` and larger than `3*10^5` for `unequal_b`. Since `N_adm ~ U q_max log N/0.97 ~ 8R q_max log N/b^2`, the minimum `N` at which the design rectangle exists at all grows like `b^{-2}`; this is not an analytic failure but it means a class-uniform common onset must depend on `b` at least this way. Beyond that, a growth of the analytic onset with `b/R -> 0` could not be separated from the growth with `U` because for `weak13_b` the slices with `tau >= 58` (4 of 9) could not be evaluated at the largest `N`.
* The combination of both mechanisms (`unequal_start`) has the largest onset, `3*10^5` at `g0 = 0.75` and not reached at `g0 = 0.5` by `3*10^5`.
* The cells that are wrong at large `N` at `g0 = 0.5` (last column of the `03_task2_analyze.py` output) all have leading gap `0.52` to `0.58`: they are the near-threshold cells, not cells deep inside the rectangle. In the listed cells of the small-`mu_*` configurations the exact winner is the face containing state 1, which carries start mass `0.98` or `0.998`, while the predicted winner is a face without it.
* Path graph (a nonedge pair retained): no wrong cell at `g0 = 0.5` for `N >= 10^3`.

Conclusion for this part: over the scanned family the onset is finite for each fixed gap threshold, does not diverge at fixed `(b, mu_*)` as the other parameters vary, and grows polynomially (about `mu_*^{-1}` to `mu_*^{-2}` for `g0` between `0.75` and `0.5`, and at least like `b^{-2}`) toward the edges of the class. This is the behaviour a compact-class common onset would have; it does not by itself show uniformity, because (i) the grids are coarse, (ii) the top of the `tau` range is not evaluated for the weakest-edge configurations, and (iii) cells with small gap are excluded.

### 3.3 The two-state counterexample over all starts

`03_twostate.py`, `03_twostate_output.txt`. Rate-one chain `Q = [[-1,1],[1,-1]]`, `v = (0, 1)`, `tau = 1/4`. Leading scores `Phi{1} = 0.2500`, `Phi{2} = 0`, `Phi{1,2} = 0.8455`: predicted winner `{2}`.

With `mu_2 = 1/(1 + c N^{1/4})` the ratio `w{2}/w{1} = (mu_2/mu_1) e^{T} = 1/c` exactly for every `N` (the factor `(1 - T/N)^{N-1}` is common): for `c = 2` it is `0.5000` at `N = 10^2, 10^6, 10^{10}, 10^{14}, ..., 10^{38}` (singleton formulas), and the exact winner is `{1}` at every `N` from `10^2` to `10^7` checked with the pair included (the pair is lower by `e^{-2.9}` at `N=100` to `e^{-9.3}` at `10^7` relative to the better singleton). For `c = 0.5` the ratio is 2 and `{2}` wins, for `c = 1` it is a tie (the one `{2}` entry at `N = 10^5` in the table is a rounding artifact of the tie). So no `N`-independent onset exists over all starts.

For a fixed start `mu_2` the onset (smallest `N` after which `{2}` stays the exact winner, no pair win seen at `N <= 10^6`):

| mu_2 | 0.5 | 0.2 | 0.1 | 0.05 | 0.02 | 0.01 | 0.005 |
|---|---:|---:|---:|---:|---:|---:|---:|
| onset N | 10 | 259 | 6571 | 1.31e5 | 5.77e6 | 9.62e7 | 1.57e9 |
| (mu_1/mu_2)^4 | 1 | 256 | 6561 | 1.30e5 | 5.77e6 | 9.61e7 | 1.57e9 |

The onset follows `(mu_1/mu_2)^4` to within `1%`: the loss of compactness at `mu_* -> 0` is the whole mechanism here (the amplitude ratio `mu_2/mu_1` competes with `N^{1/4}`, the exponent being the leading-score gap `1/4` between the two singletons).

### 3.4 Full-support faces with one visit to the suppressed state

The six-face comparison omits compositions that visit the suppressed state `k`. For `n_k >= 1` compositions the field factor is `e^{-M T n_k/N}`, which tends to 1 once `N >> M T`; the remaining penalty is combinatorial (one inserted visit costs about `(T^2/N)` times a constant, against the predicted gap `N^{-3/4}`). For this reason it was computed exactly: for each cell with leading gap `>= 0.5`, margin = `log(best of the six faces) - log(best composition with n_k = 1)`, using the validated insertion formula (`03_task2_n1.py`). The capped dynamic programme with `n_k <= L = 3` (`03_task2_triple.py`, `03_task2_triple_base_output.txt`, `N <= 3*10^4`, `tau` = 1.43 and `U`) found the best full-support composition at `n_k = 1` in every case, which is why `n_k = 1` is the one tabulated.

Minimum over cells of the margin (log scale; "-" inadmissible, "s" skipped for cost), base generator:

### base: R=4.359 b=0.9889 U=35.7 M=2728
| tau | N=1e+03 | N=3e+03 | N=1e+04 | N=3e+04 | N=1e+05 | N=3e+05 | N=1e+06 | N=3e+06 | N=1e+07 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0.057 | 14.05 | 15.23 | 17.02 | 18.84 | 20.93 | 22.89 | 25.05 |  |  |
| 0.128 | 13.35 | 13.67 | 15.08 | 16.76 | 18.77 | 20.67 | 22.80 |  |  |
| 0.286 | 14.03 | 12.45 | 12.98 | 14.28 | 16.05 | 17.80 | 19.76 |  |  |
| 0.640 | 16.72 | 10.68 | 9.14 | 9.55 | 10.72 | 12.04 | 13.61 |  |  |
| 1.430 | 28.41 | 12.70 | 6.82 | 5.46 | 5.56 | 6.19 | 7.11 |  |  |
| 3.196 | 59.62 | 23.51 | 9.22 | 5.07 | 4.07 | 4.35 | 5.12 |  |  |
| 7.142 | 132.30 | 50.62 | 17.53 | 7.17 | 3.71 | 3.20 | 3.68 |  |  |
| 15.959 | 296.49 | 113.14 | 38.06 | 13.83 | 4.87 | 2.61 | 2.41 | 2.97 | 3.87 |
| 35.664 | 664.32 | 254.69 | 85.91 | 30.67 | 9.45 | 3.26 | 1.54 | 1.63 | 2.35 |


The margin is positive in all computed cells. It decreases with `N` while the field penalty `M T/N` dominates, passes a minimum near `N ~ M T`, and then rises. For the base generator the minima are `4.07` (`tau = 3.2`, `N = 10^5`), `3.20` (`tau = 7.1`, `3*10^5`), `2.41` (`tau = 16`, `10^6`) and `1.54` (`tau = U`, `10^6`), and the margin at `tau = U` rises again to `1.63` and `2.35` at `N = 3*10^6, 10^7`. The minimum value falls with `tau` (`4.07, 3.20, 2.41, 1.54`) but does not reach zero.

For the generators with small `b` the minimum is beyond the largest `N` computed (`N = 10^6`) for `tau >= 4.5` (weak13_a), `tau >= 2.2` (unequal_b), `tau >= 3.2` (start_c, largest `N = 3*10^5`):

### weak13_a: R=3.895 b=0.3162 U=311.6 M=18925
| tau | N=1e+04 | N=3e+04 | N=1e+05 | N=3e+05 | N=1e+06 |
|---:|---:|---:|---:|---:|---:|
| 0.064 | 18.15 | 19.35 | 21.18 | 23.04 | 25.16 |
| 0.185 | 17.26 | 17.09 | 18.35 | 20.00 | 22.02 |
| 0.536 | 18.30 | 13.88 | 13.17 | 13.91 | 15.26 |
| 1.548 | 30.93 | 14.90 | 9.20 | 7.99 | 8.19 |
| 4.472 | 78.96 | 30.98 | 12.63 | 7.36 | 5.99 |
| 12.921 | 223.93 | 83.64 | 28.76 | 11.81 | 5.94 |
| 37.330 | 646.94 | 239.99 | 79.59 | 28.88 | 9.97 |
| 107.852 | 1873.74 | 696.38 | 231.08 | s | s |
| 311.601 | 5421.65 | 2018.94 | s | s | s |


### unequal_b: R=8.128 b=0.6325 U=162.6 M=42987
| tau | N=1e+04 | N=3e+04 | N=1e+05 | N=3e+05 | N=1e+06 |
|---:|---:|---:|---:|---:|---:|
| 0.031 | 19.35 | 20.54 | 22.40 | 24.29 | 26.46 |
| 0.090 | 19.22 | 18.91 | 20.16 | 21.85 | 23.92 |
| 0.262 | 23.27 | 18.65 | 18.17 | 19.29 | 21.11 |
| 0.766 | 39.83 | 22.54 | 16.92 | 16.26 | 17.26 |
| 2.236 | 91.68 | 37.08 | 16.11 | 10.02 | 8.34 |
| 6.529 | 259.00 | 97.87 | 34.74 | 15.15 | 8.25 |
| 19.065 | 753.10 | 280.88 | 94.64 | 35.68 | 13.57 |
| 55.670 | 2199.89 | 819.32 | s | s | s |
| 162.557 | - | 2395.68 | s | s | s |


### start_c: R=4.359 b=0.9889 U=35.7 M=2728
| tau | N=3e+03 | N=3e+04 | N=3e+05 |
|---:|---:|---:|---:|
| 0.057 | 9.70 | 13.38 | 17.48 |
| 0.128 | 8.38 | 11.57 | 15.51 |
| 0.286 | 7.55 | 8.64 | 12.13 |
| 0.640 | 7.62 | 6.08 | 7.60 |
| 1.430 | 10.71 | 4.84 | 6.22 |
| 3.196 | 20.55 | 2.33 | 1.79 |
| 7.142 | 48.38 | 5.13 | 1.33 |
| 15.959 | 111.60 | 12.45 | 1.38 |
| 35.664 | 253.90 | 29.84 | 2.53 |

Margins at `tau = 37` for `weak13_a` (`M = 18925`) go `647, 240, 80, 29, 10` over `N = 10^4 ... 10^6` and are still falling by a factor of about `2.9` per factor `3.3` in `N`; the dip is expected near `N ~ M T ~ 10^7`, beyond what was computed (slices above `tau = 37` are skipped). `unequal_b` shows the same: `753, 281, 95, 36, 13.6` at `tau = 19`. For `start_c` (`mu_* = 0.001`) the margins at mid `tau` are already `1.3` to `1.8` at `N = 3*10^5`. The scaling of the dip with `M ~ U R^2 ~ b^{-2}` is an extrapolation from the base case (dip at `N ~ M T` for `tau` from 3 to `U`), not a computed fact for the weak generators.

## 4. What this does and does not show

Shown (computationally, for one generator and one start, with exact arithmetic of the law): the finite-`N` controlled maximizers behave as the heuristic crossing equation says in sign, in the `T^{1/2}` exponent (to about `0.1`), and the corrected recovery rates are bounded as claimed; the singleton switch converges at rate `1/log N` with the explicit constant `log(mu_1/mu_i)/tau_0`; the leading-score winner is the exact winner on the protected rectangle from an onset that behaves like a power of the edge parameters over the scan, and the full-support faces with one visit to `k` stay below the predicted winner with a margin that has a positive minimum in the base case.

Not shown: any uniformity statement. One generator was used for Task 1. The scan has coarse grids, excludes small-gap cells, and for the weakest edges does not reach the top of the `tau` range nor the minimum of the full-support margin. Compositions with `n_k >= 2` and single visits to other states were only sampled by the capped programme at `N <= 3*10^4`. The fitted constants are numerical.

Relevance to (5b). No numerical counterexample inside the class was found; the observed growth of the onset is as one expects from the compactness mechanism (power of `1/mu_*`, powers of `1/b`, via `U` and `M`). The step that the numerics flag as the least controlled is the one that sets the common onset at the edges: the full-support margin near `N ~ M T`, where the field suppression has stopped working and the combinatorial `N^{-3/4}` loss has not yet taken over. For `b` small the location of this dip scales like `M ~ b^{-2}` and the value of the margin at the dip is not known; in the base case it is positive (`1.5`) and decreasing in `tau`.

## 5. Archive

Scripts: `03_core.py` (exact laws), `03_validate.py`, `03_validate_fast.py`, `03_validate_n1.py`, `03_task1_compute.py` (pair-entry and switch; results in `03_task1_results.json`), `03_task1_tables.py`, `03_task1_md_tables.py`, `03_task1_winners.py`, `03_task1_scaling.py`, `03_task1_triple.py`, `03_task1_reconstruct.py`, `03_twostate.py`, `03_task2_scan.py` (+ `03_task2_analyze.py`, `03_task2_slices.py`, `03_task2_md_table.py`), `03_task2_triple.py`, `03_task2_n1.py`, `03_task2_n1_table.py`. Outputs: `03_*_output.txt`, `03_task1_results.json`, `03_task2_<config>.json`, `03_task2_n1_<config>*.json`.

Status: inconclusive (numerical evidence only, no proof). The computations support (5a): sign and size of the `log log N/(2 log N)` correction (coefficient `1/2` within about `0.1`), `O(1/log N)` for `x_{i,N}`, uniqueness of the maximizing support in the examples, and the stated reconstruction rates; they exhibit the two-state loss of uniformity over starts exactly. For (5b) they find no counterexample inside the class and a polynomial growth of the onset toward the edges. The first unresolved implication is a uniform lower bound, over the class, on the margin of the faces containing the suppressed state at the intermediate range `N ~ M T` (for generators with small `b` the minimum of this margin was not reached).
