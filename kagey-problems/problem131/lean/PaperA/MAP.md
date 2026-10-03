# Paper A: map from the paper to the Lean theorems

This file matches the statements of Paper A (`paperA/problem131.tex` and the files it inputs) to
the Lean theorems of the library `PaperA` (root `PaperA.lean`, 19 modules in `PaperA/`, namespace
`Kagey131`). The library uses Lean 4 v4.33.1 and Mathlib v4.33.1. Every theorem listed here is
proved without `sorry`, `admit` or new axioms, and `#print axioms` on each of them reports only
`propext`, `Classical.choice` and `Quot.sound` (see `build-log.txt`).

The key of each row is the `\label` in the source. The column Number gives the number in the built
PDF. The numbers can change when the paper is edited, and the labels do not. "In part" means that
the exact or finite core of the statement is in Lean and the rest is listed under "Not in Lean"
below. Each Lean statement was compared by hand with the statement in the paper, and the section
"Differences between the Lean statements and the paper" records every place where the two are not
word for word the same.

## Conventions

| Paper | Lean |
| --- | --- |
| A word `w` with `N` letters, `R` and `L` | `Word N = Fin N → Bool`, with `true` for `R` |
| `chg(w)`, `rep(w)`, the bin of `w` | `chg`, `rep`, `numR` |
| `P(w)`, equation (1) (`eq:wordprob`) | `wordProb p w`, and `1` for the empty word |
| `P_N(k)` | `binProb p N k`, and `0` for `k > N` |
| `P_N^R(k)`, `P_N^L(k)` | `endProb p (N-1) k true`, `endProb p (N-1) k false` |
| `W(N,k,j)` | `W N k j`, and `0` for `j = 0` |
| `S_{a,b}(u)`, `S_N(u)` | `Sab a b u`, `SN N u = Sab (N/2) (N - N/2) u` |
| `u_{a,b}`, `p_{a,b}`, `u_N`, `p_N` | `uab a b`, `pab a b = 1/(1 + uab a b)`, `uN N`, `pN N` |
| `z_N` | written out as `N * (1 - pN N)` |
| `I_0(z)`, `I_1(z)` | `besselI0 z`, `besselI1 z`, defined by their power series |
| `F(x)`, `Φ(w)` | `Fcent x`, `Fcent (w/2)` |
| `E(z)` | `besselE z` |
| `ζ_N` | `zetaN N`, the positive root of `8 ζ e^{2ζ} = π N²` |
| `ε_N` | written out as `ζ_N(ζ_N+1)/N + 1/(16 ζ_N²)` |
| `U_r(m)`, and `A_r`, `B_r` | `normCoeff m m r`, and `normCoeff a h r`, `normCoeff b h r` |
| `Ŝ_{a,b}(u)`, `J_c(x)`, `G_η(x)` | `Tab a b u`, `Jc c x`, `Geta η x` |
| the root `x_B` of `G_η(x_B) = A` | `Groot η A` |
| `p_N^adj` | `padj N` |
| `H_a(y)`, `y_a` | `Hedge a y`, `yEdge a` |
| `S^P_{N,k}(u)`, `Ŝ^P_{N,k}(u)` | `perRatio N k u`, `perT N k u` |
| `n_N(k)` for `p = α/(α+β)` | `numer α β N k` |

## Modules

| Module | Content |
| --- | --- |
| `Model` | words, the exact law, the two-state recursion and the count of words by switches |
| `Recurrence` | the recurrence, the generating function, the numerators and the mean and variance |
| `NormalLimit` | the normal limit |
| `RunAlgebra` | falling products and the algebra of the adjacent crossings, over the integers and rationals |
| `Crossing` | the ratio `S_{a,b}`, the crossings, their ordering, the central crossing and the adjacent bins |
| `Bessel` | `I_0` and `I_1` as power series and the three weighted sums |
| `BesselDeriv` | derivatives of the series, `I_0 > I_1`, the function `G_η` and the root comparison |
| `FiniteBessel` | clipped products and their deficits, over the rationals |
| `UniformBessel` | the uniform Bessel bounds for the center, every bin, the periodic chain and the edge |
| `RootBounds` | the crossings against the Bessel roots |
| `Asymptotics` | `1 - p_N ~ (log N)/N` and the bound on `u_N - u_B` |
| `AllbinAsymptotics` | the leading term for every bin, and the periodic ordering |
| `Edge` | the polynomial `H_a`, its root `y_a` and the exact edge series |
| `EdgeExpansion` | the algebra of the coefficients of the edge expansion, over the rationals |
| `Periodic` | the cyclic count and the periodic ratio |
| `BesselIntegral` | the integral form of `I_0 + I_1` and the bounds on `E` |
| `EveryN` | the root bracket, `ζ_N`, and the crossing for `2 ≤ N ≤ 174` by certificates |
| `EveryNLarge` | the crossing for `N ≥ 175` and for every `N ≥ 2` |
| `Tables` | the numerator tables as lattice-path counts, kept in the repository for the tables note |

## Section 1, setting and notation

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `eq:wordprob` | (1) | `P(w) = (1/2) p^rep q^chg`, with `rep + chg = N - 1`, and the law has total mass 1 | `wordProb`, `rep_add_chg`, `wordProb_eq_of_pos`, `sum_wordProb`, `sum_binProb` | `Model` |
| `sec:setting` | 1.2 | `P_N(0) = P_N(N) = p^(N-1)/2` and `P_N(k) = P_N(N-k)` | `binProb_zero_bin`, `binProb_last_bin`, `binProb_symm` | `Model` |
| `sec:setting` | 1.2 | `P_N(a) = P_N(0) S_{a,b}(u)` for `p > 0` | `binProb_eq_mul_Sab`, `SN_eq_ratio` | `Crossing` |
| `eq:zN` | (2) | `z_N = N(1 - p_N) = N u_N/(1 + u_N)` | `N_one_sub_pN` | `EveryN` |

## Section 2, the exact law

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `thm:pmf` | 2.1 | the endpoints, and `P_N(k) = (1/2) Σ_j W(N,k,j) p^(N-1-j) q^j` for `1 ≤ k ≤ N-1` | `binProb_zero_bin`, `binProb_last_bin`, `binProb_eq_W` | `Model` |
| `thm:pmf` | 2.1 | `W(N,k,j)` is the number of words with `k` letters `R` and `j` switches | `card_words_eq_W`, with `cnt_eq_cntFormula`, `W_odd`, `W_even` | `Model` |
| `prop:gf` | 2.2 | the initial values of `P_1^R`, `P_1^L` | `endProb_zero_true`, `endProb_zero_false`, `binProb_eq_endProb` | `Model` |
| `eq:dp` | (3) | the two-state recursion | `endProb_succ_true`, `endProb_succ_true_zero`, `endProb_succ_false` | `Model` |
| `eq:gf` | (4) | the generating function | `probGF_eq` | `Recurrence` |
| `eq:rec` | (5) | the three-term recurrence, for every `N ≥ 2` and every `k` | `binProb_rec`, `binProb_rec_zero`, `rowPoly_rec` | `Recurrence` |
| `rem:tables` | 2.3 | `n_N(k) = 2(α+β)^(N-1) P_N(k)` is the sum of `α^rep β^chg`, an integer | `numer_eq`, `numer_cast` | `Recurrence` |
| `prop:var` | 2.4 | `E K_N = N/2`, both closed forms of `Var K_N` for `p < 1`, and `N²/4` at `p = 1` | `meanK_eq`, `varK_eq_closed`, `varK_eq_closed'`, `varK_eq_one` | `Recurrence` |
| `thm:clt` | 2.5 | the normal limit for fixed `0 < p < 1` | `normal_limit`, with `charPhi_rec`, `charPhi_closed`, `tendsto_charPhi`, `charFun_lawZ` | `NormalLimit` |

## Section 3, the central crossing at every N

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `eq:SN` | (6) | `S_N` is a polynomial with coefficients `W(N,m_N,j)`, linear coefficient 2 | `SN`, `Sab`, `SN_eq_ratio`, `W_one` | `Crossing` |
| `thm:root` (a) | 3.1 | exactly one `p_N` in `[0,1]`, `p_N ≥ 2/3`, and the sign on each side | `thm_root_a`, `pab_mem`, with `Sab_strictMonoOn`, `Sab_exists_root`, `Sab_eq_one_iff`, `two_mul_le_Sab` | `Crossing` |
| `thm:root` (b) | 3.1 | `p_2 = 2/3`, `p_3 = 1/√2`, the cubic for `p_4`, and `p_N < p_{N+1}` for `N ≥ 2` | `pN_two`, `pN_three`, `pN_four_cubic`, `pN_four_unique`, `pN_lt_succ`, `uN_lt_succ` | `Crossing` |
| `thm:root` (c) | 3.1 | `p_N → 1` and `1 - p_N ~ (log N)/N` | `thm_root_c`, with `uN_lower`, `uN_upper`, `tendsto_N_uN_div_log`, `tendsto_uN` | `Asymptotics` |
| `lem:clipped` (a) | 3.2 | `0 ≤ 1 - Π(1 - t_k)_+ ≤ Σ t_k` | `finite_product_deficit`, `clip_bounds`, `product_deficit`, and `prod_deficit` for two real factors | `FiniteBessel`, `UniformBessel` |
| `lem:clipped` (b) | 3.2 | `0 ≤ 1 - U_r(m) ≤ r(r+1)/(2m)` | `normCoeff_self_bounds`, `normCoeff_bounds`, `normCoeff_succ`, `normCoeff_eq_zero`, and `falling_product_deficit` over the rationals | `UniformBessel`, `FiniteBessel` |
| `lem:clipped` (c) | 3.2 | the three weighted Bessel sums | `hasSum_rr_b0`, `hasSum_rr_b1`, `hasSum_r1_b1` | `Bessel` |
| `thm:bessel` (i), `eq:uniformbessel` | 3.3, (7) | `0 ≤ 1 - h S_N(x/h)/F(x) ≤ x(x+1)/h` for `N ≥ 2`, `x > 0` | `uniform_bessel_central`, with `central_bessel_core`, `Sab_series`, `weighted_deficit` | `UniformBessel` |
| `thm:bessel` (ii) | 3.3 | `x_B ≤ x_N`, and `x_N - x_B ≤ -(1/2) log(1 - δ_N)` when `δ_N < 1` | `central_root_bound`, with `Fcent_eq`, `root_comparison`, `Groot_unique` | `RootBounds`, `BesselDeriv` |
| `thm:bessel` (iii) | 3.3 | `0 ≤ u_N - u_B = O(L²/N²)` | `uN_sub_uB` | `Asymptotics` |
| `eq:zetaN` | (8) | `ζ_N` is the positive root of `8 ζ e^{2ζ} = π N²`, that is of `ψ(ζ) = L + c_0` | `zetaN`, `zetaN_eq`, `zetaN_log`, `zetaN_unique` | `EveryN` |
| `thm:every-n` | 3.4 | `ζ_N + 1/(8ζ_N) - ε_N < z_N < ζ_N + 1/(8ζ_N)` for every `N ≥ 2` | `every_N_crossing` | `EveryNLarge` |
| `thm:every-n`, Steps 1 to 3 | 3.4 | the case `N ≥ 175` | `four_lt_zetaN`, `every_N_upper_large`, `every_N_lower_large` | `EveryNLarge` |
| `thm:every-n`, Step 4 | 3.4 | the case `2 ≤ N ≤ 174`, by certificates | `every_N_crossing_small`, with `everyNTable`, `everyNTable_ok`, `everyNTable_covers`, `every_N_of_cert`, `lt_zetaN_of_cert`, `zetaN_lt_of_cert` | `EveryN` |
| `lem:bracket`, `eq:bracket-log` | 3.5, (9) | `log Φ(w) - log(N/2) = ψ(w) - ψ(ζ_N) + log E(w)` | `log_Fcent_eq`, with `Fcent_half_eq`, `Fcent_eq_E`, `half_N_eq` | `EveryNLarge`, `EveryN` |
| `lem:bracket` (a) | 3.5 | `Φ(w) ≤ N/2` gives `Nw/(N+w) ≤ z_N`, strictly if `Φ(w) < N/2` | `crossing_lower_of_Fcent`, `crossing_lower_of_Fcent_strict` | `EveryN` |
| `lem:bracket` (b) | 3.5 | `Φ(w)(1 - w(w+2)/(2N)) > N/2` gives `z_N < Nw/(N+w)` | `crossing_upper_of_Fcent` | `EveryN` |
| `lem:bessel-bounds` | 3.6 | the two cubic bounds on `E(z)` for `z > 0`, `E(z) ≤ 1`, and `E(z) ≤ 1 - 1/(8z)` for `z ≥ 5/4` | `besselE_ge`, `besselE_le`, `besselE_le_one`, `besselE_le_of_ge` | `BesselIntegral` |
| `cor:every-n` (a) | 3.7 | the interval for `p_N` | `every_N_crossing` | `EveryNLarge` |

## Section 4, the crossing of every bin

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `eq:allbin-polynomial` | (13) | the run form of `S_{a,b}` | `Sab_eq_run_form`, `even_coeff_identity` | `Crossing` |
| `sec:allbin-order` | 4.1 | a unique `u_{a,b}` in `(0, 1/2]`, `p_{a,b}` in `[2/3, 1)`, and the sign of `P_N(a) - P_N(0)` on each side | `uab_spec`, `Sab_eq_one_iff`, `pab_mem`, `endpoint_lt_bin_iff`, `bin_lt_endpoint_iff`, `bin_eq_endpoint_iff` | `Crossing` |
| `prop:allbin-order` | 4.1 | `u_{a+1,b-1} < u_{a,b}` and `p_{a+1,b-1} > p_{a,b}` for `a < b - 1` | `allbin_order_inward` | `Crossing` |
| `prop:allbin-order` | 4.1 | `p_{a,b+1} > p_{a,b}` | `allbin_order_longer` | `Crossing` |
| `prop:allbin-order` | 4.1 | the inequalities hold coefficientwise, with a strict coefficient | `W_le_inward`, `W_three_lt_inward`, `W_le_longer`, `W_two_lt_longer`, `Sab_lt_Sab_of_coeff`, with `inward_product_monotone` | `Crossing`, `RunAlgebra` |
| `prop:adjacent` | 4.2 | the adjacent crossing is at `p_N^adj` | `uab_adjacent`, `pab_adjacent`, `adjacent_crossing`, `adjacent_lt_iff`, `adjacent_gt_iff`, `Sab_one`, and `free_adjacent_crossing`, `free_adjacent_root_unique` over the rationals | `Crossing`, `RunAlgebra` |
| `prop:adjacent` | 4.2 | the least likely bins on each side of `p_N^adj` | `global_min`, `interior_between` | `Crossing` |
| `prop:adjacent` | 4.2 | `p_N > p_N^adj` for `N ≥ 4` | `padj_lt_pN`, `padj_le_pN` | `Crossing` |
| `prop:adjacent` | 4.2 | at `p_N` the middle and the endpoints are the maximum and bins `1`, `N-1` the minimum | `extrema_at_pN` | `Crossing` |
| `prop:adjacent` | 4.2 | for `N = 2, 3`, `p_N = p_N^adj` and every bin ties | `small_N_ties` | `Crossing` |
| `thm:allbin-bessel`, `eq:allbin-bessel` | 4.3, (14) | `0 ≤ 1 - S_{a,b}(u)/Ŝ_{a,b}(u) ≤ (a+b)u²/2 + u = x²/(2A) + x/s` | `allbin_bessel`, `allbin_bound_eq` | `UniformBessel` |
| `eq:allbin-odd-deficit`, `eq:allbin-even-deficit` | (15), (16) | the deficits of `U_r V_r` and of `E_r` | inside `allbin_bessel`, and `paired_falling_deficit`, `shifted_paired_falling_deficit` over the rationals | `UniformBessel`, `FiniteBessel` |
| `eq:allbin-normalized-series` | (17) | the normalized series of `S_{a,b}` | `Sab_series` | `UniformBessel` |
| `eq:allbin-bessel-root` | (18) | `G_η`, and its root `x_B` exists and is unique | `Geta`, `Groot_spec`, `Groot_unique`, `Geta_strictMonoOn` | `BesselDeriv` |
| `eq:allbin-logderivative` | (19) | `G_η' - 2G_η = 2x(1-η)(I_0 - I_1) + η I_0 ≥ 0` | `hasDerivAt_Geta`, `Geta_logderiv`, `Geta_deriv_ge`, `besselI1_lt_I0`, `Geta_growth` | `BesselDeriv` |
| `cor:allbin-root-bound`, `eq:allbin-root-bound` | 4.4, (20) | `x_{a,b} ≥ x_B`, and `x_{a,b} - x_B ≤ -(1/2) log(1 - δ_{a,b})` when `δ_{a,b} < 1` | `allbin_root_bound`, with `Tab_eq_Geta`, `eta_le_one`, `root_comparison` | `RootBounds`, `BesselDeriv` |
| `thm:allbin-expansion`, `eq:allbin-leading` | 4.7, (23) | in part, only the leading term `2√(ab) u_{a,b} ~ log a`, uniformly in `b ≥ a`, also for `1 - p_{a,b}` | `allbin_leading`, `allbin_leading_prob` | `AllbinAsymptotics` |
| `eq:edge-polynomial` | (25) | `H_a(y) = (y/a) L^(1)_{a-1}(-y)` | `Hedge`, `genLaguerre`, `Hedge_eq_laguerre` | `UniformBessel`, `Edge` |
| `sec:allbin-edge` | 4.4 | `y_a` exists and is unique, `y_1 = 1`, `y_2 = √3 - 1`, and `y_{a+1} < y_a` | `yEdge_spec`, `yEdge_unique`, `yEdge_one`, `yEdge_two`, `yEdge_succ_lt`, `Hedge_strictMonoOn`, `Hedge_lt_succ` | `Edge` |
| `eq:edge-exact-series` | (28) | the exact series of `S_{a,b}` in `y = b u²` | `edge_exact_series` | `Edge` |
| `thm:edge-laguerre` | 4.8 | in part, only the algebra of the coefficients `d_1 = -2c_a`, `d_2`, `γ_a`, the second coefficient `-1` of the odds and `-(1 + c_a²)` of `1 - p_{a,b}` | `edge_first_coefficient`, `edge_second_coefficient`, `edge_third_coefficient`, `universal_edge_correction`, `edge_probability_correction` | `EdgeExpansion` |
| `thm:edge-matching`, `eq:laguerre-bessel-bound` | 4.9, (30) | in part, only `0 ≤ 1 - a H_a(x²/a)/(x I_1(2x)) ≤ x²/(2a)` | `edge_matching` | `UniformBessel` |

## Section 5, periodic boundaries

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `sec:periodicwindow` | 5 | the weight `u^(cyclic switches)` is the periodic Ising weight with `u = e^{-2J}` | `pchg`, `cyclic_energy`, `periodic_weight_ising` | `Periodic` |
| `eq:periodicratio` | (33) | the cyclic count, and it is the ratio of bin `k` to an endpoint | `perWeightBin_eq_perRatio`, `perWeightBin_zero`, `perBin_ratio` | `Periodic` |
| `sec:periodicwindow` | 5 | `S^P_{N,1} = N u²` and the adjacent crossing `J = (log N)/4` | `perRatio_one`, `periodic_adjacent_threshold`, and `periodic_adjacent_crossing`, `periodic_adjacent_root_unique` over the rationals | `Periodic`, `AllbinAsymptotics`, `RunAlgebra` |
| `sec:periodicwindow` | 5 | the ratios increase strictly toward the middle and are symmetric | `perRatio_lt_inward`, `perRatio_symm` | `AllbinAsymptotics` |
| `thm:periodic-bessel`, `eq:periodicbound` | 5.1, (34) | `0 ≤ 1 - S^P_{N,k}(u)/Ŝ^P_{N,k}(u) ≤ N u²/2` | `periodic_bessel`, `perRatio_shift` | `UniformBessel` |

## Appendix A, the crossing at every N

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `app:every-n`, `eq:E-integral` | A.1, (40) | the integral form of `I_0 + I_1` and of `E` | `besselI0_add_besselI1_eq_integral`, `besselI0_add_besselI1_eq_J`, `besselE_eq_J` | `BesselIntegral` |
| `app:every-n` | A.1 | the cubic bounds on `√(1-y)`, the signs of `p` and `q` outside `[0,1]`, and the Gamma values | `sqrt_one_sub_ge`, `sqrt_one_sub_le`, `poly_p_pos`, `poly_q_nonpos`, `Gamma_half_values`, `integral_poly_gauss` | `BesselIntegral` |
| `app:every-n` | A.2 | Step 1, `ζ_N > 4` and the small quantities for `N ≥ 175` | `four_lt_zetaN`, `N_ge_exp`, `step0_bounds` | `EveryNLarge` |
| `app:every-n` | A.2 | Step 2, the upper bound, with `B > 0` and `D > 0` | `B_pos`, `D_pos`, `tW_le_tau`, `upper_key`, `every_N_upper_large` | `EveryNLarge` |
| `app:every-n` | A.2 | Step 3, the lower bound | `lower_key`, `U_sq_expand`, `every_N_lower_large` | `EveryNLarge` |
| `app:every-n` | A.3 | `d^(N-1) S_N(c/d)` is an integer, so the sign of `S_N(c/d) - 1` is a comparison of integers | `Snum`, `Snum_eq`, `Wfast_eq`, `chooseMul_eq` | `EveryN` |

## Not in this paper, kept in the repository for the tables note

The numerator tables and their bijections left Paper A for a separate note
(`paperA/tables_note/app_tables.tex`, labels as there). Step 4 of `thm:every-n` and Appendix A.3
now use Remark 2.3 (`rem:tables`), whose Lean theorems are listed in Section 2 above. The module
`Tables` holds the two bijections.

| Label in the note | Statement | Lean | Module |
| --- | --- | --- | --- |
| `prop:num` | `n_N(k)` is the weighted word count, an integer, and its generating function | `numer_eq`, `numer_cast`, `numerGF_eq` | `Recurrence` |
| `thm:rook` | for `p = 2/3`, `n_N(k) = r(k, N-k)` | `rook_eq_numer`, `rook_eq_prob`, with `rook_rec`, `numer23_rec` | `Tables` |
| `thm:mathar` | for `p = 1/3`, `n_N(k) = M(k, N-k)` | `mathar_eq_numer`, `mathar_eq_prob`, with `mathar_corner`, `mathar_A`, `mathar_B`, `mathar_main` | `Tables` |

Notes for the tables note.

* `prop:num`. `numerGF_eq` holds for all integers `α`, `β`, and is stated in the variables `x t`
  and `t` in place of `x` and `y`, with the denominator multiplied out. The series is homogeneous,
  so nothing is lost.
* `thm:rook`. `rook` is defined by the recursion of A035002 (an entry is the sum of the entries
  to its left and below it), and `mathar` by the recursion on the last step of a walk.
* `thm:rook`, `thm:mathar`. That the recursions count the paths, and the symmetry
  `M(a,b) = M(b,a)`, are not in Lean.

## Lean theorems that the paper does not state

| Content | Lean | Module |
| --- | --- | --- |
| `p_N ≥ p_N^adj` for every `N ≥ 2` | `padj_le_pN` | `Crossing` |
| `P_N(1) ≤ P_N(k) ≤ P_N(⌊N/2⌋)` for `1 ≤ k ≤ N-1` and `0 ≤ p ≤ 1` | `interior_between`, `W_between` | `Crossing` |
| `2e^{2x-4} ≤ F(x)` for `x ≥ 1` and `F(x) ≤ 4x e^{2x}` for `x ≥ 0` | `Fcent_ge`, `Fcent_le`, with `besselI0_le_exp`, `besselI1_le_exp`, `factorial_le_stirling` | `Asymptotics` |
| for `0 < ε < 1`, eventually `(1-ε)(log N)/N < u_N < (1+ε)(log N)/N` | `uN_lower`, `uN_upper` | `Asymptotics` |
| eventually `u_N - u_B ≤ 8 (log N)²/N²` | `uN_sub_uB` | `Asymptotics` |
| `d/dx I_0(2x) = 2 I_1(2x)` and `d/dx [x I_1(2x)] = 2x I_0(2x)` | `hasDerivAt_I0`, `hasDerivAt_xI1`, `hasDerivAt_I1` | `BesselDeriv` |
| `G_η(y) ≥ e^{2(y-x)} G_η(x)` for `0 ≤ x ≤ y` | `Geta_growth` | `BesselDeriv` |
| `y_a ≤ 1` | `yEdge_spec` | `Edge` |
| `N ≥ 174.25 e^{ζ_N - 4}` for `N ≥ 175` | `N_ge_exp` | `EveryNLarge` |
| rational bounds `s/10⁴ < ζ_N < S/10⁴` from integer inequalities | `lt_zetaN_of_cert`, `zetaN_lt_of_cert` | `EveryN` |
| the recurrence of `n_N(k)` for `N ≥ 3` (and `n_N(0) = α n_{N-1}(0)`) | `numer_rec`, `weightBin_rec_zero` with `numer_cast` | `Recurrence` |
| the row-polynomial recursion `g_N = p(1+x) g_{N-1} + (1-2p) x g_{N-2}` | `rowPoly_rec` | `Recurrence` |

## Differences between the Lean statements and the paper

No Lean theorem listed above states less than the row of the table claims. The differences are
the following.

Stronger or more general hypotheses in Lean.

1. `thm:pmf`, `prop:gf`, `prop:var`. The Lean statements hold for every real `p`, since both sides
   are polynomials in `p`. The paper has `0 ≤ p ≤ 1`.
2. `prop:adjacent`. The tie of bin 1 with an endpoint (`adjacent_crossing`) is proved for
   `0 < p ≤ 1`. The paper has `0 < p < 1`.
3. `thm:bessel` (iii). Lean proves that `0 ≤ u_N - u_B ≤ 8 (log N)²/N²` for all large `N`. The
   paper states `O(L²/N²)`.
4. `eq:edge-exact-series`. Lean proves it for all `a, b ≥ 1` and `u ≥ 0`. The paper has
   `b ≥ a`.
5. `zetaN N` is defined for every `N ≥ 1`, and `zetaN_eq`, `zetaN_log` and `log_Fcent_eq`
   (`eq:bracket-log`) hold for `N ≥ 1`. The paper uses them for `N ≥ 2`.
6. `eq:allbin-normalized-series`. `Sab_series` holds for any weights `α, β > 0` in place of
   `a, b`. The paper's series is the case `α = a`, `β = b`, where `normCoeff a a r = U_r(a)`.
7. `lem:clipped` (c). The three sums `hasSum_rr_b0`, `hasSum_rr_b1`, `hasSum_r1_b1` hold for every
   real `x`. The paper has `x ≥ 0`.
8. `rem:tables`. `numer_eq` only needs `α + β > 0`. The paper has integers `α, β ≥ 0`, not
   both `0`, which is the same condition.

Different normalizations.

9. `eq:dp`. `endProb p n k e` is the probability after `n + 1` steps, so `P_N^R` is
   `endProb p (N-1) · true`.
10. `eq:gf`. `probGF_eq` is the identity with the denominator multiplied out,
    `(1 - p(1+x)t + (2p-1)x t²) G = 1 - (p - 1/2)(1+x)t`, in power series in `t` over `ℝ[x]`. The
    first factor has constant term 1, so this determines `G`.
11. `prop:var`. `varK` is the second moment about `N/2`, and `meanK_eq` shows that `N/2` is the
    mean.
12. `z_N`, `ε_N`, `Φ`. Lean has no names for them. `z_N` is `N * (1 - pN N)`, `ε_N` is written
    out, and `Φ(w)` is `Fcent (w/2)`.
13. `eq:bracket-log`. `log_Fcent_eq` has `(1/2) log(w/ζ_N) + (w - ζ_N)` in place of
    `ψ(w) - ψ(ζ_N)`. The two are equal.
14. `eq:E-integral`. Lean uses the variable `x` with `v = 2z x²`, so that
    `I_0(z) + I_1(z) = (4e^z/π) ∫_0^1 e^{-2z x²} √(1 - x²) dx`. The paper's cubic bounds on
    `√(1-y)` are used at `y = x²`.
15. `thm:allbin-expansion`. `allbin_leading` and `allbin_leading_prob` state the leading term with
    `log a`, exactly as in `eq:allbin-leading`. The expansion of the theorem itself is in
    `ℓ = log A`, and `a/2 ≤ A ≤ a`, so the two leading terms agree.

Different proofs of the same statement.

16. `prop:gf`. Lean proves `eq:rec` from the two-state recursion and then `eq:gf` from `eq:rec`. The
    paper proves `eq:gf` first.
17. `prop:var`. Lean differentiates the row polynomial twice at `x = 1` and uses `eq:rec`. The
    paper cites Dekking and Kong (Eq. (2.3) and Proposition 2.1 of the J. Appl. Probab. version)
    with `a = b = q` and the stationary start.
18. `thm:clt`. Lean uses the recurrence `φ_{N+2} = 2p cos θ φ_{N+1} - (2p-1) φ_N` from `eq:rec` and
    the closed form `c_+ λ_+^N + c_- λ_-^N` with `φ_0`, `φ_1`. The paper uses the transfer matrix
    and `λ_±^{N-1}` with `φ_1`, `φ_2`. Lean scales `K_N` with `θ = s/(2√N)`, and the paper scales
    `X_N` with `θ = s/√N`.
19. `thm:root` (c). Lean proves it from `eq:uniformbessel` and the bounds
    `2e^{2x-4} ≤ F(x) ≤ 4x e^{2x}`. The paper proves it from `thm:bessel` (i) with the bound
    `F(x) ≤ 2x e^{2x}` and the large-argument form of `I_0`.
20. `eq:allbin-logderivative`. Lean proves `I_0(2x) > I_1(2x)` from the derivative of
    `e^{2x}(I_0(2x) - I_1(2x))`. The paper uses the integral form.
21. `lem:bessel-bounds`. Lean proves the integral form of `I_0 + I_1` from the power series by
    integrating term by term. The paper derives it in Appendix A.1 from the integral
    representation of `I_n` in DLMF 10.32.3.
22. `thm:every-n` for `N ≥ 175`. Lean follows Steps 1 to 3 of Appendix A with the same test values
    `W` and `W'`, but with other constants. It has `U/N ≤ 0.0232`, `U²/N ≤ 0.0933`,
    `U³/N ≤ 0.376` and `ζ(ζ+1)/N ≤ 0.1148` in place of `0.023135`, `0.093262`, `0.375960` and
    `0.114776`, it gets them from `N ≥ 174.25 e^{ζ_N - 4}` and not from the monotonicity of
    `U^k/n(ζ)`, it has no bound on `U⁴/N`, and it uses
    `log(1-x) ≥ -(x + x²/2 + x³/(1-x))`. So the decimal constants of Appendix A are not the ones
    Lean checks. The theorem is the same.
23. `thm:every-n` for `N ≤ 174`. The values `c` and `c'` in `everyNTable` are the columns
    `u_lo_times_1e9` and `u_hi_times_1e9` of `paperA/data/every_n_certificates.csv` for all 173
    values of `N`. Lean evaluates `d^(N-1) S_N(c/d)` by the run-count sum only, and the recursion
    `eq:dp` is the second method of the Python script. Lean brackets `ζ_N` on the grid `10⁻⁴`,
    with Taylor bounds for `exp` and `3.141592 < π < 3.141593`. The script brackets `ζ_N` within
    `10⁻⁴⁵` in 60-digit arithmetic. The margins `0.033193` and `0.085591` are those of the script.

Partial coverage.

24. `lem:clipped` (a). The statement for `r` factors is in Lean over the rationals
    (`finite_product_deficit`). Over the reals Lean has the case of two factors (`prod_deficit`) and
    uses it by induction inside `normCoeff_bounds`.
25. `lem:clipped` (b). `normCoeff m m r` is `r!/m^r C(m-1,r)`. The product form
    `Π(1 - k/m)_+` appears only as the recursion `normCoeff_succ`.
26. `thm:every-n`, Step 1. Lean has `ζ_N > 4` for `N ≥ 175`. It does not state that `ζ_N < 4` for
    `N ≤ 174`.
27. `eq:zetaN`. The Lambert form `ζ_N = (1/2) W_0(πN²/4)`, the monotonicity of `ζ_N` in `N` and
    `ζ_N ≤ L` are not in Lean.
28. `cor:every-n` (a). There is no separate theorem. Part (a) is `every_N_crossing` with
    `p_N = 1 - z_N/N`.
29. `sec:allbin-order`. That `p_{a,b} = 2/3` only for `a = b = 1` is not in Lean.
30. `prop:adjacent`. `global_min` and `extrema_at_pN` have weak inequalities, so they show that the
    named bins attain the minimum or maximum. The strict inequality `P_N(k) < P_N(k+1)` between
    interior bins, which the paper's proof gives, is in Lean only for the polynomials
    (`Sab_lt_Sab_of_coeff` with `W_le_inward`, `W_three_lt_inward`) and for the crossings
    (`allbin_order_inward`).
31. `thm:edge-laguerre`. The theorems of `EdgeExpansion` are over the rationals and take the
    coefficient equations of `eq:edge-implicit-expansion` as hypotheses. The implicit function
    step and the error terms are not in Lean.
32. `sec:periodicwindow`. `perRatio` is defined as the polynomial of `eq:periodicratio`, and
    `perBin_ratio` shows that it is the ratio of the bin probabilities. The periodic central root
    `u_N^P` is not defined in Lean, and neither its existence nor the strict increase of
    `S^P_{N,k}` in `u` is stated. The ordering toward the middle is `perRatio_lt_inward` for
    `k + 2 ≤ N - k`, with `perRatio_symm`.
33. Appendix A.3. `Snum` is built from the coefficients `W`, so `Snum_eq` is the identity
    `d^(N-1) S_N(c/d) = Σ_j W(N,m_N,j) c^j d^(N-1-j)`. That this integer is `n_N(m_N)` follows from
    `card_words_eq_W` but is not stated as one theorem.
34. `thm:edge-laguerre`. The variables of `EdgeExpansion` are rationals, while `y_a`, `c_a`,
    `H_a'(y_a)` and `H_a''(y_a)` are real and in general irrational (for example `y_2 = √3 - 1`).
    The statements are polynomial identities, so the same proof works over the reals, but Lean
    does not state the real version.

## Not in Lean

The following parts of the paper are not in Lean. They need the large-argument expansion of the
Bessel functions, an implicit function argument, a limit in two variables, or a computation done in
Python.

* Section 3. Corollary 3.7 (`cor:every-n`) beyond part (a), Proposition 3.8
  (`prop:crossing-eq`) and Remark 3.9 (`rem:sign`). The values in the tables `tab:pn` and
  `tab:every-n`.
* Section 4. Remark 4.5 (`rem:jacobi`), Lemma 4.6 (`lem:inversion`), Theorem 4.7
  (`thm:allbin-expansion`) beyond its leading term, the expansions of Theorem 4.8
  (`thm:edge-laguerre`), the expansion `eq:edge-matching-expansion` of Theorem 4.9
  (`thm:edge-matching`) and Corollary 4.10 (`cor:boundary-layer`).
* Section 5. Theorem 5.2 (`thm:periodic-crossing`), even its leading term, and Theorem 5.3
  (`thm:critical-window`).
* Appendix A. The proof of Proposition 3.8, and the 60-digit comparisons of Step 4 (Lean has its
  own rational bounds in their place).
* The uniform local law (the local law note, not in Lean).
* The numerator tables module `Tables.lean`, kept in the repository for the tables note.

## Findings while checking

* No mathematical error was found in the statements above.
* Apart from the differences listed above, every result that the verification section of the
  paper says is in Lean has a Lean theorem with the same hypotheses, constants and ranges. This
  includes `N ≥ 2` in `thm:root`, `thm:bessel`, `lem:bracket` and `thm:every-n`, the strict
  inequalities of `thm:every-n`, and the definitions of `p_N`, `u_N`, `ζ_N` and `S_N`.
* The docstrings of the Lean files still refer to "Step 0" of Appendix A (Step 1 in the paper) and
  to the appendix `app:tables`.
