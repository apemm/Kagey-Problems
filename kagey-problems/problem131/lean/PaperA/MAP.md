# Paper A: map from the paper to the Lean theorems

This file maps covered statements of Paper A (`paperA/problem131.tex` and the files it inputs)
to Lean declarations and records partial coverage and omissions. The library `PaperA` has root
`PaperA.lean`, which imports all 46 modules in `PaperA/` (47 modules including the root), in
namespace `Kagey131`. It uses Lean 4 v4.33.1 and Mathlib v4.33.1. Every theorem listed here is
proved without `sorry`, `admit` or new axioms, and `#print axioms` on each of them reports only
`propext`, `Classical.choice` and `Quot.sound` (see `build-log.txt`).

The key of each row is the `\label` in the source. The column Number gives the number in the built
PDF. The numbers can change when the paper is edited, and the labels do not. "In part" means that
only the result specified in that row is covered; this can be a finite inequality, a leading
limit, or conditional rational algebra. The section "Differences between the Lean statements
and the paper" explains these qualifications, and "Not in Lean" lists the omitted results.

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
| the root `x̂_{a,b}` of `G_η(x) = A` (Section 4), and `x_B` of `F(x) = h` (Section 3) | `Groot η A` |
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
| `AllbinAsymptotics` | the all-bin leading term as `a → ∞`, uniformly in `b ≥ a`, and the periodic ordering |
| `Edge` | the polynomial `H_a`, its root `y_a` and the exact edge series |
| `EdgeExpansion` | rational algebra conditional on the edge coefficient equations |
| `Periodic` | the cyclic count and the periodic ratio |
| `BesselIntegral` | the integral form of `I_0 + I_1` and the bounds on `E` |
| `EveryN` | the root bracket, `ζ_N`, and the crossing for `2 ≤ N ≤ 174` by certificates |
| `EveryNLarge` | the crossing for `N ≥ 175` and for every `N ≥ 2` |
| `EveryNCorollary` | full positivity, probability and coupling bounds of Corollary (a), and the finite inequalities of (b) |
| `EveryNSign` | the rational threshold certificate and the crossing above ζ_N for every N ≥ 2774 |
| `EveryNSignTable` | Remark `rem:sign` for `2 ≤ N ≤ 2773` by kernel-checked certificates, and the whole sign pattern |
| `EveryNAsymptotics` | the asymptotic conclusions of Corollary (b) and (c), with explicit constants, and the conversion between `z_N` and `N u_N` |
| `CrossingEquation` | Proposition `prop:crossing-eq` for every `N ≥ 2`, analytic for `N ≥ 175` and by rational certificates below |
| `LogInversion` | Lemma `lem:inversion`, the inversion of `z + (1/2) log z`, with an explicit constant |
| `BesselAsymptotics` | the large-argument forms of `I_0`, `I_1` and `I_1 + η I_0` with explicit remainders, and the argument shift |
| `PeriodicCrossing` | the periodic central root `u_N^P`, its first order and the periodic crossing equation |
| `PeriodicExpansion` | Theorem `thm:periodic-crossing` and Corollary `cor:couplings` |
| `AllbinExpansion` | Theorem `thm:allbin-expansion` and the expansion of Theorem `thm:edge-matching`, through the Bessel root |
| `EdgeLaguerre` | Theorem `thm:edge-laguerre`, the fixed-edge expansion |
| `CriticalWindow` | Theorem `thm:critical-window`, the profile and the count for both boundary conditions |
| `IsingDictionary` | the Ising dictionary for free ends, and the positivity of the couplings and correlation lengths at the crossings |
| `InfiniteChain` | the two-point function of the free chain in zero field, its infinite-volume limit and `ξ(J)` as its correlation length |
| `BoundaryLayer` | Corollary `cor:boundary-layer`, the moving boundary layer, for arbitrary sequences `v_N` |
| `Supplements` | smaller statements: Lemma `lem:clipped` over the reals and in product form, `ζ_N < 4` for `N ≤ 174`, `p_{a,b} = 2/3` only at `a = b = 1`, strict probability ordering, and `Snum` as the numerator |
| `FixedMagnetization` | Corollary `cor:fixed-M`, the fixed-magnetization weight |
| `DomainWalls` | Proposition `prop:walls`, the domain walls at the crossing |
| `FullOrder` | Remark `rem:ordered`, full order against one bin |
| `FieldCrossing` | Theorem `thm:field`, the edge crossings in a fixed field, for free and periodic ends |
| `Tables` | identities between numerator tables and recursively defined rook and Mathar sequences; retained for the tables note |
| `TableValuesCore` | correct rounding (`RoundsTo`), Taylor certificates for `exp` and `log`, rational bounds on `ζ_N`, and bounds on `u_N` and `u_N^P` from truncated sums with a geometric tail |
| `TableValuesEveryN` | the values of the table `tab:every-n`, by kernel-checked certificates |
| `TableValuesCouplings` | the values of the table `tab:couplings`, by kernel-checked certificates |
| `TableValuesText` | decimals displayed in the text, by kernel-checked certificates |
| `TableValuesBessel` | the ratios `u_B/u_N` quoted in Section 3, with rational bounds on the Bessel root `x_B` from the series of `I_0` and `I_1` |
| `TableValuesField` | the examples after Theorem `thm:field`: the minimizing `a`, `y_*(𝓑)` and `N (u_N^{(≥2)})²` at `N = 10⁴`, with exact rational forms of `H_a`, `S_{a,b}` and `S^P_{N,a}` and an explicit threshold for the tail bound |
| `TableValuesWalls` | the numbers quoted in Section 5 on domain walls (`𝒲_N(u_N) - z_N`, `1/2 + 1/(8z_N)`, `1/(2𝒲_N(u_N))`), the mean domain length `l_d` and the window profile errors of Figure `fig:window` |

## Section 1, setting and notation

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `eq:wordprob` | (1) | `P(w) = (1/2) p^rep q^chg`, with `rep + chg = N - 1`, and the law has total mass 1 | `wordProb`, `rep_add_chg`, `wordProb_eq_of_pos`, `sum_wordProb`, `sum_binProb` | `Model` |
| `sec:setting` | 1.2 | `P_N(0) = P_N(N) = p^(N-1)/2` and `P_N(k) = P_N(N-k)` | `binProb_zero_bin`, `binProb_last_bin`, `binProb_symm` | `Model` |
| `sec:setting` | 1.2 | `P_N(a) = P_N(0) S_{a,b}(u)` for `p > 0` | `binProb_eq_mul_Sab`, `SN_eq_ratio` | `Crossing` |
| `eq:zN` | (2) | `z_N = N(1 - p_N) = N u_N/(1 + u_N)` | `N_one_sub_pN` | `EveryN` |
| `sec:setting` | 1.2 | the large-argument forms of `I_0` and `I_1`: for `z ≥ 1`, `|√(2πz) e^{-z} I_0(z) - (1 + 1/(8z))| ≤ 11/z²` and `|√(2πz) e^{-z} I_1(z) - (1 - 3/(8z))| ≤ 11/z²` | `besselI0_asymp`, `besselI1_asymp`, with `besselI0_sub_besselI1_eq`, `besselKint_bounds`, `nu_sub_bound`, `besselE_near`, `besselI0_neg`, `besselI1_neg` | `BesselAsymptotics` |
| `sec:setting` | 1.2 | uniformly in `0 ≤ η ≤ 1` and for `z ≥ 1`, `|√(2πz) e^{-z} (I_1 + η I_0)(z) - ((1+η) - (3-η)/(8z))| ≤ 22/z²` | `besselI1_add_eta_I0_asymp` | `BesselAsymptotics` |
| `sec:setting` | 1.2 | Ising dictionary: the energy `∑_{i<N} σ_i σ_{i+1}` of a word is `(N-1) - 2 chg(w)`, so `u^chg(w) = e^{-(N-1)J} exp(J ∑ σ_i σ_{i+1})` with `u = e^{-2J}`, and bin `k` is magnetization `2k - N` | `freeEnergy`, `freeEnergy_eq_rep_sub_chg`, `free_energy`, `free_weight_ising`, `magn`, `magn_eq` | `IsingDictionary` |
| `sec:setting` | 1.2 | Ising dictionary: `Z_N(N) = e^{(N-1)J}` and `S_{a,b}(u) = Z_N(a-b)/Z_N(N)` for `a, b ≥ 1`, and `J > 0` exactly when `p > 1/2` | `isingZ`, `isingZ_full`, `Sab_eq_isingZ_ratio`, `word_sum_eq_Sab`, `coupling_pos_iff` | `IsingDictionary` |
| `sec:setting` | 1.2 | Ising dictionary: with `ξ(J) = -1/log tanh J`, `tanh J = (1-u)/(1+u)`, `N/ξ = N log((1+u)/(1-u))` with `|log((1+u)/(1-u)) - 2u| ≤ u³` for `0 ≤ u ≤ 1/2`, `N(1 - tanh J)/2 = τ`, and `|τ - N/(2ξ)| ≤ 2u N/(2ξ)` for `0 < u ≤ 1/2` | `corrLen`, `tanh_neg_half_log`, `N_div_corrLen`, `log_ratio_sub_two`, `adr_scale_eq`, `switching_scale_corrLen` | `PeriodicExpansion`, `IsingDictionary` |
| `sec:setting` | 1.2 | the infinite chain behind `ξ(J)`: in every finite free chain in zero field `⟨σ_i σ_{i+r}⟩ = tanh(J)^r` for every real `J`; the infinite-volume two-point function, the limit over growing chains, is `tanh(J)^(abs(x-y))`; for `J > 0`, `⟨σ_0 σ_r⟩ = e^{-r/ξ(J)}` with `ξ(J) = -1/log tanh J`, and `ξ(J)` is the inverse of the decay rate | `chainCorr`, `chainCorr_eq`, `chainCorr_eq_dist`, `intervalCorr_eq`, `tendsto_intervalCorr`, `infCorr`, `infCorr_eq`, `tendsto_infCorr`, `infCorr_eq_exp`, `infCorr_zero_eq_exp`, `decay_rate_eq`, `tendsto_decay_rate`, `corrLen_eq_decay`, `infCorr_at_odds`, with `chainZ_succ`, `chainCorr_succ_succ`, `chainCorr_zero_succ` | `InfiniteChain` |
| `sec:setting` | 1.2 | the argument shift: for `z ≥ 48` and `|h| ≤ z/2`, `|e^{-h} √((z+h)/z) I(z+h)/I(z) - 1| ≤ 48/z` for `I = I_0, I_1` | `besselI0_shift`, `besselI1_shift`, `shift_of_first` | `BesselAsymptotics` |

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
| `lem:clipped` (a) | 3.2 | `0 ≤ 1 - Π(1 - t_k)_+ ≤ Σ t_k` | `clipped_product_deficit` over the reals for any finite family, `finite_product_deficit`, `clip_bounds`, `product_deficit`, `prod_deficit` | `Supplements`, `FiniteBessel`, `UniformBessel` |
| `lem:clipped` (b) | 3.2 | `U_r(m) = Π_{k=1}^r (1 - k/m)_+` and `0 ≤ 1 - U_r(m) ≤ r(r+1)/(2m)` | `normCoeff_eq_prod`, `normCoeff_self_bounds`, `normCoeff_bounds`, `normCoeff_succ`, `normCoeff_eq_zero`, and `falling_product_deficit` over the rationals | `Supplements`, `UniformBessel`, `FiniteBessel` |
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
| `cor:every-n` (a) | 3.7 | the full positivity chain `0 < Y'_N < Y_N < N`, probability interval and coupling interval for every N ≥ 2 | `every_N_corollary_a`, `every_N_bracket_endpoints` | `EveryNCorollary` |
| `cor:every-n` (b), `eq:secondorder` | 3.7, (10) | both finite bounds on ζ_N and both finite bounds on z_N - ν_N | `every_N_zeta_bracket`, `every_N_corollary_b_finite`, `nuN_pos` | `EveryNCorollary` |
| `cor:every-n` (b) | 3.7 | the asymptotic conclusion `z_N = ν_N + O(log L/L)`, as `|z_N - ν_N| ≤ 27 log L/L` for every N ≥ 21 and as an `IsBigO` statement | `every_N_corollary_b_bound`, `every_N_corollary_b_isBigO` | `EveryNAsymptotics` |
| `cor:every-n` (c), `eq:thirdorder` | 3.7, (11) | `z_N = ν_N + (log L/4 - c₀/2 + 1/8)/L + O((log L)²/L²)`, as the bound `52 (log L)²/L²` for every N ≥ 21 and as an `IsBigO` statement | `every_N_corollary_c_bound`, `every_N_corollary_c_isBigO`, with `every_N_c_core`, `every_N_eps_le` | `EveryNAsymptotics` |
| `eq:zN`, conversion | (2) | `0 ≤ N u_N - z_N ≤ 2(L + 1/4)²/N` for every N ≥ 2 | `N_uN_sub_zN` | `EveryNAsymptotics` |
| `rem:sign` | 3.9 | for every `N ≥ 2`, `z_N > ζ_N` for `N ≤ 15`, `z_N < ζ_N` for `16 ≤ N ≤ 218` and `z_N > ζ_N` for `N ≥ 219`, where `z_N = N(1 - p_N)` | `rem_sign`, `sign_table`, with `signCheck1` to `signCheck14`, `sign_of_check`, `sign_of_cert`, `SnumFast_eq`, `lt_zetaN_of_cert10`, `zetaN_lt_of_cert10`, `lt_zN_of_cert`, `zN_lt_of_cert`, and `every_N_crossing_above_zeta` for `N ≥ 2774` | `EveryNSignTable`, `EveryNSign` |
| `cor:every-n` (d) | 3.7 | z_N > ζ_N for every N ≥ 2774, with a kernel-checked rational threshold certificate | `every_N_crossing_above_zeta`, `zetaN_2774_lower`, `zetaN_2774_upper` | `EveryNSign` |
| `eq:zetaN`, auxiliary bounds | (8) | ζ_N is monotone in N, and 1/2 < ζ_N ≤ log N for N ≥ 2 | `zetaN_mono`, `half_lt_zetaN`, `zetaN_le_log` | `EveryNCorollary` |
| `prop:crossing-eq`, `eq:crossing-eq` | 3.8, (12) | with `R_N = z + (1/2) log z - L - c₀ - 1/(8z)`, for every `N ≥ 2`: `-(z²+z)/N ≤ R_N ≤ 1/(16z²)`, `L/2 ≤ z ≤ L` and `|R_N| ≤ 1/(4L²) + (L²+L)/N` | `crossing_equation`, `crossRem`, `crossRem_eq` | `CrossingEquation` |
| `prop:crossing-eq`, `N ≥ 175` | 3.8 | the analytic case | `crossing_eq_large`, with `large_core`, `large_sizes`, `bessel_tail_poly`, `step0_fourth` | `CrossingEquation` |
| `prop:crossing-eq`, `N ≤ 174` | 3.8 | the case `2 ≤ N ≤ 174`, by certificates | `crossing_eq_small`, with `crossEqTable`, `crossEqTable_ok`, `crossEqTable_sub`, `crossEqTable_covers`, `crossing_eq_of_cert`, `small_core`, `everyNCert_brackets` | `CrossingEquation` |
| `tab:every-n` | Table 1 | every printed value is the correct rounding of the quantity it names: `z_N` to 12 decimals, `ζ_N` to 10, `z_N - ζ_N - 1/(8ζ_N)` to 7, `-ε_N` to 5 and `R_N` to 6, for `N = 2, 10, 100, 174, 175, 1000, 10⁴` | `tab_every_n_2`, `tab_every_n_10`, `tab_every_n_100`, `tab_every_n_174`, `tab_every_n_175`, `tab_every_n_1000`, `tab_every_n_10000`, with `tv_zN_N`, `tv_zetaN_N`, `RoundsTo`, `lt_uN_of_tail`, `uN_lt_of_partial`, `lt_zetaN_of_tv`, `zetaN_lt_of_tv`, `crossRem_bounds` | `TableValuesEveryN`, `TableValuesCore` |

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
| `cor:fixed-M` | 4.4 | for `a, b ≥ 1`, `N = a + b`, `μ = a - b`, `ρ = √(1 - μ²/N²)` and `v = N e^{-2J} ρ`, `Z_N(μ) = 2 e^{(N-3)J} (I_0(v) + I_1(v)/ρ)(1 - θ)` with `0 ≤ θ ≤ (N/2) e^{-4J} + e^{-2J}`, for every real `J` | `fixed_M_weight`, `rho_eq` | `FixedMagnetization` |
| `cor:allbin-root-bound`, `eq:allbin-root-bound` | 4.6, (20) | `x_{a,b} ≥ x̂_{a,b}`, and `x_{a,b} - x̂_{a,b} ≤ -(1/2) log(1 - δ_{a,b})` when `δ_{a,b} < 1` | `allbin_root_bound`, with `Tab_eq_Geta`, `eta_le_one`, `root_comparison` | `RootBounds`, `BesselDeriv` |
| `lem:inversion` | 4.8 | for every `K > 0` there is `C_K` with `|z - ℓ + (1/2) log ℓ - C - ((1/4) log ℓ - C/2 + B)/ℓ| ≤ C_K((log ℓ)²/ℓ² + |ω|)` whenever `z ≥ 1`, `ℓ ≥ 2`, `|C|, |B| ≤ K`, `|ω| ≤ 1` and `z + (1/2) log z = ℓ + C + B/z + ω` | `log_inversion`, with `abs_log_one_add_sub_le`, `log_le_quarter` | `LogInversion` |
| `thm:allbin-expansion`, `eq:allbin-expansion` | 4.9, (21) | with `ℓ = log A`, `η = 2√(ab)/(a+b)`, `C(η) = (1/2) log(8π) - log(1+η)` and `B(η) = (3-η)/(8(1+η))`, there are `K` and `a₀` with `|2√(ab) u_{a,b} - (ℓ - (1/2) log ℓ + C(η) + ((1/4) log ℓ - C(η)/2 + B(η))/ℓ)| ≤ K((log ℓ)²/ℓ² + (log a)²/a)` for all `a ≥ a₀` and all `b ≥ a`, and the same for `1 - p_{a,b}` | `allbin_expansion`, `allbin_expansion_prob`, `rootMain`, `Ceta`, `Beta`, with `allbin_root_close` | `AllbinExpansion` |
| `thm:allbin-expansion` | 4.9 | Step 2 of the proof: if `G_η(z/2) = A` and `z ≥ 100`, then `z + (1/2) log z = log A + C(η) + B(η)/z + ω` with `|ω| ≤ 24/z²`, and there are `K` and `A₀` with `|2x̂ - (main terms in ℓ = log A)| ≤ K (log ℓ)²/ℓ²` for all `A ≥ A₀`, uniformly in `0 ≤ η ≤ 1` | `bessel_root_eq`, `bessel_root_expansion`, with `bessel_factor`, `Ceta_bounds`, `Beta_bounds` | `AllbinExpansion` |
| `thm:allbin-expansion`, `eq:allbin-leading` | 4.9, (23) | in part, only the leading term `2√(ab) u_{a,b} ~ log a`, uniformly in `b ≥ a`, also for `1 - p_{a,b}` | `allbin_leading`, `allbin_leading_prob` | `AllbinAsymptotics` |
| `eq:edge-polynomial` | (25) | `H_a(y) = (y/a) L^(1)_{a-1}(-y)` | `Hedge`, `genLaguerre`, `Hedge_eq_laguerre` | `UniformBessel`, `Edge` |
| `sec:allbin-edge` | 4.4 | `y_a` exists and is unique, `y_1 = 1`, `y_2 = √3 - 1`, and `y_{a+1} < y_a` | `yEdge_spec`, `yEdge_unique`, `yEdge_one`, `yEdge_two`, `yEdge_succ_lt`, `Hedge_strictMonoOn`, `Hedge_lt_succ` | `Edge` |
| `eq:edge-exact-series` | (28) | the exact series of `S_{a,b}` in `y = b u²` | `edge_exact_series` | `Edge` |
| `thm:edge-laguerre` | 4.10 | in part, rational algebra conditional on the coefficient equations, yielding the formal coefficients `d_1`, `d_2`, `γ`, `-1` and `-(1 + c²)`; no specialization to the actual real crossing or its asymptotics | `edge_first_coefficient`, `edge_second_coefficient`, `edge_third_coefficient`, `universal_edge_correction`, `edge_probability_correction` | `EdgeExpansion` |
| `eq:edge-exact-series`, `eq:edge-implicit-expansion` | (28), (29) | for `b ≥ a + 1`, `θ = 1/√b` and `0 ≤ c ≤ 2`, `|S_{a,b}(θc) - (H_a(c²) + 2θ c H_a'(c²) + θ² ((c² - c⁴/2) H_a''(c²) - c² H_a'(c²)))| ≤ K_a θ³` | `edge_series_error`, `Qedge`, `Kedge`, with `edge_term_error`, `normCoeff_second`, `edge_k_identity`, `H1`, `H2`, `hasDerivAt_Hedge`, `hasDerivAt_H1` | `EdgeLaguerre` |
| `thm:edge-laguerre`, `eq:edge-crossing-expansion` | 4.10, (26) | for each `a ≥ 1`, `√b u_{a,b} → c_a`, and there is `M` with `|u_{a,b} - (c_a/√b - 1/b + γ_a/b^{3/2})| ≤ M/b²` for all large `b`, with `γ_a` as in the paper | `edge_leading`, `edge_crossing_expansion`, `edge_root_expansion`, `cEdge`, `gammaEdge`, with `edge_P_expansion`, `edge_root_sign`, `psum_taylor2` | `EdgeLaguerre` |
| `thm:edge-laguerre`, `eq:edge-q-expansion` | 4.10, (27) | for each `a ≥ 1` there is `M` with `|1 - p_{a,b} - (c_a/√b - (1 + c_a²)/b)| ≤ M/b^{3/2}` for all large `b` | `edge_q_expansion` | `EdgeLaguerre` |
| `thm:edge-matching`, `eq:laguerre-bessel-bound` | 4.11, (30) | `0 ≤ 1 - a H_a(x²/a)/(x I_1(2x)) ≤ x²/(2a)` | `edge_matching` | `UniformBessel` |
| `thm:edge-matching`, `eq:edge-matching-expansion` | 4.11, (31) | with `ℓ = log a`, there is `K` with `|2√(a y_a) - (ℓ - (1/2) log ℓ + C(0) + ((1/4) log ℓ - C(0)/2 + 3/8)/ℓ)| ≤ K((log ℓ)²/ℓ² + (log a)²/a)` for all large `a`, where `C(0) = (1/2) log(8π)` | `edge_matching_expansion`, `Ceta_zero_Beta_zero`, with `edge_root_small`, `bessel_root_expansion` | `AllbinExpansion` |
| `cor:boundary-layer`, `eq:boundary-layer-width` | 4.12, (32) | for any sequence with `v_N > 0` eventually, `Ω_N = 1/(√N v_N) → ∞` and `log Ω_N/(N v_N) → 0`: `ℒ_N ~ Ω_N² log² Ω_N`, where `ℒ_N` counts the bins `1 ≤ k ≤ ⌊N/2⌋` with `P_N(k) < P_N(0)` at `p = 1/(1+v_N)` | `boundary_layer`, `layerCount`, with `layer_eventually`, `layer_core`, `layerCount_bounds`, `below_iff`, `uab_anti` | `BoundaryLayer` |
| `cor:boundary-layer` | 4.12 | the case `v_N = N^{-κ}`, `1/2 < κ < 1`: `ℒ_N ~ (κ - 1/2)² N^{2κ-1} log² N` | `boundary_layer_power` | `BoundaryLayer` |
| `cor:boundary-layer` | 4.12 | eventually, the number of interior bins `1 ≤ k ≤ N-1` with `P_N(k) < P_N(0)` is `2ℒ_N` | `boundary_layer_total`, with `total_eq_two_layer` | `BoundaryLayer` |

## Section 5, periodic boundaries

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `sec:periodicwindow` | 5 | the weight `u^(cyclic switches)` is the periodic Ising weight with `u = e^{-2J}` | `pchg`, `cyclic_energy`, `periodic_weight_ising` | `Periodic` |
| `eq:periodicratio` | (33) | the cyclic count, and it is the ratio of bin `k` to an endpoint | `perWeightBin_eq_perRatio`, `perWeightBin_zero`, `perBin_ratio` | `Periodic` |
| `sec:periodicwindow` | 5 | `S^P_{N,1} = N u²` and the adjacent crossing `J = (log N)/4` | `perRatio_one`, `periodic_adjacent_threshold`, and `periodic_adjacent_crossing`, `periodic_adjacent_root_unique` over the rationals | `Periodic`, `AllbinAsymptotics`, `RunAlgebra` |
| `sec:periodicwindow` | 5 | the ratios increase strictly toward the middle and are symmetric | `perRatio_lt_inward`, `perRatio_symm` | `AllbinAsymptotics` |
| `thm:periodic-bessel`, `eq:periodicbound` | 5.1, (34) | `0 ≤ 1 - S^P_{N,k}(u)/Ŝ^P_{N,k}(u) ≤ N u²/2` | `periodic_bessel`, `perRatio_shift` | `UniformBessel` |
| `thm:periodic-crossing` | 5.2 | for `N ≥ 2` and `1 ≤ k ≤ N-1`, `S^P_{N,k}` increases strictly in `u ≥ 0`, and `S^P_{N,m_N}(u) = 1` has exactly one root `u_N^P > 0`, which lies in `(0, 1]` and is where the central bin ties with an endpoint, with `p_N^P = 1/(1 + u_N^P)` | `uNP`, `pNP`, `uNP_spec`, `perRatio_strictMonoOn`, `perRatio_exists_root`, `perRatio_eq_one_iff`, `perRatio_lt_one_iff`, `periodic_central_tie` | `PeriodicCrossing` |
| `thm:periodic-crossing` | 5.2 | Steps 1 and 2 of the proof: eventually `L/2 ≤ N u_N^P ≤ 3L`, and `z = N u_N^P` satisfies `z + (1/2) log z = L + c_P + (3/8)/z + ω` with `|ω| ≤ 120/L²` and `c_P = (1/2) log(π/2)` | `uNP_first_order`, `periodic_crossing_eq`, `cP`, with `perRatio_between`, `log_m_piece`, `omega_total` | `PeriodicCrossing` |
| `eq:periodicasym` | (35) | there is `C` with, for all large `N`, `|N u_N^P - (L - (1/2) log L + c_P + ((1/4) log L - c_P/2 + 3/8)/L)| ≤ C (log L)²/L²`, and the same for `N(1 - p_N^P)` | `periodic_expansion`, `periodic_expansion_prob`, `perMain`, with `log_inversion` | `PeriodicExpansion` |
| `eq:boundaryshift` | (36) | there is `C` with, for all large `N`, `|N(u_N^P - u_N^F) - (log 2 + (1/4 - (1/2) log 2)/L)| ≤ C (log L)²/L²` | `boundary_shift`, with `free_expansion_uN` | `PeriodicExpansion` |
| `eq:isingtemperature` | (37) | there is `C` with, for all large `N`, `|J_N^P - ((1/2)(L - log L) + ((1/4) log L - c_P/2)/L)| ≤ C (log L)²/L²`, where `J_N^P = -(1/2) log u_N^P` | `periodic_coupling`, with `coupling_of_expansion`, `log_of_expansion` | `PeriodicExpansion` |
| `thm:critical-window`, `eq:criticalprofile` | 5.3, (38) | for free and periodic ends, for every `T, Y ≥ 0` and `ε > 0` there is `N₀` such that for all `N ≥ N₀`, `|t| ≤ T`, `|y| ≤ Y` and every integer `k` with `|k - (N/2 + yN/√(log N))| ≤ 1/2`, `|S^X_{N,k}(u_N^X + t/N) - e^{t-2y²}| ≤ ε` | `free_window_profile`, `periodic_window_profile`, with `window_profile_of_core`, `free_profile_core`, `periodic_profile_core`, `free_form`, `periodic_form`, `profile_identity`, `shift_combo`, `etaR_bounds`, `eta_vs_y`, `h_est`, `uN_near`, `uNP_near` | `CriticalWindow` |
| `prop:walls` | 5.7 | for `N ≥ 2`, `u > 0`, `w = Nu` with `w(w+2) < 2N`, `Δ = -log(1 - w(w+2)/(2N))` and every `δ > 0`, `|𝒲_N(u) - w - χ(w)| ≤ w(e^δ - 1) + Δ/δ`, where `𝒲_N(u) = u S_N'(u)/S_N(u)` and `χ(w) = I_0(w)/(I_0(w) + I_1(w))` | `walls_bound`, `wallMean`, `wallMean_eq_deriv`, `chiW`, with `wallMean_mono`, `mean_index_mono`, `hasDerivAt_logSN`, `hasDerivAt_logF`, `chiW_antitone`, `turanT_nonneg`, `besselRatio_monotone` | `DomainWalls` |
| `prop:walls` | 5.7 | for all large `N`, `|𝒲_N(u_N) - (z_N + 1/2 + 1/(8z_N))| ≤ 55/(log N)²` | `walls_at_crossing`, with `chiW_asymp` | `DomainWalls` |
| `rem:ordered` | 5.8 | `P_N(0) + P_N(N) = p^(N-1)`, which is `1/2` at `u_ord = 2^{1/(N-1)} - 1`; `|J_ord - (1/2) log((N-1)/log 2)| ≤ 1/N` for `N ≥ 2`; `J_N^F = (1/2) log(N/z_N - 1)` | `full_order_prob`, `full_order_half`, `uOrd`, `jOrd`, `jOrd_asymp`, `jF_eq` | `FullOrder` |
| `rem:ordered` | 5.8 | for all large `N`, `|J_ord - J_N^F - (1/2) log(z_N/log 2)| ≤ 7 log N/N` and `|J_ord - J_N^F - ((1/2) log log N - (1/2) log log 2)| ≤ 7 log N/N + (log log N + 3)/log N` | `ordered_minus_free`, `ordered_minus_free_loglog` | `FullOrder` |
| `thm:critical-window`, `eq:criticalcount` | 5.3, (39) | for free and periodic ends and every real `t`, `(√(log N)/N) M^X_N(t) → √(2 max(t,0))`, where `M^X_N(t)` is the number of interior bins whose probability is strictly above the endpoint probability at the odds `u_N^X + t/N` | `free_window_count`, `periodic_window_count`, `freeAbove`, `periodicAbove`, with `count_limit`, `countAbove_eq_zero`, `countAbove_le`, `card_near_mid`, `free_mono`, `periodic_mono`, `Sab_comm` | `CriticalWindow` |
| `cor:couplings` | 5.5 | for all large `N`, `J_N^F`, `J_N^P`, `ξ(J_N^F)` and `ξ(J_N^P)` are positive | `couplings_eventually_pos` | `IsingDictionary` |
| `cor:couplings` | 5.5 | (a) for all large `N`, `|J_N^F - ((1/2)(L - log L) + ((1/4) log L - c_0/2)/L)| ≤ 28 (log L)²/L²`, where `J_N^F = -(1/2) log u_N` | `free_coupling` | `PeriodicExpansion` |
| `cor:couplings` | 5.5 | (b) for all large `N`, `|J_N^F - J_N^P - (log 2)/(2L)| ≤ 2 (log L)/L²` | `coupling_shift`, with `shift_final` | `PeriodicExpansion` |
| `cor:couplings` | 5.5 | (c) with `ξ(J) = -1/log tanh J`, for all large `N`, `|N/ξ(J_N^F) - (2L - log L + log(π/8))| ≤ 4 (log L)/L` and `|N/ξ(J_N^P) - (2L - log L + log(π/2))| ≤ 4 (log L)/L` | `corrLen`, `corrLen_free`, `corrLen_periodic`, with `N_div_corrLen`, `corrLen_of_expansion` | `PeriodicExpansion` |
| `sec:field` | 5 | for `1 ≤ a ≤ N-1`, `R^X_{N,a}(u) = S^X_{N,a}(u) e^{-2𝓑a}` increases strictly from `0` to `∞` in `u ≥ 0` and equals `1` at a single `u^{(a)}_N > 0`, and `R^X_{N,a}(u) < 1` exactly when `u < u^{(a)}_N`; `u^{(≥2)}_N = min_{2 ≤ a ≤ N-1} u^{(a)}_N` for `N ≥ 3`; `y_a(𝓑)` is the positive root of `H_a(y) = e^{2𝓑a}`, with `y_1(𝓑) = e^{2𝓑}` and `y_a(0) = y_a` | `Ends`, `edgeRatio`, `fieldRatio`, `fieldRoot`, `fieldRoot_spec`, `fieldRatio_lt_one_iff`, `one_lt_fieldRatio_iff`, `fieldRatio_eq_one_iff`, `fieldRatio_strictMonoOn`, `fieldRootGe2`, `fieldRootGe2_spec`, `yField`, `yField_spec`, `yField_unique`, `yField_one`, `yField_zero_field`, `yStar` | `FieldCrossing` |
| `thm:field` (a) | 5.9 | for free and periodic ends, every real `𝓑` and every fixed `a ≥ 1`, `N (u^{(a)}_N)² → y_a(𝓑)`, and `N (u^{(1)}_N)² → e^{2𝓑}` | `field_crossing_tendsto`, `field_crossing_one_tendsto`, with `edgeRatio_tendsto`, `free_edge_tendsto`, `periodic_edge_tendsto`, `perRatio_edge_form`, `tendsto_normCoeff_self` | `FieldCrossing` |
| `thm:field` (b) | 5.9 | the uniform tail bound `R^X_{N,a}(u) ≤ 4√Y e^{2√(Ya) - 2𝓑a}` for `0 < y = N u² ≤ Y` and every `1 ≤ a ≤ N-1`; for `𝓑 > 0`, `y_a(𝓑) → ∞`, the minimum `y_*(𝓑) = min_{a ≥ 2} y_a(𝓑)` is attained, and `N (u^{(≥2)}_N)² → y_*(𝓑)` | `fieldRatio_tail_bound`, `yField_tendsto_atTop`, `yStar_attained`, `field_crossing_ge2_tendsto`, with `edgeRatio_le_exp`, `tail_threshold`, `fieldRoot_tail`, `yField_tail`, `yStar_pos` | `FieldCrossing` |
| `thm:field` (c) | 5.9 | with `𝓑_c = (1/2) log 2`: `y_* < e^{2𝓑}` for `0 < 𝓑 < 𝓑_c`, `y_* = e^{2𝓑} = 2` at `𝓑_c`, and `y_* > e^{2𝓑}` for `𝓑 > 𝓑_c`; all three parts together for either boundary | `Bcrit`, `field_trichotomy`, `yStar_lt_of_lt`, `yStar_at_critical`, `lt_yStar_of_gt`, `thm_field`, with `Hedge_inv_mul_pow_le`, `Hedge_field_le`, `Hedge_two`, `two_pow_le_factorial_succ` | `FieldCrossing` |
| `tab:couplings` | Table 2 | every printed value is the correct rounding to three decimals of the quantity it names: `J_N^P`, the main terms of `eq:isingtemperature`, `(2 log N - 1)/5`, `0.3864 log N - 0.21055`, `J_N^F` and `J_N^F - J_N^P` (computed before rounding), for `N = 10, ..., 10⁶` | `tab_couplings_1` to `tab_couplings_6`, with `tv_uN_n`, `tv_uNP_n`, `tv_JP_n`, `tv_JF_n`, `tv_main_n`, `tv_log10`, `tv_cP`, `lt_uNP_of_tail`, `uNP_lt_of_partial` | `TableValuesCouplings`, `TableValuesCore` |

## Appendix A, the crossing at every N

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `app:every-n`, `eq:E-integral` | A.1, (40) | the integral form of `I_0 + I_1` and of `E` | `besselI0_add_besselI1_eq_integral`, `besselI0_add_besselI1_eq_J`, `besselE_eq_J` | `BesselIntegral` |
| `app:every-n` | A.1 | the cubic bounds on `√(1-y)`, the signs of `p` and `q` outside `[0,1]`, and the Gamma values | `sqrt_one_sub_ge`, `sqrt_one_sub_le`, `poly_p_pos`, `poly_q_nonpos`, `Gamma_half_values`, `integral_poly_gauss` | `BesselIntegral` |
| `app:every-n` | A.2 | Step 1, `ζ_N > 4` and the small quantities for `N ≥ 175` | `four_lt_zetaN`, `N_ge_exp`, `step0_bounds` | `EveryNLarge` |
| `app:every-n` | A.2 | Step 2, the upper bound, with `B > 0` and `D > 0` | `B_pos`, `D_pos`, `tW_le_tau`, `upper_key`, `every_N_upper_large` | `EveryNLarge` |
| `app:every-n` | A.2 | Step 3, the lower bound | `lower_key`, `U_sq_expand`, `every_N_lower_large` | `EveryNLarge` |
| `app:every-n` | A.3 | `d^(N-1) S_N(c/d)` is an integer, so the sign of `S_N(c/d) - 1` is a comparison of integers | `Snum`, `Snum_eq`, `Wfast_eq`, `chooseMul_eq` | `EveryN` |
| `eq:RN-formula` | A.4, (41) | the exact formula `R_N = log Λ_N - (log E(w) + 1/(8w)) - 1/(8N) - wz/N - (1/2) log(1 + w/N)`, in the equivalent form `log Λ_N - log E(w) - (w - z) - (1/2) log(w/z) - 1/(8z)` | inside `crossing_eq_large` | `CrossingEquation` |

## Numbers displayed in the text

A decimal written with `...` is a truncation and is stated as two bounds. The others are stated
with `RoundsTo` (correct rounding). All are in the module `TableValuesText`.
Rows that name another module in the column Where are in that module.

| Where | Number | Statement | Lean |
| --- | --- | --- | --- |
| introduction and Section 3 | `c_0 = -0.467...`, `-0.46735...` | `-0.46736 < (1/2) log(π/8) < -0.46735` | `tv_c0` |
| introduction | `0.84` | `z_N/L` at `N = 10⁴` rounds to `0.84` | `tv_zN_div_L_10000` |
| introduction | `4.576`, `4.578`, `4.405` | the row `N = 10⁵` of `tab:couplings` | `tab_couplings_5` |
| Figure 1 | `p_9 = 0.82829...` | `0.82829 ≤ p_9 < 0.82830` | `tv_p9` |
| after `thm:every-n` | `0.440`, `0.163`, `0.0387`, `0.00778` | `ε_N` at `N = 10, 10², 10³, 10⁴` | `tv_eps_10`, `tv_eps_100`, `tv_eps_1000`, `tv_eps_10000` |
| proof of `thm:every-n` | `174.25...` | `174.25 ≤ √(32/π) e⁴ < 174.26` | `tv_sqrt_exp4` |
| proof of `cor:every-n` (b) | `ν_2 > 0.40` | `log 2 - (1/2) log log 2 + c_0 > 0.40` | `tv_nu2` |
| after `rem:sign` | `0.0230`, `0.00126` | `L/(2N)` at `N = 100` and `N = 3200` | `tv_L_div_2N` |
| Section 5 | `0.385`, `0.417`, `0.450` | the secant slopes of `J_N^P` against `log N` on `[10, 10²]`, `[10², 10³]`, `[10⁴, 10⁵]` | `tv_secant_1_2`, `tv_secant_2_3`, `tv_secant_4_5` |
| Section 5 | `0.002`, `0.171`, `0.338` | `|main terms - J_N^P|`, `|(2L - 1)/5 - J_N^P|`, `|0.3864 L - 0.21055 - J_N^P|` at `N = 10⁵` | `tv_off_by_5` |
| caption of `tab:couplings` | `0.030` | `(log 2)/(2 log N)` at `N = 10⁵` | `tv_shift_100000` |
| `rem:ordered` | `1.046`, `1.330` | `J_ord - J_N^F` at `N = 10³` and `N = 10⁵`, with `J_ord = -(1/2) log(2^{1/(N-1)} - 1)` | `tv_Jord_3`, `tv_Jord_5` |
| after `rem:sign` (module `TableValuesBessel`) | `0.9761`, `0.9864`, `0.9924`, `0.99579`, `0.99769`, `0.99874` | `u_B/u_N` at `N = 100, 200, 400, 800, 1600, 3200`, with `u_B = x_B/h`, `h = N/2` and `x_B = Groot 1 (h/2)` the root of `F(x_B) = h` | `tv_uB_div_uN_100`, `tv_uB_div_uN_200`, `tv_uB_div_uN_400`, `tv_uB_div_uN_800`, `tv_uB_div_uN_1600`, `tv_uB_div_uN_3200`, with `tv_xB_N`, `tv_uN_N`, `lt_Groot_of_cert`, `Groot_lt_of_cert` |
| after `thm:field` (module `TableValuesField`) | `11`, `4`, `2`, `2` and `0.757`, `1.287`, `1.764`, `2.972` | for `𝓑 = 0.1, 0.2, 0.3, 0.5`: `y_*(𝓑) = y_{a⋆}(𝓑)` with `a⋆ = 11, 4, 2, 2`, `y_{a⋆}(𝓑) < y_a(𝓑)` for every other `a ≥ 2`, and the rounding of `y_*(𝓑)` | `tv_yStar_01`, `tv_yStar_02`, `tv_yStar_03`, `tv_yStar_05`, with `yStar_eq_of_cert`, `lt_yField_of_cert`, `yField_lt_of_cert`, `tail_explicit`, `tv_exp_field_n` |
| after `thm:field` (module `TableValuesField`) | `0.758`, `1.288`, `1.764`, `2.973` and `0.741`, `1.266`, `1.738`, `2.939` | `N (u_N^{(≥2)})²` at `N = 10⁴` for periodic and free ends, `u_N^{(≥2)} = fieldRootGe2` the minimum over all bins `2 ≤ a ≤ N-1` | `tv_fieldGe2_periodic_01`, `tv_fieldGe2_periodic_02`, `tv_fieldGe2_periodic_03`, `tv_fieldGe2_periodic_05`, `tv_fieldGe2_free_01`, `tv_fieldGe2_free_02`, `tv_fieldGe2_free_03`, `tv_fieldGe2_free_05`, with `fieldRootGe2_bounds`, `lt_fieldRoot_of_cert`, `fieldRoot_lt_of_cert`, `fieldRatio_tail_bound` |
| after `prop:walls` (module `TableValuesWalls`) | `0.5191`, `0.5166`, `0.5132` and `0.5224`, `0.5162`, `0.5126` | `𝒲_N(u_N) - z_N` and `1/2 + 1/(8z_N)` at `N = 10³, 10⁴, 10⁵`, with `𝒲_N = wallMean` | `tv_walls_1000`, `tv_walls_10000`, `tv_walls_100000`, with `tv_wallMean_N`, `wallMean_uN_bounds`, `wallMean_uN`, `wallSum_le` |
| `sec:walls` (module `TableValuesWalls`) | `0.061`, `0.048` | `1/(2𝒲_N(u_N))` at `N = 10⁴` and `N = 10⁵` | `tv_walls_10000`, `tv_walls_100000` |
| `sec:walls` (module `TableValuesWalls`) | `9.27`, `31.21` | the mean domain length `l_d = ⟨N/(n_d + δ_{0,n_d})⟩` at `u = u_N^P`, `N = 20` and `N = 100`, where `n_d = 2r` has weight proportional to `C(N,2r) u^{2r}` | `tv_domainLength_20`, `tv_domainLength_100`, with `domainLength`, `domainLength_bounds`, `tv_uNP_20` |
| caption of `fig:window` (module `TableValuesWalls`) | `0.12`, `0.08`, `0.06` | the relative error `|e^{-2} S^X_{N,N/2}(u^X_N + 2/N) - 1|` of the profile at `t = 2`, `y = 0`, against the limit `1`, at `N = 10⁴, 10⁶, 10⁸`, for free and for periodic ends | `tv_window_free_10000`, `tv_window_free_1000000`, `tv_window_free_100000000`, `tv_window_periodic_10000`, `tv_window_periodic_1000000`, `tv_window_periodic_100000000`, with `SN_ge_of_cert`, `SN_le_of_cert`, `perRatio_ge_of_cert`, `perRatio_le_of_cert`, `tv_uN_1e8`, `tv_uNP_1e8`, `tv_exp_neg2` |

## Not in this paper, kept in the repository for the tables note

The numerator tables and their bijections left Paper A for a separate note
(`paperA/tables_note/app_tables.tex`, labels as there). Step 4 of `thm:every-n` and Appendix A.3
now use Remark 2.3 (`rem:tables`), whose Lean theorems are listed in Section 2 above. The module
`Tables` remains imported by `PaperA.lean`. It proves identities between the numerators and
recursively defined sequences; the path interpretations and bijections are not formalized.

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
    `ℓ = log A` (`allbin_expansion`), and `a/2 ≤ A ≤ a`, so the two leading terms agree. The
    consequences displayed after the theorem, `eq:allbin-growing-edge` and the case
    `a/N → α`, are not stated in Lean.

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
    `w̄` and `w̄'` (named `W` and `W'` in Lean, with `U` for the paper's `Y`), but with other
    constants. It has `Y/N ≤ 0.0232`, `Y²/N ≤ 0.0933`,
    `Y³/N ≤ 0.376` and `ζ(ζ+1)/N ≤ 0.1148` in place of `0.023135`, `0.093262`, `0.375960` and
    `0.114776`, it gets them from `N ≥ 174.25 e^{ζ_N - 4}` and not from the monotonicity of
    `Y^k/n(ζ)`, it has no bound on `U⁴/N`, and it uses
    `log(1-x) ≥ -(x + x²/2 + x³/(1-x))`. So the decimal constants of Appendix A are not the ones
    Lean checks. The theorem is the same.
23. `thm:every-n` for `N ≤ 174`. The values `c` and `c'` in `everyNTable` are the columns
    `u_lo_times_1e9` and `u_hi_times_1e9` of `paperA/data/every_n_certificates.csv` for all 173
    values of `N`. Lean evaluates `d^(N-1) S_N(c/d)` by the run-count sum only, and the recursion
    `eq:dp` is the second method of the Python script. Lean brackets `ζ_N` on the grid `10⁻⁴`,
    with Taylor bounds for `exp` and `3.141592 < π < 3.141593`. The script brackets `ζ_N` with
    half-width `10⁻⁴⁵` using eighty-digit outward intervals. Its certified margins exceed
    `0.03319` and `0.08559`.

Partial coverage.

24. `lem:clipped` (a). Lean states it over the rationals for a list (`finite_product_deficit`) and
    over the reals for any finite family (`clipped_product_deficit`).
25. `lem:clipped` (b). `normCoeff m m r` is defined as `r!/m^r C(m-1,r)`, and `normCoeff_eq_prod`
    shows that it is the product `Π_{k=1}^r (1 - k/m)_+` for `m ≥ 1`.
26. `thm:every-n`, Step 1. Lean has `ζ_N > 4` for `N ≥ 175` (`four_lt_zetaN`) and `ζ_N < 4` for
    `1 ≤ N ≤ 174` (`zetaN_lt_four`). The names `step0_bounds` and `step0_fourth` are kept from an
    earlier numbering of the steps.
27. `eq:zetaN`. The Lambert form `ζ_N = (1/2) W_0(πN²/4)` is not in Lean.
    Monotonicity and `ζ_N ≤ L` are proved in `EveryNCorollary`.
28. `cor:every-n`. Part (a) and the finite inequalities of (b) are standalone theorems
    about the actual `pN`, `uN` and `zetaN`. The coupling is `-Real.log (uN N) / 2`.
    The asymptotic conclusions of (b) and (c) are proved with explicit constants for every
    N ≥ 21 (`|z_N - ν_N| ≤ 27 log L/L` and `52 (log L)²/L²`) and restated as `IsBigO` along
    `N → ∞`, which is stronger than the `O(·)` of the paper. The proof follows the paper's proof of
    (c), using `-log(1-x) ≤ x + 2x²` for `0 ≤ x ≤ 1/2` and `L⁴ ≤ 24 N` for the term
    `ζ_N(ζ_N+1)/N`.
    For (d), `EveryNSign` proves `6.5230 < ζ_2774 < 6.5231` by rational Taylor
    certificates. It extends the inequality using
    `z³(z+1) ≤ a³(a+1) exp(z-a)` for `4 ≤ a ≤ z` and the defining equation for ζ_N,
    rather than differentiating the function f in the paper.
29. `sec:allbin-order`. That `p_{a,b} = 2/3` exactly when `a = b = 1` is `pab_eq_two_thirds_iff`.
30. `prop:adjacent`. `global_min` and `extrema_at_pN` have weak inequalities, so they show that the
    named bins attain the minimum or maximum. The strict inequality `P_N(k) < P_N(k+1)` between
    interior bins, for `0 < p < 1`, `k ≥ 1` and `k + 2 ≤ N - k`, is `binProb_lt_inward`.
31. `thm:edge-laguerre`. The theorems of `EdgeExpansion` are over the rationals and take the
    coefficient equations of `eq:edge-implicit-expansion` as hypotheses. They do not by
    themselves establish coefficients of the actual crossing. The theorem itself is proved
    separately in `EdgeLaguerre` (see difference 40).
32. `sec:periodicwindow`. `perRatio` is defined as the polynomial of `eq:periodicratio`, and
    `perBin_ratio` shows that it is the ratio of the bin probabilities. The periodic central root
    `uNP N` is chosen among the roots in `(0, 1]` of `perRatio N (N/2)`, and
    `perRatio_eq_one_iff` shows that it is the only positive root. The ordering toward the
    middle is `perRatio_lt_inward` for `k + 2 ≤ N - k`, with `perRatio_symm`.
33. Appendix A.3. `Snum` is built from the coefficients `W`, so `Snum_eq` is the identity
    `d^(N-1) S_N(c/d) = Σ_j W(N,m_N,j) c^j d^(N-1-j)`, and `Snum_eq_numer` shows that it is the
    numerator `n_N(m_N)` with `α = d`, `β = c`, for `N ≥ 2` and `c, d > 0`.
34. `thm:edge-laguerre`. The variables of `EdgeExpansion` are rationals, while `y_a`, `c_a`,
    `H_a'(y_a)` and `H_a''(y_a)` are real and in general irrational (for example `y_2 = √3 - 1`).
    The statements are polynomial identities, so the same proof works over the reals, but Lean
    does not state the real version.
35. `prop:crossing-eq` for `N ≥ 175`. Lean follows Steps 1 to 3 of Appendix A.4 through the exact
    formula for `R_N`, with constants of its own. It bounds the Bessel part by `0.06/w²` in place
    of `0.0559/z²`, uses `log(1-x) ≥ -(x + x²/2 + x³/(1-x))` for `log Λ_N` and `log E(w)`, and
    `Y⁴ ≤ 1.6 N` (`step0_fourth`), and it shows that the terms of order `1/N` add up to at most
    `-5/N` with the margin `(z - 1/2)² ≥ 11.42`. So the decimal constants of Appendix A.4 are not
    the ones Lean checks. The bounds proved are the same.
36. `prop:crossing-eq` for `N ≤ 174`. Lean reuses the brackets of `everyNTable` for `u_N` and
    `ζ_N`, and checks over the rationals, with `decide +kernel`, that
    `x - 1 ≥ log x ≥ 1 - 1/x` already gives both remainder bounds at the bracket ends. It
    checks `L/2 ≤ z_N ≤ L` with the Taylor bounds for `exp` of `EveryN` at two grid points `T`
    and `T'` per row. The paper uses the outward-interval Python certificates instead.
37. `cor:boundary-layer`. Lean follows the paper's sandwich with explicit choices. For
    `θ ∈ (0, 1/2]` it applies `allbin_leading` with `ε = θ/4` at `a = ⌊(1-θ)d_N⌋` and with
    `ε = θ/10` at `c = ⌈(1+θ)d_N⌉`, where `d_N = Ω_N² log² Ω_N`, and it uses
    `v_N² N d_N = log² Ω_N`. The positivity of `v_N` is assumed only eventually.
38. `thm:periodic-crossing`, `cor:couplings`. Here `L = log N`. The `O` terms of
    `eq:periodicasym`, `eq:boundaryshift` and `eq:isingtemperature` are bounds `C (log L)²/L²`
    that hold for all large `N`, with a constant `C` that Lean shows exists but does not compute.
    The paper has only `o(1/log N)` in `eq:boundaryshift`, so Lean states more there. The
    constants of Corollary 5.5 are explicit (28, 2 and 4), and the threshold for "large `N`" is
    not computed. The couplings are `J = -(1/2) log u` at the crossings and `ξ(J)` is
    `-1/log tanh J`, as in the paper. Lean does not use the Taylor form of `log tanh` near `J = ∞`
    but the series of `log((1+u)/(1-u))`.
39. `sec:setting`, Ising dictionary. Lean defines `ξ(J)` by the formula `-1/log tanh J`, and
    difference 46 shows that it is the correlation length of the infinite chain. In
    `switching_scale_corrLen` the
    `O(u)` of the paper is the explicit bound `2u`.
46. `sec:setting`, the infinite chain (module `InfiniteChain`). The sites of a chain of `N` spins are `0, …, N-1`, and the
    weights are `exp(J ∑_{i<N} σ_i σ_{i+1})` (`freeEnergy`). `⟨σ_i σ_{i+r}⟩ = tanh(J)^r` holds
    for every real `J`. The infinite-volume function `infCorr` is defined as the limit over the
    boxes `[-M, M]`, and `tendsto_infCorr` gives the same limit along any family of intervals
    that eventually contains both sites. `corrLen_eq_decay` states
    `ξ(J) = 1/lim_r (-(1/r) log ⟨σ_0 σ_r⟩)` for `J > 0`.
40. `thm:allbin-expansion`, `thm:edge-laguerre`, `thm:edge-matching`. Each `O` term is a bound
    `K` times the paper's bracket that holds from some `a₀` (or `b₀`) on. Lean shows that `K` and
    the threshold exist but does not compute them. For Theorem 4.9 they are the same for every
    `b ≥ a`. For Theorem 4.10 they depend on `a`, as `O_a` allows. Lean proves Theorem 4.10 by a
    direct root argument rather than the implicit-function theorem. It bounds the exact edge
    series against its expansion with the second-order bound `1 - σ ≤ U_r(b) ≤ 1 - σ + σ²/2`,
    `σ = r(r+1)/(2b)`, and then shows that `S_{a,b} - 1` changes sign within `Mθ³` of
    `c_a - θ + γ_a θ²`. `H_a'` and `H_a''` are the sums `H1` and `H2`, and `hasDerivAt_Hedge`,
    `hasDerivAt_H1` show that they are the derivatives.
41. `thm:critical-window`. Lean takes every integer `k` within `1/2` of `N/2 + yN/√(log N)`, which
    covers both nearest-integer conventions. Uniformity on compact sets is stated on the boxes
    `|t| ≤ T`, `|y| ≤ Y`, which contain every compact set. For free ends `M^F_N(t)` counts the
    bins with `P_N(k) > P_N(0)` at `p = 1/(1+u)`, and for periodic ends `M^P_N(t)` uses `perBin`.
    No rate of convergence is stated.
43. `cor:fixed-M`. Lean writes the magnetization as `μ = a - b` with `a, b ≥ 1`, which is the
    paper's `|μ| < N`, `μ ≡ N (mod 2)`, and proves the statement for every real `J`, not only
    `J > 0`.
44. `prop:walls`. Lean defines `𝒲_N(u)` as the mean `Σ_j j W_j u^j / S_N(u)` of the law of the
    coefficients and proves it equals `u S_N'(u)/S_N(u)` (`wallMean_eq_deriv`). That `χ` decreases
    is proved from `T(x) = 2x(I_0(2x)² - I_1(2x)²) - I_0(2x) I_1(2x)`, which vanishes at `0` and has
    derivative `I_0(2x) I_1(2x)/x ≥ 0`, in place of the integral representation. The convexity of
    `log S_N(e^θ)` is used through the monotonicity of its derivative `𝒲_N(e^θ)`, with the mean
    value theorem. The `O((log N)⁻²)` at the crossing is the explicit bound `55/(log N)²` for all
    large `N`. The periodic analogue mentioned after the proposition is not stated.
45. `rem:ordered`. The `O(1/N)`, `O(log N/N)` and `o(1)` of the remark are explicit bounds for
    all large `N`. The numerical values `1.046` and `1.330` are certified in `TableValuesText`.
42. `rem:sign`. For `2 ≤ N ≤ 2773` Lean checks one rational `r_N = n/10⁷` per `N` that lies
    strictly between `z_N` and `ζ_N`. The side of `ζ_N` is an integer inequality from ten-term
    Taylor bounds for `exp(n/(32·10⁷))`, raised to the power `64`, and `π` to twenty decimals. The
    side of `z_N` is the sign of `S_N(n/(10⁷N - n)) - 1` in integers, evaluated by `SnumFast`,
    which `SnumFast_eq` identifies with `Snum`. The kernel checks all 2772 certificates with
    `decide +kernel`, which takes about ten minutes. The numbers `n` were found in floating point,
    and they are data only. The paper replays its own outward-interval brackets instead.

47. `thm:field`. Lean defines `R^X_{N,a}(u)` by the paper's formula `S^X_{N,a}(u) e^{-2𝓑a}`;
    the Ising weights with a field, from which the paper reads off this ratio by the symmetry of
    the row, are not formalized. Part (a) is proved for every real `𝓑`, not only `𝓑 > 0`. The
    minimum `y_*(𝓑)` is defined as the infimum of `y_a(𝓑)` over `a ≥ 2`, and `yStar_attained`
    proves that it is attained. The threshold `A(Y)` of the tail bound is explicit,
    `max(2, ⌈(4√Y + Y/𝓑)/𝓑⌉)`, from `2√(Ya) ≤ Y/𝓑 + 𝓑a` and `x < e^x`. The limits of part (a)
    use only the pointwise limit `S^X_{N,a}(√(y/N)) → H_a(y)` and monotonicity, not the uniform
    limit on compact sets. The couplings `J_N^{(1)}`, `J_N^{(≥2)}` displayed after the theorem
    are not formalized.
48. `tab:every-n`, `tab:couplings`. `RoundsTo x m k` means `|x - m/10^k| < 10^{-k}/2`. Lean
    brackets `u_N` and `u_N^P` between `c/10²⁵` and `(c+1)/10²⁵` with the first terms of the
    exact polynomials and a geometric bound on the rest, `ζ_N` with width `10⁻¹⁵`, and each
    logarithm with Taylor bounds for `exp`, with `π` to 20 decimals. The rationals were chosen
    in floating point and are data only. The paper computes the tables in 50-digit and
    floating-point arithmetic instead.

49. After `rem:sign`, the ratios `u_B/u_N` (module `TableValuesBessel`). The Bessel root is
    `x_B = Groot 1 (h/2)`, the root of `G_1(x) = x(I_0(2x) + I_1(2x)) = h/2`, which is
    `F(x_B) = h` (`central_root_bound`). Lean brackets `x_B` with width `10⁻¹⁵` by the first `30`
    terms of the series of `I_0(2x) + I_1(2x)` at the two rational endpoints, with the geometric
    bound `ρ = x²/31²` on the rest, and `u_N` with width `10⁻²⁵` as in difference 48. The rational
    inequalities are checked by `decide +kernel`.

50. After `thm:field`, the examples (module `TableValuesField`). The field is the real number
    `1/10`, `1/5`, `3/10` or `1/2`, and `e^{2𝓑a}` is compared through `(e^{2𝓑})^a` with rational
    bounds on `e^{2𝓑}` of width `10⁻²⁰`. For the limit, a separating rational `s` is chosen with
    `H_{a⋆}(s) > e^{2𝓑a⋆}` and `H_a(s) < e^{2𝓑a}` for every `2 ≤ a < A`, `a ≠ a⋆`
    (`A = 90, 41, 27, 18`); for `a ≥ A`, `y_a(𝓑) > s` follows from the limit `N → ∞` of
    `fieldRatio_tail_bound` at `Y = s`. The value `y_{a⋆}(𝓑)` is bracketed with width `10⁻¹²`. At
    `N = 10⁴` every bin `2 ≤ a < A` (`A ≤ 90`) is checked at a rational `u_l`, the bins
    `A ≤ a ≤ N-1` are excluded by `fieldRatio_tail_bound` at `Y = N u_l²`, and the bin `a⋆`
    gives the upper bound at `u_l + 10⁻¹⁵`. The threshold is explicit (`tail_explicit`): for
    `0 < c ≤ 2𝓑`, `2√(Ya) ≤ Y/c + ca` and `e^E ≥ 1 + E + E²/2`. The polynomials are evaluated
    exactly over `ℚ` (`HedgeQ`, `SabQ`, `perRatioQ`), with `C(n,k) = n(n-1)⋯(n-k+1)/k!`, and the
    kernel checks them with `decide +kernel`. Lean does not prove that the minimizing bin at
    `N = 10⁴` is `a⋆`, which the paper does not state.

51. Section 5, the numbers of module `TableValuesWalls`. Since `S_N(u_N) = 1`,
    `𝒲_N(u_N) = ∑_j j W_j u_N^j` (`wallMean_uN`), which increases in `u_N`. Lean bounds it
    below by the first `2T` terms at the lower end of the bracket of `u_N` and above by the first
    `2T` terms at the upper end and the geometric tail `ρ = (2T+1)(N-2)u/(4T²)`, from
    `2T W_{j+1} ≤ (N-2) W_j` for `j ≥ 2T` (`T = 16, 19, 22`). The bounds on `z_N` are those of
    difference 48. For `l_d` Lean takes the law of `n_d` stated in the paper,
    `n_d = 2r` with weight proportional to `C(N,2r) u^{2r}` (`domainLength`), and does not derive
    it from the periodic Ising weights; numerator and denominator increase in `u`, so the bracket
    of `u_N^P` bounds `l_d`. At `y = 0` the bin of Theorem `thm:critical-window` is `k = N/2`, so
    the profile at `t = 2` is `e^{-2} S_N(u_N + 2/N)` for free ends and
    `e^{-2} S^P_{N,N/2}(u_N^P + 2/N)` for periodic ends, and its relative error against the
    limit `e^{-2y²} = 1` is `|e^{-2} S - 1|`. Lean bounds `S` at the two ends of the bracket
    shifted by `2/N` with the truncated sums of `TableValuesCore`, and `e²` with Taylor bounds.
    Not certified, because the paper does not define them precisely enough: the least-squares
    exponent `0.755` of `l_d` on `20 ≤ N ≤ 100` (the paper does not say which `N` enter the fit;
    the fit of `log l_d` against `log N` over all integers `20 ≤ N ≤ 100` gives `0.7557`, which
    rounds to `0.756`, and over the even `N` it gives `0.7555`), the local exponent `0.74` of
    `N/log N` on that range (the local slope `1 - 1/log N` runs from `0.666` to `0.783` there;
    the least-squares slope over the integers is `0.7400` and the secant slope is `0.733`), and
    the bound `0.013` after Corollary `cor:boundary-layer` (the values of `N` plotted in panel
    (b) of Figure `fig:layer` are not listed, and `𝓛_N` up to `N = 10¹²` would need about `10⁶`
    bins per point).

## Not in Lean

The following parts of the paper are not formalized. The finite results and conditional algebra
listed above do not supply these omitted limit statements or their error bounds.

* Section 4. Remarks 4.5 (`rem:sign-correction`) and 4.7 (`rem:jacobi`), and the
  consequences of Theorem 4.9 displayed after it (`eq:allbin-growing-edge` and the case
  `a/N → α`).
* Section 5. Remarks 5.4 and 5.6.
* Appendix A. The outward-interval Python calculations (Lean has its own rational bounds for
  the results listed above).
* The uniform local law (the local law note, not in Lean).
* The decimals `0.755`, `0.74` (Section 5) and `0.013` (after Corollary `cor:boundary-layer`), which the paper does not define precisely enough to certify (difference 51).

## Findings while checking

* No mathematical error was found in the statements above.
* Apart from the differences listed above, every result that the verification section of the
  paper says is in Lean has a Lean theorem with the same hypotheses, constants and ranges. This
  includes `N ≥ 2` in `thm:root`, `thm:bessel`, `lem:bracket` and `thm:every-n`, the strict
  inequalities of `thm:every-n`, and the definitions of `p_N`, `u_N`, `ζ_N` and `S_N`.
