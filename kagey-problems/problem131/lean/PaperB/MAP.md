# Paper B: map from the paper to the Lean theorems

This file matches the statements of Paper B, "Vertex crossings in a symmetric Markov multinomial
model" (`paperB/problem131_multistate.tex`), to the Lean theorems of
the library `PaperB` (root `PaperB.lean`, 19 modules in `PaperB/`, namespace `Kagey131.PaperB`).
The library uses Lean 4 v4.33.1 and Mathlib v4.33.1. Every theorem listed here is proved without
`sorry`, `admit` or new axioms. `#print axioms` on each of the 307 theorems of the library reports
only `propext`, `Classical.choice` and `Quot.sound` (see `build-log.txt` and
`verification-manifest.json` in the parent folder).

The primary key of each row is the `\label` of the statement in the source. The column Number
gives its number in the built PDF (`paperB/problem131_multistate.pdf`, the 39-page build of
2026-10-02), and it has to be refreshed when the paper is rebuilt. A row whose Number is
"removed" is a statement that was cut from the paper on 2026-10-02. Its text is kept in
`paperB/removed_proofs/B_removed_2026-10-02.tex`, and its Lean theorems are still in the library. A number with § is a section or subsection, a number in parentheses is
an equation, and any other number is a theorem, lemma, proposition, corollary, example or remark.
"In part" means that the finite or exact core of the statement is in Lean and the rest is listed
under "Not in Lean" below.

Lean numbers the states from 0, so state `i` of the paper is state `i - 1` in Lean. A word of
length `N` is a function `Fin (n+1) → Fin d` with `N = n + 1`, so `law d p n k` is the paper's
`P_N(k)` with `N = n + 1`. The start is uniform in every Lean statement. A positive count is
written `m + 1`, so the polynomial `B_a` of the paper is `Bpoly (m + 1)` with `a = m + 1`, and the
large count near a vertex is `b = c + 1`.

## Modules

| Module | Content |
| --- | --- |
| `Model` | words, changes, the word probability, the law `P_N(k)`, total mass one, the vertex probability and the ratio to a vertex |
| `Refresh` | the polynomials `B_n`, the recurrence for the last letter and the refresh form of the law |
| `Words` | words as lists, the polynomial `S_n(u)` as a sum over words, and the injection that doubles the first letter of a run |
| `Crossing` | the unique crossing of every bin with at least two positive coordinates, its growth with `N` for balanced bins, and `p_{k,k}` |
| `Coefficients` | the first two nonzero coefficients of `S_n` |
| `LogConcave` | strict log-concavity of `B_n(y)` in `n` and the transfer inequality |
| `Balance` | the integral form of the law, the multinomial case, the transfer of one unit, and symmetry under permutations |
| `EdgeExample` | the ratio form of the law and the example with `d = 3` and `N = 4` |
| `Clipped` | the clipped product deficit |
| `Constants` | the order of the constants `a_k` and the second differences of `c_k` |
| `Modes` | the lines of the field `h_i = -H(i-1)^2`, the triangle example and the Gram determinant |
| `Covariance` | powers of the transition matrix and the finite geometric double sum |
| `ChainCovariance` | the two-point marginals, the mean and the covariance of the occupation counts |
| `LaguerreBessel` | the series `Φ` and the Laguerre-Bessel inequality |
| `Elasticity` | the elasticity of one factor `B_a` |
| `VertexH` | the polynomial `H` of the rare counts, its convexity, the concavity of `log H` and the root `y_a` |
| `VertexRoot` | the arithmetic of the bracket near a vertex |
| `Randomization` | the integral form of `S_(b,a)`, the Jensen and tangent bounds, and the bracket near a vertex |
| `Singleton` | singleton insertion and `S_(b,1,...,1)`, which the paper does not state |

## Section 1, setting and notation

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `sec:setting` | §1.2 | the word probability `(1/d) p^(N-1-j) r^j` for a word with `j` changes (the Potts form) | `pathWeight_eq`, `wordProb_eq` | `Model` |
| `sec:setting` | §1.2 | the law has total mass one | `sum_wordProb`, `sum_law` | `Model` |
| `sec:setting` | §1.2 | `V_N = p^(N-1)/d` | `law_vertex`, `occ_eq_vertex_iff` | `Model` |
| `sec:setting` | §1.2 | bins that differ by a permutation of the states have the same probability | `law_perm` | `Balance` |

## Section 2, the model and the exact law

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `prop:dgf` | 2.1 | in part, the step of the proof that conditions on the last letter, `E_a(k + e_a) = σ E_a(k) + r P(k)` | `endLaw_succ`, `law_eq_sum_endLaw`, `endLaw_of_zero` | `Refresh` |
| `prop:dpmf` | 2.2 | (a), the refresh form for the uniform start | `law_closed`, with `endLaw_closed`, `Bpoly_derivative_succ`, `coeff_Bpoly` | `Refresh` |
| `prop:dpmf` | 2.2 | (b), `P_N(k)/V_N = S_n(u)` for the uniform start | `law_div_vertex`, `law_eq_SL`, `law_eq_V_SL`, `sum_changes_eq_SL` | `Model`, `Words`, `Crossing` |
| `prop:dpmf`, `eq:simplex-positive-sum` | 2.2, (3) | (c), the ratio form | `law_div_closed`, `WP_eq_CP` | `EdgeExample`, `Coefficients` |
| `sec:multistate-model` | §2 | the text after Proposition 2.2, the multinomial law at `p = 1/d` | `law_multinomial`, `PiB_coeff_top` | `Balance` |

## Section 3, the tie and its resolution

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `thm:simplex-window` | 3.1 | (iv), `a_2 > a_3 > ...` | `aConst_strictAnti`, with `gfun_strictMonoOn`, `Hfun_pos` | `Constants` |
| `thm:simplex-crossing` | 3.2 | exactly one crossing in `(0,1)`, with the bin above the vertex below it and below the vertex above it | `face_crossing`, with `SL_strictMonoOn`, `SL_zero`, `SL_root`, `SL_at_crossing`, `uOf_strictAnti` | `Crossing` |
| `thm:simplex-crossing` | 3.2 | `p_{N,k}` is strictly increasing in `N` | `face_crossing_strictMono`, with `faceBal_root_lt`, `SL_lt_SL_succ`, `dupFirst_injective`, `lch_dupFirst`, `faceBal_succ` | `Crossing`, `Words` |
| `thm:simplex-crossing` | 3.2 | `S_n = k! u^(k-1)` at `N = k` and the formula for `p_{k,k}` | `SL_faceBal_self`, `face_crossing_kk` | `Crossing` |
| `thm:simplex-crossing` | 3.2 | `(k!)^(-1/(k-1)) < 1` | `kk_odds_lt_one` | `Crossing` |
| `thm:simplex-crossing` | 3.2 | the coefficients `W_n(j) = 0` for `j < k-1`, `W_n(k-1) = k!` and `W_n(k) = k!(k-1)(N-k)/2` (in the paragraph on the idea of the proofs and in the proof) | `W_first`, `W_second`, with `WP_coeff`, `PiB_low` | `Coefficients` |
| `thm:simplex-balance` | 3.8 | moving one unit from `b` to `a` with `k_b ≥ k_a + 2` and `k_a ≥ 1` strictly increases the probability, for `1/d ≤ p < 1` | `law_transfer` | `Balance` |
| `thm:simplex-balance` | 3.8 | in part, every maximizer among the bins with a given support and total is balanced | `law_max_balanced`, `law_perm` | `Balance` |
| `eq:simplex-balance-integral` | (17) | the integral form `P_N(n) = σ^(N-1)/(dv) ∫ e^(-t) ∏ B_{n_i}(vt) dt` for `1/d < p < 1` | `law_integral`, with `integral_exp_neg_pow`, `integral_exp_poly`, `sig_pos`, `rr_pos` | `Balance` |
| `thm:simplex-balance` | 3.8 | Step 2 of the proof, strict log-concavity of `B_n(y)` for `n ≥ 1` and `y > 0` | `Bpoly_logconcave`, with `bb_succ`, `cc_bb_strict`, `bb_logconcave`, `pair_identity` | `LogConcave` |
| `thm:simplex-balance` | 3.8 | Step 3 of the proof, `B_{a+1} B_{b-1} > B_a B_b` for `b ≥ a + 2` and `a ≥ 1` | `Bpoly_transfer`, `Bratio_strictAnti` | `LogConcave` |
| `ex:simplex-edge-mode` | 3.10 | `P_4(2,2,0)/V_4 = 2u + 2u^2 + 2u^3` and `P_4(2,1,1)/V_4 = 6u^2 + 6u^3` | `ratio_220`, `ratio_211` | `EdgeExample` |
| `ex:simplex-edge-mode` | 3.10 | `u = 7/20` at `p = 10/17`, and the values `4123/4000` and `3969/4000` | `u_at`, `edge_ratio`, `center_ratio` | `EdgeExample` |
| `ex:simplex-edge-mode` | 3.10 | the three edge centers are the only global modes | `edge_modes`, `classify4` | `EdgeExample` |

## Section 5, a weak Potts field

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `prop:field-tilt` | 5.1 | (3), in the proof, `T^m = σ^m I + (1 - σ^m) J/d` | `trans_pow`, `trans_eq_Tmat` | `Covariance`, `ChainCovariance` |
| `prop:field-tilt` | 5.1 | (3), in the proof, `E K_{N,a} = N/d` | `mean_occ` | `ChainCovariance` |
| `prop:field-tilt` | 5.1 | (3), in the proof, the covariance `σ^m (1/d - 1/d^2)` of the indicators of state `a` at two times | `twoPoint`, `twoPoint_abs`, `cov_kernel` | `ChainCovariance`, `Covariance` |
| `prop:field-tilt` | 5.1 | (3), in the proof, the formula for `Var K_{N,a}` | `cov_occ`, `cov_occ_closed` (with `a = b`), `sum_sigma_abs` | `ChainCovariance`, `Covariance` |
| `thm:weakfield-phases` | 5.2 | in part, Step 3 of the proof (a line of larger slope that wins at `t_1` wins at every `t_2 > t_1`) | `winning_size_monotone` | `Modes` |
| `rem:frontier-superlevel` | removed | in part, the Gram determinant `k` of the vectors `e_i - e_k`, whose square root is the covolume `√k` | `gram_det`, `latVec_gram` | `Modes` |
| `ex:weakfield-triangle` | 5.3 | in part, the comparison of the three scores and the condition `H > 6(a_2 - a_3)` | `triangle_edge_phase`, `triangle_interval_nonempty` | `Modes` |
| `cor:weakfield-full-hierarchy` | 5.4 | the average `(k-1)(2k-1)/6` of `(i-1)^2` over `i ≤ k` | `field_average`, `sum_sq_range` | `Modes` |
| `cor:weakfield-full-hierarchy` | 5.4 | `c_1 = 0` and `c_k = -(k-1) a_k` | `cConst_one`, `cConst_eq_aConst` | `Constants` |
| `cor:weakfield-full-hierarchy` | 5.4 | `c_{k+2} - 2c_{k+1} + c_k ≤ 1/2` | `cConst_second_diff`, `cConst_sub_concave` | `Constants` |
| `cor:weakfield-full-hierarchy`, `eq:weakfield-lines` | 5.4, (11) | `ℓ_{k+1}(t) - ℓ_k(t) = t - t_k` and `ℓ_1 = 0` | `lam_succ_sub`, `lam_one` | `Modes` |
| `cor:weakfield-full-hierarchy` | 5.4 | `t_1 < t_2 < ...` for `H > 3/4` | `tau_lt_succ`, `tau_strictMono`, `tau_mono` | `Modes` |
| `cor:weakfield-full-hierarchy` | 5.4 | in part, for `t_{k-1} < t < t_k` the line `k` strictly exceeds every other line | `line_unique_max` | `Modes` |

## Section 6, near the boundary of the simplex

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `lem:uniform-laguerre-bessel`, `eq:uniform-laguerre-bessel` | 6.1, (12) | `0 ≤ 1 - B_a(w)/(w Φ(aw)) ≤ w/2` for every integer `a ≥ 1` and `w > 0` | `laguerre_bessel`, `laguerre_bessel_diff`, with `clipTau_eq`, `clipTau_deficit`, `Zf_eq_tsum`, `phi_summable`, `Phi_pos` | `LaguerreBessel` |
| `sec:vertex-completion` | §6.1 | `𝓗(y) = 1` has exactly one positive root `y_a`, and `y_a ≤ 1` (the paper's `𝓗` is `H` in Lean) | `H_root`, `H_strictMonoOn`, `H_one_ge` | `VertexH` |
| `sec:vertex-completion` | §6.1 | `S_(b,a)(u) = 1` has exactly one positive root | `SL_root`, `SL_strictMonoOn` (with the vector `kvec c m`) | `Crossing`, `Randomization` |
| `thm:vertex-uniform-root`, `eq:vertex-uniform-bracket` | 6.4, (14) | the bracket `(1-δ)√(y_a/b) ≤ u_{b,a} ≤ (1+δ)√(y_a/b)` for `δ = 16 c_ℓ ε ≤ 1/2` | `vertex_uniform_root`, with `vertex_bracket`, `logH_increment`, `upper_step`, `lower_step`, `lower_core`, `s_bound`, `log_chain` | `Randomization`, `VertexRoot` |

## Appendices

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `lem:bessel-law` | A.1 | in part, (i) in the form `∑_j j(j+1) x^j/(j!(j+1)!) = x Φ(x)` | `tsum_phiTerm2`, `phiTerm2_succ` | `LaguerreBessel` |
| `lem:clipped-product` | A.2 | `0 ≤ 1 - ∏ (1 - t_j)_+ ≤ ∑ t_j` | `clipped_product`, `clipped_product_aux` | `Clipped` |
| `eq:boundary-integral-form` | (21) | in part, the integral form of `S_n(u)`, as the integral form of the law and for the vector `(b, a_1, ..., a_ℓ)` | `law_integral`, `S_integral` | `Balance`, `Randomization` |
| `lem:vertex-elasticity` | D.1 | `𝓗` is convex | `H_convexOn`, `H_coeff_nonneg` | `VertexH` |
| `lem:vertex-elasticity` | D.1 | `log 𝓗` is concave on `(0,∞)` | `logH_concaveOn`, `logB_concaveOn` | `VertexH` |
| `lem:vertex-elasticity` | D.1 | `κ = y 𝓗'/𝓗` is the sum of the elasticities of the factors and is nondecreasing | `kapH_eq`, `kap_eq`, `kapH_monotoneOn`, `kap_monotoneOn` | `VertexH`, `Elasticity` |
| `lem:vertex-elasticity`, `eq:vertex-elasticity` | D.1, (27) | `1/(\|a\|+1) ≤ y_a ≤ 1` | `H_root`, `H_small_lt`, `H_one_ge`, `Bpoly_le_exp`, `exp_half_lt_two` | `VertexH` |
| `lem:vertex-elasticity`, `eq:vertex-elasticity` | D.1, (27) | `κ(y) ≤ ℓ + √(ℓ\|a\|y)` | `kapH_le`, `kap_le` | `VertexH`, `Elasticity` |
| `lem:vertex-elasticity`, `eq:vertex-elasticity` | D.1, (27) | `κ(y) ≥ max{ℓ, ½√(\|a\|y)}` for `0 < y ≤ 1` | `kapH_ge`, `kapH_ge_half_sqrt`, `kap_ge_one`, `kap_ge_half_sqrt`, `kap_ge_sqrt_sub` | `VertexH`, `Elasticity` |
| `lem:vertex-elasticity` | D.1 | Step 1 of the proof, the ratio identity and `Var J ≤ E J` | `wt_shift`, `shift_sum`, `cov_JR`, `var_le` | `Elasticity` |
| `lem:vertex-elasticity` | D.1 | Step 3 of the proof, `ay = κ_a^2 + Var J + (y-1)κ_a` and `κ_a^2 + yκ_a ≥ ay + 1` | `ode_moment`, `kap_sq_add`, `cs_moment` | `Elasticity` |
| `lem:vertex-randomization` | D.2 | in part, the integral form of `S_(b,a)`, the mass `v(1+v)^(b-1)` of `e^(-t) B_b(vt)`, its first moment and its exponential moments | `S_integral`, `L1_eq`, `Lt_eq`, `sum_choose_mul`, `Ls_eq`, `binom_inv_sum` | `Randomization` |
| `lem:vertex-randomization`, `eq:vertex-jensen-lower` | D.2, (29) | `(1-u)^(\|a\|) 𝓗(bu^2) ≤ S_(b,a)(u)` | `jensen_lower` | `Randomization` |
| `lem:vertex-randomization`, `eq:vertex-tangent-upper` | D.2, (30) | the upper bound for `s = κ/(bu(1-u)) < 1` | `tangent_upper` | `Randomization` |

## Statements of Paper B that are checked in the library `PaperC`

| Label | Number | Statement | Lean | Module |
| --- | --- | --- | --- | --- |
| `sec:setting` | §1.2 | `λ_F = d - k` on the complete graph | `completeQ_isLeast`, `completeQ_dirEig` | `PaperC.Spectra` |
| `eq:intro-ak` | (1) | `a_k = -(1/(k-1)) log D_k` with `D_k = k^(k+1/2) (4π)^(-(k-1)/2)` | `paperB_constant` | `PaperC.Constants` |
| `thm:simplex-window` | 3.1 | (ii), the arithmetic `τ λ_F + k - 1 = d - 1` at `τ = 1` | `complete_tie`, `complete_costs` | `PaperC.Spectra` |
| `lem:occupation-covariance` | 3.4 | in part, the determinant of the matrix of the proof for `k = 2` and `k = 3` only | `tree_formula_two`, `tree_formula_three` | `PaperC.Constants` |
| `lem:weighted-cayley` | 3.5 | the case `k = 3` only | `cayley_three` | `PaperC.Constants` |
| `ex:K3-start` | 4.9 | the arithmetic of the window `(a_2, t_ef)`, with width `log(16/(9√3)) > 0` | `three_lines`, `k3_edge_window`, `k3_window_width`, `k3_edge_criterion`, `k3_half_half_criterion` | `PaperC.Constants` |

## Lean theorems that the paper does not state

| Content | Lean | Module |
| --- | --- | --- |
| Singleton insertion, `S_(n,1)(u) = [2u + (M-1)u^2] S_n(u) + (u - u^2) u S_n'(u)` for a count vector `n` with total `M ≥ 1` | `singleton_insertion`, `insert_sum`, `sum_wordsK_insert`, `DSL_eq` | `Singleton` |
| `S_(b,1)(u) = 2u + (b-1)u^2` and `S_(b,1,1)(u) = 6u^2 + 6(b-1)u^3 + (b-1)(b-2)u^4` | `SL_b1`, `SL_b11` | `Singleton` |
| `S_(b,1,...,1)(u) = ℓ! ∑_q C(ℓ+1,q) C(b-1,q-1) u^(q+ℓ-1)` with `ℓ` singleton states | `SL_singletons`, `Fsing_step`, `sing_coeff` | `Singleton` |
| The covariance of two different occupation counts, `Cov(K_a, K_b) = -(1/d^2) ∑_{i,j<N} σ^\|i-j\|` for `a ≠ b` | `cov_occ`, `cov_occ_closed` | `ChainCovariance` |
| The double sum at `σ = 1`, and `(1+σ)/(1-σ) = (d-2+dp)/(d(1-p))` | `sum_sigma_abs_one`, `ratio_identity` | `Covariance` |

## Differences between the Lean statements and the paper

We compared each Lean statement with the paper by hand (hypotheses, constants, ranges, strictness
and definitions). No Lean statement contradicts the paper. The differences are the following.

1. The start. Every Lean statement is for the uniform start. The definitions `wordProb` and `law`
   have the factor `1/d` built in. So the first display of Proposition 2.2(a), Proposition 2.2(b)
   with `μ` and the polynomials `S^{(a)}_n` are not in Lean.
2. `prop:dgf`. Lean has no formal power series. It has only the recurrence that the proof starts
   from, `endLaw_succ`, for the uniform start.
3. `prop:dpmf`(a). The paper writes the multinomial sum over the vectors `m`. `law_closed` writes
   `P_N(k) = (1/d) ∑_{M=0}^{N-1} r^M σ^(N-1-M) (M+1)! [s^(M+1)] ∏_i B_{k_i}(s)` with `B_0 = 1`. So
   the paper's `M` is `M + 1` in Lean. The coefficient of the product equals the sum over `m` of
   `∏ C(k_i-1, m_i-1)/m_i!`, but this expansion is not carried out in Lean. The Lean statement
   holds for every real `p`, as the paper's proof does. `law_multinomial` gives the law at
   `p = 1/d` in the form `(1/d) r^(N-1) N! ∏ 1/k_i!` and does not substitute `r = 1/d`.
4. `prop:dpmf`(b). Lean assumes `p ≠ 0` and `d ≠ 0` where the paper has `p > 0`. `S_n(u)` is the
   sum `SL` of `u^(changes)` over the words with counts `k`, and the paper's `W_n(j)` is `Wcount`.
5. `S_n` and the number of states. The paper defines `S_n` for the vector `n` of positive
   coordinates and notes that it does not depend on `d`. In Lean `SL d N k` is indexed by the full
   vector `k` on `d` states, and it is not proved that `SL` is unchanged when states with count
   zero are added or removed. So every Lean statement about `S_n` is for one fixed `d`. This
   matters in note 23.
6. `prop:dpmf`(c) and `eq:simplex-positive-sum`. `law_div_closed` has the terms
   `u^(M-1) (1-u)^(N-M)` (in the paper's `M`) and holds for every `p ≠ 0`. The paper writes
   `(1-u)^(N-1) v^(M-1)` with `v = u/(1-u)` and assumes `1/d < p < 1`. The two forms agree for
   `u ≠ 1`. Lean does not state that the terms are positive.
7. `thm:simplex-crossing`, the crossing. `face_crossing` is more general than the paper. It holds
   for every bin with at least two positive coordinates, balanced or not. It states existence and
   the two strict inequalities, from which uniqueness follows.
8. `thm:simplex-crossing`, monotonicity. `face_crossing_strictMono` is one step, from `N` to
   `N + 1`, for the balanced vector `faceBal d k N` on the first `k` states, with both crossings
   given as hypotheses. The paper speaks of any balanced bin with `k` positive coordinates. The
   two agree by `law_perm`, but Lean does not prove that every balanced bin is a permutation of
   `faceBal`. The strict increase of `S_n(u)` in `N` (`SL_lt_SL_succ`) comes in Lean from the
   injection that doubles a first letter plus one word outside its image. The paper uses the
   strict growth of the coefficient `W_n(k)` instead.
9. `thm:simplex-crossing`, the bound on `u`. Lean has `(k!)^(-1/(k-1)) < 1` (`kk_odds_lt_one`),
   the value of the root at `N = k` and the decrease of the root with `N` (`faceBal_root_lt`). The
   conclusions `u ≤ (k!)^(-1/(k-1))` at every crossing and `p_{N,k} > 1/d` are not stated as
   theorems.
10. `thm:simplex-crossing`, the coefficients. `W_first` and `W_second` hold for every count vector
    with `k` positive coordinates, not only balanced ones, and assume `d ≥ 2`. `W_second` is
    stated as `2 W_n(k) = k!(k-1)(N-k)`. The Lean proof reads the coefficients from the closed
    form. The paper counts sequences of run colors.
11. `thm:simplex-window`(iv). The statement is the same. The paper's `f` and `Δ` are `gfun` and
    `Hfun` in Lean (the docstring of `Constants` calls them `g` and `H`). Lean proves `Δ(x) > 0`
    for all `x > 1` from `Δ(1) = 0`, and the paper for `x ≥ 2` from `Δ(2) > 0`.
12. `thm:simplex-balance`. The transfer statement is the same (`law_transfer`). For the first
    sentence Lean proves that every maximizer is balanced (`law_max_balanced`) and that the law is
    symmetric (`law_perm`). It does not state as one theorem that every balanced bin with the
    given support is a maximizer.
13. `eq:simplex-balance-integral`. `law_integral` assumes `σ > 0` and `r > 0` instead of
    `1/d < p < 1`. For `d ≥ 2` the two are equivalent (`sig_pos`, `rr_pos`). The product runs
    over all coordinates, with `B_0 = 1`.
14. `ex:simplex-edge-mode`. Lean proves that the edge centers are the only modes by listing all
    bins up to permutation (`classify4`), and uses the transfer only for `(3,1,0)`. The paper uses
    Theorem 3.8. The inequality `0 < T = 14/17 < log 4` is not in Lean.
15. `prop:field-tilt`(3). The statement (3) is the limit of `Λ_N(h)`, which is not in Lean. Lean
    has the exact identities of its proof. `cov_occ_closed` assumes `d ≥ 2` and `σ ≠ 1` where the
    paper has `p < 1`. For `d ≥ 2`, `σ = 1` exactly when `p = 1`, so Lean also covers `p > 1`.
    The bounds `2/(d^2 T)` and `5/T` on the variance are not in Lean.
16. `thm:weakfield-phases`. Only the comparison of two lines is in Lean, for arbitrary real
    slopes. `winning_size_monotone` says that a line of larger slope that is at least a line of
    smaller slope at `t_1` is strictly larger at every `t_2 > t_1`. The paper adds the two
    comparisons instead. The same comparison is used in Remark 4.8 (`rem:start-lines`), which
    is otherwise not in Lean. The paper now proves the modes with a start itself (Theorem 4.6,
    `thm:start-maxima`, and Corollary 4.7, `cor:start-modes`, with the proofs in Appendix B), and
    none of that is in Lean.
17. `cor:weakfield-full-hierarchy`. The paper's `t_k` and `ℓ_k` are `tau` and `lam` in Lean, and
    `c_k` is `cConst`. Lean has no `d`. `line_unique_max` compares line `k` with every line
    `j ≥ 1`, and it assumes `t < t_k` for every `k`. So for the top size `k = d` it covers only
    `t_{d-1} < t < c_d - c_{d+1} + H(4d-1)/6`, while the paper's last interval is `t > t_{d-1}`.
    For `t` above this value the comparison with the lines `j < d` follows from `lam_succ_sub`
    and `tau_mono` as in the Lean proof, but it is not a stated theorem. The proof of the
    corollary says that its arithmetic is checked in Lean, which holds with this exception. The
    second difference `cConst_second_diff` holds for every real `k > 0`, and Lean proves it from
    the concavity of `c(x) - x^2/4` where the paper integrates `c'' ≤ 1/2` twice.
18. `cor:weakfield-full-hierarchy` and `ex:weakfield-triangle`. Lean checks the arithmetic of the
    lines. The steps from the lines to the supports and to the global modes use Theorem 5.2 and
    are not in Lean. In `triangle_edge_phase` the numbers `a_2` and `a_3` are arbitrary reals,
    and only the three scores of the example are compared. That the other two edges (score
    `t - a_2 - H/2`) and the vertex `3` (score `-H`) lose is not in Lean.
19. `rem:frontier-superlevel` (removed from the paper on 2026-10-02). The removed remark said that
    the covolume `√k` is checked in Lean. Lean
    proves that the Gram matrix of the vectors `e_i - e_k`, `i < k`, has determinant `k`
    (`gram_det`). It does not prove that these vectors are a basis of the lattice, and it does
    not take the square root.
20. `lem:bessel-law`. Only (i) is in Lean, in the form without the division by `Φ(x)`, for
    `x ≥ 0`. `Φ` is defined by its series (`Phi`). The identity `Φ(x) = I_1(2√x)/√x` is not in
    Lean.
21. `eq:boundary-integral-form`. Lean states the integral form for the law, `law_integral`, and
    for `S_n` only when `n = (b, a_1, ..., a_ℓ)` with all coordinates positive (`S_integral`).
    The form for `S_n` with a general `n` follows by dividing `law_integral` by `V_N`
    (`law_eq_V_SL`), but it is not a stated theorem.
22. `lem:vertex-elasticity`. Lean defines `κ` as the sum of the elasticities `1 + E_1/Z` of the
    factors and proves `κ = y H'/H` for `y > 0` (`kapH_eq`). The upper bound
    `κ ≤ ℓ + √(ℓ|a|y)` and `κ ≥ ℓ` hold in Lean for every `y > 0`. `H_convexOn` is on `[0,∞)`.
    `H_root` assumes `ℓ ≥ 1`. For `B_a(y) ≤ y e^(ay/2)` Lean compares coefficients directly
    (`Bpoly_le_exp`) and does not pass through `y Φ(ay)`.
23. `lem:vertex-randomization` and `thm:vertex-uniform-root`, the number of states. Lean has no
    random variable `𝒳`. The identity `S_(b,a)(u) = (1-u)^|a| E[𝓗(v𝒳)]` and the moment generating
    function appear as integrals against `e^(-t) B_b(vt)` (`S_integral`, `L1_eq`, `Lt_eq`,
    `Ls_eq`). Jensen's inequality is replaced by the tangent line of the convex polynomial `H`
    (the paper's `𝓗`).
    `jensen_lower` does not need `s < 1`. All these statements are for the vector `kvec c m` on
    exactly `ℓ + 1` states. By note 5 the passage to `S_(b,a)` inside a chain with more states
    rests on the paper's remark that `S_n` does not depend on `d`, which is not in Lean.
24. `thm:vertex-uniform-root`. The Lean bracket is strict,
    `(1-δ)√(y_a/b) < u < (1+δ)√(y_a/b)`, and the paper states it with `≤`. The paper's proof
    also gives the strict form. Lean bounds every positive root `u`, and `SL_strictMonoOn` gives
    that there is only one. In Lean `y_a` is a hypothesis (any `y_a` in `[1/(|a|+1), 1]` with
    `H(y_a) = 1`), and `H_root` gives its existence and uniqueness. The paper's `c_ℓ` is `K` in
    the module `VertexRoot`. The form (15) (`eq:vertex-uniform-root`), the explicit relative
    bound `16 c_ℓ √((|a|+1)/b)`, is a consequence of the bracket and is not a Lean statement.
25. `lem:occupation-covariance` in `PaperC`. `tree_formula_two` and `tree_formula_three` start
    from the matrix `Σ = 2(D' - π'π'ᵀ) L_(1)^(-1) (D' - π'π'ᵀ)` of the proof, written out for
    `k = 2` and `k = 3`. They assume only that the `π_i` sum to `1`. The step from the quadratic
    form `2 ∑ π_i f_i χ_i` of the statement to this matrix is not in Lean.
26. `lem:weighted-cayley` in `PaperC`. `cayley_three` is the polynomial identity for the three
    spanning trees of `K_3`, with `x_i` arbitrary reals. The general `k` and the matrix-tree theorem
    are not in Lean.
27. `ex:K3-start` in `PaperC`. `k3_edge_window` uses Paper C's lines, which are the lines of the
    remark minus `2t`, with `a_2` and `a_3` written in closed form (equal to the paper's by
    `paperB_constant`). It compares the edge `{1,2}` with the vertices and the full face only.
    That the edges through `3` lose is not stated. `k3_window_width` proves that the width is
    `log(16/(9√3)) > 0`, and the decimals `-0.4673558`, `-0.4412978` and `0.0260580` are not in
    Lean. The step from the lines to the modes is now proved in Paper B itself, by Corollary 4.7
    (`cor:start-modes`), which rests on Theorem 4.6 (`thm:start-maxima`) and Lemma 4.2
    (`lem:first-run`). It no longer uses Paper C, and it is not in Lean.
28. `eq:intro-ak` in `PaperC`. `paperB_constant` holds for every real `k > 1`.
29. The module `Singleton`. Its theorems are from an earlier version of the paper. The docstrings
    of `Fsing` and `SL_singletons` say "the paper's" for a formula that the current paper does not
    state.

## Not in Lean

The asymptotic results are not in Lean, since they need the Laplace method, Bessel expansions or
limits as `N → ∞`. The library also has no general start, so the start-law results are not in it,
and the tree form of the constants is not in it. In terms of the paper these are the following.

* Section 2. Proposition 2.1 (`prop:dgf`) as an identity of power series, and Proposition 2.2
  (`prop:dpmf`) for a general start. The bounds `I_1(x) ≤ sinh x`, `Φ(x) ≤ e^(2√x)` and the
  expansion of `I_1`.
* Section 3. Theorem 3.1 (`thm:simplex-window`) (i) to (iii). The crossing equation and
  `eq:simplex-root-expansion` in Theorem 3.2, and `eq:simplex-uniform-ratio`. Theorem 3.3
  (`thm:simplex-interior`). Lemma 3.4 (`lem:occupation-covariance`), Lemma 3.5
  (`lem:weighted-cayley`) and Proposition 3.6 (`prop:kirchhoff`), which are the tree form of the
  constants. Proposition 3.7 (`prop:mass-balance`), including the exact identity (1).
  Corollary 3.9 (`cor:simplex-modes`).
* Section 4. All of it. This includes the start-law results that the paper now proves itself:
  Lemma 4.1 (`lem:start-weights`), Lemma 4.2 (`lem:first-run`, the first-run identity),
  Proposition 4.3 (`prop:start-weights`, where a conditioned path starts), Theorem 4.4
  (`thm:start-crossings`), Example 4.5 (`ex:start-balance`), Theorem 4.6 (`thm:start-maxima`, the
  face maxima with a start), Corollary 4.7 (`cor:start-modes`, the global modes with a start),
  Remark 4.8 (`rem:start-lines`), Example 4.9 (`ex:K3-start`, apart from the arithmetic checked
  in `PaperC`) and Remark 4.10 (`rem:K3-finite`).
* Section 5. Proposition 5.1 (`prop:field-tilt`) (1) and (2), and in (3) the variance bounds and
  the limit. Theorem 5.2 (`thm:weakfield-phases`) apart from the comparison of two lines. The
  steps from the lines to the modes in Example 5.3 and Corollary 5.4.
* Section 6. Theorem 6.2 (`thm:uniform-simplex-majorant`), Remark 6.3, and the form (15)
  (`eq:vertex-uniform-root`) of Theorem 6.4.
* Appendices. Lemma A.1 (`lem:bessel-law`) (ii) to (vi), Lemma A.3
  (`lem:gaussian-phi-average`), Lemma A.4 (`lem:no-rare`), Lemma B.1 (`lem:confinement`), Lemma
  B.2 (`lem:start-upper`), Theorem C.1 (`thm:simplex-boundary-crossover`), Remark C.2
  (`rem:crossover-numbers`) and Corollary C.3 (`cor:simplex-rare-invisibility`).

Some of these are checked in the library `PaperC`, as listed above. These are the tree formula
for two and three states, the weighted Cayley formula for three states, and the arithmetic of the
`K_3` window with a start.
