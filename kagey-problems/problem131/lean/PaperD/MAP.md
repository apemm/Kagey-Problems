# Paper D: map from the research notes to the Lean proofs

Paper D is `paperD/problem131_memory.tex`. The tables cite the statement labels of the 4
research notes D1 to D4, and the column Paper gives the number in the paper (for example D1 S9 is
Proposition 2.3, D2 Theorem 1 is Theorem 3.5, D3 Prop 1 is Proposition 4.1, and D4 Prop 9 is in
Remark 4.8). "Not in the paper" marks results of the notes that the paper does not state. The Lean
library is `PaperD` (root `PaperD.lean`, 16 modules in `PaperD/`, namespace `Kagey131.PaperD`),
built against Lean 4 v4.33.1 and Mathlib v4.33.1.

Every theorem below is proved without `sorry`, `admit` or new axioms. `#print axioms` on each of
the 136 theorems named in the tables reports only `propext`, `Classical.choice` and
`Quot.sound`. A clean build of the 17 `PaperD` modules takes about 2.5 minutes (Mathlib cached).

## Models

| Object | Lean | Where |
|---|---|---|
| Sign word of length `N` (`true` = `+1`) | `Word`, `numR`, `numL`, `flip` | `Words.lean` |
| Elephant walk, symmetric start: `X_{t+1}` copies a uniform earlier step, flipped with prob. `ε` | `stepProb`, `ewProb` (word law), `ewBin ε n k = P(A_n = k)` | `Elephant.lean` |
| Its count chain given `X₁ = +1`: `b_t` = number of `-1` steps, up-prob. `r_t(b) = ε + (1-2ε)b/t` | `upProb`, `law ε n b = P₊(b_n = b)` | `Elephant.lean` |
| Subtree of vertex `v` in the random recursive tree (Pólya step: vertex `k+1` joins `T_v` w.p. `|T_v|/k`) | `stLaw v m d` (tree size `v+m`) | `RecursiveTree.lean` |
| Run-length walk | only its exact quantities (`runExp`, `gammaK`, `lampertiDensity`, tail sums) | `HeavyRuns.lean` |
| Aging walk, arbitrary switching sequence `p k` at step `k ≥ 2` | `agWeight` (word weight), `agEnd`/`agEndStart` (joint law of `(S_n, X_n)`), `agBin` (fair start), `plusBin` (start `+1`) | `Aging.lean` |
| Switching rules `c/k`, `c/(k+b)`, `c/(k-1+2c)` | `agingP c`, `shiftP b c`, `dlsP c` | `AgingExact.lean`, `BetaBinomial.lean` |

For the aging walk `t` is the number of steps minus one, so `agBin p t s = P(S_{t+1} = s)`. For
the elephant walk, `law ε n` and `ewBin ε n` use the number of steps `n` directly.

## D1: elephant walk, center versus endpoint

| Note statement | Paper | Lean theorem(s) | File |
|---|---|---|---|
| S1 (reduction to the fixed start) | Lemma 2.2 | `sum_plus_ewProb`, `sum_minus_ewProb`, `ewBin_eq`, `ewBin_center` | `Elephant.lean` |
| S1, endpoint `E_n = ½(1-ε)^(n-1)` (all steps `+1`) | Lemma 2.2 | `ewBin_top`, `ewProb_const_true`, `law_zero` | `Elephant.lean` |
| (word law is a probability law) | Definition 2.1 | `sum_ewProb`, `ewProb_flip` | `Elephant.lean` |
| S2 (innovation form of `r_t`) | Section 1 (prior work) | `upProb_innovation` | `ElephantAlgebra.lean` |
| S3(b): `C_n` polynomial, `C_n(0) = 0`, `c₁ = C_n'(0) = 4/(n+2)` | Proposition 2.5(b) | `law_polynomial`, `law_at_zero`, `center_at_zero`, `center_hasDerivAt` (via `hasDerivAt_law`, `profile_hasDerivAt`) | `ElephantFirstOrder.lean` |
| S5(c) (pseudo-count Pólya form) | Lemma A.1(c) | `upProb_pseudocount` | `ElephantAlgebra.lean` |
| S6(a) (numerator identity), S6(b) (choice of `κ`) | Proposition A.4(a), (b) | `supersolution_numerator`, `upProb_half_minus`, `kappa_identity`, `kappa_eq` | `ElephantAlgebra.lean` |
| S9 (monotone likelihood ratio, every bin vs endpoint) | Proposition 2.3 | `lawRatio_mono`, `law_ratio_strictMonoOn`, `ewBin_ratio_strictMonoOn` | `ElephantCrossing.lean` |
| S9 (`C_n ≥ 2E_n` for `ε ≥ ½`; crossing exists, is unique, `ε_n < ½`; same for every bin) | Proposition 2.3 | `law_ge_of_half`, `ewBin_ge_two_top`, `crossing_exists_unique`, `center_crossing_exists_unique` | `ElephantCrossing.lean` |
| S11 (constants `2c₀ + log 2 = log(π/4)`, `log(π/4) - log 2π = -log 8`) | proof of Theorem 2.8 | `s11_log_constants` | `ElephantAlgebra.lean` |
| S15(a) (finite-`n` unimodality with the first step fixed) | Lemma 3.4 | `law_unimodal_delta`, `law_isUnimodal` | `ElephantUnimodal.lean` |
| S15(b) (`P(A_n=n-1) ≥ x/(2(1-ε)) P(A_n=n)`; not unimodal when `C_n ≤ E_n`) | Theorem 3.5, Corollary 3.6 | `law_one_ge`, `endpoint_dip`, `not_unimodal_of_dip`, `not_unimodal_at_crossing` | `ElephantCrossing.lean` |

## D2: the profile and the random recursive tree

| Note statement | Paper | Lean theorem(s) | File |
|---|---|---|---|
| Lemma 2.1 (`P(A_n=a) = ½h(n-a) + ½h(a)`, `h(0) = (1-ε)^(n-1)`, `h(n) = 0`) | Lemma 2.2 | `ewBin_eq`, `law_zero`, `law_eq_zero` | `Elephant.lean` |
| Lemma 2.3(5): `∑_v β_v(d) = n/(d(d+1))` | Lemma 2.4 | `subtreeCount_eq` (recursion `subtreeCount_succ`) | `RecursiveTree.lean` |
| Lemma 2.3(6): `∑_v (v-2) β_v(d) = 2n(n-d-1)/(d(d+1)(d+2))` | Lemma 2.4 | `subtreeCountW_eq` | `RecursiveTree.lean` |
| §11 item 2 (first-order term of `h(m)` is exactly `x/(m(m+1))`) | Section 3.1 | `profile_hasDerivAt`, `subtreeCount_eq_coef1` | `ElephantFirstOrder.lean`, `RecursiveTree.lean` |
| Lemma 2.7 (unimodality given the first step) | Lemma 3.4 | `law_unimodal_delta`, `law_isUnimodal` (`delta_succ_succ`, `delta_succ_zero`, `delta_zero_neg`) | `ElephantUnimodal.lean` |
| Lemma 3.3 (first-marked subtree: two-sided bound, tail bound) | Lemma B.4 (for the urn model) | `firstMark_bounds`, `firstMark_tail` | `RecursiveTree.lean` |
| Theorem 1, lower bound (`R₁ > x/(2(1-ε))`) | Theorem 3.5 | `endpoint_dip`, `endpoint_below_neighbour` | `ElephantCrossing.lean` |
| Theorem 1, upper bound (`R₁ ≤ x(1+1/n)²/(2-3ε) + ε/(1-ε)`) | Theorem 3.5 | `endpoint_ratio_upper`, `endpoint_above_neighbour` (via `law_one_eq`, `dipS_le`, `law_top_le`) | `ElephantEndpoint.lean` |

## D3: heavy-tailed runs

| Note statement | Paper | Lean theorem(s) | File |
|---|---|---|---|
| Cor 7: `e(α) = 1-α+1/α = -(α-φ)(α-ψ)/α`; `e = 0 ⟺ α = φ`; `e > 0 ⟺ α < φ` | Corollary 4.5 | `runExp_eq`, `runExp_eq_zero_iff`, `runExp_pos_iff`, `runExp_golden` | `HeavyRuns.lean` |
| Cor 7: golden identities `1+1/φ = φ`, `φ-1 = 1/φ`, `2-φ = φ⁻²`; fresh start `e-1 < 0` | Corollary 4.5 | `golden_identities`, `fresh_exponent_neg` | `HeavyRuns.lean` |
| Rem 13 `e(5/3) = -1/15`; Thm 8 `e(2) = -1/2 = 3/2-2` | Remark 4.7, Table 3 | `runExp_five_thirds`, `runExp_two` | `HeavyRuns.lean` |
| Rem 12: `e'(φ) = -√5/φ`, `e''(φ) = 2/φ³` | Remark 4.7 | `hasDerivAt_runExp`, `hasDerivAt_runExp_golden`, `hasDerivAt_runExp_deriv_golden` | `HeavyRuns.lean` |
| Lemma 3(i): `K_α = Γ(2-α)/(α-1) = -Γ(1-α) > 0` | Lemma 4.3 | `gammaK_eq`, `gammaK_pos` | `HeavyRuns.lean` |
| Thm 9: `f_L(1/2) = (2/π) tan(πα/2)`; constant `π/(4 tan(πα/2))` of `R_N` | Remark 4.6, Table 3 | `lamperti_half`, `lamperti_ratio_constant` | `HeavyRuns.lean` |
| Prop 1, fresh start: `E_N = ½ N^(-α)` (telescoping survival) | Proposition 4.1 | `fresh_edge` | `HeavyRuns.lean` |
| Prop 1, stationary start: `N^(1-α)/(α-1) ≤ ζ(α,N) ≤ N^(1-α)/(α-1) + N^(-α)` | Proposition 4.1 | `zeta_tail_bounds` (`rpow_step_upper`, `rpow_step_lower`) | `HeavyRuns.lean` |
| §1 stationarity check `π(k) = π(k+1) + π(1)p_k` | Section 4 | `residual_stationary` | `HeavyRuns.lean` |

## D4: the aging walk

| Note statement | Paper | Lean theorem(s) | File |
|---|---|---|---|
| Prop 1, path weights `P(x) = ½ρ(1,n)∏_{t∈T(x)} w_t`, `w_t = p_t/(1-p_t)` (`= c/(t-c)`) | Remark 4.8 | `agWeight_eq_rho_mul`, `agBin_ratio`, `agBin_top` | `Aging.lean`, `AgingCrossing.lean` |
| Prop 1, `R_{n,s}` strictly increasing on `(0,2)` for every interior bin | Remark 4.8 | `agBin_ratio_strictMonoOn` | `AgingCrossing.lean` |
| Prop 1, unique `c_n(s) ∈ (0,2)`, and `c_n(s) < 1`; sides of the crossing | Remark 4.8 | `aging_crossing_exists_unique`, `aging_crossing_sides` | `AgingCrossing.lean` |
| Prop 1, `c₂ = 2/3` | not in the paper | `two_steps_crossing` | `AgingSmall.lean` |
| Prop 1, `R_{4,2} - 1 = 3p(c)/((2-c)(3-c)(4-c))`, `p = c³-5c²+14c-8`; `c₄` its unique real root, `0.7367009 < c₄ < 0.7367010` | not in the paper | `four_steps_values`, `four_steps_ratio`, `four_steps_crossing`, `cubic4_strictMono`, `c4_bounds` | `AgingSmall.lean` |
| Prop 2 (averaging identity, arbitrary switching probabilities) | not in the paper | `agEnd_false_eq_sum`, `agTail_cum`, `agTail_compl`, `agBin_averaging` | `AgingAveraging.lean` |
| Prop 2(a) and Prop 3, fair start, `c = 1`: interior `1/n`, ends `1/(2n)` | Remark 4.8 | `agBin_one_interior`, `agBin_one_top`, `agBin_one_bottom` | `AgingExact.lean` |
| Prop 2(b): `c/n ≤ P(S_n=s) ≤ q_{j+1,n}` for `c ≤ 1` | not in the paper | `agBin_ge`, `agBin_le` | `AgingAveraging.lean` |
| Prop 2(c): `P(S_n = n/2) = 2E[q; T ≤ n-1]`, `P(T ≤ n-1) = ½` | not in the paper | `agBin_center_averaging` | `AgingAveraging.lean` |
| Prop 3, fixed start, `c = 1`: joint law, `S_n` uniform on `{1..n}` | Remark 4.8 | `plusEnd_one`, `plusBin_one` | `AgingExact.lean` |
| Thm 7 (finite part): end below every interior bin for `c ∈ (c^{(n)}, 2)`; lower bracket `c_n ≥ c^{(n/2+1)}`; `c^{(N)}` increasing | not in the paper | `end_below_all_bins`, `end_below_all_bins_of_gt_one`, `end_above_center`, `hN_mono`, `hN_mono'` | `AgingAveraging.lean` |
| Prop 9 (fixed start: ratio increasing, `= 1` at `c = 1`; `+` end strict max for `c<1`, strict min on `{1..n}` for `c>1`; crossing exactly `1`) | Remark 4.8 | `plusBin_ratio_strictMonoOn`, `plusBin_ratio_one`, `plus_top_strict_max`, `plus_top_strict_min`, `plusBin_zero_bin`, `plus_crossing_eq_one` | `AgingCrossing.lean` |
| Prop 10, identity `P(n-1)/P(n) = c(1+c)/(2-c) + c(1-c)/(n-c)`, `> 1` for `√3-1 < c ≤ 1` | not in the paper | `neighbour_ratio`, `neighbour_ratio_gt_one` | `AgingSmall.lean` |
| Prop 10, `√3-1 < c_n < 1` and end below neighbor at the crossing, every even `n ≥ 4` | not in the paper | `cubic4_sqrt3`, `c4_gt_sqrt3_sub_one`, `h4_sqrt3`, `crossing_bounds`, `end_below_neighbour_at_crossing`, `four_steps_end_below_neighbour` | `AgingSmall.lean`, `AgingAveraging.lean` |
| Cor 12 (exact part): `E N_n = c(H_n - 1)` | Figure 1 (the aging curve) | `expected_switches`, `expected_switches_aging` | `AgingSwitches.lean` |
| Prop 14(a): ratios strictly increasing on `(0, 2+b)` for `c/(k+b)` | not in the paper | `agBin_ratio_strictMonoOn_shift`, `shiftP_odds` | `AgingCrossing.lean` |
| Prop 14(b): at `c = 1`, interior `1/(n+b)`, ends `(1+b)/(2(n+b))` | not in the paper | `agEnd_shift_one`, `agBin_shift_one_interior`, `agBin_shift_one_top`, `agBin_shift_one_bottom`, `shift_ratio_one` | `AgingExact.lean`, `AgingCrossing.lean` |
| Prop 14(c): `b = 1` all-bin crossing exactly `1`; `b<1` crossings `<1`; `b>1` crossings `>1` | not in the paper | `shift_one_crossing`, `shift_crossing_lt_one`, `shift_crossing_gt_one` | `AgingCrossing.lean` |
| Prop 16: joint beta-binomial law for `c/(k-1+2c)` | not in the paper | `agEnd_dls`, `agBin_dls`, `betaBin_up`, `betaBin_stay` | `BetaBinomial.lean` |
| Prop 16(i): the `c/k` walk at `c = ½` has the discrete arcsine law | not in the paper | `dlsP_half`, `poch_half`, `aging_half_arcsine` | `BetaBinomial.lean` |
| Prop 16(ii): uniform law at `c = 1` | not in the paper | `agBin_dls_one` | `BetaBinomial.lean` |
| Prop 16(iii): ratio increasing in `c`, crossing exactly `1` | not in the paper | `dls_ratio_strictMonoOn`, `dls_crossing` | `BetaBinomial.lean` |

## Not formalized, and why

The asymptotic statements are out of scope. They need the Laplace method, stable and Gaussian
local limit theorems, Bessel or Landau limits, and `o(1)` and `O(·)` error terms. They are the
following.

* D1 S8 (uniform asymptotic), S10 (the crossing `x_n`, Theorem 2.7 and Remark 2.9), S11 (the
  comparison with the crossing of Paper A, Theorem 2.8, where only the constants are checked),
  S13 (limit `K₂`, which needs series over `t` and `u`), S14, S16 (heuristic), S3(c) (limit
  weights `t 2^{-t-1}`).
* D2 Theorem 2 (compound Poisson bulk, Remark 3.7), Theorem 3 and Corollaries 6.2, 6.3
  (explicit but very long error terms, and the profile statements are asymptotic), Theorem 4
  (Landau limit, Remark 3.7), Theorem 5, Conjecture 5.1 (Conjecture 3.10), Heuristics H1, H1',
  H2, H3.
* D3 Lemmas 3 to 5, Theorem 6 (Theorem 4.4), the asymptotic halves of Corollary 7 and
  Theorems 8, 9 (including the local min/max test at `α_c`), Heuristics 10, 11, Remarks 12, 13
  (numerics, Remark 4.7).
* D4 Theorem 4, Lemma 5, Theorems 6 and 8 (Beta limit, Kolmogorov rate, local limit, crossing
  expansion), the asymptotic half of Theorem 7 and of Corollary 12, Proposition 14(d),
  Statements 11 and 13 (heuristic or numerical).

Some exact or finite statements are not formalized either.

* D1 S3(a) (first-mutation decomposition, Proposition 2.5(a)), S4 (Duhamel identity),
  S5(a),(b),(d) (Pólya(`c`) hitting functions, bridge), S6 (supersolution bound,
  Proposition A.4), S7 (bridge product formula), S12. These need the Pólya hitting function
  `Φ^c` (Beta functions of real arguments), a comparison lemma for backward recursions, and
  digamma bounds, which would be a separate project. The exact first
  coefficient `c₁ = 4/(n+2)` of S3(b) is proved here by a different route (a first-order
  recursion with invariant `n/(k(k+1))`), which does not need S3(a) or S5. The purely algebraic
  identities of S2, S5(c), S6(a),(b) are proved (`ElephantAlgebra.lean`).
* D1 S3(c), the moment identity `∑ w_t t = 3 - 6/(h+2)` of Proposition 2.5(c), was not
  attempted.
* D2 Lemmas 2.2, 2.4, 2.5 (tree and marks, splitting, first flip, Lemmas 3.1 to 3.3) and
  Lemma 2.3(1)–(4) (the closed form `β_v(d) = C(n-d-1,v-2)/C(n-1,v-1)`, subtree tails, mean)
  are not formalized, since there is no formal random recursive tree here. The subtree chain
  `stLaw` is the Pólya-urn description that the note's proof of Lemma 2.3(1) starts from. Its
  identification with the subtree of a uniform random recursive tree is taken from the note.
  Lemma 2.3(5),(6) and Lemma 3.3 are proved for this chain.
* D2 Lemmas 3.1, 3.2 and Remark 3.4 (tail bounds) were not attempted.
* D3 Proposition 2 (the two-renewal representation, Proposition 4.2) is a known identity
  (Godrèche and Luck 2001, Section 7). A formal proof would need a composition model of the run
  walk, and it was not attempted.
* The records interpretation of D4 Proposition 3 (Rényi) was not attempted.

## Gaps and remarks found while formalizing

No statement that was formalized turned out to be false. We record 4 points.

* D1 S15(b) and the lower half of D2 Theorem 1. The inequality
  `P(A_n = n-1) ≥ x/(2(1-ε)) P(A_n = n)` holds, strictly, for every `n ≥ 2` and every
  `0 < ε < 1` (`endpoint_dip`). The hypothesis `x > 2(1-ε)` in S15(b), and `n ≥ 3`, `ε ≤ 1/2`
  in D2 Theorem 1, are needed only for the conclusion that the endpoint is below its neighbor
  (`x ≥ 2(1-ε)` suffices) and for the upper half of Theorem 1, respectively.
* D2 Lemma 2.7 holds for every `0 ≤ ε < 1` (`law_isUnimodal`), not only in the note's standing
  range `ε ≤ 1/4`.
* D4 Proposition 2(b) as stated uses `q_{j+1,n}`, whose switch is at step `j+1`. In the Lean
  indexing this is `qStay (agingP c) (j-1) t`, whose switch leaves level `j-1`, that is, at step
  `j+1`. The two agree.
* D4 Proposition 10's conclusion for `n ≥ 6` depends on Theorem 7's lower bracket, which in turn
  depends on Proposition 2(b). Both are formalized, so Proposition 10 is proved for every even
  `n ≥ 4` without numerics.
