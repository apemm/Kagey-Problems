# Paper C: map from the paper to the Lean theorems

This file matches the statements of Paper C, "Face selection for slowly switching Markov chains
and the planar persistent walk" (`paperC/problem131_switching.tex`), to the Lean theorems of the
library `PaperC` (root `PaperC.lean`). The library uses Lean 4 v4.33.1 and Mathlib v4.33.1. Every
theorem listed here is proved without `sorry`, `admit` or new axioms, and `#print axioms` on the
main theorems reports only `propext`, `Classical.choice` and `Quot.sound`.

The numbers are those of the built PDF (`paperC/problem131_switching.pdf`), and the key in
parentheses is the `\label` in the source. The last column gives the label of the same statement in
the research notes `C1.md` to `C5.md`, which the docstrings of the Lean files still use. "In part"
means that the finite or exact core of the statement is in Lean and the rest is listed under "Not in
Lean" below. Lean numbers the states from 0, so state `i` of the paper is state `i - 1` in Lean.

## Modules

| Module | Content |
| --- | --- |
| `ChainLaw` | the chain, the exact composition law and the run expansion |
| `ChainApps` | the vertex law, the star zero set, the pair identity, face masses and the directed 3-cycle |
| `Rayleigh` | Rayleigh quotients, the principal Dirichlet eigenvalue `dirEig Q F`, Barta's bound and monotonicity in the face |
| `Spectra` | exact `λ_F` for complete graphs, cycle arcs and path end-arcs, and the complement bound |
| `DVRate` | the Donsker–Varadhan rate of a face and its minimum `λ_F` |
| `SingleJump` | Rayleigh minimizers are eigenvectors, and the single-jump criterion |
| `CycleCascade` | arc eigenvalues, switch values, the bounds on `D_k` and the cascade on `C_d` |
| `TwoTriangles` | the graph `Θ_ε` |
| `Winners` | the winners at first order and the finite hull theorem |
| `Paw` | the paw, with all 15 faces |
| `DisjointJumps` | the house and `K_4` plus a vertex, with all 31 faces each |
| `Constants` | the second-order constants in finite form |
| `Planar` | the planar walk, its face exponents, the exact identity and the unique crossing |
| `Sticky` | the thresholds and the direct jump for sticky priors |
| `Fisher` | the Fisher efficiency identity and its instances |

## Section 2, the model and the exact law

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Section 2, the chain with transition matrix `I + hQ` and the law `P_N(n)`, which sums to 1 | `stepP`, `chainWt`, `wordWt`, `lawP`, `sum_wordWt` | C1 Section 1 |
| Lemma 2.3 (`lem:runs`), the run expansion | `lawP_run_expansion`, with `wordWt_eq_runWt`, `chainWt_eq`, `card_runSet`, `runs_noAdjEq`, `sum_runComp` | C1 Prop 1, C5 Lemma 1(a) |
| Equation (1) (`eq:vertexmax`), the exact part `M_{i} = μ_i (1 - h q_i)^{N-1}` | `lawP_vertex` | C2 Prop C2.8 |

## Section 3, first-order face selection

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Proposition 3.1(a) (`prop:rate`), the lower bound `I_F ≥ λ_F` and the value `λ_F` at `α*_F`, without reversibility | `dvRate_ge`, `dvRate_isLeast`, `dvPhi_le_at_qe`, `dvPhi_at_qe_r`, `dvRate_at_qe` | C1 Prop 8(a),(b), C4 Lemma DV(a),(b) |
| Proposition 3.1(c), the reversible form at interior points, with minimizer the squared Perron vector | `dvRate_symm`, `dvRate_symm_min` | C1 Prop 8(c) |
| Theorem 3.4(a) (`thm:hull`), in finite form | `size_unique_min_iff`, `size_tie`, `face_winner_iff` | C2 Theorem C2.3 |
| Theorem 3.4(b) | `winner_monotone`, `winner_strict` | C2 Theorem C2.2(ii) |
| Theorem 3.4(c), the comparison step (a face with a subface of the same exit rate never wins) | `not_winner_of_sub` | C2 Theorem C2.2(i) |
| Theorem 3.4, the last winner (a face with `λ = 0` and `d` states beats `F` for `τ > (d - \|F\|)/λ_F`) | `full_beats` | C2 Theorem C2.2(iii) |
| Text after Theorem 3.4, the Rayleigh–Ritz form of `λ_F` for symmetric `Q` and its monotonicity in the face (the strict part is by hand) | `dirEig`, `bottomEig`, `bottomEig_le`, `barta`, `isLeast_rayleigh_of_pos_eigvec`, `dirEig_anti` | C2 Lemma C2.1 |

## Section 4, the second-order theory

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Proposition 4.2(a) (`prop:constant`), `det Σ · det ∇²I = 1`, only for the directed 3-cycle | `dicyc_H_mul_Sigma`, `dicyc_det_H` | C5 Prop 4(a) |
| Proposition 4.2(b), the tree formula for `det Σ`, for `k = 2, 3` | `tree_formula_two`, `tree_formula_three` | C5 Prop 4(b) |
| Proposition 4.2(b) on a complete face of 3 states, the weighted Cayley–Prüfer sum `tree(√(α_i α_j)) = √(α_1 α_2 α_3)(√α_1 + √α_2 + √α_3)` | `cayley_three` | C5 Prop 4(b) |
| Proposition 4.9 (`prop:pair`), the exact pair identity | `lawP_pair_ratio`, `lawP_locality`, `wordWt_common_rate` | C5 Prop 12, C2 Prop C2.8, C4 Prop S4 |
| Corollary 4.10 (`cor:paperA`), `K_{1,2} = √(2/π)` and `b_FG = c_0` | `paperA_constant` | C5 Cor 10 |
| Corollary 4.11 (`cor:paperB`), `λ_F = d - k`, the tie at `τ = 1` and `b_FG = a_k` | `completeQ_isLeast`, `completeQ_dirEig`, `complete_costs`, `complete_tie`, `paperB_constant` | C5 Cor 11, C2 Theorem C2.4, C1 Checks |
| Proposition 4.13(i) (`prop:threecycle`), the exact `M_{1}` and `M_{1,2}`, with `M_{1,2}` attained only at `(1, N-1, 0)` | `dicyc_vertex`, `dicyc_face`, `dicyc_face_max`, `dicyc_face_max_strict` | C5 Prop 19(i) |
| Proposition 4.13(i), `α*`, `det ∇²I` and `K_{1,2,3}` for the full face | `dicyc_stationary`, `dicyc_inverse`, `dicyc_Sigma`, `dicyc_det_Sigma`, `dcH_eq_notes`, `dicyc_det_H`, `dicyc_K`, `dicyc_K_four` | C5 Prop 19(i) |
| Proposition 4.13(ii), exactly one root (the ratio `M_{1,2}/M_{1}` increases strictly in `h`) | `dicyc_ratio_strictMono`, `dicyc_crossing_unique` | C5 Prop 19(ii) |

## Section 5, the 4-cycle and other graphs

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Corollary 5.1(a) (`cor:C4`), the exit rates `2`, `1`, `2 - √2`, `0` and the winners (the arcs of 3 states never win) | `cycle_arc_isLeast`, `cycle_arc_dirEig`, `cycle_full_dirEig`, `lamArc_one`, `lamArc_two`, `lamArc_three`, `cycle_cascade` (with `d = 4`), `tau_full_table` | C2 Lemma C2.6a, Theorem C2.6(b),(c) |
| Corollary 5.1(b), `K_pair` and `K_arc3` from the closed form for all arcs | `Karc_pair`, `Karc_three` | C5 Cor 13 |
| Corollary 5.1(c), the exact identity `M_pair = M_vertex S_N(u)` | `lawP_pair_ratio` | C5 Prop 12 |
| Corollary 5.2 (`cor:K3start`), the comparison of the lines in (a) and the width `w = log(16/(9√3)) > 0` | `three_lines`, `k3_edge_window`, `k3_window_width`, `k3_edge_criterion`, `k3_half_half_criterion` | C5 Prop 14 |
| Table 1 (`tab:outcomes`), row `K_d` | `completeQ_isLeast`, `completeQ_dirEig`, `completeQ_killed_perp`, `completeQ_row_sum`, `complete_costs`, `complete_vertex_wins`, `complete_full_wins`, `complete_tie` | C2 Theorem C2.4 |
| Table 1, row symmetric `Q` | `complement_bound`, `complement_isLeast`, `complement_eq_iff`, `eigvec_of_rayleigh_min`, `single_jump_equal_feeding`, `unit_equal_feeding_complete` | C2 Prop C2.5 |
| Table 1, row `C_d` (the growth like `k³/(2π²)` is by hand) | `cycle_arc_isLeast`, `cycle_arc_dirEig`, `pathM_isLeast`, `pathM_eig`, `cycle_full_dirEig`, `lamArc_strictAnti`, `lamArc_convex`, `tauArc_lt_succ`, `tauArc_lt`, `DArc_two`, `DArc_gt`, `DArc_lt`, `cycle_cascade`, `arcCost_unique_min`, `d_sub_two_thirds`, `lamArc_one` to `lamArc_five`, `tauArc_two` to `tauArc_five`, `tau_full_table` | C2 Lemmas C2.6a, C2.6b, Theorem C2.6 |
| Table 1, row `P_d`, in part (the end-arc exit rates and the golden ratio) | `path_endArc_isLeast`, `path_endArc_dirEig`, `endArcM_isLeast`, `endArc_eq_lamArc`, `path_first_threshold` | C2 Cor C2.6′ |
| Table 1, row `Θ_ε`, in part | `theta_triangle_isLeast`, `lamTri_root`, `lamTri_pos`, `lamTri_lt_one`, `lamTri_lt_three_quarters_iff`, `theta_edge_isLeast`, `theta_vertex_isLeast`, `tauA_formula`, `tauStar_formula`, `theta_eps_one`, `theta_comparisons`, `eps1_root`, `theta_four_le`, `theta_four_lt_half`, `theta_four_mono` | C2 Prop C2.7 |
| Table 1, row paw | `face_dirEig_eq`, `face_dirEig_ge`, `paw_w1` to `paw_w4`, `paw_bounds`, `paw_phase1` to `paw_phase4`, `paw_not_nested` | C2 Prop C2.10 |
| Table 1, rows house and `K_4` plus a vertex | `house_bounds`, `house_w_vertex`, `house_w23`, `house_w014`, `house_wV`, `house_phase1` to `house_phase4`, `house_disjoint`, `kfv_bounds`, `kfv_w4`, `kfv_wK`, `kfv_wV`, `kfv_phase1` to `kfv_phase3`, `kfv_disjoint` | C2 Prop C2.9(b) |

## Section 6, the planar persistent walk

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Section 6, the walk and `c_N = p_0^{N-1}/4` | `planarA`, `planarQ`, `planarQ_eq`, `originMass`, `cornerMass`, `cornerMass_eq` | C3 Section 1.2 |
| Section 6, the face exponents before Lemma 6.1 and the faces that can reach the origin | `planarI_EW`, `planarI_fiber`, `planarI_uniform`, `origin_faces` | C3 Cor 1.1 |
| Theorem 6.3 (`thm:planar-first`), the first-order comparison of the exponents, `τ* = min(2/β, 1/s)` and the switch at `s = 2r` | `planar_first_order`, `planar_first_order_turns`, `planar_switch_rev`, `planar_switch_turn` | C3 Theorem 7 |
| Proposition 6.2 (`prop:decomp`), `o_N/c_N = 2 S_N(u) + R_N` with `R_N ≥ 0`, and an origin path with a turn uses all 4 directions | `planar_origin_identity`, `mixed_nonneg`, `mixed_uses_all_four`, `SPoly_eq_pair_ratio` | C3 Prop 4, C5 Cor 15 |
| Proposition 6.2, the unique crossing for `s > 0` | `planar_ratio_eq`, `originPoly_zero`, `originPoly_strictMono`, `originPoly_unique_root`, `planar_unique_crossing` | C3 Section 1.2 |

## Section 7, sticky priors

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Section 7, Theorem 3.4(b) for the sticky chain with `λ_F = 1 - ρ_F` | `winner_monotone`, `winner_strict` | C4 Prop S2(a) |
| Proposition 7.2(a) (`prop:thresholds`) | `vertex_wins_iff`, `full_wins_iff` | C4 Prop S2(b) |
| Proposition 7.2(b) | `cMinus_bounds` | C4 Prop S2(c) |
| Proposition 7.2(c), and the tie of the uniform kernel at `τ = d - 1` | `direct_jump_iff`, `uniform_tie` | C4 Prop S2(d) |
| Corollary 7.3 (`cor:uniform-kernel`), `ρ_{i,j} = √(π_ij π_ji)` | `pair_perron` | C4 |
| Corollary 7.3(a) | `symmetric_direct_uniform` | C4 Prop S3(a) |
| Corollary 7.3(b) | `d3_pair_condition`, `cyclic_pair_condition` | C4 Prop S3(b) |
| Proposition 7.4(a) (`prop:directjump`), exactly 2 of the 8 corner kernels have a direct jump | `corner_direct_card` | C4 Prop S3(c) |
| Appendix D (`app:hdp`), the logit identities in the proof of Proposition 7.4(b) | `logit_two_B`, `logit_two_one_sub_B`, `logit_pair_iff` | C4 Prop S3(d) |
| Corollary 7.5 (`cor:sticky-pair`), the exact identity through Proposition 4.9 | `lawP_pair_ratio` | C4 Prop S4 |
| Proposition 7.6 (`prop:mass`), the bounds at finite `N` | `faceMass_eq`, `iterF_sandwich`, `faceMass_sandwich` | C4 Prop S5 |

## Section 8, the information in the endpoint

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Proposition 8.1 (`prop:eta`), `e_N = Var(E[J \| K])/Var J` | `efficiency_eq`, `hasDerivAt_pathP`, `fisherK_eq`, `fisherPath_eq`, `mean_J`, `paperA_pathP`, `paperA_total`, `paperA_efficiency` | C4 Prop F1 |
| The case `N = 2` of Proposition 8.1, `e_2 = 1` | `paperA_efficiency_two` | C4 Prop F2 |

## Section 9, open questions

| Paper statement | Lean | Note label |
| --- | --- | --- |
| The zero set on a star (`P_N(n) = 0` when `supp n = [d]` and `n_d < ℓ - 1`) | `star_law_zero`, `star_runs_bound`, `star_length_bound`, `noAdjLeaves_of_switchProd` | C1 Example 7 |

## Lean theorems that the paper does not state

| Content | Lean | Note label |
| --- | --- | --- |
| The switch product in terms of transition counts, and the balance of in- and out-counts | `switchProd_eq_prod_pow`, `sum_switchCount_out`, `sum_switchCount_in`, `switch_balance`, `switchProd_eq_pow` | C1 Prop 2, in part |
| The Fisher efficiency of the occupancy vector of the sticky chain is a correlation ratio | `sticky_pathP`, `sticky_total`, `sticky_efficiency` | C4 Prop G1 |

## Not in Lean

The asymptotic results are not in Lean, since they need the Laplace method, local limit theorems
or expansions as `N → ∞`. In terms of the paper these are the following.

* Section 2. Lemma 2.2 (`lem:admissible`), Lemma 2.4 (`lem:continuum`) and the asymptotic form in
  equation (1).
* Section 3. Proposition 3.1(b) and (d), the uniqueness of the minimizer in (a), and (c) on the
  boundary of the face. Lemma 3.2 (`lem:upper`) and Theorem 3.3 (`thm:first`). The strict
  monotonicity of `λ_F` in the face.
* Section 4. Proposition 4.2(a) in general, Corollary 4.3 (`cor:symface`) for general `k`,
  Theorem 4.4 (`thm:local`), Lemma 4.5 (`lem:discrete`), Theorems 4.6 to 4.8 (`thm:facemax`,
  `thm:crossing`, `thm:window`), the asymptotic parts of Corollaries 4.10 and 4.11, Remark 4.12,
  the expansion in Proposition 4.13(ii), Proposition 4.13(iii) and (iv), and Remark 4.14.
* Section 5. Corollary 5.1(c) to (e) apart from the exact identity in (c), the part of
  Corollary 5.2 that rests on Theorem 4.8, the resultant certificates for `Θ_ε`, the rest of the
  rows `P_d` and `Θ_ε`, the numerics for `P_4` at finite `N`, and the step in Remark 5.3 that a
  proper face of `C_d` that is not an arc is disconnected (by hand in the paper, so
  `cycle_cascade` is stated for the arcs and the whole cycle).
* Section 6. Lemma 6.1, the bound on `o^(4)_N` in Proposition 6.2 and its uniqueness claim for
  `s = 0`, Theorems 6.3 and 6.4 beyond the algebra above, Remark 6.5 and Appendix C.
* Section 7. Corollary 7.1, Proposition 7.4(b) apart from the logit identities, and the asymptotic
  parts of Corollary 7.5, Proposition 7.6 and Remark 7.7.
* Section 8. Remark 8.2, Theorem 8.3, Corollary 8.4 and Appendix E.
* Appendices A and B.

## Findings while formalizing

* No mathematical error was found in the statements above.
* The research notes called the per-size minima for the house and for `K_4` plus a vertex a finite
  computation to 40 digits rather than a hand proof. `DisjointJumps` replaces it by a proof, with
  exact eigenvectors for the winning faces and rational Barta certificates for all other faces.
  The paw is proved the same way in `Paw`. So these rows of Table 1 are proved in Lean.
* Proposition 4.13 assumes `b > 2`. The monotonicity of `M_{1,2}/M_{1}` in `h`, and hence the
  uniqueness of the first crossing in 4.13(ii), holds for every `b > 1` (`dicyc_ratio_strictMono`).
