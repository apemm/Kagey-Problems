# Papers C1 and C2: map from the papers to the Lean theorems

This file matches the statements of the two papers that came out of Paper C to the Lean theorems
of the libraries `PaperC` (root `PaperC.lean`) and `PaperB` (root `PaperB.lean`).

- Paper C1, "Occupation counts of rarely switching Markov chains: stratified local laws, support
  selection and the boundary layer", main files `paperC/problem131_chains.tex` (article build, 59
  pages) and `paperC/problem131_chains_sn.tex` (Springer build, 65 pages). Statement numbers agree in the two
  builds. Equation numbers agree too, except in the appendices, where the Springer build numbers
  equations by appendix. The numbers below are those of the article build.
- Paper C2, "What the occupation functional of a finite Markov chain determines: principal
  minors, modal supports and cycle trees", journal file `paperC2/problem131_reconstruction.tex`
  (33 pages) and arXiv file `paperC2/problem131_reconstruction_arxiv.tex` (37 pages). The C2
  numbers below are those of the revision of October 25, 2026, the same in both builds for
  Sections 1 to 6.

The numbers are those of the builds of October 24, 2026, checked against the PDFs and the `.aux`
files. For C1 they are the numbers after the cuts of that day (the weak field and the start, item
19 of the C audits) and after the deep edit that followed (item 20, which renumbered Sections 5
and 7). The key in parentheses is the `\label` in the source. In October 2026 Paper B
("Vertex crossings in a symmetric Markov multinomial model", arXiv:2610.09258) was merged into
Paper C, and after the split its results are in C1. The statements of Sections 7 and 8 and of
Appendices C and D of C1 come mostly from Paper B, and their Lean files are in `lean/PaperB`. They keep their
`\label` keys from Paper B, so `lean/PaperB/MAP.md`, which uses the numbers of Paper B, can be read
alongside this file.

Both libraries use Lean 4 v4.33.1 and Mathlib v4.33.1. Every theorem listed here is proved without
`sorry`, `admit` or new axioms, and `#print axioms` reports only `propext`, `Classical.choice` and
`Quot.sound` (see `build-log.txt` and `verification-manifest.json` in the parent folder). A module
name in the column Lean is from `PaperC` unless it is marked `PaperB.`. "In part" means that the
finite or exact core of the statement is in Lean and the rest is listed under "Not in Lean" below.
Lean numbers the states from 0, so state `i` of a paper is state `i - 1` in Lean. Every statement
of the library `PaperB` is for the uniform start (note 1 of `lean/PaperB/MAP.md`). The column
"Note label" names the research note behind each row.

History. Until October 24, 2026 this file used the numbers of the earlier EJP version
(`archive/paperC_switching_ejp/problem131_switching.pdf`, with its supplement) and then of the
joint paper for the Journal of Theoretical Probability. Statements of the earlier version that
neither C1 nor C2 states are collected in their own section below.

## Modules

| Module | Paper | Content |
| --- | --- | --- |
| `ChainLaw` | C1 | the chain, the exact composition law and the run expansion |
| `ChainApps` | C1 | the vertex law, the star zero set, the pair identity, face masses and the directed 3-cycle |
| `Rayleigh` | C1 | Rayleigh quotients, the principal Dirichlet eigenvalue `dirEig Q F`, Barta's bound and monotonicity in the face |
| `Spectra` | C1 | exact `λ_F` for complete graphs, cycle arcs and path end-arcs, and the complement bound |
| `DVRate` | C1 | the Donsker–Varadhan rate of a face and its minimum `λ_F` |
| `DVRestriction` | C1 | the restriction identity `J_F = J_V` on a face (4 theorems) |
| `SingleJump` | C1 | Rayleigh minimizers are eigenvectors, and the single-jump criterion |
| `CycleCascade` | C1 | arc eigenvalues, switch values, the bounds on `D_k` and the cascade on `C_d` |
| `Winners` | C1 | the winners at first order and the finite hull theorem |
| `Constants` | C1 | the second-order constants in finite form, and the arithmetic of the `K_3` window (an example cut from C1) |
| `TwoTriangles` | earlier version | the graph `Θ_ε` |
| `Paw` | earlier version | the paw, with all 15 faces |
| `DisjointJumps` | earlier version | the house and `K_4` plus a vertex, with all 31 faces each |
| `PrincipalMinors` | C2 | the multiaffine expansion of `R_F`, and equal characteristic polynomials (7 theorems) |
| `GeneratorFiber` | C2 | irreducibility, the generator point, the sign of a Metzler-preserving diagonal similarity and the fiber on three states (26 theorems) |
| `CriticalWindow` | C2 | the four-state example of Section 6 (26 theorems) |
| `Planar` | Paper E | the planar walk |
| `Sticky` | note S3 | the thresholds and the direct jump for sticky priors |
| `Fisher` | note S1 | the Fisher efficiency identity |
| `PaperB.*` | C1 | the 19 modules of `lean/PaperB`, listed in `lean/PaperB/MAP.md`: the complete graph (words, the run polynomial `S_n`, the refresh and integral forms, the unique crossing, log-concavity and balancing, the constants `a_k`, the lines of the field) and the vertex law (the Laguerre–Bessel inequality, the polynomial of the rare counts, the compound-binomial representation and the bracket) |

The modules `DVRestriction`, `PrincipalMinors`, `GeneratorFiber` and `CriticalWindow` were added
on October 24, 2026. On October 25, 2026 the library was rebuilt with `verify_lean.py PaperC`
(`lake build PaperC`, exit 0, 20 modules, 409 theorem and lemma declarations, no build warnings).
Every theorem, those of the four new modules included, depends only on `propext`,
`Classical.choice` and `Quot.sound`, as recorded in `build-log.txt` and
`verification-manifest.json`. None uses `sorry` or `native_decide`.

# Paper C1

## Section 2, setting, notation and the exact law

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Section 2.1, the chain with transition matrix `I + hQ` and the law `P_N(n)`, which sums to 1 | `stepP`, `chainWt`, `wordWt`, `lawP`, `sum_wordWt` | C1 Section 1 |
| Lemma 2.3 (`lem:runs`), the run expansion | `lawP_run_expansion`, with `wordWt_eq_runWt`, `chainWt_eq`, `card_runSet`, `runs_noAdjEq`, `sum_runComp` | C1 Prop 1, C5 Lemma 1(a) |
| Equation (1) (`eq:vertexmax`), the exact part `M_{i} = μ_i (1 - h q_i)^{N-1}` | `lawP_vertex` | C2 Prop C2.8 |
| Example 2.5(ii) (`ex:models`), the Potts form of the word probability on the complete graph, the total mass and `V_N = p^(N-1)/d` | `PaperB.Model`: `pathWeight_eq`, `wordProb_eq`, `sum_wordProb`, `sum_law`, `law_vertex`, `occ_eq_vertex_iff` | B §1.2 |
| Equation (2) (`eq:runform`), the run form, for the uniform start (it is (20)) | `PaperB.Model`, `PaperB.Words`, `PaperB.Crossing`: `law_div_vertex`, `law_eq_SL`, `law_eq_V_SL`, `sum_changes_eq_SL` | B Prop 2.2(b) |

## Section 3, the killed functional

| Paper statement | Lean | Hypotheses in Lean | Note label |
| --- | --- | --- | --- |
| Equation (3) (`eq:JV`), the form `q_i - ∑_{j≠i} q_ij u_j/u_i` of the functional | `dvPhi_eq_exit_form` | `u > 0` on `F` | |
| Proposition 3.1 (`prop:restriction`), the restriction identity `J_F(α) = J_V(α)` | `dvRate_restriction`, with `dvPhi_univ_le_face` (the upper bound for every positive `u`) and `dvPhi_univ_extend` (with `u = w` on `F` and `ε` off `F` the functional moves by `-εK`, `K ≥ 0`) | `Q` on `Fin d` Metzler, `α ≥ 0` and `α = 0` off `F` (the sum `1` is not needed), `J_V = dvRate Q univ` and `J_F = dvRate Q F` of `DVRate`, real suprema | |
| Proposition 3.3(a) (`prop:rate`), the lower bound `J_F ≥ λ_F` and the value `λ_F` at `α*_F`, without reversibility | `dvRate_ge`, `dvRate_isLeast`, `dvPhi_le_at_qe`, `dvPhi_at_qe_r`, `dvRate_at_qe` | a positive Perron vector is a hypothesis | C1 Prop 8(a),(b), C4 Lemma DV(a),(b) |
| Proposition 3.3(c), the reversible form at interior points, with minimizer the squared Perron vector | `dvRate_symm`, `dvRate_symm_min` | symmetric `Q` | C1 Prop 8(c) |
| Lemma 3.2 (`lem:face-monotone`) for symmetric `Q`, through the Rayleigh–Ritz form of `λ_F` in Proposition 3.4 (the strict part is by hand) | `dirEig`, `bottomEig`, `bottomEig_le`, `barta`, `isLeast_rayleigh_of_pos_eigvec`, `dirEig_anti` | symmetric `Q` | C2 Lemma C2.1 |

## Section 4, first-order face selection

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Section 4.1, the 4-cycle with unit rates, the exit rates `2`, `1`, `2 - √2`, `0` and the winners (the arcs of 3 states never win) | `cycle_arc_isLeast`, `cycle_arc_dirEig`, `cycle_full_dirEig`, `lamArc_one`, `lamArc_two`, `lamArc_three`, `cycle_cascade` (with `d = 4`), `tau_full_table` | C2 Lemma C2.6a, Theorem C2.6(b),(c) |
| Section 4.1, the constant `1/√(2π)` of a pair on the 4-cycle | `Karc_pair` | C5 Cor 13 |
| Theorem 4.4(a) (`thm:hull`), in finite form (the least exit rate of each size decreasing strictly with the size) | `size_unique_min_iff`, `size_tie`, `face_winner_iff` | C2 Theorem C2.3 |
| Theorem 4.4(b) | `winner_monotone`, `winner_strict` | C2 Theorem C2.2(ii) |
| Theorem 4.4(c), the comparison step of its proof (a face with a proper subface of the same exit rate never wins) | `not_winner_of_sub` | C2 Theorem C2.2(i) |
| Theorem 4.4, the last winner (a face with `λ = 0` and `d` states beats `F` for `τ > (d - \|F\|)/λ_F`) | `full_beats` | C2 Theorem C2.2(iii) |

## Section 5, the second-order theory

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Proposition 5.2(a) (`prop:constant`), `det Σ · det ∇²J_F = 1`, only for the directed 3-cycle | `dicyc_H_mul_Sigma`, `dicyc_det_H` | C5 Prop 4(a) |
| Proposition 5.2(b), the tree formula for `det Σ`, for `k = 2, 3` (also Lemma 3.4 of Paper B) | `tree_formula_two`, `tree_formula_three` | C5 Prop 4(b) |
| Example 5.11(i) (`ex:threecycle`), the exact `M_{1}` and `M_{1,2}`, with `M_{1,2}` attained only at `(1, N-1, 0)` | `dicyc_vertex`, `dicyc_face`, `dicyc_face_max`, `dicyc_face_max_strict` | C5 Prop 19(i) |
| Example 5.11(i), `α*`, `det ∇²J_F` and `K_{1,2,3}` for the full face (the proof now computes `det Σ_{α*} = 3b²/(1+2b)⁴` from the Hessian of `J_V`, which is `dicyc_det_H`) | `dicyc_stationary`, `dicyc_inverse`, `dicyc_Sigma`, `dicyc_det_Sigma`, `dcH_eq_notes`, `dicyc_det_H`, `dicyc_K`, `dicyc_K_four` | C5 Prop 19(i) |
| Example 5.11(ii), exactly one root (the ratio `M_{1,2}/M_{1}` increases strictly in `h`) | `dicyc_ratio_strictMono`, `dicyc_crossing_unique` | C5 Prop 19(ii) |

## Section 7, the complete graph

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Lemma 7.1 (`lem:weighted-cayley`), the weighted Cayley formula, only for `k = 3`: `tree(√(α_i α_j)) = √(α_1 α_2 α_3)(√α_1 + √α_2 + √α_3)` | `cayley_three` | C5 Prop 4(b), B Lemma 3.5 |
| Corollary 7.3 (`cor:paperB`), `λ_F = d - k`, the tie at `τ = 1` and `b_FG = a_k`, with `a_k = -(1/(k-1)) log D_k` | `completeQ_isLeast`, `completeQ_dirEig`, `complete_costs`, `complete_tie`, `paperB_constant` | C5 Cor 11, C2 Theorem C2.4, B (1) |
| Theorem 7.4(i) (`thm:simplex-crossing`), exactly one crossing in `(0,1)`, with the face maximum above the vertex below it and below the vertex above it | `PaperB.Crossing`: `face_crossing`, with `SL_strictMonoOn`, `SL_zero`, `SL_root`, `SL_at_crossing`, `uOf_strictAnti` | B Thm 3.2 |
| Theorem 7.4(i), `p_{N,k}` strictly increasing in `N` (one step from `N` to `N + 1`) | `PaperB.Crossing`, `PaperB.Words`: `face_crossing_strictMono`, with `faceBal_root_lt`, `SL_lt_SL_succ`, `dupFirst_injective`, `lch_dupFirst`, `faceBal_succ` | B Thm 3.2 |
| Theorem 7.4(i), `S_n = k! u^(k-1)` at `N = k`, the formula for `p_{k,k}`, and `(k!)^(-1/(k-1)) < 1` | `PaperB.Crossing`: `SL_faceBal_self`, `face_crossing_kk`, `kk_odds_lt_one` | B Thm 3.2 |
| Theorem 7.4, the coefficients `W_n(k-1) = k!` and `W_n(k) = k!(k-1)(N-k)/2` (in its proof in Appendix C.1) | `PaperB.Coefficients`: `W_first`, `W_second`, with `WP_coeff`, `PiB_low` | B Thm 3.2 |
| Theorem 7.4(iv), `a_2 > a_3 > ...` | `PaperB.Constants`: `aConst_strictAnti`, with `gfun_strictMonoOn`, `Hfun_pos` | B Thm 3.1(iv) |
| Theorem 7.5 (`thm:simplex-balance`), the transfer of one unit for `1/d ≤ p < 1`, for the uniform start (the case of a start constant on the face follows by (2) and is not in Lean) | `PaperB.Balance`: `law_transfer`, and in part `law_max_balanced`, `law_perm` | B Thm 3.8 |
| Theorem 7.5, proof in Appendix C.2, strict log-concavity of `B_n(y)` and the transfer inequality `B_{a+1} B_{b-1} > B_a B_b` | `PaperB.LogConcave`: `Bpoly_logconcave`, `bb_succ`, `cc_bb_strict`, `bb_logconcave`, `pair_identity`, `Bpoly_transfer`, `Bratio_strictAnti` | B Thm 3.8 |
| Remark 7.7 (`rem:simplex-edge-mode`), `P_4(2,2,0)/V_4 = 2u + 2u^2 + 2u^3`, `P_4(2,1,1)/V_4 = 6u^2 + 6u^3`, the values at `u = 7/20`, and the edge centers as the only modes | `PaperB.EdgeExample`: `ratio_220`, `ratio_211`, `u_at`, `edge_ratio`, `center_ratio`, `edge_modes`, `classify4` | B Ex 3.10 |

## Section 8, near a vertex

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Lemma 8.1 (`lem:uniform-laguerre-bessel`), `0 ≤ 1 - B_a(w)/(w 𝓘(aw)) ≤ w/2` (Lean writes `Phi` for `𝓘`) | `PaperB.LaguerreBessel`: `laguerre_bessel`, `laguerre_bessel_diff`, with `clipTau_eq`, `clipTau_deficit`, `Zf_eq_tsum`, `phi_summable`, `Phi_pos` | B Lemma 6.1 |
| Lemma 8.1, proof in Appendix D, the identity `∑_j j(j+1) x^j/(j!(j+1)!) = x 𝓘(x)` and the clipped product (the paper cites Paper A, Lemma 3.2, for the latter) | `PaperB.LaguerreBessel`, `PaperB.Clipped`: `tsum_phiTerm2`, `phiTerm2_succ`, `clipped_product`, `clipped_product_aux` | B Lemmas A.1(i), A.2 |
| Section 8, `𝓑(y) = 1` has exactly one positive root `y_a ≤ 1` (Lean writes `H` for `𝓑`), and `S_(b,a)(u) = 1` has exactly one positive root | `PaperB.VertexH`, `PaperB.Crossing`: `H_root`, `H_strictMonoOn`, `H_one_ge`, `SL_root`, `SL_strictMonoOn` | B §6.1 |
| Theorem 8.2 (`thm:vertex-uniform-root`), the bracket (24), `(1-δ)√(y_a/b) ≤ u_{b,a} ≤ (1+δ)√(y_a/b)` for `δ = 16 c_ℓ ε ≤ 1/2` | `PaperB.Randomization`, `PaperB.VertexRoot`: `vertex_uniform_root`, with `vertex_bracket`, `logH_increment`, `upper_step`, `lower_step`, `lower_core`, `s_bound`, `log_chain` | B Thm 6.4 |

## Appendix C, proofs for the complete graph

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Lemma C.1(a) (`lem:refresh`), the refresh form, for the uniform start, and the multinomial law at `p = 1/d` | `PaperB.Refresh`, `PaperB.Balance`: `law_closed`, with `endLaw_closed`, `Bpoly_derivative_succ`, `coeff_Bpoly`, and `law_multinomial`, `PiB_coeff_top` | B Prop 2.2(a) |
| Lemma C.1(b), the ratio form (33) | `PaperB.EdgeExample`, `PaperB.Coefficients`: `law_div_closed`, `WP_eq_CP` | B Prop 2.2(c) |
| Lemma C.1(b), the integral form (34), as the integral form of the law and for the vector `(b, a_1, ..., a_ℓ)` | `PaperB.Balance`, `PaperB.Randomization`: `law_integral`, with `integral_exp_neg_pow`, `integral_exp_poly`, `sig_pos`, `rr_pos`, and `S_integral` | B (17), (21) |

## Appendix D, proofs near a vertex

| Paper statement | Lean | Note label |
| --- | --- | --- |
| Lemma D.1 (`lem:vertex-elasticity`), `𝓑` is convex, `log 𝓑` is concave, `κ` is the sum of the elasticities of the factors and is nondecreasing | `PaperB.VertexH`, `PaperB.Elasticity`: `H_convexOn`, `H_coeff_nonneg`, `logH_concaveOn`, `logB_concaveOn`, `kapH_eq`, `kap_eq`, `kapH_monotoneOn`, `kap_monotoneOn` | B Lemma D.1 |
| Lemma D.1, (35), `1/(\|a\|+1) ≤ y_a ≤ 1`, `κ(y) ≤ ℓ + √(ℓ\|a\|y)` and `κ(y) ≥ max{ℓ, ½√(\|a\|y)}` (upper bound for `y > 0`, lower bound for `0 < y ≤ 1`) | `PaperB.VertexH`, `PaperB.Elasticity`: `H_root`, `H_small_lt`, `H_one_ge`, `Bpoly_le_exp`, `exp_half_lt_two`, `kapH_le`, `kap_le`, `kapH_ge`, `kapH_ge_half_sqrt`, `kap_ge_one`, `kap_ge_half_sqrt`, `kap_ge_sqrt_sub` | B Lemma D.1 |
| Lemma D.1, Steps 1 and 3 of the proof | `PaperB.Elasticity`: `wt_shift`, `shift_sum`, `cov_JR`, `var_le`, `ode_moment`, `kap_sq_add`, `cs_moment` | B Lemma D.1 |
| Lemma D.2 (`lem:vertex-randomization`), in part, the integral form (36) of `S_(b,a)`, the mass `v(1+v)^(b-1)` of `e^(-t) B_b(vt)`, its first moment and exponential moments | `PaperB.Randomization`: `S_integral`, `L1_eq`, `Lt_eq`, `sum_choose_mul`, `Ls_eq`, `binom_inv_sum` | B Lemma D.2 |
| Lemma D.2, (37) and (38) | `PaperB.Randomization`: `jensen_lower`, `tangent_upper` | B Lemma D.2 |

## Differences between the Lean statements and C1

For the statements from Paper B, `lean/PaperB/MAP.md` lists the differences in its notes 1 to 29,
with the numbers of Paper B. The main ones for C1 are these. Every `PaperB` statement is for the
uniform start, so Theorem 7.5 for a start that is constant on the face is not in Lean beyond the
rows above. `S_n` is indexed by the full vector on `d` states in Lean,
and that it does not depend on `d` is not proved (note 5 there), which matters for Lemma D.2 and
Theorem 8.2 inside a chain with more states. The monotonicity in Theorem 7.4(i) is one step from
`N` to `N + 1` for one balanced vector (note 8 there). The bracket of Theorem 8.2 is strict in
Lean, and the form (25) is not a Lean statement (note 24 there).

## Not in Lean, C1

The asymptotic results are not in Lean, since they need the Laplace method, local limit theorems
or expansions as `N → ∞`. Mathlib has no Perron and Frobenius theorem for irreducible Metzler
matrices and no Donsker and Varadhan formula for the principal eigenvalue, so a positive Perron
vector is a hypothesis where one is needed. In terms of the paper these are the following.

* Section 2. Lemma 2.2 (`lem:admissible`), Lemma 2.4 (`lem:continuum`) and the asymptotic form in
  equation (1).
* Section 3. Proposition 3.3(b) and (d), the uniqueness of the minimizer in (a), and (c) on the
  boundary of the face. Proposition 3.4 (`prop:variational`) and Lemma 3.2 (`lem:face-monotone`)
  in general, including the strict monotonicity of `λ_F` in the face.
* Section 4. Lemma 4.1 (`lem:upper`), Theorem 4.2 (`thm:first`), Remark 4.3 (`rem:first-field`),
  and Theorem 4.4(a) beyond the finite form.
* Section 5. Proposition 5.2(a) in general, Corollary 5.3 (`cor:symface`) for general `k`,
  Theorem 5.4 (`thm:local`), Lemma 5.5 (`lem:discrete`), Theorems 5.6 to 5.9 (`thm:stratified`,
  `thm:facemax`, `thm:crossing`, `thm:window`), Remark 5.10, the expansion in Example 5.11(ii),
  Example 5.11(iii), and Proposition 5.12 (`prop:uniform-facemax`).
* Section 6, the boundary layer, in full.
* Section 7. Lemma 7.1 for `k ≠ 3`, Example 7.2, the asymptotic parts of Corollary 7.3, Theorem
  7.4(ii) and (iii), the display (21) and Corollary 7.6 (`cor:simplex-modes`).
* Section 8. The form (25) of Theorem 8.2, and Remark 8.3.
* Appendices A and B, and Appendices C and D beyond the rows above.

## Findings for C1

* No mathematical error was found in the statements above.
* Example 5.11 assumes `b > 2`. The monotonicity of `M_{1,2}/M_{1}` in `h`, and hence the
  uniqueness of the first crossing in 5.11(ii), holds for every `b > 1` (`dicyc_ratio_strictMono`).

# Paper C2

The modules `PrincipalMinors`, `GeneratorFiber` and `CriticalWindow` cover finite and algebraic
results of Sections 3 and 5 of C2. The declarations of `CriticalWindow` are in the namespace
`Kagey131.PaperC.FourState` and the others in `Kagey131.PaperC`. In Lean the states `1, 2, 3, 4` of
the paper are `0, 1, 2, 3`.

Irreducibility. `GeneratorFiber` defines `CutIrreducible C` for a real square matrix. Every nonempty
proper set of states `S` has an arc `C i j ≠ 0` with `i ∈ S` and `j ∉ S`. This is the "no
nontrivial invariant coordinate subset" form. `cutIrreducible_iff_reach` proves that it is
equivalent to the strong connectivity of the digraph of nonzero off-diagonal entries
(`Relation.ReflTransGen` of the arcs `i → j`, `i ≠ j`, `C i j ≠ 0`), which is the definition of
the paper. Mathlib's `Matrix.IsIrreducible` is not used, since it requires nonnegative entries.
`IsMetzler` (nonnegative off-diagonal entries) and `IsGenerator` (Metzler with zero row sums) are
also defined there.

## Section 3, the functional and the principal minors

| Paper statement | Lean | Hypotheses in Lean | Note label |
| --- | --- | --- | --- |
| Section 3.1, the display defining `R_F`: `det(-Q_F - diag w) = ∑_{A⊆F} det(-Q_A) ∏_{i∈F∖A}(-w_i)`, with `det(-Q_∅) = 1` | `det_sub_diagonal_eq_sum_minors`, `det_add_diagonal_eq_sum_minors`, `RF_eq_sum_minors`, `pminor_faceBlock`, `pminor_empty`, `pminor_univ` | any square matrix over a commutative ring (applied with `A = -Q`). The sum in `RF_eq_sum_minors` is over the subsets of the subtype `F`, and `pminor_faceBlock` identifies these minors with minors of `A` | plan review 2026-10-23, Section 5.3 |
| Corollary 3.6(a) (`thm:nonreversible`) and step (N) of its proof, equal principal minors give the same characteristic polynomial, hence the spectrum of `Q` | `charpoly_eq_of_minors_eq` | any square matrices over a commutative ring | note 06, Lemma 3.1 |
| Step (N) of the proof of Corollary 3.6, the generator point `-D⁻¹CD` with `D = diag x` is a generator | `conj_apply`, `normalize_isGenerator` | `C` Metzler (in Lean `C` is minus the Z-matrix of the paper), `x > 0`, `C x = 0` | note 06, Proposition 3.3 |
| Step (N), the null vector is unique up to a factor | `ker_eq_smul` | `C` Metzler and `CutIrreducible`, with a positive null vector `x`. Its existence (Perron and Frobenius) is a hypothesis | note 06, Proposition 3.3 |
| Step (N), every real invertible diagonal `D'` for which `D'⁻¹CD'` has zero row sums is a multiple of `D` and gives the same matrix | `normalization_unique`, `normalization_unique_matrix` | as for `ker_eq_smul`. The entries of `D'` are nonzero, of any signs | note 06, Proposition 3.3 |
| The sign lemma, named in Section 6 among the Lean results (it is not a numbered statement of C2). If `D C D⁻¹` is Metzler, the entries of `D` have one sign | `sign_constant` | `C` Metzler and `CutIrreducible`, `D` real diagonal with nonzero entries | note 06, Lemma 3.2 |
| Remark 3.7 (`rem:three-states`), with the products `ω = q_12 q_23 q_31` and `ω' = q_13 q_32 q_21` (Lean writes `c`, `c'`), `ω + ω' = q_1q_2q_3 - q_1w_23 - q_2w_13 - q_3w_12` and `ωω' = w_12w_23w_13` | `det_neg_three` (`det(-Q) = σ₃ - c - c'` for every `3 × 3` matrix), `det_neg_three_eq_zero`, `cyc_add_cycRev`, `cyc_mul_cycRev`, `sigma3_congr` | zero row sums for the first identity, none for the second | note 06, Corollary 4.2 |
| Remark 3.7, the case of the same ordered pair `(ω, ω')` gives `Q' = Q` | `eq_of_same_q_w_cyc` | two generators on `Fin 3` with all off-diagonal entries positive, the same diagonal, the same `w_ij` and the same `ω` | note 06, Corollary 4.2 |
| Corollary 3.6(a), the time reversal `Q* = D_π⁻¹QᵀD_π` is a generator with the exit rates and the products of `Q`, and its oriented product is `ω'` | `timeRev_eq_conj`, `timeRev_diag`, `timeRev_wprod`, `cyc_timeRev`, `timeRev_rowsum`, `timeRev_isGenerator`, `fiber_three_converse` | `π > 0` with `πQ = 0` | note 06, Corollary 4.2 |
| Corollary 3.6(d), the fiber on three states is `{Q, Q*}` | `fiber_three`, and `fiber_three_tree` with `π` from the tree formula (`piTree_pos`, `piTree_stationary`), so with no hypothesis on `π` | two generators on `Fin 3` with all off-diagonal entries positive, the same diagonal and the same `w_ij` (these are the minors of orders 1 and 2). The paper allows any irreducible `Q`, with zero entries, and that case is not in Lean | note 06, Corollary 4.2 |

## Section 5, low temperature and the cycle hierarchy

| Paper statement | Lean | Hypotheses in Lean | Note label |
| --- | --- | --- | --- |
| Example 5.5 (`ex:four-state`), the rates, `π ∝ (1, t, t, t)` and the exit rates `q_1, …, q_4` | `qOff`, `Q4`, `Q4_offdiag`, `Q4_rowsum`, `detailed_balance`, `exit_rates` | `t` real (the identities need no sign) | C modal hierarchy 01, (28) |
| Example 5.5, the killed matrices `-Q_{12}`, `-Q_{123}` (the display) and `-Q_{124}` | `killed_12`, `killed_123`, `killed_124` | | |
| Example 5.5, `det(-Q_{12}) = 2t⁴ + O(t⁵)` and `det(-Q_{123}) = det(-Q_{124}) = 2t⁶ + O(t⁷)`, as the exact polynomials `2t⁴ + t⁵ + 2t⁶ + 2t⁷ + t⁹` and `2t⁶ + t⁷ + 6t⁸ + 4t⁹ + 3t¹¹` | `det_A12`, `det_A123`, `det_A124` | | C modal hierarchy 01, (29) to (31) |
| Example 5.5, the adjugates, with first columns `(t, t) + O(t²)`, `(3t³, 3t³, 2t³) + O(t⁴)` and `(t³, t³, 0) + O(t⁴)` and other entries `O(t²)`, resp. `O(t⁴)`, as exact polynomial matrices | `adj_A12`, `adj_A123`, `adj_A124` | | C modal hierarchy 01, (29) to (31) |
| Example 5.5 with Proposition 5.3 (`prop:prefactor`), `t³(-Q_F)⁻¹ → B_F`, with first columns `(1/2, 1/2)`, `(3/2, 3/2, 1)`, `(1/2, 1/2, 0)` and zeros elsewhere | `B12_limit`, `B123_limit`, `B124_limit`, with `tendsto_scaled` and `inv_apply_eq` | entrywise, as `t → 0⁺` | |
| Example 5.5, `ρ(B_12) = 1/2`, `ρ(B_123) = 3/2`, `ρ(B_124) = 1/2`, so `a_12 = 2`, `a_123 = 2/3`, `a_124 = 2` | `B12_eigen`, `B123_eigen`, `B124_eigen` | the first column is an eigenvector for the stated value. That the other eigenvalues are `0` (only the first column of `B_F` is nonzero) is not a Lean statement | |
| Example 5.5, the limiting scores `1 + 2x`, `2 + 2x/3`, `2 + 2x`, `3`, the unique minimizer `{1,2}` on `(0, 3/4)`, `{1,2,3}` on `(3/4, 3/2)` and `V` on `(3/2, ∞)`, `{1,2,4}` always `1` above `{1,2}`, and the score `8/3 < 3` at `x = 1` | `s12`, `s123`, `s124`, `sV`, `window_low`, `window_mid`, `window_high`, `score_124`, `noncycle_at_one` | `x` real in the stated interval | C modal hierarchy 01, (32), (33) |

## Not in Lean, C2

* Lemma 3.1 (`lem:RF-irreducible`), the irreducibility of `R_F` over `ℂ`, and Lemma 3.2
  (`lem:perron-branch`), which needs the Zariski density of a smooth real piece of a hypersurface.
  Only the expansion of `R_F` is in Lean. Theorem 3.3 (`thm:dv`) and Remark 3.4.
* Corollary 3.6(a) beyond the rows above (the irreducibility of the fiber points and the finiteness),
  (b) and (c), and (d) for an irreducible `Q` on three states with some off-diagonal entries `0`.
  `fiber_three` assumes that all six off-diagonal entries of both generators are positive. In the
  normalization (N) the existence of the positive null vector, from Perron and Frobenius, is a
  hypothesis of the Lean statements.
* Remark 3.8 and Proposition 3.9, and Section 4 in full. The reversible design of the arXiv
  version (its Section 7) is not in Lean.
* Section 5 beyond Example 5.5. In Example 5.5, the cycles and the depths, the passage from the
  limits `B_F` to `a_F` through the spectral radius beyond the eigenvectors above, and the step
  from the limiting scores to the support of the mode (Theorem 5.4, `thm:critical-window`).

## Findings for C2

No error was found in these statements. The exact computation gives `det(-Q_{123}) = det(-Q_{124})`
as polynomials in `t`, which the paper does not need. The determinants and the adjugates of
Example 5.5 agree with an exact recomputation in rational arithmetic, and their leading terms with
the paper. Since October 25, 2026 the proof of Example 5.5 gives these cofactors by hand.

# Statements of the earlier version that neither paper states

These rows use the numbers of the earlier EJP version and its supplement
(`archive/paperC_switching_ejp`). The Lean theorems stay in the library.

| Statement of the earlier version | Lean | Note label |
| --- | --- | --- |
| Corollary 7.1(b), `K_arc3` from the closed form for all arcs (C1 Section 4.1 keeps the pair constant) | `Karc_three` | C5 Cor 13 |
| Corollary 7.1(c), the exact identity `M_pair = M_vertex S_N(u)` on the 4-cycle | `lawP_pair_ratio` | C5 Prop 12 |
| Table 2, row `C_d`, marked "Lean only" (the growth like `k³/(2π²)` is by hand). Figure 4 of C1 before the deep edit showed the cases `C_6` and `C_5` as illustrations, and C1 no longer has it | `cycle_arc_isLeast`, `cycle_arc_dirEig`, `pathM_isLeast`, `pathM_eig`, `cycle_full_dirEig`, `lamArc_strictAnti`, `lamArc_convex`, `tauArc_lt_succ`, `tauArc_lt`, `DArc_two`, `DArc_gt`, `DArc_lt`, `cycle_cascade`, `arcCost_unique_min`, `d_sub_two_thirds`, `lamArc_one` to `lamArc_five`, `tauArc_two` to `tauArc_five`, `tau_full_table` | C2 Lemmas C2.6a, C2.6b, Theorem C2.6 |
| Table 2, row `P_d`, and Proposition S1.3 of the supplement (`prop:paths`), in part (the end-arc exit rates in S1.3(a) and the golden ratio `τ'_2` of Lemma S1.2(a)) | `path_endArc_isLeast`, `path_endArc_dirEig`, `endArcM_isLeast`, `endArc_eq_lamArc`, `path_first_threshold` | C2 Cor C2.6′ |
| Table 2, row `Θ_ε`, and Proposition S1.4 of the supplement (`prop:triangles`), in part | `theta_triangle_isLeast`, `lamTri_root`, `lamTri_pos`, `lamTri_lt_one`, `lamTri_lt_three_quarters_iff`, `theta_edge_isLeast`, `theta_vertex_isLeast`, `tauA_formula`, `tauStar_formula`, `theta_eps_one`, `theta_comparisons`, `eps1_root`, `theta_four_le`, `theta_four_lt_half`, `theta_four_mono` | C2 Prop C2.7 |
| Table 2, row paw, marked "Lean only" | `face_dirEig_eq`, `face_dirEig_ge`, `paw_w1` to `paw_w4`, `paw_bounds`, `paw_phase1` to `paw_phase4`, `paw_not_nested` | C2 Prop C2.10 |
| Table 2, rows house and `K_4` plus a vertex, marked "Lean only" | `house_bounds`, `house_w_vertex`, `house_w23`, `house_w014`, `house_wV`, `house_phase1` to `house_phase4`, `house_disjoint`, `kfv_bounds`, `kfv_w4`, `kfv_wK`, `kfv_wV`, `kfv_phase1` to `kfv_phase3`, `kfv_disjoint` | C2 Prop C2.9(b) |
| Example 5.15, in part, the comparison of the three scores and the condition `H > 6(a_2 - a_3)` (Step 4 of the proof of Corollary 7.11 of C1 before the cuts proved the general form) | `PaperB.Modes`: `triangle_edge_phase`, `triangle_interval_nonempty` | B Ex 5.3 |
| Section 8, the zero set on a star (`P_N(n) = 0` when `supp n = [d]` and `n_d < ℓ - 1`) | `star_law_zero`, `star_runs_bound`, `star_length_bound`, `noAdjLeaves_of_switchProd` | C1 Example 7 |

## Statements cut from C1 on October 24, 2026

We cut the weak field (Proposition 5.15 with Section 5.6, and Section 7.4) and the start (Section
7.3) from C1 before the arXiv submission. These rows use the numbers of C1 before the cuts
(70 pages). The Lean theorems stay in the library.

| Statement of C1 before the cuts | Lean | Note label |
| --- | --- | --- |
| Example 7.10 (`ex:K3-start`), the comparison of the lines and the width `log(16/(9√3)) > 0` of the window | `three_lines`, `k3_edge_window`, `k3_window_width`, `k3_edge_criterion`, `k3_half_half_criterion` | C5 Prop 14, B Ex 4.9 |
| Corollary 7.11 (`cor:weakfield-phases`), in part, Step 3 of the proof (the winning size is nondecreasing in `t`, so a line of larger slope that wins at `t_1` wins at every `t_2 > t_1`) | `PaperB.Modes`: `winning_size_monotone` | B Rem 4.8, B Thm 5.2 |
| Corollary 7.12 (`cor:weakfield-full-hierarchy`), the average `(k-1)(2k-1)/6` of `(i-1)^2`, `log D_k = -(k-1) a_k` with `D_1 = 1` (Lean writes `c_k` for `log D_k`), the second difference `≤ 1/2`, `ℓ_{k+1} - ℓ_k = t - t_k`, `t_1 < t_2 < ...` for `H > 3/4`, and in part the strict maximum of line `k` | `PaperB.Modes`, `PaperB.Constants`: `field_average`, `sum_sq_range`, `cConst_one`, `cConst_eq_aConst`, `cConst_second_diff`, `cConst_sub_concave`, `lam_succ_sub`, `lam_one`, `tau_lt_succ`, `tau_strictMono`, `tau_mono`, `line_unique_max` | B Cor 5.4 |

For Corollary 7.12 the comparison with the lines `j < d` above `c_d - c_{d+1} + H(4d-1)/6` was not a
stated theorem (note 17 of `lean/PaperB/MAP.md`). Not in Lean were Proposition 5.15 (`prop:weakfield`),
Corollary 7.9 (`cor:start-crossings`), the step from the lines to the modes in Example 7.10, and
Corollaries 7.11 and 7.12 beyond the rows above.

### Statements cut in the deep edit of C1

Later on October 24 we cut the tree formula on a general face, Section 7.1 and Remark 7.4 from C1
(item 20 of the C audits). These rows use the numbers of C1 after the first cuts and before the
deep edit (67 pages). The Lean theorems stay in the library.

| Statement of C1 before the deep edit | Lean | Note label |
| --- | --- | --- |
| Proposition 7.1 (`prop:pair`), the exact pair identity (for a chain with two states) | `lawP_pair_ratio`, `lawP_locality`, `wordWt_common_rate` | C5 Prop 12, C2 Prop C2.8 |
| Corollary 7.2 (`cor:paperA`), `K_{1,2} = √(2/π)` and `b_FG = c_0`. It is the case `d = k = 2` of Theorem 7.4 of the current C1 | `paperA_constant` | C5 Cor 10 |
| Remark 7.4 (`rem:outcomes`), the complete graph (the vertices win for `τ < 1`, the whole set for `τ > 1`, all faces tie at `τ = 1`). The tie is still in Corollary 7.3 of the current C1 | `completeQ_isLeast`, `completeQ_dirEig`, `completeQ_killed_perp`, `completeQ_row_sum`, `complete_costs`, `complete_vertex_wins`, `complete_full_wins`, `complete_tie` | C2 Theorem C2.4 |
| Remark 7.4, symmetric `Q`, the bound `λ_{[d]∖{x}} ≤ q_x/(d-1)`, its equality case, and for unit rates equality exactly on the complete graph | `complement_bound`, `complement_isLeast`, `complement_eq_iff`, `eigvec_of_rayleigh_min`, `single_jump_equal_feeding`, `unit_equal_feeding_complete` | C2 Prop C2.5 |

Not in Lean were Proposition 5.11 (`prop:forest`, the tree formula on a general face, used only
for the constant of Example 5.14(i), which the current Example 5.11 computes directly), Lemma A.5
(`lem:forest`), and the asymptotic part of Corollary 7.2. Figure 4 and the display (21) of the
complete-graph local law went in the same edit and had no Lean rows.

The research notes called the per-size minima for the house and for `K_4` plus a vertex a finite
computation to 40 digits rather than a hand proof. `DisjointJumps` replaces it by a proof, with
exact eigenvectors for the winning faces and rational Barta certificates for all other faces. The
paw is proved the same way in `Paw`. So those rows of Table 2 were proved in Lean.

# Notes and papers outside C1 and C2

## The note S3 on sticky priors

This was Section 6 and Appendix D of Paper C until October 2026 (and Section 7 and Appendix E
before the split of October 13). It is now the note `S3_sticky_note/s3_note.tex`, and the numbers
in this table are those of the note.

| Statement of the note S3 | Lean | Note label |
| --- | --- | --- |
| Section 2, Theorem 4.4(b) of C1 for the sticky chain with `λ_F = 1 - ρ_F` | `winner_monotone`, `winner_strict` | C4 Prop S2(a) |
| Proposition 2.2(a) (`prop:thresholds`) | `vertex_wins_iff`, `full_wins_iff` | C4 Prop S2(b) |
| Proposition 2.2(b) | `cMinus_bounds` | C4 Prop S2(c) |
| Proposition 2.2(c), and the tie of the uniform kernel at `τ = d - 1` | `direct_jump_iff`, `uniform_tie` | C4 Prop S2(d) |
| Corollary 2.3 (`cor:uniform-kernel`), `ρ_{i,j} = √(π_ij π_ji)` | `pair_perron` | C4 |
| Corollary 2.3(a) | `symmetric_direct_uniform` | C4 Prop S3(a) |
| Corollary 2.3(b) | `d3_pair_condition`, `cyclic_pair_condition` | C4 Prop S3(b) |
| Proposition 2.4(a) (`prop:directjump`), exactly 2 of the 8 corner kernels have a direct jump | `corner_direct_card` | C4 Prop S3(c) |
| Appendix A (`app:hdp`), the logit identities in the proof of Proposition 2.4(b) | `logit_two_B`, `logit_two_one_sub_B`, `logit_pair_iff` | C4 Prop S3(d) |
| Corollary 2.5 (`cor:sticky-pair`), the exact identity through the pair identity (Proposition 7.1 of C1 before the deep edit, now cut from C1) | `lawP_pair_ratio` | C4 Prop S4 |
| Proposition 2.6 (`prop:mass`), the bounds at finite `N` | `faceMass_eq`, `iterF_sandwich`, `faceMass_sandwich` | C4 Prop S5 |

Not in Lean from the note S3: its Corollary 2.1, Proposition 2.4(b) apart from the logit
identities, and the asymptotic parts of Corollary 2.5, Proposition 2.6 and Remark 2.7.

## Paper E, the planar persistent walk

This was Section 6 of Paper C until October 13, 2026, and it is now Paper E, where its statements
are numbered 3.x. The rows below use the current Paper E numbers. Only the exact or algebraic
portions named here are formalized. The local limits and asymptotic crossing expansions,
including Theorems 3.4, 3.5 and 3.9, are not formalized.

| Statement in Paper E | Lean | Note label |
| --- | --- | --- |
| Section 3, the walk and `c_N = p_0^{N-1}/4` | `planarA`, `planarQ`, `planarQ_eq`, `originMass`, `cornerMass`, `cornerMass_eq` | C3 Section 1.2 |
| Section 3, the face exponents before Lemma 3.1 and the faces that can reach the origin | `planarI_EW`, `planarI_fiber`, `planarI_uniform`, `origin_faces` | C3 Cor 1.1 |
| Theorem 3.3 (`thm:planar-first`), the first-order comparison of the exponents, `τ* = min(2/β, 1/s)` and the switch at `s = 2r` | `planar_first_order`, `planar_first_order_turns`, `planar_switch_rev`, `planar_switch_turn` | C3 Theorem 7 |
| Proposition 3.2 (`prop:decomp`), `o_N/c_N = 2 S_N(u) + E_N` with `E_N ≥ 0`, and an origin path with a turn uses all 4 directions | `planar_origin_identity`, `mixed_nonneg`, `mixed_uses_all_four`, `SPoly_eq_pair_ratio` | C3 Prop 4, C5 Cor 15 |
| Proposition 3.2, the unique crossing for `s > 0` | `planar_ratio_eq`, `originPoly_zero`, `originPoly_strictMono`, `originPoly_unique_root`, `planar_unique_crossing` | C3 Section 1.2 |

## The information in the endpoint

This was Section 8 of an earlier version. It is now the note
`S1_endpoint_information_note/s1_note.tex`, and the numbers in this table are those of the note.

| Statement | Lean | Note label |
| --- | --- | --- |
| Proposition 2.1 of the note S1 (`prop:eta`), `e_N = Var(E[J \| K])/Var J` | `efficiency_eq`, `hasDerivAt_pathP`, `fisherK_eq`, `fisherPath_eq`, `mean_J`, `paperA_pathP`, `paperA_total`, `paperA_efficiency` | C4 Prop F1 |
| The case `N = 2` of Proposition 2.1 of the note S1, `e_2 = 1` | `paperA_efficiency_two` | C4 Prop F2 |

## Lean theorems that no paper states

| Content | Lean | Note label |
| --- | --- | --- |
| The switch product in terms of transition counts, and the balance of in- and out-counts | `switchProd_eq_prod_pow`, `sum_switchCount_out`, `sum_switchCount_in`, `switch_balance`, `switchProd_eq_pow` | C1 Prop 2, in part |
| The Fisher efficiency of the occupancy vector of the sticky chain is a correlation ratio | `sticky_pathP`, `sticky_total`, `sticky_efficiency` | C4 Prop G1 |
| The proof of `Λ_N(h) → h̄` in Paper B, Proposition 5.1(3), with powers of the transition matrix, the mean and the covariance of the occupation counts of the Potts chain. The earlier EJP version proved the limit of the normalizing sum for every irreducible chain in another way, and C1 does not state it. | `PaperB.Covariance`, `PaperB.ChainCovariance`: `trans_pow`, `trans_eq_Tmat`, `mean_occ`, `twoPoint`, `twoPoint_abs`, `cov_kernel`, `cov_occ`, `cov_occ_closed`, `sum_sigma_abs`, `sum_sigma_abs_one`, `ratio_identity` | B Prop 5.1(3) |
| The step of Paper B's generating function that conditions on the last letter | `PaperB.Refresh`: `endLaw_succ`, `law_eq_sum_endLaw`, `endLaw_of_zero` | B Prop 2.1 |
| Singleton insertion and `S_(b,1,...,1)`, and the Gram determinant of a removed remark of Paper B | `PaperB.Singleton`, `PaperB.Modes`: `singleton_insertion`, `SL_b1`, `SL_b11`, `SL_singletons`, `gram_det`, `latVec_gram` | B, removed |
