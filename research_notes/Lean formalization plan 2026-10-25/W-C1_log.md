# W-C1 progress log (Paper C1)

Workspace `~/lean-work/w-c1`, module folder `lean/PaperC/C1/`, sub-root `lean/PaperC/C1.lean`,
namespace `Kagey131.PaperC.C1`. Check command for each file, from `~/lean-work/w-c1`:

    L="C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/kagey-problems/problem131/lean"
    lake env lean "$L/PaperC/C1/<File>.lean"

Modules that import another C1 module were checked after compiling the imported module with
`lake env lean -R "$L" -o .lake/build/lib/lean/PaperC/C1/<File>.olean "$L/PaperC/C1/<File>.lean"`.
No `sorry`, `native_decide` or new axiom anywhere; `#print axioms` on the main theorems gives only
`propext`, `Classical.choice`, `Quot.sound`. The paper statements were read from the current text
of `paperC/sec_complete.tex`, `sec_secondorder.tex`, `sec_dv.tex`, `sec_model.tex`,
`sec_boundary.tex` on October 25.

## Status by target

| Target | Status | File | Theorems | Deviation from the paper |
|---|---|---|---|---|
| C1-1 `lem:weighted-cayley` | done | WeightedCayley.lean | `redLap`, `det_diagonal_sub_vecMulVec`, `redLap_products`, `weighted_cayley_det`, `cayley_count` | The tree sum is the determinant of the reduced Laplacian (no matrix-tree theorem in Mathlib). States are `Fin (k+1)`, so the paper's `k` is `k+1`. `weighted_cayley_det` needs `1 ≤ k` (the empty determinant is 1, the formula would give `x_0`). `cayley_count` holds for all `k`. |
| C1-2 `prop:constant`(b), determinant | done | WeightedCayley.lean | `det_diag_sub_rankOne`, `det_sigma_of_factor`, `det_sigma_formula` | Scalar written `(2:ℝ) •`; `det_sigma_of_factor` assumes `IsUnit L.det`. `det_sigma_formula` is `det Σ_α = 2^k (∏α)^2 / det(redLap c)` for `Σ_α = 2 M L⁻¹ M`. |
| C1-3 `prop:constant`(b), critical point | done | CriticalPoint.lean | `uRev`, `lRev`, `cRev`, `critical_point`, `cRev_symm`, `alpha_theta` | As in the plan; `cRev_symm` does not use `α > 0`. |
| C1-4 `cor:symface`, `ex:complete-face`, `cor:paperB` | done | SymFace.lean | `tree_scale`, `symface_constant`, `sum_offdiag_sqrt`, `Jcomplete`, `tree_complete_face`, `constant_forms_agree`, `paperB_K` | `μ(F)` enters as the scalar `m = (μ·r)(l·1)`. `tree_complete_face` and `paperB_K` need `1 ≤ k`. `constant_forms_agree` proves the three forms of `C_F(α)` (the two of `ex:complete-face` and that of `prop:constant`(b)) equal, for `P = ∏α > 0`, `A > 0`, `n ≥ 2`. `paperB_K` uses `cayley_count`; `PaperC.Constants.paperB_constant` only covers the `a_k` log arithmetic, so it was not enough. |
| C1-5 series of `lem:layer-exact` | done | LayerSeries.lean | `choose_div_factorial`, `hasSum_layer` | `r = ρ - 1` as a natural number. |
| C1-6 `prop:discrete-rate`(a) | done | DiscreteRate.lean | `dvPhiH`, `dvSetH`, `dvRateH`, `dvPhiH_le`, `dvPhiH_univ_le_face`, `dvPhiH_univ_extend`, `dvRateH_restriction`, `dvRateH_restriction_subset` | Hypothesis `1 + h Q_ii > 0` for all `i` (equals `h q_i < 1` for a generator). The converse inequality uses `log(1+x) ≤ x` for an explicit constant `K`, so no limit is needed. The second sentence is `dvRateH_restriction_subset`. |
| C1-7 `prop:discrete-variational` identities | done | DiscreteExit.lean | `Lh`, `Lh_ge`, `integral_exit_rate`, `lambdaH_zero_field` | None. The integral identity needs `h > 0`, `1 + hκ > 0`. |
| C1-8 `lem:admissible`(b),(c), walk criterion | done | Admissible.lean | `Admissible`, `IsWalk`, `IsWalkIn`, `IrreducibleFace`, `admissible_iff_walk`, `admissible_iff_of_irreducible`, `irreducible_of_admissible_symm` | Added hypotheses `μ ≥ 0`, `a ≥ 0`, `h > 0`, `h q_i < 1`. Walk edges require `x ≠ y`. The path need not end with a stay because a walk is itself a path of positive probability. |
| C1-8 (a) `lem:admissible`(a) | done (optional part) | AdmissibleComponents.lean | `SCC`, `LinkedChain`, `ComponentOrder`, `components_of_walk`, `cover_chain`, `admissible_iff_components` | The numbering of components is a list `Cs` of pairwise disjoint components covering `F`, first one meeting `supp μ`, consecutive ones linked by a positive rate. |
| C1-9 `lem:layer-exact-discrete` | done (optional) | LayerDiscrete.lean | `PZ`, `chainZ`, `wordZ`, `layer_exact_discrete`, `layer_coeff_zero` | `P^{(z)}_{N'}(n̂)` is a polynomial `PZ` in `z` (`Polynomial ℝ`), `c⁻_j = a_{ji}`, `c⁺_j = a_{ij}`. Hypotheses `1 ≤ n_i` and `1 ≤ N'`. The proof is by the first-step recursion of the chain (functional `Lam`), not by a bijection of words. `layer_coeff_zero`: `[z^0] P^{(z)}_{N'}(n̂) = lawP … N' n̂`. |

## Files

All under `kagey-problems/problem131/lean/`: `PaperC/C1.lean` (sub-root, imports all nine) and
`PaperC/C1/{WeightedCayley, CriticalPoint, SymFace, LayerSeries, LayerDiscrete, DiscreteRate,
DiscreteExit, Admissible, AdmissibleComponents}.lean`.

## Notes for the integration step

* Add `import PaperC.C1` to `lean/PaperC.lean`.
* `Admissible.lean`, `LayerDiscrete.lean` import `PaperC.ChainLaw`; `AdmissibleComponents.lean`
  imports `PaperC.C1.Admissible`; `SymFace.lean` imports `PaperC.C1.WeightedCayley`; the others
  import only `Mathlib`.
* Paper observation: in `lem:layer-exact-discrete` the identity needs only `n_i ≥ 1`, not
  `supp n = F`; the support condition is not used.

## Second round (coordinator's list, labels in `paperC`)

The coordinator's numbers map to these labels: Theorem 6.11 = `thm:pair-counts`, Proposition 6.2 =
`prop:layer-cubic`, Proposition 6.6 = `prop:layer-constants`, Propositions 3.5 and 3.6 =
`prop:discrete-rate` and `prop:discrete-variational`, Corollary 4.6 = `cor:reducible-crossing`.

| Item | Status | File | Theorems | Deviation / what is left out |
|---|---|---|---|---|
| 1. `thm:pair-counts`(a), discrete Pedler | done | PairCounts.lean | `pair_facet_law`, `pair_discrete_pedler`, `pairR`, `coeff_lin_pow`, `coeff_wordZ_pair` | Exact identity `P_N(n) = P_{N'}(n̂)·R` on the pair face `{j,i}` with `N' = M+1`, `n_i = m ≥ 1`; hypotheses `μ_j > 0`, `p_j > 0`, `j ≠ i`. Terms `K < e` are zero (guards `if e ≤ K`). Uses `layer_exact_discrete`. Parts (b) to (d) (kernel, error bounds) not formalized. |
| 2. `prop:layer-cubic`(e), 3-cycle | done | CubicCycle.lean | `cycleJ_d1`, `cycleJ_d2`, `cycleJ_d3`, `cycle_cubic_identity`, `cycle_kappa`, `cycle_kappa_neg` | Starts from the rate `J_G(β,z) = 3 - 2z - √((2+z)(1+4z))` given in the proof (via `lem:L-two`); that lemma itself is not formalized. Derivatives are the real ones (`deriv`), shown equal to `-ω`, `49√2/16`, `-1323√2/64`, `ω = 2 + 9√2/4`. `ϰ_β` is stated without real powers: `c/(ω√ω) + a²/(ω²√ω) = -49/(64√ω)`. |
| 3. `prop:layer-constants`(v) | direction `π_in = π_out ⇒ affine` done | FacetAffine.lean | `Psi_sub_zP`, `gradP_balance`, `facet_rate_le`, `facet_rate_affine` | Hypotheses: `r > 0` critical at `z = 0` (`hcrit`) and `π_in = π_out` in the cross-multiplied form `hπ`. Gives `J_G(β,z) = J_G(β) - zω_β` for all `z ≥ 0`, via the elementary bound `e^x ≥ 1 + x` (no concavity argument needed). The converse (affine ⇒ equal laws) uses the second derivative and the effective-resistance formula and is not done. |
| 4. `prop:discrete-rate`, `prop:discrete-variational` | selected finite parts done | DiscreteFacts.lean | `dvPhiH_term_eq`, `dvRateH_convexOn`, `dvPhiM_cw_lower`, `dvPhiM_eigen`, `dvPhiM_le_eigen`, `eigen_step` | Term identity `log(u_i/((I+hQ)u)_i) = h L_h(q_i - θ_i)`; convexity of `J^{(h)}_F` in `α`; Collatz–Wielandt lower bound and the equality case at `α* = l∘r/⟨l,r⟩` (Jensen), with the Perron vectors as hypotheses (`ϱ > 0`, positive `r`, `l`); `(I+hQ_F) r = (1-hλ) r`. Not done: strict convexity and uniqueness of the maximizer, analyticity, Hessian, 3.5(c) and the real-analytic parts of 3.6(c). |
| 5. `cor:reducible-crossing` on `ex:threecycle` | done | ThreeCycleCrossing.lean | `crossing_const_pair1`, `crossing_T_pair1`, `crossing_const_pair2`, `crossing_T_pair2`, `log_coefficients`, `sup_A2`, `stationary_cycle`, `hessian_det`, `K123_value`, `log_ratio_deriv_pos` | The corollary is used only through its formula `T = (Δ/δ)[L - (π/Δ)log L + b₀]`, `b₀ = -(π/Δ)log(Δ/δ) - κ/Δ`, with the values `Δ, δ, π, κ` of the example: coefficients 1 and 0, `b₀ = log((b-1)/b)` and `log(2√3πb²/(1+2b)²)`. Also `A_2 = b`, the stationary law, the Hessian determinant and `K_{123}`. The corollary itself and Theorem `thm:reducible` are not formalized. |

Files added in this round: `PairCounts`, `CubicCycle`, `FacetAffine`, `DiscreteFacts`,
`ThreeCycleCrossing`; the sub-root `PaperC/C1.lean` now imports fourteen modules.
