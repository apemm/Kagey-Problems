# W-C2 progress log (Paper C2, namespace `Kagey131.PaperC.C2`)

All files are in `kagey-problems/problem131/lean/PaperC/C2/`; the sub-root is
`kagey-problems/problem131/lean/PaperC/C2.lean`. Workspace `~/lean-work/w-c2`. Each file was
checked with `lake env lean "$L/PaperC/C2/<File>.lean"` (modules imported by others were first
compiled with `-R "$L" -o .lake/build/lib/lean/PaperC/C2/<File>.olean`). The sub-root compiles.
`#print axioms` on the main theorems of every file gives only `propext`, `Classical.choice`,
`Quot.sound`. No `sorry`, `native_decide`, `axiom`. No shared file was edited.

| Target | Status | File | Theorems | Deviation from the plan or paper |
|---|---|---|---|---|
| C2-1 | done | BranchSwitch.lean | branch_exit_one, branch_block_two, branch_block_23_eigen, branch_gap, branch_lt, weak_exit_one, weak_block_12_eigen, two_state_killing | eigenvalues certified by a positive eigenvector, as in `CriticalWindow`; the Perron root is not invoked |
| C2-2 | done | CutExample4.lean (+ MinorTools, TimeReversal) | cutQ_isGenerator, cutQ'_isGenerator, cutQ_factors, cutPi_pos, cutPi_sum, cutQ_stationary, cutQ'_stationary, cutC'_null, cutQ'_eq_conj, cutQ'_X, cutQ'_Y, cutStar_01, cutQ'_ne_star, cutQ'_ne_Q, cut_example_minors | minors via `pminor_eq_det_piecewise` and `det_fin_four` instead of `minorAt`/`orderEmbOfFin`; the statement is for all 16 subsets (the 15 nonempty ones and the empty one). `starMat` (general index type) replaces the three-state `timeRev` |
| C2-3 | done | MemorylessExample5.lean | memQ_isGenerator, memQB_isGenerator, memQ_exit, memQ_enter, memQ_stationary, memQB_stationary, memQB_ne_Q, memQB_ne_star, memory_example_minors | all 32 subsets (31 nonempty), via `det_fin_five` |
| C2-3b | done (extra) | MemorylessLaw.lean | memOffQB_eq, memory_example_law | the count laws of the d = 5 example agree for every N, h and composition, a consequence of C2-7(3), not only N <= 5 |
| C2-4 | done | PathReversal.lean | aRev, aRev_eq_starMat, aRev_exit, wordWt_reverse, lawP_aRev, lawP_aRev_weighted | stationarity is not needed for the path identity (any positive pi); it is used only in `aRev_exit` (the reversed chain keeps the exit rates, so P* is stochastic). The weighted law is `lawP * g n` for any `g` |
| C2-5 | done | CutTranspose.lean | cut_rows, cut_cols, cut_total, cutTranspose_null, cutPoint, cutTranspose_blocks, cutTranspose_isGenerator | `Q` and `pi` are given by row sums `∑ j Q i j = 0` and `∑ i pi i Q i j = 0`; the blocks are stated with `starMat`; needs `∑ b ≠ 0` and `c ⬝ᵥ pi_Y ≠ 0`. The generator statement also assumes `a,b,c,u ≥ 0` (a sign convention for the rank-one factors, not in the paper) |
| C2-6 | done | TimeReversalEigen.lean | starTilt_eq, starTilt_right, starTilt_left, starTilt_pairing, starTilt_amplitude | none |
| C2-7 | done, parts (1), (2), (3) | BlockSegment.lean, BlockReversal.lean, BlockReversalLaw.lean | seg_reverse (the plan's `block_segment`, on the subtype of `B`), segSum_eq_sub, maskB_vecMul, maskC_vecMul, maskB_pow, insideMass, outside_eq, pathSum_eq, memoryless_block_reversal, stepMat_aBlock, genPoly, coeff_genPoly, eval_genPoly, lawP_aBlock | `memoryless_block_reversal` as in the plan, over any field. `lawP_aBlock` is the corollary for `ChainLaw` (`lawP`), proved through the generating polynomial in `MvPolynomial (Fin d) ℝ` and `MvPolynomial.funext`; hypotheses on rates: `a i y = e y` for `i ∈ B, y ∉ B`, `a y i = c y * w i`, `μ i = m * w i` on `B`. No stochasticity or stationarity needed |
| C2-8 | done | CutTransposeMinors.lean | det_cut_unit, dense_det_ne_zero, det_cutTranspose, sumEquivS, pminor_cut, pminor_cutTranspose | the singular-`A` case uses continuity in `A + s•1` (finitely many bad `s`) rather than a polynomial identity in `s`; the statement is over `ℝ` |

Files created (all with the check command above):
BranchSwitch, MinorTools, TimeReversal, CutExample4, MemorylessExample5, MemorylessLaw,
PathReversal, CutTranspose, TimeReversalEigen, BlockSegment, BlockReversal, BlockReversalLaw,
CutTransposeMinors (each `lean/PaperC/C2/<Name>.lean`) and the sub-root `lean/PaperC/C2.lean`.

Paper issues found: none. Note for the integration step: `PaperC.C2` imports `PaperC.PrincipalMinors`,
`PaperC.GeneratorFiber` and `PaperC.ChainLaw`; scratch files live only in `~/lean-work/w-c2/scratch`.

## Second round: `sec_exactlaw.tex`

Same protocol; the sub-root `PaperC/C2.lean` now imports all modules and compiles; `#print axioms`
of the main theorems shows only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

| Item | Status | File | Theorems | Notes |
|---|---|---|---|---|
| 1. sign convention of C2-5 | done | CutTranspose.lean | exists_nonneg_factors, cutTranspose_isGenerator_of_blocks | The paper states `a,b,c,u >= 0` in the setting of `prop:gluing` and in `sec_minors.tex` before `eq:cut-transpose`: the blocks of an irreducible Metzler `Q` are nonzero, nonnegative and rank one, so nonnegative factors exist. Lean: a nonzero rank-one block with nonnegative entries has nonnegative factors (after `(a,b) -> (-a,-b)`), and the generator statement then holds from nonzero blocks alone |
| 2. gluing, balance | done | GluingCut.lean | glue_solution (first formula), starBlock_mul, starBlock_eq, star_q1, star_q2, star_beta, star_EY, glue_difference (second formula), glue_eq_iff, glue_eq_of_balanced, p1_eq_p2_memoryless | Stated for a solution `z` of `(diag x - Q) z = 1` at a point `x` (so `F_Q = pi z`), over any field, with `R_X`, `R_Y` inverses of the blocks and `1 - alpha beta != 0`. Only the algebraic direction of `cor:balance` (balanced side implies equal values, and the pointwise iff) is formalized; passing from points to rational functions (integral domain) and the use of `thm:one-horizon` are not. `rem:memoryless-cut`: `p_1 = p_2` for `a = 1`, `u = pi_X` |
| 3. `lem:graph` | done | ResultantGraph.lean | evalAt, mvPolynomial_eq_zero_of_open, dvd_of_not_coprime, graph_dvd | Stated for `P` in `MvPolynomial sigma C` adjoined with `s` (`Polynomial (MvPolynomial sigma C)`), `U` open in `R^sigma`, evaluation at `(theta w, w)`. Uses Mathlib's resultant, Bezout identity, Gauss lemma, `MvPolynomial.funext_set` |
| 4. second moments `d <= 4` | done for d = 2, 3, 4 | SecondMoments.lean, SecondMomentsFour.lean | second_moments_two, second_moments_three, second_moments_four, antisym_reduction, quad_antisym, second_moments_conclude, antisym_four, antisym_four_eq | `thm:second-moments`(i). Only `Q 1 = 0`, `pi Q = 0`, `pi > 0` are used (no Metzler hypothesis). The data are `Sigma_m = D Q^m + (D Q^m)^T` for `m = 1, 2`. The `d = 4` proof follows the paper's kernel argument in coordinates (`N = Nmat p q r`) instead of eigenplanes. Parts (ii) and (iii) not formalized |
| 5a. memoryless block | done | MemorylessBlock.lean | Memoryless (structure), flux_balance, colB, rowB, memoryless_isGenerator, memoryless_stationary, memoryless_eq_iff, memoryless_two, memoryless_eq_star, memoryless_irreducible | `thm:memoryless`: `Q^[B]` is a generator with stationary law `pi`, irreducible, equals `Q` iff `Q*_B = Q_B` (automatic for `\|B\| = 2`), equals `Q*` when `\|B^c\| = 1`. The law invariance is `lawP_aBlock` (`BlockReversalLaw`) |
| 5b. `rem:one-N` | done | OneN.lean | sum_choose_weighted, lawP_two_symm, circQ_isGenerator, circQ_law_two, circQ_star, circQ_ne, circQ_ne_star | the counting identity, and the 3-state circulation example: the `N = 2` law does not depend on `k`, `Q_k* = Q_{-k}` |
| 5c. stationary-law converse | done | StationaryConverse.lean | diag_sub_star, inv_star, F_star | `F_{Q*}(x) = F_Q(x)` wherever `diag x - Q` is invertible |

Not formalized (judged out of reach or analytic): `lem:reductions` (Laplace transform and series), `thm:one-horizon`,
`thm:generic-start`, `rem:balance-necessary` (expansion in `1/x`), `thm:second-moments`(ii),(iii),
`rem:memoryless-cut` beyond `p_1 = p_2`.
