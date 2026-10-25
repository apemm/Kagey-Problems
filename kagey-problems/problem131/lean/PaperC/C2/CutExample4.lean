import Mathlib
import PaperC.GeneratorFiber
import PaperC.C2.MinorTools
import PaperC.C2.TimeReversal

/-!
# Paper C2: the four-state cut-transpose example

Paper C2 (`paperC2/problem131_reconstruction.tex`), Section 3.3 (`paperC2/sec_minors.tex`), the
worked example after Corollary `thm:nonreversible` (it carries no label): `d = 4`,
`X = {1,2}`, `Y = {3,4}` (states `0, 1, 2, 3` in Lean), and the generator `Q` below, whose
off-diagonal blocks have rank one. The generator point `Q'` of the cut-transpose of `-Q` across
`X` has the same principal minors as `-Q`, agrees with `Q` on `X`, agrees with the time
reversal `Q*` on `Y`, and is neither `Q` nor `Q*`.

Everything is over `ℝ` with exact rational entries. Proved here:

* `cutQ_isGenerator`, `cutQ'_isGenerator`: both matrices are generators;
* `cutQ_factors`: `Q[X,Y] = (1,2)ᵀ (1,3)` and `Q[Y,X] = (2,1)ᵀ (1,1)`;
* `cutPi_pos`, `cutPi_sum`, `cutQ_stationary`, `cutQ'_stationary`: `π = (2226, 1134, 2675, 3638)/9673`
  is a positive probability vector with `π Q = 0` and `π Q' = 0`;
* `cutC'_null`, `cutQ'_eq_conj`: with the cut-transpose `C'` of `C = -Q` (blocks `-a cᵀ` and
  `-b uᵀ` for `a = (1,2)`, `b = (1,3)`, `c = (2,1)`, `u = (1,1)`, and `-Q[Y,Y]ᵀ`), the vector
  `x = (1, 1, s₀ π_Y)` with `s₀ = (b·1)/(c·π_Y)` is a null vector of `C'` and
  `Q' = -D_x⁻¹ C' D_x`;
* `cutQ'_X`, `cutQ'_Y`: `Q'` agrees with `Q` on `X` and with `Q*` on `Y`;
* `cutQ'_ne_star`: `Q' ≠ Q*`, since `Q'_{12} = 7/10` and `Q*_{12} = 351/530`;
* `cut_example_minors`: `det (-Q')_S = det (-Q)_S` for all sixteen subsets `S`, so the
  fifteen nonempty principal minors agree (the empty minor is `1`).
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Kagey131.PaperC

noncomputable section

/-- The generator `Q` of the `d = 4` example. -/
def cutQ : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-47/10, 7/10, 1, 3; 13/10, -93/10, 2, 6; 2, 2, -22/5, 2/5; 1, 1, 2, -4]

/-- The generator point `Q'` of the cut-transpose of `-Q` across `X = {1,2}`. -/
def cutQ' : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-47/10, 7/10, 50/21, 34/21; 13/10, -93/10, 100/21, 68/21;
    21/25, 21/25, -22/5, 68/25; 63/34, 63/34, 5/17, -4]

/-- The stationary law `π = (2226, 1134, 2675, 3638)/9673` of `Q` and of `Q'`. -/
def cutPi : Fin 4 → ℝ := fun i => ![2226, 1134, 2675, 3638] i / 9673

theorem cutQ_isGenerator : IsGenerator cutQ := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [cutQ] at hij ⊢ <;> norm_num
  · fin_cases i <;> simp [cutQ, Fin.sum_univ_four] <;> norm_num

theorem cutQ'_isGenerator : IsGenerator cutQ' := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [cutQ'] at hij ⊢ <;> norm_num
  · fin_cases i <;> simp [cutQ', Fin.sum_univ_four] <;> norm_num

set_option linter.unnecessarySeqFocus false in
/-- The blocks of `Q` have rank one: `Q[X,Y] = (1,2)ᵀ (1,3)` and `Q[Y,X] = (2,1)ᵀ (1,1)`. -/
theorem cutQ_factors (i j : Fin 2) :
    cutQ i.castSucc.castSucc j.succ.succ = ![1, 2] i * ![1, 3] j ∧
    cutQ i.succ.succ j.castSucc.castSucc = ![2, 1] i * ![1, 1] j := by
  fin_cases i <;> fin_cases j <;> simp [cutQ] <;> norm_num

theorem cutPi_pos (i : Fin 4) : 0 < cutPi i := by
  fin_cases i <;> simp [cutPi]

theorem cutPi_sum : ∑ i, cutPi i = 1 := by
  simp [cutPi, Fin.sum_univ_four]; norm_num

/-- `π Q = 0`. -/
theorem cutQ_stationary : cutPi ᵥ* cutQ = 0 := by
  ext j
  fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_four, cutPi, cutQ] <;> norm_num

/-- `π Q' = 0`. -/
theorem cutQ'_stationary : cutPi ᵥ* cutQ' = 0 := by
  ext j
  fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_four, cutPi, cutQ'] <;> norm_num

/-- The cut-transpose `C'` of `C = -Q` across `X`, with `C[X,Y] = -a bᵀ`, `C[Y,X] = -c uᵀ`
for `a = (1,2)`, `b = (1,3)`, `c = (2,1)`, `u = (1,1)`: its blocks are `-Q[X,X]`,
`-a cᵀ`, `-b uᵀ` and `-Q[Y,Y]ᵀ`. -/
def cutC' : Matrix (Fin 4) (Fin 4) ℝ :=
  !![47/10, -7/10, -2, -1; -13/10, 93/10, -4, -2; -1, -1, 22/5, -2; -3, -3, -2/5, 4]

/-- The scalar `s₀ = (b·1)/(c·π_Y)`. -/
def cutS0 : ℝ := (1 + 3) / (2 * cutPi 2 + 1 * cutPi 3)

/-- The null vector `x = (1, 1, s₀ π₃, s₀ π₄)` of the cut-transpose. -/
def cutX : Fin 4 → ℝ := ![1, 1, cutS0 * cutPi 2, cutS0 * cutPi 3]

theorem cutX_pos (i : Fin 4) : 0 < cutX i := by
  have hs : 0 < cutS0 := by
    unfold cutS0
    have := cutPi_pos 2
    have := cutPi_pos 3
    positivity
  fin_cases i <;> simp [cutX, mul_pos hs (cutPi_pos 2), mul_pos hs (cutPi_pos 3)]

/-- `C' x = 0`. -/
theorem cutC'_null : cutC' *ᵥ cutX = 0 := by
  have h : cutS0 = 4 * 9673 / 8988 := by
    simp [cutS0, cutPi]; norm_num
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four, cutC', cutX, h, cutPi] <;> norm_num

/-- The generator point of the cut-transpose: `Q' = -D_x⁻¹ C' D_x`. -/
theorem cutQ'_eq_conj : cutQ' = -(diagonal (fun i => (cutX i)⁻¹) * cutC' * diagonal cutX) := by
  have h : cutS0 = 4 * 9673 / 8988 := by
    simp [cutS0, cutPi]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cutC', cutQ', cutX, h, cutPi] <;> norm_num

/-- `Q'` agrees with `Q` on `X`. -/
theorem cutQ'_X (i j : Fin 2) :
    cutQ' i.castSucc.castSucc j.castSucc.castSucc = cutQ i.castSucc.castSucc j.castSucc.castSucc := by
  fin_cases i <;> fin_cases j <;> simp [cutQ, cutQ']

/-- `Q'` agrees with the time reversal `Q*` on `Y`. -/
theorem cutQ'_Y (i j : Fin 2) :
    cutQ' i.succ.succ j.succ.succ = starMat cutPi cutQ i.succ.succ j.succ.succ := by
  fin_cases i <;> fin_cases j <;> simp [starMat, cutQ, cutQ', cutPi] <;> norm_num

/-- `Q*_{12} = 351/530`. -/
theorem cutStar_01 : starMat cutPi cutQ 0 1 = 351 / 530 := by
  simp [starMat, cutQ, cutPi]; norm_num

/-- `Q' ≠ Q*`: the entries `(1,2)` are `7/10` and `351/530`. -/
theorem cutQ'_ne_star : cutQ' ≠ starMat cutPi cutQ := by
  intro h
  have := congrFun (congrFun h 0) 1
  rw [cutStar_01] at this
  simp [cutQ'] at this
  norm_num at this

/-- `Q' ≠ Q`: the entries `(1,3)` are `50/21` and `1`. -/
theorem cutQ'_ne_Q : cutQ' ≠ cutQ := by
  intro h
  have := congrFun (congrFun h 0) 2
  simp [cutQ, cutQ'] at this
  norm_num at this

/-- `Q* ≠ Q` for this example. -/
theorem cutStar_ne_Q : starMat cutPi cutQ ≠ cutQ := by
  intro h
  have := congrFun (congrFun h 0) 1
  rw [cutStar_01] at this
  simp [cutQ] at this
  norm_num at this

set_option maxHeartbeats 1000000 in
/-- The worked example after Corollary `thm:nonreversible`: `Q'` has all the principal minors
of `-Q`. For every subset `S` of the four states, `det (-Q')_S = det (-Q)_S`. -/
theorem cut_example_minors : ∀ S : Finset (Fin 4), pminor (-cutQ') S = pminor (-cutQ) S := by
  intro S
  fin_cases S
  all_goals rw [pminor_eq_det_piecewise, pminor_eq_det_piecewise, det_fin_four, det_fin_four]
  all_goals simp [cutQ, cutQ']
  all_goals norm_num

end

end Kagey131.PaperC.C2
