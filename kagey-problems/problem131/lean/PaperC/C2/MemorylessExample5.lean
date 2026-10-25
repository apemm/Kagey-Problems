import Mathlib
import PaperC.GeneratorFiber
import PaperC.C2.MinorTools
import PaperC.C2.TimeReversal

/-!
# Paper C2: a five-state generator with the same minors, a third generator

The `d = 5` example of a memoryless block (research note `Paper C2 identifiability O1`,
Corollary 7), which shows that the principal minors, and even the stationary law of the counts,
do not separate `Q` from a third generator. It complements the fiber description of
Corollary `thm:nonreversible` of Paper C2 (`paperC2/sec_minors.tex`).

States `0, 1, 2` form the block `B`; `3` and `4` are the outside states. The off-diagonal rates
are `q_01 = q_12 = q_20 = 2`, `q_10 = q_21 = q_02 = 1`; every `i ∈ B` goes to `3` at rate `1`
and to `4` at rate `2`; `3` goes to every `i ∈ B` at rate `1`, `4` at rate `2`; `q_34 = 1`,
`q_43 = 4`. The stationary law is `π = (4, 4, 4, 6, 3)/21`, uniform on `B`. `Q^[B]` is `Q` with
the `3 × 3` block on `B` transposed.

Everything is over `ℝ` with exact entries. Proved here:

* `memQ_isGenerator`, `memQB_isGenerator`: both are generators;
* `memQ_exit`, `memQ_enter`: every `i ∈ B` has the exit row `(1, 2)` outside `B`, and every
  outside state enters `B` proportionally to the uniform weight (rates `1` from `3`, `2` from `4`);
* `memPi_pos`, `memPi_sum`, `memQ_stationary`, `memQB_stationary`: `π` is a positive
  probability vector with `π Q = 0` and `π Q^[B] = 0`;
* `memQB_ne_Q`, `memQB_ne_star`: `Q^[B] ≠ Q` and `Q^[B] ≠ Q*`;
* `memory_example_minors`: all thirty-two principal minors of `-Q^[B]` and `-Q` agree (the
  thirty-one nonempty ones, and the empty minor `1`).
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Kagey131.PaperC

noncomputable section

/-- The off-diagonal rates of the memoryless-block example. -/
def memOff : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 2, 1, 1, 2; 1, 0, 2, 1, 2; 2, 1, 0, 1, 2; 1, 1, 1, 0, 1; 2, 2, 2, 4, 0]

/-- The generator `Q`: the off-diagonal rates, with the diagonal minus the row sum. -/
def memQ : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => if i = j then -(∑ k, memOff i k) else memOff i j

/-- `Q^[B]`: `Q` with the `3 × 3` block on `B = {0,1,2}` transposed, `Q^[B]_ij = π_j Q_ji / π_i`
on `B` with `π` uniform on `B`. -/
def memQB : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => if i.val < 3 ∧ j.val < 3 then memQ j i else memQ i j

/-- `Q` as an explicit matrix. -/
theorem memQ_eq : memQ =
    !![-6, 2, 1, 1, 2; 1, -6, 2, 1, 2; 2, 1, -6, 1, 2; 1, 1, 1, -4, 1; 2, 2, 2, 4, -10] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [memQ, memOff, Fin.sum_univ_five] <;> norm_num

/-- `Q^[B]` as an explicit matrix. -/
theorem memQB_eq : memQB =
    !![-6, 1, 2, 1, 2; 2, -6, 1, 1, 2; 1, 2, -6, 1, 2; 1, 1, 1, -4, 1; 2, 2, 2, 4, -10] := by
  ext i j
  rw [memQB]
  fin_cases i <;> fin_cases j <;> simp [memQ_eq]

/-- The stationary law `π = (4, 4, 4, 6, 3)/21`. -/
def memPi : Fin 5 → ℝ := fun i => ![4, 4, 4, 6, 3] i / 21

theorem memQ_isGenerator : IsGenerator memQ := by
  rw [memQ_eq]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · fin_cases i <;> simp [Fin.sum_univ_five] <;> norm_num

theorem memQB_isGenerator : IsGenerator memQB := by
  rw [memQB_eq]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · fin_cases i <;> simp [Fin.sum_univ_five] <;> norm_num

/-- Every state of the block `B` has the same exit row outside `B`, `(Q_i3, Q_i4) = (1, 2)`. -/
theorem memQ_exit (i : Fin 5) (hi : i.val < 3) : memQ i 3 = 1 ∧ memQ i 4 = 2 := by
  rw [memQ_eq]
  fin_cases i <;> simp at hi ⊢

/-- Every outside state enters `B` at a rate that does not depend on the state of `B`:
`Q_3i = 1` and `Q_4i = 2`, that is `c_y w_i` with `w` uniform on `B`. -/
theorem memQ_enter (i : Fin 5) (hi : i.val < 3) : memQ 3 i = 1 ∧ memQ 4 i = 2 := by
  rw [memQ_eq]
  fin_cases i <;> simp at hi ⊢

theorem memPi_pos (i : Fin 5) : 0 < memPi i := by
  fin_cases i <;> simp [memPi]

theorem memPi_sum : ∑ i, memPi i = 1 := by
  simp [memPi, Fin.sum_univ_five]; norm_num

/-- `π Q = 0`. -/
theorem memQ_stationary : memPi ᵥ* memQ = 0 := by
  rw [memQ_eq]
  ext j
  fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_five, memPi] <;> norm_num

/-- `π Q^[B] = 0`. -/
theorem memQB_stationary : memPi ᵥ* memQB = 0 := by
  rw [memQB_eq]
  ext j
  fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_five, memPi] <;> norm_num

/-- `Q^[B] ≠ Q`: the entries `(0,1)` are `1` and `2`. -/
theorem memQB_ne_Q : memQB ≠ memQ := by
  intro h
  have := congrFun (congrFun h 0) 1
  rw [memQB_eq, memQ_eq] at this
  simp at this

/-- `Q^[B] ≠ Q*`: the entries `(0,3)` are `1` and `π₃ Q_30/π₀ = 3/2`. -/
theorem memQB_ne_star : memQB ≠ starMat memPi memQ := by
  intro h
  have := congrFun (congrFun h 0) 3
  rw [memQB_eq, starMat, memQ_eq] at this
  simp [memPi] at this
  norm_num at this

set_option maxHeartbeats 4000000 in
/-- The memoryless-block example: `Q^[B]` has all the principal minors of `-Q`. -/
theorem memory_example_minors : ∀ S : Finset (Fin 5), pminor (-memQB) S = pminor (-memQ) S := by
  rw [memQ_eq, memQB_eq]
  intro S
  fin_cases S
  all_goals rw [pminor_eq_det_piecewise, pminor_eq_det_piecewise, det_fin_five, det_fin_five]
  all_goals simp [det4Expr]
  all_goals norm_num

end

end Kagey131.PaperC.C2
