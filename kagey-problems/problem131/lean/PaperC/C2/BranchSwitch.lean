import Mathlib

/-!
# Paper C2: the branch-switch example and the weak-criterion example

Paper C2 (`paperC2/problem131_reconstruction.tex`), Section 6 (`paperC2/sec_lowtemp.tex`):
Example `ex:branch-switch` (a branch switch), the example of three states with all costs `1`
after Theorem `thm:cycles-from-depths` (the weak form of the cycle criterion fails), and the
two-state killing identity used before Theorem `thm:attraction`.

States `1, 2, 3` of the paper are `0, 1, 2` in Lean. A killed block on a face `F` is the
principal submatrix of `-Q`, and a rate is an exit rate `λ_F` when a positive vector is an
eigenvector of the killed block for it. The Perron and Frobenius theorem is not used: each
eigenvalue is certified by an explicit positive eigenvector, as in `CriticalWindow`.

Proved here, with `t > 0`:

* `branch_exit_one`, `branch_block_two`, `branch_block_three`, `branch_block_23_eigen`: for
  `q_12 = q_13 = t³`, `q_21 = q_31 = t⁵`, `q_23 = q_32 = t`, the exit rate of `{1}` is `2t³`,
  those of `{2}` and `{3}` are `t + t⁵`, and the killed block on `{2,3}` has the positive
  eigenvector `(1,1)` for `t⁵`;
* `branch_gap`: `t + t⁵ - 2t³ = t (1 - t²)²`, and `branch_lt`: `2t³ < t + t⁵` for `0 < t < 1`;
* `weak_exit_one`, `weak_block_12_eigen`: for three states with all rates `t`, the exit rate of
  `{1}` is `2t` and the killed block on `{1,2}` has the positive eigenvector `(1,1)` for `t`;
* `two_state_killing`: if `λ` is a root of `(q_12 - λ)(q_21 + K - λ) = q_12 q_21` and
  `q_21 + K - λ ≠ 0`, then `q_12 - λ = q_12 q_21 / (q_21 + K - λ)`.
-/

namespace Kagey131.PaperC.C2

open Matrix

noncomputable section

/-- The off-diagonal rates of `ex:branch-switch`: `q_12 = q_13 = t³`, `q_21 = q_31 = t⁵`,
`q_23 = q_32 = t`. -/
def branchOff (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, t ^ 3, t ^ 3; t ^ 5, 0, t; t ^ 5, t, 0]

/-- The generator of `ex:branch-switch`. -/
def branchQ (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i = j then -(∑ k, branchOff t i k) else branchOff t i j

/-- The rows of the branch-switch generator sum to zero. -/
theorem branchQ_rowsum (t : ℝ) (i : Fin 3) : ∑ j, branchQ t i j = 0 := by
  fin_cases i <;> simp [branchQ, branchOff, Fin.sum_univ_three]

/-- The exit rate of `{1}` is `2t³`, so `λ_{1} = 2t³` (`ex:branch-switch`). -/
theorem branch_exit_one (t : ℝ) : -branchQ t 0 0 = 2 * t ^ 3 := by
  simp [branchQ, branchOff, Fin.sum_univ_three]; ring

/-- The exit rates of `{2}` and `{3}` are `t + t⁵`, so `λ_{2} = λ_{3} = t + t⁵`
(`ex:branch-switch`). -/
theorem branch_block_two (t : ℝ) :
    -branchQ t 1 1 = t + t ^ 5 ∧ -branchQ t 2 2 = t + t ^ 5 := by
  constructor <;> simp [branchQ, branchOff, Fin.sum_univ_three] <;> ring

/-- The killed block `-Q_{23}` on `{2,3}`. -/
def branchBlock (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![t + t ^ 5, -t; -t, t + t ^ 5]

/-- `branchBlock` is the principal block of `-Q` on `{2,3}`. -/
theorem branchBlock_eq (t : ℝ) :
    branchBlock t = (-branchQ t).submatrix (fun i : Fin 2 => i.succ) (fun i : Fin 2 => i.succ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [branchBlock, branchQ, branchOff, Fin.sum_univ_three]
    <;> ring

/-- `ex:branch-switch`: the killed block on `{2,3}` has the positive eigenvector `(1,1)` for
the eigenvalue `t⁵`, so `λ_{2,3} = t⁵`. -/
theorem branch_block_23_eigen (t : ℝ) :
    branchBlock t *ᵥ ![1, 1] = t ^ 5 • ![1, 1] := by
  ext i
  fin_cases i <;> simp [branchBlock, mulVec, dotProduct, Fin.sum_univ_two]

/-- `ex:branch-switch`: `t + t⁵ - 2t³ = t (1 - t²)²`. -/
theorem branch_gap (t : ℝ) : t + t ^ 5 - 2 * t ^ 3 = t * (1 - t ^ 2) ^ 2 := by ring

/-- `ex:branch-switch`: `2t³ < t + t⁵` for `0 < t < 1`, so `λ_{1} < λ_{2}`. -/
theorem branch_lt {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 2 * t ^ 3 < t + t ^ 5 := by
  have : 0 < t * (1 - t ^ 2) ^ 2 := by
    have : 0 < 1 - t ^ 2 := by nlinarith
    positivity
  nlinarith [branch_gap t]

/-- The generator of three states with all rates `t`. -/
def weakQ (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i = j then -2 * t else t

/-- Example after `thm:cycles-from-depths`: the exit rate of `{1}` is `2t`. -/
theorem weak_exit_one (t : ℝ) : -weakQ t 0 0 = 2 * t := by simp [weakQ]

/-- The killed block `-Q_{12}` on `{1,2}` for the weak-criterion example. -/
def weakBlock (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * t, -t; -t, 2 * t]

/-- `weakBlock` is the principal block of `-Q` on `{1,2}`. -/
theorem weakBlock_eq (t : ℝ) :
    weakBlock t = (-weakQ t).submatrix (fun i : Fin 2 => i.castSucc) (fun i : Fin 2 => i.castSucc) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weakBlock, weakQ]

/-- Example after `thm:cycles-from-depths`: the killed block on `{1,2}` has the positive
eigenvector `(1,1)` for `t`, so `λ_{1,2} = t`. -/
theorem weak_block_12_eigen (t : ℝ) :
    weakBlock t *ᵥ ![1, 1] = t • ![1, 1] := by
  ext i
  fin_cases i <;> simp [weakBlock, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The two-state killing identity before `thm:attraction`: a root `λ` of
`(q₁₂ - λ)(q₂₁ + K - λ) = q₁₂ q₂₁` with `q₂₁ + K - λ ≠ 0` satisfies
`q₁₂ - λ = q₁₂ q₂₁ / (q₂₁ + K - λ)`. -/
theorem two_state_killing {q12 q21 K lam : ℝ}
    (hroot : (q12 - lam) * (q21 + K - lam) = q12 * q21) (hne : q21 + K - lam ≠ 0) :
    q12 - lam = q12 * q21 / (q21 + K - lam) := by
  rw [eq_div_iff hne]; exact hroot

end

end Kagey131.PaperC.C2
