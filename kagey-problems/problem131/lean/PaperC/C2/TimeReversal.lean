import Mathlib
import PaperC.GeneratorFiber

/-!
# Paper C2: the time reversal on any finite state space

Paper C2 (`paperC2/sec_minors.tex`), Corollary `thm:nonreversible` and Remark `rem:stationary`.
`PaperC.GeneratorFiber` defines the time reversal `Q*` for three states only. Here it is defined
for any finite index type, with the same formula `Q*_ij = π_j Q_ji / π_i`.

* `starMat_eq_conj`: `Q* = D_π⁻¹ Qᵀ D_π`;
* `starMat_diag`: `Q*` has the diagonal of `Q`;
* `starMat_isGenerator`: for `π > 0` with `π Q = 0` and `Q` a generator, `Q*` is a generator.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Kagey131.PaperC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The time reversal `Q*_ij = π_j Q_ji / π_i`. -/
noncomputable def starMat (π : ι → ℝ) (Q : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => π j * Q j i / π i

/-- `Q* = D_π⁻¹ Qᵀ D_π`. -/
theorem starMat_eq_conj (π : ι → ℝ) (Q : Matrix ι ι ℝ) :
    starMat π Q = diagonal (fun i => (π i)⁻¹) * Qᵀ * diagonal π := by
  ext i j
  rw [conj_apply, transpose_apply, starMat]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The time reversal has the diagonal of `Q`. -/
theorem starMat_diag {π : ι → ℝ} (hπ : ∀ i, 0 < π i) (Q : Matrix ι ι ℝ) (i : ι) :
    starMat π Q i i = Q i i := by
  have := (hπ i).ne'
  simp [starMat]; field_simp

omit [DecidableEq ι] in
/-- If `Q` is a generator with a positive stationary vector `π`, then `Q*` is a generator. -/
theorem starMat_isGenerator {π : ι → ℝ} (hπ : ∀ i, 0 < π i) {Q : Matrix ι ι ℝ}
    (hQ : IsGenerator Q) (hstat : π ᵥ* Q = 0) : IsGenerator (starMat π Q) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · exact div_nonneg (mul_nonneg (hπ j).le (hQ.1 j i (Ne.symm hij))) (hπ i).le
  · have h : ∑ j, π j * Q j i = 0 := by
      have := congrFun hstat i
      simpa [vecMul, dotProduct] using this
    simp only [starMat, ← Finset.sum_div, h, zero_div]

end Kagey131.PaperC.C2
