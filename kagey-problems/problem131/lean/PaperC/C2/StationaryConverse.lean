import Mathlib
import PaperC.C2.TimeReversal

/-!
# Paper C2: the stationary law of the time reversal

Paper C2 (`paperC2/sec_exactlaw.tex`), Theorem `thm:stationary-law`, the converse: for `Q*`,
`F_{Q*}(x) = π (diag x - Q*)⁻¹ 1 = F_Q(x)`, so `O(T)` has the same stationary law under `Q` and
`Q*` for every `T`. Proved at every `x` where `diag x - Q` is invertible.

* `inv_star`: `(diag x - Q*)⁻¹ = D⁻¹ ((diag x - Q)⁻¹)ᵀ D`;
* `F_star`: `π (diag x - Q*)⁻¹ 1 = π (diag x - Q)⁻¹ 1`.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `diag x - Q*` is `D⁻¹ (diag x - Q)ᵀ D`. -/
theorem diag_sub_star {π : ι → ℝ} (hπ : ∀ i, 0 < π i) (x : ι → ℝ) (Q : Matrix ι ι ℝ) :
    diagonal x - starMat π Q
      = diagonal (fun i => (π i)⁻¹) * (diagonal x - Q)ᵀ * diagonal π := by
  have hDi : diagonal (fun i => (π i)⁻¹) * diagonal π = (1 : Matrix ι ι ℝ) := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; have := (hπ i).ne'; simp [this]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have hcomm : diagonal (fun i => (π i)⁻¹) * diagonal x * diagonal π = diagonal x := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; have := (hπ i).ne'; simp; field_simp
    · simp [diagonal_apply_ne _ hij]
  rw [transpose_sub, diagonal_transpose, starMat_eq_conj]
  rw [Matrix.mul_sub, Matrix.sub_mul, hcomm]

/-- The inverse of `diag x - Q*`. -/
theorem inv_star {π : ι → ℝ} (hπ : ∀ i, 0 < π i) (x : ι → ℝ) (Q : Matrix ι ι ℝ)
    (hM : IsUnit (diagonal x - Q).det) :
    (diagonal x - starMat π Q)⁻¹
      = diagonal (fun i => (π i)⁻¹) * ((diagonal x - Q)⁻¹)ᵀ * diagonal π := by
  have hDi : diagonal (fun i => (π i)⁻¹) * diagonal π = (1 : Matrix ι ι ℝ) := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; have := (hπ i).ne'; simp [this]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have hDi' : diagonal π * diagonal (fun i => (π i)⁻¹) = (1 : Matrix ι ι ℝ) := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; have := (hπ i).ne'; simp [this]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  set M := diagonal x - Q
  have hN : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hM
  refine Matrix.inv_eq_right_inv ?_
  rw [diag_sub_star hπ]
  calc diagonal (fun i => (π i)⁻¹) * Mᵀ * diagonal π
        * (diagonal (fun i => (π i)⁻¹) * (M⁻¹)ᵀ * diagonal π)
      = diagonal (fun i => (π i)⁻¹) * (Mᵀ * (diagonal π * diagonal (fun i => (π i)⁻¹)) * (M⁻¹)ᵀ)
          * diagonal π := by simp only [Matrix.mul_assoc]
    _ = diagonal (fun i => (π i)⁻¹) * (M⁻¹ * M)ᵀ * diagonal π := by
        rw [hDi', Matrix.mul_one, transpose_mul]
    _ = 1 := by rw [hN, transpose_one, Matrix.mul_one, hDi]

/-- `thm:stationary-law`, converse: `F_{Q*}(x) = F_Q(x)` wherever `diag x - Q` is invertible. -/
theorem F_star {π : ι → ℝ} (hπ : ∀ i, 0 < π i) (x : ι → ℝ) (Q : Matrix ι ι ℝ)
    (hM : IsUnit (diagonal x - Q).det) :
    π ⬝ᵥ ((diagonal x - starMat π Q)⁻¹ *ᵥ fun _ => (1 : ℝ))
      = π ⬝ᵥ ((diagonal x - Q)⁻¹ *ᵥ fun _ => (1 : ℝ)) := by
  rw [inv_star hπ x Q hM]
  set N := (diagonal x - Q)⁻¹
  have e1 : (diagonal (fun i => (π i)⁻¹) * Nᵀ * diagonal π) *ᵥ (fun _ => (1 : ℝ))
      = diagonal (fun i => (π i)⁻¹) *ᵥ (Nᵀ *ᵥ π) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    congr 2
    ext i; simp [mulVec_diagonal]
  rw [e1, dotProduct_mulVec]
  have e2 : π ᵥ* diagonal (fun i => (π i)⁻¹) = fun _ => (1 : ℝ) := by
    ext i; have := (hπ i).ne'; simp [vecMul_diagonal, this]
  rw [e2, mulVec_transpose]
  -- `1 ⬝ᵥ (π ᵥ* N) = π ⬝ᵥ (N *ᵥ 1)`
  simp only [dotProduct, vecMul, mulVec, one_mul, mul_one]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => by rw [Finset.mul_sum]

end Kagey131.PaperC.C2
