import Mathlib
import PaperC.C2.TimeReversal

/-!
# Paper C2: eigenvectors of the tilted time reversal and the amplitude at the stationary start

Paper C2 (`paperC2/sec_minors.tex`), Proposition `prop:amplitudes`(b), the last paragraph of the
proof. For a tilt `v`, the matrix `Q* + diag v` is `D_π⁻¹ (Q + diag v)ᵀ D_π`. If `r` and `l` are
right and left eigenvectors of `Q + diag v` for the same eigenvalue `θ`, with `l·r = 1`, then
`r* = D_π⁻¹ l` and `l* = D_π r` are right and left eigenvectors of `Q* + diag v`, for the same
eigenvalue, with `l*·r* = 1`, and at the start `π` the amplitudes agree.

* `starTilt_eq`: `Q* + diag v = D_π⁻¹ (Q + diag v)ᵀ D_π`;
* `starTilt_right`, `starTilt_left`: the eigenvector equations for `r*` and `l*`;
* `starTilt_pairing`: `l*·r* = l·r`;
* `starTilt_amplitude`: `(π·r*)(l*·1) = (π·r)(l·1)`.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Q* + diag v = D_π⁻¹ (Q + diag v)ᵀ D_π`. -/
theorem starTilt_eq {π : ι → ℝ} (hπ : ∀ i, 0 < π i) (Q : Matrix ι ι ℝ) (v : ι → ℝ) :
    starMat π Q + diagonal v
      = diagonal (fun i => (π i)⁻¹) * (Q + diagonal v)ᵀ * diagonal π := by
  ext i j
  have hi := (hπ i).ne'
  by_cases hij : i = j
  · subst hij
    simp [starMat]
    field_simp
  · simp [starMat, hij, transpose_apply]
    field_simp

/-- The right eigenvector of the tilted time reversal: `r* = D_π⁻¹ l`. -/
theorem starTilt_right {π : ι → ℝ} (hπ : ∀ i, 0 < π i) (Q : Matrix ι ι ℝ) (v l : ι → ℝ) (θ : ℝ)
    (hl : l ᵥ* (Q + diagonal v) = θ • l) :
    (starMat π Q + diagonal v) *ᵥ (fun i => l i / π i) = θ • (fun i => l i / π i) := by
  rw [starTilt_eq hπ]
  have e : (fun i => l i / π i) = diagonal (fun i => (π i)⁻¹) *ᵥ l := by
    ext i; simp [mulVec_diagonal, div_eq_inv_mul]
  have e2 : diagonal π *ᵥ (fun i => l i / π i) = l := by
    ext i; have := (hπ i).ne'; simp [mulVec_diagonal]; field_simp
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [e2, mulVec_transpose, hl, mulVec_smul, ← e]

/-- The left eigenvector of the tilted time reversal: `l* = D_π r`. -/
theorem starTilt_left {π : ι → ℝ} (hπ : ∀ i, 0 < π i) (Q : Matrix ι ι ℝ) (v r : ι → ℝ) (θ : ℝ)
    (hr : (Q + diagonal v) *ᵥ r = θ • r) :
    (fun i => π i * r i) ᵥ* (starMat π Q + diagonal v) = θ • (fun i => π i * r i) := by
  rw [starTilt_eq hπ]
  have e : (fun i => π i * r i) = diagonal π *ᵥ r := by
    ext i; simp [mulVec_diagonal]
  have e2 : (fun i => π i * r i) ᵥ* diagonal (fun i => (π i)⁻¹) = r := by
    ext i; have := (hπ i).ne'; simp [vecMul_diagonal]; field_simp
  rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, e2, vecMul_transpose, hr,
    smul_vecMul]
  ext i
  simp [vecMul_diagonal]
  left; ring

omit [DecidableEq ι] in
/-- The pairing is preserved: `l*·r* = l·r`. -/
theorem starTilt_pairing {π : ι → ℝ} (hπ : ∀ i, 0 < π i) (r l : ι → ℝ) :
    (fun i => π i * r i) ⬝ᵥ (fun i => l i / π i) = l ⬝ᵥ r := by
  simp only [dotProduct]
  refine sum_congr rfl fun i _ => ?_
  have := (hπ i).ne'
  field_simp

omit [DecidableEq ι] in
/-- At the stationary start the amplitudes agree: `(π·r*)(l*·1) = (π·r)(l·1)`. -/
theorem starTilt_amplitude {π : ι → ℝ} (hπ : ∀ i, 0 < π i) (r l : ι → ℝ) :
    (π ⬝ᵥ (fun i => l i / π i)) * ((fun i => π i * r i) ⬝ᵥ (fun _ => (1 : ℝ)))
      = (π ⬝ᵥ r) * (l ⬝ᵥ (fun _ => (1 : ℝ))) := by
  have h1 : π ⬝ᵥ (fun i => l i / π i) = l ⬝ᵥ (fun _ => (1 : ℝ)) := by
    simp only [dotProduct, mul_one]
    refine sum_congr rfl fun i _ => ?_
    have := (hπ i).ne'
    field_simp
  have h2 : (fun i => π i * r i) ⬝ᵥ (fun _ => (1 : ℝ)) = π ⬝ᵥ r := by
    simp [dotProduct]
  rw [h1, h2]; ring

end Kagey131.PaperC.C2
