import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-!
# The final change of variables in the curvature integral

The Jacobian is derived from the differential equation for H. Its powers
cancel to the weight `sqrt y * H y ^ (2 - 3*a)`. The integral substitution
uses an injective chart onto the positive half-line, not an assumed integral
identity.
-/

open Set MeasureTheory

namespace Kagey131.PaperD.AnalyticThresholdSubstitution

noncomputable def coordinate (a : ℝ) (H : ℝ → ℝ) (y : ℝ) : ℝ :=
  H y * y ^ (-(1 / (2 * a)))

noncomputable def secondWeight (a y : ℝ) : ℝ :=
  2 * a * y ^ (3 / (2 * a)) * Real.sqrt (1 - y) * (1 - (1 + a) ^ 2 * y)

noncomputable def curvatureWeight (a : ℝ) (H : ℝ → ℝ) (y : ℝ) : ℝ :=
  y ^ (1 / 2 : ℝ) * H y ^ (2 - 3 * a) * (1 - (1 + a) ^ 2 * y)

theorem hasDerivAt_coordinate {a y : ℝ} {H : ℝ → ℝ}
    (ha : a ≠ 0) (hy : 0 < y) (hy1 : y < 1)
    (hd : DifferentiableAt ℝ H y)
    (hode : H y - 2 * a * y * deriv H y = (Real.sqrt (1 - y))⁻¹) :
    HasDerivAt (coordinate a H)
      (-(y ^ (-(1 / (2 * a)) - 1)) / (2 * a * Real.sqrt (1 - y))) y := by
  have hs : Real.sqrt (1 - y) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hy1)).ne'
  have hr : y ^ (-(1 / (2 * a)) - 1) = y ^ (-(1 / (2 * a))) / y := by
    rw [Real.rpow_sub hy, Real.rpow_one]
  apply (hd.hasDerivAt.mul ((hasDerivAt_id y).rpow_const (Or.inl hy.ne'))).congr_deriv
  dsimp
  rw [hr]
  have hm := congrArg (fun z : ℝ => z * Real.sqrt (1 - y)) hode
  simp only [inv_mul_cancel₀ hs] at hm
  field_simp
  linear_combination -hm

theorem coordinate_deriv_neg {a y : ℝ} (ha : 0 < a) (hy : 0 < y) (hy1 : y < 1) :
    -(y ^ (-(1 / (2 * a)) - 1)) / (2 * a * Real.sqrt (1 - y)) < 0 := by
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (Real.rpow_pos_of_pos hy _))
    (mul_pos (mul_pos (by norm_num) ha) (Real.sqrt_pos.mpr (sub_pos.mpr hy1)))

theorem curvature_jacobian {a y : ℝ} {H : ℝ → ℝ}
    (ha : 0 < a) (hy : 0 < y) (hy1 : y < 1) (hH : 0 < H y) :
    |-(y ^ (-(1 / (2 * a)) - 1)) / (2 * a * Real.sqrt (1 - y))| *
      (coordinate a H y ^ (2 - 3 * a) * secondWeight a y) = curvatureWeight a H y := by
  have hs : Real.sqrt (1 - y) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hy1)).ne'
  rw [abs_of_neg (coordinate_deriv_neg ha hy hy1)]
  unfold coordinate secondWeight curvatureWeight
  rw [Real.mul_rpow hH.le (Real.rpow_nonneg hy.le _), ← Real.rpow_mul hy.le]
  have hexp : (-(1 / (2 * a)) - 1) + (-(1 / (2 * a)) * (2 - 3 * a)) +
      3 / (2 * a) = (1 / 2 : ℝ) := by field_simp; ring
  have hp : y ^ (-(1 / (2 * a)) - 1) * y ^ (-(1 / (2 * a)) * (2 - 3 * a)) *
      y ^ (3 / (2 * a)) = y ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hy, ← Real.rpow_add hy, hexp]
  calc
    _ = (y ^ (-(1 / (2 * a)) - 1) * y ^ (-(1 / (2 * a)) * (2 - 3 * a)) *
        y ^ (3 / (2 * a))) * H y ^ (2 - 3 * a) * (1 - (1 + a)^2*y) := by
      field_simp
    _ = _ := by rw [hp]

/-- The positive half-line integral is the manuscript's finite weighted
integral. The derivative and Jacobian are computed above. -/
theorem integral_coordinate_substitution {a Y : ℝ} {H w₂ : ℝ → ℝ}
    (ha : 0 < a) (hY : Y ≤ 1)
    (hH : ∀ y ∈ Ioo 0 Y, 0 < H y)
    (hd : ∀ y ∈ Ioo 0 Y, DifferentiableAt ℝ H y)
    (hode : ∀ y ∈ Ioo 0 Y,
      H y - 2 * a * y * deriv H y = (Real.sqrt (1 - y))⁻¹)
    (hbij : BijOn (coordinate a H) (Ioo 0 Y) (Ioi 0))
    (hw : ∀ y ∈ Ioo 0 Y, w₂ (coordinate a H y) = secondWeight a y) :
    (∫ u : ℝ in Ioi 0, u ^ (2 - 3 * a) * w₂ u) =
      ∫ y : ℝ in Ioo 0 Y, curvatureWeight a H y := by
  rw [← hbij.image_eq]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun y hy => (hasDerivAt_coordinate ha.ne' hy.1 (hy.2.trans_le hY)
      (hd y hy) (hode y hy)).hasDerivWithinAt) hbij.injOn]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro y hy
  dsimp only
  rw [smul_eq_mul, hw y hy]
  exact curvature_jacobian ha hy.1 (hy.2.trans_le hY) (hH y hy)

/-- Absolute convergence passes through exactly the same change of variables. -/
theorem curvatureWeight_integrable {a Y : ℝ} {H w₂ : ℝ → ℝ}
    (ha : 0 < a) (hY : Y ≤ 1)
    (hH : ∀ y ∈ Ioo 0 Y, 0 < H y)
    (hd : ∀ y ∈ Ioo 0 Y, DifferentiableAt ℝ H y)
    (hode : ∀ y ∈ Ioo 0 Y,
      H y - 2 * a * y * deriv H y = (Real.sqrt (1 - y))⁻¹)
    (hbij : BijOn (coordinate a H) (Ioo 0 Y) (Ioi 0))
    (hw : ∀ y ∈ Ioo 0 Y, w₂ (coordinate a H y) = secondWeight a y)
    (hi : IntegrableOn (fun u : ℝ => u ^ (2 - 3 * a) * w₂ u) (Ioi 0)) :
    IntegrableOn (curvatureWeight a H) (Ioo 0 Y) := by
  rw [← hbij.image_eq] at hi
  have he := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun y hy => (hasDerivAt_coordinate ha.ne' hy.1 (hy.2.trans_le hY)
      (hd y hy) (hode y hy)).hasDerivWithinAt) hbij.injOn
    (fun u : ℝ => u ^ (2 - 3 * a) * w₂ u)).mp hi
  apply he.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  rw [smul_eq_mul, hw y hy]
  exact curvature_jacobian ha hy.1 (hy.2.trans_le hY) (hH y hy)

end Kagey131.PaperD.AnalyticThresholdSubstitution
