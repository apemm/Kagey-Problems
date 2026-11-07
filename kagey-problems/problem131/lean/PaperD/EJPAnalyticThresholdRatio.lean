import PaperD.EJPAnalyticThresholdMeasure
import PaperD.EJPAnalyticThresholdWeights
import PaperD.EJPAnalyticThresholdSeriesRoots
import PaperD.EJPAnalyticThresholdSubstitution

/-!
# The transition ratio of the actual H-weighted probability law

Rescaling `y = Y_a u` identifies the finite curvature integral with the
normalized mean on `(0,1)`. Every density and normalizer in this file is an
actual integral constructed from the binomial series.
-/

open Set MeasureTheory

namespace Kagey131.PaperD.AnalyticThresholdRatio

open Modes.AnalyticThreshold AnalyticThresholdSubstitution

noncomputable def rootKernel (a u : ℝ) : ℝ := Weights.K a (Series.rootY a) u

noncomputable def baseWeight (a y : ℝ) : ℝ :=
  y ^ (1 / 2 : ℝ) * Series.H a y ^ (2 - 3 * a)

noncomputable def ratio (a : ℝ) : ℝ :=
  (1 + a) ^ 2 * Series.rootY a * analyticMean rootKernel a

theorem measurable_rootKernel (a : ℝ) : Measurable (rootKernel a) := by
  unfold rootKernel Weights.K
  apply Measurable.tsum
  intro k
  unfold Weights.geom
  fun_prop

theorem rootKernel_ge_one {a u : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (hu : u ∈ Icc (0 : ℝ) 1) : 1 ≤ rootKernel a u :=
  Weights.one_le_K ha (Series.rootY_mem ha ha1).1.le (Series.rootY_mem ha ha1).2
    (Series.H_rootY ha ha1) hu.1 hu.2

theorem baseWeight_rescale {a u : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    baseWeight a (Series.rootY a * u) =
      Series.rootY a ^ (1 / 2 : ℝ) * analyticWeight rootKernel a u := by
  have hr := Series.rootY_mem ha ha1
  have hK : 0 < Weights.K a (Series.rootY a) u :=
    lt_of_lt_of_le zero_lt_one (rootKernel_ge_one ha ha1 ⟨hu.1.le, hu.2.le⟩)
  unfold baseWeight analyticWeight rootKernel
  rw [Weights.H_mul_eq ha hr.1.le hr.2 (Series.H_rootY ha ha1) hu.1.le hu.2.le,
    Real.mul_rpow hr.1.le hu.1.le,
    Real.mul_rpow (sub_pos.mpr hu.2).le hK.le,
    show 2 - 3 * a = -(3 * a - 2) by ring]
  ring

lemma scale_bijOn_unit {Y : ℝ} (hY : 0 < Y) :
    BijOn (fun u : ℝ => Y * u) (Ioo 0 1) (Ioo 0 Y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    exact ⟨mul_pos hY hu.1, by simpa using mul_lt_mul_of_pos_left hu.2 hY⟩
  · intro x hx y hy he
    exact mul_left_cancel₀ hY.ne' he
  · intro y hy
    refine ⟨y / Y, ⟨div_pos hy.1 hY, (div_lt_one hY).mpr hy.2⟩, ?_⟩
    field_simp

lemma scale_hasDerivAt (Y u : ℝ) : HasDerivAt (fun v : ℝ => Y * v) Y u := by
  simpa using (hasDerivAt_id u).const_mul Y

theorem integral_baseWeight_rescale {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    (∫ y : ℝ in Ioo 0 (Series.rootY a), baseWeight a y) =
      Series.rootY a * Series.rootY a ^ (1 / 2 : ℝ) *
        weightNormalizer (analyticWeight rootKernel a) := by
  have hr := (Series.rootY_mem ha ha1).1
  have hb := scale_bijOn_unit hr
  rw [← hb.image_eq,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun u _ => (scale_hasDerivAt (Series.rootY a) u).hasDerivWithinAt) hb.injOn]
  calc
    _ = ∫ u : ℝ in Ioo 0 1,
        (Series.rootY a * Series.rootY a ^ (1 / 2 : ℝ)) * analyticWeight rootKernel a u := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      dsimp only
      rw [smul_eq_mul, abs_of_pos hr, baseWeight_rescale ha ha1 hu]
      ring
    _ = _ := by rw [integral_const_mul]; rfl

theorem integral_curvatureWeight_rescale {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (hi : Integrable (analyticWeight rootKernel a) unitIntervalVolume) :
    (∫ y : ℝ in Ioo 0 (Series.rootY a), curvatureWeight a (Series.H a) y) =
      Series.rootY a * Series.rootY a ^ (1 / 2 : ℝ) *
        weightNormalizer (analyticWeight rootKernel a) * (1 - ratio a) := by
  have hr := (Series.rootY_mem ha ha1).1
  have hb := scale_bijOn_unit hr
  have hp : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < rootKernel a u :=
    fun u hu => lt_of_lt_of_le zero_lt_one (rootKernel_ge_one ha ha1 ⟨hu.1.le, hu.2.le⟩)
  have hnorm : 0 < weightNormalizer (analyticWeight rootKernel a) :=
    weightNormalizer_pos hi (fun u hu => analyticWeight_pos hu (hp u hu))
  have hmean := analyticMean_eq_integral_ratio (measurable_rootKernel a) hi hp
  have hcoord := integrable_coordinate_mul unitIntervalVolume_ae_mem hi
  rw [← hb.image_eq,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun u _ => (scale_hasDerivAt (Series.rootY a) u).hasDerivWithinAt) hb.injOn]
  have heq : (∫ u : ℝ in Ioo 0 1,
      |Series.rootY a| • curvatureWeight a (Series.H a) (Series.rootY a * u)) =
      (Series.rootY a * Series.rootY a ^ (1 / 2 : ℝ)) *
        (weightNormalizer (analyticWeight rootKernel a) -
          ((1 + a)^2 * Series.rootY a) *
            ∫ u, u * analyticWeight rootKernel a u ∂unitIntervalVolume) := by
    calc
      _ = ∫ u : ℝ in Ioo 0 1,
          (Series.rootY a * Series.rootY a ^ (1 / 2 : ℝ)) *
            (analyticWeight rootKernel a u - ((1 + a)^2 * Series.rootY a) *
              (u * analyticWeight rootKernel a u)) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro u hu
        dsimp only
        rw [smul_eq_mul, abs_of_pos hr]
        change Series.rootY a * (baseWeight a (Series.rootY a * u) * _) = _
        rw [baseWeight_rescale ha ha1 hu]
        ring
      _ = _ := by
        rw [integral_const_mul]
        change _ * (∫ u, _ ∂unitIntervalVolume) = _
        rw [integral_sub hi (hcoord.const_mul _), integral_const_mul]
        rfl
  rw [heq]
  unfold ratio
  rw [hmean]
  field_simp

end Kagey131.PaperD.AnalyticThresholdRatio
