import PaperD.EJPAnalyticThresholdRatio
import PaperD.EJPAnalyticThresholdMeasureExterior
import PaperD.EJPAnalyticThresholdBounds

/-!
# Exterior signs for the actual analytic-threshold ratio

Every analytic input to the exterior mean comparison is discharged for the
actual H series. The rescaled weight is integrable throughout `(1/2,1)`:
`K` is bounded by the summable first moment of the root weights. Scaling the
actual Bochner integrals identifies the original mean with `Y * analyticMean`.
-/

namespace Kagey131.PaperD.AnalyticThresholdExteriorActual

open MeasureTheory Set
open Modes.AnalyticThreshold AnalyticThresholdRatio

theorem measurable_H (a : ℝ) : Measurable (Series.H a) := by
  unfold Series.H Series.powerSum
  apply measurable_const.sub
  apply Measurable.tsum
  intro k
  fun_prop

theorem H_pos_on_rootInterval {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    ∀ y ∈ Ioo (0 : ℝ) (Series.rootY a), 0 < Series.H a y :=
  fun _ hy => Series.H_pos_before_rootY ha ha1 hy.1.le hy.2

theorem antitoneOn_H_before_rootY {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    AntitoneOn (Series.H a) (Ioo (0 : ℝ) (Series.rootY a)) :=
  (Series.strictAntiOn_H ha).antitoneOn.mono
    (fun _ hy => ⟨hy.1.le, hy.2.trans (Series.rootY_mem ha ha1).2⟩)

theorem summable_root_first_moment {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    Summable (fun k : ℕ => (k : ℝ) * Weights.weight a (Series.rootY a) k) := by
  simpa only [pow_one] using Weights.summable_weight_pow ha
    (Series.rootY_mem ha ha1).1.le (Series.rootY_mem ha ha1).2 1

theorem rootKernel_le_first_moment {a u : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    rootKernel a u ≤ ∑' k : ℕ, (k : ℝ) * Weights.weight a (Series.rootY a) k := by
  have hr := Series.rootY_mem ha ha1
  apply (Weights.summable_K ha hr.1.le hr.2 hu.1 hu.2).tsum_le_tsum _
    (summable_root_first_moment ha ha1)
  intro k
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (Weights.geom_le hu.1 hu.2 k)
    (Weights.weight_nonneg ha hr.1.le k)

/-- Actual rescaled-density integrability on the entire physical interval.
There is no short-band, derivative, or externally supplied bound hypothesis. -/
theorem integrable_rootWeight {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    Integrable (analyticWeight rootKernel a) unitIntervalVolume := by
  apply integrable_analyticWeight_of_lt_one ha1 (measurable_rootKernel a)
    (fun u hu => rootKernel_ge_one ha ha1 ⟨hu.1.le, hu.2.le⟩)
  exact fun u hu => rootKernel_le_first_moment ha ha1 ⟨hu.1.le, hu.2.le⟩

/-- Integrability of the original, unnormalized H-density follows by scaling. -/
theorem integrable_actualWeight {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    Integrable (curvatureWeight a (Series.H a)) (initialIntervalVolume (Series.rootY a)) := by
  have hr := (Series.rootY_mem ha ha1).1
  have hb := scale_bijOn_unit hr
  change IntegrableOn (baseWeight a) (Ioo (0 : ℝ) (Series.rootY a))
  rw [← hb.image_eq, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun u _ => (scale_hasDerivAt (Series.rootY a) u).hasDerivWithinAt) hb.injOn]
  apply ((integrable_rootWeight ha ha1).const_mul
    (Series.rootY a * Series.rootY a ^ (1 / 2 : ℝ))).congr
  filter_upwards [unitIntervalVolume_ae_mem] with u hu
  rw [smul_eq_mul, abs_of_pos hr, baseWeight_rescale ha ha1 hu]
  ring

theorem actualProbability_isProbability {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    IsProbabilityMeasure (curvatureProbability a (Series.rootY a) (Series.H a)) :=
  curvatureProbability_isProbability (Series.rootY_mem ha ha1).1
    (integrable_actualWeight ha ha1) (H_pos_on_rootInterval ha ha1)

theorem integral_firstMoment_rescale {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    (∫ y : ℝ in Ioo 0 (Series.rootY a), y * baseWeight a y) =
      (Series.rootY a ^ 2 * Series.rootY a ^ (1 / 2 : ℝ)) *
        ∫ u, u * analyticWeight rootKernel a u ∂unitIntervalVolume := by
  have hr := (Series.rootY_mem ha ha1).1
  have hb := scale_bijOn_unit hr
  rw [← hb.image_eq,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun u _ => (scale_hasDerivAt (Series.rootY a) u).hasDerivWithinAt) hb.injOn]
  calc
    _ = ∫ u : ℝ in Ioo 0 1,
        (Series.rootY a ^ 2 * Series.rootY a ^ (1 / 2 : ℝ)) *
          (u * analyticWeight rootKernel a u) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      dsimp only
      rw [smul_eq_mul, abs_of_pos hr, baseWeight_rescale ha ha1 hu]
      ring
    _ = _ := by rw [integral_const_mul]; rfl

/-- The original expectation equals the root times the rescaled expectation. -/
theorem curvatureMean_eq_rootY_mul_analyticMean {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    curvatureMean a (Series.rootY a) (Series.H a) = Series.rootY a * analyticMean rootKernel a := by
  have hr := (Series.rootY_mem ha ha1).1
  have hi := integrable_rootWeight ha ha1
  have hp : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < rootKernel a u :=
    fun u hu => lt_of_lt_of_le zero_lt_one (rootKernel_ge_one ha ha1 ⟨hu.1.le, hu.2.le⟩)
  have hz := weightNormalizer_pos hi (fun u hu => analyticWeight_pos hu (hp u hu))
  rw [curvatureMean_eq_integral_ratio hr (measurable_H a) (integrable_actualWeight ha ha1)
    (H_pos_on_rootInterval ha ha1)]
  change (∫ y : ℝ in Ioo 0 (Series.rootY a), y * baseWeight a y) /
    (∫ y : ℝ in Ioo 0 (Series.rootY a), baseWeight a y) = _
  rw [integral_firstMoment_rescale ha ha1, integral_baseWeight_rescale ha ha1,
    analyticMean_eq_integral_ratio (measurable_rootKernel a) hi hp]
  field_simp [hr.ne', (Real.rpow_pos_of_pos hr (1 / 2 : ℝ)).ne', hz.ne']

theorem actualMean_le_three_fifths {a : ℝ} (ha : 1 / 2 < a) (ha' : a ≤ 2 / 3) :
    curvatureMean a (Series.rootY a) (Series.H a) ≤ 3 * Series.rootY a / 5 := by
  have ha1 : a < 1 := by linarith
  exact curvatureMean_le_three_fifths (Series.rootY_mem ha ha1).1 ha' (measurable_H a)
    (integrable_actualWeight ha ha1) (H_pos_on_rootInterval ha ha1) (antitoneOn_H_before_rootY ha ha1)

theorem actualMean_ge_three_fifths {a : ℝ} (ha : 2 / 3 ≤ a) (ha1 : a < 1) :
    3 * Series.rootY a / 5 ≤ curvatureMean a (Series.rootY a) (Series.H a) := by
  have ha0 : 1 / 2 < a := by linarith
  exact curvatureMean_ge_three_fifths (Series.rootY_mem ha0 ha1).1 ha (measurable_H a)
    (integrable_actualWeight ha0 ha1) (H_pos_on_rootInterval ha0 ha1)
    (antitoneOn_H_before_rootY ha0 ha1)

theorem ratio_lt_one {a : ℝ} (ha : 1 / 2 < a) (ha' : a ≤ 2 / 3) : ratio a < 1 := by
  have ha1 : a < 1 := by linarith
  have hroot : Series.rootY a < 3 / 5 :=
    (Series.rootY_strictMono.monotoneOn ⟨ha, ha1⟩
      (by norm_num : (2 / 3 : ℝ) ∈ Ioo (1 / 2 : ℝ) 1) ha').trans_lt
        Series.rootY_two_thirds_enclosure.2
  have h := curvatureRatio_lt_one (Series.rootY_mem ha ha1).1 (by linarith : -1 ≤ a)
    ha' hroot (measurable_H a) (integrable_actualWeight ha ha1)
    (H_pos_on_rootInterval ha ha1) (antitoneOn_H_before_rootY ha ha1)
  rw [curvatureMean_eq_rootY_mul_analyticMean ha ha1] at h
  simpa only [ratio, mul_assoc] using h

theorem ratio_gt_one {a : ℝ} (ha : 69 / 100 ≤ a) (ha1 : a < 1) : 1 < ratio a := by
  have ha0 : 1 / 2 < a := by linarith
  have hroot : 117 / 200 < Series.rootY a :=
    Series.rootY_two_thirds_enclosure.1.trans_le
      (Series.rootY_strictMono.monotoneOn
        (by norm_num : (2 / 3 : ℝ) ∈ Ioo (1 / 2 : ℝ) 1) ⟨ha0, ha1⟩ (by linarith))
  have h := curvatureRatio_gt_one (Series.rootY_mem ha0 ha1).1 ha hroot
    (measurable_H a) (integrable_actualWeight ha0 ha1)
    (H_pos_on_rootInterval ha0 ha1) (antitoneOn_H_before_rootY ha0 ha1)
  rw [curvatureMean_eq_rootY_mul_analyticMean ha0 ha1] at h
  simpa only [ratio, mul_assoc] using h

end Kagey131.PaperD.AnalyticThresholdExteriorActual
