import PaperD.EJPAnalyticThresholdMeasureDiff
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exterior mean comparisons for the actual curvature density

The Chebyshev argument uses only integrability of the base density and the
tilted density. In particular the extra weight need not be bounded or in L².
The base density `y^(1/2)` on `(0,Y)` has mean exactly `3*Y/5`.
-/

namespace Kagey131.PaperD.Modes.AnalyticThreshold

open MeasureTheory Set Filter
open scoped Topology

noncomputable def initialIntervalVolume (Y : ℝ) : Measure ℝ := volume.restrict (Ioo 0 Y)

lemma initialIntervalVolume_ae_mem (Y : ℝ) :
    ∀ᵐ y ∂initialIntervalVolume Y, y ∈ Ioo (0 : ℝ) Y :=
  ae_restrict_mem measurableSet_Ioo

lemma integrable_coordinate_mul_on_initialInterval {μ : Measure ℝ} {f : ℝ → ℝ} {Y : ℝ}
    (hs : ∀ᵐ y ∂μ, y ∈ Ioo (0 : ℝ) Y) (hi : Integrable f μ) :
    Integrable (fun y => y * f y) μ := by
  apply hi.bdd_mul (c := Y) measurable_id.aestronglyMeasurable
  filter_upwards [hs] with y hy
  simpa [Real.norm_eq_abs, abs_of_pos hy.1] using hy.2.le

/-- Centering at the known base mean avoids any L² assumption. -/
theorem centered_tilted_integral {μ : Measure ℝ} {w e : ℝ → ℝ} {Y m : ℝ}
    (hs : ∀ᵐ y ∂μ, y ∈ Ioo (0 : ℝ) Y)
    (hw : Integrable w μ) (hwe : Integrable (fun y => w y * e y) μ)
    (hmean : (∫ y, y * w y ∂μ) = m * ∫ y, w y ∂μ) :
    (∫ y, (y - m) * (e y - e m) * w y ∂μ) =
      (∫ y, y * (w y * e y) ∂μ) - m * ∫ y, w y * e y ∂μ := by
  have hyw := integrable_coordinate_mul_on_initialInterval hs hw
  have hywe := integrable_coordinate_mul_on_initialInterval hs hwe
  calc
    _ = ∫ y, (y * (w y * e y) - m * (w y * e y)) -
        (e m * (y * w y) - (e m * m) * w y) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by ring
    _ = _ := by
      rw [integral_sub (f := fun y => y * (w y * e y) - m * (w y * e y))
        (g := fun y => e m * (y * w y) - (e m * m) * w y)
        (hywe.sub (hwe.const_mul m))
        ((hyw.const_mul (e m)).sub (hw.const_mul (e m * m))),
        integral_sub hywe (hwe.const_mul m),
        integral_sub (hyw.const_mul (e m)) (hw.const_mul (e m * m))]
      simp only [integral_const_mul, hmean]
      ring

theorem weightedMean_le_of_antitone {μ : Measure ℝ} {w e : ℝ → ℝ} {Y m : ℝ}
    (hs : ∀ᵐ y ∂μ, y ∈ Ioo (0 : ℝ) Y)
    (hw : Integrable w μ) (hwe : Integrable (fun y => w y * e y) μ)
    (hw0 : ∀ᵐ y ∂μ, 0 ≤ w y) (hm : m ∈ Ioo (0 : ℝ) Y)
    (hmean : (∫ y, y * w y ∂μ) = m * ∫ y, w y ∂μ)
    (hZ : 0 < ∫ y, w y * e y ∂μ) (he : AntitoneOn e (Ioo (0 : ℝ) Y)) :
    (∫ y, y * (w y * e y) ∂μ) / (∫ y, w y * e y ∂μ) ≤ m := by
  apply (div_le_iff₀ hZ).2
  have hc : (∫ y, (y - m) * (e y - e m) * w y ∂μ) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [hs, hw0] with y hy hwpos
    apply mul_nonpos_of_nonpos_of_nonneg _ hwpos
    rcases le_total y m with h | h
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h)
        (sub_nonneg.mpr (he hy hm h))
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h)
        (sub_nonpos.mpr (he hm hy h))
  rw [centered_tilted_integral hs hw hwe hmean] at hc
  linarith

theorem weightedMean_ge_of_monotone {μ : Measure ℝ} {w e : ℝ → ℝ} {Y m : ℝ}
    (hs : ∀ᵐ y ∂μ, y ∈ Ioo (0 : ℝ) Y)
    (hw : Integrable w μ) (hwe : Integrable (fun y => w y * e y) μ)
    (hw0 : ∀ᵐ y ∂μ, 0 ≤ w y) (hm : m ∈ Ioo (0 : ℝ) Y)
    (hmean : (∫ y, y * w y ∂μ) = m * ∫ y, w y ∂μ)
    (hZ : 0 < ∫ y, w y * e y ∂μ) (he : MonotoneOn e (Ioo (0 : ℝ) Y)) :
    m ≤ (∫ y, y * (w y * e y) ∂μ) / (∫ y, w y * e y ∂μ) := by
  apply (le_div_iff₀ hZ).2
  have hc : 0 ≤ ∫ y, (y - m) * (e y - e m) * w y ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hs, hw0] with y hy hwpos
    apply mul_nonneg _ hwpos
    rcases le_total y m with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
        (sub_nonpos.mpr (he hy hm h))
    · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (he hm hy h))
  rw [centered_tilted_integral hs hw hwe hmean] at hc
  linarith

lemma initialInterval_integral_rpow {Y r : ℝ} (hY : 0 < Y) (hr : -1 < r) :
    (∫ y, y ^ r ∂initialIntervalVolume Y) = Y ^ (r + 1) / (r + 1) := by
  change (∫ y in Ioo (0 : ℝ) Y, y ^ r) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hY.le,
    integral_rpow (Or.inl hr)]
  simp only [Real.zero_rpow (by linarith : r + 1 ≠ 0), sub_zero]

lemma initialInterval_integrable_rpow {Y r : ℝ} (hY : 0 < Y) (hr : -1 < r) :
    Integrable (fun y : ℝ => y ^ r) (initialIntervalVolume Y) :=
  (intervalIntegral.integrableOn_Ioo_rpow_iff hY).2 hr

/-- The exact Beta(3/2,1) first moment, before normalization. -/
theorem beta_three_halves_mean {Y : ℝ} (hY : 0 < Y) :
    (∫ y, y * y ^ (1 / 2 : ℝ) ∂initialIntervalVolume Y) =
      (3 * Y / 5) * ∫ y, y ^ (1 / 2 : ℝ) ∂initialIntervalVolume Y := by
  have he : (fun y : ℝ => y * y ^ (1 / 2 : ℝ)) =ᵐ[initialIntervalVolume Y]
      (fun y : ℝ => y ^ (3 / 2 : ℝ)) := by
    filter_upwards [initialIntervalVolume_ae_mem Y] with y hy
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy.1, Real.rpow_one]
  rw [integral_congr_ae he, initialInterval_integral_rpow hY (by norm_num),
    initialInterval_integral_rpow hY (by norm_num)]
  norm_num only [show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num,
    show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num]
  rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hY, Real.rpow_one]
  ring

noncomputable def curvatureWeight (a : ℝ) (H : ℝ → ℝ) (y : ℝ) : ℝ :=
  y ^ (1 / 2 : ℝ) * H y ^ (2 - 3 * a)

noncomputable def curvatureNormalizer (a Y : ℝ) (H : ℝ → ℝ) : ℝ :=
  ∫ y, curvatureWeight a H y ∂initialIntervalVolume Y

noncomputable def curvatureProbability (a Y : ℝ) (H : ℝ → ℝ) : Measure ℝ :=
  (initialIntervalVolume Y).withDensity
    (fun y => ENNReal.ofReal (curvatureWeight a H y / curvatureNormalizer a Y H))

noncomputable def curvatureMean (a Y : ℝ) (H : ℝ → ℝ) : ℝ :=
  ∫ y, y ∂curvatureProbability a Y H

theorem curvatureNormalizer_pos {a Y : ℝ} {H : ℝ → ℝ} (hY : 0 < Y)
    (hi : Integrable (curvatureWeight a H) (initialIntervalVolume Y))
    (hH : ∀ y ∈ Ioo (0 : ℝ) Y, 0 < H y) : 0 < curvatureNormalizer a Y H := by
  have hpos : ∀ y ∈ Ioo (0 : ℝ) Y, 0 < curvatureWeight a H y :=
    fun y hy => mul_pos (Real.rpow_pos_of_pos hy.1 _) (Real.rpow_pos_of_pos (hH y hy) _)
  apply (integral_pos_iff_support_of_nonneg_ae
    ((initialIntervalVolume_ae_mem Y).mono fun y hy => (hpos y hy).le) hi).2
  have hmass : 0 < initialIntervalVolume Y (Ioo (0 : ℝ) Y) := by
    simp only [initialIntervalVolume, Measure.restrict_apply measurableSet_Ioo, inter_self,
      Real.volume_Ioo, sub_zero]
    exact ENNReal.ofReal_pos.mpr hY
  exact hmass.trans_le (measure_mono fun y hy => (hpos y hy).ne')

theorem curvatureProbability_isProbability {a Y : ℝ} {H : ℝ → ℝ} (hY : 0 < Y)
    (hi : Integrable (curvatureWeight a H) (initialIntervalVolume Y))
    (hH : ∀ y ∈ Ioo (0 : ℝ) Y, 0 < H y) :
    IsProbabilityMeasure (curvatureProbability a Y H) := by
  have hz := curvatureNormalizer_pos hY hi hH
  constructor
  rw [curvatureProbability, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)]
  · rw [integral_div]
    change ENNReal.ofReal (curvatureNormalizer a Y H / curvatureNormalizer a Y H) = 1
    simp [hz.ne']
  · filter_upwards [initialIntervalVolume_ae_mem Y] with y hy
    exact (div_pos (mul_pos (Real.rpow_pos_of_pos hy.1 _)
      (Real.rpow_pos_of_pos (hH y hy) _)) hz).le

theorem curvatureMean_eq_integral_ratio {a Y : ℝ} {H : ℝ → ℝ} (hY : 0 < Y)
    (hm : Measurable H) (hi : Integrable (curvatureWeight a H) (initialIntervalVolume Y))
    (hH : ∀ y ∈ Ioo (0 : ℝ) Y, 0 < H y) :
    curvatureMean a Y H = (∫ y, y * curvatureWeight a H y ∂initialIntervalVolume Y) /
      curvatureNormalizer a Y H := by
  have hz := curvatureNormalizer_pos hY hi hH
  have hmeas : Measurable (curvatureWeight a H) := by unfold curvatureWeight; fun_prop
  rw [curvatureMean, curvatureProbability,
    integral_withDensity_eq_integral_toReal_smul (hmeas.div_const _).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ y, (y * curvatureWeight a H y) / curvatureNormalizer a Y H
        ∂initialIntervalVolume Y := by
      apply integral_congr_ae
      filter_upwards [initialIntervalVolume_ae_mem Y] with y hy
      have hp : 0 < curvatureWeight a H y :=
        mul_pos (Real.rpow_pos_of_pos hy.1 _) (Real.rpow_pos_of_pos (hH y hy) _)
      rw [ENNReal.toReal_ofReal (div_pos hp hz).le, smul_eq_mul]
      ring
    _ = _ := integral_div _ _

theorem curvatureMean_le_three_fifths {a Y : ℝ} {H : ℝ → ℝ} (hY : 0 < Y)
    (ha : a ≤ 2 / 3) (hm : Measurable H)
    (hi : Integrable (curvatureWeight a H) (initialIntervalVolume Y))
    (hH : ∀ y ∈ Ioo (0 : ℝ) Y, 0 < H y) (hmono : AntitoneOn H (Ioo (0 : ℝ) Y)) :
    curvatureMean a Y H ≤ 3 * Y / 5 := by
  rw [curvatureMean_eq_integral_ratio hY hm hi hH]
  apply weightedMean_le_of_antitone (initialIntervalVolume_ae_mem Y)
    (initialInterval_integrable_rpow hY (by norm_num)) hi
    ((initialIntervalVolume_ae_mem Y).mono fun y hy => (Real.rpow_pos_of_pos hy.1 _).le)
    (by constructor <;> linarith) (beta_three_halves_mean hY)
    (curvatureNormalizer_pos hY hi hH)
  intro x hx y hy hxy
  exact Real.rpow_le_rpow (hH y hy).le (hmono hx hy hxy) (by linarith)

theorem curvatureMean_ge_three_fifths {a Y : ℝ} {H : ℝ → ℝ} (hY : 0 < Y)
    (ha : 2 / 3 ≤ a) (hm : Measurable H)
    (hi : Integrable (curvatureWeight a H) (initialIntervalVolume Y))
    (hH : ∀ y ∈ Ioo (0 : ℝ) Y, 0 < H y) (hmono : AntitoneOn H (Ioo (0 : ℝ) Y)) :
    3 * Y / 5 ≤ curvatureMean a Y H := by
  rw [curvatureMean_eq_integral_ratio hY hm hi hH]
  apply weightedMean_ge_of_monotone (initialIntervalVolume_ae_mem Y)
    (initialInterval_integrable_rpow hY (by norm_num)) hi
    ((initialIntervalVolume_ae_mem Y).mono fun y hy => (Real.rpow_pos_of_pos hy.1 _).le)
    (by constructor <;> linarith) (beta_three_halves_mean hY)
    (curvatureNormalizer_pos hY hi hH)
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos (hH y hy) (hmono hx hy hxy) (by linarith)

/-- The normalized base Beta(3/2,1) law has the claimed actual expectation. -/
theorem beta_three_halves_probability_mean {Y : ℝ} (hY : 0 < Y) :
    curvatureMean (2 / 3) Y (fun _ => 1) = 3 * Y / 5 := by
  have hi : Integrable (curvatureWeight (2 / 3) (fun _ => 1)) (initialIntervalVolume Y) := by
    change Integrable (fun y : ℝ => y ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (2 - 3 * (2 / 3 : ℝ)))
      (initialIntervalVolume Y)
    simpa only [Real.one_rpow, mul_one] using
      initialInterval_integrable_rpow (r := (1 / 2 : ℝ)) hY (by norm_num)
  have hpos : ∀ y ∈ Ioo (0 : ℝ) Y, 0 < (1 : ℝ) := fun _ _ => zero_lt_one
  have hmono : AntitoneOn (fun _ : ℝ => (1 : ℝ)) (Ioo (0 : ℝ) Y) := fun _ _ _ _ _ => le_rfl
  exact le_antisymm
    (curvatureMean_le_three_fifths hY le_rfl measurable_const hi hpos hmono)
    (curvatureMean_ge_three_fifths hY le_rfl measurable_const hi hpos hmono)

/-- The lower exterior sign uses only the root enclosure and actual density. -/
theorem curvatureRatio_lt_one {a Y : ℝ} {H : ℝ → ℝ} (hY : 0 < Y)
    (ha0 : -1 ≤ a) (ha : a ≤ 2 / 3) (hYupper : Y < 3 / 5)
    (hm : Measurable H) (hi : Integrable (curvatureWeight a H) (initialIntervalVolume Y))
    (hH : ∀ y ∈ Ioo (0 : ℝ) Y, 0 < H y) (hmono : AntitoneOn H (Ioo (0 : ℝ) Y)) :
    (1 + a) ^ 2 * curvatureMean a Y H < 1 := by
  apply ratio_lt_one ha0 ha hY.le hYupper
  convert curvatureMean_le_three_fifths hY ha hm hi hH hmono using 1
  ring

/-- The upper exterior sign also permits an unbounded extra weight. -/
theorem curvatureRatio_gt_one {a Y : ℝ} {H : ℝ → ℝ} (hY : 0 < Y)
    (ha : 69 / 100 ≤ a) (hYlower : 117 / 200 < Y)
    (hm : Measurable H) (hi : Integrable (curvatureWeight a H) (initialIntervalVolume Y))
    (hH : ∀ y ∈ Ioo (0 : ℝ) Y, 0 < H y) (hmono : AntitoneOn H (Ioo (0 : ℝ) Y)) :
    1 < (1 + a) ^ 2 * curvatureMean a Y H := by
  apply ratio_gt_one ha hYlower
  convert curvatureMean_ge_three_fifths hY (by linarith : (2 / 3 : ℝ) ≤ a)
    hm hi hH hmono using 1
  ring

end Kagey131.PaperD.Modes.AnalyticThreshold
