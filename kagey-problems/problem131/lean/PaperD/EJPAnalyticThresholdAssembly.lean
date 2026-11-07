import PaperD.EJPAnalyticThresholdModel
import PaperD.EJPAnalyticThresholdParamChart
import PaperD.EJPAnalyticThresholdSubstitution
import PaperD.EJPAnalyticThresholdContinuation

/-!
# The actual H chart and the randomized transform

The root and inverse chart are constructed from the binomial series. This
file identifies the chart's weight with the Jacobian-adjusted characteristic
function of the actual randomized law.
-/

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology

namespace Kagey131.PaperD.AnalyticThresholdAssembly

open AnalyticThresholdParam AnalyticThresholdModel AnalyticThresholdRandomization
open AnalyticThresholdSubstitution
open Modes.AnalyticThreshold

theorem series_rootData {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    RootData a (Series.H a) (Series.rootY a) := by
  have hr := Series.rootY_mem ha ha1
  refine ⟨hr.1, hr.2, Series.H_zero a, Series.H_rootY ha ha1, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Series.analyticAt_H ha (by norm_num : |(0 : ℝ)| < 1)).continuousAt
  · exact (Series.analyticAt_H ha (abs_lt.mpr ⟨by linarith [hr.1], hr.2⟩)).continuousAt
  · exact fun y hy => Series.H_pos_before_rootY ha ha1 hy.1.le hy.2
  · intro y hy
    exact (Series.analyticAt_H ha (abs_lt.mpr ⟨by linarith [hy.1], hy.2.trans_lt hr.2⟩)).differentiableAt
  · exact fun y hy => Series.H_ode ha hy.1.le (hy.2.trans_lt hr.2)

noncomputable def seriesChart {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    AngleChart a (Series.H a) := chartOfRoot (by linarith : 0 < a) (series_rootData ha ha1)

theorem coordinateT_at_inverse {a : ℝ} {H : ℝ → ℝ} (ha : 0 < a)
    (c : AngleChart a H) {u : ℝ} (hu : 0 < u) :
    coordinateT a H (Real.sin (c.angle u)) = u ^ (-a) := by
  have hs := c.sin_pos u hu
  unfold coordinateT
  rw [← inverse_scale c hu,
    Real.mul_rpow hu.le (Real.rpow_nonneg hs.le _), ← Real.rpow_mul hs.le]
  rw [show (1 / a) * -a = (-1 : ℝ) by field_simp, Real.rpow_neg_one]
  field_simp

theorem realTransform_at_chart {a : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 1 / 2 < a) (ha1 : a < 1) (hm : MomentEquation a μ)
    {u : ℝ} (hu : 0 < u) :
    realTransform a μ (u ^ (-a)) =
      Series.H a (Real.sin ((seriesChart ha ha1).angle u)^2) * Real.cos ((seriesChart ha ha1).angle u) := by
  let c := seriesChart ha ha1
  have hθ := chartOfRoot_range (by linarith : 0 < a) (series_rootData ha ha1) u hu
  have hr := Series.rootY_mem ha ha1
  have hy := (angle_range hr.1 hr.2 hθ).2.2
  have hs := c.sin_pos u hu
  have hc := c.cos_pos u hu
  have hid := (series_parametric_identification ha ha1 hm hs.le hy.2).1
  rw [coordinateT_at_inverse (by linarith : 0 < a) c hu] at hid
  unfold coordinateA at hid
  have hsqrt : Real.sqrt (1 - Real.sin (c.angle u)^2) = Real.cos (c.angle u) := by
    rw [show 1 - Real.sin (c.angle u)^2 = Real.cos (c.angle u)^2 by
      nlinarith [Real.sin_sq_add_cos_sq (c.angle u)], Real.sqrt_sq hc.le]
  simpa only [hsqrt] using hid

theorem series_weight_eq_real_inversePower {a : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 1 / 2 < a) (ha1 : a < 1) (hm : MomentEquation a μ)
    {u : ℝ} (hu : 0 < u) :
    weight (seriesChart ha ha1) u = (a * realTransform a μ (u ^ (-a))) / u := by
  apply (eq_div_iff hu.ne').mpr
  rw [weight_scaled (seriesChart ha ha1) hu, realTransform_at_chart ha ha1 hm hu]
  ring

theorem series_weight_identification {a : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 1 / 2 < a) (ha1 : a < 1) (hm : MomentEquation a μ)
    {u : ℝ} (hu : 0 < u) :
    (weight (seriesChart ha ha1) u : ℂ) =
      inversePowerWeight a (fun t => (realTransform a μ t : ℂ)) u := by
  rw [series_weight_eq_real_inversePower ha ha1 hm hu]
  unfold inversePowerWeight
  rw [cpow_neg_one]
  push_cast
  ring

/-- The curvature formula for the actual binomial series and the fair-start
density. The only law-specific inputs are the published moment equation and
the existing conditional Fourier/fixed-point hypotheses. -/
theorem actual_curvature_identity {a : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {g : ℝ → ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (hm : MomentEquation a μ) (hφ : Modes.ConditionalFourierHyp a g (charFun μ)) :
    IntegrableOn (curvatureWeight a (Series.H a)) (Ioo 0 (Series.rootY a)) ∧
      deriv (deriv g) 0 = -((Real.Gamma (3 - 3*a))⁻¹) / Real.pi *
        ∫ y : ℝ in Ioo 0 (Series.rootY a), curvatureWeight a (Series.H a) y := by
  have ha0 : 0 < a := by linarith
  let d := series_rootData ha ha1
  let c := chartOfRoot ha0 d
  have hw : ∀ u ∈ Ioi (0 : ℝ), (weight c u : ℂ) =
      inversePowerWeight a (fun t => ((charFun (randomizedLaw a μ) t).re : ℂ)) u := by
    intro u hu
    exact series_weight_identification ha ha1 hm hu
  obtain ⟨hi, hcurv⟩ := AnalyticThresholdContinuation.curvature_integral_chartOfRoot
    ha0 ha1 μ hφ d hw
  have hbij : BijOn (coordinate a (Series.H a)) (Ioo 0 (Series.rootY a)) (Ioi 0) :=
    yCoordinate_bijOn ha0 d
  have hw₂ : ∀ y ∈ Ioo 0 (Series.rootY a),
      weight₂ c (coordinate a (Series.H a) y) = secondWeight a y :=
    fun y hy => chartOfRoot_weight₂_yCoordinate ha0 d hy
  have hd : ∀ y ∈ Ioo 0 (Series.rootY a), DifferentiableAt ℝ (Series.H a) y :=
    fun y hy => d.differentiable y ⟨hy.1, hy.2.le⟩
  have hode : ∀ y ∈ Ioo 0 (Series.rootY a),
      Series.H a y - 2 * a * y * deriv (Series.H a) y = (Real.sqrt (1 - y))⁻¹ :=
    fun y hy => d.ode y ⟨hy.1, hy.2.le⟩
  have hsub := integral_coordinate_substitution ha0 d.root_lt_one.le d.positive hd hode hbij hw₂
  refine ⟨curvatureWeight_integrable ha0 d.root_lt_one.le d.positive hd hode hbij hw₂ hi, ?_⟩
  rw [hsub] at hcurv
  exact hcurv

end Kagey131.PaperD.AnalyticThresholdAssembly
