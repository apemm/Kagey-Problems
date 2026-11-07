import PaperD.EJPAnalyticThresholdIdentification
import PaperD.EJPAnalyticThresholdRandomization
import PaperD.EJPAnalyticThresholdParamCoordinate
import PaperD.EJPAnalyticThresholdSeriesRoots

/-!
# The conditional law and the transform equations

The classical input is the normalized moment equation of Guérin--Laulin--
Raschel--Simon, applied to the exponentially randomized conditional law.
Its real and imaginary parts, and the even initial coefficient, are derived
here. The explicit H parametrization is not part of that input.
-/

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology

namespace Kagey131.PaperD.AnalyticThresholdModel

open AnalyticThresholdRandomization AnalyticThresholdIdentification
open AnalyticThresholdParam

noncomputable def realTransform (a : ℝ) (μ : Measure ℝ) (t : ℝ) : ℝ :=
  (charFun (randomizedLaw a μ) t).re

noncomputable def imagTransform (a : ℝ) (μ : Measure ℝ) (t : ℝ) : ℝ :=
  (charFun (randomizedLaw a μ) t).im

@[simp] theorem realTransform_zero (a : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    realTransform a μ 0 = 1 := by simp [realTransform]

@[simp] theorem imagTransform_zero (a : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    imagTransform a μ 0 = 0 := by simp [imagTransform]

theorem realTransform_even (a : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    realTransform a μ (-t) = realTransform a μ t := by
  simp [realTransform, charFun_neg]

lemma deriv_zero_of_even {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f 0)
    (heven : ∀ t, f (-t) = f t) : deriv f 0 = 0 := by
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1) (0 : ℝ) :=
    (hasDerivAt_id (0 : ℝ)).neg
  have hbase : HasDerivAt f (deriv f 0) (-(0 : ℝ)) := by simpa using hf.hasDerivAt
  have h := hbase.comp (0 : ℝ) hneg
  have h' : HasDerivAt f (-deriv f 0) 0 := by
    exact (h.congr_of_eventuallyEq
      (Eventually.of_forall fun t => (heven t).symm)).congr_deriv (mul_neg_one _)
  have heq := h'.unique hf.hasDerivAt
  linarith

theorem real_imag_moment_equations {a t A B A' B' : ℝ}
    (h : (A : ℂ) + B * I + (a : ℂ) * t * ((A' : ℂ) + B' * I) =
      (1 + (a : ℂ)) / 2 * ((A : ℂ) + B * I) ^ 2 +
      (1 - (a : ℂ)) / 2 * ((A : ℂ) + B * I) * ((A : ℂ) - B * I)) :
    a * t * A' = A ^ 2 - A - a * B ^ 2 ∧
    a * t * B' = ((1 + a) * A - 1) * B := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [Complex.mul_re, Complex.mul_im, pow_two] at hr hi
  constructor <;> nlinarith

/-- The published moment-generating equation and its analytic regularity.
All functions in this input are the characteristic function of the actual
product-law randomization. No H identity or curvature formula is assumed. -/
structure MomentEquation (a : ℝ) (μ : Measure ℝ) : Prop where
  analytic_real : AnalyticOnNhd ℝ (realTransform a μ) univ
  analytic_imag : AnalyticOnNhd ℝ (imagTransform a μ) univ
  linear_coefficient : deriv (imagTransform a μ) 0 = 1
  equation : ∀ t : ℝ,
    (realTransform a μ t : ℂ) + imagTransform a μ t * I +
      (a : ℂ) * t * (Complex.ofReal (deriv (realTransform a μ) t) +
        Complex.ofReal (deriv (imagTransform a μ) t) * I) =
      (1 + (a : ℂ)) / 2 * ((realTransform a μ t : ℂ) + imagTransform a μ t * I) ^ 2 +
      (1 - (a : ℂ)) / 2 * ((realTransform a μ t : ℂ) + imagTransform a μ t * I) *
        ((realTransform a μ t : ℂ) - imagTransform a μ t * I)

theorem MomentEquation.real_deriv_zero {a : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hm : MomentEquation a μ) : deriv (realTransform a μ) 0 = 0 :=
  deriv_zero_of_even (hm.analytic_real 0 (mem_univ _)).differentiableAt
    (realTransform_even a μ)

theorem MomentEquation.real_ode {a : ℝ} {μ : Measure ℝ} (hm : MomentEquation a μ) (t : ℝ) :
    a * t * deriv (realTransform a μ) t =
      realTransform a μ t ^ 2 - realTransform a μ t - a * imagTransform a μ t ^ 2 :=
  (real_imag_moment_equations (hm.equation t)).1

theorem MomentEquation.imag_ode {a : ℝ} {μ : Measure ℝ} (hm : MomentEquation a μ) (t : ℝ) :
    a * t * deriv (imagTransform a μ) t =
      ((1 + a) * realTransform a μ t - 1) * imagTransform a μ t :=
  (real_imag_moment_equations (hm.equation t)).2

/-- Identification with an H solution, proved from the singular moment
equation and its initial coefficients. Positivity is used only before H's
first zero. -/
theorem parametric_identification {a Y : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 1 / 2 < a) (hY0 : 0 < Y) (hY1 : Y ≤ 1)
    (hm : MomentEquation a μ) (H : ℝ → ℝ) (hH0 : H 0 = 1)
    (hH : ∀ y ∈ Ico 0 Y, AnalyticAt ℝ H y)
    (hpos : ∀ y ∈ Ico 0 Y, 0 < H y)
    (hode : ∀ y ∈ Ico 0 Y, SatisfiesODE a H y)
    {x : ℝ} (hx0 : 0 ≤ x) (hxY : x ^ 2 < Y) :
    realTransform a μ (coordinateT a H x) = coordinateA H x ∧
    imagTransform a μ (coordinateT a H x) = coordinateB H x := by
  have ha0 : 0 < a := by linarith
  let A := fun t => realTransform a μ (coordinateT a H t)
  let B := fun t => imagTransform a μ (coordinateT a H t)
  have hdata {t : ℝ} (ht : t ^ 2 < Y) := coordinate_analyticAt
    (a := a) (hH (t^2) ⟨sq_nonneg t, ht⟩)
    (hpos (t^2) ⟨sq_nonneg t, ht⟩) (ht.trans_le hY1)
  have ht0 : (0 : ℝ)^2 < Y := by simpa using hY0
  have hval := coordinate_values_zero (a := a) hH0
  have hjets := coordinate_jets_zero (a := a) hH0
    (hH 0 ⟨le_rfl, hY0⟩).differentiableAt
  have hA : AnalyticAt ℝ A 0 :=
    (hm.analytic_real _ (mem_univ _)).comp (hdata ht0).1
  have hB : AnalyticAt ℝ B 0 :=
    (hm.analytic_imag _ (mem_univ _)).comp (hdata ht0).1
  have hA0 : A 0 = 1 := by dsimp [A]; rw [hval.2.2]; simp
  have hB0 : B 0 = 0 := by dsimp [B]; rw [hval.2.2]; simp
  have hAC1 : deriv A 0 = deriv (coordinateA H) 0 := by
    have hreal : HasDerivAt (realTransform a μ) 0 (coordinateT a H 0) := by
      rw [hval.2.2]
      simpa only [hm.real_deriv_zero] using
        (hm.analytic_real 0 (mem_univ _)).differentiableAt.hasDerivAt
    have hd := (hreal.comp 0 hjets.2.2).deriv
    change deriv A 0 = _ at hd
    rw [hd, hjets.1.deriv]
    simp
  have hBD1 : deriv B 0 = deriv (coordinateB H) 0 := by
    have himag : HasDerivAt (imagTransform a μ) 1 (coordinateT a H 0) := by
      rw [hval.2.2]
      simpa only [hm.linear_coefficient] using
        (hm.analytic_imag 0 (mem_univ _)).differentiableAt.hasDerivAt
    have hd := (himag.comp 0 hjets.2.2).deriv
    change deriv B 0 = _ at hd
    rw [hd, hjets.2.1.deriv]
    simp
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ^ 2 < Y :=
    ((continuousAt_id.pow 2).eventually_lt_const ht0).filter_mono nhdsWithin_le_nhds
  have hoA : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t * deriv A t = coordinateC a H t *
      (A t ^ 2 - A t - a * B t ^ 2) := by
    filter_upwards [hev] with t ht
    exact reparametrize_first_equation
      (hm.analytic_real _ (mem_univ _)).differentiableAt
      (hdata ht).1.differentiableAt
      (coordinateT_chain ha0.ne' (hpos _ ⟨sq_nonneg t, ht⟩) (ht.trans_le hY1)
        (hH _ ⟨sq_nonneg t, ht⟩).differentiableAt (hode _ ⟨sq_nonneg t, ht⟩))
      (hm.real_ode _)
  have hoB : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t * deriv B t = coordinateC a H t *
      (((1 + a) * A t - 1) * B t) := by
    filter_upwards [hev] with t ht
    exact reparametrize_second_equation
      (hm.analytic_imag _ (mem_univ _)).differentiableAt
      (hdata ht).1.differentiableAt
      (coordinateT_chain ha0.ne' (hpos _ ⟨sq_nonneg t, ht⟩) (ht.trans_le hY1)
        (hH _ ⟨sq_nonneg t, ht⟩).differentiableAt (hode _ ⟨sq_nonneg t, ht⟩))
      (hm.imag_ode _)
  have hoCD : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      (t * deriv (coordinateA H) t = coordinateC a H t *
        (coordinateA H t ^ 2 - coordinateA H t - a * coordinateB H t ^ 2)) ∧
      (t * deriv (coordinateB H) t = coordinateC a H t *
        (((1 + a) * coordinateA H t - 1) * coordinateB H t)) := by
    filter_upwards [hev] with t ht
    exact coordinate_AB_ode ha0.ne' (hpos _ ⟨sq_nonneg t, ht⟩) (ht.trans_le hY1)
      (hH _ ⟨sq_nonneg t, ht⟩).differentiableAt (hode _ ⟨sq_nonneg t, ht⟩)
  obtain ⟨R, hR, heq⟩ := transform_unique_near_zero ha A B (coordinateA H) (coordinateB H)
    (coordinateC a H) hA hB (hdata ht0).2.1 (hdata ht0).2.2
    (coordinateC_continuousAt_zero ha0.ne' hH0 (hH 0 ⟨le_rfl, hY0⟩).continuousAt)
    (coordinateC_zero hH0) hA0 hval.1 hB0 hval.2.1 hAC1 hBD1 hoA
    (hoCD.mono fun _ h => h.1) hoB (hoCD.mono fun _ h => h.2)
  rcases eq_or_lt_of_le hx0 with rfl | hx
  · exact heq 0 ⟨le_rfl, hR.le⟩
  have hb {t : ℝ} (ht : t ∈ Icc 0 x) : t ^ 2 < Y := by
    have hs : t ^ 2 ≤ x ^ 2 := sq_le_sq₀ ht.1 hx.le |>.mpr ht.2
    exact hs.trans_lt hxY
  constructor
  · exact analytic_eqOn_of_initial_interval hx hR
      (fun t ht => (hm.analytic_real _ (mem_univ _)).comp (hdata (hb ht)).1)
      (fun t ht => (hdata (hb ht)).2.1)
      (fun t ht => (heq t ht).1) ⟨hx.le, le_rfl⟩
  · exact analytic_eqOn_of_initial_interval hx hR
      (fun t ht => (hm.analytic_imag _ (mem_univ _)).comp (hdata (hb ht)).1)
      (fun t ht => (hdata (hb ht)).2.2)
      (fun t ht => (heq t ht).2) ⟨hx.le, le_rfl⟩

/-- The model-specific transform identification for the actual binomial
series H and its uniquely determined root. -/
theorem series_parametric_identification {a x : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 1 / 2 < a) (ha1 : a < 1) (hm : MomentEquation a μ)
    (hx0 : 0 ≤ x) (hx : x ^ 2 < Modes.AnalyticThreshold.Series.rootY a) :
    realTransform a μ (coordinateT a (Modes.AnalyticThreshold.Series.H a) x) =
      coordinateA (Modes.AnalyticThreshold.Series.H a) x ∧
    imagTransform a μ (coordinateT a (Modes.AnalyticThreshold.Series.H a) x) =
      coordinateB (Modes.AnalyticThreshold.Series.H a) x := by
  let H := Modes.AnalyticThreshold.Series.H a
  have hY := Modes.AnalyticThreshold.Series.rootY_mem ha ha1
  apply parametric_identification ha hY.1 hY.2.le hm H
    (Modes.AnalyticThreshold.Series.H_zero a)
  · intro y hy
    exact Modes.AnalyticThreshold.Series.analyticAt_H ha
      (abs_lt.mpr ⟨by linarith [hy.1], hy.2.trans hY.2⟩)
  · exact fun y hy => Modes.AnalyticThreshold.Series.H_pos_before_rootY ha ha1 hy.1 hy.2
  · exact fun y hy => Modes.AnalyticThreshold.Series.H_ode ha hy.1 (hy.2.trans hY.2)
  · exact hx0
  · exact hx

end Kagey131.PaperD.AnalyticThresholdModel
