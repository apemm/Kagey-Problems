import PaperD.EJPModelMomentActual
import PaperD.EJPModelFourier
import PaperD.EJPModelDensityIdentification
import PaperD.EJPAnalyticThresholdFinalRegularity

/-!
# Curvature transition for the actual ERW weak-limit family

Both the moment equation and the conditional Fourier package follow from
weak convergence of the actual scaled finite laws. The density function is
the canonical inverse Fourier integral, identified here as the density of
the actual fair-start law. No moment, fixed-point, or Fourier hypothesis
is an input here.
-/

open Set MeasureTheory ProbabilityTheory

namespace Kagey131.PaperD.ModelThreshold

open ModelLimit ModelFourier AnalyticThresholdRatio AnalyticThresholdFinal

/-- The canonical function is the density of the actual fair-start law. -/
theorem actual_fairLaw_eq_withDensity {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    {μ : ProbabilityMeasure ℝ} (hμ : WeakLimit a (by linarith) ha1.le μ) :
    fairLaw (μ : Measure ℝ) = volume.withDensity
      (fun x => ENNReal.ofReal (canonicalFairDensity (μ : Measure ℝ) x)) :=
  fairLaw_eq_withDensity_canonical_of_fixedPoint (by linarith) ha1 μ
    (fixedPoint_of_weakLimit (by linarith) ha1 μ hμ)
    (weakLimit_mean_pos ha ha1.le hμ).ne'

/-- The conditional Fourier package follows from the actual finite-law limit. -/
theorem actual_conditionalFourierHyp {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    {μ : ProbabilityMeasure ℝ} (hμ : WeakLimit a (by linarith) ha1.le μ) :
    Modes.ConditionalFourierHyp a (canonicalFairDensity (μ : Measure ℝ))
      (charFun (μ : Measure ℝ)) :=
  conditionalFourierHyp_of_fixedPoint (by linarith) ha1 μ
    (fixedPoint_of_weakLimit (by linarith) ha1 μ hμ)
    (weakLimit_mean_pos ha ha1.le hμ).ne'

/-- The actual curvature identity has only the ordinary weak-limit premise. -/
theorem actual_curvature_ratio {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    {μ : ProbabilityMeasure ℝ} (hμ : WeakLimit a (by linarith) ha1.le μ) :
    deriv (deriv (canonicalFairDensity (μ : Measure ℝ))) 0 =
      curvaturePrefactor a * (ratio a - 1) :=
  AnalyticThresholdFinal.actual_curvature_ratio ha ha1
    (ModelMoment.actual_momentEquation ha ha1 hμ)
    (actual_conditionalFourierHyp ha ha1 hμ)

/-- Global uniqueness and both curvature signs for the actual weak-limit family. -/
theorem exists_unique_actual_curvature_transition
    (μ : ℝ → ProbabilityMeasure ℝ)
    (hμ : ∀ a, ∀ ha : a ∈ Ioo (1 / 2 : ℝ) 1,
      WeakLimit a (by linarith [ha.1]) ha.2.le (μ a)) :
    ∃ r ∈ Ioo (2 / 3 : ℝ) (69 / 100),
      deriv (deriv (canonicalFairDensity (μ r : Measure ℝ))) 0 = 0 ∧
      (∀ a ∈ Ioo (1 / 2 : ℝ) 1,
        deriv (deriv (canonicalFairDensity (μ a : Measure ℝ))) 0 = 0 ↔ a = r) ∧
      (∀ a ∈ Ioo (1 / 2 : ℝ) r,
        deriv (deriv (canonicalFairDensity (μ a : Measure ℝ))) 0 < 0) ∧
      (∀ a ∈ Ioo r (1 : ℝ),
        0 < deriv (deriv (canonicalFairDensity (μ a : Measure ℝ))) 0) :=
  AnalyticThresholdFinal.exists_unique_actual_curvature_transition
    (fun a => (μ a : Measure ℝ)) (fun a => canonicalFairDensity (μ a : Measure ℝ))
    (fun _ _ => inferInstance)
    (fun a ha => ModelMoment.actual_momentEquation ha.1 ha.2 (hμ a ha))
    (fun a ha => actual_conditionalFourierHyp ha.1 ha.2 (hμ a ha))

/-- The same unique transition has a strictly positive memory derivative of
curvature. No parameter regularity of the weak-limit family is assumed. -/
theorem exists_unique_actual_curvature_transition_with_derivative
    (μ : ℝ → ProbabilityMeasure ℝ)
    (hμ : ∀ a, ∀ ha : a ∈ Ioo (1 / 2 : ℝ) 1,
      WeakLimit a (by linarith [ha.1]) ha.2.le (μ a)) :
    ∃ r ∈ Ioo (2 / 3 : ℝ) (69 / 100),
      deriv (deriv (canonicalFairDensity (μ r : Measure ℝ))) 0 = 0 ∧
      (∀ a ∈ Ioo (1 / 2 : ℝ) 1,
        deriv (deriv (canonicalFairDensity (μ a : Measure ℝ))) 0 = 0 ↔ a = r) ∧
      (∀ a ∈ Ioo (1 / 2 : ℝ) r,
        deriv (deriv (canonicalFairDensity (μ a : Measure ℝ))) 0 < 0) ∧
      (∀ a ∈ Ioo r (1 : ℝ),
        0 < deriv (deriv (canonicalFairDensity (μ a : Measure ℝ))) 0) ∧
      HasDerivAt (fun a => deriv (deriv (canonicalFairDensity (μ a : Measure ℝ))) 0)
        (curvaturePrefactor r * deriv ratio r) r ∧
      0 < deriv (fun a => deriv (deriv (canonicalFairDensity (μ a : Measure ℝ))) 0) r := by
  obtain ⟨r, hr, hz, hu, hn, hp⟩ := exists_unique_actual_curvature_transition μ hμ
  obtain ⟨s, hs⟩ := AnalyticThresholdFinal.actual_transitionCrossing
  have hsphys : s ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith [hs.root_mem.1, hs.root_mem.2]
  have hsz : deriv (deriv (canonicalFairDensity (μ s : Measure ℝ))) 0 = 0 := by
    rw [actual_curvature_ratio hsphys.1 hsphys.2 (hμ s hsphys), hs.value]
    ring
  have hsr : s = r := (hu s hsphys).mp hsz
  subst s
  have hd := AnalyticThresholdFinalRegularity.actual_curvature_derivative_pos_at_transition
    (fun a => (μ a : Measure ℝ)) (fun a => canonicalFairDensity (μ a : Measure ℝ))
    (fun _ _ => inferInstance)
    (fun a ha => ModelMoment.actual_momentEquation ha.1 ha.2 (hμ a ha))
    (fun a ha => actual_conditionalFourierHyp ha.1 ha.2 (hμ a ha)) hs
  exact ⟨r, hr, hz, hu, hn, hp, hd.1, hd.2⟩

end Kagey131.PaperD.ModelThreshold
