import PaperD.EJPAnalyticThresholdAssembly
import PaperD.EJPAnalyticThresholdRatio
import PaperD.EJPAnalyticThresholdExteriorActual
import PaperD.EJPAnalyticThresholdComparisonRatio

/-!
# The actual curvature and its positive normalizing factor

The transform identification and the change of variables are assembled here
for the H-series itself. The named conditional-law inputs remain explicit.
-/

open Set MeasureTheory ProbabilityTheory

namespace Kagey131.PaperD.AnalyticThresholdFinal

open Modes.AnalyticThreshold AnalyticThresholdRatio AnalyticThresholdModel

noncomputable def curvaturePrefactor (a : ℝ) : ℝ :=
  Series.rootY a * Series.rootY a ^ (1 / 2 : ℝ) *
    weightNormalizer (analyticWeight rootKernel a) /
      (Real.pi * Real.Gamma (3 - 3*a))

theorem curvaturePrefactor_pos_of_integrable {a : ℝ}
    (ha : 1 / 2 < a) (ha1 : a < 1)
    (hi : Integrable (analyticWeight rootKernel a) unitIntervalVolume) :
    0 < curvaturePrefactor a := by
  have hY := (Series.rootY_mem ha ha1).1
  have hZ : 0 < weightNormalizer (analyticWeight rootKernel a) :=
    weightNormalizer_pos hi (fun u hu => analyticWeight_pos hu
      (lt_of_lt_of_le zero_lt_one (rootKernel_ge_one ha ha1 ⟨hu.1.le, hu.2.le⟩)))
  unfold curvaturePrefactor
  exact div_pos (mul_pos (mul_pos hY (Real.rpow_pos_of_pos hY _)) hZ)
    (mul_pos Real.pi_pos (Real.Gamma_pos_of_pos (by linarith)))

theorem actual_curvature_ratio_of_integrable {a : ℝ} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (ha : 1 / 2 < a) (ha1 : a < 1)
    (hm : MomentEquation a μ) (hφ : Modes.ConditionalFourierHyp a g (charFun μ))
    (hi : Integrable (analyticWeight rootKernel a) unitIntervalVolume) :
    deriv (deriv g) 0 = curvaturePrefactor a * (ratio a - 1) := by
  rw [(AnalyticThresholdAssembly.actual_curvature_identity ha ha1 hm hφ).2,
    integral_curvatureWeight_rescale ha ha1 hi]
  unfold curvaturePrefactor
  ring

theorem curvaturePrefactor_pos {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    0 < curvaturePrefactor a :=
  curvaturePrefactor_pos_of_integrable ha ha1
    (AnalyticThresholdExteriorActual.integrable_rootWeight ha ha1)

/-- All integral and chart hypotheses have been discharged for the actual
H-series. Only the named conditional-law inputs remain. -/
theorem actual_curvature_ratio {a : ℝ} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (ha : 1 / 2 < a) (ha1 : a < 1)
    (hm : MomentEquation a μ) (hφ : Modes.ConditionalFourierHyp a g (charFun μ)) :
    deriv (deriv g) 0 = curvaturePrefactor a * (ratio a - 1) :=
  actual_curvature_ratio_of_integrable ha ha1 hm hφ
    (AnalyticThresholdExteriorActual.integrable_rootWeight ha ha1)

/-- The ratio constructed from the actual H-series crosses one exactly once
on the full physical memory interval. -/
theorem actual_transitionCrossing : ∃ r, TransitionCrossing ratio r := by
  apply exists_transitionCrossing_of_deriv_pos
    AnalyticThresholdComparison.actualRatio_continuousOn
    AnalyticThresholdComparison.actualRatio_deriv_pos
  · intro a ha
    exact AnalyticThresholdExteriorActual.ratio_lt_one ha.1 ha.2
  · intro a ha
    exact AnalyticThresholdExteriorActual.ratio_gt_one ha.1 ha.2

/-- Global uniqueness and both curvature signs for a family of conditional
laws. The only hypotheses concern the named classical law inputs. In
particular, no root, integral formula, score bound or crossing is assumed. -/
theorem exists_unique_actual_curvature_transition
    (μ : ℝ → Measure ℝ) (g : ℝ → ℝ → ℝ)
    (hprob : ∀ a ∈ Ioo (1 / 2 : ℝ) 1, IsProbabilityMeasure (μ a))
    (hm : ∀ a ∈ Ioo (1 / 2 : ℝ) 1, MomentEquation a (μ a))
    (hφ : ∀ a ∈ Ioo (1 / 2 : ℝ) 1,
      Modes.ConditionalFourierHyp a (g a) (charFun (μ a))) :
    ∃ r ∈ Ioo (2 / 3 : ℝ) (69 / 100),
      deriv (deriv (g r)) 0 = 0 ∧
      (∀ a ∈ Ioo (1 / 2 : ℝ) 1, deriv (deriv (g a)) 0 = 0 ↔ a = r) ∧
      (∀ a ∈ Ioo (1 / 2 : ℝ) r, deriv (deriv (g a)) 0 < 0) ∧
      (∀ a ∈ Ioo r (1 : ℝ), 0 < deriv (deriv (g a)) 0) := by
  obtain ⟨r, hr⟩ := actual_transitionCrossing
  have hC : ∀ a ∈ Ioo (1 / 2 : ℝ) 1,
      deriv (deriv (g a)) 0 = curvaturePrefactor a * (ratio a - 1) := by
    intro a ha
    letI := hprob a ha
    exact actual_curvature_ratio ha.1 ha.2 (hm a ha) (hφ a ha)
  exact ⟨r, hr.root_mem, hr.curvature_signs
    (fun a ha => curvaturePrefactor_pos ha.1 ha.2) hC⟩

end Kagey131.PaperD.AnalyticThresholdFinal
