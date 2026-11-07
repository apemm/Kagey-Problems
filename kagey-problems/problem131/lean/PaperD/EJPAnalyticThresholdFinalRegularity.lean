import PaperD.EJPAnalyticThresholdFinal
import PaperD.EJPAnalyticThresholdComparisonRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace Kagey131.PaperD.AnalyticThresholdFinalRegularity
open Modes.AnalyticThreshold AnalyticThresholdRatio AnalyticThresholdModel AnalyticThresholdFinal

/-- Every factor of the actual curvature prefactor is differentiable on the
interior of the short transition band. No regularity premise is supplied. -/
theorem curvaturePrefactor_differentiableAt {a : ℝ}
    (ha : a ∈ Ioo (2 / 3 : ℝ) (69 / 100)) :
    DifferentiableAt ℝ curvaturePrefactor a := by
  have ha₀ : (1 / 2 : ℝ) < a := by linarith [ha.1]
  have ha₁ : a < 1 := by linarith [ha.2]
  have hYpos := (Series.rootY_mem ha₀ ha₁).1
  have hY := Series.differentiableAt_rootY ha₀ ha₁
  have hpow : DifferentiableAt ℝ (fun b => Series.rootY b ^ (1 / 2 : ℝ)) a :=
    hY.rpow_const (Or.inl hYpos.ne')
  have hZ := AnalyticThresholdComparison.actualNormalizer_differentiableAt ha
  have hgammaBase : DifferentiableAt ℝ Real.Gamma (3 - 3*a) := by
    apply Real.differentiableAt_Gamma
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hlinear : DifferentiableAt ℝ (fun b : ℝ => 3 - 3*b) a := by fun_prop
  have hgamma : DifferentiableAt ℝ (fun b : ℝ => Real.Gamma (3 - 3*b)) a :=
    DifferentiableAt.comp (f := fun b : ℝ => 3 - 3*b) (g := Real.Gamma) a hgammaBase hlinear
  have hconst : DifferentiableAt ℝ (fun _ : ℝ => Real.pi) a := by fun_prop
  have hden : Real.pi * Real.Gamma (3 - 3*a) ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero (Real.Gamma_pos_of_pos (by linarith)).ne'
  exact ((hY.mul hpow).mul hZ).div (hconst.mul hgamma) hden

/-- At the actual transition, the curvature has a strictly positive memory
derivative. The laws need no parameter-regularity hypothesis: their actual
curvature identity on a neighborhood supplies the differentiability. -/
theorem actual_curvature_derivative_pos_at_transition
    (μ : ℝ → Measure ℝ) (g : ℝ → ℝ → ℝ)
    (hprob : ∀ a ∈ Ioo (1 / 2 : ℝ) 1, IsProbabilityMeasure (μ a))
    (hm : ∀ a ∈ Ioo (1 / 2 : ℝ) 1, MomentEquation a (μ a))
    (hφ : ∀ a ∈ Ioo (1 / 2 : ℝ) 1,
      Modes.ConditionalFourierHyp a (g a) (charFun (μ a)))
    {r : ℝ} (hr : TransitionCrossing ratio r) :
    HasDerivAt (fun a => deriv (deriv (g a)) 0)
      (curvaturePrefactor r * deriv ratio r) r ∧
      0 < deriv (fun a => deriv (deriv (g a)) 0) r := by
  have hrphys : r ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith [hr.root_mem.1, hr.root_mem.2]
  have hC : (fun a => deriv (deriv (g a)) 0) =ᶠ[𝓝 r]
      (fun a => curvaturePrefactor a * (ratio a - 1)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hrphys] with a ha
    let : IsProbabilityMeasure (μ a) := hprob a ha
    exact actual_curvature_ratio ha.1 ha.2 (hm a ha) (hφ a ha)
  exact curvature_derivative_at_root hr.value (curvaturePrefactor_pos hrphys.1 hrphys.2)
    (curvaturePrefactor_differentiableAt hr.root_mem).hasDerivAt
    (AnalyticThresholdComparison.actualRatio_differentiableAt hr.root_mem).hasDerivAt
    (AnalyticThresholdComparison.actualRatio_deriv_pos r hr.root_mem) hC
end Kagey131.PaperD.AnalyticThresholdFinalRegularity



