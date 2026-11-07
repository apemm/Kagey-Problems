import PaperD.EJPAnalyticThresholdWeightsRoot
import PaperD.EJPAnalyticThresholdMeasureDiff

/-!
# Comparison for the actual canonical root kernel

The coefficient-series bounds imply the strictly increasing score for the
constructed probability measure. The only intermediate analytic interface is
identification of rootKa with the parameter derivative of rootK; the final
application below will discharge it through the root-parameter calculus.
-/

open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace Kagey131.PaperD.AnalyticThresholdComparison
open Modes.AnalyticThreshold

/-- The actual logarithmic root rate is positive, with the manuscript bound. -/
theorem actual_rootRate_bounds {a : ℝ} (ha : (2/3 : ℝ) ≤ a) (ha1 : a ≤ 69/100) :
    0 < Weights.rootRate a ∧ Weights.rootRate a ≤ 12*a/Series.G (Series.rootY a) := by
  have ha0 : (1/2 : ℝ) < a := by linarith
  have ha2 : a < 1 := by linarith
  have hr := Series.rootY_mem ha0 ha2
  have hb := Weights.rootRate_balance ha0 ha2
  exact ⟨Weights.root_rate_pos ha hr.1 hr.2 (Series.H_rootY ha0 ha2) hb,
    Weights.root_rate_le ha hr.1.le hr.2 (Series.H_rootY ha0 ha2) hb⟩

/-- All constants used in dominated differentiation concern the actual kernel. -/
theorem actual_kernel_bounds {a u : ℝ} (ha : (2/3 : ℝ) ≤ a) (ha1 : a ≤ 69/100)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    1 ≤ Weights.rootK a u ∧ Weights.rootK a u ≤ 2 ∧ |Weights.rootKa a u| ≤ 12 := by
  have ha0 : (1/2 : ℝ) < a := by linarith
  have ha2 : a < 1 := by linarith
  have hr := Series.rootY_mem ha0 ha2
  exact ⟨Weights.one_le_K ha0 hr.1.le hr.2 (Series.H_rootY ha0 ha2) hu.1 hu.2,
    Weights.rootK_le_two ha ha1 hu.1 hu.2, Weights.abs_rootKa_le_twelve ha ha1 hu.1 hu.2⟩

/-- The exact positive lower bound comes from Ku, Ka, Kau and quotient calculus. -/
theorem actual_score_derivative_lower_bound {a u : ℝ}
    (ha : (2/3 : ℝ) ≤ a) (ha1 : a ≤ 69/100) (hu : u ∈ Ioo (0 : ℝ) 1) :
    (39/160 : ℝ) ≤ deriv
      (logWeightScore (Weights.rootK a) (Weights.rootKa a) (3*a-2)) u :=
  Weights.root_score_derivative_lower_bound ha ha1
    (Weights.rootRate_balance (by linarith) (by linarith)) hu.1 hu.2

theorem actual_score_strictMono {a : ℝ} (ha : (2/3 : ℝ) ≤ a) (ha1 : a ≤ 69/100) :
    StrictMonoOn (logWeightScore (Weights.rootK a) (Weights.rootKa a) (3*a-2))
      (Ioo (0 : ℝ) 1) := Weights.actual_score_strictMono ha ha1

/-- The mean is strictly between zero and one for the actual probability law. -/
theorem actualMean_mem_interval {a : ℝ} (ha : a ∈ Icc (2/3 : ℝ) (69/100)) :
    analyticMean Weights.rootK a ∈ Ioo (0 : ℝ) 1 := by
  have hK : ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ Weights.rootK a u :=
    fun u hu => (actual_kernel_bounds ha.1 ha.2 ⟨hu.1.le,hu.2.le⟩).1
  letI := analyticProbability_isProbability ha (Weights.measurable_rootK a) hK
  exact mean_mem_interval (weightedIntervalProbability_ae_mem _)
    (analyticProbability_full ha (Weights.measurable_rootK a) hK)

/-- Dominated differentiation and strict score increase for actual rootK.
The derivative interface is a separate, substantive coefficient-calculus input. -/
theorem actualMean_derivative_pos_of_kernelDerivative
    (hd : ∀ u ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Icc (2/3 : ℝ) (69/100),
      HasDerivAt (fun c => Weights.rootK c u) (Weights.rootKa b u) b)
    {a : ℝ} (ha : a ∈ Ioo (2/3 : ℝ) (69/100)) :
    HasDerivAt (analyticMean Weights.rootK)
      (covariance (fun u : ℝ => u)
        (logWeightScore (Weights.rootK a) (Weights.rootKa a) (3*a-2))
        (analyticProbability Weights.rootK a)) a ∧
      0 < deriv (analyticMean Weights.rootK) a := by
  exact analyticMean_derivative_pos (B := 2) (C := 12) ha Weights.measurable_rootK
    (Weights.measurable_rootKa a)
    (fun b hb u hu => (actual_kernel_bounds hb.1 hb.2 ⟨hu.1.le,hu.2.le⟩).1)
    (fun b hb u hu => (actual_kernel_bounds hb.1 hb.2 ⟨hu.1.le,hu.2.le⟩).2.1)
    (fun b hb u hu => (actual_kernel_bounds hb.1 hb.2 ⟨hu.1.le,hu.2.le⟩).2.2)
    hd (actual_score_strictMono ha.1.le ha.2.le)

end Kagey131.PaperD.AnalyticThresholdComparison
