import PaperD.EJPAnalyticThresholdComparison
import PaperD.EJPAnalyticThresholdWeightsParameter
import PaperD.EJPAnalyticThresholdRatio
import PaperD.EJPAnalyticThresholdMeasureContinuity

/-!
# Strict increase of the actual transition ratio

The parameter derivative of the canonical root kernel is supplied by proved
coefficient and implicit-root calculus. Consequently the actual mean has a
strictly positive covariance derivative. The actual ratio is continuous on
the closed transition band and has positive derivative throughout its interior.
There are no kernel-derivative, score, continuity, or ratio-derivative premises.
-/

open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace Kagey131.PaperD.AnalyticThresholdComparison
open Modes.AnalyticThreshold AnalyticThresholdRatio

/-- The rate in the memory-weight series is the actual logarithmic root derivative. -/
theorem actual_root_log_derivative_bounds {a : ℝ}
    (ha : (2/3 : ℝ) ≤ a) (ha1 : a ≤ 69/100) :
    0 < deriv Series.rootY a ∧
      deriv Series.rootY a / Series.rootY a ≤ 12*a/Series.G (Series.rootY a) := by
  have ha0 : (1/2 : ℝ) < a := by linarith
  have ha2 : a < 1 := by linarith
  exact ⟨Series.deriv_rootY_pos ha0 ha2,
    by rw [← Weights.rootRate_eq_log_deriv ha0 ha2]; exact (actual_rootRate_bounds ha ha1).2⟩

theorem rootKernel_uniform_bounds {a u : ℝ} (ha : a ∈ Icc (2/3 : ℝ) (69/100))
    (hu : u ∈ Icc (0 : ℝ) 1) :
    1 ≤ rootKernel a u ∧ rootKernel a u ≤ 2 ∧ |Weights.rootKa a u| ≤ 12 :=
  actual_kernel_bounds ha.1 ha.2 hu

theorem rootKernel_score_strictMono {a : ℝ} (ha : a ∈ Icc (2/3 : ℝ) (69/100)) :
    StrictMonoOn (logWeightScore (rootKernel a) (Weights.rootKa a) (3*a-2))
      (Ioo (0 : ℝ) 1) := actual_score_strictMono ha.1 ha.2

theorem rootKernel_parameter_hasDerivAt {a u : ℝ}
    (ha : a ∈ Icc (2/3 : ℝ) (69/100)) (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun b => rootKernel b u) (Weights.rootKa a u) a :=
  Weights.hasDerivAt_rootK ha.1 ha.2 hu.1 hu.2

/-- Dominated differentiation of the actual normalizer, including its exact derivative. -/
theorem weightNormalizer_hasDerivAt {a : ℝ} (ha : a ∈ Ioo (2/3 : ℝ) (69/100)) :
    HasDerivAt (fun b => weightNormalizer (analyticWeight rootKernel b))
      (∫ u, analyticWeight rootKernel a u *
        logWeightScore (rootKernel a) (Weights.rootKa a) (3*a-2) u ∂unitIntervalVolume) a := by
  exact (analyticWeight_integrals_hasDerivAt (B := 2) (C := 12) ha measurable_rootKernel
    (Weights.measurable_rootKa a)
    (fun b hb u hu => (rootKernel_uniform_bounds hb ⟨hu.1.le,hu.2.le⟩).1)
    (fun b hb u hu => (rootKernel_uniform_bounds hb ⟨hu.1.le,hu.2.le⟩).2.1)
    (fun b hb u hu => (rootKernel_uniform_bounds hb ⟨hu.1.le,hu.2.le⟩).2.2)
    (fun _ hu _ hb => rootKernel_parameter_hasDerivAt hb hu)).2.1

theorem weightNormalizer_differentiableAt {a : ℝ}
    (ha : a ∈ Ioo (2/3 : ℝ) (69/100)) :
    DifferentiableAt ℝ (fun b => weightNormalizer (analyticWeight rootKernel b)) a :=
  (weightNormalizer_hasDerivAt ha).differentiableAt

/-- All hypotheses of dominated differentiation are discharged for the actual kernel. -/
theorem actualMean_derivative_pos {a : ℝ} (ha : a ∈ Ioo (2/3 : ℝ) (69/100)) :
    HasDerivAt (analyticMean rootKernel)
      (covariance (fun u : ℝ => u)
        (logWeightScore (rootKernel a) (Weights.rootKa a) (3*a-2))
        (analyticProbability rootKernel a)) a ∧
      0 < deriv (analyticMean rootKernel) a :=
  actualMean_derivative_pos_of_kernelDerivative
    (fun _ hu _ hb => Weights.hasDerivAt_rootK hb.1 hb.2 hu.1 hu.2) ha

theorem rootKernel_parameter_continuousOn {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun b => rootKernel b u) (Icc (2/3 : ℝ) (69/100)) :=
  fun _ hb => (rootKernel_parameter_hasDerivAt hb hu).continuousAt.continuousWithinAt

/-- Includes both endpoints of the short band. -/
theorem ratio_continuousOn : ContinuousOn ratio (Icc (2/3 : ℝ) (69/100)) := by
  exact continuousOn_actualTransitionRatio
    (fun b _ => measurable_rootKernel b)
    (fun b hb u hu => (rootKernel_uniform_bounds hb ⟨hu.1.le,hu.2.le⟩).1)
    (fun _ hu => rootKernel_parameter_continuousOn hu)
    (fun b hb => (Series.differentiableAt_rootY (by linarith [hb.1])
      (by linarith [hb.2])).continuousAt.continuousWithinAt)

noncomputable def ratioDerivative (a : ℝ) : ℝ :=
  (2*(1+a)*Series.rootY a + (1+a)^2*deriv Series.rootY a) * analyticMean rootKernel a +
    (1+a)^2*Series.rootY a*deriv (analyticMean rootKernel) a

/-- The product rule applied to the actual root and actual normalized mean. -/
theorem ratio_hasDerivAt {a : ℝ} (ha : a ∈ Ioo (2/3 : ℝ) (69/100)) :
    HasDerivAt ratio (ratioDerivative a) a := by
  exact hasDerivAt_ratio
    (Series.differentiableAt_rootY (by linarith [ha.1]) (by linarith [ha.2])).hasDerivAt
    (actualMean_derivative_pos ha).1.differentiableAt.hasDerivAt

/-- The actual ratio has strictly positive derivative, with no differential premises. -/
theorem ratio_derivative_pos {a : ℝ} (ha : a ∈ Ioo (2/3 : ℝ) (69/100)) :
    0 < deriv ratio a := by
  rw [(ratio_hasDerivAt ha).deriv]
  exact Modes.AnalyticThreshold.ratio_derivative_pos (by linarith [ha.1])
    (Series.rootY_mem (by linarith [ha.1]) (by linarith [ha.2])).1
    (actualMean_mem_interval ⟨ha.1.le,ha.2.le⟩).1
    (actual_root_log_derivative_bounds ha.1.le ha.2.le).1.le
    (actualMean_derivative_pos ha).2.le

/-- Strict increase on the closed band, including comparisons to its endpoints. -/
theorem ratio_strictMonoOn : StrictMonoOn ratio (Icc (2/3 : ℝ) (69/100)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) ratio_continuousOn
  intro a ha
  exact ratio_derivative_pos (by simpa only [interior_Icc] using ha)

/-- Public interface for the final crossing theorem, including both endpoints. -/
theorem actualRatio_continuousOn :
    ContinuousOn AnalyticThresholdRatio.ratio (Icc (2/3 : ℝ) (69/100)) :=
  ratio_continuousOn

/-- Public interior derivative interface for the final crossing and slope arguments. -/
theorem actualRatio_deriv_pos : ∀ a ∈ Ioo (2/3 : ℝ) (69/100),
    0 < deriv AnalyticThresholdRatio.ratio a := fun _ ha => ratio_derivative_pos ha

theorem actualRatio_differentiableAt {a : ℝ}
    (ha : a ∈ Ioo (2/3 : ℝ) (69/100)) :
    DifferentiableAt ℝ AnalyticThresholdRatio.ratio a := (ratio_hasDerivAt ha).differentiableAt

theorem actualNormalizer_differentiableAt {a : ℝ}
    (ha : a ∈ Ioo (2/3 : ℝ) (69/100)) :
    DifferentiableAt ℝ (fun b => weightNormalizer (analyticWeight rootKernel b)) a :=
  weightNormalizer_differentiableAt ha

end Kagey131.PaperD.AnalyticThresholdComparison



