import PaperD.EJPModelMomentFixedPoint
import PaperD.EJPModelMomentEquation
import PaperD.EJPModelActualFoundation
import PaperD.EJPModelLimitFixedPoint
import PaperD.EJPModelRandomizedMoments

/-!
# Actual ERW weak-limit moment inputs

The fixed-point law, all moment integrability, and mean normalization are
derived from the actual finite ERW laws and their weak convergence. Thus
the Gamma-normalized GLRS recurrence has no distributional or moment input.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Kagey131.PaperD.ModelMoment

open ModelMoments ModelLimit
open AnalyticThresholdRandomization ModelRandomizedMoments AnalyticThresholdModel

theorem normalizedMoment_randomized {a : ℝ} (ha : 0 ≤ a) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (n : ℕ) :
    normalizedMoment (randomizedLaw a μ) n = gammaNormalizedMoment a μ n := by
  rw [normalizedMoment, integral_randomized_power ha μ n]
  rfl

/-- The original fixed point and ordinary finite moments suffice for the
entire old MomentEquation package; neither a GLRS recurrence nor an
analyticity/transform equation is an application premise. -/
theorem momentEquation_of_fixedPoint {a : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 1 / 2 < a) (ha1 : a ≤ 1) (hfix : μ = ModelFourier.fixedPointLaw a μ)
    (hfinite : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1 / Real.Gamma (a + 1)) : MomentEquation a μ := by
  have ha0 : 0 ≤ a := by linarith
  apply momentEquation_of_recurrence ha ha1
    (fun n => integrable_randomized_power ha0 (2 * n) (hfinite (2 * n)))
  have heq : normalizedMoment (randomizedLaw a μ) = gammaNormalizedMoment a μ :=
    funext (normalizedMoment_randomized ha0 μ)
  rw [heq]
  exact gammaNormalizedMoment_recurrence ha0 ha1 hfix hfinite hmean

/-- The actual weak limit satisfies the normalized GLRS recurrence. The only
foundational application input is weak convergence of the actual finite laws. -/
theorem actual_gammaNormalizedMoment_recurrence {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    {μ : ProbabilityMeasure ℝ} (hμ : WeakLimit a (by linarith) ha1.le μ) :
    MomentRecurrence a (gammaNormalizedMoment a (μ : Measure ℝ)) :=
  gammaNormalizedMoment_recurrence (by linarith) ha1.le
    (fixedPoint_of_weakLimit (by linarith) ha1 μ hμ)
    (weakLimit_all_moments ha ha1.le hμ) (weakLimit_mean ha ha1.le hμ)

theorem actual_gammaNormalizedMoment_bound {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    {μ : ProbabilityMeasure ℝ} (hμ : WeakLimit a (by linarith) ha1.le μ) (n : ℕ) :
    |gammaNormalizedMoment a (μ : Measure ℝ) n| ≤ (2 * a - 1)⁻¹ ^ n :=
  normalized_moment_abs_bound ha ha1.le (actual_gammaNormalizedMoment_recurrence ha ha1 hμ) n

/-- The natural GLRS recurrence for the actual randomized limit law. -/
theorem actual_normalizedMoment_recurrence {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    {μ : ProbabilityMeasure ℝ} (hμ : WeakLimit a (by linarith) ha1.le μ) :
    MomentRecurrence a (normalizedMoment (randomizedLaw a (μ : Measure ℝ))) := by
  have heq : normalizedMoment (randomizedLaw a (μ : Measure ℝ)) =
      gammaNormalizedMoment a (μ : Measure ℝ) := funext (normalizedMoment_randomized (by linarith) μ)
  rw [heq]
  exact actual_gammaNormalizedMoment_recurrence ha ha1 hμ

/-- Model.MomentEquation is fully derived for any ordinary weak limit of
the actual finite ERW laws. Weak convergence is the sole foundational input. -/
theorem actual_momentEquation {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    {μ : ProbabilityMeasure ℝ} (hμ : WeakLimit a (by linarith) ha1.le μ) :
    MomentEquation a (μ : Measure ℝ) :=
  momentEquation_of_fixedPoint ha ha1.le
    (fixedPoint_of_weakLimit (by linarith) ha1 μ hμ)
    (weakLimit_all_moments ha ha1.le hμ) (weakLimit_mean ha ha1.le hμ)

end Kagey131.PaperD.ModelMoment
