import PaperD.Modes.NearOnePointwise
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The probability-measure input for the profile convergence theorem

Portmanteau converts an actual weak limit of probability measures with
densities into the interval-mass input used by the deterministic shape proof.
-/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology ENNReal

theorem density_interval_mass {μ : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x)
    (hμ : (μ : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a b : ℝ} (hab : a ≤ b) :
    ((μ : Measure ℝ) (Ioc a b)).toReal = ∫ x in a..b, f x := by
  rw [hμ, withDensity_apply _ measurableSet_Ioc, intervalIntegral.integral_of_le hab]
  exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0)
    hf.integrableOn.aestronglyMeasurable).symm

theorem interval_masses_of_weak_density {μ : ℕ → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ} {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, Integrable (F n)) (hf : Integrable f)
    (hF0 : ∀ n x, 0 ≤ F n x) (hf0 : ∀ x, 0 ≤ f x)
    (hμ : ∀ n, (μ n : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (F n x)))
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hweak : Tendsto μ atTop (𝓝 ν)) :
    ∀ a b, a < b → Tendsto (fun n => ∫ x in a..b, F n x)
      atTop (𝓝 (∫ x in a..b, f x)) := by
  intro a b hab
  have hnull : (ν : Measure ℝ) (frontier (Ioc a b)) = 0 := by
    rw [hν]
    apply withDensity_absolutelyContinuous
    rw [frontier_Ioc hab]
    exact ((finite_singleton b).insert a).measure_zero volume
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak hnull
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure ℝ) (Ioc a b))).comp hlim
  simpa only [Function.comp_def, density_interval_mass (hF _) (hF0 _) (hμ _) hab.le,
    density_interval_mass hf hf0 hν hab.le] using hreal

/-- Weak convergence and unimodality yield density convergence away from
the continuous strict limiting mode. -/
theorem off_mode_pointwise_of_weak_density {μ : ℕ → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ} {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {c : ℕ → ℝ} {m : ℝ}
    (hF : ∀ n, Integrable (F n)) (hf : Integrable f) (hfc : Continuous f)
    (hF0 : ∀ n x, 0 ≤ F n x) (hf0 : ∀ x, 0 ≤ f x)
    (hμ : ∀ n, (μ n : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (F n x)))
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hweak : Tendsto μ atTop (𝓝 ν)) (hshape : ∀ n, UnimodalAt (F n) (c n))
    (hmax : ∀ x, x ≠ m → f x < f m) :
    ∀ x, x ≠ m → Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
  off_mode_pointwise_of_interval_masses hF hfc hshape hmax
    (interval_masses_of_weak_density hF hf hF0 hf0 hμ hν hweak)

end Kagey131.PaperD.Modes
