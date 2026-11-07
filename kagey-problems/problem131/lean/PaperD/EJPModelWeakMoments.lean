import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Moment bounds under ordinary weak convergence

Portmanteau transfers a uniform bound for a continuous nonnegative function
to the limiting law. In particular, finite even-moment bounds imply actual
moment integrability; weak convergence alone would not suffice.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Kagey131.PaperD.ModelWeakMoments

theorem integral_bound_of_weak_convergence
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hν : Tendsto ν atTop (𝓝 μ)) {f : ℝ → ℝ} (hf : Continuous f)
    (hfn : ∀ x, 0 ≤ f x) {C : ℝ} (hC : 0 ≤ C)
    (hfi : ∀ n, Integrable f (ν n : Measure ℝ))
    (hbound : ∀ n, (∫ x, f x ∂(ν n : Measure ℝ)) ≤ C) :
    Integrable f (μ : Measure ℝ) ∧ (∫ x, f x ∂(μ : Measure ℝ)) ≤ C := by
  have hl := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hf hfn (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν hG)
  have he (n : ℕ) : (∫⁻ x, ENNReal.ofReal (f x) ∂(ν n : Measure ℝ)) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi n) (ae_of_all _ hfn)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hb : (∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure ℝ)) ≤ ENNReal.ofReal C := by
    refine hl.trans (liminf_le_of_le ?_ ?_)
    · isBoundedDefault
    · intro b hbn
      obtain ⟨n, hn⟩ := hbn.exists
      exact hn.trans (he n)
  have hi : Integrable f (μ : Measure ℝ) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ hfn)).2
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hfn) hf.aestronglyMeasurable]
  simpa [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

theorem even_moment_bound_of_weak_convergence
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hν : Tendsto ν atTop (𝓝 μ)) (k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hfi : ∀ n, Integrable (fun x : ℝ => x^(2*k)) (ν n : Measure ℝ))
    (hbound : ∀ n, (∫ x : ℝ, x^(2*k) ∂(ν n : Measure ℝ)) ≤ C) :
    Integrable (fun x : ℝ => x^(2*k)) (μ : Measure ℝ) ∧
      (∫ x : ℝ, x^(2*k) ∂(μ : Measure ℝ)) ≤ C := by
  apply integral_bound_of_weak_convergence hν (by fun_prop) _ hC hfi hbound
  intro x
  rw [pow_mul]
  positivity

end Kagey131.PaperD.ModelWeakMoments
