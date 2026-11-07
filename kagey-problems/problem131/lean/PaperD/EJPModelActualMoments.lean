import PaperD.EJPModelMomentConvergence
import PaperD.EJPModelFiniteMomentsBounds
import PaperD.EJPModelLimitLaw

open MeasureTheory Filter Set Finset
open scoped Topology ENNReal

namespace Kagey131.PaperD.ModelLimit

open ModelFiniteMoments ModelWeakMoments

theorem integrable_scaledMeasure (a : ℝ) (n : ℕ) (f : ℝ → ℝ) :
    Integrable f (scaledMeasure a n) := by
  by_cases hn : n = 0
  · subst n
    simpa [scaledMeasure] using (integrable_dirac (by simp) : Integrable f (Measure.dirac (0:ℝ)))
  rw [scaledMeasure, if_neg hn, integrable_finsetSum_measure]
  intro b hb
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem integral_finiteLaw_pow (a : ℝ) (ha : -1 ≤ a) (ha1 : a ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (∫ x : ℝ, x^k ∂(finiteLaw a ha ha1 n : Measure ℝ)) = scaledMoment a n k := by
  rw [show (finiteLaw a ha ha1 n : Measure ℝ) = scaledMeasure a n from rfl,
    integral_scaledMeasure a ha ha1 hn, scaledMoment_eq]
  rfl

/-- Bounds for the actual finite walk give moments of its ordinary weak limit. -/
theorem weakLimit_even_moment {a : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1)
    {μ : ProbabilityMeasure ℝ} (hμ : WeakLimit a ha ha1 μ)
    (k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, 1 ≤ n → scaledMoment a n (2*k) ≤ C) :
    Integrable (fun x : ℝ => x^(2*k)) (μ : Measure ℝ) ∧
      (∫ x : ℝ, x^(2*k) ∂(μ : Measure ℝ)) ≤ C := by
  have ht : Tendsto (fun n => finiteLaw a ha ha1 (n+1)) atTop (𝓝 μ) :=
    hμ.comp (tendsto_add_atTop_nat 1)
  apply even_moment_bound_of_weak_convergence ht k hC
  · intro n
    exact integrable_scaledMeasure a (n+1) _
  · intro n
    rw [integral_finiteLaw_pow a ha ha1 (by omega)]
    exact hb (n+1) (by omega)

theorem weakLimit_moment_convergence {a : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1)
    {μ : ProbabilityMeasure ℝ} (hμ : WeakLimit a ha ha1 μ)
    (k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, 1 ≤ n → scaledMoment a n (2*k) ≤ C) :
    Tendsto (fun n => scaledMoment a (n+1) k) atTop
      (𝓝 (∫ x : ℝ, x^k ∂(μ : Measure ℝ))) := by
  have ht : Tendsto (fun n => finiteLaw a ha ha1 (n+1)) atTop (𝓝 μ) :=
    hμ.comp (tendsto_add_atTop_nat 1)
  have he : ∀ x : ℝ, (x^k)^2 = x^(2*k) := by intro x; rw [← pow_mul, Nat.mul_comm]
  have hc := integral_tendsto_of_square_bound ht (f := fun x : ℝ => x^k)
    (by fun_prop) hC (fun n => integrable_scaledMeasure a (n+1) _) (fun n => by
      simp only [he]
      rw [integral_finiteLaw_pow a ha ha1 (by omega)]
      exact hb (n+1) (by omega))
  have hex (n : ℕ) : (∫ x : ℝ, x^k ∂(finiteLaw a ha ha1 (n+1) : Measure ℝ)) =
      scaledMoment a (n+1) k := integral_finiteLaw_pow a ha ha1 (by omega) k
  simpa only [hex] using hc

end Kagey131.PaperD.ModelLimit
