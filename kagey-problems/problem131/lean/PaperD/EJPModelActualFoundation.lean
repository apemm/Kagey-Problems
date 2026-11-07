import PaperD.EJPModelActualMoments
import PaperD.EJPModelFiniteMomentsUniform
import PaperD.EJPModelMeanLimit

open MeasureTheory Filter Set
open scoped Topology

namespace Kagey131.PaperD.ModelLimit

open ModelFiniteMoments ModelWeakMoments ModelMeanLimit

/-- Every moment of the actual superdiffusive weak limit is integrable. -/
theorem weakLimit_all_moments {a : ℝ} (ha : 1/2 < a) (ha1 : a ≤ 1)
    {μ : ProbabilityMeasure ℝ} (hμ : WeakLimit a (by linarith) ha1 μ) (k : ℕ) :
    Integrable (fun x : ℝ => x^k) (μ : Measure ℝ) := by
  obtain ⟨C, hC, hb⟩ := scaledMoment_even_uniform ha ha1 k
  have h2 := (weakLimit_even_moment (by linarith) ha1 hμ k hC.le hb).1
  apply integrable_of_square (by fun_prop)
  simpa only [← pow_mul, Nat.mul_comm k 2] using h2

/-- Finite moments converge to the corresponding moments of the actual weak limit. -/
theorem weakLimit_all_moments_converge {a : ℝ} (ha : 1/2 < a) (ha1 : a ≤ 1)
    {μ : ProbabilityMeasure ℝ} (hμ : WeakLimit a (by linarith) ha1 μ) (k : ℕ) :
    Tendsto (fun n => scaledMoment a (n+1) k) atTop
      (𝓝 (∫ x : ℝ, x^k ∂(μ : Measure ℝ))) := by
  obtain ⟨C, hC, hb⟩ := scaledMoment_even_uniform ha ha1 k
  exact weakLimit_moment_convergence (by linarith) ha1 hμ k hC.le hb

/-- The limit's normalization is derived from the actual finite mean. -/
theorem weakLimit_mean {a : ℝ} (ha : 1/2 < a) (ha1 : a ≤ 1)
    {μ : ProbabilityMeasure ℝ} (hμ : WeakLimit a (by linarith) ha1 μ) :
    (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 1/Real.Gamma (a+1) := by
  have h1 := weakLimit_all_moments_converge ha ha1 hμ 1
  have h2 := (scaledMoment_first_tendsto (by linarith : 0<a)).comp (tendsto_add_atTop_nat 1)
  simpa only [pow_one] using tendsto_nhds_unique h1 h2

theorem weakLimit_mean_pos {a : ℝ} (ha : 1/2 < a) (ha1 : a ≤ 1)
    {μ : ProbabilityMeasure ℝ} (hμ : WeakLimit a (by linarith) ha1 μ) :
    0 < ∫ x : ℝ, x ∂(μ : Measure ℝ) := by
  rw [weakLimit_mean ha ha1 hμ]
  exact one_div_pos.mpr (Real.Gamma_pos_of_pos (by linarith))

end Kagey131.PaperD.ModelLimit
