import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Exponential integrability from normalized even-moment bounds

This file turns factorial even-moment bounds into a genuine integrable
exponential, using Tonelli on the nonnegative cosh series. Analyticity of
the actual complex moment-generating integral is then a theorem.
-/

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology ENNReal

namespace Kagey131.PaperD.ModelMoment

/-- The normalized actual moments, rather than formal coefficients. -/
noncomputable def normalizedMoment (ν : Measure ℝ) (n : ℕ) : ℝ :=
  (∫ x : ℝ, x ^ n ∂ν) / n.factorial

@[simp] theorem normalizedMoment_zero (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    normalizedMoment ν 0 = 1 := by simp [normalizedMoment]

theorem integrable_cosh_of_even_moment_bound {ν : Measure ℝ} {C δ : ℝ}
    (hfinite : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (2 * n)) ν)
    (hbound : ∀ n : ℕ, normalizedMoment ν (2 * n) ≤ C ^ (2 * n))
    (hC : 0 < C) (hδ : 0 < δ) (hsmall : δ * C < 1) :
    Integrable (fun x : ℝ => Real.cosh (δ * x)) ν := by
  let f : ℕ → ℝ → ℝ := fun n x => (δ * x) ^ (2 * n) / (2 * n).factorial
  have hnn : ∀ n x, 0 ≤ f n x := by
    intro n x
    dsimp [f]
    rw [pow_mul]
    positivity
  have hfi : ∀ n, Integrable (f n) ν := by
    intro n
    simpa [f, mul_pow, div_eq_mul_inv, mul_assoc] using
      ((hfinite n).const_mul (δ ^ (2 * n))).div_const ((2 * n).factorial : ℝ)
  have hint (n : ℕ) : ∫ x, f n x ∂ν = δ ^ (2 * n) * normalizedMoment ν (2 * n) := by
    simp only [f, mul_pow, integral_div, integral_const_mul, normalizedMoment]
    ring
  let r := (δ * C) ^ 2
  have hr0 : 0 ≤ r := sq_nonneg _
  have hr1 : r < 1 := by dsimp [r]; nlinarith [mul_pos hδ hC]
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  have hle (n : ℕ) : (∫ x, f n x ∂ν) ≤ r ^ n := by
    rw [hint]
    calc
      _ ≤ δ ^ (2 * n) * C ^ (2 * n) :=
        mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg hδ.le _)
      _ = r ^ n := by rw [← mul_pow, ← pow_mul]
  have hpoint (x : ℝ) : ENNReal.ofReal (Real.cosh (δ * x)) = ∑' n, ENNReal.ofReal (f n x) := by
    rw [Real.cosh_eq_tsum]
    exact ENNReal.ofReal_tsum_of_nonneg (fun n => hnn n x) (Real.hasSum_cosh (δ * x)).summable
  refine ⟨(by fun_prop), (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => (Real.cosh_pos _).le)).2 ?_⟩
  calc
    (∫⁻ x, ENNReal.ofReal (Real.cosh (δ * x)) ∂ν) = ∑' n, ∫⁻ x, ENNReal.ofReal (f n x) ∂ν := by
      simp_rw [hpoint]
      exact lintegral_tsum (fun n => (hfi n).aemeasurable.ennreal_ofReal)
    _ = ∑' n, ENNReal.ofReal (∫ x, f n x ∂ν) := by
      apply tsum_congr
      intro n
      exact (ofReal_integral_eq_lintegral_ofReal (hfi n) (ae_of_all _ (hnn n))).symm
    _ ≤ ∑' n, ENNReal.ofReal (r ^ n) := ENNReal.tsum_le_tsum (fun n => ENNReal.ofReal_le_ofReal (hle n))
    _ < ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hr0 n) hgeom]
      exact ENNReal.ofReal_lt_top

theorem integrable_exp_abs_of_even_moment_bound {ν : Measure ℝ} {C δ : ℝ}
    (hfinite : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (2 * n)) ν)
    (hbound : ∀ n : ℕ, normalizedMoment ν (2 * n) ≤ C ^ (2 * n))
    (hC : 0 < C) (hδ : 0 < δ) (hsmall : δ * C < 1) :
    Integrable (fun x : ℝ => Real.exp (δ * |x|)) ν := by
  apply ((integrable_cosh_of_even_moment_bound hfinite hbound hC hδ hsmall).const_mul 2).mono'
    (by fun_prop)
  apply ae_of_all
  intro x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, Real.cosh_eq]
    linarith [Real.exp_pos (-(δ * x))]
  · rw [abs_of_nonpos hx, Real.cosh_eq, show δ * -x = -(δ * x) by ring]
    linarith [Real.exp_pos (δ * x)]

theorem mem_interior_integrableExpSet_of_exp_abs {ν : Measure ℝ} {δ t : ℝ}
    (hδ : 0 < δ) (hint : Integrable (fun x : ℝ => Real.exp (δ * |x|)) ν) (ht : |t| < δ) :
    t ∈ interior (integrableExpSet (id : ℝ → ℝ) ν) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (isOpen_Ioo.mem_nhds (abs_lt.mp ht))
  intro u hu
  apply hint.mono' (by fun_prop)
  apply ae_of_all
  intro x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    u * x ≤ |u * x| := le_abs_self _
    _ = |u| * |x| := abs_mul _ _
    _ ≤ δ * |x| := mul_le_mul_of_nonneg_right (abs_lt.mpr hu).le (abs_nonneg x)

theorem analyticAt_complexMGF_of_exp_abs {ν : Measure ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hint : Integrable (fun x : ℝ => Real.exp (δ * |x|)) ν)
    {z : ℂ} (hz : |z.re| < δ) : AnalyticAt ℂ (complexMGF (id : ℝ → ℝ) ν) z :=
  analyticAt_complexMGF (mem_interior_integrableExpSet_of_exp_abs hδ hint hz)

end Kagey131.PaperD.ModelMoment
