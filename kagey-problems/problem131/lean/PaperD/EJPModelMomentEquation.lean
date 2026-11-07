import PaperD.EJPModelMomentRecurrence
import PaperD.EJPAnalyticThresholdModel
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Discharging Model.MomentEquation from actual finite moments

The actual randomized probability law is used throughout. The inputs are
finite even moments and the published normalized moment recurrence. Growth,
exponential integrability, analyticity, and the transform ODE are derived.
-/

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology ENNReal

namespace Kagey131.PaperD.ModelMoment

open ModelMoments AnalyticThresholdModel AnalyticThresholdRandomization

theorem analytic_re_charFun_of_exp_abs {ν : Measure ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hint : Integrable (fun x : ℝ => Real.exp (δ * |x|)) ν) (t : ℝ) :
    AnalyticAt ℝ (fun u => (charFun ν u).re) t := by
  have hM := analyticAt_complexMGF_of_exp_abs hδ hint
    (z := (t : ℂ) * I) (by simpa using hδ)
  have hg : AnalyticAt ℂ (fun z : ℂ => complexMGF (id : ℝ → ℝ) ν (z * I)) (t : ℂ) :=
    hM.comp (f := fun z : ℂ => z * I) (analyticAt_id.mul analyticAt_const)
  simpa only [complexMGF_id_mul_I] using hg.re_ofReal

theorem analytic_im_charFun_of_exp_abs {ν : Measure ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hint : Integrable (fun x : ℝ => Real.exp (δ * |x|)) ν) (t : ℝ) :
    AnalyticAt ℝ (fun u => (charFun ν u).im) t := by
  have hM := analyticAt_complexMGF_of_exp_abs hδ hint
    (z := (t : ℂ) * I) (by simpa using hδ)
  have hg : AnalyticAt ℂ (fun z : ℂ => complexMGF (id : ℝ → ℝ) ν (z * I)) (t : ℂ) :=
    hM.comp (f := fun z : ℂ => z * I) (analyticAt_id.mul analyticAt_const)
  simpa only [complexMGF_id_mul_I] using hg.im_ofReal

theorem hasDerivAt_charFun_of_exp_abs {ν : Measure ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hint : Integrable (fun x : ℝ => Real.exp (δ * |x|)) ν) (t : ℝ) :
    HasDerivAt (charFun ν)
      (deriv (complexMGF (id : ℝ → ℝ) ν) ((t : ℂ) * I) * I) t := by
  have hM := (analyticAt_complexMGF_of_exp_abs hδ hint
    (z := (t : ℂ) * I) (by simpa using hδ)).differentiableAt.hasDerivAt
  have h := hM.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const I)
  simpa only [Function.comp_def, id_eq, one_mul, complexMGF_id_mul_I] using h.comp_ofReal

/-- The old Model.MomentEquation input is now a conclusion of finite moments
and the natural GLRS coefficient recurrence. -/
theorem momentEquation_of_recurrence {a : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (ha : 1 / 2 < a) (ha1 : a ≤ 1)
    (hfinite : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (2 * n)) (randomizedLaw a μ))
    (hm : MomentRecurrence a (normalizedMoment (randomizedLaw a μ))) :
    MomentEquation a μ := by
  let ν := randomizedLaw a μ
  let M := complexMGF (id : ℝ → ℝ) ν
  have hδ : 0 < (2 * a - 1) / 2 := by linarith
  have hint := integrable_exp_abs_of_recurrence ha ha1 hfinite hm
  have hd (t : ℝ) : HasDerivAt (charFun ν) (deriv M ((t : ℂ) * I) * I) t :=
    hasDerivAt_charFun_of_exp_abs hδ hint t
  have hr (t : ℝ) : HasDerivAt (realTransform a μ) (deriv M ((t : ℂ) * I) * I).re t := by
    convert! Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hd t) using 1
  have hi (t : ℝ) : HasDerivAt (imagTransform a μ) (deriv M ((t : ℂ) * I) * I).im t := by
    convert! Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hd t) using 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    exact analytic_re_charFun_of_exp_abs hδ hint t
  · intro t ht
    exact analytic_im_charFun_of_exp_abs hδ hint t
  · have hmean : (∫ x : ℝ, x ∂ν) = 1 := by simpa [normalizedMoment] using hm.one
    have hj := iteratedDeriv_complexMGF_zero hδ hint 1
    have hM0 : deriv M 0 = 1 := by
      simp only [iteratedDeriv_one, pow_one, integral_ofReal] at hj
      change deriv M 0 = Complex.ofReal (∫ x : ℝ, x ∂ν) at hj
      simpa only [hmean, Complex.ofReal_one] using hj
    simpa [hM0] using (hi 0).deriv
  · intro t
    have hode := complexMGF_ode_of_recurrence ha ha1 hfinite hm ((t : ℂ) * I)
      (by simpa [momentStrip] using hδ)
    have hneg : M (-((t : ℂ) * I)) = (starRingEnd ℂ) (charFun ν t) := by
      change complexMGF (id : ℝ → ℝ) ν (-((t : ℂ) * I)) = _
      rw [show -((t : ℂ) * I) = ((-t : ℝ) : ℂ) * I by simp, complexMGF_id_mul_I, charFun_neg]
    have hd' : Complex.ofReal (deriv (realTransform a μ) t) + Complex.ofReal (deriv (imagTransform a μ) t) * I =
        deriv M ((t : ℂ) * I) * I := by
      rw [(hr t).deriv, (hi t).deriv]
      exact Complex.re_add_im _
    have hc : (realTransform a μ t : ℂ) + imagTransform a μ t * I = M ((t : ℂ) * I) := by
      change _ = complexMGF (id : ℝ → ℝ) ν ((t : ℂ) * I)
      rw [complexMGF_id_mul_I]
      exact Complex.re_add_im _
    have hcn : (realTransform a μ t : ℂ) - imagTransform a μ t * I = M (-((t : ℂ) * I)) := by
      rw [hneg]
      apply Complex.ext <;> simp [realTransform, imagTransform, ν]
    rw [hc, hd', hcn]
    convert! hode using 1 <;> ring

end Kagey131.PaperD.ModelMoment
