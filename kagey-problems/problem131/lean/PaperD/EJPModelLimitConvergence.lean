import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace Kagey131.PaperD.ModelLimit

noncomputable def diracLaw (x : ℝ) : ProbabilityMeasure ℝ :=
  ⟨Measure.dirac x, inferInstance⟩

theorem tendsto_diracLaw {x : ℕ → ℝ} {y : ℝ} (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun n => diracLaw (x n)) atTop (𝓝 (diracLaw y)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  simpa [diracLaw, Function.comp_def] using f.continuous.continuousAt.tendsto.comp hx

noncomputable def productCharTest : (ℝ × ℝ) →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => Complex.exp ((p.2 * p.1 : ℝ) * Complex.I)) (by fun_prop) 1
    (fun p => (Complex.norm_exp_ofReal_mul_I (p.2 * p.1)).le)

theorem integral_productCharTest (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    (∫ p, productCharTest p ∂(μ.prod (diracLaw t) : ProbabilityMeasure (ℝ × ℝ))) =
      charFun (μ : Measure ℝ) t := by
  change (∫ p, productCharTest p ∂(μ : Measure ℝ).prod (Measure.dirac t)) = _
  rw [integral_prod]
  · simp only [integral_dirac]
    change (∫ x, Complex.exp ((t * x : ℝ) * Complex.I) ∂(μ : Measure ℝ)) = _
    simp only [charFun_apply_real, Complex.ofReal_mul]
  · exact productCharTest.integrable _

/-- Weak convergence permits a simultaneously moving Fourier frequency. -/
theorem charFun_tendsto_moving {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hν : Tendsto ν atTop (𝓝 μ)) {t : ℕ → ℝ} {s : ℝ}
    (ht : Tendsto t atTop (𝓝 s)) :
    Tendsto (fun n => charFun (ν n : Measure ℝ) (t n)) atTop
      (𝓝 (charFun (μ : Measure ℝ) s)) := by
  have hp := ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
    (hν.prodMk_nhds (tendsto_diracLaw ht))
  have hi := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hp productCharTest
  simpa only [Function.comp_apply, integral_productCharTest] using hi

/-- Pointwise characteristic convergence is enough; no uniform convergence premise is needed. -/
theorem charFun_tendsto_moving_of_pointwise {ν : ℕ → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ}
    (hν : ∀ s : ℝ, Tendsto (fun n => charFun (ν n : Measure ℝ) s) atTop
      (𝓝 (charFun (μ : Measure ℝ) s)))
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) {t : ℕ → ℝ} {s : ℝ}
    (ht : Tendsto t atTop (𝓝 s)) :
    Tendsto (fun n => charFun (ν (k n) : Measure ℝ) (t n)) atTop
      (𝓝 (charFun (μ : Measure ℝ) s)) :=
  charFun_tendsto_moving ((ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr hν).comp hk) ht

end Kagey131.PaperD.ModelLimit
