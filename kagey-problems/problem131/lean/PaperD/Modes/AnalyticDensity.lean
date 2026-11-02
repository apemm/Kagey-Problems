import PaperD.Modes.AnalyticDecay
import PaperD.Modes.AnalyticDerivatives
import PaperD.Modes.StrictCore
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Analytic-density package for Paper D, Lemma F.4

The probabilistic input is the characteristic-function smoothing inequality
from the cited distributional fixed point, together with its standard
characteristic-function properties and Riemann--Lebesgue decay. The density
is identified by Fourier inversion. No conclusion about analyticity,
strictness, or derivative behavior is assumed.
-/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology

theorem analytic_deriv_no_flat {g : ℝ → ℝ} (ha : AnalyticOnNhd ℝ g univ)
    (hflat : NoFlatInterval g) (hlim : Tendsto (deriv g) atTop (𝓝 0)) :
    NoFlatInterval (deriv g) := by
  apply analytic_nonconstant_no_flat ha.deriv
  by_contra hn
  have heq : deriv g = fun _ => deriv g 0 := by
    funext x
    by_contra h
    exact hn ⟨x, 0, h⟩
  have hzero : deriv g 0 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (heq ▸ hlim)
  have hd : Differentiable ℝ g := fun x => (ha x (mem_univ _)).differentiableAt
  have hconst : ∀ x, g x = g 0 :=
    fun x => is_const_of_deriv_eq_zero hd (by intro y; rw [heq, hzero]) x 0
  exact hflat 0 1 (by norm_num) (fun x _ => hconst x)

/-- The analytic and derivative facts used by the strict shape theorems. -/
structure AnalyticDensityRegularity (g : ℝ → ℝ) : Prop where
  analytic : AnalyticOnNhd ℝ g univ
  noFlat : NoFlatInterval g
  noFlatDeriv : NoFlatInterval (deriv g)
  derivContinuous : Continuous (deriv g)
  secondContinuous : Continuous (deriv (deriv g))
  derivBounded : ∃ C : ℝ, ∀ x, |deriv g x| ≤ C
  secondBounded : ∃ C : ℝ, ∀ x, |deriv (deriv g) x| ≤ C
  derivTop : Tendsto (deriv g) atTop (𝓝 0)
  derivBot : Tendsto (deriv g) atBot (𝓝 0)
  secondTop : Tendsto (deriv (deriv g)) atTop (𝓝 0)
  secondBot : Tendsto (deriv (deriv g)) atBot (𝓝 0)

/-- Assemble Lemma F.4 and its derivative consequences from the smoothing and
Fourier-inversion inputs. The conclusion is stronger than mere no-flatness. -/
theorem analytic_density_of_smoothing {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {φ ψ : ℝ → ℂ} {g : ℝ → ℝ}
    (hφ : Continuous φ) (hbound : ∀ t, ‖φ t‖ ≤ 1)
    (hsymm : ∀ t, ‖φ (-t)‖ = ‖φ t‖)
    (hdecay : Tendsto (fun t => ‖φ t‖) atTop (𝓝 0))
    (hfp : ∀ t, 0 ≤ t → ‖φ t‖ ≤ ∫ v in Ioo (0 : ℝ) 1,
      ‖φ (t*v^a)‖ * ‖φ (t*(1-v)^a)‖)
    (hψ : Continuous ψ) (hdom : ∀ t, ‖ψ t‖ ≤ ‖φ t‖)
    (hrep : g = normalizedFourierDensity ψ) (hi : Integrable g)
    (hne : ∃ x, g x ≠ 0) : AnalyticDensityRegularity g := by
  let r := (1+a)/(2*a)
  have hr : 1 < r := by
    apply (lt_div_iff₀ (show 0 < 2*a by positivity)).mpr
    linarith
  have har : a*r < 1 := by
    have he : a*r = (1+a)/2 := by dsimp [r]; field_simp
    rw [he]
    linarith
  obtain ⟨c, hc, hcb⟩ := characteristic_stretched_decay hφ hbound hsymm ha0
    (by linarith : 0 < r) har hdecay hfp
  have hw := exponential_moments_of_stretched_bound hψ hc hr
    (fun t => (hdom t).trans (hcb t))
  have hg : AnalyticOnNhd ℝ g univ :=
    analytic_density_of_fourier_representation hψ hw (by intro x; rw [hrep]; rfl)
  have hφ1 := continuous_fourierDerivativeWeight hψ
  have hw1 := exponential_moments_fourierDerivativeWeight hψ hw
  have hφ2 := continuous_fourierDerivativeWeight hφ1
  have hw2 := exponential_moments_fourierDerivativeWeight hφ1 hw1
  have hd : deriv g = normalizedFourierDensity (fourierDerivativeWeight ψ) := by
    rw [hrep, deriv_normalizedFourierDensity hψ hw]
  have hdd : deriv (deriv g) =
      normalizedFourierDensity (fourierDerivativeWeight (fourierDerivativeWeight ψ)) := by
    rw [hd, deriv_normalizedFourierDensity hφ1 hw1]
  have hn : NoFlatInterval g := analytic_integrable_no_flat hg hi hne
  have hdt : Tendsto (deriv g) atTop (𝓝 0) := by
    rw [hd]
    exact (normalizedFourierDensity_tendsto _).1
  refine ⟨hg, hn, analytic_deriv_no_flat hg hn hdt, ?_, ?_, ?_, ?_, hdt, ?_, ?_, ?_⟩
  · rw [hd]; exact normalizedFourierDensity_continuous hφ1 hw1
  · rw [hdd]; exact normalizedFourierDensity_continuous hφ2 hw2
  · rw [hd]; exact normalizedFourierDensity_bounded _
  · rw [hdd]; exact normalizedFourierDensity_bounded _
  · rw [hd]; exact (normalizedFourierDensity_tendsto _).2
  · rw [hdd]; exact (normalizedFourierDensity_tendsto _).1
  · rw [hdd]; exact (normalizedFourierDensity_tendsto _).2

/-- The fair-start characteristic function is the real part of the conditional
one. Only the conditional characteristic function is required to satisfy the
smoothing inequality. -/
theorem fair_analytic_density_of_smoothing {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {φ : ℝ → ℂ} {g : ℝ → ℝ}
    (hφ : Continuous φ) (hbound : ∀ t, ‖φ t‖ ≤ 1)
    (hsymm : ∀ t, ‖φ (-t)‖ = ‖φ t‖)
    (hdecay : Tendsto (fun t => ‖φ t‖) atTop (𝓝 0))
    (hfp : ∀ t, 0 ≤ t → ‖φ t‖ ≤ ∫ v in Ioo (0 : ℝ) 1,
      ‖φ (t*v^a)‖ * ‖φ (t*(1-v)^a)‖)
    (hrep : g = normalizedFourierDensity (fun t => ((φ t).re : ℂ)))
    (hi : Integrable g) (hne : ∃ x, g x ≠ 0) : AnalyticDensityRegularity g := by
  apply analytic_density_of_smoothing ha0 ha1 hφ hbound hsymm hdecay hfp
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hφ)) _ hrep hi hne
  intro t
  simpa only [Function.comp_def, Complex.norm_real, Real.norm_eq_abs] using Complex.abs_re_le_norm (φ t)

end Kagey131.PaperD.Modes
