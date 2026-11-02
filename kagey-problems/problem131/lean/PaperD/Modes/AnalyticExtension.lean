import PaperD.Modes.AnalyticDerivatives
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# An actual entire extension of the real Fourier density

Taking the real part on the real axis is implemented by Schwarz reflection,
so the conclusion is an entire complex function agreeing with the density,
not merely real analyticity.
-/

namespace Kagey131.PaperD.Modes

open Set MeasureTheory

theorem entire_extension_normalizedFourierDensity {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖)) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ x : ℝ, F (x:ℂ) = (normalizedFourierDensity φ x : ℂ) := by
  let H := entireFourier φ
  let F : ℂ → ℂ := fun z => (H z + star (H (star z)))/2/(2*Real.pi)
  have hH : Differentiable ℂ H := differentiable_entireFourier hφ hw
  have hstar : Differentiable ℂ (fun z => star (H (star z))) := by
    intro z
    simpa only [Function.comp_def, starRingEnd_apply, star_star] using
      (hH (star z)).conj_conj
  refine ⟨F, (hH.add hstar).div_const _ |>.div_const _, ?_⟩
  intro x
  change (H (x:ℂ) + star (H (star (x:ℂ))))/2/(2*Real.pi) =
    (((H (x:ℂ)).re / (2*Real.pi) : ℝ):ℂ)
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.re_eq_add_conj]
  push_cast
  rfl

end Kagey131.PaperD.Modes
