import PaperD.Modes.BiasLimitTransfer
import PaperD.Modes.AnalyticExtension

/-! The entire-extension clause of Lemma F.4 for every initial bias. -/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology

theorem biased_entire_extension_of_smoothing {a q : ℝ} {φ : ℝ → ℂ} {g : ℝ → ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hφ : Continuous φ) (hbound : ∀ t, ‖φ t‖ ≤ 1)
    (hsymm : ∀ t, ‖φ (-t)‖ = ‖φ t‖)
    (hdecay : Tendsto (fun t => ‖φ t‖) atTop (𝓝 0))
    (hfp : ∀ t, 0 ≤ t → ‖φ t‖ ≤ ∫ v in Ioo (0 : ℝ) 1,
      ‖φ (t*v^a)‖ * ‖φ (t*(1-v)^a)‖)
    (hrep : g = normalizedFourierDensity (biasedCharacteristic q φ)) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F (x:ℂ) = (g x : ℂ) := by
  let r := (1+a)/(2*a)
  have hr : 1 < r := by
    apply (lt_div_iff₀ (show 0 < 2*a by positivity)).mpr
    linarith
  have har : a*r < 1 := by
    have he : a*r = (1+a)/2 := by dsimp [r]; field_simp
    rw [he]
    linarith
  obtain ⟨c,hc,hcb⟩ := characteristic_stretched_decay hφ hbound hsymm ha0
    (by linarith : 0 < r) har hdecay hfp
  have hp := biasedCharacteristic_continuous hφ q
  have hcb' : ∀ t, ‖biasedCharacteristic q φ t‖ ≤ 2*Real.exp (-c*|t|^r) :=
    fun t => (biasedCharacteristic_norm_le hq0 hq1 hsymm t).trans (hcb t)
  rw [hrep]
  exact entire_extension_normalizedFourierDensity hp
    (exponential_moments_of_stretched_bound hp hc hr hcb')

end Kagey131.PaperD.Modes
