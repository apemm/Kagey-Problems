import PaperD.FL5_LampLaplace

/-!
# Paper F, track FL5: Theorem 2.9 (the local Lamperti law), final staged form

With Lerch's theorem as a named hypothesis, Step 1 of the proof is complete
(`step1b_of_lerch`), so the reduction `N C_N → f(1/2) = 4 ∫_0^∞ t g(t)² dt` rests only on the
named hypotheses `GnedenkoLLTHyp` (Lemma A.4(ii), classical), `StablePosHyp` (the paper's
own Lemma A.4(i), assumed) and `LerchHyp` (classical) (`thm_lamperti_center_limit`).
Theorem 2.9 itself (`N C_N → (2/π) tan(πα/2)`) needs in addition Step 4 (`Step4Claim`,
`thm_lamperti_of_step4`); Step 4 is proved in `FL5_Step4b`, and `StablePosHyp` in
`FL5_LemmaA4b`, so `FL5_Final` states Theorem 2.9 with classical hypotheses only.
-/

namespace Kagey131.PaperD.FL5

open Filter Topology Real

/-- **Theorem 2.9, Steps 1 and 2 and the substitution of Step 3**: for `0 < α < 1` and a fresh start,
`N C_N → f(1/2) = 4 ∫_0^∞ t g(t)² dt`, where `g` is the density of the stable limit `G` of
Lemma A.4(i) and `f(y) = ∫_0^∞ r g(yr) g((1-y)r) dr`. -/
theorem thm_lamperti_center_limit {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hGn : GnedenkoLLTHyp)
    (hLerch : LerchHyp) {g : ℝ → ℝ} (hSt : StablePosHyp α hα0 g) :
    Tendsto (fun h : ℕ => ((2 * h : ℕ) : ℝ) * (runLaw α hα0).centerSum (runLaw α hα0) h)
      atTop (𝓝 (ratioDensity g (1 / 2))) := by
  obtain ⟨hguc, hg0, hgz, ⟨G0, hgle⟩, _, _, _, hlap, _⟩ := id hSt
  have h1b := step1b_of_lerch hα0 hα1 hg0 hgle hguc.continuous hgz hLerch hlap
  exact thm_lamperti_reduction hα0 hα1 hGn hSt h1b

/-- **Theorem 2.9** (`thm:lamperti`), given the paper's Step 4 (`f(1/2) = ℓ_α(1/2)`):
`N C_N → ℓ_α(1/2) = (2/π) tan(πα/2)`. -/
theorem thm_lamperti_of_step4 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hGn : GnedenkoLLTHyp)
    (hLerch : LerchHyp) {g : ℝ → ℝ} (hSt : StablePosHyp α hα0 g) (h4 : Step4Claim α g) :
    Tendsto (fun h : ℕ => ((2 * h : ℕ) : ℝ) * (runLaw α hα0).centerSum (runLaw α hα0) h)
      atTop (𝓝 (2 / π * Real.tan (π * α / 2))) := by
  have := thm_lamperti_center_limit hα0 hα1 hGn hLerch hSt
  rwa [h4, lamperti_half hα0 hα1] at this

end Kagey131.PaperD.FL5
