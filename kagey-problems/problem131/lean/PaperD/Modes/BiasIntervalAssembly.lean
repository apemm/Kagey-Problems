import PaperD.Modes.BiasIntervalTransfer
import PaperD.Modes.BiasMixtureIntervalModes

/-!
# The complete interval of bimodal initial biases

This entry derives the model-specific reflection dominance, half-line shape,
analyticity and global mode bound. Its inputs are the existing conditional
unimodality theorem, characteristic-function smoothing and Fourier inversion,
and the actual lattice local limits. No interval or mode-count claim is an input.
-/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology

theorem reflectedMixture_integrable {h : ℝ → ℝ} (hi : Integrable h) (q : ℝ) :
    Integrable (reflectedMixture h q) := by
  exact (hi.const_mul q).add (hi.comp_neg.const_mul (1-q))

theorem reflectedMixture_nonneg {h : ℝ → ℝ} (hn : ∀ x, 0 ≤ h x)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (x : ℝ) : 0 ≤ reflectedMixture h q x :=
  add_nonneg (mul_nonneg hq.1 (hn x))
    (mul_nonneg (sub_nonneg.mpr hq.2) (hn (-x)))

theorem reflectedMixture_positive_somewhere {h : ℝ → ℝ}
    (hn : ∀ x, 0 ≤ h x) (hp : ∃ x, 0 < h x)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : ∃ x, 0 < reflectedMixture h q x := by
  obtain ⟨x,hx⟩ := hp
  rcases eq_or_lt_of_le hq.1 with rfl | hq0
  · exact ⟨-x,by simpa [reflectedMixture] using hx⟩
  · refine ⟨x,?_⟩
    exact add_pos_of_pos_of_nonneg (mul_pos hq0 hx)
      (mul_nonneg (sub_nonneg.mpr hq.2) (hn (-x)))

/-- Every superdiffusive memory has one centred open interval of bimodal
biases. Outside, including its two endpoints, the density has one local mode.
The interval is allowed to be empty. -/
theorem biased_modes_centered_interval_of_smoothing {a : ℝ} {φ : ℝ → ℂ} {h : ℝ → ℝ}
    (ha : 1/2 < a) (ha1 : a < 1)
    (hφ : Continuous φ) (hbound : ∀ t, ‖φ t‖ ≤ 1)
    (hsymm : ∀ t, ‖φ (-t)‖ = ‖φ t‖)
    (hdecay : Tendsto (fun t => ‖φ t‖) atTop (𝓝 0))
    (hfp : ∀ t, 0 ≤ t → ‖φ t‖ ≤ ∫ v in Ioo (0 : ℝ) 1,
      ‖φ (t*v^a)‖ * ‖φ (t*(1-v)^a)‖)
    (hi : Integrable h) (hn : ∀ x, 0 ≤ h x) (hp : ∃ x, 0 < h x)
    (hcond : ∃ m, UnimodalAt h m)
    (hrep : ∀ q ∈ Icc (0 : ℝ) 1,
      reflectedMixture h q = normalizedFourierDensity (biasedCharacteristic q φ))
    (hlim : ∀ q ∈ Icc (0 : ℝ) 1,
      BiasedLocalLimitHyp ((1-a)/2) q a (reflectedMixture h q)) :
    ∃ b ∈ Icc (0 : ℝ) (1/2), ∀ q ∈ Icc (0 : ℝ) 1,
      ((∃ x y, x < y ∧ ∀ z, IsLocalMax (reflectedMixture h q) z ↔ z=x ∨ z=y) ↔
        b < q ∧ q < 1-b) ∧
      (¬(b < q ∧ q < 1-b) → ∃ m, UnimodalAt (reflectedMixture h q) m ∧
        ∀ x, IsLocalMax (reflectedMixture h q) x ↔ x=m) := by
  have hε : 0 < (1-a)/2 := by linarith
  have hε1 : (1-a)/2 < 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hreg : ∀ q ∈ Icc (0 : ℝ) 1, AnalyticDensityRegularity (reflectedMixture h q) := by
    intro q hq
    obtain ⟨x,hx⟩ := reflectedMixture_positive_somewhere hn hp hq
    exact analytic_density_of_smoothing ha0 ha1 hφ hbound hsymm hdecay hfp
      (biasedCharacteristic_continuous hφ q)
      (biasedCharacteristic_norm_le hq.1 hq.2 hsymm)
      (hrep q hq) (reflectedMixture_integrable hi q) ⟨x,hx.ne'⟩
  have hdom : ∀ x, 0 ≤ x → h (-x) ≤ h x := by
    apply conditional_limit_reflection_dominance hε.le hε1.le ha0
    · have he : reflectedMixture h 1 = h := by
        funext x
        simp [reflectedMixture]
      simpa only [he] using hlim 1 (by simp)
    · have he : reflectedMixture h 0 = fun x => h (-x) := by
        funext x
        simp [reflectedMixture]
      simpa only [he] using hlim 0 (by simp)
  obtain ⟨m,hm⟩ := hcond
  apply reflectedMixture_classification_interval hdom hm.no_strictValley
  · intro q hq
    exact biased_limit_noRightValley hε hε1 hq.1 hq.2
      (hlim q ⟨by linarith [hq.1],hq.2⟩)
  · intro q hq
    exact continuous_iff_continuousAt.mpr
      (fun x => ((hreg q hq).analytic x (mem_univ x)).continuousAt)
  · intro q _
    exact reflectedMixture_integrable hi q
  · intro q hq
    exact reflectedMixture_nonneg hn hq
  · intro q hq
    exact reflectedMixture_positive_somewhere hn hp hq
  · intro q hq
    exact (hreg q hq).noFlat
  · intro q hq
    exact NoTwoValleys.no_three
      (biased_limit_noTwoValleys hε hε1 hq.1 hq.2 (hlim q hq)) (hreg q hq).noFlat

end Kagey131.PaperD.Modes
