import PaperD.Modes.BiasIntervalAssembly
import PaperD.Modes.BiasWeakTransfer
import PaperD.Modes.BiasWeakTransferCounts

/-! The actual-model centred-interval assembly needs only fixed-window
mass limits. No pointwise lattice local limit is used. -/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology

/-- Smoothing regularity, conditional unimodality and fixed-window limits
imply the exact centred open interval of bimodal initial biases. -/
theorem biased_modes_centered_interval_of_interval_masses {a : ℝ} {φ : ℝ → ℂ} {h : ℝ → ℝ}
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
    (hmass : ∀ q ∈ Icc (0 : ℝ) 1,
      BiasedIntervalMassHyp ((1-a)/2) q a (reflectedMixture h q)) :
    ∃ b ∈ Icc (0 : ℝ) (1/2), ∀ q ∈ Icc (0 : ℝ) 1,
      ((∃ x y, x < y ∧ ∀ z, IsLocalMax (reflectedMixture h q) z ↔ z=x ∨ z=y) ↔
        b < q ∧ q < 1-b) ∧
      (¬(b < q ∧ q < 1-b) → ∃ m, UnimodalAt (reflectedMixture h q) m ∧
        ∀ x, IsLocalMax (reflectedMixture h q) x ↔ x=m) := by
  have hε : 0 < (1-a)/2 := by linarith
  have hε1 : (1-a)/2 < 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hlim : ∀ q ∈ Icc (0 : ℝ) 1,
      BiasedWindowLimitHyp ((1-a)/2) q a (reflectedMixture h q) := by
    intro q hq
    exact biased_window_limits_of_interval_masses ha0 (hmass q hq)
  have hreg : ∀ q ∈ Icc (0 : ℝ) 1, AnalyticDensityRegularity (reflectedMixture h q) := by
    intro q hq
    obtain ⟨x,hx⟩ := reflectedMixture_positive_somewhere hn hp hq
    exact analytic_density_of_smoothing ha0 ha1 hφ hbound hsymm hdecay hfp
      (biasedCharacteristic_continuous hφ q)
      (biasedCharacteristic_norm_le hq.1 hq.2 hsymm)
      (hrep q hq) (reflectedMixture_integrable hi q) ⟨x,hx.ne'⟩
  have hcont : ∀ q ∈ Icc (0 : ℝ) 1, Continuous (reflectedMixture h q) := by
    intro q hq
    exact continuous_iff_continuousAt.mpr
      (fun x => ((hreg q hq).analytic x (mem_univ x)).continuousAt)
  have hh : Continuous h := by
    have he : reflectedMixture h 1 = h := by
      funext x
      simp [reflectedMixture]
    simpa only [he] using hcont 1 (by simp)
  have hdom : ∀ x, 0 ≤ x → h (-x) ≤ h x := by
    apply conditional_window_limit_reflection_dominance hε.le hε1.le hh
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
    exact biased_window_limit_noRightValley hε hε1 hq.1 hq.2 ha0
      (hcont q ⟨by linarith [hq.1],hq.2⟩) (hlim q ⟨by linarith [hq.1],hq.2⟩)
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
      (biased_window_limit_noTwoValleys hε hε1 hq.1 hq.2 ha0 (hcont q hq) (hlim q hq)) (hreg q hq).noFlat

end Kagey131.PaperD.Modes
