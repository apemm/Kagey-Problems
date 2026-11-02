import PaperD.Modes.BiasWeakTransferProbability
import PaperD.Modes.BiasWeakTransferAssembly

/-!
# The centred bias interval from ordinary weak probability convergence

The finite laws are the scaled atomic biased count laws. Their weak convergence
to the reflected-mixture density replaces every local-limit or window-limit
assumption in the final classification interface.
-/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology ENNReal

theorem biased_modes_centered_interval_of_weak_probability
    {a : ℝ} {φ : ℝ → ℂ} {h : ℝ → ℝ}
    {μ : ℝ → ℕ → ProbabilityMeasure ℝ} {ν : ℝ → ProbabilityMeasure ℝ}
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
    (hμ : ∀ q ∈ Icc (0 : ℝ) 1, ∀ n,
      (μ q n : Measure ℝ) = Measure.sum (fun k : ℤ =>
        ENNReal.ofReal (BiasedModes.mass ((1-a)/2) q (n+1) k) •
          Measure.dirac (biasedScaledPosition a n k)))
    (hν : ∀ q ∈ Icc (0 : ℝ) 1,
      (ν q : Measure ℝ) = volume.withDensity
        (fun x => ENNReal.ofReal (reflectedMixture h q x)))
    (hweak : ∀ q ∈ Icc (0 : ℝ) 1, Tendsto (μ q) atTop (𝓝 (ν q))) :
    ∃ b ∈ Icc (0 : ℝ) (1/2), ∀ q ∈ Icc (0 : ℝ) 1,
      ((∃ x y, x < y ∧ ∀ z, IsLocalMax (reflectedMixture h q) z ↔ z=x ∨ z=y) ↔
        b < q ∧ q < 1-b) ∧
      (¬(b < q ∧ q < 1-b) → ∃ m, UnimodalAt (reflectedMixture h q) m ∧
        ∀ x, IsLocalMax (reflectedMixture h q) x ↔ x=m) := by
  apply biased_modes_centered_interval_of_interval_masses ha ha1 hφ hbound hsymm
    hdecay hfp hi hn hp hcond hrep
  intro q hq
  exact biased_interval_masses_of_weak_probability
    (by linarith : 0 ≤ (1-a)/2) (by linarith : (1-a)/2 ≤ 1)
    hq.1 hq.2 (reflectedMixture_integrable hi q)
    (reflectedMixture_nonneg hn hq) (hμ q hq) (hν q hq) (hweak q hq)

end Kagey131.PaperD.Modes
