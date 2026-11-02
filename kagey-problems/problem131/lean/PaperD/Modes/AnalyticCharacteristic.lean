import PaperD.Modes.AnalyticDensity
import PaperD.Modes.AnalyticExtension
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Probability-measure interface for the analytic density theorem

Continuity, unit norm bound, conjugate symmetry and decay are discharged for
the characteristic function of a probability law with a measurable density.
The remaining probabilistic inputs are the cited smoothing equation and
the Fourier inversion identifying the fair-start density.
-/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

theorem charFun_eq_entireFourier_neg_of_density {μ : Measure ℝ}
    {ρ : ℝ → ℝ≥0} (hρ : Measurable ρ)
    (hμ : μ = volume.withDensity (fun x => (ρ x : ℝ≥0∞))) (t : ℝ) :
    charFun μ t = entireFourier (fun x => (ρ x : ℂ)) (-t : ℝ) := by
  rw [charFun_apply_real, hμ, integral_withDensity_eq_integral_smul hρ]
  unfold entireFourier
  apply integral_congr_ae
  filter_upwards [] with x
  unfold entireFourierKernel
  simp only [NNReal.smul_def, Complex.real_smul, Complex.ofReal_neg]
  have he : (t:ℂ)*(x:ℂ)*Complex.I = (-Complex.I*(x:ℂ))*(-t:ℂ) := by ring
  rw [he, mul_comm]

theorem charFun_norm_tendsto_zero_of_density {μ : Measure ℝ}
    {ρ : ℝ → ℝ≥0} (hρ : Measurable ρ)
    (hμ : μ = volume.withDensity (fun x => (ρ x : ℝ≥0∞))) :
    Tendsto (fun t => ‖charFun μ t‖) atTop (𝓝 0) := by
  have h := (entireFourier_tendsto_atBot (fun x => (ρ x : ℂ))).comp tendsto_neg_atTop_atBot
  have hnorm := h.norm
  simpa only [Function.comp_def, ← charFun_eq_entireFourier_neg_of_density hρ hμ,
    norm_zero] using hnorm

/-- The characteristic-function conclusion of Lemma F.4, with precisely its
range of exponents. The source law is the conditional-first-step law. -/
theorem charFun_stretched_decay_of_density {a r : ℝ} (ha0 : 0 < a)
    (hr1 : 1 < r) (hrhi : r < 1/a) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ρ : ℝ → ℝ≥0} (hρ : Measurable ρ)
    (hμ : μ = volume.withDensity (fun x => (ρ x : ℝ≥0∞)))
    (hfp : ∀ t, 0 ≤ t → ‖charFun μ t‖ ≤ ∫ v in Ioo (0 : ℝ) 1,
      ‖charFun μ (t*v^a)‖ * ‖charFun μ (t*(1-v)^a)‖) :
    ∃ c > 0, ∀ t, ‖charFun μ t‖ ≤ 2 * Real.exp (-c*|t|^r) := by
  apply characteristic_stretched_decay continuous_charFun (fun t => norm_charFun_le_one t)
    _ ha0 (by linarith) _ (charFun_norm_tendsto_zero_of_density hρ hμ) hfp
  · intro t; simp only [charFun_neg, RCLike.norm_conj]
  · have h := (lt_div_iff₀ ha0).mp hrhi
    nlinarith

theorem fair_analytic_density_from_probability_measure {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ρ : ℝ → ℝ≥0} (hρ : Measurable ρ)
    (hμ : μ = volume.withDensity (fun x => (ρ x : ℝ≥0∞)))
    {g : ℝ → ℝ}
    (hfp : ∀ t, 0 ≤ t → ‖charFun μ t‖ ≤ ∫ v in Ioo (0 : ℝ) 1,
      ‖charFun μ (t*v^a)‖ * ‖charFun μ (t*(1-v)^a)‖)
    (hrep : g = normalizedFourierDensity (fun t => ((charFun μ t).re : ℂ)))
    (hi : Integrable g) (hne : ∃ x, g x ≠ 0) : AnalyticDensityRegularity g := by
  apply fair_analytic_density_of_smoothing ha0 ha1 continuous_charFun
    (fun t => norm_charFun_le_one t) _
    (charFun_norm_tendsto_zero_of_density hρ hμ) hfp hrep hi hne
  intro t
  simp only [charFun_neg, RCLike.norm_conj]

/-- Entire extension of the fair-start density, with standard characteristic
function facts discharged for the conditional probability law. -/
theorem fair_entire_extension_from_probability_measure {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ρ : ℝ → ℝ≥0} (hρ : Measurable ρ)
    (hμ : μ = volume.withDensity (fun x => (ρ x : ℝ≥0∞)))
    {g : ℝ → ℝ}
    (hfp : ∀ t, 0 ≤ t → ‖charFun μ t‖ ≤ ∫ v in Ioo (0 : ℝ) 1,
      ‖charFun μ (t*v^a)‖ * ‖charFun μ (t*(1-v)^a)‖)
    (hrep : g = normalizedFourierDensity (fun t => ((charFun μ t).re : ℂ))) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F (x:ℂ) = (g x : ℂ) := by
  let r := (1+a)/(2*a)
  have hr1 : 1 < r := by
    apply (lt_div_iff₀ (show 0 < 2*a by positivity)).mpr
    linarith
  have hrhi : r < 1/a := by
    apply (lt_div_iff₀ ha0).mpr
    have he : r*a = (1+a)/2 := by dsimp [r]; field_simp
    rw [he]
    linarith
  obtain ⟨c, hc, hcb⟩ := charFun_stretched_decay_of_density ha0 hr1 hrhi hρ hμ hfp
  have hp : Continuous (fun t => ((charFun μ t).re : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_re.comp continuous_charFun)
  have hcb' : ∀ t, ‖((charFun μ t).re : ℂ)‖ ≤ 2*Real.exp (-c*|t|^r) := by
    intro t
    have h := (Complex.abs_re_le_norm (charFun μ t)).trans (hcb t)
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h
  rw [hrep]
  exact entire_extension_normalizedFourierDensity hp
    (exponential_moments_of_stretched_bound hp hc hr1 hcb')

end Kagey131.PaperD.Modes
