import PaperD.FL5_Hyp
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Paper F, track FL5: Lemma 2.3(iv) from Lemma 2.3(ii)

Lemma 2.3(iv) of Paper F: if `G` has the characteristic function `exp(K_α(-iθ)^α)` and a
continuous integrable density `g`, then
`I_α = ∫ g² = (1/2π) ∫ e^{-σ_α|θ|^α} dθ = Γ(1+1/α)/(π σ_α^{1/α})`.

The paper's proof is: `|E e^{iθG}|² = e^{-σ_α|θ|^α}` (the real part of `(-iθ)^α` is
`|θ|^α cos(πα/2)`), Plancherel's theorem, and the substitution `x = σ_α θ^α`. Here Plancherel's
theorem is not needed as a hypothesis: since the characteristic function is integrable, Mathlib's
Fourier inversion theorem (`Continuous.fourierInv_fourier_eq`) and Fubini
(`VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip`) give the Parseval identity directly.

So the conjunct `∫ g² = I_α` of `StableLimitHyp` is derived (`stableLimitHyp_of_char`) from
the weaker `StableCharHyp`, which assumes only Lemma 2.3(ii).
-/

namespace Kagey131.PaperD.FL5

open Filter Topology MeasureTheory Real FourierTransform

/-- The real part of `(-iθ)^α` (principal branch) is `|θ|^α cos(πα/2)` for `θ ≠ 0`. -/
theorem re_negI_cpow {α θ : ℝ} (hθ : θ ≠ 0) :
    ((-(Complex.I * θ)) ^ (α : ℂ)).re = |θ| ^ α * Real.cos (π * α / 2) := by
  set x : ℂ := -(Complex.I * θ) with hx
  have hx0 : x ≠ 0 := by simp [hx, hθ, Complex.I_ne_zero]
  have hnorm : ‖x‖ = |θ| := by simp [hx]
  have harg : Real.cos (α * Complex.arg x) = Real.cos (π * α / 2) := by
    rcases lt_or_gt_of_ne hθ with h | h
    · have e : x = ((-θ : ℝ) : ℂ) * Complex.I := by simp [hx]; ring
      rw [e, Complex.arg_real_mul _ (by linarith), Complex.arg_I]
      ring_nf
    · have e : x = ((θ : ℝ) : ℂ) * (-Complex.I) := by simp [hx, mul_comm]
      rw [e, Complex.arg_real_mul _ h, Complex.arg_neg_I, mul_neg, Real.cos_neg]
      ring_nf
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.exp_re]
  have hre : (Complex.log x * α).re = Real.log ‖x‖ * α := by
    simp [Complex.mul_re, Complex.log_re]
  have him : (Complex.log x * α).im = Complex.arg x * α := by
    simp [Complex.mul_im, Complex.log_im]
  rw [hre, him, hnorm, Real.rpow_def_of_pos (abs_pos.mpr hθ), mul_comm (Complex.arg x), harg]

theorem cos_pi_alpha_half_neg {α : ℝ} (h1 : 1 < α) (h2 : α < 2) : Real.cos (π * α / 2) < 0 :=
  Real.cos_neg_of_pi_div_two_lt_of_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- `|exp(K_α(-iθ)^α)| = exp(-(σ_α/2)|θ|^α)` (proof of Lemma 2.3(ii), (iv)). -/
theorem norm_stableChar {α : ℝ} (h1 : 1 < α) (h2 : α < 2) (θ : ℝ) :
    ‖stableChar α θ‖ = Real.exp (-(sigmaα α / 2) * |θ| ^ α) := by
  unfold stableChar
  rw [Complex.norm_exp]
  rcases eq_or_ne θ 0 with rfl | hθ
  · have : (α : ℂ) ≠ 0 := by exact_mod_cast (by linarith : α ≠ 0)
    simp [Complex.zero_cpow this, Real.zero_rpow (by linarith : α ≠ 0)]
  · rw [Complex.re_ofReal_mul, re_negI_cpow hθ]
    congr 1
    have hc := cos_pi_alpha_half_neg h1 h2
    unfold sigmaα
    rw [abs_of_neg hc]
    ring

/-- `x ↦ exp(-b|x|^p)` is integrable on `ℝ` (`b, p > 0`). -/
theorem integrable_exp_neg_mul_abs_rpow {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
    Integrable fun x : ℝ => Real.exp (-b * |x| ^ p) := by
  rw [← integrableOn_univ, ← @Set.Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  have hI : IntegrableOn (fun x : ℝ => Real.exp (-b * |x| ^ p)) (Set.Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (by norm_num) hp hb).congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    simp [abs_of_pos (Set.mem_Ioi.mp hx)]
  refine ⟨?_, hI⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simp only [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iio, neg_zero]
  exact hI

/-- `∫_ℝ exp(-b|x|^p) dx = 2 b^{-1/p} Γ(1/p + 1)`. -/
theorem integral_exp_neg_mul_abs_rpow {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
    ∫ x : ℝ, Real.exp (-b * |x| ^ p) = 2 * (b ^ (-1 / p) * Real.Gamma (1 / p + 1)) := by
  rw [integral_comp_abs (f := fun x => Real.exp (-b * x ^ p)), integral_exp_neg_mul_rpow hp hb]

/-- **Parseval for the stable density** (the Plancherel step of Lemma 2.3(iv)), from Fourier
inversion: if `g` is continuous and integrable and its Fourier transform is integrable, then
`∫ g² = ∫ |𝓕 g|²`. -/
theorem integral_sq_eq_integral_norm_fourier_sq {g : ℝ → ℝ} (hgc : Continuous g)
    (hgint : Integrable g) (hF : Integrable (𝓕 (fun z => (g z : ℂ)))) :
    ∫ z, g z ^ 2 = ∫ w, ‖𝓕 (fun z => (g z : ℂ)) w‖ ^ 2 := by
  set G : ℝ → ℂ := fun z => (g z : ℂ) with hG
  have hGint : Integrable G := hgint.ofReal
  have hGc : Continuous G := Complex.continuous_ofReal.comp hgc
  have hinv : 𝓕⁻ (𝓕 G) = G := hGc.fourierInv_fourier_eq hGint hF
  have hP := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ (E := ℂ))
    Real.continuous_fourierChar (L := innerₗ ℝ) (μ := volume) (ν := volume) continuous_inner
    hGint hF
  rw [flip_innerₗ] at hP
  change ∫ ξ, innerSL ℂ (𝓕 G ξ) (𝓕 G ξ) = ∫ x, innerSL ℂ (G x) (𝓕⁻ (𝓕 G) x) at hP
  rw [hinv] at hP
  simp only [innerSL_apply_apply, RCLike.inner_apply, Complex.mul_conj'] at hP
  have h1 : ∫ ξ, ((‖𝓕 G ξ‖ ^ 2 : ℝ) : ℂ) = ∫ x, ((g x ^ 2 : ℝ) : ℂ) := by
    convert hP using 2 with ξ x
    · push_cast; ring
    · funext x
      simp only [hG, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_pow]
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  rw [integral_complex_ofReal, integral_complex_ofReal] at h1
  exact (Complex.ofReal_injective h1).symm

/-- **Lemma 2.3(iv)**: if `g` is a continuous integrable density with
`∫ e^{iθz} g(z) dz = exp(K_α(-iθ)^α)`, then `∫ g² = I_α = Γ(1+1/α)/(π σ_α^{1/α})`. -/
theorem integral_sq_eq_stableI {α : ℝ} (h1 : 1 < α) (h2 : α < 2) {g : ℝ → ℝ}
    (hgc : Continuous g) (hgint : Integrable g)
    (hchar : ∀ θ : ℝ, ∫ z : ℝ, Complex.exp (Complex.I * θ * z) * (g z : ℂ) = stableChar α θ) :
    ∫ z, g z ^ 2 = stableI α := by
  set G : ℝ → ℂ := fun z => (g z : ℂ) with hG
  have hGint : Integrable G := hgint.ofReal
  have hF : ∀ w, 𝓕 G w = stableChar α (-2 * π * w) := by
    intro w
    rw [Real.fourier_real_eq_integral_exp_smul, ← hchar]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul, hG]
    congr 2
    push_cast
    ring
  have hσ := sigmaα_pos h1 h2
  have hpi := Real.pi_pos
  set c : ℝ := sigmaα α / 2 * (2 * π) ^ α with hc
  have hc0 : 0 < c := by positivity
  have hFn : ∀ w, ‖𝓕 G w‖ = Real.exp (-c * |w| ^ α) := by
    intro w
    rw [hF, norm_stableChar h1 h2]
    congr 1
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2),
      abs_of_pos hpi, Real.mul_rpow (by positivity) (abs_nonneg _), hc]
    ring
  have hFc : Continuous (𝓕 G) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hGint
  have hFint : Integrable (𝓕 G) := by
    refine (integrable_exp_neg_mul_abs_rpow (by linarith) hc0).mono'
      hFc.aestronglyMeasurable (Eventually.of_forall fun w => (hFn w).le)
  rw [integral_sq_eq_integral_norm_fourier_sq hgc hgint hFint]
  show ∫ w, ‖𝓕 G w‖ ^ 2 = _
  have e2 : ∀ w, ‖𝓕 G w‖ ^ 2 = Real.exp (-(2 * c) * |w| ^ α) := by
    intro w
    rw [hFn, sq, ← Real.exp_add]
    ring_nf
  simp_rw [e2]
  rw [integral_exp_neg_mul_abs_rpow (by linarith) (by positivity)]
  have hcc : 2 * c = sigmaα α * (2 * π) ^ α := by rw [hc]; ring
  rw [hcc, Real.mul_rpow hσ.le (by positivity), ← Real.rpow_mul (by positivity),
    show α * (-1 / α) = -1 by field_simp, Real.rpow_neg_one,
    show (-1 / α) = -(1 / α) by ring, Real.rpow_neg hσ.le, add_comm (1 / α) 1]
  unfold stableI
  have : 0 < sigmaα α ^ (1 / α) := Real.rpow_pos_of_pos hσ _
  field_simp

/-- **Lemma 2.3(ii)** for the runs of Section 2 (`1 < α < 2`), the paper's own statement:
`(τ_m - mμ)/m^{1/α}` converges in law to a variable `G` with characteristic function
`exp(K_α(-iθ)^α)`, which has a bounded, uniformly continuous density `g` with `g(z) → 0` as
`|z| → ∞`. This is `StableLimitHyp` without its conjunct `∫ g² = I_α` (Lemma 2.3(iv)), which is
proved from it (`stableLimitHyp_of_char`). -/
def StableCharHyp (α : ℝ) (hα : 1 < α) : Prop :=
  ∃ g : ℝ → ℝ, UniformContinuous g ∧ (∀ z, 0 ≤ g z) ∧ (∃ G0, ∀ z, g z ≤ G0) ∧
    Tendsto g atTop (𝓝 0) ∧ Tendsto g atBot (𝓝 0) ∧ Integrable g ∧ ∫ z, g z = 1 ∧
    (∀ θ : ℝ, ∫ z : ℝ, Complex.exp (Complex.I * θ * z) * (g z : ℂ) = stableChar α θ) ∧
    ∀ x : ℝ, Tendsto (fun m : ℕ => cdf ((runLaw α (by linarith)).u m)
      ⌈(m : ℝ) * μα α + x * (m : ℝ) ^ (1 / α)⌉₊) atTop (𝓝 (∫ z in Set.Iio x, g z))

/-- Lemma 2.3(iv) follows from Lemma 2.3(ii): `StableCharHyp → StableLimitHyp`. -/
theorem stableLimitHyp_of_char {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (h : StableCharHyp α hα1) : StableLimitHyp α hα1 := by
  obtain ⟨g, hguc, hg0, hG0, hgtop, hgbot, hgint, hg1, hchar, hcdf⟩ := h
  exact ⟨g, hguc, hg0, hG0, hgtop, hgbot, hgint, hg1, hchar,
    integral_sq_eq_stableI hα1 hα2 hguc.continuous hgint hchar, hcdf⟩

end Kagey131.PaperD.FL5
