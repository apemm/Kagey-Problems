import PaperD.U2_LandauDensity
import PaperD.U2_LandauClassL

/-!
# Paper D, Appendix C.2: `e^B` is the characteristic function of the Landau law, of class L

With `f_L` proved to be a probability density (`U2_LandauDensity`), Mathlib's Fourier inversion
gives the rest of the paragraph "The function `e^B` is a characteristic function of class L"
of Appendix C.2, without Lévy's continuity theorem:

* `integral_exp_mul_fL` : `∫ e^{itλ} f_L(λ) dλ = e^{B(t)}` for every real `t`;
* `charFun_landauLaw` : the characteristic function (Mathlib's `charFun`) of the law with density
  `f_L` is `e^B`;
* `charFun_landauLaw_selfDecomposable` : for `0 < c < 1`, `φ(t) = φ(ct)·φ_c(t)` where `φ_c` is the
  characteristic function of the image of the law under `λ ↦ (1-c)λ + (1-c)log(1-c) + c log c`,
  i.e. the law is self-decomposable (class L).
-/

namespace Kagey131.PaperD.U2

open Complex Finset Filter Topology MeasureTheory Set
open scoped Real FourierTransform

noncomputable section

/-- **`e^B` is the Fourier transform of `f_L`**: if `f_L` is integrable, then for every real `t`,
`∫ e^{itλ} f_L(λ) dλ = e^{B(t)}`. -/
theorem integral_exp_mul_fL (hint : Integrable fL) (t : ℝ) :
    ∫ lam, cexp (((t * lam : ℝ) : ℂ) * I) * (fL lam : ℂ) = cexp (landauB t) := by
  set g : ℝ → ℂ := fun t => cexp (landauB t) with hg
  have hgc : Continuous g := by have := continuous_landauB; fun_prop
  have hpi := Real.pi_pos
  have hF : 𝓕 g = fun ξ => (2 * π : ℂ) * (fL (2 * π * ξ) : ℂ) := by
    funext ξ; exact fourier_exp_landauB ξ
  have hFint : Integrable (𝓕 g) := by
    rw [hF]
    have h1 : Integrable (fun ξ : ℝ => fL (2 * π * ξ)) :=
      hint.comp_mul_left' (by positivity)
    exact h1.ofReal.const_mul _
  have hinv := integrable_exp_landauB.fourierInv_fourier_eq hFint (v := t) hgc.continuousAt
  change 𝓕⁻ (𝓕 g) t = g t at hinv
  rw [Real.fourierInv_eq', hF] at hinv
  set h : ℝ → ℂ := fun lam => cexp (((t * lam : ℝ) : ℂ) * I) * (fL lam : ℂ) with hh
  have hcongr : (fun v : ℝ => cexp (((2 * π * inner ℝ v t : ℝ) : ℂ) * I)
      • ((2 * π : ℂ) * (fL (2 * π * v) : ℂ))) = fun v => (2 * π : ℂ) * h (2 * π * v) := by
    funext v
    simp only [hh, smul_eq_mul, RCLike.inner_apply, conj_trivial]
    rw [show 2 * π * (t * v) = t * (2 * π * v) by ring]
    ring
  rw [hcongr, integral_const_mul, Measure.integral_comp_mul_left] at hinv
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), Complex.real_smul] at hinv
  have e : (2 * π : ℂ) * (((2 * π)⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast; field_simp
  rw [← mul_assoc, e, one_mul] at hinv
  exact hinv

/-- **The characteristic function of the Landau law is `e^B`** (Mathlib's `charFun`). -/
theorem charFun_landauLaw (hL : LandauDensityHyp) (t : ℝ) :
    charFun (landauLaw hL : Measure ℝ) t = cexp (landauB t) := by
  rw [charFun_apply_real, ← integral_exp_mul_fL (integrable_fL hL) t, landauLaw,
    ProbabilityMeasure.coe_mk,
    integral_withDensity_eq_integral_toReal_smul continuous_fL.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  congr 1; funext lam
  rw [ENNReal.toReal_ofReal (hL.1 lam), Complex.real_smul]
  push_cast
  ring_nf

/-- **The Landau law is self-decomposable (class L)** (Appendix C.2): for `0 < c < 1` and real `t`,
`φ(t) = φ(ct) · φ_c(t)`, where `φ` is the characteristic function of the Landau law `μ` and `φ_c`
that of the image of `μ` under `λ ↦ (1-c)λ + (1-c)log(1-c) + c log c`. -/
theorem charFun_landauLaw_selfDecomposable (hL : LandauDensityHyp) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) (t : ℝ) :
    charFun (landauLaw hL : Measure ℝ) t
      = charFun (landauLaw hL : Measure ℝ) (c * t)
        * charFun ((landauLaw hL : Measure ℝ).map
            (fun lam => (1 - c) * lam + ((1 - c) * Real.log (1 - c) + c * Real.log c))) t := by
  set κ : ℝ := (1 - c) * Real.log (1 - c) + c * Real.log c with hκ
  have hmeas : Measurable (fun lam : ℝ => (1 - c) * lam + κ) := by fun_prop
  have hmap : charFun ((landauLaw hL : Measure ℝ).map (fun lam => (1 - c) * lam + κ)) t
      = cexp (landauB ((1 - c) * t)) * cexp ((t : ℂ) * I * (κ : ℂ)) := by
    rw [charFun_apply_real, integral_map hmeas.aemeasurable (by fun_prop)]
    have : (fun x : ℝ => cexp ((t : ℂ) * (((1 - c) * x + κ : ℝ) : ℂ) * I))
        = fun x : ℝ => cexp ((t : ℂ) * I * (κ : ℂ)) * cexp ((((1 - c) * t : ℝ) : ℂ) * (x : ℂ) * I) := by
      funext x
      rw [← Complex.exp_add]
      congr 1
      push_cast; ring
    rw [this, integral_const_mul, ← charFun_apply_real, charFun_landauLaw]
    ring
  rw [hmap, charFun_landauLaw, charFun_landauLaw, exp_landauB_classL hc0 hc1 t]
  ring

end

end Kagey131.PaperD.U2
