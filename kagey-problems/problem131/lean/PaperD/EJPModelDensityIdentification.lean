import PaperD.EJPModelFourier
import PaperD.EJPModelFourierInversion
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Fourier normalization and the actual fair symmetrization

The first identity changes variables in the actual Bochner integral. It
relates mathlib's `exp(-2πitx)` convention to the manuscript's `1/(2π)`
normalization. The symmetrized law is an explicit probability mixture of
the conditional law and its reflection, with characteristic function equal
to the real part of the conditional characteristic function.
-/

namespace Kagey131.PaperD.ModelFourier

open MeasureTheory Set Filter Complex
open scoped Topology ENNReal FourierTransform RealInnerProductSpace

/-- Exact change of variables, including the complex normalization constant. -/
theorem fourier_scaled_eq_entireFourier (φ : ℝ → ℂ) (x : ℝ) :
    𝓕 (fun t : ℝ => φ (2 * Real.pi * t)) x =
      ((2 * Real.pi)⁻¹ : ℝ) • Modes.entireFourier φ (x : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ t : ℝ, Modes.entireFourierKernel φ (x : ℂ) ((2 * Real.pi) * t) := by
      apply integral_congr_ae
      exact ae_of_all _ fun t => by
        dsimp only [Modes.entireFourierKernel]
        simp only [smul_eq_mul]
        congr 2
        push_cast
        ring
    _ = _ := by
      rw [Measure.integral_comp_mul_left]
      rw [abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi))]
      rfl

/-- The real Fourier inverse in mathlib's convention is the normalized
Fourier density used throughout the analytic-threshold argument. -/
theorem fourier_scaled_re_eq_normalizedFourierDensity (φ : ℝ → ℂ) :
    (fun x : ℝ => (𝓕 (fun t : ℝ => φ (2 * Real.pi * t)) x).re) =
      Modes.normalizedFourierDensity φ := by
  funext x
  rw [fourier_scaled_eq_entireFourier]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Modes.normalizedFourierDensity]
  ring

/-- The actual fair law is the equally weighted conditional law and its
reflection. No density or Fourier representation is part of its definition. -/
noncomputable def fairLaw (μ : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / 2 : ℝ) • μ +
    ENNReal.ofReal (1 / 2 : ℝ) • μ.map (fun x : ℝ => -x)

theorem fairLaw_isProbability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (fairLaw μ) := by
  have : IsProbabilityMeasure (μ.map (fun x : ℝ => -x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  constructor
  simp only [fairLaw, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem charFun_reflectedLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    charFun (μ.map (fun x : ℝ => -x)) t = charFun μ (-t) := by
  simpa only [neg_one_mul] using charFun_map_mul (μ := μ) (-1) t

/-- Reflection removes exactly the imaginary part, rather than changing
the spatial scale or multiplying the real part by an extra constant. -/
theorem charFun_fairLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    charFun (fairLaw μ) t = ((charFun μ t).re : ℂ) := by
  have : IsProbabilityMeasure (μ.map (fun x : ℝ => -x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hi (ν : Measure ℝ) [IsProbabilityMeasure ν] :
      Integrable (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * I)) ν := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun x => by
      rw [← Complex.ofReal_mul]
      exact (Complex.norm_exp_ofReal_mul_I _).le
  rw [charFun_apply_real, fairLaw,
    integral_add_measure ((hi μ).smul_measure ENNReal.ofReal_ne_top)
      ((hi (μ.map (fun x : ℝ => -x))).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2), Complex.real_smul]
  rw [← charFun_apply_real, ← charFun_apply_real]
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  change (1 / 2 : ℂ) * charFun μ t +
    (1 / 2 : ℂ) * charFun (μ.map (fun x : ℝ => -x)) t = _
  rw [charFun_reflectedLaw, charFun_neg]
  apply Complex.ext
  · simp
    ring
  · simp

/-- Symmetrization preserves the established `L¹` characteristic-function bound. -/
theorem charFun_fairLaw_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : Integrable (charFun μ)) : Integrable (charFun (fairLaw μ)) := by
  have he : charFun (fairLaw μ) = (fun t : ℝ => ((charFun μ t).re : ℂ)) :=
    funext (charFun_fairLaw μ)
  rw [he]
  exact hφ.re.ofReal

theorem fourier_fairLaw_eq_canonical (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (fun x : ℝ => (𝓕 (fun t : ℝ => charFun (fairLaw μ) (2 * Real.pi * t)) x).re) =
      canonicalFairDensity μ := by
  simp_rw [charFun_fairLaw]
  unfold canonicalFairDensity
  exact fourier_scaled_re_eq_normalizedFourierDensity (fun t : ℝ => ((charFun μ t).re : ℂ))

/-- Identification with the actual probability mixture. Positivity and
integrability of the inverse are consequences of characteristic-function
integrability, proved in the generic Gaussian inversion argument. -/
theorem fairLaw_eq_withDensity_canonical (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : Integrable (charFun μ)) :
    fairLaw μ = volume.withDensity (fun x => ENNReal.ofReal (canonicalFairDensity μ x)) := by
  have := fairLaw_isProbability μ
  have hd : fourierCharDensity (fairLaw μ) = canonicalFairDensity μ :=
    fourier_fairLaw_eq_canonical μ
  simpa only [hd] using measure_eq_withDensity_fourierCharDensity (fairLaw μ)
    (charFun_fairLaw_integrable μ hφ)

theorem canonicalFairDensity_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : Integrable (charFun μ)) (x : ℝ) : 0 ≤ canonicalFairDensity μ x := by
  have := fairLaw_isProbability μ
  have hd : fourierCharDensity (fairLaw μ) = canonicalFairDensity μ :=
    fourier_fairLaw_eq_canonical μ
  rw [← hd]
  exact fourierCharDensity_nonneg (fairLaw μ) (charFun_fairLaw_integrable μ hφ) x

theorem canonicalFairDensity_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : Integrable (charFun μ)) : Integrable (canonicalFairDensity μ) := by
  have := fairLaw_isProbability μ
  have hd : fourierCharDensity (fairLaw μ) = canonicalFairDensity μ :=
    fourier_fairLaw_eq_canonical μ
  rw [← hd]
  exact fourierCharDensity_integrable (fairLaw μ) (charFun_fairLaw_integrable μ hφ)

/-- The Fourier normalization agrees with the probability mass of the fair law. -/
theorem canonicalFairDensity_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : Integrable (charFun μ)) : (∫ x, canonicalFairDensity μ x) = 1 := by
  have := fairLaw_isProbability μ
  have hi := canonicalFairDensity_integrable μ hφ
  have hp := canonicalFairDensity_nonneg μ hφ
  have hm := congrArg (fun ν : Measure ℝ => ν univ)
    (fairLaw_eq_withDensity_canonical μ hφ)
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hp)] at hm
  have hr := congrArg ENNReal.toReal hm.symm
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hp), ENNReal.toReal_one] using hr

/-- The actual fixed-point law supplies the integrability needed for inversion.
There is no density, decay, or Fourier-representation premise. -/
theorem fairLaw_eq_withDensity_canonical_of_fixedPoint {a : ℝ}
    (ha₀ : 0 < a) (ha₁ : a < 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfix : μ = fixedPointLaw a μ) (hmean : (∫ x : ℝ, x ∂μ) ≠ 0) :
    fairLaw μ = volume.withDensity (fun x => ENNReal.ofReal (canonicalFairDensity μ x)) := by
  have : Measure.IsOpenPosMeasure μ := isOpenPosMeasure_of_fixedPoint ha₀ ha₁ μ hfix hmean
  exact fairLaw_eq_withDensity_canonical μ (charFun_integrable_of_fixedPoint ha₀ ha₁ μ hfix)

end Kagey131.PaperD.ModelFourier
