import PaperD.Modes.AnalyticFourier
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The first two derivatives of the Fourier density

Multiplication of the Fourier integrand by `-it` preserves all exponential
moments. Hence the differentiated densities are continuous, bounded, and
vanish at both ends of the line.
-/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology FourierTransform

noncomputable def fourierDerivativeWeight (φ : ℝ → ℂ) (t : ℝ) : ℂ :=
  (-Complex.I*(t:ℂ)) * φ t

theorem continuous_fourierDerivativeWeight {φ : ℝ → ℂ} (hφ : Continuous φ) :
    Continuous (fourierDerivativeWeight φ) :=
  (continuous_const.mul Complex.continuous_ofReal).mul hφ

theorem exponential_moments_fourierDerivativeWeight {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖)) (B : ℝ) :
    Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖fourierDerivativeWeight φ t‖) := by
  refine (hw (B+1)).mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
      (continuous_fourierDerivativeWeight hφ).norm).aestronglyMeasurable ?_
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
  have ht : |t| ≤ Real.exp |t| := (Real.add_one_le_exp |t|).trans' (by linarith)
  simp only [fourierDerivativeWeight, norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    Real.exp (B*|t|) * (|t| * ‖φ t‖) ≤ Real.exp (B*|t|) * (Real.exp |t| * ‖φ t‖) := by
      gcongr
    _ = Real.exp ((B+1)*|t|) * ‖φ t‖ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem hasDerivAt_entireFourier_weight {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖)) (z : ℂ) :
    HasDerivAt (entireFourier φ) (entireFourier (fourierDerivativeWeight φ) z) z := by
  convert hasDerivAt_entireFourier hφ hw z using 1
  unfold entireFourier
  apply integral_congr_ae
  filter_upwards [] with t
  unfold entireFourierKernel fourierDerivativeWeight
  ring

theorem entireFourier_real_eq_fourier (φ : ℝ → ℂ) (x : ℝ) :
    entireFourier φ (x:ℂ) = 𝓕 φ (x/(2*Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold entireFourier
  apply integral_congr_ae
  filter_upwards [] with t
  unfold entireFourierKernel
  rw [smul_eq_mul]
  congr 2
  push_cast
  field_simp

theorem entireFourier_tendsto_atTop (φ : ℝ → ℂ) :
    Tendsto (fun x : ℝ => entireFourier φ (x:ℂ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => x/(2*Real.pi)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have h := (Real.zero_at_infty_fourier φ).comp (ht.mono_right atTop_le_cocompact)
  simpa only [Function.comp_def, ← entireFourier_real_eq_fourier] using h

theorem entireFourier_tendsto_atBot (φ : ℝ → ℂ) :
    Tendsto (fun x : ℝ => entireFourier φ (x:ℂ)) atBot (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => x/(2*Real.pi)) atBot atBot :=
    tendsto_id.atBot_div_const (by positivity)
  have h := (Real.zero_at_infty_fourier φ).comp (ht.mono_right atBot_le_cocompact)
  simpa only [Function.comp_def, ← entireFourier_real_eq_fourier] using h

theorem norm_entireFourier_real_le (φ : ℝ → ℂ) (x : ℝ) :
    ‖entireFourier φ (x:ℂ)‖ ≤ ∫ t : ℝ, ‖φ t‖ := by
  unfold entireFourier
  calc
    _ ≤ ∫ t : ℝ, ‖entireFourierKernel φ (x:ℂ) t‖ := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp [entireFourierKernel, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

noncomputable def normalizedFourierDensity (φ : ℝ → ℂ) (x : ℝ) : ℝ :=
  (entireFourier φ (x:ℂ)).re / (2*Real.pi)

theorem hasDerivAt_normalizedFourierDensity {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖)) (x : ℝ) :
    HasDerivAt (normalizedFourierDensity φ)
      (normalizedFourierDensity (fourierDerivativeWeight φ) x) x :=
  (hasDerivAt_entireFourier_weight hφ hw (x:ℂ)).real_of_complex.div_const _

theorem deriv_normalizedFourierDensity {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖)) :
    deriv (normalizedFourierDensity φ) = normalizedFourierDensity (fourierDerivativeWeight φ) :=
  funext fun x => (hasDerivAt_normalizedFourierDensity hφ hw x).deriv

theorem normalizedFourierDensity_continuous {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖)) :
    Continuous (normalizedFourierDensity φ) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_normalizedFourierDensity hφ hw x).continuousAt

theorem normalizedFourierDensity_bounded (φ : ℝ → ℂ) :
    ∃ C : ℝ, ∀ x, |normalizedFourierDensity φ x| ≤ C := by
  refine ⟨(∫ t : ℝ, ‖φ t‖)/|2*Real.pi|, fun x => ?_⟩
  unfold normalizedFourierDensity
  rw [abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  exact (Complex.abs_re_le_norm _).trans (norm_entireFourier_real_le φ x)

theorem normalizedFourierDensity_tendsto (φ : ℝ → ℂ) :
    Tendsto (normalizedFourierDensity φ) atTop (𝓝 0) ∧
    Tendsto (normalizedFourierDensity φ) atBot (𝓝 0) := by
  constructor
  · have h := Complex.continuous_re.continuousAt.tendsto.comp (entireFourier_tendsto_atTop φ)
    change Tendsto (fun x : ℝ => (entireFourier φ (x:ℂ)).re / (2*Real.pi)) atTop (𝓝 0)
    simpa only [Function.comp_def, Complex.zero_re, zero_div] using h.div_const (2*Real.pi)
  · have h := Complex.continuous_re.continuousAt.tendsto.comp (entireFourier_tendsto_atBot φ)
    change Tendsto (fun x : ℝ => (entireFourier φ (x:ℂ)).re / (2*Real.pi)) atBot (𝓝 0)
    simpa only [Function.comp_def, Complex.zero_re, zero_div] using h.div_const (2*Real.pi)

end Kagey131.PaperD.Modes
