import PaperD.EJPModelDensityMeasure
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# An integrable characteristic function has an actual inverse density

Positive Gaussian convolutions have mass one. Bochner Fubini identifies
their transforms with Gaussian-damped characteristic functions. Dominated
convergence gives the inverse Fourier integral, and Fatou gives its
integrability. Thus positivity and integrability of the inverse are proved
from the probability law, rather than supplied as Fourier hypotheses.
-/

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal FourierTransform RealInnerProductSpace
namespace Kagey131.PaperD.ModelFourier
noncomputable def standardGaussian (t : ℝ) : ℝ := Real.exp (-Real.pi*t^2)

lemma standardGaussian_nonneg (t : ℝ) : 0 ≤ standardGaussian t := (Real.exp_pos _).le
lemma standardGaussian_integrable : Integrable standardGaussian :=
  integrable_exp_neg_mul_sq Real.pi_pos
lemma standardGaussian_integral : ∫ t, standardGaussian t = 1 := by
  change (∫ t : ℝ, Real.exp (-Real.pi*t^2)) = 1
  rw [integral_gaussian]
  simp [Real.pi_ne_zero]
lemma standardGaussian_fourier : 𝓕 (fun t => (standardGaussian t : ℂ)) =
    fun t => (standardGaussian t : ℂ) := by
  convert fourier_gaussian_pi (by norm_num : 0 < (1:ℂ).re) using 1 <;>
    simp [standardGaussian,Complex.ofReal_exp]

lemma scaledGaussian_fourier {v : ℝ} (hv : 0 < v) (x : ℝ) :
    (∫ t : ℝ, Complex.exp ((-2*Real.pi*t*x : ℝ)*Complex.I) *
      (standardGaussian (t/v) : ℂ)) =
      (v : ℂ) * (standardGaussian (v*x) : ℂ) := by
  let g : ℝ → ℂ := fun t => Complex.exp ((-2*Real.pi*t*(v*x) : ℝ)*Complex.I) *
    (standardGaussian t : ℂ)
  calc
    _ = ∫ t : ℝ, g (t/v) := by
      congr 1
      ext t
      dsimp only [g]
      congr 2
      congr 1
      field_simp
    _ = v • ∫ t, g t := by rw [Measure.integral_comp_div,abs_of_pos hv]
    _ = _ := by
      have h := congrFun standardGaussian_fourier (v*x)
      rw [Real.fourier_real_eq_integral_exp_smul] at h
      simpa only [smul_eq_mul,Complex.real_smul] using congrArg (fun z : ℂ => (v : ℂ)*z) h

noncomputable def gaussianApprox (μ : Measure ℝ) (v x : ℝ) : ℝ :=
  ∫ y, v*standardGaussian (v*(x-y)) ∂μ

lemma scaledGaussian_integrable {v : ℝ} (hv : 0 < v) (y : ℝ) :
    Integrable (fun x => v*standardGaussian (v*(x-y))) :=
  ((standardGaussian_integrable.comp_mul_left' hv.ne').comp_sub_right y).const_mul v

lemma scaledGaussian_integral {v : ℝ} (hv : 0 < v) (y : ℝ) :
    (∫ x : ℝ, v*standardGaussian (v*(x-y))) = 1 := by
  rw [integral_const_mul,integral_sub_right_eq_self (fun z : ℝ => standardGaussian (v*z)) y,Measure.integral_comp_mul_left,
    standardGaussian_integral,smul_eq_mul,abs_of_pos (inv_pos.mpr hv)]
  simpa only [mul_one] using mul_inv_cancel₀ hv.ne'

lemma gaussianApprox_nonneg (μ : Measure ℝ) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    0 ≤ gaussianApprox μ v x := integral_nonneg fun _y => mul_nonneg hv.le (standardGaussian_nonneg _)

lemma gaussianApprox_integrable_and_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ} (hv : 0 < v) : Integrable (gaussianApprox μ v) ∧ ∫ x, gaussianApprox μ v x = 1 := by
  let K : ℝ × ℝ → ℝ := fun z => v*standardGaussian (v*(z.1-z.2))
  have hiK : Integrable K (volume.prod μ) := by
    apply (integrable_prod_iff' (by unfold K standardGaussian; fun_prop)).mpr
    constructor
    · exact ae_of_all _ fun y => scaledGaussian_integrable hv y
    · have he : (fun y => ∫ x, ‖K (x,y)‖) = fun _ => (1 : ℝ) := by
        ext y
        simpa only [K,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hv.le (standardGaussian_nonneg _))]
          using scaledGaussian_integral hv y
      rw [he]
      exact integrable_const 1
  constructor
  · exact hiK.integral_prod_left
  · change (∫ x, ∫ y, K (x,y) ∂μ) = 1
    rw [integral_integral_swap hiK]
    dsimp only [K]
    simp only [scaledGaussian_integral hv,integral_const,probReal_univ,one_smul]

lemma gaussianApprox_fourier (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ} (hv : 0 < v) (x : ℝ) :
    (gaussianApprox μ v x : ℂ) =
    ∫ t : ℝ, Complex.exp ((-2*Real.pi*t*x : ℝ)*Complex.I) *
      (standardGaussian (t/v) : ℂ) * charFun μ (2*Real.pi*t) := by
  let K : ℝ × ℝ → ℂ := fun z =>
    Complex.exp ((-2*Real.pi*z.1*(x-z.2) : ℝ)*Complex.I) * (standardGaussian (z.1/v) : ℂ)
  have hKi : Integrable K (volume.prod μ) := by
    apply Integrable.mono' ((standardGaussian_integrable.comp_div hv.ne').mul_prod (integrable_const (μ := μ) (1 : ℝ)))
      (by unfold K standardGaussian; fun_prop)
    filter_upwards with z
    dsimp only [K]
    rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (standardGaussian_nonneg _)]
    simp only [mul_one]
    exact le_rfl
  calc
    _ = ∫ y, ∫ t, K (t,y) ∂volume ∂μ := by
      unfold gaussianApprox
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards with y
      simpa only [K,Complex.ofReal_mul] using (scaledGaussian_fourier hv (x-y)).symm
    _ = ∫ t, ∫ y, K (t,y) ∂μ := (integral_integral_swap hKi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [charFun_apply_real,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [K]
      calc
        _ = (Complex.exp ((-2*Real.pi*t*x : ℝ)*Complex.I) *
            Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*(y : ℂ)*Complex.I)) *
            (standardGaussian (t/v) : ℂ) := by
          congr 1
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        _ = _ := by ring

/-- The actual inverse characteristic integral, in Mathlib Fourier normalization. -/
noncomputable def fourierCharDensity (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (𝓕 (fun t : ℝ => charFun μ (2*Real.pi*t)) x).re

lemma gaussianApprox_tendsto_complex (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : Integrable (charFun μ)) (x : ℝ) :
    Tendsto (fun n : ℕ => (gaussianApprox μ ((n:ℝ)+1) x : ℂ)) atTop
      (𝓝 (𝓕 (fun t : ℝ => charFun μ (2*Real.pi*t)) x)) := by
  let F : ℝ → ℂ := fun t => charFun μ (2*Real.pi*t)
  have hF : Integrable F := hφ.comp_mul_left' (by positivity : 2*Real.pi ≠ 0)
  have hG (n : ℕ) : (gaussianApprox μ ((n:ℝ)+1) x : ℂ) =
      ∫ t : ℝ, Complex.exp ((-2*Real.pi*t*x : ℝ)*Complex.I) *
        (standardGaussian (t/((n:ℝ)+1)) : ℂ) * F t :=
    gaussianApprox_fourier μ (by positivity) x
  simp_rw [hG]
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  apply tendsto_integral_of_dominated_convergence (fun t => ‖F t‖)
  · intro n
    exact (by unfold standardGaussian F; fun_prop)
  · exact hF.norm
  · intro n
    exact ae_of_all _ fun t => by
      have hb : standardGaussian (t/((n:ℝ)+1)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _)
      rw [norm_mul,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (standardGaussian_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) hb
  · exact ae_of_all _ fun t => by
      have ht : Tendsto (fun n : ℕ => t/((n:ℝ)+1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
      have hg : Tendsto (fun n : ℕ => (standardGaussian (t/((n:ℝ)+1)) : ℂ)) atTop (𝓝 1) := by
        have hc : Continuous (fun t : ℝ => (standardGaussian t : ℂ)) := by unfold standardGaussian; fun_prop
        simpa only [Function.comp_def,standardGaussian,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,neg_zero,
          Real.exp_zero,Complex.ofReal_one] using hc.continuousAt.tendsto.comp ht
      simpa only [mul_one] using (tendsto_const_nhds.mul hg).mul_const (F t)

lemma fourierCharDensity_complex (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : Integrable (charFun μ)) (x : ℝ) :
    𝓕 (fun t : ℝ => charFun μ (2*Real.pi*t)) x = (fourierCharDensity μ x : ℂ) := by
  have ht : Tendsto (fun _ : ℕ => (0:ℝ)) atTop
      (𝓝 (𝓕 (fun t : ℝ => charFun μ (2*Real.pi*t)) x).im) := by
    simpa only [Function.comp_def,Complex.ofReal_im] using
      (Complex.continuous_im.continuousAt.tendsto.comp (gaussianApprox_tendsto_complex μ hφ x))
  have hz : (𝓕 (fun t : ℝ => charFun μ (2*Real.pi*t)) x).im = 0 :=
    tendsto_nhds_unique ht tendsto_const_nhds
  exact Complex.ext rfl (by simpa only [Complex.ofReal_im] using hz)

lemma gaussianApprox_tendsto_real (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : Integrable (charFun μ)) (x : ℝ) :
    Tendsto (fun n : ℕ => gaussianApprox μ ((n:ℝ)+1) x) atTop (𝓝 (fourierCharDensity μ x)) := by
  simpa only [Function.comp_def,Complex.ofReal_re,fourierCharDensity] using
    (Complex.continuous_re.continuousAt.tendsto.comp (gaussianApprox_tendsto_complex μ hφ x))
lemma fourierCharDensity_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : Integrable (charFun μ)) (x : ℝ) : 0 ≤ fourierCharDensity μ x := by
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (gaussianApprox_tendsto_real μ hφ x)
    (.of_forall fun n : ℕ => gaussianApprox_nonneg μ (by positivity : 0 < (n:ℝ)+1) x)

lemma fourierCharDensity_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : Integrable (charFun μ)) : Integrable (fourierCharDensity μ) := by
  have hmass (n : ℕ) : (∫⁻ x, ‖gaussianApprox μ ((n:ℝ)+1) x‖ₑ) = 1 := by
    obtain ⟨hi,hm⟩ := gaussianApprox_integrable_and_integral μ (by positivity : 0 < (n:ℝ)+1)
    rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
    have he : (fun x => ‖gaussianApprox μ ((n:ℝ)+1) x‖) = gaussianApprox μ ((n:ℝ)+1) := by
      ext x
      exact Real.norm_of_nonneg (gaussianApprox_nonneg μ (by positivity) x)
    rw [he,hm]
    norm_num
  apply integrable_of_tendsto (ae_of_all _ fun x => gaussianApprox_tendsto_real μ hφ x)
    (fun n => (gaussianApprox_integrable_and_integral μ (by positivity : 0 < (n:ℝ)+1)).1.aestronglyMeasurable)
  simp only [hmass,liminf_const,ne_eq,ENNReal.one_ne_top,not_false_eq_true]

/-- A probability measure with integrable characteristic function is the
measure with the density given by its actual inverse Fourier integral.
No density, sign, integrability of the inverse, or transform identity is
assumed: all three inverse properties are derived above from Gaussian
convolution. -/
theorem measure_eq_withDensity_fourierCharDensity (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hφ : Integrable (charFun μ)) :
    μ = volume.withDensity (fun x => ENNReal.ofReal (fourierCharDensity μ x)) := by
  exact measure_eq_withDensity_of_fourier μ hφ (fourierCharDensity μ)
    (fourierCharDensity_integrable μ hφ) (fourierCharDensity_nonneg μ hφ)
    (funext (fourierCharDensity_complex μ hφ))

end Kagey131.PaperD.ModelFourier

