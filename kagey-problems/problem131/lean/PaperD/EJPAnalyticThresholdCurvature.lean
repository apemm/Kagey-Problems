import PaperD.Modes.AnalyticDerivatives
import PaperD.Modes.RevisionShape
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

/-!
# Central curvature from Fourier inversion

Two applications of `hasDerivAt_normalizedFourierDensity` differentiate the
actual Fourier integral. The twice-differentiated Fourier weight is `-t^2 * ψ t`.
Its integrability is derived from the existing exponential weighted integral
theorem. For an even Fourier input, reflection turns the whole-line integral
into twice the positive-half-line integral, which is exactly `mellin ψ 3`.

The resulting formula is
`deriv (deriv g) 0 = -(mellin (fun t => ((φ t).re : ℂ)) 3).re / Real.pi`.
No central-curvature identity is an assumption. The fair-start Fourier
representation remains the classical inversion input.

The general interface takes continuity, evenness, and exponential weighted
integrability. The `ConditionalFourierHyp` interface derives that integrability
from the existing smoothing/decay theorem for `0 < a < 1`. For a true
characteristic function, real-part evenness follows from conjugate symmetry.
-/
open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology
namespace Kagey131.PaperD.AnalyticThresholdCurvature
open Modes

/-- Two actual derivative weights equal the negative quadratic weight. -/
lemma fourierDerivativeWeight_twice (ψ : ℝ → ℂ) :
    fourierDerivativeWeight (fourierDerivativeWeight ψ) = fun t : ℝ => -(t : ℂ)^2 * ψ t := by
  funext t
  simp only [fourierDerivativeWeight]
  calc
    (-Complex.I * (t : ℂ)) * ((-Complex.I * (t : ℂ)) * ψ t) = Complex.I^2 * (t : ℂ)^2 * ψ t := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- Reflection halves the integral of an even, absolutely integrable complex function. -/
lemma integral_even_eq_two {f : ℝ → ℂ} (hf : Integrable f) (heven : Function.Even f) :
    (∫ t : ℝ, f t) = 2 * ∫ t : ℝ in Ioi 0, f t := by
  have hneg : (∫ t : ℝ in Iic 0, f t) = ∫ t : ℝ in Ioi 0, f t := by
    calc
      _ = ∫ t : ℝ in Ioi 0, f (-t) := by simpa only [neg_zero] using (integral_comp_neg_Ioi 0 f).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        exact fun t _ => heven t
  have hsplit := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hf
  rw [compl_Ioi, hneg] at hsplit
  rw [← hsplit]
  ring

/-- The quadratic Fourier weight is integrable by the existing exponential moment calculus. -/
lemma second_weight_integrable {ψ : ℝ → ℂ} (hψ : Continuous ψ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖ψ t‖)) :
    Integrable (fun t : ℝ => (t : ℂ)^2 * ψ t) := by
  have hψ₁ := continuous_fourierDerivativeWeight hψ
  have hw₁ := exponential_moments_fourierDerivativeWeight hψ hw
  have hψ₂ := continuous_fourierDerivativeWeight hψ₁
  have hw₂ := exponential_moments_fourierDerivativeWeight hψ₁ hw₁
  have hd2 : Integrable (fourierDerivativeWeight (fourierDerivativeWeight ψ)) := by
    apply (integrable_norm_iff hψ₂.aestronglyMeasurable).mp
    simpa only [zero_mul, Real.exp_zero, one_mul] using hw₂ 0
  have hi := hd2.neg
  change Integrable (fun t : ℝ => -(fourierDerivativeWeight (fourierDerivativeWeight ψ) t)) at hi
  simpa only [fourierDerivativeWeight_twice, neg_mul, neg_neg] using hi

/-- The Mellin integral at the curvature parameter converges absolutely. -/
theorem mellin_three_convergent {ψ : ℝ → ℂ} (hψ : Continuous ψ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖ψ t‖)) :
    MellinConvergent ψ 3 := by
  simpa only [MellinConvergent, smul_eq_mul, show (3 : ℂ) - 1 = 2 by norm_num,
    cpow_two] using (second_weight_integrable hψ hw).integrableOn (s := Ioi 0)

/-- The actual derivative of the first derivative at zero, with its computed Mellin value. -/
theorem central_second_derivative {ψ : ℝ → ℂ} (hψ : Continuous ψ)
    (heven : Function.Even ψ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖ψ t‖)) :
    HasDerivAt (deriv (normalizedFourierDensity ψ)) (-(mellin ψ 3).re / Real.pi) 0 := by
  have hψ₁ := continuous_fourierDerivativeWeight hψ
  have hw₁ := exponential_moments_fourierDerivativeWeight hψ hw
  have hd := hasDerivAt_normalizedFourierDensity hψ₁ hw₁ 0
  have hd₁ := deriv_normalizedFourierDensity hψ hw
  have heven₂ : Function.Even (fun t : ℝ => (t : ℂ)^2 * ψ t) := by
    intro t
    dsimp only
    rw [ofReal_neg, neg_sq, heven t]
  have hsplit := integral_even_eq_two (second_weight_integrable hψ hw) heven₂
  have hm : mellin ψ 3 = ∫ t : ℝ in Ioi 0, (t : ℂ)^2 * ψ t := by
    simp only [mellin, smul_eq_mul, show (3 : ℂ) - 1 = 2 by norm_num, cpow_two]
  have hval : normalizedFourierDensity (fourierDerivativeWeight (fourierDerivativeWeight ψ)) 0 =
      -(mellin ψ 3).re / Real.pi := by
    rw [normalizedFourierDensity, entireFourier, fourierDerivativeWeight_twice]
    simp only [entireFourierKernel, ofReal_zero, mul_zero, exp_zero, one_mul,
      neg_mul, integral_neg]
    rw [hsplit, ← hm]
    simp only [neg_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    field_simp
  rw [hval] at hd
  rw [hd₁]
  exact hd

/-- Central curvature of an even Fourier input, with the normalization computed. -/
theorem central_curvature {ψ : ℝ → ℂ} (hψ : Continuous ψ)
    (heven : Function.Even ψ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖ψ t‖)) :
    deriv (deriv (normalizedFourierDensity ψ)) 0 = -(mellin ψ 3).re / Real.pi :=
  (central_second_derivative hψ heven hw).deriv

lemma exponential_moments_realPart {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖)) (B : ℝ) :
    Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖((φ t).re : ℂ)‖) := by
  refine (hw B).mono' ?_ (ae_of_all _ fun t => ?_)
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hφ)).norm).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_re_le_norm (φ t)

/-- Specialization to the real part of the conditional transform and its fair-start density. -/
theorem central_curvature_fair {φ : ℝ → ℂ} {g : ℝ → ℝ} (hφ : Continuous φ)
    (heven : Function.Even (fun t => (φ t).re))
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖))
    (hrep : g = normalizedFourierDensity (fun t => ((φ t).re : ℂ))) :
    deriv (deriv g) 0 = -(mellin (fun t => ((φ t).re : ℂ)) 3).re / Real.pi := by
  rw [hrep]
  apply central_curvature (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hφ))
    (fun t => congrArg Complex.ofReal (heven t))
  exact exponential_moments_realPart hφ hw


/-- The smoothing and decay hypotheses already proved in Paper D imply every
exponential weighted Fourier integral needed for differentiation. -/
theorem exponential_moments_of_conditionalFourierHyp {a : ℝ} {g : ℝ → ℝ} {φ : ℝ → ℂ}
    (ha₀ : 0 < a) (ha₁ : a < 1) (hφ : ConditionalFourierHyp a g φ) (B : ℝ) :
    Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖) := by
  let r := (1+a)/(2*a)
  have hr : 1 < r := by
    apply (lt_div_iff₀ (show 0 < 2*a by positivity)).mpr
    linarith
  have har : a*r < 1 := by
    have he : a*r = (1+a)/2 := by dsimp [r]; field_simp
    rw [he]
    linarith
  obtain ⟨c, hc, hbound⟩ := characteristic_stretched_decay hφ.continuous hφ.unit_bound
    hφ.norm_even ha₀ (by linarith : 0 < r) har hφ.decay hφ.smoothing
  exact exponential_moments_of_stretched_bound hφ.continuous hc hr hbound B

/-- The central curvature is derived from the classical fixed-point/Fourier
hypotheses. Only symmetry of the real part is additionally needed. -/
theorem central_curvature_of_conditionalFourierHyp {a : ℝ} {g : ℝ → ℝ} {φ : ℝ → ℂ}
    (ha₀ : 0 < a) (ha₁ : a < 1) (hφ : ConditionalFourierHyp a g φ)
    (heven : Function.Even (fun t => (φ t).re)) :
    deriv (deriv g) 0 = -(mellin (fun t => ((φ t).re : ℂ)) 3).re / Real.pi := by
  exact central_curvature_fair hφ.continuous heven
    (exponential_moments_of_conditionalFourierHyp ha₀ ha₁ hφ) hφ.fair_representation

/-- For a true conditional characteristic function its real-part symmetry is automatic. -/
theorem central_curvature_charFun {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hφ : ConditionalFourierHyp a g (charFun μ)) :
    deriv (deriv g) 0 = -(mellin (fun t => ((charFun μ t).re : ℂ)) 3).re / Real.pi := by
  apply central_curvature_of_conditionalFourierHyp ha₀ ha₁ hφ
  intro t
  simp only [charFun_neg, conj_re]
end Kagey131.PaperD.AnalyticThresholdCurvature

