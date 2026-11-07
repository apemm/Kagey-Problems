import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# The fixed-point law and its Fourier smoothing inequality

The uniform variable and the two copies are genuine product measures.
The independent sign is integrated out as the explicit probability mixture
`fixedPointLaw`. A distributional equality `μ = fixedPointLaw a μ` implies
the characteristic-function integral equation by Bochner Fubini. Taking norms
and using characteristic-function conjugacy gives the smoothing inequality.
No density, Fourier decay, smoothing, or transform identity is assumed.
-/
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology ENNReal
namespace Kagey131.PaperD.ModelFourier

/-- Independent uniform mixing variable on `(0,1)`. -/
noncomputable def unitUniform : Measure ℝ := volume.restrict (Ioo 0 1)
@[instance] theorem unitUniform_isProbabilityMeasure : IsProbabilityMeasure unitUniform := by
  constructor
  simp [unitUniform]

/-- Conditional on the independent sign, the recursive sum of two independent copies. -/
noncomputable def branchLaw (a ε : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (unitUniform.prod (μ.prod μ)).map (fun z : ℝ × ℝ × ℝ =>
    z.1 ^ a * z.2.1 + ε * (1-z.1) ^ a * z.2.2)

@[instance] theorem branchLaw_isProbabilityMeasure (a ε : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (branchLaw a ε μ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- The distributional fixed-point right side. The sign has probabilities
`(1+a)/2` and `(1-a)/2` and is independent of the uniform and both copies. -/
noncomputable def fixedPointLaw (a : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal ((1+a)/2) • branchLaw a 1 μ +
    ENNReal.ofReal ((1-a)/2) • branchLaw a (-1) μ

lemma integrable_charKernel (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((t*x : ℝ) * Complex.I)) ν := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ fun x => (Complex.norm_exp_ofReal_mul_I _).le

/-- Exact Fourier transform of the actual product-law recursion, by Fubini. -/
theorem charFun_branchLaw (a ε : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    charFun (branchLaw a ε μ) t = ∫ u,
      charFun μ (t*u^a) * charFun μ (t*ε*(1-u)^a) ∂unitUniform := by
  let F : ℝ × ℝ × ℝ → ℂ := fun z => Complex.exp
    ((t * (z.1^a*z.2.1 + ε*(1-z.1)^a*z.2.2) : ℝ) * Complex.I)
  have hi : Integrable F (unitUniform.prod (μ.prod μ)) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun z => (Complex.norm_exp_ofReal_mul_I _).le
  rw [charFun_apply_real, branchLaw, integral_map (by fun_prop) (by fun_prop)]
  simp only [← ofReal_mul]
  change (∫ z, F z ∂unitUniform.prod (μ.prod μ)) = _
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards with u
  calc
    _ = ∫ z : ℝ × ℝ, Complex.exp (((t*u^a)*z.1 : ℝ) * Complex.I) *
        Complex.exp (((t*ε*(1-u)^a)*z.2 : ℝ) * Complex.I) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [F]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = _ := by
      rw [integral_prod_mul (fun x : ℝ => Complex.exp (((t*u^a)*x : ℝ) * Complex.I))
      (fun y : ℝ => Complex.exp (((t*ε*(1-u)^a)*y : ℝ) * Complex.I)),
      charFun_apply_real, charFun_apply_real]
      simp only [ofReal_mul]

/-- The characteristic function identity is derived from the distributional law. -/
theorem charFun_of_fixedPoint {a : ℝ} (ha₀ : -1 ≤ a) (ha₁ : a ≤ 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hfix : μ = fixedPointLaw a μ) (t : ℝ) :
    charFun μ t = ∫ u, charFun μ (t*u^a) *
      (((1+a)/2 : ℂ) * charFun μ (t*(1-u)^a) +
        ((1-a)/2 : ℂ) * charFun μ (-(t*(1-u)^a))) ∂unitUniform := by
  have hp : 0 ≤ (1+a)/2 := by linarith
  have hq : 0 ≤ (1-a)/2 := by linarith
  have hkernel : charFun (fixedPointLaw a μ) t =
      ((1+a)/2 : ℂ) * charFun (branchLaw a 1 μ) t +
        ((1-a)/2 : ℂ) * charFun (branchLaw a (-1) μ) t := by
    unfold fixedPointLaw
    simp only [charFun_apply_real, ← ofReal_mul]
    rw [integral_add_measure
      ((integrable_charKernel (branchLaw a 1 μ) t).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_charKernel (branchLaw a (-1) μ) t).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure]
    simp only [ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq, Complex.real_smul,
      ofReal_div, ofReal_add, ofReal_sub, ofReal_one, ofReal_ofNat]
  rw [show charFun μ t = charFun (fixedPointLaw a μ) t from congrArg (fun ν => charFun ν t) hfix,
    hkernel, charFun_branchLaw, charFun_branchLaw]
  have hip : Integrable (fun u => charFun μ (t*u^a) * charFun μ (t*(1-u)^a)) unitUniform := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun u => by
      rw [norm_mul]
      exact mul_le_one₀ (norm_charFun_le_one _) (norm_nonneg _) (norm_charFun_le_one _)
  have him : Integrable (fun u => charFun μ (t*u^a) * charFun μ (-(t*(1-u)^a))) unitUniform := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun u => by
      rw [norm_mul]
      exact mul_le_one₀ (norm_charFun_le_one _) (norm_nonneg _) (norm_charFun_le_one _)
  simp only [mul_one, mul_neg, neg_mul] at *
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hip.const_mul _) (him.const_mul _)]
  apply integral_congr_ae
  filter_upwards with u
  ring

lemma norm_sign_average_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (x p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p+q=1) :
    ‖(p : ℂ)*charFun μ x + (q : ℂ)*charFun μ (-x)‖ ≤ ‖charFun μ x‖ := by
  calc
    _ ≤ ‖(p : ℂ)*charFun μ x‖ + ‖(q : ℂ)*charFun μ (-x)‖ := norm_add_le _ _
    _ = (p+q)*‖charFun μ x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp,
        abs_of_nonneg hq, charFun_neg, RCLike.norm_conj]
      ring
    _ = _ := by rw [hpq, one_mul]

/-- The norm smoothing inequality is a consequence of the actual product-law fixed point. -/
theorem norm_charFun_smoothing {a : ℝ} (ha₀ : -1 ≤ a) (ha₁ : a ≤ 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hfix : μ = fixedPointLaw a μ) (t : ℝ) :
    ‖charFun μ t‖ ≤ ∫ u : ℝ in Ioo 0 1,
      ‖charFun μ (t*u^a)‖ * ‖charFun μ (t*(1-u)^a)‖ := by
  let p : ℝ := (1+a)/2
  let q : ℝ := (1-a)/2
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p+q=1 := by dsimp [p,q]; ring
  let F : ℝ → ℂ := fun u => charFun μ (t*u^a) *
    ((p : ℂ)*charFun μ (t*(1-u)^a) + (q : ℂ)*charFun μ (-(t*(1-u)^a)))
  let G : ℝ → ℝ := fun u => ‖charFun μ (t*u^a)‖ * ‖charFun μ (t*(1-u)^a)‖
  have hG : Integrable G unitUniform := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun u => by
      simp only [G, Real.norm_eq_abs, abs_mul, abs_norm]
      exact mul_le_one₀ (norm_charFun_le_one _) (norm_nonneg _) (norm_charFun_le_one _)
  have hdom (u : ℝ) : ‖F u‖ ≤ G u := by
    dsimp only [F,G]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_sign_average_le μ _ p q hp hq hpq) (norm_nonneg _)
  have hF : Integrable F unitUniform := hG.mono' (by fun_prop) (ae_of_all _ hdom)
  have hid : charFun μ t = ∫ u, F u ∂unitUniform := by
    convert charFun_of_fixedPoint ha₀ ha₁ μ hfix t using 1
    simp only [F,p,q,ofReal_div,ofReal_add,ofReal_sub,ofReal_one,ofReal_ofNat]
  rw [hid]
  exact (norm_integral_le_integral_norm _).trans (integral_mono hF.norm hG hdom)
end Kagey131.PaperD.ModelFourier




