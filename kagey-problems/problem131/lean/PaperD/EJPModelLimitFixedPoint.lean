import PaperD.EJPModelLimitCharacteristic
import PaperD.EJPModelLimitSplit
import PaperD.EJPModelFourierSmoothing

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace Kagey131.PaperD.ModelLimit

theorem integral_unit_reflection (f : ℝ → ℂ) :
    (∫ v : ℝ in Ioo 0 1, f (1 - v)) = ∫ v : ℝ in Ioo 0 1, f v := by
  have h := intervalIntegral.integral_comp_sub_mul (a := (0 : ℝ)) (b := 1)
    (c := (1 : ℝ)) f (by norm_num) 1
  simpa only [mul_one, one_mul, inv_one, one_smul, sub_self, sub_zero,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] using h

theorem fixedPointLaw_isProbability {a : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] : IsProbabilityMeasure (ModelFourier.fixedPointLaw a μ) := by
  have hp : 0 ≤ (1 + a) / 2 := by linarith
  have hq : 0 ≤ (1 - a) / 2 := by linarith
  constructor
  simp only [ModelFourier.fixedPointLaw, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp hq, show (1 + a) / 2 + (1 - a) / 2 = 1 by ring,
    ENNReal.ofReal_one]

/-- The characteristic function of the explicit product-law mixture, without a fixed-point premise. -/
theorem charFun_fixedPointLaw {a : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    charFun (ModelFourier.fixedPointLaw a μ) t = ∫ v : ℝ in Ioo 0 1,
      charFun μ (t * v ^ a) *
        (((((1 + a) / 2 : ℝ) : ℂ) * charFun μ (t * (1 - v) ^ a)) +
          ((((1 - a) / 2 : ℝ) : ℂ) * charFun μ (-(t * (1 - v) ^ a)))) := by
  have hp : 0 ≤ (1 + a) / 2 := by linarith
  have hq : 0 ≤ (1 - a) / 2 := by linarith
  have hkernel : charFun (ModelFourier.fixedPointLaw a μ) t =
      (((1+a)/2 : ℝ) : ℂ) * charFun (ModelFourier.branchLaw a 1 μ) t +
        (((1-a)/2 : ℝ) : ℂ) * charFun (ModelFourier.branchLaw a (-1) μ) t := by
    unfold ModelFourier.fixedPointLaw
    simp only [charFun_apply_real, ← Complex.ofReal_mul]
    rw [integral_add_measure
      ((ModelFourier.integrable_charKernel (ModelFourier.branchLaw a 1 μ) t).smul_measure ENNReal.ofReal_ne_top)
      ((ModelFourier.integrable_charKernel (ModelFourier.branchLaw a (-1) μ) t).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure]
    simp only [ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq, Complex.real_smul]
  rw [hkernel, ModelFourier.charFun_branchLaw, ModelFourier.charFun_branchLaw]
  have hip : Integrable (fun v => charFun μ (t*v^a) * charFun μ (t*(1-v)^a)) ModelFourier.unitUniform := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun v => by
      rw [norm_mul]
      exact mul_le_one₀ (norm_charFun_le_one _) (norm_nonneg _) (norm_charFun_le_one _)
  have him : Integrable (fun v => charFun μ (t*v^a) * charFun μ (-(t*(1-v)^a))) ModelFourier.unitUniform := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun v => by
      rw [norm_mul]
      exact mul_le_one₀ (norm_charFun_le_one _) (norm_nonneg _) (norm_charFun_le_one _)
  simp only [mul_one, mul_neg, neg_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hip.const_mul _) (him.const_mul _)]
  apply integral_congr_ae
  filter_upwards with v
  ring

theorem integral_splitLimitKernel (a : ℝ) (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    (∫ v : ℝ in Ioo 0 1, splitLimitKernel a μ t v) =
      ∫ v : ℝ in Ioo 0 1, charFun (μ : Measure ℝ) (t * v ^ a) *
        (((((1 + a) / 2 : ℝ) : ℂ) * charFun (μ : Measure ℝ) (t * (1 - v) ^ a)) +
          ((((1 - a) / 2 : ℝ) : ℂ) * charFun (μ : Measure ℝ) (-(t * (1 - v) ^ a)))) := by
  rw [← integral_unit_reflection (splitLimitKernel a μ t)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro v _
  dsimp only [splitLimitKernel]
  rw [show (1 : ℝ) - (1 - v) = v by ring]
  ring

/-- Actual finite-law convergence alone gives the distributional fixed point.
The finite split is proved in `EJPModelSplitFormula`; it is not an input here. -/
theorem fixedPoint_of_charFun_tendsto {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hconv : ∀ t : ℝ, Tendsto (fun n => charFun (scaledMeasure a n) t) atTop (𝓝 (charFun μ t))) :
    μ = ModelFourier.fixedPointLaw a μ := by
  let ν := finiteLaw a (by linarith : -1 ≤ a) ha1.le
  let μp : ProbabilityMeasure ℝ := ⟨μ, inferInstance⟩
  have hs : FiniteCharSplit a ν := fun N hN t => finite_split_charFun a (by linarith) ha1 hN t
  have := fixedPointLaw_isProbability (by linarith : -1 ≤ a) ha1.le μ
  apply Measure.ext_of_charFun
  funext t
  exact (charFun_equation_of_finite_split ha ha1.le hs (μ := μp) hconv t).trans
    ((integral_splitLimitKernel a μp t).trans (charFun_fixedPointLaw (by linarith) ha1.le μ t).symm)

/-- Weak convergence remains the explicit foundational input for the actual ERW limit law. -/
theorem fixedPoint_of_weakLimit {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (μ : ProbabilityMeasure ℝ)
    (hconv : WeakLimit a (by linarith : -1 ≤ a) ha1.le μ) :
    (μ : Measure ℝ) = ModelFourier.fixedPointLaw a (μ : Measure ℝ) :=
  fixedPoint_of_charFun_tendsto ha ha1 μ ((weakLimit_iff_charFun a (by linarith) ha1.le μ).mp hconv)

/-- The continuum Fourier equation of the actual conditional limit, with only weak convergence retained. -/
theorem charFun_equation_of_weakLimit {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (μ : ProbabilityMeasure ℝ)
    (hconv : WeakLimit a (by linarith : -1 ≤ a) ha1.le μ) (t : ℝ) :
    charFun (μ : Measure ℝ) t = ∫ v : ℝ in Ioo 0 1,
      charFun (μ : Measure ℝ) (t * v ^ a) *
        (((((1 + a) / 2 : ℝ) : ℂ) * charFun (μ : Measure ℝ) (t * (1 - v) ^ a)) +
          ((((1 - a) / 2 : ℝ) : ℂ) * charFun (μ : Measure ℝ) (-(t * (1 - v) ^ a)))) := by
  simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_ofNat, ModelFourier.unitUniform] using
    ModelFourier.charFun_of_fixedPoint (by linarith : -1 ≤ a) ha1.le
      (μ : Measure ℝ) (fixedPoint_of_weakLimit ha ha1 μ hconv) t

end Kagey131.PaperD.ModelLimit
