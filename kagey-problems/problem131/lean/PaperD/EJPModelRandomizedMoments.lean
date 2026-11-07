import PaperD.EJPAnalyticThresholdRandomization

/-!
# Moments under actual exponential randomization

The factor Gamma(1+ak) comes from integration against the mean-one
exponential law. Both integrability and the product moment formula are proved.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

namespace Kagey131.PaperD.ModelRandomizedMoments

open AnalyticThresholdRandomization

theorem integral_expMeasure_one_real (g : ℝ → ℝ) :
    (∫ v, g v ∂expMeasure 1) = ∫ v : ℝ in Ioi 0, Real.exp (-v) * g v := by
  change (∫ v, g v ∂volume.withDensity (gammaPDF 1 1)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (f := gammaPDF 1 1) (by unfold gammaPDF; fun_prop)
    (ae_of_all _ fun v => ENNReal.ofReal_lt_top)]
  have hp (v : ℝ) : (gammaPDF 1 1 v).toReal = if 0 ≤ v then Real.exp (-v) else 0 := by
    simp only [gammaPDF, gammaPDFReal, Real.rpow_one, Real.Gamma_one, div_one,
      sub_self, Real.rpow_zero, mul_one, one_mul]
    split_ifs <;> simp_all [ENNReal.toReal_ofReal, (Real.exp_pos (-v)).le]
  simp_rw [hp, ite_smul, zero_smul]
  change (∫ v, (Ici (0 : ℝ)).indicator (fun v => Real.exp (-v) * g v) v) = _
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem integral_exp_power {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (∫ v : ℝ, (v^a)^k ∂expMeasure 1) = Real.Gamma (a*k+1) := by
  rw [integral_expMeasure_one_real, Real.Gamma_eq_integral (by positivity : 0 < a*k+1)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  simp only [add_sub_cancel_right, Real.rpow_mul_natCast hv.le]

theorem integrable_exp_power {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    Integrable (fun v : ℝ => (v^a)^k) (expMeasure 1) := by
  by_contra hn
  have hz := integral_undef hn
  rw [integral_exp_power ha k] at hz
  exact (Real.Gamma_pos_of_pos (by positivity : 0 < a*k+1)).ne' hz

theorem integrable_randomized_power {a : ℝ} (ha : 0 ≤ a) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (k : ℕ) (hk : Integrable (fun x : ℝ => x^k) μ) :
    Integrable (fun z : ℝ => z^k) (randomizedLaw a μ) := by
  unfold randomizedLaw
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  simpa only [Function.comp_def, mul_pow] using (integrable_exp_power ha k).mul_prod hk

theorem integral_randomized_power {a : ℝ} (ha : 0 ≤ a) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (k : ℕ) :
    (∫ z : ℝ, z^k ∂randomizedLaw a μ) =
      Real.Gamma (a*k+1) * ∫ x : ℝ, x^k ∂μ := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  rw [randomizedLaw, integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow]
  rw [integral_prod_mul (fun v : ℝ => (v^a)^k) (fun x : ℝ => x^k),
    integral_exp_power ha k]

end Kagey131.PaperD.ModelRandomizedMoments
