import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic
/-!
# Exponential randomization in the analytic threshold proof

`expRandomization a f t` is the Bochner integral `∫ v > 0, exp (-v) * f (t * v^a)`.
The weighted product integrand is absolutely integrable when `f` has an absolutely
convergent Mellin integral at `s` and `a * re s < 1`. Scaling its norm reduces the
Fubini estimate to a real Gamma integral. The resulting transform identity is
proved, not assumed:

`mellin (expRandomization a f) s = Gamma (1 - a*s) * mellin f s`.

The decay corollaries use local integrability, boundedness at zero, and arbitrary
polynomial decay. For the real part of a true characteristic function, only the
cited Fourier decay remains as input: the probability law supplies measurability,
local integrability, and boundedness. `randomizedLaw` is the pushforward of the
product of the mean-one exponential law and the original probability law. Its
characteristic function and its real part satisfy the randomization formula.

`inversePowerWeight` also proves the Mellin substitution `t = u^(-a)`, supplying
the initial identity needed for continuation. Identifying the model's H/ODE
parametrization with this randomized characteristic function, and verifying the
weight's derivatives and endpoint bounds, remain separate application work.
-/
open Set Filter MeasureTheory Complex Asymptotics ProbabilityTheory
open scoped Topology
namespace Kagey131.PaperD.AnalyticThresholdRandomization
/-- The exponential randomization transform, as an actual Bochner integral. -/
noncomputable def expRandomization (a : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ v : ℝ in Ioi 0, (Real.exp (-v) : ℂ) * f (t * v ^ a)

lemma weighted_scale (f : ℝ → ℂ) (s : ℂ) {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    (t : ℂ) ^ (s - 1) * f (t * c) =
      (c : ℂ) ^ (1 - s) * ((t * c : ℝ) : ℂ) ^ (s - 1) * f (t * c) := by
  rw [ofReal_mul, mul_cpow_ofReal_nonneg ht.le hc.le,
    show (1 : ℂ) - s = -(s - 1) by ring, cpow_neg]
  have hn : (c : ℂ) ^ (s - 1) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or, ofReal_eq_zero]
    exact Or.inl hc.ne'
  field_simp

lemma integral_norm_weighted_scale (f : ℝ → ℂ) (s : ℂ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * f (t * c)‖) =
      c ^ (-s.re) * ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * f t‖ := by
  calc
    _ = ∫ t : ℝ in Ioi 0, ‖(c : ℂ) ^ (1 - s)‖ *
          ‖((t * c : ℝ) : ℂ) ^ (s - 1) * f (t * c)‖ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [weighted_scale f s hc ht, mul_assoc, norm_mul]
    _ = ‖(c : ℂ) ^ (1 - s)‖ *
          (c⁻¹ * ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * f t‖) := by
      rw [integral_const_mul, integral_comp_mul_right_Ioi (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) * f t‖) 0 hc]
      simp only [zero_mul, smul_eq_mul]
    _ = _ := by
      rw [norm_cpow_eq_rpow_re_of_pos hc]
      simp only [sub_re, one_re]
      rw [← mul_assoc, ← Real.rpow_neg_one c, ← Real.rpow_add hc]
      congr 2
      ring

lemma rpow_cpow {v : ℝ} (hv : 0 < v) (a : ℝ) (s : ℂ) :
    ((v ^ a : ℝ) : ℂ) ^ (-s) = (v : ℂ) ^ (-(a : ℂ) * s) := by
  rw [← cpow_mul_ofReal_nonneg hv.le]
  congr 1
  ring

lemma gamma_kernel_integrable (a : ℝ) (s : ℂ) (hs : a * s.re < 1) :
    IntegrableOn (fun v : ℝ => (Real.exp (-v) : ℂ) * (v : ℂ) ^ (-(a : ℂ) * s)) (Ioi 0) := by
  have hz : 0 < (1 - (a : ℂ) * s).re := by
    simp only [sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, one_re]
    linarith
  simpa only [show (1 : ℂ) - (a : ℂ) * s - 1 = -(a : ℂ) * s by ring] using
    GammaIntegral_convergent hz

lemma gamma_kernel_integral (a : ℝ) (s : ℂ) (hs : a * s.re < 1) :
    (∫ v : ℝ in Ioi 0, (Real.exp (-v) : ℂ) * (v : ℂ) ^ (-(a : ℂ) * s)) =
      Gamma (1 - (a : ℂ) * s) := by
  have hz : 0 < (1 - (a : ℂ) * s).re := by
    simp only [sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, one_re]
    linarith
  rw [Gamma_eq_integral hz, GammaIntegral]
  congr 1
  funext v
  rw [show (1 : ℂ) - (a : ℂ) * s - 1 = -(a : ℂ) * s by ring]


/-- The joint integrand, with exponential variable first and Mellin variable second. -/
noncomputable def mellinKernel (a : ℝ) (f : ℝ → ℂ) (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.2 : ℂ) ^ (s - 1) * ((Real.exp (-p.1) : ℂ) * f (p.2 * p.1 ^ a))

lemma mellinKernel_measurable (a : ℝ) {f : ℝ → ℂ} (hf : Measurable f) (s : ℂ) :
    Measurable (mellinKernel a f s) := by
  exact ((measurable_ofReal.comp measurable_snd).pow_const _).mul
    ((measurable_ofReal.comp (measurable_fst.neg.exp)).mul
      (hf.comp (measurable_snd.mul (measurable_fst.pow_const a))))

/-- Absolute Fubini follows from Mellin convergence of the original function. -/
lemma mellinKernel_integrable (a : ℝ) {f : ℝ → ℂ} (hf : Measurable f)
    {s : ℂ} (hfs : MellinConvergent f s) (hs : a * s.re < 1) :
    Integrable (mellinKernel a f s)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  apply (integrable_prod_iff (mellinKernel_measurable a hf s).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hscaled : MellinConvergent (fun t => f (t * v ^ a)) s := by
      simpa only [mul_comm] using
        (MellinConvergent.comp_mul_left (Real.rpow_pos_of_pos hv a)).mpr hfs
    have hi : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * f (t * v ^ a)) (Ioi 0) := hscaled
    simpa only [mellinKernel, mul_left_comm] using hi.const_mul (Real.exp (-v) : ℂ)
  · let C := ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * f t‖
    have hgamma : IntegrableOn (fun v : ℝ => Real.exp (-v) * v ^ (-a * s.re) * C) (Ioi 0) := by
      have hz : 0 < 1 - a * s.re := by linarith
      simpa only [IntegrableOn, show 1 - a * s.re - 1 = -a * s.re by ring] using
        (Real.GammaIntegral_convergent hz).mul_const C
    apply hgamma.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    calc
      Real.exp (-v) * v ^ (-a * s.re) * C =
          Real.exp (-v) * ((v ^ a) ^ (-s.re) * C) := by
        rw [← Real.rpow_mul hv.le, show a * -s.re = -a * s.re by ring, mul_assoc]
      _ = ∫ t : ℝ in Ioi 0, ‖mellinKernel a f s (v, t)‖ := by
        rw [← integral_norm_weighted_scale f s (Real.rpow_pos_of_pos hv a), ← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only [mellinKernel]
        rw [mul_left_comm]
        simp only [norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-v))]

lemma expRandomization_mellinConvergent (a : ℝ) {f : ℝ → ℂ} (hf : Measurable f)
    {s : ℂ} (hfs : MellinConvergent f s) (hs : a * s.re < 1) :
    MellinConvergent (expRandomization a f) s := by
  have hi := (mellinKernel_integrable a hf hfs hs).integral_prod_right
  simpa only [mellinKernel, integral_const_mul, expRandomization,
    MellinConvergent, IntegrableOn, smul_eq_mul] using hi

/-- The narrow-strip Gamma factor is derived by scaling and absolute Fubini. -/
lemma mellin_expRandomization (a : ℝ) {f : ℝ → ℂ} (hf : Measurable f)
    {s : ℂ} (hfs : MellinConvergent f s) (hs : a * s.re < 1) :
    mellin (expRandomization a f) s = Gamma (1 - (a : ℂ) * s) * mellin f s := by
  have hi := mellinKernel_integrable a hf hfs hs
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ v : ℝ in Ioi 0, mellinKernel a f s (v, t) := by
      simp only [mellin, expRandomization, mellinKernel, smul_eq_mul, integral_const_mul]
    _ = ∫ v : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0, mellinKernel a f s (v, t) :=
      (integral_integral_swap (f := fun v t => mellinKernel a f s (v, t)) hi).symm
    _ = ∫ v : ℝ in Ioi 0, ((Real.exp (-v) : ℂ) *
          (v : ℂ) ^ (-(a : ℂ) * s)) * mellin f s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only [mellinKernel]
      simp_rw [mul_left_comm ( _ ^ (s - 1)) (Real.exp (-v) : ℂ)]
      rw [integral_const_mul]
      change (Real.exp (-v) : ℂ) * mellin (fun t => f (t * v ^ a)) s = _
      rw [mellin_comp_mul_right f s (Real.rpow_pos_of_pos hv a), smul_eq_mul,
        rpow_cpow hv a s]
      ring
    _ = _ := by rw [integral_mul_const, gamma_kernel_integral a s hs]

/-- Ordinary scalar decay hypotheses give absolute Mellin convergence. -/
theorem mellinConvergent_of_rapidDecay {f : ℝ → ℂ}
    (hloc : LocallyIntegrableOn f (Ioi 0))
    (hzero : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))))
    (hTop : ∀ N : ℝ, f =O[atTop] (fun t : ℝ => t ^ (-N)))
    {s : ℂ} (hs : 0 < s.re) : MellinConvergent f s := by
  exact mellinConvergent_of_isBigO_rpow hloc (hTop (s.re + 1)) (by linarith) hzero hs

/-- The manuscript's narrow-strip identity, obtained from decay and Fubini. -/
theorem hasMellin_expRandomization_of_rapidDecay {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : Measurable f)
    (hloc : LocallyIntegrableOn f (Ioi 0))
    (hzero : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))))
    (hTop : ∀ N : ℝ, f =O[atTop] (fun t : ℝ => t ^ (-N)))
    {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1 / a) :
    HasMellin (expRandomization a f) s (Gamma (1 - (a : ℂ) * s) * mellin f s) := by
  have hfs := mellinConvergent_of_rapidDecay hloc hzero hTop hs₀
  have hs : a * s.re < 1 := by simpa [mul_comm] using (lt_div_iff₀ ha).mp hs₁
  exact ⟨expRandomization_mellinConvergent a hf hfs hs, mellin_expRandomization a hf hfs hs⟩

/-- The original Fourier Mellin transform is holomorphic on the full right half-plane. -/
theorem mellin_differentiableOn_of_rapidDecay {f : ℝ → ℂ}
    (hloc : LocallyIntegrableOn f (Ioi 0))
    (hzero : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))))
    (hTop : ∀ N : ℝ, f =O[atTop] (fun t : ℝ => t ^ (-N))) :
    DifferentiableOn ℂ (mellin f) {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (mellin_differentiableAt_of_isBigO_rpow hloc (hTop (s.re + 1))
    (by linarith) hzero hs).differentiableWithinAt

/-- For bounded inputs, the randomized integral converges at every real argument. -/
theorem expRandomization_integrable_of_bounded (a t : ℝ) {f : ℝ → ℂ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    IntegrableOn (fun v : ℝ => (Real.exp (-v) : ℂ) * f (t * v ^ a)) (Ioi 0) := by
  have hexp : IntegrableOn (fun v : ℝ => Real.exp (-v) * C) (Ioi 0) := by
    simpa [IntegrableOn] using (Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1)).mul_const C
  refine hexp.mono' ?_ ?_
  · exact ((measurable_ofReal.comp measurable_id.neg.exp).mul
      (hf.comp (measurable_const.mul (measurable_id.pow_const a)))).aestronglyMeasurable
  · exact ae_of_all _ fun v => by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos (-v))]
      exact mul_le_mul_of_nonneg_left (hC _) (Real.exp_pos _).le

/-- Taking real parts commutes with exponential randomization. -/
theorem expRandomization_realPart (a t : ℝ) {f : ℝ → ℂ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    expRandomization a (fun u => ((f u).re : ℂ)) t =
      ((expRandomization a f t).re : ℂ) := by
  have hi := expRandomization_integrable_of_bounded a t hf hC
  calc
    _ = ∫ v : ℝ in Ioi 0, (((Real.exp (-v) : ℂ) * f (t * v ^ a)).re : ℂ) := by
      apply integral_congr_ae
      filter_upwards with v
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, ofReal_mul]
    _ = _ := by
      rw [integral_complex_ofReal]
      exact congrArg Complex.ofReal (integral_re hi)

/-- The mean-one exponential expectation is its actual density integral. -/
lemma integral_expMeasure_one (g : ℝ → ℂ) :
    (∫ v, g v ∂expMeasure 1) = ∫ v : ℝ in Ioi 0, (Real.exp (-v) : ℂ) * g v := by
  change (∫ v, g v ∂volume.withDensity (gammaPDF 1 1)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (f := gammaPDF 1 1) (by unfold gammaPDF; fun_prop)
    (ae_of_all _ fun v => ENNReal.ofReal_lt_top)]
  have hp (v : ℝ) : (gammaPDF 1 1 v).toReal = if 0 ≤ v then Real.exp (-v) else 0 := by
    simp only [gammaPDF, gammaPDFReal, Real.rpow_one, Real.Gamma_one, div_one,
      sub_self, Real.rpow_zero, mul_one, one_mul]
    split_ifs <;> simp_all [ENNReal.toReal_ofReal, (Real.exp_pos (-v)).le]
  simp_rw [hp, ite_smul, zero_smul]
  change (∫ v, (Ici (0 : ℝ)).indicator (fun v => Real.exp (-v) • g v) v) = _
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  simp only [Complex.real_smul]

/-- Actual law of `E^a * L` on the product of the exponential and limit laws. -/
noncomputable def randomizedLaw (a : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  ((expMeasure 1).prod μ).map (fun p : ℝ × ℝ => p.1 ^ a * p.2)

/-- Exponential randomization of a true characteristic function, derived by Fubini. -/
theorem charFun_randomizedLaw (a : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    charFun (randomizedLaw a μ) t = expRandomization a (charFun μ) t := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  let G : ℝ × ℝ → ℂ := fun p => Complex.exp ((t * (p.1 ^ a * p.2) : ℝ) * I)
  have hG : Integrable G ((expMeasure 1).prod μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun p => (norm_exp_ofReal_mul_I _).le
  rw [charFun_apply_real, randomizedLaw, integral_map (by fun_prop) (by fun_prop)]
  simp only [← ofReal_mul]
  change (∫ p, G p ∂(expMeasure 1).prod μ) = _
  rw [integral_prod _ hG]
  calc
    _ = ∫ v, charFun μ (t * v ^ a) ∂expMeasure 1 := by
      apply integral_congr_ae
      filter_upwards with v
      rw [charFun_apply_real]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [G]
      congr 1
      push_cast
      ring
    _ = _ := integral_expMeasure_one _


/-- The real formula used for `A` in the manuscript. -/
theorem re_charFun_randomizedLaw (a : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (charFun (randomizedLaw a μ) t).re =
      ∫ v : ℝ in Ioi 0, Real.exp (-v) * (charFun μ (t * v ^ a)).re := by
  rw [charFun_randomizedLaw, expRandomization]
  have hi := expRandomization_integrable_of_bounded a t
    (measurable_charFun (μ := μ)) (norm_charFun_le_one (μ := μ))
  have hr : (∫ v : ℝ in Ioi 0, (Real.exp (-v) : ℂ) * charFun μ (t * v ^ a)).re =
      ∫ v : ℝ in Ioi 0, ((Real.exp (-v) : ℂ) * charFun μ (t * v ^ a)).re :=
    (integral_re hi).symm
  simpa only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] using hr

/-- A characteristic function supplies boundedness, measurability, and local integrability.
The sole analytic assumption here is the cited Fourier decay of its real part. -/
theorem hasMellin_re_charFun_randomizedLaw_of_rapidDecay {a : ℝ} (ha : 0 < a)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hTop : ∀ N : ℝ, (fun t => ((charFun μ t).re : ℂ)) =O[atTop]
      (fun t : ℝ => t ^ (-N)))
    {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1 / a) :
    HasMellin (fun t => ((charFun (randomizedLaw a μ) t).re : ℂ)) s
      (Gamma (1 - (a : ℂ) * s) * mellin (fun t => ((charFun μ t).re : ℂ)) s) := by
  let f : ℝ → ℂ := fun t => ((charFun μ t).re : ℂ)
  have hf : Measurable f := measurable_ofReal.comp (Complex.measurable_re.comp measurable_charFun)
  have hb (t : ℝ) : ‖f t‖ ≤ 1 := by
    simpa only [f, Complex.norm_real, Real.norm_eq_abs] using
      (abs_re_le_norm (charFun μ t)).trans (norm_charFun_le_one t)
  have hloc : LocallyIntegrableOn f (Ioi 0) := by
    apply ((locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn (Ioi 0)).mono
      hf.aestronglyMeasurable
    exact ae_of_all _ fun t => by simpa using hb t
  have hzero : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall fun t => by simpa using hb t
  have hid := hasMellin_expRandomization_of_rapidDecay ha hf hloc hzero hTop hs₀ hs₁
  have heq : expRandomization a f = fun t => ((charFun (randomizedLaw a μ) t).re : ℂ) := by
    funext t
    rw [charFun_randomizedLaw]
    exact expRandomization_realPart a t measurable_charFun norm_charFun_le_one
  rw [heq] at hid
  exact hid


@[instance] theorem randomizedLaw_isProbabilityMeasure (a : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (randomizedLaw a μ) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The complex characteristic-function version needs only its absolutely convergent Mellin integral. -/
theorem hasMellin_charFun_randomizedLaw (a : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℂ} (hfs : MellinConvergent (charFun μ) s) (hs : a * s.re < 1) :
    HasMellin (charFun (randomizedLaw a μ)) s
      (Gamma (1 - (a : ℂ) * s) * mellin (charFun μ) s) := by
  have heq : expRandomization a (charFun μ) = charFun (randomizedLaw a μ) :=
    (funext (charFun_randomizedLaw a μ)).symm
  rw [← heq]
  exact ⟨expRandomization_mellinConvergent a measurable_charFun hfs hs,
    mellin_expRandomization a measurable_charFun hfs hs⟩

/-- Jacobian-adjusted inverse-power weight, with `t = u^(-a)`. In the manuscript
`A = H cos θ` and `u = H sin^(-1/a) θ`, so this is `a cos θ sin^(1/a) θ`. -/
noncomputable def inversePowerWeight (a : ℝ) (A : ℝ → ℂ) (u : ℝ) : ℂ :=
  (a : ℂ) * ((u : ℂ) ^ (-1 : ℂ) * A (u ^ (-a)))

lemma inversePower_exponent {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (1 - (a : ℂ) * s + (-1 : ℂ)) / ((-a : ℝ) : ℂ) = s := by
  have hn : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  rw [ofReal_neg]
  field_simp [hn]
  ring

/-- The Mellin substitution `t = u^(-a)` is a theorem about actual integrals. -/
theorem mellin_inversePowerWeight {a : ℝ} (ha : 0 < a) (A : ℝ → ℂ) (s : ℂ) :
    mellin (inversePowerWeight a A) (1 - (a : ℂ) * s) = mellin A s := by
  change mellin (fun u => (a : ℂ) • ((u : ℂ) ^ (-1 : ℂ) • A (u ^ (-a))))
    (1 - (a : ℂ) * s) = _
  rw [mellin_const_smul, mellin_cpow_smul, mellin_comp_rpow,
    inversePower_exponent ha s, abs_neg, abs_of_pos ha]
  simp only [Complex.real_smul, smul_eq_mul, ofReal_inv]
  rw [← mul_assoc, mul_inv_cancel₀ (ofReal_ne_zero.mpr ha.ne'), one_mul]

/-- Absolute convergence is preserved by the inverse-power substitution. -/
theorem inversePowerWeight_mellinConvergent {a : ℝ} (ha : 0 < a) {A : ℝ → ℂ}
    {s : ℂ} (hA : MellinConvergent A s) :
    MellinConvergent (inversePowerWeight a A) (1 - (a : ℂ) * s) := by
  have hcomp : MellinConvergent (fun u => A (u ^ (-a)))
      (1 - (a : ℂ) * s + (-1 : ℂ)) := by
    apply (MellinConvergent.comp_rpow (neg_ne_zero.mpr ha.ne')).mpr
    simpa only [inversePower_exponent ha s] using hA
  have hmul : MellinConvergent
      (fun u => (u : ℂ) ^ (-1 : ℂ) • A (u ^ (-a))) (1 - (a : ℂ) * s) :=
    MellinConvergent.cpow_smul.mpr hcomp
  exact hmul.const_smul (a : ℂ)

/-- This supplies the initial identity in `AnalyticThresholdMellin.mellin_continuation`
for the weight constructed from the randomized transform, without assuming that identity. -/
theorem hasMellin_inversePowerWeight_expRandomization {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : Measurable f) {s : ℂ}
    (hfs : MellinConvergent f s) (hs : a * s.re < 1) :
    HasMellin (inversePowerWeight a (expRandomization a f)) (1 - (a : ℂ) * s)
      (Gamma (1 - (a : ℂ) * s) * mellin f s) := by
  refine ⟨inversePowerWeight_mellinConvergent ha
    (expRandomization_mellinConvergent a hf hfs hs), ?_⟩
  rw [mellin_inversePowerWeight ha, mellin_expRandomization a hf hfs hs]
end Kagey131.PaperD.AnalyticThresholdRandomization


