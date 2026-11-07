import PaperD.EJPAnalyticThresholdRandomization
import PaperD.EJPAnalyticThresholdParamChart
import PaperD.EJPAnalyticThresholdCurvature

/-!
# Continuation from the conditional law to the curvature integral

The input law is the actual conditional probability measure `μ`. Its
`ConditionalFourierHyp` supplies the classical smoothing and inversion data.
The existing decay theorem gives arbitrary polynomial decay of `re (charFun μ)`;
therefore its Mellin transform converges and is holomorphic for `re s > 0`.

The only model identification input is pointwise on the positive half-line:
`weight c = inversePowerWeight a (re (charFun (randomizedLaw a μ)))`.
Exponential randomization and the inverse-power Mellin substitution derive the
initial narrow-strip identity. The chart supplies both integrations by parts,
all boundary terms, and cubic decay. The existing identity theorem then extends
the Mellin formula to the larger strip containing `s = 3`.

At `s = 3`, real-power and real-Gamma compatibility turn the continued complex
integral into an absolutely convergent real integral. The previously derived
Fourier curvature formula gives its exact coefficient. Neither a narrow-strip
identity nor a curvature formula is assumed.

`curvature_integral_chartOfRoot` is the assembly interface. It needs only
`0 < a < 1`, `ConditionalFourierHyp a g (charFun μ)`, `RootData a H Y`, and
the pointwise weight identification for the constructed `chartOfRoot`.
-/
open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology
namespace Kagey131.PaperD.AnalyticThresholdContinuation
open Modes AnalyticThresholdRandomization AnalyticThresholdParam AnalyticThresholdMellin

/-- The smoothing theorem gives arbitrary polynomial decay of the actual fair transform. -/
theorem realPart_rapidDecay_of_conditionalFourierHyp {a : ℝ} {g : ℝ → ℝ} {φ : ℝ → ℂ}
    (ha₀ : 0 < a) (ha₁ : a < 1) (hφ : ConditionalFourierHyp a g φ) (N : ℝ) :
    (fun t => ((φ t).re : ℂ)) =O[atTop] (fun t : ℝ => t ^ (-N)) := by
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
  have hstretched : (fun t => ((φ t).re : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-c*t^r)) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    calc
      _ ≤ ‖φ t‖ := by simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_re_le_norm (φ t)
      _ ≤ 2 * ‖Real.exp (-c*t^r)‖ := by
        simpa only [abs_of_nonneg ht, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hbound t
  have hexp : (fun t => ((φ t).re : ℂ)) =O[atTop] (fun t : ℝ => Real.exp (-t)) := by
    apply hstretched.trans
    simpa only [zero_mul, zero_sub, neg_mul] using (weighted_stretched_exp_littleO hc hr 0).isBigO
  apply hexp.trans
  simpa only [neg_mul, one_mul] using
    (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0 : ℝ) < 1) (-N)).isBigO

/-- Mellin convergence and holomorphy are derived from the classical conditional data. -/
theorem conditional_realPart_mellin {a : ℝ} {g : ℝ → ℝ} {φ : ℝ → ℂ}
    (ha₀ : 0 < a) (ha₁ : a < 1) (hφ : ConditionalFourierHyp a g φ) :
    (∀ s : ℂ, 0 < s.re → MellinConvergent (fun t => ((φ t).re : ℂ)) s) ∧
      DifferentiableOn ℂ (mellin (fun t => ((φ t).re : ℂ))) {s : ℂ | 0 < s.re} := by
  have hcont : Continuous (fun t => ((φ t).re : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_re.comp hφ.continuous)
  have hloc : LocallyIntegrableOn (fun t => ((φ t).re : ℂ)) (Ioi 0) :=
    hcont.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hzero : (fun t => ((φ t).re : ℂ)) =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply IsBigO.of_bound 1
    apply Eventually.of_forall
    intro t
    simpa only [neg_zero, Real.rpow_zero, norm_one, one_mul, Complex.norm_real,
      Real.norm_eq_abs] using (abs_re_le_norm (φ t)).trans (hφ.unit_bound t)
  have hTop := realPart_rapidDecay_of_conditionalFourierHyp ha₀ ha₁ hφ
  exact ⟨fun s hs => mellinConvergent_of_rapidDecay hloc hzero hTop hs,
    mellin_differentiableOn_of_rapidDecay hloc hzero hTop⟩

/-- Continuation of the actual fair conditional transform. The only identification
input is the pointwise equality of the chart weight with the randomized weight. -/
theorem continued_mellin_of_weight_identification {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hφ : ConditionalFourierHyp a g (charFun μ)) {H : ℝ → ℝ} (c : AngleChart a H)
    (hH : ContinuousAt H 0) (hH0 : H 0 = 1)
    (htop : Tendsto c.angle atTop (𝓝 0)) {θ₀ : ℝ}
    (hzero : Tendsto c.angle (𝓝[>] 0) (𝓝 θ₀))
    (hweight : ∀ u ∈ Ioi (0 : ℝ), (weight c u : ℂ) =
      inversePowerWeight a (fun t => ((charFun (randomizedLaw a μ) t).re : ℂ)) u) :
    ∀ s ∈ strip a 3,
      MellinConvergent (fun u => (weight₂ c u : ℂ)) (3 - (a : ℂ) * s) ∧
      mellin (fun t => ((charFun μ t).re : ℂ)) s =
        (Complex.Gamma (3 - (a : ℂ) * s))⁻¹ *
          ∫ u : ℝ in Ioi 0, (u : ℂ) ^ (2 - (a : ℂ) * s) * (weight₂ c u : ℂ) := by
  let f : ℝ → ℂ := fun t => ((charFun μ t).re : ℂ)
  have hm := conditional_realPart_mellin ha₀ ha₁ hφ
  have hf : Measurable f := measurable_ofReal.comp (Complex.measurable_re.comp measurable_charFun)
  have hrandom : expRandomization a f = fun t => ((charFun (randomizedLaw a μ) t).re : ℂ) := by
    funext t
    rw [charFun_randomizedLaw]
    exact expRandomization_realPart a t measurable_charFun norm_charFun_le_one
  have hinitial : ∀ s ∈ strip a 1,
      mellin (fun u => (weight c u : ℂ)) (1 - (a : ℂ) * s) =
        Complex.Gamma (1 - (a : ℂ) * s) * mellin f s := by
    intro s hs
    have hsN : a * s.re < 1 := by simpa only [mul_comm] using (lt_div_iff₀ ha₀).mp hs.2
    have hid := (hasMellin_inversePowerWeight_expRandomization ha₀ hf (hm.1 s hs.1) hsN).2
    calc
      _ = mellin (inversePowerWeight a (expRandomization a f)) (1 - (a : ℂ) * s) := by
        unfold mellin
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        dsimp only
        rw [hweight u hu, hrandom]
      _ = _ := hid
  have hparts : ∀ s ∈ strip a 1, TwiceAdmissible
      (fun u => (weight c u : ℂ)) (fun u => (weight₁ c u : ℂ))
      (fun u => (weight₂ c u : ℂ)) (1 - (a : ℂ) * s) := by
    intro s hs
    have hsN : a * s.re < 1 := by simpa only [mul_comm] using (lt_div_iff₀ ha₀).mp hs.2
    have hsP := mul_pos ha₀ hs.1
    apply twiceAdmissible ha₀ c hH hH0 htop hzero
    all_goals simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]; linarith
  have hloc : LocallyIntegrableOn (fun u => (weight₂ c u : ℂ)) (Ioi 0) :=
    (Complex.continuous_ofReal.comp_continuousOn
      ((weight₂_continuous ha₀).comp_continuousOn c.continuous)).locallyIntegrableOn measurableSet_Ioi
  have hdecay := ofReal_isBigO (weight_decay c hH hH0 htop).2.2
  have hbounded : (fun u => (weight₂ c u : ℂ)) =O[𝓝[>] 0] (fun u : ℝ => u ^ (-(0 : ℝ))) := by
    simpa only [neg_zero, Real.rpow_zero] using ofReal_isBigO (weight_zero_bounds ha₀ c hzero).2.2
  exact mellin_continuation ha₀ (fun u => (weight c u : ℂ))
    (fun u => (weight₁ c u : ℂ)) (fun u => (weight₂ c u : ℂ)) (mellin f)
    (hm.2.mono fun s hs => hs.1) hloc hdecay hbounded hparts hinitial


/-- A real power on the positive half-line gives the embedded real Bochner integral. -/
lemma integral_realPower_ofReal (p : ℝ) (w : ℝ → ℝ) :
    (∫ u : ℝ in Ioi 0, (u : ℂ) ^ (p : ℂ) * (w u : ℂ)) =
      ((∫ u : ℝ in Ioi 0, u ^ p * w u : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [ofReal_mul, ofReal_cpow hu.le]

/-- The central curvature and absolute convergence of the continued real integral.
Only the pointwise chart/randomization identification remains a model input. -/
theorem curvature_integral_of_weight_identification {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hφ : ConditionalFourierHyp a g (charFun μ)) {H : ℝ → ℝ} (c : AngleChart a H)
    (hH : ContinuousAt H 0) (hH0 : H 0 = 1)
    (htop : Tendsto c.angle atTop (𝓝 0)) {θ₀ : ℝ}
    (hzero : Tendsto c.angle (𝓝[>] 0) (𝓝 θ₀))
    (hweight : ∀ u ∈ Ioi (0 : ℝ), (weight c u : ℂ) =
      inversePowerWeight a (fun t => ((charFun (randomizedLaw a μ) t).re : ℂ)) u) :
    IntegrableOn (fun u : ℝ => u ^ (2 - 3*a) * weight₂ c u) (Ioi 0) ∧
      deriv (deriv g) 0 = -((Real.Gamma (3 - 3*a))⁻¹) / Real.pi *
        ∫ u : ℝ in Ioi 0, u ^ (2 - 3*a) * weight₂ c u := by
  obtain ⟨hconv, heq⟩ := continued_mellin_of_weight_identification ha₀ ha₁ μ hφ c
    hH hH0 htop hzero hweight 3 (three_mem_strip ha₀ ha₁)
  have hgamma : (3 : ℂ) - (a : ℂ) * 3 = ((3 - 3*a : ℝ) : ℂ) := by push_cast; ring
  have hpower : (2 : ℂ) - (a : ℂ) * 3 = ((2 - 3*a : ℝ) : ℂ) := by push_cast; ring
  have hint : IntegrableOn (fun u : ℝ => u ^ (2 - 3*a) * weight₂ c u) (Ioi 0) := by
    have hi : Integrable (fun u : ℝ => (u : ℂ) ^ ((2 - 3*a : ℝ) : ℂ) * (weight₂ c u : ℂ))
        (volume.restrict (Ioi 0)) := by
      simpa only [MellinConvergent, IntegrableOn, smul_eq_mul,
        show (3 : ℂ) - (a : ℂ) * 3 - 1 = ((2 - 3*a : ℝ) : ℂ) by push_cast; ring] using hconv
    apply hi.re.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change ((u : ℂ) ^ ((2 - 3*a : ℝ) : ℂ) * (weight₂ c u : ℂ)).re = _
    rw [← ofReal_cpow hu.le]
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  have hreal : (mellin (fun t => ((charFun μ t).re : ℂ)) 3).re =
      (Real.Gamma (3 - 3*a))⁻¹ * ∫ u : ℝ in Ioi 0, u ^ (2 - 3*a) * weight₂ c u := by
    rw [heq, hgamma, hpower, Complex.Gamma_ofReal, integral_realPower_ofReal]
    simp only [← ofReal_inv, ← ofReal_mul, ofReal_re]
  refine ⟨hint, ?_⟩
  rw [AnalyticThresholdCurvature.central_curvature_charFun ha₀ ha₁ μ hφ, hreal]
  ring

/-- Assembly interface for the inverse chart constructed from the H root data.
The endpoint and differential hypotheses are obtained from that construction. -/
theorem curvature_integral_chartOfRoot {a Y : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hφ : ConditionalFourierHyp a g (charFun μ)) {H : ℝ → ℝ} (d : RootData a H Y)
    (hweight : ∀ u ∈ Ioi (0 : ℝ), (weight (chartOfRoot ha₀ d) u : ℂ) =
      inversePowerWeight a (fun t => ((charFun (randomizedLaw a μ) t).re : ℂ)) u) :
    IntegrableOn (fun u : ℝ => u ^ (2 - 3*a) * weight₂ (chartOfRoot ha₀ d) u) (Ioi 0) ∧
      deriv (deriv g) 0 = -((Real.Gamma (3 - 3*a))⁻¹) / Real.pi *
        ∫ u : ℝ in Ioi 0, u ^ (2 - 3*a) * weight₂ (chartOfRoot ha₀ d) u := by
  exact curvature_integral_of_weight_identification ha₀ ha₁ μ hφ (chartOfRoot ha₀ d)
    d.continuous_zero d.value_zero (chartOfRoot_top ha₀ d) (chartOfRoot_zero ha₀ d) hweight
end Kagey131.PaperD.AnalyticThresholdContinuation

