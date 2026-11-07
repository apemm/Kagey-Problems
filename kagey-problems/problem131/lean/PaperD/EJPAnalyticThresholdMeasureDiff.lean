import PaperD.EJPAnalyticThresholdMeasureBounds

/-!
# Differentiation of the actual normalized density

The hypotheses concern only `K`, its derivatives, and their scalar bounds.
The density derivative, the integrable domination, and the covariance formula
are proved here. Strict score monotonicity is the separate order input.
-/

namespace Kagey131.PaperD.Modes.AnalyticThreshold

open MeasureTheory Set Filter
open scoped Topology

theorem hasDerivAt_analyticWeight {K Ka : ℝ → ℝ → ℝ} {a u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hK : 0 < K a u)
    (hd : HasDerivAt (fun b => K b u) (Ka a u) a) :
    HasDerivAt (fun b => analyticWeight K b u)
      (analyticWeight K a u * logWeightScore (K a) (Ka a) (3 * a - 2) u) a := by
  have hs : HasDerivAt (fun b : ℝ => -(3 * b - 2)) (-3) a := by
    convert! (((hasDerivAt_id a).const_mul 3).sub_const 2).neg using 1
    norm_num
  have hx := (hasDerivAt_const a (1 - u)).rpow hs (sub_pos.mpr hu.2)
  have hk := hd.rpow hs hK
  have hr : K a u ^ (-(3 * a - 2) - 1) = K a u ^ (-(3 * a - 2)) / K a u := by
    rw [Real.rpow_sub hK, Real.rpow_one]
  apply ((hx.const_mul (u ^ (1 / 2 : ℝ))).mul hk).congr_deriv
  try dsimp
  rw [hr]
  unfold analyticWeight logWeightScore
  ring

theorem score_eq_weight_deriv_div {K Ka : ℝ → ℝ → ℝ} {a u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hK : 0 < K a u)
    (hd : HasDerivAt (fun b => K b u) (Ka a u) a) :
    deriv (fun b => analyticWeight K b u) a / analyticWeight K a u =
      logWeightScore (K a) (Ka a) (3 * a - 2) u := by
  rw [(hasDerivAt_analyticWeight hu hK hd).deriv]
  exact mul_div_cancel_left₀ _ (analyticWeight_pos hu hK).ne'

theorem hasDerivAt_relativeAnalyticWeight {K Ka : ℝ → ℝ → ℝ} {a b u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hK : 0 < K b u)
    (hd : HasDerivAt (fun c => K c u) (Ka b u) b) :
    HasDerivAt (fun c => relativeAnalyticWeight K a c u)
      (relativeAnalyticWeightDeriv K Ka a b u) b :=
  (hasDerivAt_analyticWeight hu hK hd).div_const _

lemma relativeAnalyticWeightDeriv_base {K Ka : ℝ → ℝ → ℝ} {a u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hK : 0 < K a u) :
    relativeAnalyticWeightDeriv K Ka a a u =
      logWeightScore (K a) (Ka a) (3 * a - 2) u :=
  mul_div_cancel_left₀ _ (analyticWeight_pos hu hK).ne'

/-- Dominated differentiation of both unnormalized Bochner integrals.
There is no score monotonicity hypothesis in this analytic statement. -/
theorem analyticWeight_integrals_hasDerivAt
    {K Ka : ℝ → ℝ → ℝ} {a B C : ℝ}
    (ha : a ∈ Ioo (2 / 3 : ℝ) (69 / 100))
    (hm : ∀ b, Measurable (K b)) (hmKa : Measurable (Ka a))
    (hK : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K b u)
    (hKB : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), ∀ u ∈ Ioo (0 : ℝ) 1, K b u ≤ B)
    (hKa : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), ∀ u ∈ Ioo (0 : ℝ) 1, |Ka b u| ≤ C)
    (hd : ∀ u ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100),
      HasDerivAt (fun c => K c u) (Ka b u) b) :
    Integrable (fun u => analyticWeight K a u *
      logWeightScore (K a) (Ka a) (3 * a - 2) u) unitIntervalVolume ∧
    HasDerivAt (fun b => weightNormalizer (analyticWeight K b))
      (∫ u, analyticWeight K a u * logWeightScore (K a) (Ka a) (3 * a - 2) u
        ∂unitIntervalVolume) a ∧
    HasDerivAt (fun b => ∫ u, u * analyticWeight K b u ∂unitIntervalVolume)
      (∫ u, u * (analyticWeight K a u * logWeightScore (K a) (Ka a) (3 * a - 2) u)
        ∂unitIntervalVolume) a := by
  have hac : a ∈ Icc (2 / 3 : ℝ) (69 / 100) := ⟨ha.1.le, ha.2.le⟩
  let D := fun b u => analyticWeight K b u * logWeightScore (K b) (Ka b) (3 * b - 2) u
  have hmD : AEStronglyMeasurable (D a) unitIntervalVolume := by
    have hw := measurable_analyticWeight (hm a)
    have hmK := hm a
    have hs : Measurable (logWeightScore (K a) (Ka a) (3 * a - 2)) := by
      unfold logWeightScore
      fun_prop
    exact (hw.mul hs).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂unitIntervalVolume,
      ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), ‖D b u‖ ≤ (3 + 3 * B + C) * endpointEnvelope u := by
    filter_upwards [unitIntervalVolume_ae_mem] with u hu b hb
    exact analyticWeight_score_bound hb hu (hK b hb u hu) (hKB b hb u hu) (hKa b hb u hu)
  have hdiff : ∀ᵐ u ∂unitIntervalVolume, ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100),
      HasDerivAt (fun c => analyticWeight K c u) (D b u) b := by
    filter_upwards [unitIntervalVolume_ae_mem] with u hu b hb
    exact hasDerivAt_analyticWeight hu (lt_of_lt_of_le zero_lt_one (hK b hb u hu))
      (hd u hu b hb)
  have hwi := integrable_analyticWeight hac (hm a) (hK a hac)
  have henv := integrable_endpointEnvelope.const_mul (3 + 3 * B + C)
  obtain ⟨hi, hZ⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Icc_mem_nhds ha.1 ha.2)
    (Eventually.of_forall fun b => (measurable_analyticWeight (hm b)).aestronglyMeasurable)
    hwi hmD hbound henv hdiff
  refine ⟨hi, hZ, ?_⟩
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b u => u * analyticWeight K b u) (F' := fun b u => u * D b u)
    (Icc_mem_nhds ha.1 ha.2) _ (integrable_coordinate_mul unitIntervalVolume_ae_mem hwi)
    (measurable_id.aestronglyMeasurable.mul hmD) _ henv _).2
  · exact Eventually.of_forall fun b =>
      (measurable_id.mul (measurable_analyticWeight (hm b))).aestronglyMeasurable
  · filter_upwards [unitIntervalVolume_ae_mem, hbound] with u hu hb b hbs
    calc
      ‖u * D b u‖ = ‖u‖ * ‖D b u‖ := norm_mul _ _
      _ ≤ 1 * ‖D b u‖ := mul_le_mul_of_nonneg_right
        (by simpa [Real.norm_eq_abs, abs_of_pos hu.1] using hu.2.le) (norm_nonneg _)
      _ ≤ _ := by simpa using hb b hbs
  · filter_upwards [hdiff] with u hu b hb
    exact (hu b hb).const_mul u

lemma measurable_logWeightScore {K Ka : ℝ → ℝ} (hK : Measurable K)
    (hKa : Measurable Ka) (s : ℝ) : Measurable (logWeightScore K Ka s) := by
  unfold logWeightScore
  fun_prop

theorem integrable_analyticScore {K Ka : ℝ → ℝ → ℝ} {a B C : ℝ}
    (ha : a ∈ Icc (2 / 3 : ℝ) (69 / 100))
    (hm : Measurable (K a)) (hmKa : Measurable (Ka a))
    (hK : ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K a u)
    (hKB : ∀ u ∈ Ioo (0 : ℝ) 1, K a u ≤ B)
    (hKa : ∀ u ∈ Ioo (0 : ℝ) 1, |Ka a u| ≤ C) :
    Integrable (logWeightScore (K a) (Ka a) (3 * a - 2)) (analyticProbability K a) := by
  rw [analyticProbability, integrable_weightedIntervalProbability_iff
    (measurable_analyticWeight hm) (integrable_analyticWeight ha hm hK)
    (fun u hu => analyticWeight_pos hu (lt_of_lt_of_le zero_lt_one (hK u hu)))]
  apply (integrable_endpointEnvelope.const_mul (3 + 3 * B + C)).mono'
    ((measurable_analyticWeight hm).mul (measurable_logWeightScore hm hmKa _)).aestronglyMeasurable
  filter_upwards [unitIntervalVolume_ae_mem] with u hu
  exact analyticWeight_score_bound ha hu (hK u hu) (hKB u hu) (hKa u hu)

noncomputable def relativeDerivativeEnvelope (K : ℝ → ℝ → ℝ) (a B C u : ℝ) : ℝ :=
  (3 + 3 * B + C) * endpointEnvelope u / analyticWeight K a u

theorem integrable_relativeDerivativeEnvelope {K : ℝ → ℝ → ℝ} {a B C : ℝ}
    (ha : a ∈ Icc (2 / 3 : ℝ) (69 / 100)) (hm : Measurable (K a))
    (hK : ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K a u) :
    Integrable (relativeDerivativeEnvelope K a B C) (analyticProbability K a) := by
  rw [analyticProbability, integrable_weightedIntervalProbability_iff
    (measurable_analyticWeight hm) (integrable_analyticWeight ha hm hK)
    (fun u hu => analyticWeight_pos hu (lt_of_lt_of_le zero_lt_one (hK u hu)))]
  apply (integrable_endpointEnvelope.const_mul (3 + 3 * B + C)).congr
  filter_upwards [unitIntervalVolume_ae_mem] with u hu
  dsimp [relativeDerivativeEnvelope]
  field_simp [(analyticWeight_pos hu (lt_of_lt_of_le zero_lt_one (hK u hu))).ne']

theorem relativeAnalyticWeightDeriv_bound {K Ka : ℝ → ℝ → ℝ} {a b u B C : ℝ}
    (hb : b ∈ Icc (2 / 3 : ℝ) (69 / 100)) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hKa : 1 ≤ K a u) (hKb : 1 ≤ K b u) (hKB : K b u ≤ B)
    (hder : |Ka b u| ≤ C) :
    ‖relativeAnalyticWeightDeriv K Ka a b u‖ ≤ relativeDerivativeEnvelope K a B C u := by
  have hp := analyticWeight_pos hu (lt_of_lt_of_le zero_lt_one hKa)
  simp only [relativeAnalyticWeightDeriv, norm_div, Real.norm_eq_abs, abs_of_pos hp]
  change ‖analyticWeight K b u * logWeightScore (K b) (Ka b) (3 * b - 2) u‖ /
    analyticWeight K a u ≤ (3 + 3 * B + C) * endpointEnvelope u / analyticWeight K a u
  exact div_le_div_of_nonneg_right (analyticWeight_score_bound hb hu hKb hKB hder) hp.le

/-- All analytic inputs required by dominated differentiation, stated solely
for `K`. The band is a genuine neighborhood at each interior parameter. -/
theorem normalizedMean_actual_derivative_pos
    {K Ka : ℝ → ℝ → ℝ} {a B C : ℝ}
    (ha : a ∈ Ioo (2 / 3 : ℝ) (69 / 100))
    (hm : ∀ b, Measurable (K b)) (hmKa : Measurable (Ka a))
    (hK : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K b u)
    (hKB : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), ∀ u ∈ Ioo (0 : ℝ) 1, K b u ≤ B)
    (hKa : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), ∀ u ∈ Ioo (0 : ℝ) 1, |Ka b u| ≤ C)
    (hd : ∀ u ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100),
      HasDerivAt (fun c => K c u) (Ka b u) b)
    (hstrict : StrictMonoOn (logWeightScore (K a) (Ka a) (3 * a - 2)) (Ioo (0 : ℝ) 1)) :
    0 < ProbabilityTheory.covariance (fun u : ℝ => u)
        (logWeightScore (K a) (Ka a) (3 * a - 2)) (analyticProbability K a) ∧
      HasDerivAt (fun b =>
        (∫ u, u * analyticWeight K b u ∂unitIntervalVolume) /
          weightNormalizer (analyticWeight K b))
        (ProbabilityTheory.covariance (fun u : ℝ => u)
          (logWeightScore (K a) (Ka a) (3 * a - 2)) (analyticProbability K a)) a := by
  have hac : a ∈ Icc (2 / 3 : ℝ) (69 / 100) := ⟨ha.1.le, ha.2.le⟩
  have hp : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < K a u :=
    fun u hu => lt_of_lt_of_le zero_lt_one (hK a hac u hu)
  have : IsProbabilityMeasure (analyticProbability K a) :=
    analyticProbability_isProbability hac (hm a) (hK a hac)
  have hsupp : ∀ᵐ u ∂analyticProbability K a, u ∈ Ioo (0 : ℝ) 1 :=
    weightedIntervalProbability_ae_mem (analyticWeight K a)
  have hscore : (relativeAnalyticWeightDeriv K Ka a a) =ᵐ[analyticProbability K a]
      logWeightScore (K a) (Ka a) (3 * a - 2) := by
    filter_upwards [hsupp] with u hu
    exact relativeAnalyticWeightDeriv_base hu (hp u hu)
  have hstrict' : StrictMonoOn (relativeAnalyticWeightDeriv K Ka a a) (Ioo (0 : ℝ) 1) := by
    intro u hu v hv huv
    rw [relativeAnalyticWeightDeriv_base hu (hp u hu),
      relativeAnalyticWeightDeriv_base hv (hp v hv)]
    exact hstrict hu hv huv
  have hmeas : ∀ b, Measurable (relativeAnalyticWeight K a b) := by
    intro b
    exact (measurable_analyticWeight (hm b)).div (measurable_analyticWeight (hm a))
  have hscoremeas : Measurable (relativeAnalyticWeightDeriv K Ka a a) :=
    ((measurable_analyticWeight (hm a)).mul
      (measurable_logWeightScore (hm a) hmKa _)).div (measurable_analyticWeight (hm a))
  obtain ⟨hpos, hmean⟩ := normalizedMean_derivative_pos_of_dominated hsupp
    (analyticProbability_full hac (hm a) (hK a hac))
    (relativeAnalyticWeight_base hp) (Icc_mem_nhds ha.1 ha.2)
    (Eventually.of_forall fun b => (hmeas b).aestronglyMeasurable)
    hscoremeas.aestronglyMeasurable
    (bound := relativeDerivativeEnvelope K a B C)
    (by
      filter_upwards [hsupp] with u hu b hb
      exact relativeAnalyticWeightDeriv_bound hb hu (hK a hac u hu)
        (hK b hb u hu) (hKB b hb u hu) (hKa b hb u hu))
    (integrable_relativeDerivativeEnvelope hac (hm a) (hK a hac))
    (by
      filter_upwards [hsupp] with u hu b hb
      exact hasDerivAt_relativeAnalyticWeight hu
        (lt_of_lt_of_le zero_lt_one (hK b hb u hu)) (hd u hu b hb)) hstrict'
  have hcov : ProbabilityTheory.covariance (fun u : ℝ => u)
      (relativeAnalyticWeightDeriv K Ka a a) (analyticProbability K a) =
      ProbabilityTheory.covariance (fun u : ℝ => u)
        (logWeightScore (K a) (Ka a) (3 * a - 2)) (analyticProbability K a) := by
    unfold ProbabilityTheory.covariance
    rw [integral_congr_ae hscore]
    apply integral_congr_ae
    filter_upwards [hscore] with u hu
    rw [hu]
  rw [hcov] at hpos hmean
  refine ⟨hpos, ?_⟩
  apply hmean.congr_of_eventuallyEq
  exact Eventually.of_forall fun b =>
    (normalizedMean_relativeAnalyticWeight (hm a) (integrable_analyticWeight hac (hm a)
      (hK a hac)) hp b).symm

/-- The covariance derivative for the actual measure-valued construction. -/
theorem analyticMean_derivative_pos
    {K Ka : ℝ → ℝ → ℝ} {a B C : ℝ}
    (ha : a ∈ Ioo (2 / 3 : ℝ) (69 / 100))
    (hm : ∀ b, Measurable (K b)) (hmKa : Measurable (Ka a))
    (hK : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K b u)
    (hKB : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), ∀ u ∈ Ioo (0 : ℝ) 1, K b u ≤ B)
    (hKa : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), ∀ u ∈ Ioo (0 : ℝ) 1, |Ka b u| ≤ C)
    (hd : ∀ u ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100),
      HasDerivAt (fun c => K c u) (Ka b u) b)
    (hstrict : StrictMonoOn (logWeightScore (K a) (Ka a) (3 * a - 2)) (Ioo (0 : ℝ) 1)) :
    HasDerivAt (analyticMean K)
      (ProbabilityTheory.covariance (fun u : ℝ => u)
        (logWeightScore (K a) (Ka a) (3 * a - 2)) (analyticProbability K a)) a ∧
      0 < deriv (analyticMean K) a := by
  obtain ⟨hp, hdmean⟩ := normalizedMean_actual_derivative_pos ha hm hmKa hK hKB hKa hd hstrict
  have heq : analyticMean K =ᶠ[𝓝 a] (fun b =>
      (∫ u, u * analyticWeight K b u ∂unitIntervalVolume) /
        weightNormalizer (analyticWeight K b)) := by
    filter_upwards [Icc_mem_nhds ha.1 ha.2] with b hb
    exact analyticMean_eq_integral_ratio (hm b) (integrable_analyticWeight hb (hm b)
      (hK b hb)) (fun u hu => lt_of_lt_of_le zero_lt_one (hK b hb u hu))
  have hdactual := hdmean.congr_of_eventuallyEq heq
  exact ⟨hdactual, by rw [hdactual.deriv]; exact hp⟩

end Kagey131.PaperD.Modes.AnalyticThreshold
