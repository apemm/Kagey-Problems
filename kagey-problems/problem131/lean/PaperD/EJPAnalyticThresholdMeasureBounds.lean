import PaperD.EJPAnalyticThresholdMeasure

/-!
# Endpoint domination on the short parameter band

The logarithmic envelope is integrable by comparison with `(1-u)^(-57/100)`.
Bounds on `K` and its parameter derivative are scalar inputs; integrability
of the weight and of its derivative are conclusions.
-/

namespace Kagey131.PaperD.Modes.AnalyticThreshold

open MeasureTheory Set Filter
open scoped Topology

noncomputable def endpointEnvelope (u : ℝ) : ℝ :=
  (1 - u) ^ (-(7 / 100 : ℝ)) * (1 + |Real.log (1 - u)|)

lemma endpointEnvelope_nonneg {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 ≤ endpointEnvelope u := by
  unfold endpointEnvelope
  exact mul_nonneg (Real.rpow_nonneg (sub_pos.mpr hu.2).le _) (by positivity)

lemma integrable_endpoint_power {r : ℝ} (hr : -1 < r) :
    Integrable (fun u : ℝ => (1 - u) ^ r) unitIntervalVolume := by
  have h := (intervalIntegral.intervalIntegrable_rpow' hr
    (a := 0) (b := 1)).comp_sub_left 1
  norm_num only [sub_zero, sub_self] at h
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).1
    h.symm

lemma endpointEnvelope_le {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    endpointEnvelope u ≤ 3 * (1 - u) ^ (-(57 / 100 : ℝ)) := by
  let x := 1 - u
  have hx : 0 < x := sub_pos.mpr hu.2
  have hx1 : x ≤ 1 := by dsimp [x]; linarith [hu.1]
  have hp := Real.rpow_pos_of_pos hx (1 / 2 : ℝ)
  have hl := (Real.abs_log_mul_self_rpow_lt x (1 / 2) hx hx1 (by norm_num)).le
  rw [abs_mul, abs_of_pos hp] at hl
  norm_num only [one_div, inv_div, div_one] at hl
  have hlog : |Real.log x| ≤ 2 * x ^ (-(1 / 2 : ℝ)) := by
    apply (mul_le_mul_iff_left₀ hp).mp
    have he : x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hx]; norm_num
    nlinarith [he]
  have hpow : x ^ (-(7 / 100 : ℝ)) * x ^ (-(1 / 2 : ℝ)) =
      x ^ (-(57 / 100 : ℝ)) := by
    rw [← Real.rpow_add hx]; congr 1; norm_num
  have hle : x ^ (-(7 / 100 : ℝ)) ≤ x ^ (-(57 / 100 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hlog
    (Real.rpow_pos_of_pos hx (-(7 / 100 : ℝ))).le
  change x ^ (-(7 / 100 : ℝ)) * (1 + |Real.log x|) ≤ _
  dsimp [x] at hpow hle hm ⊢
  nlinarith [hpow]

theorem integrable_endpointEnvelope : Integrable endpointEnvelope unitIntervalVolume := by
  apply ((integrable_endpoint_power (r := -(57 / 100 : ℝ))
    (by norm_num)).const_mul 3).mono'
  · unfold endpointEnvelope
    exact (by fun_prop : Measurable (fun u : ℝ =>
      (1 - u) ^ (-(7 / 100 : ℝ)) * (1 + |Real.log (1 - u)|))).aestronglyMeasurable
  · filter_upwards [unitIntervalVolume_ae_mem] with u hu
    simpa [Real.norm_eq_abs, abs_of_nonneg (endpointEnvelope_nonneg hu)] using
      endpointEnvelope_le hu

lemma analyticWeight_le_endpoint_power {K : ℝ → ℝ → ℝ} {a u : ℝ}
    (ha : a ∈ Icc (2 / 3 : ℝ) (69 / 100)) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hK : 1 ≤ K a u) :
    analyticWeight K a u ≤ (1 - u) ^ (-(7 / 100 : ℝ)) := by
  have hs := s_range ha.1 ha.2
  have huweight : u ^ (1 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one hu.1.le hu.2.le (by norm_num)
  have hKweight : K a u ^ (-(3 * a - 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hK (neg_nonpos.mpr hs.1)
  have hendpoint : (1 - u) ^ (-(3 * a - 2)) ≤
      (1 - u) ^ (-(7 / 100 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge (sub_pos.mpr hu.2)
      (by linarith [hu.1]) (neg_le_neg hs.2)
  unfold analyticWeight
  calc
    _ ≤ 1 * (1 - u) ^ (-(3 * a - 2)) * 1 := by
      have hepos := (Real.rpow_pos_of_pos (sub_pos.mpr hu.2) (-(3 * a - 2))).le
      exact mul_le_mul (mul_le_mul_of_nonneg_right huweight hepos)
        hKweight (Real.rpow_nonneg (by linarith : 0 ≤ K a u) _) (by simpa using hepos)
    _ ≤ _ := by simpa using hendpoint

theorem integrable_analyticWeight {K : ℝ → ℝ → ℝ} {a : ℝ}
    (ha : a ∈ Icc (2 / 3 : ℝ) (69 / 100)) (hm : Measurable (K a))
    (hK : ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K a u) :
    Integrable (analyticWeight K a) unitIntervalVolume := by
  apply (integrable_endpoint_power (r := -(7 / 100 : ℝ)) (by norm_num)).mono'
    (measurable_analyticWeight hm).aestronglyMeasurable
  filter_upwards [unitIntervalVolume_ae_mem] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (analyticWeight_pos hu (lt_of_lt_of_le zero_lt_one (hK u hu)))]
  exact analyticWeight_le_endpoint_power ha hu (hK u hu)

/-- For a single physical parameter there is no short-band restriction.
The constant in this bound is finite even when `3*a-2` is negative. -/
lemma analyticWeight_le_endpoint_power_of_bounds {K : ℝ → ℝ → ℝ} {a u B : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hK : 1 ≤ K a u) (hKB : K a u ≤ B) :
    analyticWeight K a u ≤ max 1 (B ^ (-(3 * a - 2))) * (1 - u) ^ (-(3 * a - 2)) := by
  have hconst : K a u ^ (-(3 * a - 2)) ≤ max 1 (B ^ (-(3 * a - 2))) := by
    by_cases hs : 0 ≤ 3 * a - 2
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hK (neg_nonpos.mpr hs)).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow (by linarith : 0 ≤ K a u) hKB
        (by linarith : 0 ≤ -(3 * a - 2))).trans (le_max_right _ _)
  have hp := (Real.rpow_pos_of_pos (sub_pos.mpr hu.2) (-(3 * a - 2))).le
  have huweight : u ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hu.1.le hu.2.le (by norm_num)
  unfold analyticWeight
  calc
    _ ≤ (1 * (1 - u) ^ (-(3 * a - 2))) * max 1 (B ^ (-(3 * a - 2))) :=
      mul_le_mul (mul_le_mul_of_nonneg_right huweight hp) hconst
        (Real.rpow_nonneg (by linarith : 0 ≤ K a u) _) (by simpa using hp)
    _ = _ := by ring

theorem integrable_analyticWeight_of_lt_one {K : ℝ → ℝ → ℝ} {a B : ℝ}
    (ha : a < 1) (hm : Measurable (K a))
    (hK : ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K a u)
    (hKB : ∀ u ∈ Ioo (0 : ℝ) 1, K a u ≤ B) :
    Integrable (analyticWeight K a) unitIntervalVolume := by
  apply ((integrable_endpoint_power (r := -(3 * a - 2))
    (by linarith)).const_mul (max 1 (B ^ (-(3 * a - 2))))).mono'
    (measurable_analyticWeight hm).aestronglyMeasurable
  filter_upwards [unitIntervalVolume_ae_mem] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (analyticWeight_pos hu (lt_of_lt_of_le zero_lt_one (hK u hu)))]
  exact analyticWeight_le_endpoint_power_of_bounds hu (hK u hu) (hKB u hu)

theorem integrable_analyticWeight_physical {K : ℝ → ℝ → ℝ} {a B : ℝ}
    (ha : a ∈ Ioo (1 / 2 : ℝ) 1) (hm : Measurable (K a))
    (hK : ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K a u)
    (hKB : ∀ u ∈ Ioo (0 : ℝ) 1, K a u ≤ B) :
    Integrable (analyticWeight K a) unitIntervalVolume :=
  integrable_analyticWeight_of_lt_one ha.2 hm hK hKB

/-- A bounded positive `K` and bounded `∂a K` give the logarithmic score bound. -/
lemma logWeightScore_abs_le {K Ka : ℝ → ℝ} {s u B C : ℝ}
    (_hu : u ∈ Ioo (0 : ℝ) 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hK : 1 ≤ K u) (hKB : K u ≤ B) (hKa : |Ka u| ≤ C) :
    |logWeightScore K Ka s u| ≤ (3 + 3 * B + C) * (1 + |Real.log (1 - u)|) := by
  have hkpos : 0 < K u := lt_of_lt_of_le zero_lt_one hK
  have hB : 1 ≤ B := hK.trans hKB
  have hC : 0 ≤ C := (abs_nonneg _).trans hKa
  have hlog : |Real.log (K u)| ≤ B := by
    rw [abs_of_nonneg (Real.log_nonneg hK)]
    exact (Real.log_le_sub_one_of_pos hkpos).trans (by linarith)
  have hquot : |Ka u / K u| ≤ C := by
    rw [abs_div, abs_of_pos hkpos]
    apply (div_le_iff₀ hkpos).2
    nlinarith
  have hmul : |s * (Ka u / K u)| ≤ C := by
    rw [abs_mul, abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left hquot hs).trans (by nlinarith)
  unfold logWeightScore
  calc
    _ ≤ |(-3 : ℝ) * Real.log (1 - u)| + |3 * Real.log (K u)| +
        |s * (Ka u / K u)| := (abs_sub _ _).trans
          (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 3 * |Real.log (1 - u)| + 3 * B + C := by
      have ht : |(-3 : ℝ) * Real.log (1 - u)| = 3 * |Real.log (1 - u)| := by
        rw [abs_mul]; norm_num
      have hk : |3 * Real.log (K u)| = 3 * |Real.log (K u)| := by
        rw [abs_mul]; norm_num
      rw [ht, hk]
      linarith
    _ ≤ _ := by nlinarith [abs_nonneg (Real.log (1 - u))]

lemma analyticWeight_score_bound {K Ka : ℝ → ℝ → ℝ} {a u B C : ℝ}
    (ha : a ∈ Icc (2 / 3 : ℝ) (69 / 100)) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hK : 1 ≤ K a u) (hKB : K a u ≤ B) (hKa : |Ka a u| ≤ C) :
    ‖analyticWeight K a u * logWeightScore (K a) (Ka a) (3 * a - 2) u‖ ≤
      (3 + 3 * B + C) * endpointEnvelope u := by
  have hs := s_range ha.1 ha.2
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (analyticWeight_pos hu (lt_of_lt_of_le zero_lt_one hK))]
  calc
    _ ≤ (1 - u) ^ (-(7 / 100 : ℝ)) *
        ((3 + 3 * B + C) * (1 + |Real.log (1 - u)|)) :=
      mul_le_mul (analyticWeight_le_endpoint_power ha hu hK)
        (logWeightScore_abs_le hu hs.1 (by linarith [hs.2]) hK hKB hKa)
        (abs_nonneg _) (Real.rpow_pos_of_pos (sub_pos.mpr hu.2) _).le
    _ = _ := by unfold endpointEnvelope; ring

theorem analyticProbability_isProbability {K : ℝ → ℝ → ℝ} {a : ℝ}
    (ha : a ∈ Icc (2 / 3 : ℝ) (69 / 100)) (hm : Measurable (K a))
    (hK : ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K a u) :
    IsProbabilityMeasure (analyticProbability K a) :=
  weightedIntervalProbability_isProbability (integrable_analyticWeight ha hm hK)
    (fun u hu => analyticWeight_pos hu (lt_of_lt_of_le zero_lt_one (hK u hu)))

theorem analyticProbability_full {K : ℝ → ℝ → ℝ} {a : ℝ}
    (ha : a ∈ Icc (2 / 3 : ℝ) (69 / 100)) (hm : Measurable (K a))
    (hK : ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K a u) :
    FullIntervalSupport (analyticProbability K a) :=
  weightedIntervalProbability_full (measurable_analyticWeight hm)
    (integrable_analyticWeight ha hm hK)
    (fun u hu => analyticWeight_pos hu (lt_of_lt_of_le zero_lt_one (hK u hu)))

/-- The existing scalar mixed-derivative bound supplies strict increase of the
actual score once the spatial derivatives of `K` and `Ka` are supplied. -/
theorem strictMonoOn_logWeightScore_of_bounds
    {K Ka Ku Kau : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 7 / 100)
    (hK : ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K u)
    (hdK : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivAt K (Ku u) u)
    (hdKa : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivAt Ka (Kau u) u)
    (hKu : ∀ u ∈ Ioo (0 : ℝ) 1, 0 ≤ Ku u)
    (hKu' : ∀ u ∈ Ioo (0 : ℝ) 1, Ku u ≤ 21 / 32)
    (hKa : ∀ u ∈ Ioo (0 : ℝ) 1, 0 ≤ Ka u)
    (hKau : ∀ u ∈ Ioo (0 : ℝ) 1, Kau u ≤ 45 / 4) :
    StrictMonoOn (logWeightScore K Ka s) (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro u hu
    exact (hasDerivAt_logWeightScore (s := s) (hdK u hu) (hdKa u hu) hu.2 (hK u hu)).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : u ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ioo] using hu
    have h := deriv_logWeightScore_lower_bound (hdK u hu') (hdKa u hu')
      hu'.1 hu'.2 hs hs' (hK u hu') (hKu u hu') (hKu' u hu') (hKa u hu') (hKau u hu')
    linarith

end Kagey131.PaperD.Modes.AnalyticThreshold
