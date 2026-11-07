import PaperD.EJPAnalyticThresholdMeasureBounds

/-!
# Closed-band continuity of the actual normalized mean

Dominated convergence applies on the closed band, including its endpoints.
Only parameter continuity and `K ≥ 1` are needed for the common weight bound.
No derivative or continuity predicate for the final ratio is assumed.
-/

namespace Kagey131.PaperD.Modes.AnalyticThreshold

open MeasureTheory Set Filter
open scoped Topology

lemma analyticWeight_le_endpointEnvelope {K : ℝ → ℝ → ℝ} {a u : ℝ}
    (ha : a ∈ Icc (2 / 3 : ℝ) (69 / 100)) (hu : u ∈ Ioo (0 : ℝ) 1) (hK : 1 ≤ K a u) :
    analyticWeight K a u ≤ endpointEnvelope u := by
  apply (analyticWeight_le_endpoint_power ha hu hK).trans
  unfold endpointEnvelope
  have hp := (Real.rpow_pos_of_pos (sub_pos.mpr hu.2) (-(7 / 100 : ℝ))).le
  nlinarith [abs_nonneg (Real.log (1 - u))]

lemma continuousOn_analyticWeight_parameter {K : ℝ → ℝ → ℝ} {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1)
    (hK : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), 1 ≤ K b u)
    (hc : ContinuousOn (fun b => K b u) (Icc (2 / 3 : ℝ) (69 / 100))) :
    ContinuousOn (fun b => analyticWeight K b u) (Icc (2 / 3 : ℝ) (69 / 100)) := by
  have hs : ContinuousOn (fun b : ℝ => -(3 * b - 2)) (Icc (2 / 3 : ℝ) (69 / 100)) := by
    fun_prop
  have hx := (continuousOn_const : ContinuousOn (fun _ : ℝ => 1 - u)
    (Icc (2 / 3 : ℝ) (69 / 100))).rpow hs (fun _ _ => Or.inl (sub_pos.mpr hu.2).ne')
  have hk := hc.rpow hs (fun b hb => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (hK b hb))))
  exact (continuousOn_const.mul hx).mul hk

theorem analyticWeight_integrals_continuousOn {K : ℝ → ℝ → ℝ}
    (hm : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), Measurable (K b))
    (hK : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K b u)
    (hc : ∀ u ∈ Ioo (0 : ℝ) 1,
      ContinuousOn (fun b => K b u) (Icc (2 / 3 : ℝ) (69 / 100))) :
    ContinuousOn (fun b => weightNormalizer (analyticWeight K b)) (Icc (2 / 3 : ℝ) (69 / 100)) ∧
    ContinuousOn (fun b => ∫ u, u * analyticWeight K b u ∂unitIntervalVolume)
      (Icc (2 / 3 : ℝ) (69 / 100)) := by
  have hbound : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100),
      ∀ᵐ u ∂unitIntervalVolume, ‖analyticWeight K b u‖ ≤ endpointEnvelope u := by
    intro b hb
    filter_upwards [unitIntervalVolume_ae_mem] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (analyticWeight_pos hu
      (lt_of_lt_of_le zero_lt_one (hK b hb u hu)))]
    exact analyticWeight_le_endpointEnvelope hb hu (hK b hb u hu)
  have hcont : ∀ᵐ u ∂unitIntervalVolume,
      ContinuousOn (fun b => analyticWeight K b u) (Icc (2 / 3 : ℝ) (69 / 100)) := by
    filter_upwards [unitIntervalVolume_ae_mem] with u hu
    exact continuousOn_analyticWeight_parameter hu (fun b hb => hK b hb u hu) (hc u hu)
  refine ⟨continuousOn_of_dominated
    (fun b hb => (measurable_analyticWeight (hm b hb)).aestronglyMeasurable)
    hbound integrable_endpointEnvelope hcont, ?_⟩
  apply continuousOn_of_dominated (bound := endpointEnvelope)
    (fun b hb => (measurable_id.mul (measurable_analyticWeight (hm b hb))).aestronglyMeasurable)
    _ integrable_endpointEnvelope _
  · intro b hb
    filter_upwards [unitIntervalVolume_ae_mem, hbound b hb] with u hu hbu
    calc
      ‖u * analyticWeight K b u‖ = ‖u‖ * ‖analyticWeight K b u‖ := norm_mul _ _
      _ ≤ 1 * ‖analyticWeight K b u‖ := mul_le_mul_of_nonneg_right
        (by simpa [Real.norm_eq_abs, abs_of_pos hu.1] using hu.2.le) (norm_nonneg _)
      _ ≤ endpointEnvelope u := by simpa using hbu
  · exact hcont.mono fun u hu => continuousOn_const.mul hu

theorem continuousOn_analyticMean {K : ℝ → ℝ → ℝ}
    (hm : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), Measurable (K b))
    (hK : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K b u)
    (hc : ∀ u ∈ Ioo (0 : ℝ) 1,
      ContinuousOn (fun b => K b u) (Icc (2 / 3 : ℝ) (69 / 100))) :
    ContinuousOn (analyticMean K) (Icc (2 / 3 : ℝ) (69 / 100)) := by
  obtain ⟨hZ, hN⟩ := analyticWeight_integrals_continuousOn hm hK hc
  have hpos : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), 0 < weightNormalizer (analyticWeight K b) :=
    fun b hb => weightNormalizer_pos (integrable_analyticWeight hb (hm b hb) (hK b hb))
      (fun u hu => analyticWeight_pos hu (lt_of_lt_of_le zero_lt_one (hK b hb u hu)))
  apply (hN.div hZ (fun b hb => (hpos b hb).ne')).congr
  intro b hb
  exact analyticMean_eq_integral_ratio (hm b hb) (integrable_analyticWeight hb (hm b hb) (hK b hb))
    (fun u hu => lt_of_lt_of_le zero_lt_one (hK b hb u hu))

theorem continuousOn_actualTransitionRatio {K : ℝ → ℝ → ℝ} {Y : ℝ → ℝ}
    (hm : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), Measurable (K b))
    (hK : ∀ b ∈ Icc (2 / 3 : ℝ) (69 / 100), ∀ u ∈ Ioo (0 : ℝ) 1, 1 ≤ K b u)
    (hc : ∀ u ∈ Ioo (0 : ℝ) 1,
      ContinuousOn (fun b => K b u) (Icc (2 / 3 : ℝ) (69 / 100)))
    (hY : ContinuousOn Y (Icc (2 / 3 : ℝ) (69 / 100))) :
    ContinuousOn (fun b => (1 + b) ^ 2 * Y b * analyticMean K b)
      (Icc (2 / 3 : ℝ) (69 / 100)) :=
  (((continuousOn_const.add continuousOn_id).pow 2).mul hY).mul
    (continuousOn_analyticMean hm hK hc)

end Kagey131.PaperD.Modes.AnalyticThreshold
