import PaperD.EJPAnalyticThresholdOrder
import PaperD.EJPAnalyticThresholdBounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Normalizing the rescaled analytic-threshold weight

The normalizer and all expectations are real Bochner integrals against
Lebesgue measure restricted to `(0,1)`. No covariance or order conclusion
is included in the hypotheses of the measure construction.
-/

namespace Kagey131.PaperD.Modes.AnalyticThreshold

open MeasureTheory Set Filter
open scoped Topology

noncomputable def unitIntervalVolume : Measure ℝ := volume.restrict (Ioo 0 1)

lemma unitIntervalVolume_ae_mem : ∀ᵐ u ∂unitIntervalVolume, u ∈ Ioo (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Ioo

lemma unitIntervalVolume_full : FullIntervalSupport unitIntervalVolume := by
  intro x y hx hxy hy
  have hsub : Ioo x y ⊆ Ioo (0 : ℝ) 1 := fun _ hu =>
    ⟨hx.trans_lt hu.1, hu.2.trans_le hy⟩
  change 0 < volume.restrict (Ioo (0 : ℝ) 1) (Ioo x y)
  rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr hsub,
    Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)

noncomputable def weightNormalizer (w : ℝ → ℝ) : ℝ :=
  ∫ u, w u ∂unitIntervalVolume

noncomputable def weightedIntervalProbability (w : ℝ → ℝ) : Measure ℝ :=
  unitIntervalVolume.withDensity (fun u => ENNReal.ofReal (w u / weightNormalizer w))

theorem weightNormalizer_pos {w : ℝ → ℝ}
    (hi : Integrable w unitIntervalVolume)
    (hp : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < w u) : 0 < weightNormalizer w := by
  apply (integral_pos_iff_support_of_nonneg_ae
    (unitIntervalVolume_ae_mem.mono fun u hu => (hp u hu).le) hi).2
  apply lt_of_lt_of_le
    (unitIntervalVolume_full 0 1 le_rfl (by norm_num) le_rfl) (measure_mono ?_)
  exact fun u hu => (hp u hu).ne'

theorem weightedIntervalProbability_isProbability {w : ℝ → ℝ}
    (hi : Integrable w unitIntervalVolume)
    (hp : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < w u) :
    IsProbabilityMeasure (weightedIntervalProbability w) := by
  have hz := weightNormalizer_pos hi hp
  constructor
  rw [weightedIntervalProbability, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)]
  · rw [integral_div]
    change ENNReal.ofReal (weightNormalizer w / weightNormalizer w) = 1
    simp [hz.ne']
  · exact unitIntervalVolume_ae_mem.mono fun u hu => (div_pos (hp u hu) hz).le

theorem weightedIntervalProbability_ae_mem (w : ℝ → ℝ) :
    ∀ᵐ u ∂weightedIntervalProbability w, u ∈ Ioo (0 : ℝ) 1 :=
  (withDensity_absolutelyContinuous _ _).ae_le unitIntervalVolume_ae_mem

theorem weightedIntervalProbability_full {w : ℝ → ℝ}
    (hm : Measurable w) (hi : Integrable w unitIntervalVolume)
    (hp : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < w u) :
    FullIntervalSupport (weightedIntervalProbability w) := by
  have hz := weightNormalizer_pos hi hp
  have hac : unitIntervalVolume ≪ weightedIntervalProbability w :=
    withDensity_absolutelyContinuous' (hm.div_const _).ennreal_ofReal.aemeasurable
      (unitIntervalVolume_ae_mem.mono fun u hu =>
        (ENNReal.ofReal_pos.mpr (div_pos (hp u hu) hz)).ne')
  intro x y hx hxy hy
  exact pos_iff_ne_zero.mpr fun h =>
    (unitIntervalVolume_full x y hx hxy hy).ne' (hac h)

/-- Conversion of an actual normalized expectation into its Lebesgue integral.
This equality holds even when the observable is not integrable. -/
theorem integral_weightedIntervalProbability {w f : ℝ → ℝ}
    (hm : Measurable w) (hi : Integrable w unitIntervalVolume)
    (hp : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < w u) :
    (∫ u, f u ∂weightedIntervalProbability w) =
      (∫ u, w u * f u ∂unitIntervalVolume) / weightNormalizer w := by
  have hz := weightNormalizer_pos hi hp
  rw [weightedIntervalProbability,
    integral_withDensity_eq_integral_toReal_smul (hm.div_const _).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ u, (w u * f u) / weightNormalizer w ∂unitIntervalVolume := by
      apply integral_congr_ae
      filter_upwards [unitIntervalVolume_ae_mem] with u hu
      rw [ENNReal.toReal_ofReal (div_pos (hp u hu) hz).le, smul_eq_mul]
      ring
    _ = _ := integral_div _ _

theorem integrable_weightedIntervalProbability_iff {w f : ℝ → ℝ}
    (hm : Measurable w) (hi : Integrable w unitIntervalVolume)
    (hp : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < w u) :
    Integrable f (weightedIntervalProbability w) ↔
      Integrable (fun u => w u * f u) unitIntervalVolume := by
  have hz := weightNormalizer_pos hi hp
  rw [weightedIntervalProbability,
    integrable_withDensity_iff_integrable_smul' (hm.div_const _).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have he : (fun u => (ENNReal.ofReal (w u / weightNormalizer w)).toReal • f u)
      =ᵐ[unitIntervalVolume] (fun u => (weightNormalizer w)⁻¹ * (w u * f u)) := by
    filter_upwards [unitIntervalVolume_ae_mem] with u hu
    rw [ENNReal.toReal_ofReal (div_pos (hp u hu) hz).le, smul_eq_mul]
    ring
  rw [integrable_congr he]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (inv_ne_zero hz.ne')) _

/-- The manuscript's actual rescaled density. The endpoints are irrelevant. -/
noncomputable def analyticWeight (K : ℝ → ℝ → ℝ) (a u : ℝ) : ℝ :=
  u ^ (1 / 2 : ℝ) * (1 - u) ^ (-(3 * a - 2)) * K a u ^ (-(3 * a - 2))

lemma analyticWeight_pos {K : ℝ → ℝ → ℝ} {a u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hK : 0 < K a u) :
    0 < analyticWeight K a u :=
  mul_pos (mul_pos (Real.rpow_pos_of_pos hu.1 _)
    (Real.rpow_pos_of_pos (sub_pos.mpr hu.2) _)) (Real.rpow_pos_of_pos hK _)

lemma measurable_analyticWeight {K : ℝ → ℝ → ℝ} {a : ℝ}
    (hK : Measurable (K a)) : Measurable (analyticWeight K a) := by
  unfold analyticWeight
  fun_prop

noncomputable def analyticProbability (K : ℝ → ℝ → ℝ) (a : ℝ) : Measure ℝ :=
  weightedIntervalProbability (analyticWeight K a)

/-- The coordinate expectation of the constructed probability measure. -/
noncomputable def analyticMean (K : ℝ → ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ u, u ∂analyticProbability K a

theorem analyticMean_eq_integral_ratio {K : ℝ → ℝ → ℝ} {a : ℝ}
    (hm : Measurable (K a)) (hi : Integrable (analyticWeight K a) unitIntervalVolume)
    (hp : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < K a u) :
    analyticMean K a = (∫ u, u * analyticWeight K a u ∂unitIntervalVolume) /
      weightNormalizer (analyticWeight K a) := by
  rw [analyticMean, analyticProbability,
    integral_weightedIntervalProbability (measurable_analyticWeight hm) hi
      (fun u hu => analyticWeight_pos hu (hp u hu))]
  simp only [mul_comm]

noncomputable def relativeAnalyticWeight (K : ℝ → ℝ → ℝ) (a b u : ℝ) : ℝ :=
  analyticWeight K b u / analyticWeight K a u

noncomputable def relativeAnalyticWeightDeriv
    (K Ka : ℝ → ℝ → ℝ) (a b u : ℝ) : ℝ :=
  analyticWeight K b u * logWeightScore (K b) (Ka b) (3 * b - 2) u /
    analyticWeight K a u

lemma relativeAnalyticWeight_base {K : ℝ → ℝ → ℝ} {a : ℝ}
    (hp : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < K a u) :
    ∀ᵐ u ∂analyticProbability K a, relativeAnalyticWeight K a a u = 1 := by
  filter_upwards [weightedIntervalProbability_ae_mem (analyticWeight K a)] with u hu
  exact div_self (analyticWeight_pos hu (hp u hu)).ne'

/-- Relative weighting cancels the base density inside the actual integrals. -/
theorem normalizedMean_relativeAnalyticWeight {K : ℝ → ℝ → ℝ} {a : ℝ}
    (hm : Measurable (K a)) (hi : Integrable (analyticWeight K a) unitIntervalVolume)
    (hp : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < K a u) (b : ℝ) :
    normalizedMean (analyticProbability K a) (relativeAnalyticWeight K a) b =
      (∫ u, u * analyticWeight K b u ∂unitIntervalVolume) /
        weightNormalizer (analyticWeight K b) := by
  have hpos := fun u hu => analyticWeight_pos hu (hp u hu)
  have hc (f : ℝ → ℝ) :
      (∫ u, f u * relativeAnalyticWeight K a b u ∂analyticProbability K a) =
        (∫ u, f u * analyticWeight K b u ∂unitIntervalVolume) /
          weightNormalizer (analyticWeight K a) := by
    rw [analyticProbability, integral_weightedIntervalProbability
      (measurable_analyticWeight hm) hi hpos]
    congr 1
    apply integral_congr_ae
    filter_upwards [unitIntervalVolume_ae_mem] with u hu
    dsimp [relativeAnalyticWeight]
    field_simp [(hpos u hu).ne']
  unfold normalizedMean
  rw [hc (fun u => u)]
  have hden := hc (fun _ => 1)
  simp only [one_mul] at hden
  rw [hden]
  dsimp [weightNormalizer]
  exact div_div_div_cancel_right₀ (weightNormalizer_pos hi hpos).ne' _ _

end Kagey131.PaperD.Modes.AnalyticThreshold
