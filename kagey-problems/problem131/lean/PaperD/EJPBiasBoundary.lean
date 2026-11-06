import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Compact localization for the bias boundary

Quasiconcavity and two strict endpoint comparisons localize the maximum of a
ratio to a closed subinterval. Two such ratios can be compared on a shared
subinterval even when their domains have different right endpoints.
-/

namespace Kagey131.PaperD.Modes

open Set

/-- Quasiconcavity on `(0, k)` is the minimum inequality for ordered triples. -/
theorem ejp_bias_ratio_quasiconcave_iff {R : ℝ → ℝ} {k : ℝ} :
    QuasiconcaveOn ℝ (Ioo 0 k) R ↔
      ∀ ⦃x y z : ℝ⦄, 0 < x → x < y → y < z → z < k → min (R x) (R z) ≤ R y := by
  constructor
  · intro h x y z hx hxy hyz hz
    let s := {w ∈ Ioo 0 k | min (R x) (R z) ≤ R w}
    have hxs : x ∈ s := ⟨⟨hx, hxy.trans (hyz.trans hz)⟩, min_le_left _ _⟩
    have hzs : z ∈ s := ⟨⟨hx.trans (hxy.trans hyz), hz⟩, min_le_right _ _⟩
    have hys : y ∈ s := (h (min (R x) (R z))).ordConnected.out hxs hzs ⟨hxy.le, hyz.le⟩
    exact hys.2
  · intro h c
    apply convex_iff_ordConnected.mpr
    apply ordConnected_of_Ioo
    intro x hx z hz _ y hy
    exact ⟨⟨hx.1.1.trans hy.1, hy.2.trans hz.1.2⟩,
      (le_min hx.2 hz.2).trans (h hx.1.1 hy.1 hy.2 hz.1.2)⟩

/-- The left and right tails are bounded by their respective endpoint values. -/
theorem ejp_bias_ratio_tail_bounds {R : ℝ → ℝ} {k l t r : ℝ}
    (hqc : QuasiconcaveOn ℝ (Ioo 0 k) R) (hl : 0 < l) (ht : t ∈ Ioo l r)
    (hr : r < k) (hlt : R l < R t) (hrt : R r < R t) :
    (∀ x ∈ Ioc 0 l, R x ≤ R l) ∧ (∀ x ∈ Ico r k, R x ≤ R r) ∧
      max (R l) (R r) < R t := by
  have htriple := ejp_bias_ratio_quasiconcave_iff.mp hqc
  refine ⟨?_, ?_, max_lt_iff.mpr ⟨hlt, hrt⟩⟩
  · intro x hx
    rcases hx.2.eq_or_lt with rfl | hxl
    · exact le_rfl
    by_contra! h
    exact (not_lt_of_ge (htriple hx.1 hxl ht.1 (ht.2.trans hr))) (lt_min h hlt)
  · intro x hx
    rcases hx.1.eq_or_lt with rfl | hrx
    · exact le_rfl
    by_contra! h
    exact (not_lt_of_ge (htriple (hl.trans ht.1) ht.2 hrx hx.2)) (lt_min hrt h)

/-- A maximizer on `[l, r]` also maximizes the ratio on `(0, k)`. -/
theorem ejp_bias_ratio_isMaxOn {R : ℝ → ℝ} {k l t r m : ℝ}
    (hqc : QuasiconcaveOn ℝ (Ioo 0 k) R) (hl : 0 < l) (ht : t ∈ Ioo l r)
    (hr : r < k) (hlt : R l < R t) (hrt : R r < R t)
    (hmax : IsMaxOn R (Icc l r) m) : IsMaxOn R (Ioo 0 k) m := by
  obtain ⟨hleft, hright, _⟩ := ejp_bias_ratio_tail_bounds hqc hl ht hr hlt hrt
  have htm := hmax (show t ∈ Icc l r from ⟨ht.1.le, ht.2.le⟩)
  intro x hx
  by_cases hxl : x < l
  · exact (hleft x ⟨hx.1, hxl.le⟩).trans (hlt.le.trans htm)
  by_cases hrx : r < x
  · exact (hright x ⟨hrx.le, hx.2⟩).trans (hrt.le.trans htm)
  exact hmax (show x ∈ Icc l r from ⟨le_of_not_gt hxl, le_of_not_gt hrx⟩)

/-- A uniform error on the shared localization interval bounds the difference
of the global maximum values by the same error. -/
theorem ejp_bias_ratio_max_stability {R S : ℝ → ℝ} {kR kS l tR tS r E : ℝ}
    (hqcR : QuasiconcaveOn ℝ (Ioo 0 kR) R) (hqcS : QuasiconcaveOn ℝ (Ioo 0 kS) S)
    (hl : 0 < l) (htR : tR ∈ Ioo l r) (htS : tS ∈ Ioo l r) (hrR : r < kR) (hrS : r < kS)
    (hlR : R l < R tR) (hrR' : R r < R tR) (hlS : S l < S tS) (hrS' : S r < S tS)
    (hcontR : ContinuousOn R (Icc l r)) (hcontS : ContinuousOn S (Icc l r))
    (hclose : ∀ x ∈ Icc l r, |R x - S x| ≤ E) :
    ∃ mR ∈ Icc l r, ∃ mS ∈ Icc l r,
      IsMaxOn R (Ioo 0 kR) mR ∧ IsMaxOn S (Ioo 0 kS) mS ∧ |R mR - S mS| ≤ E := by
  have hne : (Icc l r).Nonempty := ⟨tR, htR.1.le, htR.2.le⟩
  obtain ⟨mR, hmR, hmaxR⟩ := isCompact_Icc.exists_isMaxOn hne hcontR
  obtain ⟨mS, hmS, hmaxS⟩ := isCompact_Icc.exists_isMaxOn hne hcontS
  refine ⟨mR, hmR, mS, hmS, ejp_bias_ratio_isMaxOn hqcR hl htR hrR hlR hrR' hmaxR,
    ejp_bias_ratio_isMaxOn hqcS hl htS hrS hlS hrS' hmaxS, abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩
  · calc
      R mR - S mS ≤ R mR - S mR := sub_le_sub_left (hmaxS hmR) _
      _ ≤ E := (abs_sub_le_iff.mp (hclose mR hmR)).1
  · calc
      S mS - R mR ≤ S mS - R mS := sub_le_sub_left (hmaxR hmS) _
      _ ≤ E := (abs_sub_le_iff.mp (hclose mS hmS)).2

end Kagey131.PaperD.Modes
