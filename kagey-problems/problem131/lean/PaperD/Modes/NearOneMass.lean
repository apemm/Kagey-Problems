import PaperD.Modes.NearOneMode
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Interval masses locate unimodal densities

The convergence input is convergence of masses of fixed bounded intervals.
The approximating densities need not be continuous, which permits a folded
profile with a moving cutoff.
-/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology

theorem interval_mass_le_const {f : ℝ → ℝ} {a b C : ℝ}
    (hf : IntervalIntegrable f volume a b) (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, f x ≤ C) : (∫ x in a..b, f x) ≤ (b-a)*C := by
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using
    intervalIntegral.integral_mono_on hab hf intervalIntegrable_const h

theorem const_le_interval_mass {f : ℝ → ℝ} {a b C : ℝ}
    (hf : IntervalIntegrable f volume a b) (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, C ≤ f x) : (b-a)*C ≤ ∫ x in a..b, f x := by
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using
    intervalIntegral.integral_mono_on hab intervalIntegrable_const hf h

theorem adjacent_mass_le_of_antitone {f : ℝ → ℝ} {a h : ℝ}
    (hf : Integrable f) (hh : 0 < h) (ha : AntitoneOn f (Icc a (a+2*h))) :
    (∫ x in (a+h)..(a+2*h), f x) ≤ ∫ x in a..(a+h), f x := by
  have hleft : h*f (a+h) ≤ ∫ x in a..(a+h), f x := by
    have hc := const_le_interval_mass hf.intervalIntegrable (show a ≤ a+h by linarith)
      (fun x hx => ha ⟨hx.1, by linarith [hx.2]⟩ ⟨by linarith, by linarith⟩ hx.2)
    simpa only [add_sub_cancel_left] using hc
  have hright : (∫ x in (a+h)..(a+2*h), f x) ≤ h*f (a+h) := by
    have hc := interval_mass_le_const hf.intervalIntegrable (show a+h ≤ a+2*h by linarith)
      (fun x hx => ha ⟨by linarith, by linarith⟩ ⟨by linarith [hx.1], hx.2⟩ hx.1)
    convert hc using 1 <;> ring
  exact hright.trans hleft

theorem adjacent_mass_le_of_monotone {f : ℝ → ℝ} {a h : ℝ}
    (hf : Integrable f) (hh : 0 < h) (ha : MonotoneOn f (Icc a (a+2*h))) :
    (∫ x in a..(a+h), f x) ≤ ∫ x in (a+h)..(a+2*h), f x := by
  have hleft : (∫ x in a..(a+h), f x) ≤ h*f (a+h) := by
    have hc := interval_mass_le_const hf.intervalIntegrable (show a ≤ a+h by linarith)
      (fun x hx => ha ⟨hx.1, by linarith [hx.2]⟩ ⟨by linarith, by linarith⟩ hx.2)
    simpa only [add_sub_cancel_left] using hc
  have hright : h*f (a+h) ≤ ∫ x in (a+h)..(a+2*h), f x := by
    have hc := const_le_interval_mass hf.intervalIntegrable (show a+h ≤ a+2*h by linarith)
      (fun x hx => ha ⟨by linarith, by linarith⟩ ⟨by linarith [hx.1], hx.2⟩ hx.1)
    convert hc using 1 <;> ring
  exact hleft.trans hright

theorem adjacent_mass_lt_of_strictMono {f : ℝ → ℝ} {a h : ℝ}
    (hf : Continuous f) (hh : 0 < h) (ha : StrictMonoOn f (Icc a (a+2*h))) :
    (∫ x in a..(a+h), f x) < ∫ x in (a+h)..(a+2*h), f x := by
  have hleft : (∫ x in a..(a+h), f x) < h*f (a+h) := by
    have hc := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (show a < a+h by linarith) hf.continuousOn continuousOn_const
      (fun x hx => ha.monotoneOn ⟨hx.1.le, by linarith [hx.2]⟩
        ⟨by linarith, by linarith⟩ hx.2)
      ⟨a, ⟨le_rfl, by linarith⟩,
        ha ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)⟩
    simpa only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] using hc
  have hright : h*f (a+h) ≤ ∫ x in (a+h)..(a+2*h), f x := by
    have hc := const_le_interval_mass (hf.intervalIntegrable _ _)
      (show a+h ≤ a+2*h by linarith)
      (fun x hx => ha.monotoneOn ⟨by linarith, by linarith⟩
        ⟨by linarith [hx.1], hx.2⟩ hx.1)
    convert hc using 1 <;> ring
  exact hleft.trans_le hright

theorem adjacent_mass_lt_of_strictAnti {f : ℝ → ℝ} {a h : ℝ}
    (hf : Continuous f) (hh : 0 < h) (ha : StrictAntiOn f (Icc a (a+2*h))) :
    (∫ x in (a+h)..(a+2*h), f x) < ∫ x in a..(a+h), f x := by
  have hn := adjacent_mass_lt_of_strictMono hf.neg hh ha.neg
  simpa only [Pi.neg_apply, intervalIntegral.integral_neg, neg_lt_neg_iff] using hn

/-- Mode localization follows from interval masses alone; no pointwise
convergence is used in this step. -/
theorem mode_tendsto_of_interval_masses_strict {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {c : ℕ → ℝ} {m : ℝ}
    (hF : ∀ n, Integrable (F n)) (hf : Continuous f)
    (hshape : ∀ n, UnimodalAt (F n) (c n))
    (hleft : StrictMonoOn f (Iic m)) (hright : StrictAntiOn f (Ici m))
    (hmass : ∀ a b, a < b → Tendsto (fun n => ∫ x in a..b, F n x)
      atTop (𝓝 (∫ x in a..b, f x))) : Tendsto c atTop (𝓝 m) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let h := (m-a)/3
    have hh : 0 < h := by dsimp [h]; linarith
    have hend : a+2*h < m := by dsimp [h]; linarith
    have hgap := adjacent_mass_lt_of_strictMono hf hh
      (hleft.mono (fun x hx => hx.2.trans hend.le))
    have hev := (hmass a (a+h) (by linarith)).eventually_lt
      (hmass (a+h) (a+2*h) (by linarith)) hgap
    filter_upwards [hev] with n hn
    by_contra hnc
    have hcn : c n ≤ a := le_of_not_gt hnc
    exact (not_lt_of_ge (adjacent_mass_le_of_antitone (hF n) hh
      ((hshape n).2.mono (fun x hx => hcn.trans hx.1)))) hn
  · intro b hb
    let h := (b-m)/3
    let a := b-2*h
    have hh : 0 < h := by dsimp [h]; linarith
    have hma : m < a := by dsimp [a,h]; linarith
    have hend : a+2*h = b := by dsimp [a]; ring
    have hgap := adjacent_mass_lt_of_strictAnti hf hh
      (hright.mono (fun x hx => hma.le.trans hx.1))
    have hev := (hmass (a+h) (a+2*h) (by linarith)).eventually_lt
      (hmass a (a+h) (by linarith)) hgap
    filter_upwards [hev] with n hn
    by_contra hnc
    have hbc : b ≤ c n := le_of_not_gt hnc
    exact (not_lt_of_ge (adjacent_mass_le_of_monotone (hF n) hh
      ((hshape n).1.mono (fun x hx => (hx.2.trans_eq hend).trans hbc)))) hn

theorem separated_mass_le_of_antitone {f : ℝ → ℝ} {x y h : ℝ}
    (hf : Integrable f) (hh : 0 < h) (hxy : x+h ≤ y)
    (ha : AntitoneOn f (Icc x (y+h))) :
    (∫ z in y..(y+h), f z) ≤ ∫ z in x..(x+h), f z := by
  have hleft : h*f (x+h) ≤ ∫ z in x..(x+h), f z := by
    have hc := const_le_interval_mass hf.intervalIntegrable (show x ≤ x+h by linarith)
      (fun z hz => ha ⟨hz.1, by linarith [hz.2]⟩ ⟨by linarith, by linarith⟩ hz.2)
    simpa only [add_sub_cancel_left] using hc
  have hright : (∫ z in y..(y+h), f z) ≤ h*f y := by
    have hc := interval_mass_le_const hf.intervalIntegrable (show y ≤ y+h by linarith)
      (fun z hz => ha ⟨by linarith, by linarith⟩ ⟨by linarith [hz.1], hz.2⟩ hz.1)
    simpa only [add_sub_cancel_left] using hc
  have hmid : f y ≤ f (x+h) := ha ⟨by linarith, by linarith⟩
    ⟨by linarith, by linarith⟩ hxy
  exact hright.trans ((mul_le_mul_of_nonneg_left hmid hh.le).trans hleft)

theorem separated_mass_le_of_monotone {f : ℝ → ℝ} {x y h : ℝ}
    (hf : Integrable f) (hh : 0 < h) (hxy : x+h ≤ y)
    (ha : MonotoneOn f (Icc x (y+h))) :
    (∫ z in x..(x+h), f z) ≤ ∫ z in y..(y+h), f z := by
  have hn := separated_mass_le_of_antitone hf.neg hh hxy ha.neg
  simpa only [Pi.neg_apply, intervalIntegral.integral_neg, neg_le_neg_iff] using hn

/-- A strict gap between two continuous density values supplies a strict
gap between masses of arbitrarily short intervals of the same length. -/
theorem exists_short_mass_gap {f : ℝ → ℝ} {x y r : ℝ}
    (hf : Continuous f) (hxy : f x < f y) (hr : 0 < r) :
    ∃ h, 0 < h ∧ h < r ∧
      (∫ z in x..(x+h), f z) < ∫ z in y..(y+h), f z := by
  let q₁ := (2*f x+f y)/3
  let q₂ := (f x+2*f y)/3
  have hxq : f x < q₁ := by dsimp [q₁]; linarith
  have hqy : q₂ < f y := by dsimp [q₂]; linarith
  have hqq : q₁ < q₂ := by dsimp [q₁,q₂]; linarith
  obtain ⟨δx, hδx, hnearx⟩ := Metric.eventually_nhds_iff.mp
    (hf.continuousAt.eventually (gt_mem_nhds hxq))
  obtain ⟨δy, hδy, hneary⟩ := Metric.eventually_nhds_iff.mp
    (hf.continuousAt.eventually (lt_mem_nhds hqy))
  let h := min r (min δx δy) / 2
  have hh : 0 < h := by dsimp [h]; positivity
  have hhr : h < r := by
    have := min_le_left r (min δx δy); dsimp [h]; linarith
  have hhx : h < δx := by
    have := (min_le_right r (min δx δy)).trans (min_le_left δx δy)
    dsimp [h]; linarith
  have hhy : h < δy := by
    have := (min_le_right r (min δx δy)).trans (min_le_right δx δy)
    dsimp [h]; linarith
  have hleft : (∫ z in x..(x+h), f z) ≤ h*q₁ := by
    have hc := interval_mass_le_const (hf.intervalIntegrable _ _)
      (show x ≤ x+h by linarith) (C := q₁) (fun z hz => (hnearx (by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hz.1)]
        linarith [hz.2])).le)
    simpa only [add_sub_cancel_left] using hc
  have hright : h*q₂ ≤ ∫ z in y..(y+h), f z := by
    have hc := const_le_interval_mass (hf.intervalIntegrable _ _)
      (show y ≤ y+h by linarith) (C := q₂) (fun z hz => (hneary (by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hz.1)]
        linarith [hz.2])).le)
    simpa only [add_sub_cancel_left] using hc
  exact ⟨h, hh, hhr, hleft.trans_lt ((mul_lt_mul_of_pos_left hqq hh).trans_le hright)⟩

/-- A continuous strict global mode, rather than strict monotonicity of the
limit on either side, suffices to localize every approximating mode. -/
theorem mode_tendsto_of_interval_masses {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {c : ℕ → ℝ} {m : ℝ}
    (hF : ∀ n, Integrable (F n)) (hf : Continuous f)
    (hshape : ∀ n, UnimodalAt (F n) (c n))
    (hmax : ∀ x, x ≠ m → f x < f m)
    (hmass : ∀ a b, a < b → Tendsto (fun n => ∫ x in a..b, F n x)
      atTop (𝓝 (∫ x in a..b, f x))) : Tendsto c atTop (𝓝 m) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let u := (a+m)/2
    have hau : a < u := by dsimp [u]; linarith
    have hum : u < m := by dsimp [u]; linarith
    obtain ⟨h, hh, hhu, hgap⟩ := exists_short_mass_gap hf (hmax u hum.ne)
      (sub_pos.mpr hum)
    have hev := (hmass u (u+h) (by linarith)).eventually_lt
      (hmass m (m+h) (by linarith)) hgap
    filter_upwards [hev] with n hn
    by_contra hnc
    have hcn : c n ≤ a := le_of_not_gt hnc
    exact (not_lt_of_ge (separated_mass_le_of_antitone (hF n) hh (by linarith)
      ((hshape n).2.mono (fun z hz => hcn.trans (hau.le.trans hz.1))))) hn
  · intro b hb
    let v := (m+b)/2
    have hmv : m < v := by dsimp [v]; linarith
    have hvb : v < b := by dsimp [v]; linarith
    obtain ⟨h, hh, hhr, hgap⟩ := exists_short_mass_gap hf (hmax v hmv.ne')
      (lt_min (sub_pos.mpr hmv) (sub_pos.mpr hvb))
    have hhm : h < v-m := hhr.trans_le (min_le_left _ _)
    have hhb : h < b-v := hhr.trans_le (min_le_right _ _)
    have hev := (hmass v (v+h) (by linarith)).eventually_lt
      (hmass m (m+h) (by linarith)) hgap
    filter_upwards [hev] with n hn
    by_contra hnc
    have hbc : b ≤ c n := le_of_not_gt hnc
    exact (not_lt_of_ge (separated_mass_le_of_monotone (hF n) hh (by linarith)
      ((hshape n).1.mono (fun z hz => (hz.2.trans (by linarith : v+h ≤ b)).trans hbc)))) hn

end Kagey131.PaperD.Modes
