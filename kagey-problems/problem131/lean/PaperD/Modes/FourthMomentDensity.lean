import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# A direct fourth-moment inequality for symmetric unimodal densities

Compare a decreasing even density to the uniform density on `[-r,r]`.
The two densities have the same mass and second moment when `r² = 3 m₂`.
A quartic with roots at their crossing and at `r` has nonnegative product
with their difference. Its integral proves `m₄ >= (9/5) m₂²` without a
representation theorem.
-/

namespace Kagey131.PaperD.Modes

open MeasureTheory Set

theorem even_apply_abs {g : ℝ → ℝ} (he : ∀ x, g (-x) = g x) (x : ℝ) :
    g |x| = g x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), he]

theorem decreasing_density_boundary {g : ℝ → ℝ} (hc : Continuous g)
    (he : ∀ x, g (-x) = g x) (hn : ∀ x, 0 ≤ g x) (hi : Integrable g)
    (hm : ∫ x, g x = 1) (ha : AntitoneOn g (Ici 0)) {r : ℝ} (hr : 0 < r) :
    g r ≤ 1 / (2 * r) := by
  have hle : (∫ _ in -r..r, g r) ≤ ∫ x in -r..r, g x := by
    apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hc.intervalIntegrable _ _)
    intro x hx
    have hxr : |x| ≤ r := abs_le.2 hx
    simpa only [even_apply_abs he] using ha (abs_nonneg x) hr.le hxr
  have hu : (∫ x in -r..r, g x) ≤ 1 := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact (setIntegral_le_integral hi (Filter.Eventually.of_forall hn)).trans_eq hm
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hle
  apply (le_div_iff₀ (by positivity : 0 < 2 * r)).2
  nlinarith

theorem decreasing_density_crossing {g : ℝ → ℝ} (hc : Continuous g)
    (he : ∀ x, g (-x) = g x) (ha : AntitoneOn g (Ici 0))
    {r c : ℝ} (hr : 0 < r) (hgr : g r ≤ c) :
    ∃ s ∈ Icc (0 : ℝ) r, ∀ x, (x ^ 2 - s ^ 2) * (g x - c) ≤ 0 := by
  by_cases h0 : g 0 ≤ c
  · refine ⟨0, ⟨le_rfl, hr.le⟩, ?_⟩
    intro x
    have hx : g x ≤ c := by
      have hh := ha (show (0 : ℝ) ∈ Ici 0 by simp) (abs_nonneg x) (abs_nonneg x)
      rw [even_apply_abs he] at hh
      exact hh.trans h0
    simpa using mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) (sub_nonpos.2 hx)
  · obtain ⟨s, hs, hsc⟩ := intermediate_value_Icc' hr.le hc.continuousOn
      (show c ∈ Icc (g r) (g 0) from ⟨hgr, (lt_of_not_ge h0).le⟩)
    refine ⟨s, hs, ?_⟩
    intro x
    by_cases hxs : |x| ≤ s
    · have hx : c ≤ g x := by
        rw [← hsc, ← even_apply_abs he x]
        exact ha (abs_nonneg x) hs.1 hxs
      have hx2 : x ^ 2 ≤ s ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hx2) (sub_nonneg.2 hx)
    · have hx : g x ≤ c := by
        rw [← hsc, ← even_apply_abs he x]
        exact ha hs.1 (abs_nonneg x) (le_of_lt (lt_of_not_ge hxs))
      have hsx : s ≤ |x| := (lt_of_not_ge hxs).le
      have hx2 : s ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x, hs.1]
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hx2) (sub_nonpos.2 hx)

noncomputable def crossingQuartic (s r x : ℝ) : ℝ :=
  (x ^ 2 - s ^ 2) * (x ^ 2 - r ^ 2)

theorem quartic_density_comparison {g : ℝ → ℝ} (hn : ∀ x, 0 ≤ g x)
    {s r : ℝ} (hr : 0 < r) (hs : s ∈ Icc (0 : ℝ) r)
    (hcross : ∀ x, (x ^ 2 - s ^ 2) * (g x - 1 / (2 * r)) ≤ 0) (x : ℝ) :
    (Icc (-r) r).indicator (fun y => crossingQuartic s r y / (2 * r)) x ≤
      crossingQuartic s r x * g x := by
  by_cases hx : x ∈ Icc (-r) r
  · rw [indicator_of_mem hx]
    have hxr : |x| ≤ r := abs_le.2 hx
    have hx2 : x ^ 2 - r ^ 2 ≤ 0 := by nlinarith [sq_abs x, abs_nonneg x]
    have hh := mul_nonneg_of_nonpos_of_nonpos (hcross x) hx2
    apply sub_nonneg.mp
    convert hh using 1 <;> first | rfl | (unfold crossingQuartic; ring)
  · rw [indicator_of_notMem hx]
    have hxr : r < |x| := lt_of_not_ge (fun h => hx (abs_le.1 h))
    have hxs : s ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x, hs.1, hs.2]
    have hx2 : r ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    exact mul_nonneg (mul_nonneg (sub_nonneg.2 hxs) (sub_nonneg.2 hx2)) (hn x)

theorem integral_quartic_density {g : ℝ → ℝ} (hi : Integrable g)
    (h2 : Integrable (fun x => x ^ 2 * g x))
    (h4 : Integrable (fun x => x ^ 4 * g x)) (s r : ℝ) :
    (∫ x, crossingQuartic s r x * g x) =
      (∫ x, x ^ 4 * g x) - (s ^ 2 + r ^ 2) * (∫ x, x ^ 2 * g x) +
        s ^ 2 * r ^ 2 * ∫ x, g x := by
  have he : (fun x => crossingQuartic s r x * g x) =
      (fun x => x ^ 4 * g x - (s ^ 2 + r ^ 2) * (x ^ 2 * g x) +
        (s ^ 2 * r ^ 2) * g x) := by
    funext x
    unfold crossingQuartic
    ring
  have hs : Integrable (fun x => x ^ 4 * g x - (s ^ 2 + r ^ 2) * (x ^ 2 * g x)) :=
    h4.sub (h2.const_mul _)
  rw [he, integral_add hs (hi.const_mul (s ^ 2 * r ^ 2)),
    integral_sub h4 (h2.const_mul (s ^ 2 + r ^ 2)), integral_const_mul, integral_const_mul]

theorem integrable_quartic_density {g : ℝ → ℝ} (hi : Integrable g)
    (h2 : Integrable (fun x => x ^ 2 * g x))
    (h4 : Integrable (fun x => x ^ 4 * g x)) (s r : ℝ) :
    Integrable (fun x => crossingQuartic s r x * g x) := by
  convert (h4.sub (h2.const_mul (s ^ 2 + r ^ 2))).add (hi.const_mul (s ^ 2 * r ^ 2)) using 1
  congr 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  unfold crossingQuartic
  ring

theorem integral_quartic_uniform (s r : ℝ) (hr : 0 < r) :
    (∫ x, (Icc (-r) r).indicator (fun y => crossingQuartic s r y / (2 * r)) x) =
      r ^ 4 / 5 - (s ^ 2 + r ^ 2) * (r ^ 2 / 3) + s ^ 2 * r ^ 2 := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  have he : (fun x => crossingQuartic s r x / (2 * r)) =
      (fun x => (x ^ 4 - (s ^ 2 + r ^ 2) * x ^ 2 + s ^ 2 * r ^ 2) / (2 * r)) := by
    funext x
    unfold crossingQuartic
    ring
  rw [he, intervalIntegral.integral_div]
  have hi4 : IntervalIntegrable (fun x : ℝ => x ^ 4) volume (-r) r :=
    (continuous_id.pow 4).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x : ℝ => x ^ 2) volume (-r) r :=
    (continuous_id.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hi4.sub (hi2.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_sub hi4 (hi2.const_mul _),
    intervalIntegral.integral_const_mul, integral_pow,
    integral_pow, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp
  ring

theorem fourth_moment_decreasing_density {g : ℝ → ℝ} (hc : Continuous g)
    (he : ∀ x, g (-x) = g x) (hn : ∀ x, 0 ≤ g x) (hi : Integrable g)
    (hm : ∫ x, g x = 1) (ha : AntitoneOn g (Ici 0))
    (h2 : Integrable (fun x => x ^ 2 * g x))
    (h4 : Integrable (fun x => x ^ 4 * g x))
    (hpos : 0 < ∫ x, x ^ 2 * g x) :
    (9 / 5 : ℝ) * (∫ x, x ^ 2 * g x) ^ 2 ≤ ∫ x, x ^ 4 * g x := by
  let r := Real.sqrt (3 * ∫ x, x ^ 2 * g x)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 3 * ∫ x, x ^ 2 * g x := Real.sq_sqrt (by positivity)
  obtain ⟨s, hs, hcross⟩ := decreasing_density_crossing hc he ha hr
    (decreasing_density_boundary hc he hn hi hm ha hr)
  have hu : Integrable ((Icc (-r) r).indicator (fun y => crossingQuartic s r y / (2 * r))) := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Icc
    apply ContinuousOn.integrableOn_Icc
    unfold crossingQuartic
    fun_prop
  have hcomp := integral_mono hu (integrable_quartic_density hi h2 h4 s r)
    (quartic_density_comparison hn hr hs hcross)
  rw [integral_quartic_uniform s r hr, integral_quartic_density hi h2 h4, hm] at hcomp
  have hr4 : r ^ 4 = 9 * (∫ x, x ^ 2 * g x) ^ 2 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = _ := by rw [hr2]; ring
  rw [hr4, hr2] at hcomp
  nlinarith

end Kagey131.PaperD.Modes
