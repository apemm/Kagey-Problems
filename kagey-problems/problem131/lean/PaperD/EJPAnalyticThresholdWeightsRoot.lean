import PaperD.EJPAnalyticThresholdWeightsMemory
import PaperD.EJPAnalyticThresholdSeriesRoots
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The actual canonical root kernel on the transition band

The score bound is derived from actual coefficient sums. `rootRate_balance`
constructs the differentiated-normalization equation from these sums without
an external hypothesis. `WeightsParameter` identifies this rate and `rootKa`
with the actual parameter derivatives.
-/

open Set Filter
open scoped Topology

namespace Kagey131.PaperD.Modes.AnalyticThreshold.Weights

open Series

noncomputable def rootK (a u : ℝ) : ℝ := K a (rootY a) u

noncomputable def rootScore (a q : ℝ) : ℝ → ℝ :=
  logWeightScore (K a (rootY a)) (Ka a (rootY a) q) (3 * a - 2)

/-- The logarithmic root rate determined entirely by actual coefficient sums. -/
noncomputable def rootRate (a : ℝ) : ℝ :=
  (∑' k, d a k * weight a (rootY a) k) / Series.moment a (rootY a) 1

noncomputable def rootKa (a u : ℝ) : ℝ := Ka a (rootY a) (rootRate a) u

theorem rootRate_balance {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    RootBalance a (rootY a) (rootRate a) := by
  have hr := rootY_mem ha ha1
  have hm := Series.moment_first ha (by simpa [abs_of_pos hr.1] using hr.2) (H_rootY ha ha1)
  have hp : 0 < Series.moment a (rootY a) 1 := by
    have hg := G_pos hr.1.le hr.2
    nlinarith
  exact div_mul_cancel₀ _ hp.ne'

theorem root_factorization {a u : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    H a (rootY a * u) = (1 - u) * rootK a u :=
  H_mul_eq ha (rootY_mem ha ha1).1.le (rootY_mem ha ha1).2 (H_rootY ha ha1) hu hu1

theorem root_weights_normalized {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    ∑' k, weight a (rootY a) k = 1 := sum_weight_eq_one (H_rootY ha ha1)

theorem root_kernel_bounds {a q u : ℝ} (ha : 2 / 3 ≤ a) (ha1 : a ≤ 69 / 100)
    (hq : RootBalance a (rootY a) q) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    1 ≤ rootK a u ∧ 0 ≤ Ku a (rootY a) u ∧ Ku a (rootY a) u < 21 / 32 ∧
      0 ≤ Ka a (rootY a) q u ∧ Kau a (rootY a) q u ≤ 45 / 4 := by
  have ha0 : 1 / 2 < a := by linarith
  have ha2 : a < 1 := by linarith
  have hr := rootY_mem ha0 ha2
  have hz := H_rootY ha0 ha2
  have hbound := (rootY_lt_two_thirds_on_band ha ha1).le
  exact ⟨one_le_K ha0 hr.1.le hr.2 hz hu hu1, Ku_nonneg ha0 hr.1.le hu,
    Ku_lt ha hr.1.le hbound hz hu hu1, Ka_nonneg ha hr.1 hr.2 hz hq hu hu1,
    Kau_le ha hr.1 hbound hz hq hu hu1⟩

/-- The mixed score derivative bound is a conclusion from actual weights. -/
theorem root_score_derivative_lower_bound {a q u : ℝ}
    (ha : 2 / 3 ≤ a) (ha1 : a ≤ 69 / 100) (hq : RootBalance a (rootY a) q)
    (hu : 0 < u) (hu1 : u < 1) :
    (39 / 160 : ℝ) ≤ deriv (rootScore a q) u := by
  have ha0 : 1 / 2 < a := by linarith
  have ha2 : a < 1 := by linarith
  have hr := rootY_mem ha0 ha2
  obtain ⟨hK, hKu0, hKu1, hKa, hKau⟩ := root_kernel_bounds ha ha1 hq hu.le hu1.le
  exact deriv_logWeightScore_lower_bound (hasDerivAt_K ha0 hr.1.le hr.2 hu hu1)
    (hasDerivAt_Ka ha hr.1.le hr.2 hu hu1) hu hu1 (s_range ha ha1).1 (s_range ha ha1).2
    hK hKu0 hKu1.le hKa hKau

theorem root_score_strictMono {a q : ℝ} (ha : 2 / 3 ≤ a) (ha1 : a ≤ 69 / 100)
    (hq : RootBalance a (rootY a) q) : StrictMonoOn (rootScore a q) (Ioo (0 : ℝ) 1) := by
  have ha0 : 1 / 2 < a := by linarith
  have ha2 : a < 1 := by linarith
  have hr := rootY_mem ha0 ha2
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro u hu
    exact (hasDerivAt_logWeightScore
      (hasDerivAt_K ha0 hr.1.le hr.2 hu.1 hu.2)
      (hasDerivAt_Ka ha hr.1.le hr.2 hu.1 hu.2) hu.2
      (one_le_K ha0 hr.1.le hr.2 (H_rootY ha0 ha2) hu.1.le hu.2.le)).continuousAt.continuousWithinAt
  · intro u hu
    have hui : u ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ioo] using hu
    have h := root_score_derivative_lower_bound ha ha1 hq hui.1 hui.2
    linarith

theorem measurable_K (a Y : ℝ) : Measurable (K a Y) := by
  apply Measurable.tsum
  intro k
  have hg : Continuous (geom k) := continuous_iff_continuousAt.mpr
    (fun u => (hasDerivAt_geom k u).continuousAt)
  exact measurable_const.mul hg.measurable

theorem measurable_Ka (a Y q : ℝ) : Measurable (Ka a Y q) := by
  apply Measurable.tsum
  intro k
  have hg : Continuous (geom k) := continuous_iff_continuousAt.mpr
    (fun u => (hasDerivAt_geom k u).continuousAt)
  exact measurable_const.mul hg.measurable

theorem measurable_rootK (a : ℝ) : Measurable (rootK a) := measurable_K a (rootY a)

theorem measurable_rootKa (a : ℝ) : Measurable (rootKa a) := measurable_Ka a (rootY a) (rootRate a)

theorem K_at_zero {a Y : ℝ} (hroot : H a Y = 0) : K a Y 0 = 1 := by
  rw [← sum_weight_eq_one hroot]
  apply tsum_congr
  intro k
  cases k with
  | zero => simp [geom]
  | succ k => simp [geom, Finset.sum_range_succ']

theorem Ka_at_zero {a Y q : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hq : RootBalance a Y q) : Ka a Y q 0 = 0 := by
  calc
    Ka a Y q 0 = ∑' k, weightA a Y q k := by
      apply tsum_congr
      intro k
      cases k with
      | zero => simp [geom, weightA]
      | succ k => simp [geom, Finset.sum_range_succ']
    _ = 0 := sum_weightA_zero ha hY0 hY hq

theorem continuousOn_Ka {a Y q : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 ≤ Y) (hY : Y < 1) :
    ContinuousOn (Ka a Y q) (Icc (0 : ℝ) 1) := by
  have hs := (summable_weightA_mul (q := q) ha hY0 hY 1 (f := fun k => (k : ℝ))
    (fun k => Nat.cast_nonneg k) (fun _ => by simp)).abs
  have hb : Summable (fun k => |weightA a Y q k| * (k : ℝ)) := by
    simpa [abs_mul] using hs
  apply continuousOn_tsum (fun k => ?_) hb (fun k u hu => ?_)
  · have hg : Continuous (geom k) := continuous_iff_continuousAt.mpr
      (fun u => (hasDerivAt_geom k u).continuousAt)
    exact (continuous_const.mul hg).continuousOn
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (geom_nonneg hu.1 k)]
    exact mul_le_mul_of_nonneg_left (geom_le hu.1 hu.2 k) (abs_nonneg _)

theorem rootK_le_two {a u : ℝ} (ha : 2 / 3 ≤ a) (ha1 : a ≤ 69 / 100)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) : rootK a u ≤ 2 := by
  have ha0 : 1 / 2 < a := by linarith
  have ha2 : a < 1 := by linarith
  have hr := rootY_mem ha0 ha2
  have hz := H_rootY ha0 ha2
  have hdiff : DifferentiableOn ℝ (K a (rootY a)) (interior (Icc (0 : ℝ) 1)) := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hx
    exact (hasDerivAt_K ha0 hr.1.le hr.2 hx'.1 hx'.2).differentiableAt.differentiableWithinAt
  have hsub := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    (continuousOn_K ha0 hr.1.le hr.2) hdiff
    (C := (21 / 32 : ℝ)) (fun x hx => ?_) 0 (by norm_num) u ⟨hu, hu1⟩ hu
  · rw [K_at_zero hz] at hsub
    change K a (rootY a) u ≤ 2
    linarith
  · have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hx
    rw [(hasDerivAt_K ha0 hr.1.le hr.2 hx'.1 hx'.2).deriv]
    exact (Ku_lt ha hr.1.le (rootY_lt_two_thirds_on_band ha ha1).le hz hx'.1.le hx'.2.le).le

theorem abs_rootKa_le_twelve {a u : ℝ} (ha : 2 / 3 ≤ a) (ha1 : a ≤ 69 / 100)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) : |rootKa a u| ≤ 12 := by
  have ha0 : 1 / 2 < a := by linarith
  have ha2 : a < 1 := by linarith
  have hr := rootY_mem ha0 ha2
  have hz := H_rootY ha0 ha2
  have hq := rootRate_balance ha0 ha2
  have hdiff : DifferentiableOn ℝ (Ka a (rootY a) (rootRate a)) (interior (Icc (0 : ℝ) 1)) := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hx
    exact (hasDerivAt_Ka ha hr.1.le hr.2 hx'.1 hx'.2).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Icc (0 : ℝ) 1),
      deriv (Ka a (rootY a) (rootRate a)) x ≤ (45 / 4 : ℝ) := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hx
    rw [(hasDerivAt_Ka ha hr.1.le hr.2 hx'.1 hx'.2).deriv]
    exact Kau_le ha hr.1 (rootY_lt_two_thirds_on_band ha ha1).le hz hq hx'.1.le hx'.2.le
  have hsub := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    (continuousOn_Ka ha hr.1.le hr.2) hdiff hderiv 0 (by norm_num) u ⟨hu, hu1⟩ hu
  rw [Ka_at_zero ha hr.1.le hr.2 hq] at hsub
  rw [rootKa, abs_of_nonneg (Ka_nonneg ha hr.1 hr.2 hz hq hu hu1)]
  linarith

theorem actual_score_strictMono {a : ℝ} (ha : 2 / 3 ≤ a) (ha1 : a ≤ 69 / 100) :
    StrictMonoOn (logWeightScore (rootK a) (rootKa a) (3 * a - 2)) (Ioo (0 : ℝ) 1) :=
  root_score_strictMono ha ha1 (rootRate_balance (by linarith) (by linarith))

end Kagey131.PaperD.Modes.AnalyticThreshold.Weights
