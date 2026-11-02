import PaperD.Modes.AnalyticBarrier
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Strict contraction in the smoothing inequality

The positive gap `v^p + (1-v)^p - 1`, for `p < 1`, is the reason the
stretched-exponential barrier is a strict supersolution.
-/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology

noncomputable def smoothingGap (p v : ℝ) : ℝ := v ^ p + (1 - v) ^ p - 1

theorem smoothingGap_pos {p v : ℝ} (hp : p < 1) (hv : v ∈ Ioo 0 1) :
    0 < smoothingGap p v := by
  have h1 := Real.self_lt_rpow_of_lt_one hv.1 hv.2 hp
  have h2 := Real.self_lt_rpow_of_lt_one (show 0 < 1-v by linarith [hv.2])
    (show 1-v < 1 by linarith [hv.1]) hp
  unfold smoothingGap
  linarith

theorem continuous_smoothingGap {p : ℝ} (hp : 0 ≤ p) :
    Continuous (smoothingGap p) := by
  exact ((Real.continuous_rpow_const hp).add
    ((Real.continuous_rpow_const hp).comp (continuous_const.sub continuous_id))).sub
    continuous_const

theorem smoothing_contraction_tendsto {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Tendsto (fun n : ℕ => ∫ v in Ioo (0 : ℝ) 1,
      Real.exp (-(n : ℝ) * smoothingGap p v)) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (F := fun n : ℕ => fun v : ℝ => Real.exp (-(n : ℝ) * smoothingGap p v))
    (f := fun _ : ℝ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun n => (Real.continuous_exp.comp (continuous_const.mul (continuous_smoothingGap hp0))).aestronglyMeasurable)
    (integrable_const 1) ?_ ?_
  · simpa using h
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg n)) (smoothingGap_pos hp1 hv).le)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have hvp : 0 < smoothingGap p v := smoothingGap_pos hp1 hv
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hmul : Tendsto (fun n : ℕ => (n : ℝ) * smoothingGap p v) atTop atTop :=
      hnat.atTop_mul_const hvp
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hmul)

/-- A finite strict contraction parameter exists, with no quantitative claim
about its size. This is the dominated-convergence choice in Lemma F.4. -/
theorem exists_smoothing_contraction {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∃ n : ℕ, 1 ≤ n ∧ 2 * (∫ v in Ioo (0 : ℝ) 1,
      Real.exp (-(n : ℝ) * smoothingGap p v)) < 1 := by
  have h := (smoothing_contraction_tendsto hp0 hp1).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1/2 by norm_num))
  obtain ⟨n, hn⟩ := (h.and (eventually_ge_atTop 1)).exists
  exact ⟨n, hn.2, by linarith [hn.1]⟩

noncomputable def stretchedEnvelope (c r t : ℝ) : ℝ :=
  2 * Real.exp (-c * t^r)

theorem stretchedEnvelope_pos (c r t : ℝ) : 0 < stretchedEnvelope c r t := by
  unfold stretchedEnvelope
  positivity

theorem stretchedEnvelope_antitone {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) :
    AntitoneOn (stretchedEnvelope c r) (Ici 0) := by
  intro s hs t ht hst
  unfold stretchedEnvelope
  have hp := Real.rpow_le_rpow hs hst hr
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  nlinarith

theorem continuous_stretchedEnvelope {r : ℝ} (c : ℝ) (hr : 0 ≤ r) :
    Continuous (stretchedEnvelope c r) := by
  exact continuous_const.mul
    (Real.continuous_exp.comp (continuous_const.mul (Real.continuous_rpow_const hr)))

theorem stretchedEnvelope_product {a c r t v : ℝ} (ht : 0 ≤ t)
    (hv : v ∈ Ioo 0 1) :
    stretchedEnvelope c r (t * v^a) * stretchedEnvelope c r (t * (1-v)^a) =
      stretchedEnvelope c r t * (2 * Real.exp (-c * t^r * smoothingGap (a*r) v)) := by
  unfold stretchedEnvelope smoothingGap
  rw [Real.mul_rpow ht (Real.rpow_nonneg hv.1.le _),
      Real.mul_rpow ht (Real.rpow_nonneg (by linarith [hv.2]) _),
      ← Real.rpow_mul hv.1.le, ← Real.rpow_mul (show 0 ≤ 1-v by linarith [hv.2])]
  have he : -c * (t^r * v^(a*r)) + -c * (t^r * (1-v)^(a*r)) =
      -c*t^r + -c*t^r*(v^(a*r)+(1-v)^(a*r)-1) := by ring
  calc
    _ = 4 * Real.exp (-c * (t^r * v^(a*r)) + -c * (t^r * (1-v)^(a*r))) := by
      rw [Real.exp_add]; ring
    _ = _ := by rw [he, Real.exp_add]; ring

/-- The integral smoothing inequality yields strict separation at a possible
first contact with the stretched-exponential envelope. -/
theorem smoothing_strict_barrier {f : ℝ → ℝ} {a c r n t : ℝ}
    (hf : Continuous f) (hfn : ∀ x, 0 ≤ f x) (ha : 0 < a) (hr : 0 ≤ r)
    (ht : 0 < t) (hct : n ≤ c*t^r)
    (hcon : 2 * (∫ v in Ioo (0 : ℝ) 1,
      Real.exp (-n * smoothingGap (a*r) v)) < 1)
    (hfp : f t ≤ ∫ v in Ioo (0 : ℝ) 1, f (t*v^a) * f (t*(1-v)^a))
    (hprev : ∀ u ∈ Ico 0 t, f u ≤ stretchedEnvelope c r u)
    (har : a*r < 1) : f t < stretchedEnvelope c r t := by
  have hap : 0 ≤ a*r := mul_nonneg ha.le hr
  have hc1 : Continuous (fun v : ℝ => f (t*v^a) * f (t*(1-v)^a)) := by
    exact (hf.comp (continuous_const.mul (Real.continuous_rpow_const ha.le))).mul
      (hf.comp (continuous_const.mul ((Real.continuous_rpow_const ha.le).comp
        (continuous_const.sub continuous_id))))
  have hc2 : Continuous (fun v : ℝ => stretchedEnvelope c r t *
      (2 * Real.exp (-n * smoothingGap (a*r) v))) := by
    exact continuous_const.mul (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_smoothingGap hap))))
  have himon : (∫ v in Ioo (0 : ℝ) 1, f (t*v^a)*f (t*(1-v)^a)) ≤
      ∫ v in Ioo (0 : ℝ) 1, stretchedEnvelope c r t *
        (2 * Real.exp (-n*smoothingGap (a*r) v)) := by
    apply integral_mono_ae
      (hc1.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (hc2.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have hv0 := Real.rpow_pos_of_pos hv.1 a
    have hv1 := Real.rpow_lt_one hv.1.le hv.2 ha
    have hw0 := Real.rpow_pos_of_pos (show 0 < 1-v by linarith [hv.2]) a
    have hw1 := Real.rpow_lt_one (show 0 ≤ 1-v by linarith [hv.2]) (show 1-v < 1 by linarith [hv.1]) ha
    have hleft := hprev (t*v^a) ⟨mul_nonneg ht.le hv0.le, by nlinarith⟩
    have hright := hprev (t*(1-v)^a) ⟨mul_nonneg ht.le hw0.le, by nlinarith⟩
    calc
      _ ≤ stretchedEnvelope c r (t*v^a) * stretchedEnvelope c r (t*(1-v)^a) :=
        mul_le_mul hleft hright (hfn _) (stretchedEnvelope_pos _ _ _).le
      _ = _ := stretchedEnvelope_product ht.le hv
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (stretchedEnvelope_pos _ _ _).le
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        apply Real.exp_le_exp.mpr
        have he := mul_le_mul_of_nonneg_right hct (smoothingGap_pos har hv).le
        nlinarith
  have heq : (∫ v in Ioo (0 : ℝ) 1, stretchedEnvelope c r t *
      (2 * Real.exp (-n*smoothingGap (a*r) v))) =
      stretchedEnvelope c r t * (2 * (∫ v in Ioo (0 : ℝ) 1,
        Real.exp (-n*smoothingGap (a*r) v))) := by
    rw [integral_const_mul, integral_const_mul]
  rw [heq] at himon
  exact hfp.trans himon |>.trans_lt (by
    simpa using mul_lt_mul_of_pos_left hcon (stretchedEnvelope_pos c r t))

/-- The smoothing inequality and decay at infinity imply a stretched-exponential
bound. The permitted powers are exactly `0 < r` and `a*r < 1`; analyticity uses
the subrange `1 < r`. -/
theorem stretched_decay_of_smoothing {f : ℝ → ℝ} {a r : ℝ}
    (hf : Continuous f) (hfn : ∀ t, 0 ≤ f t)
    (hf1 : ∀ t, 0 ≤ t → f t ≤ 1) (ha : 0 < a) (hr : 0 < r) (har : a*r < 1)
    (hdecay : Tendsto f atTop (𝓝 0))
    (hfp : ∀ t, 0 ≤ t → f t ≤ ∫ v in Ioo (0 : ℝ) 1,
      f (t*v^a) * f (t*(1-v)^a)) :
    ∃ c > 0, ∀ t, 0 ≤ t → f t ≤ 2 * Real.exp (-c*t^r) := by
  obtain ⟨n, _, hn⟩ := exists_smoothing_contraction (mul_nonneg ha.le hr.le) har
  let l : ℝ := Real.log 2
  have hl : 0 < l := Real.log_pos (by norm_num)
  have hparam : Tendsto (fun x : ℝ => l*x^r) atTop atTop :=
    Tendsto.const_mul_atTop hl (tendsto_rpow_atTop hr)
  obtain ⟨K0, hK0⟩ := eventually_atTop.1 (hparam.eventually (eventually_ge_atTop (n : ℝ)))
  let K := max K0 1
  have hK : 1 ≤ K := le_max_right _ _
  have hnK : (n : ℝ) ≤ l*K^r := hK0 K (le_max_left _ _)
  have hdelta : 0 < stretchedEnvelope l r K := stretchedEnvelope_pos _ _ _
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 (hdecay.eventually (gt_mem_nhds hdelta))
  let T := max T0 1
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have htail : ∀ x, T ≤ x → f x < stretchedEnvelope l r K := by
    intro x hx
    exact hT0 x ((le_max_left _ _).trans hx)
  have hb1 : stretchedEnvelope l r 1 = 1 := by
    unfold stretchedEnvelope l
    rw [Real.one_rpow, mul_one, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hg : ∀ t, 0 ≤ t → f (T*t) ≤ stretchedEnvelope l r t := by
    apply continuous_barrier (hf.comp (continuous_const.mul continuous_id))
      (continuous_stretchedEnvelope l hr.le) (by linarith : 0 ≤ K)
    · intro t ht
      by_cases ht1 : t ≤ 1
      · calc
          f (T*t) ≤ 1 := hf1 _ (mul_nonneg hT.le ht.1)
          _ = stretchedEnvelope l r 1 := hb1.symm
          _ ≤ stretchedEnvelope l r t :=
            stretchedEnvelope_antitone hl.le hr.le ht.1 (by norm_num) ht1
      · have hTt : T ≤ T*t := by nlinarith [le_of_not_ge ht1]
        exact (htail _ hTt).le.trans
          (stretchedEnvelope_antitone hl.le hr.le ht.1
            (show K ∈ Ici 0 from le_trans (by norm_num) hK) ht.2)
    · intro t hKt hprev
      have ht : 0 < t := by linarith
      have hnt : (n : ℝ) ≤ l*t^r := hnK.trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hKt hr.le) hl.le)
      apply smoothing_strict_barrier (f := fun u => f (T*u))
        (hf.comp (continuous_const.mul continuous_id)) (fun u => hfn _) ha hr.le ht hnt hn
      · simpa [mul_assoc] using hfp (T*t) (mul_nonneg hT.le ht.le)
      · exact hprev
      · exact har
  refine ⟨l/T^r, div_pos hl (Real.rpow_pos_of_pos hT _), ?_⟩
  intro t ht
  have h := hg (t/T) (div_nonneg ht hT.le)
  have hid : T*(t/T) = t := by field_simp
  rw [hid] at h
  unfold stretchedEnvelope at h
  rw [Real.div_rpow ht hT.le] at h
  convert h using 1 <;> congr 2 <;> ring

/-- Form used for the modulus of the characteristic function. -/
theorem characteristic_stretched_decay {φ : ℝ → ℂ} {a r : ℝ}
    (hφ : Continuous φ) (hbound : ∀ t, ‖φ t‖ ≤ 1)
    (hsymm : ∀ t, ‖φ (-t)‖ = ‖φ t‖)
    (ha : 0 < a) (hr : 0 < r) (har : a*r < 1)
    (hdecay : Tendsto (fun t => ‖φ t‖) atTop (𝓝 0))
    (hfp : ∀ t, 0 ≤ t → ‖φ t‖ ≤ ∫ v in Ioo (0 : ℝ) 1,
      ‖φ (t*v^a)‖ * ‖φ (t*(1-v)^a)‖) :
    ∃ c > 0, ∀ t, ‖φ t‖ ≤ 2 * Real.exp (-c*|t|^r) := by
  obtain ⟨c, hc, h⟩ := stretched_decay_of_smoothing hφ.norm (fun t => norm_nonneg _)
    (fun t _ => hbound t) ha hr har hdecay hfp
  refine ⟨c, hc, fun t => ?_⟩
  by_cases ht : 0 ≤ t
  · simpa [abs_of_nonneg ht] using h t ht
  · simpa [abs_of_neg (lt_of_not_ge ht), hsymm] using h (-t) (by linarith)

end Kagey131.PaperD.Modes
