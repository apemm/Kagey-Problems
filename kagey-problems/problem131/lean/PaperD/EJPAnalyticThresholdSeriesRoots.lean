import PaperD.EJPAnalyticThresholdSeries

/-!
# Order, truncation, and roots of the actual H series
-/

open Set Filter FormalMultilinearSeries
open scoped Topology ENNReal

namespace Kagey131.PaperD.Modes.AnalyticThreshold.Series

theorem deriv_H_neg {a y : ℝ} (ha : 1 / 2 < a) (hy0 : 0 ≤ y) (hy : y < 1) :
    deriv (H a) y < 0 := by
  have hr := enorm_lt_radius (coeff_radius ha) (abs_lt.mpr ⟨by linarith, hy⟩)
  have hs := summable_powerSum (hr.trans_le (radius_derivCoeff (coeff a)))
  have hnn : ∀ k : ℕ, 0 ≤ derivCoeff (coeff a) k * y ^ k := by
    intro k
    exact mul_nonneg (mul_nonneg (by positivity) (coeff_nonneg ha _)) (pow_nonneg hy0 k)
  have hle := hs.le_tsum 0 (fun k _ => hnn k)
  have hp := coeff_pos ha (by decide : 0 < (1 : ℕ))
  simp only [derivCoeff, Nat.cast_zero, zero_add, one_mul, pow_zero, mul_one] at hle
  change coeff a 1 ≤ powerSum (derivCoeff (coeff a)) y at hle
  rw [(hasDerivAt_H ha (abs_lt.mpr ⟨by linarith, hy⟩)).deriv]
  linarith

theorem strictAntiOn_H {a : ℝ} (ha : 1 / 2 < a) : StrictAntiOn (H a) (Ico 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico 0 1)
  · exact (continuousOn_H ha).mono (by intro y hy; constructor <;> linarith [hy.1, hy.2])
  · intro y hy
    simp only [interior_Ico, mem_Ioo] at hy
    exact deriv_H_neg ha hy.1.le hy.2

theorem coeff_parameter_antitone {a b : ℝ} (ha : 1 / 2 < a) (hab : a ≤ b) (k : ℕ) :
    coeff b k ≤ coeff a k := by
  rcases k with _ | k
  · simp
  · rw [coeff_of_pos (Nat.succ_pos k), coeff_of_pos (Nat.succ_pos k)]
    apply div_le_div_of_nonneg_left (chi_pos _).le (denominator_pos ha (Nat.succ_pos k))
    exact sub_le_sub_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hab (by norm_num : (0 : ℝ) ≤ 2)) (Nat.cast_nonneg _)) 1

theorem H_parameter_mono {a b y : ℝ} (ha : 1 / 2 < a) (hab : a ≤ b)
    (hy0 : 0 ≤ y) (hy : y < 1) : H a y ≤ H b y := by
  have habs : |y| < 1 := abs_lt.mpr ⟨by linarith, hy⟩
  have h := (summable_coeff (ha.trans_le hab) habs).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_right (coeff_parameter_antitone ha hab k) (pow_nonneg hy0 k))
    (summable_coeff ha habs)
  dsimp [H, powerSum]
  linarith

theorem H_parameter_strict {a b y : ℝ} (ha : 1 / 2 < a) (hab : a < b)
    (hy0 : 0 < y) (hy : y < 1) : H a y < H b y := by
  have habs : |y| < 1 := abs_lt.mpr ⟨by linarith, hy⟩
  have hstrict : coeff b 1 * y ^ 1 < coeff a 1 * y ^ 1 := by
    apply mul_lt_mul_of_pos_right _ (pow_pos hy0 _)
    simp only [coeff_of_pos (by decide : 0 < (1 : ℕ)), Nat.cast_one, mul_one]
    apply (div_lt_div_iff₀ (by linarith : 0 < 2 * b - 1) (by linarith : 0 < 2 * a - 1)).2
    rw [chi_one]
    nlinarith
  have h := Summable.tsum_lt_tsum
    (fun k => mul_le_mul_of_nonneg_right (coeff_parameter_antitone ha hab.le k) (pow_nonneg hy0.le k))
    hstrict (summable_coeff (ha.trans hab) habs) (summable_coeff ha habs)
  dsimp [H, powerSum]
  linarith

theorem coeff_one_succ (n : ℕ) : coeff 1 (n + 1) = chi n - chi (n + 1) := by
  rw [coeff_of_pos (Nat.succ_pos n)]
  simp only [Nat.cast_succ]
  have hd : 2 * (1 : ℝ) * (n + 1) - 1 ≠ 0 := by
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith
  apply (div_eq_iff hd).2
  have hn := chi_recurrence n
  push_cast
  nlinarith

theorem H_one_eq_mul_G {y : ℝ} (hy : |y| < 1) : H 1 y = (1 - y) * G y := by
  have hc := (summable_coeff (by norm_num : (1 / 2 : ℝ) < 1) hy).sum_add_tsum_nat_add 1
  have hg := (summable_chi hy).sum_add_tsum_nat_add 1
  have hshift := (summable_nat_add_iff 1).mpr (summable_chi hy)
  have hs : Summable (fun n : ℕ => chi n * y ^ (n + 1)) := by
    simpa [pow_succ, mul_assoc] using (summable_chi hy).mul_right y
  have h : (∑' n : ℕ, coeff 1 (n + 1) * y ^ (n + 1)) = y * G y - (G y - 1) := by
    simp_rw [coeff_one_succ, sub_mul]
    rw [hs.tsum_sub hshift]
    have hfirst : (∑' n : ℕ, chi n * y ^ (n + 1)) = y * G y := by
      simp only [pow_succ, G, powerSum, ← tsum_mul_left]
      apply tsum_congr
      intro n
      ring
    rw [hfirst]
    have hlast : (∑' n : ℕ, chi (n + 1) * y ^ (n + 1)) = G y - 1 := by
      dsimp [G, powerSum]
      simpa using (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hg))
    rw [hlast]
  simp only [Finset.sum_range_one, coeff_zero, zero_mul, zero_add] at hc
  dsimp [H, powerSum]
  rw [← hc, h]
  ring

/-- The reference parameter is identified directly, without endpoint convergence. -/
theorem H_one_eq_sqrt {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 1) :
    H 1 y = Real.sqrt (1 - y) := by
  rw [H_one_eq_mul_G (abs_lt.mpr ⟨by linarith, hy⟩), G_eq_inv_sqrt hy0 hy]
  have hs := Real.sq_sqrt (show 0 ≤ 1 - y by linarith)
  have hne := (Real.sqrt_pos.mpr (show 0 < 1 - y by linarith)).ne'
  rw [← div_eq_mul_inv]
  exact (div_eq_iff hne).2 (by nlinarith)

/-- A strictly positive first-coefficient gap forces a zero before one. -/
theorem H_le_sqrt_sub_linear {a y : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (hy0 : 0 ≤ y) (hy : y < 1) :
    H a y ≤ Real.sqrt (1 - y) - (coeff a 1 - coeff 1 1) * y := by
  have habs := abs_lt.mpr (show -1 < y ∧ y < 1 by constructor <;> linarith)
  have hs := (summable_coeff ha habs).sub (summable_coeff (a := 1) (by norm_num) habs)
  have hn : ∀ k : ℕ, 0 ≤ coeff a k * y ^ k - coeff 1 k * y ^ k := by
    intro k
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right
      (coeff_parameter_antitone ha ha1.le k) (pow_nonneg hy0 k))
  have h := hs.le_tsum 1 (fun k _ => hn k)
  rw [(summable_coeff ha habs).tsum_sub (summable_coeff (a := 1) (by norm_num) habs)] at h
  have he := H_one_eq_sqrt hy0 hy
  dsimp [H, powerSum] at he ⊢
  simp only [pow_one] at h
  nlinarith

theorem exists_negative_before_one {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    ∃ r ∈ Ioo (0 : ℝ) 1, H a r < 0 := by
  let c := coeff a 1 - coeff 1 1
  have hc : 0 < c := by
    dsimp [c]
    simp only [coeff_of_pos (by decide : 0 < (1 : ℕ)), Nat.cast_one, mul_one, chi_one]
    apply sub_pos.mpr
    norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, div_one]
    apply (lt_div_iff₀ (by linarith : 0 < 2 * a - 1)).2
    nlinarith
  let d := min (1 / 2 : ℝ) (c / 4)
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hd1 : d ≤ 1 / 2 := min_le_left _ _
  have hdc : d ≤ c / 4 := min_le_right _ _
  have hr0 : 0 < 1 - d ^ 2 := by nlinarith
  have hr1 : 1 - d ^ 2 < 1 := by nlinarith
  refine ⟨1 - d ^ 2, ⟨hr0, hr1⟩, ?_⟩
  have h := H_le_sqrt_sub_linear ha ha1 hr0.le hr1
  have hs : Real.sqrt (1 - (1 - d ^ 2)) = d := by
    rw [show 1 - (1 - d ^ 2) = d ^ 2 by ring, Real.sqrt_sq hd.le]
  rw [hs] at h
  change H a (1 - d ^ 2) ≤ d - c * (1 - d ^ 2) at h
  have hsq : d ^ 2 ≤ 1 / 4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq hc.le
  nlinarith

/-- The actual tail, rather than an assumed remainder. -/
noncomputable def tail (a y : ℝ) : ℝ := ∑' n : ℕ, coeff a (n + 4) * y ^ (n + 4)

theorem H_eq_three_sub_tail {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) :
    H a y = hThree a y - tail a y := by
  have hs := (summable_coeff ha hy).sum_add_tsum_nat_add 4
  dsimp [H, powerSum, tail, hThree]
  rw [← hs]
  norm_num [Finset.sum_range_succ, coeff, chi_one, chi_two, chi_three]
  ring

theorem tail_nonneg {a y : ℝ} (ha : 1 / 2 < a) (hy : 0 ≤ y) : 0 ≤ tail a y :=
  tsum_nonneg (fun k => mul_nonneg (coeff_nonneg ha _) (pow_nonneg hy _))

theorem tail_coeff_le {a : ℝ} (ha : 2 / 3 ≤ a) (n : ℕ) :
    coeff a (n + 4) ≤ (35 / 128 : ℝ) / (8 * a - 1) := by
  rw [coeff_of_pos (by omega : 0 < n + 4)]
  apply tail_coefficient_le ha (by exact_mod_cast (show 4 ≤ n + 4 by omega))
  simpa using chi_antitone (show 4 ≤ n + 4 by omega)

theorem tail_le {a y : ℝ} (ha : 2 / 3 ≤ a) (hy0 : 0 ≤ y) (hy : y < 1) :
    tail a y ≤ hTailMajorant a y := by
  apply tail_le_majorant hy0 hy
  · exact (summable_nat_add_iff 4).mpr (summable_coeff (by linarith) (abs_lt.mpr ⟨by linarith, hy⟩))
  · exact tail_coeff_le ha

theorem H_negative_three_fifths : H (2 / 3) (3 / 5) < 0 := by
  exact (h_negative_three_fifths
    (H_eq_three_sub_tail (by norm_num) (by norm_num))
    (tail_nonneg (by norm_num) (by norm_num))).2

theorem H_negative_upper_endpoint : H (69 / 100) (2 / 3) < 0 := by
  exact (h_negative_upper_endpoint
    (H_eq_three_sub_tail (by norm_num) (by norm_num))
    (tail_nonneg (by norm_num) (by norm_num))).2

theorem H_positive_lower_endpoint : 0 < H (2 / 3) (117 / 200) := by
  exact (h_positive_lower_endpoint
    (H_eq_three_sub_tail (by norm_num) (by norm_num))
    (tail_le le_rfl (by norm_num) (by norm_num))).2

/-- A sign bracket produces a unique actual series root in (0,1). -/
theorem exists_unique_root_of_negative {a r : ℝ} (ha : 1 / 2 < a)
    (hr0 : 0 < r) (hr1 : r < 1) (hr : H a r < 0) :
    ∃! y, y ∈ Ioo (0 : ℝ) 1 ∧ H a y = 0 := by
  have hc : ContinuousOn (H a) (Icc 0 r) :=
    (continuousOn_H ha).mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  obtain ⟨y, hy, hzero⟩ := intermediate_value_Icc' hr0.le hc
    (show (0 : ℝ) ∈ Icc (H a r) (H a 0) by simp; exact hr.le)
  have hy0 : 0 < y := by
    by_contra hn
    have : y = 0 := le_antisymm (le_of_not_gt hn) hy.1
    simp [this] at hzero
  refine ⟨y, ⟨⟨hy0, hy.2.trans_lt hr1⟩, hzero⟩, ?_⟩
  intro z hz
  exact (strictAntiOn_H ha).injOn ⟨hz.1.1.le, hz.1.2⟩ ⟨hy0.le, hy.2.trans_lt hr1⟩
    (hz.2.trans hzero.symm)

theorem exists_unique_root {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    ∃! y, y ∈ Ioo (0 : ℝ) 1 ∧ H a y = 0 := by
  obtain ⟨r, hr, hneg⟩ := exists_negative_before_one ha ha1
  exact exists_unique_root_of_negative ha hr.1 hr.2 hneg

/-- The uniquely determined actual root. Outside the physical interval it is set to zero. -/
noncomputable def rootY (a : ℝ) : ℝ :=
  if h : a ∈ Ioo (1 / 2 : ℝ) 1 then Classical.choose (exists_unique_root h.1 h.2) else 0

theorem rootY_spec {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    rootY a ∈ Ioo (0 : ℝ) 1 ∧ H a (rootY a) = 0 := by
  rw [rootY, dif_pos ⟨ha, ha1⟩]
  exact (Classical.choose_spec (exists_unique_root ha ha1)).1

theorem rootY_mem {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) : rootY a ∈ Ioo (0 : ℝ) 1 :=
  (rootY_spec ha ha1).1

theorem H_rootY {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) : H a (rootY a) = 0 :=
  (rootY_spec ha ha1).2

theorem H_pos_before_rootY {a y : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (hy0 : 0 ≤ y) (hy : y < rootY a) : 0 < H a y := by
  have hr := rootY_mem ha ha1
  have h := strictAntiOn_H ha ⟨hy0, hy.trans hr.2⟩ ⟨hr.1.le, hr.2⟩ hy
  simpa only [H_rootY ha ha1] using h

theorem H_neg_after_rootY {a y : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (hy : rootY a < y) (hy1 : y < 1) : H a y < 0 := by
  have hr := rootY_mem ha ha1
  have h := strictAntiOn_H ha ⟨hr.1.le, hr.2⟩ ⟨hr.1.le.trans hy.le, hy1⟩ hy
  simpa only [H_rootY ha ha1] using h

theorem deriv_H_rootY_neg {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    deriv (H a) (rootY a) < 0 :=
  deriv_H_neg ha (rootY_mem ha ha1).1.le (rootY_mem ha ha1).2

theorem rootY_simple {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    H a (rootY a) = 0 ∧ deriv (H a) (rootY a) ≠ 0 :=
  ⟨H_rootY ha ha1, (deriv_H_rootY_neg ha ha1).ne⟩

theorem rootY_lt_of_H_neg {a r : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hneg : H a r < 0) : rootY a < r := by
  by_contra hn
  have h := (strictAntiOn_H ha).antitoneOn ⟨hr0, hr1⟩
    ⟨(rootY_mem ha ha1).1.le, (rootY_mem ha ha1).2⟩ (le_of_not_gt hn)
  rw [H_rootY ha ha1] at h
  linarith

theorem lt_rootY_of_H_pos {a r : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hpos : 0 < H a r) : r < rootY a := by
  by_contra hn
  have h := (strictAntiOn_H ha).antitoneOn
    ⟨(rootY_mem ha ha1).1.le, (rootY_mem ha ha1).2⟩ ⟨hr0, hr1⟩ (le_of_not_gt hn)
  rw [H_rootY ha ha1] at h
  linarith

theorem rootY_strictMono : StrictMonoOn rootY (Ioo (1 / 2 : ℝ) 1) := by
  intro a ha b hb hab
  have hp := H_parameter_strict ha.1 hab (rootY_mem ha.1 ha.2).1 (rootY_mem ha.1 ha.2).2
  rw [H_rootY ha.1 ha.2] at hp
  exact lt_rootY_of_H_pos hb.1 hb.2 (rootY_mem ha.1 ha.2).1.le (rootY_mem ha.1 ha.2).2 hp

theorem rootY_two_thirds_enclosure :
    (117 / 200 : ℝ) < rootY (2 / 3) ∧ rootY (2 / 3) < 3 / 5 := by
  exact ⟨lt_rootY_of_H_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    H_positive_lower_endpoint,
    rootY_lt_of_H_neg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    H_negative_three_fifths⟩

theorem rootY_upper_endpoint_lt : rootY (69 / 100) < (2 / 3 : ℝ) :=
  rootY_lt_of_H_neg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    H_negative_upper_endpoint

theorem rootY_lt_two_thirds_on_band {a : ℝ} (ha : 2 / 3 ≤ a) (ha1 : a ≤ 69 / 100) :
    rootY a < 2 / 3 := by
  have h := rootY_strictMono.monotoneOn (show a ∈ Ioo (1 / 2 : ℝ) 1 by constructor <;> linarith)
    (show (69 / 100 : ℝ) ∈ Ioo (1 / 2 : ℝ) 1 by norm_num) ha1
  exact h.trans_lt rootY_upper_endpoint_lt

end Kagey131.PaperD.Modes.AnalyticThreshold.Series
