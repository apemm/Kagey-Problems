import PaperD.T2_RRTForced

/-!
# Reflection and lower-half first differences from two initial plus signs

With a positive root, `RRT.lawQ` counts minus signs. We use its finite
recurrence in that index, then convert to the number of plus signs.
-/

namespace Kagey131.PaperD

noncomputable abbrev minusLaw (a : ℝ) : ℕ → ℕ → ℝ :=
  RRT.lawQ (RRT.forceQ ((1 - a) / 2) 2)

/-- The plus-count law with the first two signs positive and subsequent
flip probability `(1 - a) / 2`. -/
noncomputable def positiveStartTwoLaw (a : ℝ) (n k : ℕ) : ℝ :=
  if k ≤ n then RRT.lawQ (RRT.forceQ ((1 - a) / 2) 2) n (n - k) else 0

theorem minusLaw_two (a : ℝ) (k : ℕ) :
    minusLaw a 2 k = if k = 0 then 1 else 0 :=
  RRT.lawQ_forced_early _ (by decide) le_rfl k

theorem positiveStartTwoLaw_two (a : ℝ) (k : ℕ) :
    positiveStartTwoLaw a 2 k = if k = 2 then 1 else 0 := by
  by_cases hk : k ≤ 2
  · rw [positiveStartTwoLaw, if_pos hk]
    change minusLaw a 2 (2 - k) = _
    simp only [minusLaw_two, show 2 - k = 0 ↔ k = 2 by omega]
  · simp [positiveStartTwoLaw, hk, show k ≠ 2 by omega]

noncomputable abbrev rise (a : ℝ) (n k : ℕ) : ℝ :=
  upProb ((1 - a) / 2) n k

theorem minusLaw_zero_step (a : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    minusLaw a (n + 1) 0 = minusLaw a n 0 * (1 - rise a n 0) := by
  unfold minusLaw
  rw [RRT.lawQ_succ_zero _ (show 1 ≤ n by omega), RRT.forceQ, if_neg (by omega)]

theorem minusLaw_succ_step (a : ℝ) {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    minusLaw a (n + 1) (k + 1) =
      minusLaw a n (k + 1) * (1 - rise a n (k + 1)) + minusLaw a n k * rise a n k := by
  unfold minusLaw
  rw [RRT.lawQ_succ_succ _ (show 1 ≤ n by omega), RRT.forceQ, if_neg (by omega)]

theorem rise_reflect (a : ℝ) {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) :
    rise a n (n - k) = 1 - rise a n k := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [rise, upProb, Nat.cast_sub hk, sub_div, div_self hnR]
  ring

theorem rise_succ (a : ℝ) (n k : ℕ) :
    rise a n (k + 1) = rise a n k + a / n := by
  simp only [rise, upProb, Nat.cast_add, Nat.cast_one, add_div]
  ring

theorem rise_nonneg {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) : 0 ≤ rise a n k :=
  upProb_nonneg (by linarith) (by linarith) (by omega) hk

theorem stay_nonneg {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) : 0 ≤ 1 - rise a n k := by
  rw [← rise_reflect a hn hk]
  exact rise_nonneg ha ha1 hn (by omega)

-- Both forced positive signs remain in the count at every later time.
theorem minusLaw_outside (a : ℝ) {n : ℕ} (hn : 2 ≤ n) {k : ℕ}
    (hk : n ≤ k + 1) : minusLaw a n k = 0 := by
  induction n, hn using Nat.le_induction generalizing k with
  | base => rw [minusLaw_two, if_neg (by omega)]
  | succ n hn ih =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [minusLaw_succ_step a hn, ih (by omega), ih (by omega), zero_mul, zero_mul, add_zero]

theorem minusLaw_reflection {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk : 2 * k ≤ n) :
    minusLaw a n (n - k) ≤ minusLaw a n k := by
  induction n, hn using Nat.le_induction generalizing k with
  | base =>
    rw [minusLaw_two a (2 - k), if_neg (by omega), minusLaw_two]
    split <;> norm_num
  | succ n hn ih =>
    by_cases hcenter : 2 * k = n + 1
    · rw [show n + 1 - k = k by omega]
    cases k with
    | zero =>
      rw [Nat.sub_zero, minusLaw_succ_step a hn n, minusLaw_zero_step a hn,
        minusLaw_outside a hn (by omega : n ≤ (n + 1) + 1), zero_mul, zero_add]
      have hrise : rise a n n = 1 - rise a n 0 := by
        simpa only [Nat.sub_zero] using rise_reflect a hn (Nat.zero_le n)
      rw [hrise]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Nat.sub_zero] using ih (k := 0) (by omega))
        (stay_nonneg ha ha1 hn (by omega))
    | succ j =>
      rw [show n + 1 - (j + 1) = (n - (j + 1)) + 1 by omega,
        minusLaw_succ_step a hn (n - (j + 1)), minusLaw_succ_step a hn j,
        show (n - (j + 1)) + 1 = n - j by omega,
        rise_reflect a hn (show j ≤ n by omega),
        rise_reflect a hn (show j + 1 ≤ n by omega), sub_sub_cancel]
      rw [add_comm (minusLaw a n (n - j) * rise a n j)]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (ih (k := j + 1) (by omega))
          (stay_nonneg ha ha1 hn (by omega)))
        (mul_le_mul_of_nonneg_right (ih (k := j) (by omega))
          (rise_nonneg ha ha1 hn (by omega)))

theorem minusLaw_diff_step (a : ℝ) {n : ℕ} (hn : 2 ≤ n) (j : ℕ) :
    minusLaw a (n + 1) (j + 2) - minusLaw a (n + 1) (j + 1) =
      (1 - rise a n (j + 2)) * (minusLaw a n (j + 2) - minusLaw a n (j + 1)) +
        rise a n j * (minusLaw a n (j + 1) - minusLaw a n j) := by
  rw [minusLaw_succ_step a hn (j + 1), minusLaw_succ_step a hn j,
    rise_succ a n (j + 1), rise_succ a n j]
  ring

theorem minusLaw_upper_decreasing {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk : n ≤ 2 * k + 1) (hkn : k < n) :
    minusLaw a n (k + 1) ≤ minusLaw a n k := by
  induction n, hn using Nat.le_induction generalizing k with
  | base =>
    have heq : k = 1 := by omega
    subst k
    norm_num [minusLaw_two]
  | succ n hn ih =>
    by_cases hcenter : 2 * k = n
    · -- The central bins of the new odd row are reflections of each other.
      have href := minusLaw_reflection ha ha1 (n := n + 1) (by omega) (k := k) (by omega)
      simpa only [show n + 1 - k = k + 1 by omega] using href
    by_cases hedge : k = n
    · rw [minusLaw_outside a (by omega : 2 ≤ n + 1) (by omega : n + 1 ≤ k + 1 + 1),
        minusLaw_outside a (by omega : 2 ≤ n + 1) (by omega : n + 1 ≤ k + 1)]
    -- Both differences on the preceding row lie on its upper half in the minus index.
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    apply sub_nonpos.mp
    rw [minusLaw_diff_step a hn j]
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (stay_nonneg ha ha1 hn (by omega))
        (sub_nonpos.mpr (ih (k := j + 1) (by omega) (by omega))))
      (mul_nonpos_of_nonneg_of_nonpos (rise_nonneg ha ha1 hn (by omega))
        (sub_nonpos.mpr (ih (k := j) (by omega) (by omega))))

/-- Each plus-count bin in the upper half dominates its reflected bin. -/
theorem positiveStartTwoLaw_reflection {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {n k : ℕ} (hn : 2 ≤ n) (hk : n ≤ 2 * k) (hkn : k ≤ n) :
    positiveStartTwoLaw a n (n - k) ≤ positiveStartTwoLaw a n k := by
  simp only [positiveStartTwoLaw, if_pos hkn, if_pos (Nat.sub_le n k)]
  exact minusLaw_reflection ha ha1 hn (by omega)

/-- The plus-count first differences are nonnegative through the lower half,
including the difference between the two central bins of an odd row. -/
theorem positiveStartTwoLaw_firstDiff_nonneg {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hhalf : 2 * k ≤ n + 1) :
    0 ≤ positiveStartTwoLaw a n k - positiveStartTwoLaw a n (k - 1) := by
  have hkn : k ≤ n := by omega
  have hprev : k - 1 ≤ n := by omega
  apply sub_nonneg.mpr
  simp only [positiveStartTwoLaw, if_pos hkn, if_pos hprev,
    show n - (k - 1) = (n - k) + 1 by omega]
  exact minusLaw_upper_decreasing ha ha1 hn (by omega) (by omega)

end Kagey131.PaperD

