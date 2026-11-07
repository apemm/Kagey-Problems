import PaperD.T2_RRTForced

/-!
# Log-concavity from a balanced start

Force the first flip in `RRT.lawQ`, then use flip probability `(1 - a) / 2`.
For `0 ≤ a ≤ 1`, the count law is log-concave and has positive support
exactly on the counts from `1` through `n - 1` at time `n ≥ 2`.
-/

namespace Kagey131.PaperD

/-- The determinant of three consecutive entries after an affine update. -/
theorem balanced_det_identity (A B d u v w z : ℝ) :
    (A * w + B * v) ^ 2 - ((A + d) * v + (B - d) * u) * ((A - d) * z + (B + d) * w) =
      (A ^ 2 - d ^ 2) * (w ^ 2 - v * z) + (B ^ 2 - d ^ 2) * (v ^ 2 - u * w) +
        (A - d) * (B - d) * (w * v - u * z) + d ^ 2 * (w - v) ^ 2 := by
  ring

/-- Two adjacent log-concavity inequalities give the cross inequality when the middle
entries are positive. -/
theorem cross_gap_of_adjacent {u v w z : ℝ} (hv : 0 < v) (hw : 0 < w) (hz : 0 ≤ z)
    (hleft : u * w ≤ v ^ 2) (hright : v * z ≤ w ^ 2) : u * z ≤ w * v := by
  apply le_of_mul_le_mul_right _ (mul_pos hv hw)
  calc
    u * z * (v * w) = (u * w) * (v * z) := by ring
    _ ≤ v ^ 2 * w ^ 2 := mul_le_mul hleft hright (mul_nonneg hv.le hz) (sq_nonneg v)
    _ = w * v * (v * w) := by ring

/-- The affine update preserves the adjacent inequality at an interior count. -/
theorem balanced_det_nonneg {A B d u v w z : ℝ} (hd : 0 ≤ d) (hA : d ≤ A) (hB : d ≤ B)
    (hleft : u * w ≤ v ^ 2) (hright : v * z ≤ w ^ 2) (hcross : u * z ≤ w * v) :
    ((A + d) * v + (B - d) * u) * ((A - d) * z + (B + d) * w) ≤ (A * w + B * v) ^ 2 := by
  apply sub_nonneg.mp
  rw [balanced_det_identity]
  have hAA : 0 ≤ A ^ 2 - d ^ 2 := by
    rw [show A ^ 2 - d ^ 2 = (A - d) * (A + d) by ring]
    exact mul_nonneg (sub_nonneg.mpr hA) (add_nonneg (hd.trans hA) hd)
  have hBB : 0 ≤ B ^ 2 - d ^ 2 := by
    rw [show B ^ 2 - d ^ 2 = (B - d) * (B + d) by ring]
    exact mul_nonneg (sub_nonneg.mpr hB) (add_nonneg (hd.trans hB) hd)
  exact add_nonneg
    (add_nonneg
      (add_nonneg (mul_nonneg hAA (sub_nonneg.mpr hright))
        (mul_nonneg hBB (sub_nonneg.mpr hleft)))
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB))
        (sub_nonneg.mpr hcross)))
    (mul_nonneg (sq_nonneg d) (sq_nonneg (w - v)))

/-- Adjacent log-concavity on natural count indices, including the left edge at count `1`. -/
def BalancedLogConcave (f : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, f k * f (k + 2) ≤ f (k + 1) ^ 2

/-- The support and adjacent inequalities used in the balanced-start induction. -/
structure BalancedRow (n : ℕ) (f : ℕ → ℝ) : Prop where
  zero_outside : ∀ k, k = 0 ∨ n ≤ k → f k = 0
  pos_inside : ∀ k, 1 ≤ k → k < n → 0 < f k
  logConcave : BalancedLogConcave f

theorem BalancedRow.nonneg {n : ℕ} {f : ℕ → ℝ} (hf : BalancedRow n f) (k : ℕ) :
    0 ≤ f k := by
  by_cases hk : 1 ≤ k ∧ k < n
  · exact (hf.pos_inside k hk.1 hk.2).le
  · rw [hf.zero_outside k (by omega)]

noncomputable def balancedUp (a : ℝ) (n k : ℕ) : ℝ :=
  (1 - a) / 2 + (a / n) * k

theorem balancedUp_eq (a : ℝ) (n k : ℕ) :
    balancedUp a n k = upProb ((1 - a) / 2) n k := by
  unfold balancedUp upProb
  simp only [div_eq_mul_inv]
  ring

theorem balancedUp_succ (a : ℝ) (n k : ℕ) :
    balancedUp a n (k + 1) = balancedUp a n k + a / (n : ℝ) := by
  simp only [balancedUp, Nat.cast_add, Nat.cast_one]
  ring

theorem balancedStay_eq (a : ℝ) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    1 - balancedUp a n k = (1 - a) / 2 + (a / n) * ((n : ℝ) - k) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold balancedUp
  field_simp
  ring

theorem balancedUp_ge_step {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n k : ℕ}
    (hk : 1 ≤ k) : a / (n : ℝ) ≤ balancedUp a n k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_left hkR (div_nonneg ha0 (Nat.cast_nonneg n))
  rw [mul_one] at hmul
  unfold balancedUp
  linarith

theorem balancedStay_ge_step {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n k : ℕ}
    (hk : k < n) : a / (n : ℝ) ≤ 1 - balancedUp a n k := by
  have hkR : (k : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hk)
  have hmul := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ n - (k : ℝ) by linarith)
    (div_nonneg ha0 (Nat.cast_nonneg n))
  rw [mul_one] at hmul
  rw [balancedStay_eq a (by omega)]
  linarith

theorem balancedUp_pos {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n k : ℕ}
    (hn : 0 < n) (hk : 1 ≤ k) : 0 < balancedUp a n k := by
  rcases ha0.eq_or_lt with rfl | ha
  · norm_num [balancedUp]
  · exact (div_pos ha (Nat.cast_pos.mpr hn)).trans_le (balancedUp_ge_step ha0 ha1 hk)

theorem balancedStay_pos {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n k : ℕ}
    (hk : k < n) : 0 < 1 - balancedUp a n k := by
  rcases ha0.eq_or_lt with rfl | ha
  · norm_num [balancedUp]
  · have hn : 0 < n := by omega
    exact (div_pos ha (Nat.cast_pos.mpr hn)).trans_le (balancedStay_ge_step ha0 ha1 hk)

/-- The stay-or-rise update from time `n` to time `n + 1`. -/
noncomputable def balancedStartStep (a : ℝ) (n : ℕ) (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0 * (1 - balancedUp a n 0)
  | k + 1 => f (k + 1) * (1 - balancedUp a n (k + 1)) + f k * balancedUp a n k

theorem balancedStartStep_zero_outside {a : ℝ} {n : ℕ} {f : ℕ → ℝ}
    (hf : BalancedRow n f) (k : ℕ) (hk : k = 0 ∨ n + 1 ≤ k) :
    balancedStartStep a n f k = 0 := by
  cases k with
  | zero => simp [balancedStartStep, hf.zero_outside 0 (Or.inl rfl)]
  | succ k =>
    simp [balancedStartStep, hf.zero_outside (k + 1) (by omega), hf.zero_outside k (by omega)]

theorem balancedStartStep_pos_inside {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) {f : ℕ → ℝ} (hf : BalancedRow n f)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1) : 0 < balancedStartStep a n f k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [balancedStartStep]
  by_cases hj : j + 1 < n
  · have hstay := mul_pos (hf.pos_inside (j + 1) hk hj) (balancedStay_pos ha0 ha1 hj)
    have hup : 0 ≤ f j * balancedUp a n j := by
      by_cases hj0 : j = 0
      · simp [hf.zero_outside j (Or.inl hj0)]
      · exact mul_nonneg (hf.nonneg j) (balancedUp_pos ha0 ha1 (by omega) (by omega)).le
    exact add_pos_of_pos_of_nonneg hstay hup
  · rw [hf.zero_outside (j + 1) (by omega), zero_mul, zero_add]
    exact mul_pos (hf.pos_inside j (by omega) (by omega))
      (balancedUp_pos ha0 ha1 (by omega) (by omega))

/-- An update preserves interval support and log-concavity for `0 ≤ a ≤ 1`. -/
theorem balancedStartStep_preserves {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) {f : ℕ → ℝ} (hf : BalancedRow n f) :
    BalancedRow (n + 1) (balancedStartStep a n f) := by
  refine ⟨balancedStartStep_zero_outside hf, balancedStartStep_pos_inside ha0 ha1 hn hf, ?_⟩
  intro k
  cases k with
  | zero =>
    rw [balancedStartStep_zero_outside hf 0 (Or.inl rfl), zero_mul]
    exact sq_nonneg _
  | succ j =>
    by_cases hj : j + 2 < n
    · let A := 1 - balancedUp a n (j + 2)
      let B := balancedUp a n (j + 1)
      let d := a / (n : ℝ)
      have hprevA : 1 - balancedUp a n (j + 1) = A + d := by
        change 1 - balancedUp a n (j + 1) = 1 - balancedUp a n (j + 1 + 1) + d
        rw [balancedUp_succ a n (j + 1)]
        dsimp only [d]
        ring
      have hprevB : balancedUp a n j = B - d := by
        change balancedUp a n j = balancedUp a n (j + 1) - d
        rw [balancedUp_succ a n j]
        dsimp only [d]
        ring
      have hnextA : 1 - balancedUp a n (j + 3) = A - d := by
        change 1 - balancedUp a n (j + 2 + 1) = 1 - balancedUp a n (j + 2) - d
        rw [balancedUp_succ a n (j + 2)]
        dsimp only [d]
        ring
      have hnextB : balancedUp a n (j + 2) = B + d := balancedUp_succ a n (j + 1)
      have hprev : balancedStartStep a n f (j + 1) = (A + d) * f (j + 1) + (B - d) * f j := by
        rw [balancedStartStep, hprevA, hprevB]
        ac_rfl
      have hcenter : balancedStartStep a n f (j + 2) = A * f (j + 2) + B * f (j + 1) := by
        change f (j + 2) * A + f (j + 1) * B = _
        ac_rfl
      have hnext : balancedStartStep a n f (j + 3) = (A - d) * f (j + 3) + (B + d) * f (j + 2) := by
        change f (j + 3) * (1 - balancedUp a n (j + 3)) + f (j + 2) * balancedUp a n (j + 2) = _
        rw [hnextA, hnextB]
        ac_rfl
      have hcross : f j * f (j + 3) ≤ f (j + 2) * f (j + 1) :=
        cross_gap_of_adjacent (hf.pos_inside (j + 1) (by omega) (by omega))
          (hf.pos_inside (j + 2) (by omega) hj) (hf.nonneg (j + 3))
          (hf.logConcave j) (hf.logConcave (j + 1))
      change balancedStartStep a n f (j + 1) * balancedStartStep a n f (j + 3) ≤
        balancedStartStep a n f (j + 2) ^ 2
      rw [hprev, hcenter, hnext]
      exact balanced_det_nonneg (div_nonneg ha0 (Nat.cast_nonneg n))
        (balancedStay_ge_step ha0 ha1 hj) (balancedUp_ge_step ha0 ha1 (by omega))
        (hf.logConcave j) (hf.logConcave (j + 1)) hcross
    · rw [balancedStartStep_zero_outside hf (j + 1 + 2) (by omega), mul_zero]
      exact sq_nonneg _

/-- The count law with an initial `+` and a forced `-`, followed by flips of probability
`(1 - a) / 2`. The time index counts both initial steps. -/
noncomputable def balancedStartLaw (a : ℝ) : ℕ → ℕ → ℝ :=
  RRT.lawQ (fun j => if j = 0 then 1 else (1 - a) / 2)

theorem balancedStartLaw_two (a : ℝ) (k : ℕ) :
    balancedStartLaw a 2 k = if k = 1 then 1 else 0 := by
  cases k with
  | zero => norm_num [balancedStartLaw, RRT.lawQ, upProb]
  | succ k => cases k <;> norm_num [balancedStartLaw, RRT.lawQ, upProb]

theorem balancedStartLaw_succ (a : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    balancedStartLaw a (n + 1) = balancedStartStep a n (balancedStartLaw a n) := by
  have hindex : n - 1 ≠ 0 := by omega
  funext k
  cases k with
  | zero =>
    unfold balancedStartLaw
    rw [RRT.lawQ_succ_zero _ (by omega)]
    simp [balancedStartStep, hindex, balancedUp_eq]
  | succ k =>
    unfold balancedStartLaw
    rw [RRT.lawQ_succ_succ _ (by omega)]
    simp [balancedStartStep, hindex, balancedUp_eq]

/-- Every balanced-start row from time `2` onward has interval support and is log-concave. -/
theorem balancedStartLaw_row {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n : ℕ} (hn : 2 ≤ n) :
    BalancedRow n (balancedStartLaw a n) := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp [balancedStartLaw_two, show k ≠ 1 by omega]
    · intro k hk hkn
      simp [balancedStartLaw_two, show k = 1 by omega]
    · intro k
      rw [balancedStartLaw_two a (k + 2), if_neg (by omega), mul_zero]
      exact sq_nonneg _
  | succ n hn ih =>
    rw [balancedStartLaw_succ a hn]
    exact balancedStartStep_preserves ha0 ha1 hn ih

theorem balancedStartLaw_logConcave {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) : BalancedLogConcave (balancedStartLaw a n) :=
  (balancedStartLaw_row ha0 ha1 hn).logConcave

end Kagey131.PaperD

