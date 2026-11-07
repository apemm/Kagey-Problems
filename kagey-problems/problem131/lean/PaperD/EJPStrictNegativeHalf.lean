import PaperD.Modes.BiasIntervalFinite

/-!
# Strict reflection and first differences for the positive fixed start

For `q = 1` and `0 < ε < 1 / 2`, each upper-half bin has greater mass than
its reflection. The row increases strictly through its lower half, including
the step between the two central bins of an odd row.
-/

namespace Kagey131.PaperD.BiasedModes

theorem skew_one_upper_pos {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) {k : ℤ} (hk : (n : ℤ) < 2 * k) (hkn : k ≤ n) :
    0 < skew ε 1 n k := by
  induction n, hn using Nat.le_induction generalizing k with
  | base =>
    rw [show k = 1 by omega, skew, mass_one, mass_one]
    norm_num
  | succ n hn ih =>
    rw [skew_succ ε 1 hn]
    by_cases houter : (n : ℤ) < k
    · -- At the outer endpoint only the parent at `k - 1` contributes.
      rw [skew_gt ε 1 hn houter, mul_zero, zero_add]
      exact mul_pos (hε.trans_le (rP_nonneg hεhalf (by omega)))
        (ih (by omega) (by omega))
    · -- The parent at `k` is strictly above center. The other can be central.
      have hstay : 0 < 1 - rP ε n k := hε.trans_le (one_sub_rP hεhalf (by omega))
      have hmove : 0 ≤ rP ε n (k - 1) := hε.le.trans (rP_nonneg hεhalf (by omega))
      exact add_pos_of_pos_of_nonneg (mul_pos hstay (ih (by omega) (by omega)))
        (mul_nonneg hmove
          (skew_upper_nonneg hε.le (by linarith) (by norm_num) hn (by omega)))

/-- Under `q = 1`, every bin strictly above center dominates its reflection. -/
theorem mass_one_upper_dominates_strict {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) {k : ℤ} (hk : (n : ℤ) < 2 * k) (hkn : k ≤ n) :
    mass ε 1 n (n - k) < mass ε 1 n k := by
  have hreflect : mass ε 1 n (n - k) = mass ε (1 - 1) n k := by
    simpa only [sub_sub_cancel] using mass_reflect ε (1 - 1) n k
  rw [hreflect]
  exact sub_pos.mp (skew_one_upper_pos hε hεhalf hn hk hkn)

/-- Under `q = 1`, the step from bin `k - 1` to bin `k` is strictly positive
through the lower half, including the central step of odd rows. -/
theorem mass_one_negative_half_diff_pos {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    {n : ℕ} {k : ℤ} (hk : 1 ≤ k) (hkn : 2 * k ≤ (n : ℤ) + 1) :
    0 < mass ε 1 n k - mass ε 1 n (k - 1) := by
  suffices h : 0 < diff ε 1 n (k - 1) by
    simpa only [diff, sub_add_cancel] using h
  have hn : 1 ≤ n := by omega
  induction n, hn using Nat.le_induction generalizing k with
  | base =>
    rw [show k = 1 by omega]
    norm_num [diff, mass_one, mass_zero ε 1 (n := 1) le_rfl]
  | succ n hn ih =>
    by_cases hcenter : 2 * k = (n : ℤ) + 2
    · -- In the new odd row, the two central bins are reflections.
      have h := mass_one_upper_dominates_strict hε hεhalf (n := n + 1) (k := k)
        (by omega) (by omega) (by omega)
      rw [show ((n + 1 : ℕ) : ℤ) - k = k - 1 by omega] at h
      unfold diff
      rw [sub_add_cancel]
      exact sub_pos.mpr h
    · rw [diff_succ ε 1 hn, sub_add_cancel]
      have hstay : 0 < 1 - rP ε n k := hε.trans_le (one_sub_rP hεhalf (by omega))
      have hcurr := ih hk (by omega)
      by_cases hfirst : k = 1
      · -- The missing difference is zero because both masses are zero.
        subst k
        have hmissing : diff ε 1 n (-1) = 0 := by
          norm_num [diff, mass_zero ε 1 hn, mass_neg ε 1 hn (k := -1) (by decide)]
        simpa only [Int.reduceSub, hmissing, mul_zero, zero_add] using mul_pos hstay hcurr
      · have hmove : 0 < rP ε n (k - 1 - 1) := hε.trans_le (rP_nonneg hεhalf (by omega))
        exact add_pos (mul_pos hmove (ih (by omega : 1 ≤ k - 1) (by omega)))
          (mul_pos hstay hcurr)

end Kagey131.PaperD.BiasedModes
