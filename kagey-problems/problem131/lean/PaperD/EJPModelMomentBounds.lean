import Mathlib

/-!
# Bounds from the normalized moment recurrence

The recurrence itself is kept explicit here. Its positive coefficients give
an exponential bound with base `(2*a-1)⁻¹`, without a separate growth assumption.
-/

open Finset

namespace Kagey131.PaperD.ModelMoments

noncomputable def momentParity (a : ℝ) (n : ℕ) : ℝ := if Even n then 1 else a

structure MomentRecurrence (a : ℝ) (m : ℕ → ℝ) : Prop where
  zero : m 0 = 1
  one : m 1 = 1
  step : ∀ n, 2 ≤ n → (a * n - momentParity a n) * m n =
    ∑ j ∈ Ioo 0 n, momentParity a j * m j * m (n-j)

theorem momentParity_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ momentParity a n := by
  unfold momentParity
  split_ifs <;> positivity

theorem momentParity_le_one {a : ℝ} (ha : a ≤ 1) (n : ℕ) :
    momentParity a n ≤ 1 := by
  unfold momentParity
  split_ifs <;> linarith

theorem moment_denominator_lower {a : ℝ} (ha : a ≤ 1) {n : ℕ} (hn : 2 ≤ n) :
    (2*a-1) * (n-1 : ℝ) ≤ a*n - momentParity a n := by
  have hc := momentParity_le_one ha n
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (1-a) * (n-2 : ℝ) := mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem moment_denominator_pos {a : ℝ} (ha : 1/2 < a) (ha1 : a ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) : 0 < a*n - momentParity a n := by
  have hl := moment_denominator_lower ha1 hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (2*a-1) * (n-1 : ℝ) := mul_pos (by linarith) (by linarith)
  linarith

theorem normalized_moment_nonneg {a : ℝ} {m : ℕ → ℝ}
    (ha : 1/2 < a) (ha1 : a ≤ 1) (hm : MomentRecurrence a m) (n : ℕ) :
    0 ≤ m n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n = 0
    · subst n; rw [hm.zero]; norm_num
    by_cases h1 : n = 1
    · subst n; rw [hm.one]; norm_num
    have hn : 2 ≤ n := by omega
    have hd := moment_denominator_pos ha ha1 hn
    have hs : 0 ≤ ∑ j ∈ Ioo 0 n, momentParity a j * m j * m (n-j) := by
      apply sum_nonneg
      intro j hj
      have hj' := mem_Ioo.mp hj
      exact mul_nonneg (mul_nonneg (momentParity_nonneg (by linarith) j)
        (ih j hj'.2)) (ih (n-j) (by omega))
    rw [← hm.step n hn] at hs
    nlinarith

theorem normalized_moment_le {a : ℝ} {m : ℕ → ℝ}
    (ha : 1/2 < a) (ha1 : a ≤ 1) (hm : MomentRecurrence a m)
    {n : ℕ} (hn : 1 ≤ n) : m n ≤ (2*a-1)⁻¹ ^ (n-1) := by
  have hb : 0 < 2*a-1 := by linarith
  have hR : 0 ≤ (2*a-1)⁻¹ := inv_nonneg.mpr hb.le
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n; simp [hm.one]
    have hn2 : 2 ≤ n := by omega
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hm0 := normalized_moment_nonneg ha ha1 hm n
    have hs : (a*n - momentParity a n) * m n ≤
        (n-1 : ℝ) * ((2*a-1)⁻¹ ^ (n-2)) := by
      rw [hm.step n hn2]
      calc
        _ ≤ ∑ j ∈ Ioo 0 n, (2*a-1)⁻¹ ^ (n-2) := by
          apply sum_le_sum
          intro j hj
          have hj' := mem_Ioo.mp hj
          have hmn := normalized_moment_nonneg ha ha1 hm (n-j)
          have hmj := normalized_moment_nonneg ha ha1 hm j
          have hleft : momentParity a j * m j ≤ (2*a-1)⁻¹ ^ (j-1) := by
            simpa only [one_mul] using mul_le_mul (momentParity_le_one ha1 j)
              (ih j hj'.2 (by omega)) hmj (by norm_num : (0 : ℝ) ≤ 1)
          have hprod := mul_le_mul hleft (ih (n-j) (by omega) (by omega)) hmn
            (pow_nonneg hR (j-1))
          simpa only [← pow_add, show j-1+(n-j-1) = n-2 by omega] using hprod
        _ = _ := by simp [Nat.card_Ioo, Nat.cast_sub (by omega : 1 ≤ n)]
    have hl := mul_le_mul_of_nonneg_right (moment_denominator_lower ha1 hn2) hm0
    have hbm : (2*a-1) * m n ≤ (2*a-1)⁻¹ ^ (n-2) := by
      nlinarith
    have he : (2*a-1)⁻¹ ^ (n-2) =
        (2*a-1) * ((2*a-1)⁻¹ ^ (n-1)) := by
      rw [show n-1 = (n-2)+1 by omega, pow_succ]
      field_simp
    rw [he] at hbm
    nlinarith

theorem normalized_moment_abs_bound {a : ℝ} {m : ℕ → ℝ}
    (ha : 1/2 < a) (ha1 : a ≤ 1) (hm : MomentRecurrence a m) (n : ℕ) :
    |m n| ≤ (2*a-1)⁻¹ ^ n := by
  have hR : 1 ≤ (2*a-1)⁻¹ := (one_le_inv₀ (by linarith)).mpr (by linarith)
  rw [abs_of_nonneg (normalized_moment_nonneg ha ha1 hm n)]
  by_cases h0 : n = 0
  · subst n; simp [hm.zero]
  exact (normalized_moment_le ha ha1 hm (by omega)).trans
    (pow_le_pow_right₀ hR (by omega))

end Kagey131.PaperD.ModelMoments
