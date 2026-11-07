import PaperD.EJPModelFiniteMomentsGronwall

/-!
# Uniform bounds for every scaled even moment of the actual finite ERW

The all-order induction uses the actual raw-moment recurrence. Every remainder
has even degree at most two below the leading degree. After n^a scaling its
contribution is summable, since 2a>1.
-/

namespace Kagey131.PaperD.ModelFiniteMoments

open Finset RRT

theorem pow_le_one_add_pow {x : ℝ} (hx : 0 ≤ x) {i j : ℕ} (hij : i ≤ j) :
    x ^ i ≤ 1 + x ^ j := by
  by_cases h : x ≤ 1
  · have h1 := pow_le_one₀ hx h (n := i)
    linarith [pow_nonneg hx j]
  · have h1 := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge h)) hij
    linarith

theorem even_power_le_one_add {x : ℝ} {i m : ℕ} (hi : Even i) (him : i ≤ 2 * m) :
    x ^ i ≤ 1 + x ^ (2 * m) := by
  have h0 := hi.pow_nonneg x
  have h2 : 0 ≤ x ^ (2 * m) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
  calc
    _ = |x| ^ i := by rw [← abs_pow, abs_of_nonneg h0]
    _ ≤ 1 + |x| ^ (2 * m) := pow_le_one_add_pow (abs_nonneg x) him
    _ = _ := by rw [← abs_pow, abs_of_nonneg h2]

/-- Every lower even moment is dominated by one plus the nearest higher even moment. -/
theorem rawMoment_even_le_one_add {a : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1)
    {n i m : ℕ} (hn : 1 ≤ n) (hi : Even i) (him : i ≤ 2 * m) :
    rawMoment a n i ≤ 1 + rawMoment a n (2 * m) := by
  have hmass : (∑ b ∈ range n, law ((1 - a) / 2) n b) = 1 := by
    simpa only [lawQ_const] using lawQ_mass (fun _ => (1 - a) / 2) hn
  rw [rawMoment_eq_law, rawMoment_eq_law]
  calc
    _ ≤ ∑ b ∈ range n, law ((1 - a) / 2) n b * (1 + ((n : ℝ) - 2 * b) ^ (2 * m)) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (even_power_le_one_add hi him)
        (law_nonneg (by linarith) (by linarith) n b)
    _ = _ := by simp_rw [mul_add, mul_one]; rw [Finset.sum_add_distrib, hmass]

theorem rawMoment_succ_single (a : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    rawMoment a (n + 1) k = ∑ j ∈ range (k + 1), (k.choose j : ℝ) *
      (if Even j then rawMoment a n (k - j) else a / n * rawMoment a n (k - j + 1)) := by
  rw [rawMoment_succ a hn, Finset.sum_filter, Finset.sum_filter, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : Even j <;> simp [hj] <;> ring

/-- Removing j=0 and j=1 exposes the exact leading coefficient 1+ak/n. -/
theorem rawMoment_succ_remainder (a : ℝ) {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) :
    rawMoment a (n + 1) k = (1 + a * k / n) * rawMoment a n k +
      ∑ j ∈ range (k - 1), (k.choose (j + 2) : ℝ) *
        (if Even (j + 2) then rawMoment a n (k - (j + 2))
          else a / n * rawMoment a n (k - (j + 2) + 1)) := by
  rw [rawMoment_succ_single a hn]
  let f : ℕ → ℝ := fun j => (k.choose j : ℝ) *
    (if Even j then rawMoment a n (k - j) else a / n * rawMoment a n (k - j + 1))
  have hsum : (∑ j ∈ range (k + 1), f j) =
      (∑ j ∈ range (k - 1), f (j + 2)) + f 1 + f 0 := by
    rw [show k + 1 = (k - 1) + 1 + 1 by omega,
      Finset.sum_range_succ', Finset.sum_range_succ']
  change (∑ j ∈ range (k + 1), f j) = _
  rw [hsum]
  have hk1 : k - 1 + 1 = k := by omega
  have he0 : Even (0 : ℕ) := ⟨0, by omega⟩
  simp only [f, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    he0, Nat.not_even_one, if_true, if_false, Nat.sub_zero, hk1, one_mul]
  ring

noncomputable def remainderCoeff (k : ℕ) : ℝ :=
  ∑ j ∈ range (k - 1), (k.choose (j + 2) : ℝ)

theorem remainderCoeff_nonneg (k : ℕ) : 0 ≤ remainderCoeff k :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem rawMoment_even_succ_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {n m : ℕ} (hn : 1 ≤ n) :
    rawMoment a (n + 1) (2 * (m + 1)) ≤
      (1 + a * (2 * (m + 1) : ℕ) / n) * rawMoment a n (2 * (m + 1)) +
        remainderCoeff (2 * (m + 1)) * (1 + a) * (1 + rawMoment a n (2 * m)) := by
  let k := 2 * (m + 1)
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkEven : k % 2 = 0 := by dsimp [k]; omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have haN : 0 ≤ a / n := div_nonneg ha (by positivity)
  have haN1 : a / n ≤ a := (div_le_iff₀ (by positivity : (0 : ℝ) < n)).2 (by nlinarith)
  have hprev := rawMoment_even_nonneg (by linarith : -1 ≤ a) ha1 n m
  rw [rawMoment_succ_remainder a hn hk]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ j ∈ range (k - 1), (k.choose (j + 2) : ℝ) *
        ((1 + a) * (1 + rawMoment a n (2 * m))) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjlt := Finset.mem_range.mp hj
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      by_cases he : Even (j + 2)
      · rw [if_pos he]
        have hemod := Nat.even_iff.mp he
        have hexp : Even (k - (j + 2)) := Nat.even_iff.mpr (by omega)
        have hlow : k - (j + 2) ≤ 2 * m := by dsimp [k] at *; omega
        have hh := rawMoment_even_le_one_add (by linarith : -1 ≤ a) ha1 hn hexp hlow
        nlinarith [mul_nonneg ha (show 0 ≤ 1 + rawMoment a n (2 * m) by linarith)]
      · rw [if_neg he]
        have hemod : (j + 2) % 2 = 1 := by
          have := Nat.mod_two_eq_zero_or_one (j + 2)
          rw [Nat.even_iff] at he
          omega
        have hexp : Even (k - (j + 2) + 1) := Nat.even_iff.mpr (by omega)
        have hlow : k - (j + 2) + 1 ≤ 2 * m := by dsimp [k] at *; omega
        have hh := rawMoment_even_le_one_add (by linarith : -1 ≤ a) ha1 hn hexp hlow
        exact (mul_le_mul_of_nonneg_left hh haN).trans
          (mul_le_mul_of_nonneg_right (by linarith : a / n ≤ 1 + a) (by linarith))
    _ = _ := by rw [← Finset.sum_mul]; dsimp [remainderCoeff, k]; ring

/-- Every raw even moment grows at most at its natural n^(2am) rate. -/
theorem rawMoment_even_uniform {a : ℝ} (ha : 1 / 2 < a) (ha1 : a ≤ 1) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, 1 ≤ n → rawMoment a n (2 * m) ≤ C * (n : ℝ) ^ (a * (2 * m : ℕ)) := by
  induction m with
  | zero =>
    refine ⟨1, zero_lt_one, ?_⟩
    intro n hn
    simp [rawMoment_zero a hn]
  | succ m ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    let p : ℝ := a * (2 * (m + 1) : ℕ)
    let q : ℝ := a * (2 * m : ℕ)
    let B := remainderCoeff (2 * (m + 1)) * (1 + a) * (1 + C)
    have ha0 : 0 ≤ a := by linarith
    have hp : 1 ≤ p := by dsimp [p]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hgap : q - p < -1 := by dsimp [q, p]; push_cast; nlinarith
    have hB : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg (mul_nonneg (remainderCoeff_nonneg _) (by linarith)) (by linarith)
    apply polynomial_recurrence_bound hp hgap hB
      (fun n _ => rawMoment_even_nonneg (by linarith) ha1 n (m + 1))
    intro n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : 1 ≤ (n : ℝ) ^ q := Real.one_le_rpow hnR (by dsimp [q]; positivity)
    have hlow : 1 + rawMoment a n (2 * m) ≤ (1 + C) * (n : ℝ) ^ q := by
      have h := hbound n hn
      change rawMoment a n (2 * m) ≤ C * (n : ℝ) ^ q at h
      nlinarith
    have hh := rawMoment_even_succ_le ha0 ha1 (m := m) hn
    have hmul := mul_le_mul_of_nonneg_left hlow
      (mul_nonneg (remainderCoeff_nonneg (2 * (m + 1))) (by linarith : 0 ≤ 1 + a))
    dsimp [p, B]
    nlinarith only [hh, hmul]

/-- The per-order interface for weak-limit moment integrability and truncation. -/
theorem scaledMoment_even_uniform {a : ℝ} (ha : 1 / 2 < a) (ha1 : a ≤ 1) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, 1 ≤ n → scaledMoment a n (2 * m) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := rawMoment_even_uniform ha ha1 m
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [scaledMoment, ← Real.rpow_mul_natCast hnR.le]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hnR _)).2 (hbound n hn)

end Kagey131.PaperD.ModelFiniteMoments
