import PaperD.Modes.BiasIntervalFinite
import Mathlib.Tactic.FieldSimp

/-!
# Backward step algebra for strict slopes

The reflection and first-difference recurrences for the positive fixed start
give two backward weighted averages. This file checks their lattice coordinates,
weights, and one-step moments. The stopping arguments and limiting slope
theorems lie outside this formalization.
-/

namespace Kagey131.PaperD.BiasedModes

/-- Reflection coordinate of bin `k` in row `n`. -/
noncomputable def reflectionCoord (n : ℕ) (k : ℤ) : ℝ := 2 * (k : ℝ) - n

/-- Midpoint coordinate of the difference ending at bin `k` in row `n`. -/
noncomputable def firstDiffCoord (n : ℕ) (k : ℤ) : ℝ := 2 * (k : ℝ) - n - 1

theorem reflectionCoord_parents (n : ℕ) (k : ℤ) :
    reflectionCoord n k = reflectionCoord (n + 1) k + 1 ∧
      reflectionCoord n (k - 1) = reflectionCoord (n + 1) k - 1 := by
  constructor <;> simp only [reflectionCoord, Nat.cast_add, Nat.cast_one,
    Int.cast_sub, Int.cast_one] <;> ring

theorem firstDiffCoord_parents (n : ℕ) (k : ℤ) :
    firstDiffCoord n k = firstDiffCoord (n + 1) k + 1 ∧
      firstDiffCoord n (k - 1) = firstDiffCoord (n + 1) k - 1 := by
  constructor <;> simp only [firstDiffCoord, Nat.cast_add, Nat.cast_one,
    Int.cast_sub, Int.cast_one] <;> ring

noncomputable def slopeC (a n : ℝ) : ℝ := 1 - 2 * a / n

theorem slopeC_pos {a n : ℝ} (hn : 0 < n) (h : 2 * a < n) :
    0 < slopeC a n :=
  sub_pos.mpr ((div_lt_iff₀ hn).2 (by simpa using h))

theorem slopeC_eq {a n : ℝ} (hn : n ≠ 0) :
    slopeC a n = (n - 2 * a) / n := by
  unfold slopeC
  field_simp [hn]

noncomputable def centralA (a n z : ℝ) : ℝ := 1 / 2 - a * (z + 1) / (2 * n)

noncomputable def centralB (a n z : ℝ) : ℝ := 1 / 2 + a * (z - 1) / (2 * n)

noncomputable def centralQPlus (a n z : ℝ) : ℝ :=
  centralA a n z * (z + 1) / (z * slopeC a n)

noncomputable def centralQMinus (a n z : ℝ) : ℝ :=
  centralB a n z * (z - 1) / (z * slopeC a n)

theorem central_weighted_sum (a n z : ℝ) (hn : n ≠ 0) :
    centralA a n z * (z + 1) + centralB a n z * (z - 1) = z * slopeC a n := by
  unfold centralA centralB slopeC
  field_simp [hn]
  ring

theorem central_q_sum {a n z : ℝ} (ha : 0 < a) (hn : 4 * a < n) (hz : 0 < z) :
    centralQPlus a n z + centralQMinus a n z = 1 := by
  have hn' : 0 < n := by linarith
  have hc := slopeC_pos hn' (by linarith : 2 * a < n)
  rw [centralQPlus, centralQMinus, ← add_div, central_weighted_sum a n z hn'.ne']
  exact div_self (mul_ne_zero hz.ne' hc.ne')

/-- On the positive integer lattice, `z > 0` gives the hypothesis `1 ≤ z`. -/
theorem central_q_nonneg {a n z : ℝ} (ha : 0 < a) (hn : 4 * a < n) (hz : 1 ≤ z)
    (hband : |z| + 1 < n / a) :
    0 ≤ centralQPlus a n z ∧ 0 ≤ centralQMinus a n z := by
  have hn' : 0 < n := by linarith
  have hz' : 0 ≤ z := by linarith
  have hband' : a * (z + 1) < n := by
    rw [abs_of_nonneg hz'] at hband
    simpa [mul_comm] using (lt_div_iff₀ ha).1 hband
  have hA : 0 ≤ centralA a n z := by
    unfold centralA
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : 0 < 2 * n)).2
    linarith
  have hB : 0 ≤ centralB a n z := by
    unfold centralB
    exact add_nonneg (by norm_num) (div_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hz))
      (by positivity))
  have hden := mul_nonneg hz' (slopeC_pos hn' (by linarith : 2 * a < n)).le
  exact ⟨div_nonneg (mul_nonneg hA (by positivity)) hden,
    div_nonneg (mul_nonneg hB (sub_nonneg.mpr hz)) hden⟩

theorem central_q_minus_at_one (a n : ℝ) : centralQMinus a n 1 = 0 := by
  simp [centralQMinus]

/-- The second moment of the two parent coordinates in the central step. -/
theorem central_q_second_moment {a n z : ℝ} (ha : 0 < a) (hn : 4 * a < n)
    (hz : 0 < z) :
    centralQPlus a n z * (z + 1)^2 + centralQMinus a n z * (z - 1)^2 =
      (n - 4 * a) / (n - 2 * a) * z^2 + (3 * n - 4 * a) / (n - 2 * a) := by
  have hn' : n ≠ 0 := by linarith
  have hden : n - 2 * a ≠ 0 := by linarith
  unfold centralQPlus centralQMinus centralA centralB
  rw [slopeC_eq hn']
  field_simp [hn', hden, hz.ne']
  ring

/-- The fixed-start reflection difference divided by its coordinate. -/
noncomputable def centralSlope (a : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  skew ((1 - a) / 2) 1 n k / reflectionCoord n k

theorem coord_mul_centralSlope (a : ℝ) (n : ℕ) (k : ℤ) :
    reflectionCoord n k * centralSlope a n k = skew ((1 - a) / 2) 1 n k := by
  unfold centralSlope
  by_cases hz : reflectionCoord n k = 0
  · have hk : 2 * k = (n : ℤ) := by
      unfold reflectionCoord at hz
      exact_mod_cast (sub_eq_zero.mp hz)
    rw [hz, zero_mul, skew_center _ _ hk]
  · field_simp [hz]

/-- The central backward average with one step of the product normalizer. -/
theorem centralSlope_succ {a : ℝ} {n : ℕ} (hn : 1 ≤ n) (k : ℤ) :
    let z := reflectionCoord (n + 1) k
    centralSlope a (n + 1) k / slopeC a n =
      centralQPlus a n z * centralSlope a n k +
        centralQMinus a n z * centralSlope a n (k - 1) := by
  let z := reflectionCoord (n + 1) k
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hA : 1 - rP ((1 - a) / 2) n k = centralA a n z := by
    simp only [rP, centralA, z, reflectionCoord, Nat.cast_add, Nat.cast_one]
    field_simp [hn']
    ring
  have hB : rP ((1 - a) / 2) n (k - 1) = centralB a n z := by
    simp only [rP, centralB, z, reflectionCoord, Nat.cast_add, Nat.cast_one,
      Int.cast_sub, Int.cast_one]
    field_simp [hn']
    ring
  obtain ⟨hplus, hminus⟩ := reflectionCoord_parents n k
  have hp : (z + 1) * centralSlope a n k = skew ((1 - a) / 2) 1 n k := by
    rw [← hplus, coord_mul_centralSlope]
  have hm : (z - 1) * centralSlope a n (k - 1) = skew ((1 - a) / 2) 1 n (k - 1) := by
    rw [← hminus, coord_mul_centralSlope]
  change skew ((1 - a) / 2) 1 (n + 1) k / z / slopeC a n = _
  rw [skew_succ _ _ hn, hA, hB, ← hp, ← hm, div_div]
  unfold centralQPlus centralQMinus
  ring

noncomputable def firstDiffA (a n k : ℝ) : ℝ := (1 + a) / 2 - a * k / n

noncomputable def firstDiffB (a n k : ℝ) : ℝ := (1 - a) / 2 + a * (k - 2) / n

theorem firstDiffA_eq (a : ℝ) (n : ℕ) (k : ℤ) :
    firstDiffA a n k = 1 - rP ((1 - a) / 2) n k := by
  unfold rP firstDiffA
  ring

theorem firstDiffB_eq (a : ℝ) (n : ℕ) (k : ℤ) :
    firstDiffB a n k = rP ((1 - a) / 2) n (k - 2) := by
  simp only [rP, firstDiffB, Int.cast_sub, Int.cast_ofNat]
  ring

theorem firstDiff_weight_sum (a n k : ℝ) :
    firstDiffA a n k + firstDiffB a n k = slopeC a n := by
  unfold firstDiffA firstDiffB slopeC
  ring

/-- The two normalized first-difference weights sum to one. -/
theorem firstDiff_q_sum {a n : ℝ} (ha : 0 < a) (hn : 3 * a < n) (k : ℝ) :
    firstDiffA a n k / slopeC a n + firstDiffB a n k / slopeC a n = 1 := by
  have hc := slopeC_pos (by linarith : 0 < n) (by linarith : 2 * a < n)
  rw [← add_div, firstDiff_weight_sum, div_self hc.ne']

/-- Both normalized first-difference weights are positive when both parent
differences are in the interior. -/
theorem firstDiff_q_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {n : ℕ}
    (hrow : 3 * a < (n : ℝ)) {k : ℤ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    0 < firstDiffA a n k / slopeC a n ∧ 0 < firstDiffB a n k / slopeC a n := by
  have hε : 0 < (1 - a) / 2 := by linarith
  have hεhalf : (1 - a) / 2 < 1 / 2 := by linarith
  have hc := slopeC_pos (by linarith : 0 < (n : ℝ)) (by linarith : 2 * a < (n : ℝ))
  rw [firstDiffA_eq, firstDiffB_eq]
  exact ⟨div_pos (hε.trans_le (one_sub_rP hεhalf hkn)) hc,
    div_pos (hε.trans_le (rP_nonneg hεhalf (by omega))) hc⟩

/-- The first moment of the two parent coordinates, with child coordinate
`z = 2 * k - n - 2`. -/
theorem firstDiff_q_mean {a : ℝ} {n : ℕ} (ha : 0 < a) (hn : 3 * a < (n : ℝ))
    (k : ℤ) :
    firstDiffA a n k / slopeC a n * firstDiffCoord n k +
      firstDiffB a n k / slopeC a n * firstDiffCoord n (k - 1) =
        firstDiffCoord (n + 1) k * (n - 3 * a) / (n - 2 * a) := by
  have hn' : (n : ℝ) ≠ 0 := by linarith
  have hden : (n : ℝ) - 2 * a ≠ 0 := by linarith
  obtain ⟨hplus, hminus⟩ := firstDiffCoord_parents n k
  rw [hplus, hminus, slopeC_eq hn']
  simp only [firstDiffA, firstDiffB, firstDiffCoord, Nat.cast_add, Nat.cast_one]
  field_simp [hn', hden]
  ring

/-- The first-difference backward average with one step of the product
normalizer. The existing `diff` is indexed by the left bin. -/
theorem firstDiff_succ {a : ℝ} {n : ℕ} (hn : 1 ≤ n) (k : ℤ) :
    diff ((1 - a) / 2) 1 (n + 1) (k - 1) / slopeC a n =
      firstDiffA a n k / slopeC a n * diff ((1 - a) / 2) 1 n (k - 1) +
        firstDiffB a n k / slopeC a n * diff ((1 - a) / 2) 1 n (k - 2) := by
  rw [diff_succ _ _ hn, sub_add_cancel, show k - 1 - 1 = k - 2 by ring,
    ← firstDiffA_eq, ← firstDiffB_eq]
  ring

end Kagey131.PaperD.BiasedModes

