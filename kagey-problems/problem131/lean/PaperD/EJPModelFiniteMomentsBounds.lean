import PaperD.EJPModelFiniteMoments
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Mean and second-moment bounds for the actual finite plus-start ERW

The finite moments are those of `RRT.lawQ`, not an abstract moment sequence.
The scaled second-moment bound is uniform in time and is at most four on the
analytic transition band. Passing moments to a limiting law is a separate step.
-/

namespace Kagey131.PaperD.ModelFiniteMoments

open Finset RRT

theorem rawMoment_first_succ (a : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    rawMoment a (n + 1) 1 = (1 + a / n) * rawMoment a n 1 := by
  have h := rawMoment_succ a hn 1
  norm_num [Finset.sum_filter, Finset.sum_range_succ] at h
  linarith

theorem rawMoment_second_succ (a : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    rawMoment a (n + 1) 2 = (1 + 2 * a / n) * rawMoment a n 2 + 1 := by
  have h := rawMoment_succ a hn 2
  norm_num [Finset.sum_filter, Finset.sum_range_succ, rawMoment_zero a hn] at h
  calc
    _ = rawMoment a n 2 + 1 + a / n * (2 * rawMoment a n 2) := h
    _ = _ := by ring

/-- The deterministic ERW growth product, from time one through time n. -/
noncomputable def growth (a : ℝ) (n : ℕ) : ℝ := ∏ j ∈ Ico 1 n, (1 + a / j)

@[simp] theorem growth_one (a : ℝ) : growth a 1 = 1 := by simp [growth]

theorem growth_succ (a : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    growth a (n + 1) = growth a n * (1 + a / n) := by
  exact Finset.prod_Ico_succ_top hn _

/-- The exact first mean of the actual conditional plus-start walk. -/
theorem rawMoment_first (a : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    rawMoment a n 1 = growth a n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [rawMoment_first_succ a hn, growth_succ a hn, ih]; ring

theorem growth_pos {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : 0 < growth a n := by
  apply Finset.prod_pos
  intro j _
  positivity

/-- A division-free exact second-moment identity, including a=1/2. -/
theorem rawMoment_second_identity (a : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (2 * a - 1) * rawMoment a n 2 = 2 * a * growth (2 * a) n - n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [rawMoment_second_succ a hn, growth_succ (2 * a) hn]
    calc
      (2 * a - 1) * ((1 + 2 * a / n) * rawMoment a n 2 + 1) =
          (1 + 2 * a / n) * ((2 * a - 1) * rawMoment a n 2) + (2 * a - 1) := by ring
      _ = (1 + 2 * a / n) * (2 * a * growth (2 * a) n - n) + (2 * a - 1) := by rw [ih]
      _ = 2 * a * (growth (2 * a) n * (1 + 2 * a / n)) - (n + 1 : ℕ) := by
        push_cast
        field_simp
        ring

theorem rawMoment_second_exact {a : ℝ} (ha : 2 * a - 1 ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    rawMoment a n 2 = (2 * a * growth (2 * a) n - n) / (2 * a - 1) := by
  apply (eq_div_iff ha).2
  nlinarith only [rawMoment_second_identity a hn]

/-- Real Bernoulli's inequality bounds the growth product by a power of time. -/
theorem growth_le_rpow {p : ℝ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    growth p n ≤ (n : ℝ) ^ p := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hb := one_add_mul_self_le_rpow_one_add
      (s := (n : ℝ)⁻¹) (by have := inv_nonneg.mpr hnR.le; linarith) hp
    rw [growth_succ p hn]
    calc
      growth p n * (1 + p / n) ≤ (n : ℝ) ^ p * (1 + p / n) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ (n : ℝ) ^ p * (1 + (n : ℝ)⁻¹) ^ p := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hnR.le _)
        simpa [div_eq_mul_inv] using hb
      _ = ((n + 1 : ℕ) : ℝ) ^ p := by
        rw [← Real.mul_rpow hnR.le (by positivity : 0 ≤ 1 + (n : ℝ)⁻¹)]
        congr 1
        push_cast
        field_simp

theorem rawMoment_second_le {a : ℝ} (ha : 1 / 2 < a) {n : ℕ} (hn : 1 ≤ n) :
    rawMoment a n 2 ≤ (2 * a / (2 * a - 1)) * (n : ℝ) ^ (2 * a) := by
  have hd : 0 < 2 * a - 1 := by linarith
  have h1 : rawMoment a n 2 ≤ (2 * a * growth (2 * a) n) / (2 * a - 1) := by
    apply (le_div_iff₀ hd).2
    nlinarith [rawMoment_second_identity a hn, Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ (2 * a * growth (2 * a) n) / (2 * a - 1) := h1
    _ = (2 * a / (2 * a - 1)) * growth (2 * a) n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (growth_le_rpow (by linarith) hn) (by positivity)

noncomputable def scaledMoment (a : ℝ) (n k : ℕ) : ℝ :=
  rawMoment a n k / ((n : ℝ) ^ a) ^ k

theorem rawMoment_even_nonneg {a : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1) (n k : ℕ) :
    0 ≤ rawMoment a n (2 * k) := by
  rw [rawMoment_eq_law]
  apply Finset.sum_nonneg
  intro b _
  apply mul_nonneg (law_nonneg (by linarith : 0 ≤ (1 - a) / 2)
    (by linarith : (1 - a) / 2 ≤ 1) n b)
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

theorem scaledMoment_even_nonneg {a : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1) (n k : ℕ) :
    0 ≤ scaledMoment a n (2 * k) := by
  exact div_nonneg (rawMoment_even_nonneg ha ha1 n k) (by positivity)

/-- The moments are those of the actual deterministically rescaled finite walk. -/
theorem scaledMoment_eq (a : ℝ) (n k : ℕ) :
    scaledMoment a n k = ∑ b ∈ range n, law ((1 - a) / 2) n b *
      (((n : ℝ) - 2 * b) / (n : ℝ) ^ a) ^ k := by
  rw [scaledMoment, rawMoment_eq_law, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  rw [div_pow]
  ring

/-- Uniform second moment in the conventional n^a normalization. -/
theorem scaledMoment_second_le {a : ℝ} (ha : 1 / 2 < a) {n : ℕ} (hn : 1 ≤ n) :
    scaledMoment a n 2 ≤ 2 * a / (2 * a - 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [scaledMoment, ← Real.rpow_mul_natCast hnR.le]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hnR _)).2
  simpa [mul_comm] using rawMoment_second_le ha hn

theorem scaledMoment_second_le_four {a : ℝ} (ha : 2 / 3 ≤ a) {n : ℕ} (hn : 1 ≤ n) :
    scaledMoment a n 2 ≤ 4 := by
  apply (scaledMoment_second_le (by linarith : 1 / 2 < a) hn).trans
  apply (div_le_iff₀ (by linarith : 0 < 2 * a - 1)).2
  linarith

end Kagey131.PaperD.ModelFiniteMoments
