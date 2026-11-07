import PaperD.T2_RRTFirstFlip

/-!
# Conditional plus-start moments of the actual finite ERW

`lawQ` is the existing minority-count law identified with the marked RRT.
The expectation transition below is obtained from its proved finite recurrence.
The constant-memory walk uses flip probability `(1-a)/2` and position `n-2b`.
-/

namespace Kagey131.PaperD.ModelFiniteMoments

open Finset RRT

theorem lawQ_support (q : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) {b : ℕ} (hb : n ≤ b) :
    lawQ q n b = 0 := by
  induction n, hn using Nat.le_induction generalizing b with
  | base => simp [lawQ, show b ≠ 0 by omega]
  | succ n hn ih =>
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    rw [lawQ_succ_succ q hn, ih (by omega), ih (by omega)]
    ring

/-- A test-function identity for the actual count law, including its boundary terms. -/
theorem count_step (q : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) (f : ℕ → ℝ) :
    (∑ b ∈ range (n + 1), lawQ q (n + 1) b * f b) =
      ∑ b ∈ range n, lawQ q n b *
        (upProb (q (n - 1)) n b * f (b + 1) +
          (1 - upProb (q (n - 1)) n b) * f b) :=
  dual_sum (lawQ q n) (lawQ q (n + 1)) (upProb (q (n - 1)) n) f n
    (lawQ_succ_zero q hn) (lawQ_succ_succ q hn) (lawQ_support q hn le_rfl)

theorem lawQ_mass (q : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ b ∈ range n, lawQ q n b = 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp [lawQ]
  | succ n hn ih =>
    have h := count_step q hn (fun _ => 1)
    simpa using h.trans (by simpa using ih)

noncomputable def rawMomentQ (q : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∑ b ∈ range n, lawQ q n b * ((n : ℝ) - 2 * b) ^ k

noncomputable def rawMoment (a : ℝ) (n k : ℕ) : ℝ :=
  rawMomentQ (fun _ => (1 - a) / 2) n k

theorem rawMoment_eq_law (a : ℝ) (n k : ℕ) :
    rawMoment a n k = ∑ b ∈ range n, law ((1 - a) / 2) n b * ((n : ℝ) - 2 * b) ^ k := by
  simp [rawMoment, rawMomentQ, lawQ_const]

@[simp] theorem rawMomentQ_one (q : ℕ → ℝ) (k : ℕ) : rawMomentQ q 1 k = 1 := by
  simp [rawMomentQ, lawQ]

@[simp] theorem rawMoment_one (a : ℝ) (k : ℕ) : rawMoment a 1 k = 1 := rawMomentQ_one _ _

theorem rawMomentQ_zero (q : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) : rawMomentQ q n 0 = 1 := by
  simpa [rawMomentQ] using lawQ_mass q hn

theorem rawMoment_zero (a : ℝ) {n : ℕ} (hn : 1 ≤ n) : rawMoment a n 0 = 1 :=
  rawMomentQ_zero _ hn

/-- The actual signed increment has conditional mean `a*S/n`. -/
theorem increment_mean (a : ℝ) {n : ℕ} (hn : 1 ≤ n) (b : ℕ) :
    1 - 2 * upProb ((1 - a) / 2) n b = a / n * ((n : ℝ) - 2 * b) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [upProb]
  field_simp
  ring

theorem signed_step (a : ℝ) {n : ℕ} (hn : 1 ≤ n) (f : ℝ → ℝ) :
    (∑ b ∈ range (n + 1), lawQ (fun _ => (1 - a) / 2) (n + 1) b *
      f ((n + 1 : ℕ) - 2 * (b : ℝ))) =
    ∑ b ∈ range n, lawQ (fun _ => (1 - a) / 2) n b *
      (upProb ((1 - a) / 2) n b * f (((n : ℝ) - 2 * b) - 1) +
        (1 - upProb ((1 - a) / 2) n b) * f (((n : ℝ) - 2 * b) + 1)) := by
  rw [count_step _ hn]
  apply Finset.sum_congr rfl
  intro b _
  congr 2 <;> congr 1 <;> push_cast <;> ring

/-- Binomial expansion of one actual signed transition, split by increment parity. -/
theorem transition_power (x r : ℝ) (k : ℕ) :
    r * (x - 1) ^ k + (1 - r) * (x + 1) ^ k =
      ∑ j ∈ range (k + 1), (k.choose j : ℝ) *
        (if Even j then x ^ (k - j) else (1 - 2 * r) * x ^ (k - j)) := by
  rw [show x - 1 = -1 + x by ring, show x + 1 = 1 + x by ring, add_pow, add_pow]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [neg_one_pow_eq_ite]
  split_ifs <;> simp only [one_pow] <;> ring

/-- Exact raw-moment recurrence of the existing finite plus-start ERW law. -/
theorem rawMoment_succ (a : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    rawMoment a (n + 1) k =
      (∑ j ∈ (range (k + 1)).filter (fun j => Even j),
        (k.choose j : ℝ) * rawMoment a n (k - j)) +
      a / n * ∑ j ∈ (range (k + 1)).filter (fun j => ¬Even j),
        (k.choose j : ℝ) * rawMoment a n (k - j + 1) := by
  unfold rawMoment rawMomentQ
  rw [signed_step a hn (fun x => x ^ k)]
  simp_rw [transition_power, increment_mean a hn]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he : ∀ j ∈ range (k + 1),
      (∑ b ∈ range n, lawQ (fun _ => (1 - a) / 2) n b *
        ((k.choose j : ℝ) * (if Even j then ((n : ℝ) - 2 * b) ^ (k - j)
          else a / n * ((n : ℝ) - 2 * b) * ((n : ℝ) - 2 * b) ^ (k - j)))) =
      if Even j then (k.choose j : ℝ) *
        (∑ b ∈ range n, lawQ (fun _ => (1 - a) / 2) n b * ((n : ℝ) - 2 * b) ^ (k - j))
      else a / n * ((k.choose j : ℝ) *
        (∑ b ∈ range n, lawQ (fun _ => (1 - a) / 2) n b * ((n : ℝ) - 2 * b) ^ (k - j + 1))) := by
    intro j _
    by_cases hj : Even j <;> simp only [hj, if_true, if_false]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    · rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [pow_succ]
      ring
  rw [Finset.sum_congr rfl he]
  rw [Finset.sum_ite, ← Finset.mul_sum]
  simp_rw [← Finset.mul_sum]

end Kagey131.PaperD.ModelFiniteMoments
