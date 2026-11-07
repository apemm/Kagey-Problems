import PaperD.EJPModelFiniteMoments

/-!
# The finite moment sums as actual conditional RRT expectations

The factor two conditions the existing fair-root RRT on its plus root.
This is a finite-law bridge; it makes no claim about a limiting random variable.
-/

namespace Kagey131.PaperD.ModelFiniteMoments

open Finset RRT

theorem count_expectation_eq_rrt (q : ℕ → ℝ) (t : ℕ) (f : ℕ → ℝ) :
    (∑ b ∈ range (t + 1), lawQ q (t + 1) b * f b) =
      2 * rrtExp q t (fun w => if w 0 = true then f (numL w) else 0) := by
  have he : (∑ b ∈ range (t + 2), plusSumQ q t b * f b) =
      ∑ w : Word (t + 1), ewProbQ q t w * (if w 0 = true then f (numL w) else 0) := by
    unfold plusSumQ
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    have hw : numL w ∈ range (t + 2) := by
      exact Finset.mem_range.mpr (by have := numL_le w; omega)
    by_cases h0 : w 0 = true <;> simp [h0, hw, ite_mul]
  rw [rrtExp_eq, ← he, Finset.mul_sum]
  simp_rw [sum_plus_ewProbQ]
  have hs : (∑ b ∈ range (t + 2), 2 * (lawQ q (t + 1) b / 2 * f b)) =
      ∑ b ∈ range (t + 2), lawQ q (t + 1) b * f b := by
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hs, show t + 2 = (t + 1) + 1 by omega,
    Finset.sum_range_succ (fun b => lawQ q (t + 1) b * f b) (t + 1),
    lawQ_support q (by omega : 1 ≤ t + 1) le_rfl, zero_mul, add_zero]

theorem rawMomentQ_eq_rrt (q : ℕ → ℝ) (t k : ℕ) :
    rawMomentQ q (t + 1) k = 2 * rrtExp q t (fun w =>
      if w 0 = true then (((t + 1 : ℕ) : ℝ) - 2 * numL w) ^ k else 0) :=
  count_expectation_eq_rrt q t (fun b => (((t + 1 : ℕ) : ℝ) - 2 * b) ^ k)

theorem rawMoment_eq_rrt (a : ℝ) (t k : ℕ) :
    rawMoment a (t + 1) k = 2 * rrtExp (fun _ => (1 - a) / 2) t (fun w =>
      if w 0 = true then (((t + 1 : ℕ) : ℝ) - 2 * numL w) ^ k else 0) :=
  rawMomentQ_eq_rrt _ t k

end Kagey131.PaperD.ModelFiniteMoments
