import Mathlib

/-!
# Paper B, Lemma `lem:clipped-product` (clipped product deficit)

For nonnegative reals `t_1, …, t_m`,
`0 ≤ 1 - ∏ (1 - t_j)_+ ≤ ∑ t_j`, including the empty product.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset

/-- The clipped product lies in `[0,1]` and its deficit from one is at most
the sum. -/
theorem clipped_product_aux {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → ℝ)
    (ht : ∀ j ∈ s, 0 ≤ t j) :
    0 ≤ ∏ j ∈ s, max (1 - t j) 0 ∧ ∏ j ∈ s, max (1 - t j) 0 ≤ 1 ∧
      1 - ∏ j ∈ s, max (1 - t j) 0 ≤ ∑ j ∈ s, t j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h0, h1, h2⟩ := ih fun j hj => ht j (mem_insert_of_mem hj)
    have hta := ht a (mem_insert_self a s)
    rw [prod_insert ha, sum_insert ha]
    set P := ∏ j ∈ s, max (1 - t j) 0
    set m := max (1 - t a) 0
    have hm0 : 0 ≤ m := le_max_right _ _
    have hm1 : m ≤ 1 := max_le (by linarith) (by norm_num)
    have hm2 : 1 - t a ≤ m := le_max_left _ _
    refine ⟨mul_nonneg hm0 h0, ?_, ?_⟩
    · calc m * P ≤ 1 * 1 := mul_le_mul hm1 h1 h0 (by norm_num)
        _ = 1 := by norm_num
    · nlinarith

/-- **Lemma `lem:clipped-product`.** -/
theorem clipped_product {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → ℝ)
    (ht : ∀ j ∈ s, 0 ≤ t j) :
    0 ≤ 1 - ∏ j ∈ s, max (1 - t j) 0 ∧ 1 - ∏ j ∈ s, max (1 - t j) 0 ≤ ∑ j ∈ s, t j := by
  obtain ⟨_, h1, h2⟩ := clipped_product_aux s t ht
  exact ⟨by linarith, h2⟩

end Kagey131.PaperB
