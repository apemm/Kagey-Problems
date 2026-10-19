import KageyProblems.Problem001

/-!
# Kagey's Problem 001 — three corners determine a rectangle

Lemma "three corners suffice" of Section 2 of `problem001/jis/pemmasani.tex`: three corners of a
rectangle determine the rectangle, so two distinct rectangles share at most two corners, and two
distinct rectangles with the same presentation both show at most two corners.

## Contents

* `RightAt q a b`: the angle `a q b` is a right angle, `(a - q) · (b - q) = 0`.
* `IsRect.card_eq_four`: a corner set has exactly four points.
* `IsRect.rebase`: every corner can serve as the base point `p` of `{p, p+u, p+v, p+u+v}`.
* `IsRect.three_corners`: three distinct corners `x, y, z` of a rectangle `C` include a right
  angle vertex, and `C` is the three points plus the fourth corner `a + b - q`.
* `eq_of_right_at_both`: a triangle of distinct points has at most one right angle.
* `IsRect.eq_of_three_le_card_inter`: two rectangles sharing three corners are equal;
  `eq_of_three_le_card_inter` is the same statement for `Rects n m`.
* `card_inter_le_two`: two distinct rectangles share at most two corners.
* `eq_of_pres_eq_of_three_le`: equal presentations with at least three visible corners force
  equality; `pres_card_le_two_of_ne`: two distinct rectangles with the same presentation both
  show at most two corners.
-/

namespace Kagey001

open Finset

/-- The angle at `q` in the triangle `a q b` is a right angle: `(a - q) · (b - q) = 0`. -/
def RightAt (q a b : Pt) : Prop :=
  (a.1 - q.1) * (b.1 - q.1) + (a.2 - q.2) * (b.2 - q.2) = 0

lemma RightAt.symm {q a b : Pt} (h : RightAt q a b) : RightAt q b a := by
  unfold RightAt at *
  linear_combination h

/-- A triangle has at most one right angle: right angles at `q` and at `a` force `q = a`. -/
theorem eq_of_right_at_both {q a b : Pt} (h₁ : RightAt q a b) (h₂ : RightAt a q b) : q = a := by
  unfold RightAt at h₁ h₂
  have hs : (a.1 - q.1) ^ 2 + (a.2 - q.2) ^ 2 = 0 := by linear_combination h₁ + h₂
  have e1 : a.1 - q.1 = 0 := by nlinarith [sq_nonneg (a.1 - q.1), sq_nonneg (a.2 - q.2)]
  have e2 : a.2 - q.2 = 0 := by nlinarith [sq_nonneg (a.1 - q.1), sq_nonneg (a.2 - q.2)]
  exact Prod.ext (by linarith) (by linarith)

/-- A corner set has exactly four points. -/
theorem IsRect.card_eq_four {C : Finset Pt} (hC : IsRect C) : C.card = 4 := by
  obtain ⟨p, u, v, hu, hv, huv, rfl⟩ := hC
  have hu' : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (Prod.ext h.1 h.2)
  have hv' : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (Prod.ext h.1 h.2)
  -- `u ≠ v` and `u ≠ -v`, since `u · v = 0` and `u ≠ 0`.
  have hnv : ¬ (u.1 = v.1 ∧ u.2 = v.2) := by
    rintro ⟨h1, h2⟩
    rw [← h1, ← h2] at huv
    rcases hu' with h | h
    · exact h (by nlinarith [sq_nonneg u.1, sq_nonneg u.2])
    · exact h (by nlinarith [sq_nonneg u.1, sq_nonneg u.2])
  have hnv' : ¬ (u.1 = -v.1 ∧ u.2 = -v.2) := by
    rintro ⟨h1, h2⟩
    rw [h1, h2] at huv
    rcases hv' with h | h
    · exact h (by nlinarith [sq_nonneg v.1, sq_nonneg v.2])
    · exact h (by nlinarith [sq_nonneg v.1, sq_nonneg v.2])
  rw [card_insert_of_notMem, card_insert_of_notMem, card_pair]
  all_goals
    try simp only [ne_eq, mem_insert, mem_singleton, Prod.ext_iff, Prod.fst_add, Prod.snd_add,
      not_or]
  all_goals omega

/-- Every corner of a rectangle can serve as the base point of its parametrization. -/
theorem IsRect.rebase {C : Finset Pt} (hC : IsRect C) {x : Pt} (hx : x ∈ C) :
    ∃ u v : Pt, u ≠ 0 ∧ v ≠ 0 ∧ u.1 * v.1 + u.2 * v.2 = 0 ∧ C = {x, x + u, x + v, x + u + v} := by
  obtain ⟨p, u, v, hu, hv, huv, rfl⟩ := hC
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨u, v, hu, hv, huv, rfl⟩
  · refine ⟨-u, v, neg_ne_zero.mpr hu, hv, ?_, ?_⟩
    · simp only [Prod.fst_neg, Prod.snd_neg]
      linear_combination -huv
    have e1 : p + u + -u = p := by abel
    have e2 : p + u + -u + v = p + v := by abel
    rw [e2, e1]
    ext t
    simp only [mem_insert, mem_singleton]
    tauto
  · refine ⟨u, -v, hu, neg_ne_zero.mpr hv, ?_, ?_⟩
    · simp only [Prod.fst_neg, Prod.snd_neg]
      linear_combination -huv
    have e1 : p + v + u = p + u + v := by abel
    have e2 : p + v + -v = p := by abel
    have e3 : p + v + u + -v = p + u := by abel
    rw [e3, e1, e2]
    ext t
    simp only [mem_insert, mem_singleton]
    tauto
  · refine ⟨-u, -v, neg_ne_zero.mpr hu, neg_ne_zero.mpr hv, ?_, ?_⟩
    · simp only [Prod.fst_neg, Prod.snd_neg]
      linear_combination huv
    have e1 : p + u + v + -u = p + v := by abel
    have e2 : p + u + v + -v = p + u := by abel
    have e3 : p + u + v + -u + -v = p := by abel
    rw [e3, e1, e2]
    ext t
    simp only [mem_insert, mem_singleton]
    tauto

/-- **Three corners.** Three distinct corners `x, y, z` of a rectangle `C` contain a right-angle
vertex `q` (the corner adjacent to the other two, `a` and `b`), and `C` consists of `x, y, z`
and the fourth corner `a + b - q`. -/
theorem IsRect.three_corners {C : Finset Pt} (hC : IsRect C) {x y z : Pt}
    (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (RightAt x y z ∧ C = {x, y, z, y + z - x}) ∨
    (RightAt y x z ∧ C = {x, y, z, x + z - y}) ∨
    (RightAt z x y ∧ C = {x, y, z, x + y - z}) := by
  obtain ⟨u, v, -, -, huv, rfl⟩ := hC.rebase hx
  simp only [mem_insert, mem_singleton] at hy hz
  rcases hy with rfl | rfl | rfl | rfl
  · exact absurd rfl hxy
  all_goals rcases hz with rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hxz
    | exact absurd rfl hyz
    | skip
  all_goals first
    | (refine Or.inl ⟨?_, ?_⟩
       · unfold RightAt
         simp only [Prod.fst_add, Prod.snd_add]
         first | linear_combination huv | linear_combination -huv
       · ext t
         simp only [mem_insert, mem_singleton]
         constructor <;> rintro (rfl | rfl | rfl | rfl) <;>
           simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
             true_or, or_true] <;>
           omega)
    | (refine Or.inr (Or.inl ⟨?_, ?_⟩)
       · unfold RightAt
         simp only [Prod.fst_add, Prod.snd_add]
         first | linear_combination huv | linear_combination -huv
       · ext t
         simp only [mem_insert, mem_singleton]
         constructor <;> rintro (rfl | rfl | rfl | rfl) <;>
           simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
             true_or, or_true] <;>
           omega)
    | (refine Or.inr (Or.inr ⟨?_, ?_⟩)
       · unfold RightAt
         simp only [Prod.fst_add, Prod.snd_add]
         first | linear_combination huv | linear_combination -huv
       · ext t
         simp only [mem_insert, mem_singleton]
         constructor <;> rintro (rfl | rfl | rfl | rfl) <;>
           simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
             true_or, or_true] <;>
           omega)

/-- **Lemma "three corners suffice".** Two rectangles that share three corners are equal. -/
theorem IsRect.eq_of_three_le_card_inter {C₁ C₂ : Finset Pt} (h₁ : IsRect C₁) (h₂ : IsRect C₂)
    (h : 3 ≤ (C₁ ∩ C₂).card) : C₁ = C₂ := by
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp h
  rw [mem_inter] at hx hy hz
  have k₁ := h₁.three_corners hx.1 hy.1 hz.1 hxy hxz hyz
  have k₂ := h₂.three_corners hx.2 hy.2 hz.2 hxy hxz hyz
  rcases k₁ with ⟨r₁, e₁⟩ | ⟨r₁, e₁⟩ | ⟨r₁, e₁⟩ <;>
    rcases k₂ with ⟨r₂, e₂⟩ | ⟨r₂, e₂⟩ | ⟨r₂, e₂⟩
  · rw [e₁, e₂]
  · exact absurd (eq_of_right_at_both r₁ r₂) hxy
  · exact absurd (eq_of_right_at_both r₁.symm r₂) hxz
  · exact absurd (eq_of_right_at_both r₂ r₁) hxy
  · rw [e₁, e₂]
  · exact absurd (eq_of_right_at_both r₁.symm r₂.symm) hyz
  · exact absurd (eq_of_right_at_both r₂.symm r₁) hxz
  · exact absurd (eq_of_right_at_both r₂.symm r₁.symm) hyz
  · rw [e₁, e₂]

/-- **Lemma "three corners suffice"**, for the rectangles of the `n × m` grid: if
`C₁, C₂ ∈ Rects n m` share at least three points, then `C₁ = C₂`. -/
theorem eq_of_three_le_card_inter {n m : ℕ} {C₁ C₂ : Finset Pt} (h₁ : C₁ ∈ Rects n m)
    (h₂ : C₂ ∈ Rects n m) (h : 3 ≤ (C₁ ∩ C₂).card) : C₁ = C₂ :=
  h₁.1.eq_of_three_le_card_inter h₂.1 h

/-- Two distinct rectangles share at most two corners. -/
theorem card_inter_le_two {n m : ℕ} {C₁ C₂ : Finset Pt} (h₁ : C₁ ∈ Rects n m)
    (h₂ : C₂ ∈ Rects n m) (hne : C₁ ≠ C₂) : (C₁ ∩ C₂).card ≤ 2 := by
  by_contra h
  exact hne (eq_of_three_le_card_inter h₁ h₂ (by omega))

/-- The visible corners of a rectangle under two equal presentations are common corners. -/
lemma pres_subset_inter {S C₁ C₂ : Finset Pt} (hp : pres S C₁ = pres S C₂) :
    pres S C₁ ⊆ C₁ ∩ C₂ := by
  intro t ht
  have ht₂ : t ∈ pres S C₂ := hp ▸ ht
  exact mem_inter.mpr ⟨(mem_sdiff.mp ht).1, (mem_sdiff.mp ht₂).1⟩

/-- **Corollary.** Two rectangles with the same presentation, showing at least three corners,
are equal. -/
theorem eq_of_pres_eq_of_three_le {n m : ℕ} {S C₁ C₂ : Finset Pt} (h₁ : C₁ ∈ Rects n m)
    (h₂ : C₂ ∈ Rects n m) (hp : pres S C₁ = pres S C₂) (h : 3 ≤ (pres S C₁).card) :
    C₁ = C₂ :=
  eq_of_three_le_card_inter h₁ h₂ (h.trans (card_le_card (pres_subset_inter hp)))

/-- **Corollary.** Two distinct rectangles with the same presentation both show at most two
corners. -/
theorem pres_card_le_two_of_ne {n m : ℕ} {S C₁ C₂ : Finset Pt} (h₁ : C₁ ∈ Rects n m)
    (h₂ : C₂ ∈ Rects n m) (hne : C₁ ≠ C₂) (hp : pres S C₁ = pres S C₂) :
    (pres S C₁).card ≤ 2 ∧ (pres S C₂).card ≤ 2 := by
  have a : (pres S C₁).card ≤ 2 := by
    by_contra h
    exact hne (eq_of_pres_eq_of_three_le h₁ h₂ hp (by omega))
  exact ⟨a, hp ▸ a⟩

end Kagey001
