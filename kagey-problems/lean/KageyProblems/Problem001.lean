import Mathlib

/-!
# Kagey's Problem 001 — blackouts preserving rectangle identifiability

Lean 4 / Mathlib formalization of the *proved* results of `paper/main.tex`
(A. Pemmasani, 2026).  Nothing about the open conjectures (Three-Row, Excess-1) is stated here.

Black out as many points of an `n × m` grid as possible so that every rectangle with corners
on grid points (tilted ones included) stays uniquely identifiable from its visible corners.

## Contents

* `grid n m`, `IsRect`, `Rects n m`, `pres`, `Valid`: the conventions of Section 2.
  Rectangles are identified with their corner sets; a corner set is `{p, p+u, p+v, p+u+v}` with
  `u ⊥ v` and `u, v ≠ 0`, which excludes degenerate rectangles.
* `sdiff_eq_sdiff_iff_symmDiff_subset`: Lemma 1 (difference-set characterization),
  `valid_iff_hitting`: its corollary (valid ⇔ the kept set hits every difference set),
  `at_most_one_hidden`: Remark 1 (the empty presentation needs no special convention),
  `hits_of_subset` / `hitting_erase_superset`: the containment rule of Section 4.
* `mem_rects_strip`: on a `2 × m` grid every rectangle is axis-aligned, i.e. a union of two
  columns (the geometric step of the Strip Theorem).
* `valid_strip_iff`: for `m ≥ 3`, a blackout of the strip is valid iff at most one column is
  fully blacked out.
* `strip_theorem`: **the Strip Theorem** for `m ≥ 3` — every valid blackout has at most `m + 1`
  points, the bound is attained, the maximum blackouts are exactly the `stripBlackout m e T`
  (one full column `e`, one point in every other column), and there are exactly `m * 2^(m-1)`
  of them.
* `valid_two_two`: for `m = 2` the condition is vacuous.
-/

namespace Kagey001

open Finset

/-- A grid point, written `(column, row)`. -/
abbrev Pt := ℤ × ℤ

/-- The `n × m` grid (`n` rows, `m` columns): columns `1..m`, rows `1..n`. -/
noncomputable def grid (n m : ℕ) : Finset Pt := Finset.Icc (1 : ℤ) m ×ˢ Finset.Icc (1 : ℤ) n

lemma mem_grid {n m : ℕ} {y : Pt} : y ∈ grid n m ↔ 1 ≤ y.1 ∧ y.1 ≤ m ∧ 1 ≤ y.2 ∧ y.2 ≤ n := by
  simp [grid, Finset.mem_product, Finset.mem_Icc, and_assoc]

lemma mem_grid' {n m : ℕ} {a b : ℤ} : (a, b) ∈ grid n m ↔ 1 ≤ a ∧ a ≤ m ∧ 1 ≤ b ∧ b ≤ n :=
  mem_grid

/-- `C` is the corner set of a non-degenerate rectangle: `{p, p+u, p+v, p+u+v}` with `u ⊥ v`
and `u, v ≠ 0`. -/
def IsRect (C : Finset Pt) : Prop :=
  ∃ p u v : Pt, u ≠ 0 ∧ v ≠ 0 ∧ u.1 * v.1 + u.2 * v.2 = 0 ∧ C = {p, p + u, p + v, p + u + v}

/-- The rectangle class of the `n × m` grid, identified with corner sets. -/
def Rects (n m : ℕ) : Set (Finset Pt) := {C | IsRect C ∧ C ⊆ grid n m}

/-- The presentation map `P_S(R) = C(R) \ S`: the visible corners. -/
def pres (S C : Finset Pt) : Finset Pt := C \ S

/-- A blackout `S` is valid when the presentation map is injective on rectangles. -/
def Valid (n m : ℕ) (S : Finset Pt) : Prop :=
  ∀ C₁ ∈ Rects n m, ∀ C₂ ∈ Rects n m, pres S C₁ = pres S C₂ → C₁ = C₂

/-! ### Section 3: the reduction -/

/-- **Lemma 1 (difference-set characterization).** `A \ S = B \ S ↔ A △ B ⊆ S`. -/
theorem sdiff_eq_sdiff_iff_symmDiff_subset {α : Type*} [DecidableEq α] (A B S : Finset α) :
    A \ S = B \ S ↔ symmDiff A B ⊆ S := by
  constructor
  · intro h x hx
    rw [Finset.mem_symmDiff] at hx
    by_contra hxS
    rcases hx with ⟨hA, hB⟩ | ⟨hB, hA⟩
    · have : x ∈ A \ S := Finset.mem_sdiff.mpr ⟨hA, hxS⟩
      rw [h] at this
      exact hB (Finset.mem_sdiff.mp this).1
    · have : x ∈ B \ S := Finset.mem_sdiff.mpr ⟨hB, hxS⟩
      rw [← h] at this
      exact hA (Finset.mem_sdiff.mp this).1
  · intro h
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hA, hS⟩
      refine ⟨?_, hS⟩
      by_contra hB
      exact hS (h (Finset.mem_symmDiff.mpr (Or.inl ⟨hA, hB⟩)))
    · rintro ⟨hB, hS⟩
      refine ⟨?_, hS⟩
      by_contra hA
      exact hS (h (Finset.mem_symmDiff.mpr (Or.inr ⟨hB, hA⟩)))

/-- **Corollary.** `S` is valid iff the kept set `V \ S` meets the difference set
`C(R₁) △ C(R₂)` of every pair of distinct rectangles: a maximum blackout is the complement
of a minimum hitting set of the difference hypergraph. -/
theorem valid_iff_hitting (n m : ℕ) (S : Finset Pt) :
    Valid n m S ↔ ∀ C₁ ∈ Rects n m, ∀ C₂ ∈ Rects n m, C₁ ≠ C₂ →
      ∃ x ∈ symmDiff C₁ C₂, x ∉ S := by
  simp only [Valid, pres, sdiff_eq_sdiff_iff_symmDiff_subset]
  constructor
  · intro h C₁ h₁ C₂ h₂ hne
    by_contra hcon
    exact hne (h C₁ h₁ C₂ h₂ (fun x hx => by
      by_contra hxS
      exact hcon ⟨x, hx, hxS⟩))
  · intro h C₁ h₁ C₂ h₂ hsub
    by_contra hne
    obtain ⟨x, hx, hxS⟩ := h C₁ h₁ C₂ h₂ hne
    exact hxS (hsub hx)

/-- **Remark 1.** Under a valid blackout at most one rectangle is fully hidden: the empty
presentation is an ordinary value of the presentation map. -/
theorem at_most_one_hidden {n m : ℕ} {S : Finset Pt} (hS : Valid n m S) {C₁ C₂ : Finset Pt}
    (h₁ : C₁ ∈ Rects n m) (h₂ : C₂ ∈ Rects n m) (hc₁ : C₁ ⊆ S) (hc₂ : C₂ ⊆ S) : C₁ = C₂ :=
  hS C₁ h₁ C₂ h₂ (by
    simp only [pres]
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hc₁, Finset.sdiff_eq_empty_iff_subset.mpr hc₂])

/-! ### Section 4: preprocessing (the containment rule) -/

/-- A kept set `K` hitting a difference set `D₁` hits every superset `D₂ ⊇ D₁`. -/
theorem hits_of_subset {α : Type*} {K D₁ D₂ : Finset α} (h : D₁ ⊆ D₂)
    (hK : ∃ x ∈ D₁, x ∈ K) : ∃ x ∈ D₂, x ∈ K := by
  obtain ⟨x, hx, hxK⟩ := hK
  exact ⟨x, h hx, hxK⟩

/-- Deleting a row `D₂` that properly contains another row `D₁` does not change the family of
hitting sets. -/
theorem hitting_erase_superset {α : Type*} {F : Set (Finset α)} {D₁ D₂ : Finset α}
    (h₁ : D₁ ∈ F) (h₁₂ : D₁ ⊆ D₂) (hne : D₁ ≠ D₂) (K : Finset α) :
    (∀ D ∈ F, ∃ x ∈ D, x ∈ K) ↔ ∀ D ∈ F \ {D₂}, ∃ x ∈ D, x ∈ K := by
  constructor
  · intro h D hD
    exact h D hD.1
  · intro h D hD
    by_cases hD₂ : D = D₂
    · subst hD₂
      exact hits_of_subset h₁₂ (h D₁ ⟨h₁, by simpa using hne⟩)
    · exact h D ⟨hD, by simpa using hD₂⟩

/-! ### Section 5: the Strip Theorem -/

/-- Column `i` of a two-row strip. -/
def col (i : ℤ) : Finset Pt := {(i, 1), (i, 2)}

lemma mem_col {i : ℤ} {y : Pt} : y ∈ col i ↔ y.1 = i ∧ (y.2 = 1 ∨ y.2 = 2) := by
  obtain ⟨a, b⟩ := y
  simp only [col, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

lemma card_col (i : ℤ) : (col i).card = 2 := by
  rw [col, Finset.card_pair]
  simp

/-- The geometric step: a rectangle whose four corners lie in two rows is axis-aligned. -/
lemma strip_aux {m : ℕ} (p u v : Pt) (hu : u ≠ 0) (hv : v ≠ 0) (hperp : u.1 * v.1 + u.2 * v.2 = 0)
    (hu2 : u.2 = 0) (hsub : ({p, p + u, p + v, p + u + v} : Finset Pt) ⊆ grid 2 m) :
    ∃ i j : ℤ, 1 ≤ i ∧ i < j ∧ j ≤ m ∧
      ({p, p + u, p + v, p + u + v} : Finset Pt) = col i ∪ col j := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  dsimp only at hu2 hperp
  subst hu2
  have hu1 : u1 ≠ 0 := by rintro rfl; exact hu rfl
  have hv1 : v1 = 0 := by
    have : u1 * v1 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hu1
    · exact h
  subst hv1
  have hv2 : v2 ≠ 0 := by rintro rfl; exact hv rfl
  have h1 := mem_grid.mp (hsub (by simp : (p1, p2) ∈ _))
  have h2 := mem_grid.mp (hsub (by simp : (p1, p2) + (u1, 0) ∈ _))
  have h3 := mem_grid.mp (hsub (by simp : (p1, p2) + (0, v2) ∈ _))
  simp only [Prod.mk_add_mk, add_zero] at h1 h2 h3
  rcases lt_or_gt_of_ne hu1 with hneg | hpos
  · refine ⟨p1 + u1, p1, by omega, by omega, by omega, ?_⟩
    ext ⟨a, b⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, mem_col,
      Prod.mk_add_mk, Prod.mk.injEq, add_zero]
    omega
  · refine ⟨p1, p1 + u1, by omega, by omega, by omega, ?_⟩
    ext ⟨a, b⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, mem_col,
      Prod.mk_add_mk, Prod.mk.injEq, add_zero]
    omega

/-- On a `2 × m` strip the rectangles are exactly the unions of two distinct columns. -/
theorem mem_rects_strip {m : ℕ} {C : Finset Pt} :
    C ∈ Rects 2 m ↔ ∃ i j : ℤ, 1 ≤ i ∧ i < j ∧ j ≤ m ∧ C = col i ∪ col j := by
  constructor
  · rintro ⟨⟨p, u, v, hu, hv, hperp, rfl⟩, hsub⟩
    have hrows : u.2 = 0 ∨ v.2 = 0 := by
      have h1 := mem_grid.mp (hsub (by simp : p ∈ _))
      have h2 := mem_grid.mp (hsub (by simp : p + u ∈ _))
      have h3 := mem_grid.mp (hsub (by simp : p + v ∈ _))
      have h4 := mem_grid.mp (hsub (by simp : p + u + v ∈ _))
      simp only [Prod.snd_add] at h2 h3 h4
      omega
    rcases hrows with h | h
    · exact strip_aux p u v hu hv hperp h hsub
    · have e : ({p, p + u, p + v, p + u + v} : Finset Pt) = {p, p + v, p + u, p + v + u} := by
        rw [Finset.insert_comm (p + u) (p + v), add_right_comm]
      rw [e] at hsub ⊢
      exact strip_aux p v u hv hu (by rw [mul_comm v.1, mul_comm v.2]; exact hperp) h hsub
  · rintro ⟨i, j, hi, hij, hj, rfl⟩
    refine ⟨⟨(i, 1), (j - i, 0), (0, 1), ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [Ne, Prod.mk_eq_zero]; omega
    · simp
    · simp
    · ext ⟨a, b⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, mem_col,
        Prod.mk_add_mk, Prod.mk.injEq]
      omega
    · intro y hy
      rw [Finset.mem_union, mem_col, mem_col] at hy
      rw [mem_grid]
      omega

/-- If `col c` belongs to the first rectangle but not the second, and the two rectangles have
the same presentation, then `col c` is fully blacked out. -/
lemma full_of_not_mem {S : Finset Pt} {i j k l c : ℤ}
    (h : (col i ∪ col j) \ S = (col k ∪ col l) \ S)
    (hc : c = i ∨ c = j) (hck : c ≠ k) (hcl : c ≠ l) : col c ⊆ S := by
  intro y hy
  by_contra hyS
  have hy1 : y ∈ (col i ∪ col j) \ S := by
    refine Finset.mem_sdiff.mpr ⟨?_, hyS⟩
    rw [Finset.mem_union, mem_col, mem_col]
    rw [mem_col] at hy
    omega
  rw [h] at hy1
  have := (Finset.mem_sdiff.mp hy1).1
  rw [Finset.mem_union, mem_col, mem_col] at this
  rw [mem_col] at hy
  omega

/-- For `m ≥ 3`, a blackout of the `2 × m` strip is valid iff at most one column is fully
blacked out (the pruned difference hypergraph consists of the `C(m, 2)` pair rows). -/
theorem valid_strip_iff {m : ℕ} (hm : 3 ≤ m) (S : Finset Pt) :
    Valid 2 m S ↔ ∀ p q : ℤ, 1 ≤ p → p ≤ m → 1 ≤ q → q ≤ m →
      col p ⊆ S → col q ⊆ S → p = q := by
  constructor
  · intro hv p q hp1 hp2 hq1 hq2 hpS hqS
    by_contra hne
    obtain ⟨z, hz1, hz2, hzp, hzq⟩ : ∃ z : ℤ, 1 ≤ z ∧ z ≤ m ∧ z ≠ p ∧ z ≠ q := by
      by_cases h1 : p ≠ 1 ∧ q ≠ 1
      · exact ⟨1, le_refl _, by omega, by omega, by omega⟩
      · by_cases h2 : p ≠ 2 ∧ q ≠ 2
        · exact ⟨2, by omega, by omega, by omega, by omega⟩
        · exact ⟨3, by omega, by omega, by omega, by omega⟩
    have hR : ∀ w : ℤ, 1 ≤ w → w ≤ m → w ≠ z → col z ∪ col w ∈ Rects 2 m := by
      intro w hw1 hw2 hwz
      rw [mem_rects_strip]
      rcases lt_or_gt_of_ne hwz with h | h
      · exact ⟨w, z, hw1, h, hz2, Finset.union_comm _ _⟩
      · exact ⟨z, w, hz1, h, hw2, rfl⟩
    have hpres : pres S (col z ∪ col p) = pres S (col z ∪ col q) := by
      simp only [pres, Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr hpS,
        Finset.sdiff_eq_empty_iff_subset.mpr hqS]
    have heq := hv _ (hR p hp1 hp2 (Ne.symm hzp)) _ (hR q hq1 hq2 (Ne.symm hzq)) hpres
    have hmem : ((p, 1) : Pt) ∈ col z ∪ col q := by
      rw [← heq]; simp [col]
    rw [Finset.mem_union, mem_col, mem_col] at hmem
    omega
  · intro h C₁ h₁ C₂ h₂ hpres
    obtain ⟨i, j, hi, hij, hj, rfl⟩ := mem_rects_strip.mp h₁
    obtain ⟨k, l, hk, hkl, hl, rfl⟩ := mem_rects_strip.mp h₂
    simp only [pres] at hpres
    by_cases hsame : i = k ∧ j = l
    · rw [hsame.1, hsame.2]
    · exfalso
      obtain ⟨c, hc, hck, hcl⟩ : ∃ c, (c = i ∨ c = j) ∧ c ≠ k ∧ c ≠ l := by
        by_cases hi' : i = k ∨ i = l
        · exact ⟨j, Or.inr rfl, by omega, by omega⟩
        · exact ⟨i, Or.inl rfl, by omega, by omega⟩
      obtain ⟨c', hc', hci, hcj⟩ : ∃ c', (c' = k ∨ c' = l) ∧ c' ≠ i ∧ c' ≠ j := by
        by_cases hk' : k = i ∨ k = j
        · exact ⟨l, Or.inr rfl, by omega, by omega⟩
        · exact ⟨k, Or.inl rfl, by omega, by omega⟩
      have hfull := full_of_not_mem hpres hc hck hcl
      have hfull' := full_of_not_mem hpres.symm hc' hci hcj
      have := h c c' (by omega) (by omega) (by omega) (by omega) hfull hfull'
      omega

/-- For `m = 2` there is a single rectangle, so every blackout is valid. -/
theorem valid_two_two (S : Finset Pt) : Valid 2 2 S := by
  intro C₁ h₁ C₂ h₂ _
  obtain ⟨i, j, hi, hij, hj, rfl⟩ := mem_rects_strip.mp h₁
  obtain ⟨k, l, hk, hkl, hl, rfl⟩ := mem_rects_strip.mp h₂
  have : i = 1 ∧ j = 2 ∧ k = 1 ∧ l = 2 := by omega
  rw [this.1, this.2.1, this.2.2.1, this.2.2.2]

/-! #### Counting points column by column -/

lemma inter_col_card_le (S : Finset Pt) (c : ℤ) :
    (S ∩ col c).card ≤ 1 + (if col c ⊆ S then 1 else 0) := by
  split_ifs with h
  · calc (S ∩ col c).card ≤ (col c).card := Finset.card_le_card Finset.inter_subset_right
      _ = 2 := card_col c
  · have hne : S ∩ col c ≠ col c := fun h' => h (Finset.inter_eq_right.mp h')
    have : (S ∩ col c).card < (col c).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, hne⟩)
    rw [card_col] at this
    omega

lemma card_eq_sum_cols {m : ℕ} {S : Finset Pt} (hS : S ⊆ grid 2 m) :
    S.card = ∑ c ∈ Finset.Icc (1 : ℤ) m, (S ∩ col c).card := by
  have hdecomp : S = (Finset.Icc (1 : ℤ) m).biUnion (fun c => S ∩ col c) := by
    ext y
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_inter, mem_col]
    constructor
    · intro hy
      have := mem_grid.mp (hS hy)
      exact ⟨y.1, ⟨this.1, this.2.1⟩, hy, rfl, by omega⟩
    · rintro ⟨c, _, hy, _⟩
      exact hy
  conv_lhs => rw [hdecomp]
  rw [Finset.card_biUnion]
  intro x _ y _ hxy
  show Disjoint (S ∩ col x) (S ∩ col y)
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [Finset.mem_inter, mem_col] at hz hz'
  omega

/-- The full columns of `S`. -/
noncomputable def fullCols (m : ℕ) (S : Finset Pt) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) m).filter (fun c => col c ⊆ S)

lemma card_le_add_fullCols {m : ℕ} {S : Finset Pt} (hS : S ⊆ grid 2 m) :
    S.card ≤ m + (fullCols m S).card := by
  rw [card_eq_sum_cols hS]
  calc ∑ c ∈ Finset.Icc (1 : ℤ) m, (S ∩ col c).card
      ≤ ∑ c ∈ Finset.Icc (1 : ℤ) m, (1 + if col c ⊆ S then 1 else 0) :=
        Finset.sum_le_sum (fun c _ => inter_col_card_le S c)
    _ = m + (fullCols m S).card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.card_filter, Int.card_Icc,
          smul_eq_mul, mul_one, fullCols]
        simp

lemma card_fullCols_le_one {m : ℕ} (hm : 3 ≤ m) {S : Finset Pt} (hv : Valid 2 m S) :
    (fullCols m S).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  rw [fullCols, Finset.mem_filter, Finset.mem_Icc] at hp hq
  exact (valid_strip_iff hm S).mp hv p q hp.1.1 hp.1.2 hq.1.1 hq.1.2 hp.2 hq.2

/-- **Upper bound.** A valid blackout of the `2 × m` strip (`m ≥ 3`) has at most `m + 1`
points. -/
theorem card_le_of_valid {m : ℕ} (hm : 3 ≤ m) {S : Finset Pt} (hS : S ⊆ grid 2 m)
    (hv : Valid 2 m S) : S.card ≤ m + 1 :=
  (card_le_add_fullCols hS).trans (by have := card_fullCols_le_one hm hv; omega)

/-! #### The maximum blackouts -/

/-- The blackout with column `e` fully blacked out and, in every other column `c`, exactly the
point in row `2` (if `c ∈ T`) or row `1` (if `c ∉ T`). -/
noncomputable def stripBlackout (m : ℕ) (e : ℤ) (T : Finset ℤ) : Finset Pt :=
  (grid 2 m).filter (fun y => y.1 = e ∨ (y.1 ∈ T ∧ y.2 = 2) ∨ (y.1 ∉ T ∧ y.2 = 1))

lemma mem_stripBlackout {m : ℕ} {e : ℤ} {T : Finset ℤ} {y : Pt} :
    y ∈ stripBlackout m e T ↔
      (1 ≤ y.1 ∧ y.1 ≤ m ∧ 1 ≤ y.2 ∧ y.2 ≤ 2) ∧
        (y.1 = e ∨ (y.1 ∈ T ∧ y.2 = 2) ∨ (y.1 ∉ T ∧ y.2 = 1)) := by
  simp only [stripBlackout, Finset.mem_filter, mem_grid, Nat.cast_ofNat]

lemma mem_stripBlackout' {m : ℕ} {e : ℤ} {T : Finset ℤ} {a b : ℤ} :
    (a, b) ∈ stripBlackout m e T ↔
      (1 ≤ a ∧ a ≤ m ∧ 1 ≤ b ∧ b ≤ 2) ∧ (a = e ∨ (a ∈ T ∧ b = 2) ∨ (a ∉ T ∧ b = 1)) :=
  mem_stripBlackout

lemma stripBlackout_subset (m : ℕ) (e : ℤ) (T : Finset ℤ) : stripBlackout m e T ⊆ grid 2 m :=
  Finset.filter_subset _ _

lemma col_subset_stripBlackout_iff {m : ℕ} {e : ℤ} (he : e ∈ Finset.Icc (1 : ℤ) m)
    {T : Finset ℤ} (hT : T ⊆ (Finset.Icc (1 : ℤ) m).erase e) (c : ℤ) :
    col c ⊆ stripBlackout m e T ↔ c = e := by
  rw [Finset.mem_Icc] at he
  constructor
  · intro h
    have h1 := mem_stripBlackout'.mp (h (by simp [col] : ((c, 1) : Pt) ∈ col c))
    have h2 := mem_stripBlackout'.mp (h (by simp [col] : ((c, 2) : Pt) ∈ col c))
    by_contra hce
    have hcT : c ∈ T := by
      rcases h2.2 with h | ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h hce
      · exact h
      · omega
    have hcT' : c ∉ T := by
      rcases h1.2 with h | ⟨_, h⟩ | ⟨h, _⟩
      · exact absurd h hce
      · omega
      · exact h
    exact hcT' hcT
  · rintro rfl
    intro y hy
    rw [mem_col] at hy
    rw [mem_stripBlackout]
    omega

lemma inter_col_stripBlackout {m : ℕ} {e : ℤ} (_he : e ∈ Finset.Icc (1 : ℤ) m)
    {T : Finset ℤ} (_hT : T ⊆ (Finset.Icc (1 : ℤ) m).erase e) {c : ℤ}
    (hc : c ∈ (Finset.Icc (1 : ℤ) m).erase e) :
    stripBlackout m e T ∩ col c = if c ∈ T then {((c, 2) : Pt)} else {((c, 1) : Pt)} := by
  rw [Finset.mem_erase, Finset.mem_Icc] at hc
  split_ifs with hcT
  · ext ⟨a, b⟩
    simp only [Finset.mem_inter, mem_stripBlackout', mem_col, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, h⟩, ha, hb⟩
      subst ha
      rcases h with h | ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · exact ⟨rfl, h⟩
      · exact absurd hcT h
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨by omega, Or.inr (Or.inl ⟨hcT, rfl⟩)⟩, rfl, by omega⟩
  · ext ⟨a, b⟩
    simp only [Finset.mem_inter, mem_stripBlackout', mem_col, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, h⟩, ha, hb⟩
      subst ha
      rcases h with h | ⟨h, _⟩ | ⟨_, h⟩
      · omega
      · exact absurd h hcT
      · exact ⟨rfl, h⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨by omega, Or.inr (Or.inr ⟨hcT, rfl⟩)⟩, rfl, by omega⟩

lemma card_stripBlackout {m : ℕ} {e : ℤ} (he : e ∈ Finset.Icc (1 : ℤ) m)
    {T : Finset ℤ} (hT : T ⊆ (Finset.Icc (1 : ℤ) m).erase e) :
    (stripBlackout m e T).card = m + 1 := by
  rw [card_eq_sum_cols (stripBlackout_subset m e T), ← Finset.add_sum_erase _ _ he]
  have h1 : (stripBlackout m e T ∩ col e).card = 2 := by
    rw [Finset.inter_eq_right.mpr ((col_subset_stripBlackout_iff he hT e).mpr rfl), card_col]
  have h2 : ∑ c ∈ (Finset.Icc (1 : ℤ) m).erase e, (stripBlackout m e T ∩ col c).card =
      ((Finset.Icc (1 : ℤ) m).erase e).card * 1 := by
    apply Finset.sum_const_nat
    intro c hc
    rw [inter_col_stripBlackout he hT hc]
    split_ifs <;> simp
  rw [h1, h2, Finset.card_erase_of_mem he, Int.card_Icc]
  have hm : 1 ≤ m := by rw [Finset.mem_Icc] at he; omega
  simp only [add_sub_cancel_right, Int.toNat_natCast, mul_one]
  omega

lemma valid_stripBlackout {m : ℕ} (hm : 3 ≤ m) {e : ℤ} (he : e ∈ Finset.Icc (1 : ℤ) m)
    {T : Finset ℤ} (hT : T ⊆ (Finset.Icc (1 : ℤ) m).erase e) : Valid 2 m (stripBlackout m e T) := by
  rw [valid_strip_iff hm]
  intro p q _ _ _ _ hp hq
  rw [col_subset_stripBlackout_iff he hT] at hp hq
  rw [hp, hq]

/-- **Characterization of the maximum blackouts.** For `m ≥ 3`, a blackout `S ⊆ grid 2 m` is
valid with `m + 1` points iff it is `stripBlackout m e T` for a column `e` and a set `T` of
other columns: one column fully blacked out, exactly one point blacked out in every other
column. -/
theorem max_strip_iff {m : ℕ} (hm : 3 ≤ m) {S : Finset Pt} (hS : S ⊆ grid 2 m) :
    (Valid 2 m S ∧ S.card = m + 1) ↔
      ∃ e ∈ Finset.Icc (1 : ℤ) m, ∃ T ⊆ (Finset.Icc (1 : ℤ) m).erase e,
        S = stripBlackout m e T := by
  constructor
  · rintro ⟨hv, hcard⟩
    -- exactly one full column
    have hF1 : (fullCols m S).card = 1 := by
      have := card_le_add_fullCols hS
      have := card_fullCols_le_one hm hv
      omega
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp hF1
    have heI : e ∈ Finset.Icc (1 : ℤ) m := by
      have : e ∈ fullCols m S := by rw [he]; exact Finset.mem_singleton_self e
      exact (Finset.mem_filter.mp this).1
    have hecol : col e ⊆ S := by
      have : e ∈ fullCols m S := by rw [he]; exact Finset.mem_singleton_self e
      exact (Finset.mem_filter.mp this).2
    have hfull : ∀ c, col c ⊆ S → c ∈ Finset.Icc (1 : ℤ) m → c = e := by
      intro c hc hcI
      have : c ∈ fullCols m S := Finset.mem_filter.mpr ⟨hcI, hc⟩
      rw [he] at this
      exact Finset.mem_singleton.mp this
    -- every other column contains exactly one point of `S`
    have hone : ∀ c ∈ Finset.Icc (1 : ℤ) m, c ≠ e → (S ∩ col c).card = 1 := by
      have hsum : ∑ c ∈ Finset.Icc (1 : ℤ) m, (S ∩ col c).card =
          ∑ c ∈ Finset.Icc (1 : ℤ) m, (1 + if col c ⊆ S then 1 else 0) := by
        rw [← card_eq_sum_cols hS, hcard, Finset.sum_add_distrib, Finset.sum_const,
          ← Finset.card_filter, Int.card_Icc, smul_eq_mul, mul_one]
        have : ((Finset.Icc (1 : ℤ) m).filter (fun c => col c ⊆ S)).card = 1 := hF1
        rw [this]
        simp
      have hpt := (Finset.sum_eq_sum_iff_of_le (fun c _ => inter_col_card_le S c)).mp hsum
      intro c hc hce
      have := hpt c hc
      rw [if_neg (fun h => hce (hfull c h hc))] at this
      omega
    refine ⟨e, heI, ((Finset.Icc (1 : ℤ) m).erase e).filter (fun c => ((c, 2) : Pt) ∈ S),
      Finset.filter_subset _ _, ?_⟩
    ext ⟨a, b⟩
    rw [mem_stripBlackout']
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]
    constructor
    · intro hy
      have hg := mem_grid'.mp (hS hy)
      refine ⟨hg, ?_⟩
      by_cases hae : a = e
      · exact Or.inl hae
      · have hcard1 := hone a (Finset.mem_Icc.mpr ⟨hg.1, hg.2.1⟩) hae
        rcases (by omega : b = 2 ∨ b = 1) with rfl | rfl
        · exact Or.inr (Or.inl ⟨⟨⟨hae, hg.1, hg.2.1⟩, hy⟩, rfl⟩)
        · refine Or.inr (Or.inr ⟨?_, rfl⟩)
          rintro ⟨-, h2⟩
          have hmem1 : ((a, 1) : Pt) ∈ S ∩ col a := Finset.mem_inter.mpr ⟨hy, by simp [col]⟩
          have hmem2 : ((a, 2) : Pt) ∈ S ∩ col a := Finset.mem_inter.mpr ⟨h2, by simp [col]⟩
          have := Finset.card_le_one.mp hcard1.le _ hmem1 _ hmem2
          simp at this
    · rintro ⟨hg, h⟩
      rcases h with rfl | ⟨⟨_, h2⟩, rfl⟩ | ⟨hnot, rfl⟩
      · exact hecol (mem_col.mpr ⟨rfl, by omega⟩)
      · exact h2
      · by_cases hae : a = e
        · exact hecol (mem_col.mpr ⟨hae, Or.inl rfl⟩)
        · have hcard1 := hone a (Finset.mem_Icc.mpr ⟨hg.1, hg.2.1⟩) hae
          obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard1
          have hzmem : z ∈ S ∩ col a := by rw [hz]; exact Finset.mem_singleton_self z
          rw [Finset.mem_inter, mem_col] at hzmem
          obtain ⟨hzS, hz1, hz2⟩ := hzmem
          have h2 : ((a, 2) : Pt) ∉ S := fun h => hnot ⟨⟨hae, hg.1, hg.2.1⟩, h⟩
          obtain ⟨z1, z2⟩ := z
          dsimp only at hz1 hz2
          subst hz1
          rcases hz2 with rfl | rfl
          · exact hzS
          · exact absurd hzS h2
  · rintro ⟨e, he, T, hT, rfl⟩
    exact ⟨valid_stripBlackout hm he hT, card_stripBlackout he hT⟩

lemma stripBlackout_injOn (m : ℕ) :
    Set.InjOn (fun x : Σ _ : ℤ, Finset ℤ => stripBlackout m x.1 x.2)
      ((Finset.Icc (1 : ℤ) m).sigma (fun e => ((Finset.Icc (1 : ℤ) m).erase e).powerset)) := by
  rintro ⟨e, T⟩ hx ⟨e', T'⟩ hy hxy
  simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_powerset] at hx hy
  simp only at hxy
  have hee : e = e' := by
    have h := (col_subset_stripBlackout_iff hy.1 hy.2 e).mp
      (hxy ▸ (col_subset_stripBlackout_iff hx.1 hx.2 e).mpr rfl)
    exact h
  subst hee
  have hTT : T = T' := by
    ext c
    constructor
    · intro hc
      have hce : c ≠ e := (Finset.mem_erase.mp (hx.2 hc)).1
      have hcI : 1 ≤ c ∧ c ≤ m := Finset.mem_Icc.mp (Finset.mem_erase.mp (hx.2 hc)).2
      have hmem : ((c, 2) : Pt) ∈ stripBlackout m e T :=
        mem_stripBlackout'.mpr ⟨by omega, Or.inr (Or.inl ⟨hc, rfl⟩)⟩
      rw [hxy, mem_stripBlackout'] at hmem
      rcases hmem.2 with h | ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h hce
      · exact h
      · omega
    · intro hc
      have hce : c ≠ e := (Finset.mem_erase.mp (hy.2 hc)).1
      have hcI : 1 ≤ c ∧ c ≤ m := Finset.mem_Icc.mp (Finset.mem_erase.mp (hy.2 hc)).2
      have hmem : ((c, 2) : Pt) ∈ stripBlackout m e T' :=
        mem_stripBlackout'.mpr ⟨by omega, Or.inr (Or.inl ⟨hc, rfl⟩)⟩
      rw [← hxy, mem_stripBlackout'] at hmem
      rcases hmem.2 with h | ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h hce
      · exact h
      · omega
  rw [hTT]

open Classical in
/-- **Counting.** For `m ≥ 3` there are exactly `m * 2^(m-1)` maximum blackouts of the strip. -/
theorem card_max_strip {m : ℕ} (hm : 3 ≤ m) :
    ((grid 2 m).powerset.filter (fun S => Valid 2 m S ∧ S.card = m + 1)).card =
      m * 2 ^ (m - 1) := by
  have himage : (grid 2 m).powerset.filter (fun S => Valid 2 m S ∧ S.card = m + 1) =
      ((Finset.Icc (1 : ℤ) m).sigma (fun e => ((Finset.Icc (1 : ℤ) m).erase e).powerset)).image
        (fun x : Σ _ : ℤ, Finset ℤ => stripBlackout m x.1 x.2) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, Finset.mem_sigma]
    constructor
    · rintro ⟨hS, hv, hcard⟩
      obtain ⟨e, he, T, hT, rfl⟩ := (max_strip_iff hm hS).mp ⟨hv, hcard⟩
      exact ⟨⟨e, T⟩, ⟨he, hT⟩, rfl⟩
    · rintro ⟨⟨e, T⟩, ⟨he, hT⟩, rfl⟩
      exact ⟨stripBlackout_subset m e T, valid_stripBlackout hm he hT, card_stripBlackout he hT⟩
  rw [himage, Finset.card_image_of_injOn (stripBlackout_injOn m), Finset.card_sigma]
  have hterm : ∀ e ∈ Finset.Icc (1 : ℤ) m,
      (((Finset.Icc (1 : ℤ) m).erase e).powerset).card = 2 ^ (m - 1) := by
    intro e he
    rw [Finset.card_powerset, Finset.card_erase_of_mem he, Int.card_Icc]
    simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Int.card_Icc]
  simp

open Classical in
/-- **The Strip Theorem** (`m ≥ 3`).  Every valid blackout of the `2 × m` strip has at most
`m + 1` points; the bound is attained; the maximum blackouts are exactly the `stripBlackout m e T`
(the complements of kept sets with one survivor per column, missing exactly one column); and
there are exactly `m * 2^(m-1)` of them. -/
theorem strip_theorem {m : ℕ} (hm : 3 ≤ m) :
    (∀ S ⊆ grid 2 m, Valid 2 m S → S.card ≤ m + 1) ∧
    (∃ S ⊆ grid 2 m, Valid 2 m S ∧ S.card = m + 1) ∧
    (∀ S ⊆ grid 2 m, (Valid 2 m S ∧ S.card = m + 1) ↔
      ∃ e ∈ Finset.Icc (1 : ℤ) m, ∃ T ⊆ (Finset.Icc (1 : ℤ) m).erase e,
        S = stripBlackout m e T) ∧
    ((grid 2 m).powerset.filter (fun S => Valid 2 m S ∧ S.card = m + 1)).card =
      m * 2 ^ (m - 1) := by
  have h1 : (1 : ℤ) ∈ Finset.Icc (1 : ℤ) m := by rw [Finset.mem_Icc]; omega
  refine ⟨fun S hS hv => card_le_of_valid hm hS hv, ?_, fun S hS => max_strip_iff hm hS,
    card_max_strip hm⟩
  exact ⟨stripBlackout m 1 ∅, stripBlackout_subset m 1 ∅,
    valid_stripBlackout hm h1 (Finset.empty_subset _), card_stripBlackout h1 (Finset.empty_subset _)⟩

end Kagey001
