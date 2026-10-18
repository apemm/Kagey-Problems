import KageyProblems.Problem001.Foundations

/-!
# Kagey's Problem 001 — the rectangle class as a finite list

`Rects n m` in `KageyProblems/Problem001.lean` (the conventions of Section 2 of
`problem001/jis/pemmasani.tex`) is defined by an existential over all integer vectors, so
`Valid n m S` is not a finite check as it stands. This file proves that the rectangles of the
grid are exactly the corner sets of an explicit finite family of point triples. That makes
`Valid` decidable, and the Lean kernel can then evaluate it on concrete blackouts
(`Problem001/Kernel.lean`). It is the Lean counterpart of the rectangle enumerators of
Section 9, which list every rectangle of a board and compare the presentations.

A triple `(p, q, r)` stands for the rectangle with corner `p`, the two corners `q`, `r`
adjacent to `p`, and the opposite corner `q + r - p`. To list each rectangle once, `p` is the
lexicographically least corner and `q < r` lexicographically.

## Contents

* `gridC`, `grid_eq_gridC`: a computable copy of `grid`.
* `triples n m`, `corners`: the finite family of canonical triples and their corner sets.
* `mem_Rects_iff`: a corner set lies in `Rects n m` if and only if it is the corner set of a
  canonical triple (both directions); `rects_eq_image` states it as an equality of sets.
* `valid_iff_triples`, `valid_iff_validWith`: `Valid n m S` holds if and only if the
  presentation map is injective on that finite list; the instance `decValid` makes
  `Valid n m` decidable.
* `card_le_of_layer`: since validity passes to subsets (`Valid.mono`), if no subset of the grid
  with `k + 1` points is valid, then every valid blackout has at most `k` points;
  `filter_powerset_eq_layer` identifies the valid blackouts of size `k` with one layer of the
  powerset.
-/

namespace Kagey001

open Finset

/-- Lexicographic strict order on points (first the column, then the row). -/
def lexLt (p q : Pt) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

instance : DecidableRel lexLt := fun p q => by unfold lexLt; infer_instance

lemma lexLt_ne {p q : Pt} (h : lexLt p q) : p ≠ q := by
  rintro rfl
  rcases h with h | ⟨_, h⟩ <;> exact lt_irrefl _ h

lemma lexLt_trans {p q r : Pt} (h1 : lexLt p q) (h2 : lexLt q r) : lexLt p r := by
  unfold lexLt at *
  omega

lemma lexLt_trichotomy (p q : Pt) : lexLt p q ∨ p = q ∨ lexLt q p := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  unfold lexLt
  simp only [Prod.mk.injEq]
  omega

/-- A computable copy of `grid` (the Mathlib `Finset.Icc` on `ℤ` used by `grid` goes through a
noncomputable order instance). -/
def gridC (n m : ℕ) : Finset Pt :=
  (Finset.range m ×ˢ Finset.range n).image (fun ij => ((ij.1 : ℤ) + 1, (ij.2 : ℤ) + 1))

lemma grid_eq_gridC (n m : ℕ) : grid n m = gridC n m := by
  ext ⟨a, b⟩
  rw [mem_grid']
  simp only [gridC, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists,
    Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(a - 1).toNat, (b - 1).toNat, ⟨by omega, by omega⟩, by omega, by omega⟩
  · rintro ⟨i, j, ⟨hi, hj⟩, rfl, rfl⟩
    omega

lemma mem_gridC {n m : ℕ} {y : Pt} :
    y ∈ gridC n m ↔ 1 ≤ y.1 ∧ y.1 ≤ m ∧ 1 ≤ y.2 ∧ y.2 ≤ n := by
  rw [← grid_eq_gridC, mem_grid]

/-- The corner set of the triple `(p, q, r)`. -/
def corners (t : Pt × Pt × Pt) : Finset Pt := {t.1, t.2.1, t.2.2, t.2.1 + t.2.2 - t.1}

/-- The canonical triples: right angle at `p`, `p` lexicographically least, `q < r`, and the
fourth corner inside the grid. -/
def goodTriple (n m : ℕ) (t : Pt × Pt × Pt) : Prop :=
  (t.2.1 - t.1).1 * (t.2.2 - t.1).1 + (t.2.1 - t.1).2 * (t.2.2 - t.1).2 = 0 ∧
    lexLt t.1 t.2.1 ∧ lexLt t.2.1 t.2.2 ∧ lexLt t.1 (t.2.1 + t.2.2 - t.1) ∧
    (1 ≤ (t.2.1 + t.2.2 - t.1).1 ∧ (t.2.1 + t.2.2 - t.1).1 ≤ m ∧
      1 ≤ (t.2.1 + t.2.2 - t.1).2 ∧ (t.2.1 + t.2.2 - t.1).2 ≤ n)

instance (n m : ℕ) : DecidablePred (goodTriple n m) := fun t => by
  unfold goodTriple; infer_instance

/-- The finite family of canonical triples of the `n × m` grid. -/
def triples (n m : ℕ) : Finset (Pt × Pt × Pt) :=
  (gridC n m ×ˢ gridC n m ×ˢ gridC n m).filter (goodTriple n m)

lemma mem_triples {n m : ℕ} {t : Pt × Pt × Pt} :
    t ∈ triples n m ↔ (t.1 ∈ gridC n m ∧ t.2.1 ∈ gridC n m ∧ t.2.2 ∈ gridC n m) ∧
      goodTriple n m t := by
  simp [triples, Finset.mem_filter, Finset.mem_product]

/-- Every canonical triple gives a rectangle of the grid. -/
lemma corners_mem_Rects {n m : ℕ} {t : Pt × Pt × Pt} (ht : t ∈ triples n m) :
    corners t ∈ Rects n m := by
  obtain ⟨p, q, r⟩ := t
  rw [mem_triples] at ht
  obtain ⟨⟨hp, hq, hr⟩, hperp, hpq, hqr, _, ho⟩ := ht
  refine ⟨⟨p, q - p, r - p, ?_, ?_, hperp, ?_⟩, ?_⟩
  · exact sub_ne_zero.mpr (lexLt_ne hpq).symm
  · exact sub_ne_zero.mpr (lexLt_ne (lexLt_trans hpq hqr)).symm
  · simp only [corners]
    congr 1
    · congr 1
      · abel
      · congr 1
        · abel
        · congr 1
          abel
  · intro y hy
    simp only [corners, Finset.mem_insert, Finset.mem_singleton] at hy
    rw [grid_eq_gridC]
    rcases hy with rfl | rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
    · exact mem_gridC.mpr ho

/-- One corner `x` with neighbours `y`, `z`: if `x` is lexicographically below the other three
corners, the rectangle is the corner set of a canonical triple. -/
lemma exists_triple_of_min {n m : ℕ} {x y z : Pt}
    (hperp : (y - x).1 * (z - x).1 + (y - x).2 * (z - x).2 = 0)
    (hxy : lexLt x y) (hxz : lexLt x z) (hxo : lexLt x (y + z - x)) (hyz : y ≠ z)
    (hx : x ∈ gridC n m) (hy : y ∈ gridC n m) (hz : z ∈ gridC n m)
    (ho : y + z - x ∈ gridC n m) :
    ∃ t ∈ triples n m, corners t = {x, y, z, y + z - x} := by
  rcases lexLt_trichotomy y z with h | h | h
  · exact ⟨(x, y, z), mem_triples.mpr ⟨⟨hx, hy, hz⟩, hperp, hxy, h, hxo, mem_gridC.mp ho⟩, rfl⟩
  · exact absurd h hyz
  · refine ⟨(x, z, y), mem_triples.mpr ⟨⟨hx, hz, hy⟩, ?_, hxz, h, ?_, ?_⟩, ?_⟩
    · linear_combination hperp
    · rwa [add_comm]
    · rw [add_comm]; exact mem_gridC.mp ho
    · simp only [corners]
      rw [Finset.insert_comm z y, add_comm z y]

/-- Every nonempty finite set of points has a lexicographically least element. -/
lemma exists_lexMin (s : Finset Pt) (hs : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, lexLt x y ∨ x = y := by
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert e s he ih =>
    rcases s.eq_empty_or_nonempty with hs' | hs'
    · subst hs'
      refine ⟨e, by simp, fun y hy => Or.inr ?_⟩
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hy
      exact hy.symm
    · obtain ⟨x, hx, hmin⟩ := ih hs'
      rcases lexLt_trichotomy e x with h | h | h
      · refine ⟨e, Finset.mem_insert_self _ _, fun y hy => ?_⟩
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Or.inr rfl
        · rcases hmin y hy with h' | rfl
          · exact Or.inl (lexLt_trans h h')
          · exact Or.inl h
      · refine ⟨e, Finset.mem_insert_self _ _, fun y hy => ?_⟩
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Or.inr rfl
        · subst h; exact hmin y hy
      · refine ⟨x, Finset.mem_insert_of_mem hx, fun y hy => ?_⟩
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Or.inl h
        · exact hmin y hy

lemma lexLt_of_le_ne {x y : Pt} (h : lexLt x y ∨ x = y) (hne : x ≠ y) : lexLt x y := by
  rcases h with h | h
  · exact h
  · exact absurd h hne

/-- The four corners of a non-degenerate rectangle are pairwise distinct. -/
lemma corners_distinct {p u v : Pt} (hu : u ≠ 0) (hv : v ≠ 0)
    (hperp : u.1 * v.1 + u.2 * v.2 = 0) :
    p ≠ p + u ∧ p ≠ p + v ∧ p ≠ p + u + v ∧ p + u ≠ p + v ∧ p + u ≠ p + u + v ∧
      p + v ≠ p + u + v := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  simp only [ne_eq, Prod.mk_eq_zero, not_and_or] at hu hv
  dsimp only at hperp
  have hsq : ∀ a b : ℤ, a * a + b * b = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    constructor <;> nlinarith [mul_self_nonneg a, mul_self_nonneg b]
  simp only [Prod.mk_add_mk, ne_eq, Prod.mk.injEq]
  refine ⟨by omega, by omega, ?_, ?_, by omega, by omega⟩
  · intro ⟨h1, h2⟩
    have e1 : v1 = -u1 := by omega
    have e2 : v2 = -u2 := by omega
    rw [e1, e2] at hperp
    have := hsq u1 u2 (by linarith)
    omega
  · intro ⟨h1, h2⟩
    have e1 : v1 = u1 := by omega
    have e2 : v2 = u2 := by omega
    rw [e1, e2] at hperp
    have := hsq u1 u2 (by linarith)
    omega

/-- **Bridge.** The rectangles of the grid are exactly the corner sets of canonical triples. -/
theorem mem_Rects_iff {n m : ℕ} {C : Finset Pt} :
    C ∈ Rects n m ↔ ∃ t ∈ triples n m, corners t = C := by
  constructor
  · rintro ⟨⟨p, u, v, hu, hv, hperp, rfl⟩, hsub⟩
    rw [grid_eq_gridC] at hsub
    have ha : p ∈ gridC n m := hsub (by simp)
    have hb : p + u ∈ gridC n m := hsub (by simp)
    have hc : p + v ∈ gridC n m := hsub (by simp)
    have hd : p + u + v ∈ gridC n m := hsub (by simp)
    obtain ⟨nab, nac, nad, nbc, nbd, ncd⟩ := corners_distinct (p := p) hu hv hperp
    have hbca : p + u + (p + v) - p = p + u + v := by abel
    have hadb : p + (p + u + v) - (p + u) = p + v := by abel
    have hadc : p + (p + u + v) - (p + v) = p + u := by abel
    have hbcd : p + u + (p + v) - (p + u + v) = p := by abel
    have e1 : p + u - p = u := by abel
    have e2 : p + v - p = v := by abel
    have e3 : p - (p + u) = -u := by abel
    have e4 : p + u + v - (p + u) = v := by abel
    have e5 : p - (p + v) = -v := by abel
    have e6 : p + u + v - (p + v) = u := by abel
    have e7 : p + u - (p + u + v) = -v := by abel
    have e8 : p + v - (p + u + v) = -u := by abel
    obtain ⟨x, hx, hmin⟩ := exists_lexMin ({p, p + u, p + v, p + u + v} : Finset Pt) (by simp)
    have ma := hmin p (by simp)
    have mb := hmin (p + u) (by simp)
    have mc := hmin (p + v) (by simp)
    have md := hmin (p + u + v) (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h <;> rw [h] at ma mb mc md
    · -- `p` is least: neighbours `p + u`, `p + v`
      obtain ⟨t, ht, he⟩ := exists_triple_of_min (n := n) (m := m) (x := p) (y := p + u)
        (z := p + v) (by rw [e1, e2]; exact hperp)
        (lexLt_of_le_ne mb nab) (lexLt_of_le_ne mc nac)
        (by rw [hbca]; exact lexLt_of_le_ne md nad) nbc ha hb hc (by rw [hbca]; exact hd)
      exact ⟨t, ht, by rw [he, hbca]⟩
    · -- `p + u` is least: neighbours `p`, `p + u + v`
      obtain ⟨t, ht, he⟩ := exists_triple_of_min (n := n) (m := m) (x := p + u) (y := p)
        (z := p + u + v)
        (by rw [e3, e4]; simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination -hperp)
        (lexLt_of_le_ne ma (Ne.symm nab)) (lexLt_of_le_ne md nbd)
        (by rw [hadb]; exact lexLt_of_le_ne mc nbc) nad hb ha hd (by rw [hadb]; exact hc)
      refine ⟨t, ht, ?_⟩
      rw [he, hadb]
      ext w
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]
    · -- `p + v` is least: neighbours `p`, `p + u + v`
      obtain ⟨t, ht, he⟩ := exists_triple_of_min (n := n) (m := m) (x := p + v) (y := p)
        (z := p + u + v)
        (by rw [e5, e6]; simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination -hperp)
        (lexLt_of_le_ne ma (Ne.symm nac)) (lexLt_of_le_ne md ncd)
        (by rw [hadc]; exact lexLt_of_le_ne mb (Ne.symm nbc)) nad hc ha hd
        (by rw [hadc]; exact hb)
      refine ⟨t, ht, ?_⟩
      rw [he, hadc]
      ext w
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]
    · -- `p + u + v` is least: neighbours `p + u`, `p + v`
      obtain ⟨t, ht, he⟩ := exists_triple_of_min (n := n) (m := m) (x := p + u + v)
        (y := p + u) (z := p + v)
        (by rw [e7, e8]; simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination hperp)
        (lexLt_of_le_ne mb (Ne.symm nbd)) (lexLt_of_le_ne mc (Ne.symm ncd))
        (by rw [hbcd]; exact lexLt_of_le_ne ma (Ne.symm nad)) nbc hd hb hc
        (by rw [hbcd]; exact ha)
      refine ⟨t, ht, ?_⟩
      rw [he, hbcd]
      ext w
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
  · rintro ⟨t, ht, rfl⟩
    exact corners_mem_Rects ht

/-- The rectangle class as an explicit finite set. -/
theorem rects_eq_image (n m : ℕ) : Rects n m = ↑((triples n m).image corners) := by
  ext C
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact mem_Rects_iff

/-- **Bridge for validity.** -/
theorem valid_iff_triples (n m : ℕ) (S : Finset Pt) :
    Valid n m S ↔ ∀ t₁ ∈ triples n m, ∀ t₂ ∈ triples n m,
      corners t₁ \ S = corners t₂ \ S → corners t₁ = corners t₂ := by
  constructor
  · intro h t₁ h₁ t₂ h₂ hp
    exact h _ (corners_mem_Rects h₁) _ (corners_mem_Rects h₂) hp
  · intro h C₁ h₁ C₂ h₂ hp
    obtain ⟨t₁, ht₁, rfl⟩ := mem_Rects_iff.mp h₁
    obtain ⟨t₂, ht₂, rfl⟩ := mem_Rects_iff.mp h₂
    exact h t₁ ht₁ t₂ ht₂ hp

instance decValid (n m : ℕ) : DecidablePred (Valid n m) := fun S =>
  decidable_of_iff _ (valid_iff_triples n m S).symm

/-! ### A form with the rectangle list computed once -/

/-- The corner sets of all canonical triples, as a multiset (each rectangle once). -/
def rectMS (n m : ℕ) : Multiset (Finset Pt) := (triples n m).val.map corners

/-- Injectivity of the presentation map on an explicit list of corner sets. -/
def validWith (L : Multiset (Finset Pt)) (S : Finset Pt) : Prop :=
  ∀ C₁ ∈ L, ∀ C₂ ∈ L, C₁ \ S = C₂ \ S → C₁ = C₂

instance (L : Multiset (Finset Pt)) : DecidablePred (validWith L) := fun S => by
  unfold validWith; infer_instance

theorem valid_iff_validWith (n m : ℕ) (S : Finset Pt) :
    Valid n m S ↔ validWith (rectMS n m) S := by
  rw [valid_iff_triples]
  simp only [validWith, rectMS, Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro h _ ⟨t₁, h₁, rfl⟩ _ ⟨t₂, h₂, rfl⟩ hp
    exact h t₁ h₁ t₂ h₂ hp
  · intro h t₁ h₁ t₂ h₂ hp
    exact h _ ⟨t₁, h₁, rfl⟩ _ ⟨t₂, h₂, rfl⟩ hp

theorem filter_valid_eq (n m : ℕ) (P : Finset (Finset Pt)) :
    P.filter (Valid n m) = P.filter (validWith (rectMS n m)) :=
  Finset.filter_congr (fun S _ => valid_iff_validWith n m S)

/-! ### Reducing maximality to one layer of subsets -/

/-- If no `(k+1)`-point subset of the grid is a valid blackout, every valid blackout inside
the grid has at most `k` points (validity is inherited by subsets). -/
theorem card_le_of_layer {n m k : ℕ}
    (h : ∀ T ∈ (grid n m).powersetCard (k + 1), ¬ Valid n m T) :
    ∀ S ⊆ grid n m, Valid n m S → S.card ≤ k := by
  intro S hS hv
  by_contra hlt
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (s := S) (n := k + 1) (by omega)
  exact h T (Finset.mem_powersetCard.mpr ⟨hTS.trans hS, hT⟩) (hv.mono hTS)

/-- The optima of size `k` as a single layer of the powerset. -/
theorem filter_powerset_eq_layer (n m k : ℕ) :
    (grid n m).powerset.filter (fun S => Valid n m S ∧ S.card = k) =
      ((grid n m).powersetCard k).filter (Valid n m) := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
  tauto

end Kagey001
