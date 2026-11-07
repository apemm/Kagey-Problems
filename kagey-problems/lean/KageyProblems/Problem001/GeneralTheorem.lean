import KageyProblems.Problem001.GeneralLocal
import KageyProblems.Problem001.AxisCycles
import KageyProblems.Problem001.CollarBoards

/-!
# Kagey's Problem 001 — the general theorem

The general theorem of Section "Every height at large widths" (Theorem "large widths") of `problem001/jis/pemmasani.tex`: for every
`h ≥ 3` and every `m ≥ M_h = q_h + (q_h - 1)(2 W_h + 1)`, where `q_h = ⌊h²/4⌋` and
`W_h = 1 + ⌊(h-1)²/4⌋`, the maximum size of a valid blackout of the `h × m` grid is
`m + q_h`. The upper bound is the row bound; the lower bound is the Proposition on
alternating boundary seas, for an arbitrary triangle-free graph on the rows, applied to
`K_{⌊h/2⌋, ⌈h/2⌉}`.

This Lean verification code was generated with Claude Opus 5.5.

## Contents

* `altSea h m q pos E`: the blackout with doubles in the columns `pos 0, …, pos (q-1)`, the
  double in column `pos j` black in the two rows of the edge `E j`, and every other column
  black only in its sea row `seaRow`: row `1` left of the first double, switching between
  row `1` and row `h` at each double (`seaRowAfter h j` after `j` doubles). Columns before
  the first and after the last double are sea columns.
* `AltHyp h m q pos E`: the hypotheses of the Proposition. The doubles lie in the grid at least
  `2 W_h + 2` columns apart, and `E 0, …, E (q-1)` are distinct edges `(a, b)`, `a < b`, of a
  triangle-free graph on the rows.
* `AltHyp.local_model`: near a double the blackout is the local model of `GeneralLocal.lean`;
  `AltHyp.locality`: a tilted rectangle with two black corners lies within `W_h` columns of a
  double; `AltHyp.weak`: such a rectangle shows exactly two points, in one of the shapes
  `WeakST`.
* `AltHyp.no_four`, `AltHyp.no_six`: no black four- or six-cycle (distinct edges, no
  triangle), so axis-aligned rectangles never collide (`axis_collision_cycle`).
* `AltHyp.valid`, `AltHyp.card`, `AltHyp.subset_grid`, `AltHyp.alt_sea`: **the Proposition**.
  The blackout is a valid blackout of the `h × m` grid with `m + q` points.
* `bipE`, `bipPos`, `bip_hyp`: the edges of `K_{⌊h/2⌋, ⌈h/2⌉}` (`half_mul_half`: there are
  `⌊h²/4⌋` of them) in the columns `1, 1 + (2 W_h + 2), …`, which fit when `m ≥ M_h` (`Mh`).
* `general_theorem`, `fval_general`: **the theorem**, `f(h, m) = m + ⌊h²/4⌋` for `h ≥ 3` and
  `m ≥ M_h`.
-/

namespace Kagey001

open Finset

/-! ### The alternating boundary sea -/

/-- The number of doubles strictly left of column `x`. -/
def seaCnt (q : ℕ) (pos : ℕ → ℤ) (x : ℤ) : ℕ := ((range q).filter (fun j => pos j < x)).card

/-- The sea row after `j` doubles: row `1` for even `j`, row `h` for odd `j`. -/
def seaRowAfter (h j : ℕ) : ℤ := if Even j then 1 else h

/-- The sea row of column `x`. -/
def seaRow (h q : ℕ) (pos : ℕ → ℤ) (x : ℤ) : ℤ := seaRowAfter h (seaCnt q pos x)

/-- The alternating-boundary-sea blackout of the `h × m` grid with doubles in the columns
`pos 0 < … < pos (q-1)`, the double in column `pos j` black in the rows `(E j).1` and
`(E j).2`, and every other column black only in its sea row. -/
noncomputable def altSea (h m q : ℕ) (pos : ℕ → ℤ) (E : ℕ → ℤ × ℤ) : Finset Pt :=
  ((Icc (1 : ℤ) m \ (range q).image pos).image (fun x => (x, seaRow h q pos x))) ∪
    ((range q).image (fun j => (pos j, (E j).1)) ∪ (range q).image (fun j => (pos j, (E j).2)))

/-- Rows `x` and `y` are joined by an edge of the graph `E`. -/
def Adj (q : ℕ) (E : ℕ → ℤ × ℤ) (x y : ℤ) : Prop := ∃ j < q, E j = (x, y) ∨ E j = (y, x)

/-- The hypotheses of the Proposition: `h ≥ 3`, the doubles lie in the grid at least
`2 W_h + 2` columns apart, and `E` lists `q` distinct edges of a triangle-free graph on the
rows, each as a pair `(a, b)` with `1 ≤ a < b ≤ h`. -/
structure AltHyp (h m q : ℕ) (pos : ℕ → ℤ) (E : ℕ → ℤ × ℤ) : Prop where
  three_le : 3 ≤ h
  pos_mem : ∀ j < q, 1 ≤ pos j ∧ pos j ≤ m
  gap : ∀ j, j + 1 < q → pos j + 2 * spanW h + 2 ≤ pos (j + 1)
  edge : ∀ j < q, 1 ≤ (E j).1 ∧ (E j).1 < (E j).2 ∧ (E j).2 ≤ h
  inj : ∀ i < q, ∀ j < q, E i = E j → i = j
  tri : ∀ x y z : ℤ, Adj q E x y → Adj q E y z → Adj q E z x → False

variable {h m q : ℕ} {pos : ℕ → ℤ} {E : ℕ → ℤ × ℤ}

lemma seaRowAfter_cases (h j : ℕ) : seaRowAfter h j = 1 ∨ seaRowAfter h j = h := by
  unfold seaRowAfter; split_ifs <;> simp

lemma seaRowAfter_succ (h j : ℕ) : seaRowAfter h (j + 1) = h + 1 - seaRowAfter h j := by
  by_cases he : Even j <;> simp [seaRowAfter, he, Nat.even_add_one]

lemma seaCnt_succ (q : ℕ) (pos : ℕ → ℤ) (x : ℤ) :
    seaCnt (q + 1) pos x = seaCnt q pos x + if pos q < x then 1 else 0 := by
  unfold seaCnt
  rw [range_add_one, filter_insert]
  split_ifs with hq
  · rw [card_insert_of_notMem]
    simp [mem_filter]
  · simp

lemma seaCnt_le (q : ℕ) (pos : ℕ → ℤ) (x : ℤ) : seaCnt q pos x ≤ q :=
  (card_filter_le _ _).trans (card_range q).le

lemma seaCnt_mono (q : ℕ) (pos : ℕ → ℤ) {x x' : ℤ} (hx : x ≤ x') :
    seaCnt q pos x ≤ seaCnt q pos x' := by
  apply card_le_card
  intro j hj
  simp only [mem_filter] at hj ⊢
  exact ⟨hj.1, lt_of_lt_of_le hj.2 hx⟩

lemma cnt_spec_aux (pos : ℕ → ℤ) (x : ℤ) : ∀ q : ℕ,
    (∀ i j, i ≤ j → j < q → pos i ≤ pos j) → ∀ j < q, (pos j < x ↔ j < seaCnt q pos x)
  | 0 => by intro _ j hj; omega
  | q + 1 => by
    intro hmono j hj
    have ih := cnt_spec_aux pos x q (fun i j hij hj => hmono i j hij (by omega))
    have hle := seaCnt_le q pos x
    rw [seaCnt_succ]
    by_cases hq : pos q < x
    · rw [if_pos hq]
      have hall : seaCnt q pos x = q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · omega
        · have := (ih (q - 1) (by omega)).mp
            (lt_of_le_of_lt (hmono (q - 1) q (by omega) (by omega)) hq)
          omega
      have : pos j < x := lt_of_le_of_lt (hmono j q (by omega) (by omega)) hq
      constructor
      · intro; omega
      · intro; exact this
    · rw [if_neg hq, add_zero]
      rcases Nat.lt_or_ge j q with hjq | hjq
      · exact ih j hjq
      · have : j = q := by omega
        subst this
        constructor
        · intro h'; exact absurd h' hq
        · intro h'; omega

namespace AltHyp

variable (H : AltHyp h m q pos E)
include H

lemma pos_add (i : ℕ) : ∀ d : ℕ, i + d < q →
    pos i + (2 * (spanW h : ℤ) + 2) * d ≤ pos (i + d)
  | 0, _ => by simp
  | d + 1, hd => by
    have ih := pos_add i d (by omega)
    have hg := H.gap (i + d) (by omega)
    have e : i + (d + 1) = i + d + 1 := rfl
    rw [e]
    push_cast
    linarith

lemma pos_lt {i j : ℕ} (hij : i < j) (hj : j < q) : pos i + 2 * spanW h + 2 ≤ pos j := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + (d + 1) := ⟨j - i - 1, by omega⟩
  have := H.pos_add i (d + 1) hj
  have hW : (0 : ℤ) ≤ spanW h := by positivity
  have hd : (0 : ℤ) ≤ d := by positivity
  push_cast at this
  nlinarith

lemma mono : ∀ i j, i ≤ j → j < q → pos i ≤ pos j := by
  intro i j hij hj
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have := H.pos_lt hlt hj
    have hW : (0 : ℤ) ≤ spanW h := by positivity
    linarith

lemma pos_far {i j : ℕ} (hi : i < q) (hj : j < q) (hne : i ≠ j) :
    pos i + 2 * spanW h + 2 ≤ pos j ∨ pos j + 2 * spanW h + 2 ≤ pos i := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact Or.inl (H.pos_lt hlt hj)
  · exact Or.inr (H.pos_lt hlt hi)

lemma pos_inj {i j : ℕ} (hi : i < q) (hj : j < q) (he : pos i = pos j) : i = j := by
  by_contra hne
  have hW : (0 : ℤ) ≤ spanW h := by positivity
  rcases H.pos_far hi hj hne with h1 | h1 <;> omega

lemma cnt_spec {j : ℕ} (hj : j < q) (x : ℤ) : pos j < x ↔ j < seaCnt q pos x :=
  cnt_spec_aux pos x q H.mono j hj

lemma locHyp {j : ℕ} (hj : j < q) : LocHyp h (seaRowAfter h j) (E j).1 (E j).2 :=
  ⟨H.three_le, seaRowAfter_cases h j, (H.edge j hj).1, (H.edge j hj).2.1, (H.edge j hj).2.2⟩

end AltHyp

lemma mem_altSea {y : Pt} : y ∈ altSea h m q pos E ↔
    (1 ≤ y.1 ∧ y.1 ≤ m ∧ (∀ j < q, pos j ≠ y.1) ∧ y.2 = seaRow h q pos y.1) ∨
      (∃ j < q, y.1 = pos j ∧ (y.2 = (E j).1 ∨ y.2 = (E j).2)) := by
  obtain ⟨y1, y2⟩ := y
  simp only [altSea, mem_union, mem_image, mem_sdiff, mem_Icc, mem_range, Prod.mk.injEq,
    not_exists, not_and]
  constructor
  · rintro (⟨x, ⟨⟨h1, h2⟩, hx⟩, rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩)
    · exact Or.inl ⟨h1, h2, hx, rfl⟩
    · exact Or.inr ⟨j, hj, rfl, Or.inl rfl⟩
    · exact Or.inr ⟨j, hj, rfl, Or.inr rfl⟩
  · rintro (⟨h1, h2, hx, rfl⟩ | ⟨j, hj, rfl, h' | h'⟩)
    · exact Or.inl ⟨y1, ⟨⟨h1, h2⟩, hx⟩, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨j, hj, rfl, h'.symm⟩)
    · exact Or.inr (Or.inr ⟨j, hj, rfl, h'.symm⟩)

namespace AltHyp

variable (H : AltHyp h m q pos E)
include H

/-- **The local model.** Near the double in column `pos j`, the blackout is row `σ_j` to the
left, the edge `E j` in the column, and the other boundary row to the right. -/
theorem local_model {j : ℕ} (hj : j < q) {y : Pt} (hy : y ∈ grid h m)
    (hl : pos j - spanW h ≤ y.1) (hr : y.1 ≤ pos j + spanW h) :
    y ∈ altSea h m q pos E ↔ LBlack h (pos j) (seaRowAfter h j) (E j).1 (E j).2 y := by
  have hnd : ∀ i < q, pos i = y.1 → i = j := by
    intro i hi he
    by_contra hne
    rcases H.pos_far hi hj hne with h1 | h1 <;> omega
  have hcntL : y.1 < pos j → seaCnt q pos y.1 = j := by
    intro hlt
    have hle : seaCnt q pos y.1 ≤ j := by
      by_contra hc
      have := (H.cnt_spec hj y.1).mpr (by omega)
      omega
    by_contra hne
    have hlt' : seaCnt q pos y.1 < j := lt_of_le_of_ne hle hne
    have hiq : seaCnt q pos y.1 < q := by omega
    have h1 : ¬ pos (seaCnt q pos y.1) < y.1 :=
      fun h' => lt_irrefl _ ((H.cnt_spec hiq y.1).mp h')
    have h2 := H.pos_lt hlt' hj
    omega
  have hcntR : pos j < y.1 → seaCnt q pos y.1 = j + 1 := by
    intro hlt
    have h1 : j < seaCnt q pos y.1 := (H.cnt_spec hj y.1).mp hlt
    by_contra hne
    have h2 : j + 1 < seaCnt q pos y.1 := by omega
    have hq : j + 1 < q := lt_of_lt_of_le h2 (seaCnt_le q pos y.1)
    have h3 := (H.cnt_spec hq y.1).mpr h2
    have h4 := H.gap j hq
    omega
  rw [mem_altSea]
  simp only [LBlack]
  constructor
  · rintro (⟨h1, h2, hx, h3⟩ | ⟨i, hi, he, h3⟩)
    · rcases lt_trichotomy y.1 (pos j) with hlt | heq | hgt
      · left
        exact ⟨hlt, by rw [h3, seaRow, hcntL hlt]⟩
      · exact absurd heq.symm (hx j hj)
      · right; right
        exact ⟨hgt, by rw [h3, seaRow, hcntR hgt, seaRowAfter_succ]⟩
    · have := hnd i hi he.symm
      subst this
      right; left
      exact ⟨he, h3⟩
  · have hg := mem_grid.mp hy
    rintro (⟨hlt, h3⟩ | ⟨heq, h3⟩ | ⟨hgt, h3⟩)
    · left
      refine ⟨hg.1, hg.2.1, fun i hi he => ?_, by rw [h3, seaRow, hcntL hlt]⟩
      have := hnd i hi he
      subst this
      omega
    · right
      exact ⟨j, hj, heq, h3⟩
    · left
      refine ⟨hg.1, hg.2.1, fun i hi he => ?_, by rw [h3, seaRow, hcntR hgt, seaRowAfter_succ]⟩
      have := hnd i hi he
      subst this
      omega

/-- Between two sea columns with different sea rows lies a double. -/
theorem sea_step {x x' : ℤ} (hlt : x < x') (hx : ∀ j < q, pos j ≠ x)
    (hne : seaRow h q pos x ≠ seaRow h q pos x') : ∃ j < q, x < pos j ∧ pos j < x' := by
  have hmono := seaCnt_mono q pos hlt.le
  have hne' : seaCnt q pos x ≠ seaCnt q pos x' := fun he => hne (by rw [seaRow, seaRow, he])
  have hlt' : seaCnt q pos x < seaCnt q pos x' := lt_of_le_of_ne hmono hne'
  have hiq : seaCnt q pos x < q := lt_of_lt_of_le hlt' (seaCnt_le q pos x')
  refine ⟨seaCnt q pos x, hiq, ?_, (H.cnt_spec hiq x').mpr hlt'⟩
  have h1 : ¬ pos (seaCnt q pos x) < x := fun h' => lt_irrefl _ ((H.cnt_spec hiq x).mp h')
  have h2 := hx _ hiq
  omega

/-- **Locality.** A tilted rectangle with two black corners lies within `W_h` columns of a
double. -/
theorem locality {C : Finset Pt} (hC : C ∈ Rects h m) (ht : IsTilt C) {k k' : Pt}
    (hk : k ∈ C) (hk' : k' ∈ C) (hne : k ≠ k') (bk : k ∈ altSea h m q pos E)
    (bk' : k' ∈ altSea h m q pos E) :
    ∃ j < q, ∀ c ∈ C, pos j - spanW h ≤ c.1 ∧ c.1 ≤ pos j + spanW h := by
  have hrows : ∀ c ∈ C, 1 ≤ c.2 ∧ c.2 ≤ h := fun c hc => by
    have := mem_grid.mp (hC.2 hc)
    exact ⟨this.2.2.1, this.2.2.2⟩
  have span : ∀ e ∈ C, ∀ c ∈ C, c.1 - e.1 ≤ spanW h ∧ e.1 - c.1 ≤ spanW h :=
    fun e he c hc => ⟨ht.col_sub_le hrows hc he, ht.col_sub_le hrows he hc⟩
  rw [mem_altSea] at bk bk'
  rcases bk with ⟨-, -, hx, h3⟩ | ⟨j, hj, he, -⟩
  swap
  · exact ⟨j, hj, fun c hc => by have := span k hk c hc; omega⟩
  rcases bk' with ⟨-, -, hx', h3'⟩ | ⟨j, hj, he, -⟩
  swap
  · exact ⟨j, hj, fun c hc => by have := span k' hk' c hc; omega⟩
  have hrow : k.2 ≠ k'.2 := by
    intro he
    have hb : k.2 = 1 ∨ k.2 = h := by rw [h3]; exact seaRowAfter_cases h _
    exact hne (ht.eq_of_row_eq_bound hrows hb hk hk' rfl he.symm)
  have hcol : k.1 ≠ k'.1 := by
    intro he
    apply hrow
    rw [h3, h3', he]
  rcases lt_or_gt_of_ne hcol with hlt | hlt
  · obtain ⟨j, hj, hj1, hj2⟩ := H.sea_step hlt hx (by rw [← h3, ← h3']; exact hrow)
    exact ⟨j, hj, fun c hc => by
      have := span k hk c hc
      have := span k' hk' c hc
      omega⟩
  · obtain ⟨j, hj, hj1, hj2⟩ := H.sea_step hlt hx' (by rw [← h3, ← h3']; exact hrow.symm)
    exact ⟨j, hj, fun c hc => by
      have := span k hk c hc
      have := span k' hk' c hc
      omega⟩

/-- **Weak tilted rectangles.** A tilted rectangle of the grid showing at most two corners lies
near one double and shows exactly two points, in one of the three shapes of the local model. -/
theorem weak {C : Finset Pt} (hC : C ∈ Rects h m) (ht : IsTilt C)
    (hw : (pres (altSea h m q pos E) C).card ≤ 2) :
    ∃ j < q, (∀ c ∈ C, pos j - spanW h ≤ c.1 ∧ c.1 ≤ pos j + spanW h) ∧
      ∃ s t, pres (altSea h m q pos E) C = {s, t} ∧
        WeakST h (pos j) (seaRowAfter h j) (E j).1 (E j).2 C s t := by
  set Z := altSea h m q pos E with hZ
  have hcard := ht.isRect.card_eq_four
  have h2 : 1 < (C ∩ Z).card := by
    have := card_sdiff_add_card_inter C Z
    unfold pres at hw
    omega
  obtain ⟨k, hk, k', hk', hne⟩ := Finset.one_lt_card.mp h2
  rw [mem_inter] at hk hk'
  obtain ⟨j, hj, hloc⟩ := H.locality hC ht hk.1 hk'.1 hne hk.2 hk'.2
  have hL := H.locHyp hj
  have black : ∀ y ∈ C, (y ∈ Z ↔ LBlack h (pos j) (seaRowAfter h j) (E j).1 (E j).2 y) :=
    fun y hy => H.local_model hj (hC.2 hy) (hloc y hy).1 (hloc y hy).2
  obtain ⟨⟨x, y⟩, ⟨u1, u2⟩, ⟨v1, v2⟩, hu1, hu2, hv1, hv2, huv, hCeq⟩ := ht
  have hCt : C = tc x y u1 u2 v1 v2 := by
    rw [hCeq]
    simp only [tc, Prod.mk_add_mk]
  have row : ∀ c ∈ tc x y u1 u2 v1 v2, 1 ≤ c.2 ∧ c.2 ≤ h := fun c hc => by
    rw [← hCt] at hc
    have := mem_grid.mp (hC.2 hc)
    exact ⟨this.2.2.1, this.2.2.2⟩
  have g0 := row (x, y) (by simp [tc])
  have g1 := row (x + u1, y + u2) (by simp [tc])
  have g2 := row (x + v1, y + v2) (by simp [tc])
  have g3 := row (x + u1 + v1, y + u2 + v2) (by simp [tc])
  have hT : TiltOK h y u1 u2 v1 v2 :=
    ⟨hu1, hu2, hv1, hv2, huv, g0, g1, g2, g3⟩
  have hkC : k ∈ tc x y u1 u2 v1 v2 := hCt ▸ hk.1
  have hkC' : k' ∈ tc x y u1 u2 v1 v2 := hCt ▸ hk'.1
  obtain ⟨s, t, w⟩ := local_weak hL hT hkC hkC' hne ((black k hk.1).mp hk.2)
    ((black k' hk'.1).mp hk'.2)
  rw [← hCt] at w
  refine ⟨j, hj, hloc, s, t, ?_, w⟩
  obtain ⟨k1, k2, hC', b1, b2⟩ := w.black
  obtain ⟨ws, wt, -⟩ := w.white hL
  have hsC : s ∈ C := by rw [hC']; simp
  have htC : t ∈ C := by rw [hC']; simp
  have hk1 : k1 ∈ C := by rw [hC']; simp
  have hk2 : k2 ∈ C := by rw [hC']; simp
  have hsZ : s ∉ Z := fun h' => ws ((black s hsC).mp h')
  have htZ : t ∉ Z := fun h' => wt ((black t htC).mp h')
  have k1Z : k1 ∈ Z := (black k1 hk1).mpr b1
  have k2Z : k2 ∈ Z := (black k2 hk2).mpr b2
  ext z
  simp only [pres, mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hz, hzZ⟩
    rw [hC'] at hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact absurd k1Z hzZ
    · exact absurd k2Z hzZ
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨hsC, hsZ⟩
    · exact ⟨htC, htZ⟩

/-- A column with two black points is a double, black in the rows of its edge. -/
theorem two_black {x a b : ℤ} (hab : a ≠ b) (h1 : (x, a) ∈ altSea h m q pos E)
    (h2 : (x, b) ∈ altSea h m q pos E) :
    ∃ j < q, x = pos j ∧ (E j = (a, b) ∨ E j = (b, a)) := by
  rw [mem_altSea] at h1 h2
  dsimp only at h1 h2
  rcases h1 with ⟨-, -, hx, h3⟩ | ⟨i, hi, he, h3⟩ <;>
    rcases h2 with ⟨-, -, hx', h4⟩ | ⟨i', hi', he', h4⟩
  · exact absurd (h3.trans h4.symm) hab
  · exact absurd he'.symm (hx i' hi')
  · exact absurd he.symm (hx' i hi)
  · have := H.pos_inj hi hi' (he.symm.trans he')
    subst this
    refine ⟨i, hi, he, ?_⟩
    rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4
    · exact absurd (h3.trans h4.symm) hab
    · exact Or.inl (Prod.ext h3.symm h4.symm)
    · exact Or.inr (Prod.ext h4.symm h3.symm)
    · exact absurd (h3.trans h4.symm) hab

theorem no_four : ¬ BlackFourCycle (altSea h m q pos E) := by
  rintro ⟨i, i', j, j', hii, hjj, h1, h2, h3, h4⟩
  obtain ⟨k, hk, rfl, hk'⟩ := H.two_black hjj h1 h2
  obtain ⟨l, hl, he, hl'⟩ := H.two_black hjj h3 h4
  have hel := H.edge k hk
  have hel' := H.edge l hl
  have hkl : E k = E l := by
    rcases hk' with e | e <;> rcases hl' with e' | e'
    · rw [e, e']
    · rw [e] at hel; rw [e'] at hel'; dsimp only at hel hel'; omega
    · rw [e] at hel; rw [e'] at hel'; dsimp only at hel hel'; omega
    · rw [e, e']
  have := H.inj k hk l hl hkl
  subst this
  exact hii he.symm

theorem no_six : ¬ BlackSixCycle (altSea h m q pos E) := by
  rintro ⟨a, b, c, x, y, z, hab, hbc, hca, -, -, -, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨i, hi, -, e1⟩ := H.two_black hab h1 h2
  obtain ⟨j, hj, -, e2⟩ := H.two_black hbc h3 h4
  obtain ⟨k, hk, -, e3⟩ := H.two_black hca h5 h6
  exact H.tri a b c ⟨i, hi, e1⟩ ⟨j, hj, e2⟩ ⟨k, hk, e3⟩

/-- A weak tilted rectangle and an axis-aligned rectangle never have the same presentation. -/
theorem no_rival {C D : Finset Pt} (hC : C ∈ Rects h m) (hD : D ∈ Rects h m) (ht : IsTilt C)
    (ha : IsAxis D) (hw : (pres (altSea h m q pos E) C).card ≤ 2)
    (hp : pres (altSea h m q pos E) C = pres (altSea h m q pos E) D) : False := by
  set Z := altSea h m q pos E with hZ
  obtain ⟨j, hj, hloc, s, t, hpres, w⟩ := H.weak hC ht hw
  have hL := H.locHyp hj
  have hsP : s ∈ pres Z C := by rw [hpres]; simp
  have htP : t ∈ pres Z C := by rw [hpres]; simp
  have hsC : s ∈ C := (mem_sdiff.mp hsP).1
  have htC : t ∈ C := (mem_sdiff.mp htP).1
  have hsD : s ∈ D := (mem_sdiff.mp (hp ▸ hsP)).1
  have htD : t ∈ D := (mem_sdiff.mp (hp ▸ htP)).1
  refine axis_rival hL w ha hsD htD (fun y hy hys hyt hcol => ?_)
  have hyZ : y ∈ Z := by
    by_contra hn
    have : y ∈ pres Z D := mem_sdiff.mpr ⟨hy, hn⟩
    rw [← hp, hpres] at this
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact hys h'
    · exact hyt h'
  have hcl : pos j - spanW h ≤ y.1 ∧ y.1 ≤ pos j + spanW h := by
    rcases hcol with e | e
    · rw [e]; exact hloc s hsC
    · rw [e]; exact hloc t htC
  exact (H.local_model hj (hD.2 hy) hcl.1 hcl.2).mp hyZ

/-- **Proposition (validity).** The alternating-boundary-sea blackout is valid. -/
theorem valid : Valid h m (altSea h m q pos E) := by
  set Z := altSea h m q pos E with hZ
  intro C₁ h₁ C₂ h₂ hp
  by_contra hne
  obtain ⟨w₁, w₂⟩ := pres_card_le_two_of_ne h₁ h₂ hne hp
  rcases h₁.1.axis_or_tilt with a₁ | t₁ <;> rcases h₂.1.axis_or_tilt with a₂ | t₂
  · rcases axis_collision_cycle a₁ a₂ hne hp with c | c
    · exact H.no_four c
    · exact H.no_six c
  · exact H.no_rival h₂ h₁ t₂ a₁ w₂ hp.symm
  · exact H.no_rival h₁ h₂ t₁ a₂ w₁ hp
  · obtain ⟨j, hj, hloc, s, t, hpres, w⟩ := H.weak h₁ t₁ w₁
    obtain ⟨j', hj', hloc', s', t', hpres', w'⟩ := H.weak h₂ t₂ w₂
    have hpair : ({s, t} : Finset Pt) = {s', t'} := by rw [← hpres, ← hpres', hp]
    have hsP : s ∈ pres Z C₁ := by rw [hpres]; simp
    have hsC : s ∈ C₁ := (mem_sdiff.mp hsP).1
    have hsC' : s ∈ C₂ := (mem_sdiff.mp (hp ▸ hsP)).1
    have hjj : j = j' := by
      by_contra hne'
      have := hloc s hsC
      have := hloc' s hsC'
      rcases H.pos_far hj hj' hne' with h' | h' <;> omega
    subst hjj
    have hst : (s = s' ∧ t = t') ∨ (s = t' ∧ t = s') := by
      have hs : s ∈ ({s', t'} : Finset Pt) := by rw [← hpair]; simp
      have ht : t ∈ ({s', t'} : Finset Pt) := by rw [← hpair]; simp
      have hne' : s ≠ t := fun he => (w.white (H.locHyp hj)).2.2 (by rw [he])
      simp only [mem_insert, mem_singleton] at hs ht
      rcases hs with h1 | h1 <;> rcases ht with h2 | h2
      · exact absurd (h1.trans h2.symm) hne'
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact absurd (h1.trans h2.symm) hne'
    exact hne (weak_unique (H.locHyp hj) w w' hst)

theorem subset_grid : altSea h m q pos E ⊆ grid h m := by
  intro y hy
  have hh := H.three_le
  rw [mem_altSea] at hy
  rw [mem_grid]
  rcases hy with ⟨h1, h2, -, h3⟩ | ⟨j, hj, he, h3⟩
  · rcases seaRowAfter_cases h (seaCnt q pos y.1) with e | e <;>
      · rw [seaRow, e] at h3
        omega
  · have := H.pos_mem j hj
    have := H.edge j hj
    omega

/-- **Proposition (size).** The alternating-boundary-sea blackout has `m + q` points. -/
theorem card : (altSea h m q pos E).card = m + q := by
  have hinj : Set.InjOn pos (range q) := fun i hi j hj he =>
    H.pos_inj (mem_range.mp hi) (mem_range.mp hj) he
  have hD : (range q).image pos ⊆ Icc (1 : ℤ) m := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    rw [mem_Icc]
    exact H.pos_mem j (mem_range.mp hj)
  have hDc : ((range q).image pos).card = q := by rw [card_image_of_injOn hinj, card_range]
  have hqm : q ≤ m := by
    have := card_le_card hD
    rw [hDc, Int.card_Icc] at this
    omega
  have c1 : ((Icc (1 : ℤ) m \ (range q).image pos).image
      (fun x => (x, seaRow h q pos x))).card = m - q := by
    rw [card_image_of_injective _ (fun a b e => (Prod.mk.inj e).1), card_sdiff_of_subset hD,
      hDc, Int.card_Icc]
    omega
  have c2 : ((range q).image (fun j => (pos j, (E j).1))).card = q := by
    rw [card_image_of_injOn (fun i hi j hj e => hinj hi hj (Prod.mk.inj e).1), card_range]
  have c3 : ((range q).image (fun j => (pos j, (E j).2))).card = q := by
    rw [card_image_of_injOn (fun i hi j hj e => hinj hi hj (Prod.mk.inj e).1), card_range]
  have d23 : Disjoint ((range q).image (fun j => (pos j, (E j).1)))
      ((range q).image (fun j => (pos j, (E j).2))) := by
    rw [disjoint_left]
    intro y hy hy'
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    obtain ⟨j, hj, he⟩ := mem_image.mp hy'
    obtain ⟨e1, e2⟩ := Prod.mk.inj he
    have := hinj hj hi e1
    subst this
    have := H.edge j (mem_range.mp hj)
    omega
  have d1 : Disjoint ((Icc (1 : ℤ) m \ (range q).image pos).image
      (fun x => (x, seaRow h q pos x)))
      ((range q).image (fun j => (pos j, (E j).1)) ∪
        (range q).image (fun j => (pos j, (E j).2))) := by
    rw [disjoint_left]
    intro y hy hy'
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    have hx' := (mem_sdiff.mp hx).2
    rcases mem_union.mp hy' with hy' | hy' <;>
    · obtain ⟨j, hj, he⟩ := mem_image.mp hy'
      exact hx' (mem_image.mpr ⟨j, hj, (Prod.mk.inj he).1⟩)
  unfold altSea
  rw [card_union_of_disjoint d1, card_union_of_disjoint d23, c1, c2, c3]
  omega

/-- **Proposition.** The alternating-boundary-sea blackout is a valid blackout of the `h × m`
grid with `m + q` points. -/
theorem alt_sea : altSea h m q pos E ⊆ grid h m ∧ Valid h m (altSea h m q pos E) ∧
    (altSea h m q pos E).card = m + q :=
  ⟨H.subset_grid, H.valid, H.card⟩

end AltHyp


/-! ### The theorem -/

/-- The edges of `K_{⌊h/2⌋, ⌈h/2⌉}`: edge `j` joins row `⌊j / ⌈h/2⌉⌋ + 1` of the top part
`1, …, ⌊h/2⌋` to row `⌊h/2⌋ + 1 + (j mod ⌈h/2⌉)` of the bottom part. -/
def bipE (h j : ℕ) : ℤ × ℤ :=
  (((j / (h - h / 2) : ℕ) : ℤ) + 1, ((h / 2 + 1 + j % (h - h / 2) : ℕ) : ℤ))

/-- The double columns `1, 1 + (2 W_h + 2), 1 + 2 (2 W_h + 2), …`. -/
def bipPos (h j : ℕ) : ℤ := 1 + (j : ℤ) * (2 * spanW h + 2)

/-- `M_h = q_h + (q_h - 1)(2 W_h + 1)` with `q_h = ⌊h²/4⌋`. -/
def Mh (h : ℕ) : ℕ := h ^ 2 / 4 + (h ^ 2 / 4 - 1) * (2 * spanW h + 1)

lemma half_mul_half (h : ℕ) : h / 2 * (h - h / 2) = h ^ 2 / 4 := by
  rcases Nat.even_or_odd' h with ⟨k, rfl | rfl⟩
  · have e1 : 2 * k / 2 = k := by omega
    have e2 : 2 * k - k = k := by omega
    have e3 : (2 * k) ^ 2 = 4 * (k * k) := by ring
    rw [e1, e2, e3]
    omega
  · have e1 : (2 * k + 1) / 2 = k := by omega
    have e2 : 2 * k + 1 - k = k + 1 := by omega
    have e3 : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
    have e4 : k * (k + 1) = k * k + k := by ring
    rw [e1, e2, e3, e4]
    omega

lemma bipE_bounds {h j : ℕ} (hh : 3 ≤ h) (hj : j < h ^ 2 / 4) :
    1 ≤ (bipE h j).1 ∧ (bipE h j).1 ≤ ((h / 2 : ℕ) : ℤ) ∧ ((h / 2 : ℕ) : ℤ) < (bipE h j).2 ∧
      (bipE h j).2 ≤ h := by
  have hr : 0 < h - h / 2 := by omega
  have h1 : j / (h - h / 2) < h / 2 := by
    rw [Nat.div_lt_iff_lt_mul hr, half_mul_half]
    exact hj
  have h2 : j % (h - h / 2) < h - h / 2 := Nat.mod_lt _ hr
  simp only [bipE]
  generalize j / (h - h / 2) = a at h1 ⊢
  generalize j % (h - h / 2) = c at h2 ⊢
  omega

lemma Mh_eq (h : ℕ) (hq : 1 ≤ h ^ 2 / 4) :
    1 + (h ^ 2 / 4 - 1) * (2 * spanW h + 2) = Mh h := by
  unfold Mh
  obtain ⟨q', hq'⟩ : ∃ q', h ^ 2 / 4 = q' + 1 := ⟨h ^ 2 / 4 - 1, by omega⟩
  rw [hq', Nat.add_sub_cancel]
  ring

lemma two_le_q {h : ℕ} (hh : 3 ≤ h) : 2 ≤ h ^ 2 / 4 := by
  have : 9 ≤ h ^ 2 := by nlinarith
  omega

/-- The hypotheses of the Proposition hold for `K_{⌊h/2⌋, ⌈h/2⌉}` with the doubles
`2 W_h + 2` columns apart, starting in column `1`, whenever `m ≥ M_h`. -/
theorem bip_hyp {h m : ℕ} (hh : 3 ≤ h) (hm : Mh h ≤ m) :
    AltHyp h m (h ^ 2 / 4) (bipPos h) (bipE h) where
  three_le := hh
  pos_mem := by
    intro j hj
    have hq := two_le_q hh
    have key : 1 + j * (2 * spanW h + 2) ≤ m := by
      have : j * (2 * spanW h + 2) ≤ (h ^ 2 / 4 - 1) * (2 * spanW h + 2) :=
        Nat.mul_le_mul_right _ (by omega)
      have e := Mh_eq h (by omega)
      omega
    have hnn : (0 : ℤ) ≤ (j : ℤ) * (2 * spanW h + 2) := by positivity
    unfold bipPos
    constructor
    · linarith
    · exact_mod_cast key
  gap := by
    intro j _
    unfold bipPos
    push_cast
    have : ((j : ℤ) + 1) * (2 * spanW h + 2) = (j : ℤ) * (2 * spanW h + 2) + (2 * spanW h + 2) := by
      ring
    linarith
  edge := by
    intro j hj
    have := bipE_bounds hh hj
    omega
  inj := by
    intro i _ j _ he
    simp only [bipE, Prod.mk.injEq] at he
    obtain ⟨e1, e2⟩ := he
    have e1' : i / (h - h / 2) = j / (h - h / 2) := by exact_mod_cast add_right_cancel e1
    have e2' : i % (h - h / 2) = j % (h - h / 2) := by
      have : h / 2 + 1 + i % (h - h / 2) = h / 2 + 1 + j % (h - h / 2) := by exact_mod_cast e2
      exact Nat.add_left_cancel this
    rw [← Nat.div_add_mod i (h - h / 2), ← Nat.div_add_mod j (h - h / 2), e1', e2']
  tri := by
    have adj : ∀ x y : ℤ, Adj (h ^ 2 / 4) (bipE h) x y →
        (x ≤ ((h / 2 : ℕ) : ℤ) ∧ ((h / 2 : ℕ) : ℤ) < y) ∨
          (y ≤ ((h / 2 : ℕ) : ℤ) ∧ ((h / 2 : ℕ) : ℤ) < x) := by
      rintro x y ⟨j, hj, e | e⟩ <;> have := bipE_bounds hh hj <;> rw [e] at this <;>
        dsimp only at this <;> omega
    intro x y z h1 h2 h3
    have := adj _ _ h1
    have := adj _ _ h2
    have := adj _ _ h3
    omega

/-- **The general theorem.** For `h ≥ 3` and `m ≥ M_h = q_h + (q_h - 1)(2 W_h + 1)`, the
alternating-boundary-sea blackout with `H = K_{⌊h/2⌋, ⌈h/2⌉}` is a valid blackout of the
`h × m` grid with `m + ⌊h²/4⌋` points, and no valid blackout has more (the row bound). -/
theorem general_theorem {h m : ℕ} (hh : 3 ≤ h) (hm : Mh h ≤ m) :
    (∃ S ⊆ grid h m, Valid h m S ∧ S.card = m + h ^ 2 / 4) ∧
      ∀ S ⊆ grid h m, Valid h m S → S.card ≤ m + h ^ 2 / 4 := by
  have H := bip_hyp hh hm
  have h3m : 3 ≤ m := by
    have hq := two_le_q hh
    have : 0 < (h ^ 2 / 4 - 1) * (2 * spanW h + 1) := Nat.mul_pos (by omega) (by omega)
    unfold Mh at hm
    omega
  exact ⟨⟨_, H.subset_grid, H.valid, H.card⟩, fun S hS hv => row_bound h3m hS hv⟩

/-- **`f(h, m) = m + ⌊h²/4⌋` for every `h ≥ 3` and `m ≥ M_h`.** -/
theorem fval_general {h m : ℕ} (hh : 3 ≤ h) (hm : Mh h ≤ m) : fval h m = m + h ^ 2 / 4 :=
  fval_eq (general_theorem hh hm).1 (general_theorem hh hm).2

end Kagey001
