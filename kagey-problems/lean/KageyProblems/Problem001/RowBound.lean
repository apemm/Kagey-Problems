import KageyProblems.Problem001.Foundations

/-!
# Kagey's Problem 001 — the row bound

Lean proof of the row bound `f(h, m) ≤ m + ⌊h²/4⌋` for `m ≥ 3` (Theorem "row bound" in
Section 4 of `problem001/jis/pemmasani.tex`), and of the second bound `h + ⌊m²/4⌋` for
`h ≥ 3`. As in the paper, the bound is proved for axis-valid blackouts (`AxisValid`: no two
axis-aligned rectangles have the same presentation), and every valid blackout is axis-valid.

The route is the paper's. By the second half of Lemma "axis-aligned rectangles and short
cycles", the row-column graph of an axis-valid blackout has no four-cycle (for `m ≥ 3`) and no
six-cycle. So the row graph of Lemma "row graph", with the star at the least black row of each
column as the chosen tree, is simple and triangle-free, and Mantel's theorem (Mathlib's Turán
bound `SimpleGraph.CliqueFree.card_edgeFinset_le` with `r = 2`) bounds its edges.

## Contents

* `axisRect`, `axisRect_mem`: the axis-aligned rectangle on two columns and two rows.
* `AxisRects`, `AxisValid`, `Valid.axisValid`: axis-aligned rectangles, axis-validity, and
  the fact that a valid blackout is axis-valid.
* `no_four_cycle`: for `m ≥ 3`, two distinct columns of an axis-valid blackout share at most
  one black row; `no_six_cycle`: there is no black six-cycle.
* `rowGraph`, `rowGraph_cliqueFree`, `starEdges_disjoint`: the row graph, its
  triangle-freeness, and the fact that different columns give different edges.
* `row_bound_axis`: `3 ≤ m → S ⊆ grid h m → AxisValid h m S → S.card ≤ m + h ^ 2 / 4`, and
  `row_bound`, the same for `Valid`.
* `valid_swap_iff`, `axisValid_swap_iff`: validity and axis-validity are invariant under
  exchanging rows and columns; `row_bound_swap_axis`:
  `3 ≤ h → S ⊆ grid h m → AxisValid h m S → S.card ≤ h + m ^ 2 / 4`, and `row_bound_swap`,
  the same for `Valid`.
* `row_bound_small`: `f(3, m) ≤ m + 2`, `f(4, m) ≤ m + 4`, `f(5, m) ≤ m + 6` and
  `f(6, m) ≤ m + 9` for `m ≥ 3`.
-/

namespace Kagey001

open Finset

/-- The axis-aligned rectangle on columns `a, b` and rows `c, d`. -/
def axisRect (a b c d : ℤ) : Finset Pt := {(a, c), (b, c), (a, d), (b, d)}

lemma axisRect_mem {h m : ℕ} {a b c d : ℤ} (hab : a ≠ b) (hcd : c ≠ d)
    (ha : 1 ≤ a ∧ a ≤ m) (hb : 1 ≤ b ∧ b ≤ m) (hc : 1 ≤ c ∧ c ≤ h) (hd : 1 ≤ d ∧ d ≤ h) :
    axisRect a b c d ∈ Rects h m := by
  refine ⟨⟨(a, c), (b - a, 0), (0, d - c), ?_, ?_, by ring, ?_⟩, ?_⟩
  · intro h0
    have := congrArg Prod.fst h0
    simp only [Prod.fst_zero] at this
    exact hab (by linarith)
  · intro h0
    have := congrArg Prod.snd h0
    simp only [Prod.snd_zero] at this
    exact hcd (by linarith)
  · ext ⟨x, y⟩
    simp only [axisRect, mem_insert, mem_singleton, Prod.mk_add_mk, Prod.mk.injEq]
    omega
  · intro y hy
    simp only [axisRect, mem_insert, mem_singleton] at hy
    rw [mem_grid]
    rcases hy with rfl | rfl | rfl | rfl <;> simp only <;> omega

/-- A third column exists when `m ≥ 3`. -/
lemma exists_third {m : ℕ} (hm : 3 ≤ m) (p q : ℤ) :
    ∃ z : ℤ, 1 ≤ z ∧ z ≤ m ∧ z ≠ p ∧ z ≠ q := by
  by_cases h1 : p ≠ 1 ∧ q ≠ 1
  · exact ⟨1, le_refl _, by omega, by omega, by omega⟩
  · by_cases h2 : p ≠ 2 ∧ q ≠ 2
    · exact ⟨2, by omega, by omega, by omega, by omega⟩
    · exact ⟨3, by omega, by omega, by omega, by omega⟩

/-- The axis-aligned rectangles of the `h × m` grid. -/
def AxisRects (h m : ℕ) : Set (Finset Pt) :=
  {C | ∃ a b c d : ℤ, a ≠ b ∧ c ≠ d ∧ (1 ≤ a ∧ a ≤ m) ∧ (1 ≤ b ∧ b ≤ m) ∧
    (1 ≤ c ∧ c ≤ h) ∧ (1 ≤ d ∧ d ≤ h) ∧ C = axisRect a b c d}

/-- A blackout is axis-valid when no two axis-aligned rectangles have the same presentation. -/
def AxisValid (h m : ℕ) (S : Finset Pt) : Prop :=
  ∀ C₁ ∈ AxisRects h m, ∀ C₂ ∈ AxisRects h m, pres S C₁ = pres S C₂ → C₁ = C₂

lemma axisRects_subset (h m : ℕ) : AxisRects h m ⊆ Rects h m := by
  rintro _ ⟨a, b, c, d, hab, hcd, ha, hb, hc, hd, rfl⟩
  exact axisRect_mem hab hcd ha hb hc hd

/-- A valid blackout is axis-valid. -/
theorem Valid.axisValid {h m : ℕ} {S : Finset Pt} (hv : Valid h m S) : AxisValid h m S :=
  fun _ h1 _ h2 hp => hv _ (axisRects_subset h m h1) _ (axisRects_subset h m h2) hp

lemma axisRect_mem_axis {h m : ℕ} {a b c d : ℤ} (hab : a ≠ b) (hcd : c ≠ d)
    (ha : 1 ≤ a ∧ a ≤ m) (hb : 1 ≤ b ∧ b ≤ m) (hc : 1 ≤ c ∧ c ≤ h) (hd : 1 ≤ d ∧ d ≤ h) :
    axisRect a b c d ∈ AxisRects h m :=
  ⟨a, b, c, d, hab, hcd, ha, hb, hc, hd, rfl⟩

/-- **No black four-cycle.** For `m ≥ 3`, two distinct columns of an axis-valid blackout share
at most one black row. -/
theorem no_four_cycle {h m : ℕ} (hm : 3 ≤ m) {S : Finset Pt} (hv : AxisValid h m S)
    {i i' j j' : ℤ} (hi : 1 ≤ i ∧ i ≤ m) (hi' : 1 ≤ i' ∧ i' ≤ m)
    (hj : 1 ≤ j ∧ j ≤ h) (hj' : 1 ≤ j' ∧ j' ≤ h) (hii : i ≠ i') (hjj : j ≠ j')
    (h1 : (i, j) ∈ S) (h2 : (i, j') ∈ S) (h3 : (i', j) ∈ S) (h4 : (i', j') ∈ S) : False := by
  obtain ⟨w, hw1, hw2, hwi, hwi'⟩ := exists_third hm i i'
  have R1 := axisRect_mem_axis (h := h) (m := m) (Ne.symm hwi) hjj hi ⟨hw1, hw2⟩ hj hj'
  have R2 := axisRect_mem_axis (h := h) (m := m) (Ne.symm hwi') hjj hi' ⟨hw1, hw2⟩ hj hj'
  have hp : pres S (axisRect i w j j') = pres S (axisRect i' w j j') := by
    ext ⟨x, y⟩
    simp only [pres, axisRect, mem_sdiff, mem_insert, mem_singleton, Prod.mk.injEq]
    by_cases hx : (x, y) ∈ S
    · simp [hx]
    · have e1 : ¬(x = i ∧ y = j) := by rintro ⟨rfl, rfl⟩; exact hx h1
      have e2 : ¬(x = i ∧ y = j') := by rintro ⟨rfl, rfl⟩; exact hx h2
      have e3 : ¬(x = i' ∧ y = j) := by rintro ⟨rfl, rfl⟩; exact hx h3
      have e4 : ¬(x = i' ∧ y = j') := by rintro ⟨rfl, rfl⟩; exact hx h4
      simp only [hx, not_false_eq_true, and_true]
      omega
  have heq := hv _ R1 _ R2 hp
  have hmem : ((i, j) : Pt) ∈ axisRect i' w j j' := by
    rw [← heq]; simp [axisRect]
  simp only [axisRect, mem_insert, mem_singleton, Prod.mk.injEq] at hmem
  omega

/-- **No black six-cycle.** For distinct rows `a, b, c` and distinct columns `x, y, z` of an
axis-valid blackout, it is impossible that `a, b` are black in `x`, `b, c` in `y`, and `c, a`
in `z`. -/
theorem no_six_cycle {h m : ℕ} {S : Finset Pt} (hv : AxisValid h m S) {a b c x y z : ℤ}
    (ha : 1 ≤ a ∧ a ≤ h) (hb : 1 ≤ b ∧ b ≤ h) (hc : 1 ≤ c ∧ c ≤ h)
    (hx : 1 ≤ x ∧ x ≤ m) (hy : 1 ≤ y ∧ y ≤ m) (hz : 1 ≤ z ∧ z ≤ m)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (h1 : (x, a) ∈ S) (h2 : (x, b) ∈ S) (h3 : (y, b) ∈ S) (h4 : (y, c) ∈ S)
    (h5 : (z, c) ∈ S) (h6 : (z, a) ∈ S) : False := by
  have R1 := axisRect_mem_axis (h := h) (m := m) hxy hab hx hy ha hb
  have R2 := axisRect_mem_axis (h := h) (m := m) hyz (Ne.symm hca) hy hz ha hc
  have hp : pres S (axisRect x y a b) = pres S (axisRect y z a c) := by
    ext ⟨u, v⟩
    simp only [pres, axisRect, mem_sdiff, mem_insert, mem_singleton, Prod.mk.injEq]
    by_cases hu : (u, v) ∈ S
    · simp [hu]
    · have e1 : ¬(u = x ∧ v = a) := by rintro ⟨rfl, rfl⟩; exact hu h1
      have e2 : ¬(u = x ∧ v = b) := by rintro ⟨rfl, rfl⟩; exact hu h2
      have e3 : ¬(u = y ∧ v = b) := by rintro ⟨rfl, rfl⟩; exact hu h3
      have e4 : ¬(u = y ∧ v = c) := by rintro ⟨rfl, rfl⟩; exact hu h4
      have e5 : ¬(u = z ∧ v = c) := by rintro ⟨rfl, rfl⟩; exact hu h5
      have e6 : ¬(u = z ∧ v = a) := by rintro ⟨rfl, rfl⟩; exact hu h6
      simp only [hu, not_false_eq_true, and_true]
      constructor
      · rintro (h' | h' | h' | h')
        · exact absurd h' e1
        · exact Or.inl h'
        · exact absurd h' e2
        · exact absurd h' e3
      · rintro (h' | h' | h' | h')
        · exact Or.inr (Or.inl h')
        · exact absurd h' e6
        · exact absurd h' e4
        · exact absurd h' e5
  have heq := hv _ R1 _ R2 hp
  have hmem : ((x, a) : Pt) ∈ axisRect y z a c := by
    rw [← heq]; simp [axisRect]
  simp only [axisRect, mem_insert, mem_singleton, Prod.mk.injEq] at hmem
  omega

/-! ### Columns as sets of rows -/

/-- The black rows of column `i`, indexed by `Fin h` (index `k` is row `k + 1`). -/
def blackRows (h : ℕ) (S : Finset Pt) (i : ℤ) : Finset (Fin h) :=
  univ.filter (fun k : Fin h => (i, ((k : ℕ) : ℤ) + 1) ∈ S)

lemma mem_blackRows {h : ℕ} {S : Finset Pt} {i : ℤ} {k : Fin h} :
    k ∈ blackRows h S i ↔ (i, ((k : ℕ) : ℤ) + 1) ∈ S := by
  simp [blackRows]

/-- Counting a blackout column by column. -/
lemma card_eq_sum_blackRows {h m : ℕ} {S : Finset Pt} (hS : S ⊆ grid h m) :
    S.card = ∑ i ∈ Finset.Icc (1 : ℤ) m, (blackRows h S i).card := by
  have hinj : ∀ i : ℤ, Function.Injective (fun k : Fin h => ((i, ((k : ℕ) : ℤ) + 1) : Pt)) := by
    intro i k l hkl
    simp only [Prod.mk.injEq, add_left_inj, Nat.cast_inj] at hkl
    exact Fin.ext hkl.2
  have hdecomp : S = (Finset.Icc (1 : ℤ) m).biUnion
      (fun i => (blackRows h S i).map ⟨_, hinj i⟩) := by
    ext ⟨a, b⟩
    simp only [mem_biUnion, mem_Icc, mem_map, Function.Embedding.coeFn_mk, mem_blackRows,
      Prod.mk.injEq]
    constructor
    · intro hy
      have hg := mem_grid'.mp (hS hy)
      refine ⟨a, ⟨hg.1, hg.2.1⟩, ⟨(b - 1).toNat, by omega⟩, ?_, rfl, by simp; omega⟩
      have : (((b - 1).toNat : ℕ) : ℤ) + 1 = b := by omega
      simp only [this]
      exact hy
    · rintro ⟨i, _, k, hk, rfl, rfl⟩
      exact hk
  conv_lhs => rw [hdecomp]
  rw [card_biUnion]
  · simp
  · intro x _ y _ hxy
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [mem_map, Function.Embedding.coeFn_mk] at hp hp'
    obtain ⟨k, _, rfl⟩ := hp
    obtain ⟨l, _, hl⟩ := hp'
    simp only [Prod.mk.injEq] at hl
    exact hxy hl.1.symm

/-! ### The row graph -/

/-- The row graph: one star per column, centred at its least black row. -/
def rowGraph (h m : ℕ) (S : Finset Pt) : SimpleGraph (Fin h) where
  Adj k l := k ≠ l ∧ ∃ i ∈ Finset.Icc (1 : ℤ) m, k ∈ blackRows h S i ∧ l ∈ blackRows h S i ∧
    ((∀ x ∈ blackRows h S i, k ≤ x) ∨ (∀ x ∈ blackRows h S i, l ≤ x))
  symm := ⟨fun _ _ ⟨hne, i, hi, hk, hl, hmin⟩ => ⟨Ne.symm hne, i, hi, hl, hk, hmin.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

section RowBound

variable {h m : ℕ} {S : Finset Pt}

/-- Two distinct black rows `k ≠ l` shared by columns `i ≠ i'` contradict validity. -/
lemma shared_pair_false (hm : 3 ≤ m) (hv : AxisValid h m S) {i i' : ℤ}
    (hi : i ∈ Finset.Icc (1 : ℤ) m) (hi' : i' ∈ Finset.Icc (1 : ℤ) m) (hii : i ≠ i')
    {k l : Fin h} (hkl : k ≠ l) (h1 : k ∈ blackRows h S i) (h2 : l ∈ blackRows h S i)
    (h3 : k ∈ blackRows h S i') (h4 : l ∈ blackRows h S i') : False := by
  rw [mem_Icc] at hi hi'
  rw [mem_blackRows] at h1 h2 h3 h4
  have hk := k.isLt
  have hl := l.isLt
  have hkl' : (k : ℕ) ≠ l := fun e => hkl (Fin.ext e)
  exact no_four_cycle hm hv hi hi' ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hii
    (by omega) h1 h2 h3 h4

lemma rowGraph_cliqueFree (hm : 3 ≤ m) (hv : AxisValid h m S) :
    (rowGraph h m S).CliqueFree 3 := by
  intro t ht
  rw [SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := ht
  obtain ⟨nab, x, hx, ha1, hb1, m1⟩ := hab
  obtain ⟨nac, z, hz, ha3, hc3, m3⟩ := hac
  obtain ⟨nbc, y, hy, hb2, hc2, m2⟩ := hbc
  -- `a, b ∈ x`, `a, c ∈ z`, `b, c ∈ y`
  by_cases hxy : x = y
  · subst hxy
    by_cases hxz : x = z
    · subst hxz
      -- one star contains a triangle: impossible, its edges all pass through the centre
      have uniq : ∀ p q : Fin h, p ∈ blackRows h S x → q ∈ blackRows h S x →
          (∀ r ∈ blackRows h S x, p ≤ r) → (∀ r ∈ blackRows h S x, q ≤ r) → p = q :=
        fun p q hp hq hp' hq' => le_antisymm (hp' q hq) (hq' p hp)
      rcases m1 with m1 | m1 <;> rcases m2 with m2 | m2 <;> rcases m3 with m3 | m3
      all_goals first
        | exact nab (uniq _ _ ha1 hb1 ‹_› ‹_›)
        | exact nac (uniq _ _ ha1 hc2 ‹_› ‹_›)
        | exact nbc (uniq _ _ hb1 hc2 ‹_› ‹_›)
    · -- `b, c ∈ x` and `a, c ∈ x`, `a, c ∈ z`
      exact shared_pair_false hm hv hx hz hxz nac ha1 hc2 ha3 hc3
  · by_cases hxz : x = z
    · subst hxz
      -- `b, c` in `x` (from `a,c ∈ x` and `a,b ∈ x`) and in `y`
      exact shared_pair_false hm hv hx hy hxy nbc hb1 hc3 hb2 hc2
    · by_cases hyz : y = z
      · subst hyz
        exact shared_pair_false hm hv hx hy hxy nab ha1 hb1 ha3 hb2
      · -- three distinct columns: a black six-cycle
        rw [mem_Icc] at hx hy hz
        rw [mem_blackRows] at ha1 hb1 ha3 hc3 hb2 hc2
        have := a.isLt
        have := b.isLt
        have := c.isLt
        have nab' : (a : ℕ) ≠ b := fun e => nab (Fin.ext e)
        have nbc' : (b : ℕ) ≠ c := fun e => nbc (Fin.ext e)
        have nac' : (a : ℕ) ≠ c := fun e => nac (Fin.ext e)
        exact no_six_cycle (h := h) (m := m) hv (a := (a : ℤ) + 1) (b := (b : ℤ) + 1)
          (c := (c : ℤ) + 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
          hx hy hz (by omega) (by omega) (by omega) hxy hyz (Ne.symm hxz)
          ha1 hb1 hb2 hc2 hc3 ha3

open Classical in
/-- The star edges of column `i`. -/
noncomputable def starEdges (h : ℕ) (S : Finset Pt) (i : ℤ) : Finset (Sym2 (Fin h)) :=
  if hne : (blackRows h S i).Nonempty then
    ((blackRows h S i).erase ((blackRows h S i).min' hne)).image
      (fun l => s((blackRows h S i).min' hne, l))
  else ∅

lemma card_blackRows_le (i : ℤ) :
    (blackRows h S i).card ≤ 1 + (starEdges h S i).card := by
  unfold starEdges
  split_ifs with hne
  · rw [card_image_of_injective _ (fun l l' e => Sym2.congr_right.mp e),
      card_erase_of_mem (min'_mem _ _)]
    omega
  · rw [not_nonempty_iff_eq_empty] at hne
    simp [hne]

open Classical in
lemma starEdges_subset (i : ℤ) (hi : i ∈ Finset.Icc (1 : ℤ) m) :
    starEdges h S i ⊆ (rowGraph h m S).edgeFinset := by
  unfold starEdges
  split_ifs with hne
  · intro e he
    simp only [mem_image, mem_erase] at he
    obtain ⟨l, ⟨hl, hlB⟩, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨Ne.symm hl, i, hi, min'_mem _ _, hlB, Or.inl (fun x hx => min'_le _ _ hx)⟩
  · exact empty_subset _

lemma mem_starEdges {i : ℤ} {e : Sym2 (Fin h)} (he : e ∈ starEdges h S i) :
    ∃ k l, k ≠ l ∧ k ∈ blackRows h S i ∧ l ∈ blackRows h S i ∧ e = s(k, l) := by
  unfold starEdges at he
  split_ifs at he with hne
  · simp only [mem_image, mem_erase] at he
    obtain ⟨l, ⟨hl, hlB⟩, rfl⟩ := he
    exact ⟨_, l, Ne.symm hl, min'_mem _ _, hlB, rfl⟩
  · simp at he

lemma starEdges_disjoint (hm : 3 ≤ m) (hv : AxisValid h m S) {i i' : ℤ}
    (hi : i ∈ Finset.Icc (1 : ℤ) m) (hi' : i' ∈ Finset.Icc (1 : ℤ) m) (hii : i ≠ i') :
    Disjoint (starEdges h S i) (starEdges h S i') := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨k, l, hkl, hk, hl, rfl⟩ := mem_starEdges he
  obtain ⟨k', l', _, hk', hl', he⟩ := mem_starEdges he'
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact shared_pair_false hm hv hi hi' hii hkl hk hl hk' hl'
  · exact shared_pair_false hm hv hi hi' hii hkl hk hl hl' hk'

/-- `⌊h²/4⌋` in the form produced by Mathlib's Turán bound for `r = 2`. -/
lemma turan_two_eq (h : ℕ) : (h ^ 2 - (h % 2) ^ 2) * (2 - 1) / (2 * 2) + (h % 2).choose 2 =
    h ^ 2 / 4 := by
  rcases Nat.even_or_odd' h with ⟨k, rfl | rfl⟩
  · have e : (2 * k) ^ 2 = 4 * (k * k) := by ring
    have e2 : 2 * k % 2 = 0 := by omega
    rw [e, e2]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, tsub_zero,
      Nat.add_one_sub_one, mul_one, Nat.reduceMul, Nat.choose_zero_succ, add_zero]
  · have e : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
    have e2 : (2 * k + 1) % 2 = 1 := by omega
    rw [e, e2]
    rw [show Nat.choose 1 2 = 0 from rfl]
    omega

/-- **Row bound.** For `m ≥ 3`, every axis-valid blackout of the `h × m` grid has at most
`m + ⌊h²/4⌋` points. -/
theorem row_bound_axis (hm : 3 ≤ m) (hS : S ⊆ grid h m) (hv : AxisValid h m S) :
    S.card ≤ m + h ^ 2 / 4 := by
  classical
  have hsum := card_eq_sum_blackRows hS
  have h1 : S.card ≤ ∑ i ∈ Finset.Icc (1 : ℤ) m, (1 + (starEdges h S i).card) := by
    rw [hsum]
    exact Finset.sum_le_sum (fun i _ => card_blackRows_le i)
  have h2 : ∑ i ∈ Finset.Icc (1 : ℤ) m, (starEdges h S i).card =
      ((Finset.Icc (1 : ℤ) m).biUnion (starEdges h S)).card := by
    rw [card_biUnion]
    intro x hx y hy hxy
    exact starEdges_disjoint hm hv hx hy hxy
  have h3 : ((Finset.Icc (1 : ℤ) m).biUnion (starEdges h S)).card ≤
      (rowGraph h m S).edgeFinset.card := by
    apply card_le_card
    intro e he
    rw [mem_biUnion] at he
    obtain ⟨i, hi, he⟩ := he
    exact starEdges_subset i hi he
  have h4 := (rowGraph_cliqueFree (S := S) hm hv).card_edgeFinset_le (r := 2)
  simp only [Fintype.card_fin] at h4
  rw [turan_two_eq] at h4
  rw [Finset.sum_add_distrib, h2] at h1
  simp only [sum_const, Int.card_Icc, smul_eq_mul, mul_one, add_sub_cancel_right,
    Int.toNat_natCast] at h1
  omega

/-- **Row bound for valid blackouts.** For `m ≥ 3`, every valid blackout of the `h × m` grid
has at most `m + ⌊h²/4⌋` points, so `f(h, m) ≤ m + ⌊h²/4⌋`. -/
theorem row_bound (hm : 3 ≤ m) (hS : S ⊆ grid h m) (hv : Valid h m S) :
    S.card ≤ m + h ^ 2 / 4 :=
  row_bound_axis hm hS hv.axisValid

end RowBound

/-! ### Exchanging rows and columns -/

/-- The transpose `(i, j) ↦ (j, i)` as an embedding. -/
def swapE : Pt ↪ Pt := ⟨Prod.swap, Prod.swap_injective⟩

lemma swap_add' (p q : Pt) : (p + q).swap = p.swap + q.swap := rfl

lemma isRect_map_swap {C : Finset Pt} (hC : IsRect C) : IsRect (C.map swapE) := by
  obtain ⟨p, u, v, hu, hv, hperp, rfl⟩ := hC
  refine ⟨p.swap, u.swap, v.swap, ?_, ?_, ?_, ?_⟩
  · intro h0; apply hu; rw [← Prod.swap_swap u, h0]; rfl
  · intro h0; apply hv; rw [← Prod.swap_swap v, h0]; rfl
  · simp only [Prod.fst_swap, Prod.snd_swap]; linarith
  · simp only [Finset.map_insert, Finset.map_singleton]
    rfl

lemma map_swap_grid (h m : ℕ) : (grid h m).map swapE = grid m h := by
  ext ⟨a, b⟩
  simp only [Finset.mem_map, mem_grid', Prod.exists]
  constructor
  · rintro ⟨x, y, hxy, he⟩
    simp only [swapE, Function.Embedding.coeFn_mk, Prod.swap_prod_mk, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    omega
  · intro hab
    exact ⟨b, a, by omega, rfl⟩

lemma rects_swap (h m : ℕ) : Rects m h = (Finset.map swapE) '' Rects h m := by
  ext C
  constructor
  · rintro ⟨hC, hsub⟩
    refine ⟨C.map swapE, ⟨isRect_map_swap hC, ?_⟩, ?_⟩
    · intro y hy
      have : y.swap ∈ (grid h m).map swapE := by
        rw [map_swap_grid]
        obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
        simpa [swapE] using hsub hz
      obtain ⟨z, hz, hze⟩ := Finset.mem_map.mp this
      have : z = y := by
        have := congrArg Prod.swap hze
        simpa [swapE] using this
      rw [← this]; exact hz
    · rw [Finset.map_map]
      ext y
      simp [swapE]
  · rintro ⟨D, ⟨hD, hsub⟩, rfl⟩
    refine ⟨isRect_map_swap hD, ?_⟩
    rw [← map_swap_grid]
    exact Finset.map_subset_map.mpr hsub

/-- Validity is invariant under exchanging rows and columns. -/
theorem valid_swap_iff (h m : ℕ) (S : Finset Pt) :
    Valid h m S ↔ Valid m h (S.map swapE) := by
  have e : ∀ n k (T : Finset Pt), Valid n k T ↔ Set.InjOn (fun C => C \ T) (Rects n k) :=
    fun _ _ _ => Iff.rfl
  rw [e, e, rects_swap h m]
  exact presentation_injective_map_iff swapE (Rects h m) S

lemma axisRect_map_swap (a b c d : ℤ) : (axisRect a b c d).map swapE = axisRect c d a b := by
  ext ⟨x, y⟩
  simp only [axisRect, Finset.map_insert, Finset.map_singleton, mem_insert, mem_singleton]
  simp only [swapE, Function.Embedding.coeFn_mk, Prod.swap_prod_mk]
  tauto

lemma axisRects_swap (h m : ℕ) : AxisRects m h = (Finset.map swapE) '' AxisRects h m := by
  ext C
  constructor
  · rintro ⟨a, b, c, d, hab, hcd, ha, hb, hc, hd, rfl⟩
    exact ⟨axisRect c d a b, ⟨c, d, a, b, hcd, hab, hc, hd, ha, hb, rfl⟩, axisRect_map_swap _ _ _ _⟩
  · rintro ⟨_, ⟨a, b, c, d, hab, hcd, ha, hb, hc, hd, rfl⟩, rfl⟩
    rw [axisRect_map_swap]
    exact ⟨c, d, a, b, hcd, hab, hc, hd, ha, hb, rfl⟩

/-- Axis-validity is invariant under exchanging rows and columns. -/
theorem axisValid_swap_iff (h m : ℕ) (S : Finset Pt) :
    AxisValid h m S ↔ AxisValid m h (S.map swapE) := by
  have e : ∀ n k (T : Finset Pt), AxisValid n k T ↔
      Set.InjOn (fun C => C \ T) (AxisRects n k) := fun _ _ _ => Iff.rfl
  rw [e, e, axisRects_swap h m]
  exact presentation_injective_map_iff swapE (AxisRects h m) S

/-- **Row bound, transposed.** For `h ≥ 3`, an axis-valid blackout of the `h × m` grid has at
most `h + ⌊m²/4⌋` points. -/
theorem row_bound_swap_axis {h m : ℕ} (hh : 3 ≤ h) {S : Finset Pt} (hS : S ⊆ grid h m)
    (hv : AxisValid h m S) : S.card ≤ h + m ^ 2 / 4 := by
  have hS' : S.map swapE ⊆ grid m h := by
    rw [← map_swap_grid]; exact Finset.map_subset_map.mpr hS
  have := row_bound_axis (h := m) (m := h) hh hS' ((axisValid_swap_iff h m S).mp hv)
  rwa [Finset.card_map] at this

/-- **Row bound, transposed, for valid blackouts.** -/
theorem row_bound_swap {h m : ℕ} (hh : 3 ≤ h) {S : Finset Pt} (hS : S ⊆ grid h m)
    (hv : Valid h m S) : S.card ≤ h + m ^ 2 / 4 :=
  row_bound_swap_axis hh hS hv.axisValid

/-- Consequences for small heights: `f(3, m) ≤ m + 2`, `f(4, m) ≤ m + 4`, `f(5, m) ≤ m + 6`,
and `f(6, m) ≤ m + 9` for every `m ≥ 3`. -/
theorem row_bound_small {m : ℕ} (hm : 3 ≤ m) {S : Finset Pt} :
    (S ⊆ grid 3 m → Valid 3 m S → S.card ≤ m + 2) ∧
    (S ⊆ grid 4 m → Valid 4 m S → S.card ≤ m + 4) ∧
    (S ⊆ grid 5 m → Valid 5 m S → S.card ≤ m + 6) ∧
    (S ⊆ grid 6 m → Valid 6 m S → S.card ≤ m + 9) :=
  ⟨fun hS hv => row_bound hm hS hv, fun hS hv => row_bound hm hS hv,
    fun hS hv => row_bound hm hS hv, fun hS hv => row_bound hm hS hv⟩

end Kagey001
