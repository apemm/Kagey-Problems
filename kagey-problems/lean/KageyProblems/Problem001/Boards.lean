import KageyProblems.Problem001.Compute
import KageyProblems.Problem001.RowBound

/-!
# Kagey's Problem 001 — four boards of Section 7 checked by the kernel

Four blackouts of `problem001/jis/pemmasani.tex`, Section 7, proved valid with `decide +kernel`,
so the Lean kernel evaluates the finite computation and the compiler is not trusted. Points are
`(column, row)` with `(1, 1)` at the top left, as in the paper.

The test `boardOK` avoids the full pairwise comparison of `Kernel.lean`. In a collision
`C₁ \ S = C₂ \ S` with `C₁ ≠ C₂`, each rectangle has a black corner (`black_corner`), so it is
`corners (a, q, r)` for a black corner `a` and its two neighbours `q < r` (`anchored_complete`).
For each black `a` and grid point `q`, the third corner `r` is found by solving the right-angle
equation for one coordinate (`partners`, complete by `mem_partners`). The test lists these
triples, codes each presentation and each rectangle as a natural number
(`keyF`, injective on subsets of the grid), and checks that equal presentation codes have equal
rectangle codes, comparing only codes with the same residue modulo `M`. `valid_of_boardOK`
proves that a passing test gives the paper's `Valid`.

## Contents

* `valid_of_boardOK`: soundness of the test.
* `kB68_valid`, `kB68_card`: the `15`-point blackout of Theorem "small grids" is a valid
  blackout of the `6 × 8` grid; `ksix_eight_lower`: `f(6, 8) ≥ 15` (the upper bound
  `f(6, 8) ≤ 15` is a SAT computation and is not formalized here).
* `kS15_valid`, `kS15_card`: the stored `24`-point blackout of the `6 × 15` grid is valid;
  `kfvalue_6_15`: `f(6, 15) = 24`, with the upper bound from `row_bound`.
* `kT13_valid`, `kT13_card`: the `5 × 13` collar test board of `S₈` (Theorem "five rows"(b))
  is valid, with `19` points.
* `kT23_valid`, `kT23_card`: the `6 × 23` collar test board of `S₁₆` (Theorem "six rows"(b))
  is valid, with `32` points.

The finite collar theorem itself, which turns the two test boards into the statements for every
larger width, is not formalized here.
-/

namespace Kagey001

open Finset

/-- The grid points as a list. -/
def ptsL (n m : ℕ) : List Pt :=
  (List.range m).flatMap fun (i : ℕ) => (List.range n).map fun (j : ℕ) => ((i : ℤ) + 1, (j : ℤ) + 1)

lemma mem_ptsL {n m : ℕ} {p : Pt} :
    p ∈ ptsL n m ↔ 1 ≤ p.1 ∧ p.1 ≤ m ∧ 1 ≤ p.2 ∧ p.2 ≤ n := by
  constructor
  · intro h
    obtain ⟨i, hi, hj⟩ := List.mem_flatMap.mp h
    obtain ⟨j, hj', rfl⟩ := List.mem_map.mp hj
    rw [List.mem_range] at hi hj'
    simp only
    omega
  · obtain ⟨a, b⟩ := p
    rintro ⟨h1, h2, h3, h4⟩
    refine List.mem_flatMap.mpr ⟨(a - 1).toNat, List.mem_range.mpr (by omega), ?_⟩
    refine List.mem_map.mpr ⟨(b - 1).toNat, List.mem_range.mpr (by omega), ?_⟩
    simp only [Prod.mk.injEq]
    omega

lemma mem_ptsL_iff_grid {n m : ℕ} {p : Pt} : p ∈ ptsL n m ↔ p ∈ grid n m := by
  rw [mem_ptsL, mem_grid]

/-- The test for a triple `(a, q, r)`: right angle at `a`, `q < r`, `r` and the fourth corner
in the grid. -/
def anchorOK (n m : ℕ) (a q r : Pt) : Bool :=
  decide ((q - a).1 * (r - a).1 + (q - a).2 * (r - a).2 = 0 ∧ q ≠ a ∧ r ≠ a ∧ lexLt q r ∧
    (1 ≤ r.1 ∧ r.1 ≤ m ∧ 1 ≤ r.2 ∧ r.2 ≤ n) ∧
    1 ≤ (q + r - a).1 ∧ (q + r - a).1 ≤ m ∧ 1 ≤ (q + r - a).2 ∧ (q + r - a).2 ≤ n)

/-- The integers `1, ..., n` as a list. -/
def rangeL (n : ℕ) : List ℤ := (List.range n).map fun (j : ℕ) => (j : ℤ) + 1

/-- The candidates for the third corner `r` of a right angle at `a` with first leg `q - a`:
the grid points `r` with `(q - a) ⬝ (r - a) = 0`, found by solving for one coordinate. -/
def partners (n m : ℕ) (a q : Pt) : List Pt :=
  if q.1 - a.1 = 0 then (rangeL m).map fun x => (x, a.2)
  else (rangeL n).filterMap fun y =>
    if (q.2 - a.2) * (y - a.2) % (q.1 - a.1) = 0 then
      some (a.1 - (q.2 - a.2) * (y - a.2) / (q.1 - a.1), y)
    else none

lemma mem_rangeL {n : ℕ} {y : ℤ} (h1 : 1 ≤ y) (h2 : y ≤ n) : y ∈ rangeL n :=
  List.mem_map.mpr ⟨(y - 1).toNat, List.mem_range.mpr (by omega), by omega⟩

lemma mem_partners {n m : ℕ} {a q r : Pt} (hqa : q ≠ a) (hr : r ∈ grid n m)
    (hd : (q - a).1 * (r - a).1 + (q - a).2 * (r - a).2 = 0) : r ∈ partners n m a q := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨q1, q2⟩ := q
  obtain ⟨r1, r2⟩ := r
  rw [mem_grid] at hr
  simp only [Prod.mk_sub_mk] at hd hr
  simp only [ne_eq, Prod.mk.injEq, not_and_or] at hqa
  unfold partners
  split_ifs with h
  · have hq2 : q2 - a2 ≠ 0 := by omega
    have hr2 : r2 - a2 = 0 := by
      rw [h, zero_mul, zero_add] at hd
      exact (mul_eq_zero.mp hd).resolve_left hq2
    exact List.mem_map.mpr ⟨r1, mem_rangeL hr.1 hr.2.1, Prod.ext rfl (by dsimp only; omega)⟩
  · have he : (q2 - a2) * (r2 - a2) = (q1 - a1) * (-(r1 - a1)) := by linear_combination hd
    refine List.mem_filterMap.mpr ⟨r2, mem_rangeL hr.2.2.1 hr.2.2.2, ?_⟩
    simp only
    rw [if_pos (by rw [he]; exact Int.mul_emod_right _ _), he, Int.mul_ediv_cancel_left _ h]
    simp

/-- The triples with right angle at a point of `B`. -/
def anchored (n m : ℕ) (B : List Pt) : List (Pt × Pt × Pt) :=
  B.flatMap fun a => (ptsL n m).flatMap fun q =>
    ((partners n m a q).filter fun r => anchorOK n m a q r).map fun r => (a, q, r)

lemma mem_anchored {n m : ℕ} {B : List Pt} {a q r : Pt} (ha : a ∈ B) (hq : q ∈ ptsL n m)
    (hr : r ∈ partners n m a q) (hok : anchorOK n m a q r = true) :
    (a, q, r) ∈ anchored n m B := by
  simp only [anchored, List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq]
  exact ⟨a, ha, q, hq, r, ⟨hr, hok⟩, rfl, rfl, rfl⟩

/-- An injective code of a point with nonnegative coordinates. -/
def idx (p : Pt) : ℕ := Nat.pair p.1.toNat p.2.toNat

/-- The code of a finite set of points: the sum of `2 ^ idx p`. -/
def keyF (A : Finset Pt) : ℕ := ∑ p ∈ A, 2 ^ idx p

lemma idx_inj {n m : ℕ} {p q : Pt} (hp : p ∈ grid n m) (hq : q ∈ grid n m)
    (h : idx p = idx q) : p = q := by
  rw [mem_grid] at hp hq
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [idx, Nat.pair_eq_pair] at h
  simp only at hp hq
  obtain ⟨h1, h2⟩ := h
  ext <;> simp only <;> omega

lemma keyF_inj {n m : ℕ} {A A' : Finset Pt} (hA : A ⊆ grid n m) (hA' : A' ⊆ grid n m)
    (h : keyF A = keyF A') : A = A' := by
  have hi : ∀ X : Finset Pt, X ⊆ grid n m → keyF X = ∑ i ∈ X.image idx, 2 ^ i := by
    intro X hX
    rw [keyF, Finset.sum_image]
    intro x hx y hy hxy
    exact idx_inj (hX hx) (hX hy) hxy
  rw [hi A hA, hi A' hA'] at h
  have him : A.image idx = A'.image idx := by
    rw [← Finset.toFinset_bitIndices_sum_two_pow (A.image idx), h,
      Finset.toFinset_bitIndices_sum_two_pow]
  ext x
  constructor
  · intro hx
    have : idx x ∈ A'.image idx := him ▸ Finset.mem_image_of_mem idx hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp this
    rwa [← idx_inj (hA' hy) (hA hx) hyx]
  · intro hx
    have : idx x ∈ A.image idx := him.symm ▸ Finset.mem_image_of_mem idx hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp this
    rwa [← idx_inj (hA hy) (hA' hx) hyx]

/-- The pair (code of the presentation, code of the rectangle) of each anchored triple. -/
def entries (n m : ℕ) (B : List Pt) : List (ℕ × ℕ) :=
  (anchored n m B).map fun t => (keyF ((corners t).filter (· ∉ B)), keyF (corners t))

/-- Equal first codes force equal second codes. -/
def pairOK (E : List (ℕ × ℕ)) : Bool :=
  E.all fun x => E.all fun y => !(x.1 == y.1) || x.2 == y.2

/-- `pairOK` within each class of the first code modulo `M`. -/
def bucketOK (M : ℕ) (E : List (ℕ × ℕ)) : Bool :=
  (List.range M).all fun b => pairOK (E.filter fun x => x.1 % M == b)

/-- The full test of a blackout `B` of the `n × m` grid. -/
def boardOK (n m M : ℕ) (B : List Pt) : Bool := bucketOK M (entries n m B)

lemma bucketOK_spec {M : ℕ} {E : List (ℕ × ℕ)} (hM : 0 < M) (h : bucketOK M E = true)
    {x y : ℕ × ℕ} (hx : x ∈ E) (hy : y ∈ E) (hxy : x.1 = y.1) : x.2 = y.2 := by
  simp only [bucketOK, pairOK, List.all_eq_true, List.mem_range, List.mem_filter, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  rcases h (x.1 % M) (Nat.mod_lt _ hM) x ⟨hx, rfl⟩ y ⟨hy, by rw [hxy]⟩ with h | h
  · exact absurd hxy h
  · exact h

lemma card_of_rects {n m : ℕ} {C : Finset Pt} (hC : C ∈ Rects n m) : C.card = 4 := by
  obtain ⟨⟨p, u, v, hu, hv, hperp, rfl⟩, _⟩ := hC
  obtain ⟨nab, nac, nad, nbc, nbd, ncd⟩ := corners_distinct (p := p) hu hv hperp
  rw [Finset.card_insert_of_notMem (by simp [nab, nac, nad]),
    Finset.card_insert_of_notMem (by simp [nbc, nbd]),
    Finset.card_insert_of_notMem (by simp [ncd]), Finset.card_singleton]

/-- A rectangle with a black corner `a` comes from an anchored triple. -/
lemma anchored_complete {n m : ℕ} {B : List Pt} {C : Finset Pt} (hC : C ∈ Rects n m)
    {a : Pt} (haC : a ∈ C) (haB : a ∈ B) : ∃ t ∈ anchored n m B, corners t = C := by
  have step : ∀ a y z : Pt, a ∈ B →
      (y - a).1 * (z - a).1 + (y - a).2 * (z - a).2 = 0 → y ≠ a → z ≠ a →
      y ≠ z → y ∈ grid n m → z ∈ grid n m → y + z - a ∈ grid n m →
      ∃ t ∈ anchored n m B, corners t = {a, y, z, y + z - a} := by
    intro a y z haB hperp hya hza hyz hy hz ho
    have hzp : z ∈ partners n m a y := mem_partners hya hz hperp
    have hyp : y ∈ partners n m a z := mem_partners hza hy (by linear_combination hperp)
    have hyg := mem_grid.mp hy
    have hzg := mem_grid.mp hz
    rw [← mem_ptsL_iff_grid] at hy hz
    rw [mem_grid] at ho
    rcases lexLt_trichotomy y z with h | h | h
    · refine ⟨(a, y, z), mem_anchored haB hy hzp ?_, rfl⟩
      simp only [anchorOK, decide_eq_true_eq]
      exact ⟨hperp, hya, hza, h, hzg, ho⟩
    · exact absurd h hyz
    · refine ⟨(a, z, y), mem_anchored haB hz hyp ?_, ?_⟩
      · simp only [anchorOK, decide_eq_true_eq]
        refine ⟨by linear_combination hperp, hza, hya, h, hyg, ?_⟩
        rw [add_comm z y]; exact ho
      · simp only [corners]
        rw [Finset.insert_comm z y, add_comm z y]
  obtain ⟨⟨p, u, v, hu, hv, hperp, rfl⟩, hsub⟩ := hC
  have ha : p ∈ grid n m := hsub (by simp)
  have hb : p + u ∈ grid n m := hsub (by simp)
  have hc : p + v ∈ grid n m := hsub (by simp)
  have hd : p + u + v ∈ grid n m := hsub (by simp)
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
  simp only [Finset.mem_insert, Finset.mem_singleton] at haC
  rcases haC with h | h | h | h <;> rw [h] at haB
  · obtain ⟨t, ht, he⟩ := step p (p + u) (p + v) haB (by rw [e1, e2]; exact hperp) (Ne.symm nab)
      (Ne.symm nac) nbc hb hc (by rw [hbca]; exact hd)
    exact ⟨t, ht, by rw [he, hbca]⟩
  · obtain ⟨t, ht, he⟩ := step (p + u) p (p + u + v) haB
      (by rw [e3, e4]; simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination -hperp)
      nab (Ne.symm nbd) nad ha hd (by rw [hadb]; exact hc)
    refine ⟨t, ht, ?_⟩
    rw [he, hadb]
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor <;> rintro (rfl | rfl | rfl | rfl) <;> simp
  · obtain ⟨t, ht, he⟩ := step (p + v) p (p + u + v) haB
      (by rw [e5, e6]; simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination -hperp)
      nac (Ne.symm ncd) nad ha hd (by rw [hadc]; exact hb)
    refine ⟨t, ht, ?_⟩
    rw [he, hadc]
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor <;> rintro (rfl | rfl | rfl | rfl) <;> simp
  · obtain ⟨t, ht, he⟩ := step (p + u + v) (p + u) (p + v) haB
      (by rw [e7, e8]; simp only [Prod.fst_neg, Prod.snd_neg]; linear_combination hperp)
      nbd ncd nbc hb hc (by rw [hbcd]; exact ha)
    refine ⟨t, ht, ?_⟩
    rw [he, hbcd]
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor <;> rintro (rfl | rfl | rfl | rfl) <;> simp

/-- In a collision, each of the two rectangles has a black corner. -/
lemma black_corner {n m : ℕ} {S C₁ C₂ : Finset Pt} (h₁ : C₁ ∈ Rects n m)
    (h₂ : C₂ ∈ Rects n m) (hp : C₁ \ S = C₂ \ S) (hne : C₁ ≠ C₂) : ∃ a ∈ C₁, a ∈ S := by
  by_contra hno
  push Not at hno
  have hsub : C₁ ⊆ C₂ := by
    intro x hx
    have : x ∈ C₁ \ S := Finset.mem_sdiff.mpr ⟨hx, hno x hx⟩
    rw [hp] at this
    exact (Finset.mem_sdiff.mp this).1
  exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [card_of_rects h₁, card_of_rects h₂]))

/-- **Soundness of the test.** -/
theorem valid_of_boardOK {n m M : ℕ} {B : List Pt} (hM : 0 < M)
    (h : boardOK n m M B = true) : Valid n m B.toFinset := by
  intro C₁ h₁ C₂ h₂ hp
  by_contra hne
  simp only [pres] at hp
  obtain ⟨a, ha, haS⟩ := black_corner h₁ h₂ hp hne
  obtain ⟨b, hb, hbS⟩ := black_corner h₂ h₁ hp.symm (Ne.symm hne)
  obtain ⟨t₁, ht₁, rfl⟩ := anchored_complete h₁ ha (List.mem_toFinset.mp haS)
  obtain ⟨t₂, ht₂, rfl⟩ := anchored_complete h₂ hb (List.mem_toFinset.mp hbS)
  have hf : ∀ t : Pt × Pt × Pt, (corners t).filter (· ∉ B) = corners t \ B.toFinset := by
    intro t
    ext x
    simp [Finset.mem_sdiff, Finset.mem_filter]
  have key := bucketOK_spec hM h (List.mem_map_of_mem (f := fun t =>
      (keyF ((corners t).filter (· ∉ B)), keyF (corners t))) ht₁)
    (List.mem_map_of_mem (f := fun t =>
      (keyF ((corners t).filter (· ∉ B)), keyF (corners t))) ht₂)
    (by simp only [hf, hp])
  exact hne (keyF_inj h₁.2 h₂.2 key)

/-! ### The boards -/

/-- The blackout of Theorem "small grids" on the `6 × 8` grid. -/
def kB68 : Finset Pt :=
  {(1, 1), (1, 5), (2, 1), (3, 1), (3, 2), (3, 3), (4, 3), (4, 4), (5, 4), (6, 4), (7, 4),
    (7, 5), (7, 6), (8, 2), (8, 6)}

/-- `kB68` as a list, the input of `boardOK`. -/
def kB68L : List Pt :=
  [(1, 1), (1, 5), (2, 1), (3, 1), (3, 2), (3, 3), (4, 3), (4, 4), (5, 4), (6, 4), (7, 4),
    (7, 5), (7, 6), (8, 2), (8, 6)]

theorem kB68_eq : kB68 = kB68L.toFinset := by decide +kernel

theorem kB68_card : kB68.card = 15 ∧ kB68 ⊆ grid 6 8 := by
  rw [grid_eq_gridC]; decide +kernel

set_option maxHeartbeats 0 in
theorem kB68_valid : Valid 6 8 kB68 := by
  rw [kB68_eq]
  exact valid_of_boardOK (M := 31) (by norm_num) (by decide +kernel)

/-- The `24`-point blackout of the `6 × 15` grid stored in `jis/data/six_row_sat_w15_A.json`
(row partition `{1, 3, 5} | {2, 4, 6}`). -/
def kS15 : Finset Pt :=
  {(1, 5), (1, 6), (2, 4), (2, 5), (3, 3), (3, 4), (4, 2), (4, 3), (5, 1), (6, 1), (7, 1),
    (7, 4), (8, 1), (9, 1), (10, 1), (10, 2), (11, 3), (11, 6), (12, 1), (13, 2), (13, 5),
    (14, 6), (15, 1), (15, 6)}

/-- `kS15` as a list, the input of `boardOK`. -/
def kS15L : List Pt :=
  [(1, 5), (1, 6), (2, 4), (2, 5), (3, 3), (3, 4), (4, 2), (4, 3), (5, 1), (6, 1), (7, 1),
    (7, 4), (8, 1), (9, 1), (10, 1), (10, 2), (11, 3), (11, 6), (12, 1), (13, 2), (13, 5),
    (14, 6), (15, 1), (15, 6)]

theorem kS15_eq : kS15 = kS15L.toFinset := by decide +kernel

theorem kS15_card : kS15.card = 24 ∧ kS15 ⊆ grid 6 15 := by
  rw [grid_eq_gridC]; decide +kernel

set_option maxHeartbeats 0 in
theorem kS15_valid : Valid 6 15 kS15 := by
  rw [kS15_eq]
  exact valid_of_boardOK (M := 47) (by norm_num) (by decide +kernel)

/-- The `5 × 13` collar test board of `S₈`: `S₈` followed by `(9, 1), …, (13, 1)`. -/
def kT13 : Finset Pt :=
  {(1, 1), (1, 4), (2, 4), (2, 5), (3, 2), (3, 5), (4, 5), (5, 5), (6, 3), (6, 4), (7, 2),
    (7, 3), (8, 1), (8, 2), (9, 1), (10, 1), (11, 1), (12, 1), (13, 1)}

/-- `kT13` as a list, the input of `boardOK`. -/
def kT13L : List Pt :=
  [(1, 1), (1, 4), (2, 4), (2, 5), (3, 2), (3, 5), (4, 5), (5, 5), (6, 3), (6, 4), (7, 2),
    (7, 3), (8, 1), (8, 2), (9, 1), (10, 1), (11, 1), (12, 1), (13, 1)]

theorem kT13_eq : kT13 = kT13L.toFinset := by decide +kernel

theorem kT13_card : kT13.card = 19 ∧ kT13 ⊆ grid 5 13 := by
  rw [grid_eq_gridC]; decide +kernel

set_option maxHeartbeats 0 in
theorem kT13_valid : Valid 5 13 kT13 := by
  rw [kT13_eq]
  exact valid_of_boardOK (M := 31) (by norm_num) (by decide +kernel)

/-- The `6 × 23` collar test board of `S₁₆`: `S₁₆` (part (b) of the figure in Section 7, the
width-16 witness of `jis/data/six_row_sat_w16_A.json` for the row partition
`{1, 3, 5} | {2, 4, 6}`) followed by `(17, 1), …, (23, 1)`. -/
def kT23 : Finset Pt :=
  {(1, 3), (1, 6), (2, 1), (2, 4), (3, 2), (3, 5), (4, 6), (5, 6), (6, 1), (6, 6), (7, 6),
    (8, 6), (9, 5), (9, 6), (10, 4), (10, 5), (11, 4), (12, 4), (13, 4), (14, 3), (14, 4),
    (15, 2), (15, 3), (16, 1), (16, 2), (17, 1), (18, 1), (19, 1), (20, 1), (21, 1), (22, 1),
    (23, 1)}

/-- `kT23` as a list, the input of `boardOK`. -/
def kT23L : List Pt :=
  [(1, 3), (1, 6), (2, 1), (2, 4), (3, 2), (3, 5), (4, 6), (5, 6), (6, 1), (6, 6), (7, 6),
    (8, 6), (9, 5), (9, 6), (10, 4), (10, 5), (11, 4), (12, 4), (13, 4), (14, 3), (14, 4),
    (15, 2), (15, 3), (16, 1), (16, 2), (17, 1), (18, 1), (19, 1), (20, 1), (21, 1), (22, 1),
    (23, 1)]

theorem kT23_eq : kT23 = kT23L.toFinset := by decide +kernel

theorem kT23_card : kT23.card = 32 ∧ kT23 ⊆ grid 6 23 := by
  rw [grid_eq_gridC]; decide +kernel

set_option maxHeartbeats 0 in
theorem kT23_valid : Valid 6 23 kT23 := by
  rw [kT23_eq]
  exact valid_of_boardOK (M := 67) (by norm_num) (by decide +kernel)

/-- **`f(6, 8) ≥ 15`, kernel-checked.** -/
theorem ksix_eight_lower : ∃ S ⊆ grid 6 8, Valid 6 8 S ∧ S.card = 15 :=
  ⟨kB68, kB68_card.2, kB68_valid, kB68_card.1⟩

/-- **`f(6, 15) = 24`, entirely kernel-checked.** -/
theorem kfvalue_6_15 :
    (∃ S ⊆ grid 6 15, Valid 6 15 S ∧ S.card = 24) ∧
      ∀ S ⊆ grid 6 15, Valid 6 15 S → S.card ≤ 24 :=
  ⟨⟨kS15, kS15_card.2, kS15_valid, kS15_card.1⟩, fun S hS hv => row_bound (by norm_num) hS hv⟩

end Kagey001
