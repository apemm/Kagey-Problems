import KageyProblems.Problem001.Tilt

/-!
# Kagey's Problem 001 — boundary padding

The padded boards `S_{L,R}` of Section 7 of `problem001/jis/pemmasani.tex` and the two
localization steps in the proof of Theorem "finite collar".

The padded board uses the columns `1-L, …, m+R`, so it is stated in window coordinates:
`gridW h lo hi` is the grid of columns `lo..hi` and rows `1..h`, and `ValidW h lo hi` is
validity for the rectangles of that window. `valid_pad_iff` translates a padded board back to
the one-based `Valid` of the paper.

## Contents

* `gridW`, `RectsW`, `ValidW`: windows; `validW_one_iff`: `ValidW h 1 m = Valid h m`.
* `shiftE`, `validW_shift_iff`: validity is invariant under translating the columns.
* `pad h m L R ρ S`: the padded board `S_{L,R}` with padding row `ρ`; `valid_pad_iff`: its
  window validity is the paper's validity of the translated board on `L + m + R` columns.
* `pad_col_two_black`: a column of `S_{L,R}` with two black points is an original column and
  both points are points of `S`; `pad_black_off_row`: a black point outside the padding row is
  a point of `S`.
* `pad_agree`, `pres_pad_agree`: two padded boards agree on their common columns.
* `weak_tilt_local`: a weak tilted rectangle (at most two visible corners) of `S_{L,R}` with
  a boundary padding row lies in the common columns of `S_{L,R}` and `S_{L',R'}`, when
  `L' ≥ W_h` or `L = 0`, and `R' ≥ W_h` or `R = 0`.
* `axis_tie_local`: an axis-aligned rectangle of `S_{L,R}` with the same presentation as a
  rectangle inside a window containing the original columns lies in that window.
-/

namespace Kagey001

open Finset

/-! ### Windows -/

/-- The grid of columns `lo..hi` and rows `1..h`. -/
noncomputable def gridW (h : ℕ) (lo hi : ℤ) : Finset Pt :=
  Finset.Icc lo hi ×ˢ Finset.Icc (1 : ℤ) h

/-- The rectangles of the window `gridW h lo hi`. -/
def RectsW (h : ℕ) (lo hi : ℤ) : Set (Finset Pt) := {C | IsRect C ∧ C ⊆ gridW h lo hi}

/-- Validity for the rectangles of the window `gridW h lo hi`. -/
def ValidW (h : ℕ) (lo hi : ℤ) (S : Finset Pt) : Prop :=
  ∀ C₁ ∈ RectsW h lo hi, ∀ C₂ ∈ RectsW h lo hi, pres S C₁ = pres S C₂ → C₁ = C₂

lemma mem_gridW {h : ℕ} {lo hi : ℤ} {p : Pt} :
    p ∈ gridW h lo hi ↔ lo ≤ p.1 ∧ p.1 ≤ hi ∧ 1 ≤ p.2 ∧ p.2 ≤ h := by
  simp [gridW, Finset.mem_product, Finset.mem_Icc, and_assoc]

lemma gridW_one (h m : ℕ) : gridW h 1 m = grid h m := rfl

theorem validW_one_iff (h m : ℕ) (S : Finset Pt) : ValidW h 1 m S ↔ Valid h m S := Iff.rfl

lemma gridW_mono {h : ℕ} {lo hi lo' hi' : ℤ} (hl : lo ≤ lo') (hh : hi' ≤ hi) :
    gridW h lo' hi' ⊆ gridW h lo hi := by
  intro p hp
  rw [mem_gridW] at hp ⊢
  omega

theorem ValidW.mono_window {h : ℕ} {lo hi lo' hi' : ℤ} {S : Finset Pt} (hl : lo ≤ lo')
    (hh : hi' ≤ hi) (hv : ValidW h lo hi S) : ValidW h lo' hi' S :=
  fun C₁ h₁ C₂ h₂ hp => hv C₁ ⟨h₁.1, h₁.2.trans (gridW_mono hl hh)⟩ C₂
    ⟨h₂.1, h₂.2.trans (gridW_mono hl hh)⟩ hp

/-! ### Translating the columns -/

/-- Translation of the columns by `t`. -/
def shiftE (t : ℤ) : Pt ↪ Pt := ⟨fun p => p + (t, 0), add_left_injective _⟩

lemma shiftE_apply (t : ℤ) (p : Pt) : shiftE t p = p + (t, 0) := rfl

lemma isRect_map_shift {C : Finset Pt} (t : ℤ) (hC : IsRect C) : IsRect (C.map (shiftE t)) := by
  obtain ⟨p, u, v, hu, hv, huv, rfl⟩ := hC
  refine ⟨p + (t, 0), u, v, hu, hv, huv, ?_⟩
  simp only [Finset.map_insert, Finset.map_singleton, shiftE_apply]
  have e1 : p + u + (t, 0) = p + (t, 0) + u := by abel
  have e2 : p + v + (t, 0) = p + (t, 0) + v := by abel
  have e3 : p + u + v + (t, 0) = p + (t, 0) + u + v := by abel
  rw [e1, e2, e3]

lemma map_shift_shift (t : ℤ) (C : Finset Pt) : (C.map (shiftE (-t))).map (shiftE t) = C := by
  rw [Finset.map_map]
  ext p
  simp only [Finset.mem_map, Function.Embedding.trans_apply, shiftE_apply]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have : q + (-t, 0) + (t, 0) = q := by
      rw [add_assoc, Prod.mk_add_mk]; simp
    rwa [this]
  · intro hp
    refine ⟨p, hp, ?_⟩
    rw [add_assoc, Prod.mk_add_mk]; simp

lemma map_shift_gridW (h : ℕ) (lo hi t : ℤ) :
    (gridW h lo hi).map (shiftE t) = gridW h (lo + t) (hi + t) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_map, mem_gridW, shiftE_apply, Prod.exists, Prod.mk_add_mk,
    Prod.mk.injEq, add_zero]
  constructor
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    omega
  · intro hab
    exact ⟨a - t, b, by omega, by ring, rfl⟩

lemma rectsW_shift (h : ℕ) (lo hi t : ℤ) :
    RectsW h (lo + t) (hi + t) = (Finset.map (shiftE t)) '' RectsW h lo hi := by
  ext C
  constructor
  · rintro ⟨hC, hsub⟩
    refine ⟨C.map (shiftE (-t)), ⟨isRect_map_shift (-t) hC, ?_⟩, map_shift_shift t C⟩
    have := Finset.map_subset_map (f := shiftE (-t)) |>.mpr hsub
    rw [map_shift_gridW] at this
    simpa using this
  · rintro ⟨D, ⟨hD, hsub⟩, rfl⟩
    refine ⟨isRect_map_shift t hD, ?_⟩
    rw [← map_shift_gridW]
    exact Finset.map_subset_map.mpr hsub

/-- Validity is invariant under translating the columns. -/
theorem validW_shift_iff (h : ℕ) (lo hi t : ℤ) (S : Finset Pt) :
    ValidW h lo hi S ↔ ValidW h (lo + t) (hi + t) (S.map (shiftE t)) := by
  have e : ∀ a b (T : Finset Pt), ValidW h a b T ↔ Set.InjOn (fun C => C \ T) (RectsW h a b) :=
    fun _ _ _ => Iff.rfl
  rw [e, e, rectsW_shift h lo hi t]
  exact presentation_injective_map_iff (shiftE t) (RectsW h lo hi) S

/-! ### Padded boards -/

/-- The padded board `S_{L,R}`: the points of `S` in the `h × m` grid, and the added columns
`1-L, …, 0` and `m+1, …, m+R`, each black exactly in the padding row `ρ`. -/
noncomputable def pad (h m L R : ℕ) (ρ : ℤ) (S : Finset Pt) : Finset Pt :=
  (S ∩ grid h m) ∪ ((Finset.Icc (1 - (L : ℤ)) 0 ∪ Finset.Icc ((m : ℤ) + 1) (m + R)) ×ˢ {ρ})

lemma mem_pad {h m L R : ℕ} {ρ : ℤ} {S : Finset Pt} {p : Pt} :
    p ∈ pad h m L R ρ S ↔ (p ∈ S ∧ p ∈ grid h m) ∨
      (((1 - (L : ℤ) ≤ p.1 ∧ p.1 ≤ 0) ∨ ((m : ℤ) + 1 ≤ p.1 ∧ p.1 ≤ m + R)) ∧ p.2 = ρ) := by
  simp only [pad, mem_union, mem_inter, mem_product, mem_Icc, mem_singleton]

/-- The one-based form of a padded board: translate by `L` columns. -/
theorem valid_pad_iff (h m L R : ℕ) (ρ : ℤ) (S : Finset Pt) :
    ValidW h (1 - L) (m + R) (pad h m L R ρ S) ↔
      Valid h (L + m + R) ((pad h m L R ρ S).map (shiftE L)) := by
  rw [validW_shift_iff h _ _ (L : ℤ), ← validW_one_iff]
  have e1 : (1 - (L : ℤ) + L) = 1 := by ring
  have e2 : (m : ℤ) + R + L = ((L + m + R : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2]

/-- With no left padding, the padded board is `S` followed by the right padding. -/
lemma pad_zero_left (h m R : ℕ) (ρ : ℤ) {S : Finset Pt} (hS : S ⊆ grid h m) :
    pad h m 0 R ρ S = S ∪ (Finset.Icc ((m : ℤ) + 1) (m + R) ×ˢ {ρ}) := by
  have hI : Finset.Icc (1 - ((0 : ℕ) : ℤ)) 0 = ∅ := by
    ext x; simp only [mem_Icc, Nat.cast_zero, sub_zero, Finset.notMem_empty, iff_false]; omega
  rw [pad, Finset.inter_eq_left.mpr hS, hI, Finset.empty_union]

lemma inter_grid_subset_pad (h m L R : ℕ) (ρ : ℤ) (S : Finset Pt) :
    S ∩ grid h m ⊆ pad h m L R ρ S := Finset.subset_union_left

/-- **Padding preserves the column structure.** A column of `S_{L,R}` with two black points is
an original column, and both points are points of `S`. -/
theorem pad_col_two_black {h m L R : ℕ} {ρ : ℤ} {S : Finset Pt} {x j j' : ℤ} (hjj : j ≠ j')
    (h₁ : (x, j) ∈ pad h m L R ρ S) (h₂ : (x, j') ∈ pad h m L R ρ S) :
    (x, j) ∈ S ∩ grid h m ∧ (x, j') ∈ S ∩ grid h m := by
  rw [mem_pad] at h₁ h₂
  rw [mem_inter, mem_inter]
  simp only [mem_grid'] at h₁ h₂ ⊢
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact ⟨h₁, h₂⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

/-- A black point of `S_{L,R}` outside the padding row is a point of `S`. -/
theorem pad_black_off_row {h m L R : ℕ} {ρ : ℤ} {S : Finset Pt} {p : Pt}
    (hp : p ∈ pad h m L R ρ S) (hρ : p.2 ≠ ρ) : p ∈ S ∩ grid h m := by
  rw [mem_pad] at hp
  rcases hp with hp | hp
  · exact mem_inter.mpr hp
  · exact absurd hp.2 hρ

/-- Two padded boards agree on their common columns. -/
theorem pad_agree {h m L R Ls Rs : ℕ} {ρ : ℤ} {S : Finset Pt} {p : Pt}
    (hp : p ∈ gridW h (1 - (min L Ls : ℕ)) (m + (min R Rs : ℕ))) :
    p ∈ pad h m L R ρ S ↔ p ∈ pad h m Ls Rs ρ S := by
  rw [mem_gridW] at hp
  rw [mem_pad, mem_pad]
  have k1 : (1 - (L : ℤ) ≤ p.1 ∧ p.1 ≤ 0) ↔ (1 - (Ls : ℤ) ≤ p.1 ∧ p.1 ≤ 0) := by
    rw [Nat.cast_min] at hp; omega
  have k2 : ((m : ℤ) + 1 ≤ p.1 ∧ p.1 ≤ m + R) ↔ ((m : ℤ) + 1 ≤ p.1 ∧ p.1 ≤ m + Rs) := by
    rw [Nat.cast_min] at hp; omega
  rw [k1, k2]

theorem pres_pad_agree {h m L R Ls Rs : ℕ} {ρ : ℤ} {S C : Finset Pt}
    (hC : C ⊆ gridW h (1 - (min L Ls : ℕ)) (m + (min R Rs : ℕ))) :
    pres (pad h m L R ρ S) C = pres (pad h m Ls Rs ρ S) C := by
  ext p
  simp only [pres, mem_sdiff]
  constructor
  · rintro ⟨hp, hn⟩
    exact ⟨hp, fun h' => hn ((pad_agree (hC hp)).mpr h')⟩
  · rintro ⟨hp, hn⟩
    exact ⟨hp, fun h' => hn ((pad_agree (hC hp)).mp h')⟩

lemma rows_of_mem_rectsW {h : ℕ} {lo hi : ℤ} {C : Finset Pt} (hC : C ∈ RectsW h lo hi) :
    ∀ c ∈ C, 1 ≤ c.2 ∧ c.2 ≤ h := fun c hc => by
  have := mem_gridW.mp (hC.2 hc)
  exact ⟨this.2.2.1, this.2.2.2⟩

/-- **Localization of weak tilted rectangles.** Let the padding row be a boundary row. A tilted
rectangle of `S_{L,R}` with at most two visible corners has a black corner in an original
column, so by the span bound it lies in the columns `1 - min L L' .. m + min R R'` common to
`S_{L,R}` and `S_{L',R'}`, provided `L = 0` or `L' ≥ W_h`, and `R = 0` or `R' ≥ W_h`. -/
theorem weak_tilt_local {h m L R Ls Rs : ℕ} {ρ : ℤ} (hρ : ρ = 1 ∨ ρ = h) {S : Finset Pt}
    (hL : L = 0 ∨ spanW h ≤ Ls) (hR : R = 0 ∨ spanW h ≤ Rs) {C : Finset Pt}
    (hC : C ∈ RectsW h (1 - L) (m + R)) (ht : IsTilt C)
    (hw : (pres (pad h m L R ρ S) C).card ≤ 2) :
    C ⊆ gridW h (1 - (min L Ls : ℕ)) (m + (min R Rs : ℕ)) := by
  set U := pad h m L R ρ S
  have hcard := ht.isRect.card_eq_four
  have h2 : 1 < (C ∩ U).card := by
    have := card_sdiff_add_card_inter C U
    unfold pres at hw
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h2
  rw [mem_inter] at hp hq
  have hrows := rows_of_mem_rectsW hC
  -- One of the two black corners is outside the padding row.
  obtain ⟨e, heC, heU, heρ⟩ : ∃ e ∈ C, e ∈ U ∧ e.2 ≠ ρ := by
    by_cases hp2 : p.2 = ρ
    · refine ⟨q, hq.1, hq.2, fun hq2 => hpq ?_⟩
      exact ht.eq_of_row_eq_bound hrows hρ hp.1 hq.1 hp2 hq2
    · exact ⟨p, hp.1, hp.2, hp2⟩
  have he := mem_grid.mp (mem_inter.mp (pad_black_off_row heU heρ)).2
  intro c hc
  have k1 := ht.col_sub_le hrows hc heC
  have k2 := ht.col_sub_le hrows heC hc
  have k3 := mem_gridW.mp (hC.2 hc)
  rw [mem_gridW, Nat.cast_min, Nat.cast_min]
  rcases hL with hL | hL <;> rcases hR with hR | hR <;> subst_vars <;> push_cast at * <;> omega

/-- **Step 3 of the collar theorem.** An axis-aligned rectangle `C₂` of `S_{L,R}` with the same
presentation as a rectangle `C₁` inside a window containing the original columns lies in that
window: a column of `C₂` with a visible corner is a column of `C₁`, and a column with two black
corners is an original column. -/
theorem axis_tie_local {h m L R : ℕ} {ρ : ℤ} {S : Finset Pt} {lo hi : ℤ}
    (hlo : lo ≤ 1) (hhi : (m : ℤ) ≤ hi) {C₁ C₂ : Finset Pt} (h₁ : C₁ ⊆ gridW h lo hi)
    (h₂ : C₂ ∈ RectsW h (1 - L) (m + R)) (hax : IsAxis C₂)
    (hp : pres (pad h m L R ρ S) C₁ = pres (pad h m L R ρ S) C₂) : C₂ ⊆ gridW h lo hi := by
  obtain ⟨a, b, c, d, hab, hcd, rfl⟩ := hax
  have hrows := rows_of_mem_rectsW h₂
  have vis : ∀ y : Pt, y ∈ axisRect a b c d → y ∉ pad h m L R ρ S → lo ≤ y.1 ∧ y.1 ≤ hi := by
    intro y hy hn
    have : y ∈ pres (pad h m L R ρ S) (axisRect a b c d) := mem_sdiff.mpr ⟨hy, hn⟩
    rw [← hp] at this
    have := mem_gridW.mp (h₁ (mem_sdiff.mp this).1)
    exact ⟨this.1, this.2.1⟩
  have key : ∀ x : ℤ, (x, c) ∈ axisRect a b c d → (x, d) ∈ axisRect a b c d →
      lo ≤ x ∧ x ≤ hi := by
    intro x hxc hxd
    by_cases w1 : (x, c) ∈ pad h m L R ρ S
    · by_cases w2 : (x, d) ∈ pad h m L R ρ S
      · have := mem_grid'.mp (mem_inter.mp (pad_col_two_black hcd w1 w2).1).2
        omega
      · exact vis _ hxd w2
    · exact vis _ hxc w1
  intro y hy
  have hr := hrows y hy
  rw [mem_gridW]
  have ka := key a (by simp [axisRect]) (by simp [axisRect])
  have kb := key b (by simp [axisRect]) (by simp [axisRect])
  simp only [axisRect, mem_insert, mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl <;> simp only at hr ⊢ <;> omega

end Kagey001
