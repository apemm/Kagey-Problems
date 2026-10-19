import KageyProblems.Problem001.Collar
import KageyProblems.Problem001.Kernel
import KageyProblems.Problem001.Boards

/-!
# Kagey's Problem 001 — five and six rows for every large width

Part (b) of Theorem "five rows" and part (b) of Theorem "six rows" of Section 7 of
`problem001/jis/pemmasani.tex`: `f(5, m) = m + 6` for every `m ≥ 8` and `f(6, m) = m + 9` for
every `m ≥ 15`. The upper bounds are the row bound. The lower bounds come from Theorem
"finite collar" with the padding row `1` on the right, applied to `S₈` (test board `kT13`) and
to `S₁₆` (test board `kT23`), whose validity is kernel-checked in `Boards.lean`; the width
`15` is `kfvalue_6_15`.

## Contents

* `fval h m`: `f(h, m)`, the maximum size of a valid blackout of the `h × m` grid;
  `fval_eq`: a valid blackout of size `k` together with the bound `k` gives `f(h, m) = k`.
* `collar_extend`: a blackout `S₀` of the `h × m₀` grid whose right test board is valid,
  followed by `m - m₀` columns black only in row `1`, is a valid blackout of the `h × m` grid.
* `kT13_eq_pad`, `kS16`, `kT23_eq_pad`: the two test boards are the padded boards of `S₈` and
  `S₁₆`.
* `five_rows`, `fval_five`: `f(5, m) = m + 6` for `m ≥ 8`.
* `six_rows`, `fval_six`: `f(6, m) = m + 9` for `m ≥ 15`.
-/

namespace Kagey001

open Finset

/-- `f(h, m)`: the maximum size of a valid blackout of the `h × m` grid. -/
noncomputable def fval (h m : ℕ) : ℕ := sSup {k | ∃ S ⊆ grid h m, Valid h m S ∧ S.card = k}

theorem fval_eq {h m k : ℕ} (hex : ∃ S ⊆ grid h m, Valid h m S ∧ S.card = k)
    (hle : ∀ S ⊆ grid h m, Valid h m S → S.card ≤ k) : fval h m = k := by
  apply IsGreatest.csSup_eq
  refine ⟨hex, ?_⟩
  rintro _ ⟨S, hS, hv, rfl⟩
  exact hle S hS hv

lemma spanW_five : spanW 5 = 5 := by decide

lemma spanW_six : spanW 6 = 7 := by decide

/-- A blackout of the `h × m₀` grid whose right test board (padding row `1`) is valid, followed
by `m - m₀` columns black only in row `1`, is a valid blackout of the `h × m` grid with
`m - m₀` more points. -/
theorem collar_extend {h m₀ m : ℕ} (hh : 3 ≤ h) (hm₀ : 1 ≤ m₀) (hm : m₀ ≤ m) {S₀ : Finset Pt}
    (hS₀ : S₀ ⊆ grid h m₀)
    (hv : Valid h (m₀ + spanW h)
      (S₀ ∪ (Finset.Icc ((m₀ : ℤ) + 1) (m₀ + spanW h) ×ˢ {1}))) :
    S₀ ∪ (Finset.Icc ((m₀ : ℤ) + 1) m ×ˢ {1}) ⊆ grid h m ∧
      Valid h m (S₀ ∪ (Finset.Icc ((m₀ : ℤ) + 1) m ×ˢ {1})) ∧
      (S₀ ∪ (Finset.Icc ((m₀ : ℤ) + 1) m ×ˢ {1})).card = S₀.card + (m - m₀) := by
  obtain ⟨R, rfl⟩ : ∃ R, m = m₀ + R := ⟨m - m₀, by omega⟩
  have hdisj : Disjoint S₀ (Finset.Icc ((m₀ : ℤ) + 1) ((m₀ + R : ℕ) : ℤ) ×ˢ {1}) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    have := mem_grid.mp (hS₀ hp)
    simp only [mem_product, mem_Icc, mem_singleton] at hq
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact grid_mono le_rfl (by omega) (hS₀ hp)
    · simp only [mem_product, mem_Icc, mem_singleton] at hp
      rw [mem_grid]
      push_cast at hp ⊢
      omega
  · rw [Nat.cast_add]
    exact finite_collar_right hh hm₀ (Or.inl rfl) hS₀ hv R
  · rw [card_union_of_disjoint hdisj, card_product, card_singleton, Int.card_Icc]
    push_cast
    omega

/-! ### Five rows -/

theorem kT13_eq_pad : kT13 = kS8 ∪ (Finset.Icc (9 : ℤ) 13 ×ˢ {1}) := by decide +kernel

theorem kT13_valid_pad :
    Valid 5 (8 + spanW 5) (kS8 ∪ (Finset.Icc (((8 : ℕ) : ℤ) + 1) ((8 : ℕ) + spanW 5) ×ˢ {1})) := by
  rw [spanW_five]
  have e1 : (((8 : ℕ) : ℤ) + 1) = 9 := by norm_num
  have e2 : (((8 : ℕ) : ℤ) + ((5 : ℕ) : ℤ)) = 13 := by norm_num
  rw [e1, e2, ← kT13_eq_pad]
  exact kT13_valid

/-- **Theorem "five rows" (b).** For every `m ≥ 8`, the maximum size of a valid blackout of the
`5 × m` grid is `m + 6`, attained by `S₈` followed by `m - 8` columns black in row `1` only. -/
theorem five_rows {m : ℕ} (hm : 8 ≤ m) :
    (∃ S ⊆ grid 5 m, Valid 5 m S ∧ S.card = m + 6) ∧
      ∀ S ⊆ grid 5 m, Valid 5 m S → S.card ≤ m + 6 := by
  refine ⟨?_, fun S hS hv => by simpa using row_bound (by omega) hS hv⟩
  obtain ⟨hsub, hv, hc⟩ := collar_extend (by norm_num) (by norm_num) hm kS8_card.2 kT13_valid_pad
  refine ⟨_, hsub, hv, ?_⟩
  rw [hc, kS8_card.1]
  omega

/-- **`f(5, m) = m + 6` for every `m ≥ 8`.** -/
theorem fval_five {m : ℕ} (hm : 8 ≤ m) : fval 5 m = m + 6 :=
  fval_eq (five_rows hm).1 (five_rows hm).2

/-! ### Six rows -/

/-- `S₁₆`, the blackout of the `6 × 16` grid of Section 7: the points of `kT23` in the columns
`1, …, 16`. -/
def kS16 : Finset Pt :=
  {(1, 3), (1, 6), (2, 1), (2, 4), (3, 2), (3, 5), (4, 6), (5, 6), (6, 1), (6, 6), (7, 6),
    (8, 6), (9, 5), (9, 6), (10, 4), (10, 5), (11, 4), (12, 4), (13, 4), (14, 3), (14, 4),
    (15, 2), (15, 3), (16, 1), (16, 2)}

theorem kS16_card : kS16.card = 25 ∧ kS16 ⊆ grid 6 16 := by
  rw [grid_eq_gridC]; decide +kernel

theorem kT23_eq_pad : kT23 = kS16 ∪ (Finset.Icc (17 : ℤ) 23 ×ˢ {1}) := by decide +kernel

theorem kT23_valid_pad :
    Valid 6 (16 + spanW 6)
      (kS16 ∪ (Finset.Icc (((16 : ℕ) : ℤ) + 1) ((16 : ℕ) + spanW 6) ×ˢ {1})) := by
  rw [spanW_six]
  have e1 : (((16 : ℕ) : ℤ) + 1) = 17 := by norm_num
  have e2 : (((16 : ℕ) : ℤ) + ((7 : ℕ) : ℤ)) = 23 := by norm_num
  rw [e1, e2, ← kT23_eq_pad]
  exact kT23_valid

/-- **Theorem "six rows" (b).** For every `m ≥ 15`, the maximum size of a valid blackout of the
`6 × m` grid is `m + 9`: for `m = 15` by `kfvalue_6_15`, and for `m ≥ 16` by `S₁₆` followed by
`m - 16` columns black in row `1` only. -/
theorem six_rows {m : ℕ} (hm : 15 ≤ m) :
    (∃ S ⊆ grid 6 m, Valid 6 m S ∧ S.card = m + 9) ∧
      ∀ S ⊆ grid 6 m, Valid 6 m S → S.card ≤ m + 9 := by
  refine ⟨?_, fun S hS hv => by simpa using row_bound (by omega) hS hv⟩
  rcases Nat.eq_or_lt_of_le hm with rfl | hm'
  · exact kfvalue_6_15.1
  obtain ⟨hsub, hv, hc⟩ :=
    collar_extend (by norm_num) (by norm_num) (show 16 ≤ m by omega) kS16_card.2 kT23_valid_pad
  refine ⟨_, hsub, hv, ?_⟩
  rw [hc, kS16_card.1]
  omega

/-- **`f(6, m) = m + 9` for every `m ≥ 15`.** -/
theorem fval_six {m : ℕ} (hm : 15 ≤ m) : fval 6 m = m + 9 :=
  fval_eq (six_rows hm).1 (six_rows hm).2

end Kagey001
