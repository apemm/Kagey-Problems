import KageyProblems.Problem001.AxisCycles

/-!
# Kagey's Problem 001 — the finite collar theorem

Theorem "finite collar" of Section 7 of `problem001/jis/pemmasani.tex`. Let `h ≥ 3`, `m ≥ 1`,
let `S` be a blackout of the `h × m` grid, fix the padding row (row `1` or row `h`) and choose
the left side, the right side, or both. Then the padded boards `S_{L,R}` are valid for every
admissible `(L, R)` (`L = 0` when the left side is not chosen, `R = 0` when the right side is
not chosen) if and only if the single test board `S_{L*,R*}` is valid, where `L* = W_h` if the
left side is chosen and `L* = 0` otherwise, and likewise for `R*`.

## Contents

* `starLen h side`: `W_h` if the side is chosen, `0` otherwise.
* `finite_collar`: the theorem, with validity of a padded board on its own window of columns
  `1-L, …, m+R`.
* `finite_collar_valid`: the same with the paper's one-based `Valid`, the padded board
  translated to the columns `1, …, L+m+R`.
* `finite_collar_right`: the right-padding case for a blackout `S ⊆ grid h m`, in the form the
  test boards of the five- and six-row theorems use.

The proof is the paper's. Both directions of the equivalence are proved for all admissible
`(L, R)`, without assuming `L ≤ L*` or `R ≤ R*`: a weak tilted rectangle of `S_{L,R}` lies in
the columns common to `S_{L,R}` and `S_{L*,R*}` (`weak_tilt_local`), two axis-aligned
rectangles never collide (`pad_axis_tie`), and an axis-aligned rectangle that ties with a
tilted one lies in the common columns too (`axis_tie_local`).
-/

namespace Kagey001

open Finset

/-- The padding length of the test board on one side: `W_h` if the side is chosen. -/
def starLen (h : ℕ) (side : Bool) : ℕ := if side then spanW h else 0

lemma starLen_false (h : ℕ) : starLen h false = 0 := rfl

lemma starLen_true (h : ℕ) : starLen h true = spanW h := rfl

lemma eq_zero_or_le_starLen {h L : ℕ} {side : Bool} (hadm : side = false → L = 0) :
    L = 0 ∨ spanW h ≤ starLen h side := by
  cases side
  · exact Or.inl (hadm rfl)
  · exact Or.inr (le_refl _)

/-- **Theorem "finite collar"** (window form). For `h ≥ 3`, `m ≥ 1`, a padding row `ρ` equal to
`1` or `h`, and a choice of sides (at least one), every admissible padded board `S_{L,R}` is
valid if and only if the test board `S_{L*,R*}` is valid. -/
theorem finite_collar {h m : ℕ} (hh : 3 ≤ h) (hm : 1 ≤ m) {ρ : ℤ} (hρ : ρ = 1 ∨ ρ = h)
    (S : Finset Pt) (left right : Bool) (hside : left = true ∨ right = true) :
    (∀ L R : ℕ, (left = false → L = 0) → (right = false → R = 0) →
        ValidW h (1 - L) (m + R) (pad h m L R ρ S)) ↔
      ValidW h (1 - (starLen h left : ℤ)) (m + (starLen h right : ℤ))
        (pad h m (starLen h left) (starLen h right) ρ S) := by
  constructor
  · intro H
    exact H _ _ (fun hl => by rw [hl]; rfl) (fun hr => by rw [hr]; rfl)
  intro hv L R hLa hRa C₁ h₁ C₂ h₂ hp
  set Ls := starLen h left with hLs
  set Rs := starLen h right with hRs
  have hL := eq_zero_or_le_starLen (h := h) hLa
  have hR := eq_zero_or_le_starLen (h := h) hRa
  have hW := two_le_spanW hh
  have h3 : 3 ≤ Ls + m + Rs := by
    rcases hside with hs | hs
    · have : Ls = spanW h := by rw [hLs, hs]; rfl
      omega
    · have : Rs = spanW h := by rw [hRs, hs]; rfl
      omega
  -- Rectangles in the common columns are rectangles of the test board with the same
  -- presentation.
  have fin : C₁ ⊆ gridW h (1 - (min L Ls : ℕ)) (m + (min R Rs : ℕ)) →
      C₂ ⊆ gridW h (1 - (min L Ls : ℕ)) (m + (min R Rs : ℕ)) → C₁ = C₂ := by
    intro k₁ k₂
    have hsub : gridW h (1 - (min L Ls : ℕ)) (m + (min R Rs : ℕ)) ⊆
        gridW h (1 - (Ls : ℤ)) (m + (Rs : ℤ)) := by
      apply gridW_mono
      · have : ((min L Ls : ℕ) : ℤ) ≤ Ls := Nat.cast_le.mpr (min_le_right L Ls)
        omega
      · have : ((min R Rs : ℕ) : ℤ) ≤ Rs := Nat.cast_le.mpr (min_le_right R Rs)
        omega
    apply hv C₁ ⟨h₁.1, k₁.trans hsub⟩ C₂ ⟨h₂.1, k₂.trans hsub⟩
    rw [← pres_pad_agree k₁, ← pres_pad_agree k₂]
    exact hp
  have lo1 : 1 - (((min L Ls : ℕ)) : ℤ) ≤ 1 := by omega
  have hi1 : (m : ℤ) ≤ m + ((min R Rs : ℕ) : ℤ) := by omega
  -- A rectangle that ties with a distinct one is weak.
  have weak : ∀ {D₁ D₂ : Finset Pt}, D₁ ∈ RectsW h (1 - L) (m + R) →
      D₂ ∈ RectsW h (1 - L) (m + R) → D₁ ≠ D₂ →
      pres (pad h m L R ρ S) D₁ = pres (pad h m L R ρ S) D₂ →
      (pres (pad h m L R ρ S) D₁).card ≤ 2 := by
    intro D₁ D₂ d₁ d₂ hne hpd
    have : (D₁ ∩ D₂).card ≤ 2 := by
      by_contra hc
      exact hne (d₁.1.eq_of_three_le_card_inter d₂.1 (by omega))
    exact (card_le_card (pres_subset_inter hpd)).trans this
  rcases h₁.1.axis_or_tilt with a₁ | t₁ <;> rcases h₂.1.axis_or_tilt with a₂ | t₂
  · -- Step 1: both axis-aligned.
    exact pad_axis_tie h3 hv a₁ a₂ hp
  · -- Step 3: `C₂` tilted, `C₁` axis-aligned.
    by_contra hne
    have k₂ := weak_tilt_local hρ hL hR h₂ t₂ (weak h₂ h₁ (Ne.symm hne) hp.symm)
    exact hne (fin (axis_tie_local lo1 hi1 k₂ h₁ a₁ hp.symm) k₂)
  · -- Step 3: `C₁` tilted, `C₂` axis-aligned.
    by_contra hne
    have k₁ := weak_tilt_local hρ hL hR h₁ t₁ (weak h₁ h₂ hne hp)
    exact hne (fin k₁ (axis_tie_local lo1 hi1 k₁ h₂ a₂ hp))
  · -- Step 2: both tilted.
    by_contra hne
    exact hne (fin (weak_tilt_local hρ hL hR h₁ t₁ (weak h₁ h₂ hne hp))
      (weak_tilt_local hρ hL hR h₂ t₂ (weak h₂ h₁ (Ne.symm hne) hp.symm)))

/-- **Theorem "finite collar"** with the paper's one-based validity: the padded board
`S_{L,R}`, translated to the columns `1, …, L+m+R`, is a valid blackout of the
`h × (L+m+R)` grid for every admissible `(L, R)` if and only if `S_{L*,R*}` is. -/
theorem finite_collar_valid {h m : ℕ} (hh : 3 ≤ h) (hm : 1 ≤ m) {ρ : ℤ} (hρ : ρ = 1 ∨ ρ = h)
    (S : Finset Pt) (left right : Bool) (hside : left = true ∨ right = true) :
    (∀ L R : ℕ, (left = false → L = 0) → (right = false → R = 0) →
        Valid h (L + m + R) ((pad h m L R ρ S).map (shiftE L))) ↔
      Valid h (starLen h left + m + starLen h right)
        ((pad h m (starLen h left) (starLen h right) ρ S).map (shiftE (starLen h left))) := by
  simp only [← valid_pad_iff]
  exact finite_collar hh hm hρ S left right hside

lemma validW_right_iff {h m R : ℕ} {ρ : ℤ} {S : Finset Pt} (hS : S ⊆ grid h m) :
    ValidW h (1 - ((0 : ℕ) : ℤ)) (m + (R : ℤ)) (pad h m 0 R ρ S) ↔
      Valid h (m + R) (S ∪ (Finset.Icc ((m : ℤ) + 1) (m + R) ×ˢ {ρ})) := by
  rw [pad_zero_left h m R ρ hS, Nat.cast_zero, sub_zero, ← validW_one_iff]
  push_cast
  rfl

/-- **Theorem "finite collar", right padding.** For `h ≥ 3`, `m ≥ 1`, a blackout `S` of the
`h × m` grid and the padding row `1` or `h`: if `S` followed by `W_h` columns black only in the
padding row is valid, then `S` followed by any number `R` of such columns is valid. -/
theorem finite_collar_right {h m : ℕ} (hh : 3 ≤ h) (hm : 1 ≤ m) {ρ : ℤ}
    (hρ : ρ = 1 ∨ ρ = h) {S : Finset Pt} (hS : S ⊆ grid h m)
    (hv : Valid h (m + spanW h) (S ∪ (Finset.Icc ((m : ℤ) + 1) (m + spanW h) ×ˢ {ρ})))
    (R : ℕ) : Valid h (m + R) (S ∪ (Finset.Icc ((m : ℤ) + 1) (m + R) ×ˢ {ρ})) := by
  have key := (finite_collar hh hm hρ S false true (Or.inr rfl)).mpr
    (by rw [starLen_false, starLen_true]; exact (validW_right_iff hS).mpr hv)
    0 R (fun _ => rfl) (fun h => absurd h (by simp))
  exact (validW_right_iff hS).mp key

end Kagey001
