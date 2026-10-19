import KageyProblems.Problem001.Padding

/-!
# Kagey's Problem 001 — axis-aligned collisions and short cycles

The first half of Lemma "axis-aligned rectangles and short cycles" of
`problem001/jis/pemmasani.tex` (two distinct axis-aligned rectangles with the same
presentation give a black four-cycle or a black six-cycle of the row-column graph), and Step 1
of the proof of Theorem "finite collar": axis-aligned rectangles of a padded board never
collide when the test board is valid.

## Contents

* `BlackFourCycle S`, `BlackSixCycle S`: two columns sharing two black rows, and three columns
  and three rows forming a black six-cycle.
* `axis_collision_cycle`: two distinct axis-aligned corner sets with the same presentation
  under `S` give a black four-cycle or six-cycle of `S`.
* `ValidW.no_four_cycle`, `ValidW.no_six_cycle`: a valid window with at least three columns
  has neither.
* `pad_axis_tie`: if the padded board `S_{L',R'}` is valid on at least three columns, then
  two axis-aligned rectangles with the same presentation under any `S_{L,R}` are equal.
-/

namespace Kagey001

open Finset

/-- Two columns of `S` sharing two black rows: a black four-cycle of the row-column graph. -/
def BlackFourCycle (S : Finset Pt) : Prop :=
  ∃ i i' j j' : ℤ, i ≠ i' ∧ j ≠ j' ∧ (i, j) ∈ S ∧ (i, j') ∈ S ∧ (i', j) ∈ S ∧ (i', j') ∈ S

/-- Rows `a, b` black in column `x`, rows `b, c` in column `y`, rows `c, a` in column `z`: a
black six-cycle of the row-column graph. -/
def BlackSixCycle (S : Finset Pt) : Prop :=
  ∃ a b c x y z : ℤ, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
    (x, a) ∈ S ∧ (x, b) ∈ S ∧ (y, b) ∈ S ∧ (y, c) ∈ S ∧ (z, c) ∈ S ∧ (z, a) ∈ S

lemma axisRect_eq_of {a b c d x y u v : ℤ} (h1 : (x = a ∧ y = b) ∨ (x = b ∧ y = a))
    (h2 : (u = c ∧ v = d) ∨ (u = d ∧ v = c)) : axisRect a b c d = axisRect x y u v := by
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    ext t <;> simp only [axisRect, mem_insert, mem_singleton] <;> tauto

/-- Two pairs of distinct integers, ordered so that they are equal, share their first entry
only, or are disjoint. -/
lemma pair_normal (a b a' b' : ℤ) :
    ∃ x y x' y' : ℤ, ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) ∧
      ((x' = a' ∧ y' = b') ∨ (x' = b' ∧ y' = a')) ∧
      ((x = x' ∧ y = y') ∨ (x = x' ∧ y ≠ y') ∨ (x ≠ x' ∧ x ≠ y' ∧ y ≠ x' ∧ y ≠ y')) := by
  by_cases h1 : a = a'
  · exact ⟨a, b, a', b', Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, by omega⟩
  by_cases h2 : a = b'
  · exact ⟨a, b, b', a', Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, by omega⟩
  by_cases h3 : b = a'
  · exact ⟨b, a, a', b', Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, by omega⟩
  by_cases h4 : b = b'
  · exact ⟨b, a, b', a', Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, by omega⟩
  exact ⟨a, b, a', b', Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, by omega⟩

/-- The normalized case analysis of `axis_collision_cycle`. -/
lemma axis_core {S : Finset Pt} {x y x' y' c d c' d' : ℤ} (hxy : x ≠ y) (hxy' : x' ≠ y')
    (hcd : c ≠ d) (hcd' : c' ≠ d')
    (hcol : (x = x' ∧ y = y') ∨ (x = x' ∧ y ≠ y') ∨ (x ≠ x' ∧ x ≠ y' ∧ y ≠ x' ∧ y ≠ y'))
    (hrow : (c = c' ∧ d = d') ∨ (c = c' ∧ d ≠ d') ∨ (c ≠ c' ∧ c ≠ d' ∧ d ≠ c' ∧ d ≠ d'))
    (hne : axisRect x y c d ≠ axisRect x' y' c' d')
    (hsd : symmDiff (axisRect x y c d) (axisRect x' y' c' d') ⊆ S) :
    BlackFourCycle S ∨ BlackSixCycle S := by
  have blk : ∀ p : Pt, (p ∈ axisRect x y c d ∧ p ∉ axisRect x' y' c' d') ∨
      (p ∈ axisRect x' y' c' d' ∧ p ∉ axisRect x y c d) → p ∈ S :=
    fun p hp => hsd (mem_symmDiff.mpr hp)
  rcases hcol with ⟨rfl, rfl⟩ | ⟨rfl, hy⟩ | hdc
  · rcases hrow with ⟨rfl, rfl⟩ | ⟨rfl, hd⟩ | hdr
    · exact absurd rfl hne
    · left
      refine ⟨x, y, d, d', hxy, hd, ?_, ?_, ?_, ?_⟩ <;> apply blk <;>
        simp only [axisRect, mem_insert, mem_singleton, Prod.mk.injEq, true_and, and_true,
          true_or, or_true] <;> omega
    · left
      refine ⟨x, y, c, d, hxy, hcd, ?_, ?_, ?_, ?_⟩ <;> apply blk <;>
        simp only [axisRect, mem_insert, mem_singleton, Prod.mk.injEq, true_and, and_true,
          true_or, or_true] <;> omega
  · rcases hrow with ⟨rfl, rfl⟩ | ⟨rfl, hd⟩ | hdr
    · left
      refine ⟨y, y', c, d, hy, hcd, ?_, ?_, ?_, ?_⟩ <;> apply blk <;>
        simp only [axisRect, mem_insert, mem_singleton, Prod.mk.injEq, true_and, and_true,
          true_or, or_true] <;> omega
    · right
      refine ⟨c, d, d', y, x, y', hcd, hd, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_,
        ?_, ?_⟩ <;> apply blk <;>
        simp only [axisRect, mem_insert, mem_singleton, Prod.mk.injEq, true_and, and_true,
          true_or, or_true] <;> omega
    · left
      refine ⟨x, y, c, d, hxy, hcd, ?_, ?_, ?_, ?_⟩ <;> apply blk <;>
        simp only [axisRect, mem_insert, mem_singleton, Prod.mk.injEq, true_and, and_true,
          true_or, or_true] <;> omega
  · left
    refine ⟨x, y, c, d, hxy, hcd, ?_, ?_, ?_, ?_⟩ <;> apply blk <;>
      simp only [axisRect, mem_insert, mem_singleton, Prod.mk.injEq, true_and, and_true,
          true_or, or_true] <;> omega

/-- **Axis-aligned collisions give short cycles.** Two distinct axis-aligned corner sets with
the same presentation under `S` give a black four-cycle or a black six-cycle of `S`. -/
theorem axis_collision_cycle {S C₁ C₂ : Finset Pt} (ha₁ : IsAxis C₁) (ha₂ : IsAxis C₂)
    (hne : C₁ ≠ C₂) (hp : pres S C₁ = pres S C₂) : BlackFourCycle S ∨ BlackSixCycle S := by
  have hsd := (sdiff_eq_sdiff_iff_symmDiff_subset C₁ C₂ S).mp hp
  obtain ⟨a, b, c, d, hab, hcd, rfl⟩ := ha₁
  obtain ⟨a', b', c', d', hab', hcd', rfl⟩ := ha₂
  obtain ⟨x, y, x', y', hx, hx', hcol⟩ := pair_normal a b a' b'
  obtain ⟨u, v, u', v', hu, hu', hrow⟩ := pair_normal c d c' d'
  rw [axisRect_eq_of hx hu, axisRect_eq_of hx' hu'] at hne hsd
  have e1 : x ≠ y := by rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hab, hab.symm]
  have e2 : x' ≠ y' := by rcases hx' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hab', hab'.symm]
  have e3 : u ≠ v := by rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hcd, hcd.symm]
  have e4 : u' ≠ v' := by rcases hu' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hcd', hcd'.symm]
  exact axis_core e1 e2 e3 e4 hcol hrow hne hsd

/-! ### Short cycles in a valid window -/

lemma axisRect_memW {h : ℕ} {lo hi a b c d : ℤ} (hab : a ≠ b) (hcd : c ≠ d)
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi) (hc : 1 ≤ c ∧ c ≤ h) (hd : 1 ≤ d ∧ d ≤ h) :
    axisRect a b c d ∈ RectsW h lo hi := by
  refine ⟨IsAxis.isRect ⟨a, b, c, d, hab, hcd, rfl⟩, ?_⟩
  intro y hy
  simp only [axisRect, mem_insert, mem_singleton] at hy
  rw [mem_gridW]
  rcases hy with rfl | rfl | rfl | rfl <;> simp only <;> omega

/-- **No black four-cycle** in a valid window with at least three columns. -/
theorem ValidW.no_four_cycle {h : ℕ} {lo hi : ℤ} (h3 : lo + 2 ≤ hi) {S : Finset Pt}
    (hv : ValidW h lo hi S) {i i' j j' : ℤ} (hI : lo ≤ i ∧ i ≤ hi) (hI' : lo ≤ i' ∧ i' ≤ hi)
    (hj : 1 ≤ j ∧ j ≤ h) (hj' : 1 ≤ j' ∧ j' ≤ h) (hii : i ≠ i') (hjj : j ≠ j')
    (h1 : (i, j) ∈ S) (h2 : (i, j') ∈ S) (h3' : (i', j) ∈ S) (h4 : (i', j') ∈ S) : False := by
  obtain ⟨w, hw1, hw2, hwi, hwi'⟩ : ∃ w : ℤ, lo ≤ w ∧ w ≤ hi ∧ w ≠ i ∧ w ≠ i' := by
    by_cases k1 : lo ≠ i ∧ lo ≠ i'
    · exact ⟨lo, le_refl _, by omega, k1.1, k1.2⟩
    · by_cases k2 : lo + 1 ≠ i ∧ lo + 1 ≠ i'
      · exact ⟨lo + 1, by omega, by omega, k2.1, k2.2⟩
      · exact ⟨lo + 2, by omega, h3, by omega, by omega⟩
  have R1 := axisRect_memW (h := h) (Ne.symm hwi) hjj hI ⟨hw1, hw2⟩ hj hj'
  have R2 := axisRect_memW (h := h) (Ne.symm hwi') hjj hI' ⟨hw1, hw2⟩ hj hj'
  have hp : pres S (axisRect i w j j') = pres S (axisRect i' w j j') := by
    ext ⟨x, y⟩
    simp only [pres, axisRect, mem_sdiff, mem_insert, mem_singleton, Prod.mk.injEq]
    by_cases hx : (x, y) ∈ S
    · simp [hx]
    · have e1 : ¬(x = i ∧ y = j) := by rintro ⟨rfl, rfl⟩; exact hx h1
      have e2 : ¬(x = i ∧ y = j') := by rintro ⟨rfl, rfl⟩; exact hx h2
      have e3 : ¬(x = i' ∧ y = j) := by rintro ⟨rfl, rfl⟩; exact hx h3'
      have e4 : ¬(x = i' ∧ y = j') := by rintro ⟨rfl, rfl⟩; exact hx h4
      simp only [hx, not_false_eq_true, and_true]
      omega
  have heq := hv _ R1 _ R2 hp
  have hmem : ((i, j) : Pt) ∈ axisRect i' w j j' := by
    rw [← heq]; simp [axisRect]
  simp only [axisRect, mem_insert, mem_singleton, Prod.mk.injEq] at hmem
  omega

/-- **No black six-cycle** in a valid window. -/
theorem ValidW.no_six_cycle {h : ℕ} {lo hi : ℤ} {S : Finset Pt} (hv : ValidW h lo hi S)
    {a b c x y z : ℤ} (ha : 1 ≤ a ∧ a ≤ h) (hb : 1 ≤ b ∧ b ≤ h) (hc : 1 ≤ c ∧ c ≤ h)
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi) (hz : lo ≤ z ∧ z ≤ hi)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (h1 : (x, a) ∈ S) (h2 : (x, b) ∈ S) (h3 : (y, b) ∈ S) (h4 : (y, c) ∈ S)
    (h5 : (z, c) ∈ S) (h6 : (z, a) ∈ S) : False := by
  have R1 := axisRect_memW (h := h) hxy hab hx hy ha hb
  have R2 := axisRect_memW (h := h) hyz (Ne.symm hca) hy hz ha hc
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

/-- **Step 1 of the collar theorem.** If the padded board `S_{L',R'}` is valid and has at least
three columns, then two axis-aligned rectangles with the same presentation under `S_{L,R}` are
equal: a short black cycle of `S_{L,R}` uses only columns with two black points, which are
original columns, so it is a short black cycle of `S_{L',R'}`. -/
theorem pad_axis_tie {h m L R Ls Rs : ℕ} {ρ : ℤ} {S : Finset Pt} (h3 : 3 ≤ Ls + m + Rs)
    (hv : ValidW h (1 - Ls) (m + Rs) (pad h m Ls Rs ρ S)) {C₁ C₂ : Finset Pt}
    (ha₁ : IsAxis C₁) (ha₂ : IsAxis C₂)
    (hp : pres (pad h m L R ρ S) C₁ = pres (pad h m L R ρ S) C₂) : C₁ = C₂ := by
  by_contra hne
  have up : ∀ {p : Pt}, p ∈ S ∩ grid h m → p ∈ pad h m Ls Rs ρ S :=
    fun hp => inter_grid_subset_pad h m Ls Rs ρ S hp
  have gr : ∀ {p : Pt}, p ∈ S ∩ grid h m → 1 ≤ p.1 ∧ p.1 ≤ m ∧ 1 ≤ p.2 ∧ p.2 ≤ h :=
    fun hp => mem_grid.mp (mem_inter.mp hp).2
  rcases axis_collision_cycle ha₁ ha₂ hne hp with
    ⟨i, i', j, j', hii, hjj, h1, h2, h3', h4⟩ | ⟨a, b, c, x, y, z, hab, hbc, hca, hxy, hyz, hzx,
      h1, h2, h3', h4, h5, h6⟩
  · obtain ⟨k1, k2⟩ := pad_col_two_black hjj h1 h2
    obtain ⟨k3, k4⟩ := pad_col_two_black hjj h3' h4
    have g1 := gr k1; have g2 := gr k2; have g3 := gr k3
    simp only at g1 g2 g3
    exact hv.no_four_cycle (by omega) (by omega) (by omega) (by omega) (by omega) hii hjj
      (up k1) (up k2) (up k3) (up k4)
  · obtain ⟨k1, k2⟩ := pad_col_two_black hab h1 h2
    obtain ⟨k3, k4⟩ := pad_col_two_black hbc h3' h4
    obtain ⟨k5, k6⟩ := pad_col_two_black hca h5 h6
    have g1 := gr k1; have g2 := gr k2; have g3 := gr k3; have g4 := gr k4; have g5 := gr k5
    simp only at g1 g2 g3 g4 g5
    exact hv.no_six_cycle (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hab hbc hca hxy hyz hzx (up k1) (up k2) (up k3) (up k4) (up k5) (up k6)

end Kagey001
