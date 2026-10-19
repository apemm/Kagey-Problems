import KageyProblems.Problem001.ThreeCorners
import KageyProblems.Problem001.RowBound

/-!
# Kagey's Problem 001 — tilted rectangles: rows and span

The facts about tilted rectangles that the finite collar theorem of Section 7 of
`problem001/jis/pemmasani.tex` uses: every rectangle is axis-aligned or tilted, a tilted
rectangle has at most one corner in its top row and at most one in its bottom row (the row
part of Lemma "leftmost corner"), and the columns of a tilted rectangle of an `h`-row grid
span at most `W_h = 1 + ⌊(h-1)²/4⌋` (Lemma "span bound").

## Contents

* `spanW h`: the span bound `W_h = 1 + ⌊(h-1)²/4⌋`; `two_le_spanW`: `W_h ≥ 2` for `h ≥ 3`.
* `IsAxis`, `IsTilt`: axis-aligned and tilted corner sets. A tilted corner set is
  `{p, p+u, p+v, p+u+v}` with `u ⊥ v` and all four coordinates of `u` and `v` nonzero.
* `IsRect.axis_or_tilt`: every rectangle is axis-aligned or tilted.
* `IsTilt.eq_of_row_eq_bound`: in a tilted rectangle whose rows lie in `1..h`, at most one
  corner lies in row `1` and at most one in row `h`; `IsTilt.card_filter_row_le_one` is the
  same as a cardinality bound.
* `IsTilt.col_sub_le`: two corners of such a rectangle are at most `W_h` columns apart.
-/

namespace Kagey001

open Finset

/-- The span bound `W_h = 1 + ⌊(h-1)²/4⌋` of Lemma "span bound". -/
def spanW (h : ℕ) : ℕ := 1 + (h - 1) ^ 2 / 4

lemma two_le_spanW {h : ℕ} (hh : 3 ≤ h) : 2 ≤ spanW h := by
  unfold spanW
  have : 4 ≤ (h - 1) ^ 2 := by
    have h2 : 2 ≤ h - 1 := by omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (h - 1) ^ 2 := Nat.pow_le_pow_left h2 2
  omega

lemma spanW_cast {h : ℕ} (hh : 1 ≤ h) : (spanW h : ℤ) = 1 + ((h : ℤ) - 1) ^ 2 / 4 := by
  unfold spanW
  push_cast [Nat.cast_sub hh]
  rfl

/-- `C` is the corner set of an axis-aligned rectangle. -/
def IsAxis (C : Finset Pt) : Prop := ∃ a b c d : ℤ, a ≠ b ∧ c ≠ d ∧ C = axisRect a b c d

/-- `C` is the corner set of a tilted rectangle: `{p, p+u, p+v, p+u+v}` with `u ⊥ v` and no
coordinate of `u` or `v` equal to zero. -/
def IsTilt (C : Finset Pt) : Prop :=
  ∃ p u v : Pt, u.1 ≠ 0 ∧ u.2 ≠ 0 ∧ v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ u.1 * v.1 + u.2 * v.2 = 0 ∧
    C = {p, p + u, p + v, p + u + v}

theorem IsAxis.isRect {C : Finset Pt} (hC : IsAxis C) : IsRect C := by
  obtain ⟨a, b, c, d, hab, hcd, rfl⟩ := hC
  refine ⟨(a, c), (b - a, 0), (0, d - c), ?_, ?_, by ring, ?_⟩
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

theorem IsTilt.isRect {C : Finset Pt} (hC : IsTilt C) : IsRect C := by
  obtain ⟨p, u, v, hu1, -, hv1, -, huv, rfl⟩ := hC
  refine ⟨p, u, v, ?_, ?_, huv, rfl⟩
  · intro h0
    exact hu1 (by rw [h0]; rfl)
  · intro h0
    exact hv1 (by rw [h0]; rfl)

/-- Every rectangle is axis-aligned or tilted. -/
theorem IsRect.axis_or_tilt {C : Finset Pt} (hC : IsRect C) : IsAxis C ∨ IsTilt C := by
  obtain ⟨⟨p1, p2⟩, ⟨u1, u2⟩, ⟨v1, v2⟩, hu, hv, huv, rfl⟩ := hC
  simp only [ne_eq, Prod.mk_eq_zero, not_and_or] at hu hv
  simp only at huv
  by_cases hu1 : u1 = 0
  · subst hu1
    have hu2 : u2 ≠ 0 := by tauto
    have hv2 : v2 = 0 := by
      have : u2 * v2 = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hu2
    subst hv2
    have hv1 : v1 ≠ 0 := by tauto
    left
    refine ⟨p1, p1 + v1, p2, p2 + u2, by omega, by omega, ?_⟩
    ext ⟨x, y⟩
    simp only [axisRect, mem_insert, mem_singleton, Prod.mk_add_mk, Prod.mk.injEq]
    omega
  by_cases hu2 : u2 = 0
  · subst hu2
    have hv1 : v1 = 0 := by
      have : u1 * v1 = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hu1
    subst hv1
    have hv2 : v2 ≠ 0 := by tauto
    left
    refine ⟨p1, p1 + u1, p2, p2 + v2, by omega, by omega, ?_⟩
    ext ⟨x, y⟩
    simp only [axisRect, mem_insert, mem_singleton, Prod.mk_add_mk, Prod.mk.injEq]
    omega
  have hv1 : v1 ≠ 0 := by
    intro hv1
    subst hv1
    have : u2 * v2 = 0 := by linarith
    have hv2 : v2 = 0 := (mul_eq_zero.mp this).resolve_left hu2
    tauto
  have hv2 : v2 ≠ 0 := by
    intro hv2
    subst hv2
    have : u1 * v1 = 0 := by linarith
    exact hv1 ((mul_eq_zero.mp this).resolve_left hu1)
  exact Or.inr ⟨(p1, p2), (u1, u2), (v1, v2), hu1, hu2, hv1, hv2, huv, rfl⟩

/-- A corner of a tilted rectangle in its lowest row is the only corner in that row. -/
theorem IsTilt.eq_of_row_min {C : Finset Pt} (hC : IsTilt C) {p q : Pt} (hp : p ∈ C)
    (hq : q ∈ C) (hmin : ∀ c ∈ C, p.2 ≤ c.2) (hpq : q.2 = p.2) : p = q := by
  obtain ⟨⟨p1, p2⟩, ⟨u1, u2⟩, ⟨v1, v2⟩, -, hu2, -, hv2, -, rfl⟩ := hC
  have m1 := hmin (p1, p2) (by simp)
  have m2 := hmin ((p1, p2) + (u1, u2)) (by simp)
  have m3 := hmin ((p1, p2) + (v1, v2)) (by simp)
  have m4 := hmin ((p1, p2) + (u1, u2) + (v1, v2)) (by simp)
  simp only [mem_insert, mem_singleton] at hp hq
  simp only [Prod.mk_add_mk] at m1 m2 m3 m4 hp hq
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    simp only [Prod.mk.injEq] at m1 m2 m3 m4 hpq ⊢ <;> omega

/-- A corner of a tilted rectangle in its highest row is the only corner in that row. -/
theorem IsTilt.eq_of_row_max {C : Finset Pt} (hC : IsTilt C) {p q : Pt} (hp : p ∈ C)
    (hq : q ∈ C) (hmax : ∀ c ∈ C, c.2 ≤ p.2) (hpq : q.2 = p.2) : p = q := by
  obtain ⟨⟨p1, p2⟩, ⟨u1, u2⟩, ⟨v1, v2⟩, -, hu2, -, hv2, -, rfl⟩ := hC
  have m1 := hmax (p1, p2) (by simp)
  have m2 := hmax ((p1, p2) + (u1, u2)) (by simp)
  have m3 := hmax ((p1, p2) + (v1, v2)) (by simp)
  have m4 := hmax ((p1, p2) + (u1, u2) + (v1, v2)) (by simp)
  simp only [mem_insert, mem_singleton] at hp hq
  simp only [Prod.mk_add_mk] at m1 m2 m3 m4 hp hq
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    simp only [Prod.mk.injEq] at m1 m2 m3 m4 hpq ⊢ <;> omega

/-- **One corner in each boundary row.** A tilted rectangle with rows in `1..h` has at most one
corner in row `1` and at most one in row `h`. -/
theorem IsTilt.eq_of_row_eq_bound {h : ℕ} {C : Finset Pt} (hC : IsTilt C)
    (hrows : ∀ c ∈ C, 1 ≤ c.2 ∧ c.2 ≤ h) {ρ : ℤ} (hρ : ρ = 1 ∨ ρ = h) {p q : Pt}
    (hp : p ∈ C) (hq : q ∈ C) (hp2 : p.2 = ρ) (hq2 : q.2 = ρ) : p = q := by
  rcases hρ with rfl | rfl
  · exact hC.eq_of_row_min hp hq (fun c hc => hp2 ▸ (hrows c hc).1) (hq2.trans hp2.symm)
  · exact hC.eq_of_row_max hp hq (fun c hc => hp2 ▸ (hrows c hc).2) (hq2.trans hp2.symm)

theorem IsTilt.card_filter_row_le_one {h : ℕ} {C : Finset Pt} (hC : IsTilt C)
    (hrows : ∀ c ∈ C, 1 ≤ c.2 ∧ c.2 ≤ h) {ρ : ℤ} (hρ : ρ = 1 ∨ ρ = h) :
    (C.filter (fun p => p.2 = ρ)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  rw [mem_filter] at hp hq
  exact hC.eq_of_row_eq_bound hrows hρ hp.1 hq.1 hp.2 hq.2

/-- **Span bound.** Two corners of a tilted rectangle with rows in `1..h` lie at most `W_h`
columns apart. -/
theorem IsTilt.col_sub_le {h : ℕ} {C : Finset Pt} (hC : IsTilt C)
    (hrows : ∀ c ∈ C, 1 ≤ c.2 ∧ c.2 ≤ h) {p q : Pt} (hp : p ∈ C) (hq : q ∈ C) :
    p.1 - q.1 ≤ (spanW h : ℤ) := by
  obtain ⟨⟨p1, p2⟩, ⟨u1, u2⟩, ⟨v1, v2⟩, hu1, hu2, hv1, hv2, huv, rfl⟩ := hC
  have r1 := hrows (p1, p2) (by simp)
  have r2 := hrows ((p1, p2) + (u1, u2)) (by simp)
  have r3 := hrows ((p1, p2) + (v1, v2)) (by simp)
  have r4 := hrows ((p1, p2) + (u1, u2) + (v1, v2)) (by simp)
  simp only [Prod.mk_add_mk] at r1 r2 r3 r4
  simp only at huv
  have hh : 1 ≤ h := by omega
  -- The row span is `|u₂| + |v₂| ≤ h - 1`.
  have hbd : |u2| + |v2| ≤ (h : ℤ) - 1 := by
    rcases abs_cases u2 with ⟨e1, _⟩ | ⟨e1, _⟩ <;> rcases abs_cases v2 with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      omega
  -- The column distance of two corners is at most `|u₁| + |v₁|`.
  have hcol : p.1 - q.1 ≤ |u1| + |v1| := by
    simp only [mem_insert, mem_singleton, Prod.mk_add_mk] at hp hq
    rcases abs_cases u1 with ⟨e1, _⟩ | ⟨e1, _⟩ <;> rcases abs_cases v1 with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      simp only <;> omega
  have hprod : |u1| * |v1| = |u2| * |v2| := by
    rw [← abs_mul, ← abs_mul, show u1 * v1 = -(u2 * v2) by linarith, abs_neg]
  have ha : 1 ≤ |u1| := Int.one_le_abs hu1
  have hc : 1 ≤ |v1| := Int.one_le_abs hv1
  have hb : 1 ≤ |u2| := Int.one_le_abs hu2
  have hd : 1 ≤ |v2| := Int.one_le_abs hv2
  have hac : |u1| + |v1| ≤ |u1| * |v1| + 1 := by nlinarith
  have h4 : 4 * (|u2| * |v2|) ≤ ((h : ℤ) - 1) ^ 2 := by
    nlinarith [sq_nonneg (|u2| - |v2|)]
  have hk : |u2| * |v2| ≤ ((h : ℤ) - 1) ^ 2 / 4 :=
    (Int.le_ediv_iff_mul_le (by norm_num)).mpr (by linarith)
  rw [spanW_cast hh]
  linarith

end Kagey001
