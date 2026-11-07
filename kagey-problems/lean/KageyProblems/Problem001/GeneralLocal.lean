import KageyProblems.Problem001.Tilt

/-!
# Kagey's Problem 001 — the general theorem: the analysis near one double

The local half of the proof of the general theorem of Section "Every height at large widths" (Theorem "large widths") of
`problem001/jis/pemmasani.tex`. Near one double column of an alternating-boundary-sea
blackout, a tilted rectangle with two black corners shows exactly two white points, in one of
three shapes; two such rectangles never show the same pair, and an axis-aligned rectangle
never shows it either. The graph of the doubles plays no part here.

This Lean verification code was generated with Claude Opus 5.5.

The local model `LBlack h p σ a b` is the blackout near a double in column `p`: row `σ`
(row `1` or row `h`) to the left, rows `a < b` in column `p`, and the other boundary row
`h + 1 - σ` to the right. Every statement is about this model, so the row reflection and the
half turn of the note are not needed: both sea orders are the two values of `σ`.

## Contents

* `LBlack`, `LocHyp`: the local model and its parameters; `TiltOK`, `tc`: a tilted rectangle
  `{(x, y), (x, y) + u, (x, y) + v, (x, y) + u + v}` with rows in `1..h`.
* `TypeD`: a pair straddling column `p` with both rows in `2..h-1`.
* `diag_typeD`: cases alpha, beta and gamma-diag. If two opposite corners are black, the other
  diagonal is of type `TypeD`, hence white.
* `side_black`: case gamma-side. If two adjacent corners are black, one is a sea point and
  the other lies in column `p`, and the other two corners lie on the sea's side, off its row.
* `DiagST`, `SideLST`, `SideRST`, `WeakST`: the three shapes of a weak tilted rectangle;
  `local_weak`: every tilted rectangle with two black corners has one of them (in particular
  it shows exactly two points, so three black corners are impossible).
* `black_pair_unique`, `weak_unique`: two weak tilted rectangles showing the same pair are
  equal.
* `axis_rival`: no axis-aligned rectangle shows the pair of a weak tilted rectangle.

The proofs follow the cases of the note with one change of method. The facts about the white
diagonal come from the right angle at its endpoints (`thales_between`, `thales_vertical`)
instead of the midpoint and the half-diagonal `w`, and two black diagonals with the same
midpoint and length are compared through the right angle that one endpoint of each makes
with the other pair (`thales_of_sum`, `thales_lin`), which reduces every comparison to signs.
-/

namespace Kagey001

open Finset

/-! ### The local model -/

/-- The squared length of a vector. -/
def sqd (w : Pt) : ℤ := w.1 ^ 2 + w.2 ^ 2

lemma sqd_sub_comm (s t : Pt) : sqd (s - t) = sqd (t - s) := by
  simp only [sqd, Prod.fst_sub, Prod.snd_sub]; ring

/-- The parameters of the local model: `h ≥ 3`, the sea row `σ` left of the double is a
boundary row, and the double is black in the rows `a < b`. -/
def LocHyp (h : ℕ) (σ a b : ℤ) : Prop :=
  3 ≤ h ∧ (σ = 1 ∨ σ = h) ∧ 1 ≤ a ∧ a < b ∧ b ≤ h

/-- The black points of the local model around a double in column `p`: row `σ` to the left,
rows `a` and `b` in column `p`, and row `h + 1 - σ` (the other boundary row) to the right. -/
def LBlack (h : ℕ) (p σ a b : ℤ) (y : Pt) : Prop :=
  (y.1 < p ∧ y.2 = σ) ∨ (y.1 = p ∧ (y.2 = a ∨ y.2 = b)) ∨ (p < y.1 ∧ y.2 = h + 1 - σ)

/-- A diagonal presentation: the two points straddle column `p` and avoid both boundary rows. -/
def TypeD (h : ℕ) (p : ℤ) (s t : Pt) : Prop :=
  ((s.1 < p ∧ p < t.1) ∨ (t.1 < p ∧ p < s.1)) ∧ 2 ≤ s.2 ∧ s.2 < h ∧ 2 ≤ t.2 ∧ t.2 < h

/-- The corners `(x, y)`, `(x, y) + u`, `(x, y) + v`, `(x, y) + u + v` form a tilted rectangle
with rows in `1..h`. -/
def TiltOK (h : ℕ) (y u1 u2 v1 v2 : ℤ) : Prop :=
  u1 ≠ 0 ∧ u2 ≠ 0 ∧ v1 ≠ 0 ∧ v2 ≠ 0 ∧ u1 * v1 + u2 * v2 = 0 ∧
    (1 ≤ y ∧ y ≤ h) ∧ (1 ≤ y + u2 ∧ y + u2 ≤ h) ∧ (1 ≤ y + v2 ∧ y + v2 ≤ h) ∧
    (1 ≤ y + u2 + v2 ∧ y + u2 + v2 ≤ h)

/-- The corner set of `TiltOK`. -/
def tc (x y u1 u2 v1 v2 : ℤ) : Finset Pt :=
  {(x, y), (x + u1, y + u2), (x + v1, y + v2), (x + u1 + v1, y + u2 + v2)}

/-! ### Signs of products -/

lemma thales_between {a1 a2 c1 c2 b1 b2 : ℤ}
    (th : (b1 - a1) * (b1 - c1) + (b2 - a2) * (b2 - c2) = 0)
    (hr : (a2 < b2 ∧ b2 < c2) ∨ (c2 < b2 ∧ b2 < a2)) :
    (b1 < a1 ∧ b1 < c1) ∨ (a1 < b1 ∧ c1 < b1) := by
  have hneg : (b2 - a2) * (b2 - c2) < 0 := by
    rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
    · exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have hpos : 0 < (b1 - a1) * (b1 - c1) := by linarith
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right; constructor <;> linarith
  · left; constructor <;> linarith

lemma thales_vertical {a1 a2 c1 c2 b1 b2 : ℤ}
    (th : (b1 - a1) * (b1 - c1) + (b2 - a2) * (b2 - c2) = 0) (hac : a1 = c1) (hb : b1 ≠ a1) :
    (a2 < b2 ∧ b2 < c2) ∨ (c2 < b2 ∧ b2 < a2) := by
  subst hac
  have hpos : 0 < (b1 - a1) * (b1 - a1) := mul_self_pos.mpr (sub_ne_zero.mpr hb)
  have hneg : (b2 - a2) * (b2 - c2) < 0 := by linarith
  rcases mul_neg_iff.mp hneg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; constructor <;> linarith
  · right; constructor <;> linarith

lemma sign_rel {u1 u2 v1 v2 : ℤ} (huv : u1 * v1 + u2 * v2 = 0) :
    ((0 < u1 ∧ 0 < v1) ∨ (u1 < 0 ∧ v1 < 0)) ↔ ((0 < u2 ∧ v2 < 0) ∨ (u2 < 0 ∧ 0 < v2)) := by
  rw [← mul_pos_iff, ← mul_neg_iff]
  constructor <;> intro h <;> linarith

/-- The sign pattern of `A * B + C * D = 0`. -/
lemma thales_lin {A B C D : ℤ} (h : A * B + C * D = 0) :
    ((A = 0 ∨ B = 0) ∧ (C = 0 ∨ D = 0)) ∨
    (((0 < A ∧ 0 < B) ∨ (A < 0 ∧ B < 0)) ∧ ((0 < C ∧ D < 0) ∨ (C < 0 ∧ 0 < D))) ∨
    (((0 < A ∧ B < 0) ∨ (A < 0 ∧ 0 < B)) ∧ ((0 < C ∧ 0 < D) ∨ (C < 0 ∧ D < 0))) := by
  rcases lt_trichotomy (A * B) 0 with hn | hz | hp
  · right; right
    exact ⟨mul_neg_iff.mp hn, mul_pos_iff.mp (by linarith)⟩
  · left
    exact ⟨mul_eq_zero.mp hz, mul_eq_zero.mp (by linarith)⟩
  · right; left
    exact ⟨mul_pos_iff.mp hp, mul_neg_iff.mp (by linarith)⟩

/-- Two pairs with the same sum and the same squared distance: the first point sees the second
pair at a right angle (or lies on it). -/
lemma thales_of_sum {X1 Y1 X2 Y2 Z1 W1 Z2 W2 : ℤ} (hs1 : X1 + X2 = Z1 + Z2)
    (hs2 : Y1 + Y2 = W1 + W2)
    (hl : (X1 - X2) ^ 2 + (Y1 - Y2) ^ 2 = (Z1 - Z2) ^ 2 + (W1 - W2) ^ 2) :
    (X1 - Z1) * (X1 - Z2) + (Y1 - W1) * (Y1 - W2) = 0 := by
  have h4 : 4 * ((X1 - Z1) * (X1 - Z2) + (Y1 - W1) * (Y1 - W2)) = 0 := by
    linear_combination hl + (3 * X1 - X2 - Z1 - Z2) * hs1 + (3 * Y1 - Y2 - W1 - W2) * hs2
  linarith

/-! ### Two black corners -/

/-- Case alpha, beta, gamma-diag: two opposite black corners. The other diagonal straddles the
double's column and avoids both boundary rows. -/
theorem diag_typeD {h : ℕ} {p σ a b : ℤ} (hL : LocHyp h σ a b) {x y u1 u2 v1 v2 : ℤ}
    (hT : TiltOK h y u1 u2 v1 v2) (hA : LBlack h p σ a b (x, y))
    (hC : LBlack h p σ a b (x + u1 + v1, y + u2 + v2)) :
    TypeD h p (x + u1, y + u2) (x + v1, y + v2) := by
  obtain ⟨hh, hσ, ha1, hab, hb⟩ := hL
  obtain ⟨hu1, hu2, hv1, hv2, huv, ⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩, ⟨r3, r3'⟩⟩ := hT
  simp only [LBlack] at hA hC
  have th1 : ((x + u1) - x) * ((x + u1) - (x + u1 + v1)) +
      ((y + u2) - y) * ((y + u2) - (y + u2 + v2)) = 0 := by linear_combination (-1 : ℤ) * huv
  have th2 : ((x + v1) - x) * ((x + v1) - (x + u1 + v1)) +
      ((y + v2) - y) * ((y + v2) - (y + u2 + v2)) = 0 := by linear_combination (-1 : ℤ) * huv
  have hr1 : (y < y + u2 ∧ y + u2 < y + u2 + v2) ∨ (y + u2 + v2 < y + u2 ∧ y + u2 < y) := by
    by_cases hc : x = x + u1 + v1
    · exact thales_vertical th1 hc (by omega)
    · omega
  have hr2 : (y < y + v2 ∧ y + v2 < y + u2 + v2) ∨ (y + u2 + v2 < y + v2 ∧ y + v2 < y) := by
    by_cases hc : x = x + u1 + v1
    · exact thales_vertical th2 hc (by omega)
    · omega
  have hc1 := thales_between th1 hr1
  have hc2 := thales_between th2 hr2
  simp only [TypeD]
  omega

/-- Case gamma-side: two adjacent black corners. One is a sea point and the other lies in the
double's column, and the other two corners lie on the sea's side, off the sea row. -/
theorem side_black {h : ℕ} {p σ a b : ℤ} (hL : LocHyp h σ a b) {x y u1 u2 v1 v2 : ℤ}
    (hT : TiltOK h y u1 u2 v1 v2) (hA : LBlack h p σ a b (x, y))
    (hB : LBlack h p σ a b (x + u1, y + u2)) :
    (((x < p ∧ y = σ ∧ x + u1 = p) ∨ (x = p ∧ x + u1 < p ∧ y + u2 = σ)) ∧
        x + v1 < p ∧ x + u1 + v1 < p ∧ y + v2 ≠ σ ∧ y + u2 + v2 ≠ σ) ∨
      (((x = p ∧ p < x + u1 ∧ y + u2 = h + 1 - σ) ∨ (p < x ∧ y = h + 1 - σ ∧ x + u1 = p)) ∧
        p < x + v1 ∧ p < x + u1 + v1 ∧ y + v2 ≠ h + 1 - σ ∧ y + u2 + v2 ≠ h + 1 - σ) := by
  obtain ⟨hh, hσ, ha1, hab, hb⟩ := hL
  obtain ⟨hu1, hu2, hv1, hv2, huv, ⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩, ⟨r3, r3'⟩⟩ := hT
  simp only [LBlack] at hA hB
  have hs := sign_rel huv
  rcases hA with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2⟩ <;>
    rcases hB with ⟨h3, h4⟩ | ⟨h3, h4 | h4⟩ | ⟨h3, h4⟩ <;> rcases hσ with hσ | hσ <;>
    first | (exfalso; omega) | (left; omega) | (right; omega)

/-! ### Weak tilted rectangles -/

/-- A weak tilted rectangle `C` with black diagonal `{k₁, k₂}` and shown diagonal `{s, t}`. -/
def DiagST (h : ℕ) (p σ a b : ℤ) (C : Finset Pt) (s t : Pt) : Prop :=
  ∃ k1 k2 : Pt, C = {k1, k2, s, t} ∧ TypeD h p s t ∧ k1 + k2 = s + t ∧
    sqd (k1 - k2) = sqd (s - t) ∧ LBlack h p σ a b k1 ∧ LBlack h p σ a b k2 ∧ k1 ≠ k2 ∧
    ¬(k1.2 = k2.2 ∧ (k1.2 = 1 ∨ k1.2 = h))

/-- A weak tilted rectangle `C` with black side `{k, k'}` left of the double (a sea point in
row `σ` and a point of the double's column) and shown side `{k + n, k' + n}`. -/
def SideLST (h : ℕ) (p σ a b : ℤ) (C : Finset Pt) (s t : Pt) : Prop :=
  ∃ k k' n : Pt, s = k + n ∧ t = k' + n ∧ C = {k, k', s, t} ∧ LBlack h p σ a b k ∧
    LBlack h p σ a b k' ∧ ((k.1 < p ∧ k.2 = σ ∧ k'.1 = p) ∨ (k.1 = p ∧ k'.1 < p ∧ k'.2 = σ)) ∧
    s.1 < p ∧ t.1 < p ∧ s.2 ≠ σ ∧ t.2 ≠ σ ∧ s.1 ≠ t.1 ∧ s.2 ≠ t.2

/-- The mirror image of `SideLST`, right of the double, with sea row `h + 1 - σ`. -/
def SideRST (h : ℕ) (p σ a b : ℤ) (C : Finset Pt) (s t : Pt) : Prop :=
  ∃ k k' n : Pt, s = k + n ∧ t = k' + n ∧ C = {k, k', s, t} ∧ LBlack h p σ a b k ∧
    LBlack h p σ a b k' ∧
    ((k.1 = p ∧ p < k'.1 ∧ k'.2 = h + 1 - σ) ∨ (p < k.1 ∧ k.2 = h + 1 - σ ∧ k'.1 = p)) ∧
    p < s.1 ∧ p < t.1 ∧ s.2 ≠ h + 1 - σ ∧ t.2 ≠ h + 1 - σ ∧ s.1 ≠ t.1 ∧ s.2 ≠ t.2

/-- The three shapes of a weak tilted rectangle in the local model, showing `{s, t}`. -/
def WeakST (h : ℕ) (p σ a b : ℤ) (C : Finset Pt) (s t : Pt) : Prop :=
  DiagST h p σ a b C s t ∨ SideLST h p σ a b C s t ∨ SideRST h p σ a b C s t

theorem weak_diag_base {h : ℕ} {p σ a b : ℤ} (hL : LocHyp h σ a b) {x y u1 u2 v1 v2 : ℤ}
    (hT : TiltOK h y u1 u2 v1 v2) (hA : LBlack h p σ a b (x, y))
    (hC : LBlack h p σ a b (x + u1 + v1, y + u2 + v2)) :
    WeakST h p σ a b (tc x y u1 u2 v1 v2) (x + u1, y + u2) (x + v1, y + v2) := by
  have hD := diag_typeD hL hT hA hC
  obtain ⟨hu1, hu2, hv1, hv2, huv, ⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩, ⟨r3, r3'⟩⟩ := hT
  left
  refine ⟨(x, y), (x + u1 + v1, y + u2 + v2), ?_, hD, ?_, ?_, hA, hC, ?_, ?_⟩
  · ext z
    simp only [tc, mem_insert, mem_singleton]
    tauto
  · rw [Prod.mk_add_mk, Prod.mk_add_mk]
    congr 1 <;> ring
  · simp only [sqd, Prod.fst_sub, Prod.snd_sub]
    linear_combination 4 * huv
  · intro he
    simp only [Prod.mk.injEq] at he
    obtain ⟨e1, e2⟩ := he
    have hv1' : v1 = -u1 := by omega
    have hv2' : v2 = -u2 := by omega
    subst hv1' hv2'
    have h0 : u1 * u1 + u2 * u2 = 0 := by linarith
    have := mul_self_pos.mpr hu1
    nlinarith [mul_self_nonneg u2]
  · dsimp only
    omega

theorem weak_side_base {h : ℕ} {p σ a b : ℤ} (hL : LocHyp h σ a b) {x y u1 u2 v1 v2 : ℤ}
    (hT : TiltOK h y u1 u2 v1 v2) (hA : LBlack h p σ a b (x, y))
    (hB : LBlack h p σ a b (x + u1, y + u2)) :
    WeakST h p σ a b (tc x y u1 u2 v1 v2) (x + v1, y + v2) (x + u1 + v1, y + u2 + v2) := by
  have hS := side_black hL hT hA hB
  obtain ⟨hu1, hu2, hv1, hv2, -⟩ := hT
  rcases hS with ⟨hor, h1, h2, h3, h4⟩ | ⟨hor, h1, h2, h3, h4⟩
  · right; left
    exact ⟨(x, y), (x + u1, y + u2), (v1, v2), rfl, rfl, rfl, hA, hB, hor, h1, h2, h3, h4,
      by dsimp only; omega, by dsimp only; omega⟩
  · right; right
    exact ⟨(x, y), (x + u1, y + u2), (v1, v2), rfl, rfl, rfl, hA, hB, hor, h1, h2, h3, h4,
      by dsimp only; omega, by dsimp only; omega⟩

/-! ### Relabelling the corners -/

lemma TiltOK.r1 {h : ℕ} {y u1 u2 v1 v2 : ℤ} (hT : TiltOK h y u1 u2 v1 v2) :
    TiltOK h (y + u2) (-u1) (-u2) v1 v2 := by
  obtain ⟨hu1, hu2, hv1, hv2, huv, ⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩, ⟨r3, r3'⟩⟩ := hT
  exact ⟨by omega, by omega, hv1, hv2, by linear_combination (-1 : ℤ) * huv,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

lemma TiltOK.swap {h : ℕ} {y u1 u2 v1 v2 : ℤ} (hT : TiltOK h y u1 u2 v1 v2) :
    TiltOK h y v1 v2 u1 u2 := by
  obtain ⟨hu1, hu2, hv1, hv2, huv, ⟨r0, r0'⟩, ⟨r1, r1'⟩, ⟨r2, r2'⟩, ⟨r3, r3'⟩⟩ := hT
  exact ⟨hv1, hv2, hu1, hu2, by linear_combination huv, ⟨by omega, by omega⟩,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

lemma TiltOK.r13 {h : ℕ} {y u1 u2 v1 v2 : ℤ} (hT : TiltOK h y u1 u2 v1 v2) :
    TiltOK h (y + u2) v1 v2 (-u1) (-u2) := hT.r1.swap

lemma TiltOK.r23 {h : ℕ} {y u1 u2 v1 v2 : ℤ} (hT : TiltOK h y u1 u2 v1 v2) :
    TiltOK h (y + v2) u1 u2 (-v1) (-v2) := hT.swap.r1.swap

lemma tc_r1 (x y u1 u2 v1 v2 : ℤ) :
    tc (x + u1) (y + u2) (-u1) (-u2) v1 v2 = tc x y u1 u2 v1 v2 := by
  ext ⟨X, Y⟩
  simp only [tc, mem_insert, mem_singleton, Prod.mk.injEq]
  omega

lemma tc_swap (x y u1 u2 v1 v2 : ℤ) : tc x y v1 v2 u1 u2 = tc x y u1 u2 v1 v2 := by
  ext ⟨X, Y⟩
  simp only [tc, mem_insert, mem_singleton, Prod.mk.injEq]
  omega

lemma tc_r13 (x y u1 u2 v1 v2 : ℤ) :
    tc (x + u1) (y + u2) v1 v2 (-u1) (-u2) = tc x y u1 u2 v1 v2 := by
  ext ⟨X, Y⟩
  simp only [tc, mem_insert, mem_singleton, Prod.mk.injEq]
  omega

lemma tc_r23 (x y u1 u2 v1 v2 : ℤ) :
    tc (x + v1) (y + v2) u1 u2 (-v1) (-v2) = tc x y u1 u2 v1 v2 := by
  ext ⟨X, Y⟩
  simp only [tc, mem_insert, mem_singleton, Prod.mk.injEq]
  omega

/-- **The local case analysis.** A tilted rectangle with two black corners in the local model
shows exactly two points, in one of the three shapes `WeakST`. -/
theorem local_weak {h : ℕ} {p σ a b : ℤ} (hL : LocHyp h σ a b) {x y u1 u2 v1 v2 : ℤ}
    (hT : TiltOK h y u1 u2 v1 v2) {k k' : Pt} (hk : k ∈ tc x y u1 u2 v1 v2)
    (hk' : k' ∈ tc x y u1 u2 v1 v2) (hne : k ≠ k') (bk : LBlack h p σ a b k)
    (bk' : LBlack h p σ a b k') : ∃ s t, WeakST h p σ a b (tc x y u1 u2 v1 v2) s t := by
  have D03 : LBlack h p σ a b (x, y) → LBlack h p σ a b (x + u1 + v1, y + u2 + v2) →
      ∃ s t, WeakST h p σ a b (tc x y u1 u2 v1 v2) s t :=
    fun hA hC => ⟨_, _, weak_diag_base hL hT hA hC⟩
  have D12 : LBlack h p σ a b (x + u1, y + u2) → LBlack h p σ a b (x + v1, y + v2) →
      ∃ s t, WeakST h p σ a b (tc x y u1 u2 v1 v2) s t := by
    intro hA hC
    have hC' : LBlack h p σ a b (x + u1 + -u1 + v1, y + u2 + -u2 + v2) := by
      simp only [LBlack] at hC ⊢; omega
    exact ⟨_, _, tc_r1 x y u1 u2 v1 v2 ▸ weak_diag_base hL hT.r1 hA hC'⟩
  have S01 : LBlack h p σ a b (x, y) → LBlack h p σ a b (x + u1, y + u2) →
      ∃ s t, WeakST h p σ a b (tc x y u1 u2 v1 v2) s t :=
    fun hA hB => ⟨_, _, weak_side_base hL hT hA hB⟩
  have S02 : LBlack h p σ a b (x, y) → LBlack h p σ a b (x + v1, y + v2) →
      ∃ s t, WeakST h p σ a b (tc x y u1 u2 v1 v2) s t :=
    fun hA hB => ⟨_, _, tc_swap x y u1 u2 v1 v2 ▸ weak_side_base hL hT.swap hA hB⟩
  have S13 : LBlack h p σ a b (x + u1, y + u2) →
      LBlack h p σ a b (x + u1 + v1, y + u2 + v2) →
      ∃ s t, WeakST h p σ a b (tc x y u1 u2 v1 v2) s t :=
    fun hA hB => ⟨_, _, tc_r13 x y u1 u2 v1 v2 ▸ weak_side_base hL hT.r13 hA hB⟩
  have S23 : LBlack h p σ a b (x + v1, y + v2) →
      LBlack h p σ a b (x + u1 + v1, y + u2 + v2) →
      ∃ s t, WeakST h p σ a b (tc x y u1 u2 v1 v2) s t := by
    intro hA hB
    have hB' : LBlack h p σ a b (x + v1 + u1, y + v2 + u2) := by
      simp only [LBlack] at hB ⊢; omega
    exact ⟨_, _, tc_r23 x y u1 u2 v1 v2 ▸ weak_side_base hL hT.r23 hA hB'⟩
  simp only [tc, mem_insert, mem_singleton] at hk hk'
  rcases hk with rfl | rfl | rfl | rfl <;> rcases hk' with rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hne
    | exact D03 bk bk' | exact D03 bk' bk | exact D12 bk bk' | exact D12 bk' bk
    | exact S01 bk bk' | exact S01 bk' bk | exact S02 bk bk' | exact S02 bk' bk
    | exact S13 bk bk' | exact S13 bk' bk | exact S23 bk bk' | exact S23 bk' bk

/-! ### Consequences of the shapes -/

theorem WeakST.shape {h : ℕ} {p σ a b : ℤ} {C : Finset Pt} {s t : Pt}
    (w : WeakST h p σ a b C s t) :
    TypeD h p s t ∨ (s.1 < p ∧ t.1 < p ∧ s.2 ≠ σ ∧ t.2 ≠ σ ∧ s.1 ≠ t.1 ∧ s.2 ≠ t.2) ∨
      (p < s.1 ∧ p < t.1 ∧ s.2 ≠ h + 1 - σ ∧ t.2 ≠ h + 1 - σ ∧ s.1 ≠ t.1 ∧ s.2 ≠ t.2) := by
  rcases w with ⟨_, _, _, hD, _⟩ | ⟨_, _, _, _, _, _, _, _, _, h1, h2, h3, h4, h5, h6⟩ |
      ⟨_, _, _, _, _, _, _, _, _, h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl hD
  · exact Or.inr (Or.inl ⟨h1, h2, h3, h4, h5, h6⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, h3, h4, h5, h6⟩)

/-- The shown points of a weak tilted rectangle are white, distinct, and in distinct columns. -/
theorem WeakST.white {h : ℕ} {p σ a b : ℤ} (hL : LocHyp h σ a b) {C : Finset Pt} {s t : Pt}
    (w : WeakST h p σ a b C s t) :
    ¬LBlack h p σ a b s ∧ ¬LBlack h p σ a b t ∧ s.1 ≠ t.1 := by
  obtain ⟨hh, hσ, -⟩ := hL
  simp only [LBlack]
  rcases w.shape with hD | hS | hS
  · simp only [TypeD] at hD; omega
  · omega
  · omega

/-- The black corners of a weak tilted rectangle. -/
theorem WeakST.black {h : ℕ} {p σ a b : ℤ} {C : Finset Pt} {s t : Pt}
    (w : WeakST h p σ a b C s t) :
    ∃ k1 k2 : Pt, C = {k1, k2, s, t} ∧ LBlack h p σ a b k1 ∧ LBlack h p σ a b k2 := by
  rcases w with ⟨k1, k2, hC, _, _, _, b1, b2, _⟩ | ⟨k1, k2, _, _, _, hC, b1, b2, _⟩ |
      ⟨k1, k2, _, _, _, hC, b1, b2, _⟩
  all_goals exact ⟨k1, k2, hC, b1, b2⟩

lemma four_eq {a b c d a' b' c' d' : Pt} (h1 : (a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))
    (h2 : (c = c' ∧ d = d') ∨ (c = d' ∧ d = c')) :
    ({a, b, c, d} : Finset Pt) = {a', b', c', d'} := by
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    ext z <;> simp only [mem_insert, mem_singleton] <;> tauto


/-- The case of `black_pair_unique` where the first pair is a sea point left of the double and
a sea point right of it. -/
lemma bpu_LR {h : ℕ} {p σ a b : ℤ} (hL : LocHyp h σ a b) {X1 Y1 X2 Y2 Z1 W1 Z2 W2 : ℤ}
    (g1 : X1 < p) (g2 : Y1 = σ) (g3 : p < X2) (g4 : Y2 = h + 1 - σ)
    (c1 : LBlack h p σ a b (Z1, W1)) (c2 : LBlack h p σ a b (Z2, W2))
    (hs1 : X1 + X2 = Z1 + Z2) (hs2 : Y1 + Y2 = W1 + W2)
    (th : (X1 - Z1) * (X1 - Z2) + (Y1 - W1) * (Y1 - W2) = 0) :
    ((X1 = Z1 ∧ Y1 = W1) ∧ X2 = Z2 ∧ Y2 = W2) ∨ ((X1 = Z2 ∧ Y1 = W2) ∧ X2 = Z1 ∧ Y2 = W1) := by
  obtain ⟨hh, hσ, ha1, hab, hb⟩ := hL
  have t := thales_lin th
  simp only [LBlack] at c1 c2
  rcases c1 with ⟨g5, g6⟩ | ⟨g5, g6 | g6⟩ | ⟨g5, g6⟩ <;>
    rcases c2 with ⟨g7, g8⟩ | ⟨g7, g8 | g8⟩ | ⟨g7, g8⟩ <;> omega

set_option maxHeartbeats 4000000 in
/-- **Black diagonals.** Two black pairs of the local model, each a diagonal of a tilted
rectangle, with the same midpoint and the same length, are equal. -/
theorem black_pair_unique {h : ℕ} {p σ a b : ℤ} (hL : LocHyp h σ a b) {k1 k2 j1 j2 : Pt}
    (b1 : LBlack h p σ a b k1) (b2 : LBlack h p σ a b k2) (c1 : LBlack h p σ a b j1)
    (c2 : LBlack h p σ a b j2) (n1 : k1 ≠ k2) (n2 : j1 ≠ j2)
    (e1 : ¬(k1.2 = k2.2 ∧ (k1.2 = 1 ∨ k1.2 = h))) (e2 : ¬(j1.2 = j2.2 ∧ (j1.2 = 1 ∨ j1.2 = h)))
    (hs : k1 + k2 = j1 + j2) (hl : sqd (k1 - k2) = sqd (j1 - j2)) :
    (k1 = j1 ∧ k2 = j2) ∨ (k1 = j2 ∧ k2 = j1) := by
  obtain ⟨hh, hσ, ha1, hab, hb⟩ := id hL
  obtain ⟨X1, Y1⟩ := k1
  obtain ⟨X2, Y2⟩ := k2
  obtain ⟨Z1, W1⟩ := j1
  obtain ⟨Z2, W2⟩ := j2
  simp only [sqd, Prod.mk_add_mk, Prod.fst_sub, Prod.snd_sub, Prod.mk.injEq, ne_eq]
    at n1 n2 e1 e2 hs hl ⊢
  obtain ⟨hs1, hs2⟩ := hs
  have th1 := thales_of_sum hs1 hs2 hl
  have th1' := thales_of_sum (X1 := X2) (Y1 := Y2) (X2 := X1) (Y2 := Y1) (Z1 := Z1) (W1 := W1)
    (Z2 := Z2) (W2 := W2) (by omega) (by omega)
    (by linear_combination hl)
  have th2 := thales_of_sum hs1.symm hs2.symm hl.symm
  have th2' := thales_of_sum (X1 := Z2) (Y1 := W2) (X2 := Z1) (Y2 := W1) (Z1 := X1) (W1 := Y1)
    (Z2 := X2) (W2 := Y2) (by omega) (by omega) (by linear_combination hl.symm)
  have b1' := b1
  have b2' := b2
  have c1' := c1
  have c2' := c2
  simp only [LBlack] at b1' b2' c1' c2'
  rcases b1' with ⟨g1, g2⟩ | ⟨g1, g2 | g2⟩ | ⟨g1, g2⟩ <;>
    rcases b2' with ⟨g3, g4⟩ | ⟨g3, g4 | g4⟩ | ⟨g3, g4⟩ <;>
    first
    | exact bpu_LR hL g1 g2 g3 g4 c1 c2 hs1 hs2 th1
    | (have := bpu_LR hL g3 g4 g1 g2 c1 c2 (by omega) (by omega) th1'; omega)
    | (rcases c1' with ⟨g5, g6⟩ | ⟨g5, g6 | g6⟩ | ⟨g5, g6⟩ <;>
        rcases c2' with ⟨g7, g8⟩ | ⟨g7, g8 | g8⟩ | ⟨g7, g8⟩ <;>
        first
        | (have := bpu_LR hL g5 g6 g7 g8 b1 b2 hs1.symm hs2.symm th2; omega)
        | (have := bpu_LR hL g7 g8 g5 g6 b1 b2 (by omega) (by omega) th2'; omega)
        | omega)

lemma pair_eq_symm {s1 t1 s2 t2 : Pt} (hst : (s1 = s2 ∧ t1 = t2) ∨ (s1 = t2 ∧ t1 = s2)) :
    (s2 = s1 ∧ t2 = t1) ∨ (s2 = t1 ∧ t2 = s1) := by
  rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩

lemma typeD_not_side {h : ℕ} {p : ℤ} {s t s' t' : Pt} (hD : TypeD h p s t)
    (hst : (s = s' ∧ t = t') ∨ (s = t' ∧ t = s'))
    (hside : (s'.1 < p ∧ t'.1 < p) ∨ (p < s'.1 ∧ p < t'.1)) : False := by
  simp only [TypeD] at hD
  rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

lemma left_not_right {p : ℤ} {s t s' t' : Pt} (h1 : s.1 < p) (h3 : p < s'.1)
    (h4 : p < t'.1) (hst : (s = s' ∧ t = t') ∨ (s = t' ∧ t = s')) : False := by
  rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

/-- Two black left sides with the same translate are equal. -/
lemma sideL_match {p σ : ℤ} {k k' n j j' n' : Pt}
    (hor : (k.1 < p ∧ k.2 = σ ∧ k'.1 = p) ∨ (k.1 = p ∧ k'.1 < p ∧ k'.2 = σ))
    (hor' : (j.1 < p ∧ j.2 = σ ∧ j'.1 = p) ∨ (j.1 = p ∧ j'.1 < p ∧ j'.2 = σ))
    (hst : (k + n = j + n' ∧ k' + n = j' + n') ∨ (k + n = j' + n' ∧ k' + n = j + n')) :
    (k = j ∧ k' = j') ∨ (k = j' ∧ k' = j) := by
  obtain ⟨k1, k2⟩ := k
  obtain ⟨k1', k2'⟩ := k'
  obtain ⟨n1, n2⟩ := n
  obtain ⟨j1, j2⟩ := j
  obtain ⟨j1', j2'⟩ := j'
  obtain ⟨n1', n2'⟩ := n'
  simp only [Prod.mk_add_mk, Prod.mk.injEq] at hor hor' hst ⊢
  rcases hst with ⟨⟨e1, e2⟩, e3, e4⟩ | ⟨⟨e1, e2⟩, e3, e4⟩ <;>
    rcases hor with ⟨f1, f2, f3⟩ | ⟨f1, f2, f3⟩ <;>
    rcases hor' with ⟨f4, f5, f6⟩ | ⟨f4, f5, f6⟩ <;> omega

/-- Two black right sides with the same translate are equal. -/
lemma sideR_match {p ρ : ℤ} {k k' n j j' n' : Pt}
    (hor : (k.1 = p ∧ p < k'.1 ∧ k'.2 = ρ) ∨ (p < k.1 ∧ k.2 = ρ ∧ k'.1 = p))
    (hor' : (j.1 = p ∧ p < j'.1 ∧ j'.2 = ρ) ∨ (p < j.1 ∧ j.2 = ρ ∧ j'.1 = p))
    (hst : (k + n = j + n' ∧ k' + n = j' + n') ∨ (k + n = j' + n' ∧ k' + n = j + n')) :
    (k = j ∧ k' = j') ∨ (k = j' ∧ k' = j) := by
  obtain ⟨k1, k2⟩ := k
  obtain ⟨k1', k2'⟩ := k'
  obtain ⟨n1, n2⟩ := n
  obtain ⟨j1, j2⟩ := j
  obtain ⟨j1', j2'⟩ := j'
  obtain ⟨n1', n2'⟩ := n'
  simp only [Prod.mk_add_mk, Prod.mk.injEq] at hor hor' hst ⊢
  rcases hst with ⟨⟨e1, e2⟩, e3, e4⟩ | ⟨⟨e1, e2⟩, e3, e4⟩ <;>
    rcases hor with ⟨f1, f2, f3⟩ | ⟨f1, f2, f3⟩ <;>
    rcases hor' with ⟨f4, f5, f6⟩ | ⟨f4, f5, f6⟩ <;> omega

/-- **No two weak tilted rectangles of one double show the same pair.** -/
theorem weak_unique {h : ℕ} {p σ a b : ℤ} (hL : LocHyp h σ a b) {C1 C2 : Finset Pt}
    {s1 t1 s2 t2 : Pt} (w1 : WeakST h p σ a b C1 s1 t1) (w2 : WeakST h p σ a b C2 s2 t2)
    (hst : (s1 = s2 ∧ t1 = t2) ∨ (s1 = t2 ∧ t1 = s2)) : C1 = C2 := by
  rcases w1 with ⟨k1, k2, rfl, hD1, hs1, hl1, bk1, bk2, nk, ek⟩ |
      ⟨k, k', n, rfl, rfl, rfl, bk, bk', hor, hp1, hp2, -⟩ |
      ⟨k, k', n, rfl, rfl, rfl, bk, bk', hor, hp1, hp2, -⟩ <;>
    rcases w2 with ⟨j1, j2, rfl, hD2, hs2, hl2, bj1, bj2, nj, ej⟩ |
      ⟨j, j', n', rfl, rfl, rfl, bj, bj', hor', hq1, hq2, -⟩ |
      ⟨j, j', n', rfl, rfl, rfl, bj, bj', hor', hq1, hq2, -⟩
  · -- two diagonal presentations
    have hs : k1 + k2 = j1 + j2 := by
      rw [hs1, hs2]
      rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact add_comm _ _
    have hl : sqd (k1 - k2) = sqd (j1 - j2) := by
      rw [hl1, hl2]
      rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact sqd_sub_comm _ _
    exact four_eq (black_pair_unique hL bk1 bk2 bj1 bj2 nk nj ek ej hs hl) hst
  · exact (typeD_not_side hD1 hst (Or.inl ⟨hq1, hq2⟩)).elim
  · exact (typeD_not_side hD1 hst (Or.inr ⟨hq1, hq2⟩)).elim
  · exact (typeD_not_side hD2 (pair_eq_symm hst) (Or.inl ⟨hp1, hp2⟩)).elim
  · exact four_eq (sideL_match hor hor' hst) hst
  · exact (left_not_right hp1 hq1 hq2 hst).elim
  · exact (typeD_not_side hD2 (pair_eq_symm hst) (Or.inr ⟨hp1, hp2⟩)).elim
  · exact (left_not_right hq1 hp1 hp2 (pair_eq_symm hst)).elim
  · exact four_eq (sideR_match hor hor' hst) hst

lemma mem_axisRect {a b c d X Y : ℤ} :
    (X, Y) ∈ axisRect a b c d ↔ (X = a ∨ X = b) ∧ (Y = c ∨ Y = d) := by
  simp only [axisRect, mem_insert, mem_singleton, Prod.mk.injEq]
  tauto

/-- **No axis-aligned rival.** An axis-aligned rectangle containing the shown pair of a weak
tilted rectangle has a white corner besides that pair, in one of the pair's columns. -/
theorem axis_rival {h : ℕ} {p σ a b : ℤ} (hL : LocHyp h σ a b) {C C₂ : Finset Pt} {s t : Pt}
    (w : WeakST h p σ a b C s t) (hax : IsAxis C₂) (hs : s ∈ C₂) (ht : t ∈ C₂)
    (hblk : ∀ y ∈ C₂, y ≠ s → y ≠ t → (y.1 = s.1 ∨ y.1 = t.1) → LBlack h p σ a b y) :
    False := by
  obtain ⟨hh, hσ, ha1, hab, hb⟩ := hL
  have hsh := w.shape
  obtain ⟨a', b', c', d', hab', hcd', rfl⟩ := hax
  obtain ⟨s1, s2⟩ := s
  obtain ⟨t1, t2⟩ := t
  rw [mem_axisRect] at hs ht
  have hst1 : s1 ≠ t1 := by
    rcases hsh with hD | hS | hS
    · simp only [TypeD] at hD; omega
    · exact hS.2.2.2.2.1
    · exact hS.2.2.2.2.1
  by_cases hrow : s2 = t2
  · subst hrow
    obtain ⟨r, hr, hrs⟩ : ∃ r, (r = c' ∨ r = d') ∧ r ≠ s2 := by
      rcases hs.2 with h' | h'
      · exact ⟨d', Or.inr rfl, by omega⟩
      · exact ⟨c', Or.inl rfl, by omega⟩
    have k1 := hblk (s1, r) (mem_axisRect.mpr ⟨hs.1, hr⟩) (by simp [hrs]) (by simp [hrs])
      (Or.inl rfl)
    have k2 := hblk (t1, r) (mem_axisRect.mpr ⟨ht.1, hr⟩) (by simp [hrs]) (by simp [hrs])
      (Or.inr rfl)
    simp only [LBlack, TypeD] at k1 k2 hsh
    omega
  · have k1 := hblk (t1, s2) (mem_axisRect.mpr ⟨ht.1, hs.2⟩) (by simp [Ne.symm hst1])
      (by simp [hrow]) (Or.inr rfl)
    have k2 := hblk (s1, t2) (mem_axisRect.mpr ⟨hs.1, ht.2⟩) (by simp [Ne.symm hrow])
      (by simp [hst1]) (Or.inl rfl)
    simp only [LBlack, TypeD] at k1 k2 hsh
    omega

end Kagey001
