import Mathlib
import PaperC.GeneratorFiber
import PaperC.C2.TimeReversal

/-!
# Paper C2: the generator point of a cut-transpose

Paper C2 (`paperC2/problem131_reconstruction.tex`), Proposition `prop:amplitudes`(c)
(`paperC2/sec_minors.tex`), the proof's algebra, and the cut-transpose of Corollary
`thm:nonreversible`(c).

Let `Q` be a generator on `X ⊕ Y` with rank-one off-diagonal blocks,
`Q = fromBlocks QX (a bᵀ) (c uᵀ) QY`, and `π > 0` with `π Q = 0`. The cut-transpose of
`C = -Q` across `X` is `C' = fromBlocks (-QX) (-(a cᵀ)) (-(b uᵀ)) (-QYᵀ)`. Proved here:

* `cut_rows`, `cut_cols`, `cut_total`: the three identities of the proof,
  `-QX 1 = (b·1) a` (the rows `X` of `Q 1 = 0`), `-QYᵀ π_Y = (π_X·a) b` (the columns `Y` of
  `π Q = 0`) and `(π_X·a)(b·1) = (π_Y·c)(u·1)` (the sum of the columns `X` of `π Q = 0`);
* `cutTranspose_null` (`prop:amplitudes`(c)): `C' x = 0` for `x = (1_X, s₀ π_Y)` with
  `s₀ = (b·1)/(c·π_Y)`, when `c·π_Y ≠ 0`;
* `cutPoint`, `cutTranspose_blocks` (`prop:amplitudes`(c)): when moreover `b·1 ≠ 0` and `π > 0`, the matrix
  `Q' = -D_x⁻¹ C' D_x` has the blocks `Q'_X = QX` and `Q'_Y = D_{π_Y}⁻¹ QYᵀ D_{π_Y} = Q*_Y`;
* `cutTranspose_isGenerator`: if also `a, b, c, u ≥ 0` (a sign convention for the rank-one
  factors), `Q'` is a generator, the generator point of `C'`.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Kagey131.PaperC

noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- The cut-transpose of `-Q` across `X`, for `Q = fromBlocks QX (a bᵀ) (c uᵀ) QY`. -/
def cutT (QX : Matrix X X ℝ) (QY : Matrix Y Y ℝ) (a u : X → ℝ) (b c : Y → ℝ) :
    Matrix (X ⊕ Y) (X ⊕ Y) ℝ :=
  fromBlocks (-QX) (-(vecMulVec a c)) (-(vecMulVec b u)) (-(QYᵀ))

/-- The null vector `x = (1_X, s₀ π_Y)`, `s₀ = (b·1)/(c·π_Y)`. -/
def cutVec (b c : Y → ℝ) (πY : Y → ℝ) : X ⊕ Y → ℝ :=
  Sum.elim (fun _ => 1) (fun y => ((∑ y', b y') / (c ⬝ᵥ πY)) * πY y)

section Identities

variable {QX : Matrix X X ℝ} {QY : Matrix Y Y ℝ} {a u : X → ℝ} {b c : Y → ℝ} {π : X ⊕ Y → ℝ}
  {Q : Matrix (X ⊕ Y) (X ⊕ Y) ℝ}

omit [DecidableEq X] [DecidableEq Y] in
/-- The rows `X` of `Q 1 = 0`: `∑_j QX x j = -(b·1) a_x`. -/
theorem cut_rows (hQ : Q = fromBlocks QX (vecMulVec a b) (vecMulVec c u) QY)
    (hrow : ∀ i, ∑ j, Q i j = 0) (x : X) : ∑ j, QX x j = -((∑ y, b y) * a x) := by
  have := hrow (Sum.inl x)
  rw [Fintype.sum_sum_type, hQ] at this
  simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, vecMulVec_apply] at this
  rw [← Finset.mul_sum] at this
  linarith

omit [DecidableEq X] [DecidableEq Y] in
/-- The columns `Y` of `π Q = 0`: `∑_{y'} π_{y'} QY y' y = -(π_X·a) b_y`. -/
theorem cut_cols (hQ : Q = fromBlocks QX (vecMulVec a b) (vecMulVec c u) QY)
    (hstat : ∀ j, ∑ i, π i * Q i j = 0) (y : Y) :
    ∑ y', π (Sum.inr y') * QY y' y = -((∑ x, π (Sum.inl x) * a x) * b y) := by
  have := hstat (Sum.inr y)
  rw [Fintype.sum_sum_type, hQ] at this
  simp only [fromBlocks_apply₁₂, fromBlocks_apply₂₂, vecMulVec_apply] at this
  have h : ∑ x, π (Sum.inl x) * (a x * b y) = (∑ x, π (Sum.inl x) * a x) * b y := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun _ _ => by ring)
  linarith

omit [DecidableEq X] [DecidableEq Y] in
/-- The sum of the columns `X` of `π Q = 0`: `(π_X·a)(b·1) = (π_Y·c)(u·1)`. -/
theorem cut_total (hQ : Q = fromBlocks QX (vecMulVec a b) (vecMulVec c u) QY)
    (hrow : ∀ i, ∑ j, Q i j = 0) (hstat : ∀ j, ∑ i, π i * Q i j = 0) :
    (∑ x, π (Sum.inl x) * a x) * (∑ y, b y) = (∑ y, π (Sum.inr y) * c y) * (∑ x, u x) := by
  have h3 : ∀ x : X, ∑ x', π (Sum.inl x') * QX x' x + (∑ y, π (Sum.inr y) * c y) * u x = 0 := by
    intro x
    have := hstat (Sum.inl x)
    rw [Fintype.sum_sum_type, hQ] at this
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₁, vecMulVec_apply] at this
    have h : ∑ y, π (Sum.inr y) * (c y * u x) = (∑ y, π (Sum.inr y) * c y) * u x := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith
  have h4 := Finset.sum_eq_zero (s := (univ : Finset X)) (fun x _ => h3 x)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm] at h4
  have h6 : ∀ x', ∑ x, π (Sum.inl x') * QX x' x
      = -(π (Sum.inl x') * a x' * ∑ y, b y) := by
    intro x'
    rw [← Finset.mul_sum, cut_rows hQ hrow x']; ring
  have h5 : ∑ x', ∑ x, π (Sum.inl x') * QX x' x = -((∑ x, π (Sum.inl x) * a x) * ∑ y, b y) := by
    rw [Finset.sum_congr rfl (fun x' _ => h6 x'), Finset.sum_neg_distrib, ← Finset.sum_mul]
  linarith

end Identities

section Null

variable {QX : Matrix X X ℝ} {QY : Matrix Y Y ℝ} {a u : X → ℝ} {b c : Y → ℝ} {π : X ⊕ Y → ℝ}
  {Q : Matrix (X ⊕ Y) (X ⊕ Y) ℝ}

omit [DecidableEq X] [DecidableEq Y] in
/-- `prop:amplitudes`(c): the cut-transpose `C'` has the null vector
`x = (1_X, s₀ π_Y)` with `s₀ = (b·1)/(c·π_Y)`. -/
theorem cutTranspose_null (hQ : Q = fromBlocks QX (vecMulVec a b) (vecMulVec c u) QY)
    (hrow : ∀ i, ∑ j, Q i j = 0) (hstat : ∀ j, ∑ i, π i * Q i j = 0)
    (hc : c ⬝ᵥ (fun y => π (Sum.inr y)) ≠ 0) :
    cutT QX QY a u b c *ᵥ cutVec b c (fun y => π (Sum.inr y)) = 0 := by
  have htot := cut_total hQ hrow hstat
  set P : ℝ := c ⬝ᵥ (fun y => π (Sum.inr y)) with hPdef
  have hP : ∑ y, c y * π (Sum.inr y) = P := rfl
  have hP' : ∑ y, π (Sum.inr y) * c y = P := by
    rw [← hP]; exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  set S : ℝ := ∑ y, b y with hS
  set s0 : ℝ := S / P with hs0
  have hsP : s0 * P = S := div_mul_cancel₀ _ hc
  have key : s0 * (∑ x, π (Sum.inl x) * a x) = ∑ x, u x := by
    rw [hP'] at htot
    have : P * (s0 * ∑ x, π (Sum.inl x) * a x) = P * ∑ x, u x := by
      calc P * (s0 * ∑ x, π (Sum.inl x) * a x) = (s0 * P) * ∑ x, π (Sum.inl x) * a x := by ring
        _ = P * ∑ x, u x := by rw [hsP]; linarith
    exact mul_left_cancel₀ hc this
  ext i
  rcases i with x | y
  · simp only [mulVec, dotProduct, Fintype.sum_sum_type, cutT, cutVec, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, Sum.elim_inl, Sum.elim_inr, Matrix.neg_apply, Pi.zero_apply]
    rw [show ((∑ y', b y') / ∑ x, c x * π (Sum.inr x)) = s0 from rfl]
    have h1 := cut_rows hQ hrow x
    have h2 : ∀ y, -(vecMulVec a c x y) * (s0 * π (Sum.inr y))
        = -(a x * s0) * (c y * π (Sum.inr y)) := by
      intro y; simp [vecMulVec_apply]; ring
    rw [Finset.sum_congr rfl (fun y _ => h2 y), ← Finset.mul_sum, hP]
    have h3 : ∑ x', -QX x x' * 1 = -∑ x', QX x x' := by simp
    rw [h3, h1]
    have : a x * s0 * P = a x * S := by rw [mul_assoc, hsP]
    linarith
  · simp only [mulVec, dotProduct, Fintype.sum_sum_type, cutT, cutVec, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.neg_apply, Pi.zero_apply]
    rw [show ((∑ y', b y') / ∑ x, c x * π (Sum.inr x)) = s0 from rfl]
    have h1 := cut_cols hQ hstat y
    have h2 : ∀ x, -(vecMulVec b u y x) * 1 = -(b y * u x) := by
      intro x; simp [vecMulVec_apply]
    have h3 : ∀ y', -(QYᵀ y y') * (s0 * π (Sum.inr y')) = -(s0 * (π (Sum.inr y') * QY y' y)) := by
      intro y'; simp [transpose_apply]; ring
    rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_congr rfl (fun y' _ => h3 y'),
      Finset.sum_neg_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1]
    have : b y * ∑ x, u x = s0 * ((∑ x, π (Sum.inl x) * a x) * b y) := by
      rw [← key]; ring
    linarith

/-- The generator point `Q' = D_x⁻¹ (-C') D_x` of the cut-transpose, for the null vector
`x = cutVec b c π_Y`. -/
def cutPoint (QX : Matrix X X ℝ) (QY : Matrix Y Y ℝ) (a u : X → ℝ) (b c πY : Y → ℝ) :
    Matrix (X ⊕ Y) (X ⊕ Y) ℝ :=
  diagonal (fun i => (cutVec b c πY i)⁻¹) * (-(cutT QX QY a u b c)) * diagonal (cutVec b c πY)

/-- `prop:amplitudes`(c): the blocks of the generator point are `Q'_X = QX` and
`Q'_Y = D_{π_Y}⁻¹ QYᵀ D_{π_Y} = Q*_Y`, when `b·1 ≠ 0`, `c·π_Y ≠ 0` and `π_Y > 0`. -/
theorem cutTranspose_blocks {πY : Y → ℝ} (hπ : ∀ y, 0 < πY y) (hb : ∑ y, b y ≠ 0)
    (hc : c ⬝ᵥ πY ≠ 0) :
    (cutPoint QX QY a u b c πY).toBlocks₁₁ = QX ∧
    (cutPoint QX QY a u b c πY).toBlocks₂₂ = starMat πY QY := by
  have hs0 : (∑ y', b y') / (c ⬝ᵥ πY) ≠ 0 := div_ne_zero hb hc
  constructor
  · ext x x'
    simp [cutPoint, toBlocks₁₁, cutVec, cutT]
  · ext y y'
    have hy := (hπ y).ne'
    simp [cutPoint, toBlocks₂₂, cutVec, cutT, starMat, transpose_apply]
    field_simp

/-- `prop:amplitudes`(c) and the generator point: if `Q` is a generator on `X ⊕ Y` with
`Q = fromBlocks QX (a bᵀ) (c uᵀ) QY` for nonnegative `a, b, c, u`, `π > 0` with `π Q = 0`,
`b·1 > 0` and `c·π_Y > 0`, then the generator point `Q'` of the cut-transpose is a generator. -/
theorem cutTranspose_isGenerator
    (hQ : Q = fromBlocks QX (vecMulVec a b) (vecMulVec c u) QY) (hgen : IsGenerator Q)
    (hstat : ∀ j, ∑ i, π i * Q i j = 0) (hπ : ∀ i, 0 < π i)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) (hc : ∀ y, 0 ≤ c y) (hu : ∀ x, 0 ≤ u x)
    (hbpos : 0 < ∑ y, b y) (hcpos : 0 < c ⬝ᵥ (fun y => π (Sum.inr y))) :
    IsGenerator (cutPoint QX QY a u b c (fun y => π (Sum.inr y))) := by
  have hnull := cutTranspose_null hQ hgen.2 hstat hcpos.ne'
  have hs0 : 0 < (∑ y', b y') / (c ⬝ᵥ fun y => π (Sum.inr y)) := div_pos hbpos hcpos
  have hxpos : ∀ i : X ⊕ Y, 0 < cutVec b c (fun y => π (Sum.inr y)) i := by
    intro i
    rcases i with x | y
    · simp [cutVec]
    · simp [cutVec]; exact mul_pos hs0 (hπ _)
  have hmet : IsMetzler (-(cutT QX QY a u b c)) := by
    intro i j hij
    rcases i with x | y <;> rcases j with x' | y'
    · have := hgen.1 (Sum.inl x) (Sum.inl x') (by simpa using hij)
      simpa [cutT, hQ] using this
    · simp [cutT, vecMulVec_apply]; exact mul_nonneg (ha _) (hc _)
    · simp [cutT, vecMulVec_apply]; exact mul_nonneg (hb _) (hu _)
    · have := hgen.1 (Sum.inr y') (Sum.inr y) (by simpa [eq_comm] using hij)
      simpa [cutT, hQ, transpose_apply] using this
  refine normalize_isGenerator hmet hxpos ?_
  rw [Matrix.neg_mulVec, hnull, neg_zero]


end Null

section Signs

/-- A nonzero rank-one matrix with nonnegative entries has nonnegative factors, after replacing
`(a, b)` by `(-a, -b)` if necessary. -/
theorem exists_nonneg_factors {m n : Type*} (a : m → ℝ) (b : n → ℝ) (h : ∀ i j, 0 ≤ a i * b j)
    (hne : ∃ i j, a i * b j ≠ 0) :
    ∃ (a' : m → ℝ) (b' : n → ℝ), (∀ i, 0 ≤ a' i) ∧ (∀ j, 0 ≤ b' j) ∧
      ∀ i j, a' i * b' j = a i * b j := by
  obtain ⟨i0, j0, h0⟩ := hne
  have ha0 : a i0 ≠ 0 := left_ne_zero_of_mul h0
  have hb0 : b j0 ≠ 0 := right_ne_zero_of_mul h0
  rcases lt_or_gt_of_ne ha0 with ha | ha
  · have hb : b j0 < 0 := by
      by_contra hc
      have := mul_nonpos_of_nonpos_of_nonneg ha.le (not_lt.mp hc)
      exact h0 (le_antisymm this (h i0 j0))
    refine ⟨fun i => -a i, fun j => -b j, fun i => ?_, fun j => ?_, fun i j => by ring⟩
    · have := h i j0
      by_contra hc
      push Not at hc
      nlinarith
    · have := h i0 j
      by_contra hc
      push Not at hc
      nlinarith
  · have hb : 0 < b j0 := by
      by_contra hc
      have := mul_nonpos_of_nonneg_of_nonpos ha.le (not_lt.mp hc)
      exact h0 (le_antisymm this (h i0 j0))
    refine ⟨a, b, fun i => ?_, fun j => ?_, fun i j => rfl⟩
    · have := h i j0
      by_contra hc
      push Not at hc
      nlinarith
    · have := h i0 j
      by_contra hc
      push Not at hc
      nlinarith

variable {QX : Matrix X X ℝ} {QY : Matrix Y Y ℝ} {a u : X → ℝ} {b c : Y → ℝ} {π : X ⊕ Y → ℝ}
  {Q : Matrix (X ⊕ Y) (X ⊕ Y) ℝ}

/-- The sign convention `a, b, c, u ≥ 0` is no loss. In `sec_minors.tex` (before
`eq:cut-transpose`) the paper takes the factors nonnegative because the blocks of an irreducible
Metzler `Q` are nonzero, nonnegative and of rank one. Here: if `Q` is a generator with rank-one
blocks (factors of any sign) and both blocks are nonzero, then the factors can be chosen
nonnegative without changing the blocks, and the generator point of the cut-transpose built from
them is a generator. -/
theorem cutTranspose_isGenerator_of_blocks
    (hQ : Q = fromBlocks QX (vecMulVec a b) (vecMulVec c u) QY) (hgen : IsGenerator Q)
    (hstat : ∀ j, ∑ i, π i * Q i j = 0) (hπ : ∀ i, 0 < π i)
    (hab : vecMulVec a b ≠ 0) (hcu : vecMulVec c u ≠ 0) :
    ∃ (a' u' : X → ℝ) (b' c' : Y → ℝ), (∀ x, 0 ≤ a' x) ∧ (∀ y, 0 ≤ b' y) ∧ (∀ y, 0 ≤ c' y) ∧
      (∀ x, 0 ≤ u' x) ∧ vecMulVec a' b' = vecMulVec a b ∧ vecMulVec c' u' = vecMulVec c u ∧
      IsGenerator (cutPoint QX QY a' u' b' c' (fun y => π (Sum.inr y))) := by
  have h1 : ∀ i j, 0 ≤ a i * b j := fun i j => by
    have := hgen.1 (Sum.inl i) (Sum.inr j) (by simp)
    simpa [hQ, vecMulVec_apply] using this
  have h2 : ∀ i j, 0 ≤ c i * u j := fun i j => by
    have := hgen.1 (Sum.inr i) (Sum.inl j) (by simp)
    simpa [hQ, vecMulVec_apply] using this
  have hne1 : ∃ i j, a i * b j ≠ 0 := by
    by_contra hc; push Not at hc
    exact hab (by ext i j; simpa [vecMulVec_apply] using hc i j)
  have hne2 : ∃ i j, c i * u j ≠ 0 := by
    by_contra hc; push Not at hc
    exact hcu (by ext i j; simpa [vecMulVec_apply] using hc i j)
  obtain ⟨a', b', ha', hb', hab'⟩ := exists_nonneg_factors a b h1 hne1
  obtain ⟨c', u', hc', hu', hcu'⟩ := exists_nonneg_factors c u h2 hne2
  have e1 : vecMulVec a' b' = vecMulVec a b := by ext i j; simpa [vecMulVec_apply] using hab' i j
  have e2 : vecMulVec c' u' = vecMulVec c u := by ext i j; simpa [vecMulVec_apply] using hcu' i j
  refine ⟨a', u', b', c', ha', hb', hc', hu', e1, e2, ?_⟩
  have hQ' : Q = fromBlocks QX (vecMulVec a' b') (vecMulVec c' u') QY := by rw [e1, e2]; exact hQ
  obtain ⟨i0, j0, h0⟩ := hne1
  obtain ⟨k0, l0, h0'⟩ := hne2
  have hbpos : 0 < ∑ y, b' y := by
    have hj : b' j0 ≠ 0 := by
      intro hz; apply h0; rw [← hab' i0 j0, hz, mul_zero]
    have : 0 < b' j0 := lt_of_le_of_ne (hb' j0) (Ne.symm hj)
    exact lt_of_lt_of_le this
      (Finset.single_le_sum (fun y _ => hb' y) (Finset.mem_univ j0))
  have hcpos : 0 < c' ⬝ᵥ (fun y => π (Sum.inr y)) := by
    have hj : c' k0 ≠ 0 := by
      intro hz; apply h0'; rw [← hcu' k0 l0, hz, zero_mul]
    have : 0 < c' k0 := lt_of_le_of_ne (hc' k0) (Ne.symm hj)
    have hterm : 0 < c' k0 * π (Sum.inr k0) := mul_pos this (hπ _)
    exact lt_of_lt_of_le hterm
      (Finset.single_le_sum (f := fun y => c' y * π (Sum.inr y))
        (fun y _ => mul_nonneg (hc' y) (hπ _).le) (Finset.mem_univ k0))
  exact cutTranspose_isGenerator hQ' hgen hstat hπ ha' hb' hc' hu' hbpos hcpos

end Signs

end

end Kagey131.PaperC.C2
