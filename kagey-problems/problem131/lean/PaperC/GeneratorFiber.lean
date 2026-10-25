import Mathlib

/-!
# Paper C2: the generator normalization, the sign lemma and the case `d = 3`

Paper C2 (`paperC2/problem131_reconstruction.tex`), Section 3.3 (`paperC2/sec_minors.tex`,
Theorem 3.5, `thm:nonreversible`, step (N) of its proof and parts (a) and (d), and Remark 3.6,
`rem:three-states`), and note 06 of
`research_notes/C theorems 5 and 7` (Lemma 3.2, Proposition 3.3, Corollary 4.2).

Irreducibility. A real square matrix `C` is `CutIrreducible` if every nonempty proper set `S`
of states has an arc leaving it, `C i j ≠ 0` with `i ∈ S`, `j ∉ S`. For a finite state space
this is the strong connectivity of the digraph of nonzero off-diagonal entries (the standard
"no nontrivial invariant coordinate subset" form). We do not use `Matrix.IsIrreducible` of
Mathlib, which is stated for entrywise nonnegative matrices.

Proved here:

* `cutIrreducible_iff_reach`: `CutIrreducible C` holds exactly when every state reaches every
  other along arcs `i → j` with `i ≠ j`, `C i j ≠ 0` (strong connectivity);
* `conj_apply`, `normalize_isGenerator`: for a Metzler `C` and `x > 0` with `C x = 0`,
  `diag(x)⁻¹ C diag(x)` is a generator (Metzler with zero row sums);
* `ker_eq_smul`: for an irreducible Metzler `C` with a positive null vector `x`, every null
  vector is a multiple of `x`;
* `sign_constant`: if `C` is irreducible and Metzler and `D C D⁻¹` is Metzler for a diagonal
  `D` with nonzero entries, the entries of `D` have one sign (note 06, Lemma 3.2);
* `normalization_unique`, `normalization_unique_matrix`: every diagonal `D` with nonzero
  entries for which `D⁻¹ C D` has zero row sums is a nonzero multiple of `diag(x)`, and gives
  the same generator (note 06, Proposition 3.3; the positive normalization is unique up to a
  scalar, and no mixed-sign similarity gives a generator);
* for `d = 3` (note 06, Corollary 4.2, Theorem 3.5(d) and Remark 3.6 of Paper C2), with
  `q_i = -Q_ii`, `w_ij = q_ij q_ji` and the oriented 3-cycle products `c = q_12 q_23 q_31`,
  `c' = q_13 q_32 q_21` (written `ω`, `ω'` in Paper C2):
  - `det_neg_three`: `det(-Q) = σ₃ - c - c'` with
    `σ₃ = q_1 q_2 q_3 - q_1 w_23 - q_2 w_13 - q_3 w_12`, for every `3 × 3` matrix;
  - `cyc_add_cycRev`: `c + c' = σ₃` for a generator (from `det(-Q) = 0`);
  - `cyc_mul_cycRev`: `c c' = w_12 w_23 w_13`;
  - `eq_of_same_q_w_cyc`: two generators with positive off-diagonal entries and the same
    `q_i`, `w_ij` and `c` are equal;
  - `timeRev_eq_conj`, `timeRev_isGenerator`, `timeRev_diag`, `timeRev_wprod`, `cyc_timeRev`: the time reversal
    `Q* = D_π⁻¹ Qᵀ D_π` is a generator with the same `q_i` and `w_ij` and with `c(Q*) = c'(Q)`;
  - `piTree_stationary`, `piTree_pos`: the tree formula gives a positive stationary vector;
  - `fiber_three`: two generators on three states with positive off-diagonal entries and the
    same `q_i` and `w_ij` are equal or time reversals of each other (Theorem 3.5(d) of Paper C2, for positive rates);
  - `fiber_three_converse`: the time reversal has the same `q_i` and `w_ij`.
-/

namespace Kagey131.PaperC

open Finset Matrix

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Metzler matrix: nonnegative off-diagonal entries. -/
def IsMetzler (C : Matrix ι ι ℝ) : Prop := ∀ i j, i ≠ j → 0 ≤ C i j

/-- A generator: Metzler with zero row sums. -/
def IsGenerator (Q : Matrix ι ι ℝ) : Prop := IsMetzler Q ∧ ∀ i, ∑ j, Q i j = 0

/-- Irreducibility: every nonempty proper set of states has an arc `C i j ≠ 0` leaving it. -/
def CutIrreducible (C : Matrix ι ι ℝ) : Prop :=
  ∀ S : Finset ι, S.Nonempty → S ≠ univ → ∃ i ∈ S, ∃ j ∉ S, C i j ≠ 0

/-- The arcs `i → j`, `i ≠ j`, `C i j ≠ 0`, of the digraph of `C`. -/
def arc (C : Matrix ι ι ℝ) (i j : ι) : Prop := i ≠ j ∧ C i j ≠ 0

/-- `CutIrreducible` is strong connectivity of the digraph of nonzero off-diagonal entries. -/
theorem cutIrreducible_iff_reach (C : Matrix ι ι ℝ) :
    CutIrreducible C ↔ ∀ i j, Relation.ReflTransGen (arc C) i j := by
  constructor
  · intro h i j
    classical
    by_contra hij
    set S := univ.filter (fun k => Relation.ReflTransGen (arc C) i k) with hSdef
    have hS : S.Nonempty := ⟨i, mem_filter.mpr ⟨mem_univ _, Relation.ReflTransGen.refl⟩⟩
    have hSu : S ≠ univ := fun e => by
      have hjS : j ∈ S := e ▸ mem_univ j
      exact hij (mem_filter.mp hjS).2
    obtain ⟨a, ha, b, hb, hab⟩ := h S hS hSu
    have hra := (mem_filter.mp ha).2
    have hne : a ≠ b := fun e => hb (e ▸ ha)
    exact hb (mem_filter.mpr ⟨mem_univ _, hra.tail ⟨hne, hab⟩⟩)
  · intro h S ⟨i, hi⟩ hS
    obtain ⟨j, hj⟩ : ∃ j, j ∉ S := by
      by_contra h'
      push Not at h'
      exact hS (eq_univ_iff_forall.mpr h')
    have key : ∀ k, Relation.ReflTransGen (arc C) i k → k ∉ S →
        ∃ a ∈ S, ∃ b ∉ S, C a b ≠ 0 := by
      intro k hk
      induction hk with
      | refl => exact fun h' => absurd hi h'
      | @tail b c _ hbc ih =>
        intro hc
        by_cases hb : b ∈ S
        · exact ⟨b, hb, c, hc, hbc.2⟩
        · exact ih hb
    exact key j (h i j) hj

/-- A matrix with all off-diagonal entries nonzero is irreducible. -/
theorem cutIrreducible_of_offdiag_ne {C : Matrix ι ι ℝ} (h : ∀ i j, i ≠ j → C i j ≠ 0) :
    CutIrreducible C := by
  intro S ⟨i, hi⟩ hS
  obtain ⟨j, hj⟩ : ∃ j, j ∉ S := by
    by_contra h'
    push Not at h'
    exact hS (eq_univ_iff_forall.mpr h')
  exact ⟨i, hi, j, hj, h i j (fun e => hj (e ▸ hi))⟩

/-- The entries of `diag(a) C diag(b)`. -/
theorem conj_apply (a b : ι → ℝ) (C : Matrix ι ι ℝ) (i j : ι) :
    (diagonal a * C * diagonal b) i j = a i * C i j * b j := by
  rw [mul_diagonal, diagonal_mul]

/-- `diag(x)⁻¹ C diag(x)` is a generator when `C` is Metzler, `x > 0` and `C x = 0`. -/
theorem normalize_isGenerator {C : Matrix ι ι ℝ} (hC : IsMetzler C) {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hCx : C *ᵥ x = 0) :
    IsGenerator (diagonal (fun i => (x i)⁻¹) * C * diagonal x) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conj_apply]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (hx i).le) (hC i j hij)) (hx j).le
  · simp_rw [conj_apply, mul_assoc, ← mul_sum]
    have : (C *ᵥ x) i = 0 := by rw [hCx]; rfl
    simp only [mulVec, dotProduct] at this
    rw [this, mul_zero]

/-- The null space of an irreducible Metzler matrix with a positive null vector `x` is the
line through `x`. -/
theorem ker_eq_smul {C : Matrix ι ι ℝ} (hC : IsMetzler C) (hirr : CutIrreducible C)
    {x y : ι → ℝ} (hx : ∀ i, 0 < x i) (hCx : C *ᵥ x = 0) (hCy : C *ᵥ y = 0) :
    ∃ c : ℝ, y = c • x := by
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨0, funext fun i => (IsEmpty.false i).elim⟩
  | inr h =>
  obtain ⟨i0, -, hi0⟩ := exists_min_image univ (fun i => y i / x i) univ_nonempty
  set c := y i0 / x i0
  set z := y - c • x with hz
  have hz0 : ∀ i, 0 ≤ z i := by
    intro i
    have h1 := hi0 i (mem_univ i)
    have hxi := hx i
    simp only [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg]
    rw [div_le_div_iff₀ (hx i0) hxi] at h1
    simp only [c]
    rw [div_mul_eq_mul_div, div_le_iff₀ (hx i0)]
    linarith
  have hzi0 : z i0 = 0 := by
    simp only [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, c]
    field_simp [(hx i0).ne']
    ring
  have hCz : C *ᵥ z = 0 := by
    rw [hz, mulVec_sub, mulVec_smul, hCx, hCy, smul_zero, sub_zero]
  refine ⟨c, ?_⟩
  by_contra hne
  set S := univ.filter (fun i => z i = 0)
  have hSne : S.Nonempty := ⟨i0, mem_filter.mpr ⟨mem_univ _, hzi0⟩⟩
  have hSu : S ≠ univ := by
    intro hS
    apply hne
    funext i
    have hiS : i ∈ S := hS ▸ mem_univ i
    have : z i = 0 := (mem_filter.mp hiS).2
    have := congrFun hz i
    simp only [Pi.sub_apply] at this
    linarith [this, ‹z i = 0›]
  obtain ⟨i, hi, j, hj, hij⟩ := hirr S hSne hSu
  have hzi : z i = 0 := (mem_filter.mp hi).2
  have hzj : z j ≠ 0 := fun h => hj (mem_filter.mpr ⟨mem_univ _, h⟩)
  have hne_ij : i ≠ j := fun e => hj (e ▸ hi)
  have hCij : 0 < C i j := lt_of_le_of_ne (hC i j hne_ij) (Ne.symm hij)
  have hterm : ∀ k ∈ univ, 0 ≤ C i k * z k := by
    intro k _
    by_cases hk : k = i
    · rw [hk, hzi, mul_zero]
    · exact mul_nonneg (hC i k (Ne.symm hk)) (hz0 k)
  have hpos : 0 < C i j * z j := mul_pos hCij (lt_of_le_of_ne (hz0 j) (Ne.symm hzj))
  have hsum : C i j * z j ≤ ∑ k, C i k * z k := single_le_sum hterm (mem_univ j)
  have : (C *ᵥ z) i = 0 := by rw [hCz]; rfl
  simp only [mulVec, dotProduct] at this
  linarith

/-- Note 06, Lemma 3.2 (the sign lemma): if `C` is irreducible and Metzler and
`D C D⁻¹` is Metzler for a diagonal `D` with nonzero entries, the entries of `D` have one sign. -/
theorem sign_constant {C : Matrix ι ι ℝ} (hC : IsMetzler C) (hirr : CutIrreducible C)
    {d : ι → ℝ} (hd : ∀ i, d i ≠ 0)
    (hM : IsMetzler (diagonal d * C * diagonal (fun i => (d i)⁻¹))) :
    (∀ i, 0 < d i) ∨ (∀ i, d i < 0) := by
  set S := univ.filter (fun i => 0 < d i)
  by_cases hSe : S.Nonempty
  · by_cases hSu : S = univ
    · left; intro i
      have hiS : i ∈ S := hSu ▸ mem_univ i
      exact (mem_filter.mp hiS).2
    · exfalso
      obtain ⟨i, hi, j, hj, hij⟩ := hirr S hSe hSu
      have hdi : 0 < d i := (mem_filter.mp hi).2
      have hdj : d j < 0 := lt_of_le_of_ne (not_lt.mp fun h => hj (mem_filter.mpr ⟨mem_univ _, h⟩))
        (hd j)
      have hne : i ≠ j := fun e => hj (e ▸ hi)
      have hCij : 0 < C i j := lt_of_le_of_ne (hC i j hne) (Ne.symm hij)
      have h := hM i j hne
      rw [conj_apply] at h
      have : d i * C i j * (d j)⁻¹ < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hdi hCij) (inv_lt_zero.mpr hdj)
      linarith
  · right
    intro i
    have : ¬ (0 < d i) := fun h => hSe ⟨i, mem_filter.mpr ⟨mem_univ _, h⟩⟩
    exact lt_of_le_of_ne (not_lt.mp this) (hd i)

/-- Note 06, Proposition 3.3 (the normalization), uniqueness: if `D⁻¹ C D` has zero row sums for
a diagonal `D` with nonzero entries, then `D` is a nonzero multiple of `diag(x)`. -/
theorem normalization_unique {C : Matrix ι ι ℝ} (hC : IsMetzler C) (hirr : CutIrreducible C)
    {x : ι → ℝ} (hx : ∀ i, 0 < x i) (hCx : C *ᵥ x = 0) {d : ι → ℝ} (hd : ∀ i, d i ≠ 0)
    (hrow : ∀ i, ∑ j, (diagonal (fun i => (d i)⁻¹) * C * diagonal d) i j = 0) :
    ∃ c : ℝ, c ≠ 0 ∧ d = c • x := by
  have hCd : C *ᵥ d = 0 := by
    funext i
    have h := hrow i
    simp_rw [conj_apply, mul_assoc, ← mul_sum] at h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (inv_ne_zero (hd i))
    · simpa [mulVec, dotProduct] using h
  obtain ⟨c, hc⟩ := ker_eq_smul hC hirr hx hCx hCd
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨1, one_ne_zero, funext fun i => (IsEmpty.false i).elim⟩
  | inr h =>
    obtain ⟨i⟩ := h
    refine ⟨c, fun hc0 => hd i ?_, hc⟩
    rw [hc, hc0, zero_smul]; rfl

/-- Note 06, Proposition 3.3: every diagonal similarity with nonzero entries that gives a matrix
with zero row sums gives the same generator `diag(x)⁻¹ C diag(x)`. -/
theorem normalization_unique_matrix {C : Matrix ι ι ℝ} (hC : IsMetzler C)
    (hirr : CutIrreducible C) {x : ι → ℝ} (hx : ∀ i, 0 < x i) (hCx : C *ᵥ x = 0)
    {d : ι → ℝ} (hd : ∀ i, d i ≠ 0)
    (hrow : ∀ i, ∑ j, (diagonal (fun i => (d i)⁻¹) * C * diagonal d) i j = 0) :
    diagonal (fun i => (d i)⁻¹) * C * diagonal d =
      diagonal (fun i => (x i)⁻¹) * C * diagonal x := by
  obtain ⟨c, hc0, rfl⟩ := normalization_unique hC hirr hx hCx hd hrow
  ext i j
  rw [conj_apply, conj_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have := (hx i).ne'
  field_simp

end General

section Three

/-! ### Three states -/

variable (Q : Matrix (Fin 3) (Fin 3) ℝ)

/-- The oriented 3-cycle product `c = q_12 q_23 q_31` (states `0, 1, 2` in Lean). -/
def cyc : ℝ := Q 0 1 * Q 1 2 * Q 2 0

/-- The reversed 3-cycle product `c' = q_13 q_32 q_21`. -/
def cycRev : ℝ := Q 0 2 * Q 2 1 * Q 1 0

/-- The edge product `w_ij = q_ij q_ji`. -/
def wprod (i j : Fin 3) : ℝ := Q i j * Q j i

/-- `σ₃ = q_1 q_2 q_3 - q_1 w_23 - q_2 w_13 - q_3 w_12`, with `q_i = -Q_ii`. -/
def sigma3 : ℝ :=
  (-Q 0 0) * (-Q 1 1) * (-Q 2 2) - (-Q 0 0) * wprod Q 1 2 - (-Q 1 1) * wprod Q 0 2
    - (-Q 2 2) * wprod Q 0 1

/-- `det(-Q) = σ₃ - c - c'` for every `3 × 3` matrix. -/
theorem det_neg_three : (-Q).det = sigma3 Q - cyc Q - cycRev Q := by
  rw [det_neg, det_fin_three]
  simp only [Fintype.card_fin, sigma3, wprod, cyc, cycRev]
  ring

/-- The diagonal of a generator on three states. -/
theorem diag_of_rowsum {Q : Matrix (Fin 3) (Fin 3) ℝ} (h : ∀ i, ∑ j, Q i j = 0) :
    Q 0 0 = -(Q 0 1 + Q 0 2) ∧ Q 1 1 = -(Q 1 0 + Q 1 2) ∧ Q 2 2 = -(Q 2 0 + Q 2 1) := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  simp only [Fin.sum_univ_three] at h0 h1 h2
  refine ⟨by linarith, by linarith, by linarith⟩

/-- `det(-Q) = 0` for a matrix with zero row sums. -/
theorem det_neg_three_eq_zero {Q : Matrix (Fin 3) (Fin 3) ℝ} (h : ∀ i, ∑ j, Q i j = 0) :
    (-Q).det = 0 := by
  obtain ⟨h0, h1, h2⟩ := diag_of_rowsum h
  rw [det_neg_three]
  simp only [sigma3, cyc, cycRev, wprod, h0, h1, h2]
  ring

/-- Remark 3.6 of Paper C2 (`rem:three-states`): `c + c' = σ₃` for a matrix with zero row
sums. -/
theorem cyc_add_cycRev {Q : Matrix (Fin 3) (Fin 3) ℝ} (h : ∀ i, ∑ j, Q i j = 0) :
    cyc Q + cycRev Q = sigma3 Q := by
  have := det_neg_three_eq_zero h
  rw [det_neg_three] at this
  linarith

/-- Remark 3.6 of Paper C2 (`rem:three-states`): `c c' = w_12 w_23 w_13`. -/
theorem cyc_mul_cycRev : cyc Q * cycRev Q = wprod Q 0 1 * wprod Q 1 2 * wprod Q 0 2 := by
  simp only [cyc, cycRev, wprod]
  ring

/-- `σ₃` depends only on the diagonal and the edge products. -/
theorem sigma3_congr {Q Q' : Matrix (Fin 3) (Fin 3) ℝ} (hq : ∀ i, Q' i i = Q i i)
    (hw : ∀ i j, wprod Q' i j = wprod Q i j) : sigma3 Q' = sigma3 Q := by
  simp only [sigma3, hq, hw]

/-- Two generators on three states with positive off-diagonal entries and the same `q_i`,
`w_ij` and `c` are equal (note 06, Corollary 4.2, the case of the same ordered pair). -/
theorem eq_of_same_q_w_cyc {Q Q' : Matrix (Fin 3) (Fin 3) ℝ}
    (hpos : ∀ i j, i ≠ j → 0 < Q i j) (hpos' : ∀ i j, i ≠ j → 0 < Q' i j)
    (hrow : ∀ i, ∑ j, Q i j = 0) (hrow' : ∀ i, ∑ j, Q' i j = 0)
    (hq : ∀ i, Q' i i = Q i i) (hw : ∀ i j, wprod Q' i j = wprod Q i j)
    (hc : cyc Q' = cyc Q) : Q' = Q := by
  have h01 := hpos 0 1 (by decide); have h02 := hpos 0 2 (by decide)
  have h10 := hpos 1 0 (by decide); have h12 := hpos 1 2 (by decide)
  have h20 := hpos 2 0 (by decide); have h21 := hpos 2 1 (by decide)
  have h01' := hpos' 0 1 (by decide); have h02' := hpos' 0 2 (by decide)
  have h10' := hpos' 1 0 (by decide); have h12' := hpos' 1 2 (by decide)
  have h20' := hpos' 2 0 (by decide); have h21' := hpos' 2 1 (by decide)
  have w01 := hw 0 1; have w02 := hw 0 2; have w12 := hw 1 2
  simp only [wprod] at w01 w02 w12
  simp only [cyc] at hc
  -- the potential `p = (1, a'/a, a'e'/(ae))`
  set p : Fin 3 → ℝ := ![1, Q' 0 1 / Q 0 1, Q' 0 1 * Q' 1 2 / (Q 0 1 * Q 1 2)] with hp
  have hp0 : p 0 = 1 := rfl
  have hp1 : p 1 = Q' 0 1 / Q 0 1 := rfl
  have hp2 : p 2 = Q' 0 1 * Q' 1 2 / (Q 0 1 * Q 1 2) := rfl
  -- `Q'_ij p_i = Q_ij p_j` off the diagonal
  have e01 : Q' 0 1 * p 0 = Q 0 1 * p 1 := by rw [hp0, hp1]; field_simp
  have e12 : Q' 1 2 * p 1 = Q 1 2 * p 2 := by rw [hp1, hp2]; field_simp
  have e10 : Q' 1 0 * p 1 = Q 1 0 * p 0 := by
    rw [hp0, hp1]; field_simp; linarith
  have e21 : Q' 2 1 * p 2 = Q 2 1 * p 1 := by
    rw [hp1, hp2]; field_simp
    have : Q' 2 1 * Q' 1 2 = Q 2 1 * Q 1 2 := by linarith
    linear_combination this
  have e20 : Q' 2 0 * p 2 = Q 2 0 * p 0 := by
    rw [hp0, hp2]; field_simp; linear_combination hc
  have e02 : Q' 0 2 * p 0 = Q 0 2 * p 2 := by
    rw [hp0, hp2, mul_one, mul_div_assoc', eq_div_iff (by positivity)]
    have key : (Q' 0 2 * (Q 0 1 * Q 1 2)) * Q' 2 0 = (Q 0 2 * (Q' 0 1 * Q' 1 2)) * Q' 2 0 := by
      linear_combination (Q 0 1 * Q 1 2) * w02 - Q 0 2 * hc
    exact mul_right_cancel₀ h20'.ne' key
  -- `Q p = 0`
  obtain ⟨d0, d1, d2⟩ := diag_of_rowsum hrow'
  have hq0 := hq 0; have hq1 := hq 1; have hq2 := hq 2
  have hQp : Q *ᵥ p = 0 := by
    funext i
    fin_cases i <;> simp only [mulVec, dotProduct, Fin.sum_univ_three, Pi.zero_apply] <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · rw [← e01, ← e02, ← hq0, d0]; ring
    · rw [← e10, ← e12, ← hq1, d1]; ring
    · rw [← e20, ← e21, ← hq2, d2]; ring
  have hQ1 : Q *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    funext i; simpa [mulVec, dotProduct] using hrow i
  have hM : IsMetzler Q := fun i j hij => (hpos i j hij).le
  obtain ⟨κ, hκ⟩ := ker_eq_smul hM (cutIrreducible_of_offdiag_ne fun i j h => (hpos i j h).ne')
    (fun _ => one_pos) hQ1 hQp
  have hpi : ∀ i, p i = 1 := by
    intro i
    have h0 := congrFun hκ 0
    have hi := congrFun hκ i
    simp only [Pi.smul_apply, smul_eq_mul, mul_one] at h0 hi
    rw [hi, ← h0, hp0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · exact hq0
  · simpa [hpi] using e01
  · simpa [hpi] using e02
  · simpa [hpi] using e10
  · exact hq1
  · simpa [hpi] using e12
  · simpa [hpi] using e20
  · simpa [hpi] using e21
  · exact hq2

/-- The time reversal `Q*_ij = π_j Q_ji / π_i`. -/
noncomputable def timeRev (π : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => π j * Q j i / π i

/-- `Q* = D_π⁻¹ Qᵀ D_π`. -/
theorem timeRev_eq_conj (π : Fin 3 → ℝ) :
    timeRev Q π = diagonal (fun i => (π i)⁻¹) * Qᵀ * diagonal π := by
  ext i j
  rw [conj_apply, transpose_apply, timeRev]
  ring

/-- The time reversal has the diagonal of `Q`. -/
theorem timeRev_diag {π : Fin 3 → ℝ} (hπ : ∀ i, 0 < π i) (i : Fin 3) :
    timeRev Q π i i = Q i i := by
  simp only [timeRev]; field_simp [(hπ i).ne']

/-- The time reversal has the edge products of `Q`. -/
theorem timeRev_wprod {π : Fin 3 → ℝ} (hπ : ∀ i, 0 < π i) (i j : Fin 3) :
    wprod (timeRev Q π) i j = wprod Q i j := by
  simp only [wprod, timeRev]
  field_simp [(hπ i).ne', (hπ j).ne']

/-- `c(Q*) = c'(Q)`. -/
theorem cyc_timeRev {π : Fin 3 → ℝ} (hπ : ∀ i, 0 < π i) :
    cyc (timeRev Q π) = cycRev Q := by
  simp only [cyc, cycRev, timeRev]
  field_simp [(hπ 0).ne', (hπ 1).ne', (hπ 2).ne']

/-- With `π` stationary (`π Q = 0`), the time reversal has zero row sums. -/
theorem timeRev_rowsum {π : Fin 3 → ℝ} (hstat : ∀ i, ∑ j, π j * Q j i = 0)
    (i : Fin 3) : ∑ j, timeRev Q π i j = 0 := by
  simp only [timeRev, ← sum_div, hstat i, zero_div]

/-- The time reversal of a generator with positive off-diagonal entries and positive stationary
`π` is a generator with positive off-diagonal entries. -/
theorem timeRev_isGenerator {π : Fin 3 → ℝ} (hπ : ∀ i, 0 < π i)
    (hstat : ∀ i, ∑ j, π j * Q j i = 0) (hpos : ∀ i j, i ≠ j → 0 < Q i j) :
    IsGenerator (timeRev Q π) ∧ ∀ i j, i ≠ j → 0 < timeRev Q π i j :=
  ⟨⟨fun i j hij => (div_pos (mul_pos (hπ j) (hpos j i (Ne.symm hij))) (hπ i)).le,
    timeRev_rowsum Q hstat⟩,
   fun i j hij => div_pos (mul_pos (hπ j) (hpos j i (Ne.symm hij))) (hπ i)⟩

/-- The stationary vector of a three-state generator by the tree formula. -/
def piTree : Fin 3 → ℝ :=
  ![Q 1 0 * Q 2 0 + Q 1 0 * Q 2 1 + Q 1 2 * Q 2 0,
    Q 0 1 * Q 2 1 + Q 0 1 * Q 2 0 + Q 0 2 * Q 2 1,
    Q 0 2 * Q 1 2 + Q 0 2 * Q 1 0 + Q 0 1 * Q 1 2]

theorem piTree_pos {Q : Matrix (Fin 3) (Fin 3) ℝ} (hpos : ∀ i j, i ≠ j → 0 < Q i j) (i : Fin 3) :
    0 < piTree Q i := by
  have h01 := hpos 0 1 (by decide); have h02 := hpos 0 2 (by decide)
  have h10 := hpos 1 0 (by decide); have h12 := hpos 1 2 (by decide)
  have h20 := hpos 2 0 (by decide); have h21 := hpos 2 1 (by decide)
  fin_cases i <;> simp [piTree] <;> positivity

theorem piTree_stationary {Q : Matrix (Fin 3) (Fin 3) ℝ} (hrow : ∀ i, ∑ j, Q i j = 0)
    (i : Fin 3) : ∑ j, piTree Q j * Q j i = 0 := by
  obtain ⟨d0, d1, d2⟩ := diag_of_rowsum hrow
  fin_cases i <;> simp [Fin.sum_univ_three, piTree, d0, d1, d2] <;> ring

/-- Theorem 3.5(d) of Paper C2 (`thm:nonreversible`) and note 06, Corollary 4.2: two
generators on three states with positive off-diagonal entries, the same exit rates `q_i` and the same edge products `w_ij` are
equal or time reversals of each other, `Q* = D_π⁻¹ Qᵀ D_π` for any positive stationary `π`. -/
theorem fiber_three {Q Q' : Matrix (Fin 3) (Fin 3) ℝ}
    (hpos : ∀ i j, i ≠ j → 0 < Q i j) (hpos' : ∀ i j, i ≠ j → 0 < Q' i j)
    (hrow : ∀ i, ∑ j, Q i j = 0) (hrow' : ∀ i, ∑ j, Q' i j = 0)
    (hq : ∀ i, Q' i i = Q i i) (hw : ∀ i j, wprod Q' i j = wprod Q i j)
    {π : Fin 3 → ℝ} (hπ : ∀ i, 0 < π i) (hstat : ∀ i, ∑ j, π j * Q j i = 0) :
    Q' = Q ∨ Q' = timeRev Q π := by
  have hs := cyc_add_cycRev hrow
  have hs' := cyc_add_cycRev hrow'
  have hm := cyc_mul_cycRev Q
  have hm' := cyc_mul_cycRev Q'
  rw [sigma3_congr hq hw] at hs'
  rw [hw, hw, hw] at hm'
  -- `cyc Q'` is a root of `(x - c)(x - c')`
  have hroot : (cyc Q' - cyc Q) * (cyc Q' - cycRev Q) = 0 := by
    have : cycRev Q' = cyc Q + cycRev Q - cyc Q' := by linarith
    rw [this] at hm'
    linear_combination -hm' + hm
  rcases mul_eq_zero.mp hroot with h | h
  · left
    exact eq_of_same_q_w_cyc hpos hpos' hrow hrow' hq hw (by linarith)
  · right
    obtain ⟨⟨_, hrowR⟩, hposR⟩ := timeRev_isGenerator Q hπ hstat hpos
    refine eq_of_same_q_w_cyc hposR hpos' hrowR hrow' (fun i => ?_) (fun i j => ?_) ?_
    · rw [hq, timeRev_diag Q hπ]
    · rw [hw, timeRev_wprod Q hπ]
    · rw [cyc_timeRev Q hπ]; linarith

/-- The same with the tree-formula stationary vector, with no hypothesis on `π`. -/
theorem fiber_three_tree {Q Q' : Matrix (Fin 3) (Fin 3) ℝ}
    (hpos : ∀ i j, i ≠ j → 0 < Q i j) (hpos' : ∀ i j, i ≠ j → 0 < Q' i j)
    (hrow : ∀ i, ∑ j, Q i j = 0) (hrow' : ∀ i, ∑ j, Q' i j = 0)
    (hq : ∀ i, Q' i i = Q i i) (hw : ∀ i j, wprod Q' i j = wprod Q i j) :
    Q' = Q ∨ Q' = timeRev Q (piTree Q) :=
  fiber_three hpos hpos' hrow hrow' hq hw (piTree_pos hpos) (piTree_stationary hrow)

/-- Conversely, the time reversal has the same `q_i` and `w_ij`, and is a generator. -/
theorem fiber_three_converse {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hpos : ∀ i j, i ≠ j → 0 < Q i j) {π : Fin 3 → ℝ} (hπ : ∀ i, 0 < π i)
    (hstat : ∀ i, ∑ j, π j * Q j i = 0) :
    IsGenerator (timeRev Q π) ∧ (∀ i, timeRev Q π i i = Q i i) ∧
      (∀ i j, wprod (timeRev Q π) i j = wprod Q i j) :=
  ⟨(timeRev_isGenerator Q hπ hstat hpos).1, timeRev_diag Q hπ, timeRev_wprod Q hπ⟩

end Three

end Kagey131.PaperC
