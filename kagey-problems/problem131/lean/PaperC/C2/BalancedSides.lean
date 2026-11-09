import Mathlib
import PaperC.C2.HidingTimeReversal

/-!
# Paper C2: balanced sides and one cut (Section `sec:law-balanced`)

Paper C2 (`paperC2/sec_exactlaw.tex`): the algebraic parts of `thm:balanced` and `cor:one-cut`.

* `Gshift`, `Gshift_rowsum`, `Gshift_colsum`, `flux_Gshift`, `shift_identity`, `balanced_flux`
  (`thm:balanced`): for `Q_X 1 = -λ a` and `π_X Q_X = -λ (π_X∘a)`, the matrix
  `G = Q_X + λ diag a` has `G 1 = 0` and `π_X G = 0`, the same flux matrix as `Q_X`, and
  `diag x - Q_X = diag(x + λ a) - G`; and `p_1 - p_2 = π·v - (π∘a)·u = uᵀ Φ v` (`flux_form`).
  Here `Q_X` is a matrix on its own index type.
* `memoryless_star`, `starMat_blockRev`, `blockRev_comm`, `memoryless_union`
  (`thm:balanced`, `cor:one-cut`): a memoryless block of `Q` is one of `Q*`; `(Q^{[B]})* =
  (Q*)^{[B]}`; reversals of disjoint blocks commute; the union of two memoryless blocks that
  meet is memoryless when it is not everything (and the exit rate out of it is positive, which
  follows from irreducibility).
* `cutGenX`, `cutGenY`, `starMat_cutGenX`, `starMat_cutGenX_off`, `starMat_cutGenX_XX` (`cor:one-cut`):
  the generator point `Q'` across `X` from `prop:gluing` has the time reversal `Q''`, the
  generator point across `Y`; and for `u = D_X a` the time reversal agrees with `Q` off `X × X`
  and equals `Q*_X` on `X × X`.

The statements that need the merging of overlapping blocks into disjoint ones, the splitting into
closed classes of `G`, and the identification with `Q^{[B_1]…[B_r]}` are not formalized.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Kagey131.PaperC

section Shift

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `G = Q_X + λ diag a`. -/
def Gshift (Qx : Matrix ι ι ℝ) (lam : ℝ) (a : ι → ℝ) : Matrix ι ι ℝ := Qx + lam • diagonal a

theorem Gshift_rowsum {Qx : Matrix ι ι ℝ} {lam : ℝ} {a : ι → ℝ}
    (h : ∀ i, ∑ j, Qx i j = -lam * a i) (i : ι) : ∑ j, Gshift Qx lam a i j = 0 := by
  simp only [Gshift, Matrix.add_apply, Matrix.smul_apply, diagonal_apply, smul_eq_mul,
    Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, h i]
  ring

theorem Gshift_colsum {Qx : Matrix ι ι ℝ} {lam : ℝ} {a π : ι → ℝ}
    (h : ∀ j, ∑ i, π i * Qx i j = -lam * (π j * a j)) (j : ι) :
    ∑ i, π i * Gshift Qx lam a i j = 0 := by
  simp only [Gshift, Matrix.add_apply, Matrix.smul_apply, diagonal_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, h j]
  have : ∑ i, π i * (lam * if i = j then a i else 0) = lam * (π j * a j) := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]; ring
  rw [this]; ring

/-- The diagonal does not enter the flux matrix. -/
theorem flux_Gshift (π : ι → ℝ) (Qx : Matrix ι ι ℝ) (lam : ℝ) (a : ι → ℝ) :
    flux π (Gshift Qx lam a) = flux π Qx := by
  ext i j
  rw [flux_apply, flux_apply]
  by_cases h : i = j
  · subst h; ring
  · simp [Gshift, diagonal_apply, h, Ne.symm h]

/-- `diag x - Q_X = diag(x + λ a) - G`. -/
theorem shift_identity (Qx : Matrix ι ι ℝ) (lam : ℝ) (a x : ι → ℝ) :
    diagonal x - Qx = diagonal (fun i => x i + lam * a i) - Gshift Qx lam a := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Gshift, diagonal_apply]
  · simp [Gshift, diagonal_apply, h]

/-- **`thm:balanced`.** `p_1 - p_2 = π·v - (π∘a)·u = uᵀ Φ_G v`, where `u`, `v` solve the system of
`G` at `x + λ a` with the right-hand sides `1` and `a`. -/
theorem balanced_flux {Qx : Matrix ι ι ℝ} {lam : ℝ} {π a x u v : ι → ℝ}
    (hu : ∀ i, (x i + lam * a i) * u i - (Gshift Qx lam a *ᵥ u) i = 1)
    (hv : ∀ i, (x i + lam * a i) * v i - (Gshift Qx lam a *ᵥ v) i = a i) :
    π ⬝ᵥ v - (π * a) ⬝ᵥ u = u ⬝ᵥ (flux π Qx *ᵥ v) := by
  rw [← flux_Gshift π Qx lam a]
  exact flux_form hu hv

end Shift

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ} {π : ι → ℝ} {B : Finset ι}

/-- A memoryless block of `Q` is a memoryless block of `Q*`, with the same `κ`. -/
theorem memoryless_star {κ : ℝ} {ν c : ι → ℝ} (h : Memoryless Q π B κ ν c) (hκ : κ ≠ 0) :
    Memoryless (starMat π Q) π B κ (fun y => π y * c y / (κ * ∑ j ∈ B, π j))
      (fun y => (∑ j ∈ B, π j) * κ * ν y / π y) := by
  have hB := h.sumB_pos.ne'
  have hpi := fun i => (h.pos i).ne'
  have hstat' : ∀ j, ∑ i, π i * starMat π Q i j = 0 := by
    intro j
    have : ∀ i, π i * starMat π Q i j = π j * Q j i := fun i => by
      simp only [starMat]; field_simp [hpi i]
    simp only [this, ← Finset.mul_sum, h.gen.2 j, mul_zero]
  refine ⟨h.pos, starMat_isGenerator h.pos h.gen ?_, hstat', ?_, ?_, ?_, h.nonempty⟩
  · ext j
    simpa [vecMul, dotProduct] using h.stat j
  · intro i hi y hy
    simp only [starMat, h.inn y hy i hi]
    field_simp [hpi i]
  · rw [← Finset.sum_div, ← flux_balance h]
    exact div_self (mul_ne_zero hκ hB)
  · intro y hy i hi
    simp only [starMat, h.out i hi y hy]
    field_simp

/-- `(Q^{[B]})* = (Q*)^{[B]}`. -/
theorem starMat_blockRev (hπ : ∀ i, π i ≠ 0) (B : Finset ι) (Q : Matrix ι ι ℝ) :
    starMat π (blockRev B π Q) = blockRev B π (starMat π Q) := by
  ext i j
  by_cases h : i ∈ B ∧ j ∈ B
  · have h' : j ∈ B ∧ i ∈ B := ⟨h.2, h.1⟩
    simp only [starMat, blockRev, h, h', and_self, if_true]
    try field_simp [hπ i, hπ j]
  · have h' : ¬ (j ∈ B ∧ i ∈ B) := fun e => h ⟨e.2, e.1⟩
    simp only [starMat, blockRev, h, h', if_false]

/-- Reversals of disjoint blocks commute. -/
theorem blockRev_comm {B₁ B₂ : Finset ι} (hdis : Disjoint B₁ B₂) (Q : Matrix ι ι ℝ) :
    blockRev B₁ π (blockRev B₂ π Q) = blockRev B₂ π (blockRev B₁ π Q) := by
  ext i j
  by_cases h1 : i ∈ B₁ ∧ j ∈ B₁
  · have n2 : ¬ (i ∈ B₂ ∧ j ∈ B₂) := fun h => Finset.disjoint_left.mp hdis h1.1 h.1
    have n2' : ¬ (j ∈ B₂ ∧ i ∈ B₂) := fun h => Finset.disjoint_left.mp hdis h1.2 h.1
    simp only [blockRev, h1, n2, n2', and_self, if_true, if_false]
  · by_cases h2 : i ∈ B₂ ∧ j ∈ B₂
    · have n1' : ¬ (j ∈ B₁ ∧ i ∈ B₁) := fun h => Finset.disjoint_left.mp hdis h.1 h2.2
      simp only [blockRev, h1, h2, n1', and_self, if_true, if_false]
    · simp only [blockRev, h1, h2, if_false]

/-- The union of two memoryless blocks that meet is a memoryless block, when it is not
everything (`CutIrreducible` makes the exit rate positive). -/
theorem memoryless_union {B₁ B₂ : Finset ι} {κ₁ κ₂ : ℝ} {ν₁ ν₂ c₁ c₂ : ι → ℝ}
    (h1 : Memoryless Q π B₁ κ₁ ν₁ c₁) (h2 : Memoryless Q π B₂ κ₂ ν₂ c₂)
    (hmeet : (B₁ ∩ B₂).Nonempty) (hirr : CutIrreducible Q) (hne : B₁ ∪ B₂ ≠ univ) :
    ∃ κ ν c, Memoryless Q π (B₁ ∪ B₂) κ ν c := by
  obtain ⟨i0, hi0⟩ := hmeet
  have hi1 : i0 ∈ B₁ := (Finset.mem_inter.mp hi0).1
  have hi2 : i0 ∈ B₂ := (Finset.mem_inter.mp hi0).2
  have hout : ∀ i ∈ B₁ ∪ B₂, ∀ y ∉ B₁ ∪ B₂, Q i y = Q i0 y := by
    intro i hi y hy
    have hy1 : y ∉ B₁ := fun e => hy (Finset.mem_union_left _ e)
    have hy2 : y ∉ B₂ := fun e => hy (Finset.mem_union_right _ e)
    rcases Finset.mem_union.mp hi with hi | hi
    · rw [h1.out i hi y hy1, h1.out i0 hi1 y hy1]
    · rw [h2.out i hi y hy2, h2.out i0 hi2 y hy2]
  set U := B₁ ∪ B₂ with hU
  have hnn : ∀ y ∈ Uᶜ, 0 ≤ Q i0 y := fun y hy =>
    h1.gen.1 i0 y (fun e => (mem_compl.mp hy) (e ▸ Finset.mem_union_left _ hi1))
  obtain ⟨i1, hi1U, j1, hj1, hnz⟩ := hirr U ⟨i0, Finset.mem_union_left _ hi1⟩ hne
  have hκ : 0 < ∑ y ∈ Uᶜ, Q i0 y := by
    have h3 : Q i1 j1 = Q i0 j1 := hout i1 hi1U j1 hj1
    have hpos : 0 < Q i0 j1 := by
      have := h1.gen.1 i1 j1 (fun e => hj1 (e ▸ hi1U))
      rw [← h3]; exact lt_of_le_of_ne this (Ne.symm hnz)
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun y => Q i0 y) hnn
      (mem_compl.mpr hj1))
  have hp := (h1.pos i0).ne'
  have hS1 := h1.sumB_pos.ne'
  have hS2 := h2.sumB_pos.ne'
  have hSU : (∑ j ∈ U, π j) ≠ 0 :=
    (Finset.sum_pos (fun j _ => h1.pos j) ⟨i0, Finset.mem_union_left _ hi1⟩).ne'
  have hrat : ∀ y ∉ U, c₂ y / ∑ j ∈ B₂, π j = c₁ y / ∑ j ∈ B₁, π j := by
    intro y hy
    have hy1 : y ∉ B₁ := fun e => hy (Finset.mem_union_left _ e)
    have hy2 : y ∉ B₂ := fun e => hy (Finset.mem_union_right _ e)
    have e := (h1.inn y hy1 i0 hi1).symm.trans (h2.inn y hy2 i0 hi2)
    calc c₂ y / ∑ j ∈ B₂, π j = (c₂ y * π i0 / ∑ j ∈ B₂, π j) / π i0 := by field_simp
      _ = (c₁ y * π i0 / ∑ j ∈ B₁, π j) / π i0 := by rw [e]
      _ = c₁ y / ∑ j ∈ B₁, π j := by field_simp
  refine ⟨∑ y ∈ Uᶜ, Q i0 y, fun y => Q i0 y / ∑ y ∈ Uᶜ, Q i0 y,
    fun y => (∑ j ∈ U, π j) * (c₁ y / ∑ j ∈ B₁, π j), ?_⟩
  refine ⟨h1.pos, h1.gen, h1.stat, ?_, ?_, ?_, ⟨i0, Finset.mem_union_left _ hi1⟩⟩
  · intro i hi y hy
    rw [hout i hi y hy]; field_simp
  · rw [← Finset.sum_div]; exact div_self hκ.ne'
  · intro y hy i hi
    have hy1 : y ∉ B₁ := fun e => hy (Finset.mem_union_left _ e)
    have hy2 : y ∉ B₂ := fun e => hy (Finset.mem_union_right _ e)
    rcases Finset.mem_union.mp hi with hi | hi
    · rw [h1.inn y hy1 i hi]; field_simp
    · rw [h2.inn y hy2 i hi]
      calc c₂ y * π i / ∑ j ∈ B₂, π j = (c₂ y / ∑ j ∈ B₂, π j) * π i := by ring
        _ = (c₁ y / ∑ j ∈ B₁, π j) * π i := by rw [hrat y hy]
        _ = _ := by field_simp

end Blocks

/-! ### One cut -/

section OneCut

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The generator point `Q'` across `X` (`prop:gluing`): `Q'_X = Q_X`, `Q'[X,Y] = a (D_Y c)ᵀ`,
`Q'[Y,X] = D_Y⁻¹ b uᵀ`, `Q'_Y = Q*_Y`. -/
noncomputable def cutGenX (X : Finset ι) (π a b c u : ι → ℝ) (Q : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => if i ∈ X then (if j ∈ X then Q i j else a i * (π j * c j))
    else (if j ∈ X then b i * u j / π i else π j * Q j i / π i)

/-- The generator point `Q''` across `Y`: `Q''_Y = Q_Y`, `Q''_X = Q*_X`,
`Q''[X,Y] = D_X⁻¹ u bᵀ`, `Q''[Y,X] = c (D_X a)ᵀ`. -/
noncomputable def cutGenY (X : Finset ι) (π a b c u : ι → ℝ) (Q : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => if i ∈ X then (if j ∈ X then π j * Q j i / π i else u i * b j / π i)
    else (if j ∈ X then c i * (π j * a j) else Q i j)

/-- **`cor:one-cut`.** The time reversal of `Q'` is `Q''`. -/
theorem starMat_cutGenX (hπ : ∀ i, π i ≠ 0) (X : Finset ι) (a b c u : ι → ℝ)
    (Q : Matrix ι ι ℝ) :
    starMat π (cutGenX X π a b c u Q) = cutGenY X π a b c u Q := by
  ext i j
  by_cases hi : i ∈ X <;> by_cases hj : j ∈ X <;>
    simp only [starMat, cutGenX, cutGenY, hi, hj, if_true, if_false] <;> field_simp [hπ i, hπ j]

variable {π : ι → ℝ} {X : Finset ι} {a b c u : ι → ℝ} {Q : Matrix ι ι ℝ}

/-- **`cor:one-cut`.** For `u = D_X a`, `(Q')*` agrees with `Q` off `X × X`. -/
theorem starMat_cutGenX_off (hπ : ∀ i, π i ≠ 0) (hu : ∀ i ∈ X, u i = π i * a i)
    (hXY : ∀ i ∈ X, ∀ y ∉ X, Q i y = a i * b y) (hYX : ∀ y ∉ X, ∀ i ∈ X, Q y i = c y * u i)
    (i j : ι) (h : ¬ (i ∈ X ∧ j ∈ X)) : starMat π (cutGenX X π a b c u Q) i j = Q i j := by
  rw [starMat_cutGenX hπ]
  by_cases hi : i ∈ X
  · have hj : j ∉ X := fun e => h ⟨hi, e⟩
    simp only [cutGenY, hi, hj, if_true, if_false, hu i hi, hXY i hi j hj]
    field_simp [hπ i]
  · by_cases hj : j ∈ X
    · simp only [cutGenY, hi, hj, if_true, if_false, hYX i hi j hj, hu j hj]
    · simp only [cutGenY, hi, hj, if_false]

/-- **`cor:one-cut`.** On `X × X`, `(Q')*` is `Q*_X`. -/
theorem starMat_cutGenX_XX (hπ : ∀ i, π i ≠ 0) {i j : ι} (hi : i ∈ X) (hj : j ∈ X) :
    starMat π (cutGenX X π a b c u Q) i j = starMat π Q i j := by
  rw [starMat_cutGenX hπ]
  simp only [cutGenY, starMat, hi, hj, if_true]

end OneCut

end Kagey131.PaperC.C2
