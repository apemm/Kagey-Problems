import Mathlib
import PaperC.GeneratorFiber
import PaperC.C2.TimeReversal

/-!
# Paper C2: gluing across a cut and the balance criterion

Paper C2 (`paperC2/sec_exactlaw.tex`), Section "Cuts, balanced sides and memoryless blocks":
Proposition `prop:gluing` (the formulas for `F_Q` and `F_Q - F_{Q'}`), Corollary `cor:balance`
(the algebraic direction), and the computation of Remark `rem:memoryless-cut`.

Notation of the paper, over a field `K`. For a cut `X ∪ Y`, `M = diag x - Q` has blocks `M_X`,
`M_Y` and off-diagonal blocks `-a bᵀ` and `-c uᵀ`; `R_X`, `R_Y` are the inverses of `M_X`,
`M_Y`. The scalars are `p₁ = π_X R_X a`, `p₂ = uᵀ R_X 1`, `α = uᵀ R_X a`, `E_X = π_X R_X 1`,
`q₁ = bᵀ R_Y 1`, `q₂ = π_Y R_Y c`, `β = bᵀ R_Y c`, `E_Y = π_Y R_Y 1`.

* `glue_solution`: if `M z = 1` and `1 - αβ ≠ 0`, then
  `π z = E_X + E_Y + (p₁q₁ + p₂q₂ + α q₁q₂ + β p₁p₂)/(1 - αβ)` (the first formula of
  `prop:gluing`, which is `F_Q = π (diag x - Q)⁻¹ 1` at a point `x`);
* `starBlock`, `starBlock_eq`: the block `M'_Y = D_Y⁻¹ M_Yᵀ D_Y` of the cut-transposed generator
  point is `diag x - Q*_Y`, and its inverse is `D_Y⁻¹ R_Yᵀ D_Y`;
* `glue_difference`: for `Q'` with blocks `M_X`, `-a (D_Y c)ᵀ`, `-(D_Y⁻¹ b) uᵀ`, `M'_Y`,
  `F_Q - F_{Q'} = (p₁ - p₂)(q₁ - q₂)/(1 - αβ)` (the second formula of `prop:gluing`);
* `glue_eq_iff`, `glue_eq_of_balanced`: `F_Q = F_{Q'}` exactly when `(p₁-p₂)(q₁-q₂) = 0` at the
  point, so a balanced side (`p₁ = p₂` or `q₁ = q₂`) gives the same value (the algebraic part of
  `cor:balance`; the passage from points to rational functions is the integral domain property);
* `p1_eq_p2_memoryless`: with `a = 1` and `u = π_X` one has `p₁ = p₂` (`rem:memoryless-cut`).
-/

namespace Kagey131.PaperC.C2

open Matrix Finset

set_option linter.unusedSectionVars false

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {K : Type*} [Field K]

section Scalars

variable (RX : Matrix X X K) (RY : Matrix Y Y K) (πX : X → K) (πY : Y → K)
  (a u : X → K) (b c : Y → K)

/-- `p₁ = π_X R_X a`. -/
def gp1 : K := πX ⬝ᵥ (RX *ᵥ a)
/-- `p₂ = uᵀ R_X 1`. -/
def gp2 : K := u ⬝ᵥ (RX *ᵥ fun _ => 1)
/-- `α = uᵀ R_X a`. -/
def galpha : K := u ⬝ᵥ (RX *ᵥ a)
/-- `E_X = π_X R_X 1`. -/
def gEX : K := πX ⬝ᵥ (RX *ᵥ fun _ => 1)
/-- `q₁ = bᵀ R_Y 1`. -/
def gq1 : K := b ⬝ᵥ (RY *ᵥ fun _ => 1)
/-- `q₂ = π_Y R_Y c`. -/
def gq2 : K := πY ⬝ᵥ (RY *ᵥ c)
/-- `β = bᵀ R_Y c`. -/
def gbeta : K := b ⬝ᵥ (RY *ᵥ c)
/-- `E_Y = π_Y R_Y 1`. -/
def gEY : K := πY ⬝ᵥ (RY *ᵥ fun _ => 1)

/-- The right side of the first formula of `prop:gluing`. -/
def gluedF (E_X E_Y p₁ p₂ α q₁ q₂ β : K) : K :=
  E_X + E_Y + (p₁ * q₁ + p₂ * q₂ + α * q₁ * q₂ + β * p₁ * p₂) / (1 - α * β)

end Scalars

/-- `prop:gluing`, first formula: the solution of `M z = 1` for the cut matrix has
`π z = E_X + E_Y + (p₁q₁ + p₂q₂ + αq₁q₂ + βp₁p₂)/(1 - αβ)`. -/
theorem glue_solution (MX : Matrix X X K) (MY : Matrix Y Y K) (RX : Matrix X X K)
    (RY : Matrix Y Y K) (hX : RX * MX = 1) (hY : RY * MY = 1) (πX : X → K) (πY : Y → K)
    (a u : X → K) (b c : Y → K) (z : X ⊕ Y → K)
    (hz : fromBlocks MX (-(vecMulVec a b)) (-(vecMulVec c u)) MY *ᵥ z = fun _ => 1)
    (hden : 1 - galpha RX a u * gbeta RY b c ≠ 0) :
    πX ⬝ᵥ (fun x => z (Sum.inl x)) + πY ⬝ᵥ (fun y => z (Sum.inr y))
      = gluedF (gEX RX πX) (gEY RY πY) (gp1 RX πX a) (gp2 RX u) (galpha RX a u)
          (gq1 RY b) (gq2 RY πY c) (gbeta RY b c) := by
  set zX : X → K := fun x => z (Sum.inl x) with hzX
  set zY : Y → K := fun y => z (Sum.inr y) with hzY
  have hz' : z = Sum.elim zX zY := by
    funext i; rcases i with i | i <;> rfl
  rw [hz', fromBlocks_mulVec] at hz
  have h1 : MX *ᵥ zX - (b ⬝ᵥ zY) • a = fun _ => 1 := by
    have := congrFun hz
    funext x
    have hx := this (Sum.inl x)
    simp only [Sum.elim_inl, Pi.add_apply] at hx
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hx]
    simp [Matrix.neg_mulVec, vecMulVec_mulVec]
    ring
  have h2 : MY *ᵥ zY - (u ⬝ᵥ zX) • c = fun _ => 1 := by
    have := congrFun hz
    funext y
    have hy := this (Sum.inr y)
    simp only [Sum.elim_inr, Pi.add_apply] at hy
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hy]
    simp [Matrix.neg_mulVec, vecMulVec_mulVec]
    ring
  set s : K := b ⬝ᵥ zY with hs
  set t : K := u ⬝ᵥ zX with ht
  have hzX' : zX = RX *ᵥ (fun _ => 1) + s • (RX *ᵥ a) := by
    have : MX *ᵥ zX = (fun _ => 1) + s • a := by
      rw [← h1]; abel
    calc zX = (RX * MX) *ᵥ zX := by rw [hX, one_mulVec]
      _ = RX *ᵥ (MX *ᵥ zX) := by rw [mulVec_mulVec]
      _ = _ := by rw [this, mulVec_add, mulVec_smul]
  have hzY' : zY = RY *ᵥ (fun _ => 1) + t • (RY *ᵥ c) := by
    have : MY *ᵥ zY = (fun _ => 1) + t • c := by
      rw [← h2]; abel
    calc zY = (RY * MY) *ᵥ zY := by rw [hY, one_mulVec]
      _ = RY *ᵥ (MY *ᵥ zY) := by rw [mulVec_mulVec]
      _ = _ := by rw [this, mulVec_add, mulVec_smul]
  have ht' : t = gp2 RX u + galpha RX a u * s := by
    rw [ht, hzX', dotProduct_add, dotProduct_smul, smul_eq_mul]; simp only [gp2, galpha]; ring
  have hs' : s = gq1 RY b + gbeta RY b c * t := by
    rw [hs, hzY', dotProduct_add, dotProduct_smul, smul_eq_mul]; simp only [gq1, gbeta]; ring
  have hsol_s : s * (1 - galpha RX a u * gbeta RY b c)
      = gq1 RY b + gbeta RY b c * gp2 RX u := by
    rw [ht'] at hs'; linear_combination hs'
  have hsol_t : t * (1 - galpha RX a u * gbeta RY b c)
      = gp2 RX u + galpha RX a u * gq1 RY b := by
    rw [hs'] at ht'; linear_combination ht'
  have hF : πX ⬝ᵥ zX + πY ⬝ᵥ zY = gEX RX πX + gEY RY πY + s * gp1 RX πX a + t * gq2 RY πY c := by
    rw [hzX', hzY', dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp only [gEX, gEY, gp1, gq2, smul_eq_mul]; ring
  rw [hF]
  have e1 : s = (gq1 RY b + gbeta RY b c * gp2 RX u) / (1 - galpha RX a u * gbeta RY b c) := by
    rw [eq_div_iff hden]; exact hsol_s
  have e2 : t = (gp2 RX u + galpha RX a u * gq1 RY b) / (1 - galpha RX a u * gbeta RY b c) := by
    rw [eq_div_iff hden]; exact hsol_t
  rw [e1, e2, gluedF]
  field_simp
  ring


/-- The block `M'_Y = D_Y⁻¹ M_Yᵀ D_Y` of the cut-transposed generator point. -/
def starBlock (πY : Y → K) (M : Matrix Y Y K) : Matrix Y Y K :=
  Matrix.of fun i j => (πY i)⁻¹ * M j i * πY j

/-- `starBlock` of an inverse is the inverse of `starBlock`. -/
theorem starBlock_mul (πY : Y → K) (hπ : ∀ i, πY i ≠ 0) (R M : Matrix Y Y K) (h : R * M = 1) :
    starBlock πY R * starBlock πY M = 1 := by
  have h' : M * R = 1 := mul_eq_one_comm.mp h
  ext i j
  simp only [Matrix.mul_apply, starBlock, of_apply]
  have : ∀ k, (πY i)⁻¹ * R k i * πY k * ((πY k)⁻¹ * M j k * πY j)
      = (πY i)⁻¹ * πY j * (M j k * R k i) := fun k => by
    have := hπ k
    field_simp
  simp only [this, ← Finset.mul_sum]
  have h2 : ∑ k, M j k * R k i = (M * R) j i := rfl
  rw [h2, h']
  by_cases hij : i = j
  · subst hij; have := hπ i; simp; field_simp
  · simp [Matrix.one_apply_ne hij, Ne.symm hij]

omit [Fintype Y] in
/-- Over `ℝ`, `starBlock` of `diag x - Q_Y` is `diag x - Q*_Y`. -/
theorem starBlock_eq (πY : Y → ℝ) (hπ : ∀ i, πY i ≠ 0) (x : Y → ℝ) (QY : Matrix Y Y ℝ) :
    starBlock πY (diagonal x - QY) = diagonal x - starMat πY QY := by
  ext i j
  have := hπ i
  by_cases hij : i = j
  · subst hij; simp [starBlock, starMat]; field_simp
  · simp [starBlock, starMat, diagonal_apply_ne _ hij, diagonal_apply_ne _ (Ne.symm hij)]
    field_simp

section Quantities

variable (RY : Matrix Y Y K) (πY : Y → K) (b c : Y → K)

/-- For the cut-transposed generator point the factors are `(a, D_Y c, D_Y⁻¹ b, u)` and the block
`D_Y⁻¹ R_Yᵀ D_Y`; then `q₁` and `q₂` are exchanged. -/
theorem star_q1 (hπ : ∀ i, πY i ≠ 0) : gq1 (starBlock πY RY) (fun i => πY i * c i) = gq2 RY πY c := by
  simp only [gq1, gq2, dotProduct, mulVec, starBlock, of_apply, mul_one, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  have := hπ i
  field_simp

theorem star_q2 (hπ : ∀ i, πY i ≠ 0) : gq2 (starBlock πY RY) πY (fun i => (πY i)⁻¹ * b i) = gq1 RY b := by
  simp only [gq1, gq2, dotProduct, mulVec, starBlock, of_apply, mul_one, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  have := hπ i
  have := hπ j
  field_simp

theorem star_beta (hπ : ∀ i, πY i ≠ 0) : gbeta (starBlock πY RY) (fun i => πY i * c i) (fun i => (πY i)⁻¹ * b i)
    = gbeta RY b c := by
  simp only [gbeta, dotProduct, mulVec, starBlock, of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  have := hπ i
  have := hπ j
  field_simp

theorem star_EY (hπ : ∀ i, πY i ≠ 0) : gEY (starBlock πY RY) πY = gEY RY πY := by
  simp only [gEY, dotProduct, mulVec, starBlock, of_apply, mul_one, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  have := hπ i
  field_simp

end Quantities

/-- `prop:gluing`, second formula: `F_Q - F_{Q'} = (p₁ - p₂)(q₁ - q₂)/(1 - αβ)`, where `Q'` has the
blocks `M_X`, `-a (D_Y c)ᵀ`, `-(D_Y⁻¹ b) uᵀ` and `M'_Y = D_Y⁻¹ M_Yᵀ D_Y`. -/
theorem glue_difference (MX : Matrix X X K) (MY : Matrix Y Y K) (RX : Matrix X X K)
    (RY : Matrix Y Y K) (hX : RX * MX = 1) (hY : RY * MY = 1) (πX : X → K) (πY : Y → K)
    (hπ : ∀ i, πY i ≠ 0) (a u : X → K) (b c : Y → K) (z z' : X ⊕ Y → K)
    (hz : fromBlocks MX (-(vecMulVec a b)) (-(vecMulVec c u)) MY *ᵥ z = fun _ => 1)
    (hz' : fromBlocks MX (-(vecMulVec a (fun i => πY i * c i)))
        (-(vecMulVec (fun i => (πY i)⁻¹ * b i) u)) (starBlock πY MY) *ᵥ z' = fun _ => 1)
    (hden : 1 - galpha RX a u * gbeta RY b c ≠ 0) :
    (πX ⬝ᵥ (fun x => z (Sum.inl x)) + πY ⬝ᵥ (fun y => z (Sum.inr y)))
      - (πX ⬝ᵥ (fun x => z' (Sum.inl x)) + πY ⬝ᵥ (fun y => z' (Sum.inr y)))
    = (gp1 RX πX a - gp2 RX u) * (gq1 RY b - gq2 RY πY c) / (1 - galpha RX a u * gbeta RY b c) := by
  rw [glue_solution MX MY RX RY hX hY πX πY a u b c z hz hden]
  rw [glue_solution MX (starBlock πY MY) RX (starBlock πY RY) hX
    (starBlock_mul πY hπ RY MY hY) πX πY a u (fun i => πY i * c i)
    (fun i => (πY i)⁻¹ * b i) z' hz' (by rw [star_beta RY πY b c hπ]; exact hden)]
  rw [star_q1 RY πY c hπ, star_q2 RY πY b hπ, star_beta RY πY b c hπ, star_EY RY πY hπ]
  simp only [gluedF]
  field_simp
  ring

/-- The two values agree exactly when `(p₁ - p₂)(q₁ - q₂) = 0` (the algebraic part of
`cor:balance`, at a point where `1 - αβ ≠ 0`). -/
theorem glue_eq_iff (p₁ p₂ q₁ q₂ d : K) (hd : d ≠ 0) :
    (p₁ - p₂) * (q₁ - q₂) / d = 0 ↔ p₁ = p₂ ∨ q₁ = q₂ := by
  rw [div_eq_zero_iff, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  simp [hd]

/-- A balanced side (`p₁ = p₂`, or `q₁ = q₂` for `Y`) gives the same value for `Q` and `Q'`. -/
theorem glue_eq_of_balanced (MX : Matrix X X K) (MY : Matrix Y Y K) (RX : Matrix X X K)
    (RY : Matrix Y Y K) (hX : RX * MX = 1) (hY : RY * MY = 1) (πX : X → K) (πY : Y → K)
    (hπ : ∀ i, πY i ≠ 0) (a u : X → K) (b c : Y → K) (z z' : X ⊕ Y → K)
    (hz : fromBlocks MX (-(vecMulVec a b)) (-(vecMulVec c u)) MY *ᵥ z = fun _ => 1)
    (hz' : fromBlocks MX (-(vecMulVec a (fun i => πY i * c i)))
        (-(vecMulVec (fun i => (πY i)⁻¹ * b i) u)) (starBlock πY MY) *ᵥ z' = fun _ => 1)
    (hden : 1 - galpha RX a u * gbeta RY b c ≠ 0)
    (hbal : gp1 RX πX a = gp2 RX u ∨ gq1 RY b = gq2 RY πY c) :
    (πX ⬝ᵥ (fun x => z (Sum.inl x)) + πY ⬝ᵥ (fun y => z (Sum.inr y)))
      = (πX ⬝ᵥ (fun x => z' (Sum.inl x)) + πY ⬝ᵥ (fun y => z' (Sum.inr y))) := by
  have h := glue_difference MX MY RX RY hX hY πX πY hπ a u b c z z' hz hz' hden
  have h0 : (gp1 RX πX a - gp2 RX u) * (gq1 RY b - gq2 RY πY c)
      / (1 - galpha RX a u * gbeta RY b c) = 0 := (glue_eq_iff _ _ _ _ _ hden).mpr hbal
  rw [h0] at h
  exact sub_eq_zero.mp h

/-- `rem:memoryless-cut`: for the factors `a = 1`, `u = π_X` of a memoryless block, `p₁ = p₂`. -/
theorem p1_eq_p2_memoryless (RX : Matrix X X K) (πX : X → K) :
    gp1 RX πX (fun _ => 1) = gp2 RX πX := rfl

end Kagey131.PaperC.C2
