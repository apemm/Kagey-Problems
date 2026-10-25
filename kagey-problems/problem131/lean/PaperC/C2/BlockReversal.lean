import Mathlib
import PaperC.C2.BlockSegment

/-!
# Paper C2: reversal of a memoryless block

Material headed for Paper C2, not yet labelled in the paper (research note `Paper C2 identifiability O1`, Theorem 6 and
Corollary 7; no label in the paper yet). Let `B` be a set of states and `w ≠ 0` on `B`. Suppose
every state of `B` has the same exit row outside `B`, every state outside `B` enters `B`
proportionally to `w`, and the start is proportional to `w` on `B`. Then replacing the block
`P_BB` by `W⁻¹ P_BBᵀ W` (the reversal of the block) does not change the weighted path sums
`μ Z (P Z)^N 1`, for any weights `z`, any `N`, and any matrix `P` (stochasticity is not used).

* `seg_reverse`: the segment sums agree, `wᵀ Z (W⁻¹ Pᵀ W Z)^k 1 = wᵀ Z (P Z)^k 1`;
* `segSum_eq_sub`: the masked segment sums of `BlockSegment` are the segment sums of the
  principal submatrix on `B`;
* `blockRev`: the matrix `P` with `P_BB` replaced by `w_j P_ji / w_i`;
* `memoryless_block_reversal`: the weighted path sums of `P` and `blockRev B w P` agree.

The step from path sums with weights `z` to the composition law of `PaperC.ChainLaw` is in
`BlockReversalLaw`.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset

section Seg

variable {β : Type*} [Fintype β] [DecidableEq β] {K : Type*} [Field K]

/-- Conjugation commutes with powers. -/
theorem conj_pow (Wi W T : Matrix β β K) (h1 : Wi * W = 1) (h2 : W * Wi = 1) (k : ℕ) :
    (Wi * T * W) ^ k = Wi * T ^ k * W := by
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc Wi * T ^ k * W * (Wi * T * W) = Wi * T ^ k * (W * Wi) * T * W := by
          simp only [Matrix.mul_assoc]
      _ = Wi * (T ^ k * T) * W := by rw [h2, Matrix.mul_one, Matrix.mul_assoc Wi, Matrix.mul_assoc Wi]

/-- `Z (P Z)^k = (Z P)^k Z`. -/
theorem mul_pow_comm (Z P : Matrix β β K) (k : ℕ) : Z * (P * Z) ^ k = (Z * P) ^ k * Z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ih, pow_succ]
    simp only [Matrix.mul_assoc]

/-- The segment sums of a block and of its reversal agree:
`w^T Z (W⁻¹ Pᵀ W Z)^k 1 = w^T Z (P Z)^k 1`. -/
theorem seg_reverse (Pb : Matrix β β K) (w z : β → K) (hw : ∀ i, w i ≠ 0) (k : ℕ) :
    ((fun i => w i * z i) ᵥ* (diagonal (fun i => (w i)⁻¹) * Pbᵀ * diagonal w * diagonal z) ^ k)
        ⬝ᵥ (fun _ => (1 : K))
      = ((fun i => w i * z i) ᵥ* (Pb * diagonal z) ^ k) ⬝ᵥ (fun _ => (1 : K)) := by
  set W : Matrix β β K := diagonal w with hW
  set Wi : Matrix β β K := diagonal (fun i => (w i)⁻¹) with hWi
  set Z : Matrix β β K := diagonal z with hZ
  have h1 : Wi * W = 1 := by
    rw [hWi, hW, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hw i]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have h2 : W * Wi = 1 := by
    rw [hWi, hW, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hw i]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have hWZ : W * Z = Z * W := by
    rw [hW, hZ, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext i; exact mul_comm _ _
  have e1 : Wi * Pbᵀ * W * Z = Wi * (Pbᵀ * Z) * W := by
    calc Wi * Pbᵀ * W * Z = Wi * (Pbᵀ * (W * Z)) := by simp only [Matrix.mul_assoc]
      _ = Wi * (Pbᵀ * Z) * W := by rw [hWZ]; simp only [Matrix.mul_assoc]
  rw [e1, conj_pow Wi W _ h1 h2]
  have e2 : (fun i => w i * z i) ᵥ* Wi = z := by
    ext i; have := hw i; simp [hWi, vecMul_diagonal]; field_simp
  have e3 : (fun i => w i * z i) = w ᵥ* Z := by
    ext i; simp [hZ, vecMul_diagonal]
  have e4 : W *ᵥ (fun _ => (1 : K)) = w := by
    ext i; simp [hW, mulVec_diagonal]
  have e5 : Z *ᵥ (fun _ => (1 : K)) = z := by
    ext i; simp [hZ, mulVec_diagonal]
  -- the left side
  have L : ((fun i => w i * z i) ᵥ* (Wi * (Pbᵀ * Z) ^ k * W)) ⬝ᵥ (fun _ => (1 : K))
      = w ⬝ᵥ (((Z * Pb) ^ k) *ᵥ z) := by
    rw [← vecMul_vecMul, ← vecMul_vecMul, e2, ← dotProduct_mulVec, e4, dotProduct_comm,
      ← mulVec_transpose, transpose_pow, transpose_mul, hZ, diagonal_transpose]
    simp
  have R : ((fun i => w i * z i) ᵥ* (Pb * Z) ^ k) ⬝ᵥ (fun _ => (1 : K))
      = w ⬝ᵥ (((Z * Pb) ^ k) *ᵥ z) := by
    rw [e3, vecMul_vecMul, ← dotProduct_mulVec, ← e5, mulVec_mulVec, mul_pow_comm]
  rw [L, R]

end Seg

section Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] (B : Finset ι)

/-- A vector on the subtype `B`, extended by zero. -/
def extB (x : B → K) : ι → K := fun i => if h : i ∈ B then x ⟨i, h⟩ else 0

/-- Extension by zero commutes with one step of the block `A_BB`. -/
theorem extB_vecMul (x : B → K) (A : Matrix ι ι K) :
    extB B x ᵥ* blockIn B A = extB B (x ᵥ* A.submatrix ((↑) : B → ι) ((↑) : B → ι)) := by
  funext j
  by_cases hj : j ∈ B
  · simp only [extB, vecMul, dotProduct, blockIn]
    rw [dif_pos hj]
    rw [sum_split B]
    have h0 : ∑ i ∈ Bᶜ, (if h : i ∈ B then x ⟨i, h⟩ else 0) * (if i ∈ B ∧ j ∈ B then A i j else 0) = 0 :=
      sum_eq_zero fun i hi => by simp [mem_compl.mp hi]
    rw [h0, add_zero, ← Finset.sum_coe_sort B]
    refine sum_congr rfl fun i _ => ?_
    simp [i.2, hj]
  · simp [extB, hj, vecMul, dotProduct, blockIn]

/-- Extension by zero commutes with powers of the block. -/
theorem extB_pow (x : B → K) (A : Matrix ι ι K) (k : ℕ) :
    extB B x ᵥ* blockIn B A ^ k
      = extB B (x ᵥ* (A.submatrix ((↑) : B → ι) ((↑) : B → ι)) ^ k) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [pow_succ, ← vecMul_vecMul, ih, extB_vecMul, pow_succ, ← vecMul_vecMul]

/-- The total of an extended vector. -/
theorem sum_extB (x : B → K) : extB B x ⬝ᵥ (fun _ => (1 : K)) = ∑ i, x i := by
  simp only [dotProduct, mul_one]
  rw [sum_split B, ← Finset.sum_coe_sort B]
  have h0 : ∑ i ∈ Bᶜ, extB B x i = 0 := sum_eq_zero fun i hi => by simp [extB, mem_compl.mp hi]
  rw [h0, add_zero]
  refine sum_congr rfl fun i _ => ?_
  simp [extB, i.2]

/-- The masked segment sums of `BlockSegment` are those of the principal submatrix on `B`. -/
theorem segSum_eq_sub (A : Matrix ι ι K) (ω : ι → K) (k : ℕ) :
    segSum B A ω k
      = ((fun i : B => ω i) ᵥ* (A.submatrix ((↑) : B → ι) ((↑) : B → ι)) ^ k) ⬝ᵥ (fun _ => (1 : K)) := by
  have h : maskB B ω = extB B (fun i : B => ω i) := by
    funext i; by_cases hi : i ∈ B <;> simp [maskB, extB, hi]
  rw [segSum, h, extB_pow, sum_extB]
  simp [dotProduct]

end Bridge

end Kagey131.PaperC.C2

namespace Kagey131.PaperC.C2

open Matrix Finset

section Reversal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

/-- The matrix `P` with the block `P_BB` replaced by its reversal `w_j P_ji / w_i`. -/
def blockRev (B : Finset ι) (w : ι → K) (P : Matrix ι ι K) : Matrix ι ι K :=
  fun i j => if i ∈ B ∧ j ∈ B then w j * P j i / w i else P i j

/-- Reversal of a memoryless block (research note, Theorem 6): if every state of `B` has the
exit row `e` outside `B`, every state outside `B` enters `B` at rates `c_y w_i`, and the start is
`m w` on `B`, then the weighted path sums `μ Z (P Z)^N 1` of `P` and of `blockRev B w P` agree,
for every weight vector `z` and every `N`. -/
theorem memoryless_block_reversal (B : Finset ι) (w e c z μ : ι → K) (m : K)
    (hw : ∀ i ∈ B, w i ≠ 0) (P : Matrix ι ι K)
    (hexit : ∀ i ∈ B, ∀ y ∉ B, P i y = e y) (henter : ∀ y ∉ B, ∀ i ∈ B, P y i = c y * w i)
    (hstart : ∀ i ∈ B, μ i = m * w i) (N : ℕ) :
    μ ⬝ᵥ ((diagonal z * (blockRev B w P * diagonal z) ^ N) *ᵥ fun _ => (1 : K)) =
    μ ⬝ᵥ ((diagonal z * (P * diagonal z) ^ N) *ᵥ fun _ => (1 : K)) := by
  set A : Matrix ι ι K := P * diagonal z with hA
  set A' : Matrix ι ι K := blockRev B w P * diagonal z with hA'
  have hAij : ∀ i j, A i j = P i j * z j := fun i j => by simp [hA, mul_diagonal]
  have hA'ij : ∀ i j, A' i j = blockRev B w P i j * z j := fun i j => by
    simp [hA', mul_diagonal]
  have hbr : ∀ i j, ¬ (i ∈ B ∧ j ∈ B) → blockRev B w P i j = P i j := fun i j h => by
    simp [blockRev, h]
  have conv : ∀ M : Matrix ι ι K,
      μ ⬝ᵥ ((diagonal z * M ^ N) *ᵥ fun _ => (1 : K)) = ((μ ᵥ* diagonal z) ᵥ* M ^ N) ⬝ᵥ fun _ => 1 := by
    intro M
    rw [dotProduct_mulVec, vecMul_vecMul]
  rw [conv, conv]
  refine (pathSum_eq B A' A (fun j => e j * z j) c (fun j => w j * z j) (μ ᵥ* diagonal z) m
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ N)
  · intro i hi j hj; rw [hA'ij, hbr i j (fun h => hj h.2), hexit i hi j hj, ]
  · intro i hi j hj; rw [hAij, hexit i hi j hj]
  · intro y hy j hj; rw [hA'ij, hbr y j (fun h => hy h.1), henter y hy j hj]; ring
  · intro y hy j hj; rw [hAij, henter y hy j hj]; ring
  · ext i j
    by_cases h : i ∉ B ∧ j ∉ B
    · simp only [blockOut, h, and_self]
      rw [hA'ij, hAij, hbr i j (fun h' => h.1 h'.1)]
    · simp [blockOut, h]
  · funext i
    by_cases hi : i ∈ B
    · simp [maskB, hi, vecMul_diagonal, hstart i hi]; ring
    · simp [maskB, hi]
  · intro k
    rw [segSum_eq_sub, segSum_eq_sub]
    have hs : (A'.submatrix ((↑) : B → ι) ((↑) : B → ι))
        = diagonal (fun i : B => (w i)⁻¹) * (P.submatrix ((↑) : B → ι) ((↑) : B → ι))ᵀ *
            diagonal (fun i : B => w i) * diagonal (fun i : B => z i) := by
      ext i j
      have hi := hw i i.2
      simp [hA'ij, blockRev, i.2, j.2, mul_diagonal, diagonal_mul, transpose_apply]
      field_simp
      try simp
    have hs' : (A.submatrix ((↑) : B → ι) ((↑) : B → ι))
        = (P.submatrix ((↑) : B → ι) ((↑) : B → ι)) * diagonal (fun i : B => z i) := by
      ext i j
      simp [hAij, mul_diagonal]
    rw [hs, hs']
    exact seg_reverse _ (fun i : B => w i) (fun i : B => z i) (fun i => hw i i.2) k

end Reversal

end Kagey131.PaperC.C2
