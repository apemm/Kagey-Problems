import Mathlib

/-!
# Paper C: the multiaffine polynomial `R_F` and principal minors

Paper C, Section 9.3 (`sec_reconstruction.tex`, the display defining `R_F` before
`lem:RF-irreducible`), and note 06 of `research_notes/C theorems 5 and 7`, Lemma 3.1.

Proved here, for a square matrix `A` over a commutative ring:

* `det_sub_diagonal_eq_sum_minors`: the multiaffine expansion
  `det(A - diag w) = ∑_{S ⊆ V} det A_S ∏_{i ∉ S} (-w_i)`, with `det A_∅ = 1`, by
  multilinearity of the determinant in the rows;
* `det_add_diagonal_eq_sum_minors`: the same with `+ diag w` and `∏_{i ∉ S} w_i`;
* `RF_eq_sum_minors`: the face version, `R_F(w) = det(A_F - diag w)` as the sum over the
  subsets of the face, for `A_F` the principal submatrix on a `Finset` `F`;
* `charpoly_eq_of_minors_eq`: two matrices with the same principal minors have the same
  characteristic polynomial (note 06, Lemma 3.1, used in `thm:nonreversible`(b)).
-/

namespace Kagey131.PaperC

open Finset Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The principal minor `det A_S` of `A` on the set `S`. -/
def pminor (A : Matrix n n R) (S : Finset n) : R :=
  (A.submatrix ((↑) : S → n) ((↑) : S → n)).det

/-- `R_F` with all of the states: `det(A + diag w) = ∑_S det A_S ∏_{i ∉ S} w_i`. -/
theorem det_add_diagonal_eq_sum_minors (A : Matrix n n R) (w : n → R) :
    (A + diagonal w).det = ∑ S : Finset n, pminor A S * ∏ i ∈ Sᶜ, w i := by
  let D := (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
  have h1 : (A + diagonal w) = (fun i => A i) + (fun i => w i • (1 : Matrix n n R) i) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [diagonal_apply_ne _ h, one_apply_ne h]
  change D (A + diagonal w) = _
  rw [h1, D.map_add_univ]
  refine sum_congr rfl fun S _ => ?_
  have h_smul : S.piecewise (fun i => A i) (fun i => w i • (1 : Matrix n n R) i) =
      fun i => (if i ∈ S then 1 else w i) •
        S.piecewise (fun i => A i) (fun i => (1 : Matrix n n R) i) i := by
    funext i j
    by_cases hi : i ∈ S
    · simp [piecewise, hi]
    · simp [piecewise, hi]
  rw [h_smul, D.map_smul_univ]
  have hprod : ∏ i, (if i ∈ S then (1 : R) else w i) = ∏ i ∈ Sᶜ, w i := by
    rw [← prod_mul_prod_compl S]
    rw [prod_congr rfl (fun i hi => if_pos hi), prod_const_one, one_mul]
    exact prod_congr rfl (fun i hi => if_neg (mem_compl.mp hi))
  rw [hprod, smul_eq_mul, mul_comm]
  congr 1
  exact det_piecewise_one_eq_submatrix_det A S

/-- The multiaffine expansion of `sec_reconstruction`:
`det(A - diag w) = ∑_{S ⊆ V} det A_S ∏_{i ∉ S} (-w_i)`. -/
theorem det_sub_diagonal_eq_sum_minors (A : Matrix n n R) (w : n → R) :
    (A - diagonal w).det = ∑ S : Finset n, pminor A S * ∏ i ∈ Sᶜ, (-w i) := by
  rw [show A - diagonal w = A + diagonal (fun i => -w i) by rw [sub_eq_add_neg, diagonal_neg]]
  exact det_add_diagonal_eq_sum_minors A _

omit [Fintype n] in
/-- The empty principal minor is `1`. -/
theorem pminor_empty (A : Matrix n n R) : pminor A ∅ = 1 := by
  unfold pminor
  exact det_isEmpty

/-- The full principal minor is the determinant. -/
theorem pminor_univ (A : Matrix n n R) : pminor A univ = A.det := by
  unfold pminor
  exact det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun _ => mem_univ _)) A

/-- The principal submatrix `A_F` of `A` on a face `F`. -/
def faceBlock (A : Matrix n n R) (F : Finset n) : Matrix F F R :=
  A.submatrix ((↑) : F → n) ((↑) : F → n)

/-- The polynomial `R_F(w) = det(A_F - diag w)` of `sec_reconstruction`. -/
def RF (A : Matrix n n R) (F : Finset n) (w : F → R) : R :=
  (faceBlock A F - diagonal w).det

omit [Fintype n] in
/-- `R_F(w) = ∑_{S ⊆ F} det A_S ∏_{i ∈ F ∖ S} (-w_i)`, the subsets of `F` taken as
subsets of the subtype `F`. -/
theorem RF_eq_sum_minors (A : Matrix n n R) (F : Finset n) (w : F → R) :
    RF A F w = ∑ S : Finset F, pminor (faceBlock A F) S * ∏ i ∈ Sᶜ, (-w i) :=
  det_sub_diagonal_eq_sum_minors _ w

omit [Fintype n] in
/-- A principal minor of the face block is a principal minor of `A`, on the image set. -/
theorem pminor_faceBlock (A : Matrix n n R) (F : Finset n) (S : Finset F) :
    pminor (faceBlock A F) S = pminor A (S.map (Function.Embedding.subtype _)) := by
  unfold pminor faceBlock
  let e : (S : Set F) ≃ ((S.map (Function.Embedding.subtype _) : Finset n) : Set n) :=
    { toFun := fun x => ⟨x.1.1, by simp⟩
      invFun := fun y => ⟨⟨y.1, by
          obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp y.2
          rw [← hzy]; exact z.2⟩, by
          obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp y.2
          have : z = ⟨y.1, by rw [← hzy]; exact z.2⟩ := Subtype.ext hzy
          rw [← this]; exact hz⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [← det_submatrix_equiv_self e]
  rfl

/-- Note 06, Lemma 3.1: equal principal minors give equal characteristic polynomials. -/
theorem charpoly_eq_of_minors_eq (A B : Matrix n n R) (h : ∀ S : Finset n, pminor A S = pminor B S) :
    A.charpoly = B.charpoly := by
  nontriviality R
  ext k
  by_cases hk : k ≤ Fintype.card n
  · have hk' : k = Fintype.card n - (Fintype.card n - k) := by omega
    rw [hk', charpoly_coeff_eq_sum_minors A _ (Nat.sub_le _ _),
      charpoly_coeff_eq_sum_minors B _ (Nat.sub_le _ _)]
    congr 1
    exact sum_congr rfl fun S _ => h S
  · push Not at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim]; exact hk),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim]; exact hk)]

end Kagey131.PaperC
