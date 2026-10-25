import Mathlib
import PaperC.PrincipalMinors

/-!
# Paper C2: a cut-transpose keeps all principal minors

Paper C2 (`paperC2/problem131_reconstruction.tex`), Corollary `thm:nonreversible`(c), first
paragraph of the proof (`paperC2/sec_minors.tex`). Let
`C = fromBlocks A (-(a bᵀ)) (-(c uᵀ)) D` on `X ⊕ Y`, with `a, u` on `X` and `b, c` on `Y`. Its
cut-transpose across `X` is `C' = fromBlocks A (-(a cᵀ)) (-(b uᵀ)) Dᵀ`.

* `det_cut_unit`: over a field, if `A` is invertible the two determinants agree, by the Schur
  complement with the same scalar `κ = (uᵀ A⁻¹ a)` on both sides and `det Mᵀ = det M`;
* `det_cutTranspose`: over `ℝ`, `det C = det C'` for every `A`, by continuity in the shift
  `A + s·1`, which is invertible for all but finitely many `s`;
* `pminor_cutTranspose`: the principal minors of `C'` and `C` agree on every `S ⊆ X ⊕ Y`; the
  principal submatrix on `S` is again of the same block form, with the restricted data.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Kagey131.PaperC

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- The determinants of a cut and of its cut-transpose agree when `A` is invertible. -/
theorem det_cut_unit {K : Type*} [Field K] (A : Matrix X X K) (hA : IsUnit A.det)
    (D : Matrix Y Y K) (a u : X → K) (b c : Y → K) :
    (fromBlocks A (-(vecMulVec a b)) (-(vecMulVec c u)) D).det
      = (fromBlocks A (-(vecMulVec a c)) (-(vecMulVec b u)) Dᵀ).det := by
  have : Invertible A := Matrix.invertibleOfIsUnitDet A hA
  rw [det_fromBlocks₁₁, det_fromBlocks₁₁]
  congr 1
  set κ : K := (u ᵥ* ⅟A) ⬝ᵥ a with hκ
  have e1 : D - (-(vecMulVec c u)) * ⅟A * (-(vecMulVec a b)) = D - vecMulVec c (κ • b) := by
    rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg, vecMulVec_mul, vecMulVec_mul_vecMulVec]
  have e2 : Dᵀ - (-(vecMulVec b u)) * ⅟A * (-(vecMulVec a c)) = Dᵀ - vecMulVec b (κ • c) := by
    rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg, vecMulVec_mul, vecMulVec_mul_vecMulVec]
  rw [e1, e2, ← det_transpose (D - vecMulVec c (κ • b)), transpose_sub, transpose_vecMulVec]
  congr 2
  ext i j
  simp [vecMulVec_apply]
  ring

/-- The shifted matrices `A + s·1` are invertible for all but finitely many `s`. -/
theorem dense_det_ne_zero (A : Matrix X X ℝ) : Dense {s : ℝ | (A + s • 1).det ≠ 0} := by
  have hp : (-A).charpoly ≠ 0 := (charpoly_monic (-A)).ne_zero
  have hfin := Polynomial.finite_setOfPred_isRoot hp
  have hdense := Set.Countable.dense_compl ℝ hfin.countable
  refine hdense.mono ?_
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Polynomial.IsRoot, eval_charpoly] at hs
  simp only [Set.mem_ofPred_eq]
  intro h0
  apply hs
  rw [← h0]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij; simp [scalar_apply, one_apply]; ring
  · simp [scalar_apply, hij, one_apply_ne hij]

/-- Corollary `thm:nonreversible`(c), the determinant: a cut and its cut-transpose have the same
determinant, for every `A`. -/
theorem det_cutTranspose (A : Matrix X X ℝ) (D : Matrix Y Y ℝ) (a u : X → ℝ) (b c : Y → ℝ) :
    (fromBlocks A (-(vecMulVec a b)) (-(vecMulVec c u)) D).det
      = (fromBlocks A (-(vecMulVec a c)) (-(vecMulVec b u)) Dᵀ).det := by
  let L : ℝ → Matrix (X ⊕ Y) (X ⊕ Y) ℝ := fun s =>
    fromBlocks (A + s • 1) (-(vecMulVec a b)) (-(vecMulVec c u)) D
  let R : ℝ → Matrix (X ⊕ Y) (X ⊕ Y) ℝ := fun s =>
    fromBlocks (A + s • 1) (-(vecMulVec a c)) (-(vecMulVec b u)) Dᵀ
  have hcont : ∀ (B' : Matrix X Y ℝ) (C' : Matrix Y X ℝ) (D' : Matrix Y Y ℝ),
      Continuous (fun s : ℝ => (fromBlocks (A + s • 1) B' C' D').det) := by
    intro B' C' D'
    refine Continuous.matrix_det ?_
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j
    · simp only [fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply]
      fun_prop
    · simp only [fromBlocks_apply₁₂]; exact continuous_const
    · simp only [fromBlocks_apply₂₁]; exact continuous_const
    · simp only [fromBlocks_apply₂₂]; exact continuous_const
  have key : (fun s : ℝ => (L s).det) = fun s : ℝ => (R s).det :=
    Continuous.ext_on (dense_det_ne_zero A) (hcont _ _ _) (hcont _ _ _) fun s hs =>
      det_cut_unit (A + s • 1) (isUnit_iff_ne_zero.mpr hs) D a u b c
  have := congrFun key 0
  simpa [L, R] using this

/-- The states of `S ⊆ X ⊕ Y` on the left and on the right form `S`. -/
def sumEquivS (S : Finset (X ⊕ Y)) :
    {x : X // Sum.inl x ∈ S} ⊕ {y : Y // Sum.inr y ∈ S} ≃ S where
  toFun
    | Sum.inl x => ⟨Sum.inl x.1, x.2⟩
    | Sum.inr y => ⟨Sum.inr y.1, y.2⟩
  invFun i :=
    match i with
    | ⟨Sum.inl x, hx⟩ => Sum.inl ⟨x, hx⟩
    | ⟨Sum.inr y, hy⟩ => Sum.inr ⟨y, hy⟩
  left_inv := by rintro (x | y) <;> rfl
  right_inv := by rintro ⟨x | y, h⟩ <;> rfl

/-- The principal minor of a cut on `S` is the determinant of a cut with the restricted data. -/
theorem pminor_cut (A : Matrix X X ℝ) (D : Matrix Y Y ℝ) (a u : X → ℝ) (b c : Y → ℝ)
    (S : Finset (X ⊕ Y)) :
    pminor (fromBlocks A (-(vecMulVec a b)) (-(vecMulVec c u)) D) S
      = (fromBlocks (A.submatrix (fun x : {x : X // Sum.inl x ∈ S} => x.1) (fun x => x.1))
          (-(vecMulVec (fun x : {x : X // Sum.inl x ∈ S} => a x.1)
            (fun y : {y : Y // Sum.inr y ∈ S} => b y.1)))
          (-(vecMulVec (fun y : {y : Y // Sum.inr y ∈ S} => c y.1)
            (fun x : {x : X // Sum.inl x ∈ S} => u x.1)))
          (D.submatrix (fun y : {y : Y // Sum.inr y ∈ S} => y.1) (fun y => y.1))).det := by
  unfold pminor
  rw [← det_submatrix_equiv_self (sumEquivS S)]
  congr 1
  ext (i | i) (j | j) <;> simp [sumEquivS, vecMulVec_apply]

/-- Corollary `thm:nonreversible`(c): a cut-transpose has the principal minors of the cut, on
every set `S` of states. -/
theorem pminor_cutTranspose (A : Matrix X X ℝ) (D : Matrix Y Y ℝ) (a u : X → ℝ) (b c : Y → ℝ)
    (S : Finset (X ⊕ Y)) :
    pminor (fromBlocks A (-(vecMulVec a c)) (-(vecMulVec b u)) Dᵀ) S
      = pminor (fromBlocks A (-(vecMulVec a b)) (-(vecMulVec c u)) D) S := by
  rw [pminor_cut A D a u b c S, pminor_cut A Dᵀ a u c b S]
  exact (det_cutTranspose _ _ _ _ _ _).symm

end Kagey131.PaperC.C2
