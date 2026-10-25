import Mathlib
import PaperC.PrincipalMinors

/-!
# Paper C2: tools for checking principal minors of explicit matrices

Support for the exact examples of Paper C2 (`paperC2/sec_minors.tex`, the `d = 4` example after
Corollary `thm:nonreversible`, and the memoryless-block example). A principal minor
`pminor A S` is a determinant over the subtype `S`, which is awkward to evaluate for an explicit
matrix. Proved here:

* `pminor_eq_det_piecewise`: `pminor A S` is the determinant of the full matrix whose rows
  outside `S` are replaced by the rows of the identity (from `Matrix.det_piecewise_one_eq_submatrix_det`);
* `det_fin_four`, `det_fin_five`: the expansion of a `4 × 4` determinant along the first row, and of a `5 × 5`
  determinant into `det4Expr` of its cofactors.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset Kagey131.PaperC

/-- A principal minor is the determinant of the matrix with the rows outside `S` replaced by
the rows of the identity. -/
theorem pminor_eq_det_piecewise {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (A : Matrix n n R) (S : Finset n) :
    pminor A S = det (Matrix.of fun i j => if i ∈ S then A i j else (1 : Matrix n n R) i j) := by
  rw [pminor, ← det_piecewise_one_eq_submatrix_det]
  congr 1; ext i j; simp only [Finset.piecewise, Matrix.row, Matrix.of_apply]; split_ifs <;> rfl

/-- The Laplace expansion of a `4 × 4` determinant along the first row. -/
theorem det_fin_four {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) : A.det =
    A 0 0 * (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
      + A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1))
    - A 0 1 * (A 1 0 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
      + A 1 3 * (A 2 0 * A 3 2 - A 2 2 * A 3 0))
    + A 0 2 * (A 1 0 * (A 2 1 * A 3 3 - A 2 3 * A 3 1) - A 1 1 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
      + A 1 3 * (A 2 0 * A 3 1 - A 2 1 * A 3 0))
    - A 0 3 * (A 1 0 * (A 2 1 * A 3 2 - A 2 2 * A 3 1) - A 1 1 * (A 2 0 * A 3 2 - A 2 2 * A 3 0)
      + A 1 2 * (A 2 0 * A 3 1 - A 2 1 * A 3 0)) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- The `4 × 4` determinant polynomial, as a function of the entries. -/
def det4Expr {R : Type*} [CommRing R] (A : Fin 4 → Fin 4 → R) : R :=
    A 0 0 * (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
      + A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1))
    - A 0 1 * (A 1 0 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
      + A 1 3 * (A 2 0 * A 3 2 - A 2 2 * A 3 0))
    + A 0 2 * (A 1 0 * (A 2 1 * A 3 3 - A 2 3 * A 3 1) - A 1 1 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
      + A 1 3 * (A 2 0 * A 3 1 - A 2 1 * A 3 0))
    - A 0 3 * (A 1 0 * (A 2 1 * A 3 2 - A 2 2 * A 3 1) - A 1 1 * (A 2 0 * A 3 2 - A 2 2 * A 3 0)
      + A 1 2 * (A 2 0 * A 3 1 - A 2 1 * A 3 0))

/-- The Laplace expansion of a `5 × 5` determinant along the first row, in terms of `det4Expr`. -/
theorem det_fin_five {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R) : A.det =
    A 0 0 * det4Expr (fun i j => A i.succ (![1, 2, 3, 4] j))
    - A 0 1 * det4Expr (fun i j => A i.succ (![0, 2, 3, 4] j))
    + A 0 2 * det4Expr (fun i j => A i.succ (![0, 1, 3, 4] j))
    - A 0 3 * det4Expr (fun i j => A i.succ (![0, 1, 2, 4] j))
    + A 0 4 * det4Expr (fun i j => A i.succ (![0, 1, 2, 3] j)) := by
  rw [det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h : ∀ j : Fin 5, (A.submatrix Fin.succ j.succAbove).det =
      det4Expr (fun i k => A i.succ (j.succAbove k)) := fun j => by
    rw [det_fin_four]; rfl
  simp only [h]
  simp [det4Expr, Fin.succAbove, Fin.lt_def]
  ring

end Kagey131.PaperC.C2
