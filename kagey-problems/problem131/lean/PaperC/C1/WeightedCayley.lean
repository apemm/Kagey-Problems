import Mathlib

/-!
# Paper C1: the weighted Cayley formula and the rank-one determinant

Paper C1 (`paperC/problem131_chains.tex`), `paperC/sec_complete.tex`, `lem:weighted-cayley`, and
`paperC/sec_secondorder.tex`, `prop:constant`(b), the determinant step.

Mathlib has no matrix-tree theorem, so the tree sum `tree(c)` of the paper is represented here by
the determinant of the reduced Laplacian (the Laplacian of the conductances with state `0`
deleted), which is the value the matrix-tree theorem assigns to it. The paper's states
`1, ..., k` are `Fin (k+1)` here, with the deleted state being `0`; so the paper's `k` is
`k + 1` in the statements below.

Proved here:

* `det_diagonal_sub_vecMulVec`: the matrix determinant lemma for `diag d - a aᵀ`;
* `redLap_products`: the reduced Laplacian of the conductances `x_i x_j` is
  `diag(X x_i) - x' x'ᵀ`;
* `weighted_cayley_det`: `tree(c) = x_0 ⋯ x_k (x_0 + ⋯ + x_k)^{k-1}` (`lem:weighted-cayley`);
* `cayley_count`: the case `x_i = 1`, the count `(k+1)^{k-1}` of Cayley;
* `det_diag_sub_rankOne`: `det(D' - α'α'ᵀ) = ∏ α_i` when `∑ α = 1` (`prop:constant`(b));
* `det_sigma_of_factor`: `det(2 M L⁻¹ M) = 2^k det(M)^2 / det L`;
* `det_sigma_formula`: the paper's form `det Σ_α = 2^{k-1} (∏ α_i)^2 / tree(c(α))`.
-/

namespace Kagey131.PaperC.C1

open Finset Matrix

/-- The reduced Laplacian (state `0` deleted) of symmetric conductances `c` on `Fin (k+1)`. -/
def redLap {k : ℕ} (c : Fin (k + 1) → Fin (k + 1) → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => if i = j then ∑ l ∈ Finset.univ.erase i.succ, c i.succ l else - c i.succ j.succ

/-- The matrix determinant lemma for a positive diagonal minus a rank-one term. -/
theorem det_diagonal_sub_vecMulVec {n : Type*} [Fintype n] [DecidableEq n]
    (d a : n → ℝ) (hd : ∀ i, d i ≠ 0) :
    (diagonal d - vecMulVec a a).det = (∏ i, d i) * (1 - ∑ i, a i * a i / d i) := by
  have hdet : IsUnit (diagonal d).det := by
    rw [det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  have h1 : diagonal d - vecMulVec a a
      = diagonal d + replicateCol Unit (-a) * replicateRow Unit a := by
    rw [← vecMulVec_eq Unit]
    ext i j
    simp [vecMulVec, sub_eq_add_neg]
  have hinv : (diagonal d)⁻¹ = diagonal (fun i => (d i)⁻¹) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hd i)
  rw [h1, det_add_replicateCol_mul_replicateRow hdet, det_diagonal, hinv]
  congr 1
  rw [det_unique]
  simp [Matrix.mul_apply, replicateRow, replicateCol, diagonal_apply, div_eq_mul_inv]
  rw [sub_eq_add_neg]
  congr 2
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The reduced Laplacian of the conductances `c_ij = x_i x_j` is `diag(X x_i) - x' x'ᵀ`, with
`X = ∑ x_i` and `x'_i = x_{i+1}` (the first step of the proof of `lem:weighted-cayley`). -/
theorem redLap_products {k : ℕ} (x : Fin (k + 1) → ℝ) :
    redLap (fun i j => x i * x j) =
      diagonal (fun i : Fin k => (∑ l, x l) * x i.succ)
        - vecMulVec (fun i : Fin k => x i.succ) (fun i : Fin k => x i.succ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [redLap, if_true, Matrix.sub_apply, diagonal_apply_eq, vecMulVec_apply]
    have hX : ∑ l, x l = x i.succ + ∑ l ∈ Finset.univ.erase i.succ, x l :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i.succ)).symm
    rw [← Finset.mul_sum, hX]
    ring
  · simp [redLap, hij, vecMulVec_apply]

/-- `lem:weighted-cayley`: for `x_i > 0` and conductances `c_ij = x_i x_j` on `k + 1` states
(the paper's `k` is `k + 1` here), the tree sum, taken as the determinant of the reduced
Laplacian, is `x_0 ⋯ x_k (x_0 + ⋯ + x_k)^{k-1}`. Requires `1 ≤ k`: for a single state the empty
determinant is `1`, while the right side would be `x_0`. -/
theorem weighted_cayley_det {k : ℕ} (hk : 1 ≤ k) (x : Fin (k + 1) → ℝ) (hx : ∀ i, 0 < x i) :
    (redLap (fun i j => x i * x j)).det = (∏ i, x i) * (∑ i, x i) ^ (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hX : 0 < ∑ i, x i := Finset.sum_pos (fun i _ => hx i) ⟨0, Finset.mem_univ _⟩
  set X := ∑ i, x i with hXdef
  rw [redLap_products, det_diagonal_sub_vecMulVec _ _ (fun i => (mul_pos hX (hx _)).ne')]
  have h1 : ∏ i : Fin (m + 1), (X * x i.succ) = X ^ (m + 1) * ∏ i : Fin (m + 1), x i.succ := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : ∑ i : Fin (m + 1), x i.succ * x i.succ / (X * x i.succ)
      = (X - x 0) / X := by
    have : ∀ i : Fin (m + 1), x i.succ * x i.succ / (X * x i.succ) = x i.succ / X := by
      intro i
      have := (hx i.succ).ne'
      field_simp
    rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.sum_div]
    congr 1
    have hs : X = x 0 + ∑ i : Fin (m + 1), x i.succ := Fin.sum_univ_succ x
    linarith
  have hp : ∏ i, x i = x 0 * ∏ i : Fin (m + 1), x i.succ := Fin.prod_univ_succ x
  rw [h1, h2, hp]
  have hXne := hX.ne'
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

/-- Cayley's count: with all `x_i = 1` the tree sum of the complete graph on `k + 1` states is
`(k+1)^{k-1}` (the instance of `lem:weighted-cayley` with every `x_i = 1`). -/
theorem cayley_count (k : ℕ) :
    (redLap (fun _ _ : Fin (k + 1) => (1 : ℝ))).det = ((k : ℝ) + 1) ^ (k - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have := weighted_cayley_det hk (fun _ : Fin (k + 1) => (1 : ℝ)) (fun _ => one_pos)
    simpa using this

/-- `prop:constant`(b), the determinant step: with `α > 0` summing to one and state `0`
deleted, `det(D' - α'α'ᵀ) = ∏ α_i`. -/
theorem det_diag_sub_rankOne {k : ℕ} (α : Fin (k + 1) → ℝ) (hα : ∀ i, 0 < α i)
    (hsum : ∑ i, α i = 1) :
    (diagonal (fun i : Fin k => α i.succ)
        - vecMulVec (fun i : Fin k => α i.succ) (fun i : Fin k => α i.succ)).det
      = ∏ i, α i := by
  rw [det_diagonal_sub_vecMulVec _ _ (fun i => (hα _).ne'), Fin.prod_univ_succ]
  have : ∑ i : Fin k, α i.succ * α i.succ / α i.succ = 1 - α 0 := by
    rw [← hsum, Fin.sum_univ_succ]
    rw [add_sub_cancel_left]
    exact Finset.sum_congr rfl fun i _ => by have := (hα i.succ).ne'; field_simp
  rw [this]
  ring

/-- `prop:constant`(b), the scaling step: `det(2 M L⁻¹ M) = 2^k det(M)^2 / det L` for
invertible `L`. -/
theorem det_sigma_of_factor {k : ℕ} (M L : Matrix (Fin k) (Fin k) ℝ) (hL : IsUnit L.det) :
    ((2 : ℝ) • (M * L⁻¹ * M)).det = 2 ^ k * M.det ^ 2 / L.det := by
  have hne := isUnit_iff_ne_zero.mp hL
  rw [det_smul, det_mul, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', Fintype.card_fin]
  field_simp

/-- `prop:constant`(b), the form of `det Σ_α`: for `Σ_α = 2 M L⁻¹ M` with
`M = D' - α'α'ᵀ` and `L` the reduced Laplacian of conductances `c` (the paper's `k` is `k + 1`),
`det Σ_α = 2^k (∏ α_i)^2 / tree(c)` for `α > 0` summing to one. -/
theorem det_sigma_formula {k : ℕ} (α : Fin (k + 1) → ℝ) (hα : ∀ i, 0 < α i)
    (hsum : ∑ i, α i = 1) (c : Fin (k + 1) → Fin (k + 1) → ℝ) (hL : IsUnit (redLap c).det) :
    ((2 : ℝ) • ((diagonal (fun i : Fin k => α i.succ)
          - vecMulVec (fun i : Fin k => α i.succ) (fun i : Fin k => α i.succ))
        * (redLap c)⁻¹ *
        (diagonal (fun i : Fin k => α i.succ)
          - vecMulVec (fun i : Fin k => α i.succ) (fun i : Fin k => α i.succ)))).det
      = 2 ^ k * (∏ i, α i) ^ 2 / (redLap c).det := by
  rw [det_sigma_of_factor _ _ hL, det_diag_sub_rankOne α hα hsum]

end Kagey131.PaperC.C1
