import Mathlib
import PaperC.C2.TimeReversal

/-!
# Paper C2: second moments determine the generator up to time reversal, `d = 2, 3`

Paper C2 (`paperC2/sec_exactlaw.tex`), Theorem `thm:second-moments`(i), for `d = 2` and `d = 3`.
The stationary second moments of the occupation time are given by
`Σ_m = D Q^m + (D Q^m)ᵀ`, `D = diag π` (Lemma `lem:reductions`(iii)). The theorem says that if
`Q'` has the stationary law `π` of `Q` and `Σ'_m = Σ_m` for `m = 1, 2`, then `Q'` is `Q` or the
time reversal `Q* = D⁻¹ Qᵀ D`.

Only the linear conditions `Q 1 = 0` and `π Q = 0` of a generator are used, with `π > 0`.

* `sigma`: the matrices `Σ_m`;
* `antisym_props`, `antisym_reduction`: with `A = D Q`, `N = A - Aᵀ` is antisymmetric with
  `N 1 = 0`, and the data `Σ_1`, `Σ_2` give `A + Aᵀ = A' + A'ᵀ` and `N D⁻¹ N = N' D⁻¹ N'`;
* `antisym_two`, `antisym_three`, `antisym_three_eq`: for `d = 2` such an `N` is `0`, and for
  `d = 3` it is a multiple of one fixed matrix, so `N D⁻¹ N = N' D⁻¹ N'` gives `N' = ±N`;
* `second_moments_two`: `Q' = Q`; `second_moments_three`: `Q' = Q` or `Q' = Q*`.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The second-moment matrices `Σ_m = D Q^m + (D Q^m)ᵀ`. -/
def sigma (π : ι → ℝ) (Q : Matrix ι ι ℝ) (m : ℕ) : Matrix ι ι ℝ :=
  diagonal π * Q ^ m + (diagonal π * Q ^ m)ᵀ

/-- The antisymmetric part `N = D Q - (D Q)ᵀ` is antisymmetric and kills the constants. -/
theorem antisym_props {π : ι → ℝ} {Q : Matrix ι ι ℝ} (hQ : Q *ᵥ (fun _ => 1) = 0)
    (hπ : π ᵥ* Q = 0) :
    (diagonal π * Q - (diagonal π * Q)ᵀ)ᵀ = -(diagonal π * Q - (diagonal π * Q)ᵀ) ∧
    (diagonal π * Q - (diagonal π * Q)ᵀ) *ᵥ (fun _ => 1) = 0 := by
  refine ⟨by rw [transpose_sub, transpose_transpose]; abel, ?_⟩
  rw [sub_mulVec]
  have h1 : (diagonal π * Q) *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    rw [← mulVec_mulVec, hQ, mulVec_zero]
  have h2 : (diagonal π * Q)ᵀ *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    rw [mulVec_transpose, ← vecMul_vecMul]
    have : (fun _ : ι => (1 : ℝ)) ᵥ* diagonal π = π := by ext i; simp [vecMul_diagonal]
    rw [this, hπ]
  rw [h1, h2, sub_zero]

/-- The two moment conditions reduce to a condition on the antisymmetric parts. -/
theorem antisym_reduction {π : ι → ℝ} (hpos : ∀ i, 0 < π i) {Q Q' : Matrix ι ι ℝ}
    (h1 : sigma π Q' 1 = sigma π Q 1) (h2 : sigma π Q' 2 = sigma π Q 2) :
    (diagonal π * Q' + (diagonal π * Q')ᵀ = diagonal π * Q + (diagonal π * Q)ᵀ) ∧
    (diagonal π * Q' - (diagonal π * Q')ᵀ) * diagonal (fun i => (π i)⁻¹)
        * (diagonal π * Q' - (diagonal π * Q')ᵀ)
      = (diagonal π * Q - (diagonal π * Q)ᵀ) * diagonal (fun i => (π i)⁻¹)
        * (diagonal π * Q - (diagonal π * Q)ᵀ) := by
  have hDi' : diagonal (fun i => (π i)⁻¹) * diagonal π = (1 : Matrix ι ι ℝ) := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; have := (hpos i).ne'; simp [this]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  set Di : Matrix ι ι ℝ := diagonal (fun i => (π i)⁻¹) with hDi_def
  have hDiT : Diᵀ = Di := by rw [hDi_def, diagonal_transpose]
  have key : ∀ R : Matrix ι ι ℝ, sigma π R 2 =
      (diagonal π * R) * Di * (diagonal π * R) + (diagonal π * R)ᵀ * Di * (diagonal π * R)ᵀ := by
    intro R
    have e1 : diagonal π * R ^ 2 = (diagonal π * R) * Di * (diagonal π * R) := by
      calc diagonal π * R ^ 2 = diagonal π * R * (1 : Matrix ι ι ℝ) * R := by
            rw [pow_two]; simp [Matrix.mul_assoc]
        _ = diagonal π * R * (Di * diagonal π) * R := by rw [hDi']
        _ = _ := by simp only [Matrix.mul_assoc]
    unfold sigma
    rw [e1]
    simp only [transpose_mul, hDiT, diagonal_transpose, Matrix.mul_assoc]
  have h1' : diagonal π * Q' + (diagonal π * Q')ᵀ = diagonal π * Q + (diagonal π * Q)ᵀ := by
    simpa [sigma] using h1
  refine ⟨h1', ?_⟩
  have h2' := h2
  rw [key, key] at h2'
  set A := diagonal π * Q
  set A' := diagonal π * Q'
  have idn : ∀ (B : Matrix ι ι ℝ), (2 : ℝ) • (B * Di * B + Bᵀ * Di * Bᵀ)
      = (B + Bᵀ) * Di * (B + Bᵀ) + (B - Bᵀ) * Di * (B - Bᵀ) := by
    intro B
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, two_smul]
    abel
  have e := congrArg (fun M => (2 : ℝ) • M) h2'
  simp only [idn] at e
  rw [h1'] at e
  exact add_left_cancel e

/-- If the symmetric parts of `D Q'` and `D Q` agree and the antisymmetric parts agree up to a
sign, then `Q'` is `Q` or the time reversal of `Q`. -/
theorem second_moments_conclude {π : ι → ℝ} (hpos : ∀ i, 0 < π i) {Q Q' : Matrix ι ι ℝ}
    (hT : diagonal π * Q' + (diagonal π * Q')ᵀ = diagonal π * Q + (diagonal π * Q)ᵀ)
    (hc : diagonal π * Q' - (diagonal π * Q')ᵀ = diagonal π * Q - (diagonal π * Q)ᵀ ∨
      diagonal π * Q' - (diagonal π * Q')ᵀ = -(diagonal π * Q - (diagonal π * Q)ᵀ)) :
    Q' = Q ∨ Q' = starMat π Q := by
  have hD : (diagonal (fun i => (π i)⁻¹) : Matrix ι ι ℝ) * diagonal π = 1 := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; have := (hpos i).ne'; simp [this]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have back : ∀ R : Matrix ι ι ℝ, diagonal (fun i => (π i)⁻¹) * (diagonal π * R) = R := by
    intro R; rw [← Matrix.mul_assoc, hD, Matrix.one_mul]
  rcases hc with hc' | hc'
  · left
    have : (2 : ℝ) • (diagonal π * Q') = (2 : ℝ) • (diagonal π * Q) := by
      rw [two_smul, two_smul]
      calc diagonal π * Q' + diagonal π * Q'
          = (diagonal π * Q' + (diagonal π * Q')ᵀ) + (diagonal π * Q' - (diagonal π * Q')ᵀ) := by
            abel
        _ = (diagonal π * Q + (diagonal π * Q)ᵀ) + (diagonal π * Q - (diagonal π * Q)ᵀ) := by
          rw [hT, hc']
        _ = _ := by abel
    have hA := smul_right_injective _ (two_ne_zero) this
    calc Q' = diagonal (fun i => (π i)⁻¹) * (diagonal π * Q') := (back Q').symm
      _ = Q := by rw [hA, back]
  · right
    have hA : diagonal π * Q' = (diagonal π * Q)ᵀ := by
      have : (2 : ℝ) • (diagonal π * Q') = (2 : ℝ) • (diagonal π * Q)ᵀ := by
        rw [two_smul, two_smul]
        calc diagonal π * Q' + diagonal π * Q'
            = (diagonal π * Q' + (diagonal π * Q')ᵀ) + (diagonal π * Q' - (diagonal π * Q')ᵀ) := by
              abel
          _ = (diagonal π * Q + (diagonal π * Q)ᵀ) - (diagonal π * Q - (diagonal π * Q)ᵀ) := by
            rw [hT, hc']; abel
          _ = _ := by abel
      exact smul_right_injective _ (two_ne_zero) this
    calc Q' = diagonal (fun i => (π i)⁻¹) * (diagonal π * Q') := (back Q').symm
      _ = starMat π Q := by
        rw [hA, starMat_eq_conj, transpose_mul, diagonal_transpose]
        simp only [Matrix.mul_assoc]

/-- For antisymmetric `N`, `yᵀ (N W N) y = -∑ w_i (N y)_i²`. -/
theorem quad_antisym {N : Matrix ι ι ℝ} (hN : Nᵀ = -N) (w y : ι → ℝ) :
    y ⬝ᵥ ((N * diagonal w * N) *ᵥ y) = -∑ i, w i * (N *ᵥ y) i ^ 2 := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hN, neg_mulVec,
    neg_dotProduct]
  simp only [dotProduct, mulVec_diagonal]
  congr 1
  exact sum_congr rfl fun i _ => by ring

end General

section Small

/-- `d = 2`: an antisymmetric matrix killing the constants is zero. -/
theorem antisym_two {N : Matrix (Fin 2) (Fin 2) ℝ} (hN : Nᵀ = -N)
    (h1 : N *ᵥ (fun _ => 1) = 0) : N = 0 := by
  have e : ∀ i j, N j i = -N i j := fun i j => by
    have := congrFun (congrFun hN i) j; simpa using this
  have r0 := congrFun h1 0
  have d0 := e 0 0
  have d1 := e 1 1
  have a := e 0 1
  simp [mulVec, dotProduct, Fin.sum_univ_two] at r0
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- `d = 3`: an antisymmetric matrix killing the constants is a multiple of one fixed matrix. -/
theorem antisym_three {N : Matrix (Fin 3) (Fin 3) ℝ} (hN : Nᵀ = -N)
    (h1 : N *ᵥ (fun _ => 1) = 0) :
    N = N 0 1 • !![0, 1, -1; -1, 0, 1; 1, -1, 0] := by
  have e : ∀ i j, N j i = -N i j := fun i j => by
    have := congrFun (congrFun hN i) j; simpa using this
  have r0 := congrFun h1 0
  have r1 := congrFun h1 1
  have r2 := congrFun h1 2
  simp [mulVec, dotProduct, Fin.sum_univ_three] at r0 r1 r2
  have d0 := e 0 0
  have d1 := e 1 1
  have d2 := e 2 2
  have a01 := e 0 1
  have a02 := e 0 2
  have a12 := e 1 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- For the fixed matrix `C` of `d = 3`, `x C W x C` has the entry `-x² (w₁ + w₂)` at `(0,0)`. -/
theorem three_entry (x : ℝ) (w : Fin 3 → ℝ) :
    ((x • !![0, 1, -1; -1, 0, 1; 1, -1, 0] : Matrix (Fin 3) (Fin 3) ℝ) * diagonal w
      * (x • !![0, 1, -1; -1, 0, 1; 1, -1, 0] : Matrix (Fin 3) (Fin 3) ℝ)) 0 0
      = -(x ^ 2) * (w 1 + w 2) := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, vecMul_diagonal]
  ring

/-- `d = 3`: antisymmetric `N, N'` killing the constants with `N W N = N' W N'` for `W > 0`
satisfy `N' = N` or `N' = -N`. -/
theorem antisym_three_eq {N N' : Matrix (Fin 3) (Fin 3) ℝ} (hN : Nᵀ = -N)
    (h1 : N *ᵥ (fun _ => 1) = 0) (hN' : N'ᵀ = -N') (h1' : N' *ᵥ (fun _ => 1) = 0)
    (w : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) (h : N * diagonal w * N = N' * diagonal w * N') :
    N' = N ∨ N' = -N := by
  have eN := antisym_three hN h1
  have eN' := antisym_three hN' h1'
  have h00 := congrFun (congrFun h 0) 0
  rw [eN, eN', three_entry, three_entry] at h00
  have hs : 0 < w 1 + w 2 := add_pos (hw 1) (hw 2)
  have hsq : N' 0 1 ^ 2 = N 0 1 ^ 2 := by
    have : (N' 0 1 ^ 2 - N 0 1 ^ 2) * (w 1 + w 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h0 | h0
  · left; rw [eN, eN', h0]
  · right; rw [eN, eN', h0]; simp

end Small

section Main

/-- `d = 2` (`thm:second-moments`(i)): equal `Σ_1`, `Σ_2` and the same stationary law give
`Q' = Q`. -/
theorem second_moments_two {π : Fin 2 → ℝ} (hpos : ∀ i, 0 < π i)
    {Q Q' : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q *ᵥ (fun _ => 1) = 0) (hπ : π ᵥ* Q = 0) (hQ' : Q' *ᵥ (fun _ => 1) = 0)
    (hπ' : π ᵥ* Q' = 0) (h1 : sigma π Q' 1 = sigma π Q 1) (h2 : sigma π Q' 2 = sigma π Q 2) :
    Q' = Q := by
  obtain ⟨hT, hNN⟩ := antisym_reduction hpos h1 h2
  obtain ⟨a1, a2⟩ := antisym_props hQ hπ
  obtain ⟨b1, b2⟩ := antisym_props hQ' hπ'
  have n0 := antisym_two a1 a2
  have n0' := antisym_two b1 b2
  have hA : diagonal π * Q' = diagonal π * Q := by
    have e1 : diagonal π * Q - (diagonal π * Q)ᵀ = 0 := n0
    have e2 : diagonal π * Q' - (diagonal π * Q')ᵀ = 0 := n0'
    have f1 : (diagonal π * Q)ᵀ = diagonal π * Q := (sub_eq_zero.mp e1).symm
    have f2 : (diagonal π * Q')ᵀ = diagonal π * Q' := (sub_eq_zero.mp e2).symm
    have h := hT
    rw [f1, f2] at h
    have : (2 : ℝ) • (diagonal π * Q') = (2 : ℝ) • (diagonal π * Q) := by
      simpa [two_smul] using h
    exact smul_right_injective _ (two_ne_zero) this
  have hD : (diagonal (fun i => (π i)⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) * diagonal π = 1 := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; have := (hpos i).ne'; simp [this]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  calc Q' = diagonal (fun i => (π i)⁻¹) * (diagonal π * Q') := by
        rw [← Matrix.mul_assoc, hD, Matrix.one_mul]
    _ = Q := by rw [hA, ← Matrix.mul_assoc, hD, Matrix.one_mul]

/-- `d = 3` (`thm:second-moments`(i)): equal `Σ_1`, `Σ_2` and the same stationary law give
`Q' = Q` or `Q' = Q*`. -/
theorem second_moments_three {π : Fin 3 → ℝ} (hpos : ∀ i, 0 < π i)
    {Q Q' : Matrix (Fin 3) (Fin 3) ℝ} (hQ : Q *ᵥ (fun _ => 1) = 0) (hπ : π ᵥ* Q = 0)
    (hQ' : Q' *ᵥ (fun _ => 1) = 0) (hπ' : π ᵥ* Q' = 0)
    (h1 : sigma π Q' 1 = sigma π Q 1) (h2 : sigma π Q' 2 = sigma π Q 2) :
    Q' = Q ∨ Q' = starMat π Q := by
  obtain ⟨hT, hNN⟩ := antisym_reduction hpos h1 h2
  obtain ⟨a1, a2⟩ := antisym_props hQ hπ
  obtain ⟨b1, b2⟩ := antisym_props hQ' hπ'
  have hw : ∀ i, 0 < ((fun i => (π i)⁻¹) : Fin 3 → ℝ) i := fun i => inv_pos.mpr (hpos i)
  have hcases := antisym_three_eq a1 a2 b1 b2 (fun i => (π i)⁻¹) hw hNN.symm
  have hD : (diagonal (fun i => (π i)⁻¹) : Matrix (Fin 3) (Fin 3) ℝ) * diagonal π = 1 := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; have := (hpos i).ne'; simp [this]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have back : ∀ R : Matrix (Fin 3) (Fin 3) ℝ,
      diagonal (fun i => (π i)⁻¹) * (diagonal π * R) = R := by
    intro R; rw [← Matrix.mul_assoc, hD, Matrix.one_mul]
  have e := hT
  rcases hcases with hc | hc
  · left
    have hc' : diagonal π * Q' - (diagonal π * Q')ᵀ = diagonal π * Q - (diagonal π * Q)ᵀ := hc
    have : (2 : ℝ) • (diagonal π * Q') = (2 : ℝ) • (diagonal π * Q) := by
      rw [two_smul, two_smul]
      calc diagonal π * Q' + diagonal π * Q'
          = (diagonal π * Q' + (diagonal π * Q')ᵀ) + (diagonal π * Q' - (diagonal π * Q')ᵀ) := by
            abel
        _ = (diagonal π * Q + (diagonal π * Q)ᵀ) + (diagonal π * Q - (diagonal π * Q)ᵀ) := by
          rw [e, hc']
        _ = _ := by abel
    have hA := smul_right_injective _ (two_ne_zero) this
    calc Q' = diagonal (fun i => (π i)⁻¹) * (diagonal π * Q') := (back Q').symm
      _ = Q := by rw [hA, back]
  · right
    have hc' : diagonal π * Q' - (diagonal π * Q')ᵀ
        = -(diagonal π * Q - (diagonal π * Q)ᵀ) := hc
    have hA : diagonal π * Q' = (diagonal π * Q)ᵀ := by
      have : (2 : ℝ) • (diagonal π * Q') = (2 : ℝ) • (diagonal π * Q)ᵀ := by
        rw [two_smul, two_smul]
        calc diagonal π * Q' + diagonal π * Q'
            = (diagonal π * Q' + (diagonal π * Q')ᵀ) + (diagonal π * Q' - (diagonal π * Q')ᵀ) := by
              abel
          _ = (diagonal π * Q + (diagonal π * Q)ᵀ) - (diagonal π * Q - (diagonal π * Q)ᵀ) := by
            rw [e, hc']; abel
          _ = _ := by abel
      exact smul_right_injective _ (two_ne_zero) this
    calc Q' = diagonal (fun i => (π i)⁻¹) * (diagonal π * Q') := (back Q').symm
      _ = starMat π Q := by
        rw [hA, starMat_eq_conj, transpose_mul, diagonal_transpose]
        simp only [Matrix.mul_assoc]

end Main

end Kagey131.PaperC.C2
