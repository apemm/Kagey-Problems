import Mathlib
import PaperC.C2.SecondMoments
import PaperC.C2.EigenplaneSign

/-!
# Paper C2: second moments determine the generator up to time reversal (the general case)

Paper C2 (`paperC2/sec_exactlaw.tex`), Theorem `thm:second-moments`(ii). With `D = diag π`,
`π_i = s_i²`, `E = diag s`, `G = E Q E⁻¹`, `S = (G + Gᵀ)/2` and `K = (G - Gᵀ)/2` the data
`Σ_m = D Q^m + (D Q^m)ᵀ` for `m = 1, 2, 3` are `Σ_m = E (G^m + (G^m)ᵀ) E`, and

* `sym_one`, `sym_two`, `sym_three`: `sym G = S`, `sym G² = S² + K²`,
  `sym G³ = S³ + S K² + K² S + K S K` (the display `eq:sym-powers`, with `sym A = (A + Aᵀ)/2`);
* `sigma_eq_conj`: `Σ_m = E (G^m + (G^m)ᵀ) E`;
* `second_moments_ii`: if the eigenplanes of `K²` (data `Planes`, every nonzero eigenvalue of
  multiplicity exactly 2) form a connected graph for `PlaneEdge S`, and `Σ'_m = Σ_m` for
  `m = 1, 2, 3`, then `Q'` is `Q` or the time reversal `Q*`. The linear algebra is
  `EigenplaneSign.eigenplane_sign`.

Part (i) for `d ≤ 4` is in `SecondMoments` and `SecondMomentsFour`; part (iii) (genericity of the
hypothesis) is not formalized.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The symmetric part. -/
noncomputable def sPart (G : Matrix ι ι ℝ) : Matrix ι ι ℝ := (1 / 2 : ℝ) • (G + Gᵀ)

/-- The antisymmetric part. -/
noncomputable def kPart (G : Matrix ι ι ℝ) : Matrix ι ι ℝ := (1 / 2 : ℝ) • (G - Gᵀ)

/-- `G = E Q E⁻¹`. -/
noncomputable def gmat (s : ι → ℝ) (Q : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  diagonal s * Q * diagonal (fun i => (s i)⁻¹)

theorem sPart_symm (G : Matrix ι ι ℝ) : (sPart G)ᵀ = sPart G := by
  simp [sPart, transpose_smul, transpose_add, add_comm]

theorem kPart_anti (G : Matrix ι ι ℝ) : (kPart G)ᵀ = -kPart G := by
  simp [kPart, transpose_smul, transpose_sub, smul_sub]

theorem G_eq (G : Matrix ι ι ℝ) : G = sPart G + kPart G := by
  ext i j; simp [sPart, kPart]; ring

theorem Gt_eq (G : Matrix ι ι ℝ) : Gᵀ = sPart G - kPart G := by
  ext i j; simp [sPart, kPart]; ring

/-- For `G = S + K` with `S` symmetric and `K` antisymmetric: `G + Gᵀ = 2S`. -/
theorem sym_one (G : Matrix ι ι ℝ) : G + Gᵀ = (2 : ℝ) • sPart G := by
  ext i j; simp [sPart]; ring

theorem sym_two (G : Matrix ι ι ℝ) :
    G ^ 2 + (G ^ 2)ᵀ = (2 : ℝ) • (sPart G ^ 2 + kPart G * kPart G) := by
  have h1 := G_eq G
  have h2 := Gt_eq G
  rw [transpose_pow, h2]
  nth_rewrite 1 [h1]
  rw [pow_two, pow_two, pow_two]
  simp only [add_mul, mul_add, sub_mul, mul_sub, two_smul]
  abel

theorem sym_three (G : Matrix ι ι ℝ) :
    G ^ 3 + (G ^ 3)ᵀ = (2 : ℝ) • (sPart G ^ 3 + sPart G * (kPart G * kPart G) +
      (kPart G * kPart G) * sPart G + kPart G * sPart G * kPart G) := by
  have h1 := G_eq G
  have h2 := Gt_eq G
  rw [transpose_pow, h2]
  nth_rewrite 1 [h1]
  simp only [pow_succ, pow_zero, Matrix.one_mul, add_mul, mul_add, sub_mul, mul_sub, two_smul, Matrix.mul_assoc]
  abel

section Conj

variable {s : ι → ℝ} (hs : ∀ i, 0 < s i)
include hs

theorem E_inv : diagonal s * diagonal (fun i => (s i)⁻¹) = (1 : Matrix ι ι ℝ) := by
  rw [diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij; have := (hs i).ne'; simp [this]
  · simp [diagonal_apply_ne _ hij, one_apply_ne hij]

theorem E_inv' : diagonal (fun i => (s i)⁻¹) * diagonal s = (1 : Matrix ι ι ℝ) := by
  rw [diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij; have := (hs i).ne'; simp [this]
  · simp [diagonal_apply_ne _ hij, one_apply_ne hij]

theorem Q_pow (Q : Matrix ι ι ℝ) (m : ℕ) :
    Q ^ m = diagonal (fun i => (s i)⁻¹) * (gmat s Q) ^ m * diagonal s := by
  have hQ : Q = diagonal (fun i => (s i)⁻¹) * gmat s Q * diagonal s := by
    unfold gmat
    calc Q = (diagonal (fun i => (s i)⁻¹) * diagonal s) * Q *
          (diagonal (fun i => (s i)⁻¹) * diagonal s) := by rw [E_inv' hs]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  induction m with
  | zero => simp [E_inv' hs]
  | succ m ih =>
    calc Q ^ (m + 1) = Q ^ m * Q := pow_succ _ _
      _ = (diagonal (fun i => (s i)⁻¹) * (gmat s Q) ^ m * diagonal s) *
          (diagonal (fun i => (s i)⁻¹) * gmat s Q * diagonal s) := by rw [← ih, ← hQ]
      _ = diagonal (fun i => (s i)⁻¹) * (gmat s Q) ^ (m + 1) * diagonal s := by
        rw [pow_succ]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (diagonal s), E_inv hs, Matrix.one_mul]

/-- `Σ_m = E (G^m + (G^m)ᵀ) E`. -/
theorem sigma_eq_conj {π : ι → ℝ} (hπ : ∀ i, π i = s i ^ 2) (Q : Matrix ι ι ℝ) (m : ℕ) :
    sigma π Q m = diagonal s * ((gmat s Q) ^ m + ((gmat s Q) ^ m)ᵀ) * diagonal s := by
  have hD : diagonal π = diagonal s * diagonal s := by
    rw [diagonal_mul_diagonal]; congr 1; funext i; rw [hπ, sq]
  unfold sigma
  rw [Q_pow hs Q m, hD]
  have : diagonal s * diagonal s * (diagonal (fun i => (s i)⁻¹) * gmat s Q ^ m * diagonal s) =
      diagonal s * gmat s Q ^ m * diagonal s := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal s) (diagonal fun i => (s i)⁻¹), E_inv hs, Matrix.one_mul]
  rw [this, transpose_mul, transpose_mul, diagonal_transpose]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

end Conj

/-- **`thm:second-moments`(ii).** `G = E Q E⁻¹`, `G' = E Q' E⁻¹`. -/
theorem second_moments_ii {π s : ι → ℝ} (hs : ∀ i, 0 < s i) (hπ : ∀ i, π i = s i ^ 2)
    {Q Q' G : Matrix ι ι ℝ} (hG : G = gmat s Q)
    (P : Planes (κ := κ) (kPart G * kPart G))
    (hconn : (SimpleGraph.fromRel (PlaneEdge (sPart G) P)).Connected)
    (h1 : sigma π Q' 1 = sigma π Q 1) (h2 : sigma π Q' 2 = sigma π Q 2)
    (h3 : sigma π Q' 3 = sigma π Q 3) :
    Q' = Q ∨ Q' = starMat π Q := by
  obtain ⟨G', hG'⟩ : ∃ G', G' = gmat s Q' := ⟨_, rfl⟩
  -- cancel the conjugation by E
  have cancel : ∀ A B : Matrix ι ι ℝ,
      diagonal s * A * diagonal s = diagonal s * B * diagonal s → A = B := by
    intro A B h
    have key : ∀ X : Matrix ι ι ℝ, diagonal (fun i => (s i)⁻¹) * (diagonal s * X * diagonal s) *
        diagonal (fun i => (s i)⁻¹) = X := by
      intro X
      calc _ = (diagonal (fun i => (s i)⁻¹) * diagonal s) * X *
            (diagonal s * diagonal (fun i => (s i)⁻¹)) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [E_inv' hs, E_inv hs]; simp
    rw [← key A, ← key B, h]
  have two_inj : ∀ A B : Matrix ι ι ℝ, (2 : ℝ) • A = (2 : ℝ) • B → A = B :=
    fun A B h => smul_right_injective _ (two_ne_zero) h
  rw [sigma_eq_conj hs hπ, sigma_eq_conj hs hπ, ← hG, ← hG'] at h1 h2 h3
  have e1 := cancel _ _ h1
  have e2 := cancel _ _ h2
  have e3 := cancel _ _ h3
  rw [sym_one, sym_one] at e1
  rw [sym_two, sym_two] at e2
  rw [sym_three, sym_three] at e3
  have hS : sPart G' = sPart G := two_inj _ _ (by simpa using e1)
  have hKK : kPart G' * kPart G' = kPart G * kPart G := by
    rw [hS] at e2
    have := two_inj _ _ e2
    exact add_left_cancel this
  have hKSK : kPart G' * sPart G * kPart G' = kPart G * sPart G * kPart G := by
    rw [hS, hKK] at e3
    have := two_inj _ _ e3
    exact add_left_cancel this
  have hK2 : (kPart G * kPart G)ᵀ = kPart G * kPart G := by
    rw [transpose_mul, kPart_anti]; simp
  have hres :=
    eigenplane_sign hK2 P (kPart_anti G') (kPart_anti G) (sPart_symm G) hKK rfl hKSK hconn
  -- return to Q
  have hQ' : Q' = diagonal (fun i => (s i)⁻¹) * G' * diagonal s := by
    have := Q_pow hs Q' 1; rw [← hG'] at this; simpa using this
  have hQ : Q = diagonal (fun i => (s i)⁻¹) * G * diagonal s := by
    have := Q_pow hs Q 1; rw [← hG] at this; simpa using this
  rcases hres with h | h
  · left
    have : G' = G := by rw [G_eq G', G_eq G, hS, h]
    rw [hQ', this, ← hQ]
  · right
    have : G' = Gᵀ := by rw [G_eq G', Gt_eq G, hS, h, sub_eq_add_neg]
    have hDinv : diagonal (fun i => (π i)⁻¹) =
        diagonal (fun i => (s i)⁻¹) * diagonal (fun i => (s i)⁻¹) := by
      rw [diagonal_mul_diagonal]; congr 1; funext i; rw [hπ, sq, mul_inv]
    have hD : diagonal π = diagonal s * diagonal s := by
      rw [diagonal_mul_diagonal]; congr 1; funext i; rw [hπ, sq]
    have hQt : Qᵀ = diagonal s * Gᵀ * diagonal (fun i => (s i)⁻¹) := by
      conv_lhs => rw [hQ]
      rw [transpose_mul, transpose_mul, diagonal_transpose, diagonal_transpose]
      simp only [Matrix.mul_assoc]
    rw [hQ', this, starMat_eq_conj, hDinv, hD, hQt]
    symm
    calc _ = diagonal (fun i => (s i)⁻¹) * (diagonal (fun i => (s i)⁻¹) * diagonal s) * Gᵀ *
          (diagonal (fun i => (s i)⁻¹) * diagonal s) * diagonal s := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [E_inv' hs]; simp [Matrix.mul_assoc]

end Kagey131.PaperC.C2
