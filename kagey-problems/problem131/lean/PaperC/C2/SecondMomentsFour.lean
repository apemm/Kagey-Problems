import Mathlib
import PaperC.C2.SecondMoments

/-!
# Paper C2: second moments determine the generator up to time reversal, `d = 4`

Paper C2 (`paperC2/sec_exactlaw.tex`), Theorem `thm:second-moments`(i) for `d = 4`
(`d = 2, 3` are in `SecondMoments`). As there, only the linear conditions `Q 1 = 0`,
`π Q = 0` and `π > 0` are used.

With `A = D Q`, `N = A - Aᵀ` is a `4 × 4` antisymmetric matrix with `N 1 = 0`, so it is determined
by `p = N₀₁`, `q = N₀₂`, `r = N₁₂` (`antisym_four`, `Nmat`). The vector `y = (r, -q, p, 0)` lies in
the kernel of `N`. From `N W N = N' W N'` and `W > 0` we get `ker N' ⊇ ker N` (the positivity
argument of the paper, `quad_antisym`), so `(p', q', r')` is parallel to `(p, q, r)`, and the
diagonal entries of `N W N` then give `(p', q', r') = ±(p, q, r)`.

* `antisym_four`: the parametrization;
* `antisym_four_eq`: `N W N = N' W N'` with `W > 0` gives `N' = ±N`;
* `second_moments_four`: `Q' = Q` or `Q' = Q*`.
-/

namespace Kagey131.PaperC.C2

open Matrix Finset

/-- The `4 × 4` antisymmetric matrices with zero row sums. -/
def Nmat (p q r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, p, q, -p - q; -p, 0, r, p - r; -q, -r, 0, q + r; p + q, r - p, -q - r, 0]

/-- An antisymmetric `4 × 4` matrix with zero row sums is `Nmat p q r` with `p = N₀₁`, `q = N₀₂`,
`r = N₁₂`. -/
theorem antisym_four {N : Matrix (Fin 4) (Fin 4) ℝ} (hN : Nᵀ = -N)
    (h1 : N *ᵥ (fun _ => 1) = 0) : N = Nmat (N 0 1) (N 0 2) (N 1 2) := by
  have e : ∀ i j, N j i = -N i j := fun i j => by
    have := congrFun (congrFun hN i) j; simpa using this
  have r0 := congrFun h1 0
  have r1 := congrFun h1 1
  have r2 := congrFun h1 2
  simp [mulVec, dotProduct, Fin.sum_univ_four] at r0 r1 r2
  have d0 := e 0 0
  have d1 := e 1 1
  have d2 := e 2 2
  have d3 := e 3 3
  have a01 := e 0 1
  have a02 := e 0 2
  have a03 := e 0 3
  have a12 := e 1 2
  have a13 := e 1 3
  have a23 := e 2 3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Nmat] <;> linarith

/-- `y = (r, -q, p, 0)` is in the kernel of `Nmat p q r`. -/
theorem Nmat_kernel (p q r : ℝ) : Nmat p q r *ᵥ ![r, -q, p, 0] = 0 := by
  ext i
  fin_cases i <;> simp [Nmat, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- The algebraic core: parallel parameters with equal diagonal entries are equal up to sign. -/
theorem four_core {w0 w1 w2 w3 : ℝ} (_h0 : 0 < w0) (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3)
    {p q r p' q' r' : ℝ} (e1 : p' * q = q' * p) (e2 : p' * r = r' * p) (e3 : q' * r = r' * q)
    (m00 : w1 * p ^ 2 + w2 * q ^ 2 + w3 * (p + q) ^ 2
      = w1 * p' ^ 2 + w2 * q' ^ 2 + w3 * (p' + q') ^ 2)
    (m11 : w0 * p ^ 2 + w2 * r ^ 2 + w3 * (p - r) ^ 2
      = w0 * p' ^ 2 + w2 * r' ^ 2 + w3 * (p' - r') ^ 2) :
    (p' = p ∧ q' = q ∧ r' = r) ∨ (p' = -p ∧ q' = -q ∧ r' = -r) := by
  by_cases hp : p = 0
  · by_cases hq : q = 0
    · by_cases hr : r = 0
      · subst hp hq hr
        left
        have t1 := mul_nonneg h1.le (sq_nonneg p')
        have t2 := mul_nonneg h2.le (sq_nonneg q')
        have t3 := mul_nonneg h3.le (sq_nonneg (p' + q'))
        have a1 : w1 * p' ^ 2 = 0 := by nlinarith
        have a2 : w2 * q' ^ 2 = 0 := by nlinarith
        have hp' : p' = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp a1).resolve_left h1.ne')
        have hq' : q' = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp a2).resolve_left h2.ne')
        subst hp' hq'
        have s2 := mul_nonneg h2.le (sq_nonneg r')
        have s3 := mul_nonneg h3.le (sq_nonneg (0 - r'))
        have b2 : w2 * r' ^ 2 = 0 := by nlinarith
        have hr' : r' = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp b2).resolve_left h2.ne')
        exact ⟨rfl, rfl, hr'⟩
      · have hp' : p' = 0 := by
          have : p' * r = 0 := by rw [e2, hp, mul_zero]
          exact (mul_eq_zero.mp this).resolve_right hr
        have hq' : q' = 0 := by
          have : q' * r = 0 := by rw [e3, hq, mul_zero]
          exact (mul_eq_zero.mp this).resolve_right hr
        subst hp hq hp' hq'
        have hsq : r' ^ 2 = r ^ 2 := by
          have : (w2 + w3) * (r' ^ 2 - r ^ 2) = 0 := by nlinarith
          rcases mul_eq_zero.mp this with h | h
          · linarith
          · linarith
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
        · left; exact ⟨rfl, rfl, h⟩
        · right; exact ⟨by simp, by simp, h⟩
    · have hp' : p' = 0 := by
        have : p' * q = 0 := by rw [e1, hp, mul_zero]
        exact (mul_eq_zero.mp this).resolve_right hq
      subst hp hp'
      have hsq : q' ^ 2 = q ^ 2 := by
        have : (w2 + w3) * (q' ^ 2 - q ^ 2) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · linarith
      have hr' : r' = q' * r / q := by field_simp; linarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · left
        refine ⟨rfl, h, ?_⟩
        rw [hr', h]; field_simp
      · right
        refine ⟨by simp, h, ?_⟩
        rw [hr', h]; field_simp
  · have hq' : q' = p' * q / p := by field_simp; linarith
    have hr' : r' = p' * r / p := by field_simp; linarith
    set l := p' / p with hl
    have hp'l : p' = l * p := by rw [hl]; field_simp
    have hql : q' = l * q := by rw [hq', hp'l]; field_simp
    have hrl : r' = l * r := by rw [hr', hp'l]; field_simp
    have hpos : 0 < w1 * p ^ 2 + w2 * q ^ 2 + w3 * (p + q) ^ 2 := by
      have : 0 < p ^ 2 := by positivity
      nlinarith [sq_nonneg q, sq_nonneg (p + q)]
    have hl2 : l ^ 2 = 1 := by
      have : (1 - l ^ 2) * (w1 * p ^ 2 + w2 * q ^ 2 + w3 * (p + q) ^ 2) = 0 := by
        rw [hp'l, hql] at m00; nlinarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    have hl2' : l ^ 2 = 1 ^ 2 := by rw [hl2]; norm_num
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hl2' with h | h
    · left; rw [hp'l, hql, hrl, h]; simp
    · right; rw [hp'l, hql, hrl, h]; simp

/-- `N W N = N' W N'` for antisymmetric `4 × 4` matrices killing the constants, with `W > 0`,
gives `N' = N` or `N' = -N`. -/
theorem antisym_four_eq {N N' : Matrix (Fin 4) (Fin 4) ℝ} (hN : Nᵀ = -N)
    (h1 : N *ᵥ (fun _ => 1) = 0) (hN' : N'ᵀ = -N') (h1' : N' *ᵥ (fun _ => 1) = 0)
    (w : Fin 4 → ℝ) (hw : ∀ i, 0 < w i) (h : N * diagonal w * N = N' * diagonal w * N') :
    N' = N ∨ N' = -N := by
  have eN := antisym_four hN h1
  have eN' := antisym_four hN' h1'
  set p := N 0 1
  set q := N 0 2
  set r := N 1 2
  set p' := N' 0 1
  set q' := N' 0 2
  set r' := N' 1 2
  -- the kernel vector of `N` is in the kernel of `N'`
  have hker : N *ᵥ ![r, -q, p, 0] = 0 := by rw [eN]; exact Nmat_kernel p q r
  have hz : N' *ᵥ ![r, -q, p, 0] = 0 := by
    have h0 : ![r, -q, p, 0] ⬝ᵥ ((N' * diagonal w * N') *ᵥ ![r, -q, p, 0]) = 0 := by
      rw [← h, ← mulVec_mulVec, ← mulVec_mulVec, hker]; simp
    rw [quad_antisym hN'] at h0
    have h0' : ∑ i, w i * (N' *ᵥ ![r, -q, p, 0]) i ^ 2 = 0 := by linarith
    have hnn : ∀ i, 0 ≤ w i * (N' *ᵥ ![r, -q, p, 0]) i ^ 2 := fun i =>
      mul_nonneg (hw i).le (sq_nonneg _)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp h0'
    ext i
    have hi := this i (Finset.mem_univ i)
    have : (N' *ᵥ ![r, -q, p, 0]) i ^ 2 = 0 := (mul_eq_zero.mp hi).resolve_left (hw i).ne'
    simpa using this
  have z0 := congrFun hz 0
  have z1 := congrFun hz 1
  have z2 := congrFun hz 2
  rw [eN'] at z0 z1 z2
  simp [Nmat, mulVec, dotProduct, Fin.sum_univ_four] at z0 z1 z2
  -- the diagonal entries of `N W N`
  have m00 := congrFun (congrFun h 0) 0
  have m11 := congrFun (congrFun h 1) 1
  rw [eN, eN'] at m00 m11
  simp [Nmat, Matrix.mul_apply, Fin.sum_univ_four, vecMul_diagonal] at m00 m11
  have core := four_core (hw 0) (hw 1) (hw 2) (hw 3) (p := p) (q := q) (r := r) (p' := p')
    (q' := q') (r' := r') (by linarith) (by linarith) (by linarith) (by nlinarith) (by nlinarith)
  rcases core with ⟨a, b, c⟩ | ⟨a, b, c⟩
  · left; rw [eN, eN', a, b, c]
  · right; rw [eN, eN', a, b, c]; ext i j; fin_cases i <;> fin_cases j <;> simp [Nmat] <;> ring

/-- `d = 4` (`thm:second-moments`(i)): equal `Σ_1`, `Σ_2` and the same stationary law give
`Q' = Q` or `Q' = Q*`. -/
theorem second_moments_four {π : Fin 4 → ℝ} (hpos : ∀ i, 0 < π i)
    {Q Q' : Matrix (Fin 4) (Fin 4) ℝ} (hQ : Q *ᵥ (fun _ => 1) = 0) (hπ : π ᵥ* Q = 0)
    (hQ' : Q' *ᵥ (fun _ => 1) = 0) (hπ' : π ᵥ* Q' = 0)
    (h1 : sigma π Q' 1 = sigma π Q 1) (h2 : sigma π Q' 2 = sigma π Q 2) :
    Q' = Q ∨ Q' = starMat π Q := by
  obtain ⟨hT, hNN⟩ := antisym_reduction hpos h1 h2
  obtain ⟨a1, a2⟩ := antisym_props hQ hπ
  obtain ⟨b1, b2⟩ := antisym_props hQ' hπ'
  have hw : ∀ i, 0 < ((fun i => (π i)⁻¹) : Fin 4 → ℝ) i := fun i => inv_pos.mpr (hpos i)
  have hcases := antisym_four_eq a1 a2 b1 b2 (fun i => (π i)⁻¹) hw hNN.symm
  exact second_moments_conclude hpos hT hcases

end Kagey131.PaperC.C2
