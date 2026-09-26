import Mathlib

/-!
# Paper B, Proposition `prop:field-tilt` (3) (covariance): exact finite identities

* `trans_pow`: the transition matrix `T = σ I + (1-σ) J/d` satisfies
  `T^m = σ^m I + (1-σ^m) J/d`; hence the stationary two-time covariance
  kernel is `(1/d)(T^m)_{ab} - 1/d^2 = σ^m (δ_{ab}/d - 1/d^2)`.
* `sum_sigma_abs`: the finite geometric double sum
  `∑_{i,j<N} σ^|i-j| = N(1+σ)/(1-σ) - 2σ(1-σ^N)/(1-σ)^2` for `σ ≠ 1`, and
  `= N^2` for `σ = 1` (the case `p = 1`).
* `ratio_identity`: `(1+σ)/(1-σ) = (d-2+dp)/(d(1-p))` for
  `σ = (dp-1)/(d-1)`, `p ≠ 1`.

The identification of `Cov(1{X_i=a}, 1{X_{i+m}=b})` with the matrix-power
kernel for the word law of `PaperB.Model` is not formalized here but in
`ChainCovariance.lean`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131.PaperB

open Finset Matrix

variable {d : ℕ}

/-- `T = σ I + (1-σ)/d · J`. -/
noncomputable def Tmat (d : ℕ) (σ : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  σ • (1 : Matrix (Fin d) (Fin d) ℝ) + ((1 - σ) / d) • Matrix.of fun _ _ => (1 : ℝ)

theorem J_mul_J (d : ℕ) :
    (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin d) (Fin d) ℝ) * Matrix.of (fun _ _ => 1) =
      (d : ℝ) • Matrix.of fun _ _ => (1 : ℝ) := by
  ext i j; simp [Matrix.mul_apply]

/-- **Matrix powers:** `T^m = σ^m I + (1-σ^m)/d · J` for `d ≥ 1`. -/
theorem trans_pow (hd : d ≠ 0) (σ : ℝ) (m : ℕ) :
    Tmat d σ ^ m = σ ^ m • (1 : Matrix (Fin d) (Fin d) ℝ) +
      ((1 - σ ^ m) / d) • Matrix.of fun _ _ => (1 : ℝ) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, Tmat]
    simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one, J_mul_J,
      smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    field_simp
    ring

/-- The two-time covariance kernel `σ^m (δ_{ab}/d - 1/d^2)`. -/
theorem cov_kernel (hd : d ≠ 0) (σ : ℝ) (m : ℕ) (a b : Fin d) :
    (1 / (d : ℝ)) * (Tmat d σ ^ m) a b - 1 / (d : ℝ) ^ 2 =
      σ ^ m * ((if a = b then 1 else 0) / d - 1 / (d : ℝ) ^ 2) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  rw [trans_pow hd]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  split_ifs <;> field_simp <;> ring

/-- `∑_{i,j<N} σ^|i-j|`. -/
noncomputable def absSum (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N, σ ^ (Int.natAbs ((i : ℤ) - j))

theorem absSum_succ (σ : ℝ) (N : ℕ) :
    absSum σ (N + 1) = absSum σ N + 1 + 2 * ∑ i ∈ range N, σ ^ (N - i) := by
  unfold absSum
  rw [sum_range_succ, sum_range_succ]
  simp_rw [sum_range_succ (fun j => σ ^ Int.natAbs ((_ : ℕ) - (j : ℤ)))]
  rw [sum_add_distrib]
  have h1 : ∀ i ∈ range N, σ ^ Int.natAbs ((i : ℤ) - (N : ℕ)) = σ ^ (N - i) := by
    intro i hi
    simp only [mem_range] at hi
    congr 1; omega
  have h2 : ∀ j ∈ range N, σ ^ Int.natAbs (((N : ℕ) : ℤ) - j) = σ ^ (N - j) := by
    intro j hj
    simp only [mem_range] at hj
    congr 1; omega
  rw [sum_congr rfl h1, sum_congr rfl h2]
  simp
  ring

theorem geom_tail (σ : ℝ) (hσ : σ ≠ 1) (N : ℕ) :
    ∑ i ∈ range N, σ ^ (N - i) = σ * (1 - σ ^ N) / (1 - σ) := by
  have h : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, show N + 1 - N = 1 by omega, pow_one]
    have : ∑ x ∈ range N, σ ^ (N + 1 - x) = σ * ∑ x ∈ range N, σ ^ (N - x) := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      simp only [mem_range] at hi
      rw [show N + 1 - i = (N - i) + 1 by omega, pow_succ]; ring
    rw [this, ih]
    field_simp
    ring

/-- **The finite geometric sum.** For `σ ≠ 1`,
`∑_{i,j<N} σ^|i-j| = N(1+σ)/(1-σ) - 2σ(1-σ^N)/(1-σ)^2`. -/
theorem sum_sigma_abs (σ : ℝ) (hσ : σ ≠ 1) (N : ℕ) :
    absSum σ N = N * (1 + σ) / (1 - σ) - 2 * σ * (1 - σ ^ N) / (1 - σ) ^ 2 := by
  have h : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
  induction N with
  | zero => simp [absSum]
  | succ N ih =>
    rw [absSum_succ, ih, geom_tail σ hσ]
    push_cast
    field_simp
    ring

/-- At `σ = 1` (`p = 1`) the double sum is `N^2`. -/
theorem sum_sigma_abs_one (N : ℕ) : absSum 1 N = (N : ℝ) ^ 2 := by
  simp [absSum, sq]

/-- `(1+σ)/(1-σ) = (d-2+dp)/(d(1-p))` for `σ = (dp-1)/(d-1)`. -/
theorem ratio_identity (hd : 2 ≤ d) {p : ℝ} (hp : p ≠ 1) :
    (1 + (d * p - 1) / (d - 1)) / (1 - (d * p - 1) / (d - 1)) = (d - 2 + d * p) / (d * (1 - p)) := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hp1 : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  have : 1 - (d * p - 1) / (d - 1) = d * (1 - p) / (d - 1) := by field_simp; ring
  rw [this]
  field_simp
  ring

end Kagey131.PaperB
