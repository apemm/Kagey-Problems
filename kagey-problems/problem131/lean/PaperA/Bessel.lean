import Mathlib

/-!
# Modified Bessel functions `I_0`, `I_1` as power series

Mathlib has no modified Bessel functions, so we define
`I_0(z) = ∑_r (z/2)^(2r) / (r!)^2` and `I_1(z) = ∑_r (z/2)^(2r+1) / (r! (r+1)!)`
(DLMF 10.25.2) as `tsum`s, prove that the series converge, and prove the index-shift
identities used in Paper A (proofs of Theorems `thm:bessel`, `thm:allbin-bessel`,
`thm:periodic-bessel`, `thm:edge-matching`):

* `∑ r(r+1) x^(2r)/(r!)^2 = x² I_0(2x) + x I_1(2x)`,
* `∑ r(r+1) x^(2r+1)/(r!(r+1)!) = x² I_1(2x)`,
* `∑ (r+1) x^(2r+1)/(r!(r+1)!) = x I_0(2x)`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset

/-- The modified Bessel function `I_0`, defined by its power series. -/
noncomputable def besselI0 (z : ℝ) : ℝ :=
  ∑' r : ℕ, (z / 2) ^ (2 * r) / ((r.factorial : ℝ) ^ 2)

/-- The modified Bessel function `I_1`, defined by its power series. -/
noncomputable def besselI1 (z : ℝ) : ℝ :=
  ∑' r : ℕ, (z / 2) ^ (2 * r + 1) / ((r.factorial : ℝ) * ((r + 1).factorial : ℝ))

/-- The terms of `I_0(2x)`. -/
noncomputable def b0 (x : ℝ) (r : ℕ) : ℝ := x ^ (2 * r) / ((r.factorial : ℝ) ^ 2)

/-- The terms of `I_1(2x)`. -/
noncomputable def b1 (x : ℝ) (r : ℕ) : ℝ := x ^ (2 * r + 1) / ((r.factorial : ℝ) * ((r + 1).factorial : ℝ))

theorem b0_nonneg (x : ℝ) (r : ℕ) : 0 ≤ b0 x r := by
  unfold b0
  rw [pow_mul]
  positivity

theorem b1_nonneg {x : ℝ} (hx : 0 ≤ x) (r : ℕ) : 0 ≤ b1 x r := by
  unfold b1; positivity

theorem b0_pos {x : ℝ} (hx : 0 < x) (r : ℕ) : 0 < b0 x r := by
  unfold b0; positivity

theorem b1_pos {x : ℝ} (hx : 0 < x) (r : ℕ) : 0 < b1 x r := by
  unfold b1; positivity

theorem summable_b0 (x : ℝ) : Summable (b0 x) := by
  refine Summable.of_nonneg_of_le (b0_nonneg x) (fun r => ?_)
    (Real.summable_pow_div_factorial (x ^ 2))
  unfold b0
  rw [pow_mul]
  have h1 : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r)
  have h2 : (r.factorial : ℝ) ≤ (r.factorial : ℝ) ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) h2

theorem summable_b1 (x : ℝ) : Summable (b1 x) := by
  refine Summable.of_norm_bounded ((Real.summable_pow_div_factorial (x ^ 2)).mul_left |x|)
    (fun r => ?_)
  unfold b1
  rw [Real.norm_eq_abs, abs_div, abs_pow, pow_succ, pow_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r.factorial : ℝ)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((r + 1).factorial : ℝ))]
  have h1 : (1 : ℝ) ≤ (r + 1).factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
  rw [hsq]
  have hf : (0 : ℝ) < r.factorial := by positivity
  rw [div_le_iff₀ (by positivity)]
  have : (x ^ 2) ^ r * |x| ≤ (x ^ 2) ^ r * |x| * (r + 1).factorial :=
    le_mul_of_one_le_right (by positivity) h1
  calc (x ^ 2) ^ r * |x| ≤ (x ^ 2) ^ r * |x| * (r + 1).factorial := this
    _ = |x| * ((x ^ 2) ^ r / r.factorial) * (r.factorial * (r + 1).factorial) := by
      field_simp

theorem besselI0_two_mul (x : ℝ) : besselI0 (2 * x) = ∑' r, b0 x r := by
  unfold besselI0 b0
  congr 1; ext r
  rw [mul_div_cancel_left₀ x (two_ne_zero)]

theorem besselI1_two_mul (x : ℝ) : besselI1 (2 * x) = ∑' r, b1 x r := by
  unfold besselI1 b1
  congr 1; ext r
  rw [mul_div_cancel_left₀ x (two_ne_zero)]

theorem hasSum_b0 (x : ℝ) : HasSum (b0 x) (besselI0 (2 * x)) := by
  rw [besselI0_two_mul]; exact (summable_b0 x).hasSum

theorem hasSum_b1 (x : ℝ) : HasSum (b1 x) (besselI1 (2 * x)) := by
  rw [besselI1_two_mul]; exact (summable_b1 x).hasSum

theorem b0_zero (x : ℝ) : b0 x 0 = 1 := by simp [b0]

theorem one_le_besselI0 (x : ℝ) : 1 ≤ besselI0 (2 * x) := by
  rw [besselI0_two_mul, (summable_b0 x).tsum_eq_zero_add, b0_zero]
  have : 0 ≤ ∑' r, b0 x (r + 1) := tsum_nonneg (fun r => b0_nonneg x _)
  linarith

theorem besselI1_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ besselI1 (2 * x) := by
  rw [besselI1_two_mul]; exact tsum_nonneg (b1_nonneg hx)

theorem besselI1_pos {x : ℝ} (hx : 0 < x) : 0 < besselI1 (2 * x) := by
  rw [besselI1_two_mul, (summable_b1 x).tsum_eq_zero_add]
  have h0 : 0 < b1 x 0 := b1_pos hx 0
  have : 0 ≤ ∑' r, b1 x (r + 1) := tsum_nonneg (fun r => b1_nonneg hx.le _)
  linarith

/-! ### Index-shift identities -/

theorem b0_shift (x : ℝ) (r : ℕ) :
    ((r + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) + 1) * b0 x (r + 1) = x ^ 2 * b0 x r + x * b1 x r := by
  unfold b0 b1
  rw [Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp
  ring

theorem b1_shift (x : ℝ) (r : ℕ) :
    ((r + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) + 1) * b1 x (r + 1) = x ^ 2 * b1 x r := by
  unfold b1
  rw [show r + 1 + 1 = r + 2 by ring, Nat.factorial_succ (r + 1), Nat.factorial_succ r]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp
  ring

theorem b1_weight (x : ℝ) (r : ℕ) : ((r : ℝ) + 1) * b1 x r = x * b0 x r := by
  unfold b0 b1
  rw [Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp
  ring

/-- `∑ r(r+1) x^(2r)/(r!)^2 = x² I_0(2x) + x I_1(2x)`. -/
theorem hasSum_rr_b0 (x : ℝ) :
    HasSum (fun r : ℕ => (r : ℝ) * ((r : ℝ) + 1) * b0 x r)
      (x ^ 2 * besselI0 (2 * x) + x * besselI1 (2 * x)) := by
  have h := ((hasSum_b0 x).mul_left (x ^ 2)).add ((hasSum_b1 x).mul_left x)
  have e : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1) * b0 x (n + 1)) =
      (fun b => x ^ 2 * b0 x b + x * b1 x b) := funext (b0_shift x)
  have h' : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1) * b0 x (n + 1))
      (x ^ 2 * besselI0 (2 * x) + x * besselI1 (2 * x)) := by rw [e]; exact h
  have := (hasSum_nat_add_iff (f := fun r : ℕ => (r : ℝ) * ((r : ℝ) + 1) * b0 x r) 1).1 h'
  simpa using this

/-- `∑ r(r+1) x^(2r+1)/(r!(r+1)!) = x² I_1(2x)`. -/
theorem hasSum_rr_b1 (x : ℝ) :
    HasSum (fun r : ℕ => (r : ℝ) * ((r : ℝ) + 1) * b1 x r) (x ^ 2 * besselI1 (2 * x)) := by
  have h := (hasSum_b1 x).mul_left (x ^ 2)
  have e : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1) * b1 x (n + 1)) =
      (fun b => x ^ 2 * b1 x b) := funext (b1_shift x)
  have h' : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1) * b1 x (n + 1))
      (x ^ 2 * besselI1 (2 * x)) := by rw [e]; exact h
  have := (hasSum_nat_add_iff (f := fun r : ℕ => (r : ℝ) * ((r : ℝ) + 1) * b1 x r) 1).1 h'
  simpa using this

/-- `∑ (r+1) x^(2r+1)/(r!(r+1)!) = x I_0(2x)`. -/
theorem hasSum_r1_b1 (x : ℝ) :
    HasSum (fun r : ℕ => ((r : ℝ) + 1) * b1 x r) (x * besselI0 (2 * x)) := by
  have h := (hasSum_b0 x).mul_left x
  have e : (fun r : ℕ => ((r : ℝ) + 1) * b1 x r) = (fun r => x * b0 x r) := funext (b1_weight x)
  rw [e]; exact h

end Kagey131
