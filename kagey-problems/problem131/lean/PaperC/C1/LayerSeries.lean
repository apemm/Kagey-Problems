import Mathlib

/-!
# Paper C1: the series identities in the proof of `lem:layer-exact`

Paper C1 (`paperC/problem131_chains.tex`), `paperC/sec_boundary.tex`, proof of
`lem:layer-exact`. With `ρ - 1 = r` (so `ρ ≥ 1`) the proof uses two identities.

* `choose_div_factorial`: `C(n+r, r)/(n+r)! = 1/(n! r!)`;
* `hasSum_layer`: `∑_{n≥0} C(n+r, r) y^n s^{n+r}/(n+r)! = e^{ys} s^r/r!`, as a `HasSum` in `ℝ`.
-/

namespace Kagey131.PaperC.C1

/-- `C(n+ρ-1, ρ-1)/(n+ρ-1)! = 1/(n! (ρ-1)!)`, with `r = ρ - 1`. -/
theorem choose_div_factorial (n r : ℕ) :
    ((n + r).choose r : ℝ) / ((n + r).factorial : ℝ) = 1 / ((n.factorial : ℝ) * r.factorial) := by
  have h : (((n + r).choose r : ℕ) : ℝ) * (n.factorial : ℝ) * (r.factorial : ℝ)
      = ((n + r).factorial : ℝ) := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n r
  have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (r.factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((n + r).factorial : ℝ) ≠ 0 := by positivity
  rw [div_eq_div_iff h3 (mul_ne_zero h1 h2), ← h]
  ring

/-- The series of the proof of `lem:layer-exact`:
`∑_{n≥0} C(n+r, r) y^n s^{n+r}/(n+r)! = e^{ys} s^r/r!` with `r = ρ - 1`. -/
theorem hasSum_layer (r : ℕ) (y s : ℝ) :
    HasSum (fun n : ℕ => ((n + r).choose r : ℝ) * y ^ n * s ^ (n + r) / ((n + r).factorial : ℝ))
      (Real.exp (y * s) * s ^ r / (r.factorial : ℝ)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (y * s)).mul_right (s ^ r / (r.factorial : ℝ))
  rw [← Real.exp_eq_exp_ℝ] at h
  have e : (fun n : ℕ => ((n + r).choose r : ℝ) * y ^ n * s ^ (n + r) / ((n + r).factorial : ℝ))
      = fun i : ℕ => (y * s) ^ i / (i.factorial : ℝ) * (s ^ r / (r.factorial : ℝ)) := by
    funext n
    have := choose_div_factorial n r
    calc ((n + r).choose r : ℝ) * y ^ n * s ^ (n + r) / ((n + r).factorial : ℝ)
        = (((n + r).choose r : ℝ) / ((n + r).factorial : ℝ)) * (y ^ n * s ^ (n + r)) := by ring
      _ = _ := by
        rw [this, mul_pow, pow_add]
        have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
        have h2 : (r.factorial : ℝ) ≠ 0 := by positivity
        field_simp
  rw [e, show Real.exp (y * s) * s ^ r / (r.factorial : ℝ)
    = Real.exp (y * s) * (s ^ r / (r.factorial : ℝ)) by ring]
  exact h

end Kagey131.PaperC.C1
