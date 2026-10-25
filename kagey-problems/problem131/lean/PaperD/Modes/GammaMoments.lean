import Mathlib

/-!
# Paper D, Theorem `thm:two-modes-near-one`, the moment bounds

File: `paperD/sec_bulk_applications.tex`. With `δ = 1 - a`, the moments of the limit `L_a` are
`E L_a = 1/Γ(1+a)` and `E L_a^2 = 1/((2a-1)Γ(2a))` (Guérin, Laulin and Raschel, Theorem 1.4; these
formulas are taken from that paper and are not proved here). The paper bounds them with the
convexity of `log Γ` and `ψ(2) = 1 - γ`:

* `logGamma_le_zero`, `logGamma_ge_tangent`: for `1 ≤ y ≤ 2`,
  `(1 - γ)(y - 2) ≤ log Γ(y) ≤ 0`;
* `gamma_mean_bounds`: `1 ≤ 1/Γ(1+a) ≤ exp((1-γ)(1-a))` for `39/40 ≤ a < 1`;
* `gamma_second_moment_bound`: `1/((2a-1)Γ(2a)) ≤ exp(2(1-γ)(1-a))/(1 - 2(1-a))`.

The range `39/40 ≤ a` is only used to keep `2a - 1 > 0`; the proofs need `1/2 < a < 1`.
-/

namespace Kagey131.PaperD.Modes

open Real Set

/-- `log Γ(y) ≤ 0` on `[1, 2]`: `log Γ` is convex with `Γ(1) = Γ(2) = 1`. -/
theorem logGamma_le_zero {y : ℝ} (h1 : 1 ≤ y) (h2 : y ≤ 2) : Real.log (Real.Gamma y) ≤ 0 := by
  have hc := convexOn_log_Gamma
  have := hc.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num) (show (2 : ℝ) ∈ Ioi 0 by norm_num)
    (show (0 : ℝ) ≤ 2 - y by linarith) (show (0 : ℝ) ≤ y - 1 by linarith)
    (by ring : (2 - y) + (y - 1) = 1)
  simp only [Function.comp_apply, Real.Gamma_one, Real.Gamma_two, Real.log_one, smul_eq_mul,
    mul_zero, add_zero] at this
  have e : (2 - y) * 1 + (y - 1) * 2 = y := by ring
  rw [e] at this
  exact this

/-- The derivative of `log Γ` at `2` is `1 - γ`. -/
theorem deriv_logGamma_two :
    deriv (Real.log ∘ Real.Gamma) 2 = 1 - Real.eulerMascheroniConstant := by
  have hd : deriv Real.Gamma 2 = 1 - Real.eulerMascheroniConstant := by
    have := Real.deriv_Gamma_nat 1
    norm_num at this
    linarith
  rw [Function.comp_def, deriv.log (Real.differentiableAt_Gamma (fun m => by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    intro h; linarith)) (by rw [Real.Gamma_two]; norm_num), hd, Real.Gamma_two, div_one]

/-- The tangent line at `2` lies below `log Γ` on `[1, 2]`, by convexity. -/
theorem logGamma_ge_tangent {y : ℝ} (h1 : 1 ≤ y) (h2 : y ≤ 2) :
    (1 - Real.eulerMascheroniConstant) * (y - 2) ≤ Real.log (Real.Gamma y) := by
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · simp
  · have hc := convexOn_log_Gamma
    have hder : DifferentiableAt ℝ (Real.log ∘ Real.Gamma) 2 := by
      refine (Real.differentiableAt_Gamma (fun m => ?_)).log (by rw [Real.Gamma_two]; norm_num)
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      intro h; linarith
    have := hc.slope_le_deriv (show y ∈ Ioi (0 : ℝ) by simp; linarith)
      (show (2 : ℝ) ∈ Ioi 0 by norm_num) hlt hder
    rw [deriv_logGamma_two, slope_def_field] at this
    simp only [Function.comp_apply, Real.Gamma_two, Real.log_one] at this
    have hpos : 0 < 2 - y := by linarith
    rw [div_le_iff₀ (by linarith)] at this
    nlinarith

theorem gamma_ge_exp_tangent {y : ℝ} (h1 : 1 ≤ y) (h2 : y ≤ 2) :
    Real.exp ((1 - Real.eulerMascheroniConstant) * (y - 2)) ≤ Real.Gamma y := by
  have hpos : 0 < Real.Gamma y := Real.Gamma_pos_of_pos (by linarith)
  rw [← Real.log_le_log_iff (Real.exp_pos _) hpos, Real.log_exp]
  exact logGamma_ge_tangent h1 h2

theorem gamma_le_one {y : ℝ} (h1 : 1 ≤ y) (h2 : y ≤ 2) : Real.Gamma y ≤ 1 := by
  have hpos : 0 < Real.Gamma y := Real.Gamma_pos_of_pos (by linarith)
  have := logGamma_le_zero h1 h2
  rwa [Real.log_nonpos_iff hpos.le] at this

/-- The bounds `1 ≤ E L_a ≤ M` of `thm:two-modes-near-one`. -/
theorem gamma_mean_bounds {a : ℝ} (ha : 39/40 ≤ a) (ha1 : a < 1) :
    1 ≤ 1 / Real.Gamma (1 + a) ∧
    1 / Real.Gamma (1 + a) ≤ Real.exp ((1 - Real.eulerMascheroniConstant) * (1 - a)) := by
  have hpos : 0 < Real.Gamma (1 + a) := Real.Gamma_pos_of_pos (by linarith)
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hpos]
    simpa using gamma_le_one (y := 1 + a) (by linarith) (by linarith)
  · have h := gamma_ge_exp_tangent (y := 1 + a) (by linarith) (by linarith)
    rw [div_le_iff₀ hpos]
    have e : Real.exp ((1 - Real.eulerMascheroniConstant) * (1 - a)) *
        Real.exp ((1 - Real.eulerMascheroniConstant) * (1 + a - 2)) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 2
      ring
    have hE := Real.exp_pos ((1 - Real.eulerMascheroniConstant) * (1 - a))
    nlinarith

/-- The bound `E L_a^2 ≤ e^{2(1-γ)δ}/(1-2δ)` of `thm:two-modes-near-one`, `δ = 1 - a`. -/
theorem gamma_second_moment_bound {a : ℝ} (ha : 39/40 ≤ a) (ha1 : a < 1) :
    1 / ((2 * a - 1) * Real.Gamma (2 * a)) ≤
      Real.exp (2 * (1 - Real.eulerMascheroniConstant) * (1 - a)) / (1 - 2 * (1 - a)) := by
  have hpos : 0 < Real.Gamma (2 * a) := Real.Gamma_pos_of_pos (by linarith)
  have hq : 0 < 2 * a - 1 := by linarith
  have h := gamma_ge_exp_tangent (y := 2 * a) (by linarith) (by linarith)
  have e1 : 1 - 2 * (1 - a) = 2 * a - 1 := by ring
  rw [e1, div_le_div_iff₀ (by positivity) hq]
  have e : Real.exp (2 * (1 - Real.eulerMascheroniConstant) * (1 - a)) *
      Real.exp ((1 - Real.eulerMascheroniConstant) * (2 * a - 2)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hE := Real.exp_pos (2 * (1 - Real.eulerMascheroniConstant) * (1 - a))
  nlinarith [mul_le_mul_of_nonneg_left h hE.le]

end Kagey131.PaperD.Modes
