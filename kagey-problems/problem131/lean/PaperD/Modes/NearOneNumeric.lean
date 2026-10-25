import Mathlib

/-!
# Paper D, Theorem `thm:two-modes-near-one`, the numerical core

File: `paperD/sec_bulk_applications.tex`. The proof of `thm:two-modes-near-one` ends with a
comparison of two numbers built from the bounds `M` on the mean and `V` on the variance of
`L_a`, for `δ = 1 - a ≤ 1/40`. We prove the comparison

`5/2 * (V / (V + 9/25)) < 4/7 * (1 - V / (7/4 - M)^2)`

in `near_one_numeric`. The paper evaluates `M ≤ 1.0107` and `V ≤ 0.0752` with the decimal value of
the Euler constant `γ`. Mathlib gives `γ > 1/2`, which is enough: it yields `M < 80/79` and
`V < 59/741`, and the two sides are then below `0.453` and above `0.487`.
-/

namespace Kagey131.PaperD.Modes

/-- The numerical core of `thm:two-modes-near-one`: for `0 < δ ≤ 1/40`, any `M` and `V` with
`1 ≤ M ≤ e^{(1-γ)δ}` and `0 ≤ V ≤ e^{2(1-γ)δ}/(1-2δ) - 1` satisfy
`5/2 · V/(V + 9/25) < 4/7 · (1 - V/(7/4 - M)^2)`. -/
theorem near_one_numeric {δ M V : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1/40) (_hM1 : 1 ≤ M)
    (hM : M ≤ Real.exp ((1 - Real.eulerMascheroniConstant) * δ)) (hV0 : 0 ≤ V)
    (hV : V ≤ Real.exp (2 * (1 - Real.eulerMascheroniConstant) * δ) / (1 - 2 * δ) - 1) :
    5/2 * (V / (V + 9/25)) < 4/7 * (1 - V / (7/4 - M) ^ 2) := by
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  set γ := Real.eulerMascheroniConstant
  have ht1 : (1 - γ) * δ ≤ 1/80 := by nlinarith
  have ht2 : 2 * (1 - γ) * δ ≤ 1/40 := by nlinarith
  have e1 : Real.exp ((1 - γ) * δ) ≤ Real.exp (1/80) := Real.exp_le_exp.2 ht1
  have e2 : Real.exp (2 * (1 - γ) * δ) ≤ Real.exp (1/40) := Real.exp_le_exp.2 ht2
  have b1 : Real.exp (1/80) < 1 / (1 - 1/80) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  have b2 : Real.exp (1/40) < 1 / (1 - 1/40) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  have hM' : M < 80/79 := by
    have : (1:ℝ) / (1 - 1/80) = 80/79 := by norm_num
    linarith
  have hexp2 : Real.exp (2 * (1 - γ) * δ) < 40/39 := by
    have : (1:ℝ) / (1 - 1/40) = 40/39 := by norm_num
    linarith
  have hpos : 0 < 1 - 2 * δ := by linarith
  have hV' : V ≤ 59/741 := by
    have : Real.exp (2 * (1 - γ) * δ) / (1 - 2 * δ) ≤ (40/39) / (19/20) := by
      rw [div_le_div_iff₀ hpos (by norm_num)]
      have := Real.exp_pos (2 * (1 - γ) * δ)
      nlinarith
    have h3 : (40/39 : ℝ) / (19/20) = 800/741 := by norm_num
    linarith
  -- left side
  have hden : 0 < V + 9/25 := by linarith
  have hL : V / (V + 9/25) ≤ (59/741) / (59/741 + 9/25) := by
    rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  have hd : 0 < (7/4 - M) := by linarith
  have hR : V / (7/4 - M) ^ 2 ≤ (59/741) / (7/4 - 80/79) ^ 2 := by
    have h1 : V / (7/4 - M) ^ 2 ≤ (59/741) / (7/4 - M) ^ 2 :=
      div_le_div_of_nonneg_right hV' (by positivity)
    have h2 : (59/741 : ℝ) / (7/4 - M) ^ 2 ≤ (59/741) / (7/4 - 80/79) ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have : (7/4 - 80/79 : ℝ) < 7/4 - M := by linarith
      nlinarith
    linarith
  have hL' : (5/2 : ℝ) * ((59/741) / (59/741 + 9/25)) < 4/7 * (1 - (59/741) / (7/4 - 80/79) ^ 2) := by
    norm_num
  nlinarith

end Kagey131.PaperD.Modes
