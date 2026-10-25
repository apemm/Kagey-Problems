import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
# The coin-turning note: the value of the expansion at `N = 200`

The note quotes, for `prop:aging-expansion` at `N = 200`, the value `0.8932` of
`1 - log 2 / (log N + γ + 2 - 2 log 2)`. Here it is shown to lie in `[0.8931, 0.8933]`
(`expansion_value_200`), with `γ` Euler's constant.

Mathlib's `1/2 < γ < 2/3` is too coarse, since the value moves by about `0.016` per unit of
`γ`. The constant is instead bracketed by the two monotone sequences
`harmonic n - log (n+1) < γ < harmonic n - log n` at `n = 128`, with `harmonic 128` evaluated
exactly by `norm_num` (`euler_bounds`). The logarithms are written in terms of
`log 2` (`Real.log_two_gt_d9`, `Real.log_two_lt_d9`) and two short series:
`log 129 = 7 log 2 + log (1 + 1/128)` and `log 200 = 8 log 2 + log (25/32)`.
-/

namespace Kagey131.PaperD.S4

open Real Finset


theorem log_129_128_upper : Real.log (129 / 128) < 0.007783 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -1 / 128) (by norm_num [abs_of_neg]) 3
  have e : (1 : ℝ) - -1 / 128 = 129 / 128 := by norm_num
  rw [e] at h
  have h2 := (abs_le.mp h).2
  norm_num [Finset.sum_range_succ, abs_of_neg] at h2
  linarith

theorem log_25_32_bounds : -0.246863 < Real.log (25 / 32) ∧ Real.log (25 / 32) < -0.246858 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 7 / 32) (by norm_num [abs_of_pos]) 8
  have e : (1 : ℝ) - 7 / 32 = 25 / 32 := by norm_num
  rw [e] at h
  have h2 := abs_le.mp h
  norm_num [Finset.sum_range_succ, abs_of_pos] at h2
  constructor <;> linarith [h2.1, h2.2]

/-- Bounds for `γ`: `0.5732 < γ < 0.5812`. -/
theorem euler_bounds : 0.5732 < Real.eulerMascheroniConstant ∧
    Real.eulerMascheroniConstant < 0.5812 := by
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have l129 : Real.log 129 = 7 * Real.log 2 + Real.log (129 / 128) := by
    rw [show (129 : ℝ) = 2 ^ 7 * (129 / 128) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have l128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  have h129 := log_129_128_upper
  have hlow := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 128
  have hhigh := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 128
  unfold Real.eulerMascheroniSeq at hlow
  unfold Real.eulerMascheroniSeq' at hhigh
  simp only [show (128 : ℕ) ≠ 0 by norm_num, if_false] at hhigh
  norm_num at hlow hhigh
  constructor
  · linarith
  · linarith

/-- The value of the expansion of `prop:aging-expansion` at `N = 200`, which the note quotes as
`0.8932`: `1 - log 2/(log 200 + γ + 2 - 2 log 2) ∈ [0.8931, 0.8933]`. -/
theorem expansion_value_200 :
    0.8931 ≤ 1 - Real.log 2 / (Real.log 200 + Real.eulerMascheroniConstant + 2 - 2 * Real.log 2) ∧
      1 - Real.log 2 / (Real.log 200 + Real.eulerMascheroniConstant + 2 - 2 * Real.log 2) ≤
        0.8933 := by
  obtain ⟨g1, g2⟩ := euler_bounds
  obtain ⟨b1, b2⟩ := log_25_32_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have l200 : Real.log 200 = 8 * Real.log 2 + Real.log (25 / 32) := by
    rw [show (200 : ℝ) = 2 ^ 8 * (25 / 32) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  rw [l200]
  have hD : 0 < 8 * Real.log 2 + Real.log (25 / 32) + Real.eulerMascheroniConstant + 2 -
      2 * Real.log 2 := by linarith
  constructor
  · have : Real.log 2 / (8 * Real.log 2 + Real.log (25 / 32) + Real.eulerMascheroniConstant + 2 -
        2 * Real.log 2) ≤ 0.1069 := by
      rw [div_le_iff₀ hD]; linarith
    linarith
  · have : 0.1067 ≤ Real.log 2 / (8 * Real.log 2 + Real.log (25 / 32) +
        Real.eulerMascheroniConstant + 2 - 2 * Real.log 2) := by
      rw [le_div_iff₀ hD]; linarith
    linarith

end Kagey131.PaperD.S4
