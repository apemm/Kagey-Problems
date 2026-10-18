import PaperD.U4_Refined

/-!
# Online Resource S1, part 8: an explicit `N` beyond which `g_N > x_N` (Remark S1.3)

Remark S1.3 (`rem:refined`) says "We also do not know an explicit `N` beyond which
`g_N > x_N`". Proposition S1.2 in its explicit form (`prop_refined_explicit`) gives one:

* `crossing_lt_gRoot_3500`: `x_N < g_N` for every even `N = 2h` with `log N ≥ 3500`.

This sharpens `crossing_lt_gRoot` (threshold `21000`) by using `g_N ≥ Λ_N - log Λ_N`
(`gRoot_spec`) instead of `g_N ≥ L/2`; then `g_N ≥ 1.996 L`, so the main term
`(2 g_N L + g_N²/2)/(N(1 + 1/g_N))` is about `6L²/N`, which beats the error `20822 L/N` once
`L ≥ 3480`. Assumes Hoeffding's inequality (`HoeffdingHypergeomHyp`), through
Proposition S1.1.
-/

namespace Kagey131.PaperD.U4

open Kagey131.PaperD

/-- **Remark S1.3, an explicit threshold.** Assume Hoeffding's inequality for sampling without
replacement. For every `h` with `log(2h) ≥ 3500`, the crossing `x_N` (`crossingX h`) is
strictly less than the root `g_N` of `G(g) = Λ_N` (`gRoot (2h)`). -/
theorem crossing_lt_gRoot_3500 (hHoef : HoeffdingHypergeomHyp) {h : ℕ}
    (hL : 3500 ≤ Real.log (2 * (h : ℝ))) : crossingX h < gRoot (2 * (h : ℝ)) := by
  have hL30 : 30 ≤ Real.log (2 * (h : ℝ)) := by linarith
  have hx := abs_le.mp (prop_refined_explicit hHoef hL30)
  have hh := one_le_of_L30 hL30
  have hN0 : (0 : ℝ) < 2 * (h : ℝ) := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  set N : ℝ := 2 * (h : ℝ) with hNdef
  set L := Real.log N with hLdef
  have hl8 : Real.log 8 = 3 * Real.log 2 := log_eight_eq'
  have hl2 := log_two_bounds
  have hl8192 : Real.log 8192 = 13 * Real.log 2 := by
    rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]; norm_num
  have hΛL : LamN N = 2 * L - Real.log 8 := rfl
  have hΛ1 : 1 ≤ LamN N := by rw [hΛL]; linarith
  obtain ⟨g1, g2, g3⟩ := gRoot_spec hΛ1
  set g := gRoot N
  have hΛ0 : 0 < LamN N := by linarith
  -- `log Λ ≤ log 8192 + Λ/8192 - 1` (tangent line at `8192`)
  have htan := Real.log_le_sub_one_of_pos (show 0 < LamN N / 8192 by positivity)
  rw [Real.log_div hΛ0.ne' (by norm_num)] at htan
  have hg : 1.996 * L ≤ g := by
    rw [hΛL] at g1 htan
    linarith
  have hg0 : 0 < g := by linarith
  have hL0 : 0 < L := by linarith
  -- the main term exceeds the error
  have hM : 20822 * L / N < (2 * g * L + g ^ 2 / 2) / (N * (1 + 1 / g)) := by
    have hgg : 1 + 1 / g ≤ 1 + 1 / (1.996 * L) := by
      have : 1 / g ≤ 1 / (1.996 * L) := one_div_le_one_div_of_le (by positivity) hg
      linarith
    rw [div_lt_div_iff₀ hN0 (by positivity)]
    have h1 : 5.984 * L ^ 2 ≤ 2 * g * L + g ^ 2 / 2 := by
      nlinarith [mul_le_mul hg hg (by positivity) hg0.le]
    have h2 : 20822 * L * (N * (1 + 1 / g)) ≤ 20822 * L * (N * (1 + 1 / (1.996 * L))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hgg hN0.le
    have h3 : 20822 * L * (N * (1 + 1 / (1.996 * L))) = N * (20822 * L + 20822 / 1.996) := by
      field_simp
    have h5 : 20822 * L + 20822 / 1.996 < 5.984 * L ^ 2 := by nlinarith
    have h4 : N * (20822 * L + 20822 / 1.996) < 5.984 * L ^ 2 * N := by
      nlinarith [mul_lt_mul_of_pos_left h5 hN0]
    nlinarith
  linarith

end Kagey131.PaperD.U4
