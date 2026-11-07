import PaperD.EJPAnalyticThresholdSeriesRoots
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Endpoint convergence of the actual H series

The summability comparison is obtained from telescoping central-binomial
coefficients. Root construction does not depend on this endpoint argument.
-/

open Set Filter FormalMultilinearSeries
open scoped Topology ENNReal

namespace Kagey131.PaperD.Modes.AnalyticThreshold.Series

theorem sum_coeff_one (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), coeff 1 k) = 1 - chi n := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ, hn, coeff_one_succ]
    ring

theorem summable_coeff_one : Summable (coeff 1) := by
  apply summable_of_sum_range_le (fun k => coeff_nonneg (by norm_num) k) (c := 1)
  intro n
  rcases n with _ | n
  · simp
  · rw [sum_coeff_one]
    linarith [chi_pos n]

theorem coeff_le_multiple_one {a : ℝ} (ha : 1 / 2 < a) (k : ℕ) :
    coeff a k ≤ (2 / (2 * a - 1)) * coeff 1 k := by
  rcases k with _ | k
  · simp
  · have hk : (1 : ℝ) ≤ k.succ := by exact_mod_cast Nat.succ_pos k
    have ha0 : 0 < 2 * a - 1 := by linarith
    have hk0 : 0 < 2 * (k.succ : ℝ) - 1 := by linarith
    rw [coeff_of_pos (Nat.succ_pos k), coeff_of_pos (Nat.succ_pos k)]
    have hden : (2 * a - 1) * (2 * (k.succ : ℝ) - 1) / 2 ≤ 2 * a * k.succ - 1 := by
      nlinarith
    calc
      _ ≤ chi k.succ / ((2 * a - 1) * (2 * (k.succ : ℝ) - 1) / 2) :=
        div_le_div_of_nonneg_left (chi_pos _).le (by positivity) hden
      _ = _ := by field_simp

/-- The coefficient series converges even at y=1, for every a>1/2. -/
theorem summable_coeff_endpoint {a : ℝ} (ha : 1 / 2 < a) : Summable (coeff a) :=
  Summable.of_nonneg_of_le (coeff_nonneg ha) (coeff_le_multiple_one ha)
    (summable_coeff_one.mul_left (2 / (2 * a - 1)))

theorem summable_coeff_closed {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| ≤ 1) :
    Summable (fun k : ℕ => coeff a k * y ^ k) := by
  apply (summable_coeff_endpoint ha).of_norm_bounded
  intro k
  rw [norm_mul, Real.norm_of_nonneg (coeff_nonneg ha k), norm_pow, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (coeff_nonneg ha k) (pow_le_one₀ (abs_nonneg y) hy)

theorem continuousOn_H_closed {a : ℝ} (ha : 1 / 2 < a) :
    ContinuousOn (H a) (Icc (-1) 1) := by
  have hc : ContinuousOn (fun y : ℝ => ∑' k : ℕ, coeff a k * y ^ k) (Icc (-1) 1) := by
    apply continuousOn_tsum (fun _ => by fun_prop) (summable_coeff_endpoint ha)
    intro k y hy
    rw [norm_mul, Real.norm_of_nonneg (coeff_nonneg ha k), norm_pow, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (coeff_nonneg ha k)
      (pow_le_one₀ (abs_nonneg y) (abs_le.mpr hy))
  exact continuousOn_const.sub hc

end Kagey131.PaperD.Modes.AnalyticThreshold.Series
