import PaperD.EJPAnalyticThresholdWeights
import PaperD.EJPAnalyticThresholdSeriesMoments

/-!
# Root-weight factorial moments and bounds for the actual K derivative

The actual-series Euler identities are supplied by `SeriesMoments`. This file
uses them with the finite geometric-polynomial derivative from `Weights`.
-/

open Set Filter
open scoped Topology

namespace Kagey131.PaperD.Modes.AnalyticThreshold.Weights

open Series

/-- The three ODE identities for the actual normalized root weights. -/
theorem factorial_moment_identities {a Y : ℝ} (ha : 1 / 2 < a)
    (hY0 : 0 ≤ Y) (hY : Y < 1) (hroot : H a Y = 0) :
    2 * a * Series.moment a Y 1 = G Y ∧
    2 * a * Series.moment a Y 2 = Y * deriv G Y - (2 * a - 1) * Series.moment a Y 1 ∧
    2 * a * (Series.moment a Y 3 + 2 * Series.moment a Y 2) =
      Y ^ 2 * deriv (deriv G) Y + Series.moment a Y 2 := by
  have hy : |Y| < 1 := by rwa [abs_of_nonneg hY0]
  exact ⟨Series.moment_first ha hy hroot, Series.moment_second ha hy,
    Series.moment_third ha hy⟩

theorem cast_descFactorial_two (k : ℕ) :
    (k.descFactorial 2 : ℝ) = (k : ℝ) * (k - 1) := by
  cases k with
  | zero => norm_num
  | succ k => simp [Nat.descFactorial_succ, Nat.cast_add, Nat.cast_mul]; ring

theorem Ku_le_moment {a Y u : ℝ} (ha : 1 / 2 < a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) : Ku a Y u ≤ Series.moment a Y 2 / 2 := by
  rw [Series.moment, div_eq_mul_inv, ← tsum_mul_right]
  apply (summable_Ku ha hY0 hY hu hu1).tsum_le_tsum _
    ((Series.summable_moment ha (by rwa [abs_of_nonneg hY0]) 2).mul_right (2 : ℝ)⁻¹)
  intro k
  rw [cast_descFactorial_two]
  have h := mul_le_mul_of_nonneg_left (geomU_le hu hu1 k) (weight_nonneg ha hY0 k)
  change weight a Y k * geomU k u ≤ _
  change weight a Y k * geomU k u ≤ (k : ℝ) * (k - 1) * weight a Y k * (2 : ℝ)⁻¹
  nlinarith only [h]

/-- The strict rational bound, instantiated with the actual Ku series. -/
theorem Ku_lt {a Y u : ℝ} (ha : 2 / 3 ≤ a) (hY0 : 0 ≤ Y) (hY : Y ≤ 2 / 3)
    (_hroot : H a Y = 0) (hu : 0 ≤ u) (hu1 : u ≤ 1) : Ku a Y u < 21 / 32 := by
  have ha0 : 1 / 2 < a := by linarith
  have hY1 : Y < 1 := by linarith
  have hy : |Y| < 1 := by rwa [abs_of_nonneg hY0]
  exact moment_Ku_lt ha hY (G_pos hY0 hY1).le (Series.moment_nonneg ha0 hY0 1)
    (G_sq hy) (Gp_identity hy) (Series.moment_second ha0 hy)
    (Ku_le_moment ha0 hY0 hY1 hu hu1)

theorem K_le_moment {a Y u : ℝ} (ha : 1 / 2 < a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) : K a Y u ≤ Series.moment a Y 1 := by
  apply (summable_K ha hY0 hY hu hu1).tsum_le_tsum _
    (Series.summable_moment ha (by rwa [abs_of_nonneg hY0]) 1)
  intro k
  simpa [Nat.descFactorial_one, weight, Series.weight, mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left (geom_le hu hu1 k) (weight_nonneg ha hY0 k)

theorem K_at_one {a Y : ℝ} : K a Y 1 = Series.moment a Y 1 := by
  apply tsum_congr
  intro k
  simp [geom, Series.moment, Nat.descFactorial_one, weight, Series.weight, mul_comm]

theorem Ku_at_one {a Y : ℝ} : Ku a Y 1 = Series.moment a Y 2 / 2 := by
  rw [Series.moment, div_eq_mul_inv, ← tsum_mul_right]
  apply tsum_congr
  intro k
  simp only [geomU, one_pow, mul_one, sum_range_cast, cast_descFactorial_two]
  dsimp [weight, Series.weight]
  ring

/-- Normal convergence also controls the endpoint u=1. -/
theorem continuousOn_K {a Y : ℝ} (ha : 1 / 2 < a) (hY0 : 0 ≤ Y) (hY : Y < 1) :
    ContinuousOn (K a Y) (Icc (0 : ℝ) 1) := by
  apply continuousOn_tsum (fun k => ?_) (summable_weight_pow ha hY0 hY 1)
    (fun k u hu => ?_)
  · have hg : Continuous (geom k) := continuous_iff_continuousAt.mpr
      (fun u => (hasDerivAt_geom k u).continuousAt)
    exact (continuous_const.mul hg).continuousOn
  · rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (weight_nonneg ha hY0 k) (geom_nonneg hu.1 k))]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (geom_le hu.1 hu.2 k)
      (weight_nonneg ha hY0 k)

end Kagey131.PaperD.Modes.AnalyticThreshold.Weights
