import PaperD.EJPAnalyticThresholdSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Actual root weights and the rescaled H kernel

All weights use `Series.coeff`, including its zero coefficient at index zero.
The root is an explicit argument so the identities also apply before choosing
the canonical root. Normalization follows from `Series.H a Y = 0`.
-/

open Set Filter FormalMultilinearSeries
open scoped Topology ENNReal

namespace Kagey131.PaperD.Modes.AnalyticThreshold.Weights

open Series

noncomputable def weight (a Y : ℝ) (k : ℕ) : ℝ := coeff a k * Y ^ k

noncomputable def geom (k : ℕ) (u : ℝ) : ℝ := ∑ j ∈ Finset.range k, u ^ j

noncomputable def geomU (k : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, (j : ℝ) * u ^ (j - 1)

noncomputable def K (a Y u : ℝ) : ℝ := ∑' k, weight a Y k * geom k u

noncomputable def Ku (a Y u : ℝ) : ℝ := ∑' k, weight a Y k * geomU k u

@[simp] theorem weight_zero (a Y : ℝ) : weight a Y 0 = 0 := by simp [weight]

theorem weight_nonneg {a Y : ℝ} (ha : 1 / 2 < a) (hY : 0 ≤ Y) (k : ℕ) :
    0 ≤ weight a Y k := mul_nonneg (coeff_nonneg ha k) (pow_nonneg hY k)

theorem summable_weight {a Y : ℝ} (ha : 1 / 2 < a) (hY : |Y| < 1) :
    Summable (weight a Y) := summable_coeff ha hY

theorem sum_weight_eq_one {a Y : ℝ} (hroot : H a Y = 0) :
    ∑' k, weight a Y k = 1 := by
  dsimp [H, powerSum] at hroot
  dsimp [weight]
  linarith

/-- Every polynomial moment of the actual weights is absolutely summable. -/
theorem summable_weight_pow {a Y : ℝ} (ha : 1 / 2 < a) (hY0 : 0 ≤ Y)
    (hY : Y < 1) (m : ℕ) : Summable (fun k : ℕ => (k : ℝ) ^ m * weight a Y k) := by
  have hs := (summable_pow_mul_geometric_of_norm_lt_one m
    (show ‖Y‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hY0])).mul_left
      ((2 * a - 1)⁻¹)
  apply hs.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
    (weight_nonneg ha hY0 k))]
  dsimp [weight]
  have h := mul_le_mul_of_nonneg_left (coeff_le ha k)
    (show 0 ≤ (k : ℝ) ^ m * Y ^ k by positivity)
  nlinarith only [h]

theorem geom_nonneg {u : ℝ} (hu : 0 ≤ u) (k : ℕ) : 0 ≤ geom k u :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg hu _)

theorem geom_le {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    geom k u ≤ k := by
  calc
    _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) :=
      Finset.sum_le_sum (fun _ _ => pow_le_one₀ hu hu1)
    _ = k := by simp

theorem one_le_geom {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : 0 < k) :
    1 ≤ geom k u := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.range k) => pow_nonneg hu j)
    (show 0 ∈ Finset.range k by simpa using hk)
  simpa [geom] using h

theorem summable_K {a Y u : ℝ} (ha : 1 / 2 < a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Summable (fun k => weight a Y k * geom k u) := by
  apply (summable_weight_pow ha hY0 hY 1).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_nonneg ha hY0 k) (geom_nonneg hu k))]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (geom_le hu hu1 k) (weight_nonneg ha hY0 k)

theorem one_le_K {a Y u : ℝ} (ha : 1 / 2 < a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hroot : H a Y = 0) (hu : 0 ≤ u) (hu1 : u ≤ 1) : 1 ≤ K a Y u := by
  rw [← sum_weight_eq_one hroot]
  apply (summable_weight ha (by rwa [abs_of_nonneg hY0])).tsum_le_tsum _
    (summable_K ha hY0 hY hu hu1)
  intro k
  rcases k with _ | k
  · simp
  · simpa using mul_le_mul_of_nonneg_left (one_le_geom hu (Nat.succ_pos k))
      (weight_nonneg ha hY0 (k + 1))

/-- The defining factorization is proved by summing finite geometric identities. -/
theorem H_mul_eq {a Y u : ℝ} (ha : 1 / 2 < a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hroot : H a Y = 0) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    H a (Y * u) = (1 - u) * K a Y u := by
  have hyu : |Y * u| < 1 := by
    rw [abs_of_nonneg (mul_nonneg hY0 hu)]
    exact (mul_le_of_le_one_right hY0 hu1).trans_lt hY
  have hs := summable_weight ha (by rwa [abs_of_nonneg hY0])
  have hsu := summable_coeff ha hyu
  rw [K, ← tsum_mul_left]
  have heq : (fun k => (1 - u) * (weight a Y k * geom k u)) =
      (fun k => weight a Y k - coeff a k * (Y * u) ^ k) := by
    funext k
    have hg := geom_sum_mul_neg u k
    dsimp [geom, weight] at *
    rw [mul_pow]
    nlinarith only [congrArg (fun x : ℝ => coeff a k * Y ^ k * x) hg]
  rw [heq, hs.tsum_sub hsu, sum_weight_eq_one hroot]
  rfl

theorem K_eq_div {a Y u : ℝ} (ha : 1 / 2 < a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hroot : H a Y = 0) (hu : 0 ≤ u) (hu1 : u < 1) :
    K a Y u = H a (Y * u) / (1 - u) := by
  apply (eq_div_iff (by linarith : 1 - u ≠ 0)).2
  simpa [mul_comm] using (H_mul_eq ha hY0 hY hroot hu hu1.le).symm

theorem geomU_nonneg {u : ℝ} (hu : 0 ≤ u) (k : ℕ) : 0 ≤ geomU k u :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg j) (pow_nonneg hu _))

theorem sum_range_cast (k : ℕ) :
    (∑ j ∈ Finset.range k, (j : ℝ)) = (k : ℝ) * (k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k hk => rw [Finset.sum_range_succ, hk]; push_cast; ring

theorem geomU_le {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    geomU k u ≤ (k : ℝ) * (k - 1) / 2 := by
  rw [← sum_range_cast]
  exact Finset.sum_le_sum (fun j _ => mul_le_of_le_one_right (Nat.cast_nonneg j)
    (pow_le_one₀ hu hu1))

theorem geomU_le_sq {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    geomU k u ≤ (k : ℝ) ^ 2 := by
  have := geomU_le hu hu1 k
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem hasDerivAt_geom (k : ℕ) (u : ℝ) : HasDerivAt (geom k) (geomU k u) u := by
  convert! HasDerivAt.fun_sum (u := Finset.range k)
    (fun j _ => hasDerivAt_pow j u) using 1

theorem summable_Ku {a Y u : ℝ} (ha : 1 / 2 < a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Summable (fun k => weight a Y k * geomU k u) := by
  apply (summable_weight_pow ha hY0 hY 2).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (weight_nonneg ha hY0 k) (geomU_nonneg hu k))]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (geomU_le_sq hu hu1 k)
    (weight_nonneg ha hY0 k)

/-- Genuine termwise differentiation on the rescaled open interval. -/
theorem hasDerivAt_K {a Y u : ℝ} (ha : 1 / 2 < a) (hY0 : 0 ≤ Y) (hY : Y < 1)
    (hu : 0 < u) (hu1 : u < 1) : HasDerivAt (K a Y) (Ku a Y u) u := by
  apply hasDerivAt_tsum_of_isPreconnected
    (summable_weight_pow ha hY0 hY 2) isOpen_Ioo (convex_Ioo (0 : ℝ) 1).isPreconnected
    (fun k x _ => (hasDerivAt_geom k x).const_mul (weight a Y k))
    (fun k x hx => ?_) (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)
    (summable_K ha hY0 hY (by norm_num) (by norm_num)) ⟨hu, hu1⟩
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (weight_nonneg ha hY0 k) (geomU_nonneg hx.1.le k))]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (geomU_le_sq hx.1.le hx.2.le k)
    (weight_nonneg ha hY0 k)

theorem Ku_nonneg {a Y u : ℝ} (ha : 1 / 2 < a) (hY0 : 0 ≤ Y) (hu : 0 ≤ u) :
    0 ≤ Ku a Y u := tsum_nonneg (fun k =>
      mul_nonneg (weight_nonneg ha hY0 k) (geomU_nonneg hu k))

end Kagey131.PaperD.Modes.AnalyticThreshold.Weights
