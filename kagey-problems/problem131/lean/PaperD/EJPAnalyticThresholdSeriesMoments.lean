import PaperD.EJPAnalyticThresholdSeries

/-!
# Falling-factorial moments of the actual root weights

The moment sums are defined for any point inside the convergence interval;
normalization is subsequently obtained by substituting a root of H.
-/

open Set Filter FormalMultilinearSeries
open scoped Topology ENNReal

namespace Kagey131.PaperD.Modes.AnalyticThreshold.Series

theorem radius_iter_derivCoeff (c : ℕ → ℝ) (j : ℕ) :
    (ofScalars ℝ c).radius ≤ (ofScalars ℝ (derivCoeff^[j] c)).radius := by
  induction j with
  | zero => exact le_rfl
  | succ j hj =>
    rw [Function.iterate_succ_apply']
    exact hj.trans (radius_derivCoeff _)

theorem iter_derivCoeff_apply (c : ℕ → ℝ) (j n : ℕ) :
    (derivCoeff^[j] c) n = ((n + j).descFactorial j : ℝ) * c (n + j) := by
  induction j generalizing n with
  | zero => simp
  | succ j hj =>
    rw [Function.iterate_succ_apply', derivCoeff, hj]
    rw [Nat.descFactorial_succ]
    have he : n + (j + 1) - j = n + 1 := by omega
    rw [he, Nat.cast_mul]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show n + 1 + j = n + (j + 1) by omega]
    ring

/-- Every falling-factorial moment converges, proved from the differentiated power series. -/
theorem summable_factorial {c : ℕ → ℝ} {y : ℝ}
    (hy : ‖y‖ₑ < (ofScalars ℝ c).radius) (j : ℕ) :
    Summable (fun k : ℕ => (k.descFactorial j : ℝ) * c k * y ^ k) := by
  rw [← summable_nat_add_iff j]
  have hs := (summable_powerSum (hy.trans_le (radius_iter_derivCoeff c j))).mul_left (y ^ j)
  convert! hs using 1
  funext n
  rw [iter_derivCoeff_apply, pow_add]
  ring

theorem factorial_powerSum {c : ℕ → ℝ} {y : ℝ}
    (hy : ‖y‖ₑ < (ofScalars ℝ c).radius) (j : ℕ) :
    (∑' k : ℕ, (k.descFactorial j : ℝ) * c k * y ^ k) =
      y ^ j * powerSum (derivCoeff^[j] c) y := by
  have hs := summable_factorial hy j
  rw [← hs.sum_add_tsum_nat_add j]
  have hz : (∑ k ∈ Finset.range j, (k.descFactorial j : ℝ) * c k * y ^ k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [(Nat.descFactorial_eq_zero_iff_lt).2 (Finset.mem_range.mp hk)]
    simp
  rw [hz, zero_add, powerSum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [iter_derivCoeff_apply, pow_add]
  ring

/-- The actual weights χₖ yᵏ/(2ak−1), with the harmless zero index included. -/
noncomputable def weight (a y : ℝ) (k : ℕ) : ℝ := coeff a k * y ^ k

/-- Actual falling-factorial moment sums; no moment identity is part of the definition. -/
noncomputable def moment (a y : ℝ) (j : ℕ) : ℝ :=
  ∑' k : ℕ, (k.descFactorial j : ℝ) * weight a y k

theorem summable_moment {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) (j : ℕ) :
    Summable (fun k : ℕ => (k.descFactorial j : ℝ) * weight a y k) := by
  simpa only [weight, mul_assoc] using summable_factorial (enorm_lt_radius (coeff_radius ha) hy) j

theorem moment_eq_derivSeries {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) (j : ℕ) :
    moment a y j = y ^ j * powerSum (derivCoeff^[j] (coeff a)) y := by
  simpa only [moment, weight, mul_assoc] using factorial_powerSum (enorm_lt_radius (coeff_radius ha) hy) j

theorem moment_nonneg {a y : ℝ} (ha : 1 / 2 < a) (hy : 0 ≤ y) (j : ℕ) :
    0 ≤ moment a y j := by
  apply tsum_nonneg
  intro k
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (coeff_nonneg ha _) (pow_nonneg hy k))

theorem weight_normalized {a y : ℝ} (hroot : H a y = 0) : ∑' k : ℕ, weight a y k = 1 := by
  dsimp [H, powerSum] at hroot
  dsimp [weight]
  linarith

theorem coeff_denominator {a : ℝ} (ha : 1 / 2 < a) {k : ℕ} (hk : 0 < k) :
    (2 * a * k - 1) * coeff a k = chi k := by
  rw [coeff_of_pos hk]
  have hd := (denominator_pos ha hk).ne'
  field_simp

theorem factorial_coeff_identity {a : ℝ} (ha : 1 / 2 < a) {j : ℕ} (hj : 0 < j) (k : ℕ) :
    2 * a * (k.descFactorial (j + 1) : ℝ) * coeff a k +
      (2 * a * j - 1) * (k.descFactorial j : ℝ) * coeff a k =
        (k.descFactorial j : ℝ) * chi k := by
  by_cases hkj : j ≤ k
  · have hk : 0 < k := hj.trans_le hkj
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hkj]
    calc
      _ = (k.descFactorial j : ℝ) * ((2 * a * k - 1) * coeff a k) := by ring
      _ = _ := by rw [coeff_denominator ha hk]
  · have hlt : k < j := Nat.lt_of_not_ge hkj
    rw [(Nat.descFactorial_eq_zero_iff_lt).2 hlt,
      (Nat.descFactorial_eq_zero_iff_lt).2 (hlt.trans (Nat.lt_succ_self j))]
    simp

/-- The coefficient denominator yields the full factorial-moment recurrence. -/
theorem moment_recurrence {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1)
    {j : ℕ} (hj : 0 < j) :
    2 * a * moment a y (j + 1) + (2 * a * j - 1) * moment a y j =
      y ^ j * powerSum (derivCoeff^[j] chi) y := by
  have hs₁ := (summable_moment ha hy (j + 1)).mul_left (2 * a)
  have hs₂ := (summable_moment ha hy j).mul_left (2 * a * j - 1)
  rw [← factorial_powerSum (enorm_lt_radius chi_radius hy) j]
  change 2 * a * (∑' k, (k.descFactorial (j + 1) : ℝ) * weight a y k) +
    (2 * a * j - 1) * (∑' k, (k.descFactorial j : ℝ) * weight a y k) = _
  rw [← tsum_mul_left, ← tsum_mul_left, ← hs₁.tsum_add hs₂]
  apply tsum_congr
  intro k
  simp only [weight]
  have h := congrArg (fun t : ℝ => t * y ^ k) (factorial_coeff_identity ha hj k)
  convert! h using 1 <;> ring

theorem moment_first {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) (hroot : H a y = 0) :
    2 * a * moment a y 1 = G y := by
  have h := H_series_ode ha hy
  rw [hroot, (hasDerivAt_H ha hy).deriv] at h
  rw [moment_eq_derivSeries ha hy 1]
  simpa [G, Function.iterate_one, pow_one, mul_assoc] using h

theorem moment_second {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) :
    2 * a * moment a y 2 = y * deriv G y - (2 * a - 1) * moment a y 1 := by
  have h := moment_recurrence ha hy (j := 1) (by decide)
  rw [(hasDerivAt_G hy).deriv]
  simpa only [Nat.cast_one, mul_one, Function.iterate_one, pow_one, eq_sub_iff_add_eq] using h

theorem deriv_G_eq {y : ℝ} (hy : |y| < 1) : deriv G y = powerSum (derivCoeff chi) y :=
  (hasDerivAt_G hy).deriv

theorem hasDerivAt_deriv_G {y : ℝ} (hy : |y| < 1) :
    HasDerivAt (deriv G) (powerSum (derivCoeff (derivCoeff chi)) y) y := by
  have h := hasDerivAt_powerSum
    ((enorm_lt_radius chi_radius hy).trans_le (radius_derivCoeff chi))
  apply h.congr_of_eventuallyEq
  filter_upwards [IsOpen.mem_nhds isOpen_Ioo (abs_lt.mp hy)] with z hz
  exact deriv_G_eq (abs_lt.mpr hz)

theorem moment_third {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) :
    2 * a * (moment a y 3 + 2 * moment a y 2) =
      y ^ 2 * deriv (deriv G) y + moment a y 2 := by
  have h := moment_recurrence ha hy (j := 2) (by decide)
  rw [(hasDerivAt_deriv_G hy).deriv]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Nat.cast_ofNat] at h
  linarith

theorem Gp_identity {y : ℝ} (hy : |y| < 1) : 2 * (1 - y) * deriv G y = G y := by
  rw [deriv_G_eq hy]
  exact G_series_ode hy

theorem Gpp_identity {y : ℝ} (hy : |y| < 1) :
    4 * (1 - y) ^ 2 * deriv (deriv G) y = 3 * G y := by
  have hleft := (((hasDerivAt_id y).const_sub 1).const_mul 2).mul (hasDerivAt_deriv_G hy)
  have heq : (fun x : ℝ => 2 * (1 - x) * deriv G x) =ᶠ[𝓝 y] G := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo (abs_lt.mp hy)] with z hz
    exact Gp_identity (abs_lt.mpr hz)
  have hd := (hleft.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_G hy)
  have hg := Gp_identity hy
  rw [← deriv_G_eq hy, ← (hasDerivAt_deriv_G hy).deriv] at hd
  have hs := congrArg (fun t : ℝ => t * (2 * (1 - y))) hd
  dsimp at hs
  nlinarith

end Kagey131.PaperD.Modes.AnalyticThreshold.Series
