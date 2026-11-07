import PaperD.EJPAnalyticThresholdBounds
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Data.Nat.Choose.Central

/-!
# The actual central-binomial H series

The coefficients in this file are the explicit coefficients from the analytic
appendix. No differential equation or generating-function identity is assumed.
The parameter range for H is `1 / 2 < a`.
-/

open Set Filter FormalMultilinearSeries
open scoped Topology ENNReal

namespace Kagey131.PaperD.Modes.AnalyticThreshold.Series

/-- `χₖ = choose (2k) k / 4^k`. -/
noncomputable def chi (k : ℕ) : ℝ := (Nat.centralBinom k : ℝ) / 4 ^ k

theorem chi_eq_choose (k : ℕ) : chi k = (Nat.choose (2 * k) k : ℝ) / 4 ^ k := rfl

@[simp] theorem chi_zero : chi 0 = 1 := by norm_num [chi]
@[simp] theorem chi_one : chi 1 = 1 / 2 := by norm_num [chi, Nat.centralBinom]
@[simp] theorem chi_two : chi 2 = 3 / 8 := by norm_num [chi, Nat.centralBinom, Nat.choose]
@[simp] theorem chi_three : chi 3 = 5 / 16 := by norm_num [chi, Nat.centralBinom, Nat.choose]
@[simp] theorem chi_four : chi 4 = 35 / 128 := by norm_num [chi, Nat.centralBinom, Nat.choose]

theorem chi_pos (k : ℕ) : 0 < chi k :=
  div_pos (by exact_mod_cast Nat.centralBinom_pos k) (by positivity)

theorem chi_le_one (k : ℕ) : chi k ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ) < 4 ^ k)).2
  exact_mod_cast Nat.centralBinom_le_four_pow k

theorem chi_recurrence (k : ℕ) :
    2 * (k + 1 : ℝ) * chi (k + 1) = (2 * k + 1) * chi k := by
  have h : (k + 1 : ℝ) * (Nat.centralBinom (k + 1) : ℝ) =
      2 * (2 * k + 1) * (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  dsimp [chi]
  rw [pow_succ]
  field_simp
  nlinarith

theorem chi_succ_lt (k : ℕ) : chi (k + 1) < chi k := by
  have h := chi_recurrence k
  have hp := chi_pos k
  nlinarith

theorem chi_antitone : Antitone chi := antitone_nat_of_succ_le (fun k => (chi_succ_lt k).le)

/-- Zero at index zero, so that a single natural-indexed sum represents k≥1. -/
noncomputable def coeff (a : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else chi k / (2 * a * k - 1)

@[simp] theorem coeff_zero (a : ℝ) : coeff a 0 = 0 := by simp [coeff]

theorem coeff_of_pos {k : ℕ} (hk : 0 < k) (a : ℝ) :
    coeff a k = chi k / (2 * a * k - 1) := by simp [coeff, hk.ne']

theorem denominator_pos {a : ℝ} (ha : 1 / 2 < a) {k : ℕ} (hk : 0 < k) :
    0 < 2 * a * k - 1 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

theorem coeff_pos {a : ℝ} (ha : 1 / 2 < a) {k : ℕ} (hk : 0 < k) :
    0 < coeff a k := by
  rw [coeff_of_pos hk]
  exact div_pos (chi_pos k) (denominator_pos ha hk)

theorem coeff_nonneg {a : ℝ} (ha : 1 / 2 < a) (k : ℕ) : 0 ≤ coeff a k := by
  rcases k with _ | k
  · simp
  · exact (coeff_pos ha (Nat.succ_pos k)).le

theorem coeff_le {a : ℝ} (ha : 1 / 2 < a) (k : ℕ) :
    coeff a k ≤ (2 * a - 1)⁻¹ := by
  rcases k with _ | k
  · simp only [coeff_zero]; exact inv_nonneg.mpr (by linarith)
  · rw [coeff_of_pos (Nat.succ_pos k), ← one_div]
    have hk : (1 : ℝ) ≤ k.succ := by exact_mod_cast Nat.succ_pos k
    apply (div_le_div_iff₀ (denominator_pos ha (Nat.succ_pos k)) (by linarith)).2
    have := chi_le_one (k + 1)
    have hm := mul_le_mul_of_nonneg_right this (show 0 ≤ 2 * a - 1 by linarith)
    nlinarith

/-- Scalar power series, used to state termwise differentiation precisely. -/
noncomputable def powerSum (c : ℕ → ℝ) (y : ℝ) : ℝ := ∑' k, c k * y ^ k

/-- H from the manuscript, with its constant term separated. -/
noncomputable def H (a y : ℝ) : ℝ := 1 - powerSum (coeff a) y

/-- The positive central-binomial generating series. -/
noncomputable def G (y : ℝ) : ℝ := powerSum chi y

theorem summable_of_bounded_coeff {c : ℕ → ℝ} {C y : ℝ}
    (hc : ∀ k, ‖c k‖ ≤ C) (hy : |y| < 1) : Summable (fun k => c k * y ^ k) := by
  apply ((summable_geometric_of_lt_one (abs_nonneg y) hy).mul_left C).of_norm_bounded
  intro k
  simp only [norm_mul, norm_pow, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hc k) (pow_nonneg (abs_nonneg y) k)

theorem summable_chi {y : ℝ} (hy : |y| < 1) : Summable (fun k => chi k * y ^ k) := by
  apply summable_of_bounded_coeff (C := 1) _ hy
  intro k
  simpa only [Real.norm_eq_abs, abs_of_pos (chi_pos k)] using chi_le_one k

theorem summable_coeff {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) :
    Summable (fun k => coeff a k * y ^ k) := by
  apply summable_of_bounded_coeff (C := (2 * a - 1)⁻¹) _ hy
  intro k
  simpa only [Real.norm_eq_abs, abs_of_nonneg (coeff_nonneg ha k)] using coeff_le ha k

@[simp] theorem powerSum_zero (c : ℕ → ℝ) : powerSum c 0 = c 0 := by
  simp [powerSum, zero_pow_eq]

@[simp] theorem H_zero (a : ℝ) : H a 0 = 1 := by simp [H]
@[simp] theorem G_zero : G 0 = 1 := by simp [G]

/-- Coefficients of the termwise derivative, including the shift of indices. -/
noncomputable def derivCoeff (c : ℕ → ℝ) (k : ℕ) : ℝ := (k + 1 : ℝ) * c (k + 1)

theorem scalar_derivSeries (c : ℕ → ℝ) :
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).compFormalMultilinearSeries
      (ofScalars ℝ c).derivSeries = ofScalars ℝ (derivCoeff c) := by
  ext n
  change (ofScalars ℝ c).derivSeries.coeff n 1 = _
  simp [derivCoeff]

theorem radius_derivCoeff (c : ℕ → ℝ) :
    (ofScalars ℝ c).radius ≤ (ofScalars ℝ (derivCoeff c)).radius := by
  rw [← scalar_derivSeries]
  exact (ofScalars ℝ c).radius_le_radius_derivSeries.trans
    ((ofScalars ℝ c).derivSeries.radius_le_radius_continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)))

theorem radius_of_bounded_coeff {c : ℕ → ℝ} {C : ℝ} (hc : ∀ k, ‖c k‖ ≤ C) :
    1 ≤ (ofScalars ℝ c).radius := by
  simpa using (ofScalars ℝ c).le_radius_of_bound C (r := 1) (by simpa using hc)

theorem chi_radius : 1 ≤ (ofScalars ℝ chi).radius := by
  apply radius_of_bounded_coeff (C := 1)
  intro k
  simpa only [Real.norm_eq_abs, abs_of_pos (chi_pos k)] using chi_le_one k

theorem coeff_radius {a : ℝ} (ha : 1 / 2 < a) :
    1 ≤ (ofScalars ℝ (coeff a)).radius := by
  apply radius_of_bounded_coeff (C := (2 * a - 1)⁻¹)
  intro k
  simpa only [Real.norm_eq_abs, abs_of_nonneg (coeff_nonneg ha k)] using coeff_le ha k

theorem enorm_lt_radius {c : ℕ → ℝ} (hc : 1 ≤ (ofScalars ℝ c).radius)
    {y : ℝ} (hy : |y| < 1) : ‖y‖ₑ < (ofScalars ℝ c).radius := by
  apply lt_of_lt_of_le _ hc
  simpa [enorm_eq_nnnorm] using! hy

theorem summable_powerSum {c : ℕ → ℝ} {y : ℝ}
    (hy : ‖y‖ₑ < (ofScalars ℝ c).radius) : Summable (fun k => c k * y ^ k) := by
  simpa only [ofScalars_apply_eq, smul_eq_mul, mul_comm] using
    (ofScalars ℝ c).summable (by simpa using hy)

/-- Genuine termwise differentiation, valid strictly inside the convergence radius. -/
theorem hasDerivAt_powerSum {c : ℕ → ℝ} {y : ℝ}
    (hy : ‖y‖ₑ < (ofScalars ℝ c).radius) :
    HasDerivAt (powerSum c) (powerSum (derivCoeff c) y) y := by
  have h := (ofScalars ℝ c).hasFDerivAt_sum hy
  have heq : (ofScalars ℝ c).sum = powerSum c := by
    funext z
    simp [powerSum, FormalMultilinearSeries.sum, mul_comm]
  rw [heq] at h
  apply h.hasDerivAt.congr_deriv
  have hs := (ofScalars ℝ c).derivSeries.summable
    (show y ∈ Metric.eball 0 (ofScalars ℝ c).derivSeries.radius from
      by simpa using hy.trans_le (ofScalars ℝ c).radius_le_radius_derivSeries)
  change (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
    (∑' n, (ofScalars ℝ c).derivSeries n (fun _ => y)) = _
  rw [(ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).map_tsum hs]
  simp [powerSum, derivCoeff, mul_comm]

theorem hasDerivAt_H {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) :
    HasDerivAt (H a) (-powerSum (derivCoeff (coeff a)) y) y := by
  convert! (hasDerivAt_powerSum (enorm_lt_radius (coeff_radius ha) hy)).const_sub 1 using 1

theorem hasDerivAt_G {y : ℝ} (hy : |y| < 1) :
    HasDerivAt G (powerSum (derivCoeff chi) y) y :=
  hasDerivAt_powerSum (enorm_lt_radius chi_radius hy)

theorem analyticAt_powerSum {c : ℕ → ℝ} {y : ℝ}
    (hy : ‖y‖ₑ < (ofScalars ℝ c).radius) : AnalyticAt ℝ (powerSum c) y := by
  have h := (ofScalars ℝ c).hasFPowerSeriesOnBall (lt_of_le_of_lt zero_le hy)
  have hmem : y ∈ Metric.eball (0 : ℝ) (ofScalars ℝ c).radius := by simpa using hy
  have heq : (ofScalars ℝ c).sum = powerSum c := by
    funext z
    simp [powerSum, FormalMultilinearSeries.sum, mul_comm]
  rw [← heq]
  exact h.analyticAt_of_mem hmem

theorem analyticAt_H {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) :
    AnalyticAt ℝ (H a) y := by
  exact analyticAt_const.sub (analyticAt_powerSum (enorm_lt_radius (coeff_radius ha) hy))

theorem analyticAt_G {y : ℝ} (hy : |y| < 1) : AnalyticAt ℝ G y :=
  analyticAt_powerSum (enorm_lt_radius chi_radius hy)

theorem continuousOn_H {a : ℝ} (ha : 1 / 2 < a) : ContinuousOn (H a) (Ioo (-1) 1) := by
  intro y hy
  exact (hasDerivAt_H ha (abs_lt.mpr hy)).continuousAt.continuousWithinAt

/-- Euler's operator on a convergent power series. -/
theorem mul_powerSum_derivCoeff {c : ℕ → ℝ} {y : ℝ}
    (hy : ‖y‖ₑ < (ofScalars ℝ c).radius) :
    y * powerSum (derivCoeff c) y = ∑' k : ℕ, (k : ℝ) * c k * y ^ k := by
  have hs := summable_powerSum (hy.trans_le (radius_derivCoeff c))
  rw [powerSum, ← tsum_mul_left]
  have hzero : (0 : ℝ) * c 0 * y ^ 0 = 0 := by ring
  have hshift : (fun n : ℕ => y * (derivCoeff c n * y ^ n)) =
      (fun n : ℕ => (n + 1 : ℝ) * c (n + 1) * y ^ (n + 1)) := by
    funext n
    simp only [derivCoeff, pow_succ]
    ring
  rw [hshift]
  have hsum : Summable (fun k : ℕ => (k : ℝ) * c k * y ^ k) := by
    rw [← summable_nat_add_iff 1]
    convert! hs.mul_left y using 1
    funext n
    simp only [derivCoeff, Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one] using
    (hsum.sum_add_tsum_nat_add 1)

theorem summable_euler {c : ℕ → ℝ} {y : ℝ}
    (hy : ‖y‖ₑ < (ofScalars ℝ c).radius) :
    Summable (fun k : ℕ => (k : ℝ) * c k * y ^ k) := by
  rw [← summable_nat_add_iff 1]
  have hs := (summable_powerSum (hy.trans_le (radius_derivCoeff c))).mul_left y
  convert! hs using 1
  funext n
  simp only [derivCoeff, Nat.cast_add, Nat.cast_one, pow_succ]
  ring

/-- The central-binomial recurrence gives the generating-function ODE. -/
theorem G_series_ode {y : ℝ} (hy : |y| < 1) :
    2 * (1 - y) * powerSum (derivCoeff chi) y = G y := by
  have hr := enorm_lt_radius chi_radius hy
  have hs := summable_powerSum hr
  have hd := summable_powerSum (hr.trans_le (radius_derivCoeff chi))
  have he := summable_euler hr
  have h : 2 * powerSum (derivCoeff chi) y =
      2 * (y * powerSum (derivCoeff chi) y) + G y := by
    rw [mul_powerSum_derivCoeff hr]
    change 2 * (∑' n, derivCoeff chi n * y ^ n) =
      2 * (∑' n : ℕ, (n : ℝ) * chi n * y ^ n) + ∑' n, chi n * y ^ n
    rw [← tsum_mul_left, ← tsum_mul_left, ← (he.mul_left 2).tsum_add hs]
    apply tsum_congr
    intro n
    have hn := chi_recurrence n
    dsimp [derivCoeff]
    nlinarith [congrArg (fun t : ℝ => t * y ^ n) hn]
  linarith

/-- H's differential equation, before identifying the right side with a square root. -/
theorem H_series_ode {a y : ℝ} (ha : 1 / 2 < a) (hy : |y| < 1) :
    H a y - 2 * a * y * deriv (H a) y = G y := by
  have hr := enorm_lt_radius (coeff_radius ha) hy
  rw [(hasDerivAt_H ha hy).deriv]
  have hcoeff : ∀ k : ℕ, (2 * a * k - 1) * coeff a k =
      if k = 0 then 0 else chi k := by
    intro k
    rcases k with _ | k
    · simp
    · rw [coeff_of_pos (Nat.succ_pos k), if_neg (Nat.succ_ne_zero k)]
      have hd := (denominator_pos ha (Nat.succ_pos k)).ne'
      simp only [Nat.cast_succ] at hd ⊢
      field_simp
  have hs := summable_coeff ha hy
  have he := summable_euler hr
  have hmain : 2 * a * (y * powerSum (derivCoeff (coeff a)) y) - powerSum (coeff a) y =
      G y - 1 := by
    rw [mul_powerSum_derivCoeff hr]
    change 2 * a * (∑' k : ℕ, (k : ℝ) * coeff a k * y ^ k) -
      (∑' k, coeff a k * y ^ k) = G y - 1
    rw [← tsum_mul_left, ← (he.mul_left (2 * a)).tsum_sub hs]
    have hg : (∑' k : ℕ, (if k = 0 then 0 else chi k) * y ^ k) = G y - 1 := by
      have hsg := summable_chi hy
      change _ = (∑' k : ℕ, chi k * y ^ k) - 1
      rw [← hsg.sum_add_tsum_nat_add 1]
      simp only [Finset.sum_range_one, chi_zero, pow_zero, mul_one]
      have hf : Summable (fun k : ℕ => (if k = 0 then 0 else chi k) * y ^ k) := by
        rw [← summable_nat_add_iff 1]
        simpa using (summable_nat_add_iff 1).mpr hsg
      rw [← hf.sum_add_tsum_nat_add 1]
      simp
    rw [← hg]
    apply tsum_congr
    intro k
    rw [← hcoeff k]
    ring
  dsimp [H]
  linarith

theorem G_sq {y : ℝ} (hy : |y| < 1) : (1 - y) * G y ^ 2 = 1 := by
  let F : ℝ → ℝ := fun x => (1 - x) * G x ^ 2
  have hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt F 0 x := by
    intro x hx
    have habs := abs_lt.mpr hx
    have h := ((hasDerivAt_id x).const_sub 1).mul ((hasDerivAt_G habs).pow 2)
    convert! h using 1
    have he := congrArg (fun t : ℝ => t * G x) (G_series_ode habs)
    dsimp at he ⊢
    nlinarith
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-1 : ℝ) 1).isPreconnected
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv) (abs_lt.mp hy) (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1)
  simpa [F] using hconst

theorem G_pos {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 1) : 0 < G y := by
  have hn : 0 ≤ G y := tsum_nonneg (fun k => mul_nonneg (chi_pos k).le (pow_nonneg hy0 k))
  have hs := G_sq (abs_lt.mpr ⟨by linarith, hy⟩)
  nlinarith

/-- Identification of the binomial generating series, derived from its recurrence. -/
theorem G_eq_inv_sqrt {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 1) :
    G y = (Real.sqrt (1 - y))⁻¹ := by
  have hp : 0 < 1 - y := by linarith
  have hsq := Real.sq_sqrt hp.le
  have hG := G_pos hy0 hy
  have hgsq := G_sq (abs_lt.mpr ⟨by linarith, hy⟩)
  have hs := Real.sqrt_pos.mpr hp
  have hprod : G y * Real.sqrt (1 - y) = 1 := by
    have he : (G y * Real.sqrt (1 - y)) ^ 2 = 1 := by
      rw [mul_pow, hsq]
      nlinarith
    nlinarith [mul_pos hG hs]
  rw [← one_div]
  exact (eq_div_iff hs.ne').2 hprod

/-- The manuscript's H ODE with the explicit inverse square root. -/
theorem H_ode {a y : ℝ} (ha : 1 / 2 < a) (hy0 : 0 ≤ y) (hy : y < 1) :
    H a y - 2 * a * y * deriv (H a) y = (Real.sqrt (1 - y))⁻¹ := by
  rw [H_series_ode ha (abs_lt.mpr ⟨by linarith, hy⟩), G_eq_inv_sqrt hy0 hy]

end Kagey131.PaperD.Modes.AnalyticThreshold.Series
