import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Paper F, track FL2: the numerical facts behind `C(φ) < 1` (Corollary 2.5)

Everything here is proved from Mathlib's `Real.Gamma`, `Real.pi` bounds and kernel-checked
rational arithmetic (`norm_num`); no numerical evaluation is trusted.

* `gamma_golden_ge` : `Γ(φ) ≥ 0.8856`. Paper: "The minimum of `Γ` on `(0,∞)` is `0.8856…`
  [DLMF 5.4(iii)], so `Γ(φ) ≥ 0.8856`." We prove the instance that is used, from the
  log-convexity of `Γ` (Bohr–Mollerup, Mathlib `Real.convexOn_log_Gamma`) with the anchors
  `Γ(6) = 120`, `Γ(13/2) = (10395/64)√π`, shifted down by `Γ(x+1) = xΓ(x)`.
* `gamma_le_one_of_mem_Icc` : `Γ ≤ 1` on `[1,2]` (convexity, `Γ(1) = Γ(2) = 1`), and
  `gamma_golden_inv_sq_le` : `Γ(φ⁻²) ≤ φ²`.
* `abs_cos_golden_le` : `|cos(πφ/2)| ≤ √3/2`.
* `zeta_trapezoid` : `ζ(α) - 1/2 ≥ 1/(α-1)` for `α > 1` (trapezoid rule for the convex
  `t^(-α)`), so `ζ(φ) - 1/2 ≥ φ`.
-/

namespace Kagey131.PaperF.FL2

open Real Set Filter Topology

/-! ### Elementary bounds on `√5`, `φ`, `√3`, `√π` -/

theorem sqrt5_bounds : (2.236 : ℝ) < √5 ∧ √5 < 2.23607 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem golden_bounds : (1.618 : ℝ) < goldenRatio ∧ goldenRatio < 1.61804 := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  unfold goldenRatio
  constructor <;> linarith

theorem sqrt3_lt : √3 < (1.7321 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem sqrt_pi_gt : (1.7724 : ℝ) < √π := by
  rw [Real.lt_sqrt (by norm_num)]
  have := Real.pi_gt_d4
  nlinarith

/-! ### Rational-exponent certificates -/

/-- `r ≤ x^(p/q)` from `r^q ≤ x^p` (kernel-checkable by `norm_num` when `x, r` are rational). -/
theorem le_rpow_div_of_pow_le {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) {p q : ℕ} (hq : q ≠ 0)
    (h : r ^ q ≤ x ^ p) : r ≤ x ^ ((p : ℝ) / q) := by
  have e1 : x ^ ((p : ℝ) / q) = (x ^ p) ^ ((q : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_natCast_mul hx]
  have e2 : r = (r ^ q) ^ ((q : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hr hq).symm
  rw [e1, e2]
  exact Real.rpow_le_rpow (pow_nonneg hr _) h (by positivity)

/-- `x^(p/q) ≤ r` from `x^p ≤ r^q`. -/
theorem rpow_div_le_of_pow_le {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) {p q : ℕ} (hq : q ≠ 0)
    (h : x ^ p ≤ r ^ q) : x ^ ((p : ℝ) / q) ≤ r := by
  have e1 : x ^ ((p : ℝ) / q) = (x ^ p) ^ ((q : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_natCast_mul hx]
  have e2 : r = (r ^ q) ^ ((q : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hr hq).symm
  rw [e1, e2]
  exact Real.rpow_le_rpow (pow_nonneg hx _) h (by positivity)

/-! ### `Γ(φ) ≥ 0.8856` -/

theorem gamma_succ {x : ℝ} (hx : x ≠ 0) : Gamma (x + 1) = x * Gamma x := Real.Gamma_add_one hx

theorem gamma_six : Gamma 6 = 120 := by
  rw [show (6 : ℝ) = ((5 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]

theorem gamma_thirteen_halves : Gamma (13 / 2) = 10395 / 64 * √π := by
  have h0 := Real.Gamma_one_half_eq
  have h1 : Gamma (3 / 2) = 1 / 2 * Gamma (1 / 2) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, gamma_succ (by norm_num)]
  have h2 : Gamma (5 / 2) = 3 / 2 * Gamma (3 / 2) := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, gamma_succ (by norm_num)]
  have h3 : Gamma (7 / 2) = 5 / 2 * Gamma (5 / 2) := by
    rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, gamma_succ (by norm_num)]
  have h4 : Gamma (9 / 2) = 7 / 2 * Gamma (7 / 2) := by
    rw [show (9 / 2 : ℝ) = 7 / 2 + 1 by norm_num, gamma_succ (by norm_num)]
  have h5 : Gamma (11 / 2) = 9 / 2 * Gamma (9 / 2) := by
    rw [show (11 / 2 : ℝ) = 9 / 2 + 1 by norm_num, gamma_succ (by norm_num)]
  have h6 : Gamma (13 / 2) = 11 / 2 * Gamma (11 / 2) := by
    rw [show (13 / 2 : ℝ) = 11 / 2 + 1 by norm_num, gamma_succ (by norm_num)]
  rw [h6, h5, h4, h3, h2, h1, h0]
  ring

theorem gamma_add_five (x : ℝ) (hx : 0 < x) :
    Gamma (x + 5) = x * (x + 1) * (x + 2) * (x + 3) * (x + 4) * Gamma x := by
  have e : ∀ k : ℝ, 0 ≤ k → Gamma (x + k + 1) = (x + k) * Gamma (x + k) := fun k hk =>
    gamma_succ (by linarith)
  have h1 := e 0 le_rfl
  have h2 := e 1 zero_le_one
  have h3 := e 2 zero_le_two
  have h4 := e 3 (by norm_num)
  have h5 := e 4 (by norm_num)
  norm_num at h1 h2 h3 h4 h5
  rw [show x + 5 = x + 4 + 1 by ring, h5, show x + 4 = x + 3 + 1 by ring, h4,
    show x + 3 = x + 2 + 1 by ring, h3, show x + 2 = x + 1 + 1 by ring, h2, h1]
  ring

/-- **`Γ(φ) ≥ 0.8856`** (the instance of the minimum of `Γ` used in Corollary 2.5). -/
theorem gamma_golden_ge : (0.8856 : ℝ) ≤ Gamma goldenRatio := by
  obtain ⟨hφ1, hφ2⟩ := golden_bounds
  have hφ0 : 0 < goldenRatio := by linarith
  set z : ℝ := goldenRatio + 5 with hz
  -- log-convexity: slope from 6 to 13/2 is at most slope from 13/2 to φ+5
  have hconv := Real.convexOn_log_Gamma.slope_mono_adjacent (x := 6) (y := 13 / 2) (z := z)
    (by norm_num [mem_Ioi]) (by simp only [mem_Ioi]; linarith) (by norm_num) (by linarith)
  simp only [Function.comp] at hconv
  have hG6 : 0 < Gamma 6 := Real.Gamma_pos_of_pos (by norm_num)
  have hGy : 0 < Gamma (13 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have hGz : 0 < Gamma z := Real.Gamma_pos_of_pos (by linarith)
  set t : ℝ := 2 * (z - 13 / 2) with ht
  have hzy : 0 < z - 13 / 2 := by linarith
  have hlog : Real.log (Gamma (13 / 2)) + t * (Real.log (Gamma (13 / 2)) - Real.log (Gamma 6))
      ≤ Real.log (Gamma z) := by
    rw [show (13 / 2 : ℝ) - 6 = 1 / 2 by norm_num, le_div_iff₀ hzy] at hconv
    have : (Real.log (Gamma (13 / 2)) - Real.log (Gamma 6)) / (1 / 2) =
        2 * (Real.log (Gamma (13 / 2)) - Real.log (Gamma 6)) := by ring
    rw [this] at hconv
    rw [ht]; nlinarith
  -- exponentiate
  have hratio : 1 ≤ Gamma (13 / 2) / Gamma 6 := by
    rw [gamma_thirteen_halves, gamma_six, le_div_iff₀ (by norm_num)]
    nlinarith [sqrt_pi_gt]
  have hexp : Gamma (13 / 2) * (Gamma (13 / 2) / Gamma 6) ^ t ≤ Gamma z := by
    rw [Real.rpow_def_of_pos (by linarith), Real.log_div hGy.ne' hG6.ne',
      ← Real.exp_log hGy, ← Real.exp_add, Real.exp_log hGy]
    calc Real.exp (Real.log (Gamma (13 / 2)) +
          (Real.log (Gamma (13 / 2)) - Real.log (Gamma 6)) * t)
        ≤ Real.exp (Real.log (Gamma z)) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = Gamma z := Real.exp_log hGz
  -- the exponent `t = 2φ - 3 = √5 - 2 ≥ 4/17`
  have ht0 : ((4 : ℕ) : ℝ) / (17 : ℕ) ≤ t := by
    rw [ht, hz]; norm_num; linarith
  have r0 : (10395 / 64 * 1.7724 / 120 : ℝ) ≤ Gamma (13 / 2) / Gamma 6 := by
    rw [gamma_thirteen_halves, gamma_six]
    have := sqrt_pi_gt
    rw [div_le_div_iff_of_pos_right (by norm_num)]
    nlinarith
  have step1 : (Gamma (13 / 2) / Gamma 6) ^ (((4 : ℕ) : ℝ) / (17 : ℕ)) ≤
      (Gamma (13 / 2) / Gamma 6) ^ t := Real.rpow_le_rpow_of_exponent_le hratio ht0
  have step2 : (10395 / 64 * 1.7724 / 120 : ℝ) ^ (((4 : ℕ) : ℝ) / (17 : ℕ)) ≤
      (Gamma (13 / 2) / Gamma 6) ^ (((4 : ℕ) : ℝ) / (17 : ℕ)) :=
    Real.rpow_le_rpow (by norm_num) r0 (by norm_num)
  have step3 : (1.228 : ℝ) ≤ (10395 / 64 * 1.7724 / 120 : ℝ) ^ (((4 : ℕ) : ℝ) / (17 : ℕ)) :=
    le_rpow_div_of_pow_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hA : (10395 / 64 * 1.7724 : ℝ) ≤ Gamma (13 / 2) := by
    rw [gamma_thirteen_halves]; nlinarith [sqrt_pi_gt]
  have hlow : (10395 / 64 * 1.7724 : ℝ) * 1.228 ≤ Gamma z :=
    le_trans (mul_le_mul hA (by linarith) (by norm_num) hGy.le) hexp
  -- shift down by five
  have hshift := gamma_add_five goldenRatio hφ0
  rw [← hz] at hshift
  set P := goldenRatio * (goldenRatio + 1) * (goldenRatio + 2) * (goldenRatio + 3) *
    (goldenRatio + 4) with hP
  have hP0 : 0 < P := by positivity
  have hPle : P ≤ 1.61804 * (1.61804 + 1) * (1.61804 + 2) * (1.61804 + 3) * (1.61804 + 4) := by
    rw [hP]; gcongr
  have hmain : (10395 / 64 * 1.7724 : ℝ) * 1.228 ≤ P * Gamma goldenRatio := by
    rw [← hshift]; exact hlow
  by_contra hcon
  push Not at hcon
  have hGφ : 0 < Gamma goldenRatio := Real.Gamma_pos_of_pos hφ0
  have : P * Gamma goldenRatio <
      (1.61804 * (1.61804 + 1) * (1.61804 + 2) * (1.61804 + 3) * (1.61804 + 4)) * 0.8856 :=
    mul_lt_mul' hPle hcon hGφ.le (by norm_num)
  norm_num at this hmain
  linarith

/-! ### `Γ ≤ 1` on `[1,2]` and `Γ(φ⁻²) ≤ φ²` -/

theorem gamma_le_one_of_mem_Icc {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : Gamma x ≤ 1 := by
  have hc := Real.convexOn_Gamma.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (show 0 ≤ 2 - x by linarith) (show 0 ≤ x - 1 by linarith)
    (by ring : (2 - x) + (x - 1) = 1)
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at hc
  have : (2 - x) * 1 + (x - 1) * 2 = x := by ring
  rw [this] at hc
  linarith

theorem golden_inv_sq : (goldenRatio ^ 2)⁻¹ = 2 - goldenRatio := by
  have h := Real.goldenRatio_sq
  have hpos : 0 < goldenRatio ^ 2 := by positivity
  apply inv_eq_of_mul_eq_one_right
  linear_combination (1 - goldenRatio) * h

/-- `Γ(φ⁻²) = Γ(1 + φ⁻²) φ² ≤ φ²`. -/
theorem gamma_golden_inv_sq_le : Gamma ((goldenRatio ^ 2)⁻¹) ≤ goldenRatio ^ 2 := by
  obtain ⟨hφ1, hφ2⟩ := golden_bounds
  set y := (goldenRatio ^ 2)⁻¹ with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by rw [hy, golden_inv_sq]; linarith
  have h := gamma_succ hy0.ne'
  have hle := gamma_le_one_of_mem_Icc (x := y + 1) (by linarith) (by linarith)
  rw [h] at hle
  have : goldenRatio ^ 2 = y⁻¹ := by rw [hy, inv_inv]
  rw [this, ← one_div, le_div_iff₀ hy0, mul_comm]
  exact hle

/-! ### `|cos(πφ/2)| ≤ √3/2` -/

theorem cos_golden_nonpos : Real.cos (π * goldenRatio / 2) ≤ 0 := by
  obtain ⟨hφ1, hφ2⟩ := golden_bounds
  apply Real.cos_nonpos_of_pi_div_two_le_of_le
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

theorem abs_cos_golden_le : |Real.cos (π * goldenRatio / 2)| ≤ √3 / 2 := by
  obtain ⟨hφ1, hφ2⟩ := golden_bounds
  rw [abs_of_nonpos cos_golden_nonpos]
  have h56 : Real.cos (5 * π / 6) = -(√3 / 2) := by
    rw [show 5 * π / 6 = π - π / 6 by ring, Real.cos_pi_sub, Real.cos_pi_div_six]
  have : Real.cos (5 * π / 6) ≤ Real.cos (π * goldenRatio / 2) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
  linarith

/-! ### The trapezoid bound `ζ(α) ≥ 1/2 + 1/(α-1)` -/

/-- The real zeta function as the series `ζ(α) = ∑_{n ≥ 1} n^(-α)` (`= μ = E ξ` for `α > 1`). -/
noncomputable def zetaR (α : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-α)

theorem zetaR_summable {α : ℝ} (hα : 1 < α) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-α)) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-α)) 1).mpr
    (Real.summable_nat_rpow.mpr (by linarith))
  refine h.congr (fun k => ?_)
  simp

/-- Bernoulli for a negative exponent: `x^(-α) ≥ 1 - α(x-1)` for `x > 0`, `α ≥ 0`. -/
theorem bernoulli_neg {α x : ℝ} (hα : 0 ≤ α) (hx : 0 < x) : 1 - α * (x - 1) ≤ x ^ (-α) := by
  rw [Real.rpow_def_of_pos hx]
  have h1 := Real.add_one_le_exp (Real.log x * (-α))
  have h2 := Real.log_le_sub_one_of_pos hx
  nlinarith

/-- One trapezoid step for the convex `t^(-α)`:
`∫_k^{k+1} t^(-α) dt = (k^(1-α) - (k+1)^(1-α))/(α-1) ≤ (k^(-α) + (k+1)^(-α))/2`. -/
theorem trap_step {α k : ℝ} (hα : 1 < α) (hk : 0 < k) :
    k ^ (1 - α) - (k + 1) ^ (1 - α) ≤ (α - 1) * (k ^ (-α) + (k + 1) ^ (-α)) / 2 := by
  set ψ : ℝ → ℝ := fun t => k ^ (1 - α) - t ^ (1 - α) - (α - 1) * (t - k) * (k ^ (-α) + t ^ (-α)) / 2
    with hψ
  have hder : ∀ t, 0 < t → HasDerivAt ψ
      (-((1 - α) * t ^ (-α)) - (α - 1) * ((k ^ (-α) + t ^ (-α)) + (t - k) * (-α * t ^ (-α - 1))) / 2) t := by
    intro t ht
    have d1 : HasDerivAt (fun t : ℝ => t ^ (1 - α)) ((1 - α) * t ^ (-α)) t := by
      have := Real.hasDerivAt_rpow_const (x := t) (p := 1 - α) (Or.inl ht.ne')
      rwa [show 1 - α - 1 = -α by ring] at this
    have d2 : HasDerivAt (fun t : ℝ => t ^ (-α)) (-α * t ^ (-α - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht.ne')
    have d3 : HasDerivAt (fun t : ℝ => t - k) 1 t := (hasDerivAt_id t).sub_const k
    have d4 := ((d3.const_mul (α - 1)).mul ((hasDerivAt_const t (k ^ (-α))).add d2)).div_const 2
    have d5 := ((hasDerivAt_const t (k ^ (1 - α))).sub d1).sub d4
    exact d5.congr_deriv (by simp only [Pi.add_apply]; ring)
  have hneg : ∀ t, k < t →
      -((1 - α) * t ^ (-α)) - (α - 1) * ((k ^ (-α) + t ^ (-α)) + (t - k) * (-α * t ^ (-α - 1))) / 2
        ≤ 0 := by
    intro t ht
    have ht0 : 0 < t := hk.trans ht
    have hq : 0 < k / t := div_pos hk ht0
    have hb := bernoulli_neg (by linarith : (0 : ℝ) ≤ α) hq
    have hkt : k ^ (-α) = t ^ (-α) * (k / t) ^ (-α) := by
      rw [Real.div_rpow hk.le ht0.le, mul_div_assoc', mul_comm, mul_div_assoc,
        div_self (Real.rpow_pos_of_pos ht0 _).ne', mul_one]
    have htm : t ^ (-α - 1) = t ^ (-α) / t := Real.rpow_sub_one ht0.ne' _
    have hT : 0 < t ^ (-α) := Real.rpow_pos_of_pos ht0 _
    -- key: t^(-α) + α (t-k) t^(-α-1) ≤ k^(-α)
    have key : t ^ (-α) + α * (t - k) * t ^ (-α - 1) ≤ k ^ (-α) := by
      rw [hkt, htm]
      have e : t ^ (-α) + α * (t - k) * (t ^ (-α) / t) = t ^ (-α) * (1 - α * (k / t - 1)) := by
        field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hb hT.le
    nlinarith
  have hanti : AntitoneOn ψ (Ici k) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici k)
    · intro t ht
      exact (hder t (lt_of_lt_of_le hk ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hder t (hk.trans ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hder t (hk.trans ht)).deriv]
      exact hneg t ht
  have := hanti (show k ∈ Ici k from le_refl k) (show k + 1 ∈ Ici k by simp) (by linarith)
  simp only [hψ, sub_self, mul_zero, zero_mul, zero_div] at this
  linarith

/-- **Trapezoid bound** (proof of Corollary 2.5): `ζ(α) - 1/2 ≥ 1/(α-1)` for `α > 1`. -/
theorem zeta_trapezoid {α : ℝ} (hα : 1 < α) : 1 / 2 + 1 / (α - 1) ≤ zetaR α := by
  have hα1 : 0 < α - 1 := by linarith
  set a : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-α) with ha
  set g : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (1 - α) with hg
  have ha0 : a 0 = 1 := by simp [ha]
  have hg0 : g 0 = 1 := by simp [hg]
  have hann : ∀ n, 0 ≤ a n := fun n => Real.rpow_nonneg (by positivity) _
  have claim : ∀ M : ℕ, g 0 - g M ≤
      (α - 1) * (∑ n ∈ Finset.range (M + 1), a n - 1 / 2 - a M / 2) := by
    intro M
    induction M with
    | zero => simp [ha0]; norm_num
    | succ M ih =>
      have hs := trap_step hα (show (0 : ℝ) < (M : ℝ) + 1 by positivity)
      have e1 : g (M + 1) = ((M : ℝ) + 1 + 1) ^ (1 - α) := by simp [hg]
      have e2 : a (M + 1) = ((M : ℝ) + 1 + 1) ^ (-α) := by simp [ha]
      rw [Finset.sum_range_succ (n := M + 1), e1, e2]
      rw [e1] at *
      simp only [hg, ha] at ih hs ⊢
      push_cast at ih hs ⊢
      nlinarith
  have hsum := zetaR_summable hα
  have hbound : ∀ M : ℕ, g 0 - g M ≤ (α - 1) * (zetaR α - 1 / 2) := by
    intro M
    refine (claim M).trans ?_
    apply mul_le_mul_of_nonneg_left _ hα1.le
    have : ∑ n ∈ Finset.range (M + 1), a n ≤ zetaR α :=
      hsum.sum_le_tsum _ (fun i _ => hann i)
    linarith [hann M]
  have hgM : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 := (tendsto_rpow_neg_atTop hα1).comp h1
    refine h2.congr (fun M => ?_)
    simp only [hg, Function.comp]
    rw [show -(α - 1) = 1 - α by ring]
  have hlim : g 0 - 0 ≤ (α - 1) * (zetaR α - 1 / 2) :=
    le_of_tendsto' (tendsto_const_nhds.sub hgM) hbound
  rw [hg0, sub_zero] at hlim
  have : 1 / (α - 1) ≤ zetaR α - 1 / 2 := by
    rw [div_le_iff₀ hα1]; linarith
  linarith

end Kagey131.PaperF.FL2
