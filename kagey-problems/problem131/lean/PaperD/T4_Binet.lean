import PaperD.T4_Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Paper D, Theorem 2.6(b): the digamma bounds, proved from Mathlib

This file proves the cited fact `BinetDigammaBounds` of `T4_Digamma.lean`,
`log x - 1/(2x) - 1/(12x²) < ψ(x) < log x - 1/(2x)` for `x > 0` (`binetDigammaBounds_holds`),
so that it is no longer a hypothesis. The paper cites DLMF 5.9.15 (Binet's integral). We use a
different, elementary route:
* `ψ(x+1) = ψ(x) + 1/x` (`psiR_succ`), from `Γ(x+1) = xΓ(x)`;
* `log(x-1) ≤ ψ(x) ≤ log x` for `x > 1` (`psiR_bounds`), from the convexity of `log Γ`
  (Bohr-Mollerup, Mathlib's `Real.convexOn_log_Gamma`), hence `ψ(x+n) - log(x+n) → 0`;
* the two elementary inequalities, with `u = 1/(2x+1)`,
  `log(1+u) - log(1-u) < 2u/(1-u²)` and
  `log(1+u) - log(1-u) > 2u/(1-u²) - 4u³/(3(1-u²)²)`, by comparing the power series
  `∑ 2u^{2k+1}/(2k+1)` term by term with geometric series (`logRatio_lt`, `logRatio_gt`);
* so `F(x) = ψ(x) - log x + 1/(2x)` satisfies `F(x) < F(x+1)` and
  `G(x) = F(x) + 1/(12x²)` satisfies `G(x) > G(x+1)`, and both tend to `0` along `x + n`.
-/

namespace Kagey131.PaperD

open Finset Real Filter Topology Set

/-! ### Two elementary inequalities -/

theorem logRatio_hasSum {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasSum (fun k : ℕ => 2 * u * (u ^ 2) ^ k / (2 * k + 1)) (Real.log (1 + u) - Real.log (1 - u)) := by
  have := hasSum_log_sub_log_of_abs_lt_one (show |u| < 1 by rw [abs_of_pos h0]; exact h1)
  convert this using 1
  funext k
  rw [show u ^ (2 * k + 1) = u * (u ^ 2) ^ k by rw [pow_succ, pow_mul]; ring]
  field_simp

theorem geom_hasSum {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasSum (fun k : ℕ => 2 * u * (u ^ 2) ^ k) (2 * u / (1 - u ^ 2)) := by
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg u) (by nlinarith)).mul_left (2 * u)
  rw [div_eq_mul_inv]; exact hg

theorem logRatio_lt {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    Real.log (1 + u) - Real.log (1 - u) < 2 * u / (1 - u ^ 2) := by
  refine hasSum_lt (f := fun k : ℕ => 2 * u * (u ^ 2) ^ k / (2 * k + 1))
    (g := fun k : ℕ => 2 * u * (u ^ 2) ^ k) (i := 1) ?_ ?_ (logRatio_hasSum h0 h1) (geom_hasSum h0 h1)
  · intro k
    have : 0 ≤ 2 * u * (u ^ 2) ^ k := by positivity
    exact div_le_self this (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  · show 2 * u * (u ^ 2) ^ 1 / (2 * ((1 : ℕ) : ℝ) + 1) < 2 * u * (u ^ 2) ^ 1
    have : 0 < 2 * u * (u ^ 2) ^ 1 := by positivity
    rw [div_lt_iff₀ (by norm_num)]; push_cast; linarith

theorem logRatio_gt {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    2 * u / (1 - u ^ 2) - 4 * u ^ 3 / (3 * (1 - u ^ 2) ^ 2) < Real.log (1 + u) - Real.log (1 - u) := by
  have hu2 : u ^ 2 < 1 := by nlinarith
  have hd := (geom_hasSum h0 h1).sub (logRatio_hasSum h0 h1)
  have he := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := u ^ 2)
    (by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg u)]; exact hu2)).mul_left (4 / 3 * u)
  have hlt := hasSum_lt (f := fun k : ℕ => 2 * u * (u ^ 2) ^ k - 2 * u * (u ^ 2) ^ k / (2 * k + 1))
    (g := fun k : ℕ => 4 / 3 * u * (k * (u ^ 2) ^ k)) (i := 2) ?_ ?_ hd he
  · have e : 4 / 3 * u * (u ^ 2 / (1 - u ^ 2) ^ 2) = 4 * u ^ 3 / (3 * (1 - u ^ 2) ^ 2) := by
      have : 1 - u ^ 2 ≠ 0 := by linarith
      field_simp
    rw [e] at hlt
    linarith
  · intro k
    have hr : 0 ≤ (u ^ 2) ^ k := by positivity
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    show 2 * u * (u ^ 2) ^ k - 2 * u * (u ^ 2) ^ k / (2 * k + 1) ≤ 4 / 3 * u * (k * (u ^ 2) ^ k)
    have e : 2 * u * (u ^ 2) ^ k - 2 * u * (u ^ 2) ^ k / (2 * k + 1) =
        u * (u ^ 2) ^ k * (4 * k / (2 * k + 1)) := by field_simp; ring
    rw [e, show 4 / 3 * u * (k * (u ^ 2) ^ k) = u * (u ^ 2) ^ k * (4 * k / 3) by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  · show 2 * u * (u ^ 2) ^ 2 - 2 * u * (u ^ 2) ^ 2 / (2 * ((2 : ℕ) : ℝ) + 1) <
      4 / 3 * u * (((2 : ℕ) : ℝ) * (u ^ 2) ^ 2)
    have : 0 < u * (u ^ 2) ^ 2 := by positivity
    push_cast
    nlinarith

/-- `log(y+1) - log y < 1/(2y) + 1/(2(y+1))` for `y > 0`. -/
theorem log_succ_sub_lt {y : ℝ} (hy : 0 < y) :
    Real.log (y + 1) - Real.log y < 1 / (2 * y) + 1 / (2 * (y + 1)) := by
  have hu0 : 0 < 1 / (2 * y + 1) := by positivity
  have hu1 : 1 / (2 * y + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := logRatio_lt hu0 hu1
  have e1 : Real.log (1 + 1 / (2 * y + 1)) - Real.log (1 - 1 / (2 * y + 1)) =
      Real.log (y + 1) - Real.log y := by
    have a : 1 + 1 / (2 * y + 1) = 2 * (y + 1) / (2 * y + 1) := by field_simp; ring
    have b : 1 - 1 / (2 * y + 1) = 2 * y / (2 * y + 1) := by field_simp; ring
    rw [a, b, Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity)]
    ring
  have hq : 1 - (1 / (2 * y + 1)) ^ 2 = 4 * y * (y + 1) / (2 * y + 1) ^ 2 := by
    field_simp; ring
  have e2 : 2 * (1 / (2 * y + 1)) / (1 - (1 / (2 * y + 1)) ^ 2) = 1 / (2 * y) + 1 / (2 * (y + 1)) := by
    rw [hq]; field_simp; ring
  rw [e1, e2] at h; exact h

/-- `log(y+1) - log y > 1/(2y) + 1/(2(y+1)) - 1/(12y²) + 1/(12(y+1)²)` for `y > 0`. -/
theorem log_succ_sub_gt {y : ℝ} (hy : 0 < y) :
    1 / (2 * y) + 1 / (2 * (y + 1)) - 1 / (12 * y ^ 2) + 1 / (12 * (y + 1) ^ 2) <
      Real.log (y + 1) - Real.log y := by
  have hu0 : 0 < 1 / (2 * y + 1) := by positivity
  have hu1 : 1 / (2 * y + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := logRatio_gt hu0 hu1
  have e1 : Real.log (1 + 1 / (2 * y + 1)) - Real.log (1 - 1 / (2 * y + 1)) =
      Real.log (y + 1) - Real.log y := by
    have a : 1 + 1 / (2 * y + 1) = 2 * (y + 1) / (2 * y + 1) := by field_simp; ring
    have b : 1 - 1 / (2 * y + 1) = 2 * y / (2 * y + 1) := by field_simp; ring
    rw [a, b, Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity)]
    ring
  have e2 : 2 * (1 / (2 * y + 1)) / (1 - (1 / (2 * y + 1)) ^ 2) -
      4 * (1 / (2 * y + 1)) ^ 3 / (3 * (1 - (1 / (2 * y + 1)) ^ 2) ^ 2) =
      1 / (2 * y) + 1 / (2 * (y + 1)) - 1 / (12 * y ^ 2) + 1 / (12 * (y + 1) ^ 2) := by
    have hq : 1 - (1 / (2 * y + 1)) ^ 2 = 4 * y * (y + 1) / (2 * y + 1) ^ 2 := by
      field_simp; ring
    rw [hq]; field_simp; ring
  rw [e1, e2] at h; exact h

/-! ### The digamma function: recurrence and convexity bounds -/

theorem psiR_succ {x : ℝ} (hx : 0 < x) : psiR (x + 1) = psiR x + 1 / x := by
  have h1 : HasDerivAt (fun y => Real.log (Gamma (y + 1))) (psiR (x + 1)) x := by
    have := (hasDerivAt_logGamma (show 0 < x + 1 by linarith)).comp x ((hasDerivAt_id' x).add_const 1)
    exact this.congr_deriv (mul_one _)
  have h2 : HasDerivAt (fun y => Real.log y + Real.log (Gamma y)) (x⁻¹ + psiR x) x :=
    (Real.hasDerivAt_log hx.ne').add (hasDerivAt_logGamma hx)
  have heq : (fun y => Real.log (Gamma (y + 1))) =ᶠ[𝓝 x] (fun y => Real.log y + Real.log (Gamma y)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [Gamma_succ_of_pos hy, Real.log_mul hy.ne' (Gamma_pos_of_pos hy).ne']
  have := h1.unique (h2.congr_of_eventuallyEq heq)
  rw [this, one_div]; ring

theorem psiR_bounds {y : ℝ} (hy : 1 < y) : Real.log (y - 1) ≤ psiR y ∧ psiR y ≤ Real.log y := by
  have hy0 : 0 < y := by linarith
  have hconv := Real.convexOn_log_Gamma
  have hd : DifferentiableAt ℝ (Real.log ∘ Gamma) y := (hasDerivAt_logGamma hy0).differentiableAt
  have hpsi : deriv (Real.log ∘ Gamma) y = psiR y := rfl
  constructor
  · have := hconv.slope_le_deriv (x := y - 1) (y := y) (by simp; linarith) (by simp; linarith)
      (by linarith) hd
    rw [hpsi, slope_def_field] at this
    have hG : Gamma y = (y - 1) * Gamma (y - 1) := by
      have := Gamma_succ_of_pos (show 0 < y - 1 by linarith)
      rwa [sub_add_cancel] at this
    simp only [Function.comp, hG] at this
    rw [Real.log_mul (by linarith) (Gamma_pos_of_pos (show 0 < y - 1 by linarith)).ne'] at this
    simpa using this
  · have := hconv.deriv_le_slope (x := y) (y := y + 1) (by simp; linarith) (by simp; linarith)
      (by linarith) hd
    rw [hpsi, slope_def_field] at this
    simp only [Function.comp, Gamma_succ_of_pos hy0] at this
    rw [Real.log_mul hy0.ne' (Gamma_pos_of_pos hy0).ne'] at this
    simpa using this

/-- `ψ(x + 1 + n) - log(x + 1 + n) → 0`. -/
theorem psiR_sub_log_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => psiR (x + 1 + n) - Real.log (x + 1 + n)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (x + n)⁻¹) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hlow : Tendsto (fun n : ℕ => -(x + n)⁻¹) atTop (𝓝 0) := by simpa using hinv.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_) (fun n => ?_)
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hb := (psiR_bounds (show 1 < x + 1 + n by linarith)).1
    rw [show x + 1 + n - 1 = x + n by ring] at hb
    have hl : Real.log (x + 1 + n) - Real.log (x + n) ≤ (x + n)⁻¹ := by
      rw [← Real.log_div (by linarith) (by linarith)]
      have := Real.log_le_sub_one_of_pos (show 0 < (x + 1 + n) / (x + n) by positivity)
      have e : (x + 1 + n) / (x + n) - 1 = (x + n)⁻¹ := by field_simp; ring
      linarith
    show -(x + n)⁻¹ ≤ psiR (x + 1 + n) - Real.log (x + 1 + n)
    linarith
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hb := (psiR_bounds (show 1 < x + 1 + n by linarith)).2
    show psiR (x + 1 + n) - Real.log (x + 1 + n) ≤ 0
    linarith

/-! ### The Binet bounds -/

theorem binet_upper {x : ℝ} (hx : 0 < x) : psiR x < Real.log x - 1 / (2 * x) := by
  set F : ℝ → ℝ := fun y => psiR y - Real.log y + 1 / (2 * y) with hF
  have hstep : ∀ y, 0 < y → F y < F (y + 1) := by
    intro y hy
    simp only [hF]
    rw [psiR_succ hy]
    have := log_succ_sub_lt hy
    have e : 1 / y = 1 / (2 * y) + 1 / (2 * y) := by field_simp; ring
    linarith
  have hmono : Monotone (fun n : ℕ => F (x + 1 + n)) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have := hstep (x + 1 + n) (by linarith)
    rw [show x + 1 + ((n + 1 : ℕ) : ℝ) = x + 1 + n + 1 by push_cast; ring]
    exact this.le
  have hlim : Tendsto (fun n : ℕ => F (x + 1 + n)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (x + 1 + n)⁻¹) atTop (𝓝 0) :=
      (tendsto_atTop_add_const_left atTop (x + 1) tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    have := (psiR_sub_log_tendsto hx).add (hinv.mul_const (1 / 2))
    simp only [zero_mul, add_zero] at this
    refine this.congr (fun n => ?_)
    simp only [hF]; field_simp
  have h0 := hmono.ge_of_tendsto hlim 0
  simp only [Nat.cast_zero, add_zero] at h0
  have := hstep x hx
  simp only [hF] at this h0
  linarith

theorem binet_lower {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) < psiR x := by
  set G : ℝ → ℝ := fun y => psiR y - Real.log y + 1 / (2 * y) + 1 / (12 * y ^ 2) with hG
  have hstep : ∀ y, 0 < y → G (y + 1) < G y := by
    intro y hy
    simp only [hG]
    rw [psiR_succ hy]
    have := log_succ_sub_gt hy
    have e : 1 / y = 1 / (2 * y) + 1 / (2 * y) := by field_simp; ring
    linarith
  have hanti : Antitone (fun n : ℕ => G (x + 1 + n)) := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have := hstep (x + 1 + n) (by linarith)
    rw [show x + 1 + ((n + 1 : ℕ) : ℝ) = x + 1 + n + 1 by push_cast; ring]
    exact this.le
  have hlim : Tendsto (fun n : ℕ => G (x + 1 + n)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (x + 1 + n)⁻¹) atTop (𝓝 0) :=
      (tendsto_atTop_add_const_left atTop (x + 1) tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    have := ((psiR_sub_log_tendsto hx).add (hinv.mul_const (1 / 2))).add
      ((hinv.pow 2).mul_const (1 / 12))
    simp only [zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    refine this.congr (fun n => ?_)
    simp only [hG]; field_simp
  have h0 := hanti.le_of_tendsto hlim 0
  simp only [Nat.cast_zero, add_zero] at h0
  have := hstep x hx
  simp only [hG] at this h0
  linarith

/-- The cited fact `BinetDigammaBounds` (DLMF 5.9.15) holds. -/
theorem binetDigammaBounds_holds : BinetDigammaBounds :=
  fun _ hx => ⟨binet_lower hx, binet_upper hx⟩

end Kagey131.PaperD
