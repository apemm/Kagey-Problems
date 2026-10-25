import PaperD.Modes.StepTwoA

/-!
# Paper D, Theorem `thm:two-modes`, Step 2 (the limit `N → ∞`)

File: `paperD/sec_bulk_applications.tex`. Under the hypothesis `LawConvHyp` that
`S_N/N^a = z_{A_N}` converges in law to a variable with density `g` (Guérin, Laulin and Raschel,
used in the paper through the almost sure convergence of `S_N/N^a`), the smoothed second
differences converge: `V_N(y) → ∫ φ''(y - t) g(t) dt` (`smoothedD_tendsto`). This is
`V_N(y) → u''(y)` of Step 2 once `u = φ * g` is differentiated under the integral
(`PaperD.Modes.Mollify`).
-/

namespace Kagey131.PaperD.Modes

open Kagey131.PaperD Filter Finset

/-- Convergence in law of `z_{A_N} = (2A_N - N)/N^a` to a variable with density `g`, stated for
bounded continuous test functions: `∑_k P_N(k) f(z_k) → ∫ f g`. -/
def LawConvHyp (ε a : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
    Tendsto (fun N : ℕ => ∑ k ∈ range (N + 1), ewBin ε N k * f (zPt N a k)) atTop
      (nhds (∫ y, f y * g y))

theorem tendsto_shift_pow_geom (k s : ℕ) {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) + s) ^ k * r ^ n) atTop (nhds 0) := by
  have h := (tendsto_add_atTop_iff_nat s).2 (tendsto_pow_geom k h0.le h1)
  have h2 := h.const_mul (r ^ s)⁻¹
  rw [mul_zero] at h2
  refine h2.congr (fun n => ?_)
  push_cast
  rw [pow_add]
  field_simp

theorem eta_sq_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (2 * ((n + 3 : ℕ) : ℝ) ^ (-a)) ^ 2) atTop (nhds 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have h2 : Tendsto (fun x : ℝ => x ^ (-a)) atTop (nhds 0) := tendsto_rpow_neg_atTop ha
  have h3 := ((h2.comp h1).const_mul 2).pow 2
  simpa using h3

/-- `V_N(y) → ∫ φ''(y - t) g(t) dt`. -/
theorem smoothedD_tendsto {ε a σ : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (ha : 0 < a) (ha1 : a ≤ 1)
    (hσ : 0 < σ) {g : ℝ → ℝ} (hlaw : LawConvHyp ε a g) (y : ℝ) :
    Tendsto (fun n : ℕ => smoothedD ε a σ (n + 3) y) atTop
      (nhds (∫ t, gd2 σ (y - t) * g t)) := by
  obtain ⟨M, hM0, hM⟩ := gd_bounded hσ
  -- the comparison sums converge
  have hf : Continuous (fun t => gd2 σ (y - t)) := (gd2_cont σ).comp (continuous_const.sub continuous_id)
  have hb := hlaw (fun t => gd2 σ (y - t)) hf ⟨M, fun x => (hM _).2.2.1⟩
  have hb' := (tendsto_add_atTop_iff_nat 3).2 hb
  refine tendsto_of_tendsto_of_dist hb' ?_
  -- the distance is bounded by a sequence tending to zero
  set r : ℝ := 1 - ε with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hlim := tendsto_shift_pow_geom 3 4 hr0 hr1
  have hη := eta_sq_tendsto ha
  have hup : Tendsto (fun n : ℕ => 2 * M * (2 * ((n + 3 : ℕ) : ℝ) ^ (-a)) ^ 2
      + 3 * M * (((n : ℝ) + 4) ^ 3 * r ^ n)) atTop (nhds 0) := by
    have := (hη.const_mul (2 * M)).add (hlim.const_mul (3 * M))
    simpa using this
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hup
  rw [Real.dist_eq]
  -- `|b_{n+3} - V_{n+3}| ≤ ...`
  have hclose := smoothedD_close (a := a) y hε0 hε hσ hM (N := n + 3) (by omega)
  rw [abs_sub_comm]
  refine hclose.trans ?_
  -- the edge bounds
  have hP0 : ewBin ε (n + 3) 0 ≤ r ^ n := by
    have := ewBin_zero_le hε0.le hε (n + 2)
    have h2 : r ^ (n + 2) ≤ r ^ n := pow_le_pow_of_le_one hr0.le hr1.le (by omega)
    simpa [hr] using this.trans (by simpa [hr] using h2)
  have hP1 : ewBin ε (n + 3) 1 ≤ ((n : ℝ) + 3) * r ^ n := by
    have := ewBin_one_le hε0.le hε (n + 1)
    have h2 : r ^ (n + 1) ≤ r ^ n := pow_le_pow_of_le_one hr0.le hr1.le (by omega)
    have h3 : ((↑(n + 1) : ℝ) + 2) * ε * r ^ (n + 1) ≤ ((n : ℝ) + 3) * r ^ n := by
      push_cast
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have : ε * r ^ (n + 1) ≤ r ^ n := by
        calc ε * r ^ (n + 1) ≤ 1 * r ^ n := by
              apply mul_le_mul (by linarith) h2 (by positivity) (by norm_num)
          _ = r ^ n := one_mul _
      nlinarith [pow_pos hr0 n]
    simpa [hr] using this.trans (by simpa [hr] using h3)
  have hP0nn : 0 ≤ ewBin ε (n + 3) 0 := ewBin_nonneg hε0.le (by linarith) (by omega) (by omega)
  have hP1nn : 0 ≤ ewBin ε (n + 3) 1 := ewBin_nonneg hε0.le (by linarith) (by omega) (by omega)
  -- the inverse of `η²`
  have hN : (1 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 3)
  have hinv : (((2 * ((n + 3 : ℕ) : ℝ) ^ (-a)) ^ 2)⁻¹) ≤ ((n : ℝ) + 3) ^ 2 / 4 := by
    have hpos : 0 < ((n + 3 : ℕ) : ℝ) := by linarith
    have hNa : ((n + 3 : ℕ) : ℝ) ^ a ≤ ((n + 3 : ℕ) : ℝ) := by
      calc ((n + 3 : ℕ) : ℝ) ^ a ≤ ((n + 3 : ℕ) : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN ha1
        _ = _ := Real.rpow_one _
    have hNa0 : 0 < ((n + 3 : ℕ) : ℝ) ^ a := Real.rpow_pos_of_pos hpos a
    have e : ((2 * ((n + 3 : ℕ) : ℝ) ^ (-a)) ^ 2)⁻¹ = (((n + 3 : ℕ) : ℝ) ^ a) ^ 2 / 4 := by
      rw [Real.rpow_neg hpos.le]
      field_simp
      norm_num
    rw [e]
    have h5 : (((n + 3 : ℕ) : ℝ) ^ a) ^ 2 ≤ ((n + 3 : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ hNa0.le hNa 2
    have h6 : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    calc (((n + 3 : ℕ) : ℝ) ^ a) ^ 2 / 4 ≤ ((n + 3 : ℕ) : ℝ) ^ 2 / 4 := by linarith
      _ = ((n : ℝ) + 3) ^ 2 / 4 := by rw [h6]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hrn : 0 < r ^ n := pow_pos hr0 n
  have hM0' : 0 ≤ M := hM0
  have hinv0 : 0 ≤ ((2 * ((n + 3 : ℕ) : ℝ) ^ (-a)) ^ 2)⁻¹ := by positivity
  -- combine
  have step1 : 2 * M * ((2 * ((n + 3 : ℕ) : ℝ) ^ (-a)) ^ 2)⁻¹ *
      (ewBin ε (n + 3) 0 + ewBin ε (n + 3) 1) ≤
      2 * M * (((n : ℝ) + 3) ^ 2 / 4) * ((n + 4) * r ^ n) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hinv (by positivity)) _ (by positivity)
      (by positivity)
    nlinarith
  have step2 : 2 * M * (((n : ℝ) + 3) ^ 2 / 4) * ((n + 4) * r ^ n) ≤
      (5 / 2 * M) * (((n : ℝ) + 4) ^ 3 * r ^ n) := by
    have : ((n : ℝ) + 3) ^ 2 * (n + 4) ≤ ((n : ℝ) + 4) ^ 3 := by nlinarith
    nlinarith [mul_nonneg hM0' hrn.le, mul_le_mul_of_nonneg_right this (mul_nonneg hM0' hrn.le)]
  have step3 : 2 * M * ewBin ε (n + 3) 0 ≤ 2 * M * (((n : ℝ) + 4) ^ 3 * r ^ n) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (1 : ℝ) ≤ ((n : ℝ) + 4) ^ 3 := by nlinarith
    nlinarith
  push_cast at *
  nlinarith [mul_nonneg hM0' (mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ n + 4) 3) hrn.le)]

end Kagey131.PaperD.Modes
