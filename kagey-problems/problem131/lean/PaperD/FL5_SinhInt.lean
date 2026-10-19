import Mathlib

/-!
# Paper F, track FL5: `∫_0^∞ sinh(ax)/sinh(bx) dx = (π/2b) tan(πa/2b)`

A classical integral (Gradshteyn and Ryzhik, 3.511.2), proved here from Mathlib's partial
fraction expansion of the cotangent (`cot_series_rep'`):

* `hasSum_tan`: `∑_{k ≥ 0} 4z/((2k+1)² - z²) = π tan(πz/2)` for `0 < z < 1`;
* `integral_sinh_div_sinh`: the integral, by expanding `1/sinh(bx)` in a geometric series and
  integrating term by term.

It is used for the value in Step 4 of the proof of Theorem 2.9 (`FL5_Step4`).
-/

namespace Kagey131.PaperD.FL5

open Filter Topology Real MeasureTheory Set

/-- `π tan(πz/2) = ∑_{k ≥ 0} 4z/((2k+1)² - z²)` for `0 < z < 1`. -/
theorem hasSum_tan {z : ℝ} (h0 : 0 < z) (h1 : z < 1) :
    HasSum (fun k : ℕ => 4 * z / ((2 * k + 1) ^ 2 - z ^ 2)) (π * Real.tan (π * z / 2)) := by
  set x : ℝ := (1 - z) / 2 with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  have hx1 : x < 1 / 2 := by rw [hx]; linarith
  have hxZ : (x : ℂ) ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have h := congrArg Complex.re hn
    simp only [Complex.intCast_re, Complex.ofReal_re] at h
    have h1' : (0 : ℝ) < n := by rw [h]; exact hx0
    have h2' : (n : ℝ) < 1 := by rw [h]; linarith
    have : (0 : ℤ) < n := by exact_mod_cast h1'
    have : n < (1 : ℤ) := by exact_mod_cast h2'
    omega
  have hrep := cot_series_rep' hxZ
  -- the terms are real
  set t : ℕ → ℝ := fun n => 1 / (x - (n + 1)) + 1 / (x + (n + 1)) with ht
  have hct : ∀ n : ℕ, (1 / ((x : ℂ) - (n + 1)) + 1 / ((x : ℂ) + (n + 1))) = ((t n : ℝ) : ℂ) := by
    intro n; simp [ht]
  have hcot : (π : ℂ) * Complex.cot (π * x) = ((π * Real.tan (π * z / 2) : ℝ) : ℂ) := by
    have e : (π : ℂ) * x = ((π / 2 - π * z / 2 : ℝ) : ℂ) := by rw [hx]; push_cast; ring
    rw [e, ← Complex.ofReal_cot, Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos,
      Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    push_cast; ring
  simp_rw [hct, hcot] at hrep
  have hsum_t : Summable t := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => 4 * x / ((n : ℝ) + 1) ^ 2)
      ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two) |>.mul_left
        (4 * x) |>.congr fun n => by push_cast; ring) (fun n => ?_)
    have hn : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hd1 : x - (n + 1) < 0 := by linarith
    have hd2 : 0 < x + (n + 1) := by linarith
    have e : t n = 2 * x / ((x - (n + 1)) * (x + (n + 1))) := by
      have h3 := hd1.ne
      have h4 := hd2.ne'
      rw [ht]; field_simp; ring
    have hprod : (x - (n + 1)) * (x + (n + 1)) < 0 := mul_neg_of_neg_of_pos hd1 hd2
    rw [e, Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : 0 < 2 * x), abs_of_neg hprod]
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    have hx2 : 2 * x ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hx2 (by linarith : (0 : ℝ) ≤ 2 * x)]
  have hHas : HasSum t (π * Real.tan (π * z / 2) - 1 / x) := by
    have h := hsum_t.hasSum
    have e : ∑' n, t n = π * Real.tan (π * z / 2) - 1 / x := by
      have := hrep
      rw [← Complex.ofReal_tsum] at this
      have h2 : ((π * Real.tan (π * z / 2) - 1 / x : ℝ) : ℂ) = ((∑' n, t n : ℝ) : ℂ) := by
        rw [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one]; exact this
      exact (Complex.ofReal_injective h2).symm
    rwa [e] at h
  -- partial sums
  set u : ℕ → ℝ := fun k => 4 * z / ((2 * k + 1) ^ 2 - z ^ 2) with hu
  have hu_eq : ∀ k : ℕ, u k = 2 / (2 * k + 1 - z) - 2 / (2 * k + 1 + z) := by
    intro k
    have h1' : 0 < 2 * (k : ℝ) + 1 - z := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    have h2' : 0 < 2 * (k : ℝ) + 1 + z := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    have h3 : (2 * (k : ℝ) + 1) ^ 2 - z ^ 2 = (2 * k + 1 - z) * (2 * k + 1 + z) := by ring
    have h4 := h1'.ne'
    have h5 := h2'.ne'
    rw [hu]
    simp only
    rw [h3]
    field_simp
    ring
  have hz1 : (1 : ℝ) - z ≠ 0 := by linarith
  have ht_eq : ∀ N : ℕ, t N = 2 / (2 * N + 3 - z) - 2 / (2 * N + 1 + z) := by
    intro N
    have e1 : x - ((N : ℝ) + 1) = -((2 * N + 1 + z) / 2) := by rw [hx]; ring
    have e2 : x + ((N : ℝ) + 1) = (2 * N + 3 - z) / 2 := by rw [hx]; ring
    simp only [ht]
    rw [e1, e2, one_div_neg_eq_neg_one_div, one_div_div, one_div_div]
    ring
  have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range (N + 1), u k
      = 1 / x + ∑ n ∈ Finset.range N, t n - 2 / (2 * N + 1 + z) := by
    intro N
    induction N with
    | zero =>
      rw [Finset.sum_range_one, hu_eq, hx, one_div_div]
      simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, hu_eq, ht_eq]
      push_cast
      ring
  have hu0 : ∀ k, 0 ≤ u k := by
    intro k
    rw [hu]
    have : z ^ 2 < (2 * (k : ℝ) + 1) ^ 2 := by
      have := Nat.cast_nonneg (α := ℝ) k; nlinarith
    exact div_nonneg (by linarith) (by linarith)
  rw [hasSum_iff_tendsto_nat_of_nonneg hu0]
  have hlim : Tendsto (fun N : ℕ => 1 / x + ∑ n ∈ Finset.range N, t n - 2 / (2 * N + 1 + z))
      atTop (𝓝 (1 / x + (π * Real.tan (π * z / 2) - 1 / x) - 0)) := by
    refine (tendsto_const_nhds.add hHas.tendsto_sum_nat).sub ?_
    have : Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1 + z) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos))
    have h := this.inv_tendsto_atTop.const_mul 2
    rw [mul_zero] at h
    exact h.congr fun N => by simp only [Pi.inv_apply]; ring
  have h2 := (hlim.congr fun N => (hpart N).symm)
  rw [show 1 / x + (π * Real.tan (π * z / 2) - 1 / x) - 0 = π * Real.tan (π * z / 2) by ring]
    at h2
  exact (tendsto_add_atTop_iff_nat 1).mp h2

/-- `sinh(ax)/sinh(bx) = ∑_k (e^{-((2k+1)b-a)x} - e^{-((2k+1)b+a)x})` for `x > 0`, `b > 0`. -/
theorem hasSum_sinh_div_sinh {a b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    HasSum (fun k : ℕ => Real.exp (-(((2 * k + 1) * b - a) * x))
      - Real.exp (-(((2 * k + 1) * b + a) * x))) (Real.sinh (a * x) / Real.sinh (b * x)) := by
  set q := Real.exp (-(2 * b * x)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left
    (Real.exp (a * x) * Real.exp (-(b * x)) - Real.exp (-(a * x)) * Real.exp (-(b * x)))
  have hsb : Real.sinh (b * x) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have e : (Real.exp (a * x) * Real.exp (-(b * x)) - Real.exp (-(a * x)) * Real.exp (-(b * x)))
      * (1 - q)⁻¹ = Real.sinh (a * x) / Real.sinh (b * x) := by
    have hB1 : 1 < Real.exp (b * x) := by
      have := Real.add_one_lt_exp (show b * x ≠ 0 by positivity); nlinarith [mul_pos hb hx]
    have hB0 : 0 < Real.exp (b * x) := Real.exp_pos _
    rw [Real.sinh_eq, Real.sinh_eq, hq, show -(2 * b * x) = -(b * x) + -(b * x) by ring,
      Real.exp_add, Real.exp_neg (b * x)]
    have h1 : 1 - (Real.exp (b * x))⁻¹ * (Real.exp (b * x))⁻¹ ≠ 0 := by
      have : (Real.exp (b * x))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hB1
      have : 0 < (Real.exp (b * x))⁻¹ := inv_pos.mpr hB0
      nlinarith
    have h2 : Real.exp (b * x) - (Real.exp (b * x))⁻¹ ≠ 0 := by
      have : (Real.exp (b * x))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hB1
      linarith
    have h3 : Real.exp (b * x) * Real.exp (b * x) - 1 ≠ 0 := by nlinarith
    field_simp
  rw [e] at hg
  have hk : ∀ k : ℕ, Real.exp (-(((2 * k + 1) * b - a) * x)) - Real.exp (-(((2 * k + 1) * b + a) * x))
      = (Real.exp (a * x) * Real.exp (-(b * x)) - Real.exp (-(a * x)) * Real.exp (-(b * x)))
        * q ^ k := by
    intro k
    rw [hq, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    simp only [sub_mul (Real.exp _), ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  exact hg.congr_fun hk

/-- **Gradshteyn and Ryzhik 3.511.2**: `∫_0^∞ sinh(ax)/sinh(bx) dx = (π/(2b)) tan(πa/(2b))` for
`0 < a < b`. -/
theorem integral_sinh_div_sinh {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∫ x in Ioi 0, Real.sinh (a * x) / Real.sinh (b * x) = π / (2 * b) * Real.tan (π * a / (2 * b)) := by
  have hb : 0 < b := ha.trans hab
  set F : ℕ → ℝ → ℝ := fun k x => Real.exp (-(((2 * k + 1) * b - a) * x))
      - Real.exp (-(((2 * k + 1) * b + a) * x)) with hF
  have hc1 : ∀ k : ℕ, 0 < (2 * k + 1) * b - a := by
    intro k; have := Nat.cast_nonneg (α := ℝ) k; nlinarith
  have hc2 : ∀ k : ℕ, 0 < (2 * k + 1) * b + a := by
    intro k; have := Nat.cast_nonneg (α := ℝ) k; nlinarith
  have hint1 : ∀ c : ℝ, 0 < c → IntegrableOn (fun x => Real.exp (-(c * x))) (Ioi 0) := by
    intro c hc
    have := integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
    simpa [neg_mul] using this
  have hval1 : ∀ c : ℝ, 0 < c → ∫ x in Ioi 0, Real.exp (-(c * x)) = 1 / c := by
    intro c hc
    have := integral_exp_mul_Ioi (a := -c) (by linarith) 0
    simp only [mul_zero, Real.exp_zero, neg_mul] at this
    rw [this]; field_simp
  have hFint : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) := fun k =>
    (hint1 _ (hc1 k)).sub (hint1 _ (hc2 k))
  have hFnn : ∀ k, ∀ x ∈ Ioi (0 : ℝ), 0 ≤ F k x := by
    intro k x hx
    simp only [hF, sub_nonneg, Real.exp_le_exp, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hx)
  have hFval : ∀ k : ℕ, ∫ x in Ioi 0, F k x
      = 1 / (2 * b) * (4 * (a / b) / ((2 * k + 1) ^ 2 - (a / b) ^ 2)) := by
    intro k
    rw [hF, integral_sub (hint1 _ (hc1 k)) (hint1 _ (hc2 k)), hval1 _ (hc1 k), hval1 _ (hc2 k)]
    have h1' := (hc1 k).ne'
    have h2' := (hc2 k).ne'
    have hb' := hb.ne'
    rw [show (2 * (k : ℝ) + 1) ^ 2 - (a / b) ^ 2
        = ((2 * k + 1) * b - a) * ((2 * k + 1) * b + a) / b ^ 2 by field_simp; ring]
    field_simp
    ring
  have hFnorm : ∀ k : ℕ, ∫ x in Ioi 0, ‖F k x‖ = ∫ x in Ioi 0, F k x := by
    intro k
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [Real.norm_of_nonneg (hFnn k x hx)]
  have hz0 : 0 < a / b := div_pos ha hb
  have hz1 : a / b < 1 := (div_lt_one hb).mpr hab
  have htan := (hasSum_tan hz0 hz1).mul_left (1 / (2 * b))
  have hsum : Summable fun k : ℕ => ∫ x in Ioi 0, ‖F k x‖ := by
    simp_rw [hFnorm, hFval]; exact htan.summable
  have hswap := integral_tsum_of_summable_integral_norm hFint hsum
  have hpt : ∫ x in Ioi 0, Real.sinh (a * x) / Real.sinh (b * x) = ∫ x in Ioi 0, ∑' k, F k x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    exact (hasSum_sinh_div_sinh hb hx).tsum_eq.symm
  rw [hpt, ← hswap]
  simp_rw [hFval]
  rw [htan.tsum_eq]
  have : π * (a / b) / 2 = π * a / (2 * b) := by ring
  rw [this]
  field_simp

end Kagey131.PaperD.FL5
