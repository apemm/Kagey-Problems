import PaperA.EveryNCorollary

/-!
# Asymptotic conclusions of Corollary `cor:every-n` (b) and (c)

Write `L = log N`, `ℓ = log L`, `c₀ = log(π/8)/2`, `ν_N = L - ℓ/2 + c₀` and
`z_N = N(1 - p_N)`. We prove, with explicit constants, that for every `N ≥ 21`

* `|z_N - ν_N - (ℓ/4 - c₀/2 + 1/8)/L| ≤ 52 ℓ²/L²` (part (c)), and
* `|z_N - ν_N| ≤ 27 ℓ/L` (the asymptotic claim of part (b)),

and restate both as `Asymptotics.IsBigO` along `N → ∞`. We also prove
`0 ≤ N u_N - z_N ≤ 2 (L + 1/4)²/N` for every `N ≥ 2`, the conversion between
`z_N` and `N u_N` used for the periodic and coupling results.
-/

namespace Kagey131

open Real

/-- `-log(1-x)` lies between `x` and `x + 2x²` for `0 ≤ x ≤ 1/2`. -/
theorem neg_log_one_sub_bounds {x : ℝ} (_hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    x ≤ -Real.log (1 - x) ∧ -Real.log (1 - x) ≤ x + 2 * x ^ 2 := by
  have hpos : 0 < 1 - x := by linarith
  constructor
  · have := Real.log_le_sub_one_of_pos hpos
    linarith
  · have h := Real.one_sub_inv_le_log_of_pos hpos
    have hinv : (1 - x)⁻¹ ≤ 1 + x + 2 * x ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith
    linarith

/-- `exp 3 < 21`. -/
theorem exp_three_lt_21 : Real.exp 3 < 21 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have he : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [he]
  have : Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 := by
    exact pow_lt_pow_left₀ h h0.le (by norm_num)
  norm_num at this ⊢
  linarith

/-- The constant `c₀ = log(π/8)/2` lies in `(-1/2, 0)`. -/
theorem c0_bounds : -1 / 2 < Real.log (Real.pi / 8) / 2 ∧ Real.log (Real.pi / 8) / 2 < 0 := by
  have h1 := log_pi_div_eight_gt_neg_one
  have h2 : Real.log (Real.pi / 8) < 0 := by
    apply Real.log_neg (by positivity)
    have := pi_lt_rat
    linarith
  constructor <;> linarith

/-- The basic size facts for `N ≥ 21`. -/
theorem every_N_sizes (N : ℕ) (hN : 21 ≤ N) :
    3 ≤ Real.log N ∧ 1 ≤ Real.log (Real.log N) ∧
      Real.log (Real.log N) ≤ Real.log N / 2 ∧
      Real.log (Real.log N) ≤ Real.log N - 1 := by
  have hN' : (21 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hL : 3 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNp]
    linarith [exp_three_lt_21]
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hl : 1 ≤ Real.log (Real.log N) := by
    rw [Real.le_log_iff_exp_le hLp]
    linarith [Real.exp_one_lt_d9]
  have hhalf : Real.log (Real.log N) ≤ Real.log N / 2 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.log (N : ℝ) / 2 by linarith)
    rw [Real.log_div (ne_of_gt hLp) (by norm_num)] at h
    have := Real.log_two_lt_d9
    linarith
  exact ⟨hL, hl, hhalf, Real.log_le_sub_one_of_pos hLp⟩

/-- `L⁴ ≤ 24 N`, from `exp L = N`. -/
theorem log_pow_four_le (N : ℕ) (hN : 1 ≤ N) : Real.log N ^ 4 ≤ 24 * N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have h := Real.pow_div_factorial_le_exp (x := Real.log N) hL 4
  rw [Real.exp_log hNp] at h
  norm_num [Nat.factorial] at h
  linarith

set_option maxHeartbeats 2000000 in
/-- The real-variable core of part (c). Here `L = log N`, `ℓ = log L`, `c = c₀`, `ζ = ζ_N`,
`z = z_N`, and `ε` is the width of the every-N bracket. -/
theorem every_N_c_core {L ℓ c ζ z ε : ℝ} (hL3 : 3 ≤ L) (hl1 : 1 ≤ ℓ) (hlhalf : ℓ ≤ L / 2)
    
    (hℓ : ℓ = Real.log L) (hc0lo : -1 / 2 < c) (hc0 : c < 0) (hζpos : 0 < ζ) (hζL : ζ ≤ L)
    (hνζ : L - ℓ / 2 + c ≤ ζ) (hzlog : ζ + Real.log ζ / 2 = L + c)
    (hzlo : ζ + 1 / (8 * ζ) - ε < z) (hzhi : z < ζ + 1 / (8 * ζ)) (hε : ε ≤ 49 / L ^ 2) :
    |z - (L - ℓ / 2 + c) - (ℓ / 4 - c / 2 + 1 / 8) / L| ≤ 52 * ℓ ^ 2 / L ^ 2 := by
  have hLp : 0 < L := by linarith
  have hζhalf : L / 2 ≤ ζ := by linarith
  have hlogζ : Real.log ζ ≤ ℓ := by rw [hℓ]; exact Real.log_le_log hζpos hζL
  -- x = (L - ζ)/L
  obtain ⟨x, hxdef⟩ : ∃ x, x = (L - ζ) / L := ⟨_, rfl⟩
  have hxL : x * L = L - ζ := by rw [hxdef]; field_simp
  have hδl : L - ζ ≤ ℓ := by linarith
  have hx0 : 0 ≤ x := by rw [hxdef]; exact div_nonneg (by linarith) hLp.le
  have hxl : x ≤ ℓ / L := by rw [hxdef]; exact div_le_div_of_nonneg_right hδl hLp.le
  have hxhalf : x ≤ 1 / 2 := by
    have : ℓ / L ≤ 1 / 2 := by rw [div_le_iff₀ hLp]; linarith
    linarith
  have hζx : ζ = L * (1 - x) := by linarith
  have hlogζx : Real.log ζ = ℓ + Real.log (1 - x) := by
    rw [hζx, Real.log_mul (ne_of_gt hLp) (by linarith), hℓ]
  obtain ⟨g, hgdef⟩ : ∃ g, g = -Real.log (1 - x) := ⟨_, rfl⟩
  obtain ⟨hgx, hgx2⟩ := neg_log_one_sub_bounds hx0 hxhalf
  rw [← hgdef] at hgx hgx2
  have hrel : x * L = ℓ / 2 - c - g / 2 := by
    have : Real.log ζ = ℓ - g := by rw [hlogζx, hgdef]; ring
    linarith
  -- A = ζ - ν - (ℓ/4 - c/2)/L
  have h1 : ℓ / 4 - c / 2 = L * (x / 2) + g / 4 := by linarith
  have h2 : (ℓ / 4 - c / 2) / L = x / 2 + g / (4 * L) := by
    rw [h1]; field_simp
  have hAeq : ζ - (L - ℓ / 2 + c) - (ℓ / 4 - c / 2) / L = (g - x) / 2 - g / (4 * L) := by
    rw [h2]; linarith
  have hg0 : 0 ≤ g := le_trans hx0 hgx
  have hx2x : 2 * x ^ 2 ≤ x := by nlinarith
  have hg2 : g ≤ 2 * x := by linarith
  have hgL : g / (4 * L) ≤ x / L := by
    rw [div_le_div_iff₀ (by positivity) hLp]
    have := mul_le_mul_of_nonneg_right (show g ≤ 4 * x by linarith) hLp.le
    linarith
  have hx2 : x ^ 2 ≤ ℓ ^ 2 / L ^ 2 := by
    have := pow_le_pow_left₀ hx0 hxl 2
    rwa [div_pow] at this
  have hxL' : x / L ≤ ℓ / L ^ 2 := by
    rw [div_le_div_iff₀ hLp (by positivity)]
    have h := mul_le_mul_of_nonneg_right (show x * L ≤ ℓ by linarith) hLp.le
    have e : x * L ^ 2 = x * L * L := by ring
    linarith
  have hl2 : ℓ ≤ ℓ ^ 2 := by rw [sq]; exact le_mul_of_one_le_right (by linarith) hl1
  have hLsq : 0 < L ^ 2 := by positivity
  have hlL : ℓ / L ^ 2 ≤ ℓ ^ 2 / L ^ 2 := div_le_div_of_nonneg_right hl2 hLsq.le
  have hgd0 : 0 ≤ g / (4 * L) := by positivity
  have hA : |ζ - (L - ℓ / 2 + c) - (ℓ / 4 - c / 2) / L| ≤ 2 * ℓ ^ 2 / L ^ 2 := by
    rw [hAeq, abs_le]
    have e : 2 * ℓ ^ 2 / L ^ 2 = ℓ ^ 2 / L ^ 2 + ℓ ^ 2 / L ^ 2 := by ring
    rw [e]
    have hP : 0 ≤ ℓ ^ 2 / L ^ 2 := by positivity
    constructor
    · linarith only [hgx, hgL, hxL', hlL, hx2, hP]
    · linarith only [hgx2, hx2, hgd0, hP]
  -- B = 1/(8ζ) - 1/(8L)
  have hBeq : 1 / (8 * ζ) - 1 / (8 * L) = (L - ζ) / (8 * ζ * L) := by
    field_simp
  have hB0 : 0 ≤ 1 / (8 * ζ) - 1 / (8 * L) := by
    rw [hBeq]; exact div_nonneg (by linarith) (by positivity)
  have hB : 1 / (8 * ζ) - 1 / (8 * L) ≤ ℓ / (4 * L ^ 2) := by
    rw [hBeq, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (L - ζ) * (4 * L ^ 2) ≤ ℓ * (4 * L ^ 2) :=
      mul_le_mul_of_nonneg_right hδl (by positivity)
    have hL2 : 4 * L ^ 2 ≤ 8 * ζ * L := by
      have := mul_le_mul_of_nonneg_right hζhalf hLp.le
      have e : 4 * L ^ 2 = 8 * (L / 2 * L) := by ring
      have e2 : 8 * ζ * L = 8 * (ζ * L) := by ring
      linarith
    have h2 : ℓ * (4 * L ^ 2) ≤ ℓ * (8 * ζ * L) :=
      mul_le_mul_of_nonneg_left hL2 (by linarith)
    linarith
  have hC : |z - ζ - 1 / (8 * ζ)| ≤ 49 / L ^ 2 := by
    rw [abs_le]; constructor <;> linarith
  have hsplit : z - (L - ℓ / 2 + c) - (ℓ / 4 - c / 2 + 1 / 8) / L =
      (ζ - (L - ℓ / 2 + c) - (ℓ / 4 - c / 2) / L) + (1 / (8 * ζ) - 1 / (8 * L)) +
        (z - ζ - 1 / (8 * ζ)) := by
    field_simp; ring
  rw [hsplit]
  have hb1 : ℓ / (4 * L ^ 2) ≤ ℓ ^ 2 / L ^ 2 := by
    have : ℓ / (4 * L ^ 2) ≤ ℓ / L ^ 2 :=
      div_le_div_of_nonneg_left (by linarith) hLsq (by linarith)
    linarith
  have hb2 : 49 / L ^ 2 ≤ 49 * ℓ ^ 2 / L ^ 2 := by
    apply div_le_div_of_nonneg_right _ hLsq.le
    have : 1 ≤ ℓ ^ 2 := le_trans hl1 hl2
    linarith
  have hsum : 2 * ℓ ^ 2 / L ^ 2 + ℓ ^ 2 / L ^ 2 + 49 * ℓ ^ 2 / L ^ 2 = 52 * ℓ ^ 2 / L ^ 2 := by
    ring
  have hBabs : |1 / (8 * ζ) - 1 / (8 * L)| ≤ ℓ / (4 * L ^ 2) := by
    rw [abs_of_nonneg hB0]; exact hB
  have htri := abs_add_three (ζ - (L - ℓ / 2 + c) - (ℓ / 4 - c / 2) / L)
    (1 / (8 * ζ) - 1 / (8 * L)) (z - ζ - 1 / (8 * ζ))
  linarith

/-- The width of the every-N bracket is at most `49/L²` for `N ≥ 21`. -/
theorem every_N_eps_le (N : ℕ) (hN : 21 ≤ N) :
    zetaN N * (zetaN N + 1) / N + 1 / (16 * zetaN N ^ 2) ≤ 49 / Real.log N ^ 2 := by
  obtain ⟨hL3, -, -, hlsub⟩ := every_N_sizes N hN
  have hN2 : 2 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hζpos : 0 < zetaN N := zetaN_pos N (by omega)
  have hζL := zetaN_le_log N hN2
  have hνζ := (every_N_zeta_bracket N hN2).1
  have hc := c0_bounds
  have hνL : Real.log N / 2 ≤ zetaN N := by
    have : Real.log N / 2 ≤ nuN N := by unfold nuN; linarith
    linarith
  have h4 := log_pow_four_le N (by omega)
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hfirst : zetaN N * (zetaN N + 1) / N ≤ 48 / Real.log N ^ 2 := by
    rw [div_le_div_iff₀ hNp (by positivity)]
    have hzz : zetaN N * (zetaN N + 1) ≤ 2 * Real.log N ^ 2 := by nlinarith
    nlinarith
  have hsecond : 1 / (16 * zetaN N ^ 2) ≤ 1 / Real.log N ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have : 48 / Real.log N ^ 2 + 1 / Real.log N ^ 2 = 49 / Real.log (N : ℝ) ^ 2 := by ring
  linarith

/-- Corollary `cor:every-n` (c) with an explicit constant: for every `N ≥ 21`,
`|z_N - ν_N - (ℓ/4 - c₀/2 + 1/8)/L| ≤ 52 ℓ²/L²`, where `L = log N` and `ℓ = log L`. -/
theorem every_N_corollary_c_bound (N : ℕ) (hN : 21 ≤ N) :
    |(N : ℝ) * (1 - pN N) - nuN N -
        (Real.log (Real.log N) / 4 - Real.log (Real.pi / 8) / 4 + 1 / 8) / Real.log N| ≤
      52 * Real.log (Real.log N) ^ 2 / Real.log N ^ 2 := by
  obtain ⟨hL3, hl1, hlhalf, -⟩ := every_N_sizes N hN
  have hN2 : 2 ≤ N := by omega
  obtain ⟨hc0lo, hc0⟩ := c0_bounds
  have hνζ := (every_N_zeta_bracket N hN2).1
  obtain ⟨hzlo, hzhi⟩ := every_N_crossing N hN2
  have hcore := every_N_c_core (c := Real.log (Real.pi / 8) / 2) hL3 hl1 hlhalf rfl hc0lo hc0
    (zetaN_pos N (by omega)) (zetaN_le_log N hN2) (by unfold nuN at hνζ; linarith)
    (zetaN_log N (by omega)) hzlo hzhi (every_N_eps_le N hN)
  have hν : nuN N = Real.log N - Real.log (Real.log N) / 2 + Real.log (Real.pi / 8) / 2 := rfl
  rw [hν]
  have e : Real.log (Real.pi / 8) / 4 = Real.log (Real.pi / 8) / 2 / 2 := by ring
  rw [e]
  exact hcore

/-- The asymptotic claim of Corollary `cor:every-n` (b) with an explicit constant:
`|z_N - ν_N| ≤ 27 ℓ/L` for every `N ≥ 21`. -/
theorem every_N_corollary_b_bound (N : ℕ) (hN : 21 ≤ N) :
    |(N : ℝ) * (1 - pN N) - nuN N| ≤ 27 * Real.log (Real.log N) / Real.log N := by
  obtain ⟨hL3, hl1, hlhalf, -⟩ := every_N_sizes N hN
  obtain ⟨hc0lo, hc0hi⟩ := c0_bounds
  have hc := every_N_corollary_c_bound N hN
  set L := Real.log (N : ℝ)
  set ℓ := Real.log L
  set c := Real.log (Real.pi / 8)
  have hLp : 0 < L := by linarith
  have hmain : |(ℓ / 4 - c / 4 + 1 / 8) / L| ≤ ℓ / L := by
    rw [abs_div, abs_of_pos hLp]
    apply div_le_div_of_nonneg_right _ hLp.le
    rw [abs_le]; constructor <;> linarith
  have hsq : 52 * ℓ ^ 2 / L ^ 2 ≤ 26 * ℓ / L := by
    rw [div_le_div_iff₀ (by positivity) hLp]
    have : ℓ * L ≤ L * L / 2 := by nlinarith
    nlinarith
  have htri := abs_add_three ((N : ℝ) * (1 - pN N) - nuN N - (ℓ / 4 - c / 4 + 1 / 8) / L)
    ((ℓ / 4 - c / 4 + 1 / 8) / L) 0
  simp only [abs_zero, add_zero, sub_add_cancel] at htri
  have e : 26 * ℓ / L + ℓ / L = 27 * ℓ / L := by ring
  linarith

/-- Corollary `cor:every-n` (b), asymptotic form: `z_N = ν_N + O(log L / L)`. -/
theorem every_N_corollary_b_isBigO :
    (fun N : ℕ => (N : ℝ) * (1 - pN N) - nuN N) =O[Filter.atTop]
      (fun N : ℕ => Real.log (Real.log N) / Real.log N) := by
  apply Asymptotics.IsBigO.of_bound 27
  filter_upwards [Filter.eventually_ge_atTop 21] with N hN
  obtain ⟨hL3, hl1, -, -⟩ := every_N_sizes N hN
  have hpos : (0 : ℝ) ≤ Real.log (Real.log N) / Real.log N :=
    div_nonneg (by linarith) (by linarith)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hpos]
  have := every_N_corollary_b_bound N hN
  calc _ ≤ _ := this
    _ = _ := by ring

/-- Corollary `cor:every-n` (c), asymptotic form:
`z_N = ν_N + (ℓ/4 - c₀/2 + 1/8)/L + O(ℓ²/L²)`. -/
theorem every_N_corollary_c_isBigO :
    (fun N : ℕ => (N : ℝ) * (1 - pN N) - nuN N -
        (Real.log (Real.log N) / 4 - Real.log (Real.pi / 8) / 4 + 1 / 8) / Real.log N)
      =O[Filter.atTop] (fun N : ℕ => Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by
  apply Asymptotics.IsBigO.of_bound 52
  filter_upwards [Filter.eventually_ge_atTop 21] with N hN
  have hpos : (0 : ℝ) ≤ Real.log (Real.log N) ^ 2 / Real.log N ^ 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hpos]
  have := every_N_corollary_c_bound N hN
  calc _ ≤ _ := this
    _ = _ := by ring

/-- The conversion between `z_N` and `N u_N`: `0 ≤ N u_N - z_N ≤ 2 (L + 1/4)²/N` for `N ≥ 2`. -/
theorem N_uN_sub_zN (N : ℕ) (hN : 2 ≤ N) :
    0 ≤ (N : ℝ) * uN N - (N : ℝ) * (1 - pN N) ∧
      (N : ℝ) * uN N - (N : ℝ) * (1 - pN N) ≤ 2 * (Real.log N + 1 / 4) ^ 2 / N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hu : 0 < uN N := uab_pos (by omega) (by omega)
  have hz := N_one_sub_pN N hN
  obtain ⟨-, hzhi⟩ := every_N_crossing N hN
  have hζ := half_lt_zetaN N hN
  have hζL := zetaN_le_log N hN
  have hY : zetaN N + 1 / (8 * zetaN N) < Real.log N + 1 / 4 := by
    have : 1 / (8 * zetaN N) < 1 / 4 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  set z := (N : ℝ) * (1 - pN N)
  have hz0 : 0 < z := by rw [hz]; positivity
  have hzY : z < Real.log N + 1 / 4 := lt_trans hzhi hY
  -- N u = z N/(N - z), so N u - z = z²/(N - z)
  have hLhalf : Real.log N + 1 / 4 ≤ (N : ℝ) / 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N / 2 by positivity)
    rw [Real.log_div (ne_of_gt hNp) (by norm_num)] at h
    have := Real.log_two_lt_d9
    linarith
  have hzN : z < N / 2 := by linarith
  have hu1 : uN N = z / (N - z) := by
    rw [hz]; field_simp; ring
  have hNz : 0 < (N : ℝ) - z := by linarith
  have hdiff : (N : ℝ) * uN N - z = z ^ 2 / (N - z) := by
    rw [hu1]; field_simp; ring
  rw [hdiff]
  constructor
  · positivity
  · rw [div_le_div_iff₀ hNz hNp]
    have hz2 : z ^ 2 ≤ (Real.log N + 1 / 4) ^ 2 := pow_le_pow_left₀ hz0.le hzY.le 2
    nlinarith

#print axioms every_N_corollary_c_bound
#print axioms every_N_corollary_b_bound
#print axioms every_N_corollary_b_isBigO
#print axioms every_N_corollary_c_isBigO
#print axioms N_uN_sub_zN

end Kagey131
