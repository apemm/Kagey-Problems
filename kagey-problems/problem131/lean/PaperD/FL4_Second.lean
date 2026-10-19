import PaperD.FL4_Main

/-!
# Paper F, remark after the proof of Proposition 3.7 (track FL4): the `L^{-3}` term

The remark says: with one more term in Taylor's theorem the same argument adds the term
`-Θ''(1)(log 2)²/(2L³)` to the expansion of `c_N`, with error `O(L^{-4})`, where
`L = log N + Θ'(1)` and `Θ''(1) = π²/2 - 4`.

* `lg_even`: `|log Γ(1+u) + log Γ(1-u) - π²u²/6| ≤ 4u⁴` for `0 < πu ≤ 1` (reflection formula and
  `x - x³/6 < sin x ≤ x - x³/6 + x⁵/100`), which gives `ψ'(1) = π²/6 = ζ(2)` in effect;
* `lg_odd`: `|log Γ(1+u) - log Γ(1-u) + 2γu| ≤ 8u³` for `0 < u ≤ 1/2` (the Euler limit
  `log Γ = lim logGammaSeq` of Mathlib's Bohr–Mollerup file, and `H_n - log n → γ`);
* `theta_taylor2`: `|Θ(1-ε) - (log 2 - ε Θ'(1) + ε² (π²/4 - 2))| ≤ 66 ε³` for `0 < ε ≤ 3/20`,
  i.e. the second-order Taylor expansion of `Θ` at `1` with `Θ''(1)/2 = π²/4 - 2`;
* `aging_expansion2`: `c_N = 1 - log 2/L - (π²/2 - 4)(log 2)²/(2L³) + O((log N)^{-4})`,
  uniformly over all even `N ≥ 4`.

The numbers at `N = 200` in the remark are not formalized.
-/

namespace Kagey131.PaperD.FL4

open Real Set Filter Topology Finset

/-- `|log(1-x) + x + x²/2| ≤ 2|x|³` for `|x| ≤ 1/2`. -/
theorem log_one_sub_taylor2 {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 - x) + x + x ^ 2 / 2| ≤ 2 * |x| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by linarith) 2
  have e : (∑ i ∈ range 2, x ^ (i + 1) / ((i : ℝ) + 1)) = x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ]; ring
  rw [e] at h
  have h0 : 0 ≤ |x| := abs_nonneg x
  have h1 : |x| ^ 3 / (1 - |x|) ≤ 2 * |x| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg h0 3]
  rw [show Real.log (1 - x) + x + x ^ 2 / 2 = x + x ^ 2 / 2 + Real.log (1 - x) by ring]
  exact h.trans h1

/-- `|log(1+t) - log(1-t) - 2t| ≤ 4t³` for `0 ≤ t ≤ 1/2`. -/
theorem log_odd_taylor {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    |Real.log (1 + t) - Real.log (1 - t) - 2 * t| ≤ 4 * t ^ 3 := by
  have a := log_one_sub_taylor2 (x := t) (by rw [abs_of_nonneg ht0]; exact ht)
  have b := log_one_sub_taylor2 (x := -t) (by rw [abs_neg, abs_of_nonneg ht0]; exact ht)
  rw [abs_neg, abs_of_nonneg ht0, sub_neg_eq_add] at b
  rw [abs_of_nonneg ht0] at a
  rw [abs_le] at a b ⊢
  constructor <;> nlinarith

/-- `∑_{m<n} 1/(m+1)³ ≤ 2`. -/
theorem sum_inv_cube_le (n : ℕ) : ∑ m ∈ range n, 1 / ((m : ℝ) + 1) ^ 3 ≤ 2 := by
  have key : ∀ n : ℕ, ∑ m ∈ range n, 1 / ((m : ℝ) + 1) ^ 3 ≤ 2 - 2 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hk : (0 : ℝ) ≤ k := k.cast_nonneg
      have h1 : 1 / ((k : ℝ) + 1) ^ 3 ≤ 2 / ((k : ℝ) + 1) - 2 / ((k : ℝ) + 2) := by
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg hk hk) hk, mul_nonneg hk hk, hk]
      push_cast
      rw [show (k : ℝ) + 1 + 1 = k + 2 by ring]
      linarith
  have h := key n
  have : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
  linarith

/-- The odd part of `log Γ` at `1`: `|log Γ(1+u) - log Γ(1-u) + 2γu| ≤ 8u³` for `0 < u ≤ 1/2`. -/
theorem lg_odd {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2) :
    |lg (1 + u) - lg (1 - u) + 2 * eulerMascheroniConstant * u| ≤ 8 * u ^ 3 := by
  have t1 := Real.BohrMollerup.tendsto_log_gamma (show 0 < 1 + u by linarith)
  have t2 := Real.BohrMollerup.tendsto_log_gamma (show 0 < 1 - u by linarith)
  set γ := eulerMascheroniConstant with hγ
  set a : ℕ → ℝ := fun n =>
    Real.BohrMollerup.logGammaSeq (1 + u) n - Real.BohrMollerup.logGammaSeq (1 - u) n with ha
  have ta : Tendsto a atTop (𝓝 (lg (1 + u) - lg (1 - u))) := by unfold lg; exact t1.sub t2
  -- each term of the sum
  have hterm : ∀ m : ℕ, |Real.log (1 + u + m) - Real.log (1 - u + m) - 2 * u * (1 / ((m : ℝ) + 1))| ≤
      4 * u ^ 3 * (1 / ((m : ℝ) + 1) ^ 3) := by
    intro m
    have hk : (1 : ℝ) ≤ (m : ℝ) + 1 := by have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith
    have hk0 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    set t := u / ((m : ℝ) + 1) with ht
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 / 2 := by
      rw [ht, div_le_iff₀ hk0]; nlinarith
    have e1 : 1 + u + (m : ℝ) = ((m : ℝ) + 1) * (1 + t) := by rw [ht]; field_simp; ring
    have e2 : 1 - u + (m : ℝ) = ((m : ℝ) + 1) * (1 - t) := by rw [ht]; field_simp; ring
    rw [e1, e2, Real.log_mul hk0.ne' (by linarith), Real.log_mul hk0.ne' (by linarith)]
    have h := log_odd_taylor ht0 ht1
    have e3 : 2 * u * (1 / ((m : ℝ) + 1)) = 2 * t := by rw [ht]; ring
    have e4 : 4 * u ^ 3 * (1 / ((m : ℝ) + 1) ^ 3) = 4 * t ^ 3 := by rw [ht]; field_simp
    rw [e3, e4]
    rw [show Real.log ((m : ℝ) + 1) + Real.log (1 + t) - (Real.log ((m : ℝ) + 1) + Real.log (1 - t)) - 2 * t =
      Real.log (1 + t) - Real.log (1 - t) - 2 * t by ring]
    exact h
  -- the harmonic numbers
  have hHcast : ∀ n : ℕ, ((harmonic n : ℚ) : ℝ) = ∑ m ∈ range n, 1 / ((m : ℝ) + 1) := by
    intro n; simp [harmonic, Rat.cast_sum]
  have hH : Tendsto (fun n : ℕ => ((harmonic (n + 1) : ℚ) : ℝ) - Real.log n) atTop (𝓝 γ) := by
    have h1 := Real.tendsto_harmonic_sub_log
    have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr (fun n => ?_)
    rw [harmonic_succ]; push_cast; ring
  -- the bound for each `n`
  have hb : ∀ n : ℕ, |a n + 2 * γ * u| ≤
      2 * u * |((harmonic (n + 1) : ℚ) : ℝ) - Real.log n - γ| + 8 * u ^ 3 := by
    intro n
    have hform : a n + 2 * γ * u = -(2 * u * (((harmonic (n + 1) : ℚ) : ℝ) - Real.log n - γ)) -
        ∑ m ∈ range (n + 1), (Real.log (1 + u + m) - Real.log (1 - u + m) - 2 * u * (1 / ((m : ℝ) + 1))) := by
      rw [ha]
      simp only [Real.BohrMollerup.logGammaSeq]
      rw [hHcast, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have e1 : ∀ m : ℕ, Real.log (1 + u + m) = Real.log (1 + u + (m : ℝ)) := fun _ => rfl
      ring
    rw [hform]
    have hs : |∑ m ∈ range (n + 1), (Real.log (1 + u + m) - Real.log (1 - u + m) - 2 * u * (1 / ((m : ℝ) + 1)))|
        ≤ 8 * u ^ 3 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum (fun m _ => hterm m)).trans ?_
      rw [← Finset.mul_sum]
      have := sum_inv_cube_le (n + 1)
      have hu3 : 0 ≤ 4 * u ^ 3 := by positivity
      nlinarith
    calc |-(2 * u * (((harmonic (n + 1) : ℚ) : ℝ) - Real.log n - γ)) -
          ∑ m ∈ range (n + 1), (Real.log (1 + u + m) - Real.log (1 - u + m) - 2 * u * (1 / ((m : ℝ) + 1)))|
        ≤ |-(2 * u * (((harmonic (n + 1) : ℚ) : ℝ) - Real.log n - γ))| +
          |∑ m ∈ range (n + 1), (Real.log (1 + u + m) - Real.log (1 - u + m) - 2 * u * (1 / ((m : ℝ) + 1)))| :=
          abs_sub _ _
      _ ≤ 2 * u * |((harmonic (n + 1) : ℚ) : ℝ) - Real.log n - γ| + 8 * u ^ 3 := by
          rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * u)]
          linarith
  -- pass to the limit
  have tl : Tendsto (fun n => |a n + 2 * γ * u|) atTop (𝓝 |lg (1 + u) - lg (1 - u) + 2 * γ * u|) :=
    (ta.add_const _).abs
  have tr : Tendsto (fun n : ℕ => 2 * u * |((harmonic (n + 1) : ℚ) : ℝ) - Real.log n - γ| + 8 * u ^ 3)
      atTop (𝓝 (8 * u ^ 3)) := by
    have h0 : Tendsto (fun n : ℕ => ((harmonic (n + 1) : ℚ) : ℝ) - Real.log n - γ) atTop (𝓝 0) := by
      have := hH.sub_const γ; rwa [sub_self] at this
    have := ((h0.abs).const_mul (2 * u)).add_const (8 * u ^ 3)
    simpa using this
  exact le_of_tendsto_of_tendsto' tl tr hb

/-- The even part of `log Γ` at `1`: `|log Γ(1+u) + log Γ(1-u) - π²u²/6| ≤ 4u⁴` for `0 < πu ≤ 1`. -/
theorem lg_even {u : ℝ} (hu0 : 0 < u) (hx : π * u ≤ 1) :
    |lg (1 + u) + lg (1 - u) - π ^ 2 * u ^ 2 / 6| ≤ 4 * u ^ 4 := by
  have hp3 := Real.pi_gt_three
  have hp := Real.pi_lt_d2
  have hu1 : u < 1 := by nlinarith
  have hsum : lg (1 + u) + lg (1 - u) = Real.log (π * u / Real.sin (π * u)) := by
    unfold lg
    rw [← Real.log_mul (Real.Gamma_pos_of_pos (by linarith)).ne' (Real.Gamma_pos_of_pos (by linarith)).ne',
      Gamma_one_add_mul_one_sub hu0]
  rw [hsum]
  set x := π * u with hxdef
  have hx0 : 0 < x := by positivity
  have hs1 := Real.sin_gt_sub_cube hx0
  have hs2 : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 100 := by
    have h := Real.sin_bound (x := x) (by rw [abs_of_pos hx0]; exact hx)
    rw [abs_of_pos hx0] at h
    linarith [(abs_le.mp h).2]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have hden : 0 < x - x ^ 3 / 6 := by nlinarith [mul_le_mul_of_nonneg_left hx2 hx0.le]
  have hsin : 0 < Real.sin x := by linarith
  -- upper bound
  have hup : Real.log (x / Real.sin x) ≤ x ^ 2 / 6 + x ^ 4 / 30 := by
    have h1 : x / Real.sin x - 1 ≤ x ^ 2 / 6 + x ^ 4 / 30 := by
      rw [sub_le_iff_le_add, div_le_iff₀ hsin]
      have : x ≤ (x ^ 2 / 6 + x ^ 4 / 30 + 1) * (x - x ^ 3 / 6) := by
        nlinarith [pow_pos hx0 5, pow_pos hx0 7]
      have h2 : (x ^ 2 / 6 + x ^ 4 / 30 + 1) * (x - x ^ 3 / 6) ≤ (x ^ 2 / 6 + x ^ 4 / 30 + 1) * Real.sin x :=
        mul_le_mul_of_nonneg_left hs1.le (by positivity)
      linarith
    exact (Real.log_le_sub_one_of_pos (by positivity)).trans h1
  -- lower bound
  have hlo : x ^ 2 / 6 - x ^ 4 / 100 ≤ Real.log (x / Real.sin x) := by
    have h1 : Real.log (Real.sin x / x) ≤ Real.sin x / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (x / Real.sin x) = -Real.log (Real.sin x / x) := by
      rw [← Real.log_inv, inv_div]
    have h3 : Real.sin x / x ≤ 1 - x ^ 2 / 6 + x ^ 4 / 100 := by
      rw [div_le_iff₀ hx0]; nlinarith
    linarith
  have hx4 : x ^ 4 / 30 ≤ 4 * u ^ 4 := by
    rw [hxdef, mul_pow]
    have hp2 : π ^ 2 ≤ 10 := by nlinarith [Real.pi_pos]
    have : π ^ 4 ≤ 120 := by
      have e : π ^ 4 = (π ^ 2) ^ 2 := by ring
      rw [e]; nlinarith [pow_pos Real.pi_pos 2]
    have := pow_nonneg hu0.le 4
    nlinarith
  have e : π ^ 2 * u ^ 2 / 6 = x ^ 2 / 6 := by rw [hxdef]; ring
  rw [e, abs_le]
  have : 0 ≤ x ^ 4 := by positivity
  constructor <;> nlinarith

/-- `log Γ(2 - 2ε) = log(1 - 2ε) + log Γ(1 - 2ε)`. -/
theorem lg_two_sub {ε : ℝ} (hε1 : ε < 1 / 2) : lg (2 - 2 * ε) = Real.log (1 - 2 * ε) + lg (1 - 2 * ε) := by
  unfold lg
  rw [show 2 - 2 * ε = (1 - 2 * ε) + 1 by ring, Real.Gamma_add_one (by linarith),
    Real.log_mul (by linarith) (Real.Gamma_pos_of_pos (by linarith)).ne']

/-- The second-order expansion of `Θ` at `1`:
`|Θ(1-ε) - (log 2 - ε (γ + 2 - 2 log 2) + ε² (π²/4 - 2))| ≤ 66 ε³` for `0 < ε ≤ 3/20`;
here `π²/4 - 2 = Θ''(1)/2` with `Θ''(1) = π²/2 - 4` as in the remark after Proposition 3.7. -/
theorem theta_taylor2 {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 3 / 20) :
    |Theta (1 - ε) - (Real.log 2 - ε * (eulerMascheroniConstant + 2 - 2 * Real.log 2) +
        ε ^ 2 * (π ^ 2 / 4 - 2))| ≤ 66 * ε ^ 3 := by
  have hp := Real.pi_lt_d2
  rw [Theta_eq hε0 (by linarith), lg_two_sub (by linarith)]
  have P1 := lg_even hε0 (by nlinarith [Real.pi_pos])
  have P2 := lg_even (u := 2 * ε) (by linarith) (by nlinarith [Real.pi_pos])
  have Q1 := lg_odd hε0 (by linarith)
  have Q2 := lg_odd (u := 2 * ε) (by linarith) (by linarith)
  have h2ε : |2 * ε| = 2 * ε := abs_of_pos (by linarith)
  have L1 := log_one_sub_taylor2 (x := 2 * ε) (by rw [h2ε]; linarith)
  rw [h2ε] at L1
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [hl4]
  have e4 : ε ^ 4 ≤ 3 / 20 * ε ^ 3 := by
    have := pow_pos hε0 3
    nlinarith
  have hε3 : 0 < ε ^ 3 := by positivity
  rw [abs_le] at P1 P2 Q1 Q2 L1 ⊢
  ring_nf at P1 P2 Q1 Q2 L1 e4 ⊢
  constructor <;> linarith

/-- The final algebra of the second-order expansion. -/
theorem expansion2_algebra {ε q ℓ L S A B : ℝ} (hℓ : 1 ≤ ℓ) (hL : ℓ ≤ L) (hε0 : 0 < ε)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / ℓ) (hε : ε ≤ 2 / ℓ) (hS : |S| ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : |ε - q| ≤ B / ℓ ^ 3) (h2 : |ε * L - q * L - S * ε ^ 2| ≤ A / ℓ ^ 3) :
    |ε - q - S * q ^ 2 / L| ≤ (A + 3 * B) / ℓ ^ 4 := by
  have hℓ0 : 0 < ℓ := by linarith
  have hL0 : 0 < L := by linarith
  have e : ε - q - S * q ^ 2 / L = (ε * L - q * L - S * ε ^ 2) / L + S * ((ε - q) * (ε + q)) / L := by
    field_simp; ring
  rw [e]
  have t1 : |(ε * L - q * L - S * ε ^ 2) / L| ≤ A / ℓ ^ 4 := by
    rw [abs_div, abs_of_pos hL0, div_le_div_iff₀ hL0 (by positivity)]
    have : |ε * L - q * L - S * ε ^ 2| * ℓ ^ 3 ≤ A := by rwa [le_div_iff₀ (by positivity)] at h2
    calc |ε * L - q * L - S * ε ^ 2| * ℓ ^ 4 = (|ε * L - q * L - S * ε ^ 2| * ℓ ^ 3) * ℓ := by ring
      _ ≤ A * ℓ := mul_le_mul_of_nonneg_right this hℓ0.le
      _ ≤ A * L := mul_le_mul_of_nonneg_left hL hA
  have hεq : ε + q ≤ 3 / ℓ := by
    have : 2 / ℓ + 1 / ℓ = 3 / ℓ := by ring
    linarith
  have t2 : |S * ((ε - q) * (ε + q)) / L| ≤ 3 * B / ℓ ^ 4 := by
    rw [abs_div, abs_of_pos hL0, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ ε + q)]
    have hm : |S| * (|ε - q| * (ε + q)) ≤ 1 * (B / ℓ ^ 3 * (3 / ℓ)) := by
      apply mul_le_mul hS _ (by positivity) (by norm_num)
      exact mul_le_mul h1 hεq (by linarith) (by positivity)
    have e2 : 1 * (B / ℓ ^ 3 * (3 / ℓ)) = 3 * B / ℓ ^ 4 := by field_simp
    rw [e2] at hm
    have hL1 : 1 ≤ L := by linarith
    calc |S| * (|ε - q| * (ε + q)) / L ≤ |S| * (|ε - q| * (ε + q)) :=
          div_le_self (by positivity) hL1
      _ ≤ 3 * B / ℓ ^ 4 := hm
  calc |(ε * L - q * L - S * ε ^ 2) / L + S * ((ε - q) * (ε + q)) / L|
      ≤ |(ε * L - q * L - S * ε ^ 2) / L| + |S * ((ε - q) * (ε + q)) / L| := abs_add_le _ _
    _ ≤ A / ℓ ^ 4 + 3 * B / ℓ ^ 4 := add_le_add t1 t2
    _ = (A + 3 * B) / ℓ ^ 4 := by ring

/-- The remark after the proof of Proposition 3.7 of Paper F: with `L = log N + γ + 2 - 2 log 2`,
`c_N = 1 - log 2/L - Θ''(1) (log 2)²/(2L³) + O((log N)^{-4})` with `Θ''(1) = π²/2 - 4`,
uniformly over all even `N = 2m ≥ 4`. -/
theorem aging_expansion2 : ∃ C : ℝ, ∀ m : ℕ, 2 ≤ m → ∀ c ∈ Ioo (0 : ℝ) 2,
    agBin (agingP c) (2 * m - 1) m = agBin (agingP c) (2 * m - 1) (2 * m - 1 + 1) →
    |c - (1 - Real.log 2 / (Real.log (2 * (m : ℝ)) + eulerMascheroniConstant + 2 - 2 * Real.log 2)
        - (π ^ 2 / 2 - 4) * Real.log 2 ^ 2 /
          (2 * (Real.log (2 * (m : ℝ)) + eulerMascheroniConstant + 2 - 2 * Real.log 2) ^ 3))| ≤
      C / Real.log (2 * (m : ℝ)) ^ 4 := by
  obtain ⟨C₁, hC₁⟩ := aging_expansion
  obtain ⟨Cl, hCl⟩ := llt_rate (a := 7 / 10) (b := 1) (by norm_num) (by norm_num)
  obtain ⟨d₀, hd₀, hd₀le⟩ := dc_lower (a := 7 / 10) (b := 1) (by norm_num) (by norm_num)
  set T := eulerMascheroniConstant + 2 - 2 * Real.log 2 with hT
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hT0 : 0 ≤ T := by
    have := one_half_lt_eulerMascheroniConstant; rw [hT]; linarith
  set S := π ^ 2 / 4 - 2 with hS
  have hSb : |S| ≤ 1 := by
    have h1 := Real.pi_gt_three; have h2 := Real.pi_lt_d2
    rw [hS, abs_le]; constructor <;> nlinarith
  set B := |C₁| with hB
  have hB0 : 0 ≤ B := abs_nonneg _
  set C' := |Cl| with hC'
  have hC'0 : 0 ≤ C' := abs_nonneg _
  set D := 2 * (C' / d₀) + 4 with hD
  have hD0 : 0 ≤ D := by positivity
  have hev := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 9 one_ne_zero).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  set ℓ₀ := max (max 17 (Real.sqrt B + 1)) (max (Real.log (max X 4) + 1) (Real.sqrt (2 * C' / d₀ + 1) + 1))
    with hℓ₀
  refine ⟨max (528 + D + 3 * B) (3 * ℓ₀ ^ 4), fun m hm c hc hcross => ?_⟩
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set N : ℝ := 2 * (m : ℝ) with hN
  have hN4 : 4 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  set ℓ := Real.log N with hℓ
  have hℓ1 : 1 ≤ ℓ := log_ge_one hN4
  have hℓ0 : 0 < ℓ := by linarith
  set L := ℓ + T with hLdef
  have hL : ℓ ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  set q := Real.log 2 / L with hq
  have hq0 : 0 ≤ q := div_nonneg (Real.log_pos (by norm_num)).le hL0.le
  have hq1 : q ≤ 1 / ℓ := by
    rw [hq, div_le_div_iff₀ hL0 hℓ0]; nlinarith
  obtain ⟨hcN, _, huniq⟩ := cN_spec (by omega : 1 ≤ m)
  have hceq : c = cN m := huniq c hc hcross
  rw [← hceq] at hcN
  set ε := 1 - c with hε
  have hε0 : 0 < ε := by linarith [hcN.2]
  have hgoal : c - (1 - Real.log 2 / (Real.log (2 * (m : ℝ)) + eulerMascheroniConstant + 2 - 2 * Real.log 2)
      - (π ^ 2 / 2 - 4) * Real.log 2 ^ 2 /
        (2 * (Real.log (2 * (m : ℝ)) + eulerMascheroniConstant + 2 - 2 * Real.log 2) ^ 3)) =
      -(ε - q - S * q ^ 2 / L) := by
    rw [hε, hq, hLdef, hℓ, hT, hS, hN]; field_simp; ring
  rw [hgoal, abs_neg]
  rcases lt_or_ge ℓ ℓ₀ with hsmall | hlarge
  · -- small `N`: the trivial bound
    have hq' : q ≤ 1 := hq1.trans (by rw [div_le_one hℓ0]; exact hℓ1)
    have hSq : |S * q ^ 2 / L| ≤ 1 := by
      rw [abs_div, abs_mul, abs_of_pos hL0, div_le_one hL0, abs_of_nonneg (sq_nonneg q)]
      have : q ^ 2 ≤ 1 := by nlinarith
      nlinarith [abs_nonneg S]
    have hb : |ε - q - S * q ^ 2 / L| ≤ 3 := by
      rw [abs_le] at hSq ⊢; constructor <;> linarith [hcN.1, hcN.2]
    have hℓ4 : ℓ ^ 4 ≤ ℓ₀ ^ 4 := pow_le_pow_left₀ hℓ0.le hsmall.le 4
    have h4 : 0 < ℓ ^ 4 := by positivity
    refine hb.trans ?_
    rw [le_div_iff₀ h4]
    calc 3 * ℓ ^ 4 ≤ 3 * ℓ₀ ^ 4 := by linarith
      _ ≤ max (528 + D + 3 * B) (3 * ℓ₀ ^ 4) := le_max_right _ _
  · -- large `N`
    have hℓ17 : 17 ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlarge
    have hℓB : Real.sqrt B + 1 ≤ ℓ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlarge
    have hℓX : Real.log (max X 4) + 1 ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlarge
    have hℓC : Real.sqrt (2 * C' / d₀ + 1) + 1 ≤ ℓ :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlarge
    -- the first-order expansion: `|ε - q| ≤ B/ℓ³`
    have h1 : |ε - q| ≤ B / ℓ ^ 3 := by
      have h := hC₁ m hm c hc hcross
      rw [← hN, ← hℓ] at h
      have e : c - (1 - Real.log 2 / (ℓ + eulerMascheroniConstant + 2 - 2 * Real.log 2)) = -(ε - q) := by
        rw [hε, hq, hLdef, hT]; ring
      rw [e, abs_neg] at h
      exact h.trans (div_le_div_of_nonneg_right (le_abs_self _) (by positivity))
    have hBℓ : B ≤ ℓ ^ 2 := by
      have h := Real.sq_sqrt hB0
      have : Real.sqrt B ≤ ℓ := by linarith
      calc B = Real.sqrt B ^ 2 := h.symm
        _ ≤ ℓ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg B) this 2
    have hε2 : ε ≤ 2 / ℓ := by
      have h := (abs_le.mp h1).2
      have : B / ℓ ^ 3 ≤ 1 / ℓ := by
        rw [div_le_div_iff₀ (by positivity) hℓ0]
        have := mul_le_mul_of_nonneg_right hBℓ hℓ0.le
        have e : ℓ ^ 2 * ℓ = 1 * ℓ ^ 3 := by ring
        linarith
      have : 1 / ℓ + 1 / ℓ = 2 / ℓ := by ring
      linarith
    have hε3 : ε ≤ 3 / 20 := by
      have : 2 / ℓ ≤ 2 / 17 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hℓ17
      linarith
    -- `N ≥ X`, so `ℓ^9 ≤ N`
    have hNX : X ≤ N := by
      have h1 : Real.log (max X 4) < ℓ := by linarith
      have h2 : max X 4 < N := by
        rw [hℓ] at h1
        exact (Real.log_lt_log_iff (by positivity) hN0).mp h1
      linarith [le_max_left X 4]
    have h9 := hX N hNX
    simp only [one_mul, add_zero] at h9
    have hℓ9 : ℓ ^ 9 ≤ N := by
      rw [div_lt_one hN0] at h9; exact h9.le
    -- `√(ℓ/N) ≤ 1/ℓ⁴`
    have hr : Real.sqrt (ℓ / N) ≤ 1 / ℓ ^ 4 := by
      rw [Real.sqrt_le_left (by positivity)]
      rw [div_pow, one_pow, ← pow_mul, div_le_div_iff₀ hN0 (by positivity)]
      have : ℓ * ℓ ^ (4 * 2) = ℓ ^ 9 := by ring
      linarith
    -- the LLT error
    have hcJ : c ∈ Icc (7 / 10 : ℝ) 1 := by
      obtain ⟨hcl3, h725⟩ := cN_ge_cM_three hm
      rw [← hceq] at hcl3
      exact ⟨by linarith, hcN.2.le⟩
    have hllt := hCl c hcJ m hm
    rw [← hN] at hllt
    have hd := hd₀le c hcJ
    have hdc : 0 < dc c := lt_of_lt_of_le hd₀ hd
    set e := |2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m - dc c| with he
    have he1 : e ≤ C' / ℓ ^ 4 := by
      refine hllt.trans ?_
      calc Cl * Real.sqrt (ℓ / N) ≤ C' * Real.sqrt (ℓ / N) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
        _ ≤ C' * (1 / ℓ ^ 4) := mul_le_mul_of_nonneg_left hr hC'0
        _ = C' / ℓ ^ 4 := by ring
    have hed : e / dc c ≤ C' / d₀ / ℓ ^ 4 := by
      rw [div_le_iff₀ hdc]
      calc e ≤ C' / ℓ ^ 4 := he1
        _ = C' / d₀ / ℓ ^ 4 * d₀ := by field_simp
        _ ≤ C' / d₀ / ℓ ^ 4 * dc c := mul_le_mul_of_nonneg_left hd (by positivity)
    have hℓ24 : ℓ ^ 2 ≤ ℓ ^ 4 := pow_le_pow_right₀ hℓ1 (by norm_num)
    have hCℓ : 2 * (C' / d₀) ≤ ℓ ^ 4 := by
      have h := Real.sq_sqrt (show 0 ≤ 2 * C' / d₀ + 1 by positivity)
      have : Real.sqrt (2 * C' / d₀ + 1) ≤ ℓ := by linarith
      have : 2 * C' / d₀ + 1 ≤ ℓ ^ 2 := by
        calc 2 * C' / d₀ + 1 = Real.sqrt (2 * C' / d₀ + 1) ^ 2 := h.symm
          _ ≤ ℓ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
      have e2 : 2 * (C' / d₀) = 2 * C' / d₀ := by ring
      linarith
    have he2 : e / dc c ≤ 1 / 2 := by
      refine hed.trans ?_
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hlr := logratio_at_crossing hc.1 hc.2 hm hcross he2
    rw [← hN, ← hℓ] at hlr
    -- `|εℓ - Θ(1-ε)| ≤ D/ℓ⁴`
    have hδ : |ε * ℓ - Theta (1 - ε)| ≤ D / ℓ ^ 4 := by
      rw [show 1 - ε = c by rw [hε]; ring]
      refine hlr.trans ?_
      have h4 : 4 / N ≤ 4 / ℓ ^ 4 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have : ℓ ^ 4 ≤ ℓ ^ 9 := pow_le_pow_right₀ hℓ1 (by norm_num)
        linarith
      rw [hD, add_div]
      have : 2 * (e / dc c) ≤ 2 * (C' / d₀) / ℓ ^ 4 := by
        rw [mul_div_assoc]; linarith
      linarith
    have hR : |Theta (1 - ε) - (Real.log 2 - ε * T + ε ^ 2 * S)| ≤ 66 * ε ^ 3 := by
      rw [hT, hS]; exact theta_taylor2 hε0 hε3
    -- `|εL - qL - Sε²| ≤ (528 + D)/ℓ³`
    have hqL : q * L = Real.log 2 := by rw [hq]; field_simp
    have h2 : |ε * L - q * L - S * ε ^ 2| ≤ (528 + D) / ℓ ^ 3 := by
      rw [hqL]
      have hε3' : 66 * ε ^ 3 ≤ 528 / ℓ ^ 3 := by
        have : ε ^ 3 ≤ (2 / ℓ) ^ 3 := pow_le_pow_left₀ hε0.le hε2 3
        rw [div_pow] at this
        have e3 : 528 / ℓ ^ 3 = 66 * (2 ^ 3 / ℓ ^ 3) := by ring
        rw [e3]; linarith
      have hD4 : D / ℓ ^ 4 ≤ D / ℓ ^ 3 :=
        div_le_div_of_nonneg_left hD0 (by positivity) (pow_le_pow_right₀ hℓ1 (by norm_num))
      have e5 : ε * L - Real.log 2 - S * ε ^ 2 = (ε * ℓ - Theta (1 - ε)) +
          (Theta (1 - ε) - (Real.log 2 - ε * T + ε ^ 2 * S)) := by
        rw [hLdef]; ring
      rw [e5]
      calc |(ε * ℓ - Theta (1 - ε)) + (Theta (1 - ε) - (Real.log 2 - ε * T + ε ^ 2 * S))|
          ≤ |ε * ℓ - Theta (1 - ε)| + |Theta (1 - ε) - (Real.log 2 - ε * T + ε ^ 2 * S)| := abs_add_le _ _
        _ ≤ D / ℓ ^ 3 + 528 / ℓ ^ 3 := add_le_add (hδ.trans hD4) (hR.trans hε3')
        _ = (528 + D) / ℓ ^ 3 := by ring
    have hA0 : (0 : ℝ) ≤ 528 + D := by linarith only [hD0]
    have halg := expansion2_algebra (A := 528 + D) (B := B) hℓ1 hL hε0 hq0 hq1 hε2 hSb hA0 hB0 h1 h2
    refine halg.trans ?_
    apply div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)

end Kagey131.PaperD.FL4
