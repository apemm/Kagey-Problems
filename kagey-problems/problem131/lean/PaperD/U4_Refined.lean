import PaperD.U4_SecondOrder
import PaperD.T6_CrossingAsymp

/-!
# Online Resource S1, part 7: the crossing to second order (Proposition S1.2, `prop:refined`)

Proposition S1.2: `x_N = g_N - (2g_N log N + g_N²/2)/(N(1 + 1/g_N)) + O(log N / N)` over even
`N`, and `x_N < g_N` for large `N`. Here `x_N = crossingX h`, `g_N = gRoot N`, `N = 2h`
(track T6), and Proposition S1.1 is `prop_second_order`.

* `star_second_order` (Step 1 of the proof, explicit): for even `N ≥ 64` with
  `400 L(1+L) ≤ N` (`L = log N`) and `1 ≤ x ≤ 4L`, `ε = x/N`,
  `|log C_N - log E_N - (G(x) - Λ_N + (2xL + x²/2)/N)| ≤ 5205 x/N`.
  (The only largeness condition is the paper's `400 L(1+L) ≤ N`.)
* `prop_refined_explicit` (Proposition S1.2 with an explicit constant): for every even `N` with
  `log N ≥ 30`, `|x_N - g_N + (2g_N L + g_N²/2)/(N(1 + 1/g_N))| ≤ 20822 L/N`.
* `prop_refined` (the `O(·)` statement as `N → ∞`).
* `crossing_lt_gRoot`: `x_N < g_N` for every even `N` with `log N ≥ 21000`. The paper says
  only "for large `N`" and (Remark S1.3) that it does not know an explicit such `N`.

All of these assume Hoeffding's inequality for sampling without replacement
(`HoeffdingHypergeomHyp`), through Proposition S1.1.
-/

namespace Kagey131.PaperD.U4

open Finset Kagey131.PaperD Filter Asymptotics

/-- Theorem 2.6(a) at `N = 2h` in the form of track T6. -/
theorem centerLowerBoundAt_U4 {h : ℕ} (hh : 1 ≤ h) : CenterLowerBoundAt h := by
  intro ε hε0 hε
  have := center_lower hh hε0 hε
  push_cast at this; exact this

/-- Theorem 2.6(b) at `N = 2h ≥ 64` in the form of track T6. -/
theorem centerUpperBoundAt_U4 {h : ℕ} (hh : 32 ≤ h) : CenterUpperBoundAt h := by
  intro ε hε0 hεN
  have := center_upper_all (h := h) (by omega) hε0 (by push_cast; exact hεN)
  push_cast at this; exact this

/-- `|log(1-y) + y + y²/2| ≤ 2y³` for `0 ≤ y ≤ 1/2`. -/
theorem log_one_sub_second {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) :
    |Real.log (1 - y) + y + y ^ 2 / 2| ≤ 2 * y ^ 3 := by
  have hy : |y| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hy 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_nonneg h0] at h
  norm_num at h
  have hden : 0 < 1 - y := by linarith
  have h3 : y ^ 3 / (1 - y) ≤ 2 * y ^ 3 := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg (pow_nonneg h0 3) (show (0 : ℝ) ≤ 1 - 2 * y by linarith)]
  have e : Real.log (1 - y) + y + y ^ 2 / 2 = y + y ^ 2 / 2 + Real.log (1 - y) := by ring
  rw [e]; exact h.trans h3

set_option maxHeartbeats 1000000 in
/-- **Proposition S1.2, Step 1 (explicit).** Assume Hoeffding's inequality for sampling without
replacement. Let `N = 2h ≥ 64`, `L = log N`, `400 L(1+L) ≤ N`, `1 ≤ x ≤ 4L` and
`ε = x/N`. Then `|log C_N - log E_N - (G(x) - Λ_N + (2xL + x²/2)/N)| ≤ 5205 x/N`. -/
theorem star_second_order (hHoef : HoeffdingHypergeomHyp) {h : ℕ} (hh : 32 ≤ h)
    (h400 : 400 * Real.log (2 * (h : ℝ)) * (1 + Real.log (2 * (h : ℝ))) ≤ 2 * (h : ℝ))
    {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 4 * Real.log (2 * (h : ℝ))) :
    |Real.log (ewBin (x / (2 * (h : ℝ))) (2 * h) h)
        - Real.log (ewBin (x / (2 * (h : ℝ))) (2 * h) (2 * h))
        - (Gfun x - LamN (2 * (h : ℝ)) +
            (2 * x * Real.log (2 * (h : ℝ)) + x ^ 2 / 2) / (2 * (h : ℝ)))| ≤
      5205 * x / (2 * (h : ℝ)) := by
  set N : ℝ := 2 * (h : ℝ) with hNdef
  set L := Real.log N with hLdef
  have hN64 : (64 : ℝ) ≤ N := by
    have : (32 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hN0 : 0 < N := by linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  set ε := x / N with hε
  have hε0 : 0 < ε := div_pos (by linarith) hN0
  have hxN : x ≤ N := by nlinarith
  have hεN : ε * (1 + L) ≤ 1 / 100 := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ hN0]; nlinarith
  have hε1 : ε ≤ 1 / 100 := by nlinarith
  -- Proposition S1.1 at `N`
  have hS := (prop_second_order hHoef (N := 2 * h) ⟨h, by ring⟩ (by omega) hε0
    (by push_cast; exact hεN)).2
  rw [show 2 * h / 2 = h by omega] at hS
  push_cast at hS
  rw [← hNdef, ← hLdef] at hS
  -- `log(4ε/(N+2)) = log 4 + log x - 2L - log(1 + 2/N)`
  have hx0 : 0 < x := by linarith
  have hlog4 : Real.log (4 * ε / (N + 2)) =
      Real.log 4 + Real.log x - 2 * L - Real.log (1 + 2 / N) := by
    have e : 4 * ε / (N + 2) = 4 * x / (N * N * (1 + 2 / N)) := by
      rw [hε]; field_simp
    rw [e, Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hx0.ne',
      Real.log_mul (by positivity) (by positivity), Real.log_mul hN0.ne' hN0.ne']
    ring
  have h2N0 : 0 ≤ 2 / N := by positivity
  have hl2N0 : 0 ≤ Real.log (1 + 2 / N) := Real.log_nonneg (by linarith)
  have hl2N1 : Real.log (1 + 2 / N) ≤ 2 / N := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 2 / N by positivity); linarith
  -- the end `E_N = (1-ε)^{N-1}/2`
  obtain ⟨n, hn⟩ : ∃ n, 2 * h = n + 1 := ⟨2 * h - 1, by omega⟩
  have hnN : (n : ℝ) = N - 1 := by
    have : ((2 * h : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by rw [hn]
    push_cast at this; rw [hNdef]; linarith
  have hE : Real.log (ewBin ε (2 * h) (2 * h)) = (N - 1) * Real.log (1 - ε) - Real.log 2 := by
    rw [hn, ewBin_top, Real.log_div (pow_pos (by linarith) _).ne' (by norm_num), Real.log_pow, hnN]
  have hr := log_one_sub_second hε0.le (by linarith)
  set r := Real.log (1 - ε) + ε + ε ^ 2 / 2 with hrdef
  have hl8 : Real.log 8 = Real.log 4 + Real.log 2 := log_eight_eq
  -- the identity for the error
  have hid : Real.log (ewBin ε (2 * h) h) - Real.log (ewBin ε (2 * h) (2 * h)) -
      (Gfun x - LamN N + (2 * x * L + x ^ 2 / 2) / N) =
      (Real.log (ewBin ε (2 * h) h) - Real.log (4 * ε / (N + 2)) - 2 * ε * L) -
        Real.log (1 + 2 / N) - ε - ε ^ 2 / 2 - (N - 1) * r := by
    rw [hE, hlog4, hrdef]
    unfold Gfun LamN
    rw [← hLdef, hl8, hε]
    field_simp
    ring
  rw [hid]
  have hA := abs_le.mp hS
  have hr' := abs_le.mp hr
  -- `(N-1)|r| ≤ 2Nε³ = 2x³/N² ≤ x/N`
  have hNr : |(N - 1) * r| ≤ x / N := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ N - 1)]
    have h1 : (N - 1) * |r| ≤ N * (2 * ε ^ 3) :=
      mul_le_mul (by linarith) hr (abs_nonneg _) hN0.le
    have h2 : N * (2 * ε ^ 3) ≤ x / N := by
      rw [hε]
      have hx16 : x ^ 2 ≤ 16 * L ^ 2 := by nlinarith
      rw [show N * (2 * (x / N) ^ 3) = 2 * x * x ^ 2 / N ^ 2 by field_simp, div_le_div_iff₀
        (by positivity) hN0]
      have h2x : 2 * x ^ 2 ≤ N := by linarith
      nlinarith [mul_nonneg (mul_nonneg hx0.le hN0.le) (sub_nonneg.mpr h2x)]
    linarith
  have hNr' := abs_le.mp hNr
  have hεx : ε = x / N := hε
  have hε2 : ε ^ 2 / 2 ≤ ε := by
    have := mul_le_mul_of_nonneg_left hε1 hε0.le
    rw [sq]; linarith
  have h2N : 2 / N ≤ 2 * x / N := by
    rw [div_le_div_iff_of_pos_right hN0]; linarith
  rw [abs_le]
  have e1 : 5205 * x / N = 5200 * ε + 2 * x / N + ε + ε + x / N := by rw [hε]; ring
  rw [e1]
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hN1, hN2⟩ := hNr'
  have := sq_nonneg ε
  constructor <;> linarith

set_option maxHeartbeats 1000000 in
/-- **Proposition S1.2 (`prop:refined`), explicit form.** Assume Hoeffding's inequality for
sampling without replacement. For every even `N = 2h` with `L = log N ≥ 30`,
`|x_N - g_N + (2g_N L + g_N²/2)/(N(1 + 1/g_N))| ≤ 20822 L/N`. -/
theorem prop_refined_explicit (hHoef : HoeffdingHypergeomHyp) {h : ℕ}
    (hL : 30 ≤ Real.log (2 * (h : ℝ))) :
    |crossingX h - gRoot (2 * (h : ℝ)) +
        (2 * gRoot (2 * (h : ℝ)) * Real.log (2 * (h : ℝ)) + gRoot (2 * (h : ℝ)) ^ 2 / 2) /
          (2 * (h : ℝ) * (1 + 1 / gRoot (2 * (h : ℝ))))| ≤
      20822 * Real.log (2 * (h : ℝ)) / (2 * (h : ℝ)) := by
  have hh := one_le_of_L30 hL
  have hh32 := ge32_of_L30 hL
  have hN0 : (0 : ℝ) < 2 * (h : ℝ) := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  obtain ⟨hρ, hd, -, -⟩ := crossing_explicit hL (centerLowerBoundAt_U4 hh) (centerUpperBoundAt_U4 hh32)
  obtain ⟨h400, -, -⟩ := consequences_L30 hN0 hL
  have hbig := big_of_L30 hN0 hL
  set N : ℝ := 2 * (h : ℝ) with hNdef
  set L := Real.log N with hLdef
  set ρ := rhoN N with hρdef
  have hL0 : 0 < L := by linarith
  have h32 : 32 * L ^ 2 ≤ N := by
    have hL2 : 900 ≤ L ^ 2 := by nlinarith
    have : 32 * L ^ 2 ≤ 26 * L ^ 4 := by nlinarith [mul_le_mul_of_nonneg_left hL2 (sq_nonneg L)]
    nlinarith [pow_nonneg hL0.le 3]
  -- the root `g`
  have hl8 : Real.log 8 = 3 * Real.log 2 := log_eight_eq'
  have hl2 := log_two_bounds
  have hΛL : LamN N = 2 * L - Real.log 8 := rfl
  have hΛ1 : 1 ≤ LamN N := by rw [hΛL]; linarith
  obtain ⟨g1, g2, g3⟩ := gRoot_spec hΛ1
  set g := gRoot N with hgdef
  set Λ := LamN N with hΛdef
  have hlΛ := log_le_half (show 0 < Λ by linarith)
  have hgL : L / 2 ≤ g := by rw [hΛL] at g1 hlΛ; linarith
  have hg2L : g ≤ 2 * L := by rw [hΛL] at g2; linarith
  have hg0 : 0 < g := by linarith
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; unfold rhoN; rw [← hLdef]; positivity
  have hρs : ρ ≤ 1 / 900 := by
    have : (1 : ℝ) / L ^ 2 ≤ 1 / 900 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  -- the crossing `x`
  set x := crossingX h with hxdef
  set d := x - g with hddef
  have hdab := abs_le.mp hd
  have hx1 : 1 ≤ x := by linarith
  have hx4 : x ≤ 4 * L := by linarith
  have hx0 : 0 < x := by linarith
  -- `F(x) = 0`
  have hdiv := crossingX_div hh
  have hF0 : Real.log (ewBin (x / N) (2 * h) h) - Real.log (ewBin (x / N) (2 * h) (2 * h)) = 0 := by
    rw [hxdef, hdiv, (crossingEps_spec hh).2.1, sub_self]
  have hstar := star_second_order hHoef hh32 h400 hx1 hx4
  rw [← hNdef, ← hLdef, hF0, zero_sub, abs_neg] at hstar
  -- `G(x) - Λ = d + log x - log g`
  have hG : Gfun x - Λ = d + (Real.log x - Real.log g) := by
    rw [← g3]; unfold Gfun; rw [hddef]; ring
  -- `|log x - log g - d/g| ≤ d²/g²`
  have hy : |d / g| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hg0, div_le_iff₀ hg0]
    have : |d| ≤ ρ := hd
    nlinarith
  have hlogxg : Real.log x - Real.log g = Real.log (1 + d / g) := by
    rw [← Real.log_div hx0.ne' hg0.ne']; congr 1; rw [hddef]; field_simp; ring
  have hlog_lo := log_one_add_ge (y := d / g) (by linarith [(abs_le.mp hy).1])
  have hlog_hi : Real.log (1 + d / g) ≤ d / g := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + d / g by linarith [(abs_le.mp hy).1])
    linarith
  -- `η₀(x) - η₀(g)`
  have heta : (2 * x * L + x ^ 2 / 2) / N - (2 * g * L + g ^ 2 / 2) / N =
      d * (2 * L + (x + g) / 2) / N := by rw [hddef]; field_simp; ring
  have heta_b : |d * (2 * L + (x + g) / 2) / N| ≤ 5 * L * ρ / N := by
    rw [abs_div, abs_of_pos hN0, abs_mul, abs_of_pos (by linarith : 0 < 2 * L + (x + g) / 2)]
    apply div_le_div_of_nonneg_right _ hN0.le
    have hc : 2 * L + (x + g) / 2 ≤ 5 * L := by linarith
    calc |d| * (2 * L + (x + g) / 2) ≤ ρ * (5 * L) := mul_le_mul hd hc (by linarith) hρ0
      _ = 5 * L * ρ := by ring
  -- collect: `d (1 + 1/g) + η₀(g) = E''`
  set η := (2 * g * L + g ^ 2 / 2) / N with hη
  have hsa := abs_le.mp hstar
  have hkey : |d * (1 + 1 / g) + η| ≤
      5205 * x / N + 5 * L * ρ / N + (d / g) ^ 2 := by
    have hb := abs_le.mp heta_b
    have e : d * (1 + 1 / g) + η =
        (Gfun x - Λ + (2 * x * L + x ^ 2 / 2) / N) - (Real.log (1 + d / g) - d / g) -
          d * (2 * L + (x + g) / 2) / N := by
      rw [hG, hlogxg, ← heta, hη]; field_simp; ring
    have hB1 : -(d / g) ^ 2 ≤ Real.log (1 + d / g) - d / g := by linarith
    have hB2 : Real.log (1 + d / g) - d / g ≤ 0 := by linarith
    have hsq0 : 0 ≤ (d / g) ^ 2 := sq_nonneg _
    rw [e, abs_le]
    constructor <;> linarith
  -- the small terms
  have hsq : (d / g) ^ 2 ≤ L / N := by
    have h1 : (d / g) ^ 2 ≤ ρ ^ 2 / (L / 2) ^ 2 := by
      rw [div_pow]
      have hd2 : d ^ 2 ≤ ρ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg d) hd 2
      have hg2 : (L / 2) ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ (by positivity) hgL 2
      exact div_le_div₀ (sq_nonneg ρ) hd2 (by positivity) hg2
    have h2 : ρ ^ 2 / (L / 2) ^ 2 ≤ L / N := by
      rw [hρdef]; unfold rhoN; rw [← hLdef]
      rw [div_pow, div_div, div_le_div_iff₀ (by positivity) hN0]
      have hL4 : 0 ≤ L ^ 4 := by positivity
      have hb3 : 20802 * L ^ 3 ≤ N := by linarith
      have hL2 : 900 ≤ L ^ 2 := by nlinarith
      have hN' : 2062096 * L ≤ N := by
        have : 2062096 * L ≤ 20802 * L ^ 3 := by
          have e : 20802 * L ^ 3 = 20802 * L ^ 2 * L := by ring
          rw [e]; apply mul_le_mul_of_nonneg_right _ hL0.le; linarith
        linarith
      have hc0 : 24 * L + 20800 ≤ 718 * L := by linarith
      have hc : (24 * L + 20800) ^ 2 ≤ (718 * L) ^ 2 := pow_le_pow_left₀ (by positivity) hc0 2
      have e : (24 * L ^ 2 + 20800 * L) ^ 2 * N = L ^ 2 * N * (24 * L + 20800) ^ 2 := by ring
      have e2 : L * (N ^ 2 * (L / 2) ^ 2) = L ^ 2 * N * (L * N / 4) := by ring
      rw [e, e2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : (718 * L) ^ 2 ≤ L * N / 4 := by
        have e3 : (718 * L) ^ 2 = 515524 * L * L := by ring
        rw [e3]
        have := mul_le_mul_of_nonneg_left hN' hL0.le
        nlinarith
      linarith
    linarith
  have hsmall : 5 * L * ρ / N ≤ L / N := by
    apply div_le_div_of_nonneg_right _ hN0.le; nlinarith
  have hxL : 5205 * x / N ≤ 20820 * L / N := by
    apply div_le_div_of_nonneg_right _ hN0.le; linarith
  -- divide by `1 + 1/g ≥ 1`
  have hgg : 1 ≤ 1 + 1 / g := by have : 0 < 1 / g := by positivity
                                 linarith
  have hfin : |d + η / (1 + 1 / g)| ≤ |d * (1 + 1 / g) + η| := by
    have e : d + η / (1 + 1 / g) = (d * (1 + 1 / g) + η) / (1 + 1 / g) := by
      field_simp
    rw [e, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + 1 / g)]
    exact div_le_self (abs_nonneg _) hgg
  have hgoal : crossingX h - g + (2 * g * L + g ^ 2 / 2) / (N * (1 + 1 / g)) = d + η / (1 + 1 / g) := by
    rw [hη, hddef, div_div]
  rw [hgoal]
  have e : 20822 * L / N = 20820 * L / N + L / N + L / N := by ring
  rw [e]
  linarith

/-- **Proposition S1.2 (`prop:refined`).** Assume Hoeffding's inequality for sampling without
replacement. As `N = 2h → ∞`,
`x_N = g_N - (2g_N log N + g_N²/2)/(N(1 + 1/g_N)) + O(log N/N)`. -/
theorem prop_refined (hHoef : HoeffdingHypergeomHyp) :
    (fun h : ℕ => crossingX h - (gRoot (2 * (h : ℝ)) -
        (2 * gRoot (2 * (h : ℝ)) * Real.log (2 * (h : ℝ)) + gRoot (2 * (h : ℝ)) ^ 2 / 2) /
          (2 * (h : ℝ) * (1 + 1 / gRoot (2 * (h : ℝ)))))) =O[atTop]
      (fun h : ℕ => Real.log (2 * (h : ℝ)) / (2 * (h : ℝ))) := by
  refine IsBigO.of_bound 20822 ?_
  filter_upwards [eventually_L30] with h hL
  have hh := one_le_of_L30 hL
  have hN0 : (0 : ℝ) < 2 * (h : ℝ) := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hL0 : 0 < Real.log (2 * (h : ℝ)) := by linarith
  rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ Real.log (2 * (h : ℝ)) / (2 * (h : ℝ)) by positivity),
    Real.norm_eq_abs, mul_div_assoc', sub_sub_eq_add_sub, add_sub_right_comm]
  exact prop_refined_explicit hHoef hL

/-- **Proposition S1.2, last claim, with an explicit threshold.** Assume Hoeffding's inequality
for sampling without replacement. For every even `N = 2h` with `log N ≥ 21000`, `x_N < g_N`. -/
theorem crossing_lt_gRoot (hHoef : HoeffdingHypergeomHyp) {h : ℕ}
    (hL : 21000 ≤ Real.log (2 * (h : ℝ))) : crossingX h < gRoot (2 * (h : ℝ)) := by
  have hL30 : 30 ≤ Real.log (2 * (h : ℝ)) := by linarith
  have hx := abs_le.mp (prop_refined_explicit hHoef hL30)
  have hh := one_le_of_L30 hL30
  have hN0 : (0 : ℝ) < 2 * (h : ℝ) := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  set N : ℝ := 2 * (h : ℝ) with hNdef
  set L := Real.log N with hLdef
  have hl8 : Real.log 8 = 3 * Real.log 2 := log_eight_eq'
  have hl2 := log_two_bounds
  have hΛL : LamN N = 2 * L - Real.log 8 := rfl
  have hΛ1 : 1 ≤ LamN N := by rw [hΛL]; linarith
  obtain ⟨g1, g2, g3⟩ := gRoot_spec hΛ1
  set g := gRoot N
  have hlΛ := log_le_half (show 0 < LamN N by linarith)
  have hgL : L / 2 ≤ g := by rw [hΛL] at g1 hlΛ; linarith
  have hg0 : 0 < g := by linarith
  -- the main term exceeds the error
  have hM : 20822 * L / N < (2 * g * L + g ^ 2 / 2) / (N * (1 + 1 / g)) := by
    have hgg : 1 + 1 / g ≤ 1 + 2 / L := by
      have : 1 / g ≤ 2 / L := by
        rw [div_le_div_iff₀ hg0 (by linarith)]; linarith
      linarith
    have hL0 : 0 < L := by linarith
    rw [div_lt_div_iff₀ hN0 (by positivity)]
    have h1 : L ^ 2 ≤ 2 * g * L + g ^ 2 / 2 := by nlinarith [sq_nonneg g]
    have h2 : 20822 * L * (N * (1 + 1 / g)) ≤ 20822 * L * (N * (1 + 2 / L)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hgg hN0.le
    have h3 : 20822 * L * (N * (1 + 2 / L)) = N * (20822 * L + 41644) := by
      field_simp; ring
    have h5 : 20822 * L + 41644 < L ^ 2 := by nlinarith
    have h4 : N * (20822 * L + 41644) < L ^ 2 * N := by nlinarith [mul_lt_mul_of_pos_left h5 hN0]
    nlinarith
  linarith

end Kagey131.PaperD.U4
