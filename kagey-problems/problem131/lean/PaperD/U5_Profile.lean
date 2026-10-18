import PaperD.U5_LocalUpperMain
import PaperD.T4_Main

/-!
# Paper D, Online Resource 1, Theorem S2.1 (`thm:profile`): the tail

**Theorem S2.1.** Let `N` be even, and let `x = Nε ≥ 1` depend on `N` with `x log²N/N → 0`.
Let `ω_N → ∞` with `ω_N x log²(x+1) = o(N)`, and let `δ'_N → 0`. Then
`f_N(m) = x/(m(m+1))(1 + o(1))` and `P_N(N-m) = x/(2m²)(1 + o(1))`, uniformly for
`ω_N x log²(x+1) ≤ m ≤ δ'_N N`.

Lean:
* `profile_f_bounds`: the two-sided bound `x/(m(m+1))(1 - e₁(m)) ≤ f_N(m) ≤ x/(m(m+1))(1 + C√Δ(m))`
  (Propositions B.4 and S2.4), for any `N`;
* `profile_mirror`: `0 ≤ f_N(N-m) ≤ C_N ≤ (4ε/(N+2)) N^{2ε} e^{5200ε}` for even `N` (Step 3 of
  the proof: Lemma B.5, Lemma 3.4 and Theorem 2.6(b));
* `thm_profile_uniform`: **Theorem S2.1** in uniform form: for every `η > 0` there are `W` and
  `δ > 0` such that for every even `N ≥ 64`, `ε > 0` with `x = Nε ≥ 1` and `x log²N/N ≤ δ`, and
  every `m` with `W x log²(x+1) ≤ m ≤ δ N`:
  `|f_N(m) m(m+1)/x - 1| ≤ η` and `|P_N(N-m) 2m²/x - 1| ≤ η`;
* `thm_profile`: the paper's statement with sequences `ε_N`, `ω_N → ∞`, `δ'_N → 0`
  (`N = 2h`); the hypothesis `ω_N x log²(x+1) = o(N)` is not needed.
-/

namespace Kagey131.PaperD

open Finset RRT Filter Topology

/-- **Propositions B.4 and S2.4 together.** For `N ≥ 64`, `0 ≤ ε`, `x ≥ 1`, `ε log N ≤ 1/40`,
`34000 x log²(x+1) ≤ m` and `8m ≤ N`. -/
theorem profile_f_bounds {ε : ℝ} (h0 : 0 ≤ ε) {N m : ℕ} (hN : 64 ≤ N) (hx : 1 ≤ (N : ℝ) * ε)
    (hεN : ε * Real.log N ≤ 1 / 40)
    (hA : 34000 * ((N : ℝ) * ε) * Real.log ((N : ℝ) * ε + 1) ^ 2 ≤ m) (h8m : 8 * m ≤ N) :
    (N : ℝ) * ε / ((m : ℝ) * ((m : ℝ) + 1)) *
        (1 - 20 * ((N : ℝ) * ε * Real.log ((m : ℝ) + 1) / m + ε * Real.log N +
          m * Real.exp (-((m : ℝ) / 9)))) ≤ law ε N m ∧
      law ε N m ≤ (N : ℝ) * ε / ((m : ℝ) * ((m : ℝ) + 1)) *
        (1 + 20000 * Real.sqrt ((N : ℝ) * ε * Real.log m ^ 2 / m + ε * Real.log N + (m : ℝ) / N)) := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 4 ≤ Real.log N := four_le_log_64.trans (Real.log_le_log (by norm_num) hNr)
  have hε1 : ε ≤ 1 := by nlinarith
  obtain ⟨hL1, hL2⟩ := logx1_bounds hx
  have hm16 : (16200 : ℝ) ≤ m := by nlinarith
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  exact ⟨thm_B_local_lower h0 hε1 hN hm2 (by omega), thm_B_local_upper h0 hN hx hεN hA h8m⟩

/-- **Step 3 of the proof of Theorem S2.1: the mirror term.** For even `N = 2h ≥ 64`, `ε > 0`,
`x ≥ 1`, `ε(1 + log N) ≤ 1/100`, `34000 x log²(x+1) ≤ m` and `8m ≤ N`:
`0 ≤ f_N(N - m) ≤ C_N ≤ (4ε/(N+2)) N^{2ε} e^{5200 ε}`. -/
theorem profile_mirror {ε : ℝ} (h0 : 0 < ε) {h m : ℕ} (hN : 64 ≤ 2 * h) (hx : 1 ≤ ((2 * h : ℕ) : ℝ) * ε)
    (hε : ε * (1 + Real.log ((2 * h : ℕ) : ℝ)) ≤ 1 / 100)
    (hA : 34000 * (((2 * h : ℕ) : ℝ) * ε) * Real.log (((2 * h : ℕ) : ℝ) * ε + 1) ^ 2 ≤ m)
    (h8m : 8 * m ≤ 2 * h) :
    0 ≤ law ε (2 * h) (2 * h - m) ∧
      law ε (2 * h) (2 * h - m) ≤
        4 * ε / (((2 * h : ℕ) : ℝ) + 2) * (((2 * h : ℕ) : ℝ)) ^ (2 * ε) * Real.exp (5200 * ε) := by
  have hNr : (64 : ℝ) ≤ ((2 * h : ℕ) : ℝ) := by exact_mod_cast hN
  have hlogN : 4 ≤ Real.log ((2 * h : ℕ) : ℝ) :=
    four_le_log_64.trans (Real.log_le_log (by norm_num) hNr)
  have hε1 : ε < 1 := by nlinarith
  have hεN : ε * Real.log ((2 * h : ℕ) : ℝ) ≤ 1 / 40 := by nlinarith
  refine ⟨law_nonneg h0.le hε1.le _ _, ?_⟩
  have hmode := upper_aux_mode h0.le hN hx hεN hA h8m
  have hmode' : modeH ε (2 * h) ≤ h := by
    have : (modeH ε (2 * h) : ℝ) ≤ h := by
      have : (m : ℝ) / 2 ≤ h := by
        have : ((8 * m : ℕ) : ℝ) ≤ ((2 * h : ℕ) : ℝ) := by exact_mod_cast h8m
        push_cast at this; linarith
      linarith
    exact_mod_cast this
  have hanti := law_anti_above_modeH h0.le hε1 (N := 2 * h) (by omega) hmode'
    (show h ≤ 2 * h - m by omega) (by omega)
  have hC : law ε (2 * h) h = ewBin ε (2 * h) ((2 * h) / 2) := by
    rw [show (2 * h) / 2 = h by omega, ewBin_center ε (by omega)]
  have hB := thm_erw_bounds_b (N := 2 * h) (ε := ε) ⟨h, by ring⟩ hN h0 hε
  linarith

/-- `P_N(N - m) = (f_N(m) + f_N(N - m))/2`. -/
theorem profile_P_eq (ε : ℝ) {N m : ℕ} (hN : 1 ≤ N) (hm : m ≤ N) :
    ewBin ε N (N - m) = (law ε N m + law ε N (N - m)) / 2 := by
  rw [ewBin_eq ε hN (by omega), show N - (N - m) = m by omega]

/-- `x log²m/m ≤ 2 log²W/(0.48 W) + 18/W` for `m ≥ W x log²(x+1)`, `W ≥ 34000`, `x ≥ 1`. -/
theorem profile_gW {x W m : ℝ} (hx : 1 ≤ x) (hW : 34000 ≤ W)
    (hm : W * x * Real.log (x + 1) ^ 2 ≤ m) :
    x * Real.log m ^ 2 / m ≤ 2 * Real.log W ^ 2 / (0.48 * W) + 18 / W := by
  set L := Real.log (x + 1) with hL
  obtain ⟨hL1, hL2⟩ := logx1_bounds hx
  rw [← hL] at hL1 hL2
  have hx0 : 0 < x := by linarith
  have hW0 : 0 < W := by linarith
  set M : ℝ := W * x * L ^ 2 with hM
  have hxL : 0.48 ≤ x * L ^ 2 := by nlinarith
  have hMge : 0.48 * W ≤ M := by rw [hM]; nlinarith
  have hM0 : 0 < M := by nlinarith
  have hlogM : 2 ≤ Real.log M := by
    rw [Real.le_log_iff_exp_le hM0]
    have he := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have : Real.exp 1 ^ 2 ≤ (2.72 : ℝ) ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 2
    nlinarith
  have hmono := logsq_div_anti hM0 hlogM hm
  have hl : Real.log M ≤ Real.log W + 3 * L := by
    rw [hM, Real.log_mul (by positivity) (by positivity), Real.log_mul hW0.ne' hx0.ne', Real.log_pow]
    have h2 : Real.log x ≤ L := Real.log_le_log hx0 (by linarith)
    have h3 : Real.log L ≤ L := Real.log_le_self (by linarith)
    push_cast
    linarith
  have hl0 : 0 ≤ Real.log M := by linarith
  have hsq : Real.log M ^ 2 ≤ 2 * Real.log W ^ 2 + 18 * L ^ 2 := by
    have h := mul_le_mul hl hl hl0 (by linarith)
    nlinarith [sq_nonneg (Real.log W - 3 * L)]
  have hval : x * (Real.log M ^ 2 / M) ≤ 2 * Real.log W ^ 2 / (0.48 * W) + 18 / W := by
    have e : x * (Real.log M ^ 2 / M) = Real.log M ^ 2 / (W * L ^ 2) := by
      rw [hM]; field_simp
    rw [e]
    have hWL : 0 < W * L ^ 2 := by positivity
    calc Real.log M ^ 2 / (W * L ^ 2) ≤ (2 * Real.log W ^ 2 + 18 * L ^ 2) / (W * L ^ 2) :=
          div_le_div_of_nonneg_right hsq hWL.le
      _ = 2 * Real.log W ^ 2 / (W * L ^ 2) + 18 / W := by field_simp
      _ ≤ 2 * Real.log W ^ 2 / (0.48 * W) + 18 / W := by
          have : 2 * Real.log W ^ 2 / (W * L ^ 2) ≤ 2 * Real.log W ^ 2 / (0.48 * W) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
          linarith
  have e : x * Real.log m ^ 2 / m = x * (Real.log m ^ 2 / m) := by ring
  rw [e]
  exact (mul_le_mul_of_nonneg_left hmono hx0.le).trans hval

/-- The function `W ↦ 2 log²W/(0.48 W) + 18/W` tends to `0`. -/
theorem tendsto_gW : Tendsto (fun W : ℝ => 2 * Real.log W ^ 2 / (0.48 * W) + 18 / W) atTop (𝓝 0) := by
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 0.48 0 2 (by norm_num)
  have h2 : Tendsto (fun W : ℝ => 18 / W) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h3 : Tendsto (fun W : ℝ => 2 * (Real.log W ^ 2 / (0.48 * W + 0))) atTop (𝓝 (2 * 0)) :=
    h1.const_mul 2
  simp only [add_zero, mul_zero] at h3
  have := h3.add h2
  simp only [add_zero] at this
  refine this.congr (fun W => ?_)
  ring

/-- **Theorem S2.1 (`thm:profile`), uniform form.** For every `η > 0` there are `W` and `δ > 0`
such that for every even `N = 2h ≥ 64`, every `ε > 0` with `x = Nε ≥ 1` and `x log²N/N ≤ δ`,
and every `m` with `W x log²(x+1) ≤ m ≤ δN`:
`|f_N(m) m(m+1)/x - 1| ≤ η` and `|P_N(N-m) 2m²/x - 1| ≤ η`. -/
theorem thm_profile_uniform {η : ℝ} (hη : 0 < η) :
    ∃ W δ : ℝ, 0 < δ ∧ ∀ (h m : ℕ) (ε : ℝ), 64 ≤ 2 * h → 0 < ε → 1 ≤ ((2 * h : ℕ) : ℝ) * ε →
      ((2 * h : ℕ) : ℝ) * ε * Real.log ((2 * h : ℕ) : ℝ) ^ 2 / ((2 * h : ℕ) : ℝ) ≤ δ →
      W * (((2 * h : ℕ) : ℝ) * ε) * Real.log (((2 * h : ℕ) : ℝ) * ε + 1) ^ 2 ≤ m →
      (m : ℝ) ≤ δ * ((2 * h : ℕ) : ℝ) →
      |law ε (2 * h) m * ((m : ℝ) * ((m : ℝ) + 1)) / (((2 * h : ℕ) : ℝ) * ε) - 1| ≤ η ∧
        |ewBin ε (2 * h) (2 * h - m) * (2 * (m : ℝ) ^ 2) / (((2 * h : ℕ) : ℝ) * ε) - 1| ≤ η := by
  set τ : ℝ := min η 1 / 4 with hτ
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  have hτ1 : τ ≤ 1 / 4 := by rw [hτ]; have := min_le_right η 1; linarith
  have hτη : 4 * τ ≤ η := by rw [hτ]; have := min_le_left η 1; linarith
  set c : ℝ := (τ / 20000) ^ 2 / 2 with hc
  have hc0 : 0 < c := by positivity
  have hcτ : c ≤ τ / 60 := by
    rw [hc]
    have : (τ / 20000) ^ 2 ≤ τ / 20000 := by
      rw [sq]; exact mul_le_of_le_one_left (by positivity) (by linarith)
    linarith
  -- the choice of `W`
  have hev : ∀ᶠ W : ℝ in atTop, 34000 ≤ W ∧
      2 * Real.log W ^ 2 / (0.48 * W) + 18 / W ≤ min c (τ / 120) ∧ 1 / W ≤ τ / 30000 := by
    refine (eventually_ge_atTop 34000).and ((tendsto_gW.eventually (ge_mem_nhds (by positivity))).and ?_)
    exact (tendsto_const_nhds.div_atTop tendsto_id).eventually (ge_mem_nhds (by positivity))
  obtain ⟨W, hW1, hW2, hW3⟩ := hev.exists
  set δ : ℝ := min (c / 2) (min (τ / 60) (1 / 6000)) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδc : δ ≤ c / 2 := min_le_left _ _
  have hδτ : δ ≤ τ / 60 := (min_le_right _ _).trans (min_le_left _ _)
  have hδs : δ ≤ 1 / 6000 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨W, δ, hδ0, ?_⟩
  intro h m ε hN hε0 hx hlim hWm hmδ
  set N : ℝ := ((2 * h : ℕ) : ℝ) with hNdef
  set x : ℝ := N * ε with hxdef
  have hNr : (64 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < x := by linarith
  have hlogN : 4 ≤ Real.log N := four_le_log_64.trans (Real.log_le_log (by norm_num) hNr)
  have hεx : ε = x / N := by rw [hxdef]; field_simp
  have hlogN2 : 1 ≤ Real.log N ^ 2 := one_le_pow₀ (by linarith)
  have hlogNle : Real.log N ≤ Real.log N ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  -- consequences of `x log²N/N ≤ δ`
  have hεδ : ε ≤ δ := by
    have : ε ≤ x * Real.log N ^ 2 / N := by
      rw [hεx]; apply div_le_div_of_nonneg_right _ hN0.le
      exact le_mul_of_one_le_right hx0.le hlogN2
    linarith
  have hεlogδ : ε * Real.log N ≤ δ := by
    have : ε * Real.log N ≤ x * Real.log N ^ 2 / N := by
      rw [hεx, div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ hN0.le
      exact mul_le_mul_of_nonneg_left hlogNle hx0.le
    linarith
  have hε100 : ε * (1 + Real.log N) ≤ 1 / 100 := by
    have e : ε * (1 + Real.log N) = ε + ε * Real.log N := by ring
    linarith
  have hεN40 : ε * Real.log N ≤ 1 / 40 := by linarith
  obtain ⟨hL1, hL2⟩ := logx1_bounds (x := x) hx
  have hxL : 0.48 ≤ x * Real.log (x + 1) ^ 2 := by
    calc (0.48 : ℝ) ≤ 1 * Real.log (x + 1) ^ 2 := by linarith
      _ ≤ x * Real.log (x + 1) ^ 2 := mul_le_mul_of_nonneg_right hx (sq_nonneg _)
  have hxL0 : 0 ≤ x * Real.log (x + 1) ^ 2 := by linarith
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have hWm' : W * (x * Real.log (x + 1) ^ 2) ≤ m := by
    have e : W * (x * Real.log (x + 1) ^ 2) = W * x * Real.log (x + 1) ^ 2 := by ring
    rw [e]; exact hWm
  have hA : 34000 * x * Real.log (x + 1) ^ 2 ≤ m := by
    have h1 : 34000 * (x * Real.log (x + 1) ^ 2) ≤ W * (x * Real.log (x + 1) ^ 2) :=
      mul_le_mul_of_nonneg_right hW1 hxL0
    have e : 34000 * x * Real.log (x + 1) ^ 2 = 34000 * (x * Real.log (x + 1) ^ 2) := by ring
    linarith
  have hmW : 0.48 * W ≤ m := by
    have h1 : W * 0.48 ≤ W * (x * Real.log (x + 1) ^ 2) := mul_le_mul_of_nonneg_left hxL hW0
    linarith
  have hm16 : (16320 : ℝ) ≤ m := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have h8m : 8 * m ≤ 2 * h := by
    have h1 : δ * N ≤ (1 / 6000) * N := mul_le_mul_of_nonneg_right hδs hN0.le
    have : 8 * (m : ℝ) ≤ N := by linarith
    rw [hNdef] at this; exact_mod_cast this
  have hmN : m ≤ 2 * h := by omega
  -- the two-sided bound for `f_N(m)`
  obtain ⟨hlow, hup⟩ := profile_f_bounds hε0.le (N := 2 * h) (m := m) hN hx hεN40 hA h8m
  have hgW := profile_gW hx hW1 (show W * x * Real.log (x + 1) ^ 2 ≤ m from hWm)
  set gW := 2 * Real.log W ^ 2 / (0.48 * W) + 18 / W with hgWdef
  have hgc : gW ≤ c := hW2.trans (min_le_left _ _)
  have hgτ : gW ≤ τ / 120 := hW2.trans (min_le_right _ _)
  have hlogm : 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le hm0]; have := Real.exp_one_lt_d9; linarith
  have hinvm : 1 / (m : ℝ) ≤ τ / 14000 := by
    have h1 : 1 / (m : ℝ) ≤ 1 / (0.48 * W) := one_div_le_one_div_of_le (by positivity) hmW
    have h2 : 1 / (0.48 * W) ≤ 2.1 * (1 / W) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    linarith
  -- the lower error
  have hElow : 20 * (x * Real.log ((m : ℝ) + 1) / m + ε * Real.log N + m * Real.exp (-((m : ℝ) / 9))) ≤ τ := by
    have hlm2 : Real.log m ≤ Real.log m ^ 2 := le_self_pow₀ hlogm (by norm_num)
    have h1 : x * Real.log ((m : ℝ) + 1) / m ≤ 2 * (x * Real.log m ^ 2 / m) := by
      have hl : Real.log ((m : ℝ) + 1) ≤ 2 * Real.log m ^ 2 := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((m : ℝ) + 1) / m by positivity)
        rw [Real.log_div (by positivity) hm0.ne'] at h
        have : ((m : ℝ) + 1) / m - 1 ≤ 1 := by
          rw [div_sub_one hm0.ne', div_le_one hm0]; linarith
        linarith
      have e : 2 * (x * Real.log m ^ 2 / m) = x * (2 * Real.log m ^ 2) / m := by ring
      rw [e]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl hx0.le) hm0.le
    have h2 : (m : ℝ) * Real.exp (-((m : ℝ) / 9)) ≤ 162 / m := by
      have := exp_neg_le_two_div_sq (y := (m : ℝ) / 9) (by positivity)
      have e : (162 : ℝ) / m = (m : ℝ) * (2 / ((m : ℝ) / 9) ^ 2) := by field_simp; ring
      rw [e]; exact mul_le_mul_of_nonneg_left this hm0.le
    have h3 : (162 : ℝ) / m ≤ 162 * (τ / 14000) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinvm (by norm_num)
    linarith
  -- the upper error
  have hΔ : x * Real.log m ^ 2 / m + ε * Real.log N + (m : ℝ) / N ≤ (τ / 20000) ^ 2 := by
    have : (m : ℝ) / N ≤ δ := by rw [div_le_iff₀ hN0]; exact hmδ
    have hc' : c = (τ / 20000) ^ 2 / 2 := hc
    linarith
  have hEup : 20000 * Real.sqrt (x * Real.log m ^ 2 / m + ε * Real.log N + (m : ℝ) / N) ≤ τ := by
    have := Real.sqrt_le_sqrt hΔ
    rw [Real.sqrt_sq (by positivity)] at this
    linarith
  have hmm0 : (0 : ℝ) < (m : ℝ) * ((m : ℝ) + 1) := by positivity
  set A := law ε (2 * h) m * ((m : ℝ) * ((m : ℝ) + 1)) / x with hAdef
  have hA_lo : 1 - τ ≤ A := by
    rw [hAdef, le_div_iff₀ hx0]
    have hmul := mul_le_mul_of_nonneg_right hlow hmm0.le
    have e : x / ((m : ℝ) * ((m : ℝ) + 1)) * (1 - 20 * (x * Real.log ((m : ℝ) + 1) / m + ε * Real.log N +
        m * Real.exp (-((m : ℝ) / 9)))) * ((m : ℝ) * ((m : ℝ) + 1)) =
        x * (1 - 20 * (x * Real.log ((m : ℝ) + 1) / m + ε * Real.log N +
          m * Real.exp (-((m : ℝ) / 9)))) := by field_simp
    rw [e] at hmul
    have : x * (1 - τ) ≤ x * (1 - 20 * (x * Real.log ((m : ℝ) + 1) / m + ε * Real.log N +
          m * Real.exp (-((m : ℝ) / 9)))) := mul_le_mul_of_nonneg_left (by linarith) hx0.le
    linarith
  have hA_hi : A ≤ 1 + τ := by
    rw [hAdef, div_le_iff₀ hx0]
    have hmul := mul_le_mul_of_nonneg_right hup hmm0.le
    have e : x / ((m : ℝ) * ((m : ℝ) + 1)) * (1 + 20000 * Real.sqrt (x * Real.log m ^ 2 / m +
        ε * Real.log N + (m : ℝ) / N)) * ((m : ℝ) * ((m : ℝ) + 1)) =
        x * (1 + 20000 * Real.sqrt (x * Real.log m ^ 2 / m + ε * Real.log N + (m : ℝ) / N)) := by
      field_simp
    rw [e] at hmul
    have : x * (1 + 20000 * Real.sqrt (x * Real.log m ^ 2 / m + ε * Real.log N + (m : ℝ) / N)) ≤
        x * (1 + τ) := mul_le_mul_of_nonneg_left (by linarith) hx0.le
    linarith
  refine ⟨?_, ?_⟩
  · rw [abs_le]; constructor
    · linarith only [hA_lo, hτη, hτ0]
    · linarith only [hA_hi, hτη, hτ0]
  · -- the mirror term
    obtain ⟨hB0, hBle⟩ := profile_mirror hε0 (h := h) (m := m) hN hx hε100 hA h8m
    set B := law ε (2 * h) (2 * h - m) * (m : ℝ) ^ 2 / x with hBdef
    have hB0' : 0 ≤ B := by rw [hBdef]; positivity
    have hBup : B ≤ τ := by
      rw [hBdef, div_le_iff₀ hx0]
      have hpow : N ^ (2 * ε) * Real.exp (5200 * ε) ≤ 3 := by
        rw [Real.rpow_def_of_pos hN0, ← Real.exp_add]
        have h1 : Real.log N * (2 * ε) + 5200 * ε ≤ 1 := by
          have e : Real.log N * (2 * ε) = 2 * (ε * Real.log N) := by ring
          rw [e]; linarith
        have := Real.exp_le_exp.mpr h1
        have h3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
        linarith
      have hm2 : (m : ℝ) ^ 2 ≤ δ ^ 2 * N ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hm0.le hmδ 2
      have hlaw : law ε (2 * h) (2 * h - m) ≤ 4 * ε / (N + 2) * (N ^ (2 * ε) * Real.exp (5200 * ε)) := by
        rw [← mul_assoc]; exact hBle
      have h1 : law ε (2 * h) (2 * h - m) * (m : ℝ) ^ 2 ≤
          4 * ε / (N + 2) * (N ^ (2 * ε) * Real.exp (5200 * ε)) * (δ ^ 2 * N ^ 2) :=
        mul_le_mul hlaw hm2 (sq_nonneg _) (by positivity)
      have h4 : 4 * ε / (N + 2) * (δ ^ 2 * N ^ 2) ≤ 4 * δ ^ 2 * x := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have e : 4 * ε * (δ ^ 2 * N ^ 2) = 4 * δ ^ 2 * x * N := by rw [hxdef]; ring
        rw [e]
        have : 0 ≤ 4 * δ ^ 2 * x := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith only [hN0]) this
      have h5 : 4 * ε / (N + 2) * (N ^ (2 * ε) * Real.exp (5200 * ε)) * (δ ^ 2 * N ^ 2) ≤
          12 * δ ^ 2 * x := by
        calc 4 * ε / (N + 2) * (N ^ (2 * ε) * Real.exp (5200 * ε)) * (δ ^ 2 * N ^ 2)
            = (4 * ε / (N + 2) * (δ ^ 2 * N ^ 2)) * (N ^ (2 * ε) * Real.exp (5200 * ε)) := by ring
          _ ≤ (4 * δ ^ 2 * x) * 3 := mul_le_mul h4 hpow (by positivity) (by positivity)
          _ = 12 * δ ^ 2 * x := by ring
      have h6 : 12 * δ ^ 2 ≤ τ := by
        have h61 : δ ^ 2 ≤ δ * (1 / 6000) := by rw [sq]; exact mul_le_mul_of_nonneg_left hδs hδ0.le
        have h62 : δ * (1 / 6000) ≤ τ / 60 * (1 / 6000) := mul_le_mul_of_nonneg_right hδτ (by norm_num)
        linarith only [h61, h62, hτ0]
      have h7 : 12 * δ ^ 2 * x ≤ τ * x := mul_le_mul_of_nonneg_right h6 hx0.le
      linarith only [h1, h5, h7]
    have hP := profile_P_eq ε (N := 2 * h) (m := m) (by omega) hmN
    have hPe : ewBin ε (2 * h) (2 * h - m) * (2 * (m : ℝ) ^ 2) / x = A * ((m : ℝ) / ((m : ℝ) + 1)) + B := by
      rw [hP, hAdef, hBdef]; field_simp
    rw [hPe]
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith only [hm0]
    have hfrac1 : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hm1]; linarith only
    have hfrac2 : 1 - τ / 14000 ≤ (m : ℝ) / ((m : ℝ) + 1) := by
      have e : (m : ℝ) / ((m : ℝ) + 1) = 1 - 1 / ((m : ℝ) + 1) := by
        rw [one_sub_div hm1.ne']; congr 1; ring
      rw [e]
      have h' : 1 / ((m : ℝ) + 1) ≤ 1 / (m : ℝ) := one_div_le_one_div_of_le hm0 (by linarith only)
      linarith only [h', hinvm]
    have hA0 : 0 ≤ A := by linarith only [hA_lo, hτ1]
    rw [abs_le]
    constructor
    · have h1 : (1 - τ) * (1 - τ / 14000) ≤ A * ((m : ℝ) / ((m : ℝ) + 1)) :=
        mul_le_mul hA_lo hfrac2 (by linarith only [hτ1, hτ0]) hA0
      have e : (1 - τ) * (1 - τ / 14000) = 1 - τ - τ / 14000 + τ * τ / 14000 := by ring
      have h2 : 0 ≤ τ * τ / 14000 := by positivity
      linarith only [h1, e, h2, hB0', hτη, hτ0]
    · have h1 : A * ((m : ℝ) / ((m : ℝ) + 1)) ≤ A := mul_le_of_le_one_right hA0 hfrac1
      linarith only [h1, hA_hi, hBup, hτη, hτ0]

/-- **Theorem S2.1 (`thm:profile`), with sequences.** Let `N = 2h`, eventually `ε_h > 0` and
`x_h = N ε_h ≥ 1` and `x_h log²N/N → 0`, let `ω_h → ∞` and `δ'_h → 0`. Then for every `η > 0`,
eventually in `h`, for all `m` with `ω_h x_h log²(x_h+1) ≤ m ≤ δ'_h N`:
`|f_N(m) m(m+1)/x - 1| ≤ η` and `|P_N(N-m) 2m²/x - 1| ≤ η`. (The paper also assumes
`ω_N x log²(x+1) = o(N)`, which only makes the range nonempty and is not needed here.) -/
theorem thm_profile (ε ω δ' : ℕ → ℝ) (hε0 : ∀ᶠ h in atTop, 0 < ε h)
    (hx : ∀ᶠ h in atTop, 1 ≤ ((2 * h : ℕ) : ℝ) * ε h)
    (hlim : Tendsto (fun h : ℕ => ((2 * h : ℕ) : ℝ) * ε h * Real.log ((2 * h : ℕ) : ℝ) ^ 2 /
      ((2 * h : ℕ) : ℝ)) atTop (𝓝 0))
    (hω : Tendsto ω atTop atTop) (hδ' : Tendsto δ' atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ h in atTop, ∀ m : ℕ,
      ω h * (((2 * h : ℕ) : ℝ) * ε h) * Real.log (((2 * h : ℕ) : ℝ) * ε h + 1) ^ 2 ≤ m →
      (m : ℝ) ≤ δ' h * ((2 * h : ℕ) : ℝ) →
      |law (ε h) (2 * h) m * ((m : ℝ) * ((m : ℝ) + 1)) / (((2 * h : ℕ) : ℝ) * ε h) - 1| ≤ η ∧
        |ewBin (ε h) (2 * h) (2 * h - m) * (2 * (m : ℝ) ^ 2) / (((2 * h : ℕ) : ℝ) * ε h) - 1| ≤ η := by
  obtain ⟨W, δ, hδ0, hU⟩ := thm_profile_uniform hη
  filter_upwards [eventually_ge_atTop 32, hω.eventually (eventually_ge_atTop W),
    hδ'.eventually (ge_mem_nhds hδ0), hlim.eventually (ge_mem_nhds hδ0), hε0, hx] with h h32 hωW hδδ hlimδ hε0h hxh
  intro m hm1 hm2
  have hxL : 0 ≤ (((2 * h : ℕ) : ℝ) * ε h) * Real.log (((2 * h : ℕ) : ℝ) * ε h + 1) ^ 2 := by
    have := hxh
    have : 0 ≤ Real.log (((2 * h : ℕ) : ℝ) * ε h + 1) := Real.log_nonneg (by linarith)
    positivity
  have hN0 : (0 : ℝ) ≤ ((2 * h : ℕ) : ℝ) := Nat.cast_nonneg _
  refine hU h m (ε h) (by omega) hε0h hxh hlimδ ?_ ?_
  · calc W * (((2 * h : ℕ) : ℝ) * ε h) * Real.log (((2 * h : ℕ) : ℝ) * ε h + 1) ^ 2
        = W * ((((2 * h : ℕ) : ℝ) * ε h) * Real.log (((2 * h : ℕ) : ℝ) * ε h + 1) ^ 2) := by ring
      _ ≤ ω h * ((((2 * h : ℕ) : ℝ) * ε h) * Real.log (((2 * h : ℕ) : ℝ) * ε h + 1) ^ 2) :=
          mul_le_mul_of_nonneg_right hωW hxL
      _ = _ := by ring
      _ ≤ m := hm1
  · exact hm2.trans (mul_le_mul_of_nonneg_right hδδ hN0)

end Kagey131.PaperD
