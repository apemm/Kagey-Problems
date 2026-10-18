import PaperD.U3_Main

/-!
# Paper D, track U3: Proposition 3.25(d) (convexity for large odd `N`)

For odd `N = 2k+1` the crossing `ε_N` is defined by `C̃_N = P_N(k+1) = E_N` (Proposition 3.25,
first paragraph, `odd_crossing_exists_unique`). Here

* `odd_center_upper`: `C̃_N ≤ 192 ε/(N+3)` when `ε(1 + log(N+1)) ≤ 1/100` and `log(N+1) ≥ 30`
  (Proposition 3.25(a) with Theorem 2.6(b) at `N+1`);
* `odd_window_of`, `odd_crossing_window`: for all large odd `N`, `log N ≤ x_N ≤ 2 log N`
  (a crude form of Proposition 3.25(b), enough for the Landau window);
* `prop_odd_d` (Proposition 3.25(d)): modulo Theorem 3.9(b) and Lemma 3.10, the law at the
  crossing is convex between the humps for every large odd `N`.
-/

namespace Kagey131.PaperD

open Real Filter Topology Set

/-- `C̃_N ≤ 192 ε/(N+3)` for `N = 2k+1`, `ε(1 + log(N+1)) ≤ 1/100` and `log(N+1) ≥ 30`. -/
theorem odd_center_upper {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε)
    (hε : ε * (1 + Real.log ((2 * (k + 1) : ℕ) : ℝ)) ≤ 1 / 100)
    (hL : 30 ≤ Real.log ((2 * (k + 1) : ℕ) : ℝ)) :
    ewBin ε (2 * k + 1) (k + 1) ≤ 192 * ε / (((2 * (k + 1) : ℕ) : ℝ) + 2) := by
  set M : ℝ := ((2 * (k + 1) : ℕ) : ℝ) with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  have hc := odd_center_succ ε k
  have hup := center_upper_all (h := k + 1) (by omega) h0 hε
  rw [← hM] at hup
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hε1 : ε ≤ 1 / 3100 := by nlinarith
  have hCt : 0 ≤ ewBin ε (2 * k + 1) (k + 1) :=
    ewBin_nonneg h0.le (by linarith) (by omega) (by omega)
  have hf : 1 / 2 ≤ 1 - (1 - 2 * ε) / (2 * (k : ℝ) + 1) := by
    have : (1 - 2 * ε) / (2 * (k : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hrp : M ^ (2 * ε) ≤ 3 := by
    rw [Real.rpow_def_of_pos hM0]
    have : Real.log M * (2 * ε) ≤ 1 := by nlinarith
    calc Real.exp (Real.log M * (2 * ε)) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hex : Real.exp (5200 * ε) ≤ 8 := by
    have : 5200 * ε ≤ 2 := by linarith
    calc Real.exp (5200 * ε) ≤ Real.exp 2 := Real.exp_le_exp.mpr this
      _ = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 8 := by
        have := Real.exp_one_lt_d9
        have h0' : 0 < Real.exp 1 := Real.exp_pos 1
        nlinarith
  have hA : 0 ≤ 4 * ε / (M + 2) := by positivity
  have hrp0 : 0 ≤ M ^ (2 * ε) := Real.rpow_nonneg hM0.le _
  have hC' : ewBin ε (2 * (k + 1)) (k + 1) ≤ 4 * ε / (M + 2) * 3 * 8 := by
    calc ewBin ε (2 * (k + 1)) (k + 1) ≤ 4 * ε / (M + 2) * M ^ (2 * ε) * Real.exp (5200 * ε) := hup
      _ ≤ 4 * ε / (M + 2) * 3 * 8 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hrp hA) hex (Real.exp_pos _).le (by positivity)
  have e : 192 * ε / (M + 2) = 2 * (4 * ε / (M + 2) * 3 * 8) := by ring
  rw [e]
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The odd crossing lies in the Landau window.** Let `N = 2k+1` with `L = log N ≥ 30`,
`L²/N ≤ 1/300` and `L/N ≤ 1/1152`. If `0 < ε₀ < 1` and `C̃_N = E_N` at `ε₀`, then
`L ≤ N ε₀ ≤ 2L`. -/
theorem odd_window_of {k : ℕ} (hk : 1 ≤ k) (hL : 30 ≤ Real.log ((2 * k + 1 : ℕ) : ℝ))
    (hc2 : Real.log ((2 * k + 1 : ℕ) : ℝ) ^ 2 / ((2 * k + 1 : ℕ) : ℝ) ≤ 1 / 300)
    (hc3 : Real.log ((2 * k + 1 : ℕ) : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ≤ 1 / 1152)
    {ε₀ : ℝ} (h0 : 0 < ε₀) (h1 : ε₀ < 1)
    (hcross : ewBin ε₀ (2 * k + 1) (k + 1) = ewBin ε₀ (2 * k + 1) (2 * k + 1)) :
    Real.log ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) * ε₀ ∧
      ((2 * k + 1 : ℕ) : ℝ) * ε₀ ≤ 2 * Real.log ((2 * k + 1 : ℕ) : ℝ) := by
  set N : ℝ := ((2 * k + 1 : ℕ) : ℝ) with hN
  set L := Real.log N with hLdef
  have hN0 : 0 < N := by rw [hN]; positivity
  have hNk : N = 2 * (k : ℝ) + 1 := by rw [hN]; push_cast; ring
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL0 : 0 < L := by linarith
  have hexpL : Real.exp (-L) = 1 / N := by
    rw [Real.exp_neg, hLdef, Real.exp_log hN0]; ring
  rw [div_le_iff₀ hN0] at hc2 hc3
  have hmono := (odd_crossing_exists_unique hk).1
  have hE : ∀ ε, ε < 1 → 0 < ewBin ε (2 * k + 1) (2 * k + 1) := by
    intro ε hε; rw [ewBin_top]; have : 0 < 1 - ε := by linarith
    positivity
  have hR1 : ewBin ε₀ (2 * k + 1) (k + 1) / ewBin ε₀ (2 * k + 1) (2 * k + 1) = 1 := by
    rw [hcross]; exact div_self (hE ε₀ h1).ne'
  constructor
  · -- at `ε = L/N` the central bin is below the end
    by_contra hc
    push Not at hc
    set e := L / N with he
    have he0 : 0 < e := by positivity
    have heN : N * e = L := by rw [he]; field_simp
    have he4 : e ≤ 1 / 1152 := by rw [he, div_le_iff₀ hN0]; linarith
    have hlt : ε₀ < e := by
      rw [he, lt_div_iff₀ hN0]; linarith
    -- the log of `N + 1`
    have hM : ((2 * (k + 1) : ℕ) : ℝ) = N + 1 := by rw [hNk]; push_cast; ring
    have hlogM : Real.log (N + 1) ≤ L + 1 := by
      have : Real.log (N + 1) ≤ Real.log (2 * N) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hN0.ne'] at this
      have := Real.log_two_lt_d9
      linarith
    have hlogM' : 30 ≤ Real.log (N + 1) := by
      have : L ≤ Real.log (N + 1) := Real.log_le_log hN0 (by linarith)
      linarith
    have hεc : e * (1 + Real.log ((2 * (k + 1) : ℕ) : ℝ)) ≤ 1 / 100 := by
      rw [hM]
      have : e * (1 + Real.log (N + 1)) ≤ e * (L + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) he0.le
      have h2 : e * (L + 2) * N = L * (L + 2) := by rw [← heN]; ring
      have : e * (L + 2) ≤ 1 / 100 := by
        rw [← mul_le_mul_iff_of_pos_right hN0, h2]; nlinarith
      linarith
    have hup := odd_center_upper hk he0 hεc (by rw [hM]; exact hlogM')
    rw [hM] at hup
    -- the end is at least `1/(6N)`
    have hEb : 1 / (6 * N) ≤ ewBin e (2 * k + 1) (2 * k + 1) := by
      rw [ewBin_top]
      have hlog := log_one_sub_ge he0.le (by linarith)
      have hpow : Real.exp ((2 * (k : ℝ)) * (-e - e ^ 2)) ≤ (1 - e) ^ (2 * k) := by
        rw [← Real.exp_log (show 0 < (1 - e) ^ (2 * k) by
          have : 0 < 1 - e := by linarith
          positivity), Real.log_pow]
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith
      have hlow : -L - 1 ≤ (2 * (k : ℝ)) * (-e - e ^ 2) := by
        have h2k : 2 * (k : ℝ) = N - 1 := by rw [hNk]; ring
        rw [h2k]
        have hee : N * e ^ 2 ≤ 1 := by
          have : N * e ^ 2 * N = L ^ 2 := by rw [← heN]; ring
          nlinarith
        nlinarith
      have hexp1 : Real.exp (-L - 1) = 1 / N * Real.exp (-1) := by
        rw [← hexpL, ← Real.exp_add]; ring_nf
      have he1 : 1 / 3 ≤ Real.exp (-1) := by
        have := Real.add_one_le_exp (-1 : ℝ)
        have h2 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
        have := Real.exp_one_lt_d9
        nlinarith [Real.exp_pos (-1)]
      have := Real.exp_le_exp.mpr hlow
      rw [hexp1] at this
      have h6 : 1 / (6 * N) = 1 / N * (1 / 3) / 2 := by field_simp; ring
      rw [h6]
      have : 1 / N * (1 / 3) ≤ 1 / N * Real.exp (-1) :=
        mul_le_mul_of_nonneg_left he1 (by positivity)
      linarith
    have hlt2 : ewBin e (2 * k + 1) (k + 1) < ewBin e (2 * k + 1) (2 * k + 1) := by
      have : 192 * e / (N + 1 + 2) < 1 / (6 * N) := by
        rw [div_lt_div_iff₀ (by linarith) (by positivity)]
        have : 192 * e * (6 * N) = 1152 * L := by rw [← heN]; ring
        rw [this]; linarith
      linarith
    have hR : ewBin e (2 * k + 1) (k + 1) / ewBin e (2 * k + 1) (2 * k + 1) < 1 := by
      rw [div_lt_one (hE e (by linarith))]; exact hlt2
    have := hmono ⟨h0, h1⟩ ⟨he0, by linarith⟩ hlt
    simp only at this
    linarith
  · -- at `ε = 2L/N` the central bin is above the end
    by_contra hc
    push Not at hc
    obtain ⟨e, he⟩ : ∃ e : ℝ, e = 2 * L / N := ⟨_, rfl⟩
    have he0 : 0 < e := by rw [he]; positivity
    have heN : N * e = 2 * L := by rw [he]; field_simp
    have he4 : e ≤ 1 / 500 := by
      have : N * e ≤ N * (1 / 500) := by rw [heN]; linarith
      exact le_of_mul_le_mul_left this hN0
    have hlt : e < ε₀ := by
      have : N * e < N * ε₀ := by rw [heN]; linarith
      exact lt_of_mul_lt_mul_left this hN0.le
    have hfac := odd_center_succ e k
    have he2 : e < 1 / 2 := by linarith
    have hlow := center_lower (h := k + 1) (by omega) he0 he2
    have hM : ((2 * (k + 1) : ℕ) : ℝ) = N + 1 := by rw [hNk]; push_cast; ring
    rw [hM] at hlow
    have hCt : 0 ≤ ewBin e (2 * k + 1) (k + 1) :=
      ewBin_nonneg he0.le (by linarith) (by omega) (by omega)
    have hf : 1 - (1 - 2 * e) / (2 * (k : ℝ) + 1) ≤ 1 := by
      have : 0 ≤ (1 - 2 * e) / (2 * (k : ℝ) + 1) := div_nonneg (by linarith) (by positivity)
      linarith
    have hge : ewBin e (2 * (k + 1)) (k + 1) ≤ ewBin e (2 * k + 1) (k + 1) := by
      rw [hfac]; nlinarith
    -- `C_{N+1} ≥ 2L/N²`
    have hC : 2 * L / N ^ 2 ≤ ewBin e (2 * (k + 1)) (k + 1) := by
      have : 2 * L / N ^ 2 ≤ 4 * e / (N + 1 + 2) * (1 - 2 * e) := by
        rw [div_le_iff₀ (by positivity)]
        have h1' : 4 * e / (N + 1 + 2) * (1 - 2 * e) * N ^ 2 =
            4 * (N * e) * (1 - 2 * e) * N / (N + 3) := by field_simp; ring
        rw [h1', heN, le_div_iff₀ (by linarith)]
        nlinarith
      linarith
    -- the end is at most `3/(2N²)`
    have hEb : ewBin e (2 * k + 1) (2 * k + 1) ≤ 3 / (2 * N ^ 2) := by
      rw [ewBin_top]
      have h1e : 1 - e ≤ Real.exp (-e) := by have := Real.add_one_le_exp (-e); linarith
      have hp : (1 - e) ^ (2 * k) ≤ Real.exp (-e) ^ (2 * k) :=
        pow_le_pow_left₀ (by linarith) h1e _
      rw [← Real.exp_nat_mul] at hp
      have h2k : ((2 * k : ℕ) : ℝ) * (-e) ≤ -(2 * L) + 1 := by
        have : ((2 * k : ℕ) : ℝ) = N - 1 := by rw [hNk]; push_cast; ring
        rw [this]; nlinarith
      have hx := Real.exp_le_exp.mpr h2k
      have hexp2 : Real.exp (-(2 * L) + 1) = 1 / N * (1 / N) * Real.exp 1 := by
        rw [← hexpL, ← Real.exp_add, ← Real.exp_add]; ring_nf
      rw [hexp2] at hx
      have := Real.exp_one_lt_d9
      have h3 : 1 / N * (1 / N) * Real.exp 1 ≤ 1 / N * (1 / N) * 3 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h4 : 3 / (2 * N ^ 2) = 1 / N * (1 / N) * 3 / 2 := by field_simp
      rw [h4]
      linarith
    have hgt : ewBin e (2 * k + 1) (2 * k + 1) < ewBin e (2 * k + 1) (k + 1) := by
      have : 3 / (2 * N ^ 2) < 2 * L / N ^ 2 := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
      linarith
    have hR : 1 < ewBin e (2 * k + 1) (k + 1) / ewBin e (2 * k + 1) (2 * k + 1) := by
      rw [one_lt_div (hE e (by linarith))]; exact hgt
    have := hmono ⟨he0, by linarith⟩ ⟨h0, h1⟩ hlt
    simp only at this
    linarith

/-- For all large odd `N`, every crossing `ε₀ ∈ (0,1)` has `log N ≤ N ε₀ ≤ 2 log N`. -/
theorem odd_crossing_window :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N = 2 * k + 1 → ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 →
      ewBin ε₀ (2 * k + 1) (k + 1) = ewBin ε₀ (2 * k + 1) (2 * k + 1) →
      Real.log (N : ℝ) ≤ (N : ℝ) * ε₀ ∧ (N : ℝ) * ε₀ ≤ 2 * Real.log (N : ℝ) := by
  filter_upwards [tendsto_logNat.eventually_ge_atTop 30,
    (tendsto_order.1 (tendsto_logpow_div_nat 2)).2 (1 / 300) (by norm_num),
    (tendsto_order.1 (tendsto_logpow_div_nat 1)).2 (1 / 1152) (by norm_num),
    eventually_ge_atTop 3] with N hL h2 h1 h3
  intro k hk ε₀ h0 h1' hc
  subst hk
  rw [pow_one] at h1
  exact odd_window_of (by omega) hL h2.le h1.le h0 h1' hc

/-- **Proposition 3.25(d) (`prop:odd`(d)), modulo Theorem 3.9(b) and Lemma 3.10.** There is
`N₁'` such that for every odd `N ≥ N₁'` the law at the crossing is convex between the humps. -/
theorem prop_odd_d {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ}
    (hsep : LandauSep fL lL κ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Odd N → N₁ ≤ N → T5.ConvexBetweenHumps N := by
  have hκ := hsep.1
  have hU := uniform_halfway hLim hsep (η := κ / 100) (by positivity) (by linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((hU.and odd_crossing_window).and
    (tendsto_logNat.eventually_ge_atTop 30))
  refine ⟨max N₁ 3, fun N hOdd hN => ?_⟩
  obtain ⟨⟨hUN, hWN⟩, hL⟩ := hN₁ N (le_of_max_le_left hN)
  obtain ⟨k, rfl⟩ := hOdd
  have hk : 1 ≤ k := by have := le_of_max_le_right hN; omega
  intro ε h0 h1 hcross aS hmode haS a ha1 ha2
  rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega] at hcross
  obtain ⟨hxL, hx2L⟩ := hWN k rfl ε h0 h1 hcross
  obtain ⟨-, ε₁, ⟨he0, he1⟩, -, huniq⟩ := odd_crossing_exists_unique hk
  have hε2 : ε < 1 / 2 := by rw [huniq ε ⟨h0, h1⟩ hcross]; exact he1
  have haN := mode_le_N h0 h1 (by omega) hmode
  set m := (((2 * k + 1 : ℕ) : ℤ) - aS).toNat with hm
  have hmZ : (m : ℤ) = ((2 * k + 1 : ℕ) : ℤ) - aS := by rw [hm]; omega
  have hmode' : ∀ a : ℤ, lawZ ε (2 * k + 1) a ≤
      lawZ ε (2 * k + 1) (((2 * k + 1 : ℕ) : ℤ) - m) := by
    rw [hmZ, show ((2 * k + 1 : ℕ) : ℤ) - (((2 * k + 1 : ℕ) : ℤ) - aS) = aS by ring]
    exact hmode
  obtain ⟨hm4, hhalfm, -⟩ := hUN ε h0 h1 hxL hx2L m (by omega) hmode'
  have hdip := lawZ_dip_of_hx h0 h1 (show 2 ≤ 2 * k + 1 by omega) (by linarith)
  exact convex_of_halfway h0 hε2 (by omega) hdip hmode' hm4 hhalfm a (by omega) (by omega)

/-- Proposition 3.25(d) for the Landau density, from Theorem 3.9(b) and Lemma 3.10. -/
theorem prop_odd_d_landau (hLim : LandauLimitHyp landauDensity) (hMode : LandauModeCert) :
    ∃ N₁ : ℕ, ∀ N : ℕ, Odd N → N₁ ≤ N → T5.ConvexBetweenHumps N := by
  obtain ⟨lL, hl⟩ := hMode
  exact prop_odd_d hLim (landauSep_of_modeHyp hl)

/-- **Every crossing of a large `N`, even or odd, lies in the Landau window:** for all large `N`
and every `ε ∈ (0,1)` with `P_N(⌈N/2⌉) = E_N`, `log N ≤ Nε ≤ 2 log N`. -/
theorem crossing_window :
    ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ε < 1 → ewBin ε N ((N + 1) / 2) = ewBin ε N N →
      Real.log (N : ℝ) ≤ (N : ℝ) * ε ∧ (N : ℝ) * ε ≤ 2 * Real.log (N : ℝ) := by
  filter_upwards [odd_crossing_window, tendsto_logNat.eventually_ge_atTop 30] with N hW hL
  intro ε h0 h1 hc
  rcases Nat.even_or_odd N with ⟨h, rfl⟩ | ⟨k, rfl⟩
  · have e2 : h + h = 2 * h := by ring
    simp only [e2] at hc hL ⊢
    rw [show (2 * h + 1) / 2 = h by omega] at hc
    have hcast : ((2 * h : ℕ) : ℝ) = 2 * (h : ℝ) := by push_cast; ring
    rw [hcast] at hL ⊢
    have hh := one_le_of_L30 hL
    obtain ⟨-, -, huniq⟩ := crossingEps_spec hh
    have := huniq ε ⟨h0, h1⟩ hc
    subst this
    have hb := crossingX_between hL
    unfold crossingX at hb
    constructor <;> nlinarith [hb.1, hb.2]
  · rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega] at hc
    exact hW k rfl ε h0 h1 hc

/-- **Theorem 3.21 and Proposition 3.25(d) together:** for every large `N`, even or odd, the law
at the crossing is convex between the humps. -/
theorem convex_large_all {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ}
    (hsep : LandauSep fL lL κ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → T5.ConvexBetweenHumps N := by
  obtain ⟨A, hA⟩ := thm_convex_large hLim hsep
  obtain ⟨B, hB⟩ := prop_odd_d hLim hsep
  refine ⟨max A B, fun N hN => ?_⟩
  rcases Nat.even_or_odd N with h | h
  · exact hA N h (le_of_max_le_left hN)
  · exact hB N h (le_of_max_le_right hN)

end Kagey131.PaperD
