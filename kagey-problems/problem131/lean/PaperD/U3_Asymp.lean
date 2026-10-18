import PaperD.U3_Transfer
import PaperD.EndToEnd

/-!
# Paper D, track U3: the asymptotic inputs at the even crossing

For `N = 2h` and the crossing `ε_N = crossingEps h`, `x_N = crossingX h`, `L = log N`:

* `crossingX_between`: `L ≤ x_N ≤ 2L` once `L ≥ 30` (from Theorem 2.7, `crossing_explicit`,
  proved in this library);
* `tendsto_crossingX`: `x_N → ∞`;
* `xdeltaB_le`: `x δ_B ≤ 300 L⁵/N` when `x ≤ 2L` and `16L²/N ≤ 1`;
* `eventually_landau_small`: the error of Theorem 3.9(b) at the crossing tends to `0`;
* `eventually_halfway`: Steps 1 to 3 of Theorem 3.21 at the crossing for all large even `N`.
-/

namespace Kagey131.PaperD

open Real Filter Topology

/-- `3 < log 30`. -/
theorem three_lt_log_thirty : (3 : ℝ) < Real.log 30 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  calc Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 := by gcongr
    _ < 30 := by norm_num

/-- **The crossing is between `L` and `2L`.** For `N = 2h` with `L = log N ≥ 30`,
`L ≤ x_N ≤ 2L` (from Theorem 2.7(b) in its explicit form, `crossing_explicit`). -/
theorem crossingX_between {h : ℕ} (hL : 30 ≤ Real.log (2 * (h : ℝ))) :
    Real.log (2 * (h : ℝ)) ≤ crossingX h ∧ crossingX h ≤ 2 * Real.log (2 * (h : ℝ)) := by
  have hh := one_le_of_L30 hL
  have hc := (crossing_explicit hL (centerLowerBoundAt_holds hh)
    (centerUpperBoundAt_holds hh)).2.2.2
  set L := Real.log (2 * (h : ℝ)) with hLdef
  have hL0 : 0 < L := by linarith
  have hlogL : 3 < Real.log L := by
    calc (3 : ℝ) < Real.log 30 := three_lt_log_thirty
      _ ≤ Real.log L := Real.log_le_log (by norm_num) hL
  have hhalf := log_le_half hL0
  have h16 : Real.log 16 = 4 * Real.log 2 := log_sixteen_eq
  have hl2 := log_two_bounds
  obtain ⟨c1, c2⟩ := abs_le.mp hc
  have hq1 : (2 * Real.log L + 5) / L ≤ Real.log L + Real.log 16 := by
    rw [div_le_iff₀ hL0]; nlinarith
  have hq2 : (2 * Real.log L + 5) / L ≤ 2 := by
    rw [div_le_iff₀ hL0]; nlinarith
  constructor <;> nlinarith

theorem tendsto_logTwoH : Tendsto (fun h : ℕ => Real.log (2 * (h : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)

theorem eventually_L30' : ∀ᶠ h : ℕ in atTop, 30 ≤ Real.log (2 * (h : ℝ)) :=
  tendsto_logTwoH.eventually_ge_atTop 30

/-- `x_N → ∞` along the even crossings. -/
theorem tendsto_crossingX : Tendsto crossingX atTop atTop :=
  tendsto_atTop_mono' atTop (eventually_L30'.mono fun _ hL => (crossingX_between hL).1)
    tendsto_logTwoH

/-- `L^k / N → 0` for `N = 2h`, `L = log N`. -/
theorem tendsto_logpow_div (k : ℕ) :
    Tendsto (fun h : ℕ => Real.log (2 * (h : ℝ)) ^ k / (2 * (h : ℝ))) atTop (𝓝 0) := by
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero
  simp only [one_mul, add_zero] at h1
  exact h1.comp (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)

/-- `(1 + log t)/t → 0`. -/
theorem tendsto_one_add_log_div :
    Tendsto (fun t : ℝ => (1 + Real.log t) / t) atTop (𝓝 0) := by
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simp only [one_mul, add_zero, pow_one] at h1
  have h2 := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have := h2.add h1
  simp only [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  field_simp

/-- The bound `x δ_B ≤ 300 L⁵/N` for `L = log N ≥ 1`, `0 ≤ x ≤ 2L` and `16L²/N ≤ 1`. -/
theorem xdeltaB_le {N : ℕ} {x : ℝ} (hN : 0 < (N : ℝ)) (h1 : 1 ≤ Real.log N) (hx0 : 0 ≤ x)
    (hx : x ≤ 2 * Real.log N) (hsmall : 16 * Real.log N ^ 2 / N ≤ 1) :
    x * deltaB N x ≤ 300 * Real.log N ^ 5 / N := by
  set L := Real.log N with hL
  have hH0 : 0 ≤ harmR N := by
    have : (0 : ℚ) ≤ harmonic N := by unfold harmonic; positivity
    unfold harmR; exact_mod_cast this
  have hH1 : harmR N ≤ 1 + L := by unfold harmR; exact harmonic_le_one_add_log N
  have hexp : Real.exp (4 * x ^ 2 / N) ≤ 3 := by
    have : 4 * x ^ 2 / N ≤ 1 := by
      rw [div_le_iff₀ hN]
      rw [div_le_iff₀ hN] at hsmall
      nlinarith
    calc Real.exp (4 * x ^ 2 / N) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hx2 : x ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have hx3 : x ^ 3 ≤ 8 * L ^ 3 := by
    have : x ^ 3 = x * x ^ 2 := by ring
    rw [this]; nlinarith
  have hHH : harmR N ^ 2 + harmR N ≤ 6 * L ^ 2 := by nlinarith
  have hL3 : L ^ 3 ≤ L ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  have hL4 : L ^ 4 ≤ L ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  have e : x * deltaB N x = (x ^ 3 * L + 4 * x ^ 3 * Real.exp (4 * x ^ 2 / N) +
      4 * x ^ 3 * (harmR N ^ 2 + harmR N)) / N := by
    unfold deltaB; rw [← hL]; field_simp
  rw [e, div_le_div_iff_of_pos_right hN]
  have hE0 : 0 ≤ Real.exp (4 * x ^ 2 / N) := (Real.exp_pos _).le
  have hx30 : 0 ≤ x ^ 3 := by positivity
  have t1 : x ^ 3 * L ≤ 8 * L ^ 4 := by
    have : 8 * L ^ 4 = 8 * L ^ 3 * L := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hx3 (by linarith)
  have t2 : x ^ 3 * Real.exp (4 * x ^ 2 / N) ≤ 8 * L ^ 3 * 3 :=
    mul_le_mul hx3 hexp hE0 (by positivity)
  have t3 : x ^ 3 * (harmR N ^ 2 + harmR N) ≤ 8 * L ^ 3 * (6 * L ^ 2) :=
    mul_le_mul hx3 hHH (by positivity) (by positivity)
  nlinarith

/-- `N ε_N = x_N` with `N = 2h` as a natural number. -/
theorem cast_mul_crossingEps (h : ℕ) : ((2 * h : ℕ) : ℝ) * crossingEps h = crossingX h := by
  unfold crossingX; push_cast; ring

/-- `log N → ∞` over the natural numbers. -/
theorem tendsto_logNat : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `log^k N / N → 0` over the natural numbers. -/
theorem tendsto_logpow_div_nat (k : ℕ) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ k / (N : ℝ)) atTop (𝓝 0) := by
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero
  simp only [one_mul, add_zero] at h1
  exact h1.comp tendsto_natCast_atTop_atTop

/-- `(1 + log(2y))/y → 0`. -/
theorem tendsto_one_add_log_two_div :
    Tendsto (fun y : ℝ => (1 + Real.log (2 * y)) / y) atTop (𝓝 0) := by
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simp only [one_mul, add_zero, pow_one] at h1
  have h2 := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (1 + Real.log 2)
  have := h2.add h1
  simp only [mul_zero, add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.log_mul (by norm_num) ht.ne']
  field_simp
  ring

/-- **The error of Theorem 3.9(b) is uniformly small in the window `log N ≤ x ≤ 2 log N`.**
Assuming Theorem 3.9(b) (`LandauLimitHyp fL`), for every `η > 0` there is `N₀` such that for
every `N ≥ N₀` and every `ε > 0` with `log N ≤ Nε ≤ 2 log N`,
`|x f_N(m) - f_L(λ_m)| ≤ η` for every `m`, where `x = Nε`. -/
theorem uniform_landau_small {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 < ε → Real.log N ≤ (N : ℝ) * ε →
      (N : ℝ) * ε ≤ 2 * Real.log N → ∀ m : ℕ,
        |(N : ℝ) * ε * law ε N m - fL (lamCoord ((N : ℝ) * ε) m)| ≤ η := by
  obtain ⟨C, hC⟩ := hLim
  set U : ℕ → ℝ := fun N => |C| * ((1 + Real.log (2 * Real.log (N : ℝ))) / Real.log (N : ℝ) +
      2 * (Real.log (N : ℝ) ^ 1 / (N : ℝ))) + 300 * (Real.log (N : ℝ) ^ 5 / (N : ℝ)) with hU
  have hUt : Tendsto U atTop (𝓝 0) := by
    have := (((tendsto_one_add_log_two_div.comp tendsto_logNat).add
      ((tendsto_logpow_div_nat 1).const_mul 2)).const_mul |C|).add
        ((tendsto_logpow_div_nat 5).const_mul 300)
    simp only [mul_zero, add_zero] at this
    exact this
  filter_upwards [tendsto_logNat.eventually_ge_atTop 30, (tendsto_order.1 hUt).2 η hη,
    (tendsto_order.1 (tendsto_logpow_div_nat 2)).2 (1 / 16) (by norm_num),
    (tendsto_order.1 (tendsto_logpow_div_nat 1)).2 (1 / 8) (by norm_num),
    eventually_ge_atTop 64] with N hL hUh h2 h1 h64
  intro ε he0 hxL hx2L m
  set L := Real.log (N : ℝ) with hLdef
  set x := (N : ℝ) * ε with hxdef
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 < L := by linarith
  have hε4 : ε ≤ 1 / 4 := by
    rw [pow_one, div_lt_iff₀ hN] at h1
    have : (N : ℝ) * ε ≤ (N : ℝ) * (1 / 4) := by linarith
    exact le_of_mul_le_mul_left this hN
  have key := hC N ε h64 he0 hε4 (by rw [← hxdef]; linarith) m
  have hdB : x * deltaB N x ≤ 300 * L ^ 5 / N :=
    xdeltaB_le hN (by linarith) (by linarith) hx2L
      (by rw [div_lt_iff₀ hN] at h2; rw [div_le_iff₀ hN]; linarith)
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hq : (1 + Real.log x) / x ≤ (1 + Real.log (2 * L)) / L := by
    have hlog : Real.log x ≤ Real.log (2 * L) := Real.log_le_log hx0 hx2L
    calc (1 + Real.log x) / x ≤ (1 + Real.log (2 * L)) / x :=
          div_le_div_of_nonneg_right (by linarith) hx0.le
      _ ≤ (1 + Real.log (2 * L)) / L :=
          div_le_div_of_nonneg_left (by linarith) hL0 hxL
  have ha0 : 0 ≤ (1 + Real.log x) / x + x / N := by positivity
  have hCa : C * ((1 + Real.log x) / x + x / N) ≤ |C| * ((1 + Real.log x) / x + x / N) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) ha0
  have hxN : x / N ≤ 2 * (L ^ 1 / N) := by
    rw [pow_one, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hx2L hN.le
  have hCa2 : |C| * ((1 + Real.log x) / x + x / N) ≤
      |C| * ((1 + Real.log (2 * L)) / L + 2 * (L ^ 1 / N)) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
  have hUh' : U N < η := hUh
  simp only [hU] at hUh'
  have hdB' : x * deltaB N x ≤ 300 * (L ^ 5 / N) := by
    rw [mul_div_assoc] at hdB; exact hdB
  linarith

/-- `|⌊a + 1/2⌋₊ - a| ≤ 1/2` for `a ≥ 0`. -/
theorem floor_half_near {a : ℝ} (ha : 0 ≤ a) : |((⌊a + 1 / 2⌋₊ : ℕ) : ℝ) - a| ≤ 1 / 2 := by
  have h1 := Nat.floor_le (show 0 ≤ a + 1 / 2 by linarith)
  have h2 := Nat.lt_floor_add_one (a + 1 / 2)
  rw [abs_le]; constructor <;> linarith

/-- **Steps 1 to 3 of Theorem 3.21 (`thm:convex-large`), uniformly in the window.** Assume
Theorem 3.9(b) for `fL` and the separation of `fL` at `λL` (Lemma 3.10(c), with continuity at
`λL`). Then for all large `N`, for every `0 < ε < 1` with `log N ≤ Nε ≤ 2 log N` (not only at
the crossing) and every mode `a* = N - m*` of `P_N` with `2m* ≤ N`, we have `2(2m*+2) ≤ N`,
`P_N(m* + ⌊m*/2⌋) < P_N(m*)/2`, and `κ min{1,(λ_{m*}-λL)²} ≤ 4η` for the given `η ≤ κ/100`. -/
theorem uniform_halfway {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ}
    (hsep : LandauSep fL lL κ) {η : ℝ} (hη : 0 < η) (hηκ : 100 * η ≤ κ) :
    ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ε < 1 → Real.log N ≤ (N : ℝ) * ε →
      (N : ℝ) * ε ≤ 2 * Real.log N → ∀ m : ℕ, 2 * m ≤ N →
      (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - m)) →
      2 * (2 * m + 2) ≤ N ∧ ewBin ε N (m + m / 2) < ewBin ε N m / 2 ∧
        κ * min 1 ((lamCoord ((N : ℝ) * ε) m - lL) ^ 2) ≤ 4 * η := by
  obtain ⟨hκ, hcont, hsep'⟩ := hsep
  obtain ⟨ρ, hρ, hcρ⟩ := Metric.continuousAt_iff.mp hcont η hη
  have hlogt : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_logNat
  have hc56 : 0 < 56 + 16 * |lL| := by positivity
  filter_upwards [tendsto_logNat.eventually_ge_atTop 30, uniform_landau_small hLim hη,
    (tendsto_order.1 (tendsto_logpow_div_nat 2)).2 (1 / (56 + 16 * |lL|)) (by positivity),
    (tendsto_order.1 (tendsto_logpow_div_nat 1)).2 (η / 8) (by positivity),
    hlogt.eventually_ge_atTop (5 + 2 / η - lL),
    tendsto_logNat.eventually_ge_atTop (1 / ρ), eventually_ge_atTop 1] with
    N hL hE hX2 hT1 hlg hxρ hN1
  intro ε he0 he1 hxL hx2L m hmN hmode
  set L := Real.log (N : ℝ) with hLdef
  set x := (N : ℝ) * ε with hxdef
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hx0 : 0 < x := by linarith
  have hlogx : Real.log L ≤ Real.log x := Real.log_le_log (by linarith) hxL
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlx2 : Real.log x ≤ 2 * L := by
    have := Real.log_le_sub_one_of_pos hx0; linarith
  have hxlogx : x * Real.log x ≤ 4 * L ^ 2 := by nlinarith
  have hlLx : lL * x ≤ 2 * |lL| * L ^ 2 := by
    have e1 : lL * x ≤ |lL| * x := mul_le_mul_of_nonneg_right (le_abs_self lL) hx0.le
    have e2 : |lL| * x ≤ |lL| * (2 * L) := mul_le_mul_of_nonneg_left hx2L (abs_nonneg _)
    have e3 : |lL| * (2 * L) ≤ 2 * |lL| * L ^ 2 := by
      have : 0 ≤ |lL| * (L * (L - 1)) :=
        mul_nonneg (abs_nonneg _) (mul_nonneg (by linarith) (by linarith))
      nlinarith [this]
    linarith
  have hXb : 8 * (x * Real.log x + lL * x + x) + 8 ≤ (N : ℝ) := by
    rw [div_lt_iff₀ hN] at hX2
    have hb : (56 + 16 * |lL|) * L ^ 2 < (N : ℝ) := by
      calc (56 + 16 * |lL|) * L ^ 2
          < (56 + 16 * |lL|) * (1 / (56 + 16 * |lL|) * (N : ℝ)) :=
            mul_lt_mul_of_pos_left hX2 hc56
        _ = (N : ℝ) := by field_simp
    nlinarith [abs_nonneg lL]
  have hTb : 4 * x ≤ η * (N : ℝ) := by
    rw [pow_one, div_lt_iff₀ hN] at hT1
    nlinarith
  have hlogb : 5 + 2 / η ≤ Real.log x + lL := by linarith
  set a := x * Real.log x + lL * x with ha
  have ha0 : 0 ≤ a := by
    have e : a = x * (Real.log x + lL) := by rw [ha]; ring
    rw [e]
    apply mul_nonneg hx0.le
    have : 0 < 2 / η := by positivity
    linarith
  have hnear := floor_half_near ha0
  have hm'R : ((⌊a + 1 / 2⌋₊ : ℕ) : ℝ) ≤ a + 1 / 2 := Nat.floor_le (by linarith)
  have hm'N : ⌊a + 1 / 2⌋₊ ≤ N := by
    have : ((⌊a + 1 / 2⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast this
  have hlam : |lamCoord x ⌊a + 1 / 2⌋₊ - lL| < ρ := by
    have e : lamCoord x ⌊a + 1 / 2⌋₊ - lL = (((⌊a + 1 / 2⌋₊ : ℕ) : ℝ) - a) / x := by
      unfold lamCoord; rw [ha]; field_simp; ring
    rw [e, abs_div, abs_of_pos hx0, div_lt_iff₀ hx0]
    have h1 : 1 ≤ L * ρ := by rwa [div_le_iff₀ hρ] at hxρ
    nlinarith
  have hm'f : fL lL - η ≤ fL (lamCoord x ⌊a + 1 / 2⌋₊) := by
    have := hcρ (show dist (lamCoord x ⌊a + 1 / 2⌋₊) lL < ρ by rw [Real.dist_eq]; exact hlam)
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).1
    linarith
  exact halfway_master he0 he1 hN1 hx0 hη hηκ hsep' (hE ε he0 hxL hx2L) hm'N hm'f hXb hTb
    hlogb hmN hmode

/-- **Steps 1 to 3 of Theorem 3.21 at the even crossing.** For all large `h`, at `N = 2h` and
`ε = ε_N`, every mode `a* = N - m*` of `P_N` with `2m* ≤ N` satisfies `2(2m*+2) ≤ N` and
`P_N(m* + ⌊m*/2⌋) < P_N(m*)/2`. -/
theorem eventually_halfway {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ}
    (hsep : LandauSep fL lL κ) :
    ∀ᶠ h : ℕ in atTop, ∀ m : ℕ, 2 * m ≤ 2 * h →
      (∀ a : ℤ, lawZ (crossingEps h) (2 * h) a ≤
        lawZ (crossingEps h) (2 * h) (((2 * h : ℕ) : ℤ) - m)) →
      2 * (2 * m + 2) ≤ 2 * h ∧
        ewBin (crossingEps h) (2 * h) (m + m / 2) < ewBin (crossingEps h) (2 * h) m / 2 := by
  have hκ := hsep.1
  have hU := uniform_halfway hLim hsep (η := κ / 100) (by positivity) (by linarith)
  have h2 : Tendsto (fun h : ℕ => 2 * h) atTop atTop :=
    tendsto_id.const_mul_atTop' (by norm_num)
  filter_upwards [h2.eventually hU, eventually_L30'] with h hh hL
  intro m hmN hmode
  have h1 := one_le_of_L30 hL
  obtain ⟨⟨he0, he1⟩, -, -⟩ := crossingEps_spec h1
  obtain ⟨hxL, hx2L⟩ := crossingX_between hL
  have hcast : ((2 * h : ℕ) : ℝ) = 2 * (h : ℝ) := by push_cast; ring
  have hxe := cast_mul_crossingEps h
  have r := hh (crossingEps h) he0 (by linarith) (by rw [hxe, hcast]; exact hxL)
    (by rw [hxe, hcast]; exact hx2L) m hmN hmode
  exact ⟨r.1, r.2.1⟩

end Kagey131.PaperD
