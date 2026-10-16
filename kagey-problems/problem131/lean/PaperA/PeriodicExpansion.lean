import PaperA.PeriodicCrossing

/-!
# Theorem `thm:periodic-crossing` and Corollary `cor:couplings`: the expansions
-/

namespace Kagey131

open Finset Filter Topology Asymptotics

/-- From an expansion of `z` to the expansion of `log z`: if `L ≥ 240`, `|C|, |β| ≤ 1`,
`R ≤ 1` and `|z - (L - ℓ/2 + C + (ℓ/4 - C/2 + β)/L)| ≤ R` with `ℓ = log L`, then
`|log z - ℓ - (C - ℓ/2)/L| ≤ 3ℓ²/L² + R`. -/
theorem log_of_expansion {L C β R z : ℝ} (hL : 240 ≤ L) (hC : |C| ≤ 1) (hβ : |β| ≤ 1)
    (hR0 : 0 ≤ R) (hR : R ≤ 1)
    (hz : |z - (L - Real.log L / 2 + C + (Real.log L / 4 - C / 2 + β) / L)| ≤ R) :
    |Real.log z - Real.log L - (C - Real.log L / 2) / L| ≤ 3 * Real.log L ^ 2 / L ^ 2 + R := by
  set ℓ := Real.log L with hℓ
  have hL0 : 0 < L := by linarith
  have hℓ5 : 5 ≤ ℓ := by
    rw [hℓ]
    have : Real.exp 5 ≤ L := by
      have he := Real.exp_one_lt_d9
      have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h5]
      have : Real.exp 1 ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 5
      have : (2.7182818286 : ℝ) ^ 5 ≤ 240 := by norm_num
      linarith
    rw [← Real.exp_le_exp, Real.exp_log hL0]; exact this
  have hℓL : ℓ ≤ L / 4 := log_le_quarter (by linarith)
  have hCa := abs_le.mp hC
  have hβa := abs_le.mp hβ
  have hza := abs_le.mp hz
  set D := z - L with hD
  have hfrac : |(ℓ / 4 - C / 2 + β) / L| ≤ ℓ / L := by
    rw [abs_div, abs_of_pos hL0]
    apply div_le_div_of_nonneg_right _ hL0.le
    rw [abs_le]; constructor <;> linarith
  have hfa := abs_le.mp hfrac
  have hℓL1 : ℓ / L ≤ 1 := by rw [div_le_one hL0]; linarith
  have hℓL4 : ℓ / L ≤ 1 / 4 := by rw [div_le_iff₀ hL0]; linarith
  have hDb : |D| ≤ ℓ := by rw [abs_le]; constructor <;> linarith
  set t := D / L with ht
  have htb : |t| ≤ ℓ / L := by
    rw [ht, abs_div, abs_of_pos hL0]; exact div_le_div_of_nonneg_right hDb hL0.le
  have hthalf : |t| ≤ 1 / 2 := by
    have : ℓ / L ≤ 1 / 4 := by rw [div_le_iff₀ hL0]; linarith
    linarith
  have hz0 : 0 < z := by have := abs_le.mp hDb; linarith
  have hlog : Real.log z = ℓ + Real.log (1 + t) := by
    rw [hℓ, ← Real.log_mul hL0.ne' (by have := abs_le.mp hthalf; linarith)]
    congr 1; rw [ht, hD]; field_simp; ring
  have h1 := abs_log_one_add_sub_le hthalf
  have h2 : |t - (C - ℓ / 2) / L| ≤ ℓ / L ^ 2 + R / L := by
    have e : t - (C - ℓ / 2) / L = (D - (C - ℓ / 2)) / L := by rw [ht]; ring
    rw [e, abs_div, abs_of_pos hL0]
    have hDC : |D - (C - ℓ / 2)| ≤ ℓ / L + R := by
      have e2 : D - (C - ℓ / 2) = (z - (L - ℓ / 2 + C + (ℓ / 4 - C / 2 + β) / L)) +
          (ℓ / 4 - C / 2 + β) / L := by rw [hD]; ring
      rw [e2]
      calc _ ≤ |z - (L - ℓ / 2 + C + (ℓ / 4 - C / 2 + β) / L)| + |(ℓ / 4 - C / 2 + β) / L| :=
            abs_add_le _ _
        _ ≤ R + ℓ / L := add_le_add hz hfrac
        _ = ℓ / L + R := by ring
    calc |D - (C - ℓ / 2)| / L ≤ (ℓ / L + R) / L := div_le_div_of_nonneg_right hDC hL0.le
      _ = ℓ / L ^ 2 + R / L := by field_simp
  have ht2 : 2 * t ^ 2 ≤ 2 * (ℓ ^ 2 / L ^ 2) := by
    have : t ^ 2 ≤ (ℓ / L) ^ 2 := by rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) htb 2
    calc 2 * t ^ 2 ≤ 2 * (ℓ / L) ^ 2 := by linarith
      _ = 2 * (ℓ ^ 2 / L ^ 2) := by rw [div_pow]
  have hℓℓ : ℓ / L ^ 2 ≤ ℓ ^ 2 / L ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
  have hRL : R / L ≤ R := by rw [div_le_iff₀ hL0]; nlinarith
  rw [hlog]
  have e : ℓ + Real.log (1 + t) - ℓ - (C - ℓ / 2) / L =
      (Real.log (1 + t) - t) + (t - (C - ℓ / 2) / L) := by ring
  rw [e]
  calc _ ≤ |Real.log (1 + t) - t| + |t - (C - ℓ / 2) / L| := abs_add_le _ _
    _ ≤ 2 * t ^ 2 + (ℓ / L ^ 2 + R / L) := add_le_add h1 h2
    _ ≤ 3 * ℓ ^ 2 / L ^ 2 + R := by
        have : 2 * (ℓ ^ 2 / L ^ 2) + ℓ ^ 2 / L ^ 2 = 3 * ℓ ^ 2 / L ^ 2 := by ring
        linarith

/-- The main terms of the periodic expansion. -/
noncomputable def perMain (N : ℕ) : ℝ :=
  Real.log N - Real.log (Real.log N) / 2 + cP +
    (Real.log (Real.log N) / 4 - cP / 2 + 3 / 8) / Real.log N

/-- **Theorem 5.2, `eq:periodicasym`.** There is `C` with, eventually,
`|N u_N^P - (L - (1/2) log L + c_P + ((1/4) log L - c_P/2 + 3/8)/L)| ≤ C (log L)²/L²`. -/
theorem periodic_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |(N : ℝ) * uNP N - perMain N| ≤ C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by
  obtain ⟨CK, hCK, hinv⟩ := log_inversion (K := 1) one_pos
  refine ⟨121 * CK, by positivity, ?_⟩
  filter_upwards [periodic_crossing_eq, uNP_first_order,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 240]
    with N heq hfo hL240
  obtain ⟨ω, hω, hωb⟩ := heq
  set L := Real.log (N : ℝ) with hLdef
  have hL : (240 : ℝ) ≤ L := hL240
  have hL0 : 0 < L := by linarith
  set ℓ := Real.log L with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le hL0]
    have := Real.exp_one_lt_d9; linarith
  obtain ⟨hzlo, -⟩ := hfo
  have hz1 : 1 ≤ (N : ℝ) * uNP N := by linarith
  have hcP := cP_bounds
  have hω1 : |ω| ≤ 1 := by
    have : 120 / L ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  have h := hinv ((N : ℝ) * uNP N) L cP (3 / 8) ω hz1 (by linarith)
    (by rw [abs_le]; constructor <;> linarith) (by norm_num [abs_of_pos]) hω1 hω
  have hωℓ : |ω| ≤ 120 * (ℓ ^ 2 / L ^ 2) := by
    have : 120 / L ^ 2 ≤ 120 * (ℓ ^ 2 / L ^ 2) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      have : 1 ≤ ℓ ^ 2 := by nlinarith
      nlinarith [sq_nonneg L]
    linarith
  have e : (N : ℝ) * uNP N - perMain N =
      (N : ℝ) * uNP N - L + ℓ / 2 - cP - (ℓ / 4 - cP / 2 + 3 / 8) / L := by
    unfold perMain; rw [← hLdef, ← hℓ]; ring
  rw [e]
  have hnn : 0 ≤ ℓ ^ 2 / L ^ 2 := by positivity
  calc _ ≤ CK * (ℓ ^ 2 / L ^ 2 + |ω|) := h
    _ ≤ CK * (ℓ ^ 2 / L ^ 2 + 120 * (ℓ ^ 2 / L ^ 2)) := by gcongr
    _ = 121 * CK * (ℓ ^ 2 / L ^ 2) := by ring

/-- **Theorem 5.2**, the same expansion for `N(1 - p_N^P)`. -/
theorem periodic_expansion_prob :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |(N : ℝ) * (1 - pNP N) - perMain N| ≤ C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by
  obtain ⟨C, hC, hev⟩ := periodic_expansion
  refine ⟨C + 1, by positivity, ?_⟩
  filter_upwards [hev, uNP_first_order, eventually_log_pow_le 4 (c := 1 / 9) (by norm_num),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 240,
    eventually_ge_atTop 2] with N h hfo hL4 hL240 hN2
  set L := Real.log (N : ℝ) with hLdef
  have hL : (240 : ℝ) ≤ L := hL240
  have hL0 : 0 < L := by linarith
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set ℓ := Real.log L with hℓ
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ, Real.le_log_iff_exp_le hL0]; have := Real.exp_one_lt_d9; linarith
  have hu := uNP_pos hN2
  obtain ⟨-, hzhi⟩ := hfo
  -- `N u - N(1-p) = N u²/(1+u) ≤ (Nu)²/N`
  have hdiff : |(N : ℝ) * (1 - pNP N) - (N : ℝ) * uNP N| ≤ ℓ ^ 2 / L ^ 2 := by
    have e : (N : ℝ) * (1 - pNP N) - (N : ℝ) * uNP N = -((N : ℝ) * uNP N ^ 2 / (1 + uNP N)) := by
      unfold pNP; field_simp; ring
    rw [e, abs_neg, abs_of_nonneg (by positivity)]
    have h1 : (N : ℝ) * uNP N ^ 2 / (1 + uNP N) ≤ (N : ℝ) * uNP N ^ 2 :=
      div_le_self (by positivity) (by linarith)
    have h2 : (N : ℝ) * uNP N ^ 2 = ((N : ℝ) * uNP N) ^ 2 / N := by field_simp
    have h3 : ((N : ℝ) * uNP N) ^ 2 ≤ 9 * L ^ 2 := by
      calc ((N : ℝ) * uNP N) ^ 2 ≤ (3 * L) ^ 2 := pow_le_pow_left₀ (by positivity) hzhi 2
        _ = 9 * L ^ 2 := by ring
    have h4 : 9 * L ^ 2 / N ≤ ℓ ^ 2 / L ^ 2 := by
      rw [div_le_div_iff₀ hNp (by positivity)]
      have : 1 ≤ ℓ ^ 2 := by nlinarith
      have h5 : 9 * L ^ 4 ≤ (N : ℝ) := by linarith
      nlinarith
    calc _ ≤ (N : ℝ) * uNP N ^ 2 := h1
      _ = ((N : ℝ) * uNP N) ^ 2 / N := h2
      _ ≤ 9 * L ^ 2 / N := div_le_div_of_nonneg_right h3 hNp.le
      _ ≤ ℓ ^ 2 / L ^ 2 := h4
  have e : (N : ℝ) * (1 - pNP N) - perMain N =
      ((N : ℝ) * (1 - pNP N) - (N : ℝ) * uNP N) + ((N : ℝ) * uNP N - perMain N) := by ring
  rw [e]
  calc _ ≤ |(N : ℝ) * (1 - pNP N) - (N : ℝ) * uNP N| + |(N : ℝ) * uNP N - perMain N| :=
        abs_add_le _ _
    _ ≤ ℓ ^ 2 / L ^ 2 + C * (ℓ ^ 2 / L ^ 2) := add_le_add hdiff h
    _ = (C + 1) * (ℓ ^ 2 / L ^ 2) := by ring

/-- The main terms of the free expansion (Corollary 3.7(c)). -/
noncomputable def freeMain (N : ℕ) : ℝ :=
  nuN N + (Real.log (Real.log N) / 4 - Real.log (Real.pi / 8) / 4 + 1 / 8) / Real.log N

/-- The free expansion, transferred to `N u_N`. -/
theorem free_expansion_uN :
    ∀ᶠ N : ℕ in atTop,
      |(N : ℝ) * uN N - freeMain N| ≤ 53 * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by
  filter_upwards [eventually_ge_atTop 21, eventually_log_pow_le 4 (c := 1 / 100) (by norm_num),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 240]
    with N hN hL4 hL240
  set L := Real.log (N : ℝ) with hLdef
  have hL : (240 : ℝ) ≤ L := hL240
  have hL0 : 0 < L := by linarith
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set ℓ := Real.log L with hℓ
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ, Real.le_log_iff_exp_le hL0]; have := Real.exp_one_lt_d9; linarith
  have hc := every_N_corollary_c_bound N hN
  obtain ⟨hd0, hd1⟩ := N_uN_sub_zN N (by omega)
  have hsmall : 2 * (L + 1 / 4) ^ 2 / N ≤ ℓ ^ 2 / L ^ 2 := by
    rw [div_le_div_iff₀ hNp (by positivity)]
    have : 1 ≤ ℓ ^ 2 := by nlinarith
    have h1 : 2 * (L + 1 / 4) ^ 2 ≤ 3 * L ^ 2 := by nlinarith
    have h2 : 3 * L ^ 2 * L ^ 2 ≤ (N : ℝ) := by nlinarith
    nlinarith
  have e : (N : ℝ) * uN N - freeMain N =
      ((N : ℝ) * uN N - (N : ℝ) * (1 - pN N)) +
      ((N : ℝ) * (1 - pN N) - nuN N -
        (ℓ / 4 - Real.log (Real.pi / 8) / 4 + 1 / 8) / L) := by
    unfold freeMain; rw [← hLdef, ← hℓ]; ring
  rw [e]
  have hd : |(N : ℝ) * uN N - (N : ℝ) * (1 - pN N)| ≤ ℓ ^ 2 / L ^ 2 := by
    rw [abs_of_nonneg hd0]; linarith
  have hc' : 52 * ℓ ^ 2 / L ^ 2 = 52 * (ℓ ^ 2 / L ^ 2) := by ring
  rw [hc'] at hc
  calc _ ≤ |(N : ℝ) * uN N - (N : ℝ) * (1 - pN N)| + |(N : ℝ) * (1 - pN N) - nuN N -
        (ℓ / 4 - Real.log (Real.pi / 8) / 4 + 1 / 8) / L| := abs_add_le _ _
    _ ≤ ℓ ^ 2 / L ^ 2 + 52 * (ℓ ^ 2 / L ^ 2) := add_le_add hd hc
    _ = 53 * (ℓ ^ 2 / L ^ 2) := by ring

theorem log_pi_div_two_sub : Real.log (Real.pi / 2) - Real.log (Real.pi / 8) = 2 * Real.log 2 := by
  rw [Real.log_div Real.pi_pos.ne' (by norm_num), Real.log_div Real.pi_pos.ne' (by norm_num),
    show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  ring

/-- **Theorem 5.2, `eq:boundaryshift`.** Eventually
`|N(u_N^P - u_N^F) - (log 2 + (1/4 - (1/2) log 2)/L)| ≤ C (log L)²/L²`. -/
theorem boundary_shift :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |(N : ℝ) * (uNP N - uN N) - (Real.log 2 + (1 / 4 - Real.log 2 / 2) / Real.log N)| ≤
        C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by
  obtain ⟨C, hC, hev⟩ := periodic_expansion
  refine ⟨C + 53, by positivity, ?_⟩
  filter_upwards [hev, free_expansion_uN,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 240]
    with N hP hF hL240
  set L := Real.log (N : ℝ) with hLdef
  have hL0 : 0 < L := by have : (240 : ℝ) ≤ L := hL240; linarith
  set ℓ := Real.log L with hℓ
  have e : (N : ℝ) * (uNP N - uN N) - (Real.log 2 + (1 / 4 - Real.log 2 / 2) / L) =
      ((N : ℝ) * uNP N - perMain N) - ((N : ℝ) * uN N - freeMain N) := by
    unfold perMain freeMain nuN cP; rw [← hLdef, ← hℓ]
    have h := log_pi_div_two_sub
    linear_combination (1 / 2 - 1 / (4 * L)) * h
  rw [e]
  calc _ ≤ |(N : ℝ) * uNP N - perMain N| + |(N : ℝ) * uN N - freeMain N| := abs_sub _ _
    _ ≤ C * (ℓ ^ 2 / L ^ 2) + 53 * (ℓ ^ 2 / L ^ 2) := add_le_add hP hF
    _ = (C + 53) * (ℓ ^ 2 / L ^ 2) := by ring

/-- Eventually `(log log N)²/(log N)² ≤ ε`. -/
theorem eventually_loglog_ratio_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log (Real.log N) ^ 2 / Real.log N ^ 2 ≤ ε := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound hε
  have h2 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually h
  filter_upwards [h2, (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 3]
    with N hN hL3
  simp only [Function.comp, id, Real.norm_eq_abs] at hN hL3
  set L := Real.log (N : ℝ)
  have hL0 : 0 < L := by linarith
  have hl : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  rw [abs_of_nonneg (pow_nonneg hl 2), abs_of_pos hL0] at hN
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The coupling at a crossing from the expansion of `N u`. -/
theorem coupling_of_expansion {N : ℕ} {u C β R : ℝ} (hN : 0 < (N : ℝ)) (hu : 0 < u)
    (hL : 240 ≤ Real.log N) (hC : |C| ≤ 1) (hβ : |β| ≤ 1) (hR0 : 0 ≤ R) (hR : R ≤ 1)
    (hz : |(N : ℝ) * u - (Real.log N - Real.log (Real.log N) / 2 + C +
      (Real.log (Real.log N) / 4 - C / 2 + β) / Real.log N)| ≤ R) :
    |-Real.log u / 2 - (Real.log N / 2 - Real.log (Real.log N) / 2 +
      (Real.log (Real.log N) / 4 - C / 2) / Real.log N)| ≤
      (3 * Real.log (Real.log N) ^ 2 / Real.log N ^ 2 + R) / 2 := by
  have h := log_of_expansion hL hC hβ hR0 hR hz
  have hlog : Real.log u = Real.log ((N : ℝ) * u) - Real.log N := by
    rw [Real.log_mul hN.ne' hu.ne']; ring
  have e : -Real.log u / 2 - (Real.log N / 2 - Real.log (Real.log N) / 2 +
      (Real.log (Real.log N) / 4 - C / 2) / Real.log N) =
      -(Real.log ((N : ℝ) * u) - Real.log (Real.log N) -
        (C - Real.log (Real.log N) / 2) / Real.log N) / 2 := by
    rw [hlog]; ring
  rw [e, abs_div, abs_neg, abs_two]
  linarith

/-- **Theorem 5.2, `eq:isingtemperature`.** The coupling `J_N^P = -(1/2) log u_N^P`. -/
theorem periodic_coupling :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |-Real.log (uNP N) / 2 - (Real.log N / 2 - Real.log (Real.log N) / 2 +
        (Real.log (Real.log N) / 4 - cP / 2) / Real.log N)| ≤
        C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by
  obtain ⟨C, hC, hev⟩ := periodic_expansion
  refine ⟨(3 + C) / 2, by positivity, ?_⟩
  filter_upwards [hev, eventually_loglog_ratio_le (ε := 1 / C) (by positivity),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 240,
    eventually_ge_atTop 2] with N h hsm hL240 hN2
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcP := cP_bounds
  have hR : C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hsm hC.le
    rwa [mul_one_div_cancel hC.ne'] at this
  have h' := coupling_of_expansion (C := cP) (β := 3 / 8) hNp (uNP_pos hN2) hL240
    (by rw [abs_le]; constructor <;> linarith) (by norm_num [abs_of_pos]) (by positivity) hR
    (by unfold perMain at h; exact h)
  calc _ ≤ (3 * Real.log (Real.log N) ^ 2 / Real.log N ^ 2 +
        C * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2)) / 2 := h'
    _ = (3 + C) / 2 * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by ring

/-- **Corollary 5.5(a).** The free coupling `J_N^F = -(1/2) log u_N`. -/
theorem free_coupling :
    ∀ᶠ N : ℕ in atTop,
      |-Real.log (uN N) / 2 - (Real.log N / 2 - Real.log (Real.log N) / 2 +
        (Real.log (Real.log N) / 4 - Real.log (Real.pi / 8) / 2 / 2) / Real.log N)| ≤
        28 * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by
  filter_upwards [free_expansion_uN, eventually_loglog_ratio_le (ε := 1 / 53) (by norm_num),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 240,
    eventually_ge_atTop 2] with N h hsm hL240 hN2
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hc0lo, hc0hi⟩ := c0_bounds
  have hR : 53 * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) ≤ 1 := by linarith
  have hu : 0 < uN N := uab_pos (by omega) (by omega)
  have h' := coupling_of_expansion (C := Real.log (Real.pi / 8) / 2) (β := 1 / 8) hNp hu hL240
    (by rw [abs_le]; constructor <;> linarith) (by norm_num [abs_of_pos]) (by positivity) hR
    (by
      have e : freeMain N = Real.log N - Real.log (Real.log N) / 2 + Real.log (Real.pi / 8) / 2 +
          (Real.log (Real.log N) / 4 - Real.log (Real.pi / 8) / 2 / 2 + 1 / 8) / Real.log N := by
        unfold freeMain nuN; ring
      rw [← e]; exact h)
  calc _ ≤ (3 * Real.log (Real.log N) ^ 2 / Real.log N ^ 2 +
        53 * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2)) / 2 := h'
    _ = 28 * (Real.log (Real.log N) ^ 2 / Real.log N ^ 2) := by ring


/-- Eventually `(log log N)² ≤ ε log N`. -/
theorem eventually_ell_sq_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log (Real.log N) ^ 2 ≤ ε * Real.log N := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound hε
  have h2 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually h
  filter_upwards [h2, (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 3]
    with N hN hL3
  simp only [Function.comp, id, Real.norm_eq_abs] at hN hL3
  have hl : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  rwa [abs_of_nonneg (pow_nonneg hl 2), abs_of_pos (by linarith)] at hN

/-- `log L ≥ 5` for `L ≥ 240`. -/
theorem five_le_log_of {L : ℝ} (hL : 240 ≤ L) : 5 ≤ Real.log L := by
  have hL0 : 0 < L := by linarith
  rw [Real.le_log_iff_exp_le hL0]
  have he := Real.exp_one_lt_d9
  have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h5]
  have : Real.exp 1 ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 5
  have : (2.7182818286 : ℝ) ^ 5 ≤ 240 := by norm_num
  linarith

/-- `|freeMain N - log N| ≤ (log log N)/2 + 1` for `log N ≥ 240`. -/
theorem freeMain_near {N : ℕ} (hL : 240 ≤ Real.log N) :
    |freeMain N - Real.log N| ≤ Real.log (Real.log N) / 2 + 1 := by
  set L := Real.log (N : ℝ) with hLdef
  have hL0 : 0 < L := by linarith
  set ℓ := Real.log L with hℓ
  have hℓ5 : 5 ≤ ℓ := five_le_log_of hL
  have hℓL : ℓ ≤ L / 4 := log_le_quarter (by linarith)
  obtain ⟨hc0lo, hc0hi⟩ := c0_bounds
  unfold freeMain nuN; rw [← hLdef, ← hℓ]
  have hfr : |(ℓ / 4 - Real.log (Real.pi / 8) / 4 + 1 / 8) / L| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0, abs_le]; constructor <;> linarith
  have e : L - ℓ / 2 + Real.log (Real.pi / 8) / 2 +
      (ℓ / 4 - Real.log (Real.pi / 8) / 4 + 1 / 8) / L - L =
      (-(ℓ / 2) + Real.log (Real.pi / 8) / 2) + (ℓ / 4 - Real.log (Real.pi / 8) / 4 + 1 / 8) / L := by
    ring
  rw [e]
  have h2 : |-(ℓ / 2) + Real.log (Real.pi / 8) / 2| ≤ ℓ / 2 + 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  calc _ ≤ |-(ℓ / 2) + Real.log (Real.pi / 8) / 2| +
        |(ℓ / 4 - Real.log (Real.pi / 8) / 4 + 1 / 8) / L| := abs_add_le _ _
    _ ≤ (ℓ / 2 + 1 / 2) + 1 / 2 := add_le_add h2 hfr
    _ = ℓ / 2 + 1 := by ring

/-- The last step of Corollary 5.5(b): from `t ≈ log 2/L` to the coupling difference. -/
theorem shift_final {L ℓ b t : ℝ} (hL : 240 ≤ L) (hℓ5 : 5 ≤ ℓ) (hb0 : 3 * L / 4 ≤ b)
    (ht1 : |Real.log (1 + t) - t| ≤ 2 * t ^ 2) (ht2 : 2 * t ^ 2 ≤ 2 * (1 / b) ^ 2)
    (htl : |t - Real.log 2 / L| ≤ (1 + ℓ) / (b * L)) :
    |Real.log (1 + t) / 2 - Real.log 2 / (2 * L)| ≤ 2 * ℓ / L ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hbp : 0 < b := by linarith
  have e : (Real.log (1 + t)) / 2 - Real.log 2 / (2 * L) =
      ((Real.log (1 + t) - t) + (t - Real.log 2 / L)) / 2 := by field_simp; ring
  rw [e, abs_div, abs_two]
  have hsum : |(Real.log (1 + t) - t) + (t - Real.log 2 / L)| ≤
      2 * (1 / b) ^ 2 + (1 + ℓ) / (b * L) :=
    (abs_add_le _ _).trans (add_le_add (ht1.trans ht2) htl)
  have hq1 : 2 * (1 / b) ^ 2 ≤ 4 / L ^ 2 := by
    have : (1 / b) ^ 2 ≤ (4 / (3 * L)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_div_iff₀ hbp (by positivity)]; linarith
    have e2 : (4 / (3 * L)) ^ 2 = 16 / 9 / L ^ 2 := by field_simp; ring
    rw [e2] at this
    have : 2 * (16 / 9 / L ^ 2) ≤ 4 / L ^ 2 := by
      rw [show 2 * (16 / 9 / L ^ 2) = (32 / 9) / L ^ 2 by ring]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith
  have hq2 : (1 + ℓ) / (b * L) ≤ (1 + ℓ) * 4 / (3 * L ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 := mul_le_mul_of_nonneg_right hb0 hL0.le
    have : 3 * L ^ 2 ≤ 4 * (b * L) := by
      have e : 3 * L / 4 * L = 3 * L ^ 2 / 4 := by ring
      linarith
    have h3 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 1 + ℓ)
    linarith
  have hfin : (4 / L ^ 2 + (1 + ℓ) * 4 / (3 * L ^ 2)) / 2 ≤ 2 * ℓ / L ^ 2 := by
    have e2 : (4 / L ^ 2 + (1 + ℓ) * 4 / (3 * L ^ 2)) / 2 = (8 / 3 + 2 / 3 * ℓ) / L ^ 2 := by
      field_simp; ring
    rw [e2]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

/-- **Corollary 5.5(b).** `J_N^F - J_N^P = (log 2)/(2 log N) + O(log log N/(log N)²)`,
as the explicit bound `2 (log log N)/(log N)²` for all large `N`. -/
theorem coupling_shift :
    ∀ᶠ N : ℕ in atTop,
      |(-Real.log (uN N) / 2) - (-Real.log (uNP N) / 2) - Real.log 2 / (2 * Real.log N)| ≤
        2 * Real.log (Real.log N) / Real.log N ^ 2 := by
  obtain ⟨C, hC, hev⟩ := boundary_shift
  filter_upwards [hev, free_expansion_uN, eventually_ell_sq_le (ε := 1 / (2 * C)) (by positivity),
    eventually_loglog_ratio_le (ε := 1 / 53) (by norm_num),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 240,
    eventually_ge_atTop 2] with N hsh hF hsq hsm hL240 hN2
  set L := Real.log (N : ℝ) with hLdef
  have hL : (240 : ℝ) ≤ L := hL240
  have hL0 : 0 < L := by linarith
  set ℓ := Real.log L with hℓ
  have hℓ5 : 5 ≤ ℓ := five_le_log_of hL
  have hℓL : ℓ ≤ L / 4 := log_le_quarter (by linarith)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hu := uab_pos (a := N / 2) (b := N - N / 2) (by omega) (by omega)
  have hup := uNP_pos hN2
  set a := (N : ℝ) * uNP N with ha
  set b := (N : ℝ) * uN N with hb
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  -- step 1: `|a - b - log 2| ≤ 1/L`
  have hCr : C * (ℓ ^ 2 / L ^ 2) ≤ 1 / (2 * L) := by
    have h1 : C * ℓ ^ 2 ≤ L / 2 := by
      have := mul_le_mul_of_nonneg_left hsq hC.le
      have e : C * (1 / (2 * C) * L) = L / 2 := by field_simp
      linarith
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hd : |a - b - Real.log 2| ≤ 1 / L := by
    have e : a - b - Real.log 2 = ((N : ℝ) * (uNP N - uN N) -
        (Real.log 2 + (1 / 4 - Real.log 2 / 2) / L)) + (1 / 4 - Real.log 2 / 2) / L := by
      rw [ha, hb]; ring
    rw [e]
    have h2 : |(1 / 4 - Real.log 2 / 2) / L| ≤ 1 / (2 * L) := by
      rw [abs_div, abs_of_pos hL0, div_le_div_iff₀ hL0 (by positivity)]
      have : |1 / 4 - Real.log 2 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg (1 / 4 - Real.log 2 / 2)]
    have h3 : 1 / (2 * L) + 1 / (2 * L) = 1 / L := by field_simp; ring
    calc _ ≤ |(N : ℝ) * (uNP N - uN N) - (Real.log 2 + (1 / 4 - Real.log 2 / 2) / L)| +
          |(1 / 4 - Real.log 2 / 2) / L| := abs_add_le _ _
      _ ≤ 1 / (2 * L) + 1 / (2 * L) := add_le_add (hsh.trans hCr) h2
      _ = 1 / L := h3
  -- step 2: `|b - L| ≤ ℓ`
  have hbL : |b - L| ≤ ℓ := by
    have hFr : 53 * (ℓ ^ 2 / L ^ 2) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hsm (by norm_num : (0 : ℝ) ≤ 53)
      have e : (53 : ℝ) * (1 / 53) = 1 := by norm_num
      linarith
    have hfm := freeMain_near (N := N) hL240
    have e : b - L = (b - freeMain N) + (freeMain N - L) := by ring
    rw [e]
    calc _ ≤ |b - freeMain N| + |freeMain N - L| := abs_add_le _ _
      _ ≤ 1 + (ℓ / 2 + 1) := add_le_add (hF.trans hFr) hfm
      _ ≤ ℓ := by linarith
  have hbLa := abs_le.mp hbL
  have hb0 : 3 * L / 4 ≤ b := by linarith
  have hbp : 0 < b := by linarith
  have hda := abs_le.mp hd
  have hL1 : 1 / L ≤ 1 / 240 := by rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  -- step 3: `t = (a - b)/b`
  have hab1 : |a - b| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have htb' : |(a - b) / b| ≤ 1 / b := by
    rw [abs_div, abs_of_pos hbp]; exact div_le_div_of_nonneg_right hab1 hbp.le
  have h1b : 1 / b ≤ 1 / 4 := by rw [div_le_div_iff₀ hbp (by norm_num)]; linarith
  set t := (a - b) / b with ht
  have hthalf : |t| ≤ 1 / 2 := by linarith
  have hapos : 0 < a := by
    have e : a = b * (1 + t) := by rw [ht]; field_simp; ring
    have := abs_le.mp hthalf
    rw [e]; apply mul_pos hbp; linarith
  have hlogab : Real.log a - Real.log b = Real.log (1 + t) := by
    rw [← Real.log_div hapos.ne' hbp.ne']
    congr 1; rw [ht]; field_simp; ring
  have hJ : (-Real.log (uN N) / 2) - (-Real.log (uNP N) / 2) = (Real.log a - Real.log b) / 2 := by
    have h1 : Real.log a = Real.log N + Real.log (uNP N) := Real.log_mul hNp.ne' hup.ne'
    have h2 : Real.log b = Real.log N + Real.log (uN N) := Real.log_mul hNp.ne' hu.ne'
    rw [h1, h2]; ring
  have ht1 := abs_log_one_add_sub_le hthalf
  have htl : |t - Real.log 2 / L| ≤ (1 + ℓ) / (b * L) := by
    have e : t - Real.log 2 / L = ((a - b - Real.log 2) * L - (b - L) * Real.log 2) / (b * L) := by
      rw [ht]; field_simp; ring
    rw [e, abs_div, abs_of_pos (by positivity : 0 < b * L)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc |(a - b - Real.log 2) * L - (b - L) * Real.log 2|
        ≤ |(a - b - Real.log 2) * L| + |(b - L) * Real.log 2| := abs_sub _ _
      _ = |a - b - Real.log 2| * L + |b - L| * Real.log 2 := by
          rw [abs_mul, abs_mul, abs_of_pos hL0, abs_of_pos hl2p]
      _ ≤ 1 / L * L + ℓ * 1 := by
          apply add_le_add (mul_le_mul_of_nonneg_right hd hL0.le)
          exact mul_le_mul hbL (by linarith) hl2p.le (by linarith)
      _ = 1 + ℓ := by field_simp
  have ht2 : 2 * t ^ 2 ≤ 2 * (1 / b) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg t) htb' 2
    rw [sq_abs] at this; linarith
  rw [hJ, hlogab]
  exact shift_final hL hℓ5 hb0 ht1 ht2 htl

/-- The correlation length `ξ(J) = -1/log tanh J` of the infinite zero-field chain. -/
noncomputable def corrLen (J : ℝ) : ℝ := -1 / Real.log (Real.tanh J)

theorem tanh_neg_half_log {u : ℝ} (hu : 0 < u) :
    Real.tanh (-Real.log u / 2) = (1 - u) / (1 + u) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  set r := Real.exp (-Real.log u / 2) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr2 : r ^ 2 = u⁻¹ := by
    rw [hr, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-Real.log u / 2) = -Real.log u by
      push_cast; ring, Real.exp_neg, Real.exp_log hu]
  have hneg : Real.exp (-(-Real.log u / 2)) = r⁻¹ := by rw [hr, Real.exp_neg]
  rw [hneg]
  have hu' : u = (r ^ 2)⁻¹ := by rw [hr2, inv_inv]
  rw [hu']
  field_simp

/-- `N/ξ(J) = N log((1+u)/(1-u))` at `J = -(1/2) log u`, for `0 < u < 1`. -/
theorem N_div_corrLen {u : ℝ} (hu : 0 < u) (N : ℝ) :
    N / corrLen (-Real.log u / 2) = N * Real.log ((1 + u) / (1 - u)) := by
  unfold corrLen
  rw [tanh_neg_half_log hu]
  have hlog : Real.log ((1 - u) / (1 + u)) = -Real.log ((1 + u) / (1 - u)) := by
    rw [← Real.log_inv, inv_div]
  rw [hlog]
  field_simp

/-- `|log((1+u)/(1-u)) - 2u| ≤ u³` for `0 ≤ u ≤ 1/2`. -/
theorem log_ratio_sub_two {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    |Real.log ((1 + u) / (1 - u)) - 2 * u| ≤ u ^ 3 := by
  have h1 : |u| < 1 := by rw [abs_of_nonneg hu0]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one h1
  rw [Real.log_div (by linarith) (by linarith)]
  set f := fun k : ℕ => 2 * (1 / (2 * (k : ℝ) + 1)) * u ^ (2 * k + 1) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => by rw [hf]; positivity
  have htail : HasSum (fun k => f (k + 1)) (Real.log (1 + u) - Real.log (1 - u) - f 0) := by
    have h := (hasSum_nat_add_iff' 1).mpr hs
    simpa [Finset.range_one, Finset.sum_singleton] using h
  have hf00 : f 0 = 2 * u := by rw [hf]; simp
  rw [hf00] at htail
  have hg : HasSum (fun k : ℕ => 2 / 3 * u ^ 3 * (u ^ 2) ^ k) (2 / 3 * u ^ 3 * (1 - u ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
  have hle : ∀ k, f (k + 1) ≤ 2 / 3 * u ^ 3 * (u ^ 2) ^ k := by
    intro k
    rw [hf]
    simp only
    have hk : (1 : ℝ) / (2 * ((k + 1 : ℕ) : ℝ) + 1) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; push_cast; nlinarith
    have hp : u ^ (2 * (k + 1) + 1) = u ^ 3 * (u ^ 2) ^ k := by rw [← pow_mul]; ring
    rw [hp]
    have : 0 ≤ u ^ 3 * (u ^ 2) ^ k := by positivity
    nlinarith
  have hS := hasSum_le hle htail hg
  have hS0 : 0 ≤ Real.log (1 + u) - Real.log (1 - u) - 2 * u :=
    htail.nonneg (fun k => hf0 (k + 1))
  rw [abs_of_nonneg hS0]
  have hden : 2 / 3 * u ^ 3 * (1 - u ^ 2)⁻¹ ≤ u ^ 3 := by
    have h34 : 3 / 4 ≤ 1 - u ^ 2 := by nlinarith
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg hu0 3]
  linarith

/-- `N/ξ` from the expansion of `N u`: if `0 < u ≤ 1/2`, `|N u - (L - ℓ/2 + C)| ≤ R`, then
`|N/ξ(J) - (2L - ℓ + 2C)| ≤ 2R + (N u)³/N²` at `J = -(1/2) log u`. -/
theorem corrLen_of_expansion {N : ℕ} {u C R : ℝ} (hN : 0 < (N : ℝ)) (hu : 0 < u) (hu1 : u ≤ 1 / 2)
    (hz : |(N : ℝ) * u - (Real.log N - Real.log (Real.log N) / 2 + C)| ≤ R) :
    |(N : ℝ) / corrLen (-Real.log u / 2) - (2 * Real.log N - Real.log (Real.log N) + 2 * C)| ≤
      2 * R + ((N : ℝ) * u) ^ 3 / (N : ℝ) ^ 2 := by
  rw [N_div_corrLen hu]
  have h := log_ratio_sub_two hu.le hu1
  have e : (N : ℝ) * Real.log ((1 + u) / (1 - u)) -
      (2 * Real.log N - Real.log (Real.log N) + 2 * C) =
      (N : ℝ) * (Real.log ((1 + u) / (1 - u)) - 2 * u) +
        2 * ((N : ℝ) * u - (Real.log N - Real.log (Real.log N) / 2 + C)) := by ring
  rw [e]
  have h1 : |(N : ℝ) * (Real.log ((1 + u) / (1 - u)) - 2 * u)| ≤ ((N : ℝ) * u) ^ 3 / (N : ℝ) ^ 2 := by
    rw [abs_mul, abs_of_pos hN]
    calc (N : ℝ) * |Real.log ((1 + u) / (1 - u)) - 2 * u| ≤ (N : ℝ) * u ^ 3 :=
          mul_le_mul_of_nonneg_left h hN.le
      _ = ((N : ℝ) * u) ^ 3 / (N : ℝ) ^ 2 := by field_simp
  calc _ ≤ |(N : ℝ) * (Real.log ((1 + u) / (1 - u)) - 2 * u)| +
        |2 * ((N : ℝ) * u - (Real.log N - Real.log (Real.log N) / 2 + C))| := abs_add_le _ _
    _ ≤ ((N : ℝ) * u) ^ 3 / (N : ℝ) ^ 2 + 2 * R := by
        have h2 : |2 * ((N : ℝ) * u - (Real.log N - Real.log (Real.log N) / 2 + C))| =
            2 * |(N : ℝ) * u - (Real.log N - Real.log (Real.log N) / 2 + C)| := by
          rw [abs_mul, abs_two]
        rw [h2]; linarith
    _ = 2 * R + ((N : ℝ) * u) ^ 3 / (N : ℝ) ^ 2 := by ring

/-- `(Nu)³/N² ≤ ℓ/L` when `0 ≤ Nu ≤ kL`, `k ≤ 3`, `L ≥ 240` and `L³ ≤ N`. -/
theorem cubic_small {N L z k : ℝ} (hN : 0 < N) (hL : 240 ≤ L) (hL3 : L ^ 3 ≤ 1 * N)
    (hz0 : 0 ≤ z) (hz : z ≤ k * L) (hk : k ≤ 3) :
    z ^ 3 / N ^ 2 ≤ Real.log L / L := by
  have hL0 : 0 < L := by linarith
  have hℓ : 5 ≤ Real.log L := five_le_log_of hL
  have hz3 : z ^ 3 ≤ 27 * L ^ 3 := by
    have h1 : z ≤ 3 * L := by
      have := mul_le_mul_of_nonneg_right hk hL0.le
      linarith
    have := pow_le_pow_left₀ hz0 h1 3
    calc z ^ 3 ≤ (3 * L) ^ 3 := this
      _ = 27 * L ^ 3 := by ring
  have hNL : L ^ 3 ≤ N := by linarith
  have h27 : 27 * L ≤ L ^ 3 := by
    have hL2 : 27 ≤ L ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right hL2 hL0.le
    have e : L ^ 2 * L = L ^ 3 := by ring
    linarith
  rw [div_le_div_iff₀ (by positivity) hL0]
  have h1 : z ^ 3 * L ≤ 27 * L ^ 3 * L := mul_le_mul_of_nonneg_right hz3 hL0.le
  have h2 : 27 * L ^ 3 * L = 27 * L * L ^ 3 := by ring
  have h3 : 27 * L * L ^ 3 ≤ N * N := by
    have h5 := mul_le_mul h27 hNL (by positivity) (by positivity)
    have h6 := mul_le_mul_of_nonneg_right hNL hN.le
    linarith
  have h4 : N * N ≤ Real.log L * N ^ 2 := by nlinarith
  linarith

/-- **Corollary 5.5(c), free ends.**
`N/ξ(J_N^F) = 2 log N - log log N + log(π/8) + O(log log N/log N)`. -/
theorem corrLen_free :
    ∀ᶠ N : ℕ in atTop,
      |(N : ℝ) / corrLen (-Real.log (uN N) / 2) -
        (2 * Real.log N - Real.log (Real.log N) + Real.log (Real.pi / 8))| ≤
        4 * (Real.log (Real.log N) / Real.log N) := by
  filter_upwards [free_expansion_uN, eventually_ell_sq_le (ε := 1 / 53) (by norm_num),
    eventually_log_pow_le 3 (c := 1) (by norm_num),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 240,
    eventually_ge_atTop 2] with N hF hsm hL3 hL240 hN2
  set L := Real.log (N : ℝ) with hLdef
  have hL : (240 : ℝ) ≤ L := hL240
  have hL0 : 0 < L := by linarith
  set ℓ := Real.log L with hℓ
  have hℓ5 : 5 ≤ ℓ := five_le_log_of hL
  have hℓL : ℓ ≤ L / 4 := log_le_quarter (by linarith)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hu := uab_pos (a := N / 2) (b := N - N / 2) (by omega) (by omega)
  have hu2 : uN N ≤ 1 / 2 := (uab_spec (a := N / 2) (b := N - N / 2) (by omega) (by omega)).2.1
  obtain ⟨hc0lo, hc0hi⟩ := c0_bounds
  -- `|N u_N - (L - ℓ/2 + c₀)| ≤ 53 ℓ²/L² + (ℓ/4 + 1)/L ≤ ℓ/L + 1/L`
  have hfr : |(ℓ / 4 - Real.log (Real.pi / 8) / 4 + 1 / 8) / L| ≤ (ℓ / 4 + 1) / L := by
    rw [abs_div, abs_of_pos hL0]
    apply div_le_div_of_nonneg_right _ hL0.le
    rw [abs_le]; constructor <;> linarith
  have hℓL4 : ℓ / L ≤ 1 / 4 := by rw [div_le_iff₀ hL0]; linarith
  have hsq : 53 * (ℓ ^ 2 / L ^ 2) ≤ ℓ / L := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hL0]
    have h1 : 53 * ℓ ^ 2 ≤ L := by linarith
    have h2 : 53 * ℓ ^ 2 * L ≤ L * L := mul_le_mul_of_nonneg_right h1 hL0.le
    have h3 : L * L ≤ ℓ * L ^ 2 := by nlinarith
    nlinarith
  have hR : |(N : ℝ) * uN N - (L - ℓ / 2 + Real.log (Real.pi / 8) / 2)| ≤ 3 / 2 * (ℓ / L) := by
    have e : (N : ℝ) * uN N - (L - ℓ / 2 + Real.log (Real.pi / 8) / 2) =
        ((N : ℝ) * uN N - freeMain N) + (ℓ / 4 - Real.log (Real.pi / 8) / 4 + 1 / 8) / L := by
      unfold freeMain nuN; rw [← hLdef, ← hℓ]; ring
    rw [e]
    have h1L : (ℓ / 4 + 1) / L ≤ ℓ / (2 * L) := by
      rw [div_le_div_iff₀ hL0 (by positivity)]; nlinarith
    have e2 : ℓ / L + ℓ / (2 * L) = 3 / 2 * (ℓ / L) := by field_simp; ring
    calc _ ≤ |(N : ℝ) * uN N - freeMain N| + |(ℓ / 4 - Real.log (Real.pi / 8) / 4 + 1 / 8) / L| :=
          abs_add_le _ _
      _ ≤ ℓ / L + ℓ / (2 * L) := add_le_add (hF.trans hsq) (hfr.trans h1L)
      _ = 3 / 2 * (ℓ / L) := e2
  have h := corrLen_of_expansion hNp hu hu2 hR
  have hc : ((N : ℝ) * uN N) ^ 3 / (N : ℝ) ^ 2 ≤ ℓ / L := by
    have hz : (N : ℝ) * uN N ≤ 2 * L := by
      have := abs_le.mp hR; obtain ⟨hc0lo', hc0hi'⟩ := c0_bounds; nlinarith
    exact cubic_small hNp hL hL3 (by positivity) hz (by norm_num)
  have e : 2 * (Real.log (Real.pi / 8) / 2) = Real.log (Real.pi / 8) := by ring
  rw [e] at h
  calc _ ≤ 2 * (3 / 2 * (ℓ / L)) + ((N : ℝ) * uN N) ^ 3 / (N : ℝ) ^ 2 := h
    _ ≤ 2 * (3 / 2 * (ℓ / L)) + ℓ / L := by linarith
    _ = 4 * (ℓ / L) := by ring

/-- **Corollary 5.5(c), periodic ends.**
`N/ξ(J_N^P) = 2 log N - log log N + log(π/2) + O(log log N/log N)`. -/
theorem corrLen_periodic :
    ∀ᶠ N : ℕ in atTop,
      |(N : ℝ) / corrLen (-Real.log (uNP N) / 2) -
        (2 * Real.log N - Real.log (Real.log N) + Real.log (Real.pi / 2))| ≤
        4 * (Real.log (Real.log N) / Real.log N) := by
  obtain ⟨C, hC, hev⟩ := periodic_expansion
  filter_upwards [hev, eventually_ell_sq_le (ε := 1 / (4 * C)) (by positivity),
    eventually_log_pow_le 3 (c := 1) (by norm_num), uNP_first_order,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 240,
    eventually_ge_atTop 2] with N hP hsq hL3 hfo hL240 hN2
  set L := Real.log (N : ℝ) with hLdef
  have hL : (240 : ℝ) ≤ L := hL240
  have hL0 : 0 < L := by linarith
  set ℓ := Real.log L with hℓ
  have hℓ5 : 5 ≤ ℓ := five_le_log_of hL
  have hℓL : ℓ ≤ L / 4 := log_le_quarter (by linarith)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hu := uNP_pos hN2
  obtain ⟨-, hzhi⟩ := hfo
  have hcP := cP_bounds
  have hNL : L ^ 3 ≤ (N : ℝ) := by linarith
  have hL6 : 6 * L ≤ (N : ℝ) := by nlinarith
  have hu2 : uNP N ≤ 1 / 2 := by
    by_contra hcon
    push Not at hcon
    have : (N : ℝ) / 2 < (N : ℝ) * uNP N := by nlinarith
    linarith
  -- `|N u - (L - ℓ/2 + c_P)| ≤ 3ℓ/(4L)`
  have hCr : C * (ℓ ^ 2 / L ^ 2) ≤ ℓ / (4 * L) := by
    have h1 : C * ℓ ^ 2 ≤ L / 4 := by
      have := mul_le_mul_of_nonneg_left hsq hC.le
      have e : C * (1 / (4 * C) * L) = L / 4 := by field_simp
      linarith
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hfr : |(ℓ / 4 - cP / 2 + 3 / 8) / L| ≤ ℓ / (2 * L) := by
    have hnum : |ℓ / 4 - cP / 2 + 3 / 8| ≤ ℓ / 2 := by
      rw [abs_le]; constructor <;> linarith
    rw [abs_div, abs_of_pos hL0]
    calc |ℓ / 4 - cP / 2 + 3 / 8| / L ≤ (ℓ / 2) / L := div_le_div_of_nonneg_right hnum hL0.le
      _ = ℓ / (2 * L) := by field_simp
  have hR : |(N : ℝ) * uNP N - (L - ℓ / 2 + cP)| ≤ 3 / 4 * (ℓ / L) := by
    have e : (N : ℝ) * uNP N - (L - ℓ / 2 + cP) =
        ((N : ℝ) * uNP N - perMain N) + (ℓ / 4 - cP / 2 + 3 / 8) / L := by
      unfold perMain; rw [← hLdef, ← hℓ]; ring
    rw [e]
    have e2 : ℓ / (4 * L) + ℓ / (2 * L) = 3 / 4 * (ℓ / L) := by field_simp; ring
    calc _ ≤ |(N : ℝ) * uNP N - perMain N| + |(ℓ / 4 - cP / 2 + 3 / 8) / L| := abs_add_le _ _
      _ ≤ ℓ / (4 * L) + ℓ / (2 * L) := add_le_add (hP.trans hCr) hfr
      _ = 3 / 4 * (ℓ / L) := e2
  have h := corrLen_of_expansion hNp hu hu2 hR
  have hc : ((N : ℝ) * uNP N) ^ 3 / (N : ℝ) ^ 2 ≤ ℓ / L :=
    cubic_small hNp hL hL3 (by positivity) hzhi (by norm_num)
  have e : 2 * cP = Real.log (Real.pi / 2) := by unfold cP; ring
  rw [e] at h
  have : 2 * (3 / 4 * (ℓ / L)) + ℓ / L ≤ 4 * (ℓ / L) := by
    have : 0 ≤ ℓ / L := by positivity
    linarith
  linarith

end Kagey131
