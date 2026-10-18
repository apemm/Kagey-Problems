import PaperD.U5_LocalUpper

/-!
# Paper D, Online Resource 1, Proposition S2.4 (`thm:B-local-upper`): the local upper bound

**Proposition S2.4.** Assume (H). There are absolute constants `A₁` and `C` such that if
`ε log N ≤ c̄` and `A₁ x log²(x+1) ≤ m ≤ N/8`, then
`f_N(m) ≤ x/(m(m+1)) (1 + C Δ(m)^{1/2})`, `Δ(m) = x log²m/m + ε log N + m/N`.

Lean: `thm_B_local_upper`, with `c̄ = 1/40`, `A₁ = 34000`, `C = 20000`, for `N ≥ 64`, `0 ≤ ε`,
`x ≥ 1` (the condition `ε ≤ 1/4` of (H) follows from `ε log N ≤ 1/40`).
-/

namespace Kagey131.PaperD

open Finset RRT

/-- `log² 2 ≥ 0.48`. -/
theorem log_two_sq_ge : (0.48 : ℝ) ≤ Real.log 2 ^ 2 := by
  have := Real.log_two_gt_d9
  nlinarith

/-- `log y ≤ 11` for `0 < y ≤ 59000`. -/
theorem log_le_eleven {y : ℝ} (hy0 : 0 < y) (hy : y ≤ 59000) : Real.log y ≤ 11 := by
  rw [Real.log_le_iff_le_exp hy0]
  have he := Real.exp_one_gt_d9
  have : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have : (2.718 : ℝ) ^ 11 ≤ Real.exp 1 ^ 11 := pow_le_pow_left₀ (by norm_num) (by linarith) 11
  have h2 : (59000 : ℝ) ≤ (2.718 : ℝ) ^ 11 := by norm_num
  linarith

/-- `log(A x L²) ≤ 11 + 3L` for `L = log(x+1)`, `x ≥ 1`, `0 < A ≤ 59000`. -/
theorem log_AxL_le {x A : ℝ} (hx : 1 ≤ x) (hA0 : 0 < A) (hA : A ≤ 59000) :
    Real.log (A * x * Real.log (x + 1) ^ 2) ≤ 11 + 3 * Real.log (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hA0.ne' hx0.ne', Real.log_pow]
  have h1 : Real.log A ≤ 11 := log_le_eleven hA0 hA
  have h2 : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx0 (by linarith)
  have h3 : Real.log (Real.log (x + 1)) ≤ Real.log (x + 1) := Real.log_le_self hL0.le
  push_cast
  linarith

/-- `0.69 ≤ log(x+1)` and `0.48 ≤ log²(x+1)` for `x ≥ 1`. -/
theorem logx1_bounds {x : ℝ} (hx : 1 ≤ x) :
    (0.69 : ℝ) ≤ Real.log (x + 1) ∧ (0.48 : ℝ) ≤ Real.log (x + 1) ^ 2 := by
  have hL : Real.log 2 ≤ Real.log (x + 1) := Real.log_le_log (by norm_num) (by linarith)
  have := Real.log_two_gt_d9
  refine ⟨by linarith, log_two_sq_ge.trans (pow_le_pow_left₀ (Real.log_nonneg (by norm_num)) hL 2)⟩

/-- `x log²m/m ≤ 1` for `m ≥ 34000 x log²(x+1)`, `x ≥ 1`. -/
theorem upper_aux_xlog {x m : ℝ} (hx : 1 ≤ x) (hm : 34000 * x * Real.log (x + 1) ^ 2 ≤ m) :
    x * Real.log m ^ 2 / m ≤ 1 := by
  set L := Real.log (x + 1) with hL
  obtain ⟨hL1, hL2⟩ := logx1_bounds hx
  rw [← hL] at hL1 hL2
  have hx0 : 0 < x := by linarith
  set M1 : ℝ := 34000 * x * L ^ 2 with hM1
  have hM1ge : (16320 : ℝ) ≤ M1 := by
    have : 0.48 ≤ x * L ^ 2 := by nlinarith
    rw [hM1]; nlinarith
  have hM10 : 0 < M1 := by linarith
  have hlogM1 : 2 ≤ Real.log M1 := by
    rw [Real.le_log_iff_exp_le hM10]
    have he := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have : Real.exp 1 ^ 2 ≤ (2.72 : ℝ) ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 2
    nlinarith
  have hmono := logsq_div_anti hM10 hlogM1 hm
  have hl : Real.log M1 ≤ 11 + 3 * L := log_AxL_le hx (by norm_num) (by norm_num)
  have hl0 : 0 ≤ Real.log M1 := by linarith
  have hsq : Real.log M1 ^ 2 ≤ 242 + 18 * L ^ 2 := by
    have h := mul_le_mul hl hl hl0 (by linarith)
    nlinarith [sq_nonneg (3 * L - 11)]
  have hval : x * (Real.log M1 ^ 2 / M1) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hM10, hM1]
    have : x * (242 + 18 * L ^ 2) ≤ 34000 * x * L ^ 2 := by nlinarith
    have : x * Real.log M1 ^ 2 ≤ x * (242 + 18 * L ^ 2) := mul_le_mul_of_nonneg_left hsq hx0.le
    linarith
  have e : x * Real.log m ^ 2 / m = x * (Real.log m ^ 2 / m) := by ring
  rw [e]
  exact (mul_le_mul_of_nonneg_left hmono hx0.le).trans hval

/-- `16 x log m' ≤ m'` for `m' ≥ 17000 x log²(x+1)`, `x ≥ 1`. -/
theorem upper_aux_16 {x m' : ℝ} (hx : 1 ≤ x) (hm : 17000 * x * Real.log (x + 1) ^ 2 ≤ m') :
    16 * x * Real.log m' ≤ m' := by
  set L := Real.log (x + 1) with hL
  obtain ⟨hL1, hL2⟩ := logx1_bounds hx
  rw [← hL] at hL1 hL2
  have hx0 : 0 < x := by linarith
  set M0 : ℝ := 17000 * x * L ^ 2 with hM0
  have hM0ge : (8160 : ℝ) ≤ M0 := by
    have : 0.48 ≤ x * L ^ 2 := by nlinarith
    rw [hM0]; nlinarith
  have hM00 : 0 < M0 := by linarith
  have hm0 : 0 < m' := by linarith
  have hlogM0 : 1 ≤ Real.log M0 := by
    rw [Real.le_log_iff_exp_le hM00]; have := Real.exp_one_lt_d9; linarith
  have hmono := log_div_anti hM00 hlogM0 hm
  have hl : Real.log M0 ≤ 11 + 3 * L := log_AxL_le hx (by norm_num) (by norm_num)
  have hval : 16 * x * Real.log M0 ≤ M0 := by
    have h1 : 16 * x * Real.log M0 ≤ 16 * x * (11 + 3 * L) := mul_le_mul_of_nonneg_left hl (by positivity)
    have h2 : 16 * (11 + 3 * L) ≤ 17000 * L ^ 2 := by nlinarith
    rw [hM0]
    have : 16 * x * (11 + 3 * L) ≤ 17000 * x * L ^ 2 := by nlinarith
    linarith
  have h1 : 16 * x * (Real.log m' / m') ≤ 16 * x * (Real.log M0 / M0) :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  have h2 : 16 * x * (Real.log M0 / M0) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hM00]; exact hval
  have e : 16 * x * (Real.log m' / m') = 16 * x * Real.log m' / m' := by ring
  have h3 : 16 * x * Real.log m' / m' ≤ 1 := by rw [← e]; linarith
  rwa [div_le_one hm0] at h3

/-- The mode is at most `m/2` under the hypotheses of Proposition S2.4 (from Lemma B.5). -/
theorem upper_aux_mode {ε : ℝ} (h0 : 0 ≤ ε) {N m : ℕ} (hN : 64 ≤ N) (hx : 1 ≤ (N : ℝ) * ε)
    (hεN : ε * Real.log N ≤ 1 / 40)
    (hA : 34000 * ((N : ℝ) * ε) * Real.log ((N : ℝ) * ε + 1) ^ 2 ≤ m) (h8m : 8 * m ≤ N) :
    (modeH ε N : ℝ) ≤ (m : ℝ) / 2 := by
  set x := (N : ℝ) * ε with hxdef
  set L := Real.log (x + 1) with hL
  obtain ⟨hL1, hL2⟩ := logx1_bounds hx
  rw [← hL] at hL1 hL2
  have h8mr : 8 * (m : ℝ) ≤ N := by exact_mod_cast h8m
  have hlog2 : Real.log (x + 2) ≤ 2 * L := by
    have e : Real.log ((x + 1) ^ 2) = 2 * Real.log (x + 1) := by rw [Real.log_pow]; norm_num
    rw [hL, ← e]; exact Real.log_le_log (by linarith) (by nlinarith)
  have hB := lem_B_mode h0 hN hx hεN (by
    have h1 : 804 * x * Real.log (x + 2) ≤ 804 * x * (2 * L) :=
      mul_le_mul_of_nonneg_left hlog2 (by positivity)
    have h2 : 804 * x * (2 * L) ≤ 8 * (34000 * x * L ^ 2) := by
      have : 2 * L ≤ 2.9 * L ^ 2 := by nlinarith
      have hx0 : 0 ≤ x := by linarith
      nlinarith
    linarith)
  rw [← hxdef, ← hL] at hB
  linarith

/-- The window identity `P(a ≤ M_N ≤ b) = P(M_N ≥ a) - P(M_N ≥ b+1)`. -/
theorem tail_split {ε : ℝ} {N a b : ℕ} (hab : a ≤ b) (hb : b ≤ N) :
    ∑ k ∈ range (N + 1), (if a ≤ k then law ε N k else 0) =
      ∑ ℓ ∈ Icc a b, law ε N ℓ + ∑ k ∈ range (N + 1), (if b + 1 ≤ k then law ε N k else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  rw [show (range (N + 1)).filter (fun k => a ≤ k) =
      Icc a b ∪ (range (N + 1)).filter (fun k => b + 1 ≤ k) by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega]
  rw [Finset.sum_union]
  rw [Finset.disjoint_left]
  intro k h1 h2
  simp only [Finset.mem_Icc, Finset.mem_filter] at h1 h2
  omega

/-- The first tail, from Proposition S2.3 at `m - k ≥ m/2`. -/
theorem upper_first_tail {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) {N m k : ℕ} (hN : 64 ≤ N)
    (hx : 1 ≤ (N : ℝ) * ε) (hk : 2 * k ≤ m) (h8m : 8 * m ≤ N)
    (h16 : 16 * ((N : ℝ) * ε) * Real.log ((m : ℝ) - k) ≤ (m : ℝ) - k) (hm6 : 12 ≤ m) :
    ∑ b ∈ range (N + 1), (if m - k ≤ b then law ε N b else 0) ≤
      (N : ℝ) * ε / ((m : ℝ) - k) + 3200 * ((N : ℝ) * ε) ^ 2 * Real.log m ^ 2 / (m : ℝ) ^ 2 := by
  set x := (N : ℝ) * ε with hxdef
  have hkr : 2 * (k : ℝ) ≤ m := by exact_mod_cast hk
  have hmr : (12 : ℝ) ≤ m := by exact_mod_cast hm6
  have hmk0 : (0 : ℝ) < (m : ℝ) - k := by linarith
  have hmk_nat : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by rw [Nat.cast_sub (by omega)]
  have hS3 := thm_B_cum_upper h0 hε (N := N) (m := m - k) hN hx (by omega) (by omega)
    (by rw [hmk_nat]; exact h16)
  rw [← hxdef, hmk_nat] at hS3
  refine hS3.trans ?_
  have hlm : Real.log ((m : ℝ) - k) ≤ Real.log m := Real.log_le_log hmk0 (by linarith)
  have hlm0 : 0 ≤ Real.log ((m : ℝ) - k) := Real.log_nonneg (by linarith)
  have hsq : Real.log ((m : ℝ) - k) ^ 2 ≤ Real.log m ^ 2 := pow_le_pow_left₀ hlm0 hlm 2
  have hx0 : 0 ≤ x := by linarith
  have h1 : 800 * x ^ 2 * Real.log ((m : ℝ) - k) ^ 2 / ((m : ℝ) - k) ^ 2 ≤
      3200 * x ^ 2 * Real.log m ^ 2 / (m : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hmk2 : (m : ℝ) ^ 2 ≤ 4 * ((m : ℝ) - k) ^ 2 := by nlinarith
    have hx2 : 0 ≤ x ^ 2 := by positivity
    have := mul_le_mul hsq hmk2 (sq_nonneg _) (by positivity)
    nlinarith
  have e : x / ((m : ℝ) - k) * (1 + 800 * x * Real.log ((m : ℝ) - k) ^ 2 / ((m : ℝ) - k)) =
      x / ((m : ℝ) - k) + 800 * x ^ 2 * Real.log ((m : ℝ) - k) ^ 2 / ((m : ℝ) - k) ^ 2 := by
    field_simp
  rw [e]
  linarith

/-- **Steps 1 and 2 of the proof of Proposition S2.4**, for one `k ≤ m/2`:
`f_N(m) ≤ x/((m-k)(m+1)) + 3262 x Δ/(m(k+1))`. -/
theorem upper_comb {ε : ℝ} (h0 : 0 ≤ ε) {N m : ℕ} (hN : 64 ≤ N) (hx : 1 ≤ (N : ℝ) * ε)
    (hεN : ε * Real.log N ≤ 1 / 40)
    (hA : 34000 * ((N : ℝ) * ε) * Real.log ((N : ℝ) * ε + 1) ^ 2 ≤ m) (h8m : 8 * m ≤ N)
    (k : ℕ) (hk : 2 * k ≤ m) :
    law ε N m ≤ (N : ℝ) * ε / (((m : ℝ) - k) * ((m : ℝ) + 1)) +
      3262 * ((N : ℝ) * ε) * ((N : ℝ) * ε * Real.log m ^ 2 / m + ε * Real.log N + (m : ℝ) / N) /
        ((m : ℝ) * ((k : ℝ) + 1)) := by
  set x := (N : ℝ) * ε with hxdef
  set Δ := x * Real.log m ^ 2 / m + ε * Real.log N + (m : ℝ) / N with hΔ
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 4 ≤ Real.log N := four_le_log_64.trans (Real.log_le_log (by norm_num) hNr)
  have hε160 : ε ≤ 1 / 160 := by nlinarith
  obtain ⟨hL1, hL2⟩ := logx1_bounds hx
  have hxL : 0.48 ≤ x * Real.log (x + 1) ^ 2 := by nlinarith
  have hm16 : (16200 : ℝ) ≤ m := by nlinarith
  have hm16' : 16200 ≤ m := by exact_mod_cast hm16
  have hm0 : (0 : ℝ) < m := by linarith
  have hmode := upper_aux_mode h0 hN hx hεN hA h8m
  try rw [← hxdef] at hmode
  have hkr : 2 * (k : ℝ) ≤ m := by exact_mod_cast hk
  have hmk0 : (0 : ℝ) < (m : ℝ) - k := by linarith
  have hmk_nat : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by rw [Nat.cast_sub (by omega)]
  -- the sandwich
  have hsw := lem_B_sandwich_right h0 (by linarith) (N := N) (a := m - k) (b := m) (by omega)
    (by have : (modeH ε N : ℝ) ≤ ((m - k : ℕ) : ℝ) := by rw [hmk_nat]; linarith
        exact_mod_cast this) (by omega) (by omega)
  rw [show ((m : ℝ) - ((m - k : ℕ) : ℝ) + 1) = (k : ℝ) + 1 by rw [hmk_nat]; ring] at hsw
  have hsplit := tail_split (ε := ε) (N := N) (a := m - k) (b := m) (by omega) (by omega)
  have h16 : 16 * x * Real.log ((m : ℝ) - k) ≤ (m : ℝ) - k :=
    upper_aux_16 hx (by linarith)
  have hS3 := upper_first_tail h0 (by linarith) hN hx hk h8m h16 (by omega)
  try rw [← hxdef] at hS3
  have hlow := lower_tail_sum h0 (by linarith) hN hx hm16' h8m
  try rw [← hxdef] at hlow
  try rw [← hΔ] at hlow
  -- combine
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hwin : ((k : ℝ) + 1) * law ε N m ≤ x / ((m : ℝ) - k) + 3200 * x ^ 2 * Real.log m ^ 2 / (m : ℝ) ^ 2
      - x / ((m : ℝ) + 1) * (1 - 62 * Δ) := by linarith
  have hΔa : x * Real.log m ^ 2 / m ≤ Δ := by
    rw [hΔ]
    have : (0 : ℝ) ≤ (m : ℝ) / N := by positivity
    have : 0 ≤ ε * Real.log N := mul_nonneg h0 (by linarith)
    linarith
  have hx0 : 0 < x := by linarith
  have hΔ0 : 0 ≤ Δ := le_trans (by positivity) hΔa
  have e1 : x / ((m : ℝ) - k) - x / ((m : ℝ) + 1) =
      ((k : ℝ) + 1) * (x / (((m : ℝ) - k) * ((m : ℝ) + 1))) := by
    field_simp; ring
  have h1 : 3200 * x ^ 2 * Real.log m ^ 2 / (m : ℝ) ^ 2 ≤ 3200 * x * Δ / m := by
    have e : 3200 * x ^ 2 * Real.log m ^ 2 / (m : ℝ) ^ 2 = 3200 * x / m * (x * Real.log m ^ 2 / m) := by
      field_simp
    have e' : 3200 * x * Δ / m = 3200 * x / m * Δ := by ring
    rw [e, e']
    exact mul_le_mul_of_nonneg_left hΔa (by positivity)
  have h2 : x / ((m : ℝ) + 1) * (62 * Δ) ≤ 62 * x * Δ / m := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hm0]
    have : 0 ≤ x * (62 * Δ) := by positivity
    nlinarith
  have hfin : ((k : ℝ) + 1) * law ε N m ≤ ((k : ℝ) + 1) * (x / (((m : ℝ) - k) * ((m : ℝ) + 1))) +
      3262 * x * Δ / m := by
    have e3 : x / ((m : ℝ) + 1) * (1 - 62 * Δ) = x / ((m : ℝ) + 1) - x / ((m : ℝ) + 1) * (62 * Δ) := by
      ring
    have e4 : 3262 * x * Δ / m = 3200 * x * Δ / m + 62 * x * Δ / m := by ring
    linarith
  have e4 : 3262 * x * Δ / ((m : ℝ) * ((k : ℝ) + 1)) * ((k : ℝ) + 1) = 3262 * x * Δ / m := by
    field_simp
  have : ((k : ℝ) + 1) * law ε N m ≤ ((k : ℝ) + 1) * (x / (((m : ℝ) - k) * ((m : ℝ) + 1)) +
      3262 * x * Δ / ((m : ℝ) * ((k : ℝ) + 1))) := by
    rw [mul_add, mul_comm ((k : ℝ) + 1) (3262 * x * Δ / ((m : ℝ) * ((k : ℝ) + 1))), e4]
    exact hfin
  exact le_of_mul_le_mul_left this hk1

/-- **Step 3 of the proof of Proposition S2.4: the choice of `k`**, as a statement about reals. -/
theorem choose_k_bound {f x Δ : ℝ} {m : ℕ} (hm : 16 ≤ m) (hx0 : 0 < x) (hΔm : 1 / (m : ℝ) ≤ Δ)
    (hΔmax : Δ ≤ 1.15)
    (H : ∀ k : ℕ, 2 * k ≤ m → f ≤ x / (((m : ℝ) - k) * ((m : ℝ) + 1)) +
      3262 * x * Δ / ((m : ℝ) * ((k : ℝ) + 1))) :
    f ≤ x / ((m : ℝ) * ((m : ℝ) + 1)) * (1 + 20000 * Real.sqrt Δ) := by
  have hmr : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hΔ0 : 0 < Δ := lt_of_lt_of_le (by positivity) hΔm
  set δ := Real.sqrt Δ with hδ
  have hδ0 : 0 < δ := Real.sqrt_pos.mpr hΔ0
  have hδsq : δ ^ 2 = Δ := Real.sq_sqrt hΔ0.le
  set X := x / ((m : ℝ) * ((m : ℝ) + 1)) with hX
  have hX0 : 0 < X := by positivity
  by_cases hsmall : Δ ≤ 1 / 16
  · have hδ4 : δ ≤ 1 / 4 := by
      rw [hδ, show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hsmall
    set k := ⌈(m : ℝ) * δ⌉₊ with hk
    have hkge : (m : ℝ) * δ ≤ k := Nat.le_ceil _
    have hklt : (k : ℝ) < (m : ℝ) * δ + 1 := Nat.ceil_lt_add_one (by positivity)
    have hk2 : 2 * k ≤ m := by
      have : 2 * (k : ℝ) ≤ m := by nlinarith
      exact_mod_cast this
    have hb := H k hk2
    have hkr : 2 * (k : ℝ) ≤ m := by exact_mod_cast hk2
    have hmk0 : (0 : ℝ) < (m : ℝ) - k := by linarith
    have hratio : x / (((m : ℝ) - k) * ((m : ℝ) + 1)) ≤ X * (1 + 2 * δ + 2 / m) := by
      have h1 : (m : ℝ) / ((m : ℝ) - k) ≤ 1 + 2 * (k : ℝ) / m := by
        rw [div_le_iff₀ hmk0]
        have e : (1 + 2 * (k : ℝ) / m) * ((m : ℝ) - k) = m + k - 2 * (k : ℝ) ^ 2 / m := by
          field_simp; ring
        have : 2 * (k : ℝ) ^ 2 / m ≤ k := by rw [div_le_iff₀ hm0]; nlinarith
        rw [e]; linarith
      have h2 : 2 * (k : ℝ) / m ≤ 2 * δ + 2 / m := by
        rw [div_le_iff₀ hm0]
        have : (2 * δ + 2 / m) * m = 2 * (m * δ) + 2 := by field_simp
        rw [this]; linarith
      have e : x / (((m : ℝ) - k) * ((m : ℝ) + 1)) = X * ((m : ℝ) / ((m : ℝ) - k)) := by
        rw [hX]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) hX0.le
    have hsecond : 3262 * x * Δ / ((m : ℝ) * ((k : ℝ) + 1)) ≤ X * (6524 * δ) := by
      have hk1 : (m : ℝ) * δ ≤ (k : ℝ) + 1 := by linarith
      have h1 : 3262 * x * Δ / ((m : ℝ) * ((k : ℝ) + 1)) ≤ 3262 * x * Δ / ((m : ℝ) * ((m : ℝ) * δ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hk1 hm0.le)
      refine h1.trans ?_
      rw [hX, ← hδsq, div_le_iff₀ (by positivity)]
      have e : x / ((m : ℝ) * ((m : ℝ) + 1)) * (6524 * δ) * ((m : ℝ) * ((m : ℝ) * δ)) =
          6524 * x * δ ^ 2 * ((m : ℝ) / ((m : ℝ) + 1)) := by field_simp
      rw [e]
      have : (1 : ℝ) / 2 ≤ (m : ℝ) / ((m : ℝ) + 1) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have hxd : 0 ≤ x * δ ^ 2 := by positivity
      nlinarith
    have h2m : 2 / (m : ℝ) ≤ 2 * δ := by
      have hΔδ : Δ ≤ δ := by rw [← hδsq]; nlinarith
      have : 1 / (m : ℝ) ≤ δ := le_trans hΔm hΔδ
      have e : 2 / (m : ℝ) = 2 * (1 / (m : ℝ)) := by ring
      linarith
    calc f ≤ X * (1 + 2 * δ + 2 / m) + X * (6524 * δ) := by linarith
      _ ≤ X * (1 + 20000 * δ) := by
          have : X * (1 + 2 * δ + 2 / m) + X * (6524 * δ) = X * (1 + 2 * δ + 2 / m + 6524 * δ) := by
            ring
          rw [this]
          apply mul_le_mul_of_nonneg_left _ hX0.le
          linarith
  · push Not at hsmall
    have hδ4 : 1 / 4 < δ := by
      rw [hδ, show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) hsmall
    have hδmax : δ ≤ 1.073 := by
      rw [hδ, show (1.073 : ℝ) = Real.sqrt (1.073 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num; linarith)
    set k := m / 2 with hk
    have hk2 : 2 * k ≤ m := by omega
    have hb := H k hk2
    have hkr : (m : ℝ) / 2 ≤ (k : ℝ) + 1 := by
      have : (m : ℕ) < 2 * (m / 2) + 2 := by omega
      have h' : ((m : ℕ) : ℝ) < ((2 * (m / 2) + 2 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'; rw [hk]; linarith
    have hkr2 : 2 * (k : ℝ) ≤ m := by exact_mod_cast hk2
    have hmk : (m : ℝ) / 2 ≤ (m : ℝ) - k := by linarith
    have hmk0 : (0 : ℝ) < (m : ℝ) - k := by linarith
    have h1 : x / (((m : ℝ) - k) * ((m : ℝ) + 1)) ≤ 2 * X := by
      rw [hX, div_le_iff₀ (by positivity)]
      have e : 2 * (x / ((m : ℝ) * ((m : ℝ) + 1))) * (((m : ℝ) - k) * ((m : ℝ) + 1)) =
          x * (2 * ((m : ℝ) - k) / m) := by field_simp
      rw [e]
      have : 1 ≤ 2 * ((m : ℝ) - k) / m := by rw [le_div_iff₀ hm0]; linarith
      nlinarith
    have h2 : 3262 * x * Δ / ((m : ℝ) * ((k : ℝ) + 1)) ≤ X * (13048 * Δ) := by
      rw [hX, div_le_iff₀ (by positivity)]
      have e : x / ((m : ℝ) * ((m : ℝ) + 1)) * (13048 * Δ) * ((m : ℝ) * ((k : ℝ) + 1)) =
          13048 * x * Δ * (((k : ℝ) + 1) / ((m : ℝ) + 1)) := by field_simp
      rw [e]
      have : (1 : ℝ) / 4 ≤ ((k : ℝ) + 1) / ((m : ℝ) + 1) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have hxd : 0 ≤ x * Δ := by positivity
      nlinarith
    have hΔδ : Δ ≤ 1.073 * δ := by rw [← hδsq]; nlinarith
    calc f ≤ 2 * X + X * (13048 * Δ) := by linarith
      _ ≤ X * (1 + 20000 * δ) := by
          have : 2 * X + X * (13048 * Δ) = X * (2 + 13048 * Δ) := by ring
          rw [this]
          apply mul_le_mul_of_nonneg_left _ hX0.le
          nlinarith

/-- **Proposition S2.4 (`thm:B-local-upper`).** For `N ≥ 64`, `0 ≤ ε`, `x = Nε ≥ 1`,
`ε log N ≤ 1/40` (`c̄ = 1/40`) and `34000 x log²(x+1) ≤ m`, `8m ≤ N` (`A₁ = 34000`):
`f_N(m) ≤ x/(m(m+1)) (1 + 20000 Δ(m)^{1/2})`, `Δ(m) = x log²m/m + ε log N + m/N`. -/
theorem thm_B_local_upper {ε : ℝ} (h0 : 0 ≤ ε) {N m : ℕ} (hN : 64 ≤ N) (hx : 1 ≤ (N : ℝ) * ε)
    (hεN : ε * Real.log N ≤ 1 / 40)
    (hA : 34000 * ((N : ℝ) * ε) * Real.log ((N : ℝ) * ε + 1) ^ 2 ≤ m) (h8m : 8 * m ≤ N) :
    law ε N m ≤ (N : ℝ) * ε / ((m : ℝ) * ((m : ℝ) + 1)) *
      (1 + 20000 * Real.sqrt ((N : ℝ) * ε * Real.log m ^ 2 / m + ε * Real.log N + (m : ℝ) / N)) := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 4 ≤ Real.log N := four_le_log_64.trans (Real.log_le_log (by norm_num) hNr)
  obtain ⟨hL1, hL2⟩ := logx1_bounds hx
  have hxL : 0.48 ≤ (N : ℝ) * ε * Real.log ((N : ℝ) * ε + 1) ^ 2 := by nlinarith
  have hm16 : (16200 : ℝ) ≤ m := by nlinarith
  have hm0 : (0 : ℝ) < m := by linarith
  have h8mr : 8 * (m : ℝ) ≤ N := by exact_mod_cast h8m
  have hlogm : 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le hm0]; have := Real.exp_one_lt_d9; linarith
  have hx0 : 0 < (N : ℝ) * ε := by linarith
  have hε0 : 0 ≤ ε * Real.log N := mul_nonneg h0 (by linarith)
  have hmN0 : 0 ≤ (m : ℝ) / N := by positivity
  apply choose_k_bound (m := m) (by exact_mod_cast (show (16 : ℝ) ≤ m by linarith)) hx0
  · have : 1 / (m : ℝ) ≤ (N : ℝ) * ε * Real.log m ^ 2 / m := by
      apply div_le_div_of_nonneg_right _ hm0.le
      exact one_le_mul_of_one_le_of_one_le hx (one_le_pow₀ hlogm)
    linarith
  · have h1 := upper_aux_xlog hx hA
    have : (m : ℝ) / N ≤ 1 / 8 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  · exact fun k hk => upper_comb h0 hN hx hεN hA h8m k hk

end Kagey131.PaperD
