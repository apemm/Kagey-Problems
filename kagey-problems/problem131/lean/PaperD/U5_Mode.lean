import PaperD.U5_LocalLowerMain
import PaperD.U5_Sandwich

/-!
# Paper D, Lemma B.5 (`lem:B-mode`): the mode bound

**Lemma B.5.** Assume (H). There are absolute constants `c̄ > 0` and `A₀` such that if
`ε log N ≤ c̄` and `A₀ x log(x+2) ≤ N/4`, then `m_h ≤ A₀ x log²(x+1)`.

Lean, with `c̄ = 1/40`:
* `B5_ell_lower`: at any `ℓ ≥ 200 x log(x+2)` with `4ℓ ≤ N`, `f_N(ℓ) ≥ x/(2ℓ(ℓ+1))`
  (Proposition B.4 with `e₁(ℓ) ≤ 1/2`, from the explicit form `lem_B4_explicit`).
* `lem_B5_strong`: `m_h ≤ (ℓ+1)(1 + 2H_ℓ)` for `ℓ = ⌈200 x log(x+2)⌉`, under
  `804 x log(x+2) ≤ N` (this is the bound the paper's proof gives before simplifying).
* `lem_B_mode`: `m_h ≤ 15400 x log²(x+1)` under `804 x log(x+2) ≤ N`.
* `lem_B_mode_paper`: the paper's form with `A₀ = 15400` in both places.

The hypotheses: `N ≥ 64`, `0 ≤ ε`, `x ≥ 1`, `ε log N ≤ 1/40`; the condition `ε ≤ 1/4` of (H)
follows (`ε ≤ 1/160`).
-/

namespace Kagey131.PaperD

open Finset RRT

/-- `(1 + log b)/b ≤ (1 + log a)/a` for `1 ≤ a ≤ b`. -/
theorem one_add_log_div_anti {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (1 + Real.log b) / b ≤ (1 + Real.log a) / a := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [div_le_div_iff₀ hb0 ha0]
  have h1 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hb0.ne' ha0.ne'] at h1
  have h2 : a * (Real.log b - Real.log a) ≤ b - a := by
    have := mul_le_mul_of_nonneg_left h1 ha0.le
    have e : a * (b / a - 1) = b - a := by field_simp
    linarith
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  nlinarith

/-- `log 200 ≤ 6` and `log 201 ≤ 6`. -/
theorem log_201_le : Real.log 201 ≤ 6 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have he := Real.exp_one_gt_d9
  have : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have : (2.7 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
  nlinarith

/-- `log 64 ≥ 4`. -/
theorem four_le_log_64 : 4 ≤ Real.log 64 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have he := Real.exp_one_lt_d9
  have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have : Real.exp 1 ^ 4 ≤ (2.72 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 4
  nlinarith

/-- `y e^{-y/9} ≤ 9/2000` for `y ≥ 200`. -/
theorem mul_exp_neg_ninth_small {y : ℝ} (hy : 200 ≤ y) : y * Real.exp (-(y / 9)) ≤ 9 / 2000 := by
  have hz : 0 ≤ y / 9 := by linarith
  have h5 := Real.pow_div_factorial_le_exp (y / 9) hz 5
  have hf : ((Nat.factorial 5 : ℕ) : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hf] at h5
  have hpos := Real.exp_pos (y / 9)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  have : (y / 9) ^ 5 / 120 * (9 / 2000) ≥ y := by
    have h1 : (y / 9) ^ 4 ≥ (200 / 9) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    have e : (y / 9) ^ 5 / 120 * (9 / 2000) = y * ((y / 9) ^ 4 / 240000) := by ring
    rw [e]
    have : (200 / 9 : ℝ) ^ 4 / 240000 ≥ 1 := by norm_num
    have : (y / 9) ^ 4 / 240000 ≥ 1 := by
      have := div_le_div_of_nonneg_right h1 (show (0 : ℝ) ≤ 240000 by norm_num); linarith
    nlinarith
  nlinarith

/-- **The point `ℓ` of the proof of Lemma B.5.** For `N ≥ 64`, `0 ≤ ε`, `x = Nε ≥ 1`,
`ε log N ≤ 1/40`, `ℓ ≥ 200 x log(x+2)` and `4ℓ ≤ N`: `f_N(ℓ) ≥ x/(2ℓ(ℓ+1))`. -/
theorem B5_ell_lower {ε : ℝ} (h0 : 0 ≤ ε) {N ℓ : ℕ} (hN : 64 ≤ N) (hx : 1 ≤ (N : ℝ) * ε)
    (hεN : ε * Real.log N ≤ 1 / 40)
    (hℓ : 200 * ((N : ℝ) * ε) * Real.log ((N : ℝ) * ε + 2) ≤ ℓ) (h4ℓ : 4 * ℓ ≤ N) :
    (N : ℝ) * ε / (2 * ((ℓ : ℝ) * ((ℓ : ℝ) + 1))) ≤ law ε N ℓ := by
  set x := (N : ℝ) * ε with hxdef
  set L2 := Real.log (x + 2) with hL2
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 4 ≤ Real.log N := four_le_log_64.trans (Real.log_le_log (by norm_num) hNr)
  have hε160 : ε ≤ 1 / 160 := by nlinarith
  have hε1 : ε ≤ 1 := by linarith
  have hL21 : 1 ≤ L2 := one_le_log_three.trans (Real.log_le_log (by norm_num) (by linarith))
  have hℓ200 : (200 : ℝ) ≤ ℓ := by nlinarith
  have hℓ2 : 2 ≤ ℓ := by
    have : (2 : ℝ) ≤ ℓ := by linarith
    exact_mod_cast this
  have hB := lem_B4_explicit h0 hε1 hN hℓ2 h4ℓ
  rw [← hxdef] at hB
  refine le_trans ?_ hB
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hX0 : 0 ≤ x / ((ℓ : ℝ) * ((ℓ : ℝ) + 1)) := by positivity
  have e : x / (2 * ((ℓ : ℝ) * ((ℓ : ℝ) + 1))) = x / ((ℓ : ℝ) * ((ℓ : ℝ) + 1)) * (1 / 2) := by
    field_simp
  rw [e]
  apply mul_le_mul_of_nonneg_left _ hX0
  -- the five error terms
  have hx0 : 0 < x := by linarith
  have t1 : x * (harmonic ℓ : ℝ) / ℓ ≤ 9 / 200 := by
    have hH := harmonic_le_one_add_log ℓ
    have hℓ0' : (1 : ℝ) ≤ 200 * x * L2 := by nlinarith
    have hmono := one_add_log_div_anti hℓ0' hℓ
    have hlog0 : Real.log (200 * x * L2) ≤ 6 + L2 + L2 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hx0.ne']
      have h1 : Real.log 200 ≤ 6 :=
        (Real.log_le_log (by norm_num) (by norm_num)).trans log_201_le
      have h2 : Real.log x ≤ L2 := Real.log_le_log hx0 (by linarith)
      have h3 : Real.log L2 ≤ L2 := Real.log_le_self (by linarith)
      linarith
    have : x * (harmonic ℓ : ℝ) / ℓ ≤ x * ((1 + Real.log ℓ) / ℓ) := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hH hℓ0.le) hx0.le
    refine this.trans ?_
    calc x * ((1 + Real.log ℓ) / ℓ) ≤ x * ((1 + Real.log (200 * x * L2)) / (200 * x * L2)) :=
          mul_le_mul_of_nonneg_left hmono hx0.le
      _ = (1 + Real.log (200 * x * L2)) / (200 * L2) := by field_simp
      _ ≤ (9 * L2) / (200 * L2) := by
          apply div_le_div_of_nonneg_right _ (by positivity); linarith
      _ = 9 / 200 := by field_simp
  have t2 : 2 * x * ((N : ℝ) - ℓ - 1) / ((N : ℝ) * ((ℓ : ℝ) + 2)) ≤ 1 / 100 := by
    rw [div_le_iff₀ (by positivity)]
    have : 200 * x ≤ ℓ := by nlinarith
    have hNl : (N : ℝ) - ℓ - 1 ≤ N := by linarith
    nlinarith
  have t3 : 2 * ε * (harmonic (ℓ + 1) : ℝ) ≤ 1 / 80 + 1 / 20 := by
    have hH := harmonic_le_one_add_log (ℓ + 1)
    have h4r : (4 * ℓ : ℝ) ≤ N := by exact_mod_cast h4ℓ
    have : Real.log ((ℓ + 1 : ℕ) : ℝ) ≤ Real.log N :=
      Real.log_le_log (by positivity) (by push_cast; linarith)
    nlinarith
  have t4 : 8 * ε * Real.log N ≤ 1 / 5 := by nlinarith
  have t5 : lateErr ℓ ≤ 9 / 100 := by
    have h := lateErr_le hℓ2
    have := mul_exp_neg_ninth_small hℓ200
    nlinarith
  linarith

/-- **Lemma B.5 (`lem:B-mode`), the bound before simplifying.** For `N ≥ 64`, `0 ≤ ε`, `x ≥ 1`,
`ε log N ≤ 1/40` and `804 x log(x+2) ≤ N`, with `ℓ = ⌈200 x log(x+2)⌉`:
`m_h ≤ (ℓ+1)(1 + 2H_ℓ)`. -/
theorem lem_B5_strong {ε : ℝ} (h0 : 0 ≤ ε) {N : ℕ} (hN : 64 ≤ N) (hx : 1 ≤ (N : ℝ) * ε)
    (hεN : ε * Real.log N ≤ 1 / 40)
    (hA : 804 * ((N : ℝ) * ε) * Real.log ((N : ℝ) * ε + 2) ≤ N) :
    (modeH ε N : ℝ) ≤ ((⌈200 * ((N : ℝ) * ε) * Real.log ((N : ℝ) * ε + 2)⌉₊ : ℕ) + 1 : ℝ) *
      (1 + 2 * (harmonic ⌈200 * ((N : ℝ) * ε) * Real.log ((N : ℝ) * ε + 2)⌉₊ : ℝ)) := by
  set x := (N : ℝ) * ε with hxdef
  set L2 := Real.log (x + 2) with hL2
  set ℓ := ⌈200 * x * L2⌉₊ with hℓdef
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 4 ≤ Real.log N := four_le_log_64.trans (Real.log_le_log (by norm_num) hNr)
  have hε1 : ε < 1 := by nlinarith
  have hL21 : 1 ≤ L2 := one_le_log_three.trans (Real.log_le_log (by norm_num) (by linarith))
  have hxL : 1 ≤ x * L2 := by nlinarith
  have hℓge : 200 * x * L2 ≤ ℓ := Nat.le_ceil _
  have hℓlt : (ℓ : ℝ) < 200 * x * L2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have h4ℓ : 4 * ℓ ≤ N := by
    have : (4 * ℓ : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hℓ1 : 1 ≤ ℓ := by
    have : (1 : ℝ) ≤ ℓ := by nlinarith
    exact_mod_cast this
  have hH0 : (0 : ℝ) ≤ (harmonic ℓ : ℝ) := by exact_mod_cast (harmonic_pos (by omega)).le
  by_cases hmh : modeH ε N < ℓ
  · have : (modeH ε N : ℝ) ≤ ℓ := by exact_mod_cast hmh.le
    nlinarith
  · push Not at hmh
    have hf := B5_ell_lower h0 hN hx hεN hℓge h4ℓ
    rw [← hxdef] at hf
    have hsw := lem_B_sandwich_left h0 hε1 (by omega : 1 ≤ N) hmh le_rfl
    have hmN := modeH_le ε N
    have htail := lem_B_tail_law h0 hε1.le (N := N) (z := ℓ) (by omega) hℓ1
    rw [← hxdef] at htail
    have hsub : ∑ k ∈ Icc ℓ (modeH ε N), law ε N k ≤
        ∑ b ∈ range (N + 1), (if ℓ ≤ b then law ε N b else 0) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro b hb
        simp only [Finset.mem_Icc] at hb
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · intro b _ _; exact law_nonneg h0 hε1.le _ _
    have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
    have hx0 : 0 < x := by linarith
    -- `(m_h - ℓ + 1) x/(2ℓ(ℓ+1)) ≤ x H_ℓ/ℓ`
    have hk : ((modeH ε N : ℝ) - ℓ + 1) * (x / (2 * ((ℓ : ℝ) * ((ℓ : ℝ) + 1)))) ≤
        x * (harmonic ℓ : ℝ) / ℓ := by
      have hk0 : (0 : ℝ) ≤ (modeH ε N : ℝ) - ℓ + 1 := by
        have : (ℓ : ℝ) ≤ modeH ε N := by exact_mod_cast hmh
        linarith
      calc ((modeH ε N : ℝ) - ℓ + 1) * (x / (2 * ((ℓ : ℝ) * ((ℓ : ℝ) + 1))))
          ≤ ((modeH ε N : ℝ) - ℓ + 1) * law ε N ℓ := mul_le_mul_of_nonneg_left hf hk0
        _ ≤ _ := hsw
        _ ≤ _ := hsub
        _ ≤ _ := htail
    have e : ((modeH ε N : ℝ) - ℓ + 1) * (x / (2 * ((ℓ : ℝ) * ((ℓ : ℝ) + 1)))) =
        (x / ℓ) * (((modeH ε N : ℝ) - ℓ + 1) / (2 * ((ℓ : ℝ) + 1))) := by
      field_simp
    have e2 : x * (harmonic ℓ : ℝ) / ℓ = (x / ℓ) * (harmonic ℓ : ℝ) := by ring
    rw [e, e2] at hk
    have hk' := le_of_mul_le_mul_left hk (by positivity)
    rw [div_le_iff₀ (by positivity)] at hk'
    nlinarith

/-- **Lemma B.5 (`lem:B-mode`).** For `N ≥ 64`, `0 ≤ ε`, `x = Nε ≥ 1`, `ε log N ≤ 1/40`
(`c̄ = 1/40`) and `804 x log(x+2) ≤ N`: `m_h ≤ 15400 x log²(x+1)`. -/
theorem lem_B_mode {ε : ℝ} (h0 : 0 ≤ ε) {N : ℕ} (hN : 64 ≤ N) (hx : 1 ≤ (N : ℝ) * ε)
    (hεN : ε * Real.log N ≤ 1 / 40)
    (hA : 804 * ((N : ℝ) * ε) * Real.log ((N : ℝ) * ε + 2) ≤ N) :
    (modeH ε N : ℝ) ≤ 15400 * ((N : ℝ) * ε) * Real.log ((N : ℝ) * ε + 1) ^ 2 := by
  have h := lem_B5_strong h0 hN hx hεN hA
  set x := (N : ℝ) * ε with hxdef
  set L2 := Real.log (x + 2) with hL2
  set ℓ := ⌈200 * x * L2⌉₊ with hℓdef
  have hL21 : 1 ≤ L2 := one_le_log_three.trans (Real.log_le_log (by norm_num) (by linarith))
  have hxL : 1 ≤ x * L2 := by nlinarith
  have hx0 : 0 < x := by linarith
  have hℓlt : (ℓ : ℝ) < 200 * x * L2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hℓge : 200 * x * L2 ≤ ℓ := Nat.le_ceil _
  have hℓ1 : (1 : ℝ) ≤ ℓ := by nlinarith
  -- `H_ℓ ≤ 1 + log ℓ ≤ 9 L2`
  have hH : (harmonic ℓ : ℝ) ≤ 9 * L2 := by
    have h1 := harmonic_le_one_add_log ℓ
    have h2 : Real.log ℓ ≤ Real.log (201 * x * L2) := Real.log_le_log (by linarith) (by nlinarith)
    have h3 : Real.log (201 * x * L2) ≤ 6 + L2 + L2 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hx0.ne']
      have := log_201_le
      have : Real.log x ≤ L2 := Real.log_le_log hx0 (by linarith)
      have : Real.log L2 ≤ L2 := Real.log_le_self (by linarith)
      linarith
    linarith
  -- `L2 ≤ 2 log(x+1)`
  have hL2le : L2 ≤ 2 * Real.log (x + 1) := by
    have e : Real.log ((x + 1) ^ 2) = 2 * Real.log (x + 1) := by rw [Real.log_pow]; norm_num
    rw [hL2, ← e]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hH0 : (0 : ℝ) ≤ (harmonic ℓ : ℝ) := by exact_mod_cast (harmonic_pos (by
    have : (1 : ℝ) ≤ ℓ := hℓ1
    have : 1 ≤ ℓ := by exact_mod_cast this
    omega)).le
  have hstep1 : ((ℓ : ℝ) + 1) * (1 + 2 * (harmonic ℓ : ℝ)) ≤ (202 * x * L2) * (19 * L2) := by
    apply mul_le_mul (by nlinarith) (by nlinarith) (by positivity) (by positivity)
  have hlog1 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
  have hstep2 : (202 * x * L2) * (19 * L2) ≤ 15400 * x * Real.log (x + 1) ^ 2 := by
    have : L2 ^ 2 ≤ 4 * Real.log (x + 1) ^ 2 := by nlinarith
    nlinarith
  linarith

/-- **Lemma B.5 (`lem:B-mode`), in the paper's form** with `c̄ = 1/40` and `A₀ = 15400`: if
`ε log N ≤ c̄` and `A₀ x log(x+2) ≤ N/4`, then `m_h ≤ A₀ x log²(x+1)` (under (H) without
`ε ≤ 1/4`, which follows). -/
theorem lem_B_mode_paper {ε : ℝ} (h0 : 0 ≤ ε) {N : ℕ} (hN : 64 ≤ N) (hx : 1 ≤ (N : ℝ) * ε)
    (hεN : ε * Real.log N ≤ 1 / 40)
    (hA : 15400 * ((N : ℝ) * ε) * Real.log ((N : ℝ) * ε + 2) ≤ (N : ℝ) / 4) :
    (modeH ε N : ℝ) ≤ 15400 * ((N : ℝ) * ε) * Real.log ((N : ℝ) * ε + 1) ^ 2 := by
  refine lem_B_mode h0 hN hx hεN ?_
  have hL : 0 ≤ Real.log ((N : ℝ) * ε + 2) := Real.log_nonneg (by linarith)
  have : 0 ≤ ((N : ℝ) * ε) * Real.log ((N : ℝ) * ε + 2) := by positivity
  nlinarith

end Kagey131.PaperD
