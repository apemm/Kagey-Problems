import PaperA.PeriodicCrossing
import PaperA.Edge

/-!
# Theorems `thm:allbin-expansion` and `thm:edge-matching`: the expansions of the Bessel roots
-/

namespace Kagey131

open Filter

/-- `C(η) = (1/2) log(8π) - log(1 + η)`. -/
noncomputable def Ceta (η : ℝ) : ℝ := Real.log (8 * Real.pi) / 2 - Real.log (1 + η)

/-- `B(η) = (3 - η)/(8(1 + η))`. -/
noncomputable def Beta (η : ℝ) : ℝ := (3 - η) / (8 * (1 + η))

/-- The main terms `ℓ - (1/2) log ℓ + C + ((1/4) log ℓ - C/2 + B)/ℓ` of Theorem 4.9. -/
noncomputable def rootMain (ℓ η : ℝ) : ℝ :=
  ℓ - Real.log ℓ / 2 + Ceta η + (Real.log ℓ / 4 - Ceta η / 2 + Beta η) / ℓ

theorem log_eight_pi_bounds : 2 ≤ Real.log (8 * Real.pi) ∧ Real.log (8 * Real.pi) ≤ 4 := by
  have hp := Real.pi_gt_three
  have hp4 := Real.pi_lt_four
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  have h8 : (0 : ℝ) < 8 * Real.pi := by positivity
  constructor
  · rw [Real.le_log_iff_exp_le h8]
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h1 : Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he.le 2
    nlinarith
  · rw [Real.log_le_iff_le_exp h8]
    have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h1 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
      pow_le_pow_left₀ (by norm_num) he'.le 4
    nlinarith

theorem Ceta_bounds {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) : 0 ≤ Ceta η ∧ Ceta η ≤ 2 := by
  obtain ⟨h1, h2⟩ := log_eight_pi_bounds
  have l0 : 0 ≤ Real.log (1 + η) := Real.log_nonneg (by linarith)
  have l1 : Real.log (1 + η) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
  have l2 := Real.log_two_lt_d9
  unfold Ceta
  constructor <;> linarith

theorem Beta_bounds {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) : 0 ≤ Beta η ∧ Beta η ≤ 3 / 8 := by
  unfold Beta
  have h : 0 < 8 * (1 + η) := by linarith
  constructor
  · exact div_nonneg (by linarith) h.le
  · rw [div_le_iff₀ h]; nlinarith

/-- The `t` of the Bessel factor: if `|m - ((1+η) - (3-η)/(8z))| ≤ 22/z²` and `z ≥ 100`, then
`m/(1+η) = 1 + t` with `t = -B(η)/z + e`, `|e| ≤ 22/z²` and `|t| ≤ 1/z`. -/
theorem bessel_factor {η z m : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hz : 100 ≤ z)
    (hm : |m - ((1 + η) - (3 - η) / (8 * z))| ≤ 22 / z ^ 2) :
    ∃ e : ℝ, m / (1 + η) - 1 = -Beta η / z + e ∧ |e| ≤ 22 / z ^ 2 ∧
      |m / (1 + η) - 1| ≤ 1 / z := by
  have hz0 : 0 < z := by linarith
  have h1η : 0 < 1 + η := by linarith
  set e := (m - ((1 + η) - (3 - η) / (8 * z))) / (1 + η) with he
  refine ⟨e, ?_, ?_, ?_⟩
  · rw [he]; unfold Beta; field_simp; ring
  · rw [he, abs_div, abs_of_pos h1η, div_le_iff₀ h1η]
    have hp : 0 ≤ 22 / z ^ 2 := by positivity
    nlinarith
  · have heq : m / (1 + η) - 1 = -Beta η / z + e := by rw [he]; unfold Beta; field_simp; ring
    rw [heq]
    obtain ⟨hB0, hB1⟩ := Beta_bounds hη0 hη1
    have he1 : |e| ≤ 22 / z ^ 2 := by
      rw [he, abs_div, abs_of_pos h1η, div_le_iff₀ h1η]
      have hp : 0 ≤ 22 / z ^ 2 := by positivity
      nlinarith
    have hBz : |-Beta η / z| ≤ 3 / 8 / z := by
      rw [abs_div, abs_neg, abs_of_nonneg hB0, abs_of_pos hz0]
      exact div_le_div_of_nonneg_right hB1 hz0.le
    have h22 : 22 / z ^ 2 ≤ 5 / 8 / z := by
      rw [div_le_div_iff₀ (by positivity) hz0]; nlinarith
    have e3 : 3 / 8 / z + 5 / 8 / z = 1 / z := by field_simp; norm_num
    calc _ ≤ |-Beta η / z| + |e| := abs_add_le _ _
      _ ≤ 1 / z := by linarith

/-- `log(8π) = 3 log 2 + log π`. -/
theorem log_eight_pi : Real.log (8 * Real.pi) = 3 * Real.log 2 + Real.log Real.pi := by
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  push_cast; ring

/-- **The Bessel root equation.** If `0 ≤ η ≤ 1`, `z ≥ 100` and `G_η(z/2) = A`, then
`z + (1/2) log z = log A + C(η) + B(η)/z + ω` with `|ω| ≤ 24/z²`. -/
theorem bessel_root_eq {η z A : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hz : 100 ≤ z)
    (hA : Geta η (z / 2) = A) :
    ∃ ω : ℝ, z + Real.log z / 2 = Real.log A + Ceta η + Beta η / z + ω ∧ |ω| ≤ 24 / z ^ 2 := by
  have hz0 : 0 < z := by linarith
  have h1η : 0 < 1 + η := by linarith
  have hsq : 0 < Real.sqrt (2 * Real.pi * z) := Real.sqrt_pos.mpr (by positivity)
  set m := Real.sqrt (2 * Real.pi * z) * Real.exp (-z) * (besselI1 z + η * besselI0 z) with hmdef
  have hm := besselI1_add_eta_I0_asymp (show 1 ≤ z by linarith) hη0 hη1
  rw [← hmdef] at hm
  obtain ⟨e, ht, he, htb⟩ := bessel_factor hη0 hη1 hz hm
  set t := m / (1 + η) - 1 with htdef
  have hthalf : |t| ≤ 1 / 2 := by
    have : 1 / z ≤ 1 / 2 := by rw [div_le_div_iff₀ hz0 (by norm_num)]; linarith
    linarith
  have h1t : 0 < 1 + t := by have := abs_le.mp hthalf; linarith
  have hmeq : m = (1 + η) * (1 + t) := by rw [htdef]; field_simp; ring
  have hm0 : 0 < m := by rw [hmeq]; positivity
  -- `I_1 + η I_0 = m e^z/√(2πz)`
  have hI : besselI1 z + η * besselI0 z = m * Real.exp z / Real.sqrt (2 * Real.pi * z) := by
    rw [hmdef, eq_div_iff hsq.ne']
    have h1 : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
    have h2 : Real.sqrt (2 * Real.pi * z) * Real.exp (-z) * (besselI1 z + η * besselI0 z) *
        Real.exp z = Real.sqrt (2 * Real.pi * z) * (besselI1 z + η * besselI0 z) *
        (Real.exp (-z) * Real.exp z) := by ring
    rw [h2, h1, mul_one, mul_comm]
  have hG : A = z / 2 * (m * Real.exp z / Real.sqrt (2 * Real.pi * z)) := by
    rw [← hA, ← hI]; unfold Geta; rw [show 2 * (z / 2) = z by ring]; ring
  have hlogA : Real.log A = Real.log z - Real.log 2 + (Real.log (1 + η) + Real.log (1 + t)) + z -
      (Real.log 2 + Real.log Real.pi + Real.log z) / 2 := by
    rw [hG, Real.log_mul (by positivity) (by positivity), Real.log_div hz0.ne' (by norm_num),
      Real.log_div (by positivity) hsq.ne', Real.log_mul hm0.ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_sqrt (by positivity), Real.log_mul (by positivity) hz0.ne',
      Real.log_mul (by norm_num) Real.pi_pos.ne', hmeq, Real.log_mul h1η.ne' h1t.ne']
    ring
  refine ⟨-(Real.log (1 + t) - t) - e, ?_, ?_⟩
  · rw [hlogA]
    unfold Ceta
    rw [log_eight_pi]
    have : t = -Beta η / z + e := ht
    rw [this]
    field_simp
    ring
  · have hr := abs_log_one_add_sub_le hthalf
    have ht2 : 2 * t ^ 2 ≤ 2 / z ^ 2 := by
      have : t ^ 2 ≤ (1 / z) ^ 2 := by rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) htb 2
      have e2 : (1 / z) ^ 2 = 1 / z ^ 2 := by ring
      have e3 : 2 / z ^ 2 = 2 * (1 / z ^ 2) := by ring
      rw [e3]; linarith
    have e4 : 2 / z ^ 2 + 22 / z ^ 2 = 24 / z ^ 2 := by ring
    calc |-(Real.log (1 + t) - t) - e| ≤ |-(Real.log (1 + t) - t)| + |e| := abs_sub _ _
      _ = |Real.log (1 + t) - t| + |e| := by rw [abs_neg]
      _ ≤ 24 / z ^ 2 := by linarith

/-- **The expansion of the Bessel root**, uniformly in `0 ≤ η ≤ 1`: there are `K` and `A₀` with
`|2x̂ - (ℓ - (1/2) log ℓ + C(η) + ((1/4) log ℓ - C(η)/2 + B(η))/ℓ)| ≤ K (log ℓ)²/ℓ²` for all
`A ≥ A₀`, where `G_η(x̂) = A` and `ℓ = log A`. -/
theorem bessel_root_expansion :
    ∃ K A₀ : ℝ, 0 < K ∧ 0 < A₀ ∧ ∀ η A : ℝ, 0 ≤ η → η ≤ 1 → A₀ ≤ A →
      |2 * Groot η A - rootMain (Real.log A) η| ≤
        K * (Real.log (Real.log A) ^ 2 / Real.log A ^ 2) := by
  obtain ⟨CK, hCK, hinv⟩ := log_inversion (K := 2) (by norm_num)
  have hG50 : 0 < Geta 1 50 := Geta_pos (by norm_num) (by norm_num)
  refine ⟨CK * 97, max (Geta 1 50 + 1) (Real.exp 16), by positivity,
    lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro η A h0 h1 hA
  have hA1 : Geta 1 50 + 1 ≤ A := le_trans (le_max_left _ _) hA
  have hA2 : Real.exp 16 ≤ A := le_trans (le_max_right _ _) hA
  have hApos : 0 < A := by linarith
  obtain ⟨hx0, hxA⟩ := Groot_spec h0 hApos
  set x := Groot η A with hxdef
  have hx50 : 50 ≤ x := by
    by_contra h
    push Not at h
    have hm := Geta_strictMonoOn h0 h1 (Set.mem_Ici.mpr hx0.le) (Set.mem_Ici.mpr (by norm_num)) h
    have hle : Geta η 50 ≤ Geta 1 50 := by
      unfold Geta
      have := one_le_besselI0 (50 : ℝ)
      nlinarith
    linarith
  have hz : (100 : ℝ) ≤ 2 * x := by linarith
  have hGz : Geta η (2 * x / 2) = A := by rw [show 2 * x / 2 = x by ring]; exact hxA
  obtain ⟨ω, heq, hω⟩ := bessel_root_eq h0 h1 hz hGz
  set z := 2 * x with hzdef
  set ℓ := Real.log A with hℓdef
  have hz0 : 0 < z := by linarith
  have hℓ16 : 16 ≤ ℓ := by rw [hℓdef, Real.le_log_iff_exp_le hApos]; exact hA2
  have hω1 : |ω| ≤ 1 := by
    have : 24 / z ^ 2 ≤ 1 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  obtain ⟨hC0, hC2⟩ := Ceta_bounds h0 h1
  obtain ⟨hB0, hB1⟩ := Beta_bounds h0 h1
  have hCa : |Ceta η| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hBa : |Beta η| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have h := hinv z ℓ (Ceta η) (Beta η) ω (by linarith) (by linarith) hCa hBa hω1 heq
  -- `z ≥ ℓ/2`
  have hzℓ : ℓ / 2 ≤ z := by
    have hlz : Real.log z ≤ z - 1 := Real.log_le_sub_one_of_pos hz0
    have hBz : 0 ≤ Beta η / z := div_nonneg hB0 hz0.le
    have := abs_le.mp hω1
    linarith
  have hω2 : |ω| ≤ 96 / ℓ ^ 2 := by
    have h4 : 24 / z ^ 2 ≤ 96 / ℓ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : ℓ ^ 2 ≤ 4 * z ^ 2 := by nlinarith
      linarith
    linarith
  have hlogℓ : 1 ≤ Real.log ℓ := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hq : 96 / ℓ ^ 2 ≤ 96 * (Real.log ℓ ^ 2 / ℓ ^ 2) := by
    rw [mul_div_assoc']
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have e : 2 * x - rootMain ℓ η =
      z - ℓ + Real.log ℓ / 2 - Ceta η - (Real.log ℓ / 4 - Ceta η / 2 + Beta η) / ℓ := by
    unfold rootMain; rw [hzdef]; ring
  rw [e]
  have hfin : CK * (Real.log ℓ ^ 2 / ℓ ^ 2 + |ω|) ≤ CK * 97 * (Real.log ℓ ^ 2 / ℓ ^ 2) := by
    have : Real.log ℓ ^ 2 / ℓ ^ 2 + |ω| ≤ 97 * (Real.log ℓ ^ 2 / ℓ ^ 2) := by linarith
    calc CK * (Real.log ℓ ^ 2 / ℓ ^ 2 + |ω|) ≤ CK * (97 * (Real.log ℓ ^ 2 / ℓ ^ 2)) :=
          mul_le_mul_of_nonneg_left this hCK.le
      _ = CK * 97 * (Real.log ℓ ^ 2 / ℓ ^ 2) := by ring
  linarith

/-- The facts about `s = √(ab)`, `A = ab/(a+b)` and `x = s u_{a,b}` used for Theorem 4.9: if
`3 ≤ a ≤ b`, `2 s u_{a,b} < (3/2) log a` and `(log a)² ≤ a/8`, then
`|2x - 2x̂| ≤ 4 (log a)²/a`, where `G_η(x̂) = A`. -/
theorem allbin_root_close {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b)
    (hlead : 2 * Real.sqrt ((a : ℝ) * b) * uab a b < 3 / 2 * Real.log a)
    (hsmall : Real.log a ^ 2 ≤ 1 / 8 * a) :
    |2 * (Real.sqrt ((a : ℝ) * b) * uab a b) -
      2 * Groot (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b)) ((a : ℝ) * b / (a + b))| ≤
      4 * (Real.log a ^ 2 / a) := by
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hrb := allbin_root_bound a b ha1 hb1
  simp only at hrb
  set s := Real.sqrt ((a : ℝ) * b) with hsdef
  set A := (a : ℝ) * b / (a + b) with hAdef
  set η := 2 * s / ((a : ℝ) + b) with hηdef
  set x := s * uab a b with hxdef
  have ha' : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have ha0 : (0 : ℝ) < a := by linarith
  have hsa : (a : ℝ) ≤ s := by
    rw [hsdef]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hs0 : 0 < s := by linarith
  have hAa : (a : ℝ) / 2 ≤ A := by
    rw [hAdef, div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
  have hA0 : 0 < A := by linarith
  have hu := uab_pos ha1 hb1
  have hx0 : 0 < x := by positivity
  have hla : 1 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le ha0]; have := Real.exp_one_lt_d9; linarith
  have hxl : x ≤ Real.log a := by
    have : 2 * x < 3 / 2 * Real.log a := by rw [hxdef, ← mul_assoc]; exact hlead
    linarith
  set δ := x ^ 2 / (2 * A) + x / s with hδdef
  have hδ1 : x ^ 2 / (2 * A) ≤ Real.log a ^ 2 / a := by
    rw [div_le_div_iff₀ (by positivity) ha0]
    have h1 : x ^ 2 ≤ Real.log a ^ 2 := pow_le_pow_left₀ hx0.le hxl 2
    have h2 : x ^ 2 * a ≤ Real.log a ^ 2 * a := mul_le_mul_of_nonneg_right h1 ha0.le
    have h3 : Real.log a ^ 2 * a ≤ Real.log a ^ 2 * (2 * A) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hδ2 : x / s ≤ Real.log a ^ 2 / a := by
    rw [div_le_div_iff₀ hs0 ha0]
    have h1 : x * a ≤ Real.log a * a := mul_le_mul_of_nonneg_right hxl ha0.le
    have h2 : Real.log a ≤ Real.log a ^ 2 := by nlinarith
    have h3 : Real.log a ^ 2 * a ≤ Real.log a ^ 2 * s :=
      mul_le_mul_of_nonneg_left hsa (by positivity)
    nlinarith
  have hδ : δ ≤ 2 * (Real.log a ^ 2 / a) := by rw [hδdef]; linarith
  have hδq : 2 * (Real.log a ^ 2 / a) ≤ 1 / 4 := by
    rw [mul_div_assoc', div_le_iff₀ ha0]; linarith
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  obtain ⟨hlow, hup⟩ := hrb
  have hd := hup (by linarith)
  have hlog := neg_log_one_sub_le_two hδ0 (by linarith)
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **Theorem 4.9** (`thm:allbin-expansion`, `eq:allbin-expansion`). With `s = √(ab)`,
`A = ab/(a+b)`, `η = 2s/(a+b)` and `ℓ = log A`, there are `K` and `a₀` such that for all
`a ≥ a₀` and all `b ≥ a`,
`|2s u_{a,b} - (ℓ - (1/2) log ℓ + C(η) + ((1/4) log ℓ - C(η)/2 + B(η))/ℓ)| ≤
K ((log ℓ)²/ℓ² + (log a)²/a)`. -/
theorem allbin_expansion :
    ∃ K : ℝ, 0 < K ∧ ∃ a₀ : ℕ, ∀ a b : ℕ, a₀ ≤ a → a ≤ b →
      |2 * Real.sqrt ((a : ℝ) * b) * uab a b -
        rootMain (Real.log ((a : ℝ) * b / (a + b))) (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b))| ≤
        K * (Real.log (Real.log ((a : ℝ) * b / (a + b))) ^ 2 / Real.log ((a : ℝ) * b / (a + b)) ^ 2 +
          Real.log a ^ 2 / a) := by
  obtain ⟨K, A₀, hK, hA₀, hexp⟩ := bessel_root_expansion
  obtain ⟨a₁, hlead⟩ := allbin_leading (ε := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨a₂, ha₂⟩ := eventually_atTop.mp (eventually_log_pow_le 2 (c := 1 / 8) (by norm_num))
  obtain ⟨a₃, ha₃⟩ := exists_nat_ge (2 * A₀)
  refine ⟨K + 4, by linarith, max (max a₁ a₂) (max a₃ 3), ?_⟩
  intro a b ha hab
  have ha1 : a₁ ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
  have ha2 : a₂ ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha
  have ha3 : a₃ ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ha
  have ha4 : 3 ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ha
  have hl := (hlead a b ha1 hab).2
  have hl' : 2 * Real.sqrt ((a : ℝ) * b) * uab a b < 3 / 2 * Real.log a := by
    have e : (1 + 1 / 2 : ℝ) = 3 / 2 := by norm_num
    rw [← e]; exact hl
  have hclose := allbin_root_close ha4 hab hl' (ha₂ a ha2)
  have ha' : (3 : ℝ) ≤ a := by exact_mod_cast ha4
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hAa : (a : ℝ) / 2 ≤ (a : ℝ) * b / (a + b) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
  have hA₀a : A₀ ≤ (a : ℝ) * b / (a + b) := by
    have : (a₃ : ℝ) ≤ a := by exact_mod_cast ha3
    linarith
  obtain ⟨hη0, hη1⟩ := eta_le_one a b (by omega) (by omega)
  have he := hexp _ _ hη0 hη1 hA₀a
  set M := rootMain (Real.log ((a : ℝ) * b / (a + b))) (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b))
  set G := Groot (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b)) ((a : ℝ) * b / (a + b))
  set P := Real.log (Real.log ((a : ℝ) * b / (a + b))) ^ 2 / Real.log ((a : ℝ) * b / (a + b)) ^ 2
  set Q := Real.log a ^ 2 / a
  have hP : 0 ≤ P := by positivity
  have hQ : 0 ≤ Q := by positivity
  have e : 2 * Real.sqrt ((a : ℝ) * b) * uab a b - M =
      (2 * (Real.sqrt ((a : ℝ) * b) * uab a b) - 2 * G) + (2 * G - M) := by ring
  rw [e]
  calc _ ≤ |2 * (Real.sqrt ((a : ℝ) * b) * uab a b) - 2 * G| + |2 * G - M| := abs_add_le _ _
    _ ≤ 4 * Q + K * P := add_le_add hclose he
    _ ≤ (K + 4) * (P + Q) := by nlinarith

/-- **Theorem 4.9** for `1 - p_{a,b}`: the same expansion holds for `2s(1 - p_{a,b})`. -/
theorem allbin_expansion_prob :
    ∃ K : ℝ, 0 < K ∧ ∃ a₀ : ℕ, ∀ a b : ℕ, a₀ ≤ a → a ≤ b →
      |2 * Real.sqrt ((a : ℝ) * b) * (1 - pab a b) -
        rootMain (Real.log ((a : ℝ) * b / (a + b))) (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b))| ≤
        K * (Real.log (Real.log ((a : ℝ) * b / (a + b))) ^ 2 / Real.log ((a : ℝ) * b / (a + b)) ^ 2 +
          Real.log a ^ 2 / a) := by
  obtain ⟨K, hK, a₀, h⟩ := allbin_expansion
  obtain ⟨a₁, hlead⟩ := allbin_leading (ε := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨K + 2, by linarith, max (max a₀ a₁) 3, ?_⟩
  intro a b ha hab
  have ha0 : a₀ ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
  have ha1 : a₁ ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha
  have ha3 : 3 ≤ a := le_trans (le_max_right _ _) ha
  have hm := h a b ha0 hab
  have hl := (hlead a b ha1 hab).2
  have ha' : (3 : ℝ) ≤ a := by exact_mod_cast ha3
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have ha0' : (0 : ℝ) < a := by linarith
  set s := Real.sqrt ((a : ℝ) * b) with hsdef
  have hsa : (a : ℝ) ≤ s := by
    rw [hsdef]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hs0 : 0 < s := by linarith
  have hu := uab_pos (a := a) (b := b) (by omega) (by omega)
  set u := uab a b with hudef
  have hla : 1 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le ha0']; have := Real.exp_one_lt_d9; linarith
  have hxl : s * u ≤ Real.log a := by
    have : 2 * s * u < (1 + 1 / 2) * Real.log a := hl
    nlinarith
  -- `|2s(1-p) - 2su| = 2su²/(1+u) ≤ 2(su)²/s ≤ 2 (log a)²/a`
  have hp : 1 - pab a b = u / (1 + u) := by
    unfold pab; rw [← hudef]; field_simp; ring
  have hdiff : |2 * s * (1 - pab a b) - 2 * s * u| ≤ 2 * (Real.log a ^ 2 / a) := by
    rw [hp]
    have e : 2 * s * (u / (1 + u)) - 2 * s * u = -(2 * s * u ^ 2 / (1 + u)) := by
      field_simp; ring
    rw [e, abs_neg, abs_of_nonneg (by positivity)]
    have h1 : 2 * s * u ^ 2 / (1 + u) ≤ 2 * s * u ^ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [mul_pos hs0 (pow_pos hu 2)]
    have h2 : 2 * s * u ^ 2 = 2 * ((s * u) ^ 2 / s) := by field_simp
    have h3 : (s * u) ^ 2 / s ≤ Real.log a ^ 2 / a := by
      rw [div_le_div_iff₀ hs0 ha0']
      have h4 : (s * u) ^ 2 ≤ Real.log a ^ 2 := pow_le_pow_left₀ (by positivity) hxl 2
      have h5 : (s * u) ^ 2 * a ≤ Real.log a ^ 2 * a := mul_le_mul_of_nonneg_right h4 ha0'.le
      have h6 : Real.log a ^ 2 * a ≤ Real.log a ^ 2 * s := mul_le_mul_of_nonneg_left hsa (by positivity)
      linarith
    linarith
  set M := rootMain (Real.log ((a : ℝ) * b / (a + b))) (2 * s / ((a : ℝ) + b))
  set P := Real.log (Real.log ((a : ℝ) * b / (a + b))) ^ 2 / Real.log ((a : ℝ) * b / (a + b)) ^ 2
  set Q := Real.log a ^ 2 / a
  have hP : 0 ≤ P := by positivity
  have hQ : 0 ≤ Q := by positivity
  have e : 2 * s * (1 - pab a b) - M = (2 * s * (1 - pab a b) - 2 * s * u) + (2 * s * u - M) := by
    ring
  rw [e]
  calc _ ≤ |2 * s * (1 - pab a b) - 2 * s * u| + |2 * s * u - M| := abs_add_le _ _
    _ ≤ 2 * Q + K * (P + Q) := add_le_add hdiff hm
    _ ≤ (K + 2) * (P + Q) := by nlinarith

/-- For large `a`, `a H_a((log a)²/a) > a`, so the edge root satisfies `a y_a < (log a)²`. -/
theorem edge_root_small {a : ℕ} (ha : 1 ≤ a) (hl : 13 ≤ Real.log a) (ha8 : (8 : ℝ) ≤ a)
    (hsm : Real.log a ^ 2 ≤ a) :
    (a : ℝ) * yEdge a < Real.log a ^ 2 := by
  have ha0 : (0 : ℝ) < a := by linarith
  set x := Real.log a with hxdef
  have hx0 : 0 < x := by linarith
  obtain ⟨h0, h1⟩ := edge_matching a ha hx0
  have hI : Real.exp (2 * x) / (2 * Real.sqrt (2 * Real.pi * (2 * x))) ≤ besselI1 (2 * x) :=
    besselI1_ge_half (by linarith)
  have hexp : Real.exp (2 * x) = (a : ℝ) ^ 2 := by
    rw [hxdef, show 2 * Real.log a = Real.log ((a : ℝ) ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  have hsq : Real.sqrt (2 * Real.pi * (2 * x)) ≤ x := by
    rw [Real.sqrt_le_left (by linarith)]
    have := Real.pi_lt_d2
    nlinarith
  have hsq0 : 0 < Real.sqrt (2 * Real.pi * (2 * x)) := Real.sqrt_pos.mpr (by positivity)
  -- `x I_1(2x) ≥ a²/2 ≥ 4a`
  have hxI : (a : ℝ) ^ 2 / 2 ≤ x * besselI1 (2 * x) := by
    have h2 : (a : ℝ) ^ 2 / (2 * x) ≤ besselI1 (2 * x) := by
      rw [hexp] at hI
      calc (a : ℝ) ^ 2 / (2 * x) ≤ (a : ℝ) ^ 2 / (2 * Real.sqrt (2 * Real.pi * (2 * x))) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
        _ ≤ _ := hI
    have := mul_le_mul_of_nonneg_left h2 hx0.le
    have e : x * ((a : ℝ) ^ 2 / (2 * x)) = (a : ℝ) ^ 2 / 2 := by field_simp
    linarith
  have hpos : 0 < x * besselI1 (2 * x) := by
    have := besselI1_pos (show 0 < x by linarith); positivity
  have hH : (a : ℝ) < a * Hedge a (x ^ 2 / a) := by
    have h1' : 1 - x ^ 2 / (2 * a) ≤ a * Hedge a (x ^ 2 / a) / (x * besselI1 (2 * x)) := by linarith
    rw [le_div_iff₀ hpos] at h1'
    have hhalf : 1 / 2 ≤ 1 - x ^ 2 / (2 * a) := by
      rw [show x ^ 2 / (2 * a) = x ^ 2 / a / 2 by ring]
      have : x ^ 2 / a ≤ 1 := by rw [div_le_one ha0]; exact hsm
      linarith
    have h4a : 4 * (a : ℝ) ≤ (a : ℝ) ^ 2 / 2 := by nlinarith
    nlinarith
  have hH1 : 1 < Hedge a (x ^ 2 / a) := by
    by_contra h; push Not at h
    have := mul_le_mul_of_nonneg_left h ha0.le
    linarith
  obtain ⟨hy0, -, hy1⟩ := yEdge_spec ha
  have hlt : yEdge a < x ^ 2 / a := by
    by_contra h; push Not at h
    have hm := (Hedge_strictMonoOn ha).monotoneOn (Set.mem_Ici.mpr (by positivity))
      (Set.mem_Ici.mpr hy0.le) h
    linarith
  rw [lt_div_iff₀ ha0] at hlt
  linarith

/-- **Theorem 4.11** (`thm:edge-matching`, `eq:edge-matching-expansion`). With `ℓ = log a`, there
is `K` with, for all large `a`,
`|2√(a y_a) - (ℓ - (1/2) log ℓ + C(0) + ((1/4) log ℓ - C(0)/2 + 3/8)/ℓ)| ≤
K ((log ℓ)²/ℓ² + (log a)²/a)`, where `C(0) = (1/2) log(8π)`. -/
theorem edge_matching_expansion :
    ∃ K : ℝ, 0 < K ∧ ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a →
      |2 * Real.sqrt ((a : ℝ) * yEdge a) - rootMain (Real.log a) 0| ≤
        K * (Real.log (Real.log a) ^ 2 / Real.log a ^ 2 + Real.log a ^ 2 / a) := by
  obtain ⟨K, A₀, hK, hA₀, hexp⟩ := bessel_root_expansion
  obtain ⟨a₂, ha₂⟩ := eventually_atTop.mp (eventually_log_pow_le 2 (c := 1 / 8) (by norm_num))
  obtain ⟨a₃, ha₃⟩ := exists_nat_ge (A₀ + Real.exp 13 + 8)
  refine ⟨K + 1, by linarith, max a₂ a₃, ?_⟩
  intro a ha
  have ha2 : a₂ ≤ a := le_trans (le_max_left _ _) ha
  have ha3 : a₃ ≤ a := le_trans (le_max_right _ _) ha
  have ha3' : A₀ + Real.exp 13 + 8 ≤ (a : ℝ) := le_trans ha₃ (by exact_mod_cast ha3)
  have he13 := Real.exp_pos 13
  have ha8 : (8 : ℝ) ≤ a := by linarith
  have ha0 : (0 : ℝ) < a := by linarith
  have ha1 : 1 ≤ a := by exact_mod_cast (show (1 : ℝ) ≤ a by linarith)
  have hl13 : 13 ≤ Real.log a := by rw [Real.le_log_iff_exp_le ha0]; linarith
  have hsm8 := ha₂ a ha2
  have hsm : Real.log a ^ 2 ≤ a := by linarith
  have hya := edge_root_small ha1 hl13 ha8 hsm
  obtain ⟨hy0, -, hy1⟩ := yEdge_spec ha1
  set ω := Real.sqrt ((a : ℝ) * yEdge a) with hωdef
  have hω0 : 0 < ω := Real.sqrt_pos.mpr (by positivity)
  have hω2 : ω ^ 2 = (a : ℝ) * yEdge a := Real.sq_sqrt (by positivity)
  have hωl : ω ^ 2 ≤ Real.log a ^ 2 := by linarith
  obtain ⟨h0, h1⟩ := edge_matching a ha1 hω0
  have hHy : Hedge a (ω ^ 2 / a) = 1 := by rw [hω2, mul_div_cancel_left₀ _ ha0.ne']; exact hy1
  rw [hHy, mul_one] at h0 h1
  have hG : Geta 0 ω = ω * besselI1 (2 * ω) := by unfold Geta; ring
  have hIpos : 0 < ω * besselI1 (2 * ω) := by have := besselI1_pos hω0; positivity
  set δ := ω ^ 2 / (2 * a) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hδq : δ ≤ 1 / 16 := by
    rw [hδdef, div_le_iff₀ (by positivity)]; linarith
  have hlow : (a : ℝ) ≤ Geta 0 ω := by
    rw [hG]
    have : (a : ℝ) / (ω * besselI1 (2 * ω)) ≤ 1 := by linarith
    rwa [div_le_one hIpos] at this
  have hup : Geta 0 ω ≤ a / (1 - δ) := by
    rw [hG, le_div_iff₀ (by linarith)]
    have : 1 - δ ≤ a / (ω * besselI1 (2 * ω)) := by linarith
    rw [le_div_iff₀ hIpos] at this
    linarith
  obtain ⟨hcl, hcu⟩ := root_comparison (le_refl 0) zero_le_one ha0 hω0 hlow
  have hd := hcu δ (by linarith) hup
  have hlog := neg_log_one_sub_le_two hδ0 (by linarith)
  have hclose : |2 * ω - 2 * Groot 0 a| ≤ Real.log a ^ 2 / a := by
    rw [abs_of_nonneg (by linarith)]
    have : δ ≤ Real.log a ^ 2 / (2 * a) := by
      rw [hδdef]; exact div_le_div_of_nonneg_right hωl (by positivity)
    have e : Real.log a ^ 2 / (2 * a) = Real.log a ^ 2 / a / 2 := by ring
    linarith
  have hA : A₀ ≤ (a : ℝ) := by linarith
  have he := hexp 0 a (le_refl 0) zero_le_one hA
  set P := Real.log (Real.log a) ^ 2 / Real.log a ^ 2
  set Q := Real.log a ^ 2 / a
  have hP : 0 ≤ P := by positivity
  have hQ : 0 ≤ Q := by positivity
  have e : 2 * ω - rootMain (Real.log a) 0 = (2 * ω - 2 * Groot 0 a) + (2 * Groot 0 a - rootMain (Real.log a) 0) := by
    ring
  rw [e]
  calc _ ≤ |2 * ω - 2 * Groot 0 a| + |2 * Groot 0 a - rootMain (Real.log a) 0| := abs_add_le _ _
    _ ≤ Q + K * P := add_le_add hclose he
    _ ≤ (K + 1) * (P + Q) := by nlinarith

/-- `C(0) = (1/2) log(8π)` and `B(0) = 3/8`, the constants of Theorem 4.11. -/
theorem Ceta_zero_Beta_zero : Ceta 0 = Real.log (8 * Real.pi) / 2 ∧ Beta 0 = 3 / 8 := by
  unfold Ceta Beta; norm_num

end Kagey131
