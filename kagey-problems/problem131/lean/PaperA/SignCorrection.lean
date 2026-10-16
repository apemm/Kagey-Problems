import PaperA.UniformBessel

/-!
# Remark `rem:sign-correction`: the sign of the first correction to the Bessel form

The remark makes the following mathematical claims.

1. The exact weight lies below its Bessel form, so the first correction is negative. For
   `S_{a,b}` this is the lower bound of Theorem `thm:allbin-bessel` (`allbin_bessel`). For the
   hypergeometric sum `₂F₁(-a,-b;1;z) = Σ_n C(a,n) C(b,n) z^n` with `abz = w²` it is
   `hyp2F1neg_le_besselI0`.
2. The clipped products fall short of `1` by about `σ_r = r(r+1)/(2A)`, `A = ab/(a+b)`:
   `σ_r - σ_r²/2 ≤ 1 - U_r V_r ≤ σ_r` for every `r` (`pair_deficit_bounds`).
3. The corrected expansion, with falling factorials: with `A = ab/(a+b)` and `abz = w²`,
   `₂F₁(-a,-b;1;z) = I_0(2w) - (w² I_0(2w) - w I_1(2w))/(2A) + R` with
   `0 ≤ R ≤ M/(8A²)`, `M = Σ_n (n(n-1))² w^{2n}/(n!)²` (`hyp2F1neg_expansion`). The first
   correction is `-w² I_2(2w)/(2A)`, written with `w² I_2(2w) = w² I_0(2w) - w I_1(2w)`. The
   formula with the opposite sign, `I_0(2w) + w² I_2(2w)/(2A)`, is the one the remark attributes
   to Eq. (D.6) of Dantchev, Tonchev and Rudnick.
4. The numbers at `a = b = 200`, `c = 1`, `abz = 25` (so `z = 1/1600`, `w = 5`, `A = 100`): the
   exact value is `9.5` percent below `I_0(10)` (between `9.45` and `9.55` percent), the
   formula with the plus sign is `10.1` percent above `I_0(10)` (between `10.05` and `10.15`
   percent), and the formula with the minus sign is within `0.8` percent of the exact value
   (`sign_correction_numbers`). The bounds on `I_0(10)`, `I_1(10)` and on the exact sum are
   rational and checked by the kernel.

The statement about the typo in the other paper is not a mathematical claim and is not
formalized.
-/

namespace Kagey131

open Finset

/-! ### The deficit of the clipped products -/

/-- One step of the Bonferroni bound: if `0 ≤ P ≤ 1 - S + S²/2` and `0 ≤ t ≤ 1`, then
`0 ≤ P(1-t) ≤ 1 - (S+t) + (S+t)²/2`. -/
theorem bonferroni_step {P S t : ℝ} (hP0 : 0 ≤ P) (hP : P ≤ 1 - S + S ^ 2 / 2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ P * (1 - t) ∧ P * (1 - t) ≤ 1 - (S + t) + (S + t) ^ 2 / 2 := by
  refine ⟨mul_nonneg hP0 (by linarith), ?_⟩
  have h1 : P * (1 - t) ≤ (1 - S + S ^ 2 / 2) * (1 - t) :=
    mul_le_mul_of_nonneg_right hP (by linarith)
  nlinarith [mul_nonneg (sq_nonneg S) ht0, sq_nonneg t]

/-- `U_{r+1}(m) = U_r(m) (1 - (r+1)/m)` for `r + 1 ≤ m`. -/
theorem normCoeff_self_succ {m : ℕ} (hm : 1 ≤ m) {r : ℕ} (hr : r + 1 ≤ m) :
    normCoeff m m (r + 1) = normCoeff m m r * (1 - ((r : ℝ) + 1) / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [normCoeff_succ m hm0.ne' r]
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub hm]
  field_simp
  push_cast
  ring

/-- Below the support, `0 ≤ U_r(a) V_r(b) ≤ 1 - σ + σ²/2` with
`σ = r(r+1)/2 · (1/a + 1/b)`. -/
theorem pair_product_upper {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∀ r : ℕ, r < a → r < b →
      0 ≤ normCoeff a a r * normCoeff b b r ∧
        normCoeff a a r * normCoeff b b r ≤
          1 - (r : ℝ) * (r + 1) / 2 * (1 / a + 1 / b) +
            ((r : ℝ) * (r + 1) / 2 * (1 / a + 1 / b)) ^ 2 / 2 := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  intro r
  induction r with
  | zero => intro _ _; simp [normCoeff_zero]
  | succ r ih =>
    intro hra hrb
    obtain ⟨h0, h1⟩ := ih (by omega) (by omega)
    set σ : ℝ := (r : ℝ) * (r + 1) / 2 * (1 / a + 1 / b) with hσ
    have hra' : ((r : ℝ) + 1) ≤ a := by exact_mod_cast hra.le
    have hrb' : ((r : ℝ) + 1) ≤ b := by exact_mod_cast hrb.le
    have ta0 : 0 ≤ ((r : ℝ) + 1) / a := by positivity
    have ta1 : ((r : ℝ) + 1) / a ≤ 1 := by rw [div_le_one ha0]; exact hra'
    have tb0 : 0 ≤ ((r : ℝ) + 1) / b := by positivity
    have tb1 : ((r : ℝ) + 1) / b ≤ 1 := by rw [div_le_one hb0]; exact hrb'
    obtain ⟨s0, s1⟩ := bonferroni_step h0 h1 ta0 ta1
    obtain ⟨u0, u1⟩ := bonferroni_step s0 s1 tb0 tb1
    rw [normCoeff_self_succ ha (by omega), normCoeff_self_succ hb (by omega)]
    have e : normCoeff a a r * (1 - ((r : ℝ) + 1) / a) * (normCoeff b b r * (1 - ((r : ℝ) + 1) / b)) =
        normCoeff a a r * normCoeff b b r * (1 - ((r : ℝ) + 1) / a) * (1 - ((r : ℝ) + 1) / b) := by
      ring
    have eσ : σ + ((r : ℝ) + 1) / a + ((r : ℝ) + 1) / b =
        ((r + 1 : ℕ) : ℝ) * (((r + 1 : ℕ) : ℝ) + 1) / 2 * (1 / a + 1 / b) := by
      rw [hσ]; push_cast; field_simp; ring
    rw [e, ← eσ]
    exact ⟨u0, u1⟩

/-- **Remark 4.5, the size of the deficit.** For `a, b ≥ 1`, `A = ab/(a+b)` and every `r`, with
`σ_r = r(r+1)/(2A)`: `σ_r - σ_r²/2 ≤ 1 - U_r V_r ≤ σ_r`. -/
theorem pair_deficit_bounds {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (r : ℕ) :
    (r : ℝ) * (r + 1) / (2 * ((a : ℝ) * b / (a + b))) -
        ((r : ℝ) * (r + 1) / (2 * ((a : ℝ) * b / (a + b)))) ^ 2 / 2 ≤
      1 - normCoeff a a r * normCoeff b b r ∧
    1 - normCoeff a a r * normCoeff b b r ≤ (r : ℝ) * (r + 1) / (2 * ((a : ℝ) * b / (a + b))) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hσ : (r : ℝ) * (r + 1) / (2 * ((a : ℝ) * b / (a + b))) =
      (r : ℝ) * (r + 1) / 2 * (1 / a + 1 / b) := by
    field_simp
    ring
  rw [hσ]
  set σ : ℝ := (r : ℝ) * (r + 1) / 2 * (1 / a + 1 / b) with hσdef
  constructor
  · by_cases h : r < a ∧ r < b
    · have := (pair_product_upper ha hb r h.1 h.2).2
      rw [← hσdef] at this
      linarith
    · have hz : normCoeff a a r * normCoeff b b r = 0 := by
        rcases not_and_or.mp h with h' | h'
        · rw [normCoeff_eq_zero a a (by omega) ha, zero_mul]
        · rw [normCoeff_eq_zero b b (by omega) hb, mul_zero]
      rw [hz]
      nlinarith [sq_nonneg (σ - 1)]
  · obtain ⟨u0, u1, u2⟩ := normCoeff_self_bounds ha r
    obtain ⟨v0, v1, v2⟩ := normCoeff_self_bounds hb r
    obtain ⟨-, -, hp⟩ := prod_deficit u0 u1 v0 v1
    have e : (r : ℝ) * (r + 1) / (2 * a) + (r : ℝ) * (r + 1) / (2 * b) = σ := by
      rw [hσdef]; field_simp
    linarith

/-! ### The hypergeometric sum and its corrected Bessel expansion -/

/-- The terminating hypergeometric sum `₂F₁(-a,-b;1;z) = Σ_{n ≤ a} C(a,n) C(b,n) z^n`. -/
noncomputable def hyp2F1neg (a b : ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ range (a + 1), (a.choose n : ℝ) * (b.choose n : ℝ) * z ^ n

/-- The normalized coefficients of `₂F₁(-a,-b;1;w²/(ab))` against `I_0(2w)`: `1` at `n = 0` and
`U_{n-1}(a) U_{n-1}(b)` for `n ≥ 1`. -/
noncomputable def hypCoeff (a b n : ℕ) : ℝ :=
  if n = 0 then 1 else normCoeff a a (n - 1) * normCoeff b b (n - 1)

/-- `C(m, r+1) (r+1)!/m^(r+1) = U_r(m)`. -/
theorem choose_succ_norm {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    (m.choose (r + 1) : ℝ) * ((r + 1).factorial : ℝ) / (m : ℝ) ^ (r + 1) = normCoeff m m r := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : (m - 1 + 1) * Nat.choose (m - 1) r = Nat.choose (m - 1 + 1) (r + 1) * (r + 1) :=
    Nat.add_one_mul_choose_eq (m - 1) r
  rw [Nat.sub_add_cancel hm] at hc
  have hc' : (m : ℝ) * (Nat.choose (m - 1) r : ℝ) = (m.choose (r + 1) : ℝ) * ((r : ℝ) + 1) := by
    exact_mod_cast hc
  have hc'' : (m.choose (r + 1) : ℝ) = (m : ℝ) * (Nat.choose (m - 1) r : ℝ) / ((r : ℝ) + 1) := by
    rw [eq_div_iff (by positivity)]; linarith
  rw [hc'']
  unfold normCoeff
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- The terms of `₂F₁(-a,-b;1;w²/(ab))` are `hypCoeff a b n · w^{2n}/(n!)²`. -/
theorem hyp_term_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (w : ℝ) (n : ℕ) :
    (a.choose n : ℝ) * (b.choose n : ℝ) * (w ^ 2 / ((a : ℝ) * b)) ^ n = hypCoeff a b n * b0 w n := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  unfold hypCoeff
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [b0]
  · obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
    rw [if_neg (by omega), Nat.add_sub_cancel, ← choose_succ_norm ha, ← choose_succ_norm hb]
    unfold b0
    have hf : (0 : ℝ) < ((r + 1).factorial : ℝ) := by positivity
    rw [div_pow, mul_pow, pow_mul]
    field_simp

/-- `hypCoeff` vanishes beyond `a`. -/
theorem hypCoeff_eq_zero {a b : ℕ} (ha : 1 ≤ a) {n : ℕ} (hn : a + 1 ≤ n) : hypCoeff a b n = 0 := by
  unfold hypCoeff
  rw [if_neg (by omega), normCoeff_eq_zero a a (by omega) ha, zero_mul]

theorem hasSum_hyp {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (w : ℝ) :
    HasSum (fun n => hypCoeff a b n * b0 w n) (hyp2F1neg a b (w ^ 2 / ((a : ℝ) * b))) := by
  unfold hyp2F1neg
  rw [show (∑ n ∈ range (a + 1), (a.choose n : ℝ) * (b.choose n : ℝ) * (w ^ 2 / ((a : ℝ) * b)) ^ n) =
      ∑ n ∈ range (a + 1), hypCoeff a b n * b0 w n from
    Finset.sum_congr rfl (fun n _ => hyp_term_eq ha hb w n)]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  rw [hypCoeff_eq_zero ha hn, zero_mul]

/-- The deficit of `hypCoeff`: with `σ_n = n(n-1)/(2A)`,
`σ_n - σ_n²/2 ≤ 1 - hypCoeff a b n ≤ σ_n` and `hypCoeff a b n ≤ 1`. -/
theorem hypCoeff_bounds {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (n : ℕ) :
    (n : ℝ) * (n - 1) / (2 * ((a : ℝ) * b / (a + b))) -
        ((n : ℝ) * (n - 1) / (2 * ((a : ℝ) * b / (a + b)))) ^ 2 / 2 ≤ 1 - hypCoeff a b n ∧
      1 - hypCoeff a b n ≤ (n : ℝ) * (n - 1) / (2 * ((a : ℝ) * b / (a + b))) := by
  unfold hypCoeff
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
    rw [if_neg (by omega), Nat.add_sub_cancel]
    have e : ((r + 1 : ℕ) : ℝ) * (((r + 1 : ℕ) : ℝ) - 1) = (r : ℝ) * (r + 1) := by push_cast; ring
    rw [e]
    exact pair_deficit_bounds ha hb r

/-- `(r+1) w^{2(r+1)}/((r+1)!)² = w · w^{2r+1}/(r!(r+1)!)`. -/
theorem b0_succ_weight (x : ℝ) (r : ℕ) : ((r + 1 : ℕ) : ℝ) * b0 x (r + 1) = x * b1 x r := by
  unfold b0 b1
  rw [Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  field_simp
  ring

/-- `Σ n w^{2n}/(n!)² = w I_1(2w)`. -/
theorem hasSum_n_b0 (x : ℝ) : HasSum (fun n : ℕ => (n : ℝ) * b0 x n) (x * besselI1 (2 * x)) := by
  have h := (hasSum_b1 x).mul_left x
  have e : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * b0 x (n + 1)) = (fun r => x * b1 x r) :=
    funext (b0_succ_weight x)
  have h' : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * b0 x (n + 1)) (x * besselI1 (2 * x)) := by
    rw [e]; exact h
  have := (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ) * b0 x n) 1).1 h'
  simpa using this

/-- `Σ n(n-1) w^{2n}/(n!)² = w² I_0(2w) - w I_1(2w)`, that is `w² I_2(2w)`. -/
theorem hasSum_nn_b0 (x : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * (n - 1) * b0 x n)
      (x ^ 2 * besselI0 (2 * x) - x * besselI1 (2 * x)) := by
  have h := (hasSum_rr_b0 x).sub ((hasSum_n_b0 x).mul_left 2)
  have e : x ^ 2 * besselI0 (2 * x) + x * besselI1 (2 * x) - 2 * (x * besselI1 (2 * x)) =
      x ^ 2 * besselI0 (2 * x) - x * besselI1 (2 * x) := by ring
  rw [e] at h
  refine h.congr_fun (fun n => ?_)
  ring

/-- `(n(n-1))² w^{2n}/(n!)² ≤ (4w)^{2n}/(n!)²`, so the fourth moment converges. -/
theorem summable_nn_sq_b0 (x : ℝ) :
    Summable (fun n : ℕ => ((n : ℝ) * (n - 1)) ^ 2 * b0 x n) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (b0_nonneg x n))
    (fun n => ?_) (summable_b0 (4 * x))
  have h2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hsq : ((n : ℝ) * (n - 1)) ^ 2 ≤ (16 : ℝ) ^ n := by
    have h1 : |(n : ℝ) * (n - 1)| ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [abs_of_nonneg (by nlinarith)]; nlinarith
    have h3 : (n : ℝ) ^ 2 ≤ (2 ^ n) ^ 2 := pow_le_pow_left₀ hn0 h2 2
    have h4 : ((n : ℝ) * (n - 1)) ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 ^ 2 := by
      rw [← sq_abs]
      calc |(n : ℝ) * (n - 1)| ^ 2 ≤ ((2 ^ n) ^ 2) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (h1.trans h3) 2
        _ = _ := by ring
    calc _ ≤ _ := h4
      _ = (16 : ℝ) ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h16 : b0 (4 * x) n = (16 : ℝ) ^ n * b0 x n := by
    unfold b0; rw [mul_pow, pow_mul (4 : ℝ) 2 n]; norm_num [mul_div_assoc]
  rw [h16]
  exact mul_le_mul_of_nonneg_right hsq (b0_nonneg x n)

/-- **Remark 4.5, the sign.** For `a, b ≥ 1` and real `w`, `₂F₁(-a,-b;1;w²/(ab)) ≤ I_0(2w)`. -/
theorem hyp2F1neg_le_besselI0 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (w : ℝ) :
    hyp2F1neg a b (w ^ 2 / ((a : ℝ) * b)) ≤ besselI0 (2 * w) := by
  refine hasSum_le (fun n => ?_) (hasSum_hyp ha hb w) (hasSum_b0 w)
  have h := (hypCoeff_bounds ha hb n).2
  have hσ : 0 ≤ (n : ℝ) * (n - 1) / (2 * ((a : ℝ) * b / (a + b))) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : 0 ≤ (n : ℝ) * (n - 1) := by nlinarith
      positivity
  have hc : hypCoeff a b n ≤ 1 := by
    unfold hypCoeff
    split_ifs
    · exact le_rfl
    · obtain ⟨-, u1, -⟩ := normCoeff_self_bounds ha (n - 1)
      obtain ⟨v0, v1, -⟩ := normCoeff_self_bounds hb (n - 1)
      nlinarith
  nlinarith [b0_nonneg w n]

/-- **Remark 4.5, the corrected expansion.** For `a, b ≥ 1`, real `w`, `z = w²/(ab)` and
`A = ab/(a+b)`,
`0 ≤ ₂F₁(-a,-b;1;z) - (I_0(2w) - (w² I_0(2w) - w I_1(2w))/(2A)) ≤ M/(8A²)`, where
`M = Σ_n (n(n-1))² w^{2n}/(n!)²`. So the first correction to `I_0(2w)` is
`-w² I_2(2w)/(2A) ≤ 0`. -/
theorem hyp2F1neg_expansion {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (w : ℝ) :
    0 ≤ hyp2F1neg a b (w ^ 2 / ((a : ℝ) * b)) -
        (besselI0 (2 * w) - (w ^ 2 * besselI0 (2 * w) - w * besselI1 (2 * w)) /
          (2 * ((a : ℝ) * b / (a + b)))) ∧
      hyp2F1neg a b (w ^ 2 / ((a : ℝ) * b)) -
          (besselI0 (2 * w) - (w ^ 2 * besselI0 (2 * w) - w * besselI1 (2 * w)) /
            (2 * ((a : ℝ) * b / (a + b)))) ≤
        (∑' n : ℕ, ((n : ℝ) * (n - 1)) ^ 2 * b0 w n) / (8 * ((a : ℝ) * b / (a + b)) ^ 2) := by
  set A : ℝ := (a : ℝ) * b / (a + b) with hA
  have hA0 : 0 < A := by
    have : (0 : ℝ) < a := by exact_mod_cast ha
    have : (0 : ℝ) < b := by exact_mod_cast hb
    positivity
  set F := hyp2F1neg a b (w ^ 2 / ((a : ℝ) * b))
  set C := w ^ 2 * besselI0 (2 * w) - w * besselI1 (2 * w)
  -- the main part `Σ (1 - σ_n) b0`
  have hmain : HasSum (fun n : ℕ => (1 - (n : ℝ) * (n - 1) / (2 * A)) * b0 w n)
      (besselI0 (2 * w) - C / (2 * A)) := by
    have h := (hasSum_b0 w).sub ((hasSum_nn_b0 w).div_const (2 * A))
    refine h.congr_fun (fun n => ?_)
    ring
  have hM : HasSum (fun n : ℕ => ((n : ℝ) * (n - 1)) ^ 2 * b0 w n / (8 * A ^ 2))
      ((∑' n : ℕ, ((n : ℝ) * (n - 1)) ^ 2 * b0 w n) / (8 * A ^ 2)) :=
    (summable_nn_sq_b0 w).hasSum.div_const _
  have hd := (hasSum_hyp ha hb w).sub hmain
  constructor
  · refine hasSum_le (fun n => ?_) hasSum_zero hd
    have h := (hypCoeff_bounds ha hb n).2
    nlinarith [b0_nonneg w n]
  · refine hasSum_le (fun n => ?_) hd hM
    have h := (hypCoeff_bounds ha hb n).1
    have hb0 := b0_nonneg w n
    have e : ((n : ℝ) * (n - 1)) ^ 2 * b0 w n / (8 * A ^ 2) =
        ((n : ℝ) * (n - 1) / (2 * A)) ^ 2 / 2 * b0 w n := by
      field_simp; ring
    rw [e]
    nlinarith

/-! ### The numbers at `a = b = 200`, `abz = 25` -/

/-- A tail bound: if `f` is summable and `f (n+1) ≤ f n/2` from `R` on, then
`Σ f ≤ Σ_{n<R} f n + 2 f R`. -/
theorem tsum_le_of_ratio_half {f : ℕ → ℝ} (hs : Summable f) (R : ℕ)
    (hr : ∀ n, R ≤ n → f (n + 1) ≤ f n / 2) :
    ∑' n, f n ≤ ∑ n ∈ range R, f n + 2 * f R := by
  have hk : ∀ k : ℕ, f (k + R) ≤ f R * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := hr (k + R) (by omega)
      rw [show k + 1 + R = k + R + 1 by ring, pow_succ]
      nlinarith
  have hsh : Summable (fun k => f (k + R)) := (summable_nat_add_iff R).mpr hs
  have hg : HasSum (fun k : ℕ => f R * (1 / 2) ^ k) (f R * 2) := by
    have := (summable_geometric_two.hasSum).mul_left (f R)
    rwa [tsum_geometric_two] at this
  have hle : ∑' k, f (k + R) ≤ f R * 2 := hasSum_le hk hsh.hasSum hg
  rw [← hs.sum_add_tsum_nat_add R]
  linarith

theorem b0_succ_ratio (x : ℝ) (r : ℕ) : b0 x (r + 1) = b0 x r * (x ^ 2 / ((r : ℝ) + 1) ^ 2) := by
  unfold b0
  rw [Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  rw [show 2 * (r + 1) = 2 * r + 2 by ring, pow_add]
  field_simp

theorem b1_succ_ratio (x : ℝ) (r : ℕ) :
    b1 x (r + 1) = b1 x r * (x ^ 2 / (((r : ℝ) + 1) * ((r : ℝ) + 2))) := by
  unfold b1
  rw [show r + 1 + 1 = r + 2 by ring, Nat.factorial_succ (r + 1), Nat.factorial_succ r]
  push_cast
  have hf : (0 : ℝ) < r.factorial := by positivity
  rw [show 2 * (r + 1) + 1 = 2 * r + 1 + 2 by ring, pow_add]
  field_simp
  ring

/-- `Σ_{r<30} 25^r/(r!)² ≤ I_0(10) ≤ Σ_{r<30} 25^r/(r!)² + 2 · 25^30/(30!)²`. -/
theorem besselI0_ten_bounds :
    ∑ r ∈ range 30, b0 5 r ≤ besselI0 10 ∧ besselI0 10 ≤ ∑ r ∈ range 30, b0 5 r + 2 * b0 5 30 := by
  have h10 : besselI0 10 = ∑' r, b0 5 r := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, besselI0_two_mul]
  rw [h10]
  constructor
  · exact (summable_b0 5).sum_le_tsum _ (fun r _ => b0_nonneg 5 r)
  · refine tsum_le_of_ratio_half (summable_b0 5) 30 (fun n hn => ?_)
    rw [b0_succ_ratio]
    have hn' : (30 : ℝ) ≤ n := by exact_mod_cast hn
    have : (5 : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 2 ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have := mul_le_mul_of_nonneg_left this (b0_nonneg 5 n)
    linarith

/-- The same for `I_1(10)` with the terms `5^{2r+1}/(r!(r+1)!)`. -/
theorem besselI1_ten_bounds :
    ∑ r ∈ range 30, b1 5 r ≤ besselI1 10 ∧ besselI1 10 ≤ ∑ r ∈ range 30, b1 5 r + 2 * b1 5 30 := by
  have h10 : besselI1 10 = ∑' r, b1 5 r := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, besselI1_two_mul]
  have h0 : ∀ r, 0 ≤ b1 5 r := b1_nonneg (by norm_num)
  rw [h10]
  constructor
  · exact (summable_b1 5).sum_le_tsum _ (fun r _ => h0 r)
  · refine tsum_le_of_ratio_half (summable_b1 5) 30 (fun n hn => ?_)
    rw [b1_succ_ratio]
    have hn' : (30 : ℝ) ≤ n := by exact_mod_cast hn
    have : (5 : ℝ) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have := mul_le_mul_of_nonneg_left this (h0 n)
    linarith

/-- The terms of `I_0(10)` and `I_1(10)` are rationals. -/
theorem b0_five_eq (r : ℕ) : b0 5 r = (((25 : ℚ) ^ r / (r.factorial : ℚ) ^ 2 : ℚ) : ℝ) := by
  unfold b0; push_cast; rw [pow_mul]; norm_num

theorem b1_five_eq (r : ℕ) :
    b1 5 r = (((5 : ℚ) * 25 ^ r / ((r.factorial : ℚ) * ((r + 1).factorial : ℚ)) : ℚ) : ℝ) := by
  unfold b1; push_cast; rw [pow_succ, pow_mul]; norm_num; ring

/-- `Σ_{r<30} 25^r/(r!)²`, `Σ_{r<30} 5·25^r/(r!(r+1)!)` and the two tail terms, as rationals. -/
def i0Part : ℚ := ∑ r ∈ range 30, (25 : ℚ) ^ r / (r.factorial : ℚ) ^ 2
def i0Tail : ℚ := 2 * ((25 : ℚ) ^ 30 / ((30 : ℕ).factorial : ℚ) ^ 2)
def i1Part : ℚ := ∑ r ∈ range 30, (5 : ℚ) * 25 ^ r / ((r.factorial : ℚ) * ((r + 1).factorial : ℚ))
def i1Tail : ℚ := 2 * ((5 : ℚ) * 25 ^ 30 / (((30 : ℕ).factorial : ℚ) * ((31 : ℕ).factorial : ℚ)))

/-- `n! C(200,n)`-free form of the exact sum: `C(200,n) = 200!/(n!(200-n)!)`. -/
def hyp200 : ℚ :=
  ∑ n ∈ range 201,
    (((200 : ℕ).factorial / (n.factorial * (200 - n).factorial) : ℕ) : ℚ) ^ 2 * (1 / 1600) ^ n

theorem hyp200_eq : hyp2F1neg 200 200 (1 / 1600) = ((hyp200 : ℚ) : ℝ) := by
  unfold hyp2F1neg hyp200
  push_cast
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn' : n ≤ 200 := by simp only [Finset.mem_range] at hn; omega
  rw [← Nat.choose_eq_factorial_div_factorial hn']
  ring

theorem i0_bounds_q : (2815716628 / 1000000 : ℚ) < i0Part ∧ i0Part + i0Tail < 2815716629 / 1000000 := by
  constructor <;> decide +kernel

theorem i1_bounds_q : (2670988303 / 1000000 : ℚ) < i1Part ∧ i1Part + i1Tail < 2670988304 / 1000000 := by
  constructor <;> decide +kernel

theorem hyp200_bounds_q : (254894118 / 100000 : ℚ) < hyp200 ∧ hyp200 < 254894119 / 100000 := by
  constructor <;> decide +kernel

/-- **Remark 4.5, the numbers.** At `a = b = 200`, `c = 1`, `abz = 25` (so `z = 1/1600`,
`w = 5`, `2w = 10` and `2A = 200`), let `F = ₂F₁(-200,-200;1;1/1600)` and
`D = (w² I_0(10) - w I_1(10))/(2A) = (25 I_0(10) - 5 I_1(10))/200`. Then `F` is between `9.45`
and `9.55` percent below `I_0(10)`, the formula `I_0(10) + D` with the sign of Eq. (D.6) is
between `10.05` and `10.15` percent above `I_0(10)`, and the corrected formula `I_0(10) - D` is
within `0.8` percent of `F`. -/
theorem sign_correction_numbers :
    let F := hyp2F1neg 200 200 (1 / 1600)
    let D := (25 * besselI0 10 - 5 * besselI1 10) / 200
    (0.0945 < 1 - F / besselI0 10 ∧ 1 - F / besselI0 10 < 0.0955) ∧
      (0.1005 < (besselI0 10 + D) / besselI0 10 - 1 ∧
        (besselI0 10 + D) / besselI0 10 - 1 < 0.1015) ∧
      |(besselI0 10 - D) / F - 1| < 0.008 := by
  intro F D
  obtain ⟨l0, u0⟩ := besselI0_ten_bounds
  obtain ⟨l1, u1⟩ := besselI1_ten_bounds
  have e0 : ∑ r ∈ range 30, b0 5 r = ((i0Part : ℚ) : ℝ) := by
    unfold i0Part; push_cast; exact Finset.sum_congr rfl (fun r _ => by rw [b0_five_eq]; push_cast; ring)
  have e0t : 2 * b0 5 30 = ((i0Tail : ℚ) : ℝ) := by
    unfold i0Tail; rw [b0_five_eq]; push_cast; ring
  have e1 : ∑ r ∈ range 30, b1 5 r = ((i1Part : ℚ) : ℝ) := by
    unfold i1Part; push_cast; exact Finset.sum_congr rfl (fun r _ => by rw [b1_five_eq]; push_cast; ring)
  have e1t : 2 * b1 5 30 = ((i1Tail : ℚ) : ℝ) := by
    unfold i1Tail; rw [b1_five_eq]; push_cast; ring
  rw [e0] at l0 u0; rw [e0t] at u0; rw [e1] at l1 u1; rw [e1t] at u1
  obtain ⟨q0l, q0u⟩ := i0_bounds_q
  obtain ⟨q1l, q1u⟩ := i1_bounds_q
  obtain ⟨qFl, qFu⟩ := hyp200_bounds_q
  have r0l := (Rat.cast_lt (K := ℝ)).mpr q0l
  have r0u := (Rat.cast_lt (K := ℝ)).mpr q0u
  have r1l := (Rat.cast_lt (K := ℝ)).mpr q1l
  have r1u := (Rat.cast_lt (K := ℝ)).mpr q1u
  have rFl := (Rat.cast_lt (K := ℝ)).mpr qFl
  have rFu := (Rat.cast_lt (K := ℝ)).mpr qFu
  push_cast at r0l r0u r1l r1u rFl rFu
  have hF : F = ((hyp200 : ℚ) : ℝ) := hyp200_eq
  set I0 := besselI0 10
  set I1 := besselI1 10
  set Fv := ((hyp200 : ℚ) : ℝ)
  have hI0l : (2815716628 / 1000000 : ℝ) < I0 := by linarith
  have hI0u : I0 < 2815716629 / 1000000 := by linarith
  have hI1l : (2670988303 / 1000000 : ℝ) < I1 := by linarith
  have hI1u : I1 < 2670988304 / 1000000 := by linarith
  have hI0p : 0 < I0 := by linarith
  have hFp : 0 < F := by rw [hF]; linarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', div_lt_iff₀ hI0p, hF]; nlinarith
  · rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', lt_div_iff₀ hI0p, hF]; nlinarith
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hI0p]; simp only [D]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hI0p]; simp only [D]; nlinarith
  · rw [abs_lt]
    constructor
    · rw [lt_sub_iff_add_lt, lt_div_iff₀ hFp, hF]; simp only [D]; nlinarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hFp, hF]; simp only [D]; nlinarith

end Kagey131
