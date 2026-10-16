import PaperA.AllbinExpansion

/-!
# The consequences of Theorem `thm:allbin-expansion` displayed after it

* `eq:allbin-growing-edge`: if `a → ∞` and `a = o(b)`, then
  `2√(ab)(1 - p_{a,b}) = log a - (1/2) log log a + (1/2) log(8π) + o(1)`.
* the case `a/N → α`: if `N → ∞` and `a/N → α` with `0 < α < 1`, then
  `2√(a(N-a))(1 - p_{a,N-a}) = log N - (1/2) log log N + log(α(1-α)) + C(2√(α(1-α))) + o(1)`.

Both are stated for sequences `a n`, `b n` (or `a n`, `N n`) and `n → ∞`. The common step is
`allbin_limit_core`: Theorem 4.9, applied to `min(a,b)` and `max(a,b)`, together with the
limit `rootMain_limit` of its main terms.
-/

namespace Kagey131

open Filter Topology

/-- The main terms of Theorem 4.9 under a shift of `ℓ`: if `L → ∞`, `ℓ - L → c` and `η → η₀ ≥ 0`,
then `rootMain ℓ η - (L - (1/2) log L + c + C(η₀)) → 0`. -/
theorem rootMain_limit {ι : Type*} {F : Filter ι} {ℓ L η : ι → ℝ} {c η₀ : ℝ}
    (hL : Tendsto L F atTop) (hℓ : Tendsto (fun i => ℓ i - L i) F (𝓝 c))
    (hη : Tendsto η F (𝓝 η₀)) (hη₀ : 0 ≤ η₀) :
    Tendsto (fun i => rootMain (ℓ i) (η i) - (L i - Real.log (L i) / 2 + c + Ceta η₀)) F (𝓝 0) := by
  have hℓt : Tendsto ℓ F atTop := by
    have h := hℓ.add_atTop hL
    refine h.congr (fun i => ?_)
    simp
  -- `ℓ - L - c → 0`
  have h1 : Tendsto (fun i => ℓ i - L i - c) F (𝓝 0) := by
    simpa using hℓ.sub_const c
  -- `log ℓ - log L → 0`
  have h2 : Tendsto (fun i => Real.log (ℓ i) - Real.log (L i)) F (𝓝 0) := by
    have hq : Tendsto (fun i => 1 + (ℓ i - L i) * (L i)⁻¹) F (𝓝 1) := by
      have := (hℓ.mul (tendsto_inv_atTop_zero.comp hL)).const_add 1
      simpa using this
    have hlog := ((Real.continuousAt_log one_ne_zero).tendsto.comp hq)
    rw [Real.log_one] at hlog
    refine hlog.congr' ?_
    filter_upwards [hL.eventually_gt_atTop 0, hℓt.eventually_gt_atTop 0] with i hLi hℓi
    simp only [Function.comp_apply]
    rw [← Real.log_div hℓi.ne' hLi.ne']
    congr 1
    field_simp
    ring
  -- `C(η) → C(η₀)` and `B(η) → B(η₀)`
  have h1η : (1 + η₀) ≠ 0 := by linarith
  have hC : Tendsto (fun i => Ceta (η i)) F (𝓝 (Ceta η₀)) := by
    unfold Ceta
    exact tendsto_const_nhds.sub ((tendsto_const_nhds.add hη).log h1η)
  have hB : Tendsto (fun i => Beta (η i)) F (𝓝 (Beta η₀)) := by
    unfold Beta
    exact (tendsto_const_nhds.sub hη).div (tendsto_const_nhds.mul (tendsto_const_nhds.add hη))
      (by positivity)
  have h3 : Tendsto (fun i => Ceta (η i) - Ceta η₀) F (𝓝 0) := by
    simpa using hC.sub_const (Ceta η₀)
  -- `(log ℓ/4 - C/2 + B)/ℓ → 0`
  have hlogℓ : Tendsto (fun i => Real.log (ℓ i) / ℓ i) F (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hℓt
    refine h.congr (fun i => ?_)
    simp
  have h4 : Tendsto (fun i => (Real.log (ℓ i) / 4 - Ceta (η i) / 2 + Beta (η i)) / ℓ i) F (𝓝 0) := by
    have hinv : Tendsto (fun i => (ℓ i)⁻¹) F (𝓝 0) := tendsto_inv_atTop_zero.comp hℓt
    have h := (hlogℓ.div_const 4).add ((((hC.div_const 2).neg).add hB).mul hinv)
    rw [zero_div, mul_zero, add_zero] at h
    refine h.congr (fun i => ?_)
    ring
  have h := ((h1.sub (h2.div_const 2)).add h3).add h4
  rw [zero_div, sub_zero, add_zero, add_zero] at h
  refine h.congr (fun i => ?_)
  unfold rootMain
  ring

/-- Theorem 4.9 for `1 - p_{a,b}` without the order `a ≤ b`: there are `K` and `a₀` with
`|2√(ab)(1 - p_{a,b}) - rootMain(log A, η)| ≤ K((log ℓ)²/ℓ² + (log a)²/a + (log b)²/b)` for
all `a, b ≥ a₀`. -/
theorem allbin_expansion_prob_symm :
    ∃ K : ℝ, 0 < K ∧ ∃ a₀ : ℕ, ∀ a b : ℕ, a₀ ≤ a → a₀ ≤ b →
      |2 * Real.sqrt ((a : ℝ) * b) * (1 - pab a b) -
        rootMain (Real.log ((a : ℝ) * b / (a + b))) (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b))| ≤
        K * (Real.log (Real.log ((a : ℝ) * b / (a + b))) ^ 2 / Real.log ((a : ℝ) * b / (a + b)) ^ 2 +
          Real.log a ^ 2 / a + Real.log b ^ 2 / b) := by
  obtain ⟨K, hK, a₀, h⟩ := allbin_expansion_prob
  refine ⟨K, hK, max a₀ 1, ?_⟩
  intro a b ha hb
  have ha0 : a₀ ≤ a := le_trans (le_max_left _ _) ha
  have hb0 : a₀ ≤ b := le_trans (le_max_left _ _) hb
  have ha1 : 1 ≤ a := le_trans (le_max_right _ _) ha
  have hb1 : 1 ≤ b := le_trans (le_max_right _ _) hb
  have hP : 0 ≤ Real.log (Real.log ((a : ℝ) * b / (a + b))) ^ 2 /
      Real.log ((a : ℝ) * b / (a + b)) ^ 2 := by positivity
  have hQa : 0 ≤ Real.log a ^ 2 / a := by positivity
  have hQb : 0 ≤ Real.log b ^ 2 / b := by positivity
  rcases le_total a b with hab | hba
  · have e := h a b ha0 hab
    calc _ ≤ _ := e
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hK.le
  · have e := h b a hb0 hba
    rw [pab_symm hb1 ha1, mul_comm (b : ℝ) a, add_comm (b : ℝ) a] at e
    calc _ ≤ _ := e
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hK.le

/-- `(log x)²/x → 0` along a sequence of naturals tending to infinity. -/
theorem tendsto_log_sq_div_nat {a : ℕ → ℕ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => Real.log (a n) ^ 2 / (a n : ℝ)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop.comp ha)
  refine h.congr (fun n => ?_)
  simp

/-- **The common step of the consequences of Theorem 4.9.** Let `a n, b n → ∞`, and let `L n → ∞`
with `log(ab/(a+b)) - L → c` and `η = 2√(ab)/(a+b) → η₀ ≥ 0`. Then
`2√(ab)(1 - p_{a,b}) - (L - (1/2) log L + c + C(η₀)) → 0`. -/
theorem allbin_limit_core {a b : ℕ → ℕ} {L : ℕ → ℝ} {c η₀ : ℝ}
    (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop) (hL : Tendsto L atTop atTop)
    (hℓ : Tendsto (fun n => Real.log ((a n : ℝ) * b n / (a n + b n)) - L n) atTop (𝓝 c))
    (hη : Tendsto (fun n => 2 * Real.sqrt ((a n : ℝ) * b n) / ((a n : ℝ) + b n)) atTop (𝓝 η₀))
    (hη₀ : 0 ≤ η₀) :
    Tendsto (fun n => 2 * Real.sqrt ((a n : ℝ) * b n) * (1 - pab (a n) (b n)) -
      (L n - Real.log (L n) / 2 + c + Ceta η₀)) atTop (𝓝 0) := by
  obtain ⟨K, hK, a₀, h⟩ := allbin_expansion_prob_symm
  set ℓ : ℕ → ℝ := fun n => Real.log ((a n : ℝ) * b n / (a n + b n)) with hℓdef
  have hmain := rootMain_limit hL hℓ hη hη₀
  have hℓt : Tendsto ℓ atTop atTop := by
    have h := hℓ.add_atTop hL
    refine h.congr (fun i => ?_)
    simp [hℓdef]
  have hP : Tendsto (fun n => Real.log (ℓ n) ^ 2 / ℓ n ^ 2) atTop (𝓝 0) := by
    have h1 := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hℓt).pow 2
    rw [zero_pow two_ne_zero] at h1
    refine h1.congr (fun n => ?_)
    simp [div_pow]
  have hbound : Tendsto (fun n => K * (Real.log (ℓ n) ^ 2 / ℓ n ^ 2 +
      Real.log (a n) ^ 2 / a n + Real.log (b n) ^ 2 / b n)) atTop (𝓝 0) := by
    have := ((hP.add (tendsto_log_sq_div_nat ha)).add (tendsto_log_sq_div_nat hb)).const_mul K
    simpa using this
  have herr : Tendsto (fun n => 2 * Real.sqrt ((a n : ℝ) * b n) * (1 - pab (a n) (b n)) -
      rootMain (ℓ n) (2 * Real.sqrt ((a n : ℝ) * b n) / ((a n : ℝ) + b n))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [ha.eventually_ge_atTop a₀, hb.eventually_ge_atTop a₀] with n han hbn
    rw [Real.norm_eq_abs]
    exact h (a n) (b n) han hbn
  have := herr.add hmain
  rw [add_zero] at this
  refine this.congr (fun n => ?_)
  ring

/-- **`eq:allbin-growing-edge`.** If `a → ∞`, `a ≤ b` and `a/b → 0`, then
`2√(ab)(1 - p_{a,b}) - (log a - (1/2) log log a + (1/2) log(8π)) → 0`. -/
theorem allbin_growing_edge {a b : ℕ → ℕ} (ha : Tendsto a atTop atTop) (hab : ∀ n, a n ≤ b n)
    (hr : Tendsto (fun n => (a n : ℝ) / b n) atTop (𝓝 0)) :
    Tendsto (fun n => 2 * Real.sqrt ((a n : ℝ) * b n) * (1 - pab (a n) (b n)) -
      (Real.log (a n) - Real.log (Real.log (a n)) / 2 + Real.log (8 * Real.pi) / 2))
      atTop (𝓝 0) := by
  have hb : Tendsto b atTop atTop := tendsto_atTop_mono hab ha
  have ha1 : ∀ᶠ n in atTop, 1 ≤ a n := ha.eventually_ge_atTop 1
  have hL : Tendsto (fun n => Real.log (a n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp ha)
  -- `log(ab/(a+b)) - log a = -log(1 + a/b)`
  have hℓ : Tendsto (fun n => Real.log ((a n : ℝ) * b n / (a n + b n)) - Real.log (a n))
      atTop (𝓝 0) := by
    have h := ((Real.continuousAt_log one_ne_zero).tendsto.comp
      (by simpa using hr.const_add 1 : Tendsto (fun n => 1 + (a n : ℝ) / b n) atTop (𝓝 1))).neg
    rw [Real.log_one, neg_zero] at h
    refine h.congr' ?_
    filter_upwards [ha1] with n hn
    have ha0 : (0 : ℝ) < a n := by exact_mod_cast hn
    have hb0 : (0 : ℝ) < b n := by exact_mod_cast le_trans hn (hab n)
    simp only [Function.comp_apply]
    have e : (a n : ℝ) * b n / (a n + b n) = a n / (1 + a n / b n) := by
      field_simp; ring
    rw [e, Real.log_div ha0.ne' (by positivity)]
    ring
  -- `η = 2√(a/b)/(1 + a/b) → 0`
  have hη : Tendsto (fun n => 2 * Real.sqrt ((a n : ℝ) * b n) / ((a n : ℝ) + b n)) atTop (𝓝 0) := by
    have h := ((hr.sqrt).const_mul 2).div (hr.const_add 1) (by norm_num)
    simp only [Real.sqrt_zero, mul_zero, add_zero, zero_div] at h
    refine h.congr' ?_
    filter_upwards [ha1] with n hn
    simp only [Pi.div_apply]
    have hb0 : (0 : ℝ) < b n := by exact_mod_cast le_trans hn (hab n)
    have hs : Real.sqrt ((a n : ℝ) * b n) = Real.sqrt ((a n : ℝ) / b n) * b n := by
      rw [← Real.sqrt_sq hb0.le, ← Real.sqrt_mul (by positivity), Real.sqrt_sq hb0.le]
      congr 1
      field_simp
    rw [hs]
    field_simp
    ring
  have h := allbin_limit_core ha hb hL hℓ hη le_rfl
  rw [(Ceta_zero_Beta_zero).1] at h
  exact h.congr (fun n => by ring)

/-- **The case `a/N → α`** after Theorem 4.9. If `N → ∞` and `a/N → α` with `0 < α < 1`, then
`2√(a(N-a))(1 - p_{a,N-a}) - (log N - (1/2) log log N + log(α(1-α)) + C(2√(α(1-α)))) → 0`.
The paper takes `0 < α ≤ 1/2`. -/
theorem allbin_fixed_fraction {a N : ℕ → ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hN : Tendsto N atTop atTop) (haN : Tendsto (fun n => (a n : ℝ) / N n) atTop (𝓝 α)) :
    Tendsto (fun n => 2 * Real.sqrt ((a n : ℝ) * ((N n - a n : ℕ) : ℝ)) * (1 - pab (a n) (N n - a n)) -
      (Real.log (N n) - Real.log (Real.log (N n)) / 2 + Real.log (α * (1 - α)) +
        Ceta (2 * Real.sqrt (α * (1 - α))))) atTop (𝓝 0) := by
  have hNr : Tendsto (fun n => (N n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hpos : ∀ᶠ n in atTop, 0 < (N n : ℝ) := hNr.eventually_gt_atTop 0
  have hlt : ∀ᶠ n in atTop, (a n : ℝ) / N n < 1 := haN.eventually (gt_mem_nhds hα1)
  have hle : ∀ᶠ n in atTop, a n ≤ N n := by
    filter_upwards [hpos, hlt] with n h0 h1
    rw [div_lt_one h0] at h1
    exact_mod_cast h1.le
  -- the two coordinates tend to infinity
  have hfrac : Tendsto (fun n => (a n : ℝ) / N n * (1 - (a n : ℝ) / N n)) atTop (𝓝 (α * (1 - α))) :=
    haN.mul (haN.const_sub 1)
  have hcast : ∀ᶠ n in atTop, (((N n - a n : ℕ) : ℝ)) = (N n : ℝ) - a n := by
    filter_upwards [hle] with n h
    exact Nat.cast_sub h
  have har : Tendsto (fun n => (a n : ℝ)) atTop atTop := by
    have h := Tendsto.atTop_mul_pos hα0 hNr haN
    refine h.congr' ?_
    filter_upwards [hpos] with n h0
    field_simp
  have hbr : Tendsto (fun n => (((N n - a n : ℕ) : ℝ))) atTop atTop := by
    have h := Tendsto.atTop_mul_pos (by linarith : 0 < 1 - α) hNr (haN.const_sub 1)
    refine h.congr' ?_
    filter_upwards [hpos, hcast] with n h0 hc
    rw [hc]
    field_simp
  have ha : Tendsto a atTop atTop := tendsto_natCast_atTop_iff.mp har
  have hb : Tendsto (fun n => N n - a n) atTop atTop := tendsto_natCast_atTop_iff.mp hbr
  have hL : Tendsto (fun n => Real.log (N n)) atTop atTop := Real.tendsto_log_atTop.comp hNr
  have hα' : α * (1 - α) ≠ 0 := (mul_pos hα0 (by linarith)).ne'
  -- `log(a(N-a)/N) - log N = log((a/N)(1 - a/N))`
  have hℓ : Tendsto (fun n => Real.log ((a n : ℝ) * ((N n - a n : ℕ) : ℝ) /
      (a n + ((N n - a n : ℕ) : ℝ))) - Real.log (N n)) atTop (𝓝 (Real.log (α * (1 - α)))) := by
    have h := hfrac.log hα'
    refine h.congr' ?_
    filter_upwards [hpos, hcast, ha.eventually_ge_atTop 1, hb.eventually_ge_atTop 1] with
      n h0 hc ha1 hb1
    have ha0 : (0 : ℝ) < a n := by exact_mod_cast ha1
    have hb0 : (0 : ℝ) < ((N n - a n : ℕ) : ℝ) := by exact_mod_cast hb1
    rw [hc] at hb0 ⊢
    have e : (a n : ℝ) * (N n - a n) / (a n + (N n - a n)) =
        N n * ((a n : ℝ) / N n * (1 - (a n : ℝ) / N n)) := by
      field_simp; ring
    rw [e, Real.log_mul h0.ne' (by
      have : 0 < (a n : ℝ) / N n * (1 - (a n : ℝ) / N n) := by
        rw [← mul_lt_mul_iff_of_pos_left h0, mul_zero, ← e]; positivity
      exact this.ne')]
    ring
  -- `η = 2√((a/N)(1 - a/N))`
  have hη : Tendsto (fun n => 2 * Real.sqrt ((a n : ℝ) * ((N n - a n : ℕ) : ℝ)) /
      ((a n : ℝ) + ((N n - a n : ℕ) : ℝ))) atTop (𝓝 (2 * Real.sqrt (α * (1 - α)))) := by
    have h := (hfrac.sqrt).const_mul 2
    refine h.congr' ?_
    filter_upwards [hpos, hcast] with n h0 hc
    rw [hc]
    have hs : Real.sqrt ((a n : ℝ) * (N n - a n)) =
        Real.sqrt ((a n : ℝ) / N n * (1 - (a n : ℝ) / N n)) * N n := by
      rw [← Real.sqrt_sq h0.le, ← Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq h0.le]
      congr 1
      field_simp
    rw [hs, show (a n : ℝ) + (N n - a n) = N n by ring]
    field_simp
  exact allbin_limit_core ha hb hL hℓ hη (by positivity)

end Kagey131
