import PaperD.U2_LandauDensity

/-!
# Paper D, Theorem 3.9(c) under fewer hypotheses

`thm_landau_c` (in `U2_LandauLimit`) assumes `N_n ≥ 64` and `ε_n ≤ 1/4` for every `n`. Here:

* `tendsto_errorBound_sharp` : the sharp (b) error `(889 + 165 log x)/x + 6.6 x/N + x δ_B` tends to
  `0` as soon as `x_n → ∞`, `x_n³ log² N_n / N_n → 0` and, eventually, `ε_n ≤ 1` (then
  `N_n ≥ x_n → ∞`, so eventually `log N_n ≥ 1`, `ε_n ≤ 1/4`, `4x_n ≤ N_n`);
* `thm_landau_c_sharp` : Theorem 3.9(c) with only those hypotheses: no `N ≥ 64`, no `ε ≤ 1/4`,
  and the characteristic-function and Theorem 3.8 hypotheses only for large `n`.
-/

namespace Kagey131.PaperD.U2

open Complex Finset Filter Topology MeasureTheory Set
open scoped Real

noncomputable section

lemma one_le_log_of_three {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma deltaB_nonneg' (N : ℕ) (ε : ℝ) : 0 ≤ deltaB N ε := by
  unfold deltaB
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hH := harmonic_nonneg' N
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  positivity

/-- `x δ_B ≤ 36 x³ log² N / N` once `log N ≥ 1` and `4x² ≤ N`. -/
lemma x_deltaB_le' {N : ℕ} (hL : 1 ≤ Real.log N) {ε : ℝ} (hx : 0 ≤ (N : ℝ) * ε)
    (hx2 : 4 * ((N : ℝ) * ε) ^ 2 ≤ N) :
    (N * ε) * deltaB N ε ≤ 36 * (((N : ℝ) * ε) ^ 3 * Real.log N ^ 2 / N) := by
  set x := (N : ℝ) * ε with hxdef
  set L := Real.log N with hLdef
  have hNpos : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp [hLdef] at hL; linarith
    · exact_mod_cast h
  set H := (harmonic N : ℝ) with hHdef
  have hH0 : 0 ≤ H := harmonic_nonneg' N
  have hH1 : H ≤ 1 + L := harmonic_le_one_add_log N
  have hHH : H ^ 2 + H ≤ 6 * L ^ 2 := by nlinarith
  have hexp : Real.exp (4 * x ^ 2 / N) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    rw [div_le_one hNpos]; linarith
  have he := Real.exp_one_lt_d9
  unfold deltaB
  rw [← hxdef, ← hLdef, ← hHdef]
  have hx3 : 0 ≤ x ^ 3 / N := by positivity
  have t1 : x * (x ^ 2 * L / N) ≤ x ^ 3 * L ^ 2 / N := by
    rw [show x * (x ^ 2 * L / N) = x ^ 3 / N * L by ring,
      show x ^ 3 * L ^ 2 / N = x ^ 3 / N * L ^ 2 by ring]
    gcongr; nlinarith
  have t2 : x * (4 * x ^ 2 / N * Real.exp (4 * x ^ 2 / N)) ≤ 11 * (x ^ 3 * L ^ 2 / N) := by
    rw [show x * (4 * x ^ 2 / N * Real.exp (4 * x ^ 2 / N))
        = x ^ 3 / N * (4 * Real.exp (4 * x ^ 2 / N)) by ring,
      show 11 * (x ^ 3 * L ^ 2 / N) = x ^ 3 / N * (11 * L ^ 2) by ring]
    apply mul_le_mul_of_nonneg_left _ hx3
    nlinarith
  have t3 : x * (4 * x ^ 2 * (H ^ 2 + H) / N) ≤ 24 * (x ^ 3 * L ^ 2 / N) := by
    rw [show x * (4 * x ^ 2 * (H ^ 2 + H) / N) = x ^ 3 / N * (4 * (H ^ 2 + H)) by ring,
      show 24 * (x ^ 3 * L ^ 2 / N) = x ^ 3 / N * (24 * L ^ 2) by ring]
    apply mul_le_mul_of_nonneg_left _ hx3
    linarith
  have : x * (x ^ 2 * L / N + 4 * x ^ 2 / N * Real.exp (4 * x ^ 2 / N)
      + 4 * x ^ 2 * (H ^ 2 + H) / N)
      = x * (x ^ 2 * L / N) + x * (4 * x ^ 2 / N * Real.exp (4 * x ^ 2 / N))
        + x * (4 * x ^ 2 * (H ^ 2 + H) / N) := by ring
  rw [this]
  linarith

/-- The eventual consequences of `ε_n ≤ 1`, `x_n → ∞`, `x_n³ log² N_n/N_n → 0`:
`x_n ≥ 1`, `log N_n ≥ 1`, `4x_n² ≤ N_n` (hence `4x_n ≤ N_n`), `x_n/N_n ≤ x_n³ log² N_n/N_n`. -/
lemma eventually_regime (N : ℕ → ℕ) (ε : ℕ → ℝ) (hε1 : ∀ᶠ n in atTop, ε n ≤ 1)
    (hx : Tendsto (fun n => (N n : ℝ) * ε n) atTop atTop)
    (h3 : Tendsto (fun n => ((N n : ℝ) * ε n) ^ 3 * Real.log (N n) ^ 2 / N n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 1 ≤ (N n : ℝ) * ε n ∧ 1 ≤ Real.log (N n) ∧
      4 * ((N n : ℝ) * ε n) ^ 2 ≤ N n ∧ 4 * ((N n : ℝ) * ε n) ≤ N n ∧
      (N n : ℝ) * ε n / N n ≤ ((N n : ℝ) * ε n) ^ 3 * Real.log (N n) ^ 2 / N n := by
  have hev1 : ∀ᶠ n in atTop, 1 ≤ (N n : ℝ) * ε n := hx.eventually_ge_atTop 1
  have hev3 : ∀ᶠ n in atTop, (3 : ℝ) ≤ (N n : ℝ) * ε n := hx.eventually_ge_atTop 3
  have hev2 : ∀ᶠ n in atTop, ((N n : ℝ) * ε n) ^ 3 * Real.log (N n) ^ 2 / N n ≤ 1 / 4 :=
    h3.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hev1, hev2, hev3, hε1] with n h1 h2 h3' he
  have hN0 : (0 : ℝ) ≤ N n := Nat.cast_nonneg _
  have hxN : (N n : ℝ) * ε n ≤ N n := by nlinarith
  have hN3 : 3 ≤ N n := by exact_mod_cast (show (3 : ℝ) ≤ N n by linarith)
  have hL := one_le_log_of_three hN3
  have hNpos : (0 : ℝ) < N n := by linarith
  set x := (N n : ℝ) * ε n with hxd
  have hr : x / N n ≤ x ^ 3 * Real.log (N n) ^ 2 / N n := by
    rw [div_le_div_iff_of_pos_right hNpos]
    have : 1 ≤ x ^ 2 * Real.log (N n) ^ 2 := by
      have : 1 ≤ x ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have hx2 : 4 * x ^ 2 ≤ N n := by
    have : x ^ 2 ≤ (x ^ 3 * Real.log (N n) ^ 2 / N n) * N n := by
      rw [div_mul_cancel₀ _ hNpos.ne']
      have : 1 ≤ x * Real.log (N n) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  exact ⟨h1, hL, hx2, by nlinarith, hr⟩

/-- The sharp error bound of Theorem 3.9(b), `(889 + 165 log x)/x + 6.6 x/N + x δ_B`, tends to `0`
when `x_n → ∞`, `x_n³ log² N_n / N_n → 0` and eventually `ε_n ≤ 1`. -/
theorem tendsto_errorBound_sharp (N : ℕ → ℕ) (ε : ℕ → ℝ) (hε1 : ∀ᶠ n in atTop, ε n ≤ 1)
    (hx : Tendsto (fun n => (N n : ℝ) * ε n) atTop atTop)
    (h3 : Tendsto (fun n => ((N n : ℝ) * ε n) ^ 3 * Real.log (N n) ^ 2 / N n) atTop (𝓝 0)) :
    Tendsto (fun n => (889 + 165 * Real.log (N n * ε n)) / (N n * ε n)
      + 6.6 * ((N n * ε n) / N n) + (N n * ε n) * deltaB (N n) (ε n)) atTop (𝓝 0) := by
  set x : ℕ → ℝ := fun n => (N n : ℝ) * ε n with hxd
  set r : ℕ → ℝ := fun n => x n ^ 3 * Real.log (N n) ^ 2 / N n with hr
  have hlogx : Tendsto (fun n => (889 + 165 * Real.log (x n)) / x n) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hx
    have h2 := tendsto_inv_atTop_zero.comp hx
    have := (h2.const_mul 889).add (h1.const_mul 165)
    rw [mul_zero, mul_zero, add_zero] at this
    refine this.congr (fun n => ?_)
    simp only [Function.comp_apply, pow_one, one_mul, add_zero, hxd]
    ring
  have hbound : ∀ᶠ n in atTop,
      (889 + 165 * Real.log (x n)) / x n + 6.6 * (x n / N n) + x n * deltaB (N n) (ε n)
        ≤ (889 + 165 * Real.log (x n)) / x n + 42.6 * r n := by
    filter_upwards [eventually_regime N ε hε1 hx h3] with n ⟨h1, hL, hx2, _, hxr⟩
    have hd := x_deltaB_le' hL (by linarith : (0 : ℝ) ≤ x n) hx2
    simp only [hxd, hr] at hd hxr ⊢
    linarith
  have hnonneg : ∀ᶠ n in atTop,
      0 ≤ (889 + 165 * Real.log (x n)) / x n + 6.6 * (x n / N n) + x n * deltaB (N n) (ε n) := by
    filter_upwards [hx.eventually_ge_atTop 1] with n h1
    have := deltaB_nonneg' (N n) (ε n)
    have : 0 ≤ Real.log (x n) := Real.log_nonneg h1
    have : (0 : ℝ) ≤ N n := Nat.cast_nonneg _
    have : 0 ≤ x n := by linarith
    positivity
  have hlim : Tendsto (fun n => (889 + 165 * Real.log (x n)) / x n + 42.6 * r n) atTop (𝓝 0) := by
    have := hlogx.add (h3.const_mul 42.6)
    simpa using this
  exact squeeze_zero' hnonneg hbound hlim

/-- **Theorem 3.9(c) (`thm:landau`(c)), fewer hypotheses.** Assume lattice Fourier inversion,
Scheffé, and `f_L` a probability density (`hL`; proved by `landauDensityHyp_of_cp`). Let
`x_n = N_n ε_n → ∞` with `x_n³ log² N_n / N_n → 0` and, for large `n`, `ε_n ≤ 1`. Let `f_n` be
laws on `ℕ` (the law of `M_{N_n}`), and for large `n` let `p_n ≥ 0` have characteristic function
`e^{x_nΨ_{N_n}}` and `|f_n - p_n| ≤ δ_B` (Theorem 3.8's conclusion). Then
`(M_{N_n} - x_n log x_n)/x_n` converges in law to the law with density `f_L`.
No `N_n ≥ 64` and no `ε_n ≤ 1/4` is assumed. -/
theorem thm_landau_c_sharp (hInv : LatticeFourierInversionHyp) (hS : ScheffeHyp)
    (hL : LandauDensityHyp) (N : ℕ → ℕ) (ε : ℕ → ℝ) (hε1 : ∀ᶠ n in atTop, ε n ≤ 1)
    (hx : Tendsto (fun n => (N n : ℝ) * ε n) atTop atTop)
    (h3 : Tendsto (fun n => ((N n : ℝ) * ε n) ^ 3 * Real.log (N n) ^ 2 / N n) atTop (𝓝 0))
    (p f : ℕ → ℕ → ℝ) (hp0 : ∀ᶠ n in atTop, ∀ m, 0 ≤ p n m)
    (hchar : ∀ᶠ n in atTop, CPCharFunNat (N n) (N n * ε n) (p n))
    (hcp : ∀ᶠ n in atTop, ThmCPConclusionNat (N n) (ε n) (f n) (p n))
    (hf0 : ∀ n m, 0 ≤ f n m) (hf1 : ∀ n, HasSum (f n) 1) :
    Tendsto (fun n => latticeLaw (N n * ε n) (extZ (f n)) (extZ_nonneg (hf0 n))
        (extZ_hasSum (hf1 n))) atTop (𝓝 (landauLaw hL)) := by
  set x : ℕ → ℝ := fun n => (N n : ℝ) * ε n with hxd
  have hElim := tendsto_errorBound_sharp N ε hε1 hx h3
  refine tendsto_latticeLaw_of_local hS hL x hx (fun n => extZ (f n))
    (fun n => extZ_nonneg (hf0 n)) (fun n => extZ_hasSum (hf1 n)) _ hElim ?_
  filter_upwards [eventually_regime N ε hε1 hx h3, hp0, hchar, hcp] with n ⟨hn, _, _, hxN, _⟩
    hp0n hcn hcpn m
  obtain ⟨hs, hc⟩ := cpCharFun_extZ hp0n hcn
  have hcpZ : |extZ (f n) m - extZ (p n) m| ≤ deltaB (N n) (ε n) := by
    rcases lt_or_ge m 0 with h | h
    · rw [extZ_of_neg _ h, extZ_of_neg _ h, sub_zero, abs_zero]
      exact deltaB_nonneg' (N n) (ε n)
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
      exact hcpn k
  have hb := landau_local_fN_sharp hInv hn hxN (extZ (p n)) hs hc (extZ (f n)) m hcpZ
  rw [landauDensity_eq_fL, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hb
  exact hb

end

end Kagey131.PaperD.U2
