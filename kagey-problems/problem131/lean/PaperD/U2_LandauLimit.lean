import PaperD.U2_LandauLaw

/-!
# Paper D, Theorem 3.9(c) (`thm:landau`(c)) for the elephant walk

`thm_landau_c`: let `N_n ≥ 64`, `0 < ε_n ≤ 1/4`, `x_n = N_n ε_n`, `x_n → ∞` and
`x_n³ log² N_n / N_n → 0`. Let `f_n` be the law of `M_{N_n}` and `p_n = CP_{N_n}` (both `ℕ`-indexed as in
track U1), with Theorem 3.8's conclusion and the compound-Poisson characteristic function as
hypotheses. Then `(M_{N_n} - x_n log x_n)/x_n` converges in law to the law with density `f_L`.

The asymptotic step `tendsto_errorBound` shows that the bound of Theorem 3.9(b),
`3600((1 + log x)/x + x/N) + x δ_B`, tends to `0`.
-/

namespace Kagey131.PaperD.U2

open Complex Finset Filter Topology MeasureTheory Set
open scoped Real

noncomputable section

lemma harmonic_nonneg' (N : ℕ) : (0 : ℝ) ≤ (harmonic N : ℝ) := by
  unfold harmonic
  push_cast
  exact Finset.sum_nonneg (fun i _ => by positivity)

lemma one_le_log_of_64 {N : ℕ} (hN : 64 ≤ N) : 1 ≤ Real.log N := by
  have hN' : (64 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma deltaB_nonneg {N : ℕ} (hN : 64 ≤ N) (ε : ℝ) : 0 ≤ deltaB N ε := by
  unfold deltaB
  have hL := one_le_log_of_64 hN
  have hH := harmonic_nonneg' N
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  positivity

/-- `x δ_B ≤ 36 x³ log² N / N` once `log N ≥ 1` and `x² ≤ N/4`. -/
lemma x_deltaB_le {N : ℕ} (hN : 64 ≤ N) {ε : ℝ} (hx : 0 ≤ (N : ℝ) * ε)
    (hx2 : 4 * ((N : ℝ) * ε) ^ 2 ≤ N) :
    (N * ε) * deltaB N ε ≤ 36 * (((N : ℝ) * ε) ^ 3 * Real.log N ^ 2 / N) := by
  set x := (N : ℝ) * ε with hxdef
  set L := Real.log N with hLdef
  have hL : 1 ≤ L := one_le_log_of_64 hN
  have hNpos : (0 : ℝ) < N := by have : (64 : ℝ) ≤ N := by exact_mod_cast hN
                                 linarith
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

/-- The error bound of Theorem 3.9(b) tends to `0` when `x → ∞` and `x³ log² N / N → 0`. -/
theorem tendsto_errorBound (N : ℕ → ℕ) (ε : ℕ → ℝ) (hN : ∀ n, 64 ≤ N n)
    (hx : Tendsto (fun n => (N n : ℝ) * ε n) atTop atTop)
    (h3 : Tendsto (fun n => ((N n : ℝ) * ε n) ^ 3 * Real.log (N n) ^ 2 / N n) atTop (𝓝 0)) :
    Tendsto (fun n => 3600 * ((1 + Real.log (N n * ε n)) / (N n * ε n) + (N n * ε n) / N n)
      + (N n * ε n) * deltaB (N n) (ε n)) atTop (𝓝 0) := by
  set x : ℕ → ℝ := fun n => (N n : ℝ) * ε n with hxd
  set r : ℕ → ℝ := fun n => x n ^ 3 * Real.log (N n) ^ 2 / N n with hr
  have hNpos : ∀ n, (0 : ℝ) < N n := fun n => by
    have : (64 : ℝ) ≤ N n := by exact_mod_cast hN n
    linarith
  -- `(1 + log x)/x → 0`
  have hlogx : Tendsto (fun n => (1 + Real.log (x n)) / x n) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hx
    have h2 := tendsto_inv_atTop_zero.comp hx
    have := h2.add h1
    rw [add_zero] at this
    refine this.congr (fun n => ?_)
    simp only [Function.comp_apply, pow_one, one_mul, add_zero, hxd]
    ring
  -- eventually `x ≥ 1` and `4x² ≤ N`
  have hev1 : ∀ᶠ n in atTop, 1 ≤ x n := hx.eventually_ge_atTop 1
  have hev2 : ∀ᶠ n in atTop, r n ≤ 1 / 4 := (h3.eventually (ge_mem_nhds (by norm_num)))
  have hbound : ∀ᶠ n in atTop,
      3600 * ((1 + Real.log (x n)) / x n + x n / N n) + x n * deltaB (N n) (ε n)
        ≤ 3600 * ((1 + Real.log (x n)) / x n) + 3636 * r n := by
    filter_upwards [hev1, hev2] with n h1 h2
    have hL := one_le_log_of_64 (hN n)
    have hxN : x n / N n ≤ r n := by
      simp only [hr]
      rw [div_le_div_iff_of_pos_right (hNpos n)]
      have : 1 ≤ x n ^ 2 * Real.log (N n) ^ 2 := by
        have : 1 ≤ x n ^ 2 := by nlinarith
        nlinarith
      nlinarith
    have hx2 : 4 * x n ^ 2 ≤ N n := by
      have : x n ^ 2 ≤ r n * N n := by
        simp only [hr]
        rw [div_mul_cancel₀ _ (hNpos n).ne']
        have : 1 ≤ x n * Real.log (N n) ^ 2 := by nlinarith
        nlinarith
      nlinarith [hNpos n]
    have hd := x_deltaB_le (hN n) (by linarith : (0 : ℝ) ≤ x n) hx2
    simp only [hxd] at hd ⊢
    simp only [hr, hxd] at hxN ⊢
    linarith
  have hnonneg : ∀ᶠ n in atTop,
      0 ≤ 3600 * ((1 + Real.log (x n)) / x n + x n / N n) + x n * deltaB (N n) (ε n) := by
    filter_upwards [hev1] with n h1
    have := deltaB_nonneg (hN n) (ε n)
    have : 0 ≤ Real.log (x n) := Real.log_nonneg h1
    have := hNpos n
    positivity
  have hlim : Tendsto (fun n => 3600 * ((1 + Real.log (x n)) / x n) + 3636 * r n) atTop (𝓝 0) := by
    have := (hlogx.const_mul 3600).add (h3.const_mul 3636)
    simpa using this
  exact squeeze_zero' hnonneg hbound hlim

lemma extZ_nonneg {f : ℕ → ℝ} (hf0 : ∀ m, 0 ≤ f m) (m : ℤ) : 0 ≤ extZ f m := by
  rcases lt_or_ge m 0 with h | h
  · rw [extZ_of_neg _ h]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
    exact hf0 k

lemma extZ_hasSum {f : ℕ → ℝ} {a : ℝ} (hf : HasSum f a) : HasSum (extZ f) a := by
  have hneg : HasSum (fun k : ℕ => extZ f (-((k : ℤ) + 1))) 0 := by
    have e : (fun k : ℕ => extZ f (-((k : ℤ) + 1))) = fun _ => 0 := by
      funext k; exact extZ_neg_succ _ k
    rw [e]; exact hasSum_zero
  have := HasSum.of_nat_of_neg_add_one (f := extZ f) hf hneg
  rwa [add_zero] at this

/-- **Theorem 3.9(c)** (`thm:landau`(c)): assume (H) along a sequence (`N_n ≥ 64`, `ε_n ≤ 1/4`;
`ε_n > 0` and `x_n ≥ 1` hold for large `n` since `x_n → ∞`), `x_n → ∞` and
`x_n³ log² N_n / N_n → 0`, and the named classical hypotheses (lattice Fourier inversion, Scheffé,
`f_L` a probability density). Let `f_n` be the law of `M_{N_n}` and `p_n ≥ 0` that of `CP_{N_n}`
(`ℕ`-indexed, U1 form of the characteristic function), with the conclusion of Theorem 3.8. Then
`(M_{N_n} - x_n log x_n)/x_n` converges in law to the law with density `f_L`. -/
theorem thm_landau_c (hInv : LatticeFourierInversionHyp) (hS : ScheffeHyp)
    (hL : LandauDensityHyp) (N : ℕ → ℕ) (ε : ℕ → ℝ) (hN : ∀ n, 64 ≤ N n)
    (hε : ∀ n, ε n ≤ 1 / 4)
    (hx : Tendsto (fun n => (N n : ℝ) * ε n) atTop atTop)
    (h3 : Tendsto (fun n => ((N n : ℝ) * ε n) ^ 3 * Real.log (N n) ^ 2 / N n) atTop (𝓝 0))
    (p f : ℕ → ℕ → ℝ) (hp0 : ∀ n m, 0 ≤ p n m) (hchar : ∀ n, CPCharFunNat (N n) (N n * ε n) (p n))
    (hcp : ∀ n, ThmCPConclusionNat (N n) (ε n) (f n) (p n))
    (hf0 : ∀ n m, 0 ≤ f n m) (hf1 : ∀ n, HasSum (f n) 1) :
    Tendsto (fun n => latticeLaw (N n * ε n) (extZ (f n)) (extZ_nonneg (hf0 n))
        (extZ_hasSum (hf1 n))) atTop (𝓝 (landauLaw hL)) := by
  set x : ℕ → ℝ := fun n => (N n : ℝ) * ε n with hxd
  have hElim := tendsto_errorBound N ε hN hx h3
  refine tendsto_latticeLaw_of_local hS hL x hx (fun n => extZ (f n))
    (fun n => extZ_nonneg (hf0 n)) (fun n => extZ_hasSum (hf1 n)) _ hElim ?_
  filter_upwards [hx.eventually_ge_atTop 1] with n hn m
  have hN0 : (0 : ℝ) ≤ N n := Nat.cast_nonneg _
  have hxN : 4 * x n ≤ N n := by simp only [hxd]; nlinarith [hε n]
  obtain ⟨hs, hc⟩ := cpCharFun_extZ (hp0 n) (hchar n)
  have hcpZ : |extZ (f n) m - extZ (p n) m| ≤ deltaB (N n) (ε n) := by
    rcases lt_or_ge m 0 with h | h
    · rw [extZ_of_neg _ h, extZ_of_neg _ h, sub_zero, abs_zero]
      exact deltaB_nonneg (hN n) (ε n)
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
      exact hcp n k
  have hb := landau_local_fN hInv hn hxN (extZ (p n)) hs hc (extZ (f n)) m hcpZ
  rw [landauDensity_eq_fL, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hb
  exact hb

end

end Kagey131.PaperD.U2
