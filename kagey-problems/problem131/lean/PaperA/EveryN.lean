import PaperA.Asymptotics

/-!
# Paper A: the crossing `N(1 - p_N)` at every `N`

We write `z_N = N(1 - p_N) = N u_N/(1 + u_N)`. Paper A's `F(x) = 2x (I_0(2x) + I_1(2x))`
gives `Φ(w) = F(w/2) = w (I_0(w) + I_1(w))`. The number `ζ_N` is the positive root of
`ζ + (1/2) log ζ = log N + (1/2) log(π/8)`, that is of `8 ζ e^{2ζ} = π N²`. Proved here:

* `N(1 - p_N) = N u_N/(1 + u_N)` (`N_one_sub_pN`) and `F(w/2) = w (I_0(w) + I_1(w)) = Φ(w)`
  (`Fcent_half_eq`);
* Lemma `lem:bracket` (root bracket): if `F(w/2) ≤ N/2` then `Nw/(N+w) ≤ N(1 - p_N)`, strictly if
  `F(w/2) < N/2`; if `F(w/2) (1 - w(w+2)/(2N)) > N/2` then `N(1 - p_N) < Nw/(N+w)`
  (`crossing_lower_of_Fcent`, `crossing_lower_of_Fcent_strict`, `crossing_upper_of_Fcent`);
* the definition of `ζ_N`, both of its defining equations, and its uniqueness
  (`zetaN`, `zetaN_eq`, `zetaN_log`, `zetaN_unique`);
* rational bounds `s/10⁴ < ζ_N < S/10⁴` from integer inequalities, through Taylor bounds for
  `exp` and `3.141592 < π < 3.141593` (`lt_zetaN_of_cert`, `zetaN_lt_of_cert`);
* Theorem `thm:every-n` for `2 ≤ N ≤ 174`: with `ε_N = ζ_N(ζ_N+1)/N + 1/(16 ζ_N²)`,
  `ζ_N + 1/(8ζ_N) - ε_N < N(1 - p_N) < ζ_N + 1/(8ζ_N)` (`every_N_crossing_small`).

The case `N ≤ 174` is computer-assisted. For each `N` the table `everyNTable` gives
`u_lo = x_lo/10⁹` and `u_hi = x_hi/10⁹` (the certificates of `data/every_n_certificates.csv`)
and `q = s/10⁴`, `Q = S/10⁴`. The kernel checks integer inequalities in exact
natural-number arithmetic (`decide +kernel`, no `native_decide`). From them the proofs get
`S_N(u_lo) < 1 < S_N(u_hi)`, `q < ζ_N < Q`, and the two comparisons of the certificate step
in the proof of Theorem `thm:every-n`, with every `ζ`-term replaced by its bound in the safe
direction: `z(u_hi) ≤ q + 1/(8Q)` and `Q + 1/(8q) - q(q+1)/N - 1/(16Q²) ≤ z(u_lo)`, where
`z(u) = N u/(1+u)`. The coefficients of `S_N` are evaluated with the multiplicative recursion
for binomial coefficients (`chooseMul`), proved equal to `Nat.choose`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset

/-! ### The crossing `z_N = N(1 - p_N)` -/

/-- `N(1 - p_N) = N u_N/(1 + u_N)`. -/
theorem N_one_sub_pN (N : ℕ) (hN : 2 ≤ N) :
    (N : ℝ) * (1 - pN N) = N * uN N / (1 + uN N) := by
  have hu : 0 < uN N := uab_pos (by omega) (by omega)
  show (N : ℝ) * (1 - 1 / (1 + uN N)) = N * uN N / (1 + uN N)
  have h1 : (1 : ℝ) + uN N ≠ 0 := by linarith
  field_simp
  ring

/-- The map `v ↦ N v/(1+v)` is strictly increasing on `v ≥ 0`. -/
theorem zmap_lt {N v₁ v₂ : ℝ} (hN : 0 < N) (h1 : 0 ≤ v₁) (h12 : v₁ < v₂) :
    N * v₁ / (1 + v₁) < N * v₂ / (1 + v₂) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos hN (sub_pos.2 h12)]

theorem zmap_le {N v₁ v₂ : ℝ} (hN : 0 < N) (h1 : 0 ≤ v₁) (h12 : v₁ ≤ v₂) :
    N * v₁ / (1 + v₁) ≤ N * v₂ / (1 + v₂) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg hN.le (sub_nonneg.2 h12)]

theorem zmap_div {N w : ℝ} (hN : 0 < N) (hw : 0 ≤ w) :
    N * (w / N) / (1 + w / N) = N * w / (N + w) := by
  have : N + w ≠ 0 := by linarith
  field_simp

/-! ### Lemma `lem:bracket`: the root bracket -/

/-- `F(w/2) = w (I_0(w) + I_1(w))`, the function `Φ(w)` of Paper A. -/
theorem Fcent_half_eq (w : ℝ) : Fcent (w / 2) = w * (besselI0 w + besselI1 w) := by
  unfold Fcent
  rw [show 2 * (w / 2) = w by ring]

/-- `(N/2) S_N(w/N) ≤ F(w/2)`, the lower half of eq. `eq:uniformbessel` at `x = w/2`. -/
theorem SN_le_one_of_Fcent (N : ℕ) (hN : 2 ≤ N) {w : ℝ} (hw : 0 < w) :
    (N : ℝ) / 2 * SN N (w / N) ≤ Fcent (w / 2) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hlow, -⟩ := uniform_bessel_central N hN (x := w / 2) (by positivity)
  have hx : w / 2 / ((N : ℝ) / 2) = w / N := by field_simp
  rw [hx] at hlow
  have hF : 0 < Fcent (w / 2) := Fcent_pos (by positivity)
  have : (N : ℝ) / 2 * SN N (w / N) / Fcent (w / 2) ≤ 1 := by linarith
  rwa [div_le_one hF] at this

/-- Lemma `lem:bracket` (a): if `Φ(w) = F(w/2) ≤ N/2` then `Nw/(N+w) ≤ z_N = N(1-p_N)`. -/
theorem crossing_lower_of_Fcent (N : ℕ) (hN : 2 ≤ N) {w : ℝ} (hw : 0 < w)
    (h : Fcent (w / 2) ≤ (N : ℝ) / 2) :
    (N : ℝ) * w / (N + w) ≤ (N : ℝ) * (1 - pN N) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 := SN_le_one_of_Fcent N hN hw
  have hS : SN N (w / N) ≤ 1 := by
    have : (N : ℝ) / 2 * SN N (w / N) ≤ (N : ℝ) / 2 * 1 := by linarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hv : w / N ≤ uN N := not_lt.1 (fun hcon => by
    have := (one_lt_Sab_iff (a := N / 2) (b := N - N / 2) (by omega) (by omega)
      (by positivity : (0 : ℝ) ≤ w / N)).2 hcon
    exact absurd hS (not_le.2 this))
  rw [N_one_sub_pN N hN, ← zmap_div hNpos hw.le]
  exact zmap_le hNpos (by positivity) hv

/-- Lemma `lem:bracket` (a), strict form: if `F(w/2) < N/2` then `Nw/(N+w) < N(1-p_N)`. -/
theorem crossing_lower_of_Fcent_strict (N : ℕ) (hN : 2 ≤ N) {w : ℝ} (hw : 0 < w)
    (h : Fcent (w / 2) < (N : ℝ) / 2) :
    (N : ℝ) * w / (N + w) < (N : ℝ) * (1 - pN N) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 := SN_le_one_of_Fcent N hN hw
  have hS : SN N (w / N) < 1 := by
    have : (N : ℝ) / 2 * SN N (w / N) < (N : ℝ) / 2 * 1 := by linarith
    exact lt_of_mul_lt_mul_left this (by positivity)
  have hv : w / N < uN N :=
    (Sab_lt_one_iff (a := N / 2) (b := N - N / 2) (by omega) (by omega)
      (by positivity : (0 : ℝ) ≤ w / N)).1 hS
  rw [N_one_sub_pN N hN, ← zmap_div hNpos hw.le]
  exact zmap_lt hNpos (by positivity) hv

/-- Lemma `lem:bracket` (b): if `F(w/2) (1 - w(w+2)/(2N)) > N/2` then `N(1-p_N) < Nw/(N+w)`. -/
theorem crossing_upper_of_Fcent (N : ℕ) (hN : 2 ≤ N) {w : ℝ} (hw : 0 < w)
    (h : (N : ℝ) / 2 < Fcent (w / 2) * (1 - w * (w + 2) / (2 * N))) :
    (N : ℝ) * (1 - pN N) < (N : ℝ) * w / (N + w) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨-, hup⟩ := uniform_bessel_central N hN (x := w / 2) (by positivity)
  have hx : w / 2 / ((N : ℝ) / 2) = w / N := by field_simp
  have hδ : w / 2 * (w / 2 + 1) / ((N : ℝ) / 2) = w * (w + 2) / (2 * N) := by
    field_simp
  rw [hx, hδ] at hup
  have hF : 0 < Fcent (w / 2) := Fcent_pos (by positivity)
  have h2 : Fcent (w / 2) * (1 - w * (w + 2) / (2 * N)) ≤ (N : ℝ) / 2 * SN N (w / N) := by
    have : 1 - w * (w + 2) / (2 * N) ≤ (N : ℝ) / 2 * SN N (w / N) / Fcent (w / 2) := by
      linarith
    rw [le_div_iff₀ hF] at this
    linarith
  have hS : 1 < SN N (w / N) := by
    have : (N : ℝ) / 2 * 1 < (N : ℝ) / 2 * SN N (w / N) := by linarith
    exact lt_of_mul_lt_mul_left this (by positivity)
  have hv : uN N < w / N :=
    (one_lt_Sab_iff (a := N / 2) (b := N - N / 2) (by omega) (by omega)
      (by positivity : (0 : ℝ) ≤ w / N)).1 hS
  rw [N_one_sub_pN N hN, ← zmap_div hNpos hw.le]
  exact zmap_lt hNpos (uab_pos (by omega) (by omega)).le hv

/-! ### `ζ_N` -/

/-- `g(t) = 8 t e^{2t}`. The number `ζ_N` is the root of `g(ζ) = π N²`. -/
noncomputable def zetaFun (t : ℝ) : ℝ := 8 * t * Real.exp (2 * t)

theorem zetaFun_continuous : Continuous zetaFun := by
  unfold zetaFun; fun_prop

theorem zetaFun_strictMonoOn : StrictMonoOn zetaFun (Set.Ici 0) := by
  intro s hs t ht hst
  simp only [Set.mem_Ici] at hs ht
  unfold zetaFun
  have h1 : Real.exp (2 * s) < Real.exp (2 * t) := Real.exp_lt_exp.2 (by linarith)
  have h2 : 0 < Real.exp (2 * s) := Real.exp_pos _
  nlinarith [mul_nonneg ht (sub_nonneg.2 h1.le), mul_pos (sub_pos.2 hst) h2]

theorem zetaFun_exists {c : ℝ} (hc : 0 < c) : ∃ t : ℝ, 0 < t ∧ zetaFun t = c := by
  have h0 : zetaFun 0 = 0 := by simp [zetaFun]
  have hc' : c ≤ zetaFun c := by
    unfold zetaFun
    have : 1 ≤ Real.exp (2 * c) := Real.one_le_exp (by linarith)
    nlinarith
  have hmem : c ∈ Set.Icc (zetaFun 0) (zetaFun c) := ⟨by rw [h0]; exact hc.le, hc'⟩
  obtain ⟨t, ⟨ht0, -⟩, ht⟩ :=
    intermediate_value_Icc hc.le zetaFun_continuous.continuousOn hmem
  refine ⟨t, ?_, ht⟩
  rcases ht0.lt_or_eq with h | h
  · exact h
  · rw [← h, h0] at ht; linarith

theorem pi_mul_sq_pos {N : ℕ} (hN : 1 ≤ N) : 0 < Real.pi * (N : ℝ) ^ 2 := by
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact mul_pos Real.pi_pos (by positivity)

/-- `ζ_N`, the positive root of `8 ζ e^{2ζ} = π N²` (equivalently of
`ζ + (1/2) log ζ = log N + (1/2) log(π/8)`, see `zetaN_log` and `zetaN_unique`). -/
noncomputable def zetaN (N : ℕ) : ℝ :=
  if h : 1 ≤ N then Classical.choose (zetaFun_exists (pi_mul_sq_pos h)) else 0

theorem zetaN_spec (N : ℕ) (hN : 1 ≤ N) :
    0 < zetaN N ∧ zetaFun (zetaN N) = Real.pi * (N : ℝ) ^ 2 := by
  unfold zetaN
  rw [dif_pos hN]
  exact Classical.choose_spec (zetaFun_exists (pi_mul_sq_pos hN))

theorem zetaN_pos (N : ℕ) (hN : 1 ≤ N) : 0 < zetaN N := (zetaN_spec N hN).1

/-- `8 ζ_N e^{2 ζ_N} = π N²`. -/
theorem zetaN_eq (N : ℕ) (hN : 1 ≤ N) :
    8 * zetaN N * Real.exp (2 * zetaN N) = Real.pi * (N : ℝ) ^ 2 := (zetaN_spec N hN).2

/-- `ζ_N + (1/2) log ζ_N = log N + (1/2) log(π/8)`. -/
theorem zetaN_log (N : ℕ) (hN : 1 ≤ N) :
    zetaN N + Real.log (zetaN N) / 2 = Real.log N + Real.log (Real.pi / 8) / 2 := by
  obtain ⟨hz, he⟩ := zetaN_spec N hN
  unfold zetaFun at he
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := congrArg Real.log he
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
  rw [Real.log_div (by positivity) (by norm_num)]
  push_cast at h
  linarith

/-- `ζ_N` is the only positive root of `ζ + (1/2) log ζ = log N + (1/2) log(π/8)`. -/
theorem zetaN_unique (N : ℕ) (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t)
    (h : t + Real.log t / 2 = Real.log N + Real.log (Real.pi / 8) / 2) : t = zetaN N := by
  have hz := zetaN_pos N hN
  have hl := zetaN_log N hN
  rcases lt_trichotomy t (zetaN N) with hlt | heq | hgt
  · have := Real.log_lt_log ht hlt
    linarith
  · exact heq
  · have := Real.log_lt_log hz hgt
    linarith

theorem lt_zetaN_of (N : ℕ) (hN : 1 ≤ N) {t : ℝ} (ht : 0 ≤ t)
    (h : zetaFun t < Real.pi * (N : ℝ) ^ 2) : t < zetaN N := by
  obtain ⟨hz, he⟩ := zetaN_spec N hN
  refine not_le.1 (fun hcon => ?_)
  have := zetaFun_strictMonoOn.monotoneOn (Set.mem_Ici.2 hz.le) (Set.mem_Ici.2 ht) hcon
  linarith

theorem zetaN_lt_of (N : ℕ) (hN : 1 ≤ N) {t : ℝ} (ht : 0 ≤ t)
    (h : Real.pi * (N : ℝ) ^ 2 < zetaFun t) : zetaN N < t := by
  obtain ⟨hz, he⟩ := zetaN_spec N hN
  refine not_le.1 (fun hcon => ?_)
  have := zetaFun_strictMonoOn.monotoneOn (Set.mem_Ici.2 ht) (Set.mem_Ici.2 hz.le) hcon
  linarith

/-! ### Rational bounds for `exp` and `ζ_N` -/

theorem exp_le_taylor {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (n : ℕ) (hn : 0 < n) :
    Real.exp y ≤ ∑ i ∈ range n, y ^ i / (i.factorial : ℝ) +
      y ^ n * (((n : ℝ) + 1) / ((n.factorial : ℝ) * n)) := by
  have h := Real.exp_bound (x := y) (by rw [abs_of_nonneg hy0]; exact hy1) hn
  rw [abs_of_nonneg hy0] at h
  have := (abs_le.1 h).2
  push_cast at this
  linarith

/-- `80000⁸ · 8! · 8` times the Taylor upper bound of `exp(s/80000)` with 8 terms. -/
def expNumU (s : ℕ) : ℕ :=
  322560 * 80000 ^ 8 + 322560 * s * 80000 ^ 7 + 161280 * s ^ 2 * 80000 ^ 6 +
    53760 * s ^ 3 * 80000 ^ 5 + 13440 * s ^ 4 * 80000 ^ 4 + 2688 * s ^ 5 * 80000 ^ 3 +
    448 * s ^ 6 * 80000 ^ 2 + 64 * s ^ 7 * 80000 + 9 * s ^ 8

/-- The denominator `80000⁸ · 8! · 8`. -/
def expDenU : ℕ := 322560 * 80000 ^ 8

/-- `80000⁷ · 7!` times the first 8 Taylor terms of `exp(S/80000)`. -/
def expNumL (S : ℕ) : ℕ :=
  5040 * 80000 ^ 7 + 5040 * S * 80000 ^ 6 + 2520 * S ^ 2 * 80000 ^ 5 + 840 * S ^ 3 * 80000 ^ 4 +
    210 * S ^ 4 * 80000 ^ 3 + 42 * S ^ 5 * 80000 ^ 2 + 7 * S ^ 6 * 80000 + S ^ 7

/-- The denominator `80000⁷ · 7!`. -/
def expDenL : ℕ := 5040 * 80000 ^ 7

theorem exp_le_expNumU {s : ℕ} (hs : s ≤ 80000) :
    Real.exp ((s : ℝ) / 80000) ≤ (expNumU s : ℝ) / expDenU := by
  have hs' : (s : ℝ) ≤ 80000 := by exact_mod_cast hs
  have h := exp_le_taylor (y := (s : ℝ) / 80000) (by positivity)
    (by rw [div_le_one (by norm_num)]; exact hs') 8 (by norm_num)
  refine h.trans (le_of_eq ?_)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, expNumU, expDenU]
  push_cast
  field_simp
  ring

theorem expNumL_le_exp (S : ℕ) :
    (expNumL S : ℝ) / expDenL ≤ Real.exp ((S : ℝ) / 80000) := by
  have h := Real.sum_le_exp_of_nonneg (x := (S : ℝ) / 80000) (by positivity) 8
  refine le_trans (le_of_eq ?_) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, expNumL, expDenL]
  push_cast
  field_simp
  ring

theorem pi_gt_rat : (3141592 / 1000000 : ℝ) < Real.pi := by
  have := Real.pi_gt_d6; norm_num at this ⊢; linarith

theorem pi_lt_rat : Real.pi < (3141593 / 1000000 : ℝ) := by
  have := Real.pi_lt_d6; norm_num at this ⊢; linarith

theorem exp_two_mul_eq (s : ℕ) :
    Real.exp (2 * ((s : ℝ) / 10000)) = Real.exp ((s : ℝ) / 80000) ^ 16 := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A rational lower bound `s/10⁴ < ζ_N` from an integer inequality. -/
theorem lt_zetaN_of_cert (N s : ℕ) (hN : 1 ≤ N) (hs : s ≤ 80000)
    (h : 8 * s * expNumU s ^ 16 * 10 ^ 6 ≤ 3141592 * N ^ 2 * 10000 * expDenU ^ 16) :
    (s : ℝ) / 10000 < zetaN N := by
  apply lt_zetaN_of N hN (by positivity)
  have hb := exp_le_expNumU hs
  have hDen : (0 : ℝ) < expDenU := by norm_num [expDenU]
  have hcast : (8 * s * expNumU s ^ 16 * 10 ^ 6 : ℝ) ≤
      3141592 * (N : ℝ) ^ 2 * 10000 * (expDenU : ℝ) ^ 16 := by exact_mod_cast h
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  unfold zetaFun
  rw [exp_two_mul_eq]
  generalize (expNumU s : ℝ) = U at hb hcast
  generalize (expDenU : ℝ) = D at hb hcast hDen
  have h1 : Real.exp ((s : ℝ) / 80000) ^ 16 ≤ (U / D) ^ 16 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hb 16
  have h2 : 8 * ((s : ℝ) / 10000) * (U / D) ^ 16 ≤ 3141592 / 1000000 * (N : ℝ) ^ 2 := by
    rw [div_pow, show 8 * ((s : ℝ) / 10000) * (U ^ 16 / D ^ 16) =
      8 * s * U ^ 16 / (10000 * D ^ 16) by ring,
      div_le_iff₀ (mul_pos (by norm_num) (pow_pos hDen 16))]
    linarith
  calc 8 * ((s : ℝ) / 10000) * Real.exp ((s : ℝ) / 80000) ^ 16
      ≤ 8 * ((s : ℝ) / 10000) * (U / D) ^ 16 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 3141592 / 1000000 * (N : ℝ) ^ 2 := h2
    _ < Real.pi * (N : ℝ) ^ 2 := mul_lt_mul_of_pos_right pi_gt_rat hN2

/-- A rational upper bound `ζ_N < S/10⁴` from an integer inequality. -/
theorem zetaN_lt_of_cert (N S : ℕ) (hN : 1 ≤ N)
    (h : 3141593 * N ^ 2 * 10000 * expDenL ^ 16 ≤ 8 * S * expNumL S ^ 16 * 10 ^ 6) :
    zetaN N < (S : ℝ) / 10000 := by
  apply zetaN_lt_of N hN (by positivity)
  have hb := expNumL_le_exp S
  have hDen : (0 : ℝ) < expDenL := by norm_num [expDenL]
  have hU0 : (0 : ℝ) ≤ expNumL S := Nat.cast_nonneg _
  have hcast : (3141593 * (N : ℝ) ^ 2 * 10000 * (expDenL : ℝ) ^ 16 : ℝ) ≤
      8 * S * (expNumL S : ℝ) ^ 16 * 10 ^ 6 := by exact_mod_cast h
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  unfold zetaFun
  rw [exp_two_mul_eq]
  generalize (expNumL S : ℝ) = U at hb hcast hU0
  generalize (expDenL : ℝ) = D at hb hcast hDen
  have h1 : (U / D) ^ 16 ≤ Real.exp ((S : ℝ) / 80000) ^ 16 :=
    pow_le_pow_left₀ (div_nonneg hU0 hDen.le) hb 16
  have h2 : 3141593 / 1000000 * (N : ℝ) ^ 2 ≤ 8 * ((S : ℝ) / 10000) * (U / D) ^ 16 := by
    rw [div_pow, show 8 * ((S : ℝ) / 10000) * (U ^ 16 / D ^ 16) =
      8 * S * U ^ 16 / (10000 * D ^ 16) by ring,
      le_div_iff₀ (mul_pos (by norm_num) (pow_pos hDen 16))]
    linarith
  calc Real.pi * (N : ℝ) ^ 2 < 3141593 / 1000000 * (N : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_right pi_lt_rat hN2
    _ ≤ 8 * ((S : ℝ) / 10000) * (U / D) ^ 16 := h2
    _ ≤ 8 * ((S : ℝ) / 10000) * Real.exp ((S : ℝ) / 80000) ^ 16 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

/-! ### The numerator of `S_N` in natural numbers -/

/-- `C(n,k)` by the multiplicative recursion `C(n,k+1) = C(n,k)(n-k)/(k+1)`. The kernel
evaluates it with `k` steps. -/
def chooseMul (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => chooseMul n k * (n - k) / (k + 1)

theorem chooseMul_eq (n k : ℕ) : chooseMul n k = n.choose k := by
  induction k with
  | zero => simp [chooseMul]
  | succ k ih =>
    rw [chooseMul, ih, ← Nat.choose_succ_right_eq]
    exact Nat.mul_div_cancel _ (Nat.succ_pos k)

/-- `W(N,k,j)` with `chooseMul` in place of `Nat.choose`. -/
def Wfast (N k j : ℕ) : ℕ :=
  if j = 0 then 0
  else if j % 2 = 1 then 2 * chooseMul (k - 1) (j / 2) * chooseMul (N - k - 1) (j / 2)
  else chooseMul (k - 1) (j / 2) * chooseMul (N - k - 1) (j / 2 - 1) +
    chooseMul (k - 1) (j / 2 - 1) * chooseMul (N - k - 1) (j / 2)

theorem Wfast_eq (N k j : ℕ) : Wfast N k j = W N k j := by
  simp only [Wfast, W, chooseMul_eq]

/-- `∑_{i<n} f i`, by recursion on `n`. -/
def natSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => natSum f n + f n

theorem natSum_eq (f : ℕ → ℕ) (n : ℕ) : natSum f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [natSum, ih, Finset.sum_range_succ]

/-- `∑_j W(N, m_N, j) x^j y^{N-1-j}`: the numerator `n_N(m_N)` of Proposition `prop:num` with
weight `y` per repeat and `x` per change. -/
def Snum (N x y : ℕ) : ℕ := natSum (fun j => Wfast N (N / 2) j * x ^ j * y ^ (N - 1 - j)) N

/-- `Snum N x y = y^{N-1} S_N(x/y)`. -/
theorem Snum_eq (N x y : ℕ) (hy : 0 < y) :
    (Snum N x y : ℝ) = (y : ℝ) ^ (N - 1) * SN N ((x : ℝ) / y) := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  unfold Snum SN Sab
  rw [natSum_eq, show N / 2 + (N - N / 2) = N by omega, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Wfast_eq]
  have hj' : j ≤ N - 1 := by simp only [Finset.mem_range] at hj; omega
  have hpow : (y : ℝ) ^ (N - 1) = (y : ℝ) ^ (N - 1 - j) * (y : ℝ) ^ j := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, div_pow]
  field_simp

/-! ### Theorem `thm:every-n` for `2 ≤ N ≤ 174` -/

/-- The integer inequalities checked for one `N`, with `u_lo = xl/10⁹`, `u_hi = xh/10⁹`,
`q = s/10⁴` and `Q = S/10⁴`:
`S_N(u_lo) < 1 < S_N(u_hi)`; `8 q e^{2q} < π N²` and `π N² < 8 Q e^{2Q}` through the Taylor
bounds; `z(u_hi) ≤ q + 1/(8Q)`; `Q + 1/(8q) ≤ z(u_lo) + q(q+1)/N + 1/(16Q²)`; `0 < s ≤ 80000`. -/
def EveryNCert (N xl xh s S : ℕ) : Prop :=
  Snum N xl (10 ^ 9) < (10 ^ 9) ^ (N - 1) ∧ (10 ^ 9) ^ (N - 1) < Snum N xh (10 ^ 9) ∧
  8 * s * expNumU s ^ 16 * 10 ^ 6 ≤ 3141592 * N ^ 2 * 10000 * expDenU ^ 16 ∧
  3141593 * N ^ 2 * 10000 * expDenL ^ 16 ≤ 8 * S * expNumL S ^ 16 * 10 ^ 6 ∧
  N * xh * (8 * 10000 * S) ≤ (8 * s * S + 10000 ^ 2) * (10 ^ 9 + xh) ∧
  (8 * s * S + 10000 ^ 2) * (10 ^ 9 + xl) * 10000 ^ 2 * N * 16 * S ^ 2 ≤
    N * xl * 8 * 10000 * s * 10000 ^ 2 * N * 16 * S ^ 2 +
    s * (s + 10000) * 8 * 10000 * s * (10 ^ 9 + xl) * 16 * S ^ 2 +
    10000 ^ 2 * 8 * 10000 * s * (10 ^ 9 + xl) * 10000 ^ 2 * N ∧
  0 < s ∧ s ≤ 80000

instance (N xl xh s S : ℕ) : Decidable (EveryNCert N xl xh s S) := by
  unfold EveryNCert; infer_instance

/-- Theorem `thm:every-n` from one certificate. -/
theorem every_N_of_cert {N xl xh s S : ℕ} (hN : 2 ≤ N) (hc : EveryNCert N xl xh s S) :
    zetaN N + 1 / (8 * zetaN N) - (zetaN N * (zetaN N + 1) / N + 1 / (16 * zetaN N ^ 2)) <
        (N : ℝ) * (1 - pN N) ∧
      (N : ℝ) * (1 - pN N) < zetaN N + 1 / (8 * zetaN N) := by
  obtain ⟨hlo, hhi, hq, hQ, hup, hlow, hs0, hs1⟩ := hc
  have hN1 : 1 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hζpos : 0 < zetaN N := zetaN_pos N hN1
  have hqζ : (s : ℝ) / 10000 < zetaN N := lt_zetaN_of_cert N s hN1 hs1 hq
  have hζQ : zetaN N < (S : ℝ) / 10000 := zetaN_lt_of_cert N S hN1 hQ
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  have hS0' : (0 : ℝ) < S := by
    have : (0 : ℝ) < (S : ℝ) / 10000 := by linarith
    linarith [this]
  -- the bracket of `u_N`
  have hSlo : SN N ((xl : ℝ) / 10 ^ 9) < 1 := by
    have e := Snum_eq N xl (10 ^ 9) (by norm_num)
    have hc : (Snum N xl (10 ^ 9) : ℝ) < ((10 ^ 9 : ℕ) : ℝ) ^ (N - 1) := by exact_mod_cast hlo
    rw [e] at hc
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hc
    exact (mul_lt_iff_lt_one_right (pow_pos (by norm_num : (0 : ℝ) < 10 ^ 9) (N - 1))).1 hc
  have hShi : 1 < SN N ((xh : ℝ) / 10 ^ 9) := by
    have e := Snum_eq N xh (10 ^ 9) (by norm_num)
    have hc : ((10 ^ 9 : ℕ) : ℝ) ^ (N - 1) < (Snum N xh (10 ^ 9) : ℝ) := by exact_mod_cast hhi
    rw [e] at hc
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hc
    exact (lt_mul_iff_one_lt_right (pow_pos (by norm_num : (0 : ℝ) < 10 ^ 9) (N - 1))).1 hc
  have hul : (xl : ℝ) / 10 ^ 9 < uN N :=
    (Sab_lt_one_iff (a := N / 2) (b := N - N / 2) (by omega) (by omega) (by positivity)).1 hSlo
  have huh : uN N < (xh : ℝ) / 10 ^ 9 :=
    (one_lt_Sab_iff (a := N / 2) (b := N - N / 2) (by omega) (by omega) (by positivity)).1 hShi
  have hzl : (N : ℝ) * xl / (10 ^ 9 + xl) < (N : ℝ) * (1 - pN N) := by
    rw [N_one_sub_pN N hN]
    have := zmap_lt hNpos (by positivity) hul
    have e : (N : ℝ) * ((xl : ℝ) / 10 ^ 9) / (1 + (xl : ℝ) / 10 ^ 9) =
        (N : ℝ) * xl / (10 ^ 9 + xl) := by
      field_simp
    rwa [e] at this
  have hzh : (N : ℝ) * (1 - pN N) < (N : ℝ) * xh / (10 ^ 9 + xh) := by
    rw [N_one_sub_pN N hN]
    have := zmap_lt hNpos (uab_pos (by omega) (by omega)).le huh
    have e : (N : ℝ) * ((xh : ℝ) / 10 ^ 9) / (1 + (xh : ℝ) / 10 ^ 9) =
        (N : ℝ) * xh / (10 ^ 9 + xh) := by
      field_simp
    rwa [e] at this
  constructor
  · -- lower bound
    have hc6 : ((8 * s * S + 10000 ^ 2) * (10 ^ 9 + xl) * 10000 ^ 2 * N * 16 * S ^ 2 : ℝ) ≤
        N * xl * 8 * 10000 * s * 10000 ^ 2 * N * 16 * S ^ 2 +
        s * (s + 10000) * 8 * 10000 * s * (10 ^ 9 + xl) * 16 * S ^ 2 +
        10000 ^ 2 * 8 * 10000 * s * (10 ^ 9 + xl) * 10000 ^ 2 * N := by
      exact_mod_cast hlow
    have hmid : (S : ℝ) / 10000 + 1 / (8 * ((s : ℝ) / 10000)) -
        ((s : ℝ) / 10000 * ((s : ℝ) / 10000 + 1) / N + 1 / (16 * ((S : ℝ) / 10000) ^ 2)) ≤
        (N : ℝ) * xl / (10 ^ 9 + xl) := by
      have hL : (0 : ℝ) < 8 * 10000 * s * (10 ^ 9 + xl) * 10000 ^ 2 * N * 16 * S ^ 2 := by
        positivity
      have key : (N : ℝ) * xl / (10 ^ 9 + xl) - ((S : ℝ) / 10000 + 1 / (8 * ((s : ℝ) / 10000)) -
          ((s : ℝ) / 10000 * ((s : ℝ) / 10000 + 1) / N + 1 / (16 * ((S : ℝ) / 10000) ^ 2))) =
          ((N * xl * 8 * 10000 * s * 10000 ^ 2 * N * 16 * S ^ 2 +
            s * (s + 10000) * 8 * 10000 * s * (10 ^ 9 + xl) * 16 * S ^ 2 +
            10000 ^ 2 * 8 * 10000 * s * (10 ^ 9 + xl) * 10000 ^ 2 * N) -
            (8 * s * S + 10000 ^ 2) * (10 ^ 9 + xl) * 10000 ^ 2 * N * 16 * S ^ 2) /
          (8 * 10000 * s * (10 ^ 9 + xl) * 10000 ^ 2 * N * 16 * S ^ 2) := by
        field_simp
        ring
      have : 0 ≤ ((N * xl * 8 * 10000 * s * 10000 ^ 2 * N * 16 * S ^ 2 +
            s * (s + 10000) * 8 * 10000 * s * (10 ^ 9 + xl) * 16 * S ^ 2 +
            10000 ^ 2 * 8 * 10000 * s * (10 ^ 9 + xl) * 10000 ^ 2 * N) -
            (8 * s * S + 10000 ^ 2) * (10 ^ 9 + xl) * 10000 ^ 2 * N * 16 * S ^ 2 : ℝ) /
          (8 * 10000 * s * (10 ^ 9 + xl) * 10000 ^ 2 * N * 16 * S ^ 2) :=
        div_nonneg (by linarith) hL.le
      linarith
    -- every `ζ`-term replaced by its bound in the safe direction
    have t1 : 1 / (8 * zetaN N) < 1 / (8 * ((s : ℝ) / 10000)) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have t2 : (s : ℝ) / 10000 * ((s : ℝ) / 10000 + 1) / N < zetaN N * (zetaN N + 1) / N := by
      apply div_lt_div_of_pos_right _ hNpos
      nlinarith
    have t3 : 1 / (16 * ((S : ℝ) / 10000) ^ 2) < 1 / (16 * zetaN N ^ 2) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    linarith
  · -- upper bound
    have hc5 : (N : ℝ) * xh * (8 * 10000 * S) ≤ (8 * s * S + 10000 ^ 2) * (10 ^ 9 + xh) := by
      exact_mod_cast hup
    have hmid : (N : ℝ) * xh / (10 ^ 9 + xh) ≤ (s : ℝ) / 10000 + 1 / (8 * ((S : ℝ) / 10000)) := by
      have e : (s : ℝ) / 10000 + 1 / (8 * ((S : ℝ) / 10000)) =
          (8 * s * S + 10000 ^ 2) / (8 * 10000 * S) := by
        field_simp
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have t1 : 1 / (8 * ((S : ℝ) / 10000)) < 1 / (8 * zetaN N) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith

/-- Certificates `(N, 10⁹ u_lo, 10⁹ u_hi, 10⁴ q, 10⁴ Q)` for `2 ≤ N ≤ 174`. The first three
columns are those of `data/every_n_certificates.csv`; `q` and `Q` are `ζ_N` rounded down and
up to the grid `10⁻⁴`, with a gap of at least `0.5 · 10⁻⁴`. -/
def everyNTable : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2, 499999999, 500000001, 5367, 5369), (3, 414213562, 414213563, 7650, 7652),
  (4, 342508031, 342508032, 9464, 9466), (5, 302775637, 302775638, 10961, 10963),
  (6, 267889742, 267889743, 12234, 12236), (7, 244373389, 244373390, 13342, 13344),
  (8, 223092910, 223092911, 14323, 14325), (9, 207304244, 207304245, 15203, 15205),
  (10, 192742240, 192742241, 16001, 16003), (11, 181296874, 181296875, 16731, 16733),
  (12, 170602972, 170602973, 17404, 17406), (13, 161866299, 161866300, 18028, 18030),
  (14, 153626343, 153626344, 18610, 18612), (15, 146704599, 146704600, 19156, 19158),
  (16, 140129932, 140129933, 19669, 19671), (17, 134489904, 134489905, 20153, 20155),
  (18, 129102879, 129102880, 20612, 20614), (19, 124405159, 124405160, 21048, 21050),
  (20, 119898116, 119898117, 21464, 21466), (21, 115915551, 115915552, 21860, 21862),
  (22, 112080615, 112080616, 22239, 22241), (23, 108654978, 108654979, 22603, 22605),
  (24, 105346208, 105346209, 22952, 22954), (25, 102363627, 102363628, 23287, 23289),
  (26, 99475303, 99475304, 23611, 23613), (27, 96851567, 96851568, 23922, 23924),
  (28, 94305067, 94305068, 24224, 24226), (29, 91976455, 91976456, 24515, 24517),
  (30, 89712002, 89712003, 24797, 24799), (31, 87629334, 87629335, 25070, 25072),
  (32, 85600601, 85600602, 25335, 25337), (33, 83725268, 83725269, 25592, 25594),
  (34, 81895753, 81895754, 25842, 25844), (35, 80196990, 80196991, 26085, 26087),
  (36, 78537511, 78537512, 26321, 26323), (37, 76990476, 76990477, 26552, 26554),
  (38, 75477401, 75477402, 26776, 26778), (39, 74061797, 74061798, 26995, 26997),
  (40, 72675771, 72675772, 27209, 27211), (41, 71374843, 71374844, 27418, 27420),
  (42, 70099848, 70099849, 27622, 27624), (43, 68899630, 68899631, 27821, 27823),
  (44, 67722288, 67722289, 28016, 28018), (45, 66611041, 66611042, 28207, 28209),
  (46, 65520084, 65520085, 28394, 28396), (47, 64487861, 64487862, 28577, 28579),
  (48, 63473727, 63473728, 28756, 28758), (49, 62512044, 62512045, 28932, 28934),
  (50, 61566562, 61566563, 29104, 29106), (51, 60668129, 60668130, 29273, 29275),
  (52, 59784270, 59784271, 29439, 29441), (53, 58942792, 58942793, 29602, 29604),
  (54, 58114474, 58114475, 29762, 29764), (55, 57324481, 57324482, 29919, 29921),
  (56, 56546415, 56546416, 30073, 30075), (57, 55803129, 55803130, 30225, 30227),
  (58, 55070690, 55070691, 30375, 30377), (59, 54369920, 54369921, 30521, 30523),
  (60, 53679046, 53679047, 30666, 30668), (61, 53017097, 53017098, 30808, 30810),
  (62, 52364205, 52364206, 30948, 30950), (63, 51737807, 51737808, 31086, 31088),
  (64, 51119720, 51119721, 31222, 31224), (65, 50525970, 50525971, 31355, 31357),
  (66, 49939866, 49939867, 31487, 31489), (67, 49376172, 49376173, 31617, 31619),
  (68, 48819530, 48819531, 31745, 31747), (69, 48283576, 48283577, 31871, 31873),
  (70, 47754141, 47754142, 31995, 31997), (71, 47243845, 47243846, 32118, 32120),
  (72, 46739589, 46739590, 32239, 32241), (73, 46253078, 46253079, 32358, 32360),
  (74, 45772175, 45772176, 32476, 32478), (75, 45307758, 45307759, 32593, 32595),
  (76, 44848558, 44848559, 32708, 32710), (77, 44404703, 44404704, 32821, 32823),
  (78, 43965710, 43965711, 32933, 32935), (79, 43541028, 43541029, 33044, 33046),
  (80, 43120884, 43120885, 33153, 33155), (81, 42714109, 42714110, 33261, 33263),
  (82, 42311578, 42311579, 33367, 33369), (83, 41921556, 41921557, 33473, 33475),
  (84, 41535509, 41535510, 33577, 33579), (85, 41161184, 41161185, 33680, 33682),
  (86, 40790589, 40790590, 33782, 33784), (87, 40430997, 40430998, 33883, 33885),
  (88, 40074908, 40074909, 33982, 33984), (89, 39729160, 39729161, 34081, 34083),
  (90, 39386708, 39386709, 34178, 34180), (91, 39053989, 39053990, 34275, 34277),
  (92, 38724375, 38724376, 34370, 34372), (93, 38403933, 38403934, 34465, 34467),
  (94, 38086420, 38086421, 34558, 34560), (95, 37777562, 37777563, 34650, 34652),
  (96, 37471469, 37471470, 34742, 34744), (97, 37173554, 37173555, 34833, 34835),
  (98, 36878252, 36878253, 34922, 34924), (99, 36590685, 36590686, 35011, 35013),
  (100, 36305591, 36305592, 35099, 35101), (101, 36027821, 36027822, 35186, 35188),
  (102, 35752396, 35752397, 35272, 35274), (103, 35483911, 35483912, 35358, 35360),
  (104, 35217651, 35217652, 35443, 35445), (105, 34957976, 34957977, 35526, 35528),
  (106, 34700413, 34700414, 35610, 35612), (107, 34449105, 34449106, 35692, 35694),
  (108, 34199803, 34199804, 35774, 35776), (109, 33956448, 33956449, 35854, 35856),
  (110, 33715002, 33715003, 35935, 35937), (111, 33479213, 33479214, 36014, 36016),
  (112, 33245242, 33245243, 36093, 36095), (113, 33016660, 33016661, 36171, 36173),
  (114, 32789809, 32789810, 36248, 36250), (115, 32568095, 32568096, 36325, 36327),
  (116, 32348032, 32348033, 36401, 36403), (117, 32132869, 32132870, 36477, 36479),
  (118, 31919281, 31919282, 36551, 36553), (119, 31710372, 31710373, 36626, 36628),
  (120, 31502968, 31502969, 36699, 36701), (121, 31300034, 31300035, 36772, 36774),
  (122, 31098539, 31098540, 36845, 36847), (123, 30901317, 30901318, 36917, 36919),
  (124, 30705472, 30705473, 36988, 36990), (125, 30513715, 30513716, 37059, 37061),
  (126, 30323277, 30323278, 37129, 37131), (127, 30136753, 30136754, 37199, 37201),
  (128, 29951492, 29951493, 37268, 37270), (129, 29769982, 29769983, 37337, 37339),
  (130, 29589682, 29589683, 37405, 37407), (131, 29412978, 29412979, 37472, 37474),
  (132, 29237435, 29237436, 37539, 37541), (133, 29065342, 29065343, 37606, 37608),
  (134, 28894363, 28894364, 37672, 37674), (135, 28726696, 28726697, 37738, 37740),
  (136, 28560099, 28560100, 37803, 37805), (137, 28396683, 28396684, 37868, 37870),
  (138, 28234295, 28234296, 37932, 37934), (139, 28074964, 28074965, 37996, 37998),
  (140, 27916622, 27916623, 38059, 38061), (141, 27761220, 27761221, 38122, 38124),
  (142, 27606768, 27606769, 38184, 38186), (143, 27455145, 27455146, 38246, 38248),
  (144, 27304437, 27304438, 38308, 38310), (145, 27156452, 27156453, 38369, 38371),
  (146, 27009348, 27009349, 38430, 38432), (147, 26864867, 26864868, 38491, 38493),
  (148, 26721235, 26721236, 38551, 38553), (149, 26580130, 26580131, 38610, 38612),
  (150, 26439843, 26439844, 38669, 38671), (151, 26301993, 26301994, 38728, 38730),
  (152, 26164932, 26164933, 38787, 38789), (153, 26030222, 26030223, 38845, 38847),
  (154, 25896273, 25896274, 38902, 38904), (155, 25764591, 25764592, 38960, 38962),
  (156, 25633645, 25633646, 39017, 39019), (157, 25504889, 25504890, 39073, 39075),
  (158, 25376842, 25376843, 39130, 39132), (159, 25250910, 25250911, 39186, 39188),
  (160, 25125664, 25125665, 39241, 39243), (161, 25002461, 25002462, 39297, 39299),
  (162, 24879921, 24879922, 39352, 39354), (163, 24759357, 24759358, 39406, 39408),
  (164, 24639434, 24639435, 39460, 39462), (165, 24521421, 24521422, 39514, 39516),
  (166, 24404028, 24404029, 39568, 39570), (167, 24288483, 24288484, 39621, 39623),
  (168, 24173538, 24173539, 39674, 39676), (169, 24060383, 24060384, 39727, 39729),
  (170, 23947808, 23947809, 39779, 39781), (171, 23836965, 23836966, 39832, 39834),
  (172, 23726684, 23726685, 39883, 39885), (173, 23618081, 23618082, 39935, 39937),
  (174, 23510023, 23510024, 39986, 39988)
]

set_option maxRecDepth 100000 in
/-- The kernel checks every certificate of the table. -/
theorem everyNTable_ok :
    ∀ c ∈ everyNTable, EveryNCert c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The table has an entry for every `2 ≤ N ≤ 174`. -/
theorem everyNTable_covers : ∀ N, N < 175 → 2 ≤ N → ∃ c ∈ everyNTable, c.1 = N := by
  decide +kernel

/-- Theorem `thm:every-n` for `2 ≤ N ≤ 174`: with `ε_N = ζ_N(ζ_N+1)/N + 1/(16 ζ_N²)`,
`ζ_N + 1/(8ζ_N) - ε_N < N(1 - p_N) < ζ_N + 1/(8ζ_N)`. Computer-assisted: the certificates
are checked by the kernel in `everyNTable_ok`. -/
theorem every_N_crossing_small (N : ℕ) (hN : 2 ≤ N) (hN' : N ≤ 174) :
    zetaN N + 1 / (8 * zetaN N) - (zetaN N * (zetaN N + 1) / N + 1 / (16 * zetaN N ^ 2)) <
        (N : ℝ) * (1 - pN N) ∧
      (N : ℝ) * (1 - pN N) < zetaN N + 1 / (8 * zetaN N) := by
  obtain ⟨c, hc, rfl⟩ := everyNTable_covers N (by omega) hN
  exact every_N_of_cert hN (everyNTable_ok c hc)

end Kagey131
