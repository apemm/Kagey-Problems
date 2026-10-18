import PaperD.U3_Odd

/-!
# Paper D, track U3: Corollary 3.11 (where the modes are)

* `mode_master`: Corollary 3.11(a) in a deterministic form. If `|x f_N(m) - f_L(λ_m)| ≤ E` for
  every `m`, `f_L(λ_{m'}) ≥ f_L(λL) - δ` at some `m' ≤ N`, `2E + δ + 8x/(3N) < κ` and
  `8(x log x + (λL+1)x) + 8 ≤ N`, then every maximizer `m₁` of `f_N` has
  `(λ_{m₁} - λL)² ≤ (2E + δ)/κ`, and every mode `a* = N - m* ≥ N/2` of `P_N` has
  `(λ_{m*} - λL)² ≤ (2E + δ + 8x/(3N))/κ`. The remote mirror `f_N(N - m*)` is controlled by the
  unimodality of `f_N` and its total mass only (no Lemmas B.1, B.2, B.5 and no hypothesis
  `m_h ≤ N/4`).
* `uniform_mode_rate`: Corollary 3.11(b), uniformly over the window `log N ≤ x ≤ 2 log N`:
  `|m - x log x - λL x| ≤ K √(x log x)` for every maximizer of `f_N` and every `m* = N - a*`.
* `cor_mode_location_b`: the same at the crossing, for every large `N`, even or odd.
-/

namespace Kagey131.PaperD

open Real Filter Topology Set

/-- **Corollary 3.11(a), deterministic form.** See the module docstring. -/
theorem mode_master {fL : ℝ → ℝ} {lL κ : ℝ} {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {N : ℕ}
    (hN : 1 ≤ N) {x E δ : ℝ} (hx0 : 0 < x) (hκ : 0 < κ)
    (hsep : ∀ l, κ * min 1 ((l - lL) ^ 2) ≤ fL lL - fL l)
    (hE : ∀ m, |x * law ε N m - fL (lamCoord x m)| ≤ E)
    {m' : ℕ} (hm'N : m' ≤ N) (hm' : fL lL - δ ≤ fL (lamCoord x m'))
    (hS : 2 * E + δ + 8 * x / (3 * N) < κ)
    (hX : 8 * (x * Real.log x + lL * x + x) + 8 ≤ N) :
    (∀ m₁ : ℕ, (∀ k, law ε N k ≤ law ε N m₁) → (lamCoord x m₁ - lL) ^ 2 ≤ (2 * E + δ) / κ) ∧
      ∀ m : ℕ, 2 * m ≤ N → (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - m)) →
        (lamCoord x m - lL) ^ 2 ≤ (2 * E + δ + 8 * x / (3 * N)) / κ := by
  obtain ⟨mh, -, hmhmax, htail⟩ := exists_tail_mode h0.le h1 hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hT0 : 0 ≤ 8 * x / (3 * N) := by positivity
  have hfm : ∀ m₁ : ℕ, (∀ k, law ε N k ≤ law ε N m₁) →
      (lamCoord x m₁ - lL) ^ 2 ≤ (2 * E + δ) / κ ∧ |lamCoord x m₁ - lL| < 1 :=
    fun m₁ h => sep_small hκ (fmode_sep hx0.le hE hsep hm' h) (by linarith)
  refine ⟨fun m₁ h => (hfm m₁ h).1, ?_⟩
  intro m hmN hmode
  obtain ⟨-, hmh1⟩ := hfm mh hmhmax
  obtain ⟨hmhX, -⟩ := lam_bounds hx0 hmh1
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmh0 : (0 : ℝ) ≤ mh := Nat.cast_nonneg mh
  have hNm : (2 * m : ℝ) ≤ N := by exact_mod_cast hmN
  have hmhR : (mh : ℝ) + m ≤ N := by linarith
  have hmh_m : mh + m ≤ N := by exact_mod_cast hmhR
  have hTb : x / ((N : ℝ) - m - mh + 1) ≤ 8 * x / (3 * N) := by
    have hD : 3 * (N : ℝ) / 8 ≤ (N : ℝ) - m - mh + 1 := by linarith
    calc x / ((N : ℝ) - m - mh + 1) ≤ x / (3 * (N : ℝ) / 8) :=
          div_le_div_of_nonneg_left hx0.le (by positivity) hD
      _ = 8 * x / (3 * N) := by field_simp
  obtain ⟨sm, -⟩ := Pmode_sep h0.le h1 hN hx0.le hE hsep hm'N hm' hmN hmode htail hmh_m hTb
  exact (sep_small hκ sm hS).1

/-- From `d² ≤ K log x/(κ x)`: `x|d| ≤ √(K/κ) √(x log x)`. -/
theorem abs_mul_le_sqrt {x d K κ : ℝ} (hx : 0 < x) (hκ : 0 < κ) (hK : 0 ≤ K)
    (hlx : 0 ≤ Real.log x) (h : d ^ 2 ≤ K * Real.log x / x / κ) :
    x * |d| ≤ Real.sqrt (K / κ) * Real.sqrt (x * Real.log x) := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  have e : (x * |d|) ^ 2 = x ^ 2 * d ^ 2 := by rw [mul_pow, sq_abs]
  rw [e]
  have h2 : x ^ 2 * d ^ 2 ≤ x ^ 2 * (K * Real.log x / x / κ) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have e2 : x ^ 2 * (K * Real.log x / x / κ) = K / κ * (x * Real.log x) := by
    field_simp
  linarith

set_option maxHeartbeats 8000000 in
/-- **Corollary 3.11(b), uniformly in the window.** Assume Theorem 3.9(b) for `fL`, the
separation of Lemma 3.10(c) with a constant `κ > 0`, and `fL'(λL) = 0` (Lemma 3.10(b)). Then
there is `K` such that for all large `N` and every `0 < ε < 1` with `log N ≤ x = Nε ≤ 2 log N`:
every maximizer `m₁` of `f_N` and every `m* = N - a*` for a mode `a* ≥ N/2` of `P_N` satisfy
`|m - x log x - λL x| ≤ K √(x log x)`. -/
theorem uniform_mode_rate {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ} (hκ : 0 < κ)
    (hsep : ∀ l, κ * min 1 ((l - lL) ^ 2) ≤ fL lL - fL l) (hd : HasDerivAt fL 0 lL) :
    ∃ K : ℝ, ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ε < 1 → Real.log N ≤ (N : ℝ) * ε →
      (N : ℝ) * ε ≤ 2 * Real.log N →
      (∀ m₁ : ℕ, (∀ k, law ε N k ≤ law ε N m₁) →
        |(m₁ : ℝ) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε))) ∧
      ∀ m : ℕ, 2 * m ≤ N → (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - m)) →
        |(m : ℝ) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε)) := by
  obtain ⟨C, hC⟩ := hLim
  set K0 : ℝ := 6 * |C| + 4 with hK0
  have hK00 : 0 < K0 := by positivity
  refine ⟨Real.sqrt (K0 / κ), ?_⟩
  -- the derivative gives `|fL l - fL lL| ≤ |l - lL|` near `λL`
  obtain ⟨ρ, hρ, hρd⟩ := Metric.eventually_nhds_iff.mp
    ((hasDerivAt_iff_isLittleO.mp hd).def one_pos)
  have hc56 : 0 < 56 + 16 * |lL| := by positivity
  filter_upwards [tendsto_logNat.eventually_ge_atTop 30,
    (tendsto_order.1 (tendsto_logpow_div_nat 2)).2 (1 / (56 + 16 * |lL|)) (by positivity),
    (tendsto_order.1 (tendsto_logpow_div_nat 6)).2 (1 / 600) (by norm_num),
    (tendsto_order.1 (tendsto_one_add_log_two_div.comp tendsto_logNat)).2 (κ / K0)
      (by positivity),
    tendsto_logNat.eventually_ge_atTop (1 / ρ), eventually_ge_atTop 64,
    (Real.tendsto_log_atTop.comp tendsto_logNat).eventually_ge_atTop (-lL)] with
    N hL hX2 h6 hlk hxρ h64 hll
  intro ε he0 he1 hxL hx2L
  simp only [Function.comp] at hlk hll
  set L := Real.log (N : ℝ) with hLdef
  set x := (N : ℝ) * ε with hxdef
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hx0 : 0 < x := by linarith
  have hlx1 : 1 ≤ Real.log x := by
    have : (1 : ℝ) ≤ Real.log 30 := by linarith [three_lt_log_thirty]
    linarith [Real.log_le_log (by norm_num) (show (30 : ℝ) ≤ x by linarith)]
  have hlx2 : Real.log x ≤ 2 * L := by
    have := Real.log_le_sub_one_of_pos hx0; linarith
  rw [div_lt_iff₀ hN] at hX2 h6
  have hL6 : 600 * L ^ 6 < N := by linarith
  have hL2N : 32 * L ^ 2 ≤ N := by
    have : L ^ 2 ≤ L ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  have hL5 : 1 ≤ L ^ 5 := one_le_pow₀ (by linarith)
  -- (H) holds
  have hε4 : ε ≤ 1 / 4 := by
    have : (N : ℝ) * ε ≤ (N : ℝ) * (1 / 4) := by nlinarith
    exact le_of_mul_le_mul_left this hN
  -- the Landau error `E ≤ (3|C|+1) log x / x`
  set E : ℝ := (3 * |C| + 1) * Real.log x / x with hEdef
  have hEb : ∀ m, |x * law ε N m - fL (lamCoord x m)| ≤ E := by
    intro m
    have key := hC N ε h64 he0 hε4 (by rw [← hxdef]; linarith) m
    have hdB : x * deltaB N x ≤ 300 * L ^ 5 / N :=
      xdeltaB_le hN (by linarith) (by linarith) hx2L
        (by rw [div_le_iff₀ hN]; nlinarith)
    have hdB2 : 300 * L ^ 5 / N ≤ 1 / x := by
      rw [div_le_div_iff₀ hN hx0]
      have : 300 * L ^ 5 * x ≤ 600 * L ^ 6 := by
        have : L ^ 6 = L ^ 5 * L := by ring
        rw [this]; nlinarith
      linarith
    have hxN : x / N ≤ 1 / x := by
      rw [div_le_div_iff₀ hN hx0]; nlinarith
    have hq : (1 + Real.log x) / x ≤ 2 * Real.log x / x :=
      div_le_div_of_nonneg_right (by linarith) hx0.le
    have ha0 : 0 ≤ (1 + Real.log x) / x + x / N := by positivity
    have hCa : C * ((1 + Real.log x) / x + x / N) ≤ |C| * ((1 + Real.log x) / x + x / N) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) ha0
    have hCa2 : |C| * ((1 + Real.log x) / x + x / N) ≤ |C| * (2 * Real.log x / x + 1 / x) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
    have hfin : |C| * (2 * Real.log x / x + 1 / x) + 1 / x ≤ E := by
      rw [hEdef]
      have e : |C| * (2 * Real.log x / x + 1 / x) + 1 / x =
          (2 * |C| * Real.log x + |C| + 1) / x := by field_simp
      rw [e]
      apply div_le_div_of_nonneg_right _ hx0.le
      nlinarith [abs_nonneg C]
    linarith
  -- the window conditions
  have hlogx : Real.log x ≤ Real.log (2 * L) := Real.log_le_log hx0 hx2L
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
    have hb : (56 + 16 * |lL|) * L ^ 2 < (N : ℝ) := by
      calc (56 + 16 * |lL|) * L ^ 2
          < (56 + 16 * |lL|) * (1 / (56 + 16 * |lL|) * (N : ℝ)) :=
            mul_lt_mul_of_pos_left hX2 hc56
        _ = (N : ℝ) := by field_simp
    nlinarith [abs_nonneg lL]
  -- the point `m'`
  have hlxl : 0 ≤ Real.log x + lL := by
    have : Real.log L ≤ Real.log x := Real.log_le_log (by linarith) hxL
    linarith
  set a := x * Real.log x + lL * x with ha
  have ha0 : 0 ≤ a := by
    have e : a = x * (Real.log x + lL) := by rw [ha]; ring
    rw [e]; exact mul_nonneg hx0.le hlxl
  have hnear := floor_half_near ha0
  have hm'R : ((⌊a + 1 / 2⌋₊ : ℕ) : ℝ) ≤ a + 1 / 2 := Nat.floor_le (by linarith)
  have hm'N : ⌊a + 1 / 2⌋₊ ≤ N := by
    have : ((⌊a + 1 / 2⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast this
  have hlam : |lamCoord x ⌊a + 1 / 2⌋₊ - lL| ≤ 1 / (2 * x) := by
    have e : lamCoord x ⌊a + 1 / 2⌋₊ - lL = (((⌊a + 1 / 2⌋₊ : ℕ) : ℝ) - a) / x := by
      unfold lamCoord; rw [ha]; field_simp; ring
    rw [e, abs_div, abs_of_pos hx0, div_le_div_iff₀ hx0 (by positivity)]
    nlinarith
  have hlamρ : dist (lamCoord x ⌊a + 1 / 2⌋₊) lL < ρ := by
    rw [Real.dist_eq]
    have h1 : 1 ≤ L * ρ := by rwa [div_le_iff₀ hρ] at hxρ
    have : 1 / (2 * x) < ρ := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have hm'f : fL lL - 1 / (2 * x) ≤ fL (lamCoord x ⌊a + 1 / 2⌋₊) := by
    have := hρd hlamρ
    simp only [smul_zero, sub_zero, Real.norm_eq_abs, one_mul] at this
    have := (abs_le.mp this).1
    linarith
  -- the total error `S ≤ K0 log x / x < κ`
  have hδ : 1 / (2 * x) ≤ Real.log x / x := by
    rw [div_le_div_iff₀ (by positivity) hx0]; nlinarith
  have hT : 8 * x / (3 * N) ≤ Real.log x / x := by
    rw [div_le_div_iff₀ (by positivity) hx0]
    have : x ^ 2 ≤ 4 * L ^ 2 := by nlinarith
    nlinarith
  have hS : 2 * E + 1 / (2 * x) + 8 * x / (3 * N) ≤ K0 * Real.log x / x := by
    have e : K0 * Real.log x / x = 2 * E + 2 * (Real.log x / x) := by
      rw [hEdef, hK0]; field_simp; ring
    rw [e]; linarith
  have hlk' : K0 * Real.log x / x < κ := by
    have hq : Real.log x / x ≤ (1 + Real.log (2 * L)) / L := by
      calc Real.log x / x ≤ (1 + Real.log (2 * L)) / x :=
            div_le_div_of_nonneg_right (by linarith) hx0.le
        _ ≤ (1 + Real.log (2 * L)) / L :=
            div_le_div_of_nonneg_left (by linarith) (by linarith) hxL
    have := (lt_div_iff₀' hK00).mp hlk
    rw [mul_div_assoc]
    nlinarith
  obtain ⟨hf, hP⟩ := mode_master he0 he1 (by omega) hx0 hκ hsep hEb hm'N hm'f
    (by linarith) hXb
  have hlx0 : 0 ≤ Real.log x := by linarith
  have conv : ∀ k : ℕ, (lamCoord x k - lL) ^ 2 ≤ K0 * Real.log x / x / κ →
      |(k : ℝ) - x * Real.log x - lL * x| ≤ Real.sqrt (K0 / κ) * Real.sqrt (x * Real.log x) := by
    intro k hk
    have e : (k : ℝ) - x * Real.log x - lL * x = x * (lamCoord x k - lL) := by
      unfold lamCoord; field_simp
    rw [e, abs_mul, abs_of_pos hx0]
    exact abs_mul_le_sqrt hx0 hκ hK00.le hlx0 hk
  refine ⟨fun m₁ hm₁ => conv m₁ ?_, fun m hmN hmode => conv m ?_⟩
  · have := hf m₁ hm₁
    calc (lamCoord x m₁ - lL) ^ 2 ≤ (2 * E + 1 / (2 * x)) / κ := this
      _ ≤ K0 * Real.log x / x / κ := by
        apply div_le_div_of_nonneg_right _ hκ.le
        have : 0 ≤ 8 * x / (3 * N) := by positivity
        linarith
  · have := hP m hmN hmode
    calc (lamCoord x m - lL) ^ 2 ≤ (2 * E + 1 / (2 * x) + 8 * x / (3 * N)) / κ := this
      _ ≤ K0 * Real.log x / x / κ := div_le_div_of_nonneg_right hS hκ.le

/-- **Corollary 3.11(b) (`cor:mode-location`(b)), modulo Theorem 3.9(b) and Lemma 3.10.** There
are `K` and `N₁` such that for every `N ≥ N₁`, even or odd, at every crossing
`ε ∈ (0,1)` (`P_N(⌈N/2⌉) = E_N`), with `x = Nε`: every mode `a* ≥ N/2` of `P_N` has
`|(N - a*) - x log x - λL x| ≤ K √(x log x)`, and so has every maximizer of `f_N` (in
particular its largest mode `m_h`). -/
theorem cor_mode_location_b {fL : ℝ → ℝ} (hLim : LandauLimitHyp fL) {lL κ : ℝ} (hκ : 0 < κ)
    (hsep : ∀ l, κ * min 1 ((l - lL) ^ 2) ≤ fL lL - fL l) (hd : HasDerivAt fL 0 lL) :
    ∃ K : ℝ, ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ewBin ε N ((N + 1) / 2) = ewBin ε N N →
      (∀ m₁ : ℕ, (∀ k, law ε N k ≤ law ε N m₁) →
        |(m₁ : ℝ) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε))) ∧
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) → (N : ℤ) ≤ 2 * aS →
        |((N : ℝ) - aS) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε)) := by
  obtain ⟨K, hK⟩ := uniform_mode_rate hLim hκ hsep hd
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((hK.and crossing_window).and (eventually_ge_atTop 1))
  refine ⟨K, N₁, fun N hN ε h0 h1 hc => ?_⟩
  obtain ⟨⟨hKN, hWN⟩, hN1⟩ := hN₁ N hN
  obtain ⟨hxL, hx2L⟩ := hWN ε h0 h1 hc
  obtain ⟨hf, hP⟩ := hKN ε h0 h1 hxL hx2L
  refine ⟨hf, fun aS hmode haS => ?_⟩
  have haN := mode_le_N h0 h1 hN1 hmode
  set m := ((N : ℤ) - aS).toNat with hm
  have hmZ : (m : ℤ) = (N : ℤ) - aS := by rw [hm]; omega
  have hmode' : ∀ a : ℤ, lawZ ε N a ≤ lawZ ε N ((N : ℤ) - m) := by
    rw [hmZ, show (N : ℤ) - ((N : ℤ) - aS) = aS by ring]; exact hmode
  have := hP m (by omega) hmode'
  have hmR : (m : ℝ) = (N : ℝ) - aS := by exact_mod_cast hmZ
  rwa [hmR] at this

/-- Corollary 3.11(b) for the Landau density, from Theorem 3.9(b) and Lemma 3.10. -/
theorem cor_mode_location_b_landau (hLim : LandauLimitHyp landauDensity) {lL : ℝ}
    (hMode : LandauModeHyp landauDensity lL) :
    ∃ K : ℝ, ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ewBin ε N ((N + 1) / 2) = ewBin ε N N →
      (∀ m₁ : ℕ, (∀ k, law ε N k ≤ law ε N m₁) →
        |(m₁ : ℝ) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε))) ∧
      ∀ aS : ℤ, (∀ a : ℤ, lawZ ε N a ≤ lawZ ε N aS) → (N : ℤ) ≤ 2 * aS →
        |((N : ℝ) - aS) - (N : ℝ) * ε * Real.log ((N : ℝ) * ε) - lL * ((N : ℝ) * ε)| ≤
          K * Real.sqrt ((N : ℝ) * ε * Real.log ((N : ℝ) * ε)) :=
  cor_mode_location_b hLim (by norm_num) hMode.2.2 hMode.2.1.1

end Kagey131.PaperD
