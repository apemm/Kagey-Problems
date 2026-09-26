import PaperA.RootBounds

/-!
# Paper A, Theorem `thm:root` (c): `1 - p_N ~ (log N)/N`

The paper derives (c) from Corollary `cor:every-n` (b). Here (c) comes instead from the
uniform Bessel estimate `eq:uniformbessel` together with
`F(x) ≤ 4x e^{2x}` and `F(x) ≥ 2 e^{2x-4}` (`x ≥ 1`); the lower bound on `F` uses the
Stirling-type bound `r! ≤ e √r (r/e)^r` (Mathlib's `stirlingSeq` is decreasing). Proved here:

* for every `0 < ε < 1`, eventually `(1-ε) log N / N < u_N < (1+ε) log N / N`;
* `N u_N / log N → 1`, `N (1 - p_N) / log N → 1`, and `p_N → 1`;
* the quantitative form of `u_N - u_B = O((log N)²/N²)` in Theorem `thm:bessel` (iii):
  eventually `0 ≤ u_N - u_B ≤ 8 (log N)²/N²`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset Filter Topology

/-! ### Exponential bounds for the Bessel series -/

theorem two_mul_factorial_le (r : ℕ) :
    ((2 * r).factorial : ℝ) ≤ 4 ^ r * ((r.factorial : ℝ) ^ 2) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show r ≤ 2 * r by omega)
  rw [show 2 * r - r = r by omega] at h1
  have h2 := Nat.centralBinom_le_four_pow r
  rw [Nat.centralBinom_eq_two_mul_choose] at h2
  have : (2 * r).factorial ≤ 4 ^ r * (r.factorial ^ 2) := by
    rw [← h1, sq, ← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)
  exact_mod_cast this

theorem two_mul_add_one_factorial_le (r : ℕ) :
    ((2 * r + 1).factorial : ℝ) ≤ 4 ^ r * ((r.factorial : ℝ) * ((r + 1).factorial : ℝ)) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show r ≤ 2 * r + 1 by omega)
  rw [show 2 * r + 1 - r = r + 1 by omega] at h1
  have h2 := Nat.choose_middle_le_pow r
  have : (2 * r + 1).factorial ≤ 4 ^ r * (r.factorial * (r + 1).factorial) := by
    rw [← h1, ← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)
  exact_mod_cast this

theorem exp_hasSum (y : ℝ) : HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
  have := (Real.summable_pow_div_factorial y).hasSum
  rwa [show (∑' n : ℕ, y ^ n / (n.factorial : ℝ)) = Real.exp y by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]] at this

/-- `I_0(2x) ≤ e^{2x}` for `x ≥ 0`. -/
theorem besselI0_le_exp {x : ℝ} (hx : 0 ≤ x) : besselI0 (2 * x) ≤ Real.exp (2 * x) := by
  set f : ℕ → ℝ := fun n => (2 * x) ^ n / (n.factorial : ℝ)
  have hf : Summable f := Real.summable_pow_div_factorial _
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hinj : Function.Injective (fun r : ℕ => 2 * r) := fun a b h => by simpa using h
  rw [besselI0_two_mul, ← (exp_hasSum (2 * x)).tsum_eq]
  calc ∑' r, b0 x r ≤ ∑' r, f (2 * r) := by
        refine (summable_b0 x).tsum_le_tsum (fun r => ?_) (hf.comp_injective hinj)
        show x ^ (2 * r) / (r.factorial : ℝ) ^ 2 ≤ (2 * x) ^ (2 * r) / ((2 * r).factorial : ℝ)
        have h4 : (2 : ℝ) ^ (2 * r) = 4 ^ r := by rw [pow_mul]; norm_num
        have hfac := two_mul_factorial_le r
        have hp : (0 : ℝ) < ((2 * r).factorial : ℝ) := by positivity
        have hq : (0 : ℝ) < (r.factorial : ℝ) ^ 2 := by positivity
        rw [mul_pow, h4, div_le_div_iff₀ hq hp]
        have hx2 : 0 ≤ x ^ (2 * r) := by rw [pow_mul]; positivity
        nlinarith [mul_le_mul_of_nonneg_left hfac hx2]
    _ ≤ ∑' n, f n := tsum_comp_le_tsum_of_inj hf hf0 hinj

/-- `I_1(2x) ≤ e^{2x}` for `x ≥ 0`. -/
theorem besselI1_le_exp {x : ℝ} (hx : 0 ≤ x) : besselI1 (2 * x) ≤ Real.exp (2 * x) := by
  set f : ℕ → ℝ := fun n => (2 * x) ^ n / (n.factorial : ℝ)
  have hf : Summable f := Real.summable_pow_div_factorial _
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hinj : Function.Injective (fun r : ℕ => 2 * r + 1) := fun a b h => by simpa using h
  rw [besselI1_two_mul, ← (exp_hasSum (2 * x)).tsum_eq]
  calc ∑' r, b1 x r ≤ ∑' r, f (2 * r + 1) := by
        refine (summable_b1 x).tsum_le_tsum (fun r => ?_) (hf.comp_injective hinj)
        simp only [b1, f]
        have hfac := two_mul_add_one_factorial_le r
        have hp : (0 : ℝ) < ((2 * r + 1).factorial : ℝ) := by positivity
        have hq : (0 : ℝ) < (r.factorial : ℝ) * ((r + 1).factorial : ℝ) := by positivity
        rw [div_le_div_iff₀ hq hp, mul_pow, pow_succ 2, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]
        have : 0 ≤ x ^ (2 * r + 1) := by positivity
        have h4 : (0 : ℝ) ≤ 4 ^ r := by positivity
        nlinarith
    _ ≤ ∑' n, f n := tsum_comp_le_tsum_of_inj hf hf0 hinj

/-- `F(x) ≤ 4 x e^{2x}` for `x ≥ 0`. -/
theorem Fcent_le {x : ℝ} (hx : 0 ≤ x) : Fcent x ≤ 4 * x * Real.exp (2 * x) := by
  unfold Fcent
  have h0 := besselI0_le_exp hx
  have h1 := besselI1_le_exp hx
  nlinarith

/-- Stirling-type upper bound: `r! ≤ e √r (r/e)^r` for `r ≥ 1`. -/
theorem factorial_le_stirling {r : ℕ} (hr : 1 ≤ r) :
    (r.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt r * ((r : ℝ) / Real.exp 1) ^ r := by
  have h := Stirling.stirlingSeq'_antitone (Nat.zero_le (r - 1))
  simp only [Function.comp, Nat.succ_eq_add_one, zero_add, show r - 1 + 1 = r by omega,
    Stirling.stirlingSeq_one] at h
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hpos : 0 < Real.sqrt (2 * r) * ((r : ℝ) / Real.exp 1) ^ r := by positivity
  unfold Stirling.stirlingSeq at h
  rw [div_le_iff₀ hpos] at h
  calc (r.factorial : ℝ) ≤ Real.exp 1 / Real.sqrt 2 * (Real.sqrt (2 * r) * ((r : ℝ) / Real.exp 1) ^ r) := h
    _ = Real.exp 1 * Real.sqrt r * ((r : ℝ) / Real.exp 1) ^ r := by
      rw [Real.sqrt_mul (by norm_num)]
      have : Real.sqrt 2 ≠ 0 := by positivity
      field_simp

/-- `F(x) ≥ 2 e^{2x-4}` for `x ≥ 1`, from the single term `r = ⌊x⌋` of `I_0(2x)`. -/
theorem Fcent_ge {x : ℝ} (hx : 1 ≤ x) : 2 * Real.exp (2 * x - 4) ≤ Fcent x := by
  set r := ⌊x⌋₊ with hr_def
  have hr1 : 1 ≤ r := Nat.le_floor (by simpa using hx)
  have hrx : (r : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxr : x < r + 1 := Nat.lt_floor_add_one x
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hsqrt : Real.sqrt r ≤ r := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith [(show (1 : ℝ) ≤ r by exact_mod_cast hr1)]
  -- the single term
  have hterm : b0 x r ≤ besselI0 (2 * x) := by
    rw [besselI0_two_mul]
    exact (summable_b0 x).le_tsum r (fun j _ => b0_nonneg x j)
  have hfac := factorial_le_stirling hr1
  have he : Real.exp 1 ^ r = Real.exp r := Real.exp_one_pow r
  -- `r!² ≤ e² r (r/e)^{2r}`
  have hfac2 : (r.factorial : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 * r * ((r : ℝ) ^ r / Real.exp r) ^ 2 := by
    have h0 : (0 : ℝ) ≤ r.factorial := by positivity
    have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
    calc (r.factorial : ℝ) ^ 2 ≤ (Real.exp 1 * Real.sqrt r * ((r : ℝ) / Real.exp 1) ^ r) ^ 2 :=
          pow_le_pow_left₀ h0 hfac 2
      _ = Real.exp 1 ^ 2 * r * ((r : ℝ) ^ r / Real.exp r) ^ 2 := by
          rw [div_pow, he, mul_pow, mul_pow, hs]
  have hb0 : Real.exp (2 * r - 2) / r ≤ b0 x r := by
    unfold b0
    have hxp : (r : ℝ) ^ (2 * r) ≤ x ^ (2 * r) := pow_le_pow_left₀ hr0.le hrx _
    have hf2 : (0 : ℝ) < (r.factorial : ℝ) ^ 2 := by positivity
    rw [div_le_div_iff₀ hr0 hf2]
    have key : Real.exp (2 * r - 2) * (Real.exp 1 ^ 2 * r * ((r : ℝ) ^ r / Real.exp r) ^ 2) =
        (r : ℝ) ^ (2 * r) * r := by
      have e1 : Real.exp 1 ^ 2 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
      have e2 : Real.exp r ^ 2 = Real.exp (2 * r) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      have e3 : Real.exp (2 * r - 2) * Real.exp 2 = Real.exp (2 * r) := by
        rw [← Real.exp_add]; ring_nf
      have hne : Real.exp (2 * (r : ℝ)) ≠ 0 := Real.exp_ne_zero _
      rw [div_pow, e1, e2, ← pow_mul]
      rw [show Real.exp (2 * r - 2) * (Real.exp 2 * r * ((r : ℝ) ^ (r * 2) / Real.exp (2 * r))) =
          r * (r : ℝ) ^ (r * 2) * ((Real.exp (2 * r - 2) * Real.exp 2) / Real.exp (2 * r)) by ring,
        e3, div_self hne]
      ring
    calc Real.exp (2 * r - 2) * (r.factorial : ℝ) ^ 2
        ≤ Real.exp (2 * r - 2) * (Real.exp 1 ^ 2 * r * ((r : ℝ) ^ r / Real.exp r) ^ 2) :=
          mul_le_mul_of_nonneg_left hfac2 (Real.exp_pos _).le
      _ = (r : ℝ) ^ (2 * r) * r := key
      _ ≤ x ^ (2 * r) * r := mul_le_mul_of_nonneg_right hxp hr0.le
  have hI1 := besselI1_nonneg (show (0 : ℝ) ≤ x by linarith)
  have hexp : Real.exp (2 * x - 4) ≤ Real.exp (2 * r - 2) := Real.exp_le_exp.2 (by linarith)
  have hx0 : 0 < x := by linarith
  -- `2x e^{2r-2}/r ≥ 2 e^{2r-2}`
  have h3 : 2 * Real.exp (2 * r - 2) ≤ 2 * x * (Real.exp (2 * r - 2) / r) := by
    rw [mul_div_assoc']
    rw [le_div_iff₀ hr0]
    have := Real.exp_pos (2 * (r : ℝ) - 2)
    nlinarith
  unfold Fcent
  nlinarith [mul_le_mul_of_nonneg_left hb0 (show (0 : ℝ) ≤ 2 * x by linarith),
    mul_le_mul_of_nonneg_left hterm (show (0 : ℝ) ≤ 2 * x by linarith),
    mul_nonneg (show (0 : ℝ) ≤ 2 * x by linarith) hI1]

/-! ### The sandwich for `S_N` from eq. `eq:uniformbessel` -/

theorem Fcent_pos {x : ℝ} (hx : 0 < x) : 0 < Fcent x := by
  rw [Fcent_eq]; have := Geta_pos zero_le_one hx; linarith

theorem SN_le_F (N : ℕ) (hN : 2 ≤ N) {u : ℝ} (hu : 0 < u) :
    SN N u ≤ Fcent ((N : ℝ) / 2 * u) / ((N : ℝ) / 2) := by
  have hN' : (0 : ℝ) < (N : ℝ) / 2 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hx : 0 < (N : ℝ) / 2 * u := by positivity
  obtain ⟨h1, _⟩ := uniform_bessel_central N hN hx
  rw [show (N : ℝ) / 2 * u / ((N : ℝ) / 2) = u by field_simp] at h1
  have hF := Fcent_pos hx
  rw [sub_nonneg, div_le_one hF] at h1
  rw [le_div_iff₀ hN']
  linarith

theorem F_le_SN (N : ℕ) (hN : 2 ≤ N) {u : ℝ} (hu : 0 < u) :
    Fcent ((N : ℝ) / 2 * u) *
        (1 - (N : ℝ) / 2 * u * ((N : ℝ) / 2 * u + 1) / ((N : ℝ) / 2)) / ((N : ℝ) / 2) ≤
      SN N u := by
  have hN' : (0 : ℝ) < (N : ℝ) / 2 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hx : 0 < (N : ℝ) / 2 * u := by positivity
  obtain ⟨_, h2⟩ := uniform_bessel_central N hN hx
  rw [show (N : ℝ) / 2 * u / ((N : ℝ) / 2) = u by field_simp] at h2
  have hF := Fcent_pos hx
  rw [div_le_iff₀ hN']
  have : 1 - (N : ℝ) / 2 * u * ((N : ℝ) / 2 * u + 1) / ((N : ℝ) / 2) ≤
      (N : ℝ) / 2 * SN N u / Fcent ((N : ℝ) / 2 * u) := by linarith
  rw [le_div_iff₀ hF] at this
  linarith

/-! ### Limits in `t = log N` -/

theorem tendsto_log_nat : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_pow_mul_exp_neg_mul (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => t ^ n * Real.exp (-(c * t))) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (tendsto_id.const_mul_atTop hc)
  have h2 := h.const_mul ((c ^ n)⁻¹)
  rw [mul_zero] at h2
  refine h2.congr (fun t => ?_)
  simp only [Function.comp, id]
  rw [mul_pow]
  field_simp

theorem exp_log_nat {N : ℕ} (hN : 1 ≤ N) : Real.exp (Real.log N) = N :=
  Real.exp_log (by exact_mod_cast hN)

/-- Lower half of Theorem `thm:root` (c): for `0 < ε < 1`, eventually
`(1-ε) log N / N < u_N`. -/
theorem uN_lower {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ N : ℕ in atTop, (1 - ε) * Real.log N / N < uN N := by
  have hlim := (tendsto_pow_mul_exp_neg_mul 1 hε0).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  filter_upwards [tendsto_log_nat.eventually hlim, tendsto_log_nat.eventually (eventually_gt_atTop 0),
    eventually_ge_atTop 2] with N hN1 htpos hN2
  set t := Real.log N
  simp only [pow_one] at hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNt : (N : ℝ) = Real.exp t := (exp_log_nat (by omega)).symm
  set u := (1 - ε) * t / N with hu_def
  have h1e : 0 < 1 - ε := by linarith
  have hu : 0 < u := by rw [hu_def]; positivity
  have hx : (N : ℝ) / 2 * u = (1 - ε) * t / 2 := by rw [hu_def]; field_simp
  have hS := SN_le_F N hN2 hu
  rw [hx] at hS
  have hFle := Fcent_le (show 0 ≤ (1 - ε) * t / 2 by positivity)
  have hlt : SN N u < 1 := by
    calc SN N u ≤ Fcent ((1 - ε) * t / 2) / ((N : ℝ) / 2) := hS
      _ ≤ 4 * ((1 - ε) * t / 2) * Real.exp (2 * ((1 - ε) * t / 2)) / ((N : ℝ) / 2) :=
          div_le_div_of_nonneg_right hFle (by positivity)
      _ = 4 * (1 - ε) * (t * Real.exp (-(ε * t))) := by
          rw [hNt]
          have : Real.exp (2 * ((1 - ε) * t / 2)) = Real.exp t * Real.exp (-(ε * t)) := by
            rw [← Real.exp_add]; ring_nf
          rw [this]
          field_simp
      _ < 1 := by
          have h1 : 4 * (1 - ε) * (t * Real.exp (-(ε * t))) ≤ 4 * (t * Real.exp (-(ε * t))) := by
            have : 0 ≤ t * Real.exp (-(ε * t)) := by positivity
            nlinarith
          linarith
  exact (Sab_lt_one_iff (by omega) (by omega) hu.le).1 hlt

/-- Upper half of Theorem `thm:root` (c): for `ε > 0`, eventually `u_N < (1+ε) log N / N`. -/
theorem uN_upper {ε : ℝ} (hε0 : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, uN N < (1 + ε) * Real.log N / N := by
  -- `δ(t) → 0`
  have hδ : Tendsto (fun t : ℝ => (1 + ε) ^ 2 / 2 * (t ^ 2 * Real.exp (-(1 * t))) +
      (1 + ε) * (t ^ 1 * Real.exp (-(1 * t)))) atTop (𝓝 0) := by
    have h := ((tendsto_pow_mul_exp_neg_mul 2 one_pos).const_mul ((1 + ε) ^ 2 / 2)).add
      ((tendsto_pow_mul_exp_neg_mul 1 one_pos).const_mul (1 + ε))
    simpa using h
  have hev1 := hδ.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hev2 : ∀ᶠ t : ℝ in atTop, Real.exp 4 < Real.exp (ε * t) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hε0)).eventually
      (eventually_gt_atTop _)
  have hev3 : ∀ᶠ t : ℝ in atTop, 2 / (1 + ε) ≤ t := eventually_ge_atTop _
  filter_upwards [tendsto_log_nat.eventually hev1, tendsto_log_nat.eventually hev2,
    tendsto_log_nat.eventually hev3, eventually_ge_atTop 2] with N h1 h2 h3 hN2
  set t := Real.log N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNt : (N : ℝ) = Real.exp t := (exp_log_nat (by omega)).symm
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) h3
  set u := (1 + ε) * t / N with hu_def
  have hu : 0 < u := by rw [hu_def]; positivity
  set x := (1 + ε) * t / 2 with hx_def
  have hx : (N : ℝ) / 2 * u = x := by rw [hu_def, hx_def]; field_simp
  have hx1 : 1 ≤ x := by
    rw [hx_def]
    rw [div_le_iff₀ (by positivity)] at h3
    linarith
  have hS := F_le_SN N hN2 hu
  rw [hx] at hS
  -- `δ = x(x+1)/(N/2) ≤ 1/2`
  have hδle : x * (x + 1) / ((N : ℝ) / 2) ≤ 1 / 2 := by
    rw [hNt]
    have e : x * (x + 1) / (Real.exp t / 2) =
        (1 + ε) ^ 2 / 2 * (t ^ 2 * Real.exp (-(1 * t))) + (1 + ε) * (t ^ 1 * Real.exp (-(1 * t))) := by
      rw [hx_def, one_mul, Real.exp_neg]
      field_simp
    rw [e]; exact h1.le
  have hFge := Fcent_ge hx1
  have hgt : 1 < SN N u := by
    calc (1 : ℝ) < 2 * Real.exp (2 * x - 4) * (1 / 2) / ((N : ℝ) / 2) := by
          rw [hNt, hx_def]
          have e : 2 * Real.exp (2 * ((1 + ε) * t / 2) - 4) * (1 / 2) / (Real.exp t / 2) =
              2 * Real.exp (ε * t - 4) := by
            rw [show 2 * ((1 + ε) * t / 2) - 4 = t + (ε * t - 4) by ring, Real.exp_add]
            field_simp
          rw [e]
          have : 1 < Real.exp (ε * t - 4) := by
            rw [Real.exp_sub, one_lt_div (Real.exp_pos _)]; exact h2
          linarith
      _ ≤ Fcent x * (1 - x * (x + 1) / ((N : ℝ) / 2)) / ((N : ℝ) / 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul hFge (by linarith) (by norm_num) (Fcent_pos (by linarith)).le
      _ ≤ SN N u := hS
  exact (one_lt_Sab_iff (by omega) (by omega) hu.le).1 hgt

/-- Theorem `thm:root` (c), first form: `N u_N / log N → 1`. -/
theorem tendsto_N_uN_div_log :
    Tendsto (fun N : ℕ => N * uN N / Real.log N) atTop (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    by_cases ha0 : a ≤ 0
    · filter_upwards [eventually_ge_atTop 2] with N hN
      have : 0 < (N : ℝ) * uN N / Real.log N := by
        have h1 := uab_pos (a := N / 2) (b := N - N / 2) (by omega) (by omega)
        have h2 : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
        have h3 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
        unfold uN; positivity
      linarith
    · push Not at ha0
      filter_upwards [uN_lower (ε := 1 - a) (by linarith) (by linarith), eventually_ge_atTop 2]
        with N h hN
      have h2 : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
      have h3 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      rw [lt_div_iff₀ h2]
      rw [div_lt_iff₀ h3] at h
      ring_nf at h ⊢
      linarith
  · intro b hb
    filter_upwards [uN_upper (ε := b - 1) (by linarith), eventually_ge_atTop 2] with N h hN
    have h2 : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have h3 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [div_lt_iff₀ h2]
    rw [lt_div_iff₀ h3] at h
    ring_nf at h ⊢
    linarith

/-- `u_N → 0`. -/
theorem tendsto_uN : Tendsto uN atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N / N) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    refine h.congr (fun N => ?_)
    simp
  have hup : Tendsto (fun N : ℕ => 2 * (Real.log N / N)) atTop (𝓝 0) := by
    simpa using hlog.const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact (uab_pos (a := N / 2) (b := N - N / 2) (by omega) (by omega)).le
  · filter_upwards [uN_upper (ε := 1) one_pos] with N h
    rw [mul_div_assoc'] ; norm_num at h ⊢; linarith

/-- Theorem `thm:root` (c): `p_N → 1` and `1 - p_N ~ (log N)/N`, i.e.
`N (1 - p_N) / log N → 1`. -/
theorem thm_root_c :
    Tendsto pN atTop (𝓝 1) ∧
      Tendsto (fun N : ℕ => N * (1 - pN N) / Real.log N) atTop (𝓝 1) := by
  have hu := tendsto_uN
  have h1u : Tendsto (fun N => 1 + uN N) atTop (𝓝 1) := by simpa using hu.const_add 1
  constructor
  · have := h1u.inv₀ one_ne_zero
    simp only [inv_one] at this
    refine this.congr (fun N => ?_)
    simp [pN, uN, pab, one_div]
  · have := tendsto_N_uN_div_log.div h1u one_ne_zero
    rw [div_one] at this
    refine this.congr (fun N => ?_)
    have hnn : 0 ≤ uN N := by
      unfold uN uab; split_ifs with h
      · exact (Classical.choose_spec (Sab_exists_root h.1 h.2)).1.le
      · exact le_rfl
    have hp : 1 - pN N = uN N / (1 + uN N) := by
      show 1 - 1 / (1 + uN N) = _
      have : 1 + uN N ≠ 0 := by linarith
      field_simp
      ring
    simp only [Pi.div_apply]
    rw [hp]
    have : 1 + uN N ≠ 0 := by linarith
    field_simp

/-- Theorem `thm:bessel`, `0 ≤ u_N - u_B = O((log N)²/N²)` in explicit form: with `u_B = x_B/h`,
`h = N/2`, `F(x_B) = h`, eventually `0 ≤ u_N - u_B ≤ 8 (log N)²/N²`. -/
theorem uN_sub_uB :
    ∀ᶠ N : ℕ in atTop,
      0 ≤ uN N - Groot 1 ((N : ℝ) / 2 / 2) / ((N : ℝ) / 2) ∧
        uN N - Groot 1 ((N : ℝ) / 2 / 2) / ((N : ℝ) / 2) ≤ 8 * Real.log N ^ 2 / (N : ℝ) ^ 2 := by
  have hsq : Tendsto (fun N : ℕ => Real.log N ^ 2 / N) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    refine h.congr (fun N => ?_)
    simp
  filter_upwards [uN_upper (ε := 1) one_pos, hsq.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num)),
    tendsto_log_nat.eventually (eventually_ge_atTop 1), eventually_ge_atTop 2] with N hup hlog2 hlog1 hN
  set L := Real.log N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set h : ℝ := (N : ℝ) / 2 with hh_def
  have hh : 0 < h := by positivity
  have hu := uab_pos (a := N / 2) (b := N - N / 2) (by omega) (by omega)
  have hu0 : 0 < uN N := hu
  obtain ⟨_, hle, hbound⟩ := central_root_bound N hN

  set xN := h * uN N with hxN
  set xB := Groot 1 (h / 2)
  -- `x_N ≤ L`
  have hxL : xN ≤ L := by
    rw [hxN, hh_def]
    have : uN N < 2 * L / N := by simpa [one_add_one_eq_two] using hup
    rw [lt_div_iff₀ hNpos] at this
    nlinarith
  have hx0 : 0 < xN := by positivity
  set δ := xN * (xN + 1) / h with hδ_def
  have hδle : δ ≤ 4 * L ^ 2 / N := by
    have h1 : xN * (xN + 1) ≤ 2 * L ^ 2 := by
      have := mul_le_mul hxL (show xN + 1 ≤ 2 * L by linarith) (by linarith) (by linarith)
      nlinarith
    rw [hδ_def, hh_def, div_le_div_iff₀ (by positivity) hNpos]
    nlinarith
  have hδhalf : δ ≤ 1 / 2 := by
    have : 4 * L ^ 2 / N ≤ 1 / 2 := by
      have := hlog2.le
      rw [div_le_iff₀ hNpos] at this ⊢
      nlinarith
    linarith
  have hδ0 : 0 ≤ δ := by positivity
  have hb := hbound (by linarith)
  -- `-(1/2) log(1-δ) ≤ δ`
  have hlogb : -(1 / 2) * Real.log (1 - δ) ≤ δ := by
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 - δ by linarith)
    have h2 : (1 - δ)⁻¹ ≤ 1 + 2 * δ := by
      rw [inv_le_iff_one_le_mul₀ (by linarith)]
      nlinarith
    linarith
  have hdiff : xN - xB ≤ δ := hb.trans hlogb
  constructor
  · have : xB / h ≤ uN N := by rw [div_le_iff₀ hh]; linarith
    linarith
  · have e : uN N - xB / h = (xN - xB) / h := by rw [hxN]; field_simp
    rw [e, div_le_iff₀ hh]
    calc xN - xB ≤ δ := hdiff
      _ ≤ 4 * L ^ 2 / N := hδle
      _ = 8 * L ^ 2 / (N : ℝ) ^ 2 * h := by rw [hh_def]; field_simp; ring

end Kagey131
