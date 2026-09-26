import PaperA.Asymptotics
import PaperA.Periodic

/-!
# Paper A: leading-order all-bin crossings and periodic ordering

* eq. `eq:allbin-leading`, uniformly in the bin: for every `0 < ε < 1` there is `a₀` such that
  for all `a₀ ≤ a ≤ b`, `(1-ε) log a < 2√(ab) u_{a,b} < (1+ε) log a`, and the same with
  `1 - p_{a,b}` in place of `u_{a,b}`. This is the leading term of Theorem
  `thm:allbin-expansion`; the finer terms need the large-argument Bessel expansion, which is
  not formalized.
* The periodic ratios: `R^P_{N,k}` increases strictly toward the middle, is symmetric, and the
  adjacent periodic threshold is `J = (log N)/4` (Section `sec:periodicwindow`, where the
  coupling is `J`; it is `K` in the Lean statement).

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset Filter Topology

/-- The single-term lower bound `x^{2r}/(r!)² ≥ e^{2r-2}/r` at `r = ⌊x⌋`, `x ≥ 1`. -/
theorem b0_floor_ge {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (2 * (⌊x⌋₊ : ℝ) - 2) / (⌊x⌋₊ : ℝ) ≤ b0 x ⌊x⌋₊ := by
  set r := ⌊x⌋₊ with hr_def
  have hr1 : 1 ≤ r := Nat.le_floor (by simpa using hx)
  have hrx : (r : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hfac := factorial_le_stirling hr1
  have he : Real.exp 1 ^ r = Real.exp r := Real.exp_one_pow r
  have hfac2 : (r.factorial : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 * r * ((r : ℝ) ^ r / Real.exp r) ^ 2 := by
    have h0 : (0 : ℝ) ≤ r.factorial := by positivity
    have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
    calc (r.factorial : ℝ) ^ 2 ≤ (Real.exp 1 * Real.sqrt r * ((r : ℝ) / Real.exp 1) ^ r) ^ 2 :=
          pow_le_pow_left₀ h0 hfac 2
      _ = Real.exp 1 ^ 2 * r * ((r : ℝ) ^ r / Real.exp r) ^ 2 := by
          rw [div_pow, he, mul_pow, mul_pow, hs]
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

/-- `x I_1(2x) ≥ e^{2x-4}/2` for `x ≥ 1`. -/
theorem xI1_ge {x : ℝ} (hx : 1 ≤ x) : Real.exp (2 * x - 4) / 2 ≤ x * besselI1 (2 * x) := by
  set r := ⌊x⌋₊ with hr_def
  have hr1 : 1 ≤ r := Nat.le_floor (by simpa using hx)
  have hrx : (r : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxr : x < r + 1 := Nat.lt_floor_add_one x
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hb0 := b0_floor_ge hx
  rw [← hr_def] at hb0
  have hterm : b1 x r ≤ besselI1 (2 * x) := by
    rw [besselI1_two_mul]
    exact (summable_b1 x).le_tsum r (fun j _ => b1_nonneg (by linarith) j)
  have hb1 : b1 x r = x * b0 x r / (r + 1) := by
    unfold b0 b1
    rw [Nat.factorial_succ]
    push_cast
    have hf : (0 : ℝ) < r.factorial := by positivity
    field_simp
    ring
  have hexp : Real.exp (2 * x - 4) ≤ Real.exp (2 * r - 2) := Real.exp_le_exp.2 (by linarith)
  have hE := Real.exp_pos (2 * (r : ℝ) - 2)
  -- `x b1 = x² b0/(r+1) ≥ x² e^{2r-2}/(r(r+1)) ≥ e^{2r-2}/2`
  have h1 : Real.exp (2 * r - 2) / 2 ≤ x * b1 x r := by
    rw [hb1]
    have hb0' : Real.exp (2 * r - 2) ≤ b0 x r * r := by
      rwa [div_le_iff₀ hr0] at hb0
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hx0 : 0 < x := by linarith
    rw [show x * (x * b0 x r / (r + 1)) * 2 = 2 * x ^ 2 * b0 x r / (r + 1) by ring,
      le_div_iff₀ (by linarith)]
    have hb00 : 0 ≤ b0 x r := b0_nonneg x r
    nlinarith [mul_le_mul_of_nonneg_left hrx hb00]
  have hx0 : 0 ≤ x := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hterm hx0]

/-- `G_η(x) ≤ 2x e^{2x}` for `0 ≤ η ≤ 1`, `x ≥ 0`. -/
theorem Geta_le {η x : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hx : 0 ≤ x) :
    Geta η x ≤ 2 * x * Real.exp (2 * x) := by
  unfold Geta
  have h0 := besselI0_le_exp hx
  have h1 := besselI1_le_exp hx
  have hI0 : 0 ≤ besselI0 (2 * x) := by linarith [one_le_besselI0 x]
  have : η * (x * besselI0 (2 * x)) ≤ x * Real.exp (2 * x) := by
    calc η * (x * besselI0 (2 * x)) ≤ 1 * (x * besselI0 (2 * x)) :=
          mul_le_mul_of_nonneg_right hη1 (by positivity)
      _ ≤ x * Real.exp (2 * x) := by rw [one_mul]; exact mul_le_mul_of_nonneg_left h0 hx
  nlinarith [mul_le_mul_of_nonneg_left h1 hx]

/-- eq. `eq:allbin-leading`, uniformly over `b ≥ a`: for `0 < ε < 1` there is `a₀` with
`(1-ε) log a < 2√(ab) u_{a,b} < (1+ε) log a` whenever `a₀ ≤ a ≤ b`. -/
theorem allbin_leading {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ a₀ : ℕ, ∀ a b : ℕ, a₀ ≤ a → a ≤ b →
      (1 - ε) * Real.log a < 2 * Real.sqrt ((a : ℝ) * b) * uab a b ∧
        2 * Real.sqrt ((a : ℝ) * b) * uab a b < (1 + ε) * Real.log a := by
  -- conditions in `t = log a`
  have hL := (tendsto_pow_mul_exp_neg_mul 1 hε0).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hδ : Tendsto (fun t : ℝ => (1 + ε) ^ 2 / 4 * (t ^ 2 * Real.exp (-(1 * t))) +
      (1 + ε) / 2 * (t ^ 1 * Real.exp (-(1 * t)))) atTop (𝓝 0) := by
    have h := ((tendsto_pow_mul_exp_neg_mul 2 one_pos).const_mul ((1 + ε) ^ 2 / 4)).add
      ((tendsto_pow_mul_exp_neg_mul 1 one_pos).const_mul ((1 + ε) / 2))
    simpa using h
  have hU1 := hδ.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hU2 : ∀ᶠ t : ℝ in atTop, 4 * Real.exp 4 < Real.exp (ε * t) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hε0)).eventually
      (eventually_gt_atTop _)
  have hU3 : ∀ᶠ t : ℝ in atTop, 2 / (1 - ε) ≤ t := eventually_ge_atTop _
  have hall := tendsto_log_nat.eventually (((hL.and hU1).and hU2).and hU3)
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.1 (hall.and (eventually_ge_atTop 2))
  refine ⟨a₀, fun a b ha hab => ?_⟩
  obtain ⟨⟨⟨⟨hLt, hU1t⟩, hU2t⟩, hU3t⟩, ha2⟩ := ha₀ a ha
  set t := Real.log a with ht_def
  have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hat : (a : ℝ) = Real.exp t := (exp_log_nat (by omega)).symm
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  set s := Real.sqrt ((a : ℝ) * b) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = (a : ℝ) * b := Real.sq_sqrt (by positivity)
  have hsa : (a : ℝ) ≤ s := by
    rw [hs_def]; apply Real.le_sqrt_of_sq_le; nlinarith
  set A := (a : ℝ) * b / (a + b) with hA_def
  have hA1 : (a : ℝ) / 2 ≤ A := by
    rw [hA_def, le_div_iff₀ (by positivity)]; nlinarith
  have hA2 : A ≤ a := by
    rw [hA_def, div_le_iff₀ (by positivity)]; nlinarith
  have hA0 : 0 < A := by positivity
  set η := 2 * s / ((a : ℝ) + b)
  have hη0 : 0 ≤ η := (eta_le_one a b ha1 hb1).1
  have hη1 : η ≤ 1 := (eta_le_one a b ha1 hb1).2
  have ht2 : 2 ≤ t := by
    have : (0 : ℝ) < 1 - ε := by linarith
    have h2 : 2 ≤ 2 / (1 - ε) := by rw [le_div_iff₀ this]; linarith
    linarith
  -- relation between `S`, `T` and `G`
  have hT : ∀ u : ℝ, Tab a b u = Geta η (s * u) / A := fun u => Tab_eq_Geta a b ha1 hb1 u
  have hbound := fun u => allbin_bound_eq a b ha1 hb1 u
  have hbessel := fun u (hu : 0 < u) => allbin_bessel a b ha1 hb1 hu
  clear_value η A s t
  constructor
  · -- lower bound: `S < 1` at `x = (1-ε) t/2`
    set u := (1 - ε) * t / (2 * s) with hu_def
    have h1e : 0 < 1 - ε := by linarith
    have hu : 0 < u := by rw [hu_def]; positivity
    have hsu : s * u = (1 - ε) * t / 2 := by rw [hu_def]; field_simp
    obtain ⟨hlow, _⟩ := hbessel u hu
    have ht0 : (0 : ℝ) < t := by linarith only [ht2]
    have hxpos : (0 : ℝ) < (1 - ε) * t / 2 := by
      have := mul_pos h1e ht0; linarith only [this]
    have hTpos : 0 < Tab a b u := by
      rw [hT, hsu]; exact div_pos (Geta_pos hη0 hxpos) hA0
    have hST : Sab a b u ≤ Tab a b u := by
      rw [sub_nonneg, div_le_one hTpos] at hlow; exact hlow
    have hx0 : (0 : ℝ) ≤ (1 - ε) * t / 2 := hxpos.le
    have hG := Geta_le hη0 hη1 hx0
    have hlt : Sab a b u < 1 := by
      calc Sab a b u ≤ Tab a b u := hST
        _ = Geta η ((1 - ε) * t / 2) / A := by rw [hT, hsu]
        _ ≤ 2 * ((1 - ε) * t / 2) * Real.exp (2 * ((1 - ε) * t / 2)) / (a / 2) := by
            apply div_le_div₀ (by positivity) hG (by positivity) hA1
        _ = 2 * (1 - ε) * (t * Real.exp (-(ε * t))) := by
            rw [hat]
            have : Real.exp (2 * ((1 - ε) * t / 2)) = Real.exp t * Real.exp (-(ε * t)) := by
              rw [← Real.exp_add]; ring_nf
            rw [this]; field_simp
        _ < 1 := by
            have hy : 0 ≤ t * Real.exp (-(ε * t)) := by positivity
            simp only [pow_one] at hLt
            have := mul_le_mul_of_nonneg_right (show 1 - ε ≤ 1 by linarith only [hε0]) hy
            linarith only [this, hLt]
    have hlt' : (1 - ε) * t / (2 * s) < uab a b := (Sab_lt_one_iff ha1 hb1 hu.le).1 hlt
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * s)).1 hlt'
    linarith only [this, show uab a b * (2 * s) = 2 * s * uab a b by ring]
  · -- upper bound: `S > 1` at `x = (1+ε) t/2`
    set u := (1 + ε) * t / (2 * s) with hu_def
    have hu : 0 < u := by rw [hu_def]; positivity
    set x := (1 + ε) * t / 2 with hx_def
    have hsu : s * u = x := by rw [hu_def, hx_def]; field_simp
    have hx1 : 1 ≤ x := by
      rw [hx_def]
      have := mul_pos hε0 (show (0 : ℝ) < t by linarith only [ht2])
      linarith only [this, ht2]
    obtain ⟨_, hup⟩ := hbessel u hu
    have hδeq : (s * u) ^ 2 / (2 * A) + s * u / s = ((a : ℝ) + b) * u ^ 2 / 2 + u := by
      have := hbound u
      simp only [← hs_def, ← hA_def] at this
      exact this
    clear_value x u
    rw [← hδeq, hsu] at hup
    -- `δ ≤ x²/a + x/a ≤ 1/2`
    have hδ : x ^ 2 / (2 * A) + x / s ≤ 1 / 2 := by
      have h2A : (a : ℝ) ≤ 2 * A := by linarith only [hA1]
      have hx0 : 0 ≤ x := by linarith only [hx1]
      have h1 : x ^ 2 / (2 * A) ≤ x ^ 2 / a := div_le_div_of_nonneg_left (sq_nonneg x) hapos h2A
      have h2 : x / s ≤ x / a := div_le_div_of_nonneg_left hx0 hapos hsa
      have hainv : (a : ℝ)⁻¹ = Real.exp (-t) := by rw [Real.exp_neg, ← hat]
      have h3 : x ^ 2 / a + x / a =
          (1 + ε) ^ 2 / 4 * (t ^ 2 * Real.exp (-(1 * t))) + (1 + ε) / 2 * (t ^ 1 * Real.exp (-(1 * t))) := by
        calc x ^ 2 / a + x / a = (x ^ 2 + x) * (a : ℝ)⁻¹ := by ring
          _ = (x ^ 2 + x) * Real.exp (-t) := by rw [hainv]
          _ = _ := by rw [hx_def, one_mul]; ring
      linarith only [h1, h2, h3, hU1t]
    have hTpos : 0 < Tab a b u := by rw [hT, hsu]; exact div_pos (Geta_pos hη0 (by linarith)) hA0
    have hGx : Real.exp (2 * x - 4) / 2 ≤ Geta η x := by
      have := xI1_ge hx1
      unfold Geta
      have : 0 ≤ η * (x * besselI0 (2 * x)) := by
        have := one_le_besselI0 x
        have : 0 ≤ x := by linarith
        positivity
      linarith
    have hgt : 1 < Sab a b u := by
      have hS : (1 - (x ^ 2 / (2 * A) + x / s)) * Tab a b u ≤ Sab a b u := by
        have h' : 1 - (x ^ 2 / (2 * A) + x / s) ≤ Sab a b u / Tab a b u := by
          linarith only [hup]
        rwa [le_div_iff₀ hTpos] at h'
      calc (1 : ℝ) < (1 / 2) * (Real.exp (2 * x - 4) / 2 / a) := by
            rw [hat, hx_def]
            have e : 1 / 2 * (Real.exp (2 * ((1 + ε) * t / 2) - 4) / 2 / Real.exp t) =
                Real.exp (ε * t) / (4 * Real.exp 4) := by
              rw [show 2 * ((1 + ε) * t / 2) - 4 = t + ε * t - 4 by ring, Real.exp_sub,
                Real.exp_add]
              field_simp
              ring
            rw [e, one_lt_div (by positivity)]; exact hU2t
        _ ≤ (1 - (x ^ 2 / (2 * A) + x / s)) * (Geta η x / A) := by
            apply mul_le_mul (by linarith) _ (by positivity) (by linarith)
            apply div_le_div₀ (by linarith [Geta_pos hη0 (show 0 < x by linarith)]) hGx hA0 hA2
        _ = (1 - (x ^ 2 / (2 * A) + x / s)) * Tab a b u := by rw [hT, hsu]
        _ ≤ Sab a b u := hS
    have hgt' : uab a b < u := (one_lt_Sab_iff ha1 hb1 hu.le).1 hgt
    rw [hu_def] at hgt'
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * s)).1 hgt'
    linarith only [this, show uab a b * (2 * s) = 2 * s * uab a b by ring]

/-! ### Periodic ordering and the adjacent periodic threshold -/

/-- The periodic ratio is symmetric: `R^P_{N,k} = R^P_{N,N-k}`. -/
theorem perRatio_symm (N k : ℕ) (hk : k ≤ N) (u : ℝ) : perRatio N k u = perRatio N (N - k) u := by
  rw [perRatio_shift, perRatio_shift, show N - (N - k) = k by omega, min_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  ring

/-- The periodic ratios increase strictly toward the middle (Section `sec:periodicwindow`): for `1 ≤ k` with
`k + 2 ≤ N - k` and `u > 0`, `R^P_{N,k}(u) < R^P_{N,k+1}(u)`. -/
theorem perRatio_lt_inward (N k : ℕ) (hk : 1 ≤ k) (hkN : k + 2 ≤ N - k) {u : ℝ} (hu : 0 < u) :
    perRatio N k u < perRatio N (k + 1) u := by
  rw [perRatio_shift, perRatio_shift]
  have ext : ∀ j, 1 ≤ j → j + 1 ≤ N → ∑ t ∈ range (min j (N - j)),
      (N : ℝ) / (t + 1) * (Nat.choose (j - 1) t : ℝ) * (Nat.choose (N - j - 1) t : ℝ) *
        u ^ (2 * t + 2) = ∑ t ∈ range N,
      (N : ℝ) / (t + 1) * (Nat.choose (j - 1) t : ℝ) * (Nat.choose (N - j - 1) t : ℝ) *
        u ^ (2 * t + 2) := by
    intro j hj hjN
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) (fun t _ ht => ?_)
    simp only [Finset.mem_range, not_lt] at ht
    rcases le_total j (N - j) with h | h
    · rw [min_eq_left h] at ht
      rw [Nat.choose_eq_zero_of_lt (show j - 1 < t by omega)]; simp
    · rw [min_eq_right h] at ht
      rw [Nat.choose_eq_zero_of_lt (show N - j - 1 < t by omega)]; simp
  rw [ext k hk (by omega), ext (k + 1) (by omega) (by omega)]
  simp only [show k + 1 - 1 = k by omega, show N - (k + 1) - 1 = N - k - 2 by omega]
  apply Finset.sum_lt_sum
  · intro t _
    have h := choose_mul_le_inward k (N - k) t (by omega)
    have h' : ((Nat.choose (k - 1) t : ℝ) * (Nat.choose (N - k - 1) t : ℝ)) ≤
        (Nat.choose k t : ℝ) * (Nat.choose (N - k - 2) t : ℝ) := by exact_mod_cast h
    have hc : 0 ≤ (N : ℝ) / (t + 1) := by positivity
    have hp : 0 ≤ u ^ (2 * t + 2) := by positivity
    calc (N : ℝ) / (t + 1) * (Nat.choose (k - 1) t : ℝ) * (Nat.choose (N - k - 1) t : ℝ) *
          u ^ (2 * t + 2)
        = (N : ℝ) / (t + 1) * ((Nat.choose (k - 1) t : ℝ) * (Nat.choose (N - k - 1) t : ℝ)) *
          u ^ (2 * t + 2) := by ring
      _ ≤ (N : ℝ) / (t + 1) * ((Nat.choose k t : ℝ) *
          (Nat.choose (N - k - 2) t : ℝ)) * u ^ (2 * t + 2) := by gcongr
      _ = _ := by ring
  · refine ⟨1, Finset.mem_range.2 (by omega), ?_⟩
    simp only [Nat.choose_one_right]
    have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have h1 : ((k - 1 : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) < (k : ℝ) * ((N - k - 2 : ℕ) : ℝ) := by
      have e1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk]; simp
      have e2 : ((N - k - 1 : ℕ) : ℝ) = ((N - k - 2 : ℕ) : ℝ) + 1 := by
        rw [show N - k - 1 = (N - k - 2) + 1 by omega]; push_cast; ring
      have e3 : ((k : ℕ) : ℝ) ≤ ((N - k - 2 : ℕ) : ℝ) := by
        have : k ≤ N - k - 2 := by omega
        exact_mod_cast this
      rw [e1, e2]; nlinarith
    have hpos : 0 < (N : ℝ) / ((1 : ℕ) + 1) * u ^ (2 * 1 + 2) := by positivity
    calc (N : ℝ) / ((1 : ℕ) + 1) * ((k - 1 : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ) * u ^ (2 * 1 + 2)
        = (N : ℝ) / ((1 : ℕ) + 1) * u ^ (2 * 1 + 2) * (((k - 1 : ℕ) : ℝ) * ((N - k - 1 : ℕ) : ℝ)) := by
          ring
      _ < (N : ℝ) / ((1 : ℕ) + 1) * u ^ (2 * 1 + 2) * ((k : ℝ) * ((N - k - 2 : ℕ) : ℝ)) :=
          mul_lt_mul_of_pos_left h1 hpos
      _ = _ := by ring

/-- The adjacent periodic threshold: with `u = e^{-2K}`, `R^P_{N,1}(u) = 1` iff
`K = (log N)/4`. -/
theorem periodic_adjacent_threshold (N : ℕ) (hN : 2 ≤ N) (K : ℝ) :
    perRatio N 1 (Real.exp (-2 * K)) = 1 ↔ K = Real.log N / 4 := by
  rw [perRatio_one N hN]
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have e : (N : ℝ) * Real.exp (-2 * K) ^ 2 = Real.exp (Real.log N + 2 * (-2 * K)) := by
    rw [Real.exp_add, Real.exp_log hN', ← Real.exp_nat_mul]; push_cast; ring_nf
  rw [e, Real.exp_eq_one_iff]
  constructor <;> intro h <;> linarith

/-- eq. `eq:allbin-leading` for the switching probability, uniformly over `b ≥ a`:
`(1-ε) log a < 2√(ab)(1 - p_{a,b}) < (1+ε) log a` for `a₀ ≤ a ≤ b`. -/
theorem allbin_leading_prob {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ a₀ : ℕ, ∀ a b : ℕ, a₀ ≤ a → a ≤ b →
      (1 - ε) * Real.log a < 2 * Real.sqrt ((a : ℝ) * b) * (1 - pab a b) ∧
        2 * Real.sqrt ((a : ℝ) * b) * (1 - pab a b) < (1 + ε) * Real.log a := by
  obtain ⟨a₁, ha₁⟩ := allbin_leading (ε := ε / 2) (by linarith) (by linarith)
  have hlog : Tendsto (fun a : ℕ => Real.log a / a) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    refine h.congr (fun N => ?_)
    simp
  obtain ⟨a₂, ha₂⟩ := eventually_atTop.1
    ((hlog.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by linarith))).and
      (tendsto_log_nat.eventually (eventually_ge_atTop 0)))
  refine ⟨max (max a₁ a₂) 2, fun a b ha hab => ?_⟩
  have ha1' : a₁ ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
  have ha2' : a₂ ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha
  have ha2 : 2 ≤ a := le_trans (le_max_right _ _) ha
  obtain ⟨hlow, hup⟩ := ha₁ a b ha1' hab
  obtain ⟨hla, hl0⟩ := ha₂ a ha2'
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hu := uab_pos ha1 hb1
  have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  set s := Real.sqrt ((a : ℝ) * b) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hsa : (a : ℝ) ≤ s := by rw [hs_def]; apply Real.le_sqrt_of_sq_le; nlinarith
  set u := uab a b
  set L := Real.log a
  have hp : 1 - pab a b = u / (1 + u) := by
    show 1 - 1 / (1 + u) = _
    field_simp; ring
  rw [hp]
  -- `u ≤ L/a`
  have huL : u ≤ L / a := by
    have h1 : 2 * s * u < (1 + ε / 2) * L := hup
    rw [le_div_iff₀ hapos]
    have h2 : (1 + ε / 2) * L ≤ 2 * L := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsa hu.le]
  have hu4 : u < ε / 4 := lt_of_le_of_lt huL hla
  constructor
  · -- `2su/(1+u) ≥ 2su(1-u) > (1-ε/2)(1-ε/4) L ≥ (1-ε) L`
    have h1 : 2 * s * u * (1 - u) ≤ 2 * s * (u / (1 + u)) := by
      rw [mul_div_assoc']
      rw [le_div_iff₀ (by linarith)]
      have : 0 ≤ 2 * s * u * u ^ 2 := by positivity
      nlinarith
    have h2 : (1 - ε / 2) * L * (1 - ε / 4) < 2 * s * u * (1 - u) := by
      have h3 : 1 - ε / 4 < 1 - u := by linarith
      have h4 : 0 < 1 - ε / 4 := by linarith
      calc (1 - ε / 2) * L * (1 - ε / 4) ≤ 2 * s * u * (1 - ε / 4) :=
            mul_le_mul_of_nonneg_right hlow.le h4.le
        _ < 2 * s * u * (1 - u) := mul_lt_mul_of_pos_left h3 (by positivity)
    have h5 : (1 - ε) * L ≤ (1 - ε / 2) * L * (1 - ε / 4) := by nlinarith
    linarith
  · have h1 : 2 * s * (u / (1 + u)) ≤ 2 * s * u := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h2 : (1 + ε / 2) * L ≤ (1 + ε) * L := by nlinarith
    linarith

end Kagey131
