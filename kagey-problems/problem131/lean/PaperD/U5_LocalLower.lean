import PaperD.U5_Tail

/-!
# Paper D, Proposition B.4 (`thm:B-local-lower`): the local lower bound

**Proposition B.4.** Assume (H). There is an absolute constant `C` such that for `2 ≤ m ≤ N/4`,
`f_N(m) ≥ x/(m(m+1)) (1 - e₁(m))` with `e₁(m) = C(x log(m+1)/m + ε log N + m e^{-m/9})`.

Lean:
* `lem_B4_explicit`: the bound with every error term explicit, for `N ≥ 64`, `0 ≤ ε ≤ 1`,
  `2 ≤ m`, `4m ≤ N`:
  `f_N(m) ≥ x/(m(m+1)) (1 - 2εH_{m+1} - xH_m/m - 2x(N-m-1)/(N(m+2)) - 8ε log N - R(m))`, with
  `R(m) = m(m+1)(1/(3(m-1)) + 16/(3(m-1)²)) e^{-(m-1)/9}` (`lateErr`).
* `thm_B_local_lower`: the paper's form with the explicit constant `C = 20`.

The hypotheses are weaker than (H): `ε ≤ 1/4` and `x ≥ 1` are not used, and `ε = 0` is allowed.

The proof is the paper's (Steps 1 to 5). Step 1 uses the paths of `Y` and `Z` (the realizations
of `U5_Chain`), Step 2 is Lemma B.2, Step 3 the two sums of Lemma 2.4 and Lemma B.3, Step 4 the
bound (`eq:B-subtail`).
-/

namespace Kagey131.PaperD

open Finset RRT

/-! ### Step 1: one value of `j`, pointwise in the paths -/

/-- A discrete intermediate value theorem: a function on `ℕ` that moves up by at most one per step
and goes from `≤ m` to `≥ m` takes the value `m`. -/
theorem discrete_ivt (f : ℕ → ℕ) {lo hi m : ℕ} (hlh : lo ≤ hi) (hlo : f lo ≤ m) (hhi : m ≤ f hi)
    (hstep : ∀ d, lo ≤ d → d < hi → f (d + 1) ≤ f d + 1) : ∃ d, lo ≤ d ∧ d ≤ hi ∧ f d = m := by
  induction hi, hlh using Nat.le_induction with
  | base => exact ⟨lo, le_rfl, le_rfl, by omega⟩
  | succ hi hlh ih =>
    by_cases h : m ≤ f hi
    · obtain ⟨d, h1, h2, h3⟩ := ih h (fun d h1 h2 => hstep d h1 (by omega))
      exact ⟨d, h1, by omega, h3⟩
    · have := hstep hi hlh (by omega)
      exact ⟨hi + 1, by omega, le_rfl, by omega⟩

/-- `β(m+k) ≥ β(m)(1 - qk)` from the one-step ratio bound. -/
theorem beta_shift_ge (β : ℕ → ℝ) (hβ0 : ∀ d, 0 ≤ β d) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {m K : ℕ} (hratio : ∀ k, k < K → β (m + k) * (1 - q) ≤ β (m + k + 1)) :
    ∀ k, k ≤ K → β m * (1 - q * k) ≤ β (m + k) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have hr := hratio k (by omega)
    by_cases hpos : 0 ≤ 1 - q * k
    · have h1 : β m * (1 - q * k) * (1 - q) ≤ β (m + k) * (1 - q) :=
        mul_le_mul_of_nonneg_right ih' (by linarith)
      have h2 : β m * (1 - q * ((k + 1 : ℕ) : ℝ)) ≤ β m * (1 - q * k) * (1 - q) := by
        have hb := hβ0 m
        push_cast
        have e : (1 - q * k) * (1 - q) = 1 - q * ((k : ℝ) + 1) + q * q * k := by ring
        have hqq : 0 ≤ q * q * (k : ℝ) := by positivity
        have : 1 - q * ((k : ℝ) + 1) ≤ (1 - q * k) * (1 - q) := by linarith
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left this hb
      rw [show m + (k + 1) = m + k + 1 by ring]
      linarith
    · have hb := hβ0 m
      have : β m * (1 - q * ((k + 1 : ℕ) : ℝ)) ≤ 0 := by
        push_cast
        exact mul_nonpos_of_nonneg_of_nonpos hb (by nlinarith)
      exact this.trans (hβ0 _)

/-- **Step 1 of the proof of Proposition B.4, pointwise.** Let `y` and `z` be paths (`y`
nondecreasing with `y(d) ≤ d`, `z` nondecreasing), let `β` be nonnegative,
nonincreasing on `[1, D]`, with `β(d+1) ≥ β(d)(1-q)` for `m ≤ d < 2m`, and let `2m ≤ D ≤ t+1`.
With `Γ_d = d - y(d) + z(t+1-d)` and `𝓔 = {z(t) ≤ m-1, y(2m) ≤ m}`:
`∑_d β(d) 1{Γ_d = m} ≥ β(m)(1_𝓔 - q y(2m))`. -/
theorem B4_pointwise (β : ℕ → ℝ) (hβ0 : ∀ d, 0 ≤ β d) {D t m : ℕ} (hm : 1 ≤ m) (h2m : 2 * m ≤ D)
    (hD : D ≤ t + 1) (hanti : ∀ d, 1 ≤ d → d + 1 ≤ D → β (d + 1) ≤ β d)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hratio : ∀ d, m ≤ d → d + 1 ≤ 2 * m → β d * (1 - q) ≤ β (d + 1))
    (y z : ℕ → ℕ) (hymono : ∀ d, y d ≤ y (d + 1))
    (hyle : ∀ d, y d ≤ d) (hzmono : ∀ k, z k ≤ z (k + 1)) :
    β m * ((if z t ≤ m - 1 ∧ y (2 * m) ≤ m then (1 : ℝ) else 0) - q * y (2 * m)) ≤
      ∑ d ∈ range (t + 2), β d * (if d - y d + z (t + 1 - d) = m then (1 : ℝ) else 0) := by
  have hS0 : 0 ≤ ∑ d ∈ range (t + 2), β d * (if d - y d + z (t + 1 - d) = m then (1 : ℝ) else 0) :=
    Finset.sum_nonneg (fun d _ => mul_nonneg (hβ0 d) (by split_ifs <;> norm_num))
  have hy0 : (0 : ℝ) ≤ y (2 * m) := Nat.cast_nonneg _
  by_cases hE : z t ≤ m - 1 ∧ y (2 * m) ≤ m
  · rw [if_pos hE]
    obtain ⟨hz, hy⟩ := hE
    have hymono' : ∀ i j, i ≤ j → y i ≤ y j := by
      intro i j hij
      induction j, hij using Nat.le_induction with
      | base => exact le_rfl
      | succ j _ ih => exact ih.trans (hymono j)
    have hzmono' : ∀ i j, i ≤ j → z i ≤ z j := by
      intro i j hij
      induction j, hij using Nat.le_induction with
      | base => exact le_rfl
      | succ j _ ih => exact ih.trans (hzmono j)
    set d0 := m + y (2 * m) with hd0
    have hd02 : d0 ≤ 2 * m := by omega
    set Γ : ℕ → ℕ := fun d => d - y d + z (t + 1 - d) with hΓ
    have hΓ1 : Γ 1 ≤ m := by
      simp only [hΓ]
      have := hyle 1
      rw [show t + 1 - 1 = t by omega]
      omega
    have hΓd0 : m ≤ Γ d0 := by
      simp only [hΓ]
      have := hymono' d0 (2 * m) hd02
      have := hyle d0
      omega
    have hΓstep : ∀ d, 1 ≤ d → d < d0 → Γ (d + 1) ≤ Γ d + 1 := by
      intro d _ _
      simp only [hΓ]
      have h1 := hymono d
      have h2 := hyle d
      have h3 := hzmono' (t + 1 - (d + 1)) (t + 1 - d) (by omega)
      omega
    obtain ⟨d1, hd1a, hd1b, hd1c⟩ := discrete_ivt Γ (show 1 ≤ d0 by omega) hΓ1 hΓd0 hΓstep
    -- the sum is at least the term `d1`
    have hterm : β d1 ≤ ∑ d ∈ range (t + 2), β d * (if d - y d + z (t + 1 - d) = m then (1 : ℝ) else 0) := by
      have := Finset.single_le_sum (f := fun d => β d * (if d - y d + z (t + 1 - d) = m then (1 : ℝ) else 0))
        (fun d _ => mul_nonneg (hβ0 d) (by split_ifs <;> norm_num))
        (Finset.mem_range.2 (show d1 < t + 2 by omega))
      rw [if_pos (by simpa [hΓ] using hd1c), mul_one] at this
      exact this
    -- `β` is nonincreasing from `d1` to `d0`
    have hmono : β d0 ≤ β d1 := by
      have : ∀ k, d1 + k ≤ d0 → β (d1 + k) ≤ β d1 := by
        intro k
        induction k with
        | zero => intro _; simp
        | succ k ih =>
          intro hk
          have := hanti (d1 + k) (by omega) (by omega)
          rw [show d1 + (k + 1) = d1 + k + 1 by ring]
          exact this.trans (ih (by omega))
      have h := this (d0 - d1) (by omega)
      rwa [show d1 + (d0 - d1) = d0 by omega] at h
    -- `β(m + y) ≥ β(m)(1 - q y)`
    have hshift := beta_shift_ge β hβ0 hq0 hq1 (m := m) (K := m)
      (fun k hk => hratio (m + k) (by omega) (by omega)) (y (2 * m)) hy
    have : β m * (1 - q * y (2 * m)) ≤ β d0 := hshift
    linarith
  · rw [if_neg hE]
    have : β m * (0 - q * y (2 * m)) ≤ 0 := by
      have := mul_nonneg (mul_nonneg (hβ0 m) hq0) hy0
      nlinarith
    linarith

/-- **Step 1 of the proof of Proposition B.4, in expectation.** For `0 ≤ ε ≤ 1`, `N = t + 1`,
`j = a + 1` with `1 ≤ a`, `1 ≤ m`, `4m ≤ N`, `2m + a ≤ N` and `2(a-1) ≤ N`, and
`q = 2(a-1)/N` (the paper's `2(j-2)/N`):
`Q_j(m) ≥ β_j(m) [1 - P(Y_{2m} > m) - P(Z^{(j)}_{N-1} ≥ m) - q E Y_{2m}]`. -/
theorem B4_one_j {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {t a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m)
    (h4m : 4 * m ≤ t + 1) (h2ma : 2 * m + a ≤ t + 1) (hqa : 2 * (a - 1) ≤ t + 1) :
    stLaw (a + 1) (t - a) m * (1
        - (∑ b ∈ range (2 * m + 1), if m + 1 ≤ b then law ε (2 * m) b else 0)
        - (∑ b ∈ range (t + 1), if m ≤ b then lawFrom ε a (t - a) b else 0)
        - 2 * ((a : ℝ) - 1) / ((t : ℝ) + 1) *
            ∑ b ∈ range (2 * m + 1), law ε (2 * m) b * (b : ℝ)) ≤
      ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d * convYZ ε a t d m := by
  obtain ⟨Y⟩ := chainReal_exists h0 h1 (k₀ := 1) (n := t + 1) le_rfl (by omega)
  obtain ⟨Z⟩ := chainReal_exists h0 h1 (k₀ := a) (n := t + 1) ha (by omega)
  set β : ℕ → ℝ := fun d => stLaw (a + 1) (t - a) d with hβ
  have hβ0 : ∀ d, 0 ≤ β d := fun d => stLaw_nonneg (by omega) _ _
  set q : ℝ := 2 * ((a : ℝ) - 1) / ((t : ℝ) + 1) with hq
  have ht0 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hq0 : 0 ≤ q := by rw [hq]; apply div_nonneg _ ht0.le; linarith
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one ht0]
    have : ((2 * (a - 1) : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast hqa
    push_cast [Nat.cast_sub ha] at this
    linarith
  -- the ratio bound `β(d+1) ≥ β(d)(1-q)` for `m ≤ d < 2m`
  have hratio : ∀ d, m ≤ d → d + 1 ≤ 2 * m → β d * (1 - q) ≤ β (d + 1) := by
    intro d hd1 hd2
    simp only [hβ]
    rw [stLaw_succ_eq (by omega) (by omega) (by omega)]
    apply mul_le_mul_of_nonneg_left _ (stLaw_nonneg (by omega) _ _)
    have hcast : ((a + 1 : ℕ) : ℝ) + ((t - a : ℕ) : ℝ) - d - 1 = (t : ℝ) - d := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast]
    have htd : (t : ℝ) - d ≥ ((t : ℝ) + 1) / 2 := by
      have h4 : ((4 * m : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast h4m
      have h5 : ((d + 1 : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast hd2
      push_cast at h4 h5
      linarith
    have htd0 : (0 : ℝ) < (t : ℝ) - d := by linarith
    have : (((a + 1 : ℕ) : ℝ) - 2) / ((t : ℝ) - d) ≤ q := by
      rw [hq, div_le_div_iff₀ htd0 ht0]
      push_cast
      nlinarith
    linarith
  have hanti : ∀ d, 1 ≤ d → d + 1 ≤ t - a + 1 → β (d + 1) ≤ β d :=
    fun d hd1 hd2 => stLaw_antitone (by omega) hd1 hd2
  -- the inner sum as an expectation over the two paths
  have hQ : ∑ d ∈ range (t + 2), stLaw (a + 1) (t - a) d * convYZ ε a t d m =
      ∑ ω₁, ∑ ω₂, Y.p ω₁ * Z.p ω₂ * ∑ d ∈ range (t + 2),
        β d * (if d - Y.G ω₁ d + Z.G ω₂ (t + 1 - d) = m then (1 : ℝ) else 0) := by
    have e : ∀ d ∈ range (t + 2), stLaw (a + 1) (t - a) d * convYZ ε a t d m =
        ∑ ω₁, ∑ ω₂, Y.p ω₁ * Z.p ω₂ *
          (β d * (if d - Y.G ω₁ d + Z.G ω₂ (t + 1 - d) = m then (1 : ℝ) else 0)) := by
      intro d hd
      have hd' := Finset.mem_range.1 hd
      have := Inner_eq_real Y Z (t := t) (d := d) (by omega) (by omega) (by omega)
        (fun d y z => if d - y + z = m then (1 : ℝ) else 0)
      have hc : convYZ ε a t d m = RRT.Inner ε a t d
          (fun d y z => if d - y + z = m then (1 : ℝ) else 0) := rfl
      rw [hc, this, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ω₁ _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ω₂ _ => ?_)
      simp only [hβ]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ω₁ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ω₂ _ => ?_)
    rw [Finset.mul_sum]
  rw [hQ]
  -- pointwise bound
  have hpt : ∀ ω₁ ω₂, Y.p ω₁ * Z.p ω₂ * (β m * ((if Z.G ω₂ t ≤ m - 1 ∧ Y.G ω₁ (2 * m) ≤ m
      then (1 : ℝ) else 0) - q * Y.G ω₁ (2 * m))) ≤
      Y.p ω₁ * Z.p ω₂ * ∑ d ∈ range (t + 2),
        β d * (if d - Y.G ω₁ d + Z.G ω₂ (t + 1 - d) = m then (1 : ℝ) else 0) := by
    intro ω₁ ω₂
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Y.p_nonneg ω₁) (Z.p_nonneg ω₂))
    exact B4_pointwise β hβ0 hm (show 2 * m ≤ t - a + 1 by omega) (by omega) hanti hq0 hq1 hratio
      (Y.G ω₁) (Z.G ω₂) (Y.G_mono ω₁) (Y.G_le ω₁) (Z.G_mono ω₂)
  refine le_trans ?_ (Finset.sum_le_sum (fun ω₁ _ => Finset.sum_le_sum (fun ω₂ _ => hpt ω₁ ω₂)))
  -- the indicator of `𝓔` is at least `1 - 1_A - 1_B`
  have hind : ∀ ω₁ ω₂, (1 : ℝ) - (if m + 1 ≤ Y.G ω₁ (2 * m) then 1 else 0) -
      (if m ≤ Z.G ω₂ t then 1 else 0) ≤
      (if Z.G ω₂ t ≤ m - 1 ∧ Y.G ω₁ (2 * m) ≤ m then (1 : ℝ) else 0) := by
    intro ω₁ ω₂
    by_cases hA : m + 1 ≤ Y.G ω₁ (2 * m)
    · rw [if_pos hA]; split_ifs <;> norm_num
    · by_cases hB : m ≤ Z.G ω₂ t
      · rw [if_neg hA, if_pos hB]; split_ifs <;> norm_num
      · rw [if_neg hA, if_neg hB, if_pos ⟨by omega, by omega⟩]; norm_num
  have hpt2 : ∀ ω₁ ω₂, Y.p ω₁ * Z.p ω₂ * (β m * ((1 : ℝ) - (if m + 1 ≤ Y.G ω₁ (2 * m) then 1 else 0) -
      (if m ≤ Z.G ω₂ t then 1 else 0) - q * Y.G ω₁ (2 * m))) ≤
      Y.p ω₁ * Z.p ω₂ * (β m * ((if Z.G ω₂ t ≤ m - 1 ∧ Y.G ω₁ (2 * m) ≤ m
        then (1 : ℝ) else 0) - q * Y.G ω₁ (2 * m))) := by
    intro ω₁ ω₂
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Y.p_nonneg ω₁) (Z.p_nonneg ω₂))
    apply mul_le_mul_of_nonneg_left _ (hβ0 m)
    linarith [hind ω₁ ω₂]
  refine le_trans ?_ (Finset.sum_le_sum (fun ω₁ _ => Finset.sum_le_sum (fun ω₂ _ => hpt2 ω₁ ω₂)))
  -- evaluate the expectations
  have hPY : (∑ ω₁, Y.p ω₁ * (if m + 1 ≤ Y.G ω₁ (2 * m) then (1 : ℝ) else 0)) =
      ∑ b ∈ range (2 * m + 1), if m + 1 ≤ b then law ε (2 * m) b else 0 := by
    rw [Y.sum_eq (show 2 * m ≤ t + 1 by omega) (fun b => if m + 1 ≤ b then (1 : ℝ) else 0)
      (show 2 * m < 2 * m + 1 by omega)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [lawFrom_one_pred]; split_ifs <;> ring
  have hEY : (∑ ω₁, Y.p ω₁ * (Y.G ω₁ (2 * m) : ℝ)) =
      ∑ b ∈ range (2 * m + 1), law ε (2 * m) b * (b : ℝ) := by
    rw [Y.sum_eq (show 2 * m ≤ t + 1 by omega) (fun b => (b : ℝ)) (show 2 * m < 2 * m + 1 by omega)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [lawFrom_one_pred]
  have hPZ : (∑ ω₂, Z.p ω₂ * (if m ≤ Z.G ω₂ t then (1 : ℝ) else 0)) =
      ∑ b ∈ range (t + 1), if m ≤ b then lawFrom ε a (t - a) b else 0 := by
    rw [Z.sum_eq (show t ≤ t + 1 by omega) (fun b => if m ≤ b then (1 : ℝ) else 0)
      (show t < t + 1 by omega)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    split_ifs <;> ring
  have e : ∀ ω₁ ω₂, Y.p ω₁ * Z.p ω₂ * (β m * ((1 : ℝ) - (if m + 1 ≤ Y.G ω₁ (2 * m) then 1 else 0) -
      (if m ≤ Z.G ω₂ t then 1 else 0) - q * Y.G ω₁ (2 * m))) =
      β m * (Z.p ω₂ * Y.p ω₁ - Z.p ω₂ * (Y.p ω₁ * (if m + 1 ≤ Y.G ω₁ (2 * m) then 1 else 0)) -
        Y.p ω₁ * (Z.p ω₂ * (if m ≤ Z.G ω₂ t then 1 else 0)) -
          q * (Z.p ω₂ * (Y.p ω₁ * (Y.G ω₁ (2 * m) : ℝ)))) := by
    intro ω₁ ω₂; ring
  simp only [e]
  simp only [← Finset.mul_sum]
  simp only [Finset.sum_sub_distrib]
  have s1 : ∑ ω₁ : Y.Ω, ∑ ω₂ : Z.Ω, Z.p ω₂ * Y.p ω₁ = 1 := by
    simp only [← Finset.sum_mul, Z.p_sum, one_mul, Y.p_sum]
  have s2 : ∑ ω₁ : Y.Ω, ∑ ω₂ : Z.Ω, Z.p ω₂ * (Y.p ω₁ * (if m + 1 ≤ Y.G ω₁ (2 * m) then (1 : ℝ) else 0))
      = ∑ b ∈ range (2 * m + 1), if m + 1 ≤ b then law ε (2 * m) b else 0 := by
    simp only [← Finset.sum_mul, Z.p_sum, one_mul, hPY]
  have s3 : ∑ ω₁ : Y.Ω, ∑ ω₂ : Z.Ω, Y.p ω₁ * (Z.p ω₂ * (if m ≤ Z.G ω₂ t then (1 : ℝ) else 0))
      = ∑ b ∈ range (t + 1), if m ≤ b then lawFrom ε a (t - a) b else 0 := by
    simp only [← Finset.mul_sum, hPZ, ← Finset.sum_mul, Y.p_sum, one_mul]
  have s4 : ∑ ω₁ : Y.Ω, ∑ ω₂ : Z.Ω, Z.p ω₂ * (Y.p ω₁ * (Y.G ω₁ (2 * m) : ℝ))
      = ∑ b ∈ range (2 * m + 1), law ε (2 * m) b * (b : ℝ) := by
    simp only [← Finset.sum_mul, Z.p_sum, one_mul, hEY]
  have s4' : ∑ ω₁ : Y.Ω, ∑ ω₂ : Z.Ω, q * (Z.p ω₂ * (Y.p ω₁ * (Y.G ω₁ (2 * m) : ℝ))) =
      q * ∑ b ∈ range (2 * m + 1), law ε (2 * m) b * (b : ℝ) := by
    rw [← s4]; simp only [Finset.mul_sum]
  rw [s1, s2, s3, s4']

end Kagey131.PaperD
