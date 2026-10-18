import PaperD.T6_CrossingAsymp

/-!
# Paper D, Theorem 2.8 (`thm:erw-markov`): the elephant crossing against the persistent walk

The paper compares the elephant crossing `x_N` with the crossing `z_N = N(1 - p_N)` of the
persistent (Markov) walk, using only Paper A's crossing equation
(`[paperA, Proposition 3.8]`, equation `eq:markov-crossing` of Paper D):
for every `N ≥ 2`,
`z_N + (1/2) log z_N = L + c₀ + 1/(8 z_N) + R_N`, `c₀ = (1/2) log(π/8)`,
`|R_N| ≤ 1/(4L²) + (L² + L)/N`, and `L/2 ≤ z_N ≤ L`.

## The hypothesis

`MarkovCrossingEqAt N z` is exactly that conclusion for a real number `z` at `N`, and
`PaperAProp38 z` says it holds for every `N ≥ 2` for a sequence `z : ℕ → ℝ`. The predicate is
written in the same form as the conclusion of Paper A's Lean theorem `Kagey131.crossing_equation`
(`crossRem N = z + log z / 2 - log N - log (π/8) / 2 - 1/(8z)` with `z = N (1 - pN N)`), so
`PaperAProp38 (fun N => N * (1 - pN N))` is its last three conjuncts. Paper A is not imported
into Paper D, so here `z` is arbitrary and the identification of `z` with the persistent-walk
crossing is carried entirely by the hypothesis.

## Results

* `markov_explicit`: for `N = 2h` with `L = log N ≥ 30`, given Theorem 2.6 at `N` and the crossing
  equation at `N`, `|Υ_N - c_*/L| ≤ (log L + 15)/L²`, where
  `Υ_N = x_N - (2 z_N - log(2π))` and `c_* = (1/2) log(2π) - 1/4`.
* `markov_isBigO`: `Υ_N = c_*/log N + O(log log N/(log N)²)` as `N = 2h → ∞` (Theorem 2.8).
-/

namespace Kagey131.PaperD

open Real Set Filter Asymptotics

/-- **Hypothesis** (Paper A, Proposition 3.8, at `N`): the crossing equation of the persistent
walk, `|z + (1/2) log z - log N - (1/2) log(π/8) - 1/(8z)| ≤ 1/(4L²) + (L²+L)/N` and
`L/2 ≤ z ≤ L`, `L = log N`. -/
def MarkovCrossingEqAt (N : ℕ) (z : ℝ) : Prop :=
  |z + Real.log z / 2 - Real.log N - Real.log (π / 8) / 2 - 1 / (8 * z)| ≤
      1 / (4 * Real.log N ^ 2) + (Real.log N ^ 2 + Real.log N) / N ∧
    Real.log N / 2 ≤ z ∧ z ≤ Real.log N

/-- **Hypothesis** (Paper A, Proposition 3.8): the crossing equation for every `N ≥ 2`. -/
def PaperAProp38 (z : ℕ → ℝ) : Prop := ∀ N : ℕ, 2 ≤ N → MarkovCrossingEqAt N (z N)

/-- `c_* = (1/2) log(2π) - 1/4 = 0.6689…`. -/
noncomputable def cStar : ℝ := Real.log (2 * π) / 2 - 1 / 4

theorem log_two_pi_bounds : 0 ≤ Real.log (2 * π) ∧ Real.log (2 * π) ≤ 2 := by
  have hpi := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  refine ⟨Real.log_nonneg (by linarith), ?_⟩
  rw [Real.log_le_iff_le_exp (by linarith)]
  have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e2]
  have := Real.exp_one_gt_d9
  nlinarith

theorem log_pi_div_eight_bounds : -1 ≤ Real.log (π / 8) ∧ Real.log (π / 8) ≤ 0 := by
  have hpi := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  refine ⟨?_, Real.log_nonpos (by positivity) (by linarith)⟩
  rw [Real.le_log_iff_exp_le (by positivity), Real.exp_neg]
  have := Real.exp_one_gt_d9
  rw [inv_le_comm₀ (Real.exp_pos 1) (by positivity), inv_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem log_constants_identity :
    Real.log (π / 8) + Real.log 2 - Real.log (2 * π) = -Real.log 8 := by
  have hpi := Real.pi_pos
  rw [Real.log_div hpi.ne' (by norm_num), Real.log_mul (by norm_num) hpi.ne']
  ring

set_option maxHeartbeats 1000000 in
/-- **Theorem 2.8 (`thm:erw-markov`), explicit form.** Let `N = 2h` with `L = log N ≥ 30`.
Assume Theorem 2.6 at `N` and Paper A's crossing equation at `N` for a real `z`. Then
`|x_N - (2z - log(2π)) - c_*/L| ≤ (log L + 15)/L²`. -/
theorem markov_explicit {h : ℕ} (hL : 30 ≤ Real.log (2 * (h : ℝ)))
    (hLo : CenterLowerBoundAt h) (hUp : CenterUpperBoundAt h) {z : ℝ}
    (hz : MarkovCrossingEqAt (2 * h) z) :
    |crossingX h - (2 * z - Real.log (2 * π)) - cStar / Real.log (2 * (h : ℝ))| ≤
      (Real.log (Real.log (2 * (h : ℝ))) + 15) / Real.log (2 * (h : ℝ)) ^ 2 := by
  have hh := one_le_of_L30 hL
  have hN0 : (0 : ℝ) < 2 * (h : ℝ) := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  obtain ⟨-, hρδ, hρ⟩ := consequences_L30 hN0 hL
  obtain ⟨-, -, hG, -⟩ := crossing_explicit hL hLo hUp
  have hx0 : 0 < crossingX h := by
    unfold crossingX
    exact mul_pos hN0 (crossingEps_spec hh).1.1
  unfold MarkovCrossingEqAt at hz
  push_cast at hz
  obtain ⟨he, hzL1, hzL2⟩ := hz
  have hΛL : LamN (2 * (h : ℝ)) = 2 * Real.log (2 * (h : ℝ)) - Real.log 8 := rfl
  unfold cStar
  set N : ℝ := 2 * (h : ℝ) with hNdef
  set L := Real.log N with hLdef
  set x := crossingX h with hxdef
  set ℓ := Real.log (2 * π) with hℓdef
  set ρ := rhoN N with hρdef
  set δ' := (L ^ 2 + L) / N with hδdef
  set e := z + Real.log z / 2 - L - Real.log (π / 8) / 2 - 1 / (8 * z) with hedef
  obtain ⟨hℓ0, hℓ2⟩ := log_two_pi_bounds
  rw [← hℓdef] at hℓ0 hℓ2
  obtain ⟨hc1, hc2⟩ := log_pi_div_eight_bounds
  have hid := log_constants_identity
  have hL0 : 0 < L := by linarith
  have hz0 : 0 < z := by linarith
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlogLh := log_le_half hL0
  have hq0 : 0 < 1 / L ^ 2 := by positivity
  have hδ'0 : 0 ≤ δ' := by rw [hδdef]; positivity
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; unfold rhoN; rw [← hLdef]; positivity
  clear_value e δ' ρ ℓ x L N
  have hq900 : 1 / L ^ 2 ≤ 1 / 900 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hq4 : 1 / (4 * L ^ 2) = (1 / 4) * (1 / L ^ 2) := by field_simp
  rw [hq4] at he
  have heabs := abs_le.mp he
  -- `D = L - z ∈ [0, (1/2) log L + 1]`
  have hlogz : Real.log z ≤ Real.log L := Real.log_le_log hz0 hzL2
  have h8z : 0 < 1 / (8 * z) := by positivity
  have hD : L - z ≤ Real.log L / 2 + 1 := by
    have : L - z = Real.log z / 2 - Real.log (π / 8) / 2 - 1 / (8 * z) - e := by
      rw [hedef]; ring
    rw [this]; linarith
  -- `u = ℓ/(2z)`
  obtain ⟨u, hudef⟩ : ∃ u, u = ℓ / (2 * z) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hudef]; exact div_nonneg hℓ0 (by positivity)
  have hu2 : u ≤ 2 / L := by
    rw [hudef, div_le_div_iff₀ (by positivity) hL0]
    nlinarith [mul_le_mul_of_nonneg_right hℓ2 hL0.le]
  have huq : u ^ 2 ≤ 4 * (1 / L ^ 2) := by
    have h1 := mul_le_mul hu2 hu2 hu0 (by positivity)
    have e1 : u ^ 2 = u * u := by ring
    have e2 : 2 / L * (2 / L) = 4 * (1 / L ^ 2) := by ring
    linarith
  have hu12 : u ≤ 1 / 2 := by
    have : 2 / L ≤ 1 / 2 := by rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
    linarith
  have hR0 := log_one_sub_le (show u < 1 by linarith)
  have hR1 := neg_log_one_sub_le hu0 hu12
  -- `w = 2z - ℓ` and `G(w) = Λ + 2e + 1/(4z) + log(1-u)`
  obtain ⟨w, hwdef⟩ : ∃ w, w = 2 * z - ℓ := ⟨_, rfl⟩
  have hwL : L - 2 ≤ w := by rw [hwdef]; linarith
  have hw0 : 0 < w := by linarith
  have hwfac : w = 2 * z * (1 - u) := by rw [hwdef, hudef]; field_simp
  have hlogw : Real.log w = Real.log 2 + Real.log z + Real.log (1 - u) := by
    rw [hwfac, Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) hz0.ne']
  have hGw : Gfun w = 2 * L - Real.log 8 + 2 * e + 1 / (4 * z) + Real.log (1 - u) := by
    unfold Gfun
    rw [hlogw]
    have : Real.log z = 2 * (e + L + Real.log (π / 8) / 2 + 1 / (8 * z) - z) := by
      rw [hedef]; ring
    rw [this, hwdef]
    have e4 : 2 * (1 / (8 * z)) = 1 / (4 * z) := by field_simp; ring
    linarith
  -- `G(x) - G(w) - c_*/L = E₁`
  have hcz : 1 / (4 * z) - u = -((ℓ / 2 - 1 / 4) / z) := by
    rw [hudef]; field_simp; ring
  obtain ⟨q, hqdef⟩ : ∃ q, q = (L - z) / (z * L) := ⟨_, rfl⟩
  have hq0' : 0 ≤ q := by rw [hqdef]; exact div_nonneg (by linarith) (by positivity)
  have hq1 : q ≤ (Real.log L + 2) * (1 / L ^ 2) := by
    have h1 : q ≤ (L - z) / (L ^ 2 / 2) := by
      rw [hqdef]
      exact div_le_div_of_nonneg_left (by linarith) (by positivity)
        (by have := mul_le_mul_of_nonneg_right hzL1 hL0.le
            have e : L ^ 2 / 2 = L / 2 * L := by ring
            linarith)
    have h2 : (L - z) / (L ^ 2 / 2) = 2 * (L - z) * (1 / L ^ 2) := by field_simp
    have h3 : 2 * (L - z) * (1 / L ^ 2) ≤ (Real.log L + 2) * (1 / L ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hq0.le
    linarith
  have hcq : (ℓ / 2 - 1 / 4) / z - (ℓ / 2 - 1 / 4) / L = (ℓ / 2 - 1 / 4) * q := by
    rw [hqdef]; field_simp
  have hcqb : |(ℓ / 2 - 1 / 4) * q| ≤ (3 / 4) * ((Real.log L + 2) * (1 / L ^ 2)) := by
    rw [abs_mul, abs_of_nonneg hq0']
    have : |ℓ / 2 - 1 / 4| ≤ 3 / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc |ℓ / 2 - 1 / 4| * q ≤ 3 / 4 * q := mul_le_mul_of_nonneg_right this hq0'
      _ ≤ _ := mul_le_mul_of_nonneg_left hq1 (by norm_num)
  obtain ⟨E₁, hE1def⟩ : ∃ E₁, E₁ = Gfun x - Gfun w - (ℓ / 2 - 1 / 4) / L := ⟨_, rfl⟩
  have hE1eq : E₁ = (Gfun x - LamN N) - 2 * e + (-Real.log (1 - u) - u) +
      (ℓ / 2 - 1 / 4) * q := by
    rw [hE1def, hGw, hΛL, ← hcq]; linarith [hcz]
  have hGabs := abs_le.mp hG
  have hcqabs := abs_le.mp hcqb
  have hE1 : |E₁| ≤ (3 / 4) * (Real.log L * (1 / L ^ 2)) + 11 * (1 / L ^ 2) := by
    have ex : (3 / 4) * ((Real.log L + 2) * (1 / L ^ 2)) =
        (3 / 4) * (Real.log L * (1 / L ^ 2)) + (3 / 2) * (1 / L ^ 2) := by ring
    rw [hE1eq, abs_le]
    constructor <;> linarith
  have hE1abs := abs_le.mp hE1
  -- `|Δ| ≤ |G(x) - G(w)| ≤ 2/L`
  have hη : |Gfun x - Gfun w| ≤ 2 / L := by
    have hlq : Real.log L * (1 / L ^ 2) ≤ (1 / 2) * (1 / L) := by
      have : Real.log L * (1 / L ^ 2) ≤ (L / 2) * (1 / L ^ 2) :=
        mul_le_mul_of_nonneg_right hlogLh hq0.le
      have e : (L / 2) * (1 / L ^ 2) = (1 / 2) * (1 / L) := by field_simp
      linarith
    have hqL : 1 / L ^ 2 ≤ (1 / 30) * (1 / L) := by
      rw [show (1 : ℝ) / L ^ 2 = (1 / L) * (1 / L) by ring]
      have : 1 / L ≤ 1 / 30 := one_div_le_one_div_of_le (by norm_num) hL
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hc : |(ℓ / 2 - 1 / 4) / L| ≤ (3 / 4) * (1 / L) := by
      rw [abs_div, abs_of_pos hL0, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (by positivity)
    have hcabs := abs_le.mp hc
    have e2 : 2 / L = 2 * (1 / L) := by ring
    have hsplit : Gfun x - Gfun w = E₁ + (ℓ / 2 - 1 / 4) / L := by rw [hE1def]; ring
    rw [hsplit, abs_le, e2]
    have hL1 : 0 < 1 / L := by positivity
    constructor
    · linarith only [hE1abs.1, hcabs.1, hlq, hqL, hL1]
    · linarith only [hE1abs.2, hcabs.2, hlq, hqL, hL1]
  have hΔ : |x - w| ≤ 2 / L := by
    refine le_trans ?_ hη
    rcases le_total w x with hwx | hxw
    · have := Gfun_sub_ge hw0 hwx
      have a1 : 0 ≤ x - w := by linarith only [hwx]
      have a2 : 0 ≤ Gfun x - Gfun w := by linarith only [this, hwx]
      rw [abs_of_nonneg a1, abs_of_nonneg a2]
      exact this
    · have := Gfun_sub_ge hx0 hxw
      have a1 : x - w ≤ 0 := by linarith only [hxw]
      have a2 : Gfun x - Gfun w ≤ 0 := by linarith only [this, hxw]
      rw [abs_of_nonpos a1, abs_of_nonpos a2]
      linarith only [this]
  have hΔabs := abs_le.mp hΔ
  have h2L : 2 / L ≤ 1 / 15 := by rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have hxL : L / 2 ≤ x := by linarith
  have hwL2 : L / 2 ≤ w := by linarith
  -- `|log x - log w| ≤ 4/L²`
  have hlog : |Real.log x - Real.log w| ≤ 4 * (1 / L ^ 2) := by
    have k : (2 / L) / (L / 2) = 4 * (1 / L ^ 2) := by field_simp; ring
    have a1 := log_sub_log_le hx0 hw0
    have a2 := log_sub_log_le hw0 hx0
    have b1 : (x - w) / w ≤ (2 / L) / (L / 2) := by
      rcases le_total w x with hwx | hxw
      · calc (x - w) / w ≤ (2 / L) / w := div_le_div_of_nonneg_right (by linarith) hw0.le
          _ ≤ (2 / L) / (L / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hwL2
      · have : (x - w) / w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw0.le
        have : 0 ≤ (2 / L) / (L / 2) := by positivity
        linarith
    have b2 : (w - x) / x ≤ (2 / L) / (L / 2) := by
      rcases le_total x w with hxw | hwx
      · calc (w - x) / x ≤ (2 / L) / x := div_le_div_of_nonneg_right (by linarith) hx0.le
          _ ≤ (2 / L) / (L / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hxL
      · have : (w - x) / x ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hx0.le
        have : 0 ≤ (2 / L) / (L / 2) := by positivity
        linarith
    rw [abs_le]; constructor <;> linarith
  have hlogabs := abs_le.mp hlog
  -- conclusion
  have hfin : x - w - (ℓ / 2 - 1 / 4) / L = E₁ - (Real.log x - Real.log w) := by
    rw [hE1def]; unfold Gfun; ring
  have hgoal : (Real.log L + 15) / L ^ 2 = Real.log L * (1 / L ^ 2) + 15 * (1 / L ^ 2) := by ring
  rw [← hwdef, hfin, hgoal, abs_le]
  have hlq0 : 0 ≤ Real.log L * (1 / L ^ 2) := mul_nonneg hlogL0 hq0.le
  constructor <;> linarith

/-- **Theorem 2.8 (`thm:erw-markov`):** `Υ_N = x_N - (2 z_N - log(2π)) = c_*/log N +
O(log log N / (log N)²)` as `N = 2h → ∞`, given Theorem 2.6 and Paper A's crossing equation
(Proposition 3.8 of Paper A) for the sequence `z`. -/
theorem markov_isBigO (hLo : CenterLowerBound) (hUp : CenterUpperBound) {z : ℕ → ℝ}
    (hA : PaperAProp38 z) :
    (fun h : ℕ => crossingX h - (2 * z (2 * h) - Real.log (2 * π)) -
        cStar / Real.log (2 * (h : ℝ))) =O[atTop]
      (fun h : ℕ => Real.log (Real.log (2 * (h : ℝ))) / Real.log (2 * (h : ℝ)) ^ 2) := by
  refine IsBigO.of_bound 16 ?_
  filter_upwards [eventually_L30] with h hL
  have hh := one_le_of_L30 hL
  have hc := markov_explicit hL (hLo h hh) (hUp h (ge32_of_L30 hL)) (hA (2 * h) (by omega))
  set L := Real.log (2 * (h : ℝ))
  have hL0 : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have := Real.exp_one_lt_d9
    linarith
  rw [Real.norm_of_nonneg
    (show (0 : ℝ) ≤ Real.log L / L ^ 2 from div_nonneg (by linarith) (by positivity)),
    Real.norm_eq_abs]
  refine le_trans hc ?_
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  linarith

end Kagey131.PaperD
