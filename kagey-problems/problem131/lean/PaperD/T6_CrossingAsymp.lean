import PaperD.T6_Crossing

/-!
# Paper D, Theorem 2.7 (`thm:erw-crossing`): explicit and asymptotic forms

From `crossing_trap` (Step 2 of the paper's proof) this module derives

* `crossing_explicit`: for every even `N = 2h` with `log N ≥ 30`, assuming Theorem 2.6 at `N`,
  `ρ_N ≤ 1/L²`, `|x_N - g_N| ≤ ρ_N`, `|G(x_N) - Λ_N| ≤ ρ_N`, and (part (b) with an explicit
  error) `|x_N - (2L - log L - log 16)| ≤ (2 log L + 5)/L`, where `L = log N`;
* `crossing_isBigO_G`, `crossing_isBigO_g`, `crossing_isBigO_expansion`: the `O(·)` statements of
  Theorem 2.7(a), (b) as `N = 2h → ∞`, assuming `CenterLowerBound` and `CenterUpperBound`.

The threshold `log N ≥ 30` is chosen so that the paper's condition `400 L(1+L) ≤ N` and the
nonemptiness of the two trapping ranges ("for large `N`" in the paper) follow by crude
inequalities (`e^L ≥ L^12/12!`); it plays no role in the asymptotic statements.
-/

namespace Kagey131.PaperD

open Real Set Filter Asymptotics

/-- For `L = log N ≥ 30`: `26 L⁴ + 20802 L³ ≤ N` (from `N = e^L ≥ L^12/12!`). -/
theorem big_of_L30 {N : ℝ} (hN : 0 < N) (hL : 30 ≤ Real.log N) :
    26 * Real.log N ^ 4 + 20802 * Real.log N ^ 3 ≤ N := by
  have hexp := Real.pow_div_factorial_le_exp (Real.log N) (by linarith) 12
  rw [Real.exp_log hN] at hexp
  have hf : ((Nat.factorial 12 : ℕ) : ℝ) = 479001600 := by norm_num [Nat.factorial]
  rw [hf] at hexp
  set L := Real.log N with hLdef
  have h8 : (30 : ℝ) ^ 8 ≤ L ^ 8 := pow_le_pow_left₀ (by norm_num) hL 8
  have h3 : 0 ≤ L ^ 3 := by positivity
  have h4 : 26 * L ^ 4 + 20802 * L ^ 3 ≤ 720 * L ^ 4 := by
    have : 20802 * L ^ 3 ≤ 694 * L ^ 4 := by
      have : L ^ 4 = L ^ 3 * L := by ring
      rw [this]; nlinarith
    linarith
  have h12 : 720 * L ^ 4 ≤ L ^ 12 / 479001600 := by
    rw [le_div_iff₀ (by norm_num)]
    have : L ^ 12 = L ^ 4 * L ^ 8 := by ring
    rw [this]
    have : 0 ≤ L ^ 4 := by positivity
    nlinarith
  linarith

/-- The consequences of `log N ≥ 30` used below. -/
theorem consequences_L30 {N : ℝ} (hN : 0 < N) (hL : 30 ≤ Real.log N) :
    400 * Real.log N * (1 + Real.log N) ≤ N ∧
      rhoN N + 2 * ((Real.log N ^ 2 + Real.log N) / N) ≤ 1 / Real.log N ^ 2 ∧
      rhoN N ≤ 1 / Real.log N ^ 2 := by
  have hb := big_of_L30 hN hL
  unfold rhoN
  set L := Real.log N with hLdef
  have hL0 : 0 < L := by linarith
  have key : (24 * L ^ 2 + 20800 * L) / N + 2 * ((L ^ 2 + L) / N) ≤ 1 / L ^ 2 := by
    have e : (24 * L ^ 2 + 20800 * L) / N + 2 * ((L ^ 2 + L) / N) =
        (26 * L ^ 2 + 20802 * L) / N := by ring
    rw [e, div_le_div_iff₀ hN (by positivity)]
    nlinarith
  refine ⟨?_, key, ?_⟩
  · have : 400 * L * (1 + L) ≤ 26 * L ^ 4 := by
      have h2 : 900 ≤ L ^ 2 := by nlinarith
      have : L ^ 4 = L ^ 2 * L ^ 2 := by ring
      rw [this]; nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg L)]
    nlinarith [pow_nonneg hL0.le 3]
  · have : 0 ≤ 2 * ((L ^ 2 + L) / N) := by positivity
    linarith

theorem log_two_bounds : 0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

/-- `log a - log b ≤ (a - b)/b` for `a, b > 0`. -/
theorem log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a - Real.log b ≤ (a - b) / b := by
  rw [← Real.log_div ha.ne' hb.ne']
  have := Real.log_le_sub_one_of_pos (div_pos ha hb)
  have e : a / b - 1 = (a - b) / b := by field_simp
  linarith

/-- `log y ≤ y/2` for `y > 0`. -/
theorem log_le_half {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / 2 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < y / 2 by positivity)
  rw [Real.log_div hy.ne' (by norm_num)] at h1
  have := log_two_bounds.2
  linarith

theorem one_le_of_L30 {h : ℕ} (hL : 30 ≤ Real.log (2 * (h : ℝ))) : 1 ≤ h := by
  rcases Nat.eq_zero_or_pos h with rfl | hp
  · simp at hL; linarith
  · exact hp

theorem ge32_of_L30 {h : ℕ} (hL : 30 ≤ Real.log (2 * (h : ℝ))) : 32 ≤ h := by
  have hh := one_le_of_L30 hL
  have hN : (0 : ℝ) < 2 * (h : ℝ) := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have h1 := (Real.le_log_iff_exp_le hN).mp hL
  have h2 := Real.pow_div_factorial_le_exp (30 : ℝ) (by norm_num) 2
  norm_num [Nat.factorial] at h2
  have : (32 : ℝ) ≤ h := by linarith
  exact_mod_cast this

/-- **Theorem 2.7 (`thm:erw-crossing`), explicit form.** Let `N = 2h` with `L = log N ≥ 30`,
and assume Theorem 2.6 at `N`. Then `ρ_N ≤ 1/L²`, the crossing satisfies
`|x_N - g_N| ≤ ρ_N` and `|x_N + log x_N - Λ_N| ≤ ρ_N` (part (a)), and
`|x_N - (2 log N - log log N - log 16)| ≤ (2 log log N + 5)/log N` (part (b)). -/
theorem crossing_explicit {h : ℕ} (hL : 30 ≤ Real.log (2 * (h : ℝ)))
    (hLo : CenterLowerBoundAt h) (hUp : CenterUpperBoundAt h) :
    rhoN (2 * (h : ℝ)) ≤ 1 / Real.log (2 * (h : ℝ)) ^ 2 ∧
      |crossingX h - gRoot (2 * (h : ℝ))| ≤ rhoN (2 * (h : ℝ)) ∧
      |Gfun (crossingX h) - LamN (2 * (h : ℝ))| ≤ rhoN (2 * (h : ℝ)) ∧
      |crossingX h - (2 * Real.log (2 * (h : ℝ)) - Real.log (Real.log (2 * (h : ℝ)))
          - Real.log 16)| ≤
        (2 * Real.log (Real.log (2 * (h : ℝ))) + 5) / Real.log (2 * (h : ℝ)) := by
  have hh := one_le_of_L30 hL
  have hN0 : (0 : ℝ) < 2 * (h : ℝ) := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  obtain ⟨h400, -, hρ⟩ := consequences_L30 hN0 hL
  have trap := crossing_trap (g := gRoot (2 * (h : ℝ))) hh hLo hUp h400
  have hρ0' : 0 ≤ rhoN (2 * (h : ℝ)) := by
    unfold rhoN; have : 0 < Real.log (2 * (h : ℝ)) := by linarith
    positivity
  have hΛL : LamN (2 * (h : ℝ)) = 2 * Real.log (2 * (h : ℝ)) - Real.log 8 := rfl
  set N : ℝ := 2 * (h : ℝ) with hNdef
  set L := Real.log N with hLdef
  set ρ := rhoN N with hρdef
  set Λ := LamN N with hΛdef
  have hl2 := log_two_bounds
  have hl8 : Real.log 8 = 3 * Real.log 2 := log_eight_eq'
  have hL0 : 0 < L := by linarith
  have hρ1 : ρ ≤ 1 / 900 := by
    have : (1 : ℝ) / L ^ 2 ≤ 1 / 900 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hΛ1 : 1 ≤ Λ := by rw [hΛL]; linarith
  obtain ⟨g1, g2, g3⟩ := gRoot_spec hΛ1
  rw [← hΛdef] at g1 g2 g3
  set g := gRoot N with hgdef
  have hlΛ := log_le_half (show 0 < Λ by linarith)
  have hg0 : 0 < g := by linarith
  obtain ⟨ha, hb⟩ := trap hg0 g3 (by linarith) (by rw [hΛL] at g2; linarith)
  refine ⟨hρ, ha, hb, ?_⟩
  -- part (b)
  have hl16 : Real.log 16 = 4 * Real.log 2 := log_sixteen_eq
  have hΛ2L : Λ ≤ 2 * L := by rw [hΛL]; linarith
  have hLΛ : L ≤ Λ := by rw [hΛL]; linarith
  have hlogΛ0 : 0 ≤ Real.log Λ := Real.log_nonneg hΛ1
  have hlog2L : Real.log (2 * L) = Real.log 2 + Real.log L :=
    Real.log_mul (by norm_num) hL0.ne'
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  -- A = log(2L) - log Λ ∈ [0, 2.1/L]
  have hA0 : Real.log Λ ≤ Real.log (2 * L) := Real.log_le_log (by linarith) hΛ2L
  have hA1 : Real.log (2 * L) - Real.log Λ ≤ 2.1 / L := by
    have := log_sub_log_le (show 0 < 2 * L by linarith) (show 0 < Λ by linarith)
    have e : 2 * L - Λ = Real.log 8 := by rw [hΛL]; ring
    rw [e] at this
    have h1 : Real.log 8 / Λ ≤ Real.log 8 / L :=
      div_le_div_of_nonneg_left (by linarith) hL0 hLΛ
    have h2 : Real.log 8 / L ≤ 2.1 / L := div_le_div_of_nonneg_right (by linarith) hL0.le
    linarith
  -- B = log Λ - log g ∈ [0, 2 log Λ / L]
  have hgG : g + Real.log g = Λ := g3
  have hB0 : Real.log g ≤ Real.log Λ := Real.log_le_log hg0 g2
  have hgL : L / 2 ≤ g := by linarith
  have hB1 : Real.log Λ - Real.log g ≤ 2 * Real.log Λ / L := by
    have := log_sub_log_le (show 0 < Λ by linarith) hg0
    have e : Λ - g = Real.log g := by linarith
    rw [e] at this
    have h1 : Real.log g / g ≤ Real.log Λ / g := div_le_div_of_nonneg_right hB0 hg0.le
    have h2 : Real.log Λ / g ≤ Real.log Λ / (L / 2) :=
      div_le_div_of_nonneg_left hlogΛ0 (by linarith) hgL
    have e2 : Real.log Λ / (L / 2) = 2 * Real.log Λ / L := by field_simp
    linarith
  have hρL : ρ ≤ 1 / L := by
    have : 1 / L ^ 2 ≤ 1 / L := by
      rw [div_le_div_iff₀ (by positivity) hL0]; nlinarith
    linarith
  have hab := abs_le.mp ha
  rw [abs_le]
  have eq : crossingX h - (2 * L - Real.log L - Real.log 16) =
      (crossingX h - g) + (Real.log Λ - Real.log g) + (Real.log (2 * L) - Real.log Λ) := by
    rw [hlog2L, hl16]; rw [hΛL] at hgG; linarith
  rw [eq]
  have e3 : (2 * Real.log L + 5) / L = 1 / L + 2 * (Real.log 2 + Real.log L) / L + 2.1 / L
      + (5 - 1 - 2.1 - 2 * Real.log 2) / L := by ring
  have e4 : 0 ≤ (5 - 1 - 2.1 - 2 * Real.log 2) / L := div_nonneg (by linarith) hL0.le
  have e5 : 2 * Real.log Λ / L ≤ 2 * (Real.log 2 + Real.log L) / L :=
    div_le_div_of_nonneg_right (by linarith) hL0.le
  have e6 : 0 ≤ (2 * Real.log L + 5) / L - 1 / L := by
    rw [← sub_div]; exact div_nonneg (by linarith) hL0.le
  constructor <;> linarith

/-! ### The asymptotic statements -/

theorem eventually_L30 : ∀ᶠ h : ℕ in atTop, 30 ≤ Real.log (2 * (h : ℝ)) := by
  refine eventually_atTop.mpr ⟨⌈Real.exp 30⌉₊, fun h hh => ?_⟩
  have h1 : Real.exp 30 ≤ (h : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hh)
  have h2 : Real.exp 30 ≤ 2 * (h : ℝ) := by linarith [Real.exp_pos 30]
  rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 30])]
  exact h2

/-- **Theorem 2.7(a) (`thm:erw-crossing`), first claim:** `x_N + log x_N = Λ_N + O(L²/N)` as
`N = 2h → ∞`, given Theorem 2.6. -/
theorem crossing_isBigO_G (hLo : CenterLowerBound) (hUp : CenterUpperBound) :
    (fun h : ℕ => Gfun (crossingX h) - LamN (2 * (h : ℝ))) =O[atTop]
      (fun h : ℕ => Real.log (2 * (h : ℝ)) ^ 2 / (2 * (h : ℝ))) := by
  refine IsBigO.of_bound 20824 ?_
  filter_upwards [eventually_L30] with h hL
  have hh := one_le_of_L30 hL
  obtain ⟨-, -, hb, -⟩ := crossing_explicit hL (hLo h hh) (hUp h (ge32_of_L30 hL))
  have hN0 : (0 : ℝ) < 2 * (h : ℝ) := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  rw [Real.norm_of_nonneg
    (show (0 : ℝ) ≤ Real.log (2 * (h : ℝ)) ^ 2 / (2 * (h : ℝ)) by positivity), Real.norm_eq_abs]
  refine le_trans hb ?_
  unfold rhoN
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hN0]
  nlinarith

/-- **Theorem 2.7(a) (`thm:erw-crossing`), second claim:** `x_N = g_N + O(L²/N)`. -/
theorem crossing_isBigO_g (hLo : CenterLowerBound) (hUp : CenterUpperBound) :
    (fun h : ℕ => crossingX h - gRoot (2 * (h : ℝ))) =O[atTop]
      (fun h : ℕ => Real.log (2 * (h : ℝ)) ^ 2 / (2 * (h : ℝ))) := by
  refine IsBigO.of_bound 20824 ?_
  filter_upwards [eventually_L30] with h hL
  have hh := one_le_of_L30 hL
  obtain ⟨-, ha, -, -⟩ := crossing_explicit hL (hLo h hh) (hUp h (ge32_of_L30 hL))
  have hN0 : (0 : ℝ) < 2 * (h : ℝ) := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  rw [Real.norm_of_nonneg
    (show (0 : ℝ) ≤ Real.log (2 * (h : ℝ)) ^ 2 / (2 * (h : ℝ)) by positivity), Real.norm_eq_abs]
  refine le_trans ha ?_
  unfold rhoN
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hN0]
  nlinarith

/-- **Theorem 2.7(b) (`thm:erw-crossing`):**
`x_N = 2 log N - log log N - log 16 + O(log log N / log N)` as `N = 2h → ∞`, given
Theorem 2.6. -/
theorem crossing_isBigO_expansion (hLo : CenterLowerBound) (hUp : CenterUpperBound) :
    (fun h : ℕ => crossingX h - (2 * Real.log (2 * (h : ℝ)) - Real.log (Real.log (2 * (h : ℝ)))
        - Real.log 16)) =O[atTop]
      (fun h : ℕ => Real.log (Real.log (2 * (h : ℝ))) / Real.log (2 * (h : ℝ))) := by
  refine IsBigO.of_bound 7 ?_
  filter_upwards [eventually_L30] with h hL
  have hh := one_le_of_L30 hL
  obtain ⟨-, -, -, hc⟩ := crossing_explicit hL (hLo h hh) (hUp h (ge32_of_L30 hL))
  set L := Real.log (2 * (h : ℝ))
  have hL0 : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have := Real.exp_one_lt_d9
    linarith
  rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ Real.log L / L from div_nonneg (by linarith) hL0.le),
    Real.norm_eq_abs]
  refine le_trans hc ?_
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hL0]
  linarith

end Kagey131.PaperD
