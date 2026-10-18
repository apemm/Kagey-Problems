import PaperD.U5_Profile

/-!
# Theorem S2.1 (`thm:profile`): the sequence form is not vacuous

`thm_profile_witness` applies `thm_profile` to the concrete family `N = 2h`, `ε_h = 1/N`
(so `x = 1`), `ω_h = √h`, `δ'_h = 1/√h`, checks every hypothesis, and shows that the range
`ω_h x log²(x+1) ≤ m ≤ δ'_h N` contains `m = ⌈√h⌉` for every `h ≥ 1`. So the conclusion of
`thm_profile` is used at genuine bins `m → ∞`.
-/

namespace Kagey131.PaperD

open Finset RRT Filter Topology

/-- The doubled index `h ↦ 2h` tends to infinity. -/
theorem tendsto_two_mul_nat : Tendsto (fun h : ℕ => ((2 * h : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun h => (by omega : h ≤ 2 * h)) tendsto_id)

/-- **Theorem S2.1, non-vacuity.** For `ε_h = 1/(2h)` (so `x = 1`) and every `η > 0`,
eventually in `h` there is a bin `m` with `√h ≤ m ≤ 2√h` at which both profile bounds of
`thm_profile` hold. -/
theorem thm_profile_witness {η : ℝ} (hη : 0 < η) :
    ∀ᶠ h : ℕ in atTop, ∃ m : ℕ, Real.sqrt h ≤ m ∧ (m : ℝ) ≤ 2 * Real.sqrt h ∧
      |law (1 / ((2 * h : ℕ) : ℝ)) (2 * h) m * ((m : ℝ) * ((m : ℝ) + 1)) /
          (((2 * h : ℕ) : ℝ) * (1 / ((2 * h : ℕ) : ℝ))) - 1| ≤ η ∧
        |ewBin (1 / ((2 * h : ℕ) : ℝ)) (2 * h) (2 * h - m) * (2 * (m : ℝ) ^ 2) /
          (((2 * h : ℕ) : ℝ) * (1 / ((2 * h : ℕ) : ℝ))) - 1| ≤ η := by
  set ε : ℕ → ℝ := fun h => 1 / ((2 * h : ℕ) : ℝ) with hεdef
  have hx1 : ∀ h : ℕ, 1 ≤ h → ((2 * h : ℕ) : ℝ) * ε h = 1 := by
    intro h hh
    have : (0 : ℝ) < ((2 * h : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * h)
    simp only [hεdef]; field_simp
  have hε0 : ∀ᶠ h in atTop, 0 < ε h := by
    filter_upwards [eventually_ge_atTop 1] with h hh
    have : (0 : ℝ) < ((2 * h : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * h)
    simp only [hεdef]; positivity
  have hx : ∀ᶠ h in atTop, 1 ≤ ((2 * h : ℕ) : ℝ) * ε h := by
    filter_upwards [eventually_ge_atTop 1] with h hh
    rw [hx1 h hh]
  have hlim : Tendsto (fun h : ℕ => ((2 * h : ℕ) : ℝ) * ε h * Real.log ((2 * h : ℕ) : ℝ) ^ 2 /
      ((2 * h : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp tendsto_two_mul_nat
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with h hh
    simp only [Function.comp, one_mul, add_zero]
    rw [hx1 h hh, one_mul]
  have hω : Tendsto (fun h : ℕ => Real.sqrt h) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hδ' : Tendsto (fun h : ℕ => 1 / Real.sqrt h) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp hω
    refine this.congr (fun h => ?_)
    simp [Function.comp]
  have hP := thm_profile ε (fun h => Real.sqrt h) (fun h => 1 / Real.sqrt h) hε0 hx hlim hω hδ' hη
  filter_upwards [hP, eventually_ge_atTop 1] with h hPh hh
  have hs1 : (1 : ℝ) ≤ Real.sqrt h := by
    rw [Real.one_le_sqrt]; exact_mod_cast hh
  have hs0 : (0 : ℝ) < Real.sqrt h := by linarith
  refine ⟨⌈Real.sqrt h⌉₊, Nat.le_ceil _, ?_, ?_⟩
  · have := Nat.ceil_lt_add_one hs0.le
    linarith
  · apply hPh
    · rw [hx1 h hh, mul_one]
      have hl0 : 0 ≤ Real.log (1 + 1) := Real.log_nonneg (by norm_num)
      have hl1 : Real.log (1 + 1) ≤ 1 := by
        have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
      have hsq : Real.log (1 + 1) ^ 2 ≤ 1 := by nlinarith
      calc Real.sqrt h * Real.log (1 + 1) ^ 2 ≤ Real.sqrt h * 1 :=
            mul_le_mul_of_nonneg_left hsq hs0.le
        _ = Real.sqrt h := mul_one _
        _ ≤ _ := Nat.le_ceil _
    · have hc := Nat.ceil_lt_add_one hs0.le
      have hN : ((2 * h : ℕ) : ℝ) = 2 * (Real.sqrt h * Real.sqrt h) := by
        rw [Real.mul_self_sqrt (Nat.cast_nonneg h)]; push_cast; ring
      rw [hN]
      have e : 1 / Real.sqrt h * (2 * (Real.sqrt h * Real.sqrt h)) = 2 * Real.sqrt h := by
        field_simp
      rw [e]; linarith

end Kagey131.PaperD
