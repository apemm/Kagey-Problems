import PaperA.UniformBessel
import PaperA.BesselDeriv

/-!
# Paper A: comparing the exact crossings with the Bessel roots

* Corollary `cor:allbin-root-bound`: with `s = √(ab)`, `A = ab/(a+b)`, `η = 2√(ab)/(a+b)`,
  `x_{a,b} = s u_{a,b}` and `x_B` the root of `G_η(x_B) = A`, we have `x_{a,b} ≥ x_B`, and
  if `δ_{a,b} = x_{a,b}²/(2A) + x_{a,b}/s < 1` then `x_{a,b} - x_B ≤ -(1/2) log(1 - δ_{a,b})`.
* Theorem `thm:bessel` (ii): with `h = N/2`, `x_N = h u_N`,
  `x_B` the root of `F(x_B) = h`, and `δ_N = x_N(x_N+1)/h`, we have `0 ≤ x_N - x_B`, and
  `x_N - x_B ≤ -(1/2) log(1 - δ_N)` when `δ_N < 1`; dividing by `h` gives `0 ≤ u_N - u_B`.

This Lean verification code was generated with Claude Opus 5.5.
-/

namespace Kagey131

open Finset

theorem eta_le_one (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    0 ≤ 2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b) ∧
      2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b) ≤ 1 := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hs0 : 0 ≤ Real.sqrt ((a : ℝ) * b) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt ((a : ℝ) * b) ^ 2 = (a : ℝ) * b := Real.sq_sqrt (by positivity)
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg ((a : ℝ) - b), sq_nonneg (2 * Real.sqrt ((a : ℝ) * b) - (a + b))]

/-- `T_{a,b}(u) = G_η(su)/A`. -/
theorem Tab_eq_Geta (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (u : ℝ) :
    Tab a b u = Geta (2 * Real.sqrt ((a : ℝ) * b) / ((a : ℝ) + b)) (Real.sqrt ((a : ℝ) * b) * u) /
      ((a : ℝ) * b / (a + b)) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  unfold Tab Jc Geta
  set s := Real.sqrt ((a : ℝ) * b)
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = (a : ℝ) * b := Real.sq_sqrt (by positivity)
  rw [← hs2]
  field_simp
  ring

/-- Corollary `cor:allbin-root-bound`. -/
theorem allbin_root_bound (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    let s := Real.sqrt ((a : ℝ) * b)
    let A := (a : ℝ) * b / (a + b)
    let η := 2 * s / ((a : ℝ) + b)
    let x := s * uab a b
    let δ := x ^ 2 / (2 * A) + x / s
    Groot η A ≤ x ∧ (δ < 1 → x - Groot η A ≤ -(1 / 2) * Real.log (1 - δ)) := by
  intro s A η x δ
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hA : 0 < A := by positivity
  have hu := uab_pos ha hb
  have hx : 0 < x := by positivity
  obtain ⟨hη0, hη1⟩ := eta_le_one a b ha hb
  obtain ⟨hlow, hup⟩ := allbin_bessel a b ha hb hu
  rw [Sab_uab ha hb] at hlow hup
  have hδ : ((a : ℝ) + b) * uab a b ^ 2 / 2 + uab a b = δ := (allbin_bound_eq a b ha hb (uab a b)).symm
  rw [hδ] at hup
  have hT : Tab a b (uab a b) = Geta η x / A := Tab_eq_Geta a b ha hb (uab a b)
  have hG : 0 < Geta η x := Geta_pos hη0 hx
  have hTpos : 0 < Tab a b (uab a b) := by rw [hT]; positivity
  have hGT : Geta η x = A * Tab a b (uab a b) := by
    rw [hT]; field_simp
  have hT1 : 1 ≤ Tab a b (uab a b) := by
    rw [sub_nonneg, div_le_one hTpos] at hlow; exact hlow
  have hlowG : A ≤ Geta η x := by rw [hGT]; nlinarith
  obtain ⟨hle, hbound⟩ := root_comparison hη0 hη1 hA hx hlowG
  refine ⟨hle, fun hδ1 => hbound δ hδ1 ?_⟩
  have h1δ : 0 < 1 - δ := by linarith
  have : 1 - δ ≤ 1 / Tab a b (uab a b) := by linarith
  rw [le_div_iff₀ hTpos] at this
  rw [hGT, le_div_iff₀ h1δ]
  nlinarith

/-- `F(x) = 2 G_1(x)`. -/
theorem Fcent_eq (x : ℝ) : Fcent x = 2 * Geta 1 x := by
  unfold Fcent Geta; ring

/-- Theorem `thm:bessel`, second part: with `h = N/2`, `x_N = h u_N`, `x_B` the positive root
of `F(x_B) = h` and `δ_N = x_N(x_N+1)/h`: `x_B ≤ x_N`, and `x_N - x_B ≤ -(1/2) log(1-δ_N)`
whenever `δ_N < 1`. -/
theorem central_root_bound (N : ℕ) (hN : 2 ≤ N) :
    let h : ℝ := N / 2
    let xN := h * uN N
    let xB := Groot 1 (h / 2)
    let δ := xN * (xN + 1) / h
    Fcent xB = h ∧ xB ≤ xN ∧ (δ < 1 → xN - xB ≤ -(1 / 2) * Real.log (1 - δ)) := by
  intro h xN xB δ
  have hh : 0 < h := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    simp only [h]; linarith
  have hu : 0 < uN N := uab_pos (by omega) (by omega)
  have hx : 0 < xN := by positivity
  obtain ⟨hB0, hB⟩ := Groot_spec (η := 1) zero_le_one (show 0 < h / 2 by positivity)
  have hFB : Fcent xB = h := by rw [Fcent_eq, hB]; ring
  obtain ⟨hlow, hup⟩ := uniform_bessel_central N hN hx
  have hS : SN N (xN / ((N : ℝ) / 2)) = 1 := by
    have : xN / ((N : ℝ) / 2) = uN N := by
      simp only [xN, h]; field_simp
    rw [this]
    exact Sab_uab (by omega) (by omega)
  rw [hS, mul_one] at hlow hup
  have hF : 0 < Fcent xN := by rw [Fcent_eq]; have := Geta_pos zero_le_one hx; linarith
  have hlowG : h / 2 ≤ Geta 1 xN := by
    rw [sub_nonneg, div_le_one hF] at hlow
    rw [Fcent_eq] at hlow
    simp only [h] at hlow ⊢
    linarith
  obtain ⟨hle, hbound⟩ := root_comparison zero_le_one le_rfl (show 0 < h / 2 by positivity) hx hlowG
  refine ⟨hFB, hle, fun hδ1 => hbound δ hδ1 ?_⟩
  have h1δ : 0 < 1 - δ := by linarith
  have hδ' : xN * (xN + 1) / ((N : ℝ) / 2) = δ := rfl
  rw [hδ'] at hup
  have : 1 - δ ≤ (N : ℝ) / 2 / Fcent xN := by linarith
  rw [le_div_iff₀ hF] at this
  rw [le_div_iff₀ h1δ]
  rw [Fcent_eq] at this
  simp only [h] at this ⊢
  nlinarith

end Kagey131
