import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Paper F, Appendix B (track FL4): the gamma ratio, equation (9) (`eq:D-gamma`)

Gautschi's inequality (DLMF 5.6.4), `x^{1-s} ≤ Γ(x+1)/Γ(x+s) ≤ (x+1)^{1-s}` for `x > 0`,
`0 < s < 1`, is proved here from the log-convexity of `Γ` (Mathlib's
`Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma`), so it is not a hypothesis. (The source
has strict inequalities; the non-strict form suffices for the paper.)

From it, equation (9) (`eq:D-gamma`) of Paper F: for `0 < c < 2` and real `y ≥ 2`,
`Γ(y+1-c)/Γ(y+1) = y^{-c} (1 + ϑ)` with `-1/y ≤ ϑ ≤ 2/y` (`gamma_ratio`).
-/

namespace Kagey131.PaperD.FL4

open Real

/-- Gautschi's inequality, lower half, from log-convexity. -/
theorem gautschi_lower {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    x ^ (1 - s) ≤ Gamma (x + 1) / Gamma (x + s) := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x) (t := x + 1)
    (a := 1 - s) (b := s) hx (by linarith) (by linarith) hs0 (by ring)
  have e1 : (1 - s) * x + s * (x + 1) = x + s := by ring
  rw [e1] at h
  have hG : Gamma (x + 1) = x * Gamma x := Real.Gamma_add_one hx.ne'
  have hGx : 0 < Gamma x := Real.Gamma_pos_of_pos hx
  have hG1 : 0 < Gamma (x + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hGs : 0 < Gamma (x + s) := Real.Gamma_pos_of_pos (by linarith)
  -- Γ(x)^{1-s} Γ(x+1)^s = Γ(x+1) x^{s-1}
  have e2 : Gamma x ^ (1 - s) * Gamma (x + 1) ^ s = Gamma (x + 1) * x ^ (s - 1) := by
    have : Gamma x = Gamma (x + 1) * x ^ (-1 : ℝ) := by
      rw [hG, Real.rpow_neg_one]; field_simp
    rw [this, Real.mul_rpow hG1.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le,
      mul_assoc, mul_comm (x ^ _), ← mul_assoc, ← Real.rpow_add hG1, show 1 - s + s = 1 by ring,
      Real.rpow_one]
    congr 2; ring
  rw [e2] at h
  rw [le_div_iff₀ hGs]
  calc x ^ (1 - s) * Gamma (x + s) ≤ x ^ (1 - s) * (Gamma (x + 1) * x ^ (s - 1)) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le _)
    _ = Gamma (x + 1) * (x ^ (1 - s) * x ^ (s - 1)) := by ring
    _ = Gamma (x + 1) := by rw [← Real.rpow_add hx, show 1 - s + (s - 1) = 0 by ring,
          Real.rpow_zero, mul_one]

/-- Gautschi's inequality, upper half, from log-convexity. -/
theorem gautschi_upper {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    Gamma (x + 1) / Gamma (x + s) ≤ (x + 1) ^ (1 - s) := by
  have hxs : 0 < x + s := by linarith
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x + s) (t := x + s + 1)
    (a := s) (b := 1 - s) hxs (by linarith) hs0 (by linarith) (by ring)
  have e1 : s * (x + s) + (1 - s) * (x + s + 1) = x + 1 := by ring
  rw [e1] at h
  have hG : Gamma (x + s + 1) = (x + s) * Gamma (x + s) := Real.Gamma_add_one hxs.ne'
  have hGs : 0 < Gamma (x + s) := Real.Gamma_pos_of_pos hxs
  have e2 : Gamma (x + s) ^ s * Gamma (x + s + 1) ^ (1 - s) = Gamma (x + s) * (x + s) ^ (1 - s) := by
    rw [hG, Real.mul_rpow hxs.le hGs.le, mul_comm ((x + s) ^ (1 - s)), ← mul_assoc,
      ← Real.rpow_add hGs, show s + (1 - s) = 1 by ring, Real.rpow_one]
  rw [e2] at h
  rw [div_le_iff₀ hGs]
  calc Gamma (x + 1) ≤ Gamma (x + s) * (x + s) ^ (1 - s) := h
    _ ≤ Gamma (x + s) * (x + 1) ^ (1 - s) := by
        refine mul_le_mul_of_nonneg_left ?_ hGs.le
        exact Real.rpow_le_rpow hxs.le (by linarith) (by linarith)
    _ = (x + 1) ^ (1 - s) * Gamma (x + s) := by ring

/-- Paper F, equation (9) (`eq:D-gamma`): for `0 < c < 2` and `y ≥ 2`,
`y^{-c} (1 - 1/y) ≤ Γ(y+1-c)/Γ(y+1) ≤ y^{-c} (1 + 2/y)`, that is
`Γ(y+1-c)/Γ(y+1) = y^{-c}(1+ϑ)` with `-1/y ≤ ϑ ≤ 2/y`. -/
theorem gamma_ratio_bounds {c y : ℝ} (hc0 : 0 < c) (hc2 : c < 2) (hy : 2 ≤ y) :
    y ^ (-c) * (1 - 1 / y) ≤ Gamma (y + 1 - c) / Gamma (y + 1) ∧
      Gamma (y + 1 - c) / Gamma (y + 1) ≤ y ^ (-c) * (1 + 2 / y) := by
  have hy0 : 0 < y := by linarith
  have hG1 : 0 < Gamma (y + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hGc : 0 < Gamma (y + 1 - c) := Real.Gamma_pos_of_pos (by linarith)
  have hyc : 0 < y ^ (-c) := Real.rpow_pos_of_pos hy0 _
  have hy1 : 0 < 1 / y := by positivity
  have hy1' : 1 / y ≤ 1 / 2 := by rw [div_le_div_iff₀ hy0 (by norm_num)]; linarith
  rcases lt_trichotomy c 1 with hc1 | hc1 | hc1
  · -- `c < 1`: `s = 1 - c`
    have hl := gautschi_lower hy0 (s := 1 - c) (by linarith) (by linarith)
    have hu := gautschi_upper hy0 (s := 1 - c) (by linarith) (by linarith)
    rw [show y + (1 - c) = y + 1 - c by ring, show 1 - (1 - c) = c by ring] at hl hu
    -- ratio `R = Γ(y+1-c)/Γ(y+1)` lies in `[(y+1)^{-c}, y^{-c}]`
    have hR : Gamma (y + 1 - c) / Gamma (y + 1) = (Gamma (y + 1) / Gamma (y + 1 - c))⁻¹ := by
      rw [inv_div]
    have hyc' : 0 < y ^ c := Real.rpow_pos_of_pos hy0 _
    constructor
    · rw [hR]
      have h1 : (y + 1) ^ (-c) ≤ (Gamma (y + 1) / Gamma (y + 1 - c))⁻¹ := by
        rw [Real.rpow_neg (by linarith)]
        exact inv_anti₀ (Real.rpow_pos_of_pos hy0 _ |>.trans_le hl) hu
      refine le_trans ?_ h1
      -- `(y+1)^{-c} = y^{-c} (1 + 1/y)^{-c} ≥ y^{-c}(1 - c/y) ≥ y^{-c}(1 - 1/y)`
      have e : (y + 1) ^ (-c) = y ^ (-c) * (1 + 1 / y) ^ (-c) := by
        rw [← Real.mul_rpow hy0.le (by positivity)]; congr 1; field_simp
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ hyc.le
      have hb := rpow_one_add_le_one_add_mul_self (s := 1 / y) (by linarith) hc0.le hc1.le
      have hpos : 0 < (1 + 1 / y) ^ c := Real.rpow_pos_of_pos (by linarith) _
      rw [Real.rpow_neg (by positivity)]
      rw [le_inv_comm₀ (by nlinarith) hpos]
      calc (1 + 1 / y) ^ c ≤ 1 + c * (1 / y) := hb
        _ ≤ 1 + 1 / y := by nlinarith
        _ ≤ (1 - 1 / y)⁻¹ := by
          rw [le_inv_comm₀ (by linarith) (by linarith)]
          rw [inv_eq_one_div, le_div_iff₀ (by linarith)]
          nlinarith
    · rw [hR]
      have h1 : (Gamma (y + 1) / Gamma (y + 1 - c))⁻¹ ≤ y ^ (-c) := by
        rw [Real.rpow_neg hy0.le]
        exact inv_anti₀ hyc' hl
      calc _ ≤ y ^ (-c) := h1
        _ ≤ y ^ (-c) * (1 + 2 / y) := by
          have : 0 ≤ 2 / y := by positivity
          nlinarith
  · subst hc1
    have e : Gamma (y + 1 - 1) / Gamma (y + 1) = y ^ (-(1 : ℝ)) := by
      rw [show y + 1 - 1 = y by ring, Real.Gamma_add_one hy0.ne', Real.rpow_neg_one]
      have : Gamma y ≠ 0 := (Real.Gamma_pos_of_pos hy0).ne'
      field_simp
    rw [e]
    constructor
    · have : 0 ≤ 1 / y := by positivity
      nlinarith
    · have : 0 ≤ 2 / y := by positivity
      nlinarith
  · -- `c > 1`: `s = 2 - c`, `Γ(y+1-c) = Γ(y+2-c)/(y+1-c)`
    have hl := gautschi_lower hy0 (s := 2 - c) (by linarith) (by linarith)
    have hu := gautschi_upper hy0 (s := 2 - c) (by linarith) (by linarith)
    rw [show y + (2 - c) = y + 1 - c + 1 by ring, show 1 - (2 - c) = c - 1 by ring] at hl hu
    have hyc1 : 0 < y + 1 - c := by linarith
    have hG2 : Gamma (y + 1 - c + 1) = (y + 1 - c) * Gamma (y + 1 - c) :=
      Real.Gamma_add_one hyc1.ne'
    rw [hG2] at hl hu
    -- `R = 1 / ((y+1-c) Q)` with `Q = Γ(y+1)/((y+1-c)Γ(y+1-c))`
    set Q := Gamma (y + 1) / ((y + 1 - c) * Gamma (y + 1 - c)) with hQ
    have hR : Gamma (y + 1 - c) / Gamma (y + 1) = 1 / ((y + 1 - c) * Q) := by
      rw [hQ]; field_simp
    have hQpos : 0 < Q := by rw [hQ]; positivity
    rw [hR]
    have hyp : 0 < y ^ (c - 1) := Real.rpow_pos_of_pos hy0 _
    have hyp1 : 0 < (y + 1) ^ (c - 1) := Real.rpow_pos_of_pos (by linarith) _
    have eyc : y ^ (-c) = y ^ (-(c - 1)) / y := by
      rw [show -c = -(c - 1) - 1 by ring, Real.rpow_sub_one hy0.ne']
    constructor
    · -- lower: `1/((y+1-c)Q) ≥ (y+1)^{1-c}/(y+1-c) ≥ y^{-c}(1-1/y)`
      have h1 : (y + 1) ^ (-(c - 1)) / (y + 1 - c) ≤ 1 / ((y + 1 - c) * Q) := by
        rw [Real.rpow_neg (by linarith), div_le_div_iff₀ hyc1 (by positivity)]
        have : ((y + 1) ^ (c - 1))⁻¹ * ((y + 1 - c) * Q) ≤ 1 * (y + 1 - c) := by
          rw [one_mul, mul_comm (y + 1 - c), ← mul_assoc]
          refine mul_le_of_le_one_left hyc1.le ?_
          rw [inv_mul_le_iff₀ hyp1, mul_one]; exact hu
        linarith
      refine le_trans ?_ h1
      -- `(y+1)^{1-c} = y^{1-c} (1+1/y)^{1-c} ≥ y^{1-c} (1+1/y)^{-1}`
      have e : (y + 1) ^ (-(c - 1)) = y ^ (-(c - 1)) * (1 + 1 / y) ^ (-(c - 1)) := by
        rw [← Real.mul_rpow hy0.le (by positivity)]; congr 1; field_simp
      have hb : (1 + 1 / y) ^ (-(1 : ℝ)) ≤ (1 + 1 / y) ^ (-(c - 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      rw [Real.rpow_neg_one] at hb
      rw [e, eyc]
      have hyc0 : 0 < y ^ (-(c - 1)) := Real.rpow_pos_of_pos hy0 _
      have key : y ^ (-(c - 1)) / y * (1 - 1 / y) ≤
          y ^ (-(c - 1)) * (1 + 1 / y)⁻¹ / (y + 1 - c) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hy0 hyc1]
        have e2 : (1 + 1 / y)⁻¹ = y / (y + 1) := by field_simp
        rw [e2]
        have : y ^ (-(c - 1)) * (1 - 1 / y) * (y + 1 - c) ≤ y ^ (-(c - 1)) * (y / (y + 1)) * y := by
          rw [mul_assoc, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hyc0.le
          rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
          have : (1 - 1 / y) * y = y - 1 := by field_simp
          nlinarith
        linarith
      refine key.trans ?_
      rw [div_le_div_iff_of_pos_right hyc1]
      exact mul_le_mul_of_nonneg_left hb hyc0.le
    · -- upper: `1/((y+1-c)Q) ≤ y^{1-c}/(y+1-c) ≤ y^{-c}(1+2/y)`
      have h1 : 1 / ((y + 1 - c) * Q) ≤ y ^ (-(c - 1)) / (y + 1 - c) := by
        rw [Real.rpow_neg hy0.le, div_le_div_iff₀ (by positivity) hyc1]
        rw [one_mul, mul_comm (y + 1 - c), ← mul_assoc]
        have : 1 ≤ (y ^ (c - 1))⁻¹ * Q := by
          rw [le_inv_mul_iff₀ hyp, mul_one]; exact hl
        nlinarith
      refine h1.trans ?_
      rw [eyc]
      have hyc0 : 0 < y ^ (-(c - 1)) := Real.rpow_pos_of_pos hy0 _
      have e1 : y ^ (-(c - 1)) / (y + 1 - c) = y ^ (-(c - 1)) * (1 / (y + 1 - c)) := by ring
      have e2 : y ^ (-(c - 1)) / y * (1 + 2 / y) = y ^ (-(c - 1)) * ((1 + 2 / y) / y) := by ring
      rw [e1, e2]
      refine mul_le_mul_of_nonneg_left ?_ hyc0.le
      rw [div_le_div_iff₀ hyc1 hy0, one_mul]
      have h3 : y ≤ (1 + 2 / y) * (y + 1 - c) := by
        rw [← sub_nonneg]
        have : (1 + 2 / y) * (y + 1 - c) - y = ((1 - c) * y + 2 * (y + 1 - c)) / y := by
          field_simp; ring
        rw [this]
        apply div_nonneg _ hy0.le
        nlinarith
      exact h3

/-- Paper F, equation (9) (`eq:D-gamma`), in the paper's form. -/
theorem gamma_ratio {c y : ℝ} (hc0 : 0 < c) (hc2 : c < 2) (hy : 2 ≤ y) :
    ∃ θ : ℝ, Gamma (y + 1 - c) / Gamma (y + 1) = y ^ (-c) * (1 + θ) ∧ -1 / y ≤ θ ∧ θ ≤ 2 / y := by
  obtain ⟨h1, h2⟩ := gamma_ratio_bounds hc0 hc2 hy
  have hyc : 0 < y ^ (-c) := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨Gamma (y + 1 - c) / Gamma (y + 1) / y ^ (-c) - 1, ?_, ?_, ?_⟩
  · field_simp; ring
  · rw [le_sub_iff_add_le, le_div_iff₀ hyc]
    have : (-1 / y + 1) * y ^ (-c) = y ^ (-c) * (1 - 1 / y) := by ring
    linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hyc]
    have : (2 / y + 1) * y ^ (-c) = y ^ (-c) * (1 + 2 / y) := by ring
    linarith

end Kagey131.PaperD.FL4
