import Mathlib

/-!
# Paper C1: the cubic coefficient for the non-reversible 3-cycle

Paper C1 (`paperC/problem131_chains.tex`), `paperC/sec_boundary.tex`, `prop:layer-cubic`(e).
For the cycle with `q_12 = q_23 = q_31 = 2`, `q_21 = q_32 = q_13 = 1`, `i = 3`, `β = (1/2, 1/2)`,
the weighted two-state chain on `G = {1, 2}` has `d(z) = (3 - 2z)·1`, `a_12(z) = 2 + z`,
`a_21(z) = 1 + 4z`, and (Lemma `lem:L-two`) the rate
`J_G(β, z) = 3 - 2z - √((2 + z)(1 + 4z))`, here `cycleJ` (note `(2+z)(1+4z) = 4z² + 9z + 2`).

Proved here, with `ω = 2 + (9/4)√2`:

* `cycleJ_d1`, `cycleJ_d2`, `cycleJ_d3`: `∂_z J_G(β,0) = -ω`,
  `∂_z² J_G(β,0) = (49/16)√2`, `∂_z³ J_G(β,0) = -(1323/64)√2`;
* `cycle_cubic_identity`: with `a = ½ ∂_z² J_G(β,0)` and `c = (1/6) ∂_z³ J_G(β,0)`,
  `c ω + a² = -(49/64) ω²`, that is `c + a²/ω = -(49/64) ω`;
* `cycle_kappa`: `ϰ_β = c ω^{-3/2} + a² ω^{-5/2} = -49/(64 √ω)`, so `ϰ_β < 0`.
-/

namespace Kagey131.PaperC.C1

open Real

/-- `√((2 + z)(1 + 4z))`, written as `√(4z² + 9z + 2)`. -/
noncomputable def cycleG (z : ℝ) : ℝ := Real.sqrt (4 * z ^ 2 + 9 * z + 2)

/-- The rate `J_G(β, z) = 3 - 2z - √((2 + z)(1 + 4z))` of the weighted chain on the facet. -/
noncomputable def cycleJ (z : ℝ) : ℝ := 3 - 2 * z - cycleG z

theorem cycleJ_eq (z : ℝ) : cycleJ z = 3 - 2 * z - Real.sqrt ((2 + z) * (1 + 4 * z)) := by
  unfold cycleJ cycleG; congr 2; ring

/-- The open set where the radicand is positive contains `0`. -/
def Pos (z : ℝ) : Prop := 0 < 4 * z ^ 2 + 9 * z + 2

theorem Pos_zero : Pos 0 := by unfold Pos; norm_num

theorem Pos_open : IsOpen {z : ℝ | Pos z} :=
  isOpen_lt continuous_const (by fun_prop)

theorem cycleG_sq {z : ℝ} (hz : Pos z) : cycleG z ^ 2 = 4 * z ^ 2 + 9 * z + 2 :=
  Real.sq_sqrt hz.le

theorem cycleG_pos {z : ℝ} (hz : Pos z) : 0 < cycleG z := Real.sqrt_pos.mpr hz

theorem hasDeriv_cycleG {z : ℝ} (hz : Pos z) :
    HasDerivAt cycleG ((9 + 8 * z) / (2 * cycleG z)) z := by
  have h := (((hasDerivAt_pow 2 z).const_mul 4).add ((hasDerivAt_id z).const_mul 9)).add_const 2
  have e : (9 + 8 * z) = 4 * ((2:ℕ) * z ^ (2 - 1)) + 9 * 1 := by norm_num; ring
  rw [e]
  exact h.sqrt hz.ne'

/-- First derivative: `-2 - (9 + 8z)/(2G)`. -/
noncomputable def cycleD1 (z : ℝ) : ℝ := -2 - (9 + 8 * z) / (2 * cycleG z)

/-- Second derivative: `49/(4G³)`. -/
noncomputable def cycleD2 (z : ℝ) : ℝ := 49 / (4 * cycleG z ^ 3)

/-- Third derivative: `-(147/8)(9 + 8z)/G⁵`. -/
noncomputable def cycleD3 (z : ℝ) : ℝ := -(147 / 8) * (9 + 8 * z) / cycleG z ^ 5

theorem hasDeriv_J {z : ℝ} (hz : Pos z) : HasDerivAt cycleJ (cycleD1 z) z := by
  have h := (((hasDerivAt_id z).const_mul 2).const_sub 3).sub (hasDeriv_cycleG hz)
  exact h.congr_deriv (by unfold cycleD1; simp)

theorem hasDeriv_D1 {z : ℝ} (hz : Pos z) : HasDerivAt cycleD1 (cycleD2 z) z := by
  have hg := hasDeriv_cycleG hz
  have hp := cycleG_pos hz
  have hne := hp.ne'
  have hsq := cycleG_sq hz
  have h8 : HasDerivAt (fun z : ℝ => 9 + 8 * z) 8 z := by
    simpa using ((hasDerivAt_id z).const_mul 8).const_add 9
  have h := (hasDerivAt_const z (-2 : ℝ)).sub (h8.div (hg.const_mul 2) (mul_pos two_pos hp).ne')
  have e : cycleD1 = (fun _ => (-2 : ℝ)) - (fun z : ℝ => 9 + 8 * z) / fun y => 2 * cycleG y := by
    funext w; simp [cycleD1]
  rw [e]
  refine h.congr_deriv ?_
  unfold cycleD2
  field_simp
  nlinarith [hsq]

theorem hasDeriv_D2 {z : ℝ} (hz : Pos z) : HasDerivAt cycleD2 (cycleD3 z) z := by
  have hg := hasDeriv_cycleG hz
  have hp := cycleG_pos hz
  have hne := hp.ne'
  have h := (hasDerivAt_const z (49 : ℝ)).div ((hg.pow 3).const_mul 4)
    (mul_pos (by norm_num) (pow_pos hp 3)).ne'
  have e : cycleD2 = (fun _ => (49 : ℝ)) / fun y => 4 * cycleG y ^ 3 := by
    funext w; simp [cycleD2]
  rw [e]
  refine h.congr_deriv ?_
  unfold cycleD3
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem cycleG_zero : cycleG 0 = Real.sqrt 2 := by unfold cycleG; norm_num

/-- `ω_β = 2 + (9/4)√2`. -/
noncomputable def cycleOmega : ℝ := 2 + 9 / 4 * Real.sqrt 2

theorem deriv_J_eventually : deriv cycleJ =ᶠ[nhds 0] cycleD1 :=
  Filter.eventuallyEq_of_mem (Pos_open.mem_nhds Pos_zero) fun _ hz => (hasDeriv_J hz).deriv

theorem deriv_D1_eventually : deriv cycleD1 =ᶠ[nhds 0] cycleD2 :=
  Filter.eventuallyEq_of_mem (Pos_open.mem_nhds Pos_zero) fun _ hz => (hasDeriv_D1 hz).deriv

theorem deriv_D2_eventually : deriv cycleD2 =ᶠ[nhds 0] cycleD3 :=
  Filter.eventuallyEq_of_mem (Pos_open.mem_nhds Pos_zero) fun _ hz => (hasDeriv_D2 hz).deriv

theorem s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem s6 : Real.sqrt 2 ^ 6 = 8 := by
  calc Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := by ring
    _ = 8 := by rw [s2]; norm_num

/-- `∂_z J_G(β, 0) = -ω_β`. -/
theorem cycleJ_d1 : deriv cycleJ 0 = -cycleOmega := by
  rw [(hasDeriv_J Pos_zero).deriv, cycleD1, cycleG_zero, cycleOmega]
  have hs : 0 < Real.sqrt 2 := by positivity
  field_simp
  nlinarith [s2, s6]

/-- `∂_z² J_G(β, 0) = (49/16)√2`. -/
theorem cycleJ_d2 : deriv (deriv cycleJ) 0 = 49 / 16 * Real.sqrt 2 := by
  rw [deriv_J_eventually.deriv_eq, (hasDeriv_D1 Pos_zero).deriv, cycleD2, cycleG_zero]
  have hs : 0 < Real.sqrt 2 := by positivity
  field_simp
  nlinarith [s2, s6]

theorem deriv_deriv_J {z : ℝ} (hz : Pos z) : deriv (deriv cycleJ) z = cycleD2 z := by
  have : deriv cycleJ =ᶠ[nhds z] cycleD1 :=
    Filter.eventuallyEq_of_mem (Pos_open.mem_nhds hz) fun _ hw => (hasDeriv_J hw).deriv
  rw [this.deriv_eq, (hasDeriv_D1 hz).deriv]

/-- `∂_z³ J_G(β, 0) = -(1323/64)√2`. -/
theorem cycleJ_d3 : deriv (deriv (deriv cycleJ)) 0 = -(1323 / 64) * Real.sqrt 2 := by
  have : deriv (deriv cycleJ) =ᶠ[nhds 0] cycleD2 :=
    Filter.eventuallyEq_of_mem (Pos_open.mem_nhds Pos_zero) fun _ hw => deriv_deriv_J hw
  rw [this.deriv_eq, (hasDeriv_D2 Pos_zero).deriv, cycleD3, cycleG_zero]
  have hs : 0 < Real.sqrt 2 := by positivity
  field_simp
  nlinarith [s2, s6]

/-- `prop:layer-cubic`(e): with `a = ½ ∂_z² J_G(β,0)`, `c = (1/6) ∂_z³ J_G(β,0)` and `ω = ω_β`,
`c ω + a² = -(49/64) ω²`, that is, `c + a²/ω = -(49/64) ω`. -/
theorem cycle_cubic_identity :
    (deriv (deriv (deriv cycleJ)) 0 / 6) * cycleOmega + (deriv (deriv cycleJ) 0 / 2) ^ 2
      = -(49 / 64) * cycleOmega ^ 2 := by
  rw [cycleJ_d3, cycleJ_d2, cycleOmega]
  linear_combination (-49 / 32) * s2

/-- `prop:layer-cubic`(e): `ϰ_β = c ω^{-3/2} + a² ω^{-5/2} = -49/(64 √ω)`, in the form without
real powers: `c/(ω√ω) + a²/(ω²√ω) = -49/(64√ω)`. Hence `ϰ_β < 0`. -/
theorem cycle_kappa :
    (deriv (deriv (deriv cycleJ)) 0 / 6) / (cycleOmega * Real.sqrt cycleOmega)
        + (deriv (deriv cycleJ) 0 / 2) ^ 2 / (cycleOmega ^ 2 * Real.sqrt cycleOmega)
      = -49 / (64 * Real.sqrt cycleOmega) := by
  have hω : 0 < cycleOmega := by unfold cycleOmega; positivity
  have hr : 0 < Real.sqrt cycleOmega := Real.sqrt_pos.mpr hω
  have key := cycle_cubic_identity
  have hωne := hω.ne'
  have hrne := hr.ne'
  generalize deriv (deriv (deriv cycleJ)) 0 = c3 at *
  generalize deriv (deriv cycleJ) 0 = c2 at *
  have e : c3 / 6 / (cycleOmega * Real.sqrt cycleOmega) + (c2 / 2) ^ 2 / (cycleOmega ^ 2 * Real.sqrt cycleOmega)
      = (c3 / 6 * cycleOmega + (c2 / 2) ^ 2) / (cycleOmega ^ 2 * Real.sqrt cycleOmega) := by
    field_simp
  rw [e, key]
  field_simp

theorem cycle_kappa_neg : -49 / (64 * Real.sqrt cycleOmega) < 0 := by
  have hω : 0 < cycleOmega := by unfold cycleOmega; positivity
  have hr : 0 < Real.sqrt cycleOmega := Real.sqrt_pos.mpr hω
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

end Kagey131.PaperC.C1
