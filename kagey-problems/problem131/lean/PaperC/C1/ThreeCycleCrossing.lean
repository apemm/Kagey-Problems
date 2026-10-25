import Mathlib

/-!
# Paper C1: the arithmetic of `cor:reducible-crossing` on the directed 3-cycle

Paper C1 (`paperC/problem131_chains.tex`), `paperC/sec_firstorder.tex`, `cor:reducible-crossing`,
applied to `paperC/sec_secondorder.tex`, `ex:threecycle`: `d = 3`, `q_12 = b > 2`,
`q_23 = q_31 = 1`, `μ_1 = 1`.

The faces `{1}`, `{1,2}`, `{1,2,3}` have `k = 1, 2, 3`, `λ = b, 1, 0`, `p = 0, 1, 1`
(`ex:threecycle`; `λ_{1} = b` is the exit rate of state 1), and `K = 1, b, (1+2b)²/(2√3πb)`.

Proved here:

* `crossing_const_pair1`, `crossing_T_pair1`: for `F = {1,2}`, `G = {1}` the corollary has
  `Δ = 1`, `δ = b - 1`, `π = 1`, `κ = log b`, so the coefficient `π/Δ` of `log L` is `1`, and
  `b₀ = log((b-1)/b)` (the formula of part (ii) of the example);
* `crossing_const_pair2`, `crossing_T_pair2`: for `F = {1,2,3}`, `G = {1,2}` it has `Δ = 1`,
  `δ = 1`, `π = 0`, `κ = log(K_{123}/b)`, so the coefficient is `0` and
  `b₀ = log(2√3πb²/(1+2b)²)` (part (iii));
* `sup_A2`: `A_2 = sup_{t>0} b e^{(1-b)t} = b`;
* `stationary_cycle`: `α* = (1,b,b)/(1+2b)` is stationary for the generator;
* `hessian_det` and `K123_value`: the Hessian determinant `(1+2b)⁴/(3b²)` of `J_V` and
  `K_{123} = (2π)^{-1}(det Σ)^{-1/2} = (1+2b)²/(2√3πb)`;
* `log_ratio_deriv_pos`: the derivative in `h` of `log(M_{12}/M_{1})` is positive.
-/

namespace Kagey131.PaperC.C1

open Real Matrix

/-- The constant `b₀ = -(π/Δ) log(Δ/δ) - κ/Δ` of `cor:reducible-crossing`(iii). -/
noncomputable def crossB (pi Δ δ κ : ℝ) : ℝ := -(pi / Δ) * Real.log (Δ / δ) - κ / Δ

/-- The location `(Δ/δ)[L - (π/Δ) log L + b₀]`. -/
noncomputable def crossT (pi Δ δ κ L : ℝ) : ℝ :=
  Δ / δ * (L - pi / Δ * Real.log L + crossB pi Δ δ κ)

theorem crossing_const_pair1 {b : ℝ} (hb : 2 < b) :
    crossB 1 1 (b - 1) (Real.log b) = Real.log ((b - 1) / b) := by
  have h1 : 0 < b - 1 := by linarith
  have h2 : 0 < b := by linarith
  unfold crossB
  have e : Real.log (1 / (b - 1)) = -Real.log (b - 1) := by rw [one_div, Real.log_inv]
  rw [Real.log_div h1.ne' h2.ne', e]
  ring

theorem crossing_T_pair1 {b : ℝ} (hb : 2 < b) (L : ℝ) :
    crossT 1 1 (b - 1) (Real.log b) L
      = 1 / (b - 1) * (L - Real.log L + Real.log ((b - 1) / b)) := by
  unfold crossT
  rw [crossing_const_pair1 hb]
  ring

/-- `K_{123}` of `ex:threecycle`(i). -/
noncomputable def K123 (b : ℝ) : ℝ := (1 + 2 * b) ^ 2 / (2 * Real.sqrt 3 * Real.pi * b)

theorem crossing_const_pair2 {b : ℝ} (hb : 2 < b) :
    crossB 0 1 1 (Real.log (K123 b / b))
      = Real.log (2 * Real.sqrt 3 * Real.pi * b ^ 2 / (1 + 2 * b) ^ 2) := by
  have h2 : 0 < b := by linarith
  have h3 : 0 < Real.sqrt 3 := by positivity
  have hpi := Real.pi_pos
  unfold crossB K123
  have : (1 + 2 * b) ^ 2 / (2 * Real.sqrt 3 * Real.pi * b) / b
      = ((2 * Real.sqrt 3 * Real.pi * b ^ 2) / (1 + 2 * b) ^ 2)⁻¹ := by
    field_simp
  rw [this, Real.log_inv]
  simp

theorem crossing_T_pair2 {b : ℝ} (hb : 2 < b) (L : ℝ) :
    crossT 0 1 1 (Real.log (K123 b / b)) L
      = L + Real.log (2 * Real.sqrt 3 * Real.pi * b ^ 2 / (1 + 2 * b) ^ 2) := by
  unfold crossT
  rw [crossing_const_pair2 hb]
  simp

/-- The coefficients of `log L`: `π/Δ = 1` for the pair `({1,2},{1})` and `0` for
`({1,2,3},{1,2})`, with `π = p_F - p_G`. -/
theorem log_coefficients : ((1 : ℝ) - 0) / (2 - 1) = 1 ∧ ((1 : ℝ) - 1) / (3 - 2) = 0 := by
  norm_num

/-- `A_2 = sup_{t>0} b e^{(1-b)t} = b` for `b > 1` (the sup is not attained). -/
theorem sup_A2 {b : ℝ} (hb : 1 < b) :
    sSup {x : ℝ | ∃ t : ℝ, 0 < t ∧ x = b * Real.exp ((1 - b) * t)} = b := by
  have hb0 : 0 < b := by linarith
  apply le_antisymm
  · refine csSup_le ⟨_, 1, one_pos, rfl⟩ ?_
    rintro x ⟨t, ht, rfl⟩
    have : Real.exp ((1 - b) * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    nlinarith
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    -- choose t small so that b e^{(1-b)t} > b - ε
    have hcont : ∃ t : ℝ, 0 < t ∧ b - ε < b * Real.exp ((1 - b) * t) := by
      have h1 : Filter.Tendsto (fun t : ℝ => b * Real.exp ((1 - b) * t)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (b * Real.exp ((1 - b) * 0))) :=
        (((continuous_const.mul (by fun_prop : Continuous fun t : ℝ => Real.exp ((1 - b) * t)))
          |>.tendsto 0)).mono_left nhdsWithin_le_nhds
      simp only [mul_zero, Real.exp_zero, mul_one] at h1
      have h2 := (h1.eventually (lt_mem_nhds (show b - ε < b by linarith)))
      obtain ⟨t, ht1, ht2⟩ := (h2.and self_mem_nhdsWithin).exists
      exact ⟨t, ht2, ht1⟩
    obtain ⟨t, ht, hlt⟩ := hcont
    have hbdd : BddAbove {x : ℝ | ∃ t : ℝ, 0 < t ∧ x = b * Real.exp ((1 - b) * t)} := by
      refine ⟨b, ?_⟩
      rintro x ⟨s, hs, rfl⟩
      have : Real.exp ((1 - b) * s) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      nlinarith
    have := le_csSup hbdd ⟨t, ht, rfl⟩
    linarith

/-- The generator of `ex:threecycle` and `α* = (1, b, b)/(1 + 2b)`: `α* Q = 0`. -/
theorem stationary_cycle {b : ℝ} (hb : 0 < b) :
    let Q : Matrix (Fin 3) (Fin 3) ℝ := !![-b, b, 0; 0, -1, 1; 1, 0, -1]
    let α : Fin 3 → ℝ := ![1 / (1 + 2 * b), b / (1 + 2 * b), b / (1 + 2 * b)]
    α ᵥ* Q = 0 ∧ ∑ i, α i = 1 := by
  intro Q α
  have h : (1 + 2 * b) ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · ext j
    fin_cases j <;> simp [Q, α, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> field_simp <;> ring
  · simp [α, Fin.sum_univ_three]; field_simp; ring

/-- The Hessian of `J_V` in `(α_2, α_3)` at `α*` and its determinant `(1+2b)⁴/(3b²)`
(`ex:threecycle`(i)). -/
theorem hessian_det {b : ℝ} (hb : 0 < b) :
    (!![(1 + 2 * b) / (3 * b) * (2 * b ^ 2 + 2 * b + 2),
        (1 + 2 * b) / (3 * b) * (2 * b ^ 2 + 2 * b - 1);
        (1 + 2 * b) / (3 * b) * (2 * b ^ 2 + 2 * b - 1),
        (1 + 2 * b) / (3 * b) * (2 * b ^ 2 + 2 * b + 2)] : Matrix (Fin 2) (Fin 2) ℝ).det
      = (1 + 2 * b) ^ 4 / (3 * b ^ 2) := by
  rw [Matrix.det_fin_two_of]
  field_simp
  ring

/-- `K_{123} = (2π)^{-1} (det Σ)^{-1/2}` with `det Σ = 3b²/(1+2b)⁴`. -/
theorem K123_value {b : ℝ} (hb : 0 < b) :
    (2 * Real.pi)⁻¹ * (Real.sqrt (3 * b ^ 2 / (1 + 2 * b) ^ 4))⁻¹ = K123 b := by
  have hpi := Real.pi_pos
  have h3 : 0 < Real.sqrt 3 := by positivity
  have e : Real.sqrt (3 * b ^ 2 / (1 + 2 * b) ^ 4) = Real.sqrt 3 * b / (1 + 2 * b) ^ 2 := by
    rw [show 3 * b ^ 2 / (1 + 2 * b) ^ 4 = 3 * (b / (1 + 2 * b) ^ 2) ^ 2 by field_simp,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
    ring
  rw [e]
  unfold K123
  field_simp

/-- The derivative in `h` of `log(M_{12}/M_1) = log(bh) + (N-2)log(1-h) - (N-1)log(1-bh)` is
positive for `b > 1`, `N ≥ 2`, `0 < h` and `bh < 1`. -/
theorem log_ratio_deriv_pos {b h : ℝ} (N : ℕ) (hb : 1 < b) (hN : 2 ≤ N) (hh : 0 < h)
    (hbh : b * h < 1) :
    0 < 1 / h - ((N : ℝ) - 2) / (1 - h) + ((N : ℝ) - 1) * b / (1 - b * h) := by
  have h1 : 0 < 1 - b * h := by linarith
  have h2 : 1 - b * h < 1 - h := by nlinarith
  have h3 : 0 < 1 - h := by linarith
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h4 : ((N : ℝ) - 1) / (1 - h) ≤ ((N : ℝ) - 1) * b / (1 - b * h) := by
    rw [div_le_div_iff₀ h3 h1]; nlinarith
  have h5 : ((N : ℝ) - 1) / (1 - h) = ((N : ℝ) - 2) / (1 - h) + 1 / (1 - h) := by
    field_simp; ring
  have h6 : 0 < 1 / h := by positivity
  have h7 : 0 < 1 / (1 - h) := by positivity
  linarith

end Kagey131.PaperC.C1
