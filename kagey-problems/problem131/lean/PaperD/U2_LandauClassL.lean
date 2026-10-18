import PaperD.U2_LandauLocal

/-!
# Paper D, Appendix C.2: `e^B` as a limit of characteristic functions, and its class-`L` identity

* `bulkAB` (equation (C.1), `eq:bulk-AB`): for `x ≥ 1` and `|t| ≤ πx`,
  `‖x Ψ_∞(t/x) - i t log x - B(t)‖ ≤ (t²/x)(0.631(|log|t|| + log x) + 1.53)`.
* `tendsto_cf_landau` : hence, for every real `t`, the characteristic function
  `e^{xΨ_∞(t/x) - it log x}` of `(S_x - x log x)/x` (`S_x ~ CP_∞` with parameter `x`) tends to
  `e^{B(t)}` as `x → ∞`. (Lévy's continuity theorem then makes `e^B` a characteristic function; that
  classical step is part of `LandauDensityHyp` in `U2_LandauLaw`.)
* `landauB_mul` : `B(ct) = cB(t) - ict log c` for `c > 0`.
* `exp_landauB_classL` : for `0 < c < 1`,
  `e^{B(t)} = e^{B(ct)} · e^{B((1-c)t)} · e^{it[(1-c)log(1-c) + c log c]}` (the self-decomposability
  identity of Appendix C.2).
-/

namespace Kagey131.PaperD.U2

open Complex Finset Filter Topology
open scoped Real

noncomputable section

/-- **Equation (C.1)** (`eq:bulk-AB`): for `x ≥ 1` and `|t| ≤ πx`,
`x Ψ_∞(t/x) - i t log x = B(t) + x R(t/x)` with
`|x R(t/x)| ≤ (t²/x)(0.631(|log|t|| + log x) + 1.53)`. (The paper also allows `t = 0`
trivially; we state it for all `t` with `|t| ≤ πx`.) -/
theorem bulkAB {x t : ℝ} (hx : 1 ≤ x) (ht : |t| ≤ π * x) :
    ‖(x : ℂ) * psiInf (t / x) - (t : ℂ) * I * (Real.log x : ℂ) - landauB t‖
      ≤ t ^ 2 / x * (0.631 * (|Real.log (|t|)| + Real.log x) + 1.53) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set θ := t / x with hθ
  have hθπ : |θ| ≤ π := by
    rw [hθ, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]; exact ht
  have hsplit : (x : ℂ) * psiInf θ - (t : ℂ) * I * (Real.log x : ℂ) - landauB t
      = (x : ℂ) * (psiInf θ - landauB θ) := by
    have := landauB_scale hx0 t
    rw [← hθ] at this
    linear_combination this
  rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  rcases eq_or_ne t 0 with h0 | h0
  · have : θ = 0 := by rw [hθ, h0, zero_div]
    rw [this]
    have hp : psiInf 0 = 0 := by unfold psiInf psiTerm; simp
    have hb : landauB 0 = 0 := by unfold landauB; simp
    rw [hp, hb, sub_zero, norm_zero, mul_zero, h0]
    simp
  have hθ0 : θ ≠ 0 := by rw [hθ]; exact div_ne_zero h0 hx0.ne'
  have hf := fact2_B hθ0 hθπ
  have hlog : |Real.log (|θ|)| ≤ |Real.log (|t|)| + Real.log x := by
    rw [hθ, abs_div, abs_of_pos hx0, Real.log_div (abs_pos.mpr h0).ne' hx0.ne']
    calc |Real.log (|t|) - Real.log x| ≤ |Real.log (|t|)| + |Real.log x| := abs_sub _ _
      _ = |Real.log (|t|)| + Real.log x := by rw [abs_of_nonneg hlx]
  calc x * ‖psiInf θ - landauB θ‖
      ≤ x * (θ ^ 2 * (0.631 * |Real.log (|θ|)| + 1.53)) := by gcongr
    _ ≤ x * (θ ^ 2 * (0.631 * (|Real.log (|t|)| + Real.log x) + 1.53)) := by gcongr
    _ = t ^ 2 / x * (0.631 * (|Real.log (|t|)| + Real.log x) + 1.53) := by
        rw [hθ]; field_simp

/-- For every real `t`, `e^{xΨ_∞(t/x) - it log x} → e^{B(t)}` as `x → ∞` (Appendix C.2; the
characteristic function of `(S_x - x log x)/x` tends to `e^{B}`). -/
theorem tendsto_cf_landau (t : ℝ) :
    Tendsto (fun x : ℝ => cexp ((x : ℂ) * psiInf (t / x) - (t : ℂ) * I * (Real.log x : ℂ)))
      atTop (𝓝 (cexp (landauB t))) := by
  have hpi := Real.pi_pos
  -- the exponent converges
  have hexp : Tendsto (fun x : ℝ => (x : ℂ) * psiInf (t / x) - (t : ℂ) * I * (Real.log x : ℂ))
      atTop (𝓝 (landauB t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    set c : ℝ := t ^ 2 * (0.631 * |Real.log (|t|)| + 1.53) with hc
    have hb : Tendsto (fun x : ℝ => c * x⁻¹ + 0.631 * t ^ 2 * (Real.log x / x)) atTop (𝓝 0) := by
      have h1 := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul c
      have h2 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul
        (0.631 * t ^ 2)
      have := h1.add h2
      simp only [mul_zero, add_zero] at this
      refine this.congr' ?_
      filter_upwards with x
      simp
    refine squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hb
    filter_upwards [eventually_ge_atTop (max 1 (|t| / π))] with x hx
    have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
    have hxt : |t| ≤ π * x := by
      have := le_trans (le_max_right _ _) hx
      rw [div_le_iff₀ hpi] at this; linarith
    have := bulkAB hx1 hxt
    calc _ ≤ t ^ 2 / x * (0.631 * (|Real.log (|t|)| + Real.log x) + 1.53) := this
      _ = c * x⁻¹ + 0.631 * t ^ 2 * (Real.log x / x) := by rw [hc]; field_simp; ring
  exact (Complex.continuous_exp.tendsto _).comp hexp

/-- `B(ct) = c B(t) - i c t log c` for `c > 0`. -/
theorem landauB_mul {c : ℝ} (hc : 0 < c) (t : ℝ) :
    landauB (c * t) = (c : ℂ) * landauB t - (c : ℂ) * (t : ℂ) * I * (Real.log c : ℂ) := by
  unfold landauB
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; simp
  rw [abs_mul, abs_of_pos hc, Real.log_mul hc.ne' (abs_pos.mpr ht).ne']
  push_cast
  ring

/-- **The class-`L` identity** (Appendix C.2): for `0 < c < 1` and real `t`,
`e^{B(t)} = e^{B(ct)} e^{B((1-c)t)} e^{it[(1-c)log(1-c) + c log c]}`. -/
theorem exp_landauB_classL {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (t : ℝ) :
    cexp (landauB t) = cexp (landauB (c * t)) * cexp (landauB ((1 - c) * t))
      * cexp ((t : ℂ) * I * (((1 - c) * Real.log (1 - c) + c * Real.log c : ℝ) : ℂ)) := by
  rw [← Complex.exp_add, ← Complex.exp_add, landauB_mul hc0, landauB_mul (by linarith)]
  congr 1
  push_cast
  ring

end

end Kagey131.PaperD.U2
