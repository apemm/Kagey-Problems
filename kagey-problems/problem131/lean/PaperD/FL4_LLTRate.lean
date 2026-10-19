import PaperD.FL4_LLT

/-!
# Paper F, Appendix B (track FL4): Proposition B.5 with a rate

`llt_rate`: for every `0 < a ≤ b < 2` there is `C` such that for all `c ∈ [a, b]` and all
even `N = 2m ≥ 4`, `|N C_N - d_c| ≤ C √(log N / N)`.

This is stronger than Proposition B.5 of Paper F, which has the rate `(log N) N^{-κ_J}` with
`κ_J = a_J/(1+a_J) ≤ 1/2`: `√(log N / N) ≤ (log N) N^{-κ_J}` for `N ≥ 3`. A compact
`J ⊂ (0,2)` lies in `[min J, max J]`, so the interval form is no restriction.
-/

namespace Kagey131.PaperD.FL4

open Real Set

/-- `c ↦ 1/B(c,c)` is bounded on `[a, b] ⊂ (0, ∞)`. -/
theorem inv_beta_bounded {a b : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c ∈ Icc a b, 64 / ProbabilityTheory.beta c c ≤ M := by
  have hcont : ContinuousOn (fun c : ℝ => 64 / ProbabilityTheory.beta c c) (Icc a b) := by
    intro c hc
    have hc0 : 0 < c := ha.trans_le hc.1
    have hG : ∀ s : ℝ, 0 < s → ContinuousAt Gamma s := fun s hs =>
      (Real.differentiableAt_Gamma (fun m => by
        have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith)).continuousAt
    unfold ProbabilityTheory.beta
    refine ContinuousAt.continuousWithinAt ?_
    refine continuousAt_const.div ?_ (ProbabilityTheory.beta_pos hc0 hc0).ne'
    refine ContinuousAt.div ((hG c hc0).mul (hG c hc0)) ?_
      (Real.Gamma_pos_of_pos (by linarith)).ne'
    show ContinuousAt (fun x : ℝ => Gamma (x + x)) c
    exact (hG (c + c) (by linarith)).comp (f := fun x : ℝ => x + x)
      ((continuous_id.add continuous_id).continuousAt)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun c hc => ?_⟩
  have := hC c hc
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

theorem dc_le {c : ℝ} (hc0 : 0 < c) : dc c ≤ 4 * (1 / ProbabilityTheory.beta c c) := by
  unfold dc
  have hB := beta_pos' hc0
  have : (4 : ℝ) ^ (1 - c) ≤ 4 := by
    calc (4 : ℝ) ^ (1 - c) ≤ (4 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := Real.rpow_one 4
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right this hB.le

theorem log_ge_one {N : ℝ} (hN : 4 ≤ N) : 1 ≤ Real.log N := by
  have h4 : Real.log 4 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have := Real.log_two_gt_d9
  linarith

/-- Paper F, Proposition B.5 (local limit at the center), with the rate `√(log N / N)`. -/
theorem llt_rate {a b : ℝ} (ha : 0 < a) (hb : b < 2) :
    ∃ C : ℝ, ∀ c ∈ Icc a b, ∀ m : ℕ, 2 ≤ m →
      |2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m - dc c| ≤
        C * Real.sqrt (Real.log (2 * (m : ℝ)) / (2 * (m : ℝ))) := by
  obtain ⟨M, hM0, hM⟩ := inv_beta_bounded (b := b) ha
  refine ⟨(72 * M + 884) + 32 * (4 + M / 16), fun c hc m hm => ?_⟩
  have hc0 : 0 < c := ha.trans_le hc.1
  have hc2 : c < 2 := hc.2.trans_lt hb
  have hBM := hM c hc
  have hB0 : 0 < 64 / ProbabilityTheory.beta c c := div_pos (by norm_num) (beta_pos' hc0)
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set N : ℝ := 2 * (m : ℝ) with hN
  have hN4 : 4 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  set L := Real.log N with hL
  have hL1 : 1 ≤ L := log_ge_one hN4
  set r := Real.sqrt (L / N) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  set sN := Real.sqrt N with hsN
  have hsN0 : 0 < sN := Real.sqrt_pos.mpr hN0
  have hsN2 : sN * sN = N := Real.mul_self_sqrt hN0.le
  have hsN_ge2 : 2 ≤ sN := by
    rw [hsN, show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hN4
  -- `s = 1/√N ≤ r`
  have hs_le : 1 / sN ≤ r := by
    rw [hr, Real.sqrt_div' _ hN0.le, ← hsN, div_le_div_iff_of_pos_right hsN0]
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hL1
  have hN1 : 1 / N ≤ 1 / sN := by
    rw [div_le_div_iff₀ hN0 hsN0, one_mul, one_mul, ← hsN2]; nlinarith
  -- `√(N L) = N r`
  have hNL : Real.sqrt (N * L) = N * r := by
    rw [hr, Real.sqrt_mul hN0.le, Real.sqrt_div' _ hN0.le, ← hsN]
    field_simp
    rw [show N = sN * sN from hsN2.symm]; ring
  -- the choices of `K` and `u`
  set K := Nat.sqrt (2 * m) with hK
  have hK1 : (K : ℝ) ≤ sN := by
    have := Real.nat_sqrt_le_real_sqrt (a := 2 * m); push_cast at this; exact this
  have hK2 : sN < (K : ℝ) + 1 := by
    have := Real.real_sqrt_lt_nat_sqrt_succ (a := 2 * m); push_cast at this; exact this
  set u := 2 * Real.sqrt (N * L) with hu
  have hu0 : 0 < u := by
    rw [hu]; have : 0 < N * L := by positivity
    have := Real.sqrt_pos.mpr this; linarith
  have huN : u = 2 * (N * r) := by rw [hu, hNL]
  set w := (K : ℝ) + 1 + u with hw
  have hwN : w / N ≤ 4 * r := by
    rw [div_le_iff₀ hN0, hw, huN]
    have h1 : (K : ℝ) + 1 ≤ sN + 1 := by linarith
    have h2 : sN + 1 ≤ 2 * (N * r) := by
      have : sN ≤ N * r := by
        have := mul_le_mul_of_nonneg_left hs_le hN0.le
        rw [show N * (1 / sN) = sN by rw [← hsN2]; field_simp] at this
        exact this
      have : 1 ≤ N * r := by
        have h := mul_le_mul_of_nonneg_left hs_le hN0.le
        rw [show N * (1 / sN) = sN by rw [← hsN2]; field_simp] at h
        linarith
      linarith
    linarith
  have hKs : 12 / ((K : ℝ) + 1) ≤ 12 * r := by
    have : 1 / ((K : ℝ) + 1) ≤ 1 / sN := one_div_le_one_div_of_le hsN0 hK2.le
    have := this.trans hs_le
    rw [show 12 / ((K : ℝ) + 1) = 12 * (1 / ((K : ℝ) + 1)) by ring]
    linarith
  -- the exponential term
  set η := exp (-(u ^ 2 / (2 * (2 * (m : ℝ) - 1)))) with hη
  have hη0 : 0 ≤ η := (Real.exp_pos _).le
  have hηr : η ≤ r := by
    have h1 : η ≤ exp (-(2 * L)) := by
      rw [hη]
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, hu, mul_pow, Real.sq_sqrt (by positivity), le_div_iff₀ (by linarith)]
      rw [← hN]
      have : 0 ≤ L := by linarith
      nlinarith
    have h2 : exp (-(2 * L)) = 1 / N ^ 2 := by
      rw [hL, show -(2 * Real.log N) = Real.log (N ^ 2)⁻¹ by
        rw [Real.log_inv, Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
      ring
    have h3 : 1 / N ^ 2 ≤ 1 / N := by
      apply one_div_le_one_div_of_le hN0
      nlinarith
    linarith [hN1, hs_le]
  by_cases hwm : w ≤ (m : ℝ) / 4
  · have hE := llt_explicit hc0 hc2 hm hu0 hwm
    refine hE.trans ?_
    rw [← hη]
    have hDpos : 0 < 2 * (m : ℝ) - 1 := by linarith
    have hND : N ≤ 2 * (2 * (m : ℝ) - 1) := by rw [hN]; linarith
    have hw0 : 0 ≤ w := by positivity
    have hc2' : c ≤ 2 := hc2.le
    have hwN' : w ≤ 4 * r * N := (div_le_iff₀ hN0).mp hwN
    have q1 : 2 * w / (2 * (m : ℝ) - 1) ≤ 16 * r := by
      rw [div_le_iff₀ hDpos]
      have : 4 * r * N ≤ 4 * r * (2 * (2 * (m : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hND (by positivity)
      linarith
    have P1 : c * (64 / ProbabilityTheory.beta c c * (2 * w / (2 * (m : ℝ) - 1))) ≤ 2 * (M * (16 * r)) := by
      have hq0 : 0 ≤ 2 * w / (2 * (m : ℝ) - 1) := by positivity
      have h1 := mul_le_mul hBM q1 hq0 hM0
      have h2 : 0 ≤ 64 / ProbabilityTheory.beta c c * (2 * w / (2 * (m : ℝ) - 1)) := by positivity
      calc c * (64 / ProbabilityTheory.beta c c * (2 * w / (2 * (m : ℝ) - 1)))
          ≤ 2 * (64 / ProbabilityTheory.beta c c * (2 * w / (2 * (m : ℝ) - 1))) :=
            mul_le_mul_of_nonneg_right hc2' h2
        _ ≤ 2 * (M * (16 * r)) := by linarith
    have hY : η + 12 / ((K : ℝ) + 1) ≤ 13 * r := by linarith
    have hY0 : 0 ≤ η + 12 / ((K : ℝ) + 1) := by positivity
    have P2 : c * (η + 12 / ((K : ℝ) + 1)) ≤ 2 * (13 * r) :=
      (mul_le_mul_of_nonneg_right hc2' hY0).trans (by linarith)
    have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hmc : 2 * c / ((m : ℝ) + 1) ≤ 8 / N := by
      rw [div_le_div_iff₀ hm0 hN0, hN]
      have : 2 * c * (2 * (m : ℝ)) ≤ 2 * 2 * (2 * (m : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have hmc0 : 0 ≤ 2 * c / ((m : ℝ) + 1) := by positivity
    have hNr : 1 / N ≤ r := hN1.trans hs_le
    have P3 : 2 * c / ((m : ℝ) + 1) * (8 * w + 1) ≤ 264 * r := by
      have h1 : 8 / N * (8 * w + 1) = 64 * (w / N) + 8 * (1 / N) := by ring
      have := mul_le_mul_of_nonneg_right hmc (by positivity : (0 : ℝ) ≤ 8 * w + 1)
      linarith
    have P4 : 2 * c / ((m : ℝ) + 1) * (2 * (m : ℝ) * (η + 12 / ((K : ℝ) + 1))) ≤ 104 * r := by
      have h8 : 2 * c / ((m : ℝ) + 1) * (2 * (m : ℝ)) ≤ 8 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hm0]
        have : 2 * c * (2 * (m : ℝ)) ≤ 2 * 2 * (2 * (m : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        linarith
      calc 2 * c / ((m : ℝ) + 1) * (2 * (m : ℝ) * (η + 12 / ((K : ℝ) + 1)))
          = (2 * c / ((m : ℝ) + 1) * (2 * (m : ℝ))) * (η + 12 / ((K : ℝ) + 1)) := by ring
        _ ≤ 8 * (13 * r) := mul_le_mul h8 hY hY0 (by norm_num)
        _ = 104 * r := by ring
    have P5 : 48 * c / (2 * (m : ℝ)) ≤ 96 * r := by
      rw [← hN, show 48 * c / N = 48 * c * (1 / N) by ring]
      have h0 : 0 ≤ 1 / N := by positivity
      have : 48 * c * (1 / N) ≤ 48 * 2 * (1 / N) :=
        mul_le_mul_of_nonneg_right (by linarith) h0
      linarith
    have P6 : 4 * c * (64 / ProbabilityTheory.beta c c * ((m : ℝ) / (2 * (m : ℝ) - 1) - 1 / 2)) ≤
        8 * (M * r) := by
      have e : (m : ℝ) / (2 * (m : ℝ) - 1) - 1 / 2 = 1 / (2 * (2 * (m : ℝ) - 1)) := by
        have hD' : 2 * (m : ℝ) - 1 ≠ 0 := hDpos.ne'
        rw [div_sub_div _ _ hD' (by norm_num : (2 : ℝ) ≠ 0),
          div_eq_div_iff (mul_ne_zero hD' (by norm_num)) (mul_ne_zero (by norm_num) hD')]
        ring
      rw [e]
      have h1 : 1 / (2 * (2 * (m : ℝ) - 1)) ≤ 1 / N := by
        rw [div_le_div_iff₀ (by positivity) hN0]; linarith
      have h2 : 1 / (2 * (2 * (m : ℝ) - 1)) ≤ r := h1.trans hNr
      have h3 : 0 ≤ 1 / (2 * (2 * (m : ℝ) - 1)) := by positivity
      have h5 := mul_le_mul hBM h2 h3 hM0
      have h4 : 0 ≤ 64 / ProbabilityTheory.beta c c * (1 / (2 * (2 * (m : ℝ) - 1))) := by positivity
      calc 4 * c * (64 / ProbabilityTheory.beta c c * (1 / (2 * (2 * (m : ℝ) - 1))))
          ≤ 4 * 2 * (64 / ProbabilityTheory.beta c c * (1 / (2 * (2 * (m : ℝ) - 1)))) :=
            mul_le_mul_of_nonneg_right (by linarith) h4
        _ ≤ 8 * (M * r) := by linarith
    have hfin : 2 * (c * (64 / ProbabilityTheory.beta c c * (2 * w / (2 * (m : ℝ) - 1)) +
          (η + 12 / ((K : ℝ) + 1))) +
        2 * c / ((m : ℝ) + 1) * (8 * w + 1 + 2 * (m : ℝ) * (η + 12 / ((K : ℝ) + 1)))) +
      (48 * c / (2 * (m : ℝ)) + 4 * c * (64 / ProbabilityTheory.beta c c *
        ((m : ℝ) / (2 * (m : ℝ) - 1) - 1 / 2))) ≤ 72 * (M * r) + 884 * r := by
      have e1 : c * (64 / ProbabilityTheory.beta c c * (2 * w / (2 * (m : ℝ) - 1)) +
          (η + 12 / ((K : ℝ) + 1))) = c * (64 / ProbabilityTheory.beta c c * (2 * w / (2 * (m : ℝ) - 1))) +
          c * (η + 12 / ((K : ℝ) + 1)) := by ring
      have e2 : 2 * c / ((m : ℝ) + 1) * (8 * w + 1 + 2 * (m : ℝ) * (η + 12 / ((K : ℝ) + 1))) =
          2 * c / ((m : ℝ) + 1) * (8 * w + 1) +
          2 * c / ((m : ℝ) + 1) * (2 * (m : ℝ) * (η + 12 / ((K : ℝ) + 1))) := by ring
      rw [e1, e2]
      linarith
    refine hfin.trans ?_
    have e : ((72 * M + 884) + 32 * (4 + M / 16)) * r = 72 * (M * r) + 884 * r + 32 * (4 + M / 16) * r := by
      ring
    rw [e]
    have : 0 ≤ 32 * (4 + M / 16) * r := by positivity
    linarith
  · -- the trivial range: `w > m/4` forces `r > 1/32`
    push Not at hwm
    have hr32 : 1 / 32 < r := by
      have h := (div_le_iff₀ hN0).mp hwN
      have h2 : N * (1 / 32) < N * r := by rw [hN] at h ⊢; linarith
      exact lt_of_mul_lt_mul_left h2 hN0.le
    obtain ⟨h0, h1⟩ := center_le hc0 hc2 (by omega : 1 ≤ m)
    have hdc := dc_le hc0
    have hdc0 : 0 ≤ dc c := by unfold dc; have := beta_pos' hc0; positivity
    have hb1 : 4 * (1 / ProbabilityTheory.beta c c) ≤ M / 16 := by
      have : 64 / ProbabilityTheory.beta c c = 64 * (1 / ProbabilityTheory.beta c c) := by ring
      linarith
    have habs : |2 * (m : ℝ) * agBin (agingP c) (2 * m - 1) m - dc c| ≤ 4 + M / 16 := by
      rw [abs_le]; constructor <;> linarith
    have hA : 0 ≤ 4 + M / 16 := by positivity
    have h3 : (4 + M / 16) * 1 ≤ (4 + M / 16) * (32 * r) :=
      mul_le_mul_of_nonneg_left (by linarith) hA
    have h4 : 0 ≤ (72 * M + 884) * r := by positivity
    have e : ((72 * M + 884) + 32 * (4 + M / 16)) * r = (72 * M + 884) * r + (4 + M / 16) * (32 * r) := by
      ring
    rw [e]
    linarith

end Kagey131.PaperD.FL4
