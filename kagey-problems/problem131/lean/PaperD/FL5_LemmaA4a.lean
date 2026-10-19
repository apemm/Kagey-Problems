import PaperD.FL5_Lemma23a

/-!
# Paper F, track FL5: the Laplace transforms of Lemma A.4(i) (`0 < α < 1`)

The paper's proof of Lemma A.4(i): "With `x = e^{-v}` this is
`1 - E e^{-vξ} = (e^v - 1) Li_α(e^{-v})`, and [DLMF 25.12.12] gives
`Li_α(e^{-v}) = Γ(1-α) v^{α-1} + ζ(α) + O(v)` as `v ↓ 0`. So
`1 - E e^{-vξ} = Γ(1-α) v^α + O(v)`. As `1/α > 1`, this gives
`m(1 - E e^{-sξ/a_m}) → Γ(1-α) s^α` for each `s ≥ 0`. Hence
`E e^{-sτ_m/a_m} → e^{-Γ(1-α)s^α}`."

* `genC_expansion_lt`: `1 - E e^{-vξ} = Γ(1-α) v^α + O(v)` for real `0 < v ≤ 1`;
* `tendsto_laplace_tau`: `∑_k u_m(k) e^{-s k/a_m} → e^{-Γ(1-α) s^α}` for `s ≥ 0`.
-/

namespace Kagey131.PaperD.FL5

open Finset Filter Topology Real Asymptotics

/-- `1 - E e^{-vξ} = Γ(1-α) v^α + O(v)` for real `0 < v ≤ 1`, `0 < α < 1`. -/
theorem genC_expansion_lt (hP : PolylogHyp) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 0 < v → v ≤ 1 →
      ‖1 - genC (runP α) (Complex.exp (-(v : ℂ)))
        - Complex.Gamma (1 - (α : ℂ)) * ((v : ℂ) ^ (α : ℂ))‖ ≤ C * v := by
  obtain ⟨C1, hC1, hli⟩ := li_expansion_gen hP h0 (by linarith) h1.ne
  set Γc : ℂ := Complex.Gamma (1 - (α : ℂ))
  set ζc : ℂ := riemannZeta α
  refine ⟨‖ζc‖ + C1 + (‖Γc‖ + ‖ζc‖ + C1), by positivity, fun v hv0 hv1 => ?_⟩
  have hvc0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv0.ne'
  have hvre : 0 < (v : ℂ).re := by simpa using hv0
  have hvn : ‖(v : ℂ)‖ = v := by rw [Complex.norm_real, Real.norm_of_nonneg hv0.le]
  have hvn1 : ‖(v : ℂ)‖ ≤ 1 := by rw [hvn]; exact hv1
  set R : ℂ := liC α (Complex.exp (-(v : ℂ))) - Γc * (v : ℂ) ^ ((α : ℂ) - 1) - ζc with hR
  have hRle : ‖R‖ ≤ C1 * v := by
    have := hli v hvc0 hvre.le (Or.inr hvre) hvn1
    rwa [hvn] at this
  set E : ℂ := Complex.exp v - 1 - v with hE
  have hEle : ‖E‖ ≤ v ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le hvn1
    rwa [hvn] at this
  have hS : Summable (fun k : ℕ => (((k : ℝ) ^ (-α) : ℝ) : ℂ) * Complex.exp (-(v : ℂ)) ^ k) := by
    refine summable_liC_lt h0 ?_
    rw [Complex.norm_exp]; simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hpow : ‖(v : ℂ) ^ ((α : ℂ) - 1)‖ = v ^ (α - 1) := by
    rw [show (α : ℂ) - 1 = ((α - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real, hvn]
  have hvα : v ^ α ≤ 1 := Real.rpow_le_one hv0.le hv1 h0.le
  have hv2 : v ^ 2 * v ^ (α - 1) = v * v ^ α := by
    rw [Real.rpow_sub_one hv0.ne']; field_simp
  have key : 1 - genC (runP α) (Complex.exp (-(v : ℂ))) - Γc * ((v : ℂ) ^ (α : ℂ))
      = ζc * v + v * R + E * (Γc * (v : ℂ) ^ ((α : ℂ) - 1) + ζc + R) := by
    rw [one_sub_genC_runP_exp_of_summable h0 hS]
    have hL : liC α (Complex.exp (-(v : ℂ))) = Γc * (v : ℂ) ^ ((α : ℂ) - 1) + ζc + R := by
      rw [hR]; ring
    rw [hL, show Complex.exp v - 1 = v + E by rw [hE]; ring, ← cpow_mul_self hvc0 α]
    ring
  rw [key]
  calc ‖ζc * v + v * R + E * (Γc * (v : ℂ) ^ ((α : ℂ) - 1) + ζc + R)‖
      ≤ ‖ζc‖ * v + v * ‖R‖ + ‖E‖ * (‖Γc‖ * ‖(v : ℂ) ^ ((α : ℂ) - 1)‖ + ‖ζc‖ + ‖R‖) := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans (le_of_eq ?_)) ?_
        · rw [norm_mul, norm_mul, hvn]
        · rw [norm_mul]
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
    _ ≤ ‖ζc‖ * v + v * (C1 * v) + v ^ 2 * (‖Γc‖ * v ^ (α - 1) + ‖ζc‖ + C1 * v) := by
        rw [hpow]; gcongr
    _ = ‖ζc‖ * v + C1 * v ^ 2 + ‖Γc‖ * (v * v ^ α) + ‖ζc‖ * v ^ 2 + C1 * v ^ 3 := by
        rw [← hv2]; ring
    _ ≤ ‖ζc‖ * v + C1 * v + ‖Γc‖ * (v * 1) + ‖ζc‖ * v + C1 * v := by
        have h2 : v ^ 2 ≤ v := by nlinarith
        have h3 : v ^ 3 ≤ v := by nlinarith
        gcongr
    _ = (‖ζc‖ + C1 + (‖Γc‖ + ‖ζc‖ + C1)) * v := by ring

/-- **Lemma A.4(i)**, Laplace transforms: for `0 < α < 1` and `s ≥ 0`,
`E e^{-s τ_m/a_m} = ∑_k u_m(k) e^{-s k/a_m} → e^{-Γ(1-α) s^α}`. -/
theorem tendsto_laplace_tau (hP : PolylogHyp) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {s : ℝ}
    (hs : 0 ≤ s) :
    Tendsto (fun m : ℕ => genC ((runLaw α h0).u m)
        (Complex.exp (-((s / (m : ℝ) ^ (1 / α) : ℝ) : ℂ)))) atTop
      (𝓝 (Complex.exp (-(Complex.Gamma (1 - (α : ℂ)) * ((s : ℂ) ^ (α : ℂ)))))) := by
  set L := runLaw α h0
  have hz : ∀ m : ℕ, ‖Complex.exp (-((s / (m : ℝ) ^ (1 / α) : ℝ) : ℂ))‖ ≤ 1 := fun m => by
    apply norm_exp_neg_le_one
    simp only [Complex.ofReal_re]
    exact div_nonneg hs (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  simp_rw [fun m => genC_u L m (hz m)]
  rcases eq_or_lt_of_le hs with rfl | hs0
  · have hp1 : genC L.p 1 = 1 := by
      rw [genC_one_eq, L.hasSum.tsum_eq]; simp
    have : (α : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    simp only [zero_div, Complex.ofReal_zero, neg_zero, Complex.exp_zero, hp1, one_pow,
      Complex.zero_cpow this, mul_zero]
    exact tendsto_const_nhds
  obtain ⟨C, hC, hexp⟩ := genC_expansion_lt hP h0 h1
  apply Complex.tendsto_pow_exp_of_isLittleO_sub_add_div
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hinv : Tendsto (fun m : ℕ => s / (m : ℝ) ^ (1 / α)) atTop (𝓝 0) := by
    have := (tendsto_rpow_atTop (by positivity : 0 < 1 / α)).comp tendsto_natCast_atTop_atTop
    have := this.inv_tendsto_atTop.const_mul s
    rw [mul_zero] at this
    refine this.congr fun m => ?_
    simp [div_eq_mul_inv]
  have hdecay : Tendsto (fun m : ℕ => (m : ℝ) ^ (1 - 1 / α)) atTop (𝓝 0) := by
    have h12 : 1 - 1 / α < 0 := by
      rw [sub_neg, lt_div_iff₀ h0]; linarith
    have := (tendsto_rpow_neg_atTop (y := -(1 - 1 / α)) (by linarith)).comp
      tendsto_natCast_atTop_atTop
    refine this.congr fun m => ?_
    simp
  have hCs : 0 < (C + 1) * s := by positivity
  filter_upwards [eventually_ge_atTop 1,
    hinv.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hdecay.eventually (gt_mem_nhds (show (0 : ℝ) < ε / ((C + 1) * s) by positivity))]
    with m hm hsmall hdec
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have ham : 0 < (m : ℝ) ^ (1 / α) := Real.rpow_pos_of_pos hm0 _
  set am : ℝ := (m : ℝ) ^ (1 / α) with ham_def
  set v : ℝ := s / am with hv
  have hv0 : 0 < v := div_pos hs0 ham
  have hpowm : v ^ α = s ^ α / m := by
    rw [hv, Real.div_rpow hs0.le ham.le, ham_def, ← Real.rpow_mul hm0.le,
      one_div_mul_cancel h0.ne', Real.rpow_one]
  have e3 : -(Complex.Gamma (1 - (α : ℂ)) * ((s : ℂ) ^ (α : ℂ))) / (m : ℂ)
      = -(Complex.Gamma (1 - (α : ℂ)) * ((v : ℂ) ^ (α : ℂ))) := by
    rw [← Complex.ofReal_cpow hs0.le, ← Complex.ofReal_cpow hv0.le, hpowm]
    push_cast
    ring
  have hkey := hexp v hv0 hsmall.le
  rw [e3]
  have hnm : ‖(1 : ℂ) / (m : ℂ)‖ = 1 / (m : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [hnm]
  have hsplit : (m : ℝ) ^ (1 - 1 / α) = m * (m : ℝ) ^ (-(1 / α)) := by
    rw [sub_eq_add_neg, Real.rpow_add hm0, Real.rpow_one]
  calc ‖genC L.p (Complex.exp (-(v : ℂ))) - (1 + -(Complex.Gamma (1 - (α : ℂ)) * (v : ℂ) ^ (α : ℂ)))‖
      = ‖1 - genC (runP α) (Complex.exp (-(v : ℂ)))
          - Complex.Gamma (1 - (α : ℂ)) * ((v : ℂ) ^ (α : ℂ))‖ := by
        rw [← norm_neg]; congr 1; simp only [L, runLaw]; ring
    _ ≤ C * v := hkey
    _ = C * s * (m : ℝ) ^ (-(1 / α)) := by
        rw [hv, ham_def, Real.rpow_neg hm0.le]; ring
    _ ≤ ε * (1 / (m : ℝ)) := by
        have h3 : (C + 1) * s * (m : ℝ) ^ (1 - 1 / α) < ε := by
          rw [lt_div_iff₀ hCs] at hdec; linarith
        rw [hsplit] at h3
        have hpos : 0 ≤ s * (m : ℝ) ^ (-(1 / α)) := by positivity
        rw [mul_one_div, le_div_iff₀ hm0]
        nlinarith

end Kagey131.PaperD.FL5
