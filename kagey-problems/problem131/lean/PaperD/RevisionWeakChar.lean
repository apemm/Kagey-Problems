import PaperD.U2_Bridge
import PaperD.U2_LandauCharFun
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# The weak Landau limit under the quadratic error condition

The proof uses characteristic functions directly. It therefore does not need the
extra factor `x` in the local-limit error, or a total-variation approximation.
-/

namespace Kagey131.PaperD.RevisionWeak

open Complex Finset Filter Topology MeasureTheory Set
open U1 RRT

noncomputable section

def walkChar (ε θ : ℝ) (N : ℕ) : ℂ :=
  ∑' m, (law ε N m : ℂ) * eI θ m

lemma finite_image_char {t B : ℕ} (Y : IncTree t → Word t → ℕ)
    (hY : ∀ T μ, Y T μ < B) (ε θ : ℝ) :
    (∑' m, (tmP ε t (fun T μ => Y T μ = m) : ℂ) * eI θ m) =
      ∑ T : IncTree t, ∑ μ : Word t, (wt ε t μ : ℂ) * eI θ (Y T μ) := by
  classical
  have hz (m : ℕ) (hm : m ∉ range B) : tmP ε t (fun T μ => Y T μ = m) = 0 := by
    unfold tmP
    refine sum_eq_zero (fun T _ => sum_eq_zero (fun μ _ => if_neg ?_))
    have := hY T μ
    simp only [Finset.mem_range, not_lt] at hm
    omega
  rw [tsum_eq_sum (s := range B) (fun m hm => by rw [hz m hm]; simp)]
  have ht (m : ℕ) : (tmP ε t (fun T μ => Y T μ = m) : ℂ) * eI θ m =
      ∑ T : IncTree t, ∑ μ : Word t,
        if Y T μ = m then (wt ε t μ : ℂ) * eI θ m else 0 := by
    unfold tmP
    push_cast
    rw [sum_mul]
    refine sum_congr rfl (fun T _ => ?_)
    rw [sum_mul]
    refine sum_congr rfl (fun μ _ => ?_)
    split_ifs <;> simp
  simp_rw [ht]
  rw [sum_comm]
  refine sum_congr rfl (fun T _ => ?_)
  rw [sum_comm]
  refine sum_congr rfl (fun μ _ => ?_)
  simp only [sum_ite_eq, Finset.mem_range, if_pos (hY T μ)]

lemma walkChar_eq (ε θ : ℝ) (t : ℕ) :
    walkChar ε θ (t + 1) =
      ∑ T : IncTree t, ∑ μ : Word t, (wt ε t μ : ℂ) * eI θ (oddCount T μ) := by
  unfold walkChar
  simp_rw [← tmP_oddCount ε t]
  apply finite_image_char (B := t + 2)
  intro T μ
  unfold oddCount
  have := card_filter_le (univ : Finset (Fin (t + 1))) (fun v => flips T μ v % 2 = 1)
  simp only [card_univ, Fintype.card_fin] at this
  omega

lemma charZ_eq_finite (ε θ : ℝ) (t : ℕ) :
    charZ ε θ t =
      ∑ T : IncTree t, ∑ μ : Word t, (wt ε t μ : ℂ) * eI θ (Zp T μ) := by
  unfold charZ
  apply finite_image_char (B := t * t + 1)
  intro T μ
  have := Zp_le T μ
  omega

lemma walkChar_sub_charZ {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (t : ℕ) (θ : ℝ) :
    ‖walkChar ε θ (t + 1) - charZ ε θ t‖ ≤
      2 * tmP ε t (fun T μ => oddCount T μ ≠ Zp T μ) := by
  classical
  rw [walkChar_eq, charZ_eq_finite, ← sum_sub_distrib]
  unfold tmP
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum (fun T _ => ?_))
  rw [← sum_sub_distrib, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum (fun μ _ => ?_))
  by_cases h : oddCount T μ = Zp T μ
  · simp [h]
  · rw [if_pos h, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (wt_nonneg h0 h1 t μ)]
    have hb := norm_eI_sub_eI θ (oddCount T μ) (Zp T μ)
    nlinarith [wt_nonneg h0 h1 t μ]

theorem walkChar_error (hES : EfronSteinHyp) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) (θ : ℝ) :
    ‖walkChar ε θ N - cexp (((N : ℝ) * ε : ℝ) * PsiN N θ)‖ ≤
      2 * U2.deltaB N ε := by
  obtain ⟨t, rfl⟩ : ∃ t, N = t + 1 := ⟨N - 1, by omega⟩
  have A := walkChar_sub_charZ h0 h1 t θ
  have B := step1 h0 h1 t
  have C := char_bound hES h0 h1 t θ
  have hn : 0 ≤ 2 * ε ^ 2 * t + 4 * ε ^ 2 * ∑ k ∈ range t, (Hr k ^ 2 + Hr k) := by
    have hs : 0 ≤ ∑ k ∈ range t, (Hr k ^ 2 + Hr k) :=
      sum_nonneg (fun k _ => add_nonneg (sq_nonneg _) (Hr_nonneg k))
    positivity
  have D := (deltaSum_le_deltaSharp ε (t + 1)).trans (deltaSharp_le_deltaB ε (by omega : 1 ≤ t + 1))
  rw [← U2.deltaB_eq] at D
  have E := norm_sub_le_norm_sub_add_norm_sub (walkChar ε θ (t + 1)) (charZ ε θ t)
    (cexp (((((t : ℝ) + 1) * ε : ℝ) : ℂ) * PsiN (t + 1) θ))
  have hbound : ‖walkChar ε θ (t + 1) -
      cexp (((((t : ℝ) + 1) * ε : ℝ) : ℂ) * PsiN (t + 1) θ)‖ ≤
      2 * deltaSum ε (t + 1) := by
    unfold deltaSum
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_left D (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [Nat.cast_add, Nat.cast_one] using hfinal

/-- The quadratic error condition supplies every eventual restriction needed below. -/
lemma eventually_regime (N : ℕ → ℕ) (ε : ℕ → ℝ) (hε1 : ∀ᶠ n in atTop, ε n ≤ 1)
    (hx : Tendsto (fun n => (N n : ℝ) * ε n) atTop atTop)
    (h2 : Tendsto (fun n => ((N n : ℝ) * ε n) ^ 2 * Real.log (N n) ^ 2 / N n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 1 ≤ (N n : ℝ) * ε n ∧ 1 ≤ Real.log (N n) ∧
      4 * ((N n : ℝ) * ε n) ^ 2 ≤ N n ∧
      (N n : ℝ) * ε n / N n ≤ ((N n : ℝ) * ε n) ^ 2 * Real.log (N n) ^ 2 / N n := by
  have hv := hx.eventually_ge_atTop 3
  have hr := h2.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hv, hr, hε1] with n h3 hsmall he
  have hN0 : (0 : ℝ) ≤ N n := Nat.cast_nonneg _
  have hxN : (N n : ℝ) * ε n ≤ N n := mul_le_of_le_one_right hN0 he
  have hN3 : 3 ≤ N n := by exact_mod_cast (show (3 : ℝ) ≤ N n by linarith)
  have hL := U2.one_le_log_of_three hN3
  have hNp : (0 : ℝ) < N n := by linarith
  set x := (N n : ℝ) * ε n with hxd
  have hL2 : 1 ≤ Real.log (N n) ^ 2 := by nlinarith
  have hq : x ^ 2 ≤ x ^ 2 * Real.log (N n) ^ 2 := by nlinarith [sq_nonneg x]
  have hxx : 4 * x ^ 2 ≤ N n := by
    rw [div_le_iff₀ hNp] at hsmall
    nlinarith
  refine ⟨by linarith, hL, hxx, ?_⟩
  rw [div_le_div_iff_of_pos_right hNp]
  nlinarith

theorem tendsto_deltaB (N : ℕ → ℕ) (ε : ℕ → ℝ) (hε1 : ∀ᶠ n in atTop, ε n ≤ 1)
    (hx : Tendsto (fun n => (N n : ℝ) * ε n) atTop atTop)
    (h2 : Tendsto (fun n => ((N n : ℝ) * ε n) ^ 2 * Real.log (N n) ^ 2 / N n) atTop (𝓝 0)) :
    Tendsto (fun n => U2.deltaB (N n) (ε n)) atTop (𝓝 0) := by
  have hb : ∀ᶠ n in atTop, U2.deltaB (N n) (ε n) ≤
      36 * (((N n : ℝ) * ε n) ^ 2 * Real.log (N n) ^ 2 / N n) := by
    filter_upwards [eventually_regime N ε hε1 hx h2] with n hn
    have h := U2.x_deltaB_le' hn.2.1 (by linarith : 0 ≤ (N n : ℝ) * ε n) hn.2.2.1
    have he : 36 * (((N n : ℝ) * ε n) ^ 3 * Real.log (N n) ^ 2 / N n) =
        ((N n : ℝ) * ε n) * (36 * (((N n : ℝ) * ε n) ^ 2 * Real.log (N n) ^ 2 / N n)) := by ring
    rw [he] at h
    exact (mul_le_mul_iff_right₀ (by linarith : 0 < (N n : ℝ) * ε n)).mp h
  exact squeeze_zero' (Eventually.of_forall (fun n => U2.deltaB_nonneg' (N n) (ε n))) hb
    (by simpa using h2.const_mul 36)

theorem tendsto_x_div_N (N : ℕ → ℕ) (ε : ℕ → ℝ) (hε1 : ∀ᶠ n in atTop, ε n ≤ 1)
    (hx : Tendsto (fun n => (N n : ℝ) * ε n) atTop atTop)
    (h2 : Tendsto (fun n => ((N n : ℝ) * ε n) ^ 2 * Real.log (N n) ^ 2 / N n) atTop (𝓝 0)) :
    Tendsto (fun n => (N n : ℝ) * ε n / N n) atTop (𝓝 0) := by
  have hev := eventually_regime N ε hε1 hx h2
  apply squeeze_zero' _ (hev.mono (fun _ hn => hn.2.2.2)) h2
  filter_upwards [hev] with n hn
  apply div_nonneg (by linarith) (Nat.cast_nonneg _)

lemma charFun_latticeLaw {x : ℝ} {f : ℤ → ℝ} (hf0 : ∀ m, 0 ≤ f m)
    (hf1 : HasSum f 1) (t : ℝ) :
    charFun (U2.latticeLaw x f hf0 hf1 : Measure ℝ) t =
      ∑' m, (f m : ℂ) * cexp ((t : ℂ) * (U2.lamm x m : ℂ) * I) := by
  rw [charFun_apply_real, U2.latticeLaw, ProbabilityMeasure.coe_mk,
    integral_map (U2.measurable_lamm x).aemeasurable (by fun_prop)]
  rw [PMF.integral_eq_tsum]
  · congr 1
    funext m
    change (ENNReal.ofReal (f m)).toReal • _ = _
    rw [ENNReal.toReal_ofReal (hf0 m), Complex.real_smul]
  · refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (Eventually.of_forall (fun m => ?_))
    rw [show (t : ℂ) * (U2.lamm x m : ℂ) * I = ((t * U2.lamm x m : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]

def centeredWalkLaw (N : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : ProbabilityMeasure ℝ :=
  U2.latticeLaw (N * ε) (U2.extZ (law ε N)) (U2.extZ_nonneg (law_nonneg h0 h1 N))
    (U2.extZ_hasSum (U2.hasSum_law ε N))

lemma charFun_centeredWalkLaw (N : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hx : (N : ℝ) * ε ≠ 0) (t : ℝ) :
    charFun (centeredWalkLaw N ε h0 h1 : Measure ℝ) t =
      cexp (-((t : ℂ) * I * (Real.log (N * ε) : ℂ))) * walkChar ε (t / (N * ε)) N := by
  unfold centeredWalkLaw
  rw [charFun_latticeLaw]
  set x : ℝ := N * ε
  have hs : Summable (fun m => (law ε N m : ℂ) * eI (t / x) m) := by
    apply Summable.of_norm_bounded (U2.hasSum_law ε N).summable
    intro m
    rw [norm_mul, norm_eI, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (law_nonneg h0 h1 N m)]
  have he (m : ℕ) : cexp ((t : ℂ) * (U2.lamm x (m : ℤ) : ℂ) * I) =
      cexp (-((t : ℂ) * I * (Real.log x : ℂ))) * eI (t / x) m := by
    rw [eI, ← Complex.exp_add]
    congr 1
    unfold U2.lamm
    push_cast
    have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    field_simp
    ring
  have hp : HasSum (fun m : ℕ => (U2.extZ (law ε N) (m : ℤ) : ℂ) *
      cexp ((t : ℂ) * (U2.lamm x (m : ℤ) : ℂ) * I))
      (cexp (-((t : ℂ) * I * (Real.log x : ℂ))) * walkChar ε (t / x) N) := by
    simp only [U2.extZ_natCast, he]
    simpa only [walkChar, mul_left_comm] using
      hs.hasSum.mul_left (cexp (-((t : ℂ) * I * (Real.log x : ℂ))))
  have hn : HasSum (fun m : ℕ => (U2.extZ (law ε N) (-((m : ℤ) + 1)) : ℂ) *
      cexp ((t : ℂ) * (U2.lamm x (-((m : ℤ) + 1)) : ℂ) * I)) 0 := by
    simp only [U2.extZ_neg_succ, Complex.ofReal_zero, zero_mul]
    exact hasSum_zero
  have hsZ := HasSum.of_nat_of_neg_add_one
    (f := fun m : ℤ => (U2.extZ (law ε N) m : ℂ) *
      cexp ((t : ℂ) * (U2.lamm x m : ℂ) * I)) hp hn
  simpa using hsZ.tsum_eq

lemma PsiN_eq (N : ℕ) (θ : ℝ) : PsiN N θ = U2.psiN N θ := by
  have h := U2.cp_exponent_eq N 1 θ
  simp only [Complex.ofReal_one, one_mul] at h
  rw [← h]
  unfold PsiN
  apply sum_congr rfl
  intro d hd
  simp only [eI]
  push_cast
  ring

theorem centered_char_error (hES : EfronSteinHyp) {N : ℕ} (hN : 1 ≤ N)
    {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hx : (N : ℝ) * ε ≠ 0) (t : ℝ) :
    ‖charFun (centeredWalkLaw N ε h0 h1 : Measure ℝ) t -
      cexp (U2.cpExponent N (N * ε) t)‖ ≤ 2 * U2.deltaB N ε := by
  rw [charFun_centeredWalkLaw N ε h0 h1 hx]
  have he : cexp (U2.cpExponent N (N * ε) t) =
      cexp (-((t : ℂ) * I * (Real.log (N * ε) : ℂ))) *
      cexp (((N : ℝ) * ε : ℝ) * PsiN N (t / (N * ε))) := by
    rw [← Complex.exp_add, PsiN_eq]
    congr 1
    unfold U2.cpExponent
    ring
  rw [he, ← mul_sub, norm_mul]
  have hn : ‖cexp (-((t : ℂ) * I * (Real.log (N * ε) : ℂ)))‖ = 1 := by
    rw [show -((t : ℂ) * I * (Real.log (N * ε) : ℂ)) =
      ((-t * Real.log (N * ε) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hn, one_mul]
  exact walkChar_error hES h0 h1 hN _

theorem tendsto_cpExponent (N : ℕ → ℕ) (x : ℕ → ℝ)
    (hN : ∀ᶠ n in atTop, 1 ≤ N n) (hx : Tendsto x atTop atTop)
    (hr : Tendsto (fun n => x n / N n) atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => U2.cpExponent (N n) (x n) t) atTop (𝓝 (U2.landauB t)) := by
  have hi : Tendsto (fun n => (x n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hx
  have hl : Tendsto (fun n => Real.log (x n) / x n) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hx
  have hb : Tendsto (fun n => t ^ 2 / x n *
      (0.631 * (|Real.log (|t|)| + Real.log (x n)) + 1.53) + 2 * x n / N n)
      atTop (𝓝 0) := by
    have h := ((hi.const_mul (t ^ 2 * (0.631 * |Real.log (|t|)| + 1.53))).add
      (hl.const_mul (t ^ 2 * 0.631))).add (hr.const_mul 2)
    simp only [mul_zero, add_zero] at h
    convert h using 1
    funext n
    simp only [div_eq_mul_inv]
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_ hb
  filter_upwards [hN, hx.eventually_ge_atTop 1, hx.eventually_ge_atTop (|t| / Real.pi)]
    with n hn hx1 ht
  apply U2.norm_cpExponent_sub_landauB_le hn hx1
  have := (div_le_iff₀ Real.pi_pos).mp ht
  nlinarith

/-- Theorem 3.9(c), with `x² log² N/N → 0`. The density hypothesis concerns only the
fixed limiting law, and is discharged in `thm_landau_quadratic_final` below. -/
theorem thm_landau_quadratic (hES : EfronSteinHyp) (hL : U2.LandauDensityHyp)
    (N : ℕ → ℕ) (ε : ℕ → ℝ) (h0 : ∀ n, 0 ≤ ε n) (h1 : ∀ n, ε n ≤ 1)
    (hx : Tendsto (fun n => (N n : ℝ) * ε n) atTop atTop)
    (h2 : Tendsto (fun n => ((N n : ℝ) * ε n) ^ 2 * Real.log (N n) ^ 2 / N n) atTop (𝓝 0)) :
    Tendsto (fun n => centeredWalkLaw (N n) (ε n) (h0 n) (h1 n))
      atTop (𝓝 (U2.landauLaw hL)) := by
  have he1 : ∀ᶠ n in atTop, ε n ≤ 1 := Eventually.of_forall h1
  have hv := eventually_regime N ε he1 hx h2
  have hN : ∀ᶠ n in atTop, 1 ≤ N n := by
    filter_upwards [hv] with n hn
    have hnn : (0 : ℝ) ≤ N n := Nat.cast_nonneg _
    have hxN : (N n : ℝ) * ε n ≤ N n := mul_le_of_le_one_right hnn (h1 n)
    exact_mod_cast (show (1 : ℝ) ≤ N n by linarith [hn.1])
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  rw [U2.charFun_landauLaw]
  have hp := (Complex.continuous_exp.tendsto (U2.landauB t)).comp
    (tendsto_cpExponent N (fun n => N n * ε n) hN hx (tendsto_x_div_N N ε he1 hx h2) t)
  have hd : Tendsto (fun n => charFun (centeredWalkLaw (N n) (ε n) (h0 n) (h1 n) : Measure ℝ) t -
      cexp (U2.cpExponent (N n) (N n * ε n) t)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using (tendsto_deltaB N ε he1 hx h2).const_mul 2)
    filter_upwards [hN, hv] with n hn hh
    exact centered_char_error hES hn (h0 n) (h1 n) (by linarith [hh.1]) t
  have h := hd.add hp
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using h

/-- The actual-walk quadratic-range weak limit. Compared with the old local-limit
route, Scheffé's lemma is no longer an input. The remaining three classical
interfaces are inherited from the existing library. -/
theorem thm_landau_quadratic_final (hInv : U2.LatticeFourierInversionHyp)
    (hCP : CPCharHyp) (hES : EfronSteinHyp)
    (N : ℕ → ℕ) (ε : ℕ → ℝ) (h0 : ∀ n, 0 ≤ ε n) (h1 : ∀ n, ε n ≤ 1)
    (hx : Tendsto (fun n => (N n : ℝ) * ε n) atTop atTop)
    (h2 : Tendsto (fun n => ((N n : ℝ) * ε n) ^ 2 * Real.log (N n) ^ 2 / N n) atTop (𝓝 0)) :
    Tendsto (fun n => centeredWalkLaw (N n) (ε n) (h0 n) (h1 n))
      atTop (𝓝 (U2.landauLaw (U2.landauDensityHyp_of_U1 hInv hCP))) :=
  thm_landau_quadratic hES (U2.landauDensityHyp_of_U1 hInv hCP) N ε h0 h1 hx h2

end
end Kagey131.PaperD.RevisionWeak
