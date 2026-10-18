import PaperD.U6_Cert

/-!
# Paper D, track U6: Lemma 3.10 (`lem:landau-mode`), the mode of the Landau density

`fL` is the Landau density in the paper's real-integral form
`f_L(λ) = (1/π) ∫_0^∞ e^{-s log s - λ s} sin(π s) ds` (`PaperD.U6_Landau`), and
`fL1 = Fk 1 / π`, `fL2 = Fk 2 / π`, `fL3 = Fk 3 / π` are its first three derivatives
(`hasDerivAt_fL'`, `hasDerivAt_fL1`, `hasDerivAt_fL2`).

* `fL1_at_a`, `fL1_at_b`, `fL1_at_c1`, `fL1_at_c2`: the four enclosures of `f_L'` of the paper
  (kernel-checked Taylor-model integration, `PaperD.U6_Cert`);
* `fL2_bounds`: `-0.0792 ≤ f_L'' ≤ -0.0786` on `[-0.2229, -0.2227]`;
* `lem_landau_mode`: Lemma 3.10 (a), (b), (c), under the hypothesis `Unimodal fL`.

The only hypothesis is the unimodality of `f_L` (Yamazato 1978, via the self-decomposability of
the Landau law, paper Appendix, proof of Theorem 3.9).
-/

namespace Kagey131.PaperD.U6

open Real MeasureTheory Set Filter

/-- `f_L'`. -/
noncomputable def fL1 (lam : ℝ) : ℝ := Fk 1 lam / Real.pi
/-- `f_L''`. -/
noncomputable def fL2 (lam : ℝ) : ℝ := Fk 2 lam / Real.pi
/-- `f_L'''`. -/
noncomputable def fL3 (lam : ℝ) : ℝ := Fk 3 lam / Real.pi

theorem hasDerivAt_fL' (lam : ℝ) : HasDerivAt fL (fL1 lam) lam := hasDerivAt_fL lam
theorem hasDerivAt_fL1 (lam : ℝ) : HasDerivAt fL1 (fL2 lam) lam := hasDerivAt_Fk_div 1 lam
theorem hasDerivAt_fL2 (lam : ℝ) : HasDerivAt fL2 (fL3 lam) lam := hasDerivAt_Fk_div 2 lam

theorem deriv_fL : deriv fL = fL1 := funext fun l => (hasDerivAt_fL' l).deriv
theorem deriv_fL1 : deriv fL1 = fL2 := funext fun l => (hasDerivAt_fL1 l).deriv
theorem deriv_fL2 : deriv fL2 = fL3 := funext fun l => (hasDerivAt_fL2 l).deriv

theorem continuous_fL : Continuous fL :=
  continuous_iff_continuousAt.mpr fun l => (hasDerivAt_fL' l).continuousAt
theorem continuous_fL1 : Continuous fL1 :=
  continuous_iff_continuousAt.mpr fun l => (hasDerivAt_fL1 l).continuousAt
theorem continuous_fL2 : Continuous fL2 :=
  continuous_iff_continuousAt.mpr fun l => (hasDerivAt_fL2 l).continuousAt

/-- `f_L' = -(1/π) ∫ s e^{-s log s - λ s} sin(π s) ds`. -/
theorem fL1_eq (lam : ℝ) : fL1 lam = -(∫ s in Ioi 0, integrand 1 lam true s) / Real.pi := by
  unfold fL1; rw [Fk_eq]; ring

theorem fL2_eq (lam : ℝ) : fL2 lam = (∫ s in Ioi 0, integrand 2 lam true s) / Real.pi := by
  unfold fL2; rw [Fk_eq]; ring

/-! ### The integrals -/

theorem I1_at_a : -2.900623e-5 ≤ ∫ s in Ioi 0, integrand 1 (-0.2229) true s ∧
    ∫ s in Ioi 0, integrand 1 (-0.2229) true s ≤ -2.900621e-5 := by
  have h := Ioi_of_chunks (mkP_ok (-2229) 1 true (by norm_num)) sA1 sA2 sA3 sA4 (by decide)
    (by simp only [mkP]; norm_num) (by simp only [mkP]; norm_num)
  simp only [mkP, if_true] at h
  have e : ((-2229 : ℤ) : ℝ) / ((10000 : ℕ) : ℝ) = -0.2229 := by norm_num
  rw [e, D_eq] at h
  have hp := Real.pi_lt_d2
  have he := exp_neg_32_le
  obtain ⟨h1, h2⟩ := h
  constructor
  · refine le_trans ?_ h1; norm_num; nlinarith
  · refine le_trans h2 ?_; norm_num; nlinarith

theorem I1_at_b : 2.056691e-5 ≤ ∫ s in Ioi 0, integrand 1 (-0.2227) true s ∧
    ∫ s in Ioi 0, integrand 1 (-0.2227) true s ≤ 2.056693e-5 := by
  have h := Ioi_of_chunks (mkP_ok (-2227) 1 true (by norm_num)) sB1 sB2 sB3 sB4 (by decide)
    (by simp only [mkP]; norm_num) (by simp only [mkP]; norm_num)
  simp only [mkP, if_true] at h
  have e : ((-2227 : ℤ) : ℝ) / ((10000 : ℕ) : ℝ) = -0.2227 := by norm_num
  rw [e, D_eq] at h
  have hp := Real.pi_lt_d2
  have he := exp_neg_32_le
  obtain ⟨h1, h2⟩ := h
  constructor
  · refine le_trans ?_ h1; norm_num; nlinarith
  · refine le_trans h2 ?_; norm_num; nlinarith

theorem I1_at_c1 : -2.1702e-9 ≤ ∫ s in Ioi 0, integrand 1 (-0.22278299) true s ∧
    ∫ s in Ioi 0, integrand 1 (-0.22278299) true s ≤ -2.164e-9 := by
  have h := Ioi_of_chunks (mkP_ok (-22278299) 1 true (by norm_num)) sC1 sC2 sC3 sC4 (by decide)
    (by simp only [mkP]; norm_num) (by simp only [mkP]; norm_num)
  simp only [mkP, if_true] at h
  have e : ((-22278299 : ℤ) : ℝ) / ((100000000 : ℕ) : ℝ) = -0.22278299 := by norm_num
  rw [e, D_eq] at h
  have hp := Real.pi_lt_d2
  have he := exp_neg_32_le
  obtain ⟨h1, h2⟩ := h
  constructor
  · refine le_trans ?_ h1; norm_num; nlinarith
  · refine le_trans h2 ?_; norm_num; nlinarith

theorem I1_at_c2 : 2.787e-9 ≤ ∫ s in Ioi 0, integrand 1 (-0.22278297) true s ∧
    ∫ s in Ioi 0, integrand 1 (-0.22278297) true s ≤ 2.793e-9 := by
  have h := Ioi_of_chunks (mkP_ok (-22278297) 1 true (by norm_num)) sE1 sE2 sE3 sE4 (by decide)
    (by simp only [mkP]; norm_num) (by simp only [mkP]; norm_num)
  simp only [mkP, if_true] at h
  have e : ((-22278297 : ℤ) : ℝ) / ((100000000 : ℕ) : ℝ) = -0.22278297 := by norm_num
  rw [e, D_eq] at h
  have hp := Real.pi_lt_d2
  have he := exp_neg_32_le
  obtain ⟨h1, h2⟩ := h
  constructor
  · refine le_trans ?_ h1; norm_num; nlinarith
  · refine le_trans h2 ?_; norm_num; nlinarith

theorem I2_at_mid : -0.2478657137 ≤ ∫ s in Ioi 0, integrand 2 (-0.2228) true s ∧
    ∫ s in Ioi 0, integrand 2 (-0.2228) true s ≤ -0.2478657136 := by
  have h := Ioi_of_chunks (mkP_ok (-2228) 2 true (by norm_num)) sF1 sF2 sF3 sF4 (by decide)
    (by simp only [mkP]; norm_num) (by simp only [mkP]; norm_num)
  simp only [mkP, if_true] at h
  have e : ((-2228 : ℤ) : ℝ) / ((10000 : ℕ) : ℝ) = -0.2228 := by norm_num
  rw [e, D_eq] at h
  have hp := Real.pi_lt_d2
  have he := exp_neg_32_le
  obtain ⟨h1, h2⟩ := h
  constructor
  · refine le_trans ?_ h1; norm_num; nlinarith
  · refine le_trans h2 ?_; norm_num; nlinarith

theorem J3_at_a : ∫ s in Ioi 0, integrand 3 (-0.2229) false s ≤ 7.0531 := by
  have h := Ioi_of_chunks (mkP_ok (-2229) 3 false (by norm_num)) sJ1 sJ2 sJ3 sJ4 (by decide)
    (by simp only [mkP]; norm_num) (by simp only [mkP]; norm_num)
  simp only [mkP] at h
  have e : ((-2229 : ℤ) : ℝ) / ((10000 : ℕ) : ℝ) = -0.2229 := by norm_num
  rw [e, D_eq] at h
  have he := exp_neg_32_le
  refine le_trans h.2 ?_
  norm_num; nlinarith

theorem I0_at_mid : 0.5675 ≤ ∫ s in Ioi 0, integrand 0 (-0.2228) true s := by
  have h := Ioi_of_chunks (mkP_ok (-2228) 0 true (by norm_num)) sG1 sG2 sG3 sG4 (by decide)
    (by simp only [mkP]; norm_num) (by simp only [mkP]; norm_num)
  simp only [mkP, if_true] at h
  have e : ((-2228 : ℤ) : ℝ) / ((10000 : ℕ) : ℝ) = -0.2228 := by norm_num
  rw [e, D_eq] at h
  have hp := Real.pi_lt_d2
  have he := exp_neg_32_le
  refine le_trans ?_ h.1
  norm_num; nlinarith

/-- `f_L(-0.2228) ≥ 0.1806`. -/
theorem fL_at_mid : 0.1806 ≤ fL (-0.2228) := by
  have h := I0_at_mid
  have hp2 := Real.pi_lt_d6
  unfold fL; rw [Fk_eq, pow_zero, one_mul, le_div_iff₀ Real.pi_pos]
  nlinarith

/-! ### `f_L'` at the four points and `f_L''` on the bracket -/

/-- `f_L'(-0.2229) ∈ [9.232·10⁻⁶, 9.234·10⁻⁶]`. -/
theorem fL1_at_a : 9.232e-6 ≤ fL1 (-0.2229) ∧ fL1 (-0.2229) ≤ 9.234e-6 := by
  have h := I1_at_a
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  rw [fL1_eq]
  constructor
  · rw [le_div_iff₀ Real.pi_pos]; nlinarith [h.2]
  · rw [div_le_iff₀ Real.pi_pos]; nlinarith [h.1]

/-- `f_L'(-0.2227) ∈ [-6.548·10⁻⁶, -6.546·10⁻⁶]`. -/
theorem fL1_at_b : -6.548e-6 ≤ fL1 (-0.2227) ∧ fL1 (-0.2227) ≤ -6.546e-6 := by
  have h := I1_at_b
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  rw [fL1_eq]
  constructor
  · rw [le_div_iff₀ Real.pi_pos]; nlinarith [h.2]
  · rw [div_le_iff₀ Real.pi_pos]; nlinarith [h.1]

/-- `f_L'(-0.22278299) ∈ [6.88·10⁻¹⁰, 6.91·10⁻¹⁰]`, in particular positive. -/
theorem fL1_at_c1 : 6.88e-10 ≤ fL1 (-0.22278299) ∧ fL1 (-0.22278299) ≤ 6.91e-10 := by
  have h := I1_at_c1
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  rw [fL1_eq]
  constructor
  · rw [le_div_iff₀ Real.pi_pos]; nlinarith [h.2]
  · rw [div_le_iff₀ Real.pi_pos]; nlinarith [h.1]

/-- `f_L'(-0.22278297) ∈ [-8.90·10⁻¹⁰, -8.87·10⁻¹⁰]`, in particular negative. -/
theorem fL1_at_c2 : -8.90e-10 ≤ fL1 (-0.22278297) ∧ fL1 (-0.22278297) ≤ -8.87e-10 := by
  have h := I1_at_c2
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  rw [fL1_eq]
  constructor
  · rw [le_div_iff₀ Real.pi_pos]; nlinarith [h.2]
  · rw [div_le_iff₀ Real.pi_pos]; nlinarith [h.1]

/-- `f_L''(-0.2228) ∈ [-0.0788982, -0.0788980]`. -/
theorem fL2_at_mid : -0.0788982 ≤ fL2 (-0.2228) ∧ fL2 (-0.2228) ≤ -0.0788980 := by
  have h := I2_at_mid
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  rw [fL2_eq]
  constructor
  · rw [le_div_iff₀ Real.pi_pos]; nlinarith [h.1]
  · rw [div_le_iff₀ Real.pi_pos]; nlinarith [h.2]

/-- `|f_L'''(μ)| ≤ 2.246` for `μ ≥ -0.2229`. -/
theorem abs_fL3_le {mu : ℝ} (hmu : -0.2229 ≤ mu) : |fL3 mu| ≤ 2.246 := by
  have hJ := J3_at_a
  have hle : |Fk 3 mu| ≤ ∫ s in Ioi 0, integrand 3 (-0.2229) false s := by
    rw [Fk_eq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, ← Real.norm_eq_abs]
    have hb := integrableOn_integrand 3 (-0.2229) false
    refine norm_integral_le_of_norm_le (μ := volume.restrict (Ioi 0)) hb
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun s hs => ?_)))
    rw [Real.norm_eq_abs]
    refine (abs_integrand_le hs 3 mu true).trans ?_
    unfold integrand
    simp only [Bool.false_eq_true, if_false, mul_one]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (le_of_lt hs) 3)
    apply Real.exp_le_exp.mpr
    have : (-0.2229 : ℝ) * s ≤ mu * s := mul_le_mul_of_nonneg_right hmu (le_of_lt hs)
    linarith
  unfold fL3
  rw [abs_div, abs_of_pos Real.pi_pos, div_le_iff₀ Real.pi_pos]
  have hp1 := Real.pi_gt_d6
  nlinarith

/-- Lemma 3.10(b), second half: `-0.0792 ≤ f_L''(λ) ≤ -0.0786` for `-0.2229 ≤ λ ≤ -0.2227`. -/
theorem fL2_bounds {lam : ℝ} (h1 : -0.2229 ≤ lam) (h2 : lam ≤ -0.2227) :
    -0.0792 ≤ fL2 lam ∧ fL2 lam ≤ -0.0786 := by
  have hm := fL2_at_mid
  -- mean value theorem between `-0.2228` and `λ`
  have hmvt : |fL2 lam - fL2 (-0.2228)| ≤ 2.246 * |lam - (-0.2228)| := by
    rcases lt_trichotomy lam (-0.2228) with hlt | heq | hgt
    · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope fL2 fL3 hlt
        continuous_fL2.continuousOn (fun x _ => hasDerivAt_fL2 x)
      have hb := abs_fL3_le (mu := ξ) (by linarith [hξ.1])
      have : fL2 lam - fL2 (-0.2228) = fL3 ξ * (lam - (-0.2228)) := by
        rw [hd]; field_simp; ring
      rw [this, abs_mul]; exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    · rw [heq]; simp
    · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope fL2 fL3 hgt
        continuous_fL2.continuousOn (fun x _ => hasDerivAt_fL2 x)
      have hb := abs_fL3_le (mu := ξ) (by linarith [hξ.1])
      have : fL2 lam - fL2 (-0.2228) = fL3 ξ * (lam - (-0.2228)) := by
        rw [hd]; field_simp
      rw [this, abs_mul]; exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have hd : |lam - (-0.2228)| ≤ 0.0001 := by rw [abs_le]; constructor <;> linarith
  rw [abs_le] at hmvt
  constructor <;> nlinarith [abs_nonneg (lam - (-0.2228))]

/-! ### The lemma -/

/-- A function on `ℝ` is unimodal if it is nondecreasing up to some point `m` and
nonincreasing from `m` on. -/
def Unimodal (f : ℝ → ℝ) : Prop := ∃ m, MonotoneOn f (Iic m) ∧ AntitoneOn f (Ici m)

/-- Paper, Appendix, Step 3: `f_L'` has exactly one zero `λ_L` in `[-0.2229, -0.2227]`, it lies
in `(-0.22278299, -0.22278297)`, and `f_L'` is strictly decreasing on `[-0.2229, -0.2227]`. -/
theorem fL1_zero : ∃ lamL, (-0.22278299 < lamL ∧ lamL < -0.22278297) ∧ fL1 lamL = 0 ∧
    StrictAntiOn fL1 (Icc (-0.2229) (-0.2227)) := by
  have hanti : StrictAntiOn fL1 (Icc (-0.2229) (-0.2227)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_fL1.continuousOn (fun x hx => ?_)
    rw [interior_Icc] at hx
    rw [deriv_fL1]
    have := fL2_bounds hx.1.le hx.2.le
    linarith [this.2]
  have h1 := fL1_at_c1
  have h2 := fL1_at_c2
  have hmem : (0 : ℝ) ∈ Ioo (fL1 (-0.22278297)) (fL1 (-0.22278299)) := ⟨by linarith, by linarith⟩
  obtain ⟨lamL, hL, hz⟩ := intermediate_value_Ioo' (by norm_num) continuous_fL1.continuousOn hmem
  exact ⟨lamL, hL, hz, hanti⟩

/-- Paper, Appendix, Step 4 (first half): `f_L(λ_L) - f_L(λ) ≥ 0.039 (λ - λ_L)²` on
`[-0.2229, -0.2227]`. -/
theorem quad_on_bracket {lamL : ℝ} (hL1 : -0.2229 ≤ lamL) (hL2 : lamL ≤ -0.2227)
    (hz : fL1 lamL = 0) {lam : ℝ} (h1 : -0.2229 ≤ lam) (h2 : lam ≤ -0.2227) :
    0.039 * (lam - lamL) ^ 2 ≤ fL lamL - fL lam := by
  have hgd : ∀ x, HasDerivAt (fun x => fL lamL - fL x - 0.039 * (x - lamL) ^ 2)
      (-fL1 x - 0.078 * (x - lamL)) x := by
    intro x
    have h := ((hasDerivAt_const x (fL lamL)).sub (hasDerivAt_fL' x)).sub
      ((((hasDerivAt_id' x).sub_const lamL).pow 2).const_mul (0.039 : ℝ))
    refine h.congr_deriv ?_
    push_cast; ring
  have hg'd : ∀ x, HasDerivAt (fun x => -fL1 x - 0.078 * (x - lamL)) (-fL2 x - 0.078) x := by
    intro x
    have h := (hasDerivAt_fL1 x).neg.sub (((hasDerivAt_id' x).sub_const lamL).const_mul (0.078 : ℝ))
    refine h.congr_deriv ?_
    ring
  have hmono' : MonotoneOn (fun x => -fL1 x - 0.078 * (x - lamL)) (Icc (-0.2229) (-0.2227)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr fun x => (hg'd x).continuousAt).continuousOn
      (fun x _ => (hg'd x).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
    rw [interior_Icc] at hx
    rw [(hg'd x).deriv]
    have := fL2_bounds hx.1.le hx.2.le
    linarith [this.2]
  have hg'0 : -fL1 lamL - 0.078 * (lamL - lamL) = 0 := by rw [hz]; ring
  have hcont : Continuous (fun x => fL lamL - fL x - 0.039 * (x - lamL) ^ 2) :=
    continuous_iff_continuousAt.mpr fun x => (hgd x).continuousAt
  have key : 0 ≤ fL lamL - fL lam - 0.039 * (lam - lamL) ^ 2 := by
    rcases le_total lamL lam with hle | hle
    · have hm : MonotoneOn (fun x => fL lamL - fL x - 0.039 * (x - lamL) ^ 2)
          (Icc lamL (-0.2227)) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont.continuousOn
          (fun x _ => (hgd x).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
        rw [interior_Icc] at hx
        rw [(hgd x).deriv]
        have := hmono' ⟨hL1, hL2⟩ ⟨by linarith [hx.1], hx.2.le⟩ hx.1.le
        simp only at this
        linarith
      have := hm ⟨le_rfl, hL2⟩ ⟨hle, h2⟩ hle
      simp only at this
      linarith
    · have hm : AntitoneOn (fun x => fL lamL - fL x - 0.039 * (x - lamL) ^ 2)
          (Icc (-0.2229) lamL) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont.continuousOn
          (fun x _ => (hgd x).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
        rw [interior_Icc] at hx
        rw [(hgd x).deriv]
        have := hmono' ⟨hx.1.le, by linarith [hx.2]⟩ ⟨hL1, hL2⟩ hx.2.le
        simp only at this
        linarith
      have := hm ⟨h1, hle⟩ ⟨hL1, le_rfl⟩ hle
      simp only at this
      linarith
  linarith

/-- **Lemma 3.10** (`lem:landau-mode`), under the unimodality of `f_L`.

(a) `f_L` has exactly one mode `λ_L` (its unique maximizer; `f_L` is nondecreasing up to `λ_L`
and nonincreasing after it), and `-0.22278299 < λ_L < -0.22278297`.

(b) `f_L'(λ_L) = 0`, and `-0.0792 ≤ f_L''(λ) ≤ -0.0786` for `-0.2229 ≤ λ ≤ -0.2227`, stated with
`deriv (deriv fL)` (which equals `fL2 = Fk 2 / π` by `deriv_fL`, `deriv_fL1`).

(c) `f_L(λ_L) - f_L(λ) ≥ κ_L min{1, (λ - λ_L)²}` for every real `λ`, with `κ_L = 2.6·10⁻¹⁰`.

Also `f_L(λ_L) ≥ 0.1806 > 0` (used in Theorem 3.21, Step 3). -/
theorem lem_landau_mode (hU : Unimodal fL) :
    ∃ lamL : ℝ,
      ((-0.22278299 < lamL ∧ lamL < -0.22278297) ∧
        (∀ lam, fL lam ≤ fL lamL) ∧ (∀ mu, (∀ lam, fL lam ≤ fL mu) → mu = lamL) ∧
        MonotoneOn fL (Iic lamL) ∧ AntitoneOn fL (Ici lamL) ∧ 0.1806 ≤ fL lamL) ∧
      (HasDerivAt fL 0 lamL ∧
        ∀ lam, -0.2229 ≤ lam → lam ≤ -0.2227 →
          -0.0792 ≤ deriv (deriv fL) lam ∧ deriv (deriv fL) lam ≤ -0.0786) ∧
      ∀ lam, 2.6e-10 * min 1 ((lam - lamL) ^ 2) ≤ fL lamL - fL lam := by
  obtain ⟨lamL, ⟨hc1, hc2⟩, hz, _⟩ := fL1_zero
  have hL1 : -0.2229 ≤ lamL := by linarith
  have hL2 : lamL ≤ -0.2227 := by linarith
  have quad := fun lam (h1 : -0.2229 ≤ lam) (h2 : lam ≤ -0.2227) =>
    quad_on_bracket hL1 hL2 hz h1 h2
  -- the unimodality point is λ_L
  obtain ⟨m, hmono, hanti⟩ := hU
  have hm : m = lamL := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- m < λ_L: f_L is nonincreasing on [max m a, ∞)
      set mu := max m (-0.2229)
      have hmu1 : mu < lamL := max_lt hlt (by linarith)
      have hle : fL lamL ≤ fL mu := hanti (Set.mem_Ici.mpr (le_max_left _ _))
        (Set.mem_Ici.mpr hlt.le) hmu1.le
      have hq := quad mu (le_max_right _ _) (by linarith)
      have : 0 < (mu - lamL) ^ 2 := by have : mu - lamL ≠ 0 := by linarith
                                       positivity
      linarith
    · -- λ_L < m: f_L is nondecreasing on (-∞, min m b]
      set mu := min m (-0.2227)
      have hmu1 : lamL < mu := lt_min hgt (by linarith)
      have hle : fL lamL ≤ fL mu := hmono (Set.mem_Iic.mpr hgt.le)
        (Set.mem_Iic.mpr (min_le_left _ _)) hmu1.le
      have hq := quad mu (by linarith) (min_le_right _ _)
      have : 0 < (mu - lamL) ^ 2 := by have : mu - lamL ≠ 0 := by linarith
                                       positivity
      linarith
  subst hm
  -- (c)
  have hc : ∀ lam, 2.6e-10 * min 1 ((lam - m) ^ 2) ≤ fL m - fL lam := by
    intro lam
    have hmin1 : min 1 ((lam - m) ^ 2) ≤ 1 := min_le_left _ _
    have hmin2 : min 1 ((lam - m) ^ 2) ≤ (lam - m) ^ 2 := min_le_right _ _
    rcases le_or_gt lam (-0.2227) with hb | hb
    · rcases le_or_gt (-0.2229) lam with ha | ha
      · have := quad lam ha hb
        nlinarith [sq_nonneg (lam - m)]
      · -- λ < a ≤ λ_L
        have h1 := hmono (show lam ∈ Iic m by simp only [mem_Iic]; linarith)
          (show (-0.2229 : ℝ) ∈ Iic m from hL1) ha.le
        have h2 := quad (-0.2229) le_rfl (by norm_num)
        have h3 : (0.00011701 : ℝ) ^ 2 ≤ (-0.2229 - m) ^ 2 := by
          rw [sq, sq]; nlinarith
        nlinarith
    · -- b < λ, λ_L ≤ b
      have h1 := hanti (show (-0.2227 : ℝ) ∈ Ici m from hL2)
        (show lam ∈ Ici m by simp only [mem_Ici]; linarith) hb.le
      have h2 := quad (-0.2227) (by norm_num) le_rfl
      have h3 : (0.00008297 : ℝ) ^ 2 ≤ (-0.2227 - m) ^ 2 := by
        rw [sq, sq]; nlinarith
      nlinarith
  have hmax : ∀ lam, fL lam ≤ fL m := by
    intro lam
    have := hc lam
    have : 0 ≤ min 1 ((lam - m) ^ 2) := le_min zero_le_one (sq_nonneg _)
    linarith
  refine ⟨m, ⟨⟨hc1, hc2⟩, hmax, fun mu hmu => ?_, hmono, hanti, ?_⟩, ⟨?_, ?_⟩, hc⟩
  · have h1 := hmu m
    have h2 := hc mu
    have h3 : min 1 ((mu - m) ^ 2) ≤ 0 := by nlinarith
    have h4 : (mu - m) ^ 2 ≤ 0 := by
      rcases min_choice 1 ((mu - m) ^ 2) with h | h
      · rw [h] at h3; linarith
      · rw [h] at h3; exact h3
    have : mu - m = 0 := by nlinarith [sq_nonneg (mu - m)]
    linarith
  · exact fL_at_mid.trans (hmax _)
  · rw [← hz]; exact hasDerivAt_fL' m
  · intro lam h1 h2; rw [deriv_fL, deriv_fL1]; exact fL2_bounds h1 h2

/-! ### The Fourier form of `f_L` -/

/-- The exponent `B(t) = -i t log|t| - (π/2)|t|` of Section 1 of the paper. -/
noncomputable def landauB (t : ℝ) : ℂ :=
  -Complex.I * t * Real.log |t| - (Real.pi / 2 * |t| : ℝ)

/-- The Landau density in the Fourier form of Section 1 of the paper,
`f_L(λ) = (1/2π) ∫ e^{-iλt} e^{B(t)} dt`.

We take the real part of the complex integral. The integral is in fact real, since
`B(-t) = conj (B t)` makes the integrand at `-t` the conjugate of the integrand at `t`; this is
not proved here, and nothing depends on it, because `LandauFacts.real_integral` fixes the value
of `fLFourier` directly. -/
noncomputable def fLFourier (lam : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (∫ t : ℝ, Complex.exp (-Complex.I * lam * t) * Complex.exp (landauB t)).re

/-- The two classical facts about the Landau density that Lemma 3.10 uses, as named
hypotheses: the real-integral representation (Möhle 2005, Eq. (4.3); the contour rotation of
the paper's Appendix, Step 1) and unimodality (Yamazato 1978, for the self-decomposable law
with characteristic function `e^B`, paper Appendix, proof of Theorem 3.9). -/
structure LandauFacts : Prop where
  real_integral : ∀ lam, fLFourier lam = fL lam
  unimodal : Unimodal fLFourier

/-- Lemma 3.10 for the Fourier form of `f_L`, from `LandauFacts`. -/
theorem lem_landau_mode_fourier (H : LandauFacts) :
    ∃ lamL : ℝ,
      ((-0.22278299 < lamL ∧ lamL < -0.22278297) ∧
        (∀ lam, fLFourier lam ≤ fLFourier lamL) ∧
        (∀ mu, (∀ lam, fLFourier lam ≤ fLFourier mu) → mu = lamL) ∧
        MonotoneOn fLFourier (Iic lamL) ∧ AntitoneOn fLFourier (Ici lamL) ∧
        0.1806 ≤ fLFourier lamL) ∧
      (HasDerivAt fLFourier 0 lamL ∧
        ∀ lam, -0.2229 ≤ lam → lam ≤ -0.2227 →
          -0.0792 ≤ deriv (deriv fLFourier) lam ∧ deriv (deriv fLFourier) lam ≤ -0.0786) ∧
      ∀ lam, 2.6e-10 * min 1 ((lam - lamL) ^ 2) ≤ fLFourier lamL - fLFourier lam := by
  have he : fLFourier = fL := funext H.real_integral
  have hU : Unimodal fL := he ▸ H.unimodal
  rw [he]
  exact lem_landau_mode hU

end Kagey131.PaperD.U6
