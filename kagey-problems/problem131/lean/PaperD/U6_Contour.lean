import PaperD.U6_Lemma

/-!
# Paper D, track U6: the real integral for the Landau density (contour rotation)

The paper writes the Landau density in two forms. Section 1 defines it by Fourier inversion,
`f_L(λ) = (1/2π) ∫_ℝ e^{-iλt} e^{B(t)} dt` with `B(t) = -it log|t| - (π/2)|t|` (`fLFourier`).
Appendix, proof of Lemma 3.10, Step 1, rotates the contour to get the real integral
`f_L(λ) = (1/π) ∫_0^∞ e^{-s log s - λ s} sin(π s) ds` (`fL`, eq. `(landau-real)`; Möhle 2005,
Eq. (4.3)). This module proves that the two agree (`fLFourier_eq_fL`), so the hypothesis
`LandauFacts.real_integral` of `PaperD.U6_Lemma` holds.

The proof rotates the half line `t > 0` to the ray `t = r e^{iθ}` and lets `θ` run from `0`
down to `-π/2`. On that ray the integrand is
`G(θ, r) = exp(-i(λ + log r + i(θ - π/2)) r e^{iθ}) e^{iθ}` (`rotG`), with real and imaginary
parts of the exponent written out (`rotP`, `rotQ`), so no complex logarithm appears. Then

* `∂_θ G = i ∂_r (r G)` (`rotGθ_eq`), a direct computation;
* `|G(θ, r)| ≤ e^K e^{-r}` for `-π/2 ≤ θ ≤ 0` (`norm_rotG_le`), so the integrals converge and
  can be differentiated in `θ` under the integral sign;
* `∫_0^∞ ∂_r (r G) dr = 0`, since `r G → 0` at both ends, so `θ ↦ ∫_0^∞ G(θ, r) dr` has
  derivative `0` (`hasDerivAt_rotF`);
* at `θ = 0` the integrand is the Fourier integrand (`rotG_zero`), and at `θ = -π/2` its real
  part is `e^{-r log r - λ r} sin(π r)` (`re_rotG_neg_pi_div_two`).

The negative half line gives the complex conjugate of the positive half line
(`fourierIntegrand_neg`), so the real part of the full integral is twice that of the half.
-/

namespace Kagey131.PaperD.U6

open Real MeasureTheory Set Filter Topology

/-! ### The integrand on the rotated ray -/

/-- Real part of the exponent on the ray `t = r e^{iθ}`. -/
noncomputable def rotP (lam θ r : ℝ) : ℝ :=
  r * ((θ - π / 2) * Real.cos θ + (lam + Real.log r) * Real.sin θ)

/-- Imaginary part of the exponent on the ray `t = r e^{iθ}`. -/
noncomputable def rotQ (lam θ r : ℝ) : ℝ :=
  r * ((θ - π / 2) * Real.sin θ - (lam + Real.log r) * Real.cos θ)

/-- The rotated integrand `G(θ, r) = exp(-i(λ + log r + i(θ - π/2)) r e^{iθ}) e^{iθ}`. -/
noncomputable def rotG (lam θ r : ℝ) : ℂ :=
  Complex.exp ((rotP lam θ r : ℂ) + (rotQ lam θ r : ℂ) * Complex.I) *
    Complex.exp ((θ : ℂ) * Complex.I)

/-- `∂_θ rotP`. -/
noncomputable def rotPθ (lam θ r : ℝ) : ℝ :=
  r * (Real.cos θ - (θ - π / 2) * Real.sin θ + (lam + Real.log r) * Real.cos θ)

/-- `∂_θ rotQ`. -/
noncomputable def rotQθ (lam θ r : ℝ) : ℝ :=
  r * (Real.sin θ + (θ - π / 2) * Real.cos θ + (lam + Real.log r) * Real.sin θ)

/-- `∂_r rotP` (for `r > 0`). -/
noncomputable def rotPr (lam θ r : ℝ) : ℝ :=
  (θ - π / 2) * Real.cos θ + (lam + Real.log r) * Real.sin θ + Real.sin θ

/-- `∂_r rotQ` (for `r > 0`). -/
noncomputable def rotQr (lam θ r : ℝ) : ℝ :=
  (θ - π / 2) * Real.sin θ - (lam + Real.log r) * Real.cos θ - Real.cos θ

/-- `∂_θ G`. -/
noncomputable def rotGθ (lam θ r : ℝ) : ℂ :=
  rotG lam θ r * ((rotPθ lam θ r : ℂ) + (rotQθ lam θ r : ℂ) * Complex.I + Complex.I)

theorem hasDerivAt_rotP_θ (lam r θ : ℝ) :
    HasDerivAt (fun θ => rotP lam θ r) (rotPθ lam θ r) θ := by
  have h1 := ((hasDerivAt_id' θ).sub_const (π / 2)).mul (Real.hasDerivAt_cos θ)
  have h2 := (Real.hasDerivAt_sin θ).const_mul (lam + Real.log r)
  refine ((h1.add h2).const_mul r).congr_deriv ?_
  unfold rotPθ; ring

theorem hasDerivAt_rotQ_θ (lam r θ : ℝ) :
    HasDerivAt (fun θ => rotQ lam θ r) (rotQθ lam θ r) θ := by
  have h1 := ((hasDerivAt_id' θ).sub_const (π / 2)).mul (Real.hasDerivAt_sin θ)
  have h2 := (Real.hasDerivAt_cos θ).const_mul (lam + Real.log r)
  refine ((h1.sub h2).const_mul r).congr_deriv ?_
  unfold rotQθ; ring

theorem hasDerivAt_rotG_θ (lam r θ : ℝ) :
    HasDerivAt (fun θ => rotG lam θ r) (rotGθ lam θ r) θ := by
  have hP := (hasDerivAt_rotP_θ lam r θ).ofReal_comp
  have hQ := (hasDerivAt_rotQ_θ lam r θ).ofReal_comp
  have hE := (hP.add (hQ.mul_const Complex.I)).cexp
  have hw := ((hasDerivAt_id' θ).ofReal_comp.mul_const Complex.I).cexp
  refine (hE.mul hw).congr_deriv ?_
  simp only [Pi.add_apply]
  unfold rotGθ rotG; push_cast; ring

theorem hasDerivAt_rotP_r (lam θ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r => rotP lam θ r) (rotPr lam θ r) r := by
  have hl := ((Real.hasDerivAt_log hr.ne').const_add lam).mul_const (Real.sin θ)
  have h := (hasDerivAt_id' r).mul (hl.const_add ((θ - π / 2) * Real.cos θ))
  refine h.congr_deriv ?_
  have e : r * (r⁻¹ * Real.sin θ) = Real.sin θ := by
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  unfold rotPr; linear_combination e

theorem hasDerivAt_rotQ_r (lam θ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r => rotQ lam θ r) (rotQr lam θ r) r := by
  have hl := ((Real.hasDerivAt_log hr.ne').const_add lam).mul_const (Real.cos θ)
  have h := (hasDerivAt_id' r).mul (hl.const_sub ((θ - π / 2) * Real.sin θ))
  refine h.congr_deriv ?_
  have e : r * (r⁻¹ * Real.cos θ) = Real.cos θ := by
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  unfold rotQr; linear_combination -e

/-- `r ↦ r G(θ, r)` has derivative `G (1 + r ∂_r E)` for `r > 0`. -/
theorem hasDerivAt_mul_rotG_r (lam θ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r : ℝ => (r : ℂ) * rotG lam θ r)
      (rotG lam θ r * (1 + (r : ℂ) * ((rotPr lam θ r : ℂ) + (rotQr lam θ r : ℂ) * Complex.I)))
      r := by
  have hP := (hasDerivAt_rotP_r lam θ hr).ofReal_comp
  have hQ := (hasDerivAt_rotQ_r lam θ hr).ofReal_comp
  have hE := ((hP.add (hQ.mul_const Complex.I)).cexp).mul_const
    (Complex.exp ((θ : ℂ) * Complex.I))
  have h := (hasDerivAt_id' r).ofReal_comp.mul hE
  refine h.congr_deriv ?_
  simp only [Pi.add_apply]
  unfold rotG; push_cast; ring

/-- The key identity `∂_θ G = i ∂_r (r G)`. -/
theorem rotGθ_eq (lam θ r : ℝ) :
    rotGθ lam θ r =
      Complex.I * (rotG lam θ r *
        (1 + (r : ℂ) * ((rotPr lam θ r : ℂ) + (rotQr lam θ r : ℂ) * Complex.I))) := by
  have h1 : rotPθ lam θ r = -(r * rotQr lam θ r) := by unfold rotPθ rotQr; ring
  have h2 : rotQθ lam θ r = r * rotPr lam θ r := by unfold rotQθ rotPr; ring
  unfold rotGθ
  rw [h1, h2]
  push_cast
  linear_combination (-(rotG lam θ r) * (r : ℂ) * (rotQr lam θ r : ℂ)) * Complex.I_sq

/-! ### Bounds on the rotated integrand -/

/-- `r |log r| ≤ r² + 1` for `r > 0`. -/
theorem mul_abs_log_le {r : ℝ} (hr : 0 < r) : r * |Real.log r| ≤ r ^ 2 + 1 := by
  rcases le_or_gt 1 r with h | h
  · have hl : 0 ≤ Real.log r := Real.log_nonneg h
    rw [abs_of_nonneg hl]
    have := Real.log_le_sub_one_of_pos hr
    nlinarith
  · have := Real.abs_log_mul_self_lt r hr h.le
    rw [abs_mul, abs_of_pos hr] at this
    nlinarith

/-- The constant `K` of the bound `|G| ≤ e^K e^{-r}`. -/
noncomputable def rotK (lam : ℝ) : ℝ :=
  Real.exp (1 + |lam|) * |lam| + Real.exp (1 + |lam|) ^ 2 + 1 + Real.exp (1 + |lam|)

theorem cos_sin_facts {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) 0) :
    0 ≤ Real.cos θ ∧ Real.sin θ ≤ 0 ∧ 1 ≤ Real.cos θ - Real.sin θ := by
  have hc : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hs : Real.sin θ ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le hθ.2 (by linarith [hθ.1, Real.pi_pos])
  have h1 := Real.sin_sq_add_cos_sq θ
  have hc1 := Real.cos_le_one θ
  have hs1 := Real.neg_one_le_sin θ
  refine ⟨hc, hs, ?_⟩
  nlinarith

theorem rotP_le {lam θ r : ℝ} (hθ : θ ∈ Icc (-(π / 2)) 0) (hr : 0 < r) :
    rotP lam θ r ≤ rotK lam - r := by
  obtain ⟨hc, hs, hcs⟩ := cos_sin_facts hθ
  have hb : θ - π / 2 ≤ -1 := by linarith [hθ.2, Real.pi_gt_three]
  have hbc : (θ - π / 2) * Real.cos θ ≤ -Real.cos θ := by nlinarith
  set R := Real.exp (1 + |lam|) with hR
  have hR0 : 0 < R := Real.exp_pos _
  have hK0 : 0 ≤ rotK lam := by unfold rotK; positivity
  unfold rotP
  rcases le_or_gt 1 (lam + Real.log r) with ha | ha
  · have : (lam + Real.log r) * Real.sin θ ≤ Real.sin θ := by nlinarith
    have : r * ((θ - π / 2) * Real.cos θ + (lam + Real.log r) * Real.sin θ) ≤ r * (-1) := by
      apply mul_le_mul_of_nonneg_left _ hr.le; linarith
    linarith
  · -- here `r < R`
    have hlog : Real.log r < 1 + |lam| := by linarith [neg_abs_le lam]
    have hrR : r < R := by
      rw [hR, ← Real.exp_log hr]; exact Real.exp_lt_exp.mpr hlog
    have has : (lam + Real.log r) * Real.sin θ ≤ |lam| + |Real.log r| := by
      have h1 : (lam + Real.log r) * Real.sin θ ≤ |lam + Real.log r| * |Real.sin θ| := by
        rw [← abs_mul]; exact le_abs_self _
      have h2 : |lam + Real.log r| ≤ |lam| + |Real.log r| := abs_add_le _ _
      have h3 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
      nlinarith [abs_nonneg (lam + Real.log r), abs_nonneg (Real.sin θ)]
    have hml := mul_abs_log_le hr
    have : r * ((θ - π / 2) * Real.cos θ + (lam + Real.log r) * Real.sin θ) ≤
        r * |lam| + r * |Real.log r| := by
      have : (θ - π / 2) * Real.cos θ + (lam + Real.log r) * Real.sin θ ≤
          |lam| + |Real.log r| := by linarith
      nlinarith
    have hrl : r * |lam| ≤ R * |lam| := mul_le_mul_of_nonneg_right hrR.le (abs_nonneg _)
    have hr2 : r ^ 2 ≤ R ^ 2 := by nlinarith
    unfold rotK
    rw [← hR]
    linarith

theorem norm_rotG (lam θ r : ℝ) : ‖rotG lam θ r‖ = Real.exp (rotP lam θ r) := by
  unfold rotG
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_exp]
  congr 1
  simp

theorem norm_rotG_le {lam θ r : ℝ} (hθ : θ ∈ Icc (-(π / 2)) 0) (hr : 0 < r) :
    ‖rotG lam θ r‖ ≤ Real.exp (rotK lam) * Real.exp (-1 * r) := by
  rw [norm_rotG, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith [rotP_le (lam := lam) hθ hr])

/-- The constant of the bound on `∂_θ G`. -/
noncomputable def rotC (lam : ℝ) : ℝ :=
  Real.exp (rotK lam) * (4 * (1 + π + |lam|) + 35)

theorem norm_rotGθ_le {lam θ r : ℝ} (hθ : θ ∈ Icc (-(π / 2)) 0) (hr : 0 < r) :
    ‖rotGθ lam θ r‖ ≤ rotC lam * Real.exp (-(1 / 2) * r) := by
  have hG := norm_rotG_le (lam := lam) hθ hr
  have hb : |θ - π / 2| ≤ π := by
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hc := Real.abs_cos_le_one θ
  have hs := Real.abs_sin_le_one θ
  have ha : |lam + Real.log r| ≤ |lam| + |Real.log r| := abs_add_le _ _
  have hml := mul_abs_log_le hr
  -- the factor
  have hPθ : |rotPθ lam θ r| ≤ r * (1 + π + |lam| + |Real.log r|) := by
    unfold rotPθ
    rw [abs_mul, abs_of_pos hr]
    apply mul_le_mul_of_nonneg_left _ hr.le
    calc |Real.cos θ - (θ - π / 2) * Real.sin θ + (lam + Real.log r) * Real.cos θ|
        ≤ |Real.cos θ| + |θ - π / 2| * |Real.sin θ| + |lam + Real.log r| * |Real.cos θ| := by
          have := abs_add_le (Real.cos θ - (θ - π / 2) * Real.sin θ)
            ((lam + Real.log r) * Real.cos θ)
          have := abs_sub (Real.cos θ) ((θ - π / 2) * Real.sin θ)
          rw [abs_mul] at *; linarith
      _ ≤ 1 + π * 1 + (|lam| + |Real.log r|) * 1 := by
          gcongr
      _ = 1 + π + |lam| + |Real.log r| := by ring
  have hQθ : |rotQθ lam θ r| ≤ r * (1 + π + |lam| + |Real.log r|) := by
    unfold rotQθ
    rw [abs_mul, abs_of_pos hr]
    apply mul_le_mul_of_nonneg_left _ hr.le
    calc |Real.sin θ + (θ - π / 2) * Real.cos θ + (lam + Real.log r) * Real.sin θ|
        ≤ |Real.sin θ| + |θ - π / 2| * |Real.cos θ| + |lam + Real.log r| * |Real.sin θ| := by
          have := abs_add_le (Real.sin θ + (θ - π / 2) * Real.cos θ)
            ((lam + Real.log r) * Real.sin θ)
          have := abs_add_le (Real.sin θ) ((θ - π / 2) * Real.cos θ)
          rw [abs_mul] at *; linarith
      _ ≤ 1 + π * 1 + (|lam| + |Real.log r|) * 1 := by
          gcongr
      _ = 1 + π + |lam| + |Real.log r| := by ring
  have hfac : ‖(rotPθ lam θ r : ℂ) + (rotQθ lam θ r : ℂ) * Complex.I + Complex.I‖ ≤
      2 * (1 + π + |lam|) * r + 2 * r ^ 2 + 3 := by
    have h1 := norm_add_le ((rotPθ lam θ r : ℂ) + (rotQθ lam θ r : ℂ) * Complex.I) Complex.I
    have h2 := norm_add_le (rotPθ lam θ r : ℂ) ((rotQθ lam θ r : ℂ) * Complex.I)
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs] at h2
    rw [Complex.norm_I] at h1
    nlinarith
  -- `r ≤ 2 e^{r/2}`, `r² ≤ 16 e^{r/2}`
  set u := Real.exp ((1 / 2) * r) with hu
  have hu1 : 1 ≤ u := Real.one_le_exp (by positivity)
  have hr2u : r ≤ 2 * u := by
    have := Real.add_one_le_exp ((1 / 2) * r); rw [← hu] at this; linarith
  have hr16u : r ^ 2 ≤ 16 * u := by
    have h4 := Real.add_one_le_exp ((1 / 4) * r)
    have hsq : Real.exp ((1 / 4) * r) ^ 2 = u := by
      rw [hu, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have : r ≤ 4 * Real.exp ((1 / 4) * r) := by linarith
    nlinarith
  have hX : 2 * (1 + π + |lam|) * r + 2 * r ^ 2 + 3 ≤ (4 * (1 + π + |lam|) + 35) * u := by
    have : 0 ≤ 1 + π + |lam| := by positivity
    nlinarith
  have heu : Real.exp (-1 * r) * u = Real.exp (-(1 / 2) * r) := by
    rw [hu, ← Real.exp_add]; congr 1; ring
  unfold rotGθ
  rw [norm_mul]
  calc ‖rotG lam θ r‖ * ‖(rotPθ lam θ r : ℂ) + (rotQθ lam θ r : ℂ) * Complex.I + Complex.I‖
      ≤ (Real.exp (rotK lam) * Real.exp (-1 * r)) *
          (2 * (1 + π + |lam|) * r + 2 * r ^ 2 + 3) :=
        mul_le_mul hG hfac (norm_nonneg _) (by positivity)
    _ ≤ (Real.exp (rotK lam) * Real.exp (-1 * r)) * ((4 * (1 + π + |lam|) + 35) * u) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = rotC lam * Real.exp (-(1 / 2) * r) := by
        rw [← heu]; unfold rotC; ring

/-! ### Measurability and integrability -/

theorem measurable_rotG (lam θ : ℝ) : Measurable (fun r => rotG lam θ r) := by
  unfold rotG rotP rotQ; fun_prop

theorem measurable_rotGθ (lam θ : ℝ) : Measurable (fun r => rotGθ lam θ r) := by
  unfold rotGθ rotG rotP rotQ rotPθ rotQθ; fun_prop

theorem continuous_rotG_θ (lam r : ℝ) : Continuous (fun θ => rotG lam θ r) :=
  continuous_iff_continuousAt.mpr fun θ => (hasDerivAt_rotG_θ lam r θ).continuousAt

theorem integrableOn_rotG {lam θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) 0) :
    IntegrableOn (fun r => rotG lam θ r) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1)).const_mul
    (Real.exp (rotK lam))).mono' (measurable_rotG lam θ).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
  exact norm_rotG_le hθ hr

theorem integrableOn_rotGθ {lam θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) 0) :
    IntegrableOn (fun r => rotGθ lam θ r) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
    (rotC lam)).mono' (measurable_rotGθ lam θ).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
  exact norm_rotGθ_le hθ hr

/-! ### The integral over the ray does not depend on `θ` -/

/-- `∫_0^∞ G(θ, r) dr`. -/
noncomputable def rotF (lam θ : ℝ) : ℂ := ∫ r in Ioi 0, rotG lam θ r

/-- `∫_0^∞ ∂_θ G(θ, r) dr = 0`. -/
theorem integral_rotGθ {lam θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) 0) :
    ∫ r in Ioi 0, rotGθ lam θ r = 0 := by
  set f : ℝ → ℂ := fun r => (r : ℂ) * rotG lam θ r with hf
  have hf0 : f 0 = 0 := by simp [hf]
  have hnorm : ∀ r, 0 ≤ r → ‖f r‖ ≤ Real.exp (rotK lam) * (r * Real.exp (-r)) := by
    intro r hr
    rcases hr.eq_or_lt with h | h
    · subst h; simp [hf]
    · have := norm_rotG_le (lam := lam) hθ h
      rw [hf]
      simp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h]
      have e : Real.exp (-1 * r) = Real.exp (-r) := by ring_nf
      rw [e] at this
      nlinarith [norm_nonneg (rotG lam θ r), Real.exp_pos (rotK lam), Real.exp_pos (-r)]
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    rw [ContinuousWithinAt, hf0]
    refine squeeze_zero_norm' ?_ (?_ : Tendsto (fun r : ℝ => Real.exp (rotK lam) * |r|)
      (𝓝[Ici 0] 0) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : (0 : ℝ) ≤ r := hr
      refine (hnorm r hr').trans ?_
      rw [abs_of_nonneg hr']
      have h1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h2 : r * Real.exp (-r) ≤ r := by nlinarith
      exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    · have : Continuous (fun r : ℝ => Real.exp (rotK lam) * |r|) := by fun_prop
      have h := this.tendsto 0
      simp only [abs_zero, mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
  have hderiv : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt f (-Complex.I * rotGθ lam θ r) r := by
    intro r hr
    refine (hasDerivAt_mul_rotG_r lam θ hr).congr_deriv ?_
    rw [rotGθ_eq, ← mul_assoc, show -Complex.I * Complex.I = 1 by
      rw [neg_mul, Complex.I_mul_I, neg_neg], one_mul]
  have hint : IntegrableOn (fun r => -Complex.I * rotGθ lam θ r) (Ioi 0) :=
    (integrableOn_rotGθ hθ).const_mul _
  have htop : Tendsto f atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (?_ : Tendsto (fun r : ℝ => Real.exp (rotK lam) *
      (r ^ 1 * Real.exp (-r))) atTop (𝓝 0))
    · filter_upwards [eventually_ge_atTop 0] with r hr
      rw [pow_one]; exact hnorm r hr
    · have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (Real.exp (rotK lam))
      simpa using this
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htop
  rw [hf0, sub_zero, integral_const_mul] at key
  have hI : -Complex.I ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  exact (mul_eq_zero.mp key).resolve_left hI

theorem hasDerivAt_rotF {lam θ : ℝ} (hθ : θ ∈ Ioo (-(π / 2)) 0) :
    HasDerivAt (rotF lam) 0 θ := by
  have hs : Ioo (-(π / 2)) 0 ∈ 𝓝 θ := Ioo_mem_nhds hθ.1 hθ.2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun θ r => rotG lam θ r) (F' := fun θ r => rotGθ lam θ r) (x₀ := θ)
    (bound := fun r => rotC lam * Real.exp (-(1 / 2) * r)) hs
    (Eventually.of_forall fun θ => (measurable_rotG lam θ).aestronglyMeasurable)
    (integrableOn_rotG (Ioo_subset_Icc_self hθ))
    (measurable_rotGθ lam θ).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr θ' hθ' =>
      norm_rotGθ_le (Ioo_subset_Icc_self hθ') hr))
    ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (rotC lam))
    (ae_of_all _ fun r θ' _ => hasDerivAt_rotG_θ lam r θ')
  have h := key.2
  rw [integral_rotGθ (Ioo_subset_Icc_self hθ)] at h
  exact h

theorem continuousOn_rotF (lam : ℝ) : ContinuousOn (rotF lam) (Icc (-(π / 2)) 0) := by
  refine continuousOn_of_dominated (bound := fun r => Real.exp (rotK lam) * Real.exp (-1 * r))
    (fun θ _ => (measurable_rotG lam θ).aestronglyMeasurable)
    (fun θ hθ => (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun r hr => norm_rotG_le hθ hr))
    ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1)).const_mul _)
    (ae_of_all _ fun r => (continuous_rotG_θ lam r).continuousOn)

/-- The real part of `∫_0^∞ G(θ, r) dr` is the same at `θ = 0` and `θ = -π/2`. -/
theorem re_rotF_eq (lam : ℝ) : (rotF lam 0).re = (rotF lam (-(π / 2))).re := by
  have hab : -(π / 2) < (0 : ℝ) := by linarith [Real.pi_pos]
  have hc : ContinuousOn (fun θ => (rotF lam θ).re) (Icc (-(π / 2)) 0) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_rotF lam)
  have hd : ∀ θ ∈ Ioo (-(π / 2)) (0 : ℝ), HasDerivAt (fun θ => (rotF lam θ).re) 0 θ := by
    intro θ hθ
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_rotF (lam := lam) hθ)
    simp only [map_zero] at this
    exact this
  obtain ⟨c, _, hc'⟩ := exists_hasDerivAt_eq_slope (fun θ => (rotF lam θ).re) (fun _ => 0)
    hab hc hd
  have hne : (0 : ℝ) - -(π / 2) ≠ 0 := by linarith [Real.pi_pos]
  have := hc'.symm
  rw [div_eq_zero_iff] at this
  rcases this with h | h
  · linarith
  · exact absurd h hne

/-! ### The two ends of the rotation -/

/-- The Fourier integrand `e^{-iλt} e^{B(t)}`. -/
noncomputable def fourierIntegrand (lam t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * lam * t) * Complex.exp (landauB t)

theorem rotG_zero {lam r : ℝ} (hr : 0 < r) : rotG lam 0 r = fourierIntegrand lam r := by
  unfold rotG rotP rotQ fourierIntegrand landauB
  rw [abs_of_pos hr, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring

theorem re_rotG_neg_pi_div_two (lam r : ℝ) :
    (rotG lam (-(π / 2)) r).re = gk 0 lam r := by
  unfold rotG
  rw [← Complex.exp_add, Complex.exp_re]
  have hre : ((rotP lam (-(π / 2)) r : ℂ) + (rotQ lam (-(π / 2)) r : ℂ) * Complex.I +
      ((-(π / 2) : ℝ) : ℂ) * Complex.I).re = -(r * Real.log r) - lam * r := by
    simp [rotP, Real.cos_neg, Real.sin_neg]; ring
  have him : ((rotP lam (-(π / 2)) r : ℂ) + (rotQ lam (-(π / 2)) r : ℂ) * Complex.I +
      ((-(π / 2) : ℝ) : ℂ) * Complex.I).im = π * r - π / 2 := by
    simp [rotQ, Real.cos_neg, Real.sin_neg]; ring
  rw [hre, him, Real.cos_sub_pi_div_two]
  unfold gk; simp

theorem norm_fourierIntegrand (lam t : ℝ) :
    ‖fourierIntegrand lam t‖ = Real.exp (-(π / 2 * |t|)) := by
  unfold fourierIntegrand landauB
  rw [← Complex.exp_add, Complex.norm_exp]
  congr 1
  simp

theorem fourierIntegrand_neg (lam t : ℝ) :
    fourierIntegrand lam (-t) = (starRingEnd ℂ) (fourierIntegrand lam t) := by
  unfold fourierIntegrand landauB
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_conj]
  congr 1
  apply Complex.ext
  · simp only [Complex.conj_re]; simp [abs_neg]
  · simp only [Complex.conj_im]; simp [abs_neg]; ring

theorem measurable_fourierIntegrand (lam : ℝ) : Measurable (fourierIntegrand lam) := by
  unfold fourierIntegrand landauB; fun_prop

theorem integrable_exp_neg_mul_abs' {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => Real.exp (-(c * |t|))) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-(c * |t|))) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.mp ht)]; ring_nf
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-(c * |t|))) (Iic 0) := by
    have := integrableOn_exp_mul_Iic (a := c) hc 0
    refine this.congr_fun (fun t ht => ?_) measurableSet_Iic
    rw [abs_of_nonpos (mem_Iic.mp ht)]; ring_nf
  have := h2.union h1
  rw [Iic_union_Ioi, integrableOn_univ] at this
  exact this

theorem integrable_fourierIntegrand (lam : ℝ) : Integrable (fourierIntegrand lam) := by
  refine (integrable_exp_neg_mul_abs' (c := π / 2) (by positivity)).mono'
    (measurable_fourierIntegrand lam).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_fourierIntegrand]

/-- **The contour rotation of the paper's Appendix, Step 1** (Möhle 2005, Eq. (4.3)). The
Fourier form of the Landau density equals the real integral,
`(1/2π) ∫_ℝ e^{-iλt} e^{B(t)} dt = (1/π) ∫_0^∞ e^{-s log s - λ s} sin(π s) ds`. -/
theorem fLFourier_eq_fL (lam : ℝ) : fLFourier lam = fL lam := by
  have hint := integrable_fourierIntegrand lam
  have hfun : (fun t : ℝ => Complex.exp (-Complex.I * lam * t) * Complex.exp (landauB t)) =
      fourierIntegrand lam := rfl
  -- the full line is twice the real part of the half line
  have hsplit : (∫ t : ℝ, fourierIntegrand lam t).re =
      2 * (∫ t in Ioi 0, fourierIntegrand lam t).re := by
    rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hint.integrableOn hint.integrableOn]
    have hneg : ∫ t in Iic 0, fourierIntegrand lam t =
        ∫ t in Ioi 0, fourierIntegrand lam (-t) := by
      rw [integral_comp_neg_Ioi, neg_zero]
    rw [hneg]
    simp_rw [fourierIntegrand_neg]
    rw [integral_conj, Complex.add_re, Complex.conj_re]
    ring
  have hhalf : ∫ t in Ioi 0, fourierIntegrand lam t = rotF lam 0 := by
    unfold rotF
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    exact (rotG_zero hr).symm
  have hend : (rotF lam (-(π / 2))).re = Fk 0 lam := by
    have hθ : -(π / 2) ∈ Icc (-(π / 2)) (0 : ℝ) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
    unfold rotF Fk
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ (integrableOn_rotG hθ)]
    simp only [Complex.reCLM_apply, re_rotG_neg_pi_div_two]
  unfold fLFourier fL
  rw [hfun, hsplit, hhalf, re_rotF_eq, hend]
  field_simp

/-- `LandauFacts.real_integral`, proved. -/
theorem landauFacts_of_unimodal (hU : Unimodal fLFourier) : LandauFacts :=
  ⟨fLFourier_eq_fL, hU⟩

end Kagey131.PaperD.U6
