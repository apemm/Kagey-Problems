import PaperD.FL5_Step4a
import PaperD.FL5_SinhInt

/-!
# Paper F, track FL5: Step 4 of the proof of Theorem 2.9, `f(1/2) = (2/π) tan(πα/2)`

The paper's Step 4 identifies the law of `Y = G₁/(G₁+G₂)` from the moments `E W^p` of
`W = G₁/G₂` (`E W^p = E G^p E G^{-p} = sin(πp)/(α sin(πp/α))`), and then reads off
`f(1/2) = ℓ_α(1/2)`. Only the value `f(1/2) = 4 ∫_0^∞ t g(t)² dt` is needed. Here it is computed
**by a different, shorter route that uses the same ingredients**: with `U = log G`, whose density
is `F(u) = e^u g(e^u)`,

* `∫_0^∞ t g(t)² dt = ∫ F(u)² du` (`u = log t`),
* `E e^{iτU} = E G^{iτ}`, and `|E G^{iτ}|² = E W^{iτ} = sinh(πτ)/(α sinh(πτ/α))` — the paper's
  moment formula at `p = iτ` (`imagMoment`, from the paper's `x^{-p}` integral and the reflection
  formula; `norm_imagMoment_sq`),
* Parseval (proved from Fourier inversion, `integral_sq_eq_integral_norm_fourier_sq`):
  `∫ F² = (1/2π) ∫ |E G^{iτ}|² dτ`,
* `∫_0^∞ sinh(πx)/sinh(πx/α) dx = (α/2) tan(πα/2)` (`integral_sinh_div_sinh`).

So `∫_0^∞ t g² = tan(πα/2)/(2π)` and `f(1/2) = (2/π) tan(πα/2) = ℓ_α(1/2)`: `step4_holds`.
This bypasses the paper's identification of the law of `Y` (the integral
`∫ x^β/(x² + 2x cos ϑ + 1) dx` and the uniqueness of a law with a given moment generating
function); no classical hypothesis is used.
-/

namespace Kagey131.PaperD.FL5

open Filter Topology Real MeasureTheory Set FourierTransform

/-! ### Change of variables `t = e^u` on the whole line -/

theorem integral_comp_exp_univ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ → E) : ∫ u, Real.exp u • h (Real.exp u) = ∫ t in Ioi 0, h t := by
  have := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) h
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at this
  rw [this]
  simp [abs_of_pos (Real.exp_pos _)]

theorem integrable_comp_exp_univ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ → E} (hh : IntegrableOn h (Ioi 0)) :
    Integrable fun u => Real.exp u • h (Real.exp u) := by
  have := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) h).mp
  rw [Set.image_univ, Real.range_exp, integrableOn_univ] at this
  simpa [abs_of_pos (Real.exp_pos _)] using this hh

/-- `sinh x / sinh y ≤ e^{x - y}` for `0 < x ≤ y`. -/
theorem sinh_div_sinh_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.sinh x / Real.sinh y ≤ Real.exp (x - y) := by
  have hy : 0 < Real.sinh y := Real.sinh_pos_iff.mpr (by linarith)
  rw [div_le_iff₀ hy, Real.sinh_eq, Real.sinh_eq, Real.exp_sub]
  have hey := Real.exp_pos y
  rw [div_mul_eq_mul_div, le_div_iff₀ hey]
  have h1 : Real.exp (-x) * Real.exp y ≥ Real.exp (-y) * Real.exp x := by
    rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  nlinarith [Real.exp_pos x]

/-- `sinh(πτ)/(α sinh(πτ/α))` is even. -/
theorem ratio_abs (α τ : ℝ) :
    Real.sinh (π * τ) / (α * Real.sinh (π * τ / α))
      = Real.sinh (π * |τ|) / (α * Real.sinh (π * |τ| / α)) := by
  rcases le_or_gt 0 τ with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, show π * -τ = -(π * τ) by ring, show -(π * τ) / α = -(π * τ / α) by ring,
      Real.sinh_neg, Real.sinh_neg, mul_neg, neg_div_neg_eq]

section step4

variable {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {g : ℝ → ℝ} {G0 : ℝ}
  (hg0 : ∀ z, 0 ≤ g z) (hgz : ∀ z ≤ 0, g z = 0) (hgle : ∀ z, g z ≤ G0) (hgc : Continuous g)
  (hgint : Integrable g) (hg1 : ∫ z, g z = 1)
  (hlap : ∀ s : ℝ, 0 ≤ s →
    ∫ z, Real.exp (-(s * z)) * g z = Real.exp (-(Real.Gamma (1 - α) * s ^ α)))

/-- `Q(p) = Γ(p/α + 1) (1/c)^{p/α} / Γ(p + 1)`. -/
noncomputable def momQ (α : ℝ) (p : ℂ) : ℂ :=
  Complex.Gamma (p / α + 1) * (1 / (Real.Gamma (1 - α) : ℂ)) ^ (p / α) / Complex.Gamma (p + 1)

include h0 h1 hg0 hgz hgle hgc hgint hlap in
/-- **The imaginary moments of `G`**: `E G^{iτ} = Q(-iτ)`, the limit `Re p ↓ 0` of the paper's
formula for `E G^{-p}`. -/
theorem imagMoment (τ : ℝ) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (Complex.I * τ) * (g t : ℂ) = momQ α (-(Complex.I * τ)) := by
  have hc : 0 < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hα : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
  set p : ℕ → ℂ := fun n => ((1 / ((n : ℝ) + 2) : ℝ) : ℂ) - Complex.I * τ with hp
  have hpre : ∀ n, (p n).re = 1 / ((n : ℝ) + 2) := by
    intro n
    simp only [hp, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im]
    ring
  have hpre0 : ∀ n, 0 < (p n).re := fun n => by rw [hpre]; positivity
  have hpre1 : ∀ n, (p n).re ≤ 1 / 2 := fun n => by
    rw [hpre]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  -- the formula along `p n`
  have hform : ∀ n, ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (-p n) * (g t : ℂ) = momQ α (p n) := by
    intro n
    rw [negMoment h0 h1 hg0 hgz hgle hgc hgint hlap (hpre0 n) (by linarith [hpre1 n])]
    have hpn : p n ≠ 0 := fun h => by have := hpre0 n; rw [h] at this; simp at this
    have hpa : p n / α ≠ 0 := div_ne_zero hpn hα
    unfold momQ
    rw [Complex.Gamma_add_one _ hpa, Complex.Gamma_add_one _ hpn]
    have hΓ1 := Complex.Gamma_ne_zero_of_re_pos (hpre0 n)
    field_simp
  -- `p n → -iτ`
  have hplim : Tendsto p atTop (𝓝 (-(Complex.I * τ))) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1))
    have h2 := h.sub (tendsto_const_nhds (x := Complex.I * τ))
    simp only [Complex.ofReal_zero, zero_sub] at h2
    refine h2.congr fun n => ?_
    simp only [hp, Function.comp_apply]
    push_cast
    ring
  -- continuity of `Q` at `-iτ`
  have hQcont : ContinuousAt (momQ α) (-(Complex.I * τ)) := by
    unfold momQ
    have hre1 : 0 < (-(Complex.I * τ) / α + 1).re := by simp [Complex.div_ofReal_re]
    have hre2 : 0 < (-(Complex.I * τ) + 1).re := by simp
    have hG1 : ContinuousAt (fun p : ℂ => Complex.Gamma (p / α + 1)) (-(Complex.I * τ)) := by
      have hd := Complex.differentiableAt_Gamma (-(Complex.I * τ) / α + 1) (fun m h => by
        have := congrArg Complex.re h; simp at this; linarith [hre1, this])
      exact hd.continuousAt.comp (f := fun p : ℂ => p / α + 1) (by fun_prop)
    have hG2 : ContinuousAt (fun p : ℂ => Complex.Gamma (p + 1)) (-(Complex.I * τ)) := by
      have hd := Complex.differentiableAt_Gamma (-(Complex.I * τ) + 1) (fun m h => by
        have := congrArg Complex.re h; simp at this; linarith [hre2, this])
      exact hd.continuousAt.comp (f := fun p : ℂ => p + 1) (by fun_prop)
    have hpw : ContinuousAt (fun p : ℂ => (1 / (Real.Gamma (1 - α) : ℂ)) ^ (p / α))
        (-(Complex.I * τ)) := by
      have h1c : (1 / (Real.Gamma (1 - α) : ℂ)) ≠ 0 := by
        exact one_div_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne')
      exact (continuousAt_const_cpow h1c).comp (f := fun p : ℂ => p / α) (by fun_prop)
    exact (hG1.mul hpw).div hG2 (Complex.Gamma_ne_zero_of_re_pos hre2)
  have hR : Tendsto (fun n => momQ α (p n)) atTop (𝓝 (momQ α (-(Complex.I * τ)))) :=
    hQcont.tendsto.comp hplim
  -- dominated convergence for the left side
  have hbound_int : IntegrableOn (fun t : ℝ => (1 + t ^ (-(1 / 2 : ℝ))) * g t) (Ioi 0) := by
    have := (integrableOn_rpow_neg_mul hg0 hgle hgc hgint (σ := 1 / 2) (by norm_num)
      (by norm_num))
    refine (hgint.integrableOn.add this).congr_fun (fun t _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioi
  have hL : Tendsto (fun n => ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (-p n) * (g t : ℂ)) atTop
      (𝓝 (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (Complex.I * τ) * (g t : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence (fun t => (1 + t ^ (-(1 / 2 : ℝ))) * g t)
      (fun n => ?_) hbound_int (fun n => ?_) ?_
    · refine (Measurable.mul ?_ ?_).aestronglyMeasurable
      · exact (Complex.measurable_ofReal).pow_const _
      · exact Complex.measurable_ofReal.comp hgc.measurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
        Real.norm_of_nonneg (hg0 t)]
      refine mul_le_mul_of_nonneg_right ?_ (hg0 t)
      have hre : (-p n).re = -(1 / ((n : ℝ) + 2)) := by rw [Complex.neg_re, hpre]
      rw [hre]
      rcases le_or_gt 1 t with ht1 | ht1
      · have : t ^ (-(1 / ((n : ℝ) + 2))) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos ht1 (by have := hpre0 n; rw [hpre] at this; linarith)
        have : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0.le _
        linarith
      · have : t ^ (-(1 / ((n : ℝ) + 2))) ≤ t ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le (by
            have := hpre1 n; rw [hpre] at this; linarith)
        linarith
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      have hneg : Tendsto (fun n => -p n) atTop (𝓝 (Complex.I * τ)) := by
        simpa using hplim.neg
      exact ((continuousAt_const_cpow ht0).tendsto.comp hneg).mul_const _
  exact tendsto_nhds_unique (hL.congr fun n => hform n) hR

include h0 h1 hg0 hgz hgle hgc hgint hlap in
/-- `|E G^{iτ}|² = sinh(πτ)/(α sinh(πτ/α))` for `τ ≠ 0` (the paper's
`E W^p = sin(πp)/(α sin(πp/α))` at `p = iτ`). -/
theorem norm_imagMoment_sq {τ : ℝ} (hτ : τ ≠ 0) :
    ‖∫ t : ℝ in Ioi 0, (t : ℂ) ^ (Complex.I * τ) * (g t : ℂ)‖ ^ 2
      = Real.sinh (π * τ) / (α * Real.sinh (π * τ / α)) := by
  rw [imagMoment h0 h1 hg0 hgz hgle hgc hgint hlap τ]
  have hc : 0 < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  unfold momQ
  have hpow : ‖(1 / (Real.Gamma (1 - α) : ℂ)) ^ (-(Complex.I * τ) / α)‖ = 1 := by
    rw [show (1 / (Real.Gamma (1 - α) : ℂ)) = ((1 / Real.Gamma (1 - α) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [Complex.div_ofReal_re]
  have e1 : -(Complex.I * τ) / α + 1 = 1 + Complex.I * ((-(τ / α) : ℝ) : ℂ) := by
    push_cast; ring
  have e2 : -(Complex.I * τ) + 1 = 1 + Complex.I * ((-τ : ℝ) : ℂ) := by push_cast; ring
  rw [norm_div, norm_mul, hpow, mul_one, div_pow, e1, e2,
    norm_Gamma_one_add_I_sq (by simp [hτ, h0.ne']), norm_Gamma_one_add_I_sq (by simp [hτ])]
  have hs1 : Real.sinh (π * τ) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_pos.ne' hτ
  have hs2 : Real.sinh (π * τ / α) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact div_ne_zero (mul_ne_zero Real.pi_pos.ne' hτ) h0.ne'
  rw [mul_neg, Real.sinh_neg, mul_neg, Real.sinh_neg, show π * (τ / α) = π * τ / α by ring]
  have := Real.pi_pos
  field_simp

include hg0 hgz hg1 in
theorem norm_imagMoment_le_one (τ : ℝ) :
    ‖∫ t : ℝ in Ioi 0, (t : ℂ) ^ (Complex.I * τ) * (g t : ℂ)‖ ≤ 1 := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [← hg1]
  have : ∫ z, g z = ∫ z in Ioi 0, g z := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
    exact hgz z (not_lt.mp hz)
  rw [this]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
    Real.norm_of_nonneg (hg0 t)]
  simp

/-- `F(u) = e^u g(e^u)`, the density of `log G`. -/
noncomputable def logDens (g : ℝ → ℝ) (u : ℝ) : ℝ := Real.exp u * g (Real.exp u)

include h0 h1 hg0 hgz hgle hgc hgint hg1 hlap in
/-- **Step 4 of the proof of Theorem 2.9**: `∫_0^∞ t g(t)² dt = tan(πα/2)/(2π)`. -/
theorem integral_t_g_sq : ∫ t in Ioi 0, t * g t ^ 2 = Real.tan (π * α / 2) / (2 * π) := by
  have hpi := Real.pi_pos
  set Φ : ℝ → ℂ := fun τ => ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (Complex.I * τ) * (g t : ℂ) with hΦ
  set F := logDens g with hF
  have hFc : Continuous F := by
    have e : F = fun u => Real.exp u * g (Real.exp u) := rfl
    rw [e]; exact Real.continuous_exp.mul (hgc.comp Real.continuous_exp)
  have hFint : Integrable F := by
    have := integrable_comp_exp_univ (h := g) hgint.integrableOn
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp [hF, logDens, smul_eq_mul]
  have hFsq : ∫ u, F u ^ 2 = ∫ t in Ioi 0, t * g t ^ 2 := by
    rw [← integral_comp_exp_univ]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hF, logDens, smul_eq_mul]
    ring
  -- the Fourier transform of `F`
  have hFour : ∀ w, 𝓕 (fun u => (F u : ℂ)) w = Φ (-2 * π * w) := by
    intro w
    rw [Real.fourier_real_eq_integral_exp_smul, hΦ]
    simp only
    rw [← integral_comp_exp_univ]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hF, logDens, smul_eq_mul, Complex.real_smul]
    have hlog : (((Real.exp u : ℝ)) : ℂ) ^ (Complex.I * ((-2 * π * w : ℝ) : ℂ))
        = Complex.exp (((-2 * π * u * w : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
        ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
      congr 1; push_cast; ring
    rw [hlog]
    push_cast
    ring
  -- bounds on `Φ`
  set κ : ℝ := (1 / α - 1) * π / 2 with hκ
  have hκ0 : 0 < κ := by
    have : 1 < 1 / α := by rw [lt_div_iff₀ h0]; linarith
    rw [hκ]; nlinarith
  have hΦsq_le : ∀ τ, ‖Φ τ‖ ^ 2 ≤ (1 / α) * Real.exp (-(2 * κ) * |τ|) := by
    intro τ
    rcases eq_or_ne τ 0 with rfl | hτ
    · have := norm_imagMoment_le_one hg0 hgz hg1 0
      have h1a : 1 ≤ 1 / α := by rw [le_div_iff₀ h0]; linarith
      simp only [abs_zero, mul_zero, Real.exp_zero, mul_one]
      calc ‖Φ 0‖ ^ 2 ≤ 1 := by
            have h0' := norm_nonneg (Φ 0)
            nlinarith
        _ ≤ 1 / α := h1a
    · rw [hΦ]
      simp only
      rw [norm_imagMoment_sq h0 h1 hg0 hgz hgle hgc hgint hlap hτ, ratio_abs]
      have hτ0 : 0 < |τ| := abs_pos.mpr hτ
      have hle := sinh_div_sinh_le (x := π * |τ|) (y := π * |τ| / α) (by positivity)
        (by rw [le_div_iff₀ h0]; exact mul_le_of_le_one_right (by positivity) h1.le)
      have hsp : 0 < Real.sinh (π * |τ| / α) := Real.sinh_pos_iff.mpr (by positivity)
      calc Real.sinh (π * |τ|) / (α * Real.sinh (π * |τ| / α))
          = (1 / α) * (Real.sinh (π * |τ|) / Real.sinh (π * |τ| / α)) := by
            field_simp
        _ ≤ (1 / α) * Real.exp (π * |τ| - π * |τ| / α) := by
            gcongr
        _ = (1 / α) * Real.exp (-(2 * κ) * |τ|) := by
            congr 2; rw [hκ]; field_simp; ring
  have hΦle : ∀ τ, ‖Φ τ‖ ≤ Real.sqrt (1 / α) * Real.exp (-κ * |τ|) := by
    intro τ
    have hA : 0 ≤ Real.sqrt (1 / α) * Real.exp (-κ * |τ|) := by positivity
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) hA two_ne_zero).mp ?_
    rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
    have e : ((2 : ℕ) : ℝ) * (-κ * |τ|) = -(2 * κ) * |τ| := by push_cast; ring
    rw [e]; exact hΦsq_le τ
  have hFFc : Continuous (𝓕 (fun u => (F u : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hFint.ofReal
  have hFFint : Integrable (𝓕 (fun u => (F u : ℂ))) := by
    have hI := (integrable_exp_neg_mul_abs_rpow (p := 1) one_pos
      (by positivity : 0 < κ * (2 * π))).const_mul (Real.sqrt (1 / α))
    refine hI.mono' hFFc.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [hFour]
    refine (hΦle _).trans (le_of_eq ?_)
    congr 2
    rw [Real.rpow_one, abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2),
      abs_of_pos hpi]
    ring
  -- Parseval
  have hpars := integral_sq_eq_integral_norm_fourier_sq hFc hFint hFFint
  rw [hFsq] at hpars
  rw [hpars]
  simp_rw [hFour]
  have hscale := Measure.integral_comp_mul_left (fun τ => ‖Φ τ‖ ^ 2) (-2 * π)
  rw [hscale, smul_eq_mul, abs_inv, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2),
    abs_of_pos hpi]
  -- `∫ |Φ|² = tan(πα/2)`
  have hae : (fun τ => ‖Φ τ‖ ^ 2) =ᵐ[volume]
      fun τ => Real.sinh (π * |τ|) / (α * Real.sinh (π * |τ| / α)) := by
    have : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [this] with τ hτ
    rw [hΦ]
    simp only
    rw [norm_imagMoment_sq h0 h1 hg0 hgz hgle hgc hgint hlap hτ, ratio_abs]
  rw [integral_congr_ae hae,
    integral_comp_abs (f := fun x => Real.sinh (π * x) / (α * Real.sinh (π * x / α)))]
  have e : ∀ x : ℝ, Real.sinh (π * x) / (α * Real.sinh (π * x / α))
      = (1 / α) * (Real.sinh (π * x) / Real.sinh (π / α * x)) := by
    intro x; rw [show π * x / α = π / α * x by ring]; field_simp
  simp_rw [e]
  rw [integral_const_mul, integral_sinh_div_sinh hpi (by rw [lt_div_iff₀ h0]; nlinarith)]
  rw [show π * π / (2 * (π / α)) = π * α / 2 by field_simp]
  field_simp

end step4

/-- **Step 4 of the proof of Theorem 2.9** (`Step4Claim`): `f(1/2) = ℓ_α(1/2)` for the density
`g` of Lemma A.4(i). -/
theorem step4_holds {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {g : ℝ → ℝ}
    (hSt : StablePosHyp α h0 g) : Step4Claim α g := by
  obtain ⟨hguc, hg0, hgz, ⟨G0, hgle⟩, _, hgint, hg1, hlap, _⟩ := hSt
  unfold Step4Claim
  rw [ratioDensity_half, integral_t_g_sq h0 h1 hg0 hgz hgle hguc.continuous hgint hg1 hlap,
    lamperti_half h0 h1]
  have := Real.pi_pos
  field_simp
  ring

end Kagey131.PaperD.FL5
