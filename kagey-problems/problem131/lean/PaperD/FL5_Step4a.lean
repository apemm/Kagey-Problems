import PaperD.FL5_LemmaA4b

/-!
# Paper F, track FL5: the moments of `G` (Step 4 of the proof of Theorem 2.9)

Step 4 of the paper: "For `x > 0` and `0 < p < 1`, `x^{-p} = (1/Γ(p)) ∫_0^∞ s^{p-1} e^{-sx} ds`.
We put `x = G`, take expectations and substitute `w = s^α`. [...] `E G^p = Γ(1-p/α)/Γ(1-p)`."
(The paper normalizes `E e^{-sG} = e^{-s^α}`; here `E e^{-sG} = e^{-c s^α}`, `c = Γ(1-α)`.)

* `negMoment`: `E G^{-p} = Γ(p/α) (1/c)^{p/α} / (α Γ(p))` for complex `p` with `0 < Re p < 1`
  (the paper's formula, by Fubini and the substitution `w = s^α`);
* `imagMoment`: `E G^{iτ} = Γ(1 - iτ/α) (1/c)^{-iτ/α} / Γ(1 - iτ)` (the limit `Re p → 0`);
* `norm_Gamma_one_add_I_sq`: `|Γ(1 + iy)|² = πy/sinh(πy)` (the reflection formula
  `Γ(z)Γ(1-z) = π/sin(πz)`, DLMF 5.5.3, which is Mathlib's `Complex.Gamma_mul_Gamma_one_sub`);
* `norm_imagMoment_sq`: `|E G^{iτ}|² = sinh(πτ)/(α sinh(πτ/α))` for `τ ≠ 0`.
-/

namespace Kagey131.PaperD.FL5

open Filter Topology Real MeasureTheory Set

section moments

variable {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {g : ℝ → ℝ} {G0 : ℝ}
  (hg0 : ∀ z, 0 ≤ g z) (hgz : ∀ z ≤ 0, g z = 0) (hgle : ∀ z, g z ≤ G0) (hgc : Continuous g)
  (hgint : Integrable g)
  (hlap : ∀ s : ℝ, 0 ≤ s →
    ∫ z, Real.exp (-(s * z)) * g z = Real.exp (-(Real.Gamma (1 - α) * s ^ α)))

include hg0 hgle hgc hgint in
/-- `t^{-σ} g(t)` is integrable on `(0, ∞)` for `0 ≤ σ < 1`. -/
theorem integrableOn_rpow_neg_mul {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    IntegrableOn (fun t => t ^ (-σ) * g t) (Ioi 0) := by
  have hG0 : 0 ≤ G0 := (hg0 0).trans (hgle 0)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (-σ) * g t) := by
    exact ((measurable_id.pow_const _).mul hgc.measurable).aestronglyMeasurable
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · have hp : IntegrableOn (fun t : ℝ => t ^ (-σ)) (Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr (by linarith)
    refine (hp.const_mul G0).mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (hg0 t))]
    rw [mul_comm G0]
    exact mul_le_mul_of_nonneg_left (hgle t) (Real.rpow_nonneg ht.1.le _)
  · refine hgint.integrableOn.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) (hg0 t))]
    calc t ^ (-σ) * g t ≤ 1 * g t :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith))
            (hg0 t)
      _ = g t := one_mul _

include hgz in
/-- The Laplace transform of `g` restricted to `(0, ∞)`. -/
theorem laplace_Ioi (hlap' : ∀ s : ℝ, 0 ≤ s →
    ∫ z, Real.exp (-(s * z)) * g z = Real.exp (-(Real.Gamma (1 - α) * s ^ α))) {s : ℝ}
    (hs : 0 ≤ s) :
    ∫ z in Ioi 0, Real.exp (-(s * z)) * g z = Real.exp (-(Real.Gamma (1 - α) * s ^ α)) := by
  rw [← hlap' s hs]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
  rw [hgz z (not_lt.mp hz), mul_zero]

/-- `x^{-p} = (1/Γ(p)) ∫_0^∞ s^{p-1} e^{-sx} ds` for `x > 0`, `Re p > 0`. -/
theorem cpow_neg_eq_integral {p : ℂ} (hp : 0 < p.re) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-p) = 1 / Complex.Gamma p *
      ∫ s : ℝ in Ioi 0, (s : ℂ) ^ (p - 1) * Complex.exp (-(x * s)) := by
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hp hx]
  have hΓ := Complex.Gamma_ne_zero_of_re_pos hp
  have harg : ((x : ℂ)).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne
  rw [one_div (x : ℂ), Complex.inv_cpow _ _ harg, Complex.cpow_neg]
  field_simp

include h0 in
/-- `∫_0^∞ s^{p-1} e^{-c s^α} ds = (1/α) (1/c)^{p/α} Γ(p/α)` (the substitution `w = s^α`). -/
theorem integral_cpow_mul_exp_neg_mul_rpow {p : ℂ} (hp : 0 < p.re) {c : ℝ} (hc : 0 < c) :
    ∫ s : ℝ in Ioi 0, (s : ℂ) ^ (p - 1) * Complex.exp (-(c * ((s ^ α : ℝ) : ℂ)))
      = 1 / α * ((1 / c : ℂ) ^ (p / α) * Complex.Gamma (p / α)) := by
  have hpα : 0 < (p / α).re := by
    rw [Complex.div_ofReal_re]; exact div_pos hp h0
  have hsub := integral_comp_rpow_Ioi
    (fun y : ℝ => (y : ℂ) ^ (p / α - 1) * Complex.exp (-(c * y))) h0.ne'
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hpα hc] at hsub
  rw [← hsub, ← smul_eq_mul (1 / (α : ℂ)), ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  simp only [abs_of_pos h0, smul_eq_mul, Complex.real_smul]
  have e1 : ((x ^ α : ℝ) : ℂ) ^ (p / α - 1) = (x : ℂ) ^ (p - α) := by
    rw [← Complex.cpow_mul_ofReal_nonneg hx0.le]
    congr 1
    have : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
    field_simp
  have e2 : (((x ^ (α - 1) : ℝ)) : ℂ) = (x : ℂ) ^ ((α : ℂ) - 1) := by
    rw [Complex.ofReal_cpow hx0.le]; push_cast; ring_nf
  rw [e1, Complex.ofReal_mul, e2]
  have e3 : (x : ℂ) ^ ((α : ℂ) - 1) * (x : ℂ) ^ (p - α) = (x : ℂ) ^ (p - 1) := by
    rw [← Complex.cpow_add _ _ hxc]; ring_nf
  have hα : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
  rw [show (1 / (α : ℂ)) * ((α : ℂ) * (x : ℂ) ^ ((α : ℂ) - 1) *
      ((x : ℂ) ^ (p - α) * Complex.exp (-(c * ((x ^ α : ℝ) : ℂ)))))
      = ((x : ℂ) ^ ((α : ℂ) - 1) * (x : ℂ) ^ (p - α)) * Complex.exp (-(c * ((x ^ α : ℝ) : ℂ))) by
      field_simp, e3]

include h0 h1 hg0 hgz hgle hgc hgint hlap in
/-- **The negative moments of `G`** (Step 4): `E G^{-p} = Γ(p/α) (1/c)^{p/α}/(α Γ(p))` for
`0 < Re p < 1`, `c = Γ(1-α)`. -/
theorem negMoment {p : ℂ} (hp0 : 0 < p.re) (hp1 : p.re < 1) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (-p) * (g t : ℂ)
      = Complex.Gamma (p / α) * (1 / (Real.Gamma (1 - α) : ℂ)) ^ (p / α)
          / (α * Complex.Gamma p) := by
  set c : ℝ := Real.Gamma (1 - α) with hc_def
  have hc : 0 < c := Real.Gamma_pos_of_pos (by linarith)
  have hΓ := Complex.Gamma_ne_zero_of_re_pos hp0
  set σ := p.re with hσ
  -- the kernel
  set K : ℝ → ℝ → ℂ := fun t s => (s : ℂ) ^ (p - 1) * Complex.exp (-(t * s)) * (g t : ℂ) with hK
  have hnormK : ∀ t s : ℝ, 0 < s → ‖K t s‖ = s ^ (σ - 1) * Real.exp (-(t * s)) * g t := by
    intro t s hs
    simp only [hK, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hs, Complex.norm_exp,
      Complex.norm_real, Real.norm_of_nonneg (hg0 t)]
    simp [hσ]
  have hKm : Measurable (Function.uncurry K) := by
    simp only [hK, Function.uncurry_def]
    refine Measurable.mul (Measurable.mul ?_ ?_) ?_
    · exact (Complex.measurable_ofReal.comp measurable_snd).pow_const _
    · exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp measurable_fst).mul
        (Complex.measurable_ofReal.comp measurable_snd)).neg
    · exact Complex.measurable_ofReal.comp (hgc.measurable.comp measurable_fst)
  have hKmeas : AEStronglyMeasurable (Function.uncurry K)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hKm.aestronglyMeasurable
  have hKint : Integrable (Function.uncurry K)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hKmeas]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      have hI : IntegrableOn (fun s : ℝ => s ^ (σ - 1) * Real.exp (-t * s ^ (1 : ℝ))) (Ioi 0) :=
        integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos ht0
      refine (hI.mul_const (g t)).mono' ?_ ?_
      · exact (hKm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        simp only [Function.uncurry_apply_pair]
        rw [hnormK t s hs, Real.rpow_one, neg_mul]
    · have hint := (integrableOn_rpow_neg_mul hg0 hgle hgc hgint (σ := σ) hp0.le hp1).mul_const
        (Real.Gamma σ)
      refine IntegrableOn.congr_fun hint (fun t ht => ?_) measurableSet_Ioi
      have ht0 : 0 < t := ht
      simp only [Function.uncurry_apply_pair]
      rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hnormK t s hs)]
      have e : ∀ s : ℝ, s ^ (σ - 1) * Real.exp (-(t * s)) * g t
          = g t * (s ^ (σ - 1) * Real.exp (-(t * s))) := fun s => by ring
      simp_rw [e]
      rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hp0 ht0,
        Real.div_rpow zero_le_one ht0.le, Real.one_rpow, Real.rpow_neg ht0.le]
      ring
  -- `E G^{-p} = (1/Γ(p)) ∫_t ∫_s K`
  have h1' : ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (-p) * (g t : ℂ)
      = 1 / Complex.Gamma p * ∫ t : ℝ in Ioi 0, ∫ s : ℝ in Ioi 0, K t s := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [cpow_neg_eq_integral hp0 ht, mul_assoc, ← integral_mul_const]
  rw [h1', integral_integral_swap hKint]
  -- the inner integral is the Laplace transform
  have hin : ∀ s ∈ Ioi (0 : ℝ), ∫ t : ℝ in Ioi 0, K t s
      = (s : ℂ) ^ (p - 1) * Complex.exp (-(c * ((s ^ α : ℝ) : ℂ))) := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    have e : ∀ t : ℝ, K t s = (s : ℂ) ^ (p - 1) * ((Real.exp (-(s * t)) * g t : ℝ) : ℂ) := by
      intro t
      simp only [hK]
      push_cast
      ring_nf
    simp_rw [e]
    rw [integral_const_mul, integral_complex_ofReal, laplace_Ioi hgz hlap hs0]
    simp only [hc_def]
    push_cast
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_cpow_mul_exp_neg_mul_rpow h0 hp0 hc]
  have hα : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
  field_simp

end moments

/-- `|Γ(1 + iy)|² = πy/sinh(πy)` for `y ≠ 0` (the reflection formula, DLMF 5.5.3). -/
theorem norm_Gamma_one_add_I_sq {y : ℝ} (hy : y ≠ 0) :
    ‖Complex.Gamma (1 + Complex.I * y)‖ ^ 2 = π * y / Real.sinh (π * y) := by
  have hiy : Complex.I * y ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hy)
  have hconj : (starRingEnd ℂ) (Complex.Gamma (1 + Complex.I * y))
      = Complex.Gamma (1 - Complex.I * y) := by
    rw [← Complex.Gamma_conj]; congr 1; simp [Complex.conj_ofReal]; ring
  have hsinh : Real.sinh (π * y) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_pos.ne' hy
  have key : Complex.Gamma (1 + Complex.I * y) * Complex.Gamma (1 - Complex.I * y)
      = ((π * y / Real.sinh (π * y) : ℝ) : ℂ) := by
    rw [add_comm, Complex.Gamma_add_one _ hiy, mul_assoc, Complex.Gamma_mul_Gamma_one_sub,
      show (π : ℂ) * (Complex.I * y) = ((π * y : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.sin_mul_I, ← Complex.ofReal_sinh]
    have : ((Real.sinh (π * y) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsinh
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    rw [Complex.ofReal_div, Complex.ofReal_mul]
    field_simp
  have h2 := Complex.mul_conj' (Complex.Gamma (1 + Complex.I * y))
  rw [hconj, key] at h2
  exact_mod_cast h2.symm

end Kagey131.PaperD.FL5
