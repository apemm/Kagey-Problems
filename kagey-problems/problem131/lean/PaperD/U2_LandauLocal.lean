import PaperD.U2_LandauClosedForm

/-!
# Paper D, Theorem 3.9 (`thm:landau`) (a) and (b): the Landau local limit with an explicit constant

Notation (Section 1 and Appendix C.2 of the paper):

* `landauDensity λ = f_L(λ) = (1/2π) ∫_ℝ e^{-iλt} e^{B(t)} dt` (the paper's definition of `f_L`;
  we keep it complex-valued, it is real by `B(-t) = conj B(t)`);
* `lamm x m = λ_m = (m - x log x)/x`;
* `cpExponent N x t = A(t) = x Ψ_N(t/x) - i t log x`;
* `CPCharFun N x p` : `p : ℤ → ℝ` has characteristic function `e^{x Ψ_N(θ)}`, i.e. `p` is the
  law `CP_N` of Section 1 (whose characteristic function is `e^{xΨ_N}` by the classical
  compound-Poisson formula; this is track U1's classical hypothesis `U1.CPCharHyp`, see
  `U2_Bridge.cpCharFunNat_CPN`).

Classical tools enter only as named hypotheses:

* `LatticeFourierInversionHyp` : Fourier inversion on `ℤ` for absolutely summable sequences.

Main results:

* `norm_cf_sub_le` : for `|t| ≤ πx`,
  `|e^{A(t)} - e^{B(t)}| ≤ e^{1/2} e^{-|t|/(2π)} [ (0.631(|t|³+|t|) + (0.631 log x + 1.53) t²)/x + 2x/N ]`
  (the damping over the whole inversion interval, Facts 1-3 and (C.1)).
* `landau_local_cp` (**Theorem 3.9(a)**, explicit constant): if `x ≥ 1` and `4x ≤ N` then for every
  integer `m`, `|x CP_N(m) - f_L(λ_m)| ≤ 3600 ((1 + log x)/x + x/N)`.
* `landau_local_fN` (**Theorem 3.9(b)**): if moreover `|f(m) - CP_N(m)| ≤ δ` then
  `|x f(m) - f_L(λ_m)| ≤ 3600 ((1 + log x)/x + x/N) + x δ`.
* `landau_local_fN_of_thmCP` : (b) with `δ = δ_B`, taking Theorem 3.8's conclusion as the hypothesis
  `ThmCPConclusion`.
-/

namespace Kagey131.PaperD.U2

open Complex Finset Filter Topology MeasureTheory Set
open scoped Real

noncomputable section

/-! ### Definitions and named hypotheses -/

/-- The Landau density of Section 1, `f_L(λ) = (1/2π) ∫_ℝ e^{-iλt} e^{B(t)} dt`. -/
def landauDensity (lam : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t : ℝ, cexp (-(((lam * t : ℝ) : ℂ) * I)) * cexp (landauB t)

/-- The Landau coordinate `λ_m = (m - x log x)/x`. -/
def lamm (x : ℝ) (m : ℤ) : ℝ := ((m : ℝ) - x * Real.log x) / x

/-- The exponent `A(t) = x Ψ_N(t/x) - i t log x` of Appendix C.2. -/
def cpExponent (N : ℕ) (x t : ℝ) : ℂ :=
  (x : ℂ) * psiN N (t / x) - (t : ℂ) * I * (Real.log x : ℂ)

/-- `p : ℤ → ℝ` has the characteristic function `e^{xΨ_N(θ)}` of the truncated compound Poisson law
`CP_N` (the law of `∑_{d=1}^{N-1} d 𝒩_d`, `𝒩_d` independent Poisson with means `x/(d(d+1))`). -/
def CPCharFun (N : ℕ) (x : ℝ) (p : ℤ → ℝ) : Prop :=
  ∀ θ : ℝ, ∑' k : ℤ, ((p k : ℝ) : ℂ) * cexp ((((k : ℝ) * θ : ℝ) : ℂ) * I) = cexp ((x : ℂ) * psiN N θ)

/-- **Classical (Fourier inversion on the lattice `ℤ`).** For an absolutely summable
`a : ℤ → ℂ` with Fourier series `φ(θ) = ∑_k a_k e^{ikθ}`, `a_m = (1/2π) ∫_{-π}^{π} e^{-imθ} φ(θ) dθ`.
Source: any text on Fourier series, e.g. Katznelson, *An Introduction to Harmonic Analysis*,
Ch. I §1 (orthogonality of `e^{ikθ}` plus termwise integration of the uniformly convergent series);
Feller, Vol. II, XV.3 / Durrett, *Probability*, Thm 3.3.14 for the probabilistic form.
It is true as stated: the series converges uniformly, so it may be integrated termwise, and
`∫_{-π}^{π} e^{i(k-m)θ} dθ = 2π [k = m]`. -/
def LatticeFourierInversionHyp : Prop :=
  ∀ a : ℤ → ℂ, Summable (fun k => ‖a k‖) → ∀ m : ℤ,
    a m = (1 / (2 * π) : ℂ) * ∫ θ in (-π)..π,
      cexp (-((((m : ℝ) * θ : ℝ) : ℂ) * I)) * ∑' k : ℤ, a k * cexp ((((k : ℝ) * θ : ℝ) : ℂ) * I)

/-! ### Elementary analytic lemmas -/

/-- `|e^a - e^b| ≤ |a - b| e^M` when `Re a, Re b ≤ M`. -/
lemma norm_cexp_sub_cexp_le {a b : ℂ} {M : ℝ} (ha : a.re ≤ M) (hb : b.re ≤ M) :
    ‖cexp a - cexp b‖ ≤ ‖a - b‖ * Real.exp M := by
  set f : ℝ → ℂ := fun s => cexp (b + (s : ℂ) * (a - b)) with hf
  have hd : ∀ s : ℝ, HasDerivAt f (cexp (b + (s : ℂ) * (a - b)) * (a - b)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => b + (s : ℂ) * (a - b)) (a - b) s := by
      have := ((hasDerivAt_id s).ofReal_comp).mul_const (a - b)
      simpa using this.const_add b
    exact h1.cexp
  have hbound : ∀ s ∈ Icc (0 : ℝ) 1, ‖cexp (b + (s : ℂ) * (a - b)) * (a - b)‖ ≤ ‖a - b‖ * Real.exp M := by
    intro s hs
    rw [norm_mul, Complex.norm_exp, mul_comm]
    gcongr
    have : (b + (s : ℂ) * (a - b)).re = (1 - s) * b.re + s * a.re := by
      simp [Complex.add_re, Complex.mul_re]; ring
    rw [this]
    nlinarith [hs.1, hs.2]
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) hbound (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one)
  simpa [hf] using this

lemma continuous_psiN (N : ℕ) : Continuous (psiN N) := by
  unfold psiN psiTerm
  fun_prop

lemma landauB_eq_mul_log (t : ℝ) :
    landauB t = -I * ((t * Real.log t : ℝ) : ℂ) - ((π / 2 * |t| : ℝ) : ℂ) := by
  unfold landauB
  rw [Real.log_abs]
  push_cast; ring

lemma continuous_landauB : Continuous landauB := by
  have : landauB = fun t => -I * ((t * Real.log t : ℝ) : ℂ) - ((π / 2 * |t| : ℝ) : ℂ) := by
    funext t; exact landauB_eq_mul_log t
  rw [this]
  have hc := Real.continuous_mul_log
  fun_prop

/-- `∫_0^L e^{-at}(αt³ + βt² + γt + δ) dt ≤ 6α/a⁴ + 2β/a³ + γ/a² + δ/a`. -/
lemma polyexp_integral_le {a α β γ δ L : ℝ} (ha : 0 < a) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    ∫ t in (0 : ℝ)..L, Real.exp (-(a * t)) * (α * t ^ 3 + β * t ^ 2 + γ * t + δ)
      ≤ 6 * α / a ^ 4 + 2 * β / a ^ 3 + γ / a ^ 2 + δ / a := by
  set Q : ℝ → ℝ := fun t => (α * t ^ 3 + β * t ^ 2 + γ * t + δ) / a
    + (3 * α * t ^ 2 + 2 * β * t + γ) / a ^ 2 + (6 * α * t + 2 * β) / a ^ 3 + 6 * α / a ^ 4 with hQ
  set F : ℝ → ℝ := fun t => -(Real.exp (-(a * t)) * Q t) with hF
  have hderiv : ∀ t, HasDerivAt F (Real.exp (-(a * t)) * (α * t ^ 3 + β * t ^ 2 + γ * t + δ)) t := by
    intro t
    have he : HasDerivAt (fun t : ℝ => Real.exp (-(a * t))) (Real.exp (-(a * t)) * (-a)) t := by
      have := (((hasDerivAt_id t).const_mul a).neg).exp
      simpa using this
    have hq : HasDerivAt Q ((3 * α * t ^ 2 + 2 * β * t + γ) / a
        + (6 * α * t + 2 * β) / a ^ 2 + 6 * α / a ^ 3) t := by
      have h3 := hasDerivAt_pow 3 t
      have h2 := hasDerivAt_pow 2 t
      have h1 := hasDerivAt_id t
      have hp := ((((h3.const_mul α).add (h2.const_mul β)).add (h1.const_mul γ)).add_const δ).div_const a
      have hp' := (((h2.const_mul (3 * α)).add (h1.const_mul (2 * β))).add_const γ).div_const (a ^ 2)
      have hp'' := ((h1.const_mul (6 * α)).add_const (2 * β)).div_const (a ^ 3)
      have := ((hp.add hp').add hp'').add_const (6 * α / a ^ 4)
      exact this.congr_deriv (by norm_num; ring)
    have := (he.mul hq).neg
    refine this.congr_deriv ?_
    rw [hQ]
    field_simp
    ring
  have hcont : Continuous (fun t => Real.exp (-(a * t)) * (α * t ^ 3 + β * t ^ 2 + γ * t + δ)) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hcont.intervalIntegrable _ _)]
  have hQL : 0 ≤ Q L := by simp only [hQ]; positivity
  have hQ0 : Q 0 = 6 * α / a ^ 4 + 2 * β / a ^ 3 + γ / a ^ 2 + δ / a := by
    simp only [hQ]; ring
  simp only [hF]
  rw [show -(a * 0) = 0 by ring, Real.exp_zero, one_mul, hQ0]
  have : 0 ≤ Real.exp (-(a * L)) * Q L := by positivity
  linarith

/-- `t ↦ e^{-c|t|}` is integrable on `ℝ` for `c > 0`. -/
lemma integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
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

/-- `∫_{|t| > L} e^{-c|t|} dt = 2e^{-cL}/c` (we only need `≤`). -/
lemma tail_integral_le {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L) :
    ∫ t in (Ioc (-L) L)ᶜ, Real.exp (-(c * |t|)) ≤ 2 * Real.exp (-(c * L)) / c := by
  rw [compl_Ioc]
  have hint := integrable_exp_neg_mul_abs hc
  rw [setIntegral_union (Set.disjoint_left.mpr (fun t h1 h2 => by
      simp only [Set.mem_Iic, Set.mem_Ioi] at h1 h2; linarith)) measurableSet_Ioi
    hint.integrableOn hint.integrableOn]
  have hI : ∫ t in Ioi L, Real.exp (-(c * |t|)) = Real.exp (-(c * L)) / c := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t => Real.exp ((-c) * t))
      (fun t ht => by
        simp only
        rw [abs_of_pos (lt_of_le_of_lt hL (mem_Ioi.mp ht))]; ring_nf)]
    rw [integral_exp_mul_Ioi (by linarith), neg_div_neg_eq, neg_mul]
  have hJ : ∫ t in Iic (-L), Real.exp (-(c * |t|)) = Real.exp (-(c * L)) / c := by
    rw [setIntegral_congr_fun measurableSet_Iic (g := fun t => Real.exp (c * t))
      (fun t ht => by
        simp only
        rw [abs_of_nonpos (by have := mem_Iic.mp ht; linarith)]; ring_nf)]
    rw [integral_exp_mul_Iic hc]
    ring_nf
  rw [hI, hJ]
  ring_nf
  exact le_rfl

/-! ### The characteristic-function estimate over the whole inversion interval -/

/-- The bound `g(t)` of the damping estimate. -/
def dampBound (N : ℕ) (x t : ℝ) : ℝ :=
  Real.exp (1 / 2) * Real.exp (-(|t| / (2 * π))) *
    ((0.631 * (|t| ^ 3 + |t|) + (0.631 * Real.log x + 1.53) * t ^ 2) / x + 2 * x / N)

/-- `s² |log s| ≤ s³ + s` for `s ≥ 0`. -/
lemma sq_mul_abs_log_le {s : ℝ} (hs : 0 ≤ s) : s ^ 2 * |Real.log s| ≤ s ^ 3 + s := by
  rcases eq_or_lt_of_le hs with h | h
  · subst h; simp
  rcases le_or_gt 1 s with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    have := Real.log_le_sub_one_of_pos h
    nlinarith
  · rw [abs_of_nonpos (Real.log_nonpos h.le h1.le)]
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr h)
    rw [Real.log_inv] at this
    have hs1 : s * s⁻¹ = 1 := mul_inv_cancel₀ h.ne'
    nlinarith

/-- `‖A(t) - B(t)‖ ≤ (t²/x)(0.631(|log|t|| + log x) + 1.53) + 2x/N` for `|t| ≤ πx`
(equation (C.1) of the paper together with Fact 1). -/
theorem norm_cpExponent_sub_landauB_le {N : ℕ} {x t : ℝ} (hN : 1 ≤ N) (hx : 1 ≤ x)
    (ht : |t| ≤ π * x) :
    ‖cpExponent N x t - landauB t‖
      ≤ t ^ 2 / x * (0.631 * (|Real.log (|t|)| + Real.log x) + 1.53) + 2 * x / N := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set θ := t / x with hθ
  have hθπ : |θ| ≤ π := by
    rw [hθ, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]; exact ht
  -- `A - B = x(Ψ_N(θ) - Ψ_∞(θ)) + x(Ψ_∞(θ) - B(θ))`
  have hsplit : cpExponent N x t - landauB t
      = (x : ℂ) * (psiN N θ - psiInf θ) + (x : ℂ) * (psiInf θ - landauB θ) := by
    unfold cpExponent
    have := landauB_scale hx0 t
    rw [← hθ] at this
    linear_combination this
  rw [hsplit]
  have h1 : ‖(x : ℂ) * (psiN N θ - psiInf θ)‖ ≤ 2 * x / N := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    have := norm_psiN_sub_psiInf_le N hN θ
    calc x * ‖psiN N θ - psiInf θ‖ ≤ x * (2 / N) := by gcongr
      _ = 2 * x / N := by ring
  have h2 : ‖(x : ℂ) * (psiInf θ - landauB θ)‖
      ≤ t ^ 2 / x * (0.631 * (|Real.log (|t|)| + Real.log x) + 1.53) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
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
  calc _ ≤ ‖(x : ℂ) * (psiN N θ - psiInf θ)‖ + ‖(x : ℂ) * (psiInf θ - landauB θ)‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- `Re A(t) ≤ -|t|/(2π) + 2x/N` for `|t| ≤ πx` (Facts 1 and 3). -/
theorem re_cpExponent_le {N : ℕ} {x t : ℝ} (hN : 1 ≤ N) (hx : 1 ≤ x) (ht : |t| ≤ π * x) :
    (cpExponent N x t).re ≤ -(|t| / (2 * π)) + 2 * x / N := by
  have hx0 : 0 < x := by linarith
  have hθπ : |t / x| ≤ π := by
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]; exact ht
  have h := re_psiN_le N hN hθπ
  have hre : (cpExponent N x t).re = x * (psiN N (t / x)).re := by
    unfold cpExponent
    simp [Complex.mul_re, Complex.sub_re]
  rw [hre]
  have habs : |t / x| = |t| / x := by rw [abs_div, abs_of_pos hx0]
  rw [habs] at h
  have : x * (psiN N (t / x)).re ≤ x * (-(|t| / x / (2 * π)) + 2 / N) := by gcongr
  calc x * (psiN N (t / x)).re ≤ x * (-(|t| / x / (2 * π)) + 2 / N) := this
    _ = -(|t| / (2 * π)) + 2 * x / N := by field_simp

/-- **The damping over the whole inversion interval** (Appendix C.2, proof of (a)): for
`x ≥ 1`, `4x ≤ N` and `|t| ≤ πx`, `|e^{A(t)} - e^{B(t)}| ≤ g(t)` with `g = dampBound`. -/
theorem norm_cf_sub_le {N : ℕ} {x t : ℝ} (hx : 1 ≤ x) (hxN : 4 * x ≤ N) (ht : |t| ≤ π * x) :
    ‖cexp (cpExponent N x t) - cexp (landauB t)‖ ≤ dampBound N x t := by
  have hx0 : 0 < x := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have hpi := Real.pi_pos
  set M := -(|t| / (2 * π)) + 2 * x / N with hM
  have hA := re_cpExponent_le hN hx ht
  have hB : (landauB t).re ≤ M := by
    rw [re_landauB, hM]
    have : |t| / (2 * π) ≤ π / 2 * |t| := by
      rw [div_le_iff₀ (by positivity)]
      have := Real.pi_gt_three
      have h0 := abs_nonneg t
      have h1 : 1 ≤ π ^ 2 := by nlinarith
      calc |t| = 1 * |t| := by ring
        _ ≤ π ^ 2 * |t| := by gcongr
        _ = π / 2 * |t| * (2 * π) := by ring
    have : 0 ≤ 2 * x / N := by positivity
    linarith
  have h := norm_cexp_sub_cexp_le hA hB
  have hdiff := norm_cpExponent_sub_landauB_le hN hx ht
  have hM' : Real.exp M ≤ Real.exp (1 / 2) * Real.exp (-(|t| / (2 * π))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hM]
    have : 2 * x / N ≤ 1 / 2 := by rw [div_le_iff₀ hNpos]; linarith
    linarith
  have hlogt : t ^ 2 * |Real.log (|t|)| ≤ |t| ^ 3 + |t| := by
    rw [← sq_abs t]; exact sq_mul_abs_log_le (abs_nonneg t)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hbr : t ^ 2 / x * (0.631 * (|Real.log (|t|)| + Real.log x) + 1.53) + 2 * x / N
      ≤ (0.631 * (|t| ^ 3 + |t|) + (0.631 * Real.log x + 1.53) * t ^ 2) / x + 2 * x / N := by
    have : t ^ 2 / x * (0.631 * (|Real.log (|t|)| + Real.log x) + 1.53)
        = (0.631 * (t ^ 2 * |Real.log (|t|)|) + (0.631 * Real.log x + 1.53) * t ^ 2) / x := by
      ring
    rw [this]
    gcongr
  unfold dampBound
  calc ‖cexp (cpExponent N x t) - cexp (landauB t)‖
      ≤ ‖cpExponent N x t - landauB t‖ * Real.exp M := h
    _ ≤ ((0.631 * (|t| ^ 3 + |t|) + (0.631 * Real.log x + 1.53) * t ^ 2) / x + 2 * x / N)
          * (Real.exp (1 / 2) * Real.exp (-(|t| / (2 * π)))) := by
        exact mul_le_mul (hdiff.trans hbr) hM' (by positivity) (by positivity)
    _ = _ := by ring

/-- `∫_{-L}^{L} g ≤ e^{1/2} [ (96π³·0.631 + 4π·0.631 + 16π²(0.631 log x + 1.53))/x + 4x/N ]`. -/
theorem integral_dampBound_le {N : ℕ} {x L : ℝ} (hx : 1 ≤ x) (hNpos : (0 : ℝ) < N) (hL : 0 ≤ L) :
    (1 / (2 * π)) * ∫ t in (-L)..L, dampBound N x t
      ≤ Real.exp (1 / 2) * ((96 * π ^ 3 * 0.631 + 4 * π * 0.631
          + 16 * π ^ 2 * (0.631 * Real.log x + 1.53)) / x + 4 * x / N) := by
  have hx0 : 0 < x := by linarith
  have hpi := Real.pi_pos
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hcont : Continuous (dampBound N x) := by unfold dampBound; fun_prop
  -- split at `0` and reflect
  have heven : ∀ t, dampBound N x (-t) = dampBound N x t := by
    intro t; unfold dampBound; rw [abs_neg, neg_sq]
  have hsplit : ∫ t in (-L)..L, dampBound N x t = 2 * ∫ t in (0 : ℝ)..L, dampBound N x t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
    have : ∫ t in (-L)..0, dampBound N x t = ∫ t in (0 : ℝ)..L, dampBound N x t := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := L) (dampBound N x)
      simp only [neg_zero] at this
      rw [← this]
      exact intervalIntegral.integral_congr (fun t _ => heven t)
    rw [this]; ring
  set a : ℝ := 1 / (2 * π) with ha
  have hapos : 0 < a := by positivity
  set α : ℝ := Real.exp (1 / 2) * (0.631 / x) with hα
  set β : ℝ := Real.exp (1 / 2) * ((0.631 * Real.log x + 1.53) / x) with hβ
  set γ : ℝ := Real.exp (1 / 2) * (0.631 / x) with hγ
  set δ : ℝ := Real.exp (1 / 2) * (2 * x / N) with hδ
  have hcongr : ∫ t in (0 : ℝ)..L, dampBound N x t
      = ∫ t in (0 : ℝ)..L, Real.exp (-(a * t)) * (α * t ^ 3 + β * t ^ 2 + γ * t + δ) := by
    apply intervalIntegral.integral_congr
    intro t htm
    rw [uIcc_of_le hL] at htm
    have ht0 : 0 ≤ t := htm.1
    unfold dampBound
    rw [abs_of_nonneg ht0, ha, hα, hβ, hγ, hδ]
    field_simp
    ring
  have hpoly := polyexp_integral_le hapos (by positivity : 0 ≤ α) (by positivity : 0 ≤ β)
    (by positivity : 0 ≤ γ) (by positivity : 0 ≤ δ) hL
  rw [hsplit, hcongr]
  have hfin : 1 / (2 * π) * (2 * (6 * α / a ^ 4 + 2 * β / a ^ 3 + γ / a ^ 2 + δ / a))
      = Real.exp (1 / 2) * ((96 * π ^ 3 * 0.631 + 4 * π * 0.631
          + 16 * π ^ 2 * (0.631 * Real.log x + 1.53)) / x + 4 * x / N) := by
    rw [ha, hα, hβ, hγ, hδ]
    field_simp
    ring
  rw [← hfin]
  gcongr

/-! ### Theorem 3.9 (a) and (b) -/

lemma integrable_landau_integrand (lam : ℝ) :
    Integrable (fun t : ℝ => cexp (-(((lam * t : ℝ) : ℂ) * I)) * cexp (landauB t)) := by
  have hint := integrable_exp_neg_mul_abs (c := π / 2) (by positivity)
  refine hint.mono' ?_ ?_
  · have : Continuous (fun t : ℝ => cexp (-(((lam * t : ℝ) : ℂ) * I)) * cexp (landauB t)) := by
      have := continuous_landauB
      fun_prop
    exact this.aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun t => ?_)
    rw [norm_mul, norm_exp_landauB]
    have : ‖cexp (-(((lam * t : ℝ) : ℂ) * I))‖ = 1 := by
      rw [show -(((lam * t : ℝ) : ℂ) * I) = ((-(lam * t) : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [this, one_mul]

/-- **Theorem 3.9(a)** (`thm:landau`(a)), with an explicit constant: assume Fourier inversion on `ℤ`
(`LatticeFourierInversionHyp`). Let `x ≥ 1`, `4x ≤ N` (implied by (H): `N ≥ 64`, `ε ≤ 1/4`,
`x = Nε ≥ 1`), and let `p : ℤ → ℝ` be absolutely summable with characteristic function
`e^{xΨ_N}` (i.e. `p = CP_N`). Then for every integer `m`,
`|x p(m) - f_L(λ_m)| ≤ 3600 ((1 + log x)/x + x/N)`. -/
theorem landau_local_cp (hInv : LatticeFourierInversionHyp) {N : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hxN : 4 * x ≤ N) (p : ℤ → ℝ) (hps : Summable (fun k => |p k|)) (hchar : CPCharFun N x p)
    (m : ℤ) :
    ‖((x * p m : ℝ) : ℂ) - landauDensity (lamm x m)‖
      ≤ 3600 * ((1 + Real.log x) / x + x / N) := by
  have hx0 : 0 < x := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hpi := Real.pi_pos
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set lam := lamm x m with hlam
  set L := π * x with hL
  have hL0 : 0 ≤ L := by positivity
  set GA : ℝ → ℂ := fun t => cexp (-(((lam * t : ℝ) : ℂ) * I)) * cexp (cpExponent N x t) with hGA
  set GB : ℝ → ℂ := fun t => cexp (-(((lam * t : ℝ) : ℂ) * I)) * cexp (landauB t) with hGB
  -- Step 1: `x p(m) = (1/2π) ∫_{-L}^{L} G_A`
  have hstep1 : ((x * p m : ℝ) : ℂ) = (1 / (2 * π) : ℂ) * ∫ t in (-L)..L, GA t := by
    have hsum : Summable (fun k => ‖((p k : ℝ) : ℂ)‖) := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using hps
    have hinv := hInv (fun k => ((p k : ℝ) : ℂ)) hsum m
    set H : ℝ → ℂ := fun θ => cexp (-((((m : ℝ) * θ : ℝ) : ℂ) * I)) * cexp ((x : ℂ) * psiN N θ)
      with hH
    have hinv2 : ((p m : ℝ) : ℂ) = (1 / (2 * π) : ℂ) * ∫ θ in (-π)..π, H θ := by
      refine hinv.trans ?_
      congr 1
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      simp only [hH]
      rw [← hchar θ]
    have hcomp := intervalIntegral.integral_comp_div (a := -L) (b := L) H hx0.ne'
    have e1 : -L / x = -π := by rw [hL]; field_simp
    have e2 : L / x = π := by rw [hL]; field_simp
    rw [e1, e2] at hcomp
    have hHA : (fun t => H (t / x)) = GA := by
      funext t
      simp only [hH, hGA, cpExponent, hlam, lamm]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
      push_cast
      field_simp
      ring
    rw [hHA] at hcomp
    rw [hcomp, Complex.real_smul]
    push_cast
    rw [hinv2]
    ring
  -- Step 2: `f_L(λ) = (1/2π)(∫_{-L}^{L} G_B + T)` with `‖T‖ ≤ 2e^{-πL/2}/(π/2)`
  have hGBint : Integrable GB := integrable_landau_integrand lam
  set T : ℂ := ∫ t in (Ioc (-L) L)ᶜ, GB t with hT
  have hstep2 : landauDensity lam = (1 / (2 * π) : ℂ) * ((∫ t in (-L)..L, GB t) + T) := by
    unfold landauDensity
    rw [intervalIntegral.integral_of_le (by linarith), hT,
      integral_add_compl measurableSet_Ioc hGBint]
  have hTbound : ‖T‖ ≤ 2 * Real.exp (-(π / 2 * L)) / (π / 2) := by
    rw [hT]
    calc ‖∫ t in (Ioc (-L) L)ᶜ, GB t‖ ≤ ∫ t in (Ioc (-L) L)ᶜ, ‖GB t‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ t in (Ioc (-L) L)ᶜ, Real.exp (-(π / 2 * |t|)) := by
          congr 1; funext t
          simp only [hGB]
          rw [norm_mul, norm_exp_landauB]
          have : ‖cexp (-(((lam * t : ℝ) : ℂ) * I))‖ = 1 := by
            rw [show -(((lam * t : ℝ) : ℂ) * I) = ((-(lam * t) : ℝ) : ℂ) * I by push_cast; ring]
            exact Complex.norm_exp_ofReal_mul_I _
          rw [this, one_mul]
      _ ≤ _ := tail_integral_le (by positivity) hL0
  -- Step 3: the main interval
  have hGAc : Continuous GA := by
    have := continuous_psiN N
    simp only [hGA, cpExponent]
    fun_prop
  have hGBc : Continuous GB := by
    have := continuous_landauB
    simp only [hGB]
    fun_prop
  have hD : ‖∫ t in (-L)..L, (GA t - GB t)‖ ≤ ∫ t in (-L)..L, dampBound N x t := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · refine Filter.Eventually.of_forall (fun t ht => ?_)
      have htL : |t| ≤ π * x := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      simp only [hGA, hGB]
      rw [← mul_sub, norm_mul]
      have : ‖cexp (-(((lam * t : ℝ) : ℂ) * I))‖ = 1 := by
        rw [show -(((lam * t : ℝ) : ℂ) * I) = ((-(lam * t) : ℝ) : ℂ) * I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [this, one_mul]
      exact norm_cf_sub_le hx hxN htL
    · have : Continuous (dampBound N x) := by unfold dampBound; fun_prop
      exact this.intervalIntegrable _ _
  have hIntD := integral_dampBound_le (N := N) hx hNpos hL0
  -- combine
  have hcomb : ((x * p m : ℝ) : ℂ) - landauDensity lam
      = (1 / (2 * π) : ℂ) * ((∫ t in (-L)..L, (GA t - GB t)) - T) := by
    rw [hstep1, hstep2, intervalIntegral.integral_sub (hGAc.intervalIntegrable _ _)
      (hGBc.intervalIntegrable _ _)]
    ring
  rw [hcomb, norm_mul]
  have hnorm2pi : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm2pi]
  have htri : ‖(∫ t in (-L)..L, (GA t - GB t)) - T‖ ≤ ‖∫ t in (-L)..L, (GA t - GB t)‖ + ‖T‖ :=
    norm_sub_le _ _
  -- the tail is at most `4/(π⁴ x)` after the factor `1/(2π)`
  have htail : 1 / (2 * π) * (2 * Real.exp (-(π / 2 * L)) / (π / 2)) ≤ 1 / x := by
    have hy : 0 < π / 2 * L := by rw [hL]; positivity
    have hexp : Real.exp (-(π / 2 * L)) ≤ 1 / (π / 2 * L) := by
      rw [Real.exp_neg, ← one_div]
      apply one_div_le_one_div_of_le hy
      have := Real.add_one_le_exp (π / 2 * L)
      linarith
    have h3 := Real.pi_gt_three
    calc 1 / (2 * π) * (2 * Real.exp (-(π / 2 * L)) / (π / 2))
        ≤ 1 / (2 * π) * (2 * (1 / (π / 2 * L)) / (π / 2)) := by gcongr
      _ = 4 / (π ^ 4 * x) := by rw [hL]; field_simp; ring
      _ ≤ 1 / x := by
          rw [div_le_div_iff₀ (by positivity) hx0]
          have : (3 : ℝ) ^ 4 ≤ π ^ 4 := by gcongr
          nlinarith
  -- numerics: `e^{1/2} < 1.65`, `π < 3.1416`
  have he : Real.exp (1 / 2) < 1.65 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hpi4 := Real.pi_lt_d4
  have hnum : Real.exp (1 / 2) * ((96 * π ^ 3 * 0.631 + 4 * π * 0.631
          + 16 * π ^ 2 * (0.631 * Real.log x + 1.53)) / x + 4 * x / N) + 1 / x
      ≤ 3600 * ((1 + Real.log x) / x + x / N) := by
    have hp3 : π ^ 3 ≤ 3.1416 ^ 3 := by gcongr
    have hp2 : π ^ 2 ≤ 3.1416 ^ 2 := by gcongr
    have he0 := Real.exp_pos (1 / 2)
    have hk : 96 * π ^ 3 * 0.631 + 4 * π * 0.631 + 16 * π ^ 2 * (0.631 * Real.log x + 1.53)
        ≤ 2130 + 100 * Real.log x := by nlinarith
    have hk0 : 0 ≤ 96 * π ^ 3 * 0.631 + 4 * π * 0.631 + 16 * π ^ 2 * (0.631 * Real.log x + 1.53) := by
      positivity
    have e1 : Real.exp (1 / 2) * ((96 * π ^ 3 * 0.631 + 4 * π * 0.631
          + 16 * π ^ 2 * (0.631 * Real.log x + 1.53)) / x + 4 * x / N)
        ≤ 1.65 * ((2130 + 100 * Real.log x) / x + 4 * x / N) := by
      have : 0 ≤ (96 * π ^ 3 * 0.631 + 4 * π * 0.631
          + 16 * π ^ 2 * (0.631 * Real.log x + 1.53)) / x + 4 * x / N := by positivity
      calc _ ≤ 1.65 * ((96 * π ^ 3 * 0.631 + 4 * π * 0.631
          + 16 * π ^ 2 * (0.631 * Real.log x + 1.53)) / x + 4 * x / N) := by gcongr
        _ ≤ _ := by gcongr
    have e2 : 1.65 * ((2130 + 100 * Real.log x) / x + 4 * x / N) + 1 / x
        ≤ 3600 * ((1 + Real.log x) / x + x / N) := by
      have hxN0 : 0 ≤ x / N := by positivity
      have : 1.65 * ((2130 + 100 * Real.log x) / x + 4 * x / N) + 1 / x
          = (3515.5 + 165 * Real.log x) / x + 6.6 * (x / N) := by ring
      rw [this]
      have : 3600 * ((1 + Real.log x) / x + x / N) = (3600 + 3600 * Real.log x) / x
          + 3600 * (x / N) := by ring
      rw [this]
      have : (3515.5 + 165 * Real.log x) / x ≤ (3600 + 3600 * Real.log x) / x := by
        exact div_le_div_of_nonneg_right (by nlinarith) hx0.le
      linarith
    linarith
  calc 1 / (2 * π) * ‖(∫ t in (-L)..L, (GA t - GB t)) - T‖
      ≤ 1 / (2 * π) * (‖∫ t in (-L)..L, (GA t - GB t)‖ + ‖T‖) := by gcongr
    _ ≤ 1 / (2 * π) * ((∫ t in (-L)..L, dampBound N x t)
          + 2 * Real.exp (-(π / 2 * L)) / (π / 2)) := by gcongr
    _ = 1 / (2 * π) * (∫ t in (-L)..L, dampBound N x t)
          + 1 / (2 * π) * (2 * Real.exp (-(π / 2 * L)) / (π / 2)) := by ring
    _ ≤ _ := by linarith

/-- **Theorem 3.9(b)** (`thm:landau`(b)), pointwise form: under the hypotheses of (a), if
`|f(m) - CP_N(m)| ≤ δ` at the integer `m`, then `|x f(m) - f_L(λ_m)| ≤ 3600((1+log x)/x + x/N) + xδ`. -/
theorem landau_local_fN (hInv : LatticeFourierInversionHyp) {N : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hxN : 4 * x ≤ N) (p : ℤ → ℝ) (hps : Summable (fun k => |p k|)) (hchar : CPCharFun N x p)
    (f : ℤ → ℝ) {δ : ℝ} (m : ℤ) (hcp : |f m - p m| ≤ δ) :
    ‖((x * f m : ℝ) : ℂ) - landauDensity (lamm x m)‖
      ≤ 3600 * ((1 + Real.log x) / x + x / N) + x * δ := by
  have ha := landau_local_cp hInv hx hxN p hps hchar m
  have hx0 : 0 ≤ x := by linarith
  have : ‖((x * f m : ℝ) : ℂ) - ((x * p m : ℝ) : ℂ)‖ ≤ x * δ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← mul_sub, abs_mul,
      abs_of_nonneg hx0]
    gcongr
  calc _ = ‖(((x * f m : ℝ) : ℂ) - ((x * p m : ℝ) : ℂ))
        + (((x * p m : ℝ) : ℂ) - landauDensity (lamm x m))‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by linarith

/-! ### Transfer through Theorem 3.8 -/

/-- The bound `δ_B = x² log N/N + (4x²/N) e^{4x²/N} + 4x²(H_N² + H_N)/N` of Theorem 3.8, with
`x = Nε` and `H_N = ∑_{j=1}^N 1/j` (Mathlib's `harmonic N`; U1's `Hr N` equals it by
`U1.Hr_eq_harmonic`). -/
def deltaB (N : ℕ) (ε : ℝ) : ℝ :=
  ((N : ℝ) * ε) ^ 2 * Real.log N / N + 4 * ((N : ℝ) * ε) ^ 2 / N * Real.exp (4 * ((N : ℝ) * ε) ^ 2 / N)
    + 4 * ((N : ℝ) * ε) ^ 2 * ((harmonic N : ℝ) ^ 2 + (harmonic N : ℝ)) / N

/-- **The conclusion of Theorem 3.8** (`thm:cp`) as a hypothesis, for the law `f` of `M_N`
(`f m = P(M_N = m)`) and the law `p = CP_N`: `sup_{m ≥ 0} |f_N(m) - CP_N(m)| ≤ δ_B`.
Track U1 formalizes Theorem 3.8; the integrator discharges this hypothesis with U1's theorem
(for `m < 0` both laws vanish, so only `m ≥ 0` is asked). -/
def ThmCPConclusion (N : ℕ) (ε : ℝ) (f p : ℤ → ℝ) : Prop :=
  ∀ m : ℤ, 0 ≤ m → |f m - p m| ≤ deltaB N ε

/-- **Theorem 3.9(b)** with `δ = δ_B`: assume (H) (`N ≥ 64` is not needed; we use `x = Nε ≥ 1`,
`ε ≤ 1/4`), Fourier inversion on `ℤ`, and Theorem 3.8's conclusion. Then for every integer `m ≥ 0`,
`|x f_N(m) - f_L(λ_m)| ≤ 3600((1+log x)/x + x/N) + x δ_B`. -/
theorem landau_local_fN_of_thmCP (hInv : LatticeFourierInversionHyp) {N : ℕ} {ε : ℝ}
    (hε : ε ≤ 1 / 4) (hx : 1 ≤ (N : ℝ) * ε) (p : ℤ → ℝ) (hps : Summable (fun k => |p k|))
    (hchar : CPCharFun N ((N : ℝ) * ε) p) (f : ℤ → ℝ) (hcp : ThmCPConclusion N ε f p)
    (m : ℤ) (hm : 0 ≤ m) :
    ‖(((N * ε) * f m : ℝ) : ℂ) - landauDensity (lamm (N * ε) m)‖
      ≤ 3600 * ((1 + Real.log (N * ε)) / (N * ε) + (N * ε) / N) + (N * ε) * deltaB N ε := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hxN : 4 * ((N : ℝ) * ε) ≤ N := by nlinarith
  exact landau_local_fN hInv hx hxN p hps hchar f m (hcp m hm)

end

end Kagey131.PaperD.U2
