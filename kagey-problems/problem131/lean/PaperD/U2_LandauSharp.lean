import PaperD.U2_LandauNat

/-!
# Paper D, Theorem 3.9 (a), (b) with the sharpened explicit constant `C = 889`

`U2_LandauLocal` proves Theorem 3.9(a) with `C = 3600`, bounding `s²|log s| ≤ s³ + s` in the damping
integral. Here the pointwise bound is replaced by the tangent-line bound
`s²|log s| ≤ s³/16 + (4 log 2 - 1)s² + s/e` (`log s ≤ s/16 + log 16 - 1` for `s ≥ 1`,
`s|log s| ≤ 1/e` for `0 < s < 1`), which gives

* `landau_local_cp_sharp` : `|x CP_N(m) - f_L(λ_m)| ≤ (889 + 165 log x)/x + 6.6 x/N`;
* `landau_local_cp_C` : `|x CP_N(m) - f_L(λ_m)| ≤ 889((1 + log x)/x + x/N)`;

for every integer `m`, under `x ≥ 1`, `4x ≤ N` only, and the `ℕ`-indexed and (b) forms.

The general step `landau_local_of_damp` (inversion + any damping bound `g` on `[-πx, πx]`):
`|x p(m) - f_L(λ_m)| ≤ (1/2π) ∫_{-πx}^{πx} g + 4/(π⁴ x)`.
-/

namespace Kagey131.PaperD.U2

open Complex Finset Filter Topology MeasureTheory Set
open scoped Real

noncomputable section

/-- **The inversion step of the proof of Theorem 3.9(a), for an arbitrary damping bound.** Assume
lattice Fourier inversion, `x ≥ 1`, `p` absolutely summable with characteristic function `e^{xΨ_N}`,
and `|e^{A(t)} - e^{B(t)}| ≤ g(t)` on `[-πx, πx]` with `g` continuous. Then for every integer `m`,
`|x p(m) - f_L(λ_m)| ≤ (1/2π) ∫_{-πx}^{πx} g + 4/(π⁴x)`. -/
theorem landau_local_of_damp (hInv : LatticeFourierInversionHyp) {N : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (p : ℤ → ℝ) (hps : Summable (fun k => |p k|)) (hchar : CPCharFun N x p)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : ∀ t, |t| ≤ π * x → ‖cexp (cpExponent N x t) - cexp (landauB t)‖ ≤ g t) (m : ℤ) :
    ‖((x * p m : ℝ) : ℂ) - landauDensity (lamm x m)‖
      ≤ 1 / (2 * π) * (∫ t in (-(π * x))..(π * x), g t) + 4 / (π ^ 4 * x) := by
  have hx0 : 0 < x := by linarith
  have hpi := Real.pi_pos
  set lam := lamm x m with hlam
  set L := π * x with hL
  have hL0 : 0 ≤ L := by positivity
  set GA : ℝ → ℂ := fun t => cexp (-(((lam * t : ℝ) : ℂ) * I)) * cexp (cpExponent N x t) with hGA
  set GB : ℝ → ℂ := fun t => cexp (-(((lam * t : ℝ) : ℂ) * I)) * cexp (landauB t) with hGB
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
  have hGAc : Continuous GA := by
    have := continuous_psiN N
    simp only [hGA, cpExponent]
    fun_prop
  have hGBc : Continuous GB := by
    have := continuous_landauB
    simp only [hGB]
    fun_prop
  have hD : ‖∫ t in (-L)..L, (GA t - GB t)‖ ≤ ∫ t in (-L)..L, g t := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · refine Filter.Eventually.of_forall (fun t ht => ?_)
      have htL : |t| ≤ π * x := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      simp only [hGA, hGB]
      rw [← mul_sub, norm_mul]
      have : ‖cexp (-(((lam * t : ℝ) : ℂ) * I))‖ = 1 := by
        rw [show -(((lam * t : ℝ) : ℂ) * I) = ((-(lam * t) : ℝ) : ℂ) * I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [this, one_mul]
      exact hgb t htL
    · exact hg.intervalIntegrable _ _
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
  have htail : 1 / (2 * π) * (2 * Real.exp (-(π / 2 * L)) / (π / 2)) ≤ 4 / (π ^ 4 * x) := by
    have hy : 0 < π / 2 * L := by rw [hL]; positivity
    have hexp : Real.exp (-(π / 2 * L)) ≤ 1 / (π / 2 * L) := by
      rw [Real.exp_neg, ← one_div]
      apply one_div_le_one_div_of_le hy
      have := Real.add_one_le_exp (π / 2 * L)
      linarith
    calc 1 / (2 * π) * (2 * Real.exp (-(π / 2 * L)) / (π / 2))
        ≤ 1 / (2 * π) * (2 * (1 / (π / 2 * L)) / (π / 2)) := by gcongr
      _ = 4 / (π ^ 4 * x) := by rw [hL]; field_simp; ring
  calc 1 / (2 * π) * ‖(∫ t in (-L)..L, (GA t - GB t)) - T‖
      ≤ 1 / (2 * π) * (‖∫ t in (-L)..L, (GA t - GB t)‖ + ‖T‖) := by gcongr
    _ ≤ 1 / (2 * π) * ((∫ t in (-L)..L, g t) + 2 * Real.exp (-(π / 2 * L)) / (π / 2)) := by
        gcongr
    _ = 1 / (2 * π) * (∫ t in (-L)..L, g t)
          + 1 / (2 * π) * (2 * Real.exp (-(π / 2 * L)) / (π / 2)) := by ring
    _ ≤ _ := by linarith

/-! ### The sharpened pointwise bound and damping bound -/

/-- `log y ≤ y/e` for `y > 0`. -/
lemma log_le_div_e {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / Real.exp 1 := by
  have he := Real.exp_pos 1
  have h := Real.log_le_sub_one_of_pos (div_pos hy he)
  rw [Real.log_div hy.ne' he.ne', Real.log_exp] at h
  linarith

/-- **Tangent-line bound.** `s²|log s| ≤ s³/16 + (4 log 2 - 1) s² + s/e` for `s ≥ 0`. -/
lemma sq_mul_abs_log_le_sharp {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * |Real.log s| ≤ s ^ 3 / 16 + (4 * Real.log 2 - 1) * s ^ 2 + s / Real.exp 1 := by
  have he := Real.exp_pos 1
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hc : 0 ≤ 4 * Real.log 2 - 1 := by linarith
  rcases eq_or_lt_of_le hs with h | h
  · subst h; simp
  rcases le_or_gt 1 s with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    have ht := Real.log_le_sub_one_of_pos (show 0 < s / 16 by positivity)
    rw [Real.log_div h.ne' (by norm_num : (16 : ℝ) ≠ 0),
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at ht
    push_cast at ht
    have hs2 : 0 ≤ s ^ 2 := by positivity
    have : s ^ 2 * Real.log s ≤ s ^ 2 * (s / 16 + (4 * Real.log 2 - 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hs2
    have : 0 ≤ s / Real.exp 1 := by positivity
    nlinarith
  · rw [abs_of_nonpos (Real.log_nonpos h.le h1.le)]
    have hi := log_le_div_e (inv_pos.mpr h)
    rw [Real.log_inv] at hi
    have hs1 : s * s⁻¹ = 1 := mul_inv_cancel₀ h.ne'
    have key : s ^ 2 * -Real.log s ≤ s / Real.exp 1 := by
      have : s ^ 2 * -Real.log s ≤ s ^ 2 * (s⁻¹ / Real.exp 1) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      calc s ^ 2 * -Real.log s ≤ s ^ 2 * (s⁻¹ / Real.exp 1) := this
        _ = s * (s * s⁻¹) / Real.exp 1 := by ring
        _ = s / Real.exp 1 := by rw [hs1, mul_one]
    have : 0 ≤ s ^ 3 / 16 := by positivity
    have : 0 ≤ (4 * Real.log 2 - 1) * s ^ 2 := by positivity
    linarith

/-- The sharpened damping bound
`g(t) = e^{1/2} e^{-|t|/(2π)} [(0.631(|t|³/16 + |t|/e) + (0.631(4 log 2 - 1) + 0.631 log x + 1.53)t²)/x + 2x/N]`. -/
def dampSharp (N : ℕ) (x t : ℝ) : ℝ :=
  Real.exp (1 / 2) * Real.exp (-(|t| / (2 * π))) *
    ((0.631 * (|t| ^ 3 / 16 + |t| / Real.exp 1)
      + (0.631 * (4 * Real.log 2 - 1) + 0.631 * Real.log x + 1.53) * t ^ 2) / x + 2 * x / N)

lemma continuous_dampSharp (N : ℕ) (x : ℝ) : Continuous (dampSharp N x) := by
  unfold dampSharp; fun_prop

/-- **The damping over the whole inversion interval, sharpened**: for `x ≥ 1`, `4x ≤ N`, `|t| ≤ πx`,
`|e^{A(t)} - e^{B(t)}| ≤ dampSharp N x t`. -/
theorem norm_cf_sub_le_sharp {N : ℕ} {x t : ℝ} (hx : 1 ≤ x) (hxN : 4 * x ≤ N) (ht : |t| ≤ π * x) :
    ‖cexp (cpExponent N x t) - cexp (landauB t)‖ ≤ dampSharp N x t := by
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
  have hlogt : t ^ 2 * |Real.log (|t|)|
      ≤ |t| ^ 3 / 16 + (4 * Real.log 2 - 1) * t ^ 2 + |t| / Real.exp 1 := by
    have := sq_mul_abs_log_le_sharp (abs_nonneg t)
    rwa [sq_abs] at this
  have hbr : t ^ 2 / x * (0.631 * (|Real.log (|t|)| + Real.log x) + 1.53) + 2 * x / N
      ≤ (0.631 * (|t| ^ 3 / 16 + |t| / Real.exp 1)
        + (0.631 * (4 * Real.log 2 - 1) + 0.631 * Real.log x + 1.53) * t ^ 2) / x + 2 * x / N := by
    have : t ^ 2 / x * (0.631 * (|Real.log (|t|)| + Real.log x) + 1.53)
        = (0.631 * (t ^ 2 * |Real.log (|t|)|) + (0.631 * Real.log x + 1.53) * t ^ 2) / x := by
      ring
    rw [this]
    have key : 0.631 * (t ^ 2 * |Real.log (|t|)|) + (0.631 * Real.log x + 1.53) * t ^ 2
        ≤ 0.631 * (|t| ^ 3 / 16 + |t| / Real.exp 1)
          + (0.631 * (4 * Real.log 2 - 1) + 0.631 * Real.log x + 1.53) * t ^ 2 := by
      nlinarith [hlogt]
    have := div_le_div_of_nonneg_right key hx0.le
    linarith
  unfold dampSharp
  calc ‖cexp (cpExponent N x t) - cexp (landauB t)‖
      ≤ ‖cpExponent N x t - landauB t‖ * Real.exp M := h
    _ ≤ ((0.631 * (|t| ^ 3 / 16 + |t| / Real.exp 1)
        + (0.631 * (4 * Real.log 2 - 1) + 0.631 * Real.log x + 1.53) * t ^ 2) / x + 2 * x / N)
          * (Real.exp (1 / 2) * Real.exp (-(|t| / (2 * π)))) := by
        refine mul_le_mul (hdiff.trans hbr) hM' (by positivity) ?_
        have : 0 ≤ 4 * Real.log 2 - 1 := by
          have := Real.log_two_gt_d9; linarith
        have := Real.log_nonneg hx
        positivity
    _ = _ := by ring

/-- `(1/2π)∫_{-L}^{L} g ≤ e^{1/2}[(6π³·0.631 + 16π²(0.631(4log2-1) + 0.631 log x + 1.53)
+ 4π·0.631/e)/x + 4x/N]`. -/
theorem integral_dampSharp_le {N : ℕ} {x L : ℝ} (hx : 1 ≤ x) (hNpos : (0 : ℝ) < N) (hL : 0 ≤ L) :
    (1 / (2 * π)) * ∫ t in (-L)..L, dampSharp N x t
      ≤ Real.exp (1 / 2) * ((6 * π ^ 3 * 0.631
          + 16 * π ^ 2 * (0.631 * (4 * Real.log 2 - 1) + 0.631 * Real.log x + 1.53)
          + 4 * π * 0.631 / Real.exp 1) / x + 4 * x / N) := by
  have hx0 : 0 < x := by linarith
  have hpi := Real.pi_pos
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have he1 := Real.exp_pos 1
  have hl2 : 0 ≤ 4 * Real.log 2 - 1 := by have := Real.log_two_gt_d9; linarith
  have hcont := continuous_dampSharp N x
  have heven : ∀ t, dampSharp N x (-t) = dampSharp N x t := by
    intro t; unfold dampSharp; rw [abs_neg, neg_sq]
  have hsplit : ∫ t in (-L)..L, dampSharp N x t = 2 * ∫ t in (0 : ℝ)..L, dampSharp N x t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
    have : ∫ t in (-L)..0, dampSharp N x t = ∫ t in (0 : ℝ)..L, dampSharp N x t := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := L) (dampSharp N x)
      simp only [neg_zero] at this
      rw [← this]
      exact intervalIntegral.integral_congr (fun t _ => heven t)
    rw [this]; ring
  set a : ℝ := 1 / (2 * π) with ha
  have hapos : 0 < a := by positivity
  set α : ℝ := Real.exp (1 / 2) * (0.631 / 16 / x) with hα
  set β : ℝ := Real.exp (1 / 2) *
    ((0.631 * (4 * Real.log 2 - 1) + 0.631 * Real.log x + 1.53) / x) with hβ
  set γ : ℝ := Real.exp (1 / 2) * (0.631 / Real.exp 1 / x) with hγ
  set δ : ℝ := Real.exp (1 / 2) * (2 * x / N) with hδ
  have hcongr : ∫ t in (0 : ℝ)..L, dampSharp N x t
      = ∫ t in (0 : ℝ)..L, Real.exp (-(a * t)) * (α * t ^ 3 + β * t ^ 2 + γ * t + δ) := by
    apply intervalIntegral.integral_congr
    intro t htm
    rw [uIcc_of_le hL] at htm
    have ht0 : 0 ≤ t := htm.1
    unfold dampSharp
    rw [abs_of_nonneg ht0, ha, hα, hβ, hγ, hδ]
    field_simp
    ring
  have hpoly := polyexp_integral_le hapos (by positivity : 0 ≤ α) (by positivity : 0 ≤ β)
    (by positivity : 0 ≤ γ) (by positivity : 0 ≤ δ) hL
  rw [hsplit, hcongr]
  have hfin : 1 / (2 * π) * (2 * (6 * α / a ^ 4 + 2 * β / a ^ 3 + γ / a ^ 2 + δ / a))
      = Real.exp (1 / 2) * ((6 * π ^ 3 * 0.631
          + 16 * π ^ 2 * (0.631 * (4 * Real.log 2 - 1) + 0.631 * Real.log x + 1.53)
          + 4 * π * 0.631 / Real.exp 1) / x + 4 * x / N) := by
    rw [ha, hα, hβ, hγ, hδ]
    field_simp
    ring
  rw [← hfin]
  gcongr

/-! ### Theorem 3.9 (a) and (b) with `C = 889` -/

lemma exp_half_lt : Real.exp (1 / 2) < 1.6488 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- **Theorem 3.9(a), sharp form.** Assume lattice Fourier inversion; let `x ≥ 1`, `4x ≤ N`, and
`p : ℤ → ℝ` absolutely summable with characteristic function `e^{xΨ_N}` (i.e. `p = CP_N`). Then
for every integer `m`, `|x p(m) - f_L(λ_m)| ≤ (889 + 165 log x)/x + 6.6 x/N`. -/
theorem landau_local_cp_sharp (hInv : LatticeFourierInversionHyp) {N : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hxN : 4 * x ≤ N) (p : ℤ → ℝ) (hps : Summable (fun k => |p k|)) (hchar : CPCharFun N x p)
    (m : ℤ) :
    ‖((x * p m : ℝ) : ℂ) - landauDensity (lamm x m)‖
      ≤ (889 + 165 * Real.log x) / x + 6.6 * (x / N) := by
  have hx0 : 0 < x := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hpi := Real.pi_pos
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have h := landau_local_of_damp hInv hx p hps hchar (dampSharp N x) (continuous_dampSharp N x)
    (fun t ht => norm_cf_sub_le_sharp hx hxN ht) m
  have hI := integral_dampSharp_le (N := N) hx hNpos (show 0 ≤ π * x by positivity)
  rw [show -(π * x) = -(π * x) from rfl] at h
  have he := exp_half_lt
  have he0 := Real.exp_pos (1 / 2)
  have hpi4 := Real.pi_lt_d4
  have hpi3' := Real.pi_gt_three
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have he1 := Real.exp_one_gt_d9
  have hp3 : π ^ 3 ≤ 3.1416 ^ 3 := by gcongr
  have hp2 : π ^ 2 ≤ 3.1416 ^ 2 := by gcongr
  have hpe : π / Real.exp 1 ≤ 3.1416 / 2.7182818283 := by
    apply div_le_div₀ (by norm_num) hpi4.le (by norm_num) he1.le
  have hp2l : π ^ 2 * Real.log 2 ≤ 3.1416 ^ 2 * 0.6931471808 :=
    mul_le_mul hp2 hl2.le (by linarith) (by norm_num)
  -- the constant part
  set K0 : ℝ := 6 * π ^ 3 * 0.631 + 16 * π ^ 2 * (0.631 * (4 * Real.log 2 - 1) + 1.53)
    + 4 * π * 0.631 / Real.exp 1 with hK0
  have hK0le : K0 ≤ 538.6 := by
    have : 4 * π * 0.631 / Real.exp 1 = 4 * 0.631 * (π / Real.exp 1) := by ring
    rw [hK0, this]
    nlinarith
  have hK0nn : 0 ≤ K0 := by
    have : 0 ≤ 4 * Real.log 2 - 1 := by linarith
    positivity
  have hrew : 6 * π ^ 3 * 0.631
      + 16 * π ^ 2 * (0.631 * (4 * Real.log 2 - 1) + 0.631 * Real.log x + 1.53)
      + 4 * π * 0.631 / Real.exp 1 = K0 + 16 * π ^ 2 * 0.631 * Real.log x := by
    rw [hK0]; ring
  rw [hrew] at hI
  have hlogc : 16 * π ^ 2 * 0.631 ≤ 99.66 := by nlinarith
  have hnum : Real.exp (1 / 2) * ((K0 + 16 * π ^ 2 * 0.631 * Real.log x) / x + 4 * x / N)
      ≤ 1.6488 * ((538.6 + 99.66 * Real.log x) / x + 4 * x / N) := by
    have h0 : 0 ≤ (K0 + 16 * π ^ 2 * 0.631 * Real.log x) / x + 4 * x / N := by positivity
    calc _ ≤ 1.6488 * ((K0 + 16 * π ^ 2 * 0.631 * Real.log x) / x + 4 * x / N) := by gcongr
      _ ≤ _ := by gcongr
  have htail : 4 / (π ^ 4 * x) ≤ 0.042 / x := by
    rw [div_le_div_iff₀ (by positivity) hx0]
    have : (3.14 : ℝ) ^ 4 ≤ π ^ 4 := by
      have := Real.pi_gt_d2
      gcongr
    nlinarith
  have hfinal : 1.6488 * ((538.6 + 99.66 * Real.log x) / x + 4 * x / N) + 0.042 / x
      ≤ (889 + 165 * Real.log x) / x + 6.6 * (x / N) := by
    have e1 : 1.6488 * ((538.6 + 99.66 * Real.log x) / x + 4 * x / N) + 0.042 / x
        = (1.6488 * 538.6 + 0.042 + 1.6488 * 99.66 * Real.log x) / x + 6.5952 * (x / N) := by
      ring
    rw [e1]
    have hxN0 : 0 ≤ x / N := by positivity
    have : (1.6488 * 538.6 + 0.042 + 1.6488 * 99.66 * Real.log x) / x
        ≤ (889 + 165 * Real.log x) / x :=
      div_le_div_of_nonneg_right (by nlinarith) hx0.le
    linarith
  linarith

/-- **Theorem 3.9(a) with `C = 889`**: under the hypotheses of `landau_local_cp_sharp`, for every
integer `m`, `|x CP_N(m) - f_L(λ_m)| ≤ 889((1 + log x)/x + x/N)`. -/
theorem landau_local_cp_C (hInv : LatticeFourierInversionHyp) {N : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hxN : 4 * x ≤ N) (p : ℤ → ℝ) (hps : Summable (fun k => |p k|)) (hchar : CPCharFun N x p)
    (m : ℤ) :
    ‖((x * p m : ℝ) : ℂ) - landauDensity (lamm x m)‖
      ≤ 889 * ((1 + Real.log x) / x + x / N) := by
  have h := landau_local_cp_sharp hInv hx hxN p hps hchar m
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxN0 : 0 ≤ x / (N : ℝ) := by positivity
  have : (889 + 165 * Real.log x) / x ≤ 889 * ((1 + Real.log x) / x) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hx0.le
  nlinarith

/-- **Theorem 3.9(b), sharp form**: if moreover `|f(m) - p(m)| ≤ δ` at `m`, then
`|x f(m) - f_L(λ_m)| ≤ (889 + 165 log x)/x + 6.6 x/N + xδ`. -/
theorem landau_local_fN_sharp (hInv : LatticeFourierInversionHyp) {N : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hxN : 4 * x ≤ N) (p : ℤ → ℝ) (hps : Summable (fun k => |p k|)) (hchar : CPCharFun N x p)
    (f : ℤ → ℝ) {δ : ℝ} (m : ℤ) (hcp : |f m - p m| ≤ δ) :
    ‖((x * f m : ℝ) : ℂ) - landauDensity (lamm x m)‖
      ≤ (889 + 165 * Real.log x) / x + 6.6 * (x / N) + x * δ := by
  have ha := landau_local_cp_sharp hInv hx hxN p hps hchar m
  have hx0 : 0 ≤ x := by linarith
  have : ‖((x * f m : ℝ) : ℂ) - ((x * p m : ℝ) : ℂ)‖ ≤ x * δ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← mul_sub, abs_mul,
      abs_of_nonneg hx0]
    gcongr
  calc _ = ‖(((x * f m : ℝ) : ℂ) - ((x * p m : ℝ) : ℂ))
        + (((x * p m : ℝ) : ℂ) - landauDensity (lamm x m))‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- **Theorem 3.9(a), sharp form, `ℕ`-indexed** (U1's `CPN N x`, U1 form of the characteristic
function). -/
theorem landau_local_cp_nat_sharp (hInv : LatticeFourierInversionHyp) {N : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hxN : 4 * x ≤ N) (p : ℕ → ℝ) (hp0 : ∀ m, 0 ≤ p m) (hchar : CPCharFunNat N x p) (m : ℕ) :
    ‖((x * p m : ℝ) : ℂ) - landauDensity (lamm x m)‖
      ≤ (889 + 165 * Real.log x) / x + 6.6 * (x / N) := by
  obtain ⟨hs, hc⟩ := cpCharFun_extZ hp0 hchar
  simpa using landau_local_cp_sharp hInv hx hxN (extZ p) hs hc (m : ℤ)

/-- **Theorem 3.9(b), sharp form, `ℕ`-indexed.** -/
theorem landau_local_fN_nat_sharp (hInv : LatticeFourierInversionHyp) {N : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hxN : 4 * x ≤ N) (p : ℕ → ℝ) (hp0 : ∀ m, 0 ≤ p m) (hchar : CPCharFunNat N x p)
    (f : ℕ → ℝ) {δ : ℝ} (m : ℕ) (hcp : |f m - p m| ≤ δ) :
    ‖((x * f m : ℝ) : ℂ) - landauDensity (lamm x m)‖
      ≤ (889 + 165 * Real.log x) / x + 6.6 * (x / N) + x * δ := by
  obtain ⟨hs, hc⟩ := cpCharFun_extZ hp0 hchar
  have := landau_local_fN_sharp hInv hx hxN (extZ p) hs hc (extZ f) (m : ℤ) (by simpa using hcp)
  simpa using this

end

end Kagey131.PaperD.U2
