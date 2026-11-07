import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Mellin calculus for the analytic threshold argument

This file checks the two integrations by parts in `app_analytic_threshold.tex`.
All transforms are Bochner integrals on `(0, ∞)`.
The functions denoted `w₁`, `w₂` are certified derivatives, not formal symbols.
Endpoint limits and absolute convergence are explicit analytic inputs.

This does not identify the exponentially randomized characteristic function,
construct the H parametrization, or identify a Fourier integral with curvature.
-/

open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace Kagey131.PaperD.AnalyticThresholdMellin

/-- The complex power derivative along the positive real axis, including exponent zero. -/
theorem hasDerivAt_positive_cpow (z : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ z) (z * (x : ℂ) ^ (z - 1)) x := by
  by_cases hz : z = 0
  · simpa [hz] using (hasDerivAt_const x (1 : ℂ))
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hz

/-- One integration by parts. The hypotheses are absolute integrability of the
two Mellin integrands, a derivative on `(0, ∞)`, and vanishing boundary products. -/
theorem mellin_derivative (w w₁ : ℝ → ℂ) (z : ℂ)
    (hw : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt w (w₁ x) x)
    (h₀ : MellinConvergent w z) (h₁ : MellinConvergent w₁ (z + 1))
    (hb₀ : Tendsto (fun x : ℝ => (x : ℂ) ^ z * w x) (𝓝[>] 0) (𝓝 0))
    (hbTop : Tendsto (fun x : ℝ => (x : ℂ) ^ z * w x) atTop (𝓝 0)) :
    mellin w₁ (z + 1) = -z * mellin w z := by
  have hi₁ : IntegrableOn (fun x : ℝ => (x : ℂ) ^ z * w₁ x) (Ioi 0) := by
    simpa only [MellinConvergent, add_sub_cancel_right, smul_eq_mul] using h₁
  have hi₀ : IntegrableOn (fun x : ℝ => z * (x : ℂ) ^ (z - 1) * w x) (Ioi 0) := by
    simpa only [MellinConvergent, IntegrableOn, smul_eq_mul, mul_assoc] using h₀.const_mul z
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x hx => hasDerivAt_positive_cpow z hx) hw hi₁ hi₀ hb₀ hbTop
  simpa only [mellin, add_sub_cancel_right, smul_eq_mul, mul_assoc,
    integral_const_mul, sub_self, zero_sub, neg_mul] using h

/-- Two genuine integrations by parts, with no division by the Mellin parameter.
For the manuscript substitute `z = 1 - a*s`. -/
theorem mellin_second_derivative (w w₁ w₂ : ℝ → ℂ) (z : ℂ)
    (hw : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt w (w₁ x) x)
    (hw₁ : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt w₁ (w₂ x) x)
    (h₀ : MellinConvergent w z) (h₁ : MellinConvergent w₁ (z + 1))
    (h₂ : MellinConvergent w₂ (z + 1 + 1))
    (hb₀ : Tendsto (fun x : ℝ => (x : ℂ) ^ z * w x) (𝓝[>] 0) (𝓝 0))
    (hbTop : Tendsto (fun x : ℝ => (x : ℂ) ^ z * w x) atTop (𝓝 0))
    (hb₁₀ : Tendsto (fun x : ℝ => (x : ℂ) ^ (z + 1) * w₁ x) (𝓝[>] 0) (𝓝 0))
    (hb₁Top : Tendsto (fun x : ℝ => (x : ℂ) ^ (z + 1) * w₁ x) atTop (𝓝 0)) :
    mellin w₂ (z + 1 + 1) = z * (z + 1) * mellin w z := by
  rw [mellin_derivative w₁ w₂ (z + 1) hw₁ h₁ h₂ hb₁₀ hb₁Top,
    mellin_derivative w w₁ z hw h₀ h₁ hb₀ hbTop]
  ring

/-- Standard hypotheses for the two integrations by parts at one parameter.
In particular, this structure contains no transform equality. -/
structure TwiceAdmissible (w w₁ w₂ : ℝ → ℂ) (z : ℂ) : Prop where
  deriv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt w (w₁ x) x
  deriv₁ : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt w₁ (w₂ x) x
  convergent : MellinConvergent w z
  convergent₁ : MellinConvergent w₁ (z + 1)
  convergent₂ : MellinConvergent w₂ (z + 1 + 1)
  zero : Tendsto (fun x : ℝ => (x : ℂ) ^ z * w x) (𝓝[>] 0) (𝓝 0)
  top : Tendsto (fun x : ℝ => (x : ℂ) ^ z * w x) atTop (𝓝 0)
  zero₁ : Tendsto (fun x : ℝ => (x : ℂ) ^ (z + 1) * w₁ x) (𝓝[>] 0) (𝓝 0)
  top₁ : Tendsto (fun x : ℝ => (x : ℂ) ^ (z + 1) * w₁ x) atTop (𝓝 0)

/-- Gamma recurrence normalizes the result of the integrations by parts.
The only transform equality assumed is the *initial* identity at `z`.
The integral with the second derivative is derived. -/
theorem normalized_second_mellin (w w₁ w₂ : ℝ → ℂ) (z F : ℂ)
    (h : TwiceAdmissible w w₁ w₂ z) (hz : 0 < z.re)
    (hinitial : mellin w z = Gamma z * F) :
    F = (Gamma (z + 1 + 1))⁻¹ * mellin w₂ (z + 1 + 1) := by
  have hz₀ : z ≠ 0 := ne_of_apply_ne re (by simpa using hz.ne')
  have hz₁ : z + 1 ≠ 0 := by
    intro heq
    have := congrArg re heq
    simp only [add_re, one_re, zero_re] at this
    linarith
  have hg := Gamma_ne_zero_of_re_pos hz
  have hgshift : Gamma (z + 1 + 1) = z * (z + 1) * Gamma z := by
    rw [Gamma_add_one (z + 1) hz₁, Gamma_add_one z hz₀]
    ring
  rw [mellin_second_derivative w w₁ w₂ z h.deriv h.deriv₁
    h.convergent h.convergent₁ h.convergent₂ h.zero h.top h.zero₁ h.top₁,
    hinitial, hgshift]
  field_simp

/-- The open vertical strip `0 < re s < k/a`. -/
def strip (a k : ℝ) : Set ℂ := {s | 0 < s.re ∧ s.re < k / a}

theorem isOpen_strip (a k : ℝ) : IsOpen (strip a k) :=
  (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)

theorem isPreconnected_strip (a k : ℝ) : IsPreconnected (strip a k) :=
  ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt (k / a))).isPreconnected

/-- The integral after the two integrations by parts, with the gamma factor
that is regular on the larger strip. The definition itself asserts no convergence. -/
noncomputable def continuedMellin (a : ℝ) (w₂ : ℝ → ℂ) (s : ℂ) : ℂ :=
  (Gamma (3 - (a : ℂ) * s))⁻¹ * mellin w₂ (3 - (a : ℂ) * s)

/-- Local integrability and the manuscript's `O(u⁻³)` / bounded-at-zero
bounds imply absolute convergence throughout the larger strip. -/
theorem continuedMellin_convergent {a : ℝ} (ha : 0 < a) (w₂ : ℝ → ℂ)
    (hloc : LocallyIntegrableOn w₂ (Ioi 0))
    (hTop : w₂ =O[atTop] (fun u : ℝ => u ^ (-(3 : ℝ))))
    (hzero : w₂ =O[𝓝[>] 0] (fun u : ℝ => u ^ (-(0 : ℝ))))
    {s : ℂ} (hs : s ∈ strip a 3) :
    MellinConvergent w₂ (3 - (a : ℂ) * s) := by
  have hs₁ : a * s.re < 3 := by simpa [mul_comm] using (lt_div_iff₀ ha).mp hs.2
  have hs₀ : 0 < a * s.re := mul_pos ha hs.1
  apply mellinConvergent_of_isBigO_rpow hloc hTop _ hzero
  all_goals simp only [sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    re_ofNat]; linarith

/-- Holomorphy of the continued integral follows from the same standard decay
bounds. No holomorphy of a merely formal integral is postulated. -/
theorem continuedMellin_analyticOnNhd {a : ℝ} (ha : 0 < a) (w₂ : ℝ → ℂ)
    (hloc : LocallyIntegrableOn w₂ (Ioi 0))
    (hTop : w₂ =O[atTop] (fun u : ℝ => u ^ (-(3 : ℝ))))
    (hzero : w₂ =O[𝓝[>] 0] (fun u : ℝ => u ^ (-(0 : ℝ)))) :
    AnalyticOnNhd ℂ (continuedMellin a w₂) (strip a 3) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_strip a 3)
  intro s hs
  have hs₁ : a * s.re < 3 := by simpa [mul_comm] using (lt_div_iff₀ ha).mp hs.2
  have hs₀ : 0 < a * s.re := mul_pos ha hs.1
  have hshift : Differentiable ℂ (fun z : ℂ => 3 - (a : ℂ) * z) :=
    (differentiable_const (3 : ℂ)).sub ((differentiable_const (a : ℂ)).mul differentiable_id)
  have hm : DifferentiableAt ℂ (mellin w₂) (3 - (a : ℂ) * s) := by
    apply mellin_differentiableAt_of_isBigO_rpow hloc hTop _ hzero
    all_goals simp only [sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      re_ofNat]; linarith
  exact ((differentiable_one_div_Gamma.differentiableAt.comp s (hshift s)).mul
    (hm.comp s (hshift s))).differentiableWithinAt

/-- Continuation from `0 < re s < 1/a` to `0 < re s < 3/a`.

Exact inputs: `a > 0`; holomorphy of `F` on the larger strip; local
integrability, boundedness at zero, and cubic decay of `w₂`; the standard
integration-by-parts data on the smaller strip; and the initial identity
`mellin w (1-a*s) = Gamma (1-a*s) * F s` there.

Neither the continued identity nor the exponential-randomization identity is
proved by a hypothesis with the same conclusion: the initial identity is
strictly confined to the smaller strip, and its application-specific proof
remains a separate bridge. -/
theorem mellin_continuation {a : ℝ} (ha : 0 < a)
    (w w₁ w₂ : ℝ → ℂ) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (strip a 3))
    (hloc : LocallyIntegrableOn w₂ (Ioi 0))
    (hTop : w₂ =O[atTop] (fun u : ℝ => u ^ (-(3 : ℝ))))
    (hzero : w₂ =O[𝓝[>] 0] (fun u : ℝ => u ^ (-(0 : ℝ))))
    (hparts : ∀ s ∈ strip a 1, TwiceAdmissible w w₁ w₂ (1 - (a : ℂ) * s))
    (hinitial : ∀ s ∈ strip a 1,
      mellin w (1 - (a : ℂ) * s) = Gamma (1 - (a : ℂ) * s) * F s) :
    ∀ s ∈ strip a 3, MellinConvergent w₂ (3 - (a : ℂ) * s) ∧
      F s = (Gamma (3 - (a : ℂ) * s))⁻¹ *
        ∫ u : ℝ in Ioi 0, (u : ℂ) ^ (2 - (a : ℂ) * s) * w₂ u := by
  have hnarrow : EqOn F (continuedMellin a w₂) (strip a 1) := by
    intro s hs
    have hz : 0 < (1 - (a : ℂ) * s).re := by
      have hlt := by simpa [mul_comm] using (lt_div_iff₀ ha).mp hs.2
      simp only [sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, one_re]
      linarith
    have h := normalized_second_mellin w w₁ w₂ (1 - (a : ℂ) * s) (F s)
      (hparts s hs) hz (hinitial s hs)
    simpa only [continuedMellin,
      show (1 : ℂ) - (a : ℂ) * s + 1 + 1 = 3 - (a : ℂ) * s by ring] using h
  let s₀ : ℂ := ((1 / a / 2 : ℝ) : ℂ)
  have hin : s₀ ∈ strip a 1 := by
    change 0 < 1 / a / 2 ∧ 1 / a / 2 < 1 / a
    have hp : 0 < 1 / a := one_div_pos.mpr ha
    constructor <;> linarith
  have hinwide : s₀ ∈ strip a 3 := by
    refine ⟨hin.1, hin.2.trans ?_⟩
    exact (div_lt_div_iff_of_pos_right ha).mpr (by norm_num)
  have heq := (hF.analyticOnNhd (isOpen_strip a 3)).eqOn_of_preconnected_of_eventuallyEq
    (continuedMellin_analyticOnNhd ha w₂ hloc hTop hzero)
    (isPreconnected_strip a 3) hinwide
    (Filter.eventuallyEq_of_mem ((isOpen_strip a 1).mem_nhds hin) hnarrow)
  intro s hs
  refine ⟨continuedMellin_convergent ha w₂ hloc hTop hzero hs, ?_⟩
  simpa only [continuedMellin, mellin, smul_eq_mul,
    show (3 : ℂ) - (a : ℂ) * s - 1 = 2 - (a : ℂ) * s by ring] using heq hs

/-- For the manuscript's range `0 < a < 1`, the curvature parameter is inside
the continued strip, although it need not lie inside the initial strip. -/
theorem three_mem_strip {a : ℝ} (ha : 0 < a) (ha₁ : a < 1) :
    (3 : ℂ) ∈ strip a 3 := by
  refine ⟨by norm_num, (lt_div_iff₀ ha).mpr ?_⟩
  norm_num only [re_ofNat]
  linarith

end Kagey131.PaperD.AnalyticThresholdMellin



