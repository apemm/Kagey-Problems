import PaperD.Modes.TransitionBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Differentiating the smoothing integrand

These lemmas verify the chain terms and the coefficient contributed by the
memory-dependent mixture weight. Joint differentiability of the characteristic
function, and differentiation under its smoothing integral, are separate inputs.
The half-interval identity is exact and does not assume pointwise symmetry.
-/

namespace Kagey131.PaperD.Modes

open Set MeasureTheory
open scoped Interval

/-- The joint derivative with parameter derivative `w` and frequency derivative `u`. -/
noncomputable def smoothingDifferential (w u : ℂ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight w +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight u

/-- The exponent's chain term is `t v^a log v`, including its sign. -/
theorem hasDerivAt_smoothing_argument {a t v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun b : ℝ => t * v ^ b) (t * v ^ a * Real.log v) a := by
  convert! ((hasDerivAt_id a).const_rpow hv).const_mul t using 1
  simp only [id_eq, mul_one]
  ring

/-- Joint differentiation justifies the two contributions along the actual
parameter-dependent frequency, rather than presupposing their sum. -/
theorem hasDerivAt_memory_path {Φ : ℝ × ℝ → ℂ} {a t v : ℝ} {w u : ℂ}
    (hv : 0 < v)
    (hΦ : HasFDerivAt Φ (smoothingDifferential w u) (a, t * v ^ a)) :
    HasDerivAt (fun b : ℝ => Φ (b, t * v ^ b))
      (w + (t * v ^ a * Real.log v) • u) a := by
  have hpath := (hasDerivAt_id a).prodMk (hasDerivAt_smoothing_argument (t := t) hv)
  simpa [smoothingDifferential, Function.comp_def] using hΦ.comp_hasDerivAt a hpath

/-- Frequency variation holds memory fixed, so its derivative contains only
the scaled frequency derivative. -/
theorem hasDerivAt_frequency_path {Φ : ℝ × ℝ → ℂ} {a t c : ℝ} {w u : ℂ}
    (hΦ : HasFDerivAt Φ (smoothingDifferential w u) (a, t*c)) :
    HasDerivAt (fun s : ℝ => Φ (a, s*c)) (c • u) t := by
  have hpath := (hasDerivAt_const t a).prodMk ((hasDerivAt_id t).mul_const c)
  simpa [smoothingDifferential, Function.comp_def] using hΦ.comp_hasDerivAt t hpath

/-- Weighted reflection does not increase a common modulus bound. -/
theorem norm_smoothing_mixture {p f : ℝ} {y z : ℂ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hy : ‖y‖ ≤ f) (hz : ‖z‖ ≤ f) :
    ‖p • y + (1-p) • z‖ ≤ f := by
  have hq : 0 ≤ 1-p := sub_nonneg.mpr hp1
  calc
    ‖p • y + (1-p) • z‖ ≤ ‖p • y‖ + ‖(1-p) • z‖ := norm_add_le _ _
    _ = p * ‖y‖ + (1-p) * ‖z‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hp, abs_of_nonneg hq]
    _ ≤ p*f + (1-p)*f := add_le_add
      (mul_le_mul_of_nonneg_left hy hp) (mul_le_mul_of_nonneg_left hz hq)
    _ = f := by ring

/-- The derivative of the weight contributes one copy of the modulus bound,
not two: its derivative is one half. -/
theorem norm_smoothing_weight_derivative {f : ℝ} {y z : ℂ}
    (hy : ‖y‖ ≤ f) (hz : ‖z‖ ≤ f) :
    ‖(1/2 : ℝ) • (y-z)‖ ≤ f := by
  calc
    ‖(1/2 : ℝ) • (y-z)‖ = (1/2 : ℝ) * ‖y-z‖ := by rw [norm_smul]; norm_num
    _ ≤ (1/2 : ℝ) * (‖y‖ + ‖z‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ f := by linarith

/-- The exact product and mixing-weight derivative of one smoothing integrand. -/
theorem hasDerivAt_smoothing_integrand
    {X Y Z : ℝ → ℂ} {a : ℝ} {x' y' z' : ℂ}
    (hX : HasDerivAt X x' a) (hY : HasDerivAt Y y' a) (hZ : HasDerivAt Z z' a) :
    HasDerivAt (fun b : ℝ => X b * (((1+b)/2) • Y b + ((1-b)/2) • Z b))
      (x' * (((1+a)/2) • Y a + ((1-a)/2) • Z a) +
        X a * ((1/2 : ℝ) • (Y a-Z a) + ((1+a)/2) • y' + ((1-a)/2) • z')) a := by
  have hp : HasDerivAt (fun b : ℝ => (1+b)/2) (1/2) a := by
    simpa using ((hasDerivAt_id a).const_add 1).div_const 2
  have hq : HasDerivAt (fun b : ℝ => (1-b)/2) (-(1/2)) a := by
    convert! ((hasDerivAt_id a).neg.const_add 1).div_const 2 using 1
    simp [neg_div]
  convert! hX.mul ((hp.smul hY).add (hq.smul hZ)) using 1
  simp only [Pi.add_apply, Pi.smul_apply', Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_neg]
  ring

/-- The actual frequency derivative of a smoothing integrand keeps the
mixture weight constant. -/
theorem hasDerivAt_smoothing_frequency_integrand
    {X Y Z : ℝ → ℂ} {t p : ℝ} {x' y' z' : ℂ}
    (hX : HasDerivAt X x' t) (hY : HasDerivAt Y y' t) (hZ : HasDerivAt Z z' t) :
    HasDerivAt (fun s : ℝ => X s * (p • Y s + (1-p) • Z s))
      (x' * (p • Y t + (1-p) • Z t) + X t * (p • y' + (1-p) • z')) t := by
  convert! hX.mul ((hY.const_smul p).add (hZ.const_smul (1-p))) using 1

/-- Pointwise bound for the full memory derivative. The hypotheses bound the
intrinsic memory derivatives (`wx`, `wy`) and the actual chain contributions
(`cx`, `cy`). The mixing derivative contributes exactly `fx*fy`. -/
theorem norm_smoothing_memory_derivative
    {p fx fy wx wy cx cy : ℝ} {x y z dx dy dz : ℂ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hfx : ‖x‖ ≤ fx) (hy : ‖y‖ ≤ fy) (hz : ‖z‖ ≤ fy)
    (hdx : ‖dx‖ ≤ wx+cx) (hdy : ‖dy‖ ≤ wy+cy) (hdz : ‖dz‖ ≤ wy+cy) :
    ‖dx * (p • y + (1-p) • z) +
        x * ((1/2 : ℝ) • (y-z) + p • dy + (1-p) • dz)‖ ≤
      wx*fy + fx*wy + cx*fy + fx*cy + fx*fy := by
  have hfx0 : 0 ≤ fx := (norm_nonneg x).trans hfx
  have hm := norm_smoothing_mixture hp hp1 hy hz
  have hdm := norm_smoothing_mixture hp hp1 hdy hdz
  have hw := norm_smoothing_weight_derivative hy hz
  have hsum : ‖(1/2 : ℝ) • (y-z) + p • dy + (1-p) • dz‖ ≤ fy+(wy+cy) := by
    calc
      _ = ‖(1/2 : ℝ) • (y-z) + (p • dy + (1-p) • dz)‖ := by rw [add_assoc]
      _ ≤ ‖(1/2 : ℝ) • (y-z)‖ + ‖p • dy + (1-p) • dz‖ := norm_add_le _ _
      _ ≤ fy+(wy+cy) := add_le_add hw hdm
  calc
    _ ≤ ‖dx * (p • y + (1-p) • z)‖ +
        ‖x * ((1/2 : ℝ) • (y-z) + p • dy + (1-p) • dz)‖ := norm_add_le _ _
    _ = ‖dx‖ * ‖p • y + (1-p) • z‖ +
        ‖x‖ * ‖(1/2 : ℝ) • (y-z) + p • dy + (1-p) • dz‖ := by rw [norm_mul, norm_mul]
    _ ≤ (wx+cx)*fy + fx*(fy+(wy+cy)) := add_le_add
      (mul_le_mul hdx hm (norm_nonneg _) ((norm_nonneg _).trans hdx))
      (mul_le_mul hfx hsum (norm_nonneg _) hfx0)
    _ = _ := by ring

/-- The ordinary triangle inequality exposes the actual chain contribution.
It can be used for either sign of the frequency path. -/
theorem norm_smoothing_chain {w u : ℂ} {x ℓ : ℝ} :
    ‖w + (x*ℓ) • u‖ ≤ ‖w‖ + |x| * |ℓ| * ‖u‖ := by
  calc
    _ ≤ ‖w‖ + ‖(x*ℓ) • u‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_mul]

/-- Frequency differentiation has no derivative of the mixing weight. -/
theorem norm_smoothing_frequency_derivative
    {p fx fy ux uy : ℝ} {x y z dx dy dz : ℂ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hfx : ‖x‖ ≤ fx) (hy : ‖y‖ ≤ fy) (hz : ‖z‖ ≤ fy)
    (hdx : ‖dx‖ ≤ ux) (hdy : ‖dy‖ ≤ uy) (hdz : ‖dz‖ ≤ uy) :
    ‖dx * (p • y + (1-p) • z) + x * (p • dy + (1-p) • dz)‖ ≤
      ux*fy + fx*uy := by
  have hm := norm_smoothing_mixture hp hp1 hy hz
  have hdm := norm_smoothing_mixture hp hp1 hdy hdz
  calc
    _ ≤ ‖dx * (p • y + (1-p) • z)‖ + ‖x * (p • dy + (1-p) • dz)‖ := norm_add_le _ _
    _ = ‖dx‖ * ‖p • y + (1-p) • z‖ + ‖x‖ * ‖p • dy + (1-p) • dz‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ux*fy + fx*uy := add_le_add
      (mul_le_mul hdx hm (norm_nonneg _) ((norm_nonneg _).trans hdx))
      (mul_le_mul hfx hdm (norm_nonneg _) ((norm_nonneg _).trans hfx))

/-- Splitting and reflecting the second half accounts for every factor two
in the derivative-tail estimates. Integrability, not symmetry, is required. -/
theorem smoothing_half_interval {h : ℝ → ℝ}
    (hl : IntervalIntegrable h volume 0 (1/2))
    (hr : IntervalIntegrable h volume (1/2) 1) :
    (∫ v in (0:ℝ)..1, h v) = ∫ v in (0:ℝ)..(1/2), h v + h (1-v) := by
  have href : IntervalIntegrable (fun v => h (1-v)) volume 0 (1/2) := by
    convert! (hr.comp_sub_left 1).symm using 1 <;> norm_num
  rw [intervalIntegral.integral_add hl href, intervalIntegral.integral_comp_sub_left]
  norm_num
  exact (intervalIntegral.integral_add_adjacent_intervals hl hr).symm

/-- A symmetric envelope contributes twice its half-interval integral. -/
theorem smoothing_half_interval_symmetric {h : ℝ → ℝ}
    (hl : IntervalIntegrable h volume 0 (1/2))
    (hr : IntervalIntegrable h volume (1/2) 1)
    (hsym : ∀ v ∈ Icc (0:ℝ) (1/2), h (1-v) = h v) :
    (∫ v in (0:ℝ)..1, h v) = 2 * ∫ v in (0:ℝ)..(1/2), h v := by
  rw [smoothing_half_interval hl hr]
  have heq : (∫ v in (0:ℝ)..(1/2), h v + h (1-v)) =
      ∫ v in (0:ℝ)..(1/2), h v + h v := by
    apply intervalIntegral.integral_congr
    intro v hv
    change h v + h (1-v) = h v + h v
    rw [hsym v (by simpa using hv)]
  rw [heq, intervalIntegral.integral_add hl hl]
  ring

end Kagey131.PaperD.Modes
