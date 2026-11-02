import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Entire extension of a Fourier integral

This file supplies the analytic step in Lemma F.4. The hypotheses concern
the Fourier integrand and its exponential moments, not analyticity of the
conclusion.
-/

namespace Kagey131.PaperD.Modes

open MeasureTheory Filter Set Asymptotics
open scoped Topology

theorem weighted_stretched_exp_littleO {c r : ℝ} (hc : 0 < c) (hr : 1 < r) (B : ℝ) :
    (fun x : ℝ => Real.exp (B*x-c*x^r)) =o[atTop]
      (fun x : ℝ => Real.exp (-x)) := by
  rw [Real.isLittleO_exp_comp_exp_comp]
  suffices Tendsto (fun x : ℝ => x * (c * x ^ (r-1) - (B+1))) atTop atTop by
    refine Tendsto.congr' ?_ this
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_sub_one hx.ne']
    field_simp
    ring
  apply tendsto_id.atTop_mul_atTop₀
  have ht : Tendsto (fun x : ℝ => c*x^(r-1)) atTop atTop :=
    Tendsto.const_mul_atTop hc (tendsto_rpow_atTop (by linarith))
  simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(B+1)) ht

/-- Exponential tilting of a super-exponentially decaying envelope is integrable. -/
theorem integrable_weighted_stretched_exp {c r : ℝ} (hc : 0 < c) (hr : 1 < r) (B : ℝ) :
    Integrable (fun x : ℝ => Real.exp (B*|x|-c*|x|^r)) := by
  have hcont : Continuous (fun x : ℝ => Real.exp (B*|x|-c*|x|^r)) := by
    exact Real.continuous_exp.comp ((continuous_const.mul continuous_abs).sub
      (continuous_const.mul ((Real.continuous_rpow_const (by linarith)).comp continuous_abs)))
  apply hcont.locallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    (g := fun x : ℝ => Real.exp (-x))
  · exact Filter.Eventually.of_forall (by intro x; simp)
  · apply (weighted_stretched_exp_littleO hc hr B).isBigO.congr'
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      simp [abs_of_nonneg hx]
    · exact Filter.Eventually.of_forall (fun _ => rfl)
  · exact ⟨Ioi 0, Ioi_mem_atTop 0, integrableOn_exp_neg_Ioi 0⟩

theorem exponential_moments_of_stretched_bound {φ : ℝ → ℂ}
    (hφ : Continuous φ) {c r : ℝ} (hc : 0 < c) (hr : 1 < r)
    (hbound : ∀ t, ‖φ t‖ ≤ 2 * Real.exp (-c*|t|^r)) (B : ℝ) :
    Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖) := by
  refine ((integrable_weighted_stretched_exp hc hr B).const_mul 2).mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul hφ.norm).aestronglyMeasurable ?_
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
  calc
    Real.exp (B*|t|) * ‖φ t‖ ≤ Real.exp (B*|t|) * (2 * Real.exp (-c*|t|^r)) := by
      gcongr
      exact hbound t
    _ = 2 * Real.exp (B*|t|-c*|t|^r) := by
      rw [show B*|t|-c*|t|^r = B*|t| + -c*|t|^r by ring, Real.exp_add]
      ring

noncomputable def entireFourierKernel (φ : ℝ → ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((-Complex.I * (t : ℂ))*z) * φ t

noncomputable def entireFourier (φ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, entireFourierKernel φ z t

theorem continuous_entireFourierKernel {φ : ℝ → ℂ} (hφ : Continuous φ) (z : ℂ) :
    Continuous (entireFourierKernel φ z) := by
  exact (Complex.continuous_exp.comp
    ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).mul hφ

theorem norm_entireFourierKernel_le {φ : ℝ → ℂ} {z : ℂ} {B : ℝ} (hz : ‖z‖ ≤ B) (t : ℝ) :
    ‖entireFourierKernel φ z t‖ ≤ Real.exp (B*|t|) * ‖φ t‖ := by
  unfold entireFourierKernel
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖Complex.exp ((-Complex.I*(t:ℂ))*z)‖ ≤ Real.exp ‖(-Complex.I*(t:ℂ))*z‖ :=
      Complex.norm_exp_le_exp_norm _
    _ = Real.exp (|t| *‖z‖) := by simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ Real.exp (B*|t|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hz (abs_nonneg t)]

theorem integrable_entireFourierKernel {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖)) (z : ℂ) :
    Integrable (entireFourierKernel φ z) := by
  exact (hw ‖z‖).mono' (continuous_entireFourierKernel hφ z).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_entireFourierKernel_le le_rfl))

/-- The Fourier integral is entire when every exponential weight is integrable.
This is proved by differentiation under the integral, not assumed as a Fourier theorem. -/
theorem hasDerivAt_entireFourier {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖)) (z₀ : ℂ) :
    HasDerivAt (entireFourier φ)
      (∫ t : ℝ, (-Complex.I*(t:ℂ)) * entireFourierKernel φ z₀ t) z₀ := by
  let F' : ℂ → ℝ → ℂ := fun z t =>
    (-Complex.I * (t:ℂ)) * entireFourierKernel φ z t
  have hF' : ∀ z, Continuous (F' z) := by
    intro z
    exact (continuous_const.mul Complex.continuous_ofReal).mul
      (continuous_entireFourierKernel hφ z)
  have hdiff : ∀ t z, HasDerivAt (fun z => entireFourierKernel φ z t) (F' z t) z := by
    intro t z
    simpa [F', entireFourierKernel, mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id z).const_mul (-Complex.I*(t:ℂ))).cexp).mul_const (φ t)
  have hdom : ∀ t : ℝ, ∀ z ∈ Metric.ball z₀ 1,
      ‖F' z t‖ ≤ Real.exp ((‖z₀‖+2)*|t|) * ‖φ t‖ := by
    intro t z hz
    have hzle : ‖z‖ ≤ ‖z₀‖+1 := by
      have hnorm := norm_le_norm_add_norm_sub z₀ z
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [norm_sub_rev z₀ z] at hnorm
      linarith
    have ht : |t| ≤ Real.exp |t| := (Real.add_one_le_exp |t|).trans' (by linarith)
    calc
      ‖F' z t‖ = |t| * ‖entireFourierKernel φ z t‖ := by
        simp [F', norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ Real.exp |t| * (Real.exp ((‖z₀‖+1)*|t|) * ‖φ t‖) := by
        exact mul_le_mul ht (norm_entireFourierKernel_le hzle t)
          (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((‖z₀‖+2)*|t|) * ‖φ t‖ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := entireFourierKernel φ) (F' := F') (x₀ := z₀)
    (bound := fun t : ℝ => Real.exp ((‖z₀‖+2)*|t|) * ‖φ t‖)
    (Metric.ball_mem_nhds z₀ (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun z => (continuous_entireFourierKernel hφ z).aestronglyMeasurable)
    (integrable_entireFourierKernel hφ hw z₀)
    (hF' z₀).aestronglyMeasurable (Filter.Eventually.of_forall hdom) (hw (‖z₀‖+2))
    (Filter.Eventually.of_forall fun t z _ => hdiff t z)
  exact h.2

theorem differentiable_entireFourier {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖)) :
    Differentiable ℂ (entireFourier φ) :=
  fun z => (hasDerivAt_entireFourier hφ hw z).differentiableAt

theorem analytic_entireFourier {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖)) :
    AnalyticOnNhd ℂ (entireFourier φ) univ :=
  (differentiable_entireFourier hφ hw).differentiableOn.analyticOnNhd isOpen_univ

/-- Any real density represented by this Fourier integral is real analytic. -/
theorem analytic_density_of_fourier_representation {g : ℝ → ℝ} {φ : ℝ → ℂ}
    (hφ : Continuous φ)
    (hw : ∀ B : ℝ, Integrable (fun t : ℝ => Real.exp (B*|t|) * ‖φ t‖))
    (hrep : ∀ x, g x = (entireFourier φ (x:ℂ)).re / (2*Real.pi)) :
    AnalyticOnNhd ℝ g univ := by
  intro x _
  have h := ((analytic_entireFourier hφ hw) (x:ℂ) (mem_univ _)).re_ofReal
  have hg : g = fun x : ℝ => (entireFourier φ (x:ℂ)).re / (2*Real.pi) := funext hrep
  rw [hg]
  exact h.div_const

/-- The identity theorem excludes a constant interval for any nonconstant real
analytic function; this applies to derivatives as well as densities. -/
theorem analytic_nonconstant_no_flat {g : ℝ → ℝ} (ha : AnalyticOnNhd ℝ g univ)
    (hne : ∃ u v, g u ≠ g v) :
    ∀ a b, a < b → ¬ EqOn g (fun _ => g a) (Icc a b) := by
  intro a b hab heq
  let z := (a+b)/2
  have hz : z ∈ Ioo a b := by constructor <;> dsimp [z] <;> linarith
  have hev : g =ᶠ[𝓝 z] (fun _ => g a) :=
    Filter.mem_of_superset (Ioo_mem_nhds hz.1 hz.2) (fun x hx => heq (Ioo_subset_Icc_self hx))
  have hall : g = fun _ => g a := ha.eq_of_eventuallyEq analyticOnNhd_const hev
  obtain ⟨u, v, huv⟩ := hne
  exact huv (by rw [hall])

/-- An integrable, nonzero analytic function cannot be constant on a nontrivial interval. -/
theorem analytic_integrable_no_flat {g : ℝ → ℝ} (ha : AnalyticOnNhd ℝ g univ)
    (hi : Integrable g) (hne : ∃ x, g x ≠ 0) :
    ∀ a b, a < b → ¬ EqOn g (fun _ => g a) (Icc a b) := by
  intro a b hab heq
  let z := (a+b)/2
  have hz : z ∈ Ioo a b := by constructor <;> dsimp [z] <;> linarith
  have hev : g =ᶠ[𝓝 z] (fun _ => g a) :=
    Filter.mem_of_superset (Ioo_mem_nhds hz.1 hz.2) (fun x hx => heq (Ioo_subset_Icc_self hx))
  have hall : g = fun _ => g a := ha.eq_of_eventuallyEq analyticOnNhd_const hev
  have hconst : Integrable (fun _ : ℝ => g a) := hall ▸ hi
  have hzval : g a = 0 := (integrable_const_iff.mp hconst).resolve_right (by
    rw [not_isFiniteMeasure_iff]
    simp)
  obtain ⟨x, hx⟩ := hne
  exact hx (by rw [hall, hzval])

end Kagey131.PaperD.Modes
