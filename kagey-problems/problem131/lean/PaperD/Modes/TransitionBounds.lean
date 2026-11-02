import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Bounds used in the central-curvature parameter certificate

The inhomogeneous bootstrap is a compact-maximum argument. It does not assume
decay of the derivative it is used to bound. The Fourier differentiation
theorem takes an integrable bound on the actual parameter derivative, not a
derivative of a previous approximation error. Numerical enclosures from Arb
remain explicit inputs; this file does not certify Arb's gamma evaluations.
-/

namespace Kagey131.PaperD.Modes

open Set MeasureTheory Filter
open scoped Topology

/-- A continuous, nonnegative quantity satisfying an inhomogeneous contraction
cannot cross a strict constant barrier. Applied to `t^β |∂t φ(t)|` and then to
`t^γ |∂a φ(t)|`, this proves the derivative-tail bootstraps. -/
theorem inhomogeneous_bootstrap
    {h : ℝ → ℝ} {l m A κ D : ℝ}
    (hc : ContinuousOn h (Ici l)) (hnonneg : ∀ t ∈ Ici l, 0 ≤ h t)
    (hinit : ∀ t ∈ Icc l m, h t < D) (hκ1 : κ < 1)
    (hslack : A + κ*D < D)
    (hstep : ∀ t ≥ m, ∀ B ≥ 0,
      (∀ s ∈ Icc l t, h s ≤ B) → h t ≤ A + κ*B) :
    ∀ t ∈ Ici l, h t < D := by
  intro t ht
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr ht) (hc.mono (by intro y hy; exact hy.1))
  have htx : h t ≤ h x := hmax ⟨ht, le_rfl⟩
  by_cases hxm : x ≤ m
  · exact htx.trans_lt (hinit x ⟨hx.1, hxm⟩)
  · have hmax' : ∀ s ∈ Icc l x, h s ≤ h x := by
      intro s hs
      exact hmax ⟨hs.1, hs.2.trans hx.2⟩
    have hineq := hstep x (le_of_not_ge hxm) (h x) (hnonneg x hx.1) hmax'
    have hxd : h x < D := by
      by_contra hnot
      have hge : D ≤ h x := le_of_not_gt hnot
      have hprod : 0 ≤ (1-κ)*(h x-D) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    exact htx.trans_lt hxd

/-- The rational constants used by the fresh certificate leave strict slack
for the frequency-derivative propagation. -/
theorem transition_frequency_slack {A R : ℝ}
    (hA : A < 1) (hR : R ≤ 83/1000) : A + R*2 < 2 := by
  linarith

/-- The rational constants used by the fresh certificate leave strict slack
for the memory-derivative propagation. -/
theorem transition_parameter_slack {A κ : ℝ}
    (hA : A < 2) (hκ : κ < 1/10) : A + κ*4 < 4 := by
  linarith

/-- Central curvature represented by the real part of the conditional Fourier
transform. The integral is over the full real line. -/
noncomputable def centralCurvatureFourier (φ : ℝ → ℝ → ℝ) (a : ℝ) : ℝ :=
  -(∫ t : ℝ, t^2 * φ a t) / (2*Real.pi)

/-- Dominated differentiation of the actual Fourier integral in memory.
The envelope controls `ψ = ∂a φ` uniformly on a neighbourhood of `a₀`. -/
theorem hasDerivAt_centralCurvatureFourier
    {φ ψ : ℝ → ℝ → ℝ} {a₀ : ℝ} {s : Set ℝ} {W : ℝ → ℝ}
    (hs : s ∈ 𝓝 a₀)
    (hφ : ∀ a, Continuous (φ a)) (hψ : Continuous (ψ a₀))
    (hint : Integrable (fun t : ℝ => t^2 * φ a₀ t))
    (hdom : ∀ t, ∀ a ∈ s, |ψ a t| ≤ W t)
    (hW : Integrable (fun t : ℝ => t^2 * W t))
    (hdiff : ∀ t, ∀ a ∈ s, HasDerivAt (fun b => φ b t) (ψ a t) a) :
    HasDerivAt (centralCurvatureFourier φ)
      (-(∫ t : ℝ, t^2 * ψ a₀ t) / (2*Real.pi)) a₀ := by
  have hcont : ∀ a, Continuous (fun t : ℝ => t^2 * φ a t) := by
    intro a
    exact (continuous_id.pow 2).mul (hφ a)
  have hcont' : Continuous (fun t : ℝ => t^2 * ψ a₀ t) :=
    (continuous_id.pow 2).mul hψ
  have hb : ∀ t, ∀ a ∈ s, ‖t^2 * ψ a t‖ ≤ t^2 * W t := by
    intro t a ha
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t)]
    exact mul_le_mul_of_nonneg_left (hdom t a ha) (sq_nonneg t)
  have hd : ∀ t, ∀ a ∈ s,
      HasDerivAt (fun b => t^2 * φ b t) (t^2 * ψ a t) a := by
    intro t a ha
    exact (hdiff t a ha).const_mul (t^2)
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun a t : ℝ => t^2 * φ a t) (F' := fun a t : ℝ => t^2 * ψ a t)
    (bound := fun t : ℝ => t^2 * W t) hs
    (Eventually.of_forall fun a => (hcont a).aestronglyMeasurable) hint
    hcont'.aestronglyMeasurable (Eventually.of_forall hb) hW
    (Eventually.of_forall hd)
  exact hi.2.neg.div_const (2*Real.pi)

/-- Quantitative strict positivity survives the complete numerical remainder. -/
theorem positive_curvature_derivative_of_enclosure {d center error : ℝ}
    (herror : |d-center| ≤ error) (hlower : 68/100 + error < center) :
    0 < d := by
  have h := (abs_le.mp herror).1
  linarith

/-- Assemble dominated differentiation with a finite-frequency enclosure and
its complete remainder. The positive derivative is a conclusion, not a
numerical premise about `deriv` itself. -/
theorem centralCurvature_deriv_pos_of_certificate
    {φ ψ : ℝ → ℝ → ℝ} {a₀ : ℝ} {s : Set ℝ} {W : ℝ → ℝ}
    (hs : s ∈ 𝓝 a₀)
    (hφ : ∀ a, Continuous (φ a)) (hψ : Continuous (ψ a₀))
    (hint : Integrable (fun t : ℝ => t^2 * φ a₀ t))
    (hdom : ∀ t, ∀ a ∈ s, |ψ a t| ≤ W t)
    (hW : Integrable (fun t : ℝ => t^2 * W t))
    (hdiff : ∀ t, ∀ a ∈ s, HasDerivAt (fun b => φ b t) (ψ a t) a)
    {center error : ℝ}
    (hcertificate : |(-(∫ t : ℝ, t^2 * ψ a₀ t) / (2*Real.pi))-center| ≤ error)
    (hlower : 68/100 + error < center) :
    0 < deriv (centralCurvatureFourier φ) a₀ := by
  rw [(hasDerivAt_centralCurvatureFourier hs hφ hψ hint hdom hW hdiff).deriv]
  exact positive_curvature_derivative_of_enclosure hcertificate hlower

/-- Tail of the certified parameter derivative after multiplication by `t²`:
the constant `4`, exponent `7`, and cutoff `10` give `1/(10000 π)`. -/
theorem transition_tail_value :
    (4 : ℝ) * (10 : ℝ)^(-4 : ℤ) / (4*Real.pi) = 1/(10000*Real.pi) := by
  norm_num
  ring

theorem transition_tail_small : 1/(10000*Real.pi) < (1 : ℝ)/30000 := by
  have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

end Kagey131.PaperD.Modes
