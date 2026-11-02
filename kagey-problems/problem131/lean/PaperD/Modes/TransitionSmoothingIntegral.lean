import PaperD.Modes.TransitionSmoothing

/-!
# Dominated differentiation of the memory smoothing integral

The derivative envelope is derived from the three component paths and the
memory-dependent mixture. Joint differentiation of the characteristic function
can supply these paths through `hasDerivAt_memory_path`. An integrable local
envelope remains an explicit analytic hypothesis.
-/

namespace Kagey131.PaperD.Modes

open Set MeasureTheory Filter
open scoped Topology

noncomputable def smoothingPathIntegrand (X Y Z : ℝ → ℝ → ℂ) (a v : ℝ) : ℂ :=
  X a v * (((1+a)/2) • Y a v + ((1-a)/2) • Z a v)

noncomputable def smoothingPathDerivative
    (X Y Z dX dY dZ : ℝ → ℝ → ℂ) (a v : ℝ) : ℂ :=
  dX a v * (((1+a)/2) • Y a v + ((1-a)/2) • Z a v) +
    X a v * ((1/2 : ℝ) • (Y a v-Z a v) + ((1+a)/2) • dY a v +
      ((1-a)/2) • dZ a v)

noncomputable def smoothingPathEnvelope
    (fx fy wx wy cx cy : ℝ → ℝ) (v : ℝ) : ℝ :=
  wx v * fy v + fx v * wy v + cx v * fy v + fx v * cy v + fx v * fy v

/-- Actual component derivatives and component bounds imply both a derivative
of the integral and the complete memory envelope. The full smoothing derivative
bound is a conclusion, including the term from the derivative of `p`. -/
theorem hasDerivAt_smoothing_integral
    {μ : Measure ℝ} {X Y Z dX dY dZ : ℝ → ℝ → ℂ}
    {fx fy wx wy cx cy : ℝ → ℝ} {a₀ : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 a₀) (hsa : s ⊆ Icc (-1:ℝ) 1)
    (hX : ∀ v a, a ∈ s → HasDerivAt (fun b => X b v) (dX a v) a)
    (hY : ∀ v a, a ∈ s → HasDerivAt (fun b => Y b v) (dY a v) a)
    (hZ : ∀ v a, a ∈ s → HasDerivAt (fun b => Z b v) (dZ a v) a)
    (hF : ∀ a, AEStronglyMeasurable (smoothingPathIntegrand X Y Z a) μ)
    (hFint : Integrable (smoothingPathIntegrand X Y Z a₀) μ)
    (hD : AEStronglyMeasurable (smoothingPathDerivative X Y Z dX dY dZ a₀) μ)
    (hB : Integrable (smoothingPathEnvelope fx fy wx wy cx cy) μ)
    (hfx : ∀ v a, a ∈ s → ‖X a v‖ ≤ fx v)
    (hy : ∀ v a, a ∈ s → ‖Y a v‖ ≤ fy v)
    (hz : ∀ v a, a ∈ s → ‖Z a v‖ ≤ fy v)
    (hdx : ∀ v a, a ∈ s → ‖dX a v‖ ≤ wx v+cx v)
    (hdy : ∀ v a, a ∈ s → ‖dY a v‖ ≤ wy v+cy v)
    (hdz : ∀ v a, a ∈ s → ‖dZ a v‖ ≤ wy v+cy v) :
    HasDerivAt (fun a => ∫ v, smoothingPathIntegrand X Y Z a v ∂μ)
      (∫ v, smoothingPathDerivative X Y Z dX dY dZ a₀ v ∂μ) a₀ ∧
    ‖∫ v, smoothingPathDerivative X Y Z dX dY dZ a₀ v ∂μ‖ ≤
      ∫ v, smoothingPathEnvelope fx fy wx wy cx cy v ∂μ := by
  have hbound : ∀ v a, a ∈ s →
      ‖smoothingPathDerivative X Y Z dX dY dZ a v‖ ≤
        smoothingPathEnvelope fx fy wx wy cx cy v := by
    intro v a ha
    have hap := hsa ha
    have hp : 0 ≤ (1+a)/2 := by linarith [hap.1]
    have hp1 : (1+a)/2 ≤ 1 := by linarith [hap.2]
    have hq : (1-a)/2 = 1-(1+a)/2 := by ring
    simpa only [smoothingPathDerivative, smoothingPathEnvelope, hq] using
      norm_smoothing_memory_derivative hp hp1 (hfx v a ha) (hy v a ha)
        (hz v a ha) (hdx v a ha) (hdy v a ha) (hdz v a ha)
  have hdiff : ∀ v a, a ∈ s →
      HasDerivAt (fun b => smoothingPathIntegrand X Y Z b v)
        (smoothingPathDerivative X Y Z dX dY dZ a v) a := by
    intro v a ha
    exact hasDerivAt_smoothing_integrand (hX v a ha) (hY v a ha) (hZ v a ha)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := smoothingPathIntegrand X Y Z)
    (F' := smoothingPathDerivative X Y Z dX dY dZ)
    (bound := smoothingPathEnvelope fx fy wx wy cx cy) hs
    (Eventually.of_forall hF) hFint hD (Eventually.of_forall hbound) hB
    (Eventually.of_forall hdiff)
  refine ⟨hderiv.2, ?_⟩
  exact MeasureTheory.norm_integral_le_of_norm_le hB
    (Eventually.of_forall fun v => hbound v a₀ (mem_of_mem_nhds hs))

end Kagey131.PaperD.Modes
