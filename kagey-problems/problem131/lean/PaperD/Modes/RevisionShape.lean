import PaperD.Modes.AnalyticCharacteristic
import PaperD.Modes.CurvatureShapeInflections
import PaperD.Modes.CurvatureTransfer
import PaperD.Modes.LocalModes
import PaperD.Modes.StrictShape
import PaperD.Modes.FourthMoment

/-!
# The strengthened limit-shape theorem

This file joins the analytic-density proof, the finite-walk sign bound, the
strict mode classification, and the curvature partition. The final interface
keeps the conditional-first-step characteristic function separate from the
fair-start density. Its smoothing inequality is an input from the published
distributional fixed-point theorem, not an assumption about shape.
-/

namespace Kagey131.PaperD.Modes

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

def StrictUnimodalShape (g : ℝ → ℝ) : Prop :=
  StrictMonoOn g (Iic 0) ∧ StrictAntiOn g (Ici 0) ∧
  (∀ x, IsLocalMax g x ↔ x = 0) ∧
  ∃ d > 0, StrictConcaveOn ℝ (Ioo (-d) d) g ∧
    StrictConvexOn ℝ (Iio (-d)) g ∧ StrictConvexOn ℝ (Ioi d) g

def StrictBimodalShape (g : ℝ → ℝ) : Prop :=
  ∃ c > 0, StrictMonoOn g (Icc 0 c) ∧ StrictAntiOn g (Ici c) ∧
    StrictMonoOn g (Iic (-c)) ∧ StrictAntiOn g (Icc (-c) 0) ∧
    (∀ x, IsLocalMax g x ↔ x = c ∨ x = -c) ∧
    ∃ d₁ d₂ : ℝ, 0 < d₁ ∧ d₁ < c ∧ c < d₂ ∧
      StrictConvexOn ℝ (Ioo (-d₁) d₁) g ∧
      StrictConcaveOn ℝ (Ioo (-d₂) (-d₁)) g ∧ StrictConcaveOn ℝ (Ioo d₁ d₂) g ∧
      StrictConvexOn ℝ (Iio (-d₂)) g ∧ StrictConvexOn ℝ (Ioi d₂) g

theorem StrictUnimodalShape.inflections {g : ℝ → ℝ} (h : StrictUnimodalShape g) :
    ∃ d > 0, ∀ x, IsStrictInflection g x ↔ x = -d ∨ x = d := by
  obtain ⟨d, hd, hm, hl, hr⟩ := h.2.2.2
  exact ⟨d, hd, strictInflection_unimodal_iff hd hm hl hr⟩

theorem StrictBimodalShape.inflections {g : ℝ → ℝ} (h : StrictBimodalShape g) :
    ∃ d₁ d₂ : ℝ, 0 < d₁ ∧ d₁ < d₂ ∧
      ∀ x, IsStrictInflection g x ↔ x = -d₂ ∨ x = -d₁ ∨ x = d₁ ∨ x = d₂ := by
  obtain ⟨c, hc, hm, ha, hml, hal, hlocal, d₁, d₂, hd₁, hd₁c, hcd₂,
    hcenter, hleft, hright, htailL, htailR⟩ := h
  exact ⟨d₁, d₂, hd₁, hd₁c.trans hcd₂,
    strictInflection_bimodal_iff hd₁ (hd₁c.trans hcd₂) hcenter hleft hright htailL htailR⟩

/-- Join the independently proved analytic regularity and sign-transfer arguments. -/
theorem strict_shape_of_regularity {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1/4)
    {g : ℝ → ℝ} (hg : DensityHyp g) (hlaw : LawConvHyp ε (1-2*ε) g)
    (hr : AnalyticDensityRegularity g) : StrictUnimodalShape g ∨ StrictBimodalShape g := by
  have hd : Differentiable ℝ g := fun x => (hr.analytic x (mem_univ _)).differentiableAt
  have hdd : Differentiable ℝ (deriv g) :=
    fun x => (hr.analytic.deriv x (mem_univ _)).differentiableAt
  have hfive := second_derivative_valuesAtMost hε0 hε hg hlaw
    hr.derivContinuous hr.secondContinuous hd hdd hr.derivBounded hr.secondBounded
  rcases two_modes_strict hε0 hε hg hlaw hr.noFlat with hu | ⟨c, hc, hm, ha, hml, hal, _⟩
  · exact Or.inl ⟨hu.1, hu.2, local_mode_zero_iff hu.1 hu.2,
      curvature_unimodal hd hdd hr.secondContinuous hg.even hr.derivTop hr.noFlatDeriv hfive hu.2⟩
  · exact Or.inr ⟨c, hc, hm, ha, hml, hal, local_modes_pair_iff hg.even hc hm ha hml hal,
      curvature_bimodal hd hdd hr.secondContinuous hg.even hr.derivTop hr.noFlatDeriv hfive hc hm ha⟩

/-- Explicit published-law inputs. The function `φ` belongs to the conditional
law; only its real part represents the fair-start density `g`. -/
structure ConditionalFourierHyp (a : ℝ) (g : ℝ → ℝ) (φ : ℝ → ℂ) : Prop where
  continuous : Continuous φ
  unit_bound : ∀ t, ‖φ t‖ ≤ 1
  norm_even : ∀ t, ‖φ (-t)‖ = ‖φ t‖
  decay : Tendsto (fun t => ‖φ t‖) atTop (𝓝 0)
  smoothing : ∀ t, 0 ≤ t → ‖φ t‖ ≤ ∫ v in Ioo (0 : ℝ) 1,
    ‖φ (t*v^a)‖ * ‖φ (t*(1-v)^a)‖
  fair_representation : g = normalizedFourierDensity (fun t => ((φ t).re : ℂ))

/-- Standard characteristic-function facts need not be supplied separately
when the conditional law is given as a probability measure with density. -/
theorem conditionalFourierHyp_of_probability_measure {a : ℝ} {g : ℝ → ℝ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {ρ : ℝ → ℝ≥0}
    (hρ : Measurable ρ) (hμ : μ = volume.withDensity (fun x => (ρ x : ℝ≥0∞)))
    (hfp : ∀ t, 0 ≤ t → ‖charFun μ t‖ ≤ ∫ v in Ioo (0 : ℝ) 1,
      ‖charFun μ (t*v^a)‖ * ‖charFun μ (t*(1-v)^a)‖)
    (hrep : g = normalizedFourierDensity (fun t => ((charFun μ t).re : ℂ))) :
    ConditionalFourierHyp a g (charFun μ) := by
  refine ⟨continuous_charFun, (fun t => norm_charFun_le_one t), ?_,
    charFun_norm_tendsto_zero_of_density hρ hμ, hfp, hrep⟩
  intro t
  simp only [charFun_neg, RCLike.norm_conj]

theorem regularity_of_conditional_fourier {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1/4)
    {g : ℝ → ℝ} {φ : ℝ → ℂ} (hg : DensityHyp g)
    (hlaw : LawConvHyp ε (1-2*ε) g) (hφ : ConditionalFourierHyp (1-2*ε) g φ) :
    AnalyticDensityRegularity g := by
  have hne : ∃ x, g x ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hzero : g = fun _ => 0 := funext hn
    have hm := density_integral_one_of_lawConv hlaw
    rw [hzero, integral_zero] at hm
    norm_num at hm
  exact fair_analytic_density_of_smoothing (by linarith) (by linarith)
    hφ.continuous hφ.unit_bound hφ.norm_even hφ.decay hφ.smoothing
    hφ.fair_representation hg.integrable hne

/-- The complete new shape assertion from the explicit fixed-point/Fourier
inputs. No analyticity, no-flatness, or curvature premise is left in this statement. -/
theorem strict_shape_of_conditional_fourier {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1/4)
    {g : ℝ → ℝ} {φ : ℝ → ℂ} (hg : DensityHyp g)
    (hlaw : LawConvHyp ε (1-2*ε) g) (hφ : ConditionalFourierHyp (1-2*ε) g φ) :
    StrictUnimodalShape g ∨ StrictBimodalShape g :=
  strict_shape_of_regularity hε0 hε hg hlaw
    (regularity_of_conditional_fourier hε0 hε hg hlaw hφ)

/-- At memory at least `4/5` the strict bimodal branch holds, including all
four curvature transitions. Khinchine's representation is not an input. -/
theorem strict_bimodal_four_fifths {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1/10)
    {g : ℝ → ℝ} {φ : ℝ → ℂ} (hg : DensityHyp g)
    (hlaw : LawConvHyp ε (1-2*ε) g) (hφ : ConditionalFourierHyp (1-2*ε) g φ)
    (hmom : GLRFourthMomentsHyp g (1-2*ε)) : StrictBimodalShape g := by
  rcases strict_shape_of_conditional_fourier hε0 (by linarith) hg hlaw hφ with hu | hb
  · exact False.elim (fourth_moments_not_antitone (by linarith) hg
      (density_integral_one_of_lawConv hlaw) hmom hu.2.1.antitoneOn)
  · exact hb

end Kagey131.PaperD.Modes
