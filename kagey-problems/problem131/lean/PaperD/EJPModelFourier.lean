import PaperD.EJPModelFourierSupport
import PaperD.Modes.RevisionShape
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal FourierTransform RealInnerProductSpace
namespace Kagey131.PaperD.ModelFourier

noncomputable def canonicalFairDensity (μ : Measure ℝ) : ℝ → ℝ :=
  Modes.normalizedFourierDensity (fun t => ((charFun μ t).re : ℂ))

theorem conditionalFourierHyp_of_fixedPoint {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hfix : μ = fixedPointLaw a μ)
    (hmean : (∫ x : ℝ, x ∂μ) ≠ 0) :
    Modes.ConditionalFourierHyp a (canonicalFairDensity μ) (charFun μ) := by
  let : Measure.IsOpenPosMeasure μ := isOpenPosMeasure_of_fixedPoint ha₀ ha₁ μ hfix hmean
  refine ⟨continuous_charFun,fun t => norm_charFun_le_one t,?_,
    charFun_norm_tendsto_zero_of_fixedPoint ha₀ ha₁.le μ hfix,
    fun t _ => norm_charFun_smoothing (by linarith) ha₁.le μ hfix t,rfl⟩
  intro t
  simp only [charFun_neg,RCLike.norm_conj]

end Kagey131.PaperD.ModelFourier
