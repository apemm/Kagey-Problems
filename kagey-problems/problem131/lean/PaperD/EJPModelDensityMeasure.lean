import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# Identification of a measure from its integrable Fourier inverse

Fourier inversion and characteristic-function uniqueness identify an actual
measure once its inverse transform is proved nonnegative and integrable.
The Gaussian approximation argument supplies these properties separately.
-/

open MeasureTheory Complex Real
open scoped FourierTransform RealInnerProductSpace

namespace Kagey131.PaperD.ModelFourier

theorem measure_eq_withDensity_of_fourier (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : Integrable (charFun μ)) (ρ : ℝ → ℝ) (hρi : Integrable ρ)
    (hρpos : ∀ x, 0 ≤ ρ x)
    (hP : 𝓕 (fun t : ℝ => charFun μ (2 * Real.pi * t)) =
      fun x => (ρ x : ℂ)) :
    μ = volume.withDensity (fun x => ENNReal.ofReal (ρ x)) := by
  let F : ℝ → ℂ := fun t => charFun μ (2 * Real.pi * t)
  have hFi : Integrable F := hφ.comp_mul_left' (by positivity : 2 * Real.pi ≠ 0)
  have hFc : Continuous F :=
    (continuous_charFun (μ := μ)).comp (continuous_const.mul continuous_id)
  have hρc : Integrable (fun x => (ρ x : ℂ)) := Complex.ofRealCLM.integrable_comp hρi
  have hFour : Integrable (𝓕 F) := by simpa only [F, hP] using hρc
  have hInv : 𝓕⁻ (fun x => (ρ x : ℂ)) = F := by
    simpa only [F, hP] using hFc.fourierInv_fourier_eq hFi hFour
  have hρm : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) volume :=
    hρi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) :=
    isFiniteMeasure_withDensity
      ((lintegral_ofReal_ne_top_iff_integrable hρi.aestronglyMeasurable
        (ae_of_all _ hρpos)).mpr hρi)
  apply Measure.ext_of_charFun
  funext t
  calc
    charFun μ t = F (t / (2 * Real.pi)) := by
      dsimp [F]
      congr 1
      field_simp [Real.pi_ne_zero]
    _ = 𝓕⁻ (fun x => (ρ x : ℂ)) (t / (2 * Real.pi)) :=
      (congrFun hInv _).symm
    _ = charFun (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) t := by
      rw [fourierInv_eq', charFun_apply_real,
        integral_withDensity_eq_integral_toReal_smul₀ hρm
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [ENNReal.toReal_ofReal (hρpos x)]
        simp only [smul_eq_mul, Complex.real_smul]
        have he : 2 * Real.pi * inner ℝ x (t / (2 * Real.pi)) = t * x := by
          simp only [RCLike.inner_apply, conj_trivial]
          field_simp [Real.pi_ne_zero]
        rw [he]
        have hec : ((t * x : ℝ) : ℂ) * I = I * (t : ℂ) * (x : ℂ) := by
          push_cast
          ring
        rw [hec, mul_comm]
        congr 2
        ring

end Kagey131.PaperD.ModelFourier
