import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# The sharp fourth-moment inequality for a uniform scale mixture

Khinchine's representation of a distribution unimodal at zero is `U * Z`,
where `U` is uniform on `(0,1)` and independent of `Z`. This file proves the
moment inequality from that representation; it does not assume the inequality.
-/

namespace Kagey131.PaperD.Modes

open MeasureTheory ProbabilityTheory Set

theorem uniform_unit_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U : Ω → ℝ} (hU : AEMeasurable U P)
    (hlaw : P.map U = volume.restrict (Ioc (0 : ℝ) 1)) (n : ℕ) :
    (∫ ω, U ω ^ n ∂P) = 1 / (n + 1 : ℝ) := by
  rw [← integral_map hU (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ n) (P.map U)),
    hlaw, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp

theorem independent_uniform_product_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U Z : Ω → ℝ} (hU : AEMeasurable U P) (hZ : AEMeasurable Z P)
    (hi : IndepFun U Z P) (hlaw : P.map U = volume.restrict (Ioc (0 : ℝ) 1)) (n : ℕ) :
    (∫ ω, (U ω * Z ω) ^ n ∂P) = (∫ ω, Z ω ^ n ∂P) / (n + 1 : ℝ) := by
  simp_rw [mul_pow]
  rw [hi.integral_fun_comp_mul_comp (f := fun x : ℝ => x ^ n) (g := fun x : ℝ => x ^ n)
    hU hZ (by fun_prop) (by fun_prop),
    uniform_unit_moment hU hlaw]
  ring

/-- Cauchy--Schwarz and the uniform second and fourth moments give `9/5`.
The finite fourth-moment condition is exactly `Z² ∈ L²`. -/
theorem fourth_moment_uniform_product {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U Z : Ω → ℝ}
    (hU : AEMeasurable U P) (hZ : AEMeasurable Z P) (hi : IndepFun U Z P)
    (hlaw : P.map U = volume.restrict (Ioc (0 : ℝ) 1))
    (hZ2 : MemLp (fun ω => Z ω ^ 2) 2 P) :
    (9 / 5 : ℝ) * (∫ ω, (U ω * Z ω) ^ 2 ∂P) ^ 2 ≤
      ∫ ω, (U ω * Z ω) ^ 4 ∂P := by
  have hv := variance_nonneg (fun ω => Z ω ^ 2) P
  rw [variance_eq_sub hZ2] at hv
  change 0 ≤ (∫ ω, (Z ω ^ 2) ^ 2 ∂P) - (∫ ω, Z ω ^ 2 ∂P) ^ 2 at hv
  simp_rw [← pow_mul] at hv
  norm_num at hv
  rw [independent_uniform_product_moment hU hZ hi hlaw 2,
    independent_uniform_product_moment hU hZ hi hlaw 4]
  norm_num
  nlinarith

end Kagey131.PaperD.Modes
