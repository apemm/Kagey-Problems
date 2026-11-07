import PaperD.EJPAnalyticThresholdParam
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The nonsingular square-root coordinate

In the coordinate x = sqrt y the predicted real and imaginary parts are
analytic at zero. Their jets, singular ODEs, time-chain identity, and continuous
coefficient are derived from the H ODE. These are the inputs used by the
separate analytic identification argument.
-/

open Set Filter
open scoped Topology
namespace Kagey131.PaperD.AnalyticThresholdParam

noncomputable def coordinateT (a : ℝ) (H : ℝ → ℝ) (x : ℝ) := x * H (x^2)^(-a)
noncomputable def coordinateA (H : ℝ → ℝ) (x : ℝ) := H (x^2) * Real.sqrt (1-x^2)
noncomputable def coordinateB (H : ℝ → ℝ) (x : ℝ) := H (x^2) * x
noncomputable def coordinateC (a : ℝ) (H : ℝ → ℝ) (x : ℝ) :=
  1 / (a * H (x^2) * Real.sqrt (1-x^2))

 theorem hasDerivAt_coordinateA {H : ℝ → ℝ} {x : ℝ}
    (hd : DifferentiableAt ℝ H (x^2)) (hx : x^2 < 1) :
    HasDerivAt (coordinateA H)
      (2*x*deriv H (x^2)*Real.sqrt (1-x^2) - H (x^2)*x/Real.sqrt (1-x^2)) x := by
  apply ((hd.hasDerivAt.comp (h := fun u : ℝ => u^2) (h₂ := H) x ((hasDerivAt_id x).pow 2)).mul
    (((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).sqrt
      (sub_pos.mpr hx).ne')).congr_deriv
  dsimp
  ring
 theorem hasDerivAt_coordinateB {H : ℝ → ℝ} {x : ℝ}
    (hd : DifferentiableAt ℝ H (x^2)) :
    HasDerivAt (coordinateB H) (2*x^2*deriv H (x^2) + H (x^2)) x := by
  apply ((hd.hasDerivAt.comp (h := fun u : ℝ => u^2) (h₂ := H) x ((hasDerivAt_id x).pow 2)).mul (hasDerivAt_id x)).congr_deriv
  dsimp
  ring

 theorem coordinate_AB_ode {a x : ℝ} {H : ℝ → ℝ}
    (ha : a ≠ 0) (hH : 0 < H (x^2)) (hx : x^2 < 1)
    (hd : DifferentiableAt ℝ H (x^2)) (hode : SatisfiesODE a H (x^2)) :
    x * deriv (coordinateA H) x = coordinateC a H x *
      (coordinateA H x ^ 2 - coordinateA H x - a * coordinateB H x ^ 2) ∧
    x * deriv (coordinateB H) x = coordinateC a H x *
      (((1+a) * coordinateA H x - 1) * coordinateB H x) := by
  have hs := Real.sqrt_pos.mpr (sub_pos.mpr hx)
  have hsq := Real.sq_sqrt (sub_pos.mpr hx).le
  have hm := congrArg (fun z : ℝ => z * Real.sqrt (1-x^2)) hode
  unfold SatisfiesODE at hm
  simp only [inv_mul_cancel₀ hs.ne'] at hm
  rw [(hasDerivAt_coordinateA hd hx).deriv, (hasDerivAt_coordinateB hd).deriv]
  unfold coordinateA coordinateB coordinateC
  constructor
  · field_simp
    nlinarith [congrArg (fun z : ℝ => z * H (x^2)) hm,
      congrArg (fun z : ℝ => z * (H (x^2)*Real.sqrt (1-x^2))) hsq]
  · field_simp
    nlinarith [congrArg (fun z : ℝ => z * (H (x^2)*x)) hm]

 theorem coordinateC_zero {a : ℝ} {H : ℝ → ℝ} (h0 : H 0 = 1) :
    coordinateC a H 0 = 1/a := by simp [coordinateC, h0]
 theorem coordinate_values_zero {a : ℝ} {H : ℝ → ℝ} (h0 : H 0 = 1) :
    coordinateA H 0 = 1 ∧ coordinateB H 0 = 0 ∧ coordinateT a H 0 = 0 := by
  simp [coordinateA, coordinateB, coordinateT, h0]
 theorem coordinate_jets_zero {a : ℝ} {H : ℝ → ℝ} (h0 : H 0 = 1)
    (hd : DifferentiableAt ℝ H 0) :
    HasDerivAt (coordinateA H) 0 0 ∧ HasDerivAt (coordinateB H) 1 0 ∧
    HasDerivAt (coordinateT a H) 1 0 := by
  have hd' : DifferentiableAt ℝ H ((0 : ℝ)^2) := by simpa using hd
  refine ⟨by simpa [h0] using hasDerivAt_coordinateA hd' (by norm_num),
    by simpa [h0] using hasDerivAt_coordinateB hd', ?_⟩
  have hp := (hd'.hasDerivAt.comp (h := fun u : ℝ => u^2) (h₂ := H) 0 ((hasDerivAt_id (0 : ℝ)).pow 2)).rpow_const
    (p := -a) (Or.inl (by simpa [h0] : H ((0 : ℝ)^2) ≠ 0))
  convert! (hasDerivAt_id (0 : ℝ)).mul hp using 1 <;> simp [coordinateT, h0]

/-- Positive-base rpow analyticity is derived from exp and log. -/
theorem analyticAt_rpow_of_pos {f : ℝ → ℝ} {x p : ℝ}
    (hf : AnalyticAt ℝ f x) (hp : 0 < f x) :
    AnalyticAt ℝ (fun u => f u ^ p) x := by
  apply (((hf.log hp).mul analyticAt_const).rexp').congr
  filter_upwards [hf.continuousAt.eventually (lt_mem_nhds hp)] with u hu
  exact (Real.rpow_def_of_pos hu p).symm

 theorem coordinate_analyticAt {a x : ℝ} {H : ℝ → ℝ}
    (hd : AnalyticAt ℝ H (x^2)) (hH : 0 < H (x^2)) (hx : x^2 < 1) :
    AnalyticAt ℝ (coordinateT a H) x ∧ AnalyticAt ℝ (coordinateA H) x ∧
    AnalyticAt ℝ (coordinateB H) x := by
  have hh : AnalyticAt ℝ (fun u : ℝ => H (u^2)) x := hd.comp (f := fun u : ℝ => u^2) (analyticAt_id.pow 2)
  have hs : AnalyticAt ℝ (fun u : ℝ => Real.sqrt (1-u^2)) x := by
    simp_rw [Real.sqrt_eq_rpow]
    exact analyticAt_rpow_of_pos (analyticAt_const.sub (analyticAt_id.pow 2)) (sub_pos.mpr hx)
  exact ⟨analyticAt_id.mul (analyticAt_rpow_of_pos hh hH), hh.mul hs, hh.mul analyticAt_id⟩



/-- Time-chain identity used to transport the transform ODE into x coordinates. -/
theorem hasDerivAt_coordinateT {a x : ℝ} {H : ℝ → ℝ}
    (hH : 0 < H (x^2)) (hx : x^2 < 1)
    (hd : DifferentiableAt ℝ H (x^2)) (hode : SatisfiesODE a H (x^2)) :
    HasDerivAt (coordinateT a H)
      (H (x^2)^(-a) / (H (x^2)*Real.sqrt (1-x^2))) x := by
  have hs := Real.sqrt_pos.mpr (sub_pos.mpr hx)
  have hm := congrArg (fun z : ℝ => z * Real.sqrt (1-x^2)) hode
  unfold SatisfiesODE at hm
  simp only [inv_mul_cancel₀ hs.ne'] at hm
  apply ((hasDerivAt_id x).mul
    ((hd.hasDerivAt.comp (h := fun u : ℝ => u^2) (h₂ := H) x ((hasDerivAt_id x).pow 2)).rpow_const
      (Or.inl hH.ne'))).congr_deriv
  dsimp
  rw [Real.rpow_sub hH, Real.rpow_one]
  field_simp
  nlinarith [hm]

 theorem coordinateT_chain {a x : ℝ} {H : ℝ → ℝ}
    (ha : a ≠ 0) (hH : 0 < H (x^2)) (hx : x^2 < 1)
    (hd : DifferentiableAt ℝ H (x^2)) (hode : SatisfiesODE a H (x^2)) :
    x * deriv (coordinateT a H) x = a * coordinateC a H x * coordinateT a H x := by
  rw [(hasDerivAt_coordinateT hH hx hd hode).deriv]
  unfold coordinateC coordinateT
  field_simp

 theorem coordinateC_continuousAt_zero {a : ℝ} {H : ℝ → ℝ}
    (ha : a ≠ 0) (h0 : H 0 = 1) (hc : ContinuousAt H 0) :
    ContinuousAt (coordinateC a H) 0 := by
  have hh : ContinuousAt (fun x : ℝ => H (x^2)) 0 := by
    have hc' : ContinuousAt H ((0 : ℝ)^2) := by simpa using hc
    exact hc'.comp (f := fun u : ℝ => u^2) (continuousAt_id.pow 2)
  exact continuousAt_const.div
    ((continuousAt_const.mul hh).mul
      (Real.continuous_sqrt.continuousAt.comp (continuousAt_const.sub (continuousAt_id.pow 2))))
    (by simpa [h0] using ha)

end Kagey131.PaperD.AnalyticThresholdParam




