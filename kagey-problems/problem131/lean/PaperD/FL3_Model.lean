import PaperD.FL3_AE

/-! # Paper F, track FL3: a non-vacuity check

A model on `Ω = Bool` with the fair measure, all runs equal to `1` and `sgn = id` satisfies every
hypothesis of `prop_two_renewal_center_fresh_ae` and `prop_end_ae` (from the FL3 review). -/

namespace Kagey131.PaperD.FL3.Model

open Kagey131.PaperD.FL3 MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def fair : Measure Bool := (PMF.bernoulli (1/2) (by norm_num)).toMeasure
theorem fair_isProbabilityMeasure : IsProbabilityMeasure fair := by unfold fair; infer_instance

attribute [instance] fair_isProbabilityMeasure

def R1 : ℕ → Bool → ℕ := fun _ _ => 1

theorem hind1 : iIndepFun R1 fair := by
  refine (iIndepFun_iff_map_fun_eq_infinitePi_map (X := R1) (fun _ => measurable_const)).2 ?_
  have e : ∀ i, Measure.map (R1 i) fair = Measure.dirac 1 := fun i => by show Measure.map (fun _ => 1) fair = _; rw [Measure.map_const, measure_univ, one_smul]
  have e2 : Measure.map (fun ω i => R1 i ω) fair = Measure.dirac (fun _ => 1) := by show Measure.map (fun _ => fun _ => 1) fair = _; rw [Measure.map_const, measure_univ, one_smul]
  rw [e2]; simp_rw [e]; exact (Measure.infinitePi_dirac _).symm

theorem hsind1 : IndepFun id (runVec R1) fair := by
  have : runVec R1 = fun _ => (fun _ => 1) := rfl
  rw [this]; exact indepFun_const_right _ _

theorem hfair1 : fair {ω | id ω = true} = 1/2 := by
  unfold fair
  have : {ω : Bool | id ω = true} = {true} := by ext; simp
  rw [this, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.bernoulli_apply]

example : fair {ω | walkA id R1 (1 + 1) ω = 1} =
    ∑' m, uRen fair R1 (m+1) 1 * (qRen fair R1 (m+1) 1 + qRen fair R1 (m+2) 1) :=
  prop_two_renewal_center_fresh_ae (fun _ => measurable_const) measurable_id hind1 hsind1
    (fun _ _ => IdentDistrib.refl measurable_const.aemeasurable)
    (fun _ => Filter.Eventually.of_forall (fun _ => le_rfl))
    (IdentDistrib.refl measurable_const.aemeasurable) le_rfl

example : (fair {ω | walkA id R1 2 ω = 2}) = 1/2 * fair {ω | 2 ≤ R1 0 ω} :=
  (prop_end_ae measurable_id hsind1 hfair1
    (fun _ => Filter.Eventually.of_forall (fun _ => le_rfl)) (by norm_num)).1

end Kagey131.PaperD.FL3.Model
