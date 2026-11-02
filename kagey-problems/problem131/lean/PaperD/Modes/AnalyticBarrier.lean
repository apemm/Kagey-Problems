import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# The continuous barrier argument for the fixed-point density bound

The lemma below makes the first-contact argument precise. Its local strict-bound
hypothesis is discharged by the smoothing integral in `AnalyticDecay`.
-/

namespace Kagey131.PaperD.Modes

open Set Filter

/-- A continuous function cannot first meet a barrier if the functional inequality
gives strict separation at every possible first contact. -/
theorem continuous_barrier {f b : ℝ → ℝ} {A : ℝ}
    (hf : Continuous f) (hb : Continuous b) (hA : 0 ≤ A)
    (hinit : ∀ t ∈ Icc 0 A, f t ≤ b t)
    (hstep : ∀ t, A ≤ t → (∀ u ∈ Ico 0 t, f u ≤ b u) → f t < b t) :
    ∀ t, 0 ≤ t → f t ≤ b t := by
  intro t ht
  by_contra hbad
  have hbt : b t < f t := lt_of_not_ge hbad
  have hAt : A < t := by
    by_contra h
    exact (not_lt_of_ge (hinit t ⟨ht, le_of_not_gt h⟩)) hbt
  let S : Set ℝ := {u | A ≤ u ∧ b u ≤ f u}
  have hclosed : IsClosed S := isClosed_Ici.inter (isClosed_le hb hf)
  have hnon : S.Nonempty := ⟨t, hAt.le, hbt.le⟩
  have hbelow : BddBelow S := ⟨A, fun _ hx => hx.1⟩
  have hc : sInf S ∈ S := hclosed.csInf_mem hnon hbelow
  have hprev : ∀ u ∈ Ico 0 (sInf S), f u ≤ b u := by
    intro u hu
    by_cases huA : u ≤ A
    · exact hinit u ⟨hu.1, huA⟩
    · by_contra h
      have humem : u ∈ S := ⟨(lt_of_not_ge huA).le, (lt_of_not_ge h).le⟩
      exact (not_lt_of_ge (csInf_le hbelow humem)) hu.2
  exact (not_lt_of_ge hc.2) (hstep (sInf S) hc.1 hprev)

end Kagey131.PaperD.Modes
