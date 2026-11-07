import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open MeasureTheory Filter Set Finset
open scoped Topology

namespace Kagey131.PaperD.ModelLimit

def gridCell (N j : ℕ) : Set ℝ := Ico ((j : ℝ) / N) (((j : ℝ) + 1) / N)

noncomputable def gridStep (N : ℕ) (F : ℕ → ℂ) (v : ℝ) : ℂ :=
  ∑ j ∈ range N, (gridCell N j).indicator (fun _ => F j) v

theorem gridCell_subset {N j : ℕ} (hN : 0 < N) (hj : j < N) :
    gridCell N j ⊆ Ico (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  intro v hv
  refine ⟨(div_nonneg (Nat.cast_nonneg j) hNr.le).trans hv.1, ?_⟩
  exact hv.2.trans_le ((div_le_one hNr).mpr (by exact_mod_cast hj))

theorem grid_index_lt {N : ℕ} (hN : 0 < N) {v : ℝ} (hv : v ∈ Ico (0 : ℝ) 1) :
    ⌊(N : ℝ) * v⌋₊ < N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (Nat.floor_lt (mul_nonneg hNr.le hv.1)).mpr
  nlinarith [hv.2]

theorem gridStep_eq_floor {N : ℕ} (hN : 0 < N) (F : ℕ → ℂ)
    {v : ℝ} (hv : v ∈ Ico (0 : ℝ) 1) :
    gridStep N F v = F ⌊(N : ℝ) * v⌋₊ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNv : 0 ≤ (N : ℝ) * v := mul_nonneg hNr.le hv.1
  have hm : v ∈ gridCell N ⌊(N : ℝ) * v⌋₊ := by
    constructor
    · exact (div_le_iff₀ hNr).mpr (by simpa [mul_comm] using Nat.floor_le hNv)
    · exact (lt_div_iff₀ hNr).mpr (by simpa [mul_comm] using Nat.lt_floor_add_one ((N : ℝ) * v))
  unfold gridStep
  rw [Finset.sum_eq_single ⌊(N : ℝ) * v⌋₊]
  · exact Set.indicator_of_mem hm _
  · intro j hj hne
    apply Set.indicator_of_notMem
    intro hjv
    apply hne
    symm
    apply (Nat.floor_eq_iff hNv).mpr
    constructor
    · simpa [mul_comm] using (div_le_iff₀ hNr).mp hjv.1
    · simpa [mul_comm] using (lt_div_iff₀ hNr).mp hjv.2
  · intro hnot
    exact False.elim (hnot (mem_range.mpr (grid_index_lt hN hv)))

theorem gridStep_integrable (N : ℕ) (F : ℕ → ℂ) : Integrable (gridStep N F) := by
  apply integrable_finsetSum
  intro j _
  apply (integrable_indicator_iff measurableSet_Ico).mpr
  exact integrableOn_const (by simp)

theorem integral_gridStep {N : ℕ} (hN : 0 < N) (F : ℕ → ℂ) :
    (∫ v : ℝ in Ioo 0 1, gridStep N F v) = (1 / (N : ℝ)) • ∑ j ∈ range N, F j := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← integral_Ico_eq_integral_Ioo, ← integral_indicator measurableSet_Ico]
  have heq : (Ico (0 : ℝ) 1).indicator (gridStep N F) = gridStep N F := by
    funext v
    by_cases hv : v ∈ Ico (0 : ℝ) 1
    · simp [hv]
    · rw [Set.indicator_of_notMem hv]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      apply Set.indicator_of_notMem
      exact fun h => hv (gridCell_subset hN (mem_range.mp hj) h)
  rw [heq]
  change (∫ v : ℝ, ∑ j ∈ range N, (gridCell N j).indicator (fun _ => F j) v) = _
  rw [integral_finsetSum]
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold gridCell
    rw [integral_indicator_const _ measurableSet_Ico]
    congr 1
    simp only [Real.volume_real_Ico]
    rw [show ((j : ℝ) + 1) / N - (j : ℝ) / N = 1 / N by ring,
      max_eq_left (by positivity : (0 : ℝ) ≤ 1 / N)]
  · intro j _
    exact (integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_const (by simp))

/-- Bounded triangular Riemann sums converge from their moving-grid pointwise limits. -/
theorem triangular_riemann_tendsto (F : ℕ → ℕ → ℂ) (f : ℝ → ℂ)
    (hbound : ∀ N : ℕ, 0 < N → ∀ j < N, ‖F N j‖ ≤ 1)
    (hpoint : ∀ v ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun n : ℕ => F (n + 1) ⌊((n + 1 : ℕ) : ℝ) * v⌋₊) atTop (𝓝 (f v))) :
    Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ)) • ∑ j ∈ range (n + 1), F (n + 1) j)
      atTop (𝓝 (∫ v : ℝ in Ioo 0 1, f v)) := by
  have hi := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (F := fun n => gridStep (n + 1) (F (n + 1))) (f := f) (fun _ => (1 : ℝ))
    (fun n => (gridStep_integrable (n + 1) (F (n + 1))).aestronglyMeasurable.restrict)
    (integrable_const 1) (fun n => ?_) ?_
  · simpa only [integral_gridStep (Nat.succ_pos _)] using hi
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [gridStep_eq_floor (Nat.succ_pos _) _ ⟨hv.1.le, hv.2⟩]
    exact hbound _ (Nat.succ_pos _) _ (grid_index_lt (Nat.succ_pos _) ⟨hv.1.le, hv.2⟩)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    apply (hpoint v hv).congr
    intro n
    exact (gridStep_eq_floor (Nat.succ_pos _) _ ⟨hv.1.le, hv.2⟩).symm

end Kagey131.PaperD.ModelLimit
