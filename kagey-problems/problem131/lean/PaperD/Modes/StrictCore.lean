import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

/-! Strict monotonicity and modal points from absence of flat intervals. -/

namespace Kagey131.PaperD.Modes

open Set

/-- A function is not constant on any nondegenerate closed interval. -/
def NoFlatInterval (g : ℝ → ℝ) : Prop :=
  ∀ a b, a < b → ¬ EqOn g (fun _ => g a) (Icc a b)

theorem monotoneOn_strict_of_noFlat {g : ℝ → ℝ} {s : Set ℝ}
    (hs : OrdConnected s) (hmono : MonotoneOn g s) (hflat : NoFlatInterval g) :
    StrictMonoOn g s := by
  intro x hx y hy hxy
  by_contra hn
  have heq : g x = g y := le_antisymm (hmono hx hy hxy.le) (not_lt.mp hn)
  apply hflat x y hxy
  intro z hz
  have hzs : z ∈ s := hs.out hx hy hz
  exact le_antisymm ((hmono hzs hy hz.2).trans_eq heq.symm) (hmono hx hzs hz.1)

theorem antitoneOn_strict_of_noFlat {g : ℝ → ℝ} {s : Set ℝ}
    (hs : OrdConnected s) (hanti : AntitoneOn g s) (hflat : NoFlatInterval g) :
    StrictAntiOn g s := by
  intro x hx y hy hxy
  by_contra hn
  have heq : g y = g x := le_antisymm (hanti hx hy hxy.le) (not_lt.mp hn)
  apply hflat x y hxy
  intro z hz
  have hzs : z ∈ s := hs.out hx hy hz
  exact le_antisymm (hanti hx hzs hz.1) (heq.symm.trans_le (hanti hzs hy hz.2))

/-- In the first strict alternative, zero is the only global modal point. -/
theorem unique_mode_zero {g : ℝ → ℝ} (hm : StrictMonoOn g (Iic 0))
    (ha : StrictAntiOn g (Ici 0)) :
    (∀ y, g y ≤ g 0) ∧ (∀ y, g y = g 0 ↔ y = 0) := by
  have hlt : ∀ y, y ≠ 0 → g y < g 0 := by
    intro y hy
    rcases lt_or_gt_of_ne hy with hy | hy
    · exact hm hy.le (by simp) hy
    · exact ha (by simp) hy.le hy
  constructor
  · intro y
    by_cases hy : y = 0
    · simp [hy]
    · exact (hlt y hy).le
  · intro y
    constructor
    · intro he
      by_contra hy
      exact (hlt y hy).ne he
    · rintro rfl
      rfl

/-- In the second strict alternative, the global modal points are exactly `±c`. -/
theorem unique_modes_pair {g : ℝ → ℝ} (heven : ∀ y, g (-y) = g y)
    {c : ℝ} (hc : 0 < c) (hm : StrictMonoOn g (Icc 0 c))
    (ha : StrictAntiOn g (Ici c)) :
    (∀ y, g y ≤ g c) ∧ (∀ y, g y = g c ↔ y = c ∨ y = -c) := by
  have hpos : ∀ y, 0 ≤ y → y ≠ c → g y < g c := by
    intro y hy hyc
    rcases lt_or_gt_of_ne hyc with h | h
    · exact hm ⟨hy, h.le⟩ ⟨hc.le, le_rfl⟩ h
    · exact ha (by simp) h.le h
  have hbound : ∀ y, 0 ≤ y → g y ≤ g c := by
    intro y hy
    by_cases he : y = c
    · simp [he]
    · exact (hpos y hy he).le
  constructor
  · intro y
    rcases le_or_gt 0 y with hy | hy
    · exact hbound y hy
    · rw [← heven y]
      exact hbound (-y) (by linarith)
  · intro y
    constructor
    · intro he
      rcases le_or_gt 0 y with hy | hy
      · left
        by_contra hn
        exact (hpos y hy hn).ne he
      · right
        have hneg : -y = c := by
          by_contra hn
          have := hpos (-y) (by linarith) hn
          rw [heven y] at this
          exact this.ne he
        linarith
    · rintro (rfl | rfl)
      · rfl
      · exact heven c

end Kagey131.PaperD.Modes
