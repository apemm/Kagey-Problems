import PaperD.Modes.TwoModes
import PaperD.Modes.StrictCore

/-! The strict shape conclusion for the actual limit-law interface. -/

namespace Kagey131.PaperD.Modes

open Set

/-- The full strict monotonicity alternative of Theorem 4.2. -/
theorem two_modes_strict {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4)
    {g : ℝ → ℝ} (hg : DensityHyp g) (hlaw : LawConvHyp ε (1 - 2 * ε) g)
    (hflat : NoFlatInterval g) :
    (StrictMonoOn g (Iic 0) ∧ StrictAntiOn g (Ici 0)) ∨
    (∃ c > 0, StrictMonoOn g (Icc 0 c) ∧ StrictAntiOn g (Ici c) ∧
      StrictMonoOn g (Iic (-c)) ∧ StrictAntiOn g (Icc (-c) 0) ∧ g 0 < g c) := by
  rcases two_modes hε0 hε hg hlaw with ha | ⟨c, hc, hm, ha, hgc⟩
  · exact Or.inl ⟨monotoneOn_strict_of_noFlat ordConnected_Iic ha.1 hflat,
      antitoneOn_strict_of_noFlat ordConnected_Ici ha.2 hflat⟩
  · have hm' := monotoneOn_strict_of_noFlat ordConnected_Icc hm hflat
    have ha' := antitoneOn_strict_of_noFlat ordConnected_Ici ha hflat
    refine Or.inr ⟨c, hc, hm', ha', ?_, ?_, hgc⟩
    · intro x hx y hy hxy
      change x ≤ -c at hx
      change y ≤ -c at hy
      rw [← hg.even x, ← hg.even y]
      exact ha' (by simp only [mem_Ici]; linarith [hy])
        (by simp only [mem_Ici]; linarith [hx]) (by linarith)
    · intro x hx y hy hxy
      rw [← hg.even x, ← hg.even y]
      exact hm' (by constructor <;> linarith [hy.1, hy.2])
        (by constructor <;> linarith [hx.1, hx.2]) (by linarith)

end Kagey131.PaperD.Modes
