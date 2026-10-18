import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 2000, …, 2000` (generated)

Written by `t7gen.py` from the parameter table of `t7params.py`. For every `N` there are two point
runs (`pL`, `pH`, at the ends of a bracket `[pl/q, ph/q]` of the crossing, `q = 2^64`) and one
interval run (`pI`). Each run is checked by kernel evaluation (`decide +kernel`): the segments
between checkpoints (`segOK`, the checkpoint rows are numerals computed at elaboration time by
`t7val%`, untrusted) and the final test. The theorems `cvxN : ConvexBetweenHumps N` and
`cenN : CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N` (even `N`) use only the
standard axioms.
-/

namespace Kagey131.PaperD.T7

open Kagey131.PaperD Kagey131.PaperD.T5

set_option maxRecDepth 100000
set_option Elab.async false

/-! ### `N = 2000` -/

def pL2000 : Prm := ⟨81, 38, 40, 2002, 11, 18446744073709551616, 98331796973998059, 98331796973998059⟩
def pH2000 : Prm := ⟨81, 38, 40, 2002, 11, 18446744073709551616, 98332896485625835, 98332896485625835⟩
def pI2000 : Prm := ⟨68, 34, 31, 2002, 11, 18446744073709551616, 98331796973998059, 98332896485625835⟩
noncomputable def L2000_cp1 : Nat × Nat := t7val% (fastRun pL2000 1 999 (init pL2000) (init pL2000))
theorem L2000_seg1 : segOK pL2000 1 999 (init pL2000) (init pL2000) L2000_cp1.1 L2000_cp1.2 = true := by
  decide +kernel
noncomputable def L2000_cp2 : Nat × Nat := t7val% (fastRun pL2000 1 1413 (init pL2000) (init pL2000))
theorem L2000_seg2 : segOK pL2000 1000 414 L2000_cp1.1 L2000_cp1.2 L2000_cp2.1 L2000_cp2.2 = true := by
  decide +kernel
noncomputable def L2000_cp3 : Nat × Nat := t7val% (fastRun pL2000 1 1731 (init pL2000) (init pL2000))
theorem L2000_seg3 : segOK pL2000 1414 318 L2000_cp2.1 L2000_cp2.2 L2000_cp3.1 L2000_cp3.2 = true := by
  decide +kernel
theorem L2000_fin : (prmOK pL2000 2000 && ptTest pL2000 (runFrom pL2000 (fmask pL2000) (cmask pL2000) (hmask pL2000) 1732 268 (true, L2000_cp3.1, L2000_cp3.2)) 2000 1000 false) = true := by
  decide +kernel
theorem L2000_ok : RunOK pL2000 2000 (runFrom pL2000 (fmask pL2000) (cmask pL2000) (hmask pL2000) 1732 268 (true, L2000_cp3.1, L2000_cp3.2)) ∧ ptTest pL2000 (runFrom pL2000 (fmask pL2000) (cmask pL2000) (hmask pL2000) 1732 268 (true, L2000_cp3.1, L2000_cp3.2)) 2000 1000 false = true :=
  fin_run (runOK_seg (prmOK_of_and L2000_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L2000_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L2000_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L2000_fin) true) L2000_seg1) L2000_seg2) L2000_seg3) (by decide) rfl L2000_fin ptTest_fst
noncomputable def H2000_cp1 : Nat × Nat := t7val% (fastRun pH2000 1 999 (init pH2000) (init pH2000))
theorem H2000_seg1 : segOK pH2000 1 999 (init pH2000) (init pH2000) H2000_cp1.1 H2000_cp1.2 = true := by
  decide +kernel
noncomputable def H2000_cp2 : Nat × Nat := t7val% (fastRun pH2000 1 1413 (init pH2000) (init pH2000))
theorem H2000_seg2 : segOK pH2000 1000 414 H2000_cp1.1 H2000_cp1.2 H2000_cp2.1 H2000_cp2.2 = true := by
  decide +kernel
noncomputable def H2000_cp3 : Nat × Nat := t7val% (fastRun pH2000 1 1731 (init pH2000) (init pH2000))
theorem H2000_seg3 : segOK pH2000 1414 318 H2000_cp2.1 H2000_cp2.2 H2000_cp3.1 H2000_cp3.2 = true := by
  decide +kernel
theorem H2000_fin : (prmOK pH2000 2000 && ptTest pH2000 (runFrom pH2000 (fmask pH2000) (cmask pH2000) (hmask pH2000) 1732 268 (true, H2000_cp3.1, H2000_cp3.2)) 2000 1000 true) = true := by
  decide +kernel
theorem H2000_ok : RunOK pH2000 2000 (runFrom pH2000 (fmask pH2000) (cmask pH2000) (hmask pH2000) 1732 268 (true, H2000_cp3.1, H2000_cp3.2)) ∧ ptTest pH2000 (runFrom pH2000 (fmask pH2000) (cmask pH2000) (hmask pH2000) 1732 268 (true, H2000_cp3.1, H2000_cp3.2)) 2000 1000 true = true :=
  fin_run (runOK_seg (prmOK_of_and H2000_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H2000_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H2000_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H2000_fin) true) H2000_seg1) H2000_seg2) H2000_seg3) (by decide) rfl H2000_fin ptTest_fst
noncomputable def I2000_cp1 : Nat × Nat := t7val% (fastRun pI2000 1 1154 (init pI2000) (init pI2000))
theorem I2000_seg1 : segOK pI2000 1 1154 (init pI2000) (init pI2000) I2000_cp1.1 I2000_cp1.2 = true := by
  decide +kernel
noncomputable def I2000_cp2 : Nat × Nat := t7val% (fastRun pI2000 1 1632 (init pI2000) (init pI2000))
theorem I2000_seg2 : segOK pI2000 1155 478 I2000_cp1.1 I2000_cp1.2 I2000_cp2.1 I2000_cp2.2 = true := by
  decide +kernel
theorem I2000_fin : (prmOK pI2000 2000 && intTest pI2000 (runFrom pI2000 (fmask pI2000) (cmask pI2000) (hmask pI2000) 1633 367 (true, I2000_cp2.1, I2000_cp2.2)) 2000 22 true) = true := by
  decide +kernel
theorem I2000_ok : RunOK pI2000 2000 (runFrom pI2000 (fmask pI2000) (cmask pI2000) (hmask pI2000) 1633 367 (true, I2000_cp2.1, I2000_cp2.2)) ∧ intTest pI2000 (runFrom pI2000 (fmask pI2000) (cmask pI2000) (hmask pI2000) 1633 367 (true, I2000_cp2.1, I2000_cp2.2)) 2000 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I2000_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I2000_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I2000_fin) true) I2000_seg1) I2000_seg2) (by decide) rfl I2000_fin intTest_fst
theorem link2000 : linkOK pL2000 pH2000 pI2000 = true := by decide +kernel
theorem cvx2000 : ConvexBetweenHumps 2000 :=
  cvx_of L2000_ok H2000_ok I2000_ok link2000 (by decide)
theorem cenlink2000 : cenLinkOK pI2000 2000 = true := by decide +kernel
theorem cen2000 : CenterUniqueMin 2000 ∧ DipHyp 2000 ∧ OnePointHyps 2000 :=
  cen_of L2000_ok H2000_ok I2000_ok link2000 cenlink2000

/-! ### The range -/

theorem cvx_2000_2000 {N : ℕ} (h1 : 2000 ≤ N) (h2 : N ≤ 2000) : ConvexBetweenHumps N := by
  obtain rfl : N = 2000 := by omega
  exact cvx2000

theorem cen_2000_2000 {N : ℕ} (h1 : 2000 ≤ N) (h2 : N ≤ 2000) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  obtain rfl : N = 2000 := by omega
  exact cen2000

end Kagey131.PaperD.T7
