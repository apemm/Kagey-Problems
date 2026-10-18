import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1402, …, 1421` (generated)

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

/-! ### `N = 1402` -/

def pL1402 : Prm := ⟨79, 37, 39, 1404, 11, 18446744073709551616, 131461832717401108, 131461832717401108⟩
def pH1402 : Prm := ⟨79, 37, 39, 1404, 11, 18446744073709551616, 131462932229028884, 131462932229028884⟩
def pI1402 : Prm := ⟨65, 33, 29, 1404, 11, 18446744073709551616, 131461832717401108, 131462932229028884⟩
noncomputable def L1402_cp1 : Nat × Nat := t7val% (fastRun pL1402 1 990 (init pL1402) (init pL1402))
theorem L1402_seg1 : segOK pL1402 1 990 (init pL1402) (init pL1402) L1402_cp1.1 L1402_cp1.2 = true := by
  decide +kernel
theorem L1402_fin : (prmOK pL1402 1402 && ptTest pL1402 (runFrom pL1402 (fmask pL1402) (cmask pL1402) (hmask pL1402) 991 411 (true, L1402_cp1.1, L1402_cp1.2)) 1402 701 false) = true := by
  decide +kernel
theorem L1402_ok : RunOK pL1402 1402 (runFrom pL1402 (fmask pL1402) (cmask pL1402) (hmask pL1402) 991 411 (true, L1402_cp1.1, L1402_cp1.2)) ∧ ptTest pL1402 (runFrom pL1402 (fmask pL1402) (cmask pL1402) (hmask pL1402) 991 411 (true, L1402_cp1.1, L1402_cp1.2)) 1402 701 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1402_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1402_fin) true) L1402_seg1) (by decide) rfl L1402_fin ptTest_fst
noncomputable def H1402_cp1 : Nat × Nat := t7val% (fastRun pH1402 1 990 (init pH1402) (init pH1402))
theorem H1402_seg1 : segOK pH1402 1 990 (init pH1402) (init pH1402) H1402_cp1.1 H1402_cp1.2 = true := by
  decide +kernel
theorem H1402_fin : (prmOK pH1402 1402 && ptTest pH1402 (runFrom pH1402 (fmask pH1402) (cmask pH1402) (hmask pH1402) 991 411 (true, H1402_cp1.1, H1402_cp1.2)) 1402 701 true) = true := by
  decide +kernel
theorem H1402_ok : RunOK pH1402 1402 (runFrom pH1402 (fmask pH1402) (cmask pH1402) (hmask pH1402) 991 411 (true, H1402_cp1.1, H1402_cp1.2)) ∧ ptTest pH1402 (runFrom pH1402 (fmask pH1402) (cmask pH1402) (hmask pH1402) 991 411 (true, H1402_cp1.1, H1402_cp1.2)) 1402 701 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1402_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1402_fin) true) H1402_seg1) (by decide) rfl H1402_fin ptTest_fst
noncomputable def I1402_cp1 : Nat × Nat := t7val% (fastRun pI1402 1 990 (init pI1402) (init pI1402))
theorem I1402_seg1 : segOK pI1402 1 990 (init pI1402) (init pI1402) I1402_cp1.1 I1402_cp1.2 = true := by
  decide +kernel
theorem I1402_fin : (prmOK pI1402 1402 && intTest pI1402 (runFrom pI1402 (fmask pI1402) (cmask pI1402) (hmask pI1402) 991 411 (true, I1402_cp1.1, I1402_cp1.2)) 1402 20 true) = true := by
  decide +kernel
theorem I1402_ok : RunOK pI1402 1402 (runFrom pI1402 (fmask pI1402) (cmask pI1402) (hmask pI1402) 991 411 (true, I1402_cp1.1, I1402_cp1.2)) ∧ intTest pI1402 (runFrom pI1402 (fmask pI1402) (cmask pI1402) (hmask pI1402) 991 411 (true, I1402_cp1.1, I1402_cp1.2)) 1402 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1402_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1402_fin) true) I1402_seg1) (by decide) rfl I1402_fin intTest_fst
theorem link1402 : linkOK pL1402 pH1402 pI1402 = true := by decide +kernel
theorem cvx1402 : ConvexBetweenHumps 1402 :=
  cvx_of L1402_ok H1402_ok I1402_ok link1402 (by decide)
theorem cenlink1402 : cenLinkOK pI1402 1402 = true := by decide +kernel
theorem cen1402 : CenterUniqueMin 1402 ∧ DipHyp 1402 ∧ OnePointHyps 1402 :=
  cen_of L1402_ok H1402_ok I1402_ok link1402 cenlink1402

/-! ### `N = 1403` -/

def pL1403 : Prm := ⟨79, 37, 39, 1405, 11, 18446744073709551616, 131385788868816122, 131385788868816122⟩
def pH1403 : Prm := ⟨79, 37, 39, 1405, 11, 18446744073709551616, 131386888380443898, 131386888380443898⟩
def pI1403 : Prm := ⟨65, 33, 29, 1405, 11, 18446744073709551616, 131385788868816122, 131386888380443898⟩
noncomputable def L1403_cp1 : Nat × Nat := t7val% (fastRun pL1403 1 991 (init pL1403) (init pL1403))
theorem L1403_seg1 : segOK pL1403 1 991 (init pL1403) (init pL1403) L1403_cp1.1 L1403_cp1.2 = true := by
  decide +kernel
theorem L1403_fin : (prmOK pL1403 1403 && ptTest pL1403 (runFrom pL1403 (fmask pL1403) (cmask pL1403) (hmask pL1403) 992 411 (true, L1403_cp1.1, L1403_cp1.2)) 1403 702 false) = true := by
  decide +kernel
theorem L1403_ok : RunOK pL1403 1403 (runFrom pL1403 (fmask pL1403) (cmask pL1403) (hmask pL1403) 992 411 (true, L1403_cp1.1, L1403_cp1.2)) ∧ ptTest pL1403 (runFrom pL1403 (fmask pL1403) (cmask pL1403) (hmask pL1403) 992 411 (true, L1403_cp1.1, L1403_cp1.2)) 1403 702 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1403_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1403_fin) true) L1403_seg1) (by decide) rfl L1403_fin ptTest_fst
noncomputable def H1403_cp1 : Nat × Nat := t7val% (fastRun pH1403 1 991 (init pH1403) (init pH1403))
theorem H1403_seg1 : segOK pH1403 1 991 (init pH1403) (init pH1403) H1403_cp1.1 H1403_cp1.2 = true := by
  decide +kernel
theorem H1403_fin : (prmOK pH1403 1403 && ptTest pH1403 (runFrom pH1403 (fmask pH1403) (cmask pH1403) (hmask pH1403) 992 411 (true, H1403_cp1.1, H1403_cp1.2)) 1403 702 true) = true := by
  decide +kernel
theorem H1403_ok : RunOK pH1403 1403 (runFrom pH1403 (fmask pH1403) (cmask pH1403) (hmask pH1403) 992 411 (true, H1403_cp1.1, H1403_cp1.2)) ∧ ptTest pH1403 (runFrom pH1403 (fmask pH1403) (cmask pH1403) (hmask pH1403) 992 411 (true, H1403_cp1.1, H1403_cp1.2)) 1403 702 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1403_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1403_fin) true) H1403_seg1) (by decide) rfl H1403_fin ptTest_fst
noncomputable def I1403_cp1 : Nat × Nat := t7val% (fastRun pI1403 1 991 (init pI1403) (init pI1403))
theorem I1403_seg1 : segOK pI1403 1 991 (init pI1403) (init pI1403) I1403_cp1.1 I1403_cp1.2 = true := by
  decide +kernel
theorem I1403_fin : (prmOK pI1403 1403 && intTest pI1403 (runFrom pI1403 (fmask pI1403) (cmask pI1403) (hmask pI1403) 992 411 (true, I1403_cp1.1, I1403_cp1.2)) 1403 20 false) = true := by
  decide +kernel
theorem I1403_ok : RunOK pI1403 1403 (runFrom pI1403 (fmask pI1403) (cmask pI1403) (hmask pI1403) 992 411 (true, I1403_cp1.1, I1403_cp1.2)) ∧ intTest pI1403 (runFrom pI1403 (fmask pI1403) (cmask pI1403) (hmask pI1403) 992 411 (true, I1403_cp1.1, I1403_cp1.2)) 1403 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1403_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1403_fin) true) I1403_seg1) (by decide) rfl I1403_fin intTest_fst
theorem link1403 : linkOK pL1403 pH1403 pI1403 = true := by decide +kernel
theorem cvx1403 : ConvexBetweenHumps 1403 :=
  cvx_of L1403_ok H1403_ok I1403_ok link1403 (by decide)

/-! ### `N = 1404` -/

def pL1404 : Prm := ⟨79, 37, 39, 1406, 11, 18446744073709551616, 131309881840469801, 131309881840469801⟩
def pH1404 : Prm := ⟨79, 37, 39, 1406, 11, 18446744073709551616, 131310981352097577, 131310981352097577⟩
def pI1404 : Prm := ⟨65, 33, 29, 1406, 11, 18446744073709551616, 131309881840469801, 131310981352097577⟩
noncomputable def L1404_cp1 : Nat × Nat := t7val% (fastRun pL1404 1 992 (init pL1404) (init pL1404))
theorem L1404_seg1 : segOK pL1404 1 992 (init pL1404) (init pL1404) L1404_cp1.1 L1404_cp1.2 = true := by
  decide +kernel
theorem L1404_fin : (prmOK pL1404 1404 && ptTest pL1404 (runFrom pL1404 (fmask pL1404) (cmask pL1404) (hmask pL1404) 993 411 (true, L1404_cp1.1, L1404_cp1.2)) 1404 702 false) = true := by
  decide +kernel
theorem L1404_ok : RunOK pL1404 1404 (runFrom pL1404 (fmask pL1404) (cmask pL1404) (hmask pL1404) 993 411 (true, L1404_cp1.1, L1404_cp1.2)) ∧ ptTest pL1404 (runFrom pL1404 (fmask pL1404) (cmask pL1404) (hmask pL1404) 993 411 (true, L1404_cp1.1, L1404_cp1.2)) 1404 702 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1404_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1404_fin) true) L1404_seg1) (by decide) rfl L1404_fin ptTest_fst
noncomputable def H1404_cp1 : Nat × Nat := t7val% (fastRun pH1404 1 992 (init pH1404) (init pH1404))
theorem H1404_seg1 : segOK pH1404 1 992 (init pH1404) (init pH1404) H1404_cp1.1 H1404_cp1.2 = true := by
  decide +kernel
theorem H1404_fin : (prmOK pH1404 1404 && ptTest pH1404 (runFrom pH1404 (fmask pH1404) (cmask pH1404) (hmask pH1404) 993 411 (true, H1404_cp1.1, H1404_cp1.2)) 1404 702 true) = true := by
  decide +kernel
theorem H1404_ok : RunOK pH1404 1404 (runFrom pH1404 (fmask pH1404) (cmask pH1404) (hmask pH1404) 993 411 (true, H1404_cp1.1, H1404_cp1.2)) ∧ ptTest pH1404 (runFrom pH1404 (fmask pH1404) (cmask pH1404) (hmask pH1404) 993 411 (true, H1404_cp1.1, H1404_cp1.2)) 1404 702 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1404_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1404_fin) true) H1404_seg1) (by decide) rfl H1404_fin ptTest_fst
noncomputable def I1404_cp1 : Nat × Nat := t7val% (fastRun pI1404 1 992 (init pI1404) (init pI1404))
theorem I1404_seg1 : segOK pI1404 1 992 (init pI1404) (init pI1404) I1404_cp1.1 I1404_cp1.2 = true := by
  decide +kernel
theorem I1404_fin : (prmOK pI1404 1404 && intTest pI1404 (runFrom pI1404 (fmask pI1404) (cmask pI1404) (hmask pI1404) 993 411 (true, I1404_cp1.1, I1404_cp1.2)) 1404 20 true) = true := by
  decide +kernel
theorem I1404_ok : RunOK pI1404 1404 (runFrom pI1404 (fmask pI1404) (cmask pI1404) (hmask pI1404) 993 411 (true, I1404_cp1.1, I1404_cp1.2)) ∧ intTest pI1404 (runFrom pI1404 (fmask pI1404) (cmask pI1404) (hmask pI1404) 993 411 (true, I1404_cp1.1, I1404_cp1.2)) 1404 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1404_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1404_fin) true) I1404_seg1) (by decide) rfl I1404_fin intTest_fst
theorem link1404 : linkOK pL1404 pH1404 pI1404 = true := by decide +kernel
theorem cvx1404 : ConvexBetweenHumps 1404 :=
  cvx_of L1404_ok H1404_ok I1404_ok link1404 (by decide)
theorem cenlink1404 : cenLinkOK pI1404 1404 = true := by decide +kernel
theorem cen1404 : CenterUniqueMin 1404 ∧ DipHyp 1404 ∧ OnePointHyps 1404 :=
  cen_of L1404_ok H1404_ok I1404_ok link1404 cenlink1404

/-! ### `N = 1405` -/

def pL1405 : Prm := ⟨79, 37, 39, 1407, 11, 18446744073709551616, 131234029286889810, 131234029286889810⟩
def pH1405 : Prm := ⟨79, 37, 39, 1407, 11, 18446744073709551616, 131235128798517586, 131235128798517586⟩
def pI1405 : Prm := ⟨65, 33, 29, 1407, 11, 18446744073709551616, 131234029286889810, 131235128798517586⟩
noncomputable def L1405_cp1 : Nat × Nat := t7val% (fastRun pL1405 1 992 (init pL1405) (init pL1405))
theorem L1405_seg1 : segOK pL1405 1 992 (init pL1405) (init pL1405) L1405_cp1.1 L1405_cp1.2 = true := by
  decide +kernel
theorem L1405_fin : (prmOK pL1405 1405 && ptTest pL1405 (runFrom pL1405 (fmask pL1405) (cmask pL1405) (hmask pL1405) 993 412 (true, L1405_cp1.1, L1405_cp1.2)) 1405 703 false) = true := by
  decide +kernel
theorem L1405_ok : RunOK pL1405 1405 (runFrom pL1405 (fmask pL1405) (cmask pL1405) (hmask pL1405) 993 412 (true, L1405_cp1.1, L1405_cp1.2)) ∧ ptTest pL1405 (runFrom pL1405 (fmask pL1405) (cmask pL1405) (hmask pL1405) 993 412 (true, L1405_cp1.1, L1405_cp1.2)) 1405 703 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1405_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1405_fin) true) L1405_seg1) (by decide) rfl L1405_fin ptTest_fst
noncomputable def H1405_cp1 : Nat × Nat := t7val% (fastRun pH1405 1 992 (init pH1405) (init pH1405))
theorem H1405_seg1 : segOK pH1405 1 992 (init pH1405) (init pH1405) H1405_cp1.1 H1405_cp1.2 = true := by
  decide +kernel
theorem H1405_fin : (prmOK pH1405 1405 && ptTest pH1405 (runFrom pH1405 (fmask pH1405) (cmask pH1405) (hmask pH1405) 993 412 (true, H1405_cp1.1, H1405_cp1.2)) 1405 703 true) = true := by
  decide +kernel
theorem H1405_ok : RunOK pH1405 1405 (runFrom pH1405 (fmask pH1405) (cmask pH1405) (hmask pH1405) 993 412 (true, H1405_cp1.1, H1405_cp1.2)) ∧ ptTest pH1405 (runFrom pH1405 (fmask pH1405) (cmask pH1405) (hmask pH1405) 993 412 (true, H1405_cp1.1, H1405_cp1.2)) 1405 703 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1405_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1405_fin) true) H1405_seg1) (by decide) rfl H1405_fin ptTest_fst
noncomputable def I1405_cp1 : Nat × Nat := t7val% (fastRun pI1405 1 992 (init pI1405) (init pI1405))
theorem I1405_seg1 : segOK pI1405 1 992 (init pI1405) (init pI1405) I1405_cp1.1 I1405_cp1.2 = true := by
  decide +kernel
theorem I1405_fin : (prmOK pI1405 1405 && intTest pI1405 (runFrom pI1405 (fmask pI1405) (cmask pI1405) (hmask pI1405) 993 412 (true, I1405_cp1.1, I1405_cp1.2)) 1405 20 false) = true := by
  decide +kernel
theorem I1405_ok : RunOK pI1405 1405 (runFrom pI1405 (fmask pI1405) (cmask pI1405) (hmask pI1405) 993 412 (true, I1405_cp1.1, I1405_cp1.2)) ∧ intTest pI1405 (runFrom pI1405 (fmask pI1405) (cmask pI1405) (hmask pI1405) 993 412 (true, I1405_cp1.1, I1405_cp1.2)) 1405 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1405_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1405_fin) true) I1405_seg1) (by decide) rfl I1405_fin intTest_fst
theorem link1405 : linkOK pL1405 pH1405 pI1405 = true := by decide +kernel
theorem cvx1405 : ConvexBetweenHumps 1405 :=
  cvx_of L1405_ok H1405_ok I1405_ok link1405 (by decide)

/-! ### `N = 1406` -/

def pL1406 : Prm := ⟨79, 37, 39, 1408, 11, 18446744073709551616, 131158313002913172, 131158313002913172⟩
def pH1406 : Prm := ⟨79, 37, 39, 1408, 11, 18446744073709551616, 131159412514540948, 131159412514540948⟩
def pI1406 : Prm := ⟨65, 33, 29, 1408, 11, 18446744073709551616, 131158313002913172, 131159412514540948⟩
noncomputable def L1406_cp1 : Nat × Nat := t7val% (fastRun pL1406 1 993 (init pL1406) (init pL1406))
theorem L1406_seg1 : segOK pL1406 1 993 (init pL1406) (init pL1406) L1406_cp1.1 L1406_cp1.2 = true := by
  decide +kernel
theorem L1406_fin : (prmOK pL1406 1406 && ptTest pL1406 (runFrom pL1406 (fmask pL1406) (cmask pL1406) (hmask pL1406) 994 412 (true, L1406_cp1.1, L1406_cp1.2)) 1406 703 false) = true := by
  decide +kernel
theorem L1406_ok : RunOK pL1406 1406 (runFrom pL1406 (fmask pL1406) (cmask pL1406) (hmask pL1406) 994 412 (true, L1406_cp1.1, L1406_cp1.2)) ∧ ptTest pL1406 (runFrom pL1406 (fmask pL1406) (cmask pL1406) (hmask pL1406) 994 412 (true, L1406_cp1.1, L1406_cp1.2)) 1406 703 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1406_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1406_fin) true) L1406_seg1) (by decide) rfl L1406_fin ptTest_fst
noncomputable def H1406_cp1 : Nat × Nat := t7val% (fastRun pH1406 1 993 (init pH1406) (init pH1406))
theorem H1406_seg1 : segOK pH1406 1 993 (init pH1406) (init pH1406) H1406_cp1.1 H1406_cp1.2 = true := by
  decide +kernel
theorem H1406_fin : (prmOK pH1406 1406 && ptTest pH1406 (runFrom pH1406 (fmask pH1406) (cmask pH1406) (hmask pH1406) 994 412 (true, H1406_cp1.1, H1406_cp1.2)) 1406 703 true) = true := by
  decide +kernel
theorem H1406_ok : RunOK pH1406 1406 (runFrom pH1406 (fmask pH1406) (cmask pH1406) (hmask pH1406) 994 412 (true, H1406_cp1.1, H1406_cp1.2)) ∧ ptTest pH1406 (runFrom pH1406 (fmask pH1406) (cmask pH1406) (hmask pH1406) 994 412 (true, H1406_cp1.1, H1406_cp1.2)) 1406 703 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1406_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1406_fin) true) H1406_seg1) (by decide) rfl H1406_fin ptTest_fst
noncomputable def I1406_cp1 : Nat × Nat := t7val% (fastRun pI1406 1 993 (init pI1406) (init pI1406))
theorem I1406_seg1 : segOK pI1406 1 993 (init pI1406) (init pI1406) I1406_cp1.1 I1406_cp1.2 = true := by
  decide +kernel
theorem I1406_fin : (prmOK pI1406 1406 && intTest pI1406 (runFrom pI1406 (fmask pI1406) (cmask pI1406) (hmask pI1406) 994 412 (true, I1406_cp1.1, I1406_cp1.2)) 1406 20 true) = true := by
  decide +kernel
theorem I1406_ok : RunOK pI1406 1406 (runFrom pI1406 (fmask pI1406) (cmask pI1406) (hmask pI1406) 994 412 (true, I1406_cp1.1, I1406_cp1.2)) ∧ intTest pI1406 (runFrom pI1406 (fmask pI1406) (cmask pI1406) (hmask pI1406) 994 412 (true, I1406_cp1.1, I1406_cp1.2)) 1406 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1406_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1406_fin) true) I1406_seg1) (by decide) rfl I1406_fin intTest_fst
theorem link1406 : linkOK pL1406 pH1406 pI1406 = true := by decide +kernel
theorem cvx1406 : ConvexBetweenHumps 1406 :=
  cvx_of L1406_ok H1406_ok I1406_ok link1406 (by decide)
theorem cenlink1406 : cenLinkOK pI1406 1406 = true := by decide +kernel
theorem cen1406 : CenterUniqueMin 1406 ∧ DipHyp 1406 ∧ OnePointHyps 1406 :=
  cen_of L1406_ok H1406_ok I1406_ok link1406 cenlink1406

/-! ### `N = 1407` -/

def pL1407 : Prm := ⟨79, 37, 39, 1409, 11, 18446744073709551616, 131082651000104284, 131082651000104284⟩
def pH1407 : Prm := ⟨79, 37, 39, 1409, 11, 18446744073709551616, 131083750511732060, 131083750511732060⟩
def pI1407 : Prm := ⟨65, 33, 29, 1409, 11, 18446744073709551616, 131082651000104284, 131083750511732060⟩
noncomputable def L1407_cp1 : Nat × Nat := t7val% (fastRun pL1407 1 994 (init pL1407) (init pL1407))
theorem L1407_seg1 : segOK pL1407 1 994 (init pL1407) (init pL1407) L1407_cp1.1 L1407_cp1.2 = true := by
  decide +kernel
theorem L1407_fin : (prmOK pL1407 1407 && ptTest pL1407 (runFrom pL1407 (fmask pL1407) (cmask pL1407) (hmask pL1407) 995 412 (true, L1407_cp1.1, L1407_cp1.2)) 1407 704 false) = true := by
  decide +kernel
theorem L1407_ok : RunOK pL1407 1407 (runFrom pL1407 (fmask pL1407) (cmask pL1407) (hmask pL1407) 995 412 (true, L1407_cp1.1, L1407_cp1.2)) ∧ ptTest pL1407 (runFrom pL1407 (fmask pL1407) (cmask pL1407) (hmask pL1407) 995 412 (true, L1407_cp1.1, L1407_cp1.2)) 1407 704 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1407_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1407_fin) true) L1407_seg1) (by decide) rfl L1407_fin ptTest_fst
noncomputable def H1407_cp1 : Nat × Nat := t7val% (fastRun pH1407 1 994 (init pH1407) (init pH1407))
theorem H1407_seg1 : segOK pH1407 1 994 (init pH1407) (init pH1407) H1407_cp1.1 H1407_cp1.2 = true := by
  decide +kernel
theorem H1407_fin : (prmOK pH1407 1407 && ptTest pH1407 (runFrom pH1407 (fmask pH1407) (cmask pH1407) (hmask pH1407) 995 412 (true, H1407_cp1.1, H1407_cp1.2)) 1407 704 true) = true := by
  decide +kernel
theorem H1407_ok : RunOK pH1407 1407 (runFrom pH1407 (fmask pH1407) (cmask pH1407) (hmask pH1407) 995 412 (true, H1407_cp1.1, H1407_cp1.2)) ∧ ptTest pH1407 (runFrom pH1407 (fmask pH1407) (cmask pH1407) (hmask pH1407) 995 412 (true, H1407_cp1.1, H1407_cp1.2)) 1407 704 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1407_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1407_fin) true) H1407_seg1) (by decide) rfl H1407_fin ptTest_fst
noncomputable def I1407_cp1 : Nat × Nat := t7val% (fastRun pI1407 1 994 (init pI1407) (init pI1407))
theorem I1407_seg1 : segOK pI1407 1 994 (init pI1407) (init pI1407) I1407_cp1.1 I1407_cp1.2 = true := by
  decide +kernel
theorem I1407_fin : (prmOK pI1407 1407 && intTest pI1407 (runFrom pI1407 (fmask pI1407) (cmask pI1407) (hmask pI1407) 995 412 (true, I1407_cp1.1, I1407_cp1.2)) 1407 20 false) = true := by
  decide +kernel
theorem I1407_ok : RunOK pI1407 1407 (runFrom pI1407 (fmask pI1407) (cmask pI1407) (hmask pI1407) 995 412 (true, I1407_cp1.1, I1407_cp1.2)) ∧ intTest pI1407 (runFrom pI1407 (fmask pI1407) (cmask pI1407) (hmask pI1407) 995 412 (true, I1407_cp1.1, I1407_cp1.2)) 1407 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1407_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1407_fin) true) I1407_seg1) (by decide) rfl I1407_fin intTest_fst
theorem link1407 : linkOK pL1407 pH1407 pI1407 = true := by decide +kernel
theorem cvx1407 : ConvexBetweenHumps 1407 :=
  cvx_of L1407_ok H1407_ok I1407_ok link1407 (by decide)

/-! ### `N = 1408` -/

def pL1408 : Prm := ⟨79, 37, 39, 1410, 11, 18446744073709551616, 131007124719288707, 131007124719288707⟩
def pH1408 : Prm := ⟨79, 37, 39, 1410, 11, 18446744073709551616, 131008224230916483, 131008224230916483⟩
def pI1408 : Prm := ⟨65, 33, 29, 1410, 11, 18446744073709551616, 131007124719288707, 131008224230916483⟩
noncomputable def L1408_cp1 : Nat × Nat := t7val% (fastRun pL1408 1 995 (init pL1408) (init pL1408))
theorem L1408_seg1 : segOK pL1408 1 995 (init pL1408) (init pL1408) L1408_cp1.1 L1408_cp1.2 = true := by
  decide +kernel
theorem L1408_fin : (prmOK pL1408 1408 && ptTest pL1408 (runFrom pL1408 (fmask pL1408) (cmask pL1408) (hmask pL1408) 996 412 (true, L1408_cp1.1, L1408_cp1.2)) 1408 704 false) = true := by
  decide +kernel
theorem L1408_ok : RunOK pL1408 1408 (runFrom pL1408 (fmask pL1408) (cmask pL1408) (hmask pL1408) 996 412 (true, L1408_cp1.1, L1408_cp1.2)) ∧ ptTest pL1408 (runFrom pL1408 (fmask pL1408) (cmask pL1408) (hmask pL1408) 996 412 (true, L1408_cp1.1, L1408_cp1.2)) 1408 704 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1408_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1408_fin) true) L1408_seg1) (by decide) rfl L1408_fin ptTest_fst
noncomputable def H1408_cp1 : Nat × Nat := t7val% (fastRun pH1408 1 995 (init pH1408) (init pH1408))
theorem H1408_seg1 : segOK pH1408 1 995 (init pH1408) (init pH1408) H1408_cp1.1 H1408_cp1.2 = true := by
  decide +kernel
theorem H1408_fin : (prmOK pH1408 1408 && ptTest pH1408 (runFrom pH1408 (fmask pH1408) (cmask pH1408) (hmask pH1408) 996 412 (true, H1408_cp1.1, H1408_cp1.2)) 1408 704 true) = true := by
  decide +kernel
theorem H1408_ok : RunOK pH1408 1408 (runFrom pH1408 (fmask pH1408) (cmask pH1408) (hmask pH1408) 996 412 (true, H1408_cp1.1, H1408_cp1.2)) ∧ ptTest pH1408 (runFrom pH1408 (fmask pH1408) (cmask pH1408) (hmask pH1408) 996 412 (true, H1408_cp1.1, H1408_cp1.2)) 1408 704 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1408_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1408_fin) true) H1408_seg1) (by decide) rfl H1408_fin ptTest_fst
noncomputable def I1408_cp1 : Nat × Nat := t7val% (fastRun pI1408 1 995 (init pI1408) (init pI1408))
theorem I1408_seg1 : segOK pI1408 1 995 (init pI1408) (init pI1408) I1408_cp1.1 I1408_cp1.2 = true := by
  decide +kernel
theorem I1408_fin : (prmOK pI1408 1408 && intTest pI1408 (runFrom pI1408 (fmask pI1408) (cmask pI1408) (hmask pI1408) 996 412 (true, I1408_cp1.1, I1408_cp1.2)) 1408 20 true) = true := by
  decide +kernel
theorem I1408_ok : RunOK pI1408 1408 (runFrom pI1408 (fmask pI1408) (cmask pI1408) (hmask pI1408) 996 412 (true, I1408_cp1.1, I1408_cp1.2)) ∧ intTest pI1408 (runFrom pI1408 (fmask pI1408) (cmask pI1408) (hmask pI1408) 996 412 (true, I1408_cp1.1, I1408_cp1.2)) 1408 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1408_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1408_fin) true) I1408_seg1) (by decide) rfl I1408_fin intTest_fst
theorem link1408 : linkOK pL1408 pH1408 pI1408 = true := by decide +kernel
theorem cvx1408 : ConvexBetweenHumps 1408 :=
  cvx_of L1408_ok H1408_ok I1408_ok link1408 (by decide)
theorem cenlink1408 : cenLinkOK pI1408 1408 = true := by decide +kernel
theorem cen1408 : CenterUniqueMin 1408 ∧ DipHyp 1408 ∧ OnePointHyps 1408 :=
  cen_of L1408_ok H1408_ok I1408_ok link1408 cenlink1408

/-! ### `N = 1409` -/

def pL1409 : Prm := ⟨79, 37, 39, 1411, 11, 18446744073709551616, 130931652526983083, 130931652526983083⟩
def pH1409 : Prm := ⟨79, 37, 39, 1411, 11, 18446744073709551616, 130932752038610859, 130932752038610859⟩
def pI1409 : Prm := ⟨65, 33, 29, 1411, 11, 18446744073709551616, 130931652526983083, 130932752038610859⟩
noncomputable def L1409_cp1 : Nat × Nat := t7val% (fastRun pL1409 1 995 (init pL1409) (init pL1409))
theorem L1409_seg1 : segOK pL1409 1 995 (init pL1409) (init pL1409) L1409_cp1.1 L1409_cp1.2 = true := by
  decide +kernel
theorem L1409_fin : (prmOK pL1409 1409 && ptTest pL1409 (runFrom pL1409 (fmask pL1409) (cmask pL1409) (hmask pL1409) 996 413 (true, L1409_cp1.1, L1409_cp1.2)) 1409 705 false) = true := by
  decide +kernel
theorem L1409_ok : RunOK pL1409 1409 (runFrom pL1409 (fmask pL1409) (cmask pL1409) (hmask pL1409) 996 413 (true, L1409_cp1.1, L1409_cp1.2)) ∧ ptTest pL1409 (runFrom pL1409 (fmask pL1409) (cmask pL1409) (hmask pL1409) 996 413 (true, L1409_cp1.1, L1409_cp1.2)) 1409 705 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1409_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1409_fin) true) L1409_seg1) (by decide) rfl L1409_fin ptTest_fst
noncomputable def H1409_cp1 : Nat × Nat := t7val% (fastRun pH1409 1 995 (init pH1409) (init pH1409))
theorem H1409_seg1 : segOK pH1409 1 995 (init pH1409) (init pH1409) H1409_cp1.1 H1409_cp1.2 = true := by
  decide +kernel
theorem H1409_fin : (prmOK pH1409 1409 && ptTest pH1409 (runFrom pH1409 (fmask pH1409) (cmask pH1409) (hmask pH1409) 996 413 (true, H1409_cp1.1, H1409_cp1.2)) 1409 705 true) = true := by
  decide +kernel
theorem H1409_ok : RunOK pH1409 1409 (runFrom pH1409 (fmask pH1409) (cmask pH1409) (hmask pH1409) 996 413 (true, H1409_cp1.1, H1409_cp1.2)) ∧ ptTest pH1409 (runFrom pH1409 (fmask pH1409) (cmask pH1409) (hmask pH1409) 996 413 (true, H1409_cp1.1, H1409_cp1.2)) 1409 705 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1409_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1409_fin) true) H1409_seg1) (by decide) rfl H1409_fin ptTest_fst
noncomputable def I1409_cp1 : Nat × Nat := t7val% (fastRun pI1409 1 995 (init pI1409) (init pI1409))
theorem I1409_seg1 : segOK pI1409 1 995 (init pI1409) (init pI1409) I1409_cp1.1 I1409_cp1.2 = true := by
  decide +kernel
theorem I1409_fin : (prmOK pI1409 1409 && intTest pI1409 (runFrom pI1409 (fmask pI1409) (cmask pI1409) (hmask pI1409) 996 413 (true, I1409_cp1.1, I1409_cp1.2)) 1409 20 false) = true := by
  decide +kernel
theorem I1409_ok : RunOK pI1409 1409 (runFrom pI1409 (fmask pI1409) (cmask pI1409) (hmask pI1409) 996 413 (true, I1409_cp1.1, I1409_cp1.2)) ∧ intTest pI1409 (runFrom pI1409 (fmask pI1409) (cmask pI1409) (hmask pI1409) 996 413 (true, I1409_cp1.1, I1409_cp1.2)) 1409 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1409_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1409_fin) true) I1409_seg1) (by decide) rfl I1409_fin intTest_fst
theorem link1409 : linkOK pL1409 pH1409 pI1409 = true := by decide +kernel
theorem cvx1409 : ConvexBetweenHumps 1409 :=
  cvx_of L1409_ok H1409_ok I1409_ok link1409 (by decide)

/-! ### `N = 1410` -/

def pL1410 : Prm := ⟨79, 37, 39, 1412, 11, 18446744073709551616, 130856315511993758, 130856315511993758⟩
def pH1410 : Prm := ⟨79, 37, 39, 1412, 11, 18446744073709551616, 130857415023621534, 130857415023621534⟩
def pI1410 : Prm := ⟨65, 33, 29, 1412, 11, 18446744073709551616, 130856315511993758, 130857415023621534⟩
noncomputable def L1410_cp1 : Nat × Nat := t7val% (fastRun pL1410 1 996 (init pL1410) (init pL1410))
theorem L1410_seg1 : segOK pL1410 1 996 (init pL1410) (init pL1410) L1410_cp1.1 L1410_cp1.2 = true := by
  decide +kernel
theorem L1410_fin : (prmOK pL1410 1410 && ptTest pL1410 (runFrom pL1410 (fmask pL1410) (cmask pL1410) (hmask pL1410) 997 413 (true, L1410_cp1.1, L1410_cp1.2)) 1410 705 false) = true := by
  decide +kernel
theorem L1410_ok : RunOK pL1410 1410 (runFrom pL1410 (fmask pL1410) (cmask pL1410) (hmask pL1410) 997 413 (true, L1410_cp1.1, L1410_cp1.2)) ∧ ptTest pL1410 (runFrom pL1410 (fmask pL1410) (cmask pL1410) (hmask pL1410) 997 413 (true, L1410_cp1.1, L1410_cp1.2)) 1410 705 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1410_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1410_fin) true) L1410_seg1) (by decide) rfl L1410_fin ptTest_fst
noncomputable def H1410_cp1 : Nat × Nat := t7val% (fastRun pH1410 1 996 (init pH1410) (init pH1410))
theorem H1410_seg1 : segOK pH1410 1 996 (init pH1410) (init pH1410) H1410_cp1.1 H1410_cp1.2 = true := by
  decide +kernel
theorem H1410_fin : (prmOK pH1410 1410 && ptTest pH1410 (runFrom pH1410 (fmask pH1410) (cmask pH1410) (hmask pH1410) 997 413 (true, H1410_cp1.1, H1410_cp1.2)) 1410 705 true) = true := by
  decide +kernel
theorem H1410_ok : RunOK pH1410 1410 (runFrom pH1410 (fmask pH1410) (cmask pH1410) (hmask pH1410) 997 413 (true, H1410_cp1.1, H1410_cp1.2)) ∧ ptTest pH1410 (runFrom pH1410 (fmask pH1410) (cmask pH1410) (hmask pH1410) 997 413 (true, H1410_cp1.1, H1410_cp1.2)) 1410 705 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1410_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1410_fin) true) H1410_seg1) (by decide) rfl H1410_fin ptTest_fst
noncomputable def I1410_cp1 : Nat × Nat := t7val% (fastRun pI1410 1 996 (init pI1410) (init pI1410))
theorem I1410_seg1 : segOK pI1410 1 996 (init pI1410) (init pI1410) I1410_cp1.1 I1410_cp1.2 = true := by
  decide +kernel
theorem I1410_fin : (prmOK pI1410 1410 && intTest pI1410 (runFrom pI1410 (fmask pI1410) (cmask pI1410) (hmask pI1410) 997 413 (true, I1410_cp1.1, I1410_cp1.2)) 1410 20 true) = true := by
  decide +kernel
theorem I1410_ok : RunOK pI1410 1410 (runFrom pI1410 (fmask pI1410) (cmask pI1410) (hmask pI1410) 997 413 (true, I1410_cp1.1, I1410_cp1.2)) ∧ intTest pI1410 (runFrom pI1410 (fmask pI1410) (cmask pI1410) (hmask pI1410) 997 413 (true, I1410_cp1.1, I1410_cp1.2)) 1410 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1410_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1410_fin) true) I1410_seg1) (by decide) rfl I1410_fin intTest_fst
theorem link1410 : linkOK pL1410 pH1410 pI1410 = true := by decide +kernel
theorem cvx1410 : ConvexBetweenHumps 1410 :=
  cvx_of L1410_ok H1410_ok I1410_ok link1410 (by decide)
theorem cenlink1410 : cenLinkOK pI1410 1410 = true := by decide +kernel
theorem cen1410 : CenterUniqueMin 1410 ∧ DipHyp 1410 ∧ OnePointHyps 1410 :=
  cen_of L1410_ok H1410_ok I1410_ok link1410 cenlink1410

/-! ### `N = 1411` -/

def pL1411 : Prm := ⟨79, 37, 39, 1413, 11, 18446744073709551616, 130781032393760483, 130781032393760483⟩
def pH1411 : Prm := ⟨79, 37, 39, 1413, 11, 18446744073709551616, 130782131905388259, 130782131905388259⟩
def pI1411 : Prm := ⟨65, 33, 29, 1413, 11, 18446744073709551616, 130781032393760483, 130782131905388259⟩
noncomputable def L1411_cp1 : Nat × Nat := t7val% (fastRun pL1411 1 997 (init pL1411) (init pL1411))
theorem L1411_seg1 : segOK pL1411 1 997 (init pL1411) (init pL1411) L1411_cp1.1 L1411_cp1.2 = true := by
  decide +kernel
theorem L1411_fin : (prmOK pL1411 1411 && ptTest pL1411 (runFrom pL1411 (fmask pL1411) (cmask pL1411) (hmask pL1411) 998 413 (true, L1411_cp1.1, L1411_cp1.2)) 1411 706 false) = true := by
  decide +kernel
theorem L1411_ok : RunOK pL1411 1411 (runFrom pL1411 (fmask pL1411) (cmask pL1411) (hmask pL1411) 998 413 (true, L1411_cp1.1, L1411_cp1.2)) ∧ ptTest pL1411 (runFrom pL1411 (fmask pL1411) (cmask pL1411) (hmask pL1411) 998 413 (true, L1411_cp1.1, L1411_cp1.2)) 1411 706 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1411_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1411_fin) true) L1411_seg1) (by decide) rfl L1411_fin ptTest_fst
noncomputable def H1411_cp1 : Nat × Nat := t7val% (fastRun pH1411 1 997 (init pH1411) (init pH1411))
theorem H1411_seg1 : segOK pH1411 1 997 (init pH1411) (init pH1411) H1411_cp1.1 H1411_cp1.2 = true := by
  decide +kernel
theorem H1411_fin : (prmOK pH1411 1411 && ptTest pH1411 (runFrom pH1411 (fmask pH1411) (cmask pH1411) (hmask pH1411) 998 413 (true, H1411_cp1.1, H1411_cp1.2)) 1411 706 true) = true := by
  decide +kernel
theorem H1411_ok : RunOK pH1411 1411 (runFrom pH1411 (fmask pH1411) (cmask pH1411) (hmask pH1411) 998 413 (true, H1411_cp1.1, H1411_cp1.2)) ∧ ptTest pH1411 (runFrom pH1411 (fmask pH1411) (cmask pH1411) (hmask pH1411) 998 413 (true, H1411_cp1.1, H1411_cp1.2)) 1411 706 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1411_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1411_fin) true) H1411_seg1) (by decide) rfl H1411_fin ptTest_fst
noncomputable def I1411_cp1 : Nat × Nat := t7val% (fastRun pI1411 1 997 (init pI1411) (init pI1411))
theorem I1411_seg1 : segOK pI1411 1 997 (init pI1411) (init pI1411) I1411_cp1.1 I1411_cp1.2 = true := by
  decide +kernel
theorem I1411_fin : (prmOK pI1411 1411 && intTest pI1411 (runFrom pI1411 (fmask pI1411) (cmask pI1411) (hmask pI1411) 998 413 (true, I1411_cp1.1, I1411_cp1.2)) 1411 20 false) = true := by
  decide +kernel
theorem I1411_ok : RunOK pI1411 1411 (runFrom pI1411 (fmask pI1411) (cmask pI1411) (hmask pI1411) 998 413 (true, I1411_cp1.1, I1411_cp1.2)) ∧ intTest pI1411 (runFrom pI1411 (fmask pI1411) (cmask pI1411) (hmask pI1411) 998 413 (true, I1411_cp1.1, I1411_cp1.2)) 1411 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1411_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1411_fin) true) I1411_seg1) (by decide) rfl I1411_fin intTest_fst
theorem link1411 : linkOK pL1411 pH1411 pI1411 = true := by decide +kernel
theorem cvx1411 : ConvexBetweenHumps 1411 :=
  cvx_of L1411_ok H1411_ok I1411_ok link1411 (by decide)

/-! ### `N = 1412` -/

def pL1412 : Prm := ⟨79, 37, 39, 1414, 11, 18446744073709551616, 130705883911154865, 130705883911154865⟩
def pH1412 : Prm := ⟨79, 37, 39, 1414, 11, 18446744073709551616, 130706983422782641, 130706983422782641⟩
def pI1412 : Prm := ⟨65, 33, 29, 1414, 11, 18446744073709551616, 130705883911154865, 130706983422782641⟩
noncomputable def L1412_cp1 : Nat × Nat := t7val% (fastRun pL1412 1 997 (init pL1412) (init pL1412))
theorem L1412_seg1 : segOK pL1412 1 997 (init pL1412) (init pL1412) L1412_cp1.1 L1412_cp1.2 = true := by
  decide +kernel
theorem L1412_fin : (prmOK pL1412 1412 && ptTest pL1412 (runFrom pL1412 (fmask pL1412) (cmask pL1412) (hmask pL1412) 998 414 (true, L1412_cp1.1, L1412_cp1.2)) 1412 706 false) = true := by
  decide +kernel
theorem L1412_ok : RunOK pL1412 1412 (runFrom pL1412 (fmask pL1412) (cmask pL1412) (hmask pL1412) 998 414 (true, L1412_cp1.1, L1412_cp1.2)) ∧ ptTest pL1412 (runFrom pL1412 (fmask pL1412) (cmask pL1412) (hmask pL1412) 998 414 (true, L1412_cp1.1, L1412_cp1.2)) 1412 706 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1412_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1412_fin) true) L1412_seg1) (by decide) rfl L1412_fin ptTest_fst
noncomputable def H1412_cp1 : Nat × Nat := t7val% (fastRun pH1412 1 997 (init pH1412) (init pH1412))
theorem H1412_seg1 : segOK pH1412 1 997 (init pH1412) (init pH1412) H1412_cp1.1 H1412_cp1.2 = true := by
  decide +kernel
theorem H1412_fin : (prmOK pH1412 1412 && ptTest pH1412 (runFrom pH1412 (fmask pH1412) (cmask pH1412) (hmask pH1412) 998 414 (true, H1412_cp1.1, H1412_cp1.2)) 1412 706 true) = true := by
  decide +kernel
theorem H1412_ok : RunOK pH1412 1412 (runFrom pH1412 (fmask pH1412) (cmask pH1412) (hmask pH1412) 998 414 (true, H1412_cp1.1, H1412_cp1.2)) ∧ ptTest pH1412 (runFrom pH1412 (fmask pH1412) (cmask pH1412) (hmask pH1412) 998 414 (true, H1412_cp1.1, H1412_cp1.2)) 1412 706 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1412_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1412_fin) true) H1412_seg1) (by decide) rfl H1412_fin ptTest_fst
noncomputable def I1412_cp1 : Nat × Nat := t7val% (fastRun pI1412 1 997 (init pI1412) (init pI1412))
theorem I1412_seg1 : segOK pI1412 1 997 (init pI1412) (init pI1412) I1412_cp1.1 I1412_cp1.2 = true := by
  decide +kernel
theorem I1412_fin : (prmOK pI1412 1412 && intTest pI1412 (runFrom pI1412 (fmask pI1412) (cmask pI1412) (hmask pI1412) 998 414 (true, I1412_cp1.1, I1412_cp1.2)) 1412 20 true) = true := by
  decide +kernel
theorem I1412_ok : RunOK pI1412 1412 (runFrom pI1412 (fmask pI1412) (cmask pI1412) (hmask pI1412) 998 414 (true, I1412_cp1.1, I1412_cp1.2)) ∧ intTest pI1412 (runFrom pI1412 (fmask pI1412) (cmask pI1412) (hmask pI1412) 998 414 (true, I1412_cp1.1, I1412_cp1.2)) 1412 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1412_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1412_fin) true) I1412_seg1) (by decide) rfl I1412_fin intTest_fst
theorem link1412 : linkOK pL1412 pH1412 pI1412 = true := by decide +kernel
theorem cvx1412 : ConvexBetweenHumps 1412 :=
  cvx_of L1412_ok H1412_ok I1412_ok link1412 (by decide)
theorem cenlink1412 : cenLinkOK pI1412 1412 = true := by decide +kernel
theorem cen1412 : CenterUniqueMin 1412 ∧ DipHyp 1412 ∧ OnePointHyps 1412 :=
  cen_of L1412_ok H1412_ok I1412_ok link1412 cenlink1412

/-! ### `N = 1413` -/

def pL1413 : Prm := ⟨79, 37, 39, 1415, 11, 18446744073709551616, 130630789134473730, 130630789134473730⟩
def pH1413 : Prm := ⟨79, 37, 39, 1415, 11, 18446744073709551616, 130631888646101506, 130631888646101506⟩
def pI1413 : Prm := ⟨65, 33, 29, 1415, 11, 18446744073709551616, 130630789134473730, 130631888646101506⟩
noncomputable def L1413_cp1 : Nat × Nat := t7val% (fastRun pL1413 1 998 (init pL1413) (init pL1413))
theorem L1413_seg1 : segOK pL1413 1 998 (init pL1413) (init pL1413) L1413_cp1.1 L1413_cp1.2 = true := by
  decide +kernel
theorem L1413_fin : (prmOK pL1413 1413 && ptTest pL1413 (runFrom pL1413 (fmask pL1413) (cmask pL1413) (hmask pL1413) 999 414 (true, L1413_cp1.1, L1413_cp1.2)) 1413 707 false) = true := by
  decide +kernel
theorem L1413_ok : RunOK pL1413 1413 (runFrom pL1413 (fmask pL1413) (cmask pL1413) (hmask pL1413) 999 414 (true, L1413_cp1.1, L1413_cp1.2)) ∧ ptTest pL1413 (runFrom pL1413 (fmask pL1413) (cmask pL1413) (hmask pL1413) 999 414 (true, L1413_cp1.1, L1413_cp1.2)) 1413 707 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1413_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1413_fin) true) L1413_seg1) (by decide) rfl L1413_fin ptTest_fst
noncomputable def H1413_cp1 : Nat × Nat := t7val% (fastRun pH1413 1 998 (init pH1413) (init pH1413))
theorem H1413_seg1 : segOK pH1413 1 998 (init pH1413) (init pH1413) H1413_cp1.1 H1413_cp1.2 = true := by
  decide +kernel
theorem H1413_fin : (prmOK pH1413 1413 && ptTest pH1413 (runFrom pH1413 (fmask pH1413) (cmask pH1413) (hmask pH1413) 999 414 (true, H1413_cp1.1, H1413_cp1.2)) 1413 707 true) = true := by
  decide +kernel
theorem H1413_ok : RunOK pH1413 1413 (runFrom pH1413 (fmask pH1413) (cmask pH1413) (hmask pH1413) 999 414 (true, H1413_cp1.1, H1413_cp1.2)) ∧ ptTest pH1413 (runFrom pH1413 (fmask pH1413) (cmask pH1413) (hmask pH1413) 999 414 (true, H1413_cp1.1, H1413_cp1.2)) 1413 707 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1413_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1413_fin) true) H1413_seg1) (by decide) rfl H1413_fin ptTest_fst
noncomputable def I1413_cp1 : Nat × Nat := t7val% (fastRun pI1413 1 998 (init pI1413) (init pI1413))
theorem I1413_seg1 : segOK pI1413 1 998 (init pI1413) (init pI1413) I1413_cp1.1 I1413_cp1.2 = true := by
  decide +kernel
theorem I1413_fin : (prmOK pI1413 1413 && intTest pI1413 (runFrom pI1413 (fmask pI1413) (cmask pI1413) (hmask pI1413) 999 414 (true, I1413_cp1.1, I1413_cp1.2)) 1413 20 false) = true := by
  decide +kernel
theorem I1413_ok : RunOK pI1413 1413 (runFrom pI1413 (fmask pI1413) (cmask pI1413) (hmask pI1413) 999 414 (true, I1413_cp1.1, I1413_cp1.2)) ∧ intTest pI1413 (runFrom pI1413 (fmask pI1413) (cmask pI1413) (hmask pI1413) 999 414 (true, I1413_cp1.1, I1413_cp1.2)) 1413 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1413_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1413_fin) true) I1413_seg1) (by decide) rfl I1413_fin intTest_fst
theorem link1413 : linkOK pL1413 pH1413 pI1413 = true := by decide +kernel
theorem cvx1413 : ConvexBetweenHumps 1413 :=
  cvx_of L1413_ok H1413_ok I1413_ok link1413 (by decide)

/-! ### `N = 1414` -/

def pL1414 : Prm := ⟨79, 37, 39, 1416, 11, 18446744073709551616, 130555828454664646, 130555828454664646⟩
def pH1414 : Prm := ⟨79, 37, 39, 1416, 11, 18446744073709551616, 130556927966292422, 130556927966292422⟩
def pI1414 : Prm := ⟨65, 33, 29, 1416, 11, 18446744073709551616, 130555828454664646, 130556927966292422⟩
noncomputable def L1414_cp1 : Nat × Nat := t7val% (fastRun pL1414 1 999 (init pL1414) (init pL1414))
theorem L1414_seg1 : segOK pL1414 1 999 (init pL1414) (init pL1414) L1414_cp1.1 L1414_cp1.2 = true := by
  decide +kernel
theorem L1414_fin : (prmOK pL1414 1414 && ptTest pL1414 (runFrom pL1414 (fmask pL1414) (cmask pL1414) (hmask pL1414) 1000 414 (true, L1414_cp1.1, L1414_cp1.2)) 1414 707 false) = true := by
  decide +kernel
theorem L1414_ok : RunOK pL1414 1414 (runFrom pL1414 (fmask pL1414) (cmask pL1414) (hmask pL1414) 1000 414 (true, L1414_cp1.1, L1414_cp1.2)) ∧ ptTest pL1414 (runFrom pL1414 (fmask pL1414) (cmask pL1414) (hmask pL1414) 1000 414 (true, L1414_cp1.1, L1414_cp1.2)) 1414 707 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1414_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1414_fin) true) L1414_seg1) (by decide) rfl L1414_fin ptTest_fst
noncomputable def H1414_cp1 : Nat × Nat := t7val% (fastRun pH1414 1 999 (init pH1414) (init pH1414))
theorem H1414_seg1 : segOK pH1414 1 999 (init pH1414) (init pH1414) H1414_cp1.1 H1414_cp1.2 = true := by
  decide +kernel
theorem H1414_fin : (prmOK pH1414 1414 && ptTest pH1414 (runFrom pH1414 (fmask pH1414) (cmask pH1414) (hmask pH1414) 1000 414 (true, H1414_cp1.1, H1414_cp1.2)) 1414 707 true) = true := by
  decide +kernel
theorem H1414_ok : RunOK pH1414 1414 (runFrom pH1414 (fmask pH1414) (cmask pH1414) (hmask pH1414) 1000 414 (true, H1414_cp1.1, H1414_cp1.2)) ∧ ptTest pH1414 (runFrom pH1414 (fmask pH1414) (cmask pH1414) (hmask pH1414) 1000 414 (true, H1414_cp1.1, H1414_cp1.2)) 1414 707 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1414_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1414_fin) true) H1414_seg1) (by decide) rfl H1414_fin ptTest_fst
noncomputable def I1414_cp1 : Nat × Nat := t7val% (fastRun pI1414 1 999 (init pI1414) (init pI1414))
theorem I1414_seg1 : segOK pI1414 1 999 (init pI1414) (init pI1414) I1414_cp1.1 I1414_cp1.2 = true := by
  decide +kernel
theorem I1414_fin : (prmOK pI1414 1414 && intTest pI1414 (runFrom pI1414 (fmask pI1414) (cmask pI1414) (hmask pI1414) 1000 414 (true, I1414_cp1.1, I1414_cp1.2)) 1414 20 true) = true := by
  decide +kernel
theorem I1414_ok : RunOK pI1414 1414 (runFrom pI1414 (fmask pI1414) (cmask pI1414) (hmask pI1414) 1000 414 (true, I1414_cp1.1, I1414_cp1.2)) ∧ intTest pI1414 (runFrom pI1414 (fmask pI1414) (cmask pI1414) (hmask pI1414) 1000 414 (true, I1414_cp1.1, I1414_cp1.2)) 1414 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1414_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1414_fin) true) I1414_seg1) (by decide) rfl I1414_fin intTest_fst
theorem link1414 : linkOK pL1414 pH1414 pI1414 = true := by decide +kernel
theorem cvx1414 : ConvexBetweenHumps 1414 :=
  cvx_of L1414_ok H1414_ok I1414_ok link1414 (by decide)
theorem cenlink1414 : cenLinkOK pI1414 1414 = true := by decide +kernel
theorem cen1414 : CenterUniqueMin 1414 ∧ DipHyp 1414 ∧ OnePointHyps 1414 :=
  cen_of L1414_ok H1414_ok I1414_ok link1414 cenlink1414

/-! ### `N = 1415` -/

def pL1415 : Prm := ⟨79, 37, 39, 1417, 11, 18446744073709551616, 130480921290852367, 130480921290852367⟩
def pH1415 : Prm := ⟨79, 37, 39, 1417, 11, 18446744073709551616, 130482020802480143, 130482020802480143⟩
def pI1415 : Prm := ⟨65, 33, 29, 1417, 11, 18446744073709551616, 130480921290852367, 130482020802480143⟩
noncomputable def L1415_cp1 : Nat × Nat := t7val% (fastRun pL1415 1 1000 (init pL1415) (init pL1415))
theorem L1415_seg1 : segOK pL1415 1 1000 (init pL1415) (init pL1415) L1415_cp1.1 L1415_cp1.2 = true := by
  decide +kernel
theorem L1415_fin : (prmOK pL1415 1415 && ptTest pL1415 (runFrom pL1415 (fmask pL1415) (cmask pL1415) (hmask pL1415) 1001 414 (true, L1415_cp1.1, L1415_cp1.2)) 1415 708 false) = true := by
  decide +kernel
theorem L1415_ok : RunOK pL1415 1415 (runFrom pL1415 (fmask pL1415) (cmask pL1415) (hmask pL1415) 1001 414 (true, L1415_cp1.1, L1415_cp1.2)) ∧ ptTest pL1415 (runFrom pL1415 (fmask pL1415) (cmask pL1415) (hmask pL1415) 1001 414 (true, L1415_cp1.1, L1415_cp1.2)) 1415 708 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1415_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1415_fin) true) L1415_seg1) (by decide) rfl L1415_fin ptTest_fst
noncomputable def H1415_cp1 : Nat × Nat := t7val% (fastRun pH1415 1 1000 (init pH1415) (init pH1415))
theorem H1415_seg1 : segOK pH1415 1 1000 (init pH1415) (init pH1415) H1415_cp1.1 H1415_cp1.2 = true := by
  decide +kernel
theorem H1415_fin : (prmOK pH1415 1415 && ptTest pH1415 (runFrom pH1415 (fmask pH1415) (cmask pH1415) (hmask pH1415) 1001 414 (true, H1415_cp1.1, H1415_cp1.2)) 1415 708 true) = true := by
  decide +kernel
theorem H1415_ok : RunOK pH1415 1415 (runFrom pH1415 (fmask pH1415) (cmask pH1415) (hmask pH1415) 1001 414 (true, H1415_cp1.1, H1415_cp1.2)) ∧ ptTest pH1415 (runFrom pH1415 (fmask pH1415) (cmask pH1415) (hmask pH1415) 1001 414 (true, H1415_cp1.1, H1415_cp1.2)) 1415 708 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1415_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1415_fin) true) H1415_seg1) (by decide) rfl H1415_fin ptTest_fst
noncomputable def I1415_cp1 : Nat × Nat := t7val% (fastRun pI1415 1 1000 (init pI1415) (init pI1415))
theorem I1415_seg1 : segOK pI1415 1 1000 (init pI1415) (init pI1415) I1415_cp1.1 I1415_cp1.2 = true := by
  decide +kernel
theorem I1415_fin : (prmOK pI1415 1415 && intTest pI1415 (runFrom pI1415 (fmask pI1415) (cmask pI1415) (hmask pI1415) 1001 414 (true, I1415_cp1.1, I1415_cp1.2)) 1415 20 false) = true := by
  decide +kernel
theorem I1415_ok : RunOK pI1415 1415 (runFrom pI1415 (fmask pI1415) (cmask pI1415) (hmask pI1415) 1001 414 (true, I1415_cp1.1, I1415_cp1.2)) ∧ intTest pI1415 (runFrom pI1415 (fmask pI1415) (cmask pI1415) (hmask pI1415) 1001 414 (true, I1415_cp1.1, I1415_cp1.2)) 1415 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1415_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1415_fin) true) I1415_seg1) (by decide) rfl I1415_fin intTest_fst
theorem link1415 : linkOK pL1415 pH1415 pI1415 = true := by decide +kernel
theorem cvx1415 : ConvexBetweenHumps 1415 :=
  cvx_of L1415_ok H1415_ok I1415_ok link1415 (by decide)

/-! ### `N = 1416` -/

def pL1416 : Prm := ⟨79, 37, 39, 1418, 11, 18446744073709551616, 130406147688034223, 130406147688034223⟩
def pH1416 : Prm := ⟨79, 37, 39, 1418, 11, 18446744073709551616, 130407247199661999, 130407247199661999⟩
def pI1416 : Prm := ⟨65, 33, 29, 1418, 11, 18446744073709551616, 130406147688034223, 130407247199661999⟩
noncomputable def L1416_cp1 : Nat × Nat := t7val% (fastRun pL1416 1 1000 (init pL1416) (init pL1416))
theorem L1416_seg1 : segOK pL1416 1 1000 (init pL1416) (init pL1416) L1416_cp1.1 L1416_cp1.2 = true := by
  decide +kernel
theorem L1416_fin : (prmOK pL1416 1416 && ptTest pL1416 (runFrom pL1416 (fmask pL1416) (cmask pL1416) (hmask pL1416) 1001 415 (true, L1416_cp1.1, L1416_cp1.2)) 1416 708 false) = true := by
  decide +kernel
theorem L1416_ok : RunOK pL1416 1416 (runFrom pL1416 (fmask pL1416) (cmask pL1416) (hmask pL1416) 1001 415 (true, L1416_cp1.1, L1416_cp1.2)) ∧ ptTest pL1416 (runFrom pL1416 (fmask pL1416) (cmask pL1416) (hmask pL1416) 1001 415 (true, L1416_cp1.1, L1416_cp1.2)) 1416 708 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1416_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1416_fin) true) L1416_seg1) (by decide) rfl L1416_fin ptTest_fst
noncomputable def H1416_cp1 : Nat × Nat := t7val% (fastRun pH1416 1 1000 (init pH1416) (init pH1416))
theorem H1416_seg1 : segOK pH1416 1 1000 (init pH1416) (init pH1416) H1416_cp1.1 H1416_cp1.2 = true := by
  decide +kernel
theorem H1416_fin : (prmOK pH1416 1416 && ptTest pH1416 (runFrom pH1416 (fmask pH1416) (cmask pH1416) (hmask pH1416) 1001 415 (true, H1416_cp1.1, H1416_cp1.2)) 1416 708 true) = true := by
  decide +kernel
theorem H1416_ok : RunOK pH1416 1416 (runFrom pH1416 (fmask pH1416) (cmask pH1416) (hmask pH1416) 1001 415 (true, H1416_cp1.1, H1416_cp1.2)) ∧ ptTest pH1416 (runFrom pH1416 (fmask pH1416) (cmask pH1416) (hmask pH1416) 1001 415 (true, H1416_cp1.1, H1416_cp1.2)) 1416 708 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1416_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1416_fin) true) H1416_seg1) (by decide) rfl H1416_fin ptTest_fst
noncomputable def I1416_cp1 : Nat × Nat := t7val% (fastRun pI1416 1 1000 (init pI1416) (init pI1416))
theorem I1416_seg1 : segOK pI1416 1 1000 (init pI1416) (init pI1416) I1416_cp1.1 I1416_cp1.2 = true := by
  decide +kernel
theorem I1416_fin : (prmOK pI1416 1416 && intTest pI1416 (runFrom pI1416 (fmask pI1416) (cmask pI1416) (hmask pI1416) 1001 415 (true, I1416_cp1.1, I1416_cp1.2)) 1416 20 true) = true := by
  decide +kernel
theorem I1416_ok : RunOK pI1416 1416 (runFrom pI1416 (fmask pI1416) (cmask pI1416) (hmask pI1416) 1001 415 (true, I1416_cp1.1, I1416_cp1.2)) ∧ intTest pI1416 (runFrom pI1416 (fmask pI1416) (cmask pI1416) (hmask pI1416) 1001 415 (true, I1416_cp1.1, I1416_cp1.2)) 1416 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1416_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1416_fin) true) I1416_seg1) (by decide) rfl I1416_fin intTest_fst
theorem link1416 : linkOK pL1416 pH1416 pI1416 = true := by decide +kernel
theorem cvx1416 : ConvexBetweenHumps 1416 :=
  cvx_of L1416_ok H1416_ok I1416_ok link1416 (by decide)
theorem cenlink1416 : cenLinkOK pI1416 1416 = true := by decide +kernel
theorem cen1416 : CenterUniqueMin 1416 ∧ DipHyp 1416 ∧ OnePointHyps 1416 :=
  cen_of L1416_ok H1416_ok I1416_ok link1416 cenlink1416

/-! ### `N = 1417` -/

def pL1417 : Prm := ⟨79, 37, 39, 1419, 11, 18446744073709551616, 130331427412244439, 130331427412244439⟩
def pH1417 : Prm := ⟨79, 37, 39, 1419, 11, 18446744073709551616, 130332526923872215, 130332526923872215⟩
def pI1417 : Prm := ⟨65, 33, 29, 1419, 11, 18446744073709551616, 130331427412244439, 130332526923872215⟩
noncomputable def L1417_cp1 : Nat × Nat := t7val% (fastRun pL1417 1 1001 (init pL1417) (init pL1417))
theorem L1417_seg1 : segOK pL1417 1 1001 (init pL1417) (init pL1417) L1417_cp1.1 L1417_cp1.2 = true := by
  decide +kernel
theorem L1417_fin : (prmOK pL1417 1417 && ptTest pL1417 (runFrom pL1417 (fmask pL1417) (cmask pL1417) (hmask pL1417) 1002 415 (true, L1417_cp1.1, L1417_cp1.2)) 1417 709 false) = true := by
  decide +kernel
theorem L1417_ok : RunOK pL1417 1417 (runFrom pL1417 (fmask pL1417) (cmask pL1417) (hmask pL1417) 1002 415 (true, L1417_cp1.1, L1417_cp1.2)) ∧ ptTest pL1417 (runFrom pL1417 (fmask pL1417) (cmask pL1417) (hmask pL1417) 1002 415 (true, L1417_cp1.1, L1417_cp1.2)) 1417 709 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1417_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1417_fin) true) L1417_seg1) (by decide) rfl L1417_fin ptTest_fst
noncomputable def H1417_cp1 : Nat × Nat := t7val% (fastRun pH1417 1 1001 (init pH1417) (init pH1417))
theorem H1417_seg1 : segOK pH1417 1 1001 (init pH1417) (init pH1417) H1417_cp1.1 H1417_cp1.2 = true := by
  decide +kernel
theorem H1417_fin : (prmOK pH1417 1417 && ptTest pH1417 (runFrom pH1417 (fmask pH1417) (cmask pH1417) (hmask pH1417) 1002 415 (true, H1417_cp1.1, H1417_cp1.2)) 1417 709 true) = true := by
  decide +kernel
theorem H1417_ok : RunOK pH1417 1417 (runFrom pH1417 (fmask pH1417) (cmask pH1417) (hmask pH1417) 1002 415 (true, H1417_cp1.1, H1417_cp1.2)) ∧ ptTest pH1417 (runFrom pH1417 (fmask pH1417) (cmask pH1417) (hmask pH1417) 1002 415 (true, H1417_cp1.1, H1417_cp1.2)) 1417 709 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1417_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1417_fin) true) H1417_seg1) (by decide) rfl H1417_fin ptTest_fst
noncomputable def I1417_cp1 : Nat × Nat := t7val% (fastRun pI1417 1 1001 (init pI1417) (init pI1417))
theorem I1417_seg1 : segOK pI1417 1 1001 (init pI1417) (init pI1417) I1417_cp1.1 I1417_cp1.2 = true := by
  decide +kernel
theorem I1417_fin : (prmOK pI1417 1417 && intTest pI1417 (runFrom pI1417 (fmask pI1417) (cmask pI1417) (hmask pI1417) 1002 415 (true, I1417_cp1.1, I1417_cp1.2)) 1417 20 false) = true := by
  decide +kernel
theorem I1417_ok : RunOK pI1417 1417 (runFrom pI1417 (fmask pI1417) (cmask pI1417) (hmask pI1417) 1002 415 (true, I1417_cp1.1, I1417_cp1.2)) ∧ intTest pI1417 (runFrom pI1417 (fmask pI1417) (cmask pI1417) (hmask pI1417) 1002 415 (true, I1417_cp1.1, I1417_cp1.2)) 1417 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1417_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1417_fin) true) I1417_seg1) (by decide) rfl I1417_fin intTest_fst
theorem link1417 : linkOK pL1417 pH1417 pI1417 = true := by decide +kernel
theorem cvx1417 : ConvexBetweenHumps 1417 :=
  cvx_of L1417_ok H1417_ok I1417_ok link1417 (by decide)

/-! ### `N = 1418` -/

def pL1418 : Prm := ⟨79, 37, 39, 1420, 11, 18446744073709551616, 130256840164467013, 130256840164467013⟩
def pH1418 : Prm := ⟨79, 37, 39, 1420, 11, 18446744073709551616, 130257939676094789, 130257939676094789⟩
def pI1418 : Prm := ⟨65, 33, 29, 1420, 11, 18446744073709551616, 130256840164467013, 130257939676094789⟩
noncomputable def L1418_cp1 : Nat × Nat := t7val% (fastRun pL1418 1 1002 (init pL1418) (init pL1418))
theorem L1418_seg1 : segOK pL1418 1 1002 (init pL1418) (init pL1418) L1418_cp1.1 L1418_cp1.2 = true := by
  decide +kernel
theorem L1418_fin : (prmOK pL1418 1418 && ptTest pL1418 (runFrom pL1418 (fmask pL1418) (cmask pL1418) (hmask pL1418) 1003 415 (true, L1418_cp1.1, L1418_cp1.2)) 1418 709 false) = true := by
  decide +kernel
theorem L1418_ok : RunOK pL1418 1418 (runFrom pL1418 (fmask pL1418) (cmask pL1418) (hmask pL1418) 1003 415 (true, L1418_cp1.1, L1418_cp1.2)) ∧ ptTest pL1418 (runFrom pL1418 (fmask pL1418) (cmask pL1418) (hmask pL1418) 1003 415 (true, L1418_cp1.1, L1418_cp1.2)) 1418 709 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1418_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1418_fin) true) L1418_seg1) (by decide) rfl L1418_fin ptTest_fst
noncomputable def H1418_cp1 : Nat × Nat := t7val% (fastRun pH1418 1 1002 (init pH1418) (init pH1418))
theorem H1418_seg1 : segOK pH1418 1 1002 (init pH1418) (init pH1418) H1418_cp1.1 H1418_cp1.2 = true := by
  decide +kernel
theorem H1418_fin : (prmOK pH1418 1418 && ptTest pH1418 (runFrom pH1418 (fmask pH1418) (cmask pH1418) (hmask pH1418) 1003 415 (true, H1418_cp1.1, H1418_cp1.2)) 1418 709 true) = true := by
  decide +kernel
theorem H1418_ok : RunOK pH1418 1418 (runFrom pH1418 (fmask pH1418) (cmask pH1418) (hmask pH1418) 1003 415 (true, H1418_cp1.1, H1418_cp1.2)) ∧ ptTest pH1418 (runFrom pH1418 (fmask pH1418) (cmask pH1418) (hmask pH1418) 1003 415 (true, H1418_cp1.1, H1418_cp1.2)) 1418 709 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1418_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1418_fin) true) H1418_seg1) (by decide) rfl H1418_fin ptTest_fst
noncomputable def I1418_cp1 : Nat × Nat := t7val% (fastRun pI1418 1 1002 (init pI1418) (init pI1418))
theorem I1418_seg1 : segOK pI1418 1 1002 (init pI1418) (init pI1418) I1418_cp1.1 I1418_cp1.2 = true := by
  decide +kernel
theorem I1418_fin : (prmOK pI1418 1418 && intTest pI1418 (runFrom pI1418 (fmask pI1418) (cmask pI1418) (hmask pI1418) 1003 415 (true, I1418_cp1.1, I1418_cp1.2)) 1418 20 true) = true := by
  decide +kernel
theorem I1418_ok : RunOK pI1418 1418 (runFrom pI1418 (fmask pI1418) (cmask pI1418) (hmask pI1418) 1003 415 (true, I1418_cp1.1, I1418_cp1.2)) ∧ intTest pI1418 (runFrom pI1418 (fmask pI1418) (cmask pI1418) (hmask pI1418) 1003 415 (true, I1418_cp1.1, I1418_cp1.2)) 1418 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1418_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1418_fin) true) I1418_seg1) (by decide) rfl I1418_fin intTest_fst
theorem link1418 : linkOK pL1418 pH1418 pI1418 = true := by decide +kernel
theorem cvx1418 : ConvexBetweenHumps 1418 :=
  cvx_of L1418_ok H1418_ok I1418_ok link1418 (by decide)
theorem cenlink1418 : cenLinkOK pI1418 1418 = true := by decide +kernel
theorem cen1418 : CenterUniqueMin 1418 ∧ DipHyp 1418 ∧ OnePointHyps 1418 :=
  cen_of L1418_ok H1418_ok I1418_ok link1418 cenlink1418

/-! ### `N = 1419` -/

def pL1419 : Prm := ⟨79, 37, 39, 1421, 11, 18446744073709551616, 130182306055616497, 130182306055616497⟩
def pH1419 : Prm := ⟨79, 37, 39, 1421, 11, 18446744073709551616, 130183405567244273, 130183405567244273⟩
def pI1419 : Prm := ⟨65, 33, 29, 1421, 11, 18446744073709551616, 130182306055616497, 130183405567244273⟩
noncomputable def L1419_cp1 : Nat × Nat := t7val% (fastRun pL1419 1 1002 (init pL1419) (init pL1419))
theorem L1419_seg1 : segOK pL1419 1 1002 (init pL1419) (init pL1419) L1419_cp1.1 L1419_cp1.2 = true := by
  decide +kernel
theorem L1419_fin : (prmOK pL1419 1419 && ptTest pL1419 (runFrom pL1419 (fmask pL1419) (cmask pL1419) (hmask pL1419) 1003 416 (true, L1419_cp1.1, L1419_cp1.2)) 1419 710 false) = true := by
  decide +kernel
theorem L1419_ok : RunOK pL1419 1419 (runFrom pL1419 (fmask pL1419) (cmask pL1419) (hmask pL1419) 1003 416 (true, L1419_cp1.1, L1419_cp1.2)) ∧ ptTest pL1419 (runFrom pL1419 (fmask pL1419) (cmask pL1419) (hmask pL1419) 1003 416 (true, L1419_cp1.1, L1419_cp1.2)) 1419 710 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1419_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1419_fin) true) L1419_seg1) (by decide) rfl L1419_fin ptTest_fst
noncomputable def H1419_cp1 : Nat × Nat := t7val% (fastRun pH1419 1 1002 (init pH1419) (init pH1419))
theorem H1419_seg1 : segOK pH1419 1 1002 (init pH1419) (init pH1419) H1419_cp1.1 H1419_cp1.2 = true := by
  decide +kernel
theorem H1419_fin : (prmOK pH1419 1419 && ptTest pH1419 (runFrom pH1419 (fmask pH1419) (cmask pH1419) (hmask pH1419) 1003 416 (true, H1419_cp1.1, H1419_cp1.2)) 1419 710 true) = true := by
  decide +kernel
theorem H1419_ok : RunOK pH1419 1419 (runFrom pH1419 (fmask pH1419) (cmask pH1419) (hmask pH1419) 1003 416 (true, H1419_cp1.1, H1419_cp1.2)) ∧ ptTest pH1419 (runFrom pH1419 (fmask pH1419) (cmask pH1419) (hmask pH1419) 1003 416 (true, H1419_cp1.1, H1419_cp1.2)) 1419 710 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1419_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1419_fin) true) H1419_seg1) (by decide) rfl H1419_fin ptTest_fst
noncomputable def I1419_cp1 : Nat × Nat := t7val% (fastRun pI1419 1 1002 (init pI1419) (init pI1419))
theorem I1419_seg1 : segOK pI1419 1 1002 (init pI1419) (init pI1419) I1419_cp1.1 I1419_cp1.2 = true := by
  decide +kernel
theorem I1419_fin : (prmOK pI1419 1419 && intTest pI1419 (runFrom pI1419 (fmask pI1419) (cmask pI1419) (hmask pI1419) 1003 416 (true, I1419_cp1.1, I1419_cp1.2)) 1419 20 false) = true := by
  decide +kernel
theorem I1419_ok : RunOK pI1419 1419 (runFrom pI1419 (fmask pI1419) (cmask pI1419) (hmask pI1419) 1003 416 (true, I1419_cp1.1, I1419_cp1.2)) ∧ intTest pI1419 (runFrom pI1419 (fmask pI1419) (cmask pI1419) (hmask pI1419) 1003 416 (true, I1419_cp1.1, I1419_cp1.2)) 1419 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1419_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1419_fin) true) I1419_seg1) (by decide) rfl I1419_fin intTest_fst
theorem link1419 : linkOK pL1419 pH1419 pI1419 = true := by decide +kernel
theorem cvx1419 : ConvexBetweenHumps 1419 :=
  cvx_of L1419_ok H1419_ok I1419_ok link1419 (by decide)

/-! ### `N = 1420` -/

def pL1420 : Prm := ⟨79, 37, 39, 1422, 11, 18446744073709551616, 130107904444637362, 130107904444637362⟩
def pH1420 : Prm := ⟨80, 38, 39, 1422, 11, 18446744073709551616, 130109003956265138, 130109003956265138⟩
def pI1420 : Prm := ⟨65, 33, 29, 1422, 11, 18446744073709551616, 130107904444637362, 130109003956265138⟩
noncomputable def L1420_cp1 : Nat × Nat := t7val% (fastRun pL1420 1 1003 (init pL1420) (init pL1420))
theorem L1420_seg1 : segOK pL1420 1 1003 (init pL1420) (init pL1420) L1420_cp1.1 L1420_cp1.2 = true := by
  decide +kernel
theorem L1420_fin : (prmOK pL1420 1420 && ptTest pL1420 (runFrom pL1420 (fmask pL1420) (cmask pL1420) (hmask pL1420) 1004 416 (true, L1420_cp1.1, L1420_cp1.2)) 1420 710 false) = true := by
  decide +kernel
theorem L1420_ok : RunOK pL1420 1420 (runFrom pL1420 (fmask pL1420) (cmask pL1420) (hmask pL1420) 1004 416 (true, L1420_cp1.1, L1420_cp1.2)) ∧ ptTest pL1420 (runFrom pL1420 (fmask pL1420) (cmask pL1420) (hmask pL1420) 1004 416 (true, L1420_cp1.1, L1420_cp1.2)) 1420 710 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1420_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1420_fin) true) L1420_seg1) (by decide) rfl L1420_fin ptTest_fst
noncomputable def H1420_cp1 : Nat × Nat := t7val% (fastRun pH1420 1 1003 (init pH1420) (init pH1420))
theorem H1420_seg1 : segOK pH1420 1 1003 (init pH1420) (init pH1420) H1420_cp1.1 H1420_cp1.2 = true := by
  decide +kernel
theorem H1420_fin : (prmOK pH1420 1420 && ptTest pH1420 (runFrom pH1420 (fmask pH1420) (cmask pH1420) (hmask pH1420) 1004 416 (true, H1420_cp1.1, H1420_cp1.2)) 1420 710 true) = true := by
  decide +kernel
theorem H1420_ok : RunOK pH1420 1420 (runFrom pH1420 (fmask pH1420) (cmask pH1420) (hmask pH1420) 1004 416 (true, H1420_cp1.1, H1420_cp1.2)) ∧ ptTest pH1420 (runFrom pH1420 (fmask pH1420) (cmask pH1420) (hmask pH1420) 1004 416 (true, H1420_cp1.1, H1420_cp1.2)) 1420 710 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1420_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1420_fin) true) H1420_seg1) (by decide) rfl H1420_fin ptTest_fst
noncomputable def I1420_cp1 : Nat × Nat := t7val% (fastRun pI1420 1 1003 (init pI1420) (init pI1420))
theorem I1420_seg1 : segOK pI1420 1 1003 (init pI1420) (init pI1420) I1420_cp1.1 I1420_cp1.2 = true := by
  decide +kernel
theorem I1420_fin : (prmOK pI1420 1420 && intTest pI1420 (runFrom pI1420 (fmask pI1420) (cmask pI1420) (hmask pI1420) 1004 416 (true, I1420_cp1.1, I1420_cp1.2)) 1420 20 true) = true := by
  decide +kernel
theorem I1420_ok : RunOK pI1420 1420 (runFrom pI1420 (fmask pI1420) (cmask pI1420) (hmask pI1420) 1004 416 (true, I1420_cp1.1, I1420_cp1.2)) ∧ intTest pI1420 (runFrom pI1420 (fmask pI1420) (cmask pI1420) (hmask pI1420) 1004 416 (true, I1420_cp1.1, I1420_cp1.2)) 1420 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1420_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1420_fin) true) I1420_seg1) (by decide) rfl I1420_fin intTest_fst
theorem link1420 : linkOK pL1420 pH1420 pI1420 = true := by decide +kernel
theorem cvx1420 : ConvexBetweenHumps 1420 :=
  cvx_of L1420_ok H1420_ok I1420_ok link1420 (by decide)
theorem cenlink1420 : cenLinkOK pI1420 1420 = true := by decide +kernel
theorem cen1420 : CenterUniqueMin 1420 ∧ DipHyp 1420 ∧ OnePointHyps 1420 :=
  cen_of L1420_ok H1420_ok I1420_ok link1420 cenlink1420

/-! ### `N = 1421` -/

def pL1421 : Prm := ⟨79, 37, 39, 1423, 11, 18446744073709551616, 130033555785424471, 130033555785424471⟩
def pH1421 : Prm := ⟨79, 37, 39, 1423, 11, 18446744073709551616, 130034655297052247, 130034655297052247⟩
def pI1421 : Prm := ⟨65, 33, 29, 1423, 11, 18446744073709551616, 130033555785424471, 130034655297052247⟩
noncomputable def L1421_cp1 : Nat × Nat := t7val% (fastRun pL1421 1 1004 (init pL1421) (init pL1421))
theorem L1421_seg1 : segOK pL1421 1 1004 (init pL1421) (init pL1421) L1421_cp1.1 L1421_cp1.2 = true := by
  decide +kernel
theorem L1421_fin : (prmOK pL1421 1421 && ptTest pL1421 (runFrom pL1421 (fmask pL1421) (cmask pL1421) (hmask pL1421) 1005 416 (true, L1421_cp1.1, L1421_cp1.2)) 1421 711 false) = true := by
  decide +kernel
theorem L1421_ok : RunOK pL1421 1421 (runFrom pL1421 (fmask pL1421) (cmask pL1421) (hmask pL1421) 1005 416 (true, L1421_cp1.1, L1421_cp1.2)) ∧ ptTest pL1421 (runFrom pL1421 (fmask pL1421) (cmask pL1421) (hmask pL1421) 1005 416 (true, L1421_cp1.1, L1421_cp1.2)) 1421 711 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1421_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1421_fin) true) L1421_seg1) (by decide) rfl L1421_fin ptTest_fst
noncomputable def H1421_cp1 : Nat × Nat := t7val% (fastRun pH1421 1 1004 (init pH1421) (init pH1421))
theorem H1421_seg1 : segOK pH1421 1 1004 (init pH1421) (init pH1421) H1421_cp1.1 H1421_cp1.2 = true := by
  decide +kernel
theorem H1421_fin : (prmOK pH1421 1421 && ptTest pH1421 (runFrom pH1421 (fmask pH1421) (cmask pH1421) (hmask pH1421) 1005 416 (true, H1421_cp1.1, H1421_cp1.2)) 1421 711 true) = true := by
  decide +kernel
theorem H1421_ok : RunOK pH1421 1421 (runFrom pH1421 (fmask pH1421) (cmask pH1421) (hmask pH1421) 1005 416 (true, H1421_cp1.1, H1421_cp1.2)) ∧ ptTest pH1421 (runFrom pH1421 (fmask pH1421) (cmask pH1421) (hmask pH1421) 1005 416 (true, H1421_cp1.1, H1421_cp1.2)) 1421 711 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1421_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1421_fin) true) H1421_seg1) (by decide) rfl H1421_fin ptTest_fst
noncomputable def I1421_cp1 : Nat × Nat := t7val% (fastRun pI1421 1 1004 (init pI1421) (init pI1421))
theorem I1421_seg1 : segOK pI1421 1 1004 (init pI1421) (init pI1421) I1421_cp1.1 I1421_cp1.2 = true := by
  decide +kernel
theorem I1421_fin : (prmOK pI1421 1421 && intTest pI1421 (runFrom pI1421 (fmask pI1421) (cmask pI1421) (hmask pI1421) 1005 416 (true, I1421_cp1.1, I1421_cp1.2)) 1421 20 false) = true := by
  decide +kernel
theorem I1421_ok : RunOK pI1421 1421 (runFrom pI1421 (fmask pI1421) (cmask pI1421) (hmask pI1421) 1005 416 (true, I1421_cp1.1, I1421_cp1.2)) ∧ intTest pI1421 (runFrom pI1421 (fmask pI1421) (cmask pI1421) (hmask pI1421) 1005 416 (true, I1421_cp1.1, I1421_cp1.2)) 1421 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1421_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1421_fin) true) I1421_seg1) (by decide) rfl I1421_fin intTest_fst
theorem link1421 : linkOK pL1421 pH1421 pI1421 = true := by decide +kernel
theorem cvx1421 : ConvexBetweenHumps 1421 :=
  cvx_of L1421_ok H1421_ok I1421_ok link1421 (by decide)

/-! ### The range -/

theorem cvx_1402_1421 {N : ℕ} (h1 : 1402 ≤ N) (h2 : N ≤ 1421) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1411
  · by_cases h4 : N ≤ 1406
    · by_cases h6 : N ≤ 1403
      · by_cases h8 : N ≤ 1402
        · obtain rfl : N = 1402 := by omega
          exact cvx1402
        · obtain rfl : N = 1403 := by omega
          exact cvx1403
      · by_cases h8 : N ≤ 1404
        · obtain rfl : N = 1404 := by omega
          exact cvx1404
        · by_cases h10 : N ≤ 1405
          · obtain rfl : N = 1405 := by omega
            exact cvx1405
          · obtain rfl : N = 1406 := by omega
            exact cvx1406
    · by_cases h6 : N ≤ 1408
      · by_cases h8 : N ≤ 1407
        · obtain rfl : N = 1407 := by omega
          exact cvx1407
        · obtain rfl : N = 1408 := by omega
          exact cvx1408
      · by_cases h8 : N ≤ 1409
        · obtain rfl : N = 1409 := by omega
          exact cvx1409
        · by_cases h10 : N ≤ 1410
          · obtain rfl : N = 1410 := by omega
            exact cvx1410
          · obtain rfl : N = 1411 := by omega
            exact cvx1411
  · by_cases h4 : N ≤ 1416
    · by_cases h6 : N ≤ 1413
      · by_cases h8 : N ≤ 1412
        · obtain rfl : N = 1412 := by omega
          exact cvx1412
        · obtain rfl : N = 1413 := by omega
          exact cvx1413
      · by_cases h8 : N ≤ 1414
        · obtain rfl : N = 1414 := by omega
          exact cvx1414
        · by_cases h10 : N ≤ 1415
          · obtain rfl : N = 1415 := by omega
            exact cvx1415
          · obtain rfl : N = 1416 := by omega
            exact cvx1416
    · by_cases h6 : N ≤ 1418
      · by_cases h8 : N ≤ 1417
        · obtain rfl : N = 1417 := by omega
          exact cvx1417
        · obtain rfl : N = 1418 := by omega
          exact cvx1418
      · by_cases h8 : N ≤ 1419
        · obtain rfl : N = 1419 := by omega
          exact cvx1419
        · by_cases h10 : N ≤ 1420
          · obtain rfl : N = 1420 := by omega
            exact cvx1420
          · obtain rfl : N = 1421 := by omega
            exact cvx1421

theorem cen_1402_1421 {N : ℕ} (h1 : 1402 ≤ N) (h2 : N ≤ 1421) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1410
  · by_cases h4 : N ≤ 1404
    · by_cases h6 : N ≤ 1402
      · obtain rfl : N = 1402 := by omega
        exact cen1402
      · obtain rfl : N = 1404 := by omega
        exact cen1404
    · by_cases h6 : N ≤ 1406
      · obtain rfl : N = 1406 := by omega
        exact cen1406
      · by_cases h8 : N ≤ 1408
        · obtain rfl : N = 1408 := by omega
          exact cen1408
        · obtain rfl : N = 1410 := by omega
          exact cen1410
  · by_cases h4 : N ≤ 1414
    · by_cases h6 : N ≤ 1412
      · obtain rfl : N = 1412 := by omega
        exact cen1412
      · obtain rfl : N = 1414 := by omega
        exact cen1414
    · by_cases h6 : N ≤ 1416
      · obtain rfl : N = 1416 := by omega
        exact cen1416
      · by_cases h8 : N ≤ 1418
        · obtain rfl : N = 1418 := by omega
          exact cen1418
        · obtain rfl : N = 1420 := by omega
          exact cen1420

end Kagey131.PaperD.T7
