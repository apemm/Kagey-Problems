import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1990, …, 1999` (generated)

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

/-! ### `N = 1990` -/

def pL1990 : Prm := ⟨81, 38, 40, 1992, 11, 18446744073709551616, 98738350946113340, 98738350946113340⟩
def pH1990 : Prm := ⟨81, 38, 40, 1992, 11, 18446744073709551616, 98739450457741116, 98739450457741116⟩
def pI1990 : Prm := ⟨68, 34, 31, 1992, 11, 18446744073709551616, 98738350946113340, 98739450457741116⟩
noncomputable def L1990_cp1 : Nat × Nat := t7val% (fastRun pL1990 1 1148 (init pL1990) (init pL1990))
theorem L1990_seg1 : segOK pL1990 1 1148 (init pL1990) (init pL1990) L1990_cp1.1 L1990_cp1.2 = true := by
  decide +kernel
noncomputable def L1990_cp2 : Nat × Nat := t7val% (fastRun pL1990 1 1624 (init pL1990) (init pL1990))
theorem L1990_seg2 : segOK pL1990 1149 476 L1990_cp1.1 L1990_cp1.2 L1990_cp2.1 L1990_cp2.2 = true := by
  decide +kernel
theorem L1990_fin : (prmOK pL1990 1990 && ptTest pL1990 (runFrom pL1990 (fmask pL1990) (cmask pL1990) (hmask pL1990) 1625 365 (true, L1990_cp2.1, L1990_cp2.2)) 1990 995 false) = true := by
  decide +kernel
theorem L1990_ok : RunOK pL1990 1990 (runFrom pL1990 (fmask pL1990) (cmask pL1990) (hmask pL1990) 1625 365 (true, L1990_cp2.1, L1990_cp2.2)) ∧ ptTest pL1990 (runFrom pL1990 (fmask pL1990) (cmask pL1990) (hmask pL1990) 1625 365 (true, L1990_cp2.1, L1990_cp2.2)) 1990 995 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1990_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1990_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1990_fin) true) L1990_seg1) L1990_seg2) (by decide) rfl L1990_fin ptTest_fst
noncomputable def H1990_cp1 : Nat × Nat := t7val% (fastRun pH1990 1 1148 (init pH1990) (init pH1990))
theorem H1990_seg1 : segOK pH1990 1 1148 (init pH1990) (init pH1990) H1990_cp1.1 H1990_cp1.2 = true := by
  decide +kernel
noncomputable def H1990_cp2 : Nat × Nat := t7val% (fastRun pH1990 1 1624 (init pH1990) (init pH1990))
theorem H1990_seg2 : segOK pH1990 1149 476 H1990_cp1.1 H1990_cp1.2 H1990_cp2.1 H1990_cp2.2 = true := by
  decide +kernel
theorem H1990_fin : (prmOK pH1990 1990 && ptTest pH1990 (runFrom pH1990 (fmask pH1990) (cmask pH1990) (hmask pH1990) 1625 365 (true, H1990_cp2.1, H1990_cp2.2)) 1990 995 true) = true := by
  decide +kernel
theorem H1990_ok : RunOK pH1990 1990 (runFrom pH1990 (fmask pH1990) (cmask pH1990) (hmask pH1990) 1625 365 (true, H1990_cp2.1, H1990_cp2.2)) ∧ ptTest pH1990 (runFrom pH1990 (fmask pH1990) (cmask pH1990) (hmask pH1990) 1625 365 (true, H1990_cp2.1, H1990_cp2.2)) 1990 995 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1990_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1990_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1990_fin) true) H1990_seg1) H1990_seg2) (by decide) rfl H1990_fin ptTest_fst
noncomputable def I1990_cp1 : Nat × Nat := t7val% (fastRun pI1990 1 1148 (init pI1990) (init pI1990))
theorem I1990_seg1 : segOK pI1990 1 1148 (init pI1990) (init pI1990) I1990_cp1.1 I1990_cp1.2 = true := by
  decide +kernel
noncomputable def I1990_cp2 : Nat × Nat := t7val% (fastRun pI1990 1 1624 (init pI1990) (init pI1990))
theorem I1990_seg2 : segOK pI1990 1149 476 I1990_cp1.1 I1990_cp1.2 I1990_cp2.1 I1990_cp2.2 = true := by
  decide +kernel
theorem I1990_fin : (prmOK pI1990 1990 && intTest pI1990 (runFrom pI1990 (fmask pI1990) (cmask pI1990) (hmask pI1990) 1625 365 (true, I1990_cp2.1, I1990_cp2.2)) 1990 22 true) = true := by
  decide +kernel
theorem I1990_ok : RunOK pI1990 1990 (runFrom pI1990 (fmask pI1990) (cmask pI1990) (hmask pI1990) 1625 365 (true, I1990_cp2.1, I1990_cp2.2)) ∧ intTest pI1990 (runFrom pI1990 (fmask pI1990) (cmask pI1990) (hmask pI1990) 1625 365 (true, I1990_cp2.1, I1990_cp2.2)) 1990 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1990_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1990_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1990_fin) true) I1990_seg1) I1990_seg2) (by decide) rfl I1990_fin intTest_fst
theorem link1990 : linkOK pL1990 pH1990 pI1990 = true := by decide +kernel
theorem cvx1990 : ConvexBetweenHumps 1990 :=
  cvx_of L1990_ok H1990_ok I1990_ok link1990 (by decide)
theorem cenlink1990 : cenLinkOK pI1990 1990 = true := by decide +kernel
theorem cen1990 : CenterUniqueMin 1990 ∧ DipHyp 1990 ∧ OnePointHyps 1990 :=
  cen_of L1990_ok H1990_ok I1990_ok link1990 cenlink1990

/-! ### `N = 1991` -/

def pL1991 : Prm := ⟨81, 38, 40, 1993, 11, 18446744073709551616, 98697524491893529, 98697524491893529⟩
def pH1991 : Prm := ⟨81, 38, 40, 1993, 11, 18446744073709551616, 98698624003521305, 98698624003521305⟩
def pI1991 : Prm := ⟨68, 34, 31, 1993, 11, 18446744073709551616, 98697524491893529, 98698624003521305⟩
noncomputable def L1991_cp1 : Nat × Nat := t7val% (fastRun pL1991 1 1149 (init pL1991) (init pL1991))
theorem L1991_seg1 : segOK pL1991 1 1149 (init pL1991) (init pL1991) L1991_cp1.1 L1991_cp1.2 = true := by
  decide +kernel
noncomputable def L1991_cp2 : Nat × Nat := t7val% (fastRun pL1991 1 1625 (init pL1991) (init pL1991))
theorem L1991_seg2 : segOK pL1991 1150 476 L1991_cp1.1 L1991_cp1.2 L1991_cp2.1 L1991_cp2.2 = true := by
  decide +kernel
theorem L1991_fin : (prmOK pL1991 1991 && ptTest pL1991 (runFrom pL1991 (fmask pL1991) (cmask pL1991) (hmask pL1991) 1626 365 (true, L1991_cp2.1, L1991_cp2.2)) 1991 996 false) = true := by
  decide +kernel
theorem L1991_ok : RunOK pL1991 1991 (runFrom pL1991 (fmask pL1991) (cmask pL1991) (hmask pL1991) 1626 365 (true, L1991_cp2.1, L1991_cp2.2)) ∧ ptTest pL1991 (runFrom pL1991 (fmask pL1991) (cmask pL1991) (hmask pL1991) 1626 365 (true, L1991_cp2.1, L1991_cp2.2)) 1991 996 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1991_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1991_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1991_fin) true) L1991_seg1) L1991_seg2) (by decide) rfl L1991_fin ptTest_fst
noncomputable def H1991_cp1 : Nat × Nat := t7val% (fastRun pH1991 1 1149 (init pH1991) (init pH1991))
theorem H1991_seg1 : segOK pH1991 1 1149 (init pH1991) (init pH1991) H1991_cp1.1 H1991_cp1.2 = true := by
  decide +kernel
noncomputable def H1991_cp2 : Nat × Nat := t7val% (fastRun pH1991 1 1625 (init pH1991) (init pH1991))
theorem H1991_seg2 : segOK pH1991 1150 476 H1991_cp1.1 H1991_cp1.2 H1991_cp2.1 H1991_cp2.2 = true := by
  decide +kernel
theorem H1991_fin : (prmOK pH1991 1991 && ptTest pH1991 (runFrom pH1991 (fmask pH1991) (cmask pH1991) (hmask pH1991) 1626 365 (true, H1991_cp2.1, H1991_cp2.2)) 1991 996 true) = true := by
  decide +kernel
theorem H1991_ok : RunOK pH1991 1991 (runFrom pH1991 (fmask pH1991) (cmask pH1991) (hmask pH1991) 1626 365 (true, H1991_cp2.1, H1991_cp2.2)) ∧ ptTest pH1991 (runFrom pH1991 (fmask pH1991) (cmask pH1991) (hmask pH1991) 1626 365 (true, H1991_cp2.1, H1991_cp2.2)) 1991 996 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1991_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1991_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1991_fin) true) H1991_seg1) H1991_seg2) (by decide) rfl H1991_fin ptTest_fst
noncomputable def I1991_cp1 : Nat × Nat := t7val% (fastRun pI1991 1 1149 (init pI1991) (init pI1991))
theorem I1991_seg1 : segOK pI1991 1 1149 (init pI1991) (init pI1991) I1991_cp1.1 I1991_cp1.2 = true := by
  decide +kernel
noncomputable def I1991_cp2 : Nat × Nat := t7val% (fastRun pI1991 1 1625 (init pI1991) (init pI1991))
theorem I1991_seg2 : segOK pI1991 1150 476 I1991_cp1.1 I1991_cp1.2 I1991_cp2.1 I1991_cp2.2 = true := by
  decide +kernel
theorem I1991_fin : (prmOK pI1991 1991 && intTest pI1991 (runFrom pI1991 (fmask pI1991) (cmask pI1991) (hmask pI1991) 1626 365 (true, I1991_cp2.1, I1991_cp2.2)) 1991 22 false) = true := by
  decide +kernel
theorem I1991_ok : RunOK pI1991 1991 (runFrom pI1991 (fmask pI1991) (cmask pI1991) (hmask pI1991) 1626 365 (true, I1991_cp2.1, I1991_cp2.2)) ∧ intTest pI1991 (runFrom pI1991 (fmask pI1991) (cmask pI1991) (hmask pI1991) 1626 365 (true, I1991_cp2.1, I1991_cp2.2)) 1991 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1991_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1991_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1991_fin) true) I1991_seg1) I1991_seg2) (by decide) rfl I1991_fin intTest_fst
theorem link1991 : linkOK pL1991 pH1991 pI1991 = true := by decide +kernel
theorem cvx1991 : ConvexBetweenHumps 1991 :=
  cvx_of L1991_ok H1991_ok I1991_ok link1991 (by decide)

/-! ### `N = 1992` -/

def pL1992 : Prm := ⟨81, 38, 40, 1994, 11, 18446744073709551616, 98656748768839357, 98656748768839357⟩
def pH1992 : Prm := ⟨81, 38, 40, 1994, 11, 18446744073709551616, 98657848280467133, 98657848280467133⟩
def pI1992 : Prm := ⟨68, 34, 31, 1994, 11, 18446744073709551616, 98656748768839357, 98657848280467133⟩
noncomputable def L1992_cp1 : Nat × Nat := t7val% (fastRun pL1992 1 1149 (init pL1992) (init pL1992))
theorem L1992_seg1 : segOK pL1992 1 1149 (init pL1992) (init pL1992) L1992_cp1.1 L1992_cp1.2 = true := by
  decide +kernel
noncomputable def L1992_cp2 : Nat × Nat := t7val% (fastRun pL1992 1 1625 (init pL1992) (init pL1992))
theorem L1992_seg2 : segOK pL1992 1150 476 L1992_cp1.1 L1992_cp1.2 L1992_cp2.1 L1992_cp2.2 = true := by
  decide +kernel
theorem L1992_fin : (prmOK pL1992 1992 && ptTest pL1992 (runFrom pL1992 (fmask pL1992) (cmask pL1992) (hmask pL1992) 1626 366 (true, L1992_cp2.1, L1992_cp2.2)) 1992 996 false) = true := by
  decide +kernel
theorem L1992_ok : RunOK pL1992 1992 (runFrom pL1992 (fmask pL1992) (cmask pL1992) (hmask pL1992) 1626 366 (true, L1992_cp2.1, L1992_cp2.2)) ∧ ptTest pL1992 (runFrom pL1992 (fmask pL1992) (cmask pL1992) (hmask pL1992) 1626 366 (true, L1992_cp2.1, L1992_cp2.2)) 1992 996 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1992_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1992_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1992_fin) true) L1992_seg1) L1992_seg2) (by decide) rfl L1992_fin ptTest_fst
noncomputable def H1992_cp1 : Nat × Nat := t7val% (fastRun pH1992 1 1149 (init pH1992) (init pH1992))
theorem H1992_seg1 : segOK pH1992 1 1149 (init pH1992) (init pH1992) H1992_cp1.1 H1992_cp1.2 = true := by
  decide +kernel
noncomputable def H1992_cp2 : Nat × Nat := t7val% (fastRun pH1992 1 1625 (init pH1992) (init pH1992))
theorem H1992_seg2 : segOK pH1992 1150 476 H1992_cp1.1 H1992_cp1.2 H1992_cp2.1 H1992_cp2.2 = true := by
  decide +kernel
theorem H1992_fin : (prmOK pH1992 1992 && ptTest pH1992 (runFrom pH1992 (fmask pH1992) (cmask pH1992) (hmask pH1992) 1626 366 (true, H1992_cp2.1, H1992_cp2.2)) 1992 996 true) = true := by
  decide +kernel
theorem H1992_ok : RunOK pH1992 1992 (runFrom pH1992 (fmask pH1992) (cmask pH1992) (hmask pH1992) 1626 366 (true, H1992_cp2.1, H1992_cp2.2)) ∧ ptTest pH1992 (runFrom pH1992 (fmask pH1992) (cmask pH1992) (hmask pH1992) 1626 366 (true, H1992_cp2.1, H1992_cp2.2)) 1992 996 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1992_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1992_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1992_fin) true) H1992_seg1) H1992_seg2) (by decide) rfl H1992_fin ptTest_fst
noncomputable def I1992_cp1 : Nat × Nat := t7val% (fastRun pI1992 1 1149 (init pI1992) (init pI1992))
theorem I1992_seg1 : segOK pI1992 1 1149 (init pI1992) (init pI1992) I1992_cp1.1 I1992_cp1.2 = true := by
  decide +kernel
noncomputable def I1992_cp2 : Nat × Nat := t7val% (fastRun pI1992 1 1625 (init pI1992) (init pI1992))
theorem I1992_seg2 : segOK pI1992 1150 476 I1992_cp1.1 I1992_cp1.2 I1992_cp2.1 I1992_cp2.2 = true := by
  decide +kernel
theorem I1992_fin : (prmOK pI1992 1992 && intTest pI1992 (runFrom pI1992 (fmask pI1992) (cmask pI1992) (hmask pI1992) 1626 366 (true, I1992_cp2.1, I1992_cp2.2)) 1992 22 true) = true := by
  decide +kernel
theorem I1992_ok : RunOK pI1992 1992 (runFrom pI1992 (fmask pI1992) (cmask pI1992) (hmask pI1992) 1626 366 (true, I1992_cp2.1, I1992_cp2.2)) ∧ intTest pI1992 (runFrom pI1992 (fmask pI1992) (cmask pI1992) (hmask pI1992) 1626 366 (true, I1992_cp2.1, I1992_cp2.2)) 1992 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1992_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1992_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1992_fin) true) I1992_seg1) I1992_seg2) (by decide) rfl I1992_fin intTest_fst
theorem link1992 : linkOK pL1992 pH1992 pI1992 = true := by decide +kernel
theorem cvx1992 : ConvexBetweenHumps 1992 :=
  cvx_of L1992_ok H1992_ok I1992_ok link1992 (by decide)
theorem cenlink1992 : cenLinkOK pI1992 1992 = true := by decide +kernel
theorem cen1992 : CenterUniqueMin 1992 ∧ DipHyp 1992 ∧ OnePointHyps 1992 :=
  cen_of L1992_ok H1992_ok I1992_ok link1992 cenlink1992

/-! ### `N = 1993` -/

def pL1993 : Prm := ⟨81, 38, 40, 1995, 11, 18446744073709551616, 98615995434081959, 98615995434081959⟩
def pH1993 : Prm := ⟨81, 38, 40, 1995, 11, 18446744073709551616, 98617094945709735, 98617094945709735⟩
def pI1993 : Prm := ⟨68, 34, 31, 1995, 11, 18446744073709551616, 98615995434081959, 98617094945709735⟩
noncomputable def L1993_cp1 : Nat × Nat := t7val% (fastRun pL1993 1 1150 (init pL1993) (init pL1993))
theorem L1993_seg1 : segOK pL1993 1 1150 (init pL1993) (init pL1993) L1993_cp1.1 L1993_cp1.2 = true := by
  decide +kernel
noncomputable def L1993_cp2 : Nat × Nat := t7val% (fastRun pL1993 1 1626 (init pL1993) (init pL1993))
theorem L1993_seg2 : segOK pL1993 1151 476 L1993_cp1.1 L1993_cp1.2 L1993_cp2.1 L1993_cp2.2 = true := by
  decide +kernel
theorem L1993_fin : (prmOK pL1993 1993 && ptTest pL1993 (runFrom pL1993 (fmask pL1993) (cmask pL1993) (hmask pL1993) 1627 366 (true, L1993_cp2.1, L1993_cp2.2)) 1993 997 false) = true := by
  decide +kernel
theorem L1993_ok : RunOK pL1993 1993 (runFrom pL1993 (fmask pL1993) (cmask pL1993) (hmask pL1993) 1627 366 (true, L1993_cp2.1, L1993_cp2.2)) ∧ ptTest pL1993 (runFrom pL1993 (fmask pL1993) (cmask pL1993) (hmask pL1993) 1627 366 (true, L1993_cp2.1, L1993_cp2.2)) 1993 997 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1993_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1993_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1993_fin) true) L1993_seg1) L1993_seg2) (by decide) rfl L1993_fin ptTest_fst
noncomputable def H1993_cp1 : Nat × Nat := t7val% (fastRun pH1993 1 1150 (init pH1993) (init pH1993))
theorem H1993_seg1 : segOK pH1993 1 1150 (init pH1993) (init pH1993) H1993_cp1.1 H1993_cp1.2 = true := by
  decide +kernel
noncomputable def H1993_cp2 : Nat × Nat := t7val% (fastRun pH1993 1 1626 (init pH1993) (init pH1993))
theorem H1993_seg2 : segOK pH1993 1151 476 H1993_cp1.1 H1993_cp1.2 H1993_cp2.1 H1993_cp2.2 = true := by
  decide +kernel
theorem H1993_fin : (prmOK pH1993 1993 && ptTest pH1993 (runFrom pH1993 (fmask pH1993) (cmask pH1993) (hmask pH1993) 1627 366 (true, H1993_cp2.1, H1993_cp2.2)) 1993 997 true) = true := by
  decide +kernel
theorem H1993_ok : RunOK pH1993 1993 (runFrom pH1993 (fmask pH1993) (cmask pH1993) (hmask pH1993) 1627 366 (true, H1993_cp2.1, H1993_cp2.2)) ∧ ptTest pH1993 (runFrom pH1993 (fmask pH1993) (cmask pH1993) (hmask pH1993) 1627 366 (true, H1993_cp2.1, H1993_cp2.2)) 1993 997 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1993_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1993_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1993_fin) true) H1993_seg1) H1993_seg2) (by decide) rfl H1993_fin ptTest_fst
noncomputable def I1993_cp1 : Nat × Nat := t7val% (fastRun pI1993 1 1150 (init pI1993) (init pI1993))
theorem I1993_seg1 : segOK pI1993 1 1150 (init pI1993) (init pI1993) I1993_cp1.1 I1993_cp1.2 = true := by
  decide +kernel
noncomputable def I1993_cp2 : Nat × Nat := t7val% (fastRun pI1993 1 1626 (init pI1993) (init pI1993))
theorem I1993_seg2 : segOK pI1993 1151 476 I1993_cp1.1 I1993_cp1.2 I1993_cp2.1 I1993_cp2.2 = true := by
  decide +kernel
theorem I1993_fin : (prmOK pI1993 1993 && intTest pI1993 (runFrom pI1993 (fmask pI1993) (cmask pI1993) (hmask pI1993) 1627 366 (true, I1993_cp2.1, I1993_cp2.2)) 1993 22 false) = true := by
  decide +kernel
theorem I1993_ok : RunOK pI1993 1993 (runFrom pI1993 (fmask pI1993) (cmask pI1993) (hmask pI1993) 1627 366 (true, I1993_cp2.1, I1993_cp2.2)) ∧ intTest pI1993 (runFrom pI1993 (fmask pI1993) (cmask pI1993) (hmask pI1993) 1627 366 (true, I1993_cp2.1, I1993_cp2.2)) 1993 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1993_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1993_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1993_fin) true) I1993_seg1) I1993_seg2) (by decide) rfl I1993_fin intTest_fst
theorem link1993 : linkOK pL1993 pH1993 pI1993 = true := by decide +kernel
theorem cvx1993 : ConvexBetweenHumps 1993 :=
  cvx_of L1993_ok H1993_ok I1993_ok link1993 (by decide)

/-! ### `N = 1994` -/

def pL1994 : Prm := ⟨81, 38, 40, 1996, 11, 18446744073709551616, 98575292686125982, 98575292686125982⟩
def pH1994 : Prm := ⟨81, 38, 40, 1996, 11, 18446744073709551616, 98576392197753758, 98576392197753758⟩
def pI1994 : Prm := ⟨68, 34, 31, 1996, 11, 18446744073709551616, 98575292686125982, 98576392197753758⟩
noncomputable def L1994_cp1 : Nat × Nat := t7val% (fastRun pL1994 1 1150 (init pL1994) (init pL1994))
theorem L1994_seg1 : segOK pL1994 1 1150 (init pL1994) (init pL1994) L1994_cp1.1 L1994_cp1.2 = true := by
  decide +kernel
noncomputable def L1994_cp2 : Nat × Nat := t7val% (fastRun pL1994 1 1627 (init pL1994) (init pL1994))
theorem L1994_seg2 : segOK pL1994 1151 477 L1994_cp1.1 L1994_cp1.2 L1994_cp2.1 L1994_cp2.2 = true := by
  decide +kernel
theorem L1994_fin : (prmOK pL1994 1994 && ptTest pL1994 (runFrom pL1994 (fmask pL1994) (cmask pL1994) (hmask pL1994) 1628 366 (true, L1994_cp2.1, L1994_cp2.2)) 1994 997 false) = true := by
  decide +kernel
theorem L1994_ok : RunOK pL1994 1994 (runFrom pL1994 (fmask pL1994) (cmask pL1994) (hmask pL1994) 1628 366 (true, L1994_cp2.1, L1994_cp2.2)) ∧ ptTest pL1994 (runFrom pL1994 (fmask pL1994) (cmask pL1994) (hmask pL1994) 1628 366 (true, L1994_cp2.1, L1994_cp2.2)) 1994 997 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1994_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1994_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1994_fin) true) L1994_seg1) L1994_seg2) (by decide) rfl L1994_fin ptTest_fst
noncomputable def H1994_cp1 : Nat × Nat := t7val% (fastRun pH1994 1 1150 (init pH1994) (init pH1994))
theorem H1994_seg1 : segOK pH1994 1 1150 (init pH1994) (init pH1994) H1994_cp1.1 H1994_cp1.2 = true := by
  decide +kernel
noncomputable def H1994_cp2 : Nat × Nat := t7val% (fastRun pH1994 1 1627 (init pH1994) (init pH1994))
theorem H1994_seg2 : segOK pH1994 1151 477 H1994_cp1.1 H1994_cp1.2 H1994_cp2.1 H1994_cp2.2 = true := by
  decide +kernel
theorem H1994_fin : (prmOK pH1994 1994 && ptTest pH1994 (runFrom pH1994 (fmask pH1994) (cmask pH1994) (hmask pH1994) 1628 366 (true, H1994_cp2.1, H1994_cp2.2)) 1994 997 true) = true := by
  decide +kernel
theorem H1994_ok : RunOK pH1994 1994 (runFrom pH1994 (fmask pH1994) (cmask pH1994) (hmask pH1994) 1628 366 (true, H1994_cp2.1, H1994_cp2.2)) ∧ ptTest pH1994 (runFrom pH1994 (fmask pH1994) (cmask pH1994) (hmask pH1994) 1628 366 (true, H1994_cp2.1, H1994_cp2.2)) 1994 997 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1994_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1994_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1994_fin) true) H1994_seg1) H1994_seg2) (by decide) rfl H1994_fin ptTest_fst
noncomputable def I1994_cp1 : Nat × Nat := t7val% (fastRun pI1994 1 1150 (init pI1994) (init pI1994))
theorem I1994_seg1 : segOK pI1994 1 1150 (init pI1994) (init pI1994) I1994_cp1.1 I1994_cp1.2 = true := by
  decide +kernel
noncomputable def I1994_cp2 : Nat × Nat := t7val% (fastRun pI1994 1 1627 (init pI1994) (init pI1994))
theorem I1994_seg2 : segOK pI1994 1151 477 I1994_cp1.1 I1994_cp1.2 I1994_cp2.1 I1994_cp2.2 = true := by
  decide +kernel
theorem I1994_fin : (prmOK pI1994 1994 && intTest pI1994 (runFrom pI1994 (fmask pI1994) (cmask pI1994) (hmask pI1994) 1628 366 (true, I1994_cp2.1, I1994_cp2.2)) 1994 22 true) = true := by
  decide +kernel
theorem I1994_ok : RunOK pI1994 1994 (runFrom pI1994 (fmask pI1994) (cmask pI1994) (hmask pI1994) 1628 366 (true, I1994_cp2.1, I1994_cp2.2)) ∧ intTest pI1994 (runFrom pI1994 (fmask pI1994) (cmask pI1994) (hmask pI1994) 1628 366 (true, I1994_cp2.1, I1994_cp2.2)) 1994 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1994_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1994_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1994_fin) true) I1994_seg1) I1994_seg2) (by decide) rfl I1994_fin intTest_fst
theorem link1994 : linkOK pL1994 pH1994 pI1994 = true := by decide +kernel
theorem cvx1994 : ConvexBetweenHumps 1994 :=
  cvx_of L1994_ok H1994_ok I1994_ok link1994 (by decide)
theorem cenlink1994 : cenLinkOK pI1994 1994 = true := by decide +kernel
theorem cen1994 : CenterUniqueMin 1994 ∧ DipHyp 1994 ∧ OnePointHyps 1994 :=
  cen_of L1994_ok H1994_ok I1994_ok link1994 cenlink1994

/-! ### `N = 1995` -/

def pL1995 : Prm := ⟨81, 38, 40, 1997, 11, 18446744073709551616, 98534612268599343, 98534612268599343⟩
def pH1995 : Prm := ⟨81, 38, 40, 1997, 11, 18446744073709551616, 98535711780227119, 98535711780227119⟩
def pI1995 : Prm := ⟨68, 34, 31, 1997, 11, 18446744073709551616, 98534612268599343, 98535711780227119⟩
noncomputable def L1995_cp1 : Nat × Nat := t7val% (fastRun pL1995 1 1151 (init pL1995) (init pL1995))
theorem L1995_seg1 : segOK pL1995 1 1151 (init pL1995) (init pL1995) L1995_cp1.1 L1995_cp1.2 = true := by
  decide +kernel
noncomputable def L1995_cp2 : Nat × Nat := t7val% (fastRun pL1995 1 1628 (init pL1995) (init pL1995))
theorem L1995_seg2 : segOK pL1995 1152 477 L1995_cp1.1 L1995_cp1.2 L1995_cp2.1 L1995_cp2.2 = true := by
  decide +kernel
theorem L1995_fin : (prmOK pL1995 1995 && ptTest pL1995 (runFrom pL1995 (fmask pL1995) (cmask pL1995) (hmask pL1995) 1629 366 (true, L1995_cp2.1, L1995_cp2.2)) 1995 998 false) = true := by
  decide +kernel
theorem L1995_ok : RunOK pL1995 1995 (runFrom pL1995 (fmask pL1995) (cmask pL1995) (hmask pL1995) 1629 366 (true, L1995_cp2.1, L1995_cp2.2)) ∧ ptTest pL1995 (runFrom pL1995 (fmask pL1995) (cmask pL1995) (hmask pL1995) 1629 366 (true, L1995_cp2.1, L1995_cp2.2)) 1995 998 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1995_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1995_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1995_fin) true) L1995_seg1) L1995_seg2) (by decide) rfl L1995_fin ptTest_fst
noncomputable def H1995_cp1 : Nat × Nat := t7val% (fastRun pH1995 1 1151 (init pH1995) (init pH1995))
theorem H1995_seg1 : segOK pH1995 1 1151 (init pH1995) (init pH1995) H1995_cp1.1 H1995_cp1.2 = true := by
  decide +kernel
noncomputable def H1995_cp2 : Nat × Nat := t7val% (fastRun pH1995 1 1628 (init pH1995) (init pH1995))
theorem H1995_seg2 : segOK pH1995 1152 477 H1995_cp1.1 H1995_cp1.2 H1995_cp2.1 H1995_cp2.2 = true := by
  decide +kernel
theorem H1995_fin : (prmOK pH1995 1995 && ptTest pH1995 (runFrom pH1995 (fmask pH1995) (cmask pH1995) (hmask pH1995) 1629 366 (true, H1995_cp2.1, H1995_cp2.2)) 1995 998 true) = true := by
  decide +kernel
theorem H1995_ok : RunOK pH1995 1995 (runFrom pH1995 (fmask pH1995) (cmask pH1995) (hmask pH1995) 1629 366 (true, H1995_cp2.1, H1995_cp2.2)) ∧ ptTest pH1995 (runFrom pH1995 (fmask pH1995) (cmask pH1995) (hmask pH1995) 1629 366 (true, H1995_cp2.1, H1995_cp2.2)) 1995 998 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1995_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1995_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1995_fin) true) H1995_seg1) H1995_seg2) (by decide) rfl H1995_fin ptTest_fst
noncomputable def I1995_cp1 : Nat × Nat := t7val% (fastRun pI1995 1 1151 (init pI1995) (init pI1995))
theorem I1995_seg1 : segOK pI1995 1 1151 (init pI1995) (init pI1995) I1995_cp1.1 I1995_cp1.2 = true := by
  decide +kernel
noncomputable def I1995_cp2 : Nat × Nat := t7val% (fastRun pI1995 1 1628 (init pI1995) (init pI1995))
theorem I1995_seg2 : segOK pI1995 1152 477 I1995_cp1.1 I1995_cp1.2 I1995_cp2.1 I1995_cp2.2 = true := by
  decide +kernel
theorem I1995_fin : (prmOK pI1995 1995 && intTest pI1995 (runFrom pI1995 (fmask pI1995) (cmask pI1995) (hmask pI1995) 1629 366 (true, I1995_cp2.1, I1995_cp2.2)) 1995 22 false) = true := by
  decide +kernel
theorem I1995_ok : RunOK pI1995 1995 (runFrom pI1995 (fmask pI1995) (cmask pI1995) (hmask pI1995) 1629 366 (true, I1995_cp2.1, I1995_cp2.2)) ∧ intTest pI1995 (runFrom pI1995 (fmask pI1995) (cmask pI1995) (hmask pI1995) 1629 366 (true, I1995_cp2.1, I1995_cp2.2)) 1995 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1995_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1995_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1995_fin) true) I1995_seg1) I1995_seg2) (by decide) rfl I1995_fin intTest_fst
theorem link1995 : linkOK pL1995 pH1995 pI1995 = true := by decide +kernel
theorem cvx1995 : ConvexBetweenHumps 1995 :=
  cvx_of L1995_ok H1995_ok I1995_ok link1995 (by decide)

/-! ### `N = 1996` -/

def pL1996 : Prm := ⟨81, 38, 40, 1998, 11, 18446744073709551616, 98493982294081754, 98493982294081754⟩
def pH1996 : Prm := ⟨81, 38, 40, 1998, 11, 18446744073709551616, 98495081805709530, 98495081805709530⟩
def pI1996 : Prm := ⟨68, 34, 31, 1998, 11, 18446744073709551616, 98493982294081754, 98495081805709530⟩
noncomputable def L1996_cp1 : Nat × Nat := t7val% (fastRun pL1996 1 1151 (init pL1996) (init pL1996))
theorem L1996_seg1 : segOK pL1996 1 1151 (init pL1996) (init pL1996) L1996_cp1.1 L1996_cp1.2 = true := by
  decide +kernel
noncomputable def L1996_cp2 : Nat × Nat := t7val% (fastRun pL1996 1 1629 (init pL1996) (init pL1996))
theorem L1996_seg2 : segOK pL1996 1152 478 L1996_cp1.1 L1996_cp1.2 L1996_cp2.1 L1996_cp2.2 = true := by
  decide +kernel
theorem L1996_fin : (prmOK pL1996 1996 && ptTest pL1996 (runFrom pL1996 (fmask pL1996) (cmask pL1996) (hmask pL1996) 1630 366 (true, L1996_cp2.1, L1996_cp2.2)) 1996 998 false) = true := by
  decide +kernel
theorem L1996_ok : RunOK pL1996 1996 (runFrom pL1996 (fmask pL1996) (cmask pL1996) (hmask pL1996) 1630 366 (true, L1996_cp2.1, L1996_cp2.2)) ∧ ptTest pL1996 (runFrom pL1996 (fmask pL1996) (cmask pL1996) (hmask pL1996) 1630 366 (true, L1996_cp2.1, L1996_cp2.2)) 1996 998 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1996_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1996_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1996_fin) true) L1996_seg1) L1996_seg2) (by decide) rfl L1996_fin ptTest_fst
noncomputable def H1996_cp1 : Nat × Nat := t7val% (fastRun pH1996 1 1151 (init pH1996) (init pH1996))
theorem H1996_seg1 : segOK pH1996 1 1151 (init pH1996) (init pH1996) H1996_cp1.1 H1996_cp1.2 = true := by
  decide +kernel
noncomputable def H1996_cp2 : Nat × Nat := t7val% (fastRun pH1996 1 1629 (init pH1996) (init pH1996))
theorem H1996_seg2 : segOK pH1996 1152 478 H1996_cp1.1 H1996_cp1.2 H1996_cp2.1 H1996_cp2.2 = true := by
  decide +kernel
theorem H1996_fin : (prmOK pH1996 1996 && ptTest pH1996 (runFrom pH1996 (fmask pH1996) (cmask pH1996) (hmask pH1996) 1630 366 (true, H1996_cp2.1, H1996_cp2.2)) 1996 998 true) = true := by
  decide +kernel
theorem H1996_ok : RunOK pH1996 1996 (runFrom pH1996 (fmask pH1996) (cmask pH1996) (hmask pH1996) 1630 366 (true, H1996_cp2.1, H1996_cp2.2)) ∧ ptTest pH1996 (runFrom pH1996 (fmask pH1996) (cmask pH1996) (hmask pH1996) 1630 366 (true, H1996_cp2.1, H1996_cp2.2)) 1996 998 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1996_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1996_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1996_fin) true) H1996_seg1) H1996_seg2) (by decide) rfl H1996_fin ptTest_fst
noncomputable def I1996_cp1 : Nat × Nat := t7val% (fastRun pI1996 1 1151 (init pI1996) (init pI1996))
theorem I1996_seg1 : segOK pI1996 1 1151 (init pI1996) (init pI1996) I1996_cp1.1 I1996_cp1.2 = true := by
  decide +kernel
noncomputable def I1996_cp2 : Nat × Nat := t7val% (fastRun pI1996 1 1629 (init pI1996) (init pI1996))
theorem I1996_seg2 : segOK pI1996 1152 478 I1996_cp1.1 I1996_cp1.2 I1996_cp2.1 I1996_cp2.2 = true := by
  decide +kernel
theorem I1996_fin : (prmOK pI1996 1996 && intTest pI1996 (runFrom pI1996 (fmask pI1996) (cmask pI1996) (hmask pI1996) 1630 366 (true, I1996_cp2.1, I1996_cp2.2)) 1996 22 true) = true := by
  decide +kernel
theorem I1996_ok : RunOK pI1996 1996 (runFrom pI1996 (fmask pI1996) (cmask pI1996) (hmask pI1996) 1630 366 (true, I1996_cp2.1, I1996_cp2.2)) ∧ intTest pI1996 (runFrom pI1996 (fmask pI1996) (cmask pI1996) (hmask pI1996) 1630 366 (true, I1996_cp2.1, I1996_cp2.2)) 1996 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1996_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1996_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1996_fin) true) I1996_seg1) I1996_seg2) (by decide) rfl I1996_fin intTest_fst
theorem link1996 : linkOK pL1996 pH1996 pI1996 = true := by decide +kernel
theorem cvx1996 : ConvexBetweenHumps 1996 :=
  cvx_of L1996_ok H1996_ok I1996_ok link1996 (by decide)
theorem cenlink1996 : cenLinkOK pI1996 1996 = true := by decide +kernel
theorem cen1996 : CenterUniqueMin 1996 ∧ DipHyp 1996 ∧ OnePointHyps 1996 :=
  cen_of L1996_ok H1996_ok I1996_ok link1996 cenlink1996

/-! ### `N = 1997` -/

def pL1997 : Prm := ⟨81, 38, 40, 1999, 11, 18446744073709551616, 98453374592328981, 98453374592328981⟩
def pH1997 : Prm := ⟨81, 38, 40, 1999, 11, 18446744073709551616, 98454474103956757, 98454474103956757⟩
def pI1997 : Prm := ⟨68, 34, 31, 1999, 11, 18446744073709551616, 98453374592328981, 98454474103956757⟩
noncomputable def L1997_cp1 : Nat × Nat := t7val% (fastRun pL1997 1 1152 (init pL1997) (init pL1997))
theorem L1997_seg1 : segOK pL1997 1 1152 (init pL1997) (init pL1997) L1997_cp1.1 L1997_cp1.2 = true := by
  decide +kernel
noncomputable def L1997_cp2 : Nat × Nat := t7val% (fastRun pL1997 1 1630 (init pL1997) (init pL1997))
theorem L1997_seg2 : segOK pL1997 1153 478 L1997_cp1.1 L1997_cp1.2 L1997_cp2.1 L1997_cp2.2 = true := by
  decide +kernel
theorem L1997_fin : (prmOK pL1997 1997 && ptTest pL1997 (runFrom pL1997 (fmask pL1997) (cmask pL1997) (hmask pL1997) 1631 366 (true, L1997_cp2.1, L1997_cp2.2)) 1997 999 false) = true := by
  decide +kernel
theorem L1997_ok : RunOK pL1997 1997 (runFrom pL1997 (fmask pL1997) (cmask pL1997) (hmask pL1997) 1631 366 (true, L1997_cp2.1, L1997_cp2.2)) ∧ ptTest pL1997 (runFrom pL1997 (fmask pL1997) (cmask pL1997) (hmask pL1997) 1631 366 (true, L1997_cp2.1, L1997_cp2.2)) 1997 999 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1997_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1997_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1997_fin) true) L1997_seg1) L1997_seg2) (by decide) rfl L1997_fin ptTest_fst
noncomputable def H1997_cp1 : Nat × Nat := t7val% (fastRun pH1997 1 1152 (init pH1997) (init pH1997))
theorem H1997_seg1 : segOK pH1997 1 1152 (init pH1997) (init pH1997) H1997_cp1.1 H1997_cp1.2 = true := by
  decide +kernel
noncomputable def H1997_cp2 : Nat × Nat := t7val% (fastRun pH1997 1 1630 (init pH1997) (init pH1997))
theorem H1997_seg2 : segOK pH1997 1153 478 H1997_cp1.1 H1997_cp1.2 H1997_cp2.1 H1997_cp2.2 = true := by
  decide +kernel
theorem H1997_fin : (prmOK pH1997 1997 && ptTest pH1997 (runFrom pH1997 (fmask pH1997) (cmask pH1997) (hmask pH1997) 1631 366 (true, H1997_cp2.1, H1997_cp2.2)) 1997 999 true) = true := by
  decide +kernel
theorem H1997_ok : RunOK pH1997 1997 (runFrom pH1997 (fmask pH1997) (cmask pH1997) (hmask pH1997) 1631 366 (true, H1997_cp2.1, H1997_cp2.2)) ∧ ptTest pH1997 (runFrom pH1997 (fmask pH1997) (cmask pH1997) (hmask pH1997) 1631 366 (true, H1997_cp2.1, H1997_cp2.2)) 1997 999 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1997_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1997_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1997_fin) true) H1997_seg1) H1997_seg2) (by decide) rfl H1997_fin ptTest_fst
noncomputable def I1997_cp1 : Nat × Nat := t7val% (fastRun pI1997 1 1152 (init pI1997) (init pI1997))
theorem I1997_seg1 : segOK pI1997 1 1152 (init pI1997) (init pI1997) I1997_cp1.1 I1997_cp1.2 = true := by
  decide +kernel
noncomputable def I1997_cp2 : Nat × Nat := t7val% (fastRun pI1997 1 1630 (init pI1997) (init pI1997))
theorem I1997_seg2 : segOK pI1997 1153 478 I1997_cp1.1 I1997_cp1.2 I1997_cp2.1 I1997_cp2.2 = true := by
  decide +kernel
theorem I1997_fin : (prmOK pI1997 1997 && intTest pI1997 (runFrom pI1997 (fmask pI1997) (cmask pI1997) (hmask pI1997) 1631 366 (true, I1997_cp2.1, I1997_cp2.2)) 1997 22 false) = true := by
  decide +kernel
theorem I1997_ok : RunOK pI1997 1997 (runFrom pI1997 (fmask pI1997) (cmask pI1997) (hmask pI1997) 1631 366 (true, I1997_cp2.1, I1997_cp2.2)) ∧ intTest pI1997 (runFrom pI1997 (fmask pI1997) (cmask pI1997) (hmask pI1997) 1631 366 (true, I1997_cp2.1, I1997_cp2.2)) 1997 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1997_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1997_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1997_fin) true) I1997_seg1) I1997_seg2) (by decide) rfl I1997_fin intTest_fst
theorem link1997 : linkOK pL1997 pH1997 pI1997 = true := by decide +kernel
theorem cvx1997 : ConvexBetweenHumps 1997 :=
  cvx_of L1997_ok H1997_ok I1997_ok link1997 (by decide)

/-! ### `N = 1998` -/

def pL1998 : Prm := ⟨81, 38, 40, 2000, 11, 18446744073709551616, 98412817190327845, 98412817190327845⟩
def pH1998 : Prm := ⟨81, 38, 40, 2000, 11, 18446744073709551616, 98413916701955621, 98413916701955621⟩
def pI1998 : Prm := ⟨68, 34, 31, 2000, 11, 18446744073709551616, 98412817190327845, 98413916701955621⟩
noncomputable def L1998_cp1 : Nat × Nat := t7val% (fastRun pL1998 1 998 (init pL1998) (init pL1998))
theorem L1998_seg1 : segOK pL1998 1 998 (init pL1998) (init pL1998) L1998_cp1.1 L1998_cp1.2 = true := by
  decide +kernel
noncomputable def L1998_cp2 : Nat × Nat := t7val% (fastRun pL1998 1 1412 (init pL1998) (init pL1998))
theorem L1998_seg2 : segOK pL1998 999 414 L1998_cp1.1 L1998_cp1.2 L1998_cp2.1 L1998_cp2.2 = true := by
  decide +kernel
noncomputable def L1998_cp3 : Nat × Nat := t7val% (fastRun pL1998 1 1729 (init pL1998) (init pL1998))
theorem L1998_seg3 : segOK pL1998 1413 317 L1998_cp2.1 L1998_cp2.2 L1998_cp3.1 L1998_cp3.2 = true := by
  decide +kernel
theorem L1998_fin : (prmOK pL1998 1998 && ptTest pL1998 (runFrom pL1998 (fmask pL1998) (cmask pL1998) (hmask pL1998) 1730 268 (true, L1998_cp3.1, L1998_cp3.2)) 1998 999 false) = true := by
  decide +kernel
theorem L1998_ok : RunOK pL1998 1998 (runFrom pL1998 (fmask pL1998) (cmask pL1998) (hmask pL1998) 1730 268 (true, L1998_cp3.1, L1998_cp3.2)) ∧ ptTest pL1998 (runFrom pL1998 (fmask pL1998) (cmask pL1998) (hmask pL1998) 1730 268 (true, L1998_cp3.1, L1998_cp3.2)) 1998 999 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1998_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1998_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1998_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1998_fin) true) L1998_seg1) L1998_seg2) L1998_seg3) (by decide) rfl L1998_fin ptTest_fst
noncomputable def H1998_cp1 : Nat × Nat := t7val% (fastRun pH1998 1 998 (init pH1998) (init pH1998))
theorem H1998_seg1 : segOK pH1998 1 998 (init pH1998) (init pH1998) H1998_cp1.1 H1998_cp1.2 = true := by
  decide +kernel
noncomputable def H1998_cp2 : Nat × Nat := t7val% (fastRun pH1998 1 1412 (init pH1998) (init pH1998))
theorem H1998_seg2 : segOK pH1998 999 414 H1998_cp1.1 H1998_cp1.2 H1998_cp2.1 H1998_cp2.2 = true := by
  decide +kernel
noncomputable def H1998_cp3 : Nat × Nat := t7val% (fastRun pH1998 1 1729 (init pH1998) (init pH1998))
theorem H1998_seg3 : segOK pH1998 1413 317 H1998_cp2.1 H1998_cp2.2 H1998_cp3.1 H1998_cp3.2 = true := by
  decide +kernel
theorem H1998_fin : (prmOK pH1998 1998 && ptTest pH1998 (runFrom pH1998 (fmask pH1998) (cmask pH1998) (hmask pH1998) 1730 268 (true, H1998_cp3.1, H1998_cp3.2)) 1998 999 true) = true := by
  decide +kernel
theorem H1998_ok : RunOK pH1998 1998 (runFrom pH1998 (fmask pH1998) (cmask pH1998) (hmask pH1998) 1730 268 (true, H1998_cp3.1, H1998_cp3.2)) ∧ ptTest pH1998 (runFrom pH1998 (fmask pH1998) (cmask pH1998) (hmask pH1998) 1730 268 (true, H1998_cp3.1, H1998_cp3.2)) 1998 999 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1998_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1998_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1998_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1998_fin) true) H1998_seg1) H1998_seg2) H1998_seg3) (by decide) rfl H1998_fin ptTest_fst
noncomputable def I1998_cp1 : Nat × Nat := t7val% (fastRun pI1998 1 1153 (init pI1998) (init pI1998))
theorem I1998_seg1 : segOK pI1998 1 1153 (init pI1998) (init pI1998) I1998_cp1.1 I1998_cp1.2 = true := by
  decide +kernel
noncomputable def I1998_cp2 : Nat × Nat := t7val% (fastRun pI1998 1 1630 (init pI1998) (init pI1998))
theorem I1998_seg2 : segOK pI1998 1154 477 I1998_cp1.1 I1998_cp1.2 I1998_cp2.1 I1998_cp2.2 = true := by
  decide +kernel
theorem I1998_fin : (prmOK pI1998 1998 && intTest pI1998 (runFrom pI1998 (fmask pI1998) (cmask pI1998) (hmask pI1998) 1631 367 (true, I1998_cp2.1, I1998_cp2.2)) 1998 22 true) = true := by
  decide +kernel
theorem I1998_ok : RunOK pI1998 1998 (runFrom pI1998 (fmask pI1998) (cmask pI1998) (hmask pI1998) 1631 367 (true, I1998_cp2.1, I1998_cp2.2)) ∧ intTest pI1998 (runFrom pI1998 (fmask pI1998) (cmask pI1998) (hmask pI1998) 1631 367 (true, I1998_cp2.1, I1998_cp2.2)) 1998 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1998_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1998_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1998_fin) true) I1998_seg1) I1998_seg2) (by decide) rfl I1998_fin intTest_fst
theorem link1998 : linkOK pL1998 pH1998 pI1998 = true := by decide +kernel
theorem cvx1998 : ConvexBetweenHumps 1998 :=
  cvx_of L1998_ok H1998_ok I1998_ok link1998 (by decide)
theorem cenlink1998 : cenLinkOK pI1998 1998 = true := by decide +kernel
theorem cen1998 : CenterUniqueMin 1998 ∧ DipHyp 1998 ∧ OnePointHyps 1998 :=
  cen_of L1998_ok H1998_ok I1998_ok link1998 cenlink1998

/-! ### `N = 1999` -/

def pL1999 : Prm := ⟨81, 38, 40, 2001, 11, 18446744073709551616, 98372282003629916, 98372282003629916⟩
def pH1999 : Prm := ⟨81, 38, 40, 2001, 11, 18446744073709551616, 98373381515257692, 98373381515257692⟩
def pI1999 : Prm := ⟨68, 34, 31, 2001, 11, 18446744073709551616, 98372282003629916, 98373381515257692⟩
noncomputable def L1999_cp1 : Nat × Nat := t7val% (fastRun pL1999 1 999 (init pL1999) (init pL1999))
theorem L1999_seg1 : segOK pL1999 1 999 (init pL1999) (init pL1999) L1999_cp1.1 L1999_cp1.2 = true := by
  decide +kernel
noncomputable def L1999_cp2 : Nat × Nat := t7val% (fastRun pL1999 1 1413 (init pL1999) (init pL1999))
theorem L1999_seg2 : segOK pL1999 1000 414 L1999_cp1.1 L1999_cp1.2 L1999_cp2.1 L1999_cp2.2 = true := by
  decide +kernel
noncomputable def L1999_cp3 : Nat × Nat := t7val% (fastRun pL1999 1 1730 (init pL1999) (init pL1999))
theorem L1999_seg3 : segOK pL1999 1414 317 L1999_cp2.1 L1999_cp2.2 L1999_cp3.1 L1999_cp3.2 = true := by
  decide +kernel
theorem L1999_fin : (prmOK pL1999 1999 && ptTest pL1999 (runFrom pL1999 (fmask pL1999) (cmask pL1999) (hmask pL1999) 1731 268 (true, L1999_cp3.1, L1999_cp3.2)) 1999 1000 false) = true := by
  decide +kernel
theorem L1999_ok : RunOK pL1999 1999 (runFrom pL1999 (fmask pL1999) (cmask pL1999) (hmask pL1999) 1731 268 (true, L1999_cp3.1, L1999_cp3.2)) ∧ ptTest pL1999 (runFrom pL1999 (fmask pL1999) (cmask pL1999) (hmask pL1999) 1731 268 (true, L1999_cp3.1, L1999_cp3.2)) 1999 1000 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1999_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1999_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1999_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1999_fin) true) L1999_seg1) L1999_seg2) L1999_seg3) (by decide) rfl L1999_fin ptTest_fst
noncomputable def H1999_cp1 : Nat × Nat := t7val% (fastRun pH1999 1 999 (init pH1999) (init pH1999))
theorem H1999_seg1 : segOK pH1999 1 999 (init pH1999) (init pH1999) H1999_cp1.1 H1999_cp1.2 = true := by
  decide +kernel
noncomputable def H1999_cp2 : Nat × Nat := t7val% (fastRun pH1999 1 1413 (init pH1999) (init pH1999))
theorem H1999_seg2 : segOK pH1999 1000 414 H1999_cp1.1 H1999_cp1.2 H1999_cp2.1 H1999_cp2.2 = true := by
  decide +kernel
noncomputable def H1999_cp3 : Nat × Nat := t7val% (fastRun pH1999 1 1730 (init pH1999) (init pH1999))
theorem H1999_seg3 : segOK pH1999 1414 317 H1999_cp2.1 H1999_cp2.2 H1999_cp3.1 H1999_cp3.2 = true := by
  decide +kernel
theorem H1999_fin : (prmOK pH1999 1999 && ptTest pH1999 (runFrom pH1999 (fmask pH1999) (cmask pH1999) (hmask pH1999) 1731 268 (true, H1999_cp3.1, H1999_cp3.2)) 1999 1000 true) = true := by
  decide +kernel
theorem H1999_ok : RunOK pH1999 1999 (runFrom pH1999 (fmask pH1999) (cmask pH1999) (hmask pH1999) 1731 268 (true, H1999_cp3.1, H1999_cp3.2)) ∧ ptTest pH1999 (runFrom pH1999 (fmask pH1999) (cmask pH1999) (hmask pH1999) 1731 268 (true, H1999_cp3.1, H1999_cp3.2)) 1999 1000 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1999_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1999_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1999_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1999_fin) true) H1999_seg1) H1999_seg2) H1999_seg3) (by decide) rfl H1999_fin ptTest_fst
noncomputable def I1999_cp1 : Nat × Nat := t7val% (fastRun pI1999 1 1153 (init pI1999) (init pI1999))
theorem I1999_seg1 : segOK pI1999 1 1153 (init pI1999) (init pI1999) I1999_cp1.1 I1999_cp1.2 = true := by
  decide +kernel
noncomputable def I1999_cp2 : Nat × Nat := t7val% (fastRun pI1999 1 1631 (init pI1999) (init pI1999))
theorem I1999_seg2 : segOK pI1999 1154 478 I1999_cp1.1 I1999_cp1.2 I1999_cp2.1 I1999_cp2.2 = true := by
  decide +kernel
theorem I1999_fin : (prmOK pI1999 1999 && intTest pI1999 (runFrom pI1999 (fmask pI1999) (cmask pI1999) (hmask pI1999) 1632 367 (true, I1999_cp2.1, I1999_cp2.2)) 1999 22 false) = true := by
  decide +kernel
theorem I1999_ok : RunOK pI1999 1999 (runFrom pI1999 (fmask pI1999) (cmask pI1999) (hmask pI1999) 1632 367 (true, I1999_cp2.1, I1999_cp2.2)) ∧ intTest pI1999 (runFrom pI1999 (fmask pI1999) (cmask pI1999) (hmask pI1999) 1632 367 (true, I1999_cp2.1, I1999_cp2.2)) 1999 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1999_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1999_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1999_fin) true) I1999_seg1) I1999_seg2) (by decide) rfl I1999_fin intTest_fst
theorem link1999 : linkOK pL1999 pH1999 pI1999 = true := by decide +kernel
theorem cvx1999 : ConvexBetweenHumps 1999 :=
  cvx_of L1999_ok H1999_ok I1999_ok link1999 (by decide)

/-! ### The range -/

theorem cvx_1990_1999 {N : ℕ} (h1 : 1990 ≤ N) (h2 : N ≤ 1999) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1994
  · by_cases h4 : N ≤ 1991
    · by_cases h6 : N ≤ 1990
      · obtain rfl : N = 1990 := by omega
        exact cvx1990
      · obtain rfl : N = 1991 := by omega
        exact cvx1991
    · by_cases h6 : N ≤ 1992
      · obtain rfl : N = 1992 := by omega
        exact cvx1992
      · by_cases h8 : N ≤ 1993
        · obtain rfl : N = 1993 := by omega
          exact cvx1993
        · obtain rfl : N = 1994 := by omega
          exact cvx1994
  · by_cases h4 : N ≤ 1996
    · by_cases h6 : N ≤ 1995
      · obtain rfl : N = 1995 := by omega
        exact cvx1995
      · obtain rfl : N = 1996 := by omega
        exact cvx1996
    · by_cases h6 : N ≤ 1997
      · obtain rfl : N = 1997 := by omega
        exact cvx1997
      · by_cases h8 : N ≤ 1998
        · obtain rfl : N = 1998 := by omega
          exact cvx1998
        · obtain rfl : N = 1999 := by omega
          exact cvx1999

theorem cen_1990_1999 {N : ℕ} (h1 : 1990 ≤ N) (h2 : N ≤ 1999) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1992
  · by_cases h4 : N ≤ 1990
    · obtain rfl : N = 1990 := by omega
      exact cen1990
    · obtain rfl : N = 1992 := by omega
      exact cen1992
  · by_cases h4 : N ≤ 1994
    · obtain rfl : N = 1994 := by omega
      exact cen1994
    · by_cases h6 : N ≤ 1996
      · obtain rfl : N = 1996 := by omega
        exact cen1996
      · obtain rfl : N = 1998 := by omega
        exact cen1998

end Kagey131.PaperD.T7
