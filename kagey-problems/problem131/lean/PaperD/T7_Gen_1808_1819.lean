import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1808, …, 1819` (generated)

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

/-! ### `N = 1808` -/

def pL1808 : Prm := ⟨80, 37, 40, 1810, 11, 18446744073709551616, 106833174152785470, 106833174152785470⟩
def pH1808 : Prm := ⟨80, 37, 40, 1810, 11, 18446744073709551616, 106834273664413246, 106834273664413246⟩
def pI1808 : Prm := ⟨67, 34, 30, 1810, 11, 18446744073709551616, 106833174152785470, 106834273664413246⟩
noncomputable def L1808_cp1 : Nat × Nat := t7val% (fastRun pL1808 1 1043 (init pL1808) (init pL1808))
theorem L1808_seg1 : segOK pL1808 1 1043 (init pL1808) (init pL1808) L1808_cp1.1 L1808_cp1.2 = true := by
  decide +kernel
noncomputable def L1808_cp2 : Nat × Nat := t7val% (fastRun pL1808 1 1475 (init pL1808) (init pL1808))
theorem L1808_seg2 : segOK pL1808 1044 432 L1808_cp1.1 L1808_cp1.2 L1808_cp2.1 L1808_cp2.2 = true := by
  decide +kernel
theorem L1808_fin : (prmOK pL1808 1808 && ptTest pL1808 (runFrom pL1808 (fmask pL1808) (cmask pL1808) (hmask pL1808) 1476 332 (true, L1808_cp2.1, L1808_cp2.2)) 1808 904 false) = true := by
  decide +kernel
theorem L1808_ok : RunOK pL1808 1808 (runFrom pL1808 (fmask pL1808) (cmask pL1808) (hmask pL1808) 1476 332 (true, L1808_cp2.1, L1808_cp2.2)) ∧ ptTest pL1808 (runFrom pL1808 (fmask pL1808) (cmask pL1808) (hmask pL1808) 1476 332 (true, L1808_cp2.1, L1808_cp2.2)) 1808 904 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1808_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1808_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1808_fin) true) L1808_seg1) L1808_seg2) (by decide) rfl L1808_fin ptTest_fst
noncomputable def H1808_cp1 : Nat × Nat := t7val% (fastRun pH1808 1 1043 (init pH1808) (init pH1808))
theorem H1808_seg1 : segOK pH1808 1 1043 (init pH1808) (init pH1808) H1808_cp1.1 H1808_cp1.2 = true := by
  decide +kernel
noncomputable def H1808_cp2 : Nat × Nat := t7val% (fastRun pH1808 1 1475 (init pH1808) (init pH1808))
theorem H1808_seg2 : segOK pH1808 1044 432 H1808_cp1.1 H1808_cp1.2 H1808_cp2.1 H1808_cp2.2 = true := by
  decide +kernel
theorem H1808_fin : (prmOK pH1808 1808 && ptTest pH1808 (runFrom pH1808 (fmask pH1808) (cmask pH1808) (hmask pH1808) 1476 332 (true, H1808_cp2.1, H1808_cp2.2)) 1808 904 true) = true := by
  decide +kernel
theorem H1808_ok : RunOK pH1808 1808 (runFrom pH1808 (fmask pH1808) (cmask pH1808) (hmask pH1808) 1476 332 (true, H1808_cp2.1, H1808_cp2.2)) ∧ ptTest pH1808 (runFrom pH1808 (fmask pH1808) (cmask pH1808) (hmask pH1808) 1476 332 (true, H1808_cp2.1, H1808_cp2.2)) 1808 904 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1808_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1808_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1808_fin) true) H1808_seg1) H1808_seg2) (by decide) rfl H1808_fin ptTest_fst
noncomputable def I1808_cp1 : Nat × Nat := t7val% (fastRun pI1808 1 1043 (init pI1808) (init pI1808))
theorem I1808_seg1 : segOK pI1808 1 1043 (init pI1808) (init pI1808) I1808_cp1.1 I1808_cp1.2 = true := by
  decide +kernel
noncomputable def I1808_cp2 : Nat × Nat := t7val% (fastRun pI1808 1 1475 (init pI1808) (init pI1808))
theorem I1808_seg2 : segOK pI1808 1044 432 I1808_cp1.1 I1808_cp1.2 I1808_cp2.1 I1808_cp2.2 = true := by
  decide +kernel
theorem I1808_fin : (prmOK pI1808 1808 && intTest pI1808 (runFrom pI1808 (fmask pI1808) (cmask pI1808) (hmask pI1808) 1476 332 (true, I1808_cp2.1, I1808_cp2.2)) 1808 21 true) = true := by
  decide +kernel
theorem I1808_ok : RunOK pI1808 1808 (runFrom pI1808 (fmask pI1808) (cmask pI1808) (hmask pI1808) 1476 332 (true, I1808_cp2.1, I1808_cp2.2)) ∧ intTest pI1808 (runFrom pI1808 (fmask pI1808) (cmask pI1808) (hmask pI1808) 1476 332 (true, I1808_cp2.1, I1808_cp2.2)) 1808 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1808_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1808_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1808_fin) true) I1808_seg1) I1808_seg2) (by decide) rfl I1808_fin intTest_fst
theorem link1808 : linkOK pL1808 pH1808 pI1808 = true := by decide +kernel
theorem cvx1808 : ConvexBetweenHumps 1808 :=
  cvx_of L1808_ok H1808_ok I1808_ok link1808 (by decide)
theorem cenlink1808 : cenLinkOK pI1808 1808 = true := by decide +kernel
theorem cen1808 : CenterUniqueMin 1808 ∧ DipHyp 1808 ∧ OnePointHyps 1808 :=
  cen_of L1808_ok H1808_ok I1808_ok link1808 cenlink1808

/-! ### `N = 1809` -/

def pL1809 : Prm := ⟨80, 37, 40, 1811, 11, 18446744073709551616, 106784736897711899, 106784736897711899⟩
def pH1809 : Prm := ⟨80, 37, 40, 1811, 11, 18446744073709551616, 106785836409339675, 106785836409339675⟩
def pI1809 : Prm := ⟨67, 34, 30, 1811, 11, 18446744073709551616, 106784736897711899, 106785836409339675⟩
noncomputable def L1809_cp1 : Nat × Nat := t7val% (fastRun pL1809 1 1043 (init pL1809) (init pL1809))
theorem L1809_seg1 : segOK pL1809 1 1043 (init pL1809) (init pL1809) L1809_cp1.1 L1809_cp1.2 = true := by
  decide +kernel
noncomputable def L1809_cp2 : Nat × Nat := t7val% (fastRun pL1809 1 1476 (init pL1809) (init pL1809))
theorem L1809_seg2 : segOK pL1809 1044 433 L1809_cp1.1 L1809_cp1.2 L1809_cp2.1 L1809_cp2.2 = true := by
  decide +kernel
theorem L1809_fin : (prmOK pL1809 1809 && ptTest pL1809 (runFrom pL1809 (fmask pL1809) (cmask pL1809) (hmask pL1809) 1477 332 (true, L1809_cp2.1, L1809_cp2.2)) 1809 905 false) = true := by
  decide +kernel
theorem L1809_ok : RunOK pL1809 1809 (runFrom pL1809 (fmask pL1809) (cmask pL1809) (hmask pL1809) 1477 332 (true, L1809_cp2.1, L1809_cp2.2)) ∧ ptTest pL1809 (runFrom pL1809 (fmask pL1809) (cmask pL1809) (hmask pL1809) 1477 332 (true, L1809_cp2.1, L1809_cp2.2)) 1809 905 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1809_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1809_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1809_fin) true) L1809_seg1) L1809_seg2) (by decide) rfl L1809_fin ptTest_fst
noncomputable def H1809_cp1 : Nat × Nat := t7val% (fastRun pH1809 1 1043 (init pH1809) (init pH1809))
theorem H1809_seg1 : segOK pH1809 1 1043 (init pH1809) (init pH1809) H1809_cp1.1 H1809_cp1.2 = true := by
  decide +kernel
noncomputable def H1809_cp2 : Nat × Nat := t7val% (fastRun pH1809 1 1476 (init pH1809) (init pH1809))
theorem H1809_seg2 : segOK pH1809 1044 433 H1809_cp1.1 H1809_cp1.2 H1809_cp2.1 H1809_cp2.2 = true := by
  decide +kernel
theorem H1809_fin : (prmOK pH1809 1809 && ptTest pH1809 (runFrom pH1809 (fmask pH1809) (cmask pH1809) (hmask pH1809) 1477 332 (true, H1809_cp2.1, H1809_cp2.2)) 1809 905 true) = true := by
  decide +kernel
theorem H1809_ok : RunOK pH1809 1809 (runFrom pH1809 (fmask pH1809) (cmask pH1809) (hmask pH1809) 1477 332 (true, H1809_cp2.1, H1809_cp2.2)) ∧ ptTest pH1809 (runFrom pH1809 (fmask pH1809) (cmask pH1809) (hmask pH1809) 1477 332 (true, H1809_cp2.1, H1809_cp2.2)) 1809 905 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1809_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1809_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1809_fin) true) H1809_seg1) H1809_seg2) (by decide) rfl H1809_fin ptTest_fst
noncomputable def I1809_cp1 : Nat × Nat := t7val% (fastRun pI1809 1 1043 (init pI1809) (init pI1809))
theorem I1809_seg1 : segOK pI1809 1 1043 (init pI1809) (init pI1809) I1809_cp1.1 I1809_cp1.2 = true := by
  decide +kernel
noncomputable def I1809_cp2 : Nat × Nat := t7val% (fastRun pI1809 1 1476 (init pI1809) (init pI1809))
theorem I1809_seg2 : segOK pI1809 1044 433 I1809_cp1.1 I1809_cp1.2 I1809_cp2.1 I1809_cp2.2 = true := by
  decide +kernel
theorem I1809_fin : (prmOK pI1809 1809 && intTest pI1809 (runFrom pI1809 (fmask pI1809) (cmask pI1809) (hmask pI1809) 1477 332 (true, I1809_cp2.1, I1809_cp2.2)) 1809 21 false) = true := by
  decide +kernel
theorem I1809_ok : RunOK pI1809 1809 (runFrom pI1809 (fmask pI1809) (cmask pI1809) (hmask pI1809) 1477 332 (true, I1809_cp2.1, I1809_cp2.2)) ∧ intTest pI1809 (runFrom pI1809 (fmask pI1809) (cmask pI1809) (hmask pI1809) 1477 332 (true, I1809_cp2.1, I1809_cp2.2)) 1809 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1809_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1809_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1809_fin) true) I1809_seg1) I1809_seg2) (by decide) rfl I1809_fin intTest_fst
theorem link1809 : linkOK pL1809 pH1809 pI1809 = true := by decide +kernel
theorem cvx1809 : ConvexBetweenHumps 1809 :=
  cvx_of L1809_ok H1809_ok I1809_ok link1809 (by decide)

/-! ### `N = 1810` -/

def pL1810 : Prm := ⟨80, 37, 40, 1812, 11, 18446744073709551616, 106736366229721284, 106736366229721284⟩
def pH1810 : Prm := ⟨80, 37, 40, 1812, 11, 18446744073709551616, 106737465741349060, 106737465741349060⟩
def pI1810 : Prm := ⟨67, 34, 30, 1812, 11, 18446744073709551616, 106736366229721284, 106737465741349060⟩
noncomputable def L1810_cp1 : Nat × Nat := t7val% (fastRun pL1810 1 1044 (init pL1810) (init pL1810))
theorem L1810_seg1 : segOK pL1810 1 1044 (init pL1810) (init pL1810) L1810_cp1.1 L1810_cp1.2 = true := by
  decide +kernel
noncomputable def L1810_cp2 : Nat × Nat := t7val% (fastRun pL1810 1 1477 (init pL1810) (init pL1810))
theorem L1810_seg2 : segOK pL1810 1045 433 L1810_cp1.1 L1810_cp1.2 L1810_cp2.1 L1810_cp2.2 = true := by
  decide +kernel
theorem L1810_fin : (prmOK pL1810 1810 && ptTest pL1810 (runFrom pL1810 (fmask pL1810) (cmask pL1810) (hmask pL1810) 1478 332 (true, L1810_cp2.1, L1810_cp2.2)) 1810 905 false) = true := by
  decide +kernel
theorem L1810_ok : RunOK pL1810 1810 (runFrom pL1810 (fmask pL1810) (cmask pL1810) (hmask pL1810) 1478 332 (true, L1810_cp2.1, L1810_cp2.2)) ∧ ptTest pL1810 (runFrom pL1810 (fmask pL1810) (cmask pL1810) (hmask pL1810) 1478 332 (true, L1810_cp2.1, L1810_cp2.2)) 1810 905 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1810_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1810_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1810_fin) true) L1810_seg1) L1810_seg2) (by decide) rfl L1810_fin ptTest_fst
noncomputable def H1810_cp1 : Nat × Nat := t7val% (fastRun pH1810 1 1044 (init pH1810) (init pH1810))
theorem H1810_seg1 : segOK pH1810 1 1044 (init pH1810) (init pH1810) H1810_cp1.1 H1810_cp1.2 = true := by
  decide +kernel
noncomputable def H1810_cp2 : Nat × Nat := t7val% (fastRun pH1810 1 1477 (init pH1810) (init pH1810))
theorem H1810_seg2 : segOK pH1810 1045 433 H1810_cp1.1 H1810_cp1.2 H1810_cp2.1 H1810_cp2.2 = true := by
  decide +kernel
theorem H1810_fin : (prmOK pH1810 1810 && ptTest pH1810 (runFrom pH1810 (fmask pH1810) (cmask pH1810) (hmask pH1810) 1478 332 (true, H1810_cp2.1, H1810_cp2.2)) 1810 905 true) = true := by
  decide +kernel
theorem H1810_ok : RunOK pH1810 1810 (runFrom pH1810 (fmask pH1810) (cmask pH1810) (hmask pH1810) 1478 332 (true, H1810_cp2.1, H1810_cp2.2)) ∧ ptTest pH1810 (runFrom pH1810 (fmask pH1810) (cmask pH1810) (hmask pH1810) 1478 332 (true, H1810_cp2.1, H1810_cp2.2)) 1810 905 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1810_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1810_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1810_fin) true) H1810_seg1) H1810_seg2) (by decide) rfl H1810_fin ptTest_fst
noncomputable def I1810_cp1 : Nat × Nat := t7val% (fastRun pI1810 1 1044 (init pI1810) (init pI1810))
theorem I1810_seg1 : segOK pI1810 1 1044 (init pI1810) (init pI1810) I1810_cp1.1 I1810_cp1.2 = true := by
  decide +kernel
noncomputable def I1810_cp2 : Nat × Nat := t7val% (fastRun pI1810 1 1477 (init pI1810) (init pI1810))
theorem I1810_seg2 : segOK pI1810 1045 433 I1810_cp1.1 I1810_cp1.2 I1810_cp2.1 I1810_cp2.2 = true := by
  decide +kernel
theorem I1810_fin : (prmOK pI1810 1810 && intTest pI1810 (runFrom pI1810 (fmask pI1810) (cmask pI1810) (hmask pI1810) 1478 332 (true, I1810_cp2.1, I1810_cp2.2)) 1810 21 true) = true := by
  decide +kernel
theorem I1810_ok : RunOK pI1810 1810 (runFrom pI1810 (fmask pI1810) (cmask pI1810) (hmask pI1810) 1478 332 (true, I1810_cp2.1, I1810_cp2.2)) ∧ intTest pI1810 (runFrom pI1810 (fmask pI1810) (cmask pI1810) (hmask pI1810) 1478 332 (true, I1810_cp2.1, I1810_cp2.2)) 1810 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1810_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1810_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1810_fin) true) I1810_seg1) I1810_seg2) (by decide) rfl I1810_fin intTest_fst
theorem link1810 : linkOK pL1810 pH1810 pI1810 = true := by decide +kernel
theorem cvx1810 : ConvexBetweenHumps 1810 :=
  cvx_of L1810_ok H1810_ok I1810_ok link1810 (by decide)
theorem cenlink1810 : cenLinkOK pI1810 1810 = true := by decide +kernel
theorem cen1810 : CenterUniqueMin 1810 ∧ DipHyp 1810 ∧ OnePointHyps 1810 :=
  cen_of L1810_ok H1810_ok I1810_ok link1810 cenlink1810

/-! ### `N = 1811` -/

def pL1811 : Prm := ⟨80, 37, 40, 1813, 11, 18446744073709551616, 106688024199489186, 106688024199489186⟩
def pH1811 : Prm := ⟨80, 37, 40, 1813, 11, 18446744073709551616, 106689123711116962, 106689123711116962⟩
def pI1811 : Prm := ⟨67, 34, 30, 1813, 11, 18446744073709551616, 106688024199489186, 106689123711116962⟩
noncomputable def L1811_cp1 : Nat × Nat := t7val% (fastRun pL1811 1 1045 (init pL1811) (init pL1811))
theorem L1811_seg1 : segOK pL1811 1 1045 (init pL1811) (init pL1811) L1811_cp1.1 L1811_cp1.2 = true := by
  decide +kernel
noncomputable def L1811_cp2 : Nat × Nat := t7val% (fastRun pL1811 1 1478 (init pL1811) (init pL1811))
theorem L1811_seg2 : segOK pL1811 1046 433 L1811_cp1.1 L1811_cp1.2 L1811_cp2.1 L1811_cp2.2 = true := by
  decide +kernel
theorem L1811_fin : (prmOK pL1811 1811 && ptTest pL1811 (runFrom pL1811 (fmask pL1811) (cmask pL1811) (hmask pL1811) 1479 332 (true, L1811_cp2.1, L1811_cp2.2)) 1811 906 false) = true := by
  decide +kernel
theorem L1811_ok : RunOK pL1811 1811 (runFrom pL1811 (fmask pL1811) (cmask pL1811) (hmask pL1811) 1479 332 (true, L1811_cp2.1, L1811_cp2.2)) ∧ ptTest pL1811 (runFrom pL1811 (fmask pL1811) (cmask pL1811) (hmask pL1811) 1479 332 (true, L1811_cp2.1, L1811_cp2.2)) 1811 906 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1811_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1811_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1811_fin) true) L1811_seg1) L1811_seg2) (by decide) rfl L1811_fin ptTest_fst
noncomputable def H1811_cp1 : Nat × Nat := t7val% (fastRun pH1811 1 1045 (init pH1811) (init pH1811))
theorem H1811_seg1 : segOK pH1811 1 1045 (init pH1811) (init pH1811) H1811_cp1.1 H1811_cp1.2 = true := by
  decide +kernel
noncomputable def H1811_cp2 : Nat × Nat := t7val% (fastRun pH1811 1 1478 (init pH1811) (init pH1811))
theorem H1811_seg2 : segOK pH1811 1046 433 H1811_cp1.1 H1811_cp1.2 H1811_cp2.1 H1811_cp2.2 = true := by
  decide +kernel
theorem H1811_fin : (prmOK pH1811 1811 && ptTest pH1811 (runFrom pH1811 (fmask pH1811) (cmask pH1811) (hmask pH1811) 1479 332 (true, H1811_cp2.1, H1811_cp2.2)) 1811 906 true) = true := by
  decide +kernel
theorem H1811_ok : RunOK pH1811 1811 (runFrom pH1811 (fmask pH1811) (cmask pH1811) (hmask pH1811) 1479 332 (true, H1811_cp2.1, H1811_cp2.2)) ∧ ptTest pH1811 (runFrom pH1811 (fmask pH1811) (cmask pH1811) (hmask pH1811) 1479 332 (true, H1811_cp2.1, H1811_cp2.2)) 1811 906 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1811_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1811_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1811_fin) true) H1811_seg1) H1811_seg2) (by decide) rfl H1811_fin ptTest_fst
noncomputable def I1811_cp1 : Nat × Nat := t7val% (fastRun pI1811 1 1045 (init pI1811) (init pI1811))
theorem I1811_seg1 : segOK pI1811 1 1045 (init pI1811) (init pI1811) I1811_cp1.1 I1811_cp1.2 = true := by
  decide +kernel
noncomputable def I1811_cp2 : Nat × Nat := t7val% (fastRun pI1811 1 1478 (init pI1811) (init pI1811))
theorem I1811_seg2 : segOK pI1811 1046 433 I1811_cp1.1 I1811_cp1.2 I1811_cp2.1 I1811_cp2.2 = true := by
  decide +kernel
theorem I1811_fin : (prmOK pI1811 1811 && intTest pI1811 (runFrom pI1811 (fmask pI1811) (cmask pI1811) (hmask pI1811) 1479 332 (true, I1811_cp2.1, I1811_cp2.2)) 1811 21 false) = true := by
  decide +kernel
theorem I1811_ok : RunOK pI1811 1811 (runFrom pI1811 (fmask pI1811) (cmask pI1811) (hmask pI1811) 1479 332 (true, I1811_cp2.1, I1811_cp2.2)) ∧ intTest pI1811 (runFrom pI1811 (fmask pI1811) (cmask pI1811) (hmask pI1811) 1479 332 (true, I1811_cp2.1, I1811_cp2.2)) 1811 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1811_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1811_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1811_fin) true) I1811_seg1) I1811_seg2) (by decide) rfl I1811_fin intTest_fst
theorem link1811 : linkOK pL1811 pH1811 pI1811 = true := by decide +kernel
theorem cvx1811 : ConvexBetweenHumps 1811 :=
  cvx_of L1811_ok H1811_ok I1811_ok link1811 (by decide)

/-! ### `N = 1812` -/

def pL1812 : Prm := ⟨80, 37, 40, 1814, 11, 18446744073709551616, 106639748548020963, 106639748548020963⟩
def pH1812 : Prm := ⟨80, 37, 40, 1814, 11, 18446744073709551616, 106640848059648739, 106640848059648739⟩
def pI1812 : Prm := ⟨67, 34, 30, 1814, 11, 18446744073709551616, 106639748548020963, 106640848059648739⟩
noncomputable def L1812_cp1 : Nat × Nat := t7val% (fastRun pL1812 1 1045 (init pL1812) (init pL1812))
theorem L1812_seg1 : segOK pL1812 1 1045 (init pL1812) (init pL1812) L1812_cp1.1 L1812_cp1.2 = true := by
  decide +kernel
noncomputable def L1812_cp2 : Nat × Nat := t7val% (fastRun pL1812 1 1478 (init pL1812) (init pL1812))
theorem L1812_seg2 : segOK pL1812 1046 433 L1812_cp1.1 L1812_cp1.2 L1812_cp2.1 L1812_cp2.2 = true := by
  decide +kernel
theorem L1812_fin : (prmOK pL1812 1812 && ptTest pL1812 (runFrom pL1812 (fmask pL1812) (cmask pL1812) (hmask pL1812) 1479 333 (true, L1812_cp2.1, L1812_cp2.2)) 1812 906 false) = true := by
  decide +kernel
theorem L1812_ok : RunOK pL1812 1812 (runFrom pL1812 (fmask pL1812) (cmask pL1812) (hmask pL1812) 1479 333 (true, L1812_cp2.1, L1812_cp2.2)) ∧ ptTest pL1812 (runFrom pL1812 (fmask pL1812) (cmask pL1812) (hmask pL1812) 1479 333 (true, L1812_cp2.1, L1812_cp2.2)) 1812 906 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1812_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1812_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1812_fin) true) L1812_seg1) L1812_seg2) (by decide) rfl L1812_fin ptTest_fst
noncomputable def H1812_cp1 : Nat × Nat := t7val% (fastRun pH1812 1 1045 (init pH1812) (init pH1812))
theorem H1812_seg1 : segOK pH1812 1 1045 (init pH1812) (init pH1812) H1812_cp1.1 H1812_cp1.2 = true := by
  decide +kernel
noncomputable def H1812_cp2 : Nat × Nat := t7val% (fastRun pH1812 1 1478 (init pH1812) (init pH1812))
theorem H1812_seg2 : segOK pH1812 1046 433 H1812_cp1.1 H1812_cp1.2 H1812_cp2.1 H1812_cp2.2 = true := by
  decide +kernel
theorem H1812_fin : (prmOK pH1812 1812 && ptTest pH1812 (runFrom pH1812 (fmask pH1812) (cmask pH1812) (hmask pH1812) 1479 333 (true, H1812_cp2.1, H1812_cp2.2)) 1812 906 true) = true := by
  decide +kernel
theorem H1812_ok : RunOK pH1812 1812 (runFrom pH1812 (fmask pH1812) (cmask pH1812) (hmask pH1812) 1479 333 (true, H1812_cp2.1, H1812_cp2.2)) ∧ ptTest pH1812 (runFrom pH1812 (fmask pH1812) (cmask pH1812) (hmask pH1812) 1479 333 (true, H1812_cp2.1, H1812_cp2.2)) 1812 906 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1812_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1812_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1812_fin) true) H1812_seg1) H1812_seg2) (by decide) rfl H1812_fin ptTest_fst
noncomputable def I1812_cp1 : Nat × Nat := t7val% (fastRun pI1812 1 1045 (init pI1812) (init pI1812))
theorem I1812_seg1 : segOK pI1812 1 1045 (init pI1812) (init pI1812) I1812_cp1.1 I1812_cp1.2 = true := by
  decide +kernel
noncomputable def I1812_cp2 : Nat × Nat := t7val% (fastRun pI1812 1 1478 (init pI1812) (init pI1812))
theorem I1812_seg2 : segOK pI1812 1046 433 I1812_cp1.1 I1812_cp1.2 I1812_cp2.1 I1812_cp2.2 = true := by
  decide +kernel
theorem I1812_fin : (prmOK pI1812 1812 && intTest pI1812 (runFrom pI1812 (fmask pI1812) (cmask pI1812) (hmask pI1812) 1479 333 (true, I1812_cp2.1, I1812_cp2.2)) 1812 21 true) = true := by
  decide +kernel
theorem I1812_ok : RunOK pI1812 1812 (runFrom pI1812 (fmask pI1812) (cmask pI1812) (hmask pI1812) 1479 333 (true, I1812_cp2.1, I1812_cp2.2)) ∧ intTest pI1812 (runFrom pI1812 (fmask pI1812) (cmask pI1812) (hmask pI1812) 1479 333 (true, I1812_cp2.1, I1812_cp2.2)) 1812 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1812_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1812_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1812_fin) true) I1812_seg1) I1812_seg2) (by decide) rfl I1812_fin intTest_fst
theorem link1812 : linkOK pL1812 pH1812 pI1812 = true := by decide +kernel
theorem cvx1812 : ConvexBetweenHumps 1812 :=
  cvx_of L1812_ok H1812_ok I1812_ok link1812 (by decide)
theorem cenlink1812 : cenLinkOK pI1812 1812 = true := by decide +kernel
theorem cen1812 : CenterUniqueMin 1812 ∧ DipHyp 1812 ∧ OnePointHyps 1812 :=
  cen_of L1812_ok H1812_ok I1812_ok link1812 cenlink1812

/-! ### `N = 1813` -/

def pL1813 : Prm := ⟨80, 37, 40, 1815, 11, 18446744073709551616, 106591501453440733, 106591501453440733⟩
def pH1813 : Prm := ⟨80, 37, 40, 1815, 11, 18446744073709551616, 106592600965068509, 106592600965068509⟩
def pI1813 : Prm := ⟨67, 34, 30, 1815, 11, 18446744073709551616, 106591501453440733, 106592600965068509⟩
noncomputable def L1813_cp1 : Nat × Nat := t7val% (fastRun pL1813 1 1046 (init pL1813) (init pL1813))
theorem L1813_seg1 : segOK pL1813 1 1046 (init pL1813) (init pL1813) L1813_cp1.1 L1813_cp1.2 = true := by
  decide +kernel
noncomputable def L1813_cp2 : Nat × Nat := t7val% (fastRun pL1813 1 1479 (init pL1813) (init pL1813))
theorem L1813_seg2 : segOK pL1813 1047 433 L1813_cp1.1 L1813_cp1.2 L1813_cp2.1 L1813_cp2.2 = true := by
  decide +kernel
theorem L1813_fin : (prmOK pL1813 1813 && ptTest pL1813 (runFrom pL1813 (fmask pL1813) (cmask pL1813) (hmask pL1813) 1480 333 (true, L1813_cp2.1, L1813_cp2.2)) 1813 907 false) = true := by
  decide +kernel
theorem L1813_ok : RunOK pL1813 1813 (runFrom pL1813 (fmask pL1813) (cmask pL1813) (hmask pL1813) 1480 333 (true, L1813_cp2.1, L1813_cp2.2)) ∧ ptTest pL1813 (runFrom pL1813 (fmask pL1813) (cmask pL1813) (hmask pL1813) 1480 333 (true, L1813_cp2.1, L1813_cp2.2)) 1813 907 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1813_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1813_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1813_fin) true) L1813_seg1) L1813_seg2) (by decide) rfl L1813_fin ptTest_fst
noncomputable def H1813_cp1 : Nat × Nat := t7val% (fastRun pH1813 1 1046 (init pH1813) (init pH1813))
theorem H1813_seg1 : segOK pH1813 1 1046 (init pH1813) (init pH1813) H1813_cp1.1 H1813_cp1.2 = true := by
  decide +kernel
noncomputable def H1813_cp2 : Nat × Nat := t7val% (fastRun pH1813 1 1479 (init pH1813) (init pH1813))
theorem H1813_seg2 : segOK pH1813 1047 433 H1813_cp1.1 H1813_cp1.2 H1813_cp2.1 H1813_cp2.2 = true := by
  decide +kernel
theorem H1813_fin : (prmOK pH1813 1813 && ptTest pH1813 (runFrom pH1813 (fmask pH1813) (cmask pH1813) (hmask pH1813) 1480 333 (true, H1813_cp2.1, H1813_cp2.2)) 1813 907 true) = true := by
  decide +kernel
theorem H1813_ok : RunOK pH1813 1813 (runFrom pH1813 (fmask pH1813) (cmask pH1813) (hmask pH1813) 1480 333 (true, H1813_cp2.1, H1813_cp2.2)) ∧ ptTest pH1813 (runFrom pH1813 (fmask pH1813) (cmask pH1813) (hmask pH1813) 1480 333 (true, H1813_cp2.1, H1813_cp2.2)) 1813 907 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1813_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1813_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1813_fin) true) H1813_seg1) H1813_seg2) (by decide) rfl H1813_fin ptTest_fst
noncomputable def I1813_cp1 : Nat × Nat := t7val% (fastRun pI1813 1 1046 (init pI1813) (init pI1813))
theorem I1813_seg1 : segOK pI1813 1 1046 (init pI1813) (init pI1813) I1813_cp1.1 I1813_cp1.2 = true := by
  decide +kernel
noncomputable def I1813_cp2 : Nat × Nat := t7val% (fastRun pI1813 1 1479 (init pI1813) (init pI1813))
theorem I1813_seg2 : segOK pI1813 1047 433 I1813_cp1.1 I1813_cp1.2 I1813_cp2.1 I1813_cp2.2 = true := by
  decide +kernel
theorem I1813_fin : (prmOK pI1813 1813 && intTest pI1813 (runFrom pI1813 (fmask pI1813) (cmask pI1813) (hmask pI1813) 1480 333 (true, I1813_cp2.1, I1813_cp2.2)) 1813 21 false) = true := by
  decide +kernel
theorem I1813_ok : RunOK pI1813 1813 (runFrom pI1813 (fmask pI1813) (cmask pI1813) (hmask pI1813) 1480 333 (true, I1813_cp2.1, I1813_cp2.2)) ∧ intTest pI1813 (runFrom pI1813 (fmask pI1813) (cmask pI1813) (hmask pI1813) 1480 333 (true, I1813_cp2.1, I1813_cp2.2)) 1813 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1813_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1813_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1813_fin) true) I1813_seg1) I1813_seg2) (by decide) rfl I1813_fin intTest_fst
theorem link1813 : linkOK pL1813 pH1813 pI1813 = true := by decide +kernel
theorem cvx1813 : ConvexBetweenHumps 1813 :=
  cvx_of L1813_ok H1813_ok I1813_ok link1813 (by decide)

/-! ### `N = 1814` -/

def pL1814 : Prm := ⟨80, 37, 40, 1816, 11, 18446744073709551616, 106543320530153846, 106543320530153846⟩
def pH1814 : Prm := ⟨80, 37, 40, 1816, 11, 18446744073709551616, 106544420041781622, 106544420041781622⟩
def pI1814 : Prm := ⟨67, 34, 30, 1816, 11, 18446744073709551616, 106543320530153846, 106544420041781622⟩
noncomputable def L1814_cp1 : Nat × Nat := t7val% (fastRun pL1814 1 1046 (init pL1814) (init pL1814))
theorem L1814_seg1 : segOK pL1814 1 1046 (init pL1814) (init pL1814) L1814_cp1.1 L1814_cp1.2 = true := by
  decide +kernel
noncomputable def L1814_cp2 : Nat × Nat := t7val% (fastRun pL1814 1 1480 (init pL1814) (init pL1814))
theorem L1814_seg2 : segOK pL1814 1047 434 L1814_cp1.1 L1814_cp1.2 L1814_cp2.1 L1814_cp2.2 = true := by
  decide +kernel
theorem L1814_fin : (prmOK pL1814 1814 && ptTest pL1814 (runFrom pL1814 (fmask pL1814) (cmask pL1814) (hmask pL1814) 1481 333 (true, L1814_cp2.1, L1814_cp2.2)) 1814 907 false) = true := by
  decide +kernel
theorem L1814_ok : RunOK pL1814 1814 (runFrom pL1814 (fmask pL1814) (cmask pL1814) (hmask pL1814) 1481 333 (true, L1814_cp2.1, L1814_cp2.2)) ∧ ptTest pL1814 (runFrom pL1814 (fmask pL1814) (cmask pL1814) (hmask pL1814) 1481 333 (true, L1814_cp2.1, L1814_cp2.2)) 1814 907 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1814_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1814_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1814_fin) true) L1814_seg1) L1814_seg2) (by decide) rfl L1814_fin ptTest_fst
noncomputable def H1814_cp1 : Nat × Nat := t7val% (fastRun pH1814 1 1046 (init pH1814) (init pH1814))
theorem H1814_seg1 : segOK pH1814 1 1046 (init pH1814) (init pH1814) H1814_cp1.1 H1814_cp1.2 = true := by
  decide +kernel
noncomputable def H1814_cp2 : Nat × Nat := t7val% (fastRun pH1814 1 1480 (init pH1814) (init pH1814))
theorem H1814_seg2 : segOK pH1814 1047 434 H1814_cp1.1 H1814_cp1.2 H1814_cp2.1 H1814_cp2.2 = true := by
  decide +kernel
theorem H1814_fin : (prmOK pH1814 1814 && ptTest pH1814 (runFrom pH1814 (fmask pH1814) (cmask pH1814) (hmask pH1814) 1481 333 (true, H1814_cp2.1, H1814_cp2.2)) 1814 907 true) = true := by
  decide +kernel
theorem H1814_ok : RunOK pH1814 1814 (runFrom pH1814 (fmask pH1814) (cmask pH1814) (hmask pH1814) 1481 333 (true, H1814_cp2.1, H1814_cp2.2)) ∧ ptTest pH1814 (runFrom pH1814 (fmask pH1814) (cmask pH1814) (hmask pH1814) 1481 333 (true, H1814_cp2.1, H1814_cp2.2)) 1814 907 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1814_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1814_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1814_fin) true) H1814_seg1) H1814_seg2) (by decide) rfl H1814_fin ptTest_fst
noncomputable def I1814_cp1 : Nat × Nat := t7val% (fastRun pI1814 1 1046 (init pI1814) (init pI1814))
theorem I1814_seg1 : segOK pI1814 1 1046 (init pI1814) (init pI1814) I1814_cp1.1 I1814_cp1.2 = true := by
  decide +kernel
noncomputable def I1814_cp2 : Nat × Nat := t7val% (fastRun pI1814 1 1480 (init pI1814) (init pI1814))
theorem I1814_seg2 : segOK pI1814 1047 434 I1814_cp1.1 I1814_cp1.2 I1814_cp2.1 I1814_cp2.2 = true := by
  decide +kernel
theorem I1814_fin : (prmOK pI1814 1814 && intTest pI1814 (runFrom pI1814 (fmask pI1814) (cmask pI1814) (hmask pI1814) 1481 333 (true, I1814_cp2.1, I1814_cp2.2)) 1814 21 true) = true := by
  decide +kernel
theorem I1814_ok : RunOK pI1814 1814 (runFrom pI1814 (fmask pI1814) (cmask pI1814) (hmask pI1814) 1481 333 (true, I1814_cp2.1, I1814_cp2.2)) ∧ intTest pI1814 (runFrom pI1814 (fmask pI1814) (cmask pI1814) (hmask pI1814) 1481 333 (true, I1814_cp2.1, I1814_cp2.2)) 1814 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1814_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1814_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1814_fin) true) I1814_seg1) I1814_seg2) (by decide) rfl I1814_fin intTest_fst
theorem link1814 : linkOK pL1814 pH1814 pI1814 = true := by decide +kernel
theorem cvx1814 : ConvexBetweenHumps 1814 :=
  cvx_of L1814_ok H1814_ok I1814_ok link1814 (by decide)
theorem cenlink1814 : cenLinkOK pI1814 1814 = true := by decide +kernel
theorem cen1814 : CenterUniqueMin 1814 ∧ DipHyp 1814 ∧ OnePointHyps 1814 :=
  cen_of L1814_ok H1814_ok I1814_ok link1814 cenlink1814

/-! ### `N = 1815` -/

def pL1815 : Prm := ⟨80, 37, 40, 1817, 11, 18446744073709551616, 106495168083216466, 106495168083216466⟩
def pH1815 : Prm := ⟨80, 37, 40, 1817, 11, 18446744073709551616, 106496267594844242, 106496267594844242⟩
def pI1815 : Prm := ⟨68, 34, 31, 1817, 11, 18446744073709551616, 106495168083216466, 106496267594844242⟩
noncomputable def L1815_cp1 : Nat × Nat := t7val% (fastRun pL1815 1 1047 (init pL1815) (init pL1815))
theorem L1815_seg1 : segOK pL1815 1 1047 (init pL1815) (init pL1815) L1815_cp1.1 L1815_cp1.2 = true := by
  decide +kernel
noncomputable def L1815_cp2 : Nat × Nat := t7val% (fastRun pL1815 1 1481 (init pL1815) (init pL1815))
theorem L1815_seg2 : segOK pL1815 1048 434 L1815_cp1.1 L1815_cp1.2 L1815_cp2.1 L1815_cp2.2 = true := by
  decide +kernel
theorem L1815_fin : (prmOK pL1815 1815 && ptTest pL1815 (runFrom pL1815 (fmask pL1815) (cmask pL1815) (hmask pL1815) 1482 333 (true, L1815_cp2.1, L1815_cp2.2)) 1815 908 false) = true := by
  decide +kernel
theorem L1815_ok : RunOK pL1815 1815 (runFrom pL1815 (fmask pL1815) (cmask pL1815) (hmask pL1815) 1482 333 (true, L1815_cp2.1, L1815_cp2.2)) ∧ ptTest pL1815 (runFrom pL1815 (fmask pL1815) (cmask pL1815) (hmask pL1815) 1482 333 (true, L1815_cp2.1, L1815_cp2.2)) 1815 908 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1815_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1815_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1815_fin) true) L1815_seg1) L1815_seg2) (by decide) rfl L1815_fin ptTest_fst
noncomputable def H1815_cp1 : Nat × Nat := t7val% (fastRun pH1815 1 1047 (init pH1815) (init pH1815))
theorem H1815_seg1 : segOK pH1815 1 1047 (init pH1815) (init pH1815) H1815_cp1.1 H1815_cp1.2 = true := by
  decide +kernel
noncomputable def H1815_cp2 : Nat × Nat := t7val% (fastRun pH1815 1 1481 (init pH1815) (init pH1815))
theorem H1815_seg2 : segOK pH1815 1048 434 H1815_cp1.1 H1815_cp1.2 H1815_cp2.1 H1815_cp2.2 = true := by
  decide +kernel
theorem H1815_fin : (prmOK pH1815 1815 && ptTest pH1815 (runFrom pH1815 (fmask pH1815) (cmask pH1815) (hmask pH1815) 1482 333 (true, H1815_cp2.1, H1815_cp2.2)) 1815 908 true) = true := by
  decide +kernel
theorem H1815_ok : RunOK pH1815 1815 (runFrom pH1815 (fmask pH1815) (cmask pH1815) (hmask pH1815) 1482 333 (true, H1815_cp2.1, H1815_cp2.2)) ∧ ptTest pH1815 (runFrom pH1815 (fmask pH1815) (cmask pH1815) (hmask pH1815) 1482 333 (true, H1815_cp2.1, H1815_cp2.2)) 1815 908 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1815_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1815_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1815_fin) true) H1815_seg1) H1815_seg2) (by decide) rfl H1815_fin ptTest_fst
noncomputable def I1815_cp1 : Nat × Nat := t7val% (fastRun pI1815 1 1047 (init pI1815) (init pI1815))
theorem I1815_seg1 : segOK pI1815 1 1047 (init pI1815) (init pI1815) I1815_cp1.1 I1815_cp1.2 = true := by
  decide +kernel
noncomputable def I1815_cp2 : Nat × Nat := t7val% (fastRun pI1815 1 1481 (init pI1815) (init pI1815))
theorem I1815_seg2 : segOK pI1815 1048 434 I1815_cp1.1 I1815_cp1.2 I1815_cp2.1 I1815_cp2.2 = true := by
  decide +kernel
theorem I1815_fin : (prmOK pI1815 1815 && intTest pI1815 (runFrom pI1815 (fmask pI1815) (cmask pI1815) (hmask pI1815) 1482 333 (true, I1815_cp2.1, I1815_cp2.2)) 1815 21 false) = true := by
  decide +kernel
theorem I1815_ok : RunOK pI1815 1815 (runFrom pI1815 (fmask pI1815) (cmask pI1815) (hmask pI1815) 1482 333 (true, I1815_cp2.1, I1815_cp2.2)) ∧ intTest pI1815 (runFrom pI1815 (fmask pI1815) (cmask pI1815) (hmask pI1815) 1482 333 (true, I1815_cp2.1, I1815_cp2.2)) 1815 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1815_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1815_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1815_fin) true) I1815_seg1) I1815_seg2) (by decide) rfl I1815_fin intTest_fst
theorem link1815 : linkOK pL1815 pH1815 pI1815 = true := by decide +kernel
theorem cvx1815 : ConvexBetweenHumps 1815 :=
  cvx_of L1815_ok H1815_ok I1815_ok link1815 (by decide)

/-! ### `N = 1816` -/

def pL1816 : Prm := ⟨80, 37, 40, 1818, 11, 18446744073709551616, 106447081600987344, 106447081600987344⟩
def pH1816 : Prm := ⟨80, 37, 40, 1818, 11, 18446744073709551616, 106448181112615120, 106448181112615120⟩
def pI1816 : Prm := ⟨67, 34, 30, 1818, 11, 18446744073709551616, 106447081600987344, 106448181112615120⟩
noncomputable def L1816_cp1 : Nat × Nat := t7val% (fastRun pL1816 1 1047 (init pL1816) (init pL1816))
theorem L1816_seg1 : segOK pL1816 1 1047 (init pL1816) (init pL1816) L1816_cp1.1 L1816_cp1.2 = true := by
  decide +kernel
noncomputable def L1816_cp2 : Nat × Nat := t7val% (fastRun pL1816 1 1482 (init pL1816) (init pL1816))
theorem L1816_seg2 : segOK pL1816 1048 435 L1816_cp1.1 L1816_cp1.2 L1816_cp2.1 L1816_cp2.2 = true := by
  decide +kernel
theorem L1816_fin : (prmOK pL1816 1816 && ptTest pL1816 (runFrom pL1816 (fmask pL1816) (cmask pL1816) (hmask pL1816) 1483 333 (true, L1816_cp2.1, L1816_cp2.2)) 1816 908 false) = true := by
  decide +kernel
theorem L1816_ok : RunOK pL1816 1816 (runFrom pL1816 (fmask pL1816) (cmask pL1816) (hmask pL1816) 1483 333 (true, L1816_cp2.1, L1816_cp2.2)) ∧ ptTest pL1816 (runFrom pL1816 (fmask pL1816) (cmask pL1816) (hmask pL1816) 1483 333 (true, L1816_cp2.1, L1816_cp2.2)) 1816 908 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1816_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1816_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1816_fin) true) L1816_seg1) L1816_seg2) (by decide) rfl L1816_fin ptTest_fst
noncomputable def H1816_cp1 : Nat × Nat := t7val% (fastRun pH1816 1 1047 (init pH1816) (init pH1816))
theorem H1816_seg1 : segOK pH1816 1 1047 (init pH1816) (init pH1816) H1816_cp1.1 H1816_cp1.2 = true := by
  decide +kernel
noncomputable def H1816_cp2 : Nat × Nat := t7val% (fastRun pH1816 1 1482 (init pH1816) (init pH1816))
theorem H1816_seg2 : segOK pH1816 1048 435 H1816_cp1.1 H1816_cp1.2 H1816_cp2.1 H1816_cp2.2 = true := by
  decide +kernel
theorem H1816_fin : (prmOK pH1816 1816 && ptTest pH1816 (runFrom pH1816 (fmask pH1816) (cmask pH1816) (hmask pH1816) 1483 333 (true, H1816_cp2.1, H1816_cp2.2)) 1816 908 true) = true := by
  decide +kernel
theorem H1816_ok : RunOK pH1816 1816 (runFrom pH1816 (fmask pH1816) (cmask pH1816) (hmask pH1816) 1483 333 (true, H1816_cp2.1, H1816_cp2.2)) ∧ ptTest pH1816 (runFrom pH1816 (fmask pH1816) (cmask pH1816) (hmask pH1816) 1483 333 (true, H1816_cp2.1, H1816_cp2.2)) 1816 908 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1816_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1816_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1816_fin) true) H1816_seg1) H1816_seg2) (by decide) rfl H1816_fin ptTest_fst
noncomputable def I1816_cp1 : Nat × Nat := t7val% (fastRun pI1816 1 1047 (init pI1816) (init pI1816))
theorem I1816_seg1 : segOK pI1816 1 1047 (init pI1816) (init pI1816) I1816_cp1.1 I1816_cp1.2 = true := by
  decide +kernel
noncomputable def I1816_cp2 : Nat × Nat := t7val% (fastRun pI1816 1 1482 (init pI1816) (init pI1816))
theorem I1816_seg2 : segOK pI1816 1048 435 I1816_cp1.1 I1816_cp1.2 I1816_cp2.1 I1816_cp2.2 = true := by
  decide +kernel
theorem I1816_fin : (prmOK pI1816 1816 && intTest pI1816 (runFrom pI1816 (fmask pI1816) (cmask pI1816) (hmask pI1816) 1483 333 (true, I1816_cp2.1, I1816_cp2.2)) 1816 21 true) = true := by
  decide +kernel
theorem I1816_ok : RunOK pI1816 1816 (runFrom pI1816 (fmask pI1816) (cmask pI1816) (hmask pI1816) 1483 333 (true, I1816_cp2.1, I1816_cp2.2)) ∧ intTest pI1816 (runFrom pI1816 (fmask pI1816) (cmask pI1816) (hmask pI1816) 1483 333 (true, I1816_cp2.1, I1816_cp2.2)) 1816 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1816_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1816_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1816_fin) true) I1816_seg1) I1816_seg2) (by decide) rfl I1816_fin intTest_fst
theorem link1816 : linkOK pL1816 pH1816 pI1816 = true := by decide +kernel
theorem cvx1816 : ConvexBetweenHumps 1816 :=
  cvx_of L1816_ok H1816_ok I1816_ok link1816 (by decide)
theorem cenlink1816 : cenLinkOK pI1816 1816 = true := by decide +kernel
theorem cen1816 : CenterUniqueMin 1816 ∧ DipHyp 1816 ∧ OnePointHyps 1816 :=
  cen_of L1816_ok H1816_ok I1816_ok link1816 cenlink1816

/-! ### `N = 1817` -/

def pL1817 : Prm := ⟨80, 37, 40, 1819, 11, 18446744073709551616, 106399023514901286, 106399023514901286⟩
def pH1817 : Prm := ⟨80, 37, 40, 1819, 11, 18446744073709551616, 106400123026529062, 106400123026529062⟩
def pI1817 : Prm := ⟨67, 34, 30, 1819, 11, 18446744073709551616, 106399023514901286, 106400123026529062⟩
noncomputable def L1817_cp1 : Nat × Nat := t7val% (fastRun pL1817 1 1048 (init pL1817) (init pL1817))
theorem L1817_seg1 : segOK pL1817 1 1048 (init pL1817) (init pL1817) L1817_cp1.1 L1817_cp1.2 = true := by
  decide +kernel
noncomputable def L1817_cp2 : Nat × Nat := t7val% (fastRun pL1817 1 1483 (init pL1817) (init pL1817))
theorem L1817_seg2 : segOK pL1817 1049 435 L1817_cp1.1 L1817_cp1.2 L1817_cp2.1 L1817_cp2.2 = true := by
  decide +kernel
theorem L1817_fin : (prmOK pL1817 1817 && ptTest pL1817 (runFrom pL1817 (fmask pL1817) (cmask pL1817) (hmask pL1817) 1484 333 (true, L1817_cp2.1, L1817_cp2.2)) 1817 909 false) = true := by
  decide +kernel
theorem L1817_ok : RunOK pL1817 1817 (runFrom pL1817 (fmask pL1817) (cmask pL1817) (hmask pL1817) 1484 333 (true, L1817_cp2.1, L1817_cp2.2)) ∧ ptTest pL1817 (runFrom pL1817 (fmask pL1817) (cmask pL1817) (hmask pL1817) 1484 333 (true, L1817_cp2.1, L1817_cp2.2)) 1817 909 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1817_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1817_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1817_fin) true) L1817_seg1) L1817_seg2) (by decide) rfl L1817_fin ptTest_fst
noncomputable def H1817_cp1 : Nat × Nat := t7val% (fastRun pH1817 1 1048 (init pH1817) (init pH1817))
theorem H1817_seg1 : segOK pH1817 1 1048 (init pH1817) (init pH1817) H1817_cp1.1 H1817_cp1.2 = true := by
  decide +kernel
noncomputable def H1817_cp2 : Nat × Nat := t7val% (fastRun pH1817 1 1483 (init pH1817) (init pH1817))
theorem H1817_seg2 : segOK pH1817 1049 435 H1817_cp1.1 H1817_cp1.2 H1817_cp2.1 H1817_cp2.2 = true := by
  decide +kernel
theorem H1817_fin : (prmOK pH1817 1817 && ptTest pH1817 (runFrom pH1817 (fmask pH1817) (cmask pH1817) (hmask pH1817) 1484 333 (true, H1817_cp2.1, H1817_cp2.2)) 1817 909 true) = true := by
  decide +kernel
theorem H1817_ok : RunOK pH1817 1817 (runFrom pH1817 (fmask pH1817) (cmask pH1817) (hmask pH1817) 1484 333 (true, H1817_cp2.1, H1817_cp2.2)) ∧ ptTest pH1817 (runFrom pH1817 (fmask pH1817) (cmask pH1817) (hmask pH1817) 1484 333 (true, H1817_cp2.1, H1817_cp2.2)) 1817 909 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1817_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1817_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1817_fin) true) H1817_seg1) H1817_seg2) (by decide) rfl H1817_fin ptTest_fst
noncomputable def I1817_cp1 : Nat × Nat := t7val% (fastRun pI1817 1 1048 (init pI1817) (init pI1817))
theorem I1817_seg1 : segOK pI1817 1 1048 (init pI1817) (init pI1817) I1817_cp1.1 I1817_cp1.2 = true := by
  decide +kernel
noncomputable def I1817_cp2 : Nat × Nat := t7val% (fastRun pI1817 1 1483 (init pI1817) (init pI1817))
theorem I1817_seg2 : segOK pI1817 1049 435 I1817_cp1.1 I1817_cp1.2 I1817_cp2.1 I1817_cp2.2 = true := by
  decide +kernel
theorem I1817_fin : (prmOK pI1817 1817 && intTest pI1817 (runFrom pI1817 (fmask pI1817) (cmask pI1817) (hmask pI1817) 1484 333 (true, I1817_cp2.1, I1817_cp2.2)) 1817 21 false) = true := by
  decide +kernel
theorem I1817_ok : RunOK pI1817 1817 (runFrom pI1817 (fmask pI1817) (cmask pI1817) (hmask pI1817) 1484 333 (true, I1817_cp2.1, I1817_cp2.2)) ∧ intTest pI1817 (runFrom pI1817 (fmask pI1817) (cmask pI1817) (hmask pI1817) 1484 333 (true, I1817_cp2.1, I1817_cp2.2)) 1817 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1817_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1817_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1817_fin) true) I1817_seg1) I1817_seg2) (by decide) rfl I1817_fin intTest_fst
theorem link1817 : linkOK pL1817 pH1817 pI1817 = true := by decide +kernel
theorem cvx1817 : ConvexBetweenHumps 1817 :=
  cvx_of L1817_ok H1817_ok I1817_ok link1817 (by decide)

/-! ### `N = 1818` -/

def pL1818 : Prm := ⟨80, 37, 40, 1820, 11, 18446744073709551616, 106351031187768501, 106351031187768501⟩
def pH1818 : Prm := ⟨80, 37, 40, 1820, 11, 18446744073709551616, 106352130699396277, 106352130699396277⟩
def pI1818 : Prm := ⟨67, 34, 30, 1820, 11, 18446744073709551616, 106351031187768501, 106352130699396277⟩
noncomputable def L1818_cp1 : Nat × Nat := t7val% (fastRun pL1818 1 1049 (init pL1818) (init pL1818))
theorem L1818_seg1 : segOK pL1818 1 1049 (init pL1818) (init pL1818) L1818_cp1.1 L1818_cp1.2 = true := by
  decide +kernel
noncomputable def L1818_cp2 : Nat × Nat := t7val% (fastRun pL1818 1 1483 (init pL1818) (init pL1818))
theorem L1818_seg2 : segOK pL1818 1050 434 L1818_cp1.1 L1818_cp1.2 L1818_cp2.1 L1818_cp2.2 = true := by
  decide +kernel
theorem L1818_fin : (prmOK pL1818 1818 && ptTest pL1818 (runFrom pL1818 (fmask pL1818) (cmask pL1818) (hmask pL1818) 1484 334 (true, L1818_cp2.1, L1818_cp2.2)) 1818 909 false) = true := by
  decide +kernel
theorem L1818_ok : RunOK pL1818 1818 (runFrom pL1818 (fmask pL1818) (cmask pL1818) (hmask pL1818) 1484 334 (true, L1818_cp2.1, L1818_cp2.2)) ∧ ptTest pL1818 (runFrom pL1818 (fmask pL1818) (cmask pL1818) (hmask pL1818) 1484 334 (true, L1818_cp2.1, L1818_cp2.2)) 1818 909 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1818_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1818_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1818_fin) true) L1818_seg1) L1818_seg2) (by decide) rfl L1818_fin ptTest_fst
noncomputable def H1818_cp1 : Nat × Nat := t7val% (fastRun pH1818 1 1049 (init pH1818) (init pH1818))
theorem H1818_seg1 : segOK pH1818 1 1049 (init pH1818) (init pH1818) H1818_cp1.1 H1818_cp1.2 = true := by
  decide +kernel
noncomputable def H1818_cp2 : Nat × Nat := t7val% (fastRun pH1818 1 1483 (init pH1818) (init pH1818))
theorem H1818_seg2 : segOK pH1818 1050 434 H1818_cp1.1 H1818_cp1.2 H1818_cp2.1 H1818_cp2.2 = true := by
  decide +kernel
theorem H1818_fin : (prmOK pH1818 1818 && ptTest pH1818 (runFrom pH1818 (fmask pH1818) (cmask pH1818) (hmask pH1818) 1484 334 (true, H1818_cp2.1, H1818_cp2.2)) 1818 909 true) = true := by
  decide +kernel
theorem H1818_ok : RunOK pH1818 1818 (runFrom pH1818 (fmask pH1818) (cmask pH1818) (hmask pH1818) 1484 334 (true, H1818_cp2.1, H1818_cp2.2)) ∧ ptTest pH1818 (runFrom pH1818 (fmask pH1818) (cmask pH1818) (hmask pH1818) 1484 334 (true, H1818_cp2.1, H1818_cp2.2)) 1818 909 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1818_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1818_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1818_fin) true) H1818_seg1) H1818_seg2) (by decide) rfl H1818_fin ptTest_fst
noncomputable def I1818_cp1 : Nat × Nat := t7val% (fastRun pI1818 1 1049 (init pI1818) (init pI1818))
theorem I1818_seg1 : segOK pI1818 1 1049 (init pI1818) (init pI1818) I1818_cp1.1 I1818_cp1.2 = true := by
  decide +kernel
noncomputable def I1818_cp2 : Nat × Nat := t7val% (fastRun pI1818 1 1483 (init pI1818) (init pI1818))
theorem I1818_seg2 : segOK pI1818 1050 434 I1818_cp1.1 I1818_cp1.2 I1818_cp2.1 I1818_cp2.2 = true := by
  decide +kernel
theorem I1818_fin : (prmOK pI1818 1818 && intTest pI1818 (runFrom pI1818 (fmask pI1818) (cmask pI1818) (hmask pI1818) 1484 334 (true, I1818_cp2.1, I1818_cp2.2)) 1818 21 true) = true := by
  decide +kernel
theorem I1818_ok : RunOK pI1818 1818 (runFrom pI1818 (fmask pI1818) (cmask pI1818) (hmask pI1818) 1484 334 (true, I1818_cp2.1, I1818_cp2.2)) ∧ intTest pI1818 (runFrom pI1818 (fmask pI1818) (cmask pI1818) (hmask pI1818) 1484 334 (true, I1818_cp2.1, I1818_cp2.2)) 1818 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1818_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1818_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1818_fin) true) I1818_seg1) I1818_seg2) (by decide) rfl I1818_fin intTest_fst
theorem link1818 : linkOK pL1818 pH1818 pI1818 = true := by decide +kernel
theorem cvx1818 : ConvexBetweenHumps 1818 :=
  cvx_of L1818_ok H1818_ok I1818_ok link1818 (by decide)
theorem cenlink1818 : cenLinkOK pI1818 1818 = true := by decide +kernel
theorem cen1818 : CenterUniqueMin 1818 ∧ DipHyp 1818 ∧ OnePointHyps 1818 :=
  cen_of L1818_ok H1818_ok I1818_ok link1818 cenlink1818

/-! ### `N = 1819` -/

def pL1819 : Prm := ⟨80, 37, 40, 1821, 11, 18446744073709551616, 106303067176849038, 106303067176849038⟩
def pH1819 : Prm := ⟨80, 37, 40, 1821, 11, 18446744073709551616, 106304166688476814, 106304166688476814⟩
def pI1819 : Prm := ⟨67, 34, 30, 1821, 11, 18446744073709551616, 106303067176849038, 106304166688476814⟩
noncomputable def L1819_cp1 : Nat × Nat := t7val% (fastRun pL1819 1 1049 (init pL1819) (init pL1819))
theorem L1819_seg1 : segOK pL1819 1 1049 (init pL1819) (init pL1819) L1819_cp1.1 L1819_cp1.2 = true := by
  decide +kernel
noncomputable def L1819_cp2 : Nat × Nat := t7val% (fastRun pL1819 1 1484 (init pL1819) (init pL1819))
theorem L1819_seg2 : segOK pL1819 1050 435 L1819_cp1.1 L1819_cp1.2 L1819_cp2.1 L1819_cp2.2 = true := by
  decide +kernel
theorem L1819_fin : (prmOK pL1819 1819 && ptTest pL1819 (runFrom pL1819 (fmask pL1819) (cmask pL1819) (hmask pL1819) 1485 334 (true, L1819_cp2.1, L1819_cp2.2)) 1819 910 false) = true := by
  decide +kernel
theorem L1819_ok : RunOK pL1819 1819 (runFrom pL1819 (fmask pL1819) (cmask pL1819) (hmask pL1819) 1485 334 (true, L1819_cp2.1, L1819_cp2.2)) ∧ ptTest pL1819 (runFrom pL1819 (fmask pL1819) (cmask pL1819) (hmask pL1819) 1485 334 (true, L1819_cp2.1, L1819_cp2.2)) 1819 910 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1819_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1819_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1819_fin) true) L1819_seg1) L1819_seg2) (by decide) rfl L1819_fin ptTest_fst
noncomputable def H1819_cp1 : Nat × Nat := t7val% (fastRun pH1819 1 1049 (init pH1819) (init pH1819))
theorem H1819_seg1 : segOK pH1819 1 1049 (init pH1819) (init pH1819) H1819_cp1.1 H1819_cp1.2 = true := by
  decide +kernel
noncomputable def H1819_cp2 : Nat × Nat := t7val% (fastRun pH1819 1 1484 (init pH1819) (init pH1819))
theorem H1819_seg2 : segOK pH1819 1050 435 H1819_cp1.1 H1819_cp1.2 H1819_cp2.1 H1819_cp2.2 = true := by
  decide +kernel
theorem H1819_fin : (prmOK pH1819 1819 && ptTest pH1819 (runFrom pH1819 (fmask pH1819) (cmask pH1819) (hmask pH1819) 1485 334 (true, H1819_cp2.1, H1819_cp2.2)) 1819 910 true) = true := by
  decide +kernel
theorem H1819_ok : RunOK pH1819 1819 (runFrom pH1819 (fmask pH1819) (cmask pH1819) (hmask pH1819) 1485 334 (true, H1819_cp2.1, H1819_cp2.2)) ∧ ptTest pH1819 (runFrom pH1819 (fmask pH1819) (cmask pH1819) (hmask pH1819) 1485 334 (true, H1819_cp2.1, H1819_cp2.2)) 1819 910 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1819_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1819_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1819_fin) true) H1819_seg1) H1819_seg2) (by decide) rfl H1819_fin ptTest_fst
noncomputable def I1819_cp1 : Nat × Nat := t7val% (fastRun pI1819 1 1049 (init pI1819) (init pI1819))
theorem I1819_seg1 : segOK pI1819 1 1049 (init pI1819) (init pI1819) I1819_cp1.1 I1819_cp1.2 = true := by
  decide +kernel
noncomputable def I1819_cp2 : Nat × Nat := t7val% (fastRun pI1819 1 1484 (init pI1819) (init pI1819))
theorem I1819_seg2 : segOK pI1819 1050 435 I1819_cp1.1 I1819_cp1.2 I1819_cp2.1 I1819_cp2.2 = true := by
  decide +kernel
theorem I1819_fin : (prmOK pI1819 1819 && intTest pI1819 (runFrom pI1819 (fmask pI1819) (cmask pI1819) (hmask pI1819) 1485 334 (true, I1819_cp2.1, I1819_cp2.2)) 1819 21 false) = true := by
  decide +kernel
theorem I1819_ok : RunOK pI1819 1819 (runFrom pI1819 (fmask pI1819) (cmask pI1819) (hmask pI1819) 1485 334 (true, I1819_cp2.1, I1819_cp2.2)) ∧ intTest pI1819 (runFrom pI1819 (fmask pI1819) (cmask pI1819) (hmask pI1819) 1485 334 (true, I1819_cp2.1, I1819_cp2.2)) 1819 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1819_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1819_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1819_fin) true) I1819_seg1) I1819_seg2) (by decide) rfl I1819_fin intTest_fst
theorem link1819 : linkOK pL1819 pH1819 pI1819 = true := by decide +kernel
theorem cvx1819 : ConvexBetweenHumps 1819 :=
  cvx_of L1819_ok H1819_ok I1819_ok link1819 (by decide)

/-! ### The range -/

theorem cvx_1808_1819 {N : ℕ} (h1 : 1808 ≤ N) (h2 : N ≤ 1819) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1813
  · by_cases h4 : N ≤ 1810
    · by_cases h6 : N ≤ 1808
      · obtain rfl : N = 1808 := by omega
        exact cvx1808
      · by_cases h8 : N ≤ 1809
        · obtain rfl : N = 1809 := by omega
          exact cvx1809
        · obtain rfl : N = 1810 := by omega
          exact cvx1810
    · by_cases h6 : N ≤ 1811
      · obtain rfl : N = 1811 := by omega
        exact cvx1811
      · by_cases h8 : N ≤ 1812
        · obtain rfl : N = 1812 := by omega
          exact cvx1812
        · obtain rfl : N = 1813 := by omega
          exact cvx1813
  · by_cases h4 : N ≤ 1816
    · by_cases h6 : N ≤ 1814
      · obtain rfl : N = 1814 := by omega
        exact cvx1814
      · by_cases h8 : N ≤ 1815
        · obtain rfl : N = 1815 := by omega
          exact cvx1815
        · obtain rfl : N = 1816 := by omega
          exact cvx1816
    · by_cases h6 : N ≤ 1817
      · obtain rfl : N = 1817 := by omega
        exact cvx1817
      · by_cases h8 : N ≤ 1818
        · obtain rfl : N = 1818 := by omega
          exact cvx1818
        · obtain rfl : N = 1819 := by omega
          exact cvx1819

theorem cen_1808_1819 {N : ℕ} (h1 : 1808 ≤ N) (h2 : N ≤ 1819) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1812
  · by_cases h4 : N ≤ 1808
    · obtain rfl : N = 1808 := by omega
      exact cen1808
    · by_cases h6 : N ≤ 1810
      · obtain rfl : N = 1810 := by omega
        exact cen1810
      · obtain rfl : N = 1812 := by omega
        exact cen1812
  · by_cases h4 : N ≤ 1814
    · obtain rfl : N = 1814 := by omega
      exact cen1814
    · by_cases h6 : N ≤ 1816
      · obtain rfl : N = 1816 := by omega
        exact cen1816
      · obtain rfl : N = 1818 := by omega
        exact cen1818

end Kagey131.PaperD.T7
