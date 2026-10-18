import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1734, …, 1746` (generated)

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

/-! ### `N = 1734` -/

def pL1734 : Prm := ⟨80, 37, 40, 1736, 11, 18446744073709551616, 110554311389239347, 110554311389239347⟩
def pH1734 : Prm := ⟨80, 37, 40, 1736, 11, 18446744073709551616, 110555410900867123, 110555410900867123⟩
def pI1734 : Prm := ⟨69, 33, 33, 1736, 11, 18446744073709551616, 110554311389239347, 110555410900867123⟩
noncomputable def L1734_cp1 : Nat × Nat := t7val% (fastRun pL1734 1 1000 (init pL1734) (init pL1734))
theorem L1734_seg1 : segOK pL1734 1 1000 (init pL1734) (init pL1734) L1734_cp1.1 L1734_cp1.2 = true := by
  decide +kernel
noncomputable def L1734_cp2 : Nat × Nat := t7val% (fastRun pL1734 1 1415 (init pL1734) (init pL1734))
theorem L1734_seg2 : segOK pL1734 1001 415 L1734_cp1.1 L1734_cp1.2 L1734_cp2.1 L1734_cp2.2 = true := by
  decide +kernel
theorem L1734_fin : (prmOK pL1734 1734 && ptTest pL1734 (runFrom pL1734 (fmask pL1734) (cmask pL1734) (hmask pL1734) 1416 318 (true, L1734_cp2.1, L1734_cp2.2)) 1734 867 false) = true := by
  decide +kernel
theorem L1734_ok : RunOK pL1734 1734 (runFrom pL1734 (fmask pL1734) (cmask pL1734) (hmask pL1734) 1416 318 (true, L1734_cp2.1, L1734_cp2.2)) ∧ ptTest pL1734 (runFrom pL1734 (fmask pL1734) (cmask pL1734) (hmask pL1734) 1416 318 (true, L1734_cp2.1, L1734_cp2.2)) 1734 867 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1734_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1734_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1734_fin) true) L1734_seg1) L1734_seg2) (by decide) rfl L1734_fin ptTest_fst
noncomputable def H1734_cp1 : Nat × Nat := t7val% (fastRun pH1734 1 1000 (init pH1734) (init pH1734))
theorem H1734_seg1 : segOK pH1734 1 1000 (init pH1734) (init pH1734) H1734_cp1.1 H1734_cp1.2 = true := by
  decide +kernel
noncomputable def H1734_cp2 : Nat × Nat := t7val% (fastRun pH1734 1 1415 (init pH1734) (init pH1734))
theorem H1734_seg2 : segOK pH1734 1001 415 H1734_cp1.1 H1734_cp1.2 H1734_cp2.1 H1734_cp2.2 = true := by
  decide +kernel
theorem H1734_fin : (prmOK pH1734 1734 && ptTest pH1734 (runFrom pH1734 (fmask pH1734) (cmask pH1734) (hmask pH1734) 1416 318 (true, H1734_cp2.1, H1734_cp2.2)) 1734 867 true) = true := by
  decide +kernel
theorem H1734_ok : RunOK pH1734 1734 (runFrom pH1734 (fmask pH1734) (cmask pH1734) (hmask pH1734) 1416 318 (true, H1734_cp2.1, H1734_cp2.2)) ∧ ptTest pH1734 (runFrom pH1734 (fmask pH1734) (cmask pH1734) (hmask pH1734) 1416 318 (true, H1734_cp2.1, H1734_cp2.2)) 1734 867 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1734_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1734_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1734_fin) true) H1734_seg1) H1734_seg2) (by decide) rfl H1734_fin ptTest_fst
noncomputable def I1734_cp1 : Nat × Nat := t7val% (fastRun pI1734 1 1225 (init pI1734) (init pI1734))
theorem I1734_seg1 : segOK pI1734 1 1225 (init pI1734) (init pI1734) I1734_cp1.1 I1734_cp1.2 = true := by
  decide +kernel
theorem I1734_fin : (prmOK pI1734 1734 && intTest pI1734 (runFrom pI1734 (fmask pI1734) (cmask pI1734) (hmask pI1734) 1226 508 (true, I1734_cp1.1, I1734_cp1.2)) 1734 21 true) = true := by
  decide +kernel
theorem I1734_ok : RunOK pI1734 1734 (runFrom pI1734 (fmask pI1734) (cmask pI1734) (hmask pI1734) 1226 508 (true, I1734_cp1.1, I1734_cp1.2)) ∧ intTest pI1734 (runFrom pI1734 (fmask pI1734) (cmask pI1734) (hmask pI1734) 1226 508 (true, I1734_cp1.1, I1734_cp1.2)) 1734 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1734_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1734_fin) true) I1734_seg1) (by decide) rfl I1734_fin intTest_fst
theorem link1734 : linkOK pL1734 pH1734 pI1734 = true := by decide +kernel
theorem cvx1734 : ConvexBetweenHumps 1734 :=
  cvx_of L1734_ok H1734_ok I1734_ok link1734 (by decide)
theorem cenlink1734 : cenLinkOK pI1734 1734 = true := by decide +kernel
theorem cen1734 : CenterUniqueMin 1734 ∧ DipHyp 1734 ∧ OnePointHyps 1734 :=
  cen_of L1734_ok H1734_ok I1734_ok link1734 cenlink1734

/-! ### `N = 1735` -/

def pL1735 : Prm := ⟨80, 37, 40, 1737, 11, 18446744073709551616, 110502136050289123, 110502136050289123⟩
def pH1735 : Prm := ⟨80, 37, 40, 1737, 11, 18446744073709551616, 110503235561916899, 110503235561916899⟩
def pI1735 : Prm := ⟨69, 33, 33, 1737, 11, 18446744073709551616, 110502136050289123, 110503235561916899⟩
noncomputable def L1735_cp1 : Nat × Nat := t7val% (fastRun pL1735 1 1001 (init pL1735) (init pL1735))
theorem L1735_seg1 : segOK pL1735 1 1001 (init pL1735) (init pL1735) L1735_cp1.1 L1735_cp1.2 = true := by
  decide +kernel
noncomputable def L1735_cp2 : Nat × Nat := t7val% (fastRun pL1735 1 1416 (init pL1735) (init pL1735))
theorem L1735_seg2 : segOK pL1735 1002 415 L1735_cp1.1 L1735_cp1.2 L1735_cp2.1 L1735_cp2.2 = true := by
  decide +kernel
theorem L1735_fin : (prmOK pL1735 1735 && ptTest pL1735 (runFrom pL1735 (fmask pL1735) (cmask pL1735) (hmask pL1735) 1417 318 (true, L1735_cp2.1, L1735_cp2.2)) 1735 868 false) = true := by
  decide +kernel
theorem L1735_ok : RunOK pL1735 1735 (runFrom pL1735 (fmask pL1735) (cmask pL1735) (hmask pL1735) 1417 318 (true, L1735_cp2.1, L1735_cp2.2)) ∧ ptTest pL1735 (runFrom pL1735 (fmask pL1735) (cmask pL1735) (hmask pL1735) 1417 318 (true, L1735_cp2.1, L1735_cp2.2)) 1735 868 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1735_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1735_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1735_fin) true) L1735_seg1) L1735_seg2) (by decide) rfl L1735_fin ptTest_fst
noncomputable def H1735_cp1 : Nat × Nat := t7val% (fastRun pH1735 1 1001 (init pH1735) (init pH1735))
theorem H1735_seg1 : segOK pH1735 1 1001 (init pH1735) (init pH1735) H1735_cp1.1 H1735_cp1.2 = true := by
  decide +kernel
noncomputable def H1735_cp2 : Nat × Nat := t7val% (fastRun pH1735 1 1416 (init pH1735) (init pH1735))
theorem H1735_seg2 : segOK pH1735 1002 415 H1735_cp1.1 H1735_cp1.2 H1735_cp2.1 H1735_cp2.2 = true := by
  decide +kernel
theorem H1735_fin : (prmOK pH1735 1735 && ptTest pH1735 (runFrom pH1735 (fmask pH1735) (cmask pH1735) (hmask pH1735) 1417 318 (true, H1735_cp2.1, H1735_cp2.2)) 1735 868 true) = true := by
  decide +kernel
theorem H1735_ok : RunOK pH1735 1735 (runFrom pH1735 (fmask pH1735) (cmask pH1735) (hmask pH1735) 1417 318 (true, H1735_cp2.1, H1735_cp2.2)) ∧ ptTest pH1735 (runFrom pH1735 (fmask pH1735) (cmask pH1735) (hmask pH1735) 1417 318 (true, H1735_cp2.1, H1735_cp2.2)) 1735 868 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1735_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1735_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1735_fin) true) H1735_seg1) H1735_seg2) (by decide) rfl H1735_fin ptTest_fst
noncomputable def I1735_cp1 : Nat × Nat := t7val% (fastRun pI1735 1 1226 (init pI1735) (init pI1735))
theorem I1735_seg1 : segOK pI1735 1 1226 (init pI1735) (init pI1735) I1735_cp1.1 I1735_cp1.2 = true := by
  decide +kernel
theorem I1735_fin : (prmOK pI1735 1735 && intTest pI1735 (runFrom pI1735 (fmask pI1735) (cmask pI1735) (hmask pI1735) 1227 508 (true, I1735_cp1.1, I1735_cp1.2)) 1735 21 false) = true := by
  decide +kernel
theorem I1735_ok : RunOK pI1735 1735 (runFrom pI1735 (fmask pI1735) (cmask pI1735) (hmask pI1735) 1227 508 (true, I1735_cp1.1, I1735_cp1.2)) ∧ intTest pI1735 (runFrom pI1735 (fmask pI1735) (cmask pI1735) (hmask pI1735) 1227 508 (true, I1735_cp1.1, I1735_cp1.2)) 1735 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1735_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1735_fin) true) I1735_seg1) (by decide) rfl I1735_fin intTest_fst
theorem link1735 : linkOK pL1735 pH1735 pI1735 = true := by decide +kernel
theorem cvx1735 : ConvexBetweenHumps 1735 :=
  cvx_of L1735_ok H1735_ok I1735_ok link1735 (by decide)

/-! ### `N = 1736` -/

def pL1736 : Prm := ⟨80, 37, 40, 1738, 11, 18446744073709551616, 110450035670845588, 110450035670845588⟩
def pH1736 : Prm := ⟨80, 37, 40, 1738, 11, 18446744073709551616, 110451135182473364, 110451135182473364⟩
def pI1736 : Prm := ⟨69, 33, 33, 1738, 11, 18446744073709551616, 110450035670845588, 110451135182473364⟩
noncomputable def L1736_cp1 : Nat × Nat := t7val% (fastRun pL1736 1 1001 (init pL1736) (init pL1736))
theorem L1736_seg1 : segOK pL1736 1 1001 (init pL1736) (init pL1736) L1736_cp1.1 L1736_cp1.2 = true := by
  decide +kernel
noncomputable def L1736_cp2 : Nat × Nat := t7val% (fastRun pL1736 1 1416 (init pL1736) (init pL1736))
theorem L1736_seg2 : segOK pL1736 1002 415 L1736_cp1.1 L1736_cp1.2 L1736_cp2.1 L1736_cp2.2 = true := by
  decide +kernel
theorem L1736_fin : (prmOK pL1736 1736 && ptTest pL1736 (runFrom pL1736 (fmask pL1736) (cmask pL1736) (hmask pL1736) 1417 319 (true, L1736_cp2.1, L1736_cp2.2)) 1736 868 false) = true := by
  decide +kernel
theorem L1736_ok : RunOK pL1736 1736 (runFrom pL1736 (fmask pL1736) (cmask pL1736) (hmask pL1736) 1417 319 (true, L1736_cp2.1, L1736_cp2.2)) ∧ ptTest pL1736 (runFrom pL1736 (fmask pL1736) (cmask pL1736) (hmask pL1736) 1417 319 (true, L1736_cp2.1, L1736_cp2.2)) 1736 868 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1736_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1736_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1736_fin) true) L1736_seg1) L1736_seg2) (by decide) rfl L1736_fin ptTest_fst
noncomputable def H1736_cp1 : Nat × Nat := t7val% (fastRun pH1736 1 1001 (init pH1736) (init pH1736))
theorem H1736_seg1 : segOK pH1736 1 1001 (init pH1736) (init pH1736) H1736_cp1.1 H1736_cp1.2 = true := by
  decide +kernel
noncomputable def H1736_cp2 : Nat × Nat := t7val% (fastRun pH1736 1 1416 (init pH1736) (init pH1736))
theorem H1736_seg2 : segOK pH1736 1002 415 H1736_cp1.1 H1736_cp1.2 H1736_cp2.1 H1736_cp2.2 = true := by
  decide +kernel
theorem H1736_fin : (prmOK pH1736 1736 && ptTest pH1736 (runFrom pH1736 (fmask pH1736) (cmask pH1736) (hmask pH1736) 1417 319 (true, H1736_cp2.1, H1736_cp2.2)) 1736 868 true) = true := by
  decide +kernel
theorem H1736_ok : RunOK pH1736 1736 (runFrom pH1736 (fmask pH1736) (cmask pH1736) (hmask pH1736) 1417 319 (true, H1736_cp2.1, H1736_cp2.2)) ∧ ptTest pH1736 (runFrom pH1736 (fmask pH1736) (cmask pH1736) (hmask pH1736) 1417 319 (true, H1736_cp2.1, H1736_cp2.2)) 1736 868 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1736_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1736_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1736_fin) true) H1736_seg1) H1736_seg2) (by decide) rfl H1736_fin ptTest_fst
noncomputable def I1736_cp1 : Nat × Nat := t7val% (fastRun pI1736 1 1227 (init pI1736) (init pI1736))
theorem I1736_seg1 : segOK pI1736 1 1227 (init pI1736) (init pI1736) I1736_cp1.1 I1736_cp1.2 = true := by
  decide +kernel
theorem I1736_fin : (prmOK pI1736 1736 && intTest pI1736 (runFrom pI1736 (fmask pI1736) (cmask pI1736) (hmask pI1736) 1228 508 (true, I1736_cp1.1, I1736_cp1.2)) 1736 21 true) = true := by
  decide +kernel
theorem I1736_ok : RunOK pI1736 1736 (runFrom pI1736 (fmask pI1736) (cmask pI1736) (hmask pI1736) 1228 508 (true, I1736_cp1.1, I1736_cp1.2)) ∧ intTest pI1736 (runFrom pI1736 (fmask pI1736) (cmask pI1736) (hmask pI1736) 1228 508 (true, I1736_cp1.1, I1736_cp1.2)) 1736 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1736_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1736_fin) true) I1736_seg1) (by decide) rfl I1736_fin intTest_fst
theorem link1736 : linkOK pL1736 pH1736 pI1736 = true := by decide +kernel
theorem cvx1736 : ConvexBetweenHumps 1736 :=
  cvx_of L1736_ok H1736_ok I1736_ok link1736 (by decide)
theorem cenlink1736 : cenLinkOK pI1736 1736 = true := by decide +kernel
theorem cen1736 : CenterUniqueMin 1736 ∧ DipHyp 1736 ∧ OnePointHyps 1736 :=
  cen_of L1736_ok H1736_ok I1736_ok link1736 cenlink1736

/-! ### `N = 1737` -/

def pL1737 : Prm := ⟨80, 37, 40, 1739, 11, 18446744073709551616, 110397967152932012, 110397967152932012⟩
def pH1737 : Prm := ⟨80, 37, 40, 1739, 11, 18446744073709551616, 110399066664559788, 110399066664559788⟩
def pI1737 : Prm := ⟨69, 33, 33, 1739, 11, 18446744073709551616, 110397967152932012, 110399066664559788⟩
noncomputable def L1737_cp1 : Nat × Nat := t7val% (fastRun pL1737 1 1002 (init pL1737) (init pL1737))
theorem L1737_seg1 : segOK pL1737 1 1002 (init pL1737) (init pL1737) L1737_cp1.1 L1737_cp1.2 = true := by
  decide +kernel
noncomputable def L1737_cp2 : Nat × Nat := t7val% (fastRun pL1737 1 1417 (init pL1737) (init pL1737))
theorem L1737_seg2 : segOK pL1737 1003 415 L1737_cp1.1 L1737_cp1.2 L1737_cp2.1 L1737_cp2.2 = true := by
  decide +kernel
theorem L1737_fin : (prmOK pL1737 1737 && ptTest pL1737 (runFrom pL1737 (fmask pL1737) (cmask pL1737) (hmask pL1737) 1418 319 (true, L1737_cp2.1, L1737_cp2.2)) 1737 869 false) = true := by
  decide +kernel
theorem L1737_ok : RunOK pL1737 1737 (runFrom pL1737 (fmask pL1737) (cmask pL1737) (hmask pL1737) 1418 319 (true, L1737_cp2.1, L1737_cp2.2)) ∧ ptTest pL1737 (runFrom pL1737 (fmask pL1737) (cmask pL1737) (hmask pL1737) 1418 319 (true, L1737_cp2.1, L1737_cp2.2)) 1737 869 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1737_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1737_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1737_fin) true) L1737_seg1) L1737_seg2) (by decide) rfl L1737_fin ptTest_fst
noncomputable def H1737_cp1 : Nat × Nat := t7val% (fastRun pH1737 1 1002 (init pH1737) (init pH1737))
theorem H1737_seg1 : segOK pH1737 1 1002 (init pH1737) (init pH1737) H1737_cp1.1 H1737_cp1.2 = true := by
  decide +kernel
noncomputable def H1737_cp2 : Nat × Nat := t7val% (fastRun pH1737 1 1417 (init pH1737) (init pH1737))
theorem H1737_seg2 : segOK pH1737 1003 415 H1737_cp1.1 H1737_cp1.2 H1737_cp2.1 H1737_cp2.2 = true := by
  decide +kernel
theorem H1737_fin : (prmOK pH1737 1737 && ptTest pH1737 (runFrom pH1737 (fmask pH1737) (cmask pH1737) (hmask pH1737) 1418 319 (true, H1737_cp2.1, H1737_cp2.2)) 1737 869 true) = true := by
  decide +kernel
theorem H1737_ok : RunOK pH1737 1737 (runFrom pH1737 (fmask pH1737) (cmask pH1737) (hmask pH1737) 1418 319 (true, H1737_cp2.1, H1737_cp2.2)) ∧ ptTest pH1737 (runFrom pH1737 (fmask pH1737) (cmask pH1737) (hmask pH1737) 1418 319 (true, H1737_cp2.1, H1737_cp2.2)) 1737 869 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1737_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1737_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1737_fin) true) H1737_seg1) H1737_seg2) (by decide) rfl H1737_fin ptTest_fst
noncomputable def I1737_cp1 : Nat × Nat := t7val% (fastRun pI1737 1 1227 (init pI1737) (init pI1737))
theorem I1737_seg1 : segOK pI1737 1 1227 (init pI1737) (init pI1737) I1737_cp1.1 I1737_cp1.2 = true := by
  decide +kernel
theorem I1737_fin : (prmOK pI1737 1737 && intTest pI1737 (runFrom pI1737 (fmask pI1737) (cmask pI1737) (hmask pI1737) 1228 509 (true, I1737_cp1.1, I1737_cp1.2)) 1737 21 false) = true := by
  decide +kernel
theorem I1737_ok : RunOK pI1737 1737 (runFrom pI1737 (fmask pI1737) (cmask pI1737) (hmask pI1737) 1228 509 (true, I1737_cp1.1, I1737_cp1.2)) ∧ intTest pI1737 (runFrom pI1737 (fmask pI1737) (cmask pI1737) (hmask pI1737) 1228 509 (true, I1737_cp1.1, I1737_cp1.2)) 1737 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1737_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1737_fin) true) I1737_seg1) (by decide) rfl I1737_fin intTest_fst
theorem link1737 : linkOK pL1737 pH1737 pI1737 = true := by decide +kernel
theorem cvx1737 : ConvexBetweenHumps 1737 :=
  cvx_of L1737_ok H1737_ok I1737_ok link1737 (by decide)

/-! ### `N = 1738` -/

def pL1738 : Prm := ⟨80, 37, 40, 1740, 11, 18446744073709551616, 110345973350087318, 110345973350087318⟩
def pH1738 : Prm := ⟨80, 37, 40, 1740, 11, 18446744073709551616, 110347072861715094, 110347072861715094⟩
def pI1738 : Prm := ⟨69, 33, 33, 1740, 11, 18446744073709551616, 110345973350087318, 110347072861715094⟩
noncomputable def L1738_cp1 : Nat × Nat := t7val% (fastRun pL1738 1 1002 (init pL1738) (init pL1738))
theorem L1738_seg1 : segOK pL1738 1 1002 (init pL1738) (init pL1738) L1738_cp1.1 L1738_cp1.2 = true := by
  decide +kernel
noncomputable def L1738_cp2 : Nat × Nat := t7val% (fastRun pL1738 1 1418 (init pL1738) (init pL1738))
theorem L1738_seg2 : segOK pL1738 1003 416 L1738_cp1.1 L1738_cp1.2 L1738_cp2.1 L1738_cp2.2 = true := by
  decide +kernel
theorem L1738_fin : (prmOK pL1738 1738 && ptTest pL1738 (runFrom pL1738 (fmask pL1738) (cmask pL1738) (hmask pL1738) 1419 319 (true, L1738_cp2.1, L1738_cp2.2)) 1738 869 false) = true := by
  decide +kernel
theorem L1738_ok : RunOK pL1738 1738 (runFrom pL1738 (fmask pL1738) (cmask pL1738) (hmask pL1738) 1419 319 (true, L1738_cp2.1, L1738_cp2.2)) ∧ ptTest pL1738 (runFrom pL1738 (fmask pL1738) (cmask pL1738) (hmask pL1738) 1419 319 (true, L1738_cp2.1, L1738_cp2.2)) 1738 869 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1738_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1738_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1738_fin) true) L1738_seg1) L1738_seg2) (by decide) rfl L1738_fin ptTest_fst
noncomputable def H1738_cp1 : Nat × Nat := t7val% (fastRun pH1738 1 1002 (init pH1738) (init pH1738))
theorem H1738_seg1 : segOK pH1738 1 1002 (init pH1738) (init pH1738) H1738_cp1.1 H1738_cp1.2 = true := by
  decide +kernel
noncomputable def H1738_cp2 : Nat × Nat := t7val% (fastRun pH1738 1 1418 (init pH1738) (init pH1738))
theorem H1738_seg2 : segOK pH1738 1003 416 H1738_cp1.1 H1738_cp1.2 H1738_cp2.1 H1738_cp2.2 = true := by
  decide +kernel
theorem H1738_fin : (prmOK pH1738 1738 && ptTest pH1738 (runFrom pH1738 (fmask pH1738) (cmask pH1738) (hmask pH1738) 1419 319 (true, H1738_cp2.1, H1738_cp2.2)) 1738 869 true) = true := by
  decide +kernel
theorem H1738_ok : RunOK pH1738 1738 (runFrom pH1738 (fmask pH1738) (cmask pH1738) (hmask pH1738) 1419 319 (true, H1738_cp2.1, H1738_cp2.2)) ∧ ptTest pH1738 (runFrom pH1738 (fmask pH1738) (cmask pH1738) (hmask pH1738) 1419 319 (true, H1738_cp2.1, H1738_cp2.2)) 1738 869 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1738_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1738_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1738_fin) true) H1738_seg1) H1738_seg2) (by decide) rfl H1738_fin ptTest_fst
noncomputable def I1738_cp1 : Nat × Nat := t7val% (fastRun pI1738 1 1228 (init pI1738) (init pI1738))
theorem I1738_seg1 : segOK pI1738 1 1228 (init pI1738) (init pI1738) I1738_cp1.1 I1738_cp1.2 = true := by
  decide +kernel
theorem I1738_fin : (prmOK pI1738 1738 && intTest pI1738 (runFrom pI1738 (fmask pI1738) (cmask pI1738) (hmask pI1738) 1229 509 (true, I1738_cp1.1, I1738_cp1.2)) 1738 21 true) = true := by
  decide +kernel
theorem I1738_ok : RunOK pI1738 1738 (runFrom pI1738 (fmask pI1738) (cmask pI1738) (hmask pI1738) 1229 509 (true, I1738_cp1.1, I1738_cp1.2)) ∧ intTest pI1738 (runFrom pI1738 (fmask pI1738) (cmask pI1738) (hmask pI1738) 1229 509 (true, I1738_cp1.1, I1738_cp1.2)) 1738 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1738_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1738_fin) true) I1738_seg1) (by decide) rfl I1738_fin intTest_fst
theorem link1738 : linkOK pL1738 pH1738 pI1738 = true := by decide +kernel
theorem cvx1738 : ConvexBetweenHumps 1738 :=
  cvx_of L1738_ok H1738_ok I1738_ok link1738 (by decide)
theorem cenlink1738 : cenLinkOK pI1738 1738 = true := by decide +kernel
theorem cen1738 : CenterUniqueMin 1738 ∧ DipHyp 1738 ∧ OnePointHyps 1738 :=
  cen_of L1738_ok H1738_ok I1738_ok link1738 cenlink1738

/-! ### `N = 1739` -/

def pL1739 : Prm := ⟨80, 37, 40, 1741, 11, 18446744073709551616, 110294011315339824, 110294011315339824⟩
def pH1739 : Prm := ⟨80, 37, 40, 1741, 11, 18446744073709551616, 110295110826967600, 110295110826967600⟩
def pI1739 : Prm := ⟨69, 33, 33, 1741, 11, 18446744073709551616, 110294011315339824, 110295110826967600⟩
noncomputable def L1739_cp1 : Nat × Nat := t7val% (fastRun pL1739 1 1003 (init pL1739) (init pL1739))
theorem L1739_seg1 : segOK pL1739 1 1003 (init pL1739) (init pL1739) L1739_cp1.1 L1739_cp1.2 = true := by
  decide +kernel
noncomputable def L1739_cp2 : Nat × Nat := t7val% (fastRun pL1739 1 1419 (init pL1739) (init pL1739))
theorem L1739_seg2 : segOK pL1739 1004 416 L1739_cp1.1 L1739_cp1.2 L1739_cp2.1 L1739_cp2.2 = true := by
  decide +kernel
theorem L1739_fin : (prmOK pL1739 1739 && ptTest pL1739 (runFrom pL1739 (fmask pL1739) (cmask pL1739) (hmask pL1739) 1420 319 (true, L1739_cp2.1, L1739_cp2.2)) 1739 870 false) = true := by
  decide +kernel
theorem L1739_ok : RunOK pL1739 1739 (runFrom pL1739 (fmask pL1739) (cmask pL1739) (hmask pL1739) 1420 319 (true, L1739_cp2.1, L1739_cp2.2)) ∧ ptTest pL1739 (runFrom pL1739 (fmask pL1739) (cmask pL1739) (hmask pL1739) 1420 319 (true, L1739_cp2.1, L1739_cp2.2)) 1739 870 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1739_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1739_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1739_fin) true) L1739_seg1) L1739_seg2) (by decide) rfl L1739_fin ptTest_fst
noncomputable def H1739_cp1 : Nat × Nat := t7val% (fastRun pH1739 1 1003 (init pH1739) (init pH1739))
theorem H1739_seg1 : segOK pH1739 1 1003 (init pH1739) (init pH1739) H1739_cp1.1 H1739_cp1.2 = true := by
  decide +kernel
noncomputable def H1739_cp2 : Nat × Nat := t7val% (fastRun pH1739 1 1419 (init pH1739) (init pH1739))
theorem H1739_seg2 : segOK pH1739 1004 416 H1739_cp1.1 H1739_cp1.2 H1739_cp2.1 H1739_cp2.2 = true := by
  decide +kernel
theorem H1739_fin : (prmOK pH1739 1739 && ptTest pH1739 (runFrom pH1739 (fmask pH1739) (cmask pH1739) (hmask pH1739) 1420 319 (true, H1739_cp2.1, H1739_cp2.2)) 1739 870 true) = true := by
  decide +kernel
theorem H1739_ok : RunOK pH1739 1739 (runFrom pH1739 (fmask pH1739) (cmask pH1739) (hmask pH1739) 1420 319 (true, H1739_cp2.1, H1739_cp2.2)) ∧ ptTest pH1739 (runFrom pH1739 (fmask pH1739) (cmask pH1739) (hmask pH1739) 1420 319 (true, H1739_cp2.1, H1739_cp2.2)) 1739 870 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1739_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1739_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1739_fin) true) H1739_seg1) H1739_seg2) (by decide) rfl H1739_fin ptTest_fst
noncomputable def I1739_cp1 : Nat × Nat := t7val% (fastRun pI1739 1 1229 (init pI1739) (init pI1739))
theorem I1739_seg1 : segOK pI1739 1 1229 (init pI1739) (init pI1739) I1739_cp1.1 I1739_cp1.2 = true := by
  decide +kernel
theorem I1739_fin : (prmOK pI1739 1739 && intTest pI1739 (runFrom pI1739 (fmask pI1739) (cmask pI1739) (hmask pI1739) 1230 509 (true, I1739_cp1.1, I1739_cp1.2)) 1739 21 false) = true := by
  decide +kernel
theorem I1739_ok : RunOK pI1739 1739 (runFrom pI1739 (fmask pI1739) (cmask pI1739) (hmask pI1739) 1230 509 (true, I1739_cp1.1, I1739_cp1.2)) ∧ intTest pI1739 (runFrom pI1739 (fmask pI1739) (cmask pI1739) (hmask pI1739) 1230 509 (true, I1739_cp1.1, I1739_cp1.2)) 1739 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1739_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1739_fin) true) I1739_seg1) (by decide) rfl I1739_fin intTest_fst
theorem link1739 : linkOK pL1739 pH1739 pI1739 = true := by decide +kernel
theorem cvx1739 : ConvexBetweenHumps 1739 :=
  cvx_of L1739_ok H1739_ok I1739_ok link1739 (by decide)

/-! ### `N = 1740` -/

def pL1740 : Prm := ⟨80, 37, 40, 1742, 11, 18446744073709551616, 110242123752256425, 110242123752256425⟩
def pH1740 : Prm := ⟨80, 37, 40, 1742, 11, 18446744073709551616, 110243223263884201, 110243223263884201⟩
def pI1740 : Prm := ⟨69, 33, 33, 1742, 11, 18446744073709551616, 110242123752256425, 110243223263884201⟩
noncomputable def L1740_cp1 : Nat × Nat := t7val% (fastRun pL1740 1 1004 (init pL1740) (init pL1740))
theorem L1740_seg1 : segOK pL1740 1 1004 (init pL1740) (init pL1740) L1740_cp1.1 L1740_cp1.2 = true := by
  decide +kernel
noncomputable def L1740_cp2 : Nat × Nat := t7val% (fastRun pL1740 1 1420 (init pL1740) (init pL1740))
theorem L1740_seg2 : segOK pL1740 1005 416 L1740_cp1.1 L1740_cp1.2 L1740_cp2.1 L1740_cp2.2 = true := by
  decide +kernel
theorem L1740_fin : (prmOK pL1740 1740 && ptTest pL1740 (runFrom pL1740 (fmask pL1740) (cmask pL1740) (hmask pL1740) 1421 319 (true, L1740_cp2.1, L1740_cp2.2)) 1740 870 false) = true := by
  decide +kernel
theorem L1740_ok : RunOK pL1740 1740 (runFrom pL1740 (fmask pL1740) (cmask pL1740) (hmask pL1740) 1421 319 (true, L1740_cp2.1, L1740_cp2.2)) ∧ ptTest pL1740 (runFrom pL1740 (fmask pL1740) (cmask pL1740) (hmask pL1740) 1421 319 (true, L1740_cp2.1, L1740_cp2.2)) 1740 870 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1740_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1740_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1740_fin) true) L1740_seg1) L1740_seg2) (by decide) rfl L1740_fin ptTest_fst
noncomputable def H1740_cp1 : Nat × Nat := t7val% (fastRun pH1740 1 1004 (init pH1740) (init pH1740))
theorem H1740_seg1 : segOK pH1740 1 1004 (init pH1740) (init pH1740) H1740_cp1.1 H1740_cp1.2 = true := by
  decide +kernel
noncomputable def H1740_cp2 : Nat × Nat := t7val% (fastRun pH1740 1 1420 (init pH1740) (init pH1740))
theorem H1740_seg2 : segOK pH1740 1005 416 H1740_cp1.1 H1740_cp1.2 H1740_cp2.1 H1740_cp2.2 = true := by
  decide +kernel
theorem H1740_fin : (prmOK pH1740 1740 && ptTest pH1740 (runFrom pH1740 (fmask pH1740) (cmask pH1740) (hmask pH1740) 1421 319 (true, H1740_cp2.1, H1740_cp2.2)) 1740 870 true) = true := by
  decide +kernel
theorem H1740_ok : RunOK pH1740 1740 (runFrom pH1740 (fmask pH1740) (cmask pH1740) (hmask pH1740) 1421 319 (true, H1740_cp2.1, H1740_cp2.2)) ∧ ptTest pH1740 (runFrom pH1740 (fmask pH1740) (cmask pH1740) (hmask pH1740) 1421 319 (true, H1740_cp2.1, H1740_cp2.2)) 1740 870 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1740_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1740_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1740_fin) true) H1740_seg1) H1740_seg2) (by decide) rfl H1740_fin ptTest_fst
noncomputable def I1740_cp1 : Nat × Nat := t7val% (fastRun pI1740 1 1229 (init pI1740) (init pI1740))
theorem I1740_seg1 : segOK pI1740 1 1229 (init pI1740) (init pI1740) I1740_cp1.1 I1740_cp1.2 = true := by
  decide +kernel
theorem I1740_fin : (prmOK pI1740 1740 && intTest pI1740 (runFrom pI1740 (fmask pI1740) (cmask pI1740) (hmask pI1740) 1230 510 (true, I1740_cp1.1, I1740_cp1.2)) 1740 21 true) = true := by
  decide +kernel
theorem I1740_ok : RunOK pI1740 1740 (runFrom pI1740 (fmask pI1740) (cmask pI1740) (hmask pI1740) 1230 510 (true, I1740_cp1.1, I1740_cp1.2)) ∧ intTest pI1740 (runFrom pI1740 (fmask pI1740) (cmask pI1740) (hmask pI1740) 1230 510 (true, I1740_cp1.1, I1740_cp1.2)) 1740 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1740_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1740_fin) true) I1740_seg1) (by decide) rfl I1740_fin intTest_fst
theorem link1740 : linkOK pL1740 pH1740 pI1740 = true := by decide +kernel
theorem cvx1740 : ConvexBetweenHumps 1740 :=
  cvx_of L1740_ok H1740_ok I1740_ok link1740 (by decide)
theorem cenlink1740 : cenLinkOK pI1740 1740 = true := by decide +kernel
theorem cen1740 : CenterUniqueMin 1740 ∧ DipHyp 1740 ∧ OnePointHyps 1740 :=
  cen_of L1740_ok H1740_ok I1740_ok link1740 cenlink1740

/-! ### `N = 1741` -/

def pL1741 : Prm := ⟨80, 37, 40, 1743, 11, 18446744073709551616, 110190267864206402, 110190267864206402⟩
def pH1741 : Prm := ⟨80, 37, 40, 1743, 11, 18446744073709551616, 110191367375834178, 110191367375834178⟩
def pI1741 : Prm := ⟨67, 34, 30, 1743, 11, 18446744073709551616, 110190267864206402, 110191367375834178⟩
noncomputable def L1741_cp1 : Nat × Nat := t7val% (fastRun pL1741 1 1004 (init pL1741) (init pL1741))
theorem L1741_seg1 : segOK pL1741 1 1004 (init pL1741) (init pL1741) L1741_cp1.1 L1741_cp1.2 = true := by
  decide +kernel
noncomputable def L1741_cp2 : Nat × Nat := t7val% (fastRun pL1741 1 1421 (init pL1741) (init pL1741))
theorem L1741_seg2 : segOK pL1741 1005 417 L1741_cp1.1 L1741_cp1.2 L1741_cp2.1 L1741_cp2.2 = true := by
  decide +kernel
theorem L1741_fin : (prmOK pL1741 1741 && ptTest pL1741 (runFrom pL1741 (fmask pL1741) (cmask pL1741) (hmask pL1741) 1422 319 (true, L1741_cp2.1, L1741_cp2.2)) 1741 871 false) = true := by
  decide +kernel
theorem L1741_ok : RunOK pL1741 1741 (runFrom pL1741 (fmask pL1741) (cmask pL1741) (hmask pL1741) 1422 319 (true, L1741_cp2.1, L1741_cp2.2)) ∧ ptTest pL1741 (runFrom pL1741 (fmask pL1741) (cmask pL1741) (hmask pL1741) 1422 319 (true, L1741_cp2.1, L1741_cp2.2)) 1741 871 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1741_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1741_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1741_fin) true) L1741_seg1) L1741_seg2) (by decide) rfl L1741_fin ptTest_fst
noncomputable def H1741_cp1 : Nat × Nat := t7val% (fastRun pH1741 1 1004 (init pH1741) (init pH1741))
theorem H1741_seg1 : segOK pH1741 1 1004 (init pH1741) (init pH1741) H1741_cp1.1 H1741_cp1.2 = true := by
  decide +kernel
noncomputable def H1741_cp2 : Nat × Nat := t7val% (fastRun pH1741 1 1421 (init pH1741) (init pH1741))
theorem H1741_seg2 : segOK pH1741 1005 417 H1741_cp1.1 H1741_cp1.2 H1741_cp2.1 H1741_cp2.2 = true := by
  decide +kernel
theorem H1741_fin : (prmOK pH1741 1741 && ptTest pH1741 (runFrom pH1741 (fmask pH1741) (cmask pH1741) (hmask pH1741) 1422 319 (true, H1741_cp2.1, H1741_cp2.2)) 1741 871 true) = true := by
  decide +kernel
theorem H1741_ok : RunOK pH1741 1741 (runFrom pH1741 (fmask pH1741) (cmask pH1741) (hmask pH1741) 1422 319 (true, H1741_cp2.1, H1741_cp2.2)) ∧ ptTest pH1741 (runFrom pH1741 (fmask pH1741) (cmask pH1741) (hmask pH1741) 1422 319 (true, H1741_cp2.1, H1741_cp2.2)) 1741 871 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1741_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1741_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1741_fin) true) H1741_seg1) H1741_seg2) (by decide) rfl H1741_fin ptTest_fst
noncomputable def I1741_cp1 : Nat × Nat := t7val% (fastRun pI1741 1 1230 (init pI1741) (init pI1741))
theorem I1741_seg1 : segOK pI1741 1 1230 (init pI1741) (init pI1741) I1741_cp1.1 I1741_cp1.2 = true := by
  decide +kernel
theorem I1741_fin : (prmOK pI1741 1741 && intTest pI1741 (runFrom pI1741 (fmask pI1741) (cmask pI1741) (hmask pI1741) 1231 510 (true, I1741_cp1.1, I1741_cp1.2)) 1741 21 false) = true := by
  decide +kernel
theorem I1741_ok : RunOK pI1741 1741 (runFrom pI1741 (fmask pI1741) (cmask pI1741) (hmask pI1741) 1231 510 (true, I1741_cp1.1, I1741_cp1.2)) ∧ intTest pI1741 (runFrom pI1741 (fmask pI1741) (cmask pI1741) (hmask pI1741) 1231 510 (true, I1741_cp1.1, I1741_cp1.2)) 1741 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1741_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1741_fin) true) I1741_seg1) (by decide) rfl I1741_fin intTest_fst
theorem link1741 : linkOK pL1741 pH1741 pI1741 = true := by decide +kernel
theorem cvx1741 : ConvexBetweenHumps 1741 :=
  cvx_of L1741_ok H1741_ok I1741_ok link1741 (by decide)

/-! ### `N = 1742` -/

def pL1742 : Prm := ⟨80, 37, 40, 1744, 11, 18446744073709551616, 110138486205522490, 110138486205522490⟩
def pH1742 : Prm := ⟨80, 37, 40, 1744, 11, 18446744073709551616, 110139585717150266, 110139585717150266⟩
def pI1742 : Prm := ⟨69, 33, 33, 1744, 11, 18446744073709551616, 110138486205522490, 110139585717150266⟩
noncomputable def L1742_cp1 : Nat × Nat := t7val% (fastRun pL1742 1 1005 (init pL1742) (init pL1742))
theorem L1742_seg1 : segOK pL1742 1 1005 (init pL1742) (init pL1742) L1742_cp1.1 L1742_cp1.2 = true := by
  decide +kernel
noncomputable def L1742_cp2 : Nat × Nat := t7val% (fastRun pL1742 1 1421 (init pL1742) (init pL1742))
theorem L1742_seg2 : segOK pL1742 1006 416 L1742_cp1.1 L1742_cp1.2 L1742_cp2.1 L1742_cp2.2 = true := by
  decide +kernel
theorem L1742_fin : (prmOK pL1742 1742 && ptTest pL1742 (runFrom pL1742 (fmask pL1742) (cmask pL1742) (hmask pL1742) 1422 320 (true, L1742_cp2.1, L1742_cp2.2)) 1742 871 false) = true := by
  decide +kernel
theorem L1742_ok : RunOK pL1742 1742 (runFrom pL1742 (fmask pL1742) (cmask pL1742) (hmask pL1742) 1422 320 (true, L1742_cp2.1, L1742_cp2.2)) ∧ ptTest pL1742 (runFrom pL1742 (fmask pL1742) (cmask pL1742) (hmask pL1742) 1422 320 (true, L1742_cp2.1, L1742_cp2.2)) 1742 871 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1742_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1742_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1742_fin) true) L1742_seg1) L1742_seg2) (by decide) rfl L1742_fin ptTest_fst
noncomputable def H1742_cp1 : Nat × Nat := t7val% (fastRun pH1742 1 1005 (init pH1742) (init pH1742))
theorem H1742_seg1 : segOK pH1742 1 1005 (init pH1742) (init pH1742) H1742_cp1.1 H1742_cp1.2 = true := by
  decide +kernel
noncomputable def H1742_cp2 : Nat × Nat := t7val% (fastRun pH1742 1 1421 (init pH1742) (init pH1742))
theorem H1742_seg2 : segOK pH1742 1006 416 H1742_cp1.1 H1742_cp1.2 H1742_cp2.1 H1742_cp2.2 = true := by
  decide +kernel
theorem H1742_fin : (prmOK pH1742 1742 && ptTest pH1742 (runFrom pH1742 (fmask pH1742) (cmask pH1742) (hmask pH1742) 1422 320 (true, H1742_cp2.1, H1742_cp2.2)) 1742 871 true) = true := by
  decide +kernel
theorem H1742_ok : RunOK pH1742 1742 (runFrom pH1742 (fmask pH1742) (cmask pH1742) (hmask pH1742) 1422 320 (true, H1742_cp2.1, H1742_cp2.2)) ∧ ptTest pH1742 (runFrom pH1742 (fmask pH1742) (cmask pH1742) (hmask pH1742) 1422 320 (true, H1742_cp2.1, H1742_cp2.2)) 1742 871 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1742_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1742_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1742_fin) true) H1742_seg1) H1742_seg2) (by decide) rfl H1742_fin ptTest_fst
noncomputable def I1742_cp1 : Nat × Nat := t7val% (fastRun pI1742 1 1231 (init pI1742) (init pI1742))
theorem I1742_seg1 : segOK pI1742 1 1231 (init pI1742) (init pI1742) I1742_cp1.1 I1742_cp1.2 = true := by
  decide +kernel
theorem I1742_fin : (prmOK pI1742 1742 && intTest pI1742 (runFrom pI1742 (fmask pI1742) (cmask pI1742) (hmask pI1742) 1232 510 (true, I1742_cp1.1, I1742_cp1.2)) 1742 21 true) = true := by
  decide +kernel
theorem I1742_ok : RunOK pI1742 1742 (runFrom pI1742 (fmask pI1742) (cmask pI1742) (hmask pI1742) 1232 510 (true, I1742_cp1.1, I1742_cp1.2)) ∧ intTest pI1742 (runFrom pI1742 (fmask pI1742) (cmask pI1742) (hmask pI1742) 1232 510 (true, I1742_cp1.1, I1742_cp1.2)) 1742 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1742_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1742_fin) true) I1742_seg1) (by decide) rfl I1742_fin intTest_fst
theorem link1742 : linkOK pL1742 pH1742 pI1742 = true := by decide +kernel
theorem cvx1742 : ConvexBetweenHumps 1742 :=
  cvx_of L1742_ok H1742_ok I1742_ok link1742 (by decide)
theorem cenlink1742 : cenLinkOK pI1742 1742 = true := by decide +kernel
theorem cen1742 : CenterUniqueMin 1742 ∧ DipHyp 1742 ∧ OnePointHyps 1742 :=
  cen_of L1742_ok H1742_ok I1742_ok link1742 cenlink1742

/-! ### `N = 1743` -/

def pL1743 : Prm := ⟨80, 37, 40, 1745, 11, 18446744073709551616, 110086736129121725, 110086736129121725⟩
def pH1743 : Prm := ⟨80, 37, 40, 1745, 11, 18446744073709551616, 110087835640749501, 110087835640749501⟩
def pI1743 : Prm := ⟨67, 34, 30, 1745, 11, 18446744073709551616, 110086736129121725, 110087835640749501⟩
noncomputable def L1743_cp1 : Nat × Nat := t7val% (fastRun pL1743 1 1005 (init pL1743) (init pL1743))
theorem L1743_seg1 : segOK pL1743 1 1005 (init pL1743) (init pL1743) L1743_cp1.1 L1743_cp1.2 = true := by
  decide +kernel
noncomputable def L1743_cp2 : Nat × Nat := t7val% (fastRun pL1743 1 1422 (init pL1743) (init pL1743))
theorem L1743_seg2 : segOK pL1743 1006 417 L1743_cp1.1 L1743_cp1.2 L1743_cp2.1 L1743_cp2.2 = true := by
  decide +kernel
theorem L1743_fin : (prmOK pL1743 1743 && ptTest pL1743 (runFrom pL1743 (fmask pL1743) (cmask pL1743) (hmask pL1743) 1423 320 (true, L1743_cp2.1, L1743_cp2.2)) 1743 872 false) = true := by
  decide +kernel
theorem L1743_ok : RunOK pL1743 1743 (runFrom pL1743 (fmask pL1743) (cmask pL1743) (hmask pL1743) 1423 320 (true, L1743_cp2.1, L1743_cp2.2)) ∧ ptTest pL1743 (runFrom pL1743 (fmask pL1743) (cmask pL1743) (hmask pL1743) 1423 320 (true, L1743_cp2.1, L1743_cp2.2)) 1743 872 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1743_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1743_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1743_fin) true) L1743_seg1) L1743_seg2) (by decide) rfl L1743_fin ptTest_fst
noncomputable def H1743_cp1 : Nat × Nat := t7val% (fastRun pH1743 1 1005 (init pH1743) (init pH1743))
theorem H1743_seg1 : segOK pH1743 1 1005 (init pH1743) (init pH1743) H1743_cp1.1 H1743_cp1.2 = true := by
  decide +kernel
noncomputable def H1743_cp2 : Nat × Nat := t7val% (fastRun pH1743 1 1422 (init pH1743) (init pH1743))
theorem H1743_seg2 : segOK pH1743 1006 417 H1743_cp1.1 H1743_cp1.2 H1743_cp2.1 H1743_cp2.2 = true := by
  decide +kernel
theorem H1743_fin : (prmOK pH1743 1743 && ptTest pH1743 (runFrom pH1743 (fmask pH1743) (cmask pH1743) (hmask pH1743) 1423 320 (true, H1743_cp2.1, H1743_cp2.2)) 1743 872 true) = true := by
  decide +kernel
theorem H1743_ok : RunOK pH1743 1743 (runFrom pH1743 (fmask pH1743) (cmask pH1743) (hmask pH1743) 1423 320 (true, H1743_cp2.1, H1743_cp2.2)) ∧ ptTest pH1743 (runFrom pH1743 (fmask pH1743) (cmask pH1743) (hmask pH1743) 1423 320 (true, H1743_cp2.1, H1743_cp2.2)) 1743 872 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1743_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1743_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1743_fin) true) H1743_seg1) H1743_seg2) (by decide) rfl H1743_fin ptTest_fst
noncomputable def I1743_cp1 : Nat × Nat := t7val% (fastRun pI1743 1 1231 (init pI1743) (init pI1743))
theorem I1743_seg1 : segOK pI1743 1 1231 (init pI1743) (init pI1743) I1743_cp1.1 I1743_cp1.2 = true := by
  decide +kernel
theorem I1743_fin : (prmOK pI1743 1743 && intTest pI1743 (runFrom pI1743 (fmask pI1743) (cmask pI1743) (hmask pI1743) 1232 511 (true, I1743_cp1.1, I1743_cp1.2)) 1743 21 false) = true := by
  decide +kernel
theorem I1743_ok : RunOK pI1743 1743 (runFrom pI1743 (fmask pI1743) (cmask pI1743) (hmask pI1743) 1232 511 (true, I1743_cp1.1, I1743_cp1.2)) ∧ intTest pI1743 (runFrom pI1743 (fmask pI1743) (cmask pI1743) (hmask pI1743) 1232 511 (true, I1743_cp1.1, I1743_cp1.2)) 1743 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1743_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1743_fin) true) I1743_seg1) (by decide) rfl I1743_fin intTest_fst
theorem link1743 : linkOK pL1743 pH1743 pI1743 = true := by decide +kernel
theorem cvx1743 : ConvexBetweenHumps 1743 :=
  cvx_of L1743_ok H1743_ok I1743_ok link1743 (by decide)

/-! ### `N = 1744` -/

def pL1744 : Prm := ⟨80, 37, 40, 1746, 11, 18446744073709551616, 110035060040877446, 110035060040877446⟩
def pH1744 : Prm := ⟨80, 37, 40, 1746, 11, 18446744073709551616, 110036159552505222, 110036159552505222⟩
def pI1744 : Prm := ⟨67, 34, 30, 1746, 11, 18446744073709551616, 110035060040877446, 110036159552505222⟩
noncomputable def L1744_cp1 : Nat × Nat := t7val% (fastRun pL1744 1 1006 (init pL1744) (init pL1744))
theorem L1744_seg1 : segOK pL1744 1 1006 (init pL1744) (init pL1744) L1744_cp1.1 L1744_cp1.2 = true := by
  decide +kernel
noncomputable def L1744_cp2 : Nat × Nat := t7val% (fastRun pL1744 1 1423 (init pL1744) (init pL1744))
theorem L1744_seg2 : segOK pL1744 1007 417 L1744_cp1.1 L1744_cp1.2 L1744_cp2.1 L1744_cp2.2 = true := by
  decide +kernel
theorem L1744_fin : (prmOK pL1744 1744 && ptTest pL1744 (runFrom pL1744 (fmask pL1744) (cmask pL1744) (hmask pL1744) 1424 320 (true, L1744_cp2.1, L1744_cp2.2)) 1744 872 false) = true := by
  decide +kernel
theorem L1744_ok : RunOK pL1744 1744 (runFrom pL1744 (fmask pL1744) (cmask pL1744) (hmask pL1744) 1424 320 (true, L1744_cp2.1, L1744_cp2.2)) ∧ ptTest pL1744 (runFrom pL1744 (fmask pL1744) (cmask pL1744) (hmask pL1744) 1424 320 (true, L1744_cp2.1, L1744_cp2.2)) 1744 872 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1744_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1744_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1744_fin) true) L1744_seg1) L1744_seg2) (by decide) rfl L1744_fin ptTest_fst
noncomputable def H1744_cp1 : Nat × Nat := t7val% (fastRun pH1744 1 1006 (init pH1744) (init pH1744))
theorem H1744_seg1 : segOK pH1744 1 1006 (init pH1744) (init pH1744) H1744_cp1.1 H1744_cp1.2 = true := by
  decide +kernel
noncomputable def H1744_cp2 : Nat × Nat := t7val% (fastRun pH1744 1 1423 (init pH1744) (init pH1744))
theorem H1744_seg2 : segOK pH1744 1007 417 H1744_cp1.1 H1744_cp1.2 H1744_cp2.1 H1744_cp2.2 = true := by
  decide +kernel
theorem H1744_fin : (prmOK pH1744 1744 && ptTest pH1744 (runFrom pH1744 (fmask pH1744) (cmask pH1744) (hmask pH1744) 1424 320 (true, H1744_cp2.1, H1744_cp2.2)) 1744 872 true) = true := by
  decide +kernel
theorem H1744_ok : RunOK pH1744 1744 (runFrom pH1744 (fmask pH1744) (cmask pH1744) (hmask pH1744) 1424 320 (true, H1744_cp2.1, H1744_cp2.2)) ∧ ptTest pH1744 (runFrom pH1744 (fmask pH1744) (cmask pH1744) (hmask pH1744) 1424 320 (true, H1744_cp2.1, H1744_cp2.2)) 1744 872 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1744_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1744_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1744_fin) true) H1744_seg1) H1744_seg2) (by decide) rfl H1744_fin ptTest_fst
noncomputable def I1744_cp1 : Nat × Nat := t7val% (fastRun pI1744 1 1232 (init pI1744) (init pI1744))
theorem I1744_seg1 : segOK pI1744 1 1232 (init pI1744) (init pI1744) I1744_cp1.1 I1744_cp1.2 = true := by
  decide +kernel
theorem I1744_fin : (prmOK pI1744 1744 && intTest pI1744 (runFrom pI1744 (fmask pI1744) (cmask pI1744) (hmask pI1744) 1233 511 (true, I1744_cp1.1, I1744_cp1.2)) 1744 21 true) = true := by
  decide +kernel
theorem I1744_ok : RunOK pI1744 1744 (runFrom pI1744 (fmask pI1744) (cmask pI1744) (hmask pI1744) 1233 511 (true, I1744_cp1.1, I1744_cp1.2)) ∧ intTest pI1744 (runFrom pI1744 (fmask pI1744) (cmask pI1744) (hmask pI1744) 1233 511 (true, I1744_cp1.1, I1744_cp1.2)) 1744 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1744_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1744_fin) true) I1744_seg1) (by decide) rfl I1744_fin intTest_fst
theorem link1744 : linkOK pL1744 pH1744 pI1744 = true := by decide +kernel
theorem cvx1744 : ConvexBetweenHumps 1744 :=
  cvx_of L1744_ok H1744_ok I1744_ok link1744 (by decide)
theorem cenlink1744 : cenLinkOK pI1744 1744 = true := by decide +kernel
theorem cen1744 : CenterUniqueMin 1744 ∧ DipHyp 1744 ∧ OnePointHyps 1744 :=
  cen_of L1744_ok H1744_ok I1744_ok link1744 cenlink1744

/-! ### `N = 1745` -/

def pL1745 : Prm := ⟨80, 37, 40, 1747, 11, 18446744073709551616, 109983415442571914, 109983415442571914⟩
def pH1745 : Prm := ⟨80, 37, 40, 1747, 11, 18446744073709551616, 109984514954199690, 109984514954199690⟩
def pI1745 : Prm := ⟨67, 34, 30, 1747, 11, 18446744073709551616, 109983415442571914, 109984514954199690⟩
noncomputable def L1745_cp1 : Nat × Nat := t7val% (fastRun pL1745 1 1006 (init pL1745) (init pL1745))
theorem L1745_seg1 : segOK pL1745 1 1006 (init pL1745) (init pL1745) L1745_cp1.1 L1745_cp1.2 = true := by
  decide +kernel
noncomputable def L1745_cp2 : Nat × Nat := t7val% (fastRun pL1745 1 1424 (init pL1745) (init pL1745))
theorem L1745_seg2 : segOK pL1745 1007 418 L1745_cp1.1 L1745_cp1.2 L1745_cp2.1 L1745_cp2.2 = true := by
  decide +kernel
theorem L1745_fin : (prmOK pL1745 1745 && ptTest pL1745 (runFrom pL1745 (fmask pL1745) (cmask pL1745) (hmask pL1745) 1425 320 (true, L1745_cp2.1, L1745_cp2.2)) 1745 873 false) = true := by
  decide +kernel
theorem L1745_ok : RunOK pL1745 1745 (runFrom pL1745 (fmask pL1745) (cmask pL1745) (hmask pL1745) 1425 320 (true, L1745_cp2.1, L1745_cp2.2)) ∧ ptTest pL1745 (runFrom pL1745 (fmask pL1745) (cmask pL1745) (hmask pL1745) 1425 320 (true, L1745_cp2.1, L1745_cp2.2)) 1745 873 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1745_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1745_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1745_fin) true) L1745_seg1) L1745_seg2) (by decide) rfl L1745_fin ptTest_fst
noncomputable def H1745_cp1 : Nat × Nat := t7val% (fastRun pH1745 1 1006 (init pH1745) (init pH1745))
theorem H1745_seg1 : segOK pH1745 1 1006 (init pH1745) (init pH1745) H1745_cp1.1 H1745_cp1.2 = true := by
  decide +kernel
noncomputable def H1745_cp2 : Nat × Nat := t7val% (fastRun pH1745 1 1424 (init pH1745) (init pH1745))
theorem H1745_seg2 : segOK pH1745 1007 418 H1745_cp1.1 H1745_cp1.2 H1745_cp2.1 H1745_cp2.2 = true := by
  decide +kernel
theorem H1745_fin : (prmOK pH1745 1745 && ptTest pH1745 (runFrom pH1745 (fmask pH1745) (cmask pH1745) (hmask pH1745) 1425 320 (true, H1745_cp2.1, H1745_cp2.2)) 1745 873 true) = true := by
  decide +kernel
theorem H1745_ok : RunOK pH1745 1745 (runFrom pH1745 (fmask pH1745) (cmask pH1745) (hmask pH1745) 1425 320 (true, H1745_cp2.1, H1745_cp2.2)) ∧ ptTest pH1745 (runFrom pH1745 (fmask pH1745) (cmask pH1745) (hmask pH1745) 1425 320 (true, H1745_cp2.1, H1745_cp2.2)) 1745 873 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1745_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1745_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1745_fin) true) H1745_seg1) H1745_seg2) (by decide) rfl H1745_fin ptTest_fst
noncomputable def I1745_cp1 : Nat × Nat := t7val% (fastRun pI1745 1 1233 (init pI1745) (init pI1745))
theorem I1745_seg1 : segOK pI1745 1 1233 (init pI1745) (init pI1745) I1745_cp1.1 I1745_cp1.2 = true := by
  decide +kernel
theorem I1745_fin : (prmOK pI1745 1745 && intTest pI1745 (runFrom pI1745 (fmask pI1745) (cmask pI1745) (hmask pI1745) 1234 511 (true, I1745_cp1.1, I1745_cp1.2)) 1745 21 false) = true := by
  decide +kernel
theorem I1745_ok : RunOK pI1745 1745 (runFrom pI1745 (fmask pI1745) (cmask pI1745) (hmask pI1745) 1234 511 (true, I1745_cp1.1, I1745_cp1.2)) ∧ intTest pI1745 (runFrom pI1745 (fmask pI1745) (cmask pI1745) (hmask pI1745) 1234 511 (true, I1745_cp1.1, I1745_cp1.2)) 1745 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1745_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1745_fin) true) I1745_seg1) (by decide) rfl I1745_fin intTest_fst
theorem link1745 : linkOK pL1745 pH1745 pI1745 = true := by decide +kernel
theorem cvx1745 : ConvexBetweenHumps 1745 :=
  cvx_of L1745_ok H1745_ok I1745_ok link1745 (by decide)

/-! ### `N = 1746` -/

def pL1746 : Prm := ⟨80, 37, 40, 1748, 11, 18446744073709551616, 109931844592209365, 109931844592209365⟩
def pH1746 : Prm := ⟨80, 37, 40, 1748, 11, 18446744073709551616, 109932944103837141, 109932944103837141⟩
def pI1746 : Prm := ⟨67, 34, 30, 1748, 11, 18446744073709551616, 109931844592209365, 109932944103837141⟩
noncomputable def L1746_cp1 : Nat × Nat := t7val% (fastRun pL1746 1 1007 (init pL1746) (init pL1746))
theorem L1746_seg1 : segOK pL1746 1 1007 (init pL1746) (init pL1746) L1746_cp1.1 L1746_cp1.2 = true := by
  decide +kernel
noncomputable def L1746_cp2 : Nat × Nat := t7val% (fastRun pL1746 1 1425 (init pL1746) (init pL1746))
theorem L1746_seg2 : segOK pL1746 1008 418 L1746_cp1.1 L1746_cp1.2 L1746_cp2.1 L1746_cp2.2 = true := by
  decide +kernel
theorem L1746_fin : (prmOK pL1746 1746 && ptTest pL1746 (runFrom pL1746 (fmask pL1746) (cmask pL1746) (hmask pL1746) 1426 320 (true, L1746_cp2.1, L1746_cp2.2)) 1746 873 false) = true := by
  decide +kernel
theorem L1746_ok : RunOK pL1746 1746 (runFrom pL1746 (fmask pL1746) (cmask pL1746) (hmask pL1746) 1426 320 (true, L1746_cp2.1, L1746_cp2.2)) ∧ ptTest pL1746 (runFrom pL1746 (fmask pL1746) (cmask pL1746) (hmask pL1746) 1426 320 (true, L1746_cp2.1, L1746_cp2.2)) 1746 873 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1746_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1746_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1746_fin) true) L1746_seg1) L1746_seg2) (by decide) rfl L1746_fin ptTest_fst
noncomputable def H1746_cp1 : Nat × Nat := t7val% (fastRun pH1746 1 1007 (init pH1746) (init pH1746))
theorem H1746_seg1 : segOK pH1746 1 1007 (init pH1746) (init pH1746) H1746_cp1.1 H1746_cp1.2 = true := by
  decide +kernel
noncomputable def H1746_cp2 : Nat × Nat := t7val% (fastRun pH1746 1 1425 (init pH1746) (init pH1746))
theorem H1746_seg2 : segOK pH1746 1008 418 H1746_cp1.1 H1746_cp1.2 H1746_cp2.1 H1746_cp2.2 = true := by
  decide +kernel
theorem H1746_fin : (prmOK pH1746 1746 && ptTest pH1746 (runFrom pH1746 (fmask pH1746) (cmask pH1746) (hmask pH1746) 1426 320 (true, H1746_cp2.1, H1746_cp2.2)) 1746 873 true) = true := by
  decide +kernel
theorem H1746_ok : RunOK pH1746 1746 (runFrom pH1746 (fmask pH1746) (cmask pH1746) (hmask pH1746) 1426 320 (true, H1746_cp2.1, H1746_cp2.2)) ∧ ptTest pH1746 (runFrom pH1746 (fmask pH1746) (cmask pH1746) (hmask pH1746) 1426 320 (true, H1746_cp2.1, H1746_cp2.2)) 1746 873 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1746_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1746_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1746_fin) true) H1746_seg1) H1746_seg2) (by decide) rfl H1746_fin ptTest_fst
noncomputable def I1746_cp1 : Nat × Nat := t7val% (fastRun pI1746 1 1234 (init pI1746) (init pI1746))
theorem I1746_seg1 : segOK pI1746 1 1234 (init pI1746) (init pI1746) I1746_cp1.1 I1746_cp1.2 = true := by
  decide +kernel
theorem I1746_fin : (prmOK pI1746 1746 && intTest pI1746 (runFrom pI1746 (fmask pI1746) (cmask pI1746) (hmask pI1746) 1235 511 (true, I1746_cp1.1, I1746_cp1.2)) 1746 21 true) = true := by
  decide +kernel
theorem I1746_ok : RunOK pI1746 1746 (runFrom pI1746 (fmask pI1746) (cmask pI1746) (hmask pI1746) 1235 511 (true, I1746_cp1.1, I1746_cp1.2)) ∧ intTest pI1746 (runFrom pI1746 (fmask pI1746) (cmask pI1746) (hmask pI1746) 1235 511 (true, I1746_cp1.1, I1746_cp1.2)) 1746 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1746_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1746_fin) true) I1746_seg1) (by decide) rfl I1746_fin intTest_fst
theorem link1746 : linkOK pL1746 pH1746 pI1746 = true := by decide +kernel
theorem cvx1746 : ConvexBetweenHumps 1746 :=
  cvx_of L1746_ok H1746_ok I1746_ok link1746 (by decide)
theorem cenlink1746 : cenLinkOK pI1746 1746 = true := by decide +kernel
theorem cen1746 : CenterUniqueMin 1746 ∧ DipHyp 1746 ∧ OnePointHyps 1746 :=
  cen_of L1746_ok H1746_ok I1746_ok link1746 cenlink1746

/-! ### The range -/

theorem cvx_1734_1746 {N : ℕ} (h1 : 1734 ≤ N) (h2 : N ≤ 1746) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1739
  · by_cases h4 : N ≤ 1736
    · by_cases h6 : N ≤ 1734
      · obtain rfl : N = 1734 := by omega
        exact cvx1734
      · by_cases h8 : N ≤ 1735
        · obtain rfl : N = 1735 := by omega
          exact cvx1735
        · obtain rfl : N = 1736 := by omega
          exact cvx1736
    · by_cases h6 : N ≤ 1737
      · obtain rfl : N = 1737 := by omega
        exact cvx1737
      · by_cases h8 : N ≤ 1738
        · obtain rfl : N = 1738 := by omega
          exact cvx1738
        · obtain rfl : N = 1739 := by omega
          exact cvx1739
  · by_cases h4 : N ≤ 1742
    · by_cases h6 : N ≤ 1740
      · obtain rfl : N = 1740 := by omega
        exact cvx1740
      · by_cases h8 : N ≤ 1741
        · obtain rfl : N = 1741 := by omega
          exact cvx1741
        · obtain rfl : N = 1742 := by omega
          exact cvx1742
    · by_cases h6 : N ≤ 1744
      · by_cases h8 : N ≤ 1743
        · obtain rfl : N = 1743 := by omega
          exact cvx1743
        · obtain rfl : N = 1744 := by omega
          exact cvx1744
      · by_cases h8 : N ≤ 1745
        · obtain rfl : N = 1745 := by omega
          exact cvx1745
        · obtain rfl : N = 1746 := by omega
          exact cvx1746

theorem cen_1734_1746 {N : ℕ} (h1 : 1734 ≤ N) (h2 : N ≤ 1746) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1738
  · by_cases h4 : N ≤ 1734
    · obtain rfl : N = 1734 := by omega
      exact cen1734
    · by_cases h6 : N ≤ 1736
      · obtain rfl : N = 1736 := by omega
        exact cen1736
      · obtain rfl : N = 1738 := by omega
        exact cen1738
  · by_cases h4 : N ≤ 1742
    · by_cases h6 : N ≤ 1740
      · obtain rfl : N = 1740 := by omega
        exact cen1740
      · obtain rfl : N = 1742 := by omega
        exact cen1742
    · by_cases h6 : N ≤ 1744
      · obtain rfl : N = 1744 := by omega
        exact cen1744
      · obtain rfl : N = 1746 := by omega
        exact cen1746

end Kagey131.PaperD.T7
