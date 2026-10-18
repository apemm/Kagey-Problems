import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1898, …, 1908` (generated)

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

/-! ### `N = 1898` -/

def pL1898 : Prm := ⟨80, 37, 40, 1900, 11, 18446744073709551616, 102657300889313909, 102657300889313909⟩
def pH1898 : Prm := ⟨80, 37, 40, 1900, 11, 18446744073709551616, 102658400400941685, 102658400400941685⟩
def pI1898 : Prm := ⟨68, 34, 31, 1900, 11, 18446744073709551616, 102657300889313909, 102658400400941685⟩
noncomputable def L1898_cp1 : Nat × Nat := t7val% (fastRun pL1898 1 1095 (init pL1898) (init pL1898))
theorem L1898_seg1 : segOK pL1898 1 1095 (init pL1898) (init pL1898) L1898_cp1.1 L1898_cp1.2 = true := by
  decide +kernel
noncomputable def L1898_cp2 : Nat × Nat := t7val% (fastRun pL1898 1 1549 (init pL1898) (init pL1898))
theorem L1898_seg2 : segOK pL1898 1096 454 L1898_cp1.1 L1898_cp1.2 L1898_cp2.1 L1898_cp2.2 = true := by
  decide +kernel
theorem L1898_fin : (prmOK pL1898 1898 && ptTest pL1898 (runFrom pL1898 (fmask pL1898) (cmask pL1898) (hmask pL1898) 1550 348 (true, L1898_cp2.1, L1898_cp2.2)) 1898 949 false) = true := by
  decide +kernel
theorem L1898_ok : RunOK pL1898 1898 (runFrom pL1898 (fmask pL1898) (cmask pL1898) (hmask pL1898) 1550 348 (true, L1898_cp2.1, L1898_cp2.2)) ∧ ptTest pL1898 (runFrom pL1898 (fmask pL1898) (cmask pL1898) (hmask pL1898) 1550 348 (true, L1898_cp2.1, L1898_cp2.2)) 1898 949 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1898_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1898_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1898_fin) true) L1898_seg1) L1898_seg2) (by decide) rfl L1898_fin ptTest_fst
noncomputable def H1898_cp1 : Nat × Nat := t7val% (fastRun pH1898 1 1095 (init pH1898) (init pH1898))
theorem H1898_seg1 : segOK pH1898 1 1095 (init pH1898) (init pH1898) H1898_cp1.1 H1898_cp1.2 = true := by
  decide +kernel
noncomputable def H1898_cp2 : Nat × Nat := t7val% (fastRun pH1898 1 1549 (init pH1898) (init pH1898))
theorem H1898_seg2 : segOK pH1898 1096 454 H1898_cp1.1 H1898_cp1.2 H1898_cp2.1 H1898_cp2.2 = true := by
  decide +kernel
theorem H1898_fin : (prmOK pH1898 1898 && ptTest pH1898 (runFrom pH1898 (fmask pH1898) (cmask pH1898) (hmask pH1898) 1550 348 (true, H1898_cp2.1, H1898_cp2.2)) 1898 949 true) = true := by
  decide +kernel
theorem H1898_ok : RunOK pH1898 1898 (runFrom pH1898 (fmask pH1898) (cmask pH1898) (hmask pH1898) 1550 348 (true, H1898_cp2.1, H1898_cp2.2)) ∧ ptTest pH1898 (runFrom pH1898 (fmask pH1898) (cmask pH1898) (hmask pH1898) 1550 348 (true, H1898_cp2.1, H1898_cp2.2)) 1898 949 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1898_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1898_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1898_fin) true) H1898_seg1) H1898_seg2) (by decide) rfl H1898_fin ptTest_fst
noncomputable def I1898_cp1 : Nat × Nat := t7val% (fastRun pI1898 1 1095 (init pI1898) (init pI1898))
theorem I1898_seg1 : segOK pI1898 1 1095 (init pI1898) (init pI1898) I1898_cp1.1 I1898_cp1.2 = true := by
  decide +kernel
noncomputable def I1898_cp2 : Nat × Nat := t7val% (fastRun pI1898 1 1549 (init pI1898) (init pI1898))
theorem I1898_seg2 : segOK pI1898 1096 454 I1898_cp1.1 I1898_cp1.2 I1898_cp2.1 I1898_cp2.2 = true := by
  decide +kernel
theorem I1898_fin : (prmOK pI1898 1898 && intTest pI1898 (runFrom pI1898 (fmask pI1898) (cmask pI1898) (hmask pI1898) 1550 348 (true, I1898_cp2.1, I1898_cp2.2)) 1898 21 true) = true := by
  decide +kernel
theorem I1898_ok : RunOK pI1898 1898 (runFrom pI1898 (fmask pI1898) (cmask pI1898) (hmask pI1898) 1550 348 (true, I1898_cp2.1, I1898_cp2.2)) ∧ intTest pI1898 (runFrom pI1898 (fmask pI1898) (cmask pI1898) (hmask pI1898) 1550 348 (true, I1898_cp2.1, I1898_cp2.2)) 1898 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1898_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1898_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1898_fin) true) I1898_seg1) I1898_seg2) (by decide) rfl I1898_fin intTest_fst
theorem link1898 : linkOK pL1898 pH1898 pI1898 = true := by decide +kernel
theorem cvx1898 : ConvexBetweenHumps 1898 :=
  cvx_of L1898_ok H1898_ok I1898_ok link1898 (by decide)
theorem cenlink1898 : cenLinkOK pI1898 1898 = true := by decide +kernel
theorem cen1898 : CenterUniqueMin 1898 ∧ DipHyp 1898 ∧ OnePointHyps 1898 :=
  cen_of L1898_ok H1898_ok I1898_ok link1898 cenlink1898

/-! ### `N = 1899` -/

def pL1899 : Prm := ⟨80, 37, 40, 1901, 11, 18446744073709551616, 102612878448534632, 102612878448534632⟩
def pH1899 : Prm := ⟨80, 37, 40, 1901, 11, 18446744073709551616, 102613977960162408, 102613977960162408⟩
def pI1899 : Prm := ⟨68, 34, 31, 1901, 11, 18446744073709551616, 102612878448534632, 102613977960162408⟩
noncomputable def L1899_cp1 : Nat × Nat := t7val% (fastRun pL1899 1 1095 (init pL1899) (init pL1899))
theorem L1899_seg1 : segOK pL1899 1 1095 (init pL1899) (init pL1899) L1899_cp1.1 L1899_cp1.2 = true := by
  decide +kernel
noncomputable def L1899_cp2 : Nat × Nat := t7val% (fastRun pL1899 1 1550 (init pL1899) (init pL1899))
theorem L1899_seg2 : segOK pL1899 1096 455 L1899_cp1.1 L1899_cp1.2 L1899_cp2.1 L1899_cp2.2 = true := by
  decide +kernel
theorem L1899_fin : (prmOK pL1899 1899 && ptTest pL1899 (runFrom pL1899 (fmask pL1899) (cmask pL1899) (hmask pL1899) 1551 348 (true, L1899_cp2.1, L1899_cp2.2)) 1899 950 false) = true := by
  decide +kernel
theorem L1899_ok : RunOK pL1899 1899 (runFrom pL1899 (fmask pL1899) (cmask pL1899) (hmask pL1899) 1551 348 (true, L1899_cp2.1, L1899_cp2.2)) ∧ ptTest pL1899 (runFrom pL1899 (fmask pL1899) (cmask pL1899) (hmask pL1899) 1551 348 (true, L1899_cp2.1, L1899_cp2.2)) 1899 950 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1899_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1899_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1899_fin) true) L1899_seg1) L1899_seg2) (by decide) rfl L1899_fin ptTest_fst
noncomputable def H1899_cp1 : Nat × Nat := t7val% (fastRun pH1899 1 1095 (init pH1899) (init pH1899))
theorem H1899_seg1 : segOK pH1899 1 1095 (init pH1899) (init pH1899) H1899_cp1.1 H1899_cp1.2 = true := by
  decide +kernel
noncomputable def H1899_cp2 : Nat × Nat := t7val% (fastRun pH1899 1 1550 (init pH1899) (init pH1899))
theorem H1899_seg2 : segOK pH1899 1096 455 H1899_cp1.1 H1899_cp1.2 H1899_cp2.1 H1899_cp2.2 = true := by
  decide +kernel
theorem H1899_fin : (prmOK pH1899 1899 && ptTest pH1899 (runFrom pH1899 (fmask pH1899) (cmask pH1899) (hmask pH1899) 1551 348 (true, H1899_cp2.1, H1899_cp2.2)) 1899 950 true) = true := by
  decide +kernel
theorem H1899_ok : RunOK pH1899 1899 (runFrom pH1899 (fmask pH1899) (cmask pH1899) (hmask pH1899) 1551 348 (true, H1899_cp2.1, H1899_cp2.2)) ∧ ptTest pH1899 (runFrom pH1899 (fmask pH1899) (cmask pH1899) (hmask pH1899) 1551 348 (true, H1899_cp2.1, H1899_cp2.2)) 1899 950 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1899_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1899_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1899_fin) true) H1899_seg1) H1899_seg2) (by decide) rfl H1899_fin ptTest_fst
noncomputable def I1899_cp1 : Nat × Nat := t7val% (fastRun pI1899 1 1095 (init pI1899) (init pI1899))
theorem I1899_seg1 : segOK pI1899 1 1095 (init pI1899) (init pI1899) I1899_cp1.1 I1899_cp1.2 = true := by
  decide +kernel
noncomputable def I1899_cp2 : Nat × Nat := t7val% (fastRun pI1899 1 1550 (init pI1899) (init pI1899))
theorem I1899_seg2 : segOK pI1899 1096 455 I1899_cp1.1 I1899_cp1.2 I1899_cp2.1 I1899_cp2.2 = true := by
  decide +kernel
theorem I1899_fin : (prmOK pI1899 1899 && intTest pI1899 (runFrom pI1899 (fmask pI1899) (cmask pI1899) (hmask pI1899) 1551 348 (true, I1899_cp2.1, I1899_cp2.2)) 1899 21 false) = true := by
  decide +kernel
theorem I1899_ok : RunOK pI1899 1899 (runFrom pI1899 (fmask pI1899) (cmask pI1899) (hmask pI1899) 1551 348 (true, I1899_cp2.1, I1899_cp2.2)) ∧ intTest pI1899 (runFrom pI1899 (fmask pI1899) (cmask pI1899) (hmask pI1899) 1551 348 (true, I1899_cp2.1, I1899_cp2.2)) 1899 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1899_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1899_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1899_fin) true) I1899_seg1) I1899_seg2) (by decide) rfl I1899_fin intTest_fst
theorem link1899 : linkOK pL1899 pH1899 pI1899 = true := by decide +kernel
theorem cvx1899 : ConvexBetweenHumps 1899 :=
  cvx_of L1899_ok H1899_ok I1899_ok link1899 (by decide)

/-! ### `N = 1900` -/

def pL1900 : Prm := ⟨80, 37, 40, 1902, 11, 18446744073709551616, 102568514027561621, 102568514027561621⟩
def pH1900 : Prm := ⟨80, 37, 40, 1902, 11, 18446744073709551616, 102569613539189397, 102569613539189397⟩
def pI1900 : Prm := ⟨68, 34, 31, 1902, 11, 18446744073709551616, 102568514027561621, 102569613539189397⟩
noncomputable def L1900_cp1 : Nat × Nat := t7val% (fastRun pL1900 1 1096 (init pL1900) (init pL1900))
theorem L1900_seg1 : segOK pL1900 1 1096 (init pL1900) (init pL1900) L1900_cp1.1 L1900_cp1.2 = true := by
  decide +kernel
noncomputable def L1900_cp2 : Nat × Nat := t7val% (fastRun pL1900 1 1550 (init pL1900) (init pL1900))
theorem L1900_seg2 : segOK pL1900 1097 454 L1900_cp1.1 L1900_cp1.2 L1900_cp2.1 L1900_cp2.2 = true := by
  decide +kernel
theorem L1900_fin : (prmOK pL1900 1900 && ptTest pL1900 (runFrom pL1900 (fmask pL1900) (cmask pL1900) (hmask pL1900) 1551 349 (true, L1900_cp2.1, L1900_cp2.2)) 1900 950 false) = true := by
  decide +kernel
theorem L1900_ok : RunOK pL1900 1900 (runFrom pL1900 (fmask pL1900) (cmask pL1900) (hmask pL1900) 1551 349 (true, L1900_cp2.1, L1900_cp2.2)) ∧ ptTest pL1900 (runFrom pL1900 (fmask pL1900) (cmask pL1900) (hmask pL1900) 1551 349 (true, L1900_cp2.1, L1900_cp2.2)) 1900 950 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1900_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1900_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1900_fin) true) L1900_seg1) L1900_seg2) (by decide) rfl L1900_fin ptTest_fst
noncomputable def H1900_cp1 : Nat × Nat := t7val% (fastRun pH1900 1 1096 (init pH1900) (init pH1900))
theorem H1900_seg1 : segOK pH1900 1 1096 (init pH1900) (init pH1900) H1900_cp1.1 H1900_cp1.2 = true := by
  decide +kernel
noncomputable def H1900_cp2 : Nat × Nat := t7val% (fastRun pH1900 1 1550 (init pH1900) (init pH1900))
theorem H1900_seg2 : segOK pH1900 1097 454 H1900_cp1.1 H1900_cp1.2 H1900_cp2.1 H1900_cp2.2 = true := by
  decide +kernel
theorem H1900_fin : (prmOK pH1900 1900 && ptTest pH1900 (runFrom pH1900 (fmask pH1900) (cmask pH1900) (hmask pH1900) 1551 349 (true, H1900_cp2.1, H1900_cp2.2)) 1900 950 true) = true := by
  decide +kernel
theorem H1900_ok : RunOK pH1900 1900 (runFrom pH1900 (fmask pH1900) (cmask pH1900) (hmask pH1900) 1551 349 (true, H1900_cp2.1, H1900_cp2.2)) ∧ ptTest pH1900 (runFrom pH1900 (fmask pH1900) (cmask pH1900) (hmask pH1900) 1551 349 (true, H1900_cp2.1, H1900_cp2.2)) 1900 950 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1900_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1900_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1900_fin) true) H1900_seg1) H1900_seg2) (by decide) rfl H1900_fin ptTest_fst
noncomputable def I1900_cp1 : Nat × Nat := t7val% (fastRun pI1900 1 1096 (init pI1900) (init pI1900))
theorem I1900_seg1 : segOK pI1900 1 1096 (init pI1900) (init pI1900) I1900_cp1.1 I1900_cp1.2 = true := by
  decide +kernel
noncomputable def I1900_cp2 : Nat × Nat := t7val% (fastRun pI1900 1 1550 (init pI1900) (init pI1900))
theorem I1900_seg2 : segOK pI1900 1097 454 I1900_cp1.1 I1900_cp1.2 I1900_cp2.1 I1900_cp2.2 = true := by
  decide +kernel
theorem I1900_fin : (prmOK pI1900 1900 && intTest pI1900 (runFrom pI1900 (fmask pI1900) (cmask pI1900) (hmask pI1900) 1551 349 (true, I1900_cp2.1, I1900_cp2.2)) 1900 21 true) = true := by
  decide +kernel
theorem I1900_ok : RunOK pI1900 1900 (runFrom pI1900 (fmask pI1900) (cmask pI1900) (hmask pI1900) 1551 349 (true, I1900_cp2.1, I1900_cp2.2)) ∧ intTest pI1900 (runFrom pI1900 (fmask pI1900) (cmask pI1900) (hmask pI1900) 1551 349 (true, I1900_cp2.1, I1900_cp2.2)) 1900 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1900_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1900_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1900_fin) true) I1900_seg1) I1900_seg2) (by decide) rfl I1900_fin intTest_fst
theorem link1900 : linkOK pL1900 pH1900 pI1900 = true := by decide +kernel
theorem cvx1900 : ConvexBetweenHumps 1900 :=
  cvx_of L1900_ok H1900_ok I1900_ok link1900 (by decide)
theorem cenlink1900 : cenLinkOK pI1900 1900 = true := by decide +kernel
theorem cen1900 : CenterUniqueMin 1900 ∧ DipHyp 1900 ∧ OnePointHyps 1900 :=
  cen_of L1900_ok H1900_ok I1900_ok link1900 cenlink1900

/-! ### `N = 1901` -/

def pL1901 : Prm := ⟨80, 37, 40, 1903, 11, 18446744073709551616, 102524174892942664, 102524174892942664⟩
def pH1901 : Prm := ⟨80, 37, 40, 1903, 11, 18446744073709551616, 102525274404570440, 102525274404570440⟩
def pI1901 : Prm := ⟨68, 34, 31, 1903, 11, 18446744073709551616, 102524174892942664, 102525274404570440⟩
noncomputable def L1901_cp1 : Nat × Nat := t7val% (fastRun pL1901 1 1097 (init pL1901) (init pL1901))
theorem L1901_seg1 : segOK pL1901 1 1097 (init pL1901) (init pL1901) L1901_cp1.1 L1901_cp1.2 = true := by
  decide +kernel
noncomputable def L1901_cp2 : Nat × Nat := t7val% (fastRun pL1901 1 1551 (init pL1901) (init pL1901))
theorem L1901_seg2 : segOK pL1901 1098 454 L1901_cp1.1 L1901_cp1.2 L1901_cp2.1 L1901_cp2.2 = true := by
  decide +kernel
theorem L1901_fin : (prmOK pL1901 1901 && ptTest pL1901 (runFrom pL1901 (fmask pL1901) (cmask pL1901) (hmask pL1901) 1552 349 (true, L1901_cp2.1, L1901_cp2.2)) 1901 951 false) = true := by
  decide +kernel
theorem L1901_ok : RunOK pL1901 1901 (runFrom pL1901 (fmask pL1901) (cmask pL1901) (hmask pL1901) 1552 349 (true, L1901_cp2.1, L1901_cp2.2)) ∧ ptTest pL1901 (runFrom pL1901 (fmask pL1901) (cmask pL1901) (hmask pL1901) 1552 349 (true, L1901_cp2.1, L1901_cp2.2)) 1901 951 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1901_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1901_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1901_fin) true) L1901_seg1) L1901_seg2) (by decide) rfl L1901_fin ptTest_fst
noncomputable def H1901_cp1 : Nat × Nat := t7val% (fastRun pH1901 1 1097 (init pH1901) (init pH1901))
theorem H1901_seg1 : segOK pH1901 1 1097 (init pH1901) (init pH1901) H1901_cp1.1 H1901_cp1.2 = true := by
  decide +kernel
noncomputable def H1901_cp2 : Nat × Nat := t7val% (fastRun pH1901 1 1551 (init pH1901) (init pH1901))
theorem H1901_seg2 : segOK pH1901 1098 454 H1901_cp1.1 H1901_cp1.2 H1901_cp2.1 H1901_cp2.2 = true := by
  decide +kernel
theorem H1901_fin : (prmOK pH1901 1901 && ptTest pH1901 (runFrom pH1901 (fmask pH1901) (cmask pH1901) (hmask pH1901) 1552 349 (true, H1901_cp2.1, H1901_cp2.2)) 1901 951 true) = true := by
  decide +kernel
theorem H1901_ok : RunOK pH1901 1901 (runFrom pH1901 (fmask pH1901) (cmask pH1901) (hmask pH1901) 1552 349 (true, H1901_cp2.1, H1901_cp2.2)) ∧ ptTest pH1901 (runFrom pH1901 (fmask pH1901) (cmask pH1901) (hmask pH1901) 1552 349 (true, H1901_cp2.1, H1901_cp2.2)) 1901 951 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1901_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1901_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1901_fin) true) H1901_seg1) H1901_seg2) (by decide) rfl H1901_fin ptTest_fst
noncomputable def I1901_cp1 : Nat × Nat := t7val% (fastRun pI1901 1 1097 (init pI1901) (init pI1901))
theorem I1901_seg1 : segOK pI1901 1 1097 (init pI1901) (init pI1901) I1901_cp1.1 I1901_cp1.2 = true := by
  decide +kernel
noncomputable def I1901_cp2 : Nat × Nat := t7val% (fastRun pI1901 1 1551 (init pI1901) (init pI1901))
theorem I1901_seg2 : segOK pI1901 1098 454 I1901_cp1.1 I1901_cp1.2 I1901_cp2.1 I1901_cp2.2 = true := by
  decide +kernel
theorem I1901_fin : (prmOK pI1901 1901 && intTest pI1901 (runFrom pI1901 (fmask pI1901) (cmask pI1901) (hmask pI1901) 1552 349 (true, I1901_cp2.1, I1901_cp2.2)) 1901 22 false) = true := by
  decide +kernel
theorem I1901_ok : RunOK pI1901 1901 (runFrom pI1901 (fmask pI1901) (cmask pI1901) (hmask pI1901) 1552 349 (true, I1901_cp2.1, I1901_cp2.2)) ∧ intTest pI1901 (runFrom pI1901 (fmask pI1901) (cmask pI1901) (hmask pI1901) 1552 349 (true, I1901_cp2.1, I1901_cp2.2)) 1901 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1901_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1901_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1901_fin) true) I1901_seg1) I1901_seg2) (by decide) rfl I1901_fin intTest_fst
theorem link1901 : linkOK pL1901 pH1901 pI1901 = true := by decide +kernel
theorem cvx1901 : ConvexBetweenHumps 1901 :=
  cvx_of L1901_ok H1901_ok I1901_ok link1901 (by decide)

/-! ### `N = 1902` -/

def pL1902 : Prm := ⟨80, 37, 40, 1904, 11, 18446744073709551616, 102479893605117961, 102479893605117961⟩
def pH1902 : Prm := ⟨80, 37, 40, 1904, 11, 18446744073709551616, 102480993116745737, 102480993116745737⟩
def pI1902 : Prm := ⟨68, 34, 31, 1904, 11, 18446744073709551616, 102479893605117961, 102480993116745737⟩
noncomputable def L1902_cp1 : Nat × Nat := t7val% (fastRun pL1902 1 1097 (init pL1902) (init pL1902))
theorem L1902_seg1 : segOK pL1902 1 1097 (init pL1902) (init pL1902) L1902_cp1.1 L1902_cp1.2 = true := by
  decide +kernel
noncomputable def L1902_cp2 : Nat × Nat := t7val% (fastRun pL1902 1 1552 (init pL1902) (init pL1902))
theorem L1902_seg2 : segOK pL1902 1098 455 L1902_cp1.1 L1902_cp1.2 L1902_cp2.1 L1902_cp2.2 = true := by
  decide +kernel
theorem L1902_fin : (prmOK pL1902 1902 && ptTest pL1902 (runFrom pL1902 (fmask pL1902) (cmask pL1902) (hmask pL1902) 1553 349 (true, L1902_cp2.1, L1902_cp2.2)) 1902 951 false) = true := by
  decide +kernel
theorem L1902_ok : RunOK pL1902 1902 (runFrom pL1902 (fmask pL1902) (cmask pL1902) (hmask pL1902) 1553 349 (true, L1902_cp2.1, L1902_cp2.2)) ∧ ptTest pL1902 (runFrom pL1902 (fmask pL1902) (cmask pL1902) (hmask pL1902) 1553 349 (true, L1902_cp2.1, L1902_cp2.2)) 1902 951 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1902_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1902_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1902_fin) true) L1902_seg1) L1902_seg2) (by decide) rfl L1902_fin ptTest_fst
noncomputable def H1902_cp1 : Nat × Nat := t7val% (fastRun pH1902 1 1097 (init pH1902) (init pH1902))
theorem H1902_seg1 : segOK pH1902 1 1097 (init pH1902) (init pH1902) H1902_cp1.1 H1902_cp1.2 = true := by
  decide +kernel
noncomputable def H1902_cp2 : Nat × Nat := t7val% (fastRun pH1902 1 1552 (init pH1902) (init pH1902))
theorem H1902_seg2 : segOK pH1902 1098 455 H1902_cp1.1 H1902_cp1.2 H1902_cp2.1 H1902_cp2.2 = true := by
  decide +kernel
theorem H1902_fin : (prmOK pH1902 1902 && ptTest pH1902 (runFrom pH1902 (fmask pH1902) (cmask pH1902) (hmask pH1902) 1553 349 (true, H1902_cp2.1, H1902_cp2.2)) 1902 951 true) = true := by
  decide +kernel
theorem H1902_ok : RunOK pH1902 1902 (runFrom pH1902 (fmask pH1902) (cmask pH1902) (hmask pH1902) 1553 349 (true, H1902_cp2.1, H1902_cp2.2)) ∧ ptTest pH1902 (runFrom pH1902 (fmask pH1902) (cmask pH1902) (hmask pH1902) 1553 349 (true, H1902_cp2.1, H1902_cp2.2)) 1902 951 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1902_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1902_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1902_fin) true) H1902_seg1) H1902_seg2) (by decide) rfl H1902_fin ptTest_fst
noncomputable def I1902_cp1 : Nat × Nat := t7val% (fastRun pI1902 1 1097 (init pI1902) (init pI1902))
theorem I1902_seg1 : segOK pI1902 1 1097 (init pI1902) (init pI1902) I1902_cp1.1 I1902_cp1.2 = true := by
  decide +kernel
noncomputable def I1902_cp2 : Nat × Nat := t7val% (fastRun pI1902 1 1552 (init pI1902) (init pI1902))
theorem I1902_seg2 : segOK pI1902 1098 455 I1902_cp1.1 I1902_cp1.2 I1902_cp2.1 I1902_cp2.2 = true := by
  decide +kernel
theorem I1902_fin : (prmOK pI1902 1902 && intTest pI1902 (runFrom pI1902 (fmask pI1902) (cmask pI1902) (hmask pI1902) 1553 349 (true, I1902_cp2.1, I1902_cp2.2)) 1902 22 true) = true := by
  decide +kernel
theorem I1902_ok : RunOK pI1902 1902 (runFrom pI1902 (fmask pI1902) (cmask pI1902) (hmask pI1902) 1553 349 (true, I1902_cp2.1, I1902_cp2.2)) ∧ intTest pI1902 (runFrom pI1902 (fmask pI1902) (cmask pI1902) (hmask pI1902) 1553 349 (true, I1902_cp2.1, I1902_cp2.2)) 1902 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1902_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1902_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1902_fin) true) I1902_seg1) I1902_seg2) (by decide) rfl I1902_fin intTest_fst
theorem link1902 : linkOK pL1902 pH1902 pI1902 = true := by decide +kernel
theorem cvx1902 : ConvexBetweenHumps 1902 :=
  cvx_of L1902_ok H1902_ok I1902_ok link1902 (by decide)
theorem cenlink1902 : cenLinkOK pI1902 1902 = true := by decide +kernel
theorem cen1902 : CenterUniqueMin 1902 ∧ DipHyp 1902 ∧ OnePointHyps 1902 :=
  cen_of L1902_ok H1902_ok I1902_ok link1902 cenlink1902

/-! ### `N = 1903` -/

def pL1903 : Prm := ⟨80, 37, 40, 1905, 11, 18446744073709551616, 102435637535357464, 102435637535357464⟩
def pH1903 : Prm := ⟨80, 37, 40, 1905, 11, 18446744073709551616, 102436737046985240, 102436737046985240⟩
def pI1903 : Prm := ⟨68, 34, 31, 1905, 11, 18446744073709551616, 102435637535357464, 102436737046985240⟩
noncomputable def L1903_cp1 : Nat × Nat := t7val% (fastRun pL1903 1 1098 (init pL1903) (init pL1903))
theorem L1903_seg1 : segOK pL1903 1 1098 (init pL1903) (init pL1903) L1903_cp1.1 L1903_cp1.2 = true := by
  decide +kernel
noncomputable def L1903_cp2 : Nat × Nat := t7val% (fastRun pL1903 1 1553 (init pL1903) (init pL1903))
theorem L1903_seg2 : segOK pL1903 1099 455 L1903_cp1.1 L1903_cp1.2 L1903_cp2.1 L1903_cp2.2 = true := by
  decide +kernel
theorem L1903_fin : (prmOK pL1903 1903 && ptTest pL1903 (runFrom pL1903 (fmask pL1903) (cmask pL1903) (hmask pL1903) 1554 349 (true, L1903_cp2.1, L1903_cp2.2)) 1903 952 false) = true := by
  decide +kernel
theorem L1903_ok : RunOK pL1903 1903 (runFrom pL1903 (fmask pL1903) (cmask pL1903) (hmask pL1903) 1554 349 (true, L1903_cp2.1, L1903_cp2.2)) ∧ ptTest pL1903 (runFrom pL1903 (fmask pL1903) (cmask pL1903) (hmask pL1903) 1554 349 (true, L1903_cp2.1, L1903_cp2.2)) 1903 952 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1903_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1903_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1903_fin) true) L1903_seg1) L1903_seg2) (by decide) rfl L1903_fin ptTest_fst
noncomputable def H1903_cp1 : Nat × Nat := t7val% (fastRun pH1903 1 1098 (init pH1903) (init pH1903))
theorem H1903_seg1 : segOK pH1903 1 1098 (init pH1903) (init pH1903) H1903_cp1.1 H1903_cp1.2 = true := by
  decide +kernel
noncomputable def H1903_cp2 : Nat × Nat := t7val% (fastRun pH1903 1 1553 (init pH1903) (init pH1903))
theorem H1903_seg2 : segOK pH1903 1099 455 H1903_cp1.1 H1903_cp1.2 H1903_cp2.1 H1903_cp2.2 = true := by
  decide +kernel
theorem H1903_fin : (prmOK pH1903 1903 && ptTest pH1903 (runFrom pH1903 (fmask pH1903) (cmask pH1903) (hmask pH1903) 1554 349 (true, H1903_cp2.1, H1903_cp2.2)) 1903 952 true) = true := by
  decide +kernel
theorem H1903_ok : RunOK pH1903 1903 (runFrom pH1903 (fmask pH1903) (cmask pH1903) (hmask pH1903) 1554 349 (true, H1903_cp2.1, H1903_cp2.2)) ∧ ptTest pH1903 (runFrom pH1903 (fmask pH1903) (cmask pH1903) (hmask pH1903) 1554 349 (true, H1903_cp2.1, H1903_cp2.2)) 1903 952 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1903_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1903_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1903_fin) true) H1903_seg1) H1903_seg2) (by decide) rfl H1903_fin ptTest_fst
noncomputable def I1903_cp1 : Nat × Nat := t7val% (fastRun pI1903 1 1098 (init pI1903) (init pI1903))
theorem I1903_seg1 : segOK pI1903 1 1098 (init pI1903) (init pI1903) I1903_cp1.1 I1903_cp1.2 = true := by
  decide +kernel
noncomputable def I1903_cp2 : Nat × Nat := t7val% (fastRun pI1903 1 1553 (init pI1903) (init pI1903))
theorem I1903_seg2 : segOK pI1903 1099 455 I1903_cp1.1 I1903_cp1.2 I1903_cp2.1 I1903_cp2.2 = true := by
  decide +kernel
theorem I1903_fin : (prmOK pI1903 1903 && intTest pI1903 (runFrom pI1903 (fmask pI1903) (cmask pI1903) (hmask pI1903) 1554 349 (true, I1903_cp2.1, I1903_cp2.2)) 1903 22 false) = true := by
  decide +kernel
theorem I1903_ok : RunOK pI1903 1903 (runFrom pI1903 (fmask pI1903) (cmask pI1903) (hmask pI1903) 1554 349 (true, I1903_cp2.1, I1903_cp2.2)) ∧ intTest pI1903 (runFrom pI1903 (fmask pI1903) (cmask pI1903) (hmask pI1903) 1554 349 (true, I1903_cp2.1, I1903_cp2.2)) 1903 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1903_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1903_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1903_fin) true) I1903_seg1) I1903_seg2) (by decide) rfl I1903_fin intTest_fst
theorem link1903 : linkOK pL1903 pH1903 pI1903 = true := by decide +kernel
theorem cvx1903 : ConvexBetweenHumps 1903 :=
  cvx_of L1903_ok H1903_ok I1903_ok link1903 (by decide)

/-! ### `N = 1904` -/

def pL1904 : Prm := ⟨80, 37, 40, 1906, 11, 18446744073709551616, 102391439140098631, 102391439140098631⟩
def pH1904 : Prm := ⟨80, 37, 40, 1906, 11, 18446744073709551616, 102392538651726407, 102392538651726407⟩
def pI1904 : Prm := ⟨68, 34, 31, 1906, 11, 18446744073709551616, 102391439140098631, 102392538651726407⟩
noncomputable def L1904_cp1 : Nat × Nat := t7val% (fastRun pL1904 1 1098 (init pL1904) (init pL1904))
theorem L1904_seg1 : segOK pL1904 1 1098 (init pL1904) (init pL1904) L1904_cp1.1 L1904_cp1.2 = true := by
  decide +kernel
noncomputable def L1904_cp2 : Nat × Nat := t7val% (fastRun pL1904 1 1554 (init pL1904) (init pL1904))
theorem L1904_seg2 : segOK pL1904 1099 456 L1904_cp1.1 L1904_cp1.2 L1904_cp2.1 L1904_cp2.2 = true := by
  decide +kernel
theorem L1904_fin : (prmOK pL1904 1904 && ptTest pL1904 (runFrom pL1904 (fmask pL1904) (cmask pL1904) (hmask pL1904) 1555 349 (true, L1904_cp2.1, L1904_cp2.2)) 1904 952 false) = true := by
  decide +kernel
theorem L1904_ok : RunOK pL1904 1904 (runFrom pL1904 (fmask pL1904) (cmask pL1904) (hmask pL1904) 1555 349 (true, L1904_cp2.1, L1904_cp2.2)) ∧ ptTest pL1904 (runFrom pL1904 (fmask pL1904) (cmask pL1904) (hmask pL1904) 1555 349 (true, L1904_cp2.1, L1904_cp2.2)) 1904 952 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1904_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1904_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1904_fin) true) L1904_seg1) L1904_seg2) (by decide) rfl L1904_fin ptTest_fst
noncomputable def H1904_cp1 : Nat × Nat := t7val% (fastRun pH1904 1 1098 (init pH1904) (init pH1904))
theorem H1904_seg1 : segOK pH1904 1 1098 (init pH1904) (init pH1904) H1904_cp1.1 H1904_cp1.2 = true := by
  decide +kernel
noncomputable def H1904_cp2 : Nat × Nat := t7val% (fastRun pH1904 1 1554 (init pH1904) (init pH1904))
theorem H1904_seg2 : segOK pH1904 1099 456 H1904_cp1.1 H1904_cp1.2 H1904_cp2.1 H1904_cp2.2 = true := by
  decide +kernel
theorem H1904_fin : (prmOK pH1904 1904 && ptTest pH1904 (runFrom pH1904 (fmask pH1904) (cmask pH1904) (hmask pH1904) 1555 349 (true, H1904_cp2.1, H1904_cp2.2)) 1904 952 true) = true := by
  decide +kernel
theorem H1904_ok : RunOK pH1904 1904 (runFrom pH1904 (fmask pH1904) (cmask pH1904) (hmask pH1904) 1555 349 (true, H1904_cp2.1, H1904_cp2.2)) ∧ ptTest pH1904 (runFrom pH1904 (fmask pH1904) (cmask pH1904) (hmask pH1904) 1555 349 (true, H1904_cp2.1, H1904_cp2.2)) 1904 952 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1904_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1904_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1904_fin) true) H1904_seg1) H1904_seg2) (by decide) rfl H1904_fin ptTest_fst
noncomputable def I1904_cp1 : Nat × Nat := t7val% (fastRun pI1904 1 1098 (init pI1904) (init pI1904))
theorem I1904_seg1 : segOK pI1904 1 1098 (init pI1904) (init pI1904) I1904_cp1.1 I1904_cp1.2 = true := by
  decide +kernel
noncomputable def I1904_cp2 : Nat × Nat := t7val% (fastRun pI1904 1 1554 (init pI1904) (init pI1904))
theorem I1904_seg2 : segOK pI1904 1099 456 I1904_cp1.1 I1904_cp1.2 I1904_cp2.1 I1904_cp2.2 = true := by
  decide +kernel
theorem I1904_fin : (prmOK pI1904 1904 && intTest pI1904 (runFrom pI1904 (fmask pI1904) (cmask pI1904) (hmask pI1904) 1555 349 (true, I1904_cp2.1, I1904_cp2.2)) 1904 22 true) = true := by
  decide +kernel
theorem I1904_ok : RunOK pI1904 1904 (runFrom pI1904 (fmask pI1904) (cmask pI1904) (hmask pI1904) 1555 349 (true, I1904_cp2.1, I1904_cp2.2)) ∧ intTest pI1904 (runFrom pI1904 (fmask pI1904) (cmask pI1904) (hmask pI1904) 1555 349 (true, I1904_cp2.1, I1904_cp2.2)) 1904 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1904_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1904_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1904_fin) true) I1904_seg1) I1904_seg2) (by decide) rfl I1904_fin intTest_fst
theorem link1904 : linkOK pL1904 pH1904 pI1904 = true := by decide +kernel
theorem cvx1904 : ConvexBetweenHumps 1904 :=
  cvx_of L1904_ok H1904_ok I1904_ok link1904 (by decide)
theorem cenlink1904 : cenLinkOK pI1904 1904 = true := by decide +kernel
theorem cen1904 : CenterUniqueMin 1904 ∧ DipHyp 1904 ∧ OnePointHyps 1904 :=
  cen_of L1904_ok H1904_ok I1904_ok link1904 cenlink1904

/-! ### `N = 1905` -/

def pL1905 : Prm := ⟨80, 37, 40, 1907, 11, 18446744073709551616, 102347265894872413, 102347265894872413⟩
def pH1905 : Prm := ⟨80, 37, 40, 1907, 11, 18446744073709551616, 102348365406500189, 102348365406500189⟩
def pI1905 : Prm := ⟨68, 34, 31, 1907, 11, 18446744073709551616, 102347265894872413, 102348365406500189⟩
noncomputable def L1905_cp1 : Nat × Nat := t7val% (fastRun pL1905 1 1099 (init pL1905) (init pL1905))
theorem L1905_seg1 : segOK pL1905 1 1099 (init pL1905) (init pL1905) L1905_cp1.1 L1905_cp1.2 = true := by
  decide +kernel
noncomputable def L1905_cp2 : Nat × Nat := t7val% (fastRun pL1905 1 1554 (init pL1905) (init pL1905))
theorem L1905_seg2 : segOK pL1905 1100 455 L1905_cp1.1 L1905_cp1.2 L1905_cp2.1 L1905_cp2.2 = true := by
  decide +kernel
theorem L1905_fin : (prmOK pL1905 1905 && ptTest pL1905 (runFrom pL1905 (fmask pL1905) (cmask pL1905) (hmask pL1905) 1555 350 (true, L1905_cp2.1, L1905_cp2.2)) 1905 953 false) = true := by
  decide +kernel
theorem L1905_ok : RunOK pL1905 1905 (runFrom pL1905 (fmask pL1905) (cmask pL1905) (hmask pL1905) 1555 350 (true, L1905_cp2.1, L1905_cp2.2)) ∧ ptTest pL1905 (runFrom pL1905 (fmask pL1905) (cmask pL1905) (hmask pL1905) 1555 350 (true, L1905_cp2.1, L1905_cp2.2)) 1905 953 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1905_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1905_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1905_fin) true) L1905_seg1) L1905_seg2) (by decide) rfl L1905_fin ptTest_fst
noncomputable def H1905_cp1 : Nat × Nat := t7val% (fastRun pH1905 1 1099 (init pH1905) (init pH1905))
theorem H1905_seg1 : segOK pH1905 1 1099 (init pH1905) (init pH1905) H1905_cp1.1 H1905_cp1.2 = true := by
  decide +kernel
noncomputable def H1905_cp2 : Nat × Nat := t7val% (fastRun pH1905 1 1554 (init pH1905) (init pH1905))
theorem H1905_seg2 : segOK pH1905 1100 455 H1905_cp1.1 H1905_cp1.2 H1905_cp2.1 H1905_cp2.2 = true := by
  decide +kernel
theorem H1905_fin : (prmOK pH1905 1905 && ptTest pH1905 (runFrom pH1905 (fmask pH1905) (cmask pH1905) (hmask pH1905) 1555 350 (true, H1905_cp2.1, H1905_cp2.2)) 1905 953 true) = true := by
  decide +kernel
theorem H1905_ok : RunOK pH1905 1905 (runFrom pH1905 (fmask pH1905) (cmask pH1905) (hmask pH1905) 1555 350 (true, H1905_cp2.1, H1905_cp2.2)) ∧ ptTest pH1905 (runFrom pH1905 (fmask pH1905) (cmask pH1905) (hmask pH1905) 1555 350 (true, H1905_cp2.1, H1905_cp2.2)) 1905 953 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1905_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1905_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1905_fin) true) H1905_seg1) H1905_seg2) (by decide) rfl H1905_fin ptTest_fst
noncomputable def I1905_cp1 : Nat × Nat := t7val% (fastRun pI1905 1 1099 (init pI1905) (init pI1905))
theorem I1905_seg1 : segOK pI1905 1 1099 (init pI1905) (init pI1905) I1905_cp1.1 I1905_cp1.2 = true := by
  decide +kernel
noncomputable def I1905_cp2 : Nat × Nat := t7val% (fastRun pI1905 1 1554 (init pI1905) (init pI1905))
theorem I1905_seg2 : segOK pI1905 1100 455 I1905_cp1.1 I1905_cp1.2 I1905_cp2.1 I1905_cp2.2 = true := by
  decide +kernel
theorem I1905_fin : (prmOK pI1905 1905 && intTest pI1905 (runFrom pI1905 (fmask pI1905) (cmask pI1905) (hmask pI1905) 1555 350 (true, I1905_cp2.1, I1905_cp2.2)) 1905 22 false) = true := by
  decide +kernel
theorem I1905_ok : RunOK pI1905 1905 (runFrom pI1905 (fmask pI1905) (cmask pI1905) (hmask pI1905) 1555 350 (true, I1905_cp2.1, I1905_cp2.2)) ∧ intTest pI1905 (runFrom pI1905 (fmask pI1905) (cmask pI1905) (hmask pI1905) 1555 350 (true, I1905_cp2.1, I1905_cp2.2)) 1905 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1905_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1905_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1905_fin) true) I1905_seg1) I1905_seg2) (by decide) rfl I1905_fin intTest_fst
theorem link1905 : linkOK pL1905 pH1905 pI1905 = true := by decide +kernel
theorem cvx1905 : ConvexBetweenHumps 1905 :=
  cvx_of L1905_ok H1905_ok I1905_ok link1905 (by decide)

/-! ### `N = 1906` -/

def pL1906 : Prm := ⟨80, 37, 40, 1908, 11, 18446744073709551616, 102303150152500905, 102303150152500905⟩
def pH1906 : Prm := ⟨80, 37, 40, 1908, 11, 18446744073709551616, 102304249664128681, 102304249664128681⟩
def pI1906 : Prm := ⟨68, 34, 31, 1908, 11, 18446744073709551616, 102303150152500905, 102304249664128681⟩
noncomputable def L1906_cp1 : Nat × Nat := t7val% (fastRun pL1906 1 1099 (init pL1906) (init pL1906))
theorem L1906_seg1 : segOK pL1906 1 1099 (init pL1906) (init pL1906) L1906_cp1.1 L1906_cp1.2 = true := by
  decide +kernel
noncomputable def L1906_cp2 : Nat × Nat := t7val% (fastRun pL1906 1 1555 (init pL1906) (init pL1906))
theorem L1906_seg2 : segOK pL1906 1100 456 L1906_cp1.1 L1906_cp1.2 L1906_cp2.1 L1906_cp2.2 = true := by
  decide +kernel
theorem L1906_fin : (prmOK pL1906 1906 && ptTest pL1906 (runFrom pL1906 (fmask pL1906) (cmask pL1906) (hmask pL1906) 1556 350 (true, L1906_cp2.1, L1906_cp2.2)) 1906 953 false) = true := by
  decide +kernel
theorem L1906_ok : RunOK pL1906 1906 (runFrom pL1906 (fmask pL1906) (cmask pL1906) (hmask pL1906) 1556 350 (true, L1906_cp2.1, L1906_cp2.2)) ∧ ptTest pL1906 (runFrom pL1906 (fmask pL1906) (cmask pL1906) (hmask pL1906) 1556 350 (true, L1906_cp2.1, L1906_cp2.2)) 1906 953 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1906_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1906_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1906_fin) true) L1906_seg1) L1906_seg2) (by decide) rfl L1906_fin ptTest_fst
noncomputable def H1906_cp1 : Nat × Nat := t7val% (fastRun pH1906 1 1099 (init pH1906) (init pH1906))
theorem H1906_seg1 : segOK pH1906 1 1099 (init pH1906) (init pH1906) H1906_cp1.1 H1906_cp1.2 = true := by
  decide +kernel
noncomputable def H1906_cp2 : Nat × Nat := t7val% (fastRun pH1906 1 1555 (init pH1906) (init pH1906))
theorem H1906_seg2 : segOK pH1906 1100 456 H1906_cp1.1 H1906_cp1.2 H1906_cp2.1 H1906_cp2.2 = true := by
  decide +kernel
theorem H1906_fin : (prmOK pH1906 1906 && ptTest pH1906 (runFrom pH1906 (fmask pH1906) (cmask pH1906) (hmask pH1906) 1556 350 (true, H1906_cp2.1, H1906_cp2.2)) 1906 953 true) = true := by
  decide +kernel
theorem H1906_ok : RunOK pH1906 1906 (runFrom pH1906 (fmask pH1906) (cmask pH1906) (hmask pH1906) 1556 350 (true, H1906_cp2.1, H1906_cp2.2)) ∧ ptTest pH1906 (runFrom pH1906 (fmask pH1906) (cmask pH1906) (hmask pH1906) 1556 350 (true, H1906_cp2.1, H1906_cp2.2)) 1906 953 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1906_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1906_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1906_fin) true) H1906_seg1) H1906_seg2) (by decide) rfl H1906_fin ptTest_fst
noncomputable def I1906_cp1 : Nat × Nat := t7val% (fastRun pI1906 1 1099 (init pI1906) (init pI1906))
theorem I1906_seg1 : segOK pI1906 1 1099 (init pI1906) (init pI1906) I1906_cp1.1 I1906_cp1.2 = true := by
  decide +kernel
noncomputable def I1906_cp2 : Nat × Nat := t7val% (fastRun pI1906 1 1555 (init pI1906) (init pI1906))
theorem I1906_seg2 : segOK pI1906 1100 456 I1906_cp1.1 I1906_cp1.2 I1906_cp2.1 I1906_cp2.2 = true := by
  decide +kernel
theorem I1906_fin : (prmOK pI1906 1906 && intTest pI1906 (runFrom pI1906 (fmask pI1906) (cmask pI1906) (hmask pI1906) 1556 350 (true, I1906_cp2.1, I1906_cp2.2)) 1906 22 true) = true := by
  decide +kernel
theorem I1906_ok : RunOK pI1906 1906 (runFrom pI1906 (fmask pI1906) (cmask pI1906) (hmask pI1906) 1556 350 (true, I1906_cp2.1, I1906_cp2.2)) ∧ intTest pI1906 (runFrom pI1906 (fmask pI1906) (cmask pI1906) (hmask pI1906) 1556 350 (true, I1906_cp2.1, I1906_cp2.2)) 1906 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1906_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1906_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1906_fin) true) I1906_seg1) I1906_seg2) (by decide) rfl I1906_fin intTest_fst
theorem link1906 : linkOK pL1906 pH1906 pI1906 = true := by decide +kernel
theorem cvx1906 : ConvexBetweenHumps 1906 :=
  cvx_of L1906_ok H1906_ok I1906_ok link1906 (by decide)
theorem cenlink1906 : cenLinkOK pI1906 1906 = true := by decide +kernel
theorem cen1906 : CenterUniqueMin 1906 ∧ DipHyp 1906 ∧ OnePointHyps 1906 :=
  cen_of L1906_ok H1906_ok I1906_ok link1906 cenlink1906

/-! ### `N = 1907` -/

def pL1907 : Prm := ⟨80, 37, 40, 1909, 11, 18446744073709551616, 102259059492425568, 102259059492425568⟩
def pH1907 : Prm := ⟨80, 37, 40, 1909, 11, 18446744073709551616, 102260159004053344, 102260159004053344⟩
def pI1907 : Prm := ⟨68, 34, 31, 1909, 11, 18446744073709551616, 102259059492425568, 102260159004053344⟩
noncomputable def L1907_cp1 : Nat × Nat := t7val% (fastRun pL1907 1 1100 (init pL1907) (init pL1907))
theorem L1907_seg1 : segOK pL1907 1 1100 (init pL1907) (init pL1907) L1907_cp1.1 L1907_cp1.2 = true := by
  decide +kernel
noncomputable def L1907_cp2 : Nat × Nat := t7val% (fastRun pL1907 1 1556 (init pL1907) (init pL1907))
theorem L1907_seg2 : segOK pL1907 1101 456 L1907_cp1.1 L1907_cp1.2 L1907_cp2.1 L1907_cp2.2 = true := by
  decide +kernel
theorem L1907_fin : (prmOK pL1907 1907 && ptTest pL1907 (runFrom pL1907 (fmask pL1907) (cmask pL1907) (hmask pL1907) 1557 350 (true, L1907_cp2.1, L1907_cp2.2)) 1907 954 false) = true := by
  decide +kernel
theorem L1907_ok : RunOK pL1907 1907 (runFrom pL1907 (fmask pL1907) (cmask pL1907) (hmask pL1907) 1557 350 (true, L1907_cp2.1, L1907_cp2.2)) ∧ ptTest pL1907 (runFrom pL1907 (fmask pL1907) (cmask pL1907) (hmask pL1907) 1557 350 (true, L1907_cp2.1, L1907_cp2.2)) 1907 954 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1907_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1907_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1907_fin) true) L1907_seg1) L1907_seg2) (by decide) rfl L1907_fin ptTest_fst
noncomputable def H1907_cp1 : Nat × Nat := t7val% (fastRun pH1907 1 1100 (init pH1907) (init pH1907))
theorem H1907_seg1 : segOK pH1907 1 1100 (init pH1907) (init pH1907) H1907_cp1.1 H1907_cp1.2 = true := by
  decide +kernel
noncomputable def H1907_cp2 : Nat × Nat := t7val% (fastRun pH1907 1 1556 (init pH1907) (init pH1907))
theorem H1907_seg2 : segOK pH1907 1101 456 H1907_cp1.1 H1907_cp1.2 H1907_cp2.1 H1907_cp2.2 = true := by
  decide +kernel
theorem H1907_fin : (prmOK pH1907 1907 && ptTest pH1907 (runFrom pH1907 (fmask pH1907) (cmask pH1907) (hmask pH1907) 1557 350 (true, H1907_cp2.1, H1907_cp2.2)) 1907 954 true) = true := by
  decide +kernel
theorem H1907_ok : RunOK pH1907 1907 (runFrom pH1907 (fmask pH1907) (cmask pH1907) (hmask pH1907) 1557 350 (true, H1907_cp2.1, H1907_cp2.2)) ∧ ptTest pH1907 (runFrom pH1907 (fmask pH1907) (cmask pH1907) (hmask pH1907) 1557 350 (true, H1907_cp2.1, H1907_cp2.2)) 1907 954 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1907_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1907_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1907_fin) true) H1907_seg1) H1907_seg2) (by decide) rfl H1907_fin ptTest_fst
noncomputable def I1907_cp1 : Nat × Nat := t7val% (fastRun pI1907 1 1100 (init pI1907) (init pI1907))
theorem I1907_seg1 : segOK pI1907 1 1100 (init pI1907) (init pI1907) I1907_cp1.1 I1907_cp1.2 = true := by
  decide +kernel
noncomputable def I1907_cp2 : Nat × Nat := t7val% (fastRun pI1907 1 1556 (init pI1907) (init pI1907))
theorem I1907_seg2 : segOK pI1907 1101 456 I1907_cp1.1 I1907_cp1.2 I1907_cp2.1 I1907_cp2.2 = true := by
  decide +kernel
theorem I1907_fin : (prmOK pI1907 1907 && intTest pI1907 (runFrom pI1907 (fmask pI1907) (cmask pI1907) (hmask pI1907) 1557 350 (true, I1907_cp2.1, I1907_cp2.2)) 1907 22 false) = true := by
  decide +kernel
theorem I1907_ok : RunOK pI1907 1907 (runFrom pI1907 (fmask pI1907) (cmask pI1907) (hmask pI1907) 1557 350 (true, I1907_cp2.1, I1907_cp2.2)) ∧ intTest pI1907 (runFrom pI1907 (fmask pI1907) (cmask pI1907) (hmask pI1907) 1557 350 (true, I1907_cp2.1, I1907_cp2.2)) 1907 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1907_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1907_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1907_fin) true) I1907_seg1) I1907_seg2) (by decide) rfl I1907_fin intTest_fst
theorem link1907 : linkOK pL1907 pH1907 pI1907 = true := by decide +kernel
theorem cvx1907 : ConvexBetweenHumps 1907 :=
  cvx_of L1907_ok H1907_ok I1907_ok link1907 (by decide)

/-! ### `N = 1908` -/

def pL1908 : Prm := ⟨80, 37, 40, 1910, 11, 18446744073709551616, 102215026164240517, 102215026164240517⟩
def pH1908 : Prm := ⟨80, 37, 40, 1910, 11, 18446744073709551616, 102216125675868293, 102216125675868293⟩
def pI1908 : Prm := ⟨68, 34, 31, 1910, 11, 18446744073709551616, 102215026164240517, 102216125675868293⟩
noncomputable def L1908_cp1 : Nat × Nat := t7val% (fastRun pL1908 1 1101 (init pL1908) (init pL1908))
theorem L1908_seg1 : segOK pL1908 1 1101 (init pL1908) (init pL1908) L1908_cp1.1 L1908_cp1.2 = true := by
  decide +kernel
noncomputable def L1908_cp2 : Nat × Nat := t7val% (fastRun pL1908 1 1557 (init pL1908) (init pL1908))
theorem L1908_seg2 : segOK pL1908 1102 456 L1908_cp1.1 L1908_cp1.2 L1908_cp2.1 L1908_cp2.2 = true := by
  decide +kernel
theorem L1908_fin : (prmOK pL1908 1908 && ptTest pL1908 (runFrom pL1908 (fmask pL1908) (cmask pL1908) (hmask pL1908) 1558 350 (true, L1908_cp2.1, L1908_cp2.2)) 1908 954 false) = true := by
  decide +kernel
theorem L1908_ok : RunOK pL1908 1908 (runFrom pL1908 (fmask pL1908) (cmask pL1908) (hmask pL1908) 1558 350 (true, L1908_cp2.1, L1908_cp2.2)) ∧ ptTest pL1908 (runFrom pL1908 (fmask pL1908) (cmask pL1908) (hmask pL1908) 1558 350 (true, L1908_cp2.1, L1908_cp2.2)) 1908 954 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1908_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1908_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1908_fin) true) L1908_seg1) L1908_seg2) (by decide) rfl L1908_fin ptTest_fst
noncomputable def H1908_cp1 : Nat × Nat := t7val% (fastRun pH1908 1 1101 (init pH1908) (init pH1908))
theorem H1908_seg1 : segOK pH1908 1 1101 (init pH1908) (init pH1908) H1908_cp1.1 H1908_cp1.2 = true := by
  decide +kernel
noncomputable def H1908_cp2 : Nat × Nat := t7val% (fastRun pH1908 1 1557 (init pH1908) (init pH1908))
theorem H1908_seg2 : segOK pH1908 1102 456 H1908_cp1.1 H1908_cp1.2 H1908_cp2.1 H1908_cp2.2 = true := by
  decide +kernel
theorem H1908_fin : (prmOK pH1908 1908 && ptTest pH1908 (runFrom pH1908 (fmask pH1908) (cmask pH1908) (hmask pH1908) 1558 350 (true, H1908_cp2.1, H1908_cp2.2)) 1908 954 true) = true := by
  decide +kernel
theorem H1908_ok : RunOK pH1908 1908 (runFrom pH1908 (fmask pH1908) (cmask pH1908) (hmask pH1908) 1558 350 (true, H1908_cp2.1, H1908_cp2.2)) ∧ ptTest pH1908 (runFrom pH1908 (fmask pH1908) (cmask pH1908) (hmask pH1908) 1558 350 (true, H1908_cp2.1, H1908_cp2.2)) 1908 954 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1908_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1908_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1908_fin) true) H1908_seg1) H1908_seg2) (by decide) rfl H1908_fin ptTest_fst
noncomputable def I1908_cp1 : Nat × Nat := t7val% (fastRun pI1908 1 1101 (init pI1908) (init pI1908))
theorem I1908_seg1 : segOK pI1908 1 1101 (init pI1908) (init pI1908) I1908_cp1.1 I1908_cp1.2 = true := by
  decide +kernel
noncomputable def I1908_cp2 : Nat × Nat := t7val% (fastRun pI1908 1 1557 (init pI1908) (init pI1908))
theorem I1908_seg2 : segOK pI1908 1102 456 I1908_cp1.1 I1908_cp1.2 I1908_cp2.1 I1908_cp2.2 = true := by
  decide +kernel
theorem I1908_fin : (prmOK pI1908 1908 && intTest pI1908 (runFrom pI1908 (fmask pI1908) (cmask pI1908) (hmask pI1908) 1558 350 (true, I1908_cp2.1, I1908_cp2.2)) 1908 22 true) = true := by
  decide +kernel
theorem I1908_ok : RunOK pI1908 1908 (runFrom pI1908 (fmask pI1908) (cmask pI1908) (hmask pI1908) 1558 350 (true, I1908_cp2.1, I1908_cp2.2)) ∧ intTest pI1908 (runFrom pI1908 (fmask pI1908) (cmask pI1908) (hmask pI1908) 1558 350 (true, I1908_cp2.1, I1908_cp2.2)) 1908 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1908_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1908_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1908_fin) true) I1908_seg1) I1908_seg2) (by decide) rfl I1908_fin intTest_fst
theorem link1908 : linkOK pL1908 pH1908 pI1908 = true := by decide +kernel
theorem cvx1908 : ConvexBetweenHumps 1908 :=
  cvx_of L1908_ok H1908_ok I1908_ok link1908 (by decide)
theorem cenlink1908 : cenLinkOK pI1908 1908 = true := by decide +kernel
theorem cen1908 : CenterUniqueMin 1908 ∧ DipHyp 1908 ∧ OnePointHyps 1908 :=
  cen_of L1908_ok H1908_ok I1908_ok link1908 cenlink1908

/-! ### The range -/

theorem cvx_1898_1908 {N : ℕ} (h1 : 1898 ≤ N) (h2 : N ≤ 1908) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1902
  · by_cases h4 : N ≤ 1899
    · by_cases h6 : N ≤ 1898
      · obtain rfl : N = 1898 := by omega
        exact cvx1898
      · obtain rfl : N = 1899 := by omega
        exact cvx1899
    · by_cases h6 : N ≤ 1900
      · obtain rfl : N = 1900 := by omega
        exact cvx1900
      · by_cases h8 : N ≤ 1901
        · obtain rfl : N = 1901 := by omega
          exact cvx1901
        · obtain rfl : N = 1902 := by omega
          exact cvx1902
  · by_cases h4 : N ≤ 1905
    · by_cases h6 : N ≤ 1903
      · obtain rfl : N = 1903 := by omega
        exact cvx1903
      · by_cases h8 : N ≤ 1904
        · obtain rfl : N = 1904 := by omega
          exact cvx1904
        · obtain rfl : N = 1905 := by omega
          exact cvx1905
    · by_cases h6 : N ≤ 1906
      · obtain rfl : N = 1906 := by omega
        exact cvx1906
      · by_cases h8 : N ≤ 1907
        · obtain rfl : N = 1907 := by omega
          exact cvx1907
        · obtain rfl : N = 1908 := by omega
          exact cvx1908

theorem cen_1898_1908 {N : ℕ} (h1 : 1898 ≤ N) (h2 : N ≤ 1908) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1902
  · by_cases h4 : N ≤ 1898
    · obtain rfl : N = 1898 := by omega
      exact cen1898
    · by_cases h6 : N ≤ 1900
      · obtain rfl : N = 1900 := by omega
        exact cen1900
      · obtain rfl : N = 1902 := by omega
        exact cen1902
  · by_cases h4 : N ≤ 1904
    · obtain rfl : N = 1904 := by omega
      exact cen1904
    · by_cases h6 : N ≤ 1906
      · obtain rfl : N = 1906 := by omega
        exact cen1906
      · obtain rfl : N = 1908 := by omega
        exact cen1908

end Kagey131.PaperD.T7
