import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1653, …, 1666` (generated)

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

/-! ### `N = 1653` -/

def pL1653 : Prm := ⟨80, 37, 40, 1655, 11, 18446744073709551616, 114965225396925435, 114965225396925435⟩
def pH1653 : Prm := ⟨80, 37, 40, 1655, 11, 18446744073709551616, 114966324908553211, 114966324908553211⟩
def pI1653 : Prm := ⟨67, 33, 31, 1655, 11, 18446744073709551616, 114965225396925435, 114966324908553211⟩
noncomputable def L1653_cp1 : Nat × Nat := t7val% (fastRun pL1653 1 953 (init pL1653) (init pL1653))
theorem L1653_seg1 : segOK pL1653 1 953 (init pL1653) (init pL1653) L1653_cp1.1 L1653_cp1.2 = true := by
  decide +kernel
noncomputable def L1653_cp2 : Nat × Nat := t7val% (fastRun pL1653 1 1349 (init pL1653) (init pL1653))
theorem L1653_seg2 : segOK pL1653 954 396 L1653_cp1.1 L1653_cp1.2 L1653_cp2.1 L1653_cp2.2 = true := by
  decide +kernel
theorem L1653_fin : (prmOK pL1653 1653 && ptTest pL1653 (runFrom pL1653 (fmask pL1653) (cmask pL1653) (hmask pL1653) 1350 303 (true, L1653_cp2.1, L1653_cp2.2)) 1653 827 false) = true := by
  decide +kernel
theorem L1653_ok : RunOK pL1653 1653 (runFrom pL1653 (fmask pL1653) (cmask pL1653) (hmask pL1653) 1350 303 (true, L1653_cp2.1, L1653_cp2.2)) ∧ ptTest pL1653 (runFrom pL1653 (fmask pL1653) (cmask pL1653) (hmask pL1653) 1350 303 (true, L1653_cp2.1, L1653_cp2.2)) 1653 827 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1653_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1653_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1653_fin) true) L1653_seg1) L1653_seg2) (by decide) rfl L1653_fin ptTest_fst
noncomputable def H1653_cp1 : Nat × Nat := t7val% (fastRun pH1653 1 953 (init pH1653) (init pH1653))
theorem H1653_seg1 : segOK pH1653 1 953 (init pH1653) (init pH1653) H1653_cp1.1 H1653_cp1.2 = true := by
  decide +kernel
noncomputable def H1653_cp2 : Nat × Nat := t7val% (fastRun pH1653 1 1349 (init pH1653) (init pH1653))
theorem H1653_seg2 : segOK pH1653 954 396 H1653_cp1.1 H1653_cp1.2 H1653_cp2.1 H1653_cp2.2 = true := by
  decide +kernel
theorem H1653_fin : (prmOK pH1653 1653 && ptTest pH1653 (runFrom pH1653 (fmask pH1653) (cmask pH1653) (hmask pH1653) 1350 303 (true, H1653_cp2.1, H1653_cp2.2)) 1653 827 true) = true := by
  decide +kernel
theorem H1653_ok : RunOK pH1653 1653 (runFrom pH1653 (fmask pH1653) (cmask pH1653) (hmask pH1653) 1350 303 (true, H1653_cp2.1, H1653_cp2.2)) ∧ ptTest pH1653 (runFrom pH1653 (fmask pH1653) (cmask pH1653) (hmask pH1653) 1350 303 (true, H1653_cp2.1, H1653_cp2.2)) 1653 827 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1653_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1653_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1653_fin) true) H1653_seg1) H1653_seg2) (by decide) rfl H1653_fin ptTest_fst
noncomputable def I1653_cp1 : Nat × Nat := t7val% (fastRun pI1653 1 1168 (init pI1653) (init pI1653))
theorem I1653_seg1 : segOK pI1653 1 1168 (init pI1653) (init pI1653) I1653_cp1.1 I1653_cp1.2 = true := by
  decide +kernel
theorem I1653_fin : (prmOK pI1653 1653 && intTest pI1653 (runFrom pI1653 (fmask pI1653) (cmask pI1653) (hmask pI1653) 1169 484 (true, I1653_cp1.1, I1653_cp1.2)) 1653 21 false) = true := by
  decide +kernel
theorem I1653_ok : RunOK pI1653 1653 (runFrom pI1653 (fmask pI1653) (cmask pI1653) (hmask pI1653) 1169 484 (true, I1653_cp1.1, I1653_cp1.2)) ∧ intTest pI1653 (runFrom pI1653 (fmask pI1653) (cmask pI1653) (hmask pI1653) 1169 484 (true, I1653_cp1.1, I1653_cp1.2)) 1653 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1653_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1653_fin) true) I1653_seg1) (by decide) rfl I1653_fin intTest_fst
theorem link1653 : linkOK pL1653 pH1653 pI1653 = true := by decide +kernel
theorem cvx1653 : ConvexBetweenHumps 1653 :=
  cvx_of L1653_ok H1653_ok I1653_ok link1653 (by decide)

/-! ### `N = 1654` -/

def pL1654 : Prm := ⟨80, 37, 40, 1656, 11, 18446744073709551616, 114908446456998691, 114908446456998691⟩
def pH1654 : Prm := ⟨80, 37, 40, 1656, 11, 18446744073709551616, 114909545968626467, 114909545968626467⟩
def pI1654 : Prm := ⟨67, 33, 31, 1656, 11, 18446744073709551616, 114908446456998691, 114909545968626467⟩
noncomputable def L1654_cp1 : Nat × Nat := t7val% (fastRun pL1654 1 954 (init pL1654) (init pL1654))
theorem L1654_seg1 : segOK pL1654 1 954 (init pL1654) (init pL1654) L1654_cp1.1 L1654_cp1.2 = true := by
  decide +kernel
noncomputable def L1654_cp2 : Nat × Nat := t7val% (fastRun pL1654 1 1349 (init pL1654) (init pL1654))
theorem L1654_seg2 : segOK pL1654 955 395 L1654_cp1.1 L1654_cp1.2 L1654_cp2.1 L1654_cp2.2 = true := by
  decide +kernel
theorem L1654_fin : (prmOK pL1654 1654 && ptTest pL1654 (runFrom pL1654 (fmask pL1654) (cmask pL1654) (hmask pL1654) 1350 304 (true, L1654_cp2.1, L1654_cp2.2)) 1654 827 false) = true := by
  decide +kernel
theorem L1654_ok : RunOK pL1654 1654 (runFrom pL1654 (fmask pL1654) (cmask pL1654) (hmask pL1654) 1350 304 (true, L1654_cp2.1, L1654_cp2.2)) ∧ ptTest pL1654 (runFrom pL1654 (fmask pL1654) (cmask pL1654) (hmask pL1654) 1350 304 (true, L1654_cp2.1, L1654_cp2.2)) 1654 827 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1654_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1654_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1654_fin) true) L1654_seg1) L1654_seg2) (by decide) rfl L1654_fin ptTest_fst
noncomputable def H1654_cp1 : Nat × Nat := t7val% (fastRun pH1654 1 954 (init pH1654) (init pH1654))
theorem H1654_seg1 : segOK pH1654 1 954 (init pH1654) (init pH1654) H1654_cp1.1 H1654_cp1.2 = true := by
  decide +kernel
noncomputable def H1654_cp2 : Nat × Nat := t7val% (fastRun pH1654 1 1349 (init pH1654) (init pH1654))
theorem H1654_seg2 : segOK pH1654 955 395 H1654_cp1.1 H1654_cp1.2 H1654_cp2.1 H1654_cp2.2 = true := by
  decide +kernel
theorem H1654_fin : (prmOK pH1654 1654 && ptTest pH1654 (runFrom pH1654 (fmask pH1654) (cmask pH1654) (hmask pH1654) 1350 304 (true, H1654_cp2.1, H1654_cp2.2)) 1654 827 true) = true := by
  decide +kernel
theorem H1654_ok : RunOK pH1654 1654 (runFrom pH1654 (fmask pH1654) (cmask pH1654) (hmask pH1654) 1350 304 (true, H1654_cp2.1, H1654_cp2.2)) ∧ ptTest pH1654 (runFrom pH1654 (fmask pH1654) (cmask pH1654) (hmask pH1654) 1350 304 (true, H1654_cp2.1, H1654_cp2.2)) 1654 827 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1654_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1654_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1654_fin) true) H1654_seg1) H1654_seg2) (by decide) rfl H1654_fin ptTest_fst
noncomputable def I1654_cp1 : Nat × Nat := t7val% (fastRun pI1654 1 1169 (init pI1654) (init pI1654))
theorem I1654_seg1 : segOK pI1654 1 1169 (init pI1654) (init pI1654) I1654_cp1.1 I1654_cp1.2 = true := by
  decide +kernel
theorem I1654_fin : (prmOK pI1654 1654 && intTest pI1654 (runFrom pI1654 (fmask pI1654) (cmask pI1654) (hmask pI1654) 1170 484 (true, I1654_cp1.1, I1654_cp1.2)) 1654 21 true) = true := by
  decide +kernel
theorem I1654_ok : RunOK pI1654 1654 (runFrom pI1654 (fmask pI1654) (cmask pI1654) (hmask pI1654) 1170 484 (true, I1654_cp1.1, I1654_cp1.2)) ∧ intTest pI1654 (runFrom pI1654 (fmask pI1654) (cmask pI1654) (hmask pI1654) 1170 484 (true, I1654_cp1.1, I1654_cp1.2)) 1654 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1654_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1654_fin) true) I1654_seg1) (by decide) rfl I1654_fin intTest_fst
theorem link1654 : linkOK pL1654 pH1654 pI1654 = true := by decide +kernel
theorem cvx1654 : ConvexBetweenHumps 1654 :=
  cvx_of L1654_ok H1654_ok I1654_ok link1654 (by decide)
theorem cenlink1654 : cenLinkOK pI1654 1654 = true := by decide +kernel
theorem cen1654 : CenterUniqueMin 1654 ∧ DipHyp 1654 ∧ OnePointHyps 1654 :=
  cen_of L1654_ok H1654_ok I1654_ok link1654 cenlink1654

/-! ### `N = 1655` -/

def pL1655 : Prm := ⟨80, 37, 40, 1657, 11, 18446744073709551616, 114851703555405933, 114851703555405933⟩
def pH1655 : Prm := ⟨80, 37, 40, 1657, 11, 18446744073709551616, 114852803067033709, 114852803067033709⟩
def pI1655 : Prm := ⟨67, 33, 31, 1657, 11, 18446744073709551616, 114851703555405933, 114852803067033709⟩
noncomputable def L1655_cp1 : Nat × Nat := t7val% (fastRun pL1655 1 955 (init pL1655) (init pL1655))
theorem L1655_seg1 : segOK pL1655 1 955 (init pL1655) (init pL1655) L1655_cp1.1 L1655_cp1.2 = true := by
  decide +kernel
noncomputable def L1655_cp2 : Nat × Nat := t7val% (fastRun pL1655 1 1350 (init pL1655) (init pL1655))
theorem L1655_seg2 : segOK pL1655 956 395 L1655_cp1.1 L1655_cp1.2 L1655_cp2.1 L1655_cp2.2 = true := by
  decide +kernel
theorem L1655_fin : (prmOK pL1655 1655 && ptTest pL1655 (runFrom pL1655 (fmask pL1655) (cmask pL1655) (hmask pL1655) 1351 304 (true, L1655_cp2.1, L1655_cp2.2)) 1655 828 false) = true := by
  decide +kernel
theorem L1655_ok : RunOK pL1655 1655 (runFrom pL1655 (fmask pL1655) (cmask pL1655) (hmask pL1655) 1351 304 (true, L1655_cp2.1, L1655_cp2.2)) ∧ ptTest pL1655 (runFrom pL1655 (fmask pL1655) (cmask pL1655) (hmask pL1655) 1351 304 (true, L1655_cp2.1, L1655_cp2.2)) 1655 828 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1655_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1655_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1655_fin) true) L1655_seg1) L1655_seg2) (by decide) rfl L1655_fin ptTest_fst
noncomputable def H1655_cp1 : Nat × Nat := t7val% (fastRun pH1655 1 955 (init pH1655) (init pH1655))
theorem H1655_seg1 : segOK pH1655 1 955 (init pH1655) (init pH1655) H1655_cp1.1 H1655_cp1.2 = true := by
  decide +kernel
noncomputable def H1655_cp2 : Nat × Nat := t7val% (fastRun pH1655 1 1350 (init pH1655) (init pH1655))
theorem H1655_seg2 : segOK pH1655 956 395 H1655_cp1.1 H1655_cp1.2 H1655_cp2.1 H1655_cp2.2 = true := by
  decide +kernel
theorem H1655_fin : (prmOK pH1655 1655 && ptTest pH1655 (runFrom pH1655 (fmask pH1655) (cmask pH1655) (hmask pH1655) 1351 304 (true, H1655_cp2.1, H1655_cp2.2)) 1655 828 true) = true := by
  decide +kernel
theorem H1655_ok : RunOK pH1655 1655 (runFrom pH1655 (fmask pH1655) (cmask pH1655) (hmask pH1655) 1351 304 (true, H1655_cp2.1, H1655_cp2.2)) ∧ ptTest pH1655 (runFrom pH1655 (fmask pH1655) (cmask pH1655) (hmask pH1655) 1351 304 (true, H1655_cp2.1, H1655_cp2.2)) 1655 828 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1655_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1655_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1655_fin) true) H1655_seg1) H1655_seg2) (by decide) rfl H1655_fin ptTest_fst
noncomputable def I1655_cp1 : Nat × Nat := t7val% (fastRun pI1655 1 1169 (init pI1655) (init pI1655))
theorem I1655_seg1 : segOK pI1655 1 1169 (init pI1655) (init pI1655) I1655_cp1.1 I1655_cp1.2 = true := by
  decide +kernel
theorem I1655_fin : (prmOK pI1655 1655 && intTest pI1655 (runFrom pI1655 (fmask pI1655) (cmask pI1655) (hmask pI1655) 1170 485 (true, I1655_cp1.1, I1655_cp1.2)) 1655 21 false) = true := by
  decide +kernel
theorem I1655_ok : RunOK pI1655 1655 (runFrom pI1655 (fmask pI1655) (cmask pI1655) (hmask pI1655) 1170 485 (true, I1655_cp1.1, I1655_cp1.2)) ∧ intTest pI1655 (runFrom pI1655 (fmask pI1655) (cmask pI1655) (hmask pI1655) 1170 485 (true, I1655_cp1.1, I1655_cp1.2)) 1655 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1655_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1655_fin) true) I1655_seg1) (by decide) rfl I1655_fin intTest_fst
theorem link1655 : linkOK pL1655 pH1655 pI1655 = true := by decide +kernel
theorem cvx1655 : ConvexBetweenHumps 1655 :=
  cvx_of L1655_ok H1655_ok I1655_ok link1655 (by decide)

/-! ### `N = 1656` -/

def pL1656 : Prm := ⟨80, 37, 40, 1658, 11, 18446744073709551616, 114795046346465668, 114795046346465668⟩
def pH1656 : Prm := ⟨80, 37, 40, 1658, 11, 18446744073709551616, 114796145858093444, 114796145858093444⟩
def pI1656 : Prm := ⟨67, 33, 31, 1658, 11, 18446744073709551616, 114795046346465668, 114796145858093444⟩
noncomputable def L1656_cp1 : Nat × Nat := t7val% (fastRun pL1656 1 955 (init pL1656) (init pL1656))
theorem L1656_seg1 : segOK pL1656 1 955 (init pL1656) (init pL1656) L1656_cp1.1 L1656_cp1.2 = true := by
  decide +kernel
noncomputable def L1656_cp2 : Nat × Nat := t7val% (fastRun pL1656 1 1351 (init pL1656) (init pL1656))
theorem L1656_seg2 : segOK pL1656 956 396 L1656_cp1.1 L1656_cp1.2 L1656_cp2.1 L1656_cp2.2 = true := by
  decide +kernel
theorem L1656_fin : (prmOK pL1656 1656 && ptTest pL1656 (runFrom pL1656 (fmask pL1656) (cmask pL1656) (hmask pL1656) 1352 304 (true, L1656_cp2.1, L1656_cp2.2)) 1656 828 false) = true := by
  decide +kernel
theorem L1656_ok : RunOK pL1656 1656 (runFrom pL1656 (fmask pL1656) (cmask pL1656) (hmask pL1656) 1352 304 (true, L1656_cp2.1, L1656_cp2.2)) ∧ ptTest pL1656 (runFrom pL1656 (fmask pL1656) (cmask pL1656) (hmask pL1656) 1352 304 (true, L1656_cp2.1, L1656_cp2.2)) 1656 828 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1656_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1656_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1656_fin) true) L1656_seg1) L1656_seg2) (by decide) rfl L1656_fin ptTest_fst
noncomputable def H1656_cp1 : Nat × Nat := t7val% (fastRun pH1656 1 955 (init pH1656) (init pH1656))
theorem H1656_seg1 : segOK pH1656 1 955 (init pH1656) (init pH1656) H1656_cp1.1 H1656_cp1.2 = true := by
  decide +kernel
noncomputable def H1656_cp2 : Nat × Nat := t7val% (fastRun pH1656 1 1351 (init pH1656) (init pH1656))
theorem H1656_seg2 : segOK pH1656 956 396 H1656_cp1.1 H1656_cp1.2 H1656_cp2.1 H1656_cp2.2 = true := by
  decide +kernel
theorem H1656_fin : (prmOK pH1656 1656 && ptTest pH1656 (runFrom pH1656 (fmask pH1656) (cmask pH1656) (hmask pH1656) 1352 304 (true, H1656_cp2.1, H1656_cp2.2)) 1656 828 true) = true := by
  decide +kernel
theorem H1656_ok : RunOK pH1656 1656 (runFrom pH1656 (fmask pH1656) (cmask pH1656) (hmask pH1656) 1352 304 (true, H1656_cp2.1, H1656_cp2.2)) ∧ ptTest pH1656 (runFrom pH1656 (fmask pH1656) (cmask pH1656) (hmask pH1656) 1352 304 (true, H1656_cp2.1, H1656_cp2.2)) 1656 828 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1656_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1656_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1656_fin) true) H1656_seg1) H1656_seg2) (by decide) rfl H1656_fin ptTest_fst
noncomputable def I1656_cp1 : Nat × Nat := t7val% (fastRun pI1656 1 1170 (init pI1656) (init pI1656))
theorem I1656_seg1 : segOK pI1656 1 1170 (init pI1656) (init pI1656) I1656_cp1.1 I1656_cp1.2 = true := by
  decide +kernel
theorem I1656_fin : (prmOK pI1656 1656 && intTest pI1656 (runFrom pI1656 (fmask pI1656) (cmask pI1656) (hmask pI1656) 1171 485 (true, I1656_cp1.1, I1656_cp1.2)) 1656 21 true) = true := by
  decide +kernel
theorem I1656_ok : RunOK pI1656 1656 (runFrom pI1656 (fmask pI1656) (cmask pI1656) (hmask pI1656) 1171 485 (true, I1656_cp1.1, I1656_cp1.2)) ∧ intTest pI1656 (runFrom pI1656 (fmask pI1656) (cmask pI1656) (hmask pI1656) 1171 485 (true, I1656_cp1.1, I1656_cp1.2)) 1656 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1656_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1656_fin) true) I1656_seg1) (by decide) rfl I1656_fin intTest_fst
theorem link1656 : linkOK pL1656 pH1656 pI1656 = true := by decide +kernel
theorem cvx1656 : ConvexBetweenHumps 1656 :=
  cvx_of L1656_ok H1656_ok I1656_ok link1656 (by decide)
theorem cenlink1656 : cenLinkOK pI1656 1656 = true := by decide +kernel
theorem cen1656 : CenterUniqueMin 1656 ∧ DipHyp 1656 ∧ OnePointHyps 1656 :=
  cen_of L1656_ok H1656_ok I1656_ok link1656 cenlink1656

/-! ### `N = 1657` -/

def pL1657 : Prm := ⟨80, 37, 40, 1659, 11, 18446744073709551616, 114738425065400286, 114738425065400286⟩
def pH1657 : Prm := ⟨80, 37, 40, 1659, 11, 18446744073709551616, 114739524577028062, 114739524577028062⟩
def pI1657 : Prm := ⟨67, 33, 31, 1659, 11, 18446744073709551616, 114738425065400286, 114739524577028062⟩
noncomputable def L1657_cp1 : Nat × Nat := t7val% (fastRun pL1657 1 956 (init pL1657) (init pL1657))
theorem L1657_seg1 : segOK pL1657 1 956 (init pL1657) (init pL1657) L1657_cp1.1 L1657_cp1.2 = true := by
  decide +kernel
noncomputable def L1657_cp2 : Nat × Nat := t7val% (fastRun pL1657 1 1352 (init pL1657) (init pL1657))
theorem L1657_seg2 : segOK pL1657 957 396 L1657_cp1.1 L1657_cp1.2 L1657_cp2.1 L1657_cp2.2 = true := by
  decide +kernel
theorem L1657_fin : (prmOK pL1657 1657 && ptTest pL1657 (runFrom pL1657 (fmask pL1657) (cmask pL1657) (hmask pL1657) 1353 304 (true, L1657_cp2.1, L1657_cp2.2)) 1657 829 false) = true := by
  decide +kernel
theorem L1657_ok : RunOK pL1657 1657 (runFrom pL1657 (fmask pL1657) (cmask pL1657) (hmask pL1657) 1353 304 (true, L1657_cp2.1, L1657_cp2.2)) ∧ ptTest pL1657 (runFrom pL1657 (fmask pL1657) (cmask pL1657) (hmask pL1657) 1353 304 (true, L1657_cp2.1, L1657_cp2.2)) 1657 829 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1657_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1657_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1657_fin) true) L1657_seg1) L1657_seg2) (by decide) rfl L1657_fin ptTest_fst
noncomputable def H1657_cp1 : Nat × Nat := t7val% (fastRun pH1657 1 956 (init pH1657) (init pH1657))
theorem H1657_seg1 : segOK pH1657 1 956 (init pH1657) (init pH1657) H1657_cp1.1 H1657_cp1.2 = true := by
  decide +kernel
noncomputable def H1657_cp2 : Nat × Nat := t7val% (fastRun pH1657 1 1352 (init pH1657) (init pH1657))
theorem H1657_seg2 : segOK pH1657 957 396 H1657_cp1.1 H1657_cp1.2 H1657_cp2.1 H1657_cp2.2 = true := by
  decide +kernel
theorem H1657_fin : (prmOK pH1657 1657 && ptTest pH1657 (runFrom pH1657 (fmask pH1657) (cmask pH1657) (hmask pH1657) 1353 304 (true, H1657_cp2.1, H1657_cp2.2)) 1657 829 true) = true := by
  decide +kernel
theorem H1657_ok : RunOK pH1657 1657 (runFrom pH1657 (fmask pH1657) (cmask pH1657) (hmask pH1657) 1353 304 (true, H1657_cp2.1, H1657_cp2.2)) ∧ ptTest pH1657 (runFrom pH1657 (fmask pH1657) (cmask pH1657) (hmask pH1657) 1353 304 (true, H1657_cp2.1, H1657_cp2.2)) 1657 829 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1657_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1657_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1657_fin) true) H1657_seg1) H1657_seg2) (by decide) rfl H1657_fin ptTest_fst
noncomputable def I1657_cp1 : Nat × Nat := t7val% (fastRun pI1657 1 1171 (init pI1657) (init pI1657))
theorem I1657_seg1 : segOK pI1657 1 1171 (init pI1657) (init pI1657) I1657_cp1.1 I1657_cp1.2 = true := by
  decide +kernel
theorem I1657_fin : (prmOK pI1657 1657 && intTest pI1657 (runFrom pI1657 (fmask pI1657) (cmask pI1657) (hmask pI1657) 1172 485 (true, I1657_cp1.1, I1657_cp1.2)) 1657 21 false) = true := by
  decide +kernel
theorem I1657_ok : RunOK pI1657 1657 (runFrom pI1657 (fmask pI1657) (cmask pI1657) (hmask pI1657) 1172 485 (true, I1657_cp1.1, I1657_cp1.2)) ∧ intTest pI1657 (runFrom pI1657 (fmask pI1657) (cmask pI1657) (hmask pI1657) 1172 485 (true, I1657_cp1.1, I1657_cp1.2)) 1657 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1657_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1657_fin) true) I1657_seg1) (by decide) rfl I1657_fin intTest_fst
theorem link1657 : linkOK pL1657 pH1657 pI1657 = true := by decide +kernel
theorem cvx1657 : ConvexBetweenHumps 1657 :=
  cvx_of L1657_ok H1657_ok I1657_ok link1657 (by decide)

/-! ### `N = 1658` -/

def pL1658 : Prm := ⟨80, 37, 40, 1660, 11, 18446744073709551616, 114681889184163782, 114681889184163782⟩
def pH1658 : Prm := ⟨80, 37, 40, 1660, 11, 18446744073709551616, 114682988695791558, 114682988695791558⟩
def pI1658 : Prm := ⟨67, 33, 31, 1660, 11, 18446744073709551616, 114681889184163782, 114682988695791558⟩
noncomputable def L1658_cp1 : Nat × Nat := t7val% (fastRun pL1658 1 956 (init pL1658) (init pL1658))
theorem L1658_seg1 : segOK pL1658 1 956 (init pL1658) (init pL1658) L1658_cp1.1 L1658_cp1.2 = true := by
  decide +kernel
noncomputable def L1658_cp2 : Nat × Nat := t7val% (fastRun pL1658 1 1353 (init pL1658) (init pL1658))
theorem L1658_seg2 : segOK pL1658 957 397 L1658_cp1.1 L1658_cp1.2 L1658_cp2.1 L1658_cp2.2 = true := by
  decide +kernel
theorem L1658_fin : (prmOK pL1658 1658 && ptTest pL1658 (runFrom pL1658 (fmask pL1658) (cmask pL1658) (hmask pL1658) 1354 304 (true, L1658_cp2.1, L1658_cp2.2)) 1658 829 false) = true := by
  decide +kernel
theorem L1658_ok : RunOK pL1658 1658 (runFrom pL1658 (fmask pL1658) (cmask pL1658) (hmask pL1658) 1354 304 (true, L1658_cp2.1, L1658_cp2.2)) ∧ ptTest pL1658 (runFrom pL1658 (fmask pL1658) (cmask pL1658) (hmask pL1658) 1354 304 (true, L1658_cp2.1, L1658_cp2.2)) 1658 829 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1658_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1658_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1658_fin) true) L1658_seg1) L1658_seg2) (by decide) rfl L1658_fin ptTest_fst
noncomputable def H1658_cp1 : Nat × Nat := t7val% (fastRun pH1658 1 956 (init pH1658) (init pH1658))
theorem H1658_seg1 : segOK pH1658 1 956 (init pH1658) (init pH1658) H1658_cp1.1 H1658_cp1.2 = true := by
  decide +kernel
noncomputable def H1658_cp2 : Nat × Nat := t7val% (fastRun pH1658 1 1353 (init pH1658) (init pH1658))
theorem H1658_seg2 : segOK pH1658 957 397 H1658_cp1.1 H1658_cp1.2 H1658_cp2.1 H1658_cp2.2 = true := by
  decide +kernel
theorem H1658_fin : (prmOK pH1658 1658 && ptTest pH1658 (runFrom pH1658 (fmask pH1658) (cmask pH1658) (hmask pH1658) 1354 304 (true, H1658_cp2.1, H1658_cp2.2)) 1658 829 true) = true := by
  decide +kernel
theorem H1658_ok : RunOK pH1658 1658 (runFrom pH1658 (fmask pH1658) (cmask pH1658) (hmask pH1658) 1354 304 (true, H1658_cp2.1, H1658_cp2.2)) ∧ ptTest pH1658 (runFrom pH1658 (fmask pH1658) (cmask pH1658) (hmask pH1658) 1354 304 (true, H1658_cp2.1, H1658_cp2.2)) 1658 829 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1658_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1658_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1658_fin) true) H1658_seg1) H1658_seg2) (by decide) rfl H1658_fin ptTest_fst
noncomputable def I1658_cp1 : Nat × Nat := t7val% (fastRun pI1658 1 1171 (init pI1658) (init pI1658))
theorem I1658_seg1 : segOK pI1658 1 1171 (init pI1658) (init pI1658) I1658_cp1.1 I1658_cp1.2 = true := by
  decide +kernel
theorem I1658_fin : (prmOK pI1658 1658 && intTest pI1658 (runFrom pI1658 (fmask pI1658) (cmask pI1658) (hmask pI1658) 1172 486 (true, I1658_cp1.1, I1658_cp1.2)) 1658 21 true) = true := by
  decide +kernel
theorem I1658_ok : RunOK pI1658 1658 (runFrom pI1658 (fmask pI1658) (cmask pI1658) (hmask pI1658) 1172 486 (true, I1658_cp1.1, I1658_cp1.2)) ∧ intTest pI1658 (runFrom pI1658 (fmask pI1658) (cmask pI1658) (hmask pI1658) 1172 486 (true, I1658_cp1.1, I1658_cp1.2)) 1658 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1658_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1658_fin) true) I1658_seg1) (by decide) rfl I1658_fin intTest_fst
theorem link1658 : linkOK pL1658 pH1658 pI1658 = true := by decide +kernel
theorem cvx1658 : ConvexBetweenHumps 1658 :=
  cvx_of L1658_ok H1658_ok I1658_ok link1658 (by decide)
theorem cenlink1658 : cenLinkOK pI1658 1658 = true := by decide +kernel
theorem cen1658 : CenterUniqueMin 1658 ∧ DipHyp 1658 ∧ OnePointHyps 1658 :=
  cen_of L1658_ok H1658_ok I1658_ok link1658 cenlink1658

/-! ### `N = 1659` -/

def pL1659 : Prm := ⟨80, 37, 40, 1661, 11, 18446744073709551616, 114625389120767332, 114625389120767332⟩
def pH1659 : Prm := ⟨80, 37, 40, 1661, 11, 18446744073709551616, 114626488632395108, 114626488632395108⟩
def pI1659 : Prm := ⟨67, 33, 31, 1661, 11, 18446744073709551616, 114625389120767332, 114626488632395108⟩
noncomputable def L1659_cp1 : Nat × Nat := t7val% (fastRun pL1659 1 957 (init pL1659) (init pL1659))
theorem L1659_seg1 : segOK pL1659 1 957 (init pL1659) (init pL1659) L1659_cp1.1 L1659_cp1.2 = true := by
  decide +kernel
noncomputable def L1659_cp2 : Nat × Nat := t7val% (fastRun pL1659 1 1354 (init pL1659) (init pL1659))
theorem L1659_seg2 : segOK pL1659 958 397 L1659_cp1.1 L1659_cp1.2 L1659_cp2.1 L1659_cp2.2 = true := by
  decide +kernel
theorem L1659_fin : (prmOK pL1659 1659 && ptTest pL1659 (runFrom pL1659 (fmask pL1659) (cmask pL1659) (hmask pL1659) 1355 304 (true, L1659_cp2.1, L1659_cp2.2)) 1659 830 false) = true := by
  decide +kernel
theorem L1659_ok : RunOK pL1659 1659 (runFrom pL1659 (fmask pL1659) (cmask pL1659) (hmask pL1659) 1355 304 (true, L1659_cp2.1, L1659_cp2.2)) ∧ ptTest pL1659 (runFrom pL1659 (fmask pL1659) (cmask pL1659) (hmask pL1659) 1355 304 (true, L1659_cp2.1, L1659_cp2.2)) 1659 830 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1659_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1659_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1659_fin) true) L1659_seg1) L1659_seg2) (by decide) rfl L1659_fin ptTest_fst
noncomputable def H1659_cp1 : Nat × Nat := t7val% (fastRun pH1659 1 957 (init pH1659) (init pH1659))
theorem H1659_seg1 : segOK pH1659 1 957 (init pH1659) (init pH1659) H1659_cp1.1 H1659_cp1.2 = true := by
  decide +kernel
noncomputable def H1659_cp2 : Nat × Nat := t7val% (fastRun pH1659 1 1354 (init pH1659) (init pH1659))
theorem H1659_seg2 : segOK pH1659 958 397 H1659_cp1.1 H1659_cp1.2 H1659_cp2.1 H1659_cp2.2 = true := by
  decide +kernel
theorem H1659_fin : (prmOK pH1659 1659 && ptTest pH1659 (runFrom pH1659 (fmask pH1659) (cmask pH1659) (hmask pH1659) 1355 304 (true, H1659_cp2.1, H1659_cp2.2)) 1659 830 true) = true := by
  decide +kernel
theorem H1659_ok : RunOK pH1659 1659 (runFrom pH1659 (fmask pH1659) (cmask pH1659) (hmask pH1659) 1355 304 (true, H1659_cp2.1, H1659_cp2.2)) ∧ ptTest pH1659 (runFrom pH1659 (fmask pH1659) (cmask pH1659) (hmask pH1659) 1355 304 (true, H1659_cp2.1, H1659_cp2.2)) 1659 830 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1659_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1659_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1659_fin) true) H1659_seg1) H1659_seg2) (by decide) rfl H1659_fin ptTest_fst
noncomputable def I1659_cp1 : Nat × Nat := t7val% (fastRun pI1659 1 1172 (init pI1659) (init pI1659))
theorem I1659_seg1 : segOK pI1659 1 1172 (init pI1659) (init pI1659) I1659_cp1.1 I1659_cp1.2 = true := by
  decide +kernel
theorem I1659_fin : (prmOK pI1659 1659 && intTest pI1659 (runFrom pI1659 (fmask pI1659) (cmask pI1659) (hmask pI1659) 1173 486 (true, I1659_cp1.1, I1659_cp1.2)) 1659 21 false) = true := by
  decide +kernel
theorem I1659_ok : RunOK pI1659 1659 (runFrom pI1659 (fmask pI1659) (cmask pI1659) (hmask pI1659) 1173 486 (true, I1659_cp1.1, I1659_cp1.2)) ∧ intTest pI1659 (runFrom pI1659 (fmask pI1659) (cmask pI1659) (hmask pI1659) 1173 486 (true, I1659_cp1.1, I1659_cp1.2)) 1659 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1659_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1659_fin) true) I1659_seg1) (by decide) rfl I1659_fin intTest_fst
theorem link1659 : linkOK pL1659 pH1659 pI1659 = true := by decide +kernel
theorem cvx1659 : ConvexBetweenHumps 1659 :=
  cvx_of L1659_ok H1659_ok I1659_ok link1659 (by decide)

/-! ### `N = 1660` -/

def pL1660 : Prm := ⟨80, 37, 40, 1662, 11, 18446744073709551616, 114568974165722757, 114568974165722757⟩
def pH1660 : Prm := ⟨80, 37, 40, 1662, 11, 18446744073709551616, 114570073677350533, 114570073677350533⟩
def pI1660 : Prm := ⟨67, 33, 31, 1662, 11, 18446744073709551616, 114568974165722757, 114570073677350533⟩
noncomputable def L1660_cp1 : Nat × Nat := t7val% (fastRun pL1660 1 957 (init pL1660) (init pL1660))
theorem L1660_seg1 : segOK pL1660 1 957 (init pL1660) (init pL1660) L1660_cp1.1 L1660_cp1.2 = true := by
  decide +kernel
noncomputable def L1660_cp2 : Nat × Nat := t7val% (fastRun pL1660 1 1354 (init pL1660) (init pL1660))
theorem L1660_seg2 : segOK pL1660 958 397 L1660_cp1.1 L1660_cp1.2 L1660_cp2.1 L1660_cp2.2 = true := by
  decide +kernel
theorem L1660_fin : (prmOK pL1660 1660 && ptTest pL1660 (runFrom pL1660 (fmask pL1660) (cmask pL1660) (hmask pL1660) 1355 305 (true, L1660_cp2.1, L1660_cp2.2)) 1660 830 false) = true := by
  decide +kernel
theorem L1660_ok : RunOK pL1660 1660 (runFrom pL1660 (fmask pL1660) (cmask pL1660) (hmask pL1660) 1355 305 (true, L1660_cp2.1, L1660_cp2.2)) ∧ ptTest pL1660 (runFrom pL1660 (fmask pL1660) (cmask pL1660) (hmask pL1660) 1355 305 (true, L1660_cp2.1, L1660_cp2.2)) 1660 830 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1660_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1660_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1660_fin) true) L1660_seg1) L1660_seg2) (by decide) rfl L1660_fin ptTest_fst
noncomputable def H1660_cp1 : Nat × Nat := t7val% (fastRun pH1660 1 957 (init pH1660) (init pH1660))
theorem H1660_seg1 : segOK pH1660 1 957 (init pH1660) (init pH1660) H1660_cp1.1 H1660_cp1.2 = true := by
  decide +kernel
noncomputable def H1660_cp2 : Nat × Nat := t7val% (fastRun pH1660 1 1354 (init pH1660) (init pH1660))
theorem H1660_seg2 : segOK pH1660 958 397 H1660_cp1.1 H1660_cp1.2 H1660_cp2.1 H1660_cp2.2 = true := by
  decide +kernel
theorem H1660_fin : (prmOK pH1660 1660 && ptTest pH1660 (runFrom pH1660 (fmask pH1660) (cmask pH1660) (hmask pH1660) 1355 305 (true, H1660_cp2.1, H1660_cp2.2)) 1660 830 true) = true := by
  decide +kernel
theorem H1660_ok : RunOK pH1660 1660 (runFrom pH1660 (fmask pH1660) (cmask pH1660) (hmask pH1660) 1355 305 (true, H1660_cp2.1, H1660_cp2.2)) ∧ ptTest pH1660 (runFrom pH1660 (fmask pH1660) (cmask pH1660) (hmask pH1660) 1355 305 (true, H1660_cp2.1, H1660_cp2.2)) 1660 830 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1660_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1660_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1660_fin) true) H1660_seg1) H1660_seg2) (by decide) rfl H1660_fin ptTest_fst
noncomputable def I1660_cp1 : Nat × Nat := t7val% (fastRun pI1660 1 1173 (init pI1660) (init pI1660))
theorem I1660_seg1 : segOK pI1660 1 1173 (init pI1660) (init pI1660) I1660_cp1.1 I1660_cp1.2 = true := by
  decide +kernel
theorem I1660_fin : (prmOK pI1660 1660 && intTest pI1660 (runFrom pI1660 (fmask pI1660) (cmask pI1660) (hmask pI1660) 1174 486 (true, I1660_cp1.1, I1660_cp1.2)) 1660 21 true) = true := by
  decide +kernel
theorem I1660_ok : RunOK pI1660 1660 (runFrom pI1660 (fmask pI1660) (cmask pI1660) (hmask pI1660) 1174 486 (true, I1660_cp1.1, I1660_cp1.2)) ∧ intTest pI1660 (runFrom pI1660 (fmask pI1660) (cmask pI1660) (hmask pI1660) 1174 486 (true, I1660_cp1.1, I1660_cp1.2)) 1660 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1660_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1660_fin) true) I1660_seg1) (by decide) rfl I1660_fin intTest_fst
theorem link1660 : linkOK pL1660 pH1660 pI1660 = true := by decide +kernel
theorem cvx1660 : ConvexBetweenHumps 1660 :=
  cvx_of L1660_ok H1660_ok I1660_ok link1660 (by decide)
theorem cenlink1660 : cenLinkOK pI1660 1660 = true := by decide +kernel
theorem cen1660 : CenterUniqueMin 1660 ∧ DipHyp 1660 ∧ OnePointHyps 1660 :=
  cen_of L1660_ok H1660_ok I1660_ok link1660 cenlink1660

/-! ### `N = 1661` -/

def pL1661 : Prm := ⟨80, 37, 40, 1663, 11, 18446744073709551616, 114512594918963023, 114512594918963023⟩
def pH1661 : Prm := ⟨80, 37, 40, 1663, 11, 18446744073709551616, 114513694430590799, 114513694430590799⟩
def pI1661 : Prm := ⟨67, 33, 31, 1663, 11, 18446744073709551616, 114512594918963023, 114513694430590799⟩
noncomputable def L1661_cp1 : Nat × Nat := t7val% (fastRun pL1661 1 958 (init pL1661) (init pL1661))
theorem L1661_seg1 : segOK pL1661 1 958 (init pL1661) (init pL1661) L1661_cp1.1 L1661_cp1.2 = true := by
  decide +kernel
noncomputable def L1661_cp2 : Nat × Nat := t7val% (fastRun pL1661 1 1355 (init pL1661) (init pL1661))
theorem L1661_seg2 : segOK pL1661 959 397 L1661_cp1.1 L1661_cp1.2 L1661_cp2.1 L1661_cp2.2 = true := by
  decide +kernel
theorem L1661_fin : (prmOK pL1661 1661 && ptTest pL1661 (runFrom pL1661 (fmask pL1661) (cmask pL1661) (hmask pL1661) 1356 305 (true, L1661_cp2.1, L1661_cp2.2)) 1661 831 false) = true := by
  decide +kernel
theorem L1661_ok : RunOK pL1661 1661 (runFrom pL1661 (fmask pL1661) (cmask pL1661) (hmask pL1661) 1356 305 (true, L1661_cp2.1, L1661_cp2.2)) ∧ ptTest pL1661 (runFrom pL1661 (fmask pL1661) (cmask pL1661) (hmask pL1661) 1356 305 (true, L1661_cp2.1, L1661_cp2.2)) 1661 831 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1661_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1661_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1661_fin) true) L1661_seg1) L1661_seg2) (by decide) rfl L1661_fin ptTest_fst
noncomputable def H1661_cp1 : Nat × Nat := t7val% (fastRun pH1661 1 958 (init pH1661) (init pH1661))
theorem H1661_seg1 : segOK pH1661 1 958 (init pH1661) (init pH1661) H1661_cp1.1 H1661_cp1.2 = true := by
  decide +kernel
noncomputable def H1661_cp2 : Nat × Nat := t7val% (fastRun pH1661 1 1355 (init pH1661) (init pH1661))
theorem H1661_seg2 : segOK pH1661 959 397 H1661_cp1.1 H1661_cp1.2 H1661_cp2.1 H1661_cp2.2 = true := by
  decide +kernel
theorem H1661_fin : (prmOK pH1661 1661 && ptTest pH1661 (runFrom pH1661 (fmask pH1661) (cmask pH1661) (hmask pH1661) 1356 305 (true, H1661_cp2.1, H1661_cp2.2)) 1661 831 true) = true := by
  decide +kernel
theorem H1661_ok : RunOK pH1661 1661 (runFrom pH1661 (fmask pH1661) (cmask pH1661) (hmask pH1661) 1356 305 (true, H1661_cp2.1, H1661_cp2.2)) ∧ ptTest pH1661 (runFrom pH1661 (fmask pH1661) (cmask pH1661) (hmask pH1661) 1356 305 (true, H1661_cp2.1, H1661_cp2.2)) 1661 831 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1661_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1661_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1661_fin) true) H1661_seg1) H1661_seg2) (by decide) rfl H1661_fin ptTest_fst
noncomputable def I1661_cp1 : Nat × Nat := t7val% (fastRun pI1661 1 1174 (init pI1661) (init pI1661))
theorem I1661_seg1 : segOK pI1661 1 1174 (init pI1661) (init pI1661) I1661_cp1.1 I1661_cp1.2 = true := by
  decide +kernel
theorem I1661_fin : (prmOK pI1661 1661 && intTest pI1661 (runFrom pI1661 (fmask pI1661) (cmask pI1661) (hmask pI1661) 1175 486 (true, I1661_cp1.1, I1661_cp1.2)) 1661 21 false) = true := by
  decide +kernel
theorem I1661_ok : RunOK pI1661 1661 (runFrom pI1661 (fmask pI1661) (cmask pI1661) (hmask pI1661) 1175 486 (true, I1661_cp1.1, I1661_cp1.2)) ∧ intTest pI1661 (runFrom pI1661 (fmask pI1661) (cmask pI1661) (hmask pI1661) 1175 486 (true, I1661_cp1.1, I1661_cp1.2)) 1661 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1661_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1661_fin) true) I1661_seg1) (by decide) rfl I1661_fin intTest_fst
theorem link1661 : linkOK pL1661 pH1661 pI1661 = true := by decide +kernel
theorem cvx1661 : ConvexBetweenHumps 1661 :=
  cvx_of L1661_ok H1661_ok I1661_ok link1661 (by decide)

/-! ### `N = 1662` -/

def pL1662 : Prm := ⟨80, 37, 40, 1664, 11, 18446744073709551616, 114456300490406327, 114456300490406327⟩
def pH1662 : Prm := ⟨80, 37, 40, 1664, 11, 18446744073709551616, 114457400002034103, 114457400002034103⟩
def pI1662 : Prm := ⟨67, 33, 31, 1664, 11, 18446744073709551616, 114456300490406327, 114457400002034103⟩
noncomputable def L1662_cp1 : Nat × Nat := t7val% (fastRun pL1662 1 959 (init pL1662) (init pL1662))
theorem L1662_seg1 : segOK pL1662 1 959 (init pL1662) (init pL1662) L1662_cp1.1 L1662_cp1.2 = true := by
  decide +kernel
noncomputable def L1662_cp2 : Nat × Nat := t7val% (fastRun pL1662 1 1356 (init pL1662) (init pL1662))
theorem L1662_seg2 : segOK pL1662 960 397 L1662_cp1.1 L1662_cp1.2 L1662_cp2.1 L1662_cp2.2 = true := by
  decide +kernel
theorem L1662_fin : (prmOK pL1662 1662 && ptTest pL1662 (runFrom pL1662 (fmask pL1662) (cmask pL1662) (hmask pL1662) 1357 305 (true, L1662_cp2.1, L1662_cp2.2)) 1662 831 false) = true := by
  decide +kernel
theorem L1662_ok : RunOK pL1662 1662 (runFrom pL1662 (fmask pL1662) (cmask pL1662) (hmask pL1662) 1357 305 (true, L1662_cp2.1, L1662_cp2.2)) ∧ ptTest pL1662 (runFrom pL1662 (fmask pL1662) (cmask pL1662) (hmask pL1662) 1357 305 (true, L1662_cp2.1, L1662_cp2.2)) 1662 831 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1662_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1662_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1662_fin) true) L1662_seg1) L1662_seg2) (by decide) rfl L1662_fin ptTest_fst
noncomputable def H1662_cp1 : Nat × Nat := t7val% (fastRun pH1662 1 959 (init pH1662) (init pH1662))
theorem H1662_seg1 : segOK pH1662 1 959 (init pH1662) (init pH1662) H1662_cp1.1 H1662_cp1.2 = true := by
  decide +kernel
noncomputable def H1662_cp2 : Nat × Nat := t7val% (fastRun pH1662 1 1356 (init pH1662) (init pH1662))
theorem H1662_seg2 : segOK pH1662 960 397 H1662_cp1.1 H1662_cp1.2 H1662_cp2.1 H1662_cp2.2 = true := by
  decide +kernel
theorem H1662_fin : (prmOK pH1662 1662 && ptTest pH1662 (runFrom pH1662 (fmask pH1662) (cmask pH1662) (hmask pH1662) 1357 305 (true, H1662_cp2.1, H1662_cp2.2)) 1662 831 true) = true := by
  decide +kernel
theorem H1662_ok : RunOK pH1662 1662 (runFrom pH1662 (fmask pH1662) (cmask pH1662) (hmask pH1662) 1357 305 (true, H1662_cp2.1, H1662_cp2.2)) ∧ ptTest pH1662 (runFrom pH1662 (fmask pH1662) (cmask pH1662) (hmask pH1662) 1357 305 (true, H1662_cp2.1, H1662_cp2.2)) 1662 831 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1662_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1662_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1662_fin) true) H1662_seg1) H1662_seg2) (by decide) rfl H1662_fin ptTest_fst
noncomputable def I1662_cp1 : Nat × Nat := t7val% (fastRun pI1662 1 1174 (init pI1662) (init pI1662))
theorem I1662_seg1 : segOK pI1662 1 1174 (init pI1662) (init pI1662) I1662_cp1.1 I1662_cp1.2 = true := by
  decide +kernel
theorem I1662_fin : (prmOK pI1662 1662 && intTest pI1662 (runFrom pI1662 (fmask pI1662) (cmask pI1662) (hmask pI1662) 1175 487 (true, I1662_cp1.1, I1662_cp1.2)) 1662 21 true) = true := by
  decide +kernel
theorem I1662_ok : RunOK pI1662 1662 (runFrom pI1662 (fmask pI1662) (cmask pI1662) (hmask pI1662) 1175 487 (true, I1662_cp1.1, I1662_cp1.2)) ∧ intTest pI1662 (runFrom pI1662 (fmask pI1662) (cmask pI1662) (hmask pI1662) 1175 487 (true, I1662_cp1.1, I1662_cp1.2)) 1662 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1662_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1662_fin) true) I1662_seg1) (by decide) rfl I1662_fin intTest_fst
theorem link1662 : linkOK pL1662 pH1662 pI1662 = true := by decide +kernel
theorem cvx1662 : ConvexBetweenHumps 1662 :=
  cvx_of L1662_ok H1662_ok I1662_ok link1662 (by decide)
theorem cenlink1662 : cenLinkOK pI1662 1662 = true := by decide +kernel
theorem cen1662 : CenterUniqueMin 1662 ∧ DipHyp 1662 ∧ OnePointHyps 1662 :=
  cen_of L1662_ok H1662_ok I1662_ok link1662 cenlink1662

/-! ### `N = 1663` -/

def pL1663 : Prm := ⟨80, 37, 40, 1665, 11, 18446744073709551616, 114400041661058873, 114400041661058873⟩
def pH1663 : Prm := ⟨80, 37, 40, 1665, 11, 18446744073709551616, 114401141172686649, 114401141172686649⟩
def pI1663 : Prm := ⟨67, 33, 31, 1665, 11, 18446744073709551616, 114400041661058873, 114401141172686649⟩
noncomputable def L1663_cp1 : Nat × Nat := t7val% (fastRun pL1663 1 959 (init pL1663) (init pL1663))
theorem L1663_seg1 : segOK pL1663 1 959 (init pL1663) (init pL1663) L1663_cp1.1 L1663_cp1.2 = true := by
  decide +kernel
noncomputable def L1663_cp2 : Nat × Nat := t7val% (fastRun pL1663 1 1357 (init pL1663) (init pL1663))
theorem L1663_seg2 : segOK pL1663 960 398 L1663_cp1.1 L1663_cp1.2 L1663_cp2.1 L1663_cp2.2 = true := by
  decide +kernel
theorem L1663_fin : (prmOK pL1663 1663 && ptTest pL1663 (runFrom pL1663 (fmask pL1663) (cmask pL1663) (hmask pL1663) 1358 305 (true, L1663_cp2.1, L1663_cp2.2)) 1663 832 false) = true := by
  decide +kernel
theorem L1663_ok : RunOK pL1663 1663 (runFrom pL1663 (fmask pL1663) (cmask pL1663) (hmask pL1663) 1358 305 (true, L1663_cp2.1, L1663_cp2.2)) ∧ ptTest pL1663 (runFrom pL1663 (fmask pL1663) (cmask pL1663) (hmask pL1663) 1358 305 (true, L1663_cp2.1, L1663_cp2.2)) 1663 832 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1663_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1663_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1663_fin) true) L1663_seg1) L1663_seg2) (by decide) rfl L1663_fin ptTest_fst
noncomputable def H1663_cp1 : Nat × Nat := t7val% (fastRun pH1663 1 959 (init pH1663) (init pH1663))
theorem H1663_seg1 : segOK pH1663 1 959 (init pH1663) (init pH1663) H1663_cp1.1 H1663_cp1.2 = true := by
  decide +kernel
noncomputable def H1663_cp2 : Nat × Nat := t7val% (fastRun pH1663 1 1357 (init pH1663) (init pH1663))
theorem H1663_seg2 : segOK pH1663 960 398 H1663_cp1.1 H1663_cp1.2 H1663_cp2.1 H1663_cp2.2 = true := by
  decide +kernel
theorem H1663_fin : (prmOK pH1663 1663 && ptTest pH1663 (runFrom pH1663 (fmask pH1663) (cmask pH1663) (hmask pH1663) 1358 305 (true, H1663_cp2.1, H1663_cp2.2)) 1663 832 true) = true := by
  decide +kernel
theorem H1663_ok : RunOK pH1663 1663 (runFrom pH1663 (fmask pH1663) (cmask pH1663) (hmask pH1663) 1358 305 (true, H1663_cp2.1, H1663_cp2.2)) ∧ ptTest pH1663 (runFrom pH1663 (fmask pH1663) (cmask pH1663) (hmask pH1663) 1358 305 (true, H1663_cp2.1, H1663_cp2.2)) 1663 832 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1663_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1663_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1663_fin) true) H1663_seg1) H1663_seg2) (by decide) rfl H1663_fin ptTest_fst
noncomputable def I1663_cp1 : Nat × Nat := t7val% (fastRun pI1663 1 1175 (init pI1663) (init pI1663))
theorem I1663_seg1 : segOK pI1663 1 1175 (init pI1663) (init pI1663) I1663_cp1.1 I1663_cp1.2 = true := by
  decide +kernel
theorem I1663_fin : (prmOK pI1663 1663 && intTest pI1663 (runFrom pI1663 (fmask pI1663) (cmask pI1663) (hmask pI1663) 1176 487 (true, I1663_cp1.1, I1663_cp1.2)) 1663 21 false) = true := by
  decide +kernel
theorem I1663_ok : RunOK pI1663 1663 (runFrom pI1663 (fmask pI1663) (cmask pI1663) (hmask pI1663) 1176 487 (true, I1663_cp1.1, I1663_cp1.2)) ∧ intTest pI1663 (runFrom pI1663 (fmask pI1663) (cmask pI1663) (hmask pI1663) 1176 487 (true, I1663_cp1.1, I1663_cp1.2)) 1663 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1663_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1663_fin) true) I1663_seg1) (by decide) rfl I1663_fin intTest_fst
theorem link1663 : linkOK pL1663 pH1663 pI1663 = true := by decide +kernel
theorem cvx1663 : ConvexBetweenHumps 1663 :=
  cvx_of L1663_ok H1663_ok I1663_ok link1663 (by decide)

/-! ### `N = 1664` -/

def pL1664 : Prm := ⟨80, 37, 40, 1666, 11, 18446744073709551616, 114343867361093786, 114343867361093786⟩
def pH1664 : Prm := ⟨80, 37, 40, 1666, 11, 18446744073709551616, 114344966872721562, 114344966872721562⟩
def pI1664 : Prm := ⟨67, 33, 31, 1666, 11, 18446744073709551616, 114343867361093786, 114344966872721562⟩
noncomputable def L1664_cp1 : Nat × Nat := t7val% (fastRun pL1664 1 960 (init pL1664) (init pL1664))
theorem L1664_seg1 : segOK pL1664 1 960 (init pL1664) (init pL1664) L1664_cp1.1 L1664_cp1.2 = true := by
  decide +kernel
noncomputable def L1664_cp2 : Nat × Nat := t7val% (fastRun pL1664 1 1358 (init pL1664) (init pL1664))
theorem L1664_seg2 : segOK pL1664 961 398 L1664_cp1.1 L1664_cp1.2 L1664_cp2.1 L1664_cp2.2 = true := by
  decide +kernel
theorem L1664_fin : (prmOK pL1664 1664 && ptTest pL1664 (runFrom pL1664 (fmask pL1664) (cmask pL1664) (hmask pL1664) 1359 305 (true, L1664_cp2.1, L1664_cp2.2)) 1664 832 false) = true := by
  decide +kernel
theorem L1664_ok : RunOK pL1664 1664 (runFrom pL1664 (fmask pL1664) (cmask pL1664) (hmask pL1664) 1359 305 (true, L1664_cp2.1, L1664_cp2.2)) ∧ ptTest pL1664 (runFrom pL1664 (fmask pL1664) (cmask pL1664) (hmask pL1664) 1359 305 (true, L1664_cp2.1, L1664_cp2.2)) 1664 832 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1664_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1664_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1664_fin) true) L1664_seg1) L1664_seg2) (by decide) rfl L1664_fin ptTest_fst
noncomputable def H1664_cp1 : Nat × Nat := t7val% (fastRun pH1664 1 960 (init pH1664) (init pH1664))
theorem H1664_seg1 : segOK pH1664 1 960 (init pH1664) (init pH1664) H1664_cp1.1 H1664_cp1.2 = true := by
  decide +kernel
noncomputable def H1664_cp2 : Nat × Nat := t7val% (fastRun pH1664 1 1358 (init pH1664) (init pH1664))
theorem H1664_seg2 : segOK pH1664 961 398 H1664_cp1.1 H1664_cp1.2 H1664_cp2.1 H1664_cp2.2 = true := by
  decide +kernel
theorem H1664_fin : (prmOK pH1664 1664 && ptTest pH1664 (runFrom pH1664 (fmask pH1664) (cmask pH1664) (hmask pH1664) 1359 305 (true, H1664_cp2.1, H1664_cp2.2)) 1664 832 true) = true := by
  decide +kernel
theorem H1664_ok : RunOK pH1664 1664 (runFrom pH1664 (fmask pH1664) (cmask pH1664) (hmask pH1664) 1359 305 (true, H1664_cp2.1, H1664_cp2.2)) ∧ ptTest pH1664 (runFrom pH1664 (fmask pH1664) (cmask pH1664) (hmask pH1664) 1359 305 (true, H1664_cp2.1, H1664_cp2.2)) 1664 832 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1664_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1664_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1664_fin) true) H1664_seg1) H1664_seg2) (by decide) rfl H1664_fin ptTest_fst
noncomputable def I1664_cp1 : Nat × Nat := t7val% (fastRun pI1664 1 1176 (init pI1664) (init pI1664))
theorem I1664_seg1 : segOK pI1664 1 1176 (init pI1664) (init pI1664) I1664_cp1.1 I1664_cp1.2 = true := by
  decide +kernel
theorem I1664_fin : (prmOK pI1664 1664 && intTest pI1664 (runFrom pI1664 (fmask pI1664) (cmask pI1664) (hmask pI1664) 1177 487 (true, I1664_cp1.1, I1664_cp1.2)) 1664 21 true) = true := by
  decide +kernel
theorem I1664_ok : RunOK pI1664 1664 (runFrom pI1664 (fmask pI1664) (cmask pI1664) (hmask pI1664) 1177 487 (true, I1664_cp1.1, I1664_cp1.2)) ∧ intTest pI1664 (runFrom pI1664 (fmask pI1664) (cmask pI1664) (hmask pI1664) 1177 487 (true, I1664_cp1.1, I1664_cp1.2)) 1664 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1664_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1664_fin) true) I1664_seg1) (by decide) rfl I1664_fin intTest_fst
theorem link1664 : linkOK pL1664 pH1664 pI1664 = true := by decide +kernel
theorem cvx1664 : ConvexBetweenHumps 1664 :=
  cvx_of L1664_ok H1664_ok I1664_ok link1664 (by decide)
theorem cenlink1664 : cenLinkOK pI1664 1664 = true := by decide +kernel
theorem cen1664 : CenterUniqueMin 1664 ∧ DipHyp 1664 ∧ OnePointHyps 1664 :=
  cen_of L1664_ok H1664_ok I1664_ok link1664 cenlink1664

/-! ### `N = 1665` -/

def pL1665 : Prm := ⟨80, 37, 40, 1667, 11, 18446744073709551616, 114287728551686619, 114287728551686619⟩
def pH1665 : Prm := ⟨80, 37, 40, 1667, 11, 18446744073709551616, 114288828063314395, 114288828063314395⟩
def pI1665 : Prm := ⟨67, 33, 31, 1667, 11, 18446744073709551616, 114287728551686619, 114288828063314395⟩
noncomputable def L1665_cp1 : Nat × Nat := t7val% (fastRun pL1665 1 960 (init pL1665) (init pL1665))
theorem L1665_seg1 : segOK pL1665 1 960 (init pL1665) (init pL1665) L1665_cp1.1 L1665_cp1.2 = true := by
  decide +kernel
noncomputable def L1665_cp2 : Nat × Nat := t7val% (fastRun pL1665 1 1358 (init pL1665) (init pL1665))
theorem L1665_seg2 : segOK pL1665 961 398 L1665_cp1.1 L1665_cp1.2 L1665_cp2.1 L1665_cp2.2 = true := by
  decide +kernel
theorem L1665_fin : (prmOK pL1665 1665 && ptTest pL1665 (runFrom pL1665 (fmask pL1665) (cmask pL1665) (hmask pL1665) 1359 306 (true, L1665_cp2.1, L1665_cp2.2)) 1665 833 false) = true := by
  decide +kernel
theorem L1665_ok : RunOK pL1665 1665 (runFrom pL1665 (fmask pL1665) (cmask pL1665) (hmask pL1665) 1359 306 (true, L1665_cp2.1, L1665_cp2.2)) ∧ ptTest pL1665 (runFrom pL1665 (fmask pL1665) (cmask pL1665) (hmask pL1665) 1359 306 (true, L1665_cp2.1, L1665_cp2.2)) 1665 833 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1665_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1665_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1665_fin) true) L1665_seg1) L1665_seg2) (by decide) rfl L1665_fin ptTest_fst
noncomputable def H1665_cp1 : Nat × Nat := t7val% (fastRun pH1665 1 960 (init pH1665) (init pH1665))
theorem H1665_seg1 : segOK pH1665 1 960 (init pH1665) (init pH1665) H1665_cp1.1 H1665_cp1.2 = true := by
  decide +kernel
noncomputable def H1665_cp2 : Nat × Nat := t7val% (fastRun pH1665 1 1358 (init pH1665) (init pH1665))
theorem H1665_seg2 : segOK pH1665 961 398 H1665_cp1.1 H1665_cp1.2 H1665_cp2.1 H1665_cp2.2 = true := by
  decide +kernel
theorem H1665_fin : (prmOK pH1665 1665 && ptTest pH1665 (runFrom pH1665 (fmask pH1665) (cmask pH1665) (hmask pH1665) 1359 306 (true, H1665_cp2.1, H1665_cp2.2)) 1665 833 true) = true := by
  decide +kernel
theorem H1665_ok : RunOK pH1665 1665 (runFrom pH1665 (fmask pH1665) (cmask pH1665) (hmask pH1665) 1359 306 (true, H1665_cp2.1, H1665_cp2.2)) ∧ ptTest pH1665 (runFrom pH1665 (fmask pH1665) (cmask pH1665) (hmask pH1665) 1359 306 (true, H1665_cp2.1, H1665_cp2.2)) 1665 833 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1665_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1665_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1665_fin) true) H1665_seg1) H1665_seg2) (by decide) rfl H1665_fin ptTest_fst
noncomputable def I1665_cp1 : Nat × Nat := t7val% (fastRun pI1665 1 1176 (init pI1665) (init pI1665))
theorem I1665_seg1 : segOK pI1665 1 1176 (init pI1665) (init pI1665) I1665_cp1.1 I1665_cp1.2 = true := by
  decide +kernel
theorem I1665_fin : (prmOK pI1665 1665 && intTest pI1665 (runFrom pI1665 (fmask pI1665) (cmask pI1665) (hmask pI1665) 1177 488 (true, I1665_cp1.1, I1665_cp1.2)) 1665 21 false) = true := by
  decide +kernel
theorem I1665_ok : RunOK pI1665 1665 (runFrom pI1665 (fmask pI1665) (cmask pI1665) (hmask pI1665) 1177 488 (true, I1665_cp1.1, I1665_cp1.2)) ∧ intTest pI1665 (runFrom pI1665 (fmask pI1665) (cmask pI1665) (hmask pI1665) 1177 488 (true, I1665_cp1.1, I1665_cp1.2)) 1665 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1665_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1665_fin) true) I1665_seg1) (by decide) rfl I1665_fin intTest_fst
theorem link1665 : linkOK pL1665 pH1665 pI1665 = true := by decide +kernel
theorem cvx1665 : ConvexBetweenHumps 1665 :=
  cvx_of L1665_ok H1665_ok I1665_ok link1665 (by decide)

/-! ### `N = 1666` -/

def pL1666 : Prm := ⟨80, 37, 40, 1668, 11, 18446744073709551616, 114231673984187759, 114231673984187759⟩
def pH1666 : Prm := ⟨80, 37, 40, 1668, 11, 18446744073709551616, 114232773495815535, 114232773495815535⟩
def pI1666 : Prm := ⟨67, 33, 31, 1668, 11, 18446744073709551616, 114231673984187759, 114232773495815535⟩
noncomputable def L1666_cp1 : Nat × Nat := t7val% (fastRun pL1666 1 961 (init pL1666) (init pL1666))
theorem L1666_seg1 : segOK pL1666 1 961 (init pL1666) (init pL1666) L1666_cp1.1 L1666_cp1.2 = true := by
  decide +kernel
noncomputable def L1666_cp2 : Nat × Nat := t7val% (fastRun pL1666 1 1359 (init pL1666) (init pL1666))
theorem L1666_seg2 : segOK pL1666 962 398 L1666_cp1.1 L1666_cp1.2 L1666_cp2.1 L1666_cp2.2 = true := by
  decide +kernel
theorem L1666_fin : (prmOK pL1666 1666 && ptTest pL1666 (runFrom pL1666 (fmask pL1666) (cmask pL1666) (hmask pL1666) 1360 306 (true, L1666_cp2.1, L1666_cp2.2)) 1666 833 false) = true := by
  decide +kernel
theorem L1666_ok : RunOK pL1666 1666 (runFrom pL1666 (fmask pL1666) (cmask pL1666) (hmask pL1666) 1360 306 (true, L1666_cp2.1, L1666_cp2.2)) ∧ ptTest pL1666 (runFrom pL1666 (fmask pL1666) (cmask pL1666) (hmask pL1666) 1360 306 (true, L1666_cp2.1, L1666_cp2.2)) 1666 833 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1666_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1666_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1666_fin) true) L1666_seg1) L1666_seg2) (by decide) rfl L1666_fin ptTest_fst
noncomputable def H1666_cp1 : Nat × Nat := t7val% (fastRun pH1666 1 961 (init pH1666) (init pH1666))
theorem H1666_seg1 : segOK pH1666 1 961 (init pH1666) (init pH1666) H1666_cp1.1 H1666_cp1.2 = true := by
  decide +kernel
noncomputable def H1666_cp2 : Nat × Nat := t7val% (fastRun pH1666 1 1359 (init pH1666) (init pH1666))
theorem H1666_seg2 : segOK pH1666 962 398 H1666_cp1.1 H1666_cp1.2 H1666_cp2.1 H1666_cp2.2 = true := by
  decide +kernel
theorem H1666_fin : (prmOK pH1666 1666 && ptTest pH1666 (runFrom pH1666 (fmask pH1666) (cmask pH1666) (hmask pH1666) 1360 306 (true, H1666_cp2.1, H1666_cp2.2)) 1666 833 true) = true := by
  decide +kernel
theorem H1666_ok : RunOK pH1666 1666 (runFrom pH1666 (fmask pH1666) (cmask pH1666) (hmask pH1666) 1360 306 (true, H1666_cp2.1, H1666_cp2.2)) ∧ ptTest pH1666 (runFrom pH1666 (fmask pH1666) (cmask pH1666) (hmask pH1666) 1360 306 (true, H1666_cp2.1, H1666_cp2.2)) 1666 833 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1666_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1666_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1666_fin) true) H1666_seg1) H1666_seg2) (by decide) rfl H1666_fin ptTest_fst
noncomputable def I1666_cp1 : Nat × Nat := t7val% (fastRun pI1666 1 1177 (init pI1666) (init pI1666))
theorem I1666_seg1 : segOK pI1666 1 1177 (init pI1666) (init pI1666) I1666_cp1.1 I1666_cp1.2 = true := by
  decide +kernel
theorem I1666_fin : (prmOK pI1666 1666 && intTest pI1666 (runFrom pI1666 (fmask pI1666) (cmask pI1666) (hmask pI1666) 1178 488 (true, I1666_cp1.1, I1666_cp1.2)) 1666 21 true) = true := by
  decide +kernel
theorem I1666_ok : RunOK pI1666 1666 (runFrom pI1666 (fmask pI1666) (cmask pI1666) (hmask pI1666) 1178 488 (true, I1666_cp1.1, I1666_cp1.2)) ∧ intTest pI1666 (runFrom pI1666 (fmask pI1666) (cmask pI1666) (hmask pI1666) 1178 488 (true, I1666_cp1.1, I1666_cp1.2)) 1666 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1666_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1666_fin) true) I1666_seg1) (by decide) rfl I1666_fin intTest_fst
theorem link1666 : linkOK pL1666 pH1666 pI1666 = true := by decide +kernel
theorem cvx1666 : ConvexBetweenHumps 1666 :=
  cvx_of L1666_ok H1666_ok I1666_ok link1666 (by decide)
theorem cenlink1666 : cenLinkOK pI1666 1666 = true := by decide +kernel
theorem cen1666 : CenterUniqueMin 1666 ∧ DipHyp 1666 ∧ OnePointHyps 1666 :=
  cen_of L1666_ok H1666_ok I1666_ok link1666 cenlink1666

/-! ### The range -/

theorem cvx_1653_1666 {N : ℕ} (h1 : 1653 ≤ N) (h2 : N ≤ 1666) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1659
  · by_cases h4 : N ≤ 1655
    · by_cases h6 : N ≤ 1653
      · obtain rfl : N = 1653 := by omega
        exact cvx1653
      · by_cases h8 : N ≤ 1654
        · obtain rfl : N = 1654 := by omega
          exact cvx1654
        · obtain rfl : N = 1655 := by omega
          exact cvx1655
    · by_cases h6 : N ≤ 1657
      · by_cases h8 : N ≤ 1656
        · obtain rfl : N = 1656 := by omega
          exact cvx1656
        · obtain rfl : N = 1657 := by omega
          exact cvx1657
      · by_cases h8 : N ≤ 1658
        · obtain rfl : N = 1658 := by omega
          exact cvx1658
        · obtain rfl : N = 1659 := by omega
          exact cvx1659
  · by_cases h4 : N ≤ 1662
    · by_cases h6 : N ≤ 1660
      · obtain rfl : N = 1660 := by omega
        exact cvx1660
      · by_cases h8 : N ≤ 1661
        · obtain rfl : N = 1661 := by omega
          exact cvx1661
        · obtain rfl : N = 1662 := by omega
          exact cvx1662
    · by_cases h6 : N ≤ 1664
      · by_cases h8 : N ≤ 1663
        · obtain rfl : N = 1663 := by omega
          exact cvx1663
        · obtain rfl : N = 1664 := by omega
          exact cvx1664
      · by_cases h8 : N ≤ 1665
        · obtain rfl : N = 1665 := by omega
          exact cvx1665
        · obtain rfl : N = 1666 := by omega
          exact cvx1666

theorem cen_1653_1666 {N : ℕ} (h1 : 1653 ≤ N) (h2 : N ≤ 1666) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1658
  · by_cases h4 : N ≤ 1654
    · obtain rfl : N = 1654 := by omega
      exact cen1654
    · by_cases h6 : N ≤ 1656
      · obtain rfl : N = 1656 := by omega
        exact cen1656
      · obtain rfl : N = 1658 := by omega
        exact cen1658
  · by_cases h4 : N ≤ 1662
    · by_cases h6 : N ≤ 1660
      · obtain rfl : N = 1660 := by omega
        exact cen1660
      · obtain rfl : N = 1662 := by omega
        exact cen1662
    · by_cases h6 : N ≤ 1664
      · obtain rfl : N = 1664 := by omega
        exact cen1664
      · obtain rfl : N = 1666 := by omega
        exact cen1666

end Kagey131.PaperD.T7
