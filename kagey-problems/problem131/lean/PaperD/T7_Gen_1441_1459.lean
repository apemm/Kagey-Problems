import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1441, …, 1459` (generated)

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

/-! ### `N = 1441` -/

def pL1441 : Prm := ⟨80, 38, 39, 1443, 11, 18446744073709551616, 128566152322034648, 128566152322034648⟩
def pH1441 : Prm := ⟨80, 38, 39, 1443, 11, 18446744073709551616, 128567251833662424, 128567251833662424⟩
def pI1441 : Prm := ⟨66, 33, 30, 1443, 11, 18446744073709551616, 128566152322034648, 128567251833662424⟩
noncomputable def L1441_cp1 : Nat × Nat := t7val% (fastRun pL1441 1 1018 (init pL1441) (init pL1441))
theorem L1441_seg1 : segOK pL1441 1 1018 (init pL1441) (init pL1441) L1441_cp1.1 L1441_cp1.2 = true := by
  decide +kernel
theorem L1441_fin : (prmOK pL1441 1441 && ptTest pL1441 (runFrom pL1441 (fmask pL1441) (cmask pL1441) (hmask pL1441) 1019 422 (true, L1441_cp1.1, L1441_cp1.2)) 1441 721 false) = true := by
  decide +kernel
theorem L1441_ok : RunOK pL1441 1441 (runFrom pL1441 (fmask pL1441) (cmask pL1441) (hmask pL1441) 1019 422 (true, L1441_cp1.1, L1441_cp1.2)) ∧ ptTest pL1441 (runFrom pL1441 (fmask pL1441) (cmask pL1441) (hmask pL1441) 1019 422 (true, L1441_cp1.1, L1441_cp1.2)) 1441 721 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1441_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1441_fin) true) L1441_seg1) (by decide) rfl L1441_fin ptTest_fst
noncomputable def H1441_cp1 : Nat × Nat := t7val% (fastRun pH1441 1 1018 (init pH1441) (init pH1441))
theorem H1441_seg1 : segOK pH1441 1 1018 (init pH1441) (init pH1441) H1441_cp1.1 H1441_cp1.2 = true := by
  decide +kernel
theorem H1441_fin : (prmOK pH1441 1441 && ptTest pH1441 (runFrom pH1441 (fmask pH1441) (cmask pH1441) (hmask pH1441) 1019 422 (true, H1441_cp1.1, H1441_cp1.2)) 1441 721 true) = true := by
  decide +kernel
theorem H1441_ok : RunOK pH1441 1441 (runFrom pH1441 (fmask pH1441) (cmask pH1441) (hmask pH1441) 1019 422 (true, H1441_cp1.1, H1441_cp1.2)) ∧ ptTest pH1441 (runFrom pH1441 (fmask pH1441) (cmask pH1441) (hmask pH1441) 1019 422 (true, H1441_cp1.1, H1441_cp1.2)) 1441 721 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1441_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1441_fin) true) H1441_seg1) (by decide) rfl H1441_fin ptTest_fst
noncomputable def I1441_cp1 : Nat × Nat := t7val% (fastRun pI1441 1 1018 (init pI1441) (init pI1441))
theorem I1441_seg1 : segOK pI1441 1 1018 (init pI1441) (init pI1441) I1441_cp1.1 I1441_cp1.2 = true := by
  decide +kernel
theorem I1441_fin : (prmOK pI1441 1441 && intTest pI1441 (runFrom pI1441 (fmask pI1441) (cmask pI1441) (hmask pI1441) 1019 422 (true, I1441_cp1.1, I1441_cp1.2)) 1441 20 false) = true := by
  decide +kernel
theorem I1441_ok : RunOK pI1441 1441 (runFrom pI1441 (fmask pI1441) (cmask pI1441) (hmask pI1441) 1019 422 (true, I1441_cp1.1, I1441_cp1.2)) ∧ intTest pI1441 (runFrom pI1441 (fmask pI1441) (cmask pI1441) (hmask pI1441) 1019 422 (true, I1441_cp1.1, I1441_cp1.2)) 1441 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1441_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1441_fin) true) I1441_seg1) (by decide) rfl I1441_fin intTest_fst
theorem link1441 : linkOK pL1441 pH1441 pI1441 = true := by decide +kernel
theorem cvx1441 : ConvexBetweenHumps 1441 :=
  cvx_of L1441_ok H1441_ok I1441_ok link1441 (by decide)

/-! ### `N = 1442` -/

def pL1442 : Prm := ⟨80, 38, 39, 1444, 11, 18446744073709551616, 128493746369554369, 128493746369554369⟩
def pH1442 : Prm := ⟨80, 38, 39, 1444, 11, 18446744073709551616, 128494845881182145, 128494845881182145⟩
def pI1442 : Prm := ⟨66, 33, 30, 1444, 11, 18446744073709551616, 128493746369554369, 128494845881182145⟩
noncomputable def L1442_cp1 : Nat × Nat := t7val% (fastRun pL1442 1 1019 (init pL1442) (init pL1442))
theorem L1442_seg1 : segOK pL1442 1 1019 (init pL1442) (init pL1442) L1442_cp1.1 L1442_cp1.2 = true := by
  decide +kernel
theorem L1442_fin : (prmOK pL1442 1442 && ptTest pL1442 (runFrom pL1442 (fmask pL1442) (cmask pL1442) (hmask pL1442) 1020 422 (true, L1442_cp1.1, L1442_cp1.2)) 1442 721 false) = true := by
  decide +kernel
theorem L1442_ok : RunOK pL1442 1442 (runFrom pL1442 (fmask pL1442) (cmask pL1442) (hmask pL1442) 1020 422 (true, L1442_cp1.1, L1442_cp1.2)) ∧ ptTest pL1442 (runFrom pL1442 (fmask pL1442) (cmask pL1442) (hmask pL1442) 1020 422 (true, L1442_cp1.1, L1442_cp1.2)) 1442 721 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1442_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1442_fin) true) L1442_seg1) (by decide) rfl L1442_fin ptTest_fst
noncomputable def H1442_cp1 : Nat × Nat := t7val% (fastRun pH1442 1 1019 (init pH1442) (init pH1442))
theorem H1442_seg1 : segOK pH1442 1 1019 (init pH1442) (init pH1442) H1442_cp1.1 H1442_cp1.2 = true := by
  decide +kernel
theorem H1442_fin : (prmOK pH1442 1442 && ptTest pH1442 (runFrom pH1442 (fmask pH1442) (cmask pH1442) (hmask pH1442) 1020 422 (true, H1442_cp1.1, H1442_cp1.2)) 1442 721 true) = true := by
  decide +kernel
theorem H1442_ok : RunOK pH1442 1442 (runFrom pH1442 (fmask pH1442) (cmask pH1442) (hmask pH1442) 1020 422 (true, H1442_cp1.1, H1442_cp1.2)) ∧ ptTest pH1442 (runFrom pH1442 (fmask pH1442) (cmask pH1442) (hmask pH1442) 1020 422 (true, H1442_cp1.1, H1442_cp1.2)) 1442 721 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1442_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1442_fin) true) H1442_seg1) (by decide) rfl H1442_fin ptTest_fst
noncomputable def I1442_cp1 : Nat × Nat := t7val% (fastRun pI1442 1 1019 (init pI1442) (init pI1442))
theorem I1442_seg1 : segOK pI1442 1 1019 (init pI1442) (init pI1442) I1442_cp1.1 I1442_cp1.2 = true := by
  decide +kernel
theorem I1442_fin : (prmOK pI1442 1442 && intTest pI1442 (runFrom pI1442 (fmask pI1442) (cmask pI1442) (hmask pI1442) 1020 422 (true, I1442_cp1.1, I1442_cp1.2)) 1442 20 true) = true := by
  decide +kernel
theorem I1442_ok : RunOK pI1442 1442 (runFrom pI1442 (fmask pI1442) (cmask pI1442) (hmask pI1442) 1020 422 (true, I1442_cp1.1, I1442_cp1.2)) ∧ intTest pI1442 (runFrom pI1442 (fmask pI1442) (cmask pI1442) (hmask pI1442) 1020 422 (true, I1442_cp1.1, I1442_cp1.2)) 1442 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1442_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1442_fin) true) I1442_seg1) (by decide) rfl I1442_fin intTest_fst
theorem link1442 : linkOK pL1442 pH1442 pI1442 = true := by decide +kernel
theorem cvx1442 : ConvexBetweenHumps 1442 :=
  cvx_of L1442_ok H1442_ok I1442_ok link1442 (by decide)
theorem cenlink1442 : cenLinkOK pI1442 1442 = true := by decide +kernel
theorem cen1442 : CenterUniqueMin 1442 ∧ DipHyp 1442 ∧ OnePointHyps 1442 :=
  cen_of L1442_ok H1442_ok I1442_ok link1442 cenlink1442

/-! ### `N = 1443` -/

def pL1443 : Prm := ⟨80, 38, 39, 1445, 11, 18446744073709551616, 128421391367626859, 128421391367626859⟩
def pH1443 : Prm := ⟨80, 38, 39, 1445, 11, 18446744073709551616, 128422490879254635, 128422490879254635⟩
def pI1443 : Prm := ⟨66, 33, 30, 1445, 11, 18446744073709551616, 128421391367626859, 128422490879254635⟩
noncomputable def L1443_cp1 : Nat × Nat := t7val% (fastRun pL1443 1 1019 (init pL1443) (init pL1443))
theorem L1443_seg1 : segOK pL1443 1 1019 (init pL1443) (init pL1443) L1443_cp1.1 L1443_cp1.2 = true := by
  decide +kernel
theorem L1443_fin : (prmOK pL1443 1443 && ptTest pL1443 (runFrom pL1443 (fmask pL1443) (cmask pL1443) (hmask pL1443) 1020 423 (true, L1443_cp1.1, L1443_cp1.2)) 1443 722 false) = true := by
  decide +kernel
theorem L1443_ok : RunOK pL1443 1443 (runFrom pL1443 (fmask pL1443) (cmask pL1443) (hmask pL1443) 1020 423 (true, L1443_cp1.1, L1443_cp1.2)) ∧ ptTest pL1443 (runFrom pL1443 (fmask pL1443) (cmask pL1443) (hmask pL1443) 1020 423 (true, L1443_cp1.1, L1443_cp1.2)) 1443 722 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1443_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1443_fin) true) L1443_seg1) (by decide) rfl L1443_fin ptTest_fst
noncomputable def H1443_cp1 : Nat × Nat := t7val% (fastRun pH1443 1 1019 (init pH1443) (init pH1443))
theorem H1443_seg1 : segOK pH1443 1 1019 (init pH1443) (init pH1443) H1443_cp1.1 H1443_cp1.2 = true := by
  decide +kernel
theorem H1443_fin : (prmOK pH1443 1443 && ptTest pH1443 (runFrom pH1443 (fmask pH1443) (cmask pH1443) (hmask pH1443) 1020 423 (true, H1443_cp1.1, H1443_cp1.2)) 1443 722 true) = true := by
  decide +kernel
theorem H1443_ok : RunOK pH1443 1443 (runFrom pH1443 (fmask pH1443) (cmask pH1443) (hmask pH1443) 1020 423 (true, H1443_cp1.1, H1443_cp1.2)) ∧ ptTest pH1443 (runFrom pH1443 (fmask pH1443) (cmask pH1443) (hmask pH1443) 1020 423 (true, H1443_cp1.1, H1443_cp1.2)) 1443 722 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1443_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1443_fin) true) H1443_seg1) (by decide) rfl H1443_fin ptTest_fst
noncomputable def I1443_cp1 : Nat × Nat := t7val% (fastRun pI1443 1 1019 (init pI1443) (init pI1443))
theorem I1443_seg1 : segOK pI1443 1 1019 (init pI1443) (init pI1443) I1443_cp1.1 I1443_cp1.2 = true := by
  decide +kernel
theorem I1443_fin : (prmOK pI1443 1443 && intTest pI1443 (runFrom pI1443 (fmask pI1443) (cmask pI1443) (hmask pI1443) 1020 423 (true, I1443_cp1.1, I1443_cp1.2)) 1443 20 false) = true := by
  decide +kernel
theorem I1443_ok : RunOK pI1443 1443 (runFrom pI1443 (fmask pI1443) (cmask pI1443) (hmask pI1443) 1020 423 (true, I1443_cp1.1, I1443_cp1.2)) ∧ intTest pI1443 (runFrom pI1443 (fmask pI1443) (cmask pI1443) (hmask pI1443) 1020 423 (true, I1443_cp1.1, I1443_cp1.2)) 1443 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1443_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1443_fin) true) I1443_seg1) (by decide) rfl I1443_fin intTest_fst
theorem link1443 : linkOK pL1443 pH1443 pI1443 = true := by decide +kernel
theorem cvx1443 : ConvexBetweenHumps 1443 :=
  cvx_of L1443_ok H1443_ok I1443_ok link1443 (by decide)

/-! ### `N = 1444` -/

def pL1444 : Prm := ⟨80, 38, 39, 1446, 11, 18446744073709551616, 128349162719052511, 128349162719052511⟩
def pH1444 : Prm := ⟨80, 38, 39, 1446, 11, 18446744073709551616, 128350262230680287, 128350262230680287⟩
def pI1444 : Prm := ⟨66, 33, 30, 1446, 11, 18446744073709551616, 128349162719052511, 128350262230680287⟩
noncomputable def L1444_cp1 : Nat × Nat := t7val% (fastRun pL1444 1 1020 (init pL1444) (init pL1444))
theorem L1444_seg1 : segOK pL1444 1 1020 (init pL1444) (init pL1444) L1444_cp1.1 L1444_cp1.2 = true := by
  decide +kernel
theorem L1444_fin : (prmOK pL1444 1444 && ptTest pL1444 (runFrom pL1444 (fmask pL1444) (cmask pL1444) (hmask pL1444) 1021 423 (true, L1444_cp1.1, L1444_cp1.2)) 1444 722 false) = true := by
  decide +kernel
theorem L1444_ok : RunOK pL1444 1444 (runFrom pL1444 (fmask pL1444) (cmask pL1444) (hmask pL1444) 1021 423 (true, L1444_cp1.1, L1444_cp1.2)) ∧ ptTest pL1444 (runFrom pL1444 (fmask pL1444) (cmask pL1444) (hmask pL1444) 1021 423 (true, L1444_cp1.1, L1444_cp1.2)) 1444 722 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1444_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1444_fin) true) L1444_seg1) (by decide) rfl L1444_fin ptTest_fst
noncomputable def H1444_cp1 : Nat × Nat := t7val% (fastRun pH1444 1 1020 (init pH1444) (init pH1444))
theorem H1444_seg1 : segOK pH1444 1 1020 (init pH1444) (init pH1444) H1444_cp1.1 H1444_cp1.2 = true := by
  decide +kernel
theorem H1444_fin : (prmOK pH1444 1444 && ptTest pH1444 (runFrom pH1444 (fmask pH1444) (cmask pH1444) (hmask pH1444) 1021 423 (true, H1444_cp1.1, H1444_cp1.2)) 1444 722 true) = true := by
  decide +kernel
theorem H1444_ok : RunOK pH1444 1444 (runFrom pH1444 (fmask pH1444) (cmask pH1444) (hmask pH1444) 1021 423 (true, H1444_cp1.1, H1444_cp1.2)) ∧ ptTest pH1444 (runFrom pH1444 (fmask pH1444) (cmask pH1444) (hmask pH1444) 1021 423 (true, H1444_cp1.1, H1444_cp1.2)) 1444 722 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1444_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1444_fin) true) H1444_seg1) (by decide) rfl H1444_fin ptTest_fst
noncomputable def I1444_cp1 : Nat × Nat := t7val% (fastRun pI1444 1 1020 (init pI1444) (init pI1444))
theorem I1444_seg1 : segOK pI1444 1 1020 (init pI1444) (init pI1444) I1444_cp1.1 I1444_cp1.2 = true := by
  decide +kernel
theorem I1444_fin : (prmOK pI1444 1444 && intTest pI1444 (runFrom pI1444 (fmask pI1444) (cmask pI1444) (hmask pI1444) 1021 423 (true, I1444_cp1.1, I1444_cp1.2)) 1444 20 true) = true := by
  decide +kernel
theorem I1444_ok : RunOK pI1444 1444 (runFrom pI1444 (fmask pI1444) (cmask pI1444) (hmask pI1444) 1021 423 (true, I1444_cp1.1, I1444_cp1.2)) ∧ intTest pI1444 (runFrom pI1444 (fmask pI1444) (cmask pI1444) (hmask pI1444) 1021 423 (true, I1444_cp1.1, I1444_cp1.2)) 1444 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1444_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1444_fin) true) I1444_seg1) (by decide) rfl I1444_fin intTest_fst
theorem link1444 : linkOK pL1444 pH1444 pI1444 = true := by decide +kernel
theorem cvx1444 : ConvexBetweenHumps 1444 :=
  cvx_of L1444_ok H1444_ok I1444_ok link1444 (by decide)
theorem cenlink1444 : cenLinkOK pI1444 1444 = true := by decide +kernel
theorem cen1444 : CenterUniqueMin 1444 ∧ DipHyp 1444 ∧ OnePointHyps 1444 :=
  cen_of L1444_ok H1444_ok I1444_ok link1444 cenlink1444

/-! ### `N = 1445` -/

def pL1445 : Prm := ⟨80, 38, 39, 1447, 11, 18446744073709551616, 128276984844218889, 128276984844218889⟩
def pH1445 : Prm := ⟨80, 38, 39, 1447, 11, 18446744073709551616, 128278084355846665, 128278084355846665⟩
def pI1445 : Prm := ⟨66, 33, 30, 1447, 11, 18446744073709551616, 128276984844218889, 128278084355846665⟩
noncomputable def L1445_cp1 : Nat × Nat := t7val% (fastRun pL1445 1 1021 (init pL1445) (init pL1445))
theorem L1445_seg1 : segOK pL1445 1 1021 (init pL1445) (init pL1445) L1445_cp1.1 L1445_cp1.2 = true := by
  decide +kernel
theorem L1445_fin : (prmOK pL1445 1445 && ptTest pL1445 (runFrom pL1445 (fmask pL1445) (cmask pL1445) (hmask pL1445) 1022 423 (true, L1445_cp1.1, L1445_cp1.2)) 1445 723 false) = true := by
  decide +kernel
theorem L1445_ok : RunOK pL1445 1445 (runFrom pL1445 (fmask pL1445) (cmask pL1445) (hmask pL1445) 1022 423 (true, L1445_cp1.1, L1445_cp1.2)) ∧ ptTest pL1445 (runFrom pL1445 (fmask pL1445) (cmask pL1445) (hmask pL1445) 1022 423 (true, L1445_cp1.1, L1445_cp1.2)) 1445 723 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1445_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1445_fin) true) L1445_seg1) (by decide) rfl L1445_fin ptTest_fst
noncomputable def H1445_cp1 : Nat × Nat := t7val% (fastRun pH1445 1 1021 (init pH1445) (init pH1445))
theorem H1445_seg1 : segOK pH1445 1 1021 (init pH1445) (init pH1445) H1445_cp1.1 H1445_cp1.2 = true := by
  decide +kernel
theorem H1445_fin : (prmOK pH1445 1445 && ptTest pH1445 (runFrom pH1445 (fmask pH1445) (cmask pH1445) (hmask pH1445) 1022 423 (true, H1445_cp1.1, H1445_cp1.2)) 1445 723 true) = true := by
  decide +kernel
theorem H1445_ok : RunOK pH1445 1445 (runFrom pH1445 (fmask pH1445) (cmask pH1445) (hmask pH1445) 1022 423 (true, H1445_cp1.1, H1445_cp1.2)) ∧ ptTest pH1445 (runFrom pH1445 (fmask pH1445) (cmask pH1445) (hmask pH1445) 1022 423 (true, H1445_cp1.1, H1445_cp1.2)) 1445 723 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1445_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1445_fin) true) H1445_seg1) (by decide) rfl H1445_fin ptTest_fst
noncomputable def I1445_cp1 : Nat × Nat := t7val% (fastRun pI1445 1 1021 (init pI1445) (init pI1445))
theorem I1445_seg1 : segOK pI1445 1 1021 (init pI1445) (init pI1445) I1445_cp1.1 I1445_cp1.2 = true := by
  decide +kernel
theorem I1445_fin : (prmOK pI1445 1445 && intTest pI1445 (runFrom pI1445 (fmask pI1445) (cmask pI1445) (hmask pI1445) 1022 423 (true, I1445_cp1.1, I1445_cp1.2)) 1445 20 false) = true := by
  decide +kernel
theorem I1445_ok : RunOK pI1445 1445 (runFrom pI1445 (fmask pI1445) (cmask pI1445) (hmask pI1445) 1022 423 (true, I1445_cp1.1, I1445_cp1.2)) ∧ intTest pI1445 (runFrom pI1445 (fmask pI1445) (cmask pI1445) (hmask pI1445) 1022 423 (true, I1445_cp1.1, I1445_cp1.2)) 1445 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1445_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1445_fin) true) I1445_seg1) (by decide) rfl I1445_fin intTest_fst
theorem link1445 : linkOK pL1445 pH1445 pI1445 = true := by decide +kernel
theorem cvx1445 : ConvexBetweenHumps 1445 :=
  cvx_of L1445_ok H1445_ok I1445_ok link1445 (by decide)

/-! ### `N = 1446` -/

def pL1446 : Prm := ⟨80, 38, 39, 1448, 11, 18446744073709551616, 128204932828181221, 128204932828181221⟩
def pH1446 : Prm := ⟨80, 38, 39, 1448, 11, 18446744073709551616, 128206032339808997, 128206032339808997⟩
def pI1446 : Prm := ⟨66, 33, 30, 1448, 11, 18446744073709551616, 128204932828181221, 128206032339808997⟩
noncomputable def L1446_cp1 : Nat × Nat := t7val% (fastRun pL1446 1 1021 (init pL1446) (init pL1446))
theorem L1446_seg1 : segOK pL1446 1 1021 (init pL1446) (init pL1446) L1446_cp1.1 L1446_cp1.2 = true := by
  decide +kernel
theorem L1446_fin : (prmOK pL1446 1446 && ptTest pL1446 (runFrom pL1446 (fmask pL1446) (cmask pL1446) (hmask pL1446) 1022 424 (true, L1446_cp1.1, L1446_cp1.2)) 1446 723 false) = true := by
  decide +kernel
theorem L1446_ok : RunOK pL1446 1446 (runFrom pL1446 (fmask pL1446) (cmask pL1446) (hmask pL1446) 1022 424 (true, L1446_cp1.1, L1446_cp1.2)) ∧ ptTest pL1446 (runFrom pL1446 (fmask pL1446) (cmask pL1446) (hmask pL1446) 1022 424 (true, L1446_cp1.1, L1446_cp1.2)) 1446 723 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1446_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1446_fin) true) L1446_seg1) (by decide) rfl L1446_fin ptTest_fst
noncomputable def H1446_cp1 : Nat × Nat := t7val% (fastRun pH1446 1 1021 (init pH1446) (init pH1446))
theorem H1446_seg1 : segOK pH1446 1 1021 (init pH1446) (init pH1446) H1446_cp1.1 H1446_cp1.2 = true := by
  decide +kernel
theorem H1446_fin : (prmOK pH1446 1446 && ptTest pH1446 (runFrom pH1446 (fmask pH1446) (cmask pH1446) (hmask pH1446) 1022 424 (true, H1446_cp1.1, H1446_cp1.2)) 1446 723 true) = true := by
  decide +kernel
theorem H1446_ok : RunOK pH1446 1446 (runFrom pH1446 (fmask pH1446) (cmask pH1446) (hmask pH1446) 1022 424 (true, H1446_cp1.1, H1446_cp1.2)) ∧ ptTest pH1446 (runFrom pH1446 (fmask pH1446) (cmask pH1446) (hmask pH1446) 1022 424 (true, H1446_cp1.1, H1446_cp1.2)) 1446 723 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1446_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1446_fin) true) H1446_seg1) (by decide) rfl H1446_fin ptTest_fst
noncomputable def I1446_cp1 : Nat × Nat := t7val% (fastRun pI1446 1 1021 (init pI1446) (init pI1446))
theorem I1446_seg1 : segOK pI1446 1 1021 (init pI1446) (init pI1446) I1446_cp1.1 I1446_cp1.2 = true := by
  decide +kernel
theorem I1446_fin : (prmOK pI1446 1446 && intTest pI1446 (runFrom pI1446 (fmask pI1446) (cmask pI1446) (hmask pI1446) 1022 424 (true, I1446_cp1.1, I1446_cp1.2)) 1446 20 true) = true := by
  decide +kernel
theorem I1446_ok : RunOK pI1446 1446 (runFrom pI1446 (fmask pI1446) (cmask pI1446) (hmask pI1446) 1022 424 (true, I1446_cp1.1, I1446_cp1.2)) ∧ intTest pI1446 (runFrom pI1446 (fmask pI1446) (cmask pI1446) (hmask pI1446) 1022 424 (true, I1446_cp1.1, I1446_cp1.2)) 1446 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1446_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1446_fin) true) I1446_seg1) (by decide) rfl I1446_fin intTest_fst
theorem link1446 : linkOK pL1446 pH1446 pI1446 = true := by decide +kernel
theorem cvx1446 : ConvexBetweenHumps 1446 :=
  cvx_of L1446_ok H1446_ok I1446_ok link1446 (by decide)
theorem cenlink1446 : cenLinkOK pI1446 1446 = true := by decide +kernel
theorem cen1446 : CenterUniqueMin 1446 ∧ DipHyp 1446 ∧ OnePointHyps 1446 :=
  cen_of L1446_ok H1446_ok I1446_ok link1446 cenlink1446

/-! ### `N = 1447` -/

def pL1447 : Prm := ⟨80, 38, 39, 1449, 11, 18446744073709551616, 128132931409939234, 128132931409939234⟩
def pH1447 : Prm := ⟨80, 38, 39, 1449, 11, 18446744073709551616, 128134030921567010, 128134030921567010⟩
def pI1447 : Prm := ⟨66, 33, 30, 1449, 11, 18446744073709551616, 128132931409939234, 128134030921567010⟩
noncomputable def L1447_cp1 : Nat × Nat := t7val% (fastRun pL1447 1 1022 (init pL1447) (init pL1447))
theorem L1447_seg1 : segOK pL1447 1 1022 (init pL1447) (init pL1447) L1447_cp1.1 L1447_cp1.2 = true := by
  decide +kernel
theorem L1447_fin : (prmOK pL1447 1447 && ptTest pL1447 (runFrom pL1447 (fmask pL1447) (cmask pL1447) (hmask pL1447) 1023 424 (true, L1447_cp1.1, L1447_cp1.2)) 1447 724 false) = true := by
  decide +kernel
theorem L1447_ok : RunOK pL1447 1447 (runFrom pL1447 (fmask pL1447) (cmask pL1447) (hmask pL1447) 1023 424 (true, L1447_cp1.1, L1447_cp1.2)) ∧ ptTest pL1447 (runFrom pL1447 (fmask pL1447) (cmask pL1447) (hmask pL1447) 1023 424 (true, L1447_cp1.1, L1447_cp1.2)) 1447 724 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1447_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1447_fin) true) L1447_seg1) (by decide) rfl L1447_fin ptTest_fst
noncomputable def H1447_cp1 : Nat × Nat := t7val% (fastRun pH1447 1 1022 (init pH1447) (init pH1447))
theorem H1447_seg1 : segOK pH1447 1 1022 (init pH1447) (init pH1447) H1447_cp1.1 H1447_cp1.2 = true := by
  decide +kernel
theorem H1447_fin : (prmOK pH1447 1447 && ptTest pH1447 (runFrom pH1447 (fmask pH1447) (cmask pH1447) (hmask pH1447) 1023 424 (true, H1447_cp1.1, H1447_cp1.2)) 1447 724 true) = true := by
  decide +kernel
theorem H1447_ok : RunOK pH1447 1447 (runFrom pH1447 (fmask pH1447) (cmask pH1447) (hmask pH1447) 1023 424 (true, H1447_cp1.1, H1447_cp1.2)) ∧ ptTest pH1447 (runFrom pH1447 (fmask pH1447) (cmask pH1447) (hmask pH1447) 1023 424 (true, H1447_cp1.1, H1447_cp1.2)) 1447 724 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1447_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1447_fin) true) H1447_seg1) (by decide) rfl H1447_fin ptTest_fst
noncomputable def I1447_cp1 : Nat × Nat := t7val% (fastRun pI1447 1 1022 (init pI1447) (init pI1447))
theorem I1447_seg1 : segOK pI1447 1 1022 (init pI1447) (init pI1447) I1447_cp1.1 I1447_cp1.2 = true := by
  decide +kernel
theorem I1447_fin : (prmOK pI1447 1447 && intTest pI1447 (runFrom pI1447 (fmask pI1447) (cmask pI1447) (hmask pI1447) 1023 424 (true, I1447_cp1.1, I1447_cp1.2)) 1447 20 false) = true := by
  decide +kernel
theorem I1447_ok : RunOK pI1447 1447 (runFrom pI1447 (fmask pI1447) (cmask pI1447) (hmask pI1447) 1023 424 (true, I1447_cp1.1, I1447_cp1.2)) ∧ intTest pI1447 (runFrom pI1447 (fmask pI1447) (cmask pI1447) (hmask pI1447) 1023 424 (true, I1447_cp1.1, I1447_cp1.2)) 1447 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1447_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1447_fin) true) I1447_seg1) (by decide) rfl I1447_fin intTest_fst
theorem link1447 : linkOK pL1447 pH1447 pI1447 = true := by decide +kernel
theorem cvx1447 : ConvexBetweenHumps 1447 :=
  cvx_of L1447_ok H1447_ok I1447_ok link1447 (by decide)

/-! ### `N = 1448` -/

def pL1448 : Prm := ⟨80, 38, 39, 1450, 11, 18446744073709551616, 128061055358573876, 128061055358573876⟩
def pH1448 : Prm := ⟨80, 38, 39, 1450, 11, 18446744073709551616, 128062154870201652, 128062154870201652⟩
def pI1448 : Prm := ⟨66, 33, 30, 1450, 11, 18446744073709551616, 128061055358573876, 128062154870201652⟩
noncomputable def L1448_cp1 : Nat × Nat := t7val% (fastRun pL1448 1 1023 (init pL1448) (init pL1448))
theorem L1448_seg1 : segOK pL1448 1 1023 (init pL1448) (init pL1448) L1448_cp1.1 L1448_cp1.2 = true := by
  decide +kernel
theorem L1448_fin : (prmOK pL1448 1448 && ptTest pL1448 (runFrom pL1448 (fmask pL1448) (cmask pL1448) (hmask pL1448) 1024 424 (true, L1448_cp1.1, L1448_cp1.2)) 1448 724 false) = true := by
  decide +kernel
theorem L1448_ok : RunOK pL1448 1448 (runFrom pL1448 (fmask pL1448) (cmask pL1448) (hmask pL1448) 1024 424 (true, L1448_cp1.1, L1448_cp1.2)) ∧ ptTest pL1448 (runFrom pL1448 (fmask pL1448) (cmask pL1448) (hmask pL1448) 1024 424 (true, L1448_cp1.1, L1448_cp1.2)) 1448 724 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1448_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1448_fin) true) L1448_seg1) (by decide) rfl L1448_fin ptTest_fst
noncomputable def H1448_cp1 : Nat × Nat := t7val% (fastRun pH1448 1 1023 (init pH1448) (init pH1448))
theorem H1448_seg1 : segOK pH1448 1 1023 (init pH1448) (init pH1448) H1448_cp1.1 H1448_cp1.2 = true := by
  decide +kernel
theorem H1448_fin : (prmOK pH1448 1448 && ptTest pH1448 (runFrom pH1448 (fmask pH1448) (cmask pH1448) (hmask pH1448) 1024 424 (true, H1448_cp1.1, H1448_cp1.2)) 1448 724 true) = true := by
  decide +kernel
theorem H1448_ok : RunOK pH1448 1448 (runFrom pH1448 (fmask pH1448) (cmask pH1448) (hmask pH1448) 1024 424 (true, H1448_cp1.1, H1448_cp1.2)) ∧ ptTest pH1448 (runFrom pH1448 (fmask pH1448) (cmask pH1448) (hmask pH1448) 1024 424 (true, H1448_cp1.1, H1448_cp1.2)) 1448 724 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1448_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1448_fin) true) H1448_seg1) (by decide) rfl H1448_fin ptTest_fst
noncomputable def I1448_cp1 : Nat × Nat := t7val% (fastRun pI1448 1 1023 (init pI1448) (init pI1448))
theorem I1448_seg1 : segOK pI1448 1 1023 (init pI1448) (init pI1448) I1448_cp1.1 I1448_cp1.2 = true := by
  decide +kernel
theorem I1448_fin : (prmOK pI1448 1448 && intTest pI1448 (runFrom pI1448 (fmask pI1448) (cmask pI1448) (hmask pI1448) 1024 424 (true, I1448_cp1.1, I1448_cp1.2)) 1448 20 true) = true := by
  decide +kernel
theorem I1448_ok : RunOK pI1448 1448 (runFrom pI1448 (fmask pI1448) (cmask pI1448) (hmask pI1448) 1024 424 (true, I1448_cp1.1, I1448_cp1.2)) ∧ intTest pI1448 (runFrom pI1448 (fmask pI1448) (cmask pI1448) (hmask pI1448) 1024 424 (true, I1448_cp1.1, I1448_cp1.2)) 1448 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1448_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1448_fin) true) I1448_seg1) (by decide) rfl I1448_fin intTest_fst
theorem link1448 : linkOK pL1448 pH1448 pI1448 = true := by decide +kernel
theorem cvx1448 : ConvexBetweenHumps 1448 :=
  cvx_of L1448_ok H1448_ok I1448_ok link1448 (by decide)
theorem cenlink1448 : cenLinkOK pI1448 1448 = true := by decide +kernel
theorem cen1448 : CenterUniqueMin 1448 ∧ DipHyp 1448 ∧ OnePointHyps 1448 :=
  cen_of L1448_ok H1448_ok I1448_ok link1448 cenlink1448

/-! ### `N = 1449` -/

def pL1449 : Prm := ⟨80, 38, 39, 1451, 11, 18446744073709551616, 127989229729833918, 127989229729833918⟩
def pH1449 : Prm := ⟨80, 38, 39, 1451, 11, 18446744073709551616, 127990329241461694, 127990329241461694⟩
def pI1449 : Prm := ⟨66, 33, 30, 1451, 11, 18446744073709551616, 127989229729833918, 127990329241461694⟩
noncomputable def L1449_cp1 : Nat × Nat := t7val% (fastRun pL1449 1 1024 (init pL1449) (init pL1449))
theorem L1449_seg1 : segOK pL1449 1 1024 (init pL1449) (init pL1449) L1449_cp1.1 L1449_cp1.2 = true := by
  decide +kernel
theorem L1449_fin : (prmOK pL1449 1449 && ptTest pL1449 (runFrom pL1449 (fmask pL1449) (cmask pL1449) (hmask pL1449) 1025 424 (true, L1449_cp1.1, L1449_cp1.2)) 1449 725 false) = true := by
  decide +kernel
theorem L1449_ok : RunOK pL1449 1449 (runFrom pL1449 (fmask pL1449) (cmask pL1449) (hmask pL1449) 1025 424 (true, L1449_cp1.1, L1449_cp1.2)) ∧ ptTest pL1449 (runFrom pL1449 (fmask pL1449) (cmask pL1449) (hmask pL1449) 1025 424 (true, L1449_cp1.1, L1449_cp1.2)) 1449 725 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1449_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1449_fin) true) L1449_seg1) (by decide) rfl L1449_fin ptTest_fst
noncomputable def H1449_cp1 : Nat × Nat := t7val% (fastRun pH1449 1 1024 (init pH1449) (init pH1449))
theorem H1449_seg1 : segOK pH1449 1 1024 (init pH1449) (init pH1449) H1449_cp1.1 H1449_cp1.2 = true := by
  decide +kernel
theorem H1449_fin : (prmOK pH1449 1449 && ptTest pH1449 (runFrom pH1449 (fmask pH1449) (cmask pH1449) (hmask pH1449) 1025 424 (true, H1449_cp1.1, H1449_cp1.2)) 1449 725 true) = true := by
  decide +kernel
theorem H1449_ok : RunOK pH1449 1449 (runFrom pH1449 (fmask pH1449) (cmask pH1449) (hmask pH1449) 1025 424 (true, H1449_cp1.1, H1449_cp1.2)) ∧ ptTest pH1449 (runFrom pH1449 (fmask pH1449) (cmask pH1449) (hmask pH1449) 1025 424 (true, H1449_cp1.1, H1449_cp1.2)) 1449 725 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1449_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1449_fin) true) H1449_seg1) (by decide) rfl H1449_fin ptTest_fst
noncomputable def I1449_cp1 : Nat × Nat := t7val% (fastRun pI1449 1 1024 (init pI1449) (init pI1449))
theorem I1449_seg1 : segOK pI1449 1 1024 (init pI1449) (init pI1449) I1449_cp1.1 I1449_cp1.2 = true := by
  decide +kernel
theorem I1449_fin : (prmOK pI1449 1449 && intTest pI1449 (runFrom pI1449 (fmask pI1449) (cmask pI1449) (hmask pI1449) 1025 424 (true, I1449_cp1.1, I1449_cp1.2)) 1449 20 false) = true := by
  decide +kernel
theorem I1449_ok : RunOK pI1449 1449 (runFrom pI1449 (fmask pI1449) (cmask pI1449) (hmask pI1449) 1025 424 (true, I1449_cp1.1, I1449_cp1.2)) ∧ intTest pI1449 (runFrom pI1449 (fmask pI1449) (cmask pI1449) (hmask pI1449) 1025 424 (true, I1449_cp1.1, I1449_cp1.2)) 1449 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1449_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1449_fin) true) I1449_seg1) (by decide) rfl I1449_fin intTest_fst
theorem link1449 : linkOK pL1449 pH1449 pI1449 = true := by decide +kernel
theorem cvx1449 : ConvexBetweenHumps 1449 :=
  cvx_of L1449_ok H1449_ok I1449_ok link1449 (by decide)

/-! ### `N = 1450` -/

def pL1450 : Prm := ⟨80, 38, 39, 1452, 11, 18446744073709551616, 127917528978652257, 127917528978652257⟩
def pH1450 : Prm := ⟨80, 38, 39, 1452, 11, 18446744073709551616, 127918628490280033, 127918628490280033⟩
def pI1450 : Prm := ⟨66, 33, 30, 1452, 11, 18446744073709551616, 127917528978652257, 127918628490280033⟩
noncomputable def L1450_cp1 : Nat × Nat := t7val% (fastRun pL1450 1 1024 (init pL1450) (init pL1450))
theorem L1450_seg1 : segOK pL1450 1 1024 (init pL1450) (init pL1450) L1450_cp1.1 L1450_cp1.2 = true := by
  decide +kernel
theorem L1450_fin : (prmOK pL1450 1450 && ptTest pL1450 (runFrom pL1450 (fmask pL1450) (cmask pL1450) (hmask pL1450) 1025 425 (true, L1450_cp1.1, L1450_cp1.2)) 1450 725 false) = true := by
  decide +kernel
theorem L1450_ok : RunOK pL1450 1450 (runFrom pL1450 (fmask pL1450) (cmask pL1450) (hmask pL1450) 1025 425 (true, L1450_cp1.1, L1450_cp1.2)) ∧ ptTest pL1450 (runFrom pL1450 (fmask pL1450) (cmask pL1450) (hmask pL1450) 1025 425 (true, L1450_cp1.1, L1450_cp1.2)) 1450 725 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1450_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1450_fin) true) L1450_seg1) (by decide) rfl L1450_fin ptTest_fst
noncomputable def H1450_cp1 : Nat × Nat := t7val% (fastRun pH1450 1 1024 (init pH1450) (init pH1450))
theorem H1450_seg1 : segOK pH1450 1 1024 (init pH1450) (init pH1450) H1450_cp1.1 H1450_cp1.2 = true := by
  decide +kernel
theorem H1450_fin : (prmOK pH1450 1450 && ptTest pH1450 (runFrom pH1450 (fmask pH1450) (cmask pH1450) (hmask pH1450) 1025 425 (true, H1450_cp1.1, H1450_cp1.2)) 1450 725 true) = true := by
  decide +kernel
theorem H1450_ok : RunOK pH1450 1450 (runFrom pH1450 (fmask pH1450) (cmask pH1450) (hmask pH1450) 1025 425 (true, H1450_cp1.1, H1450_cp1.2)) ∧ ptTest pH1450 (runFrom pH1450 (fmask pH1450) (cmask pH1450) (hmask pH1450) 1025 425 (true, H1450_cp1.1, H1450_cp1.2)) 1450 725 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1450_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1450_fin) true) H1450_seg1) (by decide) rfl H1450_fin ptTest_fst
noncomputable def I1450_cp1 : Nat × Nat := t7val% (fastRun pI1450 1 1024 (init pI1450) (init pI1450))
theorem I1450_seg1 : segOK pI1450 1 1024 (init pI1450) (init pI1450) I1450_cp1.1 I1450_cp1.2 = true := by
  decide +kernel
theorem I1450_fin : (prmOK pI1450 1450 && intTest pI1450 (runFrom pI1450 (fmask pI1450) (cmask pI1450) (hmask pI1450) 1025 425 (true, I1450_cp1.1, I1450_cp1.2)) 1450 20 true) = true := by
  decide +kernel
theorem I1450_ok : RunOK pI1450 1450 (runFrom pI1450 (fmask pI1450) (cmask pI1450) (hmask pI1450) 1025 425 (true, I1450_cp1.1, I1450_cp1.2)) ∧ intTest pI1450 (runFrom pI1450 (fmask pI1450) (cmask pI1450) (hmask pI1450) 1025 425 (true, I1450_cp1.1, I1450_cp1.2)) 1450 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1450_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1450_fin) true) I1450_seg1) (by decide) rfl I1450_fin intTest_fst
theorem link1450 : linkOK pL1450 pH1450 pI1450 = true := by decide +kernel
theorem cvx1450 : ConvexBetweenHumps 1450 :=
  cvx_of L1450_ok H1450_ok I1450_ok link1450 (by decide)
theorem cenlink1450 : cenLinkOK pI1450 1450 = true := by decide +kernel
theorem cen1450 : CenterUniqueMin 1450 ∧ DipHyp 1450 ∧ OnePointHyps 1450 :=
  cen_of L1450_ok H1450_ok I1450_ok link1450 cenlink1450

/-! ### `N = 1451` -/

def pL1451 : Prm := ⟨80, 38, 39, 1453, 11, 18446744073709551616, 127845878475792709, 127845878475792709⟩
def pH1451 : Prm := ⟨80, 38, 39, 1453, 11, 18446744073709551616, 127846977987420485, 127846977987420485⟩
def pI1451 : Prm := ⟨66, 33, 30, 1453, 11, 18446744073709551616, 127845878475792709, 127846977987420485⟩
noncomputable def L1451_cp1 : Nat × Nat := t7val% (fastRun pL1451 1 1025 (init pL1451) (init pL1451))
theorem L1451_seg1 : segOK pL1451 1 1025 (init pL1451) (init pL1451) L1451_cp1.1 L1451_cp1.2 = true := by
  decide +kernel
theorem L1451_fin : (prmOK pL1451 1451 && ptTest pL1451 (runFrom pL1451 (fmask pL1451) (cmask pL1451) (hmask pL1451) 1026 425 (true, L1451_cp1.1, L1451_cp1.2)) 1451 726 false) = true := by
  decide +kernel
theorem L1451_ok : RunOK pL1451 1451 (runFrom pL1451 (fmask pL1451) (cmask pL1451) (hmask pL1451) 1026 425 (true, L1451_cp1.1, L1451_cp1.2)) ∧ ptTest pL1451 (runFrom pL1451 (fmask pL1451) (cmask pL1451) (hmask pL1451) 1026 425 (true, L1451_cp1.1, L1451_cp1.2)) 1451 726 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1451_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1451_fin) true) L1451_seg1) (by decide) rfl L1451_fin ptTest_fst
noncomputable def H1451_cp1 : Nat × Nat := t7val% (fastRun pH1451 1 1025 (init pH1451) (init pH1451))
theorem H1451_seg1 : segOK pH1451 1 1025 (init pH1451) (init pH1451) H1451_cp1.1 H1451_cp1.2 = true := by
  decide +kernel
theorem H1451_fin : (prmOK pH1451 1451 && ptTest pH1451 (runFrom pH1451 (fmask pH1451) (cmask pH1451) (hmask pH1451) 1026 425 (true, H1451_cp1.1, H1451_cp1.2)) 1451 726 true) = true := by
  decide +kernel
theorem H1451_ok : RunOK pH1451 1451 (runFrom pH1451 (fmask pH1451) (cmask pH1451) (hmask pH1451) 1026 425 (true, H1451_cp1.1, H1451_cp1.2)) ∧ ptTest pH1451 (runFrom pH1451 (fmask pH1451) (cmask pH1451) (hmask pH1451) 1026 425 (true, H1451_cp1.1, H1451_cp1.2)) 1451 726 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1451_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1451_fin) true) H1451_seg1) (by decide) rfl H1451_fin ptTest_fst
noncomputable def I1451_cp1 : Nat × Nat := t7val% (fastRun pI1451 1 1025 (init pI1451) (init pI1451))
theorem I1451_seg1 : segOK pI1451 1 1025 (init pI1451) (init pI1451) I1451_cp1.1 I1451_cp1.2 = true := by
  decide +kernel
theorem I1451_fin : (prmOK pI1451 1451 && intTest pI1451 (runFrom pI1451 (fmask pI1451) (cmask pI1451) (hmask pI1451) 1026 425 (true, I1451_cp1.1, I1451_cp1.2)) 1451 20 false) = true := by
  decide +kernel
theorem I1451_ok : RunOK pI1451 1451 (runFrom pI1451 (fmask pI1451) (cmask pI1451) (hmask pI1451) 1026 425 (true, I1451_cp1.1, I1451_cp1.2)) ∧ intTest pI1451 (runFrom pI1451 (fmask pI1451) (cmask pI1451) (hmask pI1451) 1026 425 (true, I1451_cp1.1, I1451_cp1.2)) 1451 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1451_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1451_fin) true) I1451_seg1) (by decide) rfl I1451_fin intTest_fst
theorem link1451 : linkOK pL1451 pH1451 pI1451 = true := by decide +kernel
theorem cvx1451 : ConvexBetweenHumps 1451 :=
  cvx_of L1451_ok H1451_ok I1451_ok link1451 (by decide)

/-! ### `N = 1452` -/

def pL1452 : Prm := ⟨80, 38, 39, 1454, 11, 18446744073709551616, 127774352363718776, 127774352363718776⟩
def pH1452 : Prm := ⟨80, 38, 39, 1454, 11, 18446744073709551616, 127775451875346552, 127775451875346552⟩
def pI1452 : Prm := ⟨66, 33, 30, 1454, 11, 18446744073709551616, 127774352363718776, 127775451875346552⟩
noncomputable def L1452_cp1 : Nat × Nat := t7val% (fastRun pL1452 1 1026 (init pL1452) (init pL1452))
theorem L1452_seg1 : segOK pL1452 1 1026 (init pL1452) (init pL1452) L1452_cp1.1 L1452_cp1.2 = true := by
  decide +kernel
theorem L1452_fin : (prmOK pL1452 1452 && ptTest pL1452 (runFrom pL1452 (fmask pL1452) (cmask pL1452) (hmask pL1452) 1027 425 (true, L1452_cp1.1, L1452_cp1.2)) 1452 726 false) = true := by
  decide +kernel
theorem L1452_ok : RunOK pL1452 1452 (runFrom pL1452 (fmask pL1452) (cmask pL1452) (hmask pL1452) 1027 425 (true, L1452_cp1.1, L1452_cp1.2)) ∧ ptTest pL1452 (runFrom pL1452 (fmask pL1452) (cmask pL1452) (hmask pL1452) 1027 425 (true, L1452_cp1.1, L1452_cp1.2)) 1452 726 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1452_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1452_fin) true) L1452_seg1) (by decide) rfl L1452_fin ptTest_fst
noncomputable def H1452_cp1 : Nat × Nat := t7val% (fastRun pH1452 1 1026 (init pH1452) (init pH1452))
theorem H1452_seg1 : segOK pH1452 1 1026 (init pH1452) (init pH1452) H1452_cp1.1 H1452_cp1.2 = true := by
  decide +kernel
theorem H1452_fin : (prmOK pH1452 1452 && ptTest pH1452 (runFrom pH1452 (fmask pH1452) (cmask pH1452) (hmask pH1452) 1027 425 (true, H1452_cp1.1, H1452_cp1.2)) 1452 726 true) = true := by
  decide +kernel
theorem H1452_ok : RunOK pH1452 1452 (runFrom pH1452 (fmask pH1452) (cmask pH1452) (hmask pH1452) 1027 425 (true, H1452_cp1.1, H1452_cp1.2)) ∧ ptTest pH1452 (runFrom pH1452 (fmask pH1452) (cmask pH1452) (hmask pH1452) 1027 425 (true, H1452_cp1.1, H1452_cp1.2)) 1452 726 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1452_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1452_fin) true) H1452_seg1) (by decide) rfl H1452_fin ptTest_fst
noncomputable def I1452_cp1 : Nat × Nat := t7val% (fastRun pI1452 1 1026 (init pI1452) (init pI1452))
theorem I1452_seg1 : segOK pI1452 1 1026 (init pI1452) (init pI1452) I1452_cp1.1 I1452_cp1.2 = true := by
  decide +kernel
theorem I1452_fin : (prmOK pI1452 1452 && intTest pI1452 (runFrom pI1452 (fmask pI1452) (cmask pI1452) (hmask pI1452) 1027 425 (true, I1452_cp1.1, I1452_cp1.2)) 1452 20 true) = true := by
  decide +kernel
theorem I1452_ok : RunOK pI1452 1452 (runFrom pI1452 (fmask pI1452) (cmask pI1452) (hmask pI1452) 1027 425 (true, I1452_cp1.1, I1452_cp1.2)) ∧ intTest pI1452 (runFrom pI1452 (fmask pI1452) (cmask pI1452) (hmask pI1452) 1027 425 (true, I1452_cp1.1, I1452_cp1.2)) 1452 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1452_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1452_fin) true) I1452_seg1) (by decide) rfl I1452_fin intTest_fst
theorem link1452 : linkOK pL1452 pH1452 pI1452 = true := by decide +kernel
theorem cvx1452 : ConvexBetweenHumps 1452 :=
  cvx_of L1452_ok H1452_ok I1452_ok link1452 (by decide)
theorem cenlink1452 : cenLinkOK pI1452 1452 = true := by decide +kernel
theorem cen1452 : CenterUniqueMin 1452 ∧ DipHyp 1452 ∧ OnePointHyps 1452 :=
  cen_of L1452_ok H1452_ok I1452_ok link1452 cenlink1452

/-! ### `N = 1453` -/

def pL1453 : Prm := ⟨80, 38, 39, 1455, 11, 18446744073709551616, 127702876326456883, 127702876326456883⟩
def pH1453 : Prm := ⟨80, 38, 39, 1455, 11, 18446744073709551616, 127703975838084659, 127703975838084659⟩
def pI1453 : Prm := ⟨66, 33, 30, 1455, 11, 18446744073709551616, 127702876326456883, 127703975838084659⟩
noncomputable def L1453_cp1 : Nat × Nat := t7val% (fastRun pL1453 1 1026 (init pL1453) (init pL1453))
theorem L1453_seg1 : segOK pL1453 1 1026 (init pL1453) (init pL1453) L1453_cp1.1 L1453_cp1.2 = true := by
  decide +kernel
theorem L1453_fin : (prmOK pL1453 1453 && ptTest pL1453 (runFrom pL1453 (fmask pL1453) (cmask pL1453) (hmask pL1453) 1027 426 (true, L1453_cp1.1, L1453_cp1.2)) 1453 727 false) = true := by
  decide +kernel
theorem L1453_ok : RunOK pL1453 1453 (runFrom pL1453 (fmask pL1453) (cmask pL1453) (hmask pL1453) 1027 426 (true, L1453_cp1.1, L1453_cp1.2)) ∧ ptTest pL1453 (runFrom pL1453 (fmask pL1453) (cmask pL1453) (hmask pL1453) 1027 426 (true, L1453_cp1.1, L1453_cp1.2)) 1453 727 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1453_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1453_fin) true) L1453_seg1) (by decide) rfl L1453_fin ptTest_fst
noncomputable def H1453_cp1 : Nat × Nat := t7val% (fastRun pH1453 1 1026 (init pH1453) (init pH1453))
theorem H1453_seg1 : segOK pH1453 1 1026 (init pH1453) (init pH1453) H1453_cp1.1 H1453_cp1.2 = true := by
  decide +kernel
theorem H1453_fin : (prmOK pH1453 1453 && ptTest pH1453 (runFrom pH1453 (fmask pH1453) (cmask pH1453) (hmask pH1453) 1027 426 (true, H1453_cp1.1, H1453_cp1.2)) 1453 727 true) = true := by
  decide +kernel
theorem H1453_ok : RunOK pH1453 1453 (runFrom pH1453 (fmask pH1453) (cmask pH1453) (hmask pH1453) 1027 426 (true, H1453_cp1.1, H1453_cp1.2)) ∧ ptTest pH1453 (runFrom pH1453 (fmask pH1453) (cmask pH1453) (hmask pH1453) 1027 426 (true, H1453_cp1.1, H1453_cp1.2)) 1453 727 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1453_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1453_fin) true) H1453_seg1) (by decide) rfl H1453_fin ptTest_fst
noncomputable def I1453_cp1 : Nat × Nat := t7val% (fastRun pI1453 1 1026 (init pI1453) (init pI1453))
theorem I1453_seg1 : segOK pI1453 1 1026 (init pI1453) (init pI1453) I1453_cp1.1 I1453_cp1.2 = true := by
  decide +kernel
theorem I1453_fin : (prmOK pI1453 1453 && intTest pI1453 (runFrom pI1453 (fmask pI1453) (cmask pI1453) (hmask pI1453) 1027 426 (true, I1453_cp1.1, I1453_cp1.2)) 1453 20 false) = true := by
  decide +kernel
theorem I1453_ok : RunOK pI1453 1453 (runFrom pI1453 (fmask pI1453) (cmask pI1453) (hmask pI1453) 1027 426 (true, I1453_cp1.1, I1453_cp1.2)) ∧ intTest pI1453 (runFrom pI1453 (fmask pI1453) (cmask pI1453) (hmask pI1453) 1027 426 (true, I1453_cp1.1, I1453_cp1.2)) 1453 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1453_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1453_fin) true) I1453_seg1) (by decide) rfl I1453_fin intTest_fst
theorem link1453 : linkOK pL1453 pH1453 pI1453 = true := by decide +kernel
theorem cvx1453 : ConvexBetweenHumps 1453 :=
  cvx_of L1453_ok H1453_ok I1453_ok link1453 (by decide)

/-! ### `N = 1454` -/

def pL1454 : Prm := ⟨80, 38, 39, 1456, 11, 18446744073709551616, 127631524195790465, 127631524195790465⟩
def pH1454 : Prm := ⟨80, 38, 39, 1456, 11, 18446744073709551616, 127632623707418241, 127632623707418241⟩
def pI1454 : Prm := ⟨66, 33, 30, 1456, 11, 18446744073709551616, 127631524195790465, 127632623707418241⟩
noncomputable def L1454_cp1 : Nat × Nat := t7val% (fastRun pL1454 1 1027 (init pL1454) (init pL1454))
theorem L1454_seg1 : segOK pL1454 1 1027 (init pL1454) (init pL1454) L1454_cp1.1 L1454_cp1.2 = true := by
  decide +kernel
theorem L1454_fin : (prmOK pL1454 1454 && ptTest pL1454 (runFrom pL1454 (fmask pL1454) (cmask pL1454) (hmask pL1454) 1028 426 (true, L1454_cp1.1, L1454_cp1.2)) 1454 727 false) = true := by
  decide +kernel
theorem L1454_ok : RunOK pL1454 1454 (runFrom pL1454 (fmask pL1454) (cmask pL1454) (hmask pL1454) 1028 426 (true, L1454_cp1.1, L1454_cp1.2)) ∧ ptTest pL1454 (runFrom pL1454 (fmask pL1454) (cmask pL1454) (hmask pL1454) 1028 426 (true, L1454_cp1.1, L1454_cp1.2)) 1454 727 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1454_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1454_fin) true) L1454_seg1) (by decide) rfl L1454_fin ptTest_fst
noncomputable def H1454_cp1 : Nat × Nat := t7val% (fastRun pH1454 1 1027 (init pH1454) (init pH1454))
theorem H1454_seg1 : segOK pH1454 1 1027 (init pH1454) (init pH1454) H1454_cp1.1 H1454_cp1.2 = true := by
  decide +kernel
theorem H1454_fin : (prmOK pH1454 1454 && ptTest pH1454 (runFrom pH1454 (fmask pH1454) (cmask pH1454) (hmask pH1454) 1028 426 (true, H1454_cp1.1, H1454_cp1.2)) 1454 727 true) = true := by
  decide +kernel
theorem H1454_ok : RunOK pH1454 1454 (runFrom pH1454 (fmask pH1454) (cmask pH1454) (hmask pH1454) 1028 426 (true, H1454_cp1.1, H1454_cp1.2)) ∧ ptTest pH1454 (runFrom pH1454 (fmask pH1454) (cmask pH1454) (hmask pH1454) 1028 426 (true, H1454_cp1.1, H1454_cp1.2)) 1454 727 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1454_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1454_fin) true) H1454_seg1) (by decide) rfl H1454_fin ptTest_fst
noncomputable def I1454_cp1 : Nat × Nat := t7val% (fastRun pI1454 1 1027 (init pI1454) (init pI1454))
theorem I1454_seg1 : segOK pI1454 1 1027 (init pI1454) (init pI1454) I1454_cp1.1 I1454_cp1.2 = true := by
  decide +kernel
theorem I1454_fin : (prmOK pI1454 1454 && intTest pI1454 (runFrom pI1454 (fmask pI1454) (cmask pI1454) (hmask pI1454) 1028 426 (true, I1454_cp1.1, I1454_cp1.2)) 1454 20 true) = true := by
  decide +kernel
theorem I1454_ok : RunOK pI1454 1454 (runFrom pI1454 (fmask pI1454) (cmask pI1454) (hmask pI1454) 1028 426 (true, I1454_cp1.1, I1454_cp1.2)) ∧ intTest pI1454 (runFrom pI1454 (fmask pI1454) (cmask pI1454) (hmask pI1454) 1028 426 (true, I1454_cp1.1, I1454_cp1.2)) 1454 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1454_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1454_fin) true) I1454_seg1) (by decide) rfl I1454_fin intTest_fst
theorem link1454 : linkOK pL1454 pH1454 pI1454 = true := by decide +kernel
theorem cvx1454 : ConvexBetweenHumps 1454 :=
  cvx_of L1454_ok H1454_ok I1454_ok link1454 (by decide)
theorem cenlink1454 : cenLinkOK pI1454 1454 = true := by decide +kernel
theorem cen1454 : CenterUniqueMin 1454 ∧ DipHyp 1454 ∧ OnePointHyps 1454 :=
  cen_of L1454_ok H1454_ok I1454_ok link1454 cenlink1454

/-! ### `N = 1455` -/

def pL1455 : Prm := ⟨80, 38, 39, 1457, 11, 18446744073709551616, 127560221967256115, 127560221967256115⟩
def pH1455 : Prm := ⟨80, 38, 39, 1457, 11, 18446744073709551616, 127561321478883891, 127561321478883891⟩
def pI1455 : Prm := ⟨66, 33, 30, 1457, 11, 18446744073709551616, 127560221967256115, 127561321478883891⟩
noncomputable def L1455_cp1 : Nat × Nat := t7val% (fastRun pL1455 1 1028 (init pL1455) (init pL1455))
theorem L1455_seg1 : segOK pL1455 1 1028 (init pL1455) (init pL1455) L1455_cp1.1 L1455_cp1.2 = true := by
  decide +kernel
theorem L1455_fin : (prmOK pL1455 1455 && ptTest pL1455 (runFrom pL1455 (fmask pL1455) (cmask pL1455) (hmask pL1455) 1029 426 (true, L1455_cp1.1, L1455_cp1.2)) 1455 728 false) = true := by
  decide +kernel
theorem L1455_ok : RunOK pL1455 1455 (runFrom pL1455 (fmask pL1455) (cmask pL1455) (hmask pL1455) 1029 426 (true, L1455_cp1.1, L1455_cp1.2)) ∧ ptTest pL1455 (runFrom pL1455 (fmask pL1455) (cmask pL1455) (hmask pL1455) 1029 426 (true, L1455_cp1.1, L1455_cp1.2)) 1455 728 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1455_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1455_fin) true) L1455_seg1) (by decide) rfl L1455_fin ptTest_fst
noncomputable def H1455_cp1 : Nat × Nat := t7val% (fastRun pH1455 1 1028 (init pH1455) (init pH1455))
theorem H1455_seg1 : segOK pH1455 1 1028 (init pH1455) (init pH1455) H1455_cp1.1 H1455_cp1.2 = true := by
  decide +kernel
theorem H1455_fin : (prmOK pH1455 1455 && ptTest pH1455 (runFrom pH1455 (fmask pH1455) (cmask pH1455) (hmask pH1455) 1029 426 (true, H1455_cp1.1, H1455_cp1.2)) 1455 728 true) = true := by
  decide +kernel
theorem H1455_ok : RunOK pH1455 1455 (runFrom pH1455 (fmask pH1455) (cmask pH1455) (hmask pH1455) 1029 426 (true, H1455_cp1.1, H1455_cp1.2)) ∧ ptTest pH1455 (runFrom pH1455 (fmask pH1455) (cmask pH1455) (hmask pH1455) 1029 426 (true, H1455_cp1.1, H1455_cp1.2)) 1455 728 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1455_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1455_fin) true) H1455_seg1) (by decide) rfl H1455_fin ptTest_fst
noncomputable def I1455_cp1 : Nat × Nat := t7val% (fastRun pI1455 1 1028 (init pI1455) (init pI1455))
theorem I1455_seg1 : segOK pI1455 1 1028 (init pI1455) (init pI1455) I1455_cp1.1 I1455_cp1.2 = true := by
  decide +kernel
theorem I1455_fin : (prmOK pI1455 1455 && intTest pI1455 (runFrom pI1455 (fmask pI1455) (cmask pI1455) (hmask pI1455) 1029 426 (true, I1455_cp1.1, I1455_cp1.2)) 1455 20 false) = true := by
  decide +kernel
theorem I1455_ok : RunOK pI1455 1455 (runFrom pI1455 (fmask pI1455) (cmask pI1455) (hmask pI1455) 1029 426 (true, I1455_cp1.1, I1455_cp1.2)) ∧ intTest pI1455 (runFrom pI1455 (fmask pI1455) (cmask pI1455) (hmask pI1455) 1029 426 (true, I1455_cp1.1, I1455_cp1.2)) 1455 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1455_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1455_fin) true) I1455_seg1) (by decide) rfl I1455_fin intTest_fst
theorem link1455 : linkOK pL1455 pH1455 pI1455 = true := by decide +kernel
theorem cvx1455 : ConvexBetweenHumps 1455 :=
  cvx_of L1455_ok H1455_ok I1455_ok link1455 (by decide)

/-! ### `N = 1456` -/

def pL1456 : Prm := ⟨80, 38, 39, 1458, 11, 18446744073709551616, 127489043163672753, 127489043163672753⟩
def pH1456 : Prm := ⟨80, 38, 39, 1458, 11, 18446744073709551616, 127490142675300529, 127490142675300529⟩
def pI1456 : Prm := ⟨66, 33, 30, 1458, 11, 18446744073709551616, 127489043163672753, 127490142675300529⟩
noncomputable def L1456_cp1 : Nat × Nat := t7val% (fastRun pL1456 1 1029 (init pL1456) (init pL1456))
theorem L1456_seg1 : segOK pL1456 1 1029 (init pL1456) (init pL1456) L1456_cp1.1 L1456_cp1.2 = true := by
  decide +kernel
theorem L1456_fin : (prmOK pL1456 1456 && ptTest pL1456 (runFrom pL1456 (fmask pL1456) (cmask pL1456) (hmask pL1456) 1030 426 (true, L1456_cp1.1, L1456_cp1.2)) 1456 728 false) = true := by
  decide +kernel
theorem L1456_ok : RunOK pL1456 1456 (runFrom pL1456 (fmask pL1456) (cmask pL1456) (hmask pL1456) 1030 426 (true, L1456_cp1.1, L1456_cp1.2)) ∧ ptTest pL1456 (runFrom pL1456 (fmask pL1456) (cmask pL1456) (hmask pL1456) 1030 426 (true, L1456_cp1.1, L1456_cp1.2)) 1456 728 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1456_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1456_fin) true) L1456_seg1) (by decide) rfl L1456_fin ptTest_fst
noncomputable def H1456_cp1 : Nat × Nat := t7val% (fastRun pH1456 1 1029 (init pH1456) (init pH1456))
theorem H1456_seg1 : segOK pH1456 1 1029 (init pH1456) (init pH1456) H1456_cp1.1 H1456_cp1.2 = true := by
  decide +kernel
theorem H1456_fin : (prmOK pH1456 1456 && ptTest pH1456 (runFrom pH1456 (fmask pH1456) (cmask pH1456) (hmask pH1456) 1030 426 (true, H1456_cp1.1, H1456_cp1.2)) 1456 728 true) = true := by
  decide +kernel
theorem H1456_ok : RunOK pH1456 1456 (runFrom pH1456 (fmask pH1456) (cmask pH1456) (hmask pH1456) 1030 426 (true, H1456_cp1.1, H1456_cp1.2)) ∧ ptTest pH1456 (runFrom pH1456 (fmask pH1456) (cmask pH1456) (hmask pH1456) 1030 426 (true, H1456_cp1.1, H1456_cp1.2)) 1456 728 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1456_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1456_fin) true) H1456_seg1) (by decide) rfl H1456_fin ptTest_fst
noncomputable def I1456_cp1 : Nat × Nat := t7val% (fastRun pI1456 1 1029 (init pI1456) (init pI1456))
theorem I1456_seg1 : segOK pI1456 1 1029 (init pI1456) (init pI1456) I1456_cp1.1 I1456_cp1.2 = true := by
  decide +kernel
theorem I1456_fin : (prmOK pI1456 1456 && intTest pI1456 (runFrom pI1456 (fmask pI1456) (cmask pI1456) (hmask pI1456) 1030 426 (true, I1456_cp1.1, I1456_cp1.2)) 1456 20 true) = true := by
  decide +kernel
theorem I1456_ok : RunOK pI1456 1456 (runFrom pI1456 (fmask pI1456) (cmask pI1456) (hmask pI1456) 1030 426 (true, I1456_cp1.1, I1456_cp1.2)) ∧ intTest pI1456 (runFrom pI1456 (fmask pI1456) (cmask pI1456) (hmask pI1456) 1030 426 (true, I1456_cp1.1, I1456_cp1.2)) 1456 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1456_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1456_fin) true) I1456_seg1) (by decide) rfl I1456_fin intTest_fst
theorem link1456 : linkOK pL1456 pH1456 pI1456 = true := by decide +kernel
theorem cvx1456 : ConvexBetweenHumps 1456 :=
  cvx_of L1456_ok H1456_ok I1456_ok link1456 (by decide)
theorem cenlink1456 : cenLinkOK pI1456 1456 = true := by decide +kernel
theorem cen1456 : CenterUniqueMin 1456 ∧ DipHyp 1456 ∧ OnePointHyps 1456 :=
  cen_of L1456_ok H1456_ok I1456_ok link1456 cenlink1456

/-! ### `N = 1457` -/

def pL1457 : Prm := ⟨80, 38, 39, 1459, 11, 18446744073709551616, 127417914090316251, 127417914090316251⟩
def pH1457 : Prm := ⟨80, 38, 39, 1459, 11, 18446744073709551616, 127419013601944027, 127419013601944027⟩
def pI1457 : Prm := ⟨66, 33, 30, 1459, 11, 18446744073709551616, 127417914090316251, 127419013601944027⟩
noncomputable def L1457_cp1 : Nat × Nat := t7val% (fastRun pL1457 1 1029 (init pL1457) (init pL1457))
theorem L1457_seg1 : segOK pL1457 1 1029 (init pL1457) (init pL1457) L1457_cp1.1 L1457_cp1.2 = true := by
  decide +kernel
theorem L1457_fin : (prmOK pL1457 1457 && ptTest pL1457 (runFrom pL1457 (fmask pL1457) (cmask pL1457) (hmask pL1457) 1030 427 (true, L1457_cp1.1, L1457_cp1.2)) 1457 729 false) = true := by
  decide +kernel
theorem L1457_ok : RunOK pL1457 1457 (runFrom pL1457 (fmask pL1457) (cmask pL1457) (hmask pL1457) 1030 427 (true, L1457_cp1.1, L1457_cp1.2)) ∧ ptTest pL1457 (runFrom pL1457 (fmask pL1457) (cmask pL1457) (hmask pL1457) 1030 427 (true, L1457_cp1.1, L1457_cp1.2)) 1457 729 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1457_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1457_fin) true) L1457_seg1) (by decide) rfl L1457_fin ptTest_fst
noncomputable def H1457_cp1 : Nat × Nat := t7val% (fastRun pH1457 1 1029 (init pH1457) (init pH1457))
theorem H1457_seg1 : segOK pH1457 1 1029 (init pH1457) (init pH1457) H1457_cp1.1 H1457_cp1.2 = true := by
  decide +kernel
theorem H1457_fin : (prmOK pH1457 1457 && ptTest pH1457 (runFrom pH1457 (fmask pH1457) (cmask pH1457) (hmask pH1457) 1030 427 (true, H1457_cp1.1, H1457_cp1.2)) 1457 729 true) = true := by
  decide +kernel
theorem H1457_ok : RunOK pH1457 1457 (runFrom pH1457 (fmask pH1457) (cmask pH1457) (hmask pH1457) 1030 427 (true, H1457_cp1.1, H1457_cp1.2)) ∧ ptTest pH1457 (runFrom pH1457 (fmask pH1457) (cmask pH1457) (hmask pH1457) 1030 427 (true, H1457_cp1.1, H1457_cp1.2)) 1457 729 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1457_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1457_fin) true) H1457_seg1) (by decide) rfl H1457_fin ptTest_fst
noncomputable def I1457_cp1 : Nat × Nat := t7val% (fastRun pI1457 1 1029 (init pI1457) (init pI1457))
theorem I1457_seg1 : segOK pI1457 1 1029 (init pI1457) (init pI1457) I1457_cp1.1 I1457_cp1.2 = true := by
  decide +kernel
theorem I1457_fin : (prmOK pI1457 1457 && intTest pI1457 (runFrom pI1457 (fmask pI1457) (cmask pI1457) (hmask pI1457) 1030 427 (true, I1457_cp1.1, I1457_cp1.2)) 1457 20 false) = true := by
  decide +kernel
theorem I1457_ok : RunOK pI1457 1457 (runFrom pI1457 (fmask pI1457) (cmask pI1457) (hmask pI1457) 1030 427 (true, I1457_cp1.1, I1457_cp1.2)) ∧ intTest pI1457 (runFrom pI1457 (fmask pI1457) (cmask pI1457) (hmask pI1457) 1030 427 (true, I1457_cp1.1, I1457_cp1.2)) 1457 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1457_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1457_fin) true) I1457_seg1) (by decide) rfl I1457_fin intTest_fst
theorem link1457 : linkOK pL1457 pH1457 pI1457 = true := by decide +kernel
theorem cvx1457 : ConvexBetweenHumps 1457 :=
  cvx_of L1457_ok H1457_ok I1457_ok link1457 (by decide)

/-! ### `N = 1458` -/

def pL1458 : Prm := ⟨80, 38, 39, 1460, 11, 18446744073709551616, 127346907962793454, 127346907962793454⟩
def pH1458 : Prm := ⟨80, 38, 39, 1460, 11, 18446744073709551616, 127348007474421230, 127348007474421230⟩
def pI1458 : Prm := ⟨66, 33, 30, 1460, 11, 18446744073709551616, 127346907962793454, 127348007474421230⟩
noncomputable def L1458_cp1 : Nat × Nat := t7val% (fastRun pL1458 1 1030 (init pL1458) (init pL1458))
theorem L1458_seg1 : segOK pL1458 1 1030 (init pL1458) (init pL1458) L1458_cp1.1 L1458_cp1.2 = true := by
  decide +kernel
theorem L1458_fin : (prmOK pL1458 1458 && ptTest pL1458 (runFrom pL1458 (fmask pL1458) (cmask pL1458) (hmask pL1458) 1031 427 (true, L1458_cp1.1, L1458_cp1.2)) 1458 729 false) = true := by
  decide +kernel
theorem L1458_ok : RunOK pL1458 1458 (runFrom pL1458 (fmask pL1458) (cmask pL1458) (hmask pL1458) 1031 427 (true, L1458_cp1.1, L1458_cp1.2)) ∧ ptTest pL1458 (runFrom pL1458 (fmask pL1458) (cmask pL1458) (hmask pL1458) 1031 427 (true, L1458_cp1.1, L1458_cp1.2)) 1458 729 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1458_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1458_fin) true) L1458_seg1) (by decide) rfl L1458_fin ptTest_fst
noncomputable def H1458_cp1 : Nat × Nat := t7val% (fastRun pH1458 1 1030 (init pH1458) (init pH1458))
theorem H1458_seg1 : segOK pH1458 1 1030 (init pH1458) (init pH1458) H1458_cp1.1 H1458_cp1.2 = true := by
  decide +kernel
theorem H1458_fin : (prmOK pH1458 1458 && ptTest pH1458 (runFrom pH1458 (fmask pH1458) (cmask pH1458) (hmask pH1458) 1031 427 (true, H1458_cp1.1, H1458_cp1.2)) 1458 729 true) = true := by
  decide +kernel
theorem H1458_ok : RunOK pH1458 1458 (runFrom pH1458 (fmask pH1458) (cmask pH1458) (hmask pH1458) 1031 427 (true, H1458_cp1.1, H1458_cp1.2)) ∧ ptTest pH1458 (runFrom pH1458 (fmask pH1458) (cmask pH1458) (hmask pH1458) 1031 427 (true, H1458_cp1.1, H1458_cp1.2)) 1458 729 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1458_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1458_fin) true) H1458_seg1) (by decide) rfl H1458_fin ptTest_fst
noncomputable def I1458_cp1 : Nat × Nat := t7val% (fastRun pI1458 1 1030 (init pI1458) (init pI1458))
theorem I1458_seg1 : segOK pI1458 1 1030 (init pI1458) (init pI1458) I1458_cp1.1 I1458_cp1.2 = true := by
  decide +kernel
theorem I1458_fin : (prmOK pI1458 1458 && intTest pI1458 (runFrom pI1458 (fmask pI1458) (cmask pI1458) (hmask pI1458) 1031 427 (true, I1458_cp1.1, I1458_cp1.2)) 1458 20 true) = true := by
  decide +kernel
theorem I1458_ok : RunOK pI1458 1458 (runFrom pI1458 (fmask pI1458) (cmask pI1458) (hmask pI1458) 1031 427 (true, I1458_cp1.1, I1458_cp1.2)) ∧ intTest pI1458 (runFrom pI1458 (fmask pI1458) (cmask pI1458) (hmask pI1458) 1031 427 (true, I1458_cp1.1, I1458_cp1.2)) 1458 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1458_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1458_fin) true) I1458_seg1) (by decide) rfl I1458_fin intTest_fst
theorem link1458 : linkOK pL1458 pH1458 pI1458 = true := by decide +kernel
theorem cvx1458 : ConvexBetweenHumps 1458 :=
  cvx_of L1458_ok H1458_ok I1458_ok link1458 (by decide)
theorem cenlink1458 : cenLinkOK pI1458 1458 = true := by decide +kernel
theorem cen1458 : CenterUniqueMin 1458 ∧ DipHyp 1458 ∧ OnePointHyps 1458 :=
  cen_of L1458_ok H1458_ok I1458_ok link1458 cenlink1458

/-! ### `N = 1459` -/

def pL1459 : Prm := ⟨80, 38, 39, 1461, 11, 18446744073709551616, 127275951394422411, 127275951394422411⟩
def pH1459 : Prm := ⟨80, 38, 39, 1461, 11, 18446744073709551616, 127277050906050187, 127277050906050187⟩
def pI1459 : Prm := ⟨66, 33, 30, 1461, 11, 18446744073709551616, 127275951394422411, 127277050906050187⟩
noncomputable def L1459_cp1 : Nat × Nat := t7val% (fastRun pL1459 1 1031 (init pL1459) (init pL1459))
theorem L1459_seg1 : segOK pL1459 1 1031 (init pL1459) (init pL1459) L1459_cp1.1 L1459_cp1.2 = true := by
  decide +kernel
theorem L1459_fin : (prmOK pL1459 1459 && ptTest pL1459 (runFrom pL1459 (fmask pL1459) (cmask pL1459) (hmask pL1459) 1032 427 (true, L1459_cp1.1, L1459_cp1.2)) 1459 730 false) = true := by
  decide +kernel
theorem L1459_ok : RunOK pL1459 1459 (runFrom pL1459 (fmask pL1459) (cmask pL1459) (hmask pL1459) 1032 427 (true, L1459_cp1.1, L1459_cp1.2)) ∧ ptTest pL1459 (runFrom pL1459 (fmask pL1459) (cmask pL1459) (hmask pL1459) 1032 427 (true, L1459_cp1.1, L1459_cp1.2)) 1459 730 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1459_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1459_fin) true) L1459_seg1) (by decide) rfl L1459_fin ptTest_fst
noncomputable def H1459_cp1 : Nat × Nat := t7val% (fastRun pH1459 1 1031 (init pH1459) (init pH1459))
theorem H1459_seg1 : segOK pH1459 1 1031 (init pH1459) (init pH1459) H1459_cp1.1 H1459_cp1.2 = true := by
  decide +kernel
theorem H1459_fin : (prmOK pH1459 1459 && ptTest pH1459 (runFrom pH1459 (fmask pH1459) (cmask pH1459) (hmask pH1459) 1032 427 (true, H1459_cp1.1, H1459_cp1.2)) 1459 730 true) = true := by
  decide +kernel
theorem H1459_ok : RunOK pH1459 1459 (runFrom pH1459 (fmask pH1459) (cmask pH1459) (hmask pH1459) 1032 427 (true, H1459_cp1.1, H1459_cp1.2)) ∧ ptTest pH1459 (runFrom pH1459 (fmask pH1459) (cmask pH1459) (hmask pH1459) 1032 427 (true, H1459_cp1.1, H1459_cp1.2)) 1459 730 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1459_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1459_fin) true) H1459_seg1) (by decide) rfl H1459_fin ptTest_fst
noncomputable def I1459_cp1 : Nat × Nat := t7val% (fastRun pI1459 1 1031 (init pI1459) (init pI1459))
theorem I1459_seg1 : segOK pI1459 1 1031 (init pI1459) (init pI1459) I1459_cp1.1 I1459_cp1.2 = true := by
  decide +kernel
theorem I1459_fin : (prmOK pI1459 1459 && intTest pI1459 (runFrom pI1459 (fmask pI1459) (cmask pI1459) (hmask pI1459) 1032 427 (true, I1459_cp1.1, I1459_cp1.2)) 1459 20 false) = true := by
  decide +kernel
theorem I1459_ok : RunOK pI1459 1459 (runFrom pI1459 (fmask pI1459) (cmask pI1459) (hmask pI1459) 1032 427 (true, I1459_cp1.1, I1459_cp1.2)) ∧ intTest pI1459 (runFrom pI1459 (fmask pI1459) (cmask pI1459) (hmask pI1459) 1032 427 (true, I1459_cp1.1, I1459_cp1.2)) 1459 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1459_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1459_fin) true) I1459_seg1) (by decide) rfl I1459_fin intTest_fst
theorem link1459 : linkOK pL1459 pH1459 pI1459 = true := by decide +kernel
theorem cvx1459 : ConvexBetweenHumps 1459 :=
  cvx_of L1459_ok H1459_ok I1459_ok link1459 (by decide)

/-! ### The range -/

theorem cvx_1441_1459 {N : ℕ} (h1 : 1441 ≤ N) (h2 : N ≤ 1459) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1449
  · by_cases h4 : N ≤ 1444
    · by_cases h6 : N ≤ 1442
      · by_cases h8 : N ≤ 1441
        · obtain rfl : N = 1441 := by omega
          exact cvx1441
        · obtain rfl : N = 1442 := by omega
          exact cvx1442
      · by_cases h8 : N ≤ 1443
        · obtain rfl : N = 1443 := by omega
          exact cvx1443
        · obtain rfl : N = 1444 := by omega
          exact cvx1444
    · by_cases h6 : N ≤ 1446
      · by_cases h8 : N ≤ 1445
        · obtain rfl : N = 1445 := by omega
          exact cvx1445
        · obtain rfl : N = 1446 := by omega
          exact cvx1446
      · by_cases h8 : N ≤ 1447
        · obtain rfl : N = 1447 := by omega
          exact cvx1447
        · by_cases h10 : N ≤ 1448
          · obtain rfl : N = 1448 := by omega
            exact cvx1448
          · obtain rfl : N = 1449 := by omega
            exact cvx1449
  · by_cases h4 : N ≤ 1454
    · by_cases h6 : N ≤ 1451
      · by_cases h8 : N ≤ 1450
        · obtain rfl : N = 1450 := by omega
          exact cvx1450
        · obtain rfl : N = 1451 := by omega
          exact cvx1451
      · by_cases h8 : N ≤ 1452
        · obtain rfl : N = 1452 := by omega
          exact cvx1452
        · by_cases h10 : N ≤ 1453
          · obtain rfl : N = 1453 := by omega
            exact cvx1453
          · obtain rfl : N = 1454 := by omega
            exact cvx1454
    · by_cases h6 : N ≤ 1456
      · by_cases h8 : N ≤ 1455
        · obtain rfl : N = 1455 := by omega
          exact cvx1455
        · obtain rfl : N = 1456 := by omega
          exact cvx1456
      · by_cases h8 : N ≤ 1457
        · obtain rfl : N = 1457 := by omega
          exact cvx1457
        · by_cases h10 : N ≤ 1458
          · obtain rfl : N = 1458 := by omega
            exact cvx1458
          · obtain rfl : N = 1459 := by omega
            exact cvx1459

theorem cen_1441_1459 {N : ℕ} (h1 : 1441 ≤ N) (h2 : N ≤ 1459) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1448
  · by_cases h4 : N ≤ 1444
    · by_cases h6 : N ≤ 1442
      · obtain rfl : N = 1442 := by omega
        exact cen1442
      · obtain rfl : N = 1444 := by omega
        exact cen1444
    · by_cases h6 : N ≤ 1446
      · obtain rfl : N = 1446 := by omega
        exact cen1446
      · obtain rfl : N = 1448 := by omega
        exact cen1448
  · by_cases h4 : N ≤ 1452
    · by_cases h6 : N ≤ 1450
      · obtain rfl : N = 1450 := by omega
        exact cen1450
      · obtain rfl : N = 1452 := by omega
        exact cen1452
    · by_cases h6 : N ≤ 1454
      · obtain rfl : N = 1454 := by omega
        exact cen1454
      · by_cases h8 : N ≤ 1456
        · obtain rfl : N = 1456 := by omega
          exact cen1456
        · obtain rfl : N = 1458 := by omega
          exact cen1458

end Kagey131.PaperD.T7
