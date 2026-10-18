import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1832, …, 1842` (generated)

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

/-! ### `N = 1832` -/

def pL1832 : Prm := ⟨80, 37, 40, 1834, 11, 18446744073709551616, 105683909118512852, 105683909118512852⟩
def pH1832 : Prm := ⟨80, 37, 40, 1834, 11, 18446744073709551616, 105685008630140628, 105685008630140628⟩
def pI1832 : Prm := ⟨68, 34, 31, 1834, 11, 18446744073709551616, 105683909118512852, 105685008630140628⟩
noncomputable def L1832_cp1 : Nat × Nat := t7val% (fastRun pL1832 1 1057 (init pL1832) (init pL1832))
theorem L1832_seg1 : segOK pL1832 1 1057 (init pL1832) (init pL1832) L1832_cp1.1 L1832_cp1.2 = true := by
  decide +kernel
noncomputable def L1832_cp2 : Nat × Nat := t7val% (fastRun pL1832 1 1495 (init pL1832) (init pL1832))
theorem L1832_seg2 : segOK pL1832 1058 438 L1832_cp1.1 L1832_cp1.2 L1832_cp2.1 L1832_cp2.2 = true := by
  decide +kernel
theorem L1832_fin : (prmOK pL1832 1832 && ptTest pL1832 (runFrom pL1832 (fmask pL1832) (cmask pL1832) (hmask pL1832) 1496 336 (true, L1832_cp2.1, L1832_cp2.2)) 1832 916 false) = true := by
  decide +kernel
theorem L1832_ok : RunOK pL1832 1832 (runFrom pL1832 (fmask pL1832) (cmask pL1832) (hmask pL1832) 1496 336 (true, L1832_cp2.1, L1832_cp2.2)) ∧ ptTest pL1832 (runFrom pL1832 (fmask pL1832) (cmask pL1832) (hmask pL1832) 1496 336 (true, L1832_cp2.1, L1832_cp2.2)) 1832 916 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1832_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1832_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1832_fin) true) L1832_seg1) L1832_seg2) (by decide) rfl L1832_fin ptTest_fst
noncomputable def H1832_cp1 : Nat × Nat := t7val% (fastRun pH1832 1 1057 (init pH1832) (init pH1832))
theorem H1832_seg1 : segOK pH1832 1 1057 (init pH1832) (init pH1832) H1832_cp1.1 H1832_cp1.2 = true := by
  decide +kernel
noncomputable def H1832_cp2 : Nat × Nat := t7val% (fastRun pH1832 1 1495 (init pH1832) (init pH1832))
theorem H1832_seg2 : segOK pH1832 1058 438 H1832_cp1.1 H1832_cp1.2 H1832_cp2.1 H1832_cp2.2 = true := by
  decide +kernel
theorem H1832_fin : (prmOK pH1832 1832 && ptTest pH1832 (runFrom pH1832 (fmask pH1832) (cmask pH1832) (hmask pH1832) 1496 336 (true, H1832_cp2.1, H1832_cp2.2)) 1832 916 true) = true := by
  decide +kernel
theorem H1832_ok : RunOK pH1832 1832 (runFrom pH1832 (fmask pH1832) (cmask pH1832) (hmask pH1832) 1496 336 (true, H1832_cp2.1, H1832_cp2.2)) ∧ ptTest pH1832 (runFrom pH1832 (fmask pH1832) (cmask pH1832) (hmask pH1832) 1496 336 (true, H1832_cp2.1, H1832_cp2.2)) 1832 916 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1832_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1832_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1832_fin) true) H1832_seg1) H1832_seg2) (by decide) rfl H1832_fin ptTest_fst
noncomputable def I1832_cp1 : Nat × Nat := t7val% (fastRun pI1832 1 1057 (init pI1832) (init pI1832))
theorem I1832_seg1 : segOK pI1832 1 1057 (init pI1832) (init pI1832) I1832_cp1.1 I1832_cp1.2 = true := by
  decide +kernel
noncomputable def I1832_cp2 : Nat × Nat := t7val% (fastRun pI1832 1 1495 (init pI1832) (init pI1832))
theorem I1832_seg2 : segOK pI1832 1058 438 I1832_cp1.1 I1832_cp1.2 I1832_cp2.1 I1832_cp2.2 = true := by
  decide +kernel
theorem I1832_fin : (prmOK pI1832 1832 && intTest pI1832 (runFrom pI1832 (fmask pI1832) (cmask pI1832) (hmask pI1832) 1496 336 (true, I1832_cp2.1, I1832_cp2.2)) 1832 21 true) = true := by
  decide +kernel
theorem I1832_ok : RunOK pI1832 1832 (runFrom pI1832 (fmask pI1832) (cmask pI1832) (hmask pI1832) 1496 336 (true, I1832_cp2.1, I1832_cp2.2)) ∧ intTest pI1832 (runFrom pI1832 (fmask pI1832) (cmask pI1832) (hmask pI1832) 1496 336 (true, I1832_cp2.1, I1832_cp2.2)) 1832 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1832_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1832_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1832_fin) true) I1832_seg1) I1832_seg2) (by decide) rfl I1832_fin intTest_fst
theorem link1832 : linkOK pL1832 pH1832 pI1832 = true := by decide +kernel
theorem cvx1832 : ConvexBetweenHumps 1832 :=
  cvx_of L1832_ok H1832_ok I1832_ok link1832 (by decide)
theorem cenlink1832 : cenLinkOK pI1832 1832 = true := by decide +kernel
theorem cen1832 : CenterUniqueMin 1832 ∧ DipHyp 1832 ∧ OnePointHyps 1832 :=
  cen_of L1832_ok H1832_ok I1832_ok link1832 cenlink1832

/-! ### `N = 1833` -/

def pL1833 : Prm := ⟨80, 37, 40, 1835, 11, 18446744073709551616, 105636595733388007, 105636595733388007⟩
def pH1833 : Prm := ⟨80, 37, 40, 1835, 11, 18446744073709551616, 105637695245015783, 105637695245015783⟩
def pI1833 : Prm := ⟨68, 34, 31, 1835, 11, 18446744073709551616, 105636595733388007, 105637695245015783⟩
noncomputable def L1833_cp1 : Nat × Nat := t7val% (fastRun pL1833 1 1057 (init pL1833) (init pL1833))
theorem L1833_seg1 : segOK pL1833 1 1057 (init pL1833) (init pL1833) L1833_cp1.1 L1833_cp1.2 = true := by
  decide +kernel
noncomputable def L1833_cp2 : Nat × Nat := t7val% (fastRun pL1833 1 1496 (init pL1833) (init pL1833))
theorem L1833_seg2 : segOK pL1833 1058 439 L1833_cp1.1 L1833_cp1.2 L1833_cp2.1 L1833_cp2.2 = true := by
  decide +kernel
theorem L1833_fin : (prmOK pL1833 1833 && ptTest pL1833 (runFrom pL1833 (fmask pL1833) (cmask pL1833) (hmask pL1833) 1497 336 (true, L1833_cp2.1, L1833_cp2.2)) 1833 917 false) = true := by
  decide +kernel
theorem L1833_ok : RunOK pL1833 1833 (runFrom pL1833 (fmask pL1833) (cmask pL1833) (hmask pL1833) 1497 336 (true, L1833_cp2.1, L1833_cp2.2)) ∧ ptTest pL1833 (runFrom pL1833 (fmask pL1833) (cmask pL1833) (hmask pL1833) 1497 336 (true, L1833_cp2.1, L1833_cp2.2)) 1833 917 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1833_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1833_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1833_fin) true) L1833_seg1) L1833_seg2) (by decide) rfl L1833_fin ptTest_fst
noncomputable def H1833_cp1 : Nat × Nat := t7val% (fastRun pH1833 1 1057 (init pH1833) (init pH1833))
theorem H1833_seg1 : segOK pH1833 1 1057 (init pH1833) (init pH1833) H1833_cp1.1 H1833_cp1.2 = true := by
  decide +kernel
noncomputable def H1833_cp2 : Nat × Nat := t7val% (fastRun pH1833 1 1496 (init pH1833) (init pH1833))
theorem H1833_seg2 : segOK pH1833 1058 439 H1833_cp1.1 H1833_cp1.2 H1833_cp2.1 H1833_cp2.2 = true := by
  decide +kernel
theorem H1833_fin : (prmOK pH1833 1833 && ptTest pH1833 (runFrom pH1833 (fmask pH1833) (cmask pH1833) (hmask pH1833) 1497 336 (true, H1833_cp2.1, H1833_cp2.2)) 1833 917 true) = true := by
  decide +kernel
theorem H1833_ok : RunOK pH1833 1833 (runFrom pH1833 (fmask pH1833) (cmask pH1833) (hmask pH1833) 1497 336 (true, H1833_cp2.1, H1833_cp2.2)) ∧ ptTest pH1833 (runFrom pH1833 (fmask pH1833) (cmask pH1833) (hmask pH1833) 1497 336 (true, H1833_cp2.1, H1833_cp2.2)) 1833 917 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1833_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1833_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1833_fin) true) H1833_seg1) H1833_seg2) (by decide) rfl H1833_fin ptTest_fst
noncomputable def I1833_cp1 : Nat × Nat := t7val% (fastRun pI1833 1 1057 (init pI1833) (init pI1833))
theorem I1833_seg1 : segOK pI1833 1 1057 (init pI1833) (init pI1833) I1833_cp1.1 I1833_cp1.2 = true := by
  decide +kernel
noncomputable def I1833_cp2 : Nat × Nat := t7val% (fastRun pI1833 1 1496 (init pI1833) (init pI1833))
theorem I1833_seg2 : segOK pI1833 1058 439 I1833_cp1.1 I1833_cp1.2 I1833_cp2.1 I1833_cp2.2 = true := by
  decide +kernel
theorem I1833_fin : (prmOK pI1833 1833 && intTest pI1833 (runFrom pI1833 (fmask pI1833) (cmask pI1833) (hmask pI1833) 1497 336 (true, I1833_cp2.1, I1833_cp2.2)) 1833 21 false) = true := by
  decide +kernel
theorem I1833_ok : RunOK pI1833 1833 (runFrom pI1833 (fmask pI1833) (cmask pI1833) (hmask pI1833) 1497 336 (true, I1833_cp2.1, I1833_cp2.2)) ∧ intTest pI1833 (runFrom pI1833 (fmask pI1833) (cmask pI1833) (hmask pI1833) 1497 336 (true, I1833_cp2.1, I1833_cp2.2)) 1833 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1833_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1833_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1833_fin) true) I1833_seg1) I1833_seg2) (by decide) rfl I1833_fin intTest_fst
theorem link1833 : linkOK pL1833 pH1833 pI1833 = true := by decide +kernel
theorem cvx1833 : ConvexBetweenHumps 1833 :=
  cvx_of L1833_ok H1833_ok I1833_ok link1833 (by decide)

/-! ### `N = 1834` -/

def pL1834 : Prm := ⟨80, 37, 40, 1836, 11, 18446744073709551616, 105589346492203992, 105589346492203992⟩
def pH1834 : Prm := ⟨80, 37, 40, 1836, 11, 18446744073709551616, 105590446003831768, 105590446003831768⟩
def pI1834 : Prm := ⟨68, 34, 31, 1836, 11, 18446744073709551616, 105589346492203992, 105590446003831768⟩
noncomputable def L1834_cp1 : Nat × Nat := t7val% (fastRun pL1834 1 1058 (init pL1834) (init pL1834))
theorem L1834_seg1 : segOK pL1834 1 1058 (init pL1834) (init pL1834) L1834_cp1.1 L1834_cp1.2 = true := by
  decide +kernel
noncomputable def L1834_cp2 : Nat × Nat := t7val% (fastRun pL1834 1 1496 (init pL1834) (init pL1834))
theorem L1834_seg2 : segOK pL1834 1059 438 L1834_cp1.1 L1834_cp1.2 L1834_cp2.1 L1834_cp2.2 = true := by
  decide +kernel
theorem L1834_fin : (prmOK pL1834 1834 && ptTest pL1834 (runFrom pL1834 (fmask pL1834) (cmask pL1834) (hmask pL1834) 1497 337 (true, L1834_cp2.1, L1834_cp2.2)) 1834 917 false) = true := by
  decide +kernel
theorem L1834_ok : RunOK pL1834 1834 (runFrom pL1834 (fmask pL1834) (cmask pL1834) (hmask pL1834) 1497 337 (true, L1834_cp2.1, L1834_cp2.2)) ∧ ptTest pL1834 (runFrom pL1834 (fmask pL1834) (cmask pL1834) (hmask pL1834) 1497 337 (true, L1834_cp2.1, L1834_cp2.2)) 1834 917 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1834_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1834_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1834_fin) true) L1834_seg1) L1834_seg2) (by decide) rfl L1834_fin ptTest_fst
noncomputable def H1834_cp1 : Nat × Nat := t7val% (fastRun pH1834 1 1058 (init pH1834) (init pH1834))
theorem H1834_seg1 : segOK pH1834 1 1058 (init pH1834) (init pH1834) H1834_cp1.1 H1834_cp1.2 = true := by
  decide +kernel
noncomputable def H1834_cp2 : Nat × Nat := t7val% (fastRun pH1834 1 1496 (init pH1834) (init pH1834))
theorem H1834_seg2 : segOK pH1834 1059 438 H1834_cp1.1 H1834_cp1.2 H1834_cp2.1 H1834_cp2.2 = true := by
  decide +kernel
theorem H1834_fin : (prmOK pH1834 1834 && ptTest pH1834 (runFrom pH1834 (fmask pH1834) (cmask pH1834) (hmask pH1834) 1497 337 (true, H1834_cp2.1, H1834_cp2.2)) 1834 917 true) = true := by
  decide +kernel
theorem H1834_ok : RunOK pH1834 1834 (runFrom pH1834 (fmask pH1834) (cmask pH1834) (hmask pH1834) 1497 337 (true, H1834_cp2.1, H1834_cp2.2)) ∧ ptTest pH1834 (runFrom pH1834 (fmask pH1834) (cmask pH1834) (hmask pH1834) 1497 337 (true, H1834_cp2.1, H1834_cp2.2)) 1834 917 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1834_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1834_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1834_fin) true) H1834_seg1) H1834_seg2) (by decide) rfl H1834_fin ptTest_fst
noncomputable def I1834_cp1 : Nat × Nat := t7val% (fastRun pI1834 1 1058 (init pI1834) (init pI1834))
theorem I1834_seg1 : segOK pI1834 1 1058 (init pI1834) (init pI1834) I1834_cp1.1 I1834_cp1.2 = true := by
  decide +kernel
noncomputable def I1834_cp2 : Nat × Nat := t7val% (fastRun pI1834 1 1496 (init pI1834) (init pI1834))
theorem I1834_seg2 : segOK pI1834 1059 438 I1834_cp1.1 I1834_cp1.2 I1834_cp2.1 I1834_cp2.2 = true := by
  decide +kernel
theorem I1834_fin : (prmOK pI1834 1834 && intTest pI1834 (runFrom pI1834 (fmask pI1834) (cmask pI1834) (hmask pI1834) 1497 337 (true, I1834_cp2.1, I1834_cp2.2)) 1834 21 true) = true := by
  decide +kernel
theorem I1834_ok : RunOK pI1834 1834 (runFrom pI1834 (fmask pI1834) (cmask pI1834) (hmask pI1834) 1497 337 (true, I1834_cp2.1, I1834_cp2.2)) ∧ intTest pI1834 (runFrom pI1834 (fmask pI1834) (cmask pI1834) (hmask pI1834) 1497 337 (true, I1834_cp2.1, I1834_cp2.2)) 1834 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1834_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1834_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1834_fin) true) I1834_seg1) I1834_seg2) (by decide) rfl I1834_fin intTest_fst
theorem link1834 : linkOK pL1834 pH1834 pI1834 = true := by decide +kernel
theorem cvx1834 : ConvexBetweenHumps 1834 :=
  cvx_of L1834_ok H1834_ok I1834_ok link1834 (by decide)
theorem cenlink1834 : cenLinkOK pI1834 1834 = true := by decide +kernel
theorem cen1834 : CenterUniqueMin 1834 ∧ DipHyp 1834 ∧ OnePointHyps 1834 :=
  cen_of L1834_ok H1834_ok I1834_ok link1834 cenlink1834

/-! ### `N = 1835` -/

def pL1835 : Prm := ⟨80, 37, 40, 1837, 11, 18446744073709551616, 105542124938734283, 105542124938734283⟩
def pH1835 : Prm := ⟨80, 37, 40, 1837, 11, 18446744073709551616, 105543224450362059, 105543224450362059⟩
def pI1835 : Prm := ⟨68, 34, 31, 1837, 11, 18446744073709551616, 105542124938734283, 105543224450362059⟩
noncomputable def L1835_cp1 : Nat × Nat := t7val% (fastRun pL1835 1 1058 (init pL1835) (init pL1835))
theorem L1835_seg1 : segOK pL1835 1 1058 (init pL1835) (init pL1835) L1835_cp1.1 L1835_cp1.2 = true := by
  decide +kernel
noncomputable def L1835_cp2 : Nat × Nat := t7val% (fastRun pL1835 1 1497 (init pL1835) (init pL1835))
theorem L1835_seg2 : segOK pL1835 1059 439 L1835_cp1.1 L1835_cp1.2 L1835_cp2.1 L1835_cp2.2 = true := by
  decide +kernel
theorem L1835_fin : (prmOK pL1835 1835 && ptTest pL1835 (runFrom pL1835 (fmask pL1835) (cmask pL1835) (hmask pL1835) 1498 337 (true, L1835_cp2.1, L1835_cp2.2)) 1835 918 false) = true := by
  decide +kernel
theorem L1835_ok : RunOK pL1835 1835 (runFrom pL1835 (fmask pL1835) (cmask pL1835) (hmask pL1835) 1498 337 (true, L1835_cp2.1, L1835_cp2.2)) ∧ ptTest pL1835 (runFrom pL1835 (fmask pL1835) (cmask pL1835) (hmask pL1835) 1498 337 (true, L1835_cp2.1, L1835_cp2.2)) 1835 918 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1835_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1835_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1835_fin) true) L1835_seg1) L1835_seg2) (by decide) rfl L1835_fin ptTest_fst
noncomputable def H1835_cp1 : Nat × Nat := t7val% (fastRun pH1835 1 1058 (init pH1835) (init pH1835))
theorem H1835_seg1 : segOK pH1835 1 1058 (init pH1835) (init pH1835) H1835_cp1.1 H1835_cp1.2 = true := by
  decide +kernel
noncomputable def H1835_cp2 : Nat × Nat := t7val% (fastRun pH1835 1 1497 (init pH1835) (init pH1835))
theorem H1835_seg2 : segOK pH1835 1059 439 H1835_cp1.1 H1835_cp1.2 H1835_cp2.1 H1835_cp2.2 = true := by
  decide +kernel
theorem H1835_fin : (prmOK pH1835 1835 && ptTest pH1835 (runFrom pH1835 (fmask pH1835) (cmask pH1835) (hmask pH1835) 1498 337 (true, H1835_cp2.1, H1835_cp2.2)) 1835 918 true) = true := by
  decide +kernel
theorem H1835_ok : RunOK pH1835 1835 (runFrom pH1835 (fmask pH1835) (cmask pH1835) (hmask pH1835) 1498 337 (true, H1835_cp2.1, H1835_cp2.2)) ∧ ptTest pH1835 (runFrom pH1835 (fmask pH1835) (cmask pH1835) (hmask pH1835) 1498 337 (true, H1835_cp2.1, H1835_cp2.2)) 1835 918 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1835_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1835_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1835_fin) true) H1835_seg1) H1835_seg2) (by decide) rfl H1835_fin ptTest_fst
noncomputable def I1835_cp1 : Nat × Nat := t7val% (fastRun pI1835 1 1058 (init pI1835) (init pI1835))
theorem I1835_seg1 : segOK pI1835 1 1058 (init pI1835) (init pI1835) I1835_cp1.1 I1835_cp1.2 = true := by
  decide +kernel
noncomputable def I1835_cp2 : Nat × Nat := t7val% (fastRun pI1835 1 1497 (init pI1835) (init pI1835))
theorem I1835_seg2 : segOK pI1835 1059 439 I1835_cp1.1 I1835_cp1.2 I1835_cp2.1 I1835_cp2.2 = true := by
  decide +kernel
theorem I1835_fin : (prmOK pI1835 1835 && intTest pI1835 (runFrom pI1835 (fmask pI1835) (cmask pI1835) (hmask pI1835) 1498 337 (true, I1835_cp2.1, I1835_cp2.2)) 1835 21 false) = true := by
  decide +kernel
theorem I1835_ok : RunOK pI1835 1835 (runFrom pI1835 (fmask pI1835) (cmask pI1835) (hmask pI1835) 1498 337 (true, I1835_cp2.1, I1835_cp2.2)) ∧ intTest pI1835 (runFrom pI1835 (fmask pI1835) (cmask pI1835) (hmask pI1835) 1498 337 (true, I1835_cp2.1, I1835_cp2.2)) 1835 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1835_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1835_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1835_fin) true) I1835_seg1) I1835_seg2) (by decide) rfl I1835_fin intTest_fst
theorem link1835 : linkOK pL1835 pH1835 pI1835 = true := by decide +kernel
theorem cvx1835 : ConvexBetweenHumps 1835 :=
  cvx_of L1835_ok H1835_ok I1835_ok link1835 (by decide)

/-! ### `N = 1836` -/

def pL1836 : Prm := ⟨80, 37, 40, 1838, 11, 18446744073709551616, 105494967331105818, 105494967331105818⟩
def pH1836 : Prm := ⟨80, 37, 40, 1838, 11, 18446744073709551616, 105496066842733594, 105496066842733594⟩
def pI1836 : Prm := ⟨68, 34, 31, 1838, 11, 18446744073709551616, 105494967331105818, 105496066842733594⟩
noncomputable def L1836_cp1 : Nat × Nat := t7val% (fastRun pL1836 1 1059 (init pL1836) (init pL1836))
theorem L1836_seg1 : segOK pL1836 1 1059 (init pL1836) (init pL1836) L1836_cp1.1 L1836_cp1.2 = true := by
  decide +kernel
noncomputable def L1836_cp2 : Nat × Nat := t7val% (fastRun pL1836 1 1498 (init pL1836) (init pL1836))
theorem L1836_seg2 : segOK pL1836 1060 439 L1836_cp1.1 L1836_cp1.2 L1836_cp2.1 L1836_cp2.2 = true := by
  decide +kernel
theorem L1836_fin : (prmOK pL1836 1836 && ptTest pL1836 (runFrom pL1836 (fmask pL1836) (cmask pL1836) (hmask pL1836) 1499 337 (true, L1836_cp2.1, L1836_cp2.2)) 1836 918 false) = true := by
  decide +kernel
theorem L1836_ok : RunOK pL1836 1836 (runFrom pL1836 (fmask pL1836) (cmask pL1836) (hmask pL1836) 1499 337 (true, L1836_cp2.1, L1836_cp2.2)) ∧ ptTest pL1836 (runFrom pL1836 (fmask pL1836) (cmask pL1836) (hmask pL1836) 1499 337 (true, L1836_cp2.1, L1836_cp2.2)) 1836 918 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1836_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1836_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1836_fin) true) L1836_seg1) L1836_seg2) (by decide) rfl L1836_fin ptTest_fst
noncomputable def H1836_cp1 : Nat × Nat := t7val% (fastRun pH1836 1 1059 (init pH1836) (init pH1836))
theorem H1836_seg1 : segOK pH1836 1 1059 (init pH1836) (init pH1836) H1836_cp1.1 H1836_cp1.2 = true := by
  decide +kernel
noncomputable def H1836_cp2 : Nat × Nat := t7val% (fastRun pH1836 1 1498 (init pH1836) (init pH1836))
theorem H1836_seg2 : segOK pH1836 1060 439 H1836_cp1.1 H1836_cp1.2 H1836_cp2.1 H1836_cp2.2 = true := by
  decide +kernel
theorem H1836_fin : (prmOK pH1836 1836 && ptTest pH1836 (runFrom pH1836 (fmask pH1836) (cmask pH1836) (hmask pH1836) 1499 337 (true, H1836_cp2.1, H1836_cp2.2)) 1836 918 true) = true := by
  decide +kernel
theorem H1836_ok : RunOK pH1836 1836 (runFrom pH1836 (fmask pH1836) (cmask pH1836) (hmask pH1836) 1499 337 (true, H1836_cp2.1, H1836_cp2.2)) ∧ ptTest pH1836 (runFrom pH1836 (fmask pH1836) (cmask pH1836) (hmask pH1836) 1499 337 (true, H1836_cp2.1, H1836_cp2.2)) 1836 918 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1836_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1836_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1836_fin) true) H1836_seg1) H1836_seg2) (by decide) rfl H1836_fin ptTest_fst
noncomputable def I1836_cp1 : Nat × Nat := t7val% (fastRun pI1836 1 1059 (init pI1836) (init pI1836))
theorem I1836_seg1 : segOK pI1836 1 1059 (init pI1836) (init pI1836) I1836_cp1.1 I1836_cp1.2 = true := by
  decide +kernel
noncomputable def I1836_cp2 : Nat × Nat := t7val% (fastRun pI1836 1 1498 (init pI1836) (init pI1836))
theorem I1836_seg2 : segOK pI1836 1060 439 I1836_cp1.1 I1836_cp1.2 I1836_cp2.1 I1836_cp2.2 = true := by
  decide +kernel
theorem I1836_fin : (prmOK pI1836 1836 && intTest pI1836 (runFrom pI1836 (fmask pI1836) (cmask pI1836) (hmask pI1836) 1499 337 (true, I1836_cp2.1, I1836_cp2.2)) 1836 21 true) = true := by
  decide +kernel
theorem I1836_ok : RunOK pI1836 1836 (runFrom pI1836 (fmask pI1836) (cmask pI1836) (hmask pI1836) 1499 337 (true, I1836_cp2.1, I1836_cp2.2)) ∧ intTest pI1836 (runFrom pI1836 (fmask pI1836) (cmask pI1836) (hmask pI1836) 1499 337 (true, I1836_cp2.1, I1836_cp2.2)) 1836 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1836_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1836_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1836_fin) true) I1836_seg1) I1836_seg2) (by decide) rfl I1836_fin intTest_fst
theorem link1836 : linkOK pL1836 pH1836 pI1836 = true := by decide +kernel
theorem cvx1836 : ConvexBetweenHumps 1836 :=
  cvx_of L1836_ok H1836_ok I1836_ok link1836 (by decide)
theorem cenlink1836 : cenLinkOK pI1836 1836 = true := by decide +kernel
theorem cen1836 : CenterUniqueMin 1836 ∧ DipHyp 1836 ∧ OnePointHyps 1836 :=
  cen_of L1836_ok H1836_ok I1836_ok link1836 cenlink1836

/-! ### `N = 1837` -/

def pL1837 : Prm := ⟨80, 37, 40, 1839, 11, 18446744073709551616, 105447837333973588, 105447837333973588⟩
def pH1837 : Prm := ⟨80, 37, 40, 1839, 11, 18446744073709551616, 105448936845601364, 105448936845601364⟩
def pI1837 : Prm := ⟨68, 34, 31, 1839, 11, 18446744073709551616, 105447837333973588, 105448936845601364⟩
noncomputable def L1837_cp1 : Nat × Nat := t7val% (fastRun pL1837 1 1060 (init pL1837) (init pL1837))
theorem L1837_seg1 : segOK pL1837 1 1060 (init pL1837) (init pL1837) L1837_cp1.1 L1837_cp1.2 = true := by
  decide +kernel
noncomputable def L1837_cp2 : Nat × Nat := t7val% (fastRun pL1837 1 1499 (init pL1837) (init pL1837))
theorem L1837_seg2 : segOK pL1837 1061 439 L1837_cp1.1 L1837_cp1.2 L1837_cp2.1 L1837_cp2.2 = true := by
  decide +kernel
theorem L1837_fin : (prmOK pL1837 1837 && ptTest pL1837 (runFrom pL1837 (fmask pL1837) (cmask pL1837) (hmask pL1837) 1500 337 (true, L1837_cp2.1, L1837_cp2.2)) 1837 919 false) = true := by
  decide +kernel
theorem L1837_ok : RunOK pL1837 1837 (runFrom pL1837 (fmask pL1837) (cmask pL1837) (hmask pL1837) 1500 337 (true, L1837_cp2.1, L1837_cp2.2)) ∧ ptTest pL1837 (runFrom pL1837 (fmask pL1837) (cmask pL1837) (hmask pL1837) 1500 337 (true, L1837_cp2.1, L1837_cp2.2)) 1837 919 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1837_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1837_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1837_fin) true) L1837_seg1) L1837_seg2) (by decide) rfl L1837_fin ptTest_fst
noncomputable def H1837_cp1 : Nat × Nat := t7val% (fastRun pH1837 1 1060 (init pH1837) (init pH1837))
theorem H1837_seg1 : segOK pH1837 1 1060 (init pH1837) (init pH1837) H1837_cp1.1 H1837_cp1.2 = true := by
  decide +kernel
noncomputable def H1837_cp2 : Nat × Nat := t7val% (fastRun pH1837 1 1499 (init pH1837) (init pH1837))
theorem H1837_seg2 : segOK pH1837 1061 439 H1837_cp1.1 H1837_cp1.2 H1837_cp2.1 H1837_cp2.2 = true := by
  decide +kernel
theorem H1837_fin : (prmOK pH1837 1837 && ptTest pH1837 (runFrom pH1837 (fmask pH1837) (cmask pH1837) (hmask pH1837) 1500 337 (true, H1837_cp2.1, H1837_cp2.2)) 1837 919 true) = true := by
  decide +kernel
theorem H1837_ok : RunOK pH1837 1837 (runFrom pH1837 (fmask pH1837) (cmask pH1837) (hmask pH1837) 1500 337 (true, H1837_cp2.1, H1837_cp2.2)) ∧ ptTest pH1837 (runFrom pH1837 (fmask pH1837) (cmask pH1837) (hmask pH1837) 1500 337 (true, H1837_cp2.1, H1837_cp2.2)) 1837 919 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1837_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1837_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1837_fin) true) H1837_seg1) H1837_seg2) (by decide) rfl H1837_fin ptTest_fst
noncomputable def I1837_cp1 : Nat × Nat := t7val% (fastRun pI1837 1 1060 (init pI1837) (init pI1837))
theorem I1837_seg1 : segOK pI1837 1 1060 (init pI1837) (init pI1837) I1837_cp1.1 I1837_cp1.2 = true := by
  decide +kernel
noncomputable def I1837_cp2 : Nat × Nat := t7val% (fastRun pI1837 1 1499 (init pI1837) (init pI1837))
theorem I1837_seg2 : segOK pI1837 1061 439 I1837_cp1.1 I1837_cp1.2 I1837_cp2.1 I1837_cp2.2 = true := by
  decide +kernel
theorem I1837_fin : (prmOK pI1837 1837 && intTest pI1837 (runFrom pI1837 (fmask pI1837) (cmask pI1837) (hmask pI1837) 1500 337 (true, I1837_cp2.1, I1837_cp2.2)) 1837 21 false) = true := by
  decide +kernel
theorem I1837_ok : RunOK pI1837 1837 (runFrom pI1837 (fmask pI1837) (cmask pI1837) (hmask pI1837) 1500 337 (true, I1837_cp2.1, I1837_cp2.2)) ∧ intTest pI1837 (runFrom pI1837 (fmask pI1837) (cmask pI1837) (hmask pI1837) 1500 337 (true, I1837_cp2.1, I1837_cp2.2)) 1837 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1837_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1837_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1837_fin) true) I1837_seg1) I1837_seg2) (by decide) rfl I1837_fin intTest_fst
theorem link1837 : linkOK pL1837 pH1837 pI1837 = true := by decide +kernel
theorem cvx1837 : ConvexBetweenHumps 1837 :=
  cvx_of L1837_ok H1837_ok I1837_ok link1837 (by decide)

/-! ### `N = 1838` -/

def pL1838 : Prm := ⟨80, 37, 40, 1840, 11, 18446744073709551616, 105400771085394675, 105400771085394675⟩
def pH1838 : Prm := ⟨80, 37, 40, 1840, 11, 18446744073709551616, 105401870597022451, 105401870597022451⟩
def pI1838 : Prm := ⟨68, 34, 31, 1840, 11, 18446744073709551616, 105400771085394675, 105401870597022451⟩
noncomputable def L1838_cp1 : Nat × Nat := t7val% (fastRun pL1838 1 1060 (init pL1838) (init pL1838))
theorem L1838_seg1 : segOK pL1838 1 1060 (init pL1838) (init pL1838) L1838_cp1.1 L1838_cp1.2 = true := by
  decide +kernel
noncomputable def L1838_cp2 : Nat × Nat := t7val% (fastRun pL1838 1 1500 (init pL1838) (init pL1838))
theorem L1838_seg2 : segOK pL1838 1061 440 L1838_cp1.1 L1838_cp1.2 L1838_cp2.1 L1838_cp2.2 = true := by
  decide +kernel
theorem L1838_fin : (prmOK pL1838 1838 && ptTest pL1838 (runFrom pL1838 (fmask pL1838) (cmask pL1838) (hmask pL1838) 1501 337 (true, L1838_cp2.1, L1838_cp2.2)) 1838 919 false) = true := by
  decide +kernel
theorem L1838_ok : RunOK pL1838 1838 (runFrom pL1838 (fmask pL1838) (cmask pL1838) (hmask pL1838) 1501 337 (true, L1838_cp2.1, L1838_cp2.2)) ∧ ptTest pL1838 (runFrom pL1838 (fmask pL1838) (cmask pL1838) (hmask pL1838) 1501 337 (true, L1838_cp2.1, L1838_cp2.2)) 1838 919 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1838_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1838_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1838_fin) true) L1838_seg1) L1838_seg2) (by decide) rfl L1838_fin ptTest_fst
noncomputable def H1838_cp1 : Nat × Nat := t7val% (fastRun pH1838 1 1060 (init pH1838) (init pH1838))
theorem H1838_seg1 : segOK pH1838 1 1060 (init pH1838) (init pH1838) H1838_cp1.1 H1838_cp1.2 = true := by
  decide +kernel
noncomputable def H1838_cp2 : Nat × Nat := t7val% (fastRun pH1838 1 1500 (init pH1838) (init pH1838))
theorem H1838_seg2 : segOK pH1838 1061 440 H1838_cp1.1 H1838_cp1.2 H1838_cp2.1 H1838_cp2.2 = true := by
  decide +kernel
theorem H1838_fin : (prmOK pH1838 1838 && ptTest pH1838 (runFrom pH1838 (fmask pH1838) (cmask pH1838) (hmask pH1838) 1501 337 (true, H1838_cp2.1, H1838_cp2.2)) 1838 919 true) = true := by
  decide +kernel
theorem H1838_ok : RunOK pH1838 1838 (runFrom pH1838 (fmask pH1838) (cmask pH1838) (hmask pH1838) 1501 337 (true, H1838_cp2.1, H1838_cp2.2)) ∧ ptTest pH1838 (runFrom pH1838 (fmask pH1838) (cmask pH1838) (hmask pH1838) 1501 337 (true, H1838_cp2.1, H1838_cp2.2)) 1838 919 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1838_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1838_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1838_fin) true) H1838_seg1) H1838_seg2) (by decide) rfl H1838_fin ptTest_fst
noncomputable def I1838_cp1 : Nat × Nat := t7val% (fastRun pI1838 1 1060 (init pI1838) (init pI1838))
theorem I1838_seg1 : segOK pI1838 1 1060 (init pI1838) (init pI1838) I1838_cp1.1 I1838_cp1.2 = true := by
  decide +kernel
noncomputable def I1838_cp2 : Nat × Nat := t7val% (fastRun pI1838 1 1500 (init pI1838) (init pI1838))
theorem I1838_seg2 : segOK pI1838 1061 440 I1838_cp1.1 I1838_cp1.2 I1838_cp2.1 I1838_cp2.2 = true := by
  decide +kernel
theorem I1838_fin : (prmOK pI1838 1838 && intTest pI1838 (runFrom pI1838 (fmask pI1838) (cmask pI1838) (hmask pI1838) 1501 337 (true, I1838_cp2.1, I1838_cp2.2)) 1838 21 true) = true := by
  decide +kernel
theorem I1838_ok : RunOK pI1838 1838 (runFrom pI1838 (fmask pI1838) (cmask pI1838) (hmask pI1838) 1501 337 (true, I1838_cp2.1, I1838_cp2.2)) ∧ intTest pI1838 (runFrom pI1838 (fmask pI1838) (cmask pI1838) (hmask pI1838) 1501 337 (true, I1838_cp2.1, I1838_cp2.2)) 1838 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1838_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1838_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1838_fin) true) I1838_seg1) I1838_seg2) (by decide) rfl I1838_fin intTest_fst
theorem link1838 : linkOK pL1838 pH1838 pI1838 = true := by decide +kernel
theorem cvx1838 : ConvexBetweenHumps 1838 :=
  cvx_of L1838_ok H1838_ok I1838_ok link1838 (by decide)
theorem cenlink1838 : cenLinkOK pI1838 1838 = true := by decide +kernel
theorem cen1838 : CenterUniqueMin 1838 ∧ DipHyp 1838 ∧ OnePointHyps 1838 :=
  cen_of L1838_ok H1838_ok I1838_ok link1838 cenlink1838

/-! ### `N = 1839` -/

def pL1839 : Prm := ⟨80, 37, 40, 1841, 11, 18446744073709551616, 105353732370389073, 105353732370389073⟩
def pH1839 : Prm := ⟨80, 37, 40, 1841, 11, 18446744073709551616, 105354831882016849, 105354831882016849⟩
def pI1839 : Prm := ⟨68, 34, 31, 1841, 11, 18446744073709551616, 105353732370389073, 105354831882016849⟩
noncomputable def L1839_cp1 : Nat × Nat := t7val% (fastRun pL1839 1 1061 (init pL1839) (init pL1839))
theorem L1839_seg1 : segOK pL1839 1 1061 (init pL1839) (init pL1839) L1839_cp1.1 L1839_cp1.2 = true := by
  decide +kernel
noncomputable def L1839_cp2 : Nat × Nat := t7val% (fastRun pL1839 1 1501 (init pL1839) (init pL1839))
theorem L1839_seg2 : segOK pL1839 1062 440 L1839_cp1.1 L1839_cp1.2 L1839_cp2.1 L1839_cp2.2 = true := by
  decide +kernel
theorem L1839_fin : (prmOK pL1839 1839 && ptTest pL1839 (runFrom pL1839 (fmask pL1839) (cmask pL1839) (hmask pL1839) 1502 337 (true, L1839_cp2.1, L1839_cp2.2)) 1839 920 false) = true := by
  decide +kernel
theorem L1839_ok : RunOK pL1839 1839 (runFrom pL1839 (fmask pL1839) (cmask pL1839) (hmask pL1839) 1502 337 (true, L1839_cp2.1, L1839_cp2.2)) ∧ ptTest pL1839 (runFrom pL1839 (fmask pL1839) (cmask pL1839) (hmask pL1839) 1502 337 (true, L1839_cp2.1, L1839_cp2.2)) 1839 920 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1839_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1839_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1839_fin) true) L1839_seg1) L1839_seg2) (by decide) rfl L1839_fin ptTest_fst
noncomputable def H1839_cp1 : Nat × Nat := t7val% (fastRun pH1839 1 1061 (init pH1839) (init pH1839))
theorem H1839_seg1 : segOK pH1839 1 1061 (init pH1839) (init pH1839) H1839_cp1.1 H1839_cp1.2 = true := by
  decide +kernel
noncomputable def H1839_cp2 : Nat × Nat := t7val% (fastRun pH1839 1 1501 (init pH1839) (init pH1839))
theorem H1839_seg2 : segOK pH1839 1062 440 H1839_cp1.1 H1839_cp1.2 H1839_cp2.1 H1839_cp2.2 = true := by
  decide +kernel
theorem H1839_fin : (prmOK pH1839 1839 && ptTest pH1839 (runFrom pH1839 (fmask pH1839) (cmask pH1839) (hmask pH1839) 1502 337 (true, H1839_cp2.1, H1839_cp2.2)) 1839 920 true) = true := by
  decide +kernel
theorem H1839_ok : RunOK pH1839 1839 (runFrom pH1839 (fmask pH1839) (cmask pH1839) (hmask pH1839) 1502 337 (true, H1839_cp2.1, H1839_cp2.2)) ∧ ptTest pH1839 (runFrom pH1839 (fmask pH1839) (cmask pH1839) (hmask pH1839) 1502 337 (true, H1839_cp2.1, H1839_cp2.2)) 1839 920 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1839_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1839_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1839_fin) true) H1839_seg1) H1839_seg2) (by decide) rfl H1839_fin ptTest_fst
noncomputable def I1839_cp1 : Nat × Nat := t7val% (fastRun pI1839 1 1061 (init pI1839) (init pI1839))
theorem I1839_seg1 : segOK pI1839 1 1061 (init pI1839) (init pI1839) I1839_cp1.1 I1839_cp1.2 = true := by
  decide +kernel
noncomputable def I1839_cp2 : Nat × Nat := t7val% (fastRun pI1839 1 1501 (init pI1839) (init pI1839))
theorem I1839_seg2 : segOK pI1839 1062 440 I1839_cp1.1 I1839_cp1.2 I1839_cp2.1 I1839_cp2.2 = true := by
  decide +kernel
theorem I1839_fin : (prmOK pI1839 1839 && intTest pI1839 (runFrom pI1839 (fmask pI1839) (cmask pI1839) (hmask pI1839) 1502 337 (true, I1839_cp2.1, I1839_cp2.2)) 1839 21 false) = true := by
  decide +kernel
theorem I1839_ok : RunOK pI1839 1839 (runFrom pI1839 (fmask pI1839) (cmask pI1839) (hmask pI1839) 1502 337 (true, I1839_cp2.1, I1839_cp2.2)) ∧ intTest pI1839 (runFrom pI1839 (fmask pI1839) (cmask pI1839) (hmask pI1839) 1502 337 (true, I1839_cp2.1, I1839_cp2.2)) 1839 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1839_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1839_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1839_fin) true) I1839_seg1) I1839_seg2) (by decide) rfl I1839_fin intTest_fst
theorem link1839 : linkOK pL1839 pH1839 pI1839 = true := by decide +kernel
theorem cvx1839 : ConvexBetweenHumps 1839 :=
  cvx_of L1839_ok H1839_ok I1839_ok link1839 (by decide)

/-! ### `N = 1840` -/

def pL1840 : Prm := ⟨80, 37, 40, 1842, 11, 18446744073709551616, 105306757207497411, 105306757207497411⟩
def pH1840 : Prm := ⟨80, 37, 40, 1842, 11, 18446744073709551616, 105307856719125187, 105307856719125187⟩
def pI1840 : Prm := ⟨68, 34, 31, 1842, 11, 18446744073709551616, 105306757207497411, 105307856719125187⟩
noncomputable def L1840_cp1 : Nat × Nat := t7val% (fastRun pL1840 1 1061 (init pL1840) (init pL1840))
theorem L1840_seg1 : segOK pL1840 1 1061 (init pL1840) (init pL1840) L1840_cp1.1 L1840_cp1.2 = true := by
  decide +kernel
noncomputable def L1840_cp2 : Nat × Nat := t7val% (fastRun pL1840 1 1501 (init pL1840) (init pL1840))
theorem L1840_seg2 : segOK pL1840 1062 440 L1840_cp1.1 L1840_cp1.2 L1840_cp2.1 L1840_cp2.2 = true := by
  decide +kernel
theorem L1840_fin : (prmOK pL1840 1840 && ptTest pL1840 (runFrom pL1840 (fmask pL1840) (cmask pL1840) (hmask pL1840) 1502 338 (true, L1840_cp2.1, L1840_cp2.2)) 1840 920 false) = true := by
  decide +kernel
theorem L1840_ok : RunOK pL1840 1840 (runFrom pL1840 (fmask pL1840) (cmask pL1840) (hmask pL1840) 1502 338 (true, L1840_cp2.1, L1840_cp2.2)) ∧ ptTest pL1840 (runFrom pL1840 (fmask pL1840) (cmask pL1840) (hmask pL1840) 1502 338 (true, L1840_cp2.1, L1840_cp2.2)) 1840 920 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1840_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1840_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1840_fin) true) L1840_seg1) L1840_seg2) (by decide) rfl L1840_fin ptTest_fst
noncomputable def H1840_cp1 : Nat × Nat := t7val% (fastRun pH1840 1 1061 (init pH1840) (init pH1840))
theorem H1840_seg1 : segOK pH1840 1 1061 (init pH1840) (init pH1840) H1840_cp1.1 H1840_cp1.2 = true := by
  decide +kernel
noncomputable def H1840_cp2 : Nat × Nat := t7val% (fastRun pH1840 1 1501 (init pH1840) (init pH1840))
theorem H1840_seg2 : segOK pH1840 1062 440 H1840_cp1.1 H1840_cp1.2 H1840_cp2.1 H1840_cp2.2 = true := by
  decide +kernel
theorem H1840_fin : (prmOK pH1840 1840 && ptTest pH1840 (runFrom pH1840 (fmask pH1840) (cmask pH1840) (hmask pH1840) 1502 338 (true, H1840_cp2.1, H1840_cp2.2)) 1840 920 true) = true := by
  decide +kernel
theorem H1840_ok : RunOK pH1840 1840 (runFrom pH1840 (fmask pH1840) (cmask pH1840) (hmask pH1840) 1502 338 (true, H1840_cp2.1, H1840_cp2.2)) ∧ ptTest pH1840 (runFrom pH1840 (fmask pH1840) (cmask pH1840) (hmask pH1840) 1502 338 (true, H1840_cp2.1, H1840_cp2.2)) 1840 920 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1840_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1840_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1840_fin) true) H1840_seg1) H1840_seg2) (by decide) rfl H1840_fin ptTest_fst
noncomputable def I1840_cp1 : Nat × Nat := t7val% (fastRun pI1840 1 1061 (init pI1840) (init pI1840))
theorem I1840_seg1 : segOK pI1840 1 1061 (init pI1840) (init pI1840) I1840_cp1.1 I1840_cp1.2 = true := by
  decide +kernel
noncomputable def I1840_cp2 : Nat × Nat := t7val% (fastRun pI1840 1 1501 (init pI1840) (init pI1840))
theorem I1840_seg2 : segOK pI1840 1062 440 I1840_cp1.1 I1840_cp1.2 I1840_cp2.1 I1840_cp2.2 = true := by
  decide +kernel
theorem I1840_fin : (prmOK pI1840 1840 && intTest pI1840 (runFrom pI1840 (fmask pI1840) (cmask pI1840) (hmask pI1840) 1502 338 (true, I1840_cp2.1, I1840_cp2.2)) 1840 21 true) = true := by
  decide +kernel
theorem I1840_ok : RunOK pI1840 1840 (runFrom pI1840 (fmask pI1840) (cmask pI1840) (hmask pI1840) 1502 338 (true, I1840_cp2.1, I1840_cp2.2)) ∧ intTest pI1840 (runFrom pI1840 (fmask pI1840) (cmask pI1840) (hmask pI1840) 1502 338 (true, I1840_cp2.1, I1840_cp2.2)) 1840 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1840_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1840_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1840_fin) true) I1840_seg1) I1840_seg2) (by decide) rfl I1840_fin intTest_fst
theorem link1840 : linkOK pL1840 pH1840 pI1840 = true := by decide +kernel
theorem cvx1840 : ConvexBetweenHumps 1840 :=
  cvx_of L1840_ok H1840_ok I1840_ok link1840 (by decide)
theorem cenlink1840 : cenLinkOK pI1840 1840 = true := by decide +kernel
theorem cen1840 : CenterUniqueMin 1840 ∧ DipHyp 1840 ∧ OnePointHyps 1840 :=
  cen_of L1840_ok H1840_ok I1840_ok link1840 cenlink1840

/-! ### `N = 1841` -/

def pL1841 : Prm := ⟨80, 37, 40, 1843, 11, 18446744073709551616, 105259809501514393, 105259809501514393⟩
def pH1841 : Prm := ⟨80, 37, 40, 1843, 11, 18446744073709551616, 105260909013142169, 105260909013142169⟩
def pI1841 : Prm := ⟨68, 34, 31, 1843, 11, 18446744073709551616, 105259809501514393, 105260909013142169⟩
noncomputable def L1841_cp1 : Nat × Nat := t7val% (fastRun pL1841 1 1062 (init pL1841) (init pL1841))
theorem L1841_seg1 : segOK pL1841 1 1062 (init pL1841) (init pL1841) L1841_cp1.1 L1841_cp1.2 = true := by
  decide +kernel
noncomputable def L1841_cp2 : Nat × Nat := t7val% (fastRun pL1841 1 1502 (init pL1841) (init pL1841))
theorem L1841_seg2 : segOK pL1841 1063 440 L1841_cp1.1 L1841_cp1.2 L1841_cp2.1 L1841_cp2.2 = true := by
  decide +kernel
theorem L1841_fin : (prmOK pL1841 1841 && ptTest pL1841 (runFrom pL1841 (fmask pL1841) (cmask pL1841) (hmask pL1841) 1503 338 (true, L1841_cp2.1, L1841_cp2.2)) 1841 921 false) = true := by
  decide +kernel
theorem L1841_ok : RunOK pL1841 1841 (runFrom pL1841 (fmask pL1841) (cmask pL1841) (hmask pL1841) 1503 338 (true, L1841_cp2.1, L1841_cp2.2)) ∧ ptTest pL1841 (runFrom pL1841 (fmask pL1841) (cmask pL1841) (hmask pL1841) 1503 338 (true, L1841_cp2.1, L1841_cp2.2)) 1841 921 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1841_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1841_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1841_fin) true) L1841_seg1) L1841_seg2) (by decide) rfl L1841_fin ptTest_fst
noncomputable def H1841_cp1 : Nat × Nat := t7val% (fastRun pH1841 1 1062 (init pH1841) (init pH1841))
theorem H1841_seg1 : segOK pH1841 1 1062 (init pH1841) (init pH1841) H1841_cp1.1 H1841_cp1.2 = true := by
  decide +kernel
noncomputable def H1841_cp2 : Nat × Nat := t7val% (fastRun pH1841 1 1502 (init pH1841) (init pH1841))
theorem H1841_seg2 : segOK pH1841 1063 440 H1841_cp1.1 H1841_cp1.2 H1841_cp2.1 H1841_cp2.2 = true := by
  decide +kernel
theorem H1841_fin : (prmOK pH1841 1841 && ptTest pH1841 (runFrom pH1841 (fmask pH1841) (cmask pH1841) (hmask pH1841) 1503 338 (true, H1841_cp2.1, H1841_cp2.2)) 1841 921 true) = true := by
  decide +kernel
theorem H1841_ok : RunOK pH1841 1841 (runFrom pH1841 (fmask pH1841) (cmask pH1841) (hmask pH1841) 1503 338 (true, H1841_cp2.1, H1841_cp2.2)) ∧ ptTest pH1841 (runFrom pH1841 (fmask pH1841) (cmask pH1841) (hmask pH1841) 1503 338 (true, H1841_cp2.1, H1841_cp2.2)) 1841 921 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1841_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1841_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1841_fin) true) H1841_seg1) H1841_seg2) (by decide) rfl H1841_fin ptTest_fst
noncomputable def I1841_cp1 : Nat × Nat := t7val% (fastRun pI1841 1 1062 (init pI1841) (init pI1841))
theorem I1841_seg1 : segOK pI1841 1 1062 (init pI1841) (init pI1841) I1841_cp1.1 I1841_cp1.2 = true := by
  decide +kernel
noncomputable def I1841_cp2 : Nat × Nat := t7val% (fastRun pI1841 1 1502 (init pI1841) (init pI1841))
theorem I1841_seg2 : segOK pI1841 1063 440 I1841_cp1.1 I1841_cp1.2 I1841_cp2.1 I1841_cp2.2 = true := by
  decide +kernel
theorem I1841_fin : (prmOK pI1841 1841 && intTest pI1841 (runFrom pI1841 (fmask pI1841) (cmask pI1841) (hmask pI1841) 1503 338 (true, I1841_cp2.1, I1841_cp2.2)) 1841 21 false) = true := by
  decide +kernel
theorem I1841_ok : RunOK pI1841 1841 (runFrom pI1841 (fmask pI1841) (cmask pI1841) (hmask pI1841) 1503 338 (true, I1841_cp2.1, I1841_cp2.2)) ∧ intTest pI1841 (runFrom pI1841 (fmask pI1841) (cmask pI1841) (hmask pI1841) 1503 338 (true, I1841_cp2.1, I1841_cp2.2)) 1841 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1841_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1841_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1841_fin) true) I1841_seg1) I1841_seg2) (by decide) rfl I1841_fin intTest_fst
theorem link1841 : linkOK pL1841 pH1841 pI1841 = true := by decide +kernel
theorem cvx1841 : ConvexBetweenHumps 1841 :=
  cvx_of L1841_ok H1841_ok I1841_ok link1841 (by decide)

/-! ### `N = 1842` -/

def pL1842 : Prm := ⟨80, 37, 40, 1844, 11, 18446744073709551616, 105212925152017593, 105212925152017593⟩
def pH1842 : Prm := ⟨80, 37, 40, 1844, 11, 18446744073709551616, 105214024663645369, 105214024663645369⟩
def pI1842 : Prm := ⟨68, 34, 31, 1844, 11, 18446744073709551616, 105212925152017593, 105214024663645369⟩
noncomputable def L1842_cp1 : Nat × Nat := t7val% (fastRun pL1842 1 1062 (init pL1842) (init pL1842))
theorem L1842_seg1 : segOK pL1842 1 1062 (init pL1842) (init pL1842) L1842_cp1.1 L1842_cp1.2 = true := by
  decide +kernel
noncomputable def L1842_cp2 : Nat × Nat := t7val% (fastRun pL1842 1 1503 (init pL1842) (init pL1842))
theorem L1842_seg2 : segOK pL1842 1063 441 L1842_cp1.1 L1842_cp1.2 L1842_cp2.1 L1842_cp2.2 = true := by
  decide +kernel
theorem L1842_fin : (prmOK pL1842 1842 && ptTest pL1842 (runFrom pL1842 (fmask pL1842) (cmask pL1842) (hmask pL1842) 1504 338 (true, L1842_cp2.1, L1842_cp2.2)) 1842 921 false) = true := by
  decide +kernel
theorem L1842_ok : RunOK pL1842 1842 (runFrom pL1842 (fmask pL1842) (cmask pL1842) (hmask pL1842) 1504 338 (true, L1842_cp2.1, L1842_cp2.2)) ∧ ptTest pL1842 (runFrom pL1842 (fmask pL1842) (cmask pL1842) (hmask pL1842) 1504 338 (true, L1842_cp2.1, L1842_cp2.2)) 1842 921 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1842_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1842_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1842_fin) true) L1842_seg1) L1842_seg2) (by decide) rfl L1842_fin ptTest_fst
noncomputable def H1842_cp1 : Nat × Nat := t7val% (fastRun pH1842 1 1062 (init pH1842) (init pH1842))
theorem H1842_seg1 : segOK pH1842 1 1062 (init pH1842) (init pH1842) H1842_cp1.1 H1842_cp1.2 = true := by
  decide +kernel
noncomputable def H1842_cp2 : Nat × Nat := t7val% (fastRun pH1842 1 1503 (init pH1842) (init pH1842))
theorem H1842_seg2 : segOK pH1842 1063 441 H1842_cp1.1 H1842_cp1.2 H1842_cp2.1 H1842_cp2.2 = true := by
  decide +kernel
theorem H1842_fin : (prmOK pH1842 1842 && ptTest pH1842 (runFrom pH1842 (fmask pH1842) (cmask pH1842) (hmask pH1842) 1504 338 (true, H1842_cp2.1, H1842_cp2.2)) 1842 921 true) = true := by
  decide +kernel
theorem H1842_ok : RunOK pH1842 1842 (runFrom pH1842 (fmask pH1842) (cmask pH1842) (hmask pH1842) 1504 338 (true, H1842_cp2.1, H1842_cp2.2)) ∧ ptTest pH1842 (runFrom pH1842 (fmask pH1842) (cmask pH1842) (hmask pH1842) 1504 338 (true, H1842_cp2.1, H1842_cp2.2)) 1842 921 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1842_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1842_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1842_fin) true) H1842_seg1) H1842_seg2) (by decide) rfl H1842_fin ptTest_fst
noncomputable def I1842_cp1 : Nat × Nat := t7val% (fastRun pI1842 1 1062 (init pI1842) (init pI1842))
theorem I1842_seg1 : segOK pI1842 1 1062 (init pI1842) (init pI1842) I1842_cp1.1 I1842_cp1.2 = true := by
  decide +kernel
noncomputable def I1842_cp2 : Nat × Nat := t7val% (fastRun pI1842 1 1503 (init pI1842) (init pI1842))
theorem I1842_seg2 : segOK pI1842 1063 441 I1842_cp1.1 I1842_cp1.2 I1842_cp2.1 I1842_cp2.2 = true := by
  decide +kernel
theorem I1842_fin : (prmOK pI1842 1842 && intTest pI1842 (runFrom pI1842 (fmask pI1842) (cmask pI1842) (hmask pI1842) 1504 338 (true, I1842_cp2.1, I1842_cp2.2)) 1842 21 true) = true := by
  decide +kernel
theorem I1842_ok : RunOK pI1842 1842 (runFrom pI1842 (fmask pI1842) (cmask pI1842) (hmask pI1842) 1504 338 (true, I1842_cp2.1, I1842_cp2.2)) ∧ intTest pI1842 (runFrom pI1842 (fmask pI1842) (cmask pI1842) (hmask pI1842) 1504 338 (true, I1842_cp2.1, I1842_cp2.2)) 1842 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1842_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1842_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1842_fin) true) I1842_seg1) I1842_seg2) (by decide) rfl I1842_fin intTest_fst
theorem link1842 : linkOK pL1842 pH1842 pI1842 = true := by decide +kernel
theorem cvx1842 : ConvexBetweenHumps 1842 :=
  cvx_of L1842_ok H1842_ok I1842_ok link1842 (by decide)
theorem cenlink1842 : cenLinkOK pI1842 1842 = true := by decide +kernel
theorem cen1842 : CenterUniqueMin 1842 ∧ DipHyp 1842 ∧ OnePointHyps 1842 :=
  cen_of L1842_ok H1842_ok I1842_ok link1842 cenlink1842

/-! ### The range -/

theorem cvx_1832_1842 {N : ℕ} (h1 : 1832 ≤ N) (h2 : N ≤ 1842) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1836
  · by_cases h4 : N ≤ 1833
    · by_cases h6 : N ≤ 1832
      · obtain rfl : N = 1832 := by omega
        exact cvx1832
      · obtain rfl : N = 1833 := by omega
        exact cvx1833
    · by_cases h6 : N ≤ 1834
      · obtain rfl : N = 1834 := by omega
        exact cvx1834
      · by_cases h8 : N ≤ 1835
        · obtain rfl : N = 1835 := by omega
          exact cvx1835
        · obtain rfl : N = 1836 := by omega
          exact cvx1836
  · by_cases h4 : N ≤ 1839
    · by_cases h6 : N ≤ 1837
      · obtain rfl : N = 1837 := by omega
        exact cvx1837
      · by_cases h8 : N ≤ 1838
        · obtain rfl : N = 1838 := by omega
          exact cvx1838
        · obtain rfl : N = 1839 := by omega
          exact cvx1839
    · by_cases h6 : N ≤ 1840
      · obtain rfl : N = 1840 := by omega
        exact cvx1840
      · by_cases h8 : N ≤ 1841
        · obtain rfl : N = 1841 := by omega
          exact cvx1841
        · obtain rfl : N = 1842 := by omega
          exact cvx1842

theorem cen_1832_1842 {N : ℕ} (h1 : 1832 ≤ N) (h2 : N ≤ 1842) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1836
  · by_cases h4 : N ≤ 1832
    · obtain rfl : N = 1832 := by omega
      exact cen1832
    · by_cases h6 : N ≤ 1834
      · obtain rfl : N = 1834 := by omega
        exact cen1834
      · obtain rfl : N = 1836 := by omega
        exact cen1836
  · by_cases h4 : N ≤ 1838
    · obtain rfl : N = 1838 := by omega
      exact cen1838
    · by_cases h6 : N ≤ 1840
      · obtain rfl : N = 1840 := by omega
        exact cen1840
      · obtain rfl : N = 1842 := by omega
        exact cen1842

end Kagey131.PaperD.T7
