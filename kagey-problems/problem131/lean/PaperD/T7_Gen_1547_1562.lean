import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1547, …, 1562` (generated)

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

/-! ### `N = 1547` -/

def pL1547 : Prm := ⟨81, 39, 39, 1549, 11, 18446744073709551616, 121352688249562903, 121352688249562903⟩
def pH1547 : Prm := ⟨81, 39, 39, 1549, 11, 18446744073709551616, 121353787761190679, 121353787761190679⟩
def pI1547 : Prm := ⟨67, 33, 31, 1549, 11, 18446744073709551616, 121352688249562903, 121353787761190679⟩
noncomputable def L1547_cp1 : Nat × Nat := t7val% (fastRun pL1547 1 1093 (init pL1547) (init pL1547))
theorem L1547_seg1 : segOK pL1547 1 1093 (init pL1547) (init pL1547) L1547_cp1.1 L1547_cp1.2 = true := by
  decide +kernel
theorem L1547_fin : (prmOK pL1547 1547 && ptTest pL1547 (runFrom pL1547 (fmask pL1547) (cmask pL1547) (hmask pL1547) 1094 453 (true, L1547_cp1.1, L1547_cp1.2)) 1547 774 false) = true := by
  decide +kernel
theorem L1547_ok : RunOK pL1547 1547 (runFrom pL1547 (fmask pL1547) (cmask pL1547) (hmask pL1547) 1094 453 (true, L1547_cp1.1, L1547_cp1.2)) ∧ ptTest pL1547 (runFrom pL1547 (fmask pL1547) (cmask pL1547) (hmask pL1547) 1094 453 (true, L1547_cp1.1, L1547_cp1.2)) 1547 774 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1547_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1547_fin) true) L1547_seg1) (by decide) rfl L1547_fin ptTest_fst
noncomputable def H1547_cp1 : Nat × Nat := t7val% (fastRun pH1547 1 1093 (init pH1547) (init pH1547))
theorem H1547_seg1 : segOK pH1547 1 1093 (init pH1547) (init pH1547) H1547_cp1.1 H1547_cp1.2 = true := by
  decide +kernel
theorem H1547_fin : (prmOK pH1547 1547 && ptTest pH1547 (runFrom pH1547 (fmask pH1547) (cmask pH1547) (hmask pH1547) 1094 453 (true, H1547_cp1.1, H1547_cp1.2)) 1547 774 true) = true := by
  decide +kernel
theorem H1547_ok : RunOK pH1547 1547 (runFrom pH1547 (fmask pH1547) (cmask pH1547) (hmask pH1547) 1094 453 (true, H1547_cp1.1, H1547_cp1.2)) ∧ ptTest pH1547 (runFrom pH1547 (fmask pH1547) (cmask pH1547) (hmask pH1547) 1094 453 (true, H1547_cp1.1, H1547_cp1.2)) 1547 774 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1547_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1547_fin) true) H1547_seg1) (by decide) rfl H1547_fin ptTest_fst
noncomputable def I1547_cp1 : Nat × Nat := t7val% (fastRun pI1547 1 1093 (init pI1547) (init pI1547))
theorem I1547_seg1 : segOK pI1547 1 1093 (init pI1547) (init pI1547) I1547_cp1.1 I1547_cp1.2 = true := by
  decide +kernel
theorem I1547_fin : (prmOK pI1547 1547 && intTest pI1547 (runFrom pI1547 (fmask pI1547) (cmask pI1547) (hmask pI1547) 1094 453 (true, I1547_cp1.1, I1547_cp1.2)) 1547 20 false) = true := by
  decide +kernel
theorem I1547_ok : RunOK pI1547 1547 (runFrom pI1547 (fmask pI1547) (cmask pI1547) (hmask pI1547) 1094 453 (true, I1547_cp1.1, I1547_cp1.2)) ∧ intTest pI1547 (runFrom pI1547 (fmask pI1547) (cmask pI1547) (hmask pI1547) 1094 453 (true, I1547_cp1.1, I1547_cp1.2)) 1547 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1547_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1547_fin) true) I1547_seg1) (by decide) rfl I1547_fin intTest_fst
theorem link1547 : linkOK pL1547 pH1547 pI1547 = true := by decide +kernel
theorem cvx1547 : ConvexBetweenHumps 1547 :=
  cvx_of L1547_ok H1547_ok I1547_ok link1547 (by decide)

/-! ### `N = 1548` -/

def pL1548 : Prm := ⟨81, 39, 39, 1550, 11, 18446744073709551616, 121288828893995226, 121288828893995226⟩
def pH1548 : Prm := ⟨81, 39, 39, 1550, 11, 18446744073709551616, 121289928405623002, 121289928405623002⟩
def pI1548 : Prm := ⟨67, 33, 31, 1550, 11, 18446744073709551616, 121288828893995226, 121289928405623002⟩
noncomputable def L1548_cp1 : Nat × Nat := t7val% (fastRun pL1548 1 1094 (init pL1548) (init pL1548))
theorem L1548_seg1 : segOK pL1548 1 1094 (init pL1548) (init pL1548) L1548_cp1.1 L1548_cp1.2 = true := by
  decide +kernel
theorem L1548_fin : (prmOK pL1548 1548 && ptTest pL1548 (runFrom pL1548 (fmask pL1548) (cmask pL1548) (hmask pL1548) 1095 453 (true, L1548_cp1.1, L1548_cp1.2)) 1548 774 false) = true := by
  decide +kernel
theorem L1548_ok : RunOK pL1548 1548 (runFrom pL1548 (fmask pL1548) (cmask pL1548) (hmask pL1548) 1095 453 (true, L1548_cp1.1, L1548_cp1.2)) ∧ ptTest pL1548 (runFrom pL1548 (fmask pL1548) (cmask pL1548) (hmask pL1548) 1095 453 (true, L1548_cp1.1, L1548_cp1.2)) 1548 774 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1548_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1548_fin) true) L1548_seg1) (by decide) rfl L1548_fin ptTest_fst
noncomputable def H1548_cp1 : Nat × Nat := t7val% (fastRun pH1548 1 1094 (init pH1548) (init pH1548))
theorem H1548_seg1 : segOK pH1548 1 1094 (init pH1548) (init pH1548) H1548_cp1.1 H1548_cp1.2 = true := by
  decide +kernel
theorem H1548_fin : (prmOK pH1548 1548 && ptTest pH1548 (runFrom pH1548 (fmask pH1548) (cmask pH1548) (hmask pH1548) 1095 453 (true, H1548_cp1.1, H1548_cp1.2)) 1548 774 true) = true := by
  decide +kernel
theorem H1548_ok : RunOK pH1548 1548 (runFrom pH1548 (fmask pH1548) (cmask pH1548) (hmask pH1548) 1095 453 (true, H1548_cp1.1, H1548_cp1.2)) ∧ ptTest pH1548 (runFrom pH1548 (fmask pH1548) (cmask pH1548) (hmask pH1548) 1095 453 (true, H1548_cp1.1, H1548_cp1.2)) 1548 774 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1548_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1548_fin) true) H1548_seg1) (by decide) rfl H1548_fin ptTest_fst
noncomputable def I1548_cp1 : Nat × Nat := t7val% (fastRun pI1548 1 1094 (init pI1548) (init pI1548))
theorem I1548_seg1 : segOK pI1548 1 1094 (init pI1548) (init pI1548) I1548_cp1.1 I1548_cp1.2 = true := by
  decide +kernel
theorem I1548_fin : (prmOK pI1548 1548 && intTest pI1548 (runFrom pI1548 (fmask pI1548) (cmask pI1548) (hmask pI1548) 1095 453 (true, I1548_cp1.1, I1548_cp1.2)) 1548 20 true) = true := by
  decide +kernel
theorem I1548_ok : RunOK pI1548 1548 (runFrom pI1548 (fmask pI1548) (cmask pI1548) (hmask pI1548) 1095 453 (true, I1548_cp1.1, I1548_cp1.2)) ∧ intTest pI1548 (runFrom pI1548 (fmask pI1548) (cmask pI1548) (hmask pI1548) 1095 453 (true, I1548_cp1.1, I1548_cp1.2)) 1548 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1548_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1548_fin) true) I1548_seg1) (by decide) rfl I1548_fin intTest_fst
theorem link1548 : linkOK pL1548 pH1548 pI1548 = true := by decide +kernel
theorem cvx1548 : ConvexBetweenHumps 1548 :=
  cvx_of L1548_ok H1548_ok I1548_ok link1548 (by decide)
theorem cenlink1548 : cenLinkOK pI1548 1548 = true := by decide +kernel
theorem cen1548 : CenterUniqueMin 1548 ∧ DipHyp 1548 ∧ OnePointHyps 1548 :=
  cen_of L1548_ok H1548_ok I1548_ok link1548 cenlink1548

/-! ### `N = 1549` -/

def pL1549 : Prm := ⟨81, 39, 39, 1551, 11, 18446744073709551616, 121225012159353030, 121225012159353030⟩
def pH1549 : Prm := ⟨81, 39, 39, 1551, 11, 18446744073709551616, 121226111670980806, 121226111670980806⟩
def pI1549 : Prm := ⟨67, 33, 31, 1551, 11, 18446744073709551616, 121225012159353030, 121226111670980806⟩
noncomputable def L1549_cp1 : Nat × Nat := t7val% (fastRun pL1549 1 1094 (init pL1549) (init pL1549))
theorem L1549_seg1 : segOK pL1549 1 1094 (init pL1549) (init pL1549) L1549_cp1.1 L1549_cp1.2 = true := by
  decide +kernel
theorem L1549_fin : (prmOK pL1549 1549 && ptTest pL1549 (runFrom pL1549 (fmask pL1549) (cmask pL1549) (hmask pL1549) 1095 454 (true, L1549_cp1.1, L1549_cp1.2)) 1549 775 false) = true := by
  decide +kernel
theorem L1549_ok : RunOK pL1549 1549 (runFrom pL1549 (fmask pL1549) (cmask pL1549) (hmask pL1549) 1095 454 (true, L1549_cp1.1, L1549_cp1.2)) ∧ ptTest pL1549 (runFrom pL1549 (fmask pL1549) (cmask pL1549) (hmask pL1549) 1095 454 (true, L1549_cp1.1, L1549_cp1.2)) 1549 775 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1549_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1549_fin) true) L1549_seg1) (by decide) rfl L1549_fin ptTest_fst
noncomputable def H1549_cp1 : Nat × Nat := t7val% (fastRun pH1549 1 1094 (init pH1549) (init pH1549))
theorem H1549_seg1 : segOK pH1549 1 1094 (init pH1549) (init pH1549) H1549_cp1.1 H1549_cp1.2 = true := by
  decide +kernel
theorem H1549_fin : (prmOK pH1549 1549 && ptTest pH1549 (runFrom pH1549 (fmask pH1549) (cmask pH1549) (hmask pH1549) 1095 454 (true, H1549_cp1.1, H1549_cp1.2)) 1549 775 true) = true := by
  decide +kernel
theorem H1549_ok : RunOK pH1549 1549 (runFrom pH1549 (fmask pH1549) (cmask pH1549) (hmask pH1549) 1095 454 (true, H1549_cp1.1, H1549_cp1.2)) ∧ ptTest pH1549 (runFrom pH1549 (fmask pH1549) (cmask pH1549) (hmask pH1549) 1095 454 (true, H1549_cp1.1, H1549_cp1.2)) 1549 775 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1549_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1549_fin) true) H1549_seg1) (by decide) rfl H1549_fin ptTest_fst
noncomputable def I1549_cp1 : Nat × Nat := t7val% (fastRun pI1549 1 1094 (init pI1549) (init pI1549))
theorem I1549_seg1 : segOK pI1549 1 1094 (init pI1549) (init pI1549) I1549_cp1.1 I1549_cp1.2 = true := by
  decide +kernel
theorem I1549_fin : (prmOK pI1549 1549 && intTest pI1549 (runFrom pI1549 (fmask pI1549) (cmask pI1549) (hmask pI1549) 1095 454 (true, I1549_cp1.1, I1549_cp1.2)) 1549 20 false) = true := by
  decide +kernel
theorem I1549_ok : RunOK pI1549 1549 (runFrom pI1549 (fmask pI1549) (cmask pI1549) (hmask pI1549) 1095 454 (true, I1549_cp1.1, I1549_cp1.2)) ∧ intTest pI1549 (runFrom pI1549 (fmask pI1549) (cmask pI1549) (hmask pI1549) 1095 454 (true, I1549_cp1.1, I1549_cp1.2)) 1549 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1549_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1549_fin) true) I1549_seg1) (by decide) rfl I1549_fin intTest_fst
theorem link1549 : linkOK pL1549 pH1549 pI1549 = true := by decide +kernel
theorem cvx1549 : ConvexBetweenHumps 1549 :=
  cvx_of L1549_ok H1549_ok I1549_ok link1549 (by decide)

/-! ### `N = 1550` -/

def pL1550 : Prm := ⟨81, 39, 39, 1552, 11, 18446744073709551616, 121161298795874298, 121161298795874298⟩
def pH1550 : Prm := ⟨81, 39, 39, 1552, 11, 18446744073709551616, 121162398307502074, 121162398307502074⟩
def pI1550 : Prm := ⟨67, 33, 31, 1552, 11, 18446744073709551616, 121161298795874298, 121162398307502074⟩
noncomputable def L1550_cp1 : Nat × Nat := t7val% (fastRun pL1550 1 1095 (init pL1550) (init pL1550))
theorem L1550_seg1 : segOK pL1550 1 1095 (init pL1550) (init pL1550) L1550_cp1.1 L1550_cp1.2 = true := by
  decide +kernel
theorem L1550_fin : (prmOK pL1550 1550 && ptTest pL1550 (runFrom pL1550 (fmask pL1550) (cmask pL1550) (hmask pL1550) 1096 454 (true, L1550_cp1.1, L1550_cp1.2)) 1550 775 false) = true := by
  decide +kernel
theorem L1550_ok : RunOK pL1550 1550 (runFrom pL1550 (fmask pL1550) (cmask pL1550) (hmask pL1550) 1096 454 (true, L1550_cp1.1, L1550_cp1.2)) ∧ ptTest pL1550 (runFrom pL1550 (fmask pL1550) (cmask pL1550) (hmask pL1550) 1096 454 (true, L1550_cp1.1, L1550_cp1.2)) 1550 775 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1550_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1550_fin) true) L1550_seg1) (by decide) rfl L1550_fin ptTest_fst
noncomputable def H1550_cp1 : Nat × Nat := t7val% (fastRun pH1550 1 1095 (init pH1550) (init pH1550))
theorem H1550_seg1 : segOK pH1550 1 1095 (init pH1550) (init pH1550) H1550_cp1.1 H1550_cp1.2 = true := by
  decide +kernel
theorem H1550_fin : (prmOK pH1550 1550 && ptTest pH1550 (runFrom pH1550 (fmask pH1550) (cmask pH1550) (hmask pH1550) 1096 454 (true, H1550_cp1.1, H1550_cp1.2)) 1550 775 true) = true := by
  decide +kernel
theorem H1550_ok : RunOK pH1550 1550 (runFrom pH1550 (fmask pH1550) (cmask pH1550) (hmask pH1550) 1096 454 (true, H1550_cp1.1, H1550_cp1.2)) ∧ ptTest pH1550 (runFrom pH1550 (fmask pH1550) (cmask pH1550) (hmask pH1550) 1096 454 (true, H1550_cp1.1, H1550_cp1.2)) 1550 775 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1550_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1550_fin) true) H1550_seg1) (by decide) rfl H1550_fin ptTest_fst
noncomputable def I1550_cp1 : Nat × Nat := t7val% (fastRun pI1550 1 1095 (init pI1550) (init pI1550))
theorem I1550_seg1 : segOK pI1550 1 1095 (init pI1550) (init pI1550) I1550_cp1.1 I1550_cp1.2 = true := by
  decide +kernel
theorem I1550_fin : (prmOK pI1550 1550 && intTest pI1550 (runFrom pI1550 (fmask pI1550) (cmask pI1550) (hmask pI1550) 1096 454 (true, I1550_cp1.1, I1550_cp1.2)) 1550 20 true) = true := by
  decide +kernel
theorem I1550_ok : RunOK pI1550 1550 (runFrom pI1550 (fmask pI1550) (cmask pI1550) (hmask pI1550) 1096 454 (true, I1550_cp1.1, I1550_cp1.2)) ∧ intTest pI1550 (runFrom pI1550 (fmask pI1550) (cmask pI1550) (hmask pI1550) 1096 454 (true, I1550_cp1.1, I1550_cp1.2)) 1550 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1550_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1550_fin) true) I1550_seg1) (by decide) rfl I1550_fin intTest_fst
theorem link1550 : linkOK pL1550 pH1550 pI1550 = true := by decide +kernel
theorem cvx1550 : ConvexBetweenHumps 1550 :=
  cvx_of L1550_ok H1550_ok I1550_ok link1550 (by decide)
theorem cenlink1550 : cenLinkOK pI1550 1550 = true := by decide +kernel
theorem cen1550 : CenterUniqueMin 1550 ∧ DipHyp 1550 ∧ OnePointHyps 1550 :=
  cen_of L1550_ok H1550_ok I1550_ok link1550 cenlink1550

/-! ### `N = 1551` -/

def pL1551 : Prm := ⟨81, 39, 39, 1553, 11, 18446744073709551616, 121097627914564638, 121097627914564638⟩
def pH1551 : Prm := ⟨81, 39, 39, 1553, 11, 18446744073709551616, 121098727426192414, 121098727426192414⟩
def pI1551 : Prm := ⟨67, 33, 31, 1553, 11, 18446744073709551616, 121097627914564638, 121098727426192414⟩
noncomputable def L1551_cp1 : Nat × Nat := t7val% (fastRun pL1551 1 1096 (init pL1551) (init pL1551))
theorem L1551_seg1 : segOK pL1551 1 1096 (init pL1551) (init pL1551) L1551_cp1.1 L1551_cp1.2 = true := by
  decide +kernel
theorem L1551_fin : (prmOK pL1551 1551 && ptTest pL1551 (runFrom pL1551 (fmask pL1551) (cmask pL1551) (hmask pL1551) 1097 454 (true, L1551_cp1.1, L1551_cp1.2)) 1551 776 false) = true := by
  decide +kernel
theorem L1551_ok : RunOK pL1551 1551 (runFrom pL1551 (fmask pL1551) (cmask pL1551) (hmask pL1551) 1097 454 (true, L1551_cp1.1, L1551_cp1.2)) ∧ ptTest pL1551 (runFrom pL1551 (fmask pL1551) (cmask pL1551) (hmask pL1551) 1097 454 (true, L1551_cp1.1, L1551_cp1.2)) 1551 776 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1551_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1551_fin) true) L1551_seg1) (by decide) rfl L1551_fin ptTest_fst
noncomputable def H1551_cp1 : Nat × Nat := t7val% (fastRun pH1551 1 1096 (init pH1551) (init pH1551))
theorem H1551_seg1 : segOK pH1551 1 1096 (init pH1551) (init pH1551) H1551_cp1.1 H1551_cp1.2 = true := by
  decide +kernel
theorem H1551_fin : (prmOK pH1551 1551 && ptTest pH1551 (runFrom pH1551 (fmask pH1551) (cmask pH1551) (hmask pH1551) 1097 454 (true, H1551_cp1.1, H1551_cp1.2)) 1551 776 true) = true := by
  decide +kernel
theorem H1551_ok : RunOK pH1551 1551 (runFrom pH1551 (fmask pH1551) (cmask pH1551) (hmask pH1551) 1097 454 (true, H1551_cp1.1, H1551_cp1.2)) ∧ ptTest pH1551 (runFrom pH1551 (fmask pH1551) (cmask pH1551) (hmask pH1551) 1097 454 (true, H1551_cp1.1, H1551_cp1.2)) 1551 776 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1551_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1551_fin) true) H1551_seg1) (by decide) rfl H1551_fin ptTest_fst
noncomputable def I1551_cp1 : Nat × Nat := t7val% (fastRun pI1551 1 1096 (init pI1551) (init pI1551))
theorem I1551_seg1 : segOK pI1551 1 1096 (init pI1551) (init pI1551) I1551_cp1.1 I1551_cp1.2 = true := by
  decide +kernel
theorem I1551_fin : (prmOK pI1551 1551 && intTest pI1551 (runFrom pI1551 (fmask pI1551) (cmask pI1551) (hmask pI1551) 1097 454 (true, I1551_cp1.1, I1551_cp1.2)) 1551 20 false) = true := by
  decide +kernel
theorem I1551_ok : RunOK pI1551 1551 (runFrom pI1551 (fmask pI1551) (cmask pI1551) (hmask pI1551) 1097 454 (true, I1551_cp1.1, I1551_cp1.2)) ∧ intTest pI1551 (runFrom pI1551 (fmask pI1551) (cmask pI1551) (hmask pI1551) 1097 454 (true, I1551_cp1.1, I1551_cp1.2)) 1551 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1551_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1551_fin) true) I1551_seg1) (by decide) rfl I1551_fin intTest_fst
theorem link1551 : linkOK pL1551 pH1551 pI1551 = true := by decide +kernel
theorem cvx1551 : ConvexBetweenHumps 1551 :=
  cvx_of L1551_ok H1551_ok I1551_ok link1551 (by decide)

/-! ### `N = 1552` -/

def pL1552 : Prm := ⟨81, 39, 39, 1554, 11, 18446744073709551616, 121034060027256312, 121034060027256312⟩
def pH1552 : Prm := ⟨81, 39, 39, 1554, 11, 18446744073709551616, 121035159538884088, 121035159538884088⟩
def pI1552 : Prm := ⟨67, 33, 31, 1554, 11, 18446744073709551616, 121034060027256312, 121035159538884088⟩
noncomputable def L1552_cp1 : Nat × Nat := t7val% (fastRun pL1552 1 1096 (init pL1552) (init pL1552))
theorem L1552_seg1 : segOK pL1552 1 1096 (init pL1552) (init pL1552) L1552_cp1.1 L1552_cp1.2 = true := by
  decide +kernel
theorem L1552_fin : (prmOK pL1552 1552 && ptTest pL1552 (runFrom pL1552 (fmask pL1552) (cmask pL1552) (hmask pL1552) 1097 455 (true, L1552_cp1.1, L1552_cp1.2)) 1552 776 false) = true := by
  decide +kernel
theorem L1552_ok : RunOK pL1552 1552 (runFrom pL1552 (fmask pL1552) (cmask pL1552) (hmask pL1552) 1097 455 (true, L1552_cp1.1, L1552_cp1.2)) ∧ ptTest pL1552 (runFrom pL1552 (fmask pL1552) (cmask pL1552) (hmask pL1552) 1097 455 (true, L1552_cp1.1, L1552_cp1.2)) 1552 776 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1552_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1552_fin) true) L1552_seg1) (by decide) rfl L1552_fin ptTest_fst
noncomputable def H1552_cp1 : Nat × Nat := t7val% (fastRun pH1552 1 1096 (init pH1552) (init pH1552))
theorem H1552_seg1 : segOK pH1552 1 1096 (init pH1552) (init pH1552) H1552_cp1.1 H1552_cp1.2 = true := by
  decide +kernel
theorem H1552_fin : (prmOK pH1552 1552 && ptTest pH1552 (runFrom pH1552 (fmask pH1552) (cmask pH1552) (hmask pH1552) 1097 455 (true, H1552_cp1.1, H1552_cp1.2)) 1552 776 true) = true := by
  decide +kernel
theorem H1552_ok : RunOK pH1552 1552 (runFrom pH1552 (fmask pH1552) (cmask pH1552) (hmask pH1552) 1097 455 (true, H1552_cp1.1, H1552_cp1.2)) ∧ ptTest pH1552 (runFrom pH1552 (fmask pH1552) (cmask pH1552) (hmask pH1552) 1097 455 (true, H1552_cp1.1, H1552_cp1.2)) 1552 776 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1552_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1552_fin) true) H1552_seg1) (by decide) rfl H1552_fin ptTest_fst
noncomputable def I1552_cp1 : Nat × Nat := t7val% (fastRun pI1552 1 1096 (init pI1552) (init pI1552))
theorem I1552_seg1 : segOK pI1552 1 1096 (init pI1552) (init pI1552) I1552_cp1.1 I1552_cp1.2 = true := by
  decide +kernel
theorem I1552_fin : (prmOK pI1552 1552 && intTest pI1552 (runFrom pI1552 (fmask pI1552) (cmask pI1552) (hmask pI1552) 1097 455 (true, I1552_cp1.1, I1552_cp1.2)) 1552 20 true) = true := by
  decide +kernel
theorem I1552_ok : RunOK pI1552 1552 (runFrom pI1552 (fmask pI1552) (cmask pI1552) (hmask pI1552) 1097 455 (true, I1552_cp1.1, I1552_cp1.2)) ∧ intTest pI1552 (runFrom pI1552 (fmask pI1552) (cmask pI1552) (hmask pI1552) 1097 455 (true, I1552_cp1.1, I1552_cp1.2)) 1552 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1552_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1552_fin) true) I1552_seg1) (by decide) rfl I1552_fin intTest_fst
theorem link1552 : linkOK pL1552 pH1552 pI1552 = true := by decide +kernel
theorem cvx1552 : ConvexBetweenHumps 1552 :=
  cvx_of L1552_ok H1552_ok I1552_ok link1552 (by decide)
theorem cenlink1552 : cenLinkOK pI1552 1552 = true := by decide +kernel
theorem cen1552 : CenterUniqueMin 1552 ∧ DipHyp 1552 ∧ OnePointHyps 1552 :=
  cen_of L1552_ok H1552_ok I1552_ok link1552 cenlink1552

/-! ### `N = 1553` -/

def pL1553 : Prm := ⟨81, 39, 39, 1555, 11, 18446744073709551616, 120970534483987840, 120970534483987840⟩
def pH1553 : Prm := ⟨81, 39, 39, 1555, 11, 18446744073709551616, 120971633995615616, 120971633995615616⟩
def pI1553 : Prm := ⟨67, 33, 31, 1555, 11, 18446744073709551616, 120970534483987840, 120971633995615616⟩
noncomputable def L1553_cp1 : Nat × Nat := t7val% (fastRun pL1553 1 1097 (init pL1553) (init pL1553))
theorem L1553_seg1 : segOK pL1553 1 1097 (init pL1553) (init pL1553) L1553_cp1.1 L1553_cp1.2 = true := by
  decide +kernel
theorem L1553_fin : (prmOK pL1553 1553 && ptTest pL1553 (runFrom pL1553 (fmask pL1553) (cmask pL1553) (hmask pL1553) 1098 455 (true, L1553_cp1.1, L1553_cp1.2)) 1553 777 false) = true := by
  decide +kernel
theorem L1553_ok : RunOK pL1553 1553 (runFrom pL1553 (fmask pL1553) (cmask pL1553) (hmask pL1553) 1098 455 (true, L1553_cp1.1, L1553_cp1.2)) ∧ ptTest pL1553 (runFrom pL1553 (fmask pL1553) (cmask pL1553) (hmask pL1553) 1098 455 (true, L1553_cp1.1, L1553_cp1.2)) 1553 777 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1553_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1553_fin) true) L1553_seg1) (by decide) rfl L1553_fin ptTest_fst
noncomputable def H1553_cp1 : Nat × Nat := t7val% (fastRun pH1553 1 1097 (init pH1553) (init pH1553))
theorem H1553_seg1 : segOK pH1553 1 1097 (init pH1553) (init pH1553) H1553_cp1.1 H1553_cp1.2 = true := by
  decide +kernel
theorem H1553_fin : (prmOK pH1553 1553 && ptTest pH1553 (runFrom pH1553 (fmask pH1553) (cmask pH1553) (hmask pH1553) 1098 455 (true, H1553_cp1.1, H1553_cp1.2)) 1553 777 true) = true := by
  decide +kernel
theorem H1553_ok : RunOK pH1553 1553 (runFrom pH1553 (fmask pH1553) (cmask pH1553) (hmask pH1553) 1098 455 (true, H1553_cp1.1, H1553_cp1.2)) ∧ ptTest pH1553 (runFrom pH1553 (fmask pH1553) (cmask pH1553) (hmask pH1553) 1098 455 (true, H1553_cp1.1, H1553_cp1.2)) 1553 777 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1553_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1553_fin) true) H1553_seg1) (by decide) rfl H1553_fin ptTest_fst
noncomputable def I1553_cp1 : Nat × Nat := t7val% (fastRun pI1553 1 1097 (init pI1553) (init pI1553))
theorem I1553_seg1 : segOK pI1553 1 1097 (init pI1553) (init pI1553) I1553_cp1.1 I1553_cp1.2 = true := by
  decide +kernel
theorem I1553_fin : (prmOK pI1553 1553 && intTest pI1553 (runFrom pI1553 (fmask pI1553) (cmask pI1553) (hmask pI1553) 1098 455 (true, I1553_cp1.1, I1553_cp1.2)) 1553 20 false) = true := by
  decide +kernel
theorem I1553_ok : RunOK pI1553 1553 (runFrom pI1553 (fmask pI1553) (cmask pI1553) (hmask pI1553) 1098 455 (true, I1553_cp1.1, I1553_cp1.2)) ∧ intTest pI1553 (runFrom pI1553 (fmask pI1553) (cmask pI1553) (hmask pI1553) 1098 455 (true, I1553_cp1.1, I1553_cp1.2)) 1553 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1553_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1553_fin) true) I1553_seg1) (by decide) rfl I1553_fin intTest_fst
theorem link1553 : linkOK pL1553 pH1553 pI1553 = true := by decide +kernel
theorem cvx1553 : ConvexBetweenHumps 1553 :=
  cvx_of L1553_ok H1553_ok I1553_ok link1553 (by decide)

/-! ### `N = 1554` -/

def pL1554 : Prm := ⟨81, 39, 39, 1556, 11, 18446744073709551616, 120907111559384800, 120907111559384800⟩
def pH1554 : Prm := ⟨81, 39, 39, 1556, 11, 18446744073709551616, 120908211071012576, 120908211071012576⟩
def pI1554 : Prm := ⟨67, 33, 31, 1556, 11, 18446744073709551616, 120907111559384800, 120908211071012576⟩
noncomputable def L1554_cp1 : Nat × Nat := t7val% (fastRun pL1554 1 1098 (init pL1554) (init pL1554))
theorem L1554_seg1 : segOK pL1554 1 1098 (init pL1554) (init pL1554) L1554_cp1.1 L1554_cp1.2 = true := by
  decide +kernel
theorem L1554_fin : (prmOK pL1554 1554 && ptTest pL1554 (runFrom pL1554 (fmask pL1554) (cmask pL1554) (hmask pL1554) 1099 455 (true, L1554_cp1.1, L1554_cp1.2)) 1554 777 false) = true := by
  decide +kernel
theorem L1554_ok : RunOK pL1554 1554 (runFrom pL1554 (fmask pL1554) (cmask pL1554) (hmask pL1554) 1099 455 (true, L1554_cp1.1, L1554_cp1.2)) ∧ ptTest pL1554 (runFrom pL1554 (fmask pL1554) (cmask pL1554) (hmask pL1554) 1099 455 (true, L1554_cp1.1, L1554_cp1.2)) 1554 777 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1554_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1554_fin) true) L1554_seg1) (by decide) rfl L1554_fin ptTest_fst
noncomputable def H1554_cp1 : Nat × Nat := t7val% (fastRun pH1554 1 1098 (init pH1554) (init pH1554))
theorem H1554_seg1 : segOK pH1554 1 1098 (init pH1554) (init pH1554) H1554_cp1.1 H1554_cp1.2 = true := by
  decide +kernel
theorem H1554_fin : (prmOK pH1554 1554 && ptTest pH1554 (runFrom pH1554 (fmask pH1554) (cmask pH1554) (hmask pH1554) 1099 455 (true, H1554_cp1.1, H1554_cp1.2)) 1554 777 true) = true := by
  decide +kernel
theorem H1554_ok : RunOK pH1554 1554 (runFrom pH1554 (fmask pH1554) (cmask pH1554) (hmask pH1554) 1099 455 (true, H1554_cp1.1, H1554_cp1.2)) ∧ ptTest pH1554 (runFrom pH1554 (fmask pH1554) (cmask pH1554) (hmask pH1554) 1099 455 (true, H1554_cp1.1, H1554_cp1.2)) 1554 777 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1554_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1554_fin) true) H1554_seg1) (by decide) rfl H1554_fin ptTest_fst
noncomputable def I1554_cp1 : Nat × Nat := t7val% (fastRun pI1554 1 1098 (init pI1554) (init pI1554))
theorem I1554_seg1 : segOK pI1554 1 1098 (init pI1554) (init pI1554) I1554_cp1.1 I1554_cp1.2 = true := by
  decide +kernel
theorem I1554_fin : (prmOK pI1554 1554 && intTest pI1554 (runFrom pI1554 (fmask pI1554) (cmask pI1554) (hmask pI1554) 1099 455 (true, I1554_cp1.1, I1554_cp1.2)) 1554 20 true) = true := by
  decide +kernel
theorem I1554_ok : RunOK pI1554 1554 (runFrom pI1554 (fmask pI1554) (cmask pI1554) (hmask pI1554) 1099 455 (true, I1554_cp1.1, I1554_cp1.2)) ∧ intTest pI1554 (runFrom pI1554 (fmask pI1554) (cmask pI1554) (hmask pI1554) 1099 455 (true, I1554_cp1.1, I1554_cp1.2)) 1554 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1554_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1554_fin) true) I1554_seg1) (by decide) rfl I1554_fin intTest_fst
theorem link1554 : linkOK pL1554 pH1554 pI1554 = true := by decide +kernel
theorem cvx1554 : ConvexBetweenHumps 1554 :=
  cvx_of L1554_ok H1554_ok I1554_ok link1554 (by decide)
theorem cenlink1554 : cenLinkOK pI1554 1554 = true := by decide +kernel
theorem cen1554 : CenterUniqueMin 1554 ∧ DipHyp 1554 ∧ OnePointHyps 1554 :=
  cen_of L1554_ok H1554_ok I1554_ok link1554 cenlink1554

/-! ### `N = 1555` -/

def pL1555 : Prm := ⟨81, 39, 39, 1557, 11, 18446744073709551616, 120843730841319582, 120843730841319582⟩
def pH1555 : Prm := ⟨81, 39, 39, 1557, 11, 18446744073709551616, 120844830352947358, 120844830352947358⟩
def pI1555 : Prm := ⟨67, 33, 31, 1557, 11, 18446744073709551616, 120843730841319582, 120844830352947358⟩
noncomputable def L1555_cp1 : Nat × Nat := t7val% (fastRun pL1555 1 1099 (init pL1555) (init pL1555))
theorem L1555_seg1 : segOK pL1555 1 1099 (init pL1555) (init pL1555) L1555_cp1.1 L1555_cp1.2 = true := by
  decide +kernel
theorem L1555_fin : (prmOK pL1555 1555 && ptTest pL1555 (runFrom pL1555 (fmask pL1555) (cmask pL1555) (hmask pL1555) 1100 455 (true, L1555_cp1.1, L1555_cp1.2)) 1555 778 false) = true := by
  decide +kernel
theorem L1555_ok : RunOK pL1555 1555 (runFrom pL1555 (fmask pL1555) (cmask pL1555) (hmask pL1555) 1100 455 (true, L1555_cp1.1, L1555_cp1.2)) ∧ ptTest pL1555 (runFrom pL1555 (fmask pL1555) (cmask pL1555) (hmask pL1555) 1100 455 (true, L1555_cp1.1, L1555_cp1.2)) 1555 778 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1555_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1555_fin) true) L1555_seg1) (by decide) rfl L1555_fin ptTest_fst
noncomputable def H1555_cp1 : Nat × Nat := t7val% (fastRun pH1555 1 1099 (init pH1555) (init pH1555))
theorem H1555_seg1 : segOK pH1555 1 1099 (init pH1555) (init pH1555) H1555_cp1.1 H1555_cp1.2 = true := by
  decide +kernel
theorem H1555_fin : (prmOK pH1555 1555 && ptTest pH1555 (runFrom pH1555 (fmask pH1555) (cmask pH1555) (hmask pH1555) 1100 455 (true, H1555_cp1.1, H1555_cp1.2)) 1555 778 true) = true := by
  decide +kernel
theorem H1555_ok : RunOK pH1555 1555 (runFrom pH1555 (fmask pH1555) (cmask pH1555) (hmask pH1555) 1100 455 (true, H1555_cp1.1, H1555_cp1.2)) ∧ ptTest pH1555 (runFrom pH1555 (fmask pH1555) (cmask pH1555) (hmask pH1555) 1100 455 (true, H1555_cp1.1, H1555_cp1.2)) 1555 778 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1555_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1555_fin) true) H1555_seg1) (by decide) rfl H1555_fin ptTest_fst
noncomputable def I1555_cp1 : Nat × Nat := t7val% (fastRun pI1555 1 1099 (init pI1555) (init pI1555))
theorem I1555_seg1 : segOK pI1555 1 1099 (init pI1555) (init pI1555) I1555_cp1.1 I1555_cp1.2 = true := by
  decide +kernel
theorem I1555_fin : (prmOK pI1555 1555 && intTest pI1555 (runFrom pI1555 (fmask pI1555) (cmask pI1555) (hmask pI1555) 1100 455 (true, I1555_cp1.1, I1555_cp1.2)) 1555 20 false) = true := by
  decide +kernel
theorem I1555_ok : RunOK pI1555 1555 (runFrom pI1555 (fmask pI1555) (cmask pI1555) (hmask pI1555) 1100 455 (true, I1555_cp1.1, I1555_cp1.2)) ∧ intTest pI1555 (runFrom pI1555 (fmask pI1555) (cmask pI1555) (hmask pI1555) 1100 455 (true, I1555_cp1.1, I1555_cp1.2)) 1555 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1555_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1555_fin) true) I1555_seg1) (by decide) rfl I1555_fin intTest_fst
theorem link1555 : linkOK pL1555 pH1555 pI1555 = true := by decide +kernel
theorem cvx1555 : ConvexBetweenHumps 1555 :=
  cvx_of L1555_ok H1555_ok I1555_ok link1555 (by decide)

/-! ### `N = 1556` -/

def pL1556 : Prm := ⟨81, 39, 39, 1558, 11, 18446744073709551616, 120780452368447017, 120780452368447017⟩
def pH1556 : Prm := ⟨81, 39, 39, 1558, 11, 18446744073709551616, 120781551880074793, 120781551880074793⟩
def pI1556 : Prm := ⟨67, 33, 31, 1558, 11, 18446744073709551616, 120780452368447017, 120781551880074793⟩
noncomputable def L1556_cp1 : Nat × Nat := t7val% (fastRun pL1556 1 1099 (init pL1556) (init pL1556))
theorem L1556_seg1 : segOK pL1556 1 1099 (init pL1556) (init pL1556) L1556_cp1.1 L1556_cp1.2 = true := by
  decide +kernel
theorem L1556_fin : (prmOK pL1556 1556 && ptTest pL1556 (runFrom pL1556 (fmask pL1556) (cmask pL1556) (hmask pL1556) 1100 456 (true, L1556_cp1.1, L1556_cp1.2)) 1556 778 false) = true := by
  decide +kernel
theorem L1556_ok : RunOK pL1556 1556 (runFrom pL1556 (fmask pL1556) (cmask pL1556) (hmask pL1556) 1100 456 (true, L1556_cp1.1, L1556_cp1.2)) ∧ ptTest pL1556 (runFrom pL1556 (fmask pL1556) (cmask pL1556) (hmask pL1556) 1100 456 (true, L1556_cp1.1, L1556_cp1.2)) 1556 778 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1556_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1556_fin) true) L1556_seg1) (by decide) rfl L1556_fin ptTest_fst
noncomputable def H1556_cp1 : Nat × Nat := t7val% (fastRun pH1556 1 1099 (init pH1556) (init pH1556))
theorem H1556_seg1 : segOK pH1556 1 1099 (init pH1556) (init pH1556) H1556_cp1.1 H1556_cp1.2 = true := by
  decide +kernel
theorem H1556_fin : (prmOK pH1556 1556 && ptTest pH1556 (runFrom pH1556 (fmask pH1556) (cmask pH1556) (hmask pH1556) 1100 456 (true, H1556_cp1.1, H1556_cp1.2)) 1556 778 true) = true := by
  decide +kernel
theorem H1556_ok : RunOK pH1556 1556 (runFrom pH1556 (fmask pH1556) (cmask pH1556) (hmask pH1556) 1100 456 (true, H1556_cp1.1, H1556_cp1.2)) ∧ ptTest pH1556 (runFrom pH1556 (fmask pH1556) (cmask pH1556) (hmask pH1556) 1100 456 (true, H1556_cp1.1, H1556_cp1.2)) 1556 778 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1556_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1556_fin) true) H1556_seg1) (by decide) rfl H1556_fin ptTest_fst
noncomputable def I1556_cp1 : Nat × Nat := t7val% (fastRun pI1556 1 1099 (init pI1556) (init pI1556))
theorem I1556_seg1 : segOK pI1556 1 1099 (init pI1556) (init pI1556) I1556_cp1.1 I1556_cp1.2 = true := by
  decide +kernel
theorem I1556_fin : (prmOK pI1556 1556 && intTest pI1556 (runFrom pI1556 (fmask pI1556) (cmask pI1556) (hmask pI1556) 1100 456 (true, I1556_cp1.1, I1556_cp1.2)) 1556 20 true) = true := by
  decide +kernel
theorem I1556_ok : RunOK pI1556 1556 (runFrom pI1556 (fmask pI1556) (cmask pI1556) (hmask pI1556) 1100 456 (true, I1556_cp1.1, I1556_cp1.2)) ∧ intTest pI1556 (runFrom pI1556 (fmask pI1556) (cmask pI1556) (hmask pI1556) 1100 456 (true, I1556_cp1.1, I1556_cp1.2)) 1556 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1556_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1556_fin) true) I1556_seg1) (by decide) rfl I1556_fin intTest_fst
theorem link1556 : linkOK pL1556 pH1556 pI1556 = true := by decide +kernel
theorem cvx1556 : ConvexBetweenHumps 1556 :=
  cvx_of L1556_ok H1556_ok I1556_ok link1556 (by decide)
theorem cenlink1556 : cenLinkOK pI1556 1556 = true := by decide +kernel
theorem cen1556 : CenterUniqueMin 1556 ∧ DipHyp 1556 ∧ OnePointHyps 1556 :=
  cen_of L1556_ok H1556_ok I1556_ok link1556 cenlink1556

/-! ### `N = 1557` -/

def pL1557 : Prm := ⟨81, 39, 39, 1559, 11, 18446744073709551616, 120717215965200540, 120717215965200540⟩
def pH1557 : Prm := ⟨81, 39, 39, 1559, 11, 18446744073709551616, 120718315476828316, 120718315476828316⟩
def pI1557 : Prm := ⟨67, 33, 31, 1559, 11, 18446744073709551616, 120717215965200540, 120718315476828316⟩
noncomputable def L1557_cp1 : Nat × Nat := t7val% (fastRun pL1557 1 1100 (init pL1557) (init pL1557))
theorem L1557_seg1 : segOK pL1557 1 1100 (init pL1557) (init pL1557) L1557_cp1.1 L1557_cp1.2 = true := by
  decide +kernel
theorem L1557_fin : (prmOK pL1557 1557 && ptTest pL1557 (runFrom pL1557 (fmask pL1557) (cmask pL1557) (hmask pL1557) 1101 456 (true, L1557_cp1.1, L1557_cp1.2)) 1557 779 false) = true := by
  decide +kernel
theorem L1557_ok : RunOK pL1557 1557 (runFrom pL1557 (fmask pL1557) (cmask pL1557) (hmask pL1557) 1101 456 (true, L1557_cp1.1, L1557_cp1.2)) ∧ ptTest pL1557 (runFrom pL1557 (fmask pL1557) (cmask pL1557) (hmask pL1557) 1101 456 (true, L1557_cp1.1, L1557_cp1.2)) 1557 779 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1557_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1557_fin) true) L1557_seg1) (by decide) rfl L1557_fin ptTest_fst
noncomputable def H1557_cp1 : Nat × Nat := t7val% (fastRun pH1557 1 1100 (init pH1557) (init pH1557))
theorem H1557_seg1 : segOK pH1557 1 1100 (init pH1557) (init pH1557) H1557_cp1.1 H1557_cp1.2 = true := by
  decide +kernel
theorem H1557_fin : (prmOK pH1557 1557 && ptTest pH1557 (runFrom pH1557 (fmask pH1557) (cmask pH1557) (hmask pH1557) 1101 456 (true, H1557_cp1.1, H1557_cp1.2)) 1557 779 true) = true := by
  decide +kernel
theorem H1557_ok : RunOK pH1557 1557 (runFrom pH1557 (fmask pH1557) (cmask pH1557) (hmask pH1557) 1101 456 (true, H1557_cp1.1, H1557_cp1.2)) ∧ ptTest pH1557 (runFrom pH1557 (fmask pH1557) (cmask pH1557) (hmask pH1557) 1101 456 (true, H1557_cp1.1, H1557_cp1.2)) 1557 779 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1557_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1557_fin) true) H1557_seg1) (by decide) rfl H1557_fin ptTest_fst
noncomputable def I1557_cp1 : Nat × Nat := t7val% (fastRun pI1557 1 1100 (init pI1557) (init pI1557))
theorem I1557_seg1 : segOK pI1557 1 1100 (init pI1557) (init pI1557) I1557_cp1.1 I1557_cp1.2 = true := by
  decide +kernel
theorem I1557_fin : (prmOK pI1557 1557 && intTest pI1557 (runFrom pI1557 (fmask pI1557) (cmask pI1557) (hmask pI1557) 1101 456 (true, I1557_cp1.1, I1557_cp1.2)) 1557 20 false) = true := by
  decide +kernel
theorem I1557_ok : RunOK pI1557 1557 (runFrom pI1557 (fmask pI1557) (cmask pI1557) (hmask pI1557) 1101 456 (true, I1557_cp1.1, I1557_cp1.2)) ∧ intTest pI1557 (runFrom pI1557 (fmask pI1557) (cmask pI1557) (hmask pI1557) 1101 456 (true, I1557_cp1.1, I1557_cp1.2)) 1557 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1557_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1557_fin) true) I1557_seg1) (by decide) rfl I1557_fin intTest_fst
theorem link1557 : linkOK pL1557 pH1557 pI1557 = true := by decide +kernel
theorem cvx1557 : ConvexBetweenHumps 1557 :=
  cvx_of L1557_ok H1557_ok I1557_ok link1557 (by decide)

/-! ### `N = 1558` -/

def pL1558 : Prm := ⟨81, 39, 39, 1560, 11, 18446744073709551616, 120654081435518610, 120654081435518610⟩
def pH1558 : Prm := ⟨81, 39, 39, 1560, 11, 18446744073709551616, 120655180947146386, 120655180947146386⟩
def pI1558 : Prm := ⟨67, 33, 31, 1560, 11, 18446744073709551616, 120654081435518610, 120655180947146386⟩
noncomputable def L1558_cp1 : Nat × Nat := t7val% (fastRun pL1558 1 1101 (init pL1558) (init pL1558))
theorem L1558_seg1 : segOK pL1558 1 1101 (init pL1558) (init pL1558) L1558_cp1.1 L1558_cp1.2 = true := by
  decide +kernel
theorem L1558_fin : (prmOK pL1558 1558 && ptTest pL1558 (runFrom pL1558 (fmask pL1558) (cmask pL1558) (hmask pL1558) 1102 456 (true, L1558_cp1.1, L1558_cp1.2)) 1558 779 false) = true := by
  decide +kernel
theorem L1558_ok : RunOK pL1558 1558 (runFrom pL1558 (fmask pL1558) (cmask pL1558) (hmask pL1558) 1102 456 (true, L1558_cp1.1, L1558_cp1.2)) ∧ ptTest pL1558 (runFrom pL1558 (fmask pL1558) (cmask pL1558) (hmask pL1558) 1102 456 (true, L1558_cp1.1, L1558_cp1.2)) 1558 779 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1558_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1558_fin) true) L1558_seg1) (by decide) rfl L1558_fin ptTest_fst
noncomputable def H1558_cp1 : Nat × Nat := t7val% (fastRun pH1558 1 1101 (init pH1558) (init pH1558))
theorem H1558_seg1 : segOK pH1558 1 1101 (init pH1558) (init pH1558) H1558_cp1.1 H1558_cp1.2 = true := by
  decide +kernel
theorem H1558_fin : (prmOK pH1558 1558 && ptTest pH1558 (runFrom pH1558 (fmask pH1558) (cmask pH1558) (hmask pH1558) 1102 456 (true, H1558_cp1.1, H1558_cp1.2)) 1558 779 true) = true := by
  decide +kernel
theorem H1558_ok : RunOK pH1558 1558 (runFrom pH1558 (fmask pH1558) (cmask pH1558) (hmask pH1558) 1102 456 (true, H1558_cp1.1, H1558_cp1.2)) ∧ ptTest pH1558 (runFrom pH1558 (fmask pH1558) (cmask pH1558) (hmask pH1558) 1102 456 (true, H1558_cp1.1, H1558_cp1.2)) 1558 779 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1558_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1558_fin) true) H1558_seg1) (by decide) rfl H1558_fin ptTest_fst
noncomputable def I1558_cp1 : Nat × Nat := t7val% (fastRun pI1558 1 1101 (init pI1558) (init pI1558))
theorem I1558_seg1 : segOK pI1558 1 1101 (init pI1558) (init pI1558) I1558_cp1.1 I1558_cp1.2 = true := by
  decide +kernel
theorem I1558_fin : (prmOK pI1558 1558 && intTest pI1558 (runFrom pI1558 (fmask pI1558) (cmask pI1558) (hmask pI1558) 1102 456 (true, I1558_cp1.1, I1558_cp1.2)) 1558 20 true) = true := by
  decide +kernel
theorem I1558_ok : RunOK pI1558 1558 (runFrom pI1558 (fmask pI1558) (cmask pI1558) (hmask pI1558) 1102 456 (true, I1558_cp1.1, I1558_cp1.2)) ∧ intTest pI1558 (runFrom pI1558 (fmask pI1558) (cmask pI1558) (hmask pI1558) 1102 456 (true, I1558_cp1.1, I1558_cp1.2)) 1558 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1558_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1558_fin) true) I1558_seg1) (by decide) rfl I1558_fin intTest_fst
theorem link1558 : linkOK pL1558 pH1558 pI1558 = true := by decide +kernel
theorem cvx1558 : ConvexBetweenHumps 1558 :=
  cvx_of L1558_ok H1558_ok I1558_ok link1558 (by decide)
theorem cenlink1558 : cenLinkOK pI1558 1558 = true := by decide +kernel
theorem cen1558 : CenterUniqueMin 1558 ∧ DipHyp 1558 ∧ OnePointHyps 1558 :=
  cen_of L1558_ok H1558_ok I1558_ok link1558 cenlink1558

/-! ### `N = 1559` -/

def pL1559 : Prm := ⟨81, 39, 39, 1561, 11, 18446744073709551616, 120590988839141328, 120590988839141328⟩
def pH1559 : Prm := ⟨81, 39, 39, 1561, 11, 18446744073709551616, 120592088350769104, 120592088350769104⟩
def pI1559 : Prm := ⟨67, 33, 31, 1561, 11, 18446744073709551616, 120590988839141328, 120592088350769104⟩
noncomputable def L1559_cp1 : Nat × Nat := t7val% (fastRun pL1559 1 1101 (init pL1559) (init pL1559))
theorem L1559_seg1 : segOK pL1559 1 1101 (init pL1559) (init pL1559) L1559_cp1.1 L1559_cp1.2 = true := by
  decide +kernel
theorem L1559_fin : (prmOK pL1559 1559 && ptTest pL1559 (runFrom pL1559 (fmask pL1559) (cmask pL1559) (hmask pL1559) 1102 457 (true, L1559_cp1.1, L1559_cp1.2)) 1559 780 false) = true := by
  decide +kernel
theorem L1559_ok : RunOK pL1559 1559 (runFrom pL1559 (fmask pL1559) (cmask pL1559) (hmask pL1559) 1102 457 (true, L1559_cp1.1, L1559_cp1.2)) ∧ ptTest pL1559 (runFrom pL1559 (fmask pL1559) (cmask pL1559) (hmask pL1559) 1102 457 (true, L1559_cp1.1, L1559_cp1.2)) 1559 780 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1559_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1559_fin) true) L1559_seg1) (by decide) rfl L1559_fin ptTest_fst
noncomputable def H1559_cp1 : Nat × Nat := t7val% (fastRun pH1559 1 1101 (init pH1559) (init pH1559))
theorem H1559_seg1 : segOK pH1559 1 1101 (init pH1559) (init pH1559) H1559_cp1.1 H1559_cp1.2 = true := by
  decide +kernel
theorem H1559_fin : (prmOK pH1559 1559 && ptTest pH1559 (runFrom pH1559 (fmask pH1559) (cmask pH1559) (hmask pH1559) 1102 457 (true, H1559_cp1.1, H1559_cp1.2)) 1559 780 true) = true := by
  decide +kernel
theorem H1559_ok : RunOK pH1559 1559 (runFrom pH1559 (fmask pH1559) (cmask pH1559) (hmask pH1559) 1102 457 (true, H1559_cp1.1, H1559_cp1.2)) ∧ ptTest pH1559 (runFrom pH1559 (fmask pH1559) (cmask pH1559) (hmask pH1559) 1102 457 (true, H1559_cp1.1, H1559_cp1.2)) 1559 780 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1559_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1559_fin) true) H1559_seg1) (by decide) rfl H1559_fin ptTest_fst
noncomputable def I1559_cp1 : Nat × Nat := t7val% (fastRun pI1559 1 1101 (init pI1559) (init pI1559))
theorem I1559_seg1 : segOK pI1559 1 1101 (init pI1559) (init pI1559) I1559_cp1.1 I1559_cp1.2 = true := by
  decide +kernel
theorem I1559_fin : (prmOK pI1559 1559 && intTest pI1559 (runFrom pI1559 (fmask pI1559) (cmask pI1559) (hmask pI1559) 1102 457 (true, I1559_cp1.1, I1559_cp1.2)) 1559 20 false) = true := by
  decide +kernel
theorem I1559_ok : RunOK pI1559 1559 (runFrom pI1559 (fmask pI1559) (cmask pI1559) (hmask pI1559) 1102 457 (true, I1559_cp1.1, I1559_cp1.2)) ∧ intTest pI1559 (runFrom pI1559 (fmask pI1559) (cmask pI1559) (hmask pI1559) 1102 457 (true, I1559_cp1.1, I1559_cp1.2)) 1559 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1559_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1559_fin) true) I1559_seg1) (by decide) rfl I1559_fin intTest_fst
theorem link1559 : linkOK pL1559 pH1559 pI1559 = true := by decide +kernel
theorem cvx1559 : ConvexBetweenHumps 1559 :=
  cvx_of L1559_ok H1559_ok I1559_ok link1559 (by decide)

/-! ### `N = 1560` -/

def pL1560 : Prm := ⟨81, 39, 39, 1562, 11, 18446744073709551616, 120527997746508267, 120527997746508267⟩
def pH1560 : Prm := ⟨81, 39, 39, 1562, 11, 18446744073709551616, 120529097258136043, 120529097258136043⟩
def pI1560 : Prm := ⟨67, 33, 31, 1562, 11, 18446744073709551616, 120527997746508267, 120529097258136043⟩
noncomputable def L1560_cp1 : Nat × Nat := t7val% (fastRun pL1560 1 1102 (init pL1560) (init pL1560))
theorem L1560_seg1 : segOK pL1560 1 1102 (init pL1560) (init pL1560) L1560_cp1.1 L1560_cp1.2 = true := by
  decide +kernel
theorem L1560_fin : (prmOK pL1560 1560 && ptTest pL1560 (runFrom pL1560 (fmask pL1560) (cmask pL1560) (hmask pL1560) 1103 457 (true, L1560_cp1.1, L1560_cp1.2)) 1560 780 false) = true := by
  decide +kernel
theorem L1560_ok : RunOK pL1560 1560 (runFrom pL1560 (fmask pL1560) (cmask pL1560) (hmask pL1560) 1103 457 (true, L1560_cp1.1, L1560_cp1.2)) ∧ ptTest pL1560 (runFrom pL1560 (fmask pL1560) (cmask pL1560) (hmask pL1560) 1103 457 (true, L1560_cp1.1, L1560_cp1.2)) 1560 780 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1560_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1560_fin) true) L1560_seg1) (by decide) rfl L1560_fin ptTest_fst
noncomputable def H1560_cp1 : Nat × Nat := t7val% (fastRun pH1560 1 1102 (init pH1560) (init pH1560))
theorem H1560_seg1 : segOK pH1560 1 1102 (init pH1560) (init pH1560) H1560_cp1.1 H1560_cp1.2 = true := by
  decide +kernel
theorem H1560_fin : (prmOK pH1560 1560 && ptTest pH1560 (runFrom pH1560 (fmask pH1560) (cmask pH1560) (hmask pH1560) 1103 457 (true, H1560_cp1.1, H1560_cp1.2)) 1560 780 true) = true := by
  decide +kernel
theorem H1560_ok : RunOK pH1560 1560 (runFrom pH1560 (fmask pH1560) (cmask pH1560) (hmask pH1560) 1103 457 (true, H1560_cp1.1, H1560_cp1.2)) ∧ ptTest pH1560 (runFrom pH1560 (fmask pH1560) (cmask pH1560) (hmask pH1560) 1103 457 (true, H1560_cp1.1, H1560_cp1.2)) 1560 780 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1560_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1560_fin) true) H1560_seg1) (by decide) rfl H1560_fin ptTest_fst
noncomputable def I1560_cp1 : Nat × Nat := t7val% (fastRun pI1560 1 1102 (init pI1560) (init pI1560))
theorem I1560_seg1 : segOK pI1560 1 1102 (init pI1560) (init pI1560) I1560_cp1.1 I1560_cp1.2 = true := by
  decide +kernel
theorem I1560_fin : (prmOK pI1560 1560 && intTest pI1560 (runFrom pI1560 (fmask pI1560) (cmask pI1560) (hmask pI1560) 1103 457 (true, I1560_cp1.1, I1560_cp1.2)) 1560 20 true) = true := by
  decide +kernel
theorem I1560_ok : RunOK pI1560 1560 (runFrom pI1560 (fmask pI1560) (cmask pI1560) (hmask pI1560) 1103 457 (true, I1560_cp1.1, I1560_cp1.2)) ∧ intTest pI1560 (runFrom pI1560 (fmask pI1560) (cmask pI1560) (hmask pI1560) 1103 457 (true, I1560_cp1.1, I1560_cp1.2)) 1560 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1560_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1560_fin) true) I1560_seg1) (by decide) rfl I1560_fin intTest_fst
theorem link1560 : linkOK pL1560 pH1560 pI1560 = true := by decide +kernel
theorem cvx1560 : ConvexBetweenHumps 1560 :=
  cvx_of L1560_ok H1560_ok I1560_ok link1560 (by decide)
theorem cenlink1560 : cenLinkOK pI1560 1560 = true := by decide +kernel
theorem cen1560 : CenterUniqueMin 1560 ∧ DipHyp 1560 ∧ OnePointHyps 1560 :=
  cen_of L1560_ok H1560_ok I1560_ok link1560 cenlink1560

/-! ### `N = 1561` -/

def pL1561 : Prm := ⟨81, 39, 39, 1563, 11, 18446744073709551616, 120465048451467159, 120465048451467159⟩
def pH1561 : Prm := ⟨81, 39, 39, 1563, 11, 18446744073709551616, 120466147963094935, 120466147963094935⟩
def pI1561 : Prm := ⟨67, 33, 31, 1563, 11, 18446744073709551616, 120465048451467159, 120466147963094935⟩
noncomputable def L1561_cp1 : Nat × Nat := t7val% (fastRun pL1561 1 1103 (init pL1561) (init pL1561))
theorem L1561_seg1 : segOK pL1561 1 1103 (init pL1561) (init pL1561) L1561_cp1.1 L1561_cp1.2 = true := by
  decide +kernel
theorem L1561_fin : (prmOK pL1561 1561 && ptTest pL1561 (runFrom pL1561 (fmask pL1561) (cmask pL1561) (hmask pL1561) 1104 457 (true, L1561_cp1.1, L1561_cp1.2)) 1561 781 false) = true := by
  decide +kernel
theorem L1561_ok : RunOK pL1561 1561 (runFrom pL1561 (fmask pL1561) (cmask pL1561) (hmask pL1561) 1104 457 (true, L1561_cp1.1, L1561_cp1.2)) ∧ ptTest pL1561 (runFrom pL1561 (fmask pL1561) (cmask pL1561) (hmask pL1561) 1104 457 (true, L1561_cp1.1, L1561_cp1.2)) 1561 781 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1561_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1561_fin) true) L1561_seg1) (by decide) rfl L1561_fin ptTest_fst
noncomputable def H1561_cp1 : Nat × Nat := t7val% (fastRun pH1561 1 1103 (init pH1561) (init pH1561))
theorem H1561_seg1 : segOK pH1561 1 1103 (init pH1561) (init pH1561) H1561_cp1.1 H1561_cp1.2 = true := by
  decide +kernel
theorem H1561_fin : (prmOK pH1561 1561 && ptTest pH1561 (runFrom pH1561 (fmask pH1561) (cmask pH1561) (hmask pH1561) 1104 457 (true, H1561_cp1.1, H1561_cp1.2)) 1561 781 true) = true := by
  decide +kernel
theorem H1561_ok : RunOK pH1561 1561 (runFrom pH1561 (fmask pH1561) (cmask pH1561) (hmask pH1561) 1104 457 (true, H1561_cp1.1, H1561_cp1.2)) ∧ ptTest pH1561 (runFrom pH1561 (fmask pH1561) (cmask pH1561) (hmask pH1561) 1104 457 (true, H1561_cp1.1, H1561_cp1.2)) 1561 781 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1561_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1561_fin) true) H1561_seg1) (by decide) rfl H1561_fin ptTest_fst
noncomputable def I1561_cp1 : Nat × Nat := t7val% (fastRun pI1561 1 1103 (init pI1561) (init pI1561))
theorem I1561_seg1 : segOK pI1561 1 1103 (init pI1561) (init pI1561) I1561_cp1.1 I1561_cp1.2 = true := by
  decide +kernel
theorem I1561_fin : (prmOK pI1561 1561 && intTest pI1561 (runFrom pI1561 (fmask pI1561) (cmask pI1561) (hmask pI1561) 1104 457 (true, I1561_cp1.1, I1561_cp1.2)) 1561 20 false) = true := by
  decide +kernel
theorem I1561_ok : RunOK pI1561 1561 (runFrom pI1561 (fmask pI1561) (cmask pI1561) (hmask pI1561) 1104 457 (true, I1561_cp1.1, I1561_cp1.2)) ∧ intTest pI1561 (runFrom pI1561 (fmask pI1561) (cmask pI1561) (hmask pI1561) 1104 457 (true, I1561_cp1.1, I1561_cp1.2)) 1561 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1561_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1561_fin) true) I1561_seg1) (by decide) rfl I1561_fin intTest_fst
theorem link1561 : linkOK pL1561 pH1561 pI1561 = true := by decide +kernel
theorem cvx1561 : ConvexBetweenHumps 1561 :=
  cvx_of L1561_ok H1561_ok I1561_ok link1561 (by decide)

/-! ### `N = 1562` -/

def pL1562 : Prm := ⟨81, 39, 39, 1564, 11, 18446744073709551616, 120402200292194622, 120402200292194622⟩
def pH1562 : Prm := ⟨81, 39, 39, 1564, 11, 18446744073709551616, 120403299803822398, 120403299803822398⟩
def pI1562 : Prm := ⟨67, 33, 31, 1564, 11, 18446744073709551616, 120402200292194622, 120403299803822398⟩
noncomputable def L1562_cp1 : Nat × Nat := t7val% (fastRun pL1562 1 1104 (init pL1562) (init pL1562))
theorem L1562_seg1 : segOK pL1562 1 1104 (init pL1562) (init pL1562) L1562_cp1.1 L1562_cp1.2 = true := by
  decide +kernel
theorem L1562_fin : (prmOK pL1562 1562 && ptTest pL1562 (runFrom pL1562 (fmask pL1562) (cmask pL1562) (hmask pL1562) 1105 457 (true, L1562_cp1.1, L1562_cp1.2)) 1562 781 false) = true := by
  decide +kernel
theorem L1562_ok : RunOK pL1562 1562 (runFrom pL1562 (fmask pL1562) (cmask pL1562) (hmask pL1562) 1105 457 (true, L1562_cp1.1, L1562_cp1.2)) ∧ ptTest pL1562 (runFrom pL1562 (fmask pL1562) (cmask pL1562) (hmask pL1562) 1105 457 (true, L1562_cp1.1, L1562_cp1.2)) 1562 781 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1562_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1562_fin) true) L1562_seg1) (by decide) rfl L1562_fin ptTest_fst
noncomputable def H1562_cp1 : Nat × Nat := t7val% (fastRun pH1562 1 1104 (init pH1562) (init pH1562))
theorem H1562_seg1 : segOK pH1562 1 1104 (init pH1562) (init pH1562) H1562_cp1.1 H1562_cp1.2 = true := by
  decide +kernel
theorem H1562_fin : (prmOK pH1562 1562 && ptTest pH1562 (runFrom pH1562 (fmask pH1562) (cmask pH1562) (hmask pH1562) 1105 457 (true, H1562_cp1.1, H1562_cp1.2)) 1562 781 true) = true := by
  decide +kernel
theorem H1562_ok : RunOK pH1562 1562 (runFrom pH1562 (fmask pH1562) (cmask pH1562) (hmask pH1562) 1105 457 (true, H1562_cp1.1, H1562_cp1.2)) ∧ ptTest pH1562 (runFrom pH1562 (fmask pH1562) (cmask pH1562) (hmask pH1562) 1105 457 (true, H1562_cp1.1, H1562_cp1.2)) 1562 781 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1562_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1562_fin) true) H1562_seg1) (by decide) rfl H1562_fin ptTest_fst
noncomputable def I1562_cp1 : Nat × Nat := t7val% (fastRun pI1562 1 1104 (init pI1562) (init pI1562))
theorem I1562_seg1 : segOK pI1562 1 1104 (init pI1562) (init pI1562) I1562_cp1.1 I1562_cp1.2 = true := by
  decide +kernel
theorem I1562_fin : (prmOK pI1562 1562 && intTest pI1562 (runFrom pI1562 (fmask pI1562) (cmask pI1562) (hmask pI1562) 1105 457 (true, I1562_cp1.1, I1562_cp1.2)) 1562 20 true) = true := by
  decide +kernel
theorem I1562_ok : RunOK pI1562 1562 (runFrom pI1562 (fmask pI1562) (cmask pI1562) (hmask pI1562) 1105 457 (true, I1562_cp1.1, I1562_cp1.2)) ∧ intTest pI1562 (runFrom pI1562 (fmask pI1562) (cmask pI1562) (hmask pI1562) 1105 457 (true, I1562_cp1.1, I1562_cp1.2)) 1562 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1562_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1562_fin) true) I1562_seg1) (by decide) rfl I1562_fin intTest_fst
theorem link1562 : linkOK pL1562 pH1562 pI1562 = true := by decide +kernel
theorem cvx1562 : ConvexBetweenHumps 1562 :=
  cvx_of L1562_ok H1562_ok I1562_ok link1562 (by decide)
theorem cenlink1562 : cenLinkOK pI1562 1562 = true := by decide +kernel
theorem cen1562 : CenterUniqueMin 1562 ∧ DipHyp 1562 ∧ OnePointHyps 1562 :=
  cen_of L1562_ok H1562_ok I1562_ok link1562 cenlink1562

/-! ### The range -/

theorem cvx_1547_1562 {N : ℕ} (h1 : 1547 ≤ N) (h2 : N ≤ 1562) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1554
  · by_cases h4 : N ≤ 1550
    · by_cases h6 : N ≤ 1548
      · by_cases h8 : N ≤ 1547
        · obtain rfl : N = 1547 := by omega
          exact cvx1547
        · obtain rfl : N = 1548 := by omega
          exact cvx1548
      · by_cases h8 : N ≤ 1549
        · obtain rfl : N = 1549 := by omega
          exact cvx1549
        · obtain rfl : N = 1550 := by omega
          exact cvx1550
    · by_cases h6 : N ≤ 1552
      · by_cases h8 : N ≤ 1551
        · obtain rfl : N = 1551 := by omega
          exact cvx1551
        · obtain rfl : N = 1552 := by omega
          exact cvx1552
      · by_cases h8 : N ≤ 1553
        · obtain rfl : N = 1553 := by omega
          exact cvx1553
        · obtain rfl : N = 1554 := by omega
          exact cvx1554
  · by_cases h4 : N ≤ 1558
    · by_cases h6 : N ≤ 1556
      · by_cases h8 : N ≤ 1555
        · obtain rfl : N = 1555 := by omega
          exact cvx1555
        · obtain rfl : N = 1556 := by omega
          exact cvx1556
      · by_cases h8 : N ≤ 1557
        · obtain rfl : N = 1557 := by omega
          exact cvx1557
        · obtain rfl : N = 1558 := by omega
          exact cvx1558
    · by_cases h6 : N ≤ 1560
      · by_cases h8 : N ≤ 1559
        · obtain rfl : N = 1559 := by omega
          exact cvx1559
        · obtain rfl : N = 1560 := by omega
          exact cvx1560
      · by_cases h8 : N ≤ 1561
        · obtain rfl : N = 1561 := by omega
          exact cvx1561
        · obtain rfl : N = 1562 := by omega
          exact cvx1562

theorem cen_1547_1562 {N : ℕ} (h1 : 1547 ≤ N) (h2 : N ≤ 1562) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1554
  · by_cases h4 : N ≤ 1550
    · by_cases h6 : N ≤ 1548
      · obtain rfl : N = 1548 := by omega
        exact cen1548
      · obtain rfl : N = 1550 := by omega
        exact cen1550
    · by_cases h6 : N ≤ 1552
      · obtain rfl : N = 1552 := by omega
        exact cen1552
      · obtain rfl : N = 1554 := by omega
        exact cen1554
  · by_cases h4 : N ≤ 1558
    · by_cases h6 : N ≤ 1556
      · obtain rfl : N = 1556 := by omega
        exact cen1556
      · obtain rfl : N = 1558 := by omega
        exact cen1558
    · by_cases h6 : N ≤ 1560
      · obtain rfl : N = 1560 := by omega
        exact cen1560
      · obtain rfl : N = 1562 := by omega
        exact cen1562

end Kagey131.PaperD.T7
