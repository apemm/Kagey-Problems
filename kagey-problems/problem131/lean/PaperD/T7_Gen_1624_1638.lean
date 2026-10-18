import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1624, …, 1638` (generated)

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

/-! ### `N = 1624` -/

def pL1624 : Prm := ⟨80, 37, 40, 1626, 11, 18446744073709551616, 116639160128267495, 116639160128267495⟩
def pH1624 : Prm := ⟨80, 37, 40, 1626, 11, 18446744073709551616, 116640259639895271, 116640259639895271⟩
def pI1624 : Prm := ⟨68, 33, 32, 1626, 11, 18446744073709551616, 116639160128267495, 116640259639895271⟩
noncomputable def L1624_cp1 : Nat × Nat := t7val% (fastRun pL1624 1 1147 (init pL1624) (init pL1624))
theorem L1624_seg1 : segOK pL1624 1 1147 (init pL1624) (init pL1624) L1624_cp1.1 L1624_cp1.2 = true := by
  decide +kernel
theorem L1624_fin : (prmOK pL1624 1624 && ptTest pL1624 (runFrom pL1624 (fmask pL1624) (cmask pL1624) (hmask pL1624) 1148 476 (true, L1624_cp1.1, L1624_cp1.2)) 1624 812 false) = true := by
  decide +kernel
theorem L1624_ok : RunOK pL1624 1624 (runFrom pL1624 (fmask pL1624) (cmask pL1624) (hmask pL1624) 1148 476 (true, L1624_cp1.1, L1624_cp1.2)) ∧ ptTest pL1624 (runFrom pL1624 (fmask pL1624) (cmask pL1624) (hmask pL1624) 1148 476 (true, L1624_cp1.1, L1624_cp1.2)) 1624 812 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1624_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1624_fin) true) L1624_seg1) (by decide) rfl L1624_fin ptTest_fst
noncomputable def H1624_cp1 : Nat × Nat := t7val% (fastRun pH1624 1 1147 (init pH1624) (init pH1624))
theorem H1624_seg1 : segOK pH1624 1 1147 (init pH1624) (init pH1624) H1624_cp1.1 H1624_cp1.2 = true := by
  decide +kernel
theorem H1624_fin : (prmOK pH1624 1624 && ptTest pH1624 (runFrom pH1624 (fmask pH1624) (cmask pH1624) (hmask pH1624) 1148 476 (true, H1624_cp1.1, H1624_cp1.2)) 1624 812 true) = true := by
  decide +kernel
theorem H1624_ok : RunOK pH1624 1624 (runFrom pH1624 (fmask pH1624) (cmask pH1624) (hmask pH1624) 1148 476 (true, H1624_cp1.1, H1624_cp1.2)) ∧ ptTest pH1624 (runFrom pH1624 (fmask pH1624) (cmask pH1624) (hmask pH1624) 1148 476 (true, H1624_cp1.1, H1624_cp1.2)) 1624 812 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1624_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1624_fin) true) H1624_seg1) (by decide) rfl H1624_fin ptTest_fst
noncomputable def I1624_cp1 : Nat × Nat := t7val% (fastRun pI1624 1 1147 (init pI1624) (init pI1624))
theorem I1624_seg1 : segOK pI1624 1 1147 (init pI1624) (init pI1624) I1624_cp1.1 I1624_cp1.2 = true := by
  decide +kernel
theorem I1624_fin : (prmOK pI1624 1624 && intTest pI1624 (runFrom pI1624 (fmask pI1624) (cmask pI1624) (hmask pI1624) 1148 476 (true, I1624_cp1.1, I1624_cp1.2)) 1624 21 true) = true := by
  decide +kernel
theorem I1624_ok : RunOK pI1624 1624 (runFrom pI1624 (fmask pI1624) (cmask pI1624) (hmask pI1624) 1148 476 (true, I1624_cp1.1, I1624_cp1.2)) ∧ intTest pI1624 (runFrom pI1624 (fmask pI1624) (cmask pI1624) (hmask pI1624) 1148 476 (true, I1624_cp1.1, I1624_cp1.2)) 1624 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1624_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1624_fin) true) I1624_seg1) (by decide) rfl I1624_fin intTest_fst
theorem link1624 : linkOK pL1624 pH1624 pI1624 = true := by decide +kernel
theorem cvx1624 : ConvexBetweenHumps 1624 :=
  cvx_of L1624_ok H1624_ok I1624_ok link1624 (by decide)
theorem cenlink1624 : cenLinkOK pI1624 1624 = true := by decide +kernel
theorem cen1624 : CenterUniqueMin 1624 ∧ DipHyp 1624 ∧ OnePointHyps 1624 :=
  cen_of L1624_ok H1624_ok I1624_ok link1624 cenlink1624

/-! ### `N = 1625` -/

def pL1625 : Prm := ⟨80, 37, 40, 1627, 11, 18446744073709551616, 116580543316723659, 116580543316723659⟩
def pH1625 : Prm := ⟨80, 37, 40, 1627, 11, 18446744073709551616, 116581642828351435, 116581642828351435⟩
def pI1625 : Prm := ⟨68, 33, 32, 1627, 11, 18446744073709551616, 116580543316723659, 116581642828351435⟩
noncomputable def L1625_cp1 : Nat × Nat := t7val% (fastRun pL1625 1 1148 (init pL1625) (init pL1625))
theorem L1625_seg1 : segOK pL1625 1 1148 (init pL1625) (init pL1625) L1625_cp1.1 L1625_cp1.2 = true := by
  decide +kernel
theorem L1625_fin : (prmOK pL1625 1625 && ptTest pL1625 (runFrom pL1625 (fmask pL1625) (cmask pL1625) (hmask pL1625) 1149 476 (true, L1625_cp1.1, L1625_cp1.2)) 1625 813 false) = true := by
  decide +kernel
theorem L1625_ok : RunOK pL1625 1625 (runFrom pL1625 (fmask pL1625) (cmask pL1625) (hmask pL1625) 1149 476 (true, L1625_cp1.1, L1625_cp1.2)) ∧ ptTest pL1625 (runFrom pL1625 (fmask pL1625) (cmask pL1625) (hmask pL1625) 1149 476 (true, L1625_cp1.1, L1625_cp1.2)) 1625 813 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1625_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1625_fin) true) L1625_seg1) (by decide) rfl L1625_fin ptTest_fst
noncomputable def H1625_cp1 : Nat × Nat := t7val% (fastRun pH1625 1 1148 (init pH1625) (init pH1625))
theorem H1625_seg1 : segOK pH1625 1 1148 (init pH1625) (init pH1625) H1625_cp1.1 H1625_cp1.2 = true := by
  decide +kernel
theorem H1625_fin : (prmOK pH1625 1625 && ptTest pH1625 (runFrom pH1625 (fmask pH1625) (cmask pH1625) (hmask pH1625) 1149 476 (true, H1625_cp1.1, H1625_cp1.2)) 1625 813 true) = true := by
  decide +kernel
theorem H1625_ok : RunOK pH1625 1625 (runFrom pH1625 (fmask pH1625) (cmask pH1625) (hmask pH1625) 1149 476 (true, H1625_cp1.1, H1625_cp1.2)) ∧ ptTest pH1625 (runFrom pH1625 (fmask pH1625) (cmask pH1625) (hmask pH1625) 1149 476 (true, H1625_cp1.1, H1625_cp1.2)) 1625 813 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1625_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1625_fin) true) H1625_seg1) (by decide) rfl H1625_fin ptTest_fst
noncomputable def I1625_cp1 : Nat × Nat := t7val% (fastRun pI1625 1 1148 (init pI1625) (init pI1625))
theorem I1625_seg1 : segOK pI1625 1 1148 (init pI1625) (init pI1625) I1625_cp1.1 I1625_cp1.2 = true := by
  decide +kernel
theorem I1625_fin : (prmOK pI1625 1625 && intTest pI1625 (runFrom pI1625 (fmask pI1625) (cmask pI1625) (hmask pI1625) 1149 476 (true, I1625_cp1.1, I1625_cp1.2)) 1625 21 false) = true := by
  decide +kernel
theorem I1625_ok : RunOK pI1625 1625 (runFrom pI1625 (fmask pI1625) (cmask pI1625) (hmask pI1625) 1149 476 (true, I1625_cp1.1, I1625_cp1.2)) ∧ intTest pI1625 (runFrom pI1625 (fmask pI1625) (cmask pI1625) (hmask pI1625) 1149 476 (true, I1625_cp1.1, I1625_cp1.2)) 1625 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1625_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1625_fin) true) I1625_seg1) (by decide) rfl I1625_fin intTest_fst
theorem link1625 : linkOK pL1625 pH1625 pI1625 = true := by decide +kernel
theorem cvx1625 : ConvexBetweenHumps 1625 :=
  cvx_of L1625_ok H1625_ok I1625_ok link1625 (by decide)

/-! ### `N = 1626` -/

def pL1626 : Prm := ⟨80, 37, 40, 1628, 11, 18446744073709551616, 116522016757701432, 116522016757701432⟩
def pH1626 : Prm := ⟨80, 37, 40, 1628, 11, 18446744073709551616, 116523116269329208, 116523116269329208⟩
def pI1626 : Prm := ⟨67, 33, 31, 1628, 11, 18446744073709551616, 116522016757701432, 116523116269329208⟩
noncomputable def L1626_cp1 : Nat × Nat := t7val% (fastRun pL1626 1 1149 (init pL1626) (init pL1626))
theorem L1626_seg1 : segOK pL1626 1 1149 (init pL1626) (init pL1626) L1626_cp1.1 L1626_cp1.2 = true := by
  decide +kernel
theorem L1626_fin : (prmOK pL1626 1626 && ptTest pL1626 (runFrom pL1626 (fmask pL1626) (cmask pL1626) (hmask pL1626) 1150 476 (true, L1626_cp1.1, L1626_cp1.2)) 1626 813 false) = true := by
  decide +kernel
theorem L1626_ok : RunOK pL1626 1626 (runFrom pL1626 (fmask pL1626) (cmask pL1626) (hmask pL1626) 1150 476 (true, L1626_cp1.1, L1626_cp1.2)) ∧ ptTest pL1626 (runFrom pL1626 (fmask pL1626) (cmask pL1626) (hmask pL1626) 1150 476 (true, L1626_cp1.1, L1626_cp1.2)) 1626 813 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1626_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1626_fin) true) L1626_seg1) (by decide) rfl L1626_fin ptTest_fst
noncomputable def H1626_cp1 : Nat × Nat := t7val% (fastRun pH1626 1 1149 (init pH1626) (init pH1626))
theorem H1626_seg1 : segOK pH1626 1 1149 (init pH1626) (init pH1626) H1626_cp1.1 H1626_cp1.2 = true := by
  decide +kernel
theorem H1626_fin : (prmOK pH1626 1626 && ptTest pH1626 (runFrom pH1626 (fmask pH1626) (cmask pH1626) (hmask pH1626) 1150 476 (true, H1626_cp1.1, H1626_cp1.2)) 1626 813 true) = true := by
  decide +kernel
theorem H1626_ok : RunOK pH1626 1626 (runFrom pH1626 (fmask pH1626) (cmask pH1626) (hmask pH1626) 1150 476 (true, H1626_cp1.1, H1626_cp1.2)) ∧ ptTest pH1626 (runFrom pH1626 (fmask pH1626) (cmask pH1626) (hmask pH1626) 1150 476 (true, H1626_cp1.1, H1626_cp1.2)) 1626 813 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1626_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1626_fin) true) H1626_seg1) (by decide) rfl H1626_fin ptTest_fst
noncomputable def I1626_cp1 : Nat × Nat := t7val% (fastRun pI1626 1 1149 (init pI1626) (init pI1626))
theorem I1626_seg1 : segOK pI1626 1 1149 (init pI1626) (init pI1626) I1626_cp1.1 I1626_cp1.2 = true := by
  decide +kernel
theorem I1626_fin : (prmOK pI1626 1626 && intTest pI1626 (runFrom pI1626 (fmask pI1626) (cmask pI1626) (hmask pI1626) 1150 476 (true, I1626_cp1.1, I1626_cp1.2)) 1626 21 true) = true := by
  decide +kernel
theorem I1626_ok : RunOK pI1626 1626 (runFrom pI1626 (fmask pI1626) (cmask pI1626) (hmask pI1626) 1150 476 (true, I1626_cp1.1, I1626_cp1.2)) ∧ intTest pI1626 (runFrom pI1626 (fmask pI1626) (cmask pI1626) (hmask pI1626) 1150 476 (true, I1626_cp1.1, I1626_cp1.2)) 1626 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1626_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1626_fin) true) I1626_seg1) (by decide) rfl I1626_fin intTest_fst
theorem link1626 : linkOK pL1626 pH1626 pI1626 = true := by decide +kernel
theorem cvx1626 : ConvexBetweenHumps 1626 :=
  cvx_of L1626_ok H1626_ok I1626_ok link1626 (by decide)
theorem cenlink1626 : cenLinkOK pI1626 1626 = true := by decide +kernel
theorem cen1626 : CenterUniqueMin 1626 ∧ DipHyp 1626 ∧ OnePointHyps 1626 :=
  cen_of L1626_ok H1626_ok I1626_ok link1626 cenlink1626

/-! ### `N = 1627` -/

def pL1627 : Prm := ⟨80, 37, 40, 1629, 11, 18446744073709551616, 116463527833339082, 116463527833339082⟩
def pH1627 : Prm := ⟨80, 37, 40, 1629, 11, 18446744073709551616, 116464627344966858, 116464627344966858⟩
def pI1627 : Prm := ⟨67, 33, 31, 1629, 11, 18446744073709551616, 116463527833339082, 116464627344966858⟩
noncomputable def L1627_cp1 : Nat × Nat := t7val% (fastRun pL1627 1 1149 (init pL1627) (init pL1627))
theorem L1627_seg1 : segOK pL1627 1 1149 (init pL1627) (init pL1627) L1627_cp1.1 L1627_cp1.2 = true := by
  decide +kernel
theorem L1627_fin : (prmOK pL1627 1627 && ptTest pL1627 (runFrom pL1627 (fmask pL1627) (cmask pL1627) (hmask pL1627) 1150 477 (true, L1627_cp1.1, L1627_cp1.2)) 1627 814 false) = true := by
  decide +kernel
theorem L1627_ok : RunOK pL1627 1627 (runFrom pL1627 (fmask pL1627) (cmask pL1627) (hmask pL1627) 1150 477 (true, L1627_cp1.1, L1627_cp1.2)) ∧ ptTest pL1627 (runFrom pL1627 (fmask pL1627) (cmask pL1627) (hmask pL1627) 1150 477 (true, L1627_cp1.1, L1627_cp1.2)) 1627 814 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1627_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1627_fin) true) L1627_seg1) (by decide) rfl L1627_fin ptTest_fst
noncomputable def H1627_cp1 : Nat × Nat := t7val% (fastRun pH1627 1 1149 (init pH1627) (init pH1627))
theorem H1627_seg1 : segOK pH1627 1 1149 (init pH1627) (init pH1627) H1627_cp1.1 H1627_cp1.2 = true := by
  decide +kernel
theorem H1627_fin : (prmOK pH1627 1627 && ptTest pH1627 (runFrom pH1627 (fmask pH1627) (cmask pH1627) (hmask pH1627) 1150 477 (true, H1627_cp1.1, H1627_cp1.2)) 1627 814 true) = true := by
  decide +kernel
theorem H1627_ok : RunOK pH1627 1627 (runFrom pH1627 (fmask pH1627) (cmask pH1627) (hmask pH1627) 1150 477 (true, H1627_cp1.1, H1627_cp1.2)) ∧ ptTest pH1627 (runFrom pH1627 (fmask pH1627) (cmask pH1627) (hmask pH1627) 1150 477 (true, H1627_cp1.1, H1627_cp1.2)) 1627 814 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1627_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1627_fin) true) H1627_seg1) (by decide) rfl H1627_fin ptTest_fst
noncomputable def I1627_cp1 : Nat × Nat := t7val% (fastRun pI1627 1 1149 (init pI1627) (init pI1627))
theorem I1627_seg1 : segOK pI1627 1 1149 (init pI1627) (init pI1627) I1627_cp1.1 I1627_cp1.2 = true := by
  decide +kernel
theorem I1627_fin : (prmOK pI1627 1627 && intTest pI1627 (runFrom pI1627 (fmask pI1627) (cmask pI1627) (hmask pI1627) 1150 477 (true, I1627_cp1.1, I1627_cp1.2)) 1627 21 false) = true := by
  decide +kernel
theorem I1627_ok : RunOK pI1627 1627 (runFrom pI1627 (fmask pI1627) (cmask pI1627) (hmask pI1627) 1150 477 (true, I1627_cp1.1, I1627_cp1.2)) ∧ intTest pI1627 (runFrom pI1627 (fmask pI1627) (cmask pI1627) (hmask pI1627) 1150 477 (true, I1627_cp1.1, I1627_cp1.2)) 1627 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1627_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1627_fin) true) I1627_seg1) (by decide) rfl I1627_fin intTest_fst
theorem link1627 : linkOK pL1627 pH1627 pI1627 = true := by decide +kernel
theorem cvx1627 : ConvexBetweenHumps 1627 :=
  cvx_of L1627_ok H1627_ok I1627_ok link1627 (by decide)

/-! ### `N = 1628` -/

def pL1628 : Prm := ⟨80, 37, 40, 1630, 11, 18446744073709551616, 116405128847442523, 116405128847442523⟩
def pH1628 : Prm := ⟨80, 37, 40, 1630, 11, 18446744073709551616, 116406228359070299, 116406228359070299⟩
def pI1628 : Prm := ⟨67, 33, 31, 1630, 11, 18446744073709551616, 116405128847442523, 116406228359070299⟩
noncomputable def L1628_cp1 : Nat × Nat := t7val% (fastRun pL1628 1 1150 (init pL1628) (init pL1628))
theorem L1628_seg1 : segOK pL1628 1 1150 (init pL1628) (init pL1628) L1628_cp1.1 L1628_cp1.2 = true := by
  decide +kernel
theorem L1628_fin : (prmOK pL1628 1628 && ptTest pL1628 (runFrom pL1628 (fmask pL1628) (cmask pL1628) (hmask pL1628) 1151 477 (true, L1628_cp1.1, L1628_cp1.2)) 1628 814 false) = true := by
  decide +kernel
theorem L1628_ok : RunOK pL1628 1628 (runFrom pL1628 (fmask pL1628) (cmask pL1628) (hmask pL1628) 1151 477 (true, L1628_cp1.1, L1628_cp1.2)) ∧ ptTest pL1628 (runFrom pL1628 (fmask pL1628) (cmask pL1628) (hmask pL1628) 1151 477 (true, L1628_cp1.1, L1628_cp1.2)) 1628 814 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1628_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1628_fin) true) L1628_seg1) (by decide) rfl L1628_fin ptTest_fst
noncomputable def H1628_cp1 : Nat × Nat := t7val% (fastRun pH1628 1 1150 (init pH1628) (init pH1628))
theorem H1628_seg1 : segOK pH1628 1 1150 (init pH1628) (init pH1628) H1628_cp1.1 H1628_cp1.2 = true := by
  decide +kernel
theorem H1628_fin : (prmOK pH1628 1628 && ptTest pH1628 (runFrom pH1628 (fmask pH1628) (cmask pH1628) (hmask pH1628) 1151 477 (true, H1628_cp1.1, H1628_cp1.2)) 1628 814 true) = true := by
  decide +kernel
theorem H1628_ok : RunOK pH1628 1628 (runFrom pH1628 (fmask pH1628) (cmask pH1628) (hmask pH1628) 1151 477 (true, H1628_cp1.1, H1628_cp1.2)) ∧ ptTest pH1628 (runFrom pH1628 (fmask pH1628) (cmask pH1628) (hmask pH1628) 1151 477 (true, H1628_cp1.1, H1628_cp1.2)) 1628 814 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1628_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1628_fin) true) H1628_seg1) (by decide) rfl H1628_fin ptTest_fst
noncomputable def I1628_cp1 : Nat × Nat := t7val% (fastRun pI1628 1 1150 (init pI1628) (init pI1628))
theorem I1628_seg1 : segOK pI1628 1 1150 (init pI1628) (init pI1628) I1628_cp1.1 I1628_cp1.2 = true := by
  decide +kernel
theorem I1628_fin : (prmOK pI1628 1628 && intTest pI1628 (runFrom pI1628 (fmask pI1628) (cmask pI1628) (hmask pI1628) 1151 477 (true, I1628_cp1.1, I1628_cp1.2)) 1628 21 true) = true := by
  decide +kernel
theorem I1628_ok : RunOK pI1628 1628 (runFrom pI1628 (fmask pI1628) (cmask pI1628) (hmask pI1628) 1151 477 (true, I1628_cp1.1, I1628_cp1.2)) ∧ intTest pI1628 (runFrom pI1628 (fmask pI1628) (cmask pI1628) (hmask pI1628) 1151 477 (true, I1628_cp1.1, I1628_cp1.2)) 1628 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1628_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1628_fin) true) I1628_seg1) (by decide) rfl I1628_fin intTest_fst
theorem link1628 : linkOK pL1628 pH1628 pI1628 = true := by decide +kernel
theorem cvx1628 : ConvexBetweenHumps 1628 :=
  cvx_of L1628_ok H1628_ok I1628_ok link1628 (by decide)
theorem cenlink1628 : cenLinkOK pI1628 1628 = true := by decide +kernel
theorem cen1628 : CenterUniqueMin 1628 ∧ DipHyp 1628 ∧ OnePointHyps 1628 :=
  cen_of L1628_ok H1628_ok I1628_ok link1628 cenlink1628

/-! ### `N = 1629` -/

def pL1629 : Prm := ⟨80, 37, 40, 1631, 11, 18446744073709551616, 116346767379050569, 116346767379050569⟩
def pH1629 : Prm := ⟨80, 37, 40, 1631, 11, 18446744073709551616, 116347866890678345, 116347866890678345⟩
def pI1629 : Prm := ⟨67, 33, 31, 1631, 11, 18446744073709551616, 116346767379050569, 116347866890678345⟩
noncomputable def L1629_cp1 : Nat × Nat := t7val% (fastRun pL1629 1 1151 (init pL1629) (init pL1629))
theorem L1629_seg1 : segOK pL1629 1 1151 (init pL1629) (init pL1629) L1629_cp1.1 L1629_cp1.2 = true := by
  decide +kernel
theorem L1629_fin : (prmOK pL1629 1629 && ptTest pL1629 (runFrom pL1629 (fmask pL1629) (cmask pL1629) (hmask pL1629) 1152 477 (true, L1629_cp1.1, L1629_cp1.2)) 1629 815 false) = true := by
  decide +kernel
theorem L1629_ok : RunOK pL1629 1629 (runFrom pL1629 (fmask pL1629) (cmask pL1629) (hmask pL1629) 1152 477 (true, L1629_cp1.1, L1629_cp1.2)) ∧ ptTest pL1629 (runFrom pL1629 (fmask pL1629) (cmask pL1629) (hmask pL1629) 1152 477 (true, L1629_cp1.1, L1629_cp1.2)) 1629 815 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1629_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1629_fin) true) L1629_seg1) (by decide) rfl L1629_fin ptTest_fst
noncomputable def H1629_cp1 : Nat × Nat := t7val% (fastRun pH1629 1 1151 (init pH1629) (init pH1629))
theorem H1629_seg1 : segOK pH1629 1 1151 (init pH1629) (init pH1629) H1629_cp1.1 H1629_cp1.2 = true := by
  decide +kernel
theorem H1629_fin : (prmOK pH1629 1629 && ptTest pH1629 (runFrom pH1629 (fmask pH1629) (cmask pH1629) (hmask pH1629) 1152 477 (true, H1629_cp1.1, H1629_cp1.2)) 1629 815 true) = true := by
  decide +kernel
theorem H1629_ok : RunOK pH1629 1629 (runFrom pH1629 (fmask pH1629) (cmask pH1629) (hmask pH1629) 1152 477 (true, H1629_cp1.1, H1629_cp1.2)) ∧ ptTest pH1629 (runFrom pH1629 (fmask pH1629) (cmask pH1629) (hmask pH1629) 1152 477 (true, H1629_cp1.1, H1629_cp1.2)) 1629 815 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1629_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1629_fin) true) H1629_seg1) (by decide) rfl H1629_fin ptTest_fst
noncomputable def I1629_cp1 : Nat × Nat := t7val% (fastRun pI1629 1 1151 (init pI1629) (init pI1629))
theorem I1629_seg1 : segOK pI1629 1 1151 (init pI1629) (init pI1629) I1629_cp1.1 I1629_cp1.2 = true := by
  decide +kernel
theorem I1629_fin : (prmOK pI1629 1629 && intTest pI1629 (runFrom pI1629 (fmask pI1629) (cmask pI1629) (hmask pI1629) 1152 477 (true, I1629_cp1.1, I1629_cp1.2)) 1629 21 false) = true := by
  decide +kernel
theorem I1629_ok : RunOK pI1629 1629 (runFrom pI1629 (fmask pI1629) (cmask pI1629) (hmask pI1629) 1152 477 (true, I1629_cp1.1, I1629_cp1.2)) ∧ intTest pI1629 (runFrom pI1629 (fmask pI1629) (cmask pI1629) (hmask pI1629) 1152 477 (true, I1629_cp1.1, I1629_cp1.2)) 1629 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1629_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1629_fin) true) I1629_seg1) (by decide) rfl I1629_fin intTest_fst
theorem link1629 : linkOK pL1629 pH1629 pI1629 = true := by decide +kernel
theorem cvx1629 : ConvexBetweenHumps 1629 :=
  cvx_of L1629_ok H1629_ok I1629_ok link1629 (by decide)

/-! ### `N = 1630` -/

def pL1630 : Prm := ⟨80, 37, 40, 1632, 11, 18446744073709551616, 116288495536544328, 116288495536544328⟩
def pH1630 : Prm := ⟨80, 37, 40, 1632, 11, 18446744073709551616, 116289595048172104, 116289595048172104⟩
def pI1630 : Prm := ⟨67, 33, 31, 1632, 11, 18446744073709551616, 116288495536544328, 116289595048172104⟩
noncomputable def L1630_cp1 : Nat × Nat := t7val% (fastRun pL1630 1 1152 (init pL1630) (init pL1630))
theorem L1630_seg1 : segOK pL1630 1 1152 (init pL1630) (init pL1630) L1630_cp1.1 L1630_cp1.2 = true := by
  decide +kernel
theorem L1630_fin : (prmOK pL1630 1630 && ptTest pL1630 (runFrom pL1630 (fmask pL1630) (cmask pL1630) (hmask pL1630) 1153 477 (true, L1630_cp1.1, L1630_cp1.2)) 1630 815 false) = true := by
  decide +kernel
theorem L1630_ok : RunOK pL1630 1630 (runFrom pL1630 (fmask pL1630) (cmask pL1630) (hmask pL1630) 1153 477 (true, L1630_cp1.1, L1630_cp1.2)) ∧ ptTest pL1630 (runFrom pL1630 (fmask pL1630) (cmask pL1630) (hmask pL1630) 1153 477 (true, L1630_cp1.1, L1630_cp1.2)) 1630 815 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1630_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1630_fin) true) L1630_seg1) (by decide) rfl L1630_fin ptTest_fst
noncomputable def H1630_cp1 : Nat × Nat := t7val% (fastRun pH1630 1 1152 (init pH1630) (init pH1630))
theorem H1630_seg1 : segOK pH1630 1 1152 (init pH1630) (init pH1630) H1630_cp1.1 H1630_cp1.2 = true := by
  decide +kernel
theorem H1630_fin : (prmOK pH1630 1630 && ptTest pH1630 (runFrom pH1630 (fmask pH1630) (cmask pH1630) (hmask pH1630) 1153 477 (true, H1630_cp1.1, H1630_cp1.2)) 1630 815 true) = true := by
  decide +kernel
theorem H1630_ok : RunOK pH1630 1630 (runFrom pH1630 (fmask pH1630) (cmask pH1630) (hmask pH1630) 1153 477 (true, H1630_cp1.1, H1630_cp1.2)) ∧ ptTest pH1630 (runFrom pH1630 (fmask pH1630) (cmask pH1630) (hmask pH1630) 1153 477 (true, H1630_cp1.1, H1630_cp1.2)) 1630 815 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1630_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1630_fin) true) H1630_seg1) (by decide) rfl H1630_fin ptTest_fst
noncomputable def I1630_cp1 : Nat × Nat := t7val% (fastRun pI1630 1 1152 (init pI1630) (init pI1630))
theorem I1630_seg1 : segOK pI1630 1 1152 (init pI1630) (init pI1630) I1630_cp1.1 I1630_cp1.2 = true := by
  decide +kernel
theorem I1630_fin : (prmOK pI1630 1630 && intTest pI1630 (runFrom pI1630 (fmask pI1630) (cmask pI1630) (hmask pI1630) 1153 477 (true, I1630_cp1.1, I1630_cp1.2)) 1630 21 true) = true := by
  decide +kernel
theorem I1630_ok : RunOK pI1630 1630 (runFrom pI1630 (fmask pI1630) (cmask pI1630) (hmask pI1630) 1153 477 (true, I1630_cp1.1, I1630_cp1.2)) ∧ intTest pI1630 (runFrom pI1630 (fmask pI1630) (cmask pI1630) (hmask pI1630) 1153 477 (true, I1630_cp1.1, I1630_cp1.2)) 1630 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1630_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1630_fin) true) I1630_seg1) (by decide) rfl I1630_fin intTest_fst
theorem link1630 : linkOK pL1630 pH1630 pI1630 = true := by decide +kernel
theorem cvx1630 : ConvexBetweenHumps 1630 :=
  cvx_of L1630_ok H1630_ok I1630_ok link1630 (by decide)
theorem cenlink1630 : cenLinkOK pI1630 1630 = true := by decide +kernel
theorem cen1630 : CenterUniqueMin 1630 ∧ DipHyp 1630 ∧ OnePointHyps 1630 :=
  cen_of L1630_ok H1630_ok I1630_ok link1630 cenlink1630

/-! ### `N = 1631` -/

def pL1631 : Prm := ⟨80, 37, 40, 1633, 11, 18446744073709551616, 116230261094848589, 116230261094848589⟩
def pH1631 : Prm := ⟨80, 37, 40, 1633, 11, 18446744073709551616, 116231360606476365, 116231360606476365⟩
def pI1631 : Prm := ⟨67, 33, 31, 1633, 11, 18446744073709551616, 116230261094848589, 116231360606476365⟩
noncomputable def L1631_cp1 : Nat × Nat := t7val% (fastRun pL1631 1 1152 (init pL1631) (init pL1631))
theorem L1631_seg1 : segOK pL1631 1 1152 (init pL1631) (init pL1631) L1631_cp1.1 L1631_cp1.2 = true := by
  decide +kernel
theorem L1631_fin : (prmOK pL1631 1631 && ptTest pL1631 (runFrom pL1631 (fmask pL1631) (cmask pL1631) (hmask pL1631) 1153 478 (true, L1631_cp1.1, L1631_cp1.2)) 1631 816 false) = true := by
  decide +kernel
theorem L1631_ok : RunOK pL1631 1631 (runFrom pL1631 (fmask pL1631) (cmask pL1631) (hmask pL1631) 1153 478 (true, L1631_cp1.1, L1631_cp1.2)) ∧ ptTest pL1631 (runFrom pL1631 (fmask pL1631) (cmask pL1631) (hmask pL1631) 1153 478 (true, L1631_cp1.1, L1631_cp1.2)) 1631 816 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1631_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1631_fin) true) L1631_seg1) (by decide) rfl L1631_fin ptTest_fst
noncomputable def H1631_cp1 : Nat × Nat := t7val% (fastRun pH1631 1 1152 (init pH1631) (init pH1631))
theorem H1631_seg1 : segOK pH1631 1 1152 (init pH1631) (init pH1631) H1631_cp1.1 H1631_cp1.2 = true := by
  decide +kernel
theorem H1631_fin : (prmOK pH1631 1631 && ptTest pH1631 (runFrom pH1631 (fmask pH1631) (cmask pH1631) (hmask pH1631) 1153 478 (true, H1631_cp1.1, H1631_cp1.2)) 1631 816 true) = true := by
  decide +kernel
theorem H1631_ok : RunOK pH1631 1631 (runFrom pH1631 (fmask pH1631) (cmask pH1631) (hmask pH1631) 1153 478 (true, H1631_cp1.1, H1631_cp1.2)) ∧ ptTest pH1631 (runFrom pH1631 (fmask pH1631) (cmask pH1631) (hmask pH1631) 1153 478 (true, H1631_cp1.1, H1631_cp1.2)) 1631 816 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1631_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1631_fin) true) H1631_seg1) (by decide) rfl H1631_fin ptTest_fst
noncomputable def I1631_cp1 : Nat × Nat := t7val% (fastRun pI1631 1 1152 (init pI1631) (init pI1631))
theorem I1631_seg1 : segOK pI1631 1 1152 (init pI1631) (init pI1631) I1631_cp1.1 I1631_cp1.2 = true := by
  decide +kernel
theorem I1631_fin : (prmOK pI1631 1631 && intTest pI1631 (runFrom pI1631 (fmask pI1631) (cmask pI1631) (hmask pI1631) 1153 478 (true, I1631_cp1.1, I1631_cp1.2)) 1631 21 false) = true := by
  decide +kernel
theorem I1631_ok : RunOK pI1631 1631 (runFrom pI1631 (fmask pI1631) (cmask pI1631) (hmask pI1631) 1153 478 (true, I1631_cp1.1, I1631_cp1.2)) ∧ intTest pI1631 (runFrom pI1631 (fmask pI1631) (cmask pI1631) (hmask pI1631) 1153 478 (true, I1631_cp1.1, I1631_cp1.2)) 1631 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1631_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1631_fin) true) I1631_seg1) (by decide) rfl I1631_fin intTest_fst
theorem link1631 : linkOK pL1631 pH1631 pI1631 = true := by decide +kernel
theorem cvx1631 : ConvexBetweenHumps 1631 :=
  cvx_of L1631_ok H1631_ok I1631_ok link1631 (by decide)

/-! ### `N = 1632` -/

def pL1632 : Prm := ⟨80, 37, 40, 1634, 11, 18446744073709551616, 116172115967952671, 116172115967952671⟩
def pH1632 : Prm := ⟨80, 37, 40, 1634, 11, 18446744073709551616, 116173215479580447, 116173215479580447⟩
def pI1632 : Prm := ⟨67, 33, 31, 1634, 11, 18446744073709551616, 116172115967952671, 116173215479580447⟩
noncomputable def L1632_cp1 : Nat × Nat := t7val% (fastRun pL1632 1 1153 (init pL1632) (init pL1632))
theorem L1632_seg1 : segOK pL1632 1 1153 (init pL1632) (init pL1632) L1632_cp1.1 L1632_cp1.2 = true := by
  decide +kernel
theorem L1632_fin : (prmOK pL1632 1632 && ptTest pL1632 (runFrom pL1632 (fmask pL1632) (cmask pL1632) (hmask pL1632) 1154 478 (true, L1632_cp1.1, L1632_cp1.2)) 1632 816 false) = true := by
  decide +kernel
theorem L1632_ok : RunOK pL1632 1632 (runFrom pL1632 (fmask pL1632) (cmask pL1632) (hmask pL1632) 1154 478 (true, L1632_cp1.1, L1632_cp1.2)) ∧ ptTest pL1632 (runFrom pL1632 (fmask pL1632) (cmask pL1632) (hmask pL1632) 1154 478 (true, L1632_cp1.1, L1632_cp1.2)) 1632 816 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1632_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1632_fin) true) L1632_seg1) (by decide) rfl L1632_fin ptTest_fst
noncomputable def H1632_cp1 : Nat × Nat := t7val% (fastRun pH1632 1 1153 (init pH1632) (init pH1632))
theorem H1632_seg1 : segOK pH1632 1 1153 (init pH1632) (init pH1632) H1632_cp1.1 H1632_cp1.2 = true := by
  decide +kernel
theorem H1632_fin : (prmOK pH1632 1632 && ptTest pH1632 (runFrom pH1632 (fmask pH1632) (cmask pH1632) (hmask pH1632) 1154 478 (true, H1632_cp1.1, H1632_cp1.2)) 1632 816 true) = true := by
  decide +kernel
theorem H1632_ok : RunOK pH1632 1632 (runFrom pH1632 (fmask pH1632) (cmask pH1632) (hmask pH1632) 1154 478 (true, H1632_cp1.1, H1632_cp1.2)) ∧ ptTest pH1632 (runFrom pH1632 (fmask pH1632) (cmask pH1632) (hmask pH1632) 1154 478 (true, H1632_cp1.1, H1632_cp1.2)) 1632 816 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1632_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1632_fin) true) H1632_seg1) (by decide) rfl H1632_fin ptTest_fst
noncomputable def I1632_cp1 : Nat × Nat := t7val% (fastRun pI1632 1 1153 (init pI1632) (init pI1632))
theorem I1632_seg1 : segOK pI1632 1 1153 (init pI1632) (init pI1632) I1632_cp1.1 I1632_cp1.2 = true := by
  decide +kernel
theorem I1632_fin : (prmOK pI1632 1632 && intTest pI1632 (runFrom pI1632 (fmask pI1632) (cmask pI1632) (hmask pI1632) 1154 478 (true, I1632_cp1.1, I1632_cp1.2)) 1632 21 true) = true := by
  decide +kernel
theorem I1632_ok : RunOK pI1632 1632 (runFrom pI1632 (fmask pI1632) (cmask pI1632) (hmask pI1632) 1154 478 (true, I1632_cp1.1, I1632_cp1.2)) ∧ intTest pI1632 (runFrom pI1632 (fmask pI1632) (cmask pI1632) (hmask pI1632) 1154 478 (true, I1632_cp1.1, I1632_cp1.2)) 1632 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1632_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1632_fin) true) I1632_seg1) (by decide) rfl I1632_fin intTest_fst
theorem link1632 : linkOK pL1632 pH1632 pI1632 = true := by decide +kernel
theorem cvx1632 : ConvexBetweenHumps 1632 :=
  cvx_of L1632_ok H1632_ok I1632_ok link1632 (by decide)
theorem cenlink1632 : cenLinkOK pI1632 1632 = true := by decide +kernel
theorem cen1632 : CenterUniqueMin 1632 ∧ DipHyp 1632 ∧ OnePointHyps 1632 :=
  cen_of L1632_ok H1632_ok I1632_ok link1632 cenlink1632

/-! ### `N = 1633` -/

def pL1633 : Prm := ⟨80, 37, 40, 1635, 11, 18446744073709551616, 116114008125671215, 116114008125671215⟩
def pH1633 : Prm := ⟨80, 37, 40, 1635, 11, 18446744073709551616, 116115107637298991, 116115107637298991⟩
def pI1633 : Prm := ⟨67, 33, 31, 1635, 11, 18446744073709551616, 116114008125671215, 116115107637298991⟩
noncomputable def L1633_cp1 : Nat × Nat := t7val% (fastRun pL1633 1 1154 (init pL1633) (init pL1633))
theorem L1633_seg1 : segOK pL1633 1 1154 (init pL1633) (init pL1633) L1633_cp1.1 L1633_cp1.2 = true := by
  decide +kernel
theorem L1633_fin : (prmOK pL1633 1633 && ptTest pL1633 (runFrom pL1633 (fmask pL1633) (cmask pL1633) (hmask pL1633) 1155 478 (true, L1633_cp1.1, L1633_cp1.2)) 1633 817 false) = true := by
  decide +kernel
theorem L1633_ok : RunOK pL1633 1633 (runFrom pL1633 (fmask pL1633) (cmask pL1633) (hmask pL1633) 1155 478 (true, L1633_cp1.1, L1633_cp1.2)) ∧ ptTest pL1633 (runFrom pL1633 (fmask pL1633) (cmask pL1633) (hmask pL1633) 1155 478 (true, L1633_cp1.1, L1633_cp1.2)) 1633 817 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1633_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1633_fin) true) L1633_seg1) (by decide) rfl L1633_fin ptTest_fst
noncomputable def H1633_cp1 : Nat × Nat := t7val% (fastRun pH1633 1 1154 (init pH1633) (init pH1633))
theorem H1633_seg1 : segOK pH1633 1 1154 (init pH1633) (init pH1633) H1633_cp1.1 H1633_cp1.2 = true := by
  decide +kernel
theorem H1633_fin : (prmOK pH1633 1633 && ptTest pH1633 (runFrom pH1633 (fmask pH1633) (cmask pH1633) (hmask pH1633) 1155 478 (true, H1633_cp1.1, H1633_cp1.2)) 1633 817 true) = true := by
  decide +kernel
theorem H1633_ok : RunOK pH1633 1633 (runFrom pH1633 (fmask pH1633) (cmask pH1633) (hmask pH1633) 1155 478 (true, H1633_cp1.1, H1633_cp1.2)) ∧ ptTest pH1633 (runFrom pH1633 (fmask pH1633) (cmask pH1633) (hmask pH1633) 1155 478 (true, H1633_cp1.1, H1633_cp1.2)) 1633 817 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1633_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1633_fin) true) H1633_seg1) (by decide) rfl H1633_fin ptTest_fst
noncomputable def I1633_cp1 : Nat × Nat := t7val% (fastRun pI1633 1 1154 (init pI1633) (init pI1633))
theorem I1633_seg1 : segOK pI1633 1 1154 (init pI1633) (init pI1633) I1633_cp1.1 I1633_cp1.2 = true := by
  decide +kernel
theorem I1633_fin : (prmOK pI1633 1633 && intTest pI1633 (runFrom pI1633 (fmask pI1633) (cmask pI1633) (hmask pI1633) 1155 478 (true, I1633_cp1.1, I1633_cp1.2)) 1633 21 false) = true := by
  decide +kernel
theorem I1633_ok : RunOK pI1633 1633 (runFrom pI1633 (fmask pI1633) (cmask pI1633) (hmask pI1633) 1155 478 (true, I1633_cp1.1, I1633_cp1.2)) ∧ intTest pI1633 (runFrom pI1633 (fmask pI1633) (cmask pI1633) (hmask pI1633) 1155 478 (true, I1633_cp1.1, I1633_cp1.2)) 1633 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1633_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1633_fin) true) I1633_seg1) (by decide) rfl I1633_fin intTest_fst
theorem link1633 : linkOK pL1633 pH1633 pI1633 = true := by decide +kernel
theorem cvx1633 : ConvexBetweenHumps 1633 :=
  cvx_of L1633_ok H1633_ok I1633_ok link1633 (by decide)

/-! ### `N = 1634` -/

def pL1634 : Prm := ⟨82, 40, 39, 1636, 11, 18446744073709551616, 116055989288524086, 116055989288524086⟩
def pH1634 : Prm := ⟨80, 37, 40, 1636, 11, 18446744073709551616, 116057088800151862, 116057088800151862⟩
def pI1634 : Prm := ⟨67, 33, 31, 1636, 11, 18446744073709551616, 116055989288524086, 116057088800151862⟩
noncomputable def L1634_cp1 : Nat × Nat := t7val% (fastRun pL1634 1 942 (init pL1634) (init pL1634))
theorem L1634_seg1 : segOK pL1634 1 942 (init pL1634) (init pL1634) L1634_cp1.1 L1634_cp1.2 = true := by
  decide +kernel
noncomputable def L1634_cp2 : Nat × Nat := t7val% (fastRun pL1634 1 1333 (init pL1634) (init pL1634))
theorem L1634_seg2 : segOK pL1634 943 391 L1634_cp1.1 L1634_cp1.2 L1634_cp2.1 L1634_cp2.2 = true := by
  decide +kernel
theorem L1634_fin : (prmOK pL1634 1634 && ptTest pL1634 (runFrom pL1634 (fmask pL1634) (cmask pL1634) (hmask pL1634) 1334 300 (true, L1634_cp2.1, L1634_cp2.2)) 1634 817 false) = true := by
  decide +kernel
theorem L1634_ok : RunOK pL1634 1634 (runFrom pL1634 (fmask pL1634) (cmask pL1634) (hmask pL1634) 1334 300 (true, L1634_cp2.1, L1634_cp2.2)) ∧ ptTest pL1634 (runFrom pL1634 (fmask pL1634) (cmask pL1634) (hmask pL1634) 1334 300 (true, L1634_cp2.1, L1634_cp2.2)) 1634 817 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1634_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1634_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1634_fin) true) L1634_seg1) L1634_seg2) (by decide) rfl L1634_fin ptTest_fst
noncomputable def H1634_cp1 : Nat × Nat := t7val% (fastRun pH1634 1 1154 (init pH1634) (init pH1634))
theorem H1634_seg1 : segOK pH1634 1 1154 (init pH1634) (init pH1634) H1634_cp1.1 H1634_cp1.2 = true := by
  decide +kernel
theorem H1634_fin : (prmOK pH1634 1634 && ptTest pH1634 (runFrom pH1634 (fmask pH1634) (cmask pH1634) (hmask pH1634) 1155 479 (true, H1634_cp1.1, H1634_cp1.2)) 1634 817 true) = true := by
  decide +kernel
theorem H1634_ok : RunOK pH1634 1634 (runFrom pH1634 (fmask pH1634) (cmask pH1634) (hmask pH1634) 1155 479 (true, H1634_cp1.1, H1634_cp1.2)) ∧ ptTest pH1634 (runFrom pH1634 (fmask pH1634) (cmask pH1634) (hmask pH1634) 1155 479 (true, H1634_cp1.1, H1634_cp1.2)) 1634 817 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1634_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1634_fin) true) H1634_seg1) (by decide) rfl H1634_fin ptTest_fst
noncomputable def I1634_cp1 : Nat × Nat := t7val% (fastRun pI1634 1 1154 (init pI1634) (init pI1634))
theorem I1634_seg1 : segOK pI1634 1 1154 (init pI1634) (init pI1634) I1634_cp1.1 I1634_cp1.2 = true := by
  decide +kernel
theorem I1634_fin : (prmOK pI1634 1634 && intTest pI1634 (runFrom pI1634 (fmask pI1634) (cmask pI1634) (hmask pI1634) 1155 479 (true, I1634_cp1.1, I1634_cp1.2)) 1634 21 true) = true := by
  decide +kernel
theorem I1634_ok : RunOK pI1634 1634 (runFrom pI1634 (fmask pI1634) (cmask pI1634) (hmask pI1634) 1155 479 (true, I1634_cp1.1, I1634_cp1.2)) ∧ intTest pI1634 (runFrom pI1634 (fmask pI1634) (cmask pI1634) (hmask pI1634) 1155 479 (true, I1634_cp1.1, I1634_cp1.2)) 1634 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1634_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1634_fin) true) I1634_seg1) (by decide) rfl I1634_fin intTest_fst
theorem link1634 : linkOK pL1634 pH1634 pI1634 = true := by decide +kernel
theorem cvx1634 : ConvexBetweenHumps 1634 :=
  cvx_of L1634_ok H1634_ok I1634_ok link1634 (by decide)
theorem cenlink1634 : cenLinkOK pI1634 1634 = true := by decide +kernel
theorem cen1634 : CenterUniqueMin 1634 ∧ DipHyp 1634 ∧ OnePointHyps 1634 :=
  cen_of L1634_ok H1634_ok I1634_ok link1634 cenlink1634

/-! ### `N = 1635` -/

def pL1635 : Prm := ⟨80, 37, 40, 1637, 11, 18446744073709551616, 115998007620293440, 115998007620293440⟩
def pH1635 : Prm := ⟨80, 37, 40, 1637, 11, 18446744073709551616, 115999107131921216, 115999107131921216⟩
def pI1635 : Prm := ⟨67, 33, 31, 1637, 11, 18446744073709551616, 115998007620293440, 115999107131921216⟩
noncomputable def L1635_cp1 : Nat × Nat := t7val% (fastRun pL1635 1 1155 (init pL1635) (init pL1635))
theorem L1635_seg1 : segOK pL1635 1 1155 (init pL1635) (init pL1635) L1635_cp1.1 L1635_cp1.2 = true := by
  decide +kernel
theorem L1635_fin : (prmOK pL1635 1635 && ptTest pL1635 (runFrom pL1635 (fmask pL1635) (cmask pL1635) (hmask pL1635) 1156 479 (true, L1635_cp1.1, L1635_cp1.2)) 1635 818 false) = true := by
  decide +kernel
theorem L1635_ok : RunOK pL1635 1635 (runFrom pL1635 (fmask pL1635) (cmask pL1635) (hmask pL1635) 1156 479 (true, L1635_cp1.1, L1635_cp1.2)) ∧ ptTest pL1635 (runFrom pL1635 (fmask pL1635) (cmask pL1635) (hmask pL1635) 1156 479 (true, L1635_cp1.1, L1635_cp1.2)) 1635 818 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1635_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1635_fin) true) L1635_seg1) (by decide) rfl L1635_fin ptTest_fst
noncomputable def H1635_cp1 : Nat × Nat := t7val% (fastRun pH1635 1 1155 (init pH1635) (init pH1635))
theorem H1635_seg1 : segOK pH1635 1 1155 (init pH1635) (init pH1635) H1635_cp1.1 H1635_cp1.2 = true := by
  decide +kernel
theorem H1635_fin : (prmOK pH1635 1635 && ptTest pH1635 (runFrom pH1635 (fmask pH1635) (cmask pH1635) (hmask pH1635) 1156 479 (true, H1635_cp1.1, H1635_cp1.2)) 1635 818 true) = true := by
  decide +kernel
theorem H1635_ok : RunOK pH1635 1635 (runFrom pH1635 (fmask pH1635) (cmask pH1635) (hmask pH1635) 1156 479 (true, H1635_cp1.1, H1635_cp1.2)) ∧ ptTest pH1635 (runFrom pH1635 (fmask pH1635) (cmask pH1635) (hmask pH1635) 1156 479 (true, H1635_cp1.1, H1635_cp1.2)) 1635 818 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1635_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1635_fin) true) H1635_seg1) (by decide) rfl H1635_fin ptTest_fst
noncomputable def I1635_cp1 : Nat × Nat := t7val% (fastRun pI1635 1 1155 (init pI1635) (init pI1635))
theorem I1635_seg1 : segOK pI1635 1 1155 (init pI1635) (init pI1635) I1635_cp1.1 I1635_cp1.2 = true := by
  decide +kernel
theorem I1635_fin : (prmOK pI1635 1635 && intTest pI1635 (runFrom pI1635 (fmask pI1635) (cmask pI1635) (hmask pI1635) 1156 479 (true, I1635_cp1.1, I1635_cp1.2)) 1635 21 false) = true := by
  decide +kernel
theorem I1635_ok : RunOK pI1635 1635 (runFrom pI1635 (fmask pI1635) (cmask pI1635) (hmask pI1635) 1156 479 (true, I1635_cp1.1, I1635_cp1.2)) ∧ intTest pI1635 (runFrom pI1635 (fmask pI1635) (cmask pI1635) (hmask pI1635) 1156 479 (true, I1635_cp1.1, I1635_cp1.2)) 1635 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1635_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1635_fin) true) I1635_seg1) (by decide) rfl I1635_fin intTest_fst
theorem link1635 : linkOK pL1635 pH1635 pI1635 = true := by decide +kernel
theorem cvx1635 : ConvexBetweenHumps 1635 :=
  cvx_of L1635_ok H1635_ok I1635_ok link1635 (by decide)

/-! ### `N = 1636` -/

def pL1636 : Prm := ⟨80, 37, 40, 1638, 11, 18446744073709551616, 115940114649007368, 115940114649007368⟩
def pH1636 : Prm := ⟨80, 37, 40, 1638, 11, 18446744073709551616, 115941214160635144, 115941214160635144⟩
def pI1636 : Prm := ⟨67, 33, 31, 1638, 11, 18446744073709551616, 115940114649007368, 115941214160635144⟩
noncomputable def L1636_cp1 : Nat × Nat := t7val% (fastRun pL1636 1 1156 (init pL1636) (init pL1636))
theorem L1636_seg1 : segOK pL1636 1 1156 (init pL1636) (init pL1636) L1636_cp1.1 L1636_cp1.2 = true := by
  decide +kernel
theorem L1636_fin : (prmOK pL1636 1636 && ptTest pL1636 (runFrom pL1636 (fmask pL1636) (cmask pL1636) (hmask pL1636) 1157 479 (true, L1636_cp1.1, L1636_cp1.2)) 1636 818 false) = true := by
  decide +kernel
theorem L1636_ok : RunOK pL1636 1636 (runFrom pL1636 (fmask pL1636) (cmask pL1636) (hmask pL1636) 1157 479 (true, L1636_cp1.1, L1636_cp1.2)) ∧ ptTest pL1636 (runFrom pL1636 (fmask pL1636) (cmask pL1636) (hmask pL1636) 1157 479 (true, L1636_cp1.1, L1636_cp1.2)) 1636 818 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1636_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1636_fin) true) L1636_seg1) (by decide) rfl L1636_fin ptTest_fst
noncomputable def H1636_cp1 : Nat × Nat := t7val% (fastRun pH1636 1 1156 (init pH1636) (init pH1636))
theorem H1636_seg1 : segOK pH1636 1 1156 (init pH1636) (init pH1636) H1636_cp1.1 H1636_cp1.2 = true := by
  decide +kernel
theorem H1636_fin : (prmOK pH1636 1636 && ptTest pH1636 (runFrom pH1636 (fmask pH1636) (cmask pH1636) (hmask pH1636) 1157 479 (true, H1636_cp1.1, H1636_cp1.2)) 1636 818 true) = true := by
  decide +kernel
theorem H1636_ok : RunOK pH1636 1636 (runFrom pH1636 (fmask pH1636) (cmask pH1636) (hmask pH1636) 1157 479 (true, H1636_cp1.1, H1636_cp1.2)) ∧ ptTest pH1636 (runFrom pH1636 (fmask pH1636) (cmask pH1636) (hmask pH1636) 1157 479 (true, H1636_cp1.1, H1636_cp1.2)) 1636 818 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1636_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1636_fin) true) H1636_seg1) (by decide) rfl H1636_fin ptTest_fst
noncomputable def I1636_cp1 : Nat × Nat := t7val% (fastRun pI1636 1 1156 (init pI1636) (init pI1636))
theorem I1636_seg1 : segOK pI1636 1 1156 (init pI1636) (init pI1636) I1636_cp1.1 I1636_cp1.2 = true := by
  decide +kernel
theorem I1636_fin : (prmOK pI1636 1636 && intTest pI1636 (runFrom pI1636 (fmask pI1636) (cmask pI1636) (hmask pI1636) 1157 479 (true, I1636_cp1.1, I1636_cp1.2)) 1636 21 true) = true := by
  decide +kernel
theorem I1636_ok : RunOK pI1636 1636 (runFrom pI1636 (fmask pI1636) (cmask pI1636) (hmask pI1636) 1157 479 (true, I1636_cp1.1, I1636_cp1.2)) ∧ intTest pI1636 (runFrom pI1636 (fmask pI1636) (cmask pI1636) (hmask pI1636) 1157 479 (true, I1636_cp1.1, I1636_cp1.2)) 1636 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1636_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1636_fin) true) I1636_seg1) (by decide) rfl I1636_fin intTest_fst
theorem link1636 : linkOK pL1636 pH1636 pI1636 = true := by decide +kernel
theorem cvx1636 : ConvexBetweenHumps 1636 :=
  cvx_of L1636_ok H1636_ok I1636_ok link1636 (by decide)
theorem cenlink1636 : cenLinkOK pI1636 1636 = true := by decide +kernel
theorem cen1636 : CenterUniqueMin 1636 ∧ DipHyp 1636 ∧ OnePointHyps 1636 :=
  cen_of L1636_ok H1636_ok I1636_ok link1636 cenlink1636

/-! ### `N = 1637` -/

def pL1637 : Prm := ⟨80, 37, 40, 1639, 11, 18446744073709551616, 115882258731419416, 115882258731419416⟩
def pH1637 : Prm := ⟨80, 37, 40, 1639, 11, 18446744073709551616, 115883358243047192, 115883358243047192⟩
def pI1637 : Prm := ⟨67, 33, 31, 1639, 11, 18446744073709551616, 115882258731419416, 115883358243047192⟩
noncomputable def L1637_cp1 : Nat × Nat := t7val% (fastRun pL1637 1 1157 (init pL1637) (init pL1637))
theorem L1637_seg1 : segOK pL1637 1 1157 (init pL1637) (init pL1637) L1637_cp1.1 L1637_cp1.2 = true := by
  decide +kernel
theorem L1637_fin : (prmOK pL1637 1637 && ptTest pL1637 (runFrom pL1637 (fmask pL1637) (cmask pL1637) (hmask pL1637) 1158 479 (true, L1637_cp1.1, L1637_cp1.2)) 1637 819 false) = true := by
  decide +kernel
theorem L1637_ok : RunOK pL1637 1637 (runFrom pL1637 (fmask pL1637) (cmask pL1637) (hmask pL1637) 1158 479 (true, L1637_cp1.1, L1637_cp1.2)) ∧ ptTest pL1637 (runFrom pL1637 (fmask pL1637) (cmask pL1637) (hmask pL1637) 1158 479 (true, L1637_cp1.1, L1637_cp1.2)) 1637 819 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1637_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1637_fin) true) L1637_seg1) (by decide) rfl L1637_fin ptTest_fst
noncomputable def H1637_cp1 : Nat × Nat := t7val% (fastRun pH1637 1 1157 (init pH1637) (init pH1637))
theorem H1637_seg1 : segOK pH1637 1 1157 (init pH1637) (init pH1637) H1637_cp1.1 H1637_cp1.2 = true := by
  decide +kernel
theorem H1637_fin : (prmOK pH1637 1637 && ptTest pH1637 (runFrom pH1637 (fmask pH1637) (cmask pH1637) (hmask pH1637) 1158 479 (true, H1637_cp1.1, H1637_cp1.2)) 1637 819 true) = true := by
  decide +kernel
theorem H1637_ok : RunOK pH1637 1637 (runFrom pH1637 (fmask pH1637) (cmask pH1637) (hmask pH1637) 1158 479 (true, H1637_cp1.1, H1637_cp1.2)) ∧ ptTest pH1637 (runFrom pH1637 (fmask pH1637) (cmask pH1637) (hmask pH1637) 1158 479 (true, H1637_cp1.1, H1637_cp1.2)) 1637 819 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1637_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1637_fin) true) H1637_seg1) (by decide) rfl H1637_fin ptTest_fst
noncomputable def I1637_cp1 : Nat × Nat := t7val% (fastRun pI1637 1 1157 (init pI1637) (init pI1637))
theorem I1637_seg1 : segOK pI1637 1 1157 (init pI1637) (init pI1637) I1637_cp1.1 I1637_cp1.2 = true := by
  decide +kernel
theorem I1637_fin : (prmOK pI1637 1637 && intTest pI1637 (runFrom pI1637 (fmask pI1637) (cmask pI1637) (hmask pI1637) 1158 479 (true, I1637_cp1.1, I1637_cp1.2)) 1637 21 false) = true := by
  decide +kernel
theorem I1637_ok : RunOK pI1637 1637 (runFrom pI1637 (fmask pI1637) (cmask pI1637) (hmask pI1637) 1158 479 (true, I1637_cp1.1, I1637_cp1.2)) ∧ intTest pI1637 (runFrom pI1637 (fmask pI1637) (cmask pI1637) (hmask pI1637) 1158 479 (true, I1637_cp1.1, I1637_cp1.2)) 1637 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1637_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1637_fin) true) I1637_seg1) (by decide) rfl I1637_fin intTest_fst
theorem link1637 : linkOK pL1637 pH1637 pI1637 = true := by decide +kernel
theorem cvx1637 : ConvexBetweenHumps 1637 :=
  cvx_of L1637_ok H1637_ok I1637_ok link1637 (by decide)

/-! ### `N = 1638` -/

def pL1638 : Prm := ⟨80, 37, 40, 1640, 11, 18446744073709551616, 115824491204006684, 115824491204006684⟩
def pH1638 : Prm := ⟨80, 37, 40, 1640, 11, 18446744073709551616, 115825590715634460, 115825590715634460⟩
def pI1638 : Prm := ⟨67, 33, 31, 1640, 11, 18446744073709551616, 115824491204006684, 115825590715634460⟩
noncomputable def L1638_cp1 : Nat × Nat := t7val% (fastRun pL1638 1 1157 (init pL1638) (init pL1638))
theorem L1638_seg1 : segOK pL1638 1 1157 (init pL1638) (init pL1638) L1638_cp1.1 L1638_cp1.2 = true := by
  decide +kernel
theorem L1638_fin : (prmOK pL1638 1638 && ptTest pL1638 (runFrom pL1638 (fmask pL1638) (cmask pL1638) (hmask pL1638) 1158 480 (true, L1638_cp1.1, L1638_cp1.2)) 1638 819 false) = true := by
  decide +kernel
theorem L1638_ok : RunOK pL1638 1638 (runFrom pL1638 (fmask pL1638) (cmask pL1638) (hmask pL1638) 1158 480 (true, L1638_cp1.1, L1638_cp1.2)) ∧ ptTest pL1638 (runFrom pL1638 (fmask pL1638) (cmask pL1638) (hmask pL1638) 1158 480 (true, L1638_cp1.1, L1638_cp1.2)) 1638 819 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1638_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1638_fin) true) L1638_seg1) (by decide) rfl L1638_fin ptTest_fst
noncomputable def H1638_cp1 : Nat × Nat := t7val% (fastRun pH1638 1 1157 (init pH1638) (init pH1638))
theorem H1638_seg1 : segOK pH1638 1 1157 (init pH1638) (init pH1638) H1638_cp1.1 H1638_cp1.2 = true := by
  decide +kernel
theorem H1638_fin : (prmOK pH1638 1638 && ptTest pH1638 (runFrom pH1638 (fmask pH1638) (cmask pH1638) (hmask pH1638) 1158 480 (true, H1638_cp1.1, H1638_cp1.2)) 1638 819 true) = true := by
  decide +kernel
theorem H1638_ok : RunOK pH1638 1638 (runFrom pH1638 (fmask pH1638) (cmask pH1638) (hmask pH1638) 1158 480 (true, H1638_cp1.1, H1638_cp1.2)) ∧ ptTest pH1638 (runFrom pH1638 (fmask pH1638) (cmask pH1638) (hmask pH1638) 1158 480 (true, H1638_cp1.1, H1638_cp1.2)) 1638 819 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1638_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1638_fin) true) H1638_seg1) (by decide) rfl H1638_fin ptTest_fst
noncomputable def I1638_cp1 : Nat × Nat := t7val% (fastRun pI1638 1 1157 (init pI1638) (init pI1638))
theorem I1638_seg1 : segOK pI1638 1 1157 (init pI1638) (init pI1638) I1638_cp1.1 I1638_cp1.2 = true := by
  decide +kernel
theorem I1638_fin : (prmOK pI1638 1638 && intTest pI1638 (runFrom pI1638 (fmask pI1638) (cmask pI1638) (hmask pI1638) 1158 480 (true, I1638_cp1.1, I1638_cp1.2)) 1638 21 true) = true := by
  decide +kernel
theorem I1638_ok : RunOK pI1638 1638 (runFrom pI1638 (fmask pI1638) (cmask pI1638) (hmask pI1638) 1158 480 (true, I1638_cp1.1, I1638_cp1.2)) ∧ intTest pI1638 (runFrom pI1638 (fmask pI1638) (cmask pI1638) (hmask pI1638) 1158 480 (true, I1638_cp1.1, I1638_cp1.2)) 1638 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1638_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1638_fin) true) I1638_seg1) (by decide) rfl I1638_fin intTest_fst
theorem link1638 : linkOK pL1638 pH1638 pI1638 = true := by decide +kernel
theorem cvx1638 : ConvexBetweenHumps 1638 :=
  cvx_of L1638_ok H1638_ok I1638_ok link1638 (by decide)
theorem cenlink1638 : cenLinkOK pI1638 1638 = true := by decide +kernel
theorem cen1638 : CenterUniqueMin 1638 ∧ DipHyp 1638 ∧ OnePointHyps 1638 :=
  cen_of L1638_ok H1638_ok I1638_ok link1638 cenlink1638

/-! ### The range -/

theorem cvx_1624_1638 {N : ℕ} (h1 : 1624 ≤ N) (h2 : N ≤ 1638) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1630
  · by_cases h4 : N ≤ 1626
    · by_cases h6 : N ≤ 1624
      · obtain rfl : N = 1624 := by omega
        exact cvx1624
      · by_cases h8 : N ≤ 1625
        · obtain rfl : N = 1625 := by omega
          exact cvx1625
        · obtain rfl : N = 1626 := by omega
          exact cvx1626
    · by_cases h6 : N ≤ 1628
      · by_cases h8 : N ≤ 1627
        · obtain rfl : N = 1627 := by omega
          exact cvx1627
        · obtain rfl : N = 1628 := by omega
          exact cvx1628
      · by_cases h8 : N ≤ 1629
        · obtain rfl : N = 1629 := by omega
          exact cvx1629
        · obtain rfl : N = 1630 := by omega
          exact cvx1630
  · by_cases h4 : N ≤ 1634
    · by_cases h6 : N ≤ 1632
      · by_cases h8 : N ≤ 1631
        · obtain rfl : N = 1631 := by omega
          exact cvx1631
        · obtain rfl : N = 1632 := by omega
          exact cvx1632
      · by_cases h8 : N ≤ 1633
        · obtain rfl : N = 1633 := by omega
          exact cvx1633
        · obtain rfl : N = 1634 := by omega
          exact cvx1634
    · by_cases h6 : N ≤ 1636
      · by_cases h8 : N ≤ 1635
        · obtain rfl : N = 1635 := by omega
          exact cvx1635
        · obtain rfl : N = 1636 := by omega
          exact cvx1636
      · by_cases h8 : N ≤ 1637
        · obtain rfl : N = 1637 := by omega
          exact cvx1637
        · obtain rfl : N = 1638 := by omega
          exact cvx1638

theorem cen_1624_1638 {N : ℕ} (h1 : 1624 ≤ N) (h2 : N ≤ 1638) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1630
  · by_cases h4 : N ≤ 1626
    · by_cases h6 : N ≤ 1624
      · obtain rfl : N = 1624 := by omega
        exact cen1624
      · obtain rfl : N = 1626 := by omega
        exact cen1626
    · by_cases h6 : N ≤ 1628
      · obtain rfl : N = 1628 := by omega
        exact cen1628
      · obtain rfl : N = 1630 := by omega
        exact cen1630
  · by_cases h4 : N ≤ 1634
    · by_cases h6 : N ≤ 1632
      · obtain rfl : N = 1632 := by omega
        exact cen1632
      · obtain rfl : N = 1634 := by omega
        exact cen1634
    · by_cases h6 : N ≤ 1636
      · obtain rfl : N = 1636 := by omega
        exact cen1636
      · obtain rfl : N = 1638 := by omega
        exact cen1638

end Kagey131.PaperD.T7
