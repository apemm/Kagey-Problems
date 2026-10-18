import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1784, …, 1795` (generated)

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

/-! ### `N = 1784` -/

def pL1784 : Prm := ⟨80, 37, 40, 1786, 11, 18446744073709551616, 108009921563275516, 108009921563275516⟩
def pH1784 : Prm := ⟨80, 37, 40, 1786, 11, 18446744073709551616, 108011021074903292, 108011021074903292⟩
def pI1784 : Prm := ⟨67, 34, 30, 1786, 11, 18446744073709551616, 108009921563275516, 108011021074903292⟩
noncomputable def L1784_cp1 : Nat × Nat := t7val% (fastRun pL1784 1 1029 (init pL1784) (init pL1784))
theorem L1784_seg1 : segOK pL1784 1 1029 (init pL1784) (init pL1784) L1784_cp1.1 L1784_cp1.2 = true := by
  decide +kernel
noncomputable def L1784_cp2 : Nat × Nat := t7val% (fastRun pL1784 1 1456 (init pL1784) (init pL1784))
theorem L1784_seg2 : segOK pL1784 1030 427 L1784_cp1.1 L1784_cp1.2 L1784_cp2.1 L1784_cp2.2 = true := by
  decide +kernel
theorem L1784_fin : (prmOK pL1784 1784 && ptTest pL1784 (runFrom pL1784 (fmask pL1784) (cmask pL1784) (hmask pL1784) 1457 327 (true, L1784_cp2.1, L1784_cp2.2)) 1784 892 false) = true := by
  decide +kernel
theorem L1784_ok : RunOK pL1784 1784 (runFrom pL1784 (fmask pL1784) (cmask pL1784) (hmask pL1784) 1457 327 (true, L1784_cp2.1, L1784_cp2.2)) ∧ ptTest pL1784 (runFrom pL1784 (fmask pL1784) (cmask pL1784) (hmask pL1784) 1457 327 (true, L1784_cp2.1, L1784_cp2.2)) 1784 892 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1784_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1784_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1784_fin) true) L1784_seg1) L1784_seg2) (by decide) rfl L1784_fin ptTest_fst
noncomputable def H1784_cp1 : Nat × Nat := t7val% (fastRun pH1784 1 1029 (init pH1784) (init pH1784))
theorem H1784_seg1 : segOK pH1784 1 1029 (init pH1784) (init pH1784) H1784_cp1.1 H1784_cp1.2 = true := by
  decide +kernel
noncomputable def H1784_cp2 : Nat × Nat := t7val% (fastRun pH1784 1 1456 (init pH1784) (init pH1784))
theorem H1784_seg2 : segOK pH1784 1030 427 H1784_cp1.1 H1784_cp1.2 H1784_cp2.1 H1784_cp2.2 = true := by
  decide +kernel
theorem H1784_fin : (prmOK pH1784 1784 && ptTest pH1784 (runFrom pH1784 (fmask pH1784) (cmask pH1784) (hmask pH1784) 1457 327 (true, H1784_cp2.1, H1784_cp2.2)) 1784 892 true) = true := by
  decide +kernel
theorem H1784_ok : RunOK pH1784 1784 (runFrom pH1784 (fmask pH1784) (cmask pH1784) (hmask pH1784) 1457 327 (true, H1784_cp2.1, H1784_cp2.2)) ∧ ptTest pH1784 (runFrom pH1784 (fmask pH1784) (cmask pH1784) (hmask pH1784) 1457 327 (true, H1784_cp2.1, H1784_cp2.2)) 1784 892 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1784_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1784_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1784_fin) true) H1784_seg1) H1784_seg2) (by decide) rfl H1784_fin ptTest_fst
noncomputable def I1784_cp1 : Nat × Nat := t7val% (fastRun pI1784 1 1260 (init pI1784) (init pI1784))
theorem I1784_seg1 : segOK pI1784 1 1260 (init pI1784) (init pI1784) I1784_cp1.1 I1784_cp1.2 = true := by
  decide +kernel
theorem I1784_fin : (prmOK pI1784 1784 && intTest pI1784 (runFrom pI1784 (fmask pI1784) (cmask pI1784) (hmask pI1784) 1261 523 (true, I1784_cp1.1, I1784_cp1.2)) 1784 21 true) = true := by
  decide +kernel
theorem I1784_ok : RunOK pI1784 1784 (runFrom pI1784 (fmask pI1784) (cmask pI1784) (hmask pI1784) 1261 523 (true, I1784_cp1.1, I1784_cp1.2)) ∧ intTest pI1784 (runFrom pI1784 (fmask pI1784) (cmask pI1784) (hmask pI1784) 1261 523 (true, I1784_cp1.1, I1784_cp1.2)) 1784 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1784_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1784_fin) true) I1784_seg1) (by decide) rfl I1784_fin intTest_fst
theorem link1784 : linkOK pL1784 pH1784 pI1784 = true := by decide +kernel
theorem cvx1784 : ConvexBetweenHumps 1784 :=
  cvx_of L1784_ok H1784_ok I1784_ok link1784 (by decide)
theorem cenlink1784 : cenLinkOK pI1784 1784 = true := by decide +kernel
theorem cen1784 : CenterUniqueMin 1784 ∧ DipHyp 1784 ∧ OnePointHyps 1784 :=
  cen_of L1784_ok H1784_ok I1784_ok link1784 cenlink1784

/-! ### `N = 1785` -/

def pL1785 : Prm := ⟨80, 37, 40, 1787, 11, 18446744073709551616, 107960318611423177, 107960318611423177⟩
def pH1785 : Prm := ⟨80, 37, 40, 1787, 11, 18446744073709551616, 107961418123050953, 107961418123050953⟩
def pI1785 : Prm := ⟨67, 34, 30, 1787, 11, 18446744073709551616, 107960318611423177, 107961418123050953⟩
noncomputable def L1785_cp1 : Nat × Nat := t7val% (fastRun pL1785 1 1030 (init pL1785) (init pL1785))
theorem L1785_seg1 : segOK pL1785 1 1030 (init pL1785) (init pL1785) L1785_cp1.1 L1785_cp1.2 = true := by
  decide +kernel
noncomputable def L1785_cp2 : Nat × Nat := t7val% (fastRun pL1785 1 1456 (init pL1785) (init pL1785))
theorem L1785_seg2 : segOK pL1785 1031 426 L1785_cp1.1 L1785_cp1.2 L1785_cp2.1 L1785_cp2.2 = true := by
  decide +kernel
theorem L1785_fin : (prmOK pL1785 1785 && ptTest pL1785 (runFrom pL1785 (fmask pL1785) (cmask pL1785) (hmask pL1785) 1457 328 (true, L1785_cp2.1, L1785_cp2.2)) 1785 893 false) = true := by
  decide +kernel
theorem L1785_ok : RunOK pL1785 1785 (runFrom pL1785 (fmask pL1785) (cmask pL1785) (hmask pL1785) 1457 328 (true, L1785_cp2.1, L1785_cp2.2)) ∧ ptTest pL1785 (runFrom pL1785 (fmask pL1785) (cmask pL1785) (hmask pL1785) 1457 328 (true, L1785_cp2.1, L1785_cp2.2)) 1785 893 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1785_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1785_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1785_fin) true) L1785_seg1) L1785_seg2) (by decide) rfl L1785_fin ptTest_fst
noncomputable def H1785_cp1 : Nat × Nat := t7val% (fastRun pH1785 1 1030 (init pH1785) (init pH1785))
theorem H1785_seg1 : segOK pH1785 1 1030 (init pH1785) (init pH1785) H1785_cp1.1 H1785_cp1.2 = true := by
  decide +kernel
noncomputable def H1785_cp2 : Nat × Nat := t7val% (fastRun pH1785 1 1456 (init pH1785) (init pH1785))
theorem H1785_seg2 : segOK pH1785 1031 426 H1785_cp1.1 H1785_cp1.2 H1785_cp2.1 H1785_cp2.2 = true := by
  decide +kernel
theorem H1785_fin : (prmOK pH1785 1785 && ptTest pH1785 (runFrom pH1785 (fmask pH1785) (cmask pH1785) (hmask pH1785) 1457 328 (true, H1785_cp2.1, H1785_cp2.2)) 1785 893 true) = true := by
  decide +kernel
theorem H1785_ok : RunOK pH1785 1785 (runFrom pH1785 (fmask pH1785) (cmask pH1785) (hmask pH1785) 1457 328 (true, H1785_cp2.1, H1785_cp2.2)) ∧ ptTest pH1785 (runFrom pH1785 (fmask pH1785) (cmask pH1785) (hmask pH1785) 1457 328 (true, H1785_cp2.1, H1785_cp2.2)) 1785 893 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1785_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1785_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1785_fin) true) H1785_seg1) H1785_seg2) (by decide) rfl H1785_fin ptTest_fst
noncomputable def I1785_cp1 : Nat × Nat := t7val% (fastRun pI1785 1 1261 (init pI1785) (init pI1785))
theorem I1785_seg1 : segOK pI1785 1 1261 (init pI1785) (init pI1785) I1785_cp1.1 I1785_cp1.2 = true := by
  decide +kernel
theorem I1785_fin : (prmOK pI1785 1785 && intTest pI1785 (runFrom pI1785 (fmask pI1785) (cmask pI1785) (hmask pI1785) 1262 523 (true, I1785_cp1.1, I1785_cp1.2)) 1785 21 false) = true := by
  decide +kernel
theorem I1785_ok : RunOK pI1785 1785 (runFrom pI1785 (fmask pI1785) (cmask pI1785) (hmask pI1785) 1262 523 (true, I1785_cp1.1, I1785_cp1.2)) ∧ intTest pI1785 (runFrom pI1785 (fmask pI1785) (cmask pI1785) (hmask pI1785) 1262 523 (true, I1785_cp1.1, I1785_cp1.2)) 1785 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1785_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1785_fin) true) I1785_seg1) (by decide) rfl I1785_fin intTest_fst
theorem link1785 : linkOK pL1785 pH1785 pI1785 = true := by decide +kernel
theorem cvx1785 : ConvexBetweenHumps 1785 :=
  cvx_of L1785_ok H1785_ok I1785_ok link1785 (by decide)

/-! ### `N = 1786` -/

def pL1786 : Prm := ⟨80, 37, 40, 1788, 11, 18446744073709551616, 107910784817133793, 107910784817133793⟩
def pH1786 : Prm := ⟨80, 37, 40, 1788, 11, 18446744073709551616, 107911884328761569, 107911884328761569⟩
def pI1786 : Prm := ⟨67, 34, 30, 1788, 11, 18446744073709551616, 107910784817133793, 107911884328761569⟩
noncomputable def L1786_cp1 : Nat × Nat := t7val% (fastRun pL1786 1 1030 (init pL1786) (init pL1786))
theorem L1786_seg1 : segOK pL1786 1 1030 (init pL1786) (init pL1786) L1786_cp1.1 L1786_cp1.2 = true := by
  decide +kernel
noncomputable def L1786_cp2 : Nat × Nat := t7val% (fastRun pL1786 1 1457 (init pL1786) (init pL1786))
theorem L1786_seg2 : segOK pL1786 1031 427 L1786_cp1.1 L1786_cp1.2 L1786_cp2.1 L1786_cp2.2 = true := by
  decide +kernel
theorem L1786_fin : (prmOK pL1786 1786 && ptTest pL1786 (runFrom pL1786 (fmask pL1786) (cmask pL1786) (hmask pL1786) 1458 328 (true, L1786_cp2.1, L1786_cp2.2)) 1786 893 false) = true := by
  decide +kernel
theorem L1786_ok : RunOK pL1786 1786 (runFrom pL1786 (fmask pL1786) (cmask pL1786) (hmask pL1786) 1458 328 (true, L1786_cp2.1, L1786_cp2.2)) ∧ ptTest pL1786 (runFrom pL1786 (fmask pL1786) (cmask pL1786) (hmask pL1786) 1458 328 (true, L1786_cp2.1, L1786_cp2.2)) 1786 893 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1786_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1786_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1786_fin) true) L1786_seg1) L1786_seg2) (by decide) rfl L1786_fin ptTest_fst
noncomputable def H1786_cp1 : Nat × Nat := t7val% (fastRun pH1786 1 1030 (init pH1786) (init pH1786))
theorem H1786_seg1 : segOK pH1786 1 1030 (init pH1786) (init pH1786) H1786_cp1.1 H1786_cp1.2 = true := by
  decide +kernel
noncomputable def H1786_cp2 : Nat × Nat := t7val% (fastRun pH1786 1 1457 (init pH1786) (init pH1786))
theorem H1786_seg2 : segOK pH1786 1031 427 H1786_cp1.1 H1786_cp1.2 H1786_cp2.1 H1786_cp2.2 = true := by
  decide +kernel
theorem H1786_fin : (prmOK pH1786 1786 && ptTest pH1786 (runFrom pH1786 (fmask pH1786) (cmask pH1786) (hmask pH1786) 1458 328 (true, H1786_cp2.1, H1786_cp2.2)) 1786 893 true) = true := by
  decide +kernel
theorem H1786_ok : RunOK pH1786 1786 (runFrom pH1786 (fmask pH1786) (cmask pH1786) (hmask pH1786) 1458 328 (true, H1786_cp2.1, H1786_cp2.2)) ∧ ptTest pH1786 (runFrom pH1786 (fmask pH1786) (cmask pH1786) (hmask pH1786) 1458 328 (true, H1786_cp2.1, H1786_cp2.2)) 1786 893 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1786_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1786_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1786_fin) true) H1786_seg1) H1786_seg2) (by decide) rfl H1786_fin ptTest_fst
noncomputable def I1786_cp1 : Nat × Nat := t7val% (fastRun pI1786 1 1262 (init pI1786) (init pI1786))
theorem I1786_seg1 : segOK pI1786 1 1262 (init pI1786) (init pI1786) I1786_cp1.1 I1786_cp1.2 = true := by
  decide +kernel
theorem I1786_fin : (prmOK pI1786 1786 && intTest pI1786 (runFrom pI1786 (fmask pI1786) (cmask pI1786) (hmask pI1786) 1263 523 (true, I1786_cp1.1, I1786_cp1.2)) 1786 21 true) = true := by
  decide +kernel
theorem I1786_ok : RunOK pI1786 1786 (runFrom pI1786 (fmask pI1786) (cmask pI1786) (hmask pI1786) 1263 523 (true, I1786_cp1.1, I1786_cp1.2)) ∧ intTest pI1786 (runFrom pI1786 (fmask pI1786) (cmask pI1786) (hmask pI1786) 1263 523 (true, I1786_cp1.1, I1786_cp1.2)) 1786 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1786_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1786_fin) true) I1786_seg1) (by decide) rfl I1786_fin intTest_fst
theorem link1786 : linkOK pL1786 pH1786 pI1786 = true := by decide +kernel
theorem cvx1786 : ConvexBetweenHumps 1786 :=
  cvx_of L1786_ok H1786_ok I1786_ok link1786 (by decide)
theorem cenlink1786 : cenLinkOK pI1786 1786 = true := by decide +kernel
theorem cen1786 : CenterUniqueMin 1786 ∧ DipHyp 1786 ∧ OnePointHyps 1786 :=
  cen_of L1786_ok H1786_ok I1786_ok link1786 cenlink1786

/-! ### `N = 1787` -/

def pL1787 : Prm := ⟨80, 37, 40, 1789, 11, 18446744073709551616, 107861280655509622, 107861280655509622⟩
def pH1787 : Prm := ⟨80, 37, 40, 1789, 11, 18446744073709551616, 107862380167137398, 107862380167137398⟩
def pI1787 : Prm := ⟨67, 34, 30, 1789, 11, 18446744073709551616, 107861280655509622, 107862380167137398⟩
noncomputable def L1787_cp1 : Nat × Nat := t7val% (fastRun pL1787 1 1031 (init pL1787) (init pL1787))
theorem L1787_seg1 : segOK pL1787 1 1031 (init pL1787) (init pL1787) L1787_cp1.1 L1787_cp1.2 = true := by
  decide +kernel
noncomputable def L1787_cp2 : Nat × Nat := t7val% (fastRun pL1787 1 1458 (init pL1787) (init pL1787))
theorem L1787_seg2 : segOK pL1787 1032 427 L1787_cp1.1 L1787_cp1.2 L1787_cp2.1 L1787_cp2.2 = true := by
  decide +kernel
theorem L1787_fin : (prmOK pL1787 1787 && ptTest pL1787 (runFrom pL1787 (fmask pL1787) (cmask pL1787) (hmask pL1787) 1459 328 (true, L1787_cp2.1, L1787_cp2.2)) 1787 894 false) = true := by
  decide +kernel
theorem L1787_ok : RunOK pL1787 1787 (runFrom pL1787 (fmask pL1787) (cmask pL1787) (hmask pL1787) 1459 328 (true, L1787_cp2.1, L1787_cp2.2)) ∧ ptTest pL1787 (runFrom pL1787 (fmask pL1787) (cmask pL1787) (hmask pL1787) 1459 328 (true, L1787_cp2.1, L1787_cp2.2)) 1787 894 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1787_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1787_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1787_fin) true) L1787_seg1) L1787_seg2) (by decide) rfl L1787_fin ptTest_fst
noncomputable def H1787_cp1 : Nat × Nat := t7val% (fastRun pH1787 1 1031 (init pH1787) (init pH1787))
theorem H1787_seg1 : segOK pH1787 1 1031 (init pH1787) (init pH1787) H1787_cp1.1 H1787_cp1.2 = true := by
  decide +kernel
noncomputable def H1787_cp2 : Nat × Nat := t7val% (fastRun pH1787 1 1458 (init pH1787) (init pH1787))
theorem H1787_seg2 : segOK pH1787 1032 427 H1787_cp1.1 H1787_cp1.2 H1787_cp2.1 H1787_cp2.2 = true := by
  decide +kernel
theorem H1787_fin : (prmOK pH1787 1787 && ptTest pH1787 (runFrom pH1787 (fmask pH1787) (cmask pH1787) (hmask pH1787) 1459 328 (true, H1787_cp2.1, H1787_cp2.2)) 1787 894 true) = true := by
  decide +kernel
theorem H1787_ok : RunOK pH1787 1787 (runFrom pH1787 (fmask pH1787) (cmask pH1787) (hmask pH1787) 1459 328 (true, H1787_cp2.1, H1787_cp2.2)) ∧ ptTest pH1787 (runFrom pH1787 (fmask pH1787) (cmask pH1787) (hmask pH1787) 1459 328 (true, H1787_cp2.1, H1787_cp2.2)) 1787 894 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1787_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1787_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1787_fin) true) H1787_seg1) H1787_seg2) (by decide) rfl H1787_fin ptTest_fst
noncomputable def I1787_cp1 : Nat × Nat := t7val% (fastRun pI1787 1 1263 (init pI1787) (init pI1787))
theorem I1787_seg1 : segOK pI1787 1 1263 (init pI1787) (init pI1787) I1787_cp1.1 I1787_cp1.2 = true := by
  decide +kernel
theorem I1787_fin : (prmOK pI1787 1787 && intTest pI1787 (runFrom pI1787 (fmask pI1787) (cmask pI1787) (hmask pI1787) 1264 523 (true, I1787_cp1.1, I1787_cp1.2)) 1787 21 false) = true := by
  decide +kernel
theorem I1787_ok : RunOK pI1787 1787 (runFrom pI1787 (fmask pI1787) (cmask pI1787) (hmask pI1787) 1264 523 (true, I1787_cp1.1, I1787_cp1.2)) ∧ intTest pI1787 (runFrom pI1787 (fmask pI1787) (cmask pI1787) (hmask pI1787) 1264 523 (true, I1787_cp1.1, I1787_cp1.2)) 1787 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1787_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1787_fin) true) I1787_seg1) (by decide) rfl I1787_fin intTest_fst
theorem link1787 : linkOK pL1787 pH1787 pI1787 = true := by decide +kernel
theorem cvx1787 : ConvexBetweenHumps 1787 :=
  cvx_of L1787_ok H1787_ok I1787_ok link1787 (by decide)

/-! ### `N = 1788` -/

def pL1788 : Prm := ⟨80, 37, 40, 1790, 11, 18446744073709551616, 107811845432171959, 107811845432171959⟩
def pH1788 : Prm := ⟨80, 37, 40, 1790, 11, 18446744073709551616, 107812944943799735, 107812944943799735⟩
def pI1788 : Prm := ⟨67, 34, 30, 1790, 11, 18446744073709551616, 107811845432171959, 107812944943799735⟩
noncomputable def L1788_cp1 : Nat × Nat := t7val% (fastRun pL1788 1 1031 (init pL1788) (init pL1788))
theorem L1788_seg1 : segOK pL1788 1 1031 (init pL1788) (init pL1788) L1788_cp1.1 L1788_cp1.2 = true := by
  decide +kernel
noncomputable def L1788_cp2 : Nat × Nat := t7val% (fastRun pL1788 1 1459 (init pL1788) (init pL1788))
theorem L1788_seg2 : segOK pL1788 1032 428 L1788_cp1.1 L1788_cp1.2 L1788_cp2.1 L1788_cp2.2 = true := by
  decide +kernel
theorem L1788_fin : (prmOK pL1788 1788 && ptTest pL1788 (runFrom pL1788 (fmask pL1788) (cmask pL1788) (hmask pL1788) 1460 328 (true, L1788_cp2.1, L1788_cp2.2)) 1788 894 false) = true := by
  decide +kernel
theorem L1788_ok : RunOK pL1788 1788 (runFrom pL1788 (fmask pL1788) (cmask pL1788) (hmask pL1788) 1460 328 (true, L1788_cp2.1, L1788_cp2.2)) ∧ ptTest pL1788 (runFrom pL1788 (fmask pL1788) (cmask pL1788) (hmask pL1788) 1460 328 (true, L1788_cp2.1, L1788_cp2.2)) 1788 894 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1788_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1788_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1788_fin) true) L1788_seg1) L1788_seg2) (by decide) rfl L1788_fin ptTest_fst
noncomputable def H1788_cp1 : Nat × Nat := t7val% (fastRun pH1788 1 1031 (init pH1788) (init pH1788))
theorem H1788_seg1 : segOK pH1788 1 1031 (init pH1788) (init pH1788) H1788_cp1.1 H1788_cp1.2 = true := by
  decide +kernel
noncomputable def H1788_cp2 : Nat × Nat := t7val% (fastRun pH1788 1 1459 (init pH1788) (init pH1788))
theorem H1788_seg2 : segOK pH1788 1032 428 H1788_cp1.1 H1788_cp1.2 H1788_cp2.1 H1788_cp2.2 = true := by
  decide +kernel
theorem H1788_fin : (prmOK pH1788 1788 && ptTest pH1788 (runFrom pH1788 (fmask pH1788) (cmask pH1788) (hmask pH1788) 1460 328 (true, H1788_cp2.1, H1788_cp2.2)) 1788 894 true) = true := by
  decide +kernel
theorem H1788_ok : RunOK pH1788 1788 (runFrom pH1788 (fmask pH1788) (cmask pH1788) (hmask pH1788) 1460 328 (true, H1788_cp2.1, H1788_cp2.2)) ∧ ptTest pH1788 (runFrom pH1788 (fmask pH1788) (cmask pH1788) (hmask pH1788) 1460 328 (true, H1788_cp2.1, H1788_cp2.2)) 1788 894 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1788_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1788_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1788_fin) true) H1788_seg1) H1788_seg2) (by decide) rfl H1788_fin ptTest_fst
noncomputable def I1788_cp1 : Nat × Nat := t7val% (fastRun pI1788 1 1263 (init pI1788) (init pI1788))
theorem I1788_seg1 : segOK pI1788 1 1263 (init pI1788) (init pI1788) I1788_cp1.1 I1788_cp1.2 = true := by
  decide +kernel
theorem I1788_fin : (prmOK pI1788 1788 && intTest pI1788 (runFrom pI1788 (fmask pI1788) (cmask pI1788) (hmask pI1788) 1264 524 (true, I1788_cp1.1, I1788_cp1.2)) 1788 21 true) = true := by
  decide +kernel
theorem I1788_ok : RunOK pI1788 1788 (runFrom pI1788 (fmask pI1788) (cmask pI1788) (hmask pI1788) 1264 524 (true, I1788_cp1.1, I1788_cp1.2)) ∧ intTest pI1788 (runFrom pI1788 (fmask pI1788) (cmask pI1788) (hmask pI1788) 1264 524 (true, I1788_cp1.1, I1788_cp1.2)) 1788 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1788_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1788_fin) true) I1788_seg1) (by decide) rfl I1788_fin intTest_fst
theorem link1788 : linkOK pL1788 pH1788 pI1788 = true := by decide +kernel
theorem cvx1788 : ConvexBetweenHumps 1788 :=
  cvx_of L1788_ok H1788_ok I1788_ok link1788 (by decide)
theorem cenlink1788 : cenLinkOK pI1788 1788 = true := by decide +kernel
theorem cen1788 : CenterUniqueMin 1788 ∧ DipHyp 1788 ∧ OnePointHyps 1788 :=
  cen_of L1788_ok H1788_ok I1788_ok link1788 cenlink1788

/-! ### `N = 1789` -/

def pL1789 : Prm := ⟨80, 37, 40, 1791, 11, 18446744073709551616, 107762439756810507, 107762439756810507⟩
def pH1789 : Prm := ⟨80, 37, 40, 1791, 11, 18446744073709551616, 107763539268438283, 107763539268438283⟩
def pI1789 : Prm := ⟨67, 34, 30, 1791, 11, 18446744073709551616, 107762439756810507, 107763539268438283⟩
noncomputable def L1789_cp1 : Nat × Nat := t7val% (fastRun pL1789 1 1032 (init pL1789) (init pL1789))
theorem L1789_seg1 : segOK pL1789 1 1032 (init pL1789) (init pL1789) L1789_cp1.1 L1789_cp1.2 = true := by
  decide +kernel
noncomputable def L1789_cp2 : Nat × Nat := t7val% (fastRun pL1789 1 1460 (init pL1789) (init pL1789))
theorem L1789_seg2 : segOK pL1789 1033 428 L1789_cp1.1 L1789_cp1.2 L1789_cp2.1 L1789_cp2.2 = true := by
  decide +kernel
theorem L1789_fin : (prmOK pL1789 1789 && ptTest pL1789 (runFrom pL1789 (fmask pL1789) (cmask pL1789) (hmask pL1789) 1461 328 (true, L1789_cp2.1, L1789_cp2.2)) 1789 895 false) = true := by
  decide +kernel
theorem L1789_ok : RunOK pL1789 1789 (runFrom pL1789 (fmask pL1789) (cmask pL1789) (hmask pL1789) 1461 328 (true, L1789_cp2.1, L1789_cp2.2)) ∧ ptTest pL1789 (runFrom pL1789 (fmask pL1789) (cmask pL1789) (hmask pL1789) 1461 328 (true, L1789_cp2.1, L1789_cp2.2)) 1789 895 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1789_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1789_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1789_fin) true) L1789_seg1) L1789_seg2) (by decide) rfl L1789_fin ptTest_fst
noncomputable def H1789_cp1 : Nat × Nat := t7val% (fastRun pH1789 1 1032 (init pH1789) (init pH1789))
theorem H1789_seg1 : segOK pH1789 1 1032 (init pH1789) (init pH1789) H1789_cp1.1 H1789_cp1.2 = true := by
  decide +kernel
noncomputable def H1789_cp2 : Nat × Nat := t7val% (fastRun pH1789 1 1460 (init pH1789) (init pH1789))
theorem H1789_seg2 : segOK pH1789 1033 428 H1789_cp1.1 H1789_cp1.2 H1789_cp2.1 H1789_cp2.2 = true := by
  decide +kernel
theorem H1789_fin : (prmOK pH1789 1789 && ptTest pH1789 (runFrom pH1789 (fmask pH1789) (cmask pH1789) (hmask pH1789) 1461 328 (true, H1789_cp2.1, H1789_cp2.2)) 1789 895 true) = true := by
  decide +kernel
theorem H1789_ok : RunOK pH1789 1789 (runFrom pH1789 (fmask pH1789) (cmask pH1789) (hmask pH1789) 1461 328 (true, H1789_cp2.1, H1789_cp2.2)) ∧ ptTest pH1789 (runFrom pH1789 (fmask pH1789) (cmask pH1789) (hmask pH1789) 1461 328 (true, H1789_cp2.1, H1789_cp2.2)) 1789 895 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1789_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1789_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1789_fin) true) H1789_seg1) H1789_seg2) (by decide) rfl H1789_fin ptTest_fst
noncomputable def I1789_cp1 : Nat × Nat := t7val% (fastRun pI1789 1 1264 (init pI1789) (init pI1789))
theorem I1789_seg1 : segOK pI1789 1 1264 (init pI1789) (init pI1789) I1789_cp1.1 I1789_cp1.2 = true := by
  decide +kernel
theorem I1789_fin : (prmOK pI1789 1789 && intTest pI1789 (runFrom pI1789 (fmask pI1789) (cmask pI1789) (hmask pI1789) 1265 524 (true, I1789_cp1.1, I1789_cp1.2)) 1789 21 false) = true := by
  decide +kernel
theorem I1789_ok : RunOK pI1789 1789 (runFrom pI1789 (fmask pI1789) (cmask pI1789) (hmask pI1789) 1265 524 (true, I1789_cp1.1, I1789_cp1.2)) ∧ intTest pI1789 (runFrom pI1789 (fmask pI1789) (cmask pI1789) (hmask pI1789) 1265 524 (true, I1789_cp1.1, I1789_cp1.2)) 1789 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1789_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1789_fin) true) I1789_seg1) (by decide) rfl I1789_fin intTest_fst
theorem link1789 : linkOK pL1789 pH1789 pI1789 = true := by decide +kernel
theorem cvx1789 : ConvexBetweenHumps 1789 :=
  cvx_of L1789_ok H1789_ok I1789_ok link1789 (by decide)

/-! ### `N = 1790` -/

def pL1790 : Prm := ⟨80, 37, 40, 1792, 11, 18446744073709551616, 107713102801418348, 107713102801418348⟩
def pH1790 : Prm := ⟨80, 37, 40, 1792, 11, 18446744073709551616, 107714202313046124, 107714202313046124⟩
def pI1790 : Prm := ⟨67, 34, 30, 1792, 11, 18446744073709551616, 107713102801418348, 107714202313046124⟩
noncomputable def L1790_cp1 : Nat × Nat := t7val% (fastRun pL1790 1 1032 (init pL1790) (init pL1790))
theorem L1790_seg1 : segOK pL1790 1 1032 (init pL1790) (init pL1790) L1790_cp1.1 L1790_cp1.2 = true := by
  decide +kernel
noncomputable def L1790_cp2 : Nat × Nat := t7val% (fastRun pL1790 1 1461 (init pL1790) (init pL1790))
theorem L1790_seg2 : segOK pL1790 1033 429 L1790_cp1.1 L1790_cp1.2 L1790_cp2.1 L1790_cp2.2 = true := by
  decide +kernel
theorem L1790_fin : (prmOK pL1790 1790 && ptTest pL1790 (runFrom pL1790 (fmask pL1790) (cmask pL1790) (hmask pL1790) 1462 328 (true, L1790_cp2.1, L1790_cp2.2)) 1790 895 false) = true := by
  decide +kernel
theorem L1790_ok : RunOK pL1790 1790 (runFrom pL1790 (fmask pL1790) (cmask pL1790) (hmask pL1790) 1462 328 (true, L1790_cp2.1, L1790_cp2.2)) ∧ ptTest pL1790 (runFrom pL1790 (fmask pL1790) (cmask pL1790) (hmask pL1790) 1462 328 (true, L1790_cp2.1, L1790_cp2.2)) 1790 895 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1790_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1790_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1790_fin) true) L1790_seg1) L1790_seg2) (by decide) rfl L1790_fin ptTest_fst
noncomputable def H1790_cp1 : Nat × Nat := t7val% (fastRun pH1790 1 1032 (init pH1790) (init pH1790))
theorem H1790_seg1 : segOK pH1790 1 1032 (init pH1790) (init pH1790) H1790_cp1.1 H1790_cp1.2 = true := by
  decide +kernel
noncomputable def H1790_cp2 : Nat × Nat := t7val% (fastRun pH1790 1 1461 (init pH1790) (init pH1790))
theorem H1790_seg2 : segOK pH1790 1033 429 H1790_cp1.1 H1790_cp1.2 H1790_cp2.1 H1790_cp2.2 = true := by
  decide +kernel
theorem H1790_fin : (prmOK pH1790 1790 && ptTest pH1790 (runFrom pH1790 (fmask pH1790) (cmask pH1790) (hmask pH1790) 1462 328 (true, H1790_cp2.1, H1790_cp2.2)) 1790 895 true) = true := by
  decide +kernel
theorem H1790_ok : RunOK pH1790 1790 (runFrom pH1790 (fmask pH1790) (cmask pH1790) (hmask pH1790) 1462 328 (true, H1790_cp2.1, H1790_cp2.2)) ∧ ptTest pH1790 (runFrom pH1790 (fmask pH1790) (cmask pH1790) (hmask pH1790) 1462 328 (true, H1790_cp2.1, H1790_cp2.2)) 1790 895 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1790_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1790_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1790_fin) true) H1790_seg1) H1790_seg2) (by decide) rfl H1790_fin ptTest_fst
noncomputable def I1790_cp1 : Nat × Nat := t7val% (fastRun pI1790 1 1265 (init pI1790) (init pI1790))
theorem I1790_seg1 : segOK pI1790 1 1265 (init pI1790) (init pI1790) I1790_cp1.1 I1790_cp1.2 = true := by
  decide +kernel
theorem I1790_fin : (prmOK pI1790 1790 && intTest pI1790 (runFrom pI1790 (fmask pI1790) (cmask pI1790) (hmask pI1790) 1266 524 (true, I1790_cp1.1, I1790_cp1.2)) 1790 21 true) = true := by
  decide +kernel
theorem I1790_ok : RunOK pI1790 1790 (runFrom pI1790 (fmask pI1790) (cmask pI1790) (hmask pI1790) 1266 524 (true, I1790_cp1.1, I1790_cp1.2)) ∧ intTest pI1790 (runFrom pI1790 (fmask pI1790) (cmask pI1790) (hmask pI1790) 1266 524 (true, I1790_cp1.1, I1790_cp1.2)) 1790 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1790_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1790_fin) true) I1790_seg1) (by decide) rfl I1790_fin intTest_fst
theorem link1790 : linkOK pL1790 pH1790 pI1790 = true := by decide +kernel
theorem cvx1790 : ConvexBetweenHumps 1790 :=
  cvx_of L1790_ok H1790_ok I1790_ok link1790 (by decide)
theorem cenlink1790 : cenLinkOK pI1790 1790 = true := by decide +kernel
theorem cen1790 : CenterUniqueMin 1790 ∧ DipHyp 1790 ∧ OnePointHyps 1790 :=
  cen_of L1790_ok H1790_ok I1790_ok link1790 cenlink1790

/-! ### `N = 1791` -/

def pL1791 : Prm := ⟨80, 37, 40, 1793, 11, 18446744073709551616, 107663795309626991, 107663795309626991⟩
def pH1791 : Prm := ⟨80, 37, 40, 1793, 11, 18446744073709551616, 107664894821254767, 107664894821254767⟩
def pI1791 : Prm := ⟨67, 34, 30, 1793, 11, 18446744073709551616, 107663795309626991, 107664894821254767⟩
noncomputable def L1791_cp1 : Nat × Nat := t7val% (fastRun pL1791 1 1033 (init pL1791) (init pL1791))
theorem L1791_seg1 : segOK pL1791 1 1033 (init pL1791) (init pL1791) L1791_cp1.1 L1791_cp1.2 = true := by
  decide +kernel
noncomputable def L1791_cp2 : Nat × Nat := t7val% (fastRun pL1791 1 1461 (init pL1791) (init pL1791))
theorem L1791_seg2 : segOK pL1791 1034 428 L1791_cp1.1 L1791_cp1.2 L1791_cp2.1 L1791_cp2.2 = true := by
  decide +kernel
theorem L1791_fin : (prmOK pL1791 1791 && ptTest pL1791 (runFrom pL1791 (fmask pL1791) (cmask pL1791) (hmask pL1791) 1462 329 (true, L1791_cp2.1, L1791_cp2.2)) 1791 896 false) = true := by
  decide +kernel
theorem L1791_ok : RunOK pL1791 1791 (runFrom pL1791 (fmask pL1791) (cmask pL1791) (hmask pL1791) 1462 329 (true, L1791_cp2.1, L1791_cp2.2)) ∧ ptTest pL1791 (runFrom pL1791 (fmask pL1791) (cmask pL1791) (hmask pL1791) 1462 329 (true, L1791_cp2.1, L1791_cp2.2)) 1791 896 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1791_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1791_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1791_fin) true) L1791_seg1) L1791_seg2) (by decide) rfl L1791_fin ptTest_fst
noncomputable def H1791_cp1 : Nat × Nat := t7val% (fastRun pH1791 1 1033 (init pH1791) (init pH1791))
theorem H1791_seg1 : segOK pH1791 1 1033 (init pH1791) (init pH1791) H1791_cp1.1 H1791_cp1.2 = true := by
  decide +kernel
noncomputable def H1791_cp2 : Nat × Nat := t7val% (fastRun pH1791 1 1461 (init pH1791) (init pH1791))
theorem H1791_seg2 : segOK pH1791 1034 428 H1791_cp1.1 H1791_cp1.2 H1791_cp2.1 H1791_cp2.2 = true := by
  decide +kernel
theorem H1791_fin : (prmOK pH1791 1791 && ptTest pH1791 (runFrom pH1791 (fmask pH1791) (cmask pH1791) (hmask pH1791) 1462 329 (true, H1791_cp2.1, H1791_cp2.2)) 1791 896 true) = true := by
  decide +kernel
theorem H1791_ok : RunOK pH1791 1791 (runFrom pH1791 (fmask pH1791) (cmask pH1791) (hmask pH1791) 1462 329 (true, H1791_cp2.1, H1791_cp2.2)) ∧ ptTest pH1791 (runFrom pH1791 (fmask pH1791) (cmask pH1791) (hmask pH1791) 1462 329 (true, H1791_cp2.1, H1791_cp2.2)) 1791 896 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1791_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1791_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1791_fin) true) H1791_seg1) H1791_seg2) (by decide) rfl H1791_fin ptTest_fst
noncomputable def I1791_cp1 : Nat × Nat := t7val% (fastRun pI1791 1 1265 (init pI1791) (init pI1791))
theorem I1791_seg1 : segOK pI1791 1 1265 (init pI1791) (init pI1791) I1791_cp1.1 I1791_cp1.2 = true := by
  decide +kernel
theorem I1791_fin : (prmOK pI1791 1791 && intTest pI1791 (runFrom pI1791 (fmask pI1791) (cmask pI1791) (hmask pI1791) 1266 525 (true, I1791_cp1.1, I1791_cp1.2)) 1791 21 false) = true := by
  decide +kernel
theorem I1791_ok : RunOK pI1791 1791 (runFrom pI1791 (fmask pI1791) (cmask pI1791) (hmask pI1791) 1266 525 (true, I1791_cp1.1, I1791_cp1.2)) ∧ intTest pI1791 (runFrom pI1791 (fmask pI1791) (cmask pI1791) (hmask pI1791) 1266 525 (true, I1791_cp1.1, I1791_cp1.2)) 1791 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1791_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1791_fin) true) I1791_seg1) (by decide) rfl I1791_fin intTest_fst
theorem link1791 : linkOK pL1791 pH1791 pI1791 = true := by decide +kernel
theorem cvx1791 : ConvexBetweenHumps 1791 :=
  cvx_of L1791_ok H1791_ok I1791_ok link1791 (by decide)

/-! ### `N = 1792` -/

def pL1792 : Prm := ⟨80, 37, 40, 1794, 11, 18446744073709551616, 107614556320410047, 107614556320410047⟩
def pH1792 : Prm := ⟨80, 37, 40, 1794, 11, 18446744073709551616, 107615655832037823, 107615655832037823⟩
def pI1792 : Prm := ⟨67, 34, 30, 1794, 11, 18446744073709551616, 107614556320410047, 107615655832037823⟩
noncomputable def L1792_cp1 : Nat × Nat := t7val% (fastRun pL1792 1 1034 (init pL1792) (init pL1792))
theorem L1792_seg1 : segOK pL1792 1 1034 (init pL1792) (init pL1792) L1792_cp1.1 L1792_cp1.2 = true := by
  decide +kernel
noncomputable def L1792_cp2 : Nat × Nat := t7val% (fastRun pL1792 1 1462 (init pL1792) (init pL1792))
theorem L1792_seg2 : segOK pL1792 1035 428 L1792_cp1.1 L1792_cp1.2 L1792_cp2.1 L1792_cp2.2 = true := by
  decide +kernel
theorem L1792_fin : (prmOK pL1792 1792 && ptTest pL1792 (runFrom pL1792 (fmask pL1792) (cmask pL1792) (hmask pL1792) 1463 329 (true, L1792_cp2.1, L1792_cp2.2)) 1792 896 false) = true := by
  decide +kernel
theorem L1792_ok : RunOK pL1792 1792 (runFrom pL1792 (fmask pL1792) (cmask pL1792) (hmask pL1792) 1463 329 (true, L1792_cp2.1, L1792_cp2.2)) ∧ ptTest pL1792 (runFrom pL1792 (fmask pL1792) (cmask pL1792) (hmask pL1792) 1463 329 (true, L1792_cp2.1, L1792_cp2.2)) 1792 896 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1792_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1792_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1792_fin) true) L1792_seg1) L1792_seg2) (by decide) rfl L1792_fin ptTest_fst
noncomputable def H1792_cp1 : Nat × Nat := t7val% (fastRun pH1792 1 1034 (init pH1792) (init pH1792))
theorem H1792_seg1 : segOK pH1792 1 1034 (init pH1792) (init pH1792) H1792_cp1.1 H1792_cp1.2 = true := by
  decide +kernel
noncomputable def H1792_cp2 : Nat × Nat := t7val% (fastRun pH1792 1 1462 (init pH1792) (init pH1792))
theorem H1792_seg2 : segOK pH1792 1035 428 H1792_cp1.1 H1792_cp1.2 H1792_cp2.1 H1792_cp2.2 = true := by
  decide +kernel
theorem H1792_fin : (prmOK pH1792 1792 && ptTest pH1792 (runFrom pH1792 (fmask pH1792) (cmask pH1792) (hmask pH1792) 1463 329 (true, H1792_cp2.1, H1792_cp2.2)) 1792 896 true) = true := by
  decide +kernel
theorem H1792_ok : RunOK pH1792 1792 (runFrom pH1792 (fmask pH1792) (cmask pH1792) (hmask pH1792) 1463 329 (true, H1792_cp2.1, H1792_cp2.2)) ∧ ptTest pH1792 (runFrom pH1792 (fmask pH1792) (cmask pH1792) (hmask pH1792) 1463 329 (true, H1792_cp2.1, H1792_cp2.2)) 1792 896 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1792_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1792_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1792_fin) true) H1792_seg1) H1792_seg2) (by decide) rfl H1792_fin ptTest_fst
noncomputable def I1792_cp1 : Nat × Nat := t7val% (fastRun pI1792 1 1266 (init pI1792) (init pI1792))
theorem I1792_seg1 : segOK pI1792 1 1266 (init pI1792) (init pI1792) I1792_cp1.1 I1792_cp1.2 = true := by
  decide +kernel
theorem I1792_fin : (prmOK pI1792 1792 && intTest pI1792 (runFrom pI1792 (fmask pI1792) (cmask pI1792) (hmask pI1792) 1267 525 (true, I1792_cp1.1, I1792_cp1.2)) 1792 21 true) = true := by
  decide +kernel
theorem I1792_ok : RunOK pI1792 1792 (runFrom pI1792 (fmask pI1792) (cmask pI1792) (hmask pI1792) 1267 525 (true, I1792_cp1.1, I1792_cp1.2)) ∧ intTest pI1792 (runFrom pI1792 (fmask pI1792) (cmask pI1792) (hmask pI1792) 1267 525 (true, I1792_cp1.1, I1792_cp1.2)) 1792 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1792_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1792_fin) true) I1792_seg1) (by decide) rfl I1792_fin intTest_fst
theorem link1792 : linkOK pL1792 pH1792 pI1792 = true := by decide +kernel
theorem cvx1792 : ConvexBetweenHumps 1792 :=
  cvx_of L1792_ok H1792_ok I1792_ok link1792 (by decide)
theorem cenlink1792 : cenLinkOK pI1792 1792 = true := by decide +kernel
theorem cen1792 : CenterUniqueMin 1792 ∧ DipHyp 1792 ∧ OnePointHyps 1792 :=
  cen_of L1792_ok H1792_ok I1792_ok link1792 cenlink1792

/-! ### `N = 1793` -/

def pL1793 : Prm := ⟨80, 37, 40, 1795, 11, 18446744073709551616, 107565346710768988, 107565346710768988⟩
def pH1793 : Prm := ⟨80, 37, 40, 1795, 11, 18446744073709551616, 107566446222396764, 107566446222396764⟩
def pI1793 : Prm := ⟨67, 34, 30, 1795, 11, 18446744073709551616, 107565346710768988, 107566446222396764⟩
noncomputable def L1793_cp1 : Nat × Nat := t7val% (fastRun pL1793 1 1034 (init pL1793) (init pL1793))
theorem L1793_seg1 : segOK pL1793 1 1034 (init pL1793) (init pL1793) L1793_cp1.1 L1793_cp1.2 = true := by
  decide +kernel
noncomputable def L1793_cp2 : Nat × Nat := t7val% (fastRun pL1793 1 1463 (init pL1793) (init pL1793))
theorem L1793_seg2 : segOK pL1793 1035 429 L1793_cp1.1 L1793_cp1.2 L1793_cp2.1 L1793_cp2.2 = true := by
  decide +kernel
theorem L1793_fin : (prmOK pL1793 1793 && ptTest pL1793 (runFrom pL1793 (fmask pL1793) (cmask pL1793) (hmask pL1793) 1464 329 (true, L1793_cp2.1, L1793_cp2.2)) 1793 897 false) = true := by
  decide +kernel
theorem L1793_ok : RunOK pL1793 1793 (runFrom pL1793 (fmask pL1793) (cmask pL1793) (hmask pL1793) 1464 329 (true, L1793_cp2.1, L1793_cp2.2)) ∧ ptTest pL1793 (runFrom pL1793 (fmask pL1793) (cmask pL1793) (hmask pL1793) 1464 329 (true, L1793_cp2.1, L1793_cp2.2)) 1793 897 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1793_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1793_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1793_fin) true) L1793_seg1) L1793_seg2) (by decide) rfl L1793_fin ptTest_fst
noncomputable def H1793_cp1 : Nat × Nat := t7val% (fastRun pH1793 1 1034 (init pH1793) (init pH1793))
theorem H1793_seg1 : segOK pH1793 1 1034 (init pH1793) (init pH1793) H1793_cp1.1 H1793_cp1.2 = true := by
  decide +kernel
noncomputable def H1793_cp2 : Nat × Nat := t7val% (fastRun pH1793 1 1463 (init pH1793) (init pH1793))
theorem H1793_seg2 : segOK pH1793 1035 429 H1793_cp1.1 H1793_cp1.2 H1793_cp2.1 H1793_cp2.2 = true := by
  decide +kernel
theorem H1793_fin : (prmOK pH1793 1793 && ptTest pH1793 (runFrom pH1793 (fmask pH1793) (cmask pH1793) (hmask pH1793) 1464 329 (true, H1793_cp2.1, H1793_cp2.2)) 1793 897 true) = true := by
  decide +kernel
theorem H1793_ok : RunOK pH1793 1793 (runFrom pH1793 (fmask pH1793) (cmask pH1793) (hmask pH1793) 1464 329 (true, H1793_cp2.1, H1793_cp2.2)) ∧ ptTest pH1793 (runFrom pH1793 (fmask pH1793) (cmask pH1793) (hmask pH1793) 1464 329 (true, H1793_cp2.1, H1793_cp2.2)) 1793 897 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1793_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1793_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1793_fin) true) H1793_seg1) H1793_seg2) (by decide) rfl H1793_fin ptTest_fst
noncomputable def I1793_cp1 : Nat × Nat := t7val% (fastRun pI1793 1 1034 (init pI1793) (init pI1793))
theorem I1793_seg1 : segOK pI1793 1 1034 (init pI1793) (init pI1793) I1793_cp1.1 I1793_cp1.2 = true := by
  decide +kernel
noncomputable def I1793_cp2 : Nat × Nat := t7val% (fastRun pI1793 1 1463 (init pI1793) (init pI1793))
theorem I1793_seg2 : segOK pI1793 1035 429 I1793_cp1.1 I1793_cp1.2 I1793_cp2.1 I1793_cp2.2 = true := by
  decide +kernel
theorem I1793_fin : (prmOK pI1793 1793 && intTest pI1793 (runFrom pI1793 (fmask pI1793) (cmask pI1793) (hmask pI1793) 1464 329 (true, I1793_cp2.1, I1793_cp2.2)) 1793 21 false) = true := by
  decide +kernel
theorem I1793_ok : RunOK pI1793 1793 (runFrom pI1793 (fmask pI1793) (cmask pI1793) (hmask pI1793) 1464 329 (true, I1793_cp2.1, I1793_cp2.2)) ∧ intTest pI1793 (runFrom pI1793 (fmask pI1793) (cmask pI1793) (hmask pI1793) 1464 329 (true, I1793_cp2.1, I1793_cp2.2)) 1793 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1793_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1793_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1793_fin) true) I1793_seg1) I1793_seg2) (by decide) rfl I1793_fin intTest_fst
theorem link1793 : linkOK pL1793 pH1793 pI1793 = true := by decide +kernel
theorem cvx1793 : ConvexBetweenHumps 1793 :=
  cvx_of L1793_ok H1793_ok I1793_ok link1793 (by decide)

/-! ### `N = 1794` -/

def pL1794 : Prm := ⟨80, 37, 40, 1796, 11, 18446744073709551616, 107516205387211355, 107516205387211355⟩
def pH1794 : Prm := ⟨80, 37, 40, 1796, 11, 18446744073709551616, 107517304898839131, 107517304898839131⟩
def pI1794 : Prm := ⟨67, 34, 30, 1796, 11, 18446744073709551616, 107516205387211355, 107517304898839131⟩
noncomputable def L1794_cp1 : Nat × Nat := t7val% (fastRun pL1794 1 1035 (init pL1794) (init pL1794))
theorem L1794_seg1 : segOK pL1794 1 1035 (init pL1794) (init pL1794) L1794_cp1.1 L1794_cp1.2 = true := by
  decide +kernel
noncomputable def L1794_cp2 : Nat × Nat := t7val% (fastRun pL1794 1 1464 (init pL1794) (init pL1794))
theorem L1794_seg2 : segOK pL1794 1036 429 L1794_cp1.1 L1794_cp1.2 L1794_cp2.1 L1794_cp2.2 = true := by
  decide +kernel
theorem L1794_fin : (prmOK pL1794 1794 && ptTest pL1794 (runFrom pL1794 (fmask pL1794) (cmask pL1794) (hmask pL1794) 1465 329 (true, L1794_cp2.1, L1794_cp2.2)) 1794 897 false) = true := by
  decide +kernel
theorem L1794_ok : RunOK pL1794 1794 (runFrom pL1794 (fmask pL1794) (cmask pL1794) (hmask pL1794) 1465 329 (true, L1794_cp2.1, L1794_cp2.2)) ∧ ptTest pL1794 (runFrom pL1794 (fmask pL1794) (cmask pL1794) (hmask pL1794) 1465 329 (true, L1794_cp2.1, L1794_cp2.2)) 1794 897 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1794_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1794_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1794_fin) true) L1794_seg1) L1794_seg2) (by decide) rfl L1794_fin ptTest_fst
noncomputable def H1794_cp1 : Nat × Nat := t7val% (fastRun pH1794 1 1035 (init pH1794) (init pH1794))
theorem H1794_seg1 : segOK pH1794 1 1035 (init pH1794) (init pH1794) H1794_cp1.1 H1794_cp1.2 = true := by
  decide +kernel
noncomputable def H1794_cp2 : Nat × Nat := t7val% (fastRun pH1794 1 1464 (init pH1794) (init pH1794))
theorem H1794_seg2 : segOK pH1794 1036 429 H1794_cp1.1 H1794_cp1.2 H1794_cp2.1 H1794_cp2.2 = true := by
  decide +kernel
theorem H1794_fin : (prmOK pH1794 1794 && ptTest pH1794 (runFrom pH1794 (fmask pH1794) (cmask pH1794) (hmask pH1794) 1465 329 (true, H1794_cp2.1, H1794_cp2.2)) 1794 897 true) = true := by
  decide +kernel
theorem H1794_ok : RunOK pH1794 1794 (runFrom pH1794 (fmask pH1794) (cmask pH1794) (hmask pH1794) 1465 329 (true, H1794_cp2.1, H1794_cp2.2)) ∧ ptTest pH1794 (runFrom pH1794 (fmask pH1794) (cmask pH1794) (hmask pH1794) 1465 329 (true, H1794_cp2.1, H1794_cp2.2)) 1794 897 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1794_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1794_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1794_fin) true) H1794_seg1) H1794_seg2) (by decide) rfl H1794_fin ptTest_fst
noncomputable def I1794_cp1 : Nat × Nat := t7val% (fastRun pI1794 1 1035 (init pI1794) (init pI1794))
theorem I1794_seg1 : segOK pI1794 1 1035 (init pI1794) (init pI1794) I1794_cp1.1 I1794_cp1.2 = true := by
  decide +kernel
noncomputable def I1794_cp2 : Nat × Nat := t7val% (fastRun pI1794 1 1464 (init pI1794) (init pI1794))
theorem I1794_seg2 : segOK pI1794 1036 429 I1794_cp1.1 I1794_cp1.2 I1794_cp2.1 I1794_cp2.2 = true := by
  decide +kernel
theorem I1794_fin : (prmOK pI1794 1794 && intTest pI1794 (runFrom pI1794 (fmask pI1794) (cmask pI1794) (hmask pI1794) 1465 329 (true, I1794_cp2.1, I1794_cp2.2)) 1794 21 true) = true := by
  decide +kernel
theorem I1794_ok : RunOK pI1794 1794 (runFrom pI1794 (fmask pI1794) (cmask pI1794) (hmask pI1794) 1465 329 (true, I1794_cp2.1, I1794_cp2.2)) ∧ intTest pI1794 (runFrom pI1794 (fmask pI1794) (cmask pI1794) (hmask pI1794) 1465 329 (true, I1794_cp2.1, I1794_cp2.2)) 1794 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1794_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1794_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1794_fin) true) I1794_seg1) I1794_seg2) (by decide) rfl I1794_fin intTest_fst
theorem link1794 : linkOK pL1794 pH1794 pI1794 = true := by decide +kernel
theorem cvx1794 : ConvexBetweenHumps 1794 :=
  cvx_of L1794_ok H1794_ok I1794_ok link1794 (by decide)
theorem cenlink1794 : cenLinkOK pI1794 1794 = true := by decide +kernel
theorem cen1794 : CenterUniqueMin 1794 ∧ DipHyp 1794 ∧ OnePointHyps 1794 :=
  cen_of L1794_ok H1794_ok I1794_ok link1794 cenlink1794

/-! ### `N = 1795` -/

def pL1795 : Prm := ⟨80, 37, 40, 1797, 11, 18446744073709551616, 107467093359536726, 107467093359536726⟩
def pH1795 : Prm := ⟨80, 37, 40, 1797, 11, 18446744073709551616, 107468192871164502, 107468192871164502⟩
def pI1795 : Prm := ⟨67, 34, 30, 1797, 11, 18446744073709551616, 107467093359536726, 107468192871164502⟩
noncomputable def L1795_cp1 : Nat × Nat := t7val% (fastRun pL1795 1 1035 (init pL1795) (init pL1795))
theorem L1795_seg1 : segOK pL1795 1 1035 (init pL1795) (init pL1795) L1795_cp1.1 L1795_cp1.2 = true := by
  decide +kernel
noncomputable def L1795_cp2 : Nat × Nat := t7val% (fastRun pL1795 1 1465 (init pL1795) (init pL1795))
theorem L1795_seg2 : segOK pL1795 1036 430 L1795_cp1.1 L1795_cp1.2 L1795_cp2.1 L1795_cp2.2 = true := by
  decide +kernel
theorem L1795_fin : (prmOK pL1795 1795 && ptTest pL1795 (runFrom pL1795 (fmask pL1795) (cmask pL1795) (hmask pL1795) 1466 329 (true, L1795_cp2.1, L1795_cp2.2)) 1795 898 false) = true := by
  decide +kernel
theorem L1795_ok : RunOK pL1795 1795 (runFrom pL1795 (fmask pL1795) (cmask pL1795) (hmask pL1795) 1466 329 (true, L1795_cp2.1, L1795_cp2.2)) ∧ ptTest pL1795 (runFrom pL1795 (fmask pL1795) (cmask pL1795) (hmask pL1795) 1466 329 (true, L1795_cp2.1, L1795_cp2.2)) 1795 898 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1795_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1795_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1795_fin) true) L1795_seg1) L1795_seg2) (by decide) rfl L1795_fin ptTest_fst
noncomputable def H1795_cp1 : Nat × Nat := t7val% (fastRun pH1795 1 1035 (init pH1795) (init pH1795))
theorem H1795_seg1 : segOK pH1795 1 1035 (init pH1795) (init pH1795) H1795_cp1.1 H1795_cp1.2 = true := by
  decide +kernel
noncomputable def H1795_cp2 : Nat × Nat := t7val% (fastRun pH1795 1 1465 (init pH1795) (init pH1795))
theorem H1795_seg2 : segOK pH1795 1036 430 H1795_cp1.1 H1795_cp1.2 H1795_cp2.1 H1795_cp2.2 = true := by
  decide +kernel
theorem H1795_fin : (prmOK pH1795 1795 && ptTest pH1795 (runFrom pH1795 (fmask pH1795) (cmask pH1795) (hmask pH1795) 1466 329 (true, H1795_cp2.1, H1795_cp2.2)) 1795 898 true) = true := by
  decide +kernel
theorem H1795_ok : RunOK pH1795 1795 (runFrom pH1795 (fmask pH1795) (cmask pH1795) (hmask pH1795) 1466 329 (true, H1795_cp2.1, H1795_cp2.2)) ∧ ptTest pH1795 (runFrom pH1795 (fmask pH1795) (cmask pH1795) (hmask pH1795) 1466 329 (true, H1795_cp2.1, H1795_cp2.2)) 1795 898 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1795_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1795_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1795_fin) true) H1795_seg1) H1795_seg2) (by decide) rfl H1795_fin ptTest_fst
noncomputable def I1795_cp1 : Nat × Nat := t7val% (fastRun pI1795 1 1035 (init pI1795) (init pI1795))
theorem I1795_seg1 : segOK pI1795 1 1035 (init pI1795) (init pI1795) I1795_cp1.1 I1795_cp1.2 = true := by
  decide +kernel
noncomputable def I1795_cp2 : Nat × Nat := t7val% (fastRun pI1795 1 1465 (init pI1795) (init pI1795))
theorem I1795_seg2 : segOK pI1795 1036 430 I1795_cp1.1 I1795_cp1.2 I1795_cp2.1 I1795_cp2.2 = true := by
  decide +kernel
theorem I1795_fin : (prmOK pI1795 1795 && intTest pI1795 (runFrom pI1795 (fmask pI1795) (cmask pI1795) (hmask pI1795) 1466 329 (true, I1795_cp2.1, I1795_cp2.2)) 1795 21 false) = true := by
  decide +kernel
theorem I1795_ok : RunOK pI1795 1795 (runFrom pI1795 (fmask pI1795) (cmask pI1795) (hmask pI1795) 1466 329 (true, I1795_cp2.1, I1795_cp2.2)) ∧ intTest pI1795 (runFrom pI1795 (fmask pI1795) (cmask pI1795) (hmask pI1795) 1466 329 (true, I1795_cp2.1, I1795_cp2.2)) 1795 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1795_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1795_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1795_fin) true) I1795_seg1) I1795_seg2) (by decide) rfl I1795_fin intTest_fst
theorem link1795 : linkOK pL1795 pH1795 pI1795 = true := by decide +kernel
theorem cvx1795 : ConvexBetweenHumps 1795 :=
  cvx_of L1795_ok H1795_ok I1795_ok link1795 (by decide)

/-! ### The range -/

theorem cvx_1784_1795 {N : ℕ} (h1 : 1784 ≤ N) (h2 : N ≤ 1795) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1789
  · by_cases h4 : N ≤ 1786
    · by_cases h6 : N ≤ 1784
      · obtain rfl : N = 1784 := by omega
        exact cvx1784
      · by_cases h8 : N ≤ 1785
        · obtain rfl : N = 1785 := by omega
          exact cvx1785
        · obtain rfl : N = 1786 := by omega
          exact cvx1786
    · by_cases h6 : N ≤ 1787
      · obtain rfl : N = 1787 := by omega
        exact cvx1787
      · by_cases h8 : N ≤ 1788
        · obtain rfl : N = 1788 := by omega
          exact cvx1788
        · obtain rfl : N = 1789 := by omega
          exact cvx1789
  · by_cases h4 : N ≤ 1792
    · by_cases h6 : N ≤ 1790
      · obtain rfl : N = 1790 := by omega
        exact cvx1790
      · by_cases h8 : N ≤ 1791
        · obtain rfl : N = 1791 := by omega
          exact cvx1791
        · obtain rfl : N = 1792 := by omega
          exact cvx1792
    · by_cases h6 : N ≤ 1793
      · obtain rfl : N = 1793 := by omega
        exact cvx1793
      · by_cases h8 : N ≤ 1794
        · obtain rfl : N = 1794 := by omega
          exact cvx1794
        · obtain rfl : N = 1795 := by omega
          exact cvx1795

theorem cen_1784_1795 {N : ℕ} (h1 : 1784 ≤ N) (h2 : N ≤ 1795) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1788
  · by_cases h4 : N ≤ 1784
    · obtain rfl : N = 1784 := by omega
      exact cen1784
    · by_cases h6 : N ≤ 1786
      · obtain rfl : N = 1786 := by omega
        exact cen1786
      · obtain rfl : N = 1788 := by omega
        exact cen1788
  · by_cases h4 : N ≤ 1790
    · obtain rfl : N = 1790 := by omega
      exact cen1790
    · by_cases h6 : N ≤ 1792
      · obtain rfl : N = 1792 := by omega
        exact cen1792
      · obtain rfl : N = 1794 := by omega
        exact cen1794

end Kagey131.PaperD.T7
