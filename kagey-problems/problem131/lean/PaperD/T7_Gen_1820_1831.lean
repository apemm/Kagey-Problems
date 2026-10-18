import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1820, …, 1831` (generated)

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

/-! ### `N = 1820` -/

def pL1820 : Prm := ⟨80, 37, 40, 1822, 11, 18446744073709551616, 106255168720050203, 106255168720050203⟩
def pH1820 : Prm := ⟨80, 37, 40, 1822, 11, 18446744073709551616, 106256268231677979, 106256268231677979⟩
def pI1820 : Prm := ⟨68, 34, 31, 1822, 11, 18446744073709551616, 106255168720050203, 106256268231677979⟩
noncomputable def L1820_cp1 : Nat × Nat := t7val% (fastRun pL1820 1 1050 (init pL1820) (init pL1820))
theorem L1820_seg1 : segOK pL1820 1 1050 (init pL1820) (init pL1820) L1820_cp1.1 L1820_cp1.2 = true := by
  decide +kernel
noncomputable def L1820_cp2 : Nat × Nat := t7val% (fastRun pL1820 1 1485 (init pL1820) (init pL1820))
theorem L1820_seg2 : segOK pL1820 1051 435 L1820_cp1.1 L1820_cp1.2 L1820_cp2.1 L1820_cp2.2 = true := by
  decide +kernel
theorem L1820_fin : (prmOK pL1820 1820 && ptTest pL1820 (runFrom pL1820 (fmask pL1820) (cmask pL1820) (hmask pL1820) 1486 334 (true, L1820_cp2.1, L1820_cp2.2)) 1820 910 false) = true := by
  decide +kernel
theorem L1820_ok : RunOK pL1820 1820 (runFrom pL1820 (fmask pL1820) (cmask pL1820) (hmask pL1820) 1486 334 (true, L1820_cp2.1, L1820_cp2.2)) ∧ ptTest pL1820 (runFrom pL1820 (fmask pL1820) (cmask pL1820) (hmask pL1820) 1486 334 (true, L1820_cp2.1, L1820_cp2.2)) 1820 910 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1820_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1820_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1820_fin) true) L1820_seg1) L1820_seg2) (by decide) rfl L1820_fin ptTest_fst
noncomputable def H1820_cp1 : Nat × Nat := t7val% (fastRun pH1820 1 1050 (init pH1820) (init pH1820))
theorem H1820_seg1 : segOK pH1820 1 1050 (init pH1820) (init pH1820) H1820_cp1.1 H1820_cp1.2 = true := by
  decide +kernel
noncomputable def H1820_cp2 : Nat × Nat := t7val% (fastRun pH1820 1 1485 (init pH1820) (init pH1820))
theorem H1820_seg2 : segOK pH1820 1051 435 H1820_cp1.1 H1820_cp1.2 H1820_cp2.1 H1820_cp2.2 = true := by
  decide +kernel
theorem H1820_fin : (prmOK pH1820 1820 && ptTest pH1820 (runFrom pH1820 (fmask pH1820) (cmask pH1820) (hmask pH1820) 1486 334 (true, H1820_cp2.1, H1820_cp2.2)) 1820 910 true) = true := by
  decide +kernel
theorem H1820_ok : RunOK pH1820 1820 (runFrom pH1820 (fmask pH1820) (cmask pH1820) (hmask pH1820) 1486 334 (true, H1820_cp2.1, H1820_cp2.2)) ∧ ptTest pH1820 (runFrom pH1820 (fmask pH1820) (cmask pH1820) (hmask pH1820) 1486 334 (true, H1820_cp2.1, H1820_cp2.2)) 1820 910 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1820_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1820_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1820_fin) true) H1820_seg1) H1820_seg2) (by decide) rfl H1820_fin ptTest_fst
noncomputable def I1820_cp1 : Nat × Nat := t7val% (fastRun pI1820 1 1050 (init pI1820) (init pI1820))
theorem I1820_seg1 : segOK pI1820 1 1050 (init pI1820) (init pI1820) I1820_cp1.1 I1820_cp1.2 = true := by
  decide +kernel
noncomputable def I1820_cp2 : Nat × Nat := t7val% (fastRun pI1820 1 1485 (init pI1820) (init pI1820))
theorem I1820_seg2 : segOK pI1820 1051 435 I1820_cp1.1 I1820_cp1.2 I1820_cp2.1 I1820_cp2.2 = true := by
  decide +kernel
theorem I1820_fin : (prmOK pI1820 1820 && intTest pI1820 (runFrom pI1820 (fmask pI1820) (cmask pI1820) (hmask pI1820) 1486 334 (true, I1820_cp2.1, I1820_cp2.2)) 1820 21 true) = true := by
  decide +kernel
theorem I1820_ok : RunOK pI1820 1820 (runFrom pI1820 (fmask pI1820) (cmask pI1820) (hmask pI1820) 1486 334 (true, I1820_cp2.1, I1820_cp2.2)) ∧ intTest pI1820 (runFrom pI1820 (fmask pI1820) (cmask pI1820) (hmask pI1820) 1486 334 (true, I1820_cp2.1, I1820_cp2.2)) 1820 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1820_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1820_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1820_fin) true) I1820_seg1) I1820_seg2) (by decide) rfl I1820_fin intTest_fst
theorem link1820 : linkOK pL1820 pH1820 pI1820 = true := by decide +kernel
theorem cvx1820 : ConvexBetweenHumps 1820 :=
  cvx_of L1820_ok H1820_ok I1820_ok link1820 (by decide)
theorem cenlink1820 : cenLinkOK pI1820 1820 = true := by decide +kernel
theorem cen1820 : CenterUniqueMin 1820 ∧ DipHyp 1820 ∧ OnePointHyps 1820 :=
  cen_of L1820_ok H1820_ok I1820_ok link1820 cenlink1820

/-! ### `N = 1821` -/

def pL1821 : Prm := ⟨80, 37, 40, 1823, 11, 18446744073709551616, 106207298499848543, 106207298499848543⟩
def pH1821 : Prm := ⟨80, 37, 40, 1823, 11, 18446744073709551616, 106208398011476319, 106208398011476319⟩
def pI1821 : Prm := ⟨68, 34, 31, 1823, 11, 18446744073709551616, 106207298499848543, 106208398011476319⟩
noncomputable def L1821_cp1 : Nat × Nat := t7val% (fastRun pL1821 1 1050 (init pL1821) (init pL1821))
theorem L1821_seg1 : segOK pL1821 1 1050 (init pL1821) (init pL1821) L1821_cp1.1 L1821_cp1.2 = true := by
  decide +kernel
noncomputable def L1821_cp2 : Nat × Nat := t7val% (fastRun pL1821 1 1486 (init pL1821) (init pL1821))
theorem L1821_seg2 : segOK pL1821 1051 436 L1821_cp1.1 L1821_cp1.2 L1821_cp2.1 L1821_cp2.2 = true := by
  decide +kernel
theorem L1821_fin : (prmOK pL1821 1821 && ptTest pL1821 (runFrom pL1821 (fmask pL1821) (cmask pL1821) (hmask pL1821) 1487 334 (true, L1821_cp2.1, L1821_cp2.2)) 1821 911 false) = true := by
  decide +kernel
theorem L1821_ok : RunOK pL1821 1821 (runFrom pL1821 (fmask pL1821) (cmask pL1821) (hmask pL1821) 1487 334 (true, L1821_cp2.1, L1821_cp2.2)) ∧ ptTest pL1821 (runFrom pL1821 (fmask pL1821) (cmask pL1821) (hmask pL1821) 1487 334 (true, L1821_cp2.1, L1821_cp2.2)) 1821 911 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1821_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1821_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1821_fin) true) L1821_seg1) L1821_seg2) (by decide) rfl L1821_fin ptTest_fst
noncomputable def H1821_cp1 : Nat × Nat := t7val% (fastRun pH1821 1 1050 (init pH1821) (init pH1821))
theorem H1821_seg1 : segOK pH1821 1 1050 (init pH1821) (init pH1821) H1821_cp1.1 H1821_cp1.2 = true := by
  decide +kernel
noncomputable def H1821_cp2 : Nat × Nat := t7val% (fastRun pH1821 1 1486 (init pH1821) (init pH1821))
theorem H1821_seg2 : segOK pH1821 1051 436 H1821_cp1.1 H1821_cp1.2 H1821_cp2.1 H1821_cp2.2 = true := by
  decide +kernel
theorem H1821_fin : (prmOK pH1821 1821 && ptTest pH1821 (runFrom pH1821 (fmask pH1821) (cmask pH1821) (hmask pH1821) 1487 334 (true, H1821_cp2.1, H1821_cp2.2)) 1821 911 true) = true := by
  decide +kernel
theorem H1821_ok : RunOK pH1821 1821 (runFrom pH1821 (fmask pH1821) (cmask pH1821) (hmask pH1821) 1487 334 (true, H1821_cp2.1, H1821_cp2.2)) ∧ ptTest pH1821 (runFrom pH1821 (fmask pH1821) (cmask pH1821) (hmask pH1821) 1487 334 (true, H1821_cp2.1, H1821_cp2.2)) 1821 911 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1821_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1821_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1821_fin) true) H1821_seg1) H1821_seg2) (by decide) rfl H1821_fin ptTest_fst
noncomputable def I1821_cp1 : Nat × Nat := t7val% (fastRun pI1821 1 1050 (init pI1821) (init pI1821))
theorem I1821_seg1 : segOK pI1821 1 1050 (init pI1821) (init pI1821) I1821_cp1.1 I1821_cp1.2 = true := by
  decide +kernel
noncomputable def I1821_cp2 : Nat × Nat := t7val% (fastRun pI1821 1 1486 (init pI1821) (init pI1821))
theorem I1821_seg2 : segOK pI1821 1051 436 I1821_cp1.1 I1821_cp1.2 I1821_cp2.1 I1821_cp2.2 = true := by
  decide +kernel
theorem I1821_fin : (prmOK pI1821 1821 && intTest pI1821 (runFrom pI1821 (fmask pI1821) (cmask pI1821) (hmask pI1821) 1487 334 (true, I1821_cp2.1, I1821_cp2.2)) 1821 21 false) = true := by
  decide +kernel
theorem I1821_ok : RunOK pI1821 1821 (runFrom pI1821 (fmask pI1821) (cmask pI1821) (hmask pI1821) 1487 334 (true, I1821_cp2.1, I1821_cp2.2)) ∧ intTest pI1821 (runFrom pI1821 (fmask pI1821) (cmask pI1821) (hmask pI1821) 1487 334 (true, I1821_cp2.1, I1821_cp2.2)) 1821 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1821_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1821_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1821_fin) true) I1821_seg1) I1821_seg2) (by decide) rfl I1821_fin intTest_fst
theorem link1821 : linkOK pL1821 pH1821 pI1821 = true := by decide +kernel
theorem cvx1821 : ConvexBetweenHumps 1821 :=
  cvx_of L1821_ok H1821_ok I1821_ok link1821 (by decide)

/-! ### `N = 1822` -/

def pL1822 : Prm := ⟨80, 37, 40, 1824, 11, 18446744073709551616, 106159493629764967, 106159493629764967⟩
def pH1822 : Prm := ⟨80, 37, 40, 1824, 11, 18446744073709551616, 106160593141392743, 106160593141392743⟩
def pI1822 : Prm := ⟨68, 34, 31, 1824, 11, 18446744073709551616, 106159493629764967, 106160593141392743⟩
noncomputable def L1822_cp1 : Nat × Nat := t7val% (fastRun pL1822 1 1051 (init pL1822) (init pL1822))
theorem L1822_seg1 : segOK pL1822 1 1051 (init pL1822) (init pL1822) L1822_cp1.1 L1822_cp1.2 = true := by
  decide +kernel
noncomputable def L1822_cp2 : Nat × Nat := t7val% (fastRun pL1822 1 1487 (init pL1822) (init pL1822))
theorem L1822_seg2 : segOK pL1822 1052 436 L1822_cp1.1 L1822_cp1.2 L1822_cp2.1 L1822_cp2.2 = true := by
  decide +kernel
theorem L1822_fin : (prmOK pL1822 1822 && ptTest pL1822 (runFrom pL1822 (fmask pL1822) (cmask pL1822) (hmask pL1822) 1488 334 (true, L1822_cp2.1, L1822_cp2.2)) 1822 911 false) = true := by
  decide +kernel
theorem L1822_ok : RunOK pL1822 1822 (runFrom pL1822 (fmask pL1822) (cmask pL1822) (hmask pL1822) 1488 334 (true, L1822_cp2.1, L1822_cp2.2)) ∧ ptTest pL1822 (runFrom pL1822 (fmask pL1822) (cmask pL1822) (hmask pL1822) 1488 334 (true, L1822_cp2.1, L1822_cp2.2)) 1822 911 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1822_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1822_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1822_fin) true) L1822_seg1) L1822_seg2) (by decide) rfl L1822_fin ptTest_fst
noncomputable def H1822_cp1 : Nat × Nat := t7val% (fastRun pH1822 1 1051 (init pH1822) (init pH1822))
theorem H1822_seg1 : segOK pH1822 1 1051 (init pH1822) (init pH1822) H1822_cp1.1 H1822_cp1.2 = true := by
  decide +kernel
noncomputable def H1822_cp2 : Nat × Nat := t7val% (fastRun pH1822 1 1487 (init pH1822) (init pH1822))
theorem H1822_seg2 : segOK pH1822 1052 436 H1822_cp1.1 H1822_cp1.2 H1822_cp2.1 H1822_cp2.2 = true := by
  decide +kernel
theorem H1822_fin : (prmOK pH1822 1822 && ptTest pH1822 (runFrom pH1822 (fmask pH1822) (cmask pH1822) (hmask pH1822) 1488 334 (true, H1822_cp2.1, H1822_cp2.2)) 1822 911 true) = true := by
  decide +kernel
theorem H1822_ok : RunOK pH1822 1822 (runFrom pH1822 (fmask pH1822) (cmask pH1822) (hmask pH1822) 1488 334 (true, H1822_cp2.1, H1822_cp2.2)) ∧ ptTest pH1822 (runFrom pH1822 (fmask pH1822) (cmask pH1822) (hmask pH1822) 1488 334 (true, H1822_cp2.1, H1822_cp2.2)) 1822 911 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1822_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1822_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1822_fin) true) H1822_seg1) H1822_seg2) (by decide) rfl H1822_fin ptTest_fst
noncomputable def I1822_cp1 : Nat × Nat := t7val% (fastRun pI1822 1 1051 (init pI1822) (init pI1822))
theorem I1822_seg1 : segOK pI1822 1 1051 (init pI1822) (init pI1822) I1822_cp1.1 I1822_cp1.2 = true := by
  decide +kernel
noncomputable def I1822_cp2 : Nat × Nat := t7val% (fastRun pI1822 1 1487 (init pI1822) (init pI1822))
theorem I1822_seg2 : segOK pI1822 1052 436 I1822_cp1.1 I1822_cp1.2 I1822_cp2.1 I1822_cp2.2 = true := by
  decide +kernel
theorem I1822_fin : (prmOK pI1822 1822 && intTest pI1822 (runFrom pI1822 (fmask pI1822) (cmask pI1822) (hmask pI1822) 1488 334 (true, I1822_cp2.1, I1822_cp2.2)) 1822 21 true) = true := by
  decide +kernel
theorem I1822_ok : RunOK pI1822 1822 (runFrom pI1822 (fmask pI1822) (cmask pI1822) (hmask pI1822) 1488 334 (true, I1822_cp2.1, I1822_cp2.2)) ∧ intTest pI1822 (runFrom pI1822 (fmask pI1822) (cmask pI1822) (hmask pI1822) 1488 334 (true, I1822_cp2.1, I1822_cp2.2)) 1822 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1822_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1822_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1822_fin) true) I1822_seg1) I1822_seg2) (by decide) rfl I1822_fin intTest_fst
theorem link1822 : linkOK pL1822 pH1822 pI1822 = true := by decide +kernel
theorem cvx1822 : ConvexBetweenHumps 1822 :=
  cvx_of L1822_ok H1822_ok I1822_ok link1822 (by decide)
theorem cenlink1822 : cenLinkOK pI1822 1822 = true := by decide +kernel
theorem cen1822 : CenterUniqueMin 1822 ∧ DipHyp 1822 ∧ OnePointHyps 1822 :=
  cen_of L1822_ok H1822_ok I1822_ok link1822 cenlink1822

/-! ### `N = 1823` -/

def pL1823 : Prm := ⟨80, 37, 40, 1825, 11, 18446744073709551616, 106111716916957566, 106111716916957566⟩
def pH1823 : Prm := ⟨80, 37, 40, 1825, 11, 18446744073709551616, 106112816428585342, 106112816428585342⟩
def pI1823 : Prm := ⟨68, 34, 31, 1825, 11, 18446744073709551616, 106111716916957566, 106112816428585342⟩
noncomputable def L1823_cp1 : Nat × Nat := t7val% (fastRun pL1823 1 1052 (init pL1823) (init pL1823))
theorem L1823_seg1 : segOK pL1823 1 1052 (init pL1823) (init pL1823) L1823_cp1.1 L1823_cp1.2 = true := by
  decide +kernel
noncomputable def L1823_cp2 : Nat × Nat := t7val% (fastRun pL1823 1 1487 (init pL1823) (init pL1823))
theorem L1823_seg2 : segOK pL1823 1053 435 L1823_cp1.1 L1823_cp1.2 L1823_cp2.1 L1823_cp2.2 = true := by
  decide +kernel
theorem L1823_fin : (prmOK pL1823 1823 && ptTest pL1823 (runFrom pL1823 (fmask pL1823) (cmask pL1823) (hmask pL1823) 1488 335 (true, L1823_cp2.1, L1823_cp2.2)) 1823 912 false) = true := by
  decide +kernel
theorem L1823_ok : RunOK pL1823 1823 (runFrom pL1823 (fmask pL1823) (cmask pL1823) (hmask pL1823) 1488 335 (true, L1823_cp2.1, L1823_cp2.2)) ∧ ptTest pL1823 (runFrom pL1823 (fmask pL1823) (cmask pL1823) (hmask pL1823) 1488 335 (true, L1823_cp2.1, L1823_cp2.2)) 1823 912 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1823_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1823_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1823_fin) true) L1823_seg1) L1823_seg2) (by decide) rfl L1823_fin ptTest_fst
noncomputable def H1823_cp1 : Nat × Nat := t7val% (fastRun pH1823 1 1052 (init pH1823) (init pH1823))
theorem H1823_seg1 : segOK pH1823 1 1052 (init pH1823) (init pH1823) H1823_cp1.1 H1823_cp1.2 = true := by
  decide +kernel
noncomputable def H1823_cp2 : Nat × Nat := t7val% (fastRun pH1823 1 1487 (init pH1823) (init pH1823))
theorem H1823_seg2 : segOK pH1823 1053 435 H1823_cp1.1 H1823_cp1.2 H1823_cp2.1 H1823_cp2.2 = true := by
  decide +kernel
theorem H1823_fin : (prmOK pH1823 1823 && ptTest pH1823 (runFrom pH1823 (fmask pH1823) (cmask pH1823) (hmask pH1823) 1488 335 (true, H1823_cp2.1, H1823_cp2.2)) 1823 912 true) = true := by
  decide +kernel
theorem H1823_ok : RunOK pH1823 1823 (runFrom pH1823 (fmask pH1823) (cmask pH1823) (hmask pH1823) 1488 335 (true, H1823_cp2.1, H1823_cp2.2)) ∧ ptTest pH1823 (runFrom pH1823 (fmask pH1823) (cmask pH1823) (hmask pH1823) 1488 335 (true, H1823_cp2.1, H1823_cp2.2)) 1823 912 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1823_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1823_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1823_fin) true) H1823_seg1) H1823_seg2) (by decide) rfl H1823_fin ptTest_fst
noncomputable def I1823_cp1 : Nat × Nat := t7val% (fastRun pI1823 1 1052 (init pI1823) (init pI1823))
theorem I1823_seg1 : segOK pI1823 1 1052 (init pI1823) (init pI1823) I1823_cp1.1 I1823_cp1.2 = true := by
  decide +kernel
noncomputable def I1823_cp2 : Nat × Nat := t7val% (fastRun pI1823 1 1487 (init pI1823) (init pI1823))
theorem I1823_seg2 : segOK pI1823 1053 435 I1823_cp1.1 I1823_cp1.2 I1823_cp2.1 I1823_cp2.2 = true := by
  decide +kernel
theorem I1823_fin : (prmOK pI1823 1823 && intTest pI1823 (runFrom pI1823 (fmask pI1823) (cmask pI1823) (hmask pI1823) 1488 335 (true, I1823_cp2.1, I1823_cp2.2)) 1823 21 false) = true := by
  decide +kernel
theorem I1823_ok : RunOK pI1823 1823 (runFrom pI1823 (fmask pI1823) (cmask pI1823) (hmask pI1823) 1488 335 (true, I1823_cp2.1, I1823_cp2.2)) ∧ intTest pI1823 (runFrom pI1823 (fmask pI1823) (cmask pI1823) (hmask pI1823) 1488 335 (true, I1823_cp2.1, I1823_cp2.2)) 1823 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1823_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1823_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1823_fin) true) I1823_seg1) I1823_seg2) (by decide) rfl I1823_fin intTest_fst
theorem link1823 : linkOK pL1823 pH1823 pI1823 = true := by decide +kernel
theorem cvx1823 : ConvexBetweenHumps 1823 :=
  cvx_of L1823_ok H1823_ok I1823_ok link1823 (by decide)

/-! ### `N = 1824` -/

def pL1824 : Prm := ⟨80, 37, 40, 1826, 11, 18446744073709551616, 106064005351114258, 106064005351114258⟩
def pH1824 : Prm := ⟨80, 37, 40, 1826, 11, 18446744073709551616, 106065104862742034, 106065104862742034⟩
def pI1824 : Prm := ⟨68, 34, 31, 1826, 11, 18446744073709551616, 106064005351114258, 106065104862742034⟩
noncomputable def L1824_cp1 : Nat × Nat := t7val% (fastRun pL1824 1 1052 (init pL1824) (init pL1824))
theorem L1824_seg1 : segOK pL1824 1 1052 (init pL1824) (init pL1824) L1824_cp1.1 L1824_cp1.2 = true := by
  decide +kernel
noncomputable def L1824_cp2 : Nat × Nat := t7val% (fastRun pL1824 1 1488 (init pL1824) (init pL1824))
theorem L1824_seg2 : segOK pL1824 1053 436 L1824_cp1.1 L1824_cp1.2 L1824_cp2.1 L1824_cp2.2 = true := by
  decide +kernel
theorem L1824_fin : (prmOK pL1824 1824 && ptTest pL1824 (runFrom pL1824 (fmask pL1824) (cmask pL1824) (hmask pL1824) 1489 335 (true, L1824_cp2.1, L1824_cp2.2)) 1824 912 false) = true := by
  decide +kernel
theorem L1824_ok : RunOK pL1824 1824 (runFrom pL1824 (fmask pL1824) (cmask pL1824) (hmask pL1824) 1489 335 (true, L1824_cp2.1, L1824_cp2.2)) ∧ ptTest pL1824 (runFrom pL1824 (fmask pL1824) (cmask pL1824) (hmask pL1824) 1489 335 (true, L1824_cp2.1, L1824_cp2.2)) 1824 912 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1824_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1824_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1824_fin) true) L1824_seg1) L1824_seg2) (by decide) rfl L1824_fin ptTest_fst
noncomputable def H1824_cp1 : Nat × Nat := t7val% (fastRun pH1824 1 1052 (init pH1824) (init pH1824))
theorem H1824_seg1 : segOK pH1824 1 1052 (init pH1824) (init pH1824) H1824_cp1.1 H1824_cp1.2 = true := by
  decide +kernel
noncomputable def H1824_cp2 : Nat × Nat := t7val% (fastRun pH1824 1 1488 (init pH1824) (init pH1824))
theorem H1824_seg2 : segOK pH1824 1053 436 H1824_cp1.1 H1824_cp1.2 H1824_cp2.1 H1824_cp2.2 = true := by
  decide +kernel
theorem H1824_fin : (prmOK pH1824 1824 && ptTest pH1824 (runFrom pH1824 (fmask pH1824) (cmask pH1824) (hmask pH1824) 1489 335 (true, H1824_cp2.1, H1824_cp2.2)) 1824 912 true) = true := by
  decide +kernel
theorem H1824_ok : RunOK pH1824 1824 (runFrom pH1824 (fmask pH1824) (cmask pH1824) (hmask pH1824) 1489 335 (true, H1824_cp2.1, H1824_cp2.2)) ∧ ptTest pH1824 (runFrom pH1824 (fmask pH1824) (cmask pH1824) (hmask pH1824) 1489 335 (true, H1824_cp2.1, H1824_cp2.2)) 1824 912 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1824_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1824_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1824_fin) true) H1824_seg1) H1824_seg2) (by decide) rfl H1824_fin ptTest_fst
noncomputable def I1824_cp1 : Nat × Nat := t7val% (fastRun pI1824 1 1052 (init pI1824) (init pI1824))
theorem I1824_seg1 : segOK pI1824 1 1052 (init pI1824) (init pI1824) I1824_cp1.1 I1824_cp1.2 = true := by
  decide +kernel
noncomputable def I1824_cp2 : Nat × Nat := t7val% (fastRun pI1824 1 1488 (init pI1824) (init pI1824))
theorem I1824_seg2 : segOK pI1824 1053 436 I1824_cp1.1 I1824_cp1.2 I1824_cp2.1 I1824_cp2.2 = true := by
  decide +kernel
theorem I1824_fin : (prmOK pI1824 1824 && intTest pI1824 (runFrom pI1824 (fmask pI1824) (cmask pI1824) (hmask pI1824) 1489 335 (true, I1824_cp2.1, I1824_cp2.2)) 1824 21 true) = true := by
  decide +kernel
theorem I1824_ok : RunOK pI1824 1824 (runFrom pI1824 (fmask pI1824) (cmask pI1824) (hmask pI1824) 1489 335 (true, I1824_cp2.1, I1824_cp2.2)) ∧ intTest pI1824 (runFrom pI1824 (fmask pI1824) (cmask pI1824) (hmask pI1824) 1489 335 (true, I1824_cp2.1, I1824_cp2.2)) 1824 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1824_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1824_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1824_fin) true) I1824_seg1) I1824_seg2) (by decide) rfl I1824_fin intTest_fst
theorem link1824 : linkOK pL1824 pH1824 pI1824 = true := by decide +kernel
theorem cvx1824 : ConvexBetweenHumps 1824 :=
  cvx_of L1824_ok H1824_ok I1824_ok link1824 (by decide)
theorem cenlink1824 : cenLinkOK pI1824 1824 = true := by decide +kernel
theorem cen1824 : CenterUniqueMin 1824 ∧ DipHyp 1824 ∧ OnePointHyps 1824 :=
  cen_of L1824_ok H1824_ok I1824_ok link1824 cenlink1824

/-! ### `N = 1825` -/

def pL1825 : Prm := ⟨80, 37, 40, 1827, 11, 18446744073709551616, 106016321863558166, 106016321863558166⟩
def pH1825 : Prm := ⟨80, 37, 40, 1827, 11, 18446744073709551616, 106017421375185942, 106017421375185942⟩
def pI1825 : Prm := ⟨68, 34, 31, 1827, 11, 18446744073709551616, 106016321863558166, 106017421375185942⟩
noncomputable def L1825_cp1 : Nat × Nat := t7val% (fastRun pL1825 1 1053 (init pL1825) (init pL1825))
theorem L1825_seg1 : segOK pL1825 1 1053 (init pL1825) (init pL1825) L1825_cp1.1 L1825_cp1.2 = true := by
  decide +kernel
noncomputable def L1825_cp2 : Nat × Nat := t7val% (fastRun pL1825 1 1489 (init pL1825) (init pL1825))
theorem L1825_seg2 : segOK pL1825 1054 436 L1825_cp1.1 L1825_cp1.2 L1825_cp2.1 L1825_cp2.2 = true := by
  decide +kernel
theorem L1825_fin : (prmOK pL1825 1825 && ptTest pL1825 (runFrom pL1825 (fmask pL1825) (cmask pL1825) (hmask pL1825) 1490 335 (true, L1825_cp2.1, L1825_cp2.2)) 1825 913 false) = true := by
  decide +kernel
theorem L1825_ok : RunOK pL1825 1825 (runFrom pL1825 (fmask pL1825) (cmask pL1825) (hmask pL1825) 1490 335 (true, L1825_cp2.1, L1825_cp2.2)) ∧ ptTest pL1825 (runFrom pL1825 (fmask pL1825) (cmask pL1825) (hmask pL1825) 1490 335 (true, L1825_cp2.1, L1825_cp2.2)) 1825 913 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1825_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1825_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1825_fin) true) L1825_seg1) L1825_seg2) (by decide) rfl L1825_fin ptTest_fst
noncomputable def H1825_cp1 : Nat × Nat := t7val% (fastRun pH1825 1 1053 (init pH1825) (init pH1825))
theorem H1825_seg1 : segOK pH1825 1 1053 (init pH1825) (init pH1825) H1825_cp1.1 H1825_cp1.2 = true := by
  decide +kernel
noncomputable def H1825_cp2 : Nat × Nat := t7val% (fastRun pH1825 1 1489 (init pH1825) (init pH1825))
theorem H1825_seg2 : segOK pH1825 1054 436 H1825_cp1.1 H1825_cp1.2 H1825_cp2.1 H1825_cp2.2 = true := by
  decide +kernel
theorem H1825_fin : (prmOK pH1825 1825 && ptTest pH1825 (runFrom pH1825 (fmask pH1825) (cmask pH1825) (hmask pH1825) 1490 335 (true, H1825_cp2.1, H1825_cp2.2)) 1825 913 true) = true := by
  decide +kernel
theorem H1825_ok : RunOK pH1825 1825 (runFrom pH1825 (fmask pH1825) (cmask pH1825) (hmask pH1825) 1490 335 (true, H1825_cp2.1, H1825_cp2.2)) ∧ ptTest pH1825 (runFrom pH1825 (fmask pH1825) (cmask pH1825) (hmask pH1825) 1490 335 (true, H1825_cp2.1, H1825_cp2.2)) 1825 913 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1825_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1825_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1825_fin) true) H1825_seg1) H1825_seg2) (by decide) rfl H1825_fin ptTest_fst
noncomputable def I1825_cp1 : Nat × Nat := t7val% (fastRun pI1825 1 1053 (init pI1825) (init pI1825))
theorem I1825_seg1 : segOK pI1825 1 1053 (init pI1825) (init pI1825) I1825_cp1.1 I1825_cp1.2 = true := by
  decide +kernel
noncomputable def I1825_cp2 : Nat × Nat := t7val% (fastRun pI1825 1 1489 (init pI1825) (init pI1825))
theorem I1825_seg2 : segOK pI1825 1054 436 I1825_cp1.1 I1825_cp1.2 I1825_cp2.1 I1825_cp2.2 = true := by
  decide +kernel
theorem I1825_fin : (prmOK pI1825 1825 && intTest pI1825 (runFrom pI1825 (fmask pI1825) (cmask pI1825) (hmask pI1825) 1490 335 (true, I1825_cp2.1, I1825_cp2.2)) 1825 21 false) = true := by
  decide +kernel
theorem I1825_ok : RunOK pI1825 1825 (runFrom pI1825 (fmask pI1825) (cmask pI1825) (hmask pI1825) 1490 335 (true, I1825_cp2.1, I1825_cp2.2)) ∧ intTest pI1825 (runFrom pI1825 (fmask pI1825) (cmask pI1825) (hmask pI1825) 1490 335 (true, I1825_cp2.1, I1825_cp2.2)) 1825 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1825_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1825_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1825_fin) true) I1825_seg1) I1825_seg2) (by decide) rfl I1825_fin intTest_fst
theorem link1825 : linkOK pL1825 pH1825 pI1825 = true := by decide +kernel
theorem cvx1825 : ConvexBetweenHumps 1825 :=
  cvx_of L1825_ok H1825_ok I1825_ok link1825 (by decide)

/-! ### `N = 1826` -/

def pL1826 : Prm := ⟨80, 37, 40, 1828, 11, 18446744073709551616, 105968703320679172, 105968703320679172⟩
def pH1826 : Prm := ⟨80, 37, 40, 1828, 11, 18446744073709551616, 105969802832306948, 105969802832306948⟩
def pI1826 : Prm := ⟨68, 34, 31, 1828, 11, 18446744073709551616, 105968703320679172, 105969802832306948⟩
noncomputable def L1826_cp1 : Nat × Nat := t7val% (fastRun pL1826 1 1053 (init pL1826) (init pL1826))
theorem L1826_seg1 : segOK pL1826 1 1053 (init pL1826) (init pL1826) L1826_cp1.1 L1826_cp1.2 = true := by
  decide +kernel
noncomputable def L1826_cp2 : Nat × Nat := t7val% (fastRun pL1826 1 1490 (init pL1826) (init pL1826))
theorem L1826_seg2 : segOK pL1826 1054 437 L1826_cp1.1 L1826_cp1.2 L1826_cp2.1 L1826_cp2.2 = true := by
  decide +kernel
theorem L1826_fin : (prmOK pL1826 1826 && ptTest pL1826 (runFrom pL1826 (fmask pL1826) (cmask pL1826) (hmask pL1826) 1491 335 (true, L1826_cp2.1, L1826_cp2.2)) 1826 913 false) = true := by
  decide +kernel
theorem L1826_ok : RunOK pL1826 1826 (runFrom pL1826 (fmask pL1826) (cmask pL1826) (hmask pL1826) 1491 335 (true, L1826_cp2.1, L1826_cp2.2)) ∧ ptTest pL1826 (runFrom pL1826 (fmask pL1826) (cmask pL1826) (hmask pL1826) 1491 335 (true, L1826_cp2.1, L1826_cp2.2)) 1826 913 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1826_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1826_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1826_fin) true) L1826_seg1) L1826_seg2) (by decide) rfl L1826_fin ptTest_fst
noncomputable def H1826_cp1 : Nat × Nat := t7val% (fastRun pH1826 1 1053 (init pH1826) (init pH1826))
theorem H1826_seg1 : segOK pH1826 1 1053 (init pH1826) (init pH1826) H1826_cp1.1 H1826_cp1.2 = true := by
  decide +kernel
noncomputable def H1826_cp2 : Nat × Nat := t7val% (fastRun pH1826 1 1490 (init pH1826) (init pH1826))
theorem H1826_seg2 : segOK pH1826 1054 437 H1826_cp1.1 H1826_cp1.2 H1826_cp2.1 H1826_cp2.2 = true := by
  decide +kernel
theorem H1826_fin : (prmOK pH1826 1826 && ptTest pH1826 (runFrom pH1826 (fmask pH1826) (cmask pH1826) (hmask pH1826) 1491 335 (true, H1826_cp2.1, H1826_cp2.2)) 1826 913 true) = true := by
  decide +kernel
theorem H1826_ok : RunOK pH1826 1826 (runFrom pH1826 (fmask pH1826) (cmask pH1826) (hmask pH1826) 1491 335 (true, H1826_cp2.1, H1826_cp2.2)) ∧ ptTest pH1826 (runFrom pH1826 (fmask pH1826) (cmask pH1826) (hmask pH1826) 1491 335 (true, H1826_cp2.1, H1826_cp2.2)) 1826 913 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1826_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1826_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1826_fin) true) H1826_seg1) H1826_seg2) (by decide) rfl H1826_fin ptTest_fst
noncomputable def I1826_cp1 : Nat × Nat := t7val% (fastRun pI1826 1 1053 (init pI1826) (init pI1826))
theorem I1826_seg1 : segOK pI1826 1 1053 (init pI1826) (init pI1826) I1826_cp1.1 I1826_cp1.2 = true := by
  decide +kernel
noncomputable def I1826_cp2 : Nat × Nat := t7val% (fastRun pI1826 1 1490 (init pI1826) (init pI1826))
theorem I1826_seg2 : segOK pI1826 1054 437 I1826_cp1.1 I1826_cp1.2 I1826_cp2.1 I1826_cp2.2 = true := by
  decide +kernel
theorem I1826_fin : (prmOK pI1826 1826 && intTest pI1826 (runFrom pI1826 (fmask pI1826) (cmask pI1826) (hmask pI1826) 1491 335 (true, I1826_cp2.1, I1826_cp2.2)) 1826 21 true) = true := by
  decide +kernel
theorem I1826_ok : RunOK pI1826 1826 (runFrom pI1826 (fmask pI1826) (cmask pI1826) (hmask pI1826) 1491 335 (true, I1826_cp2.1, I1826_cp2.2)) ∧ intTest pI1826 (runFrom pI1826 (fmask pI1826) (cmask pI1826) (hmask pI1826) 1491 335 (true, I1826_cp2.1, I1826_cp2.2)) 1826 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1826_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1826_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1826_fin) true) I1826_seg1) I1826_seg2) (by decide) rfl I1826_fin intTest_fst
theorem link1826 : linkOK pL1826 pH1826 pI1826 = true := by decide +kernel
theorem cvx1826 : ConvexBetweenHumps 1826 :=
  cvx_of L1826_ok H1826_ok I1826_ok link1826 (by decide)
theorem cenlink1826 : cenLinkOK pI1826 1826 = true := by decide +kernel
theorem cen1826 : CenterUniqueMin 1826 ∧ DipHyp 1826 ∧ OnePointHyps 1826 :=
  cen_of L1826_ok H1826_ok I1826_ok link1826 cenlink1826

/-! ### `N = 1827` -/

def pL1827 : Prm := ⟨80, 37, 40, 1829, 11, 18446744073709551616, 105921112777375137, 105921112777375137⟩
def pH1827 : Prm := ⟨80, 37, 40, 1829, 11, 18446744073709551616, 105922212289002913, 105922212289002913⟩
def pI1827 : Prm := ⟨68, 34, 31, 1829, 11, 18446744073709551616, 105921112777375137, 105922212289002913⟩
noncomputable def L1827_cp1 : Nat × Nat := t7val% (fastRun pL1827 1 1054 (init pL1827) (init pL1827))
theorem L1827_seg1 : segOK pL1827 1 1054 (init pL1827) (init pL1827) L1827_cp1.1 L1827_cp1.2 = true := by
  decide +kernel
noncomputable def L1827_cp2 : Nat × Nat := t7val% (fastRun pL1827 1 1491 (init pL1827) (init pL1827))
theorem L1827_seg2 : segOK pL1827 1055 437 L1827_cp1.1 L1827_cp1.2 L1827_cp2.1 L1827_cp2.2 = true := by
  decide +kernel
theorem L1827_fin : (prmOK pL1827 1827 && ptTest pL1827 (runFrom pL1827 (fmask pL1827) (cmask pL1827) (hmask pL1827) 1492 335 (true, L1827_cp2.1, L1827_cp2.2)) 1827 914 false) = true := by
  decide +kernel
theorem L1827_ok : RunOK pL1827 1827 (runFrom pL1827 (fmask pL1827) (cmask pL1827) (hmask pL1827) 1492 335 (true, L1827_cp2.1, L1827_cp2.2)) ∧ ptTest pL1827 (runFrom pL1827 (fmask pL1827) (cmask pL1827) (hmask pL1827) 1492 335 (true, L1827_cp2.1, L1827_cp2.2)) 1827 914 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1827_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1827_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1827_fin) true) L1827_seg1) L1827_seg2) (by decide) rfl L1827_fin ptTest_fst
noncomputable def H1827_cp1 : Nat × Nat := t7val% (fastRun pH1827 1 1054 (init pH1827) (init pH1827))
theorem H1827_seg1 : segOK pH1827 1 1054 (init pH1827) (init pH1827) H1827_cp1.1 H1827_cp1.2 = true := by
  decide +kernel
noncomputable def H1827_cp2 : Nat × Nat := t7val% (fastRun pH1827 1 1491 (init pH1827) (init pH1827))
theorem H1827_seg2 : segOK pH1827 1055 437 H1827_cp1.1 H1827_cp1.2 H1827_cp2.1 H1827_cp2.2 = true := by
  decide +kernel
theorem H1827_fin : (prmOK pH1827 1827 && ptTest pH1827 (runFrom pH1827 (fmask pH1827) (cmask pH1827) (hmask pH1827) 1492 335 (true, H1827_cp2.1, H1827_cp2.2)) 1827 914 true) = true := by
  decide +kernel
theorem H1827_ok : RunOK pH1827 1827 (runFrom pH1827 (fmask pH1827) (cmask pH1827) (hmask pH1827) 1492 335 (true, H1827_cp2.1, H1827_cp2.2)) ∧ ptTest pH1827 (runFrom pH1827 (fmask pH1827) (cmask pH1827) (hmask pH1827) 1492 335 (true, H1827_cp2.1, H1827_cp2.2)) 1827 914 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1827_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1827_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1827_fin) true) H1827_seg1) H1827_seg2) (by decide) rfl H1827_fin ptTest_fst
noncomputable def I1827_cp1 : Nat × Nat := t7val% (fastRun pI1827 1 1054 (init pI1827) (init pI1827))
theorem I1827_seg1 : segOK pI1827 1 1054 (init pI1827) (init pI1827) I1827_cp1.1 I1827_cp1.2 = true := by
  decide +kernel
noncomputable def I1827_cp2 : Nat × Nat := t7val% (fastRun pI1827 1 1491 (init pI1827) (init pI1827))
theorem I1827_seg2 : segOK pI1827 1055 437 I1827_cp1.1 I1827_cp1.2 I1827_cp2.1 I1827_cp2.2 = true := by
  decide +kernel
theorem I1827_fin : (prmOK pI1827 1827 && intTest pI1827 (runFrom pI1827 (fmask pI1827) (cmask pI1827) (hmask pI1827) 1492 335 (true, I1827_cp2.1, I1827_cp2.2)) 1827 21 false) = true := by
  decide +kernel
theorem I1827_ok : RunOK pI1827 1827 (runFrom pI1827 (fmask pI1827) (cmask pI1827) (hmask pI1827) 1492 335 (true, I1827_cp2.1, I1827_cp2.2)) ∧ intTest pI1827 (runFrom pI1827 (fmask pI1827) (cmask pI1827) (hmask pI1827) 1492 335 (true, I1827_cp2.1, I1827_cp2.2)) 1827 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1827_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1827_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1827_fin) true) I1827_seg1) I1827_seg2) (by decide) rfl I1827_fin intTest_fst
theorem link1827 : linkOK pL1827 pH1827 pI1827 = true := by decide +kernel
theorem cvx1827 : ConvexBetweenHumps 1827 :=
  cvx_of L1827_ok H1827_ok I1827_ok link1827 (by decide)

/-! ### `N = 1828` -/

def pL1828 : Prm := ⟨80, 37, 40, 1830, 11, 18446744073709551616, 105873586977309754, 105873586977309754⟩
def pH1828 : Prm := ⟨80, 37, 40, 1830, 11, 18446744073709551616, 105874686488937530, 105874686488937530⟩
def pI1828 : Prm := ⟨68, 34, 31, 1830, 11, 18446744073709551616, 105873586977309754, 105874686488937530⟩
noncomputable def L1828_cp1 : Nat × Nat := t7val% (fastRun pL1828 1 1054 (init pL1828) (init pL1828))
theorem L1828_seg1 : segOK pL1828 1 1054 (init pL1828) (init pL1828) L1828_cp1.1 L1828_cp1.2 = true := by
  decide +kernel
noncomputable def L1828_cp2 : Nat × Nat := t7val% (fastRun pL1828 1 1492 (init pL1828) (init pL1828))
theorem L1828_seg2 : segOK pL1828 1055 438 L1828_cp1.1 L1828_cp1.2 L1828_cp2.1 L1828_cp2.2 = true := by
  decide +kernel
theorem L1828_fin : (prmOK pL1828 1828 && ptTest pL1828 (runFrom pL1828 (fmask pL1828) (cmask pL1828) (hmask pL1828) 1493 335 (true, L1828_cp2.1, L1828_cp2.2)) 1828 914 false) = true := by
  decide +kernel
theorem L1828_ok : RunOK pL1828 1828 (runFrom pL1828 (fmask pL1828) (cmask pL1828) (hmask pL1828) 1493 335 (true, L1828_cp2.1, L1828_cp2.2)) ∧ ptTest pL1828 (runFrom pL1828 (fmask pL1828) (cmask pL1828) (hmask pL1828) 1493 335 (true, L1828_cp2.1, L1828_cp2.2)) 1828 914 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1828_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1828_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1828_fin) true) L1828_seg1) L1828_seg2) (by decide) rfl L1828_fin ptTest_fst
noncomputable def H1828_cp1 : Nat × Nat := t7val% (fastRun pH1828 1 1054 (init pH1828) (init pH1828))
theorem H1828_seg1 : segOK pH1828 1 1054 (init pH1828) (init pH1828) H1828_cp1.1 H1828_cp1.2 = true := by
  decide +kernel
noncomputable def H1828_cp2 : Nat × Nat := t7val% (fastRun pH1828 1 1492 (init pH1828) (init pH1828))
theorem H1828_seg2 : segOK pH1828 1055 438 H1828_cp1.1 H1828_cp1.2 H1828_cp2.1 H1828_cp2.2 = true := by
  decide +kernel
theorem H1828_fin : (prmOK pH1828 1828 && ptTest pH1828 (runFrom pH1828 (fmask pH1828) (cmask pH1828) (hmask pH1828) 1493 335 (true, H1828_cp2.1, H1828_cp2.2)) 1828 914 true) = true := by
  decide +kernel
theorem H1828_ok : RunOK pH1828 1828 (runFrom pH1828 (fmask pH1828) (cmask pH1828) (hmask pH1828) 1493 335 (true, H1828_cp2.1, H1828_cp2.2)) ∧ ptTest pH1828 (runFrom pH1828 (fmask pH1828) (cmask pH1828) (hmask pH1828) 1493 335 (true, H1828_cp2.1, H1828_cp2.2)) 1828 914 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1828_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1828_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1828_fin) true) H1828_seg1) H1828_seg2) (by decide) rfl H1828_fin ptTest_fst
noncomputable def I1828_cp1 : Nat × Nat := t7val% (fastRun pI1828 1 1054 (init pI1828) (init pI1828))
theorem I1828_seg1 : segOK pI1828 1 1054 (init pI1828) (init pI1828) I1828_cp1.1 I1828_cp1.2 = true := by
  decide +kernel
noncomputable def I1828_cp2 : Nat × Nat := t7val% (fastRun pI1828 1 1492 (init pI1828) (init pI1828))
theorem I1828_seg2 : segOK pI1828 1055 438 I1828_cp1.1 I1828_cp1.2 I1828_cp2.1 I1828_cp2.2 = true := by
  decide +kernel
theorem I1828_fin : (prmOK pI1828 1828 && intTest pI1828 (runFrom pI1828 (fmask pI1828) (cmask pI1828) (hmask pI1828) 1493 335 (true, I1828_cp2.1, I1828_cp2.2)) 1828 21 true) = true := by
  decide +kernel
theorem I1828_ok : RunOK pI1828 1828 (runFrom pI1828 (fmask pI1828) (cmask pI1828) (hmask pI1828) 1493 335 (true, I1828_cp2.1, I1828_cp2.2)) ∧ intTest pI1828 (runFrom pI1828 (fmask pI1828) (cmask pI1828) (hmask pI1828) 1493 335 (true, I1828_cp2.1, I1828_cp2.2)) 1828 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1828_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1828_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1828_fin) true) I1828_seg1) I1828_seg2) (by decide) rfl I1828_fin intTest_fst
theorem link1828 : linkOK pL1828 pH1828 pI1828 = true := by decide +kernel
theorem cvx1828 : ConvexBetweenHumps 1828 :=
  cvx_of L1828_ok H1828_ok I1828_ok link1828 (by decide)
theorem cenlink1828 : cenLinkOK pI1828 1828 = true := by decide +kernel
theorem cen1828 : CenterUniqueMin 1828 ∧ DipHyp 1828 ∧ OnePointHyps 1828 :=
  cen_of L1828_ok H1828_ok I1828_ok link1828 cenlink1828

/-! ### `N = 1829` -/

def pL1829 : Prm := ⟨80, 37, 40, 1831, 11, 18446744073709551616, 105826089098383775, 105826089098383775⟩
def pH1829 : Prm := ⟨80, 37, 40, 1831, 11, 18446744073709551616, 105827188610011551, 105827188610011551⟩
def pI1829 : Prm := ⟨68, 34, 31, 1831, 11, 18446744073709551616, 105826089098383775, 105827188610011551⟩
noncomputable def L1829_cp1 : Nat × Nat := t7val% (fastRun pL1829 1 1055 (init pL1829) (init pL1829))
theorem L1829_seg1 : segOK pL1829 1 1055 (init pL1829) (init pL1829) L1829_cp1.1 L1829_cp1.2 = true := by
  decide +kernel
noncomputable def L1829_cp2 : Nat × Nat := t7val% (fastRun pL1829 1 1492 (init pL1829) (init pL1829))
theorem L1829_seg2 : segOK pL1829 1056 437 L1829_cp1.1 L1829_cp1.2 L1829_cp2.1 L1829_cp2.2 = true := by
  decide +kernel
theorem L1829_fin : (prmOK pL1829 1829 && ptTest pL1829 (runFrom pL1829 (fmask pL1829) (cmask pL1829) (hmask pL1829) 1493 336 (true, L1829_cp2.1, L1829_cp2.2)) 1829 915 false) = true := by
  decide +kernel
theorem L1829_ok : RunOK pL1829 1829 (runFrom pL1829 (fmask pL1829) (cmask pL1829) (hmask pL1829) 1493 336 (true, L1829_cp2.1, L1829_cp2.2)) ∧ ptTest pL1829 (runFrom pL1829 (fmask pL1829) (cmask pL1829) (hmask pL1829) 1493 336 (true, L1829_cp2.1, L1829_cp2.2)) 1829 915 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1829_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1829_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1829_fin) true) L1829_seg1) L1829_seg2) (by decide) rfl L1829_fin ptTest_fst
noncomputable def H1829_cp1 : Nat × Nat := t7val% (fastRun pH1829 1 1055 (init pH1829) (init pH1829))
theorem H1829_seg1 : segOK pH1829 1 1055 (init pH1829) (init pH1829) H1829_cp1.1 H1829_cp1.2 = true := by
  decide +kernel
noncomputable def H1829_cp2 : Nat × Nat := t7val% (fastRun pH1829 1 1492 (init pH1829) (init pH1829))
theorem H1829_seg2 : segOK pH1829 1056 437 H1829_cp1.1 H1829_cp1.2 H1829_cp2.1 H1829_cp2.2 = true := by
  decide +kernel
theorem H1829_fin : (prmOK pH1829 1829 && ptTest pH1829 (runFrom pH1829 (fmask pH1829) (cmask pH1829) (hmask pH1829) 1493 336 (true, H1829_cp2.1, H1829_cp2.2)) 1829 915 true) = true := by
  decide +kernel
theorem H1829_ok : RunOK pH1829 1829 (runFrom pH1829 (fmask pH1829) (cmask pH1829) (hmask pH1829) 1493 336 (true, H1829_cp2.1, H1829_cp2.2)) ∧ ptTest pH1829 (runFrom pH1829 (fmask pH1829) (cmask pH1829) (hmask pH1829) 1493 336 (true, H1829_cp2.1, H1829_cp2.2)) 1829 915 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1829_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1829_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1829_fin) true) H1829_seg1) H1829_seg2) (by decide) rfl H1829_fin ptTest_fst
noncomputable def I1829_cp1 : Nat × Nat := t7val% (fastRun pI1829 1 1055 (init pI1829) (init pI1829))
theorem I1829_seg1 : segOK pI1829 1 1055 (init pI1829) (init pI1829) I1829_cp1.1 I1829_cp1.2 = true := by
  decide +kernel
noncomputable def I1829_cp2 : Nat × Nat := t7val% (fastRun pI1829 1 1492 (init pI1829) (init pI1829))
theorem I1829_seg2 : segOK pI1829 1056 437 I1829_cp1.1 I1829_cp1.2 I1829_cp2.1 I1829_cp2.2 = true := by
  decide +kernel
theorem I1829_fin : (prmOK pI1829 1829 && intTest pI1829 (runFrom pI1829 (fmask pI1829) (cmask pI1829) (hmask pI1829) 1493 336 (true, I1829_cp2.1, I1829_cp2.2)) 1829 21 false) = true := by
  decide +kernel
theorem I1829_ok : RunOK pI1829 1829 (runFrom pI1829 (fmask pI1829) (cmask pI1829) (hmask pI1829) 1493 336 (true, I1829_cp2.1, I1829_cp2.2)) ∧ intTest pI1829 (runFrom pI1829 (fmask pI1829) (cmask pI1829) (hmask pI1829) 1493 336 (true, I1829_cp2.1, I1829_cp2.2)) 1829 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1829_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1829_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1829_fin) true) I1829_seg1) I1829_seg2) (by decide) rfl I1829_fin intTest_fst
theorem link1829 : linkOK pL1829 pH1829 pI1829 = true := by decide +kernel
theorem cvx1829 : ConvexBetweenHumps 1829 :=
  cvx_of L1829_ok H1829_ok I1829_ok link1829 (by decide)

/-! ### `N = 1830` -/

def pL1830 : Prm := ⟨80, 37, 40, 1832, 11, 18446744073709551616, 105778655762106552, 105778655762106552⟩
def pH1830 : Prm := ⟨80, 37, 40, 1832, 11, 18446744073709551616, 105779755273734328, 105779755273734328⟩
def pI1830 : Prm := ⟨68, 34, 31, 1832, 11, 18446744073709551616, 105778655762106552, 105779755273734328⟩
noncomputable def L1830_cp1 : Nat × Nat := t7val% (fastRun pL1830 1 1056 (init pL1830) (init pL1830))
theorem L1830_seg1 : segOK pL1830 1 1056 (init pL1830) (init pL1830) L1830_cp1.1 L1830_cp1.2 = true := by
  decide +kernel
noncomputable def L1830_cp2 : Nat × Nat := t7val% (fastRun pL1830 1 1493 (init pL1830) (init pL1830))
theorem L1830_seg2 : segOK pL1830 1057 437 L1830_cp1.1 L1830_cp1.2 L1830_cp2.1 L1830_cp2.2 = true := by
  decide +kernel
theorem L1830_fin : (prmOK pL1830 1830 && ptTest pL1830 (runFrom pL1830 (fmask pL1830) (cmask pL1830) (hmask pL1830) 1494 336 (true, L1830_cp2.1, L1830_cp2.2)) 1830 915 false) = true := by
  decide +kernel
theorem L1830_ok : RunOK pL1830 1830 (runFrom pL1830 (fmask pL1830) (cmask pL1830) (hmask pL1830) 1494 336 (true, L1830_cp2.1, L1830_cp2.2)) ∧ ptTest pL1830 (runFrom pL1830 (fmask pL1830) (cmask pL1830) (hmask pL1830) 1494 336 (true, L1830_cp2.1, L1830_cp2.2)) 1830 915 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1830_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1830_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1830_fin) true) L1830_seg1) L1830_seg2) (by decide) rfl L1830_fin ptTest_fst
noncomputable def H1830_cp1 : Nat × Nat := t7val% (fastRun pH1830 1 1056 (init pH1830) (init pH1830))
theorem H1830_seg1 : segOK pH1830 1 1056 (init pH1830) (init pH1830) H1830_cp1.1 H1830_cp1.2 = true := by
  decide +kernel
noncomputable def H1830_cp2 : Nat × Nat := t7val% (fastRun pH1830 1 1493 (init pH1830) (init pH1830))
theorem H1830_seg2 : segOK pH1830 1057 437 H1830_cp1.1 H1830_cp1.2 H1830_cp2.1 H1830_cp2.2 = true := by
  decide +kernel
theorem H1830_fin : (prmOK pH1830 1830 && ptTest pH1830 (runFrom pH1830 (fmask pH1830) (cmask pH1830) (hmask pH1830) 1494 336 (true, H1830_cp2.1, H1830_cp2.2)) 1830 915 true) = true := by
  decide +kernel
theorem H1830_ok : RunOK pH1830 1830 (runFrom pH1830 (fmask pH1830) (cmask pH1830) (hmask pH1830) 1494 336 (true, H1830_cp2.1, H1830_cp2.2)) ∧ ptTest pH1830 (runFrom pH1830 (fmask pH1830) (cmask pH1830) (hmask pH1830) 1494 336 (true, H1830_cp2.1, H1830_cp2.2)) 1830 915 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1830_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1830_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1830_fin) true) H1830_seg1) H1830_seg2) (by decide) rfl H1830_fin ptTest_fst
noncomputable def I1830_cp1 : Nat × Nat := t7val% (fastRun pI1830 1 1056 (init pI1830) (init pI1830))
theorem I1830_seg1 : segOK pI1830 1 1056 (init pI1830) (init pI1830) I1830_cp1.1 I1830_cp1.2 = true := by
  decide +kernel
noncomputable def I1830_cp2 : Nat × Nat := t7val% (fastRun pI1830 1 1493 (init pI1830) (init pI1830))
theorem I1830_seg2 : segOK pI1830 1057 437 I1830_cp1.1 I1830_cp1.2 I1830_cp2.1 I1830_cp2.2 = true := by
  decide +kernel
theorem I1830_fin : (prmOK pI1830 1830 && intTest pI1830 (runFrom pI1830 (fmask pI1830) (cmask pI1830) (hmask pI1830) 1494 336 (true, I1830_cp2.1, I1830_cp2.2)) 1830 21 true) = true := by
  decide +kernel
theorem I1830_ok : RunOK pI1830 1830 (runFrom pI1830 (fmask pI1830) (cmask pI1830) (hmask pI1830) 1494 336 (true, I1830_cp2.1, I1830_cp2.2)) ∧ intTest pI1830 (runFrom pI1830 (fmask pI1830) (cmask pI1830) (hmask pI1830) 1494 336 (true, I1830_cp2.1, I1830_cp2.2)) 1830 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1830_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1830_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1830_fin) true) I1830_seg1) I1830_seg2) (by decide) rfl I1830_fin intTest_fst
theorem link1830 : linkOK pL1830 pH1830 pI1830 = true := by decide +kernel
theorem cvx1830 : ConvexBetweenHumps 1830 :=
  cvx_of L1830_ok H1830_ok I1830_ok link1830 (by decide)
theorem cenlink1830 : cenLinkOK pI1830 1830 = true := by decide +kernel
theorem cen1830 : CenterUniqueMin 1830 ∧ DipHyp 1830 ∧ OnePointHyps 1830 :=
  cen_of L1830_ok H1830_ok I1830_ok link1830 cenlink1830

/-! ### `N = 1831` -/

def pL1831 : Prm := ⟨80, 37, 40, 1833, 11, 18446744073709551616, 105731250268865219, 105731250268865219⟩
def pH1831 : Prm := ⟨80, 37, 40, 1833, 11, 18446744073709551616, 105732349780492995, 105732349780492995⟩
def pI1831 : Prm := ⟨68, 34, 31, 1833, 11, 18446744073709551616, 105731250268865219, 105732349780492995⟩
noncomputable def L1831_cp1 : Nat × Nat := t7val% (fastRun pL1831 1 1056 (init pL1831) (init pL1831))
theorem L1831_seg1 : segOK pL1831 1 1056 (init pL1831) (init pL1831) L1831_cp1.1 L1831_cp1.2 = true := by
  decide +kernel
noncomputable def L1831_cp2 : Nat × Nat := t7val% (fastRun pL1831 1 1494 (init pL1831) (init pL1831))
theorem L1831_seg2 : segOK pL1831 1057 438 L1831_cp1.1 L1831_cp1.2 L1831_cp2.1 L1831_cp2.2 = true := by
  decide +kernel
theorem L1831_fin : (prmOK pL1831 1831 && ptTest pL1831 (runFrom pL1831 (fmask pL1831) (cmask pL1831) (hmask pL1831) 1495 336 (true, L1831_cp2.1, L1831_cp2.2)) 1831 916 false) = true := by
  decide +kernel
theorem L1831_ok : RunOK pL1831 1831 (runFrom pL1831 (fmask pL1831) (cmask pL1831) (hmask pL1831) 1495 336 (true, L1831_cp2.1, L1831_cp2.2)) ∧ ptTest pL1831 (runFrom pL1831 (fmask pL1831) (cmask pL1831) (hmask pL1831) 1495 336 (true, L1831_cp2.1, L1831_cp2.2)) 1831 916 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1831_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1831_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1831_fin) true) L1831_seg1) L1831_seg2) (by decide) rfl L1831_fin ptTest_fst
noncomputable def H1831_cp1 : Nat × Nat := t7val% (fastRun pH1831 1 1056 (init pH1831) (init pH1831))
theorem H1831_seg1 : segOK pH1831 1 1056 (init pH1831) (init pH1831) H1831_cp1.1 H1831_cp1.2 = true := by
  decide +kernel
noncomputable def H1831_cp2 : Nat × Nat := t7val% (fastRun pH1831 1 1494 (init pH1831) (init pH1831))
theorem H1831_seg2 : segOK pH1831 1057 438 H1831_cp1.1 H1831_cp1.2 H1831_cp2.1 H1831_cp2.2 = true := by
  decide +kernel
theorem H1831_fin : (prmOK pH1831 1831 && ptTest pH1831 (runFrom pH1831 (fmask pH1831) (cmask pH1831) (hmask pH1831) 1495 336 (true, H1831_cp2.1, H1831_cp2.2)) 1831 916 true) = true := by
  decide +kernel
theorem H1831_ok : RunOK pH1831 1831 (runFrom pH1831 (fmask pH1831) (cmask pH1831) (hmask pH1831) 1495 336 (true, H1831_cp2.1, H1831_cp2.2)) ∧ ptTest pH1831 (runFrom pH1831 (fmask pH1831) (cmask pH1831) (hmask pH1831) 1495 336 (true, H1831_cp2.1, H1831_cp2.2)) 1831 916 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1831_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1831_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1831_fin) true) H1831_seg1) H1831_seg2) (by decide) rfl H1831_fin ptTest_fst
noncomputable def I1831_cp1 : Nat × Nat := t7val% (fastRun pI1831 1 1056 (init pI1831) (init pI1831))
theorem I1831_seg1 : segOK pI1831 1 1056 (init pI1831) (init pI1831) I1831_cp1.1 I1831_cp1.2 = true := by
  decide +kernel
noncomputable def I1831_cp2 : Nat × Nat := t7val% (fastRun pI1831 1 1494 (init pI1831) (init pI1831))
theorem I1831_seg2 : segOK pI1831 1057 438 I1831_cp1.1 I1831_cp1.2 I1831_cp2.1 I1831_cp2.2 = true := by
  decide +kernel
theorem I1831_fin : (prmOK pI1831 1831 && intTest pI1831 (runFrom pI1831 (fmask pI1831) (cmask pI1831) (hmask pI1831) 1495 336 (true, I1831_cp2.1, I1831_cp2.2)) 1831 21 false) = true := by
  decide +kernel
theorem I1831_ok : RunOK pI1831 1831 (runFrom pI1831 (fmask pI1831) (cmask pI1831) (hmask pI1831) 1495 336 (true, I1831_cp2.1, I1831_cp2.2)) ∧ intTest pI1831 (runFrom pI1831 (fmask pI1831) (cmask pI1831) (hmask pI1831) 1495 336 (true, I1831_cp2.1, I1831_cp2.2)) 1831 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1831_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1831_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1831_fin) true) I1831_seg1) I1831_seg2) (by decide) rfl I1831_fin intTest_fst
theorem link1831 : linkOK pL1831 pH1831 pI1831 = true := by decide +kernel
theorem cvx1831 : ConvexBetweenHumps 1831 :=
  cvx_of L1831_ok H1831_ok I1831_ok link1831 (by decide)

/-! ### The range -/

theorem cvx_1820_1831 {N : ℕ} (h1 : 1820 ≤ N) (h2 : N ≤ 1831) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1825
  · by_cases h4 : N ≤ 1822
    · by_cases h6 : N ≤ 1820
      · obtain rfl : N = 1820 := by omega
        exact cvx1820
      · by_cases h8 : N ≤ 1821
        · obtain rfl : N = 1821 := by omega
          exact cvx1821
        · obtain rfl : N = 1822 := by omega
          exact cvx1822
    · by_cases h6 : N ≤ 1823
      · obtain rfl : N = 1823 := by omega
        exact cvx1823
      · by_cases h8 : N ≤ 1824
        · obtain rfl : N = 1824 := by omega
          exact cvx1824
        · obtain rfl : N = 1825 := by omega
          exact cvx1825
  · by_cases h4 : N ≤ 1828
    · by_cases h6 : N ≤ 1826
      · obtain rfl : N = 1826 := by omega
        exact cvx1826
      · by_cases h8 : N ≤ 1827
        · obtain rfl : N = 1827 := by omega
          exact cvx1827
        · obtain rfl : N = 1828 := by omega
          exact cvx1828
    · by_cases h6 : N ≤ 1829
      · obtain rfl : N = 1829 := by omega
        exact cvx1829
      · by_cases h8 : N ≤ 1830
        · obtain rfl : N = 1830 := by omega
          exact cvx1830
        · obtain rfl : N = 1831 := by omega
          exact cvx1831

theorem cen_1820_1831 {N : ℕ} (h1 : 1820 ≤ N) (h2 : N ≤ 1831) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1824
  · by_cases h4 : N ≤ 1820
    · obtain rfl : N = 1820 := by omega
      exact cen1820
    · by_cases h6 : N ≤ 1822
      · obtain rfl : N = 1822 := by omega
        exact cen1822
      · obtain rfl : N = 1824 := by omega
        exact cen1824
  · by_cases h4 : N ≤ 1826
    · obtain rfl : N = 1826 := by omega
      exact cen1826
    · by_cases h6 : N ≤ 1828
      · obtain rfl : N = 1828 := by omega
        exact cen1828
      · obtain rfl : N = 1830 := by omega
        exact cen1830

end Kagey131.PaperD.T7
