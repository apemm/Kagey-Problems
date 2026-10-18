import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1970, …, 1979` (generated)

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

/-! ### `N = 1970` -/

def pL1970 : Prm := ⟨81, 38, 40, 1972, 11, 18446744073709551616, 99562497867209781, 99562497867209781⟩
def pH1970 : Prm := ⟨81, 38, 40, 1972, 11, 18446744073709551616, 99563597378837557, 99563597378837557⟩
def pI1970 : Prm := ⟨68, 34, 31, 1972, 11, 18446744073709551616, 99562497867209781, 99563597378837557⟩
noncomputable def L1970_cp1 : Nat × Nat := t7val% (fastRun pL1970 1 1136 (init pL1970) (init pL1970))
theorem L1970_seg1 : segOK pL1970 1 1136 (init pL1970) (init pL1970) L1970_cp1.1 L1970_cp1.2 = true := by
  decide +kernel
noncomputable def L1970_cp2 : Nat × Nat := t7val% (fastRun pL1970 1 1607 (init pL1970) (init pL1970))
theorem L1970_seg2 : segOK pL1970 1137 471 L1970_cp1.1 L1970_cp1.2 L1970_cp2.1 L1970_cp2.2 = true := by
  decide +kernel
theorem L1970_fin : (prmOK pL1970 1970 && ptTest pL1970 (runFrom pL1970 (fmask pL1970) (cmask pL1970) (hmask pL1970) 1608 362 (true, L1970_cp2.1, L1970_cp2.2)) 1970 985 false) = true := by
  decide +kernel
theorem L1970_ok : RunOK pL1970 1970 (runFrom pL1970 (fmask pL1970) (cmask pL1970) (hmask pL1970) 1608 362 (true, L1970_cp2.1, L1970_cp2.2)) ∧ ptTest pL1970 (runFrom pL1970 (fmask pL1970) (cmask pL1970) (hmask pL1970) 1608 362 (true, L1970_cp2.1, L1970_cp2.2)) 1970 985 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1970_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1970_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1970_fin) true) L1970_seg1) L1970_seg2) (by decide) rfl L1970_fin ptTest_fst
noncomputable def H1970_cp1 : Nat × Nat := t7val% (fastRun pH1970 1 1136 (init pH1970) (init pH1970))
theorem H1970_seg1 : segOK pH1970 1 1136 (init pH1970) (init pH1970) H1970_cp1.1 H1970_cp1.2 = true := by
  decide +kernel
noncomputable def H1970_cp2 : Nat × Nat := t7val% (fastRun pH1970 1 1607 (init pH1970) (init pH1970))
theorem H1970_seg2 : segOK pH1970 1137 471 H1970_cp1.1 H1970_cp1.2 H1970_cp2.1 H1970_cp2.2 = true := by
  decide +kernel
theorem H1970_fin : (prmOK pH1970 1970 && ptTest pH1970 (runFrom pH1970 (fmask pH1970) (cmask pH1970) (hmask pH1970) 1608 362 (true, H1970_cp2.1, H1970_cp2.2)) 1970 985 true) = true := by
  decide +kernel
theorem H1970_ok : RunOK pH1970 1970 (runFrom pH1970 (fmask pH1970) (cmask pH1970) (hmask pH1970) 1608 362 (true, H1970_cp2.1, H1970_cp2.2)) ∧ ptTest pH1970 (runFrom pH1970 (fmask pH1970) (cmask pH1970) (hmask pH1970) 1608 362 (true, H1970_cp2.1, H1970_cp2.2)) 1970 985 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1970_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1970_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1970_fin) true) H1970_seg1) H1970_seg2) (by decide) rfl H1970_fin ptTest_fst
noncomputable def I1970_cp1 : Nat × Nat := t7val% (fastRun pI1970 1 1136 (init pI1970) (init pI1970))
theorem I1970_seg1 : segOK pI1970 1 1136 (init pI1970) (init pI1970) I1970_cp1.1 I1970_cp1.2 = true := by
  decide +kernel
noncomputable def I1970_cp2 : Nat × Nat := t7val% (fastRun pI1970 1 1607 (init pI1970) (init pI1970))
theorem I1970_seg2 : segOK pI1970 1137 471 I1970_cp1.1 I1970_cp1.2 I1970_cp2.1 I1970_cp2.2 = true := by
  decide +kernel
theorem I1970_fin : (prmOK pI1970 1970 && intTest pI1970 (runFrom pI1970 (fmask pI1970) (cmask pI1970) (hmask pI1970) 1608 362 (true, I1970_cp2.1, I1970_cp2.2)) 1970 22 true) = true := by
  decide +kernel
theorem I1970_ok : RunOK pI1970 1970 (runFrom pI1970 (fmask pI1970) (cmask pI1970) (hmask pI1970) 1608 362 (true, I1970_cp2.1, I1970_cp2.2)) ∧ intTest pI1970 (runFrom pI1970 (fmask pI1970) (cmask pI1970) (hmask pI1970) 1608 362 (true, I1970_cp2.1, I1970_cp2.2)) 1970 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1970_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1970_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1970_fin) true) I1970_seg1) I1970_seg2) (by decide) rfl I1970_fin intTest_fst
theorem link1970 : linkOK pL1970 pH1970 pI1970 = true := by decide +kernel
theorem cvx1970 : ConvexBetweenHumps 1970 :=
  cvx_of L1970_ok H1970_ok I1970_ok link1970 (by decide)
theorem cenlink1970 : cenLinkOK pI1970 1970 = true := by decide +kernel
theorem cen1970 : CenterUniqueMin 1970 ∧ DipHyp 1970 ∧ OnePointHyps 1970 :=
  cen_of L1970_ok H1970_ok I1970_ok link1970 cenlink1970

/-! ### `N = 1971` -/

def pL1971 : Prm := ⟨81, 38, 40, 1973, 11, 18446744073709551616, 99520928927482718, 99520928927482718⟩
def pH1971 : Prm := ⟨81, 38, 40, 1973, 11, 18446744073709551616, 99522028439110494, 99522028439110494⟩
def pI1971 : Prm := ⟨68, 34, 31, 1973, 11, 18446744073709551616, 99520928927482718, 99522028439110494⟩
noncomputable def L1971_cp1 : Nat × Nat := t7val% (fastRun pL1971 1 1137 (init pL1971) (init pL1971))
theorem L1971_seg1 : segOK pL1971 1 1137 (init pL1971) (init pL1971) L1971_cp1.1 L1971_cp1.2 = true := by
  decide +kernel
noncomputable def L1971_cp2 : Nat × Nat := t7val% (fastRun pL1971 1 1608 (init pL1971) (init pL1971))
theorem L1971_seg2 : segOK pL1971 1138 471 L1971_cp1.1 L1971_cp1.2 L1971_cp2.1 L1971_cp2.2 = true := by
  decide +kernel
theorem L1971_fin : (prmOK pL1971 1971 && ptTest pL1971 (runFrom pL1971 (fmask pL1971) (cmask pL1971) (hmask pL1971) 1609 362 (true, L1971_cp2.1, L1971_cp2.2)) 1971 986 false) = true := by
  decide +kernel
theorem L1971_ok : RunOK pL1971 1971 (runFrom pL1971 (fmask pL1971) (cmask pL1971) (hmask pL1971) 1609 362 (true, L1971_cp2.1, L1971_cp2.2)) ∧ ptTest pL1971 (runFrom pL1971 (fmask pL1971) (cmask pL1971) (hmask pL1971) 1609 362 (true, L1971_cp2.1, L1971_cp2.2)) 1971 986 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1971_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1971_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1971_fin) true) L1971_seg1) L1971_seg2) (by decide) rfl L1971_fin ptTest_fst
noncomputable def H1971_cp1 : Nat × Nat := t7val% (fastRun pH1971 1 1137 (init pH1971) (init pH1971))
theorem H1971_seg1 : segOK pH1971 1 1137 (init pH1971) (init pH1971) H1971_cp1.1 H1971_cp1.2 = true := by
  decide +kernel
noncomputable def H1971_cp2 : Nat × Nat := t7val% (fastRun pH1971 1 1608 (init pH1971) (init pH1971))
theorem H1971_seg2 : segOK pH1971 1138 471 H1971_cp1.1 H1971_cp1.2 H1971_cp2.1 H1971_cp2.2 = true := by
  decide +kernel
theorem H1971_fin : (prmOK pH1971 1971 && ptTest pH1971 (runFrom pH1971 (fmask pH1971) (cmask pH1971) (hmask pH1971) 1609 362 (true, H1971_cp2.1, H1971_cp2.2)) 1971 986 true) = true := by
  decide +kernel
theorem H1971_ok : RunOK pH1971 1971 (runFrom pH1971 (fmask pH1971) (cmask pH1971) (hmask pH1971) 1609 362 (true, H1971_cp2.1, H1971_cp2.2)) ∧ ptTest pH1971 (runFrom pH1971 (fmask pH1971) (cmask pH1971) (hmask pH1971) 1609 362 (true, H1971_cp2.1, H1971_cp2.2)) 1971 986 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1971_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1971_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1971_fin) true) H1971_seg1) H1971_seg2) (by decide) rfl H1971_fin ptTest_fst
noncomputable def I1971_cp1 : Nat × Nat := t7val% (fastRun pI1971 1 1137 (init pI1971) (init pI1971))
theorem I1971_seg1 : segOK pI1971 1 1137 (init pI1971) (init pI1971) I1971_cp1.1 I1971_cp1.2 = true := by
  decide +kernel
noncomputable def I1971_cp2 : Nat × Nat := t7val% (fastRun pI1971 1 1608 (init pI1971) (init pI1971))
theorem I1971_seg2 : segOK pI1971 1138 471 I1971_cp1.1 I1971_cp1.2 I1971_cp2.1 I1971_cp2.2 = true := by
  decide +kernel
theorem I1971_fin : (prmOK pI1971 1971 && intTest pI1971 (runFrom pI1971 (fmask pI1971) (cmask pI1971) (hmask pI1971) 1609 362 (true, I1971_cp2.1, I1971_cp2.2)) 1971 22 false) = true := by
  decide +kernel
theorem I1971_ok : RunOK pI1971 1971 (runFrom pI1971 (fmask pI1971) (cmask pI1971) (hmask pI1971) 1609 362 (true, I1971_cp2.1, I1971_cp2.2)) ∧ intTest pI1971 (runFrom pI1971 (fmask pI1971) (cmask pI1971) (hmask pI1971) 1609 362 (true, I1971_cp2.1, I1971_cp2.2)) 1971 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1971_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1971_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1971_fin) true) I1971_seg1) I1971_seg2) (by decide) rfl I1971_fin intTest_fst
theorem link1971 : linkOK pL1971 pH1971 pI1971 = true := by decide +kernel
theorem cvx1971 : ConvexBetweenHumps 1971 :=
  cvx_of L1971_ok H1971_ok I1971_ok link1971 (by decide)

/-! ### `N = 1972` -/

def pL1972 : Prm := ⟨81, 38, 40, 1974, 11, 18446744073709551616, 99479412193461784, 99479412193461784⟩
def pH1972 : Prm := ⟨81, 38, 40, 1974, 11, 18446744073709551616, 99480511705089560, 99480511705089560⟩
def pI1972 : Prm := ⟨68, 34, 31, 1974, 11, 18446744073709551616, 99479412193461784, 99480511705089560⟩
noncomputable def L1972_cp1 : Nat × Nat := t7val% (fastRun pL1972 1 1138 (init pL1972) (init pL1972))
theorem L1972_seg1 : segOK pL1972 1 1138 (init pL1972) (init pL1972) L1972_cp1.1 L1972_cp1.2 = true := by
  decide +kernel
noncomputable def L1972_cp2 : Nat × Nat := t7val% (fastRun pL1972 1 1609 (init pL1972) (init pL1972))
theorem L1972_seg2 : segOK pL1972 1139 471 L1972_cp1.1 L1972_cp1.2 L1972_cp2.1 L1972_cp2.2 = true := by
  decide +kernel
theorem L1972_fin : (prmOK pL1972 1972 && ptTest pL1972 (runFrom pL1972 (fmask pL1972) (cmask pL1972) (hmask pL1972) 1610 362 (true, L1972_cp2.1, L1972_cp2.2)) 1972 986 false) = true := by
  decide +kernel
theorem L1972_ok : RunOK pL1972 1972 (runFrom pL1972 (fmask pL1972) (cmask pL1972) (hmask pL1972) 1610 362 (true, L1972_cp2.1, L1972_cp2.2)) ∧ ptTest pL1972 (runFrom pL1972 (fmask pL1972) (cmask pL1972) (hmask pL1972) 1610 362 (true, L1972_cp2.1, L1972_cp2.2)) 1972 986 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1972_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1972_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1972_fin) true) L1972_seg1) L1972_seg2) (by decide) rfl L1972_fin ptTest_fst
noncomputable def H1972_cp1 : Nat × Nat := t7val% (fastRun pH1972 1 1138 (init pH1972) (init pH1972))
theorem H1972_seg1 : segOK pH1972 1 1138 (init pH1972) (init pH1972) H1972_cp1.1 H1972_cp1.2 = true := by
  decide +kernel
noncomputable def H1972_cp2 : Nat × Nat := t7val% (fastRun pH1972 1 1609 (init pH1972) (init pH1972))
theorem H1972_seg2 : segOK pH1972 1139 471 H1972_cp1.1 H1972_cp1.2 H1972_cp2.1 H1972_cp2.2 = true := by
  decide +kernel
theorem H1972_fin : (prmOK pH1972 1972 && ptTest pH1972 (runFrom pH1972 (fmask pH1972) (cmask pH1972) (hmask pH1972) 1610 362 (true, H1972_cp2.1, H1972_cp2.2)) 1972 986 true) = true := by
  decide +kernel
theorem H1972_ok : RunOK pH1972 1972 (runFrom pH1972 (fmask pH1972) (cmask pH1972) (hmask pH1972) 1610 362 (true, H1972_cp2.1, H1972_cp2.2)) ∧ ptTest pH1972 (runFrom pH1972 (fmask pH1972) (cmask pH1972) (hmask pH1972) 1610 362 (true, H1972_cp2.1, H1972_cp2.2)) 1972 986 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1972_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1972_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1972_fin) true) H1972_seg1) H1972_seg2) (by decide) rfl H1972_fin ptTest_fst
noncomputable def I1972_cp1 : Nat × Nat := t7val% (fastRun pI1972 1 1138 (init pI1972) (init pI1972))
theorem I1972_seg1 : segOK pI1972 1 1138 (init pI1972) (init pI1972) I1972_cp1.1 I1972_cp1.2 = true := by
  decide +kernel
noncomputable def I1972_cp2 : Nat × Nat := t7val% (fastRun pI1972 1 1609 (init pI1972) (init pI1972))
theorem I1972_seg2 : segOK pI1972 1139 471 I1972_cp1.1 I1972_cp1.2 I1972_cp2.1 I1972_cp2.2 = true := by
  decide +kernel
theorem I1972_fin : (prmOK pI1972 1972 && intTest pI1972 (runFrom pI1972 (fmask pI1972) (cmask pI1972) (hmask pI1972) 1610 362 (true, I1972_cp2.1, I1972_cp2.2)) 1972 22 true) = true := by
  decide +kernel
theorem I1972_ok : RunOK pI1972 1972 (runFrom pI1972 (fmask pI1972) (cmask pI1972) (hmask pI1972) 1610 362 (true, I1972_cp2.1, I1972_cp2.2)) ∧ intTest pI1972 (runFrom pI1972 (fmask pI1972) (cmask pI1972) (hmask pI1972) 1610 362 (true, I1972_cp2.1, I1972_cp2.2)) 1972 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1972_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1972_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1972_fin) true) I1972_seg1) I1972_seg2) (by decide) rfl I1972_fin intTest_fst
theorem link1972 : linkOK pL1972 pH1972 pI1972 = true := by decide +kernel
theorem cvx1972 : ConvexBetweenHumps 1972 :=
  cvx_of L1972_ok H1972_ok I1972_ok link1972 (by decide)
theorem cenlink1972 : cenLinkOK pI1972 1972 = true := by decide +kernel
theorem cen1972 : CenterUniqueMin 1972 ∧ DipHyp 1972 ∧ OnePointHyps 1972 :=
  cen_of L1972_ok H1972_ok I1972_ok link1972 cenlink1972

/-! ### `N = 1973` -/

def pL1973 : Prm := ⟨81, 38, 40, 1975, 11, 18446744073709551616, 99437918437793625, 99437918437793625⟩
def pH1973 : Prm := ⟨81, 38, 40, 1975, 11, 18446744073709551616, 99439017949421401, 99439017949421401⟩
def pI1973 : Prm := ⟨68, 34, 31, 1975, 11, 18446744073709551616, 99437918437793625, 99439017949421401⟩
noncomputable def L1973_cp1 : Nat × Nat := t7val% (fastRun pL1973 1 1138 (init pL1973) (init pL1973))
theorem L1973_seg1 : segOK pL1973 1 1138 (init pL1973) (init pL1973) L1973_cp1.1 L1973_cp1.2 = true := by
  decide +kernel
noncomputable def L1973_cp2 : Nat × Nat := t7val% (fastRun pL1973 1 1610 (init pL1973) (init pL1973))
theorem L1973_seg2 : segOK pL1973 1139 472 L1973_cp1.1 L1973_cp1.2 L1973_cp2.1 L1973_cp2.2 = true := by
  decide +kernel
theorem L1973_fin : (prmOK pL1973 1973 && ptTest pL1973 (runFrom pL1973 (fmask pL1973) (cmask pL1973) (hmask pL1973) 1611 362 (true, L1973_cp2.1, L1973_cp2.2)) 1973 987 false) = true := by
  decide +kernel
theorem L1973_ok : RunOK pL1973 1973 (runFrom pL1973 (fmask pL1973) (cmask pL1973) (hmask pL1973) 1611 362 (true, L1973_cp2.1, L1973_cp2.2)) ∧ ptTest pL1973 (runFrom pL1973 (fmask pL1973) (cmask pL1973) (hmask pL1973) 1611 362 (true, L1973_cp2.1, L1973_cp2.2)) 1973 987 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1973_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1973_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1973_fin) true) L1973_seg1) L1973_seg2) (by decide) rfl L1973_fin ptTest_fst
noncomputable def H1973_cp1 : Nat × Nat := t7val% (fastRun pH1973 1 1138 (init pH1973) (init pH1973))
theorem H1973_seg1 : segOK pH1973 1 1138 (init pH1973) (init pH1973) H1973_cp1.1 H1973_cp1.2 = true := by
  decide +kernel
noncomputable def H1973_cp2 : Nat × Nat := t7val% (fastRun pH1973 1 1610 (init pH1973) (init pH1973))
theorem H1973_seg2 : segOK pH1973 1139 472 H1973_cp1.1 H1973_cp1.2 H1973_cp2.1 H1973_cp2.2 = true := by
  decide +kernel
theorem H1973_fin : (prmOK pH1973 1973 && ptTest pH1973 (runFrom pH1973 (fmask pH1973) (cmask pH1973) (hmask pH1973) 1611 362 (true, H1973_cp2.1, H1973_cp2.2)) 1973 987 true) = true := by
  decide +kernel
theorem H1973_ok : RunOK pH1973 1973 (runFrom pH1973 (fmask pH1973) (cmask pH1973) (hmask pH1973) 1611 362 (true, H1973_cp2.1, H1973_cp2.2)) ∧ ptTest pH1973 (runFrom pH1973 (fmask pH1973) (cmask pH1973) (hmask pH1973) 1611 362 (true, H1973_cp2.1, H1973_cp2.2)) 1973 987 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1973_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1973_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1973_fin) true) H1973_seg1) H1973_seg2) (by decide) rfl H1973_fin ptTest_fst
noncomputable def I1973_cp1 : Nat × Nat := t7val% (fastRun pI1973 1 1138 (init pI1973) (init pI1973))
theorem I1973_seg1 : segOK pI1973 1 1138 (init pI1973) (init pI1973) I1973_cp1.1 I1973_cp1.2 = true := by
  decide +kernel
noncomputable def I1973_cp2 : Nat × Nat := t7val% (fastRun pI1973 1 1610 (init pI1973) (init pI1973))
theorem I1973_seg2 : segOK pI1973 1139 472 I1973_cp1.1 I1973_cp1.2 I1973_cp2.1 I1973_cp2.2 = true := by
  decide +kernel
theorem I1973_fin : (prmOK pI1973 1973 && intTest pI1973 (runFrom pI1973 (fmask pI1973) (cmask pI1973) (hmask pI1973) 1611 362 (true, I1973_cp2.1, I1973_cp2.2)) 1973 22 false) = true := by
  decide +kernel
theorem I1973_ok : RunOK pI1973 1973 (runFrom pI1973 (fmask pI1973) (cmask pI1973) (hmask pI1973) 1611 362 (true, I1973_cp2.1, I1973_cp2.2)) ∧ intTest pI1973 (runFrom pI1973 (fmask pI1973) (cmask pI1973) (hmask pI1973) 1611 362 (true, I1973_cp2.1, I1973_cp2.2)) 1973 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1973_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1973_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1973_fin) true) I1973_seg1) I1973_seg2) (by decide) rfl I1973_fin intTest_fst
theorem link1973 : linkOK pL1973 pH1973 pI1973 = true := by decide +kernel
theorem cvx1973 : ConvexBetweenHumps 1973 :=
  cvx_of L1973_ok H1973_ok I1973_ok link1973 (by decide)

/-! ### `N = 1974` -/

def pL1974 : Prm := ⟨81, 38, 40, 1976, 11, 18446744073709551616, 99396476737785779, 99396476737785779⟩
def pH1974 : Prm := ⟨81, 38, 40, 1976, 11, 18446744073709551616, 99397576249413555, 99397576249413555⟩
def pI1974 : Prm := ⟨68, 34, 31, 1976, 11, 18446744073709551616, 99396476737785779, 99397576249413555⟩
noncomputable def L1974_cp1 : Nat × Nat := t7val% (fastRun pL1974 1 1139 (init pL1974) (init pL1974))
theorem L1974_seg1 : segOK pL1974 1 1139 (init pL1974) (init pL1974) L1974_cp1.1 L1974_cp1.2 = true := by
  decide +kernel
noncomputable def L1974_cp2 : Nat × Nat := t7val% (fastRun pL1974 1 1611 (init pL1974) (init pL1974))
theorem L1974_seg2 : segOK pL1974 1140 472 L1974_cp1.1 L1974_cp1.2 L1974_cp2.1 L1974_cp2.2 = true := by
  decide +kernel
theorem L1974_fin : (prmOK pL1974 1974 && ptTest pL1974 (runFrom pL1974 (fmask pL1974) (cmask pL1974) (hmask pL1974) 1612 362 (true, L1974_cp2.1, L1974_cp2.2)) 1974 987 false) = true := by
  decide +kernel
theorem L1974_ok : RunOK pL1974 1974 (runFrom pL1974 (fmask pL1974) (cmask pL1974) (hmask pL1974) 1612 362 (true, L1974_cp2.1, L1974_cp2.2)) ∧ ptTest pL1974 (runFrom pL1974 (fmask pL1974) (cmask pL1974) (hmask pL1974) 1612 362 (true, L1974_cp2.1, L1974_cp2.2)) 1974 987 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1974_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1974_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1974_fin) true) L1974_seg1) L1974_seg2) (by decide) rfl L1974_fin ptTest_fst
noncomputable def H1974_cp1 : Nat × Nat := t7val% (fastRun pH1974 1 1139 (init pH1974) (init pH1974))
theorem H1974_seg1 : segOK pH1974 1 1139 (init pH1974) (init pH1974) H1974_cp1.1 H1974_cp1.2 = true := by
  decide +kernel
noncomputable def H1974_cp2 : Nat × Nat := t7val% (fastRun pH1974 1 1611 (init pH1974) (init pH1974))
theorem H1974_seg2 : segOK pH1974 1140 472 H1974_cp1.1 H1974_cp1.2 H1974_cp2.1 H1974_cp2.2 = true := by
  decide +kernel
theorem H1974_fin : (prmOK pH1974 1974 && ptTest pH1974 (runFrom pH1974 (fmask pH1974) (cmask pH1974) (hmask pH1974) 1612 362 (true, H1974_cp2.1, H1974_cp2.2)) 1974 987 true) = true := by
  decide +kernel
theorem H1974_ok : RunOK pH1974 1974 (runFrom pH1974 (fmask pH1974) (cmask pH1974) (hmask pH1974) 1612 362 (true, H1974_cp2.1, H1974_cp2.2)) ∧ ptTest pH1974 (runFrom pH1974 (fmask pH1974) (cmask pH1974) (hmask pH1974) 1612 362 (true, H1974_cp2.1, H1974_cp2.2)) 1974 987 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1974_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1974_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1974_fin) true) H1974_seg1) H1974_seg2) (by decide) rfl H1974_fin ptTest_fst
noncomputable def I1974_cp1 : Nat × Nat := t7val% (fastRun pI1974 1 1139 (init pI1974) (init pI1974))
theorem I1974_seg1 : segOK pI1974 1 1139 (init pI1974) (init pI1974) I1974_cp1.1 I1974_cp1.2 = true := by
  decide +kernel
noncomputable def I1974_cp2 : Nat × Nat := t7val% (fastRun pI1974 1 1611 (init pI1974) (init pI1974))
theorem I1974_seg2 : segOK pI1974 1140 472 I1974_cp1.1 I1974_cp1.2 I1974_cp2.1 I1974_cp2.2 = true := by
  decide +kernel
theorem I1974_fin : (prmOK pI1974 1974 && intTest pI1974 (runFrom pI1974 (fmask pI1974) (cmask pI1974) (hmask pI1974) 1612 362 (true, I1974_cp2.1, I1974_cp2.2)) 1974 22 true) = true := by
  decide +kernel
theorem I1974_ok : RunOK pI1974 1974 (runFrom pI1974 (fmask pI1974) (cmask pI1974) (hmask pI1974) 1612 362 (true, I1974_cp2.1, I1974_cp2.2)) ∧ intTest pI1974 (runFrom pI1974 (fmask pI1974) (cmask pI1974) (hmask pI1974) 1612 362 (true, I1974_cp2.1, I1974_cp2.2)) 1974 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1974_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1974_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1974_fin) true) I1974_seg1) I1974_seg2) (by decide) rfl I1974_fin intTest_fst
theorem link1974 : linkOK pL1974 pH1974 pI1974 = true := by decide +kernel
theorem cvx1974 : ConvexBetweenHumps 1974 :=
  cvx_of L1974_ok H1974_ok I1974_ok link1974 (by decide)
theorem cenlink1974 : cenLinkOK pI1974 1974 = true := by decide +kernel
theorem cen1974 : CenterUniqueMin 1974 ∧ DipHyp 1974 ∧ OnePointHyps 1974 :=
  cen_of L1974_ok H1974_ok I1974_ok link1974 cenlink1974

/-! ### `N = 1975` -/

def pL1975 : Prm := ⟨81, 38, 40, 1977, 11, 18446744073709551616, 99355057956160343, 99355057956160343⟩
def pH1975 : Prm := ⟨81, 38, 40, 1977, 11, 18446744073709551616, 99356157467788119, 99356157467788119⟩
def pI1975 : Prm := ⟨68, 34, 31, 1977, 11, 18446744073709551616, 99355057956160343, 99356157467788119⟩
noncomputable def L1975_cp1 : Nat × Nat := t7val% (fastRun pL1975 1 1139 (init pL1975) (init pL1975))
theorem L1975_seg1 : segOK pL1975 1 1139 (init pL1975) (init pL1975) L1975_cp1.1 L1975_cp1.2 = true := by
  decide +kernel
noncomputable def L1975_cp2 : Nat × Nat := t7val% (fastRun pL1975 1 1612 (init pL1975) (init pL1975))
theorem L1975_seg2 : segOK pL1975 1140 473 L1975_cp1.1 L1975_cp1.2 L1975_cp2.1 L1975_cp2.2 = true := by
  decide +kernel
theorem L1975_fin : (prmOK pL1975 1975 && ptTest pL1975 (runFrom pL1975 (fmask pL1975) (cmask pL1975) (hmask pL1975) 1613 362 (true, L1975_cp2.1, L1975_cp2.2)) 1975 988 false) = true := by
  decide +kernel
theorem L1975_ok : RunOK pL1975 1975 (runFrom pL1975 (fmask pL1975) (cmask pL1975) (hmask pL1975) 1613 362 (true, L1975_cp2.1, L1975_cp2.2)) ∧ ptTest pL1975 (runFrom pL1975 (fmask pL1975) (cmask pL1975) (hmask pL1975) 1613 362 (true, L1975_cp2.1, L1975_cp2.2)) 1975 988 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1975_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1975_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1975_fin) true) L1975_seg1) L1975_seg2) (by decide) rfl L1975_fin ptTest_fst
noncomputable def H1975_cp1 : Nat × Nat := t7val% (fastRun pH1975 1 1139 (init pH1975) (init pH1975))
theorem H1975_seg1 : segOK pH1975 1 1139 (init pH1975) (init pH1975) H1975_cp1.1 H1975_cp1.2 = true := by
  decide +kernel
noncomputable def H1975_cp2 : Nat × Nat := t7val% (fastRun pH1975 1 1612 (init pH1975) (init pH1975))
theorem H1975_seg2 : segOK pH1975 1140 473 H1975_cp1.1 H1975_cp1.2 H1975_cp2.1 H1975_cp2.2 = true := by
  decide +kernel
theorem H1975_fin : (prmOK pH1975 1975 && ptTest pH1975 (runFrom pH1975 (fmask pH1975) (cmask pH1975) (hmask pH1975) 1613 362 (true, H1975_cp2.1, H1975_cp2.2)) 1975 988 true) = true := by
  decide +kernel
theorem H1975_ok : RunOK pH1975 1975 (runFrom pH1975 (fmask pH1975) (cmask pH1975) (hmask pH1975) 1613 362 (true, H1975_cp2.1, H1975_cp2.2)) ∧ ptTest pH1975 (runFrom pH1975 (fmask pH1975) (cmask pH1975) (hmask pH1975) 1613 362 (true, H1975_cp2.1, H1975_cp2.2)) 1975 988 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1975_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1975_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1975_fin) true) H1975_seg1) H1975_seg2) (by decide) rfl H1975_fin ptTest_fst
noncomputable def I1975_cp1 : Nat × Nat := t7val% (fastRun pI1975 1 1139 (init pI1975) (init pI1975))
theorem I1975_seg1 : segOK pI1975 1 1139 (init pI1975) (init pI1975) I1975_cp1.1 I1975_cp1.2 = true := by
  decide +kernel
noncomputable def I1975_cp2 : Nat × Nat := t7val% (fastRun pI1975 1 1612 (init pI1975) (init pI1975))
theorem I1975_seg2 : segOK pI1975 1140 473 I1975_cp1.1 I1975_cp1.2 I1975_cp2.1 I1975_cp2.2 = true := by
  decide +kernel
theorem I1975_fin : (prmOK pI1975 1975 && intTest pI1975 (runFrom pI1975 (fmask pI1975) (cmask pI1975) (hmask pI1975) 1613 362 (true, I1975_cp2.1, I1975_cp2.2)) 1975 22 false) = true := by
  decide +kernel
theorem I1975_ok : RunOK pI1975 1975 (runFrom pI1975 (fmask pI1975) (cmask pI1975) (hmask pI1975) 1613 362 (true, I1975_cp2.1, I1975_cp2.2)) ∧ intTest pI1975 (runFrom pI1975 (fmask pI1975) (cmask pI1975) (hmask pI1975) 1613 362 (true, I1975_cp2.1, I1975_cp2.2)) 1975 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1975_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1975_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1975_fin) true) I1975_seg1) I1975_seg2) (by decide) rfl I1975_fin intTest_fst
theorem link1975 : linkOK pL1975 pH1975 pI1975 = true := by decide +kernel
theorem cvx1975 : ConvexBetweenHumps 1975 :=
  cvx_of L1975_ok H1975_ok I1975_ok link1975 (by decide)

/-! ### `N = 1976` -/

def pL1976 : Prm := ⟨81, 38, 40, 1978, 11, 18446744073709551616, 99313691080758145, 99313691080758145⟩
def pH1976 : Prm := ⟨81, 38, 40, 1978, 11, 18446744073709551616, 99314790592385921, 99314790592385921⟩
def pI1976 : Prm := ⟨68, 34, 31, 1978, 11, 18446744073709551616, 99313691080758145, 99314790592385921⟩
noncomputable def L1976_cp1 : Nat × Nat := t7val% (fastRun pL1976 1 1140 (init pL1976) (init pL1976))
theorem L1976_seg1 : segOK pL1976 1 1140 (init pL1976) (init pL1976) L1976_cp1.1 L1976_cp1.2 = true := by
  decide +kernel
noncomputable def L1976_cp2 : Nat × Nat := t7val% (fastRun pL1976 1 1612 (init pL1976) (init pL1976))
theorem L1976_seg2 : segOK pL1976 1141 472 L1976_cp1.1 L1976_cp1.2 L1976_cp2.1 L1976_cp2.2 = true := by
  decide +kernel
theorem L1976_fin : (prmOK pL1976 1976 && ptTest pL1976 (runFrom pL1976 (fmask pL1976) (cmask pL1976) (hmask pL1976) 1613 363 (true, L1976_cp2.1, L1976_cp2.2)) 1976 988 false) = true := by
  decide +kernel
theorem L1976_ok : RunOK pL1976 1976 (runFrom pL1976 (fmask pL1976) (cmask pL1976) (hmask pL1976) 1613 363 (true, L1976_cp2.1, L1976_cp2.2)) ∧ ptTest pL1976 (runFrom pL1976 (fmask pL1976) (cmask pL1976) (hmask pL1976) 1613 363 (true, L1976_cp2.1, L1976_cp2.2)) 1976 988 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1976_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1976_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1976_fin) true) L1976_seg1) L1976_seg2) (by decide) rfl L1976_fin ptTest_fst
noncomputable def H1976_cp1 : Nat × Nat := t7val% (fastRun pH1976 1 1140 (init pH1976) (init pH1976))
theorem H1976_seg1 : segOK pH1976 1 1140 (init pH1976) (init pH1976) H1976_cp1.1 H1976_cp1.2 = true := by
  decide +kernel
noncomputable def H1976_cp2 : Nat × Nat := t7val% (fastRun pH1976 1 1612 (init pH1976) (init pH1976))
theorem H1976_seg2 : segOK pH1976 1141 472 H1976_cp1.1 H1976_cp1.2 H1976_cp2.1 H1976_cp2.2 = true := by
  decide +kernel
theorem H1976_fin : (prmOK pH1976 1976 && ptTest pH1976 (runFrom pH1976 (fmask pH1976) (cmask pH1976) (hmask pH1976) 1613 363 (true, H1976_cp2.1, H1976_cp2.2)) 1976 988 true) = true := by
  decide +kernel
theorem H1976_ok : RunOK pH1976 1976 (runFrom pH1976 (fmask pH1976) (cmask pH1976) (hmask pH1976) 1613 363 (true, H1976_cp2.1, H1976_cp2.2)) ∧ ptTest pH1976 (runFrom pH1976 (fmask pH1976) (cmask pH1976) (hmask pH1976) 1613 363 (true, H1976_cp2.1, H1976_cp2.2)) 1976 988 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1976_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1976_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1976_fin) true) H1976_seg1) H1976_seg2) (by decide) rfl H1976_fin ptTest_fst
noncomputable def I1976_cp1 : Nat × Nat := t7val% (fastRun pI1976 1 1140 (init pI1976) (init pI1976))
theorem I1976_seg1 : segOK pI1976 1 1140 (init pI1976) (init pI1976) I1976_cp1.1 I1976_cp1.2 = true := by
  decide +kernel
noncomputable def I1976_cp2 : Nat × Nat := t7val% (fastRun pI1976 1 1612 (init pI1976) (init pI1976))
theorem I1976_seg2 : segOK pI1976 1141 472 I1976_cp1.1 I1976_cp1.2 I1976_cp2.1 I1976_cp2.2 = true := by
  decide +kernel
theorem I1976_fin : (prmOK pI1976 1976 && intTest pI1976 (runFrom pI1976 (fmask pI1976) (cmask pI1976) (hmask pI1976) 1613 363 (true, I1976_cp2.1, I1976_cp2.2)) 1976 22 true) = true := by
  decide +kernel
theorem I1976_ok : RunOK pI1976 1976 (runFrom pI1976 (fmask pI1976) (cmask pI1976) (hmask pI1976) 1613 363 (true, I1976_cp2.1, I1976_cp2.2)) ∧ intTest pI1976 (runFrom pI1976 (fmask pI1976) (cmask pI1976) (hmask pI1976) 1613 363 (true, I1976_cp2.1, I1976_cp2.2)) 1976 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1976_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1976_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1976_fin) true) I1976_seg1) I1976_seg2) (by decide) rfl I1976_fin intTest_fst
theorem link1976 : linkOK pL1976 pH1976 pI1976 = true := by decide +kernel
theorem cvx1976 : ConvexBetweenHumps 1976 :=
  cvx_of L1976_ok H1976_ok I1976_ok link1976 (by decide)
theorem cenlink1976 : cenLinkOK pI1976 1976 = true := by decide +kernel
theorem cen1976 : CenterUniqueMin 1976 ∧ DipHyp 1976 ∧ OnePointHyps 1976 :=
  cen_of L1976_ok H1976_ok I1976_ok link1976 cenlink1976

/-! ### `N = 1977` -/

def pL1977 : Prm := ⟨81, 38, 40, 1979, 11, 18446744073709551616, 99272347064007801, 99272347064007801⟩
def pH1977 : Prm := ⟨81, 38, 40, 1979, 11, 18446744073709551616, 99273446575635577, 99273446575635577⟩
def pI1977 : Prm := ⟨68, 34, 31, 1979, 11, 18446744073709551616, 99272347064007801, 99273446575635577⟩
noncomputable def L1977_cp1 : Nat × Nat := t7val% (fastRun pL1977 1 1140 (init pL1977) (init pL1977))
theorem L1977_seg1 : segOK pL1977 1 1140 (init pL1977) (init pL1977) L1977_cp1.1 L1977_cp1.2 = true := by
  decide +kernel
noncomputable def L1977_cp2 : Nat × Nat := t7val% (fastRun pL1977 1 1613 (init pL1977) (init pL1977))
theorem L1977_seg2 : segOK pL1977 1141 473 L1977_cp1.1 L1977_cp1.2 L1977_cp2.1 L1977_cp2.2 = true := by
  decide +kernel
theorem L1977_fin : (prmOK pL1977 1977 && ptTest pL1977 (runFrom pL1977 (fmask pL1977) (cmask pL1977) (hmask pL1977) 1614 363 (true, L1977_cp2.1, L1977_cp2.2)) 1977 989 false) = true := by
  decide +kernel
theorem L1977_ok : RunOK pL1977 1977 (runFrom pL1977 (fmask pL1977) (cmask pL1977) (hmask pL1977) 1614 363 (true, L1977_cp2.1, L1977_cp2.2)) ∧ ptTest pL1977 (runFrom pL1977 (fmask pL1977) (cmask pL1977) (hmask pL1977) 1614 363 (true, L1977_cp2.1, L1977_cp2.2)) 1977 989 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1977_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1977_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1977_fin) true) L1977_seg1) L1977_seg2) (by decide) rfl L1977_fin ptTest_fst
noncomputable def H1977_cp1 : Nat × Nat := t7val% (fastRun pH1977 1 1140 (init pH1977) (init pH1977))
theorem H1977_seg1 : segOK pH1977 1 1140 (init pH1977) (init pH1977) H1977_cp1.1 H1977_cp1.2 = true := by
  decide +kernel
noncomputable def H1977_cp2 : Nat × Nat := t7val% (fastRun pH1977 1 1613 (init pH1977) (init pH1977))
theorem H1977_seg2 : segOK pH1977 1141 473 H1977_cp1.1 H1977_cp1.2 H1977_cp2.1 H1977_cp2.2 = true := by
  decide +kernel
theorem H1977_fin : (prmOK pH1977 1977 && ptTest pH1977 (runFrom pH1977 (fmask pH1977) (cmask pH1977) (hmask pH1977) 1614 363 (true, H1977_cp2.1, H1977_cp2.2)) 1977 989 true) = true := by
  decide +kernel
theorem H1977_ok : RunOK pH1977 1977 (runFrom pH1977 (fmask pH1977) (cmask pH1977) (hmask pH1977) 1614 363 (true, H1977_cp2.1, H1977_cp2.2)) ∧ ptTest pH1977 (runFrom pH1977 (fmask pH1977) (cmask pH1977) (hmask pH1977) 1614 363 (true, H1977_cp2.1, H1977_cp2.2)) 1977 989 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1977_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1977_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1977_fin) true) H1977_seg1) H1977_seg2) (by decide) rfl H1977_fin ptTest_fst
noncomputable def I1977_cp1 : Nat × Nat := t7val% (fastRun pI1977 1 1140 (init pI1977) (init pI1977))
theorem I1977_seg1 : segOK pI1977 1 1140 (init pI1977) (init pI1977) I1977_cp1.1 I1977_cp1.2 = true := by
  decide +kernel
noncomputable def I1977_cp2 : Nat × Nat := t7val% (fastRun pI1977 1 1613 (init pI1977) (init pI1977))
theorem I1977_seg2 : segOK pI1977 1141 473 I1977_cp1.1 I1977_cp1.2 I1977_cp2.1 I1977_cp2.2 = true := by
  decide +kernel
theorem I1977_fin : (prmOK pI1977 1977 && intTest pI1977 (runFrom pI1977 (fmask pI1977) (cmask pI1977) (hmask pI1977) 1614 363 (true, I1977_cp2.1, I1977_cp2.2)) 1977 22 false) = true := by
  decide +kernel
theorem I1977_ok : RunOK pI1977 1977 (runFrom pI1977 (fmask pI1977) (cmask pI1977) (hmask pI1977) 1614 363 (true, I1977_cp2.1, I1977_cp2.2)) ∧ intTest pI1977 (runFrom pI1977 (fmask pI1977) (cmask pI1977) (hmask pI1977) 1614 363 (true, I1977_cp2.1, I1977_cp2.2)) 1977 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1977_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1977_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1977_fin) true) I1977_seg1) I1977_seg2) (by decide) rfl I1977_fin intTest_fst
theorem link1977 : linkOK pL1977 pH1977 pI1977 = true := by decide +kernel
theorem cvx1977 : ConvexBetweenHumps 1977 :=
  cvx_of L1977_ok H1977_ok I1977_ok link1977 (by decide)

/-! ### `N = 1978` -/

def pL1978 : Prm := ⟨81, 38, 40, 1980, 11, 18446744073709551616, 99231054804597024, 99231054804597024⟩
def pH1978 : Prm := ⟨81, 38, 40, 1980, 11, 18446744073709551616, 99232154316224800, 99232154316224800⟩
def pI1978 : Prm := ⟨68, 34, 31, 1980, 11, 18446744073709551616, 99231054804597024, 99232154316224800⟩
noncomputable def L1978_cp1 : Nat × Nat := t7val% (fastRun pL1978 1 1141 (init pL1978) (init pL1978))
theorem L1978_seg1 : segOK pL1978 1 1141 (init pL1978) (init pL1978) L1978_cp1.1 L1978_cp1.2 = true := by
  decide +kernel
noncomputable def L1978_cp2 : Nat × Nat := t7val% (fastRun pL1978 1 1614 (init pL1978) (init pL1978))
theorem L1978_seg2 : segOK pL1978 1142 473 L1978_cp1.1 L1978_cp1.2 L1978_cp2.1 L1978_cp2.2 = true := by
  decide +kernel
theorem L1978_fin : (prmOK pL1978 1978 && ptTest pL1978 (runFrom pL1978 (fmask pL1978) (cmask pL1978) (hmask pL1978) 1615 363 (true, L1978_cp2.1, L1978_cp2.2)) 1978 989 false) = true := by
  decide +kernel
theorem L1978_ok : RunOK pL1978 1978 (runFrom pL1978 (fmask pL1978) (cmask pL1978) (hmask pL1978) 1615 363 (true, L1978_cp2.1, L1978_cp2.2)) ∧ ptTest pL1978 (runFrom pL1978 (fmask pL1978) (cmask pL1978) (hmask pL1978) 1615 363 (true, L1978_cp2.1, L1978_cp2.2)) 1978 989 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1978_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1978_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1978_fin) true) L1978_seg1) L1978_seg2) (by decide) rfl L1978_fin ptTest_fst
noncomputable def H1978_cp1 : Nat × Nat := t7val% (fastRun pH1978 1 1141 (init pH1978) (init pH1978))
theorem H1978_seg1 : segOK pH1978 1 1141 (init pH1978) (init pH1978) H1978_cp1.1 H1978_cp1.2 = true := by
  decide +kernel
noncomputable def H1978_cp2 : Nat × Nat := t7val% (fastRun pH1978 1 1614 (init pH1978) (init pH1978))
theorem H1978_seg2 : segOK pH1978 1142 473 H1978_cp1.1 H1978_cp1.2 H1978_cp2.1 H1978_cp2.2 = true := by
  decide +kernel
theorem H1978_fin : (prmOK pH1978 1978 && ptTest pH1978 (runFrom pH1978 (fmask pH1978) (cmask pH1978) (hmask pH1978) 1615 363 (true, H1978_cp2.1, H1978_cp2.2)) 1978 989 true) = true := by
  decide +kernel
theorem H1978_ok : RunOK pH1978 1978 (runFrom pH1978 (fmask pH1978) (cmask pH1978) (hmask pH1978) 1615 363 (true, H1978_cp2.1, H1978_cp2.2)) ∧ ptTest pH1978 (runFrom pH1978 (fmask pH1978) (cmask pH1978) (hmask pH1978) 1615 363 (true, H1978_cp2.1, H1978_cp2.2)) 1978 989 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1978_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1978_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1978_fin) true) H1978_seg1) H1978_seg2) (by decide) rfl H1978_fin ptTest_fst
noncomputable def I1978_cp1 : Nat × Nat := t7val% (fastRun pI1978 1 1141 (init pI1978) (init pI1978))
theorem I1978_seg1 : segOK pI1978 1 1141 (init pI1978) (init pI1978) I1978_cp1.1 I1978_cp1.2 = true := by
  decide +kernel
noncomputable def I1978_cp2 : Nat × Nat := t7val% (fastRun pI1978 1 1614 (init pI1978) (init pI1978))
theorem I1978_seg2 : segOK pI1978 1142 473 I1978_cp1.1 I1978_cp1.2 I1978_cp2.1 I1978_cp2.2 = true := by
  decide +kernel
theorem I1978_fin : (prmOK pI1978 1978 && intTest pI1978 (runFrom pI1978 (fmask pI1978) (cmask pI1978) (hmask pI1978) 1615 363 (true, I1978_cp2.1, I1978_cp2.2)) 1978 22 true) = true := by
  decide +kernel
theorem I1978_ok : RunOK pI1978 1978 (runFrom pI1978 (fmask pI1978) (cmask pI1978) (hmask pI1978) 1615 363 (true, I1978_cp2.1, I1978_cp2.2)) ∧ intTest pI1978 (runFrom pI1978 (fmask pI1978) (cmask pI1978) (hmask pI1978) 1615 363 (true, I1978_cp2.1, I1978_cp2.2)) 1978 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1978_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1978_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1978_fin) true) I1978_seg1) I1978_seg2) (by decide) rfl I1978_fin intTest_fst
theorem link1978 : linkOK pL1978 pH1978 pI1978 = true := by decide +kernel
theorem cvx1978 : ConvexBetweenHumps 1978 :=
  cvx_of L1978_ok H1978_ok I1978_ok link1978 (by decide)
theorem cenlink1978 : cenLinkOK pI1978 1978 = true := by decide +kernel
theorem cen1978 : CenterUniqueMin 1978 ∧ DipHyp 1978 ∧ OnePointHyps 1978 :=
  cen_of L1978_ok H1978_ok I1978_ok link1978 cenlink1978

/-! ### `N = 1979` -/

def pL1979 : Prm := ⟨81, 38, 40, 1981, 11, 18446744073709551616, 99189785344310457, 99189785344310457⟩
def pH1979 : Prm := ⟨81, 38, 40, 1981, 11, 18446744073709551616, 99190884855938233, 99190884855938233⟩
def pI1979 : Prm := ⟨68, 34, 31, 1981, 11, 18446744073709551616, 99189785344310457, 99190884855938233⟩
noncomputable def L1979_cp1 : Nat × Nat := t7val% (fastRun pL1979 1 1142 (init pL1979) (init pL1979))
theorem L1979_seg1 : segOK pL1979 1 1142 (init pL1979) (init pL1979) L1979_cp1.1 L1979_cp1.2 = true := by
  decide +kernel
noncomputable def L1979_cp2 : Nat × Nat := t7val% (fastRun pL1979 1 1615 (init pL1979) (init pL1979))
theorem L1979_seg2 : segOK pL1979 1143 473 L1979_cp1.1 L1979_cp1.2 L1979_cp2.1 L1979_cp2.2 = true := by
  decide +kernel
theorem L1979_fin : (prmOK pL1979 1979 && ptTest pL1979 (runFrom pL1979 (fmask pL1979) (cmask pL1979) (hmask pL1979) 1616 363 (true, L1979_cp2.1, L1979_cp2.2)) 1979 990 false) = true := by
  decide +kernel
theorem L1979_ok : RunOK pL1979 1979 (runFrom pL1979 (fmask pL1979) (cmask pL1979) (hmask pL1979) 1616 363 (true, L1979_cp2.1, L1979_cp2.2)) ∧ ptTest pL1979 (runFrom pL1979 (fmask pL1979) (cmask pL1979) (hmask pL1979) 1616 363 (true, L1979_cp2.1, L1979_cp2.2)) 1979 990 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1979_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1979_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1979_fin) true) L1979_seg1) L1979_seg2) (by decide) rfl L1979_fin ptTest_fst
noncomputable def H1979_cp1 : Nat × Nat := t7val% (fastRun pH1979 1 1142 (init pH1979) (init pH1979))
theorem H1979_seg1 : segOK pH1979 1 1142 (init pH1979) (init pH1979) H1979_cp1.1 H1979_cp1.2 = true := by
  decide +kernel
noncomputable def H1979_cp2 : Nat × Nat := t7val% (fastRun pH1979 1 1615 (init pH1979) (init pH1979))
theorem H1979_seg2 : segOK pH1979 1143 473 H1979_cp1.1 H1979_cp1.2 H1979_cp2.1 H1979_cp2.2 = true := by
  decide +kernel
theorem H1979_fin : (prmOK pH1979 1979 && ptTest pH1979 (runFrom pH1979 (fmask pH1979) (cmask pH1979) (hmask pH1979) 1616 363 (true, H1979_cp2.1, H1979_cp2.2)) 1979 990 true) = true := by
  decide +kernel
theorem H1979_ok : RunOK pH1979 1979 (runFrom pH1979 (fmask pH1979) (cmask pH1979) (hmask pH1979) 1616 363 (true, H1979_cp2.1, H1979_cp2.2)) ∧ ptTest pH1979 (runFrom pH1979 (fmask pH1979) (cmask pH1979) (hmask pH1979) 1616 363 (true, H1979_cp2.1, H1979_cp2.2)) 1979 990 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1979_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1979_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1979_fin) true) H1979_seg1) H1979_seg2) (by decide) rfl H1979_fin ptTest_fst
noncomputable def I1979_cp1 : Nat × Nat := t7val% (fastRun pI1979 1 1142 (init pI1979) (init pI1979))
theorem I1979_seg1 : segOK pI1979 1 1142 (init pI1979) (init pI1979) I1979_cp1.1 I1979_cp1.2 = true := by
  decide +kernel
noncomputable def I1979_cp2 : Nat × Nat := t7val% (fastRun pI1979 1 1615 (init pI1979) (init pI1979))
theorem I1979_seg2 : segOK pI1979 1143 473 I1979_cp1.1 I1979_cp1.2 I1979_cp2.1 I1979_cp2.2 = true := by
  decide +kernel
theorem I1979_fin : (prmOK pI1979 1979 && intTest pI1979 (runFrom pI1979 (fmask pI1979) (cmask pI1979) (hmask pI1979) 1616 363 (true, I1979_cp2.1, I1979_cp2.2)) 1979 22 false) = true := by
  decide +kernel
theorem I1979_ok : RunOK pI1979 1979 (runFrom pI1979 (fmask pI1979) (cmask pI1979) (hmask pI1979) 1616 363 (true, I1979_cp2.1, I1979_cp2.2)) ∧ intTest pI1979 (runFrom pI1979 (fmask pI1979) (cmask pI1979) (hmask pI1979) 1616 363 (true, I1979_cp2.1, I1979_cp2.2)) 1979 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1979_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1979_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1979_fin) true) I1979_seg1) I1979_seg2) (by decide) rfl I1979_fin intTest_fst
theorem link1979 : linkOK pL1979 pH1979 pI1979 = true := by decide +kernel
theorem cvx1979 : ConvexBetweenHumps 1979 :=
  cvx_of L1979_ok H1979_ok I1979_ok link1979 (by decide)

/-! ### The range -/

theorem cvx_1970_1979 {N : ℕ} (h1 : 1970 ≤ N) (h2 : N ≤ 1979) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1974
  · by_cases h4 : N ≤ 1971
    · by_cases h6 : N ≤ 1970
      · obtain rfl : N = 1970 := by omega
        exact cvx1970
      · obtain rfl : N = 1971 := by omega
        exact cvx1971
    · by_cases h6 : N ≤ 1972
      · obtain rfl : N = 1972 := by omega
        exact cvx1972
      · by_cases h8 : N ≤ 1973
        · obtain rfl : N = 1973 := by omega
          exact cvx1973
        · obtain rfl : N = 1974 := by omega
          exact cvx1974
  · by_cases h4 : N ≤ 1976
    · by_cases h6 : N ≤ 1975
      · obtain rfl : N = 1975 := by omega
        exact cvx1975
      · obtain rfl : N = 1976 := by omega
        exact cvx1976
    · by_cases h6 : N ≤ 1977
      · obtain rfl : N = 1977 := by omega
        exact cvx1977
      · by_cases h8 : N ≤ 1978
        · obtain rfl : N = 1978 := by omega
          exact cvx1978
        · obtain rfl : N = 1979 := by omega
          exact cvx1979

theorem cen_1970_1979 {N : ℕ} (h1 : 1970 ≤ N) (h2 : N ≤ 1979) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1972
  · by_cases h4 : N ≤ 1970
    · obtain rfl : N = 1970 := by omega
      exact cen1970
    · obtain rfl : N = 1972 := by omega
      exact cen1972
  · by_cases h4 : N ≤ 1974
    · obtain rfl : N = 1974 := by omega
      exact cen1974
    · by_cases h6 : N ≤ 1976
      · obtain rfl : N = 1976 := by omega
        exact cen1976
      · obtain rfl : N = 1978 := by omega
        exact cen1978

end Kagey131.PaperD.T7
