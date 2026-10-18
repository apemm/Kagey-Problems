import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1865, …, 1875` (generated)

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

/-! ### `N = 1865` -/

def pL1865 : Prm := ⟨80, 37, 40, 1867, 11, 18446744073709551616, 104146742530385320, 104146742530385320⟩
def pH1865 : Prm := ⟨80, 37, 40, 1867, 11, 18446744073709551616, 104147842042013096, 104147842042013096⟩
def pI1865 : Prm := ⟨68, 34, 31, 1867, 11, 18446744073709551616, 104146742530385320, 104147842042013096⟩
noncomputable def L1865_cp1 : Nat × Nat := t7val% (fastRun pL1865 1 1076 (init pL1865) (init pL1865))
theorem L1865_seg1 : segOK pL1865 1 1076 (init pL1865) (init pL1865) L1865_cp1.1 L1865_cp1.2 = true := by
  decide +kernel
noncomputable def L1865_cp2 : Nat × Nat := t7val% (fastRun pL1865 1 1522 (init pL1865) (init pL1865))
theorem L1865_seg2 : segOK pL1865 1077 446 L1865_cp1.1 L1865_cp1.2 L1865_cp2.1 L1865_cp2.2 = true := by
  decide +kernel
theorem L1865_fin : (prmOK pL1865 1865 && ptTest pL1865 (runFrom pL1865 (fmask pL1865) (cmask pL1865) (hmask pL1865) 1523 342 (true, L1865_cp2.1, L1865_cp2.2)) 1865 933 false) = true := by
  decide +kernel
theorem L1865_ok : RunOK pL1865 1865 (runFrom pL1865 (fmask pL1865) (cmask pL1865) (hmask pL1865) 1523 342 (true, L1865_cp2.1, L1865_cp2.2)) ∧ ptTest pL1865 (runFrom pL1865 (fmask pL1865) (cmask pL1865) (hmask pL1865) 1523 342 (true, L1865_cp2.1, L1865_cp2.2)) 1865 933 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1865_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1865_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1865_fin) true) L1865_seg1) L1865_seg2) (by decide) rfl L1865_fin ptTest_fst
noncomputable def H1865_cp1 : Nat × Nat := t7val% (fastRun pH1865 1 1076 (init pH1865) (init pH1865))
theorem H1865_seg1 : segOK pH1865 1 1076 (init pH1865) (init pH1865) H1865_cp1.1 H1865_cp1.2 = true := by
  decide +kernel
noncomputable def H1865_cp2 : Nat × Nat := t7val% (fastRun pH1865 1 1522 (init pH1865) (init pH1865))
theorem H1865_seg2 : segOK pH1865 1077 446 H1865_cp1.1 H1865_cp1.2 H1865_cp2.1 H1865_cp2.2 = true := by
  decide +kernel
theorem H1865_fin : (prmOK pH1865 1865 && ptTest pH1865 (runFrom pH1865 (fmask pH1865) (cmask pH1865) (hmask pH1865) 1523 342 (true, H1865_cp2.1, H1865_cp2.2)) 1865 933 true) = true := by
  decide +kernel
theorem H1865_ok : RunOK pH1865 1865 (runFrom pH1865 (fmask pH1865) (cmask pH1865) (hmask pH1865) 1523 342 (true, H1865_cp2.1, H1865_cp2.2)) ∧ ptTest pH1865 (runFrom pH1865 (fmask pH1865) (cmask pH1865) (hmask pH1865) 1523 342 (true, H1865_cp2.1, H1865_cp2.2)) 1865 933 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1865_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1865_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1865_fin) true) H1865_seg1) H1865_seg2) (by decide) rfl H1865_fin ptTest_fst
noncomputable def I1865_cp1 : Nat × Nat := t7val% (fastRun pI1865 1 1076 (init pI1865) (init pI1865))
theorem I1865_seg1 : segOK pI1865 1 1076 (init pI1865) (init pI1865) I1865_cp1.1 I1865_cp1.2 = true := by
  decide +kernel
noncomputable def I1865_cp2 : Nat × Nat := t7val% (fastRun pI1865 1 1522 (init pI1865) (init pI1865))
theorem I1865_seg2 : segOK pI1865 1077 446 I1865_cp1.1 I1865_cp1.2 I1865_cp2.1 I1865_cp2.2 = true := by
  decide +kernel
theorem I1865_fin : (prmOK pI1865 1865 && intTest pI1865 (runFrom pI1865 (fmask pI1865) (cmask pI1865) (hmask pI1865) 1523 342 (true, I1865_cp2.1, I1865_cp2.2)) 1865 21 false) = true := by
  decide +kernel
theorem I1865_ok : RunOK pI1865 1865 (runFrom pI1865 (fmask pI1865) (cmask pI1865) (hmask pI1865) 1523 342 (true, I1865_cp2.1, I1865_cp2.2)) ∧ intTest pI1865 (runFrom pI1865 (fmask pI1865) (cmask pI1865) (hmask pI1865) 1523 342 (true, I1865_cp2.1, I1865_cp2.2)) 1865 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1865_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1865_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1865_fin) true) I1865_seg1) I1865_seg2) (by decide) rfl I1865_fin intTest_fst
theorem link1865 : linkOK pL1865 pH1865 pI1865 = true := by decide +kernel
theorem cvx1865 : ConvexBetweenHumps 1865 :=
  cvx_of L1865_ok H1865_ok I1865_ok link1865 (by decide)

/-! ### `N = 1866` -/

def pL1866 : Prm := ⟨80, 37, 40, 1868, 11, 18446744073709551616, 104100927099370157, 104100927099370157⟩
def pH1866 : Prm := ⟨80, 37, 40, 1868, 11, 18446744073709551616, 104102026610997933, 104102026610997933⟩
def pI1866 : Prm := ⟨68, 34, 31, 1868, 11, 18446744073709551616, 104100927099370157, 104102026610997933⟩
noncomputable def L1866_cp1 : Nat × Nat := t7val% (fastRun pL1866 1 1076 (init pL1866) (init pL1866))
theorem L1866_seg1 : segOK pL1866 1 1076 (init pL1866) (init pL1866) L1866_cp1.1 L1866_cp1.2 = true := by
  decide +kernel
noncomputable def L1866_cp2 : Nat × Nat := t7val% (fastRun pL1866 1 1523 (init pL1866) (init pL1866))
theorem L1866_seg2 : segOK pL1866 1077 447 L1866_cp1.1 L1866_cp1.2 L1866_cp2.1 L1866_cp2.2 = true := by
  decide +kernel
theorem L1866_fin : (prmOK pL1866 1866 && ptTest pL1866 (runFrom pL1866 (fmask pL1866) (cmask pL1866) (hmask pL1866) 1524 342 (true, L1866_cp2.1, L1866_cp2.2)) 1866 933 false) = true := by
  decide +kernel
theorem L1866_ok : RunOK pL1866 1866 (runFrom pL1866 (fmask pL1866) (cmask pL1866) (hmask pL1866) 1524 342 (true, L1866_cp2.1, L1866_cp2.2)) ∧ ptTest pL1866 (runFrom pL1866 (fmask pL1866) (cmask pL1866) (hmask pL1866) 1524 342 (true, L1866_cp2.1, L1866_cp2.2)) 1866 933 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1866_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1866_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1866_fin) true) L1866_seg1) L1866_seg2) (by decide) rfl L1866_fin ptTest_fst
noncomputable def H1866_cp1 : Nat × Nat := t7val% (fastRun pH1866 1 1076 (init pH1866) (init pH1866))
theorem H1866_seg1 : segOK pH1866 1 1076 (init pH1866) (init pH1866) H1866_cp1.1 H1866_cp1.2 = true := by
  decide +kernel
noncomputable def H1866_cp2 : Nat × Nat := t7val% (fastRun pH1866 1 1523 (init pH1866) (init pH1866))
theorem H1866_seg2 : segOK pH1866 1077 447 H1866_cp1.1 H1866_cp1.2 H1866_cp2.1 H1866_cp2.2 = true := by
  decide +kernel
theorem H1866_fin : (prmOK pH1866 1866 && ptTest pH1866 (runFrom pH1866 (fmask pH1866) (cmask pH1866) (hmask pH1866) 1524 342 (true, H1866_cp2.1, H1866_cp2.2)) 1866 933 true) = true := by
  decide +kernel
theorem H1866_ok : RunOK pH1866 1866 (runFrom pH1866 (fmask pH1866) (cmask pH1866) (hmask pH1866) 1524 342 (true, H1866_cp2.1, H1866_cp2.2)) ∧ ptTest pH1866 (runFrom pH1866 (fmask pH1866) (cmask pH1866) (hmask pH1866) 1524 342 (true, H1866_cp2.1, H1866_cp2.2)) 1866 933 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1866_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1866_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1866_fin) true) H1866_seg1) H1866_seg2) (by decide) rfl H1866_fin ptTest_fst
noncomputable def I1866_cp1 : Nat × Nat := t7val% (fastRun pI1866 1 1076 (init pI1866) (init pI1866))
theorem I1866_seg1 : segOK pI1866 1 1076 (init pI1866) (init pI1866) I1866_cp1.1 I1866_cp1.2 = true := by
  decide +kernel
noncomputable def I1866_cp2 : Nat × Nat := t7val% (fastRun pI1866 1 1523 (init pI1866) (init pI1866))
theorem I1866_seg2 : segOK pI1866 1077 447 I1866_cp1.1 I1866_cp1.2 I1866_cp2.1 I1866_cp2.2 = true := by
  decide +kernel
theorem I1866_fin : (prmOK pI1866 1866 && intTest pI1866 (runFrom pI1866 (fmask pI1866) (cmask pI1866) (hmask pI1866) 1524 342 (true, I1866_cp2.1, I1866_cp2.2)) 1866 21 true) = true := by
  decide +kernel
theorem I1866_ok : RunOK pI1866 1866 (runFrom pI1866 (fmask pI1866) (cmask pI1866) (hmask pI1866) 1524 342 (true, I1866_cp2.1, I1866_cp2.2)) ∧ intTest pI1866 (runFrom pI1866 (fmask pI1866) (cmask pI1866) (hmask pI1866) 1524 342 (true, I1866_cp2.1, I1866_cp2.2)) 1866 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1866_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1866_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1866_fin) true) I1866_seg1) I1866_seg2) (by decide) rfl I1866_fin intTest_fst
theorem link1866 : linkOK pL1866 pH1866 pI1866 = true := by decide +kernel
theorem cvx1866 : ConvexBetweenHumps 1866 :=
  cvx_of L1866_ok H1866_ok I1866_ok link1866 (by decide)
theorem cenlink1866 : cenLinkOK pI1866 1866 = true := by decide +kernel
theorem cen1866 : CenterUniqueMin 1866 ∧ DipHyp 1866 ∧ OnePointHyps 1866 :=
  cen_of L1866_ok H1866_ok I1866_ok link1866 cenlink1866

/-! ### `N = 1867` -/

def pL1867 : Prm := ⟨80, 37, 40, 1869, 11, 18446744073709551616, 104055138154761984, 104055138154761984⟩
def pH1867 : Prm := ⟨80, 37, 40, 1869, 11, 18446744073709551616, 104056237666389760, 104056237666389760⟩
def pI1867 : Prm := ⟨68, 34, 31, 1869, 11, 18446744073709551616, 104055138154761984, 104056237666389760⟩
noncomputable def L1867_cp1 : Nat × Nat := t7val% (fastRun pL1867 1 1077 (init pL1867) (init pL1867))
theorem L1867_seg1 : segOK pL1867 1 1077 (init pL1867) (init pL1867) L1867_cp1.1 L1867_cp1.2 = true := by
  decide +kernel
noncomputable def L1867_cp2 : Nat × Nat := t7val% (fastRun pL1867 1 1523 (init pL1867) (init pL1867))
theorem L1867_seg2 : segOK pL1867 1078 446 L1867_cp1.1 L1867_cp1.2 L1867_cp2.1 L1867_cp2.2 = true := by
  decide +kernel
theorem L1867_fin : (prmOK pL1867 1867 && ptTest pL1867 (runFrom pL1867 (fmask pL1867) (cmask pL1867) (hmask pL1867) 1524 343 (true, L1867_cp2.1, L1867_cp2.2)) 1867 934 false) = true := by
  decide +kernel
theorem L1867_ok : RunOK pL1867 1867 (runFrom pL1867 (fmask pL1867) (cmask pL1867) (hmask pL1867) 1524 343 (true, L1867_cp2.1, L1867_cp2.2)) ∧ ptTest pL1867 (runFrom pL1867 (fmask pL1867) (cmask pL1867) (hmask pL1867) 1524 343 (true, L1867_cp2.1, L1867_cp2.2)) 1867 934 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1867_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1867_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1867_fin) true) L1867_seg1) L1867_seg2) (by decide) rfl L1867_fin ptTest_fst
noncomputable def H1867_cp1 : Nat × Nat := t7val% (fastRun pH1867 1 1077 (init pH1867) (init pH1867))
theorem H1867_seg1 : segOK pH1867 1 1077 (init pH1867) (init pH1867) H1867_cp1.1 H1867_cp1.2 = true := by
  decide +kernel
noncomputable def H1867_cp2 : Nat × Nat := t7val% (fastRun pH1867 1 1523 (init pH1867) (init pH1867))
theorem H1867_seg2 : segOK pH1867 1078 446 H1867_cp1.1 H1867_cp1.2 H1867_cp2.1 H1867_cp2.2 = true := by
  decide +kernel
theorem H1867_fin : (prmOK pH1867 1867 && ptTest pH1867 (runFrom pH1867 (fmask pH1867) (cmask pH1867) (hmask pH1867) 1524 343 (true, H1867_cp2.1, H1867_cp2.2)) 1867 934 true) = true := by
  decide +kernel
theorem H1867_ok : RunOK pH1867 1867 (runFrom pH1867 (fmask pH1867) (cmask pH1867) (hmask pH1867) 1524 343 (true, H1867_cp2.1, H1867_cp2.2)) ∧ ptTest pH1867 (runFrom pH1867 (fmask pH1867) (cmask pH1867) (hmask pH1867) 1524 343 (true, H1867_cp2.1, H1867_cp2.2)) 1867 934 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1867_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1867_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1867_fin) true) H1867_seg1) H1867_seg2) (by decide) rfl H1867_fin ptTest_fst
noncomputable def I1867_cp1 : Nat × Nat := t7val% (fastRun pI1867 1 1077 (init pI1867) (init pI1867))
theorem I1867_seg1 : segOK pI1867 1 1077 (init pI1867) (init pI1867) I1867_cp1.1 I1867_cp1.2 = true := by
  decide +kernel
noncomputable def I1867_cp2 : Nat × Nat := t7val% (fastRun pI1867 1 1523 (init pI1867) (init pI1867))
theorem I1867_seg2 : segOK pI1867 1078 446 I1867_cp1.1 I1867_cp1.2 I1867_cp2.1 I1867_cp2.2 = true := by
  decide +kernel
theorem I1867_fin : (prmOK pI1867 1867 && intTest pI1867 (runFrom pI1867 (fmask pI1867) (cmask pI1867) (hmask pI1867) 1524 343 (true, I1867_cp2.1, I1867_cp2.2)) 1867 21 false) = true := by
  decide +kernel
theorem I1867_ok : RunOK pI1867 1867 (runFrom pI1867 (fmask pI1867) (cmask pI1867) (hmask pI1867) 1524 343 (true, I1867_cp2.1, I1867_cp2.2)) ∧ intTest pI1867 (runFrom pI1867 (fmask pI1867) (cmask pI1867) (hmask pI1867) 1524 343 (true, I1867_cp2.1, I1867_cp2.2)) 1867 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1867_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1867_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1867_fin) true) I1867_seg1) I1867_seg2) (by decide) rfl I1867_fin intTest_fst
theorem link1867 : linkOK pL1867 pH1867 pI1867 = true := by decide +kernel
theorem cvx1867 : ConvexBetweenHumps 1867 :=
  cvx_of L1867_ok H1867_ok I1867_ok link1867 (by decide)

/-! ### `N = 1868` -/

def pL1868 : Prm := ⟨80, 37, 40, 1870, 11, 18446744073709551616, 104009410095754001, 104009410095754001⟩
def pH1868 : Prm := ⟨80, 37, 40, 1870, 11, 18446744073709551616, 104010509607381777, 104010509607381777⟩
def pI1868 : Prm := ⟨68, 34, 31, 1870, 11, 18446744073709551616, 104009410095754001, 104010509607381777⟩
noncomputable def L1868_cp1 : Nat × Nat := t7val% (fastRun pL1868 1 1077 (init pL1868) (init pL1868))
theorem L1868_seg1 : segOK pL1868 1 1077 (init pL1868) (init pL1868) L1868_cp1.1 L1868_cp1.2 = true := by
  decide +kernel
noncomputable def L1868_cp2 : Nat × Nat := t7val% (fastRun pL1868 1 1524 (init pL1868) (init pL1868))
theorem L1868_seg2 : segOK pL1868 1078 447 L1868_cp1.1 L1868_cp1.2 L1868_cp2.1 L1868_cp2.2 = true := by
  decide +kernel
theorem L1868_fin : (prmOK pL1868 1868 && ptTest pL1868 (runFrom pL1868 (fmask pL1868) (cmask pL1868) (hmask pL1868) 1525 343 (true, L1868_cp2.1, L1868_cp2.2)) 1868 934 false) = true := by
  decide +kernel
theorem L1868_ok : RunOK pL1868 1868 (runFrom pL1868 (fmask pL1868) (cmask pL1868) (hmask pL1868) 1525 343 (true, L1868_cp2.1, L1868_cp2.2)) ∧ ptTest pL1868 (runFrom pL1868 (fmask pL1868) (cmask pL1868) (hmask pL1868) 1525 343 (true, L1868_cp2.1, L1868_cp2.2)) 1868 934 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1868_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1868_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1868_fin) true) L1868_seg1) L1868_seg2) (by decide) rfl L1868_fin ptTest_fst
noncomputable def H1868_cp1 : Nat × Nat := t7val% (fastRun pH1868 1 1077 (init pH1868) (init pH1868))
theorem H1868_seg1 : segOK pH1868 1 1077 (init pH1868) (init pH1868) H1868_cp1.1 H1868_cp1.2 = true := by
  decide +kernel
noncomputable def H1868_cp2 : Nat × Nat := t7val% (fastRun pH1868 1 1524 (init pH1868) (init pH1868))
theorem H1868_seg2 : segOK pH1868 1078 447 H1868_cp1.1 H1868_cp1.2 H1868_cp2.1 H1868_cp2.2 = true := by
  decide +kernel
theorem H1868_fin : (prmOK pH1868 1868 && ptTest pH1868 (runFrom pH1868 (fmask pH1868) (cmask pH1868) (hmask pH1868) 1525 343 (true, H1868_cp2.1, H1868_cp2.2)) 1868 934 true) = true := by
  decide +kernel
theorem H1868_ok : RunOK pH1868 1868 (runFrom pH1868 (fmask pH1868) (cmask pH1868) (hmask pH1868) 1525 343 (true, H1868_cp2.1, H1868_cp2.2)) ∧ ptTest pH1868 (runFrom pH1868 (fmask pH1868) (cmask pH1868) (hmask pH1868) 1525 343 (true, H1868_cp2.1, H1868_cp2.2)) 1868 934 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1868_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1868_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1868_fin) true) H1868_seg1) H1868_seg2) (by decide) rfl H1868_fin ptTest_fst
noncomputable def I1868_cp1 : Nat × Nat := t7val% (fastRun pI1868 1 1077 (init pI1868) (init pI1868))
theorem I1868_seg1 : segOK pI1868 1 1077 (init pI1868) (init pI1868) I1868_cp1.1 I1868_cp1.2 = true := by
  decide +kernel
noncomputable def I1868_cp2 : Nat × Nat := t7val% (fastRun pI1868 1 1524 (init pI1868) (init pI1868))
theorem I1868_seg2 : segOK pI1868 1078 447 I1868_cp1.1 I1868_cp1.2 I1868_cp2.1 I1868_cp2.2 = true := by
  decide +kernel
theorem I1868_fin : (prmOK pI1868 1868 && intTest pI1868 (runFrom pI1868 (fmask pI1868) (cmask pI1868) (hmask pI1868) 1525 343 (true, I1868_cp2.1, I1868_cp2.2)) 1868 21 true) = true := by
  decide +kernel
theorem I1868_ok : RunOK pI1868 1868 (runFrom pI1868 (fmask pI1868) (cmask pI1868) (hmask pI1868) 1525 343 (true, I1868_cp2.1, I1868_cp2.2)) ∧ intTest pI1868 (runFrom pI1868 (fmask pI1868) (cmask pI1868) (hmask pI1868) 1525 343 (true, I1868_cp2.1, I1868_cp2.2)) 1868 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1868_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1868_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1868_fin) true) I1868_seg1) I1868_seg2) (by decide) rfl I1868_fin intTest_fst
theorem link1868 : linkOK pL1868 pH1868 pI1868 = true := by decide +kernel
theorem cvx1868 : ConvexBetweenHumps 1868 :=
  cvx_of L1868_ok H1868_ok I1868_ok link1868 (by decide)
theorem cenlink1868 : cenLinkOK pI1868 1868 = true := by decide +kernel
theorem cen1868 : CenterUniqueMin 1868 ∧ DipHyp 1868 ∧ OnePointHyps 1868 :=
  cen_of L1868_ok H1868_ok I1868_ok link1868 cenlink1868

/-! ### `N = 1869` -/

def pL1869 : Prm := ⟨80, 37, 40, 1871, 11, 18446744073709551616, 103963708450454391, 103963708450454391⟩
def pH1869 : Prm := ⟨80, 37, 40, 1871, 11, 18446744073709551616, 103964807962082167, 103964807962082167⟩
def pI1869 : Prm := ⟨68, 34, 31, 1871, 11, 18446744073709551616, 103963708450454391, 103964807962082167⟩
noncomputable def L1869_cp1 : Nat × Nat := t7val% (fastRun pL1869 1 1078 (init pL1869) (init pL1869))
theorem L1869_seg1 : segOK pL1869 1 1078 (init pL1869) (init pL1869) L1869_cp1.1 L1869_cp1.2 = true := by
  decide +kernel
noncomputable def L1869_cp2 : Nat × Nat := t7val% (fastRun pL1869 1 1525 (init pL1869) (init pL1869))
theorem L1869_seg2 : segOK pL1869 1079 447 L1869_cp1.1 L1869_cp1.2 L1869_cp2.1 L1869_cp2.2 = true := by
  decide +kernel
theorem L1869_fin : (prmOK pL1869 1869 && ptTest pL1869 (runFrom pL1869 (fmask pL1869) (cmask pL1869) (hmask pL1869) 1526 343 (true, L1869_cp2.1, L1869_cp2.2)) 1869 935 false) = true := by
  decide +kernel
theorem L1869_ok : RunOK pL1869 1869 (runFrom pL1869 (fmask pL1869) (cmask pL1869) (hmask pL1869) 1526 343 (true, L1869_cp2.1, L1869_cp2.2)) ∧ ptTest pL1869 (runFrom pL1869 (fmask pL1869) (cmask pL1869) (hmask pL1869) 1526 343 (true, L1869_cp2.1, L1869_cp2.2)) 1869 935 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1869_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1869_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1869_fin) true) L1869_seg1) L1869_seg2) (by decide) rfl L1869_fin ptTest_fst
noncomputable def H1869_cp1 : Nat × Nat := t7val% (fastRun pH1869 1 1078 (init pH1869) (init pH1869))
theorem H1869_seg1 : segOK pH1869 1 1078 (init pH1869) (init pH1869) H1869_cp1.1 H1869_cp1.2 = true := by
  decide +kernel
noncomputable def H1869_cp2 : Nat × Nat := t7val% (fastRun pH1869 1 1525 (init pH1869) (init pH1869))
theorem H1869_seg2 : segOK pH1869 1079 447 H1869_cp1.1 H1869_cp1.2 H1869_cp2.1 H1869_cp2.2 = true := by
  decide +kernel
theorem H1869_fin : (prmOK pH1869 1869 && ptTest pH1869 (runFrom pH1869 (fmask pH1869) (cmask pH1869) (hmask pH1869) 1526 343 (true, H1869_cp2.1, H1869_cp2.2)) 1869 935 true) = true := by
  decide +kernel
theorem H1869_ok : RunOK pH1869 1869 (runFrom pH1869 (fmask pH1869) (cmask pH1869) (hmask pH1869) 1526 343 (true, H1869_cp2.1, H1869_cp2.2)) ∧ ptTest pH1869 (runFrom pH1869 (fmask pH1869) (cmask pH1869) (hmask pH1869) 1526 343 (true, H1869_cp2.1, H1869_cp2.2)) 1869 935 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1869_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1869_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1869_fin) true) H1869_seg1) H1869_seg2) (by decide) rfl H1869_fin ptTest_fst
noncomputable def I1869_cp1 : Nat × Nat := t7val% (fastRun pI1869 1 1078 (init pI1869) (init pI1869))
theorem I1869_seg1 : segOK pI1869 1 1078 (init pI1869) (init pI1869) I1869_cp1.1 I1869_cp1.2 = true := by
  decide +kernel
noncomputable def I1869_cp2 : Nat × Nat := t7val% (fastRun pI1869 1 1525 (init pI1869) (init pI1869))
theorem I1869_seg2 : segOK pI1869 1079 447 I1869_cp1.1 I1869_cp1.2 I1869_cp2.1 I1869_cp2.2 = true := by
  decide +kernel
theorem I1869_fin : (prmOK pI1869 1869 && intTest pI1869 (runFrom pI1869 (fmask pI1869) (cmask pI1869) (hmask pI1869) 1526 343 (true, I1869_cp2.1, I1869_cp2.2)) 1869 21 false) = true := by
  decide +kernel
theorem I1869_ok : RunOK pI1869 1869 (runFrom pI1869 (fmask pI1869) (cmask pI1869) (hmask pI1869) 1526 343 (true, I1869_cp2.1, I1869_cp2.2)) ∧ intTest pI1869 (runFrom pI1869 (fmask pI1869) (cmask pI1869) (hmask pI1869) 1526 343 (true, I1869_cp2.1, I1869_cp2.2)) 1869 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1869_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1869_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1869_fin) true) I1869_seg1) I1869_seg2) (by decide) rfl I1869_fin intTest_fst
theorem link1869 : linkOK pL1869 pH1869 pI1869 = true := by decide +kernel
theorem cvx1869 : ConvexBetweenHumps 1869 :=
  cvx_of L1869_ok H1869_ok I1869_ok link1869 (by decide)

/-! ### `N = 1870` -/

def pL1870 : Prm := ⟨80, 37, 40, 1872, 11, 18446744073709551616, 103918067506121509, 103918067506121509⟩
def pH1870 : Prm := ⟨80, 37, 40, 1872, 11, 18446744073709551616, 103919167017749285, 103919167017749285⟩
def pI1870 : Prm := ⟨68, 34, 31, 1872, 11, 18446744073709551616, 103918067506121509, 103919167017749285⟩
noncomputable def L1870_cp1 : Nat × Nat := t7val% (fastRun pL1870 1 1079 (init pL1870) (init pL1870))
theorem L1870_seg1 : segOK pL1870 1 1079 (init pL1870) (init pL1870) L1870_cp1.1 L1870_cp1.2 = true := by
  decide +kernel
noncomputable def L1870_cp2 : Nat × Nat := t7val% (fastRun pL1870 1 1526 (init pL1870) (init pL1870))
theorem L1870_seg2 : segOK pL1870 1080 447 L1870_cp1.1 L1870_cp1.2 L1870_cp2.1 L1870_cp2.2 = true := by
  decide +kernel
theorem L1870_fin : (prmOK pL1870 1870 && ptTest pL1870 (runFrom pL1870 (fmask pL1870) (cmask pL1870) (hmask pL1870) 1527 343 (true, L1870_cp2.1, L1870_cp2.2)) 1870 935 false) = true := by
  decide +kernel
theorem L1870_ok : RunOK pL1870 1870 (runFrom pL1870 (fmask pL1870) (cmask pL1870) (hmask pL1870) 1527 343 (true, L1870_cp2.1, L1870_cp2.2)) ∧ ptTest pL1870 (runFrom pL1870 (fmask pL1870) (cmask pL1870) (hmask pL1870) 1527 343 (true, L1870_cp2.1, L1870_cp2.2)) 1870 935 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1870_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1870_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1870_fin) true) L1870_seg1) L1870_seg2) (by decide) rfl L1870_fin ptTest_fst
noncomputable def H1870_cp1 : Nat × Nat := t7val% (fastRun pH1870 1 1079 (init pH1870) (init pH1870))
theorem H1870_seg1 : segOK pH1870 1 1079 (init pH1870) (init pH1870) H1870_cp1.1 H1870_cp1.2 = true := by
  decide +kernel
noncomputable def H1870_cp2 : Nat × Nat := t7val% (fastRun pH1870 1 1526 (init pH1870) (init pH1870))
theorem H1870_seg2 : segOK pH1870 1080 447 H1870_cp1.1 H1870_cp1.2 H1870_cp2.1 H1870_cp2.2 = true := by
  decide +kernel
theorem H1870_fin : (prmOK pH1870 1870 && ptTest pH1870 (runFrom pH1870 (fmask pH1870) (cmask pH1870) (hmask pH1870) 1527 343 (true, H1870_cp2.1, H1870_cp2.2)) 1870 935 true) = true := by
  decide +kernel
theorem H1870_ok : RunOK pH1870 1870 (runFrom pH1870 (fmask pH1870) (cmask pH1870) (hmask pH1870) 1527 343 (true, H1870_cp2.1, H1870_cp2.2)) ∧ ptTest pH1870 (runFrom pH1870 (fmask pH1870) (cmask pH1870) (hmask pH1870) 1527 343 (true, H1870_cp2.1, H1870_cp2.2)) 1870 935 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1870_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1870_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1870_fin) true) H1870_seg1) H1870_seg2) (by decide) rfl H1870_fin ptTest_fst
noncomputable def I1870_cp1 : Nat × Nat := t7val% (fastRun pI1870 1 1079 (init pI1870) (init pI1870))
theorem I1870_seg1 : segOK pI1870 1 1079 (init pI1870) (init pI1870) I1870_cp1.1 I1870_cp1.2 = true := by
  decide +kernel
noncomputable def I1870_cp2 : Nat × Nat := t7val% (fastRun pI1870 1 1526 (init pI1870) (init pI1870))
theorem I1870_seg2 : segOK pI1870 1080 447 I1870_cp1.1 I1870_cp1.2 I1870_cp2.1 I1870_cp2.2 = true := by
  decide +kernel
theorem I1870_fin : (prmOK pI1870 1870 && intTest pI1870 (runFrom pI1870 (fmask pI1870) (cmask pI1870) (hmask pI1870) 1527 343 (true, I1870_cp2.1, I1870_cp2.2)) 1870 21 true) = true := by
  decide +kernel
theorem I1870_ok : RunOK pI1870 1870 (runFrom pI1870 (fmask pI1870) (cmask pI1870) (hmask pI1870) 1527 343 (true, I1870_cp2.1, I1870_cp2.2)) ∧ intTest pI1870 (runFrom pI1870 (fmask pI1870) (cmask pI1870) (hmask pI1870) 1527 343 (true, I1870_cp2.1, I1870_cp2.2)) 1870 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1870_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1870_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1870_fin) true) I1870_seg1) I1870_seg2) (by decide) rfl I1870_fin intTest_fst
theorem link1870 : linkOK pL1870 pH1870 pI1870 = true := by decide +kernel
theorem cvx1870 : ConvexBetweenHumps 1870 :=
  cvx_of L1870_ok H1870_ok I1870_ok link1870 (by decide)
theorem cenlink1870 : cenLinkOK pI1870 1870 = true := by decide +kernel
theorem cen1870 : CenterUniqueMin 1870 ∧ DipHyp 1870 ∧ OnePointHyps 1870 :=
  cen_of L1870_ok H1870_ok I1870_ok link1870 cenlink1870

/-! ### `N = 1871` -/

def pL1871 : Prm := ⟨80, 37, 40, 1873, 11, 18446744073709551616, 103872452903056635, 103872452903056635⟩
def pH1871 : Prm := ⟨80, 37, 40, 1873, 11, 18446744073709551616, 103873552414684411, 103873552414684411⟩
def pI1871 : Prm := ⟨68, 34, 31, 1873, 11, 18446744073709551616, 103872452903056635, 103873552414684411⟩
noncomputable def L1871_cp1 : Nat × Nat := t7val% (fastRun pL1871 1 1079 (init pL1871) (init pL1871))
theorem L1871_seg1 : segOK pL1871 1 1079 (init pL1871) (init pL1871) L1871_cp1.1 L1871_cp1.2 = true := by
  decide +kernel
noncomputable def L1871_cp2 : Nat × Nat := t7val% (fastRun pL1871 1 1527 (init pL1871) (init pL1871))
theorem L1871_seg2 : segOK pL1871 1080 448 L1871_cp1.1 L1871_cp1.2 L1871_cp2.1 L1871_cp2.2 = true := by
  decide +kernel
theorem L1871_fin : (prmOK pL1871 1871 && ptTest pL1871 (runFrom pL1871 (fmask pL1871) (cmask pL1871) (hmask pL1871) 1528 343 (true, L1871_cp2.1, L1871_cp2.2)) 1871 936 false) = true := by
  decide +kernel
theorem L1871_ok : RunOK pL1871 1871 (runFrom pL1871 (fmask pL1871) (cmask pL1871) (hmask pL1871) 1528 343 (true, L1871_cp2.1, L1871_cp2.2)) ∧ ptTest pL1871 (runFrom pL1871 (fmask pL1871) (cmask pL1871) (hmask pL1871) 1528 343 (true, L1871_cp2.1, L1871_cp2.2)) 1871 936 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1871_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1871_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1871_fin) true) L1871_seg1) L1871_seg2) (by decide) rfl L1871_fin ptTest_fst
noncomputable def H1871_cp1 : Nat × Nat := t7val% (fastRun pH1871 1 1079 (init pH1871) (init pH1871))
theorem H1871_seg1 : segOK pH1871 1 1079 (init pH1871) (init pH1871) H1871_cp1.1 H1871_cp1.2 = true := by
  decide +kernel
noncomputable def H1871_cp2 : Nat × Nat := t7val% (fastRun pH1871 1 1527 (init pH1871) (init pH1871))
theorem H1871_seg2 : segOK pH1871 1080 448 H1871_cp1.1 H1871_cp1.2 H1871_cp2.1 H1871_cp2.2 = true := by
  decide +kernel
theorem H1871_fin : (prmOK pH1871 1871 && ptTest pH1871 (runFrom pH1871 (fmask pH1871) (cmask pH1871) (hmask pH1871) 1528 343 (true, H1871_cp2.1, H1871_cp2.2)) 1871 936 true) = true := by
  decide +kernel
theorem H1871_ok : RunOK pH1871 1871 (runFrom pH1871 (fmask pH1871) (cmask pH1871) (hmask pH1871) 1528 343 (true, H1871_cp2.1, H1871_cp2.2)) ∧ ptTest pH1871 (runFrom pH1871 (fmask pH1871) (cmask pH1871) (hmask pH1871) 1528 343 (true, H1871_cp2.1, H1871_cp2.2)) 1871 936 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1871_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1871_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1871_fin) true) H1871_seg1) H1871_seg2) (by decide) rfl H1871_fin ptTest_fst
noncomputable def I1871_cp1 : Nat × Nat := t7val% (fastRun pI1871 1 1079 (init pI1871) (init pI1871))
theorem I1871_seg1 : segOK pI1871 1 1079 (init pI1871) (init pI1871) I1871_cp1.1 I1871_cp1.2 = true := by
  decide +kernel
noncomputable def I1871_cp2 : Nat × Nat := t7val% (fastRun pI1871 1 1527 (init pI1871) (init pI1871))
theorem I1871_seg2 : segOK pI1871 1080 448 I1871_cp1.1 I1871_cp1.2 I1871_cp2.1 I1871_cp2.2 = true := by
  decide +kernel
theorem I1871_fin : (prmOK pI1871 1871 && intTest pI1871 (runFrom pI1871 (fmask pI1871) (cmask pI1871) (hmask pI1871) 1528 343 (true, I1871_cp2.1, I1871_cp2.2)) 1871 21 false) = true := by
  decide +kernel
theorem I1871_ok : RunOK pI1871 1871 (runFrom pI1871 (fmask pI1871) (cmask pI1871) (hmask pI1871) 1528 343 (true, I1871_cp2.1, I1871_cp2.2)) ∧ intTest pI1871 (runFrom pI1871 (fmask pI1871) (cmask pI1871) (hmask pI1871) 1528 343 (true, I1871_cp2.1, I1871_cp2.2)) 1871 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1871_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1871_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1871_fin) true) I1871_seg1) I1871_seg2) (by decide) rfl I1871_fin intTest_fst
theorem link1871 : linkOK pL1871 pH1871 pI1871 = true := by decide +kernel
theorem cvx1871 : ConvexBetweenHumps 1871 :=
  cvx_of L1871_ok H1871_ok I1871_ok link1871 (by decide)

/-! ### `N = 1872` -/

def pL1872 : Prm := ⟨80, 37, 40, 1874, 11, 18446744073709551616, 103826898817062900, 103826898817062900⟩
def pH1872 : Prm := ⟨80, 37, 40, 1874, 11, 18446744073709551616, 103827998328690676, 103827998328690676⟩
def pI1872 : Prm := ⟨68, 34, 31, 1874, 11, 18446744073709551616, 103826898817062900, 103827998328690676⟩
noncomputable def L1872_cp1 : Nat × Nat := t7val% (fastRun pL1872 1 1080 (init pL1872) (init pL1872))
theorem L1872_seg1 : segOK pL1872 1 1080 (init pL1872) (init pL1872) L1872_cp1.1 L1872_cp1.2 = true := by
  decide +kernel
noncomputable def L1872_cp2 : Nat × Nat := t7val% (fastRun pL1872 1 1527 (init pL1872) (init pL1872))
theorem L1872_seg2 : segOK pL1872 1081 447 L1872_cp1.1 L1872_cp1.2 L1872_cp2.1 L1872_cp2.2 = true := by
  decide +kernel
theorem L1872_fin : (prmOK pL1872 1872 && ptTest pL1872 (runFrom pL1872 (fmask pL1872) (cmask pL1872) (hmask pL1872) 1528 344 (true, L1872_cp2.1, L1872_cp2.2)) 1872 936 false) = true := by
  decide +kernel
theorem L1872_ok : RunOK pL1872 1872 (runFrom pL1872 (fmask pL1872) (cmask pL1872) (hmask pL1872) 1528 344 (true, L1872_cp2.1, L1872_cp2.2)) ∧ ptTest pL1872 (runFrom pL1872 (fmask pL1872) (cmask pL1872) (hmask pL1872) 1528 344 (true, L1872_cp2.1, L1872_cp2.2)) 1872 936 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1872_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1872_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1872_fin) true) L1872_seg1) L1872_seg2) (by decide) rfl L1872_fin ptTest_fst
noncomputable def H1872_cp1 : Nat × Nat := t7val% (fastRun pH1872 1 1080 (init pH1872) (init pH1872))
theorem H1872_seg1 : segOK pH1872 1 1080 (init pH1872) (init pH1872) H1872_cp1.1 H1872_cp1.2 = true := by
  decide +kernel
noncomputable def H1872_cp2 : Nat × Nat := t7val% (fastRun pH1872 1 1527 (init pH1872) (init pH1872))
theorem H1872_seg2 : segOK pH1872 1081 447 H1872_cp1.1 H1872_cp1.2 H1872_cp2.1 H1872_cp2.2 = true := by
  decide +kernel
theorem H1872_fin : (prmOK pH1872 1872 && ptTest pH1872 (runFrom pH1872 (fmask pH1872) (cmask pH1872) (hmask pH1872) 1528 344 (true, H1872_cp2.1, H1872_cp2.2)) 1872 936 true) = true := by
  decide +kernel
theorem H1872_ok : RunOK pH1872 1872 (runFrom pH1872 (fmask pH1872) (cmask pH1872) (hmask pH1872) 1528 344 (true, H1872_cp2.1, H1872_cp2.2)) ∧ ptTest pH1872 (runFrom pH1872 (fmask pH1872) (cmask pH1872) (hmask pH1872) 1528 344 (true, H1872_cp2.1, H1872_cp2.2)) 1872 936 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1872_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1872_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1872_fin) true) H1872_seg1) H1872_seg2) (by decide) rfl H1872_fin ptTest_fst
noncomputable def I1872_cp1 : Nat × Nat := t7val% (fastRun pI1872 1 1080 (init pI1872) (init pI1872))
theorem I1872_seg1 : segOK pI1872 1 1080 (init pI1872) (init pI1872) I1872_cp1.1 I1872_cp1.2 = true := by
  decide +kernel
noncomputable def I1872_cp2 : Nat × Nat := t7val% (fastRun pI1872 1 1527 (init pI1872) (init pI1872))
theorem I1872_seg2 : segOK pI1872 1081 447 I1872_cp1.1 I1872_cp1.2 I1872_cp2.1 I1872_cp2.2 = true := by
  decide +kernel
theorem I1872_fin : (prmOK pI1872 1872 && intTest pI1872 (runFrom pI1872 (fmask pI1872) (cmask pI1872) (hmask pI1872) 1528 344 (true, I1872_cp2.1, I1872_cp2.2)) 1872 21 true) = true := by
  decide +kernel
theorem I1872_ok : RunOK pI1872 1872 (runFrom pI1872 (fmask pI1872) (cmask pI1872) (hmask pI1872) 1528 344 (true, I1872_cp2.1, I1872_cp2.2)) ∧ intTest pI1872 (runFrom pI1872 (fmask pI1872) (cmask pI1872) (hmask pI1872) 1528 344 (true, I1872_cp2.1, I1872_cp2.2)) 1872 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1872_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1872_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1872_fin) true) I1872_seg1) I1872_seg2) (by decide) rfl I1872_fin intTest_fst
theorem link1872 : linkOK pL1872 pH1872 pI1872 = true := by decide +kernel
theorem cvx1872 : ConvexBetweenHumps 1872 :=
  cvx_of L1872_ok H1872_ok I1872_ok link1872 (by decide)
theorem cenlink1872 : cenLinkOK pI1872 1872 = true := by decide +kernel
theorem cen1872 : CenterUniqueMin 1872 ∧ DipHyp 1872 ∧ OnePointHyps 1872 :=
  cen_of L1872_ok H1872_ok I1872_ok link1872 cenlink1872

/-! ### `N = 1873` -/

def pL1873 : Prm := ⟨80, 37, 40, 1875, 11, 18446744073709551616, 103781371000173508, 103781371000173508⟩
def pH1873 : Prm := ⟨80, 37, 40, 1875, 11, 18446744073709551616, 103782470511801284, 103782470511801284⟩
def pI1873 : Prm := ⟨68, 34, 31, 1875, 11, 18446744073709551616, 103781371000173508, 103782470511801284⟩
noncomputable def L1873_cp1 : Nat × Nat := t7val% (fastRun pL1873 1 1080 (init pL1873) (init pL1873))
theorem L1873_seg1 : segOK pL1873 1 1080 (init pL1873) (init pL1873) L1873_cp1.1 L1873_cp1.2 = true := by
  decide +kernel
noncomputable def L1873_cp2 : Nat × Nat := t7val% (fastRun pL1873 1 1528 (init pL1873) (init pL1873))
theorem L1873_seg2 : segOK pL1873 1081 448 L1873_cp1.1 L1873_cp1.2 L1873_cp2.1 L1873_cp2.2 = true := by
  decide +kernel
theorem L1873_fin : (prmOK pL1873 1873 && ptTest pL1873 (runFrom pL1873 (fmask pL1873) (cmask pL1873) (hmask pL1873) 1529 344 (true, L1873_cp2.1, L1873_cp2.2)) 1873 937 false) = true := by
  decide +kernel
theorem L1873_ok : RunOK pL1873 1873 (runFrom pL1873 (fmask pL1873) (cmask pL1873) (hmask pL1873) 1529 344 (true, L1873_cp2.1, L1873_cp2.2)) ∧ ptTest pL1873 (runFrom pL1873 (fmask pL1873) (cmask pL1873) (hmask pL1873) 1529 344 (true, L1873_cp2.1, L1873_cp2.2)) 1873 937 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1873_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1873_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1873_fin) true) L1873_seg1) L1873_seg2) (by decide) rfl L1873_fin ptTest_fst
noncomputable def H1873_cp1 : Nat × Nat := t7val% (fastRun pH1873 1 1080 (init pH1873) (init pH1873))
theorem H1873_seg1 : segOK pH1873 1 1080 (init pH1873) (init pH1873) H1873_cp1.1 H1873_cp1.2 = true := by
  decide +kernel
noncomputable def H1873_cp2 : Nat × Nat := t7val% (fastRun pH1873 1 1528 (init pH1873) (init pH1873))
theorem H1873_seg2 : segOK pH1873 1081 448 H1873_cp1.1 H1873_cp1.2 H1873_cp2.1 H1873_cp2.2 = true := by
  decide +kernel
theorem H1873_fin : (prmOK pH1873 1873 && ptTest pH1873 (runFrom pH1873 (fmask pH1873) (cmask pH1873) (hmask pH1873) 1529 344 (true, H1873_cp2.1, H1873_cp2.2)) 1873 937 true) = true := by
  decide +kernel
theorem H1873_ok : RunOK pH1873 1873 (runFrom pH1873 (fmask pH1873) (cmask pH1873) (hmask pH1873) 1529 344 (true, H1873_cp2.1, H1873_cp2.2)) ∧ ptTest pH1873 (runFrom pH1873 (fmask pH1873) (cmask pH1873) (hmask pH1873) 1529 344 (true, H1873_cp2.1, H1873_cp2.2)) 1873 937 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1873_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1873_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1873_fin) true) H1873_seg1) H1873_seg2) (by decide) rfl H1873_fin ptTest_fst
noncomputable def I1873_cp1 : Nat × Nat := t7val% (fastRun pI1873 1 1080 (init pI1873) (init pI1873))
theorem I1873_seg1 : segOK pI1873 1 1080 (init pI1873) (init pI1873) I1873_cp1.1 I1873_cp1.2 = true := by
  decide +kernel
noncomputable def I1873_cp2 : Nat × Nat := t7val% (fastRun pI1873 1 1528 (init pI1873) (init pI1873))
theorem I1873_seg2 : segOK pI1873 1081 448 I1873_cp1.1 I1873_cp1.2 I1873_cp2.1 I1873_cp2.2 = true := by
  decide +kernel
theorem I1873_fin : (prmOK pI1873 1873 && intTest pI1873 (runFrom pI1873 (fmask pI1873) (cmask pI1873) (hmask pI1873) 1529 344 (true, I1873_cp2.1, I1873_cp2.2)) 1873 21 false) = true := by
  decide +kernel
theorem I1873_ok : RunOK pI1873 1873 (runFrom pI1873 (fmask pI1873) (cmask pI1873) (hmask pI1873) 1529 344 (true, I1873_cp2.1, I1873_cp2.2)) ∧ intTest pI1873 (runFrom pI1873 (fmask pI1873) (cmask pI1873) (hmask pI1873) 1529 344 (true, I1873_cp2.1, I1873_cp2.2)) 1873 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1873_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1873_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1873_fin) true) I1873_seg1) I1873_seg2) (by decide) rfl I1873_fin intTest_fst
theorem link1873 : linkOK pL1873 pH1873 pI1873 = true := by decide +kernel
theorem cvx1873 : ConvexBetweenHumps 1873 :=
  cvx_of L1873_ok H1873_ok I1873_ok link1873 (by decide)

/-! ### `N = 1874` -/

def pL1874 : Prm := ⟨80, 37, 40, 1876, 11, 18446744073709551616, 103735903517215980, 103735903517215980⟩
def pH1874 : Prm := ⟨80, 37, 40, 1876, 11, 18446744073709551616, 103737003028843756, 103737003028843756⟩
def pI1874 : Prm := ⟨68, 34, 31, 1876, 11, 18446744073709551616, 103735903517215980, 103737003028843756⟩
noncomputable def L1874_cp1 : Nat × Nat := t7val% (fastRun pL1874 1 1081 (init pL1874) (init pL1874))
theorem L1874_seg1 : segOK pL1874 1 1081 (init pL1874) (init pL1874) L1874_cp1.1 L1874_cp1.2 = true := by
  decide +kernel
noncomputable def L1874_cp2 : Nat × Nat := t7val% (fastRun pL1874 1 1529 (init pL1874) (init pL1874))
theorem L1874_seg2 : segOK pL1874 1082 448 L1874_cp1.1 L1874_cp1.2 L1874_cp2.1 L1874_cp2.2 = true := by
  decide +kernel
theorem L1874_fin : (prmOK pL1874 1874 && ptTest pL1874 (runFrom pL1874 (fmask pL1874) (cmask pL1874) (hmask pL1874) 1530 344 (true, L1874_cp2.1, L1874_cp2.2)) 1874 937 false) = true := by
  decide +kernel
theorem L1874_ok : RunOK pL1874 1874 (runFrom pL1874 (fmask pL1874) (cmask pL1874) (hmask pL1874) 1530 344 (true, L1874_cp2.1, L1874_cp2.2)) ∧ ptTest pL1874 (runFrom pL1874 (fmask pL1874) (cmask pL1874) (hmask pL1874) 1530 344 (true, L1874_cp2.1, L1874_cp2.2)) 1874 937 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1874_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1874_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1874_fin) true) L1874_seg1) L1874_seg2) (by decide) rfl L1874_fin ptTest_fst
noncomputable def H1874_cp1 : Nat × Nat := t7val% (fastRun pH1874 1 1081 (init pH1874) (init pH1874))
theorem H1874_seg1 : segOK pH1874 1 1081 (init pH1874) (init pH1874) H1874_cp1.1 H1874_cp1.2 = true := by
  decide +kernel
noncomputable def H1874_cp2 : Nat × Nat := t7val% (fastRun pH1874 1 1529 (init pH1874) (init pH1874))
theorem H1874_seg2 : segOK pH1874 1082 448 H1874_cp1.1 H1874_cp1.2 H1874_cp2.1 H1874_cp2.2 = true := by
  decide +kernel
theorem H1874_fin : (prmOK pH1874 1874 && ptTest pH1874 (runFrom pH1874 (fmask pH1874) (cmask pH1874) (hmask pH1874) 1530 344 (true, H1874_cp2.1, H1874_cp2.2)) 1874 937 true) = true := by
  decide +kernel
theorem H1874_ok : RunOK pH1874 1874 (runFrom pH1874 (fmask pH1874) (cmask pH1874) (hmask pH1874) 1530 344 (true, H1874_cp2.1, H1874_cp2.2)) ∧ ptTest pH1874 (runFrom pH1874 (fmask pH1874) (cmask pH1874) (hmask pH1874) 1530 344 (true, H1874_cp2.1, H1874_cp2.2)) 1874 937 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1874_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1874_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1874_fin) true) H1874_seg1) H1874_seg2) (by decide) rfl H1874_fin ptTest_fst
noncomputable def I1874_cp1 : Nat × Nat := t7val% (fastRun pI1874 1 1081 (init pI1874) (init pI1874))
theorem I1874_seg1 : segOK pI1874 1 1081 (init pI1874) (init pI1874) I1874_cp1.1 I1874_cp1.2 = true := by
  decide +kernel
noncomputable def I1874_cp2 : Nat × Nat := t7val% (fastRun pI1874 1 1529 (init pI1874) (init pI1874))
theorem I1874_seg2 : segOK pI1874 1082 448 I1874_cp1.1 I1874_cp1.2 I1874_cp2.1 I1874_cp2.2 = true := by
  decide +kernel
theorem I1874_fin : (prmOK pI1874 1874 && intTest pI1874 (runFrom pI1874 (fmask pI1874) (cmask pI1874) (hmask pI1874) 1530 344 (true, I1874_cp2.1, I1874_cp2.2)) 1874 21 true) = true := by
  decide +kernel
theorem I1874_ok : RunOK pI1874 1874 (runFrom pI1874 (fmask pI1874) (cmask pI1874) (hmask pI1874) 1530 344 (true, I1874_cp2.1, I1874_cp2.2)) ∧ intTest pI1874 (runFrom pI1874 (fmask pI1874) (cmask pI1874) (hmask pI1874) 1530 344 (true, I1874_cp2.1, I1874_cp2.2)) 1874 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1874_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1874_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1874_fin) true) I1874_seg1) I1874_seg2) (by decide) rfl I1874_fin intTest_fst
theorem link1874 : linkOK pL1874 pH1874 pI1874 = true := by decide +kernel
theorem cvx1874 : ConvexBetweenHumps 1874 :=
  cvx_of L1874_ok H1874_ok I1874_ok link1874 (by decide)
theorem cenlink1874 : cenLinkOK pI1874 1874 = true := by decide +kernel
theorem cen1874 : CenterUniqueMin 1874 ∧ DipHyp 1874 ∧ OnePointHyps 1874 :=
  cen_of L1874_ok H1874_ok I1874_ok link1874 cenlink1874

/-! ### `N = 1875` -/

def pL1875 : Prm := ⟨80, 37, 40, 1877, 11, 18446744073709551616, 103690462231457388, 103690462231457388⟩
def pH1875 : Prm := ⟨80, 37, 40, 1877, 11, 18446744073709551616, 103691561743085164, 103691561743085164⟩
def pI1875 : Prm := ⟨68, 34, 31, 1877, 11, 18446744073709551616, 103690462231457388, 103691561743085164⟩
noncomputable def L1875_cp1 : Nat × Nat := t7val% (fastRun pL1875 1 1082 (init pL1875) (init pL1875))
theorem L1875_seg1 : segOK pL1875 1 1082 (init pL1875) (init pL1875) L1875_cp1.1 L1875_cp1.2 = true := by
  decide +kernel
noncomputable def L1875_cp2 : Nat × Nat := t7val% (fastRun pL1875 1 1530 (init pL1875) (init pL1875))
theorem L1875_seg2 : segOK pL1875 1083 448 L1875_cp1.1 L1875_cp1.2 L1875_cp2.1 L1875_cp2.2 = true := by
  decide +kernel
theorem L1875_fin : (prmOK pL1875 1875 && ptTest pL1875 (runFrom pL1875 (fmask pL1875) (cmask pL1875) (hmask pL1875) 1531 344 (true, L1875_cp2.1, L1875_cp2.2)) 1875 938 false) = true := by
  decide +kernel
theorem L1875_ok : RunOK pL1875 1875 (runFrom pL1875 (fmask pL1875) (cmask pL1875) (hmask pL1875) 1531 344 (true, L1875_cp2.1, L1875_cp2.2)) ∧ ptTest pL1875 (runFrom pL1875 (fmask pL1875) (cmask pL1875) (hmask pL1875) 1531 344 (true, L1875_cp2.1, L1875_cp2.2)) 1875 938 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1875_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1875_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1875_fin) true) L1875_seg1) L1875_seg2) (by decide) rfl L1875_fin ptTest_fst
noncomputable def H1875_cp1 : Nat × Nat := t7val% (fastRun pH1875 1 1082 (init pH1875) (init pH1875))
theorem H1875_seg1 : segOK pH1875 1 1082 (init pH1875) (init pH1875) H1875_cp1.1 H1875_cp1.2 = true := by
  decide +kernel
noncomputable def H1875_cp2 : Nat × Nat := t7val% (fastRun pH1875 1 1530 (init pH1875) (init pH1875))
theorem H1875_seg2 : segOK pH1875 1083 448 H1875_cp1.1 H1875_cp1.2 H1875_cp2.1 H1875_cp2.2 = true := by
  decide +kernel
theorem H1875_fin : (prmOK pH1875 1875 && ptTest pH1875 (runFrom pH1875 (fmask pH1875) (cmask pH1875) (hmask pH1875) 1531 344 (true, H1875_cp2.1, H1875_cp2.2)) 1875 938 true) = true := by
  decide +kernel
theorem H1875_ok : RunOK pH1875 1875 (runFrom pH1875 (fmask pH1875) (cmask pH1875) (hmask pH1875) 1531 344 (true, H1875_cp2.1, H1875_cp2.2)) ∧ ptTest pH1875 (runFrom pH1875 (fmask pH1875) (cmask pH1875) (hmask pH1875) 1531 344 (true, H1875_cp2.1, H1875_cp2.2)) 1875 938 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1875_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1875_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1875_fin) true) H1875_seg1) H1875_seg2) (by decide) rfl H1875_fin ptTest_fst
noncomputable def I1875_cp1 : Nat × Nat := t7val% (fastRun pI1875 1 1082 (init pI1875) (init pI1875))
theorem I1875_seg1 : segOK pI1875 1 1082 (init pI1875) (init pI1875) I1875_cp1.1 I1875_cp1.2 = true := by
  decide +kernel
noncomputable def I1875_cp2 : Nat × Nat := t7val% (fastRun pI1875 1 1530 (init pI1875) (init pI1875))
theorem I1875_seg2 : segOK pI1875 1083 448 I1875_cp1.1 I1875_cp1.2 I1875_cp2.1 I1875_cp2.2 = true := by
  decide +kernel
theorem I1875_fin : (prmOK pI1875 1875 && intTest pI1875 (runFrom pI1875 (fmask pI1875) (cmask pI1875) (hmask pI1875) 1531 344 (true, I1875_cp2.1, I1875_cp2.2)) 1875 21 false) = true := by
  decide +kernel
theorem I1875_ok : RunOK pI1875 1875 (runFrom pI1875 (fmask pI1875) (cmask pI1875) (hmask pI1875) 1531 344 (true, I1875_cp2.1, I1875_cp2.2)) ∧ intTest pI1875 (runFrom pI1875 (fmask pI1875) (cmask pI1875) (hmask pI1875) 1531 344 (true, I1875_cp2.1, I1875_cp2.2)) 1875 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1875_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1875_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1875_fin) true) I1875_seg1) I1875_seg2) (by decide) rfl I1875_fin intTest_fst
theorem link1875 : linkOK pL1875 pH1875 pI1875 = true := by decide +kernel
theorem cvx1875 : ConvexBetweenHumps 1875 :=
  cvx_of L1875_ok H1875_ok I1875_ok link1875 (by decide)

/-! ### The range -/

theorem cvx_1865_1875 {N : ℕ} (h1 : 1865 ≤ N) (h2 : N ≤ 1875) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1869
  · by_cases h4 : N ≤ 1866
    · by_cases h6 : N ≤ 1865
      · obtain rfl : N = 1865 := by omega
        exact cvx1865
      · obtain rfl : N = 1866 := by omega
        exact cvx1866
    · by_cases h6 : N ≤ 1867
      · obtain rfl : N = 1867 := by omega
        exact cvx1867
      · by_cases h8 : N ≤ 1868
        · obtain rfl : N = 1868 := by omega
          exact cvx1868
        · obtain rfl : N = 1869 := by omega
          exact cvx1869
  · by_cases h4 : N ≤ 1872
    · by_cases h6 : N ≤ 1870
      · obtain rfl : N = 1870 := by omega
        exact cvx1870
      · by_cases h8 : N ≤ 1871
        · obtain rfl : N = 1871 := by omega
          exact cvx1871
        · obtain rfl : N = 1872 := by omega
          exact cvx1872
    · by_cases h6 : N ≤ 1873
      · obtain rfl : N = 1873 := by omega
        exact cvx1873
      · by_cases h8 : N ≤ 1874
        · obtain rfl : N = 1874 := by omega
          exact cvx1874
        · obtain rfl : N = 1875 := by omega
          exact cvx1875

theorem cen_1865_1875 {N : ℕ} (h1 : 1865 ≤ N) (h2 : N ≤ 1875) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1868
  · by_cases h4 : N ≤ 1866
    · obtain rfl : N = 1866 := by omega
      exact cen1866
    · obtain rfl : N = 1868 := by omega
      exact cen1868
  · by_cases h4 : N ≤ 1870
    · obtain rfl : N = 1870 := by omega
      exact cen1870
    · by_cases h6 : N ≤ 1872
      · obtain rfl : N = 1872 := by omega
        exact cen1872
      · obtain rfl : N = 1874 := by omega
        exact cen1874

end Kagey131.PaperD.T7
