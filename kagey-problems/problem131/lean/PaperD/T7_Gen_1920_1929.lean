import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1920, …, 1929` (generated)

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

/-! ### `N = 1920` -/

def pL1920 : Prm := ⟨80, 37, 40, 1922, 11, 18446744073709551616, 101689720681044195, 101689720681044195⟩
def pH1920 : Prm := ⟨80, 37, 40, 1922, 11, 18446744073709551616, 101690820192671971, 101690820192671971⟩
def pI1920 : Prm := ⟨68, 34, 31, 1922, 11, 18446744073709551616, 101689720681044195, 101690820192671971⟩
noncomputable def L1920_cp1 : Nat × Nat := t7val% (fastRun pL1920 1 1108 (init pL1920) (init pL1920))
theorem L1920_seg1 : segOK pL1920 1 1108 (init pL1920) (init pL1920) L1920_cp1.1 L1920_cp1.2 = true := by
  decide +kernel
noncomputable def L1920_cp2 : Nat × Nat := t7val% (fastRun pL1920 1 1567 (init pL1920) (init pL1920))
theorem L1920_seg2 : segOK pL1920 1109 459 L1920_cp1.1 L1920_cp1.2 L1920_cp2.1 L1920_cp2.2 = true := by
  decide +kernel
theorem L1920_fin : (prmOK pL1920 1920 && ptTest pL1920 (runFrom pL1920 (fmask pL1920) (cmask pL1920) (hmask pL1920) 1568 352 (true, L1920_cp2.1, L1920_cp2.2)) 1920 960 false) = true := by
  decide +kernel
theorem L1920_ok : RunOK pL1920 1920 (runFrom pL1920 (fmask pL1920) (cmask pL1920) (hmask pL1920) 1568 352 (true, L1920_cp2.1, L1920_cp2.2)) ∧ ptTest pL1920 (runFrom pL1920 (fmask pL1920) (cmask pL1920) (hmask pL1920) 1568 352 (true, L1920_cp2.1, L1920_cp2.2)) 1920 960 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1920_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1920_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1920_fin) true) L1920_seg1) L1920_seg2) (by decide) rfl L1920_fin ptTest_fst
noncomputable def H1920_cp1 : Nat × Nat := t7val% (fastRun pH1920 1 1108 (init pH1920) (init pH1920))
theorem H1920_seg1 : segOK pH1920 1 1108 (init pH1920) (init pH1920) H1920_cp1.1 H1920_cp1.2 = true := by
  decide +kernel
noncomputable def H1920_cp2 : Nat × Nat := t7val% (fastRun pH1920 1 1567 (init pH1920) (init pH1920))
theorem H1920_seg2 : segOK pH1920 1109 459 H1920_cp1.1 H1920_cp1.2 H1920_cp2.1 H1920_cp2.2 = true := by
  decide +kernel
theorem H1920_fin : (prmOK pH1920 1920 && ptTest pH1920 (runFrom pH1920 (fmask pH1920) (cmask pH1920) (hmask pH1920) 1568 352 (true, H1920_cp2.1, H1920_cp2.2)) 1920 960 true) = true := by
  decide +kernel
theorem H1920_ok : RunOK pH1920 1920 (runFrom pH1920 (fmask pH1920) (cmask pH1920) (hmask pH1920) 1568 352 (true, H1920_cp2.1, H1920_cp2.2)) ∧ ptTest pH1920 (runFrom pH1920 (fmask pH1920) (cmask pH1920) (hmask pH1920) 1568 352 (true, H1920_cp2.1, H1920_cp2.2)) 1920 960 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1920_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1920_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1920_fin) true) H1920_seg1) H1920_seg2) (by decide) rfl H1920_fin ptTest_fst
noncomputable def I1920_cp1 : Nat × Nat := t7val% (fastRun pI1920 1 1108 (init pI1920) (init pI1920))
theorem I1920_seg1 : segOK pI1920 1 1108 (init pI1920) (init pI1920) I1920_cp1.1 I1920_cp1.2 = true := by
  decide +kernel
noncomputable def I1920_cp2 : Nat × Nat := t7val% (fastRun pI1920 1 1567 (init pI1920) (init pI1920))
theorem I1920_seg2 : segOK pI1920 1109 459 I1920_cp1.1 I1920_cp1.2 I1920_cp2.1 I1920_cp2.2 = true := by
  decide +kernel
theorem I1920_fin : (prmOK pI1920 1920 && intTest pI1920 (runFrom pI1920 (fmask pI1920) (cmask pI1920) (hmask pI1920) 1568 352 (true, I1920_cp2.1, I1920_cp2.2)) 1920 22 true) = true := by
  decide +kernel
theorem I1920_ok : RunOK pI1920 1920 (runFrom pI1920 (fmask pI1920) (cmask pI1920) (hmask pI1920) 1568 352 (true, I1920_cp2.1, I1920_cp2.2)) ∧ intTest pI1920 (runFrom pI1920 (fmask pI1920) (cmask pI1920) (hmask pI1920) 1568 352 (true, I1920_cp2.1, I1920_cp2.2)) 1920 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1920_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1920_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1920_fin) true) I1920_seg1) I1920_seg2) (by decide) rfl I1920_fin intTest_fst
theorem link1920 : linkOK pL1920 pH1920 pI1920 = true := by decide +kernel
theorem cvx1920 : ConvexBetweenHumps 1920 :=
  cvx_of L1920_ok H1920_ok I1920_ok link1920 (by decide)
theorem cenlink1920 : cenLinkOK pI1920 1920 = true := by decide +kernel
theorem cen1920 : CenterUniqueMin 1920 ∧ DipHyp 1920 ∧ OnePointHyps 1920 :=
  cen_of L1920_ok H1920_ok I1920_ok link1920 cenlink1920

/-! ### `N = 1921` -/

def pL1921 : Prm := ⟨80, 37, 40, 1923, 11, 18446744073709551616, 101646201491858443, 101646201491858443⟩
def pH1921 : Prm := ⟨80, 37, 40, 1923, 11, 18446744073709551616, 101647301003486219, 101647301003486219⟩
def pI1921 : Prm := ⟨68, 34, 31, 1923, 11, 18446744073709551616, 101646201491858443, 101647301003486219⟩
noncomputable def L1921_cp1 : Nat × Nat := t7val% (fastRun pL1921 1 1108 (init pL1921) (init pL1921))
theorem L1921_seg1 : segOK pL1921 1 1108 (init pL1921) (init pL1921) L1921_cp1.1 L1921_cp1.2 = true := by
  decide +kernel
noncomputable def L1921_cp2 : Nat × Nat := t7val% (fastRun pL1921 1 1567 (init pL1921) (init pL1921))
theorem L1921_seg2 : segOK pL1921 1109 459 L1921_cp1.1 L1921_cp1.2 L1921_cp2.1 L1921_cp2.2 = true := by
  decide +kernel
theorem L1921_fin : (prmOK pL1921 1921 && ptTest pL1921 (runFrom pL1921 (fmask pL1921) (cmask pL1921) (hmask pL1921) 1568 353 (true, L1921_cp2.1, L1921_cp2.2)) 1921 961 false) = true := by
  decide +kernel
theorem L1921_ok : RunOK pL1921 1921 (runFrom pL1921 (fmask pL1921) (cmask pL1921) (hmask pL1921) 1568 353 (true, L1921_cp2.1, L1921_cp2.2)) ∧ ptTest pL1921 (runFrom pL1921 (fmask pL1921) (cmask pL1921) (hmask pL1921) 1568 353 (true, L1921_cp2.1, L1921_cp2.2)) 1921 961 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1921_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1921_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1921_fin) true) L1921_seg1) L1921_seg2) (by decide) rfl L1921_fin ptTest_fst
noncomputable def H1921_cp1 : Nat × Nat := t7val% (fastRun pH1921 1 1108 (init pH1921) (init pH1921))
theorem H1921_seg1 : segOK pH1921 1 1108 (init pH1921) (init pH1921) H1921_cp1.1 H1921_cp1.2 = true := by
  decide +kernel
noncomputable def H1921_cp2 : Nat × Nat := t7val% (fastRun pH1921 1 1567 (init pH1921) (init pH1921))
theorem H1921_seg2 : segOK pH1921 1109 459 H1921_cp1.1 H1921_cp1.2 H1921_cp2.1 H1921_cp2.2 = true := by
  decide +kernel
theorem H1921_fin : (prmOK pH1921 1921 && ptTest pH1921 (runFrom pH1921 (fmask pH1921) (cmask pH1921) (hmask pH1921) 1568 353 (true, H1921_cp2.1, H1921_cp2.2)) 1921 961 true) = true := by
  decide +kernel
theorem H1921_ok : RunOK pH1921 1921 (runFrom pH1921 (fmask pH1921) (cmask pH1921) (hmask pH1921) 1568 353 (true, H1921_cp2.1, H1921_cp2.2)) ∧ ptTest pH1921 (runFrom pH1921 (fmask pH1921) (cmask pH1921) (hmask pH1921) 1568 353 (true, H1921_cp2.1, H1921_cp2.2)) 1921 961 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1921_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1921_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1921_fin) true) H1921_seg1) H1921_seg2) (by decide) rfl H1921_fin ptTest_fst
noncomputable def I1921_cp1 : Nat × Nat := t7val% (fastRun pI1921 1 1108 (init pI1921) (init pI1921))
theorem I1921_seg1 : segOK pI1921 1 1108 (init pI1921) (init pI1921) I1921_cp1.1 I1921_cp1.2 = true := by
  decide +kernel
noncomputable def I1921_cp2 : Nat × Nat := t7val% (fastRun pI1921 1 1567 (init pI1921) (init pI1921))
theorem I1921_seg2 : segOK pI1921 1109 459 I1921_cp1.1 I1921_cp1.2 I1921_cp2.1 I1921_cp2.2 = true := by
  decide +kernel
theorem I1921_fin : (prmOK pI1921 1921 && intTest pI1921 (runFrom pI1921 (fmask pI1921) (cmask pI1921) (hmask pI1921) 1568 353 (true, I1921_cp2.1, I1921_cp2.2)) 1921 22 false) = true := by
  decide +kernel
theorem I1921_ok : RunOK pI1921 1921 (runFrom pI1921 (fmask pI1921) (cmask pI1921) (hmask pI1921) 1568 353 (true, I1921_cp2.1, I1921_cp2.2)) ∧ intTest pI1921 (runFrom pI1921 (fmask pI1921) (cmask pI1921) (hmask pI1921) 1568 353 (true, I1921_cp2.1, I1921_cp2.2)) 1921 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1921_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1921_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1921_fin) true) I1921_seg1) I1921_seg2) (by decide) rfl I1921_fin intTest_fst
theorem link1921 : linkOK pL1921 pH1921 pI1921 = true := by decide +kernel
theorem cvx1921 : ConvexBetweenHumps 1921 :=
  cvx_of L1921_ok H1921_ok I1921_ok link1921 (by decide)

/-! ### `N = 1922` -/

def pL1922 : Prm := ⟨80, 37, 40, 1924, 11, 18446744073709551616, 101602738457015068, 101602738457015068⟩
def pH1922 : Prm := ⟨80, 37, 40, 1924, 11, 18446744073709551616, 101603837968642844, 101603837968642844⟩
def pI1922 : Prm := ⟨68, 34, 31, 1924, 11, 18446744073709551616, 101602738457015068, 101603837968642844⟩
noncomputable def L1922_cp1 : Nat × Nat := t7val% (fastRun pL1922 1 1109 (init pL1922) (init pL1922))
theorem L1922_seg1 : segOK pL1922 1 1109 (init pL1922) (init pL1922) L1922_cp1.1 L1922_cp1.2 = true := by
  decide +kernel
noncomputable def L1922_cp2 : Nat × Nat := t7val% (fastRun pL1922 1 1568 (init pL1922) (init pL1922))
theorem L1922_seg2 : segOK pL1922 1110 459 L1922_cp1.1 L1922_cp1.2 L1922_cp2.1 L1922_cp2.2 = true := by
  decide +kernel
theorem L1922_fin : (prmOK pL1922 1922 && ptTest pL1922 (runFrom pL1922 (fmask pL1922) (cmask pL1922) (hmask pL1922) 1569 353 (true, L1922_cp2.1, L1922_cp2.2)) 1922 961 false) = true := by
  decide +kernel
theorem L1922_ok : RunOK pL1922 1922 (runFrom pL1922 (fmask pL1922) (cmask pL1922) (hmask pL1922) 1569 353 (true, L1922_cp2.1, L1922_cp2.2)) ∧ ptTest pL1922 (runFrom pL1922 (fmask pL1922) (cmask pL1922) (hmask pL1922) 1569 353 (true, L1922_cp2.1, L1922_cp2.2)) 1922 961 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1922_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1922_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1922_fin) true) L1922_seg1) L1922_seg2) (by decide) rfl L1922_fin ptTest_fst
noncomputable def H1922_cp1 : Nat × Nat := t7val% (fastRun pH1922 1 1109 (init pH1922) (init pH1922))
theorem H1922_seg1 : segOK pH1922 1 1109 (init pH1922) (init pH1922) H1922_cp1.1 H1922_cp1.2 = true := by
  decide +kernel
noncomputable def H1922_cp2 : Nat × Nat := t7val% (fastRun pH1922 1 1568 (init pH1922) (init pH1922))
theorem H1922_seg2 : segOK pH1922 1110 459 H1922_cp1.1 H1922_cp1.2 H1922_cp2.1 H1922_cp2.2 = true := by
  decide +kernel
theorem H1922_fin : (prmOK pH1922 1922 && ptTest pH1922 (runFrom pH1922 (fmask pH1922) (cmask pH1922) (hmask pH1922) 1569 353 (true, H1922_cp2.1, H1922_cp2.2)) 1922 961 true) = true := by
  decide +kernel
theorem H1922_ok : RunOK pH1922 1922 (runFrom pH1922 (fmask pH1922) (cmask pH1922) (hmask pH1922) 1569 353 (true, H1922_cp2.1, H1922_cp2.2)) ∧ ptTest pH1922 (runFrom pH1922 (fmask pH1922) (cmask pH1922) (hmask pH1922) 1569 353 (true, H1922_cp2.1, H1922_cp2.2)) 1922 961 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1922_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1922_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1922_fin) true) H1922_seg1) H1922_seg2) (by decide) rfl H1922_fin ptTest_fst
noncomputable def I1922_cp1 : Nat × Nat := t7val% (fastRun pI1922 1 1109 (init pI1922) (init pI1922))
theorem I1922_seg1 : segOK pI1922 1 1109 (init pI1922) (init pI1922) I1922_cp1.1 I1922_cp1.2 = true := by
  decide +kernel
noncomputable def I1922_cp2 : Nat × Nat := t7val% (fastRun pI1922 1 1568 (init pI1922) (init pI1922))
theorem I1922_seg2 : segOK pI1922 1110 459 I1922_cp1.1 I1922_cp1.2 I1922_cp2.1 I1922_cp2.2 = true := by
  decide +kernel
theorem I1922_fin : (prmOK pI1922 1922 && intTest pI1922 (runFrom pI1922 (fmask pI1922) (cmask pI1922) (hmask pI1922) 1569 353 (true, I1922_cp2.1, I1922_cp2.2)) 1922 22 true) = true := by
  decide +kernel
theorem I1922_ok : RunOK pI1922 1922 (runFrom pI1922 (fmask pI1922) (cmask pI1922) (hmask pI1922) 1569 353 (true, I1922_cp2.1, I1922_cp2.2)) ∧ intTest pI1922 (runFrom pI1922 (fmask pI1922) (cmask pI1922) (hmask pI1922) 1569 353 (true, I1922_cp2.1, I1922_cp2.2)) 1922 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1922_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1922_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1922_fin) true) I1922_seg1) I1922_seg2) (by decide) rfl I1922_fin intTest_fst
theorem link1922 : linkOK pL1922 pH1922 pI1922 = true := by decide +kernel
theorem cvx1922 : ConvexBetweenHumps 1922 :=
  cvx_of L1922_ok H1922_ok I1922_ok link1922 (by decide)
theorem cenlink1922 : cenLinkOK pI1922 1922 = true := by decide +kernel
theorem cen1922 : CenterUniqueMin 1922 ∧ DipHyp 1922 ∧ OnePointHyps 1922 :=
  cen_of L1922_ok H1922_ok I1922_ok link1922 cenlink1922

/-! ### `N = 1923` -/

def pL1923 : Prm := ⟨80, 37, 40, 1925, 11, 18446744073709551616, 101559299971098707, 101559299971098707⟩
def pH1923 : Prm := ⟨80, 37, 40, 1925, 11, 18446744073709551616, 101560399482726483, 101560399482726483⟩
def pI1923 : Prm := ⟨68, 34, 31, 1925, 11, 18446744073709551616, 101559299971098707, 101560399482726483⟩
noncomputable def L1923_cp1 : Nat × Nat := t7val% (fastRun pL1923 1 1109 (init pL1923) (init pL1923))
theorem L1923_seg1 : segOK pL1923 1 1109 (init pL1923) (init pL1923) L1923_cp1.1 L1923_cp1.2 = true := by
  decide +kernel
noncomputable def L1923_cp2 : Nat × Nat := t7val% (fastRun pL1923 1 1569 (init pL1923) (init pL1923))
theorem L1923_seg2 : segOK pL1923 1110 460 L1923_cp1.1 L1923_cp1.2 L1923_cp2.1 L1923_cp2.2 = true := by
  decide +kernel
theorem L1923_fin : (prmOK pL1923 1923 && ptTest pL1923 (runFrom pL1923 (fmask pL1923) (cmask pL1923) (hmask pL1923) 1570 353 (true, L1923_cp2.1, L1923_cp2.2)) 1923 962 false) = true := by
  decide +kernel
theorem L1923_ok : RunOK pL1923 1923 (runFrom pL1923 (fmask pL1923) (cmask pL1923) (hmask pL1923) 1570 353 (true, L1923_cp2.1, L1923_cp2.2)) ∧ ptTest pL1923 (runFrom pL1923 (fmask pL1923) (cmask pL1923) (hmask pL1923) 1570 353 (true, L1923_cp2.1, L1923_cp2.2)) 1923 962 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1923_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1923_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1923_fin) true) L1923_seg1) L1923_seg2) (by decide) rfl L1923_fin ptTest_fst
noncomputable def H1923_cp1 : Nat × Nat := t7val% (fastRun pH1923 1 1109 (init pH1923) (init pH1923))
theorem H1923_seg1 : segOK pH1923 1 1109 (init pH1923) (init pH1923) H1923_cp1.1 H1923_cp1.2 = true := by
  decide +kernel
noncomputable def H1923_cp2 : Nat × Nat := t7val% (fastRun pH1923 1 1569 (init pH1923) (init pH1923))
theorem H1923_seg2 : segOK pH1923 1110 460 H1923_cp1.1 H1923_cp1.2 H1923_cp2.1 H1923_cp2.2 = true := by
  decide +kernel
theorem H1923_fin : (prmOK pH1923 1923 && ptTest pH1923 (runFrom pH1923 (fmask pH1923) (cmask pH1923) (hmask pH1923) 1570 353 (true, H1923_cp2.1, H1923_cp2.2)) 1923 962 true) = true := by
  decide +kernel
theorem H1923_ok : RunOK pH1923 1923 (runFrom pH1923 (fmask pH1923) (cmask pH1923) (hmask pH1923) 1570 353 (true, H1923_cp2.1, H1923_cp2.2)) ∧ ptTest pH1923 (runFrom pH1923 (fmask pH1923) (cmask pH1923) (hmask pH1923) 1570 353 (true, H1923_cp2.1, H1923_cp2.2)) 1923 962 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1923_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1923_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1923_fin) true) H1923_seg1) H1923_seg2) (by decide) rfl H1923_fin ptTest_fst
noncomputable def I1923_cp1 : Nat × Nat := t7val% (fastRun pI1923 1 1109 (init pI1923) (init pI1923))
theorem I1923_seg1 : segOK pI1923 1 1109 (init pI1923) (init pI1923) I1923_cp1.1 I1923_cp1.2 = true := by
  decide +kernel
noncomputable def I1923_cp2 : Nat × Nat := t7val% (fastRun pI1923 1 1569 (init pI1923) (init pI1923))
theorem I1923_seg2 : segOK pI1923 1110 460 I1923_cp1.1 I1923_cp1.2 I1923_cp2.1 I1923_cp2.2 = true := by
  decide +kernel
theorem I1923_fin : (prmOK pI1923 1923 && intTest pI1923 (runFrom pI1923 (fmask pI1923) (cmask pI1923) (hmask pI1923) 1570 353 (true, I1923_cp2.1, I1923_cp2.2)) 1923 22 false) = true := by
  decide +kernel
theorem I1923_ok : RunOK pI1923 1923 (runFrom pI1923 (fmask pI1923) (cmask pI1923) (hmask pI1923) 1570 353 (true, I1923_cp2.1, I1923_cp2.2)) ∧ intTest pI1923 (runFrom pI1923 (fmask pI1923) (cmask pI1923) (hmask pI1923) 1570 353 (true, I1923_cp2.1, I1923_cp2.2)) 1923 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1923_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1923_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1923_fin) true) I1923_seg1) I1923_seg2) (by decide) rfl I1923_fin intTest_fst
theorem link1923 : linkOK pL1923 pH1923 pI1923 = true := by decide +kernel
theorem cvx1923 : ConvexBetweenHumps 1923 :=
  cvx_of L1923_ok H1923_ok I1923_ok link1923 (by decide)

/-! ### `N = 1924` -/

def pL1924 : Prm := ⟨80, 37, 40, 1926, 11, 18446744073709551616, 101515917474002088, 101515917474002088⟩
def pH1924 : Prm := ⟨80, 37, 40, 1926, 11, 18446744073709551616, 101517016985629864, 101517016985629864⟩
def pI1924 : Prm := ⟨68, 34, 31, 1926, 11, 18446744073709551616, 101515917474002088, 101517016985629864⟩
noncomputable def L1924_cp1 : Nat × Nat := t7val% (fastRun pL1924 1 1110 (init pL1924) (init pL1924))
theorem L1924_seg1 : segOK pL1924 1 1110 (init pL1924) (init pL1924) L1924_cp1.1 L1924_cp1.2 = true := by
  decide +kernel
noncomputable def L1924_cp2 : Nat × Nat := t7val% (fastRun pL1924 1 1570 (init pL1924) (init pL1924))
theorem L1924_seg2 : segOK pL1924 1111 460 L1924_cp1.1 L1924_cp1.2 L1924_cp2.1 L1924_cp2.2 = true := by
  decide +kernel
theorem L1924_fin : (prmOK pL1924 1924 && ptTest pL1924 (runFrom pL1924 (fmask pL1924) (cmask pL1924) (hmask pL1924) 1571 353 (true, L1924_cp2.1, L1924_cp2.2)) 1924 962 false) = true := by
  decide +kernel
theorem L1924_ok : RunOK pL1924 1924 (runFrom pL1924 (fmask pL1924) (cmask pL1924) (hmask pL1924) 1571 353 (true, L1924_cp2.1, L1924_cp2.2)) ∧ ptTest pL1924 (runFrom pL1924 (fmask pL1924) (cmask pL1924) (hmask pL1924) 1571 353 (true, L1924_cp2.1, L1924_cp2.2)) 1924 962 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1924_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1924_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1924_fin) true) L1924_seg1) L1924_seg2) (by decide) rfl L1924_fin ptTest_fst
noncomputable def H1924_cp1 : Nat × Nat := t7val% (fastRun pH1924 1 1110 (init pH1924) (init pH1924))
theorem H1924_seg1 : segOK pH1924 1 1110 (init pH1924) (init pH1924) H1924_cp1.1 H1924_cp1.2 = true := by
  decide +kernel
noncomputable def H1924_cp2 : Nat × Nat := t7val% (fastRun pH1924 1 1570 (init pH1924) (init pH1924))
theorem H1924_seg2 : segOK pH1924 1111 460 H1924_cp1.1 H1924_cp1.2 H1924_cp2.1 H1924_cp2.2 = true := by
  decide +kernel
theorem H1924_fin : (prmOK pH1924 1924 && ptTest pH1924 (runFrom pH1924 (fmask pH1924) (cmask pH1924) (hmask pH1924) 1571 353 (true, H1924_cp2.1, H1924_cp2.2)) 1924 962 true) = true := by
  decide +kernel
theorem H1924_ok : RunOK pH1924 1924 (runFrom pH1924 (fmask pH1924) (cmask pH1924) (hmask pH1924) 1571 353 (true, H1924_cp2.1, H1924_cp2.2)) ∧ ptTest pH1924 (runFrom pH1924 (fmask pH1924) (cmask pH1924) (hmask pH1924) 1571 353 (true, H1924_cp2.1, H1924_cp2.2)) 1924 962 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1924_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1924_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1924_fin) true) H1924_seg1) H1924_seg2) (by decide) rfl H1924_fin ptTest_fst
noncomputable def I1924_cp1 : Nat × Nat := t7val% (fastRun pI1924 1 1110 (init pI1924) (init pI1924))
theorem I1924_seg1 : segOK pI1924 1 1110 (init pI1924) (init pI1924) I1924_cp1.1 I1924_cp1.2 = true := by
  decide +kernel
noncomputable def I1924_cp2 : Nat × Nat := t7val% (fastRun pI1924 1 1570 (init pI1924) (init pI1924))
theorem I1924_seg2 : segOK pI1924 1111 460 I1924_cp1.1 I1924_cp1.2 I1924_cp2.1 I1924_cp2.2 = true := by
  decide +kernel
theorem I1924_fin : (prmOK pI1924 1924 && intTest pI1924 (runFrom pI1924 (fmask pI1924) (cmask pI1924) (hmask pI1924) 1571 353 (true, I1924_cp2.1, I1924_cp2.2)) 1924 22 true) = true := by
  decide +kernel
theorem I1924_ok : RunOK pI1924 1924 (runFrom pI1924 (fmask pI1924) (cmask pI1924) (hmask pI1924) 1571 353 (true, I1924_cp2.1, I1924_cp2.2)) ∧ intTest pI1924 (runFrom pI1924 (fmask pI1924) (cmask pI1924) (hmask pI1924) 1571 353 (true, I1924_cp2.1, I1924_cp2.2)) 1924 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1924_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1924_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1924_fin) true) I1924_seg1) I1924_seg2) (by decide) rfl I1924_fin intTest_fst
theorem link1924 : linkOK pL1924 pH1924 pI1924 = true := by decide +kernel
theorem cvx1924 : ConvexBetweenHumps 1924 :=
  cvx_of L1924_ok H1924_ok I1924_ok link1924 (by decide)
theorem cenlink1924 : cenLinkOK pI1924 1924 = true := by decide +kernel
theorem cen1924 : CenterUniqueMin 1924 ∧ DipHyp 1924 ∧ OnePointHyps 1924 :=
  cen_of L1924_ok H1924_ok I1924_ok link1924 cenlink1924

/-! ### `N = 1925` -/

def pL1925 : Prm := ⟨80, 37, 40, 1927, 11, 18446744073709551616, 101472559460235861, 101472559460235861⟩
def pH1925 : Prm := ⟨80, 37, 40, 1927, 11, 18446744073709551616, 101473658971863637, 101473658971863637⟩
def pI1925 : Prm := ⟨68, 34, 31, 1927, 11, 18446744073709551616, 101472559460235861, 101473658971863637⟩
noncomputable def L1925_cp1 : Nat × Nat := t7val% (fastRun pL1925 1 1110 (init pL1925) (init pL1925))
theorem L1925_seg1 : segOK pL1925 1 1110 (init pL1925) (init pL1925) L1925_cp1.1 L1925_cp1.2 = true := by
  decide +kernel
noncomputable def L1925_cp2 : Nat × Nat := t7val% (fastRun pL1925 1 1571 (init pL1925) (init pL1925))
theorem L1925_seg2 : segOK pL1925 1111 461 L1925_cp1.1 L1925_cp1.2 L1925_cp2.1 L1925_cp2.2 = true := by
  decide +kernel
theorem L1925_fin : (prmOK pL1925 1925 && ptTest pL1925 (runFrom pL1925 (fmask pL1925) (cmask pL1925) (hmask pL1925) 1572 353 (true, L1925_cp2.1, L1925_cp2.2)) 1925 963 false) = true := by
  decide +kernel
theorem L1925_ok : RunOK pL1925 1925 (runFrom pL1925 (fmask pL1925) (cmask pL1925) (hmask pL1925) 1572 353 (true, L1925_cp2.1, L1925_cp2.2)) ∧ ptTest pL1925 (runFrom pL1925 (fmask pL1925) (cmask pL1925) (hmask pL1925) 1572 353 (true, L1925_cp2.1, L1925_cp2.2)) 1925 963 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1925_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1925_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1925_fin) true) L1925_seg1) L1925_seg2) (by decide) rfl L1925_fin ptTest_fst
noncomputable def H1925_cp1 : Nat × Nat := t7val% (fastRun pH1925 1 1110 (init pH1925) (init pH1925))
theorem H1925_seg1 : segOK pH1925 1 1110 (init pH1925) (init pH1925) H1925_cp1.1 H1925_cp1.2 = true := by
  decide +kernel
noncomputable def H1925_cp2 : Nat × Nat := t7val% (fastRun pH1925 1 1571 (init pH1925) (init pH1925))
theorem H1925_seg2 : segOK pH1925 1111 461 H1925_cp1.1 H1925_cp1.2 H1925_cp2.1 H1925_cp2.2 = true := by
  decide +kernel
theorem H1925_fin : (prmOK pH1925 1925 && ptTest pH1925 (runFrom pH1925 (fmask pH1925) (cmask pH1925) (hmask pH1925) 1572 353 (true, H1925_cp2.1, H1925_cp2.2)) 1925 963 true) = true := by
  decide +kernel
theorem H1925_ok : RunOK pH1925 1925 (runFrom pH1925 (fmask pH1925) (cmask pH1925) (hmask pH1925) 1572 353 (true, H1925_cp2.1, H1925_cp2.2)) ∧ ptTest pH1925 (runFrom pH1925 (fmask pH1925) (cmask pH1925) (hmask pH1925) 1572 353 (true, H1925_cp2.1, H1925_cp2.2)) 1925 963 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1925_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1925_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1925_fin) true) H1925_seg1) H1925_seg2) (by decide) rfl H1925_fin ptTest_fst
noncomputable def I1925_cp1 : Nat × Nat := t7val% (fastRun pI1925 1 1110 (init pI1925) (init pI1925))
theorem I1925_seg1 : segOK pI1925 1 1110 (init pI1925) (init pI1925) I1925_cp1.1 I1925_cp1.2 = true := by
  decide +kernel
noncomputable def I1925_cp2 : Nat × Nat := t7val% (fastRun pI1925 1 1571 (init pI1925) (init pI1925))
theorem I1925_seg2 : segOK pI1925 1111 461 I1925_cp1.1 I1925_cp1.2 I1925_cp2.1 I1925_cp2.2 = true := by
  decide +kernel
theorem I1925_fin : (prmOK pI1925 1925 && intTest pI1925 (runFrom pI1925 (fmask pI1925) (cmask pI1925) (hmask pI1925) 1572 353 (true, I1925_cp2.1, I1925_cp2.2)) 1925 22 false) = true := by
  decide +kernel
theorem I1925_ok : RunOK pI1925 1925 (runFrom pI1925 (fmask pI1925) (cmask pI1925) (hmask pI1925) 1572 353 (true, I1925_cp2.1, I1925_cp2.2)) ∧ intTest pI1925 (runFrom pI1925 (fmask pI1925) (cmask pI1925) (hmask pI1925) 1572 353 (true, I1925_cp2.1, I1925_cp2.2)) 1925 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1925_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1925_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1925_fin) true) I1925_seg1) I1925_seg2) (by decide) rfl I1925_fin intTest_fst
theorem link1925 : linkOK pL1925 pH1925 pI1925 = true := by decide +kernel
theorem cvx1925 : ConvexBetweenHumps 1925 :=
  cvx_of L1925_ok H1925_ok I1925_ok link1925 (by decide)

/-! ### `N = 1926` -/

def pL1926 : Prm := ⟨80, 37, 40, 1928, 11, 18446744073709551616, 101429257270393931, 101429257270393931⟩
def pH1926 : Prm := ⟨80, 37, 40, 1928, 11, 18446744073709551616, 101430356782021707, 101430356782021707⟩
def pI1926 : Prm := ⟨68, 34, 31, 1928, 11, 18446744073709551616, 101429257270393931, 101430356782021707⟩
noncomputable def L1926_cp1 : Nat × Nat := t7val% (fastRun pL1926 1 1111 (init pL1926) (init pL1926))
theorem L1926_seg1 : segOK pL1926 1 1111 (init pL1926) (init pL1926) L1926_cp1.1 L1926_cp1.2 = true := by
  decide +kernel
noncomputable def L1926_cp2 : Nat × Nat := t7val% (fastRun pL1926 1 1572 (init pL1926) (init pL1926))
theorem L1926_seg2 : segOK pL1926 1112 461 L1926_cp1.1 L1926_cp1.2 L1926_cp2.1 L1926_cp2.2 = true := by
  decide +kernel
theorem L1926_fin : (prmOK pL1926 1926 && ptTest pL1926 (runFrom pL1926 (fmask pL1926) (cmask pL1926) (hmask pL1926) 1573 353 (true, L1926_cp2.1, L1926_cp2.2)) 1926 963 false) = true := by
  decide +kernel
theorem L1926_ok : RunOK pL1926 1926 (runFrom pL1926 (fmask pL1926) (cmask pL1926) (hmask pL1926) 1573 353 (true, L1926_cp2.1, L1926_cp2.2)) ∧ ptTest pL1926 (runFrom pL1926 (fmask pL1926) (cmask pL1926) (hmask pL1926) 1573 353 (true, L1926_cp2.1, L1926_cp2.2)) 1926 963 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1926_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1926_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1926_fin) true) L1926_seg1) L1926_seg2) (by decide) rfl L1926_fin ptTest_fst
noncomputable def H1926_cp1 : Nat × Nat := t7val% (fastRun pH1926 1 1111 (init pH1926) (init pH1926))
theorem H1926_seg1 : segOK pH1926 1 1111 (init pH1926) (init pH1926) H1926_cp1.1 H1926_cp1.2 = true := by
  decide +kernel
noncomputable def H1926_cp2 : Nat × Nat := t7val% (fastRun pH1926 1 1572 (init pH1926) (init pH1926))
theorem H1926_seg2 : segOK pH1926 1112 461 H1926_cp1.1 H1926_cp1.2 H1926_cp2.1 H1926_cp2.2 = true := by
  decide +kernel
theorem H1926_fin : (prmOK pH1926 1926 && ptTest pH1926 (runFrom pH1926 (fmask pH1926) (cmask pH1926) (hmask pH1926) 1573 353 (true, H1926_cp2.1, H1926_cp2.2)) 1926 963 true) = true := by
  decide +kernel
theorem H1926_ok : RunOK pH1926 1926 (runFrom pH1926 (fmask pH1926) (cmask pH1926) (hmask pH1926) 1573 353 (true, H1926_cp2.1, H1926_cp2.2)) ∧ ptTest pH1926 (runFrom pH1926 (fmask pH1926) (cmask pH1926) (hmask pH1926) 1573 353 (true, H1926_cp2.1, H1926_cp2.2)) 1926 963 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1926_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1926_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1926_fin) true) H1926_seg1) H1926_seg2) (by decide) rfl H1926_fin ptTest_fst
noncomputable def I1926_cp1 : Nat × Nat := t7val% (fastRun pI1926 1 1111 (init pI1926) (init pI1926))
theorem I1926_seg1 : segOK pI1926 1 1111 (init pI1926) (init pI1926) I1926_cp1.1 I1926_cp1.2 = true := by
  decide +kernel
noncomputable def I1926_cp2 : Nat × Nat := t7val% (fastRun pI1926 1 1572 (init pI1926) (init pI1926))
theorem I1926_seg2 : segOK pI1926 1112 461 I1926_cp1.1 I1926_cp1.2 I1926_cp2.1 I1926_cp2.2 = true := by
  decide +kernel
theorem I1926_fin : (prmOK pI1926 1926 && intTest pI1926 (runFrom pI1926 (fmask pI1926) (cmask pI1926) (hmask pI1926) 1573 353 (true, I1926_cp2.1, I1926_cp2.2)) 1926 22 true) = true := by
  decide +kernel
theorem I1926_ok : RunOK pI1926 1926 (runFrom pI1926 (fmask pI1926) (cmask pI1926) (hmask pI1926) 1573 353 (true, I1926_cp2.1, I1926_cp2.2)) ∧ intTest pI1926 (runFrom pI1926 (fmask pI1926) (cmask pI1926) (hmask pI1926) 1573 353 (true, I1926_cp2.1, I1926_cp2.2)) 1926 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1926_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1926_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1926_fin) true) I1926_seg1) I1926_seg2) (by decide) rfl I1926_fin intTest_fst
theorem link1926 : linkOK pL1926 pH1926 pI1926 = true := by decide +kernel
theorem cvx1926 : ConvexBetweenHumps 1926 :=
  cvx_of L1926_ok H1926_ok I1926_ok link1926 (by decide)
theorem cenlink1926 : cenLinkOK pI1926 1926 = true := by decide +kernel
theorem cen1926 : CenterUniqueMin 1926 ∧ DipHyp 1926 ∧ OnePointHyps 1926 :=
  cen_of L1926_ok H1926_ok I1926_ok link1926 cenlink1926

/-! ### `N = 1927` -/

def pL1927 : Prm := ⟨80, 37, 40, 1929, 11, 18446744073709551616, 101385979498562472, 101385979498562472⟩
def pH1927 : Prm := ⟨80, 37, 40, 1929, 11, 18446744073709551616, 101387079010190248, 101387079010190248⟩
def pI1927 : Prm := ⟨68, 34, 31, 1929, 11, 18446744073709551616, 101385979498562472, 101387079010190248⟩
noncomputable def L1927_cp1 : Nat × Nat := t7val% (fastRun pL1927 1 1112 (init pL1927) (init pL1927))
theorem L1927_seg1 : segOK pL1927 1 1112 (init pL1927) (init pL1927) L1927_cp1.1 L1927_cp1.2 = true := by
  decide +kernel
noncomputable def L1927_cp2 : Nat × Nat := t7val% (fastRun pL1927 1 1572 (init pL1927) (init pL1927))
theorem L1927_seg2 : segOK pL1927 1113 460 L1927_cp1.1 L1927_cp1.2 L1927_cp2.1 L1927_cp2.2 = true := by
  decide +kernel
theorem L1927_fin : (prmOK pL1927 1927 && ptTest pL1927 (runFrom pL1927 (fmask pL1927) (cmask pL1927) (hmask pL1927) 1573 354 (true, L1927_cp2.1, L1927_cp2.2)) 1927 964 false) = true := by
  decide +kernel
theorem L1927_ok : RunOK pL1927 1927 (runFrom pL1927 (fmask pL1927) (cmask pL1927) (hmask pL1927) 1573 354 (true, L1927_cp2.1, L1927_cp2.2)) ∧ ptTest pL1927 (runFrom pL1927 (fmask pL1927) (cmask pL1927) (hmask pL1927) 1573 354 (true, L1927_cp2.1, L1927_cp2.2)) 1927 964 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1927_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1927_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1927_fin) true) L1927_seg1) L1927_seg2) (by decide) rfl L1927_fin ptTest_fst
noncomputable def H1927_cp1 : Nat × Nat := t7val% (fastRun pH1927 1 1112 (init pH1927) (init pH1927))
theorem H1927_seg1 : segOK pH1927 1 1112 (init pH1927) (init pH1927) H1927_cp1.1 H1927_cp1.2 = true := by
  decide +kernel
noncomputable def H1927_cp2 : Nat × Nat := t7val% (fastRun pH1927 1 1572 (init pH1927) (init pH1927))
theorem H1927_seg2 : segOK pH1927 1113 460 H1927_cp1.1 H1927_cp1.2 H1927_cp2.1 H1927_cp2.2 = true := by
  decide +kernel
theorem H1927_fin : (prmOK pH1927 1927 && ptTest pH1927 (runFrom pH1927 (fmask pH1927) (cmask pH1927) (hmask pH1927) 1573 354 (true, H1927_cp2.1, H1927_cp2.2)) 1927 964 true) = true := by
  decide +kernel
theorem H1927_ok : RunOK pH1927 1927 (runFrom pH1927 (fmask pH1927) (cmask pH1927) (hmask pH1927) 1573 354 (true, H1927_cp2.1, H1927_cp2.2)) ∧ ptTest pH1927 (runFrom pH1927 (fmask pH1927) (cmask pH1927) (hmask pH1927) 1573 354 (true, H1927_cp2.1, H1927_cp2.2)) 1927 964 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1927_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1927_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1927_fin) true) H1927_seg1) H1927_seg2) (by decide) rfl H1927_fin ptTest_fst
noncomputable def I1927_cp1 : Nat × Nat := t7val% (fastRun pI1927 1 1112 (init pI1927) (init pI1927))
theorem I1927_seg1 : segOK pI1927 1 1112 (init pI1927) (init pI1927) I1927_cp1.1 I1927_cp1.2 = true := by
  decide +kernel
noncomputable def I1927_cp2 : Nat × Nat := t7val% (fastRun pI1927 1 1572 (init pI1927) (init pI1927))
theorem I1927_seg2 : segOK pI1927 1113 460 I1927_cp1.1 I1927_cp1.2 I1927_cp2.1 I1927_cp2.2 = true := by
  decide +kernel
theorem I1927_fin : (prmOK pI1927 1927 && intTest pI1927 (runFrom pI1927 (fmask pI1927) (cmask pI1927) (hmask pI1927) 1573 354 (true, I1927_cp2.1, I1927_cp2.2)) 1927 22 false) = true := by
  decide +kernel
theorem I1927_ok : RunOK pI1927 1927 (runFrom pI1927 (fmask pI1927) (cmask pI1927) (hmask pI1927) 1573 354 (true, I1927_cp2.1, I1927_cp2.2)) ∧ intTest pI1927 (runFrom pI1927 (fmask pI1927) (cmask pI1927) (hmask pI1927) 1573 354 (true, I1927_cp2.1, I1927_cp2.2)) 1927 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1927_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1927_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1927_fin) true) I1927_seg1) I1927_seg2) (by decide) rfl I1927_fin intTest_fst
theorem link1927 : linkOK pL1927 pH1927 pI1927 = true := by decide +kernel
theorem cvx1927 : ConvexBetweenHumps 1927 :=
  cvx_of L1927_ok H1927_ok I1927_ok link1927 (by decide)

/-! ### `N = 1928` -/

def pL1928 : Prm := ⟨80, 37, 40, 1930, 11, 18446744073709551616, 101342757386387054, 101342757386387054⟩
def pH1928 : Prm := ⟨81, 38, 40, 1930, 11, 18446744073709551616, 101343856898014830, 101343856898014830⟩
def pI1928 : Prm := ⟨68, 34, 31, 1930, 11, 18446744073709551616, 101342757386387054, 101343856898014830⟩
noncomputable def L1928_cp1 : Nat × Nat := t7val% (fastRun pL1928 1 1112 (init pL1928) (init pL1928))
theorem L1928_seg1 : segOK pL1928 1 1112 (init pL1928) (init pL1928) L1928_cp1.1 L1928_cp1.2 = true := by
  decide +kernel
noncomputable def L1928_cp2 : Nat × Nat := t7val% (fastRun pL1928 1 1573 (init pL1928) (init pL1928))
theorem L1928_seg2 : segOK pL1928 1113 461 L1928_cp1.1 L1928_cp1.2 L1928_cp2.1 L1928_cp2.2 = true := by
  decide +kernel
theorem L1928_fin : (prmOK pL1928 1928 && ptTest pL1928 (runFrom pL1928 (fmask pL1928) (cmask pL1928) (hmask pL1928) 1574 354 (true, L1928_cp2.1, L1928_cp2.2)) 1928 964 false) = true := by
  decide +kernel
theorem L1928_ok : RunOK pL1928 1928 (runFrom pL1928 (fmask pL1928) (cmask pL1928) (hmask pL1928) 1574 354 (true, L1928_cp2.1, L1928_cp2.2)) ∧ ptTest pL1928 (runFrom pL1928 (fmask pL1928) (cmask pL1928) (hmask pL1928) 1574 354 (true, L1928_cp2.1, L1928_cp2.2)) 1928 964 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1928_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1928_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1928_fin) true) L1928_seg1) L1928_seg2) (by decide) rfl L1928_fin ptTest_fst
noncomputable def H1928_cp1 : Nat × Nat := t7val% (fastRun pH1928 1 1112 (init pH1928) (init pH1928))
theorem H1928_seg1 : segOK pH1928 1 1112 (init pH1928) (init pH1928) H1928_cp1.1 H1928_cp1.2 = true := by
  decide +kernel
noncomputable def H1928_cp2 : Nat × Nat := t7val% (fastRun pH1928 1 1573 (init pH1928) (init pH1928))
theorem H1928_seg2 : segOK pH1928 1113 461 H1928_cp1.1 H1928_cp1.2 H1928_cp2.1 H1928_cp2.2 = true := by
  decide +kernel
theorem H1928_fin : (prmOK pH1928 1928 && ptTest pH1928 (runFrom pH1928 (fmask pH1928) (cmask pH1928) (hmask pH1928) 1574 354 (true, H1928_cp2.1, H1928_cp2.2)) 1928 964 true) = true := by
  decide +kernel
theorem H1928_ok : RunOK pH1928 1928 (runFrom pH1928 (fmask pH1928) (cmask pH1928) (hmask pH1928) 1574 354 (true, H1928_cp2.1, H1928_cp2.2)) ∧ ptTest pH1928 (runFrom pH1928 (fmask pH1928) (cmask pH1928) (hmask pH1928) 1574 354 (true, H1928_cp2.1, H1928_cp2.2)) 1928 964 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1928_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1928_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1928_fin) true) H1928_seg1) H1928_seg2) (by decide) rfl H1928_fin ptTest_fst
noncomputable def I1928_cp1 : Nat × Nat := t7val% (fastRun pI1928 1 1112 (init pI1928) (init pI1928))
theorem I1928_seg1 : segOK pI1928 1 1112 (init pI1928) (init pI1928) I1928_cp1.1 I1928_cp1.2 = true := by
  decide +kernel
noncomputable def I1928_cp2 : Nat × Nat := t7val% (fastRun pI1928 1 1573 (init pI1928) (init pI1928))
theorem I1928_seg2 : segOK pI1928 1113 461 I1928_cp1.1 I1928_cp1.2 I1928_cp2.1 I1928_cp2.2 = true := by
  decide +kernel
theorem I1928_fin : (prmOK pI1928 1928 && intTest pI1928 (runFrom pI1928 (fmask pI1928) (cmask pI1928) (hmask pI1928) 1574 354 (true, I1928_cp2.1, I1928_cp2.2)) 1928 22 true) = true := by
  decide +kernel
theorem I1928_ok : RunOK pI1928 1928 (runFrom pI1928 (fmask pI1928) (cmask pI1928) (hmask pI1928) 1574 354 (true, I1928_cp2.1, I1928_cp2.2)) ∧ intTest pI1928 (runFrom pI1928 (fmask pI1928) (cmask pI1928) (hmask pI1928) 1574 354 (true, I1928_cp2.1, I1928_cp2.2)) 1928 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1928_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1928_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1928_fin) true) I1928_seg1) I1928_seg2) (by decide) rfl I1928_fin intTest_fst
theorem link1928 : linkOK pL1928 pH1928 pI1928 = true := by decide +kernel
theorem cvx1928 : ConvexBetweenHumps 1928 :=
  cvx_of L1928_ok H1928_ok I1928_ok link1928 (by decide)
theorem cenlink1928 : cenLinkOK pI1928 1928 = true := by decide +kernel
theorem cen1928 : CenterUniqueMin 1928 ∧ DipHyp 1928 ∧ OnePointHyps 1928 :=
  cen_of L1928_ok H1928_ok I1928_ok link1928 cenlink1928

/-! ### `N = 1929` -/

def pL1929 : Prm := ⟨80, 37, 40, 1931, 11, 18446744073709551616, 101299559627123547, 101299559627123547⟩
def pH1929 : Prm := ⟨80, 37, 40, 1931, 11, 18446744073709551616, 101300659138751323, 101300659138751323⟩
def pI1929 : Prm := ⟨68, 34, 31, 1931, 11, 18446744073709551616, 101299559627123547, 101300659138751323⟩
noncomputable def L1929_cp1 : Nat × Nat := t7val% (fastRun pL1929 1 1113 (init pL1929) (init pL1929))
theorem L1929_seg1 : segOK pL1929 1 1113 (init pL1929) (init pL1929) L1929_cp1.1 L1929_cp1.2 = true := by
  decide +kernel
noncomputable def L1929_cp2 : Nat × Nat := t7val% (fastRun pL1929 1 1574 (init pL1929) (init pL1929))
theorem L1929_seg2 : segOK pL1929 1114 461 L1929_cp1.1 L1929_cp1.2 L1929_cp2.1 L1929_cp2.2 = true := by
  decide +kernel
theorem L1929_fin : (prmOK pL1929 1929 && ptTest pL1929 (runFrom pL1929 (fmask pL1929) (cmask pL1929) (hmask pL1929) 1575 354 (true, L1929_cp2.1, L1929_cp2.2)) 1929 965 false) = true := by
  decide +kernel
theorem L1929_ok : RunOK pL1929 1929 (runFrom pL1929 (fmask pL1929) (cmask pL1929) (hmask pL1929) 1575 354 (true, L1929_cp2.1, L1929_cp2.2)) ∧ ptTest pL1929 (runFrom pL1929 (fmask pL1929) (cmask pL1929) (hmask pL1929) 1575 354 (true, L1929_cp2.1, L1929_cp2.2)) 1929 965 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1929_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1929_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1929_fin) true) L1929_seg1) L1929_seg2) (by decide) rfl L1929_fin ptTest_fst
noncomputable def H1929_cp1 : Nat × Nat := t7val% (fastRun pH1929 1 1113 (init pH1929) (init pH1929))
theorem H1929_seg1 : segOK pH1929 1 1113 (init pH1929) (init pH1929) H1929_cp1.1 H1929_cp1.2 = true := by
  decide +kernel
noncomputable def H1929_cp2 : Nat × Nat := t7val% (fastRun pH1929 1 1574 (init pH1929) (init pH1929))
theorem H1929_seg2 : segOK pH1929 1114 461 H1929_cp1.1 H1929_cp1.2 H1929_cp2.1 H1929_cp2.2 = true := by
  decide +kernel
theorem H1929_fin : (prmOK pH1929 1929 && ptTest pH1929 (runFrom pH1929 (fmask pH1929) (cmask pH1929) (hmask pH1929) 1575 354 (true, H1929_cp2.1, H1929_cp2.2)) 1929 965 true) = true := by
  decide +kernel
theorem H1929_ok : RunOK pH1929 1929 (runFrom pH1929 (fmask pH1929) (cmask pH1929) (hmask pH1929) 1575 354 (true, H1929_cp2.1, H1929_cp2.2)) ∧ ptTest pH1929 (runFrom pH1929 (fmask pH1929) (cmask pH1929) (hmask pH1929) 1575 354 (true, H1929_cp2.1, H1929_cp2.2)) 1929 965 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1929_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1929_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1929_fin) true) H1929_seg1) H1929_seg2) (by decide) rfl H1929_fin ptTest_fst
noncomputable def I1929_cp1 : Nat × Nat := t7val% (fastRun pI1929 1 1113 (init pI1929) (init pI1929))
theorem I1929_seg1 : segOK pI1929 1 1113 (init pI1929) (init pI1929) I1929_cp1.1 I1929_cp1.2 = true := by
  decide +kernel
noncomputable def I1929_cp2 : Nat × Nat := t7val% (fastRun pI1929 1 1574 (init pI1929) (init pI1929))
theorem I1929_seg2 : segOK pI1929 1114 461 I1929_cp1.1 I1929_cp1.2 I1929_cp2.1 I1929_cp2.2 = true := by
  decide +kernel
theorem I1929_fin : (prmOK pI1929 1929 && intTest pI1929 (runFrom pI1929 (fmask pI1929) (cmask pI1929) (hmask pI1929) 1575 354 (true, I1929_cp2.1, I1929_cp2.2)) 1929 22 false) = true := by
  decide +kernel
theorem I1929_ok : RunOK pI1929 1929 (runFrom pI1929 (fmask pI1929) (cmask pI1929) (hmask pI1929) 1575 354 (true, I1929_cp2.1, I1929_cp2.2)) ∧ intTest pI1929 (runFrom pI1929 (fmask pI1929) (cmask pI1929) (hmask pI1929) 1575 354 (true, I1929_cp2.1, I1929_cp2.2)) 1929 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1929_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1929_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1929_fin) true) I1929_seg1) I1929_seg2) (by decide) rfl I1929_fin intTest_fst
theorem link1929 : linkOK pL1929 pH1929 pI1929 = true := by decide +kernel
theorem cvx1929 : ConvexBetweenHumps 1929 :=
  cvx_of L1929_ok H1929_ok I1929_ok link1929 (by decide)

/-! ### The range -/

theorem cvx_1920_1929 {N : ℕ} (h1 : 1920 ≤ N) (h2 : N ≤ 1929) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1924
  · by_cases h4 : N ≤ 1921
    · by_cases h6 : N ≤ 1920
      · obtain rfl : N = 1920 := by omega
        exact cvx1920
      · obtain rfl : N = 1921 := by omega
        exact cvx1921
    · by_cases h6 : N ≤ 1922
      · obtain rfl : N = 1922 := by omega
        exact cvx1922
      · by_cases h8 : N ≤ 1923
        · obtain rfl : N = 1923 := by omega
          exact cvx1923
        · obtain rfl : N = 1924 := by omega
          exact cvx1924
  · by_cases h4 : N ≤ 1926
    · by_cases h6 : N ≤ 1925
      · obtain rfl : N = 1925 := by omega
        exact cvx1925
      · obtain rfl : N = 1926 := by omega
        exact cvx1926
    · by_cases h6 : N ≤ 1927
      · obtain rfl : N = 1927 := by omega
        exact cvx1927
      · by_cases h8 : N ≤ 1928
        · obtain rfl : N = 1928 := by omega
          exact cvx1928
        · obtain rfl : N = 1929 := by omega
          exact cvx1929

theorem cen_1920_1929 {N : ℕ} (h1 : 1920 ≤ N) (h2 : N ≤ 1929) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1922
  · by_cases h4 : N ≤ 1920
    · obtain rfl : N = 1920 := by omega
      exact cen1920
    · obtain rfl : N = 1922 := by omega
      exact cen1922
  · by_cases h4 : N ≤ 1924
    · obtain rfl : N = 1924 := by omega
      exact cen1924
    · by_cases h6 : N ≤ 1926
      · obtain rfl : N = 1926 := by omega
        exact cen1926
      · obtain rfl : N = 1928 := by omega
        exact cen1928

end Kagey131.PaperD.T7
