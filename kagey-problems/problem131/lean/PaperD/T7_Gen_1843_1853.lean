import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1843, …, 1853` (generated)

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

/-! ### `N = 1843` -/

def pL1843 : Prm := ⟨80, 37, 40, 1845, 11, 18446744073709551616, 105166068183078362, 105166068183078362⟩
def pH1843 : Prm := ⟨80, 37, 40, 1845, 11, 18446744073709551616, 105167167694706138, 105167167694706138⟩
def pI1843 : Prm := ⟨68, 34, 31, 1845, 11, 18446744073709551616, 105166068183078362, 105167167694706138⟩
noncomputable def L1843_cp1 : Nat × Nat := t7val% (fastRun pL1843 1 1063 (init pL1843) (init pL1843))
theorem L1843_seg1 : segOK pL1843 1 1063 (init pL1843) (init pL1843) L1843_cp1.1 L1843_cp1.2 = true := by
  decide +kernel
noncomputable def L1843_cp2 : Nat × Nat := t7val% (fastRun pL1843 1 1504 (init pL1843) (init pL1843))
theorem L1843_seg2 : segOK pL1843 1064 441 L1843_cp1.1 L1843_cp1.2 L1843_cp2.1 L1843_cp2.2 = true := by
  decide +kernel
theorem L1843_fin : (prmOK pL1843 1843 && ptTest pL1843 (runFrom pL1843 (fmask pL1843) (cmask pL1843) (hmask pL1843) 1505 338 (true, L1843_cp2.1, L1843_cp2.2)) 1843 922 false) = true := by
  decide +kernel
theorem L1843_ok : RunOK pL1843 1843 (runFrom pL1843 (fmask pL1843) (cmask pL1843) (hmask pL1843) 1505 338 (true, L1843_cp2.1, L1843_cp2.2)) ∧ ptTest pL1843 (runFrom pL1843 (fmask pL1843) (cmask pL1843) (hmask pL1843) 1505 338 (true, L1843_cp2.1, L1843_cp2.2)) 1843 922 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1843_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1843_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1843_fin) true) L1843_seg1) L1843_seg2) (by decide) rfl L1843_fin ptTest_fst
noncomputable def H1843_cp1 : Nat × Nat := t7val% (fastRun pH1843 1 1063 (init pH1843) (init pH1843))
theorem H1843_seg1 : segOK pH1843 1 1063 (init pH1843) (init pH1843) H1843_cp1.1 H1843_cp1.2 = true := by
  decide +kernel
noncomputable def H1843_cp2 : Nat × Nat := t7val% (fastRun pH1843 1 1504 (init pH1843) (init pH1843))
theorem H1843_seg2 : segOK pH1843 1064 441 H1843_cp1.1 H1843_cp1.2 H1843_cp2.1 H1843_cp2.2 = true := by
  decide +kernel
theorem H1843_fin : (prmOK pH1843 1843 && ptTest pH1843 (runFrom pH1843 (fmask pH1843) (cmask pH1843) (hmask pH1843) 1505 338 (true, H1843_cp2.1, H1843_cp2.2)) 1843 922 true) = true := by
  decide +kernel
theorem H1843_ok : RunOK pH1843 1843 (runFrom pH1843 (fmask pH1843) (cmask pH1843) (hmask pH1843) 1505 338 (true, H1843_cp2.1, H1843_cp2.2)) ∧ ptTest pH1843 (runFrom pH1843 (fmask pH1843) (cmask pH1843) (hmask pH1843) 1505 338 (true, H1843_cp2.1, H1843_cp2.2)) 1843 922 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1843_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1843_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1843_fin) true) H1843_seg1) H1843_seg2) (by decide) rfl H1843_fin ptTest_fst
noncomputable def I1843_cp1 : Nat × Nat := t7val% (fastRun pI1843 1 1063 (init pI1843) (init pI1843))
theorem I1843_seg1 : segOK pI1843 1 1063 (init pI1843) (init pI1843) I1843_cp1.1 I1843_cp1.2 = true := by
  decide +kernel
noncomputable def I1843_cp2 : Nat × Nat := t7val% (fastRun pI1843 1 1504 (init pI1843) (init pI1843))
theorem I1843_seg2 : segOK pI1843 1064 441 I1843_cp1.1 I1843_cp1.2 I1843_cp2.1 I1843_cp2.2 = true := by
  decide +kernel
theorem I1843_fin : (prmOK pI1843 1843 && intTest pI1843 (runFrom pI1843 (fmask pI1843) (cmask pI1843) (hmask pI1843) 1505 338 (true, I1843_cp2.1, I1843_cp2.2)) 1843 21 false) = true := by
  decide +kernel
theorem I1843_ok : RunOK pI1843 1843 (runFrom pI1843 (fmask pI1843) (cmask pI1843) (hmask pI1843) 1505 338 (true, I1843_cp2.1, I1843_cp2.2)) ∧ intTest pI1843 (runFrom pI1843 (fmask pI1843) (cmask pI1843) (hmask pI1843) 1505 338 (true, I1843_cp2.1, I1843_cp2.2)) 1843 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1843_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1843_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1843_fin) true) I1843_seg1) I1843_seg2) (by decide) rfl I1843_fin intTest_fst
theorem link1843 : linkOK pL1843 pH1843 pI1843 = true := by decide +kernel
theorem cvx1843 : ConvexBetweenHumps 1843 :=
  cvx_of L1843_ok H1843_ok I1843_ok link1843 (by decide)

/-! ### `N = 1844` -/

def pL1844 : Prm := ⟨80, 37, 40, 1846, 11, 18446744073709551616, 105119274375790839, 105119274375790839⟩
def pH1844 : Prm := ⟨80, 37, 40, 1846, 11, 18446744073709551616, 105120373887418615, 105120373887418615⟩
def pI1844 : Prm := ⟨68, 34, 31, 1846, 11, 18446744073709551616, 105119274375790839, 105120373887418615⟩
noncomputable def L1844_cp1 : Nat × Nat := t7val% (fastRun pL1844 1 1064 (init pL1844) (init pL1844))
theorem L1844_seg1 : segOK pL1844 1 1064 (init pL1844) (init pL1844) L1844_cp1.1 L1844_cp1.2 = true := by
  decide +kernel
noncomputable def L1844_cp2 : Nat × Nat := t7val% (fastRun pL1844 1 1505 (init pL1844) (init pL1844))
theorem L1844_seg2 : segOK pL1844 1065 441 L1844_cp1.1 L1844_cp1.2 L1844_cp2.1 L1844_cp2.2 = true := by
  decide +kernel
theorem L1844_fin : (prmOK pL1844 1844 && ptTest pL1844 (runFrom pL1844 (fmask pL1844) (cmask pL1844) (hmask pL1844) 1506 338 (true, L1844_cp2.1, L1844_cp2.2)) 1844 922 false) = true := by
  decide +kernel
theorem L1844_ok : RunOK pL1844 1844 (runFrom pL1844 (fmask pL1844) (cmask pL1844) (hmask pL1844) 1506 338 (true, L1844_cp2.1, L1844_cp2.2)) ∧ ptTest pL1844 (runFrom pL1844 (fmask pL1844) (cmask pL1844) (hmask pL1844) 1506 338 (true, L1844_cp2.1, L1844_cp2.2)) 1844 922 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1844_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1844_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1844_fin) true) L1844_seg1) L1844_seg2) (by decide) rfl L1844_fin ptTest_fst
noncomputable def H1844_cp1 : Nat × Nat := t7val% (fastRun pH1844 1 1064 (init pH1844) (init pH1844))
theorem H1844_seg1 : segOK pH1844 1 1064 (init pH1844) (init pH1844) H1844_cp1.1 H1844_cp1.2 = true := by
  decide +kernel
noncomputable def H1844_cp2 : Nat × Nat := t7val% (fastRun pH1844 1 1505 (init pH1844) (init pH1844))
theorem H1844_seg2 : segOK pH1844 1065 441 H1844_cp1.1 H1844_cp1.2 H1844_cp2.1 H1844_cp2.2 = true := by
  decide +kernel
theorem H1844_fin : (prmOK pH1844 1844 && ptTest pH1844 (runFrom pH1844 (fmask pH1844) (cmask pH1844) (hmask pH1844) 1506 338 (true, H1844_cp2.1, H1844_cp2.2)) 1844 922 true) = true := by
  decide +kernel
theorem H1844_ok : RunOK pH1844 1844 (runFrom pH1844 (fmask pH1844) (cmask pH1844) (hmask pH1844) 1506 338 (true, H1844_cp2.1, H1844_cp2.2)) ∧ ptTest pH1844 (runFrom pH1844 (fmask pH1844) (cmask pH1844) (hmask pH1844) 1506 338 (true, H1844_cp2.1, H1844_cp2.2)) 1844 922 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1844_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1844_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1844_fin) true) H1844_seg1) H1844_seg2) (by decide) rfl H1844_fin ptTest_fst
noncomputable def I1844_cp1 : Nat × Nat := t7val% (fastRun pI1844 1 1064 (init pI1844) (init pI1844))
theorem I1844_seg1 : segOK pI1844 1 1064 (init pI1844) (init pI1844) I1844_cp1.1 I1844_cp1.2 = true := by
  decide +kernel
noncomputable def I1844_cp2 : Nat × Nat := t7val% (fastRun pI1844 1 1505 (init pI1844) (init pI1844))
theorem I1844_seg2 : segOK pI1844 1065 441 I1844_cp1.1 I1844_cp1.2 I1844_cp2.1 I1844_cp2.2 = true := by
  decide +kernel
theorem I1844_fin : (prmOK pI1844 1844 && intTest pI1844 (runFrom pI1844 (fmask pI1844) (cmask pI1844) (hmask pI1844) 1506 338 (true, I1844_cp2.1, I1844_cp2.2)) 1844 21 true) = true := by
  decide +kernel
theorem I1844_ok : RunOK pI1844 1844 (runFrom pI1844 (fmask pI1844) (cmask pI1844) (hmask pI1844) 1506 338 (true, I1844_cp2.1, I1844_cp2.2)) ∧ intTest pI1844 (runFrom pI1844 (fmask pI1844) (cmask pI1844) (hmask pI1844) 1506 338 (true, I1844_cp2.1, I1844_cp2.2)) 1844 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1844_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1844_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1844_fin) true) I1844_seg1) I1844_seg2) (by decide) rfl I1844_fin intTest_fst
theorem link1844 : linkOK pL1844 pH1844 pI1844 = true := by decide +kernel
theorem cvx1844 : ConvexBetweenHumps 1844 :=
  cvx_of L1844_ok H1844_ok I1844_ok link1844 (by decide)
theorem cenlink1844 : cenLinkOK pI1844 1844 = true := by decide +kernel
theorem cen1844 : CenterUniqueMin 1844 ∧ DipHyp 1844 ∧ OnePointHyps 1844 :=
  cen_of L1844_ok H1844_ok I1844_ok link1844 cenlink1844

/-! ### `N = 1845` -/

def pL1845 : Prm := ⟨80, 37, 40, 1847, 11, 18446744073709551616, 105072507873004960, 105072507873004960⟩
def pH1845 : Prm := ⟨80, 37, 40, 1847, 11, 18446744073709551616, 105073607384632736, 105073607384632736⟩
def pI1845 : Prm := ⟨68, 34, 31, 1847, 11, 18446744073709551616, 105072507873004960, 105073607384632736⟩
noncomputable def L1845_cp1 : Nat × Nat := t7val% (fastRun pL1845 1 1064 (init pL1845) (init pL1845))
theorem L1845_seg1 : segOK pL1845 1 1064 (init pL1845) (init pL1845) L1845_cp1.1 L1845_cp1.2 = true := by
  decide +kernel
noncomputable def L1845_cp2 : Nat × Nat := t7val% (fastRun pL1845 1 1505 (init pL1845) (init pL1845))
theorem L1845_seg2 : segOK pL1845 1065 441 L1845_cp1.1 L1845_cp1.2 L1845_cp2.1 L1845_cp2.2 = true := by
  decide +kernel
theorem L1845_fin : (prmOK pL1845 1845 && ptTest pL1845 (runFrom pL1845 (fmask pL1845) (cmask pL1845) (hmask pL1845) 1506 339 (true, L1845_cp2.1, L1845_cp2.2)) 1845 923 false) = true := by
  decide +kernel
theorem L1845_ok : RunOK pL1845 1845 (runFrom pL1845 (fmask pL1845) (cmask pL1845) (hmask pL1845) 1506 339 (true, L1845_cp2.1, L1845_cp2.2)) ∧ ptTest pL1845 (runFrom pL1845 (fmask pL1845) (cmask pL1845) (hmask pL1845) 1506 339 (true, L1845_cp2.1, L1845_cp2.2)) 1845 923 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1845_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1845_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1845_fin) true) L1845_seg1) L1845_seg2) (by decide) rfl L1845_fin ptTest_fst
noncomputable def H1845_cp1 : Nat × Nat := t7val% (fastRun pH1845 1 1064 (init pH1845) (init pH1845))
theorem H1845_seg1 : segOK pH1845 1 1064 (init pH1845) (init pH1845) H1845_cp1.1 H1845_cp1.2 = true := by
  decide +kernel
noncomputable def H1845_cp2 : Nat × Nat := t7val% (fastRun pH1845 1 1505 (init pH1845) (init pH1845))
theorem H1845_seg2 : segOK pH1845 1065 441 H1845_cp1.1 H1845_cp1.2 H1845_cp2.1 H1845_cp2.2 = true := by
  decide +kernel
theorem H1845_fin : (prmOK pH1845 1845 && ptTest pH1845 (runFrom pH1845 (fmask pH1845) (cmask pH1845) (hmask pH1845) 1506 339 (true, H1845_cp2.1, H1845_cp2.2)) 1845 923 true) = true := by
  decide +kernel
theorem H1845_ok : RunOK pH1845 1845 (runFrom pH1845 (fmask pH1845) (cmask pH1845) (hmask pH1845) 1506 339 (true, H1845_cp2.1, H1845_cp2.2)) ∧ ptTest pH1845 (runFrom pH1845 (fmask pH1845) (cmask pH1845) (hmask pH1845) 1506 339 (true, H1845_cp2.1, H1845_cp2.2)) 1845 923 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1845_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1845_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1845_fin) true) H1845_seg1) H1845_seg2) (by decide) rfl H1845_fin ptTest_fst
noncomputable def I1845_cp1 : Nat × Nat := t7val% (fastRun pI1845 1 1064 (init pI1845) (init pI1845))
theorem I1845_seg1 : segOK pI1845 1 1064 (init pI1845) (init pI1845) I1845_cp1.1 I1845_cp1.2 = true := by
  decide +kernel
noncomputable def I1845_cp2 : Nat × Nat := t7val% (fastRun pI1845 1 1505 (init pI1845) (init pI1845))
theorem I1845_seg2 : segOK pI1845 1065 441 I1845_cp1.1 I1845_cp1.2 I1845_cp2.1 I1845_cp2.2 = true := by
  decide +kernel
theorem I1845_fin : (prmOK pI1845 1845 && intTest pI1845 (runFrom pI1845 (fmask pI1845) (cmask pI1845) (hmask pI1845) 1506 339 (true, I1845_cp2.1, I1845_cp2.2)) 1845 21 false) = true := by
  decide +kernel
theorem I1845_ok : RunOK pI1845 1845 (runFrom pI1845 (fmask pI1845) (cmask pI1845) (hmask pI1845) 1506 339 (true, I1845_cp2.1, I1845_cp2.2)) ∧ intTest pI1845 (runFrom pI1845 (fmask pI1845) (cmask pI1845) (hmask pI1845) 1506 339 (true, I1845_cp2.1, I1845_cp2.2)) 1845 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1845_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1845_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1845_fin) true) I1845_seg1) I1845_seg2) (by decide) rfl I1845_fin intTest_fst
theorem link1845 : linkOK pL1845 pH1845 pI1845 = true := by decide +kernel
theorem cvx1845 : ConvexBetweenHumps 1845 :=
  cvx_of L1845_ok H1845_ok I1845_ok link1845 (by decide)

/-! ### `N = 1846` -/

def pL1846 : Prm := ⟨80, 37, 40, 1848, 11, 18446744073709551616, 105025804337847934, 105025804337847934⟩
def pH1846 : Prm := ⟨80, 37, 40, 1848, 11, 18446744073709551616, 105026903849475710, 105026903849475710⟩
def pI1846 : Prm := ⟨68, 34, 31, 1848, 11, 18446744073709551616, 105025804337847934, 105026903849475710⟩
noncomputable def L1846_cp1 : Nat × Nat := t7val% (fastRun pL1846 1 1065 (init pL1846) (init pL1846))
theorem L1846_seg1 : segOK pL1846 1 1065 (init pL1846) (init pL1846) L1846_cp1.1 L1846_cp1.2 = true := by
  decide +kernel
noncomputable def L1846_cp2 : Nat × Nat := t7val% (fastRun pL1846 1 1506 (init pL1846) (init pL1846))
theorem L1846_seg2 : segOK pL1846 1066 441 L1846_cp1.1 L1846_cp1.2 L1846_cp2.1 L1846_cp2.2 = true := by
  decide +kernel
theorem L1846_fin : (prmOK pL1846 1846 && ptTest pL1846 (runFrom pL1846 (fmask pL1846) (cmask pL1846) (hmask pL1846) 1507 339 (true, L1846_cp2.1, L1846_cp2.2)) 1846 923 false) = true := by
  decide +kernel
theorem L1846_ok : RunOK pL1846 1846 (runFrom pL1846 (fmask pL1846) (cmask pL1846) (hmask pL1846) 1507 339 (true, L1846_cp2.1, L1846_cp2.2)) ∧ ptTest pL1846 (runFrom pL1846 (fmask pL1846) (cmask pL1846) (hmask pL1846) 1507 339 (true, L1846_cp2.1, L1846_cp2.2)) 1846 923 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1846_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1846_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1846_fin) true) L1846_seg1) L1846_seg2) (by decide) rfl L1846_fin ptTest_fst
noncomputable def H1846_cp1 : Nat × Nat := t7val% (fastRun pH1846 1 1065 (init pH1846) (init pH1846))
theorem H1846_seg1 : segOK pH1846 1 1065 (init pH1846) (init pH1846) H1846_cp1.1 H1846_cp1.2 = true := by
  decide +kernel
noncomputable def H1846_cp2 : Nat × Nat := t7val% (fastRun pH1846 1 1506 (init pH1846) (init pH1846))
theorem H1846_seg2 : segOK pH1846 1066 441 H1846_cp1.1 H1846_cp1.2 H1846_cp2.1 H1846_cp2.2 = true := by
  decide +kernel
theorem H1846_fin : (prmOK pH1846 1846 && ptTest pH1846 (runFrom pH1846 (fmask pH1846) (cmask pH1846) (hmask pH1846) 1507 339 (true, H1846_cp2.1, H1846_cp2.2)) 1846 923 true) = true := by
  decide +kernel
theorem H1846_ok : RunOK pH1846 1846 (runFrom pH1846 (fmask pH1846) (cmask pH1846) (hmask pH1846) 1507 339 (true, H1846_cp2.1, H1846_cp2.2)) ∧ ptTest pH1846 (runFrom pH1846 (fmask pH1846) (cmask pH1846) (hmask pH1846) 1507 339 (true, H1846_cp2.1, H1846_cp2.2)) 1846 923 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1846_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1846_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1846_fin) true) H1846_seg1) H1846_seg2) (by decide) rfl H1846_fin ptTest_fst
noncomputable def I1846_cp1 : Nat × Nat := t7val% (fastRun pI1846 1 1065 (init pI1846) (init pI1846))
theorem I1846_seg1 : segOK pI1846 1 1065 (init pI1846) (init pI1846) I1846_cp1.1 I1846_cp1.2 = true := by
  decide +kernel
noncomputable def I1846_cp2 : Nat × Nat := t7val% (fastRun pI1846 1 1506 (init pI1846) (init pI1846))
theorem I1846_seg2 : segOK pI1846 1066 441 I1846_cp1.1 I1846_cp1.2 I1846_cp2.1 I1846_cp2.2 = true := by
  decide +kernel
theorem I1846_fin : (prmOK pI1846 1846 && intTest pI1846 (runFrom pI1846 (fmask pI1846) (cmask pI1846) (hmask pI1846) 1507 339 (true, I1846_cp2.1, I1846_cp2.2)) 1846 21 true) = true := by
  decide +kernel
theorem I1846_ok : RunOK pI1846 1846 (runFrom pI1846 (fmask pI1846) (cmask pI1846) (hmask pI1846) 1507 339 (true, I1846_cp2.1, I1846_cp2.2)) ∧ intTest pI1846 (runFrom pI1846 (fmask pI1846) (cmask pI1846) (hmask pI1846) 1507 339 (true, I1846_cp2.1, I1846_cp2.2)) 1846 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1846_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1846_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1846_fin) true) I1846_seg1) I1846_seg2) (by decide) rfl I1846_fin intTest_fst
theorem link1846 : linkOK pL1846 pH1846 pI1846 = true := by decide +kernel
theorem cvx1846 : ConvexBetweenHumps 1846 :=
  cvx_of L1846_ok H1846_ok I1846_ok link1846 (by decide)
theorem cenlink1846 : cenLinkOK pI1846 1846 = true := by decide +kernel
theorem cen1846 : CenterUniqueMin 1846 ∧ DipHyp 1846 ∧ OnePointHyps 1846 :=
  cen_of L1846_ok H1846_ok I1846_ok link1846 cenlink1846

/-! ### `N = 1847` -/

def pL1847 : Prm := ⟨80, 37, 40, 1849, 11, 18446744073709551616, 104979128031431774, 104979128031431774⟩
def pH1847 : Prm := ⟨80, 37, 40, 1849, 11, 18446744073709551616, 104980227543059550, 104980227543059550⟩
def pI1847 : Prm := ⟨68, 34, 31, 1849, 11, 18446744073709551616, 104979128031431774, 104980227543059550⟩
noncomputable def L1847_cp1 : Nat × Nat := t7val% (fastRun pL1847 1 1065 (init pL1847) (init pL1847))
theorem L1847_seg1 : segOK pL1847 1 1065 (init pL1847) (init pL1847) L1847_cp1.1 L1847_cp1.2 = true := by
  decide +kernel
noncomputable def L1847_cp2 : Nat × Nat := t7val% (fastRun pL1847 1 1507 (init pL1847) (init pL1847))
theorem L1847_seg2 : segOK pL1847 1066 442 L1847_cp1.1 L1847_cp1.2 L1847_cp2.1 L1847_cp2.2 = true := by
  decide +kernel
theorem L1847_fin : (prmOK pL1847 1847 && ptTest pL1847 (runFrom pL1847 (fmask pL1847) (cmask pL1847) (hmask pL1847) 1508 339 (true, L1847_cp2.1, L1847_cp2.2)) 1847 924 false) = true := by
  decide +kernel
theorem L1847_ok : RunOK pL1847 1847 (runFrom pL1847 (fmask pL1847) (cmask pL1847) (hmask pL1847) 1508 339 (true, L1847_cp2.1, L1847_cp2.2)) ∧ ptTest pL1847 (runFrom pL1847 (fmask pL1847) (cmask pL1847) (hmask pL1847) 1508 339 (true, L1847_cp2.1, L1847_cp2.2)) 1847 924 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1847_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1847_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1847_fin) true) L1847_seg1) L1847_seg2) (by decide) rfl L1847_fin ptTest_fst
noncomputable def H1847_cp1 : Nat × Nat := t7val% (fastRun pH1847 1 1065 (init pH1847) (init pH1847))
theorem H1847_seg1 : segOK pH1847 1 1065 (init pH1847) (init pH1847) H1847_cp1.1 H1847_cp1.2 = true := by
  decide +kernel
noncomputable def H1847_cp2 : Nat × Nat := t7val% (fastRun pH1847 1 1507 (init pH1847) (init pH1847))
theorem H1847_seg2 : segOK pH1847 1066 442 H1847_cp1.1 H1847_cp1.2 H1847_cp2.1 H1847_cp2.2 = true := by
  decide +kernel
theorem H1847_fin : (prmOK pH1847 1847 && ptTest pH1847 (runFrom pH1847 (fmask pH1847) (cmask pH1847) (hmask pH1847) 1508 339 (true, H1847_cp2.1, H1847_cp2.2)) 1847 924 true) = true := by
  decide +kernel
theorem H1847_ok : RunOK pH1847 1847 (runFrom pH1847 (fmask pH1847) (cmask pH1847) (hmask pH1847) 1508 339 (true, H1847_cp2.1, H1847_cp2.2)) ∧ ptTest pH1847 (runFrom pH1847 (fmask pH1847) (cmask pH1847) (hmask pH1847) 1508 339 (true, H1847_cp2.1, H1847_cp2.2)) 1847 924 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1847_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1847_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1847_fin) true) H1847_seg1) H1847_seg2) (by decide) rfl H1847_fin ptTest_fst
noncomputable def I1847_cp1 : Nat × Nat := t7val% (fastRun pI1847 1 1065 (init pI1847) (init pI1847))
theorem I1847_seg1 : segOK pI1847 1 1065 (init pI1847) (init pI1847) I1847_cp1.1 I1847_cp1.2 = true := by
  decide +kernel
noncomputable def I1847_cp2 : Nat × Nat := t7val% (fastRun pI1847 1 1507 (init pI1847) (init pI1847))
theorem I1847_seg2 : segOK pI1847 1066 442 I1847_cp1.1 I1847_cp1.2 I1847_cp2.1 I1847_cp2.2 = true := by
  decide +kernel
theorem I1847_fin : (prmOK pI1847 1847 && intTest pI1847 (runFrom pI1847 (fmask pI1847) (cmask pI1847) (hmask pI1847) 1508 339 (true, I1847_cp2.1, I1847_cp2.2)) 1847 21 false) = true := by
  decide +kernel
theorem I1847_ok : RunOK pI1847 1847 (runFrom pI1847 (fmask pI1847) (cmask pI1847) (hmask pI1847) 1508 339 (true, I1847_cp2.1, I1847_cp2.2)) ∧ intTest pI1847 (runFrom pI1847 (fmask pI1847) (cmask pI1847) (hmask pI1847) 1508 339 (true, I1847_cp2.1, I1847_cp2.2)) 1847 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1847_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1847_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1847_fin) true) I1847_seg1) I1847_seg2) (by decide) rfl I1847_fin intTest_fst
theorem link1847 : linkOK pL1847 pH1847 pI1847 = true := by decide +kernel
theorem cvx1847 : ConvexBetweenHumps 1847 :=
  cvx_of L1847_ok H1847_ok I1847_ok link1847 (by decide)

/-! ### `N = 1848` -/

def pL1848 : Prm := ⟨80, 37, 40, 1850, 11, 18446744073709551616, 104932514499433271, 104932514499433271⟩
def pH1848 : Prm := ⟨80, 37, 40, 1850, 11, 18446744073709551616, 104933614011061047, 104933614011061047⟩
def pI1848 : Prm := ⟨68, 34, 31, 1850, 11, 18446744073709551616, 104932514499433271, 104933614011061047⟩
noncomputable def L1848_cp1 : Nat × Nat := t7val% (fastRun pL1848 1 1066 (init pL1848) (init pL1848))
theorem L1848_seg1 : segOK pL1848 1 1066 (init pL1848) (init pL1848) L1848_cp1.1 L1848_cp1.2 = true := by
  decide +kernel
noncomputable def L1848_cp2 : Nat × Nat := t7val% (fastRun pL1848 1 1508 (init pL1848) (init pL1848))
theorem L1848_seg2 : segOK pL1848 1067 442 L1848_cp1.1 L1848_cp1.2 L1848_cp2.1 L1848_cp2.2 = true := by
  decide +kernel
theorem L1848_fin : (prmOK pL1848 1848 && ptTest pL1848 (runFrom pL1848 (fmask pL1848) (cmask pL1848) (hmask pL1848) 1509 339 (true, L1848_cp2.1, L1848_cp2.2)) 1848 924 false) = true := by
  decide +kernel
theorem L1848_ok : RunOK pL1848 1848 (runFrom pL1848 (fmask pL1848) (cmask pL1848) (hmask pL1848) 1509 339 (true, L1848_cp2.1, L1848_cp2.2)) ∧ ptTest pL1848 (runFrom pL1848 (fmask pL1848) (cmask pL1848) (hmask pL1848) 1509 339 (true, L1848_cp2.1, L1848_cp2.2)) 1848 924 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1848_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1848_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1848_fin) true) L1848_seg1) L1848_seg2) (by decide) rfl L1848_fin ptTest_fst
noncomputable def H1848_cp1 : Nat × Nat := t7val% (fastRun pH1848 1 1066 (init pH1848) (init pH1848))
theorem H1848_seg1 : segOK pH1848 1 1066 (init pH1848) (init pH1848) H1848_cp1.1 H1848_cp1.2 = true := by
  decide +kernel
noncomputable def H1848_cp2 : Nat × Nat := t7val% (fastRun pH1848 1 1508 (init pH1848) (init pH1848))
theorem H1848_seg2 : segOK pH1848 1067 442 H1848_cp1.1 H1848_cp1.2 H1848_cp2.1 H1848_cp2.2 = true := by
  decide +kernel
theorem H1848_fin : (prmOK pH1848 1848 && ptTest pH1848 (runFrom pH1848 (fmask pH1848) (cmask pH1848) (hmask pH1848) 1509 339 (true, H1848_cp2.1, H1848_cp2.2)) 1848 924 true) = true := by
  decide +kernel
theorem H1848_ok : RunOK pH1848 1848 (runFrom pH1848 (fmask pH1848) (cmask pH1848) (hmask pH1848) 1509 339 (true, H1848_cp2.1, H1848_cp2.2)) ∧ ptTest pH1848 (runFrom pH1848 (fmask pH1848) (cmask pH1848) (hmask pH1848) 1509 339 (true, H1848_cp2.1, H1848_cp2.2)) 1848 924 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1848_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1848_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1848_fin) true) H1848_seg1) H1848_seg2) (by decide) rfl H1848_fin ptTest_fst
noncomputable def I1848_cp1 : Nat × Nat := t7val% (fastRun pI1848 1 1066 (init pI1848) (init pI1848))
theorem I1848_seg1 : segOK pI1848 1 1066 (init pI1848) (init pI1848) I1848_cp1.1 I1848_cp1.2 = true := by
  decide +kernel
noncomputable def I1848_cp2 : Nat × Nat := t7val% (fastRun pI1848 1 1508 (init pI1848) (init pI1848))
theorem I1848_seg2 : segOK pI1848 1067 442 I1848_cp1.1 I1848_cp1.2 I1848_cp2.1 I1848_cp2.2 = true := by
  decide +kernel
theorem I1848_fin : (prmOK pI1848 1848 && intTest pI1848 (runFrom pI1848 (fmask pI1848) (cmask pI1848) (hmask pI1848) 1509 339 (true, I1848_cp2.1, I1848_cp2.2)) 1848 21 true) = true := by
  decide +kernel
theorem I1848_ok : RunOK pI1848 1848 (runFrom pI1848 (fmask pI1848) (cmask pI1848) (hmask pI1848) 1509 339 (true, I1848_cp2.1, I1848_cp2.2)) ∧ intTest pI1848 (runFrom pI1848 (fmask pI1848) (cmask pI1848) (hmask pI1848) 1509 339 (true, I1848_cp2.1, I1848_cp2.2)) 1848 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1848_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1848_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1848_fin) true) I1848_seg1) I1848_seg2) (by decide) rfl I1848_fin intTest_fst
theorem link1848 : linkOK pL1848 pH1848 pI1848 = true := by decide +kernel
theorem cvx1848 : ConvexBetweenHumps 1848 :=
  cvx_of L1848_ok H1848_ok I1848_ok link1848 (by decide)
theorem cenlink1848 : cenLinkOK pI1848 1848 = true := by decide +kernel
theorem cen1848 : CenterUniqueMin 1848 ∧ DipHyp 1848 ∧ OnePointHyps 1848 :=
  cen_of L1848_ok H1848_ok I1848_ok link1848 cenlink1848

/-! ### `N = 1849` -/

def pL1849 : Prm := ⟨80, 37, 40, 1851, 11, 18446744073709551616, 104885928120636215, 104885928120636215⟩
def pH1849 : Prm := ⟨80, 37, 40, 1851, 11, 18446744073709551616, 104887027632263991, 104887027632263991⟩
def pI1849 : Prm := ⟨68, 34, 31, 1851, 11, 18446744073709551616, 104885928120636215, 104887027632263991⟩
noncomputable def L1849_cp1 : Nat × Nat := t7val% (fastRun pL1849 1 1067 (init pL1849) (init pL1849))
theorem L1849_seg1 : segOK pL1849 1 1067 (init pL1849) (init pL1849) L1849_cp1.1 L1849_cp1.2 = true := by
  decide +kernel
noncomputable def L1849_cp2 : Nat × Nat := t7val% (fastRun pL1849 1 1509 (init pL1849) (init pL1849))
theorem L1849_seg2 : segOK pL1849 1068 442 L1849_cp1.1 L1849_cp1.2 L1849_cp2.1 L1849_cp2.2 = true := by
  decide +kernel
theorem L1849_fin : (prmOK pL1849 1849 && ptTest pL1849 (runFrom pL1849 (fmask pL1849) (cmask pL1849) (hmask pL1849) 1510 339 (true, L1849_cp2.1, L1849_cp2.2)) 1849 925 false) = true := by
  decide +kernel
theorem L1849_ok : RunOK pL1849 1849 (runFrom pL1849 (fmask pL1849) (cmask pL1849) (hmask pL1849) 1510 339 (true, L1849_cp2.1, L1849_cp2.2)) ∧ ptTest pL1849 (runFrom pL1849 (fmask pL1849) (cmask pL1849) (hmask pL1849) 1510 339 (true, L1849_cp2.1, L1849_cp2.2)) 1849 925 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1849_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1849_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1849_fin) true) L1849_seg1) L1849_seg2) (by decide) rfl L1849_fin ptTest_fst
noncomputable def H1849_cp1 : Nat × Nat := t7val% (fastRun pH1849 1 1067 (init pH1849) (init pH1849))
theorem H1849_seg1 : segOK pH1849 1 1067 (init pH1849) (init pH1849) H1849_cp1.1 H1849_cp1.2 = true := by
  decide +kernel
noncomputable def H1849_cp2 : Nat × Nat := t7val% (fastRun pH1849 1 1509 (init pH1849) (init pH1849))
theorem H1849_seg2 : segOK pH1849 1068 442 H1849_cp1.1 H1849_cp1.2 H1849_cp2.1 H1849_cp2.2 = true := by
  decide +kernel
theorem H1849_fin : (prmOK pH1849 1849 && ptTest pH1849 (runFrom pH1849 (fmask pH1849) (cmask pH1849) (hmask pH1849) 1510 339 (true, H1849_cp2.1, H1849_cp2.2)) 1849 925 true) = true := by
  decide +kernel
theorem H1849_ok : RunOK pH1849 1849 (runFrom pH1849 (fmask pH1849) (cmask pH1849) (hmask pH1849) 1510 339 (true, H1849_cp2.1, H1849_cp2.2)) ∧ ptTest pH1849 (runFrom pH1849 (fmask pH1849) (cmask pH1849) (hmask pH1849) 1510 339 (true, H1849_cp2.1, H1849_cp2.2)) 1849 925 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1849_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1849_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1849_fin) true) H1849_seg1) H1849_seg2) (by decide) rfl H1849_fin ptTest_fst
noncomputable def I1849_cp1 : Nat × Nat := t7val% (fastRun pI1849 1 1067 (init pI1849) (init pI1849))
theorem I1849_seg1 : segOK pI1849 1 1067 (init pI1849) (init pI1849) I1849_cp1.1 I1849_cp1.2 = true := by
  decide +kernel
noncomputable def I1849_cp2 : Nat × Nat := t7val% (fastRun pI1849 1 1509 (init pI1849) (init pI1849))
theorem I1849_seg2 : segOK pI1849 1068 442 I1849_cp1.1 I1849_cp1.2 I1849_cp2.1 I1849_cp2.2 = true := by
  decide +kernel
theorem I1849_fin : (prmOK pI1849 1849 && intTest pI1849 (runFrom pI1849 (fmask pI1849) (cmask pI1849) (hmask pI1849) 1510 339 (true, I1849_cp2.1, I1849_cp2.2)) 1849 21 false) = true := by
  decide +kernel
theorem I1849_ok : RunOK pI1849 1849 (runFrom pI1849 (fmask pI1849) (cmask pI1849) (hmask pI1849) 1510 339 (true, I1849_cp2.1, I1849_cp2.2)) ∧ intTest pI1849 (runFrom pI1849 (fmask pI1849) (cmask pI1849) (hmask pI1849) 1510 339 (true, I1849_cp2.1, I1849_cp2.2)) 1849 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1849_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1849_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1849_fin) true) I1849_seg1) I1849_seg2) (by decide) rfl I1849_fin intTest_fst
theorem link1849 : linkOK pL1849 pH1849 pI1849 = true := by decide +kernel
theorem cvx1849 : ConvexBetweenHumps 1849 :=
  cvx_of L1849_ok H1849_ok I1849_ok link1849 (by decide)

/-! ### `N = 1850` -/

def pL1850 : Prm := ⟨80, 37, 40, 1852, 11, 18446744073709551616, 104839404323894170, 104839404323894170⟩
def pH1850 : Prm := ⟨80, 37, 40, 1852, 11, 18446744073709551616, 104840503835521946, 104840503835521946⟩
def pI1850 : Prm := ⟨68, 34, 31, 1852, 11, 18446744073709551616, 104839404323894170, 104840503835521946⟩
noncomputable def L1850_cp1 : Nat × Nat := t7val% (fastRun pL1850 1 1067 (init pL1850) (init pL1850))
theorem L1850_seg1 : segOK pL1850 1 1067 (init pL1850) (init pL1850) L1850_cp1.1 L1850_cp1.2 = true := by
  decide +kernel
noncomputable def L1850_cp2 : Nat × Nat := t7val% (fastRun pL1850 1 1510 (init pL1850) (init pL1850))
theorem L1850_seg2 : segOK pL1850 1068 443 L1850_cp1.1 L1850_cp1.2 L1850_cp2.1 L1850_cp2.2 = true := by
  decide +kernel
theorem L1850_fin : (prmOK pL1850 1850 && ptTest pL1850 (runFrom pL1850 (fmask pL1850) (cmask pL1850) (hmask pL1850) 1511 339 (true, L1850_cp2.1, L1850_cp2.2)) 1850 925 false) = true := by
  decide +kernel
theorem L1850_ok : RunOK pL1850 1850 (runFrom pL1850 (fmask pL1850) (cmask pL1850) (hmask pL1850) 1511 339 (true, L1850_cp2.1, L1850_cp2.2)) ∧ ptTest pL1850 (runFrom pL1850 (fmask pL1850) (cmask pL1850) (hmask pL1850) 1511 339 (true, L1850_cp2.1, L1850_cp2.2)) 1850 925 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1850_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1850_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1850_fin) true) L1850_seg1) L1850_seg2) (by decide) rfl L1850_fin ptTest_fst
noncomputable def H1850_cp1 : Nat × Nat := t7val% (fastRun pH1850 1 1067 (init pH1850) (init pH1850))
theorem H1850_seg1 : segOK pH1850 1 1067 (init pH1850) (init pH1850) H1850_cp1.1 H1850_cp1.2 = true := by
  decide +kernel
noncomputable def H1850_cp2 : Nat × Nat := t7val% (fastRun pH1850 1 1510 (init pH1850) (init pH1850))
theorem H1850_seg2 : segOK pH1850 1068 443 H1850_cp1.1 H1850_cp1.2 H1850_cp2.1 H1850_cp2.2 = true := by
  decide +kernel
theorem H1850_fin : (prmOK pH1850 1850 && ptTest pH1850 (runFrom pH1850 (fmask pH1850) (cmask pH1850) (hmask pH1850) 1511 339 (true, H1850_cp2.1, H1850_cp2.2)) 1850 925 true) = true := by
  decide +kernel
theorem H1850_ok : RunOK pH1850 1850 (runFrom pH1850 (fmask pH1850) (cmask pH1850) (hmask pH1850) 1511 339 (true, H1850_cp2.1, H1850_cp2.2)) ∧ ptTest pH1850 (runFrom pH1850 (fmask pH1850) (cmask pH1850) (hmask pH1850) 1511 339 (true, H1850_cp2.1, H1850_cp2.2)) 1850 925 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1850_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1850_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1850_fin) true) H1850_seg1) H1850_seg2) (by decide) rfl H1850_fin ptTest_fst
noncomputable def I1850_cp1 : Nat × Nat := t7val% (fastRun pI1850 1 1067 (init pI1850) (init pI1850))
theorem I1850_seg1 : segOK pI1850 1 1067 (init pI1850) (init pI1850) I1850_cp1.1 I1850_cp1.2 = true := by
  decide +kernel
noncomputable def I1850_cp2 : Nat × Nat := t7val% (fastRun pI1850 1 1510 (init pI1850) (init pI1850))
theorem I1850_seg2 : segOK pI1850 1068 443 I1850_cp1.1 I1850_cp1.2 I1850_cp2.1 I1850_cp2.2 = true := by
  decide +kernel
theorem I1850_fin : (prmOK pI1850 1850 && intTest pI1850 (runFrom pI1850 (fmask pI1850) (cmask pI1850) (hmask pI1850) 1511 339 (true, I1850_cp2.1, I1850_cp2.2)) 1850 21 true) = true := by
  decide +kernel
theorem I1850_ok : RunOK pI1850 1850 (runFrom pI1850 (fmask pI1850) (cmask pI1850) (hmask pI1850) 1511 339 (true, I1850_cp2.1, I1850_cp2.2)) ∧ intTest pI1850 (runFrom pI1850 (fmask pI1850) (cmask pI1850) (hmask pI1850) 1511 339 (true, I1850_cp2.1, I1850_cp2.2)) 1850 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1850_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1850_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1850_fin) true) I1850_seg1) I1850_seg2) (by decide) rfl I1850_fin intTest_fst
theorem link1850 : linkOK pL1850 pH1850 pI1850 = true := by decide +kernel
theorem cvx1850 : ConvexBetweenHumps 1850 :=
  cvx_of L1850_ok H1850_ok I1850_ok link1850 (by decide)
theorem cenlink1850 : cenLinkOK pI1850 1850 = true := by decide +kernel
theorem cen1850 : CenterUniqueMin 1850 ∧ DipHyp 1850 ∧ OnePointHyps 1850 :=
  cen_of L1850_ok H1850_ok I1850_ok link1850 cenlink1850

/-! ### `N = 1851` -/

def pL1851 : Prm := ⟨80, 37, 40, 1853, 11, 18446744073709551616, 104792907605146197, 104792907605146197⟩
def pH1851 : Prm := ⟨80, 37, 40, 1853, 11, 18446744073709551616, 104794007116773973, 104794007116773973⟩
def pI1851 : Prm := ⟨68, 34, 31, 1853, 11, 18446744073709551616, 104792907605146197, 104794007116773973⟩
noncomputable def L1851_cp1 : Nat × Nat := t7val% (fastRun pL1851 1 1068 (init pL1851) (init pL1851))
theorem L1851_seg1 : segOK pL1851 1 1068 (init pL1851) (init pL1851) L1851_cp1.1 L1851_cp1.2 = true := by
  decide +kernel
noncomputable def L1851_cp2 : Nat × Nat := t7val% (fastRun pL1851 1 1510 (init pL1851) (init pL1851))
theorem L1851_seg2 : segOK pL1851 1069 442 L1851_cp1.1 L1851_cp1.2 L1851_cp2.1 L1851_cp2.2 = true := by
  decide +kernel
theorem L1851_fin : (prmOK pL1851 1851 && ptTest pL1851 (runFrom pL1851 (fmask pL1851) (cmask pL1851) (hmask pL1851) 1511 340 (true, L1851_cp2.1, L1851_cp2.2)) 1851 926 false) = true := by
  decide +kernel
theorem L1851_ok : RunOK pL1851 1851 (runFrom pL1851 (fmask pL1851) (cmask pL1851) (hmask pL1851) 1511 340 (true, L1851_cp2.1, L1851_cp2.2)) ∧ ptTest pL1851 (runFrom pL1851 (fmask pL1851) (cmask pL1851) (hmask pL1851) 1511 340 (true, L1851_cp2.1, L1851_cp2.2)) 1851 926 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1851_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1851_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1851_fin) true) L1851_seg1) L1851_seg2) (by decide) rfl L1851_fin ptTest_fst
noncomputable def H1851_cp1 : Nat × Nat := t7val% (fastRun pH1851 1 1068 (init pH1851) (init pH1851))
theorem H1851_seg1 : segOK pH1851 1 1068 (init pH1851) (init pH1851) H1851_cp1.1 H1851_cp1.2 = true := by
  decide +kernel
noncomputable def H1851_cp2 : Nat × Nat := t7val% (fastRun pH1851 1 1510 (init pH1851) (init pH1851))
theorem H1851_seg2 : segOK pH1851 1069 442 H1851_cp1.1 H1851_cp1.2 H1851_cp2.1 H1851_cp2.2 = true := by
  decide +kernel
theorem H1851_fin : (prmOK pH1851 1851 && ptTest pH1851 (runFrom pH1851 (fmask pH1851) (cmask pH1851) (hmask pH1851) 1511 340 (true, H1851_cp2.1, H1851_cp2.2)) 1851 926 true) = true := by
  decide +kernel
theorem H1851_ok : RunOK pH1851 1851 (runFrom pH1851 (fmask pH1851) (cmask pH1851) (hmask pH1851) 1511 340 (true, H1851_cp2.1, H1851_cp2.2)) ∧ ptTest pH1851 (runFrom pH1851 (fmask pH1851) (cmask pH1851) (hmask pH1851) 1511 340 (true, H1851_cp2.1, H1851_cp2.2)) 1851 926 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1851_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1851_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1851_fin) true) H1851_seg1) H1851_seg2) (by decide) rfl H1851_fin ptTest_fst
noncomputable def I1851_cp1 : Nat × Nat := t7val% (fastRun pI1851 1 1068 (init pI1851) (init pI1851))
theorem I1851_seg1 : segOK pI1851 1 1068 (init pI1851) (init pI1851) I1851_cp1.1 I1851_cp1.2 = true := by
  decide +kernel
noncomputable def I1851_cp2 : Nat × Nat := t7val% (fastRun pI1851 1 1510 (init pI1851) (init pI1851))
theorem I1851_seg2 : segOK pI1851 1069 442 I1851_cp1.1 I1851_cp1.2 I1851_cp2.1 I1851_cp2.2 = true := by
  decide +kernel
theorem I1851_fin : (prmOK pI1851 1851 && intTest pI1851 (runFrom pI1851 (fmask pI1851) (cmask pI1851) (hmask pI1851) 1511 340 (true, I1851_cp2.1, I1851_cp2.2)) 1851 21 false) = true := by
  decide +kernel
theorem I1851_ok : RunOK pI1851 1851 (runFrom pI1851 (fmask pI1851) (cmask pI1851) (hmask pI1851) 1511 340 (true, I1851_cp2.1, I1851_cp2.2)) ∧ intTest pI1851 (runFrom pI1851 (fmask pI1851) (cmask pI1851) (hmask pI1851) 1511 340 (true, I1851_cp2.1, I1851_cp2.2)) 1851 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1851_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1851_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1851_fin) true) I1851_seg1) I1851_seg2) (by decide) rfl I1851_fin intTest_fst
theorem link1851 : linkOK pL1851 pH1851 pI1851 = true := by decide +kernel
theorem cvx1851 : ConvexBetweenHumps 1851 :=
  cvx_of L1851_ok H1851_ok I1851_ok link1851 (by decide)

/-! ### `N = 1852` -/

def pL1852 : Prm := ⟨80, 37, 40, 1854, 11, 18446744073709551616, 104746473276791562, 104746473276791562⟩
def pH1852 : Prm := ⟨80, 37, 40, 1854, 11, 18446744073709551616, 104747572788419338, 104747572788419338⟩
def pI1852 : Prm := ⟨68, 34, 31, 1854, 11, 18446744073709551616, 104746473276791562, 104747572788419338⟩
noncomputable def L1852_cp1 : Nat × Nat := t7val% (fastRun pL1852 1 1068 (init pL1852) (init pL1852))
theorem L1852_seg1 : segOK pL1852 1 1068 (init pL1852) (init pL1852) L1852_cp1.1 L1852_cp1.2 = true := by
  decide +kernel
noncomputable def L1852_cp2 : Nat × Nat := t7val% (fastRun pL1852 1 1511 (init pL1852) (init pL1852))
theorem L1852_seg2 : segOK pL1852 1069 443 L1852_cp1.1 L1852_cp1.2 L1852_cp2.1 L1852_cp2.2 = true := by
  decide +kernel
theorem L1852_fin : (prmOK pL1852 1852 && ptTest pL1852 (runFrom pL1852 (fmask pL1852) (cmask pL1852) (hmask pL1852) 1512 340 (true, L1852_cp2.1, L1852_cp2.2)) 1852 926 false) = true := by
  decide +kernel
theorem L1852_ok : RunOK pL1852 1852 (runFrom pL1852 (fmask pL1852) (cmask pL1852) (hmask pL1852) 1512 340 (true, L1852_cp2.1, L1852_cp2.2)) ∧ ptTest pL1852 (runFrom pL1852 (fmask pL1852) (cmask pL1852) (hmask pL1852) 1512 340 (true, L1852_cp2.1, L1852_cp2.2)) 1852 926 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1852_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1852_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1852_fin) true) L1852_seg1) L1852_seg2) (by decide) rfl L1852_fin ptTest_fst
noncomputable def H1852_cp1 : Nat × Nat := t7val% (fastRun pH1852 1 1068 (init pH1852) (init pH1852))
theorem H1852_seg1 : segOK pH1852 1 1068 (init pH1852) (init pH1852) H1852_cp1.1 H1852_cp1.2 = true := by
  decide +kernel
noncomputable def H1852_cp2 : Nat × Nat := t7val% (fastRun pH1852 1 1511 (init pH1852) (init pH1852))
theorem H1852_seg2 : segOK pH1852 1069 443 H1852_cp1.1 H1852_cp1.2 H1852_cp2.1 H1852_cp2.2 = true := by
  decide +kernel
theorem H1852_fin : (prmOK pH1852 1852 && ptTest pH1852 (runFrom pH1852 (fmask pH1852) (cmask pH1852) (hmask pH1852) 1512 340 (true, H1852_cp2.1, H1852_cp2.2)) 1852 926 true) = true := by
  decide +kernel
theorem H1852_ok : RunOK pH1852 1852 (runFrom pH1852 (fmask pH1852) (cmask pH1852) (hmask pH1852) 1512 340 (true, H1852_cp2.1, H1852_cp2.2)) ∧ ptTest pH1852 (runFrom pH1852 (fmask pH1852) (cmask pH1852) (hmask pH1852) 1512 340 (true, H1852_cp2.1, H1852_cp2.2)) 1852 926 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1852_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1852_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1852_fin) true) H1852_seg1) H1852_seg2) (by decide) rfl H1852_fin ptTest_fst
noncomputable def I1852_cp1 : Nat × Nat := t7val% (fastRun pI1852 1 1068 (init pI1852) (init pI1852))
theorem I1852_seg1 : segOK pI1852 1 1068 (init pI1852) (init pI1852) I1852_cp1.1 I1852_cp1.2 = true := by
  decide +kernel
noncomputable def I1852_cp2 : Nat × Nat := t7val% (fastRun pI1852 1 1511 (init pI1852) (init pI1852))
theorem I1852_seg2 : segOK pI1852 1069 443 I1852_cp1.1 I1852_cp1.2 I1852_cp2.1 I1852_cp2.2 = true := by
  decide +kernel
theorem I1852_fin : (prmOK pI1852 1852 && intTest pI1852 (runFrom pI1852 (fmask pI1852) (cmask pI1852) (hmask pI1852) 1512 340 (true, I1852_cp2.1, I1852_cp2.2)) 1852 21 true) = true := by
  decide +kernel
theorem I1852_ok : RunOK pI1852 1852 (runFrom pI1852 (fmask pI1852) (cmask pI1852) (hmask pI1852) 1512 340 (true, I1852_cp2.1, I1852_cp2.2)) ∧ intTest pI1852 (runFrom pI1852 (fmask pI1852) (cmask pI1852) (hmask pI1852) 1512 340 (true, I1852_cp2.1, I1852_cp2.2)) 1852 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1852_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1852_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1852_fin) true) I1852_seg1) I1852_seg2) (by decide) rfl I1852_fin intTest_fst
theorem link1852 : linkOK pL1852 pH1852 pI1852 = true := by decide +kernel
theorem cvx1852 : ConvexBetweenHumps 1852 :=
  cvx_of L1852_ok H1852_ok I1852_ok link1852 (by decide)
theorem cenlink1852 : cenLinkOK pI1852 1852 = true := by decide +kernel
theorem cen1852 : CenterUniqueMin 1852 ∧ DipHyp 1852 ∧ OnePointHyps 1852 :=
  cen_of L1852_ok H1852_ok I1852_ok link1852 cenlink1852

/-! ### `N = 1853` -/

def pL1853 : Prm := ⟨80, 37, 40, 1855, 11, 18446744073709551616, 104700065951537219, 104700065951537219⟩
def pH1853 : Prm := ⟨80, 37, 40, 1855, 11, 18446744073709551616, 104701165463164995, 104701165463164995⟩
def pI1853 : Prm := ⟨68, 34, 31, 1855, 11, 18446744073709551616, 104700065951537219, 104701165463164995⟩
noncomputable def L1853_cp1 : Nat × Nat := t7val% (fastRun pL1853 1 1069 (init pL1853) (init pL1853))
theorem L1853_seg1 : segOK pL1853 1 1069 (init pL1853) (init pL1853) L1853_cp1.1 L1853_cp1.2 = true := by
  decide +kernel
noncomputable def L1853_cp2 : Nat × Nat := t7val% (fastRun pL1853 1 1512 (init pL1853) (init pL1853))
theorem L1853_seg2 : segOK pL1853 1070 443 L1853_cp1.1 L1853_cp1.2 L1853_cp2.1 L1853_cp2.2 = true := by
  decide +kernel
theorem L1853_fin : (prmOK pL1853 1853 && ptTest pL1853 (runFrom pL1853 (fmask pL1853) (cmask pL1853) (hmask pL1853) 1513 340 (true, L1853_cp2.1, L1853_cp2.2)) 1853 927 false) = true := by
  decide +kernel
theorem L1853_ok : RunOK pL1853 1853 (runFrom pL1853 (fmask pL1853) (cmask pL1853) (hmask pL1853) 1513 340 (true, L1853_cp2.1, L1853_cp2.2)) ∧ ptTest pL1853 (runFrom pL1853 (fmask pL1853) (cmask pL1853) (hmask pL1853) 1513 340 (true, L1853_cp2.1, L1853_cp2.2)) 1853 927 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1853_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1853_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1853_fin) true) L1853_seg1) L1853_seg2) (by decide) rfl L1853_fin ptTest_fst
noncomputable def H1853_cp1 : Nat × Nat := t7val% (fastRun pH1853 1 1069 (init pH1853) (init pH1853))
theorem H1853_seg1 : segOK pH1853 1 1069 (init pH1853) (init pH1853) H1853_cp1.1 H1853_cp1.2 = true := by
  decide +kernel
noncomputable def H1853_cp2 : Nat × Nat := t7val% (fastRun pH1853 1 1512 (init pH1853) (init pH1853))
theorem H1853_seg2 : segOK pH1853 1070 443 H1853_cp1.1 H1853_cp1.2 H1853_cp2.1 H1853_cp2.2 = true := by
  decide +kernel
theorem H1853_fin : (prmOK pH1853 1853 && ptTest pH1853 (runFrom pH1853 (fmask pH1853) (cmask pH1853) (hmask pH1853) 1513 340 (true, H1853_cp2.1, H1853_cp2.2)) 1853 927 true) = true := by
  decide +kernel
theorem H1853_ok : RunOK pH1853 1853 (runFrom pH1853 (fmask pH1853) (cmask pH1853) (hmask pH1853) 1513 340 (true, H1853_cp2.1, H1853_cp2.2)) ∧ ptTest pH1853 (runFrom pH1853 (fmask pH1853) (cmask pH1853) (hmask pH1853) 1513 340 (true, H1853_cp2.1, H1853_cp2.2)) 1853 927 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1853_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1853_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1853_fin) true) H1853_seg1) H1853_seg2) (by decide) rfl H1853_fin ptTest_fst
noncomputable def I1853_cp1 : Nat × Nat := t7val% (fastRun pI1853 1 1069 (init pI1853) (init pI1853))
theorem I1853_seg1 : segOK pI1853 1 1069 (init pI1853) (init pI1853) I1853_cp1.1 I1853_cp1.2 = true := by
  decide +kernel
noncomputable def I1853_cp2 : Nat × Nat := t7val% (fastRun pI1853 1 1512 (init pI1853) (init pI1853))
theorem I1853_seg2 : segOK pI1853 1070 443 I1853_cp1.1 I1853_cp1.2 I1853_cp2.1 I1853_cp2.2 = true := by
  decide +kernel
theorem I1853_fin : (prmOK pI1853 1853 && intTest pI1853 (runFrom pI1853 (fmask pI1853) (cmask pI1853) (hmask pI1853) 1513 340 (true, I1853_cp2.1, I1853_cp2.2)) 1853 21 false) = true := by
  decide +kernel
theorem I1853_ok : RunOK pI1853 1853 (runFrom pI1853 (fmask pI1853) (cmask pI1853) (hmask pI1853) 1513 340 (true, I1853_cp2.1, I1853_cp2.2)) ∧ intTest pI1853 (runFrom pI1853 (fmask pI1853) (cmask pI1853) (hmask pI1853) 1513 340 (true, I1853_cp2.1, I1853_cp2.2)) 1853 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1853_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1853_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1853_fin) true) I1853_seg1) I1853_seg2) (by decide) rfl I1853_fin intTest_fst
theorem link1853 : linkOK pL1853 pH1853 pI1853 = true := by decide +kernel
theorem cvx1853 : ConvexBetweenHumps 1853 :=
  cvx_of L1853_ok H1853_ok I1853_ok link1853 (by decide)

/-! ### The range -/

theorem cvx_1843_1853 {N : ℕ} (h1 : 1843 ≤ N) (h2 : N ≤ 1853) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1847
  · by_cases h4 : N ≤ 1844
    · by_cases h6 : N ≤ 1843
      · obtain rfl : N = 1843 := by omega
        exact cvx1843
      · obtain rfl : N = 1844 := by omega
        exact cvx1844
    · by_cases h6 : N ≤ 1845
      · obtain rfl : N = 1845 := by omega
        exact cvx1845
      · by_cases h8 : N ≤ 1846
        · obtain rfl : N = 1846 := by omega
          exact cvx1846
        · obtain rfl : N = 1847 := by omega
          exact cvx1847
  · by_cases h4 : N ≤ 1850
    · by_cases h6 : N ≤ 1848
      · obtain rfl : N = 1848 := by omega
        exact cvx1848
      · by_cases h8 : N ≤ 1849
        · obtain rfl : N = 1849 := by omega
          exact cvx1849
        · obtain rfl : N = 1850 := by omega
          exact cvx1850
    · by_cases h6 : N ≤ 1851
      · obtain rfl : N = 1851 := by omega
        exact cvx1851
      · by_cases h8 : N ≤ 1852
        · obtain rfl : N = 1852 := by omega
          exact cvx1852
        · obtain rfl : N = 1853 := by omega
          exact cvx1853

theorem cen_1843_1853 {N : ℕ} (h1 : 1843 ≤ N) (h2 : N ≤ 1853) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1846
  · by_cases h4 : N ≤ 1844
    · obtain rfl : N = 1844 := by omega
      exact cen1844
    · obtain rfl : N = 1846 := by omega
      exact cen1846
  · by_cases h4 : N ≤ 1848
    · obtain rfl : N = 1848 := by omega
      exact cen1848
    · by_cases h6 : N ≤ 1850
      · obtain rfl : N = 1850 := by omega
        exact cen1850
      · obtain rfl : N = 1852 := by omega
        exact cen1852

end Kagey131.PaperD.T7
