import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1796, …, 1807` (generated)

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

/-! ### `N = 1796` -/

def pL1796 : Prm := ⟨80, 37, 40, 1798, 11, 18446744073709551616, 107418049402395318, 107418049402395318⟩
def pH1796 : Prm := ⟨80, 37, 40, 1798, 11, 18446744073709551616, 107419148914023094, 107419148914023094⟩
def pI1796 : Prm := ⟨67, 34, 30, 1798, 11, 18446744073709551616, 107418049402395318, 107419148914023094⟩
noncomputable def L1796_cp1 : Nat × Nat := t7val% (fastRun pL1796 1 1036 (init pL1796) (init pL1796))
theorem L1796_seg1 : segOK pL1796 1 1036 (init pL1796) (init pL1796) L1796_cp1.1 L1796_cp1.2 = true := by
  decide +kernel
noncomputable def L1796_cp2 : Nat × Nat := t7val% (fastRun pL1796 1 1465 (init pL1796) (init pL1796))
theorem L1796_seg2 : segOK pL1796 1037 429 L1796_cp1.1 L1796_cp1.2 L1796_cp2.1 L1796_cp2.2 = true := by
  decide +kernel
theorem L1796_fin : (prmOK pL1796 1796 && ptTest pL1796 (runFrom pL1796 (fmask pL1796) (cmask pL1796) (hmask pL1796) 1466 330 (true, L1796_cp2.1, L1796_cp2.2)) 1796 898 false) = true := by
  decide +kernel
theorem L1796_ok : RunOK pL1796 1796 (runFrom pL1796 (fmask pL1796) (cmask pL1796) (hmask pL1796) 1466 330 (true, L1796_cp2.1, L1796_cp2.2)) ∧ ptTest pL1796 (runFrom pL1796 (fmask pL1796) (cmask pL1796) (hmask pL1796) 1466 330 (true, L1796_cp2.1, L1796_cp2.2)) 1796 898 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1796_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1796_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1796_fin) true) L1796_seg1) L1796_seg2) (by decide) rfl L1796_fin ptTest_fst
noncomputable def H1796_cp1 : Nat × Nat := t7val% (fastRun pH1796 1 1036 (init pH1796) (init pH1796))
theorem H1796_seg1 : segOK pH1796 1 1036 (init pH1796) (init pH1796) H1796_cp1.1 H1796_cp1.2 = true := by
  decide +kernel
noncomputable def H1796_cp2 : Nat × Nat := t7val% (fastRun pH1796 1 1465 (init pH1796) (init pH1796))
theorem H1796_seg2 : segOK pH1796 1037 429 H1796_cp1.1 H1796_cp1.2 H1796_cp2.1 H1796_cp2.2 = true := by
  decide +kernel
theorem H1796_fin : (prmOK pH1796 1796 && ptTest pH1796 (runFrom pH1796 (fmask pH1796) (cmask pH1796) (hmask pH1796) 1466 330 (true, H1796_cp2.1, H1796_cp2.2)) 1796 898 true) = true := by
  decide +kernel
theorem H1796_ok : RunOK pH1796 1796 (runFrom pH1796 (fmask pH1796) (cmask pH1796) (hmask pH1796) 1466 330 (true, H1796_cp2.1, H1796_cp2.2)) ∧ ptTest pH1796 (runFrom pH1796 (fmask pH1796) (cmask pH1796) (hmask pH1796) 1466 330 (true, H1796_cp2.1, H1796_cp2.2)) 1796 898 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1796_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1796_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1796_fin) true) H1796_seg1) H1796_seg2) (by decide) rfl H1796_fin ptTest_fst
noncomputable def I1796_cp1 : Nat × Nat := t7val% (fastRun pI1796 1 1036 (init pI1796) (init pI1796))
theorem I1796_seg1 : segOK pI1796 1 1036 (init pI1796) (init pI1796) I1796_cp1.1 I1796_cp1.2 = true := by
  decide +kernel
noncomputable def I1796_cp2 : Nat × Nat := t7val% (fastRun pI1796 1 1465 (init pI1796) (init pI1796))
theorem I1796_seg2 : segOK pI1796 1037 429 I1796_cp1.1 I1796_cp1.2 I1796_cp2.1 I1796_cp2.2 = true := by
  decide +kernel
theorem I1796_fin : (prmOK pI1796 1796 && intTest pI1796 (runFrom pI1796 (fmask pI1796) (cmask pI1796) (hmask pI1796) 1466 330 (true, I1796_cp2.1, I1796_cp2.2)) 1796 21 true) = true := by
  decide +kernel
theorem I1796_ok : RunOK pI1796 1796 (runFrom pI1796 (fmask pI1796) (cmask pI1796) (hmask pI1796) 1466 330 (true, I1796_cp2.1, I1796_cp2.2)) ∧ intTest pI1796 (runFrom pI1796 (fmask pI1796) (cmask pI1796) (hmask pI1796) 1466 330 (true, I1796_cp2.1, I1796_cp2.2)) 1796 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1796_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1796_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1796_fin) true) I1796_seg1) I1796_seg2) (by decide) rfl I1796_fin intTest_fst
theorem link1796 : linkOK pL1796 pH1796 pI1796 = true := by decide +kernel
theorem cvx1796 : ConvexBetweenHumps 1796 :=
  cvx_of L1796_ok H1796_ok I1796_ok link1796 (by decide)
theorem cenlink1796 : cenLinkOK pI1796 1796 = true := by decide +kernel
theorem cen1796 : CenterUniqueMin 1796 ∧ DipHyp 1796 ∧ OnePointHyps 1796 :=
  cen_of L1796_ok H1796_ok I1796_ok link1796 cenlink1796

/-! ### `N = 1797` -/

def pL1797 : Prm := ⟨80, 37, 40, 1799, 11, 18446744073709551616, 107369034657757634, 107369034657757634⟩
def pH1797 : Prm := ⟨80, 37, 40, 1799, 11, 18446744073709551616, 107370134169385410, 107370134169385410⟩
def pI1797 : Prm := ⟨67, 34, 30, 1799, 11, 18446744073709551616, 107369034657757634, 107370134169385410⟩
noncomputable def L1797_cp1 : Nat × Nat := t7val% (fastRun pL1797 1 1036 (init pL1797) (init pL1797))
theorem L1797_seg1 : segOK pL1797 1 1036 (init pL1797) (init pL1797) L1797_cp1.1 L1797_cp1.2 = true := by
  decide +kernel
noncomputable def L1797_cp2 : Nat × Nat := t7val% (fastRun pL1797 1 1466 (init pL1797) (init pL1797))
theorem L1797_seg2 : segOK pL1797 1037 430 L1797_cp1.1 L1797_cp1.2 L1797_cp2.1 L1797_cp2.2 = true := by
  decide +kernel
theorem L1797_fin : (prmOK pL1797 1797 && ptTest pL1797 (runFrom pL1797 (fmask pL1797) (cmask pL1797) (hmask pL1797) 1467 330 (true, L1797_cp2.1, L1797_cp2.2)) 1797 899 false) = true := by
  decide +kernel
theorem L1797_ok : RunOK pL1797 1797 (runFrom pL1797 (fmask pL1797) (cmask pL1797) (hmask pL1797) 1467 330 (true, L1797_cp2.1, L1797_cp2.2)) ∧ ptTest pL1797 (runFrom pL1797 (fmask pL1797) (cmask pL1797) (hmask pL1797) 1467 330 (true, L1797_cp2.1, L1797_cp2.2)) 1797 899 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1797_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1797_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1797_fin) true) L1797_seg1) L1797_seg2) (by decide) rfl L1797_fin ptTest_fst
noncomputable def H1797_cp1 : Nat × Nat := t7val% (fastRun pH1797 1 1036 (init pH1797) (init pH1797))
theorem H1797_seg1 : segOK pH1797 1 1036 (init pH1797) (init pH1797) H1797_cp1.1 H1797_cp1.2 = true := by
  decide +kernel
noncomputable def H1797_cp2 : Nat × Nat := t7val% (fastRun pH1797 1 1466 (init pH1797) (init pH1797))
theorem H1797_seg2 : segOK pH1797 1037 430 H1797_cp1.1 H1797_cp1.2 H1797_cp2.1 H1797_cp2.2 = true := by
  decide +kernel
theorem H1797_fin : (prmOK pH1797 1797 && ptTest pH1797 (runFrom pH1797 (fmask pH1797) (cmask pH1797) (hmask pH1797) 1467 330 (true, H1797_cp2.1, H1797_cp2.2)) 1797 899 true) = true := by
  decide +kernel
theorem H1797_ok : RunOK pH1797 1797 (runFrom pH1797 (fmask pH1797) (cmask pH1797) (hmask pH1797) 1467 330 (true, H1797_cp2.1, H1797_cp2.2)) ∧ ptTest pH1797 (runFrom pH1797 (fmask pH1797) (cmask pH1797) (hmask pH1797) 1467 330 (true, H1797_cp2.1, H1797_cp2.2)) 1797 899 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1797_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1797_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1797_fin) true) H1797_seg1) H1797_seg2) (by decide) rfl H1797_fin ptTest_fst
noncomputable def I1797_cp1 : Nat × Nat := t7val% (fastRun pI1797 1 1036 (init pI1797) (init pI1797))
theorem I1797_seg1 : segOK pI1797 1 1036 (init pI1797) (init pI1797) I1797_cp1.1 I1797_cp1.2 = true := by
  decide +kernel
noncomputable def I1797_cp2 : Nat × Nat := t7val% (fastRun pI1797 1 1466 (init pI1797) (init pI1797))
theorem I1797_seg2 : segOK pI1797 1037 430 I1797_cp1.1 I1797_cp1.2 I1797_cp2.1 I1797_cp2.2 = true := by
  decide +kernel
theorem I1797_fin : (prmOK pI1797 1797 && intTest pI1797 (runFrom pI1797 (fmask pI1797) (cmask pI1797) (hmask pI1797) 1467 330 (true, I1797_cp2.1, I1797_cp2.2)) 1797 21 false) = true := by
  decide +kernel
theorem I1797_ok : RunOK pI1797 1797 (runFrom pI1797 (fmask pI1797) (cmask pI1797) (hmask pI1797) 1467 330 (true, I1797_cp2.1, I1797_cp2.2)) ∧ intTest pI1797 (runFrom pI1797 (fmask pI1797) (cmask pI1797) (hmask pI1797) 1467 330 (true, I1797_cp2.1, I1797_cp2.2)) 1797 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1797_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1797_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1797_fin) true) I1797_seg1) I1797_seg2) (by decide) rfl I1797_fin intTest_fst
theorem link1797 : linkOK pL1797 pH1797 pI1797 = true := by decide +kernel
theorem cvx1797 : ConvexBetweenHumps 1797 :=
  cvx_of L1797_ok H1797_ok I1797_ok link1797 (by decide)

/-! ### `N = 1798` -/

def pL1798 : Prm := ⟨80, 37, 40, 1800, 11, 18446744073709551616, 107320087769025303, 107320087769025303⟩
def pH1798 : Prm := ⟨80, 37, 40, 1800, 11, 18446744073709551616, 107321187280653079, 107321187280653079⟩
def pI1798 : Prm := ⟨67, 34, 30, 1800, 11, 18446744073709551616, 107320087769025303, 107321187280653079⟩
noncomputable def L1798_cp1 : Nat × Nat := t7val% (fastRun pL1798 1 1037 (init pL1798) (init pL1798))
theorem L1798_seg1 : segOK pL1798 1 1037 (init pL1798) (init pL1798) L1798_cp1.1 L1798_cp1.2 = true := by
  decide +kernel
noncomputable def L1798_cp2 : Nat × Nat := t7val% (fastRun pL1798 1 1467 (init pL1798) (init pL1798))
theorem L1798_seg2 : segOK pL1798 1038 430 L1798_cp1.1 L1798_cp1.2 L1798_cp2.1 L1798_cp2.2 = true := by
  decide +kernel
theorem L1798_fin : (prmOK pL1798 1798 && ptTest pL1798 (runFrom pL1798 (fmask pL1798) (cmask pL1798) (hmask pL1798) 1468 330 (true, L1798_cp2.1, L1798_cp2.2)) 1798 899 false) = true := by
  decide +kernel
theorem L1798_ok : RunOK pL1798 1798 (runFrom pL1798 (fmask pL1798) (cmask pL1798) (hmask pL1798) 1468 330 (true, L1798_cp2.1, L1798_cp2.2)) ∧ ptTest pL1798 (runFrom pL1798 (fmask pL1798) (cmask pL1798) (hmask pL1798) 1468 330 (true, L1798_cp2.1, L1798_cp2.2)) 1798 899 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1798_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1798_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1798_fin) true) L1798_seg1) L1798_seg2) (by decide) rfl L1798_fin ptTest_fst
noncomputable def H1798_cp1 : Nat × Nat := t7val% (fastRun pH1798 1 1037 (init pH1798) (init pH1798))
theorem H1798_seg1 : segOK pH1798 1 1037 (init pH1798) (init pH1798) H1798_cp1.1 H1798_cp1.2 = true := by
  decide +kernel
noncomputable def H1798_cp2 : Nat × Nat := t7val% (fastRun pH1798 1 1467 (init pH1798) (init pH1798))
theorem H1798_seg2 : segOK pH1798 1038 430 H1798_cp1.1 H1798_cp1.2 H1798_cp2.1 H1798_cp2.2 = true := by
  decide +kernel
theorem H1798_fin : (prmOK pH1798 1798 && ptTest pH1798 (runFrom pH1798 (fmask pH1798) (cmask pH1798) (hmask pH1798) 1468 330 (true, H1798_cp2.1, H1798_cp2.2)) 1798 899 true) = true := by
  decide +kernel
theorem H1798_ok : RunOK pH1798 1798 (runFrom pH1798 (fmask pH1798) (cmask pH1798) (hmask pH1798) 1468 330 (true, H1798_cp2.1, H1798_cp2.2)) ∧ ptTest pH1798 (runFrom pH1798 (fmask pH1798) (cmask pH1798) (hmask pH1798) 1468 330 (true, H1798_cp2.1, H1798_cp2.2)) 1798 899 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1798_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1798_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1798_fin) true) H1798_seg1) H1798_seg2) (by decide) rfl H1798_fin ptTest_fst
noncomputable def I1798_cp1 : Nat × Nat := t7val% (fastRun pI1798 1 1037 (init pI1798) (init pI1798))
theorem I1798_seg1 : segOK pI1798 1 1037 (init pI1798) (init pI1798) I1798_cp1.1 I1798_cp1.2 = true := by
  decide +kernel
noncomputable def I1798_cp2 : Nat × Nat := t7val% (fastRun pI1798 1 1467 (init pI1798) (init pI1798))
theorem I1798_seg2 : segOK pI1798 1038 430 I1798_cp1.1 I1798_cp1.2 I1798_cp2.1 I1798_cp2.2 = true := by
  decide +kernel
theorem I1798_fin : (prmOK pI1798 1798 && intTest pI1798 (runFrom pI1798 (fmask pI1798) (cmask pI1798) (hmask pI1798) 1468 330 (true, I1798_cp2.1, I1798_cp2.2)) 1798 21 true) = true := by
  decide +kernel
theorem I1798_ok : RunOK pI1798 1798 (runFrom pI1798 (fmask pI1798) (cmask pI1798) (hmask pI1798) 1468 330 (true, I1798_cp2.1, I1798_cp2.2)) ∧ intTest pI1798 (runFrom pI1798 (fmask pI1798) (cmask pI1798) (hmask pI1798) 1468 330 (true, I1798_cp2.1, I1798_cp2.2)) 1798 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1798_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1798_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1798_fin) true) I1798_seg1) I1798_seg2) (by decide) rfl I1798_fin intTest_fst
theorem link1798 : linkOK pL1798 pH1798 pI1798 = true := by decide +kernel
theorem cvx1798 : ConvexBetweenHumps 1798 :=
  cvx_of L1798_ok H1798_ok I1798_ok link1798 (by decide)
theorem cenlink1798 : cenLinkOK pI1798 1798 = true := by decide +kernel
theorem cen1798 : CenterUniqueMin 1798 ∧ DipHyp 1798 ∧ OnePointHyps 1798 :=
  cen_of L1798_ok H1798_ok I1798_ok link1798 cenlink1798

/-! ### `N = 1799` -/

def pL1799 : Prm := ⟨80, 37, 40, 1801, 11, 18446744073709551616, 107271170009712559, 107271170009712559⟩
def pH1799 : Prm := ⟨80, 37, 40, 1801, 11, 18446744073709551616, 107272269521340335, 107272269521340335⟩
def pI1799 : Prm := ⟨67, 34, 30, 1801, 11, 18446744073709551616, 107271170009712559, 107272269521340335⟩
noncomputable def L1799_cp1 : Nat × Nat := t7val% (fastRun pL1799 1 1038 (init pL1799) (init pL1799))
theorem L1799_seg1 : segOK pL1799 1 1038 (init pL1799) (init pL1799) L1799_cp1.1 L1799_cp1.2 = true := by
  decide +kernel
noncomputable def L1799_cp2 : Nat × Nat := t7val% (fastRun pL1799 1 1468 (init pL1799) (init pL1799))
theorem L1799_seg2 : segOK pL1799 1039 430 L1799_cp1.1 L1799_cp1.2 L1799_cp2.1 L1799_cp2.2 = true := by
  decide +kernel
theorem L1799_fin : (prmOK pL1799 1799 && ptTest pL1799 (runFrom pL1799 (fmask pL1799) (cmask pL1799) (hmask pL1799) 1469 330 (true, L1799_cp2.1, L1799_cp2.2)) 1799 900 false) = true := by
  decide +kernel
theorem L1799_ok : RunOK pL1799 1799 (runFrom pL1799 (fmask pL1799) (cmask pL1799) (hmask pL1799) 1469 330 (true, L1799_cp2.1, L1799_cp2.2)) ∧ ptTest pL1799 (runFrom pL1799 (fmask pL1799) (cmask pL1799) (hmask pL1799) 1469 330 (true, L1799_cp2.1, L1799_cp2.2)) 1799 900 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1799_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1799_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1799_fin) true) L1799_seg1) L1799_seg2) (by decide) rfl L1799_fin ptTest_fst
noncomputable def H1799_cp1 : Nat × Nat := t7val% (fastRun pH1799 1 1038 (init pH1799) (init pH1799))
theorem H1799_seg1 : segOK pH1799 1 1038 (init pH1799) (init pH1799) H1799_cp1.1 H1799_cp1.2 = true := by
  decide +kernel
noncomputable def H1799_cp2 : Nat × Nat := t7val% (fastRun pH1799 1 1468 (init pH1799) (init pH1799))
theorem H1799_seg2 : segOK pH1799 1039 430 H1799_cp1.1 H1799_cp1.2 H1799_cp2.1 H1799_cp2.2 = true := by
  decide +kernel
theorem H1799_fin : (prmOK pH1799 1799 && ptTest pH1799 (runFrom pH1799 (fmask pH1799) (cmask pH1799) (hmask pH1799) 1469 330 (true, H1799_cp2.1, H1799_cp2.2)) 1799 900 true) = true := by
  decide +kernel
theorem H1799_ok : RunOK pH1799 1799 (runFrom pH1799 (fmask pH1799) (cmask pH1799) (hmask pH1799) 1469 330 (true, H1799_cp2.1, H1799_cp2.2)) ∧ ptTest pH1799 (runFrom pH1799 (fmask pH1799) (cmask pH1799) (hmask pH1799) 1469 330 (true, H1799_cp2.1, H1799_cp2.2)) 1799 900 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1799_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1799_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1799_fin) true) H1799_seg1) H1799_seg2) (by decide) rfl H1799_fin ptTest_fst
noncomputable def I1799_cp1 : Nat × Nat := t7val% (fastRun pI1799 1 1038 (init pI1799) (init pI1799))
theorem I1799_seg1 : segOK pI1799 1 1038 (init pI1799) (init pI1799) I1799_cp1.1 I1799_cp1.2 = true := by
  decide +kernel
noncomputable def I1799_cp2 : Nat × Nat := t7val% (fastRun pI1799 1 1468 (init pI1799) (init pI1799))
theorem I1799_seg2 : segOK pI1799 1039 430 I1799_cp1.1 I1799_cp1.2 I1799_cp2.1 I1799_cp2.2 = true := by
  decide +kernel
theorem I1799_fin : (prmOK pI1799 1799 && intTest pI1799 (runFrom pI1799 (fmask pI1799) (cmask pI1799) (hmask pI1799) 1469 330 (true, I1799_cp2.1, I1799_cp2.2)) 1799 21 false) = true := by
  decide +kernel
theorem I1799_ok : RunOK pI1799 1799 (runFrom pI1799 (fmask pI1799) (cmask pI1799) (hmask pI1799) 1469 330 (true, I1799_cp2.1, I1799_cp2.2)) ∧ intTest pI1799 (runFrom pI1799 (fmask pI1799) (cmask pI1799) (hmask pI1799) 1469 330 (true, I1799_cp2.1, I1799_cp2.2)) 1799 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1799_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1799_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1799_fin) true) I1799_seg1) I1799_seg2) (by decide) rfl I1799_fin intTest_fst
theorem link1799 : linkOK pL1799 pH1799 pI1799 = true := by decide +kernel
theorem cvx1799 : ConvexBetweenHumps 1799 :=
  cvx_of L1799_ok H1799_ok I1799_ok link1799 (by decide)

/-! ### `N = 1800` -/

def pL1800 : Prm := ⟨80, 37, 40, 1802, 11, 18446744073709551616, 107222319892581191, 107222319892581191⟩
def pH1800 : Prm := ⟨80, 37, 40, 1802, 11, 18446744073709551616, 107223419404208967, 107223419404208967⟩
def pI1800 : Prm := ⟨67, 34, 30, 1802, 11, 18446744073709551616, 107222319892581191, 107223419404208967⟩
noncomputable def L1800_cp1 : Nat × Nat := t7val% (fastRun pL1800 1 1038 (init pL1800) (init pL1800))
theorem L1800_seg1 : segOK pL1800 1 1038 (init pL1800) (init pL1800) L1800_cp1.1 L1800_cp1.2 = true := by
  decide +kernel
noncomputable def L1800_cp2 : Nat × Nat := t7val% (fastRun pL1800 1 1469 (init pL1800) (init pL1800))
theorem L1800_seg2 : segOK pL1800 1039 431 L1800_cp1.1 L1800_cp1.2 L1800_cp2.1 L1800_cp2.2 = true := by
  decide +kernel
theorem L1800_fin : (prmOK pL1800 1800 && ptTest pL1800 (runFrom pL1800 (fmask pL1800) (cmask pL1800) (hmask pL1800) 1470 330 (true, L1800_cp2.1, L1800_cp2.2)) 1800 900 false) = true := by
  decide +kernel
theorem L1800_ok : RunOK pL1800 1800 (runFrom pL1800 (fmask pL1800) (cmask pL1800) (hmask pL1800) 1470 330 (true, L1800_cp2.1, L1800_cp2.2)) ∧ ptTest pL1800 (runFrom pL1800 (fmask pL1800) (cmask pL1800) (hmask pL1800) 1470 330 (true, L1800_cp2.1, L1800_cp2.2)) 1800 900 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1800_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1800_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1800_fin) true) L1800_seg1) L1800_seg2) (by decide) rfl L1800_fin ptTest_fst
noncomputable def H1800_cp1 : Nat × Nat := t7val% (fastRun pH1800 1 1038 (init pH1800) (init pH1800))
theorem H1800_seg1 : segOK pH1800 1 1038 (init pH1800) (init pH1800) H1800_cp1.1 H1800_cp1.2 = true := by
  decide +kernel
noncomputable def H1800_cp2 : Nat × Nat := t7val% (fastRun pH1800 1 1469 (init pH1800) (init pH1800))
theorem H1800_seg2 : segOK pH1800 1039 431 H1800_cp1.1 H1800_cp1.2 H1800_cp2.1 H1800_cp2.2 = true := by
  decide +kernel
theorem H1800_fin : (prmOK pH1800 1800 && ptTest pH1800 (runFrom pH1800 (fmask pH1800) (cmask pH1800) (hmask pH1800) 1470 330 (true, H1800_cp2.1, H1800_cp2.2)) 1800 900 true) = true := by
  decide +kernel
theorem H1800_ok : RunOK pH1800 1800 (runFrom pH1800 (fmask pH1800) (cmask pH1800) (hmask pH1800) 1470 330 (true, H1800_cp2.1, H1800_cp2.2)) ∧ ptTest pH1800 (runFrom pH1800 (fmask pH1800) (cmask pH1800) (hmask pH1800) 1470 330 (true, H1800_cp2.1, H1800_cp2.2)) 1800 900 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1800_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1800_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1800_fin) true) H1800_seg1) H1800_seg2) (by decide) rfl H1800_fin ptTest_fst
noncomputable def I1800_cp1 : Nat × Nat := t7val% (fastRun pI1800 1 1038 (init pI1800) (init pI1800))
theorem I1800_seg1 : segOK pI1800 1 1038 (init pI1800) (init pI1800) I1800_cp1.1 I1800_cp1.2 = true := by
  decide +kernel
noncomputable def I1800_cp2 : Nat × Nat := t7val% (fastRun pI1800 1 1469 (init pI1800) (init pI1800))
theorem I1800_seg2 : segOK pI1800 1039 431 I1800_cp1.1 I1800_cp1.2 I1800_cp2.1 I1800_cp2.2 = true := by
  decide +kernel
theorem I1800_fin : (prmOK pI1800 1800 && intTest pI1800 (runFrom pI1800 (fmask pI1800) (cmask pI1800) (hmask pI1800) 1470 330 (true, I1800_cp2.1, I1800_cp2.2)) 1800 21 true) = true := by
  decide +kernel
theorem I1800_ok : RunOK pI1800 1800 (runFrom pI1800 (fmask pI1800) (cmask pI1800) (hmask pI1800) 1470 330 (true, I1800_cp2.1, I1800_cp2.2)) ∧ intTest pI1800 (runFrom pI1800 (fmask pI1800) (cmask pI1800) (hmask pI1800) 1470 330 (true, I1800_cp2.1, I1800_cp2.2)) 1800 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1800_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1800_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1800_fin) true) I1800_seg1) I1800_seg2) (by decide) rfl I1800_fin intTest_fst
theorem link1800 : linkOK pL1800 pH1800 pI1800 = true := by decide +kernel
theorem cvx1800 : ConvexBetweenHumps 1800 :=
  cvx_of L1800_ok H1800_ok I1800_ok link1800 (by decide)
theorem cenlink1800 : cenLinkOK pI1800 1800 = true := by decide +kernel
theorem cen1800 : CenterUniqueMin 1800 ∧ DipHyp 1800 ∧ OnePointHyps 1800 :=
  cen_of L1800_ok H1800_ok I1800_ok link1800 cenlink1800

/-! ### `N = 1801` -/

def pL1801 : Prm := ⟨80, 37, 40, 1803, 11, 18446744073709551616, 107173498822154211, 107173498822154211⟩
def pH1801 : Prm := ⟨80, 37, 40, 1803, 11, 18446744073709551616, 107174598333781987, 107174598333781987⟩
def pI1801 : Prm := ⟨67, 34, 30, 1803, 11, 18446744073709551616, 107173498822154211, 107174598333781987⟩
noncomputable def L1801_cp1 : Nat × Nat := t7val% (fastRun pL1801 1 1039 (init pL1801) (init pL1801))
theorem L1801_seg1 : segOK pL1801 1 1039 (init pL1801) (init pL1801) L1801_cp1.1 L1801_cp1.2 = true := by
  decide +kernel
noncomputable def L1801_cp2 : Nat × Nat := t7val% (fastRun pL1801 1 1470 (init pL1801) (init pL1801))
theorem L1801_seg2 : segOK pL1801 1040 431 L1801_cp1.1 L1801_cp1.2 L1801_cp2.1 L1801_cp2.2 = true := by
  decide +kernel
theorem L1801_fin : (prmOK pL1801 1801 && ptTest pL1801 (runFrom pL1801 (fmask pL1801) (cmask pL1801) (hmask pL1801) 1471 330 (true, L1801_cp2.1, L1801_cp2.2)) 1801 901 false) = true := by
  decide +kernel
theorem L1801_ok : RunOK pL1801 1801 (runFrom pL1801 (fmask pL1801) (cmask pL1801) (hmask pL1801) 1471 330 (true, L1801_cp2.1, L1801_cp2.2)) ∧ ptTest pL1801 (runFrom pL1801 (fmask pL1801) (cmask pL1801) (hmask pL1801) 1471 330 (true, L1801_cp2.1, L1801_cp2.2)) 1801 901 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1801_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1801_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1801_fin) true) L1801_seg1) L1801_seg2) (by decide) rfl L1801_fin ptTest_fst
noncomputable def H1801_cp1 : Nat × Nat := t7val% (fastRun pH1801 1 1039 (init pH1801) (init pH1801))
theorem H1801_seg1 : segOK pH1801 1 1039 (init pH1801) (init pH1801) H1801_cp1.1 H1801_cp1.2 = true := by
  decide +kernel
noncomputable def H1801_cp2 : Nat × Nat := t7val% (fastRun pH1801 1 1470 (init pH1801) (init pH1801))
theorem H1801_seg2 : segOK pH1801 1040 431 H1801_cp1.1 H1801_cp1.2 H1801_cp2.1 H1801_cp2.2 = true := by
  decide +kernel
theorem H1801_fin : (prmOK pH1801 1801 && ptTest pH1801 (runFrom pH1801 (fmask pH1801) (cmask pH1801) (hmask pH1801) 1471 330 (true, H1801_cp2.1, H1801_cp2.2)) 1801 901 true) = true := by
  decide +kernel
theorem H1801_ok : RunOK pH1801 1801 (runFrom pH1801 (fmask pH1801) (cmask pH1801) (hmask pH1801) 1471 330 (true, H1801_cp2.1, H1801_cp2.2)) ∧ ptTest pH1801 (runFrom pH1801 (fmask pH1801) (cmask pH1801) (hmask pH1801) 1471 330 (true, H1801_cp2.1, H1801_cp2.2)) 1801 901 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1801_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1801_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1801_fin) true) H1801_seg1) H1801_seg2) (by decide) rfl H1801_fin ptTest_fst
noncomputable def I1801_cp1 : Nat × Nat := t7val% (fastRun pI1801 1 1039 (init pI1801) (init pI1801))
theorem I1801_seg1 : segOK pI1801 1 1039 (init pI1801) (init pI1801) I1801_cp1.1 I1801_cp1.2 = true := by
  decide +kernel
noncomputable def I1801_cp2 : Nat × Nat := t7val% (fastRun pI1801 1 1470 (init pI1801) (init pI1801))
theorem I1801_seg2 : segOK pI1801 1040 431 I1801_cp1.1 I1801_cp1.2 I1801_cp2.1 I1801_cp2.2 = true := by
  decide +kernel
theorem I1801_fin : (prmOK pI1801 1801 && intTest pI1801 (runFrom pI1801 (fmask pI1801) (cmask pI1801) (hmask pI1801) 1471 330 (true, I1801_cp2.1, I1801_cp2.2)) 1801 21 false) = true := by
  decide +kernel
theorem I1801_ok : RunOK pI1801 1801 (runFrom pI1801 (fmask pI1801) (cmask pI1801) (hmask pI1801) 1471 330 (true, I1801_cp2.1, I1801_cp2.2)) ∧ intTest pI1801 (runFrom pI1801 (fmask pI1801) (cmask pI1801) (hmask pI1801) 1471 330 (true, I1801_cp2.1, I1801_cp2.2)) 1801 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1801_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1801_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1801_fin) true) I1801_seg1) I1801_seg2) (by decide) rfl I1801_fin intTest_fst
theorem link1801 : linkOK pL1801 pH1801 pI1801 = true := by decide +kernel
theorem cvx1801 : ConvexBetweenHumps 1801 :=
  cvx_of L1801_ok H1801_ok I1801_ok link1801 (by decide)

/-! ### `N = 1802` -/

def pL1802 : Prm := ⟨80, 37, 40, 1804, 11, 18446744073709551616, 107124745181088520, 107124745181088520⟩
def pH1802 : Prm := ⟨80, 37, 40, 1804, 11, 18446744073709551616, 107125844692716296, 107125844692716296⟩
def pI1802 : Prm := ⟨67, 34, 30, 1804, 11, 18446744073709551616, 107124745181088520, 107125844692716296⟩
noncomputable def L1802_cp1 : Nat × Nat := t7val% (fastRun pL1802 1 1039 (init pL1802) (init pL1802))
theorem L1802_seg1 : segOK pL1802 1 1039 (init pL1802) (init pL1802) L1802_cp1.1 L1802_cp1.2 = true := by
  decide +kernel
noncomputable def L1802_cp2 : Nat × Nat := t7val% (fastRun pL1802 1 1470 (init pL1802) (init pL1802))
theorem L1802_seg2 : segOK pL1802 1040 431 L1802_cp1.1 L1802_cp1.2 L1802_cp2.1 L1802_cp2.2 = true := by
  decide +kernel
theorem L1802_fin : (prmOK pL1802 1802 && ptTest pL1802 (runFrom pL1802 (fmask pL1802) (cmask pL1802) (hmask pL1802) 1471 331 (true, L1802_cp2.1, L1802_cp2.2)) 1802 901 false) = true := by
  decide +kernel
theorem L1802_ok : RunOK pL1802 1802 (runFrom pL1802 (fmask pL1802) (cmask pL1802) (hmask pL1802) 1471 331 (true, L1802_cp2.1, L1802_cp2.2)) ∧ ptTest pL1802 (runFrom pL1802 (fmask pL1802) (cmask pL1802) (hmask pL1802) 1471 331 (true, L1802_cp2.1, L1802_cp2.2)) 1802 901 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1802_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1802_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1802_fin) true) L1802_seg1) L1802_seg2) (by decide) rfl L1802_fin ptTest_fst
noncomputable def H1802_cp1 : Nat × Nat := t7val% (fastRun pH1802 1 1039 (init pH1802) (init pH1802))
theorem H1802_seg1 : segOK pH1802 1 1039 (init pH1802) (init pH1802) H1802_cp1.1 H1802_cp1.2 = true := by
  decide +kernel
noncomputable def H1802_cp2 : Nat × Nat := t7val% (fastRun pH1802 1 1470 (init pH1802) (init pH1802))
theorem H1802_seg2 : segOK pH1802 1040 431 H1802_cp1.1 H1802_cp1.2 H1802_cp2.1 H1802_cp2.2 = true := by
  decide +kernel
theorem H1802_fin : (prmOK pH1802 1802 && ptTest pH1802 (runFrom pH1802 (fmask pH1802) (cmask pH1802) (hmask pH1802) 1471 331 (true, H1802_cp2.1, H1802_cp2.2)) 1802 901 true) = true := by
  decide +kernel
theorem H1802_ok : RunOK pH1802 1802 (runFrom pH1802 (fmask pH1802) (cmask pH1802) (hmask pH1802) 1471 331 (true, H1802_cp2.1, H1802_cp2.2)) ∧ ptTest pH1802 (runFrom pH1802 (fmask pH1802) (cmask pH1802) (hmask pH1802) 1471 331 (true, H1802_cp2.1, H1802_cp2.2)) 1802 901 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1802_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1802_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1802_fin) true) H1802_seg1) H1802_seg2) (by decide) rfl H1802_fin ptTest_fst
noncomputable def I1802_cp1 : Nat × Nat := t7val% (fastRun pI1802 1 1039 (init pI1802) (init pI1802))
theorem I1802_seg1 : segOK pI1802 1 1039 (init pI1802) (init pI1802) I1802_cp1.1 I1802_cp1.2 = true := by
  decide +kernel
noncomputable def I1802_cp2 : Nat × Nat := t7val% (fastRun pI1802 1 1470 (init pI1802) (init pI1802))
theorem I1802_seg2 : segOK pI1802 1040 431 I1802_cp1.1 I1802_cp1.2 I1802_cp2.1 I1802_cp2.2 = true := by
  decide +kernel
theorem I1802_fin : (prmOK pI1802 1802 && intTest pI1802 (runFrom pI1802 (fmask pI1802) (cmask pI1802) (hmask pI1802) 1471 331 (true, I1802_cp2.1, I1802_cp2.2)) 1802 21 true) = true := by
  decide +kernel
theorem I1802_ok : RunOK pI1802 1802 (runFrom pI1802 (fmask pI1802) (cmask pI1802) (hmask pI1802) 1471 331 (true, I1802_cp2.1, I1802_cp2.2)) ∧ intTest pI1802 (runFrom pI1802 (fmask pI1802) (cmask pI1802) (hmask pI1802) 1471 331 (true, I1802_cp2.1, I1802_cp2.2)) 1802 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1802_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1802_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1802_fin) true) I1802_seg1) I1802_seg2) (by decide) rfl I1802_fin intTest_fst
theorem link1802 : linkOK pL1802 pH1802 pI1802 = true := by decide +kernel
theorem cvx1802 : ConvexBetweenHumps 1802 :=
  cvx_of L1802_ok H1802_ok I1802_ok link1802 (by decide)
theorem cenlink1802 : cenLinkOK pI1802 1802 = true := by decide +kernel
theorem cen1802 : CenterUniqueMin 1802 ∧ DipHyp 1802 ∧ OnePointHyps 1802 :=
  cen_of L1802_ok H1802_ok I1802_ok link1802 cenlink1802

/-! ### `N = 1803` -/

def pL1803 : Prm := ⟨80, 37, 40, 1805, 11, 18446744073709551616, 107076020504307165, 107076020504307165⟩
def pH1803 : Prm := ⟨80, 37, 40, 1805, 11, 18446744073709551616, 107077120015934941, 107077120015934941⟩
def pI1803 : Prm := ⟨67, 34, 30, 1805, 11, 18446744073709551616, 107076020504307165, 107077120015934941⟩
noncomputable def L1803_cp1 : Nat × Nat := t7val% (fastRun pL1803 1 1040 (init pL1803) (init pL1803))
theorem L1803_seg1 : segOK pL1803 1 1040 (init pL1803) (init pL1803) L1803_cp1.1 L1803_cp1.2 = true := by
  decide +kernel
noncomputable def L1803_cp2 : Nat × Nat := t7val% (fastRun pL1803 1 1471 (init pL1803) (init pL1803))
theorem L1803_seg2 : segOK pL1803 1041 431 L1803_cp1.1 L1803_cp1.2 L1803_cp2.1 L1803_cp2.2 = true := by
  decide +kernel
theorem L1803_fin : (prmOK pL1803 1803 && ptTest pL1803 (runFrom pL1803 (fmask pL1803) (cmask pL1803) (hmask pL1803) 1472 331 (true, L1803_cp2.1, L1803_cp2.2)) 1803 902 false) = true := by
  decide +kernel
theorem L1803_ok : RunOK pL1803 1803 (runFrom pL1803 (fmask pL1803) (cmask pL1803) (hmask pL1803) 1472 331 (true, L1803_cp2.1, L1803_cp2.2)) ∧ ptTest pL1803 (runFrom pL1803 (fmask pL1803) (cmask pL1803) (hmask pL1803) 1472 331 (true, L1803_cp2.1, L1803_cp2.2)) 1803 902 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1803_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1803_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1803_fin) true) L1803_seg1) L1803_seg2) (by decide) rfl L1803_fin ptTest_fst
noncomputable def H1803_cp1 : Nat × Nat := t7val% (fastRun pH1803 1 1040 (init pH1803) (init pH1803))
theorem H1803_seg1 : segOK pH1803 1 1040 (init pH1803) (init pH1803) H1803_cp1.1 H1803_cp1.2 = true := by
  decide +kernel
noncomputable def H1803_cp2 : Nat × Nat := t7val% (fastRun pH1803 1 1471 (init pH1803) (init pH1803))
theorem H1803_seg2 : segOK pH1803 1041 431 H1803_cp1.1 H1803_cp1.2 H1803_cp2.1 H1803_cp2.2 = true := by
  decide +kernel
theorem H1803_fin : (prmOK pH1803 1803 && ptTest pH1803 (runFrom pH1803 (fmask pH1803) (cmask pH1803) (hmask pH1803) 1472 331 (true, H1803_cp2.1, H1803_cp2.2)) 1803 902 true) = true := by
  decide +kernel
theorem H1803_ok : RunOK pH1803 1803 (runFrom pH1803 (fmask pH1803) (cmask pH1803) (hmask pH1803) 1472 331 (true, H1803_cp2.1, H1803_cp2.2)) ∧ ptTest pH1803 (runFrom pH1803 (fmask pH1803) (cmask pH1803) (hmask pH1803) 1472 331 (true, H1803_cp2.1, H1803_cp2.2)) 1803 902 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1803_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1803_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1803_fin) true) H1803_seg1) H1803_seg2) (by decide) rfl H1803_fin ptTest_fst
noncomputable def I1803_cp1 : Nat × Nat := t7val% (fastRun pI1803 1 1040 (init pI1803) (init pI1803))
theorem I1803_seg1 : segOK pI1803 1 1040 (init pI1803) (init pI1803) I1803_cp1.1 I1803_cp1.2 = true := by
  decide +kernel
noncomputable def I1803_cp2 : Nat × Nat := t7val% (fastRun pI1803 1 1471 (init pI1803) (init pI1803))
theorem I1803_seg2 : segOK pI1803 1041 431 I1803_cp1.1 I1803_cp1.2 I1803_cp2.1 I1803_cp2.2 = true := by
  decide +kernel
theorem I1803_fin : (prmOK pI1803 1803 && intTest pI1803 (runFrom pI1803 (fmask pI1803) (cmask pI1803) (hmask pI1803) 1472 331 (true, I1803_cp2.1, I1803_cp2.2)) 1803 21 false) = true := by
  decide +kernel
theorem I1803_ok : RunOK pI1803 1803 (runFrom pI1803 (fmask pI1803) (cmask pI1803) (hmask pI1803) 1472 331 (true, I1803_cp2.1, I1803_cp2.2)) ∧ intTest pI1803 (runFrom pI1803 (fmask pI1803) (cmask pI1803) (hmask pI1803) 1472 331 (true, I1803_cp2.1, I1803_cp2.2)) 1803 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1803_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1803_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1803_fin) true) I1803_seg1) I1803_seg2) (by decide) rfl I1803_fin intTest_fst
theorem link1803 : linkOK pL1803 pH1803 pI1803 = true := by decide +kernel
theorem cvx1803 : ConvexBetweenHumps 1803 :=
  cvx_of L1803_ok H1803_ok I1803_ok link1803 (by decide)

/-! ### `N = 1804` -/

def pL1804 : Prm := ⟨80, 37, 40, 1806, 11, 18446744073709551616, 107027363044970903, 107027363044970903⟩
def pH1804 : Prm := ⟨80, 37, 40, 1806, 11, 18446744073709551616, 107028462556598679, 107028462556598679⟩
def pI1804 : Prm := ⟨67, 34, 30, 1806, 11, 18446744073709551616, 107027363044970903, 107028462556598679⟩
noncomputable def L1804_cp1 : Nat × Nat := t7val% (fastRun pL1804 1 1041 (init pL1804) (init pL1804))
theorem L1804_seg1 : segOK pL1804 1 1041 (init pL1804) (init pL1804) L1804_cp1.1 L1804_cp1.2 = true := by
  decide +kernel
noncomputable def L1804_cp2 : Nat × Nat := t7val% (fastRun pL1804 1 1472 (init pL1804) (init pL1804))
theorem L1804_seg2 : segOK pL1804 1042 431 L1804_cp1.1 L1804_cp1.2 L1804_cp2.1 L1804_cp2.2 = true := by
  decide +kernel
theorem L1804_fin : (prmOK pL1804 1804 && ptTest pL1804 (runFrom pL1804 (fmask pL1804) (cmask pL1804) (hmask pL1804) 1473 331 (true, L1804_cp2.1, L1804_cp2.2)) 1804 902 false) = true := by
  decide +kernel
theorem L1804_ok : RunOK pL1804 1804 (runFrom pL1804 (fmask pL1804) (cmask pL1804) (hmask pL1804) 1473 331 (true, L1804_cp2.1, L1804_cp2.2)) ∧ ptTest pL1804 (runFrom pL1804 (fmask pL1804) (cmask pL1804) (hmask pL1804) 1473 331 (true, L1804_cp2.1, L1804_cp2.2)) 1804 902 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1804_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1804_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1804_fin) true) L1804_seg1) L1804_seg2) (by decide) rfl L1804_fin ptTest_fst
noncomputable def H1804_cp1 : Nat × Nat := t7val% (fastRun pH1804 1 1041 (init pH1804) (init pH1804))
theorem H1804_seg1 : segOK pH1804 1 1041 (init pH1804) (init pH1804) H1804_cp1.1 H1804_cp1.2 = true := by
  decide +kernel
noncomputable def H1804_cp2 : Nat × Nat := t7val% (fastRun pH1804 1 1472 (init pH1804) (init pH1804))
theorem H1804_seg2 : segOK pH1804 1042 431 H1804_cp1.1 H1804_cp1.2 H1804_cp2.1 H1804_cp2.2 = true := by
  decide +kernel
theorem H1804_fin : (prmOK pH1804 1804 && ptTest pH1804 (runFrom pH1804 (fmask pH1804) (cmask pH1804) (hmask pH1804) 1473 331 (true, H1804_cp2.1, H1804_cp2.2)) 1804 902 true) = true := by
  decide +kernel
theorem H1804_ok : RunOK pH1804 1804 (runFrom pH1804 (fmask pH1804) (cmask pH1804) (hmask pH1804) 1473 331 (true, H1804_cp2.1, H1804_cp2.2)) ∧ ptTest pH1804 (runFrom pH1804 (fmask pH1804) (cmask pH1804) (hmask pH1804) 1473 331 (true, H1804_cp2.1, H1804_cp2.2)) 1804 902 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1804_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1804_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1804_fin) true) H1804_seg1) H1804_seg2) (by decide) rfl H1804_fin ptTest_fst
noncomputable def I1804_cp1 : Nat × Nat := t7val% (fastRun pI1804 1 1041 (init pI1804) (init pI1804))
theorem I1804_seg1 : segOK pI1804 1 1041 (init pI1804) (init pI1804) I1804_cp1.1 I1804_cp1.2 = true := by
  decide +kernel
noncomputable def I1804_cp2 : Nat × Nat := t7val% (fastRun pI1804 1 1472 (init pI1804) (init pI1804))
theorem I1804_seg2 : segOK pI1804 1042 431 I1804_cp1.1 I1804_cp1.2 I1804_cp2.1 I1804_cp2.2 = true := by
  decide +kernel
theorem I1804_fin : (prmOK pI1804 1804 && intTest pI1804 (runFrom pI1804 (fmask pI1804) (cmask pI1804) (hmask pI1804) 1473 331 (true, I1804_cp2.1, I1804_cp2.2)) 1804 21 true) = true := by
  decide +kernel
theorem I1804_ok : RunOK pI1804 1804 (runFrom pI1804 (fmask pI1804) (cmask pI1804) (hmask pI1804) 1473 331 (true, I1804_cp2.1, I1804_cp2.2)) ∧ intTest pI1804 (runFrom pI1804 (fmask pI1804) (cmask pI1804) (hmask pI1804) 1473 331 (true, I1804_cp2.1, I1804_cp2.2)) 1804 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1804_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1804_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1804_fin) true) I1804_seg1) I1804_seg2) (by decide) rfl I1804_fin intTest_fst
theorem link1804 : linkOK pL1804 pH1804 pI1804 = true := by decide +kernel
theorem cvx1804 : ConvexBetweenHumps 1804 :=
  cvx_of L1804_ok H1804_ok I1804_ok link1804 (by decide)
theorem cenlink1804 : cenLinkOK pI1804 1804 = true := by decide +kernel
theorem cen1804 : CenterUniqueMin 1804 ∧ DipHyp 1804 ∧ OnePointHyps 1804 :=
  cen_of L1804_ok H1804_ok I1804_ok link1804 cenlink1804

/-! ### `N = 1805` -/

def pL1805 : Prm := ⟨80, 37, 40, 1807, 11, 18446744073709551616, 106978734467830964, 106978734467830964⟩
def pH1805 : Prm := ⟨80, 37, 40, 1807, 11, 18446744073709551616, 106979833979458740, 106979833979458740⟩
def pI1805 : Prm := ⟨67, 34, 30, 1807, 11, 18446744073709551616, 106978734467830964, 106979833979458740⟩
noncomputable def L1805_cp1 : Nat × Nat := t7val% (fastRun pL1805 1 1041 (init pL1805) (init pL1805))
theorem L1805_seg1 : segOK pL1805 1 1041 (init pL1805) (init pL1805) L1805_cp1.1 L1805_cp1.2 = true := by
  decide +kernel
noncomputable def L1805_cp2 : Nat × Nat := t7val% (fastRun pL1805 1 1473 (init pL1805) (init pL1805))
theorem L1805_seg2 : segOK pL1805 1042 432 L1805_cp1.1 L1805_cp1.2 L1805_cp2.1 L1805_cp2.2 = true := by
  decide +kernel
theorem L1805_fin : (prmOK pL1805 1805 && ptTest pL1805 (runFrom pL1805 (fmask pL1805) (cmask pL1805) (hmask pL1805) 1474 331 (true, L1805_cp2.1, L1805_cp2.2)) 1805 903 false) = true := by
  decide +kernel
theorem L1805_ok : RunOK pL1805 1805 (runFrom pL1805 (fmask pL1805) (cmask pL1805) (hmask pL1805) 1474 331 (true, L1805_cp2.1, L1805_cp2.2)) ∧ ptTest pL1805 (runFrom pL1805 (fmask pL1805) (cmask pL1805) (hmask pL1805) 1474 331 (true, L1805_cp2.1, L1805_cp2.2)) 1805 903 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1805_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1805_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1805_fin) true) L1805_seg1) L1805_seg2) (by decide) rfl L1805_fin ptTest_fst
noncomputable def H1805_cp1 : Nat × Nat := t7val% (fastRun pH1805 1 1041 (init pH1805) (init pH1805))
theorem H1805_seg1 : segOK pH1805 1 1041 (init pH1805) (init pH1805) H1805_cp1.1 H1805_cp1.2 = true := by
  decide +kernel
noncomputable def H1805_cp2 : Nat × Nat := t7val% (fastRun pH1805 1 1473 (init pH1805) (init pH1805))
theorem H1805_seg2 : segOK pH1805 1042 432 H1805_cp1.1 H1805_cp1.2 H1805_cp2.1 H1805_cp2.2 = true := by
  decide +kernel
theorem H1805_fin : (prmOK pH1805 1805 && ptTest pH1805 (runFrom pH1805 (fmask pH1805) (cmask pH1805) (hmask pH1805) 1474 331 (true, H1805_cp2.1, H1805_cp2.2)) 1805 903 true) = true := by
  decide +kernel
theorem H1805_ok : RunOK pH1805 1805 (runFrom pH1805 (fmask pH1805) (cmask pH1805) (hmask pH1805) 1474 331 (true, H1805_cp2.1, H1805_cp2.2)) ∧ ptTest pH1805 (runFrom pH1805 (fmask pH1805) (cmask pH1805) (hmask pH1805) 1474 331 (true, H1805_cp2.1, H1805_cp2.2)) 1805 903 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1805_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1805_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1805_fin) true) H1805_seg1) H1805_seg2) (by decide) rfl H1805_fin ptTest_fst
noncomputable def I1805_cp1 : Nat × Nat := t7val% (fastRun pI1805 1 1041 (init pI1805) (init pI1805))
theorem I1805_seg1 : segOK pI1805 1 1041 (init pI1805) (init pI1805) I1805_cp1.1 I1805_cp1.2 = true := by
  decide +kernel
noncomputable def I1805_cp2 : Nat × Nat := t7val% (fastRun pI1805 1 1473 (init pI1805) (init pI1805))
theorem I1805_seg2 : segOK pI1805 1042 432 I1805_cp1.1 I1805_cp1.2 I1805_cp2.1 I1805_cp2.2 = true := by
  decide +kernel
theorem I1805_fin : (prmOK pI1805 1805 && intTest pI1805 (runFrom pI1805 (fmask pI1805) (cmask pI1805) (hmask pI1805) 1474 331 (true, I1805_cp2.1, I1805_cp2.2)) 1805 21 false) = true := by
  decide +kernel
theorem I1805_ok : RunOK pI1805 1805 (runFrom pI1805 (fmask pI1805) (cmask pI1805) (hmask pI1805) 1474 331 (true, I1805_cp2.1, I1805_cp2.2)) ∧ intTest pI1805 (runFrom pI1805 (fmask pI1805) (cmask pI1805) (hmask pI1805) 1474 331 (true, I1805_cp2.1, I1805_cp2.2)) 1805 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1805_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1805_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1805_fin) true) I1805_seg1) I1805_seg2) (by decide) rfl I1805_fin intTest_fst
theorem link1805 : linkOK pL1805 pH1805 pI1805 = true := by decide +kernel
theorem cvx1805 : ConvexBetweenHumps 1805 :=
  cvx_of L1805_ok H1805_ok I1805_ok link1805 (by decide)

/-! ### `N = 1806` -/

def pL1806 : Prm := ⟨80, 37, 40, 1808, 11, 18446744073709551616, 106930172897123815, 106930172897123815⟩
def pH1806 : Prm := ⟨80, 37, 40, 1808, 11, 18446744073709551616, 106931272408751591, 106931272408751591⟩
def pI1806 : Prm := ⟨67, 34, 30, 1808, 11, 18446744073709551616, 106930172897123815, 106931272408751591⟩
noncomputable def L1806_cp1 : Nat × Nat := t7val% (fastRun pL1806 1 1042 (init pL1806) (init pL1806))
theorem L1806_seg1 : segOK pL1806 1 1042 (init pL1806) (init pL1806) L1806_cp1.1 L1806_cp1.2 = true := by
  decide +kernel
noncomputable def L1806_cp2 : Nat × Nat := t7val% (fastRun pL1806 1 1474 (init pL1806) (init pL1806))
theorem L1806_seg2 : segOK pL1806 1043 432 L1806_cp1.1 L1806_cp1.2 L1806_cp2.1 L1806_cp2.2 = true := by
  decide +kernel
theorem L1806_fin : (prmOK pL1806 1806 && ptTest pL1806 (runFrom pL1806 (fmask pL1806) (cmask pL1806) (hmask pL1806) 1475 331 (true, L1806_cp2.1, L1806_cp2.2)) 1806 903 false) = true := by
  decide +kernel
theorem L1806_ok : RunOK pL1806 1806 (runFrom pL1806 (fmask pL1806) (cmask pL1806) (hmask pL1806) 1475 331 (true, L1806_cp2.1, L1806_cp2.2)) ∧ ptTest pL1806 (runFrom pL1806 (fmask pL1806) (cmask pL1806) (hmask pL1806) 1475 331 (true, L1806_cp2.1, L1806_cp2.2)) 1806 903 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1806_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1806_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1806_fin) true) L1806_seg1) L1806_seg2) (by decide) rfl L1806_fin ptTest_fst
noncomputable def H1806_cp1 : Nat × Nat := t7val% (fastRun pH1806 1 1042 (init pH1806) (init pH1806))
theorem H1806_seg1 : segOK pH1806 1 1042 (init pH1806) (init pH1806) H1806_cp1.1 H1806_cp1.2 = true := by
  decide +kernel
noncomputable def H1806_cp2 : Nat × Nat := t7val% (fastRun pH1806 1 1474 (init pH1806) (init pH1806))
theorem H1806_seg2 : segOK pH1806 1043 432 H1806_cp1.1 H1806_cp1.2 H1806_cp2.1 H1806_cp2.2 = true := by
  decide +kernel
theorem H1806_fin : (prmOK pH1806 1806 && ptTest pH1806 (runFrom pH1806 (fmask pH1806) (cmask pH1806) (hmask pH1806) 1475 331 (true, H1806_cp2.1, H1806_cp2.2)) 1806 903 true) = true := by
  decide +kernel
theorem H1806_ok : RunOK pH1806 1806 (runFrom pH1806 (fmask pH1806) (cmask pH1806) (hmask pH1806) 1475 331 (true, H1806_cp2.1, H1806_cp2.2)) ∧ ptTest pH1806 (runFrom pH1806 (fmask pH1806) (cmask pH1806) (hmask pH1806) 1475 331 (true, H1806_cp2.1, H1806_cp2.2)) 1806 903 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1806_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1806_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1806_fin) true) H1806_seg1) H1806_seg2) (by decide) rfl H1806_fin ptTest_fst
noncomputable def I1806_cp1 : Nat × Nat := t7val% (fastRun pI1806 1 1042 (init pI1806) (init pI1806))
theorem I1806_seg1 : segOK pI1806 1 1042 (init pI1806) (init pI1806) I1806_cp1.1 I1806_cp1.2 = true := by
  decide +kernel
noncomputable def I1806_cp2 : Nat × Nat := t7val% (fastRun pI1806 1 1474 (init pI1806) (init pI1806))
theorem I1806_seg2 : segOK pI1806 1043 432 I1806_cp1.1 I1806_cp1.2 I1806_cp2.1 I1806_cp2.2 = true := by
  decide +kernel
theorem I1806_fin : (prmOK pI1806 1806 && intTest pI1806 (runFrom pI1806 (fmask pI1806) (cmask pI1806) (hmask pI1806) 1475 331 (true, I1806_cp2.1, I1806_cp2.2)) 1806 21 true) = true := by
  decide +kernel
theorem I1806_ok : RunOK pI1806 1806 (runFrom pI1806 (fmask pI1806) (cmask pI1806) (hmask pI1806) 1475 331 (true, I1806_cp2.1, I1806_cp2.2)) ∧ intTest pI1806 (runFrom pI1806 (fmask pI1806) (cmask pI1806) (hmask pI1806) 1475 331 (true, I1806_cp2.1, I1806_cp2.2)) 1806 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1806_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1806_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1806_fin) true) I1806_seg1) I1806_seg2) (by decide) rfl I1806_fin intTest_fst
theorem link1806 : linkOK pL1806 pH1806 pI1806 = true := by decide +kernel
theorem cvx1806 : ConvexBetweenHumps 1806 :=
  cvx_of L1806_ok H1806_ok I1806_ok link1806 (by decide)
theorem cenlink1806 : cenLinkOK pI1806 1806 = true := by decide +kernel
theorem cen1806 : CenterUniqueMin 1806 ∧ DipHyp 1806 ∧ OnePointHyps 1806 :=
  cen_of L1806_ok H1806_ok I1806_ok link1806 cenlink1806

/-! ### `N = 1807` -/

def pL1807 : Prm := ⟨80, 37, 40, 1809, 11, 18446744073709551616, 106881640126783232, 106881640126783232⟩
def pH1807 : Prm := ⟨80, 37, 40, 1809, 11, 18446744073709551616, 106882739638411008, 106882739638411008⟩
def pI1807 : Prm := ⟨67, 34, 30, 1809, 11, 18446744073709551616, 106881640126783232, 106882739638411008⟩
noncomputable def L1807_cp1 : Nat × Nat := t7val% (fastRun pL1807 1 1042 (init pL1807) (init pL1807))
theorem L1807_seg1 : segOK pL1807 1 1042 (init pL1807) (init pL1807) L1807_cp1.1 L1807_cp1.2 = true := by
  decide +kernel
noncomputable def L1807_cp2 : Nat × Nat := t7val% (fastRun pL1807 1 1474 (init pL1807) (init pL1807))
theorem L1807_seg2 : segOK pL1807 1043 432 L1807_cp1.1 L1807_cp1.2 L1807_cp2.1 L1807_cp2.2 = true := by
  decide +kernel
theorem L1807_fin : (prmOK pL1807 1807 && ptTest pL1807 (runFrom pL1807 (fmask pL1807) (cmask pL1807) (hmask pL1807) 1475 332 (true, L1807_cp2.1, L1807_cp2.2)) 1807 904 false) = true := by
  decide +kernel
theorem L1807_ok : RunOK pL1807 1807 (runFrom pL1807 (fmask pL1807) (cmask pL1807) (hmask pL1807) 1475 332 (true, L1807_cp2.1, L1807_cp2.2)) ∧ ptTest pL1807 (runFrom pL1807 (fmask pL1807) (cmask pL1807) (hmask pL1807) 1475 332 (true, L1807_cp2.1, L1807_cp2.2)) 1807 904 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1807_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1807_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1807_fin) true) L1807_seg1) L1807_seg2) (by decide) rfl L1807_fin ptTest_fst
noncomputable def H1807_cp1 : Nat × Nat := t7val% (fastRun pH1807 1 1042 (init pH1807) (init pH1807))
theorem H1807_seg1 : segOK pH1807 1 1042 (init pH1807) (init pH1807) H1807_cp1.1 H1807_cp1.2 = true := by
  decide +kernel
noncomputable def H1807_cp2 : Nat × Nat := t7val% (fastRun pH1807 1 1474 (init pH1807) (init pH1807))
theorem H1807_seg2 : segOK pH1807 1043 432 H1807_cp1.1 H1807_cp1.2 H1807_cp2.1 H1807_cp2.2 = true := by
  decide +kernel
theorem H1807_fin : (prmOK pH1807 1807 && ptTest pH1807 (runFrom pH1807 (fmask pH1807) (cmask pH1807) (hmask pH1807) 1475 332 (true, H1807_cp2.1, H1807_cp2.2)) 1807 904 true) = true := by
  decide +kernel
theorem H1807_ok : RunOK pH1807 1807 (runFrom pH1807 (fmask pH1807) (cmask pH1807) (hmask pH1807) 1475 332 (true, H1807_cp2.1, H1807_cp2.2)) ∧ ptTest pH1807 (runFrom pH1807 (fmask pH1807) (cmask pH1807) (hmask pH1807) 1475 332 (true, H1807_cp2.1, H1807_cp2.2)) 1807 904 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1807_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1807_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1807_fin) true) H1807_seg1) H1807_seg2) (by decide) rfl H1807_fin ptTest_fst
noncomputable def I1807_cp1 : Nat × Nat := t7val% (fastRun pI1807 1 1042 (init pI1807) (init pI1807))
theorem I1807_seg1 : segOK pI1807 1 1042 (init pI1807) (init pI1807) I1807_cp1.1 I1807_cp1.2 = true := by
  decide +kernel
noncomputable def I1807_cp2 : Nat × Nat := t7val% (fastRun pI1807 1 1474 (init pI1807) (init pI1807))
theorem I1807_seg2 : segOK pI1807 1043 432 I1807_cp1.1 I1807_cp1.2 I1807_cp2.1 I1807_cp2.2 = true := by
  decide +kernel
theorem I1807_fin : (prmOK pI1807 1807 && intTest pI1807 (runFrom pI1807 (fmask pI1807) (cmask pI1807) (hmask pI1807) 1475 332 (true, I1807_cp2.1, I1807_cp2.2)) 1807 21 false) = true := by
  decide +kernel
theorem I1807_ok : RunOK pI1807 1807 (runFrom pI1807 (fmask pI1807) (cmask pI1807) (hmask pI1807) 1475 332 (true, I1807_cp2.1, I1807_cp2.2)) ∧ intTest pI1807 (runFrom pI1807 (fmask pI1807) (cmask pI1807) (hmask pI1807) 1475 332 (true, I1807_cp2.1, I1807_cp2.2)) 1807 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1807_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1807_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1807_fin) true) I1807_seg1) I1807_seg2) (by decide) rfl I1807_fin intTest_fst
theorem link1807 : linkOK pL1807 pH1807 pI1807 = true := by decide +kernel
theorem cvx1807 : ConvexBetweenHumps 1807 :=
  cvx_of L1807_ok H1807_ok I1807_ok link1807 (by decide)

/-! ### The range -/

theorem cvx_1796_1807 {N : ℕ} (h1 : 1796 ≤ N) (h2 : N ≤ 1807) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1801
  · by_cases h4 : N ≤ 1798
    · by_cases h6 : N ≤ 1796
      · obtain rfl : N = 1796 := by omega
        exact cvx1796
      · by_cases h8 : N ≤ 1797
        · obtain rfl : N = 1797 := by omega
          exact cvx1797
        · obtain rfl : N = 1798 := by omega
          exact cvx1798
    · by_cases h6 : N ≤ 1799
      · obtain rfl : N = 1799 := by omega
        exact cvx1799
      · by_cases h8 : N ≤ 1800
        · obtain rfl : N = 1800 := by omega
          exact cvx1800
        · obtain rfl : N = 1801 := by omega
          exact cvx1801
  · by_cases h4 : N ≤ 1804
    · by_cases h6 : N ≤ 1802
      · obtain rfl : N = 1802 := by omega
        exact cvx1802
      · by_cases h8 : N ≤ 1803
        · obtain rfl : N = 1803 := by omega
          exact cvx1803
        · obtain rfl : N = 1804 := by omega
          exact cvx1804
    · by_cases h6 : N ≤ 1805
      · obtain rfl : N = 1805 := by omega
        exact cvx1805
      · by_cases h8 : N ≤ 1806
        · obtain rfl : N = 1806 := by omega
          exact cvx1806
        · obtain rfl : N = 1807 := by omega
          exact cvx1807

theorem cen_1796_1807 {N : ℕ} (h1 : 1796 ≤ N) (h2 : N ≤ 1807) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1800
  · by_cases h4 : N ≤ 1796
    · obtain rfl : N = 1796 := by omega
      exact cen1796
    · by_cases h6 : N ≤ 1798
      · obtain rfl : N = 1798 := by omega
        exact cen1798
      · obtain rfl : N = 1800 := by omega
        exact cen1800
  · by_cases h4 : N ≤ 1802
    · obtain rfl : N = 1802 := by omega
      exact cen1802
    · by_cases h6 : N ≤ 1804
      · obtain rfl : N = 1804 := by omega
        exact cen1804
      · obtain rfl : N = 1806 := by omega
        exact cen1806

end Kagey131.PaperD.T7
