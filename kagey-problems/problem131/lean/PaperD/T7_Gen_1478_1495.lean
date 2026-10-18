import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1478, …, 1495` (generated)

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

/-! ### `N = 1478` -/

def pL1478 : Prm := ⟨80, 38, 39, 1480, 11, 18446744073709551616, 125944294365687484, 125944294365687484⟩
def pH1478 : Prm := ⟨80, 38, 39, 1480, 11, 18446744073709551616, 125945393877315260, 125945393877315260⟩
def pI1478 : Prm := ⟨66, 33, 30, 1480, 11, 18446744073709551616, 125944294365687484, 125945393877315260⟩
noncomputable def L1478_cp1 : Nat × Nat := t7val% (fastRun pL1478 1 1044 (init pL1478) (init pL1478))
theorem L1478_seg1 : segOK pL1478 1 1044 (init pL1478) (init pL1478) L1478_cp1.1 L1478_cp1.2 = true := by
  decide +kernel
theorem L1478_fin : (prmOK pL1478 1478 && ptTest pL1478 (runFrom pL1478 (fmask pL1478) (cmask pL1478) (hmask pL1478) 1045 433 (true, L1478_cp1.1, L1478_cp1.2)) 1478 739 false) = true := by
  decide +kernel
theorem L1478_ok : RunOK pL1478 1478 (runFrom pL1478 (fmask pL1478) (cmask pL1478) (hmask pL1478) 1045 433 (true, L1478_cp1.1, L1478_cp1.2)) ∧ ptTest pL1478 (runFrom pL1478 (fmask pL1478) (cmask pL1478) (hmask pL1478) 1045 433 (true, L1478_cp1.1, L1478_cp1.2)) 1478 739 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1478_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1478_fin) true) L1478_seg1) (by decide) rfl L1478_fin ptTest_fst
noncomputable def H1478_cp1 : Nat × Nat := t7val% (fastRun pH1478 1 1044 (init pH1478) (init pH1478))
theorem H1478_seg1 : segOK pH1478 1 1044 (init pH1478) (init pH1478) H1478_cp1.1 H1478_cp1.2 = true := by
  decide +kernel
theorem H1478_fin : (prmOK pH1478 1478 && ptTest pH1478 (runFrom pH1478 (fmask pH1478) (cmask pH1478) (hmask pH1478) 1045 433 (true, H1478_cp1.1, H1478_cp1.2)) 1478 739 true) = true := by
  decide +kernel
theorem H1478_ok : RunOK pH1478 1478 (runFrom pH1478 (fmask pH1478) (cmask pH1478) (hmask pH1478) 1045 433 (true, H1478_cp1.1, H1478_cp1.2)) ∧ ptTest pH1478 (runFrom pH1478 (fmask pH1478) (cmask pH1478) (hmask pH1478) 1045 433 (true, H1478_cp1.1, H1478_cp1.2)) 1478 739 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1478_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1478_fin) true) H1478_seg1) (by decide) rfl H1478_fin ptTest_fst
noncomputable def I1478_cp1 : Nat × Nat := t7val% (fastRun pI1478 1 1044 (init pI1478) (init pI1478))
theorem I1478_seg1 : segOK pI1478 1 1044 (init pI1478) (init pI1478) I1478_cp1.1 I1478_cp1.2 = true := by
  decide +kernel
theorem I1478_fin : (prmOK pI1478 1478 && intTest pI1478 (runFrom pI1478 (fmask pI1478) (cmask pI1478) (hmask pI1478) 1045 433 (true, I1478_cp1.1, I1478_cp1.2)) 1478 20 true) = true := by
  decide +kernel
theorem I1478_ok : RunOK pI1478 1478 (runFrom pI1478 (fmask pI1478) (cmask pI1478) (hmask pI1478) 1045 433 (true, I1478_cp1.1, I1478_cp1.2)) ∧ intTest pI1478 (runFrom pI1478 (fmask pI1478) (cmask pI1478) (hmask pI1478) 1045 433 (true, I1478_cp1.1, I1478_cp1.2)) 1478 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1478_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1478_fin) true) I1478_seg1) (by decide) rfl I1478_fin intTest_fst
theorem link1478 : linkOK pL1478 pH1478 pI1478 = true := by decide +kernel
theorem cvx1478 : ConvexBetweenHumps 1478 :=
  cvx_of L1478_ok H1478_ok I1478_ok link1478 (by decide)
theorem cenlink1478 : cenLinkOK pI1478 1478 = true := by decide +kernel
theorem cen1478 : CenterUniqueMin 1478 ∧ DipHyp 1478 ∧ OnePointHyps 1478 :=
  cen_of L1478_ok H1478_ok I1478_ok link1478 cenlink1478

/-! ### `N = 1479` -/

def pL1479 : Prm := ⟨80, 38, 39, 1481, 11, 18446744073709551616, 125875027802895198, 125875027802895198⟩
def pH1479 : Prm := ⟨80, 38, 39, 1481, 11, 18446744073709551616, 125876127314522974, 125876127314522974⟩
def pI1479 : Prm := ⟨66, 33, 30, 1481, 11, 18446744073709551616, 125875027802895198, 125876127314522974⟩
noncomputable def L1479_cp1 : Nat × Nat := t7val% (fastRun pL1479 1 1045 (init pL1479) (init pL1479))
theorem L1479_seg1 : segOK pL1479 1 1045 (init pL1479) (init pL1479) L1479_cp1.1 L1479_cp1.2 = true := by
  decide +kernel
theorem L1479_fin : (prmOK pL1479 1479 && ptTest pL1479 (runFrom pL1479 (fmask pL1479) (cmask pL1479) (hmask pL1479) 1046 433 (true, L1479_cp1.1, L1479_cp1.2)) 1479 740 false) = true := by
  decide +kernel
theorem L1479_ok : RunOK pL1479 1479 (runFrom pL1479 (fmask pL1479) (cmask pL1479) (hmask pL1479) 1046 433 (true, L1479_cp1.1, L1479_cp1.2)) ∧ ptTest pL1479 (runFrom pL1479 (fmask pL1479) (cmask pL1479) (hmask pL1479) 1046 433 (true, L1479_cp1.1, L1479_cp1.2)) 1479 740 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1479_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1479_fin) true) L1479_seg1) (by decide) rfl L1479_fin ptTest_fst
noncomputable def H1479_cp1 : Nat × Nat := t7val% (fastRun pH1479 1 1045 (init pH1479) (init pH1479))
theorem H1479_seg1 : segOK pH1479 1 1045 (init pH1479) (init pH1479) H1479_cp1.1 H1479_cp1.2 = true := by
  decide +kernel
theorem H1479_fin : (prmOK pH1479 1479 && ptTest pH1479 (runFrom pH1479 (fmask pH1479) (cmask pH1479) (hmask pH1479) 1046 433 (true, H1479_cp1.1, H1479_cp1.2)) 1479 740 true) = true := by
  decide +kernel
theorem H1479_ok : RunOK pH1479 1479 (runFrom pH1479 (fmask pH1479) (cmask pH1479) (hmask pH1479) 1046 433 (true, H1479_cp1.1, H1479_cp1.2)) ∧ ptTest pH1479 (runFrom pH1479 (fmask pH1479) (cmask pH1479) (hmask pH1479) 1046 433 (true, H1479_cp1.1, H1479_cp1.2)) 1479 740 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1479_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1479_fin) true) H1479_seg1) (by decide) rfl H1479_fin ptTest_fst
noncomputable def I1479_cp1 : Nat × Nat := t7val% (fastRun pI1479 1 1045 (init pI1479) (init pI1479))
theorem I1479_seg1 : segOK pI1479 1 1045 (init pI1479) (init pI1479) I1479_cp1.1 I1479_cp1.2 = true := by
  decide +kernel
theorem I1479_fin : (prmOK pI1479 1479 && intTest pI1479 (runFrom pI1479 (fmask pI1479) (cmask pI1479) (hmask pI1479) 1046 433 (true, I1479_cp1.1, I1479_cp1.2)) 1479 20 false) = true := by
  decide +kernel
theorem I1479_ok : RunOK pI1479 1479 (runFrom pI1479 (fmask pI1479) (cmask pI1479) (hmask pI1479) 1046 433 (true, I1479_cp1.1, I1479_cp1.2)) ∧ intTest pI1479 (runFrom pI1479 (fmask pI1479) (cmask pI1479) (hmask pI1479) 1046 433 (true, I1479_cp1.1, I1479_cp1.2)) 1479 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1479_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1479_fin) true) I1479_seg1) (by decide) rfl I1479_fin intTest_fst
theorem link1479 : linkOK pL1479 pH1479 pI1479 = true := by decide +kernel
theorem cvx1479 : ConvexBetweenHumps 1479 :=
  cvx_of L1479_ok H1479_ok I1479_ok link1479 (by decide)

/-! ### `N = 1480` -/

def pL1480 : Prm := ⟨80, 38, 39, 1482, 11, 18446744073709551616, 125805879077461333, 125805879077461333⟩
def pH1480 : Prm := ⟨80, 38, 39, 1482, 11, 18446744073709551616, 125806978589089109, 125806978589089109⟩
def pI1480 : Prm := ⟨66, 33, 30, 1482, 11, 18446744073709551616, 125805879077461333, 125806978589089109⟩
noncomputable def L1480_cp1 : Nat × Nat := t7val% (fastRun pL1480 1 1046 (init pL1480) (init pL1480))
theorem L1480_seg1 : segOK pL1480 1 1046 (init pL1480) (init pL1480) L1480_cp1.1 L1480_cp1.2 = true := by
  decide +kernel
theorem L1480_fin : (prmOK pL1480 1480 && ptTest pL1480 (runFrom pL1480 (fmask pL1480) (cmask pL1480) (hmask pL1480) 1047 433 (true, L1480_cp1.1, L1480_cp1.2)) 1480 740 false) = true := by
  decide +kernel
theorem L1480_ok : RunOK pL1480 1480 (runFrom pL1480 (fmask pL1480) (cmask pL1480) (hmask pL1480) 1047 433 (true, L1480_cp1.1, L1480_cp1.2)) ∧ ptTest pL1480 (runFrom pL1480 (fmask pL1480) (cmask pL1480) (hmask pL1480) 1047 433 (true, L1480_cp1.1, L1480_cp1.2)) 1480 740 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1480_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1480_fin) true) L1480_seg1) (by decide) rfl L1480_fin ptTest_fst
noncomputable def H1480_cp1 : Nat × Nat := t7val% (fastRun pH1480 1 1046 (init pH1480) (init pH1480))
theorem H1480_seg1 : segOK pH1480 1 1046 (init pH1480) (init pH1480) H1480_cp1.1 H1480_cp1.2 = true := by
  decide +kernel
theorem H1480_fin : (prmOK pH1480 1480 && ptTest pH1480 (runFrom pH1480 (fmask pH1480) (cmask pH1480) (hmask pH1480) 1047 433 (true, H1480_cp1.1, H1480_cp1.2)) 1480 740 true) = true := by
  decide +kernel
theorem H1480_ok : RunOK pH1480 1480 (runFrom pH1480 (fmask pH1480) (cmask pH1480) (hmask pH1480) 1047 433 (true, H1480_cp1.1, H1480_cp1.2)) ∧ ptTest pH1480 (runFrom pH1480 (fmask pH1480) (cmask pH1480) (hmask pH1480) 1047 433 (true, H1480_cp1.1, H1480_cp1.2)) 1480 740 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1480_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1480_fin) true) H1480_seg1) (by decide) rfl H1480_fin ptTest_fst
noncomputable def I1480_cp1 : Nat × Nat := t7val% (fastRun pI1480 1 1046 (init pI1480) (init pI1480))
theorem I1480_seg1 : segOK pI1480 1 1046 (init pI1480) (init pI1480) I1480_cp1.1 I1480_cp1.2 = true := by
  decide +kernel
theorem I1480_fin : (prmOK pI1480 1480 && intTest pI1480 (runFrom pI1480 (fmask pI1480) (cmask pI1480) (hmask pI1480) 1047 433 (true, I1480_cp1.1, I1480_cp1.2)) 1480 20 true) = true := by
  decide +kernel
theorem I1480_ok : RunOK pI1480 1480 (runFrom pI1480 (fmask pI1480) (cmask pI1480) (hmask pI1480) 1047 433 (true, I1480_cp1.1, I1480_cp1.2)) ∧ intTest pI1480 (runFrom pI1480 (fmask pI1480) (cmask pI1480) (hmask pI1480) 1047 433 (true, I1480_cp1.1, I1480_cp1.2)) 1480 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1480_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1480_fin) true) I1480_seg1) (by decide) rfl I1480_fin intTest_fst
theorem link1480 : linkOK pL1480 pH1480 pI1480 = true := by decide +kernel
theorem cvx1480 : ConvexBetweenHumps 1480 :=
  cvx_of L1480_ok H1480_ok I1480_ok link1480 (by decide)
theorem cenlink1480 : cenLinkOK pI1480 1480 = true := by decide +kernel
theorem cen1480 : CenterUniqueMin 1480 ∧ DipHyp 1480 ∧ OnePointHyps 1480 :=
  cen_of L1480_ok H1480_ok I1480_ok link1480 cenlink1480

/-! ### `N = 1481` -/

def pL1481 : Prm := ⟨80, 38, 39, 1483, 11, 18446744073709551616, 125736778081040851, 125736778081040851⟩
def pH1481 : Prm := ⟨80, 38, 39, 1483, 11, 18446744073709551616, 125737877592668627, 125737877592668627⟩
def pI1481 : Prm := ⟨66, 33, 30, 1483, 11, 18446744073709551616, 125736778081040851, 125737877592668627⟩
noncomputable def L1481_cp1 : Nat × Nat := t7val% (fastRun pL1481 1 1046 (init pL1481) (init pL1481))
theorem L1481_seg1 : segOK pL1481 1 1046 (init pL1481) (init pL1481) L1481_cp1.1 L1481_cp1.2 = true := by
  decide +kernel
theorem L1481_fin : (prmOK pL1481 1481 && ptTest pL1481 (runFrom pL1481 (fmask pL1481) (cmask pL1481) (hmask pL1481) 1047 434 (true, L1481_cp1.1, L1481_cp1.2)) 1481 741 false) = true := by
  decide +kernel
theorem L1481_ok : RunOK pL1481 1481 (runFrom pL1481 (fmask pL1481) (cmask pL1481) (hmask pL1481) 1047 434 (true, L1481_cp1.1, L1481_cp1.2)) ∧ ptTest pL1481 (runFrom pL1481 (fmask pL1481) (cmask pL1481) (hmask pL1481) 1047 434 (true, L1481_cp1.1, L1481_cp1.2)) 1481 741 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1481_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1481_fin) true) L1481_seg1) (by decide) rfl L1481_fin ptTest_fst
noncomputable def H1481_cp1 : Nat × Nat := t7val% (fastRun pH1481 1 1046 (init pH1481) (init pH1481))
theorem H1481_seg1 : segOK pH1481 1 1046 (init pH1481) (init pH1481) H1481_cp1.1 H1481_cp1.2 = true := by
  decide +kernel
theorem H1481_fin : (prmOK pH1481 1481 && ptTest pH1481 (runFrom pH1481 (fmask pH1481) (cmask pH1481) (hmask pH1481) 1047 434 (true, H1481_cp1.1, H1481_cp1.2)) 1481 741 true) = true := by
  decide +kernel
theorem H1481_ok : RunOK pH1481 1481 (runFrom pH1481 (fmask pH1481) (cmask pH1481) (hmask pH1481) 1047 434 (true, H1481_cp1.1, H1481_cp1.2)) ∧ ptTest pH1481 (runFrom pH1481 (fmask pH1481) (cmask pH1481) (hmask pH1481) 1047 434 (true, H1481_cp1.1, H1481_cp1.2)) 1481 741 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1481_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1481_fin) true) H1481_seg1) (by decide) rfl H1481_fin ptTest_fst
noncomputable def I1481_cp1 : Nat × Nat := t7val% (fastRun pI1481 1 1046 (init pI1481) (init pI1481))
theorem I1481_seg1 : segOK pI1481 1 1046 (init pI1481) (init pI1481) I1481_cp1.1 I1481_cp1.2 = true := by
  decide +kernel
theorem I1481_fin : (prmOK pI1481 1481 && intTest pI1481 (runFrom pI1481 (fmask pI1481) (cmask pI1481) (hmask pI1481) 1047 434 (true, I1481_cp1.1, I1481_cp1.2)) 1481 20 false) = true := by
  decide +kernel
theorem I1481_ok : RunOK pI1481 1481 (runFrom pI1481 (fmask pI1481) (cmask pI1481) (hmask pI1481) 1047 434 (true, I1481_cp1.1, I1481_cp1.2)) ∧ intTest pI1481 (runFrom pI1481 (fmask pI1481) (cmask pI1481) (hmask pI1481) 1047 434 (true, I1481_cp1.1, I1481_cp1.2)) 1481 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1481_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1481_fin) true) I1481_seg1) (by decide) rfl I1481_fin intTest_fst
theorem link1481 : linkOK pL1481 pH1481 pI1481 = true := by decide +kernel
theorem cvx1481 : ConvexBetweenHumps 1481 :=
  cvx_of L1481_ok H1481_ok I1481_ok link1481 (by decide)

/-! ### `N = 1482` -/

def pL1482 : Prm := ⟨80, 38, 39, 1484, 11, 18446744073709551616, 125667794471878234, 125667794471878234⟩
def pH1482 : Prm := ⟨80, 38, 39, 1484, 11, 18446744073709551616, 125668893983506010, 125668893983506010⟩
def pI1482 : Prm := ⟨66, 33, 30, 1484, 11, 18446744073709551616, 125667794471878234, 125668893983506010⟩
noncomputable def L1482_cp1 : Nat × Nat := t7val% (fastRun pL1482 1 1047 (init pL1482) (init pL1482))
theorem L1482_seg1 : segOK pL1482 1 1047 (init pL1482) (init pL1482) L1482_cp1.1 L1482_cp1.2 = true := by
  decide +kernel
theorem L1482_fin : (prmOK pL1482 1482 && ptTest pL1482 (runFrom pL1482 (fmask pL1482) (cmask pL1482) (hmask pL1482) 1048 434 (true, L1482_cp1.1, L1482_cp1.2)) 1482 741 false) = true := by
  decide +kernel
theorem L1482_ok : RunOK pL1482 1482 (runFrom pL1482 (fmask pL1482) (cmask pL1482) (hmask pL1482) 1048 434 (true, L1482_cp1.1, L1482_cp1.2)) ∧ ptTest pL1482 (runFrom pL1482 (fmask pL1482) (cmask pL1482) (hmask pL1482) 1048 434 (true, L1482_cp1.1, L1482_cp1.2)) 1482 741 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1482_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1482_fin) true) L1482_seg1) (by decide) rfl L1482_fin ptTest_fst
noncomputable def H1482_cp1 : Nat × Nat := t7val% (fastRun pH1482 1 1047 (init pH1482) (init pH1482))
theorem H1482_seg1 : segOK pH1482 1 1047 (init pH1482) (init pH1482) H1482_cp1.1 H1482_cp1.2 = true := by
  decide +kernel
theorem H1482_fin : (prmOK pH1482 1482 && ptTest pH1482 (runFrom pH1482 (fmask pH1482) (cmask pH1482) (hmask pH1482) 1048 434 (true, H1482_cp1.1, H1482_cp1.2)) 1482 741 true) = true := by
  decide +kernel
theorem H1482_ok : RunOK pH1482 1482 (runFrom pH1482 (fmask pH1482) (cmask pH1482) (hmask pH1482) 1048 434 (true, H1482_cp1.1, H1482_cp1.2)) ∧ ptTest pH1482 (runFrom pH1482 (fmask pH1482) (cmask pH1482) (hmask pH1482) 1048 434 (true, H1482_cp1.1, H1482_cp1.2)) 1482 741 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1482_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1482_fin) true) H1482_seg1) (by decide) rfl H1482_fin ptTest_fst
noncomputable def I1482_cp1 : Nat × Nat := t7val% (fastRun pI1482 1 1047 (init pI1482) (init pI1482))
theorem I1482_seg1 : segOK pI1482 1 1047 (init pI1482) (init pI1482) I1482_cp1.1 I1482_cp1.2 = true := by
  decide +kernel
theorem I1482_fin : (prmOK pI1482 1482 && intTest pI1482 (runFrom pI1482 (fmask pI1482) (cmask pI1482) (hmask pI1482) 1048 434 (true, I1482_cp1.1, I1482_cp1.2)) 1482 20 true) = true := by
  decide +kernel
theorem I1482_ok : RunOK pI1482 1482 (runFrom pI1482 (fmask pI1482) (cmask pI1482) (hmask pI1482) 1048 434 (true, I1482_cp1.1, I1482_cp1.2)) ∧ intTest pI1482 (runFrom pI1482 (fmask pI1482) (cmask pI1482) (hmask pI1482) 1048 434 (true, I1482_cp1.1, I1482_cp1.2)) 1482 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1482_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1482_fin) true) I1482_seg1) (by decide) rfl I1482_fin intTest_fst
theorem link1482 : linkOK pL1482 pH1482 pI1482 = true := by decide +kernel
theorem cvx1482 : ConvexBetweenHumps 1482 :=
  cvx_of L1482_ok H1482_ok I1482_ok link1482 (by decide)
theorem cenlink1482 : cenLinkOK pI1482 1482 = true := by decide +kernel
theorem cen1482 : CenterUniqueMin 1482 ∧ DipHyp 1482 ∧ OnePointHyps 1482 :=
  cen_of L1482_ok H1482_ok I1482_ok link1482 cenlink1482

/-! ### `N = 1483` -/

def pL1483 : Prm := ⟨80, 38, 39, 1485, 11, 18446744073709551616, 125598858429932608, 125598858429932608⟩
def pH1483 : Prm := ⟨80, 38, 39, 1485, 11, 18446744073709551616, 125599957941560384, 125599957941560384⟩
def pI1483 : Prm := ⟨66, 33, 30, 1485, 11, 18446744073709551616, 125598858429932608, 125599957941560384⟩
noncomputable def L1483_cp1 : Nat × Nat := t7val% (fastRun pL1483 1 1048 (init pL1483) (init pL1483))
theorem L1483_seg1 : segOK pL1483 1 1048 (init pL1483) (init pL1483) L1483_cp1.1 L1483_cp1.2 = true := by
  decide +kernel
theorem L1483_fin : (prmOK pL1483 1483 && ptTest pL1483 (runFrom pL1483 (fmask pL1483) (cmask pL1483) (hmask pL1483) 1049 434 (true, L1483_cp1.1, L1483_cp1.2)) 1483 742 false) = true := by
  decide +kernel
theorem L1483_ok : RunOK pL1483 1483 (runFrom pL1483 (fmask pL1483) (cmask pL1483) (hmask pL1483) 1049 434 (true, L1483_cp1.1, L1483_cp1.2)) ∧ ptTest pL1483 (runFrom pL1483 (fmask pL1483) (cmask pL1483) (hmask pL1483) 1049 434 (true, L1483_cp1.1, L1483_cp1.2)) 1483 742 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1483_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1483_fin) true) L1483_seg1) (by decide) rfl L1483_fin ptTest_fst
noncomputable def H1483_cp1 : Nat × Nat := t7val% (fastRun pH1483 1 1048 (init pH1483) (init pH1483))
theorem H1483_seg1 : segOK pH1483 1 1048 (init pH1483) (init pH1483) H1483_cp1.1 H1483_cp1.2 = true := by
  decide +kernel
theorem H1483_fin : (prmOK pH1483 1483 && ptTest pH1483 (runFrom pH1483 (fmask pH1483) (cmask pH1483) (hmask pH1483) 1049 434 (true, H1483_cp1.1, H1483_cp1.2)) 1483 742 true) = true := by
  decide +kernel
theorem H1483_ok : RunOK pH1483 1483 (runFrom pH1483 (fmask pH1483) (cmask pH1483) (hmask pH1483) 1049 434 (true, H1483_cp1.1, H1483_cp1.2)) ∧ ptTest pH1483 (runFrom pH1483 (fmask pH1483) (cmask pH1483) (hmask pH1483) 1049 434 (true, H1483_cp1.1, H1483_cp1.2)) 1483 742 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1483_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1483_fin) true) H1483_seg1) (by decide) rfl H1483_fin ptTest_fst
noncomputable def I1483_cp1 : Nat × Nat := t7val% (fastRun pI1483 1 1048 (init pI1483) (init pI1483))
theorem I1483_seg1 : segOK pI1483 1 1048 (init pI1483) (init pI1483) I1483_cp1.1 I1483_cp1.2 = true := by
  decide +kernel
theorem I1483_fin : (prmOK pI1483 1483 && intTest pI1483 (runFrom pI1483 (fmask pI1483) (cmask pI1483) (hmask pI1483) 1049 434 (true, I1483_cp1.1, I1483_cp1.2)) 1483 20 false) = true := by
  decide +kernel
theorem I1483_ok : RunOK pI1483 1483 (runFrom pI1483 (fmask pI1483) (cmask pI1483) (hmask pI1483) 1049 434 (true, I1483_cp1.1, I1483_cp1.2)) ∧ intTest pI1483 (runFrom pI1483 (fmask pI1483) (cmask pI1483) (hmask pI1483) 1049 434 (true, I1483_cp1.1, I1483_cp1.2)) 1483 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1483_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1483_fin) true) I1483_seg1) (by decide) rfl I1483_fin intTest_fst
theorem link1483 : linkOK pL1483 pH1483 pI1483 = true := by decide +kernel
theorem cvx1483 : ConvexBetweenHumps 1483 :=
  cvx_of L1483_ok H1483_ok I1483_ok link1483 (by decide)

/-! ### `N = 1484` -/

def pL1484 : Prm := ⟨80, 38, 39, 1486, 11, 18446744073709551616, 125530039327487028, 125530039327487028⟩
def pH1484 : Prm := ⟨80, 38, 39, 1486, 11, 18446744073709551616, 125531138839114804, 125531138839114804⟩
def pI1484 : Prm := ⟨66, 33, 30, 1486, 11, 18446744073709551616, 125530039327487028, 125531138839114804⟩
noncomputable def L1484_cp1 : Nat × Nat := t7val% (fastRun pL1484 1 1048 (init pL1484) (init pL1484))
theorem L1484_seg1 : segOK pL1484 1 1048 (init pL1484) (init pL1484) L1484_cp1.1 L1484_cp1.2 = true := by
  decide +kernel
theorem L1484_fin : (prmOK pL1484 1484 && ptTest pL1484 (runFrom pL1484 (fmask pL1484) (cmask pL1484) (hmask pL1484) 1049 435 (true, L1484_cp1.1, L1484_cp1.2)) 1484 742 false) = true := by
  decide +kernel
theorem L1484_ok : RunOK pL1484 1484 (runFrom pL1484 (fmask pL1484) (cmask pL1484) (hmask pL1484) 1049 435 (true, L1484_cp1.1, L1484_cp1.2)) ∧ ptTest pL1484 (runFrom pL1484 (fmask pL1484) (cmask pL1484) (hmask pL1484) 1049 435 (true, L1484_cp1.1, L1484_cp1.2)) 1484 742 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1484_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1484_fin) true) L1484_seg1) (by decide) rfl L1484_fin ptTest_fst
noncomputable def H1484_cp1 : Nat × Nat := t7val% (fastRun pH1484 1 1048 (init pH1484) (init pH1484))
theorem H1484_seg1 : segOK pH1484 1 1048 (init pH1484) (init pH1484) H1484_cp1.1 H1484_cp1.2 = true := by
  decide +kernel
theorem H1484_fin : (prmOK pH1484 1484 && ptTest pH1484 (runFrom pH1484 (fmask pH1484) (cmask pH1484) (hmask pH1484) 1049 435 (true, H1484_cp1.1, H1484_cp1.2)) 1484 742 true) = true := by
  decide +kernel
theorem H1484_ok : RunOK pH1484 1484 (runFrom pH1484 (fmask pH1484) (cmask pH1484) (hmask pH1484) 1049 435 (true, H1484_cp1.1, H1484_cp1.2)) ∧ ptTest pH1484 (runFrom pH1484 (fmask pH1484) (cmask pH1484) (hmask pH1484) 1049 435 (true, H1484_cp1.1, H1484_cp1.2)) 1484 742 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1484_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1484_fin) true) H1484_seg1) (by decide) rfl H1484_fin ptTest_fst
noncomputable def I1484_cp1 : Nat × Nat := t7val% (fastRun pI1484 1 1048 (init pI1484) (init pI1484))
theorem I1484_seg1 : segOK pI1484 1 1048 (init pI1484) (init pI1484) I1484_cp1.1 I1484_cp1.2 = true := by
  decide +kernel
theorem I1484_fin : (prmOK pI1484 1484 && intTest pI1484 (runFrom pI1484 (fmask pI1484) (cmask pI1484) (hmask pI1484) 1049 435 (true, I1484_cp1.1, I1484_cp1.2)) 1484 20 true) = true := by
  decide +kernel
theorem I1484_ok : RunOK pI1484 1484 (runFrom pI1484 (fmask pI1484) (cmask pI1484) (hmask pI1484) 1049 435 (true, I1484_cp1.1, I1484_cp1.2)) ∧ intTest pI1484 (runFrom pI1484 (fmask pI1484) (cmask pI1484) (hmask pI1484) 1049 435 (true, I1484_cp1.1, I1484_cp1.2)) 1484 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1484_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1484_fin) true) I1484_seg1) (by decide) rfl I1484_fin intTest_fst
theorem link1484 : linkOK pL1484 pH1484 pI1484 = true := by decide +kernel
theorem cvx1484 : ConvexBetweenHumps 1484 :=
  cvx_of L1484_ok H1484_ok I1484_ok link1484 (by decide)
theorem cenlink1484 : cenLinkOK pI1484 1484 = true := by decide +kernel
theorem cen1484 : CenterUniqueMin 1484 ∧ DipHyp 1484 ∧ OnePointHyps 1484 :=
  cen_of L1484_ok H1484_ok I1484_ok link1484 cenlink1484

/-! ### `N = 1485` -/

def pL1485 : Prm := ⟨80, 38, 39, 1487, 11, 18446744073709551616, 125461267631199916, 125461267631199916⟩
def pH1485 : Prm := ⟨80, 38, 39, 1487, 11, 18446744073709551616, 125462367142827692, 125462367142827692⟩
def pI1485 : Prm := ⟨66, 33, 30, 1487, 11, 18446744073709551616, 125461267631199916, 125462367142827692⟩
noncomputable def L1485_cp1 : Nat × Nat := t7val% (fastRun pL1485 1 1049 (init pL1485) (init pL1485))
theorem L1485_seg1 : segOK pL1485 1 1049 (init pL1485) (init pL1485) L1485_cp1.1 L1485_cp1.2 = true := by
  decide +kernel
theorem L1485_fin : (prmOK pL1485 1485 && ptTest pL1485 (runFrom pL1485 (fmask pL1485) (cmask pL1485) (hmask pL1485) 1050 435 (true, L1485_cp1.1, L1485_cp1.2)) 1485 743 false) = true := by
  decide +kernel
theorem L1485_ok : RunOK pL1485 1485 (runFrom pL1485 (fmask pL1485) (cmask pL1485) (hmask pL1485) 1050 435 (true, L1485_cp1.1, L1485_cp1.2)) ∧ ptTest pL1485 (runFrom pL1485 (fmask pL1485) (cmask pL1485) (hmask pL1485) 1050 435 (true, L1485_cp1.1, L1485_cp1.2)) 1485 743 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1485_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1485_fin) true) L1485_seg1) (by decide) rfl L1485_fin ptTest_fst
noncomputable def H1485_cp1 : Nat × Nat := t7val% (fastRun pH1485 1 1049 (init pH1485) (init pH1485))
theorem H1485_seg1 : segOK pH1485 1 1049 (init pH1485) (init pH1485) H1485_cp1.1 H1485_cp1.2 = true := by
  decide +kernel
theorem H1485_fin : (prmOK pH1485 1485 && ptTest pH1485 (runFrom pH1485 (fmask pH1485) (cmask pH1485) (hmask pH1485) 1050 435 (true, H1485_cp1.1, H1485_cp1.2)) 1485 743 true) = true := by
  decide +kernel
theorem H1485_ok : RunOK pH1485 1485 (runFrom pH1485 (fmask pH1485) (cmask pH1485) (hmask pH1485) 1050 435 (true, H1485_cp1.1, H1485_cp1.2)) ∧ ptTest pH1485 (runFrom pH1485 (fmask pH1485) (cmask pH1485) (hmask pH1485) 1050 435 (true, H1485_cp1.1, H1485_cp1.2)) 1485 743 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1485_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1485_fin) true) H1485_seg1) (by decide) rfl H1485_fin ptTest_fst
noncomputable def I1485_cp1 : Nat × Nat := t7val% (fastRun pI1485 1 1049 (init pI1485) (init pI1485))
theorem I1485_seg1 : segOK pI1485 1 1049 (init pI1485) (init pI1485) I1485_cp1.1 I1485_cp1.2 = true := by
  decide +kernel
theorem I1485_fin : (prmOK pI1485 1485 && intTest pI1485 (runFrom pI1485 (fmask pI1485) (cmask pI1485) (hmask pI1485) 1050 435 (true, I1485_cp1.1, I1485_cp1.2)) 1485 20 false) = true := by
  decide +kernel
theorem I1485_ok : RunOK pI1485 1485 (runFrom pI1485 (fmask pI1485) (cmask pI1485) (hmask pI1485) 1050 435 (true, I1485_cp1.1, I1485_cp1.2)) ∧ intTest pI1485 (runFrom pI1485 (fmask pI1485) (cmask pI1485) (hmask pI1485) 1050 435 (true, I1485_cp1.1, I1485_cp1.2)) 1485 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1485_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1485_fin) true) I1485_seg1) (by decide) rfl I1485_fin intTest_fst
theorem link1485 : linkOK pL1485 pH1485 pI1485 = true := by decide +kernel
theorem cvx1485 : ConvexBetweenHumps 1485 :=
  cvx_of L1485_ok H1485_ok I1485_ok link1485 (by decide)

/-! ### `N = 1486` -/

def pL1486 : Prm := ⟨80, 38, 39, 1488, 11, 18446744073709551616, 125392612428942428, 125392612428942428⟩
def pH1486 : Prm := ⟨80, 38, 39, 1488, 11, 18446744073709551616, 125393711940570204, 125393711940570204⟩
def pI1486 : Prm := ⟨66, 33, 30, 1488, 11, 18446744073709551616, 125392612428942428, 125393711940570204⟩
noncomputable def L1486_cp1 : Nat × Nat := t7val% (fastRun pL1486 1 1050 (init pL1486) (init pL1486))
theorem L1486_seg1 : segOK pL1486 1 1050 (init pL1486) (init pL1486) L1486_cp1.1 L1486_cp1.2 = true := by
  decide +kernel
theorem L1486_fin : (prmOK pL1486 1486 && ptTest pL1486 (runFrom pL1486 (fmask pL1486) (cmask pL1486) (hmask pL1486) 1051 435 (true, L1486_cp1.1, L1486_cp1.2)) 1486 743 false) = true := by
  decide +kernel
theorem L1486_ok : RunOK pL1486 1486 (runFrom pL1486 (fmask pL1486) (cmask pL1486) (hmask pL1486) 1051 435 (true, L1486_cp1.1, L1486_cp1.2)) ∧ ptTest pL1486 (runFrom pL1486 (fmask pL1486) (cmask pL1486) (hmask pL1486) 1051 435 (true, L1486_cp1.1, L1486_cp1.2)) 1486 743 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1486_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1486_fin) true) L1486_seg1) (by decide) rfl L1486_fin ptTest_fst
noncomputable def H1486_cp1 : Nat × Nat := t7val% (fastRun pH1486 1 1050 (init pH1486) (init pH1486))
theorem H1486_seg1 : segOK pH1486 1 1050 (init pH1486) (init pH1486) H1486_cp1.1 H1486_cp1.2 = true := by
  decide +kernel
theorem H1486_fin : (prmOK pH1486 1486 && ptTest pH1486 (runFrom pH1486 (fmask pH1486) (cmask pH1486) (hmask pH1486) 1051 435 (true, H1486_cp1.1, H1486_cp1.2)) 1486 743 true) = true := by
  decide +kernel
theorem H1486_ok : RunOK pH1486 1486 (runFrom pH1486 (fmask pH1486) (cmask pH1486) (hmask pH1486) 1051 435 (true, H1486_cp1.1, H1486_cp1.2)) ∧ ptTest pH1486 (runFrom pH1486 (fmask pH1486) (cmask pH1486) (hmask pH1486) 1051 435 (true, H1486_cp1.1, H1486_cp1.2)) 1486 743 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1486_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1486_fin) true) H1486_seg1) (by decide) rfl H1486_fin ptTest_fst
noncomputable def I1486_cp1 : Nat × Nat := t7val% (fastRun pI1486 1 1050 (init pI1486) (init pI1486))
theorem I1486_seg1 : segOK pI1486 1 1050 (init pI1486) (init pI1486) I1486_cp1.1 I1486_cp1.2 = true := by
  decide +kernel
theorem I1486_fin : (prmOK pI1486 1486 && intTest pI1486 (runFrom pI1486 (fmask pI1486) (cmask pI1486) (hmask pI1486) 1051 435 (true, I1486_cp1.1, I1486_cp1.2)) 1486 20 true) = true := by
  decide +kernel
theorem I1486_ok : RunOK pI1486 1486 (runFrom pI1486 (fmask pI1486) (cmask pI1486) (hmask pI1486) 1051 435 (true, I1486_cp1.1, I1486_cp1.2)) ∧ intTest pI1486 (runFrom pI1486 (fmask pI1486) (cmask pI1486) (hmask pI1486) 1051 435 (true, I1486_cp1.1, I1486_cp1.2)) 1486 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1486_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1486_fin) true) I1486_seg1) (by decide) rfl I1486_fin intTest_fst
theorem link1486 : linkOK pL1486 pH1486 pI1486 = true := by decide +kernel
theorem cvx1486 : ConvexBetweenHumps 1486 :=
  cvx_of L1486_ok H1486_ok I1486_ok link1486 (by decide)
theorem cenlink1486 : cenLinkOK pI1486 1486 = true := by decide +kernel
theorem cen1486 : CenterUniqueMin 1486 ∧ DipHyp 1486 ∧ OnePointHyps 1486 :=
  cen_of L1486_ok H1486_ok I1486_ok link1486 cenlink1486

/-! ### `N = 1487` -/

def pL1487 : Prm := ⟨80, 38, 39, 1489, 11, 18446744073709551616, 125324004472541203, 125324004472541203⟩
def pH1487 : Prm := ⟨80, 38, 39, 1489, 11, 18446744073709551616, 125325103984168979, 125325103984168979⟩
def pI1487 : Prm := ⟨66, 33, 30, 1489, 11, 18446744073709551616, 125324004472541203, 125325103984168979⟩
noncomputable def L1487_cp1 : Nat × Nat := t7val% (fastRun pL1487 1 1050 (init pL1487) (init pL1487))
theorem L1487_seg1 : segOK pL1487 1 1050 (init pL1487) (init pL1487) L1487_cp1.1 L1487_cp1.2 = true := by
  decide +kernel
theorem L1487_fin : (prmOK pL1487 1487 && ptTest pL1487 (runFrom pL1487 (fmask pL1487) (cmask pL1487) (hmask pL1487) 1051 436 (true, L1487_cp1.1, L1487_cp1.2)) 1487 744 false) = true := by
  decide +kernel
theorem L1487_ok : RunOK pL1487 1487 (runFrom pL1487 (fmask pL1487) (cmask pL1487) (hmask pL1487) 1051 436 (true, L1487_cp1.1, L1487_cp1.2)) ∧ ptTest pL1487 (runFrom pL1487 (fmask pL1487) (cmask pL1487) (hmask pL1487) 1051 436 (true, L1487_cp1.1, L1487_cp1.2)) 1487 744 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1487_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1487_fin) true) L1487_seg1) (by decide) rfl L1487_fin ptTest_fst
noncomputable def H1487_cp1 : Nat × Nat := t7val% (fastRun pH1487 1 1050 (init pH1487) (init pH1487))
theorem H1487_seg1 : segOK pH1487 1 1050 (init pH1487) (init pH1487) H1487_cp1.1 H1487_cp1.2 = true := by
  decide +kernel
theorem H1487_fin : (prmOK pH1487 1487 && ptTest pH1487 (runFrom pH1487 (fmask pH1487) (cmask pH1487) (hmask pH1487) 1051 436 (true, H1487_cp1.1, H1487_cp1.2)) 1487 744 true) = true := by
  decide +kernel
theorem H1487_ok : RunOK pH1487 1487 (runFrom pH1487 (fmask pH1487) (cmask pH1487) (hmask pH1487) 1051 436 (true, H1487_cp1.1, H1487_cp1.2)) ∧ ptTest pH1487 (runFrom pH1487 (fmask pH1487) (cmask pH1487) (hmask pH1487) 1051 436 (true, H1487_cp1.1, H1487_cp1.2)) 1487 744 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1487_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1487_fin) true) H1487_seg1) (by decide) rfl H1487_fin ptTest_fst
noncomputable def I1487_cp1 : Nat × Nat := t7val% (fastRun pI1487 1 1050 (init pI1487) (init pI1487))
theorem I1487_seg1 : segOK pI1487 1 1050 (init pI1487) (init pI1487) I1487_cp1.1 I1487_cp1.2 = true := by
  decide +kernel
theorem I1487_fin : (prmOK pI1487 1487 && intTest pI1487 (runFrom pI1487 (fmask pI1487) (cmask pI1487) (hmask pI1487) 1051 436 (true, I1487_cp1.1, I1487_cp1.2)) 1487 20 false) = true := by
  decide +kernel
theorem I1487_ok : RunOK pI1487 1487 (runFrom pI1487 (fmask pI1487) (cmask pI1487) (hmask pI1487) 1051 436 (true, I1487_cp1.1, I1487_cp1.2)) ∧ intTest pI1487 (runFrom pI1487 (fmask pI1487) (cmask pI1487) (hmask pI1487) 1051 436 (true, I1487_cp1.1, I1487_cp1.2)) 1487 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1487_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1487_fin) true) I1487_seg1) (by decide) rfl I1487_fin intTest_fst
theorem link1487 : linkOK pL1487 pH1487 pI1487 = true := by decide +kernel
theorem cvx1487 : ConvexBetweenHumps 1487 :=
  cvx_of L1487_ok H1487_ok I1487_ok link1487 (by decide)

/-! ### `N = 1488` -/

def pL1488 : Prm := ⟨80, 38, 39, 1490, 11, 18446744073709551616, 125255512566968127, 125255512566968127⟩
def pH1488 : Prm := ⟨80, 38, 39, 1490, 11, 18446744073709551616, 125256612078595903, 125256612078595903⟩
def pI1488 : Prm := ⟨66, 33, 30, 1490, 11, 18446744073709551616, 125255512566968127, 125256612078595903⟩
noncomputable def L1488_cp1 : Nat × Nat := t7val% (fastRun pL1488 1 1051 (init pL1488) (init pL1488))
theorem L1488_seg1 : segOK pL1488 1 1051 (init pL1488) (init pL1488) L1488_cp1.1 L1488_cp1.2 = true := by
  decide +kernel
theorem L1488_fin : (prmOK pL1488 1488 && ptTest pL1488 (runFrom pL1488 (fmask pL1488) (cmask pL1488) (hmask pL1488) 1052 436 (true, L1488_cp1.1, L1488_cp1.2)) 1488 744 false) = true := by
  decide +kernel
theorem L1488_ok : RunOK pL1488 1488 (runFrom pL1488 (fmask pL1488) (cmask pL1488) (hmask pL1488) 1052 436 (true, L1488_cp1.1, L1488_cp1.2)) ∧ ptTest pL1488 (runFrom pL1488 (fmask pL1488) (cmask pL1488) (hmask pL1488) 1052 436 (true, L1488_cp1.1, L1488_cp1.2)) 1488 744 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1488_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1488_fin) true) L1488_seg1) (by decide) rfl L1488_fin ptTest_fst
noncomputable def H1488_cp1 : Nat × Nat := t7val% (fastRun pH1488 1 1051 (init pH1488) (init pH1488))
theorem H1488_seg1 : segOK pH1488 1 1051 (init pH1488) (init pH1488) H1488_cp1.1 H1488_cp1.2 = true := by
  decide +kernel
theorem H1488_fin : (prmOK pH1488 1488 && ptTest pH1488 (runFrom pH1488 (fmask pH1488) (cmask pH1488) (hmask pH1488) 1052 436 (true, H1488_cp1.1, H1488_cp1.2)) 1488 744 true) = true := by
  decide +kernel
theorem H1488_ok : RunOK pH1488 1488 (runFrom pH1488 (fmask pH1488) (cmask pH1488) (hmask pH1488) 1052 436 (true, H1488_cp1.1, H1488_cp1.2)) ∧ ptTest pH1488 (runFrom pH1488 (fmask pH1488) (cmask pH1488) (hmask pH1488) 1052 436 (true, H1488_cp1.1, H1488_cp1.2)) 1488 744 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1488_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1488_fin) true) H1488_seg1) (by decide) rfl H1488_fin ptTest_fst
noncomputable def I1488_cp1 : Nat × Nat := t7val% (fastRun pI1488 1 1051 (init pI1488) (init pI1488))
theorem I1488_seg1 : segOK pI1488 1 1051 (init pI1488) (init pI1488) I1488_cp1.1 I1488_cp1.2 = true := by
  decide +kernel
theorem I1488_fin : (prmOK pI1488 1488 && intTest pI1488 (runFrom pI1488 (fmask pI1488) (cmask pI1488) (hmask pI1488) 1052 436 (true, I1488_cp1.1, I1488_cp1.2)) 1488 20 true) = true := by
  decide +kernel
theorem I1488_ok : RunOK pI1488 1488 (runFrom pI1488 (fmask pI1488) (cmask pI1488) (hmask pI1488) 1052 436 (true, I1488_cp1.1, I1488_cp1.2)) ∧ intTest pI1488 (runFrom pI1488 (fmask pI1488) (cmask pI1488) (hmask pI1488) 1052 436 (true, I1488_cp1.1, I1488_cp1.2)) 1488 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1488_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1488_fin) true) I1488_seg1) (by decide) rfl I1488_fin intTest_fst
theorem link1488 : linkOK pL1488 pH1488 pI1488 = true := by decide +kernel
theorem cvx1488 : ConvexBetweenHumps 1488 :=
  cvx_of L1488_ok H1488_ok I1488_ok link1488 (by decide)
theorem cenlink1488 : cenLinkOK pI1488 1488 = true := by decide +kernel
theorem cen1488 : CenterUniqueMin 1488 ∧ DipHyp 1488 ∧ OnePointHyps 1488 :=
  cen_of L1488_ok H1488_ok I1488_ok link1488 cenlink1488

/-! ### `N = 1489` -/

def pL1489 : Prm := ⟨80, 38, 39, 1491, 11, 18446744073709551616, 125187067747668531, 125187067747668531⟩
def pH1489 : Prm := ⟨80, 38, 39, 1491, 11, 18446744073709551616, 125188167259296307, 125188167259296307⟩
def pI1489 : Prm := ⟨66, 33, 30, 1491, 11, 18446744073709551616, 125187067747668531, 125188167259296307⟩
noncomputable def L1489_cp1 : Nat × Nat := t7val% (fastRun pL1489 1 1052 (init pL1489) (init pL1489))
theorem L1489_seg1 : segOK pL1489 1 1052 (init pL1489) (init pL1489) L1489_cp1.1 L1489_cp1.2 = true := by
  decide +kernel
theorem L1489_fin : (prmOK pL1489 1489 && ptTest pL1489 (runFrom pL1489 (fmask pL1489) (cmask pL1489) (hmask pL1489) 1053 436 (true, L1489_cp1.1, L1489_cp1.2)) 1489 745 false) = true := by
  decide +kernel
theorem L1489_ok : RunOK pL1489 1489 (runFrom pL1489 (fmask pL1489) (cmask pL1489) (hmask pL1489) 1053 436 (true, L1489_cp1.1, L1489_cp1.2)) ∧ ptTest pL1489 (runFrom pL1489 (fmask pL1489) (cmask pL1489) (hmask pL1489) 1053 436 (true, L1489_cp1.1, L1489_cp1.2)) 1489 745 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1489_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1489_fin) true) L1489_seg1) (by decide) rfl L1489_fin ptTest_fst
noncomputable def H1489_cp1 : Nat × Nat := t7val% (fastRun pH1489 1 1052 (init pH1489) (init pH1489))
theorem H1489_seg1 : segOK pH1489 1 1052 (init pH1489) (init pH1489) H1489_cp1.1 H1489_cp1.2 = true := by
  decide +kernel
theorem H1489_fin : (prmOK pH1489 1489 && ptTest pH1489 (runFrom pH1489 (fmask pH1489) (cmask pH1489) (hmask pH1489) 1053 436 (true, H1489_cp1.1, H1489_cp1.2)) 1489 745 true) = true := by
  decide +kernel
theorem H1489_ok : RunOK pH1489 1489 (runFrom pH1489 (fmask pH1489) (cmask pH1489) (hmask pH1489) 1053 436 (true, H1489_cp1.1, H1489_cp1.2)) ∧ ptTest pH1489 (runFrom pH1489 (fmask pH1489) (cmask pH1489) (hmask pH1489) 1053 436 (true, H1489_cp1.1, H1489_cp1.2)) 1489 745 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1489_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1489_fin) true) H1489_seg1) (by decide) rfl H1489_fin ptTest_fst
noncomputable def I1489_cp1 : Nat × Nat := t7val% (fastRun pI1489 1 1052 (init pI1489) (init pI1489))
theorem I1489_seg1 : segOK pI1489 1 1052 (init pI1489) (init pI1489) I1489_cp1.1 I1489_cp1.2 = true := by
  decide +kernel
theorem I1489_fin : (prmOK pI1489 1489 && intTest pI1489 (runFrom pI1489 (fmask pI1489) (cmask pI1489) (hmask pI1489) 1053 436 (true, I1489_cp1.1, I1489_cp1.2)) 1489 20 false) = true := by
  decide +kernel
theorem I1489_ok : RunOK pI1489 1489 (runFrom pI1489 (fmask pI1489) (cmask pI1489) (hmask pI1489) 1053 436 (true, I1489_cp1.1, I1489_cp1.2)) ∧ intTest pI1489 (runFrom pI1489 (fmask pI1489) (cmask pI1489) (hmask pI1489) 1053 436 (true, I1489_cp1.1, I1489_cp1.2)) 1489 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1489_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1489_fin) true) I1489_seg1) (by decide) rfl I1489_fin intTest_fst
theorem link1489 : linkOK pL1489 pH1489 pI1489 = true := by decide +kernel
theorem cvx1489 : ConvexBetweenHumps 1489 :=
  cvx_of L1489_ok H1489_ok I1489_ok link1489 (by decide)

/-! ### `N = 1490` -/

def pL1490 : Prm := ⟨80, 38, 39, 1492, 11, 18446744073709551616, 125118738538319902, 125118738538319902⟩
def pH1490 : Prm := ⟨80, 38, 39, 1492, 11, 18446744073709551616, 125119838049947678, 125119838049947678⟩
def pI1490 : Prm := ⟨66, 33, 30, 1492, 11, 18446744073709551616, 125118738538319902, 125119838049947678⟩
noncomputable def L1490_cp1 : Nat × Nat := t7val% (fastRun pL1490 1 1053 (init pL1490) (init pL1490))
theorem L1490_seg1 : segOK pL1490 1 1053 (init pL1490) (init pL1490) L1490_cp1.1 L1490_cp1.2 = true := by
  decide +kernel
theorem L1490_fin : (prmOK pL1490 1490 && ptTest pL1490 (runFrom pL1490 (fmask pL1490) (cmask pL1490) (hmask pL1490) 1054 436 (true, L1490_cp1.1, L1490_cp1.2)) 1490 745 false) = true := by
  decide +kernel
theorem L1490_ok : RunOK pL1490 1490 (runFrom pL1490 (fmask pL1490) (cmask pL1490) (hmask pL1490) 1054 436 (true, L1490_cp1.1, L1490_cp1.2)) ∧ ptTest pL1490 (runFrom pL1490 (fmask pL1490) (cmask pL1490) (hmask pL1490) 1054 436 (true, L1490_cp1.1, L1490_cp1.2)) 1490 745 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1490_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1490_fin) true) L1490_seg1) (by decide) rfl L1490_fin ptTest_fst
noncomputable def H1490_cp1 : Nat × Nat := t7val% (fastRun pH1490 1 1053 (init pH1490) (init pH1490))
theorem H1490_seg1 : segOK pH1490 1 1053 (init pH1490) (init pH1490) H1490_cp1.1 H1490_cp1.2 = true := by
  decide +kernel
theorem H1490_fin : (prmOK pH1490 1490 && ptTest pH1490 (runFrom pH1490 (fmask pH1490) (cmask pH1490) (hmask pH1490) 1054 436 (true, H1490_cp1.1, H1490_cp1.2)) 1490 745 true) = true := by
  decide +kernel
theorem H1490_ok : RunOK pH1490 1490 (runFrom pH1490 (fmask pH1490) (cmask pH1490) (hmask pH1490) 1054 436 (true, H1490_cp1.1, H1490_cp1.2)) ∧ ptTest pH1490 (runFrom pH1490 (fmask pH1490) (cmask pH1490) (hmask pH1490) 1054 436 (true, H1490_cp1.1, H1490_cp1.2)) 1490 745 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1490_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1490_fin) true) H1490_seg1) (by decide) rfl H1490_fin ptTest_fst
noncomputable def I1490_cp1 : Nat × Nat := t7val% (fastRun pI1490 1 1053 (init pI1490) (init pI1490))
theorem I1490_seg1 : segOK pI1490 1 1053 (init pI1490) (init pI1490) I1490_cp1.1 I1490_cp1.2 = true := by
  decide +kernel
theorem I1490_fin : (prmOK pI1490 1490 && intTest pI1490 (runFrom pI1490 (fmask pI1490) (cmask pI1490) (hmask pI1490) 1054 436 (true, I1490_cp1.1, I1490_cp1.2)) 1490 20 true) = true := by
  decide +kernel
theorem I1490_ok : RunOK pI1490 1490 (runFrom pI1490 (fmask pI1490) (cmask pI1490) (hmask pI1490) 1054 436 (true, I1490_cp1.1, I1490_cp1.2)) ∧ intTest pI1490 (runFrom pI1490 (fmask pI1490) (cmask pI1490) (hmask pI1490) 1054 436 (true, I1490_cp1.1, I1490_cp1.2)) 1490 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1490_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1490_fin) true) I1490_seg1) (by decide) rfl I1490_fin intTest_fst
theorem link1490 : linkOK pL1490 pH1490 pI1490 = true := by decide +kernel
theorem cvx1490 : ConvexBetweenHumps 1490 :=
  cvx_of L1490_ok H1490_ok I1490_ok link1490 (by decide)
theorem cenlink1490 : cenLinkOK pI1490 1490 = true := by decide +kernel
theorem cen1490 : CenterUniqueMin 1490 ∧ DipHyp 1490 ∧ OnePointHyps 1490 :=
  cen_of L1490_ok H1490_ok I1490_ok link1490 cenlink1490

/-! ### `N = 1491` -/

def pL1491 : Prm := ⟨80, 38, 39, 1493, 11, 18446744073709551616, 125050456256381393, 125050456256381393⟩
def pH1491 : Prm := ⟨80, 38, 39, 1493, 11, 18446744073709551616, 125051555768009169, 125051555768009169⟩
def pI1491 : Prm := ⟨66, 33, 30, 1493, 11, 18446744073709551616, 125050456256381393, 125051555768009169⟩
noncomputable def L1491_cp1 : Nat × Nat := t7val% (fastRun pL1491 1 1053 (init pL1491) (init pL1491))
theorem L1491_seg1 : segOK pL1491 1 1053 (init pL1491) (init pL1491) L1491_cp1.1 L1491_cp1.2 = true := by
  decide +kernel
theorem L1491_fin : (prmOK pL1491 1491 && ptTest pL1491 (runFrom pL1491 (fmask pL1491) (cmask pL1491) (hmask pL1491) 1054 437 (true, L1491_cp1.1, L1491_cp1.2)) 1491 746 false) = true := by
  decide +kernel
theorem L1491_ok : RunOK pL1491 1491 (runFrom pL1491 (fmask pL1491) (cmask pL1491) (hmask pL1491) 1054 437 (true, L1491_cp1.1, L1491_cp1.2)) ∧ ptTest pL1491 (runFrom pL1491 (fmask pL1491) (cmask pL1491) (hmask pL1491) 1054 437 (true, L1491_cp1.1, L1491_cp1.2)) 1491 746 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1491_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1491_fin) true) L1491_seg1) (by decide) rfl L1491_fin ptTest_fst
noncomputable def H1491_cp1 : Nat × Nat := t7val% (fastRun pH1491 1 1053 (init pH1491) (init pH1491))
theorem H1491_seg1 : segOK pH1491 1 1053 (init pH1491) (init pH1491) H1491_cp1.1 H1491_cp1.2 = true := by
  decide +kernel
theorem H1491_fin : (prmOK pH1491 1491 && ptTest pH1491 (runFrom pH1491 (fmask pH1491) (cmask pH1491) (hmask pH1491) 1054 437 (true, H1491_cp1.1, H1491_cp1.2)) 1491 746 true) = true := by
  decide +kernel
theorem H1491_ok : RunOK pH1491 1491 (runFrom pH1491 (fmask pH1491) (cmask pH1491) (hmask pH1491) 1054 437 (true, H1491_cp1.1, H1491_cp1.2)) ∧ ptTest pH1491 (runFrom pH1491 (fmask pH1491) (cmask pH1491) (hmask pH1491) 1054 437 (true, H1491_cp1.1, H1491_cp1.2)) 1491 746 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1491_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1491_fin) true) H1491_seg1) (by decide) rfl H1491_fin ptTest_fst
noncomputable def I1491_cp1 : Nat × Nat := t7val% (fastRun pI1491 1 1053 (init pI1491) (init pI1491))
theorem I1491_seg1 : segOK pI1491 1 1053 (init pI1491) (init pI1491) I1491_cp1.1 I1491_cp1.2 = true := by
  decide +kernel
theorem I1491_fin : (prmOK pI1491 1491 && intTest pI1491 (runFrom pI1491 (fmask pI1491) (cmask pI1491) (hmask pI1491) 1054 437 (true, I1491_cp1.1, I1491_cp1.2)) 1491 20 false) = true := by
  decide +kernel
theorem I1491_ok : RunOK pI1491 1491 (runFrom pI1491 (fmask pI1491) (cmask pI1491) (hmask pI1491) 1054 437 (true, I1491_cp1.1, I1491_cp1.2)) ∧ intTest pI1491 (runFrom pI1491 (fmask pI1491) (cmask pI1491) (hmask pI1491) 1054 437 (true, I1491_cp1.1, I1491_cp1.2)) 1491 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1491_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1491_fin) true) I1491_seg1) (by decide) rfl I1491_fin intTest_fst
theorem link1491 : linkOK pL1491 pH1491 pI1491 = true := by decide +kernel
theorem cvx1491 : ConvexBetweenHumps 1491 :=
  cvx_of L1491_ok H1491_ok I1491_ok link1491 (by decide)

/-! ### `N = 1492` -/

def pL1492 : Prm := ⟨80, 38, 39, 1494, 11, 18446744073709551616, 124982289145748723, 124982289145748723⟩
def pH1492 : Prm := ⟨80, 38, 39, 1494, 11, 18446744073709551616, 124983388657376499, 124983388657376499⟩
def pI1492 : Prm := ⟨66, 33, 30, 1494, 11, 18446744073709551616, 124982289145748723, 124983388657376499⟩
noncomputable def L1492_cp1 : Nat × Nat := t7val% (fastRun pL1492 1 1054 (init pL1492) (init pL1492))
theorem L1492_seg1 : segOK pL1492 1 1054 (init pL1492) (init pL1492) L1492_cp1.1 L1492_cp1.2 = true := by
  decide +kernel
theorem L1492_fin : (prmOK pL1492 1492 && ptTest pL1492 (runFrom pL1492 (fmask pL1492) (cmask pL1492) (hmask pL1492) 1055 437 (true, L1492_cp1.1, L1492_cp1.2)) 1492 746 false) = true := by
  decide +kernel
theorem L1492_ok : RunOK pL1492 1492 (runFrom pL1492 (fmask pL1492) (cmask pL1492) (hmask pL1492) 1055 437 (true, L1492_cp1.1, L1492_cp1.2)) ∧ ptTest pL1492 (runFrom pL1492 (fmask pL1492) (cmask pL1492) (hmask pL1492) 1055 437 (true, L1492_cp1.1, L1492_cp1.2)) 1492 746 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1492_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1492_fin) true) L1492_seg1) (by decide) rfl L1492_fin ptTest_fst
noncomputable def H1492_cp1 : Nat × Nat := t7val% (fastRun pH1492 1 1054 (init pH1492) (init pH1492))
theorem H1492_seg1 : segOK pH1492 1 1054 (init pH1492) (init pH1492) H1492_cp1.1 H1492_cp1.2 = true := by
  decide +kernel
theorem H1492_fin : (prmOK pH1492 1492 && ptTest pH1492 (runFrom pH1492 (fmask pH1492) (cmask pH1492) (hmask pH1492) 1055 437 (true, H1492_cp1.1, H1492_cp1.2)) 1492 746 true) = true := by
  decide +kernel
theorem H1492_ok : RunOK pH1492 1492 (runFrom pH1492 (fmask pH1492) (cmask pH1492) (hmask pH1492) 1055 437 (true, H1492_cp1.1, H1492_cp1.2)) ∧ ptTest pH1492 (runFrom pH1492 (fmask pH1492) (cmask pH1492) (hmask pH1492) 1055 437 (true, H1492_cp1.1, H1492_cp1.2)) 1492 746 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1492_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1492_fin) true) H1492_seg1) (by decide) rfl H1492_fin ptTest_fst
noncomputable def I1492_cp1 : Nat × Nat := t7val% (fastRun pI1492 1 1054 (init pI1492) (init pI1492))
theorem I1492_seg1 : segOK pI1492 1 1054 (init pI1492) (init pI1492) I1492_cp1.1 I1492_cp1.2 = true := by
  decide +kernel
theorem I1492_fin : (prmOK pI1492 1492 && intTest pI1492 (runFrom pI1492 (fmask pI1492) (cmask pI1492) (hmask pI1492) 1055 437 (true, I1492_cp1.1, I1492_cp1.2)) 1492 20 true) = true := by
  decide +kernel
theorem I1492_ok : RunOK pI1492 1492 (runFrom pI1492 (fmask pI1492) (cmask pI1492) (hmask pI1492) 1055 437 (true, I1492_cp1.1, I1492_cp1.2)) ∧ intTest pI1492 (runFrom pI1492 (fmask pI1492) (cmask pI1492) (hmask pI1492) 1055 437 (true, I1492_cp1.1, I1492_cp1.2)) 1492 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1492_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1492_fin) true) I1492_seg1) (by decide) rfl I1492_fin intTest_fst
theorem link1492 : linkOK pL1492 pH1492 pI1492 = true := by decide +kernel
theorem cvx1492 : ConvexBetweenHumps 1492 :=
  cvx_of L1492_ok H1492_ok I1492_ok link1492 (by decide)
theorem cenlink1492 : cenLinkOK pI1492 1492 = true := by decide +kernel
theorem cen1492 : CenterUniqueMin 1492 ∧ DipHyp 1492 ∧ OnePointHyps 1492 :=
  cen_of L1492_ok H1492_ok I1492_ok link1492 cenlink1492

/-! ### `N = 1493` -/

def pL1493 : Prm := ⟨80, 38, 39, 1495, 11, 18446744073709551616, 124914168804400682, 124914168804400682⟩
def pH1493 : Prm := ⟨80, 38, 39, 1495, 11, 18446744073709551616, 124915268316028458, 124915268316028458⟩
def pI1493 : Prm := ⟨66, 33, 30, 1495, 11, 18446744073709551616, 124914168804400682, 124915268316028458⟩
noncomputable def L1493_cp1 : Nat × Nat := t7val% (fastRun pL1493 1 1055 (init pL1493) (init pL1493))
theorem L1493_seg1 : segOK pL1493 1 1055 (init pL1493) (init pL1493) L1493_cp1.1 L1493_cp1.2 = true := by
  decide +kernel
theorem L1493_fin : (prmOK pL1493 1493 && ptTest pL1493 (runFrom pL1493 (fmask pL1493) (cmask pL1493) (hmask pL1493) 1056 437 (true, L1493_cp1.1, L1493_cp1.2)) 1493 747 false) = true := by
  decide +kernel
theorem L1493_ok : RunOK pL1493 1493 (runFrom pL1493 (fmask pL1493) (cmask pL1493) (hmask pL1493) 1056 437 (true, L1493_cp1.1, L1493_cp1.2)) ∧ ptTest pL1493 (runFrom pL1493 (fmask pL1493) (cmask pL1493) (hmask pL1493) 1056 437 (true, L1493_cp1.1, L1493_cp1.2)) 1493 747 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1493_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1493_fin) true) L1493_seg1) (by decide) rfl L1493_fin ptTest_fst
noncomputable def H1493_cp1 : Nat × Nat := t7val% (fastRun pH1493 1 1055 (init pH1493) (init pH1493))
theorem H1493_seg1 : segOK pH1493 1 1055 (init pH1493) (init pH1493) H1493_cp1.1 H1493_cp1.2 = true := by
  decide +kernel
theorem H1493_fin : (prmOK pH1493 1493 && ptTest pH1493 (runFrom pH1493 (fmask pH1493) (cmask pH1493) (hmask pH1493) 1056 437 (true, H1493_cp1.1, H1493_cp1.2)) 1493 747 true) = true := by
  decide +kernel
theorem H1493_ok : RunOK pH1493 1493 (runFrom pH1493 (fmask pH1493) (cmask pH1493) (hmask pH1493) 1056 437 (true, H1493_cp1.1, H1493_cp1.2)) ∧ ptTest pH1493 (runFrom pH1493 (fmask pH1493) (cmask pH1493) (hmask pH1493) 1056 437 (true, H1493_cp1.1, H1493_cp1.2)) 1493 747 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1493_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1493_fin) true) H1493_seg1) (by decide) rfl H1493_fin ptTest_fst
noncomputable def I1493_cp1 : Nat × Nat := t7val% (fastRun pI1493 1 1055 (init pI1493) (init pI1493))
theorem I1493_seg1 : segOK pI1493 1 1055 (init pI1493) (init pI1493) I1493_cp1.1 I1493_cp1.2 = true := by
  decide +kernel
theorem I1493_fin : (prmOK pI1493 1493 && intTest pI1493 (runFrom pI1493 (fmask pI1493) (cmask pI1493) (hmask pI1493) 1056 437 (true, I1493_cp1.1, I1493_cp1.2)) 1493 20 false) = true := by
  decide +kernel
theorem I1493_ok : RunOK pI1493 1493 (runFrom pI1493 (fmask pI1493) (cmask pI1493) (hmask pI1493) 1056 437 (true, I1493_cp1.1, I1493_cp1.2)) ∧ intTest pI1493 (runFrom pI1493 (fmask pI1493) (cmask pI1493) (hmask pI1493) 1056 437 (true, I1493_cp1.1, I1493_cp1.2)) 1493 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1493_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1493_fin) true) I1493_seg1) (by decide) rfl I1493_fin intTest_fst
theorem link1493 : linkOK pL1493 pH1493 pI1493 = true := by decide +kernel
theorem cvx1493 : ConvexBetweenHumps 1493 :=
  cvx_of L1493_ok H1493_ok I1493_ok link1493 (by decide)

/-! ### `N = 1494` -/

def pL1494 : Prm := ⟨80, 38, 39, 1496, 11, 18446744073709551616, 124846163197963857, 124846163197963857⟩
def pH1494 : Prm := ⟨80, 38, 39, 1496, 11, 18446744073709551616, 124847262709591633, 124847262709591633⟩
def pI1494 : Prm := ⟨66, 33, 30, 1496, 11, 18446744073709551616, 124846163197963857, 124847262709591633⟩
noncomputable def L1494_cp1 : Nat × Nat := t7val% (fastRun pL1494 1 1055 (init pL1494) (init pL1494))
theorem L1494_seg1 : segOK pL1494 1 1055 (init pL1494) (init pL1494) L1494_cp1.1 L1494_cp1.2 = true := by
  decide +kernel
theorem L1494_fin : (prmOK pL1494 1494 && ptTest pL1494 (runFrom pL1494 (fmask pL1494) (cmask pL1494) (hmask pL1494) 1056 438 (true, L1494_cp1.1, L1494_cp1.2)) 1494 747 false) = true := by
  decide +kernel
theorem L1494_ok : RunOK pL1494 1494 (runFrom pL1494 (fmask pL1494) (cmask pL1494) (hmask pL1494) 1056 438 (true, L1494_cp1.1, L1494_cp1.2)) ∧ ptTest pL1494 (runFrom pL1494 (fmask pL1494) (cmask pL1494) (hmask pL1494) 1056 438 (true, L1494_cp1.1, L1494_cp1.2)) 1494 747 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1494_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1494_fin) true) L1494_seg1) (by decide) rfl L1494_fin ptTest_fst
noncomputable def H1494_cp1 : Nat × Nat := t7val% (fastRun pH1494 1 1055 (init pH1494) (init pH1494))
theorem H1494_seg1 : segOK pH1494 1 1055 (init pH1494) (init pH1494) H1494_cp1.1 H1494_cp1.2 = true := by
  decide +kernel
theorem H1494_fin : (prmOK pH1494 1494 && ptTest pH1494 (runFrom pH1494 (fmask pH1494) (cmask pH1494) (hmask pH1494) 1056 438 (true, H1494_cp1.1, H1494_cp1.2)) 1494 747 true) = true := by
  decide +kernel
theorem H1494_ok : RunOK pH1494 1494 (runFrom pH1494 (fmask pH1494) (cmask pH1494) (hmask pH1494) 1056 438 (true, H1494_cp1.1, H1494_cp1.2)) ∧ ptTest pH1494 (runFrom pH1494 (fmask pH1494) (cmask pH1494) (hmask pH1494) 1056 438 (true, H1494_cp1.1, H1494_cp1.2)) 1494 747 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1494_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1494_fin) true) H1494_seg1) (by decide) rfl H1494_fin ptTest_fst
noncomputable def I1494_cp1 : Nat × Nat := t7val% (fastRun pI1494 1 1055 (init pI1494) (init pI1494))
theorem I1494_seg1 : segOK pI1494 1 1055 (init pI1494) (init pI1494) I1494_cp1.1 I1494_cp1.2 = true := by
  decide +kernel
theorem I1494_fin : (prmOK pI1494 1494 && intTest pI1494 (runFrom pI1494 (fmask pI1494) (cmask pI1494) (hmask pI1494) 1056 438 (true, I1494_cp1.1, I1494_cp1.2)) 1494 20 true) = true := by
  decide +kernel
theorem I1494_ok : RunOK pI1494 1494 (runFrom pI1494 (fmask pI1494) (cmask pI1494) (hmask pI1494) 1056 438 (true, I1494_cp1.1, I1494_cp1.2)) ∧ intTest pI1494 (runFrom pI1494 (fmask pI1494) (cmask pI1494) (hmask pI1494) 1056 438 (true, I1494_cp1.1, I1494_cp1.2)) 1494 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1494_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1494_fin) true) I1494_seg1) (by decide) rfl I1494_fin intTest_fst
theorem link1494 : linkOK pL1494 pH1494 pI1494 = true := by decide +kernel
theorem cvx1494 : ConvexBetweenHumps 1494 :=
  cvx_of L1494_ok H1494_ok I1494_ok link1494 (by decide)
theorem cenlink1494 : cenLinkOK pI1494 1494 = true := by decide +kernel
theorem cen1494 : CenterUniqueMin 1494 ∧ DipHyp 1494 ∧ OnePointHyps 1494 :=
  cen_of L1494_ok H1494_ok I1494_ok link1494 cenlink1494

/-! ### `N = 1495` -/

def pL1495 : Prm := ⟨80, 38, 39, 1497, 11, 18446744073709551616, 124778204203424041, 124778204203424041⟩
def pH1495 : Prm := ⟨80, 38, 39, 1497, 11, 18446744073709551616, 124779303715051817, 124779303715051817⟩
def pI1495 : Prm := ⟨66, 33, 30, 1497, 11, 18446744073709551616, 124778204203424041, 124779303715051817⟩
noncomputable def L1495_cp1 : Nat × Nat := t7val% (fastRun pL1495 1 1056 (init pL1495) (init pL1495))
theorem L1495_seg1 : segOK pL1495 1 1056 (init pL1495) (init pL1495) L1495_cp1.1 L1495_cp1.2 = true := by
  decide +kernel
theorem L1495_fin : (prmOK pL1495 1495 && ptTest pL1495 (runFrom pL1495 (fmask pL1495) (cmask pL1495) (hmask pL1495) 1057 438 (true, L1495_cp1.1, L1495_cp1.2)) 1495 748 false) = true := by
  decide +kernel
theorem L1495_ok : RunOK pL1495 1495 (runFrom pL1495 (fmask pL1495) (cmask pL1495) (hmask pL1495) 1057 438 (true, L1495_cp1.1, L1495_cp1.2)) ∧ ptTest pL1495 (runFrom pL1495 (fmask pL1495) (cmask pL1495) (hmask pL1495) 1057 438 (true, L1495_cp1.1, L1495_cp1.2)) 1495 748 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1495_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1495_fin) true) L1495_seg1) (by decide) rfl L1495_fin ptTest_fst
noncomputable def H1495_cp1 : Nat × Nat := t7val% (fastRun pH1495 1 1056 (init pH1495) (init pH1495))
theorem H1495_seg1 : segOK pH1495 1 1056 (init pH1495) (init pH1495) H1495_cp1.1 H1495_cp1.2 = true := by
  decide +kernel
theorem H1495_fin : (prmOK pH1495 1495 && ptTest pH1495 (runFrom pH1495 (fmask pH1495) (cmask pH1495) (hmask pH1495) 1057 438 (true, H1495_cp1.1, H1495_cp1.2)) 1495 748 true) = true := by
  decide +kernel
theorem H1495_ok : RunOK pH1495 1495 (runFrom pH1495 (fmask pH1495) (cmask pH1495) (hmask pH1495) 1057 438 (true, H1495_cp1.1, H1495_cp1.2)) ∧ ptTest pH1495 (runFrom pH1495 (fmask pH1495) (cmask pH1495) (hmask pH1495) 1057 438 (true, H1495_cp1.1, H1495_cp1.2)) 1495 748 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1495_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1495_fin) true) H1495_seg1) (by decide) rfl H1495_fin ptTest_fst
noncomputable def I1495_cp1 : Nat × Nat := t7val% (fastRun pI1495 1 1056 (init pI1495) (init pI1495))
theorem I1495_seg1 : segOK pI1495 1 1056 (init pI1495) (init pI1495) I1495_cp1.1 I1495_cp1.2 = true := by
  decide +kernel
theorem I1495_fin : (prmOK pI1495 1495 && intTest pI1495 (runFrom pI1495 (fmask pI1495) (cmask pI1495) (hmask pI1495) 1057 438 (true, I1495_cp1.1, I1495_cp1.2)) 1495 20 false) = true := by
  decide +kernel
theorem I1495_ok : RunOK pI1495 1495 (runFrom pI1495 (fmask pI1495) (cmask pI1495) (hmask pI1495) 1057 438 (true, I1495_cp1.1, I1495_cp1.2)) ∧ intTest pI1495 (runFrom pI1495 (fmask pI1495) (cmask pI1495) (hmask pI1495) 1057 438 (true, I1495_cp1.1, I1495_cp1.2)) 1495 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1495_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1495_fin) true) I1495_seg1) (by decide) rfl I1495_fin intTest_fst
theorem link1495 : linkOK pL1495 pH1495 pI1495 = true := by decide +kernel
theorem cvx1495 : ConvexBetweenHumps 1495 :=
  cvx_of L1495_ok H1495_ok I1495_ok link1495 (by decide)

/-! ### The range -/

theorem cvx_1478_1495 {N : ℕ} (h1 : 1478 ≤ N) (h2 : N ≤ 1495) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1486
  · by_cases h4 : N ≤ 1481
    · by_cases h6 : N ≤ 1479
      · by_cases h8 : N ≤ 1478
        · obtain rfl : N = 1478 := by omega
          exact cvx1478
        · obtain rfl : N = 1479 := by omega
          exact cvx1479
      · by_cases h8 : N ≤ 1480
        · obtain rfl : N = 1480 := by omega
          exact cvx1480
        · obtain rfl : N = 1481 := by omega
          exact cvx1481
    · by_cases h6 : N ≤ 1483
      · by_cases h8 : N ≤ 1482
        · obtain rfl : N = 1482 := by omega
          exact cvx1482
        · obtain rfl : N = 1483 := by omega
          exact cvx1483
      · by_cases h8 : N ≤ 1484
        · obtain rfl : N = 1484 := by omega
          exact cvx1484
        · by_cases h10 : N ≤ 1485
          · obtain rfl : N = 1485 := by omega
            exact cvx1485
          · obtain rfl : N = 1486 := by omega
            exact cvx1486
  · by_cases h4 : N ≤ 1490
    · by_cases h6 : N ≤ 1488
      · by_cases h8 : N ≤ 1487
        · obtain rfl : N = 1487 := by omega
          exact cvx1487
        · obtain rfl : N = 1488 := by omega
          exact cvx1488
      · by_cases h8 : N ≤ 1489
        · obtain rfl : N = 1489 := by omega
          exact cvx1489
        · obtain rfl : N = 1490 := by omega
          exact cvx1490
    · by_cases h6 : N ≤ 1492
      · by_cases h8 : N ≤ 1491
        · obtain rfl : N = 1491 := by omega
          exact cvx1491
        · obtain rfl : N = 1492 := by omega
          exact cvx1492
      · by_cases h8 : N ≤ 1493
        · obtain rfl : N = 1493 := by omega
          exact cvx1493
        · by_cases h10 : N ≤ 1494
          · obtain rfl : N = 1494 := by omega
            exact cvx1494
          · obtain rfl : N = 1495 := by omega
            exact cvx1495

theorem cen_1478_1495 {N : ℕ} (h1 : 1478 ≤ N) (h2 : N ≤ 1495) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1484
  · by_cases h4 : N ≤ 1480
    · by_cases h6 : N ≤ 1478
      · obtain rfl : N = 1478 := by omega
        exact cen1478
      · obtain rfl : N = 1480 := by omega
        exact cen1480
    · by_cases h6 : N ≤ 1482
      · obtain rfl : N = 1482 := by omega
        exact cen1482
      · obtain rfl : N = 1484 := by omega
        exact cen1484
  · by_cases h4 : N ≤ 1488
    · by_cases h6 : N ≤ 1486
      · obtain rfl : N = 1486 := by omega
        exact cen1486
      · obtain rfl : N = 1488 := by omega
        exact cen1488
    · by_cases h6 : N ≤ 1490
      · obtain rfl : N = 1490 := by omega
        exact cen1490
      · by_cases h8 : N ≤ 1492
        · obtain rfl : N = 1492 := by omega
          exact cen1492
        · obtain rfl : N = 1494 := by omega
          exact cen1494

end Kagey131.PaperD.T7
