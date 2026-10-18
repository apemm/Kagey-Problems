import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1609, …, 1623` (generated)

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

/-! ### `N = 1609` -/

def pL1609 : Prm := ⟨82, 40, 39, 1611, 11, 18446744073709551616, 117525952622877493, 117525952622877493⟩
def pH1609 : Prm := ⟨82, 40, 39, 1611, 11, 18446744073709551616, 117527052134505269, 117527052134505269⟩
def pI1609 : Prm := ⟨67, 33, 31, 1611, 11, 18446744073709551616, 117525952622877493, 117527052134505269⟩
noncomputable def L1609_cp1 : Nat × Nat := t7val% (fastRun pL1609 1 1137 (init pL1609) (init pL1609))
theorem L1609_seg1 : segOK pL1609 1 1137 (init pL1609) (init pL1609) L1609_cp1.1 L1609_cp1.2 = true := by
  decide +kernel
theorem L1609_fin : (prmOK pL1609 1609 && ptTest pL1609 (runFrom pL1609 (fmask pL1609) (cmask pL1609) (hmask pL1609) 1138 471 (true, L1609_cp1.1, L1609_cp1.2)) 1609 805 false) = true := by
  decide +kernel
theorem L1609_ok : RunOK pL1609 1609 (runFrom pL1609 (fmask pL1609) (cmask pL1609) (hmask pL1609) 1138 471 (true, L1609_cp1.1, L1609_cp1.2)) ∧ ptTest pL1609 (runFrom pL1609 (fmask pL1609) (cmask pL1609) (hmask pL1609) 1138 471 (true, L1609_cp1.1, L1609_cp1.2)) 1609 805 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1609_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1609_fin) true) L1609_seg1) (by decide) rfl L1609_fin ptTest_fst
noncomputable def H1609_cp1 : Nat × Nat := t7val% (fastRun pH1609 1 1137 (init pH1609) (init pH1609))
theorem H1609_seg1 : segOK pH1609 1 1137 (init pH1609) (init pH1609) H1609_cp1.1 H1609_cp1.2 = true := by
  decide +kernel
theorem H1609_fin : (prmOK pH1609 1609 && ptTest pH1609 (runFrom pH1609 (fmask pH1609) (cmask pH1609) (hmask pH1609) 1138 471 (true, H1609_cp1.1, H1609_cp1.2)) 1609 805 true) = true := by
  decide +kernel
theorem H1609_ok : RunOK pH1609 1609 (runFrom pH1609 (fmask pH1609) (cmask pH1609) (hmask pH1609) 1138 471 (true, H1609_cp1.1, H1609_cp1.2)) ∧ ptTest pH1609 (runFrom pH1609 (fmask pH1609) (cmask pH1609) (hmask pH1609) 1138 471 (true, H1609_cp1.1, H1609_cp1.2)) 1609 805 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1609_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1609_fin) true) H1609_seg1) (by decide) rfl H1609_fin ptTest_fst
noncomputable def I1609_cp1 : Nat × Nat := t7val% (fastRun pI1609 1 1137 (init pI1609) (init pI1609))
theorem I1609_seg1 : segOK pI1609 1 1137 (init pI1609) (init pI1609) I1609_cp1.1 I1609_cp1.2 = true := by
  decide +kernel
theorem I1609_fin : (prmOK pI1609 1609 && intTest pI1609 (runFrom pI1609 (fmask pI1609) (cmask pI1609) (hmask pI1609) 1138 471 (true, I1609_cp1.1, I1609_cp1.2)) 1609 21 false) = true := by
  decide +kernel
theorem I1609_ok : RunOK pI1609 1609 (runFrom pI1609 (fmask pI1609) (cmask pI1609) (hmask pI1609) 1138 471 (true, I1609_cp1.1, I1609_cp1.2)) ∧ intTest pI1609 (runFrom pI1609 (fmask pI1609) (cmask pI1609) (hmask pI1609) 1138 471 (true, I1609_cp1.1, I1609_cp1.2)) 1609 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1609_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1609_fin) true) I1609_seg1) (by decide) rfl I1609_fin intTest_fst
theorem link1609 : linkOK pL1609 pH1609 pI1609 = true := by decide +kernel
theorem cvx1609 : ConvexBetweenHumps 1609 :=
  cvx_of L1609_ok H1609_ok I1609_ok link1609 (by decide)

/-! ### `N = 1610` -/

def pL1610 : Prm := ⟨82, 40, 39, 1612, 11, 18446744073709551616, 117466389768754118, 117466389768754118⟩
def pH1610 : Prm := ⟨80, 37, 40, 1612, 11, 18446744073709551616, 117467489280381894, 117467489280381894⟩
def pI1610 : Prm := ⟨67, 33, 31, 1612, 11, 18446744073709551616, 117466389768754118, 117467489280381894⟩
noncomputable def L1610_cp1 : Nat × Nat := t7val% (fastRun pL1610 1 1137 (init pL1610) (init pL1610))
theorem L1610_seg1 : segOK pL1610 1 1137 (init pL1610) (init pL1610) L1610_cp1.1 L1610_cp1.2 = true := by
  decide +kernel
theorem L1610_fin : (prmOK pL1610 1610 && ptTest pL1610 (runFrom pL1610 (fmask pL1610) (cmask pL1610) (hmask pL1610) 1138 472 (true, L1610_cp1.1, L1610_cp1.2)) 1610 805 false) = true := by
  decide +kernel
theorem L1610_ok : RunOK pL1610 1610 (runFrom pL1610 (fmask pL1610) (cmask pL1610) (hmask pL1610) 1138 472 (true, L1610_cp1.1, L1610_cp1.2)) ∧ ptTest pL1610 (runFrom pL1610 (fmask pL1610) (cmask pL1610) (hmask pL1610) 1138 472 (true, L1610_cp1.1, L1610_cp1.2)) 1610 805 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1610_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1610_fin) true) L1610_seg1) (by decide) rfl L1610_fin ptTest_fst
noncomputable def H1610_cp1 : Nat × Nat := t7val% (fastRun pH1610 1 1137 (init pH1610) (init pH1610))
theorem H1610_seg1 : segOK pH1610 1 1137 (init pH1610) (init pH1610) H1610_cp1.1 H1610_cp1.2 = true := by
  decide +kernel
theorem H1610_fin : (prmOK pH1610 1610 && ptTest pH1610 (runFrom pH1610 (fmask pH1610) (cmask pH1610) (hmask pH1610) 1138 472 (true, H1610_cp1.1, H1610_cp1.2)) 1610 805 true) = true := by
  decide +kernel
theorem H1610_ok : RunOK pH1610 1610 (runFrom pH1610 (fmask pH1610) (cmask pH1610) (hmask pH1610) 1138 472 (true, H1610_cp1.1, H1610_cp1.2)) ∧ ptTest pH1610 (runFrom pH1610 (fmask pH1610) (cmask pH1610) (hmask pH1610) 1138 472 (true, H1610_cp1.1, H1610_cp1.2)) 1610 805 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1610_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1610_fin) true) H1610_seg1) (by decide) rfl H1610_fin ptTest_fst
noncomputable def I1610_cp1 : Nat × Nat := t7val% (fastRun pI1610 1 1137 (init pI1610) (init pI1610))
theorem I1610_seg1 : segOK pI1610 1 1137 (init pI1610) (init pI1610) I1610_cp1.1 I1610_cp1.2 = true := by
  decide +kernel
theorem I1610_fin : (prmOK pI1610 1610 && intTest pI1610 (runFrom pI1610 (fmask pI1610) (cmask pI1610) (hmask pI1610) 1138 472 (true, I1610_cp1.1, I1610_cp1.2)) 1610 21 true) = true := by
  decide +kernel
theorem I1610_ok : RunOK pI1610 1610 (runFrom pI1610 (fmask pI1610) (cmask pI1610) (hmask pI1610) 1138 472 (true, I1610_cp1.1, I1610_cp1.2)) ∧ intTest pI1610 (runFrom pI1610 (fmask pI1610) (cmask pI1610) (hmask pI1610) 1138 472 (true, I1610_cp1.1, I1610_cp1.2)) 1610 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1610_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1610_fin) true) I1610_seg1) (by decide) rfl I1610_fin intTest_fst
theorem link1610 : linkOK pL1610 pH1610 pI1610 = true := by decide +kernel
theorem cvx1610 : ConvexBetweenHumps 1610 :=
  cvx_of L1610_ok H1610_ok I1610_ok link1610 (by decide)
theorem cenlink1610 : cenLinkOK pI1610 1610 = true := by decide +kernel
theorem cen1610 : CenterUniqueMin 1610 ∧ DipHyp 1610 ∧ OnePointHyps 1610 :=
  cen_of L1610_ok H1610_ok I1610_ok link1610 cenlink1610

/-! ### `N = 1611` -/

def pL1611 : Prm := ⟨82, 40, 39, 1613, 11, 18446744073709551616, 117406865504850411, 117406865504850411⟩
def pH1611 : Prm := ⟨80, 37, 40, 1613, 11, 18446744073709551616, 117407965016478187, 117407965016478187⟩
def pI1611 : Prm := ⟨67, 33, 31, 1613, 11, 18446744073709551616, 117406865504850411, 117407965016478187⟩
noncomputable def L1611_cp1 : Nat × Nat := t7val% (fastRun pL1611 1 1138 (init pL1611) (init pL1611))
theorem L1611_seg1 : segOK pL1611 1 1138 (init pL1611) (init pL1611) L1611_cp1.1 L1611_cp1.2 = true := by
  decide +kernel
theorem L1611_fin : (prmOK pL1611 1611 && ptTest pL1611 (runFrom pL1611 (fmask pL1611) (cmask pL1611) (hmask pL1611) 1139 472 (true, L1611_cp1.1, L1611_cp1.2)) 1611 806 false) = true := by
  decide +kernel
theorem L1611_ok : RunOK pL1611 1611 (runFrom pL1611 (fmask pL1611) (cmask pL1611) (hmask pL1611) 1139 472 (true, L1611_cp1.1, L1611_cp1.2)) ∧ ptTest pL1611 (runFrom pL1611 (fmask pL1611) (cmask pL1611) (hmask pL1611) 1139 472 (true, L1611_cp1.1, L1611_cp1.2)) 1611 806 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1611_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1611_fin) true) L1611_seg1) (by decide) rfl L1611_fin ptTest_fst
noncomputable def H1611_cp1 : Nat × Nat := t7val% (fastRun pH1611 1 1138 (init pH1611) (init pH1611))
theorem H1611_seg1 : segOK pH1611 1 1138 (init pH1611) (init pH1611) H1611_cp1.1 H1611_cp1.2 = true := by
  decide +kernel
theorem H1611_fin : (prmOK pH1611 1611 && ptTest pH1611 (runFrom pH1611 (fmask pH1611) (cmask pH1611) (hmask pH1611) 1139 472 (true, H1611_cp1.1, H1611_cp1.2)) 1611 806 true) = true := by
  decide +kernel
theorem H1611_ok : RunOK pH1611 1611 (runFrom pH1611 (fmask pH1611) (cmask pH1611) (hmask pH1611) 1139 472 (true, H1611_cp1.1, H1611_cp1.2)) ∧ ptTest pH1611 (runFrom pH1611 (fmask pH1611) (cmask pH1611) (hmask pH1611) 1139 472 (true, H1611_cp1.1, H1611_cp1.2)) 1611 806 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1611_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1611_fin) true) H1611_seg1) (by decide) rfl H1611_fin ptTest_fst
noncomputable def I1611_cp1 : Nat × Nat := t7val% (fastRun pI1611 1 1138 (init pI1611) (init pI1611))
theorem I1611_seg1 : segOK pI1611 1 1138 (init pI1611) (init pI1611) I1611_cp1.1 I1611_cp1.2 = true := by
  decide +kernel
theorem I1611_fin : (prmOK pI1611 1611 && intTest pI1611 (runFrom pI1611 (fmask pI1611) (cmask pI1611) (hmask pI1611) 1139 472 (true, I1611_cp1.1, I1611_cp1.2)) 1611 21 false) = true := by
  decide +kernel
theorem I1611_ok : RunOK pI1611 1611 (runFrom pI1611 (fmask pI1611) (cmask pI1611) (hmask pI1611) 1139 472 (true, I1611_cp1.1, I1611_cp1.2)) ∧ intTest pI1611 (runFrom pI1611 (fmask pI1611) (cmask pI1611) (hmask pI1611) 1139 472 (true, I1611_cp1.1, I1611_cp1.2)) 1611 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1611_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1611_fin) true) I1611_seg1) (by decide) rfl I1611_fin intTest_fst
theorem link1611 : linkOK pL1611 pH1611 pI1611 = true := by decide +kernel
theorem cvx1611 : ConvexBetweenHumps 1611 :=
  cvx_of L1611_ok H1611_ok I1611_ok link1611 (by decide)

/-! ### `N = 1612` -/

def pL1612 : Prm := ⟨82, 40, 39, 1614, 11, 18446744073709551616, 117347433733806933, 117347433733806933⟩
def pH1612 : Prm := ⟨80, 37, 40, 1614, 11, 18446744073709551616, 117348533245434709, 117348533245434709⟩
def pI1612 : Prm := ⟨67, 33, 31, 1614, 11, 18446744073709551616, 117347433733806933, 117348533245434709⟩
noncomputable def L1612_cp1 : Nat × Nat := t7val% (fastRun pL1612 1 1139 (init pL1612) (init pL1612))
theorem L1612_seg1 : segOK pL1612 1 1139 (init pL1612) (init pL1612) L1612_cp1.1 L1612_cp1.2 = true := by
  decide +kernel
theorem L1612_fin : (prmOK pL1612 1612 && ptTest pL1612 (runFrom pL1612 (fmask pL1612) (cmask pL1612) (hmask pL1612) 1140 472 (true, L1612_cp1.1, L1612_cp1.2)) 1612 806 false) = true := by
  decide +kernel
theorem L1612_ok : RunOK pL1612 1612 (runFrom pL1612 (fmask pL1612) (cmask pL1612) (hmask pL1612) 1140 472 (true, L1612_cp1.1, L1612_cp1.2)) ∧ ptTest pL1612 (runFrom pL1612 (fmask pL1612) (cmask pL1612) (hmask pL1612) 1140 472 (true, L1612_cp1.1, L1612_cp1.2)) 1612 806 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1612_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1612_fin) true) L1612_seg1) (by decide) rfl L1612_fin ptTest_fst
noncomputable def H1612_cp1 : Nat × Nat := t7val% (fastRun pH1612 1 1139 (init pH1612) (init pH1612))
theorem H1612_seg1 : segOK pH1612 1 1139 (init pH1612) (init pH1612) H1612_cp1.1 H1612_cp1.2 = true := by
  decide +kernel
theorem H1612_fin : (prmOK pH1612 1612 && ptTest pH1612 (runFrom pH1612 (fmask pH1612) (cmask pH1612) (hmask pH1612) 1140 472 (true, H1612_cp1.1, H1612_cp1.2)) 1612 806 true) = true := by
  decide +kernel
theorem H1612_ok : RunOK pH1612 1612 (runFrom pH1612 (fmask pH1612) (cmask pH1612) (hmask pH1612) 1140 472 (true, H1612_cp1.1, H1612_cp1.2)) ∧ ptTest pH1612 (runFrom pH1612 (fmask pH1612) (cmask pH1612) (hmask pH1612) 1140 472 (true, H1612_cp1.1, H1612_cp1.2)) 1612 806 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1612_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1612_fin) true) H1612_seg1) (by decide) rfl H1612_fin ptTest_fst
noncomputable def I1612_cp1 : Nat × Nat := t7val% (fastRun pI1612 1 1139 (init pI1612) (init pI1612))
theorem I1612_seg1 : segOK pI1612 1 1139 (init pI1612) (init pI1612) I1612_cp1.1 I1612_cp1.2 = true := by
  decide +kernel
theorem I1612_fin : (prmOK pI1612 1612 && intTest pI1612 (runFrom pI1612 (fmask pI1612) (cmask pI1612) (hmask pI1612) 1140 472 (true, I1612_cp1.1, I1612_cp1.2)) 1612 21 true) = true := by
  decide +kernel
theorem I1612_ok : RunOK pI1612 1612 (runFrom pI1612 (fmask pI1612) (cmask pI1612) (hmask pI1612) 1140 472 (true, I1612_cp1.1, I1612_cp1.2)) ∧ intTest pI1612 (runFrom pI1612 (fmask pI1612) (cmask pI1612) (hmask pI1612) 1140 472 (true, I1612_cp1.1, I1612_cp1.2)) 1612 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1612_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1612_fin) true) I1612_seg1) (by decide) rfl I1612_fin intTest_fst
theorem link1612 : linkOK pL1612 pH1612 pI1612 = true := by decide +kernel
theorem cvx1612 : ConvexBetweenHumps 1612 :=
  cvx_of L1612_ok H1612_ok I1612_ok link1612 (by decide)
theorem cenlink1612 : cenLinkOK pI1612 1612 = true := by decide +kernel
theorem cen1612 : CenterUniqueMin 1612 ∧ DipHyp 1612 ∧ OnePointHyps 1612 :=
  cen_of L1612_ok H1612_ok I1612_ok link1612 cenlink1612

/-! ### `N = 1613` -/

def pL1613 : Prm := ⟨82, 40, 39, 1615, 11, 18446744073709551616, 117288040431751120, 117288040431751120⟩
def pH1613 : Prm := ⟨82, 40, 39, 1615, 11, 18446744073709551616, 117289139943378896, 117289139943378896⟩
def pI1613 : Prm := ⟨67, 33, 31, 1615, 11, 18446744073709551616, 117288040431751120, 117289139943378896⟩
noncomputable def L1613_cp1 : Nat × Nat := t7val% (fastRun pL1613 1 1140 (init pL1613) (init pL1613))
theorem L1613_seg1 : segOK pL1613 1 1140 (init pL1613) (init pL1613) L1613_cp1.1 L1613_cp1.2 = true := by
  decide +kernel
theorem L1613_fin : (prmOK pL1613 1613 && ptTest pL1613 (runFrom pL1613 (fmask pL1613) (cmask pL1613) (hmask pL1613) 1141 472 (true, L1613_cp1.1, L1613_cp1.2)) 1613 807 false) = true := by
  decide +kernel
theorem L1613_ok : RunOK pL1613 1613 (runFrom pL1613 (fmask pL1613) (cmask pL1613) (hmask pL1613) 1141 472 (true, L1613_cp1.1, L1613_cp1.2)) ∧ ptTest pL1613 (runFrom pL1613 (fmask pL1613) (cmask pL1613) (hmask pL1613) 1141 472 (true, L1613_cp1.1, L1613_cp1.2)) 1613 807 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1613_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1613_fin) true) L1613_seg1) (by decide) rfl L1613_fin ptTest_fst
noncomputable def H1613_cp1 : Nat × Nat := t7val% (fastRun pH1613 1 1140 (init pH1613) (init pH1613))
theorem H1613_seg1 : segOK pH1613 1 1140 (init pH1613) (init pH1613) H1613_cp1.1 H1613_cp1.2 = true := by
  decide +kernel
theorem H1613_fin : (prmOK pH1613 1613 && ptTest pH1613 (runFrom pH1613 (fmask pH1613) (cmask pH1613) (hmask pH1613) 1141 472 (true, H1613_cp1.1, H1613_cp1.2)) 1613 807 true) = true := by
  decide +kernel
theorem H1613_ok : RunOK pH1613 1613 (runFrom pH1613 (fmask pH1613) (cmask pH1613) (hmask pH1613) 1141 472 (true, H1613_cp1.1, H1613_cp1.2)) ∧ ptTest pH1613 (runFrom pH1613 (fmask pH1613) (cmask pH1613) (hmask pH1613) 1141 472 (true, H1613_cp1.1, H1613_cp1.2)) 1613 807 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1613_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1613_fin) true) H1613_seg1) (by decide) rfl H1613_fin ptTest_fst
noncomputable def I1613_cp1 : Nat × Nat := t7val% (fastRun pI1613 1 1140 (init pI1613) (init pI1613))
theorem I1613_seg1 : segOK pI1613 1 1140 (init pI1613) (init pI1613) I1613_cp1.1 I1613_cp1.2 = true := by
  decide +kernel
theorem I1613_fin : (prmOK pI1613 1613 && intTest pI1613 (runFrom pI1613 (fmask pI1613) (cmask pI1613) (hmask pI1613) 1141 472 (true, I1613_cp1.1, I1613_cp1.2)) 1613 21 false) = true := by
  decide +kernel
theorem I1613_ok : RunOK pI1613 1613 (runFrom pI1613 (fmask pI1613) (cmask pI1613) (hmask pI1613) 1141 472 (true, I1613_cp1.1, I1613_cp1.2)) ∧ intTest pI1613 (runFrom pI1613 (fmask pI1613) (cmask pI1613) (hmask pI1613) 1141 472 (true, I1613_cp1.1, I1613_cp1.2)) 1613 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1613_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1613_fin) true) I1613_seg1) (by decide) rfl I1613_fin intTest_fst
theorem link1613 : linkOK pL1613 pH1613 pI1613 = true := by decide +kernel
theorem cvx1613 : ConvexBetweenHumps 1613 :=
  cvx_of L1613_ok H1613_ok I1613_ok link1613 (by decide)

/-! ### `N = 1614` -/

def pL1614 : Prm := ⟨82, 40, 39, 1616, 11, 18446744073709551616, 117228739297948181, 117228739297948181⟩
def pH1614 : Prm := ⟨82, 40, 39, 1616, 11, 18446744073709551616, 117229838809575957, 117229838809575957⟩
def pI1614 : Prm := ⟨67, 33, 31, 1616, 11, 18446744073709551616, 117228739297948181, 117229838809575957⟩
noncomputable def L1614_cp1 : Nat × Nat := t7val% (fastRun pL1614 1 1140 (init pL1614) (init pL1614))
theorem L1614_seg1 : segOK pL1614 1 1140 (init pL1614) (init pL1614) L1614_cp1.1 L1614_cp1.2 = true := by
  decide +kernel
theorem L1614_fin : (prmOK pL1614 1614 && ptTest pL1614 (runFrom pL1614 (fmask pL1614) (cmask pL1614) (hmask pL1614) 1141 473 (true, L1614_cp1.1, L1614_cp1.2)) 1614 807 false) = true := by
  decide +kernel
theorem L1614_ok : RunOK pL1614 1614 (runFrom pL1614 (fmask pL1614) (cmask pL1614) (hmask pL1614) 1141 473 (true, L1614_cp1.1, L1614_cp1.2)) ∧ ptTest pL1614 (runFrom pL1614 (fmask pL1614) (cmask pL1614) (hmask pL1614) 1141 473 (true, L1614_cp1.1, L1614_cp1.2)) 1614 807 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1614_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1614_fin) true) L1614_seg1) (by decide) rfl L1614_fin ptTest_fst
noncomputable def H1614_cp1 : Nat × Nat := t7val% (fastRun pH1614 1 1140 (init pH1614) (init pH1614))
theorem H1614_seg1 : segOK pH1614 1 1140 (init pH1614) (init pH1614) H1614_cp1.1 H1614_cp1.2 = true := by
  decide +kernel
theorem H1614_fin : (prmOK pH1614 1614 && ptTest pH1614 (runFrom pH1614 (fmask pH1614) (cmask pH1614) (hmask pH1614) 1141 473 (true, H1614_cp1.1, H1614_cp1.2)) 1614 807 true) = true := by
  decide +kernel
theorem H1614_ok : RunOK pH1614 1614 (runFrom pH1614 (fmask pH1614) (cmask pH1614) (hmask pH1614) 1141 473 (true, H1614_cp1.1, H1614_cp1.2)) ∧ ptTest pH1614 (runFrom pH1614 (fmask pH1614) (cmask pH1614) (hmask pH1614) 1141 473 (true, H1614_cp1.1, H1614_cp1.2)) 1614 807 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1614_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1614_fin) true) H1614_seg1) (by decide) rfl H1614_fin ptTest_fst
noncomputable def I1614_cp1 : Nat × Nat := t7val% (fastRun pI1614 1 1140 (init pI1614) (init pI1614))
theorem I1614_seg1 : segOK pI1614 1 1140 (init pI1614) (init pI1614) I1614_cp1.1 I1614_cp1.2 = true := by
  decide +kernel
theorem I1614_fin : (prmOK pI1614 1614 && intTest pI1614 (runFrom pI1614 (fmask pI1614) (cmask pI1614) (hmask pI1614) 1141 473 (true, I1614_cp1.1, I1614_cp1.2)) 1614 21 true) = true := by
  decide +kernel
theorem I1614_ok : RunOK pI1614 1614 (runFrom pI1614 (fmask pI1614) (cmask pI1614) (hmask pI1614) 1141 473 (true, I1614_cp1.1, I1614_cp1.2)) ∧ intTest pI1614 (runFrom pI1614 (fmask pI1614) (cmask pI1614) (hmask pI1614) 1141 473 (true, I1614_cp1.1, I1614_cp1.2)) 1614 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1614_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1614_fin) true) I1614_seg1) (by decide) rfl I1614_fin intTest_fst
theorem link1614 : linkOK pL1614 pH1614 pI1614 = true := by decide +kernel
theorem cvx1614 : ConvexBetweenHumps 1614 :=
  cvx_of L1614_ok H1614_ok I1614_ok link1614 (by decide)
theorem cenlink1614 : cenLinkOK pI1614 1614 = true := by decide +kernel
theorem cen1614 : CenterUniqueMin 1614 ∧ DipHyp 1614 ∧ OnePointHyps 1614 :=
  cen_of L1614_ok H1614_ok I1614_ok link1614 cenlink1614

/-! ### `N = 1615` -/

def pL1615 : Prm := ⟨82, 40, 39, 1617, 11, 18446744073709551616, 117169476512398967, 117169476512398967⟩
def pH1615 : Prm := ⟨80, 37, 40, 1617, 11, 18446744073709551616, 117170576024026743, 117170576024026743⟩
def pI1615 : Prm := ⟨67, 33, 31, 1617, 11, 18446744073709551616, 117169476512398967, 117170576024026743⟩
noncomputable def L1615_cp1 : Nat × Nat := t7val% (fastRun pL1615 1 1141 (init pL1615) (init pL1615))
theorem L1615_seg1 : segOK pL1615 1 1141 (init pL1615) (init pL1615) L1615_cp1.1 L1615_cp1.2 = true := by
  decide +kernel
theorem L1615_fin : (prmOK pL1615 1615 && ptTest pL1615 (runFrom pL1615 (fmask pL1615) (cmask pL1615) (hmask pL1615) 1142 473 (true, L1615_cp1.1, L1615_cp1.2)) 1615 808 false) = true := by
  decide +kernel
theorem L1615_ok : RunOK pL1615 1615 (runFrom pL1615 (fmask pL1615) (cmask pL1615) (hmask pL1615) 1142 473 (true, L1615_cp1.1, L1615_cp1.2)) ∧ ptTest pL1615 (runFrom pL1615 (fmask pL1615) (cmask pL1615) (hmask pL1615) 1142 473 (true, L1615_cp1.1, L1615_cp1.2)) 1615 808 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1615_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1615_fin) true) L1615_seg1) (by decide) rfl L1615_fin ptTest_fst
noncomputable def H1615_cp1 : Nat × Nat := t7val% (fastRun pH1615 1 1141 (init pH1615) (init pH1615))
theorem H1615_seg1 : segOK pH1615 1 1141 (init pH1615) (init pH1615) H1615_cp1.1 H1615_cp1.2 = true := by
  decide +kernel
theorem H1615_fin : (prmOK pH1615 1615 && ptTest pH1615 (runFrom pH1615 (fmask pH1615) (cmask pH1615) (hmask pH1615) 1142 473 (true, H1615_cp1.1, H1615_cp1.2)) 1615 808 true) = true := by
  decide +kernel
theorem H1615_ok : RunOK pH1615 1615 (runFrom pH1615 (fmask pH1615) (cmask pH1615) (hmask pH1615) 1142 473 (true, H1615_cp1.1, H1615_cp1.2)) ∧ ptTest pH1615 (runFrom pH1615 (fmask pH1615) (cmask pH1615) (hmask pH1615) 1142 473 (true, H1615_cp1.1, H1615_cp1.2)) 1615 808 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1615_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1615_fin) true) H1615_seg1) (by decide) rfl H1615_fin ptTest_fst
noncomputable def I1615_cp1 : Nat × Nat := t7val% (fastRun pI1615 1 1141 (init pI1615) (init pI1615))
theorem I1615_seg1 : segOK pI1615 1 1141 (init pI1615) (init pI1615) I1615_cp1.1 I1615_cp1.2 = true := by
  decide +kernel
theorem I1615_fin : (prmOK pI1615 1615 && intTest pI1615 (runFrom pI1615 (fmask pI1615) (cmask pI1615) (hmask pI1615) 1142 473 (true, I1615_cp1.1, I1615_cp1.2)) 1615 21 false) = true := by
  decide +kernel
theorem I1615_ok : RunOK pI1615 1615 (runFrom pI1615 (fmask pI1615) (cmask pI1615) (hmask pI1615) 1142 473 (true, I1615_cp1.1, I1615_cp1.2)) ∧ intTest pI1615 (runFrom pI1615 (fmask pI1615) (cmask pI1615) (hmask pI1615) 1142 473 (true, I1615_cp1.1, I1615_cp1.2)) 1615 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1615_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1615_fin) true) I1615_seg1) (by decide) rfl I1615_fin intTest_fst
theorem link1615 : linkOK pL1615 pH1615 pI1615 = true := by decide +kernel
theorem cvx1615 : ConvexBetweenHumps 1615 :=
  cvx_of L1615_ok H1615_ok I1615_ok link1615 (by decide)

/-! ### `N = 1616` -/

def pL1616 : Prm := ⟨80, 37, 40, 1618, 11, 18446744073709551616, 117110305572044799, 117110305572044799⟩
def pH1616 : Prm := ⟨80, 37, 40, 1618, 11, 18446744073709551616, 117111405083672575, 117111405083672575⟩
def pI1616 : Prm := ⟨67, 33, 31, 1618, 11, 18446744073709551616, 117110305572044799, 117111405083672575⟩
noncomputable def L1616_cp1 : Nat × Nat := t7val% (fastRun pL1616 1 1142 (init pL1616) (init pL1616))
theorem L1616_seg1 : segOK pL1616 1 1142 (init pL1616) (init pL1616) L1616_cp1.1 L1616_cp1.2 = true := by
  decide +kernel
theorem L1616_fin : (prmOK pL1616 1616 && ptTest pL1616 (runFrom pL1616 (fmask pL1616) (cmask pL1616) (hmask pL1616) 1143 473 (true, L1616_cp1.1, L1616_cp1.2)) 1616 808 false) = true := by
  decide +kernel
theorem L1616_ok : RunOK pL1616 1616 (runFrom pL1616 (fmask pL1616) (cmask pL1616) (hmask pL1616) 1143 473 (true, L1616_cp1.1, L1616_cp1.2)) ∧ ptTest pL1616 (runFrom pL1616 (fmask pL1616) (cmask pL1616) (hmask pL1616) 1143 473 (true, L1616_cp1.1, L1616_cp1.2)) 1616 808 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1616_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1616_fin) true) L1616_seg1) (by decide) rfl L1616_fin ptTest_fst
noncomputable def H1616_cp1 : Nat × Nat := t7val% (fastRun pH1616 1 1142 (init pH1616) (init pH1616))
theorem H1616_seg1 : segOK pH1616 1 1142 (init pH1616) (init pH1616) H1616_cp1.1 H1616_cp1.2 = true := by
  decide +kernel
theorem H1616_fin : (prmOK pH1616 1616 && ptTest pH1616 (runFrom pH1616 (fmask pH1616) (cmask pH1616) (hmask pH1616) 1143 473 (true, H1616_cp1.1, H1616_cp1.2)) 1616 808 true) = true := by
  decide +kernel
theorem H1616_ok : RunOK pH1616 1616 (runFrom pH1616 (fmask pH1616) (cmask pH1616) (hmask pH1616) 1143 473 (true, H1616_cp1.1, H1616_cp1.2)) ∧ ptTest pH1616 (runFrom pH1616 (fmask pH1616) (cmask pH1616) (hmask pH1616) 1143 473 (true, H1616_cp1.1, H1616_cp1.2)) 1616 808 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1616_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1616_fin) true) H1616_seg1) (by decide) rfl H1616_fin ptTest_fst
noncomputable def I1616_cp1 : Nat × Nat := t7val% (fastRun pI1616 1 1142 (init pI1616) (init pI1616))
theorem I1616_seg1 : segOK pI1616 1 1142 (init pI1616) (init pI1616) I1616_cp1.1 I1616_cp1.2 = true := by
  decide +kernel
theorem I1616_fin : (prmOK pI1616 1616 && intTest pI1616 (runFrom pI1616 (fmask pI1616) (cmask pI1616) (hmask pI1616) 1143 473 (true, I1616_cp1.1, I1616_cp1.2)) 1616 21 true) = true := by
  decide +kernel
theorem I1616_ok : RunOK pI1616 1616 (runFrom pI1616 (fmask pI1616) (cmask pI1616) (hmask pI1616) 1143 473 (true, I1616_cp1.1, I1616_cp1.2)) ∧ intTest pI1616 (runFrom pI1616 (fmask pI1616) (cmask pI1616) (hmask pI1616) 1143 473 (true, I1616_cp1.1, I1616_cp1.2)) 1616 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1616_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1616_fin) true) I1616_seg1) (by decide) rfl I1616_fin intTest_fst
theorem link1616 : linkOK pL1616 pH1616 pI1616 = true := by decide +kernel
theorem cvx1616 : ConvexBetweenHumps 1616 :=
  cvx_of L1616_ok H1616_ok I1616_ok link1616 (by decide)
theorem cenlink1616 : cenLinkOK pI1616 1616 = true := by decide +kernel
theorem cen1616 : CenterUniqueMin 1616 ∧ DipHyp 1616 ∧ OnePointHyps 1616 :=
  cen_of L1616_ok H1616_ok I1616_ok link1616 cenlink1616

/-! ### `N = 1617` -/

def pL1617 : Prm := ⟨80, 37, 40, 1619, 11, 18446744073709551616, 117051172859726924, 117051172859726924⟩
def pH1617 : Prm := ⟨80, 37, 40, 1619, 11, 18446744073709551616, 117052272371354700, 117052272371354700⟩
def pI1617 : Prm := ⟨67, 33, 31, 1619, 11, 18446744073709551616, 117051172859726924, 117052272371354700⟩
noncomputable def L1617_cp1 : Nat × Nat := t7val% (fastRun pL1617 1 1142 (init pL1617) (init pL1617))
theorem L1617_seg1 : segOK pL1617 1 1142 (init pL1617) (init pL1617) L1617_cp1.1 L1617_cp1.2 = true := by
  decide +kernel
theorem L1617_fin : (prmOK pL1617 1617 && ptTest pL1617 (runFrom pL1617 (fmask pL1617) (cmask pL1617) (hmask pL1617) 1143 474 (true, L1617_cp1.1, L1617_cp1.2)) 1617 809 false) = true := by
  decide +kernel
theorem L1617_ok : RunOK pL1617 1617 (runFrom pL1617 (fmask pL1617) (cmask pL1617) (hmask pL1617) 1143 474 (true, L1617_cp1.1, L1617_cp1.2)) ∧ ptTest pL1617 (runFrom pL1617 (fmask pL1617) (cmask pL1617) (hmask pL1617) 1143 474 (true, L1617_cp1.1, L1617_cp1.2)) 1617 809 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1617_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1617_fin) true) L1617_seg1) (by decide) rfl L1617_fin ptTest_fst
noncomputable def H1617_cp1 : Nat × Nat := t7val% (fastRun pH1617 1 1142 (init pH1617) (init pH1617))
theorem H1617_seg1 : segOK pH1617 1 1142 (init pH1617) (init pH1617) H1617_cp1.1 H1617_cp1.2 = true := by
  decide +kernel
theorem H1617_fin : (prmOK pH1617 1617 && ptTest pH1617 (runFrom pH1617 (fmask pH1617) (cmask pH1617) (hmask pH1617) 1143 474 (true, H1617_cp1.1, H1617_cp1.2)) 1617 809 true) = true := by
  decide +kernel
theorem H1617_ok : RunOK pH1617 1617 (runFrom pH1617 (fmask pH1617) (cmask pH1617) (hmask pH1617) 1143 474 (true, H1617_cp1.1, H1617_cp1.2)) ∧ ptTest pH1617 (runFrom pH1617 (fmask pH1617) (cmask pH1617) (hmask pH1617) 1143 474 (true, H1617_cp1.1, H1617_cp1.2)) 1617 809 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1617_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1617_fin) true) H1617_seg1) (by decide) rfl H1617_fin ptTest_fst
noncomputable def I1617_cp1 : Nat × Nat := t7val% (fastRun pI1617 1 1142 (init pI1617) (init pI1617))
theorem I1617_seg1 : segOK pI1617 1 1142 (init pI1617) (init pI1617) I1617_cp1.1 I1617_cp1.2 = true := by
  decide +kernel
theorem I1617_fin : (prmOK pI1617 1617 && intTest pI1617 (runFrom pI1617 (fmask pI1617) (cmask pI1617) (hmask pI1617) 1143 474 (true, I1617_cp1.1, I1617_cp1.2)) 1617 21 false) = true := by
  decide +kernel
theorem I1617_ok : RunOK pI1617 1617 (runFrom pI1617 (fmask pI1617) (cmask pI1617) (hmask pI1617) 1143 474 (true, I1617_cp1.1, I1617_cp1.2)) ∧ intTest pI1617 (runFrom pI1617 (fmask pI1617) (cmask pI1617) (hmask pI1617) 1143 474 (true, I1617_cp1.1, I1617_cp1.2)) 1617 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1617_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1617_fin) true) I1617_seg1) (by decide) rfl I1617_fin intTest_fst
theorem link1617 : linkOK pL1617 pH1617 pI1617 = true := by decide +kernel
theorem cvx1617 : ConvexBetweenHumps 1617 :=
  cvx_of L1617_ok H1617_ok I1617_ok link1617 (by decide)

/-! ### `N = 1618` -/

def pL1618 : Prm := ⟨82, 40, 39, 1620, 11, 18446744073709551616, 116992131671058898, 116992131671058898⟩
def pH1618 : Prm := ⟨80, 37, 40, 1620, 11, 18446744073709551616, 116993231182686674, 116993231182686674⟩
def pI1618 : Prm := ⟨68, 33, 32, 1620, 11, 18446744073709551616, 116992131671058898, 116993231182686674⟩
noncomputable def L1618_cp1 : Nat × Nat := t7val% (fastRun pL1618 1 1143 (init pL1618) (init pL1618))
theorem L1618_seg1 : segOK pL1618 1 1143 (init pL1618) (init pL1618) L1618_cp1.1 L1618_cp1.2 = true := by
  decide +kernel
theorem L1618_fin : (prmOK pL1618 1618 && ptTest pL1618 (runFrom pL1618 (fmask pL1618) (cmask pL1618) (hmask pL1618) 1144 474 (true, L1618_cp1.1, L1618_cp1.2)) 1618 809 false) = true := by
  decide +kernel
theorem L1618_ok : RunOK pL1618 1618 (runFrom pL1618 (fmask pL1618) (cmask pL1618) (hmask pL1618) 1144 474 (true, L1618_cp1.1, L1618_cp1.2)) ∧ ptTest pL1618 (runFrom pL1618 (fmask pL1618) (cmask pL1618) (hmask pL1618) 1144 474 (true, L1618_cp1.1, L1618_cp1.2)) 1618 809 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1618_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1618_fin) true) L1618_seg1) (by decide) rfl L1618_fin ptTest_fst
noncomputable def H1618_cp1 : Nat × Nat := t7val% (fastRun pH1618 1 1143 (init pH1618) (init pH1618))
theorem H1618_seg1 : segOK pH1618 1 1143 (init pH1618) (init pH1618) H1618_cp1.1 H1618_cp1.2 = true := by
  decide +kernel
theorem H1618_fin : (prmOK pH1618 1618 && ptTest pH1618 (runFrom pH1618 (fmask pH1618) (cmask pH1618) (hmask pH1618) 1144 474 (true, H1618_cp1.1, H1618_cp1.2)) 1618 809 true) = true := by
  decide +kernel
theorem H1618_ok : RunOK pH1618 1618 (runFrom pH1618 (fmask pH1618) (cmask pH1618) (hmask pH1618) 1144 474 (true, H1618_cp1.1, H1618_cp1.2)) ∧ ptTest pH1618 (runFrom pH1618 (fmask pH1618) (cmask pH1618) (hmask pH1618) 1144 474 (true, H1618_cp1.1, H1618_cp1.2)) 1618 809 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1618_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1618_fin) true) H1618_seg1) (by decide) rfl H1618_fin ptTest_fst
noncomputable def I1618_cp1 : Nat × Nat := t7val% (fastRun pI1618 1 1143 (init pI1618) (init pI1618))
theorem I1618_seg1 : segOK pI1618 1 1143 (init pI1618) (init pI1618) I1618_cp1.1 I1618_cp1.2 = true := by
  decide +kernel
theorem I1618_fin : (prmOK pI1618 1618 && intTest pI1618 (runFrom pI1618 (fmask pI1618) (cmask pI1618) (hmask pI1618) 1144 474 (true, I1618_cp1.1, I1618_cp1.2)) 1618 21 true) = true := by
  decide +kernel
theorem I1618_ok : RunOK pI1618 1618 (runFrom pI1618 (fmask pI1618) (cmask pI1618) (hmask pI1618) 1144 474 (true, I1618_cp1.1, I1618_cp1.2)) ∧ intTest pI1618 (runFrom pI1618 (fmask pI1618) (cmask pI1618) (hmask pI1618) 1144 474 (true, I1618_cp1.1, I1618_cp1.2)) 1618 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1618_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1618_fin) true) I1618_seg1) (by decide) rfl I1618_fin intTest_fst
theorem link1618 : linkOK pL1618 pH1618 pI1618 = true := by decide +kernel
theorem cvx1618 : ConvexBetweenHumps 1618 :=
  cvx_of L1618_ok H1618_ok I1618_ok link1618 (by decide)
theorem cenlink1618 : cenLinkOK pI1618 1618 = true := by decide +kernel
theorem cen1618 : CenterUniqueMin 1618 ∧ DipHyp 1618 ∧ OnePointHyps 1618 :=
  cen_of L1618_ok H1618_ok I1618_ok link1618 cenlink1618

/-! ### `N = 1619` -/

def pL1619 : Prm := ⟨80, 37, 40, 1621, 11, 18446744073709551616, 116933128590763138, 116933128590763138⟩
def pH1619 : Prm := ⟨80, 37, 40, 1621, 11, 18446744073709551616, 116934228102390914, 116934228102390914⟩
def pI1619 : Prm := ⟨67, 33, 31, 1621, 11, 18446744073709551616, 116933128590763138, 116934228102390914⟩
noncomputable def L1619_cp1 : Nat × Nat := t7val% (fastRun pL1619 1 1144 (init pL1619) (init pL1619))
theorem L1619_seg1 : segOK pL1619 1 1144 (init pL1619) (init pL1619) L1619_cp1.1 L1619_cp1.2 = true := by
  decide +kernel
theorem L1619_fin : (prmOK pL1619 1619 && ptTest pL1619 (runFrom pL1619 (fmask pL1619) (cmask pL1619) (hmask pL1619) 1145 474 (true, L1619_cp1.1, L1619_cp1.2)) 1619 810 false) = true := by
  decide +kernel
theorem L1619_ok : RunOK pL1619 1619 (runFrom pL1619 (fmask pL1619) (cmask pL1619) (hmask pL1619) 1145 474 (true, L1619_cp1.1, L1619_cp1.2)) ∧ ptTest pL1619 (runFrom pL1619 (fmask pL1619) (cmask pL1619) (hmask pL1619) 1145 474 (true, L1619_cp1.1, L1619_cp1.2)) 1619 810 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1619_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1619_fin) true) L1619_seg1) (by decide) rfl L1619_fin ptTest_fst
noncomputable def H1619_cp1 : Nat × Nat := t7val% (fastRun pH1619 1 1144 (init pH1619) (init pH1619))
theorem H1619_seg1 : segOK pH1619 1 1144 (init pH1619) (init pH1619) H1619_cp1.1 H1619_cp1.2 = true := by
  decide +kernel
theorem H1619_fin : (prmOK pH1619 1619 && ptTest pH1619 (runFrom pH1619 (fmask pH1619) (cmask pH1619) (hmask pH1619) 1145 474 (true, H1619_cp1.1, H1619_cp1.2)) 1619 810 true) = true := by
  decide +kernel
theorem H1619_ok : RunOK pH1619 1619 (runFrom pH1619 (fmask pH1619) (cmask pH1619) (hmask pH1619) 1145 474 (true, H1619_cp1.1, H1619_cp1.2)) ∧ ptTest pH1619 (runFrom pH1619 (fmask pH1619) (cmask pH1619) (hmask pH1619) 1145 474 (true, H1619_cp1.1, H1619_cp1.2)) 1619 810 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1619_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1619_fin) true) H1619_seg1) (by decide) rfl H1619_fin ptTest_fst
noncomputable def I1619_cp1 : Nat × Nat := t7val% (fastRun pI1619 1 1144 (init pI1619) (init pI1619))
theorem I1619_seg1 : segOK pI1619 1 1144 (init pI1619) (init pI1619) I1619_cp1.1 I1619_cp1.2 = true := by
  decide +kernel
theorem I1619_fin : (prmOK pI1619 1619 && intTest pI1619 (runFrom pI1619 (fmask pI1619) (cmask pI1619) (hmask pI1619) 1145 474 (true, I1619_cp1.1, I1619_cp1.2)) 1619 21 false) = true := by
  decide +kernel
theorem I1619_ok : RunOK pI1619 1619 (runFrom pI1619 (fmask pI1619) (cmask pI1619) (hmask pI1619) 1145 474 (true, I1619_cp1.1, I1619_cp1.2)) ∧ intTest pI1619 (runFrom pI1619 (fmask pI1619) (cmask pI1619) (hmask pI1619) 1145 474 (true, I1619_cp1.1, I1619_cp1.2)) 1619 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1619_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1619_fin) true) I1619_seg1) (by decide) rfl I1619_fin intTest_fst
theorem link1619 : linkOK pL1619 pH1619 pI1619 = true := by decide +kernel
theorem cvx1619 : ConvexBetweenHumps 1619 :=
  cvx_of L1619_ok H1619_ok I1619_ok link1619 (by decide)

/-! ### `N = 1620` -/

def pL1620 : Prm := ⟨80, 37, 40, 1622, 11, 18446744073709551616, 116874216714047770, 116874216714047770⟩
def pH1620 : Prm := ⟨80, 37, 40, 1622, 11, 18446744073709551616, 116875316225675546, 116875316225675546⟩
def pI1620 : Prm := ⟨67, 33, 31, 1622, 11, 18446744073709551616, 116874216714047770, 116875316225675546⟩
noncomputable def L1620_cp1 : Nat × Nat := t7val% (fastRun pL1620 1 1145 (init pL1620) (init pL1620))
theorem L1620_seg1 : segOK pL1620 1 1145 (init pL1620) (init pL1620) L1620_cp1.1 L1620_cp1.2 = true := by
  decide +kernel
theorem L1620_fin : (prmOK pL1620 1620 && ptTest pL1620 (runFrom pL1620 (fmask pL1620) (cmask pL1620) (hmask pL1620) 1146 474 (true, L1620_cp1.1, L1620_cp1.2)) 1620 810 false) = true := by
  decide +kernel
theorem L1620_ok : RunOK pL1620 1620 (runFrom pL1620 (fmask pL1620) (cmask pL1620) (hmask pL1620) 1146 474 (true, L1620_cp1.1, L1620_cp1.2)) ∧ ptTest pL1620 (runFrom pL1620 (fmask pL1620) (cmask pL1620) (hmask pL1620) 1146 474 (true, L1620_cp1.1, L1620_cp1.2)) 1620 810 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1620_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1620_fin) true) L1620_seg1) (by decide) rfl L1620_fin ptTest_fst
noncomputable def H1620_cp1 : Nat × Nat := t7val% (fastRun pH1620 1 1145 (init pH1620) (init pH1620))
theorem H1620_seg1 : segOK pH1620 1 1145 (init pH1620) (init pH1620) H1620_cp1.1 H1620_cp1.2 = true := by
  decide +kernel
theorem H1620_fin : (prmOK pH1620 1620 && ptTest pH1620 (runFrom pH1620 (fmask pH1620) (cmask pH1620) (hmask pH1620) 1146 474 (true, H1620_cp1.1, H1620_cp1.2)) 1620 810 true) = true := by
  decide +kernel
theorem H1620_ok : RunOK pH1620 1620 (runFrom pH1620 (fmask pH1620) (cmask pH1620) (hmask pH1620) 1146 474 (true, H1620_cp1.1, H1620_cp1.2)) ∧ ptTest pH1620 (runFrom pH1620 (fmask pH1620) (cmask pH1620) (hmask pH1620) 1146 474 (true, H1620_cp1.1, H1620_cp1.2)) 1620 810 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1620_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1620_fin) true) H1620_seg1) (by decide) rfl H1620_fin ptTest_fst
noncomputable def I1620_cp1 : Nat × Nat := t7val% (fastRun pI1620 1 1145 (init pI1620) (init pI1620))
theorem I1620_seg1 : segOK pI1620 1 1145 (init pI1620) (init pI1620) I1620_cp1.1 I1620_cp1.2 = true := by
  decide +kernel
theorem I1620_fin : (prmOK pI1620 1620 && intTest pI1620 (runFrom pI1620 (fmask pI1620) (cmask pI1620) (hmask pI1620) 1146 474 (true, I1620_cp1.1, I1620_cp1.2)) 1620 21 true) = true := by
  decide +kernel
theorem I1620_ok : RunOK pI1620 1620 (runFrom pI1620 (fmask pI1620) (cmask pI1620) (hmask pI1620) 1146 474 (true, I1620_cp1.1, I1620_cp1.2)) ∧ intTest pI1620 (runFrom pI1620 (fmask pI1620) (cmask pI1620) (hmask pI1620) 1146 474 (true, I1620_cp1.1, I1620_cp1.2)) 1620 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1620_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1620_fin) true) I1620_seg1) (by decide) rfl I1620_fin intTest_fst
theorem link1620 : linkOK pL1620 pH1620 pI1620 = true := by decide +kernel
theorem cvx1620 : ConvexBetweenHumps 1620 :=
  cvx_of L1620_ok H1620_ok I1620_ok link1620 (by decide)
theorem cenlink1620 : cenLinkOK pI1620 1620 = true := by decide +kernel
theorem cen1620 : CenterUniqueMin 1620 ∧ DipHyp 1620 ∧ OnePointHyps 1620 :=
  cen_of L1620_ok H1620_ok I1620_ok link1620 cenlink1620

/-! ### `N = 1621` -/

def pL1621 : Prm := ⟨80, 37, 40, 1623, 11, 18446744073709551616, 116815342826538701, 116815342826538701⟩
def pH1621 : Prm := ⟨80, 37, 40, 1623, 11, 18446744073709551616, 116816442338166477, 116816442338166477⟩
def pI1621 : Prm := ⟨68, 33, 32, 1623, 11, 18446744073709551616, 116815342826538701, 116816442338166477⟩
noncomputable def L1621_cp1 : Nat × Nat := t7val% (fastRun pL1621 1 1145 (init pL1621) (init pL1621))
theorem L1621_seg1 : segOK pL1621 1 1145 (init pL1621) (init pL1621) L1621_cp1.1 L1621_cp1.2 = true := by
  decide +kernel
theorem L1621_fin : (prmOK pL1621 1621 && ptTest pL1621 (runFrom pL1621 (fmask pL1621) (cmask pL1621) (hmask pL1621) 1146 475 (true, L1621_cp1.1, L1621_cp1.2)) 1621 811 false) = true := by
  decide +kernel
theorem L1621_ok : RunOK pL1621 1621 (runFrom pL1621 (fmask pL1621) (cmask pL1621) (hmask pL1621) 1146 475 (true, L1621_cp1.1, L1621_cp1.2)) ∧ ptTest pL1621 (runFrom pL1621 (fmask pL1621) (cmask pL1621) (hmask pL1621) 1146 475 (true, L1621_cp1.1, L1621_cp1.2)) 1621 811 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1621_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1621_fin) true) L1621_seg1) (by decide) rfl L1621_fin ptTest_fst
noncomputable def H1621_cp1 : Nat × Nat := t7val% (fastRun pH1621 1 1145 (init pH1621) (init pH1621))
theorem H1621_seg1 : segOK pH1621 1 1145 (init pH1621) (init pH1621) H1621_cp1.1 H1621_cp1.2 = true := by
  decide +kernel
theorem H1621_fin : (prmOK pH1621 1621 && ptTest pH1621 (runFrom pH1621 (fmask pH1621) (cmask pH1621) (hmask pH1621) 1146 475 (true, H1621_cp1.1, H1621_cp1.2)) 1621 811 true) = true := by
  decide +kernel
theorem H1621_ok : RunOK pH1621 1621 (runFrom pH1621 (fmask pH1621) (cmask pH1621) (hmask pH1621) 1146 475 (true, H1621_cp1.1, H1621_cp1.2)) ∧ ptTest pH1621 (runFrom pH1621 (fmask pH1621) (cmask pH1621) (hmask pH1621) 1146 475 (true, H1621_cp1.1, H1621_cp1.2)) 1621 811 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1621_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1621_fin) true) H1621_seg1) (by decide) rfl H1621_fin ptTest_fst
noncomputable def I1621_cp1 : Nat × Nat := t7val% (fastRun pI1621 1 1145 (init pI1621) (init pI1621))
theorem I1621_seg1 : segOK pI1621 1 1145 (init pI1621) (init pI1621) I1621_cp1.1 I1621_cp1.2 = true := by
  decide +kernel
theorem I1621_fin : (prmOK pI1621 1621 && intTest pI1621 (runFrom pI1621 (fmask pI1621) (cmask pI1621) (hmask pI1621) 1146 475 (true, I1621_cp1.1, I1621_cp1.2)) 1621 21 false) = true := by
  decide +kernel
theorem I1621_ok : RunOK pI1621 1621 (runFrom pI1621 (fmask pI1621) (cmask pI1621) (hmask pI1621) 1146 475 (true, I1621_cp1.1, I1621_cp1.2)) ∧ intTest pI1621 (runFrom pI1621 (fmask pI1621) (cmask pI1621) (hmask pI1621) 1146 475 (true, I1621_cp1.1, I1621_cp1.2)) 1621 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1621_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1621_fin) true) I1621_seg1) (by decide) rfl I1621_fin intTest_fst
theorem link1621 : linkOK pL1621 pH1621 pI1621 = true := by decide +kernel
theorem cvx1621 : ConvexBetweenHumps 1621 :=
  cvx_of L1621_ok H1621_ok I1621_ok link1621 (by decide)

/-! ### `N = 1622` -/

def pL1622 : Prm := ⟨80, 37, 40, 1624, 11, 18446744073709551616, 116756559824090094, 116756559824090094⟩
def pH1622 : Prm := ⟨80, 37, 40, 1624, 11, 18446744073709551616, 116757659335717870, 116757659335717870⟩
def pI1622 : Prm := ⟨67, 33, 31, 1624, 11, 18446744073709551616, 116756559824090094, 116757659335717870⟩
noncomputable def L1622_cp1 : Nat × Nat := t7val% (fastRun pL1622 1 1146 (init pL1622) (init pL1622))
theorem L1622_seg1 : segOK pL1622 1 1146 (init pL1622) (init pL1622) L1622_cp1.1 L1622_cp1.2 = true := by
  decide +kernel
theorem L1622_fin : (prmOK pL1622 1622 && ptTest pL1622 (runFrom pL1622 (fmask pL1622) (cmask pL1622) (hmask pL1622) 1147 475 (true, L1622_cp1.1, L1622_cp1.2)) 1622 811 false) = true := by
  decide +kernel
theorem L1622_ok : RunOK pL1622 1622 (runFrom pL1622 (fmask pL1622) (cmask pL1622) (hmask pL1622) 1147 475 (true, L1622_cp1.1, L1622_cp1.2)) ∧ ptTest pL1622 (runFrom pL1622 (fmask pL1622) (cmask pL1622) (hmask pL1622) 1147 475 (true, L1622_cp1.1, L1622_cp1.2)) 1622 811 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1622_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1622_fin) true) L1622_seg1) (by decide) rfl L1622_fin ptTest_fst
noncomputable def H1622_cp1 : Nat × Nat := t7val% (fastRun pH1622 1 1146 (init pH1622) (init pH1622))
theorem H1622_seg1 : segOK pH1622 1 1146 (init pH1622) (init pH1622) H1622_cp1.1 H1622_cp1.2 = true := by
  decide +kernel
theorem H1622_fin : (prmOK pH1622 1622 && ptTest pH1622 (runFrom pH1622 (fmask pH1622) (cmask pH1622) (hmask pH1622) 1147 475 (true, H1622_cp1.1, H1622_cp1.2)) 1622 811 true) = true := by
  decide +kernel
theorem H1622_ok : RunOK pH1622 1622 (runFrom pH1622 (fmask pH1622) (cmask pH1622) (hmask pH1622) 1147 475 (true, H1622_cp1.1, H1622_cp1.2)) ∧ ptTest pH1622 (runFrom pH1622 (fmask pH1622) (cmask pH1622) (hmask pH1622) 1147 475 (true, H1622_cp1.1, H1622_cp1.2)) 1622 811 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1622_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1622_fin) true) H1622_seg1) (by decide) rfl H1622_fin ptTest_fst
noncomputable def I1622_cp1 : Nat × Nat := t7val% (fastRun pI1622 1 1146 (init pI1622) (init pI1622))
theorem I1622_seg1 : segOK pI1622 1 1146 (init pI1622) (init pI1622) I1622_cp1.1 I1622_cp1.2 = true := by
  decide +kernel
theorem I1622_fin : (prmOK pI1622 1622 && intTest pI1622 (runFrom pI1622 (fmask pI1622) (cmask pI1622) (hmask pI1622) 1147 475 (true, I1622_cp1.1, I1622_cp1.2)) 1622 21 true) = true := by
  decide +kernel
theorem I1622_ok : RunOK pI1622 1622 (runFrom pI1622 (fmask pI1622) (cmask pI1622) (hmask pI1622) 1147 475 (true, I1622_cp1.1, I1622_cp1.2)) ∧ intTest pI1622 (runFrom pI1622 (fmask pI1622) (cmask pI1622) (hmask pI1622) 1147 475 (true, I1622_cp1.1, I1622_cp1.2)) 1622 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1622_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1622_fin) true) I1622_seg1) (by decide) rfl I1622_fin intTest_fst
theorem link1622 : linkOK pL1622 pH1622 pI1622 = true := by decide +kernel
theorem cvx1622 : ConvexBetweenHumps 1622 :=
  cvx_of L1622_ok H1622_ok I1622_ok link1622 (by decide)
theorem cenlink1622 : cenLinkOK pI1622 1622 = true := by decide +kernel
theorem cen1622 : CenterUniqueMin 1622 ∧ DipHyp 1622 ∧ OnePointHyps 1622 :=
  cen_of L1622_ok H1622_ok I1622_ok link1622 cenlink1622

/-! ### `N = 1623` -/

def pL1623 : Prm := ⟨82, 40, 39, 1625, 11, 18446744073709551616, 116697814692142988, 116697814692142988⟩
def pH1623 : Prm := ⟨80, 37, 40, 1625, 11, 18446744073709551616, 116698914203770764, 116698914203770764⟩
def pI1623 : Prm := ⟨68, 33, 32, 1625, 11, 18446744073709551616, 116697814692142988, 116698914203770764⟩
noncomputable def L1623_cp1 : Nat × Nat := t7val% (fastRun pL1623 1 936 (init pL1623) (init pL1623))
theorem L1623_seg1 : segOK pL1623 1 936 (init pL1623) (init pL1623) L1623_cp1.1 L1623_cp1.2 = true := by
  decide +kernel
noncomputable def L1623_cp2 : Nat × Nat := t7val% (fastRun pL1623 1 1324 (init pL1623) (init pL1623))
theorem L1623_seg2 : segOK pL1623 937 388 L1623_cp1.1 L1623_cp1.2 L1623_cp2.1 L1623_cp2.2 = true := by
  decide +kernel
theorem L1623_fin : (prmOK pL1623 1623 && ptTest pL1623 (runFrom pL1623 (fmask pL1623) (cmask pL1623) (hmask pL1623) 1325 298 (true, L1623_cp2.1, L1623_cp2.2)) 1623 812 false) = true := by
  decide +kernel
theorem L1623_ok : RunOK pL1623 1623 (runFrom pL1623 (fmask pL1623) (cmask pL1623) (hmask pL1623) 1325 298 (true, L1623_cp2.1, L1623_cp2.2)) ∧ ptTest pL1623 (runFrom pL1623 (fmask pL1623) (cmask pL1623) (hmask pL1623) 1325 298 (true, L1623_cp2.1, L1623_cp2.2)) 1623 812 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1623_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1623_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1623_fin) true) L1623_seg1) L1623_seg2) (by decide) rfl L1623_fin ptTest_fst
noncomputable def H1623_cp1 : Nat × Nat := t7val% (fastRun pH1623 1 1147 (init pH1623) (init pH1623))
theorem H1623_seg1 : segOK pH1623 1 1147 (init pH1623) (init pH1623) H1623_cp1.1 H1623_cp1.2 = true := by
  decide +kernel
theorem H1623_fin : (prmOK pH1623 1623 && ptTest pH1623 (runFrom pH1623 (fmask pH1623) (cmask pH1623) (hmask pH1623) 1148 475 (true, H1623_cp1.1, H1623_cp1.2)) 1623 812 true) = true := by
  decide +kernel
theorem H1623_ok : RunOK pH1623 1623 (runFrom pH1623 (fmask pH1623) (cmask pH1623) (hmask pH1623) 1148 475 (true, H1623_cp1.1, H1623_cp1.2)) ∧ ptTest pH1623 (runFrom pH1623 (fmask pH1623) (cmask pH1623) (hmask pH1623) 1148 475 (true, H1623_cp1.1, H1623_cp1.2)) 1623 812 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1623_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1623_fin) true) H1623_seg1) (by decide) rfl H1623_fin ptTest_fst
noncomputable def I1623_cp1 : Nat × Nat := t7val% (fastRun pI1623 1 1147 (init pI1623) (init pI1623))
theorem I1623_seg1 : segOK pI1623 1 1147 (init pI1623) (init pI1623) I1623_cp1.1 I1623_cp1.2 = true := by
  decide +kernel
theorem I1623_fin : (prmOK pI1623 1623 && intTest pI1623 (runFrom pI1623 (fmask pI1623) (cmask pI1623) (hmask pI1623) 1148 475 (true, I1623_cp1.1, I1623_cp1.2)) 1623 21 false) = true := by
  decide +kernel
theorem I1623_ok : RunOK pI1623 1623 (runFrom pI1623 (fmask pI1623) (cmask pI1623) (hmask pI1623) 1148 475 (true, I1623_cp1.1, I1623_cp1.2)) ∧ intTest pI1623 (runFrom pI1623 (fmask pI1623) (cmask pI1623) (hmask pI1623) 1148 475 (true, I1623_cp1.1, I1623_cp1.2)) 1623 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1623_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1623_fin) true) I1623_seg1) (by decide) rfl I1623_fin intTest_fst
theorem link1623 : linkOK pL1623 pH1623 pI1623 = true := by decide +kernel
theorem cvx1623 : ConvexBetweenHumps 1623 :=
  cvx_of L1623_ok H1623_ok I1623_ok link1623 (by decide)

/-! ### The range -/

theorem cvx_1609_1623 {N : ℕ} (h1 : 1609 ≤ N) (h2 : N ≤ 1623) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1615
  · by_cases h4 : N ≤ 1611
    · by_cases h6 : N ≤ 1609
      · obtain rfl : N = 1609 := by omega
        exact cvx1609
      · by_cases h8 : N ≤ 1610
        · obtain rfl : N = 1610 := by omega
          exact cvx1610
        · obtain rfl : N = 1611 := by omega
          exact cvx1611
    · by_cases h6 : N ≤ 1613
      · by_cases h8 : N ≤ 1612
        · obtain rfl : N = 1612 := by omega
          exact cvx1612
        · obtain rfl : N = 1613 := by omega
          exact cvx1613
      · by_cases h8 : N ≤ 1614
        · obtain rfl : N = 1614 := by omega
          exact cvx1614
        · obtain rfl : N = 1615 := by omega
          exact cvx1615
  · by_cases h4 : N ≤ 1619
    · by_cases h6 : N ≤ 1617
      · by_cases h8 : N ≤ 1616
        · obtain rfl : N = 1616 := by omega
          exact cvx1616
        · obtain rfl : N = 1617 := by omega
          exact cvx1617
      · by_cases h8 : N ≤ 1618
        · obtain rfl : N = 1618 := by omega
          exact cvx1618
        · obtain rfl : N = 1619 := by omega
          exact cvx1619
    · by_cases h6 : N ≤ 1621
      · by_cases h8 : N ≤ 1620
        · obtain rfl : N = 1620 := by omega
          exact cvx1620
        · obtain rfl : N = 1621 := by omega
          exact cvx1621
      · by_cases h8 : N ≤ 1622
        · obtain rfl : N = 1622 := by omega
          exact cvx1622
        · obtain rfl : N = 1623 := by omega
          exact cvx1623

theorem cen_1609_1623 {N : ℕ} (h1 : 1609 ≤ N) (h2 : N ≤ 1623) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1614
  · by_cases h4 : N ≤ 1610
    · obtain rfl : N = 1610 := by omega
      exact cen1610
    · by_cases h6 : N ≤ 1612
      · obtain rfl : N = 1612 := by omega
        exact cen1612
      · obtain rfl : N = 1614 := by omega
        exact cen1614
  · by_cases h4 : N ≤ 1618
    · by_cases h6 : N ≤ 1616
      · obtain rfl : N = 1616 := by omega
        exact cen1616
      · obtain rfl : N = 1618 := by omega
        exact cen1618
    · by_cases h6 : N ≤ 1620
      · obtain rfl : N = 1620 := by omega
        exact cen1620
      · obtain rfl : N = 1622 := by omega
        exact cen1622

end Kagey131.PaperD.T7
