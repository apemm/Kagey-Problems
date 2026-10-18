import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1760, …, 1771` (generated)

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

/-! ### `N = 1760` -/

def pL1760 : Prm := ⟨80, 37, 40, 1762, 11, 18446744073709551616, 109215181138382548, 109215181138382548⟩
def pH1760 : Prm := ⟨80, 37, 40, 1762, 11, 18446744073709551616, 109216280650010324, 109216280650010324⟩
def pI1760 : Prm := ⟨67, 34, 30, 1762, 11, 18446744073709551616, 109215181138382548, 109216280650010324⟩
noncomputable def L1760_cp1 : Nat × Nat := t7val% (fastRun pL1760 1 1015 (init pL1760) (init pL1760))
theorem L1760_seg1 : segOK pL1760 1 1015 (init pL1760) (init pL1760) L1760_cp1.1 L1760_cp1.2 = true := by
  decide +kernel
noncomputable def L1760_cp2 : Nat × Nat := t7val% (fastRun pL1760 1 1436 (init pL1760) (init pL1760))
theorem L1760_seg2 : segOK pL1760 1016 421 L1760_cp1.1 L1760_cp1.2 L1760_cp2.1 L1760_cp2.2 = true := by
  decide +kernel
theorem L1760_fin : (prmOK pL1760 1760 && ptTest pL1760 (runFrom pL1760 (fmask pL1760) (cmask pL1760) (hmask pL1760) 1437 323 (true, L1760_cp2.1, L1760_cp2.2)) 1760 880 false) = true := by
  decide +kernel
theorem L1760_ok : RunOK pL1760 1760 (runFrom pL1760 (fmask pL1760) (cmask pL1760) (hmask pL1760) 1437 323 (true, L1760_cp2.1, L1760_cp2.2)) ∧ ptTest pL1760 (runFrom pL1760 (fmask pL1760) (cmask pL1760) (hmask pL1760) 1437 323 (true, L1760_cp2.1, L1760_cp2.2)) 1760 880 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1760_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1760_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1760_fin) true) L1760_seg1) L1760_seg2) (by decide) rfl L1760_fin ptTest_fst
noncomputable def H1760_cp1 : Nat × Nat := t7val% (fastRun pH1760 1 1015 (init pH1760) (init pH1760))
theorem H1760_seg1 : segOK pH1760 1 1015 (init pH1760) (init pH1760) H1760_cp1.1 H1760_cp1.2 = true := by
  decide +kernel
noncomputable def H1760_cp2 : Nat × Nat := t7val% (fastRun pH1760 1 1436 (init pH1760) (init pH1760))
theorem H1760_seg2 : segOK pH1760 1016 421 H1760_cp1.1 H1760_cp1.2 H1760_cp2.1 H1760_cp2.2 = true := by
  decide +kernel
theorem H1760_fin : (prmOK pH1760 1760 && ptTest pH1760 (runFrom pH1760 (fmask pH1760) (cmask pH1760) (hmask pH1760) 1437 323 (true, H1760_cp2.1, H1760_cp2.2)) 1760 880 true) = true := by
  decide +kernel
theorem H1760_ok : RunOK pH1760 1760 (runFrom pH1760 (fmask pH1760) (cmask pH1760) (hmask pH1760) 1437 323 (true, H1760_cp2.1, H1760_cp2.2)) ∧ ptTest pH1760 (runFrom pH1760 (fmask pH1760) (cmask pH1760) (hmask pH1760) 1437 323 (true, H1760_cp2.1, H1760_cp2.2)) 1760 880 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1760_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1760_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1760_fin) true) H1760_seg1) H1760_seg2) (by decide) rfl H1760_fin ptTest_fst
noncomputable def I1760_cp1 : Nat × Nat := t7val% (fastRun pI1760 1 1244 (init pI1760) (init pI1760))
theorem I1760_seg1 : segOK pI1760 1 1244 (init pI1760) (init pI1760) I1760_cp1.1 I1760_cp1.2 = true := by
  decide +kernel
theorem I1760_fin : (prmOK pI1760 1760 && intTest pI1760 (runFrom pI1760 (fmask pI1760) (cmask pI1760) (hmask pI1760) 1245 515 (true, I1760_cp1.1, I1760_cp1.2)) 1760 21 true) = true := by
  decide +kernel
theorem I1760_ok : RunOK pI1760 1760 (runFrom pI1760 (fmask pI1760) (cmask pI1760) (hmask pI1760) 1245 515 (true, I1760_cp1.1, I1760_cp1.2)) ∧ intTest pI1760 (runFrom pI1760 (fmask pI1760) (cmask pI1760) (hmask pI1760) 1245 515 (true, I1760_cp1.1, I1760_cp1.2)) 1760 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1760_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1760_fin) true) I1760_seg1) (by decide) rfl I1760_fin intTest_fst
theorem link1760 : linkOK pL1760 pH1760 pI1760 = true := by decide +kernel
theorem cvx1760 : ConvexBetweenHumps 1760 :=
  cvx_of L1760_ok H1760_ok I1760_ok link1760 (by decide)
theorem cenlink1760 : cenLinkOK pI1760 1760 = true := by decide +kernel
theorem cen1760 : CenterUniqueMin 1760 ∧ DipHyp 1760 ∧ OnePointHyps 1760 :=
  cen_of L1760_ok H1760_ok I1760_ok link1760 cenlink1760

/-! ### `N = 1761` -/

def pL1761 : Prm := ⟨80, 37, 40, 1763, 11, 18446744073709551616, 109164368524888420, 109164368524888420⟩
def pH1761 : Prm := ⟨80, 37, 40, 1763, 11, 18446744073709551616, 109165468036516196, 109165468036516196⟩
def pI1761 : Prm := ⟨67, 34, 30, 1763, 11, 18446744073709551616, 109164368524888420, 109165468036516196⟩
noncomputable def L1761_cp1 : Nat × Nat := t7val% (fastRun pL1761 1 1016 (init pL1761) (init pL1761))
theorem L1761_seg1 : segOK pL1761 1 1016 (init pL1761) (init pL1761) L1761_cp1.1 L1761_cp1.2 = true := by
  decide +kernel
noncomputable def L1761_cp2 : Nat × Nat := t7val% (fastRun pL1761 1 1437 (init pL1761) (init pL1761))
theorem L1761_seg2 : segOK pL1761 1017 421 L1761_cp1.1 L1761_cp1.2 L1761_cp2.1 L1761_cp2.2 = true := by
  decide +kernel
theorem L1761_fin : (prmOK pL1761 1761 && ptTest pL1761 (runFrom pL1761 (fmask pL1761) (cmask pL1761) (hmask pL1761) 1438 323 (true, L1761_cp2.1, L1761_cp2.2)) 1761 881 false) = true := by
  decide +kernel
theorem L1761_ok : RunOK pL1761 1761 (runFrom pL1761 (fmask pL1761) (cmask pL1761) (hmask pL1761) 1438 323 (true, L1761_cp2.1, L1761_cp2.2)) ∧ ptTest pL1761 (runFrom pL1761 (fmask pL1761) (cmask pL1761) (hmask pL1761) 1438 323 (true, L1761_cp2.1, L1761_cp2.2)) 1761 881 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1761_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1761_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1761_fin) true) L1761_seg1) L1761_seg2) (by decide) rfl L1761_fin ptTest_fst
noncomputable def H1761_cp1 : Nat × Nat := t7val% (fastRun pH1761 1 1016 (init pH1761) (init pH1761))
theorem H1761_seg1 : segOK pH1761 1 1016 (init pH1761) (init pH1761) H1761_cp1.1 H1761_cp1.2 = true := by
  decide +kernel
noncomputable def H1761_cp2 : Nat × Nat := t7val% (fastRun pH1761 1 1437 (init pH1761) (init pH1761))
theorem H1761_seg2 : segOK pH1761 1017 421 H1761_cp1.1 H1761_cp1.2 H1761_cp2.1 H1761_cp2.2 = true := by
  decide +kernel
theorem H1761_fin : (prmOK pH1761 1761 && ptTest pH1761 (runFrom pH1761 (fmask pH1761) (cmask pH1761) (hmask pH1761) 1438 323 (true, H1761_cp2.1, H1761_cp2.2)) 1761 881 true) = true := by
  decide +kernel
theorem H1761_ok : RunOK pH1761 1761 (runFrom pH1761 (fmask pH1761) (cmask pH1761) (hmask pH1761) 1438 323 (true, H1761_cp2.1, H1761_cp2.2)) ∧ ptTest pH1761 (runFrom pH1761 (fmask pH1761) (cmask pH1761) (hmask pH1761) 1438 323 (true, H1761_cp2.1, H1761_cp2.2)) 1761 881 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1761_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1761_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1761_fin) true) H1761_seg1) H1761_seg2) (by decide) rfl H1761_fin ptTest_fst
noncomputable def I1761_cp1 : Nat × Nat := t7val% (fastRun pI1761 1 1244 (init pI1761) (init pI1761))
theorem I1761_seg1 : segOK pI1761 1 1244 (init pI1761) (init pI1761) I1761_cp1.1 I1761_cp1.2 = true := by
  decide +kernel
theorem I1761_fin : (prmOK pI1761 1761 && intTest pI1761 (runFrom pI1761 (fmask pI1761) (cmask pI1761) (hmask pI1761) 1245 516 (true, I1761_cp1.1, I1761_cp1.2)) 1761 21 false) = true := by
  decide +kernel
theorem I1761_ok : RunOK pI1761 1761 (runFrom pI1761 (fmask pI1761) (cmask pI1761) (hmask pI1761) 1245 516 (true, I1761_cp1.1, I1761_cp1.2)) ∧ intTest pI1761 (runFrom pI1761 (fmask pI1761) (cmask pI1761) (hmask pI1761) 1245 516 (true, I1761_cp1.1, I1761_cp1.2)) 1761 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1761_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1761_fin) true) I1761_seg1) (by decide) rfl I1761_fin intTest_fst
theorem link1761 : linkOK pL1761 pH1761 pI1761 = true := by decide +kernel
theorem cvx1761 : ConvexBetweenHumps 1761 :=
  cvx_of L1761_ok H1761_ok I1761_ok link1761 (by decide)

/-! ### `N = 1762` -/

def pL1762 : Prm := ⟨80, 37, 40, 1764, 11, 18446744073709551616, 109113627775242177, 109113627775242177⟩
def pH1762 : Prm := ⟨80, 37, 40, 1764, 11, 18446744073709551616, 109114727286869953, 109114727286869953⟩
def pI1762 : Prm := ⟨67, 34, 30, 1764, 11, 18446744073709551616, 109113627775242177, 109114727286869953⟩
noncomputable def L1762_cp1 : Nat × Nat := t7val% (fastRun pL1762 1 1016 (init pL1762) (init pL1762))
theorem L1762_seg1 : segOK pL1762 1 1016 (init pL1762) (init pL1762) L1762_cp1.1 L1762_cp1.2 = true := by
  decide +kernel
noncomputable def L1762_cp2 : Nat × Nat := t7val% (fastRun pL1762 1 1438 (init pL1762) (init pL1762))
theorem L1762_seg2 : segOK pL1762 1017 422 L1762_cp1.1 L1762_cp1.2 L1762_cp2.1 L1762_cp2.2 = true := by
  decide +kernel
theorem L1762_fin : (prmOK pL1762 1762 && ptTest pL1762 (runFrom pL1762 (fmask pL1762) (cmask pL1762) (hmask pL1762) 1439 323 (true, L1762_cp2.1, L1762_cp2.2)) 1762 881 false) = true := by
  decide +kernel
theorem L1762_ok : RunOK pL1762 1762 (runFrom pL1762 (fmask pL1762) (cmask pL1762) (hmask pL1762) 1439 323 (true, L1762_cp2.1, L1762_cp2.2)) ∧ ptTest pL1762 (runFrom pL1762 (fmask pL1762) (cmask pL1762) (hmask pL1762) 1439 323 (true, L1762_cp2.1, L1762_cp2.2)) 1762 881 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1762_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1762_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1762_fin) true) L1762_seg1) L1762_seg2) (by decide) rfl L1762_fin ptTest_fst
noncomputable def H1762_cp1 : Nat × Nat := t7val% (fastRun pH1762 1 1016 (init pH1762) (init pH1762))
theorem H1762_seg1 : segOK pH1762 1 1016 (init pH1762) (init pH1762) H1762_cp1.1 H1762_cp1.2 = true := by
  decide +kernel
noncomputable def H1762_cp2 : Nat × Nat := t7val% (fastRun pH1762 1 1438 (init pH1762) (init pH1762))
theorem H1762_seg2 : segOK pH1762 1017 422 H1762_cp1.1 H1762_cp1.2 H1762_cp2.1 H1762_cp2.2 = true := by
  decide +kernel
theorem H1762_fin : (prmOK pH1762 1762 && ptTest pH1762 (runFrom pH1762 (fmask pH1762) (cmask pH1762) (hmask pH1762) 1439 323 (true, H1762_cp2.1, H1762_cp2.2)) 1762 881 true) = true := by
  decide +kernel
theorem H1762_ok : RunOK pH1762 1762 (runFrom pH1762 (fmask pH1762) (cmask pH1762) (hmask pH1762) 1439 323 (true, H1762_cp2.1, H1762_cp2.2)) ∧ ptTest pH1762 (runFrom pH1762 (fmask pH1762) (cmask pH1762) (hmask pH1762) 1439 323 (true, H1762_cp2.1, H1762_cp2.2)) 1762 881 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1762_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1762_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1762_fin) true) H1762_seg1) H1762_seg2) (by decide) rfl H1762_fin ptTest_fst
noncomputable def I1762_cp1 : Nat × Nat := t7val% (fastRun pI1762 1 1245 (init pI1762) (init pI1762))
theorem I1762_seg1 : segOK pI1762 1 1245 (init pI1762) (init pI1762) I1762_cp1.1 I1762_cp1.2 = true := by
  decide +kernel
theorem I1762_fin : (prmOK pI1762 1762 && intTest pI1762 (runFrom pI1762 (fmask pI1762) (cmask pI1762) (hmask pI1762) 1246 516 (true, I1762_cp1.1, I1762_cp1.2)) 1762 21 true) = true := by
  decide +kernel
theorem I1762_ok : RunOK pI1762 1762 (runFrom pI1762 (fmask pI1762) (cmask pI1762) (hmask pI1762) 1246 516 (true, I1762_cp1.1, I1762_cp1.2)) ∧ intTest pI1762 (runFrom pI1762 (fmask pI1762) (cmask pI1762) (hmask pI1762) 1246 516 (true, I1762_cp1.1, I1762_cp1.2)) 1762 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1762_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1762_fin) true) I1762_seg1) (by decide) rfl I1762_fin intTest_fst
theorem link1762 : linkOK pL1762 pH1762 pI1762 = true := by decide +kernel
theorem cvx1762 : ConvexBetweenHumps 1762 :=
  cvx_of L1762_ok H1762_ok I1762_ok link1762 (by decide)
theorem cenlink1762 : cenLinkOK pI1762 1762 = true := by decide +kernel
theorem cen1762 : CenterUniqueMin 1762 ∧ DipHyp 1762 ∧ OnePointHyps 1762 :=
  cen_of L1762_ok H1762_ok I1762_ok link1762 cenlink1762

/-! ### `N = 1763` -/

def pL1763 : Prm := ⟨80, 37, 40, 1765, 11, 18446744073709551616, 109062917700741994, 109062917700741994⟩
def pH1763 : Prm := ⟨80, 37, 40, 1765, 11, 18446744073709551616, 109064017212369770, 109064017212369770⟩
def pI1763 : Prm := ⟨67, 34, 30, 1765, 11, 18446744073709551616, 109062917700741994, 109064017212369770⟩
noncomputable def L1763_cp1 : Nat × Nat := t7val% (fastRun pL1763 1 1017 (init pL1763) (init pL1763))
theorem L1763_seg1 : segOK pL1763 1 1017 (init pL1763) (init pL1763) L1763_cp1.1 L1763_cp1.2 = true := by
  decide +kernel
noncomputable def L1763_cp2 : Nat × Nat := t7val% (fastRun pL1763 1 1438 (init pL1763) (init pL1763))
theorem L1763_seg2 : segOK pL1763 1018 421 L1763_cp1.1 L1763_cp1.2 L1763_cp2.1 L1763_cp2.2 = true := by
  decide +kernel
theorem L1763_fin : (prmOK pL1763 1763 && ptTest pL1763 (runFrom pL1763 (fmask pL1763) (cmask pL1763) (hmask pL1763) 1439 324 (true, L1763_cp2.1, L1763_cp2.2)) 1763 882 false) = true := by
  decide +kernel
theorem L1763_ok : RunOK pL1763 1763 (runFrom pL1763 (fmask pL1763) (cmask pL1763) (hmask pL1763) 1439 324 (true, L1763_cp2.1, L1763_cp2.2)) ∧ ptTest pL1763 (runFrom pL1763 (fmask pL1763) (cmask pL1763) (hmask pL1763) 1439 324 (true, L1763_cp2.1, L1763_cp2.2)) 1763 882 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1763_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1763_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1763_fin) true) L1763_seg1) L1763_seg2) (by decide) rfl L1763_fin ptTest_fst
noncomputable def H1763_cp1 : Nat × Nat := t7val% (fastRun pH1763 1 1017 (init pH1763) (init pH1763))
theorem H1763_seg1 : segOK pH1763 1 1017 (init pH1763) (init pH1763) H1763_cp1.1 H1763_cp1.2 = true := by
  decide +kernel
noncomputable def H1763_cp2 : Nat × Nat := t7val% (fastRun pH1763 1 1438 (init pH1763) (init pH1763))
theorem H1763_seg2 : segOK pH1763 1018 421 H1763_cp1.1 H1763_cp1.2 H1763_cp2.1 H1763_cp2.2 = true := by
  decide +kernel
theorem H1763_fin : (prmOK pH1763 1763 && ptTest pH1763 (runFrom pH1763 (fmask pH1763) (cmask pH1763) (hmask pH1763) 1439 324 (true, H1763_cp2.1, H1763_cp2.2)) 1763 882 true) = true := by
  decide +kernel
theorem H1763_ok : RunOK pH1763 1763 (runFrom pH1763 (fmask pH1763) (cmask pH1763) (hmask pH1763) 1439 324 (true, H1763_cp2.1, H1763_cp2.2)) ∧ ptTest pH1763 (runFrom pH1763 (fmask pH1763) (cmask pH1763) (hmask pH1763) 1439 324 (true, H1763_cp2.1, H1763_cp2.2)) 1763 882 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1763_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1763_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1763_fin) true) H1763_seg1) H1763_seg2) (by decide) rfl H1763_fin ptTest_fst
noncomputable def I1763_cp1 : Nat × Nat := t7val% (fastRun pI1763 1 1246 (init pI1763) (init pI1763))
theorem I1763_seg1 : segOK pI1763 1 1246 (init pI1763) (init pI1763) I1763_cp1.1 I1763_cp1.2 = true := by
  decide +kernel
theorem I1763_fin : (prmOK pI1763 1763 && intTest pI1763 (runFrom pI1763 (fmask pI1763) (cmask pI1763) (hmask pI1763) 1247 516 (true, I1763_cp1.1, I1763_cp1.2)) 1763 21 false) = true := by
  decide +kernel
theorem I1763_ok : RunOK pI1763 1763 (runFrom pI1763 (fmask pI1763) (cmask pI1763) (hmask pI1763) 1247 516 (true, I1763_cp1.1, I1763_cp1.2)) ∧ intTest pI1763 (runFrom pI1763 (fmask pI1763) (cmask pI1763) (hmask pI1763) 1247 516 (true, I1763_cp1.1, I1763_cp1.2)) 1763 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1763_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1763_fin) true) I1763_seg1) (by decide) rfl I1763_fin intTest_fst
theorem link1763 : linkOK pL1763 pH1763 pI1763 = true := by decide +kernel
theorem cvx1763 : ConvexBetweenHumps 1763 :=
  cvx_of L1763_ok H1763_ok I1763_ok link1763 (by decide)

/-! ### `N = 1764` -/

def pL1764 : Prm := ⟨80, 37, 40, 1766, 11, 18446744073709551616, 109012279259136460, 109012279259136460⟩
def pH1764 : Prm := ⟨80, 37, 40, 1766, 11, 18446744073709551616, 109013378770764236, 109013378770764236⟩
def pI1764 : Prm := ⟨67, 34, 30, 1766, 11, 18446744073709551616, 109012279259136460, 109013378770764236⟩
noncomputable def L1764_cp1 : Nat × Nat := t7val% (fastRun pL1764 1 1017 (init pL1764) (init pL1764))
theorem L1764_seg1 : segOK pL1764 1 1017 (init pL1764) (init pL1764) L1764_cp1.1 L1764_cp1.2 = true := by
  decide +kernel
noncomputable def L1764_cp2 : Nat × Nat := t7val% (fastRun pL1764 1 1439 (init pL1764) (init pL1764))
theorem L1764_seg2 : segOK pL1764 1018 422 L1764_cp1.1 L1764_cp1.2 L1764_cp2.1 L1764_cp2.2 = true := by
  decide +kernel
theorem L1764_fin : (prmOK pL1764 1764 && ptTest pL1764 (runFrom pL1764 (fmask pL1764) (cmask pL1764) (hmask pL1764) 1440 324 (true, L1764_cp2.1, L1764_cp2.2)) 1764 882 false) = true := by
  decide +kernel
theorem L1764_ok : RunOK pL1764 1764 (runFrom pL1764 (fmask pL1764) (cmask pL1764) (hmask pL1764) 1440 324 (true, L1764_cp2.1, L1764_cp2.2)) ∧ ptTest pL1764 (runFrom pL1764 (fmask pL1764) (cmask pL1764) (hmask pL1764) 1440 324 (true, L1764_cp2.1, L1764_cp2.2)) 1764 882 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1764_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1764_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1764_fin) true) L1764_seg1) L1764_seg2) (by decide) rfl L1764_fin ptTest_fst
noncomputable def H1764_cp1 : Nat × Nat := t7val% (fastRun pH1764 1 1017 (init pH1764) (init pH1764))
theorem H1764_seg1 : segOK pH1764 1 1017 (init pH1764) (init pH1764) H1764_cp1.1 H1764_cp1.2 = true := by
  decide +kernel
noncomputable def H1764_cp2 : Nat × Nat := t7val% (fastRun pH1764 1 1439 (init pH1764) (init pH1764))
theorem H1764_seg2 : segOK pH1764 1018 422 H1764_cp1.1 H1764_cp1.2 H1764_cp2.1 H1764_cp2.2 = true := by
  decide +kernel
theorem H1764_fin : (prmOK pH1764 1764 && ptTest pH1764 (runFrom pH1764 (fmask pH1764) (cmask pH1764) (hmask pH1764) 1440 324 (true, H1764_cp2.1, H1764_cp2.2)) 1764 882 true) = true := by
  decide +kernel
theorem H1764_ok : RunOK pH1764 1764 (runFrom pH1764 (fmask pH1764) (cmask pH1764) (hmask pH1764) 1440 324 (true, H1764_cp2.1, H1764_cp2.2)) ∧ ptTest pH1764 (runFrom pH1764 (fmask pH1764) (cmask pH1764) (hmask pH1764) 1440 324 (true, H1764_cp2.1, H1764_cp2.2)) 1764 882 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1764_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1764_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1764_fin) true) H1764_seg1) H1764_seg2) (by decide) rfl H1764_fin ptTest_fst
noncomputable def I1764_cp1 : Nat × Nat := t7val% (fastRun pI1764 1 1246 (init pI1764) (init pI1764))
theorem I1764_seg1 : segOK pI1764 1 1246 (init pI1764) (init pI1764) I1764_cp1.1 I1764_cp1.2 = true := by
  decide +kernel
theorem I1764_fin : (prmOK pI1764 1764 && intTest pI1764 (runFrom pI1764 (fmask pI1764) (cmask pI1764) (hmask pI1764) 1247 517 (true, I1764_cp1.1, I1764_cp1.2)) 1764 21 true) = true := by
  decide +kernel
theorem I1764_ok : RunOK pI1764 1764 (runFrom pI1764 (fmask pI1764) (cmask pI1764) (hmask pI1764) 1247 517 (true, I1764_cp1.1, I1764_cp1.2)) ∧ intTest pI1764 (runFrom pI1764 (fmask pI1764) (cmask pI1764) (hmask pI1764) 1247 517 (true, I1764_cp1.1, I1764_cp1.2)) 1764 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1764_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1764_fin) true) I1764_seg1) (by decide) rfl I1764_fin intTest_fst
theorem link1764 : linkOK pL1764 pH1764 pI1764 = true := by decide +kernel
theorem cvx1764 : ConvexBetweenHumps 1764 :=
  cvx_of L1764_ok H1764_ok I1764_ok link1764 (by decide)
theorem cenlink1764 : cenLinkOK pI1764 1764 = true := by decide +kernel
theorem cen1764 : CenterUniqueMin 1764 ∧ DipHyp 1764 ∧ OnePointHyps 1764 :=
  cen_of L1764_ok H1764_ok I1764_ok link1764 cenlink1764

/-! ### `N = 1765` -/

def pL1765 : Prm := ⟨80, 37, 40, 1767, 11, 18446744073709551616, 108961671403911254, 108961671403911254⟩
def pH1765 : Prm := ⟨80, 37, 40, 1767, 11, 18446744073709551616, 108962770915539030, 108962770915539030⟩
def pI1765 : Prm := ⟨67, 34, 30, 1767, 11, 18446744073709551616, 108961671403911254, 108962770915539030⟩
noncomputable def L1765_cp1 : Nat × Nat := t7val% (fastRun pL1765 1 1018 (init pL1765) (init pL1765))
theorem L1765_seg1 : segOK pL1765 1 1018 (init pL1765) (init pL1765) L1765_cp1.1 L1765_cp1.2 = true := by
  decide +kernel
noncomputable def L1765_cp2 : Nat × Nat := t7val% (fastRun pL1765 1 1440 (init pL1765) (init pL1765))
theorem L1765_seg2 : segOK pL1765 1019 422 L1765_cp1.1 L1765_cp1.2 L1765_cp2.1 L1765_cp2.2 = true := by
  decide +kernel
theorem L1765_fin : (prmOK pL1765 1765 && ptTest pL1765 (runFrom pL1765 (fmask pL1765) (cmask pL1765) (hmask pL1765) 1441 324 (true, L1765_cp2.1, L1765_cp2.2)) 1765 883 false) = true := by
  decide +kernel
theorem L1765_ok : RunOK pL1765 1765 (runFrom pL1765 (fmask pL1765) (cmask pL1765) (hmask pL1765) 1441 324 (true, L1765_cp2.1, L1765_cp2.2)) ∧ ptTest pL1765 (runFrom pL1765 (fmask pL1765) (cmask pL1765) (hmask pL1765) 1441 324 (true, L1765_cp2.1, L1765_cp2.2)) 1765 883 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1765_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1765_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1765_fin) true) L1765_seg1) L1765_seg2) (by decide) rfl L1765_fin ptTest_fst
noncomputable def H1765_cp1 : Nat × Nat := t7val% (fastRun pH1765 1 1018 (init pH1765) (init pH1765))
theorem H1765_seg1 : segOK pH1765 1 1018 (init pH1765) (init pH1765) H1765_cp1.1 H1765_cp1.2 = true := by
  decide +kernel
noncomputable def H1765_cp2 : Nat × Nat := t7val% (fastRun pH1765 1 1440 (init pH1765) (init pH1765))
theorem H1765_seg2 : segOK pH1765 1019 422 H1765_cp1.1 H1765_cp1.2 H1765_cp2.1 H1765_cp2.2 = true := by
  decide +kernel
theorem H1765_fin : (prmOK pH1765 1765 && ptTest pH1765 (runFrom pH1765 (fmask pH1765) (cmask pH1765) (hmask pH1765) 1441 324 (true, H1765_cp2.1, H1765_cp2.2)) 1765 883 true) = true := by
  decide +kernel
theorem H1765_ok : RunOK pH1765 1765 (runFrom pH1765 (fmask pH1765) (cmask pH1765) (hmask pH1765) 1441 324 (true, H1765_cp2.1, H1765_cp2.2)) ∧ ptTest pH1765 (runFrom pH1765 (fmask pH1765) (cmask pH1765) (hmask pH1765) 1441 324 (true, H1765_cp2.1, H1765_cp2.2)) 1765 883 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1765_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1765_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1765_fin) true) H1765_seg1) H1765_seg2) (by decide) rfl H1765_fin ptTest_fst
noncomputable def I1765_cp1 : Nat × Nat := t7val% (fastRun pI1765 1 1247 (init pI1765) (init pI1765))
theorem I1765_seg1 : segOK pI1765 1 1247 (init pI1765) (init pI1765) I1765_cp1.1 I1765_cp1.2 = true := by
  decide +kernel
theorem I1765_fin : (prmOK pI1765 1765 && intTest pI1765 (runFrom pI1765 (fmask pI1765) (cmask pI1765) (hmask pI1765) 1248 517 (true, I1765_cp1.1, I1765_cp1.2)) 1765 21 false) = true := by
  decide +kernel
theorem I1765_ok : RunOK pI1765 1765 (runFrom pI1765 (fmask pI1765) (cmask pI1765) (hmask pI1765) 1248 517 (true, I1765_cp1.1, I1765_cp1.2)) ∧ intTest pI1765 (runFrom pI1765 (fmask pI1765) (cmask pI1765) (hmask pI1765) 1248 517 (true, I1765_cp1.1, I1765_cp1.2)) 1765 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1765_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1765_fin) true) I1765_seg1) (by decide) rfl I1765_fin intTest_fst
theorem link1765 : linkOK pL1765 pH1765 pI1765 = true := by decide +kernel
theorem cvx1765 : ConvexBetweenHumps 1765 :=
  cvx_of L1765_ok H1765_ok I1765_ok link1765 (by decide)

/-! ### `N = 1766` -/

def pL1766 : Prm := ⟨80, 37, 40, 1768, 11, 18446744073709551616, 108911134951660479, 108911134951660479⟩
def pH1766 : Prm := ⟨80, 37, 40, 1768, 11, 18446744073709551616, 108912234463288255, 108912234463288255⟩
def pI1766 : Prm := ⟨67, 34, 30, 1768, 11, 18446744073709551616, 108911134951660479, 108912234463288255⟩
noncomputable def L1766_cp1 : Nat × Nat := t7val% (fastRun pL1766 1 1019 (init pL1766) (init pL1766))
theorem L1766_seg1 : segOK pL1766 1 1019 (init pL1766) (init pL1766) L1766_cp1.1 L1766_cp1.2 = true := by
  decide +kernel
noncomputable def L1766_cp2 : Nat × Nat := t7val% (fastRun pL1766 1 1441 (init pL1766) (init pL1766))
theorem L1766_seg2 : segOK pL1766 1020 422 L1766_cp1.1 L1766_cp1.2 L1766_cp2.1 L1766_cp2.2 = true := by
  decide +kernel
theorem L1766_fin : (prmOK pL1766 1766 && ptTest pL1766 (runFrom pL1766 (fmask pL1766) (cmask pL1766) (hmask pL1766) 1442 324 (true, L1766_cp2.1, L1766_cp2.2)) 1766 883 false) = true := by
  decide +kernel
theorem L1766_ok : RunOK pL1766 1766 (runFrom pL1766 (fmask pL1766) (cmask pL1766) (hmask pL1766) 1442 324 (true, L1766_cp2.1, L1766_cp2.2)) ∧ ptTest pL1766 (runFrom pL1766 (fmask pL1766) (cmask pL1766) (hmask pL1766) 1442 324 (true, L1766_cp2.1, L1766_cp2.2)) 1766 883 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1766_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1766_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1766_fin) true) L1766_seg1) L1766_seg2) (by decide) rfl L1766_fin ptTest_fst
noncomputable def H1766_cp1 : Nat × Nat := t7val% (fastRun pH1766 1 1019 (init pH1766) (init pH1766))
theorem H1766_seg1 : segOK pH1766 1 1019 (init pH1766) (init pH1766) H1766_cp1.1 H1766_cp1.2 = true := by
  decide +kernel
noncomputable def H1766_cp2 : Nat × Nat := t7val% (fastRun pH1766 1 1441 (init pH1766) (init pH1766))
theorem H1766_seg2 : segOK pH1766 1020 422 H1766_cp1.1 H1766_cp1.2 H1766_cp2.1 H1766_cp2.2 = true := by
  decide +kernel
theorem H1766_fin : (prmOK pH1766 1766 && ptTest pH1766 (runFrom pH1766 (fmask pH1766) (cmask pH1766) (hmask pH1766) 1442 324 (true, H1766_cp2.1, H1766_cp2.2)) 1766 883 true) = true := by
  decide +kernel
theorem H1766_ok : RunOK pH1766 1766 (runFrom pH1766 (fmask pH1766) (cmask pH1766) (hmask pH1766) 1442 324 (true, H1766_cp2.1, H1766_cp2.2)) ∧ ptTest pH1766 (runFrom pH1766 (fmask pH1766) (cmask pH1766) (hmask pH1766) 1442 324 (true, H1766_cp2.1, H1766_cp2.2)) 1766 883 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1766_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1766_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1766_fin) true) H1766_seg1) H1766_seg2) (by decide) rfl H1766_fin ptTest_fst
noncomputable def I1766_cp1 : Nat × Nat := t7val% (fastRun pI1766 1 1248 (init pI1766) (init pI1766))
theorem I1766_seg1 : segOK pI1766 1 1248 (init pI1766) (init pI1766) I1766_cp1.1 I1766_cp1.2 = true := by
  decide +kernel
theorem I1766_fin : (prmOK pI1766 1766 && intTest pI1766 (runFrom pI1766 (fmask pI1766) (cmask pI1766) (hmask pI1766) 1249 517 (true, I1766_cp1.1, I1766_cp1.2)) 1766 21 true) = true := by
  decide +kernel
theorem I1766_ok : RunOK pI1766 1766 (runFrom pI1766 (fmask pI1766) (cmask pI1766) (hmask pI1766) 1249 517 (true, I1766_cp1.1, I1766_cp1.2)) ∧ intTest pI1766 (runFrom pI1766 (fmask pI1766) (cmask pI1766) (hmask pI1766) 1249 517 (true, I1766_cp1.1, I1766_cp1.2)) 1766 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1766_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1766_fin) true) I1766_seg1) (by decide) rfl I1766_fin intTest_fst
theorem link1766 : linkOK pL1766 pH1766 pI1766 = true := by decide +kernel
theorem cvx1766 : ConvexBetweenHumps 1766 :=
  cvx_of L1766_ok H1766_ok I1766_ok link1766 (by decide)
theorem cenlink1766 : cenLinkOK pI1766 1766 = true := by decide +kernel
theorem cen1766 : CenterUniqueMin 1766 ∧ DipHyp 1766 ∧ OnePointHyps 1766 :=
  cen_of L1766_ok H1766_ok I1766_ok link1766 cenlink1766

/-! ### `N = 1767` -/

def pL1767 : Prm := ⟨80, 37, 40, 1769, 11, 18446744073709551616, 108860628997374788, 108860628997374788⟩
def pH1767 : Prm := ⟨80, 37, 40, 1769, 11, 18446744073709551616, 108861728509002564, 108861728509002564⟩
def pI1767 : Prm := ⟨67, 34, 30, 1769, 11, 18446744073709551616, 108860628997374788, 108861728509002564⟩
noncomputable def L1767_cp1 : Nat × Nat := t7val% (fastRun pL1767 1 1019 (init pL1767) (init pL1767))
theorem L1767_seg1 : segOK pL1767 1 1019 (init pL1767) (init pL1767) L1767_cp1.1 L1767_cp1.2 = true := by
  decide +kernel
noncomputable def L1767_cp2 : Nat × Nat := t7val% (fastRun pL1767 1 1442 (init pL1767) (init pL1767))
theorem L1767_seg2 : segOK pL1767 1020 423 L1767_cp1.1 L1767_cp1.2 L1767_cp2.1 L1767_cp2.2 = true := by
  decide +kernel
theorem L1767_fin : (prmOK pL1767 1767 && ptTest pL1767 (runFrom pL1767 (fmask pL1767) (cmask pL1767) (hmask pL1767) 1443 324 (true, L1767_cp2.1, L1767_cp2.2)) 1767 884 false) = true := by
  decide +kernel
theorem L1767_ok : RunOK pL1767 1767 (runFrom pL1767 (fmask pL1767) (cmask pL1767) (hmask pL1767) 1443 324 (true, L1767_cp2.1, L1767_cp2.2)) ∧ ptTest pL1767 (runFrom pL1767 (fmask pL1767) (cmask pL1767) (hmask pL1767) 1443 324 (true, L1767_cp2.1, L1767_cp2.2)) 1767 884 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1767_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1767_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1767_fin) true) L1767_seg1) L1767_seg2) (by decide) rfl L1767_fin ptTest_fst
noncomputable def H1767_cp1 : Nat × Nat := t7val% (fastRun pH1767 1 1019 (init pH1767) (init pH1767))
theorem H1767_seg1 : segOK pH1767 1 1019 (init pH1767) (init pH1767) H1767_cp1.1 H1767_cp1.2 = true := by
  decide +kernel
noncomputable def H1767_cp2 : Nat × Nat := t7val% (fastRun pH1767 1 1442 (init pH1767) (init pH1767))
theorem H1767_seg2 : segOK pH1767 1020 423 H1767_cp1.1 H1767_cp1.2 H1767_cp2.1 H1767_cp2.2 = true := by
  decide +kernel
theorem H1767_fin : (prmOK pH1767 1767 && ptTest pH1767 (runFrom pH1767 (fmask pH1767) (cmask pH1767) (hmask pH1767) 1443 324 (true, H1767_cp2.1, H1767_cp2.2)) 1767 884 true) = true := by
  decide +kernel
theorem H1767_ok : RunOK pH1767 1767 (runFrom pH1767 (fmask pH1767) (cmask pH1767) (hmask pH1767) 1443 324 (true, H1767_cp2.1, H1767_cp2.2)) ∧ ptTest pH1767 (runFrom pH1767 (fmask pH1767) (cmask pH1767) (hmask pH1767) 1443 324 (true, H1767_cp2.1, H1767_cp2.2)) 1767 884 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1767_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1767_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1767_fin) true) H1767_seg1) H1767_seg2) (by decide) rfl H1767_fin ptTest_fst
noncomputable def I1767_cp1 : Nat × Nat := t7val% (fastRun pI1767 1 1248 (init pI1767) (init pI1767))
theorem I1767_seg1 : segOK pI1767 1 1248 (init pI1767) (init pI1767) I1767_cp1.1 I1767_cp1.2 = true := by
  decide +kernel
theorem I1767_fin : (prmOK pI1767 1767 && intTest pI1767 (runFrom pI1767 (fmask pI1767) (cmask pI1767) (hmask pI1767) 1249 518 (true, I1767_cp1.1, I1767_cp1.2)) 1767 21 false) = true := by
  decide +kernel
theorem I1767_ok : RunOK pI1767 1767 (runFrom pI1767 (fmask pI1767) (cmask pI1767) (hmask pI1767) 1249 518 (true, I1767_cp1.1, I1767_cp1.2)) ∧ intTest pI1767 (runFrom pI1767 (fmask pI1767) (cmask pI1767) (hmask pI1767) 1249 518 (true, I1767_cp1.1, I1767_cp1.2)) 1767 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1767_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1767_fin) true) I1767_seg1) (by decide) rfl I1767_fin intTest_fst
theorem link1767 : linkOK pL1767 pH1767 pI1767 = true := by decide +kernel
theorem cvx1767 : ConvexBetweenHumps 1767 :=
  cvx_of L1767_ok H1767_ok I1767_ok link1767 (by decide)

/-! ### `N = 1768` -/

def pL1768 : Prm := ⟨80, 37, 40, 1770, 11, 18446744073709551616, 108810194217120988, 108810194217120988⟩
def pH1768 : Prm := ⟨80, 37, 40, 1770, 11, 18446744073709551616, 108811293728748764, 108811293728748764⟩
def pI1768 : Prm := ⟨67, 34, 30, 1770, 11, 18446744073709551616, 108810194217120988, 108811293728748764⟩
noncomputable def L1768_cp1 : Nat × Nat := t7val% (fastRun pL1768 1 1020 (init pL1768) (init pL1768))
theorem L1768_seg1 : segOK pL1768 1 1020 (init pL1768) (init pL1768) L1768_cp1.1 L1768_cp1.2 = true := by
  decide +kernel
noncomputable def L1768_cp2 : Nat × Nat := t7val% (fastRun pL1768 1 1443 (init pL1768) (init pL1768))
theorem L1768_seg2 : segOK pL1768 1021 423 L1768_cp1.1 L1768_cp1.2 L1768_cp2.1 L1768_cp2.2 = true := by
  decide +kernel
theorem L1768_fin : (prmOK pL1768 1768 && ptTest pL1768 (runFrom pL1768 (fmask pL1768) (cmask pL1768) (hmask pL1768) 1444 324 (true, L1768_cp2.1, L1768_cp2.2)) 1768 884 false) = true := by
  decide +kernel
theorem L1768_ok : RunOK pL1768 1768 (runFrom pL1768 (fmask pL1768) (cmask pL1768) (hmask pL1768) 1444 324 (true, L1768_cp2.1, L1768_cp2.2)) ∧ ptTest pL1768 (runFrom pL1768 (fmask pL1768) (cmask pL1768) (hmask pL1768) 1444 324 (true, L1768_cp2.1, L1768_cp2.2)) 1768 884 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1768_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1768_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1768_fin) true) L1768_seg1) L1768_seg2) (by decide) rfl L1768_fin ptTest_fst
noncomputable def H1768_cp1 : Nat × Nat := t7val% (fastRun pH1768 1 1020 (init pH1768) (init pH1768))
theorem H1768_seg1 : segOK pH1768 1 1020 (init pH1768) (init pH1768) H1768_cp1.1 H1768_cp1.2 = true := by
  decide +kernel
noncomputable def H1768_cp2 : Nat × Nat := t7val% (fastRun pH1768 1 1443 (init pH1768) (init pH1768))
theorem H1768_seg2 : segOK pH1768 1021 423 H1768_cp1.1 H1768_cp1.2 H1768_cp2.1 H1768_cp2.2 = true := by
  decide +kernel
theorem H1768_fin : (prmOK pH1768 1768 && ptTest pH1768 (runFrom pH1768 (fmask pH1768) (cmask pH1768) (hmask pH1768) 1444 324 (true, H1768_cp2.1, H1768_cp2.2)) 1768 884 true) = true := by
  decide +kernel
theorem H1768_ok : RunOK pH1768 1768 (runFrom pH1768 (fmask pH1768) (cmask pH1768) (hmask pH1768) 1444 324 (true, H1768_cp2.1, H1768_cp2.2)) ∧ ptTest pH1768 (runFrom pH1768 (fmask pH1768) (cmask pH1768) (hmask pH1768) 1444 324 (true, H1768_cp2.1, H1768_cp2.2)) 1768 884 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1768_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1768_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1768_fin) true) H1768_seg1) H1768_seg2) (by decide) rfl H1768_fin ptTest_fst
noncomputable def I1768_cp1 : Nat × Nat := t7val% (fastRun pI1768 1 1249 (init pI1768) (init pI1768))
theorem I1768_seg1 : segOK pI1768 1 1249 (init pI1768) (init pI1768) I1768_cp1.1 I1768_cp1.2 = true := by
  decide +kernel
theorem I1768_fin : (prmOK pI1768 1768 && intTest pI1768 (runFrom pI1768 (fmask pI1768) (cmask pI1768) (hmask pI1768) 1250 518 (true, I1768_cp1.1, I1768_cp1.2)) 1768 21 true) = true := by
  decide +kernel
theorem I1768_ok : RunOK pI1768 1768 (runFrom pI1768 (fmask pI1768) (cmask pI1768) (hmask pI1768) 1250 518 (true, I1768_cp1.1, I1768_cp1.2)) ∧ intTest pI1768 (runFrom pI1768 (fmask pI1768) (cmask pI1768) (hmask pI1768) 1250 518 (true, I1768_cp1.1, I1768_cp1.2)) 1768 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1768_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1768_fin) true) I1768_seg1) (by decide) rfl I1768_fin intTest_fst
theorem link1768 : linkOK pL1768 pH1768 pI1768 = true := by decide +kernel
theorem cvx1768 : ConvexBetweenHumps 1768 :=
  cvx_of L1768_ok H1768_ok I1768_ok link1768 (by decide)
theorem cenlink1768 : cenLinkOK pI1768 1768 = true := by decide +kernel
theorem cen1768 : CenterUniqueMin 1768 ∧ DipHyp 1768 ∧ OnePointHyps 1768 :=
  cen_of L1768_ok H1768_ok I1768_ok link1768 cenlink1768

/-! ### `N = 1769` -/

def pL1769 : Prm := ⟨80, 37, 40, 1771, 11, 18446744073709551616, 108759789846785961, 108759789846785961⟩
def pH1769 : Prm := ⟨80, 37, 40, 1771, 11, 18446744073709551616, 108760889358413737, 108760889358413737⟩
def pI1769 : Prm := ⟨67, 34, 30, 1771, 11, 18446744073709551616, 108759789846785961, 108760889358413737⟩
noncomputable def L1769_cp1 : Nat × Nat := t7val% (fastRun pL1769 1 1020 (init pL1769) (init pL1769))
theorem L1769_seg1 : segOK pL1769 1 1020 (init pL1769) (init pL1769) L1769_cp1.1 L1769_cp1.2 = true := by
  decide +kernel
noncomputable def L1769_cp2 : Nat × Nat := t7val% (fastRun pL1769 1 1443 (init pL1769) (init pL1769))
theorem L1769_seg2 : segOK pL1769 1021 423 L1769_cp1.1 L1769_cp1.2 L1769_cp2.1 L1769_cp2.2 = true := by
  decide +kernel
theorem L1769_fin : (prmOK pL1769 1769 && ptTest pL1769 (runFrom pL1769 (fmask pL1769) (cmask pL1769) (hmask pL1769) 1444 325 (true, L1769_cp2.1, L1769_cp2.2)) 1769 885 false) = true := by
  decide +kernel
theorem L1769_ok : RunOK pL1769 1769 (runFrom pL1769 (fmask pL1769) (cmask pL1769) (hmask pL1769) 1444 325 (true, L1769_cp2.1, L1769_cp2.2)) ∧ ptTest pL1769 (runFrom pL1769 (fmask pL1769) (cmask pL1769) (hmask pL1769) 1444 325 (true, L1769_cp2.1, L1769_cp2.2)) 1769 885 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1769_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1769_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1769_fin) true) L1769_seg1) L1769_seg2) (by decide) rfl L1769_fin ptTest_fst
noncomputable def H1769_cp1 : Nat × Nat := t7val% (fastRun pH1769 1 1020 (init pH1769) (init pH1769))
theorem H1769_seg1 : segOK pH1769 1 1020 (init pH1769) (init pH1769) H1769_cp1.1 H1769_cp1.2 = true := by
  decide +kernel
noncomputable def H1769_cp2 : Nat × Nat := t7val% (fastRun pH1769 1 1443 (init pH1769) (init pH1769))
theorem H1769_seg2 : segOK pH1769 1021 423 H1769_cp1.1 H1769_cp1.2 H1769_cp2.1 H1769_cp2.2 = true := by
  decide +kernel
theorem H1769_fin : (prmOK pH1769 1769 && ptTest pH1769 (runFrom pH1769 (fmask pH1769) (cmask pH1769) (hmask pH1769) 1444 325 (true, H1769_cp2.1, H1769_cp2.2)) 1769 885 true) = true := by
  decide +kernel
theorem H1769_ok : RunOK pH1769 1769 (runFrom pH1769 (fmask pH1769) (cmask pH1769) (hmask pH1769) 1444 325 (true, H1769_cp2.1, H1769_cp2.2)) ∧ ptTest pH1769 (runFrom pH1769 (fmask pH1769) (cmask pH1769) (hmask pH1769) 1444 325 (true, H1769_cp2.1, H1769_cp2.2)) 1769 885 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1769_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1769_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1769_fin) true) H1769_seg1) H1769_seg2) (by decide) rfl H1769_fin ptTest_fst
noncomputable def I1769_cp1 : Nat × Nat := t7val% (fastRun pI1769 1 1250 (init pI1769) (init pI1769))
theorem I1769_seg1 : segOK pI1769 1 1250 (init pI1769) (init pI1769) I1769_cp1.1 I1769_cp1.2 = true := by
  decide +kernel
theorem I1769_fin : (prmOK pI1769 1769 && intTest pI1769 (runFrom pI1769 (fmask pI1769) (cmask pI1769) (hmask pI1769) 1251 518 (true, I1769_cp1.1, I1769_cp1.2)) 1769 21 false) = true := by
  decide +kernel
theorem I1769_ok : RunOK pI1769 1769 (runFrom pI1769 (fmask pI1769) (cmask pI1769) (hmask pI1769) 1251 518 (true, I1769_cp1.1, I1769_cp1.2)) ∧ intTest pI1769 (runFrom pI1769 (fmask pI1769) (cmask pI1769) (hmask pI1769) 1251 518 (true, I1769_cp1.1, I1769_cp1.2)) 1769 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1769_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1769_fin) true) I1769_seg1) (by decide) rfl I1769_fin intTest_fst
theorem link1769 : linkOK pL1769 pH1769 pI1769 = true := by decide +kernel
theorem cvx1769 : ConvexBetweenHumps 1769 :=
  cvx_of L1769_ok H1769_ok I1769_ok link1769 (by decide)

/-! ### `N = 1770` -/

def pL1770 : Prm := ⟨80, 37, 40, 1772, 11, 18446744073709551616, 108709456422554854, 108709456422554854⟩
def pH1770 : Prm := ⟨80, 37, 40, 1772, 11, 18446744073709551616, 108710555934182630, 108710555934182630⟩
def pI1770 : Prm := ⟨67, 34, 30, 1772, 11, 18446744073709551616, 108709456422554854, 108710555934182630⟩
noncomputable def L1770_cp1 : Nat × Nat := t7val% (fastRun pL1770 1 1021 (init pL1770) (init pL1770))
theorem L1770_seg1 : segOK pL1770 1 1021 (init pL1770) (init pL1770) L1770_cp1.1 L1770_cp1.2 = true := by
  decide +kernel
noncomputable def L1770_cp2 : Nat × Nat := t7val% (fastRun pL1770 1 1444 (init pL1770) (init pL1770))
theorem L1770_seg2 : segOK pL1770 1022 423 L1770_cp1.1 L1770_cp1.2 L1770_cp2.1 L1770_cp2.2 = true := by
  decide +kernel
theorem L1770_fin : (prmOK pL1770 1770 && ptTest pL1770 (runFrom pL1770 (fmask pL1770) (cmask pL1770) (hmask pL1770) 1445 325 (true, L1770_cp2.1, L1770_cp2.2)) 1770 885 false) = true := by
  decide +kernel
theorem L1770_ok : RunOK pL1770 1770 (runFrom pL1770 (fmask pL1770) (cmask pL1770) (hmask pL1770) 1445 325 (true, L1770_cp2.1, L1770_cp2.2)) ∧ ptTest pL1770 (runFrom pL1770 (fmask pL1770) (cmask pL1770) (hmask pL1770) 1445 325 (true, L1770_cp2.1, L1770_cp2.2)) 1770 885 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1770_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1770_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1770_fin) true) L1770_seg1) L1770_seg2) (by decide) rfl L1770_fin ptTest_fst
noncomputable def H1770_cp1 : Nat × Nat := t7val% (fastRun pH1770 1 1021 (init pH1770) (init pH1770))
theorem H1770_seg1 : segOK pH1770 1 1021 (init pH1770) (init pH1770) H1770_cp1.1 H1770_cp1.2 = true := by
  decide +kernel
noncomputable def H1770_cp2 : Nat × Nat := t7val% (fastRun pH1770 1 1444 (init pH1770) (init pH1770))
theorem H1770_seg2 : segOK pH1770 1022 423 H1770_cp1.1 H1770_cp1.2 H1770_cp2.1 H1770_cp2.2 = true := by
  decide +kernel
theorem H1770_fin : (prmOK pH1770 1770 && ptTest pH1770 (runFrom pH1770 (fmask pH1770) (cmask pH1770) (hmask pH1770) 1445 325 (true, H1770_cp2.1, H1770_cp2.2)) 1770 885 true) = true := by
  decide +kernel
theorem H1770_ok : RunOK pH1770 1770 (runFrom pH1770 (fmask pH1770) (cmask pH1770) (hmask pH1770) 1445 325 (true, H1770_cp2.1, H1770_cp2.2)) ∧ ptTest pH1770 (runFrom pH1770 (fmask pH1770) (cmask pH1770) (hmask pH1770) 1445 325 (true, H1770_cp2.1, H1770_cp2.2)) 1770 885 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1770_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1770_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1770_fin) true) H1770_seg1) H1770_seg2) (by decide) rfl H1770_fin ptTest_fst
noncomputable def I1770_cp1 : Nat × Nat := t7val% (fastRun pI1770 1 1251 (init pI1770) (init pI1770))
theorem I1770_seg1 : segOK pI1770 1 1251 (init pI1770) (init pI1770) I1770_cp1.1 I1770_cp1.2 = true := by
  decide +kernel
theorem I1770_fin : (prmOK pI1770 1770 && intTest pI1770 (runFrom pI1770 (fmask pI1770) (cmask pI1770) (hmask pI1770) 1252 518 (true, I1770_cp1.1, I1770_cp1.2)) 1770 21 true) = true := by
  decide +kernel
theorem I1770_ok : RunOK pI1770 1770 (runFrom pI1770 (fmask pI1770) (cmask pI1770) (hmask pI1770) 1252 518 (true, I1770_cp1.1, I1770_cp1.2)) ∧ intTest pI1770 (runFrom pI1770 (fmask pI1770) (cmask pI1770) (hmask pI1770) 1252 518 (true, I1770_cp1.1, I1770_cp1.2)) 1770 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1770_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1770_fin) true) I1770_seg1) (by decide) rfl I1770_fin intTest_fst
theorem link1770 : linkOK pL1770 pH1770 pI1770 = true := by decide +kernel
theorem cvx1770 : ConvexBetweenHumps 1770 :=
  cvx_of L1770_ok H1770_ok I1770_ok link1770 (by decide)
theorem cenlink1770 : cenLinkOK pI1770 1770 = true := by decide +kernel
theorem cen1770 : CenterUniqueMin 1770 ∧ DipHyp 1770 ∧ OnePointHyps 1770 :=
  cen_of L1770_ok H1770_ok I1770_ok link1770 cenlink1770

/-! ### `N = 1771` -/

def pL1771 : Prm := ⟨80, 37, 40, 1773, 11, 18446744073709551616, 108659153320509807, 108659153320509807⟩
def pH1771 : Prm := ⟨80, 37, 40, 1773, 11, 18446744073709551616, 108660252832137583, 108660252832137583⟩
def pI1771 : Prm := ⟨67, 34, 30, 1773, 11, 18446744073709551616, 108659153320509807, 108660252832137583⟩
noncomputable def L1771_cp1 : Nat × Nat := t7val% (fastRun pL1771 1 1021 (init pL1771) (init pL1771))
theorem L1771_seg1 : segOK pL1771 1 1021 (init pL1771) (init pL1771) L1771_cp1.1 L1771_cp1.2 = true := by
  decide +kernel
noncomputable def L1771_cp2 : Nat × Nat := t7val% (fastRun pL1771 1 1445 (init pL1771) (init pL1771))
theorem L1771_seg2 : segOK pL1771 1022 424 L1771_cp1.1 L1771_cp1.2 L1771_cp2.1 L1771_cp2.2 = true := by
  decide +kernel
theorem L1771_fin : (prmOK pL1771 1771 && ptTest pL1771 (runFrom pL1771 (fmask pL1771) (cmask pL1771) (hmask pL1771) 1446 325 (true, L1771_cp2.1, L1771_cp2.2)) 1771 886 false) = true := by
  decide +kernel
theorem L1771_ok : RunOK pL1771 1771 (runFrom pL1771 (fmask pL1771) (cmask pL1771) (hmask pL1771) 1446 325 (true, L1771_cp2.1, L1771_cp2.2)) ∧ ptTest pL1771 (runFrom pL1771 (fmask pL1771) (cmask pL1771) (hmask pL1771) 1446 325 (true, L1771_cp2.1, L1771_cp2.2)) 1771 886 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1771_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1771_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1771_fin) true) L1771_seg1) L1771_seg2) (by decide) rfl L1771_fin ptTest_fst
noncomputable def H1771_cp1 : Nat × Nat := t7val% (fastRun pH1771 1 1021 (init pH1771) (init pH1771))
theorem H1771_seg1 : segOK pH1771 1 1021 (init pH1771) (init pH1771) H1771_cp1.1 H1771_cp1.2 = true := by
  decide +kernel
noncomputable def H1771_cp2 : Nat × Nat := t7val% (fastRun pH1771 1 1445 (init pH1771) (init pH1771))
theorem H1771_seg2 : segOK pH1771 1022 424 H1771_cp1.1 H1771_cp1.2 H1771_cp2.1 H1771_cp2.2 = true := by
  decide +kernel
theorem H1771_fin : (prmOK pH1771 1771 && ptTest pH1771 (runFrom pH1771 (fmask pH1771) (cmask pH1771) (hmask pH1771) 1446 325 (true, H1771_cp2.1, H1771_cp2.2)) 1771 886 true) = true := by
  decide +kernel
theorem H1771_ok : RunOK pH1771 1771 (runFrom pH1771 (fmask pH1771) (cmask pH1771) (hmask pH1771) 1446 325 (true, H1771_cp2.1, H1771_cp2.2)) ∧ ptTest pH1771 (runFrom pH1771 (fmask pH1771) (cmask pH1771) (hmask pH1771) 1446 325 (true, H1771_cp2.1, H1771_cp2.2)) 1771 886 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1771_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1771_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1771_fin) true) H1771_seg1) H1771_seg2) (by decide) rfl H1771_fin ptTest_fst
noncomputable def I1771_cp1 : Nat × Nat := t7val% (fastRun pI1771 1 1251 (init pI1771) (init pI1771))
theorem I1771_seg1 : segOK pI1771 1 1251 (init pI1771) (init pI1771) I1771_cp1.1 I1771_cp1.2 = true := by
  decide +kernel
theorem I1771_fin : (prmOK pI1771 1771 && intTest pI1771 (runFrom pI1771 (fmask pI1771) (cmask pI1771) (hmask pI1771) 1252 519 (true, I1771_cp1.1, I1771_cp1.2)) 1771 21 false) = true := by
  decide +kernel
theorem I1771_ok : RunOK pI1771 1771 (runFrom pI1771 (fmask pI1771) (cmask pI1771) (hmask pI1771) 1252 519 (true, I1771_cp1.1, I1771_cp1.2)) ∧ intTest pI1771 (runFrom pI1771 (fmask pI1771) (cmask pI1771) (hmask pI1771) 1252 519 (true, I1771_cp1.1, I1771_cp1.2)) 1771 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1771_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1771_fin) true) I1771_seg1) (by decide) rfl I1771_fin intTest_fst
theorem link1771 : linkOK pL1771 pH1771 pI1771 = true := by decide +kernel
theorem cvx1771 : ConvexBetweenHumps 1771 :=
  cvx_of L1771_ok H1771_ok I1771_ok link1771 (by decide)

/-! ### The range -/

theorem cvx_1760_1771 {N : ℕ} (h1 : 1760 ≤ N) (h2 : N ≤ 1771) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1765
  · by_cases h4 : N ≤ 1762
    · by_cases h6 : N ≤ 1760
      · obtain rfl : N = 1760 := by omega
        exact cvx1760
      · by_cases h8 : N ≤ 1761
        · obtain rfl : N = 1761 := by omega
          exact cvx1761
        · obtain rfl : N = 1762 := by omega
          exact cvx1762
    · by_cases h6 : N ≤ 1763
      · obtain rfl : N = 1763 := by omega
        exact cvx1763
      · by_cases h8 : N ≤ 1764
        · obtain rfl : N = 1764 := by omega
          exact cvx1764
        · obtain rfl : N = 1765 := by omega
          exact cvx1765
  · by_cases h4 : N ≤ 1768
    · by_cases h6 : N ≤ 1766
      · obtain rfl : N = 1766 := by omega
        exact cvx1766
      · by_cases h8 : N ≤ 1767
        · obtain rfl : N = 1767 := by omega
          exact cvx1767
        · obtain rfl : N = 1768 := by omega
          exact cvx1768
    · by_cases h6 : N ≤ 1769
      · obtain rfl : N = 1769 := by omega
        exact cvx1769
      · by_cases h8 : N ≤ 1770
        · obtain rfl : N = 1770 := by omega
          exact cvx1770
        · obtain rfl : N = 1771 := by omega
          exact cvx1771

theorem cen_1760_1771 {N : ℕ} (h1 : 1760 ≤ N) (h2 : N ≤ 1771) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1764
  · by_cases h4 : N ≤ 1760
    · obtain rfl : N = 1760 := by omega
      exact cen1760
    · by_cases h6 : N ≤ 1762
      · obtain rfl : N = 1762 := by omega
        exact cen1762
      · obtain rfl : N = 1764 := by omega
        exact cen1764
  · by_cases h4 : N ≤ 1766
    · obtain rfl : N = 1766 := by omega
      exact cen1766
    · by_cases h6 : N ≤ 1768
      · obtain rfl : N = 1768 := by omega
        exact cen1768
      · obtain rfl : N = 1770 := by omega
        exact cen1770

end Kagey131.PaperD.T7
