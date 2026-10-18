import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1513, …, 1529` (generated)

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

/-! ### `N = 1513` -/

def pL1513 : Prm := ⟨80, 38, 39, 1515, 11, 18446744073709551616, 123568857908503634, 123568857908503634⟩
def pH1513 : Prm := ⟨80, 38, 39, 1515, 11, 18446744073709551616, 123569957420131410, 123569957420131410⟩
def pI1513 : Prm := ⟨66, 33, 30, 1515, 11, 18446744073709551616, 123568857908503634, 123569957420131410⟩
noncomputable def L1513_cp1 : Nat × Nat := t7val% (fastRun pL1513 1 1069 (init pL1513) (init pL1513))
theorem L1513_seg1 : segOK pL1513 1 1069 (init pL1513) (init pL1513) L1513_cp1.1 L1513_cp1.2 = true := by
  decide +kernel
theorem L1513_fin : (prmOK pL1513 1513 && ptTest pL1513 (runFrom pL1513 (fmask pL1513) (cmask pL1513) (hmask pL1513) 1070 443 (true, L1513_cp1.1, L1513_cp1.2)) 1513 757 false) = true := by
  decide +kernel
theorem L1513_ok : RunOK pL1513 1513 (runFrom pL1513 (fmask pL1513) (cmask pL1513) (hmask pL1513) 1070 443 (true, L1513_cp1.1, L1513_cp1.2)) ∧ ptTest pL1513 (runFrom pL1513 (fmask pL1513) (cmask pL1513) (hmask pL1513) 1070 443 (true, L1513_cp1.1, L1513_cp1.2)) 1513 757 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1513_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1513_fin) true) L1513_seg1) (by decide) rfl L1513_fin ptTest_fst
noncomputable def H1513_cp1 : Nat × Nat := t7val% (fastRun pH1513 1 1069 (init pH1513) (init pH1513))
theorem H1513_seg1 : segOK pH1513 1 1069 (init pH1513) (init pH1513) H1513_cp1.1 H1513_cp1.2 = true := by
  decide +kernel
theorem H1513_fin : (prmOK pH1513 1513 && ptTest pH1513 (runFrom pH1513 (fmask pH1513) (cmask pH1513) (hmask pH1513) 1070 443 (true, H1513_cp1.1, H1513_cp1.2)) 1513 757 true) = true := by
  decide +kernel
theorem H1513_ok : RunOK pH1513 1513 (runFrom pH1513 (fmask pH1513) (cmask pH1513) (hmask pH1513) 1070 443 (true, H1513_cp1.1, H1513_cp1.2)) ∧ ptTest pH1513 (runFrom pH1513 (fmask pH1513) (cmask pH1513) (hmask pH1513) 1070 443 (true, H1513_cp1.1, H1513_cp1.2)) 1513 757 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1513_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1513_fin) true) H1513_seg1) (by decide) rfl H1513_fin ptTest_fst
noncomputable def I1513_cp1 : Nat × Nat := t7val% (fastRun pI1513 1 1069 (init pI1513) (init pI1513))
theorem I1513_seg1 : segOK pI1513 1 1069 (init pI1513) (init pI1513) I1513_cp1.1 I1513_cp1.2 = true := by
  decide +kernel
theorem I1513_fin : (prmOK pI1513 1513 && intTest pI1513 (runFrom pI1513 (fmask pI1513) (cmask pI1513) (hmask pI1513) 1070 443 (true, I1513_cp1.1, I1513_cp1.2)) 1513 20 false) = true := by
  decide +kernel
theorem I1513_ok : RunOK pI1513 1513 (runFrom pI1513 (fmask pI1513) (cmask pI1513) (hmask pI1513) 1070 443 (true, I1513_cp1.1, I1513_cp1.2)) ∧ intTest pI1513 (runFrom pI1513 (fmask pI1513) (cmask pI1513) (hmask pI1513) 1070 443 (true, I1513_cp1.1, I1513_cp1.2)) 1513 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1513_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1513_fin) true) I1513_seg1) (by decide) rfl I1513_fin intTest_fst
theorem link1513 : linkOK pL1513 pH1513 pI1513 = true := by decide +kernel
theorem cvx1513 : ConvexBetweenHumps 1513 :=
  cvx_of L1513_ok H1513_ok I1513_ok link1513 (by decide)

/-! ### `N = 1514` -/

def pL1514 : Prm := ⟨80, 38, 39, 1516, 11, 18446744073709551616, 123502435285889896, 123502435285889896⟩
def pH1514 : Prm := ⟨80, 38, 39, 1516, 11, 18446744073709551616, 123503534797517672, 123503534797517672⟩
def pI1514 : Prm := ⟨66, 33, 30, 1516, 11, 18446744073709551616, 123502435285889896, 123503534797517672⟩
noncomputable def L1514_cp1 : Nat × Nat := t7val% (fastRun pL1514 1 1070 (init pL1514) (init pL1514))
theorem L1514_seg1 : segOK pL1514 1 1070 (init pL1514) (init pL1514) L1514_cp1.1 L1514_cp1.2 = true := by
  decide +kernel
theorem L1514_fin : (prmOK pL1514 1514 && ptTest pL1514 (runFrom pL1514 (fmask pL1514) (cmask pL1514) (hmask pL1514) 1071 443 (true, L1514_cp1.1, L1514_cp1.2)) 1514 757 false) = true := by
  decide +kernel
theorem L1514_ok : RunOK pL1514 1514 (runFrom pL1514 (fmask pL1514) (cmask pL1514) (hmask pL1514) 1071 443 (true, L1514_cp1.1, L1514_cp1.2)) ∧ ptTest pL1514 (runFrom pL1514 (fmask pL1514) (cmask pL1514) (hmask pL1514) 1071 443 (true, L1514_cp1.1, L1514_cp1.2)) 1514 757 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1514_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1514_fin) true) L1514_seg1) (by decide) rfl L1514_fin ptTest_fst
noncomputable def H1514_cp1 : Nat × Nat := t7val% (fastRun pH1514 1 1070 (init pH1514) (init pH1514))
theorem H1514_seg1 : segOK pH1514 1 1070 (init pH1514) (init pH1514) H1514_cp1.1 H1514_cp1.2 = true := by
  decide +kernel
theorem H1514_fin : (prmOK pH1514 1514 && ptTest pH1514 (runFrom pH1514 (fmask pH1514) (cmask pH1514) (hmask pH1514) 1071 443 (true, H1514_cp1.1, H1514_cp1.2)) 1514 757 true) = true := by
  decide +kernel
theorem H1514_ok : RunOK pH1514 1514 (runFrom pH1514 (fmask pH1514) (cmask pH1514) (hmask pH1514) 1071 443 (true, H1514_cp1.1, H1514_cp1.2)) ∧ ptTest pH1514 (runFrom pH1514 (fmask pH1514) (cmask pH1514) (hmask pH1514) 1071 443 (true, H1514_cp1.1, H1514_cp1.2)) 1514 757 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1514_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1514_fin) true) H1514_seg1) (by decide) rfl H1514_fin ptTest_fst
noncomputable def I1514_cp1 : Nat × Nat := t7val% (fastRun pI1514 1 1070 (init pI1514) (init pI1514))
theorem I1514_seg1 : segOK pI1514 1 1070 (init pI1514) (init pI1514) I1514_cp1.1 I1514_cp1.2 = true := by
  decide +kernel
theorem I1514_fin : (prmOK pI1514 1514 && intTest pI1514 (runFrom pI1514 (fmask pI1514) (cmask pI1514) (hmask pI1514) 1071 443 (true, I1514_cp1.1, I1514_cp1.2)) 1514 20 true) = true := by
  decide +kernel
theorem I1514_ok : RunOK pI1514 1514 (runFrom pI1514 (fmask pI1514) (cmask pI1514) (hmask pI1514) 1071 443 (true, I1514_cp1.1, I1514_cp1.2)) ∧ intTest pI1514 (runFrom pI1514 (fmask pI1514) (cmask pI1514) (hmask pI1514) 1071 443 (true, I1514_cp1.1, I1514_cp1.2)) 1514 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1514_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1514_fin) true) I1514_seg1) (by decide) rfl I1514_fin intTest_fst
theorem link1514 : linkOK pL1514 pH1514 pI1514 = true := by decide +kernel
theorem cvx1514 : ConvexBetweenHumps 1514 :=
  cvx_of L1514_ok H1514_ok I1514_ok link1514 (by decide)
theorem cenlink1514 : cenLinkOK pI1514 1514 = true := by decide +kernel
theorem cen1514 : CenterUniqueMin 1514 ∧ DipHyp 1514 ∧ OnePointHyps 1514 :=
  cen_of L1514_ok H1514_ok I1514_ok link1514 cenlink1514

/-! ### `N = 1515` -/

def pL1515 : Prm := ⟨80, 38, 39, 1517, 11, 18446744073709551616, 123436057740090464, 123436057740090464⟩
def pH1515 : Prm := ⟨80, 38, 39, 1517, 11, 18446744073709551616, 123437157251718240, 123437157251718240⟩
def pI1515 : Prm := ⟨66, 33, 30, 1517, 11, 18446744073709551616, 123436057740090464, 123437157251718240⟩
noncomputable def L1515_cp1 : Nat × Nat := t7val% (fastRun pL1515 1 1070 (init pL1515) (init pL1515))
theorem L1515_seg1 : segOK pL1515 1 1070 (init pL1515) (init pL1515) L1515_cp1.1 L1515_cp1.2 = true := by
  decide +kernel
theorem L1515_fin : (prmOK pL1515 1515 && ptTest pL1515 (runFrom pL1515 (fmask pL1515) (cmask pL1515) (hmask pL1515) 1071 444 (true, L1515_cp1.1, L1515_cp1.2)) 1515 758 false) = true := by
  decide +kernel
theorem L1515_ok : RunOK pL1515 1515 (runFrom pL1515 (fmask pL1515) (cmask pL1515) (hmask pL1515) 1071 444 (true, L1515_cp1.1, L1515_cp1.2)) ∧ ptTest pL1515 (runFrom pL1515 (fmask pL1515) (cmask pL1515) (hmask pL1515) 1071 444 (true, L1515_cp1.1, L1515_cp1.2)) 1515 758 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1515_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1515_fin) true) L1515_seg1) (by decide) rfl L1515_fin ptTest_fst
noncomputable def H1515_cp1 : Nat × Nat := t7val% (fastRun pH1515 1 1070 (init pH1515) (init pH1515))
theorem H1515_seg1 : segOK pH1515 1 1070 (init pH1515) (init pH1515) H1515_cp1.1 H1515_cp1.2 = true := by
  decide +kernel
theorem H1515_fin : (prmOK pH1515 1515 && ptTest pH1515 (runFrom pH1515 (fmask pH1515) (cmask pH1515) (hmask pH1515) 1071 444 (true, H1515_cp1.1, H1515_cp1.2)) 1515 758 true) = true := by
  decide +kernel
theorem H1515_ok : RunOK pH1515 1515 (runFrom pH1515 (fmask pH1515) (cmask pH1515) (hmask pH1515) 1071 444 (true, H1515_cp1.1, H1515_cp1.2)) ∧ ptTest pH1515 (runFrom pH1515 (fmask pH1515) (cmask pH1515) (hmask pH1515) 1071 444 (true, H1515_cp1.1, H1515_cp1.2)) 1515 758 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1515_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1515_fin) true) H1515_seg1) (by decide) rfl H1515_fin ptTest_fst
noncomputable def I1515_cp1 : Nat × Nat := t7val% (fastRun pI1515 1 1070 (init pI1515) (init pI1515))
theorem I1515_seg1 : segOK pI1515 1 1070 (init pI1515) (init pI1515) I1515_cp1.1 I1515_cp1.2 = true := by
  decide +kernel
theorem I1515_fin : (prmOK pI1515 1515 && intTest pI1515 (runFrom pI1515 (fmask pI1515) (cmask pI1515) (hmask pI1515) 1071 444 (true, I1515_cp1.1, I1515_cp1.2)) 1515 20 false) = true := by
  decide +kernel
theorem I1515_ok : RunOK pI1515 1515 (runFrom pI1515 (fmask pI1515) (cmask pI1515) (hmask pI1515) 1071 444 (true, I1515_cp1.1, I1515_cp1.2)) ∧ intTest pI1515 (runFrom pI1515 (fmask pI1515) (cmask pI1515) (hmask pI1515) 1071 444 (true, I1515_cp1.1, I1515_cp1.2)) 1515 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1515_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1515_fin) true) I1515_seg1) (by decide) rfl I1515_fin intTest_fst
theorem link1515 : linkOK pL1515 pH1515 pI1515 = true := by decide +kernel
theorem cvx1515 : ConvexBetweenHumps 1515 :=
  cvx_of L1515_ok H1515_ok I1515_ok link1515 (by decide)

/-! ### `N = 1516` -/

def pL1516 : Prm := ⟨80, 38, 39, 1518, 11, 18446744073709551616, 123369790272819769, 123369790272819769⟩
def pH1516 : Prm := ⟨80, 38, 39, 1518, 11, 18446744073709551616, 123370889784447545, 123370889784447545⟩
def pI1516 : Prm := ⟨66, 33, 30, 1518, 11, 18446744073709551616, 123369790272819769, 123370889784447545⟩
noncomputable def L1516_cp1 : Nat × Nat := t7val% (fastRun pL1516 1 1071 (init pL1516) (init pL1516))
theorem L1516_seg1 : segOK pL1516 1 1071 (init pL1516) (init pL1516) L1516_cp1.1 L1516_cp1.2 = true := by
  decide +kernel
theorem L1516_fin : (prmOK pL1516 1516 && ptTest pL1516 (runFrom pL1516 (fmask pL1516) (cmask pL1516) (hmask pL1516) 1072 444 (true, L1516_cp1.1, L1516_cp1.2)) 1516 758 false) = true := by
  decide +kernel
theorem L1516_ok : RunOK pL1516 1516 (runFrom pL1516 (fmask pL1516) (cmask pL1516) (hmask pL1516) 1072 444 (true, L1516_cp1.1, L1516_cp1.2)) ∧ ptTest pL1516 (runFrom pL1516 (fmask pL1516) (cmask pL1516) (hmask pL1516) 1072 444 (true, L1516_cp1.1, L1516_cp1.2)) 1516 758 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1516_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1516_fin) true) L1516_seg1) (by decide) rfl L1516_fin ptTest_fst
noncomputable def H1516_cp1 : Nat × Nat := t7val% (fastRun pH1516 1 1071 (init pH1516) (init pH1516))
theorem H1516_seg1 : segOK pH1516 1 1071 (init pH1516) (init pH1516) H1516_cp1.1 H1516_cp1.2 = true := by
  decide +kernel
theorem H1516_fin : (prmOK pH1516 1516 && ptTest pH1516 (runFrom pH1516 (fmask pH1516) (cmask pH1516) (hmask pH1516) 1072 444 (true, H1516_cp1.1, H1516_cp1.2)) 1516 758 true) = true := by
  decide +kernel
theorem H1516_ok : RunOK pH1516 1516 (runFrom pH1516 (fmask pH1516) (cmask pH1516) (hmask pH1516) 1072 444 (true, H1516_cp1.1, H1516_cp1.2)) ∧ ptTest pH1516 (runFrom pH1516 (fmask pH1516) (cmask pH1516) (hmask pH1516) 1072 444 (true, H1516_cp1.1, H1516_cp1.2)) 1516 758 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1516_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1516_fin) true) H1516_seg1) (by decide) rfl H1516_fin ptTest_fst
noncomputable def I1516_cp1 : Nat × Nat := t7val% (fastRun pI1516 1 1071 (init pI1516) (init pI1516))
theorem I1516_seg1 : segOK pI1516 1 1071 (init pI1516) (init pI1516) I1516_cp1.1 I1516_cp1.2 = true := by
  decide +kernel
theorem I1516_fin : (prmOK pI1516 1516 && intTest pI1516 (runFrom pI1516 (fmask pI1516) (cmask pI1516) (hmask pI1516) 1072 444 (true, I1516_cp1.1, I1516_cp1.2)) 1516 20 true) = true := by
  decide +kernel
theorem I1516_ok : RunOK pI1516 1516 (runFrom pI1516 (fmask pI1516) (cmask pI1516) (hmask pI1516) 1072 444 (true, I1516_cp1.1, I1516_cp1.2)) ∧ intTest pI1516 (runFrom pI1516 (fmask pI1516) (cmask pI1516) (hmask pI1516) 1072 444 (true, I1516_cp1.1, I1516_cp1.2)) 1516 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1516_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1516_fin) true) I1516_seg1) (by decide) rfl I1516_fin intTest_fst
theorem link1516 : linkOK pL1516 pH1516 pI1516 = true := by decide +kernel
theorem cvx1516 : ConvexBetweenHumps 1516 :=
  cvx_of L1516_ok H1516_ok I1516_ok link1516 (by decide)
theorem cenlink1516 : cenLinkOK pI1516 1516 = true := by decide +kernel
theorem cen1516 : CenterUniqueMin 1516 ∧ DipHyp 1516 ∧ OnePointHyps 1516 :=
  cen_of L1516_ok H1516_ok I1516_ok link1516 cenlink1516

/-! ### `N = 1517` -/

def pL1517 : Prm := ⟨80, 38, 39, 1519, 11, 18446744073709551616, 123303567732649605, 123303567732649605⟩
def pH1517 : Prm := ⟨80, 38, 39, 1519, 11, 18446744073709551616, 123304667244277381, 123304667244277381⟩
def pI1517 : Prm := ⟨66, 33, 30, 1519, 11, 18446744073709551616, 123303567732649605, 123304667244277381⟩
noncomputable def L1517_cp1 : Nat × Nat := t7val% (fastRun pL1517 1 1072 (init pL1517) (init pL1517))
theorem L1517_seg1 : segOK pL1517 1 1072 (init pL1517) (init pL1517) L1517_cp1.1 L1517_cp1.2 = true := by
  decide +kernel
theorem L1517_fin : (prmOK pL1517 1517 && ptTest pL1517 (runFrom pL1517 (fmask pL1517) (cmask pL1517) (hmask pL1517) 1073 444 (true, L1517_cp1.1, L1517_cp1.2)) 1517 759 false) = true := by
  decide +kernel
theorem L1517_ok : RunOK pL1517 1517 (runFrom pL1517 (fmask pL1517) (cmask pL1517) (hmask pL1517) 1073 444 (true, L1517_cp1.1, L1517_cp1.2)) ∧ ptTest pL1517 (runFrom pL1517 (fmask pL1517) (cmask pL1517) (hmask pL1517) 1073 444 (true, L1517_cp1.1, L1517_cp1.2)) 1517 759 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1517_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1517_fin) true) L1517_seg1) (by decide) rfl L1517_fin ptTest_fst
noncomputable def H1517_cp1 : Nat × Nat := t7val% (fastRun pH1517 1 1072 (init pH1517) (init pH1517))
theorem H1517_seg1 : segOK pH1517 1 1072 (init pH1517) (init pH1517) H1517_cp1.1 H1517_cp1.2 = true := by
  decide +kernel
theorem H1517_fin : (prmOK pH1517 1517 && ptTest pH1517 (runFrom pH1517 (fmask pH1517) (cmask pH1517) (hmask pH1517) 1073 444 (true, H1517_cp1.1, H1517_cp1.2)) 1517 759 true) = true := by
  decide +kernel
theorem H1517_ok : RunOK pH1517 1517 (runFrom pH1517 (fmask pH1517) (cmask pH1517) (hmask pH1517) 1073 444 (true, H1517_cp1.1, H1517_cp1.2)) ∧ ptTest pH1517 (runFrom pH1517 (fmask pH1517) (cmask pH1517) (hmask pH1517) 1073 444 (true, H1517_cp1.1, H1517_cp1.2)) 1517 759 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1517_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1517_fin) true) H1517_seg1) (by decide) rfl H1517_fin ptTest_fst
noncomputable def I1517_cp1 : Nat × Nat := t7val% (fastRun pI1517 1 1072 (init pI1517) (init pI1517))
theorem I1517_seg1 : segOK pI1517 1 1072 (init pI1517) (init pI1517) I1517_cp1.1 I1517_cp1.2 = true := by
  decide +kernel
theorem I1517_fin : (prmOK pI1517 1517 && intTest pI1517 (runFrom pI1517 (fmask pI1517) (cmask pI1517) (hmask pI1517) 1073 444 (true, I1517_cp1.1, I1517_cp1.2)) 1517 20 false) = true := by
  decide +kernel
theorem I1517_ok : RunOK pI1517 1517 (runFrom pI1517 (fmask pI1517) (cmask pI1517) (hmask pI1517) 1073 444 (true, I1517_cp1.1, I1517_cp1.2)) ∧ intTest pI1517 (runFrom pI1517 (fmask pI1517) (cmask pI1517) (hmask pI1517) 1073 444 (true, I1517_cp1.1, I1517_cp1.2)) 1517 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1517_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1517_fin) true) I1517_seg1) (by decide) rfl I1517_fin intTest_fst
theorem link1517 : linkOK pL1517 pH1517 pI1517 = true := by decide +kernel
theorem cvx1517 : ConvexBetweenHumps 1517 :=
  cvx_of L1517_ok H1517_ok I1517_ok link1517 (by decide)

/-! ### `N = 1518` -/

def pL1518 : Prm := ⟨80, 38, 39, 1520, 11, 18446744073709551616, 123237454860457441, 123237454860457441⟩
def pH1518 : Prm := ⟨80, 38, 39, 1520, 11, 18446744073709551616, 123238554372085217, 123238554372085217⟩
def pI1518 : Prm := ⟨66, 33, 30, 1520, 11, 18446744073709551616, 123237454860457441, 123238554372085217⟩
noncomputable def L1518_cp1 : Nat × Nat := t7val% (fastRun pL1518 1 1072 (init pL1518) (init pL1518))
theorem L1518_seg1 : segOK pL1518 1 1072 (init pL1518) (init pL1518) L1518_cp1.1 L1518_cp1.2 = true := by
  decide +kernel
theorem L1518_fin : (prmOK pL1518 1518 && ptTest pL1518 (runFrom pL1518 (fmask pL1518) (cmask pL1518) (hmask pL1518) 1073 445 (true, L1518_cp1.1, L1518_cp1.2)) 1518 759 false) = true := by
  decide +kernel
theorem L1518_ok : RunOK pL1518 1518 (runFrom pL1518 (fmask pL1518) (cmask pL1518) (hmask pL1518) 1073 445 (true, L1518_cp1.1, L1518_cp1.2)) ∧ ptTest pL1518 (runFrom pL1518 (fmask pL1518) (cmask pL1518) (hmask pL1518) 1073 445 (true, L1518_cp1.1, L1518_cp1.2)) 1518 759 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1518_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1518_fin) true) L1518_seg1) (by decide) rfl L1518_fin ptTest_fst
noncomputable def H1518_cp1 : Nat × Nat := t7val% (fastRun pH1518 1 1072 (init pH1518) (init pH1518))
theorem H1518_seg1 : segOK pH1518 1 1072 (init pH1518) (init pH1518) H1518_cp1.1 H1518_cp1.2 = true := by
  decide +kernel
theorem H1518_fin : (prmOK pH1518 1518 && ptTest pH1518 (runFrom pH1518 (fmask pH1518) (cmask pH1518) (hmask pH1518) 1073 445 (true, H1518_cp1.1, H1518_cp1.2)) 1518 759 true) = true := by
  decide +kernel
theorem H1518_ok : RunOK pH1518 1518 (runFrom pH1518 (fmask pH1518) (cmask pH1518) (hmask pH1518) 1073 445 (true, H1518_cp1.1, H1518_cp1.2)) ∧ ptTest pH1518 (runFrom pH1518 (fmask pH1518) (cmask pH1518) (hmask pH1518) 1073 445 (true, H1518_cp1.1, H1518_cp1.2)) 1518 759 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1518_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1518_fin) true) H1518_seg1) (by decide) rfl H1518_fin ptTest_fst
noncomputable def I1518_cp1 : Nat × Nat := t7val% (fastRun pI1518 1 1072 (init pI1518) (init pI1518))
theorem I1518_seg1 : segOK pI1518 1 1072 (init pI1518) (init pI1518) I1518_cp1.1 I1518_cp1.2 = true := by
  decide +kernel
theorem I1518_fin : (prmOK pI1518 1518 && intTest pI1518 (runFrom pI1518 (fmask pI1518) (cmask pI1518) (hmask pI1518) 1073 445 (true, I1518_cp1.1, I1518_cp1.2)) 1518 20 true) = true := by
  decide +kernel
theorem I1518_ok : RunOK pI1518 1518 (runFrom pI1518 (fmask pI1518) (cmask pI1518) (hmask pI1518) 1073 445 (true, I1518_cp1.1, I1518_cp1.2)) ∧ intTest pI1518 (runFrom pI1518 (fmask pI1518) (cmask pI1518) (hmask pI1518) 1073 445 (true, I1518_cp1.1, I1518_cp1.2)) 1518 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1518_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1518_fin) true) I1518_seg1) (by decide) rfl I1518_fin intTest_fst
theorem link1518 : linkOK pL1518 pH1518 pI1518 = true := by decide +kernel
theorem cvx1518 : ConvexBetweenHumps 1518 :=
  cvx_of L1518_ok H1518_ok I1518_ok link1518 (by decide)
theorem cenlink1518 : cenLinkOK pI1518 1518 = true := by decide +kernel
theorem cen1518 : CenterUniqueMin 1518 ∧ DipHyp 1518 ∧ OnePointHyps 1518 :=
  cen_of L1518_ok H1518_ok I1518_ok link1518 cenlink1518

/-! ### `N = 1519` -/

def pL1519 : Prm := ⟨80, 38, 39, 1521, 11, 18446744073709551616, 123171386766334565, 123171386766334565⟩
def pH1519 : Prm := ⟨80, 38, 39, 1521, 11, 18446744073709551616, 123172486277962341, 123172486277962341⟩
def pI1519 : Prm := ⟨66, 33, 30, 1521, 11, 18446744073709551616, 123171386766334565, 123172486277962341⟩
noncomputable def L1519_cp1 : Nat × Nat := t7val% (fastRun pL1519 1 1073 (init pL1519) (init pL1519))
theorem L1519_seg1 : segOK pL1519 1 1073 (init pL1519) (init pL1519) L1519_cp1.1 L1519_cp1.2 = true := by
  decide +kernel
theorem L1519_fin : (prmOK pL1519 1519 && ptTest pL1519 (runFrom pL1519 (fmask pL1519) (cmask pL1519) (hmask pL1519) 1074 445 (true, L1519_cp1.1, L1519_cp1.2)) 1519 760 false) = true := by
  decide +kernel
theorem L1519_ok : RunOK pL1519 1519 (runFrom pL1519 (fmask pL1519) (cmask pL1519) (hmask pL1519) 1074 445 (true, L1519_cp1.1, L1519_cp1.2)) ∧ ptTest pL1519 (runFrom pL1519 (fmask pL1519) (cmask pL1519) (hmask pL1519) 1074 445 (true, L1519_cp1.1, L1519_cp1.2)) 1519 760 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1519_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1519_fin) true) L1519_seg1) (by decide) rfl L1519_fin ptTest_fst
noncomputable def H1519_cp1 : Nat × Nat := t7val% (fastRun pH1519 1 1073 (init pH1519) (init pH1519))
theorem H1519_seg1 : segOK pH1519 1 1073 (init pH1519) (init pH1519) H1519_cp1.1 H1519_cp1.2 = true := by
  decide +kernel
theorem H1519_fin : (prmOK pH1519 1519 && ptTest pH1519 (runFrom pH1519 (fmask pH1519) (cmask pH1519) (hmask pH1519) 1074 445 (true, H1519_cp1.1, H1519_cp1.2)) 1519 760 true) = true := by
  decide +kernel
theorem H1519_ok : RunOK pH1519 1519 (runFrom pH1519 (fmask pH1519) (cmask pH1519) (hmask pH1519) 1074 445 (true, H1519_cp1.1, H1519_cp1.2)) ∧ ptTest pH1519 (runFrom pH1519 (fmask pH1519) (cmask pH1519) (hmask pH1519) 1074 445 (true, H1519_cp1.1, H1519_cp1.2)) 1519 760 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1519_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1519_fin) true) H1519_seg1) (by decide) rfl H1519_fin ptTest_fst
noncomputable def I1519_cp1 : Nat × Nat := t7val% (fastRun pI1519 1 1073 (init pI1519) (init pI1519))
theorem I1519_seg1 : segOK pI1519 1 1073 (init pI1519) (init pI1519) I1519_cp1.1 I1519_cp1.2 = true := by
  decide +kernel
theorem I1519_fin : (prmOK pI1519 1519 && intTest pI1519 (runFrom pI1519 (fmask pI1519) (cmask pI1519) (hmask pI1519) 1074 445 (true, I1519_cp1.1, I1519_cp1.2)) 1519 20 false) = true := by
  decide +kernel
theorem I1519_ok : RunOK pI1519 1519 (runFrom pI1519 (fmask pI1519) (cmask pI1519) (hmask pI1519) 1074 445 (true, I1519_cp1.1, I1519_cp1.2)) ∧ intTest pI1519 (runFrom pI1519 (fmask pI1519) (cmask pI1519) (hmask pI1519) 1074 445 (true, I1519_cp1.1, I1519_cp1.2)) 1519 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1519_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1519_fin) true) I1519_seg1) (by decide) rfl I1519_fin intTest_fst
theorem link1519 : linkOK pL1519 pH1519 pI1519 = true := by decide +kernel
theorem cvx1519 : ConvexBetweenHumps 1519 :=
  cvx_of L1519_ok H1519_ok I1519_ok link1519 (by decide)

/-! ### `N = 1520` -/

def pL1520 : Prm := ⟨80, 38, 39, 1522, 11, 18446744073709551616, 123105427931686540, 123105427931686540⟩
def pH1520 : Prm := ⟨80, 38, 39, 1522, 11, 18446744073709551616, 123106527443314316, 123106527443314316⟩
def pI1520 : Prm := ⟨66, 33, 30, 1522, 11, 18446744073709551616, 123105427931686540, 123106527443314316⟩
noncomputable def L1520_cp1 : Nat × Nat := t7val% (fastRun pL1520 1 1074 (init pL1520) (init pL1520))
theorem L1520_seg1 : segOK pL1520 1 1074 (init pL1520) (init pL1520) L1520_cp1.1 L1520_cp1.2 = true := by
  decide +kernel
theorem L1520_fin : (prmOK pL1520 1520 && ptTest pL1520 (runFrom pL1520 (fmask pL1520) (cmask pL1520) (hmask pL1520) 1075 445 (true, L1520_cp1.1, L1520_cp1.2)) 1520 760 false) = true := by
  decide +kernel
theorem L1520_ok : RunOK pL1520 1520 (runFrom pL1520 (fmask pL1520) (cmask pL1520) (hmask pL1520) 1075 445 (true, L1520_cp1.1, L1520_cp1.2)) ∧ ptTest pL1520 (runFrom pL1520 (fmask pL1520) (cmask pL1520) (hmask pL1520) 1075 445 (true, L1520_cp1.1, L1520_cp1.2)) 1520 760 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1520_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1520_fin) true) L1520_seg1) (by decide) rfl L1520_fin ptTest_fst
noncomputable def H1520_cp1 : Nat × Nat := t7val% (fastRun pH1520 1 1074 (init pH1520) (init pH1520))
theorem H1520_seg1 : segOK pH1520 1 1074 (init pH1520) (init pH1520) H1520_cp1.1 H1520_cp1.2 = true := by
  decide +kernel
theorem H1520_fin : (prmOK pH1520 1520 && ptTest pH1520 (runFrom pH1520 (fmask pH1520) (cmask pH1520) (hmask pH1520) 1075 445 (true, H1520_cp1.1, H1520_cp1.2)) 1520 760 true) = true := by
  decide +kernel
theorem H1520_ok : RunOK pH1520 1520 (runFrom pH1520 (fmask pH1520) (cmask pH1520) (hmask pH1520) 1075 445 (true, H1520_cp1.1, H1520_cp1.2)) ∧ ptTest pH1520 (runFrom pH1520 (fmask pH1520) (cmask pH1520) (hmask pH1520) 1075 445 (true, H1520_cp1.1, H1520_cp1.2)) 1520 760 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1520_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1520_fin) true) H1520_seg1) (by decide) rfl H1520_fin ptTest_fst
noncomputable def I1520_cp1 : Nat × Nat := t7val% (fastRun pI1520 1 1074 (init pI1520) (init pI1520))
theorem I1520_seg1 : segOK pI1520 1 1074 (init pI1520) (init pI1520) I1520_cp1.1 I1520_cp1.2 = true := by
  decide +kernel
theorem I1520_fin : (prmOK pI1520 1520 && intTest pI1520 (runFrom pI1520 (fmask pI1520) (cmask pI1520) (hmask pI1520) 1075 445 (true, I1520_cp1.1, I1520_cp1.2)) 1520 20 true) = true := by
  decide +kernel
theorem I1520_ok : RunOK pI1520 1520 (runFrom pI1520 (fmask pI1520) (cmask pI1520) (hmask pI1520) 1075 445 (true, I1520_cp1.1, I1520_cp1.2)) ∧ intTest pI1520 (runFrom pI1520 (fmask pI1520) (cmask pI1520) (hmask pI1520) 1075 445 (true, I1520_cp1.1, I1520_cp1.2)) 1520 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1520_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1520_fin) true) I1520_seg1) (by decide) rfl I1520_fin intTest_fst
theorem link1520 : linkOK pL1520 pH1520 pI1520 = true := by decide +kernel
theorem cvx1520 : ConvexBetweenHumps 1520 :=
  cvx_of L1520_ok H1520_ok I1520_ok link1520 (by decide)
theorem cenlink1520 : cenLinkOK pI1520 1520 = true := by decide +kernel
theorem cen1520 : CenterUniqueMin 1520 ∧ DipHyp 1520 ∧ OnePointHyps 1520 :=
  cen_of L1520_ok H1520_ok I1520_ok link1520 cenlink1520

/-! ### `N = 1521` -/

def pL1521 : Prm := ⟨80, 38, 39, 1523, 11, 18446744073709551616, 123039513726722193, 123039513726722193⟩
def pH1521 : Prm := ⟨81, 39, 39, 1523, 11, 18446744073709551616, 123040613238349969, 123040613238349969⟩
def pI1521 : Prm := ⟨66, 33, 30, 1523, 11, 18446744073709551616, 123039513726722193, 123040613238349969⟩
noncomputable def L1521_cp1 : Nat × Nat := t7val% (fastRun pL1521 1 1075 (init pL1521) (init pL1521))
theorem L1521_seg1 : segOK pL1521 1 1075 (init pL1521) (init pL1521) L1521_cp1.1 L1521_cp1.2 = true := by
  decide +kernel
theorem L1521_fin : (prmOK pL1521 1521 && ptTest pL1521 (runFrom pL1521 (fmask pL1521) (cmask pL1521) (hmask pL1521) 1076 445 (true, L1521_cp1.1, L1521_cp1.2)) 1521 761 false) = true := by
  decide +kernel
theorem L1521_ok : RunOK pL1521 1521 (runFrom pL1521 (fmask pL1521) (cmask pL1521) (hmask pL1521) 1076 445 (true, L1521_cp1.1, L1521_cp1.2)) ∧ ptTest pL1521 (runFrom pL1521 (fmask pL1521) (cmask pL1521) (hmask pL1521) 1076 445 (true, L1521_cp1.1, L1521_cp1.2)) 1521 761 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1521_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1521_fin) true) L1521_seg1) (by decide) rfl L1521_fin ptTest_fst
noncomputable def H1521_cp1 : Nat × Nat := t7val% (fastRun pH1521 1 1075 (init pH1521) (init pH1521))
theorem H1521_seg1 : segOK pH1521 1 1075 (init pH1521) (init pH1521) H1521_cp1.1 H1521_cp1.2 = true := by
  decide +kernel
theorem H1521_fin : (prmOK pH1521 1521 && ptTest pH1521 (runFrom pH1521 (fmask pH1521) (cmask pH1521) (hmask pH1521) 1076 445 (true, H1521_cp1.1, H1521_cp1.2)) 1521 761 true) = true := by
  decide +kernel
theorem H1521_ok : RunOK pH1521 1521 (runFrom pH1521 (fmask pH1521) (cmask pH1521) (hmask pH1521) 1076 445 (true, H1521_cp1.1, H1521_cp1.2)) ∧ ptTest pH1521 (runFrom pH1521 (fmask pH1521) (cmask pH1521) (hmask pH1521) 1076 445 (true, H1521_cp1.1, H1521_cp1.2)) 1521 761 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1521_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1521_fin) true) H1521_seg1) (by decide) rfl H1521_fin ptTest_fst
noncomputable def I1521_cp1 : Nat × Nat := t7val% (fastRun pI1521 1 1075 (init pI1521) (init pI1521))
theorem I1521_seg1 : segOK pI1521 1 1075 (init pI1521) (init pI1521) I1521_cp1.1 I1521_cp1.2 = true := by
  decide +kernel
theorem I1521_fin : (prmOK pI1521 1521 && intTest pI1521 (runFrom pI1521 (fmask pI1521) (cmask pI1521) (hmask pI1521) 1076 445 (true, I1521_cp1.1, I1521_cp1.2)) 1521 20 false) = true := by
  decide +kernel
theorem I1521_ok : RunOK pI1521 1521 (runFrom pI1521 (fmask pI1521) (cmask pI1521) (hmask pI1521) 1076 445 (true, I1521_cp1.1, I1521_cp1.2)) ∧ intTest pI1521 (runFrom pI1521 (fmask pI1521) (cmask pI1521) (hmask pI1521) 1076 445 (true, I1521_cp1.1, I1521_cp1.2)) 1521 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1521_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1521_fin) true) I1521_seg1) (by decide) rfl I1521_fin intTest_fst
theorem link1521 : linkOK pL1521 pH1521 pI1521 = true := by decide +kernel
theorem cvx1521 : ConvexBetweenHumps 1521 :=
  cvx_of L1521_ok H1521_ok I1521_ok link1521 (by decide)

/-! ### `N = 1522` -/

def pL1522 : Prm := ⟨80, 38, 39, 1524, 11, 18446744073709551616, 122973708374777140, 122973708374777140⟩
def pH1522 : Prm := ⟨80, 38, 39, 1524, 11, 18446744073709551616, 122974807886404916, 122974807886404916⟩
def pI1522 : Prm := ⟨66, 33, 30, 1524, 11, 18446744073709551616, 122973708374777140, 122974807886404916⟩
noncomputable def L1522_cp1 : Nat × Nat := t7val% (fastRun pL1522 1 1075 (init pL1522) (init pL1522))
theorem L1522_seg1 : segOK pL1522 1 1075 (init pL1522) (init pL1522) L1522_cp1.1 L1522_cp1.2 = true := by
  decide +kernel
theorem L1522_fin : (prmOK pL1522 1522 && ptTest pL1522 (runFrom pL1522 (fmask pL1522) (cmask pL1522) (hmask pL1522) 1076 446 (true, L1522_cp1.1, L1522_cp1.2)) 1522 761 false) = true := by
  decide +kernel
theorem L1522_ok : RunOK pL1522 1522 (runFrom pL1522 (fmask pL1522) (cmask pL1522) (hmask pL1522) 1076 446 (true, L1522_cp1.1, L1522_cp1.2)) ∧ ptTest pL1522 (runFrom pL1522 (fmask pL1522) (cmask pL1522) (hmask pL1522) 1076 446 (true, L1522_cp1.1, L1522_cp1.2)) 1522 761 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1522_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1522_fin) true) L1522_seg1) (by decide) rfl L1522_fin ptTest_fst
noncomputable def H1522_cp1 : Nat × Nat := t7val% (fastRun pH1522 1 1075 (init pH1522) (init pH1522))
theorem H1522_seg1 : segOK pH1522 1 1075 (init pH1522) (init pH1522) H1522_cp1.1 H1522_cp1.2 = true := by
  decide +kernel
theorem H1522_fin : (prmOK pH1522 1522 && ptTest pH1522 (runFrom pH1522 (fmask pH1522) (cmask pH1522) (hmask pH1522) 1076 446 (true, H1522_cp1.1, H1522_cp1.2)) 1522 761 true) = true := by
  decide +kernel
theorem H1522_ok : RunOK pH1522 1522 (runFrom pH1522 (fmask pH1522) (cmask pH1522) (hmask pH1522) 1076 446 (true, H1522_cp1.1, H1522_cp1.2)) ∧ ptTest pH1522 (runFrom pH1522 (fmask pH1522) (cmask pH1522) (hmask pH1522) 1076 446 (true, H1522_cp1.1, H1522_cp1.2)) 1522 761 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1522_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1522_fin) true) H1522_seg1) (by decide) rfl H1522_fin ptTest_fst
noncomputable def I1522_cp1 : Nat × Nat := t7val% (fastRun pI1522 1 1075 (init pI1522) (init pI1522))
theorem I1522_seg1 : segOK pI1522 1 1075 (init pI1522) (init pI1522) I1522_cp1.1 I1522_cp1.2 = true := by
  decide +kernel
theorem I1522_fin : (prmOK pI1522 1522 && intTest pI1522 (runFrom pI1522 (fmask pI1522) (cmask pI1522) (hmask pI1522) 1076 446 (true, I1522_cp1.1, I1522_cp1.2)) 1522 20 true) = true := by
  decide +kernel
theorem I1522_ok : RunOK pI1522 1522 (runFrom pI1522 (fmask pI1522) (cmask pI1522) (hmask pI1522) 1076 446 (true, I1522_cp1.1, I1522_cp1.2)) ∧ intTest pI1522 (runFrom pI1522 (fmask pI1522) (cmask pI1522) (hmask pI1522) 1076 446 (true, I1522_cp1.1, I1522_cp1.2)) 1522 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1522_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1522_fin) true) I1522_seg1) (by decide) rfl I1522_fin intTest_fst
theorem link1522 : linkOK pL1522 pH1522 pI1522 = true := by decide +kernel
theorem cvx1522 : ConvexBetweenHumps 1522 :=
  cvx_of L1522_ok H1522_ok I1522_ok link1522 (by decide)
theorem cenlink1522 : cenLinkOK pI1522 1522 = true := by decide +kernel
theorem cen1522 : CenterUniqueMin 1522 ∧ DipHyp 1522 ∧ OnePointHyps 1522 :=
  cen_of L1522_ok H1522_ok I1522_ok link1522 cenlink1522

/-! ### `N = 1523` -/

def pL1523 : Prm := ⟨80, 38, 39, 1525, 11, 18446744073709551616, 122907947504849577, 122907947504849577⟩
def pH1523 : Prm := ⟨80, 38, 39, 1525, 11, 18446744073709551616, 122909047016477353, 122909047016477353⟩
def pI1523 : Prm := ⟨66, 33, 30, 1525, 11, 18446744073709551616, 122907947504849577, 122909047016477353⟩
noncomputable def L1523_cp1 : Nat × Nat := t7val% (fastRun pL1523 1 1076 (init pL1523) (init pL1523))
theorem L1523_seg1 : segOK pL1523 1 1076 (init pL1523) (init pL1523) L1523_cp1.1 L1523_cp1.2 = true := by
  decide +kernel
theorem L1523_fin : (prmOK pL1523 1523 && ptTest pL1523 (runFrom pL1523 (fmask pL1523) (cmask pL1523) (hmask pL1523) 1077 446 (true, L1523_cp1.1, L1523_cp1.2)) 1523 762 false) = true := by
  decide +kernel
theorem L1523_ok : RunOK pL1523 1523 (runFrom pL1523 (fmask pL1523) (cmask pL1523) (hmask pL1523) 1077 446 (true, L1523_cp1.1, L1523_cp1.2)) ∧ ptTest pL1523 (runFrom pL1523 (fmask pL1523) (cmask pL1523) (hmask pL1523) 1077 446 (true, L1523_cp1.1, L1523_cp1.2)) 1523 762 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1523_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1523_fin) true) L1523_seg1) (by decide) rfl L1523_fin ptTest_fst
noncomputable def H1523_cp1 : Nat × Nat := t7val% (fastRun pH1523 1 1076 (init pH1523) (init pH1523))
theorem H1523_seg1 : segOK pH1523 1 1076 (init pH1523) (init pH1523) H1523_cp1.1 H1523_cp1.2 = true := by
  decide +kernel
theorem H1523_fin : (prmOK pH1523 1523 && ptTest pH1523 (runFrom pH1523 (fmask pH1523) (cmask pH1523) (hmask pH1523) 1077 446 (true, H1523_cp1.1, H1523_cp1.2)) 1523 762 true) = true := by
  decide +kernel
theorem H1523_ok : RunOK pH1523 1523 (runFrom pH1523 (fmask pH1523) (cmask pH1523) (hmask pH1523) 1077 446 (true, H1523_cp1.1, H1523_cp1.2)) ∧ ptTest pH1523 (runFrom pH1523 (fmask pH1523) (cmask pH1523) (hmask pH1523) 1077 446 (true, H1523_cp1.1, H1523_cp1.2)) 1523 762 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1523_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1523_fin) true) H1523_seg1) (by decide) rfl H1523_fin ptTest_fst
noncomputable def I1523_cp1 : Nat × Nat := t7val% (fastRun pI1523 1 1076 (init pI1523) (init pI1523))
theorem I1523_seg1 : segOK pI1523 1 1076 (init pI1523) (init pI1523) I1523_cp1.1 I1523_cp1.2 = true := by
  decide +kernel
theorem I1523_fin : (prmOK pI1523 1523 && intTest pI1523 (runFrom pI1523 (fmask pI1523) (cmask pI1523) (hmask pI1523) 1077 446 (true, I1523_cp1.1, I1523_cp1.2)) 1523 20 false) = true := by
  decide +kernel
theorem I1523_ok : RunOK pI1523 1523 (runFrom pI1523 (fmask pI1523) (cmask pI1523) (hmask pI1523) 1077 446 (true, I1523_cp1.1, I1523_cp1.2)) ∧ intTest pI1523 (runFrom pI1523 (fmask pI1523) (cmask pI1523) (hmask pI1523) 1077 446 (true, I1523_cp1.1, I1523_cp1.2)) 1523 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1523_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1523_fin) true) I1523_seg1) (by decide) rfl I1523_fin intTest_fst
theorem link1523 : linkOK pL1523 pH1523 pI1523 = true := by decide +kernel
theorem cvx1523 : ConvexBetweenHumps 1523 :=
  cvx_of L1523_ok H1523_ok I1523_ok link1523 (by decide)

/-! ### `N = 1524` -/

def pL1524 : Prm := ⟨80, 38, 39, 1526, 11, 18446744073709551616, 122842295083533339, 122842295083533339⟩
def pH1524 : Prm := ⟨80, 38, 39, 1526, 11, 18446744073709551616, 122843394595161115, 122843394595161115⟩
def pI1524 : Prm := ⟨66, 33, 30, 1526, 11, 18446744073709551616, 122842295083533339, 122843394595161115⟩
noncomputable def L1524_cp1 : Nat × Nat := t7val% (fastRun pL1524 1 1077 (init pL1524) (init pL1524))
theorem L1524_seg1 : segOK pL1524 1 1077 (init pL1524) (init pL1524) L1524_cp1.1 L1524_cp1.2 = true := by
  decide +kernel
theorem L1524_fin : (prmOK pL1524 1524 && ptTest pL1524 (runFrom pL1524 (fmask pL1524) (cmask pL1524) (hmask pL1524) 1078 446 (true, L1524_cp1.1, L1524_cp1.2)) 1524 762 false) = true := by
  decide +kernel
theorem L1524_ok : RunOK pL1524 1524 (runFrom pL1524 (fmask pL1524) (cmask pL1524) (hmask pL1524) 1078 446 (true, L1524_cp1.1, L1524_cp1.2)) ∧ ptTest pL1524 (runFrom pL1524 (fmask pL1524) (cmask pL1524) (hmask pL1524) 1078 446 (true, L1524_cp1.1, L1524_cp1.2)) 1524 762 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1524_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1524_fin) true) L1524_seg1) (by decide) rfl L1524_fin ptTest_fst
noncomputable def H1524_cp1 : Nat × Nat := t7val% (fastRun pH1524 1 1077 (init pH1524) (init pH1524))
theorem H1524_seg1 : segOK pH1524 1 1077 (init pH1524) (init pH1524) H1524_cp1.1 H1524_cp1.2 = true := by
  decide +kernel
theorem H1524_fin : (prmOK pH1524 1524 && ptTest pH1524 (runFrom pH1524 (fmask pH1524) (cmask pH1524) (hmask pH1524) 1078 446 (true, H1524_cp1.1, H1524_cp1.2)) 1524 762 true) = true := by
  decide +kernel
theorem H1524_ok : RunOK pH1524 1524 (runFrom pH1524 (fmask pH1524) (cmask pH1524) (hmask pH1524) 1078 446 (true, H1524_cp1.1, H1524_cp1.2)) ∧ ptTest pH1524 (runFrom pH1524 (fmask pH1524) (cmask pH1524) (hmask pH1524) 1078 446 (true, H1524_cp1.1, H1524_cp1.2)) 1524 762 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1524_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1524_fin) true) H1524_seg1) (by decide) rfl H1524_fin ptTest_fst
noncomputable def I1524_cp1 : Nat × Nat := t7val% (fastRun pI1524 1 1077 (init pI1524) (init pI1524))
theorem I1524_seg1 : segOK pI1524 1 1077 (init pI1524) (init pI1524) I1524_cp1.1 I1524_cp1.2 = true := by
  decide +kernel
theorem I1524_fin : (prmOK pI1524 1524 && intTest pI1524 (runFrom pI1524 (fmask pI1524) (cmask pI1524) (hmask pI1524) 1078 446 (true, I1524_cp1.1, I1524_cp1.2)) 1524 20 true) = true := by
  decide +kernel
theorem I1524_ok : RunOK pI1524 1524 (runFrom pI1524 (fmask pI1524) (cmask pI1524) (hmask pI1524) 1078 446 (true, I1524_cp1.1, I1524_cp1.2)) ∧ intTest pI1524 (runFrom pI1524 (fmask pI1524) (cmask pI1524) (hmask pI1524) 1078 446 (true, I1524_cp1.1, I1524_cp1.2)) 1524 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1524_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1524_fin) true) I1524_seg1) (by decide) rfl I1524_fin intTest_fst
theorem link1524 : linkOK pL1524 pH1524 pI1524 = true := by decide +kernel
theorem cvx1524 : ConvexBetweenHumps 1524 :=
  cvx_of L1524_ok H1524_ok I1524_ok link1524 (by decide)
theorem cenlink1524 : cenLinkOK pI1524 1524 = true := by decide +kernel
theorem cen1524 : CenterUniqueMin 1524 ∧ DipHyp 1524 ∧ OnePointHyps 1524 :=
  cen_of L1524_ok H1524_ok I1524_ok link1524 cenlink1524

/-! ### `N = 1525` -/

def pL1525 : Prm := ⟨80, 38, 39, 1527, 11, 18446744073709551616, 122776686997177146, 122776686997177146⟩
def pH1525 : Prm := ⟨80, 38, 39, 1527, 11, 18446744073709551616, 122777786508804922, 122777786508804922⟩
def pI1525 : Prm := ⟨66, 33, 30, 1527, 11, 18446744073709551616, 122776686997177146, 122777786508804922⟩
noncomputable def L1525_cp1 : Nat × Nat := t7val% (fastRun pL1525 1 1077 (init pL1525) (init pL1525))
theorem L1525_seg1 : segOK pL1525 1 1077 (init pL1525) (init pL1525) L1525_cp1.1 L1525_cp1.2 = true := by
  decide +kernel
theorem L1525_fin : (prmOK pL1525 1525 && ptTest pL1525 (runFrom pL1525 (fmask pL1525) (cmask pL1525) (hmask pL1525) 1078 447 (true, L1525_cp1.1, L1525_cp1.2)) 1525 763 false) = true := by
  decide +kernel
theorem L1525_ok : RunOK pL1525 1525 (runFrom pL1525 (fmask pL1525) (cmask pL1525) (hmask pL1525) 1078 447 (true, L1525_cp1.1, L1525_cp1.2)) ∧ ptTest pL1525 (runFrom pL1525 (fmask pL1525) (cmask pL1525) (hmask pL1525) 1078 447 (true, L1525_cp1.1, L1525_cp1.2)) 1525 763 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1525_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1525_fin) true) L1525_seg1) (by decide) rfl L1525_fin ptTest_fst
noncomputable def H1525_cp1 : Nat × Nat := t7val% (fastRun pH1525 1 1077 (init pH1525) (init pH1525))
theorem H1525_seg1 : segOK pH1525 1 1077 (init pH1525) (init pH1525) H1525_cp1.1 H1525_cp1.2 = true := by
  decide +kernel
theorem H1525_fin : (prmOK pH1525 1525 && ptTest pH1525 (runFrom pH1525 (fmask pH1525) (cmask pH1525) (hmask pH1525) 1078 447 (true, H1525_cp1.1, H1525_cp1.2)) 1525 763 true) = true := by
  decide +kernel
theorem H1525_ok : RunOK pH1525 1525 (runFrom pH1525 (fmask pH1525) (cmask pH1525) (hmask pH1525) 1078 447 (true, H1525_cp1.1, H1525_cp1.2)) ∧ ptTest pH1525 (runFrom pH1525 (fmask pH1525) (cmask pH1525) (hmask pH1525) 1078 447 (true, H1525_cp1.1, H1525_cp1.2)) 1525 763 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1525_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1525_fin) true) H1525_seg1) (by decide) rfl H1525_fin ptTest_fst
noncomputable def I1525_cp1 : Nat × Nat := t7val% (fastRun pI1525 1 1077 (init pI1525) (init pI1525))
theorem I1525_seg1 : segOK pI1525 1 1077 (init pI1525) (init pI1525) I1525_cp1.1 I1525_cp1.2 = true := by
  decide +kernel
theorem I1525_fin : (prmOK pI1525 1525 && intTest pI1525 (runFrom pI1525 (fmask pI1525) (cmask pI1525) (hmask pI1525) 1078 447 (true, I1525_cp1.1, I1525_cp1.2)) 1525 20 false) = true := by
  decide +kernel
theorem I1525_ok : RunOK pI1525 1525 (runFrom pI1525 (fmask pI1525) (cmask pI1525) (hmask pI1525) 1078 447 (true, I1525_cp1.1, I1525_cp1.2)) ∧ intTest pI1525 (runFrom pI1525 (fmask pI1525) (cmask pI1525) (hmask pI1525) 1078 447 (true, I1525_cp1.1, I1525_cp1.2)) 1525 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1525_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1525_fin) true) I1525_seg1) (by decide) rfl I1525_fin intTest_fst
theorem link1525 : linkOK pL1525 pH1525 pI1525 = true := by decide +kernel
theorem cvx1525 : ConvexBetweenHumps 1525 :=
  cvx_of L1525_ok H1525_ok I1525_ok link1525 (by decide)

/-! ### `N = 1526` -/

def pL1526 : Prm := ⟨80, 38, 39, 1528, 11, 18446744073709551616, 122711186957053449, 122711186957053449⟩
def pH1526 : Prm := ⟨80, 38, 39, 1528, 11, 18446744073709551616, 122712286468681225, 122712286468681225⟩
def pI1526 : Prm := ⟨66, 33, 30, 1528, 11, 18446744073709551616, 122711186957053449, 122712286468681225⟩
noncomputable def L1526_cp1 : Nat × Nat := t7val% (fastRun pL1526 1 1078 (init pL1526) (init pL1526))
theorem L1526_seg1 : segOK pL1526 1 1078 (init pL1526) (init pL1526) L1526_cp1.1 L1526_cp1.2 = true := by
  decide +kernel
theorem L1526_fin : (prmOK pL1526 1526 && ptTest pL1526 (runFrom pL1526 (fmask pL1526) (cmask pL1526) (hmask pL1526) 1079 447 (true, L1526_cp1.1, L1526_cp1.2)) 1526 763 false) = true := by
  decide +kernel
theorem L1526_ok : RunOK pL1526 1526 (runFrom pL1526 (fmask pL1526) (cmask pL1526) (hmask pL1526) 1079 447 (true, L1526_cp1.1, L1526_cp1.2)) ∧ ptTest pL1526 (runFrom pL1526 (fmask pL1526) (cmask pL1526) (hmask pL1526) 1079 447 (true, L1526_cp1.1, L1526_cp1.2)) 1526 763 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1526_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1526_fin) true) L1526_seg1) (by decide) rfl L1526_fin ptTest_fst
noncomputable def H1526_cp1 : Nat × Nat := t7val% (fastRun pH1526 1 1078 (init pH1526) (init pH1526))
theorem H1526_seg1 : segOK pH1526 1 1078 (init pH1526) (init pH1526) H1526_cp1.1 H1526_cp1.2 = true := by
  decide +kernel
theorem H1526_fin : (prmOK pH1526 1526 && ptTest pH1526 (runFrom pH1526 (fmask pH1526) (cmask pH1526) (hmask pH1526) 1079 447 (true, H1526_cp1.1, H1526_cp1.2)) 1526 763 true) = true := by
  decide +kernel
theorem H1526_ok : RunOK pH1526 1526 (runFrom pH1526 (fmask pH1526) (cmask pH1526) (hmask pH1526) 1079 447 (true, H1526_cp1.1, H1526_cp1.2)) ∧ ptTest pH1526 (runFrom pH1526 (fmask pH1526) (cmask pH1526) (hmask pH1526) 1079 447 (true, H1526_cp1.1, H1526_cp1.2)) 1526 763 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1526_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1526_fin) true) H1526_seg1) (by decide) rfl H1526_fin ptTest_fst
noncomputable def I1526_cp1 : Nat × Nat := t7val% (fastRun pI1526 1 1078 (init pI1526) (init pI1526))
theorem I1526_seg1 : segOK pI1526 1 1078 (init pI1526) (init pI1526) I1526_cp1.1 I1526_cp1.2 = true := by
  decide +kernel
theorem I1526_fin : (prmOK pI1526 1526 && intTest pI1526 (runFrom pI1526 (fmask pI1526) (cmask pI1526) (hmask pI1526) 1079 447 (true, I1526_cp1.1, I1526_cp1.2)) 1526 20 true) = true := by
  decide +kernel
theorem I1526_ok : RunOK pI1526 1526 (runFrom pI1526 (fmask pI1526) (cmask pI1526) (hmask pI1526) 1079 447 (true, I1526_cp1.1, I1526_cp1.2)) ∧ intTest pI1526 (runFrom pI1526 (fmask pI1526) (cmask pI1526) (hmask pI1526) 1079 447 (true, I1526_cp1.1, I1526_cp1.2)) 1526 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1526_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1526_fin) true) I1526_seg1) (by decide) rfl I1526_fin intTest_fst
theorem link1526 : linkOK pL1526 pH1526 pI1526 = true := by decide +kernel
theorem cvx1526 : ConvexBetweenHumps 1526 :=
  cvx_of L1526_ok H1526_ok I1526_ok link1526 (by decide)
theorem cenlink1526 : cenLinkOK pI1526 1526 = true := by decide +kernel
theorem cen1526 : CenterUniqueMin 1526 ∧ DipHyp 1526 ∧ OnePointHyps 1526 :=
  cen_of L1526_ok H1526_ok I1526_ok link1526 cenlink1526

/-! ### `N = 1527` -/

def pL1527 : Prm := ⟨80, 38, 39, 1529, 11, 18446744073709551616, 122645731105514885, 122645731105514885⟩
def pH1527 : Prm := ⟨81, 39, 39, 1529, 11, 18446744073709551616, 122646830617142661, 122646830617142661⟩
def pI1527 : Prm := ⟨66, 33, 30, 1529, 11, 18446744073709551616, 122645731105514885, 122646830617142661⟩
noncomputable def L1527_cp1 : Nat × Nat := t7val% (fastRun pL1527 1 1079 (init pL1527) (init pL1527))
theorem L1527_seg1 : segOK pL1527 1 1079 (init pL1527) (init pL1527) L1527_cp1.1 L1527_cp1.2 = true := by
  decide +kernel
theorem L1527_fin : (prmOK pL1527 1527 && ptTest pL1527 (runFrom pL1527 (fmask pL1527) (cmask pL1527) (hmask pL1527) 1080 447 (true, L1527_cp1.1, L1527_cp1.2)) 1527 764 false) = true := by
  decide +kernel
theorem L1527_ok : RunOK pL1527 1527 (runFrom pL1527 (fmask pL1527) (cmask pL1527) (hmask pL1527) 1080 447 (true, L1527_cp1.1, L1527_cp1.2)) ∧ ptTest pL1527 (runFrom pL1527 (fmask pL1527) (cmask pL1527) (hmask pL1527) 1080 447 (true, L1527_cp1.1, L1527_cp1.2)) 1527 764 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1527_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1527_fin) true) L1527_seg1) (by decide) rfl L1527_fin ptTest_fst
noncomputable def H1527_cp1 : Nat × Nat := t7val% (fastRun pH1527 1 1079 (init pH1527) (init pH1527))
theorem H1527_seg1 : segOK pH1527 1 1079 (init pH1527) (init pH1527) H1527_cp1.1 H1527_cp1.2 = true := by
  decide +kernel
theorem H1527_fin : (prmOK pH1527 1527 && ptTest pH1527 (runFrom pH1527 (fmask pH1527) (cmask pH1527) (hmask pH1527) 1080 447 (true, H1527_cp1.1, H1527_cp1.2)) 1527 764 true) = true := by
  decide +kernel
theorem H1527_ok : RunOK pH1527 1527 (runFrom pH1527 (fmask pH1527) (cmask pH1527) (hmask pH1527) 1080 447 (true, H1527_cp1.1, H1527_cp1.2)) ∧ ptTest pH1527 (runFrom pH1527 (fmask pH1527) (cmask pH1527) (hmask pH1527) 1080 447 (true, H1527_cp1.1, H1527_cp1.2)) 1527 764 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1527_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1527_fin) true) H1527_seg1) (by decide) rfl H1527_fin ptTest_fst
noncomputable def I1527_cp1 : Nat × Nat := t7val% (fastRun pI1527 1 1079 (init pI1527) (init pI1527))
theorem I1527_seg1 : segOK pI1527 1 1079 (init pI1527) (init pI1527) I1527_cp1.1 I1527_cp1.2 = true := by
  decide +kernel
theorem I1527_fin : (prmOK pI1527 1527 && intTest pI1527 (runFrom pI1527 (fmask pI1527) (cmask pI1527) (hmask pI1527) 1080 447 (true, I1527_cp1.1, I1527_cp1.2)) 1527 20 false) = true := by
  decide +kernel
theorem I1527_ok : RunOK pI1527 1527 (runFrom pI1527 (fmask pI1527) (cmask pI1527) (hmask pI1527) 1080 447 (true, I1527_cp1.1, I1527_cp1.2)) ∧ intTest pI1527 (runFrom pI1527 (fmask pI1527) (cmask pI1527) (hmask pI1527) 1080 447 (true, I1527_cp1.1, I1527_cp1.2)) 1527 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1527_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1527_fin) true) I1527_seg1) (by decide) rfl I1527_fin intTest_fst
theorem link1527 : linkOK pL1527 pH1527 pI1527 = true := by decide +kernel
theorem cvx1527 : ConvexBetweenHumps 1527 :=
  cvx_of L1527_ok H1527_ok I1527_ok link1527 (by decide)

/-! ### `N = 1528` -/

def pL1528 : Prm := ⟨80, 38, 39, 1530, 11, 18446744073709551616, 122580382899859129, 122580382899859129⟩
def pH1528 : Prm := ⟨81, 39, 39, 1530, 11, 18446744073709551616, 122581482411486905, 122581482411486905⟩
def pI1528 : Prm := ⟨66, 33, 30, 1530, 11, 18446744073709551616, 122580382899859129, 122581482411486905⟩
noncomputable def L1528_cp1 : Nat × Nat := t7val% (fastRun pL1528 1 1079 (init pL1528) (init pL1528))
theorem L1528_seg1 : segOK pL1528 1 1079 (init pL1528) (init pL1528) L1528_cp1.1 L1528_cp1.2 = true := by
  decide +kernel
theorem L1528_fin : (prmOK pL1528 1528 && ptTest pL1528 (runFrom pL1528 (fmask pL1528) (cmask pL1528) (hmask pL1528) 1080 448 (true, L1528_cp1.1, L1528_cp1.2)) 1528 764 false) = true := by
  decide +kernel
theorem L1528_ok : RunOK pL1528 1528 (runFrom pL1528 (fmask pL1528) (cmask pL1528) (hmask pL1528) 1080 448 (true, L1528_cp1.1, L1528_cp1.2)) ∧ ptTest pL1528 (runFrom pL1528 (fmask pL1528) (cmask pL1528) (hmask pL1528) 1080 448 (true, L1528_cp1.1, L1528_cp1.2)) 1528 764 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1528_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1528_fin) true) L1528_seg1) (by decide) rfl L1528_fin ptTest_fst
noncomputable def H1528_cp1 : Nat × Nat := t7val% (fastRun pH1528 1 1079 (init pH1528) (init pH1528))
theorem H1528_seg1 : segOK pH1528 1 1079 (init pH1528) (init pH1528) H1528_cp1.1 H1528_cp1.2 = true := by
  decide +kernel
theorem H1528_fin : (prmOK pH1528 1528 && ptTest pH1528 (runFrom pH1528 (fmask pH1528) (cmask pH1528) (hmask pH1528) 1080 448 (true, H1528_cp1.1, H1528_cp1.2)) 1528 764 true) = true := by
  decide +kernel
theorem H1528_ok : RunOK pH1528 1528 (runFrom pH1528 (fmask pH1528) (cmask pH1528) (hmask pH1528) 1080 448 (true, H1528_cp1.1, H1528_cp1.2)) ∧ ptTest pH1528 (runFrom pH1528 (fmask pH1528) (cmask pH1528) (hmask pH1528) 1080 448 (true, H1528_cp1.1, H1528_cp1.2)) 1528 764 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1528_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1528_fin) true) H1528_seg1) (by decide) rfl H1528_fin ptTest_fst
noncomputable def I1528_cp1 : Nat × Nat := t7val% (fastRun pI1528 1 1079 (init pI1528) (init pI1528))
theorem I1528_seg1 : segOK pI1528 1 1079 (init pI1528) (init pI1528) I1528_cp1.1 I1528_cp1.2 = true := by
  decide +kernel
theorem I1528_fin : (prmOK pI1528 1528 && intTest pI1528 (runFrom pI1528 (fmask pI1528) (cmask pI1528) (hmask pI1528) 1080 448 (true, I1528_cp1.1, I1528_cp1.2)) 1528 20 true) = true := by
  decide +kernel
theorem I1528_ok : RunOK pI1528 1528 (runFrom pI1528 (fmask pI1528) (cmask pI1528) (hmask pI1528) 1080 448 (true, I1528_cp1.1, I1528_cp1.2)) ∧ intTest pI1528 (runFrom pI1528 (fmask pI1528) (cmask pI1528) (hmask pI1528) 1080 448 (true, I1528_cp1.1, I1528_cp1.2)) 1528 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1528_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1528_fin) true) I1528_seg1) (by decide) rfl I1528_fin intTest_fst
theorem link1528 : linkOK pL1528 pH1528 pI1528 = true := by decide +kernel
theorem cvx1528 : ConvexBetweenHumps 1528 :=
  cvx_of L1528_ok H1528_ok I1528_ok link1528 (by decide)
theorem cenlink1528 : cenLinkOK pI1528 1528 = true := by decide +kernel
theorem cen1528 : CenterUniqueMin 1528 ∧ DipHyp 1528 ∧ OnePointHyps 1528 :=
  cen_of L1528_ok H1528_ok I1528_ok link1528 cenlink1528

/-! ### `N = 1529` -/

def pL1529 : Prm := ⟨80, 38, 39, 1531, 11, 18446744073709551616, 122515078737059228, 122515078737059228⟩
def pH1529 : Prm := ⟨81, 39, 39, 1531, 11, 18446744073709551616, 122516178248687004, 122516178248687004⟩
def pI1529 : Prm := ⟨66, 33, 30, 1531, 11, 18446744073709551616, 122515078737059228, 122516178248687004⟩
noncomputable def L1529_cp1 : Nat × Nat := t7val% (fastRun pL1529 1 1080 (init pL1529) (init pL1529))
theorem L1529_seg1 : segOK pL1529 1 1080 (init pL1529) (init pL1529) L1529_cp1.1 L1529_cp1.2 = true := by
  decide +kernel
theorem L1529_fin : (prmOK pL1529 1529 && ptTest pL1529 (runFrom pL1529 (fmask pL1529) (cmask pL1529) (hmask pL1529) 1081 448 (true, L1529_cp1.1, L1529_cp1.2)) 1529 765 false) = true := by
  decide +kernel
theorem L1529_ok : RunOK pL1529 1529 (runFrom pL1529 (fmask pL1529) (cmask pL1529) (hmask pL1529) 1081 448 (true, L1529_cp1.1, L1529_cp1.2)) ∧ ptTest pL1529 (runFrom pL1529 (fmask pL1529) (cmask pL1529) (hmask pL1529) 1081 448 (true, L1529_cp1.1, L1529_cp1.2)) 1529 765 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1529_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1529_fin) true) L1529_seg1) (by decide) rfl L1529_fin ptTest_fst
noncomputable def H1529_cp1 : Nat × Nat := t7val% (fastRun pH1529 1 1080 (init pH1529) (init pH1529))
theorem H1529_seg1 : segOK pH1529 1 1080 (init pH1529) (init pH1529) H1529_cp1.1 H1529_cp1.2 = true := by
  decide +kernel
theorem H1529_fin : (prmOK pH1529 1529 && ptTest pH1529 (runFrom pH1529 (fmask pH1529) (cmask pH1529) (hmask pH1529) 1081 448 (true, H1529_cp1.1, H1529_cp1.2)) 1529 765 true) = true := by
  decide +kernel
theorem H1529_ok : RunOK pH1529 1529 (runFrom pH1529 (fmask pH1529) (cmask pH1529) (hmask pH1529) 1081 448 (true, H1529_cp1.1, H1529_cp1.2)) ∧ ptTest pH1529 (runFrom pH1529 (fmask pH1529) (cmask pH1529) (hmask pH1529) 1081 448 (true, H1529_cp1.1, H1529_cp1.2)) 1529 765 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1529_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1529_fin) true) H1529_seg1) (by decide) rfl H1529_fin ptTest_fst
noncomputable def I1529_cp1 : Nat × Nat := t7val% (fastRun pI1529 1 1080 (init pI1529) (init pI1529))
theorem I1529_seg1 : segOK pI1529 1 1080 (init pI1529) (init pI1529) I1529_cp1.1 I1529_cp1.2 = true := by
  decide +kernel
theorem I1529_fin : (prmOK pI1529 1529 && intTest pI1529 (runFrom pI1529 (fmask pI1529) (cmask pI1529) (hmask pI1529) 1081 448 (true, I1529_cp1.1, I1529_cp1.2)) 1529 20 false) = true := by
  decide +kernel
theorem I1529_ok : RunOK pI1529 1529 (runFrom pI1529 (fmask pI1529) (cmask pI1529) (hmask pI1529) 1081 448 (true, I1529_cp1.1, I1529_cp1.2)) ∧ intTest pI1529 (runFrom pI1529 (fmask pI1529) (cmask pI1529) (hmask pI1529) 1081 448 (true, I1529_cp1.1, I1529_cp1.2)) 1529 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1529_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1529_fin) true) I1529_seg1) (by decide) rfl I1529_fin intTest_fst
theorem link1529 : linkOK pL1529 pH1529 pI1529 = true := by decide +kernel
theorem cvx1529 : ConvexBetweenHumps 1529 :=
  cvx_of L1529_ok H1529_ok I1529_ok link1529 (by decide)

/-! ### The range -/

theorem cvx_1513_1529 {N : ℕ} (h1 : 1513 ≤ N) (h2 : N ≤ 1529) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1520
  · by_cases h4 : N ≤ 1516
    · by_cases h6 : N ≤ 1514
      · by_cases h8 : N ≤ 1513
        · obtain rfl : N = 1513 := by omega
          exact cvx1513
        · obtain rfl : N = 1514 := by omega
          exact cvx1514
      · by_cases h8 : N ≤ 1515
        · obtain rfl : N = 1515 := by omega
          exact cvx1515
        · obtain rfl : N = 1516 := by omega
          exact cvx1516
    · by_cases h6 : N ≤ 1518
      · by_cases h8 : N ≤ 1517
        · obtain rfl : N = 1517 := by omega
          exact cvx1517
        · obtain rfl : N = 1518 := by omega
          exact cvx1518
      · by_cases h8 : N ≤ 1519
        · obtain rfl : N = 1519 := by omega
          exact cvx1519
        · obtain rfl : N = 1520 := by omega
          exact cvx1520
  · by_cases h4 : N ≤ 1524
    · by_cases h6 : N ≤ 1522
      · by_cases h8 : N ≤ 1521
        · obtain rfl : N = 1521 := by omega
          exact cvx1521
        · obtain rfl : N = 1522 := by omega
          exact cvx1522
      · by_cases h8 : N ≤ 1523
        · obtain rfl : N = 1523 := by omega
          exact cvx1523
        · obtain rfl : N = 1524 := by omega
          exact cvx1524
    · by_cases h6 : N ≤ 1526
      · by_cases h8 : N ≤ 1525
        · obtain rfl : N = 1525 := by omega
          exact cvx1525
        · obtain rfl : N = 1526 := by omega
          exact cvx1526
      · by_cases h8 : N ≤ 1527
        · obtain rfl : N = 1527 := by omega
          exact cvx1527
        · by_cases h10 : N ≤ 1528
          · obtain rfl : N = 1528 := by omega
            exact cvx1528
          · obtain rfl : N = 1529 := by omega
            exact cvx1529

theorem cen_1513_1529 {N : ℕ} (h1 : 1513 ≤ N) (h2 : N ≤ 1529) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1520
  · by_cases h4 : N ≤ 1516
    · by_cases h6 : N ≤ 1514
      · obtain rfl : N = 1514 := by omega
        exact cen1514
      · obtain rfl : N = 1516 := by omega
        exact cen1516
    · by_cases h6 : N ≤ 1518
      · obtain rfl : N = 1518 := by omega
        exact cen1518
      · obtain rfl : N = 1520 := by omega
        exact cen1520
  · by_cases h4 : N ≤ 1524
    · by_cases h6 : N ≤ 1522
      · obtain rfl : N = 1522 := by omega
        exact cen1522
      · obtain rfl : N = 1524 := by omega
        exact cen1524
    · by_cases h6 : N ≤ 1526
      · obtain rfl : N = 1526 := by omega
        exact cen1526
      · obtain rfl : N = 1528 := by omega
        exact cen1528

end Kagey131.PaperD.T7
