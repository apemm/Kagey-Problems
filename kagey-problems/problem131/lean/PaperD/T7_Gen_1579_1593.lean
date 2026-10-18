import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1579, …, 1593` (generated)

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

/-! ### `N = 1579` -/

def pL1579 : Prm := ⟨81, 39, 39, 1581, 11, 18446744073709551616, 119344323628979086, 119344323628979086⟩
def pH1579 : Prm := ⟨81, 39, 39, 1581, 11, 18446744073709551616, 119345423140606862, 119345423140606862⟩
def pI1579 : Prm := ⟨67, 33, 31, 1581, 11, 18446744073709551616, 119344323628979086, 119345423140606862⟩
noncomputable def L1579_cp1 : Nat × Nat := t7val% (fastRun pL1579 1 1116 (init pL1579) (init pL1579))
theorem L1579_seg1 : segOK pL1579 1 1116 (init pL1579) (init pL1579) L1579_cp1.1 L1579_cp1.2 = true := by
  decide +kernel
theorem L1579_fin : (prmOK pL1579 1579 && ptTest pL1579 (runFrom pL1579 (fmask pL1579) (cmask pL1579) (hmask pL1579) 1117 462 (true, L1579_cp1.1, L1579_cp1.2)) 1579 790 false) = true := by
  decide +kernel
theorem L1579_ok : RunOK pL1579 1579 (runFrom pL1579 (fmask pL1579) (cmask pL1579) (hmask pL1579) 1117 462 (true, L1579_cp1.1, L1579_cp1.2)) ∧ ptTest pL1579 (runFrom pL1579 (fmask pL1579) (cmask pL1579) (hmask pL1579) 1117 462 (true, L1579_cp1.1, L1579_cp1.2)) 1579 790 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1579_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1579_fin) true) L1579_seg1) (by decide) rfl L1579_fin ptTest_fst
noncomputable def H1579_cp1 : Nat × Nat := t7val% (fastRun pH1579 1 1116 (init pH1579) (init pH1579))
theorem H1579_seg1 : segOK pH1579 1 1116 (init pH1579) (init pH1579) H1579_cp1.1 H1579_cp1.2 = true := by
  decide +kernel
theorem H1579_fin : (prmOK pH1579 1579 && ptTest pH1579 (runFrom pH1579 (fmask pH1579) (cmask pH1579) (hmask pH1579) 1117 462 (true, H1579_cp1.1, H1579_cp1.2)) 1579 790 true) = true := by
  decide +kernel
theorem H1579_ok : RunOK pH1579 1579 (runFrom pH1579 (fmask pH1579) (cmask pH1579) (hmask pH1579) 1117 462 (true, H1579_cp1.1, H1579_cp1.2)) ∧ ptTest pH1579 (runFrom pH1579 (fmask pH1579) (cmask pH1579) (hmask pH1579) 1117 462 (true, H1579_cp1.1, H1579_cp1.2)) 1579 790 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1579_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1579_fin) true) H1579_seg1) (by decide) rfl H1579_fin ptTest_fst
noncomputable def I1579_cp1 : Nat × Nat := t7val% (fastRun pI1579 1 1116 (init pI1579) (init pI1579))
theorem I1579_seg1 : segOK pI1579 1 1116 (init pI1579) (init pI1579) I1579_cp1.1 I1579_cp1.2 = true := by
  decide +kernel
theorem I1579_fin : (prmOK pI1579 1579 && intTest pI1579 (runFrom pI1579 (fmask pI1579) (cmask pI1579) (hmask pI1579) 1117 462 (true, I1579_cp1.1, I1579_cp1.2)) 1579 20 false) = true := by
  decide +kernel
theorem I1579_ok : RunOK pI1579 1579 (runFrom pI1579 (fmask pI1579) (cmask pI1579) (hmask pI1579) 1117 462 (true, I1579_cp1.1, I1579_cp1.2)) ∧ intTest pI1579 (runFrom pI1579 (fmask pI1579) (cmask pI1579) (hmask pI1579) 1117 462 (true, I1579_cp1.1, I1579_cp1.2)) 1579 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1579_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1579_fin) true) I1579_seg1) (by decide) rfl I1579_fin intTest_fst
theorem link1579 : linkOK pL1579 pH1579 pI1579 = true := by decide +kernel
theorem cvx1579 : ConvexBetweenHumps 1579 :=
  cvx_of L1579_ok H1579_ok I1579_ok link1579 (by decide)

/-! ### `N = 1580` -/

def pL1580 : Prm := ⟨81, 39, 39, 1582, 11, 18446744073709551616, 119282739593054372, 119282739593054372⟩
def pH1580 : Prm := ⟨82, 40, 39, 1582, 11, 18446744073709551616, 119283839104682148, 119283839104682148⟩
def pI1580 : Prm := ⟨67, 33, 31, 1582, 11, 18446744073709551616, 119282739593054372, 119283839104682148⟩
noncomputable def L1580_cp1 : Nat × Nat := t7val% (fastRun pL1580 1 1116 (init pL1580) (init pL1580))
theorem L1580_seg1 : segOK pL1580 1 1116 (init pL1580) (init pL1580) L1580_cp1.1 L1580_cp1.2 = true := by
  decide +kernel
theorem L1580_fin : (prmOK pL1580 1580 && ptTest pL1580 (runFrom pL1580 (fmask pL1580) (cmask pL1580) (hmask pL1580) 1117 463 (true, L1580_cp1.1, L1580_cp1.2)) 1580 790 false) = true := by
  decide +kernel
theorem L1580_ok : RunOK pL1580 1580 (runFrom pL1580 (fmask pL1580) (cmask pL1580) (hmask pL1580) 1117 463 (true, L1580_cp1.1, L1580_cp1.2)) ∧ ptTest pL1580 (runFrom pL1580 (fmask pL1580) (cmask pL1580) (hmask pL1580) 1117 463 (true, L1580_cp1.1, L1580_cp1.2)) 1580 790 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1580_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1580_fin) true) L1580_seg1) (by decide) rfl L1580_fin ptTest_fst
noncomputable def H1580_cp1 : Nat × Nat := t7val% (fastRun pH1580 1 1116 (init pH1580) (init pH1580))
theorem H1580_seg1 : segOK pH1580 1 1116 (init pH1580) (init pH1580) H1580_cp1.1 H1580_cp1.2 = true := by
  decide +kernel
theorem H1580_fin : (prmOK pH1580 1580 && ptTest pH1580 (runFrom pH1580 (fmask pH1580) (cmask pH1580) (hmask pH1580) 1117 463 (true, H1580_cp1.1, H1580_cp1.2)) 1580 790 true) = true := by
  decide +kernel
theorem H1580_ok : RunOK pH1580 1580 (runFrom pH1580 (fmask pH1580) (cmask pH1580) (hmask pH1580) 1117 463 (true, H1580_cp1.1, H1580_cp1.2)) ∧ ptTest pH1580 (runFrom pH1580 (fmask pH1580) (cmask pH1580) (hmask pH1580) 1117 463 (true, H1580_cp1.1, H1580_cp1.2)) 1580 790 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1580_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1580_fin) true) H1580_seg1) (by decide) rfl H1580_fin ptTest_fst
noncomputable def I1580_cp1 : Nat × Nat := t7val% (fastRun pI1580 1 1116 (init pI1580) (init pI1580))
theorem I1580_seg1 : segOK pI1580 1 1116 (init pI1580) (init pI1580) I1580_cp1.1 I1580_cp1.2 = true := by
  decide +kernel
theorem I1580_fin : (prmOK pI1580 1580 && intTest pI1580 (runFrom pI1580 (fmask pI1580) (cmask pI1580) (hmask pI1580) 1117 463 (true, I1580_cp1.1, I1580_cp1.2)) 1580 20 true) = true := by
  decide +kernel
theorem I1580_ok : RunOK pI1580 1580 (runFrom pI1580 (fmask pI1580) (cmask pI1580) (hmask pI1580) 1117 463 (true, I1580_cp1.1, I1580_cp1.2)) ∧ intTest pI1580 (runFrom pI1580 (fmask pI1580) (cmask pI1580) (hmask pI1580) 1117 463 (true, I1580_cp1.1, I1580_cp1.2)) 1580 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1580_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1580_fin) true) I1580_seg1) (by decide) rfl I1580_fin intTest_fst
theorem link1580 : linkOK pL1580 pH1580 pI1580 = true := by decide +kernel
theorem cvx1580 : ConvexBetweenHumps 1580 :=
  cvx_of L1580_ok H1580_ok I1580_ok link1580 (by decide)
theorem cenlink1580 : cenLinkOK pI1580 1580 = true := by decide +kernel
theorem cen1580 : CenterUniqueMin 1580 ∧ DipHyp 1580 ∧ OnePointHyps 1580 :=
  cen_of L1580_ok H1580_ok I1580_ok link1580 cenlink1580

/-! ### `N = 1581` -/

def pL1581 : Prm := ⟨81, 39, 39, 1583, 11, 18446744073709551616, 119221196029821112, 119221196029821112⟩
def pH1581 : Prm := ⟨82, 40, 39, 1583, 11, 18446744073709551616, 119222295541448888, 119222295541448888⟩
def pI1581 : Prm := ⟨67, 33, 31, 1583, 11, 18446744073709551616, 119221196029821112, 119222295541448888⟩
noncomputable def L1581_cp1 : Nat × Nat := t7val% (fastRun pL1581 1 1117 (init pL1581) (init pL1581))
theorem L1581_seg1 : segOK pL1581 1 1117 (init pL1581) (init pL1581) L1581_cp1.1 L1581_cp1.2 = true := by
  decide +kernel
theorem L1581_fin : (prmOK pL1581 1581 && ptTest pL1581 (runFrom pL1581 (fmask pL1581) (cmask pL1581) (hmask pL1581) 1118 463 (true, L1581_cp1.1, L1581_cp1.2)) 1581 791 false) = true := by
  decide +kernel
theorem L1581_ok : RunOK pL1581 1581 (runFrom pL1581 (fmask pL1581) (cmask pL1581) (hmask pL1581) 1118 463 (true, L1581_cp1.1, L1581_cp1.2)) ∧ ptTest pL1581 (runFrom pL1581 (fmask pL1581) (cmask pL1581) (hmask pL1581) 1118 463 (true, L1581_cp1.1, L1581_cp1.2)) 1581 791 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1581_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1581_fin) true) L1581_seg1) (by decide) rfl L1581_fin ptTest_fst
noncomputable def H1581_cp1 : Nat × Nat := t7val% (fastRun pH1581 1 1117 (init pH1581) (init pH1581))
theorem H1581_seg1 : segOK pH1581 1 1117 (init pH1581) (init pH1581) H1581_cp1.1 H1581_cp1.2 = true := by
  decide +kernel
theorem H1581_fin : (prmOK pH1581 1581 && ptTest pH1581 (runFrom pH1581 (fmask pH1581) (cmask pH1581) (hmask pH1581) 1118 463 (true, H1581_cp1.1, H1581_cp1.2)) 1581 791 true) = true := by
  decide +kernel
theorem H1581_ok : RunOK pH1581 1581 (runFrom pH1581 (fmask pH1581) (cmask pH1581) (hmask pH1581) 1118 463 (true, H1581_cp1.1, H1581_cp1.2)) ∧ ptTest pH1581 (runFrom pH1581 (fmask pH1581) (cmask pH1581) (hmask pH1581) 1118 463 (true, H1581_cp1.1, H1581_cp1.2)) 1581 791 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1581_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1581_fin) true) H1581_seg1) (by decide) rfl H1581_fin ptTest_fst
noncomputable def I1581_cp1 : Nat × Nat := t7val% (fastRun pI1581 1 1117 (init pI1581) (init pI1581))
theorem I1581_seg1 : segOK pI1581 1 1117 (init pI1581) (init pI1581) I1581_cp1.1 I1581_cp1.2 = true := by
  decide +kernel
theorem I1581_fin : (prmOK pI1581 1581 && intTest pI1581 (runFrom pI1581 (fmask pI1581) (cmask pI1581) (hmask pI1581) 1118 463 (true, I1581_cp1.1, I1581_cp1.2)) 1581 20 false) = true := by
  decide +kernel
theorem I1581_ok : RunOK pI1581 1581 (runFrom pI1581 (fmask pI1581) (cmask pI1581) (hmask pI1581) 1118 463 (true, I1581_cp1.1, I1581_cp1.2)) ∧ intTest pI1581 (runFrom pI1581 (fmask pI1581) (cmask pI1581) (hmask pI1581) 1118 463 (true, I1581_cp1.1, I1581_cp1.2)) 1581 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1581_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1581_fin) true) I1581_seg1) (by decide) rfl I1581_fin intTest_fst
theorem link1581 : linkOK pL1581 pH1581 pI1581 = true := by decide +kernel
theorem cvx1581 : ConvexBetweenHumps 1581 :=
  cvx_of L1581_ok H1581_ok I1581_ok link1581 (by decide)

/-! ### `N = 1582` -/

def pL1582 : Prm := ⟨81, 39, 39, 1584, 11, 18446744073709551616, 119159750019482214, 119159750019482214⟩
def pH1582 : Prm := ⟨81, 39, 39, 1584, 11, 18446744073709551616, 119160849531109990, 119160849531109990⟩
def pI1582 : Prm := ⟨67, 33, 31, 1584, 11, 18446744073709551616, 119159750019482214, 119160849531109990⟩
noncomputable def L1582_cp1 : Nat × Nat := t7val% (fastRun pL1582 1 1118 (init pL1582) (init pL1582))
theorem L1582_seg1 : segOK pL1582 1 1118 (init pL1582) (init pL1582) L1582_cp1.1 L1582_cp1.2 = true := by
  decide +kernel
theorem L1582_fin : (prmOK pL1582 1582 && ptTest pL1582 (runFrom pL1582 (fmask pL1582) (cmask pL1582) (hmask pL1582) 1119 463 (true, L1582_cp1.1, L1582_cp1.2)) 1582 791 false) = true := by
  decide +kernel
theorem L1582_ok : RunOK pL1582 1582 (runFrom pL1582 (fmask pL1582) (cmask pL1582) (hmask pL1582) 1119 463 (true, L1582_cp1.1, L1582_cp1.2)) ∧ ptTest pL1582 (runFrom pL1582 (fmask pL1582) (cmask pL1582) (hmask pL1582) 1119 463 (true, L1582_cp1.1, L1582_cp1.2)) 1582 791 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1582_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1582_fin) true) L1582_seg1) (by decide) rfl L1582_fin ptTest_fst
noncomputable def H1582_cp1 : Nat × Nat := t7val% (fastRun pH1582 1 1118 (init pH1582) (init pH1582))
theorem H1582_seg1 : segOK pH1582 1 1118 (init pH1582) (init pH1582) H1582_cp1.1 H1582_cp1.2 = true := by
  decide +kernel
theorem H1582_fin : (prmOK pH1582 1582 && ptTest pH1582 (runFrom pH1582 (fmask pH1582) (cmask pH1582) (hmask pH1582) 1119 463 (true, H1582_cp1.1, H1582_cp1.2)) 1582 791 true) = true := by
  decide +kernel
theorem H1582_ok : RunOK pH1582 1582 (runFrom pH1582 (fmask pH1582) (cmask pH1582) (hmask pH1582) 1119 463 (true, H1582_cp1.1, H1582_cp1.2)) ∧ ptTest pH1582 (runFrom pH1582 (fmask pH1582) (cmask pH1582) (hmask pH1582) 1119 463 (true, H1582_cp1.1, H1582_cp1.2)) 1582 791 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1582_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1582_fin) true) H1582_seg1) (by decide) rfl H1582_fin ptTest_fst
noncomputable def I1582_cp1 : Nat × Nat := t7val% (fastRun pI1582 1 1118 (init pI1582) (init pI1582))
theorem I1582_seg1 : segOK pI1582 1 1118 (init pI1582) (init pI1582) I1582_cp1.1 I1582_cp1.2 = true := by
  decide +kernel
theorem I1582_fin : (prmOK pI1582 1582 && intTest pI1582 (runFrom pI1582 (fmask pI1582) (cmask pI1582) (hmask pI1582) 1119 463 (true, I1582_cp1.1, I1582_cp1.2)) 1582 20 true) = true := by
  decide +kernel
theorem I1582_ok : RunOK pI1582 1582 (runFrom pI1582 (fmask pI1582) (cmask pI1582) (hmask pI1582) 1119 463 (true, I1582_cp1.1, I1582_cp1.2)) ∧ intTest pI1582 (runFrom pI1582 (fmask pI1582) (cmask pI1582) (hmask pI1582) 1119 463 (true, I1582_cp1.1, I1582_cp1.2)) 1582 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1582_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1582_fin) true) I1582_seg1) (by decide) rfl I1582_fin intTest_fst
theorem link1582 : linkOK pL1582 pH1582 pI1582 = true := by decide +kernel
theorem cvx1582 : ConvexBetweenHumps 1582 :=
  cvx_of L1582_ok H1582_ok I1582_ok link1582 (by decide)
theorem cenlink1582 : cenLinkOK pI1582 1582 = true := by decide +kernel
theorem cen1582 : CenterUniqueMin 1582 ∧ DipHyp 1582 ∧ OnePointHyps 1582 :=
  cen_of L1582_ok H1582_ok I1582_ok link1582 cenlink1582

/-! ### `N = 1583` -/

def pL1583 : Prm := ⟨81, 39, 39, 1585, 11, 18446744073709551616, 119098344352504646, 119098344352504646⟩
def pH1583 : Prm := ⟨82, 40, 39, 1585, 11, 18446744073709551616, 119099443864132422, 119099443864132422⟩
def pI1583 : Prm := ⟨67, 33, 31, 1585, 11, 18446744073709551616, 119098344352504646, 119099443864132422⟩
noncomputable def L1583_cp1 : Nat × Nat := t7val% (fastRun pL1583 1 1118 (init pL1583) (init pL1583))
theorem L1583_seg1 : segOK pL1583 1 1118 (init pL1583) (init pL1583) L1583_cp1.1 L1583_cp1.2 = true := by
  decide +kernel
theorem L1583_fin : (prmOK pL1583 1583 && ptTest pL1583 (runFrom pL1583 (fmask pL1583) (cmask pL1583) (hmask pL1583) 1119 464 (true, L1583_cp1.1, L1583_cp1.2)) 1583 792 false) = true := by
  decide +kernel
theorem L1583_ok : RunOK pL1583 1583 (runFrom pL1583 (fmask pL1583) (cmask pL1583) (hmask pL1583) 1119 464 (true, L1583_cp1.1, L1583_cp1.2)) ∧ ptTest pL1583 (runFrom pL1583 (fmask pL1583) (cmask pL1583) (hmask pL1583) 1119 464 (true, L1583_cp1.1, L1583_cp1.2)) 1583 792 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1583_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1583_fin) true) L1583_seg1) (by decide) rfl L1583_fin ptTest_fst
noncomputable def H1583_cp1 : Nat × Nat := t7val% (fastRun pH1583 1 1118 (init pH1583) (init pH1583))
theorem H1583_seg1 : segOK pH1583 1 1118 (init pH1583) (init pH1583) H1583_cp1.1 H1583_cp1.2 = true := by
  decide +kernel
theorem H1583_fin : (prmOK pH1583 1583 && ptTest pH1583 (runFrom pH1583 (fmask pH1583) (cmask pH1583) (hmask pH1583) 1119 464 (true, H1583_cp1.1, H1583_cp1.2)) 1583 792 true) = true := by
  decide +kernel
theorem H1583_ok : RunOK pH1583 1583 (runFrom pH1583 (fmask pH1583) (cmask pH1583) (hmask pH1583) 1119 464 (true, H1583_cp1.1, H1583_cp1.2)) ∧ ptTest pH1583 (runFrom pH1583 (fmask pH1583) (cmask pH1583) (hmask pH1583) 1119 464 (true, H1583_cp1.1, H1583_cp1.2)) 1583 792 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1583_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1583_fin) true) H1583_seg1) (by decide) rfl H1583_fin ptTest_fst
noncomputable def I1583_cp1 : Nat × Nat := t7val% (fastRun pI1583 1 1118 (init pI1583) (init pI1583))
theorem I1583_seg1 : segOK pI1583 1 1118 (init pI1583) (init pI1583) I1583_cp1.1 I1583_cp1.2 = true := by
  decide +kernel
theorem I1583_fin : (prmOK pI1583 1583 && intTest pI1583 (runFrom pI1583 (fmask pI1583) (cmask pI1583) (hmask pI1583) 1119 464 (true, I1583_cp1.1, I1583_cp1.2)) 1583 20 false) = true := by
  decide +kernel
theorem I1583_ok : RunOK pI1583 1583 (runFrom pI1583 (fmask pI1583) (cmask pI1583) (hmask pI1583) 1119 464 (true, I1583_cp1.1, I1583_cp1.2)) ∧ intTest pI1583 (runFrom pI1583 (fmask pI1583) (cmask pI1583) (hmask pI1583) 1119 464 (true, I1583_cp1.1, I1583_cp1.2)) 1583 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1583_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1583_fin) true) I1583_seg1) (by decide) rfl I1583_fin intTest_fst
theorem link1583 : linkOK pL1583 pH1583 pI1583 = true := by decide +kernel
theorem cvx1583 : ConvexBetweenHumps 1583 :=
  cvx_of L1583_ok H1583_ok I1583_ok link1583 (by decide)

/-! ### `N = 1584` -/

def pL1584 : Prm := ⟨81, 39, 39, 1586, 11, 18446744073709551616, 119037035889611958, 119037035889611958⟩
def pH1584 : Prm := ⟨82, 40, 39, 1586, 11, 18446744073709551616, 119038135401239734, 119038135401239734⟩
def pI1584 : Prm := ⟨67, 33, 31, 1586, 11, 18446744073709551616, 119037035889611958, 119038135401239734⟩
noncomputable def L1584_cp1 : Nat × Nat := t7val% (fastRun pL1584 1 1119 (init pL1584) (init pL1584))
theorem L1584_seg1 : segOK pL1584 1 1119 (init pL1584) (init pL1584) L1584_cp1.1 L1584_cp1.2 = true := by
  decide +kernel
theorem L1584_fin : (prmOK pL1584 1584 && ptTest pL1584 (runFrom pL1584 (fmask pL1584) (cmask pL1584) (hmask pL1584) 1120 464 (true, L1584_cp1.1, L1584_cp1.2)) 1584 792 false) = true := by
  decide +kernel
theorem L1584_ok : RunOK pL1584 1584 (runFrom pL1584 (fmask pL1584) (cmask pL1584) (hmask pL1584) 1120 464 (true, L1584_cp1.1, L1584_cp1.2)) ∧ ptTest pL1584 (runFrom pL1584 (fmask pL1584) (cmask pL1584) (hmask pL1584) 1120 464 (true, L1584_cp1.1, L1584_cp1.2)) 1584 792 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1584_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1584_fin) true) L1584_seg1) (by decide) rfl L1584_fin ptTest_fst
noncomputable def H1584_cp1 : Nat × Nat := t7val% (fastRun pH1584 1 1119 (init pH1584) (init pH1584))
theorem H1584_seg1 : segOK pH1584 1 1119 (init pH1584) (init pH1584) H1584_cp1.1 H1584_cp1.2 = true := by
  decide +kernel
theorem H1584_fin : (prmOK pH1584 1584 && ptTest pH1584 (runFrom pH1584 (fmask pH1584) (cmask pH1584) (hmask pH1584) 1120 464 (true, H1584_cp1.1, H1584_cp1.2)) 1584 792 true) = true := by
  decide +kernel
theorem H1584_ok : RunOK pH1584 1584 (runFrom pH1584 (fmask pH1584) (cmask pH1584) (hmask pH1584) 1120 464 (true, H1584_cp1.1, H1584_cp1.2)) ∧ ptTest pH1584 (runFrom pH1584 (fmask pH1584) (cmask pH1584) (hmask pH1584) 1120 464 (true, H1584_cp1.1, H1584_cp1.2)) 1584 792 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1584_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1584_fin) true) H1584_seg1) (by decide) rfl H1584_fin ptTest_fst
noncomputable def I1584_cp1 : Nat × Nat := t7val% (fastRun pI1584 1 1119 (init pI1584) (init pI1584))
theorem I1584_seg1 : segOK pI1584 1 1119 (init pI1584) (init pI1584) I1584_cp1.1 I1584_cp1.2 = true := by
  decide +kernel
theorem I1584_fin : (prmOK pI1584 1584 && intTest pI1584 (runFrom pI1584 (fmask pI1584) (cmask pI1584) (hmask pI1584) 1120 464 (true, I1584_cp1.1, I1584_cp1.2)) 1584 20 true) = true := by
  decide +kernel
theorem I1584_ok : RunOK pI1584 1584 (runFrom pI1584 (fmask pI1584) (cmask pI1584) (hmask pI1584) 1120 464 (true, I1584_cp1.1, I1584_cp1.2)) ∧ intTest pI1584 (runFrom pI1584 (fmask pI1584) (cmask pI1584) (hmask pI1584) 1120 464 (true, I1584_cp1.1, I1584_cp1.2)) 1584 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1584_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1584_fin) true) I1584_seg1) (by decide) rfl I1584_fin intTest_fst
theorem link1584 : linkOK pL1584 pH1584 pI1584 = true := by decide +kernel
theorem cvx1584 : ConvexBetweenHumps 1584 :=
  cvx_of L1584_ok H1584_ok I1584_ok link1584 (by decide)
theorem cenlink1584 : cenLinkOK pI1584 1584 = true := by decide +kernel
theorem cen1584 : CenterUniqueMin 1584 ∧ DipHyp 1584 ∧ OnePointHyps 1584 :=
  cen_of L1584_ok H1584_ok I1584_ok link1584 cenlink1584

/-! ### `N = 1585` -/

def pL1585 : Prm := ⟨82, 40, 39, 1587, 11, 18446744073709551616, 118975767641303879, 118975767641303879⟩
def pH1585 : Prm := ⟨82, 40, 39, 1587, 11, 18446744073709551616, 118976867152931655, 118976867152931655⟩
def pI1585 : Prm := ⟨67, 33, 31, 1587, 11, 18446744073709551616, 118975767641303879, 118976867152931655⟩
noncomputable def L1585_cp1 : Nat × Nat := t7val% (fastRun pL1585 1 1120 (init pL1585) (init pL1585))
theorem L1585_seg1 : segOK pL1585 1 1120 (init pL1585) (init pL1585) L1585_cp1.1 L1585_cp1.2 = true := by
  decide +kernel
theorem L1585_fin : (prmOK pL1585 1585 && ptTest pL1585 (runFrom pL1585 (fmask pL1585) (cmask pL1585) (hmask pL1585) 1121 464 (true, L1585_cp1.1, L1585_cp1.2)) 1585 793 false) = true := by
  decide +kernel
theorem L1585_ok : RunOK pL1585 1585 (runFrom pL1585 (fmask pL1585) (cmask pL1585) (hmask pL1585) 1121 464 (true, L1585_cp1.1, L1585_cp1.2)) ∧ ptTest pL1585 (runFrom pL1585 (fmask pL1585) (cmask pL1585) (hmask pL1585) 1121 464 (true, L1585_cp1.1, L1585_cp1.2)) 1585 793 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1585_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1585_fin) true) L1585_seg1) (by decide) rfl L1585_fin ptTest_fst
noncomputable def H1585_cp1 : Nat × Nat := t7val% (fastRun pH1585 1 1120 (init pH1585) (init pH1585))
theorem H1585_seg1 : segOK pH1585 1 1120 (init pH1585) (init pH1585) H1585_cp1.1 H1585_cp1.2 = true := by
  decide +kernel
theorem H1585_fin : (prmOK pH1585 1585 && ptTest pH1585 (runFrom pH1585 (fmask pH1585) (cmask pH1585) (hmask pH1585) 1121 464 (true, H1585_cp1.1, H1585_cp1.2)) 1585 793 true) = true := by
  decide +kernel
theorem H1585_ok : RunOK pH1585 1585 (runFrom pH1585 (fmask pH1585) (cmask pH1585) (hmask pH1585) 1121 464 (true, H1585_cp1.1, H1585_cp1.2)) ∧ ptTest pH1585 (runFrom pH1585 (fmask pH1585) (cmask pH1585) (hmask pH1585) 1121 464 (true, H1585_cp1.1, H1585_cp1.2)) 1585 793 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1585_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1585_fin) true) H1585_seg1) (by decide) rfl H1585_fin ptTest_fst
noncomputable def I1585_cp1 : Nat × Nat := t7val% (fastRun pI1585 1 1120 (init pI1585) (init pI1585))
theorem I1585_seg1 : segOK pI1585 1 1120 (init pI1585) (init pI1585) I1585_cp1.1 I1585_cp1.2 = true := by
  decide +kernel
theorem I1585_fin : (prmOK pI1585 1585 && intTest pI1585 (runFrom pI1585 (fmask pI1585) (cmask pI1585) (hmask pI1585) 1121 464 (true, I1585_cp1.1, I1585_cp1.2)) 1585 20 false) = true := by
  decide +kernel
theorem I1585_ok : RunOK pI1585 1585 (runFrom pI1585 (fmask pI1585) (cmask pI1585) (hmask pI1585) 1121 464 (true, I1585_cp1.1, I1585_cp1.2)) ∧ intTest pI1585 (runFrom pI1585 (fmask pI1585) (cmask pI1585) (hmask pI1585) 1121 464 (true, I1585_cp1.1, I1585_cp1.2)) 1585 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1585_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1585_fin) true) I1585_seg1) (by decide) rfl I1585_fin intTest_fst
theorem link1585 : linkOK pL1585 pH1585 pI1585 = true := by decide +kernel
theorem cvx1585 : ConvexBetweenHumps 1585 :=
  cvx_of L1585_ok H1585_ok I1585_ok link1585 (by decide)

/-! ### `N = 1586` -/

def pL1586 : Prm := ⟨81, 39, 39, 1588, 11, 18446744073709551616, 118914596249968297, 118914596249968297⟩
def pH1586 : Prm := ⟨82, 40, 39, 1588, 11, 18446744073709551616, 118915695761596073, 118915695761596073⟩
def pI1586 : Prm := ⟨67, 33, 31, 1588, 11, 18446744073709551616, 118914596249968297, 118915695761596073⟩
noncomputable def L1586_cp1 : Nat × Nat := t7val% (fastRun pL1586 1 1120 (init pL1586) (init pL1586))
theorem L1586_seg1 : segOK pL1586 1 1120 (init pL1586) (init pL1586) L1586_cp1.1 L1586_cp1.2 = true := by
  decide +kernel
theorem L1586_fin : (prmOK pL1586 1586 && ptTest pL1586 (runFrom pL1586 (fmask pL1586) (cmask pL1586) (hmask pL1586) 1121 465 (true, L1586_cp1.1, L1586_cp1.2)) 1586 793 false) = true := by
  decide +kernel
theorem L1586_ok : RunOK pL1586 1586 (runFrom pL1586 (fmask pL1586) (cmask pL1586) (hmask pL1586) 1121 465 (true, L1586_cp1.1, L1586_cp1.2)) ∧ ptTest pL1586 (runFrom pL1586 (fmask pL1586) (cmask pL1586) (hmask pL1586) 1121 465 (true, L1586_cp1.1, L1586_cp1.2)) 1586 793 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1586_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1586_fin) true) L1586_seg1) (by decide) rfl L1586_fin ptTest_fst
noncomputable def H1586_cp1 : Nat × Nat := t7val% (fastRun pH1586 1 1120 (init pH1586) (init pH1586))
theorem H1586_seg1 : segOK pH1586 1 1120 (init pH1586) (init pH1586) H1586_cp1.1 H1586_cp1.2 = true := by
  decide +kernel
theorem H1586_fin : (prmOK pH1586 1586 && ptTest pH1586 (runFrom pH1586 (fmask pH1586) (cmask pH1586) (hmask pH1586) 1121 465 (true, H1586_cp1.1, H1586_cp1.2)) 1586 793 true) = true := by
  decide +kernel
theorem H1586_ok : RunOK pH1586 1586 (runFrom pH1586 (fmask pH1586) (cmask pH1586) (hmask pH1586) 1121 465 (true, H1586_cp1.1, H1586_cp1.2)) ∧ ptTest pH1586 (runFrom pH1586 (fmask pH1586) (cmask pH1586) (hmask pH1586) 1121 465 (true, H1586_cp1.1, H1586_cp1.2)) 1586 793 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1586_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1586_fin) true) H1586_seg1) (by decide) rfl H1586_fin ptTest_fst
noncomputable def I1586_cp1 : Nat × Nat := t7val% (fastRun pI1586 1 1120 (init pI1586) (init pI1586))
theorem I1586_seg1 : segOK pI1586 1 1120 (init pI1586) (init pI1586) I1586_cp1.1 I1586_cp1.2 = true := by
  decide +kernel
theorem I1586_fin : (prmOK pI1586 1586 && intTest pI1586 (runFrom pI1586 (fmask pI1586) (cmask pI1586) (hmask pI1586) 1121 465 (true, I1586_cp1.1, I1586_cp1.2)) 1586 20 true) = true := by
  decide +kernel
theorem I1586_ok : RunOK pI1586 1586 (runFrom pI1586 (fmask pI1586) (cmask pI1586) (hmask pI1586) 1121 465 (true, I1586_cp1.1, I1586_cp1.2)) ∧ intTest pI1586 (runFrom pI1586 (fmask pI1586) (cmask pI1586) (hmask pI1586) 1121 465 (true, I1586_cp1.1, I1586_cp1.2)) 1586 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1586_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1586_fin) true) I1586_seg1) (by decide) rfl I1586_fin intTest_fst
theorem link1586 : linkOK pL1586 pH1586 pI1586 = true := by decide +kernel
theorem cvx1586 : ConvexBetweenHumps 1586 :=
  cvx_of L1586_ok H1586_ok I1586_ok link1586 (by decide)
theorem cenlink1586 : cenLinkOK pI1586 1586 = true := by decide +kernel
theorem cen1586 : CenterUniqueMin 1586 ∧ DipHyp 1586 ∧ OnePointHyps 1586 :=
  cen_of L1586_ok H1586_ok I1586_ok link1586 cenlink1586

/-! ### `N = 1587` -/

def pL1587 : Prm := ⟨81, 39, 39, 1589, 11, 18446744073709551616, 118853464944994006, 118853464944994006⟩
def pH1587 : Prm := ⟨82, 40, 39, 1589, 11, 18446744073709551616, 118854564456621782, 118854564456621782⟩
def pI1587 : Prm := ⟨67, 33, 31, 1589, 11, 18446744073709551616, 118853464944994006, 118854564456621782⟩
noncomputable def L1587_cp1 : Nat × Nat := t7val% (fastRun pL1587 1 1121 (init pL1587) (init pL1587))
theorem L1587_seg1 : segOK pL1587 1 1121 (init pL1587) (init pL1587) L1587_cp1.1 L1587_cp1.2 = true := by
  decide +kernel
theorem L1587_fin : (prmOK pL1587 1587 && ptTest pL1587 (runFrom pL1587 (fmask pL1587) (cmask pL1587) (hmask pL1587) 1122 465 (true, L1587_cp1.1, L1587_cp1.2)) 1587 794 false) = true := by
  decide +kernel
theorem L1587_ok : RunOK pL1587 1587 (runFrom pL1587 (fmask pL1587) (cmask pL1587) (hmask pL1587) 1122 465 (true, L1587_cp1.1, L1587_cp1.2)) ∧ ptTest pL1587 (runFrom pL1587 (fmask pL1587) (cmask pL1587) (hmask pL1587) 1122 465 (true, L1587_cp1.1, L1587_cp1.2)) 1587 794 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1587_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1587_fin) true) L1587_seg1) (by decide) rfl L1587_fin ptTest_fst
noncomputable def H1587_cp1 : Nat × Nat := t7val% (fastRun pH1587 1 1121 (init pH1587) (init pH1587))
theorem H1587_seg1 : segOK pH1587 1 1121 (init pH1587) (init pH1587) H1587_cp1.1 H1587_cp1.2 = true := by
  decide +kernel
theorem H1587_fin : (prmOK pH1587 1587 && ptTest pH1587 (runFrom pH1587 (fmask pH1587) (cmask pH1587) (hmask pH1587) 1122 465 (true, H1587_cp1.1, H1587_cp1.2)) 1587 794 true) = true := by
  decide +kernel
theorem H1587_ok : RunOK pH1587 1587 (runFrom pH1587 (fmask pH1587) (cmask pH1587) (hmask pH1587) 1122 465 (true, H1587_cp1.1, H1587_cp1.2)) ∧ ptTest pH1587 (runFrom pH1587 (fmask pH1587) (cmask pH1587) (hmask pH1587) 1122 465 (true, H1587_cp1.1, H1587_cp1.2)) 1587 794 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1587_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1587_fin) true) H1587_seg1) (by decide) rfl H1587_fin ptTest_fst
noncomputable def I1587_cp1 : Nat × Nat := t7val% (fastRun pI1587 1 1121 (init pI1587) (init pI1587))
theorem I1587_seg1 : segOK pI1587 1 1121 (init pI1587) (init pI1587) I1587_cp1.1 I1587_cp1.2 = true := by
  decide +kernel
theorem I1587_fin : (prmOK pI1587 1587 && intTest pI1587 (runFrom pI1587 (fmask pI1587) (cmask pI1587) (hmask pI1587) 1122 465 (true, I1587_cp1.1, I1587_cp1.2)) 1587 20 false) = true := by
  decide +kernel
theorem I1587_ok : RunOK pI1587 1587 (runFrom pI1587 (fmask pI1587) (cmask pI1587) (hmask pI1587) 1122 465 (true, I1587_cp1.1, I1587_cp1.2)) ∧ intTest pI1587 (runFrom pI1587 (fmask pI1587) (cmask pI1587) (hmask pI1587) 1122 465 (true, I1587_cp1.1, I1587_cp1.2)) 1587 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1587_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1587_fin) true) I1587_seg1) (by decide) rfl I1587_fin intTest_fst
theorem link1587 : linkOK pL1587 pH1587 pI1587 = true := by decide +kernel
theorem cvx1587 : ConvexBetweenHumps 1587 :=
  cvx_of L1587_ok H1587_ok I1587_ok link1587 (by decide)

/-! ### `N = 1588` -/

def pL1588 : Prm := ⟨81, 39, 39, 1590, 11, 18446744073709551616, 118792430151521587, 118792430151521587⟩
def pH1588 : Prm := ⟨82, 40, 39, 1590, 11, 18446744073709551616, 118793529663149363, 118793529663149363⟩
def pI1588 : Prm := ⟨67, 33, 31, 1590, 11, 18446744073709551616, 118792430151521587, 118793529663149363⟩
noncomputable def L1588_cp1 : Nat × Nat := t7val% (fastRun pL1588 1 1122 (init pL1588) (init pL1588))
theorem L1588_seg1 : segOK pL1588 1 1122 (init pL1588) (init pL1588) L1588_cp1.1 L1588_cp1.2 = true := by
  decide +kernel
theorem L1588_fin : (prmOK pL1588 1588 && ptTest pL1588 (runFrom pL1588 (fmask pL1588) (cmask pL1588) (hmask pL1588) 1123 465 (true, L1588_cp1.1, L1588_cp1.2)) 1588 794 false) = true := by
  decide +kernel
theorem L1588_ok : RunOK pL1588 1588 (runFrom pL1588 (fmask pL1588) (cmask pL1588) (hmask pL1588) 1123 465 (true, L1588_cp1.1, L1588_cp1.2)) ∧ ptTest pL1588 (runFrom pL1588 (fmask pL1588) (cmask pL1588) (hmask pL1588) 1123 465 (true, L1588_cp1.1, L1588_cp1.2)) 1588 794 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1588_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1588_fin) true) L1588_seg1) (by decide) rfl L1588_fin ptTest_fst
noncomputable def H1588_cp1 : Nat × Nat := t7val% (fastRun pH1588 1 1122 (init pH1588) (init pH1588))
theorem H1588_seg1 : segOK pH1588 1 1122 (init pH1588) (init pH1588) H1588_cp1.1 H1588_cp1.2 = true := by
  decide +kernel
theorem H1588_fin : (prmOK pH1588 1588 && ptTest pH1588 (runFrom pH1588 (fmask pH1588) (cmask pH1588) (hmask pH1588) 1123 465 (true, H1588_cp1.1, H1588_cp1.2)) 1588 794 true) = true := by
  decide +kernel
theorem H1588_ok : RunOK pH1588 1588 (runFrom pH1588 (fmask pH1588) (cmask pH1588) (hmask pH1588) 1123 465 (true, H1588_cp1.1, H1588_cp1.2)) ∧ ptTest pH1588 (runFrom pH1588 (fmask pH1588) (cmask pH1588) (hmask pH1588) 1123 465 (true, H1588_cp1.1, H1588_cp1.2)) 1588 794 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1588_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1588_fin) true) H1588_seg1) (by decide) rfl H1588_fin ptTest_fst
noncomputable def I1588_cp1 : Nat × Nat := t7val% (fastRun pI1588 1 1122 (init pI1588) (init pI1588))
theorem I1588_seg1 : segOK pI1588 1 1122 (init pI1588) (init pI1588) I1588_cp1.1 I1588_cp1.2 = true := by
  decide +kernel
theorem I1588_fin : (prmOK pI1588 1588 && intTest pI1588 (runFrom pI1588 (fmask pI1588) (cmask pI1588) (hmask pI1588) 1123 465 (true, I1588_cp1.1, I1588_cp1.2)) 1588 20 true) = true := by
  decide +kernel
theorem I1588_ok : RunOK pI1588 1588 (runFrom pI1588 (fmask pI1588) (cmask pI1588) (hmask pI1588) 1123 465 (true, I1588_cp1.1, I1588_cp1.2)) ∧ intTest pI1588 (runFrom pI1588 (fmask pI1588) (cmask pI1588) (hmask pI1588) 1123 465 (true, I1588_cp1.1, I1588_cp1.2)) 1588 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1588_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1588_fin) true) I1588_seg1) (by decide) rfl I1588_fin intTest_fst
theorem link1588 : linkOK pL1588 pH1588 pI1588 = true := by decide +kernel
theorem cvx1588 : ConvexBetweenHumps 1588 :=
  cvx_of L1588_ok H1588_ok I1588_ok link1588 (by decide)
theorem cenlink1588 : cenLinkOK pI1588 1588 = true := by decide +kernel
theorem cen1588 : CenterUniqueMin 1588 ∧ DipHyp 1588 ∧ OnePointHyps 1588 :=
  cen_of L1588_ok H1588_ok I1588_ok link1588 cenlink1588

/-! ### `N = 1589` -/

def pL1589 : Prm := ⟨82, 40, 39, 1591, 11, 18446744073709551616, 118731435316777439, 118731435316777439⟩
def pH1589 : Prm := ⟨82, 40, 39, 1591, 11, 18446744073709551616, 118732534828405215, 118732534828405215⟩
def pI1589 : Prm := ⟨67, 33, 31, 1591, 11, 18446744073709551616, 118731435316777439, 118732534828405215⟩
noncomputable def L1589_cp1 : Nat × Nat := t7val% (fastRun pL1589 1 1123 (init pL1589) (init pL1589))
theorem L1589_seg1 : segOK pL1589 1 1123 (init pL1589) (init pL1589) L1589_cp1.1 L1589_cp1.2 = true := by
  decide +kernel
theorem L1589_fin : (prmOK pL1589 1589 && ptTest pL1589 (runFrom pL1589 (fmask pL1589) (cmask pL1589) (hmask pL1589) 1124 465 (true, L1589_cp1.1, L1589_cp1.2)) 1589 795 false) = true := by
  decide +kernel
theorem L1589_ok : RunOK pL1589 1589 (runFrom pL1589 (fmask pL1589) (cmask pL1589) (hmask pL1589) 1124 465 (true, L1589_cp1.1, L1589_cp1.2)) ∧ ptTest pL1589 (runFrom pL1589 (fmask pL1589) (cmask pL1589) (hmask pL1589) 1124 465 (true, L1589_cp1.1, L1589_cp1.2)) 1589 795 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1589_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1589_fin) true) L1589_seg1) (by decide) rfl L1589_fin ptTest_fst
noncomputable def H1589_cp1 : Nat × Nat := t7val% (fastRun pH1589 1 1123 (init pH1589) (init pH1589))
theorem H1589_seg1 : segOK pH1589 1 1123 (init pH1589) (init pH1589) H1589_cp1.1 H1589_cp1.2 = true := by
  decide +kernel
theorem H1589_fin : (prmOK pH1589 1589 && ptTest pH1589 (runFrom pH1589 (fmask pH1589) (cmask pH1589) (hmask pH1589) 1124 465 (true, H1589_cp1.1, H1589_cp1.2)) 1589 795 true) = true := by
  decide +kernel
theorem H1589_ok : RunOK pH1589 1589 (runFrom pH1589 (fmask pH1589) (cmask pH1589) (hmask pH1589) 1124 465 (true, H1589_cp1.1, H1589_cp1.2)) ∧ ptTest pH1589 (runFrom pH1589 (fmask pH1589) (cmask pH1589) (hmask pH1589) 1124 465 (true, H1589_cp1.1, H1589_cp1.2)) 1589 795 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1589_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1589_fin) true) H1589_seg1) (by decide) rfl H1589_fin ptTest_fst
noncomputable def I1589_cp1 : Nat × Nat := t7val% (fastRun pI1589 1 1123 (init pI1589) (init pI1589))
theorem I1589_seg1 : segOK pI1589 1 1123 (init pI1589) (init pI1589) I1589_cp1.1 I1589_cp1.2 = true := by
  decide +kernel
theorem I1589_fin : (prmOK pI1589 1589 && intTest pI1589 (runFrom pI1589 (fmask pI1589) (cmask pI1589) (hmask pI1589) 1124 465 (true, I1589_cp1.1, I1589_cp1.2)) 1589 20 false) = true := by
  decide +kernel
theorem I1589_ok : RunOK pI1589 1589 (runFrom pI1589 (fmask pI1589) (cmask pI1589) (hmask pI1589) 1124 465 (true, I1589_cp1.1, I1589_cp1.2)) ∧ intTest pI1589 (runFrom pI1589 (fmask pI1589) (cmask pI1589) (hmask pI1589) 1124 465 (true, I1589_cp1.1, I1589_cp1.2)) 1589 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1589_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1589_fin) true) I1589_seg1) (by decide) rfl I1589_fin intTest_fst
theorem link1589 : linkOK pL1589 pH1589 pI1589 = true := by decide +kernel
theorem cvx1589 : ConvexBetweenHumps 1589 :=
  cvx_of L1589_ok H1589_ok I1589_ok link1589 (by decide)

/-! ### `N = 1590` -/

def pL1590 : Prm := ⟨82, 40, 39, 1592, 11, 18446744073709551616, 118670536649743194, 118670536649743194⟩
def pH1590 : Prm := ⟨82, 40, 39, 1592, 11, 18446744073709551616, 118671636161370970, 118671636161370970⟩
def pI1590 : Prm := ⟨67, 33, 31, 1592, 11, 18446744073709551616, 118670536649743194, 118671636161370970⟩
noncomputable def L1590_cp1 : Nat × Nat := t7val% (fastRun pL1590 1 1123 (init pL1590) (init pL1590))
theorem L1590_seg1 : segOK pL1590 1 1123 (init pL1590) (init pL1590) L1590_cp1.1 L1590_cp1.2 = true := by
  decide +kernel
theorem L1590_fin : (prmOK pL1590 1590 && ptTest pL1590 (runFrom pL1590 (fmask pL1590) (cmask pL1590) (hmask pL1590) 1124 466 (true, L1590_cp1.1, L1590_cp1.2)) 1590 795 false) = true := by
  decide +kernel
theorem L1590_ok : RunOK pL1590 1590 (runFrom pL1590 (fmask pL1590) (cmask pL1590) (hmask pL1590) 1124 466 (true, L1590_cp1.1, L1590_cp1.2)) ∧ ptTest pL1590 (runFrom pL1590 (fmask pL1590) (cmask pL1590) (hmask pL1590) 1124 466 (true, L1590_cp1.1, L1590_cp1.2)) 1590 795 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1590_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1590_fin) true) L1590_seg1) (by decide) rfl L1590_fin ptTest_fst
noncomputable def H1590_cp1 : Nat × Nat := t7val% (fastRun pH1590 1 1123 (init pH1590) (init pH1590))
theorem H1590_seg1 : segOK pH1590 1 1123 (init pH1590) (init pH1590) H1590_cp1.1 H1590_cp1.2 = true := by
  decide +kernel
theorem H1590_fin : (prmOK pH1590 1590 && ptTest pH1590 (runFrom pH1590 (fmask pH1590) (cmask pH1590) (hmask pH1590) 1124 466 (true, H1590_cp1.1, H1590_cp1.2)) 1590 795 true) = true := by
  decide +kernel
theorem H1590_ok : RunOK pH1590 1590 (runFrom pH1590 (fmask pH1590) (cmask pH1590) (hmask pH1590) 1124 466 (true, H1590_cp1.1, H1590_cp1.2)) ∧ ptTest pH1590 (runFrom pH1590 (fmask pH1590) (cmask pH1590) (hmask pH1590) 1124 466 (true, H1590_cp1.1, H1590_cp1.2)) 1590 795 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1590_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1590_fin) true) H1590_seg1) (by decide) rfl H1590_fin ptTest_fst
noncomputable def I1590_cp1 : Nat × Nat := t7val% (fastRun pI1590 1 1123 (init pI1590) (init pI1590))
theorem I1590_seg1 : segOK pI1590 1 1123 (init pI1590) (init pI1590) I1590_cp1.1 I1590_cp1.2 = true := by
  decide +kernel
theorem I1590_fin : (prmOK pI1590 1590 && intTest pI1590 (runFrom pI1590 (fmask pI1590) (cmask pI1590) (hmask pI1590) 1124 466 (true, I1590_cp1.1, I1590_cp1.2)) 1590 20 true) = true := by
  decide +kernel
theorem I1590_ok : RunOK pI1590 1590 (runFrom pI1590 (fmask pI1590) (cmask pI1590) (hmask pI1590) 1124 466 (true, I1590_cp1.1, I1590_cp1.2)) ∧ intTest pI1590 (runFrom pI1590 (fmask pI1590) (cmask pI1590) (hmask pI1590) 1124 466 (true, I1590_cp1.1, I1590_cp1.2)) 1590 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1590_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1590_fin) true) I1590_seg1) (by decide) rfl I1590_fin intTest_fst
theorem link1590 : linkOK pL1590 pH1590 pI1590 = true := by decide +kernel
theorem cvx1590 : ConvexBetweenHumps 1590 :=
  cvx_of L1590_ok H1590_ok I1590_ok link1590 (by decide)
theorem cenlink1590 : cenLinkOK pI1590 1590 = true := by decide +kernel
theorem cen1590 : CenterUniqueMin 1590 ∧ DipHyp 1590 ∧ OnePointHyps 1590 :=
  cen_of L1590_ok H1590_ok I1590_ok link1590 cenlink1590

/-! ### `N = 1591` -/

def pL1591 : Prm := ⟨81, 39, 39, 1593, 11, 18446744073709551616, 118609677814320705, 118609677814320705⟩
def pH1591 : Prm := ⟨81, 39, 39, 1593, 11, 18446744073709551616, 118610777325948481, 118610777325948481⟩
def pI1591 : Prm := ⟨67, 33, 31, 1593, 11, 18446744073709551616, 118609677814320705, 118610777325948481⟩
noncomputable def L1591_cp1 : Nat × Nat := t7val% (fastRun pL1591 1 1124 (init pL1591) (init pL1591))
theorem L1591_seg1 : segOK pL1591 1 1124 (init pL1591) (init pL1591) L1591_cp1.1 L1591_cp1.2 = true := by
  decide +kernel
theorem L1591_fin : (prmOK pL1591 1591 && ptTest pL1591 (runFrom pL1591 (fmask pL1591) (cmask pL1591) (hmask pL1591) 1125 466 (true, L1591_cp1.1, L1591_cp1.2)) 1591 796 false) = true := by
  decide +kernel
theorem L1591_ok : RunOK pL1591 1591 (runFrom pL1591 (fmask pL1591) (cmask pL1591) (hmask pL1591) 1125 466 (true, L1591_cp1.1, L1591_cp1.2)) ∧ ptTest pL1591 (runFrom pL1591 (fmask pL1591) (cmask pL1591) (hmask pL1591) 1125 466 (true, L1591_cp1.1, L1591_cp1.2)) 1591 796 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1591_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1591_fin) true) L1591_seg1) (by decide) rfl L1591_fin ptTest_fst
noncomputable def H1591_cp1 : Nat × Nat := t7val% (fastRun pH1591 1 1124 (init pH1591) (init pH1591))
theorem H1591_seg1 : segOK pH1591 1 1124 (init pH1591) (init pH1591) H1591_cp1.1 H1591_cp1.2 = true := by
  decide +kernel
theorem H1591_fin : (prmOK pH1591 1591 && ptTest pH1591 (runFrom pH1591 (fmask pH1591) (cmask pH1591) (hmask pH1591) 1125 466 (true, H1591_cp1.1, H1591_cp1.2)) 1591 796 true) = true := by
  decide +kernel
theorem H1591_ok : RunOK pH1591 1591 (runFrom pH1591 (fmask pH1591) (cmask pH1591) (hmask pH1591) 1125 466 (true, H1591_cp1.1, H1591_cp1.2)) ∧ ptTest pH1591 (runFrom pH1591 (fmask pH1591) (cmask pH1591) (hmask pH1591) 1125 466 (true, H1591_cp1.1, H1591_cp1.2)) 1591 796 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1591_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1591_fin) true) H1591_seg1) (by decide) rfl H1591_fin ptTest_fst
noncomputable def I1591_cp1 : Nat × Nat := t7val% (fastRun pI1591 1 1124 (init pI1591) (init pI1591))
theorem I1591_seg1 : segOK pI1591 1 1124 (init pI1591) (init pI1591) I1591_cp1.1 I1591_cp1.2 = true := by
  decide +kernel
theorem I1591_fin : (prmOK pI1591 1591 && intTest pI1591 (runFrom pI1591 (fmask pI1591) (cmask pI1591) (hmask pI1591) 1125 466 (true, I1591_cp1.1, I1591_cp1.2)) 1591 20 false) = true := by
  decide +kernel
theorem I1591_ok : RunOK pI1591 1591 (runFrom pI1591 (fmask pI1591) (cmask pI1591) (hmask pI1591) 1125 466 (true, I1591_cp1.1, I1591_cp1.2)) ∧ intTest pI1591 (runFrom pI1591 (fmask pI1591) (cmask pI1591) (hmask pI1591) 1125 466 (true, I1591_cp1.1, I1591_cp1.2)) 1591 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1591_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1591_fin) true) I1591_seg1) (by decide) rfl I1591_fin intTest_fst
theorem link1591 : linkOK pL1591 pH1591 pI1591 = true := by decide +kernel
theorem cvx1591 : ConvexBetweenHumps 1591 :=
  cvx_of L1591_ok H1591_ok I1591_ok link1591 (by decide)

/-! ### `N = 1592` -/

def pL1592 : Prm := ⟨82, 40, 39, 1594, 11, 18446744073709551616, 118548914804476358, 118548914804476358⟩
def pH1592 : Prm := ⟨82, 40, 39, 1594, 11, 18446744073709551616, 118550014316104134, 118550014316104134⟩
def pI1592 : Prm := ⟨67, 33, 31, 1594, 11, 18446744073709551616, 118548914804476358, 118550014316104134⟩
noncomputable def L1592_cp1 : Nat × Nat := t7val% (fastRun pL1592 1 1125 (init pL1592) (init pL1592))
theorem L1592_seg1 : segOK pL1592 1 1125 (init pL1592) (init pL1592) L1592_cp1.1 L1592_cp1.2 = true := by
  decide +kernel
theorem L1592_fin : (prmOK pL1592 1592 && ptTest pL1592 (runFrom pL1592 (fmask pL1592) (cmask pL1592) (hmask pL1592) 1126 466 (true, L1592_cp1.1, L1592_cp1.2)) 1592 796 false) = true := by
  decide +kernel
theorem L1592_ok : RunOK pL1592 1592 (runFrom pL1592 (fmask pL1592) (cmask pL1592) (hmask pL1592) 1126 466 (true, L1592_cp1.1, L1592_cp1.2)) ∧ ptTest pL1592 (runFrom pL1592 (fmask pL1592) (cmask pL1592) (hmask pL1592) 1126 466 (true, L1592_cp1.1, L1592_cp1.2)) 1592 796 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1592_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1592_fin) true) L1592_seg1) (by decide) rfl L1592_fin ptTest_fst
noncomputable def H1592_cp1 : Nat × Nat := t7val% (fastRun pH1592 1 1125 (init pH1592) (init pH1592))
theorem H1592_seg1 : segOK pH1592 1 1125 (init pH1592) (init pH1592) H1592_cp1.1 H1592_cp1.2 = true := by
  decide +kernel
theorem H1592_fin : (prmOK pH1592 1592 && ptTest pH1592 (runFrom pH1592 (fmask pH1592) (cmask pH1592) (hmask pH1592) 1126 466 (true, H1592_cp1.1, H1592_cp1.2)) 1592 796 true) = true := by
  decide +kernel
theorem H1592_ok : RunOK pH1592 1592 (runFrom pH1592 (fmask pH1592) (cmask pH1592) (hmask pH1592) 1126 466 (true, H1592_cp1.1, H1592_cp1.2)) ∧ ptTest pH1592 (runFrom pH1592 (fmask pH1592) (cmask pH1592) (hmask pH1592) 1126 466 (true, H1592_cp1.1, H1592_cp1.2)) 1592 796 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1592_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1592_fin) true) H1592_seg1) (by decide) rfl H1592_fin ptTest_fst
noncomputable def I1592_cp1 : Nat × Nat := t7val% (fastRun pI1592 1 1125 (init pI1592) (init pI1592))
theorem I1592_seg1 : segOK pI1592 1 1125 (init pI1592) (init pI1592) I1592_cp1.1 I1592_cp1.2 = true := by
  decide +kernel
theorem I1592_fin : (prmOK pI1592 1592 && intTest pI1592 (runFrom pI1592 (fmask pI1592) (cmask pI1592) (hmask pI1592) 1126 466 (true, I1592_cp1.1, I1592_cp1.2)) 1592 20 true) = true := by
  decide +kernel
theorem I1592_ok : RunOK pI1592 1592 (runFrom pI1592 (fmask pI1592) (cmask pI1592) (hmask pI1592) 1126 466 (true, I1592_cp1.1, I1592_cp1.2)) ∧ intTest pI1592 (runFrom pI1592 (fmask pI1592) (cmask pI1592) (hmask pI1592) 1126 466 (true, I1592_cp1.1, I1592_cp1.2)) 1592 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1592_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1592_fin) true) I1592_seg1) (by decide) rfl I1592_fin intTest_fst
theorem link1592 : linkOK pL1592 pH1592 pI1592 = true := by decide +kernel
theorem cvx1592 : ConvexBetweenHumps 1592 :=
  cvx_of L1592_ok H1592_ok I1592_ok link1592 (by decide)
theorem cenlink1592 : cenLinkOK pI1592 1592 = true := by decide +kernel
theorem cen1592 : CenterUniqueMin 1592 ∧ DipHyp 1592 ∧ OnePointHyps 1592 :=
  cen_of L1592_ok H1592_ok I1592_ok link1592 cenlink1592

/-! ### `N = 1593` -/

def pL1593 : Prm := ⟨82, 40, 39, 1595, 11, 18446744073709551616, 118488191499680655, 118488191499680655⟩
def pH1593 : Prm := ⟨82, 40, 39, 1595, 11, 18446744073709551616, 118489291011308431, 118489291011308431⟩
def pI1593 : Prm := ⟨67, 33, 31, 1595, 11, 18446744073709551616, 118488191499680655, 118489291011308431⟩
noncomputable def L1593_cp1 : Nat × Nat := t7val% (fastRun pL1593 1 1125 (init pL1593) (init pL1593))
theorem L1593_seg1 : segOK pL1593 1 1125 (init pL1593) (init pL1593) L1593_cp1.1 L1593_cp1.2 = true := by
  decide +kernel
theorem L1593_fin : (prmOK pL1593 1593 && ptTest pL1593 (runFrom pL1593 (fmask pL1593) (cmask pL1593) (hmask pL1593) 1126 467 (true, L1593_cp1.1, L1593_cp1.2)) 1593 797 false) = true := by
  decide +kernel
theorem L1593_ok : RunOK pL1593 1593 (runFrom pL1593 (fmask pL1593) (cmask pL1593) (hmask pL1593) 1126 467 (true, L1593_cp1.1, L1593_cp1.2)) ∧ ptTest pL1593 (runFrom pL1593 (fmask pL1593) (cmask pL1593) (hmask pL1593) 1126 467 (true, L1593_cp1.1, L1593_cp1.2)) 1593 797 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1593_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1593_fin) true) L1593_seg1) (by decide) rfl L1593_fin ptTest_fst
noncomputable def H1593_cp1 : Nat × Nat := t7val% (fastRun pH1593 1 1125 (init pH1593) (init pH1593))
theorem H1593_seg1 : segOK pH1593 1 1125 (init pH1593) (init pH1593) H1593_cp1.1 H1593_cp1.2 = true := by
  decide +kernel
theorem H1593_fin : (prmOK pH1593 1593 && ptTest pH1593 (runFrom pH1593 (fmask pH1593) (cmask pH1593) (hmask pH1593) 1126 467 (true, H1593_cp1.1, H1593_cp1.2)) 1593 797 true) = true := by
  decide +kernel
theorem H1593_ok : RunOK pH1593 1593 (runFrom pH1593 (fmask pH1593) (cmask pH1593) (hmask pH1593) 1126 467 (true, H1593_cp1.1, H1593_cp1.2)) ∧ ptTest pH1593 (runFrom pH1593 (fmask pH1593) (cmask pH1593) (hmask pH1593) 1126 467 (true, H1593_cp1.1, H1593_cp1.2)) 1593 797 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1593_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1593_fin) true) H1593_seg1) (by decide) rfl H1593_fin ptTest_fst
noncomputable def I1593_cp1 : Nat × Nat := t7val% (fastRun pI1593 1 1125 (init pI1593) (init pI1593))
theorem I1593_seg1 : segOK pI1593 1 1125 (init pI1593) (init pI1593) I1593_cp1.1 I1593_cp1.2 = true := by
  decide +kernel
theorem I1593_fin : (prmOK pI1593 1593 && intTest pI1593 (runFrom pI1593 (fmask pI1593) (cmask pI1593) (hmask pI1593) 1126 467 (true, I1593_cp1.1, I1593_cp1.2)) 1593 20 false) = true := by
  decide +kernel
theorem I1593_ok : RunOK pI1593 1593 (runFrom pI1593 (fmask pI1593) (cmask pI1593) (hmask pI1593) 1126 467 (true, I1593_cp1.1, I1593_cp1.2)) ∧ intTest pI1593 (runFrom pI1593 (fmask pI1593) (cmask pI1593) (hmask pI1593) 1126 467 (true, I1593_cp1.1, I1593_cp1.2)) 1593 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1593_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1593_fin) true) I1593_seg1) (by decide) rfl I1593_fin intTest_fst
theorem link1593 : linkOK pL1593 pH1593 pI1593 = true := by decide +kernel
theorem cvx1593 : ConvexBetweenHumps 1593 :=
  cvx_of L1593_ok H1593_ok I1593_ok link1593 (by decide)

/-! ### The range -/

theorem cvx_1579_1593 {N : ℕ} (h1 : 1579 ≤ N) (h2 : N ≤ 1593) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1585
  · by_cases h4 : N ≤ 1581
    · by_cases h6 : N ≤ 1579
      · obtain rfl : N = 1579 := by omega
        exact cvx1579
      · by_cases h8 : N ≤ 1580
        · obtain rfl : N = 1580 := by omega
          exact cvx1580
        · obtain rfl : N = 1581 := by omega
          exact cvx1581
    · by_cases h6 : N ≤ 1583
      · by_cases h8 : N ≤ 1582
        · obtain rfl : N = 1582 := by omega
          exact cvx1582
        · obtain rfl : N = 1583 := by omega
          exact cvx1583
      · by_cases h8 : N ≤ 1584
        · obtain rfl : N = 1584 := by omega
          exact cvx1584
        · obtain rfl : N = 1585 := by omega
          exact cvx1585
  · by_cases h4 : N ≤ 1589
    · by_cases h6 : N ≤ 1587
      · by_cases h8 : N ≤ 1586
        · obtain rfl : N = 1586 := by omega
          exact cvx1586
        · obtain rfl : N = 1587 := by omega
          exact cvx1587
      · by_cases h8 : N ≤ 1588
        · obtain rfl : N = 1588 := by omega
          exact cvx1588
        · obtain rfl : N = 1589 := by omega
          exact cvx1589
    · by_cases h6 : N ≤ 1591
      · by_cases h8 : N ≤ 1590
        · obtain rfl : N = 1590 := by omega
          exact cvx1590
        · obtain rfl : N = 1591 := by omega
          exact cvx1591
      · by_cases h8 : N ≤ 1592
        · obtain rfl : N = 1592 := by omega
          exact cvx1592
        · obtain rfl : N = 1593 := by omega
          exact cvx1593

theorem cen_1579_1593 {N : ℕ} (h1 : 1579 ≤ N) (h2 : N ≤ 1593) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1584
  · by_cases h4 : N ≤ 1580
    · obtain rfl : N = 1580 := by omega
      exact cen1580
    · by_cases h6 : N ≤ 1582
      · obtain rfl : N = 1582 := by omega
        exact cen1582
      · obtain rfl : N = 1584 := by omega
        exact cen1584
  · by_cases h4 : N ≤ 1588
    · by_cases h6 : N ≤ 1586
      · obtain rfl : N = 1586 := by omega
        exact cen1586
      · obtain rfl : N = 1588 := by omega
        exact cen1588
    · by_cases h6 : N ≤ 1590
      · obtain rfl : N = 1590 := by omega
        exact cen1590
      · obtain rfl : N = 1592 := by omega
        exact cen1592

end Kagey131.PaperD.T7
