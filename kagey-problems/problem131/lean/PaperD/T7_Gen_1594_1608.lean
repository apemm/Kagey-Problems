import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1594, …, 1608` (generated)

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

/-! ### `N = 1594` -/

def pL1594 : Prm := ⟨81, 39, 39, 1596, 11, 18446744073709551616, 118427563679954644, 118427563679954644⟩
def pH1594 : Prm := ⟨82, 40, 39, 1596, 11, 18446744073709551616, 118428663191582420, 118428663191582420⟩
def pI1594 : Prm := ⟨67, 33, 31, 1596, 11, 18446744073709551616, 118427563679954644, 118428663191582420⟩
noncomputable def L1594_cp1 : Nat × Nat := t7val% (fastRun pL1594 1 1126 (init pL1594) (init pL1594))
theorem L1594_seg1 : segOK pL1594 1 1126 (init pL1594) (init pL1594) L1594_cp1.1 L1594_cp1.2 = true := by
  decide +kernel
theorem L1594_fin : (prmOK pL1594 1594 && ptTest pL1594 (runFrom pL1594 (fmask pL1594) (cmask pL1594) (hmask pL1594) 1127 467 (true, L1594_cp1.1, L1594_cp1.2)) 1594 797 false) = true := by
  decide +kernel
theorem L1594_ok : RunOK pL1594 1594 (runFrom pL1594 (fmask pL1594) (cmask pL1594) (hmask pL1594) 1127 467 (true, L1594_cp1.1, L1594_cp1.2)) ∧ ptTest pL1594 (runFrom pL1594 (fmask pL1594) (cmask pL1594) (hmask pL1594) 1127 467 (true, L1594_cp1.1, L1594_cp1.2)) 1594 797 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1594_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1594_fin) true) L1594_seg1) (by decide) rfl L1594_fin ptTest_fst
noncomputable def H1594_cp1 : Nat × Nat := t7val% (fastRun pH1594 1 1126 (init pH1594) (init pH1594))
theorem H1594_seg1 : segOK pH1594 1 1126 (init pH1594) (init pH1594) H1594_cp1.1 H1594_cp1.2 = true := by
  decide +kernel
theorem H1594_fin : (prmOK pH1594 1594 && ptTest pH1594 (runFrom pH1594 (fmask pH1594) (cmask pH1594) (hmask pH1594) 1127 467 (true, H1594_cp1.1, H1594_cp1.2)) 1594 797 true) = true := by
  decide +kernel
theorem H1594_ok : RunOK pH1594 1594 (runFrom pH1594 (fmask pH1594) (cmask pH1594) (hmask pH1594) 1127 467 (true, H1594_cp1.1, H1594_cp1.2)) ∧ ptTest pH1594 (runFrom pH1594 (fmask pH1594) (cmask pH1594) (hmask pH1594) 1127 467 (true, H1594_cp1.1, H1594_cp1.2)) 1594 797 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1594_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1594_fin) true) H1594_seg1) (by decide) rfl H1594_fin ptTest_fst
noncomputable def I1594_cp1 : Nat × Nat := t7val% (fastRun pI1594 1 1126 (init pI1594) (init pI1594))
theorem I1594_seg1 : segOK pI1594 1 1126 (init pI1594) (init pI1594) I1594_cp1.1 I1594_cp1.2 = true := by
  decide +kernel
theorem I1594_fin : (prmOK pI1594 1594 && intTest pI1594 (runFrom pI1594 (fmask pI1594) (cmask pI1594) (hmask pI1594) 1127 467 (true, I1594_cp1.1, I1594_cp1.2)) 1594 20 true) = true := by
  decide +kernel
theorem I1594_ok : RunOK pI1594 1594 (runFrom pI1594 (fmask pI1594) (cmask pI1594) (hmask pI1594) 1127 467 (true, I1594_cp1.1, I1594_cp1.2)) ∧ intTest pI1594 (runFrom pI1594 (fmask pI1594) (cmask pI1594) (hmask pI1594) 1127 467 (true, I1594_cp1.1, I1594_cp1.2)) 1594 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1594_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1594_fin) true) I1594_seg1) (by decide) rfl I1594_fin intTest_fst
theorem link1594 : linkOK pL1594 pH1594 pI1594 = true := by decide +kernel
theorem cvx1594 : ConvexBetweenHumps 1594 :=
  cvx_of L1594_ok H1594_ok I1594_ok link1594 (by decide)
theorem cenlink1594 : cenLinkOK pI1594 1594 = true := by decide +kernel
theorem cen1594 : CenterUniqueMin 1594 ∧ DipHyp 1594 ∧ OnePointHyps 1594 :=
  cen_of L1594_ok H1594_ok I1594_ok link1594 cenlink1594

/-! ### `N = 1595` -/

def pL1595 : Prm := ⟨82, 40, 39, 1597, 11, 18446744073709551616, 118366975439267571, 118366975439267571⟩
def pH1595 : Prm := ⟨82, 40, 39, 1597, 11, 18446744073709551616, 118368074950895347, 118368074950895347⟩
def pI1595 : Prm := ⟨67, 33, 31, 1597, 11, 18446744073709551616, 118366975439267571, 118368074950895347⟩
noncomputable def L1595_cp1 : Nat × Nat := t7val% (fastRun pL1595 1 1127 (init pL1595) (init pL1595))
theorem L1595_seg1 : segOK pL1595 1 1127 (init pL1595) (init pL1595) L1595_cp1.1 L1595_cp1.2 = true := by
  decide +kernel
theorem L1595_fin : (prmOK pL1595 1595 && ptTest pL1595 (runFrom pL1595 (fmask pL1595) (cmask pL1595) (hmask pL1595) 1128 467 (true, L1595_cp1.1, L1595_cp1.2)) 1595 798 false) = true := by
  decide +kernel
theorem L1595_ok : RunOK pL1595 1595 (runFrom pL1595 (fmask pL1595) (cmask pL1595) (hmask pL1595) 1128 467 (true, L1595_cp1.1, L1595_cp1.2)) ∧ ptTest pL1595 (runFrom pL1595 (fmask pL1595) (cmask pL1595) (hmask pL1595) 1128 467 (true, L1595_cp1.1, L1595_cp1.2)) 1595 798 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1595_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1595_fin) true) L1595_seg1) (by decide) rfl L1595_fin ptTest_fst
noncomputable def H1595_cp1 : Nat × Nat := t7val% (fastRun pH1595 1 1127 (init pH1595) (init pH1595))
theorem H1595_seg1 : segOK pH1595 1 1127 (init pH1595) (init pH1595) H1595_cp1.1 H1595_cp1.2 = true := by
  decide +kernel
theorem H1595_fin : (prmOK pH1595 1595 && ptTest pH1595 (runFrom pH1595 (fmask pH1595) (cmask pH1595) (hmask pH1595) 1128 467 (true, H1595_cp1.1, H1595_cp1.2)) 1595 798 true) = true := by
  decide +kernel
theorem H1595_ok : RunOK pH1595 1595 (runFrom pH1595 (fmask pH1595) (cmask pH1595) (hmask pH1595) 1128 467 (true, H1595_cp1.1, H1595_cp1.2)) ∧ ptTest pH1595 (runFrom pH1595 (fmask pH1595) (cmask pH1595) (hmask pH1595) 1128 467 (true, H1595_cp1.1, H1595_cp1.2)) 1595 798 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1595_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1595_fin) true) H1595_seg1) (by decide) rfl H1595_fin ptTest_fst
noncomputable def I1595_cp1 : Nat × Nat := t7val% (fastRun pI1595 1 1127 (init pI1595) (init pI1595))
theorem I1595_seg1 : segOK pI1595 1 1127 (init pI1595) (init pI1595) I1595_cp1.1 I1595_cp1.2 = true := by
  decide +kernel
theorem I1595_fin : (prmOK pI1595 1595 && intTest pI1595 (runFrom pI1595 (fmask pI1595) (cmask pI1595) (hmask pI1595) 1128 467 (true, I1595_cp1.1, I1595_cp1.2)) 1595 20 false) = true := by
  decide +kernel
theorem I1595_ok : RunOK pI1595 1595 (runFrom pI1595 (fmask pI1595) (cmask pI1595) (hmask pI1595) 1128 467 (true, I1595_cp1.1, I1595_cp1.2)) ∧ intTest pI1595 (runFrom pI1595 (fmask pI1595) (cmask pI1595) (hmask pI1595) 1128 467 (true, I1595_cp1.1, I1595_cp1.2)) 1595 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1595_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1595_fin) true) I1595_seg1) (by decide) rfl I1595_fin intTest_fst
theorem link1595 : linkOK pL1595 pH1595 pI1595 = true := by decide +kernel
theorem cvx1595 : ConvexBetweenHumps 1595 :=
  cvx_of L1595_ok H1595_ok I1595_ok link1595 (by decide)

/-! ### `N = 1596` -/

def pL1596 : Prm := ⟨82, 40, 39, 1598, 11, 18446744073709551616, 118306482344783501, 118306482344783501⟩
def pH1596 : Prm := ⟨82, 40, 39, 1598, 11, 18446744073709551616, 118307581856411277, 118307581856411277⟩
def pI1596 : Prm := ⟨67, 33, 31, 1598, 11, 18446744073709551616, 118306482344783501, 118307581856411277⟩
noncomputable def L1596_cp1 : Nat × Nat := t7val% (fastRun pL1596 1 1128 (init pL1596) (init pL1596))
theorem L1596_seg1 : segOK pL1596 1 1128 (init pL1596) (init pL1596) L1596_cp1.1 L1596_cp1.2 = true := by
  decide +kernel
theorem L1596_fin : (prmOK pL1596 1596 && ptTest pL1596 (runFrom pL1596 (fmask pL1596) (cmask pL1596) (hmask pL1596) 1129 467 (true, L1596_cp1.1, L1596_cp1.2)) 1596 798 false) = true := by
  decide +kernel
theorem L1596_ok : RunOK pL1596 1596 (runFrom pL1596 (fmask pL1596) (cmask pL1596) (hmask pL1596) 1129 467 (true, L1596_cp1.1, L1596_cp1.2)) ∧ ptTest pL1596 (runFrom pL1596 (fmask pL1596) (cmask pL1596) (hmask pL1596) 1129 467 (true, L1596_cp1.1, L1596_cp1.2)) 1596 798 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1596_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1596_fin) true) L1596_seg1) (by decide) rfl L1596_fin ptTest_fst
noncomputable def H1596_cp1 : Nat × Nat := t7val% (fastRun pH1596 1 1128 (init pH1596) (init pH1596))
theorem H1596_seg1 : segOK pH1596 1 1128 (init pH1596) (init pH1596) H1596_cp1.1 H1596_cp1.2 = true := by
  decide +kernel
theorem H1596_fin : (prmOK pH1596 1596 && ptTest pH1596 (runFrom pH1596 (fmask pH1596) (cmask pH1596) (hmask pH1596) 1129 467 (true, H1596_cp1.1, H1596_cp1.2)) 1596 798 true) = true := by
  decide +kernel
theorem H1596_ok : RunOK pH1596 1596 (runFrom pH1596 (fmask pH1596) (cmask pH1596) (hmask pH1596) 1129 467 (true, H1596_cp1.1, H1596_cp1.2)) ∧ ptTest pH1596 (runFrom pH1596 (fmask pH1596) (cmask pH1596) (hmask pH1596) 1129 467 (true, H1596_cp1.1, H1596_cp1.2)) 1596 798 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1596_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1596_fin) true) H1596_seg1) (by decide) rfl H1596_fin ptTest_fst
noncomputable def I1596_cp1 : Nat × Nat := t7val% (fastRun pI1596 1 1128 (init pI1596) (init pI1596))
theorem I1596_seg1 : segOK pI1596 1 1128 (init pI1596) (init pI1596) I1596_cp1.1 I1596_cp1.2 = true := by
  decide +kernel
theorem I1596_fin : (prmOK pI1596 1596 && intTest pI1596 (runFrom pI1596 (fmask pI1596) (cmask pI1596) (hmask pI1596) 1129 467 (true, I1596_cp1.1, I1596_cp1.2)) 1596 20 true) = true := by
  decide +kernel
theorem I1596_ok : RunOK pI1596 1596 (runFrom pI1596 (fmask pI1596) (cmask pI1596) (hmask pI1596) 1129 467 (true, I1596_cp1.1, I1596_cp1.2)) ∧ intTest pI1596 (runFrom pI1596 (fmask pI1596) (cmask pI1596) (hmask pI1596) 1129 467 (true, I1596_cp1.1, I1596_cp1.2)) 1596 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1596_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1596_fin) true) I1596_seg1) (by decide) rfl I1596_fin intTest_fst
theorem link1596 : linkOK pL1596 pH1596 pI1596 = true := by decide +kernel
theorem cvx1596 : ConvexBetweenHumps 1596 :=
  cvx_of L1596_ok H1596_ok I1596_ok link1596 (by decide)
theorem cenlink1596 : cenLinkOK pI1596 1596 = true := by decide +kernel
theorem cen1596 : CenterUniqueMin 1596 ∧ DipHyp 1596 ∧ OnePointHyps 1596 :=
  cen_of L1596_ok H1596_ok I1596_ok link1596 cenlink1596

/-! ### `N = 1597` -/

def pL1597 : Prm := ⟨82, 40, 39, 1599, 11, 18446744073709551616, 118246028703882060, 118246028703882060⟩
def pH1597 : Prm := ⟨82, 40, 39, 1599, 11, 18446744073709551616, 118247128215509836, 118247128215509836⟩
def pI1597 : Prm := ⟨67, 33, 31, 1599, 11, 18446744073709551616, 118246028703882060, 118247128215509836⟩
noncomputable def L1597_cp1 : Nat × Nat := t7val% (fastRun pL1597 1 1128 (init pL1597) (init pL1597))
theorem L1597_seg1 : segOK pL1597 1 1128 (init pL1597) (init pL1597) L1597_cp1.1 L1597_cp1.2 = true := by
  decide +kernel
theorem L1597_fin : (prmOK pL1597 1597 && ptTest pL1597 (runFrom pL1597 (fmask pL1597) (cmask pL1597) (hmask pL1597) 1129 468 (true, L1597_cp1.1, L1597_cp1.2)) 1597 799 false) = true := by
  decide +kernel
theorem L1597_ok : RunOK pL1597 1597 (runFrom pL1597 (fmask pL1597) (cmask pL1597) (hmask pL1597) 1129 468 (true, L1597_cp1.1, L1597_cp1.2)) ∧ ptTest pL1597 (runFrom pL1597 (fmask pL1597) (cmask pL1597) (hmask pL1597) 1129 468 (true, L1597_cp1.1, L1597_cp1.2)) 1597 799 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1597_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1597_fin) true) L1597_seg1) (by decide) rfl L1597_fin ptTest_fst
noncomputable def H1597_cp1 : Nat × Nat := t7val% (fastRun pH1597 1 1128 (init pH1597) (init pH1597))
theorem H1597_seg1 : segOK pH1597 1 1128 (init pH1597) (init pH1597) H1597_cp1.1 H1597_cp1.2 = true := by
  decide +kernel
theorem H1597_fin : (prmOK pH1597 1597 && ptTest pH1597 (runFrom pH1597 (fmask pH1597) (cmask pH1597) (hmask pH1597) 1129 468 (true, H1597_cp1.1, H1597_cp1.2)) 1597 799 true) = true := by
  decide +kernel
theorem H1597_ok : RunOK pH1597 1597 (runFrom pH1597 (fmask pH1597) (cmask pH1597) (hmask pH1597) 1129 468 (true, H1597_cp1.1, H1597_cp1.2)) ∧ ptTest pH1597 (runFrom pH1597 (fmask pH1597) (cmask pH1597) (hmask pH1597) 1129 468 (true, H1597_cp1.1, H1597_cp1.2)) 1597 799 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1597_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1597_fin) true) H1597_seg1) (by decide) rfl H1597_fin ptTest_fst
noncomputable def I1597_cp1 : Nat × Nat := t7val% (fastRun pI1597 1 1128 (init pI1597) (init pI1597))
theorem I1597_seg1 : segOK pI1597 1 1128 (init pI1597) (init pI1597) I1597_cp1.1 I1597_cp1.2 = true := by
  decide +kernel
theorem I1597_fin : (prmOK pI1597 1597 && intTest pI1597 (runFrom pI1597 (fmask pI1597) (cmask pI1597) (hmask pI1597) 1129 468 (true, I1597_cp1.1, I1597_cp1.2)) 1597 20 false) = true := by
  decide +kernel
theorem I1597_ok : RunOK pI1597 1597 (runFrom pI1597 (fmask pI1597) (cmask pI1597) (hmask pI1597) 1129 468 (true, I1597_cp1.1, I1597_cp1.2)) ∧ intTest pI1597 (runFrom pI1597 (fmask pI1597) (cmask pI1597) (hmask pI1597) 1129 468 (true, I1597_cp1.1, I1597_cp1.2)) 1597 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1597_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1597_fin) true) I1597_seg1) (by decide) rfl I1597_fin intTest_fst
theorem link1597 : linkOK pL1597 pH1597 pI1597 = true := by decide +kernel
theorem cvx1597 : ConvexBetweenHumps 1597 :=
  cvx_of L1597_ok H1597_ok I1597_ok link1597 (by decide)

/-! ### `N = 1598` -/

def pL1598 : Prm := ⟨82, 40, 39, 1600, 11, 18446744073709551616, 118185669871940248, 118185669871940248⟩
def pH1598 : Prm := ⟨82, 40, 39, 1600, 11, 18446744073709551616, 118186769383568024, 118186769383568024⟩
def pI1598 : Prm := ⟨67, 33, 31, 1600, 11, 18446744073709551616, 118185669871940248, 118186769383568024⟩
noncomputable def L1598_cp1 : Nat × Nat := t7val% (fastRun pL1598 1 1129 (init pL1598) (init pL1598))
theorem L1598_seg1 : segOK pL1598 1 1129 (init pL1598) (init pL1598) L1598_cp1.1 L1598_cp1.2 = true := by
  decide +kernel
theorem L1598_fin : (prmOK pL1598 1598 && ptTest pL1598 (runFrom pL1598 (fmask pL1598) (cmask pL1598) (hmask pL1598) 1130 468 (true, L1598_cp1.1, L1598_cp1.2)) 1598 799 false) = true := by
  decide +kernel
theorem L1598_ok : RunOK pL1598 1598 (runFrom pL1598 (fmask pL1598) (cmask pL1598) (hmask pL1598) 1130 468 (true, L1598_cp1.1, L1598_cp1.2)) ∧ ptTest pL1598 (runFrom pL1598 (fmask pL1598) (cmask pL1598) (hmask pL1598) 1130 468 (true, L1598_cp1.1, L1598_cp1.2)) 1598 799 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1598_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1598_fin) true) L1598_seg1) (by decide) rfl L1598_fin ptTest_fst
noncomputable def H1598_cp1 : Nat × Nat := t7val% (fastRun pH1598 1 1129 (init pH1598) (init pH1598))
theorem H1598_seg1 : segOK pH1598 1 1129 (init pH1598) (init pH1598) H1598_cp1.1 H1598_cp1.2 = true := by
  decide +kernel
theorem H1598_fin : (prmOK pH1598 1598 && ptTest pH1598 (runFrom pH1598 (fmask pH1598) (cmask pH1598) (hmask pH1598) 1130 468 (true, H1598_cp1.1, H1598_cp1.2)) 1598 799 true) = true := by
  decide +kernel
theorem H1598_ok : RunOK pH1598 1598 (runFrom pH1598 (fmask pH1598) (cmask pH1598) (hmask pH1598) 1130 468 (true, H1598_cp1.1, H1598_cp1.2)) ∧ ptTest pH1598 (runFrom pH1598 (fmask pH1598) (cmask pH1598) (hmask pH1598) 1130 468 (true, H1598_cp1.1, H1598_cp1.2)) 1598 799 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1598_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1598_fin) true) H1598_seg1) (by decide) rfl H1598_fin ptTest_fst
noncomputable def I1598_cp1 : Nat × Nat := t7val% (fastRun pI1598 1 1129 (init pI1598) (init pI1598))
theorem I1598_seg1 : segOK pI1598 1 1129 (init pI1598) (init pI1598) I1598_cp1.1 I1598_cp1.2 = true := by
  decide +kernel
theorem I1598_fin : (prmOK pI1598 1598 && intTest pI1598 (runFrom pI1598 (fmask pI1598) (cmask pI1598) (hmask pI1598) 1130 468 (true, I1598_cp1.1, I1598_cp1.2)) 1598 20 true) = true := by
  decide +kernel
theorem I1598_ok : RunOK pI1598 1598 (runFrom pI1598 (fmask pI1598) (cmask pI1598) (hmask pI1598) 1130 468 (true, I1598_cp1.1, I1598_cp1.2)) ∧ intTest pI1598 (runFrom pI1598 (fmask pI1598) (cmask pI1598) (hmask pI1598) 1130 468 (true, I1598_cp1.1, I1598_cp1.2)) 1598 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1598_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1598_fin) true) I1598_seg1) (by decide) rfl I1598_fin intTest_fst
theorem link1598 : linkOK pL1598 pH1598 pI1598 = true := by decide +kernel
theorem cvx1598 : ConvexBetweenHumps 1598 :=
  cvx_of L1598_ok H1598_ok I1598_ok link1598 (by decide)
theorem cenlink1598 : cenLinkOK pI1598 1598 = true := by decide +kernel
theorem cen1598 : CenterUniqueMin 1598 ∧ DipHyp 1598 ∧ OnePointHyps 1598 :=
  cen_of L1598_ok H1598_ok I1598_ok link1598 cenlink1598

/-! ### `N = 1599` -/

def pL1599 : Prm := ⟨82, 40, 39, 1601, 11, 18446744073709551616, 118125350368622822, 118125350368622822⟩
def pH1599 : Prm := ⟨82, 40, 39, 1601, 11, 18446744073709551616, 118126449880250598, 118126449880250598⟩
def pI1599 : Prm := ⟨67, 33, 31, 1601, 11, 18446744073709551616, 118125350368622822, 118126449880250598⟩
noncomputable def L1599_cp1 : Nat × Nat := t7val% (fastRun pL1599 1 1130 (init pL1599) (init pL1599))
theorem L1599_seg1 : segOK pL1599 1 1130 (init pL1599) (init pL1599) L1599_cp1.1 L1599_cp1.2 = true := by
  decide +kernel
theorem L1599_fin : (prmOK pL1599 1599 && ptTest pL1599 (runFrom pL1599 (fmask pL1599) (cmask pL1599) (hmask pL1599) 1131 468 (true, L1599_cp1.1, L1599_cp1.2)) 1599 800 false) = true := by
  decide +kernel
theorem L1599_ok : RunOK pL1599 1599 (runFrom pL1599 (fmask pL1599) (cmask pL1599) (hmask pL1599) 1131 468 (true, L1599_cp1.1, L1599_cp1.2)) ∧ ptTest pL1599 (runFrom pL1599 (fmask pL1599) (cmask pL1599) (hmask pL1599) 1131 468 (true, L1599_cp1.1, L1599_cp1.2)) 1599 800 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1599_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1599_fin) true) L1599_seg1) (by decide) rfl L1599_fin ptTest_fst
noncomputable def H1599_cp1 : Nat × Nat := t7val% (fastRun pH1599 1 1130 (init pH1599) (init pH1599))
theorem H1599_seg1 : segOK pH1599 1 1130 (init pH1599) (init pH1599) H1599_cp1.1 H1599_cp1.2 = true := by
  decide +kernel
theorem H1599_fin : (prmOK pH1599 1599 && ptTest pH1599 (runFrom pH1599 (fmask pH1599) (cmask pH1599) (hmask pH1599) 1131 468 (true, H1599_cp1.1, H1599_cp1.2)) 1599 800 true) = true := by
  decide +kernel
theorem H1599_ok : RunOK pH1599 1599 (runFrom pH1599 (fmask pH1599) (cmask pH1599) (hmask pH1599) 1131 468 (true, H1599_cp1.1, H1599_cp1.2)) ∧ ptTest pH1599 (runFrom pH1599 (fmask pH1599) (cmask pH1599) (hmask pH1599) 1131 468 (true, H1599_cp1.1, H1599_cp1.2)) 1599 800 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1599_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1599_fin) true) H1599_seg1) (by decide) rfl H1599_fin ptTest_fst
noncomputable def I1599_cp1 : Nat × Nat := t7val% (fastRun pI1599 1 1130 (init pI1599) (init pI1599))
theorem I1599_seg1 : segOK pI1599 1 1130 (init pI1599) (init pI1599) I1599_cp1.1 I1599_cp1.2 = true := by
  decide +kernel
theorem I1599_fin : (prmOK pI1599 1599 && intTest pI1599 (runFrom pI1599 (fmask pI1599) (cmask pI1599) (hmask pI1599) 1131 468 (true, I1599_cp1.1, I1599_cp1.2)) 1599 20 false) = true := by
  decide +kernel
theorem I1599_ok : RunOK pI1599 1599 (runFrom pI1599 (fmask pI1599) (cmask pI1599) (hmask pI1599) 1131 468 (true, I1599_cp1.1, I1599_cp1.2)) ∧ intTest pI1599 (runFrom pI1599 (fmask pI1599) (cmask pI1599) (hmask pI1599) 1131 468 (true, I1599_cp1.1, I1599_cp1.2)) 1599 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1599_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1599_fin) true) I1599_seg1) (by decide) rfl I1599_fin intTest_fst
theorem link1599 : linkOK pL1599 pH1599 pI1599 = true := by decide +kernel
theorem cvx1599 : ConvexBetweenHumps 1599 :=
  cvx_of L1599_ok H1599_ok I1599_ok link1599 (by decide)

/-! ### `N = 1600` -/

def pL1600 : Prm := ⟨82, 40, 39, 1602, 11, 18446744073709551616, 118065125338663409, 118065125338663409⟩
def pH1600 : Prm := ⟨82, 40, 39, 1602, 11, 18446744073709551616, 118066224850291185, 118066224850291185⟩
def pI1600 : Prm := ⟨67, 33, 31, 1602, 11, 18446744073709551616, 118065125338663409, 118066224850291185⟩
noncomputable def L1600_cp1 : Nat × Nat := t7val% (fastRun pL1600 1 1130 (init pL1600) (init pL1600))
theorem L1600_seg1 : segOK pL1600 1 1130 (init pL1600) (init pL1600) L1600_cp1.1 L1600_cp1.2 = true := by
  decide +kernel
theorem L1600_fin : (prmOK pL1600 1600 && ptTest pL1600 (runFrom pL1600 (fmask pL1600) (cmask pL1600) (hmask pL1600) 1131 469 (true, L1600_cp1.1, L1600_cp1.2)) 1600 800 false) = true := by
  decide +kernel
theorem L1600_ok : RunOK pL1600 1600 (runFrom pL1600 (fmask pL1600) (cmask pL1600) (hmask pL1600) 1131 469 (true, L1600_cp1.1, L1600_cp1.2)) ∧ ptTest pL1600 (runFrom pL1600 (fmask pL1600) (cmask pL1600) (hmask pL1600) 1131 469 (true, L1600_cp1.1, L1600_cp1.2)) 1600 800 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1600_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1600_fin) true) L1600_seg1) (by decide) rfl L1600_fin ptTest_fst
noncomputable def H1600_cp1 : Nat × Nat := t7val% (fastRun pH1600 1 1130 (init pH1600) (init pH1600))
theorem H1600_seg1 : segOK pH1600 1 1130 (init pH1600) (init pH1600) H1600_cp1.1 H1600_cp1.2 = true := by
  decide +kernel
theorem H1600_fin : (prmOK pH1600 1600 && ptTest pH1600 (runFrom pH1600 (fmask pH1600) (cmask pH1600) (hmask pH1600) 1131 469 (true, H1600_cp1.1, H1600_cp1.2)) 1600 800 true) = true := by
  decide +kernel
theorem H1600_ok : RunOK pH1600 1600 (runFrom pH1600 (fmask pH1600) (cmask pH1600) (hmask pH1600) 1131 469 (true, H1600_cp1.1, H1600_cp1.2)) ∧ ptTest pH1600 (runFrom pH1600 (fmask pH1600) (cmask pH1600) (hmask pH1600) 1131 469 (true, H1600_cp1.1, H1600_cp1.2)) 1600 800 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1600_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1600_fin) true) H1600_seg1) (by decide) rfl H1600_fin ptTest_fst
noncomputable def I1600_cp1 : Nat × Nat := t7val% (fastRun pI1600 1 1130 (init pI1600) (init pI1600))
theorem I1600_seg1 : segOK pI1600 1 1130 (init pI1600) (init pI1600) I1600_cp1.1 I1600_cp1.2 = true := by
  decide +kernel
theorem I1600_fin : (prmOK pI1600 1600 && intTest pI1600 (runFrom pI1600 (fmask pI1600) (cmask pI1600) (hmask pI1600) 1131 469 (true, I1600_cp1.1, I1600_cp1.2)) 1600 21 true) = true := by
  decide +kernel
theorem I1600_ok : RunOK pI1600 1600 (runFrom pI1600 (fmask pI1600) (cmask pI1600) (hmask pI1600) 1131 469 (true, I1600_cp1.1, I1600_cp1.2)) ∧ intTest pI1600 (runFrom pI1600 (fmask pI1600) (cmask pI1600) (hmask pI1600) 1131 469 (true, I1600_cp1.1, I1600_cp1.2)) 1600 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1600_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1600_fin) true) I1600_seg1) (by decide) rfl I1600_fin intTest_fst
theorem link1600 : linkOK pL1600 pH1600 pI1600 = true := by decide +kernel
theorem cvx1600 : ConvexBetweenHumps 1600 :=
  cvx_of L1600_ok H1600_ok I1600_ok link1600 (by decide)
theorem cenlink1600 : cenLinkOK pI1600 1600 = true := by decide +kernel
theorem cen1600 : CenterUniqueMin 1600 ∧ DipHyp 1600 ∧ OnePointHyps 1600 :=
  cen_of L1600_ok H1600_ok I1600_ok link1600 cenlink1600

/-! ### `N = 1601` -/

def pL1601 : Prm := ⟨82, 40, 39, 1603, 11, 18446744073709551616, 118004939512905093, 118004939512905093⟩
def pH1601 : Prm := ⟨82, 40, 39, 1603, 11, 18446744073709551616, 118006039024532869, 118006039024532869⟩
def pI1601 : Prm := ⟨67, 33, 31, 1603, 11, 18446744073709551616, 118004939512905093, 118006039024532869⟩
noncomputable def L1601_cp1 : Nat × Nat := t7val% (fastRun pL1601 1 1131 (init pL1601) (init pL1601))
theorem L1601_seg1 : segOK pL1601 1 1131 (init pL1601) (init pL1601) L1601_cp1.1 L1601_cp1.2 = true := by
  decide +kernel
theorem L1601_fin : (prmOK pL1601 1601 && ptTest pL1601 (runFrom pL1601 (fmask pL1601) (cmask pL1601) (hmask pL1601) 1132 469 (true, L1601_cp1.1, L1601_cp1.2)) 1601 801 false) = true := by
  decide +kernel
theorem L1601_ok : RunOK pL1601 1601 (runFrom pL1601 (fmask pL1601) (cmask pL1601) (hmask pL1601) 1132 469 (true, L1601_cp1.1, L1601_cp1.2)) ∧ ptTest pL1601 (runFrom pL1601 (fmask pL1601) (cmask pL1601) (hmask pL1601) 1132 469 (true, L1601_cp1.1, L1601_cp1.2)) 1601 801 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1601_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1601_fin) true) L1601_seg1) (by decide) rfl L1601_fin ptTest_fst
noncomputable def H1601_cp1 : Nat × Nat := t7val% (fastRun pH1601 1 1131 (init pH1601) (init pH1601))
theorem H1601_seg1 : segOK pH1601 1 1131 (init pH1601) (init pH1601) H1601_cp1.1 H1601_cp1.2 = true := by
  decide +kernel
theorem H1601_fin : (prmOK pH1601 1601 && ptTest pH1601 (runFrom pH1601 (fmask pH1601) (cmask pH1601) (hmask pH1601) 1132 469 (true, H1601_cp1.1, H1601_cp1.2)) 1601 801 true) = true := by
  decide +kernel
theorem H1601_ok : RunOK pH1601 1601 (runFrom pH1601 (fmask pH1601) (cmask pH1601) (hmask pH1601) 1132 469 (true, H1601_cp1.1, H1601_cp1.2)) ∧ ptTest pH1601 (runFrom pH1601 (fmask pH1601) (cmask pH1601) (hmask pH1601) 1132 469 (true, H1601_cp1.1, H1601_cp1.2)) 1601 801 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1601_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1601_fin) true) H1601_seg1) (by decide) rfl H1601_fin ptTest_fst
noncomputable def I1601_cp1 : Nat × Nat := t7val% (fastRun pI1601 1 1131 (init pI1601) (init pI1601))
theorem I1601_seg1 : segOK pI1601 1 1131 (init pI1601) (init pI1601) I1601_cp1.1 I1601_cp1.2 = true := by
  decide +kernel
theorem I1601_fin : (prmOK pI1601 1601 && intTest pI1601 (runFrom pI1601 (fmask pI1601) (cmask pI1601) (hmask pI1601) 1132 469 (true, I1601_cp1.1, I1601_cp1.2)) 1601 21 false) = true := by
  decide +kernel
theorem I1601_ok : RunOK pI1601 1601 (runFrom pI1601 (fmask pI1601) (cmask pI1601) (hmask pI1601) 1132 469 (true, I1601_cp1.1, I1601_cp1.2)) ∧ intTest pI1601 (runFrom pI1601 (fmask pI1601) (cmask pI1601) (hmask pI1601) 1132 469 (true, I1601_cp1.1, I1601_cp1.2)) 1601 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1601_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1601_fin) true) I1601_seg1) (by decide) rfl I1601_fin intTest_fst
theorem link1601 : linkOK pL1601 pH1601 pI1601 = true := by decide +kernel
theorem cvx1601 : ConvexBetweenHumps 1601 :=
  cvx_of L1601_ok H1601_ok I1601_ok link1601 (by decide)

/-! ### `N = 1602` -/

def pL1602 : Prm := ⟨82, 40, 39, 1604, 11, 18446744073709551616, 117944847826489596, 117944847826489596⟩
def pH1602 : Prm := ⟨82, 40, 39, 1604, 11, 18446744073709551616, 117945947338117372, 117945947338117372⟩
def pI1602 : Prm := ⟨67, 33, 31, 1604, 11, 18446744073709551616, 117944847826489596, 117945947338117372⟩
noncomputable def L1602_cp1 : Nat × Nat := t7val% (fastRun pL1602 1 1132 (init pL1602) (init pL1602))
theorem L1602_seg1 : segOK pL1602 1 1132 (init pL1602) (init pL1602) L1602_cp1.1 L1602_cp1.2 = true := by
  decide +kernel
theorem L1602_fin : (prmOK pL1602 1602 && ptTest pL1602 (runFrom pL1602 (fmask pL1602) (cmask pL1602) (hmask pL1602) 1133 469 (true, L1602_cp1.1, L1602_cp1.2)) 1602 801 false) = true := by
  decide +kernel
theorem L1602_ok : RunOK pL1602 1602 (runFrom pL1602 (fmask pL1602) (cmask pL1602) (hmask pL1602) 1133 469 (true, L1602_cp1.1, L1602_cp1.2)) ∧ ptTest pL1602 (runFrom pL1602 (fmask pL1602) (cmask pL1602) (hmask pL1602) 1133 469 (true, L1602_cp1.1, L1602_cp1.2)) 1602 801 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1602_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1602_fin) true) L1602_seg1) (by decide) rfl L1602_fin ptTest_fst
noncomputable def H1602_cp1 : Nat × Nat := t7val% (fastRun pH1602 1 1132 (init pH1602) (init pH1602))
theorem H1602_seg1 : segOK pH1602 1 1132 (init pH1602) (init pH1602) H1602_cp1.1 H1602_cp1.2 = true := by
  decide +kernel
theorem H1602_fin : (prmOK pH1602 1602 && ptTest pH1602 (runFrom pH1602 (fmask pH1602) (cmask pH1602) (hmask pH1602) 1133 469 (true, H1602_cp1.1, H1602_cp1.2)) 1602 801 true) = true := by
  decide +kernel
theorem H1602_ok : RunOK pH1602 1602 (runFrom pH1602 (fmask pH1602) (cmask pH1602) (hmask pH1602) 1133 469 (true, H1602_cp1.1, H1602_cp1.2)) ∧ ptTest pH1602 (runFrom pH1602 (fmask pH1602) (cmask pH1602) (hmask pH1602) 1133 469 (true, H1602_cp1.1, H1602_cp1.2)) 1602 801 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1602_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1602_fin) true) H1602_seg1) (by decide) rfl H1602_fin ptTest_fst
noncomputable def I1602_cp1 : Nat × Nat := t7val% (fastRun pI1602 1 1132 (init pI1602) (init pI1602))
theorem I1602_seg1 : segOK pI1602 1 1132 (init pI1602) (init pI1602) I1602_cp1.1 I1602_cp1.2 = true := by
  decide +kernel
theorem I1602_fin : (prmOK pI1602 1602 && intTest pI1602 (runFrom pI1602 (fmask pI1602) (cmask pI1602) (hmask pI1602) 1133 469 (true, I1602_cp1.1, I1602_cp1.2)) 1602 21 true) = true := by
  decide +kernel
theorem I1602_ok : RunOK pI1602 1602 (runFrom pI1602 (fmask pI1602) (cmask pI1602) (hmask pI1602) 1133 469 (true, I1602_cp1.1, I1602_cp1.2)) ∧ intTest pI1602 (runFrom pI1602 (fmask pI1602) (cmask pI1602) (hmask pI1602) 1133 469 (true, I1602_cp1.1, I1602_cp1.2)) 1602 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1602_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1602_fin) true) I1602_seg1) (by decide) rfl I1602_fin intTest_fst
theorem link1602 : linkOK pL1602 pH1602 pI1602 = true := by decide +kernel
theorem cvx1602 : ConvexBetweenHumps 1602 :=
  cvx_of L1602_ok H1602_ok I1602_ok link1602 (by decide)
theorem cenlink1602 : cenLinkOK pI1602 1602 = true := by decide +kernel
theorem cen1602 : CenterUniqueMin 1602 ∧ DipHyp 1602 ∧ OnePointHyps 1602 :=
  cen_of L1602_ok H1602_ok I1602_ok link1602 cenlink1602

/-! ### `N = 1603` -/

def pL1603 : Prm := ⟨82, 40, 39, 1605, 11, 18446744073709551616, 117884795220442203, 117884795220442203⟩
def pH1603 : Prm := ⟨82, 40, 39, 1605, 11, 18446744073709551616, 117885894732069979, 117885894732069979⟩
def pI1603 : Prm := ⟨67, 33, 31, 1605, 11, 18446744073709551616, 117884795220442203, 117885894732069979⟩
noncomputable def L1603_cp1 : Nat × Nat := t7val% (fastRun pL1603 1 1132 (init pL1603) (init pL1603))
theorem L1603_seg1 : segOK pL1603 1 1132 (init pL1603) (init pL1603) L1603_cp1.1 L1603_cp1.2 = true := by
  decide +kernel
theorem L1603_fin : (prmOK pL1603 1603 && ptTest pL1603 (runFrom pL1603 (fmask pL1603) (cmask pL1603) (hmask pL1603) 1133 470 (true, L1603_cp1.1, L1603_cp1.2)) 1603 802 false) = true := by
  decide +kernel
theorem L1603_ok : RunOK pL1603 1603 (runFrom pL1603 (fmask pL1603) (cmask pL1603) (hmask pL1603) 1133 470 (true, L1603_cp1.1, L1603_cp1.2)) ∧ ptTest pL1603 (runFrom pL1603 (fmask pL1603) (cmask pL1603) (hmask pL1603) 1133 470 (true, L1603_cp1.1, L1603_cp1.2)) 1603 802 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1603_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1603_fin) true) L1603_seg1) (by decide) rfl L1603_fin ptTest_fst
noncomputable def H1603_cp1 : Nat × Nat := t7val% (fastRun pH1603 1 1132 (init pH1603) (init pH1603))
theorem H1603_seg1 : segOK pH1603 1 1132 (init pH1603) (init pH1603) H1603_cp1.1 H1603_cp1.2 = true := by
  decide +kernel
theorem H1603_fin : (prmOK pH1603 1603 && ptTest pH1603 (runFrom pH1603 (fmask pH1603) (cmask pH1603) (hmask pH1603) 1133 470 (true, H1603_cp1.1, H1603_cp1.2)) 1603 802 true) = true := by
  decide +kernel
theorem H1603_ok : RunOK pH1603 1603 (runFrom pH1603 (fmask pH1603) (cmask pH1603) (hmask pH1603) 1133 470 (true, H1603_cp1.1, H1603_cp1.2)) ∧ ptTest pH1603 (runFrom pH1603 (fmask pH1603) (cmask pH1603) (hmask pH1603) 1133 470 (true, H1603_cp1.1, H1603_cp1.2)) 1603 802 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1603_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1603_fin) true) H1603_seg1) (by decide) rfl H1603_fin ptTest_fst
noncomputable def I1603_cp1 : Nat × Nat := t7val% (fastRun pI1603 1 1132 (init pI1603) (init pI1603))
theorem I1603_seg1 : segOK pI1603 1 1132 (init pI1603) (init pI1603) I1603_cp1.1 I1603_cp1.2 = true := by
  decide +kernel
theorem I1603_fin : (prmOK pI1603 1603 && intTest pI1603 (runFrom pI1603 (fmask pI1603) (cmask pI1603) (hmask pI1603) 1133 470 (true, I1603_cp1.1, I1603_cp1.2)) 1603 21 false) = true := by
  decide +kernel
theorem I1603_ok : RunOK pI1603 1603 (runFrom pI1603 (fmask pI1603) (cmask pI1603) (hmask pI1603) 1133 470 (true, I1603_cp1.1, I1603_cp1.2)) ∧ intTest pI1603 (runFrom pI1603 (fmask pI1603) (cmask pI1603) (hmask pI1603) 1133 470 (true, I1603_cp1.1, I1603_cp1.2)) 1603 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1603_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1603_fin) true) I1603_seg1) (by decide) rfl I1603_fin intTest_fst
theorem link1603 : linkOK pL1603 pH1603 pI1603 = true := by decide +kernel
theorem cvx1603 : ConvexBetweenHumps 1603 :=
  cvx_of L1603_ok H1603_ok I1603_ok link1603 (by decide)

/-! ### `N = 1604` -/

def pL1604 : Prm := ⟨82, 40, 39, 1606, 11, 18446744073709551616, 117824836421271959, 117824836421271959⟩
def pH1604 : Prm := ⟨82, 40, 39, 1606, 11, 18446744073709551616, 117825935932899735, 117825935932899735⟩
def pI1604 : Prm := ⟨67, 33, 31, 1606, 11, 18446744073709551616, 117824836421271959, 117825935932899735⟩
noncomputable def L1604_cp1 : Nat × Nat := t7val% (fastRun pL1604 1 1133 (init pL1604) (init pL1604))
theorem L1604_seg1 : segOK pL1604 1 1133 (init pL1604) (init pL1604) L1604_cp1.1 L1604_cp1.2 = true := by
  decide +kernel
theorem L1604_fin : (prmOK pL1604 1604 && ptTest pL1604 (runFrom pL1604 (fmask pL1604) (cmask pL1604) (hmask pL1604) 1134 470 (true, L1604_cp1.1, L1604_cp1.2)) 1604 802 false) = true := by
  decide +kernel
theorem L1604_ok : RunOK pL1604 1604 (runFrom pL1604 (fmask pL1604) (cmask pL1604) (hmask pL1604) 1134 470 (true, L1604_cp1.1, L1604_cp1.2)) ∧ ptTest pL1604 (runFrom pL1604 (fmask pL1604) (cmask pL1604) (hmask pL1604) 1134 470 (true, L1604_cp1.1, L1604_cp1.2)) 1604 802 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1604_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1604_fin) true) L1604_seg1) (by decide) rfl L1604_fin ptTest_fst
noncomputable def H1604_cp1 : Nat × Nat := t7val% (fastRun pH1604 1 1133 (init pH1604) (init pH1604))
theorem H1604_seg1 : segOK pH1604 1 1133 (init pH1604) (init pH1604) H1604_cp1.1 H1604_cp1.2 = true := by
  decide +kernel
theorem H1604_fin : (prmOK pH1604 1604 && ptTest pH1604 (runFrom pH1604 (fmask pH1604) (cmask pH1604) (hmask pH1604) 1134 470 (true, H1604_cp1.1, H1604_cp1.2)) 1604 802 true) = true := by
  decide +kernel
theorem H1604_ok : RunOK pH1604 1604 (runFrom pH1604 (fmask pH1604) (cmask pH1604) (hmask pH1604) 1134 470 (true, H1604_cp1.1, H1604_cp1.2)) ∧ ptTest pH1604 (runFrom pH1604 (fmask pH1604) (cmask pH1604) (hmask pH1604) 1134 470 (true, H1604_cp1.1, H1604_cp1.2)) 1604 802 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1604_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1604_fin) true) H1604_seg1) (by decide) rfl H1604_fin ptTest_fst
noncomputable def I1604_cp1 : Nat × Nat := t7val% (fastRun pI1604 1 1133 (init pI1604) (init pI1604))
theorem I1604_seg1 : segOK pI1604 1 1133 (init pI1604) (init pI1604) I1604_cp1.1 I1604_cp1.2 = true := by
  decide +kernel
theorem I1604_fin : (prmOK pI1604 1604 && intTest pI1604 (runFrom pI1604 (fmask pI1604) (cmask pI1604) (hmask pI1604) 1134 470 (true, I1604_cp1.1, I1604_cp1.2)) 1604 21 true) = true := by
  decide +kernel
theorem I1604_ok : RunOK pI1604 1604 (runFrom pI1604 (fmask pI1604) (cmask pI1604) (hmask pI1604) 1134 470 (true, I1604_cp1.1, I1604_cp1.2)) ∧ intTest pI1604 (runFrom pI1604 (fmask pI1604) (cmask pI1604) (hmask pI1604) 1134 470 (true, I1604_cp1.1, I1604_cp1.2)) 1604 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1604_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1604_fin) true) I1604_seg1) (by decide) rfl I1604_fin intTest_fst
theorem link1604 : linkOK pL1604 pH1604 pI1604 = true := by decide +kernel
theorem cvx1604 : ConvexBetweenHumps 1604 :=
  cvx_of L1604_ok H1604_ok I1604_ok link1604 (by decide)
theorem cenlink1604 : cenLinkOK pI1604 1604 = true := by decide +kernel
theorem cen1604 : CenterUniqueMin 1604 ∧ DipHyp 1604 ∧ OnePointHyps 1604 :=
  cen_of L1604_ok H1604_ok I1604_ok link1604 cenlink1604

/-! ### `N = 1605` -/

def pL1605 : Prm := ⟨82, 40, 39, 1607, 11, 18446744073709551616, 117764916579134889, 117764916579134889⟩
def pH1605 : Prm := ⟨82, 40, 39, 1607, 11, 18446744073709551616, 117766016090762665, 117766016090762665⟩
def pI1605 : Prm := ⟨67, 33, 31, 1607, 11, 18446744073709551616, 117764916579134889, 117766016090762665⟩
noncomputable def L1605_cp1 : Nat × Nat := t7val% (fastRun pL1605 1 1134 (init pL1605) (init pL1605))
theorem L1605_seg1 : segOK pL1605 1 1134 (init pL1605) (init pL1605) L1605_cp1.1 L1605_cp1.2 = true := by
  decide +kernel
theorem L1605_fin : (prmOK pL1605 1605 && ptTest pL1605 (runFrom pL1605 (fmask pL1605) (cmask pL1605) (hmask pL1605) 1135 470 (true, L1605_cp1.1, L1605_cp1.2)) 1605 803 false) = true := by
  decide +kernel
theorem L1605_ok : RunOK pL1605 1605 (runFrom pL1605 (fmask pL1605) (cmask pL1605) (hmask pL1605) 1135 470 (true, L1605_cp1.1, L1605_cp1.2)) ∧ ptTest pL1605 (runFrom pL1605 (fmask pL1605) (cmask pL1605) (hmask pL1605) 1135 470 (true, L1605_cp1.1, L1605_cp1.2)) 1605 803 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1605_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1605_fin) true) L1605_seg1) (by decide) rfl L1605_fin ptTest_fst
noncomputable def H1605_cp1 : Nat × Nat := t7val% (fastRun pH1605 1 1134 (init pH1605) (init pH1605))
theorem H1605_seg1 : segOK pH1605 1 1134 (init pH1605) (init pH1605) H1605_cp1.1 H1605_cp1.2 = true := by
  decide +kernel
theorem H1605_fin : (prmOK pH1605 1605 && ptTest pH1605 (runFrom pH1605 (fmask pH1605) (cmask pH1605) (hmask pH1605) 1135 470 (true, H1605_cp1.1, H1605_cp1.2)) 1605 803 true) = true := by
  decide +kernel
theorem H1605_ok : RunOK pH1605 1605 (runFrom pH1605 (fmask pH1605) (cmask pH1605) (hmask pH1605) 1135 470 (true, H1605_cp1.1, H1605_cp1.2)) ∧ ptTest pH1605 (runFrom pH1605 (fmask pH1605) (cmask pH1605) (hmask pH1605) 1135 470 (true, H1605_cp1.1, H1605_cp1.2)) 1605 803 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1605_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1605_fin) true) H1605_seg1) (by decide) rfl H1605_fin ptTest_fst
noncomputable def I1605_cp1 : Nat × Nat := t7val% (fastRun pI1605 1 1134 (init pI1605) (init pI1605))
theorem I1605_seg1 : segOK pI1605 1 1134 (init pI1605) (init pI1605) I1605_cp1.1 I1605_cp1.2 = true := by
  decide +kernel
theorem I1605_fin : (prmOK pI1605 1605 && intTest pI1605 (runFrom pI1605 (fmask pI1605) (cmask pI1605) (hmask pI1605) 1135 470 (true, I1605_cp1.1, I1605_cp1.2)) 1605 21 false) = true := by
  decide +kernel
theorem I1605_ok : RunOK pI1605 1605 (runFrom pI1605 (fmask pI1605) (cmask pI1605) (hmask pI1605) 1135 470 (true, I1605_cp1.1, I1605_cp1.2)) ∧ intTest pI1605 (runFrom pI1605 (fmask pI1605) (cmask pI1605) (hmask pI1605) 1135 470 (true, I1605_cp1.1, I1605_cp1.2)) 1605 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1605_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1605_fin) true) I1605_seg1) (by decide) rfl I1605_fin intTest_fst
theorem link1605 : linkOK pL1605 pH1605 pI1605 = true := by decide +kernel
theorem cvx1605 : ConvexBetweenHumps 1605 :=
  cvx_of L1605_ok H1605_ok I1605_ok link1605 (by decide)

/-! ### `N = 1606` -/

def pL1606 : Prm := ⟨82, 40, 39, 1608, 11, 18446744073709551616, 117705090213032614, 117705090213032614⟩
def pH1606 : Prm := ⟨82, 40, 39, 1608, 11, 18446744073709551616, 117706189724660390, 117706189724660390⟩
def pI1606 : Prm := ⟨67, 33, 31, 1608, 11, 18446744073709551616, 117705090213032614, 117706189724660390⟩
noncomputable def L1606_cp1 : Nat × Nat := t7val% (fastRun pL1606 1 1135 (init pL1606) (init pL1606))
theorem L1606_seg1 : segOK pL1606 1 1135 (init pL1606) (init pL1606) L1606_cp1.1 L1606_cp1.2 = true := by
  decide +kernel
theorem L1606_fin : (prmOK pL1606 1606 && ptTest pL1606 (runFrom pL1606 (fmask pL1606) (cmask pL1606) (hmask pL1606) 1136 470 (true, L1606_cp1.1, L1606_cp1.2)) 1606 803 false) = true := by
  decide +kernel
theorem L1606_ok : RunOK pL1606 1606 (runFrom pL1606 (fmask pL1606) (cmask pL1606) (hmask pL1606) 1136 470 (true, L1606_cp1.1, L1606_cp1.2)) ∧ ptTest pL1606 (runFrom pL1606 (fmask pL1606) (cmask pL1606) (hmask pL1606) 1136 470 (true, L1606_cp1.1, L1606_cp1.2)) 1606 803 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1606_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1606_fin) true) L1606_seg1) (by decide) rfl L1606_fin ptTest_fst
noncomputable def H1606_cp1 : Nat × Nat := t7val% (fastRun pH1606 1 1135 (init pH1606) (init pH1606))
theorem H1606_seg1 : segOK pH1606 1 1135 (init pH1606) (init pH1606) H1606_cp1.1 H1606_cp1.2 = true := by
  decide +kernel
theorem H1606_fin : (prmOK pH1606 1606 && ptTest pH1606 (runFrom pH1606 (fmask pH1606) (cmask pH1606) (hmask pH1606) 1136 470 (true, H1606_cp1.1, H1606_cp1.2)) 1606 803 true) = true := by
  decide +kernel
theorem H1606_ok : RunOK pH1606 1606 (runFrom pH1606 (fmask pH1606) (cmask pH1606) (hmask pH1606) 1136 470 (true, H1606_cp1.1, H1606_cp1.2)) ∧ ptTest pH1606 (runFrom pH1606 (fmask pH1606) (cmask pH1606) (hmask pH1606) 1136 470 (true, H1606_cp1.1, H1606_cp1.2)) 1606 803 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1606_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1606_fin) true) H1606_seg1) (by decide) rfl H1606_fin ptTest_fst
noncomputable def I1606_cp1 : Nat × Nat := t7val% (fastRun pI1606 1 1135 (init pI1606) (init pI1606))
theorem I1606_seg1 : segOK pI1606 1 1135 (init pI1606) (init pI1606) I1606_cp1.1 I1606_cp1.2 = true := by
  decide +kernel
theorem I1606_fin : (prmOK pI1606 1606 && intTest pI1606 (runFrom pI1606 (fmask pI1606) (cmask pI1606) (hmask pI1606) 1136 470 (true, I1606_cp1.1, I1606_cp1.2)) 1606 21 true) = true := by
  decide +kernel
theorem I1606_ok : RunOK pI1606 1606 (runFrom pI1606 (fmask pI1606) (cmask pI1606) (hmask pI1606) 1136 470 (true, I1606_cp1.1, I1606_cp1.2)) ∧ intTest pI1606 (runFrom pI1606 (fmask pI1606) (cmask pI1606) (hmask pI1606) 1136 470 (true, I1606_cp1.1, I1606_cp1.2)) 1606 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1606_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1606_fin) true) I1606_seg1) (by decide) rfl I1606_fin intTest_fst
theorem link1606 : linkOK pL1606 pH1606 pI1606 = true := by decide +kernel
theorem cvx1606 : ConvexBetweenHumps 1606 :=
  cvx_of L1606_ok H1606_ok I1606_ok link1606 (by decide)
theorem cenlink1606 : cenLinkOK pI1606 1606 = true := by decide +kernel
theorem cen1606 : CenterUniqueMin 1606 ∧ DipHyp 1606 ∧ OnePointHyps 1606 :=
  cen_of L1606_ok H1606_ok I1606_ok link1606 cenlink1606

/-! ### `N = 1607` -/

def pL1607 : Prm := ⟨82, 40, 39, 1609, 11, 18446744073709551616, 117645302681163537, 117645302681163537⟩
def pH1607 : Prm := ⟨82, 40, 39, 1609, 11, 18446744073709551616, 117646402192791313, 117646402192791313⟩
def pI1607 : Prm := ⟨67, 33, 31, 1609, 11, 18446744073709551616, 117645302681163537, 117646402192791313⟩
noncomputable def L1607_cp1 : Nat × Nat := t7val% (fastRun pL1607 1 1135 (init pL1607) (init pL1607))
theorem L1607_seg1 : segOK pL1607 1 1135 (init pL1607) (init pL1607) L1607_cp1.1 L1607_cp1.2 = true := by
  decide +kernel
theorem L1607_fin : (prmOK pL1607 1607 && ptTest pL1607 (runFrom pL1607 (fmask pL1607) (cmask pL1607) (hmask pL1607) 1136 471 (true, L1607_cp1.1, L1607_cp1.2)) 1607 804 false) = true := by
  decide +kernel
theorem L1607_ok : RunOK pL1607 1607 (runFrom pL1607 (fmask pL1607) (cmask pL1607) (hmask pL1607) 1136 471 (true, L1607_cp1.1, L1607_cp1.2)) ∧ ptTest pL1607 (runFrom pL1607 (fmask pL1607) (cmask pL1607) (hmask pL1607) 1136 471 (true, L1607_cp1.1, L1607_cp1.2)) 1607 804 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1607_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1607_fin) true) L1607_seg1) (by decide) rfl L1607_fin ptTest_fst
noncomputable def H1607_cp1 : Nat × Nat := t7val% (fastRun pH1607 1 1135 (init pH1607) (init pH1607))
theorem H1607_seg1 : segOK pH1607 1 1135 (init pH1607) (init pH1607) H1607_cp1.1 H1607_cp1.2 = true := by
  decide +kernel
theorem H1607_fin : (prmOK pH1607 1607 && ptTest pH1607 (runFrom pH1607 (fmask pH1607) (cmask pH1607) (hmask pH1607) 1136 471 (true, H1607_cp1.1, H1607_cp1.2)) 1607 804 true) = true := by
  decide +kernel
theorem H1607_ok : RunOK pH1607 1607 (runFrom pH1607 (fmask pH1607) (cmask pH1607) (hmask pH1607) 1136 471 (true, H1607_cp1.1, H1607_cp1.2)) ∧ ptTest pH1607 (runFrom pH1607 (fmask pH1607) (cmask pH1607) (hmask pH1607) 1136 471 (true, H1607_cp1.1, H1607_cp1.2)) 1607 804 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1607_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1607_fin) true) H1607_seg1) (by decide) rfl H1607_fin ptTest_fst
noncomputable def I1607_cp1 : Nat × Nat := t7val% (fastRun pI1607 1 1135 (init pI1607) (init pI1607))
theorem I1607_seg1 : segOK pI1607 1 1135 (init pI1607) (init pI1607) I1607_cp1.1 I1607_cp1.2 = true := by
  decide +kernel
theorem I1607_fin : (prmOK pI1607 1607 && intTest pI1607 (runFrom pI1607 (fmask pI1607) (cmask pI1607) (hmask pI1607) 1136 471 (true, I1607_cp1.1, I1607_cp1.2)) 1607 21 false) = true := by
  decide +kernel
theorem I1607_ok : RunOK pI1607 1607 (runFrom pI1607 (fmask pI1607) (cmask pI1607) (hmask pI1607) 1136 471 (true, I1607_cp1.1, I1607_cp1.2)) ∧ intTest pI1607 (runFrom pI1607 (fmask pI1607) (cmask pI1607) (hmask pI1607) 1136 471 (true, I1607_cp1.1, I1607_cp1.2)) 1607 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1607_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1607_fin) true) I1607_seg1) (by decide) rfl I1607_fin intTest_fst
theorem link1607 : linkOK pL1607 pH1607 pI1607 = true := by decide +kernel
theorem cvx1607 : ConvexBetweenHumps 1607 :=
  cvx_of L1607_ok H1607_ok I1607_ok link1607 (by decide)

/-! ### `N = 1608` -/

def pL1608 : Prm := ⟨82, 40, 39, 1610, 11, 18446744073709551616, 117585608296036426, 117585608296036426⟩
def pH1608 : Prm := ⟨82, 40, 39, 1610, 11, 18446744073709551616, 117586707807664202, 117586707807664202⟩
def pI1608 : Prm := ⟨67, 33, 31, 1610, 11, 18446744073709551616, 117585608296036426, 117586707807664202⟩
noncomputable def L1608_cp1 : Nat × Nat := t7val% (fastRun pL1608 1 1136 (init pL1608) (init pL1608))
theorem L1608_seg1 : segOK pL1608 1 1136 (init pL1608) (init pL1608) L1608_cp1.1 L1608_cp1.2 = true := by
  decide +kernel
theorem L1608_fin : (prmOK pL1608 1608 && ptTest pL1608 (runFrom pL1608 (fmask pL1608) (cmask pL1608) (hmask pL1608) 1137 471 (true, L1608_cp1.1, L1608_cp1.2)) 1608 804 false) = true := by
  decide +kernel
theorem L1608_ok : RunOK pL1608 1608 (runFrom pL1608 (fmask pL1608) (cmask pL1608) (hmask pL1608) 1137 471 (true, L1608_cp1.1, L1608_cp1.2)) ∧ ptTest pL1608 (runFrom pL1608 (fmask pL1608) (cmask pL1608) (hmask pL1608) 1137 471 (true, L1608_cp1.1, L1608_cp1.2)) 1608 804 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1608_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1608_fin) true) L1608_seg1) (by decide) rfl L1608_fin ptTest_fst
noncomputable def H1608_cp1 : Nat × Nat := t7val% (fastRun pH1608 1 1136 (init pH1608) (init pH1608))
theorem H1608_seg1 : segOK pH1608 1 1136 (init pH1608) (init pH1608) H1608_cp1.1 H1608_cp1.2 = true := by
  decide +kernel
theorem H1608_fin : (prmOK pH1608 1608 && ptTest pH1608 (runFrom pH1608 (fmask pH1608) (cmask pH1608) (hmask pH1608) 1137 471 (true, H1608_cp1.1, H1608_cp1.2)) 1608 804 true) = true := by
  decide +kernel
theorem H1608_ok : RunOK pH1608 1608 (runFrom pH1608 (fmask pH1608) (cmask pH1608) (hmask pH1608) 1137 471 (true, H1608_cp1.1, H1608_cp1.2)) ∧ ptTest pH1608 (runFrom pH1608 (fmask pH1608) (cmask pH1608) (hmask pH1608) 1137 471 (true, H1608_cp1.1, H1608_cp1.2)) 1608 804 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1608_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1608_fin) true) H1608_seg1) (by decide) rfl H1608_fin ptTest_fst
noncomputable def I1608_cp1 : Nat × Nat := t7val% (fastRun pI1608 1 1136 (init pI1608) (init pI1608))
theorem I1608_seg1 : segOK pI1608 1 1136 (init pI1608) (init pI1608) I1608_cp1.1 I1608_cp1.2 = true := by
  decide +kernel
theorem I1608_fin : (prmOK pI1608 1608 && intTest pI1608 (runFrom pI1608 (fmask pI1608) (cmask pI1608) (hmask pI1608) 1137 471 (true, I1608_cp1.1, I1608_cp1.2)) 1608 21 true) = true := by
  decide +kernel
theorem I1608_ok : RunOK pI1608 1608 (runFrom pI1608 (fmask pI1608) (cmask pI1608) (hmask pI1608) 1137 471 (true, I1608_cp1.1, I1608_cp1.2)) ∧ intTest pI1608 (runFrom pI1608 (fmask pI1608) (cmask pI1608) (hmask pI1608) 1137 471 (true, I1608_cp1.1, I1608_cp1.2)) 1608 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1608_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1608_fin) true) I1608_seg1) (by decide) rfl I1608_fin intTest_fst
theorem link1608 : linkOK pL1608 pH1608 pI1608 = true := by decide +kernel
theorem cvx1608 : ConvexBetweenHumps 1608 :=
  cvx_of L1608_ok H1608_ok I1608_ok link1608 (by decide)
theorem cenlink1608 : cenLinkOK pI1608 1608 = true := by decide +kernel
theorem cen1608 : CenterUniqueMin 1608 ∧ DipHyp 1608 ∧ OnePointHyps 1608 :=
  cen_of L1608_ok H1608_ok I1608_ok link1608 cenlink1608

/-! ### The range -/

theorem cvx_1594_1608 {N : ℕ} (h1 : 1594 ≤ N) (h2 : N ≤ 1608) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1600
  · by_cases h4 : N ≤ 1596
    · by_cases h6 : N ≤ 1594
      · obtain rfl : N = 1594 := by omega
        exact cvx1594
      · by_cases h8 : N ≤ 1595
        · obtain rfl : N = 1595 := by omega
          exact cvx1595
        · obtain rfl : N = 1596 := by omega
          exact cvx1596
    · by_cases h6 : N ≤ 1598
      · by_cases h8 : N ≤ 1597
        · obtain rfl : N = 1597 := by omega
          exact cvx1597
        · obtain rfl : N = 1598 := by omega
          exact cvx1598
      · by_cases h8 : N ≤ 1599
        · obtain rfl : N = 1599 := by omega
          exact cvx1599
        · obtain rfl : N = 1600 := by omega
          exact cvx1600
  · by_cases h4 : N ≤ 1604
    · by_cases h6 : N ≤ 1602
      · by_cases h8 : N ≤ 1601
        · obtain rfl : N = 1601 := by omega
          exact cvx1601
        · obtain rfl : N = 1602 := by omega
          exact cvx1602
      · by_cases h8 : N ≤ 1603
        · obtain rfl : N = 1603 := by omega
          exact cvx1603
        · obtain rfl : N = 1604 := by omega
          exact cvx1604
    · by_cases h6 : N ≤ 1606
      · by_cases h8 : N ≤ 1605
        · obtain rfl : N = 1605 := by omega
          exact cvx1605
        · obtain rfl : N = 1606 := by omega
          exact cvx1606
      · by_cases h8 : N ≤ 1607
        · obtain rfl : N = 1607 := by omega
          exact cvx1607
        · obtain rfl : N = 1608 := by omega
          exact cvx1608

theorem cen_1594_1608 {N : ℕ} (h1 : 1594 ≤ N) (h2 : N ≤ 1608) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1600
  · by_cases h4 : N ≤ 1596
    · by_cases h6 : N ≤ 1594
      · obtain rfl : N = 1594 := by omega
        exact cen1594
      · obtain rfl : N = 1596 := by omega
        exact cen1596
    · by_cases h6 : N ≤ 1598
      · obtain rfl : N = 1598 := by omega
        exact cen1598
      · obtain rfl : N = 1600 := by omega
        exact cen1600
  · by_cases h4 : N ≤ 1604
    · by_cases h6 : N ≤ 1602
      · obtain rfl : N = 1602 := by omega
        exact cen1602
      · obtain rfl : N = 1604 := by omega
        exact cen1604
    · by_cases h6 : N ≤ 1606
      · obtain rfl : N = 1606 := by omega
        exact cen1606
      · obtain rfl : N = 1608 := by omega
        exact cen1608

end Kagey131.PaperD.T7
