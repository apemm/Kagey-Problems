import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1563, …, 1578` (generated)

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

/-! ### `N = 1563` -/

def pL1563 : Prm := ⟨81, 39, 39, 1565, 11, 18446744073709551616, 120339393795373191, 120339393795373191⟩
def pH1563 : Prm := ⟨81, 39, 39, 1565, 11, 18446744073709551616, 120340493307000967, 120340493307000967⟩
def pI1563 : Prm := ⟨67, 33, 31, 1565, 11, 18446744073709551616, 120339393795373191, 120340493307000967⟩
noncomputable def L1563_cp1 : Nat × Nat := t7val% (fastRun pL1563 1 1104 (init pL1563) (init pL1563))
theorem L1563_seg1 : segOK pL1563 1 1104 (init pL1563) (init pL1563) L1563_cp1.1 L1563_cp1.2 = true := by
  decide +kernel
theorem L1563_fin : (prmOK pL1563 1563 && ptTest pL1563 (runFrom pL1563 (fmask pL1563) (cmask pL1563) (hmask pL1563) 1105 458 (true, L1563_cp1.1, L1563_cp1.2)) 1563 782 false) = true := by
  decide +kernel
theorem L1563_ok : RunOK pL1563 1563 (runFrom pL1563 (fmask pL1563) (cmask pL1563) (hmask pL1563) 1105 458 (true, L1563_cp1.1, L1563_cp1.2)) ∧ ptTest pL1563 (runFrom pL1563 (fmask pL1563) (cmask pL1563) (hmask pL1563) 1105 458 (true, L1563_cp1.1, L1563_cp1.2)) 1563 782 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1563_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1563_fin) true) L1563_seg1) (by decide) rfl L1563_fin ptTest_fst
noncomputable def H1563_cp1 : Nat × Nat := t7val% (fastRun pH1563 1 1104 (init pH1563) (init pH1563))
theorem H1563_seg1 : segOK pH1563 1 1104 (init pH1563) (init pH1563) H1563_cp1.1 H1563_cp1.2 = true := by
  decide +kernel
theorem H1563_fin : (prmOK pH1563 1563 && ptTest pH1563 (runFrom pH1563 (fmask pH1563) (cmask pH1563) (hmask pH1563) 1105 458 (true, H1563_cp1.1, H1563_cp1.2)) 1563 782 true) = true := by
  decide +kernel
theorem H1563_ok : RunOK pH1563 1563 (runFrom pH1563 (fmask pH1563) (cmask pH1563) (hmask pH1563) 1105 458 (true, H1563_cp1.1, H1563_cp1.2)) ∧ ptTest pH1563 (runFrom pH1563 (fmask pH1563) (cmask pH1563) (hmask pH1563) 1105 458 (true, H1563_cp1.1, H1563_cp1.2)) 1563 782 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1563_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1563_fin) true) H1563_seg1) (by decide) rfl H1563_fin ptTest_fst
noncomputable def I1563_cp1 : Nat × Nat := t7val% (fastRun pI1563 1 1104 (init pI1563) (init pI1563))
theorem I1563_seg1 : segOK pI1563 1 1104 (init pI1563) (init pI1563) I1563_cp1.1 I1563_cp1.2 = true := by
  decide +kernel
theorem I1563_fin : (prmOK pI1563 1563 && intTest pI1563 (runFrom pI1563 (fmask pI1563) (cmask pI1563) (hmask pI1563) 1105 458 (true, I1563_cp1.1, I1563_cp1.2)) 1563 20 false) = true := by
  decide +kernel
theorem I1563_ok : RunOK pI1563 1563 (runFrom pI1563 (fmask pI1563) (cmask pI1563) (hmask pI1563) 1105 458 (true, I1563_cp1.1, I1563_cp1.2)) ∧ intTest pI1563 (runFrom pI1563 (fmask pI1563) (cmask pI1563) (hmask pI1563) 1105 458 (true, I1563_cp1.1, I1563_cp1.2)) 1563 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1563_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1563_fin) true) I1563_seg1) (by decide) rfl I1563_fin intTest_fst
theorem link1563 : linkOK pL1563 pH1563 pI1563 = true := by decide +kernel
theorem cvx1563 : ConvexBetweenHumps 1563 :=
  cvx_of L1563_ok H1563_ok I1563_ok link1563 (by decide)

/-! ### `N = 1564` -/

def pL1564 : Prm := ⟨81, 39, 39, 1566, 11, 18446744073709551616, 120276688068097119, 120276688068097119⟩
def pH1564 : Prm := ⟨81, 39, 39, 1566, 11, 18446744073709551616, 120277787579724895, 120277787579724895⟩
def pI1564 : Prm := ⟨67, 33, 31, 1566, 11, 18446744073709551616, 120276688068097119, 120277787579724895⟩
noncomputable def L1564_cp1 : Nat × Nat := t7val% (fastRun pL1564 1 1105 (init pL1564) (init pL1564))
theorem L1564_seg1 : segOK pL1564 1 1105 (init pL1564) (init pL1564) L1564_cp1.1 L1564_cp1.2 = true := by
  decide +kernel
theorem L1564_fin : (prmOK pL1564 1564 && ptTest pL1564 (runFrom pL1564 (fmask pL1564) (cmask pL1564) (hmask pL1564) 1106 458 (true, L1564_cp1.1, L1564_cp1.2)) 1564 782 false) = true := by
  decide +kernel
theorem L1564_ok : RunOK pL1564 1564 (runFrom pL1564 (fmask pL1564) (cmask pL1564) (hmask pL1564) 1106 458 (true, L1564_cp1.1, L1564_cp1.2)) ∧ ptTest pL1564 (runFrom pL1564 (fmask pL1564) (cmask pL1564) (hmask pL1564) 1106 458 (true, L1564_cp1.1, L1564_cp1.2)) 1564 782 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1564_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1564_fin) true) L1564_seg1) (by decide) rfl L1564_fin ptTest_fst
noncomputable def H1564_cp1 : Nat × Nat := t7val% (fastRun pH1564 1 1105 (init pH1564) (init pH1564))
theorem H1564_seg1 : segOK pH1564 1 1105 (init pH1564) (init pH1564) H1564_cp1.1 H1564_cp1.2 = true := by
  decide +kernel
theorem H1564_fin : (prmOK pH1564 1564 && ptTest pH1564 (runFrom pH1564 (fmask pH1564) (cmask pH1564) (hmask pH1564) 1106 458 (true, H1564_cp1.1, H1564_cp1.2)) 1564 782 true) = true := by
  decide +kernel
theorem H1564_ok : RunOK pH1564 1564 (runFrom pH1564 (fmask pH1564) (cmask pH1564) (hmask pH1564) 1106 458 (true, H1564_cp1.1, H1564_cp1.2)) ∧ ptTest pH1564 (runFrom pH1564 (fmask pH1564) (cmask pH1564) (hmask pH1564) 1106 458 (true, H1564_cp1.1, H1564_cp1.2)) 1564 782 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1564_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1564_fin) true) H1564_seg1) (by decide) rfl H1564_fin ptTest_fst
noncomputable def I1564_cp1 : Nat × Nat := t7val% (fastRun pI1564 1 1105 (init pI1564) (init pI1564))
theorem I1564_seg1 : segOK pI1564 1 1105 (init pI1564) (init pI1564) I1564_cp1.1 I1564_cp1.2 = true := by
  decide +kernel
theorem I1564_fin : (prmOK pI1564 1564 && intTest pI1564 (runFrom pI1564 (fmask pI1564) (cmask pI1564) (hmask pI1564) 1106 458 (true, I1564_cp1.1, I1564_cp1.2)) 1564 20 true) = true := by
  decide +kernel
theorem I1564_ok : RunOK pI1564 1564 (runFrom pI1564 (fmask pI1564) (cmask pI1564) (hmask pI1564) 1106 458 (true, I1564_cp1.1, I1564_cp1.2)) ∧ intTest pI1564 (runFrom pI1564 (fmask pI1564) (cmask pI1564) (hmask pI1564) 1106 458 (true, I1564_cp1.1, I1564_cp1.2)) 1564 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1564_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1564_fin) true) I1564_seg1) (by decide) rfl I1564_fin intTest_fst
theorem link1564 : linkOK pL1564 pH1564 pI1564 = true := by decide +kernel
theorem cvx1564 : ConvexBetweenHumps 1564 :=
  cvx_of L1564_ok H1564_ok I1564_ok link1564 (by decide)
theorem cenlink1564 : cenLinkOK pI1564 1564 = true := by decide +kernel
theorem cen1564 : CenterUniqueMin 1564 ∧ DipHyp 1564 ∧ OnePointHyps 1564 :=
  cen_of L1564_ok H1564_ok I1564_ok link1564 cenlink1564

/-! ### `N = 1565` -/

def pL1565 : Prm := ⟨81, 39, 39, 1567, 11, 18446744073709551616, 120214023868776943, 120214023868776943⟩
def pH1565 : Prm := ⟨81, 39, 39, 1567, 11, 18446744073709551616, 120215123380404719, 120215123380404719⟩
def pI1565 : Prm := ⟨67, 33, 31, 1567, 11, 18446744073709551616, 120214023868776943, 120215123380404719⟩
noncomputable def L1565_cp1 : Nat × Nat := t7val% (fastRun pL1565 1 1106 (init pL1565) (init pL1565))
theorem L1565_seg1 : segOK pL1565 1 1106 (init pL1565) (init pL1565) L1565_cp1.1 L1565_cp1.2 = true := by
  decide +kernel
theorem L1565_fin : (prmOK pL1565 1565 && ptTest pL1565 (runFrom pL1565 (fmask pL1565) (cmask pL1565) (hmask pL1565) 1107 458 (true, L1565_cp1.1, L1565_cp1.2)) 1565 783 false) = true := by
  decide +kernel
theorem L1565_ok : RunOK pL1565 1565 (runFrom pL1565 (fmask pL1565) (cmask pL1565) (hmask pL1565) 1107 458 (true, L1565_cp1.1, L1565_cp1.2)) ∧ ptTest pL1565 (runFrom pL1565 (fmask pL1565) (cmask pL1565) (hmask pL1565) 1107 458 (true, L1565_cp1.1, L1565_cp1.2)) 1565 783 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1565_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1565_fin) true) L1565_seg1) (by decide) rfl L1565_fin ptTest_fst
noncomputable def H1565_cp1 : Nat × Nat := t7val% (fastRun pH1565 1 1106 (init pH1565) (init pH1565))
theorem H1565_seg1 : segOK pH1565 1 1106 (init pH1565) (init pH1565) H1565_cp1.1 H1565_cp1.2 = true := by
  decide +kernel
theorem H1565_fin : (prmOK pH1565 1565 && ptTest pH1565 (runFrom pH1565 (fmask pH1565) (cmask pH1565) (hmask pH1565) 1107 458 (true, H1565_cp1.1, H1565_cp1.2)) 1565 783 true) = true := by
  decide +kernel
theorem H1565_ok : RunOK pH1565 1565 (runFrom pH1565 (fmask pH1565) (cmask pH1565) (hmask pH1565) 1107 458 (true, H1565_cp1.1, H1565_cp1.2)) ∧ ptTest pH1565 (runFrom pH1565 (fmask pH1565) (cmask pH1565) (hmask pH1565) 1107 458 (true, H1565_cp1.1, H1565_cp1.2)) 1565 783 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1565_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1565_fin) true) H1565_seg1) (by decide) rfl H1565_fin ptTest_fst
noncomputable def I1565_cp1 : Nat × Nat := t7val% (fastRun pI1565 1 1106 (init pI1565) (init pI1565))
theorem I1565_seg1 : segOK pI1565 1 1106 (init pI1565) (init pI1565) I1565_cp1.1 I1565_cp1.2 = true := by
  decide +kernel
theorem I1565_fin : (prmOK pI1565 1565 && intTest pI1565 (runFrom pI1565 (fmask pI1565) (cmask pI1565) (hmask pI1565) 1107 458 (true, I1565_cp1.1, I1565_cp1.2)) 1565 20 false) = true := by
  decide +kernel
theorem I1565_ok : RunOK pI1565 1565 (runFrom pI1565 (fmask pI1565) (cmask pI1565) (hmask pI1565) 1107 458 (true, I1565_cp1.1, I1565_cp1.2)) ∧ intTest pI1565 (runFrom pI1565 (fmask pI1565) (cmask pI1565) (hmask pI1565) 1107 458 (true, I1565_cp1.1, I1565_cp1.2)) 1565 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1565_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1565_fin) true) I1565_seg1) (by decide) rfl I1565_fin intTest_fst
theorem link1565 : linkOK pL1565 pH1565 pI1565 = true := by decide +kernel
theorem cvx1565 : ConvexBetweenHumps 1565 :=
  cvx_of L1565_ok H1565_ok I1565_ok link1565 (by decide)

/-! ### `N = 1566` -/

def pL1566 : Prm := ⟨81, 39, 39, 1568, 11, 18446744073709551616, 120151460074586697, 120151460074586697⟩
def pH1566 : Prm := ⟨81, 39, 39, 1568, 11, 18446744073709551616, 120152559586214473, 120152559586214473⟩
def pI1566 : Prm := ⟨67, 33, 31, 1568, 11, 18446744073709551616, 120151460074586697, 120152559586214473⟩
noncomputable def L1566_cp1 : Nat × Nat := t7val% (fastRun pL1566 1 1106 (init pL1566) (init pL1566))
theorem L1566_seg1 : segOK pL1566 1 1106 (init pL1566) (init pL1566) L1566_cp1.1 L1566_cp1.2 = true := by
  decide +kernel
theorem L1566_fin : (prmOK pL1566 1566 && ptTest pL1566 (runFrom pL1566 (fmask pL1566) (cmask pL1566) (hmask pL1566) 1107 459 (true, L1566_cp1.1, L1566_cp1.2)) 1566 783 false) = true := by
  decide +kernel
theorem L1566_ok : RunOK pL1566 1566 (runFrom pL1566 (fmask pL1566) (cmask pL1566) (hmask pL1566) 1107 459 (true, L1566_cp1.1, L1566_cp1.2)) ∧ ptTest pL1566 (runFrom pL1566 (fmask pL1566) (cmask pL1566) (hmask pL1566) 1107 459 (true, L1566_cp1.1, L1566_cp1.2)) 1566 783 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1566_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1566_fin) true) L1566_seg1) (by decide) rfl L1566_fin ptTest_fst
noncomputable def H1566_cp1 : Nat × Nat := t7val% (fastRun pH1566 1 1106 (init pH1566) (init pH1566))
theorem H1566_seg1 : segOK pH1566 1 1106 (init pH1566) (init pH1566) H1566_cp1.1 H1566_cp1.2 = true := by
  decide +kernel
theorem H1566_fin : (prmOK pH1566 1566 && ptTest pH1566 (runFrom pH1566 (fmask pH1566) (cmask pH1566) (hmask pH1566) 1107 459 (true, H1566_cp1.1, H1566_cp1.2)) 1566 783 true) = true := by
  decide +kernel
theorem H1566_ok : RunOK pH1566 1566 (runFrom pH1566 (fmask pH1566) (cmask pH1566) (hmask pH1566) 1107 459 (true, H1566_cp1.1, H1566_cp1.2)) ∧ ptTest pH1566 (runFrom pH1566 (fmask pH1566) (cmask pH1566) (hmask pH1566) 1107 459 (true, H1566_cp1.1, H1566_cp1.2)) 1566 783 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1566_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1566_fin) true) H1566_seg1) (by decide) rfl H1566_fin ptTest_fst
noncomputable def I1566_cp1 : Nat × Nat := t7val% (fastRun pI1566 1 1106 (init pI1566) (init pI1566))
theorem I1566_seg1 : segOK pI1566 1 1106 (init pI1566) (init pI1566) I1566_cp1.1 I1566_cp1.2 = true := by
  decide +kernel
theorem I1566_fin : (prmOK pI1566 1566 && intTest pI1566 (runFrom pI1566 (fmask pI1566) (cmask pI1566) (hmask pI1566) 1107 459 (true, I1566_cp1.1, I1566_cp1.2)) 1566 20 true) = true := by
  decide +kernel
theorem I1566_ok : RunOK pI1566 1566 (runFrom pI1566 (fmask pI1566) (cmask pI1566) (hmask pI1566) 1107 459 (true, I1566_cp1.1, I1566_cp1.2)) ∧ intTest pI1566 (runFrom pI1566 (fmask pI1566) (cmask pI1566) (hmask pI1566) 1107 459 (true, I1566_cp1.1, I1566_cp1.2)) 1566 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1566_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1566_fin) true) I1566_seg1) (by decide) rfl I1566_fin intTest_fst
theorem link1566 : linkOK pL1566 pH1566 pI1566 = true := by decide +kernel
theorem cvx1566 : ConvexBetweenHumps 1566 :=
  cvx_of L1566_ok H1566_ok I1566_ok link1566 (by decide)
theorem cenlink1566 : cenLinkOK pI1566 1566 = true := by decide +kernel
theorem cen1566 : CenterUniqueMin 1566 ∧ DipHyp 1566 ∧ OnePointHyps 1566 :=
  cen_of L1566_ok H1566_ok I1566_ok link1566 cenlink1566

/-! ### `N = 1567` -/

def pL1567 : Prm := ⟨81, 39, 39, 1569, 11, 18446744073709551616, 120088937674392091, 120088937674392091⟩
def pH1567 : Prm := ⟨81, 39, 39, 1569, 11, 18446744073709551616, 120090037186019867, 120090037186019867⟩
def pI1567 : Prm := ⟨67, 33, 31, 1569, 11, 18446744073709551616, 120088937674392091, 120090037186019867⟩
noncomputable def L1567_cp1 : Nat × Nat := t7val% (fastRun pL1567 1 1107 (init pL1567) (init pL1567))
theorem L1567_seg1 : segOK pL1567 1 1107 (init pL1567) (init pL1567) L1567_cp1.1 L1567_cp1.2 = true := by
  decide +kernel
theorem L1567_fin : (prmOK pL1567 1567 && ptTest pL1567 (runFrom pL1567 (fmask pL1567) (cmask pL1567) (hmask pL1567) 1108 459 (true, L1567_cp1.1, L1567_cp1.2)) 1567 784 false) = true := by
  decide +kernel
theorem L1567_ok : RunOK pL1567 1567 (runFrom pL1567 (fmask pL1567) (cmask pL1567) (hmask pL1567) 1108 459 (true, L1567_cp1.1, L1567_cp1.2)) ∧ ptTest pL1567 (runFrom pL1567 (fmask pL1567) (cmask pL1567) (hmask pL1567) 1108 459 (true, L1567_cp1.1, L1567_cp1.2)) 1567 784 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1567_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1567_fin) true) L1567_seg1) (by decide) rfl L1567_fin ptTest_fst
noncomputable def H1567_cp1 : Nat × Nat := t7val% (fastRun pH1567 1 1107 (init pH1567) (init pH1567))
theorem H1567_seg1 : segOK pH1567 1 1107 (init pH1567) (init pH1567) H1567_cp1.1 H1567_cp1.2 = true := by
  decide +kernel
theorem H1567_fin : (prmOK pH1567 1567 && ptTest pH1567 (runFrom pH1567 (fmask pH1567) (cmask pH1567) (hmask pH1567) 1108 459 (true, H1567_cp1.1, H1567_cp1.2)) 1567 784 true) = true := by
  decide +kernel
theorem H1567_ok : RunOK pH1567 1567 (runFrom pH1567 (fmask pH1567) (cmask pH1567) (hmask pH1567) 1108 459 (true, H1567_cp1.1, H1567_cp1.2)) ∧ ptTest pH1567 (runFrom pH1567 (fmask pH1567) (cmask pH1567) (hmask pH1567) 1108 459 (true, H1567_cp1.1, H1567_cp1.2)) 1567 784 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1567_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1567_fin) true) H1567_seg1) (by decide) rfl H1567_fin ptTest_fst
noncomputable def I1567_cp1 : Nat × Nat := t7val% (fastRun pI1567 1 1107 (init pI1567) (init pI1567))
theorem I1567_seg1 : segOK pI1567 1 1107 (init pI1567) (init pI1567) I1567_cp1.1 I1567_cp1.2 = true := by
  decide +kernel
theorem I1567_fin : (prmOK pI1567 1567 && intTest pI1567 (runFrom pI1567 (fmask pI1567) (cmask pI1567) (hmask pI1567) 1108 459 (true, I1567_cp1.1, I1567_cp1.2)) 1567 20 false) = true := by
  decide +kernel
theorem I1567_ok : RunOK pI1567 1567 (runFrom pI1567 (fmask pI1567) (cmask pI1567) (hmask pI1567) 1108 459 (true, I1567_cp1.1, I1567_cp1.2)) ∧ intTest pI1567 (runFrom pI1567 (fmask pI1567) (cmask pI1567) (hmask pI1567) 1108 459 (true, I1567_cp1.1, I1567_cp1.2)) 1567 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1567_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1567_fin) true) I1567_seg1) (by decide) rfl I1567_fin intTest_fst
theorem link1567 : linkOK pL1567 pH1567 pI1567 = true := by decide +kernel
theorem cvx1567 : ConvexBetweenHumps 1567 :=
  cvx_of L1567_ok H1567_ok I1567_ok link1567 (by decide)

/-! ### `N = 1568` -/

def pL1568 : Prm := ⟨81, 39, 39, 1570, 11, 18446744073709551616, 120026515316701321, 120026515316701321⟩
def pH1568 : Prm := ⟨81, 39, 39, 1570, 11, 18446744073709551616, 120027614828329097, 120027614828329097⟩
def pI1568 : Prm := ⟨67, 33, 31, 1570, 11, 18446744073709551616, 120026515316701321, 120027614828329097⟩
noncomputable def L1568_cp1 : Nat × Nat := t7val% (fastRun pL1568 1 1108 (init pL1568) (init pL1568))
theorem L1568_seg1 : segOK pL1568 1 1108 (init pL1568) (init pL1568) L1568_cp1.1 L1568_cp1.2 = true := by
  decide +kernel
theorem L1568_fin : (prmOK pL1568 1568 && ptTest pL1568 (runFrom pL1568 (fmask pL1568) (cmask pL1568) (hmask pL1568) 1109 459 (true, L1568_cp1.1, L1568_cp1.2)) 1568 784 false) = true := by
  decide +kernel
theorem L1568_ok : RunOK pL1568 1568 (runFrom pL1568 (fmask pL1568) (cmask pL1568) (hmask pL1568) 1109 459 (true, L1568_cp1.1, L1568_cp1.2)) ∧ ptTest pL1568 (runFrom pL1568 (fmask pL1568) (cmask pL1568) (hmask pL1568) 1109 459 (true, L1568_cp1.1, L1568_cp1.2)) 1568 784 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1568_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1568_fin) true) L1568_seg1) (by decide) rfl L1568_fin ptTest_fst
noncomputable def H1568_cp1 : Nat × Nat := t7val% (fastRun pH1568 1 1108 (init pH1568) (init pH1568))
theorem H1568_seg1 : segOK pH1568 1 1108 (init pH1568) (init pH1568) H1568_cp1.1 H1568_cp1.2 = true := by
  decide +kernel
theorem H1568_fin : (prmOK pH1568 1568 && ptTest pH1568 (runFrom pH1568 (fmask pH1568) (cmask pH1568) (hmask pH1568) 1109 459 (true, H1568_cp1.1, H1568_cp1.2)) 1568 784 true) = true := by
  decide +kernel
theorem H1568_ok : RunOK pH1568 1568 (runFrom pH1568 (fmask pH1568) (cmask pH1568) (hmask pH1568) 1109 459 (true, H1568_cp1.1, H1568_cp1.2)) ∧ ptTest pH1568 (runFrom pH1568 (fmask pH1568) (cmask pH1568) (hmask pH1568) 1109 459 (true, H1568_cp1.1, H1568_cp1.2)) 1568 784 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1568_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1568_fin) true) H1568_seg1) (by decide) rfl H1568_fin ptTest_fst
noncomputable def I1568_cp1 : Nat × Nat := t7val% (fastRun pI1568 1 1108 (init pI1568) (init pI1568))
theorem I1568_seg1 : segOK pI1568 1 1108 (init pI1568) (init pI1568) I1568_cp1.1 I1568_cp1.2 = true := by
  decide +kernel
theorem I1568_fin : (prmOK pI1568 1568 && intTest pI1568 (runFrom pI1568 (fmask pI1568) (cmask pI1568) (hmask pI1568) 1109 459 (true, I1568_cp1.1, I1568_cp1.2)) 1568 20 true) = true := by
  decide +kernel
theorem I1568_ok : RunOK pI1568 1568 (runFrom pI1568 (fmask pI1568) (cmask pI1568) (hmask pI1568) 1109 459 (true, I1568_cp1.1, I1568_cp1.2)) ∧ intTest pI1568 (runFrom pI1568 (fmask pI1568) (cmask pI1568) (hmask pI1568) 1109 459 (true, I1568_cp1.1, I1568_cp1.2)) 1568 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1568_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1568_fin) true) I1568_seg1) (by decide) rfl I1568_fin intTest_fst
theorem link1568 : linkOK pL1568 pH1568 pI1568 = true := by decide +kernel
theorem cvx1568 : ConvexBetweenHumps 1568 :=
  cvx_of L1568_ok H1568_ok I1568_ok link1568 (by decide)
theorem cenlink1568 : cenLinkOK pI1568 1568 = true := by decide +kernel
theorem cen1568 : CenterUniqueMin 1568 ∧ DipHyp 1568 ∧ OnePointHyps 1568 :=
  cen_of L1568_ok H1568_ok I1568_ok link1568 cenlink1568

/-! ### `N = 1569` -/

def pL1569 : Prm := ⟨81, 39, 39, 1571, 11, 18446744073709551616, 119964134219673124, 119964134219673124⟩
def pH1569 : Prm := ⟨81, 39, 39, 1571, 11, 18446744073709551616, 119965233731300900, 119965233731300900⟩
def pI1569 : Prm := ⟨67, 33, 31, 1571, 11, 18446744073709551616, 119964134219673124, 119965233731300900⟩
noncomputable def L1569_cp1 : Nat × Nat := t7val% (fastRun pL1569 1 1108 (init pL1569) (init pL1569))
theorem L1569_seg1 : segOK pL1569 1 1108 (init pL1569) (init pL1569) L1569_cp1.1 L1569_cp1.2 = true := by
  decide +kernel
theorem L1569_fin : (prmOK pL1569 1569 && ptTest pL1569 (runFrom pL1569 (fmask pL1569) (cmask pL1569) (hmask pL1569) 1109 460 (true, L1569_cp1.1, L1569_cp1.2)) 1569 785 false) = true := by
  decide +kernel
theorem L1569_ok : RunOK pL1569 1569 (runFrom pL1569 (fmask pL1569) (cmask pL1569) (hmask pL1569) 1109 460 (true, L1569_cp1.1, L1569_cp1.2)) ∧ ptTest pL1569 (runFrom pL1569 (fmask pL1569) (cmask pL1569) (hmask pL1569) 1109 460 (true, L1569_cp1.1, L1569_cp1.2)) 1569 785 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1569_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1569_fin) true) L1569_seg1) (by decide) rfl L1569_fin ptTest_fst
noncomputable def H1569_cp1 : Nat × Nat := t7val% (fastRun pH1569 1 1108 (init pH1569) (init pH1569))
theorem H1569_seg1 : segOK pH1569 1 1108 (init pH1569) (init pH1569) H1569_cp1.1 H1569_cp1.2 = true := by
  decide +kernel
theorem H1569_fin : (prmOK pH1569 1569 && ptTest pH1569 (runFrom pH1569 (fmask pH1569) (cmask pH1569) (hmask pH1569) 1109 460 (true, H1569_cp1.1, H1569_cp1.2)) 1569 785 true) = true := by
  decide +kernel
theorem H1569_ok : RunOK pH1569 1569 (runFrom pH1569 (fmask pH1569) (cmask pH1569) (hmask pH1569) 1109 460 (true, H1569_cp1.1, H1569_cp1.2)) ∧ ptTest pH1569 (runFrom pH1569 (fmask pH1569) (cmask pH1569) (hmask pH1569) 1109 460 (true, H1569_cp1.1, H1569_cp1.2)) 1569 785 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1569_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1569_fin) true) H1569_seg1) (by decide) rfl H1569_fin ptTest_fst
noncomputable def I1569_cp1 : Nat × Nat := t7val% (fastRun pI1569 1 1108 (init pI1569) (init pI1569))
theorem I1569_seg1 : segOK pI1569 1 1108 (init pI1569) (init pI1569) I1569_cp1.1 I1569_cp1.2 = true := by
  decide +kernel
theorem I1569_fin : (prmOK pI1569 1569 && intTest pI1569 (runFrom pI1569 (fmask pI1569) (cmask pI1569) (hmask pI1569) 1109 460 (true, I1569_cp1.1, I1569_cp1.2)) 1569 20 false) = true := by
  decide +kernel
theorem I1569_ok : RunOK pI1569 1569 (runFrom pI1569 (fmask pI1569) (cmask pI1569) (hmask pI1569) 1109 460 (true, I1569_cp1.1, I1569_cp1.2)) ∧ intTest pI1569 (runFrom pI1569 (fmask pI1569) (cmask pI1569) (hmask pI1569) 1109 460 (true, I1569_cp1.1, I1569_cp1.2)) 1569 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1569_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1569_fin) true) I1569_seg1) (by decide) rfl I1569_fin intTest_fst
theorem link1569 : linkOK pL1569 pH1569 pI1569 = true := by decide +kernel
theorem cvx1569 : ConvexBetweenHumps 1569 :=
  cvx_of L1569_ok H1569_ok I1569_ok link1569 (by decide)

/-! ### `N = 1570` -/

def pL1570 : Prm := ⟨81, 39, 39, 1572, 11, 18446744073709551616, 119901852804275109, 119901852804275109⟩
def pH1570 : Prm := ⟨81, 39, 39, 1572, 11, 18446744073709551616, 119902952315902885, 119902952315902885⟩
def pI1570 : Prm := ⟨67, 33, 31, 1572, 11, 18446744073709551616, 119901852804275109, 119902952315902885⟩
noncomputable def L1570_cp1 : Nat × Nat := t7val% (fastRun pL1570 1 1109 (init pL1570) (init pL1570))
theorem L1570_seg1 : segOK pL1570 1 1109 (init pL1570) (init pL1570) L1570_cp1.1 L1570_cp1.2 = true := by
  decide +kernel
theorem L1570_fin : (prmOK pL1570 1570 && ptTest pL1570 (runFrom pL1570 (fmask pL1570) (cmask pL1570) (hmask pL1570) 1110 460 (true, L1570_cp1.1, L1570_cp1.2)) 1570 785 false) = true := by
  decide +kernel
theorem L1570_ok : RunOK pL1570 1570 (runFrom pL1570 (fmask pL1570) (cmask pL1570) (hmask pL1570) 1110 460 (true, L1570_cp1.1, L1570_cp1.2)) ∧ ptTest pL1570 (runFrom pL1570 (fmask pL1570) (cmask pL1570) (hmask pL1570) 1110 460 (true, L1570_cp1.1, L1570_cp1.2)) 1570 785 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1570_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1570_fin) true) L1570_seg1) (by decide) rfl L1570_fin ptTest_fst
noncomputable def H1570_cp1 : Nat × Nat := t7val% (fastRun pH1570 1 1109 (init pH1570) (init pH1570))
theorem H1570_seg1 : segOK pH1570 1 1109 (init pH1570) (init pH1570) H1570_cp1.1 H1570_cp1.2 = true := by
  decide +kernel
theorem H1570_fin : (prmOK pH1570 1570 && ptTest pH1570 (runFrom pH1570 (fmask pH1570) (cmask pH1570) (hmask pH1570) 1110 460 (true, H1570_cp1.1, H1570_cp1.2)) 1570 785 true) = true := by
  decide +kernel
theorem H1570_ok : RunOK pH1570 1570 (runFrom pH1570 (fmask pH1570) (cmask pH1570) (hmask pH1570) 1110 460 (true, H1570_cp1.1, H1570_cp1.2)) ∧ ptTest pH1570 (runFrom pH1570 (fmask pH1570) (cmask pH1570) (hmask pH1570) 1110 460 (true, H1570_cp1.1, H1570_cp1.2)) 1570 785 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1570_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1570_fin) true) H1570_seg1) (by decide) rfl H1570_fin ptTest_fst
noncomputable def I1570_cp1 : Nat × Nat := t7val% (fastRun pI1570 1 1109 (init pI1570) (init pI1570))
theorem I1570_seg1 : segOK pI1570 1 1109 (init pI1570) (init pI1570) I1570_cp1.1 I1570_cp1.2 = true := by
  decide +kernel
theorem I1570_fin : (prmOK pI1570 1570 && intTest pI1570 (runFrom pI1570 (fmask pI1570) (cmask pI1570) (hmask pI1570) 1110 460 (true, I1570_cp1.1, I1570_cp1.2)) 1570 20 true) = true := by
  decide +kernel
theorem I1570_ok : RunOK pI1570 1570 (runFrom pI1570 (fmask pI1570) (cmask pI1570) (hmask pI1570) 1110 460 (true, I1570_cp1.1, I1570_cp1.2)) ∧ intTest pI1570 (runFrom pI1570 (fmask pI1570) (cmask pI1570) (hmask pI1570) 1110 460 (true, I1570_cp1.1, I1570_cp1.2)) 1570 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1570_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1570_fin) true) I1570_seg1) (by decide) rfl I1570_fin intTest_fst
theorem link1570 : linkOK pL1570 pH1570 pI1570 = true := by decide +kernel
theorem cvx1570 : ConvexBetweenHumps 1570 :=
  cvx_of L1570_ok H1570_ok I1570_ok link1570 (by decide)
theorem cenlink1570 : cenLinkOK pI1570 1570 = true := by decide +kernel
theorem cen1570 : CenterUniqueMin 1570 ∧ DipHyp 1570 ∧ OnePointHyps 1570 :=
  cen_of L1570_ok H1570_ok I1570_ok link1570 cenlink1570

/-! ### `N = 1571` -/

def pL1571 : Prm := ⟨81, 39, 39, 1573, 11, 18446744073709551616, 119839612516760004, 119839612516760004⟩
def pH1571 : Prm := ⟨81, 39, 39, 1573, 11, 18446744073709551616, 119840712028387780, 119840712028387780⟩
def pI1571 : Prm := ⟨67, 33, 31, 1573, 11, 18446744073709551616, 119839612516760004, 119840712028387780⟩
noncomputable def L1571_cp1 : Nat × Nat := t7val% (fastRun pL1571 1 1110 (init pL1571) (init pL1571))
theorem L1571_seg1 : segOK pL1571 1 1110 (init pL1571) (init pL1571) L1571_cp1.1 L1571_cp1.2 = true := by
  decide +kernel
theorem L1571_fin : (prmOK pL1571 1571 && ptTest pL1571 (runFrom pL1571 (fmask pL1571) (cmask pL1571) (hmask pL1571) 1111 460 (true, L1571_cp1.1, L1571_cp1.2)) 1571 786 false) = true := by
  decide +kernel
theorem L1571_ok : RunOK pL1571 1571 (runFrom pL1571 (fmask pL1571) (cmask pL1571) (hmask pL1571) 1111 460 (true, L1571_cp1.1, L1571_cp1.2)) ∧ ptTest pL1571 (runFrom pL1571 (fmask pL1571) (cmask pL1571) (hmask pL1571) 1111 460 (true, L1571_cp1.1, L1571_cp1.2)) 1571 786 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1571_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1571_fin) true) L1571_seg1) (by decide) rfl L1571_fin ptTest_fst
noncomputable def H1571_cp1 : Nat × Nat := t7val% (fastRun pH1571 1 1110 (init pH1571) (init pH1571))
theorem H1571_seg1 : segOK pH1571 1 1110 (init pH1571) (init pH1571) H1571_cp1.1 H1571_cp1.2 = true := by
  decide +kernel
theorem H1571_fin : (prmOK pH1571 1571 && ptTest pH1571 (runFrom pH1571 (fmask pH1571) (cmask pH1571) (hmask pH1571) 1111 460 (true, H1571_cp1.1, H1571_cp1.2)) 1571 786 true) = true := by
  decide +kernel
theorem H1571_ok : RunOK pH1571 1571 (runFrom pH1571 (fmask pH1571) (cmask pH1571) (hmask pH1571) 1111 460 (true, H1571_cp1.1, H1571_cp1.2)) ∧ ptTest pH1571 (runFrom pH1571 (fmask pH1571) (cmask pH1571) (hmask pH1571) 1111 460 (true, H1571_cp1.1, H1571_cp1.2)) 1571 786 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1571_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1571_fin) true) H1571_seg1) (by decide) rfl H1571_fin ptTest_fst
noncomputable def I1571_cp1 : Nat × Nat := t7val% (fastRun pI1571 1 1110 (init pI1571) (init pI1571))
theorem I1571_seg1 : segOK pI1571 1 1110 (init pI1571) (init pI1571) I1571_cp1.1 I1571_cp1.2 = true := by
  decide +kernel
theorem I1571_fin : (prmOK pI1571 1571 && intTest pI1571 (runFrom pI1571 (fmask pI1571) (cmask pI1571) (hmask pI1571) 1111 460 (true, I1571_cp1.1, I1571_cp1.2)) 1571 20 false) = true := by
  decide +kernel
theorem I1571_ok : RunOK pI1571 1571 (runFrom pI1571 (fmask pI1571) (cmask pI1571) (hmask pI1571) 1111 460 (true, I1571_cp1.1, I1571_cp1.2)) ∧ intTest pI1571 (runFrom pI1571 (fmask pI1571) (cmask pI1571) (hmask pI1571) 1111 460 (true, I1571_cp1.1, I1571_cp1.2)) 1571 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1571_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1571_fin) true) I1571_seg1) (by decide) rfl I1571_fin intTest_fst
theorem link1571 : linkOK pL1571 pH1571 pI1571 = true := by decide +kernel
theorem cvx1571 : ConvexBetweenHumps 1571 :=
  cvx_of L1571_ok H1571_ok I1571_ok link1571 (by decide)

/-! ### `N = 1572` -/

def pL1572 : Prm := ⟨81, 39, 39, 1574, 11, 18446744073709551616, 119777471551772313, 119777471551772313⟩
def pH1572 : Prm := ⟨81, 39, 39, 1574, 11, 18446744073709551616, 119778571063400089, 119778571063400089⟩
def pI1572 : Prm := ⟨67, 33, 31, 1574, 11, 18446744073709551616, 119777471551772313, 119778571063400089⟩
noncomputable def L1572_cp1 : Nat × Nat := t7val% (fastRun pL1572 1 1111 (init pL1572) (init pL1572))
theorem L1572_seg1 : segOK pL1572 1 1111 (init pL1572) (init pL1572) L1572_cp1.1 L1572_cp1.2 = true := by
  decide +kernel
theorem L1572_fin : (prmOK pL1572 1572 && ptTest pL1572 (runFrom pL1572 (fmask pL1572) (cmask pL1572) (hmask pL1572) 1112 460 (true, L1572_cp1.1, L1572_cp1.2)) 1572 786 false) = true := by
  decide +kernel
theorem L1572_ok : RunOK pL1572 1572 (runFrom pL1572 (fmask pL1572) (cmask pL1572) (hmask pL1572) 1112 460 (true, L1572_cp1.1, L1572_cp1.2)) ∧ ptTest pL1572 (runFrom pL1572 (fmask pL1572) (cmask pL1572) (hmask pL1572) 1112 460 (true, L1572_cp1.1, L1572_cp1.2)) 1572 786 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1572_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1572_fin) true) L1572_seg1) (by decide) rfl L1572_fin ptTest_fst
noncomputable def H1572_cp1 : Nat × Nat := t7val% (fastRun pH1572 1 1111 (init pH1572) (init pH1572))
theorem H1572_seg1 : segOK pH1572 1 1111 (init pH1572) (init pH1572) H1572_cp1.1 H1572_cp1.2 = true := by
  decide +kernel
theorem H1572_fin : (prmOK pH1572 1572 && ptTest pH1572 (runFrom pH1572 (fmask pH1572) (cmask pH1572) (hmask pH1572) 1112 460 (true, H1572_cp1.1, H1572_cp1.2)) 1572 786 true) = true := by
  decide +kernel
theorem H1572_ok : RunOK pH1572 1572 (runFrom pH1572 (fmask pH1572) (cmask pH1572) (hmask pH1572) 1112 460 (true, H1572_cp1.1, H1572_cp1.2)) ∧ ptTest pH1572 (runFrom pH1572 (fmask pH1572) (cmask pH1572) (hmask pH1572) 1112 460 (true, H1572_cp1.1, H1572_cp1.2)) 1572 786 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1572_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1572_fin) true) H1572_seg1) (by decide) rfl H1572_fin ptTest_fst
noncomputable def I1572_cp1 : Nat × Nat := t7val% (fastRun pI1572 1 1111 (init pI1572) (init pI1572))
theorem I1572_seg1 : segOK pI1572 1 1111 (init pI1572) (init pI1572) I1572_cp1.1 I1572_cp1.2 = true := by
  decide +kernel
theorem I1572_fin : (prmOK pI1572 1572 && intTest pI1572 (runFrom pI1572 (fmask pI1572) (cmask pI1572) (hmask pI1572) 1112 460 (true, I1572_cp1.1, I1572_cp1.2)) 1572 20 true) = true := by
  decide +kernel
theorem I1572_ok : RunOK pI1572 1572 (runFrom pI1572 (fmask pI1572) (cmask pI1572) (hmask pI1572) 1112 460 (true, I1572_cp1.1, I1572_cp1.2)) ∧ intTest pI1572 (runFrom pI1572 (fmask pI1572) (cmask pI1572) (hmask pI1572) 1112 460 (true, I1572_cp1.1, I1572_cp1.2)) 1572 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1572_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1572_fin) true) I1572_seg1) (by decide) rfl I1572_fin intTest_fst
theorem link1572 : linkOK pL1572 pH1572 pI1572 = true := by decide +kernel
theorem cvx1572 : ConvexBetweenHumps 1572 :=
  cvx_of L1572_ok H1572_ok I1572_ok link1572 (by decide)
theorem cenlink1572 : cenLinkOK pI1572 1572 = true := by decide +kernel
theorem cen1572 : CenterUniqueMin 1572 ∧ DipHyp 1572 ∧ OnePointHyps 1572 :=
  cen_of L1572_ok H1572_ok I1572_ok link1572 cenlink1572

/-! ### `N = 1573` -/

def pL1573 : Prm := ⟨81, 39, 39, 1575, 11, 18446744073709551616, 119715371582459717, 119715371582459717⟩
def pH1573 : Prm := ⟨81, 39, 39, 1575, 11, 18446744073709551616, 119716471094087493, 119716471094087493⟩
def pI1573 : Prm := ⟨67, 33, 31, 1575, 11, 18446744073709551616, 119715371582459717, 119716471094087493⟩
noncomputable def L1573_cp1 : Nat × Nat := t7val% (fastRun pL1573 1 1111 (init pL1573) (init pL1573))
theorem L1573_seg1 : segOK pL1573 1 1111 (init pL1573) (init pL1573) L1573_cp1.1 L1573_cp1.2 = true := by
  decide +kernel
theorem L1573_fin : (prmOK pL1573 1573 && ptTest pL1573 (runFrom pL1573 (fmask pL1573) (cmask pL1573) (hmask pL1573) 1112 461 (true, L1573_cp1.1, L1573_cp1.2)) 1573 787 false) = true := by
  decide +kernel
theorem L1573_ok : RunOK pL1573 1573 (runFrom pL1573 (fmask pL1573) (cmask pL1573) (hmask pL1573) 1112 461 (true, L1573_cp1.1, L1573_cp1.2)) ∧ ptTest pL1573 (runFrom pL1573 (fmask pL1573) (cmask pL1573) (hmask pL1573) 1112 461 (true, L1573_cp1.1, L1573_cp1.2)) 1573 787 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1573_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1573_fin) true) L1573_seg1) (by decide) rfl L1573_fin ptTest_fst
noncomputable def H1573_cp1 : Nat × Nat := t7val% (fastRun pH1573 1 1111 (init pH1573) (init pH1573))
theorem H1573_seg1 : segOK pH1573 1 1111 (init pH1573) (init pH1573) H1573_cp1.1 H1573_cp1.2 = true := by
  decide +kernel
theorem H1573_fin : (prmOK pH1573 1573 && ptTest pH1573 (runFrom pH1573 (fmask pH1573) (cmask pH1573) (hmask pH1573) 1112 461 (true, H1573_cp1.1, H1573_cp1.2)) 1573 787 true) = true := by
  decide +kernel
theorem H1573_ok : RunOK pH1573 1573 (runFrom pH1573 (fmask pH1573) (cmask pH1573) (hmask pH1573) 1112 461 (true, H1573_cp1.1, H1573_cp1.2)) ∧ ptTest pH1573 (runFrom pH1573 (fmask pH1573) (cmask pH1573) (hmask pH1573) 1112 461 (true, H1573_cp1.1, H1573_cp1.2)) 1573 787 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1573_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1573_fin) true) H1573_seg1) (by decide) rfl H1573_fin ptTest_fst
noncomputable def I1573_cp1 : Nat × Nat := t7val% (fastRun pI1573 1 1111 (init pI1573) (init pI1573))
theorem I1573_seg1 : segOK pI1573 1 1111 (init pI1573) (init pI1573) I1573_cp1.1 I1573_cp1.2 = true := by
  decide +kernel
theorem I1573_fin : (prmOK pI1573 1573 && intTest pI1573 (runFrom pI1573 (fmask pI1573) (cmask pI1573) (hmask pI1573) 1112 461 (true, I1573_cp1.1, I1573_cp1.2)) 1573 20 false) = true := by
  decide +kernel
theorem I1573_ok : RunOK pI1573 1573 (runFrom pI1573 (fmask pI1573) (cmask pI1573) (hmask pI1573) 1112 461 (true, I1573_cp1.1, I1573_cp1.2)) ∧ intTest pI1573 (runFrom pI1573 (fmask pI1573) (cmask pI1573) (hmask pI1573) 1112 461 (true, I1573_cp1.1, I1573_cp1.2)) 1573 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1573_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1573_fin) true) I1573_seg1) (by decide) rfl I1573_fin intTest_fst
theorem link1573 : linkOK pL1573 pH1573 pI1573 = true := by decide +kernel
theorem cvx1573 : ConvexBetweenHumps 1573 :=
  cvx_of L1573_ok H1573_ok I1573_ok link1573 (by decide)

/-! ### `N = 1574` -/

def pL1574 : Prm := ⟨81, 39, 39, 1576, 11, 18446744073709551616, 119653370578305763, 119653370578305763⟩
def pH1574 : Prm := ⟨82, 40, 39, 1576, 11, 18446744073709551616, 119654470089933539, 119654470089933539⟩
def pI1574 : Prm := ⟨67, 33, 31, 1576, 11, 18446744073709551616, 119653370578305763, 119654470089933539⟩
noncomputable def L1574_cp1 : Nat × Nat := t7val% (fastRun pL1574 1 1112 (init pL1574) (init pL1574))
theorem L1574_seg1 : segOK pL1574 1 1112 (init pL1574) (init pL1574) L1574_cp1.1 L1574_cp1.2 = true := by
  decide +kernel
theorem L1574_fin : (prmOK pL1574 1574 && ptTest pL1574 (runFrom pL1574 (fmask pL1574) (cmask pL1574) (hmask pL1574) 1113 461 (true, L1574_cp1.1, L1574_cp1.2)) 1574 787 false) = true := by
  decide +kernel
theorem L1574_ok : RunOK pL1574 1574 (runFrom pL1574 (fmask pL1574) (cmask pL1574) (hmask pL1574) 1113 461 (true, L1574_cp1.1, L1574_cp1.2)) ∧ ptTest pL1574 (runFrom pL1574 (fmask pL1574) (cmask pL1574) (hmask pL1574) 1113 461 (true, L1574_cp1.1, L1574_cp1.2)) 1574 787 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1574_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1574_fin) true) L1574_seg1) (by decide) rfl L1574_fin ptTest_fst
noncomputable def H1574_cp1 : Nat × Nat := t7val% (fastRun pH1574 1 1112 (init pH1574) (init pH1574))
theorem H1574_seg1 : segOK pH1574 1 1112 (init pH1574) (init pH1574) H1574_cp1.1 H1574_cp1.2 = true := by
  decide +kernel
theorem H1574_fin : (prmOK pH1574 1574 && ptTest pH1574 (runFrom pH1574 (fmask pH1574) (cmask pH1574) (hmask pH1574) 1113 461 (true, H1574_cp1.1, H1574_cp1.2)) 1574 787 true) = true := by
  decide +kernel
theorem H1574_ok : RunOK pH1574 1574 (runFrom pH1574 (fmask pH1574) (cmask pH1574) (hmask pH1574) 1113 461 (true, H1574_cp1.1, H1574_cp1.2)) ∧ ptTest pH1574 (runFrom pH1574 (fmask pH1574) (cmask pH1574) (hmask pH1574) 1113 461 (true, H1574_cp1.1, H1574_cp1.2)) 1574 787 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1574_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1574_fin) true) H1574_seg1) (by decide) rfl H1574_fin ptTest_fst
noncomputable def I1574_cp1 : Nat × Nat := t7val% (fastRun pI1574 1 1112 (init pI1574) (init pI1574))
theorem I1574_seg1 : segOK pI1574 1 1112 (init pI1574) (init pI1574) I1574_cp1.1 I1574_cp1.2 = true := by
  decide +kernel
theorem I1574_fin : (prmOK pI1574 1574 && intTest pI1574 (runFrom pI1574 (fmask pI1574) (cmask pI1574) (hmask pI1574) 1113 461 (true, I1574_cp1.1, I1574_cp1.2)) 1574 20 true) = true := by
  decide +kernel
theorem I1574_ok : RunOK pI1574 1574 (runFrom pI1574 (fmask pI1574) (cmask pI1574) (hmask pI1574) 1113 461 (true, I1574_cp1.1, I1574_cp1.2)) ∧ intTest pI1574 (runFrom pI1574 (fmask pI1574) (cmask pI1574) (hmask pI1574) 1113 461 (true, I1574_cp1.1, I1574_cp1.2)) 1574 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1574_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1574_fin) true) I1574_seg1) (by decide) rfl I1574_fin intTest_fst
theorem link1574 : linkOK pL1574 pH1574 pI1574 = true := by decide +kernel
theorem cvx1574 : ConvexBetweenHumps 1574 :=
  cvx_of L1574_ok H1574_ok I1574_ok link1574 (by decide)
theorem cenlink1574 : cenLinkOK pI1574 1574 = true := by decide +kernel
theorem cen1574 : CenterUniqueMin 1574 ∧ DipHyp 1574 ∧ OnePointHyps 1574 :=
  cen_of L1574_ok H1574_ok I1574_ok link1574 cenlink1574

/-! ### `N = 1575` -/

def pL1575 : Prm := ⟨81, 39, 39, 1577, 11, 18446744073709551616, 119591410438246278, 119591410438246278⟩
def pH1575 : Prm := ⟨82, 40, 39, 1577, 11, 18446744073709551616, 119592509949874054, 119592509949874054⟩
def pI1575 : Prm := ⟨67, 33, 31, 1577, 11, 18446744073709551616, 119591410438246278, 119592509949874054⟩
noncomputable def L1575_cp1 : Nat × Nat := t7val% (fastRun pL1575 1 1113 (init pL1575) (init pL1575))
theorem L1575_seg1 : segOK pL1575 1 1113 (init pL1575) (init pL1575) L1575_cp1.1 L1575_cp1.2 = true := by
  decide +kernel
theorem L1575_fin : (prmOK pL1575 1575 && ptTest pL1575 (runFrom pL1575 (fmask pL1575) (cmask pL1575) (hmask pL1575) 1114 461 (true, L1575_cp1.1, L1575_cp1.2)) 1575 788 false) = true := by
  decide +kernel
theorem L1575_ok : RunOK pL1575 1575 (runFrom pL1575 (fmask pL1575) (cmask pL1575) (hmask pL1575) 1114 461 (true, L1575_cp1.1, L1575_cp1.2)) ∧ ptTest pL1575 (runFrom pL1575 (fmask pL1575) (cmask pL1575) (hmask pL1575) 1114 461 (true, L1575_cp1.1, L1575_cp1.2)) 1575 788 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1575_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1575_fin) true) L1575_seg1) (by decide) rfl L1575_fin ptTest_fst
noncomputable def H1575_cp1 : Nat × Nat := t7val% (fastRun pH1575 1 1113 (init pH1575) (init pH1575))
theorem H1575_seg1 : segOK pH1575 1 1113 (init pH1575) (init pH1575) H1575_cp1.1 H1575_cp1.2 = true := by
  decide +kernel
theorem H1575_fin : (prmOK pH1575 1575 && ptTest pH1575 (runFrom pH1575 (fmask pH1575) (cmask pH1575) (hmask pH1575) 1114 461 (true, H1575_cp1.1, H1575_cp1.2)) 1575 788 true) = true := by
  decide +kernel
theorem H1575_ok : RunOK pH1575 1575 (runFrom pH1575 (fmask pH1575) (cmask pH1575) (hmask pH1575) 1114 461 (true, H1575_cp1.1, H1575_cp1.2)) ∧ ptTest pH1575 (runFrom pH1575 (fmask pH1575) (cmask pH1575) (hmask pH1575) 1114 461 (true, H1575_cp1.1, H1575_cp1.2)) 1575 788 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1575_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1575_fin) true) H1575_seg1) (by decide) rfl H1575_fin ptTest_fst
noncomputable def I1575_cp1 : Nat × Nat := t7val% (fastRun pI1575 1 1113 (init pI1575) (init pI1575))
theorem I1575_seg1 : segOK pI1575 1 1113 (init pI1575) (init pI1575) I1575_cp1.1 I1575_cp1.2 = true := by
  decide +kernel
theorem I1575_fin : (prmOK pI1575 1575 && intTest pI1575 (runFrom pI1575 (fmask pI1575) (cmask pI1575) (hmask pI1575) 1114 461 (true, I1575_cp1.1, I1575_cp1.2)) 1575 20 false) = true := by
  decide +kernel
theorem I1575_ok : RunOK pI1575 1575 (runFrom pI1575 (fmask pI1575) (cmask pI1575) (hmask pI1575) 1114 461 (true, I1575_cp1.1, I1575_cp1.2)) ∧ intTest pI1575 (runFrom pI1575 (fmask pI1575) (cmask pI1575) (hmask pI1575) 1114 461 (true, I1575_cp1.1, I1575_cp1.2)) 1575 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1575_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1575_fin) true) I1575_seg1) (by decide) rfl I1575_fin intTest_fst
theorem link1575 : linkOK pL1575 pH1575 pI1575 = true := by decide +kernel
theorem cvx1575 : ConvexBetweenHumps 1575 :=
  cvx_of L1575_ok H1575_ok I1575_ok link1575 (by decide)

/-! ### `N = 1576` -/

def pL1576 : Prm := ⟨81, 39, 39, 1578, 11, 18446744073709551616, 119529548907692208, 119529548907692208⟩
def pH1576 : Prm := ⟨81, 39, 39, 1578, 11, 18446744073709551616, 119530648419319984, 119530648419319984⟩
def pI1576 : Prm := ⟨67, 33, 31, 1578, 11, 18446744073709551616, 119529548907692208, 119530648419319984⟩
noncomputable def L1576_cp1 : Nat × Nat := t7val% (fastRun pL1576 1 1113 (init pL1576) (init pL1576))
theorem L1576_seg1 : segOK pL1576 1 1113 (init pL1576) (init pL1576) L1576_cp1.1 L1576_cp1.2 = true := by
  decide +kernel
theorem L1576_fin : (prmOK pL1576 1576 && ptTest pL1576 (runFrom pL1576 (fmask pL1576) (cmask pL1576) (hmask pL1576) 1114 462 (true, L1576_cp1.1, L1576_cp1.2)) 1576 788 false) = true := by
  decide +kernel
theorem L1576_ok : RunOK pL1576 1576 (runFrom pL1576 (fmask pL1576) (cmask pL1576) (hmask pL1576) 1114 462 (true, L1576_cp1.1, L1576_cp1.2)) ∧ ptTest pL1576 (runFrom pL1576 (fmask pL1576) (cmask pL1576) (hmask pL1576) 1114 462 (true, L1576_cp1.1, L1576_cp1.2)) 1576 788 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1576_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1576_fin) true) L1576_seg1) (by decide) rfl L1576_fin ptTest_fst
noncomputable def H1576_cp1 : Nat × Nat := t7val% (fastRun pH1576 1 1113 (init pH1576) (init pH1576))
theorem H1576_seg1 : segOK pH1576 1 1113 (init pH1576) (init pH1576) H1576_cp1.1 H1576_cp1.2 = true := by
  decide +kernel
theorem H1576_fin : (prmOK pH1576 1576 && ptTest pH1576 (runFrom pH1576 (fmask pH1576) (cmask pH1576) (hmask pH1576) 1114 462 (true, H1576_cp1.1, H1576_cp1.2)) 1576 788 true) = true := by
  decide +kernel
theorem H1576_ok : RunOK pH1576 1576 (runFrom pH1576 (fmask pH1576) (cmask pH1576) (hmask pH1576) 1114 462 (true, H1576_cp1.1, H1576_cp1.2)) ∧ ptTest pH1576 (runFrom pH1576 (fmask pH1576) (cmask pH1576) (hmask pH1576) 1114 462 (true, H1576_cp1.1, H1576_cp1.2)) 1576 788 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1576_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1576_fin) true) H1576_seg1) (by decide) rfl H1576_fin ptTest_fst
noncomputable def I1576_cp1 : Nat × Nat := t7val% (fastRun pI1576 1 1113 (init pI1576) (init pI1576))
theorem I1576_seg1 : segOK pI1576 1 1113 (init pI1576) (init pI1576) I1576_cp1.1 I1576_cp1.2 = true := by
  decide +kernel
theorem I1576_fin : (prmOK pI1576 1576 && intTest pI1576 (runFrom pI1576 (fmask pI1576) (cmask pI1576) (hmask pI1576) 1114 462 (true, I1576_cp1.1, I1576_cp1.2)) 1576 20 true) = true := by
  decide +kernel
theorem I1576_ok : RunOK pI1576 1576 (runFrom pI1576 (fmask pI1576) (cmask pI1576) (hmask pI1576) 1114 462 (true, I1576_cp1.1, I1576_cp1.2)) ∧ intTest pI1576 (runFrom pI1576 (fmask pI1576) (cmask pI1576) (hmask pI1576) 1114 462 (true, I1576_cp1.1, I1576_cp1.2)) 1576 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1576_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1576_fin) true) I1576_seg1) (by decide) rfl I1576_fin intTest_fst
theorem link1576 : linkOK pL1576 pH1576 pI1576 = true := by decide +kernel
theorem cvx1576 : ConvexBetweenHumps 1576 :=
  cvx_of L1576_ok H1576_ok I1576_ok link1576 (by decide)
theorem cenlink1576 : cenLinkOK pI1576 1576 = true := by decide +kernel
theorem cen1576 : CenterUniqueMin 1576 ∧ DipHyp 1576 ∧ OnePointHyps 1576 :=
  cen_of L1576_ok H1576_ok I1576_ok link1576 cenlink1576

/-! ### `N = 1577` -/

def pL1577 : Prm := ⟨81, 39, 39, 1579, 11, 18446744073709551616, 119467728110205385, 119467728110205385⟩
def pH1577 : Prm := ⟨81, 39, 39, 1579, 11, 18446744073709551616, 119468827621833161, 119468827621833161⟩
def pI1577 : Prm := ⟨67, 33, 31, 1579, 11, 18446744073709551616, 119467728110205385, 119468827621833161⟩
noncomputable def L1577_cp1 : Nat × Nat := t7val% (fastRun pL1577 1 1114 (init pL1577) (init pL1577))
theorem L1577_seg1 : segOK pL1577 1 1114 (init pL1577) (init pL1577) L1577_cp1.1 L1577_cp1.2 = true := by
  decide +kernel
theorem L1577_fin : (prmOK pL1577 1577 && ptTest pL1577 (runFrom pL1577 (fmask pL1577) (cmask pL1577) (hmask pL1577) 1115 462 (true, L1577_cp1.1, L1577_cp1.2)) 1577 789 false) = true := by
  decide +kernel
theorem L1577_ok : RunOK pL1577 1577 (runFrom pL1577 (fmask pL1577) (cmask pL1577) (hmask pL1577) 1115 462 (true, L1577_cp1.1, L1577_cp1.2)) ∧ ptTest pL1577 (runFrom pL1577 (fmask pL1577) (cmask pL1577) (hmask pL1577) 1115 462 (true, L1577_cp1.1, L1577_cp1.2)) 1577 789 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1577_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1577_fin) true) L1577_seg1) (by decide) rfl L1577_fin ptTest_fst
noncomputable def H1577_cp1 : Nat × Nat := t7val% (fastRun pH1577 1 1114 (init pH1577) (init pH1577))
theorem H1577_seg1 : segOK pH1577 1 1114 (init pH1577) (init pH1577) H1577_cp1.1 H1577_cp1.2 = true := by
  decide +kernel
theorem H1577_fin : (prmOK pH1577 1577 && ptTest pH1577 (runFrom pH1577 (fmask pH1577) (cmask pH1577) (hmask pH1577) 1115 462 (true, H1577_cp1.1, H1577_cp1.2)) 1577 789 true) = true := by
  decide +kernel
theorem H1577_ok : RunOK pH1577 1577 (runFrom pH1577 (fmask pH1577) (cmask pH1577) (hmask pH1577) 1115 462 (true, H1577_cp1.1, H1577_cp1.2)) ∧ ptTest pH1577 (runFrom pH1577 (fmask pH1577) (cmask pH1577) (hmask pH1577) 1115 462 (true, H1577_cp1.1, H1577_cp1.2)) 1577 789 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1577_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1577_fin) true) H1577_seg1) (by decide) rfl H1577_fin ptTest_fst
noncomputable def I1577_cp1 : Nat × Nat := t7val% (fastRun pI1577 1 1114 (init pI1577) (init pI1577))
theorem I1577_seg1 : segOK pI1577 1 1114 (init pI1577) (init pI1577) I1577_cp1.1 I1577_cp1.2 = true := by
  decide +kernel
theorem I1577_fin : (prmOK pI1577 1577 && intTest pI1577 (runFrom pI1577 (fmask pI1577) (cmask pI1577) (hmask pI1577) 1115 462 (true, I1577_cp1.1, I1577_cp1.2)) 1577 20 false) = true := by
  decide +kernel
theorem I1577_ok : RunOK pI1577 1577 (runFrom pI1577 (fmask pI1577) (cmask pI1577) (hmask pI1577) 1115 462 (true, I1577_cp1.1, I1577_cp1.2)) ∧ intTest pI1577 (runFrom pI1577 (fmask pI1577) (cmask pI1577) (hmask pI1577) 1115 462 (true, I1577_cp1.1, I1577_cp1.2)) 1577 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1577_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1577_fin) true) I1577_seg1) (by decide) rfl I1577_fin intTest_fst
theorem link1577 : linkOK pL1577 pH1577 pI1577 = true := by decide +kernel
theorem cvx1577 : ConvexBetweenHumps 1577 :=
  cvx_of L1577_ok H1577_ok I1577_ok link1577 (by decide)

/-! ### `N = 1578` -/

def pL1578 : Prm := ⟨81, 39, 39, 1580, 11, 18446744073709551616, 119406005568286300, 119406005568286300⟩
def pH1578 : Prm := ⟨81, 39, 39, 1580, 11, 18446744073709551616, 119407105079914076, 119407105079914076⟩
def pI1578 : Prm := ⟨67, 33, 31, 1580, 11, 18446744073709551616, 119406005568286300, 119407105079914076⟩
noncomputable def L1578_cp1 : Nat × Nat := t7val% (fastRun pL1578 1 1115 (init pL1578) (init pL1578))
theorem L1578_seg1 : segOK pL1578 1 1115 (init pL1578) (init pL1578) L1578_cp1.1 L1578_cp1.2 = true := by
  decide +kernel
theorem L1578_fin : (prmOK pL1578 1578 && ptTest pL1578 (runFrom pL1578 (fmask pL1578) (cmask pL1578) (hmask pL1578) 1116 462 (true, L1578_cp1.1, L1578_cp1.2)) 1578 789 false) = true := by
  decide +kernel
theorem L1578_ok : RunOK pL1578 1578 (runFrom pL1578 (fmask pL1578) (cmask pL1578) (hmask pL1578) 1116 462 (true, L1578_cp1.1, L1578_cp1.2)) ∧ ptTest pL1578 (runFrom pL1578 (fmask pL1578) (cmask pL1578) (hmask pL1578) 1116 462 (true, L1578_cp1.1, L1578_cp1.2)) 1578 789 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1578_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1578_fin) true) L1578_seg1) (by decide) rfl L1578_fin ptTest_fst
noncomputable def H1578_cp1 : Nat × Nat := t7val% (fastRun pH1578 1 1115 (init pH1578) (init pH1578))
theorem H1578_seg1 : segOK pH1578 1 1115 (init pH1578) (init pH1578) H1578_cp1.1 H1578_cp1.2 = true := by
  decide +kernel
theorem H1578_fin : (prmOK pH1578 1578 && ptTest pH1578 (runFrom pH1578 (fmask pH1578) (cmask pH1578) (hmask pH1578) 1116 462 (true, H1578_cp1.1, H1578_cp1.2)) 1578 789 true) = true := by
  decide +kernel
theorem H1578_ok : RunOK pH1578 1578 (runFrom pH1578 (fmask pH1578) (cmask pH1578) (hmask pH1578) 1116 462 (true, H1578_cp1.1, H1578_cp1.2)) ∧ ptTest pH1578 (runFrom pH1578 (fmask pH1578) (cmask pH1578) (hmask pH1578) 1116 462 (true, H1578_cp1.1, H1578_cp1.2)) 1578 789 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1578_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1578_fin) true) H1578_seg1) (by decide) rfl H1578_fin ptTest_fst
noncomputable def I1578_cp1 : Nat × Nat := t7val% (fastRun pI1578 1 1115 (init pI1578) (init pI1578))
theorem I1578_seg1 : segOK pI1578 1 1115 (init pI1578) (init pI1578) I1578_cp1.1 I1578_cp1.2 = true := by
  decide +kernel
theorem I1578_fin : (prmOK pI1578 1578 && intTest pI1578 (runFrom pI1578 (fmask pI1578) (cmask pI1578) (hmask pI1578) 1116 462 (true, I1578_cp1.1, I1578_cp1.2)) 1578 20 true) = true := by
  decide +kernel
theorem I1578_ok : RunOK pI1578 1578 (runFrom pI1578 (fmask pI1578) (cmask pI1578) (hmask pI1578) 1116 462 (true, I1578_cp1.1, I1578_cp1.2)) ∧ intTest pI1578 (runFrom pI1578 (fmask pI1578) (cmask pI1578) (hmask pI1578) 1116 462 (true, I1578_cp1.1, I1578_cp1.2)) 1578 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1578_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1578_fin) true) I1578_seg1) (by decide) rfl I1578_fin intTest_fst
theorem link1578 : linkOK pL1578 pH1578 pI1578 = true := by decide +kernel
theorem cvx1578 : ConvexBetweenHumps 1578 :=
  cvx_of L1578_ok H1578_ok I1578_ok link1578 (by decide)
theorem cenlink1578 : cenLinkOK pI1578 1578 = true := by decide +kernel
theorem cen1578 : CenterUniqueMin 1578 ∧ DipHyp 1578 ∧ OnePointHyps 1578 :=
  cen_of L1578_ok H1578_ok I1578_ok link1578 cenlink1578

/-! ### The range -/

theorem cvx_1563_1578 {N : ℕ} (h1 : 1563 ≤ N) (h2 : N ≤ 1578) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1570
  · by_cases h4 : N ≤ 1566
    · by_cases h6 : N ≤ 1564
      · by_cases h8 : N ≤ 1563
        · obtain rfl : N = 1563 := by omega
          exact cvx1563
        · obtain rfl : N = 1564 := by omega
          exact cvx1564
      · by_cases h8 : N ≤ 1565
        · obtain rfl : N = 1565 := by omega
          exact cvx1565
        · obtain rfl : N = 1566 := by omega
          exact cvx1566
    · by_cases h6 : N ≤ 1568
      · by_cases h8 : N ≤ 1567
        · obtain rfl : N = 1567 := by omega
          exact cvx1567
        · obtain rfl : N = 1568 := by omega
          exact cvx1568
      · by_cases h8 : N ≤ 1569
        · obtain rfl : N = 1569 := by omega
          exact cvx1569
        · obtain rfl : N = 1570 := by omega
          exact cvx1570
  · by_cases h4 : N ≤ 1574
    · by_cases h6 : N ≤ 1572
      · by_cases h8 : N ≤ 1571
        · obtain rfl : N = 1571 := by omega
          exact cvx1571
        · obtain rfl : N = 1572 := by omega
          exact cvx1572
      · by_cases h8 : N ≤ 1573
        · obtain rfl : N = 1573 := by omega
          exact cvx1573
        · obtain rfl : N = 1574 := by omega
          exact cvx1574
    · by_cases h6 : N ≤ 1576
      · by_cases h8 : N ≤ 1575
        · obtain rfl : N = 1575 := by omega
          exact cvx1575
        · obtain rfl : N = 1576 := by omega
          exact cvx1576
      · by_cases h8 : N ≤ 1577
        · obtain rfl : N = 1577 := by omega
          exact cvx1577
        · obtain rfl : N = 1578 := by omega
          exact cvx1578

theorem cen_1563_1578 {N : ℕ} (h1 : 1563 ≤ N) (h2 : N ≤ 1578) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1570
  · by_cases h4 : N ≤ 1566
    · by_cases h6 : N ≤ 1564
      · obtain rfl : N = 1564 := by omega
        exact cen1564
      · obtain rfl : N = 1566 := by omega
        exact cen1566
    · by_cases h6 : N ≤ 1568
      · obtain rfl : N = 1568 := by omega
        exact cen1568
      · obtain rfl : N = 1570 := by omega
        exact cen1570
  · by_cases h4 : N ≤ 1574
    · by_cases h6 : N ≤ 1572
      · obtain rfl : N = 1572 := by omega
        exact cen1572
      · obtain rfl : N = 1574 := by omega
        exact cen1574
    · by_cases h6 : N ≤ 1576
      · obtain rfl : N = 1576 := by omega
        exact cen1576
      · obtain rfl : N = 1578 := by omega
        exact cen1578

end Kagey131.PaperD.T7
