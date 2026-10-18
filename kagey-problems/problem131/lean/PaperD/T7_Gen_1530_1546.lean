import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1530, …, 1546` (generated)

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

/-! ### `N = 1530` -/

def pL1530 : Prm := ⟨80, 38, 39, 1532, 11, 18446744073709551616, 122449881821766250, 122449881821766250⟩
def pH1530 : Prm := ⟨81, 39, 39, 1532, 11, 18446744073709551616, 122450981333394026, 122450981333394026⟩
def pI1530 : Prm := ⟨66, 33, 30, 1532, 11, 18446744073709551616, 122449881821766250, 122450981333394026⟩
noncomputable def L1530_cp1 : Nat × Nat := t7val% (fastRun pL1530 1 1081 (init pL1530) (init pL1530))
theorem L1530_seg1 : segOK pL1530 1 1081 (init pL1530) (init pL1530) L1530_cp1.1 L1530_cp1.2 = true := by
  decide +kernel
theorem L1530_fin : (prmOK pL1530 1530 && ptTest pL1530 (runFrom pL1530 (fmask pL1530) (cmask pL1530) (hmask pL1530) 1082 448 (true, L1530_cp1.1, L1530_cp1.2)) 1530 765 false) = true := by
  decide +kernel
theorem L1530_ok : RunOK pL1530 1530 (runFrom pL1530 (fmask pL1530) (cmask pL1530) (hmask pL1530) 1082 448 (true, L1530_cp1.1, L1530_cp1.2)) ∧ ptTest pL1530 (runFrom pL1530 (fmask pL1530) (cmask pL1530) (hmask pL1530) 1082 448 (true, L1530_cp1.1, L1530_cp1.2)) 1530 765 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1530_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1530_fin) true) L1530_seg1) (by decide) rfl L1530_fin ptTest_fst
noncomputable def H1530_cp1 : Nat × Nat := t7val% (fastRun pH1530 1 1081 (init pH1530) (init pH1530))
theorem H1530_seg1 : segOK pH1530 1 1081 (init pH1530) (init pH1530) H1530_cp1.1 H1530_cp1.2 = true := by
  decide +kernel
theorem H1530_fin : (prmOK pH1530 1530 && ptTest pH1530 (runFrom pH1530 (fmask pH1530) (cmask pH1530) (hmask pH1530) 1082 448 (true, H1530_cp1.1, H1530_cp1.2)) 1530 765 true) = true := by
  decide +kernel
theorem H1530_ok : RunOK pH1530 1530 (runFrom pH1530 (fmask pH1530) (cmask pH1530) (hmask pH1530) 1082 448 (true, H1530_cp1.1, H1530_cp1.2)) ∧ ptTest pH1530 (runFrom pH1530 (fmask pH1530) (cmask pH1530) (hmask pH1530) 1082 448 (true, H1530_cp1.1, H1530_cp1.2)) 1530 765 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1530_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1530_fin) true) H1530_seg1) (by decide) rfl H1530_fin ptTest_fst
noncomputable def I1530_cp1 : Nat × Nat := t7val% (fastRun pI1530 1 1081 (init pI1530) (init pI1530))
theorem I1530_seg1 : segOK pI1530 1 1081 (init pI1530) (init pI1530) I1530_cp1.1 I1530_cp1.2 = true := by
  decide +kernel
theorem I1530_fin : (prmOK pI1530 1530 && intTest pI1530 (runFrom pI1530 (fmask pI1530) (cmask pI1530) (hmask pI1530) 1082 448 (true, I1530_cp1.1, I1530_cp1.2)) 1530 20 true) = true := by
  decide +kernel
theorem I1530_ok : RunOK pI1530 1530 (runFrom pI1530 (fmask pI1530) (cmask pI1530) (hmask pI1530) 1082 448 (true, I1530_cp1.1, I1530_cp1.2)) ∧ intTest pI1530 (runFrom pI1530 (fmask pI1530) (cmask pI1530) (hmask pI1530) 1082 448 (true, I1530_cp1.1, I1530_cp1.2)) 1530 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1530_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1530_fin) true) I1530_seg1) (by decide) rfl I1530_fin intTest_fst
theorem link1530 : linkOK pL1530 pH1530 pI1530 = true := by decide +kernel
theorem cvx1530 : ConvexBetweenHumps 1530 :=
  cvx_of L1530_ok H1530_ok I1530_ok link1530 (by decide)
theorem cenlink1530 : cenLinkOK pI1530 1530 = true := by decide +kernel
theorem cen1530 : CenterUniqueMin 1530 ∧ DipHyp 1530 ∧ OnePointHyps 1530 :=
  cen_of L1530_ok H1530_ok I1530_ok link1530 cenlink1530

/-! ### `N = 1531` -/

def pL1531 : Prm := ⟨80, 38, 39, 1533, 11, 18446744073709551616, 122384728804263931, 122384728804263931⟩
def pH1531 : Prm := ⟨81, 39, 39, 1533, 11, 18446744073709551616, 122385828315891707, 122385828315891707⟩
def pI1531 : Prm := ⟨66, 33, 30, 1533, 11, 18446744073709551616, 122384728804263931, 122385828315891707⟩
noncomputable def L1531_cp1 : Nat × Nat := t7val% (fastRun pL1531 1 1082 (init pL1531) (init pL1531))
theorem L1531_seg1 : segOK pL1531 1 1082 (init pL1531) (init pL1531) L1531_cp1.1 L1531_cp1.2 = true := by
  decide +kernel
theorem L1531_fin : (prmOK pL1531 1531 && ptTest pL1531 (runFrom pL1531 (fmask pL1531) (cmask pL1531) (hmask pL1531) 1083 448 (true, L1531_cp1.1, L1531_cp1.2)) 1531 766 false) = true := by
  decide +kernel
theorem L1531_ok : RunOK pL1531 1531 (runFrom pL1531 (fmask pL1531) (cmask pL1531) (hmask pL1531) 1083 448 (true, L1531_cp1.1, L1531_cp1.2)) ∧ ptTest pL1531 (runFrom pL1531 (fmask pL1531) (cmask pL1531) (hmask pL1531) 1083 448 (true, L1531_cp1.1, L1531_cp1.2)) 1531 766 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1531_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1531_fin) true) L1531_seg1) (by decide) rfl L1531_fin ptTest_fst
noncomputable def H1531_cp1 : Nat × Nat := t7val% (fastRun pH1531 1 1082 (init pH1531) (init pH1531))
theorem H1531_seg1 : segOK pH1531 1 1082 (init pH1531) (init pH1531) H1531_cp1.1 H1531_cp1.2 = true := by
  decide +kernel
theorem H1531_fin : (prmOK pH1531 1531 && ptTest pH1531 (runFrom pH1531 (fmask pH1531) (cmask pH1531) (hmask pH1531) 1083 448 (true, H1531_cp1.1, H1531_cp1.2)) 1531 766 true) = true := by
  decide +kernel
theorem H1531_ok : RunOK pH1531 1531 (runFrom pH1531 (fmask pH1531) (cmask pH1531) (hmask pH1531) 1083 448 (true, H1531_cp1.1, H1531_cp1.2)) ∧ ptTest pH1531 (runFrom pH1531 (fmask pH1531) (cmask pH1531) (hmask pH1531) 1083 448 (true, H1531_cp1.1, H1531_cp1.2)) 1531 766 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1531_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1531_fin) true) H1531_seg1) (by decide) rfl H1531_fin ptTest_fst
noncomputable def I1531_cp1 : Nat × Nat := t7val% (fastRun pI1531 1 1082 (init pI1531) (init pI1531))
theorem I1531_seg1 : segOK pI1531 1 1082 (init pI1531) (init pI1531) I1531_cp1.1 I1531_cp1.2 = true := by
  decide +kernel
theorem I1531_fin : (prmOK pI1531 1531 && intTest pI1531 (runFrom pI1531 (fmask pI1531) (cmask pI1531) (hmask pI1531) 1083 448 (true, I1531_cp1.1, I1531_cp1.2)) 1531 20 false) = true := by
  decide +kernel
theorem I1531_ok : RunOK pI1531 1531 (runFrom pI1531 (fmask pI1531) (cmask pI1531) (hmask pI1531) 1083 448 (true, I1531_cp1.1, I1531_cp1.2)) ∧ intTest pI1531 (runFrom pI1531 (fmask pI1531) (cmask pI1531) (hmask pI1531) 1083 448 (true, I1531_cp1.1, I1531_cp1.2)) 1531 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1531_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1531_fin) true) I1531_seg1) (by decide) rfl I1531_fin intTest_fst
theorem link1531 : linkOK pL1531 pH1531 pI1531 = true := by decide +kernel
theorem cvx1531 : ConvexBetweenHumps 1531 :=
  cvx_of L1531_ok H1531_ok I1531_ok link1531 (by decide)

/-! ### `N = 1532` -/

def pL1532 : Prm := ⟨80, 38, 39, 1534, 11, 18446744073709551616, 122319682637884900, 122319682637884900⟩
def pH1532 : Prm := ⟨80, 38, 39, 1534, 11, 18446744073709551616, 122320782149512676, 122320782149512676⟩
def pI1532 : Prm := ⟨66, 33, 30, 1534, 11, 18446744073709551616, 122319682637884900, 122320782149512676⟩
noncomputable def L1532_cp1 : Nat × Nat := t7val% (fastRun pL1532 1 1082 (init pL1532) (init pL1532))
theorem L1532_seg1 : segOK pL1532 1 1082 (init pL1532) (init pL1532) L1532_cp1.1 L1532_cp1.2 = true := by
  decide +kernel
theorem L1532_fin : (prmOK pL1532 1532 && ptTest pL1532 (runFrom pL1532 (fmask pL1532) (cmask pL1532) (hmask pL1532) 1083 449 (true, L1532_cp1.1, L1532_cp1.2)) 1532 766 false) = true := by
  decide +kernel
theorem L1532_ok : RunOK pL1532 1532 (runFrom pL1532 (fmask pL1532) (cmask pL1532) (hmask pL1532) 1083 449 (true, L1532_cp1.1, L1532_cp1.2)) ∧ ptTest pL1532 (runFrom pL1532 (fmask pL1532) (cmask pL1532) (hmask pL1532) 1083 449 (true, L1532_cp1.1, L1532_cp1.2)) 1532 766 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1532_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1532_fin) true) L1532_seg1) (by decide) rfl L1532_fin ptTest_fst
noncomputable def H1532_cp1 : Nat × Nat := t7val% (fastRun pH1532 1 1082 (init pH1532) (init pH1532))
theorem H1532_seg1 : segOK pH1532 1 1082 (init pH1532) (init pH1532) H1532_cp1.1 H1532_cp1.2 = true := by
  decide +kernel
theorem H1532_fin : (prmOK pH1532 1532 && ptTest pH1532 (runFrom pH1532 (fmask pH1532) (cmask pH1532) (hmask pH1532) 1083 449 (true, H1532_cp1.1, H1532_cp1.2)) 1532 766 true) = true := by
  decide +kernel
theorem H1532_ok : RunOK pH1532 1532 (runFrom pH1532 (fmask pH1532) (cmask pH1532) (hmask pH1532) 1083 449 (true, H1532_cp1.1, H1532_cp1.2)) ∧ ptTest pH1532 (runFrom pH1532 (fmask pH1532) (cmask pH1532) (hmask pH1532) 1083 449 (true, H1532_cp1.1, H1532_cp1.2)) 1532 766 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1532_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1532_fin) true) H1532_seg1) (by decide) rfl H1532_fin ptTest_fst
noncomputable def I1532_cp1 : Nat × Nat := t7val% (fastRun pI1532 1 1082 (init pI1532) (init pI1532))
theorem I1532_seg1 : segOK pI1532 1 1082 (init pI1532) (init pI1532) I1532_cp1.1 I1532_cp1.2 = true := by
  decide +kernel
theorem I1532_fin : (prmOK pI1532 1532 && intTest pI1532 (runFrom pI1532 (fmask pI1532) (cmask pI1532) (hmask pI1532) 1083 449 (true, I1532_cp1.1, I1532_cp1.2)) 1532 20 true) = true := by
  decide +kernel
theorem I1532_ok : RunOK pI1532 1532 (runFrom pI1532 (fmask pI1532) (cmask pI1532) (hmask pI1532) 1083 449 (true, I1532_cp1.1, I1532_cp1.2)) ∧ intTest pI1532 (runFrom pI1532 (fmask pI1532) (cmask pI1532) (hmask pI1532) 1083 449 (true, I1532_cp1.1, I1532_cp1.2)) 1532 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1532_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1532_fin) true) I1532_seg1) (by decide) rfl I1532_fin intTest_fst
theorem link1532 : linkOK pL1532 pH1532 pI1532 = true := by decide +kernel
theorem cvx1532 : ConvexBetweenHumps 1532 :=
  cvx_of L1532_ok H1532_ok I1532_ok link1532 (by decide)
theorem cenlink1532 : cenLinkOK pI1532 1532 = true := by decide +kernel
theorem cen1532 : CenterUniqueMin 1532 ∧ DipHyp 1532 ∧ OnePointHyps 1532 :=
  cen_of L1532_ok H1532_ok I1532_ok link1532 cenlink1532

/-! ### `N = 1533` -/

def pL1533 : Prm := ⟨81, 39, 39, 1535, 11, 18446744073709551616, 122254680224876967, 122254680224876967⟩
def pH1533 : Prm := ⟨81, 39, 39, 1535, 11, 18446744073709551616, 122255779736504743, 122255779736504743⟩
def pI1533 : Prm := ⟨66, 33, 30, 1535, 11, 18446744073709551616, 122254680224876967, 122255779736504743⟩
noncomputable def L1533_cp1 : Nat × Nat := t7val% (fastRun pL1533 1 1083 (init pL1533) (init pL1533))
theorem L1533_seg1 : segOK pL1533 1 1083 (init pL1533) (init pL1533) L1533_cp1.1 L1533_cp1.2 = true := by
  decide +kernel
theorem L1533_fin : (prmOK pL1533 1533 && ptTest pL1533 (runFrom pL1533 (fmask pL1533) (cmask pL1533) (hmask pL1533) 1084 449 (true, L1533_cp1.1, L1533_cp1.2)) 1533 767 false) = true := by
  decide +kernel
theorem L1533_ok : RunOK pL1533 1533 (runFrom pL1533 (fmask pL1533) (cmask pL1533) (hmask pL1533) 1084 449 (true, L1533_cp1.1, L1533_cp1.2)) ∧ ptTest pL1533 (runFrom pL1533 (fmask pL1533) (cmask pL1533) (hmask pL1533) 1084 449 (true, L1533_cp1.1, L1533_cp1.2)) 1533 767 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1533_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1533_fin) true) L1533_seg1) (by decide) rfl L1533_fin ptTest_fst
noncomputable def H1533_cp1 : Nat × Nat := t7val% (fastRun pH1533 1 1083 (init pH1533) (init pH1533))
theorem H1533_seg1 : segOK pH1533 1 1083 (init pH1533) (init pH1533) H1533_cp1.1 H1533_cp1.2 = true := by
  decide +kernel
theorem H1533_fin : (prmOK pH1533 1533 && ptTest pH1533 (runFrom pH1533 (fmask pH1533) (cmask pH1533) (hmask pH1533) 1084 449 (true, H1533_cp1.1, H1533_cp1.2)) 1533 767 true) = true := by
  decide +kernel
theorem H1533_ok : RunOK pH1533 1533 (runFrom pH1533 (fmask pH1533) (cmask pH1533) (hmask pH1533) 1084 449 (true, H1533_cp1.1, H1533_cp1.2)) ∧ ptTest pH1533 (runFrom pH1533 (fmask pH1533) (cmask pH1533) (hmask pH1533) 1084 449 (true, H1533_cp1.1, H1533_cp1.2)) 1533 767 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1533_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1533_fin) true) H1533_seg1) (by decide) rfl H1533_fin ptTest_fst
noncomputable def I1533_cp1 : Nat × Nat := t7val% (fastRun pI1533 1 1083 (init pI1533) (init pI1533))
theorem I1533_seg1 : segOK pI1533 1 1083 (init pI1533) (init pI1533) I1533_cp1.1 I1533_cp1.2 = true := by
  decide +kernel
theorem I1533_fin : (prmOK pI1533 1533 && intTest pI1533 (runFrom pI1533 (fmask pI1533) (cmask pI1533) (hmask pI1533) 1084 449 (true, I1533_cp1.1, I1533_cp1.2)) 1533 20 false) = true := by
  decide +kernel
theorem I1533_ok : RunOK pI1533 1533 (runFrom pI1533 (fmask pI1533) (cmask pI1533) (hmask pI1533) 1084 449 (true, I1533_cp1.1, I1533_cp1.2)) ∧ intTest pI1533 (runFrom pI1533 (fmask pI1533) (cmask pI1533) (hmask pI1533) 1084 449 (true, I1533_cp1.1, I1533_cp1.2)) 1533 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1533_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1533_fin) true) I1533_seg1) (by decide) rfl I1533_fin intTest_fst
theorem link1533 : linkOK pL1533 pH1533 pI1533 = true := by decide +kernel
theorem cvx1533 : ConvexBetweenHumps 1533 :=
  cvx_of L1533_ok H1533_ok I1533_ok link1533 (by decide)

/-! ### `N = 1534` -/

def pL1534 : Prm := ⟨81, 39, 39, 1536, 11, 18446744073709551616, 122189784268582487, 122189784268582487⟩
def pH1534 : Prm := ⟨81, 39, 39, 1536, 11, 18446744073709551616, 122190883780210263, 122190883780210263⟩
def pI1534 : Prm := ⟨66, 33, 30, 1536, 11, 18446744073709551616, 122189784268582487, 122190883780210263⟩
noncomputable def L1534_cp1 : Nat × Nat := t7val% (fastRun pL1534 1 1084 (init pL1534) (init pL1534))
theorem L1534_seg1 : segOK pL1534 1 1084 (init pL1534) (init pL1534) L1534_cp1.1 L1534_cp1.2 = true := by
  decide +kernel
theorem L1534_fin : (prmOK pL1534 1534 && ptTest pL1534 (runFrom pL1534 (fmask pL1534) (cmask pL1534) (hmask pL1534) 1085 449 (true, L1534_cp1.1, L1534_cp1.2)) 1534 767 false) = true := by
  decide +kernel
theorem L1534_ok : RunOK pL1534 1534 (runFrom pL1534 (fmask pL1534) (cmask pL1534) (hmask pL1534) 1085 449 (true, L1534_cp1.1, L1534_cp1.2)) ∧ ptTest pL1534 (runFrom pL1534 (fmask pL1534) (cmask pL1534) (hmask pL1534) 1085 449 (true, L1534_cp1.1, L1534_cp1.2)) 1534 767 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1534_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1534_fin) true) L1534_seg1) (by decide) rfl L1534_fin ptTest_fst
noncomputable def H1534_cp1 : Nat × Nat := t7val% (fastRun pH1534 1 1084 (init pH1534) (init pH1534))
theorem H1534_seg1 : segOK pH1534 1 1084 (init pH1534) (init pH1534) H1534_cp1.1 H1534_cp1.2 = true := by
  decide +kernel
theorem H1534_fin : (prmOK pH1534 1534 && ptTest pH1534 (runFrom pH1534 (fmask pH1534) (cmask pH1534) (hmask pH1534) 1085 449 (true, H1534_cp1.1, H1534_cp1.2)) 1534 767 true) = true := by
  decide +kernel
theorem H1534_ok : RunOK pH1534 1534 (runFrom pH1534 (fmask pH1534) (cmask pH1534) (hmask pH1534) 1085 449 (true, H1534_cp1.1, H1534_cp1.2)) ∧ ptTest pH1534 (runFrom pH1534 (fmask pH1534) (cmask pH1534) (hmask pH1534) 1085 449 (true, H1534_cp1.1, H1534_cp1.2)) 1534 767 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1534_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1534_fin) true) H1534_seg1) (by decide) rfl H1534_fin ptTest_fst
noncomputable def I1534_cp1 : Nat × Nat := t7val% (fastRun pI1534 1 1084 (init pI1534) (init pI1534))
theorem I1534_seg1 : segOK pI1534 1 1084 (init pI1534) (init pI1534) I1534_cp1.1 I1534_cp1.2 = true := by
  decide +kernel
theorem I1534_fin : (prmOK pI1534 1534 && intTest pI1534 (runFrom pI1534 (fmask pI1534) (cmask pI1534) (hmask pI1534) 1085 449 (true, I1534_cp1.1, I1534_cp1.2)) 1534 20 true) = true := by
  decide +kernel
theorem I1534_ok : RunOK pI1534 1534 (runFrom pI1534 (fmask pI1534) (cmask pI1534) (hmask pI1534) 1085 449 (true, I1534_cp1.1, I1534_cp1.2)) ∧ intTest pI1534 (runFrom pI1534 (fmask pI1534) (cmask pI1534) (hmask pI1534) 1085 449 (true, I1534_cp1.1, I1534_cp1.2)) 1534 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1534_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1534_fin) true) I1534_seg1) (by decide) rfl I1534_fin intTest_fst
theorem link1534 : linkOK pL1534 pH1534 pI1534 = true := by decide +kernel
theorem cvx1534 : ConvexBetweenHumps 1534 :=
  cvx_of L1534_ok H1534_ok I1534_ok link1534 (by decide)
theorem cenlink1534 : cenLinkOK pI1534 1534 = true := by decide +kernel
theorem cen1534 : CenterUniqueMin 1534 ∧ DipHyp 1534 ∧ OnePointHyps 1534 :=
  cen_of L1534_ok H1534_ok I1534_ok link1534 cenlink1534

/-! ### `N = 1535` -/

def pL1535 : Prm := ⟨80, 38, 39, 1537, 11, 18446744073709551616, 122124931921903630, 122124931921903630⟩
def pH1535 : Prm := ⟨81, 39, 39, 1537, 11, 18446744073709551616, 122126031433531406, 122126031433531406⟩
def pI1535 : Prm := ⟨66, 33, 30, 1537, 11, 18446744073709551616, 122124931921903630, 122126031433531406⟩
noncomputable def L1535_cp1 : Nat × Nat := t7val% (fastRun pL1535 1 1084 (init pL1535) (init pL1535))
theorem L1535_seg1 : segOK pL1535 1 1084 (init pL1535) (init pL1535) L1535_cp1.1 L1535_cp1.2 = true := by
  decide +kernel
theorem L1535_fin : (prmOK pL1535 1535 && ptTest pL1535 (runFrom pL1535 (fmask pL1535) (cmask pL1535) (hmask pL1535) 1085 450 (true, L1535_cp1.1, L1535_cp1.2)) 1535 768 false) = true := by
  decide +kernel
theorem L1535_ok : RunOK pL1535 1535 (runFrom pL1535 (fmask pL1535) (cmask pL1535) (hmask pL1535) 1085 450 (true, L1535_cp1.1, L1535_cp1.2)) ∧ ptTest pL1535 (runFrom pL1535 (fmask pL1535) (cmask pL1535) (hmask pL1535) 1085 450 (true, L1535_cp1.1, L1535_cp1.2)) 1535 768 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1535_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1535_fin) true) L1535_seg1) (by decide) rfl L1535_fin ptTest_fst
noncomputable def H1535_cp1 : Nat × Nat := t7val% (fastRun pH1535 1 1084 (init pH1535) (init pH1535))
theorem H1535_seg1 : segOK pH1535 1 1084 (init pH1535) (init pH1535) H1535_cp1.1 H1535_cp1.2 = true := by
  decide +kernel
theorem H1535_fin : (prmOK pH1535 1535 && ptTest pH1535 (runFrom pH1535 (fmask pH1535) (cmask pH1535) (hmask pH1535) 1085 450 (true, H1535_cp1.1, H1535_cp1.2)) 1535 768 true) = true := by
  decide +kernel
theorem H1535_ok : RunOK pH1535 1535 (runFrom pH1535 (fmask pH1535) (cmask pH1535) (hmask pH1535) 1085 450 (true, H1535_cp1.1, H1535_cp1.2)) ∧ ptTest pH1535 (runFrom pH1535 (fmask pH1535) (cmask pH1535) (hmask pH1535) 1085 450 (true, H1535_cp1.1, H1535_cp1.2)) 1535 768 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1535_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1535_fin) true) H1535_seg1) (by decide) rfl H1535_fin ptTest_fst
noncomputable def I1535_cp1 : Nat × Nat := t7val% (fastRun pI1535 1 1084 (init pI1535) (init pI1535))
theorem I1535_seg1 : segOK pI1535 1 1084 (init pI1535) (init pI1535) I1535_cp1.1 I1535_cp1.2 = true := by
  decide +kernel
theorem I1535_fin : (prmOK pI1535 1535 && intTest pI1535 (runFrom pI1535 (fmask pI1535) (cmask pI1535) (hmask pI1535) 1085 450 (true, I1535_cp1.1, I1535_cp1.2)) 1535 20 false) = true := by
  decide +kernel
theorem I1535_ok : RunOK pI1535 1535 (runFrom pI1535 (fmask pI1535) (cmask pI1535) (hmask pI1535) 1085 450 (true, I1535_cp1.1, I1535_cp1.2)) ∧ intTest pI1535 (runFrom pI1535 (fmask pI1535) (cmask pI1535) (hmask pI1535) 1085 450 (true, I1535_cp1.1, I1535_cp1.2)) 1535 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1535_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1535_fin) true) I1535_seg1) (by decide) rfl I1535_fin intTest_fst
theorem link1535 : linkOK pL1535 pH1535 pI1535 = true := by decide +kernel
theorem cvx1535 : ConvexBetweenHumps 1535 :=
  cvx_of L1535_ok H1535_ok I1535_ok link1535 (by decide)

/-! ### `N = 1536` -/

def pL1536 : Prm := ⟨80, 38, 39, 1538, 11, 18446744073709551616, 122060185639502191, 122060185639502191⟩
def pH1536 : Prm := ⟨80, 38, 39, 1538, 11, 18446744073709551616, 122061285151129967, 122061285151129967⟩
def pI1536 : Prm := ⟨66, 33, 30, 1538, 11, 18446744073709551616, 122060185639502191, 122061285151129967⟩
noncomputable def L1536_cp1 : Nat × Nat := t7val% (fastRun pL1536 1 1085 (init pL1536) (init pL1536))
theorem L1536_seg1 : segOK pL1536 1 1085 (init pL1536) (init pL1536) L1536_cp1.1 L1536_cp1.2 = true := by
  decide +kernel
theorem L1536_fin : (prmOK pL1536 1536 && ptTest pL1536 (runFrom pL1536 (fmask pL1536) (cmask pL1536) (hmask pL1536) 1086 450 (true, L1536_cp1.1, L1536_cp1.2)) 1536 768 false) = true := by
  decide +kernel
theorem L1536_ok : RunOK pL1536 1536 (runFrom pL1536 (fmask pL1536) (cmask pL1536) (hmask pL1536) 1086 450 (true, L1536_cp1.1, L1536_cp1.2)) ∧ ptTest pL1536 (runFrom pL1536 (fmask pL1536) (cmask pL1536) (hmask pL1536) 1086 450 (true, L1536_cp1.1, L1536_cp1.2)) 1536 768 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1536_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1536_fin) true) L1536_seg1) (by decide) rfl L1536_fin ptTest_fst
noncomputable def H1536_cp1 : Nat × Nat := t7val% (fastRun pH1536 1 1085 (init pH1536) (init pH1536))
theorem H1536_seg1 : segOK pH1536 1 1085 (init pH1536) (init pH1536) H1536_cp1.1 H1536_cp1.2 = true := by
  decide +kernel
theorem H1536_fin : (prmOK pH1536 1536 && ptTest pH1536 (runFrom pH1536 (fmask pH1536) (cmask pH1536) (hmask pH1536) 1086 450 (true, H1536_cp1.1, H1536_cp1.2)) 1536 768 true) = true := by
  decide +kernel
theorem H1536_ok : RunOK pH1536 1536 (runFrom pH1536 (fmask pH1536) (cmask pH1536) (hmask pH1536) 1086 450 (true, H1536_cp1.1, H1536_cp1.2)) ∧ ptTest pH1536 (runFrom pH1536 (fmask pH1536) (cmask pH1536) (hmask pH1536) 1086 450 (true, H1536_cp1.1, H1536_cp1.2)) 1536 768 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1536_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1536_fin) true) H1536_seg1) (by decide) rfl H1536_fin ptTest_fst
noncomputable def I1536_cp1 : Nat × Nat := t7val% (fastRun pI1536 1 1085 (init pI1536) (init pI1536))
theorem I1536_seg1 : segOK pI1536 1 1085 (init pI1536) (init pI1536) I1536_cp1.1 I1536_cp1.2 = true := by
  decide +kernel
theorem I1536_fin : (prmOK pI1536 1536 && intTest pI1536 (runFrom pI1536 (fmask pI1536) (cmask pI1536) (hmask pI1536) 1086 450 (true, I1536_cp1.1, I1536_cp1.2)) 1536 20 true) = true := by
  decide +kernel
theorem I1536_ok : RunOK pI1536 1536 (runFrom pI1536 (fmask pI1536) (cmask pI1536) (hmask pI1536) 1086 450 (true, I1536_cp1.1, I1536_cp1.2)) ∧ intTest pI1536 (runFrom pI1536 (fmask pI1536) (cmask pI1536) (hmask pI1536) 1086 450 (true, I1536_cp1.1, I1536_cp1.2)) 1536 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1536_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1536_fin) true) I1536_seg1) (by decide) rfl I1536_fin intTest_fst
theorem link1536 : linkOK pL1536 pH1536 pI1536 = true := by decide +kernel
theorem cvx1536 : ConvexBetweenHumps 1536 :=
  cvx_of L1536_ok H1536_ok I1536_ok link1536 (by decide)
theorem cenlink1536 : cenLinkOK pI1536 1536 = true := by decide +kernel
theorem cen1536 : CenterUniqueMin 1536 ∧ DipHyp 1536 ∧ OnePointHyps 1536 :=
  cen_of L1536_ok H1536_ok I1536_ok link1536 cenlink1536

/-! ### `N = 1537` -/

def pL1537 : Prm := ⟨81, 39, 39, 1539, 11, 18446744073709551616, 121995482823569641, 121995482823569641⟩
def pH1537 : Prm := ⟨81, 39, 39, 1539, 11, 18446744073709551616, 121996582335197417, 121996582335197417⟩
def pI1537 : Prm := ⟨66, 33, 30, 1539, 11, 18446744073709551616, 121995482823569641, 121996582335197417⟩
noncomputable def L1537_cp1 : Nat × Nat := t7val% (fastRun pL1537 1 1086 (init pL1537) (init pL1537))
theorem L1537_seg1 : segOK pL1537 1 1086 (init pL1537) (init pL1537) L1537_cp1.1 L1537_cp1.2 = true := by
  decide +kernel
theorem L1537_fin : (prmOK pL1537 1537 && ptTest pL1537 (runFrom pL1537 (fmask pL1537) (cmask pL1537) (hmask pL1537) 1087 450 (true, L1537_cp1.1, L1537_cp1.2)) 1537 769 false) = true := by
  decide +kernel
theorem L1537_ok : RunOK pL1537 1537 (runFrom pL1537 (fmask pL1537) (cmask pL1537) (hmask pL1537) 1087 450 (true, L1537_cp1.1, L1537_cp1.2)) ∧ ptTest pL1537 (runFrom pL1537 (fmask pL1537) (cmask pL1537) (hmask pL1537) 1087 450 (true, L1537_cp1.1, L1537_cp1.2)) 1537 769 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1537_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1537_fin) true) L1537_seg1) (by decide) rfl L1537_fin ptTest_fst
noncomputable def H1537_cp1 : Nat × Nat := t7val% (fastRun pH1537 1 1086 (init pH1537) (init pH1537))
theorem H1537_seg1 : segOK pH1537 1 1086 (init pH1537) (init pH1537) H1537_cp1.1 H1537_cp1.2 = true := by
  decide +kernel
theorem H1537_fin : (prmOK pH1537 1537 && ptTest pH1537 (runFrom pH1537 (fmask pH1537) (cmask pH1537) (hmask pH1537) 1087 450 (true, H1537_cp1.1, H1537_cp1.2)) 1537 769 true) = true := by
  decide +kernel
theorem H1537_ok : RunOK pH1537 1537 (runFrom pH1537 (fmask pH1537) (cmask pH1537) (hmask pH1537) 1087 450 (true, H1537_cp1.1, H1537_cp1.2)) ∧ ptTest pH1537 (runFrom pH1537 (fmask pH1537) (cmask pH1537) (hmask pH1537) 1087 450 (true, H1537_cp1.1, H1537_cp1.2)) 1537 769 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1537_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1537_fin) true) H1537_seg1) (by decide) rfl H1537_fin ptTest_fst
noncomputable def I1537_cp1 : Nat × Nat := t7val% (fastRun pI1537 1 1086 (init pI1537) (init pI1537))
theorem I1537_seg1 : segOK pI1537 1 1086 (init pI1537) (init pI1537) I1537_cp1.1 I1537_cp1.2 = true := by
  decide +kernel
theorem I1537_fin : (prmOK pI1537 1537 && intTest pI1537 (runFrom pI1537 (fmask pI1537) (cmask pI1537) (hmask pI1537) 1087 450 (true, I1537_cp1.1, I1537_cp1.2)) 1537 20 false) = true := by
  decide +kernel
theorem I1537_ok : RunOK pI1537 1537 (runFrom pI1537 (fmask pI1537) (cmask pI1537) (hmask pI1537) 1087 450 (true, I1537_cp1.1, I1537_cp1.2)) ∧ intTest pI1537 (runFrom pI1537 (fmask pI1537) (cmask pI1537) (hmask pI1537) 1087 450 (true, I1537_cp1.1, I1537_cp1.2)) 1537 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1537_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1537_fin) true) I1537_seg1) (by decide) rfl I1537_fin intTest_fst
theorem link1537 : linkOK pL1537 pH1537 pI1537 = true := by decide +kernel
theorem cvx1537 : ConvexBetweenHumps 1537 :=
  cvx_of L1537_ok H1537_ok I1537_ok link1537 (by decide)

/-! ### `N = 1538` -/

def pL1538 : Prm := ⟨81, 39, 39, 1540, 11, 18446744073709551616, 121930885681415385, 121930885681415385⟩
def pH1538 : Prm := ⟨81, 39, 39, 1540, 11, 18446744073709551616, 121931985193043161, 121931985193043161⟩
def pI1538 : Prm := ⟨66, 33, 30, 1540, 11, 18446744073709551616, 121930885681415385, 121931985193043161⟩
noncomputable def L1538_cp1 : Nat × Nat := t7val% (fastRun pL1538 1 1087 (init pL1538) (init pL1538))
theorem L1538_seg1 : segOK pL1538 1 1087 (init pL1538) (init pL1538) L1538_cp1.1 L1538_cp1.2 = true := by
  decide +kernel
theorem L1538_fin : (prmOK pL1538 1538 && ptTest pL1538 (runFrom pL1538 (fmask pL1538) (cmask pL1538) (hmask pL1538) 1088 450 (true, L1538_cp1.1, L1538_cp1.2)) 1538 769 false) = true := by
  decide +kernel
theorem L1538_ok : RunOK pL1538 1538 (runFrom pL1538 (fmask pL1538) (cmask pL1538) (hmask pL1538) 1088 450 (true, L1538_cp1.1, L1538_cp1.2)) ∧ ptTest pL1538 (runFrom pL1538 (fmask pL1538) (cmask pL1538) (hmask pL1538) 1088 450 (true, L1538_cp1.1, L1538_cp1.2)) 1538 769 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1538_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1538_fin) true) L1538_seg1) (by decide) rfl L1538_fin ptTest_fst
noncomputable def H1538_cp1 : Nat × Nat := t7val% (fastRun pH1538 1 1087 (init pH1538) (init pH1538))
theorem H1538_seg1 : segOK pH1538 1 1087 (init pH1538) (init pH1538) H1538_cp1.1 H1538_cp1.2 = true := by
  decide +kernel
theorem H1538_fin : (prmOK pH1538 1538 && ptTest pH1538 (runFrom pH1538 (fmask pH1538) (cmask pH1538) (hmask pH1538) 1088 450 (true, H1538_cp1.1, H1538_cp1.2)) 1538 769 true) = true := by
  decide +kernel
theorem H1538_ok : RunOK pH1538 1538 (runFrom pH1538 (fmask pH1538) (cmask pH1538) (hmask pH1538) 1088 450 (true, H1538_cp1.1, H1538_cp1.2)) ∧ ptTest pH1538 (runFrom pH1538 (fmask pH1538) (cmask pH1538) (hmask pH1538) 1088 450 (true, H1538_cp1.1, H1538_cp1.2)) 1538 769 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1538_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1538_fin) true) H1538_seg1) (by decide) rfl H1538_fin ptTest_fst
noncomputable def I1538_cp1 : Nat × Nat := t7val% (fastRun pI1538 1 1087 (init pI1538) (init pI1538))
theorem I1538_seg1 : segOK pI1538 1 1087 (init pI1538) (init pI1538) I1538_cp1.1 I1538_cp1.2 = true := by
  decide +kernel
theorem I1538_fin : (prmOK pI1538 1538 && intTest pI1538 (runFrom pI1538 (fmask pI1538) (cmask pI1538) (hmask pI1538) 1088 450 (true, I1538_cp1.1, I1538_cp1.2)) 1538 20 true) = true := by
  decide +kernel
theorem I1538_ok : RunOK pI1538 1538 (runFrom pI1538 (fmask pI1538) (cmask pI1538) (hmask pI1538) 1088 450 (true, I1538_cp1.1, I1538_cp1.2)) ∧ intTest pI1538 (runFrom pI1538 (fmask pI1538) (cmask pI1538) (hmask pI1538) 1088 450 (true, I1538_cp1.1, I1538_cp1.2)) 1538 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1538_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1538_fin) true) I1538_seg1) (by decide) rfl I1538_fin intTest_fst
theorem link1538 : linkOK pL1538 pH1538 pI1538 = true := by decide +kernel
theorem cvx1538 : ConvexBetweenHumps 1538 :=
  cvx_of L1538_ok H1538_ok I1538_ok link1538 (by decide)
theorem cenlink1538 : cenLinkOK pI1538 1538 = true := by decide +kernel
theorem cen1538 : CenterUniqueMin 1538 ∧ DipHyp 1538 ∧ OnePointHyps 1538 :=
  cen_of L1538_ok H1538_ok I1538_ok link1538 cenlink1538

/-! ### `N = 1539` -/

def pL1539 : Prm := ⟨81, 39, 39, 1541, 11, 18446744073709551616, 121866331863247366, 121866331863247366⟩
def pH1539 : Prm := ⟨81, 39, 39, 1541, 11, 18446744073709551616, 121867431374875142, 121867431374875142⟩
def pI1539 : Prm := ⟨66, 33, 30, 1541, 11, 18446744073709551616, 121866331863247366, 121867431374875142⟩
noncomputable def L1539_cp1 : Nat × Nat := t7val% (fastRun pL1539 1 1087 (init pL1539) (init pL1539))
theorem L1539_seg1 : segOK pL1539 1 1087 (init pL1539) (init pL1539) L1539_cp1.1 L1539_cp1.2 = true := by
  decide +kernel
theorem L1539_fin : (prmOK pL1539 1539 && ptTest pL1539 (runFrom pL1539 (fmask pL1539) (cmask pL1539) (hmask pL1539) 1088 451 (true, L1539_cp1.1, L1539_cp1.2)) 1539 770 false) = true := by
  decide +kernel
theorem L1539_ok : RunOK pL1539 1539 (runFrom pL1539 (fmask pL1539) (cmask pL1539) (hmask pL1539) 1088 451 (true, L1539_cp1.1, L1539_cp1.2)) ∧ ptTest pL1539 (runFrom pL1539 (fmask pL1539) (cmask pL1539) (hmask pL1539) 1088 451 (true, L1539_cp1.1, L1539_cp1.2)) 1539 770 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1539_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1539_fin) true) L1539_seg1) (by decide) rfl L1539_fin ptTest_fst
noncomputable def H1539_cp1 : Nat × Nat := t7val% (fastRun pH1539 1 1087 (init pH1539) (init pH1539))
theorem H1539_seg1 : segOK pH1539 1 1087 (init pH1539) (init pH1539) H1539_cp1.1 H1539_cp1.2 = true := by
  decide +kernel
theorem H1539_fin : (prmOK pH1539 1539 && ptTest pH1539 (runFrom pH1539 (fmask pH1539) (cmask pH1539) (hmask pH1539) 1088 451 (true, H1539_cp1.1, H1539_cp1.2)) 1539 770 true) = true := by
  decide +kernel
theorem H1539_ok : RunOK pH1539 1539 (runFrom pH1539 (fmask pH1539) (cmask pH1539) (hmask pH1539) 1088 451 (true, H1539_cp1.1, H1539_cp1.2)) ∧ ptTest pH1539 (runFrom pH1539 (fmask pH1539) (cmask pH1539) (hmask pH1539) 1088 451 (true, H1539_cp1.1, H1539_cp1.2)) 1539 770 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1539_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1539_fin) true) H1539_seg1) (by decide) rfl H1539_fin ptTest_fst
noncomputable def I1539_cp1 : Nat × Nat := t7val% (fastRun pI1539 1 1087 (init pI1539) (init pI1539))
theorem I1539_seg1 : segOK pI1539 1 1087 (init pI1539) (init pI1539) I1539_cp1.1 I1539_cp1.2 = true := by
  decide +kernel
theorem I1539_fin : (prmOK pI1539 1539 && intTest pI1539 (runFrom pI1539 (fmask pI1539) (cmask pI1539) (hmask pI1539) 1088 451 (true, I1539_cp1.1, I1539_cp1.2)) 1539 20 false) = true := by
  decide +kernel
theorem I1539_ok : RunOK pI1539 1539 (runFrom pI1539 (fmask pI1539) (cmask pI1539) (hmask pI1539) 1088 451 (true, I1539_cp1.1, I1539_cp1.2)) ∧ intTest pI1539 (runFrom pI1539 (fmask pI1539) (cmask pI1539) (hmask pI1539) 1088 451 (true, I1539_cp1.1, I1539_cp1.2)) 1539 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1539_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1539_fin) true) I1539_seg1) (by decide) rfl I1539_fin intTest_fst
theorem link1539 : linkOK pL1539 pH1539 pI1539 = true := by decide +kernel
theorem cvx1539 : ConvexBetweenHumps 1539 :=
  cvx_of L1539_ok H1539_ok I1539_ok link1539 (by decide)

/-! ### `N = 1540` -/

def pL1540 : Prm := ⟨80, 38, 39, 1542, 11, 18446744073709551616, 121801883330313870, 121801883330313870⟩
def pH1540 : Prm := ⟨81, 39, 39, 1542, 11, 18446744073709551616, 121802982841941646, 121802982841941646⟩
def pI1540 : Prm := ⟨66, 33, 30, 1542, 11, 18446744073709551616, 121801883330313870, 121802982841941646⟩
noncomputable def L1540_cp1 : Nat × Nat := t7val% (fastRun pL1540 1 1088 (init pL1540) (init pL1540))
theorem L1540_seg1 : segOK pL1540 1 1088 (init pL1540) (init pL1540) L1540_cp1.1 L1540_cp1.2 = true := by
  decide +kernel
theorem L1540_fin : (prmOK pL1540 1540 && ptTest pL1540 (runFrom pL1540 (fmask pL1540) (cmask pL1540) (hmask pL1540) 1089 451 (true, L1540_cp1.1, L1540_cp1.2)) 1540 770 false) = true := by
  decide +kernel
theorem L1540_ok : RunOK pL1540 1540 (runFrom pL1540 (fmask pL1540) (cmask pL1540) (hmask pL1540) 1089 451 (true, L1540_cp1.1, L1540_cp1.2)) ∧ ptTest pL1540 (runFrom pL1540 (fmask pL1540) (cmask pL1540) (hmask pL1540) 1089 451 (true, L1540_cp1.1, L1540_cp1.2)) 1540 770 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1540_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1540_fin) true) L1540_seg1) (by decide) rfl L1540_fin ptTest_fst
noncomputable def H1540_cp1 : Nat × Nat := t7val% (fastRun pH1540 1 1088 (init pH1540) (init pH1540))
theorem H1540_seg1 : segOK pH1540 1 1088 (init pH1540) (init pH1540) H1540_cp1.1 H1540_cp1.2 = true := by
  decide +kernel
theorem H1540_fin : (prmOK pH1540 1540 && ptTest pH1540 (runFrom pH1540 (fmask pH1540) (cmask pH1540) (hmask pH1540) 1089 451 (true, H1540_cp1.1, H1540_cp1.2)) 1540 770 true) = true := by
  decide +kernel
theorem H1540_ok : RunOK pH1540 1540 (runFrom pH1540 (fmask pH1540) (cmask pH1540) (hmask pH1540) 1089 451 (true, H1540_cp1.1, H1540_cp1.2)) ∧ ptTest pH1540 (runFrom pH1540 (fmask pH1540) (cmask pH1540) (hmask pH1540) 1089 451 (true, H1540_cp1.1, H1540_cp1.2)) 1540 770 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1540_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1540_fin) true) H1540_seg1) (by decide) rfl H1540_fin ptTest_fst
noncomputable def I1540_cp1 : Nat × Nat := t7val% (fastRun pI1540 1 1088 (init pI1540) (init pI1540))
theorem I1540_seg1 : segOK pI1540 1 1088 (init pI1540) (init pI1540) I1540_cp1.1 I1540_cp1.2 = true := by
  decide +kernel
theorem I1540_fin : (prmOK pI1540 1540 && intTest pI1540 (runFrom pI1540 (fmask pI1540) (cmask pI1540) (hmask pI1540) 1089 451 (true, I1540_cp1.1, I1540_cp1.2)) 1540 20 true) = true := by
  decide +kernel
theorem I1540_ok : RunOK pI1540 1540 (runFrom pI1540 (fmask pI1540) (cmask pI1540) (hmask pI1540) 1089 451 (true, I1540_cp1.1, I1540_cp1.2)) ∧ intTest pI1540 (runFrom pI1540 (fmask pI1540) (cmask pI1540) (hmask pI1540) 1089 451 (true, I1540_cp1.1, I1540_cp1.2)) 1540 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1540_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1540_fin) true) I1540_seg1) (by decide) rfl I1540_fin intTest_fst
theorem link1540 : linkOK pL1540 pH1540 pI1540 = true := by decide +kernel
theorem cvx1540 : ConvexBetweenHumps 1540 :=
  cvx_of L1540_ok H1540_ok I1540_ok link1540 (by decide)
theorem cenlink1540 : cenLinkOK pI1540 1540 = true := by decide +kernel
theorem cen1540 : CenterUniqueMin 1540 ∧ DipHyp 1540 ∧ OnePointHyps 1540 :=
  cen_of L1540_ok H1540_ok I1540_ok link1540 cenlink1540

/-! ### `N = 1541` -/

def pL1541 : Prm := ⟨80, 38, 39, 1543, 11, 18446744073709551616, 121737477979492703, 121737477979492703⟩
def pH1541 : Prm := ⟨81, 39, 39, 1543, 11, 18446744073709551616, 121738577491120479, 121738577491120479⟩
def pI1541 : Prm := ⟨66, 33, 30, 1543, 11, 18446744073709551616, 121737477979492703, 121738577491120479⟩
noncomputable def L1541_cp1 : Nat × Nat := t7val% (fastRun pL1541 1 1089 (init pL1541) (init pL1541))
theorem L1541_seg1 : segOK pL1541 1 1089 (init pL1541) (init pL1541) L1541_cp1.1 L1541_cp1.2 = true := by
  decide +kernel
theorem L1541_fin : (prmOK pL1541 1541 && ptTest pL1541 (runFrom pL1541 (fmask pL1541) (cmask pL1541) (hmask pL1541) 1090 451 (true, L1541_cp1.1, L1541_cp1.2)) 1541 771 false) = true := by
  decide +kernel
theorem L1541_ok : RunOK pL1541 1541 (runFrom pL1541 (fmask pL1541) (cmask pL1541) (hmask pL1541) 1090 451 (true, L1541_cp1.1, L1541_cp1.2)) ∧ ptTest pL1541 (runFrom pL1541 (fmask pL1541) (cmask pL1541) (hmask pL1541) 1090 451 (true, L1541_cp1.1, L1541_cp1.2)) 1541 771 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1541_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1541_fin) true) L1541_seg1) (by decide) rfl L1541_fin ptTest_fst
noncomputable def H1541_cp1 : Nat × Nat := t7val% (fastRun pH1541 1 1089 (init pH1541) (init pH1541))
theorem H1541_seg1 : segOK pH1541 1 1089 (init pH1541) (init pH1541) H1541_cp1.1 H1541_cp1.2 = true := by
  decide +kernel
theorem H1541_fin : (prmOK pH1541 1541 && ptTest pH1541 (runFrom pH1541 (fmask pH1541) (cmask pH1541) (hmask pH1541) 1090 451 (true, H1541_cp1.1, H1541_cp1.2)) 1541 771 true) = true := by
  decide +kernel
theorem H1541_ok : RunOK pH1541 1541 (runFrom pH1541 (fmask pH1541) (cmask pH1541) (hmask pH1541) 1090 451 (true, H1541_cp1.1, H1541_cp1.2)) ∧ ptTest pH1541 (runFrom pH1541 (fmask pH1541) (cmask pH1541) (hmask pH1541) 1090 451 (true, H1541_cp1.1, H1541_cp1.2)) 1541 771 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1541_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1541_fin) true) H1541_seg1) (by decide) rfl H1541_fin ptTest_fst
noncomputable def I1541_cp1 : Nat × Nat := t7val% (fastRun pI1541 1 1089 (init pI1541) (init pI1541))
theorem I1541_seg1 : segOK pI1541 1 1089 (init pI1541) (init pI1541) I1541_cp1.1 I1541_cp1.2 = true := by
  decide +kernel
theorem I1541_fin : (prmOK pI1541 1541 && intTest pI1541 (runFrom pI1541 (fmask pI1541) (cmask pI1541) (hmask pI1541) 1090 451 (true, I1541_cp1.1, I1541_cp1.2)) 1541 20 false) = true := by
  decide +kernel
theorem I1541_ok : RunOK pI1541 1541 (runFrom pI1541 (fmask pI1541) (cmask pI1541) (hmask pI1541) 1090 451 (true, I1541_cp1.1, I1541_cp1.2)) ∧ intTest pI1541 (runFrom pI1541 (fmask pI1541) (cmask pI1541) (hmask pI1541) 1090 451 (true, I1541_cp1.1, I1541_cp1.2)) 1541 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1541_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1541_fin) true) I1541_seg1) (by decide) rfl I1541_fin intTest_fst
theorem link1541 : linkOK pL1541 pH1541 pI1541 = true := by decide +kernel
theorem cvx1541 : ConvexBetweenHumps 1541 :=
  cvx_of L1541_ok H1541_ok I1541_ok link1541 (by decide)

/-! ### `N = 1542` -/

def pL1542 : Prm := ⟨81, 39, 39, 1544, 11, 18446744073709551616, 121673177527280750, 121673177527280750⟩
def pH1542 : Prm := ⟨81, 39, 39, 1544, 11, 18446744073709551616, 121674277038908526, 121674277038908526⟩
def pI1542 : Prm := ⟨66, 33, 30, 1544, 11, 18446744073709551616, 121673177527280750, 121674277038908526⟩
noncomputable def L1542_cp1 : Nat × Nat := t7val% (fastRun pL1542 1 1089 (init pL1542) (init pL1542))
theorem L1542_seg1 : segOK pL1542 1 1089 (init pL1542) (init pL1542) L1542_cp1.1 L1542_cp1.2 = true := by
  decide +kernel
theorem L1542_fin : (prmOK pL1542 1542 && ptTest pL1542 (runFrom pL1542 (fmask pL1542) (cmask pL1542) (hmask pL1542) 1090 452 (true, L1542_cp1.1, L1542_cp1.2)) 1542 771 false) = true := by
  decide +kernel
theorem L1542_ok : RunOK pL1542 1542 (runFrom pL1542 (fmask pL1542) (cmask pL1542) (hmask pL1542) 1090 452 (true, L1542_cp1.1, L1542_cp1.2)) ∧ ptTest pL1542 (runFrom pL1542 (fmask pL1542) (cmask pL1542) (hmask pL1542) 1090 452 (true, L1542_cp1.1, L1542_cp1.2)) 1542 771 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1542_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1542_fin) true) L1542_seg1) (by decide) rfl L1542_fin ptTest_fst
noncomputable def H1542_cp1 : Nat × Nat := t7val% (fastRun pH1542 1 1089 (init pH1542) (init pH1542))
theorem H1542_seg1 : segOK pH1542 1 1089 (init pH1542) (init pH1542) H1542_cp1.1 H1542_cp1.2 = true := by
  decide +kernel
theorem H1542_fin : (prmOK pH1542 1542 && ptTest pH1542 (runFrom pH1542 (fmask pH1542) (cmask pH1542) (hmask pH1542) 1090 452 (true, H1542_cp1.1, H1542_cp1.2)) 1542 771 true) = true := by
  decide +kernel
theorem H1542_ok : RunOK pH1542 1542 (runFrom pH1542 (fmask pH1542) (cmask pH1542) (hmask pH1542) 1090 452 (true, H1542_cp1.1, H1542_cp1.2)) ∧ ptTest pH1542 (runFrom pH1542 (fmask pH1542) (cmask pH1542) (hmask pH1542) 1090 452 (true, H1542_cp1.1, H1542_cp1.2)) 1542 771 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1542_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1542_fin) true) H1542_seg1) (by decide) rfl H1542_fin ptTest_fst
noncomputable def I1542_cp1 : Nat × Nat := t7val% (fastRun pI1542 1 1089 (init pI1542) (init pI1542))
theorem I1542_seg1 : segOK pI1542 1 1089 (init pI1542) (init pI1542) I1542_cp1.1 I1542_cp1.2 = true := by
  decide +kernel
theorem I1542_fin : (prmOK pI1542 1542 && intTest pI1542 (runFrom pI1542 (fmask pI1542) (cmask pI1542) (hmask pI1542) 1090 452 (true, I1542_cp1.1, I1542_cp1.2)) 1542 20 true) = true := by
  decide +kernel
theorem I1542_ok : RunOK pI1542 1542 (runFrom pI1542 (fmask pI1542) (cmask pI1542) (hmask pI1542) 1090 452 (true, I1542_cp1.1, I1542_cp1.2)) ∧ intTest pI1542 (runFrom pI1542 (fmask pI1542) (cmask pI1542) (hmask pI1542) 1090 452 (true, I1542_cp1.1, I1542_cp1.2)) 1542 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1542_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1542_fin) true) I1542_seg1) (by decide) rfl I1542_fin intTest_fst
theorem link1542 : linkOK pL1542 pH1542 pI1542 = true := by decide +kernel
theorem cvx1542 : ConvexBetweenHumps 1542 :=
  cvx_of L1542_ok H1542_ok I1542_ok link1542 (by decide)
theorem cenlink1542 : cenLinkOK pI1542 1542 = true := by decide +kernel
theorem cen1542 : CenterUniqueMin 1542 ∧ DipHyp 1542 ∧ OnePointHyps 1542 :=
  cen_of L1542_ok H1542_ok I1542_ok link1542 cenlink1542

/-! ### `N = 1543` -/

def pL1543 : Prm := ⟨81, 39, 39, 1545, 11, 18446744073709551616, 121608920115952854, 121608920115952854⟩
def pH1543 : Prm := ⟨81, 39, 39, 1545, 11, 18446744073709551616, 121610019627580630, 121610019627580630⟩
def pI1543 : Prm := ⟨66, 33, 30, 1545, 11, 18446744073709551616, 121608920115952854, 121610019627580630⟩
noncomputable def L1543_cp1 : Nat × Nat := t7val% (fastRun pL1543 1 1090 (init pL1543) (init pL1543))
theorem L1543_seg1 : segOK pL1543 1 1090 (init pL1543) (init pL1543) L1543_cp1.1 L1543_cp1.2 = true := by
  decide +kernel
theorem L1543_fin : (prmOK pL1543 1543 && ptTest pL1543 (runFrom pL1543 (fmask pL1543) (cmask pL1543) (hmask pL1543) 1091 452 (true, L1543_cp1.1, L1543_cp1.2)) 1543 772 false) = true := by
  decide +kernel
theorem L1543_ok : RunOK pL1543 1543 (runFrom pL1543 (fmask pL1543) (cmask pL1543) (hmask pL1543) 1091 452 (true, L1543_cp1.1, L1543_cp1.2)) ∧ ptTest pL1543 (runFrom pL1543 (fmask pL1543) (cmask pL1543) (hmask pL1543) 1091 452 (true, L1543_cp1.1, L1543_cp1.2)) 1543 772 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1543_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1543_fin) true) L1543_seg1) (by decide) rfl L1543_fin ptTest_fst
noncomputable def H1543_cp1 : Nat × Nat := t7val% (fastRun pH1543 1 1090 (init pH1543) (init pH1543))
theorem H1543_seg1 : segOK pH1543 1 1090 (init pH1543) (init pH1543) H1543_cp1.1 H1543_cp1.2 = true := by
  decide +kernel
theorem H1543_fin : (prmOK pH1543 1543 && ptTest pH1543 (runFrom pH1543 (fmask pH1543) (cmask pH1543) (hmask pH1543) 1091 452 (true, H1543_cp1.1, H1543_cp1.2)) 1543 772 true) = true := by
  decide +kernel
theorem H1543_ok : RunOK pH1543 1543 (runFrom pH1543 (fmask pH1543) (cmask pH1543) (hmask pH1543) 1091 452 (true, H1543_cp1.1, H1543_cp1.2)) ∧ ptTest pH1543 (runFrom pH1543 (fmask pH1543) (cmask pH1543) (hmask pH1543) 1091 452 (true, H1543_cp1.1, H1543_cp1.2)) 1543 772 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1543_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1543_fin) true) H1543_seg1) (by decide) rfl H1543_fin ptTest_fst
noncomputable def I1543_cp1 : Nat × Nat := t7val% (fastRun pI1543 1 1090 (init pI1543) (init pI1543))
theorem I1543_seg1 : segOK pI1543 1 1090 (init pI1543) (init pI1543) I1543_cp1.1 I1543_cp1.2 = true := by
  decide +kernel
theorem I1543_fin : (prmOK pI1543 1543 && intTest pI1543 (runFrom pI1543 (fmask pI1543) (cmask pI1543) (hmask pI1543) 1091 452 (true, I1543_cp1.1, I1543_cp1.2)) 1543 20 false) = true := by
  decide +kernel
theorem I1543_ok : RunOK pI1543 1543 (runFrom pI1543 (fmask pI1543) (cmask pI1543) (hmask pI1543) 1091 452 (true, I1543_cp1.1, I1543_cp1.2)) ∧ intTest pI1543 (runFrom pI1543 (fmask pI1543) (cmask pI1543) (hmask pI1543) 1091 452 (true, I1543_cp1.1, I1543_cp1.2)) 1543 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1543_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1543_fin) true) I1543_seg1) (by decide) rfl I1543_fin intTest_fst
theorem link1543 : linkOK pL1543 pH1543 pI1543 = true := by decide +kernel
theorem cvx1543 : ConvexBetweenHumps 1543 :=
  cvx_of L1543_ok H1543_ok I1543_ok link1543 (by decide)

/-! ### `N = 1544` -/

def pL1544 : Prm := ⟨81, 39, 39, 1546, 11, 18446744073709551616, 121544767218527323, 121544767218527323⟩
def pH1544 : Prm := ⟨81, 39, 39, 1546, 11, 18446744073709551616, 121545866730155099, 121545866730155099⟩
def pI1544 : Prm := ⟨66, 33, 30, 1546, 11, 18446744073709551616, 121544767218527323, 121545866730155099⟩
noncomputable def L1544_cp1 : Nat × Nat := t7val% (fastRun pL1544 1 1091 (init pL1544) (init pL1544))
theorem L1544_seg1 : segOK pL1544 1 1091 (init pL1544) (init pL1544) L1544_cp1.1 L1544_cp1.2 = true := by
  decide +kernel
theorem L1544_fin : (prmOK pL1544 1544 && ptTest pL1544 (runFrom pL1544 (fmask pL1544) (cmask pL1544) (hmask pL1544) 1092 452 (true, L1544_cp1.1, L1544_cp1.2)) 1544 772 false) = true := by
  decide +kernel
theorem L1544_ok : RunOK pL1544 1544 (runFrom pL1544 (fmask pL1544) (cmask pL1544) (hmask pL1544) 1092 452 (true, L1544_cp1.1, L1544_cp1.2)) ∧ ptTest pL1544 (runFrom pL1544 (fmask pL1544) (cmask pL1544) (hmask pL1544) 1092 452 (true, L1544_cp1.1, L1544_cp1.2)) 1544 772 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1544_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1544_fin) true) L1544_seg1) (by decide) rfl L1544_fin ptTest_fst
noncomputable def H1544_cp1 : Nat × Nat := t7val% (fastRun pH1544 1 1091 (init pH1544) (init pH1544))
theorem H1544_seg1 : segOK pH1544 1 1091 (init pH1544) (init pH1544) H1544_cp1.1 H1544_cp1.2 = true := by
  decide +kernel
theorem H1544_fin : (prmOK pH1544 1544 && ptTest pH1544 (runFrom pH1544 (fmask pH1544) (cmask pH1544) (hmask pH1544) 1092 452 (true, H1544_cp1.1, H1544_cp1.2)) 1544 772 true) = true := by
  decide +kernel
theorem H1544_ok : RunOK pH1544 1544 (runFrom pH1544 (fmask pH1544) (cmask pH1544) (hmask pH1544) 1092 452 (true, H1544_cp1.1, H1544_cp1.2)) ∧ ptTest pH1544 (runFrom pH1544 (fmask pH1544) (cmask pH1544) (hmask pH1544) 1092 452 (true, H1544_cp1.1, H1544_cp1.2)) 1544 772 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1544_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1544_fin) true) H1544_seg1) (by decide) rfl H1544_fin ptTest_fst
noncomputable def I1544_cp1 : Nat × Nat := t7val% (fastRun pI1544 1 1091 (init pI1544) (init pI1544))
theorem I1544_seg1 : segOK pI1544 1 1091 (init pI1544) (init pI1544) I1544_cp1.1 I1544_cp1.2 = true := by
  decide +kernel
theorem I1544_fin : (prmOK pI1544 1544 && intTest pI1544 (runFrom pI1544 (fmask pI1544) (cmask pI1544) (hmask pI1544) 1092 452 (true, I1544_cp1.1, I1544_cp1.2)) 1544 20 true) = true := by
  decide +kernel
theorem I1544_ok : RunOK pI1544 1544 (runFrom pI1544 (fmask pI1544) (cmask pI1544) (hmask pI1544) 1092 452 (true, I1544_cp1.1, I1544_cp1.2)) ∧ intTest pI1544 (runFrom pI1544 (fmask pI1544) (cmask pI1544) (hmask pI1544) 1092 452 (true, I1544_cp1.1, I1544_cp1.2)) 1544 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1544_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1544_fin) true) I1544_seg1) (by decide) rfl I1544_fin intTest_fst
theorem link1544 : linkOK pL1544 pH1544 pI1544 = true := by decide +kernel
theorem cvx1544 : ConvexBetweenHumps 1544 :=
  cvx_of L1544_ok H1544_ok I1544_ok link1544 (by decide)
theorem cenlink1544 : cenLinkOK pI1544 1544 = true := by decide +kernel
theorem cen1544 : CenterUniqueMin 1544 ∧ DipHyp 1544 ∧ OnePointHyps 1544 :=
  cen_of L1544_ok H1544_ok I1544_ok link1544 cenlink1544

/-! ### `N = 1545` -/

def pL1545 : Prm := ⟨81, 39, 39, 1547, 11, 18446744073709551616, 121480657221366319, 121480657221366319⟩
def pH1545 : Prm := ⟨81, 39, 39, 1547, 11, 18446744073709551616, 121481756732994095, 121481756732994095⟩
def pI1545 : Prm := ⟨66, 33, 30, 1547, 11, 18446744073709551616, 121480657221366319, 121481756732994095⟩
noncomputable def L1545_cp1 : Nat × Nat := t7val% (fastRun pL1545 1 1091 (init pL1545) (init pL1545))
theorem L1545_seg1 : segOK pL1545 1 1091 (init pL1545) (init pL1545) L1545_cp1.1 L1545_cp1.2 = true := by
  decide +kernel
theorem L1545_fin : (prmOK pL1545 1545 && ptTest pL1545 (runFrom pL1545 (fmask pL1545) (cmask pL1545) (hmask pL1545) 1092 453 (true, L1545_cp1.1, L1545_cp1.2)) 1545 773 false) = true := by
  decide +kernel
theorem L1545_ok : RunOK pL1545 1545 (runFrom pL1545 (fmask pL1545) (cmask pL1545) (hmask pL1545) 1092 453 (true, L1545_cp1.1, L1545_cp1.2)) ∧ ptTest pL1545 (runFrom pL1545 (fmask pL1545) (cmask pL1545) (hmask pL1545) 1092 453 (true, L1545_cp1.1, L1545_cp1.2)) 1545 773 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1545_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1545_fin) true) L1545_seg1) (by decide) rfl L1545_fin ptTest_fst
noncomputable def H1545_cp1 : Nat × Nat := t7val% (fastRun pH1545 1 1091 (init pH1545) (init pH1545))
theorem H1545_seg1 : segOK pH1545 1 1091 (init pH1545) (init pH1545) H1545_cp1.1 H1545_cp1.2 = true := by
  decide +kernel
theorem H1545_fin : (prmOK pH1545 1545 && ptTest pH1545 (runFrom pH1545 (fmask pH1545) (cmask pH1545) (hmask pH1545) 1092 453 (true, H1545_cp1.1, H1545_cp1.2)) 1545 773 true) = true := by
  decide +kernel
theorem H1545_ok : RunOK pH1545 1545 (runFrom pH1545 (fmask pH1545) (cmask pH1545) (hmask pH1545) 1092 453 (true, H1545_cp1.1, H1545_cp1.2)) ∧ ptTest pH1545 (runFrom pH1545 (fmask pH1545) (cmask pH1545) (hmask pH1545) 1092 453 (true, H1545_cp1.1, H1545_cp1.2)) 1545 773 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1545_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1545_fin) true) H1545_seg1) (by decide) rfl H1545_fin ptTest_fst
noncomputable def I1545_cp1 : Nat × Nat := t7val% (fastRun pI1545 1 1091 (init pI1545) (init pI1545))
theorem I1545_seg1 : segOK pI1545 1 1091 (init pI1545) (init pI1545) I1545_cp1.1 I1545_cp1.2 = true := by
  decide +kernel
theorem I1545_fin : (prmOK pI1545 1545 && intTest pI1545 (runFrom pI1545 (fmask pI1545) (cmask pI1545) (hmask pI1545) 1092 453 (true, I1545_cp1.1, I1545_cp1.2)) 1545 20 false) = true := by
  decide +kernel
theorem I1545_ok : RunOK pI1545 1545 (runFrom pI1545 (fmask pI1545) (cmask pI1545) (hmask pI1545) 1092 453 (true, I1545_cp1.1, I1545_cp1.2)) ∧ intTest pI1545 (runFrom pI1545 (fmask pI1545) (cmask pI1545) (hmask pI1545) 1092 453 (true, I1545_cp1.1, I1545_cp1.2)) 1545 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1545_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1545_fin) true) I1545_seg1) (by decide) rfl I1545_fin intTest_fst
theorem link1545 : linkOK pL1545 pH1545 pI1545 = true := by decide +kernel
theorem cvx1545 : ConvexBetweenHumps 1545 :=
  cvx_of L1545_ok H1545_ok I1545_ok link1545 (by decide)

/-! ### `N = 1546` -/

def pL1546 : Prm := ⟨81, 39, 39, 1548, 11, 18446744073709551616, 121416651355319295, 121416651355319295⟩
def pH1546 : Prm := ⟨81, 39, 39, 1548, 11, 18446744073709551616, 121417750866947071, 121417750866947071⟩
def pI1546 : Prm := ⟨66, 33, 30, 1548, 11, 18446744073709551616, 121416651355319295, 121417750866947071⟩
noncomputable def L1546_cp1 : Nat × Nat := t7val% (fastRun pL1546 1 1092 (init pL1546) (init pL1546))
theorem L1546_seg1 : segOK pL1546 1 1092 (init pL1546) (init pL1546) L1546_cp1.1 L1546_cp1.2 = true := by
  decide +kernel
theorem L1546_fin : (prmOK pL1546 1546 && ptTest pL1546 (runFrom pL1546 (fmask pL1546) (cmask pL1546) (hmask pL1546) 1093 453 (true, L1546_cp1.1, L1546_cp1.2)) 1546 773 false) = true := by
  decide +kernel
theorem L1546_ok : RunOK pL1546 1546 (runFrom pL1546 (fmask pL1546) (cmask pL1546) (hmask pL1546) 1093 453 (true, L1546_cp1.1, L1546_cp1.2)) ∧ ptTest pL1546 (runFrom pL1546 (fmask pL1546) (cmask pL1546) (hmask pL1546) 1093 453 (true, L1546_cp1.1, L1546_cp1.2)) 1546 773 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1546_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1546_fin) true) L1546_seg1) (by decide) rfl L1546_fin ptTest_fst
noncomputable def H1546_cp1 : Nat × Nat := t7val% (fastRun pH1546 1 1092 (init pH1546) (init pH1546))
theorem H1546_seg1 : segOK pH1546 1 1092 (init pH1546) (init pH1546) H1546_cp1.1 H1546_cp1.2 = true := by
  decide +kernel
theorem H1546_fin : (prmOK pH1546 1546 && ptTest pH1546 (runFrom pH1546 (fmask pH1546) (cmask pH1546) (hmask pH1546) 1093 453 (true, H1546_cp1.1, H1546_cp1.2)) 1546 773 true) = true := by
  decide +kernel
theorem H1546_ok : RunOK pH1546 1546 (runFrom pH1546 (fmask pH1546) (cmask pH1546) (hmask pH1546) 1093 453 (true, H1546_cp1.1, H1546_cp1.2)) ∧ ptTest pH1546 (runFrom pH1546 (fmask pH1546) (cmask pH1546) (hmask pH1546) 1093 453 (true, H1546_cp1.1, H1546_cp1.2)) 1546 773 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1546_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1546_fin) true) H1546_seg1) (by decide) rfl H1546_fin ptTest_fst
noncomputable def I1546_cp1 : Nat × Nat := t7val% (fastRun pI1546 1 1092 (init pI1546) (init pI1546))
theorem I1546_seg1 : segOK pI1546 1 1092 (init pI1546) (init pI1546) I1546_cp1.1 I1546_cp1.2 = true := by
  decide +kernel
theorem I1546_fin : (prmOK pI1546 1546 && intTest pI1546 (runFrom pI1546 (fmask pI1546) (cmask pI1546) (hmask pI1546) 1093 453 (true, I1546_cp1.1, I1546_cp1.2)) 1546 20 true) = true := by
  decide +kernel
theorem I1546_ok : RunOK pI1546 1546 (runFrom pI1546 (fmask pI1546) (cmask pI1546) (hmask pI1546) 1093 453 (true, I1546_cp1.1, I1546_cp1.2)) ∧ intTest pI1546 (runFrom pI1546 (fmask pI1546) (cmask pI1546) (hmask pI1546) 1093 453 (true, I1546_cp1.1, I1546_cp1.2)) 1546 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1546_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1546_fin) true) I1546_seg1) (by decide) rfl I1546_fin intTest_fst
theorem link1546 : linkOK pL1546 pH1546 pI1546 = true := by decide +kernel
theorem cvx1546 : ConvexBetweenHumps 1546 :=
  cvx_of L1546_ok H1546_ok I1546_ok link1546 (by decide)
theorem cenlink1546 : cenLinkOK pI1546 1546 = true := by decide +kernel
theorem cen1546 : CenterUniqueMin 1546 ∧ DipHyp 1546 ∧ OnePointHyps 1546 :=
  cen_of L1546_ok H1546_ok I1546_ok link1546 cenlink1546

/-! ### The range -/

theorem cvx_1530_1546 {N : ℕ} (h1 : 1530 ≤ N) (h2 : N ≤ 1546) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1537
  · by_cases h4 : N ≤ 1533
    · by_cases h6 : N ≤ 1531
      · by_cases h8 : N ≤ 1530
        · obtain rfl : N = 1530 := by omega
          exact cvx1530
        · obtain rfl : N = 1531 := by omega
          exact cvx1531
      · by_cases h8 : N ≤ 1532
        · obtain rfl : N = 1532 := by omega
          exact cvx1532
        · obtain rfl : N = 1533 := by omega
          exact cvx1533
    · by_cases h6 : N ≤ 1535
      · by_cases h8 : N ≤ 1534
        · obtain rfl : N = 1534 := by omega
          exact cvx1534
        · obtain rfl : N = 1535 := by omega
          exact cvx1535
      · by_cases h8 : N ≤ 1536
        · obtain rfl : N = 1536 := by omega
          exact cvx1536
        · obtain rfl : N = 1537 := by omega
          exact cvx1537
  · by_cases h4 : N ≤ 1541
    · by_cases h6 : N ≤ 1539
      · by_cases h8 : N ≤ 1538
        · obtain rfl : N = 1538 := by omega
          exact cvx1538
        · obtain rfl : N = 1539 := by omega
          exact cvx1539
      · by_cases h8 : N ≤ 1540
        · obtain rfl : N = 1540 := by omega
          exact cvx1540
        · obtain rfl : N = 1541 := by omega
          exact cvx1541
    · by_cases h6 : N ≤ 1543
      · by_cases h8 : N ≤ 1542
        · obtain rfl : N = 1542 := by omega
          exact cvx1542
        · obtain rfl : N = 1543 := by omega
          exact cvx1543
      · by_cases h8 : N ≤ 1544
        · obtain rfl : N = 1544 := by omega
          exact cvx1544
        · by_cases h10 : N ≤ 1545
          · obtain rfl : N = 1545 := by omega
            exact cvx1545
          · obtain rfl : N = 1546 := by omega
            exact cvx1546

theorem cen_1530_1546 {N : ℕ} (h1 : 1530 ≤ N) (h2 : N ≤ 1546) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1536
  · by_cases h4 : N ≤ 1532
    · by_cases h6 : N ≤ 1530
      · obtain rfl : N = 1530 := by omega
        exact cen1530
      · obtain rfl : N = 1532 := by omega
        exact cen1532
    · by_cases h6 : N ≤ 1534
      · obtain rfl : N = 1534 := by omega
        exact cen1534
      · obtain rfl : N = 1536 := by omega
        exact cen1536
  · by_cases h4 : N ≤ 1540
    · by_cases h6 : N ≤ 1538
      · obtain rfl : N = 1538 := by omega
        exact cen1538
      · obtain rfl : N = 1540 := by omega
        exact cen1540
    · by_cases h6 : N ≤ 1542
      · obtain rfl : N = 1542 := by omega
        exact cen1542
      · by_cases h8 : N ≤ 1544
        · obtain rfl : N = 1544 := by omega
          exact cen1544
        · obtain rfl : N = 1546 := by omega
          exact cen1546

end Kagey131.PaperD.T7
