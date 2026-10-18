import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1338, …, 1359` (generated)

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

/-! ### `N = 1338` -/

def pL1338 : Prm := ⟨79, 37, 39, 1340, 11, 18446744073709551616, 136535296710126637, 136535296710126637⟩
def pH1338 : Prm := ⟨79, 37, 39, 1340, 11, 18446744073709551616, 136536396221754413, 136536396221754413⟩
def pI1338 : Prm := ⟨65, 33, 29, 1340, 11, 18446744073709551616, 136535296710126637, 136536396221754413⟩
noncomputable def L1338_cp1 : Nat × Nat := t7val% (fastRun pL1338 1 945 (init pL1338) (init pL1338))
theorem L1338_seg1 : segOK pL1338 1 945 (init pL1338) (init pL1338) L1338_cp1.1 L1338_cp1.2 = true := by
  decide +kernel
theorem L1338_fin : (prmOK pL1338 1338 && ptTest pL1338 (runFrom pL1338 (fmask pL1338) (cmask pL1338) (hmask pL1338) 946 392 (true, L1338_cp1.1, L1338_cp1.2)) 1338 669 false) = true := by
  decide +kernel
theorem L1338_ok : RunOK pL1338 1338 (runFrom pL1338 (fmask pL1338) (cmask pL1338) (hmask pL1338) 946 392 (true, L1338_cp1.1, L1338_cp1.2)) ∧ ptTest pL1338 (runFrom pL1338 (fmask pL1338) (cmask pL1338) (hmask pL1338) 946 392 (true, L1338_cp1.1, L1338_cp1.2)) 1338 669 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1338_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1338_fin) true) L1338_seg1) (by decide) rfl L1338_fin ptTest_fst
noncomputable def H1338_cp1 : Nat × Nat := t7val% (fastRun pH1338 1 945 (init pH1338) (init pH1338))
theorem H1338_seg1 : segOK pH1338 1 945 (init pH1338) (init pH1338) H1338_cp1.1 H1338_cp1.2 = true := by
  decide +kernel
theorem H1338_fin : (prmOK pH1338 1338 && ptTest pH1338 (runFrom pH1338 (fmask pH1338) (cmask pH1338) (hmask pH1338) 946 392 (true, H1338_cp1.1, H1338_cp1.2)) 1338 669 true) = true := by
  decide +kernel
theorem H1338_ok : RunOK pH1338 1338 (runFrom pH1338 (fmask pH1338) (cmask pH1338) (hmask pH1338) 946 392 (true, H1338_cp1.1, H1338_cp1.2)) ∧ ptTest pH1338 (runFrom pH1338 (fmask pH1338) (cmask pH1338) (hmask pH1338) 946 392 (true, H1338_cp1.1, H1338_cp1.2)) 1338 669 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1338_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1338_fin) true) H1338_seg1) (by decide) rfl H1338_fin ptTest_fst
noncomputable def I1338_cp1 : Nat × Nat := t7val% (fastRun pI1338 1 945 (init pI1338) (init pI1338))
theorem I1338_seg1 : segOK pI1338 1 945 (init pI1338) (init pI1338) I1338_cp1.1 I1338_cp1.2 = true := by
  decide +kernel
theorem I1338_fin : (prmOK pI1338 1338 && intTest pI1338 (runFrom pI1338 (fmask pI1338) (cmask pI1338) (hmask pI1338) 946 392 (true, I1338_cp1.1, I1338_cp1.2)) 1338 19 true) = true := by
  decide +kernel
theorem I1338_ok : RunOK pI1338 1338 (runFrom pI1338 (fmask pI1338) (cmask pI1338) (hmask pI1338) 946 392 (true, I1338_cp1.1, I1338_cp1.2)) ∧ intTest pI1338 (runFrom pI1338 (fmask pI1338) (cmask pI1338) (hmask pI1338) 946 392 (true, I1338_cp1.1, I1338_cp1.2)) 1338 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1338_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1338_fin) true) I1338_seg1) (by decide) rfl I1338_fin intTest_fst
theorem link1338 : linkOK pL1338 pH1338 pI1338 = true := by decide +kernel
theorem cvx1338 : ConvexBetweenHumps 1338 :=
  cvx_of L1338_ok H1338_ok I1338_ok link1338 (by decide)
theorem cenlink1338 : cenLinkOK pI1338 1338 = true := by decide +kernel
theorem cen1338 : CenterUniqueMin 1338 ∧ DipHyp 1338 ∧ OnePointHyps 1338 :=
  cen_of L1338_ok H1338_ok I1338_ok link1338 cenlink1338

/-! ### `N = 1339` -/

def pL1339 : Prm := ⟨79, 37, 39, 1341, 11, 18446744073709551616, 136452713558190371, 136452713558190371⟩
def pH1339 : Prm := ⟨79, 37, 39, 1341, 11, 18446744073709551616, 136453813069818147, 136453813069818147⟩
def pI1339 : Prm := ⟨65, 33, 29, 1341, 11, 18446744073709551616, 136452713558190371, 136453813069818147⟩
noncomputable def L1339_cp1 : Nat × Nat := t7val% (fastRun pL1339 1 946 (init pL1339) (init pL1339))
theorem L1339_seg1 : segOK pL1339 1 946 (init pL1339) (init pL1339) L1339_cp1.1 L1339_cp1.2 = true := by
  decide +kernel
theorem L1339_fin : (prmOK pL1339 1339 && ptTest pL1339 (runFrom pL1339 (fmask pL1339) (cmask pL1339) (hmask pL1339) 947 392 (true, L1339_cp1.1, L1339_cp1.2)) 1339 670 false) = true := by
  decide +kernel
theorem L1339_ok : RunOK pL1339 1339 (runFrom pL1339 (fmask pL1339) (cmask pL1339) (hmask pL1339) 947 392 (true, L1339_cp1.1, L1339_cp1.2)) ∧ ptTest pL1339 (runFrom pL1339 (fmask pL1339) (cmask pL1339) (hmask pL1339) 947 392 (true, L1339_cp1.1, L1339_cp1.2)) 1339 670 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1339_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1339_fin) true) L1339_seg1) (by decide) rfl L1339_fin ptTest_fst
noncomputable def H1339_cp1 : Nat × Nat := t7val% (fastRun pH1339 1 946 (init pH1339) (init pH1339))
theorem H1339_seg1 : segOK pH1339 1 946 (init pH1339) (init pH1339) H1339_cp1.1 H1339_cp1.2 = true := by
  decide +kernel
theorem H1339_fin : (prmOK pH1339 1339 && ptTest pH1339 (runFrom pH1339 (fmask pH1339) (cmask pH1339) (hmask pH1339) 947 392 (true, H1339_cp1.1, H1339_cp1.2)) 1339 670 true) = true := by
  decide +kernel
theorem H1339_ok : RunOK pH1339 1339 (runFrom pH1339 (fmask pH1339) (cmask pH1339) (hmask pH1339) 947 392 (true, H1339_cp1.1, H1339_cp1.2)) ∧ ptTest pH1339 (runFrom pH1339 (fmask pH1339) (cmask pH1339) (hmask pH1339) 947 392 (true, H1339_cp1.1, H1339_cp1.2)) 1339 670 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1339_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1339_fin) true) H1339_seg1) (by decide) rfl H1339_fin ptTest_fst
noncomputable def I1339_cp1 : Nat × Nat := t7val% (fastRun pI1339 1 946 (init pI1339) (init pI1339))
theorem I1339_seg1 : segOK pI1339 1 946 (init pI1339) (init pI1339) I1339_cp1.1 I1339_cp1.2 = true := by
  decide +kernel
theorem I1339_fin : (prmOK pI1339 1339 && intTest pI1339 (runFrom pI1339 (fmask pI1339) (cmask pI1339) (hmask pI1339) 947 392 (true, I1339_cp1.1, I1339_cp1.2)) 1339 19 false) = true := by
  decide +kernel
theorem I1339_ok : RunOK pI1339 1339 (runFrom pI1339 (fmask pI1339) (cmask pI1339) (hmask pI1339) 947 392 (true, I1339_cp1.1, I1339_cp1.2)) ∧ intTest pI1339 (runFrom pI1339 (fmask pI1339) (cmask pI1339) (hmask pI1339) 947 392 (true, I1339_cp1.1, I1339_cp1.2)) 1339 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1339_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1339_fin) true) I1339_seg1) (by decide) rfl I1339_fin intTest_fst
theorem link1339 : linkOK pL1339 pH1339 pI1339 = true := by decide +kernel
theorem cvx1339 : ConvexBetweenHumps 1339 :=
  cvx_of L1339_ok H1339_ok I1339_ok link1339 (by decide)

/-! ### `N = 1340` -/

def pL1340 : Prm := ⟨79, 37, 39, 1342, 11, 18446744073709551616, 136370286555415485, 136370286555415485⟩
def pH1340 : Prm := ⟨79, 37, 39, 1342, 11, 18446744073709551616, 136371386067043261, 136371386067043261⟩
def pI1340 : Prm := ⟨65, 33, 29, 1342, 11, 18446744073709551616, 136370286555415485, 136371386067043261⟩
noncomputable def L1340_cp1 : Nat × Nat := t7val% (fastRun pL1340 1 947 (init pL1340) (init pL1340))
theorem L1340_seg1 : segOK pL1340 1 947 (init pL1340) (init pL1340) L1340_cp1.1 L1340_cp1.2 = true := by
  decide +kernel
theorem L1340_fin : (prmOK pL1340 1340 && ptTest pL1340 (runFrom pL1340 (fmask pL1340) (cmask pL1340) (hmask pL1340) 948 392 (true, L1340_cp1.1, L1340_cp1.2)) 1340 670 false) = true := by
  decide +kernel
theorem L1340_ok : RunOK pL1340 1340 (runFrom pL1340 (fmask pL1340) (cmask pL1340) (hmask pL1340) 948 392 (true, L1340_cp1.1, L1340_cp1.2)) ∧ ptTest pL1340 (runFrom pL1340 (fmask pL1340) (cmask pL1340) (hmask pL1340) 948 392 (true, L1340_cp1.1, L1340_cp1.2)) 1340 670 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1340_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1340_fin) true) L1340_seg1) (by decide) rfl L1340_fin ptTest_fst
noncomputable def H1340_cp1 : Nat × Nat := t7val% (fastRun pH1340 1 947 (init pH1340) (init pH1340))
theorem H1340_seg1 : segOK pH1340 1 947 (init pH1340) (init pH1340) H1340_cp1.1 H1340_cp1.2 = true := by
  decide +kernel
theorem H1340_fin : (prmOK pH1340 1340 && ptTest pH1340 (runFrom pH1340 (fmask pH1340) (cmask pH1340) (hmask pH1340) 948 392 (true, H1340_cp1.1, H1340_cp1.2)) 1340 670 true) = true := by
  decide +kernel
theorem H1340_ok : RunOK pH1340 1340 (runFrom pH1340 (fmask pH1340) (cmask pH1340) (hmask pH1340) 948 392 (true, H1340_cp1.1, H1340_cp1.2)) ∧ ptTest pH1340 (runFrom pH1340 (fmask pH1340) (cmask pH1340) (hmask pH1340) 948 392 (true, H1340_cp1.1, H1340_cp1.2)) 1340 670 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1340_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1340_fin) true) H1340_seg1) (by decide) rfl H1340_fin ptTest_fst
noncomputable def I1340_cp1 : Nat × Nat := t7val% (fastRun pI1340 1 947 (init pI1340) (init pI1340))
theorem I1340_seg1 : segOK pI1340 1 947 (init pI1340) (init pI1340) I1340_cp1.1 I1340_cp1.2 = true := by
  decide +kernel
theorem I1340_fin : (prmOK pI1340 1340 && intTest pI1340 (runFrom pI1340 (fmask pI1340) (cmask pI1340) (hmask pI1340) 948 392 (true, I1340_cp1.1, I1340_cp1.2)) 1340 19 true) = true := by
  decide +kernel
theorem I1340_ok : RunOK pI1340 1340 (runFrom pI1340 (fmask pI1340) (cmask pI1340) (hmask pI1340) 948 392 (true, I1340_cp1.1, I1340_cp1.2)) ∧ intTest pI1340 (runFrom pI1340 (fmask pI1340) (cmask pI1340) (hmask pI1340) 948 392 (true, I1340_cp1.1, I1340_cp1.2)) 1340 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1340_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1340_fin) true) I1340_seg1) (by decide) rfl I1340_fin intTest_fst
theorem link1340 : linkOK pL1340 pH1340 pI1340 = true := by decide +kernel
theorem cvx1340 : ConvexBetweenHumps 1340 :=
  cvx_of L1340_ok H1340_ok I1340_ok link1340 (by decide)
theorem cenlink1340 : cenLinkOK pI1340 1340 = true := by decide +kernel
theorem cen1340 : CenterUniqueMin 1340 ∧ DipHyp 1340 ∧ OnePointHyps 1340 :=
  cen_of L1340_ok H1340_ok I1340_ok link1340 cenlink1340

/-! ### `N = 1341` -/

def pL1341 : Prm := ⟨79, 37, 39, 1343, 11, 18446744073709551616, 136287920751927673, 136287920751927673⟩
def pH1341 : Prm := ⟨79, 37, 39, 1343, 11, 18446744073709551616, 136289020263555449, 136289020263555449⟩
def pI1341 : Prm := ⟨65, 33, 29, 1343, 11, 18446744073709551616, 136287920751927673, 136289020263555449⟩
noncomputable def L1341_cp1 : Nat × Nat := t7val% (fastRun pL1341 1 947 (init pL1341) (init pL1341))
theorem L1341_seg1 : segOK pL1341 1 947 (init pL1341) (init pL1341) L1341_cp1.1 L1341_cp1.2 = true := by
  decide +kernel
theorem L1341_fin : (prmOK pL1341 1341 && ptTest pL1341 (runFrom pL1341 (fmask pL1341) (cmask pL1341) (hmask pL1341) 948 393 (true, L1341_cp1.1, L1341_cp1.2)) 1341 671 false) = true := by
  decide +kernel
theorem L1341_ok : RunOK pL1341 1341 (runFrom pL1341 (fmask pL1341) (cmask pL1341) (hmask pL1341) 948 393 (true, L1341_cp1.1, L1341_cp1.2)) ∧ ptTest pL1341 (runFrom pL1341 (fmask pL1341) (cmask pL1341) (hmask pL1341) 948 393 (true, L1341_cp1.1, L1341_cp1.2)) 1341 671 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1341_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1341_fin) true) L1341_seg1) (by decide) rfl L1341_fin ptTest_fst
noncomputable def H1341_cp1 : Nat × Nat := t7val% (fastRun pH1341 1 947 (init pH1341) (init pH1341))
theorem H1341_seg1 : segOK pH1341 1 947 (init pH1341) (init pH1341) H1341_cp1.1 H1341_cp1.2 = true := by
  decide +kernel
theorem H1341_fin : (prmOK pH1341 1341 && ptTest pH1341 (runFrom pH1341 (fmask pH1341) (cmask pH1341) (hmask pH1341) 948 393 (true, H1341_cp1.1, H1341_cp1.2)) 1341 671 true) = true := by
  decide +kernel
theorem H1341_ok : RunOK pH1341 1341 (runFrom pH1341 (fmask pH1341) (cmask pH1341) (hmask pH1341) 948 393 (true, H1341_cp1.1, H1341_cp1.2)) ∧ ptTest pH1341 (runFrom pH1341 (fmask pH1341) (cmask pH1341) (hmask pH1341) 948 393 (true, H1341_cp1.1, H1341_cp1.2)) 1341 671 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1341_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1341_fin) true) H1341_seg1) (by decide) rfl H1341_fin ptTest_fst
noncomputable def I1341_cp1 : Nat × Nat := t7val% (fastRun pI1341 1 947 (init pI1341) (init pI1341))
theorem I1341_seg1 : segOK pI1341 1 947 (init pI1341) (init pI1341) I1341_cp1.1 I1341_cp1.2 = true := by
  decide +kernel
theorem I1341_fin : (prmOK pI1341 1341 && intTest pI1341 (runFrom pI1341 (fmask pI1341) (cmask pI1341) (hmask pI1341) 948 393 (true, I1341_cp1.1, I1341_cp1.2)) 1341 19 false) = true := by
  decide +kernel
theorem I1341_ok : RunOK pI1341 1341 (runFrom pI1341 (fmask pI1341) (cmask pI1341) (hmask pI1341) 948 393 (true, I1341_cp1.1, I1341_cp1.2)) ∧ intTest pI1341 (runFrom pI1341 (fmask pI1341) (cmask pI1341) (hmask pI1341) 948 393 (true, I1341_cp1.1, I1341_cp1.2)) 1341 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1341_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1341_fin) true) I1341_seg1) (by decide) rfl I1341_fin intTest_fst
theorem link1341 : linkOK pL1341 pH1341 pI1341 = true := by decide +kernel
theorem cvx1341 : ConvexBetweenHumps 1341 :=
  cvx_of L1341_ok H1341_ok I1341_ok link1341 (by decide)

/-! ### `N = 1342` -/

def pL1342 : Prm := ⟨79, 37, 39, 1344, 11, 18446744073709551616, 136205710439495199, 136205710439495199⟩
def pH1342 : Prm := ⟨79, 37, 39, 1344, 11, 18446744073709551616, 136206809951122975, 136206809951122975⟩
def pI1342 : Prm := ⟨67, 32, 32, 1344, 11, 18446744073709551616, 136205710439495199, 136206809951122975⟩
noncomputable def L1342_cp1 : Nat × Nat := t7val% (fastRun pL1342 1 948 (init pL1342) (init pL1342))
theorem L1342_seg1 : segOK pL1342 1 948 (init pL1342) (init pL1342) L1342_cp1.1 L1342_cp1.2 = true := by
  decide +kernel
theorem L1342_fin : (prmOK pL1342 1342 && ptTest pL1342 (runFrom pL1342 (fmask pL1342) (cmask pL1342) (hmask pL1342) 949 393 (true, L1342_cp1.1, L1342_cp1.2)) 1342 671 false) = true := by
  decide +kernel
theorem L1342_ok : RunOK pL1342 1342 (runFrom pL1342 (fmask pL1342) (cmask pL1342) (hmask pL1342) 949 393 (true, L1342_cp1.1, L1342_cp1.2)) ∧ ptTest pL1342 (runFrom pL1342 (fmask pL1342) (cmask pL1342) (hmask pL1342) 949 393 (true, L1342_cp1.1, L1342_cp1.2)) 1342 671 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1342_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1342_fin) true) L1342_seg1) (by decide) rfl L1342_fin ptTest_fst
noncomputable def H1342_cp1 : Nat × Nat := t7val% (fastRun pH1342 1 948 (init pH1342) (init pH1342))
theorem H1342_seg1 : segOK pH1342 1 948 (init pH1342) (init pH1342) H1342_cp1.1 H1342_cp1.2 = true := by
  decide +kernel
theorem H1342_fin : (prmOK pH1342 1342 && ptTest pH1342 (runFrom pH1342 (fmask pH1342) (cmask pH1342) (hmask pH1342) 949 393 (true, H1342_cp1.1, H1342_cp1.2)) 1342 671 true) = true := by
  decide +kernel
theorem H1342_ok : RunOK pH1342 1342 (runFrom pH1342 (fmask pH1342) (cmask pH1342) (hmask pH1342) 949 393 (true, H1342_cp1.1, H1342_cp1.2)) ∧ ptTest pH1342 (runFrom pH1342 (fmask pH1342) (cmask pH1342) (hmask pH1342) 949 393 (true, H1342_cp1.1, H1342_cp1.2)) 1342 671 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1342_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1342_fin) true) H1342_seg1) (by decide) rfl H1342_fin ptTest_fst
noncomputable def I1342_cp1 : Nat × Nat := t7val% (fastRun pI1342 1 948 (init pI1342) (init pI1342))
theorem I1342_seg1 : segOK pI1342 1 948 (init pI1342) (init pI1342) I1342_cp1.1 I1342_cp1.2 = true := by
  decide +kernel
theorem I1342_fin : (prmOK pI1342 1342 && intTest pI1342 (runFrom pI1342 (fmask pI1342) (cmask pI1342) (hmask pI1342) 949 393 (true, I1342_cp1.1, I1342_cp1.2)) 1342 19 true) = true := by
  decide +kernel
theorem I1342_ok : RunOK pI1342 1342 (runFrom pI1342 (fmask pI1342) (cmask pI1342) (hmask pI1342) 949 393 (true, I1342_cp1.1, I1342_cp1.2)) ∧ intTest pI1342 (runFrom pI1342 (fmask pI1342) (cmask pI1342) (hmask pI1342) 949 393 (true, I1342_cp1.1, I1342_cp1.2)) 1342 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1342_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1342_fin) true) I1342_seg1) (by decide) rfl I1342_fin intTest_fst
theorem link1342 : linkOK pL1342 pH1342 pI1342 = true := by decide +kernel
theorem cvx1342 : ConvexBetweenHumps 1342 :=
  cvx_of L1342_ok H1342_ok I1342_ok link1342 (by decide)
theorem cenlink1342 : cenLinkOK pI1342 1342 = true := by decide +kernel
theorem cen1342 : CenterUniqueMin 1342 ∧ DipHyp 1342 ∧ OnePointHyps 1342 :=
  cen_of L1342_ok H1342_ok I1342_ok link1342 cenlink1342

/-! ### `N = 1343` -/

def pL1343 : Prm := ⟨79, 37, 39, 1345, 11, 18446744073709551616, 136123561099639314, 136123561099639314⟩
def pH1343 : Prm := ⟨79, 37, 39, 1345, 11, 18446744073709551616, 136124660611267090, 136124660611267090⟩
def pI1343 : Prm := ⟨65, 33, 29, 1345, 11, 18446744073709551616, 136123561099639314, 136124660611267090⟩
noncomputable def L1343_cp1 : Nat × Nat := t7val% (fastRun pL1343 1 949 (init pL1343) (init pL1343))
theorem L1343_seg1 : segOK pL1343 1 949 (init pL1343) (init pL1343) L1343_cp1.1 L1343_cp1.2 = true := by
  decide +kernel
theorem L1343_fin : (prmOK pL1343 1343 && ptTest pL1343 (runFrom pL1343 (fmask pL1343) (cmask pL1343) (hmask pL1343) 950 393 (true, L1343_cp1.1, L1343_cp1.2)) 1343 672 false) = true := by
  decide +kernel
theorem L1343_ok : RunOK pL1343 1343 (runFrom pL1343 (fmask pL1343) (cmask pL1343) (hmask pL1343) 950 393 (true, L1343_cp1.1, L1343_cp1.2)) ∧ ptTest pL1343 (runFrom pL1343 (fmask pL1343) (cmask pL1343) (hmask pL1343) 950 393 (true, L1343_cp1.1, L1343_cp1.2)) 1343 672 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1343_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1343_fin) true) L1343_seg1) (by decide) rfl L1343_fin ptTest_fst
noncomputable def H1343_cp1 : Nat × Nat := t7val% (fastRun pH1343 1 949 (init pH1343) (init pH1343))
theorem H1343_seg1 : segOK pH1343 1 949 (init pH1343) (init pH1343) H1343_cp1.1 H1343_cp1.2 = true := by
  decide +kernel
theorem H1343_fin : (prmOK pH1343 1343 && ptTest pH1343 (runFrom pH1343 (fmask pH1343) (cmask pH1343) (hmask pH1343) 950 393 (true, H1343_cp1.1, H1343_cp1.2)) 1343 672 true) = true := by
  decide +kernel
theorem H1343_ok : RunOK pH1343 1343 (runFrom pH1343 (fmask pH1343) (cmask pH1343) (hmask pH1343) 950 393 (true, H1343_cp1.1, H1343_cp1.2)) ∧ ptTest pH1343 (runFrom pH1343 (fmask pH1343) (cmask pH1343) (hmask pH1343) 950 393 (true, H1343_cp1.1, H1343_cp1.2)) 1343 672 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1343_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1343_fin) true) H1343_seg1) (by decide) rfl H1343_fin ptTest_fst
noncomputable def I1343_cp1 : Nat × Nat := t7val% (fastRun pI1343 1 949 (init pI1343) (init pI1343))
theorem I1343_seg1 : segOK pI1343 1 949 (init pI1343) (init pI1343) I1343_cp1.1 I1343_cp1.2 = true := by
  decide +kernel
theorem I1343_fin : (prmOK pI1343 1343 && intTest pI1343 (runFrom pI1343 (fmask pI1343) (cmask pI1343) (hmask pI1343) 950 393 (true, I1343_cp1.1, I1343_cp1.2)) 1343 19 false) = true := by
  decide +kernel
theorem I1343_ok : RunOK pI1343 1343 (runFrom pI1343 (fmask pI1343) (cmask pI1343) (hmask pI1343) 950 393 (true, I1343_cp1.1, I1343_cp1.2)) ∧ intTest pI1343 (runFrom pI1343 (fmask pI1343) (cmask pI1343) (hmask pI1343) 950 393 (true, I1343_cp1.1, I1343_cp1.2)) 1343 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1343_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1343_fin) true) I1343_seg1) (by decide) rfl I1343_fin intTest_fst
theorem link1343 : linkOK pL1343 pH1343 pI1343 = true := by decide +kernel
theorem cvx1343 : ConvexBetweenHumps 1343 :=
  cvx_of L1343_ok H1343_ok I1343_ok link1343 (by decide)

/-! ### `N = 1344` -/

def pL1344 : Prm := ⟨79, 37, 39, 1346, 11, 18446744073709551616, 136041566596440522, 136041566596440522⟩
def pH1344 : Prm := ⟨79, 37, 39, 1346, 11, 18446744073709551616, 136042666108068298, 136042666108068298⟩
def pI1344 : Prm := ⟨65, 33, 29, 1346, 11, 18446744073709551616, 136041566596440522, 136042666108068298⟩
noncomputable def L1344_cp1 : Nat × Nat := t7val% (fastRun pL1344 1 949 (init pL1344) (init pL1344))
theorem L1344_seg1 : segOK pL1344 1 949 (init pL1344) (init pL1344) L1344_cp1.1 L1344_cp1.2 = true := by
  decide +kernel
theorem L1344_fin : (prmOK pL1344 1344 && ptTest pL1344 (runFrom pL1344 (fmask pL1344) (cmask pL1344) (hmask pL1344) 950 394 (true, L1344_cp1.1, L1344_cp1.2)) 1344 672 false) = true := by
  decide +kernel
theorem L1344_ok : RunOK pL1344 1344 (runFrom pL1344 (fmask pL1344) (cmask pL1344) (hmask pL1344) 950 394 (true, L1344_cp1.1, L1344_cp1.2)) ∧ ptTest pL1344 (runFrom pL1344 (fmask pL1344) (cmask pL1344) (hmask pL1344) 950 394 (true, L1344_cp1.1, L1344_cp1.2)) 1344 672 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1344_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1344_fin) true) L1344_seg1) (by decide) rfl L1344_fin ptTest_fst
noncomputable def H1344_cp1 : Nat × Nat := t7val% (fastRun pH1344 1 949 (init pH1344) (init pH1344))
theorem H1344_seg1 : segOK pH1344 1 949 (init pH1344) (init pH1344) H1344_cp1.1 H1344_cp1.2 = true := by
  decide +kernel
theorem H1344_fin : (prmOK pH1344 1344 && ptTest pH1344 (runFrom pH1344 (fmask pH1344) (cmask pH1344) (hmask pH1344) 950 394 (true, H1344_cp1.1, H1344_cp1.2)) 1344 672 true) = true := by
  decide +kernel
theorem H1344_ok : RunOK pH1344 1344 (runFrom pH1344 (fmask pH1344) (cmask pH1344) (hmask pH1344) 950 394 (true, H1344_cp1.1, H1344_cp1.2)) ∧ ptTest pH1344 (runFrom pH1344 (fmask pH1344) (cmask pH1344) (hmask pH1344) 950 394 (true, H1344_cp1.1, H1344_cp1.2)) 1344 672 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1344_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1344_fin) true) H1344_seg1) (by decide) rfl H1344_fin ptTest_fst
noncomputable def I1344_cp1 : Nat × Nat := t7val% (fastRun pI1344 1 949 (init pI1344) (init pI1344))
theorem I1344_seg1 : segOK pI1344 1 949 (init pI1344) (init pI1344) I1344_cp1.1 I1344_cp1.2 = true := by
  decide +kernel
theorem I1344_fin : (prmOK pI1344 1344 && intTest pI1344 (runFrom pI1344 (fmask pI1344) (cmask pI1344) (hmask pI1344) 950 394 (true, I1344_cp1.1, I1344_cp1.2)) 1344 20 true) = true := by
  decide +kernel
theorem I1344_ok : RunOK pI1344 1344 (runFrom pI1344 (fmask pI1344) (cmask pI1344) (hmask pI1344) 950 394 (true, I1344_cp1.1, I1344_cp1.2)) ∧ intTest pI1344 (runFrom pI1344 (fmask pI1344) (cmask pI1344) (hmask pI1344) 950 394 (true, I1344_cp1.1, I1344_cp1.2)) 1344 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1344_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1344_fin) true) I1344_seg1) (by decide) rfl I1344_fin intTest_fst
theorem link1344 : linkOK pL1344 pH1344 pI1344 = true := by decide +kernel
theorem cvx1344 : ConvexBetweenHumps 1344 :=
  cvx_of L1344_ok H1344_ok I1344_ok link1344 (by decide)
theorem cenlink1344 : cenLinkOK pI1344 1344 = true := by decide +kernel
theorem cen1344 : CenterUniqueMin 1344 ∧ DipHyp 1344 ∧ OnePointHyps 1344 :=
  cen_of L1344_ok H1344_ok I1344_ok link1344 cenlink1344

/-! ### `N = 1345` -/

def pL1345 : Prm := ⟨79, 37, 39, 1347, 11, 18446744073709551616, 135959632840214640, 135959632840214640⟩
def pH1345 : Prm := ⟨79, 37, 39, 1347, 11, 18446744073709551616, 135960732351842416, 135960732351842416⟩
def pI1345 : Prm := ⟨65, 33, 29, 1347, 11, 18446744073709551616, 135959632840214640, 135960732351842416⟩
noncomputable def L1345_cp1 : Nat × Nat := t7val% (fastRun pL1345 1 950 (init pL1345) (init pL1345))
theorem L1345_seg1 : segOK pL1345 1 950 (init pL1345) (init pL1345) L1345_cp1.1 L1345_cp1.2 = true := by
  decide +kernel
theorem L1345_fin : (prmOK pL1345 1345 && ptTest pL1345 (runFrom pL1345 (fmask pL1345) (cmask pL1345) (hmask pL1345) 951 394 (true, L1345_cp1.1, L1345_cp1.2)) 1345 673 false) = true := by
  decide +kernel
theorem L1345_ok : RunOK pL1345 1345 (runFrom pL1345 (fmask pL1345) (cmask pL1345) (hmask pL1345) 951 394 (true, L1345_cp1.1, L1345_cp1.2)) ∧ ptTest pL1345 (runFrom pL1345 (fmask pL1345) (cmask pL1345) (hmask pL1345) 951 394 (true, L1345_cp1.1, L1345_cp1.2)) 1345 673 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1345_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1345_fin) true) L1345_seg1) (by decide) rfl L1345_fin ptTest_fst
noncomputable def H1345_cp1 : Nat × Nat := t7val% (fastRun pH1345 1 950 (init pH1345) (init pH1345))
theorem H1345_seg1 : segOK pH1345 1 950 (init pH1345) (init pH1345) H1345_cp1.1 H1345_cp1.2 = true := by
  decide +kernel
theorem H1345_fin : (prmOK pH1345 1345 && ptTest pH1345 (runFrom pH1345 (fmask pH1345) (cmask pH1345) (hmask pH1345) 951 394 (true, H1345_cp1.1, H1345_cp1.2)) 1345 673 true) = true := by
  decide +kernel
theorem H1345_ok : RunOK pH1345 1345 (runFrom pH1345 (fmask pH1345) (cmask pH1345) (hmask pH1345) 951 394 (true, H1345_cp1.1, H1345_cp1.2)) ∧ ptTest pH1345 (runFrom pH1345 (fmask pH1345) (cmask pH1345) (hmask pH1345) 951 394 (true, H1345_cp1.1, H1345_cp1.2)) 1345 673 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1345_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1345_fin) true) H1345_seg1) (by decide) rfl H1345_fin ptTest_fst
noncomputable def I1345_cp1 : Nat × Nat := t7val% (fastRun pI1345 1 950 (init pI1345) (init pI1345))
theorem I1345_seg1 : segOK pI1345 1 950 (init pI1345) (init pI1345) I1345_cp1.1 I1345_cp1.2 = true := by
  decide +kernel
theorem I1345_fin : (prmOK pI1345 1345 && intTest pI1345 (runFrom pI1345 (fmask pI1345) (cmask pI1345) (hmask pI1345) 951 394 (true, I1345_cp1.1, I1345_cp1.2)) 1345 20 false) = true := by
  decide +kernel
theorem I1345_ok : RunOK pI1345 1345 (runFrom pI1345 (fmask pI1345) (cmask pI1345) (hmask pI1345) 951 394 (true, I1345_cp1.1, I1345_cp1.2)) ∧ intTest pI1345 (runFrom pI1345 (fmask pI1345) (cmask pI1345) (hmask pI1345) 951 394 (true, I1345_cp1.1, I1345_cp1.2)) 1345 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1345_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1345_fin) true) I1345_seg1) (by decide) rfl I1345_fin intTest_fst
theorem link1345 : linkOK pL1345 pH1345 pI1345 = true := by decide +kernel
theorem cvx1345 : ConvexBetweenHumps 1345 :=
  cvx_of L1345_ok H1345_ok I1345_ok link1345 (by decide)

/-! ### `N = 1346` -/

def pL1346 : Prm := ⟨79, 37, 39, 1348, 11, 18446744073709551616, 135877853270010739, 135877853270010739⟩
def pH1346 : Prm := ⟨79, 37, 39, 1348, 11, 18446744073709551616, 135878952781638515, 135878952781638515⟩
def pI1346 : Prm := ⟨65, 33, 29, 1348, 11, 18446744073709551616, 135877853270010739, 135878952781638515⟩
noncomputable def L1346_cp1 : Nat × Nat := t7val% (fastRun pL1346 1 951 (init pL1346) (init pL1346))
theorem L1346_seg1 : segOK pL1346 1 951 (init pL1346) (init pL1346) L1346_cp1.1 L1346_cp1.2 = true := by
  decide +kernel
theorem L1346_fin : (prmOK pL1346 1346 && ptTest pL1346 (runFrom pL1346 (fmask pL1346) (cmask pL1346) (hmask pL1346) 952 394 (true, L1346_cp1.1, L1346_cp1.2)) 1346 673 false) = true := by
  decide +kernel
theorem L1346_ok : RunOK pL1346 1346 (runFrom pL1346 (fmask pL1346) (cmask pL1346) (hmask pL1346) 952 394 (true, L1346_cp1.1, L1346_cp1.2)) ∧ ptTest pL1346 (runFrom pL1346 (fmask pL1346) (cmask pL1346) (hmask pL1346) 952 394 (true, L1346_cp1.1, L1346_cp1.2)) 1346 673 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1346_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1346_fin) true) L1346_seg1) (by decide) rfl L1346_fin ptTest_fst
noncomputable def H1346_cp1 : Nat × Nat := t7val% (fastRun pH1346 1 951 (init pH1346) (init pH1346))
theorem H1346_seg1 : segOK pH1346 1 951 (init pH1346) (init pH1346) H1346_cp1.1 H1346_cp1.2 = true := by
  decide +kernel
theorem H1346_fin : (prmOK pH1346 1346 && ptTest pH1346 (runFrom pH1346 (fmask pH1346) (cmask pH1346) (hmask pH1346) 952 394 (true, H1346_cp1.1, H1346_cp1.2)) 1346 673 true) = true := by
  decide +kernel
theorem H1346_ok : RunOK pH1346 1346 (runFrom pH1346 (fmask pH1346) (cmask pH1346) (hmask pH1346) 952 394 (true, H1346_cp1.1, H1346_cp1.2)) ∧ ptTest pH1346 (runFrom pH1346 (fmask pH1346) (cmask pH1346) (hmask pH1346) 952 394 (true, H1346_cp1.1, H1346_cp1.2)) 1346 673 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1346_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1346_fin) true) H1346_seg1) (by decide) rfl H1346_fin ptTest_fst
noncomputable def I1346_cp1 : Nat × Nat := t7val% (fastRun pI1346 1 951 (init pI1346) (init pI1346))
theorem I1346_seg1 : segOK pI1346 1 951 (init pI1346) (init pI1346) I1346_cp1.1 I1346_cp1.2 = true := by
  decide +kernel
theorem I1346_fin : (prmOK pI1346 1346 && intTest pI1346 (runFrom pI1346 (fmask pI1346) (cmask pI1346) (hmask pI1346) 952 394 (true, I1346_cp1.1, I1346_cp1.2)) 1346 20 true) = true := by
  decide +kernel
theorem I1346_ok : RunOK pI1346 1346 (runFrom pI1346 (fmask pI1346) (cmask pI1346) (hmask pI1346) 952 394 (true, I1346_cp1.1, I1346_cp1.2)) ∧ intTest pI1346 (runFrom pI1346 (fmask pI1346) (cmask pI1346) (hmask pI1346) 952 394 (true, I1346_cp1.1, I1346_cp1.2)) 1346 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1346_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1346_fin) true) I1346_seg1) (by decide) rfl I1346_fin intTest_fst
theorem link1346 : linkOK pL1346 pH1346 pI1346 = true := by decide +kernel
theorem cvx1346 : ConvexBetweenHumps 1346 :=
  cvx_of L1346_ok H1346_ok I1346_ok link1346 (by decide)
theorem cenlink1346 : cenLinkOK pI1346 1346 = true := by decide +kernel
theorem cen1346 : CenterUniqueMin 1346 ∧ DipHyp 1346 ∧ OnePointHyps 1346 :=
  cen_of L1346_ok H1346_ok I1346_ok link1346 cenlink1346

/-! ### `N = 1347` -/

def pL1347 : Prm := ⟨79, 37, 39, 1349, 11, 18446744073709551616, 135796134222301319, 135796134222301319⟩
def pH1347 : Prm := ⟨79, 37, 39, 1349, 11, 18446744073709551616, 135797233733929095, 135797233733929095⟩
def pI1347 : Prm := ⟨65, 33, 29, 1349, 11, 18446744073709551616, 135796134222301319, 135797233733929095⟩
noncomputable def L1347_cp1 : Nat × Nat := t7val% (fastRun pL1347 1 951 (init pL1347) (init pL1347))
theorem L1347_seg1 : segOK pL1347 1 951 (init pL1347) (init pL1347) L1347_cp1.1 L1347_cp1.2 = true := by
  decide +kernel
theorem L1347_fin : (prmOK pL1347 1347 && ptTest pL1347 (runFrom pL1347 (fmask pL1347) (cmask pL1347) (hmask pL1347) 952 395 (true, L1347_cp1.1, L1347_cp1.2)) 1347 674 false) = true := by
  decide +kernel
theorem L1347_ok : RunOK pL1347 1347 (runFrom pL1347 (fmask pL1347) (cmask pL1347) (hmask pL1347) 952 395 (true, L1347_cp1.1, L1347_cp1.2)) ∧ ptTest pL1347 (runFrom pL1347 (fmask pL1347) (cmask pL1347) (hmask pL1347) 952 395 (true, L1347_cp1.1, L1347_cp1.2)) 1347 674 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1347_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1347_fin) true) L1347_seg1) (by decide) rfl L1347_fin ptTest_fst
noncomputable def H1347_cp1 : Nat × Nat := t7val% (fastRun pH1347 1 951 (init pH1347) (init pH1347))
theorem H1347_seg1 : segOK pH1347 1 951 (init pH1347) (init pH1347) H1347_cp1.1 H1347_cp1.2 = true := by
  decide +kernel
theorem H1347_fin : (prmOK pH1347 1347 && ptTest pH1347 (runFrom pH1347 (fmask pH1347) (cmask pH1347) (hmask pH1347) 952 395 (true, H1347_cp1.1, H1347_cp1.2)) 1347 674 true) = true := by
  decide +kernel
theorem H1347_ok : RunOK pH1347 1347 (runFrom pH1347 (fmask pH1347) (cmask pH1347) (hmask pH1347) 952 395 (true, H1347_cp1.1, H1347_cp1.2)) ∧ ptTest pH1347 (runFrom pH1347 (fmask pH1347) (cmask pH1347) (hmask pH1347) 952 395 (true, H1347_cp1.1, H1347_cp1.2)) 1347 674 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1347_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1347_fin) true) H1347_seg1) (by decide) rfl H1347_fin ptTest_fst
noncomputable def I1347_cp1 : Nat × Nat := t7val% (fastRun pI1347 1 951 (init pI1347) (init pI1347))
theorem I1347_seg1 : segOK pI1347 1 951 (init pI1347) (init pI1347) I1347_cp1.1 I1347_cp1.2 = true := by
  decide +kernel
theorem I1347_fin : (prmOK pI1347 1347 && intTest pI1347 (runFrom pI1347 (fmask pI1347) (cmask pI1347) (hmask pI1347) 952 395 (true, I1347_cp1.1, I1347_cp1.2)) 1347 20 false) = true := by
  decide +kernel
theorem I1347_ok : RunOK pI1347 1347 (runFrom pI1347 (fmask pI1347) (cmask pI1347) (hmask pI1347) 952 395 (true, I1347_cp1.1, I1347_cp1.2)) ∧ intTest pI1347 (runFrom pI1347 (fmask pI1347) (cmask pI1347) (hmask pI1347) 952 395 (true, I1347_cp1.1, I1347_cp1.2)) 1347 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1347_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1347_fin) true) I1347_seg1) (by decide) rfl I1347_fin intTest_fst
theorem link1347 : linkOK pL1347 pH1347 pI1347 = true := by decide +kernel
theorem cvx1347 : ConvexBetweenHumps 1347 :=
  cvx_of L1347_ok H1347_ok I1347_ok link1347 (by decide)

/-! ### `N = 1348` -/

def pL1348 : Prm := ⟨79, 37, 39, 1350, 11, 18446744073709551616, 135714568713631226, 135714568713631226⟩
def pH1348 : Prm := ⟨79, 37, 39, 1350, 11, 18446744073709551616, 135715668225259002, 135715668225259002⟩
def pI1348 : Prm := ⟨65, 33, 29, 1350, 11, 18446744073709551616, 135714568713631226, 135715668225259002⟩
noncomputable def L1348_cp1 : Nat × Nat := t7val% (fastRun pL1348 1 952 (init pL1348) (init pL1348))
theorem L1348_seg1 : segOK pL1348 1 952 (init pL1348) (init pL1348) L1348_cp1.1 L1348_cp1.2 = true := by
  decide +kernel
theorem L1348_fin : (prmOK pL1348 1348 && ptTest pL1348 (runFrom pL1348 (fmask pL1348) (cmask pL1348) (hmask pL1348) 953 395 (true, L1348_cp1.1, L1348_cp1.2)) 1348 674 false) = true := by
  decide +kernel
theorem L1348_ok : RunOK pL1348 1348 (runFrom pL1348 (fmask pL1348) (cmask pL1348) (hmask pL1348) 953 395 (true, L1348_cp1.1, L1348_cp1.2)) ∧ ptTest pL1348 (runFrom pL1348 (fmask pL1348) (cmask pL1348) (hmask pL1348) 953 395 (true, L1348_cp1.1, L1348_cp1.2)) 1348 674 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1348_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1348_fin) true) L1348_seg1) (by decide) rfl L1348_fin ptTest_fst
noncomputable def H1348_cp1 : Nat × Nat := t7val% (fastRun pH1348 1 952 (init pH1348) (init pH1348))
theorem H1348_seg1 : segOK pH1348 1 952 (init pH1348) (init pH1348) H1348_cp1.1 H1348_cp1.2 = true := by
  decide +kernel
theorem H1348_fin : (prmOK pH1348 1348 && ptTest pH1348 (runFrom pH1348 (fmask pH1348) (cmask pH1348) (hmask pH1348) 953 395 (true, H1348_cp1.1, H1348_cp1.2)) 1348 674 true) = true := by
  decide +kernel
theorem H1348_ok : RunOK pH1348 1348 (runFrom pH1348 (fmask pH1348) (cmask pH1348) (hmask pH1348) 953 395 (true, H1348_cp1.1, H1348_cp1.2)) ∧ ptTest pH1348 (runFrom pH1348 (fmask pH1348) (cmask pH1348) (hmask pH1348) 953 395 (true, H1348_cp1.1, H1348_cp1.2)) 1348 674 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1348_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1348_fin) true) H1348_seg1) (by decide) rfl H1348_fin ptTest_fst
noncomputable def I1348_cp1 : Nat × Nat := t7val% (fastRun pI1348 1 952 (init pI1348) (init pI1348))
theorem I1348_seg1 : segOK pI1348 1 952 (init pI1348) (init pI1348) I1348_cp1.1 I1348_cp1.2 = true := by
  decide +kernel
theorem I1348_fin : (prmOK pI1348 1348 && intTest pI1348 (runFrom pI1348 (fmask pI1348) (cmask pI1348) (hmask pI1348) 953 395 (true, I1348_cp1.1, I1348_cp1.2)) 1348 20 true) = true := by
  decide +kernel
theorem I1348_ok : RunOK pI1348 1348 (runFrom pI1348 (fmask pI1348) (cmask pI1348) (hmask pI1348) 953 395 (true, I1348_cp1.1, I1348_cp1.2)) ∧ intTest pI1348 (runFrom pI1348 (fmask pI1348) (cmask pI1348) (hmask pI1348) 953 395 (true, I1348_cp1.1, I1348_cp1.2)) 1348 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1348_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1348_fin) true) I1348_seg1) (by decide) rfl I1348_fin intTest_fst
theorem link1348 : linkOK pL1348 pH1348 pI1348 = true := by decide +kernel
theorem cvx1348 : ConvexBetweenHumps 1348 :=
  cvx_of L1348_ok H1348_ok I1348_ok link1348 (by decide)
theorem cenlink1348 : cenLinkOK pI1348 1348 = true := by decide +kernel
theorem cen1348 : CenterUniqueMin 1348 ∧ DipHyp 1348 ∧ OnePointHyps 1348 :=
  cen_of L1348_ok H1348_ok I1348_ok link1348 cenlink1348

/-! ### `N = 1349` -/

def pL1349 : Prm := ⟨79, 37, 39, 1351, 11, 18446744073709551616, 135633063504120883, 135633063504120883⟩
def pH1349 : Prm := ⟨79, 37, 39, 1351, 11, 18446744073709551616, 135634163015748659, 135634163015748659⟩
def pI1349 : Prm := ⟨67, 32, 32, 1351, 11, 18446744073709551616, 135633063504120883, 135634163015748659⟩
noncomputable def L1349_cp1 : Nat × Nat := t7val% (fastRun pL1349 1 953 (init pL1349) (init pL1349))
theorem L1349_seg1 : segOK pL1349 1 953 (init pL1349) (init pL1349) L1349_cp1.1 L1349_cp1.2 = true := by
  decide +kernel
theorem L1349_fin : (prmOK pL1349 1349 && ptTest pL1349 (runFrom pL1349 (fmask pL1349) (cmask pL1349) (hmask pL1349) 954 395 (true, L1349_cp1.1, L1349_cp1.2)) 1349 675 false) = true := by
  decide +kernel
theorem L1349_ok : RunOK pL1349 1349 (runFrom pL1349 (fmask pL1349) (cmask pL1349) (hmask pL1349) 954 395 (true, L1349_cp1.1, L1349_cp1.2)) ∧ ptTest pL1349 (runFrom pL1349 (fmask pL1349) (cmask pL1349) (hmask pL1349) 954 395 (true, L1349_cp1.1, L1349_cp1.2)) 1349 675 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1349_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1349_fin) true) L1349_seg1) (by decide) rfl L1349_fin ptTest_fst
noncomputable def H1349_cp1 : Nat × Nat := t7val% (fastRun pH1349 1 953 (init pH1349) (init pH1349))
theorem H1349_seg1 : segOK pH1349 1 953 (init pH1349) (init pH1349) H1349_cp1.1 H1349_cp1.2 = true := by
  decide +kernel
theorem H1349_fin : (prmOK pH1349 1349 && ptTest pH1349 (runFrom pH1349 (fmask pH1349) (cmask pH1349) (hmask pH1349) 954 395 (true, H1349_cp1.1, H1349_cp1.2)) 1349 675 true) = true := by
  decide +kernel
theorem H1349_ok : RunOK pH1349 1349 (runFrom pH1349 (fmask pH1349) (cmask pH1349) (hmask pH1349) 954 395 (true, H1349_cp1.1, H1349_cp1.2)) ∧ ptTest pH1349 (runFrom pH1349 (fmask pH1349) (cmask pH1349) (hmask pH1349) 954 395 (true, H1349_cp1.1, H1349_cp1.2)) 1349 675 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1349_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1349_fin) true) H1349_seg1) (by decide) rfl H1349_fin ptTest_fst
noncomputable def I1349_cp1 : Nat × Nat := t7val% (fastRun pI1349 1 953 (init pI1349) (init pI1349))
theorem I1349_seg1 : segOK pI1349 1 953 (init pI1349) (init pI1349) I1349_cp1.1 I1349_cp1.2 = true := by
  decide +kernel
theorem I1349_fin : (prmOK pI1349 1349 && intTest pI1349 (runFrom pI1349 (fmask pI1349) (cmask pI1349) (hmask pI1349) 954 395 (true, I1349_cp1.1, I1349_cp1.2)) 1349 20 false) = true := by
  decide +kernel
theorem I1349_ok : RunOK pI1349 1349 (runFrom pI1349 (fmask pI1349) (cmask pI1349) (hmask pI1349) 954 395 (true, I1349_cp1.1, I1349_cp1.2)) ∧ intTest pI1349 (runFrom pI1349 (fmask pI1349) (cmask pI1349) (hmask pI1349) 954 395 (true, I1349_cp1.1, I1349_cp1.2)) 1349 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1349_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1349_fin) true) I1349_seg1) (by decide) rfl I1349_fin intTest_fst
theorem link1349 : linkOK pL1349 pH1349 pI1349 = true := by decide +kernel
theorem cvx1349 : ConvexBetweenHumps 1349 :=
  cvx_of L1349_ok H1349_ok I1349_ok link1349 (by decide)

/-! ### `N = 1350` -/

def pL1350 : Prm := ⟨79, 37, 39, 1352, 11, 18446744073709551616, 135551711190356561, 135551711190356561⟩
def pH1350 : Prm := ⟨79, 37, 39, 1352, 11, 18446744073709551616, 135552810701984337, 135552810701984337⟩
def pI1350 : Prm := ⟨65, 33, 29, 1352, 11, 18446744073709551616, 135551711190356561, 135552810701984337⟩
noncomputable def L1350_cp1 : Nat × Nat := t7val% (fastRun pL1350 1 954 (init pL1350) (init pL1350))
theorem L1350_seg1 : segOK pL1350 1 954 (init pL1350) (init pL1350) L1350_cp1.1 L1350_cp1.2 = true := by
  decide +kernel
theorem L1350_fin : (prmOK pL1350 1350 && ptTest pL1350 (runFrom pL1350 (fmask pL1350) (cmask pL1350) (hmask pL1350) 955 395 (true, L1350_cp1.1, L1350_cp1.2)) 1350 675 false) = true := by
  decide +kernel
theorem L1350_ok : RunOK pL1350 1350 (runFrom pL1350 (fmask pL1350) (cmask pL1350) (hmask pL1350) 955 395 (true, L1350_cp1.1, L1350_cp1.2)) ∧ ptTest pL1350 (runFrom pL1350 (fmask pL1350) (cmask pL1350) (hmask pL1350) 955 395 (true, L1350_cp1.1, L1350_cp1.2)) 1350 675 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1350_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1350_fin) true) L1350_seg1) (by decide) rfl L1350_fin ptTest_fst
noncomputable def H1350_cp1 : Nat × Nat := t7val% (fastRun pH1350 1 954 (init pH1350) (init pH1350))
theorem H1350_seg1 : segOK pH1350 1 954 (init pH1350) (init pH1350) H1350_cp1.1 H1350_cp1.2 = true := by
  decide +kernel
theorem H1350_fin : (prmOK pH1350 1350 && ptTest pH1350 (runFrom pH1350 (fmask pH1350) (cmask pH1350) (hmask pH1350) 955 395 (true, H1350_cp1.1, H1350_cp1.2)) 1350 675 true) = true := by
  decide +kernel
theorem H1350_ok : RunOK pH1350 1350 (runFrom pH1350 (fmask pH1350) (cmask pH1350) (hmask pH1350) 955 395 (true, H1350_cp1.1, H1350_cp1.2)) ∧ ptTest pH1350 (runFrom pH1350 (fmask pH1350) (cmask pH1350) (hmask pH1350) 955 395 (true, H1350_cp1.1, H1350_cp1.2)) 1350 675 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1350_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1350_fin) true) H1350_seg1) (by decide) rfl H1350_fin ptTest_fst
noncomputable def I1350_cp1 : Nat × Nat := t7val% (fastRun pI1350 1 954 (init pI1350) (init pI1350))
theorem I1350_seg1 : segOK pI1350 1 954 (init pI1350) (init pI1350) I1350_cp1.1 I1350_cp1.2 = true := by
  decide +kernel
theorem I1350_fin : (prmOK pI1350 1350 && intTest pI1350 (runFrom pI1350 (fmask pI1350) (cmask pI1350) (hmask pI1350) 955 395 (true, I1350_cp1.1, I1350_cp1.2)) 1350 20 true) = true := by
  decide +kernel
theorem I1350_ok : RunOK pI1350 1350 (runFrom pI1350 (fmask pI1350) (cmask pI1350) (hmask pI1350) 955 395 (true, I1350_cp1.1, I1350_cp1.2)) ∧ intTest pI1350 (runFrom pI1350 (fmask pI1350) (cmask pI1350) (hmask pI1350) 955 395 (true, I1350_cp1.1, I1350_cp1.2)) 1350 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1350_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1350_fin) true) I1350_seg1) (by decide) rfl I1350_fin intTest_fst
theorem link1350 : linkOK pL1350 pH1350 pI1350 = true := by decide +kernel
theorem cvx1350 : ConvexBetweenHumps 1350 :=
  cvx_of L1350_ok H1350_ok I1350_ok link1350 (by decide)
theorem cenlink1350 : cenLinkOK pI1350 1350 = true := by decide +kernel
theorem cen1350 : CenterUniqueMin 1350 ∧ DipHyp 1350 ∧ OnePointHyps 1350 :=
  cen_of L1350_ok H1350_ok I1350_ok link1350 cenlink1350

/-! ### `N = 1351` -/

def pL1351 : Prm := ⟨79, 37, 39, 1353, 11, 18446744073709551616, 135470418953505617, 135470418953505617⟩
def pH1351 : Prm := ⟨79, 37, 39, 1353, 11, 18446744073709551616, 135471518465133393, 135471518465133393⟩
def pI1351 : Prm := ⟨65, 33, 29, 1353, 11, 18446744073709551616, 135470418953505617, 135471518465133393⟩
noncomputable def L1351_cp1 : Nat × Nat := t7val% (fastRun pL1351 1 954 (init pL1351) (init pL1351))
theorem L1351_seg1 : segOK pL1351 1 954 (init pL1351) (init pL1351) L1351_cp1.1 L1351_cp1.2 = true := by
  decide +kernel
theorem L1351_fin : (prmOK pL1351 1351 && ptTest pL1351 (runFrom pL1351 (fmask pL1351) (cmask pL1351) (hmask pL1351) 955 396 (true, L1351_cp1.1, L1351_cp1.2)) 1351 676 false) = true := by
  decide +kernel
theorem L1351_ok : RunOK pL1351 1351 (runFrom pL1351 (fmask pL1351) (cmask pL1351) (hmask pL1351) 955 396 (true, L1351_cp1.1, L1351_cp1.2)) ∧ ptTest pL1351 (runFrom pL1351 (fmask pL1351) (cmask pL1351) (hmask pL1351) 955 396 (true, L1351_cp1.1, L1351_cp1.2)) 1351 676 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1351_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1351_fin) true) L1351_seg1) (by decide) rfl L1351_fin ptTest_fst
noncomputable def H1351_cp1 : Nat × Nat := t7val% (fastRun pH1351 1 954 (init pH1351) (init pH1351))
theorem H1351_seg1 : segOK pH1351 1 954 (init pH1351) (init pH1351) H1351_cp1.1 H1351_cp1.2 = true := by
  decide +kernel
theorem H1351_fin : (prmOK pH1351 1351 && ptTest pH1351 (runFrom pH1351 (fmask pH1351) (cmask pH1351) (hmask pH1351) 955 396 (true, H1351_cp1.1, H1351_cp1.2)) 1351 676 true) = true := by
  decide +kernel
theorem H1351_ok : RunOK pH1351 1351 (runFrom pH1351 (fmask pH1351) (cmask pH1351) (hmask pH1351) 955 396 (true, H1351_cp1.1, H1351_cp1.2)) ∧ ptTest pH1351 (runFrom pH1351 (fmask pH1351) (cmask pH1351) (hmask pH1351) 955 396 (true, H1351_cp1.1, H1351_cp1.2)) 1351 676 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1351_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1351_fin) true) H1351_seg1) (by decide) rfl H1351_fin ptTest_fst
noncomputable def I1351_cp1 : Nat × Nat := t7val% (fastRun pI1351 1 954 (init pI1351) (init pI1351))
theorem I1351_seg1 : segOK pI1351 1 954 (init pI1351) (init pI1351) I1351_cp1.1 I1351_cp1.2 = true := by
  decide +kernel
theorem I1351_fin : (prmOK pI1351 1351 && intTest pI1351 (runFrom pI1351 (fmask pI1351) (cmask pI1351) (hmask pI1351) 955 396 (true, I1351_cp1.1, I1351_cp1.2)) 1351 20 false) = true := by
  decide +kernel
theorem I1351_ok : RunOK pI1351 1351 (runFrom pI1351 (fmask pI1351) (cmask pI1351) (hmask pI1351) 955 396 (true, I1351_cp1.1, I1351_cp1.2)) ∧ intTest pI1351 (runFrom pI1351 (fmask pI1351) (cmask pI1351) (hmask pI1351) 955 396 (true, I1351_cp1.1, I1351_cp1.2)) 1351 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1351_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1351_fin) true) I1351_seg1) (by decide) rfl I1351_fin intTest_fst
theorem link1351 : linkOK pL1351 pH1351 pI1351 = true := by decide +kernel
theorem cvx1351 : ConvexBetweenHumps 1351 :=
  cvx_of L1351_ok H1351_ok I1351_ok link1351 (by decide)

/-! ### `N = 1352` -/

def pL1352 : Prm := ⟨79, 37, 39, 1354, 11, 18446744073709551616, 135389278972741396, 135389278972741396⟩
def pH1352 : Prm := ⟨79, 37, 39, 1354, 11, 18446744073709551616, 135390378484369172, 135390378484369172⟩
def pI1352 : Prm := ⟨65, 33, 29, 1354, 11, 18446744073709551616, 135389278972741396, 135390378484369172⟩
noncomputable def L1352_cp1 : Nat × Nat := t7val% (fastRun pL1352 1 955 (init pL1352) (init pL1352))
theorem L1352_seg1 : segOK pL1352 1 955 (init pL1352) (init pL1352) L1352_cp1.1 L1352_cp1.2 = true := by
  decide +kernel
theorem L1352_fin : (prmOK pL1352 1352 && ptTest pL1352 (runFrom pL1352 (fmask pL1352) (cmask pL1352) (hmask pL1352) 956 396 (true, L1352_cp1.1, L1352_cp1.2)) 1352 676 false) = true := by
  decide +kernel
theorem L1352_ok : RunOK pL1352 1352 (runFrom pL1352 (fmask pL1352) (cmask pL1352) (hmask pL1352) 956 396 (true, L1352_cp1.1, L1352_cp1.2)) ∧ ptTest pL1352 (runFrom pL1352 (fmask pL1352) (cmask pL1352) (hmask pL1352) 956 396 (true, L1352_cp1.1, L1352_cp1.2)) 1352 676 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1352_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1352_fin) true) L1352_seg1) (by decide) rfl L1352_fin ptTest_fst
noncomputable def H1352_cp1 : Nat × Nat := t7val% (fastRun pH1352 1 955 (init pH1352) (init pH1352))
theorem H1352_seg1 : segOK pH1352 1 955 (init pH1352) (init pH1352) H1352_cp1.1 H1352_cp1.2 = true := by
  decide +kernel
theorem H1352_fin : (prmOK pH1352 1352 && ptTest pH1352 (runFrom pH1352 (fmask pH1352) (cmask pH1352) (hmask pH1352) 956 396 (true, H1352_cp1.1, H1352_cp1.2)) 1352 676 true) = true := by
  decide +kernel
theorem H1352_ok : RunOK pH1352 1352 (runFrom pH1352 (fmask pH1352) (cmask pH1352) (hmask pH1352) 956 396 (true, H1352_cp1.1, H1352_cp1.2)) ∧ ptTest pH1352 (runFrom pH1352 (fmask pH1352) (cmask pH1352) (hmask pH1352) 956 396 (true, H1352_cp1.1, H1352_cp1.2)) 1352 676 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1352_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1352_fin) true) H1352_seg1) (by decide) rfl H1352_fin ptTest_fst
noncomputable def I1352_cp1 : Nat × Nat := t7val% (fastRun pI1352 1 955 (init pI1352) (init pI1352))
theorem I1352_seg1 : segOK pI1352 1 955 (init pI1352) (init pI1352) I1352_cp1.1 I1352_cp1.2 = true := by
  decide +kernel
theorem I1352_fin : (prmOK pI1352 1352 && intTest pI1352 (runFrom pI1352 (fmask pI1352) (cmask pI1352) (hmask pI1352) 956 396 (true, I1352_cp1.1, I1352_cp1.2)) 1352 20 true) = true := by
  decide +kernel
theorem I1352_ok : RunOK pI1352 1352 (runFrom pI1352 (fmask pI1352) (cmask pI1352) (hmask pI1352) 956 396 (true, I1352_cp1.1, I1352_cp1.2)) ∧ intTest pI1352 (runFrom pI1352 (fmask pI1352) (cmask pI1352) (hmask pI1352) 956 396 (true, I1352_cp1.1, I1352_cp1.2)) 1352 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1352_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1352_fin) true) I1352_seg1) (by decide) rfl I1352_fin intTest_fst
theorem link1352 : linkOK pL1352 pH1352 pI1352 = true := by decide +kernel
theorem cvx1352 : ConvexBetweenHumps 1352 :=
  cvx_of L1352_ok H1352_ok I1352_ok link1352 (by decide)
theorem cenlink1352 : cenLinkOK pI1352 1352 = true := by decide +kernel
theorem cen1352 : CenterUniqueMin 1352 ∧ DipHyp 1352 ∧ OnePointHyps 1352 :=
  cen_of L1352_ok H1352_ok I1352_ok link1352 cenlink1352

/-! ### `N = 1353` -/

def pL1353 : Prm := ⟨79, 37, 39, 1355, 11, 18446744073709551616, 135308198847769432, 135308198847769432⟩
def pH1353 : Prm := ⟨79, 37, 39, 1355, 11, 18446744073709551616, 135309298359397208, 135309298359397208⟩
def pI1353 : Prm := ⟨65, 33, 29, 1355, 11, 18446744073709551616, 135308198847769432, 135309298359397208⟩
noncomputable def L1353_cp1 : Nat × Nat := t7val% (fastRun pL1353 1 956 (init pL1353) (init pL1353))
theorem L1353_seg1 : segOK pL1353 1 956 (init pL1353) (init pL1353) L1353_cp1.1 L1353_cp1.2 = true := by
  decide +kernel
theorem L1353_fin : (prmOK pL1353 1353 && ptTest pL1353 (runFrom pL1353 (fmask pL1353) (cmask pL1353) (hmask pL1353) 957 396 (true, L1353_cp1.1, L1353_cp1.2)) 1353 677 false) = true := by
  decide +kernel
theorem L1353_ok : RunOK pL1353 1353 (runFrom pL1353 (fmask pL1353) (cmask pL1353) (hmask pL1353) 957 396 (true, L1353_cp1.1, L1353_cp1.2)) ∧ ptTest pL1353 (runFrom pL1353 (fmask pL1353) (cmask pL1353) (hmask pL1353) 957 396 (true, L1353_cp1.1, L1353_cp1.2)) 1353 677 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1353_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1353_fin) true) L1353_seg1) (by decide) rfl L1353_fin ptTest_fst
noncomputable def H1353_cp1 : Nat × Nat := t7val% (fastRun pH1353 1 956 (init pH1353) (init pH1353))
theorem H1353_seg1 : segOK pH1353 1 956 (init pH1353) (init pH1353) H1353_cp1.1 H1353_cp1.2 = true := by
  decide +kernel
theorem H1353_fin : (prmOK pH1353 1353 && ptTest pH1353 (runFrom pH1353 (fmask pH1353) (cmask pH1353) (hmask pH1353) 957 396 (true, H1353_cp1.1, H1353_cp1.2)) 1353 677 true) = true := by
  decide +kernel
theorem H1353_ok : RunOK pH1353 1353 (runFrom pH1353 (fmask pH1353) (cmask pH1353) (hmask pH1353) 957 396 (true, H1353_cp1.1, H1353_cp1.2)) ∧ ptTest pH1353 (runFrom pH1353 (fmask pH1353) (cmask pH1353) (hmask pH1353) 957 396 (true, H1353_cp1.1, H1353_cp1.2)) 1353 677 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1353_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1353_fin) true) H1353_seg1) (by decide) rfl H1353_fin ptTest_fst
noncomputable def I1353_cp1 : Nat × Nat := t7val% (fastRun pI1353 1 956 (init pI1353) (init pI1353))
theorem I1353_seg1 : segOK pI1353 1 956 (init pI1353) (init pI1353) I1353_cp1.1 I1353_cp1.2 = true := by
  decide +kernel
theorem I1353_fin : (prmOK pI1353 1353 && intTest pI1353 (runFrom pI1353 (fmask pI1353) (cmask pI1353) (hmask pI1353) 957 396 (true, I1353_cp1.1, I1353_cp1.2)) 1353 20 false) = true := by
  decide +kernel
theorem I1353_ok : RunOK pI1353 1353 (runFrom pI1353 (fmask pI1353) (cmask pI1353) (hmask pI1353) 957 396 (true, I1353_cp1.1, I1353_cp1.2)) ∧ intTest pI1353 (runFrom pI1353 (fmask pI1353) (cmask pI1353) (hmask pI1353) 957 396 (true, I1353_cp1.1, I1353_cp1.2)) 1353 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1353_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1353_fin) true) I1353_seg1) (by decide) rfl I1353_fin intTest_fst
theorem link1353 : linkOK pL1353 pH1353 pI1353 = true := by decide +kernel
theorem cvx1353 : ConvexBetweenHumps 1353 :=
  cvx_of L1353_ok H1353_ok I1353_ok link1353 (by decide)

/-! ### `N = 1354` -/

def pL1354 : Prm := ⟨79, 37, 39, 1356, 11, 18446744073709551616, 135227270342822009, 135227270342822009⟩
def pH1354 : Prm := ⟨79, 37, 39, 1356, 11, 18446744073709551616, 135228369854449785, 135228369854449785⟩
def pI1354 : Prm := ⟨65, 33, 29, 1356, 11, 18446744073709551616, 135227270342822009, 135228369854449785⟩
noncomputable def L1354_cp1 : Nat × Nat := t7val% (fastRun pL1354 1 956 (init pL1354) (init pL1354))
theorem L1354_seg1 : segOK pL1354 1 956 (init pL1354) (init pL1354) L1354_cp1.1 L1354_cp1.2 = true := by
  decide +kernel
theorem L1354_fin : (prmOK pL1354 1354 && ptTest pL1354 (runFrom pL1354 (fmask pL1354) (cmask pL1354) (hmask pL1354) 957 397 (true, L1354_cp1.1, L1354_cp1.2)) 1354 677 false) = true := by
  decide +kernel
theorem L1354_ok : RunOK pL1354 1354 (runFrom pL1354 (fmask pL1354) (cmask pL1354) (hmask pL1354) 957 397 (true, L1354_cp1.1, L1354_cp1.2)) ∧ ptTest pL1354 (runFrom pL1354 (fmask pL1354) (cmask pL1354) (hmask pL1354) 957 397 (true, L1354_cp1.1, L1354_cp1.2)) 1354 677 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1354_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1354_fin) true) L1354_seg1) (by decide) rfl L1354_fin ptTest_fst
noncomputable def H1354_cp1 : Nat × Nat := t7val% (fastRun pH1354 1 956 (init pH1354) (init pH1354))
theorem H1354_seg1 : segOK pH1354 1 956 (init pH1354) (init pH1354) H1354_cp1.1 H1354_cp1.2 = true := by
  decide +kernel
theorem H1354_fin : (prmOK pH1354 1354 && ptTest pH1354 (runFrom pH1354 (fmask pH1354) (cmask pH1354) (hmask pH1354) 957 397 (true, H1354_cp1.1, H1354_cp1.2)) 1354 677 true) = true := by
  decide +kernel
theorem H1354_ok : RunOK pH1354 1354 (runFrom pH1354 (fmask pH1354) (cmask pH1354) (hmask pH1354) 957 397 (true, H1354_cp1.1, H1354_cp1.2)) ∧ ptTest pH1354 (runFrom pH1354 (fmask pH1354) (cmask pH1354) (hmask pH1354) 957 397 (true, H1354_cp1.1, H1354_cp1.2)) 1354 677 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1354_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1354_fin) true) H1354_seg1) (by decide) rfl H1354_fin ptTest_fst
noncomputable def I1354_cp1 : Nat × Nat := t7val% (fastRun pI1354 1 956 (init pI1354) (init pI1354))
theorem I1354_seg1 : segOK pI1354 1 956 (init pI1354) (init pI1354) I1354_cp1.1 I1354_cp1.2 = true := by
  decide +kernel
theorem I1354_fin : (prmOK pI1354 1354 && intTest pI1354 (runFrom pI1354 (fmask pI1354) (cmask pI1354) (hmask pI1354) 957 397 (true, I1354_cp1.1, I1354_cp1.2)) 1354 20 true) = true := by
  decide +kernel
theorem I1354_ok : RunOK pI1354 1354 (runFrom pI1354 (fmask pI1354) (cmask pI1354) (hmask pI1354) 957 397 (true, I1354_cp1.1, I1354_cp1.2)) ∧ intTest pI1354 (runFrom pI1354 (fmask pI1354) (cmask pI1354) (hmask pI1354) 957 397 (true, I1354_cp1.1, I1354_cp1.2)) 1354 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1354_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1354_fin) true) I1354_seg1) (by decide) rfl I1354_fin intTest_fst
theorem link1354 : linkOK pL1354 pH1354 pI1354 = true := by decide +kernel
theorem cvx1354 : ConvexBetweenHumps 1354 :=
  cvx_of L1354_ok H1354_ok I1354_ok link1354 (by decide)
theorem cenlink1354 : cenLinkOK pI1354 1354 = true := by decide +kernel
theorem cen1354 : CenterUniqueMin 1354 ∧ DipHyp 1354 ∧ OnePointHyps 1354 :=
  cen_of L1354_ok H1354_ok I1354_ok link1354 cenlink1354

/-! ### `N = 1355` -/

def pL1355 : Prm := ⟨79, 37, 39, 1357, 11, 18446744073709551616, 135146401473670972, 135146401473670972⟩
def pH1355 : Prm := ⟨79, 37, 39, 1357, 11, 18446744073709551616, 135147500985298748, 135147500985298748⟩
def pI1355 : Prm := ⟨65, 33, 29, 1357, 11, 18446744073709551616, 135146401473670972, 135147500985298748⟩
noncomputable def L1355_cp1 : Nat × Nat := t7val% (fastRun pL1355 1 957 (init pL1355) (init pL1355))
theorem L1355_seg1 : segOK pL1355 1 957 (init pL1355) (init pL1355) L1355_cp1.1 L1355_cp1.2 = true := by
  decide +kernel
theorem L1355_fin : (prmOK pL1355 1355 && ptTest pL1355 (runFrom pL1355 (fmask pL1355) (cmask pL1355) (hmask pL1355) 958 397 (true, L1355_cp1.1, L1355_cp1.2)) 1355 678 false) = true := by
  decide +kernel
theorem L1355_ok : RunOK pL1355 1355 (runFrom pL1355 (fmask pL1355) (cmask pL1355) (hmask pL1355) 958 397 (true, L1355_cp1.1, L1355_cp1.2)) ∧ ptTest pL1355 (runFrom pL1355 (fmask pL1355) (cmask pL1355) (hmask pL1355) 958 397 (true, L1355_cp1.1, L1355_cp1.2)) 1355 678 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1355_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1355_fin) true) L1355_seg1) (by decide) rfl L1355_fin ptTest_fst
noncomputable def H1355_cp1 : Nat × Nat := t7val% (fastRun pH1355 1 957 (init pH1355) (init pH1355))
theorem H1355_seg1 : segOK pH1355 1 957 (init pH1355) (init pH1355) H1355_cp1.1 H1355_cp1.2 = true := by
  decide +kernel
theorem H1355_fin : (prmOK pH1355 1355 && ptTest pH1355 (runFrom pH1355 (fmask pH1355) (cmask pH1355) (hmask pH1355) 958 397 (true, H1355_cp1.1, H1355_cp1.2)) 1355 678 true) = true := by
  decide +kernel
theorem H1355_ok : RunOK pH1355 1355 (runFrom pH1355 (fmask pH1355) (cmask pH1355) (hmask pH1355) 958 397 (true, H1355_cp1.1, H1355_cp1.2)) ∧ ptTest pH1355 (runFrom pH1355 (fmask pH1355) (cmask pH1355) (hmask pH1355) 958 397 (true, H1355_cp1.1, H1355_cp1.2)) 1355 678 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1355_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1355_fin) true) H1355_seg1) (by decide) rfl H1355_fin ptTest_fst
noncomputable def I1355_cp1 : Nat × Nat := t7val% (fastRun pI1355 1 957 (init pI1355) (init pI1355))
theorem I1355_seg1 : segOK pI1355 1 957 (init pI1355) (init pI1355) I1355_cp1.1 I1355_cp1.2 = true := by
  decide +kernel
theorem I1355_fin : (prmOK pI1355 1355 && intTest pI1355 (runFrom pI1355 (fmask pI1355) (cmask pI1355) (hmask pI1355) 958 397 (true, I1355_cp1.1, I1355_cp1.2)) 1355 20 false) = true := by
  decide +kernel
theorem I1355_ok : RunOK pI1355 1355 (runFrom pI1355 (fmask pI1355) (cmask pI1355) (hmask pI1355) 958 397 (true, I1355_cp1.1, I1355_cp1.2)) ∧ intTest pI1355 (runFrom pI1355 (fmask pI1355) (cmask pI1355) (hmask pI1355) 958 397 (true, I1355_cp1.1, I1355_cp1.2)) 1355 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1355_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1355_fin) true) I1355_seg1) (by decide) rfl I1355_fin intTest_fst
theorem link1355 : linkOK pL1355 pH1355 pI1355 = true := by decide +kernel
theorem cvx1355 : ConvexBetweenHumps 1355 :=
  cvx_of L1355_ok H1355_ok I1355_ok link1355 (by decide)

/-! ### `N = 1356` -/

def pL1356 : Prm := ⟨79, 37, 39, 1358, 11, 18446744073709551616, 135065683592042516, 135065683592042516⟩
def pH1356 : Prm := ⟨79, 37, 39, 1358, 11, 18446744073709551616, 135066783103670292, 135066783103670292⟩
def pI1356 : Prm := ⟨65, 33, 29, 1358, 11, 18446744073709551616, 135065683592042516, 135066783103670292⟩
noncomputable def L1356_cp1 : Nat × Nat := t7val% (fastRun pL1356 1 958 (init pL1356) (init pL1356))
theorem L1356_seg1 : segOK pL1356 1 958 (init pL1356) (init pL1356) L1356_cp1.1 L1356_cp1.2 = true := by
  decide +kernel
theorem L1356_fin : (prmOK pL1356 1356 && ptTest pL1356 (runFrom pL1356 (fmask pL1356) (cmask pL1356) (hmask pL1356) 959 397 (true, L1356_cp1.1, L1356_cp1.2)) 1356 678 false) = true := by
  decide +kernel
theorem L1356_ok : RunOK pL1356 1356 (runFrom pL1356 (fmask pL1356) (cmask pL1356) (hmask pL1356) 959 397 (true, L1356_cp1.1, L1356_cp1.2)) ∧ ptTest pL1356 (runFrom pL1356 (fmask pL1356) (cmask pL1356) (hmask pL1356) 959 397 (true, L1356_cp1.1, L1356_cp1.2)) 1356 678 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1356_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1356_fin) true) L1356_seg1) (by decide) rfl L1356_fin ptTest_fst
noncomputable def H1356_cp1 : Nat × Nat := t7val% (fastRun pH1356 1 958 (init pH1356) (init pH1356))
theorem H1356_seg1 : segOK pH1356 1 958 (init pH1356) (init pH1356) H1356_cp1.1 H1356_cp1.2 = true := by
  decide +kernel
theorem H1356_fin : (prmOK pH1356 1356 && ptTest pH1356 (runFrom pH1356 (fmask pH1356) (cmask pH1356) (hmask pH1356) 959 397 (true, H1356_cp1.1, H1356_cp1.2)) 1356 678 true) = true := by
  decide +kernel
theorem H1356_ok : RunOK pH1356 1356 (runFrom pH1356 (fmask pH1356) (cmask pH1356) (hmask pH1356) 959 397 (true, H1356_cp1.1, H1356_cp1.2)) ∧ ptTest pH1356 (runFrom pH1356 (fmask pH1356) (cmask pH1356) (hmask pH1356) 959 397 (true, H1356_cp1.1, H1356_cp1.2)) 1356 678 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1356_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1356_fin) true) H1356_seg1) (by decide) rfl H1356_fin ptTest_fst
noncomputable def I1356_cp1 : Nat × Nat := t7val% (fastRun pI1356 1 958 (init pI1356) (init pI1356))
theorem I1356_seg1 : segOK pI1356 1 958 (init pI1356) (init pI1356) I1356_cp1.1 I1356_cp1.2 = true := by
  decide +kernel
theorem I1356_fin : (prmOK pI1356 1356 && intTest pI1356 (runFrom pI1356 (fmask pI1356) (cmask pI1356) (hmask pI1356) 959 397 (true, I1356_cp1.1, I1356_cp1.2)) 1356 20 true) = true := by
  decide +kernel
theorem I1356_ok : RunOK pI1356 1356 (runFrom pI1356 (fmask pI1356) (cmask pI1356) (hmask pI1356) 959 397 (true, I1356_cp1.1, I1356_cp1.2)) ∧ intTest pI1356 (runFrom pI1356 (fmask pI1356) (cmask pI1356) (hmask pI1356) 959 397 (true, I1356_cp1.1, I1356_cp1.2)) 1356 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1356_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1356_fin) true) I1356_seg1) (by decide) rfl I1356_fin intTest_fst
theorem link1356 : linkOK pL1356 pH1356 pI1356 = true := by decide +kernel
theorem cvx1356 : ConvexBetweenHumps 1356 :=
  cvx_of L1356_ok H1356_ok I1356_ok link1356 (by decide)
theorem cenlink1356 : cenLinkOK pI1356 1356 = true := by decide +kernel
theorem cen1356 : CenterUniqueMin 1356 ∧ DipHyp 1356 ∧ OnePointHyps 1356 :=
  cen_of L1356_ok H1356_ok I1356_ok link1356 cenlink1356

/-! ### `N = 1357` -/

def pL1357 : Prm := ⟨79, 37, 39, 1359, 11, 18446744073709551616, 134985025127284487, 134985025127284487⟩
def pH1357 : Prm := ⟨79, 37, 39, 1359, 11, 18446744073709551616, 134986124638912263, 134986124638912263⟩
def pI1357 : Prm := ⟨65, 33, 29, 1359, 11, 18446744073709551616, 134985025127284487, 134986124638912263⟩
noncomputable def L1357_cp1 : Nat × Nat := t7val% (fastRun pL1357 1 959 (init pL1357) (init pL1357))
theorem L1357_seg1 : segOK pL1357 1 959 (init pL1357) (init pL1357) L1357_cp1.1 L1357_cp1.2 = true := by
  decide +kernel
theorem L1357_fin : (prmOK pL1357 1357 && ptTest pL1357 (runFrom pL1357 (fmask pL1357) (cmask pL1357) (hmask pL1357) 960 397 (true, L1357_cp1.1, L1357_cp1.2)) 1357 679 false) = true := by
  decide +kernel
theorem L1357_ok : RunOK pL1357 1357 (runFrom pL1357 (fmask pL1357) (cmask pL1357) (hmask pL1357) 960 397 (true, L1357_cp1.1, L1357_cp1.2)) ∧ ptTest pL1357 (runFrom pL1357 (fmask pL1357) (cmask pL1357) (hmask pL1357) 960 397 (true, L1357_cp1.1, L1357_cp1.2)) 1357 679 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1357_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1357_fin) true) L1357_seg1) (by decide) rfl L1357_fin ptTest_fst
noncomputable def H1357_cp1 : Nat × Nat := t7val% (fastRun pH1357 1 959 (init pH1357) (init pH1357))
theorem H1357_seg1 : segOK pH1357 1 959 (init pH1357) (init pH1357) H1357_cp1.1 H1357_cp1.2 = true := by
  decide +kernel
theorem H1357_fin : (prmOK pH1357 1357 && ptTest pH1357 (runFrom pH1357 (fmask pH1357) (cmask pH1357) (hmask pH1357) 960 397 (true, H1357_cp1.1, H1357_cp1.2)) 1357 679 true) = true := by
  decide +kernel
theorem H1357_ok : RunOK pH1357 1357 (runFrom pH1357 (fmask pH1357) (cmask pH1357) (hmask pH1357) 960 397 (true, H1357_cp1.1, H1357_cp1.2)) ∧ ptTest pH1357 (runFrom pH1357 (fmask pH1357) (cmask pH1357) (hmask pH1357) 960 397 (true, H1357_cp1.1, H1357_cp1.2)) 1357 679 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1357_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1357_fin) true) H1357_seg1) (by decide) rfl H1357_fin ptTest_fst
noncomputable def I1357_cp1 : Nat × Nat := t7val% (fastRun pI1357 1 959 (init pI1357) (init pI1357))
theorem I1357_seg1 : segOK pI1357 1 959 (init pI1357) (init pI1357) I1357_cp1.1 I1357_cp1.2 = true := by
  decide +kernel
theorem I1357_fin : (prmOK pI1357 1357 && intTest pI1357 (runFrom pI1357 (fmask pI1357) (cmask pI1357) (hmask pI1357) 960 397 (true, I1357_cp1.1, I1357_cp1.2)) 1357 20 false) = true := by
  decide +kernel
theorem I1357_ok : RunOK pI1357 1357 (runFrom pI1357 (fmask pI1357) (cmask pI1357) (hmask pI1357) 960 397 (true, I1357_cp1.1, I1357_cp1.2)) ∧ intTest pI1357 (runFrom pI1357 (fmask pI1357) (cmask pI1357) (hmask pI1357) 960 397 (true, I1357_cp1.1, I1357_cp1.2)) 1357 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1357_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1357_fin) true) I1357_seg1) (by decide) rfl I1357_fin intTest_fst
theorem link1357 : linkOK pL1357 pH1357 pI1357 = true := by decide +kernel
theorem cvx1357 : ConvexBetweenHumps 1357 :=
  cvx_of L1357_ok H1357_ok I1357_ok link1357 (by decide)

/-! ### `N = 1358` -/

def pL1358 : Prm := ⟨79, 37, 39, 1360, 11, 18446744073709551616, 134904517021162640, 134904517021162640⟩
def pH1358 : Prm := ⟨79, 37, 39, 1360, 11, 18446744073709551616, 134905616532790416, 134905616532790416⟩
def pI1358 : Prm := ⟨65, 33, 29, 1360, 11, 18446744073709551616, 134904517021162640, 134905616532790416⟩
noncomputable def L1358_cp1 : Nat × Nat := t7val% (fastRun pL1358 1 959 (init pL1358) (init pL1358))
theorem L1358_seg1 : segOK pL1358 1 959 (init pL1358) (init pL1358) L1358_cp1.1 L1358_cp1.2 = true := by
  decide +kernel
theorem L1358_fin : (prmOK pL1358 1358 && ptTest pL1358 (runFrom pL1358 (fmask pL1358) (cmask pL1358) (hmask pL1358) 960 398 (true, L1358_cp1.1, L1358_cp1.2)) 1358 679 false) = true := by
  decide +kernel
theorem L1358_ok : RunOK pL1358 1358 (runFrom pL1358 (fmask pL1358) (cmask pL1358) (hmask pL1358) 960 398 (true, L1358_cp1.1, L1358_cp1.2)) ∧ ptTest pL1358 (runFrom pL1358 (fmask pL1358) (cmask pL1358) (hmask pL1358) 960 398 (true, L1358_cp1.1, L1358_cp1.2)) 1358 679 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1358_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1358_fin) true) L1358_seg1) (by decide) rfl L1358_fin ptTest_fst
noncomputable def H1358_cp1 : Nat × Nat := t7val% (fastRun pH1358 1 959 (init pH1358) (init pH1358))
theorem H1358_seg1 : segOK pH1358 1 959 (init pH1358) (init pH1358) H1358_cp1.1 H1358_cp1.2 = true := by
  decide +kernel
theorem H1358_fin : (prmOK pH1358 1358 && ptTest pH1358 (runFrom pH1358 (fmask pH1358) (cmask pH1358) (hmask pH1358) 960 398 (true, H1358_cp1.1, H1358_cp1.2)) 1358 679 true) = true := by
  decide +kernel
theorem H1358_ok : RunOK pH1358 1358 (runFrom pH1358 (fmask pH1358) (cmask pH1358) (hmask pH1358) 960 398 (true, H1358_cp1.1, H1358_cp1.2)) ∧ ptTest pH1358 (runFrom pH1358 (fmask pH1358) (cmask pH1358) (hmask pH1358) 960 398 (true, H1358_cp1.1, H1358_cp1.2)) 1358 679 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1358_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1358_fin) true) H1358_seg1) (by decide) rfl H1358_fin ptTest_fst
noncomputable def I1358_cp1 : Nat × Nat := t7val% (fastRun pI1358 1 959 (init pI1358) (init pI1358))
theorem I1358_seg1 : segOK pI1358 1 959 (init pI1358) (init pI1358) I1358_cp1.1 I1358_cp1.2 = true := by
  decide +kernel
theorem I1358_fin : (prmOK pI1358 1358 && intTest pI1358 (runFrom pI1358 (fmask pI1358) (cmask pI1358) (hmask pI1358) 960 398 (true, I1358_cp1.1, I1358_cp1.2)) 1358 20 true) = true := by
  decide +kernel
theorem I1358_ok : RunOK pI1358 1358 (runFrom pI1358 (fmask pI1358) (cmask pI1358) (hmask pI1358) 960 398 (true, I1358_cp1.1, I1358_cp1.2)) ∧ intTest pI1358 (runFrom pI1358 (fmask pI1358) (cmask pI1358) (hmask pI1358) 960 398 (true, I1358_cp1.1, I1358_cp1.2)) 1358 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1358_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1358_fin) true) I1358_seg1) (by decide) rfl I1358_fin intTest_fst
theorem link1358 : linkOK pL1358 pH1358 pI1358 = true := by decide +kernel
theorem cvx1358 : ConvexBetweenHumps 1358 :=
  cvx_of L1358_ok H1358_ok I1358_ok link1358 (by decide)
theorem cenlink1358 : cenLinkOK pI1358 1358 = true := by decide +kernel
theorem cen1358 : CenterUniqueMin 1358 ∧ DipHyp 1358 ∧ OnePointHyps 1358 :=
  cen_of L1358_ok H1358_ok I1358_ok link1358 cenlink1358

/-! ### `N = 1359` -/

def pL1359 : Prm := ⟨79, 37, 39, 1361, 11, 18446744073709551616, 134824068114073620, 134824068114073620⟩
def pH1359 : Prm := ⟨79, 37, 39, 1361, 11, 18446744073709551616, 134825167625701396, 134825167625701396⟩
def pI1359 : Prm := ⟨65, 33, 29, 1361, 11, 18446744073709551616, 134824068114073620, 134825167625701396⟩
noncomputable def L1359_cp1 : Nat × Nat := t7val% (fastRun pL1359 1 960 (init pL1359) (init pL1359))
theorem L1359_seg1 : segOK pL1359 1 960 (init pL1359) (init pL1359) L1359_cp1.1 L1359_cp1.2 = true := by
  decide +kernel
theorem L1359_fin : (prmOK pL1359 1359 && ptTest pL1359 (runFrom pL1359 (fmask pL1359) (cmask pL1359) (hmask pL1359) 961 398 (true, L1359_cp1.1, L1359_cp1.2)) 1359 680 false) = true := by
  decide +kernel
theorem L1359_ok : RunOK pL1359 1359 (runFrom pL1359 (fmask pL1359) (cmask pL1359) (hmask pL1359) 961 398 (true, L1359_cp1.1, L1359_cp1.2)) ∧ ptTest pL1359 (runFrom pL1359 (fmask pL1359) (cmask pL1359) (hmask pL1359) 961 398 (true, L1359_cp1.1, L1359_cp1.2)) 1359 680 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1359_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1359_fin) true) L1359_seg1) (by decide) rfl L1359_fin ptTest_fst
noncomputable def H1359_cp1 : Nat × Nat := t7val% (fastRun pH1359 1 960 (init pH1359) (init pH1359))
theorem H1359_seg1 : segOK pH1359 1 960 (init pH1359) (init pH1359) H1359_cp1.1 H1359_cp1.2 = true := by
  decide +kernel
theorem H1359_fin : (prmOK pH1359 1359 && ptTest pH1359 (runFrom pH1359 (fmask pH1359) (cmask pH1359) (hmask pH1359) 961 398 (true, H1359_cp1.1, H1359_cp1.2)) 1359 680 true) = true := by
  decide +kernel
theorem H1359_ok : RunOK pH1359 1359 (runFrom pH1359 (fmask pH1359) (cmask pH1359) (hmask pH1359) 961 398 (true, H1359_cp1.1, H1359_cp1.2)) ∧ ptTest pH1359 (runFrom pH1359 (fmask pH1359) (cmask pH1359) (hmask pH1359) 961 398 (true, H1359_cp1.1, H1359_cp1.2)) 1359 680 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1359_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1359_fin) true) H1359_seg1) (by decide) rfl H1359_fin ptTest_fst
noncomputable def I1359_cp1 : Nat × Nat := t7val% (fastRun pI1359 1 960 (init pI1359) (init pI1359))
theorem I1359_seg1 : segOK pI1359 1 960 (init pI1359) (init pI1359) I1359_cp1.1 I1359_cp1.2 = true := by
  decide +kernel
theorem I1359_fin : (prmOK pI1359 1359 && intTest pI1359 (runFrom pI1359 (fmask pI1359) (cmask pI1359) (hmask pI1359) 961 398 (true, I1359_cp1.1, I1359_cp1.2)) 1359 20 false) = true := by
  decide +kernel
theorem I1359_ok : RunOK pI1359 1359 (runFrom pI1359 (fmask pI1359) (cmask pI1359) (hmask pI1359) 961 398 (true, I1359_cp1.1, I1359_cp1.2)) ∧ intTest pI1359 (runFrom pI1359 (fmask pI1359) (cmask pI1359) (hmask pI1359) 961 398 (true, I1359_cp1.1, I1359_cp1.2)) 1359 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1359_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1359_fin) true) I1359_seg1) (by decide) rfl I1359_fin intTest_fst
theorem link1359 : linkOK pL1359 pH1359 pI1359 = true := by decide +kernel
theorem cvx1359 : ConvexBetweenHumps 1359 :=
  cvx_of L1359_ok H1359_ok I1359_ok link1359 (by decide)

/-! ### The range -/

theorem cvx_1338_1359 {N : ℕ} (h1 : 1338 ≤ N) (h2 : N ≤ 1359) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1348
  · by_cases h4 : N ≤ 1342
    · by_cases h6 : N ≤ 1339
      · by_cases h8 : N ≤ 1338
        · obtain rfl : N = 1338 := by omega
          exact cvx1338
        · obtain rfl : N = 1339 := by omega
          exact cvx1339
      · by_cases h8 : N ≤ 1340
        · obtain rfl : N = 1340 := by omega
          exact cvx1340
        · by_cases h10 : N ≤ 1341
          · obtain rfl : N = 1341 := by omega
            exact cvx1341
          · obtain rfl : N = 1342 := by omega
            exact cvx1342
    · by_cases h6 : N ≤ 1345
      · by_cases h8 : N ≤ 1343
        · obtain rfl : N = 1343 := by omega
          exact cvx1343
        · by_cases h10 : N ≤ 1344
          · obtain rfl : N = 1344 := by omega
            exact cvx1344
          · obtain rfl : N = 1345 := by omega
            exact cvx1345
      · by_cases h8 : N ≤ 1346
        · obtain rfl : N = 1346 := by omega
          exact cvx1346
        · by_cases h10 : N ≤ 1347
          · obtain rfl : N = 1347 := by omega
            exact cvx1347
          · obtain rfl : N = 1348 := by omega
            exact cvx1348
  · by_cases h4 : N ≤ 1353
    · by_cases h6 : N ≤ 1350
      · by_cases h8 : N ≤ 1349
        · obtain rfl : N = 1349 := by omega
          exact cvx1349
        · obtain rfl : N = 1350 := by omega
          exact cvx1350
      · by_cases h8 : N ≤ 1351
        · obtain rfl : N = 1351 := by omega
          exact cvx1351
        · by_cases h10 : N ≤ 1352
          · obtain rfl : N = 1352 := by omega
            exact cvx1352
          · obtain rfl : N = 1353 := by omega
            exact cvx1353
    · by_cases h6 : N ≤ 1356
      · by_cases h8 : N ≤ 1354
        · obtain rfl : N = 1354 := by omega
          exact cvx1354
        · by_cases h10 : N ≤ 1355
          · obtain rfl : N = 1355 := by omega
            exact cvx1355
          · obtain rfl : N = 1356 := by omega
            exact cvx1356
      · by_cases h8 : N ≤ 1357
        · obtain rfl : N = 1357 := by omega
          exact cvx1357
        · by_cases h10 : N ≤ 1358
          · obtain rfl : N = 1358 := by omega
            exact cvx1358
          · obtain rfl : N = 1359 := by omega
            exact cvx1359

theorem cen_1338_1359 {N : ℕ} (h1 : 1338 ≤ N) (h2 : N ≤ 1359) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1346
  · by_cases h4 : N ≤ 1340
    · by_cases h6 : N ≤ 1338
      · obtain rfl : N = 1338 := by omega
        exact cen1338
      · obtain rfl : N = 1340 := by omega
        exact cen1340
    · by_cases h6 : N ≤ 1342
      · obtain rfl : N = 1342 := by omega
        exact cen1342
      · by_cases h8 : N ≤ 1344
        · obtain rfl : N = 1344 := by omega
          exact cen1344
        · obtain rfl : N = 1346 := by omega
          exact cen1346
  · by_cases h4 : N ≤ 1352
    · by_cases h6 : N ≤ 1348
      · obtain rfl : N = 1348 := by omega
        exact cen1348
      · by_cases h8 : N ≤ 1350
        · obtain rfl : N = 1350 := by omega
          exact cen1350
        · obtain rfl : N = 1352 := by omega
          exact cen1352
    · by_cases h6 : N ≤ 1354
      · obtain rfl : N = 1354 := by omega
        exact cen1354
      · by_cases h8 : N ≤ 1356
        · obtain rfl : N = 1356 := by omega
          exact cen1356
        · obtain rfl : N = 1358 := by omega
          exact cen1358

end Kagey131.PaperD.T7
