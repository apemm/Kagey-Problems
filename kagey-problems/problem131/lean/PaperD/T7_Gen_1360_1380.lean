import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1360, …, 1380` (generated)

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

/-! ### `N = 1360` -/

def pL1360 : Prm := ⟨79, 37, 39, 1362, 11, 18446744073709551616, 134743768940220817, 134743768940220817⟩
def pH1360 : Prm := ⟨79, 37, 39, 1362, 11, 18446744073709551616, 134744868451848593, 134744868451848593⟩
def pI1360 : Prm := ⟨65, 33, 29, 1362, 11, 18446744073709551616, 134743768940220817, 134744868451848593⟩
noncomputable def L1360_cp1 : Nat × Nat := t7val% (fastRun pL1360 1 961 (init pL1360) (init pL1360))
theorem L1360_seg1 : segOK pL1360 1 961 (init pL1360) (init pL1360) L1360_cp1.1 L1360_cp1.2 = true := by
  decide +kernel
theorem L1360_fin : (prmOK pL1360 1360 && ptTest pL1360 (runFrom pL1360 (fmask pL1360) (cmask pL1360) (hmask pL1360) 962 398 (true, L1360_cp1.1, L1360_cp1.2)) 1360 680 false) = true := by
  decide +kernel
theorem L1360_ok : RunOK pL1360 1360 (runFrom pL1360 (fmask pL1360) (cmask pL1360) (hmask pL1360) 962 398 (true, L1360_cp1.1, L1360_cp1.2)) ∧ ptTest pL1360 (runFrom pL1360 (fmask pL1360) (cmask pL1360) (hmask pL1360) 962 398 (true, L1360_cp1.1, L1360_cp1.2)) 1360 680 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1360_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1360_fin) true) L1360_seg1) (by decide) rfl L1360_fin ptTest_fst
noncomputable def H1360_cp1 : Nat × Nat := t7val% (fastRun pH1360 1 961 (init pH1360) (init pH1360))
theorem H1360_seg1 : segOK pH1360 1 961 (init pH1360) (init pH1360) H1360_cp1.1 H1360_cp1.2 = true := by
  decide +kernel
theorem H1360_fin : (prmOK pH1360 1360 && ptTest pH1360 (runFrom pH1360 (fmask pH1360) (cmask pH1360) (hmask pH1360) 962 398 (true, H1360_cp1.1, H1360_cp1.2)) 1360 680 true) = true := by
  decide +kernel
theorem H1360_ok : RunOK pH1360 1360 (runFrom pH1360 (fmask pH1360) (cmask pH1360) (hmask pH1360) 962 398 (true, H1360_cp1.1, H1360_cp1.2)) ∧ ptTest pH1360 (runFrom pH1360 (fmask pH1360) (cmask pH1360) (hmask pH1360) 962 398 (true, H1360_cp1.1, H1360_cp1.2)) 1360 680 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1360_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1360_fin) true) H1360_seg1) (by decide) rfl H1360_fin ptTest_fst
noncomputable def I1360_cp1 : Nat × Nat := t7val% (fastRun pI1360 1 961 (init pI1360) (init pI1360))
theorem I1360_seg1 : segOK pI1360 1 961 (init pI1360) (init pI1360) I1360_cp1.1 I1360_cp1.2 = true := by
  decide +kernel
theorem I1360_fin : (prmOK pI1360 1360 && intTest pI1360 (runFrom pI1360 (fmask pI1360) (cmask pI1360) (hmask pI1360) 962 398 (true, I1360_cp1.1, I1360_cp1.2)) 1360 20 true) = true := by
  decide +kernel
theorem I1360_ok : RunOK pI1360 1360 (runFrom pI1360 (fmask pI1360) (cmask pI1360) (hmask pI1360) 962 398 (true, I1360_cp1.1, I1360_cp1.2)) ∧ intTest pI1360 (runFrom pI1360 (fmask pI1360) (cmask pI1360) (hmask pI1360) 962 398 (true, I1360_cp1.1, I1360_cp1.2)) 1360 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1360_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1360_fin) true) I1360_seg1) (by decide) rfl I1360_fin intTest_fst
theorem link1360 : linkOK pL1360 pH1360 pI1360 = true := by decide +kernel
theorem cvx1360 : ConvexBetweenHumps 1360 :=
  cvx_of L1360_ok H1360_ok I1360_ok link1360 (by decide)
theorem cenlink1360 : cenLinkOK pI1360 1360 = true := by decide +kernel
theorem cen1360 : CenterUniqueMin 1360 ∧ DipHyp 1360 ∧ OnePointHyps 1360 :=
  cen_of L1360_ok H1360_ok I1360_ok link1360 cenlink1360

/-! ### `N = 1361` -/

def pL1361 : Prm := ⟨79, 37, 39, 1363, 11, 18446744073709551616, 134663528748688492, 134663528748688492⟩
def pH1361 : Prm := ⟨79, 37, 39, 1363, 11, 18446744073709551616, 134664628260316268, 134664628260316268⟩
def pI1361 : Prm := ⟨65, 33, 29, 1363, 11, 18446744073709551616, 134663528748688492, 134664628260316268⟩
noncomputable def L1361_cp1 : Nat × Nat := t7val% (fastRun pL1361 1 961 (init pL1361) (init pL1361))
theorem L1361_seg1 : segOK pL1361 1 961 (init pL1361) (init pL1361) L1361_cp1.1 L1361_cp1.2 = true := by
  decide +kernel
theorem L1361_fin : (prmOK pL1361 1361 && ptTest pL1361 (runFrom pL1361 (fmask pL1361) (cmask pL1361) (hmask pL1361) 962 399 (true, L1361_cp1.1, L1361_cp1.2)) 1361 681 false) = true := by
  decide +kernel
theorem L1361_ok : RunOK pL1361 1361 (runFrom pL1361 (fmask pL1361) (cmask pL1361) (hmask pL1361) 962 399 (true, L1361_cp1.1, L1361_cp1.2)) ∧ ptTest pL1361 (runFrom pL1361 (fmask pL1361) (cmask pL1361) (hmask pL1361) 962 399 (true, L1361_cp1.1, L1361_cp1.2)) 1361 681 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1361_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1361_fin) true) L1361_seg1) (by decide) rfl L1361_fin ptTest_fst
noncomputable def H1361_cp1 : Nat × Nat := t7val% (fastRun pH1361 1 961 (init pH1361) (init pH1361))
theorem H1361_seg1 : segOK pH1361 1 961 (init pH1361) (init pH1361) H1361_cp1.1 H1361_cp1.2 = true := by
  decide +kernel
theorem H1361_fin : (prmOK pH1361 1361 && ptTest pH1361 (runFrom pH1361 (fmask pH1361) (cmask pH1361) (hmask pH1361) 962 399 (true, H1361_cp1.1, H1361_cp1.2)) 1361 681 true) = true := by
  decide +kernel
theorem H1361_ok : RunOK pH1361 1361 (runFrom pH1361 (fmask pH1361) (cmask pH1361) (hmask pH1361) 962 399 (true, H1361_cp1.1, H1361_cp1.2)) ∧ ptTest pH1361 (runFrom pH1361 (fmask pH1361) (cmask pH1361) (hmask pH1361) 962 399 (true, H1361_cp1.1, H1361_cp1.2)) 1361 681 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1361_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1361_fin) true) H1361_seg1) (by decide) rfl H1361_fin ptTest_fst
noncomputable def I1361_cp1 : Nat × Nat := t7val% (fastRun pI1361 1 961 (init pI1361) (init pI1361))
theorem I1361_seg1 : segOK pI1361 1 961 (init pI1361) (init pI1361) I1361_cp1.1 I1361_cp1.2 = true := by
  decide +kernel
theorem I1361_fin : (prmOK pI1361 1361 && intTest pI1361 (runFrom pI1361 (fmask pI1361) (cmask pI1361) (hmask pI1361) 962 399 (true, I1361_cp1.1, I1361_cp1.2)) 1361 20 false) = true := by
  decide +kernel
theorem I1361_ok : RunOK pI1361 1361 (runFrom pI1361 (fmask pI1361) (cmask pI1361) (hmask pI1361) 962 399 (true, I1361_cp1.1, I1361_cp1.2)) ∧ intTest pI1361 (runFrom pI1361 (fmask pI1361) (cmask pI1361) (hmask pI1361) 962 399 (true, I1361_cp1.1, I1361_cp1.2)) 1361 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1361_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1361_fin) true) I1361_seg1) (by decide) rfl I1361_fin intTest_fst
theorem link1361 : linkOK pL1361 pH1361 pI1361 = true := by decide +kernel
theorem cvx1361 : ConvexBetweenHumps 1361 :=
  cvx_of L1361_ok H1361_ok I1361_ok link1361 (by decide)

/-! ### `N = 1362` -/

def pL1362 : Prm := ⟨79, 37, 39, 1364, 11, 18446744073709551616, 134583437668497301, 134583437668497301⟩
def pH1362 : Prm := ⟨79, 37, 39, 1364, 11, 18446744073709551616, 134584537180125077, 134584537180125077⟩
def pI1362 : Prm := ⟨65, 33, 29, 1364, 11, 18446744073709551616, 134583437668497301, 134584537180125077⟩
noncomputable def L1362_cp1 : Nat × Nat := t7val% (fastRun pL1362 1 962 (init pL1362) (init pL1362))
theorem L1362_seg1 : segOK pL1362 1 962 (init pL1362) (init pL1362) L1362_cp1.1 L1362_cp1.2 = true := by
  decide +kernel
theorem L1362_fin : (prmOK pL1362 1362 && ptTest pL1362 (runFrom pL1362 (fmask pL1362) (cmask pL1362) (hmask pL1362) 963 399 (true, L1362_cp1.1, L1362_cp1.2)) 1362 681 false) = true := by
  decide +kernel
theorem L1362_ok : RunOK pL1362 1362 (runFrom pL1362 (fmask pL1362) (cmask pL1362) (hmask pL1362) 963 399 (true, L1362_cp1.1, L1362_cp1.2)) ∧ ptTest pL1362 (runFrom pL1362 (fmask pL1362) (cmask pL1362) (hmask pL1362) 963 399 (true, L1362_cp1.1, L1362_cp1.2)) 1362 681 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1362_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1362_fin) true) L1362_seg1) (by decide) rfl L1362_fin ptTest_fst
noncomputable def H1362_cp1 : Nat × Nat := t7val% (fastRun pH1362 1 962 (init pH1362) (init pH1362))
theorem H1362_seg1 : segOK pH1362 1 962 (init pH1362) (init pH1362) H1362_cp1.1 H1362_cp1.2 = true := by
  decide +kernel
theorem H1362_fin : (prmOK pH1362 1362 && ptTest pH1362 (runFrom pH1362 (fmask pH1362) (cmask pH1362) (hmask pH1362) 963 399 (true, H1362_cp1.1, H1362_cp1.2)) 1362 681 true) = true := by
  decide +kernel
theorem H1362_ok : RunOK pH1362 1362 (runFrom pH1362 (fmask pH1362) (cmask pH1362) (hmask pH1362) 963 399 (true, H1362_cp1.1, H1362_cp1.2)) ∧ ptTest pH1362 (runFrom pH1362 (fmask pH1362) (cmask pH1362) (hmask pH1362) 963 399 (true, H1362_cp1.1, H1362_cp1.2)) 1362 681 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1362_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1362_fin) true) H1362_seg1) (by decide) rfl H1362_fin ptTest_fst
noncomputable def I1362_cp1 : Nat × Nat := t7val% (fastRun pI1362 1 962 (init pI1362) (init pI1362))
theorem I1362_seg1 : segOK pI1362 1 962 (init pI1362) (init pI1362) I1362_cp1.1 I1362_cp1.2 = true := by
  decide +kernel
theorem I1362_fin : (prmOK pI1362 1362 && intTest pI1362 (runFrom pI1362 (fmask pI1362) (cmask pI1362) (hmask pI1362) 963 399 (true, I1362_cp1.1, I1362_cp1.2)) 1362 20 true) = true := by
  decide +kernel
theorem I1362_ok : RunOK pI1362 1362 (runFrom pI1362 (fmask pI1362) (cmask pI1362) (hmask pI1362) 963 399 (true, I1362_cp1.1, I1362_cp1.2)) ∧ intTest pI1362 (runFrom pI1362 (fmask pI1362) (cmask pI1362) (hmask pI1362) 963 399 (true, I1362_cp1.1, I1362_cp1.2)) 1362 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1362_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1362_fin) true) I1362_seg1) (by decide) rfl I1362_fin intTest_fst
theorem link1362 : linkOK pL1362 pH1362 pI1362 = true := by decide +kernel
theorem cvx1362 : ConvexBetweenHumps 1362 :=
  cvx_of L1362_ok H1362_ok I1362_ok link1362 (by decide)
theorem cenlink1362 : cenLinkOK pI1362 1362 = true := by decide +kernel
theorem cen1362 : CenterUniqueMin 1362 ∧ DipHyp 1362 ∧ OnePointHyps 1362 :=
  cen_of L1362_ok H1362_ok I1362_ok link1362 cenlink1362

/-! ### `N = 1363` -/

def pL1363 : Prm := ⟨79, 37, 39, 1365, 11, 18446744073709551616, 134503405354928810, 134503405354928810⟩
def pH1363 : Prm := ⟨79, 37, 39, 1365, 11, 18446744073709551616, 134504504866556586, 134504504866556586⟩
def pI1363 : Prm := ⟨65, 33, 29, 1365, 11, 18446744073709551616, 134503405354928810, 134504504866556586⟩
noncomputable def L1363_cp1 : Nat × Nat := t7val% (fastRun pL1363 1 963 (init pL1363) (init pL1363))
theorem L1363_seg1 : segOK pL1363 1 963 (init pL1363) (init pL1363) L1363_cp1.1 L1363_cp1.2 = true := by
  decide +kernel
theorem L1363_fin : (prmOK pL1363 1363 && ptTest pL1363 (runFrom pL1363 (fmask pL1363) (cmask pL1363) (hmask pL1363) 964 399 (true, L1363_cp1.1, L1363_cp1.2)) 1363 682 false) = true := by
  decide +kernel
theorem L1363_ok : RunOK pL1363 1363 (runFrom pL1363 (fmask pL1363) (cmask pL1363) (hmask pL1363) 964 399 (true, L1363_cp1.1, L1363_cp1.2)) ∧ ptTest pL1363 (runFrom pL1363 (fmask pL1363) (cmask pL1363) (hmask pL1363) 964 399 (true, L1363_cp1.1, L1363_cp1.2)) 1363 682 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1363_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1363_fin) true) L1363_seg1) (by decide) rfl L1363_fin ptTest_fst
noncomputable def H1363_cp1 : Nat × Nat := t7val% (fastRun pH1363 1 963 (init pH1363) (init pH1363))
theorem H1363_seg1 : segOK pH1363 1 963 (init pH1363) (init pH1363) H1363_cp1.1 H1363_cp1.2 = true := by
  decide +kernel
theorem H1363_fin : (prmOK pH1363 1363 && ptTest pH1363 (runFrom pH1363 (fmask pH1363) (cmask pH1363) (hmask pH1363) 964 399 (true, H1363_cp1.1, H1363_cp1.2)) 1363 682 true) = true := by
  decide +kernel
theorem H1363_ok : RunOK pH1363 1363 (runFrom pH1363 (fmask pH1363) (cmask pH1363) (hmask pH1363) 964 399 (true, H1363_cp1.1, H1363_cp1.2)) ∧ ptTest pH1363 (runFrom pH1363 (fmask pH1363) (cmask pH1363) (hmask pH1363) 964 399 (true, H1363_cp1.1, H1363_cp1.2)) 1363 682 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1363_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1363_fin) true) H1363_seg1) (by decide) rfl H1363_fin ptTest_fst
noncomputable def I1363_cp1 : Nat × Nat := t7val% (fastRun pI1363 1 963 (init pI1363) (init pI1363))
theorem I1363_seg1 : segOK pI1363 1 963 (init pI1363) (init pI1363) I1363_cp1.1 I1363_cp1.2 = true := by
  decide +kernel
theorem I1363_fin : (prmOK pI1363 1363 && intTest pI1363 (runFrom pI1363 (fmask pI1363) (cmask pI1363) (hmask pI1363) 964 399 (true, I1363_cp1.1, I1363_cp1.2)) 1363 20 false) = true := by
  decide +kernel
theorem I1363_ok : RunOK pI1363 1363 (runFrom pI1363 (fmask pI1363) (cmask pI1363) (hmask pI1363) 964 399 (true, I1363_cp1.1, I1363_cp1.2)) ∧ intTest pI1363 (runFrom pI1363 (fmask pI1363) (cmask pI1363) (hmask pI1363) 964 399 (true, I1363_cp1.1, I1363_cp1.2)) 1363 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1363_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1363_fin) true) I1363_seg1) (by decide) rfl I1363_fin intTest_fst
theorem link1363 : linkOK pL1363 pH1363 pI1363 = true := by decide +kernel
theorem cvx1363 : ConvexBetweenHumps 1363 :=
  cvx_of L1363_ok H1363_ok I1363_ok link1363 (by decide)

/-! ### `N = 1364` -/

def pL1364 : Prm := ⟨79, 37, 39, 1366, 11, 18446744073709551616, 134423521534348144, 134423521534348144⟩
def pH1364 : Prm := ⟨79, 37, 39, 1366, 11, 18446744073709551616, 134424621045975920, 134424621045975920⟩
def pI1364 : Prm := ⟨65, 33, 29, 1366, 11, 18446744073709551616, 134423521534348144, 134424621045975920⟩
noncomputable def L1364_cp1 : Nat × Nat := t7val% (fastRun pL1364 1 963 (init pL1364) (init pL1364))
theorem L1364_seg1 : segOK pL1364 1 963 (init pL1364) (init pL1364) L1364_cp1.1 L1364_cp1.2 = true := by
  decide +kernel
theorem L1364_fin : (prmOK pL1364 1364 && ptTest pL1364 (runFrom pL1364 (fmask pL1364) (cmask pL1364) (hmask pL1364) 964 400 (true, L1364_cp1.1, L1364_cp1.2)) 1364 682 false) = true := by
  decide +kernel
theorem L1364_ok : RunOK pL1364 1364 (runFrom pL1364 (fmask pL1364) (cmask pL1364) (hmask pL1364) 964 400 (true, L1364_cp1.1, L1364_cp1.2)) ∧ ptTest pL1364 (runFrom pL1364 (fmask pL1364) (cmask pL1364) (hmask pL1364) 964 400 (true, L1364_cp1.1, L1364_cp1.2)) 1364 682 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1364_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1364_fin) true) L1364_seg1) (by decide) rfl L1364_fin ptTest_fst
noncomputable def H1364_cp1 : Nat × Nat := t7val% (fastRun pH1364 1 963 (init pH1364) (init pH1364))
theorem H1364_seg1 : segOK pH1364 1 963 (init pH1364) (init pH1364) H1364_cp1.1 H1364_cp1.2 = true := by
  decide +kernel
theorem H1364_fin : (prmOK pH1364 1364 && ptTest pH1364 (runFrom pH1364 (fmask pH1364) (cmask pH1364) (hmask pH1364) 964 400 (true, H1364_cp1.1, H1364_cp1.2)) 1364 682 true) = true := by
  decide +kernel
theorem H1364_ok : RunOK pH1364 1364 (runFrom pH1364 (fmask pH1364) (cmask pH1364) (hmask pH1364) 964 400 (true, H1364_cp1.1, H1364_cp1.2)) ∧ ptTest pH1364 (runFrom pH1364 (fmask pH1364) (cmask pH1364) (hmask pH1364) 964 400 (true, H1364_cp1.1, H1364_cp1.2)) 1364 682 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1364_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1364_fin) true) H1364_seg1) (by decide) rfl H1364_fin ptTest_fst
noncomputable def I1364_cp1 : Nat × Nat := t7val% (fastRun pI1364 1 963 (init pI1364) (init pI1364))
theorem I1364_seg1 : segOK pI1364 1 963 (init pI1364) (init pI1364) I1364_cp1.1 I1364_cp1.2 = true := by
  decide +kernel
theorem I1364_fin : (prmOK pI1364 1364 && intTest pI1364 (runFrom pI1364 (fmask pI1364) (cmask pI1364) (hmask pI1364) 964 400 (true, I1364_cp1.1, I1364_cp1.2)) 1364 20 true) = true := by
  decide +kernel
theorem I1364_ok : RunOK pI1364 1364 (runFrom pI1364 (fmask pI1364) (cmask pI1364) (hmask pI1364) 964 400 (true, I1364_cp1.1, I1364_cp1.2)) ∧ intTest pI1364 (runFrom pI1364 (fmask pI1364) (cmask pI1364) (hmask pI1364) 964 400 (true, I1364_cp1.1, I1364_cp1.2)) 1364 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1364_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1364_fin) true) I1364_seg1) (by decide) rfl I1364_fin intTest_fst
theorem link1364 : linkOK pL1364 pH1364 pI1364 = true := by decide +kernel
theorem cvx1364 : ConvexBetweenHumps 1364 :=
  cvx_of L1364_ok H1364_ok I1364_ok link1364 (by decide)
theorem cenlink1364 : cenLinkOK pI1364 1364 = true := by decide +kernel
theorem cen1364 : CenterUniqueMin 1364 ∧ DipHyp 1364 ∧ OnePointHyps 1364 :=
  cen_of L1364_ok H1364_ok I1364_ok link1364 cenlink1364

/-! ### `N = 1365` -/

def pL1365 : Prm := ⟨79, 37, 39, 1367, 11, 18446744073709551616, 134343696265780757, 134343696265780757⟩
def pH1365 : Prm := ⟨79, 37, 39, 1367, 11, 18446744073709551616, 134344795777408533, 134344795777408533⟩
def pI1365 : Prm := ⟨65, 33, 29, 1367, 11, 18446744073709551616, 134343696265780757, 134344795777408533⟩
noncomputable def L1365_cp1 : Nat × Nat := t7val% (fastRun pL1365 1 964 (init pL1365) (init pL1365))
theorem L1365_seg1 : segOK pL1365 1 964 (init pL1365) (init pL1365) L1365_cp1.1 L1365_cp1.2 = true := by
  decide +kernel
theorem L1365_fin : (prmOK pL1365 1365 && ptTest pL1365 (runFrom pL1365 (fmask pL1365) (cmask pL1365) (hmask pL1365) 965 400 (true, L1365_cp1.1, L1365_cp1.2)) 1365 683 false) = true := by
  decide +kernel
theorem L1365_ok : RunOK pL1365 1365 (runFrom pL1365 (fmask pL1365) (cmask pL1365) (hmask pL1365) 965 400 (true, L1365_cp1.1, L1365_cp1.2)) ∧ ptTest pL1365 (runFrom pL1365 (fmask pL1365) (cmask pL1365) (hmask pL1365) 965 400 (true, L1365_cp1.1, L1365_cp1.2)) 1365 683 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1365_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1365_fin) true) L1365_seg1) (by decide) rfl L1365_fin ptTest_fst
noncomputable def H1365_cp1 : Nat × Nat := t7val% (fastRun pH1365 1 964 (init pH1365) (init pH1365))
theorem H1365_seg1 : segOK pH1365 1 964 (init pH1365) (init pH1365) H1365_cp1.1 H1365_cp1.2 = true := by
  decide +kernel
theorem H1365_fin : (prmOK pH1365 1365 && ptTest pH1365 (runFrom pH1365 (fmask pH1365) (cmask pH1365) (hmask pH1365) 965 400 (true, H1365_cp1.1, H1365_cp1.2)) 1365 683 true) = true := by
  decide +kernel
theorem H1365_ok : RunOK pH1365 1365 (runFrom pH1365 (fmask pH1365) (cmask pH1365) (hmask pH1365) 965 400 (true, H1365_cp1.1, H1365_cp1.2)) ∧ ptTest pH1365 (runFrom pH1365 (fmask pH1365) (cmask pH1365) (hmask pH1365) 965 400 (true, H1365_cp1.1, H1365_cp1.2)) 1365 683 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1365_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1365_fin) true) H1365_seg1) (by decide) rfl H1365_fin ptTest_fst
noncomputable def I1365_cp1 : Nat × Nat := t7val% (fastRun pI1365 1 964 (init pI1365) (init pI1365))
theorem I1365_seg1 : segOK pI1365 1 964 (init pI1365) (init pI1365) I1365_cp1.1 I1365_cp1.2 = true := by
  decide +kernel
theorem I1365_fin : (prmOK pI1365 1365 && intTest pI1365 (runFrom pI1365 (fmask pI1365) (cmask pI1365) (hmask pI1365) 965 400 (true, I1365_cp1.1, I1365_cp1.2)) 1365 20 false) = true := by
  decide +kernel
theorem I1365_ok : RunOK pI1365 1365 (runFrom pI1365 (fmask pI1365) (cmask pI1365) (hmask pI1365) 965 400 (true, I1365_cp1.1, I1365_cp1.2)) ∧ intTest pI1365 (runFrom pI1365 (fmask pI1365) (cmask pI1365) (hmask pI1365) 965 400 (true, I1365_cp1.1, I1365_cp1.2)) 1365 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1365_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1365_fin) true) I1365_seg1) (by decide) rfl I1365_fin intTest_fst
theorem link1365 : linkOK pL1365 pH1365 pI1365 = true := by decide +kernel
theorem cvx1365 : ConvexBetweenHumps 1365 :=
  cvx_of L1365_ok H1365_ok I1365_ok link1365 (by decide)

/-! ### `N = 1366` -/

def pL1366 : Prm := ⟨79, 37, 39, 1368, 11, 18446744073709551616, 134264018875242089, 134264018875242089⟩
def pH1366 : Prm := ⟨79, 37, 39, 1368, 11, 18446744073709551616, 134265118386869865, 134265118386869865⟩
def pI1366 : Prm := ⟨65, 33, 29, 1368, 11, 18446744073709551616, 134264018875242089, 134265118386869865⟩
noncomputable def L1366_cp1 : Nat × Nat := t7val% (fastRun pL1366 1 965 (init pL1366) (init pL1366))
theorem L1366_seg1 : segOK pL1366 1 965 (init pL1366) (init pL1366) L1366_cp1.1 L1366_cp1.2 = true := by
  decide +kernel
theorem L1366_fin : (prmOK pL1366 1366 && ptTest pL1366 (runFrom pL1366 (fmask pL1366) (cmask pL1366) (hmask pL1366) 966 400 (true, L1366_cp1.1, L1366_cp1.2)) 1366 683 false) = true := by
  decide +kernel
theorem L1366_ok : RunOK pL1366 1366 (runFrom pL1366 (fmask pL1366) (cmask pL1366) (hmask pL1366) 966 400 (true, L1366_cp1.1, L1366_cp1.2)) ∧ ptTest pL1366 (runFrom pL1366 (fmask pL1366) (cmask pL1366) (hmask pL1366) 966 400 (true, L1366_cp1.1, L1366_cp1.2)) 1366 683 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1366_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1366_fin) true) L1366_seg1) (by decide) rfl L1366_fin ptTest_fst
noncomputable def H1366_cp1 : Nat × Nat := t7val% (fastRun pH1366 1 965 (init pH1366) (init pH1366))
theorem H1366_seg1 : segOK pH1366 1 965 (init pH1366) (init pH1366) H1366_cp1.1 H1366_cp1.2 = true := by
  decide +kernel
theorem H1366_fin : (prmOK pH1366 1366 && ptTest pH1366 (runFrom pH1366 (fmask pH1366) (cmask pH1366) (hmask pH1366) 966 400 (true, H1366_cp1.1, H1366_cp1.2)) 1366 683 true) = true := by
  decide +kernel
theorem H1366_ok : RunOK pH1366 1366 (runFrom pH1366 (fmask pH1366) (cmask pH1366) (hmask pH1366) 966 400 (true, H1366_cp1.1, H1366_cp1.2)) ∧ ptTest pH1366 (runFrom pH1366 (fmask pH1366) (cmask pH1366) (hmask pH1366) 966 400 (true, H1366_cp1.1, H1366_cp1.2)) 1366 683 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1366_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1366_fin) true) H1366_seg1) (by decide) rfl H1366_fin ptTest_fst
noncomputable def I1366_cp1 : Nat × Nat := t7val% (fastRun pI1366 1 965 (init pI1366) (init pI1366))
theorem I1366_seg1 : segOK pI1366 1 965 (init pI1366) (init pI1366) I1366_cp1.1 I1366_cp1.2 = true := by
  decide +kernel
theorem I1366_fin : (prmOK pI1366 1366 && intTest pI1366 (runFrom pI1366 (fmask pI1366) (cmask pI1366) (hmask pI1366) 966 400 (true, I1366_cp1.1, I1366_cp1.2)) 1366 20 true) = true := by
  decide +kernel
theorem I1366_ok : RunOK pI1366 1366 (runFrom pI1366 (fmask pI1366) (cmask pI1366) (hmask pI1366) 966 400 (true, I1366_cp1.1, I1366_cp1.2)) ∧ intTest pI1366 (runFrom pI1366 (fmask pI1366) (cmask pI1366) (hmask pI1366) 966 400 (true, I1366_cp1.1, I1366_cp1.2)) 1366 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1366_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1366_fin) true) I1366_seg1) (by decide) rfl I1366_fin intTest_fst
theorem link1366 : linkOK pL1366 pH1366 pI1366 = true := by decide +kernel
theorem cvx1366 : ConvexBetweenHumps 1366 :=
  cvx_of L1366_ok H1366_ok I1366_ok link1366 (by decide)
theorem cenlink1366 : cenLinkOK pI1366 1366 = true := by decide +kernel
theorem cen1366 : CenterUniqueMin 1366 ∧ DipHyp 1366 ∧ OnePointHyps 1366 :=
  cen_of L1366_ok H1366_ok I1366_ok link1366 cenlink1366

/-! ### `N = 1367` -/

def pL1367 : Prm := ⟨79, 37, 39, 1369, 11, 18446744073709551616, 134184399823232530, 134184399823232530⟩
def pH1367 : Prm := ⟨79, 37, 39, 1369, 11, 18446744073709551616, 134185499334860306, 134185499334860306⟩
def pI1367 : Prm := ⟨65, 33, 29, 1369, 11, 18446744073709551616, 134184399823232530, 134185499334860306⟩
noncomputable def L1367_cp1 : Nat × Nat := t7val% (fastRun pL1367 1 966 (init pL1367) (init pL1367))
theorem L1367_seg1 : segOK pL1367 1 966 (init pL1367) (init pL1367) L1367_cp1.1 L1367_cp1.2 = true := by
  decide +kernel
theorem L1367_fin : (prmOK pL1367 1367 && ptTest pL1367 (runFrom pL1367 (fmask pL1367) (cmask pL1367) (hmask pL1367) 967 400 (true, L1367_cp1.1, L1367_cp1.2)) 1367 684 false) = true := by
  decide +kernel
theorem L1367_ok : RunOK pL1367 1367 (runFrom pL1367 (fmask pL1367) (cmask pL1367) (hmask pL1367) 967 400 (true, L1367_cp1.1, L1367_cp1.2)) ∧ ptTest pL1367 (runFrom pL1367 (fmask pL1367) (cmask pL1367) (hmask pL1367) 967 400 (true, L1367_cp1.1, L1367_cp1.2)) 1367 684 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1367_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1367_fin) true) L1367_seg1) (by decide) rfl L1367_fin ptTest_fst
noncomputable def H1367_cp1 : Nat × Nat := t7val% (fastRun pH1367 1 966 (init pH1367) (init pH1367))
theorem H1367_seg1 : segOK pH1367 1 966 (init pH1367) (init pH1367) H1367_cp1.1 H1367_cp1.2 = true := by
  decide +kernel
theorem H1367_fin : (prmOK pH1367 1367 && ptTest pH1367 (runFrom pH1367 (fmask pH1367) (cmask pH1367) (hmask pH1367) 967 400 (true, H1367_cp1.1, H1367_cp1.2)) 1367 684 true) = true := by
  decide +kernel
theorem H1367_ok : RunOK pH1367 1367 (runFrom pH1367 (fmask pH1367) (cmask pH1367) (hmask pH1367) 967 400 (true, H1367_cp1.1, H1367_cp1.2)) ∧ ptTest pH1367 (runFrom pH1367 (fmask pH1367) (cmask pH1367) (hmask pH1367) 967 400 (true, H1367_cp1.1, H1367_cp1.2)) 1367 684 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1367_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1367_fin) true) H1367_seg1) (by decide) rfl H1367_fin ptTest_fst
noncomputable def I1367_cp1 : Nat × Nat := t7val% (fastRun pI1367 1 966 (init pI1367) (init pI1367))
theorem I1367_seg1 : segOK pI1367 1 966 (init pI1367) (init pI1367) I1367_cp1.1 I1367_cp1.2 = true := by
  decide +kernel
theorem I1367_fin : (prmOK pI1367 1367 && intTest pI1367 (runFrom pI1367 (fmask pI1367) (cmask pI1367) (hmask pI1367) 967 400 (true, I1367_cp1.1, I1367_cp1.2)) 1367 20 false) = true := by
  decide +kernel
theorem I1367_ok : RunOK pI1367 1367 (runFrom pI1367 (fmask pI1367) (cmask pI1367) (hmask pI1367) 967 400 (true, I1367_cp1.1, I1367_cp1.2)) ∧ intTest pI1367 (runFrom pI1367 (fmask pI1367) (cmask pI1367) (hmask pI1367) 967 400 (true, I1367_cp1.1, I1367_cp1.2)) 1367 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1367_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1367_fin) true) I1367_seg1) (by decide) rfl I1367_fin intTest_fst
theorem link1367 : linkOK pL1367 pH1367 pI1367 = true := by decide +kernel
theorem cvx1367 : ConvexBetweenHumps 1367 :=
  cvx_of L1367_ok H1367_ok I1367_ok link1367 (by decide)

/-! ### `N = 1368` -/

def pL1368 : Prm := ⟨79, 37, 39, 1370, 11, 18446744073709551616, 134104928037723677, 134104928037723677⟩
def pH1368 : Prm := ⟨79, 37, 39, 1370, 11, 18446744073709551616, 134106027549351453, 134106027549351453⟩
def pI1368 : Prm := ⟨66, 32, 31, 1370, 11, 18446744073709551616, 134104928037723677, 134106027549351453⟩
noncomputable def L1368_cp1 : Nat × Nat := t7val% (fastRun pL1368 1 966 (init pL1368) (init pL1368))
theorem L1368_seg1 : segOK pL1368 1 966 (init pL1368) (init pL1368) L1368_cp1.1 L1368_cp1.2 = true := by
  decide +kernel
theorem L1368_fin : (prmOK pL1368 1368 && ptTest pL1368 (runFrom pL1368 (fmask pL1368) (cmask pL1368) (hmask pL1368) 967 401 (true, L1368_cp1.1, L1368_cp1.2)) 1368 684 false) = true := by
  decide +kernel
theorem L1368_ok : RunOK pL1368 1368 (runFrom pL1368 (fmask pL1368) (cmask pL1368) (hmask pL1368) 967 401 (true, L1368_cp1.1, L1368_cp1.2)) ∧ ptTest pL1368 (runFrom pL1368 (fmask pL1368) (cmask pL1368) (hmask pL1368) 967 401 (true, L1368_cp1.1, L1368_cp1.2)) 1368 684 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1368_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1368_fin) true) L1368_seg1) (by decide) rfl L1368_fin ptTest_fst
noncomputable def H1368_cp1 : Nat × Nat := t7val% (fastRun pH1368 1 966 (init pH1368) (init pH1368))
theorem H1368_seg1 : segOK pH1368 1 966 (init pH1368) (init pH1368) H1368_cp1.1 H1368_cp1.2 = true := by
  decide +kernel
theorem H1368_fin : (prmOK pH1368 1368 && ptTest pH1368 (runFrom pH1368 (fmask pH1368) (cmask pH1368) (hmask pH1368) 967 401 (true, H1368_cp1.1, H1368_cp1.2)) 1368 684 true) = true := by
  decide +kernel
theorem H1368_ok : RunOK pH1368 1368 (runFrom pH1368 (fmask pH1368) (cmask pH1368) (hmask pH1368) 967 401 (true, H1368_cp1.1, H1368_cp1.2)) ∧ ptTest pH1368 (runFrom pH1368 (fmask pH1368) (cmask pH1368) (hmask pH1368) 967 401 (true, H1368_cp1.1, H1368_cp1.2)) 1368 684 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1368_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1368_fin) true) H1368_seg1) (by decide) rfl H1368_fin ptTest_fst
noncomputable def I1368_cp1 : Nat × Nat := t7val% (fastRun pI1368 1 966 (init pI1368) (init pI1368))
theorem I1368_seg1 : segOK pI1368 1 966 (init pI1368) (init pI1368) I1368_cp1.1 I1368_cp1.2 = true := by
  decide +kernel
theorem I1368_fin : (prmOK pI1368 1368 && intTest pI1368 (runFrom pI1368 (fmask pI1368) (cmask pI1368) (hmask pI1368) 967 401 (true, I1368_cp1.1, I1368_cp1.2)) 1368 20 true) = true := by
  decide +kernel
theorem I1368_ok : RunOK pI1368 1368 (runFrom pI1368 (fmask pI1368) (cmask pI1368) (hmask pI1368) 967 401 (true, I1368_cp1.1, I1368_cp1.2)) ∧ intTest pI1368 (runFrom pI1368 (fmask pI1368) (cmask pI1368) (hmask pI1368) 967 401 (true, I1368_cp1.1, I1368_cp1.2)) 1368 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1368_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1368_fin) true) I1368_seg1) (by decide) rfl I1368_fin intTest_fst
theorem link1368 : linkOK pL1368 pH1368 pI1368 = true := by decide +kernel
theorem cvx1368 : ConvexBetweenHumps 1368 :=
  cvx_of L1368_ok H1368_ok I1368_ok link1368 (by decide)
theorem cenlink1368 : cenLinkOK pI1368 1368 = true := by decide +kernel
theorem cen1368 : CenterUniqueMin 1368 ∧ DipHyp 1368 ∧ OnePointHyps 1368 :=
  cen_of L1368_ok H1368_ok I1368_ok link1368 cenlink1368

/-! ### `N = 1369` -/

def pL1369 : Prm := ⟨79, 37, 39, 1371, 11, 18446744073709551616, 134025514378237442, 134025514378237442⟩
def pH1369 : Prm := ⟨79, 37, 39, 1371, 11, 18446744073709551616, 134026613889865218, 134026613889865218⟩
def pI1369 : Prm := ⟨66, 32, 31, 1371, 11, 18446744073709551616, 134025514378237442, 134026613889865218⟩
noncomputable def L1369_cp1 : Nat × Nat := t7val% (fastRun pL1369 1 967 (init pL1369) (init pL1369))
theorem L1369_seg1 : segOK pL1369 1 967 (init pL1369) (init pL1369) L1369_cp1.1 L1369_cp1.2 = true := by
  decide +kernel
theorem L1369_fin : (prmOK pL1369 1369 && ptTest pL1369 (runFrom pL1369 (fmask pL1369) (cmask pL1369) (hmask pL1369) 968 401 (true, L1369_cp1.1, L1369_cp1.2)) 1369 685 false) = true := by
  decide +kernel
theorem L1369_ok : RunOK pL1369 1369 (runFrom pL1369 (fmask pL1369) (cmask pL1369) (hmask pL1369) 968 401 (true, L1369_cp1.1, L1369_cp1.2)) ∧ ptTest pL1369 (runFrom pL1369 (fmask pL1369) (cmask pL1369) (hmask pL1369) 968 401 (true, L1369_cp1.1, L1369_cp1.2)) 1369 685 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1369_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1369_fin) true) L1369_seg1) (by decide) rfl L1369_fin ptTest_fst
noncomputable def H1369_cp1 : Nat × Nat := t7val% (fastRun pH1369 1 967 (init pH1369) (init pH1369))
theorem H1369_seg1 : segOK pH1369 1 967 (init pH1369) (init pH1369) H1369_cp1.1 H1369_cp1.2 = true := by
  decide +kernel
theorem H1369_fin : (prmOK pH1369 1369 && ptTest pH1369 (runFrom pH1369 (fmask pH1369) (cmask pH1369) (hmask pH1369) 968 401 (true, H1369_cp1.1, H1369_cp1.2)) 1369 685 true) = true := by
  decide +kernel
theorem H1369_ok : RunOK pH1369 1369 (runFrom pH1369 (fmask pH1369) (cmask pH1369) (hmask pH1369) 968 401 (true, H1369_cp1.1, H1369_cp1.2)) ∧ ptTest pH1369 (runFrom pH1369 (fmask pH1369) (cmask pH1369) (hmask pH1369) 968 401 (true, H1369_cp1.1, H1369_cp1.2)) 1369 685 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1369_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1369_fin) true) H1369_seg1) (by decide) rfl H1369_fin ptTest_fst
noncomputable def I1369_cp1 : Nat × Nat := t7val% (fastRun pI1369 1 967 (init pI1369) (init pI1369))
theorem I1369_seg1 : segOK pI1369 1 967 (init pI1369) (init pI1369) I1369_cp1.1 I1369_cp1.2 = true := by
  decide +kernel
theorem I1369_fin : (prmOK pI1369 1369 && intTest pI1369 (runFrom pI1369 (fmask pI1369) (cmask pI1369) (hmask pI1369) 968 401 (true, I1369_cp1.1, I1369_cp1.2)) 1369 20 false) = true := by
  decide +kernel
theorem I1369_ok : RunOK pI1369 1369 (runFrom pI1369 (fmask pI1369) (cmask pI1369) (hmask pI1369) 968 401 (true, I1369_cp1.1, I1369_cp1.2)) ∧ intTest pI1369 (runFrom pI1369 (fmask pI1369) (cmask pI1369) (hmask pI1369) 968 401 (true, I1369_cp1.1, I1369_cp1.2)) 1369 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1369_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1369_fin) true) I1369_seg1) (by decide) rfl I1369_fin intTest_fst
theorem link1369 : linkOK pL1369 pH1369 pI1369 = true := by decide +kernel
theorem cvx1369 : ConvexBetweenHumps 1369 :=
  cvx_of L1369_ok H1369_ok I1369_ok link1369 (by decide)

/-! ### `N = 1370` -/

def pL1370 : Prm := ⟨79, 37, 39, 1372, 11, 18446744073709551616, 133946247377191888, 133946247377191888⟩
def pH1370 : Prm := ⟨79, 37, 39, 1372, 11, 18446744073709551616, 133947346888819664, 133947346888819664⟩
def pI1370 : Prm := ⟨66, 32, 31, 1372, 11, 18446744073709551616, 133946247377191888, 133947346888819664⟩
noncomputable def L1370_cp1 : Nat × Nat := t7val% (fastRun pL1370 1 968 (init pL1370) (init pL1370))
theorem L1370_seg1 : segOK pL1370 1 968 (init pL1370) (init pL1370) L1370_cp1.1 L1370_cp1.2 = true := by
  decide +kernel
theorem L1370_fin : (prmOK pL1370 1370 && ptTest pL1370 (runFrom pL1370 (fmask pL1370) (cmask pL1370) (hmask pL1370) 969 401 (true, L1370_cp1.1, L1370_cp1.2)) 1370 685 false) = true := by
  decide +kernel
theorem L1370_ok : RunOK pL1370 1370 (runFrom pL1370 (fmask pL1370) (cmask pL1370) (hmask pL1370) 969 401 (true, L1370_cp1.1, L1370_cp1.2)) ∧ ptTest pL1370 (runFrom pL1370 (fmask pL1370) (cmask pL1370) (hmask pL1370) 969 401 (true, L1370_cp1.1, L1370_cp1.2)) 1370 685 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1370_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1370_fin) true) L1370_seg1) (by decide) rfl L1370_fin ptTest_fst
noncomputable def H1370_cp1 : Nat × Nat := t7val% (fastRun pH1370 1 968 (init pH1370) (init pH1370))
theorem H1370_seg1 : segOK pH1370 1 968 (init pH1370) (init pH1370) H1370_cp1.1 H1370_cp1.2 = true := by
  decide +kernel
theorem H1370_fin : (prmOK pH1370 1370 && ptTest pH1370 (runFrom pH1370 (fmask pH1370) (cmask pH1370) (hmask pH1370) 969 401 (true, H1370_cp1.1, H1370_cp1.2)) 1370 685 true) = true := by
  decide +kernel
theorem H1370_ok : RunOK pH1370 1370 (runFrom pH1370 (fmask pH1370) (cmask pH1370) (hmask pH1370) 969 401 (true, H1370_cp1.1, H1370_cp1.2)) ∧ ptTest pH1370 (runFrom pH1370 (fmask pH1370) (cmask pH1370) (hmask pH1370) 969 401 (true, H1370_cp1.1, H1370_cp1.2)) 1370 685 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1370_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1370_fin) true) H1370_seg1) (by decide) rfl H1370_fin ptTest_fst
noncomputable def I1370_cp1 : Nat × Nat := t7val% (fastRun pI1370 1 968 (init pI1370) (init pI1370))
theorem I1370_seg1 : segOK pI1370 1 968 (init pI1370) (init pI1370) I1370_cp1.1 I1370_cp1.2 = true := by
  decide +kernel
theorem I1370_fin : (prmOK pI1370 1370 && intTest pI1370 (runFrom pI1370 (fmask pI1370) (cmask pI1370) (hmask pI1370) 969 401 (true, I1370_cp1.1, I1370_cp1.2)) 1370 20 true) = true := by
  decide +kernel
theorem I1370_ok : RunOK pI1370 1370 (runFrom pI1370 (fmask pI1370) (cmask pI1370) (hmask pI1370) 969 401 (true, I1370_cp1.1, I1370_cp1.2)) ∧ intTest pI1370 (runFrom pI1370 (fmask pI1370) (cmask pI1370) (hmask pI1370) 969 401 (true, I1370_cp1.1, I1370_cp1.2)) 1370 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1370_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1370_fin) true) I1370_seg1) (by decide) rfl I1370_fin intTest_fst
theorem link1370 : linkOK pL1370 pH1370 pI1370 = true := by decide +kernel
theorem cvx1370 : ConvexBetweenHumps 1370 :=
  cvx_of L1370_ok H1370_ok I1370_ok link1370 (by decide)
theorem cenlink1370 : cenLinkOK pI1370 1370 = true := by decide +kernel
theorem cen1370 : CenterUniqueMin 1370 ∧ DipHyp 1370 ∧ OnePointHyps 1370 :=
  cen_of L1370_ok H1370_ok I1370_ok link1370 cenlink1370

/-! ### `N = 1371` -/

def pL1371 : Prm := ⟨79, 37, 39, 1373, 11, 18446744073709551616, 133867038290732372, 133867038290732372⟩
def pH1371 : Prm := ⟨79, 37, 39, 1373, 11, 18446744073709551616, 133868137802360148, 133868137802360148⟩
def pI1371 : Prm := ⟨66, 32, 31, 1373, 11, 18446744073709551616, 133867038290732372, 133868137802360148⟩
noncomputable def L1371_cp1 : Nat × Nat := t7val% (fastRun pL1371 1 968 (init pL1371) (init pL1371))
theorem L1371_seg1 : segOK pL1371 1 968 (init pL1371) (init pL1371) L1371_cp1.1 L1371_cp1.2 = true := by
  decide +kernel
theorem L1371_fin : (prmOK pL1371 1371 && ptTest pL1371 (runFrom pL1371 (fmask pL1371) (cmask pL1371) (hmask pL1371) 969 402 (true, L1371_cp1.1, L1371_cp1.2)) 1371 686 false) = true := by
  decide +kernel
theorem L1371_ok : RunOK pL1371 1371 (runFrom pL1371 (fmask pL1371) (cmask pL1371) (hmask pL1371) 969 402 (true, L1371_cp1.1, L1371_cp1.2)) ∧ ptTest pL1371 (runFrom pL1371 (fmask pL1371) (cmask pL1371) (hmask pL1371) 969 402 (true, L1371_cp1.1, L1371_cp1.2)) 1371 686 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1371_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1371_fin) true) L1371_seg1) (by decide) rfl L1371_fin ptTest_fst
noncomputable def H1371_cp1 : Nat × Nat := t7val% (fastRun pH1371 1 968 (init pH1371) (init pH1371))
theorem H1371_seg1 : segOK pH1371 1 968 (init pH1371) (init pH1371) H1371_cp1.1 H1371_cp1.2 = true := by
  decide +kernel
theorem H1371_fin : (prmOK pH1371 1371 && ptTest pH1371 (runFrom pH1371 (fmask pH1371) (cmask pH1371) (hmask pH1371) 969 402 (true, H1371_cp1.1, H1371_cp1.2)) 1371 686 true) = true := by
  decide +kernel
theorem H1371_ok : RunOK pH1371 1371 (runFrom pH1371 (fmask pH1371) (cmask pH1371) (hmask pH1371) 969 402 (true, H1371_cp1.1, H1371_cp1.2)) ∧ ptTest pH1371 (runFrom pH1371 (fmask pH1371) (cmask pH1371) (hmask pH1371) 969 402 (true, H1371_cp1.1, H1371_cp1.2)) 1371 686 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1371_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1371_fin) true) H1371_seg1) (by decide) rfl H1371_fin ptTest_fst
noncomputable def I1371_cp1 : Nat × Nat := t7val% (fastRun pI1371 1 968 (init pI1371) (init pI1371))
theorem I1371_seg1 : segOK pI1371 1 968 (init pI1371) (init pI1371) I1371_cp1.1 I1371_cp1.2 = true := by
  decide +kernel
theorem I1371_fin : (prmOK pI1371 1371 && intTest pI1371 (runFrom pI1371 (fmask pI1371) (cmask pI1371) (hmask pI1371) 969 402 (true, I1371_cp1.1, I1371_cp1.2)) 1371 20 false) = true := by
  decide +kernel
theorem I1371_ok : RunOK pI1371 1371 (runFrom pI1371 (fmask pI1371) (cmask pI1371) (hmask pI1371) 969 402 (true, I1371_cp1.1, I1371_cp1.2)) ∧ intTest pI1371 (runFrom pI1371 (fmask pI1371) (cmask pI1371) (hmask pI1371) 969 402 (true, I1371_cp1.1, I1371_cp1.2)) 1371 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1371_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1371_fin) true) I1371_seg1) (by decide) rfl I1371_fin intTest_fst
theorem link1371 : linkOK pL1371 pH1371 pI1371 = true := by decide +kernel
theorem cvx1371 : ConvexBetweenHumps 1371 :=
  cvx_of L1371_ok H1371_ok I1371_ok link1371 (by decide)

/-! ### `N = 1372` -/

def pL1372 : Prm := ⟨79, 37, 39, 1374, 11, 18446744073709551616, 133787975258010819, 133787975258010819⟩
def pH1372 : Prm := ⟨79, 37, 39, 1374, 11, 18446744073709551616, 133789074769638595, 133789074769638595⟩
def pI1372 : Prm := ⟨67, 32, 32, 1374, 11, 18446744073709551616, 133787975258010819, 133789074769638595⟩
noncomputable def L1372_cp1 : Nat × Nat := t7val% (fastRun pL1372 1 969 (init pL1372) (init pL1372))
theorem L1372_seg1 : segOK pL1372 1 969 (init pL1372) (init pL1372) L1372_cp1.1 L1372_cp1.2 = true := by
  decide +kernel
theorem L1372_fin : (prmOK pL1372 1372 && ptTest pL1372 (runFrom pL1372 (fmask pL1372) (cmask pL1372) (hmask pL1372) 970 402 (true, L1372_cp1.1, L1372_cp1.2)) 1372 686 false) = true := by
  decide +kernel
theorem L1372_ok : RunOK pL1372 1372 (runFrom pL1372 (fmask pL1372) (cmask pL1372) (hmask pL1372) 970 402 (true, L1372_cp1.1, L1372_cp1.2)) ∧ ptTest pL1372 (runFrom pL1372 (fmask pL1372) (cmask pL1372) (hmask pL1372) 970 402 (true, L1372_cp1.1, L1372_cp1.2)) 1372 686 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1372_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1372_fin) true) L1372_seg1) (by decide) rfl L1372_fin ptTest_fst
noncomputable def H1372_cp1 : Nat × Nat := t7val% (fastRun pH1372 1 969 (init pH1372) (init pH1372))
theorem H1372_seg1 : segOK pH1372 1 969 (init pH1372) (init pH1372) H1372_cp1.1 H1372_cp1.2 = true := by
  decide +kernel
theorem H1372_fin : (prmOK pH1372 1372 && ptTest pH1372 (runFrom pH1372 (fmask pH1372) (cmask pH1372) (hmask pH1372) 970 402 (true, H1372_cp1.1, H1372_cp1.2)) 1372 686 true) = true := by
  decide +kernel
theorem H1372_ok : RunOK pH1372 1372 (runFrom pH1372 (fmask pH1372) (cmask pH1372) (hmask pH1372) 970 402 (true, H1372_cp1.1, H1372_cp1.2)) ∧ ptTest pH1372 (runFrom pH1372 (fmask pH1372) (cmask pH1372) (hmask pH1372) 970 402 (true, H1372_cp1.1, H1372_cp1.2)) 1372 686 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1372_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1372_fin) true) H1372_seg1) (by decide) rfl H1372_fin ptTest_fst
noncomputable def I1372_cp1 : Nat × Nat := t7val% (fastRun pI1372 1 969 (init pI1372) (init pI1372))
theorem I1372_seg1 : segOK pI1372 1 969 (init pI1372) (init pI1372) I1372_cp1.1 I1372_cp1.2 = true := by
  decide +kernel
theorem I1372_fin : (prmOK pI1372 1372 && intTest pI1372 (runFrom pI1372 (fmask pI1372) (cmask pI1372) (hmask pI1372) 970 402 (true, I1372_cp1.1, I1372_cp1.2)) 1372 20 true) = true := by
  decide +kernel
theorem I1372_ok : RunOK pI1372 1372 (runFrom pI1372 (fmask pI1372) (cmask pI1372) (hmask pI1372) 970 402 (true, I1372_cp1.1, I1372_cp1.2)) ∧ intTest pI1372 (runFrom pI1372 (fmask pI1372) (cmask pI1372) (hmask pI1372) 970 402 (true, I1372_cp1.1, I1372_cp1.2)) 1372 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1372_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1372_fin) true) I1372_seg1) (by decide) rfl I1372_fin intTest_fst
theorem link1372 : linkOK pL1372 pH1372 pI1372 = true := by decide +kernel
theorem cvx1372 : ConvexBetweenHumps 1372 :=
  cvx_of L1372_ok H1372_ok I1372_ok link1372 (by decide)
theorem cenlink1372 : cenLinkOK pI1372 1372 = true := by decide +kernel
theorem cen1372 : CenterUniqueMin 1372 ∧ DipHyp 1372 ∧ OnePointHyps 1372 :=
  cen_of L1372_ok H1372_ok I1372_ok link1372 cenlink1372

/-! ### `N = 1373` -/

def pL1373 : Prm := ⟨79, 37, 39, 1375, 11, 18446744073709551616, 133708969929508634, 133708969929508634⟩
def pH1373 : Prm := ⟨79, 37, 39, 1375, 11, 18446744073709551616, 133710069441136410, 133710069441136410⟩
def pI1373 : Prm := ⟨66, 32, 31, 1375, 11, 18446744073709551616, 133708969929508634, 133710069441136410⟩
noncomputable def L1373_cp1 : Nat × Nat := t7val% (fastRun pL1373 1 970 (init pL1373) (init pL1373))
theorem L1373_seg1 : segOK pL1373 1 970 (init pL1373) (init pL1373) L1373_cp1.1 L1373_cp1.2 = true := by
  decide +kernel
theorem L1373_fin : (prmOK pL1373 1373 && ptTest pL1373 (runFrom pL1373 (fmask pL1373) (cmask pL1373) (hmask pL1373) 971 402 (true, L1373_cp1.1, L1373_cp1.2)) 1373 687 false) = true := by
  decide +kernel
theorem L1373_ok : RunOK pL1373 1373 (runFrom pL1373 (fmask pL1373) (cmask pL1373) (hmask pL1373) 971 402 (true, L1373_cp1.1, L1373_cp1.2)) ∧ ptTest pL1373 (runFrom pL1373 (fmask pL1373) (cmask pL1373) (hmask pL1373) 971 402 (true, L1373_cp1.1, L1373_cp1.2)) 1373 687 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1373_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1373_fin) true) L1373_seg1) (by decide) rfl L1373_fin ptTest_fst
noncomputable def H1373_cp1 : Nat × Nat := t7val% (fastRun pH1373 1 970 (init pH1373) (init pH1373))
theorem H1373_seg1 : segOK pH1373 1 970 (init pH1373) (init pH1373) H1373_cp1.1 H1373_cp1.2 = true := by
  decide +kernel
theorem H1373_fin : (prmOK pH1373 1373 && ptTest pH1373 (runFrom pH1373 (fmask pH1373) (cmask pH1373) (hmask pH1373) 971 402 (true, H1373_cp1.1, H1373_cp1.2)) 1373 687 true) = true := by
  decide +kernel
theorem H1373_ok : RunOK pH1373 1373 (runFrom pH1373 (fmask pH1373) (cmask pH1373) (hmask pH1373) 971 402 (true, H1373_cp1.1, H1373_cp1.2)) ∧ ptTest pH1373 (runFrom pH1373 (fmask pH1373) (cmask pH1373) (hmask pH1373) 971 402 (true, H1373_cp1.1, H1373_cp1.2)) 1373 687 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1373_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1373_fin) true) H1373_seg1) (by decide) rfl H1373_fin ptTest_fst
noncomputable def I1373_cp1 : Nat × Nat := t7val% (fastRun pI1373 1 970 (init pI1373) (init pI1373))
theorem I1373_seg1 : segOK pI1373 1 970 (init pI1373) (init pI1373) I1373_cp1.1 I1373_cp1.2 = true := by
  decide +kernel
theorem I1373_fin : (prmOK pI1373 1373 && intTest pI1373 (runFrom pI1373 (fmask pI1373) (cmask pI1373) (hmask pI1373) 971 402 (true, I1373_cp1.1, I1373_cp1.2)) 1373 20 false) = true := by
  decide +kernel
theorem I1373_ok : RunOK pI1373 1373 (runFrom pI1373 (fmask pI1373) (cmask pI1373) (hmask pI1373) 971 402 (true, I1373_cp1.1, I1373_cp1.2)) ∧ intTest pI1373 (runFrom pI1373 (fmask pI1373) (cmask pI1373) (hmask pI1373) 971 402 (true, I1373_cp1.1, I1373_cp1.2)) 1373 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1373_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1373_fin) true) I1373_seg1) (by decide) rfl I1373_fin intTest_fst
theorem link1373 : linkOK pL1373 pH1373 pI1373 = true := by decide +kernel
theorem cvx1373 : ConvexBetweenHumps 1373 :=
  cvx_of L1373_ok H1373_ok I1373_ok link1373 (by decide)

/-! ### `N = 1374` -/

def pL1374 : Prm := ⟨79, 37, 39, 1376, 11, 18446744073709551616, 133630110053380556, 133630110053380556⟩
def pH1374 : Prm := ⟨79, 37, 39, 1376, 11, 18446744073709551616, 133631209565008332, 133631209565008332⟩
def pI1374 : Prm := ⟨67, 32, 32, 1376, 11, 18446744073709551616, 133630110053380556, 133631209565008332⟩
noncomputable def L1374_cp1 : Nat × Nat := t7val% (fastRun pL1374 1 971 (init pL1374) (init pL1374))
theorem L1374_seg1 : segOK pL1374 1 971 (init pL1374) (init pL1374) L1374_cp1.1 L1374_cp1.2 = true := by
  decide +kernel
theorem L1374_fin : (prmOK pL1374 1374 && ptTest pL1374 (runFrom pL1374 (fmask pL1374) (cmask pL1374) (hmask pL1374) 972 402 (true, L1374_cp1.1, L1374_cp1.2)) 1374 687 false) = true := by
  decide +kernel
theorem L1374_ok : RunOK pL1374 1374 (runFrom pL1374 (fmask pL1374) (cmask pL1374) (hmask pL1374) 972 402 (true, L1374_cp1.1, L1374_cp1.2)) ∧ ptTest pL1374 (runFrom pL1374 (fmask pL1374) (cmask pL1374) (hmask pL1374) 972 402 (true, L1374_cp1.1, L1374_cp1.2)) 1374 687 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1374_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1374_fin) true) L1374_seg1) (by decide) rfl L1374_fin ptTest_fst
noncomputable def H1374_cp1 : Nat × Nat := t7val% (fastRun pH1374 1 971 (init pH1374) (init pH1374))
theorem H1374_seg1 : segOK pH1374 1 971 (init pH1374) (init pH1374) H1374_cp1.1 H1374_cp1.2 = true := by
  decide +kernel
theorem H1374_fin : (prmOK pH1374 1374 && ptTest pH1374 (runFrom pH1374 (fmask pH1374) (cmask pH1374) (hmask pH1374) 972 402 (true, H1374_cp1.1, H1374_cp1.2)) 1374 687 true) = true := by
  decide +kernel
theorem H1374_ok : RunOK pH1374 1374 (runFrom pH1374 (fmask pH1374) (cmask pH1374) (hmask pH1374) 972 402 (true, H1374_cp1.1, H1374_cp1.2)) ∧ ptTest pH1374 (runFrom pH1374 (fmask pH1374) (cmask pH1374) (hmask pH1374) 972 402 (true, H1374_cp1.1, H1374_cp1.2)) 1374 687 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1374_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1374_fin) true) H1374_seg1) (by decide) rfl H1374_fin ptTest_fst
noncomputable def I1374_cp1 : Nat × Nat := t7val% (fastRun pI1374 1 971 (init pI1374) (init pI1374))
theorem I1374_seg1 : segOK pI1374 1 971 (init pI1374) (init pI1374) I1374_cp1.1 I1374_cp1.2 = true := by
  decide +kernel
theorem I1374_fin : (prmOK pI1374 1374 && intTest pI1374 (runFrom pI1374 (fmask pI1374) (cmask pI1374) (hmask pI1374) 972 402 (true, I1374_cp1.1, I1374_cp1.2)) 1374 20 true) = true := by
  decide +kernel
theorem I1374_ok : RunOK pI1374 1374 (runFrom pI1374 (fmask pI1374) (cmask pI1374) (hmask pI1374) 972 402 (true, I1374_cp1.1, I1374_cp1.2)) ∧ intTest pI1374 (runFrom pI1374 (fmask pI1374) (cmask pI1374) (hmask pI1374) 972 402 (true, I1374_cp1.1, I1374_cp1.2)) 1374 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1374_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1374_fin) true) I1374_seg1) (by decide) rfl I1374_fin intTest_fst
theorem link1374 : linkOK pL1374 pH1374 pI1374 = true := by decide +kernel
theorem cvx1374 : ConvexBetweenHumps 1374 :=
  cvx_of L1374_ok H1374_ok I1374_ok link1374 (by decide)
theorem cenlink1374 : cenLinkOK pI1374 1374 = true := by decide +kernel
theorem cen1374 : CenterUniqueMin 1374 ∧ DipHyp 1374 ∧ OnePointHyps 1374 :=
  cen_of L1374_ok H1374_ok I1374_ok link1374 cenlink1374

/-! ### `N = 1375` -/

def pL1375 : Prm := ⟨79, 37, 39, 1377, 11, 18446744073709551616, 133551307672101301, 133551307672101301⟩
def pH1375 : Prm := ⟨79, 37, 39, 1377, 11, 18446744073709551616, 133552407183729077, 133552407183729077⟩
def pI1375 : Prm := ⟨67, 32, 32, 1377, 11, 18446744073709551616, 133551307672101301, 133552407183729077⟩
noncomputable def L1375_cp1 : Nat × Nat := t7val% (fastRun pL1375 1 971 (init pL1375) (init pL1375))
theorem L1375_seg1 : segOK pL1375 1 971 (init pL1375) (init pL1375) L1375_cp1.1 L1375_cp1.2 = true := by
  decide +kernel
theorem L1375_fin : (prmOK pL1375 1375 && ptTest pL1375 (runFrom pL1375 (fmask pL1375) (cmask pL1375) (hmask pL1375) 972 403 (true, L1375_cp1.1, L1375_cp1.2)) 1375 688 false) = true := by
  decide +kernel
theorem L1375_ok : RunOK pL1375 1375 (runFrom pL1375 (fmask pL1375) (cmask pL1375) (hmask pL1375) 972 403 (true, L1375_cp1.1, L1375_cp1.2)) ∧ ptTest pL1375 (runFrom pL1375 (fmask pL1375) (cmask pL1375) (hmask pL1375) 972 403 (true, L1375_cp1.1, L1375_cp1.2)) 1375 688 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1375_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1375_fin) true) L1375_seg1) (by decide) rfl L1375_fin ptTest_fst
noncomputable def H1375_cp1 : Nat × Nat := t7val% (fastRun pH1375 1 971 (init pH1375) (init pH1375))
theorem H1375_seg1 : segOK pH1375 1 971 (init pH1375) (init pH1375) H1375_cp1.1 H1375_cp1.2 = true := by
  decide +kernel
theorem H1375_fin : (prmOK pH1375 1375 && ptTest pH1375 (runFrom pH1375 (fmask pH1375) (cmask pH1375) (hmask pH1375) 972 403 (true, H1375_cp1.1, H1375_cp1.2)) 1375 688 true) = true := by
  decide +kernel
theorem H1375_ok : RunOK pH1375 1375 (runFrom pH1375 (fmask pH1375) (cmask pH1375) (hmask pH1375) 972 403 (true, H1375_cp1.1, H1375_cp1.2)) ∧ ptTest pH1375 (runFrom pH1375 (fmask pH1375) (cmask pH1375) (hmask pH1375) 972 403 (true, H1375_cp1.1, H1375_cp1.2)) 1375 688 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1375_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1375_fin) true) H1375_seg1) (by decide) rfl H1375_fin ptTest_fst
noncomputable def I1375_cp1 : Nat × Nat := t7val% (fastRun pI1375 1 971 (init pI1375) (init pI1375))
theorem I1375_seg1 : segOK pI1375 1 971 (init pI1375) (init pI1375) I1375_cp1.1 I1375_cp1.2 = true := by
  decide +kernel
theorem I1375_fin : (prmOK pI1375 1375 && intTest pI1375 (runFrom pI1375 (fmask pI1375) (cmask pI1375) (hmask pI1375) 972 403 (true, I1375_cp1.1, I1375_cp1.2)) 1375 20 false) = true := by
  decide +kernel
theorem I1375_ok : RunOK pI1375 1375 (runFrom pI1375 (fmask pI1375) (cmask pI1375) (hmask pI1375) 972 403 (true, I1375_cp1.1, I1375_cp1.2)) ∧ intTest pI1375 (runFrom pI1375 (fmask pI1375) (cmask pI1375) (hmask pI1375) 972 403 (true, I1375_cp1.1, I1375_cp1.2)) 1375 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1375_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1375_fin) true) I1375_seg1) (by decide) rfl I1375_fin intTest_fst
theorem link1375 : linkOK pL1375 pH1375 pI1375 = true := by decide +kernel
theorem cvx1375 : ConvexBetweenHumps 1375 :=
  cvx_of L1375_ok H1375_ok I1375_ok link1375 (by decide)

/-! ### `N = 1376` -/

def pL1376 : Prm := ⟨79, 37, 39, 1378, 11, 18446744073709551616, 133472650145226496, 133472650145226496⟩
def pH1376 : Prm := ⟨79, 37, 39, 1378, 11, 18446744073709551616, 133473749656854272, 133473749656854272⟩
def pI1376 : Prm := ⟨66, 32, 31, 1378, 11, 18446744073709551616, 133472650145226496, 133473749656854272⟩
noncomputable def L1376_cp1 : Nat × Nat := t7val% (fastRun pL1376 1 972 (init pL1376) (init pL1376))
theorem L1376_seg1 : segOK pL1376 1 972 (init pL1376) (init pL1376) L1376_cp1.1 L1376_cp1.2 = true := by
  decide +kernel
theorem L1376_fin : (prmOK pL1376 1376 && ptTest pL1376 (runFrom pL1376 (fmask pL1376) (cmask pL1376) (hmask pL1376) 973 403 (true, L1376_cp1.1, L1376_cp1.2)) 1376 688 false) = true := by
  decide +kernel
theorem L1376_ok : RunOK pL1376 1376 (runFrom pL1376 (fmask pL1376) (cmask pL1376) (hmask pL1376) 973 403 (true, L1376_cp1.1, L1376_cp1.2)) ∧ ptTest pL1376 (runFrom pL1376 (fmask pL1376) (cmask pL1376) (hmask pL1376) 973 403 (true, L1376_cp1.1, L1376_cp1.2)) 1376 688 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1376_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1376_fin) true) L1376_seg1) (by decide) rfl L1376_fin ptTest_fst
noncomputable def H1376_cp1 : Nat × Nat := t7val% (fastRun pH1376 1 972 (init pH1376) (init pH1376))
theorem H1376_seg1 : segOK pH1376 1 972 (init pH1376) (init pH1376) H1376_cp1.1 H1376_cp1.2 = true := by
  decide +kernel
theorem H1376_fin : (prmOK pH1376 1376 && ptTest pH1376 (runFrom pH1376 (fmask pH1376) (cmask pH1376) (hmask pH1376) 973 403 (true, H1376_cp1.1, H1376_cp1.2)) 1376 688 true) = true := by
  decide +kernel
theorem H1376_ok : RunOK pH1376 1376 (runFrom pH1376 (fmask pH1376) (cmask pH1376) (hmask pH1376) 973 403 (true, H1376_cp1.1, H1376_cp1.2)) ∧ ptTest pH1376 (runFrom pH1376 (fmask pH1376) (cmask pH1376) (hmask pH1376) 973 403 (true, H1376_cp1.1, H1376_cp1.2)) 1376 688 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1376_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1376_fin) true) H1376_seg1) (by decide) rfl H1376_fin ptTest_fst
noncomputable def I1376_cp1 : Nat × Nat := t7val% (fastRun pI1376 1 972 (init pI1376) (init pI1376))
theorem I1376_seg1 : segOK pI1376 1 972 (init pI1376) (init pI1376) I1376_cp1.1 I1376_cp1.2 = true := by
  decide +kernel
theorem I1376_fin : (prmOK pI1376 1376 && intTest pI1376 (runFrom pI1376 (fmask pI1376) (cmask pI1376) (hmask pI1376) 973 403 (true, I1376_cp1.1, I1376_cp1.2)) 1376 20 true) = true := by
  decide +kernel
theorem I1376_ok : RunOK pI1376 1376 (runFrom pI1376 (fmask pI1376) (cmask pI1376) (hmask pI1376) 973 403 (true, I1376_cp1.1, I1376_cp1.2)) ∧ intTest pI1376 (runFrom pI1376 (fmask pI1376) (cmask pI1376) (hmask pI1376) 973 403 (true, I1376_cp1.1, I1376_cp1.2)) 1376 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1376_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1376_fin) true) I1376_seg1) (by decide) rfl I1376_fin intTest_fst
theorem link1376 : linkOK pL1376 pH1376 pI1376 = true := by decide +kernel
theorem cvx1376 : ConvexBetweenHumps 1376 :=
  cvx_of L1376_ok H1376_ok I1376_ok link1376 (by decide)
theorem cenlink1376 : cenLinkOK pI1376 1376 = true := by decide +kernel
theorem cen1376 : CenterUniqueMin 1376 ∧ DipHyp 1376 ∧ OnePointHyps 1376 :=
  cen_of L1376_ok H1376_ok I1376_ok link1376 cenlink1376

/-! ### `N = 1377` -/

def pL1377 : Prm := ⟨79, 37, 39, 1379, 11, 18446744073709551616, 133394049904881433, 133394049904881433⟩
def pH1377 : Prm := ⟨79, 37, 39, 1379, 11, 18446744073709551616, 133395149416509209, 133395149416509209⟩
def pI1377 : Prm := ⟨67, 32, 32, 1379, 11, 18446744073709551616, 133394049904881433, 133395149416509209⟩
noncomputable def L1377_cp1 : Nat × Nat := t7val% (fastRun pL1377 1 973 (init pL1377) (init pL1377))
theorem L1377_seg1 : segOK pL1377 1 973 (init pL1377) (init pL1377) L1377_cp1.1 L1377_cp1.2 = true := by
  decide +kernel
theorem L1377_fin : (prmOK pL1377 1377 && ptTest pL1377 (runFrom pL1377 (fmask pL1377) (cmask pL1377) (hmask pL1377) 974 403 (true, L1377_cp1.1, L1377_cp1.2)) 1377 689 false) = true := by
  decide +kernel
theorem L1377_ok : RunOK pL1377 1377 (runFrom pL1377 (fmask pL1377) (cmask pL1377) (hmask pL1377) 974 403 (true, L1377_cp1.1, L1377_cp1.2)) ∧ ptTest pL1377 (runFrom pL1377 (fmask pL1377) (cmask pL1377) (hmask pL1377) 974 403 (true, L1377_cp1.1, L1377_cp1.2)) 1377 689 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1377_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1377_fin) true) L1377_seg1) (by decide) rfl L1377_fin ptTest_fst
noncomputable def H1377_cp1 : Nat × Nat := t7val% (fastRun pH1377 1 973 (init pH1377) (init pH1377))
theorem H1377_seg1 : segOK pH1377 1 973 (init pH1377) (init pH1377) H1377_cp1.1 H1377_cp1.2 = true := by
  decide +kernel
theorem H1377_fin : (prmOK pH1377 1377 && ptTest pH1377 (runFrom pH1377 (fmask pH1377) (cmask pH1377) (hmask pH1377) 974 403 (true, H1377_cp1.1, H1377_cp1.2)) 1377 689 true) = true := by
  decide +kernel
theorem H1377_ok : RunOK pH1377 1377 (runFrom pH1377 (fmask pH1377) (cmask pH1377) (hmask pH1377) 974 403 (true, H1377_cp1.1, H1377_cp1.2)) ∧ ptTest pH1377 (runFrom pH1377 (fmask pH1377) (cmask pH1377) (hmask pH1377) 974 403 (true, H1377_cp1.1, H1377_cp1.2)) 1377 689 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1377_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1377_fin) true) H1377_seg1) (by decide) rfl H1377_fin ptTest_fst
noncomputable def I1377_cp1 : Nat × Nat := t7val% (fastRun pI1377 1 973 (init pI1377) (init pI1377))
theorem I1377_seg1 : segOK pI1377 1 973 (init pI1377) (init pI1377) I1377_cp1.1 I1377_cp1.2 = true := by
  decide +kernel
theorem I1377_fin : (prmOK pI1377 1377 && intTest pI1377 (runFrom pI1377 (fmask pI1377) (cmask pI1377) (hmask pI1377) 974 403 (true, I1377_cp1.1, I1377_cp1.2)) 1377 20 false) = true := by
  decide +kernel
theorem I1377_ok : RunOK pI1377 1377 (runFrom pI1377 (fmask pI1377) (cmask pI1377) (hmask pI1377) 974 403 (true, I1377_cp1.1, I1377_cp1.2)) ∧ intTest pI1377 (runFrom pI1377 (fmask pI1377) (cmask pI1377) (hmask pI1377) 974 403 (true, I1377_cp1.1, I1377_cp1.2)) 1377 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1377_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1377_fin) true) I1377_seg1) (by decide) rfl I1377_fin intTest_fst
theorem link1377 : linkOK pL1377 pH1377 pI1377 = true := by decide +kernel
theorem cvx1377 : ConvexBetweenHumps 1377 :=
  cvx_of L1377_ok H1377_ok I1377_ok link1377 (by decide)

/-! ### `N = 1378` -/

def pL1378 : Prm := ⟨79, 37, 39, 1380, 11, 18446744073709551616, 133315593924236239, 133315593924236239⟩
def pH1378 : Prm := ⟨79, 37, 39, 1380, 11, 18446744073709551616, 133316693435864015, 133316693435864015⟩
def pI1378 : Prm := ⟨67, 32, 32, 1380, 11, 18446744073709551616, 133315593924236239, 133316693435864015⟩
noncomputable def L1378_cp1 : Nat × Nat := t7val% (fastRun pL1378 1 973 (init pL1378) (init pL1378))
theorem L1378_seg1 : segOK pL1378 1 973 (init pL1378) (init pL1378) L1378_cp1.1 L1378_cp1.2 = true := by
  decide +kernel
theorem L1378_fin : (prmOK pL1378 1378 && ptTest pL1378 (runFrom pL1378 (fmask pL1378) (cmask pL1378) (hmask pL1378) 974 404 (true, L1378_cp1.1, L1378_cp1.2)) 1378 689 false) = true := by
  decide +kernel
theorem L1378_ok : RunOK pL1378 1378 (runFrom pL1378 (fmask pL1378) (cmask pL1378) (hmask pL1378) 974 404 (true, L1378_cp1.1, L1378_cp1.2)) ∧ ptTest pL1378 (runFrom pL1378 (fmask pL1378) (cmask pL1378) (hmask pL1378) 974 404 (true, L1378_cp1.1, L1378_cp1.2)) 1378 689 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1378_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1378_fin) true) L1378_seg1) (by decide) rfl L1378_fin ptTest_fst
noncomputable def H1378_cp1 : Nat × Nat := t7val% (fastRun pH1378 1 973 (init pH1378) (init pH1378))
theorem H1378_seg1 : segOK pH1378 1 973 (init pH1378) (init pH1378) H1378_cp1.1 H1378_cp1.2 = true := by
  decide +kernel
theorem H1378_fin : (prmOK pH1378 1378 && ptTest pH1378 (runFrom pH1378 (fmask pH1378) (cmask pH1378) (hmask pH1378) 974 404 (true, H1378_cp1.1, H1378_cp1.2)) 1378 689 true) = true := by
  decide +kernel
theorem H1378_ok : RunOK pH1378 1378 (runFrom pH1378 (fmask pH1378) (cmask pH1378) (hmask pH1378) 974 404 (true, H1378_cp1.1, H1378_cp1.2)) ∧ ptTest pH1378 (runFrom pH1378 (fmask pH1378) (cmask pH1378) (hmask pH1378) 974 404 (true, H1378_cp1.1, H1378_cp1.2)) 1378 689 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1378_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1378_fin) true) H1378_seg1) (by decide) rfl H1378_fin ptTest_fst
noncomputable def I1378_cp1 : Nat × Nat := t7val% (fastRun pI1378 1 973 (init pI1378) (init pI1378))
theorem I1378_seg1 : segOK pI1378 1 973 (init pI1378) (init pI1378) I1378_cp1.1 I1378_cp1.2 = true := by
  decide +kernel
theorem I1378_fin : (prmOK pI1378 1378 && intTest pI1378 (runFrom pI1378 (fmask pI1378) (cmask pI1378) (hmask pI1378) 974 404 (true, I1378_cp1.1, I1378_cp1.2)) 1378 20 true) = true := by
  decide +kernel
theorem I1378_ok : RunOK pI1378 1378 (runFrom pI1378 (fmask pI1378) (cmask pI1378) (hmask pI1378) 974 404 (true, I1378_cp1.1, I1378_cp1.2)) ∧ intTest pI1378 (runFrom pI1378 (fmask pI1378) (cmask pI1378) (hmask pI1378) 974 404 (true, I1378_cp1.1, I1378_cp1.2)) 1378 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1378_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1378_fin) true) I1378_seg1) (by decide) rfl I1378_fin intTest_fst
theorem link1378 : linkOK pL1378 pH1378 pI1378 = true := by decide +kernel
theorem cvx1378 : ConvexBetweenHumps 1378 :=
  cvx_of L1378_ok H1378_ok I1378_ok link1378 (by decide)
theorem cenlink1378 : cenLinkOK pI1378 1378 = true := by decide +kernel
theorem cen1378 : CenterUniqueMin 1378 ∧ DipHyp 1378 ∧ OnePointHyps 1378 :=
  cen_of L1378_ok H1378_ok I1378_ok link1378 cenlink1378

/-! ### `N = 1379` -/

def pL1379 : Prm := ⟨79, 37, 39, 1381, 11, 18446744073709551616, 133237195022834724, 133237195022834724⟩
def pH1379 : Prm := ⟨79, 37, 39, 1381, 11, 18446744073709551616, 133238294534462500, 133238294534462500⟩
def pI1379 : Prm := ⟨67, 32, 32, 1381, 11, 18446744073709551616, 133237195022834724, 133238294534462500⟩
noncomputable def L1379_cp1 : Nat × Nat := t7val% (fastRun pL1379 1 974 (init pL1379) (init pL1379))
theorem L1379_seg1 : segOK pL1379 1 974 (init pL1379) (init pL1379) L1379_cp1.1 L1379_cp1.2 = true := by
  decide +kernel
theorem L1379_fin : (prmOK pL1379 1379 && ptTest pL1379 (runFrom pL1379 (fmask pL1379) (cmask pL1379) (hmask pL1379) 975 404 (true, L1379_cp1.1, L1379_cp1.2)) 1379 690 false) = true := by
  decide +kernel
theorem L1379_ok : RunOK pL1379 1379 (runFrom pL1379 (fmask pL1379) (cmask pL1379) (hmask pL1379) 975 404 (true, L1379_cp1.1, L1379_cp1.2)) ∧ ptTest pL1379 (runFrom pL1379 (fmask pL1379) (cmask pL1379) (hmask pL1379) 975 404 (true, L1379_cp1.1, L1379_cp1.2)) 1379 690 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1379_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1379_fin) true) L1379_seg1) (by decide) rfl L1379_fin ptTest_fst
noncomputable def H1379_cp1 : Nat × Nat := t7val% (fastRun pH1379 1 974 (init pH1379) (init pH1379))
theorem H1379_seg1 : segOK pH1379 1 974 (init pH1379) (init pH1379) H1379_cp1.1 H1379_cp1.2 = true := by
  decide +kernel
theorem H1379_fin : (prmOK pH1379 1379 && ptTest pH1379 (runFrom pH1379 (fmask pH1379) (cmask pH1379) (hmask pH1379) 975 404 (true, H1379_cp1.1, H1379_cp1.2)) 1379 690 true) = true := by
  decide +kernel
theorem H1379_ok : RunOK pH1379 1379 (runFrom pH1379 (fmask pH1379) (cmask pH1379) (hmask pH1379) 975 404 (true, H1379_cp1.1, H1379_cp1.2)) ∧ ptTest pH1379 (runFrom pH1379 (fmask pH1379) (cmask pH1379) (hmask pH1379) 975 404 (true, H1379_cp1.1, H1379_cp1.2)) 1379 690 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1379_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1379_fin) true) H1379_seg1) (by decide) rfl H1379_fin ptTest_fst
noncomputable def I1379_cp1 : Nat × Nat := t7val% (fastRun pI1379 1 974 (init pI1379) (init pI1379))
theorem I1379_seg1 : segOK pI1379 1 974 (init pI1379) (init pI1379) I1379_cp1.1 I1379_cp1.2 = true := by
  decide +kernel
theorem I1379_fin : (prmOK pI1379 1379 && intTest pI1379 (runFrom pI1379 (fmask pI1379) (cmask pI1379) (hmask pI1379) 975 404 (true, I1379_cp1.1, I1379_cp1.2)) 1379 20 false) = true := by
  decide +kernel
theorem I1379_ok : RunOK pI1379 1379 (runFrom pI1379 (fmask pI1379) (cmask pI1379) (hmask pI1379) 975 404 (true, I1379_cp1.1, I1379_cp1.2)) ∧ intTest pI1379 (runFrom pI1379 (fmask pI1379) (cmask pI1379) (hmask pI1379) 975 404 (true, I1379_cp1.1, I1379_cp1.2)) 1379 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1379_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1379_fin) true) I1379_seg1) (by decide) rfl I1379_fin intTest_fst
theorem link1379 : linkOK pL1379 pH1379 pI1379 = true := by decide +kernel
theorem cvx1379 : ConvexBetweenHumps 1379 :=
  cvx_of L1379_ok H1379_ok I1379_ok link1379 (by decide)

/-! ### `N = 1380` -/

def pL1380 : Prm := ⟨79, 37, 39, 1382, 11, 18446744073709551616, 133158939789748909, 133158939789748909⟩
def pH1380 : Prm := ⟨79, 37, 39, 1382, 11, 18446744073709551616, 133160039301376685, 133160039301376685⟩
def pI1380 : Prm := ⟨67, 32, 32, 1382, 11, 18446744073709551616, 133158939789748909, 133160039301376685⟩
noncomputable def L1380_cp1 : Nat × Nat := t7val% (fastRun pL1380 1 975 (init pL1380) (init pL1380))
theorem L1380_seg1 : segOK pL1380 1 975 (init pL1380) (init pL1380) L1380_cp1.1 L1380_cp1.2 = true := by
  decide +kernel
theorem L1380_fin : (prmOK pL1380 1380 && ptTest pL1380 (runFrom pL1380 (fmask pL1380) (cmask pL1380) (hmask pL1380) 976 404 (true, L1380_cp1.1, L1380_cp1.2)) 1380 690 false) = true := by
  decide +kernel
theorem L1380_ok : RunOK pL1380 1380 (runFrom pL1380 (fmask pL1380) (cmask pL1380) (hmask pL1380) 976 404 (true, L1380_cp1.1, L1380_cp1.2)) ∧ ptTest pL1380 (runFrom pL1380 (fmask pL1380) (cmask pL1380) (hmask pL1380) 976 404 (true, L1380_cp1.1, L1380_cp1.2)) 1380 690 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1380_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1380_fin) true) L1380_seg1) (by decide) rfl L1380_fin ptTest_fst
noncomputable def H1380_cp1 : Nat × Nat := t7val% (fastRun pH1380 1 975 (init pH1380) (init pH1380))
theorem H1380_seg1 : segOK pH1380 1 975 (init pH1380) (init pH1380) H1380_cp1.1 H1380_cp1.2 = true := by
  decide +kernel
theorem H1380_fin : (prmOK pH1380 1380 && ptTest pH1380 (runFrom pH1380 (fmask pH1380) (cmask pH1380) (hmask pH1380) 976 404 (true, H1380_cp1.1, H1380_cp1.2)) 1380 690 true) = true := by
  decide +kernel
theorem H1380_ok : RunOK pH1380 1380 (runFrom pH1380 (fmask pH1380) (cmask pH1380) (hmask pH1380) 976 404 (true, H1380_cp1.1, H1380_cp1.2)) ∧ ptTest pH1380 (runFrom pH1380 (fmask pH1380) (cmask pH1380) (hmask pH1380) 976 404 (true, H1380_cp1.1, H1380_cp1.2)) 1380 690 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1380_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1380_fin) true) H1380_seg1) (by decide) rfl H1380_fin ptTest_fst
noncomputable def I1380_cp1 : Nat × Nat := t7val% (fastRun pI1380 1 975 (init pI1380) (init pI1380))
theorem I1380_seg1 : segOK pI1380 1 975 (init pI1380) (init pI1380) I1380_cp1.1 I1380_cp1.2 = true := by
  decide +kernel
theorem I1380_fin : (prmOK pI1380 1380 && intTest pI1380 (runFrom pI1380 (fmask pI1380) (cmask pI1380) (hmask pI1380) 976 404 (true, I1380_cp1.1, I1380_cp1.2)) 1380 20 true) = true := by
  decide +kernel
theorem I1380_ok : RunOK pI1380 1380 (runFrom pI1380 (fmask pI1380) (cmask pI1380) (hmask pI1380) 976 404 (true, I1380_cp1.1, I1380_cp1.2)) ∧ intTest pI1380 (runFrom pI1380 (fmask pI1380) (cmask pI1380) (hmask pI1380) 976 404 (true, I1380_cp1.1, I1380_cp1.2)) 1380 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1380_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1380_fin) true) I1380_seg1) (by decide) rfl I1380_fin intTest_fst
theorem link1380 : linkOK pL1380 pH1380 pI1380 = true := by decide +kernel
theorem cvx1380 : ConvexBetweenHumps 1380 :=
  cvx_of L1380_ok H1380_ok I1380_ok link1380 (by decide)
theorem cenlink1380 : cenLinkOK pI1380 1380 = true := by decide +kernel
theorem cen1380 : CenterUniqueMin 1380 ∧ DipHyp 1380 ∧ OnePointHyps 1380 :=
  cen_of L1380_ok H1380_ok I1380_ok link1380 cenlink1380

/-! ### The range -/

theorem cvx_1360_1380 {N : ℕ} (h1 : 1360 ≤ N) (h2 : N ≤ 1380) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1369
  · by_cases h4 : N ≤ 1364
    · by_cases h6 : N ≤ 1361
      · by_cases h8 : N ≤ 1360
        · obtain rfl : N = 1360 := by omega
          exact cvx1360
        · obtain rfl : N = 1361 := by omega
          exact cvx1361
      · by_cases h8 : N ≤ 1362
        · obtain rfl : N = 1362 := by omega
          exact cvx1362
        · by_cases h10 : N ≤ 1363
          · obtain rfl : N = 1363 := by omega
            exact cvx1363
          · obtain rfl : N = 1364 := by omega
            exact cvx1364
    · by_cases h6 : N ≤ 1366
      · by_cases h8 : N ≤ 1365
        · obtain rfl : N = 1365 := by omega
          exact cvx1365
        · obtain rfl : N = 1366 := by omega
          exact cvx1366
      · by_cases h8 : N ≤ 1367
        · obtain rfl : N = 1367 := by omega
          exact cvx1367
        · by_cases h10 : N ≤ 1368
          · obtain rfl : N = 1368 := by omega
            exact cvx1368
          · obtain rfl : N = 1369 := by omega
            exact cvx1369
  · by_cases h4 : N ≤ 1374
    · by_cases h6 : N ≤ 1371
      · by_cases h8 : N ≤ 1370
        · obtain rfl : N = 1370 := by omega
          exact cvx1370
        · obtain rfl : N = 1371 := by omega
          exact cvx1371
      · by_cases h8 : N ≤ 1372
        · obtain rfl : N = 1372 := by omega
          exact cvx1372
        · by_cases h10 : N ≤ 1373
          · obtain rfl : N = 1373 := by omega
            exact cvx1373
          · obtain rfl : N = 1374 := by omega
            exact cvx1374
    · by_cases h6 : N ≤ 1377
      · by_cases h8 : N ≤ 1375
        · obtain rfl : N = 1375 := by omega
          exact cvx1375
        · by_cases h10 : N ≤ 1376
          · obtain rfl : N = 1376 := by omega
            exact cvx1376
          · obtain rfl : N = 1377 := by omega
            exact cvx1377
      · by_cases h8 : N ≤ 1378
        · obtain rfl : N = 1378 := by omega
          exact cvx1378
        · by_cases h10 : N ≤ 1379
          · obtain rfl : N = 1379 := by omega
            exact cvx1379
          · obtain rfl : N = 1380 := by omega
            exact cvx1380

theorem cen_1360_1380 {N : ℕ} (h1 : 1360 ≤ N) (h2 : N ≤ 1380) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1368
  · by_cases h4 : N ≤ 1362
    · by_cases h6 : N ≤ 1360
      · obtain rfl : N = 1360 := by omega
        exact cen1360
      · obtain rfl : N = 1362 := by omega
        exact cen1362
    · by_cases h6 : N ≤ 1364
      · obtain rfl : N = 1364 := by omega
        exact cen1364
      · by_cases h8 : N ≤ 1366
        · obtain rfl : N = 1366 := by omega
          exact cen1366
        · obtain rfl : N = 1368 := by omega
          exact cen1368
  · by_cases h4 : N ≤ 1374
    · by_cases h6 : N ≤ 1370
      · obtain rfl : N = 1370 := by omega
        exact cen1370
      · by_cases h8 : N ≤ 1372
        · obtain rfl : N = 1372 := by omega
          exact cen1372
        · obtain rfl : N = 1374 := by omega
          exact cen1374
    · by_cases h6 : N ≤ 1376
      · obtain rfl : N = 1376 := by omega
        exact cen1376
      · by_cases h8 : N ≤ 1378
        · obtain rfl : N = 1378 := by omega
          exact cen1378
        · obtain rfl : N = 1380 := by omega
          exact cen1380

end Kagey131.PaperD.T7
