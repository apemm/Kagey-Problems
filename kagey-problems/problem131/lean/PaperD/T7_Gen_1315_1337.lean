import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1315, …, 1337` (generated)

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

/-! ### `N = 1315` -/

def pL1315 : Prm := ⟨79, 37, 39, 1317, 11, 18446744073709551616, 138464667816978913, 138464667816978913⟩
def pH1315 : Prm := ⟨79, 37, 39, 1317, 11, 18446744073709551616, 138465767328606689, 138465767328606689⟩
def pI1315 : Prm := ⟨66, 32, 31, 1317, 11, 18446744073709551616, 138464667816978913, 138465767328606689⟩
noncomputable def L1315_cp1 : Nat × Nat := t7val% (fastRun pL1315 1 929 (init pL1315) (init pL1315))
theorem L1315_seg1 : segOK pL1315 1 929 (init pL1315) (init pL1315) L1315_cp1.1 L1315_cp1.2 = true := by
  decide +kernel
theorem L1315_fin : (prmOK pL1315 1315 && ptTest pL1315 (runFrom pL1315 (fmask pL1315) (cmask pL1315) (hmask pL1315) 930 385 (true, L1315_cp1.1, L1315_cp1.2)) 1315 658 false) = true := by
  decide +kernel
theorem L1315_ok : RunOK pL1315 1315 (runFrom pL1315 (fmask pL1315) (cmask pL1315) (hmask pL1315) 930 385 (true, L1315_cp1.1, L1315_cp1.2)) ∧ ptTest pL1315 (runFrom pL1315 (fmask pL1315) (cmask pL1315) (hmask pL1315) 930 385 (true, L1315_cp1.1, L1315_cp1.2)) 1315 658 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1315_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1315_fin) true) L1315_seg1) (by decide) rfl L1315_fin ptTest_fst
noncomputable def H1315_cp1 : Nat × Nat := t7val% (fastRun pH1315 1 929 (init pH1315) (init pH1315))
theorem H1315_seg1 : segOK pH1315 1 929 (init pH1315) (init pH1315) H1315_cp1.1 H1315_cp1.2 = true := by
  decide +kernel
theorem H1315_fin : (prmOK pH1315 1315 && ptTest pH1315 (runFrom pH1315 (fmask pH1315) (cmask pH1315) (hmask pH1315) 930 385 (true, H1315_cp1.1, H1315_cp1.2)) 1315 658 true) = true := by
  decide +kernel
theorem H1315_ok : RunOK pH1315 1315 (runFrom pH1315 (fmask pH1315) (cmask pH1315) (hmask pH1315) 930 385 (true, H1315_cp1.1, H1315_cp1.2)) ∧ ptTest pH1315 (runFrom pH1315 (fmask pH1315) (cmask pH1315) (hmask pH1315) 930 385 (true, H1315_cp1.1, H1315_cp1.2)) 1315 658 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1315_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1315_fin) true) H1315_seg1) (by decide) rfl H1315_fin ptTest_fst
noncomputable def I1315_cp1 : Nat × Nat := t7val% (fastRun pI1315 1 929 (init pI1315) (init pI1315))
theorem I1315_seg1 : segOK pI1315 1 929 (init pI1315) (init pI1315) I1315_cp1.1 I1315_cp1.2 = true := by
  decide +kernel
theorem I1315_fin : (prmOK pI1315 1315 && intTest pI1315 (runFrom pI1315 (fmask pI1315) (cmask pI1315) (hmask pI1315) 930 385 (true, I1315_cp1.1, I1315_cp1.2)) 1315 19 false) = true := by
  decide +kernel
theorem I1315_ok : RunOK pI1315 1315 (runFrom pI1315 (fmask pI1315) (cmask pI1315) (hmask pI1315) 930 385 (true, I1315_cp1.1, I1315_cp1.2)) ∧ intTest pI1315 (runFrom pI1315 (fmask pI1315) (cmask pI1315) (hmask pI1315) 930 385 (true, I1315_cp1.1, I1315_cp1.2)) 1315 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1315_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1315_fin) true) I1315_seg1) (by decide) rfl I1315_fin intTest_fst
theorem link1315 : linkOK pL1315 pH1315 pI1315 = true := by decide +kernel
theorem cvx1315 : ConvexBetweenHumps 1315 :=
  cvx_of L1315_ok H1315_ok I1315_ok link1315 (by decide)

/-! ### `N = 1316` -/

def pL1316 : Prm := ⟨79, 37, 39, 1318, 11, 18446744073709551616, 138379569989469041, 138379569989469041⟩
def pH1316 : Prm := ⟨79, 37, 39, 1318, 11, 18446744073709551616, 138380669501096817, 138380669501096817⟩
def pI1316 : Prm := ⟨66, 32, 31, 1318, 11, 18446744073709551616, 138379569989469041, 138380669501096817⟩
noncomputable def L1316_cp1 : Nat × Nat := t7val% (fastRun pL1316 1 930 (init pL1316) (init pL1316))
theorem L1316_seg1 : segOK pL1316 1 930 (init pL1316) (init pL1316) L1316_cp1.1 L1316_cp1.2 = true := by
  decide +kernel
theorem L1316_fin : (prmOK pL1316 1316 && ptTest pL1316 (runFrom pL1316 (fmask pL1316) (cmask pL1316) (hmask pL1316) 931 385 (true, L1316_cp1.1, L1316_cp1.2)) 1316 658 false) = true := by
  decide +kernel
theorem L1316_ok : RunOK pL1316 1316 (runFrom pL1316 (fmask pL1316) (cmask pL1316) (hmask pL1316) 931 385 (true, L1316_cp1.1, L1316_cp1.2)) ∧ ptTest pL1316 (runFrom pL1316 (fmask pL1316) (cmask pL1316) (hmask pL1316) 931 385 (true, L1316_cp1.1, L1316_cp1.2)) 1316 658 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1316_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1316_fin) true) L1316_seg1) (by decide) rfl L1316_fin ptTest_fst
noncomputable def H1316_cp1 : Nat × Nat := t7val% (fastRun pH1316 1 930 (init pH1316) (init pH1316))
theorem H1316_seg1 : segOK pH1316 1 930 (init pH1316) (init pH1316) H1316_cp1.1 H1316_cp1.2 = true := by
  decide +kernel
theorem H1316_fin : (prmOK pH1316 1316 && ptTest pH1316 (runFrom pH1316 (fmask pH1316) (cmask pH1316) (hmask pH1316) 931 385 (true, H1316_cp1.1, H1316_cp1.2)) 1316 658 true) = true := by
  decide +kernel
theorem H1316_ok : RunOK pH1316 1316 (runFrom pH1316 (fmask pH1316) (cmask pH1316) (hmask pH1316) 931 385 (true, H1316_cp1.1, H1316_cp1.2)) ∧ ptTest pH1316 (runFrom pH1316 (fmask pH1316) (cmask pH1316) (hmask pH1316) 931 385 (true, H1316_cp1.1, H1316_cp1.2)) 1316 658 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1316_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1316_fin) true) H1316_seg1) (by decide) rfl H1316_fin ptTest_fst
noncomputable def I1316_cp1 : Nat × Nat := t7val% (fastRun pI1316 1 930 (init pI1316) (init pI1316))
theorem I1316_seg1 : segOK pI1316 1 930 (init pI1316) (init pI1316) I1316_cp1.1 I1316_cp1.2 = true := by
  decide +kernel
theorem I1316_fin : (prmOK pI1316 1316 && intTest pI1316 (runFrom pI1316 (fmask pI1316) (cmask pI1316) (hmask pI1316) 931 385 (true, I1316_cp1.1, I1316_cp1.2)) 1316 19 true) = true := by
  decide +kernel
theorem I1316_ok : RunOK pI1316 1316 (runFrom pI1316 (fmask pI1316) (cmask pI1316) (hmask pI1316) 931 385 (true, I1316_cp1.1, I1316_cp1.2)) ∧ intTest pI1316 (runFrom pI1316 (fmask pI1316) (cmask pI1316) (hmask pI1316) 931 385 (true, I1316_cp1.1, I1316_cp1.2)) 1316 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1316_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1316_fin) true) I1316_seg1) (by decide) rfl I1316_fin intTest_fst
theorem link1316 : linkOK pL1316 pH1316 pI1316 = true := by decide +kernel
theorem cvx1316 : ConvexBetweenHumps 1316 :=
  cvx_of L1316_ok H1316_ok I1316_ok link1316 (by decide)
theorem cenlink1316 : cenLinkOK pI1316 1316 = true := by decide +kernel
theorem cen1316 : CenterUniqueMin 1316 ∧ DipHyp 1316 ∧ OnePointHyps 1316 :=
  cen_of L1316_ok H1316_ok I1316_ok link1316 cenlink1316

/-! ### `N = 1317` -/

def pL1317 : Prm := ⟨79, 37, 39, 1319, 11, 18446744073709551616, 138294536173747524, 138294536173747524⟩
def pH1317 : Prm := ⟨79, 37, 39, 1319, 11, 18446744073709551616, 138295635685375300, 138295635685375300⟩
def pI1317 : Prm := ⟨66, 32, 31, 1319, 11, 18446744073709551616, 138294536173747524, 138295635685375300⟩
noncomputable def L1317_cp1 : Nat × Nat := t7val% (fastRun pL1317 1 930 (init pL1317) (init pL1317))
theorem L1317_seg1 : segOK pL1317 1 930 (init pL1317) (init pL1317) L1317_cp1.1 L1317_cp1.2 = true := by
  decide +kernel
theorem L1317_fin : (prmOK pL1317 1317 && ptTest pL1317 (runFrom pL1317 (fmask pL1317) (cmask pL1317) (hmask pL1317) 931 386 (true, L1317_cp1.1, L1317_cp1.2)) 1317 659 false) = true := by
  decide +kernel
theorem L1317_ok : RunOK pL1317 1317 (runFrom pL1317 (fmask pL1317) (cmask pL1317) (hmask pL1317) 931 386 (true, L1317_cp1.1, L1317_cp1.2)) ∧ ptTest pL1317 (runFrom pL1317 (fmask pL1317) (cmask pL1317) (hmask pL1317) 931 386 (true, L1317_cp1.1, L1317_cp1.2)) 1317 659 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1317_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1317_fin) true) L1317_seg1) (by decide) rfl L1317_fin ptTest_fst
noncomputable def H1317_cp1 : Nat × Nat := t7val% (fastRun pH1317 1 930 (init pH1317) (init pH1317))
theorem H1317_seg1 : segOK pH1317 1 930 (init pH1317) (init pH1317) H1317_cp1.1 H1317_cp1.2 = true := by
  decide +kernel
theorem H1317_fin : (prmOK pH1317 1317 && ptTest pH1317 (runFrom pH1317 (fmask pH1317) (cmask pH1317) (hmask pH1317) 931 386 (true, H1317_cp1.1, H1317_cp1.2)) 1317 659 true) = true := by
  decide +kernel
theorem H1317_ok : RunOK pH1317 1317 (runFrom pH1317 (fmask pH1317) (cmask pH1317) (hmask pH1317) 931 386 (true, H1317_cp1.1, H1317_cp1.2)) ∧ ptTest pH1317 (runFrom pH1317 (fmask pH1317) (cmask pH1317) (hmask pH1317) 931 386 (true, H1317_cp1.1, H1317_cp1.2)) 1317 659 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1317_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1317_fin) true) H1317_seg1) (by decide) rfl H1317_fin ptTest_fst
noncomputable def I1317_cp1 : Nat × Nat := t7val% (fastRun pI1317 1 930 (init pI1317) (init pI1317))
theorem I1317_seg1 : segOK pI1317 1 930 (init pI1317) (init pI1317) I1317_cp1.1 I1317_cp1.2 = true := by
  decide +kernel
theorem I1317_fin : (prmOK pI1317 1317 && intTest pI1317 (runFrom pI1317 (fmask pI1317) (cmask pI1317) (hmask pI1317) 931 386 (true, I1317_cp1.1, I1317_cp1.2)) 1317 19 false) = true := by
  decide +kernel
theorem I1317_ok : RunOK pI1317 1317 (runFrom pI1317 (fmask pI1317) (cmask pI1317) (hmask pI1317) 931 386 (true, I1317_cp1.1, I1317_cp1.2)) ∧ intTest pI1317 (runFrom pI1317 (fmask pI1317) (cmask pI1317) (hmask pI1317) 931 386 (true, I1317_cp1.1, I1317_cp1.2)) 1317 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1317_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1317_fin) true) I1317_seg1) (by decide) rfl I1317_fin intTest_fst
theorem link1317 : linkOK pL1317 pH1317 pI1317 = true := by decide +kernel
theorem cvx1317 : ConvexBetweenHumps 1317 :=
  cvx_of L1317_ok H1317_ok I1317_ok link1317 (by decide)

/-! ### `N = 1318` -/

def pL1318 : Prm := ⟨79, 37, 39, 1320, 11, 18446744073709551616, 138209666001121828, 138209666001121828⟩
def pH1318 : Prm := ⟨79, 37, 39, 1320, 11, 18446744073709551616, 138210765512749604, 138210765512749604⟩
def pI1318 : Prm := ⟨67, 32, 32, 1320, 11, 18446744073709551616, 138209666001121828, 138210765512749604⟩
noncomputable def L1318_cp1 : Nat × Nat := t7val% (fastRun pL1318 1 931 (init pL1318) (init pL1318))
theorem L1318_seg1 : segOK pL1318 1 931 (init pL1318) (init pL1318) L1318_cp1.1 L1318_cp1.2 = true := by
  decide +kernel
theorem L1318_fin : (prmOK pL1318 1318 && ptTest pL1318 (runFrom pL1318 (fmask pL1318) (cmask pL1318) (hmask pL1318) 932 386 (true, L1318_cp1.1, L1318_cp1.2)) 1318 659 false) = true := by
  decide +kernel
theorem L1318_ok : RunOK pL1318 1318 (runFrom pL1318 (fmask pL1318) (cmask pL1318) (hmask pL1318) 932 386 (true, L1318_cp1.1, L1318_cp1.2)) ∧ ptTest pL1318 (runFrom pL1318 (fmask pL1318) (cmask pL1318) (hmask pL1318) 932 386 (true, L1318_cp1.1, L1318_cp1.2)) 1318 659 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1318_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1318_fin) true) L1318_seg1) (by decide) rfl L1318_fin ptTest_fst
noncomputable def H1318_cp1 : Nat × Nat := t7val% (fastRun pH1318 1 931 (init pH1318) (init pH1318))
theorem H1318_seg1 : segOK pH1318 1 931 (init pH1318) (init pH1318) H1318_cp1.1 H1318_cp1.2 = true := by
  decide +kernel
theorem H1318_fin : (prmOK pH1318 1318 && ptTest pH1318 (runFrom pH1318 (fmask pH1318) (cmask pH1318) (hmask pH1318) 932 386 (true, H1318_cp1.1, H1318_cp1.2)) 1318 659 true) = true := by
  decide +kernel
theorem H1318_ok : RunOK pH1318 1318 (runFrom pH1318 (fmask pH1318) (cmask pH1318) (hmask pH1318) 932 386 (true, H1318_cp1.1, H1318_cp1.2)) ∧ ptTest pH1318 (runFrom pH1318 (fmask pH1318) (cmask pH1318) (hmask pH1318) 932 386 (true, H1318_cp1.1, H1318_cp1.2)) 1318 659 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1318_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1318_fin) true) H1318_seg1) (by decide) rfl H1318_fin ptTest_fst
noncomputable def I1318_cp1 : Nat × Nat := t7val% (fastRun pI1318 1 931 (init pI1318) (init pI1318))
theorem I1318_seg1 : segOK pI1318 1 931 (init pI1318) (init pI1318) I1318_cp1.1 I1318_cp1.2 = true := by
  decide +kernel
theorem I1318_fin : (prmOK pI1318 1318 && intTest pI1318 (runFrom pI1318 (fmask pI1318) (cmask pI1318) (hmask pI1318) 932 386 (true, I1318_cp1.1, I1318_cp1.2)) 1318 19 true) = true := by
  decide +kernel
theorem I1318_ok : RunOK pI1318 1318 (runFrom pI1318 (fmask pI1318) (cmask pI1318) (hmask pI1318) 932 386 (true, I1318_cp1.1, I1318_cp1.2)) ∧ intTest pI1318 (runFrom pI1318 (fmask pI1318) (cmask pI1318) (hmask pI1318) 932 386 (true, I1318_cp1.1, I1318_cp1.2)) 1318 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1318_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1318_fin) true) I1318_seg1) (by decide) rfl I1318_fin intTest_fst
theorem link1318 : linkOK pL1318 pH1318 pI1318 = true := by decide +kernel
theorem cvx1318 : ConvexBetweenHumps 1318 :=
  cvx_of L1318_ok H1318_ok I1318_ok link1318 (by decide)
theorem cenlink1318 : cenLinkOK pI1318 1318 = true := by decide +kernel
theorem cen1318 : CenterUniqueMin 1318 ∧ DipHyp 1318 ∧ OnePointHyps 1318 :=
  cen_of L1318_ok H1318_ok I1318_ok link1318 cenlink1318

/-! ### `N = 1319` -/

def pL1319 : Prm := ⟨79, 37, 39, 1321, 11, 18446744073709551616, 138124859599314669, 138124859599314669⟩
def pH1319 : Prm := ⟨79, 37, 39, 1321, 11, 18446744073709551616, 138125959110942445, 138125959110942445⟩
def pI1319 : Prm := ⟨66, 32, 31, 1321, 11, 18446744073709551616, 138124859599314669, 138125959110942445⟩
noncomputable def L1319_cp1 : Nat × Nat := t7val% (fastRun pL1319 1 932 (init pL1319) (init pL1319))
theorem L1319_seg1 : segOK pL1319 1 932 (init pL1319) (init pL1319) L1319_cp1.1 L1319_cp1.2 = true := by
  decide +kernel
theorem L1319_fin : (prmOK pL1319 1319 && ptTest pL1319 (runFrom pL1319 (fmask pL1319) (cmask pL1319) (hmask pL1319) 933 386 (true, L1319_cp1.1, L1319_cp1.2)) 1319 660 false) = true := by
  decide +kernel
theorem L1319_ok : RunOK pL1319 1319 (runFrom pL1319 (fmask pL1319) (cmask pL1319) (hmask pL1319) 933 386 (true, L1319_cp1.1, L1319_cp1.2)) ∧ ptTest pL1319 (runFrom pL1319 (fmask pL1319) (cmask pL1319) (hmask pL1319) 933 386 (true, L1319_cp1.1, L1319_cp1.2)) 1319 660 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1319_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1319_fin) true) L1319_seg1) (by decide) rfl L1319_fin ptTest_fst
noncomputable def H1319_cp1 : Nat × Nat := t7val% (fastRun pH1319 1 932 (init pH1319) (init pH1319))
theorem H1319_seg1 : segOK pH1319 1 932 (init pH1319) (init pH1319) H1319_cp1.1 H1319_cp1.2 = true := by
  decide +kernel
theorem H1319_fin : (prmOK pH1319 1319 && ptTest pH1319 (runFrom pH1319 (fmask pH1319) (cmask pH1319) (hmask pH1319) 933 386 (true, H1319_cp1.1, H1319_cp1.2)) 1319 660 true) = true := by
  decide +kernel
theorem H1319_ok : RunOK pH1319 1319 (runFrom pH1319 (fmask pH1319) (cmask pH1319) (hmask pH1319) 933 386 (true, H1319_cp1.1, H1319_cp1.2)) ∧ ptTest pH1319 (runFrom pH1319 (fmask pH1319) (cmask pH1319) (hmask pH1319) 933 386 (true, H1319_cp1.1, H1319_cp1.2)) 1319 660 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1319_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1319_fin) true) H1319_seg1) (by decide) rfl H1319_fin ptTest_fst
noncomputable def I1319_cp1 : Nat × Nat := t7val% (fastRun pI1319 1 932 (init pI1319) (init pI1319))
theorem I1319_seg1 : segOK pI1319 1 932 (init pI1319) (init pI1319) I1319_cp1.1 I1319_cp1.2 = true := by
  decide +kernel
theorem I1319_fin : (prmOK pI1319 1319 && intTest pI1319 (runFrom pI1319 (fmask pI1319) (cmask pI1319) (hmask pI1319) 933 386 (true, I1319_cp1.1, I1319_cp1.2)) 1319 19 false) = true := by
  decide +kernel
theorem I1319_ok : RunOK pI1319 1319 (runFrom pI1319 (fmask pI1319) (cmask pI1319) (hmask pI1319) 933 386 (true, I1319_cp1.1, I1319_cp1.2)) ∧ intTest pI1319 (runFrom pI1319 (fmask pI1319) (cmask pI1319) (hmask pI1319) 933 386 (true, I1319_cp1.1, I1319_cp1.2)) 1319 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1319_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1319_fin) true) I1319_seg1) (by decide) rfl I1319_fin intTest_fst
theorem link1319 : linkOK pL1319 pH1319 pI1319 = true := by decide +kernel
theorem cvx1319 : ConvexBetweenHumps 1319 :=
  cvx_of L1319_ok H1319_ok I1319_ok link1319 (by decide)

/-! ### `N = 1320` -/

def pL1320 : Prm := ⟨79, 37, 39, 1322, 11, 18446744073709551616, 138040216139534822, 138040216139534822⟩
def pH1320 : Prm := ⟨79, 37, 39, 1322, 11, 18446744073709551616, 138041315651162598, 138041315651162598⟩
def pI1320 : Prm := ⟨66, 32, 31, 1322, 11, 18446744073709551616, 138040216139534822, 138041315651162598⟩
noncomputable def L1320_cp1 : Nat × Nat := t7val% (fastRun pL1320 1 932 (init pL1320) (init pL1320))
theorem L1320_seg1 : segOK pL1320 1 932 (init pL1320) (init pL1320) L1320_cp1.1 L1320_cp1.2 = true := by
  decide +kernel
theorem L1320_fin : (prmOK pL1320 1320 && ptTest pL1320 (runFrom pL1320 (fmask pL1320) (cmask pL1320) (hmask pL1320) 933 387 (true, L1320_cp1.1, L1320_cp1.2)) 1320 660 false) = true := by
  decide +kernel
theorem L1320_ok : RunOK pL1320 1320 (runFrom pL1320 (fmask pL1320) (cmask pL1320) (hmask pL1320) 933 387 (true, L1320_cp1.1, L1320_cp1.2)) ∧ ptTest pL1320 (runFrom pL1320 (fmask pL1320) (cmask pL1320) (hmask pL1320) 933 387 (true, L1320_cp1.1, L1320_cp1.2)) 1320 660 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1320_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1320_fin) true) L1320_seg1) (by decide) rfl L1320_fin ptTest_fst
noncomputable def H1320_cp1 : Nat × Nat := t7val% (fastRun pH1320 1 932 (init pH1320) (init pH1320))
theorem H1320_seg1 : segOK pH1320 1 932 (init pH1320) (init pH1320) H1320_cp1.1 H1320_cp1.2 = true := by
  decide +kernel
theorem H1320_fin : (prmOK pH1320 1320 && ptTest pH1320 (runFrom pH1320 (fmask pH1320) (cmask pH1320) (hmask pH1320) 933 387 (true, H1320_cp1.1, H1320_cp1.2)) 1320 660 true) = true := by
  decide +kernel
theorem H1320_ok : RunOK pH1320 1320 (runFrom pH1320 (fmask pH1320) (cmask pH1320) (hmask pH1320) 933 387 (true, H1320_cp1.1, H1320_cp1.2)) ∧ ptTest pH1320 (runFrom pH1320 (fmask pH1320) (cmask pH1320) (hmask pH1320) 933 387 (true, H1320_cp1.1, H1320_cp1.2)) 1320 660 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1320_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1320_fin) true) H1320_seg1) (by decide) rfl H1320_fin ptTest_fst
noncomputable def I1320_cp1 : Nat × Nat := t7val% (fastRun pI1320 1 932 (init pI1320) (init pI1320))
theorem I1320_seg1 : segOK pI1320 1 932 (init pI1320) (init pI1320) I1320_cp1.1 I1320_cp1.2 = true := by
  decide +kernel
theorem I1320_fin : (prmOK pI1320 1320 && intTest pI1320 (runFrom pI1320 (fmask pI1320) (cmask pI1320) (hmask pI1320) 933 387 (true, I1320_cp1.1, I1320_cp1.2)) 1320 19 true) = true := by
  decide +kernel
theorem I1320_ok : RunOK pI1320 1320 (runFrom pI1320 (fmask pI1320) (cmask pI1320) (hmask pI1320) 933 387 (true, I1320_cp1.1, I1320_cp1.2)) ∧ intTest pI1320 (runFrom pI1320 (fmask pI1320) (cmask pI1320) (hmask pI1320) 933 387 (true, I1320_cp1.1, I1320_cp1.2)) 1320 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1320_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1320_fin) true) I1320_seg1) (by decide) rfl I1320_fin intTest_fst
theorem link1320 : linkOK pL1320 pH1320 pI1320 = true := by decide +kernel
theorem cvx1320 : ConvexBetweenHumps 1320 :=
  cvx_of L1320_ok H1320_ok I1320_ok link1320 (by decide)
theorem cenlink1320 : cenLinkOK pI1320 1320 = true := by decide +kernel
theorem cen1320 : CenterUniqueMin 1320 ∧ DipHyp 1320 ∧ OnePointHyps 1320 :=
  cen_of L1320_ok H1320_ok I1320_ok link1320 cenlink1320

/-! ### `N = 1321` -/

def pL1321 : Prm := ⟨79, 37, 39, 1323, 11, 18446744073709551616, 137955636210765839, 137955636210765839⟩
def pH1321 : Prm := ⟨79, 37, 39, 1323, 11, 18446744073709551616, 137956735722393615, 137956735722393615⟩
def pI1321 : Prm := ⟨67, 32, 32, 1323, 11, 18446744073709551616, 137955636210765839, 137956735722393615⟩
noncomputable def L1321_cp1 : Nat × Nat := t7val% (fastRun pL1321 1 933 (init pL1321) (init pL1321))
theorem L1321_seg1 : segOK pL1321 1 933 (init pL1321) (init pL1321) L1321_cp1.1 L1321_cp1.2 = true := by
  decide +kernel
theorem L1321_fin : (prmOK pL1321 1321 && ptTest pL1321 (runFrom pL1321 (fmask pL1321) (cmask pL1321) (hmask pL1321) 934 387 (true, L1321_cp1.1, L1321_cp1.2)) 1321 661 false) = true := by
  decide +kernel
theorem L1321_ok : RunOK pL1321 1321 (runFrom pL1321 (fmask pL1321) (cmask pL1321) (hmask pL1321) 934 387 (true, L1321_cp1.1, L1321_cp1.2)) ∧ ptTest pL1321 (runFrom pL1321 (fmask pL1321) (cmask pL1321) (hmask pL1321) 934 387 (true, L1321_cp1.1, L1321_cp1.2)) 1321 661 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1321_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1321_fin) true) L1321_seg1) (by decide) rfl L1321_fin ptTest_fst
noncomputable def H1321_cp1 : Nat × Nat := t7val% (fastRun pH1321 1 933 (init pH1321) (init pH1321))
theorem H1321_seg1 : segOK pH1321 1 933 (init pH1321) (init pH1321) H1321_cp1.1 H1321_cp1.2 = true := by
  decide +kernel
theorem H1321_fin : (prmOK pH1321 1321 && ptTest pH1321 (runFrom pH1321 (fmask pH1321) (cmask pH1321) (hmask pH1321) 934 387 (true, H1321_cp1.1, H1321_cp1.2)) 1321 661 true) = true := by
  decide +kernel
theorem H1321_ok : RunOK pH1321 1321 (runFrom pH1321 (fmask pH1321) (cmask pH1321) (hmask pH1321) 934 387 (true, H1321_cp1.1, H1321_cp1.2)) ∧ ptTest pH1321 (runFrom pH1321 (fmask pH1321) (cmask pH1321) (hmask pH1321) 934 387 (true, H1321_cp1.1, H1321_cp1.2)) 1321 661 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1321_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1321_fin) true) H1321_seg1) (by decide) rfl H1321_fin ptTest_fst
noncomputable def I1321_cp1 : Nat × Nat := t7val% (fastRun pI1321 1 933 (init pI1321) (init pI1321))
theorem I1321_seg1 : segOK pI1321 1 933 (init pI1321) (init pI1321) I1321_cp1.1 I1321_cp1.2 = true := by
  decide +kernel
theorem I1321_fin : (prmOK pI1321 1321 && intTest pI1321 (runFrom pI1321 (fmask pI1321) (cmask pI1321) (hmask pI1321) 934 387 (true, I1321_cp1.1, I1321_cp1.2)) 1321 19 false) = true := by
  decide +kernel
theorem I1321_ok : RunOK pI1321 1321 (runFrom pI1321 (fmask pI1321) (cmask pI1321) (hmask pI1321) 934 387 (true, I1321_cp1.1, I1321_cp1.2)) ∧ intTest pI1321 (runFrom pI1321 (fmask pI1321) (cmask pI1321) (hmask pI1321) 934 387 (true, I1321_cp1.1, I1321_cp1.2)) 1321 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1321_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1321_fin) true) I1321_seg1) (by decide) rfl I1321_fin intTest_fst
theorem link1321 : linkOK pL1321 pH1321 pI1321 = true := by decide +kernel
theorem cvx1321 : ConvexBetweenHumps 1321 :=
  cvx_of L1321_ok H1321_ok I1321_ok link1321 (by decide)

/-! ### `N = 1322` -/

def pL1322 : Prm := ⟨79, 37, 39, 1324, 11, 18446744073709551616, 137871218526995497, 137871218526995497⟩
def pH1322 : Prm := ⟨79, 37, 39, 1324, 11, 18446744073709551616, 137872318038623273, 137872318038623273⟩
def pI1322 : Prm := ⟨67, 32, 32, 1324, 11, 18446744073709551616, 137871218526995497, 137872318038623273⟩
noncomputable def L1322_cp1 : Nat × Nat := t7val% (fastRun pL1322 1 934 (init pL1322) (init pL1322))
theorem L1322_seg1 : segOK pL1322 1 934 (init pL1322) (init pL1322) L1322_cp1.1 L1322_cp1.2 = true := by
  decide +kernel
theorem L1322_fin : (prmOK pL1322 1322 && ptTest pL1322 (runFrom pL1322 (fmask pL1322) (cmask pL1322) (hmask pL1322) 935 387 (true, L1322_cp1.1, L1322_cp1.2)) 1322 661 false) = true := by
  decide +kernel
theorem L1322_ok : RunOK pL1322 1322 (runFrom pL1322 (fmask pL1322) (cmask pL1322) (hmask pL1322) 935 387 (true, L1322_cp1.1, L1322_cp1.2)) ∧ ptTest pL1322 (runFrom pL1322 (fmask pL1322) (cmask pL1322) (hmask pL1322) 935 387 (true, L1322_cp1.1, L1322_cp1.2)) 1322 661 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1322_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1322_fin) true) L1322_seg1) (by decide) rfl L1322_fin ptTest_fst
noncomputable def H1322_cp1 : Nat × Nat := t7val% (fastRun pH1322 1 934 (init pH1322) (init pH1322))
theorem H1322_seg1 : segOK pH1322 1 934 (init pH1322) (init pH1322) H1322_cp1.1 H1322_cp1.2 = true := by
  decide +kernel
theorem H1322_fin : (prmOK pH1322 1322 && ptTest pH1322 (runFrom pH1322 (fmask pH1322) (cmask pH1322) (hmask pH1322) 935 387 (true, H1322_cp1.1, H1322_cp1.2)) 1322 661 true) = true := by
  decide +kernel
theorem H1322_ok : RunOK pH1322 1322 (runFrom pH1322 (fmask pH1322) (cmask pH1322) (hmask pH1322) 935 387 (true, H1322_cp1.1, H1322_cp1.2)) ∧ ptTest pH1322 (runFrom pH1322 (fmask pH1322) (cmask pH1322) (hmask pH1322) 935 387 (true, H1322_cp1.1, H1322_cp1.2)) 1322 661 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1322_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1322_fin) true) H1322_seg1) (by decide) rfl H1322_fin ptTest_fst
noncomputable def I1322_cp1 : Nat × Nat := t7val% (fastRun pI1322 1 934 (init pI1322) (init pI1322))
theorem I1322_seg1 : segOK pI1322 1 934 (init pI1322) (init pI1322) I1322_cp1.1 I1322_cp1.2 = true := by
  decide +kernel
theorem I1322_fin : (prmOK pI1322 1322 && intTest pI1322 (runFrom pI1322 (fmask pI1322) (cmask pI1322) (hmask pI1322) 935 387 (true, I1322_cp1.1, I1322_cp1.2)) 1322 19 true) = true := by
  decide +kernel
theorem I1322_ok : RunOK pI1322 1322 (runFrom pI1322 (fmask pI1322) (cmask pI1322) (hmask pI1322) 935 387 (true, I1322_cp1.1, I1322_cp1.2)) ∧ intTest pI1322 (runFrom pI1322 (fmask pI1322) (cmask pI1322) (hmask pI1322) 935 387 (true, I1322_cp1.1, I1322_cp1.2)) 1322 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1322_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1322_fin) true) I1322_seg1) (by decide) rfl I1322_fin intTest_fst
theorem link1322 : linkOK pL1322 pH1322 pI1322 = true := by decide +kernel
theorem cvx1322 : ConvexBetweenHumps 1322 :=
  cvx_of L1322_ok H1322_ok I1322_ok link1322 (by decide)
theorem cenlink1322 : cenLinkOK pI1322 1322 = true := by decide +kernel
theorem cen1322 : CenterUniqueMin 1322 ∧ DipHyp 1322 ∧ OnePointHyps 1322 :=
  cen_of L1322_ok H1322_ok I1322_ok link1322 cenlink1322

/-! ### `N = 1323` -/

def pL1323 : Prm := ⟨79, 37, 39, 1325, 11, 18446744073709551616, 137786864135719618, 137786864135719618⟩
def pH1323 : Prm := ⟨79, 37, 39, 1325, 11, 18446744073709551616, 137787963647347394, 137787963647347394⟩
def pI1323 : Prm := ⟨66, 32, 31, 1325, 11, 18446744073709551616, 137786864135719618, 137787963647347394⟩
noncomputable def L1323_cp1 : Nat × Nat := t7val% (fastRun pL1323 1 935 (init pL1323) (init pL1323))
theorem L1323_seg1 : segOK pL1323 1 935 (init pL1323) (init pL1323) L1323_cp1.1 L1323_cp1.2 = true := by
  decide +kernel
theorem L1323_fin : (prmOK pL1323 1323 && ptTest pL1323 (runFrom pL1323 (fmask pL1323) (cmask pL1323) (hmask pL1323) 936 387 (true, L1323_cp1.1, L1323_cp1.2)) 1323 662 false) = true := by
  decide +kernel
theorem L1323_ok : RunOK pL1323 1323 (runFrom pL1323 (fmask pL1323) (cmask pL1323) (hmask pL1323) 936 387 (true, L1323_cp1.1, L1323_cp1.2)) ∧ ptTest pL1323 (runFrom pL1323 (fmask pL1323) (cmask pL1323) (hmask pL1323) 936 387 (true, L1323_cp1.1, L1323_cp1.2)) 1323 662 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1323_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1323_fin) true) L1323_seg1) (by decide) rfl L1323_fin ptTest_fst
noncomputable def H1323_cp1 : Nat × Nat := t7val% (fastRun pH1323 1 935 (init pH1323) (init pH1323))
theorem H1323_seg1 : segOK pH1323 1 935 (init pH1323) (init pH1323) H1323_cp1.1 H1323_cp1.2 = true := by
  decide +kernel
theorem H1323_fin : (prmOK pH1323 1323 && ptTest pH1323 (runFrom pH1323 (fmask pH1323) (cmask pH1323) (hmask pH1323) 936 387 (true, H1323_cp1.1, H1323_cp1.2)) 1323 662 true) = true := by
  decide +kernel
theorem H1323_ok : RunOK pH1323 1323 (runFrom pH1323 (fmask pH1323) (cmask pH1323) (hmask pH1323) 936 387 (true, H1323_cp1.1, H1323_cp1.2)) ∧ ptTest pH1323 (runFrom pH1323 (fmask pH1323) (cmask pH1323) (hmask pH1323) 936 387 (true, H1323_cp1.1, H1323_cp1.2)) 1323 662 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1323_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1323_fin) true) H1323_seg1) (by decide) rfl H1323_fin ptTest_fst
noncomputable def I1323_cp1 : Nat × Nat := t7val% (fastRun pI1323 1 935 (init pI1323) (init pI1323))
theorem I1323_seg1 : segOK pI1323 1 935 (init pI1323) (init pI1323) I1323_cp1.1 I1323_cp1.2 = true := by
  decide +kernel
theorem I1323_fin : (prmOK pI1323 1323 && intTest pI1323 (runFrom pI1323 (fmask pI1323) (cmask pI1323) (hmask pI1323) 936 387 (true, I1323_cp1.1, I1323_cp1.2)) 1323 19 false) = true := by
  decide +kernel
theorem I1323_ok : RunOK pI1323 1323 (runFrom pI1323 (fmask pI1323) (cmask pI1323) (hmask pI1323) 936 387 (true, I1323_cp1.1, I1323_cp1.2)) ∧ intTest pI1323 (runFrom pI1323 (fmask pI1323) (cmask pI1323) (hmask pI1323) 936 387 (true, I1323_cp1.1, I1323_cp1.2)) 1323 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1323_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1323_fin) true) I1323_seg1) (by decide) rfl I1323_fin intTest_fst
theorem link1323 : linkOK pL1323 pH1323 pI1323 = true := by decide +kernel
theorem cvx1323 : ConvexBetweenHumps 1323 :=
  cvx_of L1323_ok H1323_ok I1323_ok link1323 (by decide)

/-! ### `N = 1324` -/

def pL1324 : Prm := ⟨79, 37, 39, 1326, 11, 18446744073709551616, 137702671296398204, 137702671296398204⟩
def pH1324 : Prm := ⟨79, 37, 39, 1326, 11, 18446744073709551616, 137703770808025980, 137703770808025980⟩
def pI1324 : Prm := ⟨67, 32, 32, 1326, 11, 18446744073709551616, 137702671296398204, 137703770808025980⟩
noncomputable def L1324_cp1 : Nat × Nat := t7val% (fastRun pL1324 1 935 (init pL1324) (init pL1324))
theorem L1324_seg1 : segOK pL1324 1 935 (init pL1324) (init pL1324) L1324_cp1.1 L1324_cp1.2 = true := by
  decide +kernel
theorem L1324_fin : (prmOK pL1324 1324 && ptTest pL1324 (runFrom pL1324 (fmask pL1324) (cmask pL1324) (hmask pL1324) 936 388 (true, L1324_cp1.1, L1324_cp1.2)) 1324 662 false) = true := by
  decide +kernel
theorem L1324_ok : RunOK pL1324 1324 (runFrom pL1324 (fmask pL1324) (cmask pL1324) (hmask pL1324) 936 388 (true, L1324_cp1.1, L1324_cp1.2)) ∧ ptTest pL1324 (runFrom pL1324 (fmask pL1324) (cmask pL1324) (hmask pL1324) 936 388 (true, L1324_cp1.1, L1324_cp1.2)) 1324 662 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1324_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1324_fin) true) L1324_seg1) (by decide) rfl L1324_fin ptTest_fst
noncomputable def H1324_cp1 : Nat × Nat := t7val% (fastRun pH1324 1 935 (init pH1324) (init pH1324))
theorem H1324_seg1 : segOK pH1324 1 935 (init pH1324) (init pH1324) H1324_cp1.1 H1324_cp1.2 = true := by
  decide +kernel
theorem H1324_fin : (prmOK pH1324 1324 && ptTest pH1324 (runFrom pH1324 (fmask pH1324) (cmask pH1324) (hmask pH1324) 936 388 (true, H1324_cp1.1, H1324_cp1.2)) 1324 662 true) = true := by
  decide +kernel
theorem H1324_ok : RunOK pH1324 1324 (runFrom pH1324 (fmask pH1324) (cmask pH1324) (hmask pH1324) 936 388 (true, H1324_cp1.1, H1324_cp1.2)) ∧ ptTest pH1324 (runFrom pH1324 (fmask pH1324) (cmask pH1324) (hmask pH1324) 936 388 (true, H1324_cp1.1, H1324_cp1.2)) 1324 662 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1324_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1324_fin) true) H1324_seg1) (by decide) rfl H1324_fin ptTest_fst
noncomputable def I1324_cp1 : Nat × Nat := t7val% (fastRun pI1324 1 935 (init pI1324) (init pI1324))
theorem I1324_seg1 : segOK pI1324 1 935 (init pI1324) (init pI1324) I1324_cp1.1 I1324_cp1.2 = true := by
  decide +kernel
theorem I1324_fin : (prmOK pI1324 1324 && intTest pI1324 (runFrom pI1324 (fmask pI1324) (cmask pI1324) (hmask pI1324) 936 388 (true, I1324_cp1.1, I1324_cp1.2)) 1324 19 true) = true := by
  decide +kernel
theorem I1324_ok : RunOK pI1324 1324 (runFrom pI1324 (fmask pI1324) (cmask pI1324) (hmask pI1324) 936 388 (true, I1324_cp1.1, I1324_cp1.2)) ∧ intTest pI1324 (runFrom pI1324 (fmask pI1324) (cmask pI1324) (hmask pI1324) 936 388 (true, I1324_cp1.1, I1324_cp1.2)) 1324 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1324_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1324_fin) true) I1324_seg1) (by decide) rfl I1324_fin intTest_fst
theorem link1324 : linkOK pL1324 pH1324 pI1324 = true := by decide +kernel
theorem cvx1324 : ConvexBetweenHumps 1324 :=
  cvx_of L1324_ok H1324_ok I1324_ok link1324 (by decide)
theorem cenlink1324 : cenLinkOK pI1324 1324 = true := by decide +kernel
theorem cen1324 : CenterUniqueMin 1324 ∧ DipHyp 1324 ∧ OnePointHyps 1324 :=
  cen_of L1324_ok H1324_ok I1324_ok link1324 cenlink1324

/-! ### `N = 1325` -/

def pL1325 : Prm := ⟨79, 37, 39, 1327, 11, 18446744073709551616, 137618541512216998, 137618541512216998⟩
def pH1325 : Prm := ⟨79, 37, 39, 1327, 11, 18446744073709551616, 137619641023844774, 137619641023844774⟩
def pI1325 : Prm := ⟨67, 32, 32, 1327, 11, 18446744073709551616, 137618541512216998, 137619641023844774⟩
noncomputable def L1325_cp1 : Nat × Nat := t7val% (fastRun pL1325 1 936 (init pL1325) (init pL1325))
theorem L1325_seg1 : segOK pL1325 1 936 (init pL1325) (init pL1325) L1325_cp1.1 L1325_cp1.2 = true := by
  decide +kernel
theorem L1325_fin : (prmOK pL1325 1325 && ptTest pL1325 (runFrom pL1325 (fmask pL1325) (cmask pL1325) (hmask pL1325) 937 388 (true, L1325_cp1.1, L1325_cp1.2)) 1325 663 false) = true := by
  decide +kernel
theorem L1325_ok : RunOK pL1325 1325 (runFrom pL1325 (fmask pL1325) (cmask pL1325) (hmask pL1325) 937 388 (true, L1325_cp1.1, L1325_cp1.2)) ∧ ptTest pL1325 (runFrom pL1325 (fmask pL1325) (cmask pL1325) (hmask pL1325) 937 388 (true, L1325_cp1.1, L1325_cp1.2)) 1325 663 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1325_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1325_fin) true) L1325_seg1) (by decide) rfl L1325_fin ptTest_fst
noncomputable def H1325_cp1 : Nat × Nat := t7val% (fastRun pH1325 1 936 (init pH1325) (init pH1325))
theorem H1325_seg1 : segOK pH1325 1 936 (init pH1325) (init pH1325) H1325_cp1.1 H1325_cp1.2 = true := by
  decide +kernel
theorem H1325_fin : (prmOK pH1325 1325 && ptTest pH1325 (runFrom pH1325 (fmask pH1325) (cmask pH1325) (hmask pH1325) 937 388 (true, H1325_cp1.1, H1325_cp1.2)) 1325 663 true) = true := by
  decide +kernel
theorem H1325_ok : RunOK pH1325 1325 (runFrom pH1325 (fmask pH1325) (cmask pH1325) (hmask pH1325) 937 388 (true, H1325_cp1.1, H1325_cp1.2)) ∧ ptTest pH1325 (runFrom pH1325 (fmask pH1325) (cmask pH1325) (hmask pH1325) 937 388 (true, H1325_cp1.1, H1325_cp1.2)) 1325 663 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1325_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1325_fin) true) H1325_seg1) (by decide) rfl H1325_fin ptTest_fst
noncomputable def I1325_cp1 : Nat × Nat := t7val% (fastRun pI1325 1 936 (init pI1325) (init pI1325))
theorem I1325_seg1 : segOK pI1325 1 936 (init pI1325) (init pI1325) I1325_cp1.1 I1325_cp1.2 = true := by
  decide +kernel
theorem I1325_fin : (prmOK pI1325 1325 && intTest pI1325 (runFrom pI1325 (fmask pI1325) (cmask pI1325) (hmask pI1325) 937 388 (true, I1325_cp1.1, I1325_cp1.2)) 1325 19 false) = true := by
  decide +kernel
theorem I1325_ok : RunOK pI1325 1325 (runFrom pI1325 (fmask pI1325) (cmask pI1325) (hmask pI1325) 937 388 (true, I1325_cp1.1, I1325_cp1.2)) ∧ intTest pI1325 (runFrom pI1325 (fmask pI1325) (cmask pI1325) (hmask pI1325) 937 388 (true, I1325_cp1.1, I1325_cp1.2)) 1325 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1325_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1325_fin) true) I1325_seg1) (by decide) rfl I1325_fin intTest_fst
theorem link1325 : linkOK pL1325 pH1325 pI1325 = true := by decide +kernel
theorem cvx1325 : ConvexBetweenHumps 1325 :=
  cvx_of L1325_ok H1325_ok I1325_ok link1325 (by decide)

/-! ### `N = 1326` -/

def pL1326 : Prm := ⟨79, 37, 39, 1328, 11, 18446744073709551616, 137534572591004366, 137534572591004366⟩
def pH1326 : Prm := ⟨79, 37, 39, 1328, 11, 18446744073709551616, 137535672102632142, 137535672102632142⟩
def pI1326 : Prm := ⟨67, 32, 32, 1328, 11, 18446744073709551616, 137534572591004366, 137535672102632142⟩
noncomputable def L1326_cp1 : Nat × Nat := t7val% (fastRun pL1326 1 937 (init pL1326) (init pL1326))
theorem L1326_seg1 : segOK pL1326 1 937 (init pL1326) (init pL1326) L1326_cp1.1 L1326_cp1.2 = true := by
  decide +kernel
theorem L1326_fin : (prmOK pL1326 1326 && ptTest pL1326 (runFrom pL1326 (fmask pL1326) (cmask pL1326) (hmask pL1326) 938 388 (true, L1326_cp1.1, L1326_cp1.2)) 1326 663 false) = true := by
  decide +kernel
theorem L1326_ok : RunOK pL1326 1326 (runFrom pL1326 (fmask pL1326) (cmask pL1326) (hmask pL1326) 938 388 (true, L1326_cp1.1, L1326_cp1.2)) ∧ ptTest pL1326 (runFrom pL1326 (fmask pL1326) (cmask pL1326) (hmask pL1326) 938 388 (true, L1326_cp1.1, L1326_cp1.2)) 1326 663 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1326_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1326_fin) true) L1326_seg1) (by decide) rfl L1326_fin ptTest_fst
noncomputable def H1326_cp1 : Nat × Nat := t7val% (fastRun pH1326 1 937 (init pH1326) (init pH1326))
theorem H1326_seg1 : segOK pH1326 1 937 (init pH1326) (init pH1326) H1326_cp1.1 H1326_cp1.2 = true := by
  decide +kernel
theorem H1326_fin : (prmOK pH1326 1326 && ptTest pH1326 (runFrom pH1326 (fmask pH1326) (cmask pH1326) (hmask pH1326) 938 388 (true, H1326_cp1.1, H1326_cp1.2)) 1326 663 true) = true := by
  decide +kernel
theorem H1326_ok : RunOK pH1326 1326 (runFrom pH1326 (fmask pH1326) (cmask pH1326) (hmask pH1326) 938 388 (true, H1326_cp1.1, H1326_cp1.2)) ∧ ptTest pH1326 (runFrom pH1326 (fmask pH1326) (cmask pH1326) (hmask pH1326) 938 388 (true, H1326_cp1.1, H1326_cp1.2)) 1326 663 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1326_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1326_fin) true) H1326_seg1) (by decide) rfl H1326_fin ptTest_fst
noncomputable def I1326_cp1 : Nat × Nat := t7val% (fastRun pI1326 1 937 (init pI1326) (init pI1326))
theorem I1326_seg1 : segOK pI1326 1 937 (init pI1326) (init pI1326) I1326_cp1.1 I1326_cp1.2 = true := by
  decide +kernel
theorem I1326_fin : (prmOK pI1326 1326 && intTest pI1326 (runFrom pI1326 (fmask pI1326) (cmask pI1326) (hmask pI1326) 938 388 (true, I1326_cp1.1, I1326_cp1.2)) 1326 19 true) = true := by
  decide +kernel
theorem I1326_ok : RunOK pI1326 1326 (runFrom pI1326 (fmask pI1326) (cmask pI1326) (hmask pI1326) 938 388 (true, I1326_cp1.1, I1326_cp1.2)) ∧ intTest pI1326 (runFrom pI1326 (fmask pI1326) (cmask pI1326) (hmask pI1326) 938 388 (true, I1326_cp1.1, I1326_cp1.2)) 1326 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1326_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1326_fin) true) I1326_seg1) (by decide) rfl I1326_fin intTest_fst
theorem link1326 : linkOK pL1326 pH1326 pI1326 = true := by decide +kernel
theorem cvx1326 : ConvexBetweenHumps 1326 :=
  cvx_of L1326_ok H1326_ok I1326_ok link1326 (by decide)
theorem cenlink1326 : cenLinkOK pI1326 1326 = true := by decide +kernel
theorem cen1326 : CenterUniqueMin 1326 ∧ DipHyp 1326 ∧ OnePointHyps 1326 :=
  cen_of L1326_ok H1326_ok I1326_ok link1326 cenlink1326

/-! ### `N = 1327` -/

def pL1327 : Prm := ⟨79, 37, 39, 1329, 11, 18446744073709551616, 137450666488813617, 137450666488813617⟩
def pH1327 : Prm := ⟨79, 37, 39, 1329, 11, 18446744073709551616, 137451766000441393, 137451766000441393⟩
def pI1327 : Prm := ⟨67, 32, 32, 1329, 11, 18446744073709551616, 137450666488813617, 137451766000441393⟩
noncomputable def L1327_cp1 : Nat × Nat := t7val% (fastRun pL1327 1 937 (init pL1327) (init pL1327))
theorem L1327_seg1 : segOK pL1327 1 937 (init pL1327) (init pL1327) L1327_cp1.1 L1327_cp1.2 = true := by
  decide +kernel
theorem L1327_fin : (prmOK pL1327 1327 && ptTest pL1327 (runFrom pL1327 (fmask pL1327) (cmask pL1327) (hmask pL1327) 938 389 (true, L1327_cp1.1, L1327_cp1.2)) 1327 664 false) = true := by
  decide +kernel
theorem L1327_ok : RunOK pL1327 1327 (runFrom pL1327 (fmask pL1327) (cmask pL1327) (hmask pL1327) 938 389 (true, L1327_cp1.1, L1327_cp1.2)) ∧ ptTest pL1327 (runFrom pL1327 (fmask pL1327) (cmask pL1327) (hmask pL1327) 938 389 (true, L1327_cp1.1, L1327_cp1.2)) 1327 664 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1327_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1327_fin) true) L1327_seg1) (by decide) rfl L1327_fin ptTest_fst
noncomputable def H1327_cp1 : Nat × Nat := t7val% (fastRun pH1327 1 937 (init pH1327) (init pH1327))
theorem H1327_seg1 : segOK pH1327 1 937 (init pH1327) (init pH1327) H1327_cp1.1 H1327_cp1.2 = true := by
  decide +kernel
theorem H1327_fin : (prmOK pH1327 1327 && ptTest pH1327 (runFrom pH1327 (fmask pH1327) (cmask pH1327) (hmask pH1327) 938 389 (true, H1327_cp1.1, H1327_cp1.2)) 1327 664 true) = true := by
  decide +kernel
theorem H1327_ok : RunOK pH1327 1327 (runFrom pH1327 (fmask pH1327) (cmask pH1327) (hmask pH1327) 938 389 (true, H1327_cp1.1, H1327_cp1.2)) ∧ ptTest pH1327 (runFrom pH1327 (fmask pH1327) (cmask pH1327) (hmask pH1327) 938 389 (true, H1327_cp1.1, H1327_cp1.2)) 1327 664 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1327_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1327_fin) true) H1327_seg1) (by decide) rfl H1327_fin ptTest_fst
noncomputable def I1327_cp1 : Nat × Nat := t7val% (fastRun pI1327 1 937 (init pI1327) (init pI1327))
theorem I1327_seg1 : segOK pI1327 1 937 (init pI1327) (init pI1327) I1327_cp1.1 I1327_cp1.2 = true := by
  decide +kernel
theorem I1327_fin : (prmOK pI1327 1327 && intTest pI1327 (runFrom pI1327 (fmask pI1327) (cmask pI1327) (hmask pI1327) 938 389 (true, I1327_cp1.1, I1327_cp1.2)) 1327 19 false) = true := by
  decide +kernel
theorem I1327_ok : RunOK pI1327 1327 (runFrom pI1327 (fmask pI1327) (cmask pI1327) (hmask pI1327) 938 389 (true, I1327_cp1.1, I1327_cp1.2)) ∧ intTest pI1327 (runFrom pI1327 (fmask pI1327) (cmask pI1327) (hmask pI1327) 938 389 (true, I1327_cp1.1, I1327_cp1.2)) 1327 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1327_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1327_fin) true) I1327_seg1) (by decide) rfl I1327_fin intTest_fst
theorem link1327 : linkOK pL1327 pH1327 pI1327 = true := by decide +kernel
theorem cvx1327 : ConvexBetweenHumps 1327 :=
  cvx_of L1327_ok H1327_ok I1327_ok link1327 (by decide)

/-! ### `N = 1328` -/

def pL1328 : Prm := ⟨79, 37, 39, 1330, 11, 18446744073709551616, 137366920564497815, 137366920564497815⟩
def pH1328 : Prm := ⟨79, 37, 39, 1330, 11, 18446744073709551616, 137368020076125591, 137368020076125591⟩
def pI1328 : Prm := ⟨67, 32, 32, 1330, 11, 18446744073709551616, 137366920564497815, 137368020076125591⟩
noncomputable def L1328_cp1 : Nat × Nat := t7val% (fastRun pL1328 1 938 (init pL1328) (init pL1328))
theorem L1328_seg1 : segOK pL1328 1 938 (init pL1328) (init pL1328) L1328_cp1.1 L1328_cp1.2 = true := by
  decide +kernel
theorem L1328_fin : (prmOK pL1328 1328 && ptTest pL1328 (runFrom pL1328 (fmask pL1328) (cmask pL1328) (hmask pL1328) 939 389 (true, L1328_cp1.1, L1328_cp1.2)) 1328 664 false) = true := by
  decide +kernel
theorem L1328_ok : RunOK pL1328 1328 (runFrom pL1328 (fmask pL1328) (cmask pL1328) (hmask pL1328) 939 389 (true, L1328_cp1.1, L1328_cp1.2)) ∧ ptTest pL1328 (runFrom pL1328 (fmask pL1328) (cmask pL1328) (hmask pL1328) 939 389 (true, L1328_cp1.1, L1328_cp1.2)) 1328 664 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1328_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1328_fin) true) L1328_seg1) (by decide) rfl L1328_fin ptTest_fst
noncomputable def H1328_cp1 : Nat × Nat := t7val% (fastRun pH1328 1 938 (init pH1328) (init pH1328))
theorem H1328_seg1 : segOK pH1328 1 938 (init pH1328) (init pH1328) H1328_cp1.1 H1328_cp1.2 = true := by
  decide +kernel
theorem H1328_fin : (prmOK pH1328 1328 && ptTest pH1328 (runFrom pH1328 (fmask pH1328) (cmask pH1328) (hmask pH1328) 939 389 (true, H1328_cp1.1, H1328_cp1.2)) 1328 664 true) = true := by
  decide +kernel
theorem H1328_ok : RunOK pH1328 1328 (runFrom pH1328 (fmask pH1328) (cmask pH1328) (hmask pH1328) 939 389 (true, H1328_cp1.1, H1328_cp1.2)) ∧ ptTest pH1328 (runFrom pH1328 (fmask pH1328) (cmask pH1328) (hmask pH1328) 939 389 (true, H1328_cp1.1, H1328_cp1.2)) 1328 664 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1328_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1328_fin) true) H1328_seg1) (by decide) rfl H1328_fin ptTest_fst
noncomputable def I1328_cp1 : Nat × Nat := t7val% (fastRun pI1328 1 938 (init pI1328) (init pI1328))
theorem I1328_seg1 : segOK pI1328 1 938 (init pI1328) (init pI1328) I1328_cp1.1 I1328_cp1.2 = true := by
  decide +kernel
theorem I1328_fin : (prmOK pI1328 1328 && intTest pI1328 (runFrom pI1328 (fmask pI1328) (cmask pI1328) (hmask pI1328) 939 389 (true, I1328_cp1.1, I1328_cp1.2)) 1328 19 true) = true := by
  decide +kernel
theorem I1328_ok : RunOK pI1328 1328 (runFrom pI1328 (fmask pI1328) (cmask pI1328) (hmask pI1328) 939 389 (true, I1328_cp1.1, I1328_cp1.2)) ∧ intTest pI1328 (runFrom pI1328 (fmask pI1328) (cmask pI1328) (hmask pI1328) 939 389 (true, I1328_cp1.1, I1328_cp1.2)) 1328 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1328_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1328_fin) true) I1328_seg1) (by decide) rfl I1328_fin intTest_fst
theorem link1328 : linkOK pL1328 pH1328 pI1328 = true := by decide +kernel
theorem cvx1328 : ConvexBetweenHumps 1328 :=
  cvx_of L1328_ok H1328_ok I1328_ok link1328 (by decide)
theorem cenlink1328 : cenLinkOK pI1328 1328 = true := by decide +kernel
theorem cen1328 : CenterUniqueMin 1328 ∧ DipHyp 1328 ∧ OnePointHyps 1328 :=
  cen_of L1328_ok H1328_ok I1328_ok link1328 cenlink1328

/-! ### `N = 1329` -/

def pL1329 : Prm := ⟨79, 37, 39, 1331, 11, 18446744073709551616, 137283237224284610, 137283237224284610⟩
def pH1329 : Prm := ⟨79, 37, 39, 1331, 11, 18446744073709551616, 137284336735912386, 137284336735912386⟩
def pI1329 : Prm := ⟨67, 32, 32, 1331, 11, 18446744073709551616, 137283237224284610, 137284336735912386⟩
noncomputable def L1329_cp1 : Nat × Nat := t7val% (fastRun pL1329 1 939 (init pL1329) (init pL1329))
theorem L1329_seg1 : segOK pL1329 1 939 (init pL1329) (init pL1329) L1329_cp1.1 L1329_cp1.2 = true := by
  decide +kernel
theorem L1329_fin : (prmOK pL1329 1329 && ptTest pL1329 (runFrom pL1329 (fmask pL1329) (cmask pL1329) (hmask pL1329) 940 389 (true, L1329_cp1.1, L1329_cp1.2)) 1329 665 false) = true := by
  decide +kernel
theorem L1329_ok : RunOK pL1329 1329 (runFrom pL1329 (fmask pL1329) (cmask pL1329) (hmask pL1329) 940 389 (true, L1329_cp1.1, L1329_cp1.2)) ∧ ptTest pL1329 (runFrom pL1329 (fmask pL1329) (cmask pL1329) (hmask pL1329) 940 389 (true, L1329_cp1.1, L1329_cp1.2)) 1329 665 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1329_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1329_fin) true) L1329_seg1) (by decide) rfl L1329_fin ptTest_fst
noncomputable def H1329_cp1 : Nat × Nat := t7val% (fastRun pH1329 1 939 (init pH1329) (init pH1329))
theorem H1329_seg1 : segOK pH1329 1 939 (init pH1329) (init pH1329) H1329_cp1.1 H1329_cp1.2 = true := by
  decide +kernel
theorem H1329_fin : (prmOK pH1329 1329 && ptTest pH1329 (runFrom pH1329 (fmask pH1329) (cmask pH1329) (hmask pH1329) 940 389 (true, H1329_cp1.1, H1329_cp1.2)) 1329 665 true) = true := by
  decide +kernel
theorem H1329_ok : RunOK pH1329 1329 (runFrom pH1329 (fmask pH1329) (cmask pH1329) (hmask pH1329) 940 389 (true, H1329_cp1.1, H1329_cp1.2)) ∧ ptTest pH1329 (runFrom pH1329 (fmask pH1329) (cmask pH1329) (hmask pH1329) 940 389 (true, H1329_cp1.1, H1329_cp1.2)) 1329 665 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1329_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1329_fin) true) H1329_seg1) (by decide) rfl H1329_fin ptTest_fst
noncomputable def I1329_cp1 : Nat × Nat := t7val% (fastRun pI1329 1 939 (init pI1329) (init pI1329))
theorem I1329_seg1 : segOK pI1329 1 939 (init pI1329) (init pI1329) I1329_cp1.1 I1329_cp1.2 = true := by
  decide +kernel
theorem I1329_fin : (prmOK pI1329 1329 && intTest pI1329 (runFrom pI1329 (fmask pI1329) (cmask pI1329) (hmask pI1329) 940 389 (true, I1329_cp1.1, I1329_cp1.2)) 1329 19 false) = true := by
  decide +kernel
theorem I1329_ok : RunOK pI1329 1329 (runFrom pI1329 (fmask pI1329) (cmask pI1329) (hmask pI1329) 940 389 (true, I1329_cp1.1, I1329_cp1.2)) ∧ intTest pI1329 (runFrom pI1329 (fmask pI1329) (cmask pI1329) (hmask pI1329) 940 389 (true, I1329_cp1.1, I1329_cp1.2)) 1329 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1329_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1329_fin) true) I1329_seg1) (by decide) rfl I1329_fin intTest_fst
theorem link1329 : linkOK pL1329 pH1329 pI1329 = true := by decide +kernel
theorem cvx1329 : ConvexBetweenHumps 1329 :=
  cvx_of L1329_ok H1329_ok I1329_ok link1329 (by decide)

/-! ### `N = 1330` -/

def pL1330 : Prm := ⟨79, 37, 39, 1332, 11, 18446744073709551616, 137199713380818773, 137199713380818773⟩
def pH1330 : Prm := ⟨79, 37, 39, 1332, 11, 18446744073709551616, 137200812892446549, 137200812892446549⟩
def pI1330 : Prm := ⟨67, 32, 32, 1332, 11, 18446744073709551616, 137199713380818773, 137200812892446549⟩
noncomputable def L1330_cp1 : Nat × Nat := t7val% (fastRun pL1330 1 939 (init pL1330) (init pL1330))
theorem L1330_seg1 : segOK pL1330 1 939 (init pL1330) (init pL1330) L1330_cp1.1 L1330_cp1.2 = true := by
  decide +kernel
theorem L1330_fin : (prmOK pL1330 1330 && ptTest pL1330 (runFrom pL1330 (fmask pL1330) (cmask pL1330) (hmask pL1330) 940 390 (true, L1330_cp1.1, L1330_cp1.2)) 1330 665 false) = true := by
  decide +kernel
theorem L1330_ok : RunOK pL1330 1330 (runFrom pL1330 (fmask pL1330) (cmask pL1330) (hmask pL1330) 940 390 (true, L1330_cp1.1, L1330_cp1.2)) ∧ ptTest pL1330 (runFrom pL1330 (fmask pL1330) (cmask pL1330) (hmask pL1330) 940 390 (true, L1330_cp1.1, L1330_cp1.2)) 1330 665 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1330_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1330_fin) true) L1330_seg1) (by decide) rfl L1330_fin ptTest_fst
noncomputable def H1330_cp1 : Nat × Nat := t7val% (fastRun pH1330 1 939 (init pH1330) (init pH1330))
theorem H1330_seg1 : segOK pH1330 1 939 (init pH1330) (init pH1330) H1330_cp1.1 H1330_cp1.2 = true := by
  decide +kernel
theorem H1330_fin : (prmOK pH1330 1330 && ptTest pH1330 (runFrom pH1330 (fmask pH1330) (cmask pH1330) (hmask pH1330) 940 390 (true, H1330_cp1.1, H1330_cp1.2)) 1330 665 true) = true := by
  decide +kernel
theorem H1330_ok : RunOK pH1330 1330 (runFrom pH1330 (fmask pH1330) (cmask pH1330) (hmask pH1330) 940 390 (true, H1330_cp1.1, H1330_cp1.2)) ∧ ptTest pH1330 (runFrom pH1330 (fmask pH1330) (cmask pH1330) (hmask pH1330) 940 390 (true, H1330_cp1.1, H1330_cp1.2)) 1330 665 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1330_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1330_fin) true) H1330_seg1) (by decide) rfl H1330_fin ptTest_fst
noncomputable def I1330_cp1 : Nat × Nat := t7val% (fastRun pI1330 1 939 (init pI1330) (init pI1330))
theorem I1330_seg1 : segOK pI1330 1 939 (init pI1330) (init pI1330) I1330_cp1.1 I1330_cp1.2 = true := by
  decide +kernel
theorem I1330_fin : (prmOK pI1330 1330 && intTest pI1330 (runFrom pI1330 (fmask pI1330) (cmask pI1330) (hmask pI1330) 940 390 (true, I1330_cp1.1, I1330_cp1.2)) 1330 19 true) = true := by
  decide +kernel
theorem I1330_ok : RunOK pI1330 1330 (runFrom pI1330 (fmask pI1330) (cmask pI1330) (hmask pI1330) 940 390 (true, I1330_cp1.1, I1330_cp1.2)) ∧ intTest pI1330 (runFrom pI1330 (fmask pI1330) (cmask pI1330) (hmask pI1330) 940 390 (true, I1330_cp1.1, I1330_cp1.2)) 1330 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1330_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1330_fin) true) I1330_seg1) (by decide) rfl I1330_fin intTest_fst
theorem link1330 : linkOK pL1330 pH1330 pI1330 = true := by decide +kernel
theorem cvx1330 : ConvexBetweenHumps 1330 :=
  cvx_of L1330_ok H1330_ok I1330_ok link1330 (by decide)
theorem cenlink1330 : cenLinkOK pI1330 1330 = true := by decide +kernel
theorem cen1330 : CenterUniqueMin 1330 ∧ DipHyp 1330 ∧ OnePointHyps 1330 :=
  cen_of L1330_ok H1330_ok I1330_ok link1330 cenlink1330

/-! ### `N = 1331` -/

def pL1331 : Prm := ⟨79, 37, 39, 1333, 11, 18446744073709551616, 137116251887735286, 137116251887735286⟩
def pH1331 : Prm := ⟨79, 37, 39, 1333, 11, 18446744073709551616, 137117351399363062, 137117351399363062⟩
def pI1331 : Prm := ⟨67, 32, 32, 1333, 11, 18446744073709551616, 137116251887735286, 137117351399363062⟩
noncomputable def L1331_cp1 : Nat × Nat := t7val% (fastRun pL1331 1 940 (init pL1331) (init pL1331))
theorem L1331_seg1 : segOK pL1331 1 940 (init pL1331) (init pL1331) L1331_cp1.1 L1331_cp1.2 = true := by
  decide +kernel
theorem L1331_fin : (prmOK pL1331 1331 && ptTest pL1331 (runFrom pL1331 (fmask pL1331) (cmask pL1331) (hmask pL1331) 941 390 (true, L1331_cp1.1, L1331_cp1.2)) 1331 666 false) = true := by
  decide +kernel
theorem L1331_ok : RunOK pL1331 1331 (runFrom pL1331 (fmask pL1331) (cmask pL1331) (hmask pL1331) 941 390 (true, L1331_cp1.1, L1331_cp1.2)) ∧ ptTest pL1331 (runFrom pL1331 (fmask pL1331) (cmask pL1331) (hmask pL1331) 941 390 (true, L1331_cp1.1, L1331_cp1.2)) 1331 666 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1331_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1331_fin) true) L1331_seg1) (by decide) rfl L1331_fin ptTest_fst
noncomputable def H1331_cp1 : Nat × Nat := t7val% (fastRun pH1331 1 940 (init pH1331) (init pH1331))
theorem H1331_seg1 : segOK pH1331 1 940 (init pH1331) (init pH1331) H1331_cp1.1 H1331_cp1.2 = true := by
  decide +kernel
theorem H1331_fin : (prmOK pH1331 1331 && ptTest pH1331 (runFrom pH1331 (fmask pH1331) (cmask pH1331) (hmask pH1331) 941 390 (true, H1331_cp1.1, H1331_cp1.2)) 1331 666 true) = true := by
  decide +kernel
theorem H1331_ok : RunOK pH1331 1331 (runFrom pH1331 (fmask pH1331) (cmask pH1331) (hmask pH1331) 941 390 (true, H1331_cp1.1, H1331_cp1.2)) ∧ ptTest pH1331 (runFrom pH1331 (fmask pH1331) (cmask pH1331) (hmask pH1331) 941 390 (true, H1331_cp1.1, H1331_cp1.2)) 1331 666 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1331_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1331_fin) true) H1331_seg1) (by decide) rfl H1331_fin ptTest_fst
noncomputable def I1331_cp1 : Nat × Nat := t7val% (fastRun pI1331 1 940 (init pI1331) (init pI1331))
theorem I1331_seg1 : segOK pI1331 1 940 (init pI1331) (init pI1331) I1331_cp1.1 I1331_cp1.2 = true := by
  decide +kernel
theorem I1331_fin : (prmOK pI1331 1331 && intTest pI1331 (runFrom pI1331 (fmask pI1331) (cmask pI1331) (hmask pI1331) 941 390 (true, I1331_cp1.1, I1331_cp1.2)) 1331 19 false) = true := by
  decide +kernel
theorem I1331_ok : RunOK pI1331 1331 (runFrom pI1331 (fmask pI1331) (cmask pI1331) (hmask pI1331) 941 390 (true, I1331_cp1.1, I1331_cp1.2)) ∧ intTest pI1331 (runFrom pI1331 (fmask pI1331) (cmask pI1331) (hmask pI1331) 941 390 (true, I1331_cp1.1, I1331_cp1.2)) 1331 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1331_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1331_fin) true) I1331_seg1) (by decide) rfl I1331_fin intTest_fst
theorem link1331 : linkOK pL1331 pH1331 pI1331 = true := by decide +kernel
theorem cvx1331 : ConvexBetweenHumps 1331 :=
  cvx_of L1331_ok H1331_ok I1331_ok link1331 (by decide)

/-! ### `N = 1332` -/

def pL1332 : Prm := ⟨79, 37, 39, 1334, 11, 18446744073709551616, 137032949214182298, 137032949214182298⟩
def pH1332 : Prm := ⟨79, 37, 39, 1334, 11, 18446744073709551616, 137034048725810074, 137034048725810074⟩
def pI1332 : Prm := ⟨67, 32, 32, 1334, 11, 18446744073709551616, 137032949214182298, 137034048725810074⟩
noncomputable def L1332_cp1 : Nat × Nat := t7val% (fastRun pL1332 1 941 (init pL1332) (init pL1332))
theorem L1332_seg1 : segOK pL1332 1 941 (init pL1332) (init pL1332) L1332_cp1.1 L1332_cp1.2 = true := by
  decide +kernel
theorem L1332_fin : (prmOK pL1332 1332 && ptTest pL1332 (runFrom pL1332 (fmask pL1332) (cmask pL1332) (hmask pL1332) 942 390 (true, L1332_cp1.1, L1332_cp1.2)) 1332 666 false) = true := by
  decide +kernel
theorem L1332_ok : RunOK pL1332 1332 (runFrom pL1332 (fmask pL1332) (cmask pL1332) (hmask pL1332) 942 390 (true, L1332_cp1.1, L1332_cp1.2)) ∧ ptTest pL1332 (runFrom pL1332 (fmask pL1332) (cmask pL1332) (hmask pL1332) 942 390 (true, L1332_cp1.1, L1332_cp1.2)) 1332 666 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1332_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1332_fin) true) L1332_seg1) (by decide) rfl L1332_fin ptTest_fst
noncomputable def H1332_cp1 : Nat × Nat := t7val% (fastRun pH1332 1 941 (init pH1332) (init pH1332))
theorem H1332_seg1 : segOK pH1332 1 941 (init pH1332) (init pH1332) H1332_cp1.1 H1332_cp1.2 = true := by
  decide +kernel
theorem H1332_fin : (prmOK pH1332 1332 && ptTest pH1332 (runFrom pH1332 (fmask pH1332) (cmask pH1332) (hmask pH1332) 942 390 (true, H1332_cp1.1, H1332_cp1.2)) 1332 666 true) = true := by
  decide +kernel
theorem H1332_ok : RunOK pH1332 1332 (runFrom pH1332 (fmask pH1332) (cmask pH1332) (hmask pH1332) 942 390 (true, H1332_cp1.1, H1332_cp1.2)) ∧ ptTest pH1332 (runFrom pH1332 (fmask pH1332) (cmask pH1332) (hmask pH1332) 942 390 (true, H1332_cp1.1, H1332_cp1.2)) 1332 666 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1332_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1332_fin) true) H1332_seg1) (by decide) rfl H1332_fin ptTest_fst
noncomputable def I1332_cp1 : Nat × Nat := t7val% (fastRun pI1332 1 941 (init pI1332) (init pI1332))
theorem I1332_seg1 : segOK pI1332 1 941 (init pI1332) (init pI1332) I1332_cp1.1 I1332_cp1.2 = true := by
  decide +kernel
theorem I1332_fin : (prmOK pI1332 1332 && intTest pI1332 (runFrom pI1332 (fmask pI1332) (cmask pI1332) (hmask pI1332) 942 390 (true, I1332_cp1.1, I1332_cp1.2)) 1332 19 true) = true := by
  decide +kernel
theorem I1332_ok : RunOK pI1332 1332 (runFrom pI1332 (fmask pI1332) (cmask pI1332) (hmask pI1332) 942 390 (true, I1332_cp1.1, I1332_cp1.2)) ∧ intTest pI1332 (runFrom pI1332 (fmask pI1332) (cmask pI1332) (hmask pI1332) 942 390 (true, I1332_cp1.1, I1332_cp1.2)) 1332 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1332_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1332_fin) true) I1332_seg1) (by decide) rfl I1332_fin intTest_fst
theorem link1332 : linkOK pL1332 pH1332 pI1332 = true := by decide +kernel
theorem cvx1332 : ConvexBetweenHumps 1332 :=
  cvx_of L1332_ok H1332_ok I1332_ok link1332 (by decide)
theorem cenlink1332 : cenLinkOK pI1332 1332 = true := by decide +kernel
theorem cen1332 : CenterUniqueMin 1332 ∧ DipHyp 1332 ∧ OnePointHyps 1332 :=
  cen_of L1332_ok H1332_ok I1332_ok link1332 cenlink1332

/-! ### `N = 1333` -/

def pL1333 : Prm := ⟨79, 37, 39, 1335, 11, 18446744073709551616, 136949708658453559, 136949708658453559⟩
def pH1333 : Prm := ⟨79, 37, 39, 1335, 11, 18446744073709551616, 136950808170081335, 136950808170081335⟩
def pI1333 : Prm := ⟨67, 32, 32, 1335, 11, 18446744073709551616, 136949708658453559, 136950808170081335⟩
noncomputable def L1333_cp1 : Nat × Nat := t7val% (fastRun pL1333 1 942 (init pL1333) (init pL1333))
theorem L1333_seg1 : segOK pL1333 1 942 (init pL1333) (init pL1333) L1333_cp1.1 L1333_cp1.2 = true := by
  decide +kernel
theorem L1333_fin : (prmOK pL1333 1333 && ptTest pL1333 (runFrom pL1333 (fmask pL1333) (cmask pL1333) (hmask pL1333) 943 390 (true, L1333_cp1.1, L1333_cp1.2)) 1333 667 false) = true := by
  decide +kernel
theorem L1333_ok : RunOK pL1333 1333 (runFrom pL1333 (fmask pL1333) (cmask pL1333) (hmask pL1333) 943 390 (true, L1333_cp1.1, L1333_cp1.2)) ∧ ptTest pL1333 (runFrom pL1333 (fmask pL1333) (cmask pL1333) (hmask pL1333) 943 390 (true, L1333_cp1.1, L1333_cp1.2)) 1333 667 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1333_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1333_fin) true) L1333_seg1) (by decide) rfl L1333_fin ptTest_fst
noncomputable def H1333_cp1 : Nat × Nat := t7val% (fastRun pH1333 1 942 (init pH1333) (init pH1333))
theorem H1333_seg1 : segOK pH1333 1 942 (init pH1333) (init pH1333) H1333_cp1.1 H1333_cp1.2 = true := by
  decide +kernel
theorem H1333_fin : (prmOK pH1333 1333 && ptTest pH1333 (runFrom pH1333 (fmask pH1333) (cmask pH1333) (hmask pH1333) 943 390 (true, H1333_cp1.1, H1333_cp1.2)) 1333 667 true) = true := by
  decide +kernel
theorem H1333_ok : RunOK pH1333 1333 (runFrom pH1333 (fmask pH1333) (cmask pH1333) (hmask pH1333) 943 390 (true, H1333_cp1.1, H1333_cp1.2)) ∧ ptTest pH1333 (runFrom pH1333 (fmask pH1333) (cmask pH1333) (hmask pH1333) 943 390 (true, H1333_cp1.1, H1333_cp1.2)) 1333 667 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1333_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1333_fin) true) H1333_seg1) (by decide) rfl H1333_fin ptTest_fst
noncomputable def I1333_cp1 : Nat × Nat := t7val% (fastRun pI1333 1 942 (init pI1333) (init pI1333))
theorem I1333_seg1 : segOK pI1333 1 942 (init pI1333) (init pI1333) I1333_cp1.1 I1333_cp1.2 = true := by
  decide +kernel
theorem I1333_fin : (prmOK pI1333 1333 && intTest pI1333 (runFrom pI1333 (fmask pI1333) (cmask pI1333) (hmask pI1333) 943 390 (true, I1333_cp1.1, I1333_cp1.2)) 1333 19 false) = true := by
  decide +kernel
theorem I1333_ok : RunOK pI1333 1333 (runFrom pI1333 (fmask pI1333) (cmask pI1333) (hmask pI1333) 943 390 (true, I1333_cp1.1, I1333_cp1.2)) ∧ intTest pI1333 (runFrom pI1333 (fmask pI1333) (cmask pI1333) (hmask pI1333) 943 390 (true, I1333_cp1.1, I1333_cp1.2)) 1333 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1333_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1333_fin) true) I1333_seg1) (by decide) rfl I1333_fin intTest_fst
theorem link1333 : linkOK pL1333 pH1333 pI1333 = true := by decide +kernel
theorem cvx1333 : ConvexBetweenHumps 1333 :=
  cvx_of L1333_ok H1333_ok I1333_ok link1333 (by decide)

/-! ### `N = 1334` -/

def pL1334 : Prm := ⟨79, 37, 39, 1336, 11, 18446744073709551616, 136866626248912266, 136866626248912266⟩
def pH1334 : Prm := ⟨79, 37, 39, 1336, 11, 18446744073709551616, 136867725760540042, 136867725760540042⟩
def pI1334 : Prm := ⟨67, 32, 32, 1336, 11, 18446744073709551616, 136866626248912266, 136867725760540042⟩
noncomputable def L1334_cp1 : Nat × Nat := t7val% (fastRun pL1334 1 942 (init pL1334) (init pL1334))
theorem L1334_seg1 : segOK pL1334 1 942 (init pL1334) (init pL1334) L1334_cp1.1 L1334_cp1.2 = true := by
  decide +kernel
theorem L1334_fin : (prmOK pL1334 1334 && ptTest pL1334 (runFrom pL1334 (fmask pL1334) (cmask pL1334) (hmask pL1334) 943 391 (true, L1334_cp1.1, L1334_cp1.2)) 1334 667 false) = true := by
  decide +kernel
theorem L1334_ok : RunOK pL1334 1334 (runFrom pL1334 (fmask pL1334) (cmask pL1334) (hmask pL1334) 943 391 (true, L1334_cp1.1, L1334_cp1.2)) ∧ ptTest pL1334 (runFrom pL1334 (fmask pL1334) (cmask pL1334) (hmask pL1334) 943 391 (true, L1334_cp1.1, L1334_cp1.2)) 1334 667 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1334_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1334_fin) true) L1334_seg1) (by decide) rfl L1334_fin ptTest_fst
noncomputable def H1334_cp1 : Nat × Nat := t7val% (fastRun pH1334 1 942 (init pH1334) (init pH1334))
theorem H1334_seg1 : segOK pH1334 1 942 (init pH1334) (init pH1334) H1334_cp1.1 H1334_cp1.2 = true := by
  decide +kernel
theorem H1334_fin : (prmOK pH1334 1334 && ptTest pH1334 (runFrom pH1334 (fmask pH1334) (cmask pH1334) (hmask pH1334) 943 391 (true, H1334_cp1.1, H1334_cp1.2)) 1334 667 true) = true := by
  decide +kernel
theorem H1334_ok : RunOK pH1334 1334 (runFrom pH1334 (fmask pH1334) (cmask pH1334) (hmask pH1334) 943 391 (true, H1334_cp1.1, H1334_cp1.2)) ∧ ptTest pH1334 (runFrom pH1334 (fmask pH1334) (cmask pH1334) (hmask pH1334) 943 391 (true, H1334_cp1.1, H1334_cp1.2)) 1334 667 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1334_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1334_fin) true) H1334_seg1) (by decide) rfl H1334_fin ptTest_fst
noncomputable def I1334_cp1 : Nat × Nat := t7val% (fastRun pI1334 1 942 (init pI1334) (init pI1334))
theorem I1334_seg1 : segOK pI1334 1 942 (init pI1334) (init pI1334) I1334_cp1.1 I1334_cp1.2 = true := by
  decide +kernel
theorem I1334_fin : (prmOK pI1334 1334 && intTest pI1334 (runFrom pI1334 (fmask pI1334) (cmask pI1334) (hmask pI1334) 943 391 (true, I1334_cp1.1, I1334_cp1.2)) 1334 19 true) = true := by
  decide +kernel
theorem I1334_ok : RunOK pI1334 1334 (runFrom pI1334 (fmask pI1334) (cmask pI1334) (hmask pI1334) 943 391 (true, I1334_cp1.1, I1334_cp1.2)) ∧ intTest pI1334 (runFrom pI1334 (fmask pI1334) (cmask pI1334) (hmask pI1334) 943 391 (true, I1334_cp1.1, I1334_cp1.2)) 1334 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1334_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1334_fin) true) I1334_seg1) (by decide) rfl I1334_fin intTest_fst
theorem link1334 : linkOK pL1334 pH1334 pI1334 = true := by decide +kernel
theorem cvx1334 : ConvexBetweenHumps 1334 :=
  cvx_of L1334_ok H1334_ok I1334_ok link1334 (by decide)
theorem cenlink1334 : cenLinkOK pI1334 1334 = true := by decide +kernel
theorem cen1334 : CenterUniqueMin 1334 ∧ DipHyp 1334 ∧ OnePointHyps 1334 :=
  cen_of L1334_ok H1334_ok I1334_ok link1334 cenlink1334

/-! ### `N = 1335` -/

def pL1335 : Prm := ⟨79, 37, 39, 1337, 11, 18446744073709551616, 136783605725817711, 136783605725817711⟩
def pH1335 : Prm := ⟨79, 37, 39, 1337, 11, 18446744073709551616, 136784705237445487, 136784705237445487⟩
def pI1335 : Prm := ⟨67, 32, 32, 1337, 11, 18446744073709551616, 136783605725817711, 136784705237445487⟩
noncomputable def L1335_cp1 : Nat × Nat := t7val% (fastRun pL1335 1 943 (init pL1335) (init pL1335))
theorem L1335_seg1 : segOK pL1335 1 943 (init pL1335) (init pL1335) L1335_cp1.1 L1335_cp1.2 = true := by
  decide +kernel
theorem L1335_fin : (prmOK pL1335 1335 && ptTest pL1335 (runFrom pL1335 (fmask pL1335) (cmask pL1335) (hmask pL1335) 944 391 (true, L1335_cp1.1, L1335_cp1.2)) 1335 668 false) = true := by
  decide +kernel
theorem L1335_ok : RunOK pL1335 1335 (runFrom pL1335 (fmask pL1335) (cmask pL1335) (hmask pL1335) 944 391 (true, L1335_cp1.1, L1335_cp1.2)) ∧ ptTest pL1335 (runFrom pL1335 (fmask pL1335) (cmask pL1335) (hmask pL1335) 944 391 (true, L1335_cp1.1, L1335_cp1.2)) 1335 668 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1335_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1335_fin) true) L1335_seg1) (by decide) rfl L1335_fin ptTest_fst
noncomputable def H1335_cp1 : Nat × Nat := t7val% (fastRun pH1335 1 943 (init pH1335) (init pH1335))
theorem H1335_seg1 : segOK pH1335 1 943 (init pH1335) (init pH1335) H1335_cp1.1 H1335_cp1.2 = true := by
  decide +kernel
theorem H1335_fin : (prmOK pH1335 1335 && ptTest pH1335 (runFrom pH1335 (fmask pH1335) (cmask pH1335) (hmask pH1335) 944 391 (true, H1335_cp1.1, H1335_cp1.2)) 1335 668 true) = true := by
  decide +kernel
theorem H1335_ok : RunOK pH1335 1335 (runFrom pH1335 (fmask pH1335) (cmask pH1335) (hmask pH1335) 944 391 (true, H1335_cp1.1, H1335_cp1.2)) ∧ ptTest pH1335 (runFrom pH1335 (fmask pH1335) (cmask pH1335) (hmask pH1335) 944 391 (true, H1335_cp1.1, H1335_cp1.2)) 1335 668 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1335_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1335_fin) true) H1335_seg1) (by decide) rfl H1335_fin ptTest_fst
noncomputable def I1335_cp1 : Nat × Nat := t7val% (fastRun pI1335 1 943 (init pI1335) (init pI1335))
theorem I1335_seg1 : segOK pI1335 1 943 (init pI1335) (init pI1335) I1335_cp1.1 I1335_cp1.2 = true := by
  decide +kernel
theorem I1335_fin : (prmOK pI1335 1335 && intTest pI1335 (runFrom pI1335 (fmask pI1335) (cmask pI1335) (hmask pI1335) 944 391 (true, I1335_cp1.1, I1335_cp1.2)) 1335 19 false) = true := by
  decide +kernel
theorem I1335_ok : RunOK pI1335 1335 (runFrom pI1335 (fmask pI1335) (cmask pI1335) (hmask pI1335) 944 391 (true, I1335_cp1.1, I1335_cp1.2)) ∧ intTest pI1335 (runFrom pI1335 (fmask pI1335) (cmask pI1335) (hmask pI1335) 944 391 (true, I1335_cp1.1, I1335_cp1.2)) 1335 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1335_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1335_fin) true) I1335_seg1) (by decide) rfl I1335_fin intTest_fst
theorem link1335 : linkOK pL1335 pH1335 pI1335 = true := by decide +kernel
theorem cvx1335 : ConvexBetweenHumps 1335 :=
  cvx_of L1335_ok H1335_ok I1335_ok link1335 (by decide)

/-! ### `N = 1336` -/

def pL1336 : Prm := ⟨79, 37, 39, 1338, 11, 18446744073709551616, 136700742679422919, 136700742679422919⟩
def pH1336 : Prm := ⟨79, 37, 39, 1338, 11, 18446744073709551616, 136701842191050695, 136701842191050695⟩
def pI1336 : Prm := ⟨67, 32, 32, 1338, 11, 18446744073709551616, 136700742679422919, 136701842191050695⟩
noncomputable def L1336_cp1 : Nat × Nat := t7val% (fastRun pL1336 1 944 (init pL1336) (init pL1336))
theorem L1336_seg1 : segOK pL1336 1 944 (init pL1336) (init pL1336) L1336_cp1.1 L1336_cp1.2 = true := by
  decide +kernel
theorem L1336_fin : (prmOK pL1336 1336 && ptTest pL1336 (runFrom pL1336 (fmask pL1336) (cmask pL1336) (hmask pL1336) 945 391 (true, L1336_cp1.1, L1336_cp1.2)) 1336 668 false) = true := by
  decide +kernel
theorem L1336_ok : RunOK pL1336 1336 (runFrom pL1336 (fmask pL1336) (cmask pL1336) (hmask pL1336) 945 391 (true, L1336_cp1.1, L1336_cp1.2)) ∧ ptTest pL1336 (runFrom pL1336 (fmask pL1336) (cmask pL1336) (hmask pL1336) 945 391 (true, L1336_cp1.1, L1336_cp1.2)) 1336 668 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1336_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1336_fin) true) L1336_seg1) (by decide) rfl L1336_fin ptTest_fst
noncomputable def H1336_cp1 : Nat × Nat := t7val% (fastRun pH1336 1 944 (init pH1336) (init pH1336))
theorem H1336_seg1 : segOK pH1336 1 944 (init pH1336) (init pH1336) H1336_cp1.1 H1336_cp1.2 = true := by
  decide +kernel
theorem H1336_fin : (prmOK pH1336 1336 && ptTest pH1336 (runFrom pH1336 (fmask pH1336) (cmask pH1336) (hmask pH1336) 945 391 (true, H1336_cp1.1, H1336_cp1.2)) 1336 668 true) = true := by
  decide +kernel
theorem H1336_ok : RunOK pH1336 1336 (runFrom pH1336 (fmask pH1336) (cmask pH1336) (hmask pH1336) 945 391 (true, H1336_cp1.1, H1336_cp1.2)) ∧ ptTest pH1336 (runFrom pH1336 (fmask pH1336) (cmask pH1336) (hmask pH1336) 945 391 (true, H1336_cp1.1, H1336_cp1.2)) 1336 668 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1336_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1336_fin) true) H1336_seg1) (by decide) rfl H1336_fin ptTest_fst
noncomputable def I1336_cp1 : Nat × Nat := t7val% (fastRun pI1336 1 944 (init pI1336) (init pI1336))
theorem I1336_seg1 : segOK pI1336 1 944 (init pI1336) (init pI1336) I1336_cp1.1 I1336_cp1.2 = true := by
  decide +kernel
theorem I1336_fin : (prmOK pI1336 1336 && intTest pI1336 (runFrom pI1336 (fmask pI1336) (cmask pI1336) (hmask pI1336) 945 391 (true, I1336_cp1.1, I1336_cp1.2)) 1336 19 true) = true := by
  decide +kernel
theorem I1336_ok : RunOK pI1336 1336 (runFrom pI1336 (fmask pI1336) (cmask pI1336) (hmask pI1336) 945 391 (true, I1336_cp1.1, I1336_cp1.2)) ∧ intTest pI1336 (runFrom pI1336 (fmask pI1336) (cmask pI1336) (hmask pI1336) 945 391 (true, I1336_cp1.1, I1336_cp1.2)) 1336 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1336_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1336_fin) true) I1336_seg1) (by decide) rfl I1336_fin intTest_fst
theorem link1336 : linkOK pL1336 pH1336 pI1336 = true := by decide +kernel
theorem cvx1336 : ConvexBetweenHumps 1336 :=
  cvx_of L1336_ok H1336_ok I1336_ok link1336 (by decide)
theorem cenlink1336 : cenLinkOK pI1336 1336 = true := by decide +kernel
theorem cen1336 : CenterUniqueMin 1336 ∧ DipHyp 1336 ∧ OnePointHyps 1336 :=
  cen_of L1336_ok H1336_ok I1336_ok link1336 cenlink1336

/-! ### `N = 1337` -/

def pL1337 : Prm := ⟨79, 37, 39, 1339, 11, 18446744073709551616, 136617941289259499, 136617941289259499⟩
def pH1337 : Prm := ⟨79, 37, 39, 1339, 11, 18446744073709551616, 136619040800887275, 136619040800887275⟩
def pI1337 : Prm := ⟨67, 32, 32, 1339, 11, 18446744073709551616, 136617941289259499, 136619040800887275⟩
noncomputable def L1337_cp1 : Nat × Nat := t7val% (fastRun pL1337 1 944 (init pL1337) (init pL1337))
theorem L1337_seg1 : segOK pL1337 1 944 (init pL1337) (init pL1337) L1337_cp1.1 L1337_cp1.2 = true := by
  decide +kernel
theorem L1337_fin : (prmOK pL1337 1337 && ptTest pL1337 (runFrom pL1337 (fmask pL1337) (cmask pL1337) (hmask pL1337) 945 392 (true, L1337_cp1.1, L1337_cp1.2)) 1337 669 false) = true := by
  decide +kernel
theorem L1337_ok : RunOK pL1337 1337 (runFrom pL1337 (fmask pL1337) (cmask pL1337) (hmask pL1337) 945 392 (true, L1337_cp1.1, L1337_cp1.2)) ∧ ptTest pL1337 (runFrom pL1337 (fmask pL1337) (cmask pL1337) (hmask pL1337) 945 392 (true, L1337_cp1.1, L1337_cp1.2)) 1337 669 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1337_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1337_fin) true) L1337_seg1) (by decide) rfl L1337_fin ptTest_fst
noncomputable def H1337_cp1 : Nat × Nat := t7val% (fastRun pH1337 1 944 (init pH1337) (init pH1337))
theorem H1337_seg1 : segOK pH1337 1 944 (init pH1337) (init pH1337) H1337_cp1.1 H1337_cp1.2 = true := by
  decide +kernel
theorem H1337_fin : (prmOK pH1337 1337 && ptTest pH1337 (runFrom pH1337 (fmask pH1337) (cmask pH1337) (hmask pH1337) 945 392 (true, H1337_cp1.1, H1337_cp1.2)) 1337 669 true) = true := by
  decide +kernel
theorem H1337_ok : RunOK pH1337 1337 (runFrom pH1337 (fmask pH1337) (cmask pH1337) (hmask pH1337) 945 392 (true, H1337_cp1.1, H1337_cp1.2)) ∧ ptTest pH1337 (runFrom pH1337 (fmask pH1337) (cmask pH1337) (hmask pH1337) 945 392 (true, H1337_cp1.1, H1337_cp1.2)) 1337 669 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1337_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1337_fin) true) H1337_seg1) (by decide) rfl H1337_fin ptTest_fst
noncomputable def I1337_cp1 : Nat × Nat := t7val% (fastRun pI1337 1 944 (init pI1337) (init pI1337))
theorem I1337_seg1 : segOK pI1337 1 944 (init pI1337) (init pI1337) I1337_cp1.1 I1337_cp1.2 = true := by
  decide +kernel
theorem I1337_fin : (prmOK pI1337 1337 && intTest pI1337 (runFrom pI1337 (fmask pI1337) (cmask pI1337) (hmask pI1337) 945 392 (true, I1337_cp1.1, I1337_cp1.2)) 1337 19 false) = true := by
  decide +kernel
theorem I1337_ok : RunOK pI1337 1337 (runFrom pI1337 (fmask pI1337) (cmask pI1337) (hmask pI1337) 945 392 (true, I1337_cp1.1, I1337_cp1.2)) ∧ intTest pI1337 (runFrom pI1337 (fmask pI1337) (cmask pI1337) (hmask pI1337) 945 392 (true, I1337_cp1.1, I1337_cp1.2)) 1337 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1337_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1337_fin) true) I1337_seg1) (by decide) rfl I1337_fin intTest_fst
theorem link1337 : linkOK pL1337 pH1337 pI1337 = true := by decide +kernel
theorem cvx1337 : ConvexBetweenHumps 1337 :=
  cvx_of L1337_ok H1337_ok I1337_ok link1337 (by decide)

/-! ### The range -/

theorem cvx_1315_1337 {N : ℕ} (h1 : 1315 ≤ N) (h2 : N ≤ 1337) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1325
  · by_cases h4 : N ≤ 1319
    · by_cases h6 : N ≤ 1316
      · by_cases h8 : N ≤ 1315
        · obtain rfl : N = 1315 := by omega
          exact cvx1315
        · obtain rfl : N = 1316 := by omega
          exact cvx1316
      · by_cases h8 : N ≤ 1317
        · obtain rfl : N = 1317 := by omega
          exact cvx1317
        · by_cases h10 : N ≤ 1318
          · obtain rfl : N = 1318 := by omega
            exact cvx1318
          · obtain rfl : N = 1319 := by omega
            exact cvx1319
    · by_cases h6 : N ≤ 1322
      · by_cases h8 : N ≤ 1320
        · obtain rfl : N = 1320 := by omega
          exact cvx1320
        · by_cases h10 : N ≤ 1321
          · obtain rfl : N = 1321 := by omega
            exact cvx1321
          · obtain rfl : N = 1322 := by omega
            exact cvx1322
      · by_cases h8 : N ≤ 1323
        · obtain rfl : N = 1323 := by omega
          exact cvx1323
        · by_cases h10 : N ≤ 1324
          · obtain rfl : N = 1324 := by omega
            exact cvx1324
          · obtain rfl : N = 1325 := by omega
            exact cvx1325
  · by_cases h4 : N ≤ 1331
    · by_cases h6 : N ≤ 1328
      · by_cases h8 : N ≤ 1326
        · obtain rfl : N = 1326 := by omega
          exact cvx1326
        · by_cases h10 : N ≤ 1327
          · obtain rfl : N = 1327 := by omega
            exact cvx1327
          · obtain rfl : N = 1328 := by omega
            exact cvx1328
      · by_cases h8 : N ≤ 1329
        · obtain rfl : N = 1329 := by omega
          exact cvx1329
        · by_cases h10 : N ≤ 1330
          · obtain rfl : N = 1330 := by omega
            exact cvx1330
          · obtain rfl : N = 1331 := by omega
            exact cvx1331
    · by_cases h6 : N ≤ 1334
      · by_cases h8 : N ≤ 1332
        · obtain rfl : N = 1332 := by omega
          exact cvx1332
        · by_cases h10 : N ≤ 1333
          · obtain rfl : N = 1333 := by omega
            exact cvx1333
          · obtain rfl : N = 1334 := by omega
            exact cvx1334
      · by_cases h8 : N ≤ 1335
        · obtain rfl : N = 1335 := by omega
          exact cvx1335
        · by_cases h10 : N ≤ 1336
          · obtain rfl : N = 1336 := by omega
            exact cvx1336
          · obtain rfl : N = 1337 := by omega
            exact cvx1337

theorem cen_1315_1337 {N : ℕ} (h1 : 1315 ≤ N) (h2 : N ≤ 1337) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1324
  · by_cases h4 : N ≤ 1318
    · by_cases h6 : N ≤ 1316
      · obtain rfl : N = 1316 := by omega
        exact cen1316
      · obtain rfl : N = 1318 := by omega
        exact cen1318
    · by_cases h6 : N ≤ 1320
      · obtain rfl : N = 1320 := by omega
        exact cen1320
      · by_cases h8 : N ≤ 1322
        · obtain rfl : N = 1322 := by omega
          exact cen1322
        · obtain rfl : N = 1324 := by omega
          exact cen1324
  · by_cases h4 : N ≤ 1330
    · by_cases h6 : N ≤ 1326
      · obtain rfl : N = 1326 := by omega
        exact cen1326
      · by_cases h8 : N ≤ 1328
        · obtain rfl : N = 1328 := by omega
          exact cen1328
        · obtain rfl : N = 1330 := by omega
          exact cen1330
    · by_cases h6 : N ≤ 1332
      · obtain rfl : N = 1332 := by omega
        exact cen1332
      · by_cases h8 : N ≤ 1334
        · obtain rfl : N = 1334 := by omega
          exact cen1334
        · obtain rfl : N = 1336 := by omega
          exact cen1336

end Kagey131.PaperD.T7
