import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1639, …, 1652` (generated)

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

/-! ### `N = 1639` -/

def pL1639 : Prm := ⟨80, 37, 40, 1641, 11, 18446744073709551616, 115766760615590217, 115766760615590217⟩
def pH1639 : Prm := ⟨80, 37, 40, 1641, 11, 18446744073709551616, 115767860127217993, 115767860127217993⟩
def pI1639 : Prm := ⟨67, 33, 31, 1641, 11, 18446744073709551616, 115766760615590217, 115767860127217993⟩
noncomputable def L1639_cp1 : Nat × Nat := t7val% (fastRun pL1639 1 1158 (init pL1639) (init pL1639))
theorem L1639_seg1 : segOK pL1639 1 1158 (init pL1639) (init pL1639) L1639_cp1.1 L1639_cp1.2 = true := by
  decide +kernel
theorem L1639_fin : (prmOK pL1639 1639 && ptTest pL1639 (runFrom pL1639 (fmask pL1639) (cmask pL1639) (hmask pL1639) 1159 480 (true, L1639_cp1.1, L1639_cp1.2)) 1639 820 false) = true := by
  decide +kernel
theorem L1639_ok : RunOK pL1639 1639 (runFrom pL1639 (fmask pL1639) (cmask pL1639) (hmask pL1639) 1159 480 (true, L1639_cp1.1, L1639_cp1.2)) ∧ ptTest pL1639 (runFrom pL1639 (fmask pL1639) (cmask pL1639) (hmask pL1639) 1159 480 (true, L1639_cp1.1, L1639_cp1.2)) 1639 820 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1639_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1639_fin) true) L1639_seg1) (by decide) rfl L1639_fin ptTest_fst
noncomputable def H1639_cp1 : Nat × Nat := t7val% (fastRun pH1639 1 1158 (init pH1639) (init pH1639))
theorem H1639_seg1 : segOK pH1639 1 1158 (init pH1639) (init pH1639) H1639_cp1.1 H1639_cp1.2 = true := by
  decide +kernel
theorem H1639_fin : (prmOK pH1639 1639 && ptTest pH1639 (runFrom pH1639 (fmask pH1639) (cmask pH1639) (hmask pH1639) 1159 480 (true, H1639_cp1.1, H1639_cp1.2)) 1639 820 true) = true := by
  decide +kernel
theorem H1639_ok : RunOK pH1639 1639 (runFrom pH1639 (fmask pH1639) (cmask pH1639) (hmask pH1639) 1159 480 (true, H1639_cp1.1, H1639_cp1.2)) ∧ ptTest pH1639 (runFrom pH1639 (fmask pH1639) (cmask pH1639) (hmask pH1639) 1159 480 (true, H1639_cp1.1, H1639_cp1.2)) 1639 820 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1639_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1639_fin) true) H1639_seg1) (by decide) rfl H1639_fin ptTest_fst
noncomputable def I1639_cp1 : Nat × Nat := t7val% (fastRun pI1639 1 1158 (init pI1639) (init pI1639))
theorem I1639_seg1 : segOK pI1639 1 1158 (init pI1639) (init pI1639) I1639_cp1.1 I1639_cp1.2 = true := by
  decide +kernel
theorem I1639_fin : (prmOK pI1639 1639 && intTest pI1639 (runFrom pI1639 (fmask pI1639) (cmask pI1639) (hmask pI1639) 1159 480 (true, I1639_cp1.1, I1639_cp1.2)) 1639 21 false) = true := by
  decide +kernel
theorem I1639_ok : RunOK pI1639 1639 (runFrom pI1639 (fmask pI1639) (cmask pI1639) (hmask pI1639) 1159 480 (true, I1639_cp1.1, I1639_cp1.2)) ∧ intTest pI1639 (runFrom pI1639 (fmask pI1639) (cmask pI1639) (hmask pI1639) 1159 480 (true, I1639_cp1.1, I1639_cp1.2)) 1639 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1639_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1639_fin) true) I1639_seg1) (by decide) rfl I1639_fin intTest_fst
theorem link1639 : linkOK pL1639 pH1639 pI1639 = true := by decide +kernel
theorem cvx1639 : ConvexBetweenHumps 1639 :=
  cvx_of L1639_ok H1639_ok I1639_ok link1639 (by decide)

/-! ### `N = 1640` -/

def pL1640 : Prm := ⟨80, 37, 40, 1642, 11, 18446744073709551616, 115709118112000015, 115709118112000015⟩
def pH1640 : Prm := ⟨80, 37, 40, 1642, 11, 18446744073709551616, 115710217623627791, 115710217623627791⟩
def pI1640 : Prm := ⟨67, 33, 31, 1642, 11, 18446744073709551616, 115709118112000015, 115710217623627791⟩
noncomputable def L1640_cp1 : Nat × Nat := t7val% (fastRun pL1640 1 1159 (init pL1640) (init pL1640))
theorem L1640_seg1 : segOK pL1640 1 1159 (init pL1640) (init pL1640) L1640_cp1.1 L1640_cp1.2 = true := by
  decide +kernel
theorem L1640_fin : (prmOK pL1640 1640 && ptTest pL1640 (runFrom pL1640 (fmask pL1640) (cmask pL1640) (hmask pL1640) 1160 480 (true, L1640_cp1.1, L1640_cp1.2)) 1640 820 false) = true := by
  decide +kernel
theorem L1640_ok : RunOK pL1640 1640 (runFrom pL1640 (fmask pL1640) (cmask pL1640) (hmask pL1640) 1160 480 (true, L1640_cp1.1, L1640_cp1.2)) ∧ ptTest pL1640 (runFrom pL1640 (fmask pL1640) (cmask pL1640) (hmask pL1640) 1160 480 (true, L1640_cp1.1, L1640_cp1.2)) 1640 820 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1640_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1640_fin) true) L1640_seg1) (by decide) rfl L1640_fin ptTest_fst
noncomputable def H1640_cp1 : Nat × Nat := t7val% (fastRun pH1640 1 1159 (init pH1640) (init pH1640))
theorem H1640_seg1 : segOK pH1640 1 1159 (init pH1640) (init pH1640) H1640_cp1.1 H1640_cp1.2 = true := by
  decide +kernel
theorem H1640_fin : (prmOK pH1640 1640 && ptTest pH1640 (runFrom pH1640 (fmask pH1640) (cmask pH1640) (hmask pH1640) 1160 480 (true, H1640_cp1.1, H1640_cp1.2)) 1640 820 true) = true := by
  decide +kernel
theorem H1640_ok : RunOK pH1640 1640 (runFrom pH1640 (fmask pH1640) (cmask pH1640) (hmask pH1640) 1160 480 (true, H1640_cp1.1, H1640_cp1.2)) ∧ ptTest pH1640 (runFrom pH1640 (fmask pH1640) (cmask pH1640) (hmask pH1640) 1160 480 (true, H1640_cp1.1, H1640_cp1.2)) 1640 820 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1640_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1640_fin) true) H1640_seg1) (by decide) rfl H1640_fin ptTest_fst
noncomputable def I1640_cp1 : Nat × Nat := t7val% (fastRun pI1640 1 1159 (init pI1640) (init pI1640))
theorem I1640_seg1 : segOK pI1640 1 1159 (init pI1640) (init pI1640) I1640_cp1.1 I1640_cp1.2 = true := by
  decide +kernel
theorem I1640_fin : (prmOK pI1640 1640 && intTest pI1640 (runFrom pI1640 (fmask pI1640) (cmask pI1640) (hmask pI1640) 1160 480 (true, I1640_cp1.1, I1640_cp1.2)) 1640 21 true) = true := by
  decide +kernel
theorem I1640_ok : RunOK pI1640 1640 (runFrom pI1640 (fmask pI1640) (cmask pI1640) (hmask pI1640) 1160 480 (true, I1640_cp1.1, I1640_cp1.2)) ∧ intTest pI1640 (runFrom pI1640 (fmask pI1640) (cmask pI1640) (hmask pI1640) 1160 480 (true, I1640_cp1.1, I1640_cp1.2)) 1640 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1640_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1640_fin) true) I1640_seg1) (by decide) rfl I1640_fin intTest_fst
theorem link1640 : linkOK pL1640 pH1640 pI1640 = true := by decide +kernel
theorem cvx1640 : ConvexBetweenHumps 1640 :=
  cvx_of L1640_ok H1640_ok I1640_ok link1640 (by decide)
theorem cenlink1640 : cenLinkOK pI1640 1640 = true := by decide +kernel
theorem cen1640 : CenterUniqueMin 1640 ∧ DipHyp 1640 ∧ OnePointHyps 1640 :=
  cen_of L1640_ok H1640_ok I1640_ok link1640 cenlink1640

/-! ### `N = 1641` -/

def pL1641 : Prm := ⟨80, 37, 40, 1643, 11, 18446744073709551616, 115651512433146946, 115651512433146946⟩
def pH1641 : Prm := ⟨80, 37, 40, 1643, 11, 18446744073709551616, 115652611944774722, 115652611944774722⟩
def pI1641 : Prm := ⟨67, 33, 31, 1643, 11, 18446744073709551616, 115651512433146946, 115652611944774722⟩
noncomputable def L1641_cp1 : Nat × Nat := t7val% (fastRun pL1641 1 946 (init pL1641) (init pL1641))
theorem L1641_seg1 : segOK pL1641 1 946 (init pL1641) (init pL1641) L1641_cp1.1 L1641_cp1.2 = true := by
  decide +kernel
noncomputable def L1641_cp2 : Nat × Nat := t7val% (fastRun pL1641 1 1339 (init pL1641) (init pL1641))
theorem L1641_seg2 : segOK pL1641 947 393 L1641_cp1.1 L1641_cp1.2 L1641_cp2.1 L1641_cp2.2 = true := by
  decide +kernel
theorem L1641_fin : (prmOK pL1641 1641 && ptTest pL1641 (runFrom pL1641 (fmask pL1641) (cmask pL1641) (hmask pL1641) 1340 301 (true, L1641_cp2.1, L1641_cp2.2)) 1641 821 false) = true := by
  decide +kernel
theorem L1641_ok : RunOK pL1641 1641 (runFrom pL1641 (fmask pL1641) (cmask pL1641) (hmask pL1641) 1340 301 (true, L1641_cp2.1, L1641_cp2.2)) ∧ ptTest pL1641 (runFrom pL1641 (fmask pL1641) (cmask pL1641) (hmask pL1641) 1340 301 (true, L1641_cp2.1, L1641_cp2.2)) 1641 821 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1641_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1641_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1641_fin) true) L1641_seg1) L1641_seg2) (by decide) rfl L1641_fin ptTest_fst
noncomputable def H1641_cp1 : Nat × Nat := t7val% (fastRun pH1641 1 946 (init pH1641) (init pH1641))
theorem H1641_seg1 : segOK pH1641 1 946 (init pH1641) (init pH1641) H1641_cp1.1 H1641_cp1.2 = true := by
  decide +kernel
noncomputable def H1641_cp2 : Nat × Nat := t7val% (fastRun pH1641 1 1339 (init pH1641) (init pH1641))
theorem H1641_seg2 : segOK pH1641 947 393 H1641_cp1.1 H1641_cp1.2 H1641_cp2.1 H1641_cp2.2 = true := by
  decide +kernel
theorem H1641_fin : (prmOK pH1641 1641 && ptTest pH1641 (runFrom pH1641 (fmask pH1641) (cmask pH1641) (hmask pH1641) 1340 301 (true, H1641_cp2.1, H1641_cp2.2)) 1641 821 true) = true := by
  decide +kernel
theorem H1641_ok : RunOK pH1641 1641 (runFrom pH1641 (fmask pH1641) (cmask pH1641) (hmask pH1641) 1340 301 (true, H1641_cp2.1, H1641_cp2.2)) ∧ ptTest pH1641 (runFrom pH1641 (fmask pH1641) (cmask pH1641) (hmask pH1641) 1340 301 (true, H1641_cp2.1, H1641_cp2.2)) 1641 821 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1641_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1641_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1641_fin) true) H1641_seg1) H1641_seg2) (by decide) rfl H1641_fin ptTest_fst
noncomputable def I1641_cp1 : Nat × Nat := t7val% (fastRun pI1641 1 1159 (init pI1641) (init pI1641))
theorem I1641_seg1 : segOK pI1641 1 1159 (init pI1641) (init pI1641) I1641_cp1.1 I1641_cp1.2 = true := by
  decide +kernel
theorem I1641_fin : (prmOK pI1641 1641 && intTest pI1641 (runFrom pI1641 (fmask pI1641) (cmask pI1641) (hmask pI1641) 1160 481 (true, I1641_cp1.1, I1641_cp1.2)) 1641 21 false) = true := by
  decide +kernel
theorem I1641_ok : RunOK pI1641 1641 (runFrom pI1641 (fmask pI1641) (cmask pI1641) (hmask pI1641) 1160 481 (true, I1641_cp1.1, I1641_cp1.2)) ∧ intTest pI1641 (runFrom pI1641 (fmask pI1641) (cmask pI1641) (hmask pI1641) 1160 481 (true, I1641_cp1.1, I1641_cp1.2)) 1641 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1641_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1641_fin) true) I1641_seg1) (by decide) rfl I1641_fin intTest_fst
theorem link1641 : linkOK pL1641 pH1641 pI1641 = true := by decide +kernel
theorem cvx1641 : ConvexBetweenHumps 1641 :=
  cvx_of L1641_ok H1641_ok I1641_ok link1641 (by decide)

/-! ### `N = 1642` -/

def pL1642 : Prm := ⟨80, 37, 40, 1644, 11, 18446744073709551616, 115593994535210034, 115593994535210034⟩
def pH1642 : Prm := ⟨80, 37, 40, 1644, 11, 18446744073709551616, 115595094046837810, 115595094046837810⟩
def pI1642 : Prm := ⟨67, 33, 31, 1644, 11, 18446744073709551616, 115593994535210034, 115595094046837810⟩
noncomputable def L1642_cp1 : Nat × Nat := t7val% (fastRun pL1642 1 947 (init pL1642) (init pL1642))
theorem L1642_seg1 : segOK pL1642 1 947 (init pL1642) (init pL1642) L1642_cp1.1 L1642_cp1.2 = true := by
  decide +kernel
noncomputable def L1642_cp2 : Nat × Nat := t7val% (fastRun pL1642 1 1340 (init pL1642) (init pL1642))
theorem L1642_seg2 : segOK pL1642 948 393 L1642_cp1.1 L1642_cp1.2 L1642_cp2.1 L1642_cp2.2 = true := by
  decide +kernel
theorem L1642_fin : (prmOK pL1642 1642 && ptTest pL1642 (runFrom pL1642 (fmask pL1642) (cmask pL1642) (hmask pL1642) 1341 301 (true, L1642_cp2.1, L1642_cp2.2)) 1642 821 false) = true := by
  decide +kernel
theorem L1642_ok : RunOK pL1642 1642 (runFrom pL1642 (fmask pL1642) (cmask pL1642) (hmask pL1642) 1341 301 (true, L1642_cp2.1, L1642_cp2.2)) ∧ ptTest pL1642 (runFrom pL1642 (fmask pL1642) (cmask pL1642) (hmask pL1642) 1341 301 (true, L1642_cp2.1, L1642_cp2.2)) 1642 821 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1642_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1642_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1642_fin) true) L1642_seg1) L1642_seg2) (by decide) rfl L1642_fin ptTest_fst
noncomputable def H1642_cp1 : Nat × Nat := t7val% (fastRun pH1642 1 947 (init pH1642) (init pH1642))
theorem H1642_seg1 : segOK pH1642 1 947 (init pH1642) (init pH1642) H1642_cp1.1 H1642_cp1.2 = true := by
  decide +kernel
noncomputable def H1642_cp2 : Nat × Nat := t7val% (fastRun pH1642 1 1340 (init pH1642) (init pH1642))
theorem H1642_seg2 : segOK pH1642 948 393 H1642_cp1.1 H1642_cp1.2 H1642_cp2.1 H1642_cp2.2 = true := by
  decide +kernel
theorem H1642_fin : (prmOK pH1642 1642 && ptTest pH1642 (runFrom pH1642 (fmask pH1642) (cmask pH1642) (hmask pH1642) 1341 301 (true, H1642_cp2.1, H1642_cp2.2)) 1642 821 true) = true := by
  decide +kernel
theorem H1642_ok : RunOK pH1642 1642 (runFrom pH1642 (fmask pH1642) (cmask pH1642) (hmask pH1642) 1341 301 (true, H1642_cp2.1, H1642_cp2.2)) ∧ ptTest pH1642 (runFrom pH1642 (fmask pH1642) (cmask pH1642) (hmask pH1642) 1341 301 (true, H1642_cp2.1, H1642_cp2.2)) 1642 821 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1642_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1642_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1642_fin) true) H1642_seg1) H1642_seg2) (by decide) rfl H1642_fin ptTest_fst
noncomputable def I1642_cp1 : Nat × Nat := t7val% (fastRun pI1642 1 1160 (init pI1642) (init pI1642))
theorem I1642_seg1 : segOK pI1642 1 1160 (init pI1642) (init pI1642) I1642_cp1.1 I1642_cp1.2 = true := by
  decide +kernel
theorem I1642_fin : (prmOK pI1642 1642 && intTest pI1642 (runFrom pI1642 (fmask pI1642) (cmask pI1642) (hmask pI1642) 1161 481 (true, I1642_cp1.1, I1642_cp1.2)) 1642 21 true) = true := by
  decide +kernel
theorem I1642_ok : RunOK pI1642 1642 (runFrom pI1642 (fmask pI1642) (cmask pI1642) (hmask pI1642) 1161 481 (true, I1642_cp1.1, I1642_cp1.2)) ∧ intTest pI1642 (runFrom pI1642 (fmask pI1642) (cmask pI1642) (hmask pI1642) 1161 481 (true, I1642_cp1.1, I1642_cp1.2)) 1642 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1642_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1642_fin) true) I1642_seg1) (by decide) rfl I1642_fin intTest_fst
theorem link1642 : linkOK pL1642 pH1642 pI1642 = true := by decide +kernel
theorem cvx1642 : ConvexBetweenHumps 1642 :=
  cvx_of L1642_ok H1642_ok I1642_ok link1642 (by decide)
theorem cenlink1642 : cenLinkOK pI1642 1642 = true := by decide +kernel
theorem cen1642 : CenterUniqueMin 1642 ∧ DipHyp 1642 ∧ OnePointHyps 1642 :=
  cen_of L1642_ok H1642_ok I1642_ok link1642 cenlink1642

/-! ### `N = 1643` -/

def pL1643 : Prm := ⟨80, 37, 40, 1645, 11, 18446744073709551616, 115536513348267630, 115536513348267630⟩
def pH1643 : Prm := ⟨80, 37, 40, 1645, 11, 18446744073709551616, 115537612859895406, 115537612859895406⟩
def pI1643 : Prm := ⟨67, 33, 31, 1645, 11, 18446744073709551616, 115536513348267630, 115537612859895406⟩
noncomputable def L1643_cp1 : Nat × Nat := t7val% (fastRun pL1643 1 948 (init pL1643) (init pL1643))
theorem L1643_seg1 : segOK pL1643 1 948 (init pL1643) (init pL1643) L1643_cp1.1 L1643_cp1.2 = true := by
  decide +kernel
noncomputable def L1643_cp2 : Nat × Nat := t7val% (fastRun pL1643 1 1341 (init pL1643) (init pL1643))
theorem L1643_seg2 : segOK pL1643 949 393 L1643_cp1.1 L1643_cp1.2 L1643_cp2.1 L1643_cp2.2 = true := by
  decide +kernel
theorem L1643_fin : (prmOK pL1643 1643 && ptTest pL1643 (runFrom pL1643 (fmask pL1643) (cmask pL1643) (hmask pL1643) 1342 301 (true, L1643_cp2.1, L1643_cp2.2)) 1643 822 false) = true := by
  decide +kernel
theorem L1643_ok : RunOK pL1643 1643 (runFrom pL1643 (fmask pL1643) (cmask pL1643) (hmask pL1643) 1342 301 (true, L1643_cp2.1, L1643_cp2.2)) ∧ ptTest pL1643 (runFrom pL1643 (fmask pL1643) (cmask pL1643) (hmask pL1643) 1342 301 (true, L1643_cp2.1, L1643_cp2.2)) 1643 822 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1643_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1643_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1643_fin) true) L1643_seg1) L1643_seg2) (by decide) rfl L1643_fin ptTest_fst
noncomputable def H1643_cp1 : Nat × Nat := t7val% (fastRun pH1643 1 948 (init pH1643) (init pH1643))
theorem H1643_seg1 : segOK pH1643 1 948 (init pH1643) (init pH1643) H1643_cp1.1 H1643_cp1.2 = true := by
  decide +kernel
noncomputable def H1643_cp2 : Nat × Nat := t7val% (fastRun pH1643 1 1341 (init pH1643) (init pH1643))
theorem H1643_seg2 : segOK pH1643 949 393 H1643_cp1.1 H1643_cp1.2 H1643_cp2.1 H1643_cp2.2 = true := by
  decide +kernel
theorem H1643_fin : (prmOK pH1643 1643 && ptTest pH1643 (runFrom pH1643 (fmask pH1643) (cmask pH1643) (hmask pH1643) 1342 301 (true, H1643_cp2.1, H1643_cp2.2)) 1643 822 true) = true := by
  decide +kernel
theorem H1643_ok : RunOK pH1643 1643 (runFrom pH1643 (fmask pH1643) (cmask pH1643) (hmask pH1643) 1342 301 (true, H1643_cp2.1, H1643_cp2.2)) ∧ ptTest pH1643 (runFrom pH1643 (fmask pH1643) (cmask pH1643) (hmask pH1643) 1342 301 (true, H1643_cp2.1, H1643_cp2.2)) 1643 822 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1643_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1643_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1643_fin) true) H1643_seg1) H1643_seg2) (by decide) rfl H1643_fin ptTest_fst
noncomputable def I1643_cp1 : Nat × Nat := t7val% (fastRun pI1643 1 1161 (init pI1643) (init pI1643))
theorem I1643_seg1 : segOK pI1643 1 1161 (init pI1643) (init pI1643) I1643_cp1.1 I1643_cp1.2 = true := by
  decide +kernel
theorem I1643_fin : (prmOK pI1643 1643 && intTest pI1643 (runFrom pI1643 (fmask pI1643) (cmask pI1643) (hmask pI1643) 1162 481 (true, I1643_cp1.1, I1643_cp1.2)) 1643 21 false) = true := by
  decide +kernel
theorem I1643_ok : RunOK pI1643 1643 (runFrom pI1643 (fmask pI1643) (cmask pI1643) (hmask pI1643) 1162 481 (true, I1643_cp1.1, I1643_cp1.2)) ∧ intTest pI1643 (runFrom pI1643 (fmask pI1643) (cmask pI1643) (hmask pI1643) 1162 481 (true, I1643_cp1.1, I1643_cp1.2)) 1643 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1643_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1643_fin) true) I1643_seg1) (by decide) rfl I1643_fin intTest_fst
theorem link1643 : linkOK pL1643 pH1643 pI1643 = true := by decide +kernel
theorem cvx1643 : ConvexBetweenHumps 1643 :=
  cvx_of L1643_ok H1643_ok I1643_ok link1643 (by decide)

/-! ### `N = 1644` -/

def pL1644 : Prm := ⟨80, 37, 40, 1646, 11, 18446744073709551616, 115479119639733226, 115479119639733226⟩
def pH1644 : Prm := ⟨80, 37, 40, 1646, 11, 18446744073709551616, 115480219151361002, 115480219151361002⟩
def pI1644 : Prm := ⟨67, 33, 31, 1646, 11, 18446744073709551616, 115479119639733226, 115480219151361002⟩
noncomputable def L1644_cp1 : Nat × Nat := t7val% (fastRun pL1644 1 948 (init pL1644) (init pL1644))
theorem L1644_seg1 : segOK pL1644 1 948 (init pL1644) (init pL1644) L1644_cp1.1 L1644_cp1.2 = true := by
  decide +kernel
noncomputable def L1644_cp2 : Nat × Nat := t7val% (fastRun pL1644 1 1341 (init pL1644) (init pL1644))
theorem L1644_seg2 : segOK pL1644 949 393 L1644_cp1.1 L1644_cp1.2 L1644_cp2.1 L1644_cp2.2 = true := by
  decide +kernel
theorem L1644_fin : (prmOK pL1644 1644 && ptTest pL1644 (runFrom pL1644 (fmask pL1644) (cmask pL1644) (hmask pL1644) 1342 302 (true, L1644_cp2.1, L1644_cp2.2)) 1644 822 false) = true := by
  decide +kernel
theorem L1644_ok : RunOK pL1644 1644 (runFrom pL1644 (fmask pL1644) (cmask pL1644) (hmask pL1644) 1342 302 (true, L1644_cp2.1, L1644_cp2.2)) ∧ ptTest pL1644 (runFrom pL1644 (fmask pL1644) (cmask pL1644) (hmask pL1644) 1342 302 (true, L1644_cp2.1, L1644_cp2.2)) 1644 822 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1644_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1644_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1644_fin) true) L1644_seg1) L1644_seg2) (by decide) rfl L1644_fin ptTest_fst
noncomputable def H1644_cp1 : Nat × Nat := t7val% (fastRun pH1644 1 948 (init pH1644) (init pH1644))
theorem H1644_seg1 : segOK pH1644 1 948 (init pH1644) (init pH1644) H1644_cp1.1 H1644_cp1.2 = true := by
  decide +kernel
noncomputable def H1644_cp2 : Nat × Nat := t7val% (fastRun pH1644 1 1341 (init pH1644) (init pH1644))
theorem H1644_seg2 : segOK pH1644 949 393 H1644_cp1.1 H1644_cp1.2 H1644_cp2.1 H1644_cp2.2 = true := by
  decide +kernel
theorem H1644_fin : (prmOK pH1644 1644 && ptTest pH1644 (runFrom pH1644 (fmask pH1644) (cmask pH1644) (hmask pH1644) 1342 302 (true, H1644_cp2.1, H1644_cp2.2)) 1644 822 true) = true := by
  decide +kernel
theorem H1644_ok : RunOK pH1644 1644 (runFrom pH1644 (fmask pH1644) (cmask pH1644) (hmask pH1644) 1342 302 (true, H1644_cp2.1, H1644_cp2.2)) ∧ ptTest pH1644 (runFrom pH1644 (fmask pH1644) (cmask pH1644) (hmask pH1644) 1342 302 (true, H1644_cp2.1, H1644_cp2.2)) 1644 822 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1644_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1644_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1644_fin) true) H1644_seg1) H1644_seg2) (by decide) rfl H1644_fin ptTest_fst
noncomputable def I1644_cp1 : Nat × Nat := t7val% (fastRun pI1644 1 1161 (init pI1644) (init pI1644))
theorem I1644_seg1 : segOK pI1644 1 1161 (init pI1644) (init pI1644) I1644_cp1.1 I1644_cp1.2 = true := by
  decide +kernel
theorem I1644_fin : (prmOK pI1644 1644 && intTest pI1644 (runFrom pI1644 (fmask pI1644) (cmask pI1644) (hmask pI1644) 1162 482 (true, I1644_cp1.1, I1644_cp1.2)) 1644 21 true) = true := by
  decide +kernel
theorem I1644_ok : RunOK pI1644 1644 (runFrom pI1644 (fmask pI1644) (cmask pI1644) (hmask pI1644) 1162 482 (true, I1644_cp1.1, I1644_cp1.2)) ∧ intTest pI1644 (runFrom pI1644 (fmask pI1644) (cmask pI1644) (hmask pI1644) 1162 482 (true, I1644_cp1.1, I1644_cp1.2)) 1644 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1644_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1644_fin) true) I1644_seg1) (by decide) rfl I1644_fin intTest_fst
theorem link1644 : linkOK pL1644 pH1644 pI1644 = true := by decide +kernel
theorem cvx1644 : ConvexBetweenHumps 1644 :=
  cvx_of L1644_ok H1644_ok I1644_ok link1644 (by decide)
theorem cenlink1644 : cenLinkOK pI1644 1644 = true := by decide +kernel
theorem cen1644 : CenterUniqueMin 1644 ∧ DipHyp 1644 ∧ OnePointHyps 1644 :=
  cen_of L1644_ok H1644_ok I1644_ok link1644 cenlink1644

/-! ### `N = 1645` -/

def pL1645 : Prm := ⟨80, 37, 40, 1647, 11, 18446744073709551616, 115421762528911875, 115421762528911875⟩
def pH1645 : Prm := ⟨80, 37, 40, 1647, 11, 18446744073709551616, 115422862040539651, 115422862040539651⟩
def pI1645 : Prm := ⟨67, 33, 31, 1647, 11, 18446744073709551616, 115421762528911875, 115422862040539651⟩
noncomputable def L1645_cp1 : Nat × Nat := t7val% (fastRun pL1645 1 949 (init pL1645) (init pL1645))
theorem L1645_seg1 : segOK pL1645 1 949 (init pL1645) (init pL1645) L1645_cp1.1 L1645_cp1.2 = true := by
  decide +kernel
noncomputable def L1645_cp2 : Nat × Nat := t7val% (fastRun pL1645 1 1342 (init pL1645) (init pL1645))
theorem L1645_seg2 : segOK pL1645 950 393 L1645_cp1.1 L1645_cp1.2 L1645_cp2.1 L1645_cp2.2 = true := by
  decide +kernel
theorem L1645_fin : (prmOK pL1645 1645 && ptTest pL1645 (runFrom pL1645 (fmask pL1645) (cmask pL1645) (hmask pL1645) 1343 302 (true, L1645_cp2.1, L1645_cp2.2)) 1645 823 false) = true := by
  decide +kernel
theorem L1645_ok : RunOK pL1645 1645 (runFrom pL1645 (fmask pL1645) (cmask pL1645) (hmask pL1645) 1343 302 (true, L1645_cp2.1, L1645_cp2.2)) ∧ ptTest pL1645 (runFrom pL1645 (fmask pL1645) (cmask pL1645) (hmask pL1645) 1343 302 (true, L1645_cp2.1, L1645_cp2.2)) 1645 823 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1645_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1645_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1645_fin) true) L1645_seg1) L1645_seg2) (by decide) rfl L1645_fin ptTest_fst
noncomputable def H1645_cp1 : Nat × Nat := t7val% (fastRun pH1645 1 949 (init pH1645) (init pH1645))
theorem H1645_seg1 : segOK pH1645 1 949 (init pH1645) (init pH1645) H1645_cp1.1 H1645_cp1.2 = true := by
  decide +kernel
noncomputable def H1645_cp2 : Nat × Nat := t7val% (fastRun pH1645 1 1342 (init pH1645) (init pH1645))
theorem H1645_seg2 : segOK pH1645 950 393 H1645_cp1.1 H1645_cp1.2 H1645_cp2.1 H1645_cp2.2 = true := by
  decide +kernel
theorem H1645_fin : (prmOK pH1645 1645 && ptTest pH1645 (runFrom pH1645 (fmask pH1645) (cmask pH1645) (hmask pH1645) 1343 302 (true, H1645_cp2.1, H1645_cp2.2)) 1645 823 true) = true := by
  decide +kernel
theorem H1645_ok : RunOK pH1645 1645 (runFrom pH1645 (fmask pH1645) (cmask pH1645) (hmask pH1645) 1343 302 (true, H1645_cp2.1, H1645_cp2.2)) ∧ ptTest pH1645 (runFrom pH1645 (fmask pH1645) (cmask pH1645) (hmask pH1645) 1343 302 (true, H1645_cp2.1, H1645_cp2.2)) 1645 823 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1645_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1645_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1645_fin) true) H1645_seg1) H1645_seg2) (by decide) rfl H1645_fin ptTest_fst
noncomputable def I1645_cp1 : Nat × Nat := t7val% (fastRun pI1645 1 1162 (init pI1645) (init pI1645))
theorem I1645_seg1 : segOK pI1645 1 1162 (init pI1645) (init pI1645) I1645_cp1.1 I1645_cp1.2 = true := by
  decide +kernel
theorem I1645_fin : (prmOK pI1645 1645 && intTest pI1645 (runFrom pI1645 (fmask pI1645) (cmask pI1645) (hmask pI1645) 1163 482 (true, I1645_cp1.1, I1645_cp1.2)) 1645 21 false) = true := by
  decide +kernel
theorem I1645_ok : RunOK pI1645 1645 (runFrom pI1645 (fmask pI1645) (cmask pI1645) (hmask pI1645) 1163 482 (true, I1645_cp1.1, I1645_cp1.2)) ∧ intTest pI1645 (runFrom pI1645 (fmask pI1645) (cmask pI1645) (hmask pI1645) 1163 482 (true, I1645_cp1.1, I1645_cp1.2)) 1645 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1645_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1645_fin) true) I1645_seg1) (by decide) rfl I1645_fin intTest_fst
theorem link1645 : linkOK pL1645 pH1645 pI1645 = true := by decide +kernel
theorem cvx1645 : ConvexBetweenHumps 1645 :=
  cvx_of L1645_ok H1645_ok I1645_ok link1645 (by decide)

/-! ### `N = 1646` -/

def pL1646 : Prm := ⟨80, 37, 40, 1648, 11, 18446744073709551616, 115364492595392323, 115364492595392323⟩
def pH1646 : Prm := ⟨80, 37, 40, 1648, 11, 18446744073709551616, 115365592107020099, 115365592107020099⟩
def pI1646 : Prm := ⟨67, 33, 31, 1648, 11, 18446744073709551616, 115364492595392323, 115365592107020099⟩
noncomputable def L1646_cp1 : Nat × Nat := t7val% (fastRun pL1646 1 949 (init pL1646) (init pL1646))
theorem L1646_seg1 : segOK pL1646 1 949 (init pL1646) (init pL1646) L1646_cp1.1 L1646_cp1.2 = true := by
  decide +kernel
noncomputable def L1646_cp2 : Nat × Nat := t7val% (fastRun pL1646 1 1343 (init pL1646) (init pL1646))
theorem L1646_seg2 : segOK pL1646 950 394 L1646_cp1.1 L1646_cp1.2 L1646_cp2.1 L1646_cp2.2 = true := by
  decide +kernel
theorem L1646_fin : (prmOK pL1646 1646 && ptTest pL1646 (runFrom pL1646 (fmask pL1646) (cmask pL1646) (hmask pL1646) 1344 302 (true, L1646_cp2.1, L1646_cp2.2)) 1646 823 false) = true := by
  decide +kernel
theorem L1646_ok : RunOK pL1646 1646 (runFrom pL1646 (fmask pL1646) (cmask pL1646) (hmask pL1646) 1344 302 (true, L1646_cp2.1, L1646_cp2.2)) ∧ ptTest pL1646 (runFrom pL1646 (fmask pL1646) (cmask pL1646) (hmask pL1646) 1344 302 (true, L1646_cp2.1, L1646_cp2.2)) 1646 823 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1646_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1646_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1646_fin) true) L1646_seg1) L1646_seg2) (by decide) rfl L1646_fin ptTest_fst
noncomputable def H1646_cp1 : Nat × Nat := t7val% (fastRun pH1646 1 949 (init pH1646) (init pH1646))
theorem H1646_seg1 : segOK pH1646 1 949 (init pH1646) (init pH1646) H1646_cp1.1 H1646_cp1.2 = true := by
  decide +kernel
noncomputable def H1646_cp2 : Nat × Nat := t7val% (fastRun pH1646 1 1343 (init pH1646) (init pH1646))
theorem H1646_seg2 : segOK pH1646 950 394 H1646_cp1.1 H1646_cp1.2 H1646_cp2.1 H1646_cp2.2 = true := by
  decide +kernel
theorem H1646_fin : (prmOK pH1646 1646 && ptTest pH1646 (runFrom pH1646 (fmask pH1646) (cmask pH1646) (hmask pH1646) 1344 302 (true, H1646_cp2.1, H1646_cp2.2)) 1646 823 true) = true := by
  decide +kernel
theorem H1646_ok : RunOK pH1646 1646 (runFrom pH1646 (fmask pH1646) (cmask pH1646) (hmask pH1646) 1344 302 (true, H1646_cp2.1, H1646_cp2.2)) ∧ ptTest pH1646 (runFrom pH1646 (fmask pH1646) (cmask pH1646) (hmask pH1646) 1344 302 (true, H1646_cp2.1, H1646_cp2.2)) 1646 823 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1646_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1646_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1646_fin) true) H1646_seg1) H1646_seg2) (by decide) rfl H1646_fin ptTest_fst
noncomputable def I1646_cp1 : Nat × Nat := t7val% (fastRun pI1646 1 1163 (init pI1646) (init pI1646))
theorem I1646_seg1 : segOK pI1646 1 1163 (init pI1646) (init pI1646) I1646_cp1.1 I1646_cp1.2 = true := by
  decide +kernel
theorem I1646_fin : (prmOK pI1646 1646 && intTest pI1646 (runFrom pI1646 (fmask pI1646) (cmask pI1646) (hmask pI1646) 1164 482 (true, I1646_cp1.1, I1646_cp1.2)) 1646 21 true) = true := by
  decide +kernel
theorem I1646_ok : RunOK pI1646 1646 (runFrom pI1646 (fmask pI1646) (cmask pI1646) (hmask pI1646) 1164 482 (true, I1646_cp1.1, I1646_cp1.2)) ∧ intTest pI1646 (runFrom pI1646 (fmask pI1646) (cmask pI1646) (hmask pI1646) 1164 482 (true, I1646_cp1.1, I1646_cp1.2)) 1646 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1646_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1646_fin) true) I1646_seg1) (by decide) rfl I1646_fin intTest_fst
theorem link1646 : linkOK pL1646 pH1646 pI1646 = true := by decide +kernel
theorem cvx1646 : ConvexBetweenHumps 1646 :=
  cvx_of L1646_ok H1646_ok I1646_ok link1646 (by decide)
theorem cenlink1646 : cenLinkOK pI1646 1646 = true := by decide +kernel
theorem cen1646 : CenterUniqueMin 1646 ∧ DipHyp 1646 ∧ OnePointHyps 1646 :=
  cen_of L1646_ok H1646_ok I1646_ok link1646 cenlink1646

/-! ### `N = 1647` -/

def pL1647 : Prm := ⟨80, 37, 40, 1649, 11, 18446744073709551616, 115307259146765535, 115307259146765535⟩
def pH1647 : Prm := ⟨80, 37, 40, 1649, 11, 18446744073709551616, 115308358658393311, 115308358658393311⟩
def pI1647 : Prm := ⟨67, 33, 31, 1649, 11, 18446744073709551616, 115307259146765535, 115308358658393311⟩
noncomputable def L1647_cp1 : Nat × Nat := t7val% (fastRun pL1647 1 950 (init pL1647) (init pL1647))
theorem L1647_seg1 : segOK pL1647 1 950 (init pL1647) (init pL1647) L1647_cp1.1 L1647_cp1.2 = true := by
  decide +kernel
noncomputable def L1647_cp2 : Nat × Nat := t7val% (fastRun pL1647 1 1344 (init pL1647) (init pL1647))
theorem L1647_seg2 : segOK pL1647 951 394 L1647_cp1.1 L1647_cp1.2 L1647_cp2.1 L1647_cp2.2 = true := by
  decide +kernel
theorem L1647_fin : (prmOK pL1647 1647 && ptTest pL1647 (runFrom pL1647 (fmask pL1647) (cmask pL1647) (hmask pL1647) 1345 302 (true, L1647_cp2.1, L1647_cp2.2)) 1647 824 false) = true := by
  decide +kernel
theorem L1647_ok : RunOK pL1647 1647 (runFrom pL1647 (fmask pL1647) (cmask pL1647) (hmask pL1647) 1345 302 (true, L1647_cp2.1, L1647_cp2.2)) ∧ ptTest pL1647 (runFrom pL1647 (fmask pL1647) (cmask pL1647) (hmask pL1647) 1345 302 (true, L1647_cp2.1, L1647_cp2.2)) 1647 824 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1647_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1647_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1647_fin) true) L1647_seg1) L1647_seg2) (by decide) rfl L1647_fin ptTest_fst
noncomputable def H1647_cp1 : Nat × Nat := t7val% (fastRun pH1647 1 950 (init pH1647) (init pH1647))
theorem H1647_seg1 : segOK pH1647 1 950 (init pH1647) (init pH1647) H1647_cp1.1 H1647_cp1.2 = true := by
  decide +kernel
noncomputable def H1647_cp2 : Nat × Nat := t7val% (fastRun pH1647 1 1344 (init pH1647) (init pH1647))
theorem H1647_seg2 : segOK pH1647 951 394 H1647_cp1.1 H1647_cp1.2 H1647_cp2.1 H1647_cp2.2 = true := by
  decide +kernel
theorem H1647_fin : (prmOK pH1647 1647 && ptTest pH1647 (runFrom pH1647 (fmask pH1647) (cmask pH1647) (hmask pH1647) 1345 302 (true, H1647_cp2.1, H1647_cp2.2)) 1647 824 true) = true := by
  decide +kernel
theorem H1647_ok : RunOK pH1647 1647 (runFrom pH1647 (fmask pH1647) (cmask pH1647) (hmask pH1647) 1345 302 (true, H1647_cp2.1, H1647_cp2.2)) ∧ ptTest pH1647 (runFrom pH1647 (fmask pH1647) (cmask pH1647) (hmask pH1647) 1345 302 (true, H1647_cp2.1, H1647_cp2.2)) 1647 824 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1647_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1647_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1647_fin) true) H1647_seg1) H1647_seg2) (by decide) rfl H1647_fin ptTest_fst
noncomputable def I1647_cp1 : Nat × Nat := t7val% (fastRun pI1647 1 1164 (init pI1647) (init pI1647))
theorem I1647_seg1 : segOK pI1647 1 1164 (init pI1647) (init pI1647) I1647_cp1.1 I1647_cp1.2 = true := by
  decide +kernel
theorem I1647_fin : (prmOK pI1647 1647 && intTest pI1647 (runFrom pI1647 (fmask pI1647) (cmask pI1647) (hmask pI1647) 1165 482 (true, I1647_cp1.1, I1647_cp1.2)) 1647 21 false) = true := by
  decide +kernel
theorem I1647_ok : RunOK pI1647 1647 (runFrom pI1647 (fmask pI1647) (cmask pI1647) (hmask pI1647) 1165 482 (true, I1647_cp1.1, I1647_cp1.2)) ∧ intTest pI1647 (runFrom pI1647 (fmask pI1647) (cmask pI1647) (hmask pI1647) 1165 482 (true, I1647_cp1.1, I1647_cp1.2)) 1647 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1647_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1647_fin) true) I1647_seg1) (by decide) rfl I1647_fin intTest_fst
theorem link1647 : linkOK pL1647 pH1647 pI1647 = true := by decide +kernel
theorem cvx1647 : ConvexBetweenHumps 1647 :=
  cvx_of L1647_ok H1647_ok I1647_ok link1647 (by decide)

/-! ### `N = 1648` -/

def pL1648 : Prm := ⟨80, 37, 40, 1650, 11, 18446744073709551616, 115250112575773188, 115250112575773188⟩
def pH1648 : Prm := ⟨80, 37, 40, 1650, 11, 18446744073709551616, 115251212087400964, 115251212087400964⟩
def pI1648 : Prm := ⟨67, 33, 31, 1650, 11, 18446744073709551616, 115250112575773188, 115251212087400964⟩
noncomputable def L1648_cp1 : Nat × Nat := t7val% (fastRun pL1648 1 950 (init pL1648) (init pL1648))
theorem L1648_seg1 : segOK pL1648 1 950 (init pL1648) (init pL1648) L1648_cp1.1 L1648_cp1.2 = true := by
  decide +kernel
noncomputable def L1648_cp2 : Nat × Nat := t7val% (fastRun pL1648 1 1345 (init pL1648) (init pL1648))
theorem L1648_seg2 : segOK pL1648 951 395 L1648_cp1.1 L1648_cp1.2 L1648_cp2.1 L1648_cp2.2 = true := by
  decide +kernel
theorem L1648_fin : (prmOK pL1648 1648 && ptTest pL1648 (runFrom pL1648 (fmask pL1648) (cmask pL1648) (hmask pL1648) 1346 302 (true, L1648_cp2.1, L1648_cp2.2)) 1648 824 false) = true := by
  decide +kernel
theorem L1648_ok : RunOK pL1648 1648 (runFrom pL1648 (fmask pL1648) (cmask pL1648) (hmask pL1648) 1346 302 (true, L1648_cp2.1, L1648_cp2.2)) ∧ ptTest pL1648 (runFrom pL1648 (fmask pL1648) (cmask pL1648) (hmask pL1648) 1346 302 (true, L1648_cp2.1, L1648_cp2.2)) 1648 824 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1648_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1648_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1648_fin) true) L1648_seg1) L1648_seg2) (by decide) rfl L1648_fin ptTest_fst
noncomputable def H1648_cp1 : Nat × Nat := t7val% (fastRun pH1648 1 950 (init pH1648) (init pH1648))
theorem H1648_seg1 : segOK pH1648 1 950 (init pH1648) (init pH1648) H1648_cp1.1 H1648_cp1.2 = true := by
  decide +kernel
noncomputable def H1648_cp2 : Nat × Nat := t7val% (fastRun pH1648 1 1345 (init pH1648) (init pH1648))
theorem H1648_seg2 : segOK pH1648 951 395 H1648_cp1.1 H1648_cp1.2 H1648_cp2.1 H1648_cp2.2 = true := by
  decide +kernel
theorem H1648_fin : (prmOK pH1648 1648 && ptTest pH1648 (runFrom pH1648 (fmask pH1648) (cmask pH1648) (hmask pH1648) 1346 302 (true, H1648_cp2.1, H1648_cp2.2)) 1648 824 true) = true := by
  decide +kernel
theorem H1648_ok : RunOK pH1648 1648 (runFrom pH1648 (fmask pH1648) (cmask pH1648) (hmask pH1648) 1346 302 (true, H1648_cp2.1, H1648_cp2.2)) ∧ ptTest pH1648 (runFrom pH1648 (fmask pH1648) (cmask pH1648) (hmask pH1648) 1346 302 (true, H1648_cp2.1, H1648_cp2.2)) 1648 824 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1648_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1648_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1648_fin) true) H1648_seg1) H1648_seg2) (by decide) rfl H1648_fin ptTest_fst
noncomputable def I1648_cp1 : Nat × Nat := t7val% (fastRun pI1648 1 1164 (init pI1648) (init pI1648))
theorem I1648_seg1 : segOK pI1648 1 1164 (init pI1648) (init pI1648) I1648_cp1.1 I1648_cp1.2 = true := by
  decide +kernel
theorem I1648_fin : (prmOK pI1648 1648 && intTest pI1648 (runFrom pI1648 (fmask pI1648) (cmask pI1648) (hmask pI1648) 1165 483 (true, I1648_cp1.1, I1648_cp1.2)) 1648 21 true) = true := by
  decide +kernel
theorem I1648_ok : RunOK pI1648 1648 (runFrom pI1648 (fmask pI1648) (cmask pI1648) (hmask pI1648) 1165 483 (true, I1648_cp1.1, I1648_cp1.2)) ∧ intTest pI1648 (runFrom pI1648 (fmask pI1648) (cmask pI1648) (hmask pI1648) 1165 483 (true, I1648_cp1.1, I1648_cp1.2)) 1648 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1648_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1648_fin) true) I1648_seg1) (by decide) rfl I1648_fin intTest_fst
theorem link1648 : linkOK pL1648 pH1648 pI1648 = true := by decide +kernel
theorem cvx1648 : ConvexBetweenHumps 1648 :=
  cvx_of L1648_ok H1648_ok I1648_ok link1648 (by decide)
theorem cenlink1648 : cenLinkOK pI1648 1648 = true := by decide +kernel
theorem cen1648 : CenterUniqueMin 1648 ∧ DipHyp 1648 ∧ OnePointHyps 1648 :=
  cen_of L1648_ok H1648_ok I1648_ok link1648 cenlink1648

/-! ### `N = 1649` -/

def pL1649 : Prm := ⟨80, 37, 40, 1651, 11, 18446744073709551616, 115193002377332936, 115193002377332936⟩
def pH1649 : Prm := ⟨80, 37, 40, 1651, 11, 18446744073709551616, 115194101888960712, 115194101888960712⟩
def pI1649 : Prm := ⟨67, 33, 31, 1651, 11, 18446744073709551616, 115193002377332936, 115194101888960712⟩
noncomputable def L1649_cp1 : Nat × Nat := t7val% (fastRun pL1649 1 951 (init pL1649) (init pL1649))
theorem L1649_seg1 : segOK pL1649 1 951 (init pL1649) (init pL1649) L1649_cp1.1 L1649_cp1.2 = true := by
  decide +kernel
noncomputable def L1649_cp2 : Nat × Nat := t7val% (fastRun pL1649 1 1345 (init pL1649) (init pL1649))
theorem L1649_seg2 : segOK pL1649 952 394 L1649_cp1.1 L1649_cp1.2 L1649_cp2.1 L1649_cp2.2 = true := by
  decide +kernel
theorem L1649_fin : (prmOK pL1649 1649 && ptTest pL1649 (runFrom pL1649 (fmask pL1649) (cmask pL1649) (hmask pL1649) 1346 303 (true, L1649_cp2.1, L1649_cp2.2)) 1649 825 false) = true := by
  decide +kernel
theorem L1649_ok : RunOK pL1649 1649 (runFrom pL1649 (fmask pL1649) (cmask pL1649) (hmask pL1649) 1346 303 (true, L1649_cp2.1, L1649_cp2.2)) ∧ ptTest pL1649 (runFrom pL1649 (fmask pL1649) (cmask pL1649) (hmask pL1649) 1346 303 (true, L1649_cp2.1, L1649_cp2.2)) 1649 825 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1649_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1649_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1649_fin) true) L1649_seg1) L1649_seg2) (by decide) rfl L1649_fin ptTest_fst
noncomputable def H1649_cp1 : Nat × Nat := t7val% (fastRun pH1649 1 951 (init pH1649) (init pH1649))
theorem H1649_seg1 : segOK pH1649 1 951 (init pH1649) (init pH1649) H1649_cp1.1 H1649_cp1.2 = true := by
  decide +kernel
noncomputable def H1649_cp2 : Nat × Nat := t7val% (fastRun pH1649 1 1345 (init pH1649) (init pH1649))
theorem H1649_seg2 : segOK pH1649 952 394 H1649_cp1.1 H1649_cp1.2 H1649_cp2.1 H1649_cp2.2 = true := by
  decide +kernel
theorem H1649_fin : (prmOK pH1649 1649 && ptTest pH1649 (runFrom pH1649 (fmask pH1649) (cmask pH1649) (hmask pH1649) 1346 303 (true, H1649_cp2.1, H1649_cp2.2)) 1649 825 true) = true := by
  decide +kernel
theorem H1649_ok : RunOK pH1649 1649 (runFrom pH1649 (fmask pH1649) (cmask pH1649) (hmask pH1649) 1346 303 (true, H1649_cp2.1, H1649_cp2.2)) ∧ ptTest pH1649 (runFrom pH1649 (fmask pH1649) (cmask pH1649) (hmask pH1649) 1346 303 (true, H1649_cp2.1, H1649_cp2.2)) 1649 825 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1649_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1649_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1649_fin) true) H1649_seg1) H1649_seg2) (by decide) rfl H1649_fin ptTest_fst
noncomputable def I1649_cp1 : Nat × Nat := t7val% (fastRun pI1649 1 1165 (init pI1649) (init pI1649))
theorem I1649_seg1 : segOK pI1649 1 1165 (init pI1649) (init pI1649) I1649_cp1.1 I1649_cp1.2 = true := by
  decide +kernel
theorem I1649_fin : (prmOK pI1649 1649 && intTest pI1649 (runFrom pI1649 (fmask pI1649) (cmask pI1649) (hmask pI1649) 1166 483 (true, I1649_cp1.1, I1649_cp1.2)) 1649 21 false) = true := by
  decide +kernel
theorem I1649_ok : RunOK pI1649 1649 (runFrom pI1649 (fmask pI1649) (cmask pI1649) (hmask pI1649) 1166 483 (true, I1649_cp1.1, I1649_cp1.2)) ∧ intTest pI1649 (runFrom pI1649 (fmask pI1649) (cmask pI1649) (hmask pI1649) 1166 483 (true, I1649_cp1.1, I1649_cp1.2)) 1649 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1649_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1649_fin) true) I1649_seg1) (by decide) rfl I1649_fin intTest_fst
theorem link1649 : linkOK pL1649 pH1649 pI1649 = true := by decide +kernel
theorem cvx1649 : ConvexBetweenHumps 1649 :=
  cvx_of L1649_ok H1649_ok I1649_ok link1649 (by decide)

/-! ### `N = 1650` -/

def pL1650 : Prm := ⟨80, 37, 40, 1652, 11, 18446744073709551616, 115135978758206378, 115135978758206378⟩
def pH1650 : Prm := ⟨80, 37, 40, 1652, 11, 18446744073709551616, 115137078269834154, 115137078269834154⟩
def pI1650 : Prm := ⟨67, 33, 31, 1652, 11, 18446744073709551616, 115135978758206378, 115137078269834154⟩
noncomputable def L1650_cp1 : Nat × Nat := t7val% (fastRun pL1650 1 952 (init pL1650) (init pL1650))
theorem L1650_seg1 : segOK pL1650 1 952 (init pL1650) (init pL1650) L1650_cp1.1 L1650_cp1.2 = true := by
  decide +kernel
noncomputable def L1650_cp2 : Nat × Nat := t7val% (fastRun pL1650 1 1346 (init pL1650) (init pL1650))
theorem L1650_seg2 : segOK pL1650 953 394 L1650_cp1.1 L1650_cp1.2 L1650_cp2.1 L1650_cp2.2 = true := by
  decide +kernel
theorem L1650_fin : (prmOK pL1650 1650 && ptTest pL1650 (runFrom pL1650 (fmask pL1650) (cmask pL1650) (hmask pL1650) 1347 303 (true, L1650_cp2.1, L1650_cp2.2)) 1650 825 false) = true := by
  decide +kernel
theorem L1650_ok : RunOK pL1650 1650 (runFrom pL1650 (fmask pL1650) (cmask pL1650) (hmask pL1650) 1347 303 (true, L1650_cp2.1, L1650_cp2.2)) ∧ ptTest pL1650 (runFrom pL1650 (fmask pL1650) (cmask pL1650) (hmask pL1650) 1347 303 (true, L1650_cp2.1, L1650_cp2.2)) 1650 825 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1650_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1650_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1650_fin) true) L1650_seg1) L1650_seg2) (by decide) rfl L1650_fin ptTest_fst
noncomputable def H1650_cp1 : Nat × Nat := t7val% (fastRun pH1650 1 952 (init pH1650) (init pH1650))
theorem H1650_seg1 : segOK pH1650 1 952 (init pH1650) (init pH1650) H1650_cp1.1 H1650_cp1.2 = true := by
  decide +kernel
noncomputable def H1650_cp2 : Nat × Nat := t7val% (fastRun pH1650 1 1346 (init pH1650) (init pH1650))
theorem H1650_seg2 : segOK pH1650 953 394 H1650_cp1.1 H1650_cp1.2 H1650_cp2.1 H1650_cp2.2 = true := by
  decide +kernel
theorem H1650_fin : (prmOK pH1650 1650 && ptTest pH1650 (runFrom pH1650 (fmask pH1650) (cmask pH1650) (hmask pH1650) 1347 303 (true, H1650_cp2.1, H1650_cp2.2)) 1650 825 true) = true := by
  decide +kernel
theorem H1650_ok : RunOK pH1650 1650 (runFrom pH1650 (fmask pH1650) (cmask pH1650) (hmask pH1650) 1347 303 (true, H1650_cp2.1, H1650_cp2.2)) ∧ ptTest pH1650 (runFrom pH1650 (fmask pH1650) (cmask pH1650) (hmask pH1650) 1347 303 (true, H1650_cp2.1, H1650_cp2.2)) 1650 825 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1650_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1650_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1650_fin) true) H1650_seg1) H1650_seg2) (by decide) rfl H1650_fin ptTest_fst
noncomputable def I1650_cp1 : Nat × Nat := t7val% (fastRun pI1650 1 1166 (init pI1650) (init pI1650))
theorem I1650_seg1 : segOK pI1650 1 1166 (init pI1650) (init pI1650) I1650_cp1.1 I1650_cp1.2 = true := by
  decide +kernel
theorem I1650_fin : (prmOK pI1650 1650 && intTest pI1650 (runFrom pI1650 (fmask pI1650) (cmask pI1650) (hmask pI1650) 1167 483 (true, I1650_cp1.1, I1650_cp1.2)) 1650 21 true) = true := by
  decide +kernel
theorem I1650_ok : RunOK pI1650 1650 (runFrom pI1650 (fmask pI1650) (cmask pI1650) (hmask pI1650) 1167 483 (true, I1650_cp1.1, I1650_cp1.2)) ∧ intTest pI1650 (runFrom pI1650 (fmask pI1650) (cmask pI1650) (hmask pI1650) 1167 483 (true, I1650_cp1.1, I1650_cp1.2)) 1650 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1650_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1650_fin) true) I1650_seg1) (by decide) rfl I1650_fin intTest_fst
theorem link1650 : linkOK pL1650 pH1650 pI1650 = true := by decide +kernel
theorem cvx1650 : ConvexBetweenHumps 1650 :=
  cvx_of L1650_ok H1650_ok I1650_ok link1650 (by decide)
theorem cenlink1650 : cenLinkOK pI1650 1650 = true := by decide +kernel
theorem cen1650 : CenterUniqueMin 1650 ∧ DipHyp 1650 ∧ OnePointHyps 1650 :=
  cen_of L1650_ok H1650_ok I1650_ok link1650 cenlink1650

/-! ### `N = 1651` -/

def pL1651 : Prm := ⟨80, 37, 40, 1653, 11, 18446744073709551616, 115078991399752412, 115078991399752412⟩
def pH1651 : Prm := ⟨80, 37, 40, 1653, 11, 18446744073709551616, 115080090911380188, 115080090911380188⟩
def pI1651 : Prm := ⟨67, 33, 31, 1653, 11, 18446744073709551616, 115078991399752412, 115080090911380188⟩
noncomputable def L1651_cp1 : Nat × Nat := t7val% (fastRun pL1651 1 952 (init pL1651) (init pL1651))
theorem L1651_seg1 : segOK pL1651 1 952 (init pL1651) (init pL1651) L1651_cp1.1 L1651_cp1.2 = true := by
  decide +kernel
noncomputable def L1651_cp2 : Nat × Nat := t7val% (fastRun pL1651 1 1347 (init pL1651) (init pL1651))
theorem L1651_seg2 : segOK pL1651 953 395 L1651_cp1.1 L1651_cp1.2 L1651_cp2.1 L1651_cp2.2 = true := by
  decide +kernel
theorem L1651_fin : (prmOK pL1651 1651 && ptTest pL1651 (runFrom pL1651 (fmask pL1651) (cmask pL1651) (hmask pL1651) 1348 303 (true, L1651_cp2.1, L1651_cp2.2)) 1651 826 false) = true := by
  decide +kernel
theorem L1651_ok : RunOK pL1651 1651 (runFrom pL1651 (fmask pL1651) (cmask pL1651) (hmask pL1651) 1348 303 (true, L1651_cp2.1, L1651_cp2.2)) ∧ ptTest pL1651 (runFrom pL1651 (fmask pL1651) (cmask pL1651) (hmask pL1651) 1348 303 (true, L1651_cp2.1, L1651_cp2.2)) 1651 826 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1651_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1651_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1651_fin) true) L1651_seg1) L1651_seg2) (by decide) rfl L1651_fin ptTest_fst
noncomputable def H1651_cp1 : Nat × Nat := t7val% (fastRun pH1651 1 952 (init pH1651) (init pH1651))
theorem H1651_seg1 : segOK pH1651 1 952 (init pH1651) (init pH1651) H1651_cp1.1 H1651_cp1.2 = true := by
  decide +kernel
noncomputable def H1651_cp2 : Nat × Nat := t7val% (fastRun pH1651 1 1347 (init pH1651) (init pH1651))
theorem H1651_seg2 : segOK pH1651 953 395 H1651_cp1.1 H1651_cp1.2 H1651_cp2.1 H1651_cp2.2 = true := by
  decide +kernel
theorem H1651_fin : (prmOK pH1651 1651 && ptTest pH1651 (runFrom pH1651 (fmask pH1651) (cmask pH1651) (hmask pH1651) 1348 303 (true, H1651_cp2.1, H1651_cp2.2)) 1651 826 true) = true := by
  decide +kernel
theorem H1651_ok : RunOK pH1651 1651 (runFrom pH1651 (fmask pH1651) (cmask pH1651) (hmask pH1651) 1348 303 (true, H1651_cp2.1, H1651_cp2.2)) ∧ ptTest pH1651 (runFrom pH1651 (fmask pH1651) (cmask pH1651) (hmask pH1651) 1348 303 (true, H1651_cp2.1, H1651_cp2.2)) 1651 826 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1651_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1651_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1651_fin) true) H1651_seg1) H1651_seg2) (by decide) rfl H1651_fin ptTest_fst
noncomputable def I1651_cp1 : Nat × Nat := t7val% (fastRun pI1651 1 1166 (init pI1651) (init pI1651))
theorem I1651_seg1 : segOK pI1651 1 1166 (init pI1651) (init pI1651) I1651_cp1.1 I1651_cp1.2 = true := by
  decide +kernel
theorem I1651_fin : (prmOK pI1651 1651 && intTest pI1651 (runFrom pI1651 (fmask pI1651) (cmask pI1651) (hmask pI1651) 1167 484 (true, I1651_cp1.1, I1651_cp1.2)) 1651 21 false) = true := by
  decide +kernel
theorem I1651_ok : RunOK pI1651 1651 (runFrom pI1651 (fmask pI1651) (cmask pI1651) (hmask pI1651) 1167 484 (true, I1651_cp1.1, I1651_cp1.2)) ∧ intTest pI1651 (runFrom pI1651 (fmask pI1651) (cmask pI1651) (hmask pI1651) 1167 484 (true, I1651_cp1.1, I1651_cp1.2)) 1651 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1651_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1651_fin) true) I1651_seg1) (by decide) rfl I1651_fin intTest_fst
theorem link1651 : linkOK pL1651 pH1651 pI1651 = true := by decide +kernel
theorem cvx1651 : ConvexBetweenHumps 1651 :=
  cvx_of L1651_ok H1651_ok I1651_ok link1651 (by decide)

/-! ### `N = 1652` -/

def pL1652 : Prm := ⟨80, 37, 40, 1654, 11, 18446744073709551616, 115022090323711795, 115022090323711795⟩
def pH1652 : Prm := ⟨80, 37, 40, 1654, 11, 18446744073709551616, 115023189835339571, 115023189835339571⟩
def pI1652 : Prm := ⟨67, 33, 31, 1654, 11, 18446744073709551616, 115022090323711795, 115023189835339571⟩
noncomputable def L1652_cp1 : Nat × Nat := t7val% (fastRun pL1652 1 953 (init pL1652) (init pL1652))
theorem L1652_seg1 : segOK pL1652 1 953 (init pL1652) (init pL1652) L1652_cp1.1 L1652_cp1.2 = true := by
  decide +kernel
noncomputable def L1652_cp2 : Nat × Nat := t7val% (fastRun pL1652 1 1348 (init pL1652) (init pL1652))
theorem L1652_seg2 : segOK pL1652 954 395 L1652_cp1.1 L1652_cp1.2 L1652_cp2.1 L1652_cp2.2 = true := by
  decide +kernel
theorem L1652_fin : (prmOK pL1652 1652 && ptTest pL1652 (runFrom pL1652 (fmask pL1652) (cmask pL1652) (hmask pL1652) 1349 303 (true, L1652_cp2.1, L1652_cp2.2)) 1652 826 false) = true := by
  decide +kernel
theorem L1652_ok : RunOK pL1652 1652 (runFrom pL1652 (fmask pL1652) (cmask pL1652) (hmask pL1652) 1349 303 (true, L1652_cp2.1, L1652_cp2.2)) ∧ ptTest pL1652 (runFrom pL1652 (fmask pL1652) (cmask pL1652) (hmask pL1652) 1349 303 (true, L1652_cp2.1, L1652_cp2.2)) 1652 826 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1652_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1652_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1652_fin) true) L1652_seg1) L1652_seg2) (by decide) rfl L1652_fin ptTest_fst
noncomputable def H1652_cp1 : Nat × Nat := t7val% (fastRun pH1652 1 953 (init pH1652) (init pH1652))
theorem H1652_seg1 : segOK pH1652 1 953 (init pH1652) (init pH1652) H1652_cp1.1 H1652_cp1.2 = true := by
  decide +kernel
noncomputable def H1652_cp2 : Nat × Nat := t7val% (fastRun pH1652 1 1348 (init pH1652) (init pH1652))
theorem H1652_seg2 : segOK pH1652 954 395 H1652_cp1.1 H1652_cp1.2 H1652_cp2.1 H1652_cp2.2 = true := by
  decide +kernel
theorem H1652_fin : (prmOK pH1652 1652 && ptTest pH1652 (runFrom pH1652 (fmask pH1652) (cmask pH1652) (hmask pH1652) 1349 303 (true, H1652_cp2.1, H1652_cp2.2)) 1652 826 true) = true := by
  decide +kernel
theorem H1652_ok : RunOK pH1652 1652 (runFrom pH1652 (fmask pH1652) (cmask pH1652) (hmask pH1652) 1349 303 (true, H1652_cp2.1, H1652_cp2.2)) ∧ ptTest pH1652 (runFrom pH1652 (fmask pH1652) (cmask pH1652) (hmask pH1652) 1349 303 (true, H1652_cp2.1, H1652_cp2.2)) 1652 826 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1652_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1652_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1652_fin) true) H1652_seg1) H1652_seg2) (by decide) rfl H1652_fin ptTest_fst
noncomputable def I1652_cp1 : Nat × Nat := t7val% (fastRun pI1652 1 1167 (init pI1652) (init pI1652))
theorem I1652_seg1 : segOK pI1652 1 1167 (init pI1652) (init pI1652) I1652_cp1.1 I1652_cp1.2 = true := by
  decide +kernel
theorem I1652_fin : (prmOK pI1652 1652 && intTest pI1652 (runFrom pI1652 (fmask pI1652) (cmask pI1652) (hmask pI1652) 1168 484 (true, I1652_cp1.1, I1652_cp1.2)) 1652 21 true) = true := by
  decide +kernel
theorem I1652_ok : RunOK pI1652 1652 (runFrom pI1652 (fmask pI1652) (cmask pI1652) (hmask pI1652) 1168 484 (true, I1652_cp1.1, I1652_cp1.2)) ∧ intTest pI1652 (runFrom pI1652 (fmask pI1652) (cmask pI1652) (hmask pI1652) 1168 484 (true, I1652_cp1.1, I1652_cp1.2)) 1652 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1652_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1652_fin) true) I1652_seg1) (by decide) rfl I1652_fin intTest_fst
theorem link1652 : linkOK pL1652 pH1652 pI1652 = true := by decide +kernel
theorem cvx1652 : ConvexBetweenHumps 1652 :=
  cvx_of L1652_ok H1652_ok I1652_ok link1652 (by decide)
theorem cenlink1652 : cenLinkOK pI1652 1652 = true := by decide +kernel
theorem cen1652 : CenterUniqueMin 1652 ∧ DipHyp 1652 ∧ OnePointHyps 1652 :=
  cen_of L1652_ok H1652_ok I1652_ok link1652 cenlink1652

/-! ### The range -/

theorem cvx_1639_1652 {N : ℕ} (h1 : 1639 ≤ N) (h2 : N ≤ 1652) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1645
  · by_cases h4 : N ≤ 1641
    · by_cases h6 : N ≤ 1639
      · obtain rfl : N = 1639 := by omega
        exact cvx1639
      · by_cases h8 : N ≤ 1640
        · obtain rfl : N = 1640 := by omega
          exact cvx1640
        · obtain rfl : N = 1641 := by omega
          exact cvx1641
    · by_cases h6 : N ≤ 1643
      · by_cases h8 : N ≤ 1642
        · obtain rfl : N = 1642 := by omega
          exact cvx1642
        · obtain rfl : N = 1643 := by omega
          exact cvx1643
      · by_cases h8 : N ≤ 1644
        · obtain rfl : N = 1644 := by omega
          exact cvx1644
        · obtain rfl : N = 1645 := by omega
          exact cvx1645
  · by_cases h4 : N ≤ 1648
    · by_cases h6 : N ≤ 1646
      · obtain rfl : N = 1646 := by omega
        exact cvx1646
      · by_cases h8 : N ≤ 1647
        · obtain rfl : N = 1647 := by omega
          exact cvx1647
        · obtain rfl : N = 1648 := by omega
          exact cvx1648
    · by_cases h6 : N ≤ 1650
      · by_cases h8 : N ≤ 1649
        · obtain rfl : N = 1649 := by omega
          exact cvx1649
        · obtain rfl : N = 1650 := by omega
          exact cvx1650
      · by_cases h8 : N ≤ 1651
        · obtain rfl : N = 1651 := by omega
          exact cvx1651
        · obtain rfl : N = 1652 := by omega
          exact cvx1652

theorem cen_1639_1652 {N : ℕ} (h1 : 1639 ≤ N) (h2 : N ≤ 1652) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1644
  · by_cases h4 : N ≤ 1640
    · obtain rfl : N = 1640 := by omega
      exact cen1640
    · by_cases h6 : N ≤ 1642
      · obtain rfl : N = 1642 := by omega
        exact cen1642
      · obtain rfl : N = 1644 := by omega
        exact cen1644
  · by_cases h4 : N ≤ 1648
    · by_cases h6 : N ≤ 1646
      · obtain rfl : N = 1646 := by omega
        exact cen1646
      · obtain rfl : N = 1648 := by omega
        exact cen1648
    · by_cases h6 : N ≤ 1650
      · obtain rfl : N = 1650 := by omega
        exact cen1650
      · obtain rfl : N = 1652 := by omega
        exact cen1652

end Kagey131.PaperD.T7
