import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1721, …, 1733` (generated)

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

/-! ### `N = 1721` -/

def pL1721 : Prm := ⟨80, 37, 40, 1723, 11, 18446744073709551616, 111237341173345319, 111237341173345319⟩
def pH1721 : Prm := ⟨80, 37, 40, 1723, 11, 18446744073709551616, 111238440684973095, 111238440684973095⟩
def pI1721 : Prm := ⟨69, 33, 33, 1723, 11, 18446744073709551616, 111237341173345319, 111238440684973095⟩
noncomputable def L1721_cp1 : Nat × Nat := t7val% (fastRun pL1721 1 993 (init pL1721) (init pL1721))
theorem L1721_seg1 : segOK pL1721 1 993 (init pL1721) (init pL1721) L1721_cp1.1 L1721_cp1.2 = true := by
  decide +kernel
noncomputable def L1721_cp2 : Nat × Nat := t7val% (fastRun pL1721 1 1404 (init pL1721) (init pL1721))
theorem L1721_seg2 : segOK pL1721 994 411 L1721_cp1.1 L1721_cp1.2 L1721_cp2.1 L1721_cp2.2 = true := by
  decide +kernel
theorem L1721_fin : (prmOK pL1721 1721 && ptTest pL1721 (runFrom pL1721 (fmask pL1721) (cmask pL1721) (hmask pL1721) 1405 316 (true, L1721_cp2.1, L1721_cp2.2)) 1721 861 false) = true := by
  decide +kernel
theorem L1721_ok : RunOK pL1721 1721 (runFrom pL1721 (fmask pL1721) (cmask pL1721) (hmask pL1721) 1405 316 (true, L1721_cp2.1, L1721_cp2.2)) ∧ ptTest pL1721 (runFrom pL1721 (fmask pL1721) (cmask pL1721) (hmask pL1721) 1405 316 (true, L1721_cp2.1, L1721_cp2.2)) 1721 861 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1721_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1721_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1721_fin) true) L1721_seg1) L1721_seg2) (by decide) rfl L1721_fin ptTest_fst
noncomputable def H1721_cp1 : Nat × Nat := t7val% (fastRun pH1721 1 993 (init pH1721) (init pH1721))
theorem H1721_seg1 : segOK pH1721 1 993 (init pH1721) (init pH1721) H1721_cp1.1 H1721_cp1.2 = true := by
  decide +kernel
noncomputable def H1721_cp2 : Nat × Nat := t7val% (fastRun pH1721 1 1404 (init pH1721) (init pH1721))
theorem H1721_seg2 : segOK pH1721 994 411 H1721_cp1.1 H1721_cp1.2 H1721_cp2.1 H1721_cp2.2 = true := by
  decide +kernel
theorem H1721_fin : (prmOK pH1721 1721 && ptTest pH1721 (runFrom pH1721 (fmask pH1721) (cmask pH1721) (hmask pH1721) 1405 316 (true, H1721_cp2.1, H1721_cp2.2)) 1721 861 true) = true := by
  decide +kernel
theorem H1721_ok : RunOK pH1721 1721 (runFrom pH1721 (fmask pH1721) (cmask pH1721) (hmask pH1721) 1405 316 (true, H1721_cp2.1, H1721_cp2.2)) ∧ ptTest pH1721 (runFrom pH1721 (fmask pH1721) (cmask pH1721) (hmask pH1721) 1405 316 (true, H1721_cp2.1, H1721_cp2.2)) 1721 861 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1721_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1721_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1721_fin) true) H1721_seg1) H1721_seg2) (by decide) rfl H1721_fin ptTest_fst
noncomputable def I1721_cp1 : Nat × Nat := t7val% (fastRun pI1721 1 1216 (init pI1721) (init pI1721))
theorem I1721_seg1 : segOK pI1721 1 1216 (init pI1721) (init pI1721) I1721_cp1.1 I1721_cp1.2 = true := by
  decide +kernel
theorem I1721_fin : (prmOK pI1721 1721 && intTest pI1721 (runFrom pI1721 (fmask pI1721) (cmask pI1721) (hmask pI1721) 1217 504 (true, I1721_cp1.1, I1721_cp1.2)) 1721 21 false) = true := by
  decide +kernel
theorem I1721_ok : RunOK pI1721 1721 (runFrom pI1721 (fmask pI1721) (cmask pI1721) (hmask pI1721) 1217 504 (true, I1721_cp1.1, I1721_cp1.2)) ∧ intTest pI1721 (runFrom pI1721 (fmask pI1721) (cmask pI1721) (hmask pI1721) 1217 504 (true, I1721_cp1.1, I1721_cp1.2)) 1721 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1721_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1721_fin) true) I1721_seg1) (by decide) rfl I1721_fin intTest_fst
theorem link1721 : linkOK pL1721 pH1721 pI1721 = true := by decide +kernel
theorem cvx1721 : ConvexBetweenHumps 1721 :=
  cvx_of L1721_ok H1721_ok I1721_ok link1721 (by decide)

/-! ### `N = 1722` -/

def pL1722 : Prm := ⟨80, 37, 40, 1724, 11, 18446744073709551616, 111184485203698416, 111184485203698416⟩
def pH1722 : Prm := ⟨80, 37, 40, 1724, 11, 18446744073709551616, 111185584715326192, 111185584715326192⟩
def pI1722 : Prm := ⟨68, 33, 32, 1724, 11, 18446744073709551616, 111184485203698416, 111185584715326192⟩
noncomputable def L1722_cp1 : Nat × Nat := t7val% (fastRun pL1722 1 993 (init pL1722) (init pL1722))
theorem L1722_seg1 : segOK pL1722 1 993 (init pL1722) (init pL1722) L1722_cp1.1 L1722_cp1.2 = true := by
  decide +kernel
noncomputable def L1722_cp2 : Nat × Nat := t7val% (fastRun pL1722 1 1405 (init pL1722) (init pL1722))
theorem L1722_seg2 : segOK pL1722 994 412 L1722_cp1.1 L1722_cp1.2 L1722_cp2.1 L1722_cp2.2 = true := by
  decide +kernel
theorem L1722_fin : (prmOK pL1722 1722 && ptTest pL1722 (runFrom pL1722 (fmask pL1722) (cmask pL1722) (hmask pL1722) 1406 316 (true, L1722_cp2.1, L1722_cp2.2)) 1722 861 false) = true := by
  decide +kernel
theorem L1722_ok : RunOK pL1722 1722 (runFrom pL1722 (fmask pL1722) (cmask pL1722) (hmask pL1722) 1406 316 (true, L1722_cp2.1, L1722_cp2.2)) ∧ ptTest pL1722 (runFrom pL1722 (fmask pL1722) (cmask pL1722) (hmask pL1722) 1406 316 (true, L1722_cp2.1, L1722_cp2.2)) 1722 861 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1722_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1722_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1722_fin) true) L1722_seg1) L1722_seg2) (by decide) rfl L1722_fin ptTest_fst
noncomputable def H1722_cp1 : Nat × Nat := t7val% (fastRun pH1722 1 993 (init pH1722) (init pH1722))
theorem H1722_seg1 : segOK pH1722 1 993 (init pH1722) (init pH1722) H1722_cp1.1 H1722_cp1.2 = true := by
  decide +kernel
noncomputable def H1722_cp2 : Nat × Nat := t7val% (fastRun pH1722 1 1405 (init pH1722) (init pH1722))
theorem H1722_seg2 : segOK pH1722 994 412 H1722_cp1.1 H1722_cp1.2 H1722_cp2.1 H1722_cp2.2 = true := by
  decide +kernel
theorem H1722_fin : (prmOK pH1722 1722 && ptTest pH1722 (runFrom pH1722 (fmask pH1722) (cmask pH1722) (hmask pH1722) 1406 316 (true, H1722_cp2.1, H1722_cp2.2)) 1722 861 true) = true := by
  decide +kernel
theorem H1722_ok : RunOK pH1722 1722 (runFrom pH1722 (fmask pH1722) (cmask pH1722) (hmask pH1722) 1406 316 (true, H1722_cp2.1, H1722_cp2.2)) ∧ ptTest pH1722 (runFrom pH1722 (fmask pH1722) (cmask pH1722) (hmask pH1722) 1406 316 (true, H1722_cp2.1, H1722_cp2.2)) 1722 861 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1722_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1722_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1722_fin) true) H1722_seg1) H1722_seg2) (by decide) rfl H1722_fin ptTest_fst
noncomputable def I1722_cp1 : Nat × Nat := t7val% (fastRun pI1722 1 1217 (init pI1722) (init pI1722))
theorem I1722_seg1 : segOK pI1722 1 1217 (init pI1722) (init pI1722) I1722_cp1.1 I1722_cp1.2 = true := by
  decide +kernel
theorem I1722_fin : (prmOK pI1722 1722 && intTest pI1722 (runFrom pI1722 (fmask pI1722) (cmask pI1722) (hmask pI1722) 1218 504 (true, I1722_cp1.1, I1722_cp1.2)) 1722 21 true) = true := by
  decide +kernel
theorem I1722_ok : RunOK pI1722 1722 (runFrom pI1722 (fmask pI1722) (cmask pI1722) (hmask pI1722) 1218 504 (true, I1722_cp1.1, I1722_cp1.2)) ∧ intTest pI1722 (runFrom pI1722 (fmask pI1722) (cmask pI1722) (hmask pI1722) 1218 504 (true, I1722_cp1.1, I1722_cp1.2)) 1722 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1722_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1722_fin) true) I1722_seg1) (by decide) rfl I1722_fin intTest_fst
theorem link1722 : linkOK pL1722 pH1722 pI1722 = true := by decide +kernel
theorem cvx1722 : ConvexBetweenHumps 1722 :=
  cvx_of L1722_ok H1722_ok I1722_ok link1722 (by decide)
theorem cenlink1722 : cenLinkOK pI1722 1722 = true := by decide +kernel
theorem cen1722 : CenterUniqueMin 1722 ∧ DipHyp 1722 ∧ OnePointHyps 1722 :=
  cen_of L1722_ok H1722_ok I1722_ok link1722 cenlink1722

/-! ### `N = 1723` -/

def pL1723 : Prm := ⟨80, 37, 40, 1725, 11, 18446744073709551616, 111131661760346788, 111131661760346788⟩
def pH1723 : Prm := ⟨80, 37, 40, 1725, 11, 18446744073709551616, 111132761271974564, 111132761271974564⟩
def pI1723 : Prm := ⟨69, 33, 33, 1725, 11, 18446744073709551616, 111131661760346788, 111132761271974564⟩
noncomputable def L1723_cp1 : Nat × Nat := t7val% (fastRun pL1723 1 994 (init pL1723) (init pL1723))
theorem L1723_seg1 : segOK pL1723 1 994 (init pL1723) (init pL1723) L1723_cp1.1 L1723_cp1.2 = true := by
  decide +kernel
noncomputable def L1723_cp2 : Nat × Nat := t7val% (fastRun pL1723 1 1406 (init pL1723) (init pL1723))
theorem L1723_seg2 : segOK pL1723 995 412 L1723_cp1.1 L1723_cp1.2 L1723_cp2.1 L1723_cp2.2 = true := by
  decide +kernel
theorem L1723_fin : (prmOK pL1723 1723 && ptTest pL1723 (runFrom pL1723 (fmask pL1723) (cmask pL1723) (hmask pL1723) 1407 316 (true, L1723_cp2.1, L1723_cp2.2)) 1723 862 false) = true := by
  decide +kernel
theorem L1723_ok : RunOK pL1723 1723 (runFrom pL1723 (fmask pL1723) (cmask pL1723) (hmask pL1723) 1407 316 (true, L1723_cp2.1, L1723_cp2.2)) ∧ ptTest pL1723 (runFrom pL1723 (fmask pL1723) (cmask pL1723) (hmask pL1723) 1407 316 (true, L1723_cp2.1, L1723_cp2.2)) 1723 862 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1723_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1723_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1723_fin) true) L1723_seg1) L1723_seg2) (by decide) rfl L1723_fin ptTest_fst
noncomputable def H1723_cp1 : Nat × Nat := t7val% (fastRun pH1723 1 994 (init pH1723) (init pH1723))
theorem H1723_seg1 : segOK pH1723 1 994 (init pH1723) (init pH1723) H1723_cp1.1 H1723_cp1.2 = true := by
  decide +kernel
noncomputable def H1723_cp2 : Nat × Nat := t7val% (fastRun pH1723 1 1406 (init pH1723) (init pH1723))
theorem H1723_seg2 : segOK pH1723 995 412 H1723_cp1.1 H1723_cp1.2 H1723_cp2.1 H1723_cp2.2 = true := by
  decide +kernel
theorem H1723_fin : (prmOK pH1723 1723 && ptTest pH1723 (runFrom pH1723 (fmask pH1723) (cmask pH1723) (hmask pH1723) 1407 316 (true, H1723_cp2.1, H1723_cp2.2)) 1723 862 true) = true := by
  decide +kernel
theorem H1723_ok : RunOK pH1723 1723 (runFrom pH1723 (fmask pH1723) (cmask pH1723) (hmask pH1723) 1407 316 (true, H1723_cp2.1, H1723_cp2.2)) ∧ ptTest pH1723 (runFrom pH1723 (fmask pH1723) (cmask pH1723) (hmask pH1723) 1407 316 (true, H1723_cp2.1, H1723_cp2.2)) 1723 862 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1723_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1723_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1723_fin) true) H1723_seg1) H1723_seg2) (by decide) rfl H1723_fin ptTest_fst
noncomputable def I1723_cp1 : Nat × Nat := t7val% (fastRun pI1723 1 1217 (init pI1723) (init pI1723))
theorem I1723_seg1 : segOK pI1723 1 1217 (init pI1723) (init pI1723) I1723_cp1.1 I1723_cp1.2 = true := by
  decide +kernel
theorem I1723_fin : (prmOK pI1723 1723 && intTest pI1723 (runFrom pI1723 (fmask pI1723) (cmask pI1723) (hmask pI1723) 1218 505 (true, I1723_cp1.1, I1723_cp1.2)) 1723 21 false) = true := by
  decide +kernel
theorem I1723_ok : RunOK pI1723 1723 (runFrom pI1723 (fmask pI1723) (cmask pI1723) (hmask pI1723) 1218 505 (true, I1723_cp1.1, I1723_cp1.2)) ∧ intTest pI1723 (runFrom pI1723 (fmask pI1723) (cmask pI1723) (hmask pI1723) 1218 505 (true, I1723_cp1.1, I1723_cp1.2)) 1723 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1723_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1723_fin) true) I1723_seg1) (by decide) rfl I1723_fin intTest_fst
theorem link1723 : linkOK pL1723 pH1723 pI1723 = true := by decide +kernel
theorem cvx1723 : ConvexBetweenHumps 1723 :=
  cvx_of L1723_ok H1723_ok I1723_ok link1723 (by decide)

/-! ### `N = 1724` -/

def pL1724 : Prm := ⟨80, 37, 40, 1726, 11, 18446744073709551616, 111078914766131773, 111078914766131773⟩
def pH1724 : Prm := ⟨80, 37, 40, 1726, 11, 18446744073709551616, 111080014277759549, 111080014277759549⟩
def pI1724 : Prm := ⟨69, 33, 33, 1726, 11, 18446744073709551616, 111078914766131773, 111080014277759549⟩
noncomputable def L1724_cp1 : Nat × Nat := t7val% (fastRun pL1724 1 994 (init pL1724) (init pL1724))
theorem L1724_seg1 : segOK pL1724 1 994 (init pL1724) (init pL1724) L1724_cp1.1 L1724_cp1.2 = true := by
  decide +kernel
noncomputable def L1724_cp2 : Nat × Nat := t7val% (fastRun pL1724 1 1407 (init pL1724) (init pL1724))
theorem L1724_seg2 : segOK pL1724 995 413 L1724_cp1.1 L1724_cp1.2 L1724_cp2.1 L1724_cp2.2 = true := by
  decide +kernel
theorem L1724_fin : (prmOK pL1724 1724 && ptTest pL1724 (runFrom pL1724 (fmask pL1724) (cmask pL1724) (hmask pL1724) 1408 316 (true, L1724_cp2.1, L1724_cp2.2)) 1724 862 false) = true := by
  decide +kernel
theorem L1724_ok : RunOK pL1724 1724 (runFrom pL1724 (fmask pL1724) (cmask pL1724) (hmask pL1724) 1408 316 (true, L1724_cp2.1, L1724_cp2.2)) ∧ ptTest pL1724 (runFrom pL1724 (fmask pL1724) (cmask pL1724) (hmask pL1724) 1408 316 (true, L1724_cp2.1, L1724_cp2.2)) 1724 862 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1724_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1724_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1724_fin) true) L1724_seg1) L1724_seg2) (by decide) rfl L1724_fin ptTest_fst
noncomputable def H1724_cp1 : Nat × Nat := t7val% (fastRun pH1724 1 994 (init pH1724) (init pH1724))
theorem H1724_seg1 : segOK pH1724 1 994 (init pH1724) (init pH1724) H1724_cp1.1 H1724_cp1.2 = true := by
  decide +kernel
noncomputable def H1724_cp2 : Nat × Nat := t7val% (fastRun pH1724 1 1407 (init pH1724) (init pH1724))
theorem H1724_seg2 : segOK pH1724 995 413 H1724_cp1.1 H1724_cp1.2 H1724_cp2.1 H1724_cp2.2 = true := by
  decide +kernel
theorem H1724_fin : (prmOK pH1724 1724 && ptTest pH1724 (runFrom pH1724 (fmask pH1724) (cmask pH1724) (hmask pH1724) 1408 316 (true, H1724_cp2.1, H1724_cp2.2)) 1724 862 true) = true := by
  decide +kernel
theorem H1724_ok : RunOK pH1724 1724 (runFrom pH1724 (fmask pH1724) (cmask pH1724) (hmask pH1724) 1408 316 (true, H1724_cp2.1, H1724_cp2.2)) ∧ ptTest pH1724 (runFrom pH1724 (fmask pH1724) (cmask pH1724) (hmask pH1724) 1408 316 (true, H1724_cp2.1, H1724_cp2.2)) 1724 862 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1724_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1724_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1724_fin) true) H1724_seg1) H1724_seg2) (by decide) rfl H1724_fin ptTest_fst
noncomputable def I1724_cp1 : Nat × Nat := t7val% (fastRun pI1724 1 1218 (init pI1724) (init pI1724))
theorem I1724_seg1 : segOK pI1724 1 1218 (init pI1724) (init pI1724) I1724_cp1.1 I1724_cp1.2 = true := by
  decide +kernel
theorem I1724_fin : (prmOK pI1724 1724 && intTest pI1724 (runFrom pI1724 (fmask pI1724) (cmask pI1724) (hmask pI1724) 1219 505 (true, I1724_cp1.1, I1724_cp1.2)) 1724 21 true) = true := by
  decide +kernel
theorem I1724_ok : RunOK pI1724 1724 (runFrom pI1724 (fmask pI1724) (cmask pI1724) (hmask pI1724) 1219 505 (true, I1724_cp1.1, I1724_cp1.2)) ∧ intTest pI1724 (runFrom pI1724 (fmask pI1724) (cmask pI1724) (hmask pI1724) 1219 505 (true, I1724_cp1.1, I1724_cp1.2)) 1724 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1724_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1724_fin) true) I1724_seg1) (by decide) rfl I1724_fin intTest_fst
theorem link1724 : linkOK pL1724 pH1724 pI1724 = true := by decide +kernel
theorem cvx1724 : ConvexBetweenHumps 1724 :=
  cvx_of L1724_ok H1724_ok I1724_ok link1724 (by decide)
theorem cenlink1724 : cenLinkOK pI1724 1724 = true := by decide +kernel
theorem cen1724 : CenterUniqueMin 1724 ∧ DipHyp 1724 ∧ OnePointHyps 1724 :=
  cen_of L1724_ok H1724_ok I1724_ok link1724 cenlink1724

/-! ### `N = 1725` -/

def pL1725 : Prm := ⟨80, 37, 40, 1727, 11, 18446744073709551616, 111026200202104496, 111026200202104496⟩
def pH1725 : Prm := ⟨80, 37, 40, 1727, 11, 18446744073709551616, 111027299713732272, 111027299713732272⟩
def pI1725 : Prm := ⟨68, 33, 32, 1727, 11, 18446744073709551616, 111026200202104496, 111027299713732272⟩
noncomputable def L1725_cp1 : Nat × Nat := t7val% (fastRun pL1725 1 995 (init pL1725) (init pL1725))
theorem L1725_seg1 : segOK pL1725 1 995 (init pL1725) (init pL1725) L1725_cp1.1 L1725_cp1.2 = true := by
  decide +kernel
noncomputable def L1725_cp2 : Nat × Nat := t7val% (fastRun pL1725 1 1407 (init pL1725) (init pL1725))
theorem L1725_seg2 : segOK pL1725 996 412 L1725_cp1.1 L1725_cp1.2 L1725_cp2.1 L1725_cp2.2 = true := by
  decide +kernel
theorem L1725_fin : (prmOK pL1725 1725 && ptTest pL1725 (runFrom pL1725 (fmask pL1725) (cmask pL1725) (hmask pL1725) 1408 317 (true, L1725_cp2.1, L1725_cp2.2)) 1725 863 false) = true := by
  decide +kernel
theorem L1725_ok : RunOK pL1725 1725 (runFrom pL1725 (fmask pL1725) (cmask pL1725) (hmask pL1725) 1408 317 (true, L1725_cp2.1, L1725_cp2.2)) ∧ ptTest pL1725 (runFrom pL1725 (fmask pL1725) (cmask pL1725) (hmask pL1725) 1408 317 (true, L1725_cp2.1, L1725_cp2.2)) 1725 863 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1725_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1725_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1725_fin) true) L1725_seg1) L1725_seg2) (by decide) rfl L1725_fin ptTest_fst
noncomputable def H1725_cp1 : Nat × Nat := t7val% (fastRun pH1725 1 995 (init pH1725) (init pH1725))
theorem H1725_seg1 : segOK pH1725 1 995 (init pH1725) (init pH1725) H1725_cp1.1 H1725_cp1.2 = true := by
  decide +kernel
noncomputable def H1725_cp2 : Nat × Nat := t7val% (fastRun pH1725 1 1407 (init pH1725) (init pH1725))
theorem H1725_seg2 : segOK pH1725 996 412 H1725_cp1.1 H1725_cp1.2 H1725_cp2.1 H1725_cp2.2 = true := by
  decide +kernel
theorem H1725_fin : (prmOK pH1725 1725 && ptTest pH1725 (runFrom pH1725 (fmask pH1725) (cmask pH1725) (hmask pH1725) 1408 317 (true, H1725_cp2.1, H1725_cp2.2)) 1725 863 true) = true := by
  decide +kernel
theorem H1725_ok : RunOK pH1725 1725 (runFrom pH1725 (fmask pH1725) (cmask pH1725) (hmask pH1725) 1408 317 (true, H1725_cp2.1, H1725_cp2.2)) ∧ ptTest pH1725 (runFrom pH1725 (fmask pH1725) (cmask pH1725) (hmask pH1725) 1408 317 (true, H1725_cp2.1, H1725_cp2.2)) 1725 863 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1725_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1725_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1725_fin) true) H1725_seg1) H1725_seg2) (by decide) rfl H1725_fin ptTest_fst
noncomputable def I1725_cp1 : Nat × Nat := t7val% (fastRun pI1725 1 1219 (init pI1725) (init pI1725))
theorem I1725_seg1 : segOK pI1725 1 1219 (init pI1725) (init pI1725) I1725_cp1.1 I1725_cp1.2 = true := by
  decide +kernel
theorem I1725_fin : (prmOK pI1725 1725 && intTest pI1725 (runFrom pI1725 (fmask pI1725) (cmask pI1725) (hmask pI1725) 1220 505 (true, I1725_cp1.1, I1725_cp1.2)) 1725 21 false) = true := by
  decide +kernel
theorem I1725_ok : RunOK pI1725 1725 (runFrom pI1725 (fmask pI1725) (cmask pI1725) (hmask pI1725) 1220 505 (true, I1725_cp1.1, I1725_cp1.2)) ∧ intTest pI1725 (runFrom pI1725 (fmask pI1725) (cmask pI1725) (hmask pI1725) 1220 505 (true, I1725_cp1.1, I1725_cp1.2)) 1725 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1725_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1725_fin) true) I1725_seg1) (by decide) rfl I1725_fin intTest_fst
theorem link1725 : linkOK pL1725 pH1725 pI1725 = true := by decide +kernel
theorem cvx1725 : ConvexBetweenHumps 1725 :=
  cvx_of L1725_ok H1725_ok I1725_ok link1725 (by decide)

/-! ### `N = 1726` -/

def pL1726 : Prm := ⟨80, 37, 40, 1728, 11, 18446744073709551616, 110973561836172091, 110973561836172091⟩
def pH1726 : Prm := ⟨80, 37, 40, 1728, 11, 18446744073709551616, 110974661347799867, 110974661347799867⟩
def pI1726 : Prm := ⟨69, 33, 33, 1728, 11, 18446744073709551616, 110973561836172091, 110974661347799867⟩
noncomputable def L1726_cp1 : Nat × Nat := t7val% (fastRun pL1726 1 996 (init pL1726) (init pL1726))
theorem L1726_seg1 : segOK pL1726 1 996 (init pL1726) (init pL1726) L1726_cp1.1 L1726_cp1.2 = true := by
  decide +kernel
noncomputable def L1726_cp2 : Nat × Nat := t7val% (fastRun pL1726 1 1408 (init pL1726) (init pL1726))
theorem L1726_seg2 : segOK pL1726 997 412 L1726_cp1.1 L1726_cp1.2 L1726_cp2.1 L1726_cp2.2 = true := by
  decide +kernel
theorem L1726_fin : (prmOK pL1726 1726 && ptTest pL1726 (runFrom pL1726 (fmask pL1726) (cmask pL1726) (hmask pL1726) 1409 317 (true, L1726_cp2.1, L1726_cp2.2)) 1726 863 false) = true := by
  decide +kernel
theorem L1726_ok : RunOK pL1726 1726 (runFrom pL1726 (fmask pL1726) (cmask pL1726) (hmask pL1726) 1409 317 (true, L1726_cp2.1, L1726_cp2.2)) ∧ ptTest pL1726 (runFrom pL1726 (fmask pL1726) (cmask pL1726) (hmask pL1726) 1409 317 (true, L1726_cp2.1, L1726_cp2.2)) 1726 863 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1726_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1726_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1726_fin) true) L1726_seg1) L1726_seg2) (by decide) rfl L1726_fin ptTest_fst
noncomputable def H1726_cp1 : Nat × Nat := t7val% (fastRun pH1726 1 996 (init pH1726) (init pH1726))
theorem H1726_seg1 : segOK pH1726 1 996 (init pH1726) (init pH1726) H1726_cp1.1 H1726_cp1.2 = true := by
  decide +kernel
noncomputable def H1726_cp2 : Nat × Nat := t7val% (fastRun pH1726 1 1408 (init pH1726) (init pH1726))
theorem H1726_seg2 : segOK pH1726 997 412 H1726_cp1.1 H1726_cp1.2 H1726_cp2.1 H1726_cp2.2 = true := by
  decide +kernel
theorem H1726_fin : (prmOK pH1726 1726 && ptTest pH1726 (runFrom pH1726 (fmask pH1726) (cmask pH1726) (hmask pH1726) 1409 317 (true, H1726_cp2.1, H1726_cp2.2)) 1726 863 true) = true := by
  decide +kernel
theorem H1726_ok : RunOK pH1726 1726 (runFrom pH1726 (fmask pH1726) (cmask pH1726) (hmask pH1726) 1409 317 (true, H1726_cp2.1, H1726_cp2.2)) ∧ ptTest pH1726 (runFrom pH1726 (fmask pH1726) (cmask pH1726) (hmask pH1726) 1409 317 (true, H1726_cp2.1, H1726_cp2.2)) 1726 863 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1726_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1726_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1726_fin) true) H1726_seg1) H1726_seg2) (by decide) rfl H1726_fin ptTest_fst
noncomputable def I1726_cp1 : Nat × Nat := t7val% (fastRun pI1726 1 1219 (init pI1726) (init pI1726))
theorem I1726_seg1 : segOK pI1726 1 1219 (init pI1726) (init pI1726) I1726_cp1.1 I1726_cp1.2 = true := by
  decide +kernel
theorem I1726_fin : (prmOK pI1726 1726 && intTest pI1726 (runFrom pI1726 (fmask pI1726) (cmask pI1726) (hmask pI1726) 1220 506 (true, I1726_cp1.1, I1726_cp1.2)) 1726 21 true) = true := by
  decide +kernel
theorem I1726_ok : RunOK pI1726 1726 (runFrom pI1726 (fmask pI1726) (cmask pI1726) (hmask pI1726) 1220 506 (true, I1726_cp1.1, I1726_cp1.2)) ∧ intTest pI1726 (runFrom pI1726 (fmask pI1726) (cmask pI1726) (hmask pI1726) 1220 506 (true, I1726_cp1.1, I1726_cp1.2)) 1726 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1726_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1726_fin) true) I1726_seg1) (by decide) rfl I1726_fin intTest_fst
theorem link1726 : linkOK pL1726 pH1726 pI1726 = true := by decide +kernel
theorem cvx1726 : ConvexBetweenHumps 1726 :=
  cvx_of L1726_ok H1726_ok I1726_ok link1726 (by decide)
theorem cenlink1726 : cenLinkOK pI1726 1726 = true := by decide +kernel
theorem cen1726 : CenterUniqueMin 1726 ∧ DipHyp 1726 ∧ OnePointHyps 1726 :=
  cen_of L1726_ok H1726_ok I1726_ok link1726 cenlink1726

/-! ### `N = 1727` -/

def pL1727 : Prm := ⟨80, 37, 40, 1729, 11, 18446744073709551616, 110920955804725717, 110920955804725717⟩
def pH1727 : Prm := ⟨80, 37, 40, 1729, 11, 18446744073709551616, 110922055316353493, 110922055316353493⟩
def pI1727 : Prm := ⟨69, 33, 33, 1729, 11, 18446744073709551616, 110920955804725717, 110922055316353493⟩
noncomputable def L1727_cp1 : Nat × Nat := t7val% (fastRun pL1727 1 996 (init pL1727) (init pL1727))
theorem L1727_seg1 : segOK pL1727 1 996 (init pL1727) (init pL1727) L1727_cp1.1 L1727_cp1.2 = true := by
  decide +kernel
noncomputable def L1727_cp2 : Nat × Nat := t7val% (fastRun pL1727 1 1409 (init pL1727) (init pL1727))
theorem L1727_seg2 : segOK pL1727 997 413 L1727_cp1.1 L1727_cp1.2 L1727_cp2.1 L1727_cp2.2 = true := by
  decide +kernel
theorem L1727_fin : (prmOK pL1727 1727 && ptTest pL1727 (runFrom pL1727 (fmask pL1727) (cmask pL1727) (hmask pL1727) 1410 317 (true, L1727_cp2.1, L1727_cp2.2)) 1727 864 false) = true := by
  decide +kernel
theorem L1727_ok : RunOK pL1727 1727 (runFrom pL1727 (fmask pL1727) (cmask pL1727) (hmask pL1727) 1410 317 (true, L1727_cp2.1, L1727_cp2.2)) ∧ ptTest pL1727 (runFrom pL1727 (fmask pL1727) (cmask pL1727) (hmask pL1727) 1410 317 (true, L1727_cp2.1, L1727_cp2.2)) 1727 864 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1727_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1727_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1727_fin) true) L1727_seg1) L1727_seg2) (by decide) rfl L1727_fin ptTest_fst
noncomputable def H1727_cp1 : Nat × Nat := t7val% (fastRun pH1727 1 996 (init pH1727) (init pH1727))
theorem H1727_seg1 : segOK pH1727 1 996 (init pH1727) (init pH1727) H1727_cp1.1 H1727_cp1.2 = true := by
  decide +kernel
noncomputable def H1727_cp2 : Nat × Nat := t7val% (fastRun pH1727 1 1409 (init pH1727) (init pH1727))
theorem H1727_seg2 : segOK pH1727 997 413 H1727_cp1.1 H1727_cp1.2 H1727_cp2.1 H1727_cp2.2 = true := by
  decide +kernel
theorem H1727_fin : (prmOK pH1727 1727 && ptTest pH1727 (runFrom pH1727 (fmask pH1727) (cmask pH1727) (hmask pH1727) 1410 317 (true, H1727_cp2.1, H1727_cp2.2)) 1727 864 true) = true := by
  decide +kernel
theorem H1727_ok : RunOK pH1727 1727 (runFrom pH1727 (fmask pH1727) (cmask pH1727) (hmask pH1727) 1410 317 (true, H1727_cp2.1, H1727_cp2.2)) ∧ ptTest pH1727 (runFrom pH1727 (fmask pH1727) (cmask pH1727) (hmask pH1727) 1410 317 (true, H1727_cp2.1, H1727_cp2.2)) 1727 864 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1727_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1727_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1727_fin) true) H1727_seg1) H1727_seg2) (by decide) rfl H1727_fin ptTest_fst
noncomputable def I1727_cp1 : Nat × Nat := t7val% (fastRun pI1727 1 1220 (init pI1727) (init pI1727))
theorem I1727_seg1 : segOK pI1727 1 1220 (init pI1727) (init pI1727) I1727_cp1.1 I1727_cp1.2 = true := by
  decide +kernel
theorem I1727_fin : (prmOK pI1727 1727 && intTest pI1727 (runFrom pI1727 (fmask pI1727) (cmask pI1727) (hmask pI1727) 1221 506 (true, I1727_cp1.1, I1727_cp1.2)) 1727 21 false) = true := by
  decide +kernel
theorem I1727_ok : RunOK pI1727 1727 (runFrom pI1727 (fmask pI1727) (cmask pI1727) (hmask pI1727) 1221 506 (true, I1727_cp1.1, I1727_cp1.2)) ∧ intTest pI1727 (runFrom pI1727 (fmask pI1727) (cmask pI1727) (hmask pI1727) 1221 506 (true, I1727_cp1.1, I1727_cp1.2)) 1727 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1727_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1727_fin) true) I1727_seg1) (by decide) rfl I1727_fin intTest_fst
theorem link1727 : linkOK pL1727 pH1727 pI1727 = true := by decide +kernel
theorem cvx1727 : ConvexBetweenHumps 1727 :=
  cvx_of L1727_ok H1727_ok I1727_ok link1727 (by decide)

/-! ### `N = 1728` -/

def pL1728 : Prm := ⟨80, 37, 40, 1730, 11, 18446744073709551616, 110868425721457726, 110868425721457726⟩
def pH1728 : Prm := ⟨80, 37, 40, 1730, 11, 18446744073709551616, 110869525233085502, 110869525233085502⟩
def pI1728 : Prm := ⟨69, 33, 33, 1730, 11, 18446744073709551616, 110868425721457726, 110869525233085502⟩
noncomputable def L1728_cp1 : Nat × Nat := t7val% (fastRun pL1728 1 997 (init pL1728) (init pL1728))
theorem L1728_seg1 : segOK pL1728 1 997 (init pL1728) (init pL1728) L1728_cp1.1 L1728_cp1.2 = true := by
  decide +kernel
noncomputable def L1728_cp2 : Nat × Nat := t7val% (fastRun pL1728 1 1410 (init pL1728) (init pL1728))
theorem L1728_seg2 : segOK pL1728 998 413 L1728_cp1.1 L1728_cp1.2 L1728_cp2.1 L1728_cp2.2 = true := by
  decide +kernel
theorem L1728_fin : (prmOK pL1728 1728 && ptTest pL1728 (runFrom pL1728 (fmask pL1728) (cmask pL1728) (hmask pL1728) 1411 317 (true, L1728_cp2.1, L1728_cp2.2)) 1728 864 false) = true := by
  decide +kernel
theorem L1728_ok : RunOK pL1728 1728 (runFrom pL1728 (fmask pL1728) (cmask pL1728) (hmask pL1728) 1411 317 (true, L1728_cp2.1, L1728_cp2.2)) ∧ ptTest pL1728 (runFrom pL1728 (fmask pL1728) (cmask pL1728) (hmask pL1728) 1411 317 (true, L1728_cp2.1, L1728_cp2.2)) 1728 864 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1728_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1728_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1728_fin) true) L1728_seg1) L1728_seg2) (by decide) rfl L1728_fin ptTest_fst
noncomputable def H1728_cp1 : Nat × Nat := t7val% (fastRun pH1728 1 997 (init pH1728) (init pH1728))
theorem H1728_seg1 : segOK pH1728 1 997 (init pH1728) (init pH1728) H1728_cp1.1 H1728_cp1.2 = true := by
  decide +kernel
noncomputable def H1728_cp2 : Nat × Nat := t7val% (fastRun pH1728 1 1410 (init pH1728) (init pH1728))
theorem H1728_seg2 : segOK pH1728 998 413 H1728_cp1.1 H1728_cp1.2 H1728_cp2.1 H1728_cp2.2 = true := by
  decide +kernel
theorem H1728_fin : (prmOK pH1728 1728 && ptTest pH1728 (runFrom pH1728 (fmask pH1728) (cmask pH1728) (hmask pH1728) 1411 317 (true, H1728_cp2.1, H1728_cp2.2)) 1728 864 true) = true := by
  decide +kernel
theorem H1728_ok : RunOK pH1728 1728 (runFrom pH1728 (fmask pH1728) (cmask pH1728) (hmask pH1728) 1411 317 (true, H1728_cp2.1, H1728_cp2.2)) ∧ ptTest pH1728 (runFrom pH1728 (fmask pH1728) (cmask pH1728) (hmask pH1728) 1411 317 (true, H1728_cp2.1, H1728_cp2.2)) 1728 864 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1728_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1728_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1728_fin) true) H1728_seg1) H1728_seg2) (by decide) rfl H1728_fin ptTest_fst
noncomputable def I1728_cp1 : Nat × Nat := t7val% (fastRun pI1728 1 1221 (init pI1728) (init pI1728))
theorem I1728_seg1 : segOK pI1728 1 1221 (init pI1728) (init pI1728) I1728_cp1.1 I1728_cp1.2 = true := by
  decide +kernel
theorem I1728_fin : (prmOK pI1728 1728 && intTest pI1728 (runFrom pI1728 (fmask pI1728) (cmask pI1728) (hmask pI1728) 1222 506 (true, I1728_cp1.1, I1728_cp1.2)) 1728 21 true) = true := by
  decide +kernel
theorem I1728_ok : RunOK pI1728 1728 (runFrom pI1728 (fmask pI1728) (cmask pI1728) (hmask pI1728) 1222 506 (true, I1728_cp1.1, I1728_cp1.2)) ∧ intTest pI1728 (runFrom pI1728 (fmask pI1728) (cmask pI1728) (hmask pI1728) 1222 506 (true, I1728_cp1.1, I1728_cp1.2)) 1728 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1728_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1728_fin) true) I1728_seg1) (by decide) rfl I1728_fin intTest_fst
theorem link1728 : linkOK pL1728 pH1728 pI1728 = true := by decide +kernel
theorem cvx1728 : ConvexBetweenHumps 1728 :=
  cvx_of L1728_ok H1728_ok I1728_ok link1728 (by decide)
theorem cenlink1728 : cenLinkOK pI1728 1728 = true := by decide +kernel
theorem cen1728 : CenterUniqueMin 1728 ∧ DipHyp 1728 ∧ OnePointHyps 1728 :=
  cen_of L1728_ok H1728_ok I1728_ok link1728 cenlink1728

/-! ### `N = 1729` -/

def pL1729 : Prm := ⟨80, 37, 40, 1731, 11, 18446744073709551616, 110815927877306098, 110815927877306098⟩
def pH1729 : Prm := ⟨80, 37, 40, 1731, 11, 18446744073709551616, 110817027388933874, 110817027388933874⟩
def pI1729 : Prm := ⟨69, 33, 33, 1731, 11, 18446744073709551616, 110815927877306098, 110817027388933874⟩
noncomputable def L1729_cp1 : Nat × Nat := t7val% (fastRun pL1729 1 997 (init pL1729) (init pL1729))
theorem L1729_seg1 : segOK pL1729 1 997 (init pL1729) (init pL1729) L1729_cp1.1 L1729_cp1.2 = true := by
  decide +kernel
noncomputable def L1729_cp2 : Nat × Nat := t7val% (fastRun pL1729 1 1411 (init pL1729) (init pL1729))
theorem L1729_seg2 : segOK pL1729 998 414 L1729_cp1.1 L1729_cp1.2 L1729_cp2.1 L1729_cp2.2 = true := by
  decide +kernel
theorem L1729_fin : (prmOK pL1729 1729 && ptTest pL1729 (runFrom pL1729 (fmask pL1729) (cmask pL1729) (hmask pL1729) 1412 317 (true, L1729_cp2.1, L1729_cp2.2)) 1729 865 false) = true := by
  decide +kernel
theorem L1729_ok : RunOK pL1729 1729 (runFrom pL1729 (fmask pL1729) (cmask pL1729) (hmask pL1729) 1412 317 (true, L1729_cp2.1, L1729_cp2.2)) ∧ ptTest pL1729 (runFrom pL1729 (fmask pL1729) (cmask pL1729) (hmask pL1729) 1412 317 (true, L1729_cp2.1, L1729_cp2.2)) 1729 865 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1729_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1729_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1729_fin) true) L1729_seg1) L1729_seg2) (by decide) rfl L1729_fin ptTest_fst
noncomputable def H1729_cp1 : Nat × Nat := t7val% (fastRun pH1729 1 997 (init pH1729) (init pH1729))
theorem H1729_seg1 : segOK pH1729 1 997 (init pH1729) (init pH1729) H1729_cp1.1 H1729_cp1.2 = true := by
  decide +kernel
noncomputable def H1729_cp2 : Nat × Nat := t7val% (fastRun pH1729 1 1411 (init pH1729) (init pH1729))
theorem H1729_seg2 : segOK pH1729 998 414 H1729_cp1.1 H1729_cp1.2 H1729_cp2.1 H1729_cp2.2 = true := by
  decide +kernel
theorem H1729_fin : (prmOK pH1729 1729 && ptTest pH1729 (runFrom pH1729 (fmask pH1729) (cmask pH1729) (hmask pH1729) 1412 317 (true, H1729_cp2.1, H1729_cp2.2)) 1729 865 true) = true := by
  decide +kernel
theorem H1729_ok : RunOK pH1729 1729 (runFrom pH1729 (fmask pH1729) (cmask pH1729) (hmask pH1729) 1412 317 (true, H1729_cp2.1, H1729_cp2.2)) ∧ ptTest pH1729 (runFrom pH1729 (fmask pH1729) (cmask pH1729) (hmask pH1729) 1412 317 (true, H1729_cp2.1, H1729_cp2.2)) 1729 865 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1729_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1729_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1729_fin) true) H1729_seg1) H1729_seg2) (by decide) rfl H1729_fin ptTest_fst
noncomputable def I1729_cp1 : Nat × Nat := t7val% (fastRun pI1729 1 1222 (init pI1729) (init pI1729))
theorem I1729_seg1 : segOK pI1729 1 1222 (init pI1729) (init pI1729) I1729_cp1.1 I1729_cp1.2 = true := by
  decide +kernel
theorem I1729_fin : (prmOK pI1729 1729 && intTest pI1729 (runFrom pI1729 (fmask pI1729) (cmask pI1729) (hmask pI1729) 1223 506 (true, I1729_cp1.1, I1729_cp1.2)) 1729 21 false) = true := by
  decide +kernel
theorem I1729_ok : RunOK pI1729 1729 (runFrom pI1729 (fmask pI1729) (cmask pI1729) (hmask pI1729) 1223 506 (true, I1729_cp1.1, I1729_cp1.2)) ∧ intTest pI1729 (runFrom pI1729 (fmask pI1729) (cmask pI1729) (hmask pI1729) 1223 506 (true, I1729_cp1.1, I1729_cp1.2)) 1729 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1729_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1729_fin) true) I1729_seg1) (by decide) rfl I1729_fin intTest_fst
theorem link1729 : linkOK pL1729 pH1729 pI1729 = true := by decide +kernel
theorem cvx1729 : ConvexBetweenHumps 1729 :=
  cvx_of L1729_ok H1729_ok I1729_ok link1729 (by decide)

/-! ### `N = 1730` -/

def pL1730 : Prm := ⟨80, 37, 40, 1732, 11, 18446744073709551616, 110763505732523171, 110763505732523171⟩
def pH1730 : Prm := ⟨80, 37, 40, 1732, 11, 18446744073709551616, 110764605244150947, 110764605244150947⟩
def pI1730 : Prm := ⟨69, 33, 33, 1732, 11, 18446744073709551616, 110763505732523171, 110764605244150947⟩
noncomputable def L1730_cp1 : Nat × Nat := t7val% (fastRun pL1730 1 998 (init pL1730) (init pL1730))
theorem L1730_seg1 : segOK pL1730 1 998 (init pL1730) (init pL1730) L1730_cp1.1 L1730_cp1.2 = true := by
  decide +kernel
noncomputable def L1730_cp2 : Nat × Nat := t7val% (fastRun pL1730 1 1412 (init pL1730) (init pL1730))
theorem L1730_seg2 : segOK pL1730 999 414 L1730_cp1.1 L1730_cp1.2 L1730_cp2.1 L1730_cp2.2 = true := by
  decide +kernel
theorem L1730_fin : (prmOK pL1730 1730 && ptTest pL1730 (runFrom pL1730 (fmask pL1730) (cmask pL1730) (hmask pL1730) 1413 317 (true, L1730_cp2.1, L1730_cp2.2)) 1730 865 false) = true := by
  decide +kernel
theorem L1730_ok : RunOK pL1730 1730 (runFrom pL1730 (fmask pL1730) (cmask pL1730) (hmask pL1730) 1413 317 (true, L1730_cp2.1, L1730_cp2.2)) ∧ ptTest pL1730 (runFrom pL1730 (fmask pL1730) (cmask pL1730) (hmask pL1730) 1413 317 (true, L1730_cp2.1, L1730_cp2.2)) 1730 865 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1730_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1730_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1730_fin) true) L1730_seg1) L1730_seg2) (by decide) rfl L1730_fin ptTest_fst
noncomputable def H1730_cp1 : Nat × Nat := t7val% (fastRun pH1730 1 998 (init pH1730) (init pH1730))
theorem H1730_seg1 : segOK pH1730 1 998 (init pH1730) (init pH1730) H1730_cp1.1 H1730_cp1.2 = true := by
  decide +kernel
noncomputable def H1730_cp2 : Nat × Nat := t7val% (fastRun pH1730 1 1412 (init pH1730) (init pH1730))
theorem H1730_seg2 : segOK pH1730 999 414 H1730_cp1.1 H1730_cp1.2 H1730_cp2.1 H1730_cp2.2 = true := by
  decide +kernel
theorem H1730_fin : (prmOK pH1730 1730 && ptTest pH1730 (runFrom pH1730 (fmask pH1730) (cmask pH1730) (hmask pH1730) 1413 317 (true, H1730_cp2.1, H1730_cp2.2)) 1730 865 true) = true := by
  decide +kernel
theorem H1730_ok : RunOK pH1730 1730 (runFrom pH1730 (fmask pH1730) (cmask pH1730) (hmask pH1730) 1413 317 (true, H1730_cp2.1, H1730_cp2.2)) ∧ ptTest pH1730 (runFrom pH1730 (fmask pH1730) (cmask pH1730) (hmask pH1730) 1413 317 (true, H1730_cp2.1, H1730_cp2.2)) 1730 865 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1730_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1730_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1730_fin) true) H1730_seg1) H1730_seg2) (by decide) rfl H1730_fin ptTest_fst
noncomputable def I1730_cp1 : Nat × Nat := t7val% (fastRun pI1730 1 1222 (init pI1730) (init pI1730))
theorem I1730_seg1 : segOK pI1730 1 1222 (init pI1730) (init pI1730) I1730_cp1.1 I1730_cp1.2 = true := by
  decide +kernel
theorem I1730_fin : (prmOK pI1730 1730 && intTest pI1730 (runFrom pI1730 (fmask pI1730) (cmask pI1730) (hmask pI1730) 1223 507 (true, I1730_cp1.1, I1730_cp1.2)) 1730 21 true) = true := by
  decide +kernel
theorem I1730_ok : RunOK pI1730 1730 (runFrom pI1730 (fmask pI1730) (cmask pI1730) (hmask pI1730) 1223 507 (true, I1730_cp1.1, I1730_cp1.2)) ∧ intTest pI1730 (runFrom pI1730 (fmask pI1730) (cmask pI1730) (hmask pI1730) 1223 507 (true, I1730_cp1.1, I1730_cp1.2)) 1730 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1730_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1730_fin) true) I1730_seg1) (by decide) rfl I1730_fin intTest_fst
theorem link1730 : linkOK pL1730 pH1730 pI1730 = true := by decide +kernel
theorem cvx1730 : ConvexBetweenHumps 1730 :=
  cvx_of L1730_ok H1730_ok I1730_ok link1730 (by decide)
theorem cenlink1730 : cenLinkOK pI1730 1730 = true := by decide +kernel
theorem cen1730 : CenterUniqueMin 1730 ∧ DipHyp 1730 ∧ OnePointHyps 1730 :=
  cen_of L1730_ok H1730_ok I1730_ok link1730 cenlink1730

/-! ### `N = 1731` -/

def pL1731 : Prm := ⟨80, 37, 40, 1733, 11, 18446744073709551616, 110711115731911214, 110711115731911214⟩
def pH1731 : Prm := ⟨80, 37, 40, 1733, 11, 18446744073709551616, 110712215243538990, 110712215243538990⟩
def pI1731 : Prm := ⟨69, 33, 33, 1733, 11, 18446744073709551616, 110711115731911214, 110712215243538990⟩
noncomputable def L1731_cp1 : Nat × Nat := t7val% (fastRun pL1731 1 998 (init pL1731) (init pL1731))
theorem L1731_seg1 : segOK pL1731 1 998 (init pL1731) (init pL1731) L1731_cp1.1 L1731_cp1.2 = true := by
  decide +kernel
noncomputable def L1731_cp2 : Nat × Nat := t7val% (fastRun pL1731 1 1412 (init pL1731) (init pL1731))
theorem L1731_seg2 : segOK pL1731 999 414 L1731_cp1.1 L1731_cp1.2 L1731_cp2.1 L1731_cp2.2 = true := by
  decide +kernel
theorem L1731_fin : (prmOK pL1731 1731 && ptTest pL1731 (runFrom pL1731 (fmask pL1731) (cmask pL1731) (hmask pL1731) 1413 318 (true, L1731_cp2.1, L1731_cp2.2)) 1731 866 false) = true := by
  decide +kernel
theorem L1731_ok : RunOK pL1731 1731 (runFrom pL1731 (fmask pL1731) (cmask pL1731) (hmask pL1731) 1413 318 (true, L1731_cp2.1, L1731_cp2.2)) ∧ ptTest pL1731 (runFrom pL1731 (fmask pL1731) (cmask pL1731) (hmask pL1731) 1413 318 (true, L1731_cp2.1, L1731_cp2.2)) 1731 866 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1731_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1731_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1731_fin) true) L1731_seg1) L1731_seg2) (by decide) rfl L1731_fin ptTest_fst
noncomputable def H1731_cp1 : Nat × Nat := t7val% (fastRun pH1731 1 998 (init pH1731) (init pH1731))
theorem H1731_seg1 : segOK pH1731 1 998 (init pH1731) (init pH1731) H1731_cp1.1 H1731_cp1.2 = true := by
  decide +kernel
noncomputable def H1731_cp2 : Nat × Nat := t7val% (fastRun pH1731 1 1412 (init pH1731) (init pH1731))
theorem H1731_seg2 : segOK pH1731 999 414 H1731_cp1.1 H1731_cp1.2 H1731_cp2.1 H1731_cp2.2 = true := by
  decide +kernel
theorem H1731_fin : (prmOK pH1731 1731 && ptTest pH1731 (runFrom pH1731 (fmask pH1731) (cmask pH1731) (hmask pH1731) 1413 318 (true, H1731_cp2.1, H1731_cp2.2)) 1731 866 true) = true := by
  decide +kernel
theorem H1731_ok : RunOK pH1731 1731 (runFrom pH1731 (fmask pH1731) (cmask pH1731) (hmask pH1731) 1413 318 (true, H1731_cp2.1, H1731_cp2.2)) ∧ ptTest pH1731 (runFrom pH1731 (fmask pH1731) (cmask pH1731) (hmask pH1731) 1413 318 (true, H1731_cp2.1, H1731_cp2.2)) 1731 866 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1731_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1731_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1731_fin) true) H1731_seg1) H1731_seg2) (by decide) rfl H1731_fin ptTest_fst
noncomputable def I1731_cp1 : Nat × Nat := t7val% (fastRun pI1731 1 1223 (init pI1731) (init pI1731))
theorem I1731_seg1 : segOK pI1731 1 1223 (init pI1731) (init pI1731) I1731_cp1.1 I1731_cp1.2 = true := by
  decide +kernel
theorem I1731_fin : (prmOK pI1731 1731 && intTest pI1731 (runFrom pI1731 (fmask pI1731) (cmask pI1731) (hmask pI1731) 1224 507 (true, I1731_cp1.1, I1731_cp1.2)) 1731 21 false) = true := by
  decide +kernel
theorem I1731_ok : RunOK pI1731 1731 (runFrom pI1731 (fmask pI1731) (cmask pI1731) (hmask pI1731) 1224 507 (true, I1731_cp1.1, I1731_cp1.2)) ∧ intTest pI1731 (runFrom pI1731 (fmask pI1731) (cmask pI1731) (hmask pI1731) 1224 507 (true, I1731_cp1.1, I1731_cp1.2)) 1731 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1731_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1731_fin) true) I1731_seg1) (by decide) rfl I1731_fin intTest_fst
theorem link1731 : linkOK pL1731 pH1731 pI1731 = true := by decide +kernel
theorem cvx1731 : ConvexBetweenHumps 1731 :=
  cvx_of L1731_ok H1731_ok I1731_ok link1731 (by decide)

/-! ### `N = 1732` -/

def pL1732 : Prm := ⟨80, 37, 40, 1734, 11, 18446744073709551616, 110658801182965078, 110658801182965078⟩
def pH1732 : Prm := ⟨80, 37, 40, 1734, 11, 18446744073709551616, 110659900694592854, 110659900694592854⟩
def pI1732 : Prm := ⟨69, 33, 33, 1734, 11, 18446744073709551616, 110658801182965078, 110659900694592854⟩
noncomputable def L1732_cp1 : Nat × Nat := t7val% (fastRun pL1732 1 999 (init pL1732) (init pL1732))
theorem L1732_seg1 : segOK pL1732 1 999 (init pL1732) (init pL1732) L1732_cp1.1 L1732_cp1.2 = true := by
  decide +kernel
noncomputable def L1732_cp2 : Nat × Nat := t7val% (fastRun pL1732 1 1413 (init pL1732) (init pL1732))
theorem L1732_seg2 : segOK pL1732 1000 414 L1732_cp1.1 L1732_cp1.2 L1732_cp2.1 L1732_cp2.2 = true := by
  decide +kernel
theorem L1732_fin : (prmOK pL1732 1732 && ptTest pL1732 (runFrom pL1732 (fmask pL1732) (cmask pL1732) (hmask pL1732) 1414 318 (true, L1732_cp2.1, L1732_cp2.2)) 1732 866 false) = true := by
  decide +kernel
theorem L1732_ok : RunOK pL1732 1732 (runFrom pL1732 (fmask pL1732) (cmask pL1732) (hmask pL1732) 1414 318 (true, L1732_cp2.1, L1732_cp2.2)) ∧ ptTest pL1732 (runFrom pL1732 (fmask pL1732) (cmask pL1732) (hmask pL1732) 1414 318 (true, L1732_cp2.1, L1732_cp2.2)) 1732 866 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1732_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1732_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1732_fin) true) L1732_seg1) L1732_seg2) (by decide) rfl L1732_fin ptTest_fst
noncomputable def H1732_cp1 : Nat × Nat := t7val% (fastRun pH1732 1 999 (init pH1732) (init pH1732))
theorem H1732_seg1 : segOK pH1732 1 999 (init pH1732) (init pH1732) H1732_cp1.1 H1732_cp1.2 = true := by
  decide +kernel
noncomputable def H1732_cp2 : Nat × Nat := t7val% (fastRun pH1732 1 1413 (init pH1732) (init pH1732))
theorem H1732_seg2 : segOK pH1732 1000 414 H1732_cp1.1 H1732_cp1.2 H1732_cp2.1 H1732_cp2.2 = true := by
  decide +kernel
theorem H1732_fin : (prmOK pH1732 1732 && ptTest pH1732 (runFrom pH1732 (fmask pH1732) (cmask pH1732) (hmask pH1732) 1414 318 (true, H1732_cp2.1, H1732_cp2.2)) 1732 866 true) = true := by
  decide +kernel
theorem H1732_ok : RunOK pH1732 1732 (runFrom pH1732 (fmask pH1732) (cmask pH1732) (hmask pH1732) 1414 318 (true, H1732_cp2.1, H1732_cp2.2)) ∧ ptTest pH1732 (runFrom pH1732 (fmask pH1732) (cmask pH1732) (hmask pH1732) 1414 318 (true, H1732_cp2.1, H1732_cp2.2)) 1732 866 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1732_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1732_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1732_fin) true) H1732_seg1) H1732_seg2) (by decide) rfl H1732_fin ptTest_fst
noncomputable def I1732_cp1 : Nat × Nat := t7val% (fastRun pI1732 1 1224 (init pI1732) (init pI1732))
theorem I1732_seg1 : segOK pI1732 1 1224 (init pI1732) (init pI1732) I1732_cp1.1 I1732_cp1.2 = true := by
  decide +kernel
theorem I1732_fin : (prmOK pI1732 1732 && intTest pI1732 (runFrom pI1732 (fmask pI1732) (cmask pI1732) (hmask pI1732) 1225 507 (true, I1732_cp1.1, I1732_cp1.2)) 1732 21 true) = true := by
  decide +kernel
theorem I1732_ok : RunOK pI1732 1732 (runFrom pI1732 (fmask pI1732) (cmask pI1732) (hmask pI1732) 1225 507 (true, I1732_cp1.1, I1732_cp1.2)) ∧ intTest pI1732 (runFrom pI1732 (fmask pI1732) (cmask pI1732) (hmask pI1732) 1225 507 (true, I1732_cp1.1, I1732_cp1.2)) 1732 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1732_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1732_fin) true) I1732_seg1) (by decide) rfl I1732_fin intTest_fst
theorem link1732 : linkOK pL1732 pH1732 pI1732 = true := by decide +kernel
theorem cvx1732 : ConvexBetweenHumps 1732 :=
  cvx_of L1732_ok H1732_ok I1732_ok link1732 (by decide)
theorem cenlink1732 : cenLinkOK pI1732 1732 = true := by decide +kernel
theorem cen1732 : CenterUniqueMin 1732 ∧ DipHyp 1732 ∧ OnePointHyps 1732 :=
  cen_of L1732_ok H1732_ok I1732_ok link1732 cenlink1732

/-! ### `N = 1733` -/

def pL1733 : Prm := ⟨80, 37, 40, 1735, 11, 18446744073709551616, 110606518683576563, 110606518683576563⟩
def pH1733 : Prm := ⟨80, 37, 40, 1735, 11, 18446744073709551616, 110607618195204339, 110607618195204339⟩
def pI1733 : Prm := ⟨69, 33, 33, 1735, 11, 18446744073709551616, 110606518683576563, 110607618195204339⟩
noncomputable def L1733_cp1 : Nat × Nat := t7val% (fastRun pL1733 1 1000 (init pL1733) (init pL1733))
theorem L1733_seg1 : segOK pL1733 1 1000 (init pL1733) (init pL1733) L1733_cp1.1 L1733_cp1.2 = true := by
  decide +kernel
noncomputable def L1733_cp2 : Nat × Nat := t7val% (fastRun pL1733 1 1414 (init pL1733) (init pL1733))
theorem L1733_seg2 : segOK pL1733 1001 414 L1733_cp1.1 L1733_cp1.2 L1733_cp2.1 L1733_cp2.2 = true := by
  decide +kernel
theorem L1733_fin : (prmOK pL1733 1733 && ptTest pL1733 (runFrom pL1733 (fmask pL1733) (cmask pL1733) (hmask pL1733) 1415 318 (true, L1733_cp2.1, L1733_cp2.2)) 1733 867 false) = true := by
  decide +kernel
theorem L1733_ok : RunOK pL1733 1733 (runFrom pL1733 (fmask pL1733) (cmask pL1733) (hmask pL1733) 1415 318 (true, L1733_cp2.1, L1733_cp2.2)) ∧ ptTest pL1733 (runFrom pL1733 (fmask pL1733) (cmask pL1733) (hmask pL1733) 1415 318 (true, L1733_cp2.1, L1733_cp2.2)) 1733 867 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1733_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1733_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1733_fin) true) L1733_seg1) L1733_seg2) (by decide) rfl L1733_fin ptTest_fst
noncomputable def H1733_cp1 : Nat × Nat := t7val% (fastRun pH1733 1 1000 (init pH1733) (init pH1733))
theorem H1733_seg1 : segOK pH1733 1 1000 (init pH1733) (init pH1733) H1733_cp1.1 H1733_cp1.2 = true := by
  decide +kernel
noncomputable def H1733_cp2 : Nat × Nat := t7val% (fastRun pH1733 1 1414 (init pH1733) (init pH1733))
theorem H1733_seg2 : segOK pH1733 1001 414 H1733_cp1.1 H1733_cp1.2 H1733_cp2.1 H1733_cp2.2 = true := by
  decide +kernel
theorem H1733_fin : (prmOK pH1733 1733 && ptTest pH1733 (runFrom pH1733 (fmask pH1733) (cmask pH1733) (hmask pH1733) 1415 318 (true, H1733_cp2.1, H1733_cp2.2)) 1733 867 true) = true := by
  decide +kernel
theorem H1733_ok : RunOK pH1733 1733 (runFrom pH1733 (fmask pH1733) (cmask pH1733) (hmask pH1733) 1415 318 (true, H1733_cp2.1, H1733_cp2.2)) ∧ ptTest pH1733 (runFrom pH1733 (fmask pH1733) (cmask pH1733) (hmask pH1733) 1415 318 (true, H1733_cp2.1, H1733_cp2.2)) 1733 867 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1733_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1733_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1733_fin) true) H1733_seg1) H1733_seg2) (by decide) rfl H1733_fin ptTest_fst
noncomputable def I1733_cp1 : Nat × Nat := t7val% (fastRun pI1733 1 1224 (init pI1733) (init pI1733))
theorem I1733_seg1 : segOK pI1733 1 1224 (init pI1733) (init pI1733) I1733_cp1.1 I1733_cp1.2 = true := by
  decide +kernel
theorem I1733_fin : (prmOK pI1733 1733 && intTest pI1733 (runFrom pI1733 (fmask pI1733) (cmask pI1733) (hmask pI1733) 1225 508 (true, I1733_cp1.1, I1733_cp1.2)) 1733 21 false) = true := by
  decide +kernel
theorem I1733_ok : RunOK pI1733 1733 (runFrom pI1733 (fmask pI1733) (cmask pI1733) (hmask pI1733) 1225 508 (true, I1733_cp1.1, I1733_cp1.2)) ∧ intTest pI1733 (runFrom pI1733 (fmask pI1733) (cmask pI1733) (hmask pI1733) 1225 508 (true, I1733_cp1.1, I1733_cp1.2)) 1733 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1733_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1733_fin) true) I1733_seg1) (by decide) rfl I1733_fin intTest_fst
theorem link1733 : linkOK pL1733 pH1733 pI1733 = true := by decide +kernel
theorem cvx1733 : ConvexBetweenHumps 1733 :=
  cvx_of L1733_ok H1733_ok I1733_ok link1733 (by decide)

/-! ### The range -/

theorem cvx_1721_1733 {N : ℕ} (h1 : 1721 ≤ N) (h2 : N ≤ 1733) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1726
  · by_cases h4 : N ≤ 1723
    · by_cases h6 : N ≤ 1721
      · obtain rfl : N = 1721 := by omega
        exact cvx1721
      · by_cases h8 : N ≤ 1722
        · obtain rfl : N = 1722 := by omega
          exact cvx1722
        · obtain rfl : N = 1723 := by omega
          exact cvx1723
    · by_cases h6 : N ≤ 1724
      · obtain rfl : N = 1724 := by omega
        exact cvx1724
      · by_cases h8 : N ≤ 1725
        · obtain rfl : N = 1725 := by omega
          exact cvx1725
        · obtain rfl : N = 1726 := by omega
          exact cvx1726
  · by_cases h4 : N ≤ 1729
    · by_cases h6 : N ≤ 1727
      · obtain rfl : N = 1727 := by omega
        exact cvx1727
      · by_cases h8 : N ≤ 1728
        · obtain rfl : N = 1728 := by omega
          exact cvx1728
        · obtain rfl : N = 1729 := by omega
          exact cvx1729
    · by_cases h6 : N ≤ 1731
      · by_cases h8 : N ≤ 1730
        · obtain rfl : N = 1730 := by omega
          exact cvx1730
        · obtain rfl : N = 1731 := by omega
          exact cvx1731
      · by_cases h8 : N ≤ 1732
        · obtain rfl : N = 1732 := by omega
          exact cvx1732
        · obtain rfl : N = 1733 := by omega
          exact cvx1733

theorem cen_1721_1733 {N : ℕ} (h1 : 1721 ≤ N) (h2 : N ≤ 1733) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1726
  · by_cases h4 : N ≤ 1722
    · obtain rfl : N = 1722 := by omega
      exact cen1722
    · by_cases h6 : N ≤ 1724
      · obtain rfl : N = 1724 := by omega
        exact cen1724
      · obtain rfl : N = 1726 := by omega
        exact cen1726
  · by_cases h4 : N ≤ 1728
    · obtain rfl : N = 1728 := by omega
      exact cen1728
    · by_cases h6 : N ≤ 1730
      · obtain rfl : N = 1730 := by omega
        exact cen1730
      · obtain rfl : N = 1732 := by omega
        exact cen1732

end Kagey131.PaperD.T7
