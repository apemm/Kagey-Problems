import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1291, …, 1314` (generated)

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

/-! ### `N = 1291` -/

def pL1291 : Prm := ⟨77, 36, 38, 1293, 11, 18446744073709551616, 140541893282068411, 140541893282068411⟩
def pH1291 : Prm := ⟨77, 36, 38, 1293, 11, 18446744073709551616, 140544092305323963, 140544092305323963⟩
def pI1291 : Prm := ⟨66, 33, 30, 1293, 11, 18446744073709551616, 140541893282068411, 140544092305323963⟩
noncomputable def L1291_cp1 : Nat × Nat := t7val% (fastRun pL1291 1 912 (init pL1291) (init pL1291))
theorem L1291_seg1 : segOK pL1291 1 912 (init pL1291) (init pL1291) L1291_cp1.1 L1291_cp1.2 = true := by
  decide +kernel
theorem L1291_fin : (prmOK pL1291 1291 && ptTest pL1291 (runFrom pL1291 (fmask pL1291) (cmask pL1291) (hmask pL1291) 913 378 (true, L1291_cp1.1, L1291_cp1.2)) 1291 646 false) = true := by
  decide +kernel
theorem L1291_ok : RunOK pL1291 1291 (runFrom pL1291 (fmask pL1291) (cmask pL1291) (hmask pL1291) 913 378 (true, L1291_cp1.1, L1291_cp1.2)) ∧ ptTest pL1291 (runFrom pL1291 (fmask pL1291) (cmask pL1291) (hmask pL1291) 913 378 (true, L1291_cp1.1, L1291_cp1.2)) 1291 646 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1291_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1291_fin) true) L1291_seg1) (by decide) rfl L1291_fin ptTest_fst
noncomputable def H1291_cp1 : Nat × Nat := t7val% (fastRun pH1291 1 912 (init pH1291) (init pH1291))
theorem H1291_seg1 : segOK pH1291 1 912 (init pH1291) (init pH1291) H1291_cp1.1 H1291_cp1.2 = true := by
  decide +kernel
theorem H1291_fin : (prmOK pH1291 1291 && ptTest pH1291 (runFrom pH1291 (fmask pH1291) (cmask pH1291) (hmask pH1291) 913 378 (true, H1291_cp1.1, H1291_cp1.2)) 1291 646 true) = true := by
  decide +kernel
theorem H1291_ok : RunOK pH1291 1291 (runFrom pH1291 (fmask pH1291) (cmask pH1291) (hmask pH1291) 913 378 (true, H1291_cp1.1, H1291_cp1.2)) ∧ ptTest pH1291 (runFrom pH1291 (fmask pH1291) (cmask pH1291) (hmask pH1291) 913 378 (true, H1291_cp1.1, H1291_cp1.2)) 1291 646 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1291_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1291_fin) true) H1291_seg1) (by decide) rfl H1291_fin ptTest_fst
noncomputable def I1291_cp1 : Nat × Nat := t7val% (fastRun pI1291 1 912 (init pI1291) (init pI1291))
theorem I1291_seg1 : segOK pI1291 1 912 (init pI1291) (init pI1291) I1291_cp1.1 I1291_cp1.2 = true := by
  decide +kernel
theorem I1291_fin : (prmOK pI1291 1291 && intTest pI1291 (runFrom pI1291 (fmask pI1291) (cmask pI1291) (hmask pI1291) 913 378 (true, I1291_cp1.1, I1291_cp1.2)) 1291 19 false) = true := by
  decide +kernel
theorem I1291_ok : RunOK pI1291 1291 (runFrom pI1291 (fmask pI1291) (cmask pI1291) (hmask pI1291) 913 378 (true, I1291_cp1.1, I1291_cp1.2)) ∧ intTest pI1291 (runFrom pI1291 (fmask pI1291) (cmask pI1291) (hmask pI1291) 913 378 (true, I1291_cp1.1, I1291_cp1.2)) 1291 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1291_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1291_fin) true) I1291_seg1) (by decide) rfl I1291_fin intTest_fst
theorem link1291 : linkOK pL1291 pH1291 pI1291 = true := by decide +kernel
theorem cvx1291 : ConvexBetweenHumps 1291 :=
  cvx_of L1291_ok H1291_ok I1291_ok link1291 (by decide)

/-! ### `N = 1292` -/

def pL1292 : Prm := ⟨77, 36, 38, 1294, 11, 18446744073709551616, 140453988137900039, 140453988137900039⟩
def pH1292 : Prm := ⟨77, 36, 38, 1294, 11, 18446744073709551616, 140456187161155591, 140456187161155591⟩
def pI1292 : Prm := ⟨66, 33, 30, 1294, 11, 18446744073709551616, 140453988137900039, 140456187161155591⟩
noncomputable def L1292_cp1 : Nat × Nat := t7val% (fastRun pL1292 1 913 (init pL1292) (init pL1292))
theorem L1292_seg1 : segOK pL1292 1 913 (init pL1292) (init pL1292) L1292_cp1.1 L1292_cp1.2 = true := by
  decide +kernel
theorem L1292_fin : (prmOK pL1292 1292 && ptTest pL1292 (runFrom pL1292 (fmask pL1292) (cmask pL1292) (hmask pL1292) 914 378 (true, L1292_cp1.1, L1292_cp1.2)) 1292 646 false) = true := by
  decide +kernel
theorem L1292_ok : RunOK pL1292 1292 (runFrom pL1292 (fmask pL1292) (cmask pL1292) (hmask pL1292) 914 378 (true, L1292_cp1.1, L1292_cp1.2)) ∧ ptTest pL1292 (runFrom pL1292 (fmask pL1292) (cmask pL1292) (hmask pL1292) 914 378 (true, L1292_cp1.1, L1292_cp1.2)) 1292 646 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1292_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1292_fin) true) L1292_seg1) (by decide) rfl L1292_fin ptTest_fst
noncomputable def H1292_cp1 : Nat × Nat := t7val% (fastRun pH1292 1 913 (init pH1292) (init pH1292))
theorem H1292_seg1 : segOK pH1292 1 913 (init pH1292) (init pH1292) H1292_cp1.1 H1292_cp1.2 = true := by
  decide +kernel
theorem H1292_fin : (prmOK pH1292 1292 && ptTest pH1292 (runFrom pH1292 (fmask pH1292) (cmask pH1292) (hmask pH1292) 914 378 (true, H1292_cp1.1, H1292_cp1.2)) 1292 646 true) = true := by
  decide +kernel
theorem H1292_ok : RunOK pH1292 1292 (runFrom pH1292 (fmask pH1292) (cmask pH1292) (hmask pH1292) 914 378 (true, H1292_cp1.1, H1292_cp1.2)) ∧ ptTest pH1292 (runFrom pH1292 (fmask pH1292) (cmask pH1292) (hmask pH1292) 914 378 (true, H1292_cp1.1, H1292_cp1.2)) 1292 646 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1292_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1292_fin) true) H1292_seg1) (by decide) rfl H1292_fin ptTest_fst
noncomputable def I1292_cp1 : Nat × Nat := t7val% (fastRun pI1292 1 913 (init pI1292) (init pI1292))
theorem I1292_seg1 : segOK pI1292 1 913 (init pI1292) (init pI1292) I1292_cp1.1 I1292_cp1.2 = true := by
  decide +kernel
theorem I1292_fin : (prmOK pI1292 1292 && intTest pI1292 (runFrom pI1292 (fmask pI1292) (cmask pI1292) (hmask pI1292) 914 378 (true, I1292_cp1.1, I1292_cp1.2)) 1292 19 true) = true := by
  decide +kernel
theorem I1292_ok : RunOK pI1292 1292 (runFrom pI1292 (fmask pI1292) (cmask pI1292) (hmask pI1292) 914 378 (true, I1292_cp1.1, I1292_cp1.2)) ∧ intTest pI1292 (runFrom pI1292 (fmask pI1292) (cmask pI1292) (hmask pI1292) 914 378 (true, I1292_cp1.1, I1292_cp1.2)) 1292 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1292_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1292_fin) true) I1292_seg1) (by decide) rfl I1292_fin intTest_fst
theorem link1292 : linkOK pL1292 pH1292 pI1292 = true := by decide +kernel
theorem cvx1292 : ConvexBetweenHumps 1292 :=
  cvx_of L1292_ok H1292_ok I1292_ok link1292 (by decide)
theorem cenlink1292 : cenLinkOK pI1292 1292 = true := by decide +kernel
theorem cen1292 : CenterUniqueMin 1292 ∧ DipHyp 1292 ∧ OnePointHyps 1292 :=
  cen_of L1292_ok H1292_ok I1292_ok link1292 cenlink1292

/-! ### `N = 1293` -/

def pL1293 : Prm := ⟨77, 36, 38, 1295, 11, 18446744073709551616, 140366149996456661, 140366149996456661⟩
def pH1293 : Prm := ⟨77, 36, 38, 1295, 11, 18446744073709551616, 140368349019712213, 140368349019712213⟩
def pI1293 : Prm := ⟨66, 33, 30, 1295, 11, 18446744073709551616, 140366149996456661, 140368349019712213⟩
noncomputable def L1293_cp1 : Nat × Nat := t7val% (fastRun pL1293 1 913 (init pL1293) (init pL1293))
theorem L1293_seg1 : segOK pL1293 1 913 (init pL1293) (init pL1293) L1293_cp1.1 L1293_cp1.2 = true := by
  decide +kernel
theorem L1293_fin : (prmOK pL1293 1293 && ptTest pL1293 (runFrom pL1293 (fmask pL1293) (cmask pL1293) (hmask pL1293) 914 379 (true, L1293_cp1.1, L1293_cp1.2)) 1293 647 false) = true := by
  decide +kernel
theorem L1293_ok : RunOK pL1293 1293 (runFrom pL1293 (fmask pL1293) (cmask pL1293) (hmask pL1293) 914 379 (true, L1293_cp1.1, L1293_cp1.2)) ∧ ptTest pL1293 (runFrom pL1293 (fmask pL1293) (cmask pL1293) (hmask pL1293) 914 379 (true, L1293_cp1.1, L1293_cp1.2)) 1293 647 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1293_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1293_fin) true) L1293_seg1) (by decide) rfl L1293_fin ptTest_fst
noncomputable def H1293_cp1 : Nat × Nat := t7val% (fastRun pH1293 1 913 (init pH1293) (init pH1293))
theorem H1293_seg1 : segOK pH1293 1 913 (init pH1293) (init pH1293) H1293_cp1.1 H1293_cp1.2 = true := by
  decide +kernel
theorem H1293_fin : (prmOK pH1293 1293 && ptTest pH1293 (runFrom pH1293 (fmask pH1293) (cmask pH1293) (hmask pH1293) 914 379 (true, H1293_cp1.1, H1293_cp1.2)) 1293 647 true) = true := by
  decide +kernel
theorem H1293_ok : RunOK pH1293 1293 (runFrom pH1293 (fmask pH1293) (cmask pH1293) (hmask pH1293) 914 379 (true, H1293_cp1.1, H1293_cp1.2)) ∧ ptTest pH1293 (runFrom pH1293 (fmask pH1293) (cmask pH1293) (hmask pH1293) 914 379 (true, H1293_cp1.1, H1293_cp1.2)) 1293 647 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1293_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1293_fin) true) H1293_seg1) (by decide) rfl H1293_fin ptTest_fst
noncomputable def I1293_cp1 : Nat × Nat := t7val% (fastRun pI1293 1 913 (init pI1293) (init pI1293))
theorem I1293_seg1 : segOK pI1293 1 913 (init pI1293) (init pI1293) I1293_cp1.1 I1293_cp1.2 = true := by
  decide +kernel
theorem I1293_fin : (prmOK pI1293 1293 && intTest pI1293 (runFrom pI1293 (fmask pI1293) (cmask pI1293) (hmask pI1293) 914 379 (true, I1293_cp1.1, I1293_cp1.2)) 1293 19 false) = true := by
  decide +kernel
theorem I1293_ok : RunOK pI1293 1293 (runFrom pI1293 (fmask pI1293) (cmask pI1293) (hmask pI1293) 914 379 (true, I1293_cp1.1, I1293_cp1.2)) ∧ intTest pI1293 (runFrom pI1293 (fmask pI1293) (cmask pI1293) (hmask pI1293) 914 379 (true, I1293_cp1.1, I1293_cp1.2)) 1293 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1293_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1293_fin) true) I1293_seg1) (by decide) rfl I1293_fin intTest_fst
theorem link1293 : linkOK pL1293 pH1293 pI1293 = true := by decide +kernel
theorem cvx1293 : ConvexBetweenHumps 1293 :=
  cvx_of L1293_ok H1293_ok I1293_ok link1293 (by decide)

/-! ### `N = 1294` -/

def pL1294 : Prm := ⟨77, 36, 38, 1296, 11, 18446744073709551616, 140278484238268678, 140278484238268678⟩
def pH1294 : Prm := ⟨77, 36, 38, 1296, 11, 18446744073709551616, 140280683261524230, 140280683261524230⟩
def pI1294 : Prm := ⟨66, 33, 30, 1296, 11, 18446744073709551616, 140278484238268678, 140280683261524230⟩
noncomputable def L1294_cp1 : Nat × Nat := t7val% (fastRun pL1294 1 914 (init pL1294) (init pL1294))
theorem L1294_seg1 : segOK pL1294 1 914 (init pL1294) (init pL1294) L1294_cp1.1 L1294_cp1.2 = true := by
  decide +kernel
theorem L1294_fin : (prmOK pL1294 1294 && ptTest pL1294 (runFrom pL1294 (fmask pL1294) (cmask pL1294) (hmask pL1294) 915 379 (true, L1294_cp1.1, L1294_cp1.2)) 1294 647 false) = true := by
  decide +kernel
theorem L1294_ok : RunOK pL1294 1294 (runFrom pL1294 (fmask pL1294) (cmask pL1294) (hmask pL1294) 915 379 (true, L1294_cp1.1, L1294_cp1.2)) ∧ ptTest pL1294 (runFrom pL1294 (fmask pL1294) (cmask pL1294) (hmask pL1294) 915 379 (true, L1294_cp1.1, L1294_cp1.2)) 1294 647 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1294_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1294_fin) true) L1294_seg1) (by decide) rfl L1294_fin ptTest_fst
noncomputable def H1294_cp1 : Nat × Nat := t7val% (fastRun pH1294 1 914 (init pH1294) (init pH1294))
theorem H1294_seg1 : segOK pH1294 1 914 (init pH1294) (init pH1294) H1294_cp1.1 H1294_cp1.2 = true := by
  decide +kernel
theorem H1294_fin : (prmOK pH1294 1294 && ptTest pH1294 (runFrom pH1294 (fmask pH1294) (cmask pH1294) (hmask pH1294) 915 379 (true, H1294_cp1.1, H1294_cp1.2)) 1294 647 true) = true := by
  decide +kernel
theorem H1294_ok : RunOK pH1294 1294 (runFrom pH1294 (fmask pH1294) (cmask pH1294) (hmask pH1294) 915 379 (true, H1294_cp1.1, H1294_cp1.2)) ∧ ptTest pH1294 (runFrom pH1294 (fmask pH1294) (cmask pH1294) (hmask pH1294) 915 379 (true, H1294_cp1.1, H1294_cp1.2)) 1294 647 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1294_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1294_fin) true) H1294_seg1) (by decide) rfl H1294_fin ptTest_fst
noncomputable def I1294_cp1 : Nat × Nat := t7val% (fastRun pI1294 1 914 (init pI1294) (init pI1294))
theorem I1294_seg1 : segOK pI1294 1 914 (init pI1294) (init pI1294) I1294_cp1.1 I1294_cp1.2 = true := by
  decide +kernel
theorem I1294_fin : (prmOK pI1294 1294 && intTest pI1294 (runFrom pI1294 (fmask pI1294) (cmask pI1294) (hmask pI1294) 915 379 (true, I1294_cp1.1, I1294_cp1.2)) 1294 19 true) = true := by
  decide +kernel
theorem I1294_ok : RunOK pI1294 1294 (runFrom pI1294 (fmask pI1294) (cmask pI1294) (hmask pI1294) 915 379 (true, I1294_cp1.1, I1294_cp1.2)) ∧ intTest pI1294 (runFrom pI1294 (fmask pI1294) (cmask pI1294) (hmask pI1294) 915 379 (true, I1294_cp1.1, I1294_cp1.2)) 1294 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1294_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1294_fin) true) I1294_seg1) (by decide) rfl I1294_fin intTest_fst
theorem link1294 : linkOK pL1294 pH1294 pI1294 = true := by decide +kernel
theorem cvx1294 : ConvexBetweenHumps 1294 :=
  cvx_of L1294_ok H1294_ok I1294_ok link1294 (by decide)
theorem cenlink1294 : cenLinkOK pI1294 1294 = true := by decide +kernel
theorem cen1294 : CenterUniqueMin 1294 ∧ DipHyp 1294 ∧ OnePointHyps 1294 :=
  cen_of L1294_ok H1294_ok I1294_ok link1294 cenlink1294

/-! ### `N = 1295` -/

def pL1295 : Prm := ⟨77, 36, 38, 1297, 11, 18446744073709551616, 140190885226377498, 140190885226377498⟩
def pH1295 : Prm := ⟨77, 36, 38, 1297, 11, 18446744073709551616, 140193084249633050, 140193084249633050⟩
def pI1295 : Prm := ⟨66, 33, 30, 1297, 11, 18446744073709551616, 140190885226377498, 140193084249633050⟩
noncomputable def L1295_cp1 : Nat × Nat := t7val% (fastRun pL1295 1 915 (init pL1295) (init pL1295))
theorem L1295_seg1 : segOK pL1295 1 915 (init pL1295) (init pL1295) L1295_cp1.1 L1295_cp1.2 = true := by
  decide +kernel
theorem L1295_fin : (prmOK pL1295 1295 && ptTest pL1295 (runFrom pL1295 (fmask pL1295) (cmask pL1295) (hmask pL1295) 916 379 (true, L1295_cp1.1, L1295_cp1.2)) 1295 648 false) = true := by
  decide +kernel
theorem L1295_ok : RunOK pL1295 1295 (runFrom pL1295 (fmask pL1295) (cmask pL1295) (hmask pL1295) 916 379 (true, L1295_cp1.1, L1295_cp1.2)) ∧ ptTest pL1295 (runFrom pL1295 (fmask pL1295) (cmask pL1295) (hmask pL1295) 916 379 (true, L1295_cp1.1, L1295_cp1.2)) 1295 648 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1295_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1295_fin) true) L1295_seg1) (by decide) rfl L1295_fin ptTest_fst
noncomputable def H1295_cp1 : Nat × Nat := t7val% (fastRun pH1295 1 915 (init pH1295) (init pH1295))
theorem H1295_seg1 : segOK pH1295 1 915 (init pH1295) (init pH1295) H1295_cp1.1 H1295_cp1.2 = true := by
  decide +kernel
theorem H1295_fin : (prmOK pH1295 1295 && ptTest pH1295 (runFrom pH1295 (fmask pH1295) (cmask pH1295) (hmask pH1295) 916 379 (true, H1295_cp1.1, H1295_cp1.2)) 1295 648 true) = true := by
  decide +kernel
theorem H1295_ok : RunOK pH1295 1295 (runFrom pH1295 (fmask pH1295) (cmask pH1295) (hmask pH1295) 916 379 (true, H1295_cp1.1, H1295_cp1.2)) ∧ ptTest pH1295 (runFrom pH1295 (fmask pH1295) (cmask pH1295) (hmask pH1295) 916 379 (true, H1295_cp1.1, H1295_cp1.2)) 1295 648 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1295_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1295_fin) true) H1295_seg1) (by decide) rfl H1295_fin ptTest_fst
noncomputable def I1295_cp1 : Nat × Nat := t7val% (fastRun pI1295 1 915 (init pI1295) (init pI1295))
theorem I1295_seg1 : segOK pI1295 1 915 (init pI1295) (init pI1295) I1295_cp1.1 I1295_cp1.2 = true := by
  decide +kernel
theorem I1295_fin : (prmOK pI1295 1295 && intTest pI1295 (runFrom pI1295 (fmask pI1295) (cmask pI1295) (hmask pI1295) 916 379 (true, I1295_cp1.1, I1295_cp1.2)) 1295 19 false) = true := by
  decide +kernel
theorem I1295_ok : RunOK pI1295 1295 (runFrom pI1295 (fmask pI1295) (cmask pI1295) (hmask pI1295) 916 379 (true, I1295_cp1.1, I1295_cp1.2)) ∧ intTest pI1295 (runFrom pI1295 (fmask pI1295) (cmask pI1295) (hmask pI1295) 916 379 (true, I1295_cp1.1, I1295_cp1.2)) 1295 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1295_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1295_fin) true) I1295_seg1) (by decide) rfl I1295_fin intTest_fst
theorem link1295 : linkOK pL1295 pH1295 pI1295 = true := by decide +kernel
theorem cvx1295 : ConvexBetweenHumps 1295 :=
  cvx_of L1295_ok H1295_ok I1295_ok link1295 (by decide)

/-! ### `N = 1296` -/

def pL1296 : Prm := ⟨77, 36, 38, 1298, 11, 18446744073709551616, 140103457845631066, 140103457845631066⟩
def pH1296 : Prm := ⟨77, 36, 38, 1298, 11, 18446744073709551616, 140105656868886618, 140105656868886618⟩
def pI1296 : Prm := ⟨66, 33, 30, 1298, 11, 18446744073709551616, 140103457845631066, 140105656868886618⟩
noncomputable def L1296_cp1 : Nat × Nat := t7val% (fastRun pL1296 1 915 (init pL1296) (init pL1296))
theorem L1296_seg1 : segOK pL1296 1 915 (init pL1296) (init pL1296) L1296_cp1.1 L1296_cp1.2 = true := by
  decide +kernel
theorem L1296_fin : (prmOK pL1296 1296 && ptTest pL1296 (runFrom pL1296 (fmask pL1296) (cmask pL1296) (hmask pL1296) 916 380 (true, L1296_cp1.1, L1296_cp1.2)) 1296 648 false) = true := by
  decide +kernel
theorem L1296_ok : RunOK pL1296 1296 (runFrom pL1296 (fmask pL1296) (cmask pL1296) (hmask pL1296) 916 380 (true, L1296_cp1.1, L1296_cp1.2)) ∧ ptTest pL1296 (runFrom pL1296 (fmask pL1296) (cmask pL1296) (hmask pL1296) 916 380 (true, L1296_cp1.1, L1296_cp1.2)) 1296 648 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1296_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1296_fin) true) L1296_seg1) (by decide) rfl L1296_fin ptTest_fst
noncomputable def H1296_cp1 : Nat × Nat := t7val% (fastRun pH1296 1 915 (init pH1296) (init pH1296))
theorem H1296_seg1 : segOK pH1296 1 915 (init pH1296) (init pH1296) H1296_cp1.1 H1296_cp1.2 = true := by
  decide +kernel
theorem H1296_fin : (prmOK pH1296 1296 && ptTest pH1296 (runFrom pH1296 (fmask pH1296) (cmask pH1296) (hmask pH1296) 916 380 (true, H1296_cp1.1, H1296_cp1.2)) 1296 648 true) = true := by
  decide +kernel
theorem H1296_ok : RunOK pH1296 1296 (runFrom pH1296 (fmask pH1296) (cmask pH1296) (hmask pH1296) 916 380 (true, H1296_cp1.1, H1296_cp1.2)) ∧ ptTest pH1296 (runFrom pH1296 (fmask pH1296) (cmask pH1296) (hmask pH1296) 916 380 (true, H1296_cp1.1, H1296_cp1.2)) 1296 648 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1296_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1296_fin) true) H1296_seg1) (by decide) rfl H1296_fin ptTest_fst
noncomputable def I1296_cp1 : Nat × Nat := t7val% (fastRun pI1296 1 915 (init pI1296) (init pI1296))
theorem I1296_seg1 : segOK pI1296 1 915 (init pI1296) (init pI1296) I1296_cp1.1 I1296_cp1.2 = true := by
  decide +kernel
theorem I1296_fin : (prmOK pI1296 1296 && intTest pI1296 (runFrom pI1296 (fmask pI1296) (cmask pI1296) (hmask pI1296) 916 380 (true, I1296_cp1.1, I1296_cp1.2)) 1296 19 true) = true := by
  decide +kernel
theorem I1296_ok : RunOK pI1296 1296 (runFrom pI1296 (fmask pI1296) (cmask pI1296) (hmask pI1296) 916 380 (true, I1296_cp1.1, I1296_cp1.2)) ∧ intTest pI1296 (runFrom pI1296 (fmask pI1296) (cmask pI1296) (hmask pI1296) 916 380 (true, I1296_cp1.1, I1296_cp1.2)) 1296 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1296_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1296_fin) true) I1296_seg1) (by decide) rfl I1296_fin intTest_fst
theorem link1296 : linkOK pL1296 pH1296 pI1296 = true := by decide +kernel
theorem cvx1296 : ConvexBetweenHumps 1296 :=
  cvx_of L1296_ok H1296_ok I1296_ok link1296 (by decide)
theorem cenlink1296 : cenLinkOK pI1296 1296 = true := by decide +kernel
theorem cen1296 : CenterUniqueMin 1296 ∧ DipHyp 1296 ∧ OnePointHyps 1296 :=
  cen_of L1296_ok H1296_ok I1296_ok link1296 cenlink1296

/-! ### `N = 1297` -/

def pL1297 : Prm := ⟨77, 36, 38, 1299, 11, 18446744073709551616, 140016096956136752, 140016096956136752⟩
def pH1297 : Prm := ⟨77, 36, 38, 1299, 11, 18446744073709551616, 140018295979392304, 140018295979392304⟩
def pI1297 : Prm := ⟨66, 33, 30, 1299, 11, 18446744073709551616, 140016096956136752, 140018295979392304⟩
noncomputable def L1297_cp1 : Nat × Nat := t7val% (fastRun pL1297 1 916 (init pL1297) (init pL1297))
theorem L1297_seg1 : segOK pL1297 1 916 (init pL1297) (init pL1297) L1297_cp1.1 L1297_cp1.2 = true := by
  decide +kernel
theorem L1297_fin : (prmOK pL1297 1297 && ptTest pL1297 (runFrom pL1297 (fmask pL1297) (cmask pL1297) (hmask pL1297) 917 380 (true, L1297_cp1.1, L1297_cp1.2)) 1297 649 false) = true := by
  decide +kernel
theorem L1297_ok : RunOK pL1297 1297 (runFrom pL1297 (fmask pL1297) (cmask pL1297) (hmask pL1297) 917 380 (true, L1297_cp1.1, L1297_cp1.2)) ∧ ptTest pL1297 (runFrom pL1297 (fmask pL1297) (cmask pL1297) (hmask pL1297) 917 380 (true, L1297_cp1.1, L1297_cp1.2)) 1297 649 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1297_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1297_fin) true) L1297_seg1) (by decide) rfl L1297_fin ptTest_fst
noncomputable def H1297_cp1 : Nat × Nat := t7val% (fastRun pH1297 1 916 (init pH1297) (init pH1297))
theorem H1297_seg1 : segOK pH1297 1 916 (init pH1297) (init pH1297) H1297_cp1.1 H1297_cp1.2 = true := by
  decide +kernel
theorem H1297_fin : (prmOK pH1297 1297 && ptTest pH1297 (runFrom pH1297 (fmask pH1297) (cmask pH1297) (hmask pH1297) 917 380 (true, H1297_cp1.1, H1297_cp1.2)) 1297 649 true) = true := by
  decide +kernel
theorem H1297_ok : RunOK pH1297 1297 (runFrom pH1297 (fmask pH1297) (cmask pH1297) (hmask pH1297) 917 380 (true, H1297_cp1.1, H1297_cp1.2)) ∧ ptTest pH1297 (runFrom pH1297 (fmask pH1297) (cmask pH1297) (hmask pH1297) 917 380 (true, H1297_cp1.1, H1297_cp1.2)) 1297 649 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1297_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1297_fin) true) H1297_seg1) (by decide) rfl H1297_fin ptTest_fst
noncomputable def I1297_cp1 : Nat × Nat := t7val% (fastRun pI1297 1 916 (init pI1297) (init pI1297))
theorem I1297_seg1 : segOK pI1297 1 916 (init pI1297) (init pI1297) I1297_cp1.1 I1297_cp1.2 = true := by
  decide +kernel
theorem I1297_fin : (prmOK pI1297 1297 && intTest pI1297 (runFrom pI1297 (fmask pI1297) (cmask pI1297) (hmask pI1297) 917 380 (true, I1297_cp1.1, I1297_cp1.2)) 1297 19 false) = true := by
  decide +kernel
theorem I1297_ok : RunOK pI1297 1297 (runFrom pI1297 (fmask pI1297) (cmask pI1297) (hmask pI1297) 917 380 (true, I1297_cp1.1, I1297_cp1.2)) ∧ intTest pI1297 (runFrom pI1297 (fmask pI1297) (cmask pI1297) (hmask pI1297) 917 380 (true, I1297_cp1.1, I1297_cp1.2)) 1297 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1297_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1297_fin) true) I1297_seg1) (by decide) rfl I1297_fin intTest_fst
theorem link1297 : linkOK pL1297 pH1297 pI1297 = true := by decide +kernel
theorem cvx1297 : ConvexBetweenHumps 1297 :=
  cvx_of L1297_ok H1297_ok I1297_ok link1297 (by decide)

/-! ### `N = 1298` -/

def pL1298 : Prm := ⟨77, 36, 38, 1300, 11, 18446744073709551616, 139928906950122202, 139928906950122202⟩
def pH1298 : Prm := ⟨77, 36, 38, 1300, 11, 18446744073709551616, 139931105973377754, 139931105973377754⟩
def pI1298 : Prm := ⟨66, 33, 30, 1300, 11, 18446744073709551616, 139928906950122202, 139931105973377754⟩
noncomputable def L1298_cp1 : Nat × Nat := t7val% (fastRun pL1298 1 917 (init pL1298) (init pL1298))
theorem L1298_seg1 : segOK pL1298 1 917 (init pL1298) (init pL1298) L1298_cp1.1 L1298_cp1.2 = true := by
  decide +kernel
theorem L1298_fin : (prmOK pL1298 1298 && ptTest pL1298 (runFrom pL1298 (fmask pL1298) (cmask pL1298) (hmask pL1298) 918 380 (true, L1298_cp1.1, L1298_cp1.2)) 1298 649 false) = true := by
  decide +kernel
theorem L1298_ok : RunOK pL1298 1298 (runFrom pL1298 (fmask pL1298) (cmask pL1298) (hmask pL1298) 918 380 (true, L1298_cp1.1, L1298_cp1.2)) ∧ ptTest pL1298 (runFrom pL1298 (fmask pL1298) (cmask pL1298) (hmask pL1298) 918 380 (true, L1298_cp1.1, L1298_cp1.2)) 1298 649 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1298_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1298_fin) true) L1298_seg1) (by decide) rfl L1298_fin ptTest_fst
noncomputable def H1298_cp1 : Nat × Nat := t7val% (fastRun pH1298 1 917 (init pH1298) (init pH1298))
theorem H1298_seg1 : segOK pH1298 1 917 (init pH1298) (init pH1298) H1298_cp1.1 H1298_cp1.2 = true := by
  decide +kernel
theorem H1298_fin : (prmOK pH1298 1298 && ptTest pH1298 (runFrom pH1298 (fmask pH1298) (cmask pH1298) (hmask pH1298) 918 380 (true, H1298_cp1.1, H1298_cp1.2)) 1298 649 true) = true := by
  decide +kernel
theorem H1298_ok : RunOK pH1298 1298 (runFrom pH1298 (fmask pH1298) (cmask pH1298) (hmask pH1298) 918 380 (true, H1298_cp1.1, H1298_cp1.2)) ∧ ptTest pH1298 (runFrom pH1298 (fmask pH1298) (cmask pH1298) (hmask pH1298) 918 380 (true, H1298_cp1.1, H1298_cp1.2)) 1298 649 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1298_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1298_fin) true) H1298_seg1) (by decide) rfl H1298_fin ptTest_fst
noncomputable def I1298_cp1 : Nat × Nat := t7val% (fastRun pI1298 1 917 (init pI1298) (init pI1298))
theorem I1298_seg1 : segOK pI1298 1 917 (init pI1298) (init pI1298) I1298_cp1.1 I1298_cp1.2 = true := by
  decide +kernel
theorem I1298_fin : (prmOK pI1298 1298 && intTest pI1298 (runFrom pI1298 (fmask pI1298) (cmask pI1298) (hmask pI1298) 918 380 (true, I1298_cp1.1, I1298_cp1.2)) 1298 19 true) = true := by
  decide +kernel
theorem I1298_ok : RunOK pI1298 1298 (runFrom pI1298 (fmask pI1298) (cmask pI1298) (hmask pI1298) 918 380 (true, I1298_cp1.1, I1298_cp1.2)) ∧ intTest pI1298 (runFrom pI1298 (fmask pI1298) (cmask pI1298) (hmask pI1298) 918 380 (true, I1298_cp1.1, I1298_cp1.2)) 1298 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1298_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1298_fin) true) I1298_seg1) (by decide) rfl I1298_fin intTest_fst
theorem link1298 : linkOK pL1298 pH1298 pI1298 = true := by decide +kernel
theorem cvx1298 : ConvexBetweenHumps 1298 :=
  cvx_of L1298_ok H1298_ok I1298_ok link1298 (by decide)
theorem cenlink1298 : cenLinkOK pI1298 1298 = true := by decide +kernel
theorem cen1298 : CenterUniqueMin 1298 ∧ DipHyp 1298 ∧ OnePointHyps 1298 :=
  cen_of L1298_ok H1298_ok I1298_ok link1298 cenlink1298

/-! ### `N = 1299` -/

def pL1299 : Prm := ⟨79, 37, 39, 1301, 11, 18446744073709551616, 139842332937401801, 139842332937401801⟩
def pH1299 : Prm := ⟨79, 37, 39, 1301, 11, 18446744073709551616, 139843432449029577, 139843432449029577⟩
def pI1299 : Prm := ⟨66, 32, 31, 1301, 11, 18446744073709551616, 139842332937401801, 139843432449029577⟩
noncomputable def L1299_cp1 : Nat × Nat := t7val% (fastRun pL1299 1 918 (init pL1299) (init pL1299))
theorem L1299_seg1 : segOK pL1299 1 918 (init pL1299) (init pL1299) L1299_cp1.1 L1299_cp1.2 = true := by
  decide +kernel
theorem L1299_fin : (prmOK pL1299 1299 && ptTest pL1299 (runFrom pL1299 (fmask pL1299) (cmask pL1299) (hmask pL1299) 919 380 (true, L1299_cp1.1, L1299_cp1.2)) 1299 650 false) = true := by
  decide +kernel
theorem L1299_ok : RunOK pL1299 1299 (runFrom pL1299 (fmask pL1299) (cmask pL1299) (hmask pL1299) 919 380 (true, L1299_cp1.1, L1299_cp1.2)) ∧ ptTest pL1299 (runFrom pL1299 (fmask pL1299) (cmask pL1299) (hmask pL1299) 919 380 (true, L1299_cp1.1, L1299_cp1.2)) 1299 650 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1299_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1299_fin) true) L1299_seg1) (by decide) rfl L1299_fin ptTest_fst
noncomputable def H1299_cp1 : Nat × Nat := t7val% (fastRun pH1299 1 918 (init pH1299) (init pH1299))
theorem H1299_seg1 : segOK pH1299 1 918 (init pH1299) (init pH1299) H1299_cp1.1 H1299_cp1.2 = true := by
  decide +kernel
theorem H1299_fin : (prmOK pH1299 1299 && ptTest pH1299 (runFrom pH1299 (fmask pH1299) (cmask pH1299) (hmask pH1299) 919 380 (true, H1299_cp1.1, H1299_cp1.2)) 1299 650 true) = true := by
  decide +kernel
theorem H1299_ok : RunOK pH1299 1299 (runFrom pH1299 (fmask pH1299) (cmask pH1299) (hmask pH1299) 919 380 (true, H1299_cp1.1, H1299_cp1.2)) ∧ ptTest pH1299 (runFrom pH1299 (fmask pH1299) (cmask pH1299) (hmask pH1299) 919 380 (true, H1299_cp1.1, H1299_cp1.2)) 1299 650 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1299_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1299_fin) true) H1299_seg1) (by decide) rfl H1299_fin ptTest_fst
noncomputable def I1299_cp1 : Nat × Nat := t7val% (fastRun pI1299 1 918 (init pI1299) (init pI1299))
theorem I1299_seg1 : segOK pI1299 1 918 (init pI1299) (init pI1299) I1299_cp1.1 I1299_cp1.2 = true := by
  decide +kernel
theorem I1299_fin : (prmOK pI1299 1299 && intTest pI1299 (runFrom pI1299 (fmask pI1299) (cmask pI1299) (hmask pI1299) 919 380 (true, I1299_cp1.1, I1299_cp1.2)) 1299 19 false) = true := by
  decide +kernel
theorem I1299_ok : RunOK pI1299 1299 (runFrom pI1299 (fmask pI1299) (cmask pI1299) (hmask pI1299) 919 380 (true, I1299_cp1.1, I1299_cp1.2)) ∧ intTest pI1299 (runFrom pI1299 (fmask pI1299) (cmask pI1299) (hmask pI1299) 919 380 (true, I1299_cp1.1, I1299_cp1.2)) 1299 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1299_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1299_fin) true) I1299_seg1) (by decide) rfl I1299_fin intTest_fst
theorem link1299 : linkOK pL1299 pH1299 pI1299 = true := by decide +kernel
theorem cvx1299 : ConvexBetweenHumps 1299 :=
  cvx_of L1299_ok H1299_ok I1299_ok link1299 (by decide)

/-! ### `N = 1300` -/

def pL1300 : Prm := ⟨79, 37, 39, 1302, 11, 18446744073709551616, 139755379309072616, 139755379309072616⟩
def pH1300 : Prm := ⟨79, 37, 39, 1302, 11, 18446744073709551616, 139756478820700392, 139756478820700392⟩
def pI1300 : Prm := ⟨66, 32, 31, 1302, 11, 18446744073709551616, 139755379309072616, 139756478820700392⟩
noncomputable def L1300_cp1 : Nat × Nat := t7val% (fastRun pL1300 1 918 (init pL1300) (init pL1300))
theorem L1300_seg1 : segOK pL1300 1 918 (init pL1300) (init pL1300) L1300_cp1.1 L1300_cp1.2 = true := by
  decide +kernel
theorem L1300_fin : (prmOK pL1300 1300 && ptTest pL1300 (runFrom pL1300 (fmask pL1300) (cmask pL1300) (hmask pL1300) 919 381 (true, L1300_cp1.1, L1300_cp1.2)) 1300 650 false) = true := by
  decide +kernel
theorem L1300_ok : RunOK pL1300 1300 (runFrom pL1300 (fmask pL1300) (cmask pL1300) (hmask pL1300) 919 381 (true, L1300_cp1.1, L1300_cp1.2)) ∧ ptTest pL1300 (runFrom pL1300 (fmask pL1300) (cmask pL1300) (hmask pL1300) 919 381 (true, L1300_cp1.1, L1300_cp1.2)) 1300 650 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1300_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1300_fin) true) L1300_seg1) (by decide) rfl L1300_fin ptTest_fst
noncomputable def H1300_cp1 : Nat × Nat := t7val% (fastRun pH1300 1 918 (init pH1300) (init pH1300))
theorem H1300_seg1 : segOK pH1300 1 918 (init pH1300) (init pH1300) H1300_cp1.1 H1300_cp1.2 = true := by
  decide +kernel
theorem H1300_fin : (prmOK pH1300 1300 && ptTest pH1300 (runFrom pH1300 (fmask pH1300) (cmask pH1300) (hmask pH1300) 919 381 (true, H1300_cp1.1, H1300_cp1.2)) 1300 650 true) = true := by
  decide +kernel
theorem H1300_ok : RunOK pH1300 1300 (runFrom pH1300 (fmask pH1300) (cmask pH1300) (hmask pH1300) 919 381 (true, H1300_cp1.1, H1300_cp1.2)) ∧ ptTest pH1300 (runFrom pH1300 (fmask pH1300) (cmask pH1300) (hmask pH1300) 919 381 (true, H1300_cp1.1, H1300_cp1.2)) 1300 650 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1300_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1300_fin) true) H1300_seg1) (by decide) rfl H1300_fin ptTest_fst
noncomputable def I1300_cp1 : Nat × Nat := t7val% (fastRun pI1300 1 918 (init pI1300) (init pI1300))
theorem I1300_seg1 : segOK pI1300 1 918 (init pI1300) (init pI1300) I1300_cp1.1 I1300_cp1.2 = true := by
  decide +kernel
theorem I1300_fin : (prmOK pI1300 1300 && intTest pI1300 (runFrom pI1300 (fmask pI1300) (cmask pI1300) (hmask pI1300) 919 381 (true, I1300_cp1.1, I1300_cp1.2)) 1300 19 true) = true := by
  decide +kernel
theorem I1300_ok : RunOK pI1300 1300 (runFrom pI1300 (fmask pI1300) (cmask pI1300) (hmask pI1300) 919 381 (true, I1300_cp1.1, I1300_cp1.2)) ∧ intTest pI1300 (runFrom pI1300 (fmask pI1300) (cmask pI1300) (hmask pI1300) 919 381 (true, I1300_cp1.1, I1300_cp1.2)) 1300 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1300_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1300_fin) true) I1300_seg1) (by decide) rfl I1300_fin intTest_fst
theorem link1300 : linkOK pL1300 pH1300 pI1300 = true := by decide +kernel
theorem cvx1300 : ConvexBetweenHumps 1300 :=
  cvx_of L1300_ok H1300_ok I1300_ok link1300 (by decide)
theorem cenlink1300 : cenLinkOK pI1300 1300 = true := by decide +kernel
theorem cen1300 : CenterUniqueMin 1300 ∧ DipHyp 1300 ∧ OnePointHyps 1300 :=
  cen_of L1300_ok H1300_ok I1300_ok link1300 cenlink1300

/-! ### `N = 1301` -/

def pL1301 : Prm := ⟨79, 37, 39, 1303, 11, 18446744073709551616, 139668491665798447, 139668491665798447⟩
def pH1301 : Prm := ⟨79, 37, 39, 1303, 11, 18446744073709551616, 139669591177426223, 139669591177426223⟩
def pI1301 : Prm := ⟨66, 32, 31, 1303, 11, 18446744073709551616, 139668491665798447, 139669591177426223⟩
noncomputable def L1301_cp1 : Nat × Nat := t7val% (fastRun pL1301 1 919 (init pL1301) (init pL1301))
theorem L1301_seg1 : segOK pL1301 1 919 (init pL1301) (init pL1301) L1301_cp1.1 L1301_cp1.2 = true := by
  decide +kernel
theorem L1301_fin : (prmOK pL1301 1301 && ptTest pL1301 (runFrom pL1301 (fmask pL1301) (cmask pL1301) (hmask pL1301) 920 381 (true, L1301_cp1.1, L1301_cp1.2)) 1301 651 false) = true := by
  decide +kernel
theorem L1301_ok : RunOK pL1301 1301 (runFrom pL1301 (fmask pL1301) (cmask pL1301) (hmask pL1301) 920 381 (true, L1301_cp1.1, L1301_cp1.2)) ∧ ptTest pL1301 (runFrom pL1301 (fmask pL1301) (cmask pL1301) (hmask pL1301) 920 381 (true, L1301_cp1.1, L1301_cp1.2)) 1301 651 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1301_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1301_fin) true) L1301_seg1) (by decide) rfl L1301_fin ptTest_fst
noncomputable def H1301_cp1 : Nat × Nat := t7val% (fastRun pH1301 1 919 (init pH1301) (init pH1301))
theorem H1301_seg1 : segOK pH1301 1 919 (init pH1301) (init pH1301) H1301_cp1.1 H1301_cp1.2 = true := by
  decide +kernel
theorem H1301_fin : (prmOK pH1301 1301 && ptTest pH1301 (runFrom pH1301 (fmask pH1301) (cmask pH1301) (hmask pH1301) 920 381 (true, H1301_cp1.1, H1301_cp1.2)) 1301 651 true) = true := by
  decide +kernel
theorem H1301_ok : RunOK pH1301 1301 (runFrom pH1301 (fmask pH1301) (cmask pH1301) (hmask pH1301) 920 381 (true, H1301_cp1.1, H1301_cp1.2)) ∧ ptTest pH1301 (runFrom pH1301 (fmask pH1301) (cmask pH1301) (hmask pH1301) 920 381 (true, H1301_cp1.1, H1301_cp1.2)) 1301 651 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1301_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1301_fin) true) H1301_seg1) (by decide) rfl H1301_fin ptTest_fst
noncomputable def I1301_cp1 : Nat × Nat := t7val% (fastRun pI1301 1 919 (init pI1301) (init pI1301))
theorem I1301_seg1 : segOK pI1301 1 919 (init pI1301) (init pI1301) I1301_cp1.1 I1301_cp1.2 = true := by
  decide +kernel
theorem I1301_fin : (prmOK pI1301 1301 && intTest pI1301 (runFrom pI1301 (fmask pI1301) (cmask pI1301) (hmask pI1301) 920 381 (true, I1301_cp1.1, I1301_cp1.2)) 1301 19 false) = true := by
  decide +kernel
theorem I1301_ok : RunOK pI1301 1301 (runFrom pI1301 (fmask pI1301) (cmask pI1301) (hmask pI1301) 920 381 (true, I1301_cp1.1, I1301_cp1.2)) ∧ intTest pI1301 (runFrom pI1301 (fmask pI1301) (cmask pI1301) (hmask pI1301) 920 381 (true, I1301_cp1.1, I1301_cp1.2)) 1301 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1301_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1301_fin) true) I1301_seg1) (by decide) rfl I1301_fin intTest_fst
theorem link1301 : linkOK pL1301 pH1301 pI1301 = true := by decide +kernel
theorem cvx1301 : ConvexBetweenHumps 1301 :=
  cvx_of L1301_ok H1301_ok I1301_ok link1301 (by decide)

/-! ### `N = 1302` -/

def pL1302 : Prm := ⟨79, 37, 39, 1304, 11, 18446744073709551616, 139581773423808153, 139581773423808153⟩
def pH1302 : Prm := ⟨79, 37, 39, 1304, 11, 18446744073709551616, 139582872935435929, 139582872935435929⟩
def pI1302 : Prm := ⟨66, 32, 31, 1304, 11, 18446744073709551616, 139581773423808153, 139582872935435929⟩
noncomputable def L1302_cp1 : Nat × Nat := t7val% (fastRun pL1302 1 920 (init pL1302) (init pL1302))
theorem L1302_seg1 : segOK pL1302 1 920 (init pL1302) (init pL1302) L1302_cp1.1 L1302_cp1.2 = true := by
  decide +kernel
theorem L1302_fin : (prmOK pL1302 1302 && ptTest pL1302 (runFrom pL1302 (fmask pL1302) (cmask pL1302) (hmask pL1302) 921 381 (true, L1302_cp1.1, L1302_cp1.2)) 1302 651 false) = true := by
  decide +kernel
theorem L1302_ok : RunOK pL1302 1302 (runFrom pL1302 (fmask pL1302) (cmask pL1302) (hmask pL1302) 921 381 (true, L1302_cp1.1, L1302_cp1.2)) ∧ ptTest pL1302 (runFrom pL1302 (fmask pL1302) (cmask pL1302) (hmask pL1302) 921 381 (true, L1302_cp1.1, L1302_cp1.2)) 1302 651 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1302_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1302_fin) true) L1302_seg1) (by decide) rfl L1302_fin ptTest_fst
noncomputable def H1302_cp1 : Nat × Nat := t7val% (fastRun pH1302 1 920 (init pH1302) (init pH1302))
theorem H1302_seg1 : segOK pH1302 1 920 (init pH1302) (init pH1302) H1302_cp1.1 H1302_cp1.2 = true := by
  decide +kernel
theorem H1302_fin : (prmOK pH1302 1302 && ptTest pH1302 (runFrom pH1302 (fmask pH1302) (cmask pH1302) (hmask pH1302) 921 381 (true, H1302_cp1.1, H1302_cp1.2)) 1302 651 true) = true := by
  decide +kernel
theorem H1302_ok : RunOK pH1302 1302 (runFrom pH1302 (fmask pH1302) (cmask pH1302) (hmask pH1302) 921 381 (true, H1302_cp1.1, H1302_cp1.2)) ∧ ptTest pH1302 (runFrom pH1302 (fmask pH1302) (cmask pH1302) (hmask pH1302) 921 381 (true, H1302_cp1.1, H1302_cp1.2)) 1302 651 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1302_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1302_fin) true) H1302_seg1) (by decide) rfl H1302_fin ptTest_fst
noncomputable def I1302_cp1 : Nat × Nat := t7val% (fastRun pI1302 1 920 (init pI1302) (init pI1302))
theorem I1302_seg1 : segOK pI1302 1 920 (init pI1302) (init pI1302) I1302_cp1.1 I1302_cp1.2 = true := by
  decide +kernel
theorem I1302_fin : (prmOK pI1302 1302 && intTest pI1302 (runFrom pI1302 (fmask pI1302) (cmask pI1302) (hmask pI1302) 921 381 (true, I1302_cp1.1, I1302_cp1.2)) 1302 19 true) = true := by
  decide +kernel
theorem I1302_ok : RunOK pI1302 1302 (runFrom pI1302 (fmask pI1302) (cmask pI1302) (hmask pI1302) 921 381 (true, I1302_cp1.1, I1302_cp1.2)) ∧ intTest pI1302 (runFrom pI1302 (fmask pI1302) (cmask pI1302) (hmask pI1302) 921 381 (true, I1302_cp1.1, I1302_cp1.2)) 1302 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1302_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1302_fin) true) I1302_seg1) (by decide) rfl I1302_fin intTest_fst
theorem link1302 : linkOK pL1302 pH1302 pI1302 = true := by decide +kernel
theorem cvx1302 : ConvexBetweenHumps 1302 :=
  cvx_of L1302_ok H1302_ok I1302_ok link1302 (by decide)
theorem cenlink1302 : cenLinkOK pI1302 1302 = true := by decide +kernel
theorem cen1302 : CenterUniqueMin 1302 ∧ DipHyp 1302 ∧ OnePointHyps 1302 :=
  cen_of L1302_ok H1302_ok I1302_ok link1302 cenlink1302

/-! ### `N = 1303` -/

def pL1303 : Prm := ⟨79, 37, 39, 1305, 11, 18446744073709551616, 139495120915720455, 139495120915720455⟩
def pH1303 : Prm := ⟨79, 37, 39, 1305, 11, 18446744073709551616, 139496220427348231, 139496220427348231⟩
def pI1303 : Prm := ⟨66, 32, 31, 1305, 11, 18446744073709551616, 139495120915720455, 139496220427348231⟩
noncomputable def L1303_cp1 : Nat × Nat := t7val% (fastRun pL1303 1 920 (init pL1303) (init pL1303))
theorem L1303_seg1 : segOK pL1303 1 920 (init pL1303) (init pL1303) L1303_cp1.1 L1303_cp1.2 = true := by
  decide +kernel
theorem L1303_fin : (prmOK pL1303 1303 && ptTest pL1303 (runFrom pL1303 (fmask pL1303) (cmask pL1303) (hmask pL1303) 921 382 (true, L1303_cp1.1, L1303_cp1.2)) 1303 652 false) = true := by
  decide +kernel
theorem L1303_ok : RunOK pL1303 1303 (runFrom pL1303 (fmask pL1303) (cmask pL1303) (hmask pL1303) 921 382 (true, L1303_cp1.1, L1303_cp1.2)) ∧ ptTest pL1303 (runFrom pL1303 (fmask pL1303) (cmask pL1303) (hmask pL1303) 921 382 (true, L1303_cp1.1, L1303_cp1.2)) 1303 652 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1303_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1303_fin) true) L1303_seg1) (by decide) rfl L1303_fin ptTest_fst
noncomputable def H1303_cp1 : Nat × Nat := t7val% (fastRun pH1303 1 920 (init pH1303) (init pH1303))
theorem H1303_seg1 : segOK pH1303 1 920 (init pH1303) (init pH1303) H1303_cp1.1 H1303_cp1.2 = true := by
  decide +kernel
theorem H1303_fin : (prmOK pH1303 1303 && ptTest pH1303 (runFrom pH1303 (fmask pH1303) (cmask pH1303) (hmask pH1303) 921 382 (true, H1303_cp1.1, H1303_cp1.2)) 1303 652 true) = true := by
  decide +kernel
theorem H1303_ok : RunOK pH1303 1303 (runFrom pH1303 (fmask pH1303) (cmask pH1303) (hmask pH1303) 921 382 (true, H1303_cp1.1, H1303_cp1.2)) ∧ ptTest pH1303 (runFrom pH1303 (fmask pH1303) (cmask pH1303) (hmask pH1303) 921 382 (true, H1303_cp1.1, H1303_cp1.2)) 1303 652 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1303_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1303_fin) true) H1303_seg1) (by decide) rfl H1303_fin ptTest_fst
noncomputable def I1303_cp1 : Nat × Nat := t7val% (fastRun pI1303 1 920 (init pI1303) (init pI1303))
theorem I1303_seg1 : segOK pI1303 1 920 (init pI1303) (init pI1303) I1303_cp1.1 I1303_cp1.2 = true := by
  decide +kernel
theorem I1303_fin : (prmOK pI1303 1303 && intTest pI1303 (runFrom pI1303 (fmask pI1303) (cmask pI1303) (hmask pI1303) 921 382 (true, I1303_cp1.1, I1303_cp1.2)) 1303 19 false) = true := by
  decide +kernel
theorem I1303_ok : RunOK pI1303 1303 (runFrom pI1303 (fmask pI1303) (cmask pI1303) (hmask pI1303) 921 382 (true, I1303_cp1.1, I1303_cp1.2)) ∧ intTest pI1303 (runFrom pI1303 (fmask pI1303) (cmask pI1303) (hmask pI1303) 921 382 (true, I1303_cp1.1, I1303_cp1.2)) 1303 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1303_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1303_fin) true) I1303_seg1) (by decide) rfl I1303_fin intTest_fst
theorem link1303 : linkOK pL1303 pH1303 pI1303 = true := by decide +kernel
theorem cvx1303 : ConvexBetweenHumps 1303 :=
  cvx_of L1303_ok H1303_ok I1303_ok link1303 (by decide)

/-! ### `N = 1304` -/

def pL1304 : Prm := ⟨79, 37, 39, 1306, 11, 18446744073709551616, 139408637074348837, 139408637074348837⟩
def pH1304 : Prm := ⟨79, 37, 39, 1306, 11, 18446744073709551616, 139409736585976613, 139409736585976613⟩
def pI1304 : Prm := ⟨66, 32, 31, 1306, 11, 18446744073709551616, 139408637074348837, 139409736585976613⟩
noncomputable def L1304_cp1 : Nat × Nat := t7val% (fastRun pL1304 1 921 (init pL1304) (init pL1304))
theorem L1304_seg1 : segOK pL1304 1 921 (init pL1304) (init pL1304) L1304_cp1.1 L1304_cp1.2 = true := by
  decide +kernel
theorem L1304_fin : (prmOK pL1304 1304 && ptTest pL1304 (runFrom pL1304 (fmask pL1304) (cmask pL1304) (hmask pL1304) 922 382 (true, L1304_cp1.1, L1304_cp1.2)) 1304 652 false) = true := by
  decide +kernel
theorem L1304_ok : RunOK pL1304 1304 (runFrom pL1304 (fmask pL1304) (cmask pL1304) (hmask pL1304) 922 382 (true, L1304_cp1.1, L1304_cp1.2)) ∧ ptTest pL1304 (runFrom pL1304 (fmask pL1304) (cmask pL1304) (hmask pL1304) 922 382 (true, L1304_cp1.1, L1304_cp1.2)) 1304 652 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1304_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1304_fin) true) L1304_seg1) (by decide) rfl L1304_fin ptTest_fst
noncomputable def H1304_cp1 : Nat × Nat := t7val% (fastRun pH1304 1 921 (init pH1304) (init pH1304))
theorem H1304_seg1 : segOK pH1304 1 921 (init pH1304) (init pH1304) H1304_cp1.1 H1304_cp1.2 = true := by
  decide +kernel
theorem H1304_fin : (prmOK pH1304 1304 && ptTest pH1304 (runFrom pH1304 (fmask pH1304) (cmask pH1304) (hmask pH1304) 922 382 (true, H1304_cp1.1, H1304_cp1.2)) 1304 652 true) = true := by
  decide +kernel
theorem H1304_ok : RunOK pH1304 1304 (runFrom pH1304 (fmask pH1304) (cmask pH1304) (hmask pH1304) 922 382 (true, H1304_cp1.1, H1304_cp1.2)) ∧ ptTest pH1304 (runFrom pH1304 (fmask pH1304) (cmask pH1304) (hmask pH1304) 922 382 (true, H1304_cp1.1, H1304_cp1.2)) 1304 652 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1304_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1304_fin) true) H1304_seg1) (by decide) rfl H1304_fin ptTest_fst
noncomputable def I1304_cp1 : Nat × Nat := t7val% (fastRun pI1304 1 921 (init pI1304) (init pI1304))
theorem I1304_seg1 : segOK pI1304 1 921 (init pI1304) (init pI1304) I1304_cp1.1 I1304_cp1.2 = true := by
  decide +kernel
theorem I1304_fin : (prmOK pI1304 1304 && intTest pI1304 (runFrom pI1304 (fmask pI1304) (cmask pI1304) (hmask pI1304) 922 382 (true, I1304_cp1.1, I1304_cp1.2)) 1304 19 true) = true := by
  decide +kernel
theorem I1304_ok : RunOK pI1304 1304 (runFrom pI1304 (fmask pI1304) (cmask pI1304) (hmask pI1304) 922 382 (true, I1304_cp1.1, I1304_cp1.2)) ∧ intTest pI1304 (runFrom pI1304 (fmask pI1304) (cmask pI1304) (hmask pI1304) 922 382 (true, I1304_cp1.1, I1304_cp1.2)) 1304 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1304_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1304_fin) true) I1304_seg1) (by decide) rfl I1304_fin intTest_fst
theorem link1304 : linkOK pL1304 pH1304 pI1304 = true := by decide +kernel
theorem cvx1304 : ConvexBetweenHumps 1304 :=
  cvx_of L1304_ok H1304_ok I1304_ok link1304 (by decide)
theorem cenlink1304 : cenLinkOK pI1304 1304 = true := by decide +kernel
theorem cen1304 : CenterUniqueMin 1304 ∧ DipHyp 1304 ∧ OnePointHyps 1304 :=
  cen_of L1304_ok H1304_ok I1304_ok link1304 cenlink1304

/-! ### `N = 1305` -/

def pL1305 : Prm := ⟨79, 37, 39, 1307, 11, 18446744073709551616, 139322218717037113, 139322218717037113⟩
def pH1305 : Prm := ⟨79, 37, 39, 1307, 11, 18446744073709551616, 139323318228664889, 139323318228664889⟩
def pI1305 : Prm := ⟨66, 32, 31, 1307, 11, 18446744073709551616, 139322218717037113, 139323318228664889⟩
noncomputable def L1305_cp1 : Nat × Nat := t7val% (fastRun pL1305 1 922 (init pL1305) (init pL1305))
theorem L1305_seg1 : segOK pL1305 1 922 (init pL1305) (init pL1305) L1305_cp1.1 L1305_cp1.2 = true := by
  decide +kernel
theorem L1305_fin : (prmOK pL1305 1305 && ptTest pL1305 (runFrom pL1305 (fmask pL1305) (cmask pL1305) (hmask pL1305) 923 382 (true, L1305_cp1.1, L1305_cp1.2)) 1305 653 false) = true := by
  decide +kernel
theorem L1305_ok : RunOK pL1305 1305 (runFrom pL1305 (fmask pL1305) (cmask pL1305) (hmask pL1305) 923 382 (true, L1305_cp1.1, L1305_cp1.2)) ∧ ptTest pL1305 (runFrom pL1305 (fmask pL1305) (cmask pL1305) (hmask pL1305) 923 382 (true, L1305_cp1.1, L1305_cp1.2)) 1305 653 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1305_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1305_fin) true) L1305_seg1) (by decide) rfl L1305_fin ptTest_fst
noncomputable def H1305_cp1 : Nat × Nat := t7val% (fastRun pH1305 1 922 (init pH1305) (init pH1305))
theorem H1305_seg1 : segOK pH1305 1 922 (init pH1305) (init pH1305) H1305_cp1.1 H1305_cp1.2 = true := by
  decide +kernel
theorem H1305_fin : (prmOK pH1305 1305 && ptTest pH1305 (runFrom pH1305 (fmask pH1305) (cmask pH1305) (hmask pH1305) 923 382 (true, H1305_cp1.1, H1305_cp1.2)) 1305 653 true) = true := by
  decide +kernel
theorem H1305_ok : RunOK pH1305 1305 (runFrom pH1305 (fmask pH1305) (cmask pH1305) (hmask pH1305) 923 382 (true, H1305_cp1.1, H1305_cp1.2)) ∧ ptTest pH1305 (runFrom pH1305 (fmask pH1305) (cmask pH1305) (hmask pH1305) 923 382 (true, H1305_cp1.1, H1305_cp1.2)) 1305 653 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1305_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1305_fin) true) H1305_seg1) (by decide) rfl H1305_fin ptTest_fst
noncomputable def I1305_cp1 : Nat × Nat := t7val% (fastRun pI1305 1 922 (init pI1305) (init pI1305))
theorem I1305_seg1 : segOK pI1305 1 922 (init pI1305) (init pI1305) I1305_cp1.1 I1305_cp1.2 = true := by
  decide +kernel
theorem I1305_fin : (prmOK pI1305 1305 && intTest pI1305 (runFrom pI1305 (fmask pI1305) (cmask pI1305) (hmask pI1305) 923 382 (true, I1305_cp1.1, I1305_cp1.2)) 1305 19 false) = true := by
  decide +kernel
theorem I1305_ok : RunOK pI1305 1305 (runFrom pI1305 (fmask pI1305) (cmask pI1305) (hmask pI1305) 923 382 (true, I1305_cp1.1, I1305_cp1.2)) ∧ intTest pI1305 (runFrom pI1305 (fmask pI1305) (cmask pI1305) (hmask pI1305) 923 382 (true, I1305_cp1.1, I1305_cp1.2)) 1305 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1305_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1305_fin) true) I1305_seg1) (by decide) rfl I1305_fin intTest_fst
theorem link1305 : linkOK pL1305 pH1305 pI1305 = true := by decide +kernel
theorem cvx1305 : ConvexBetweenHumps 1305 :=
  cvx_of L1305_ok H1305_ok I1305_ok link1305 (by decide)

/-! ### `N = 1306` -/

def pL1306 : Prm := ⟨79, 37, 39, 1308, 11, 18446744073709551616, 139235968296134870, 139235968296134870⟩
def pH1306 : Prm := ⟨79, 37, 39, 1308, 11, 18446744073709551616, 139237067807762646, 139237067807762646⟩
def pI1306 : Prm := ⟨66, 32, 31, 1308, 11, 18446744073709551616, 139235968296134870, 139237067807762646⟩
noncomputable def L1306_cp1 : Nat × Nat := t7val% (fastRun pL1306 1 922 (init pL1306) (init pL1306))
theorem L1306_seg1 : segOK pL1306 1 922 (init pL1306) (init pL1306) L1306_cp1.1 L1306_cp1.2 = true := by
  decide +kernel
theorem L1306_fin : (prmOK pL1306 1306 && ptTest pL1306 (runFrom pL1306 (fmask pL1306) (cmask pL1306) (hmask pL1306) 923 383 (true, L1306_cp1.1, L1306_cp1.2)) 1306 653 false) = true := by
  decide +kernel
theorem L1306_ok : RunOK pL1306 1306 (runFrom pL1306 (fmask pL1306) (cmask pL1306) (hmask pL1306) 923 383 (true, L1306_cp1.1, L1306_cp1.2)) ∧ ptTest pL1306 (runFrom pL1306 (fmask pL1306) (cmask pL1306) (hmask pL1306) 923 383 (true, L1306_cp1.1, L1306_cp1.2)) 1306 653 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1306_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1306_fin) true) L1306_seg1) (by decide) rfl L1306_fin ptTest_fst
noncomputable def H1306_cp1 : Nat × Nat := t7val% (fastRun pH1306 1 922 (init pH1306) (init pH1306))
theorem H1306_seg1 : segOK pH1306 1 922 (init pH1306) (init pH1306) H1306_cp1.1 H1306_cp1.2 = true := by
  decide +kernel
theorem H1306_fin : (prmOK pH1306 1306 && ptTest pH1306 (runFrom pH1306 (fmask pH1306) (cmask pH1306) (hmask pH1306) 923 383 (true, H1306_cp1.1, H1306_cp1.2)) 1306 653 true) = true := by
  decide +kernel
theorem H1306_ok : RunOK pH1306 1306 (runFrom pH1306 (fmask pH1306) (cmask pH1306) (hmask pH1306) 923 383 (true, H1306_cp1.1, H1306_cp1.2)) ∧ ptTest pH1306 (runFrom pH1306 (fmask pH1306) (cmask pH1306) (hmask pH1306) 923 383 (true, H1306_cp1.1, H1306_cp1.2)) 1306 653 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1306_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1306_fin) true) H1306_seg1) (by decide) rfl H1306_fin ptTest_fst
noncomputable def I1306_cp1 : Nat × Nat := t7val% (fastRun pI1306 1 922 (init pI1306) (init pI1306))
theorem I1306_seg1 : segOK pI1306 1 922 (init pI1306) (init pI1306) I1306_cp1.1 I1306_cp1.2 = true := by
  decide +kernel
theorem I1306_fin : (prmOK pI1306 1306 && intTest pI1306 (runFrom pI1306 (fmask pI1306) (cmask pI1306) (hmask pI1306) 923 383 (true, I1306_cp1.1, I1306_cp1.2)) 1306 19 true) = true := by
  decide +kernel
theorem I1306_ok : RunOK pI1306 1306 (runFrom pI1306 (fmask pI1306) (cmask pI1306) (hmask pI1306) 923 383 (true, I1306_cp1.1, I1306_cp1.2)) ∧ intTest pI1306 (runFrom pI1306 (fmask pI1306) (cmask pI1306) (hmask pI1306) 923 383 (true, I1306_cp1.1, I1306_cp1.2)) 1306 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1306_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1306_fin) true) I1306_seg1) (by decide) rfl I1306_fin intTest_fst
theorem link1306 : linkOK pL1306 pH1306 pI1306 = true := by decide +kernel
theorem cvx1306 : ConvexBetweenHumps 1306 :=
  cvx_of L1306_ok H1306_ok I1306_ok link1306 (by decide)
theorem cenlink1306 : cenLinkOK pI1306 1306 = true := by decide +kernel
theorem cen1306 : CenterUniqueMin 1306 ∧ DipHyp 1306 ∧ OnePointHyps 1306 :=
  cen_of L1306_ok H1306_ok I1306_ok link1306 cenlink1306

/-! ### `N = 1307` -/

def pL1307 : Prm := ⟨79, 37, 39, 1309, 11, 18446744073709551616, 139149783110759539, 139149783110759539⟩
def pH1307 : Prm := ⟨79, 37, 39, 1309, 11, 18446744073709551616, 139150882622387315, 139150882622387315⟩
def pI1307 : Prm := ⟨66, 32, 31, 1309, 11, 18446744073709551616, 139149783110759539, 139150882622387315⟩
noncomputable def L1307_cp1 : Nat × Nat := t7val% (fastRun pL1307 1 923 (init pL1307) (init pL1307))
theorem L1307_seg1 : segOK pL1307 1 923 (init pL1307) (init pL1307) L1307_cp1.1 L1307_cp1.2 = true := by
  decide +kernel
theorem L1307_fin : (prmOK pL1307 1307 && ptTest pL1307 (runFrom pL1307 (fmask pL1307) (cmask pL1307) (hmask pL1307) 924 383 (true, L1307_cp1.1, L1307_cp1.2)) 1307 654 false) = true := by
  decide +kernel
theorem L1307_ok : RunOK pL1307 1307 (runFrom pL1307 (fmask pL1307) (cmask pL1307) (hmask pL1307) 924 383 (true, L1307_cp1.1, L1307_cp1.2)) ∧ ptTest pL1307 (runFrom pL1307 (fmask pL1307) (cmask pL1307) (hmask pL1307) 924 383 (true, L1307_cp1.1, L1307_cp1.2)) 1307 654 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1307_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1307_fin) true) L1307_seg1) (by decide) rfl L1307_fin ptTest_fst
noncomputable def H1307_cp1 : Nat × Nat := t7val% (fastRun pH1307 1 923 (init pH1307) (init pH1307))
theorem H1307_seg1 : segOK pH1307 1 923 (init pH1307) (init pH1307) H1307_cp1.1 H1307_cp1.2 = true := by
  decide +kernel
theorem H1307_fin : (prmOK pH1307 1307 && ptTest pH1307 (runFrom pH1307 (fmask pH1307) (cmask pH1307) (hmask pH1307) 924 383 (true, H1307_cp1.1, H1307_cp1.2)) 1307 654 true) = true := by
  decide +kernel
theorem H1307_ok : RunOK pH1307 1307 (runFrom pH1307 (fmask pH1307) (cmask pH1307) (hmask pH1307) 924 383 (true, H1307_cp1.1, H1307_cp1.2)) ∧ ptTest pH1307 (runFrom pH1307 (fmask pH1307) (cmask pH1307) (hmask pH1307) 924 383 (true, H1307_cp1.1, H1307_cp1.2)) 1307 654 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1307_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1307_fin) true) H1307_seg1) (by decide) rfl H1307_fin ptTest_fst
noncomputable def I1307_cp1 : Nat × Nat := t7val% (fastRun pI1307 1 923 (init pI1307) (init pI1307))
theorem I1307_seg1 : segOK pI1307 1 923 (init pI1307) (init pI1307) I1307_cp1.1 I1307_cp1.2 = true := by
  decide +kernel
theorem I1307_fin : (prmOK pI1307 1307 && intTest pI1307 (runFrom pI1307 (fmask pI1307) (cmask pI1307) (hmask pI1307) 924 383 (true, I1307_cp1.1, I1307_cp1.2)) 1307 19 false) = true := by
  decide +kernel
theorem I1307_ok : RunOK pI1307 1307 (runFrom pI1307 (fmask pI1307) (cmask pI1307) (hmask pI1307) 924 383 (true, I1307_cp1.1, I1307_cp1.2)) ∧ intTest pI1307 (runFrom pI1307 (fmask pI1307) (cmask pI1307) (hmask pI1307) 924 383 (true, I1307_cp1.1, I1307_cp1.2)) 1307 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1307_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1307_fin) true) I1307_seg1) (by decide) rfl I1307_fin intTest_fst
theorem link1307 : linkOK pL1307 pH1307 pI1307 = true := by decide +kernel
theorem cvx1307 : ConvexBetweenHumps 1307 :=
  cvx_of L1307_ok H1307_ok I1307_ok link1307 (by decide)

/-! ### `N = 1308` -/

def pL1308 : Prm := ⟨79, 37, 39, 1310, 11, 18446744073709551616, 139063765135766737, 139063765135766737⟩
def pH1308 : Prm := ⟨79, 37, 39, 1310, 11, 18446744073709551616, 139064864647394513, 139064864647394513⟩
def pI1308 : Prm := ⟨66, 32, 31, 1310, 11, 18446744073709551616, 139063765135766737, 139064864647394513⟩
noncomputable def L1308_cp1 : Nat × Nat := t7val% (fastRun pL1308 1 924 (init pL1308) (init pL1308))
theorem L1308_seg1 : segOK pL1308 1 924 (init pL1308) (init pL1308) L1308_cp1.1 L1308_cp1.2 = true := by
  decide +kernel
theorem L1308_fin : (prmOK pL1308 1308 && ptTest pL1308 (runFrom pL1308 (fmask pL1308) (cmask pL1308) (hmask pL1308) 925 383 (true, L1308_cp1.1, L1308_cp1.2)) 1308 654 false) = true := by
  decide +kernel
theorem L1308_ok : RunOK pL1308 1308 (runFrom pL1308 (fmask pL1308) (cmask pL1308) (hmask pL1308) 925 383 (true, L1308_cp1.1, L1308_cp1.2)) ∧ ptTest pL1308 (runFrom pL1308 (fmask pL1308) (cmask pL1308) (hmask pL1308) 925 383 (true, L1308_cp1.1, L1308_cp1.2)) 1308 654 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1308_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1308_fin) true) L1308_seg1) (by decide) rfl L1308_fin ptTest_fst
noncomputable def H1308_cp1 : Nat × Nat := t7val% (fastRun pH1308 1 924 (init pH1308) (init pH1308))
theorem H1308_seg1 : segOK pH1308 1 924 (init pH1308) (init pH1308) H1308_cp1.1 H1308_cp1.2 = true := by
  decide +kernel
theorem H1308_fin : (prmOK pH1308 1308 && ptTest pH1308 (runFrom pH1308 (fmask pH1308) (cmask pH1308) (hmask pH1308) 925 383 (true, H1308_cp1.1, H1308_cp1.2)) 1308 654 true) = true := by
  decide +kernel
theorem H1308_ok : RunOK pH1308 1308 (runFrom pH1308 (fmask pH1308) (cmask pH1308) (hmask pH1308) 925 383 (true, H1308_cp1.1, H1308_cp1.2)) ∧ ptTest pH1308 (runFrom pH1308 (fmask pH1308) (cmask pH1308) (hmask pH1308) 925 383 (true, H1308_cp1.1, H1308_cp1.2)) 1308 654 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1308_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1308_fin) true) H1308_seg1) (by decide) rfl H1308_fin ptTest_fst
noncomputable def I1308_cp1 : Nat × Nat := t7val% (fastRun pI1308 1 924 (init pI1308) (init pI1308))
theorem I1308_seg1 : segOK pI1308 1 924 (init pI1308) (init pI1308) I1308_cp1.1 I1308_cp1.2 = true := by
  decide +kernel
theorem I1308_fin : (prmOK pI1308 1308 && intTest pI1308 (runFrom pI1308 (fmask pI1308) (cmask pI1308) (hmask pI1308) 925 383 (true, I1308_cp1.1, I1308_cp1.2)) 1308 19 true) = true := by
  decide +kernel
theorem I1308_ok : RunOK pI1308 1308 (runFrom pI1308 (fmask pI1308) (cmask pI1308) (hmask pI1308) 925 383 (true, I1308_cp1.1, I1308_cp1.2)) ∧ intTest pI1308 (runFrom pI1308 (fmask pI1308) (cmask pI1308) (hmask pI1308) 925 383 (true, I1308_cp1.1, I1308_cp1.2)) 1308 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1308_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1308_fin) true) I1308_seg1) (by decide) rfl I1308_fin intTest_fst
theorem link1308 : linkOK pL1308 pH1308 pI1308 = true := by decide +kernel
theorem cvx1308 : ConvexBetweenHumps 1308 :=
  cvx_of L1308_ok H1308_ok I1308_ok link1308 (by decide)
theorem cenlink1308 : cenLinkOK pI1308 1308 = true := by decide +kernel
theorem cen1308 : CenterUniqueMin 1308 ∧ DipHyp 1308 ∧ OnePointHyps 1308 :=
  cen_of L1308_ok H1308_ok I1308_ok link1308 cenlink1308

/-! ### `N = 1309` -/

def pL1309 : Prm := ⟨79, 37, 39, 1311, 11, 18446744073709551616, 138977812149022242, 138977812149022242⟩
def pH1309 : Prm := ⟨79, 37, 39, 1311, 11, 18446744073709551616, 138978911660650018, 138978911660650018⟩
def pI1309 : Prm := ⟨66, 32, 31, 1311, 11, 18446744073709551616, 138977812149022242, 138978911660650018⟩
noncomputable def L1309_cp1 : Nat × Nat := t7val% (fastRun pL1309 1 925 (init pL1309) (init pL1309))
theorem L1309_seg1 : segOK pL1309 1 925 (init pL1309) (init pL1309) L1309_cp1.1 L1309_cp1.2 = true := by
  decide +kernel
theorem L1309_fin : (prmOK pL1309 1309 && ptTest pL1309 (runFrom pL1309 (fmask pL1309) (cmask pL1309) (hmask pL1309) 926 383 (true, L1309_cp1.1, L1309_cp1.2)) 1309 655 false) = true := by
  decide +kernel
theorem L1309_ok : RunOK pL1309 1309 (runFrom pL1309 (fmask pL1309) (cmask pL1309) (hmask pL1309) 926 383 (true, L1309_cp1.1, L1309_cp1.2)) ∧ ptTest pL1309 (runFrom pL1309 (fmask pL1309) (cmask pL1309) (hmask pL1309) 926 383 (true, L1309_cp1.1, L1309_cp1.2)) 1309 655 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1309_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1309_fin) true) L1309_seg1) (by decide) rfl L1309_fin ptTest_fst
noncomputable def H1309_cp1 : Nat × Nat := t7val% (fastRun pH1309 1 925 (init pH1309) (init pH1309))
theorem H1309_seg1 : segOK pH1309 1 925 (init pH1309) (init pH1309) H1309_cp1.1 H1309_cp1.2 = true := by
  decide +kernel
theorem H1309_fin : (prmOK pH1309 1309 && ptTest pH1309 (runFrom pH1309 (fmask pH1309) (cmask pH1309) (hmask pH1309) 926 383 (true, H1309_cp1.1, H1309_cp1.2)) 1309 655 true) = true := by
  decide +kernel
theorem H1309_ok : RunOK pH1309 1309 (runFrom pH1309 (fmask pH1309) (cmask pH1309) (hmask pH1309) 926 383 (true, H1309_cp1.1, H1309_cp1.2)) ∧ ptTest pH1309 (runFrom pH1309 (fmask pH1309) (cmask pH1309) (hmask pH1309) 926 383 (true, H1309_cp1.1, H1309_cp1.2)) 1309 655 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1309_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1309_fin) true) H1309_seg1) (by decide) rfl H1309_fin ptTest_fst
noncomputable def I1309_cp1 : Nat × Nat := t7val% (fastRun pI1309 1 925 (init pI1309) (init pI1309))
theorem I1309_seg1 : segOK pI1309 1 925 (init pI1309) (init pI1309) I1309_cp1.1 I1309_cp1.2 = true := by
  decide +kernel
theorem I1309_fin : (prmOK pI1309 1309 && intTest pI1309 (runFrom pI1309 (fmask pI1309) (cmask pI1309) (hmask pI1309) 926 383 (true, I1309_cp1.1, I1309_cp1.2)) 1309 19 false) = true := by
  decide +kernel
theorem I1309_ok : RunOK pI1309 1309 (runFrom pI1309 (fmask pI1309) (cmask pI1309) (hmask pI1309) 926 383 (true, I1309_cp1.1, I1309_cp1.2)) ∧ intTest pI1309 (runFrom pI1309 (fmask pI1309) (cmask pI1309) (hmask pI1309) 926 383 (true, I1309_cp1.1, I1309_cp1.2)) 1309 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1309_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1309_fin) true) I1309_seg1) (by decide) rfl I1309_fin intTest_fst
theorem link1309 : linkOK pL1309 pH1309 pI1309 = true := by decide +kernel
theorem cvx1309 : ConvexBetweenHumps 1309 :=
  cvx_of L1309_ok H1309_ok I1309_ok link1309 (by decide)

/-! ### `N = 1310` -/

def pL1310 : Prm := ⟨79, 37, 39, 1312, 11, 18446744073709551616, 138892025650857626, 138892025650857626⟩
def pH1310 : Prm := ⟨79, 37, 39, 1312, 11, 18446744073709551616, 138893125162485402, 138893125162485402⟩
def pI1310 : Prm := ⟨66, 32, 31, 1312, 11, 18446744073709551616, 138892025650857626, 138893125162485402⟩
noncomputable def L1310_cp1 : Nat × Nat := t7val% (fastRun pL1310 1 925 (init pL1310) (init pL1310))
theorem L1310_seg1 : segOK pL1310 1 925 (init pL1310) (init pL1310) L1310_cp1.1 L1310_cp1.2 = true := by
  decide +kernel
theorem L1310_fin : (prmOK pL1310 1310 && ptTest pL1310 (runFrom pL1310 (fmask pL1310) (cmask pL1310) (hmask pL1310) 926 384 (true, L1310_cp1.1, L1310_cp1.2)) 1310 655 false) = true := by
  decide +kernel
theorem L1310_ok : RunOK pL1310 1310 (runFrom pL1310 (fmask pL1310) (cmask pL1310) (hmask pL1310) 926 384 (true, L1310_cp1.1, L1310_cp1.2)) ∧ ptTest pL1310 (runFrom pL1310 (fmask pL1310) (cmask pL1310) (hmask pL1310) 926 384 (true, L1310_cp1.1, L1310_cp1.2)) 1310 655 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1310_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1310_fin) true) L1310_seg1) (by decide) rfl L1310_fin ptTest_fst
noncomputable def H1310_cp1 : Nat × Nat := t7val% (fastRun pH1310 1 925 (init pH1310) (init pH1310))
theorem H1310_seg1 : segOK pH1310 1 925 (init pH1310) (init pH1310) H1310_cp1.1 H1310_cp1.2 = true := by
  decide +kernel
theorem H1310_fin : (prmOK pH1310 1310 && ptTest pH1310 (runFrom pH1310 (fmask pH1310) (cmask pH1310) (hmask pH1310) 926 384 (true, H1310_cp1.1, H1310_cp1.2)) 1310 655 true) = true := by
  decide +kernel
theorem H1310_ok : RunOK pH1310 1310 (runFrom pH1310 (fmask pH1310) (cmask pH1310) (hmask pH1310) 926 384 (true, H1310_cp1.1, H1310_cp1.2)) ∧ ptTest pH1310 (runFrom pH1310 (fmask pH1310) (cmask pH1310) (hmask pH1310) 926 384 (true, H1310_cp1.1, H1310_cp1.2)) 1310 655 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1310_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1310_fin) true) H1310_seg1) (by decide) rfl H1310_fin ptTest_fst
noncomputable def I1310_cp1 : Nat × Nat := t7val% (fastRun pI1310 1 925 (init pI1310) (init pI1310))
theorem I1310_seg1 : segOK pI1310 1 925 (init pI1310) (init pI1310) I1310_cp1.1 I1310_cp1.2 = true := by
  decide +kernel
theorem I1310_fin : (prmOK pI1310 1310 && intTest pI1310 (runFrom pI1310 (fmask pI1310) (cmask pI1310) (hmask pI1310) 926 384 (true, I1310_cp1.1, I1310_cp1.2)) 1310 19 true) = true := by
  decide +kernel
theorem I1310_ok : RunOK pI1310 1310 (runFrom pI1310 (fmask pI1310) (cmask pI1310) (hmask pI1310) 926 384 (true, I1310_cp1.1, I1310_cp1.2)) ∧ intTest pI1310 (runFrom pI1310 (fmask pI1310) (cmask pI1310) (hmask pI1310) 926 384 (true, I1310_cp1.1, I1310_cp1.2)) 1310 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1310_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1310_fin) true) I1310_seg1) (by decide) rfl I1310_fin intTest_fst
theorem link1310 : linkOK pL1310 pH1310 pI1310 = true := by decide +kernel
theorem cvx1310 : ConvexBetweenHumps 1310 :=
  cvx_of L1310_ok H1310_ok I1310_ok link1310 (by decide)
theorem cenlink1310 : cenLinkOK pI1310 1310 = true := by decide +kernel
theorem cen1310 : CenterUniqueMin 1310 ∧ DipHyp 1310 ∧ OnePointHyps 1310 :=
  cen_of L1310_ok H1310_ok I1310_ok link1310 cenlink1310

/-! ### `N = 1311` -/

def pL1311 : Prm := ⟨79, 37, 39, 1313, 11, 18446744073709551616, 138806303894953985, 138806303894953985⟩
def pH1311 : Prm := ⟨79, 37, 39, 1313, 11, 18446744073709551616, 138807403406581761, 138807403406581761⟩
def pI1311 : Prm := ⟨66, 32, 31, 1313, 11, 18446744073709551616, 138806303894953985, 138807403406581761⟩
noncomputable def L1311_cp1 : Nat × Nat := t7val% (fastRun pL1311 1 926 (init pL1311) (init pL1311))
theorem L1311_seg1 : segOK pL1311 1 926 (init pL1311) (init pL1311) L1311_cp1.1 L1311_cp1.2 = true := by
  decide +kernel
theorem L1311_fin : (prmOK pL1311 1311 && ptTest pL1311 (runFrom pL1311 (fmask pL1311) (cmask pL1311) (hmask pL1311) 927 384 (true, L1311_cp1.1, L1311_cp1.2)) 1311 656 false) = true := by
  decide +kernel
theorem L1311_ok : RunOK pL1311 1311 (runFrom pL1311 (fmask pL1311) (cmask pL1311) (hmask pL1311) 927 384 (true, L1311_cp1.1, L1311_cp1.2)) ∧ ptTest pL1311 (runFrom pL1311 (fmask pL1311) (cmask pL1311) (hmask pL1311) 927 384 (true, L1311_cp1.1, L1311_cp1.2)) 1311 656 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1311_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1311_fin) true) L1311_seg1) (by decide) rfl L1311_fin ptTest_fst
noncomputable def H1311_cp1 : Nat × Nat := t7val% (fastRun pH1311 1 926 (init pH1311) (init pH1311))
theorem H1311_seg1 : segOK pH1311 1 926 (init pH1311) (init pH1311) H1311_cp1.1 H1311_cp1.2 = true := by
  decide +kernel
theorem H1311_fin : (prmOK pH1311 1311 && ptTest pH1311 (runFrom pH1311 (fmask pH1311) (cmask pH1311) (hmask pH1311) 927 384 (true, H1311_cp1.1, H1311_cp1.2)) 1311 656 true) = true := by
  decide +kernel
theorem H1311_ok : RunOK pH1311 1311 (runFrom pH1311 (fmask pH1311) (cmask pH1311) (hmask pH1311) 927 384 (true, H1311_cp1.1, H1311_cp1.2)) ∧ ptTest pH1311 (runFrom pH1311 (fmask pH1311) (cmask pH1311) (hmask pH1311) 927 384 (true, H1311_cp1.1, H1311_cp1.2)) 1311 656 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1311_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1311_fin) true) H1311_seg1) (by decide) rfl H1311_fin ptTest_fst
noncomputable def I1311_cp1 : Nat × Nat := t7val% (fastRun pI1311 1 926 (init pI1311) (init pI1311))
theorem I1311_seg1 : segOK pI1311 1 926 (init pI1311) (init pI1311) I1311_cp1.1 I1311_cp1.2 = true := by
  decide +kernel
theorem I1311_fin : (prmOK pI1311 1311 && intTest pI1311 (runFrom pI1311 (fmask pI1311) (cmask pI1311) (hmask pI1311) 927 384 (true, I1311_cp1.1, I1311_cp1.2)) 1311 19 false) = true := by
  decide +kernel
theorem I1311_ok : RunOK pI1311 1311 (runFrom pI1311 (fmask pI1311) (cmask pI1311) (hmask pI1311) 927 384 (true, I1311_cp1.1, I1311_cp1.2)) ∧ intTest pI1311 (runFrom pI1311 (fmask pI1311) (cmask pI1311) (hmask pI1311) 927 384 (true, I1311_cp1.1, I1311_cp1.2)) 1311 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1311_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1311_fin) true) I1311_seg1) (by decide) rfl I1311_fin intTest_fst
theorem link1311 : linkOK pL1311 pH1311 pI1311 = true := by decide +kernel
theorem cvx1311 : ConvexBetweenHumps 1311 :=
  cvx_of L1311_ok H1311_ok I1311_ok link1311 (by decide)

/-! ### `N = 1312` -/

def pL1312 : Prm := ⟨79, 37, 39, 1314, 11, 18446744073709551616, 138720747910033432, 138720747910033432⟩
def pH1312 : Prm := ⟨79, 37, 39, 1314, 11, 18446744073709551616, 138721847421661208, 138721847421661208⟩
def pI1312 : Prm := ⟨66, 32, 31, 1314, 11, 18446744073709551616, 138720747910033432, 138721847421661208⟩
noncomputable def L1312_cp1 : Nat × Nat := t7val% (fastRun pL1312 1 927 (init pL1312) (init pL1312))
theorem L1312_seg1 : segOK pL1312 1 927 (init pL1312) (init pL1312) L1312_cp1.1 L1312_cp1.2 = true := by
  decide +kernel
theorem L1312_fin : (prmOK pL1312 1312 && ptTest pL1312 (runFrom pL1312 (fmask pL1312) (cmask pL1312) (hmask pL1312) 928 384 (true, L1312_cp1.1, L1312_cp1.2)) 1312 656 false) = true := by
  decide +kernel
theorem L1312_ok : RunOK pL1312 1312 (runFrom pL1312 (fmask pL1312) (cmask pL1312) (hmask pL1312) 928 384 (true, L1312_cp1.1, L1312_cp1.2)) ∧ ptTest pL1312 (runFrom pL1312 (fmask pL1312) (cmask pL1312) (hmask pL1312) 928 384 (true, L1312_cp1.1, L1312_cp1.2)) 1312 656 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1312_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1312_fin) true) L1312_seg1) (by decide) rfl L1312_fin ptTest_fst
noncomputable def H1312_cp1 : Nat × Nat := t7val% (fastRun pH1312 1 927 (init pH1312) (init pH1312))
theorem H1312_seg1 : segOK pH1312 1 927 (init pH1312) (init pH1312) H1312_cp1.1 H1312_cp1.2 = true := by
  decide +kernel
theorem H1312_fin : (prmOK pH1312 1312 && ptTest pH1312 (runFrom pH1312 (fmask pH1312) (cmask pH1312) (hmask pH1312) 928 384 (true, H1312_cp1.1, H1312_cp1.2)) 1312 656 true) = true := by
  decide +kernel
theorem H1312_ok : RunOK pH1312 1312 (runFrom pH1312 (fmask pH1312) (cmask pH1312) (hmask pH1312) 928 384 (true, H1312_cp1.1, H1312_cp1.2)) ∧ ptTest pH1312 (runFrom pH1312 (fmask pH1312) (cmask pH1312) (hmask pH1312) 928 384 (true, H1312_cp1.1, H1312_cp1.2)) 1312 656 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1312_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1312_fin) true) H1312_seg1) (by decide) rfl H1312_fin ptTest_fst
noncomputable def I1312_cp1 : Nat × Nat := t7val% (fastRun pI1312 1 927 (init pI1312) (init pI1312))
theorem I1312_seg1 : segOK pI1312 1 927 (init pI1312) (init pI1312) I1312_cp1.1 I1312_cp1.2 = true := by
  decide +kernel
theorem I1312_fin : (prmOK pI1312 1312 && intTest pI1312 (runFrom pI1312 (fmask pI1312) (cmask pI1312) (hmask pI1312) 928 384 (true, I1312_cp1.1, I1312_cp1.2)) 1312 19 true) = true := by
  decide +kernel
theorem I1312_ok : RunOK pI1312 1312 (runFrom pI1312 (fmask pI1312) (cmask pI1312) (hmask pI1312) 928 384 (true, I1312_cp1.1, I1312_cp1.2)) ∧ intTest pI1312 (runFrom pI1312 (fmask pI1312) (cmask pI1312) (hmask pI1312) 928 384 (true, I1312_cp1.1, I1312_cp1.2)) 1312 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1312_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1312_fin) true) I1312_seg1) (by decide) rfl I1312_fin intTest_fst
theorem link1312 : linkOK pL1312 pH1312 pI1312 = true := by decide +kernel
theorem cvx1312 : ConvexBetweenHumps 1312 :=
  cvx_of L1312_ok H1312_ok I1312_ok link1312 (by decide)
theorem cenlink1312 : cenLinkOK pI1312 1312 = true := by decide +kernel
theorem cen1312 : CenterUniqueMin 1312 ∧ DipHyp 1312 ∧ OnePointHyps 1312 :=
  cen_of L1312_ok H1312_ok I1312_ok link1312 cenlink1312

/-! ### `N = 1313` -/

def pL1313 : Prm := ⟨79, 37, 39, 1315, 11, 18446744073709551616, 138635256422622453, 138635256422622453⟩
def pH1313 : Prm := ⟨79, 37, 39, 1315, 11, 18446744073709551616, 138636355934250229, 138636355934250229⟩
def pI1313 : Prm := ⟨66, 32, 31, 1315, 11, 18446744073709551616, 138635256422622453, 138636355934250229⟩
noncomputable def L1313_cp1 : Nat × Nat := t7val% (fastRun pL1313 1 927 (init pL1313) (init pL1313))
theorem L1313_seg1 : segOK pL1313 1 927 (init pL1313) (init pL1313) L1313_cp1.1 L1313_cp1.2 = true := by
  decide +kernel
theorem L1313_fin : (prmOK pL1313 1313 && ptTest pL1313 (runFrom pL1313 (fmask pL1313) (cmask pL1313) (hmask pL1313) 928 385 (true, L1313_cp1.1, L1313_cp1.2)) 1313 657 false) = true := by
  decide +kernel
theorem L1313_ok : RunOK pL1313 1313 (runFrom pL1313 (fmask pL1313) (cmask pL1313) (hmask pL1313) 928 385 (true, L1313_cp1.1, L1313_cp1.2)) ∧ ptTest pL1313 (runFrom pL1313 (fmask pL1313) (cmask pL1313) (hmask pL1313) 928 385 (true, L1313_cp1.1, L1313_cp1.2)) 1313 657 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1313_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1313_fin) true) L1313_seg1) (by decide) rfl L1313_fin ptTest_fst
noncomputable def H1313_cp1 : Nat × Nat := t7val% (fastRun pH1313 1 927 (init pH1313) (init pH1313))
theorem H1313_seg1 : segOK pH1313 1 927 (init pH1313) (init pH1313) H1313_cp1.1 H1313_cp1.2 = true := by
  decide +kernel
theorem H1313_fin : (prmOK pH1313 1313 && ptTest pH1313 (runFrom pH1313 (fmask pH1313) (cmask pH1313) (hmask pH1313) 928 385 (true, H1313_cp1.1, H1313_cp1.2)) 1313 657 true) = true := by
  decide +kernel
theorem H1313_ok : RunOK pH1313 1313 (runFrom pH1313 (fmask pH1313) (cmask pH1313) (hmask pH1313) 928 385 (true, H1313_cp1.1, H1313_cp1.2)) ∧ ptTest pH1313 (runFrom pH1313 (fmask pH1313) (cmask pH1313) (hmask pH1313) 928 385 (true, H1313_cp1.1, H1313_cp1.2)) 1313 657 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1313_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1313_fin) true) H1313_seg1) (by decide) rfl H1313_fin ptTest_fst
noncomputable def I1313_cp1 : Nat × Nat := t7val% (fastRun pI1313 1 927 (init pI1313) (init pI1313))
theorem I1313_seg1 : segOK pI1313 1 927 (init pI1313) (init pI1313) I1313_cp1.1 I1313_cp1.2 = true := by
  decide +kernel
theorem I1313_fin : (prmOK pI1313 1313 && intTest pI1313 (runFrom pI1313 (fmask pI1313) (cmask pI1313) (hmask pI1313) 928 385 (true, I1313_cp1.1, I1313_cp1.2)) 1313 19 false) = true := by
  decide +kernel
theorem I1313_ok : RunOK pI1313 1313 (runFrom pI1313 (fmask pI1313) (cmask pI1313) (hmask pI1313) 928 385 (true, I1313_cp1.1, I1313_cp1.2)) ∧ intTest pI1313 (runFrom pI1313 (fmask pI1313) (cmask pI1313) (hmask pI1313) 928 385 (true, I1313_cp1.1, I1313_cp1.2)) 1313 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1313_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1313_fin) true) I1313_seg1) (by decide) rfl I1313_fin intTest_fst
theorem link1313 : linkOK pL1313 pH1313 pI1313 = true := by decide +kernel
theorem cvx1313 : ConvexBetweenHumps 1313 :=
  cvx_of L1313_ok H1313_ok I1313_ok link1313 (by decide)

/-! ### `N = 1314` -/

def pL1314 : Prm := ⟨79, 37, 39, 1316, 11, 18446744073709551616, 138549929992785184, 138549929992785184⟩
def pH1314 : Prm := ⟨79, 37, 39, 1316, 11, 18446744073709551616, 138551029504412960, 138551029504412960⟩
def pI1314 : Prm := ⟨66, 32, 31, 1316, 11, 18446744073709551616, 138549929992785184, 138551029504412960⟩
noncomputable def L1314_cp1 : Nat × Nat := t7val% (fastRun pL1314 1 928 (init pL1314) (init pL1314))
theorem L1314_seg1 : segOK pL1314 1 928 (init pL1314) (init pL1314) L1314_cp1.1 L1314_cp1.2 = true := by
  decide +kernel
theorem L1314_fin : (prmOK pL1314 1314 && ptTest pL1314 (runFrom pL1314 (fmask pL1314) (cmask pL1314) (hmask pL1314) 929 385 (true, L1314_cp1.1, L1314_cp1.2)) 1314 657 false) = true := by
  decide +kernel
theorem L1314_ok : RunOK pL1314 1314 (runFrom pL1314 (fmask pL1314) (cmask pL1314) (hmask pL1314) 929 385 (true, L1314_cp1.1, L1314_cp1.2)) ∧ ptTest pL1314 (runFrom pL1314 (fmask pL1314) (cmask pL1314) (hmask pL1314) 929 385 (true, L1314_cp1.1, L1314_cp1.2)) 1314 657 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1314_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1314_fin) true) L1314_seg1) (by decide) rfl L1314_fin ptTest_fst
noncomputable def H1314_cp1 : Nat × Nat := t7val% (fastRun pH1314 1 928 (init pH1314) (init pH1314))
theorem H1314_seg1 : segOK pH1314 1 928 (init pH1314) (init pH1314) H1314_cp1.1 H1314_cp1.2 = true := by
  decide +kernel
theorem H1314_fin : (prmOK pH1314 1314 && ptTest pH1314 (runFrom pH1314 (fmask pH1314) (cmask pH1314) (hmask pH1314) 929 385 (true, H1314_cp1.1, H1314_cp1.2)) 1314 657 true) = true := by
  decide +kernel
theorem H1314_ok : RunOK pH1314 1314 (runFrom pH1314 (fmask pH1314) (cmask pH1314) (hmask pH1314) 929 385 (true, H1314_cp1.1, H1314_cp1.2)) ∧ ptTest pH1314 (runFrom pH1314 (fmask pH1314) (cmask pH1314) (hmask pH1314) 929 385 (true, H1314_cp1.1, H1314_cp1.2)) 1314 657 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1314_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1314_fin) true) H1314_seg1) (by decide) rfl H1314_fin ptTest_fst
noncomputable def I1314_cp1 : Nat × Nat := t7val% (fastRun pI1314 1 928 (init pI1314) (init pI1314))
theorem I1314_seg1 : segOK pI1314 1 928 (init pI1314) (init pI1314) I1314_cp1.1 I1314_cp1.2 = true := by
  decide +kernel
theorem I1314_fin : (prmOK pI1314 1314 && intTest pI1314 (runFrom pI1314 (fmask pI1314) (cmask pI1314) (hmask pI1314) 929 385 (true, I1314_cp1.1, I1314_cp1.2)) 1314 19 true) = true := by
  decide +kernel
theorem I1314_ok : RunOK pI1314 1314 (runFrom pI1314 (fmask pI1314) (cmask pI1314) (hmask pI1314) 929 385 (true, I1314_cp1.1, I1314_cp1.2)) ∧ intTest pI1314 (runFrom pI1314 (fmask pI1314) (cmask pI1314) (hmask pI1314) 929 385 (true, I1314_cp1.1, I1314_cp1.2)) 1314 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1314_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1314_fin) true) I1314_seg1) (by decide) rfl I1314_fin intTest_fst
theorem link1314 : linkOK pL1314 pH1314 pI1314 = true := by decide +kernel
theorem cvx1314 : ConvexBetweenHumps 1314 :=
  cvx_of L1314_ok H1314_ok I1314_ok link1314 (by decide)
theorem cenlink1314 : cenLinkOK pI1314 1314 = true := by decide +kernel
theorem cen1314 : CenterUniqueMin 1314 ∧ DipHyp 1314 ∧ OnePointHyps 1314 :=
  cen_of L1314_ok H1314_ok I1314_ok link1314 cenlink1314

/-! ### The range -/

theorem cvx_1291_1314 {N : ℕ} (h1 : 1291 ≤ N) (h2 : N ≤ 1314) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1302
  · by_cases h4 : N ≤ 1296
    · by_cases h6 : N ≤ 1293
      · by_cases h8 : N ≤ 1291
        · obtain rfl : N = 1291 := by omega
          exact cvx1291
        · by_cases h10 : N ≤ 1292
          · obtain rfl : N = 1292 := by omega
            exact cvx1292
          · obtain rfl : N = 1293 := by omega
            exact cvx1293
      · by_cases h8 : N ≤ 1294
        · obtain rfl : N = 1294 := by omega
          exact cvx1294
        · by_cases h10 : N ≤ 1295
          · obtain rfl : N = 1295 := by omega
            exact cvx1295
          · obtain rfl : N = 1296 := by omega
            exact cvx1296
    · by_cases h6 : N ≤ 1299
      · by_cases h8 : N ≤ 1297
        · obtain rfl : N = 1297 := by omega
          exact cvx1297
        · by_cases h10 : N ≤ 1298
          · obtain rfl : N = 1298 := by omega
            exact cvx1298
          · obtain rfl : N = 1299 := by omega
            exact cvx1299
      · by_cases h8 : N ≤ 1300
        · obtain rfl : N = 1300 := by omega
          exact cvx1300
        · by_cases h10 : N ≤ 1301
          · obtain rfl : N = 1301 := by omega
            exact cvx1301
          · obtain rfl : N = 1302 := by omega
            exact cvx1302
  · by_cases h4 : N ≤ 1308
    · by_cases h6 : N ≤ 1305
      · by_cases h8 : N ≤ 1303
        · obtain rfl : N = 1303 := by omega
          exact cvx1303
        · by_cases h10 : N ≤ 1304
          · obtain rfl : N = 1304 := by omega
            exact cvx1304
          · obtain rfl : N = 1305 := by omega
            exact cvx1305
      · by_cases h8 : N ≤ 1306
        · obtain rfl : N = 1306 := by omega
          exact cvx1306
        · by_cases h10 : N ≤ 1307
          · obtain rfl : N = 1307 := by omega
            exact cvx1307
          · obtain rfl : N = 1308 := by omega
            exact cvx1308
    · by_cases h6 : N ≤ 1311
      · by_cases h8 : N ≤ 1309
        · obtain rfl : N = 1309 := by omega
          exact cvx1309
        · by_cases h10 : N ≤ 1310
          · obtain rfl : N = 1310 := by omega
            exact cvx1310
          · obtain rfl : N = 1311 := by omega
            exact cvx1311
      · by_cases h8 : N ≤ 1312
        · obtain rfl : N = 1312 := by omega
          exact cvx1312
        · by_cases h10 : N ≤ 1313
          · obtain rfl : N = 1313 := by omega
            exact cvx1313
          · obtain rfl : N = 1314 := by omega
            exact cvx1314

theorem cen_1291_1314 {N : ℕ} (h1 : 1291 ≤ N) (h2 : N ≤ 1314) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1302
  · by_cases h4 : N ≤ 1296
    · by_cases h6 : N ≤ 1292
      · obtain rfl : N = 1292 := by omega
        exact cen1292
      · by_cases h8 : N ≤ 1294
        · obtain rfl : N = 1294 := by omega
          exact cen1294
        · obtain rfl : N = 1296 := by omega
          exact cen1296
    · by_cases h6 : N ≤ 1298
      · obtain rfl : N = 1298 := by omega
        exact cen1298
      · by_cases h8 : N ≤ 1300
        · obtain rfl : N = 1300 := by omega
          exact cen1300
        · obtain rfl : N = 1302 := by omega
          exact cen1302
  · by_cases h4 : N ≤ 1308
    · by_cases h6 : N ≤ 1304
      · obtain rfl : N = 1304 := by omega
        exact cen1304
      · by_cases h8 : N ≤ 1306
        · obtain rfl : N = 1306 := by omega
          exact cen1306
        · obtain rfl : N = 1308 := by omega
          exact cen1308
    · by_cases h6 : N ≤ 1310
      · obtain rfl : N = 1310 := by omega
        exact cen1310
      · by_cases h8 : N ≤ 1312
        · obtain rfl : N = 1312 := by omega
          exact cen1312
        · obtain rfl : N = 1314 := by omega
          exact cen1314

end Kagey131.PaperD.T7
