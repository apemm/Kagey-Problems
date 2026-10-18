import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1422, …, 1440` (generated)

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

/-! ### `N = 1422` -/

def pL1422 : Prm := ⟨79, 37, 39, 1424, 11, 18446744073709551616, 129959339096838122, 129959339096838122⟩
def pH1422 : Prm := ⟨80, 38, 39, 1424, 11, 18446744073709551616, 129960438608465898, 129960438608465898⟩
def pI1422 : Prm := ⟨65, 33, 29, 1424, 11, 18446744073709551616, 129959339096838122, 129960438608465898⟩
noncomputable def L1422_cp1 : Nat × Nat := t7val% (fastRun pL1422 1 1005 (init pL1422) (init pL1422))
theorem L1422_seg1 : segOK pL1422 1 1005 (init pL1422) (init pL1422) L1422_cp1.1 L1422_cp1.2 = true := by
  decide +kernel
theorem L1422_fin : (prmOK pL1422 1422 && ptTest pL1422 (runFrom pL1422 (fmask pL1422) (cmask pL1422) (hmask pL1422) 1006 416 (true, L1422_cp1.1, L1422_cp1.2)) 1422 711 false) = true := by
  decide +kernel
theorem L1422_ok : RunOK pL1422 1422 (runFrom pL1422 (fmask pL1422) (cmask pL1422) (hmask pL1422) 1006 416 (true, L1422_cp1.1, L1422_cp1.2)) ∧ ptTest pL1422 (runFrom pL1422 (fmask pL1422) (cmask pL1422) (hmask pL1422) 1006 416 (true, L1422_cp1.1, L1422_cp1.2)) 1422 711 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1422_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1422_fin) true) L1422_seg1) (by decide) rfl L1422_fin ptTest_fst
noncomputable def H1422_cp1 : Nat × Nat := t7val% (fastRun pH1422 1 1005 (init pH1422) (init pH1422))
theorem H1422_seg1 : segOK pH1422 1 1005 (init pH1422) (init pH1422) H1422_cp1.1 H1422_cp1.2 = true := by
  decide +kernel
theorem H1422_fin : (prmOK pH1422 1422 && ptTest pH1422 (runFrom pH1422 (fmask pH1422) (cmask pH1422) (hmask pH1422) 1006 416 (true, H1422_cp1.1, H1422_cp1.2)) 1422 711 true) = true := by
  decide +kernel
theorem H1422_ok : RunOK pH1422 1422 (runFrom pH1422 (fmask pH1422) (cmask pH1422) (hmask pH1422) 1006 416 (true, H1422_cp1.1, H1422_cp1.2)) ∧ ptTest pH1422 (runFrom pH1422 (fmask pH1422) (cmask pH1422) (hmask pH1422) 1006 416 (true, H1422_cp1.1, H1422_cp1.2)) 1422 711 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1422_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1422_fin) true) H1422_seg1) (by decide) rfl H1422_fin ptTest_fst
noncomputable def I1422_cp1 : Nat × Nat := t7val% (fastRun pI1422 1 1005 (init pI1422) (init pI1422))
theorem I1422_seg1 : segOK pI1422 1 1005 (init pI1422) (init pI1422) I1422_cp1.1 I1422_cp1.2 = true := by
  decide +kernel
theorem I1422_fin : (prmOK pI1422 1422 && intTest pI1422 (runFrom pI1422 (fmask pI1422) (cmask pI1422) (hmask pI1422) 1006 416 (true, I1422_cp1.1, I1422_cp1.2)) 1422 20 true) = true := by
  decide +kernel
theorem I1422_ok : RunOK pI1422 1422 (runFrom pI1422 (fmask pI1422) (cmask pI1422) (hmask pI1422) 1006 416 (true, I1422_cp1.1, I1422_cp1.2)) ∧ intTest pI1422 (runFrom pI1422 (fmask pI1422) (cmask pI1422) (hmask pI1422) 1006 416 (true, I1422_cp1.1, I1422_cp1.2)) 1422 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1422_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1422_fin) true) I1422_seg1) (by decide) rfl I1422_fin intTest_fst
theorem link1422 : linkOK pL1422 pH1422 pI1422 = true := by decide +kernel
theorem cvx1422 : ConvexBetweenHumps 1422 :=
  cvx_of L1422_ok H1422_ok I1422_ok link1422 (by decide)
theorem cenlink1422 : cenLinkOK pI1422 1422 = true := by decide +kernel
theorem cen1422 : CenterUniqueMin 1422 ∧ DipHyp 1422 ∧ OnePointHyps 1422 :=
  cen_of L1422_ok H1422_ok I1422_ok link1422 cenlink1422

/-! ### `N = 1423` -/

def pL1423 : Prm := ⟨79, 37, 39, 1425, 11, 18446744073709551616, 129885175173687456, 129885175173687456⟩
def pH1423 : Prm := ⟨79, 37, 39, 1425, 11, 18446744073709551616, 129886274685315232, 129886274685315232⟩
def pI1423 : Prm := ⟨65, 33, 29, 1425, 11, 18446744073709551616, 129885175173687456, 129886274685315232⟩
noncomputable def L1423_cp1 : Nat × Nat := t7val% (fastRun pL1423 1 1005 (init pL1423) (init pL1423))
theorem L1423_seg1 : segOK pL1423 1 1005 (init pL1423) (init pL1423) L1423_cp1.1 L1423_cp1.2 = true := by
  decide +kernel
theorem L1423_fin : (prmOK pL1423 1423 && ptTest pL1423 (runFrom pL1423 (fmask pL1423) (cmask pL1423) (hmask pL1423) 1006 417 (true, L1423_cp1.1, L1423_cp1.2)) 1423 712 false) = true := by
  decide +kernel
theorem L1423_ok : RunOK pL1423 1423 (runFrom pL1423 (fmask pL1423) (cmask pL1423) (hmask pL1423) 1006 417 (true, L1423_cp1.1, L1423_cp1.2)) ∧ ptTest pL1423 (runFrom pL1423 (fmask pL1423) (cmask pL1423) (hmask pL1423) 1006 417 (true, L1423_cp1.1, L1423_cp1.2)) 1423 712 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1423_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1423_fin) true) L1423_seg1) (by decide) rfl L1423_fin ptTest_fst
noncomputable def H1423_cp1 : Nat × Nat := t7val% (fastRun pH1423 1 1005 (init pH1423) (init pH1423))
theorem H1423_seg1 : segOK pH1423 1 1005 (init pH1423) (init pH1423) H1423_cp1.1 H1423_cp1.2 = true := by
  decide +kernel
theorem H1423_fin : (prmOK pH1423 1423 && ptTest pH1423 (runFrom pH1423 (fmask pH1423) (cmask pH1423) (hmask pH1423) 1006 417 (true, H1423_cp1.1, H1423_cp1.2)) 1423 712 true) = true := by
  decide +kernel
theorem H1423_ok : RunOK pH1423 1423 (runFrom pH1423 (fmask pH1423) (cmask pH1423) (hmask pH1423) 1006 417 (true, H1423_cp1.1, H1423_cp1.2)) ∧ ptTest pH1423 (runFrom pH1423 (fmask pH1423) (cmask pH1423) (hmask pH1423) 1006 417 (true, H1423_cp1.1, H1423_cp1.2)) 1423 712 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1423_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1423_fin) true) H1423_seg1) (by decide) rfl H1423_fin ptTest_fst
noncomputable def I1423_cp1 : Nat × Nat := t7val% (fastRun pI1423 1 1005 (init pI1423) (init pI1423))
theorem I1423_seg1 : segOK pI1423 1 1005 (init pI1423) (init pI1423) I1423_cp1.1 I1423_cp1.2 = true := by
  decide +kernel
theorem I1423_fin : (prmOK pI1423 1423 && intTest pI1423 (runFrom pI1423 (fmask pI1423) (cmask pI1423) (hmask pI1423) 1006 417 (true, I1423_cp1.1, I1423_cp1.2)) 1423 20 false) = true := by
  decide +kernel
theorem I1423_ok : RunOK pI1423 1423 (runFrom pI1423 (fmask pI1423) (cmask pI1423) (hmask pI1423) 1006 417 (true, I1423_cp1.1, I1423_cp1.2)) ∧ intTest pI1423 (runFrom pI1423 (fmask pI1423) (cmask pI1423) (hmask pI1423) 1006 417 (true, I1423_cp1.1, I1423_cp1.2)) 1423 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1423_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1423_fin) true) I1423_seg1) (by decide) rfl I1423_fin intTest_fst
theorem link1423 : linkOK pL1423 pH1423 pI1423 = true := by decide +kernel
theorem cvx1423 : ConvexBetweenHumps 1423 :=
  cvx_of L1423_ok H1423_ok I1423_ok link1423 (by decide)

/-! ### `N = 1424` -/

def pL1424 : Prm := ⟨79, 37, 39, 1426, 11, 18446744073709551616, 129811142696740844, 129811142696740844⟩
def pH1424 : Prm := ⟨80, 38, 39, 1426, 11, 18446744073709551616, 129812242208368620, 129812242208368620⟩
def pI1424 : Prm := ⟨65, 33, 29, 1426, 11, 18446744073709551616, 129811142696740844, 129812242208368620⟩
noncomputable def L1424_cp1 : Nat × Nat := t7val% (fastRun pL1424 1 1006 (init pL1424) (init pL1424))
theorem L1424_seg1 : segOK pL1424 1 1006 (init pL1424) (init pL1424) L1424_cp1.1 L1424_cp1.2 = true := by
  decide +kernel
theorem L1424_fin : (prmOK pL1424 1424 && ptTest pL1424 (runFrom pL1424 (fmask pL1424) (cmask pL1424) (hmask pL1424) 1007 417 (true, L1424_cp1.1, L1424_cp1.2)) 1424 712 false) = true := by
  decide +kernel
theorem L1424_ok : RunOK pL1424 1424 (runFrom pL1424 (fmask pL1424) (cmask pL1424) (hmask pL1424) 1007 417 (true, L1424_cp1.1, L1424_cp1.2)) ∧ ptTest pL1424 (runFrom pL1424 (fmask pL1424) (cmask pL1424) (hmask pL1424) 1007 417 (true, L1424_cp1.1, L1424_cp1.2)) 1424 712 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1424_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1424_fin) true) L1424_seg1) (by decide) rfl L1424_fin ptTest_fst
noncomputable def H1424_cp1 : Nat × Nat := t7val% (fastRun pH1424 1 1006 (init pH1424) (init pH1424))
theorem H1424_seg1 : segOK pH1424 1 1006 (init pH1424) (init pH1424) H1424_cp1.1 H1424_cp1.2 = true := by
  decide +kernel
theorem H1424_fin : (prmOK pH1424 1424 && ptTest pH1424 (runFrom pH1424 (fmask pH1424) (cmask pH1424) (hmask pH1424) 1007 417 (true, H1424_cp1.1, H1424_cp1.2)) 1424 712 true) = true := by
  decide +kernel
theorem H1424_ok : RunOK pH1424 1424 (runFrom pH1424 (fmask pH1424) (cmask pH1424) (hmask pH1424) 1007 417 (true, H1424_cp1.1, H1424_cp1.2)) ∧ ptTest pH1424 (runFrom pH1424 (fmask pH1424) (cmask pH1424) (hmask pH1424) 1007 417 (true, H1424_cp1.1, H1424_cp1.2)) 1424 712 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1424_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1424_fin) true) H1424_seg1) (by decide) rfl H1424_fin ptTest_fst
noncomputable def I1424_cp1 : Nat × Nat := t7val% (fastRun pI1424 1 1006 (init pI1424) (init pI1424))
theorem I1424_seg1 : segOK pI1424 1 1006 (init pI1424) (init pI1424) I1424_cp1.1 I1424_cp1.2 = true := by
  decide +kernel
theorem I1424_fin : (prmOK pI1424 1424 && intTest pI1424 (runFrom pI1424 (fmask pI1424) (cmask pI1424) (hmask pI1424) 1007 417 (true, I1424_cp1.1, I1424_cp1.2)) 1424 20 true) = true := by
  decide +kernel
theorem I1424_ok : RunOK pI1424 1424 (runFrom pI1424 (fmask pI1424) (cmask pI1424) (hmask pI1424) 1007 417 (true, I1424_cp1.1, I1424_cp1.2)) ∧ intTest pI1424 (runFrom pI1424 (fmask pI1424) (cmask pI1424) (hmask pI1424) 1007 417 (true, I1424_cp1.1, I1424_cp1.2)) 1424 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1424_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1424_fin) true) I1424_seg1) (by decide) rfl I1424_fin intTest_fst
theorem link1424 : linkOK pL1424 pH1424 pI1424 = true := by decide +kernel
theorem cvx1424 : ConvexBetweenHumps 1424 :=
  cvx_of L1424_ok H1424_ok I1424_ok link1424 (by decide)
theorem cenlink1424 : cenLinkOK pI1424 1424 = true := by decide +kernel
theorem cen1424 : CenterUniqueMin 1424 ∧ DipHyp 1424 ∧ OnePointHyps 1424 :=
  cen_of L1424_ok H1424_ok I1424_ok link1424 cenlink1424

/-! ### `N = 1425` -/

def pL1425 : Prm := ⟨79, 37, 39, 1427, 11, 18446744073709551616, 129737162799840137, 129737162799840137⟩
def pH1425 : Prm := ⟨80, 38, 39, 1427, 11, 18446744073709551616, 129738262311467913, 129738262311467913⟩
def pI1425 : Prm := ⟨65, 33, 29, 1427, 11, 18446744073709551616, 129737162799840137, 129738262311467913⟩
noncomputable def L1425_cp1 : Nat × Nat := t7val% (fastRun pL1425 1 1007 (init pL1425) (init pL1425))
theorem L1425_seg1 : segOK pL1425 1 1007 (init pL1425) (init pL1425) L1425_cp1.1 L1425_cp1.2 = true := by
  decide +kernel
theorem L1425_fin : (prmOK pL1425 1425 && ptTest pL1425 (runFrom pL1425 (fmask pL1425) (cmask pL1425) (hmask pL1425) 1008 417 (true, L1425_cp1.1, L1425_cp1.2)) 1425 713 false) = true := by
  decide +kernel
theorem L1425_ok : RunOK pL1425 1425 (runFrom pL1425 (fmask pL1425) (cmask pL1425) (hmask pL1425) 1008 417 (true, L1425_cp1.1, L1425_cp1.2)) ∧ ptTest pL1425 (runFrom pL1425 (fmask pL1425) (cmask pL1425) (hmask pL1425) 1008 417 (true, L1425_cp1.1, L1425_cp1.2)) 1425 713 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1425_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1425_fin) true) L1425_seg1) (by decide) rfl L1425_fin ptTest_fst
noncomputable def H1425_cp1 : Nat × Nat := t7val% (fastRun pH1425 1 1007 (init pH1425) (init pH1425))
theorem H1425_seg1 : segOK pH1425 1 1007 (init pH1425) (init pH1425) H1425_cp1.1 H1425_cp1.2 = true := by
  decide +kernel
theorem H1425_fin : (prmOK pH1425 1425 && ptTest pH1425 (runFrom pH1425 (fmask pH1425) (cmask pH1425) (hmask pH1425) 1008 417 (true, H1425_cp1.1, H1425_cp1.2)) 1425 713 true) = true := by
  decide +kernel
theorem H1425_ok : RunOK pH1425 1425 (runFrom pH1425 (fmask pH1425) (cmask pH1425) (hmask pH1425) 1008 417 (true, H1425_cp1.1, H1425_cp1.2)) ∧ ptTest pH1425 (runFrom pH1425 (fmask pH1425) (cmask pH1425) (hmask pH1425) 1008 417 (true, H1425_cp1.1, H1425_cp1.2)) 1425 713 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1425_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1425_fin) true) H1425_seg1) (by decide) rfl H1425_fin ptTest_fst
noncomputable def I1425_cp1 : Nat × Nat := t7val% (fastRun pI1425 1 1007 (init pI1425) (init pI1425))
theorem I1425_seg1 : segOK pI1425 1 1007 (init pI1425) (init pI1425) I1425_cp1.1 I1425_cp1.2 = true := by
  decide +kernel
theorem I1425_fin : (prmOK pI1425 1425 && intTest pI1425 (runFrom pI1425 (fmask pI1425) (cmask pI1425) (hmask pI1425) 1008 417 (true, I1425_cp1.1, I1425_cp1.2)) 1425 20 false) = true := by
  decide +kernel
theorem I1425_ok : RunOK pI1425 1425 (runFrom pI1425 (fmask pI1425) (cmask pI1425) (hmask pI1425) 1008 417 (true, I1425_cp1.1, I1425_cp1.2)) ∧ intTest pI1425 (runFrom pI1425 (fmask pI1425) (cmask pI1425) (hmask pI1425) 1008 417 (true, I1425_cp1.1, I1425_cp1.2)) 1425 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1425_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1425_fin) true) I1425_seg1) (by decide) rfl I1425_fin intTest_fst
theorem link1425 : linkOK pL1425 pH1425 pI1425 = true := by decide +kernel
theorem cvx1425 : ConvexBetweenHumps 1425 :=
  cvx_of L1425_ok H1425_ok I1425_ok link1425 (by decide)

/-! ### `N = 1426` -/

def pL1426 : Prm := ⟨79, 37, 39, 1428, 11, 18446744073709551616, 129663313827488009, 129663313827488009⟩
def pH1426 : Prm := ⟨80, 38, 39, 1428, 11, 18446744073709551616, 129664413339115785, 129664413339115785⟩
def pI1426 : Prm := ⟨66, 33, 30, 1428, 11, 18446744073709551616, 129663313827488009, 129664413339115785⟩
noncomputable def L1426_cp1 : Nat × Nat := t7val% (fastRun pL1426 1 1007 (init pL1426) (init pL1426))
theorem L1426_seg1 : segOK pL1426 1 1007 (init pL1426) (init pL1426) L1426_cp1.1 L1426_cp1.2 = true := by
  decide +kernel
theorem L1426_fin : (prmOK pL1426 1426 && ptTest pL1426 (runFrom pL1426 (fmask pL1426) (cmask pL1426) (hmask pL1426) 1008 418 (true, L1426_cp1.1, L1426_cp1.2)) 1426 713 false) = true := by
  decide +kernel
theorem L1426_ok : RunOK pL1426 1426 (runFrom pL1426 (fmask pL1426) (cmask pL1426) (hmask pL1426) 1008 418 (true, L1426_cp1.1, L1426_cp1.2)) ∧ ptTest pL1426 (runFrom pL1426 (fmask pL1426) (cmask pL1426) (hmask pL1426) 1008 418 (true, L1426_cp1.1, L1426_cp1.2)) 1426 713 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1426_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1426_fin) true) L1426_seg1) (by decide) rfl L1426_fin ptTest_fst
noncomputable def H1426_cp1 : Nat × Nat := t7val% (fastRun pH1426 1 1007 (init pH1426) (init pH1426))
theorem H1426_seg1 : segOK pH1426 1 1007 (init pH1426) (init pH1426) H1426_cp1.1 H1426_cp1.2 = true := by
  decide +kernel
theorem H1426_fin : (prmOK pH1426 1426 && ptTest pH1426 (runFrom pH1426 (fmask pH1426) (cmask pH1426) (hmask pH1426) 1008 418 (true, H1426_cp1.1, H1426_cp1.2)) 1426 713 true) = true := by
  decide +kernel
theorem H1426_ok : RunOK pH1426 1426 (runFrom pH1426 (fmask pH1426) (cmask pH1426) (hmask pH1426) 1008 418 (true, H1426_cp1.1, H1426_cp1.2)) ∧ ptTest pH1426 (runFrom pH1426 (fmask pH1426) (cmask pH1426) (hmask pH1426) 1008 418 (true, H1426_cp1.1, H1426_cp1.2)) 1426 713 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1426_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1426_fin) true) H1426_seg1) (by decide) rfl H1426_fin ptTest_fst
noncomputable def I1426_cp1 : Nat × Nat := t7val% (fastRun pI1426 1 1007 (init pI1426) (init pI1426))
theorem I1426_seg1 : segOK pI1426 1 1007 (init pI1426) (init pI1426) I1426_cp1.1 I1426_cp1.2 = true := by
  decide +kernel
theorem I1426_fin : (prmOK pI1426 1426 && intTest pI1426 (runFrom pI1426 (fmask pI1426) (cmask pI1426) (hmask pI1426) 1008 418 (true, I1426_cp1.1, I1426_cp1.2)) 1426 20 true) = true := by
  decide +kernel
theorem I1426_ok : RunOK pI1426 1426 (runFrom pI1426 (fmask pI1426) (cmask pI1426) (hmask pI1426) 1008 418 (true, I1426_cp1.1, I1426_cp1.2)) ∧ intTest pI1426 (runFrom pI1426 (fmask pI1426) (cmask pI1426) (hmask pI1426) 1008 418 (true, I1426_cp1.1, I1426_cp1.2)) 1426 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1426_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1426_fin) true) I1426_seg1) (by decide) rfl I1426_fin intTest_fst
theorem link1426 : linkOK pL1426 pH1426 pI1426 = true := by decide +kernel
theorem cvx1426 : ConvexBetweenHumps 1426 :=
  cvx_of L1426_ok H1426_ok I1426_ok link1426 (by decide)
theorem cenlink1426 : cenLinkOK pI1426 1426 = true := by decide +kernel
theorem cen1426 : CenterUniqueMin 1426 ∧ DipHyp 1426 ∧ OnePointHyps 1426 :=
  cen_of L1426_ok H1426_ok I1426_ok link1426 cenlink1426

/-! ### `N = 1427` -/

def pL1427 : Prm := ⟨80, 38, 39, 1429, 11, 18446744073709551616, 129589517250677451, 129589517250677451⟩
def pH1427 : Prm := ⟨80, 38, 39, 1429, 11, 18446744073709551616, 129590616762305227, 129590616762305227⟩
def pI1427 : Prm := ⟨66, 33, 30, 1429, 11, 18446744073709551616, 129589517250677451, 129590616762305227⟩
noncomputable def L1427_cp1 : Nat × Nat := t7val% (fastRun pL1427 1 1008 (init pL1427) (init pL1427))
theorem L1427_seg1 : segOK pL1427 1 1008 (init pL1427) (init pL1427) L1427_cp1.1 L1427_cp1.2 = true := by
  decide +kernel
theorem L1427_fin : (prmOK pL1427 1427 && ptTest pL1427 (runFrom pL1427 (fmask pL1427) (cmask pL1427) (hmask pL1427) 1009 418 (true, L1427_cp1.1, L1427_cp1.2)) 1427 714 false) = true := by
  decide +kernel
theorem L1427_ok : RunOK pL1427 1427 (runFrom pL1427 (fmask pL1427) (cmask pL1427) (hmask pL1427) 1009 418 (true, L1427_cp1.1, L1427_cp1.2)) ∧ ptTest pL1427 (runFrom pL1427 (fmask pL1427) (cmask pL1427) (hmask pL1427) 1009 418 (true, L1427_cp1.1, L1427_cp1.2)) 1427 714 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1427_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1427_fin) true) L1427_seg1) (by decide) rfl L1427_fin ptTest_fst
noncomputable def H1427_cp1 : Nat × Nat := t7val% (fastRun pH1427 1 1008 (init pH1427) (init pH1427))
theorem H1427_seg1 : segOK pH1427 1 1008 (init pH1427) (init pH1427) H1427_cp1.1 H1427_cp1.2 = true := by
  decide +kernel
theorem H1427_fin : (prmOK pH1427 1427 && ptTest pH1427 (runFrom pH1427 (fmask pH1427) (cmask pH1427) (hmask pH1427) 1009 418 (true, H1427_cp1.1, H1427_cp1.2)) 1427 714 true) = true := by
  decide +kernel
theorem H1427_ok : RunOK pH1427 1427 (runFrom pH1427 (fmask pH1427) (cmask pH1427) (hmask pH1427) 1009 418 (true, H1427_cp1.1, H1427_cp1.2)) ∧ ptTest pH1427 (runFrom pH1427 (fmask pH1427) (cmask pH1427) (hmask pH1427) 1009 418 (true, H1427_cp1.1, H1427_cp1.2)) 1427 714 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1427_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1427_fin) true) H1427_seg1) (by decide) rfl H1427_fin ptTest_fst
noncomputable def I1427_cp1 : Nat × Nat := t7val% (fastRun pI1427 1 1008 (init pI1427) (init pI1427))
theorem I1427_seg1 : segOK pI1427 1 1008 (init pI1427) (init pI1427) I1427_cp1.1 I1427_cp1.2 = true := by
  decide +kernel
theorem I1427_fin : (prmOK pI1427 1427 && intTest pI1427 (runFrom pI1427 (fmask pI1427) (cmask pI1427) (hmask pI1427) 1009 418 (true, I1427_cp1.1, I1427_cp1.2)) 1427 20 false) = true := by
  decide +kernel
theorem I1427_ok : RunOK pI1427 1427 (runFrom pI1427 (fmask pI1427) (cmask pI1427) (hmask pI1427) 1009 418 (true, I1427_cp1.1, I1427_cp1.2)) ∧ intTest pI1427 (runFrom pI1427 (fmask pI1427) (cmask pI1427) (hmask pI1427) 1009 418 (true, I1427_cp1.1, I1427_cp1.2)) 1427 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1427_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1427_fin) true) I1427_seg1) (by decide) rfl I1427_fin intTest_fst
theorem link1427 : linkOK pL1427 pH1427 pI1427 = true := by decide +kernel
theorem cvx1427 : ConvexBetweenHumps 1427 :=
  cvx_of L1427_ok H1427_ok I1427_ok link1427 (by decide)

/-! ### `N = 1428` -/

def pL1428 : Prm := ⟨79, 37, 39, 1430, 11, 18446744073709551616, 129515851079582347, 129515851079582347⟩
def pH1428 : Prm := ⟨80, 38, 39, 1430, 11, 18446744073709551616, 129516950591210123, 129516950591210123⟩
def pI1428 : Prm := ⟨66, 33, 30, 1430, 11, 18446744073709551616, 129515851079582347, 129516950591210123⟩
noncomputable def L1428_cp1 : Nat × Nat := t7val% (fastRun pL1428 1 1009 (init pL1428) (init pL1428))
theorem L1428_seg1 : segOK pL1428 1 1009 (init pL1428) (init pL1428) L1428_cp1.1 L1428_cp1.2 = true := by
  decide +kernel
theorem L1428_fin : (prmOK pL1428 1428 && ptTest pL1428 (runFrom pL1428 (fmask pL1428) (cmask pL1428) (hmask pL1428) 1010 418 (true, L1428_cp1.1, L1428_cp1.2)) 1428 714 false) = true := by
  decide +kernel
theorem L1428_ok : RunOK pL1428 1428 (runFrom pL1428 (fmask pL1428) (cmask pL1428) (hmask pL1428) 1010 418 (true, L1428_cp1.1, L1428_cp1.2)) ∧ ptTest pL1428 (runFrom pL1428 (fmask pL1428) (cmask pL1428) (hmask pL1428) 1010 418 (true, L1428_cp1.1, L1428_cp1.2)) 1428 714 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1428_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1428_fin) true) L1428_seg1) (by decide) rfl L1428_fin ptTest_fst
noncomputable def H1428_cp1 : Nat × Nat := t7val% (fastRun pH1428 1 1009 (init pH1428) (init pH1428))
theorem H1428_seg1 : segOK pH1428 1 1009 (init pH1428) (init pH1428) H1428_cp1.1 H1428_cp1.2 = true := by
  decide +kernel
theorem H1428_fin : (prmOK pH1428 1428 && ptTest pH1428 (runFrom pH1428 (fmask pH1428) (cmask pH1428) (hmask pH1428) 1010 418 (true, H1428_cp1.1, H1428_cp1.2)) 1428 714 true) = true := by
  decide +kernel
theorem H1428_ok : RunOK pH1428 1428 (runFrom pH1428 (fmask pH1428) (cmask pH1428) (hmask pH1428) 1010 418 (true, H1428_cp1.1, H1428_cp1.2)) ∧ ptTest pH1428 (runFrom pH1428 (fmask pH1428) (cmask pH1428) (hmask pH1428) 1010 418 (true, H1428_cp1.1, H1428_cp1.2)) 1428 714 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1428_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1428_fin) true) H1428_seg1) (by decide) rfl H1428_fin ptTest_fst
noncomputable def I1428_cp1 : Nat × Nat := t7val% (fastRun pI1428 1 1009 (init pI1428) (init pI1428))
theorem I1428_seg1 : segOK pI1428 1 1009 (init pI1428) (init pI1428) I1428_cp1.1 I1428_cp1.2 = true := by
  decide +kernel
theorem I1428_fin : (prmOK pI1428 1428 && intTest pI1428 (runFrom pI1428 (fmask pI1428) (cmask pI1428) (hmask pI1428) 1010 418 (true, I1428_cp1.1, I1428_cp1.2)) 1428 20 true) = true := by
  decide +kernel
theorem I1428_ok : RunOK pI1428 1428 (runFrom pI1428 (fmask pI1428) (cmask pI1428) (hmask pI1428) 1010 418 (true, I1428_cp1.1, I1428_cp1.2)) ∧ intTest pI1428 (runFrom pI1428 (fmask pI1428) (cmask pI1428) (hmask pI1428) 1010 418 (true, I1428_cp1.1, I1428_cp1.2)) 1428 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1428_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1428_fin) true) I1428_seg1) (by decide) rfl I1428_fin intTest_fst
theorem link1428 : linkOK pL1428 pH1428 pI1428 = true := by decide +kernel
theorem cvx1428 : ConvexBetweenHumps 1428 :=
  cvx_of L1428_ok H1428_ok I1428_ok link1428 (by decide)
theorem cenlink1428 : cenLinkOK pI1428 1428 = true := by decide +kernel
theorem cen1428 : CenterUniqueMin 1428 ∧ DipHyp 1428 ∧ OnePointHyps 1428 :=
  cen_of L1428_ok H1428_ok I1428_ok link1428 cenlink1428

/-! ### `N = 1429` -/

def pL1429 : Prm := ⟨80, 38, 39, 1431, 11, 18446744073709551616, 129442237120391478, 129442237120391478⟩
def pH1429 : Prm := ⟨80, 38, 39, 1431, 11, 18446744073709551616, 129443336632019254, 129443336632019254⟩
def pI1429 : Prm := ⟨65, 33, 29, 1431, 11, 18446744073709551616, 129442237120391478, 129443336632019254⟩
noncomputable def L1429_cp1 : Nat × Nat := t7val% (fastRun pL1429 1 1009 (init pL1429) (init pL1429))
theorem L1429_seg1 : segOK pL1429 1 1009 (init pL1429) (init pL1429) L1429_cp1.1 L1429_cp1.2 = true := by
  decide +kernel
theorem L1429_fin : (prmOK pL1429 1429 && ptTest pL1429 (runFrom pL1429 (fmask pL1429) (cmask pL1429) (hmask pL1429) 1010 419 (true, L1429_cp1.1, L1429_cp1.2)) 1429 715 false) = true := by
  decide +kernel
theorem L1429_ok : RunOK pL1429 1429 (runFrom pL1429 (fmask pL1429) (cmask pL1429) (hmask pL1429) 1010 419 (true, L1429_cp1.1, L1429_cp1.2)) ∧ ptTest pL1429 (runFrom pL1429 (fmask pL1429) (cmask pL1429) (hmask pL1429) 1010 419 (true, L1429_cp1.1, L1429_cp1.2)) 1429 715 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1429_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1429_fin) true) L1429_seg1) (by decide) rfl L1429_fin ptTest_fst
noncomputable def H1429_cp1 : Nat × Nat := t7val% (fastRun pH1429 1 1009 (init pH1429) (init pH1429))
theorem H1429_seg1 : segOK pH1429 1 1009 (init pH1429) (init pH1429) H1429_cp1.1 H1429_cp1.2 = true := by
  decide +kernel
theorem H1429_fin : (prmOK pH1429 1429 && ptTest pH1429 (runFrom pH1429 (fmask pH1429) (cmask pH1429) (hmask pH1429) 1010 419 (true, H1429_cp1.1, H1429_cp1.2)) 1429 715 true) = true := by
  decide +kernel
theorem H1429_ok : RunOK pH1429 1429 (runFrom pH1429 (fmask pH1429) (cmask pH1429) (hmask pH1429) 1010 419 (true, H1429_cp1.1, H1429_cp1.2)) ∧ ptTest pH1429 (runFrom pH1429 (fmask pH1429) (cmask pH1429) (hmask pH1429) 1010 419 (true, H1429_cp1.1, H1429_cp1.2)) 1429 715 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1429_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1429_fin) true) H1429_seg1) (by decide) rfl H1429_fin ptTest_fst
noncomputable def I1429_cp1 : Nat × Nat := t7val% (fastRun pI1429 1 1009 (init pI1429) (init pI1429))
theorem I1429_seg1 : segOK pI1429 1 1009 (init pI1429) (init pI1429) I1429_cp1.1 I1429_cp1.2 = true := by
  decide +kernel
theorem I1429_fin : (prmOK pI1429 1429 && intTest pI1429 (runFrom pI1429 (fmask pI1429) (cmask pI1429) (hmask pI1429) 1010 419 (true, I1429_cp1.1, I1429_cp1.2)) 1429 20 false) = true := by
  decide +kernel
theorem I1429_ok : RunOK pI1429 1429 (runFrom pI1429 (fmask pI1429) (cmask pI1429) (hmask pI1429) 1010 419 (true, I1429_cp1.1, I1429_cp1.2)) ∧ intTest pI1429 (runFrom pI1429 (fmask pI1429) (cmask pI1429) (hmask pI1429) 1010 419 (true, I1429_cp1.1, I1429_cp1.2)) 1429 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1429_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1429_fin) true) I1429_seg1) (by decide) rfl I1429_fin intTest_fst
theorem link1429 : linkOK pL1429 pH1429 pI1429 = true := by decide +kernel
theorem cvx1429 : ConvexBetweenHumps 1429 :=
  cvx_of L1429_ok H1429_ok I1429_ok link1429 (by decide)

/-! ### `N = 1430` -/

def pL1430 : Prm := ⟨80, 38, 39, 1432, 11, 18446744073709551616, 129368753050868397, 129368753050868397⟩
def pH1430 : Prm := ⟨80, 38, 39, 1432, 11, 18446744073709551616, 129369852562496173, 129369852562496173⟩
def pI1430 : Prm := ⟨66, 33, 30, 1432, 11, 18446744073709551616, 129368753050868397, 129369852562496173⟩
noncomputable def L1430_cp1 : Nat × Nat := t7val% (fastRun pL1430 1 1010 (init pL1430) (init pL1430))
theorem L1430_seg1 : segOK pL1430 1 1010 (init pL1430) (init pL1430) L1430_cp1.1 L1430_cp1.2 = true := by
  decide +kernel
theorem L1430_fin : (prmOK pL1430 1430 && ptTest pL1430 (runFrom pL1430 (fmask pL1430) (cmask pL1430) (hmask pL1430) 1011 419 (true, L1430_cp1.1, L1430_cp1.2)) 1430 715 false) = true := by
  decide +kernel
theorem L1430_ok : RunOK pL1430 1430 (runFrom pL1430 (fmask pL1430) (cmask pL1430) (hmask pL1430) 1011 419 (true, L1430_cp1.1, L1430_cp1.2)) ∧ ptTest pL1430 (runFrom pL1430 (fmask pL1430) (cmask pL1430) (hmask pL1430) 1011 419 (true, L1430_cp1.1, L1430_cp1.2)) 1430 715 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1430_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1430_fin) true) L1430_seg1) (by decide) rfl L1430_fin ptTest_fst
noncomputable def H1430_cp1 : Nat × Nat := t7val% (fastRun pH1430 1 1010 (init pH1430) (init pH1430))
theorem H1430_seg1 : segOK pH1430 1 1010 (init pH1430) (init pH1430) H1430_cp1.1 H1430_cp1.2 = true := by
  decide +kernel
theorem H1430_fin : (prmOK pH1430 1430 && ptTest pH1430 (runFrom pH1430 (fmask pH1430) (cmask pH1430) (hmask pH1430) 1011 419 (true, H1430_cp1.1, H1430_cp1.2)) 1430 715 true) = true := by
  decide +kernel
theorem H1430_ok : RunOK pH1430 1430 (runFrom pH1430 (fmask pH1430) (cmask pH1430) (hmask pH1430) 1011 419 (true, H1430_cp1.1, H1430_cp1.2)) ∧ ptTest pH1430 (runFrom pH1430 (fmask pH1430) (cmask pH1430) (hmask pH1430) 1011 419 (true, H1430_cp1.1, H1430_cp1.2)) 1430 715 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1430_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1430_fin) true) H1430_seg1) (by decide) rfl H1430_fin ptTest_fst
noncomputable def I1430_cp1 : Nat × Nat := t7val% (fastRun pI1430 1 1010 (init pI1430) (init pI1430))
theorem I1430_seg1 : segOK pI1430 1 1010 (init pI1430) (init pI1430) I1430_cp1.1 I1430_cp1.2 = true := by
  decide +kernel
theorem I1430_fin : (prmOK pI1430 1430 && intTest pI1430 (runFrom pI1430 (fmask pI1430) (cmask pI1430) (hmask pI1430) 1011 419 (true, I1430_cp1.1, I1430_cp1.2)) 1430 20 true) = true := by
  decide +kernel
theorem I1430_ok : RunOK pI1430 1430 (runFrom pI1430 (fmask pI1430) (cmask pI1430) (hmask pI1430) 1011 419 (true, I1430_cp1.1, I1430_cp1.2)) ∧ intTest pI1430 (runFrom pI1430 (fmask pI1430) (cmask pI1430) (hmask pI1430) 1011 419 (true, I1430_cp1.1, I1430_cp1.2)) 1430 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1430_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1430_fin) true) I1430_seg1) (by decide) rfl I1430_fin intTest_fst
theorem link1430 : linkOK pL1430 pH1430 pI1430 = true := by decide +kernel
theorem cvx1430 : ConvexBetweenHumps 1430 :=
  cvx_of L1430_ok H1430_ok I1430_ok link1430 (by decide)
theorem cenlink1430 : cenLinkOK pI1430 1430 = true := by decide +kernel
theorem cen1430 : CenterUniqueMin 1430 ∧ DipHyp 1430 ∧ OnePointHyps 1430 :=
  cen_of L1430_ok H1430_ok I1430_ok link1430 cenlink1430

/-! ### `N = 1431` -/

def pL1431 : Prm := ⟨80, 38, 39, 1433, 11, 18446744073709551616, 129295321010442316, 129295321010442316⟩
def pH1431 : Prm := ⟨80, 38, 39, 1433, 11, 18446744073709551616, 129296420522070092, 129296420522070092⟩
def pI1431 : Prm := ⟨66, 33, 30, 1433, 11, 18446744073709551616, 129295321010442316, 129296420522070092⟩
noncomputable def L1431_cp1 : Nat × Nat := t7val% (fastRun pL1431 1 1011 (init pL1431) (init pL1431))
theorem L1431_seg1 : segOK pL1431 1 1011 (init pL1431) (init pL1431) L1431_cp1.1 L1431_cp1.2 = true := by
  decide +kernel
theorem L1431_fin : (prmOK pL1431 1431 && ptTest pL1431 (runFrom pL1431 (fmask pL1431) (cmask pL1431) (hmask pL1431) 1012 419 (true, L1431_cp1.1, L1431_cp1.2)) 1431 716 false) = true := by
  decide +kernel
theorem L1431_ok : RunOK pL1431 1431 (runFrom pL1431 (fmask pL1431) (cmask pL1431) (hmask pL1431) 1012 419 (true, L1431_cp1.1, L1431_cp1.2)) ∧ ptTest pL1431 (runFrom pL1431 (fmask pL1431) (cmask pL1431) (hmask pL1431) 1012 419 (true, L1431_cp1.1, L1431_cp1.2)) 1431 716 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1431_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1431_fin) true) L1431_seg1) (by decide) rfl L1431_fin ptTest_fst
noncomputable def H1431_cp1 : Nat × Nat := t7val% (fastRun pH1431 1 1011 (init pH1431) (init pH1431))
theorem H1431_seg1 : segOK pH1431 1 1011 (init pH1431) (init pH1431) H1431_cp1.1 H1431_cp1.2 = true := by
  decide +kernel
theorem H1431_fin : (prmOK pH1431 1431 && ptTest pH1431 (runFrom pH1431 (fmask pH1431) (cmask pH1431) (hmask pH1431) 1012 419 (true, H1431_cp1.1, H1431_cp1.2)) 1431 716 true) = true := by
  decide +kernel
theorem H1431_ok : RunOK pH1431 1431 (runFrom pH1431 (fmask pH1431) (cmask pH1431) (hmask pH1431) 1012 419 (true, H1431_cp1.1, H1431_cp1.2)) ∧ ptTest pH1431 (runFrom pH1431 (fmask pH1431) (cmask pH1431) (hmask pH1431) 1012 419 (true, H1431_cp1.1, H1431_cp1.2)) 1431 716 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1431_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1431_fin) true) H1431_seg1) (by decide) rfl H1431_fin ptTest_fst
noncomputable def I1431_cp1 : Nat × Nat := t7val% (fastRun pI1431 1 1011 (init pI1431) (init pI1431))
theorem I1431_seg1 : segOK pI1431 1 1011 (init pI1431) (init pI1431) I1431_cp1.1 I1431_cp1.2 = true := by
  decide +kernel
theorem I1431_fin : (prmOK pI1431 1431 && intTest pI1431 (runFrom pI1431 (fmask pI1431) (cmask pI1431) (hmask pI1431) 1012 419 (true, I1431_cp1.1, I1431_cp1.2)) 1431 20 false) = true := by
  decide +kernel
theorem I1431_ok : RunOK pI1431 1431 (runFrom pI1431 (fmask pI1431) (cmask pI1431) (hmask pI1431) 1012 419 (true, I1431_cp1.1, I1431_cp1.2)) ∧ intTest pI1431 (runFrom pI1431 (fmask pI1431) (cmask pI1431) (hmask pI1431) 1012 419 (true, I1431_cp1.1, I1431_cp1.2)) 1431 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1431_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1431_fin) true) I1431_seg1) (by decide) rfl I1431_fin intTest_fst
theorem link1431 : linkOK pL1431 pH1431 pI1431 = true := by decide +kernel
theorem cvx1431 : ConvexBetweenHumps 1431 :=
  cvx_of L1431_ok H1431_ok I1431_ok link1431 (by decide)

/-! ### `N = 1432` -/

def pL1432 : Prm := ⟨80, 38, 39, 1434, 11, 18446744073709551616, 129222018346403371, 129222018346403371⟩
def pH1432 : Prm := ⟨80, 38, 39, 1434, 11, 18446744073709551616, 129223117858031147, 129223117858031147⟩
def pI1432 : Prm := ⟨66, 33, 30, 1434, 11, 18446744073709551616, 129222018346403371, 129223117858031147⟩
noncomputable def L1432_cp1 : Nat × Nat := t7val% (fastRun pL1432 1 1012 (init pL1432) (init pL1432))
theorem L1432_seg1 : segOK pL1432 1 1012 (init pL1432) (init pL1432) L1432_cp1.1 L1432_cp1.2 = true := by
  decide +kernel
theorem L1432_fin : (prmOK pL1432 1432 && ptTest pL1432 (runFrom pL1432 (fmask pL1432) (cmask pL1432) (hmask pL1432) 1013 419 (true, L1432_cp1.1, L1432_cp1.2)) 1432 716 false) = true := by
  decide +kernel
theorem L1432_ok : RunOK pL1432 1432 (runFrom pL1432 (fmask pL1432) (cmask pL1432) (hmask pL1432) 1013 419 (true, L1432_cp1.1, L1432_cp1.2)) ∧ ptTest pL1432 (runFrom pL1432 (fmask pL1432) (cmask pL1432) (hmask pL1432) 1013 419 (true, L1432_cp1.1, L1432_cp1.2)) 1432 716 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1432_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1432_fin) true) L1432_seg1) (by decide) rfl L1432_fin ptTest_fst
noncomputable def H1432_cp1 : Nat × Nat := t7val% (fastRun pH1432 1 1012 (init pH1432) (init pH1432))
theorem H1432_seg1 : segOK pH1432 1 1012 (init pH1432) (init pH1432) H1432_cp1.1 H1432_cp1.2 = true := by
  decide +kernel
theorem H1432_fin : (prmOK pH1432 1432 && ptTest pH1432 (runFrom pH1432 (fmask pH1432) (cmask pH1432) (hmask pH1432) 1013 419 (true, H1432_cp1.1, H1432_cp1.2)) 1432 716 true) = true := by
  decide +kernel
theorem H1432_ok : RunOK pH1432 1432 (runFrom pH1432 (fmask pH1432) (cmask pH1432) (hmask pH1432) 1013 419 (true, H1432_cp1.1, H1432_cp1.2)) ∧ ptTest pH1432 (runFrom pH1432 (fmask pH1432) (cmask pH1432) (hmask pH1432) 1013 419 (true, H1432_cp1.1, H1432_cp1.2)) 1432 716 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1432_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1432_fin) true) H1432_seg1) (by decide) rfl H1432_fin ptTest_fst
noncomputable def I1432_cp1 : Nat × Nat := t7val% (fastRun pI1432 1 1012 (init pI1432) (init pI1432))
theorem I1432_seg1 : segOK pI1432 1 1012 (init pI1432) (init pI1432) I1432_cp1.1 I1432_cp1.2 = true := by
  decide +kernel
theorem I1432_fin : (prmOK pI1432 1432 && intTest pI1432 (runFrom pI1432 (fmask pI1432) (cmask pI1432) (hmask pI1432) 1013 419 (true, I1432_cp1.1, I1432_cp1.2)) 1432 20 true) = true := by
  decide +kernel
theorem I1432_ok : RunOK pI1432 1432 (runFrom pI1432 (fmask pI1432) (cmask pI1432) (hmask pI1432) 1013 419 (true, I1432_cp1.1, I1432_cp1.2)) ∧ intTest pI1432 (runFrom pI1432 (fmask pI1432) (cmask pI1432) (hmask pI1432) 1013 419 (true, I1432_cp1.1, I1432_cp1.2)) 1432 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1432_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1432_fin) true) I1432_seg1) (by decide) rfl I1432_fin intTest_fst
theorem link1432 : linkOK pL1432 pH1432 pI1432 = true := by decide +kernel
theorem cvx1432 : ConvexBetweenHumps 1432 :=
  cvx_of L1432_ok H1432_ok I1432_ok link1432 (by decide)
theorem cenlink1432 : cenLinkOK pI1432 1432 = true := by decide +kernel
theorem cen1432 : CenterUniqueMin 1432 ∧ DipHyp 1432 ∧ OnePointHyps 1432 :=
  cen_of L1432_ok H1432_ok I1432_ok link1432 cenlink1432

/-! ### `N = 1433` -/

def pL1433 : Prm := ⟨80, 38, 39, 1435, 11, 18446744073709551616, 129148767529558082, 129148767529558082⟩
def pH1433 : Prm := ⟨80, 38, 39, 1435, 11, 18446744073709551616, 129149867041185858, 129149867041185858⟩
def pI1433 : Prm := ⟨66, 33, 30, 1435, 11, 18446744073709551616, 129148767529558082, 129149867041185858⟩
noncomputable def L1433_cp1 : Nat × Nat := t7val% (fastRun pL1433 1 1012 (init pL1433) (init pL1433))
theorem L1433_seg1 : segOK pL1433 1 1012 (init pL1433) (init pL1433) L1433_cp1.1 L1433_cp1.2 = true := by
  decide +kernel
theorem L1433_fin : (prmOK pL1433 1433 && ptTest pL1433 (runFrom pL1433 (fmask pL1433) (cmask pL1433) (hmask pL1433) 1013 420 (true, L1433_cp1.1, L1433_cp1.2)) 1433 717 false) = true := by
  decide +kernel
theorem L1433_ok : RunOK pL1433 1433 (runFrom pL1433 (fmask pL1433) (cmask pL1433) (hmask pL1433) 1013 420 (true, L1433_cp1.1, L1433_cp1.2)) ∧ ptTest pL1433 (runFrom pL1433 (fmask pL1433) (cmask pL1433) (hmask pL1433) 1013 420 (true, L1433_cp1.1, L1433_cp1.2)) 1433 717 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1433_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1433_fin) true) L1433_seg1) (by decide) rfl L1433_fin ptTest_fst
noncomputable def H1433_cp1 : Nat × Nat := t7val% (fastRun pH1433 1 1012 (init pH1433) (init pH1433))
theorem H1433_seg1 : segOK pH1433 1 1012 (init pH1433) (init pH1433) H1433_cp1.1 H1433_cp1.2 = true := by
  decide +kernel
theorem H1433_fin : (prmOK pH1433 1433 && ptTest pH1433 (runFrom pH1433 (fmask pH1433) (cmask pH1433) (hmask pH1433) 1013 420 (true, H1433_cp1.1, H1433_cp1.2)) 1433 717 true) = true := by
  decide +kernel
theorem H1433_ok : RunOK pH1433 1433 (runFrom pH1433 (fmask pH1433) (cmask pH1433) (hmask pH1433) 1013 420 (true, H1433_cp1.1, H1433_cp1.2)) ∧ ptTest pH1433 (runFrom pH1433 (fmask pH1433) (cmask pH1433) (hmask pH1433) 1013 420 (true, H1433_cp1.1, H1433_cp1.2)) 1433 717 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1433_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1433_fin) true) H1433_seg1) (by decide) rfl H1433_fin ptTest_fst
noncomputable def I1433_cp1 : Nat × Nat := t7val% (fastRun pI1433 1 1012 (init pI1433) (init pI1433))
theorem I1433_seg1 : segOK pI1433 1 1012 (init pI1433) (init pI1433) I1433_cp1.1 I1433_cp1.2 = true := by
  decide +kernel
theorem I1433_fin : (prmOK pI1433 1433 && intTest pI1433 (runFrom pI1433 (fmask pI1433) (cmask pI1433) (hmask pI1433) 1013 420 (true, I1433_cp1.1, I1433_cp1.2)) 1433 20 false) = true := by
  decide +kernel
theorem I1433_ok : RunOK pI1433 1433 (runFrom pI1433 (fmask pI1433) (cmask pI1433) (hmask pI1433) 1013 420 (true, I1433_cp1.1, I1433_cp1.2)) ∧ intTest pI1433 (runFrom pI1433 (fmask pI1433) (cmask pI1433) (hmask pI1433) 1013 420 (true, I1433_cp1.1, I1433_cp1.2)) 1433 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1433_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1433_fin) true) I1433_seg1) (by decide) rfl I1433_fin intTest_fst
theorem link1433 : linkOK pL1433 pH1433 pI1433 = true := by decide +kernel
theorem cvx1433 : ConvexBetweenHumps 1433 :=
  cvx_of L1433_ok H1433_ok I1433_ok link1433 (by decide)

/-! ### `N = 1434` -/

def pL1434 : Prm := ⟨80, 38, 39, 1436, 11, 18446744073709551616, 129075645578512498, 129075645578512498⟩
def pH1434 : Prm := ⟨80, 38, 39, 1436, 11, 18446744073709551616, 129076745090140274, 129076745090140274⟩
def pI1434 : Prm := ⟨66, 33, 30, 1436, 11, 18446744073709551616, 129075645578512498, 129076745090140274⟩
noncomputable def L1434_cp1 : Nat × Nat := t7val% (fastRun pL1434 1 1013 (init pL1434) (init pL1434))
theorem L1434_seg1 : segOK pL1434 1 1013 (init pL1434) (init pL1434) L1434_cp1.1 L1434_cp1.2 = true := by
  decide +kernel
theorem L1434_fin : (prmOK pL1434 1434 && ptTest pL1434 (runFrom pL1434 (fmask pL1434) (cmask pL1434) (hmask pL1434) 1014 420 (true, L1434_cp1.1, L1434_cp1.2)) 1434 717 false) = true := by
  decide +kernel
theorem L1434_ok : RunOK pL1434 1434 (runFrom pL1434 (fmask pL1434) (cmask pL1434) (hmask pL1434) 1014 420 (true, L1434_cp1.1, L1434_cp1.2)) ∧ ptTest pL1434 (runFrom pL1434 (fmask pL1434) (cmask pL1434) (hmask pL1434) 1014 420 (true, L1434_cp1.1, L1434_cp1.2)) 1434 717 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1434_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1434_fin) true) L1434_seg1) (by decide) rfl L1434_fin ptTest_fst
noncomputable def H1434_cp1 : Nat × Nat := t7val% (fastRun pH1434 1 1013 (init pH1434) (init pH1434))
theorem H1434_seg1 : segOK pH1434 1 1013 (init pH1434) (init pH1434) H1434_cp1.1 H1434_cp1.2 = true := by
  decide +kernel
theorem H1434_fin : (prmOK pH1434 1434 && ptTest pH1434 (runFrom pH1434 (fmask pH1434) (cmask pH1434) (hmask pH1434) 1014 420 (true, H1434_cp1.1, H1434_cp1.2)) 1434 717 true) = true := by
  decide +kernel
theorem H1434_ok : RunOK pH1434 1434 (runFrom pH1434 (fmask pH1434) (cmask pH1434) (hmask pH1434) 1014 420 (true, H1434_cp1.1, H1434_cp1.2)) ∧ ptTest pH1434 (runFrom pH1434 (fmask pH1434) (cmask pH1434) (hmask pH1434) 1014 420 (true, H1434_cp1.1, H1434_cp1.2)) 1434 717 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1434_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1434_fin) true) H1434_seg1) (by decide) rfl H1434_fin ptTest_fst
noncomputable def I1434_cp1 : Nat × Nat := t7val% (fastRun pI1434 1 1013 (init pI1434) (init pI1434))
theorem I1434_seg1 : segOK pI1434 1 1013 (init pI1434) (init pI1434) I1434_cp1.1 I1434_cp1.2 = true := by
  decide +kernel
theorem I1434_fin : (prmOK pI1434 1434 && intTest pI1434 (runFrom pI1434 (fmask pI1434) (cmask pI1434) (hmask pI1434) 1014 420 (true, I1434_cp1.1, I1434_cp1.2)) 1434 20 true) = true := by
  decide +kernel
theorem I1434_ok : RunOK pI1434 1434 (runFrom pI1434 (fmask pI1434) (cmask pI1434) (hmask pI1434) 1014 420 (true, I1434_cp1.1, I1434_cp1.2)) ∧ intTest pI1434 (runFrom pI1434 (fmask pI1434) (cmask pI1434) (hmask pI1434) 1014 420 (true, I1434_cp1.1, I1434_cp1.2)) 1434 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1434_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1434_fin) true) I1434_seg1) (by decide) rfl I1434_fin intTest_fst
theorem link1434 : linkOK pL1434 pH1434 pI1434 = true := by decide +kernel
theorem cvx1434 : ConvexBetweenHumps 1434 :=
  cvx_of L1434_ok H1434_ok I1434_ok link1434 (by decide)
theorem cenlink1434 : cenLinkOK pI1434 1434 = true := by decide +kernel
theorem cen1434 : CenterUniqueMin 1434 ∧ DipHyp 1434 ∧ OnePointHyps 1434 :=
  cen_of L1434_ok H1434_ok I1434_ok link1434 cenlink1434

/-! ### `N = 1435` -/

def pL1435 : Prm := ⟨80, 38, 39, 1437, 11, 18446744073709551616, 129002575293642673, 129002575293642673⟩
def pH1435 : Prm := ⟨80, 38, 39, 1437, 11, 18446744073709551616, 129003674805270449, 129003674805270449⟩
def pI1435 : Prm := ⟨66, 33, 30, 1437, 11, 18446744073709551616, 129002575293642673, 129003674805270449⟩
noncomputable def L1435_cp1 : Nat × Nat := t7val% (fastRun pL1435 1 1014 (init pL1435) (init pL1435))
theorem L1435_seg1 : segOK pL1435 1 1014 (init pL1435) (init pL1435) L1435_cp1.1 L1435_cp1.2 = true := by
  decide +kernel
theorem L1435_fin : (prmOK pL1435 1435 && ptTest pL1435 (runFrom pL1435 (fmask pL1435) (cmask pL1435) (hmask pL1435) 1015 420 (true, L1435_cp1.1, L1435_cp1.2)) 1435 718 false) = true := by
  decide +kernel
theorem L1435_ok : RunOK pL1435 1435 (runFrom pL1435 (fmask pL1435) (cmask pL1435) (hmask pL1435) 1015 420 (true, L1435_cp1.1, L1435_cp1.2)) ∧ ptTest pL1435 (runFrom pL1435 (fmask pL1435) (cmask pL1435) (hmask pL1435) 1015 420 (true, L1435_cp1.1, L1435_cp1.2)) 1435 718 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1435_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1435_fin) true) L1435_seg1) (by decide) rfl L1435_fin ptTest_fst
noncomputable def H1435_cp1 : Nat × Nat := t7val% (fastRun pH1435 1 1014 (init pH1435) (init pH1435))
theorem H1435_seg1 : segOK pH1435 1 1014 (init pH1435) (init pH1435) H1435_cp1.1 H1435_cp1.2 = true := by
  decide +kernel
theorem H1435_fin : (prmOK pH1435 1435 && ptTest pH1435 (runFrom pH1435 (fmask pH1435) (cmask pH1435) (hmask pH1435) 1015 420 (true, H1435_cp1.1, H1435_cp1.2)) 1435 718 true) = true := by
  decide +kernel
theorem H1435_ok : RunOK pH1435 1435 (runFrom pH1435 (fmask pH1435) (cmask pH1435) (hmask pH1435) 1015 420 (true, H1435_cp1.1, H1435_cp1.2)) ∧ ptTest pH1435 (runFrom pH1435 (fmask pH1435) (cmask pH1435) (hmask pH1435) 1015 420 (true, H1435_cp1.1, H1435_cp1.2)) 1435 718 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1435_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1435_fin) true) H1435_seg1) (by decide) rfl H1435_fin ptTest_fst
noncomputable def I1435_cp1 : Nat × Nat := t7val% (fastRun pI1435 1 1014 (init pI1435) (init pI1435))
theorem I1435_seg1 : segOK pI1435 1 1014 (init pI1435) (init pI1435) I1435_cp1.1 I1435_cp1.2 = true := by
  decide +kernel
theorem I1435_fin : (prmOK pI1435 1435 && intTest pI1435 (runFrom pI1435 (fmask pI1435) (cmask pI1435) (hmask pI1435) 1015 420 (true, I1435_cp1.1, I1435_cp1.2)) 1435 20 false) = true := by
  decide +kernel
theorem I1435_ok : RunOK pI1435 1435 (runFrom pI1435 (fmask pI1435) (cmask pI1435) (hmask pI1435) 1015 420 (true, I1435_cp1.1, I1435_cp1.2)) ∧ intTest pI1435 (runFrom pI1435 (fmask pI1435) (cmask pI1435) (hmask pI1435) 1015 420 (true, I1435_cp1.1, I1435_cp1.2)) 1435 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1435_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1435_fin) true) I1435_seg1) (by decide) rfl I1435_fin intTest_fst
theorem link1435 : linkOK pL1435 pH1435 pI1435 = true := by decide +kernel
theorem cvx1435 : ConvexBetweenHumps 1435 :=
  cvx_of L1435_ok H1435_ok I1435_ok link1435 (by decide)

/-! ### `N = 1436` -/

def pL1436 : Prm := ⟨80, 38, 39, 1438, 11, 18446744073709551616, 128929633366715241, 128929633366715241⟩
def pH1436 : Prm := ⟨80, 38, 39, 1438, 11, 18446744073709551616, 128930732878343017, 128930732878343017⟩
def pI1436 : Prm := ⟨66, 33, 30, 1438, 11, 18446744073709551616, 128929633366715241, 128930732878343017⟩
noncomputable def L1436_cp1 : Nat × Nat := t7val% (fastRun pL1436 1 1014 (init pL1436) (init pL1436))
theorem L1436_seg1 : segOK pL1436 1 1014 (init pL1436) (init pL1436) L1436_cp1.1 L1436_cp1.2 = true := by
  decide +kernel
theorem L1436_fin : (prmOK pL1436 1436 && ptTest pL1436 (runFrom pL1436 (fmask pL1436) (cmask pL1436) (hmask pL1436) 1015 421 (true, L1436_cp1.1, L1436_cp1.2)) 1436 718 false) = true := by
  decide +kernel
theorem L1436_ok : RunOK pL1436 1436 (runFrom pL1436 (fmask pL1436) (cmask pL1436) (hmask pL1436) 1015 421 (true, L1436_cp1.1, L1436_cp1.2)) ∧ ptTest pL1436 (runFrom pL1436 (fmask pL1436) (cmask pL1436) (hmask pL1436) 1015 421 (true, L1436_cp1.1, L1436_cp1.2)) 1436 718 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1436_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1436_fin) true) L1436_seg1) (by decide) rfl L1436_fin ptTest_fst
noncomputable def H1436_cp1 : Nat × Nat := t7val% (fastRun pH1436 1 1014 (init pH1436) (init pH1436))
theorem H1436_seg1 : segOK pH1436 1 1014 (init pH1436) (init pH1436) H1436_cp1.1 H1436_cp1.2 = true := by
  decide +kernel
theorem H1436_fin : (prmOK pH1436 1436 && ptTest pH1436 (runFrom pH1436 (fmask pH1436) (cmask pH1436) (hmask pH1436) 1015 421 (true, H1436_cp1.1, H1436_cp1.2)) 1436 718 true) = true := by
  decide +kernel
theorem H1436_ok : RunOK pH1436 1436 (runFrom pH1436 (fmask pH1436) (cmask pH1436) (hmask pH1436) 1015 421 (true, H1436_cp1.1, H1436_cp1.2)) ∧ ptTest pH1436 (runFrom pH1436 (fmask pH1436) (cmask pH1436) (hmask pH1436) 1015 421 (true, H1436_cp1.1, H1436_cp1.2)) 1436 718 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1436_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1436_fin) true) H1436_seg1) (by decide) rfl H1436_fin ptTest_fst
noncomputable def I1436_cp1 : Nat × Nat := t7val% (fastRun pI1436 1 1014 (init pI1436) (init pI1436))
theorem I1436_seg1 : segOK pI1436 1 1014 (init pI1436) (init pI1436) I1436_cp1.1 I1436_cp1.2 = true := by
  decide +kernel
theorem I1436_fin : (prmOK pI1436 1436 && intTest pI1436 (runFrom pI1436 (fmask pI1436) (cmask pI1436) (hmask pI1436) 1015 421 (true, I1436_cp1.1, I1436_cp1.2)) 1436 20 true) = true := by
  decide +kernel
theorem I1436_ok : RunOK pI1436 1436 (runFrom pI1436 (fmask pI1436) (cmask pI1436) (hmask pI1436) 1015 421 (true, I1436_cp1.1, I1436_cp1.2)) ∧ intTest pI1436 (runFrom pI1436 (fmask pI1436) (cmask pI1436) (hmask pI1436) 1015 421 (true, I1436_cp1.1, I1436_cp1.2)) 1436 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1436_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1436_fin) true) I1436_seg1) (by decide) rfl I1436_fin intTest_fst
theorem link1436 : linkOK pL1436 pH1436 pI1436 = true := by decide +kernel
theorem cvx1436 : ConvexBetweenHumps 1436 :=
  cvx_of L1436_ok H1436_ok I1436_ok link1436 (by decide)
theorem cenlink1436 : cenLinkOK pI1436 1436 = true := by decide +kernel
theorem cen1436 : CenterUniqueMin 1436 ∧ DipHyp 1436 ∧ OnePointHyps 1436 :=
  cen_of L1436_ok H1436_ok I1436_ok link1436 cenlink1436

/-! ### `N = 1437` -/

def pL1437 : Prm := ⟨80, 38, 39, 1439, 11, 18446744073709551616, 128856742925794218, 128856742925794218⟩
def pH1437 : Prm := ⟨80, 38, 39, 1439, 11, 18446744073709551616, 128857842437421994, 128857842437421994⟩
def pI1437 : Prm := ⟨66, 33, 30, 1439, 11, 18446744073709551616, 128856742925794218, 128857842437421994⟩
noncomputable def L1437_cp1 : Nat × Nat := t7val% (fastRun pL1437 1 1015 (init pL1437) (init pL1437))
theorem L1437_seg1 : segOK pL1437 1 1015 (init pL1437) (init pL1437) L1437_cp1.1 L1437_cp1.2 = true := by
  decide +kernel
theorem L1437_fin : (prmOK pL1437 1437 && ptTest pL1437 (runFrom pL1437 (fmask pL1437) (cmask pL1437) (hmask pL1437) 1016 421 (true, L1437_cp1.1, L1437_cp1.2)) 1437 719 false) = true := by
  decide +kernel
theorem L1437_ok : RunOK pL1437 1437 (runFrom pL1437 (fmask pL1437) (cmask pL1437) (hmask pL1437) 1016 421 (true, L1437_cp1.1, L1437_cp1.2)) ∧ ptTest pL1437 (runFrom pL1437 (fmask pL1437) (cmask pL1437) (hmask pL1437) 1016 421 (true, L1437_cp1.1, L1437_cp1.2)) 1437 719 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1437_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1437_fin) true) L1437_seg1) (by decide) rfl L1437_fin ptTest_fst
noncomputable def H1437_cp1 : Nat × Nat := t7val% (fastRun pH1437 1 1015 (init pH1437) (init pH1437))
theorem H1437_seg1 : segOK pH1437 1 1015 (init pH1437) (init pH1437) H1437_cp1.1 H1437_cp1.2 = true := by
  decide +kernel
theorem H1437_fin : (prmOK pH1437 1437 && ptTest pH1437 (runFrom pH1437 (fmask pH1437) (cmask pH1437) (hmask pH1437) 1016 421 (true, H1437_cp1.1, H1437_cp1.2)) 1437 719 true) = true := by
  decide +kernel
theorem H1437_ok : RunOK pH1437 1437 (runFrom pH1437 (fmask pH1437) (cmask pH1437) (hmask pH1437) 1016 421 (true, H1437_cp1.1, H1437_cp1.2)) ∧ ptTest pH1437 (runFrom pH1437 (fmask pH1437) (cmask pH1437) (hmask pH1437) 1016 421 (true, H1437_cp1.1, H1437_cp1.2)) 1437 719 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1437_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1437_fin) true) H1437_seg1) (by decide) rfl H1437_fin ptTest_fst
noncomputable def I1437_cp1 : Nat × Nat := t7val% (fastRun pI1437 1 1015 (init pI1437) (init pI1437))
theorem I1437_seg1 : segOK pI1437 1 1015 (init pI1437) (init pI1437) I1437_cp1.1 I1437_cp1.2 = true := by
  decide +kernel
theorem I1437_fin : (prmOK pI1437 1437 && intTest pI1437 (runFrom pI1437 (fmask pI1437) (cmask pI1437) (hmask pI1437) 1016 421 (true, I1437_cp1.1, I1437_cp1.2)) 1437 20 false) = true := by
  decide +kernel
theorem I1437_ok : RunOK pI1437 1437 (runFrom pI1437 (fmask pI1437) (cmask pI1437) (hmask pI1437) 1016 421 (true, I1437_cp1.1, I1437_cp1.2)) ∧ intTest pI1437 (runFrom pI1437 (fmask pI1437) (cmask pI1437) (hmask pI1437) 1016 421 (true, I1437_cp1.1, I1437_cp1.2)) 1437 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1437_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1437_fin) true) I1437_seg1) (by decide) rfl I1437_fin intTest_fst
theorem link1437 : linkOK pL1437 pH1437 pI1437 = true := by decide +kernel
theorem cvx1437 : ConvexBetweenHumps 1437 :=
  cvx_of L1437_ok H1437_ok I1437_ok link1437 (by decide)

/-! ### `N = 1438` -/

def pL1438 : Prm := ⟨80, 38, 39, 1440, 11, 18446744073709551616, 128783980337651503, 128783980337651503⟩
def pH1438 : Prm := ⟨80, 38, 39, 1440, 11, 18446744073709551616, 128785079849279279, 128785079849279279⟩
def pI1438 : Prm := ⟨66, 33, 30, 1440, 11, 18446744073709551616, 128783980337651503, 128785079849279279⟩
noncomputable def L1438_cp1 : Nat × Nat := t7val% (fastRun pL1438 1 1016 (init pL1438) (init pL1438))
theorem L1438_seg1 : segOK pL1438 1 1016 (init pL1438) (init pL1438) L1438_cp1.1 L1438_cp1.2 = true := by
  decide +kernel
theorem L1438_fin : (prmOK pL1438 1438 && ptTest pL1438 (runFrom pL1438 (fmask pL1438) (cmask pL1438) (hmask pL1438) 1017 421 (true, L1438_cp1.1, L1438_cp1.2)) 1438 719 false) = true := by
  decide +kernel
theorem L1438_ok : RunOK pL1438 1438 (runFrom pL1438 (fmask pL1438) (cmask pL1438) (hmask pL1438) 1017 421 (true, L1438_cp1.1, L1438_cp1.2)) ∧ ptTest pL1438 (runFrom pL1438 (fmask pL1438) (cmask pL1438) (hmask pL1438) 1017 421 (true, L1438_cp1.1, L1438_cp1.2)) 1438 719 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1438_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1438_fin) true) L1438_seg1) (by decide) rfl L1438_fin ptTest_fst
noncomputable def H1438_cp1 : Nat × Nat := t7val% (fastRun pH1438 1 1016 (init pH1438) (init pH1438))
theorem H1438_seg1 : segOK pH1438 1 1016 (init pH1438) (init pH1438) H1438_cp1.1 H1438_cp1.2 = true := by
  decide +kernel
theorem H1438_fin : (prmOK pH1438 1438 && ptTest pH1438 (runFrom pH1438 (fmask pH1438) (cmask pH1438) (hmask pH1438) 1017 421 (true, H1438_cp1.1, H1438_cp1.2)) 1438 719 true) = true := by
  decide +kernel
theorem H1438_ok : RunOK pH1438 1438 (runFrom pH1438 (fmask pH1438) (cmask pH1438) (hmask pH1438) 1017 421 (true, H1438_cp1.1, H1438_cp1.2)) ∧ ptTest pH1438 (runFrom pH1438 (fmask pH1438) (cmask pH1438) (hmask pH1438) 1017 421 (true, H1438_cp1.1, H1438_cp1.2)) 1438 719 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1438_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1438_fin) true) H1438_seg1) (by decide) rfl H1438_fin ptTest_fst
noncomputable def I1438_cp1 : Nat × Nat := t7val% (fastRun pI1438 1 1016 (init pI1438) (init pI1438))
theorem I1438_seg1 : segOK pI1438 1 1016 (init pI1438) (init pI1438) I1438_cp1.1 I1438_cp1.2 = true := by
  decide +kernel
theorem I1438_fin : (prmOK pI1438 1438 && intTest pI1438 (runFrom pI1438 (fmask pI1438) (cmask pI1438) (hmask pI1438) 1017 421 (true, I1438_cp1.1, I1438_cp1.2)) 1438 20 true) = true := by
  decide +kernel
theorem I1438_ok : RunOK pI1438 1438 (runFrom pI1438 (fmask pI1438) (cmask pI1438) (hmask pI1438) 1017 421 (true, I1438_cp1.1, I1438_cp1.2)) ∧ intTest pI1438 (runFrom pI1438 (fmask pI1438) (cmask pI1438) (hmask pI1438) 1017 421 (true, I1438_cp1.1, I1438_cp1.2)) 1438 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1438_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1438_fin) true) I1438_seg1) (by decide) rfl I1438_fin intTest_fst
theorem link1438 : linkOK pL1438 pH1438 pI1438 = true := by decide +kernel
theorem cvx1438 : ConvexBetweenHumps 1438 :=
  cvx_of L1438_ok H1438_ok I1438_ok link1438 (by decide)
theorem cenlink1438 : cenLinkOK pI1438 1438 = true := by decide +kernel
theorem cen1438 : CenterUniqueMin 1438 ∧ DipHyp 1438 ∧ OnePointHyps 1438 :=
  cen_of L1438_ok H1438_ok I1438_ok link1438 cenlink1438

/-! ### `N = 1439` -/

def pL1439 : Prm := ⟨80, 38, 39, 1441, 11, 18446744073709551616, 128711269056175949, 128711269056175949⟩
def pH1439 : Prm := ⟨80, 38, 39, 1441, 11, 18446744073709551616, 128712368567803725, 128712368567803725⟩
def pI1439 : Prm := ⟨66, 33, 30, 1441, 11, 18446744073709551616, 128711269056175949, 128712368567803725⟩
noncomputable def L1439_cp1 : Nat × Nat := t7val% (fastRun pL1439 1 1017 (init pL1439) (init pL1439))
theorem L1439_seg1 : segOK pL1439 1 1017 (init pL1439) (init pL1439) L1439_cp1.1 L1439_cp1.2 = true := by
  decide +kernel
theorem L1439_fin : (prmOK pL1439 1439 && ptTest pL1439 (runFrom pL1439 (fmask pL1439) (cmask pL1439) (hmask pL1439) 1018 421 (true, L1439_cp1.1, L1439_cp1.2)) 1439 720 false) = true := by
  decide +kernel
theorem L1439_ok : RunOK pL1439 1439 (runFrom pL1439 (fmask pL1439) (cmask pL1439) (hmask pL1439) 1018 421 (true, L1439_cp1.1, L1439_cp1.2)) ∧ ptTest pL1439 (runFrom pL1439 (fmask pL1439) (cmask pL1439) (hmask pL1439) 1018 421 (true, L1439_cp1.1, L1439_cp1.2)) 1439 720 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1439_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1439_fin) true) L1439_seg1) (by decide) rfl L1439_fin ptTest_fst
noncomputable def H1439_cp1 : Nat × Nat := t7val% (fastRun pH1439 1 1017 (init pH1439) (init pH1439))
theorem H1439_seg1 : segOK pH1439 1 1017 (init pH1439) (init pH1439) H1439_cp1.1 H1439_cp1.2 = true := by
  decide +kernel
theorem H1439_fin : (prmOK pH1439 1439 && ptTest pH1439 (runFrom pH1439 (fmask pH1439) (cmask pH1439) (hmask pH1439) 1018 421 (true, H1439_cp1.1, H1439_cp1.2)) 1439 720 true) = true := by
  decide +kernel
theorem H1439_ok : RunOK pH1439 1439 (runFrom pH1439 (fmask pH1439) (cmask pH1439) (hmask pH1439) 1018 421 (true, H1439_cp1.1, H1439_cp1.2)) ∧ ptTest pH1439 (runFrom pH1439 (fmask pH1439) (cmask pH1439) (hmask pH1439) 1018 421 (true, H1439_cp1.1, H1439_cp1.2)) 1439 720 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1439_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1439_fin) true) H1439_seg1) (by decide) rfl H1439_fin ptTest_fst
noncomputable def I1439_cp1 : Nat × Nat := t7val% (fastRun pI1439 1 1017 (init pI1439) (init pI1439))
theorem I1439_seg1 : segOK pI1439 1 1017 (init pI1439) (init pI1439) I1439_cp1.1 I1439_cp1.2 = true := by
  decide +kernel
theorem I1439_fin : (prmOK pI1439 1439 && intTest pI1439 (runFrom pI1439 (fmask pI1439) (cmask pI1439) (hmask pI1439) 1018 421 (true, I1439_cp1.1, I1439_cp1.2)) 1439 20 false) = true := by
  decide +kernel
theorem I1439_ok : RunOK pI1439 1439 (runFrom pI1439 (fmask pI1439) (cmask pI1439) (hmask pI1439) 1018 421 (true, I1439_cp1.1, I1439_cp1.2)) ∧ intTest pI1439 (runFrom pI1439 (fmask pI1439) (cmask pI1439) (hmask pI1439) 1018 421 (true, I1439_cp1.1, I1439_cp1.2)) 1439 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1439_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1439_fin) true) I1439_seg1) (by decide) rfl I1439_fin intTest_fst
theorem link1439 : linkOK pL1439 pH1439 pI1439 = true := by decide +kernel
theorem cvx1439 : ConvexBetweenHumps 1439 :=
  cvx_of L1439_ok H1439_ok I1439_ok link1439 (by decide)

/-! ### `N = 1440` -/

def pL1440 : Prm := ⟨80, 38, 39, 1442, 11, 18446744073709551616, 128638685125007842, 128638685125007842⟩
def pH1440 : Prm := ⟨80, 38, 39, 1442, 11, 18446744073709551616, 128639784636635618, 128639784636635618⟩
def pI1440 : Prm := ⟨66, 33, 30, 1442, 11, 18446744073709551616, 128638685125007842, 128639784636635618⟩
noncomputable def L1440_cp1 : Nat × Nat := t7val% (fastRun pL1440 1 1017 (init pL1440) (init pL1440))
theorem L1440_seg1 : segOK pL1440 1 1017 (init pL1440) (init pL1440) L1440_cp1.1 L1440_cp1.2 = true := by
  decide +kernel
theorem L1440_fin : (prmOK pL1440 1440 && ptTest pL1440 (runFrom pL1440 (fmask pL1440) (cmask pL1440) (hmask pL1440) 1018 422 (true, L1440_cp1.1, L1440_cp1.2)) 1440 720 false) = true := by
  decide +kernel
theorem L1440_ok : RunOK pL1440 1440 (runFrom pL1440 (fmask pL1440) (cmask pL1440) (hmask pL1440) 1018 422 (true, L1440_cp1.1, L1440_cp1.2)) ∧ ptTest pL1440 (runFrom pL1440 (fmask pL1440) (cmask pL1440) (hmask pL1440) 1018 422 (true, L1440_cp1.1, L1440_cp1.2)) 1440 720 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1440_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1440_fin) true) L1440_seg1) (by decide) rfl L1440_fin ptTest_fst
noncomputable def H1440_cp1 : Nat × Nat := t7val% (fastRun pH1440 1 1017 (init pH1440) (init pH1440))
theorem H1440_seg1 : segOK pH1440 1 1017 (init pH1440) (init pH1440) H1440_cp1.1 H1440_cp1.2 = true := by
  decide +kernel
theorem H1440_fin : (prmOK pH1440 1440 && ptTest pH1440 (runFrom pH1440 (fmask pH1440) (cmask pH1440) (hmask pH1440) 1018 422 (true, H1440_cp1.1, H1440_cp1.2)) 1440 720 true) = true := by
  decide +kernel
theorem H1440_ok : RunOK pH1440 1440 (runFrom pH1440 (fmask pH1440) (cmask pH1440) (hmask pH1440) 1018 422 (true, H1440_cp1.1, H1440_cp1.2)) ∧ ptTest pH1440 (runFrom pH1440 (fmask pH1440) (cmask pH1440) (hmask pH1440) 1018 422 (true, H1440_cp1.1, H1440_cp1.2)) 1440 720 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1440_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1440_fin) true) H1440_seg1) (by decide) rfl H1440_fin ptTest_fst
noncomputable def I1440_cp1 : Nat × Nat := t7val% (fastRun pI1440 1 1017 (init pI1440) (init pI1440))
theorem I1440_seg1 : segOK pI1440 1 1017 (init pI1440) (init pI1440) I1440_cp1.1 I1440_cp1.2 = true := by
  decide +kernel
theorem I1440_fin : (prmOK pI1440 1440 && intTest pI1440 (runFrom pI1440 (fmask pI1440) (cmask pI1440) (hmask pI1440) 1018 422 (true, I1440_cp1.1, I1440_cp1.2)) 1440 20 true) = true := by
  decide +kernel
theorem I1440_ok : RunOK pI1440 1440 (runFrom pI1440 (fmask pI1440) (cmask pI1440) (hmask pI1440) 1018 422 (true, I1440_cp1.1, I1440_cp1.2)) ∧ intTest pI1440 (runFrom pI1440 (fmask pI1440) (cmask pI1440) (hmask pI1440) 1018 422 (true, I1440_cp1.1, I1440_cp1.2)) 1440 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1440_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1440_fin) true) I1440_seg1) (by decide) rfl I1440_fin intTest_fst
theorem link1440 : linkOK pL1440 pH1440 pI1440 = true := by decide +kernel
theorem cvx1440 : ConvexBetweenHumps 1440 :=
  cvx_of L1440_ok H1440_ok I1440_ok link1440 (by decide)
theorem cenlink1440 : cenLinkOK pI1440 1440 = true := by decide +kernel
theorem cen1440 : CenterUniqueMin 1440 ∧ DipHyp 1440 ∧ OnePointHyps 1440 :=
  cen_of L1440_ok H1440_ok I1440_ok link1440 cenlink1440

/-! ### The range -/

theorem cvx_1422_1440 {N : ℕ} (h1 : 1422 ≤ N) (h2 : N ≤ 1440) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1430
  · by_cases h4 : N ≤ 1425
    · by_cases h6 : N ≤ 1423
      · by_cases h8 : N ≤ 1422
        · obtain rfl : N = 1422 := by omega
          exact cvx1422
        · obtain rfl : N = 1423 := by omega
          exact cvx1423
      · by_cases h8 : N ≤ 1424
        · obtain rfl : N = 1424 := by omega
          exact cvx1424
        · obtain rfl : N = 1425 := by omega
          exact cvx1425
    · by_cases h6 : N ≤ 1427
      · by_cases h8 : N ≤ 1426
        · obtain rfl : N = 1426 := by omega
          exact cvx1426
        · obtain rfl : N = 1427 := by omega
          exact cvx1427
      · by_cases h8 : N ≤ 1428
        · obtain rfl : N = 1428 := by omega
          exact cvx1428
        · by_cases h10 : N ≤ 1429
          · obtain rfl : N = 1429 := by omega
            exact cvx1429
          · obtain rfl : N = 1430 := by omega
            exact cvx1430
  · by_cases h4 : N ≤ 1435
    · by_cases h6 : N ≤ 1432
      · by_cases h8 : N ≤ 1431
        · obtain rfl : N = 1431 := by omega
          exact cvx1431
        · obtain rfl : N = 1432 := by omega
          exact cvx1432
      · by_cases h8 : N ≤ 1433
        · obtain rfl : N = 1433 := by omega
          exact cvx1433
        · by_cases h10 : N ≤ 1434
          · obtain rfl : N = 1434 := by omega
            exact cvx1434
          · obtain rfl : N = 1435 := by omega
            exact cvx1435
    · by_cases h6 : N ≤ 1437
      · by_cases h8 : N ≤ 1436
        · obtain rfl : N = 1436 := by omega
          exact cvx1436
        · obtain rfl : N = 1437 := by omega
          exact cvx1437
      · by_cases h8 : N ≤ 1438
        · obtain rfl : N = 1438 := by omega
          exact cvx1438
        · by_cases h10 : N ≤ 1439
          · obtain rfl : N = 1439 := by omega
            exact cvx1439
          · obtain rfl : N = 1440 := by omega
            exact cvx1440

theorem cen_1422_1440 {N : ℕ} (h1 : 1422 ≤ N) (h2 : N ≤ 1440) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1430
  · by_cases h4 : N ≤ 1424
    · by_cases h6 : N ≤ 1422
      · obtain rfl : N = 1422 := by omega
        exact cen1422
      · obtain rfl : N = 1424 := by omega
        exact cen1424
    · by_cases h6 : N ≤ 1426
      · obtain rfl : N = 1426 := by omega
        exact cen1426
      · by_cases h8 : N ≤ 1428
        · obtain rfl : N = 1428 := by omega
          exact cen1428
        · obtain rfl : N = 1430 := by omega
          exact cen1430
  · by_cases h4 : N ≤ 1434
    · by_cases h6 : N ≤ 1432
      · obtain rfl : N = 1432 := by omega
        exact cen1432
      · obtain rfl : N = 1434 := by omega
        exact cen1434
    · by_cases h6 : N ≤ 1436
      · obtain rfl : N = 1436 := by omega
        exact cen1436
      · by_cases h8 : N ≤ 1438
        · obtain rfl : N = 1438 := by omega
          exact cen1438
        · obtain rfl : N = 1440 := by omega
          exact cen1440

end Kagey131.PaperD.T7
