import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1381, …, 1401` (generated)

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

/-! ### `N = 1381` -/

def pL1381 : Prm := ⟨79, 37, 39, 1383, 11, 18446744073709551616, 133080741429616833, 133080741429616833⟩
def pH1381 : Prm := ⟨79, 37, 39, 1383, 11, 18446744073709551616, 133081840941244609, 133081840941244609⟩
def pI1381 : Prm := ⟨67, 32, 32, 1383, 11, 18446744073709551616, 133080741429616833, 133081840941244609⟩
noncomputable def L1381_cp1 : Nat × Nat := t7val% (fastRun pL1381 1 976 (init pL1381) (init pL1381))
theorem L1381_seg1 : segOK pL1381 1 976 (init pL1381) (init pL1381) L1381_cp1.1 L1381_cp1.2 = true := by
  decide +kernel
theorem L1381_fin : (prmOK pL1381 1381 && ptTest pL1381 (runFrom pL1381 (fmask pL1381) (cmask pL1381) (hmask pL1381) 977 404 (true, L1381_cp1.1, L1381_cp1.2)) 1381 691 false) = true := by
  decide +kernel
theorem L1381_ok : RunOK pL1381 1381 (runFrom pL1381 (fmask pL1381) (cmask pL1381) (hmask pL1381) 977 404 (true, L1381_cp1.1, L1381_cp1.2)) ∧ ptTest pL1381 (runFrom pL1381 (fmask pL1381) (cmask pL1381) (hmask pL1381) 977 404 (true, L1381_cp1.1, L1381_cp1.2)) 1381 691 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1381_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1381_fin) true) L1381_seg1) (by decide) rfl L1381_fin ptTest_fst
noncomputable def H1381_cp1 : Nat × Nat := t7val% (fastRun pH1381 1 976 (init pH1381) (init pH1381))
theorem H1381_seg1 : segOK pH1381 1 976 (init pH1381) (init pH1381) H1381_cp1.1 H1381_cp1.2 = true := by
  decide +kernel
theorem H1381_fin : (prmOK pH1381 1381 && ptTest pH1381 (runFrom pH1381 (fmask pH1381) (cmask pH1381) (hmask pH1381) 977 404 (true, H1381_cp1.1, H1381_cp1.2)) 1381 691 true) = true := by
  decide +kernel
theorem H1381_ok : RunOK pH1381 1381 (runFrom pH1381 (fmask pH1381) (cmask pH1381) (hmask pH1381) 977 404 (true, H1381_cp1.1, H1381_cp1.2)) ∧ ptTest pH1381 (runFrom pH1381 (fmask pH1381) (cmask pH1381) (hmask pH1381) 977 404 (true, H1381_cp1.1, H1381_cp1.2)) 1381 691 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1381_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1381_fin) true) H1381_seg1) (by decide) rfl H1381_fin ptTest_fst
noncomputable def I1381_cp1 : Nat × Nat := t7val% (fastRun pI1381 1 976 (init pI1381) (init pI1381))
theorem I1381_seg1 : segOK pI1381 1 976 (init pI1381) (init pI1381) I1381_cp1.1 I1381_cp1.2 = true := by
  decide +kernel
theorem I1381_fin : (prmOK pI1381 1381 && intTest pI1381 (runFrom pI1381 (fmask pI1381) (cmask pI1381) (hmask pI1381) 977 404 (true, I1381_cp1.1, I1381_cp1.2)) 1381 20 false) = true := by
  decide +kernel
theorem I1381_ok : RunOK pI1381 1381 (runFrom pI1381 (fmask pI1381) (cmask pI1381) (hmask pI1381) 977 404 (true, I1381_cp1.1, I1381_cp1.2)) ∧ intTest pI1381 (runFrom pI1381 (fmask pI1381) (cmask pI1381) (hmask pI1381) 977 404 (true, I1381_cp1.1, I1381_cp1.2)) 1381 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1381_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1381_fin) true) I1381_seg1) (by decide) rfl I1381_fin intTest_fst
theorem link1381 : linkOK pL1381 pH1381 pI1381 = true := by decide +kernel
theorem cvx1381 : ConvexBetweenHumps 1381 :=
  cvx_of L1381_ok H1381_ok I1381_ok link1381 (by decide)

/-! ### `N = 1382` -/

def pL1382 : Prm := ⟨79, 37, 39, 1384, 11, 18446744073709551616, 133002686149662917, 133002686149662917⟩
def pH1382 : Prm := ⟨79, 37, 39, 1384, 11, 18446744073709551616, 133003785661290693, 133003785661290693⟩
def pI1382 : Prm := ⟨67, 32, 32, 1384, 11, 18446744073709551616, 133002686149662917, 133003785661290693⟩
noncomputable def L1382_cp1 : Nat × Nat := t7val% (fastRun pL1382 1 976 (init pL1382) (init pL1382))
theorem L1382_seg1 : segOK pL1382 1 976 (init pL1382) (init pL1382) L1382_cp1.1 L1382_cp1.2 = true := by
  decide +kernel
theorem L1382_fin : (prmOK pL1382 1382 && ptTest pL1382 (runFrom pL1382 (fmask pL1382) (cmask pL1382) (hmask pL1382) 977 405 (true, L1382_cp1.1, L1382_cp1.2)) 1382 691 false) = true := by
  decide +kernel
theorem L1382_ok : RunOK pL1382 1382 (runFrom pL1382 (fmask pL1382) (cmask pL1382) (hmask pL1382) 977 405 (true, L1382_cp1.1, L1382_cp1.2)) ∧ ptTest pL1382 (runFrom pL1382 (fmask pL1382) (cmask pL1382) (hmask pL1382) 977 405 (true, L1382_cp1.1, L1382_cp1.2)) 1382 691 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1382_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1382_fin) true) L1382_seg1) (by decide) rfl L1382_fin ptTest_fst
noncomputable def H1382_cp1 : Nat × Nat := t7val% (fastRun pH1382 1 976 (init pH1382) (init pH1382))
theorem H1382_seg1 : segOK pH1382 1 976 (init pH1382) (init pH1382) H1382_cp1.1 H1382_cp1.2 = true := by
  decide +kernel
theorem H1382_fin : (prmOK pH1382 1382 && ptTest pH1382 (runFrom pH1382 (fmask pH1382) (cmask pH1382) (hmask pH1382) 977 405 (true, H1382_cp1.1, H1382_cp1.2)) 1382 691 true) = true := by
  decide +kernel
theorem H1382_ok : RunOK pH1382 1382 (runFrom pH1382 (fmask pH1382) (cmask pH1382) (hmask pH1382) 977 405 (true, H1382_cp1.1, H1382_cp1.2)) ∧ ptTest pH1382 (runFrom pH1382 (fmask pH1382) (cmask pH1382) (hmask pH1382) 977 405 (true, H1382_cp1.1, H1382_cp1.2)) 1382 691 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1382_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1382_fin) true) H1382_seg1) (by decide) rfl H1382_fin ptTest_fst
noncomputable def I1382_cp1 : Nat × Nat := t7val% (fastRun pI1382 1 976 (init pI1382) (init pI1382))
theorem I1382_seg1 : segOK pI1382 1 976 (init pI1382) (init pI1382) I1382_cp1.1 I1382_cp1.2 = true := by
  decide +kernel
theorem I1382_fin : (prmOK pI1382 1382 && intTest pI1382 (runFrom pI1382 (fmask pI1382) (cmask pI1382) (hmask pI1382) 977 405 (true, I1382_cp1.1, I1382_cp1.2)) 1382 20 true) = true := by
  decide +kernel
theorem I1382_ok : RunOK pI1382 1382 (runFrom pI1382 (fmask pI1382) (cmask pI1382) (hmask pI1382) 977 405 (true, I1382_cp1.1, I1382_cp1.2)) ∧ intTest pI1382 (runFrom pI1382 (fmask pI1382) (cmask pI1382) (hmask pI1382) 977 405 (true, I1382_cp1.1, I1382_cp1.2)) 1382 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1382_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1382_fin) true) I1382_seg1) (by decide) rfl I1382_fin intTest_fst
theorem link1382 : linkOK pL1382 pH1382 pI1382 = true := by decide +kernel
theorem cvx1382 : ConvexBetweenHumps 1382 :=
  cvx_of L1382_ok H1382_ok I1382_ok link1382 (by decide)
theorem cenlink1382 : cenLinkOK pI1382 1382 = true := by decide +kernel
theorem cen1382 : CenterUniqueMin 1382 ∧ DipHyp 1382 ∧ OnePointHyps 1382 :=
  cen_of L1382_ok H1382_ok I1382_ok link1382 cenlink1382

/-! ### `N = 1383` -/

def pL1383 : Prm := ⟨79, 37, 39, 1385, 11, 18446744073709551616, 132924687537424266, 132924687537424266⟩
def pH1383 : Prm := ⟨79, 37, 39, 1385, 11, 18446744073709551616, 132925787049052042, 132925787049052042⟩
def pI1383 : Prm := ⟨67, 32, 32, 1385, 11, 18446744073709551616, 132924687537424266, 132925787049052042⟩
noncomputable def L1383_cp1 : Nat × Nat := t7val% (fastRun pL1383 1 977 (init pL1383) (init pL1383))
theorem L1383_seg1 : segOK pL1383 1 977 (init pL1383) (init pL1383) L1383_cp1.1 L1383_cp1.2 = true := by
  decide +kernel
theorem L1383_fin : (prmOK pL1383 1383 && ptTest pL1383 (runFrom pL1383 (fmask pL1383) (cmask pL1383) (hmask pL1383) 978 405 (true, L1383_cp1.1, L1383_cp1.2)) 1383 692 false) = true := by
  decide +kernel
theorem L1383_ok : RunOK pL1383 1383 (runFrom pL1383 (fmask pL1383) (cmask pL1383) (hmask pL1383) 978 405 (true, L1383_cp1.1, L1383_cp1.2)) ∧ ptTest pL1383 (runFrom pL1383 (fmask pL1383) (cmask pL1383) (hmask pL1383) 978 405 (true, L1383_cp1.1, L1383_cp1.2)) 1383 692 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1383_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1383_fin) true) L1383_seg1) (by decide) rfl L1383_fin ptTest_fst
noncomputable def H1383_cp1 : Nat × Nat := t7val% (fastRun pH1383 1 977 (init pH1383) (init pH1383))
theorem H1383_seg1 : segOK pH1383 1 977 (init pH1383) (init pH1383) H1383_cp1.1 H1383_cp1.2 = true := by
  decide +kernel
theorem H1383_fin : (prmOK pH1383 1383 && ptTest pH1383 (runFrom pH1383 (fmask pH1383) (cmask pH1383) (hmask pH1383) 978 405 (true, H1383_cp1.1, H1383_cp1.2)) 1383 692 true) = true := by
  decide +kernel
theorem H1383_ok : RunOK pH1383 1383 (runFrom pH1383 (fmask pH1383) (cmask pH1383) (hmask pH1383) 978 405 (true, H1383_cp1.1, H1383_cp1.2)) ∧ ptTest pH1383 (runFrom pH1383 (fmask pH1383) (cmask pH1383) (hmask pH1383) 978 405 (true, H1383_cp1.1, H1383_cp1.2)) 1383 692 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1383_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1383_fin) true) H1383_seg1) (by decide) rfl H1383_fin ptTest_fst
noncomputable def I1383_cp1 : Nat × Nat := t7val% (fastRun pI1383 1 977 (init pI1383) (init pI1383))
theorem I1383_seg1 : segOK pI1383 1 977 (init pI1383) (init pI1383) I1383_cp1.1 I1383_cp1.2 = true := by
  decide +kernel
theorem I1383_fin : (prmOK pI1383 1383 && intTest pI1383 (runFrom pI1383 (fmask pI1383) (cmask pI1383) (hmask pI1383) 978 405 (true, I1383_cp1.1, I1383_cp1.2)) 1383 20 false) = true := by
  decide +kernel
theorem I1383_ok : RunOK pI1383 1383 (runFrom pI1383 (fmask pI1383) (cmask pI1383) (hmask pI1383) 978 405 (true, I1383_cp1.1, I1383_cp1.2)) ∧ intTest pI1383 (runFrom pI1383 (fmask pI1383) (cmask pI1383) (hmask pI1383) 978 405 (true, I1383_cp1.1, I1383_cp1.2)) 1383 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1383_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1383_fin) true) I1383_seg1) (by decide) rfl I1383_fin intTest_fst
theorem link1383 : linkOK pL1383 pH1383 pI1383 = true := by decide +kernel
theorem cvx1383 : ConvexBetweenHumps 1383 :=
  cvx_of L1383_ok H1383_ok I1383_ok link1383 (by decide)

/-! ### `N = 1384` -/

def pL1384 : Prm := ⟨79, 37, 39, 1386, 11, 18446744073709551616, 132846831420472860, 132846831420472860⟩
def pH1384 : Prm := ⟨79, 37, 39, 1386, 11, 18446744073709551616, 132847930932100636, 132847930932100636⟩
def pI1384 : Prm := ⟨67, 32, 32, 1386, 11, 18446744073709551616, 132846831420472860, 132847930932100636⟩
noncomputable def L1384_cp1 : Nat × Nat := t7val% (fastRun pL1384 1 978 (init pL1384) (init pL1384))
theorem L1384_seg1 : segOK pL1384 1 978 (init pL1384) (init pL1384) L1384_cp1.1 L1384_cp1.2 = true := by
  decide +kernel
theorem L1384_fin : (prmOK pL1384 1384 && ptTest pL1384 (runFrom pL1384 (fmask pL1384) (cmask pL1384) (hmask pL1384) 979 405 (true, L1384_cp1.1, L1384_cp1.2)) 1384 692 false) = true := by
  decide +kernel
theorem L1384_ok : RunOK pL1384 1384 (runFrom pL1384 (fmask pL1384) (cmask pL1384) (hmask pL1384) 979 405 (true, L1384_cp1.1, L1384_cp1.2)) ∧ ptTest pL1384 (runFrom pL1384 (fmask pL1384) (cmask pL1384) (hmask pL1384) 979 405 (true, L1384_cp1.1, L1384_cp1.2)) 1384 692 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1384_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1384_fin) true) L1384_seg1) (by decide) rfl L1384_fin ptTest_fst
noncomputable def H1384_cp1 : Nat × Nat := t7val% (fastRun pH1384 1 978 (init pH1384) (init pH1384))
theorem H1384_seg1 : segOK pH1384 1 978 (init pH1384) (init pH1384) H1384_cp1.1 H1384_cp1.2 = true := by
  decide +kernel
theorem H1384_fin : (prmOK pH1384 1384 && ptTest pH1384 (runFrom pH1384 (fmask pH1384) (cmask pH1384) (hmask pH1384) 979 405 (true, H1384_cp1.1, H1384_cp1.2)) 1384 692 true) = true := by
  decide +kernel
theorem H1384_ok : RunOK pH1384 1384 (runFrom pH1384 (fmask pH1384) (cmask pH1384) (hmask pH1384) 979 405 (true, H1384_cp1.1, H1384_cp1.2)) ∧ ptTest pH1384 (runFrom pH1384 (fmask pH1384) (cmask pH1384) (hmask pH1384) 979 405 (true, H1384_cp1.1, H1384_cp1.2)) 1384 692 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1384_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1384_fin) true) H1384_seg1) (by decide) rfl H1384_fin ptTest_fst
noncomputable def I1384_cp1 : Nat × Nat := t7val% (fastRun pI1384 1 978 (init pI1384) (init pI1384))
theorem I1384_seg1 : segOK pI1384 1 978 (init pI1384) (init pI1384) I1384_cp1.1 I1384_cp1.2 = true := by
  decide +kernel
theorem I1384_fin : (prmOK pI1384 1384 && intTest pI1384 (runFrom pI1384 (fmask pI1384) (cmask pI1384) (hmask pI1384) 979 405 (true, I1384_cp1.1, I1384_cp1.2)) 1384 20 true) = true := by
  decide +kernel
theorem I1384_ok : RunOK pI1384 1384 (runFrom pI1384 (fmask pI1384) (cmask pI1384) (hmask pI1384) 979 405 (true, I1384_cp1.1, I1384_cp1.2)) ∧ intTest pI1384 (runFrom pI1384 (fmask pI1384) (cmask pI1384) (hmask pI1384) 979 405 (true, I1384_cp1.1, I1384_cp1.2)) 1384 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1384_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1384_fin) true) I1384_seg1) (by decide) rfl I1384_fin intTest_fst
theorem link1384 : linkOK pL1384 pH1384 pI1384 = true := by decide +kernel
theorem cvx1384 : ConvexBetweenHumps 1384 :=
  cvx_of L1384_ok H1384_ok I1384_ok link1384 (by decide)
theorem cenlink1384 : cenLinkOK pI1384 1384 = true := by decide +kernel
theorem cen1384 : CenterUniqueMin 1384 ∧ DipHyp 1384 ∧ OnePointHyps 1384 :=
  cen_of L1384_ok H1384_ok I1384_ok link1384 cenlink1384

/-! ### `N = 1385` -/

def pL1385 : Prm := ⟨79, 37, 39, 1387, 11, 18446744073709551616, 132769031766975922, 132769031766975922⟩
def pH1385 : Prm := ⟨79, 37, 39, 1387, 11, 18446744073709551616, 132770131278603698, 132770131278603698⟩
def pI1385 : Prm := ⟨67, 32, 32, 1387, 11, 18446744073709551616, 132769031766975922, 132770131278603698⟩
noncomputable def L1385_cp1 : Nat × Nat := t7val% (fastRun pL1385 1 978 (init pL1385) (init pL1385))
theorem L1385_seg1 : segOK pL1385 1 978 (init pL1385) (init pL1385) L1385_cp1.1 L1385_cp1.2 = true := by
  decide +kernel
theorem L1385_fin : (prmOK pL1385 1385 && ptTest pL1385 (runFrom pL1385 (fmask pL1385) (cmask pL1385) (hmask pL1385) 979 406 (true, L1385_cp1.1, L1385_cp1.2)) 1385 693 false) = true := by
  decide +kernel
theorem L1385_ok : RunOK pL1385 1385 (runFrom pL1385 (fmask pL1385) (cmask pL1385) (hmask pL1385) 979 406 (true, L1385_cp1.1, L1385_cp1.2)) ∧ ptTest pL1385 (runFrom pL1385 (fmask pL1385) (cmask pL1385) (hmask pL1385) 979 406 (true, L1385_cp1.1, L1385_cp1.2)) 1385 693 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1385_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1385_fin) true) L1385_seg1) (by decide) rfl L1385_fin ptTest_fst
noncomputable def H1385_cp1 : Nat × Nat := t7val% (fastRun pH1385 1 978 (init pH1385) (init pH1385))
theorem H1385_seg1 : segOK pH1385 1 978 (init pH1385) (init pH1385) H1385_cp1.1 H1385_cp1.2 = true := by
  decide +kernel
theorem H1385_fin : (prmOK pH1385 1385 && ptTest pH1385 (runFrom pH1385 (fmask pH1385) (cmask pH1385) (hmask pH1385) 979 406 (true, H1385_cp1.1, H1385_cp1.2)) 1385 693 true) = true := by
  decide +kernel
theorem H1385_ok : RunOK pH1385 1385 (runFrom pH1385 (fmask pH1385) (cmask pH1385) (hmask pH1385) 979 406 (true, H1385_cp1.1, H1385_cp1.2)) ∧ ptTest pH1385 (runFrom pH1385 (fmask pH1385) (cmask pH1385) (hmask pH1385) 979 406 (true, H1385_cp1.1, H1385_cp1.2)) 1385 693 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1385_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1385_fin) true) H1385_seg1) (by decide) rfl H1385_fin ptTest_fst
noncomputable def I1385_cp1 : Nat × Nat := t7val% (fastRun pI1385 1 978 (init pI1385) (init pI1385))
theorem I1385_seg1 : segOK pI1385 1 978 (init pI1385) (init pI1385) I1385_cp1.1 I1385_cp1.2 = true := by
  decide +kernel
theorem I1385_fin : (prmOK pI1385 1385 && intTest pI1385 (runFrom pI1385 (fmask pI1385) (cmask pI1385) (hmask pI1385) 979 406 (true, I1385_cp1.1, I1385_cp1.2)) 1385 20 false) = true := by
  decide +kernel
theorem I1385_ok : RunOK pI1385 1385 (runFrom pI1385 (fmask pI1385) (cmask pI1385) (hmask pI1385) 979 406 (true, I1385_cp1.1, I1385_cp1.2)) ∧ intTest pI1385 (runFrom pI1385 (fmask pI1385) (cmask pI1385) (hmask pI1385) 979 406 (true, I1385_cp1.1, I1385_cp1.2)) 1385 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1385_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1385_fin) true) I1385_seg1) (by decide) rfl I1385_fin intTest_fst
theorem link1385 : linkOK pL1385 pH1385 pI1385 = true := by decide +kernel
theorem cvx1385 : ConvexBetweenHumps 1385 :=
  cvx_of L1385_ok H1385_ok I1385_ok link1385 (by decide)

/-! ### `N = 1386` -/

def pL1386 : Prm := ⟨79, 37, 39, 1388, 11, 18446744073709551616, 132691374027103494, 132691374027103494⟩
def pH1386 : Prm := ⟨79, 37, 39, 1388, 11, 18446744073709551616, 132692473538731270, 132692473538731270⟩
def pI1386 : Prm := ⟨67, 32, 32, 1388, 11, 18446744073709551616, 132691374027103494, 132692473538731270⟩
noncomputable def L1386_cp1 : Nat × Nat := t7val% (fastRun pL1386 1 979 (init pL1386) (init pL1386))
theorem L1386_seg1 : segOK pL1386 1 979 (init pL1386) (init pL1386) L1386_cp1.1 L1386_cp1.2 = true := by
  decide +kernel
theorem L1386_fin : (prmOK pL1386 1386 && ptTest pL1386 (runFrom pL1386 (fmask pL1386) (cmask pL1386) (hmask pL1386) 980 406 (true, L1386_cp1.1, L1386_cp1.2)) 1386 693 false) = true := by
  decide +kernel
theorem L1386_ok : RunOK pL1386 1386 (runFrom pL1386 (fmask pL1386) (cmask pL1386) (hmask pL1386) 980 406 (true, L1386_cp1.1, L1386_cp1.2)) ∧ ptTest pL1386 (runFrom pL1386 (fmask pL1386) (cmask pL1386) (hmask pL1386) 980 406 (true, L1386_cp1.1, L1386_cp1.2)) 1386 693 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1386_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1386_fin) true) L1386_seg1) (by decide) rfl L1386_fin ptTest_fst
noncomputable def H1386_cp1 : Nat × Nat := t7val% (fastRun pH1386 1 979 (init pH1386) (init pH1386))
theorem H1386_seg1 : segOK pH1386 1 979 (init pH1386) (init pH1386) H1386_cp1.1 H1386_cp1.2 = true := by
  decide +kernel
theorem H1386_fin : (prmOK pH1386 1386 && ptTest pH1386 (runFrom pH1386 (fmask pH1386) (cmask pH1386) (hmask pH1386) 980 406 (true, H1386_cp1.1, H1386_cp1.2)) 1386 693 true) = true := by
  decide +kernel
theorem H1386_ok : RunOK pH1386 1386 (runFrom pH1386 (fmask pH1386) (cmask pH1386) (hmask pH1386) 980 406 (true, H1386_cp1.1, H1386_cp1.2)) ∧ ptTest pH1386 (runFrom pH1386 (fmask pH1386) (cmask pH1386) (hmask pH1386) 980 406 (true, H1386_cp1.1, H1386_cp1.2)) 1386 693 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1386_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1386_fin) true) H1386_seg1) (by decide) rfl H1386_fin ptTest_fst
noncomputable def I1386_cp1 : Nat × Nat := t7val% (fastRun pI1386 1 979 (init pI1386) (init pI1386))
theorem I1386_seg1 : segOK pI1386 1 979 (init pI1386) (init pI1386) I1386_cp1.1 I1386_cp1.2 = true := by
  decide +kernel
theorem I1386_fin : (prmOK pI1386 1386 && intTest pI1386 (runFrom pI1386 (fmask pI1386) (cmask pI1386) (hmask pI1386) 980 406 (true, I1386_cp1.1, I1386_cp1.2)) 1386 20 true) = true := by
  decide +kernel
theorem I1386_ok : RunOK pI1386 1386 (runFrom pI1386 (fmask pI1386) (cmask pI1386) (hmask pI1386) 980 406 (true, I1386_cp1.1, I1386_cp1.2)) ∧ intTest pI1386 (runFrom pI1386 (fmask pI1386) (cmask pI1386) (hmask pI1386) 980 406 (true, I1386_cp1.1, I1386_cp1.2)) 1386 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1386_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1386_fin) true) I1386_seg1) (by decide) rfl I1386_fin intTest_fst
theorem link1386 : linkOK pL1386 pH1386 pI1386 = true := by decide +kernel
theorem cvx1386 : ConvexBetweenHumps 1386 :=
  cvx_of L1386_ok H1386_ok I1386_ok link1386 (by decide)
theorem cenlink1386 : cenLinkOK pI1386 1386 = true := by decide +kernel
theorem cen1386 : CenterUniqueMin 1386 ∧ DipHyp 1386 ∧ OnePointHyps 1386 :=
  cen_of L1386_ok H1386_ok I1386_ok link1386 cenlink1386

/-! ### `N = 1387` -/

def pL1387 : Prm := ⟨79, 37, 39, 1389, 11, 18446744073709551616, 132613772547420862, 132613772547420862⟩
def pH1387 : Prm := ⟨79, 37, 39, 1389, 11, 18446744073709551616, 132614872059048638, 132614872059048638⟩
def pI1387 : Prm := ⟨67, 32, 32, 1389, 11, 18446744073709551616, 132613772547420862, 132614872059048638⟩
noncomputable def L1387_cp1 : Nat × Nat := t7val% (fastRun pL1387 1 980 (init pL1387) (init pL1387))
theorem L1387_seg1 : segOK pL1387 1 980 (init pL1387) (init pL1387) L1387_cp1.1 L1387_cp1.2 = true := by
  decide +kernel
theorem L1387_fin : (prmOK pL1387 1387 && ptTest pL1387 (runFrom pL1387 (fmask pL1387) (cmask pL1387) (hmask pL1387) 981 406 (true, L1387_cp1.1, L1387_cp1.2)) 1387 694 false) = true := by
  decide +kernel
theorem L1387_ok : RunOK pL1387 1387 (runFrom pL1387 (fmask pL1387) (cmask pL1387) (hmask pL1387) 981 406 (true, L1387_cp1.1, L1387_cp1.2)) ∧ ptTest pL1387 (runFrom pL1387 (fmask pL1387) (cmask pL1387) (hmask pL1387) 981 406 (true, L1387_cp1.1, L1387_cp1.2)) 1387 694 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1387_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1387_fin) true) L1387_seg1) (by decide) rfl L1387_fin ptTest_fst
noncomputable def H1387_cp1 : Nat × Nat := t7val% (fastRun pH1387 1 980 (init pH1387) (init pH1387))
theorem H1387_seg1 : segOK pH1387 1 980 (init pH1387) (init pH1387) H1387_cp1.1 H1387_cp1.2 = true := by
  decide +kernel
theorem H1387_fin : (prmOK pH1387 1387 && ptTest pH1387 (runFrom pH1387 (fmask pH1387) (cmask pH1387) (hmask pH1387) 981 406 (true, H1387_cp1.1, H1387_cp1.2)) 1387 694 true) = true := by
  decide +kernel
theorem H1387_ok : RunOK pH1387 1387 (runFrom pH1387 (fmask pH1387) (cmask pH1387) (hmask pH1387) 981 406 (true, H1387_cp1.1, H1387_cp1.2)) ∧ ptTest pH1387 (runFrom pH1387 (fmask pH1387) (cmask pH1387) (hmask pH1387) 981 406 (true, H1387_cp1.1, H1387_cp1.2)) 1387 694 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1387_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1387_fin) true) H1387_seg1) (by decide) rfl H1387_fin ptTest_fst
noncomputable def I1387_cp1 : Nat × Nat := t7val% (fastRun pI1387 1 980 (init pI1387) (init pI1387))
theorem I1387_seg1 : segOK pI1387 1 980 (init pI1387) (init pI1387) I1387_cp1.1 I1387_cp1.2 = true := by
  decide +kernel
theorem I1387_fin : (prmOK pI1387 1387 && intTest pI1387 (runFrom pI1387 (fmask pI1387) (cmask pI1387) (hmask pI1387) 981 406 (true, I1387_cp1.1, I1387_cp1.2)) 1387 20 false) = true := by
  decide +kernel
theorem I1387_ok : RunOK pI1387 1387 (runFrom pI1387 (fmask pI1387) (cmask pI1387) (hmask pI1387) 981 406 (true, I1387_cp1.1, I1387_cp1.2)) ∧ intTest pI1387 (runFrom pI1387 (fmask pI1387) (cmask pI1387) (hmask pI1387) 981 406 (true, I1387_cp1.1, I1387_cp1.2)) 1387 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1387_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1387_fin) true) I1387_seg1) (by decide) rfl I1387_fin intTest_fst
theorem link1387 : linkOK pL1387 pH1387 pI1387 = true := by decide +kernel
theorem cvx1387 : ConvexBetweenHumps 1387 :=
  cvx_of L1387_ok H1387_ok I1387_ok link1387 (by decide)

/-! ### `N = 1388` -/

def pL1388 : Prm := ⟨79, 37, 39, 1390, 11, 18446744073709551616, 132536312402928186, 132536312402928186⟩
def pH1388 : Prm := ⟨79, 37, 39, 1390, 11, 18446744073709551616, 132537411914555962, 132537411914555962⟩
def pI1388 : Prm := ⟨65, 33, 29, 1390, 11, 18446744073709551616, 132536312402928186, 132537411914555962⟩
noncomputable def L1388_cp1 : Nat × Nat := t7val% (fastRun pL1388 1 980 (init pL1388) (init pL1388))
theorem L1388_seg1 : segOK pL1388 1 980 (init pL1388) (init pL1388) L1388_cp1.1 L1388_cp1.2 = true := by
  decide +kernel
theorem L1388_fin : (prmOK pL1388 1388 && ptTest pL1388 (runFrom pL1388 (fmask pL1388) (cmask pL1388) (hmask pL1388) 981 407 (true, L1388_cp1.1, L1388_cp1.2)) 1388 694 false) = true := by
  decide +kernel
theorem L1388_ok : RunOK pL1388 1388 (runFrom pL1388 (fmask pL1388) (cmask pL1388) (hmask pL1388) 981 407 (true, L1388_cp1.1, L1388_cp1.2)) ∧ ptTest pL1388 (runFrom pL1388 (fmask pL1388) (cmask pL1388) (hmask pL1388) 981 407 (true, L1388_cp1.1, L1388_cp1.2)) 1388 694 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1388_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1388_fin) true) L1388_seg1) (by decide) rfl L1388_fin ptTest_fst
noncomputable def H1388_cp1 : Nat × Nat := t7val% (fastRun pH1388 1 980 (init pH1388) (init pH1388))
theorem H1388_seg1 : segOK pH1388 1 980 (init pH1388) (init pH1388) H1388_cp1.1 H1388_cp1.2 = true := by
  decide +kernel
theorem H1388_fin : (prmOK pH1388 1388 && ptTest pH1388 (runFrom pH1388 (fmask pH1388) (cmask pH1388) (hmask pH1388) 981 407 (true, H1388_cp1.1, H1388_cp1.2)) 1388 694 true) = true := by
  decide +kernel
theorem H1388_ok : RunOK pH1388 1388 (runFrom pH1388 (fmask pH1388) (cmask pH1388) (hmask pH1388) 981 407 (true, H1388_cp1.1, H1388_cp1.2)) ∧ ptTest pH1388 (runFrom pH1388 (fmask pH1388) (cmask pH1388) (hmask pH1388) 981 407 (true, H1388_cp1.1, H1388_cp1.2)) 1388 694 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1388_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1388_fin) true) H1388_seg1) (by decide) rfl H1388_fin ptTest_fst
noncomputable def I1388_cp1 : Nat × Nat := t7val% (fastRun pI1388 1 980 (init pI1388) (init pI1388))
theorem I1388_seg1 : segOK pI1388 1 980 (init pI1388) (init pI1388) I1388_cp1.1 I1388_cp1.2 = true := by
  decide +kernel
theorem I1388_fin : (prmOK pI1388 1388 && intTest pI1388 (runFrom pI1388 (fmask pI1388) (cmask pI1388) (hmask pI1388) 981 407 (true, I1388_cp1.1, I1388_cp1.2)) 1388 20 true) = true := by
  decide +kernel
theorem I1388_ok : RunOK pI1388 1388 (runFrom pI1388 (fmask pI1388) (cmask pI1388) (hmask pI1388) 981 407 (true, I1388_cp1.1, I1388_cp1.2)) ∧ intTest pI1388 (runFrom pI1388 (fmask pI1388) (cmask pI1388) (hmask pI1388) 981 407 (true, I1388_cp1.1, I1388_cp1.2)) 1388 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1388_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1388_fin) true) I1388_seg1) (by decide) rfl I1388_fin intTest_fst
theorem link1388 : linkOK pL1388 pH1388 pI1388 = true := by decide +kernel
theorem cvx1388 : ConvexBetweenHumps 1388 :=
  cvx_of L1388_ok H1388_ok I1388_ok link1388 (by decide)
theorem cenlink1388 : cenLinkOK pI1388 1388 = true := by decide +kernel
theorem cen1388 : CenterUniqueMin 1388 ∧ DipHyp 1388 ∧ OnePointHyps 1388 :=
  cen_of L1388_ok H1388_ok I1388_ok link1388 cenlink1388

/-! ### `N = 1389` -/

def pL1389 : Prm := ⟨79, 37, 39, 1391, 11, 18446744073709551616, 132458908316375203, 132458908316375203⟩
def pH1389 : Prm := ⟨79, 37, 39, 1391, 11, 18446744073709551616, 132460007828002979, 132460007828002979⟩
def pI1389 : Prm := ⟨67, 32, 32, 1391, 11, 18446744073709551616, 132458908316375203, 132460007828002979⟩
noncomputable def L1389_cp1 : Nat × Nat := t7val% (fastRun pL1389 1 981 (init pL1389) (init pL1389))
theorem L1389_seg1 : segOK pL1389 1 981 (init pL1389) (init pL1389) L1389_cp1.1 L1389_cp1.2 = true := by
  decide +kernel
theorem L1389_fin : (prmOK pL1389 1389 && ptTest pL1389 (runFrom pL1389 (fmask pL1389) (cmask pL1389) (hmask pL1389) 982 407 (true, L1389_cp1.1, L1389_cp1.2)) 1389 695 false) = true := by
  decide +kernel
theorem L1389_ok : RunOK pL1389 1389 (runFrom pL1389 (fmask pL1389) (cmask pL1389) (hmask pL1389) 982 407 (true, L1389_cp1.1, L1389_cp1.2)) ∧ ptTest pL1389 (runFrom pL1389 (fmask pL1389) (cmask pL1389) (hmask pL1389) 982 407 (true, L1389_cp1.1, L1389_cp1.2)) 1389 695 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1389_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1389_fin) true) L1389_seg1) (by decide) rfl L1389_fin ptTest_fst
noncomputable def H1389_cp1 : Nat × Nat := t7val% (fastRun pH1389 1 981 (init pH1389) (init pH1389))
theorem H1389_seg1 : segOK pH1389 1 981 (init pH1389) (init pH1389) H1389_cp1.1 H1389_cp1.2 = true := by
  decide +kernel
theorem H1389_fin : (prmOK pH1389 1389 && ptTest pH1389 (runFrom pH1389 (fmask pH1389) (cmask pH1389) (hmask pH1389) 982 407 (true, H1389_cp1.1, H1389_cp1.2)) 1389 695 true) = true := by
  decide +kernel
theorem H1389_ok : RunOK pH1389 1389 (runFrom pH1389 (fmask pH1389) (cmask pH1389) (hmask pH1389) 982 407 (true, H1389_cp1.1, H1389_cp1.2)) ∧ ptTest pH1389 (runFrom pH1389 (fmask pH1389) (cmask pH1389) (hmask pH1389) 982 407 (true, H1389_cp1.1, H1389_cp1.2)) 1389 695 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1389_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1389_fin) true) H1389_seg1) (by decide) rfl H1389_fin ptTest_fst
noncomputable def I1389_cp1 : Nat × Nat := t7val% (fastRun pI1389 1 981 (init pI1389) (init pI1389))
theorem I1389_seg1 : segOK pI1389 1 981 (init pI1389) (init pI1389) I1389_cp1.1 I1389_cp1.2 = true := by
  decide +kernel
theorem I1389_fin : (prmOK pI1389 1389 && intTest pI1389 (runFrom pI1389 (fmask pI1389) (cmask pI1389) (hmask pI1389) 982 407 (true, I1389_cp1.1, I1389_cp1.2)) 1389 20 false) = true := by
  decide +kernel
theorem I1389_ok : RunOK pI1389 1389 (runFrom pI1389 (fmask pI1389) (cmask pI1389) (hmask pI1389) 982 407 (true, I1389_cp1.1, I1389_cp1.2)) ∧ intTest pI1389 (runFrom pI1389 (fmask pI1389) (cmask pI1389) (hmask pI1389) 982 407 (true, I1389_cp1.1, I1389_cp1.2)) 1389 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1389_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1389_fin) true) I1389_seg1) (by decide) rfl I1389_fin intTest_fst
theorem link1389 : linkOK pL1389 pH1389 pI1389 = true := by decide +kernel
theorem cvx1389 : ConvexBetweenHumps 1389 :=
  cvx_of L1389_ok H1389_ok I1389_ok link1389 (by decide)

/-! ### `N = 1390` -/

def pL1390 : Prm := ⟨79, 37, 39, 1392, 11, 18446744073709551616, 132381644989713570, 132381644989713570⟩
def pH1390 : Prm := ⟨79, 37, 39, 1392, 11, 18446744073709551616, 132382744501341346, 132382744501341346⟩
def pI1390 : Prm := ⟨67, 32, 32, 1392, 11, 18446744073709551616, 132381644989713570, 132382744501341346⟩
noncomputable def L1390_cp1 : Nat × Nat := t7val% (fastRun pL1390 1 982 (init pL1390) (init pL1390))
theorem L1390_seg1 : segOK pL1390 1 982 (init pL1390) (init pL1390) L1390_cp1.1 L1390_cp1.2 = true := by
  decide +kernel
theorem L1390_fin : (prmOK pL1390 1390 && ptTest pL1390 (runFrom pL1390 (fmask pL1390) (cmask pL1390) (hmask pL1390) 983 407 (true, L1390_cp1.1, L1390_cp1.2)) 1390 695 false) = true := by
  decide +kernel
theorem L1390_ok : RunOK pL1390 1390 (runFrom pL1390 (fmask pL1390) (cmask pL1390) (hmask pL1390) 983 407 (true, L1390_cp1.1, L1390_cp1.2)) ∧ ptTest pL1390 (runFrom pL1390 (fmask pL1390) (cmask pL1390) (hmask pL1390) 983 407 (true, L1390_cp1.1, L1390_cp1.2)) 1390 695 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1390_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1390_fin) true) L1390_seg1) (by decide) rfl L1390_fin ptTest_fst
noncomputable def H1390_cp1 : Nat × Nat := t7val% (fastRun pH1390 1 982 (init pH1390) (init pH1390))
theorem H1390_seg1 : segOK pH1390 1 982 (init pH1390) (init pH1390) H1390_cp1.1 H1390_cp1.2 = true := by
  decide +kernel
theorem H1390_fin : (prmOK pH1390 1390 && ptTest pH1390 (runFrom pH1390 (fmask pH1390) (cmask pH1390) (hmask pH1390) 983 407 (true, H1390_cp1.1, H1390_cp1.2)) 1390 695 true) = true := by
  decide +kernel
theorem H1390_ok : RunOK pH1390 1390 (runFrom pH1390 (fmask pH1390) (cmask pH1390) (hmask pH1390) 983 407 (true, H1390_cp1.1, H1390_cp1.2)) ∧ ptTest pH1390 (runFrom pH1390 (fmask pH1390) (cmask pH1390) (hmask pH1390) 983 407 (true, H1390_cp1.1, H1390_cp1.2)) 1390 695 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1390_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1390_fin) true) H1390_seg1) (by decide) rfl H1390_fin ptTest_fst
noncomputable def I1390_cp1 : Nat × Nat := t7val% (fastRun pI1390 1 982 (init pI1390) (init pI1390))
theorem I1390_seg1 : segOK pI1390 1 982 (init pI1390) (init pI1390) I1390_cp1.1 I1390_cp1.2 = true := by
  decide +kernel
theorem I1390_fin : (prmOK pI1390 1390 && intTest pI1390 (runFrom pI1390 (fmask pI1390) (cmask pI1390) (hmask pI1390) 983 407 (true, I1390_cp1.1, I1390_cp1.2)) 1390 20 true) = true := by
  decide +kernel
theorem I1390_ok : RunOK pI1390 1390 (runFrom pI1390 (fmask pI1390) (cmask pI1390) (hmask pI1390) 983 407 (true, I1390_cp1.1, I1390_cp1.2)) ∧ intTest pI1390 (runFrom pI1390 (fmask pI1390) (cmask pI1390) (hmask pI1390) 983 407 (true, I1390_cp1.1, I1390_cp1.2)) 1390 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1390_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1390_fin) true) I1390_seg1) (by decide) rfl I1390_fin intTest_fst
theorem link1390 : linkOK pL1390 pH1390 pI1390 = true := by decide +kernel
theorem cvx1390 : ConvexBetweenHumps 1390 :=
  cvx_of L1390_ok H1390_ok I1390_ok link1390 (by decide)
theorem cenlink1390 : cenLinkOK pI1390 1390 = true := by decide +kernel
theorem cen1390 : CenterUniqueMin 1390 ∧ DipHyp 1390 ∧ OnePointHyps 1390 :=
  cen_of L1390_ok H1390_ok I1390_ok link1390 cenlink1390

/-! ### `N = 1391` -/

def pL1391 : Prm := ⟨79, 37, 39, 1393, 11, 18446744073709551616, 132304437519682311, 132304437519682311⟩
def pH1391 : Prm := ⟨79, 37, 39, 1393, 11, 18446744073709551616, 132305537031310087, 132305537031310087⟩
def pI1391 : Prm := ⟨67, 32, 32, 1393, 11, 18446744073709551616, 132304437519682311, 132305537031310087⟩
noncomputable def L1391_cp1 : Nat × Nat := t7val% (fastRun pL1391 1 983 (init pL1391) (init pL1391))
theorem L1391_seg1 : segOK pL1391 1 983 (init pL1391) (init pL1391) L1391_cp1.1 L1391_cp1.2 = true := by
  decide +kernel
theorem L1391_fin : (prmOK pL1391 1391 && ptTest pL1391 (runFrom pL1391 (fmask pL1391) (cmask pL1391) (hmask pL1391) 984 407 (true, L1391_cp1.1, L1391_cp1.2)) 1391 696 false) = true := by
  decide +kernel
theorem L1391_ok : RunOK pL1391 1391 (runFrom pL1391 (fmask pL1391) (cmask pL1391) (hmask pL1391) 984 407 (true, L1391_cp1.1, L1391_cp1.2)) ∧ ptTest pL1391 (runFrom pL1391 (fmask pL1391) (cmask pL1391) (hmask pL1391) 984 407 (true, L1391_cp1.1, L1391_cp1.2)) 1391 696 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1391_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1391_fin) true) L1391_seg1) (by decide) rfl L1391_fin ptTest_fst
noncomputable def H1391_cp1 : Nat × Nat := t7val% (fastRun pH1391 1 983 (init pH1391) (init pH1391))
theorem H1391_seg1 : segOK pH1391 1 983 (init pH1391) (init pH1391) H1391_cp1.1 H1391_cp1.2 = true := by
  decide +kernel
theorem H1391_fin : (prmOK pH1391 1391 && ptTest pH1391 (runFrom pH1391 (fmask pH1391) (cmask pH1391) (hmask pH1391) 984 407 (true, H1391_cp1.1, H1391_cp1.2)) 1391 696 true) = true := by
  decide +kernel
theorem H1391_ok : RunOK pH1391 1391 (runFrom pH1391 (fmask pH1391) (cmask pH1391) (hmask pH1391) 984 407 (true, H1391_cp1.1, H1391_cp1.2)) ∧ ptTest pH1391 (runFrom pH1391 (fmask pH1391) (cmask pH1391) (hmask pH1391) 984 407 (true, H1391_cp1.1, H1391_cp1.2)) 1391 696 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1391_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1391_fin) true) H1391_seg1) (by decide) rfl H1391_fin ptTest_fst
noncomputable def I1391_cp1 : Nat × Nat := t7val% (fastRun pI1391 1 983 (init pI1391) (init pI1391))
theorem I1391_seg1 : segOK pI1391 1 983 (init pI1391) (init pI1391) I1391_cp1.1 I1391_cp1.2 = true := by
  decide +kernel
theorem I1391_fin : (prmOK pI1391 1391 && intTest pI1391 (runFrom pI1391 (fmask pI1391) (cmask pI1391) (hmask pI1391) 984 407 (true, I1391_cp1.1, I1391_cp1.2)) 1391 20 false) = true := by
  decide +kernel
theorem I1391_ok : RunOK pI1391 1391 (runFrom pI1391 (fmask pI1391) (cmask pI1391) (hmask pI1391) 984 407 (true, I1391_cp1.1, I1391_cp1.2)) ∧ intTest pI1391 (runFrom pI1391 (fmask pI1391) (cmask pI1391) (hmask pI1391) 984 407 (true, I1391_cp1.1, I1391_cp1.2)) 1391 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1391_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1391_fin) true) I1391_seg1) (by decide) rfl I1391_fin intTest_fst
theorem link1391 : linkOK pL1391 pH1391 pI1391 = true := by decide +kernel
theorem cvx1391 : ConvexBetweenHumps 1391 :=
  cvx_of L1391_ok H1391_ok I1391_ok link1391 (by decide)

/-! ### `N = 1392` -/

def pL1392 : Prm := ⟨79, 37, 39, 1394, 11, 18446744073709551616, 132227370237453528, 132227370237453528⟩
def pH1392 : Prm := ⟨79, 37, 39, 1394, 11, 18446744073709551616, 132228469749081304, 132228469749081304⟩
def pI1392 : Prm := ⟨67, 32, 32, 1394, 11, 18446744073709551616, 132227370237453528, 132228469749081304⟩
noncomputable def L1392_cp1 : Nat × Nat := t7val% (fastRun pL1392 1 983 (init pL1392) (init pL1392))
theorem L1392_seg1 : segOK pL1392 1 983 (init pL1392) (init pL1392) L1392_cp1.1 L1392_cp1.2 = true := by
  decide +kernel
theorem L1392_fin : (prmOK pL1392 1392 && ptTest pL1392 (runFrom pL1392 (fmask pL1392) (cmask pL1392) (hmask pL1392) 984 408 (true, L1392_cp1.1, L1392_cp1.2)) 1392 696 false) = true := by
  decide +kernel
theorem L1392_ok : RunOK pL1392 1392 (runFrom pL1392 (fmask pL1392) (cmask pL1392) (hmask pL1392) 984 408 (true, L1392_cp1.1, L1392_cp1.2)) ∧ ptTest pL1392 (runFrom pL1392 (fmask pL1392) (cmask pL1392) (hmask pL1392) 984 408 (true, L1392_cp1.1, L1392_cp1.2)) 1392 696 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1392_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1392_fin) true) L1392_seg1) (by decide) rfl L1392_fin ptTest_fst
noncomputable def H1392_cp1 : Nat × Nat := t7val% (fastRun pH1392 1 983 (init pH1392) (init pH1392))
theorem H1392_seg1 : segOK pH1392 1 983 (init pH1392) (init pH1392) H1392_cp1.1 H1392_cp1.2 = true := by
  decide +kernel
theorem H1392_fin : (prmOK pH1392 1392 && ptTest pH1392 (runFrom pH1392 (fmask pH1392) (cmask pH1392) (hmask pH1392) 984 408 (true, H1392_cp1.1, H1392_cp1.2)) 1392 696 true) = true := by
  decide +kernel
theorem H1392_ok : RunOK pH1392 1392 (runFrom pH1392 (fmask pH1392) (cmask pH1392) (hmask pH1392) 984 408 (true, H1392_cp1.1, H1392_cp1.2)) ∧ ptTest pH1392 (runFrom pH1392 (fmask pH1392) (cmask pH1392) (hmask pH1392) 984 408 (true, H1392_cp1.1, H1392_cp1.2)) 1392 696 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1392_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1392_fin) true) H1392_seg1) (by decide) rfl H1392_fin ptTest_fst
noncomputable def I1392_cp1 : Nat × Nat := t7val% (fastRun pI1392 1 983 (init pI1392) (init pI1392))
theorem I1392_seg1 : segOK pI1392 1 983 (init pI1392) (init pI1392) I1392_cp1.1 I1392_cp1.2 = true := by
  decide +kernel
theorem I1392_fin : (prmOK pI1392 1392 && intTest pI1392 (runFrom pI1392 (fmask pI1392) (cmask pI1392) (hmask pI1392) 984 408 (true, I1392_cp1.1, I1392_cp1.2)) 1392 20 true) = true := by
  decide +kernel
theorem I1392_ok : RunOK pI1392 1392 (runFrom pI1392 (fmask pI1392) (cmask pI1392) (hmask pI1392) 984 408 (true, I1392_cp1.1, I1392_cp1.2)) ∧ intTest pI1392 (runFrom pI1392 (fmask pI1392) (cmask pI1392) (hmask pI1392) 984 408 (true, I1392_cp1.1, I1392_cp1.2)) 1392 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1392_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1392_fin) true) I1392_seg1) (by decide) rfl I1392_fin intTest_fst
theorem link1392 : linkOK pL1392 pH1392 pI1392 = true := by decide +kernel
theorem cvx1392 : ConvexBetweenHumps 1392 :=
  cvx_of L1392_ok H1392_ok I1392_ok link1392 (by decide)
theorem cenlink1392 : cenLinkOK pI1392 1392 = true := by decide +kernel
theorem cen1392 : CenterUniqueMin 1392 ∧ DipHyp 1392 ∧ OnePointHyps 1392 :=
  cen_of L1392_ok H1392_ok I1392_ok link1392 cenlink1392

/-! ### `N = 1393` -/

def pL1393 : Prm := ⟨79, 37, 39, 1395, 11, 18446744073709551616, 132150358611578820, 132150358611578820⟩
def pH1393 : Prm := ⟨79, 37, 39, 1395, 11, 18446744073709551616, 132151458123206596, 132151458123206596⟩
def pI1393 : Prm := ⟨65, 33, 29, 1395, 11, 18446744073709551616, 132150358611578820, 132151458123206596⟩
noncomputable def L1393_cp1 : Nat × Nat := t7val% (fastRun pL1393 1 984 (init pL1393) (init pL1393))
theorem L1393_seg1 : segOK pL1393 1 984 (init pL1393) (init pL1393) L1393_cp1.1 L1393_cp1.2 = true := by
  decide +kernel
theorem L1393_fin : (prmOK pL1393 1393 && ptTest pL1393 (runFrom pL1393 (fmask pL1393) (cmask pL1393) (hmask pL1393) 985 408 (true, L1393_cp1.1, L1393_cp1.2)) 1393 697 false) = true := by
  decide +kernel
theorem L1393_ok : RunOK pL1393 1393 (runFrom pL1393 (fmask pL1393) (cmask pL1393) (hmask pL1393) 985 408 (true, L1393_cp1.1, L1393_cp1.2)) ∧ ptTest pL1393 (runFrom pL1393 (fmask pL1393) (cmask pL1393) (hmask pL1393) 985 408 (true, L1393_cp1.1, L1393_cp1.2)) 1393 697 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1393_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1393_fin) true) L1393_seg1) (by decide) rfl L1393_fin ptTest_fst
noncomputable def H1393_cp1 : Nat × Nat := t7val% (fastRun pH1393 1 984 (init pH1393) (init pH1393))
theorem H1393_seg1 : segOK pH1393 1 984 (init pH1393) (init pH1393) H1393_cp1.1 H1393_cp1.2 = true := by
  decide +kernel
theorem H1393_fin : (prmOK pH1393 1393 && ptTest pH1393 (runFrom pH1393 (fmask pH1393) (cmask pH1393) (hmask pH1393) 985 408 (true, H1393_cp1.1, H1393_cp1.2)) 1393 697 true) = true := by
  decide +kernel
theorem H1393_ok : RunOK pH1393 1393 (runFrom pH1393 (fmask pH1393) (cmask pH1393) (hmask pH1393) 985 408 (true, H1393_cp1.1, H1393_cp1.2)) ∧ ptTest pH1393 (runFrom pH1393 (fmask pH1393) (cmask pH1393) (hmask pH1393) 985 408 (true, H1393_cp1.1, H1393_cp1.2)) 1393 697 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1393_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1393_fin) true) H1393_seg1) (by decide) rfl H1393_fin ptTest_fst
noncomputable def I1393_cp1 : Nat × Nat := t7val% (fastRun pI1393 1 984 (init pI1393) (init pI1393))
theorem I1393_seg1 : segOK pI1393 1 984 (init pI1393) (init pI1393) I1393_cp1.1 I1393_cp1.2 = true := by
  decide +kernel
theorem I1393_fin : (prmOK pI1393 1393 && intTest pI1393 (runFrom pI1393 (fmask pI1393) (cmask pI1393) (hmask pI1393) 985 408 (true, I1393_cp1.1, I1393_cp1.2)) 1393 20 false) = true := by
  decide +kernel
theorem I1393_ok : RunOK pI1393 1393 (runFrom pI1393 (fmask pI1393) (cmask pI1393) (hmask pI1393) 985 408 (true, I1393_cp1.1, I1393_cp1.2)) ∧ intTest pI1393 (runFrom pI1393 (fmask pI1393) (cmask pI1393) (hmask pI1393) 985 408 (true, I1393_cp1.1, I1393_cp1.2)) 1393 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1393_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1393_fin) true) I1393_seg1) (by decide) rfl I1393_fin intTest_fst
theorem link1393 : linkOK pL1393 pH1393 pI1393 = true := by decide +kernel
theorem cvx1393 : ConvexBetweenHumps 1393 :=
  cvx_of L1393_ok H1393_ok I1393_ok link1393 (by decide)

/-! ### `N = 1394` -/

def pL1394 : Prm := ⟨79, 37, 39, 1396, 11, 18446744073709551616, 132073486604498319, 132073486604498319⟩
def pH1394 : Prm := ⟨79, 37, 39, 1396, 11, 18446744073709551616, 132074586116126095, 132074586116126095⟩
def pI1394 : Prm := ⟨67, 32, 32, 1396, 11, 18446744073709551616, 132073486604498319, 132074586116126095⟩
noncomputable def L1394_cp1 : Nat × Nat := t7val% (fastRun pL1394 1 985 (init pL1394) (init pL1394))
theorem L1394_seg1 : segOK pL1394 1 985 (init pL1394) (init pL1394) L1394_cp1.1 L1394_cp1.2 = true := by
  decide +kernel
theorem L1394_fin : (prmOK pL1394 1394 && ptTest pL1394 (runFrom pL1394 (fmask pL1394) (cmask pL1394) (hmask pL1394) 986 408 (true, L1394_cp1.1, L1394_cp1.2)) 1394 697 false) = true := by
  decide +kernel
theorem L1394_ok : RunOK pL1394 1394 (runFrom pL1394 (fmask pL1394) (cmask pL1394) (hmask pL1394) 986 408 (true, L1394_cp1.1, L1394_cp1.2)) ∧ ptTest pL1394 (runFrom pL1394 (fmask pL1394) (cmask pL1394) (hmask pL1394) 986 408 (true, L1394_cp1.1, L1394_cp1.2)) 1394 697 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1394_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1394_fin) true) L1394_seg1) (by decide) rfl L1394_fin ptTest_fst
noncomputable def H1394_cp1 : Nat × Nat := t7val% (fastRun pH1394 1 985 (init pH1394) (init pH1394))
theorem H1394_seg1 : segOK pH1394 1 985 (init pH1394) (init pH1394) H1394_cp1.1 H1394_cp1.2 = true := by
  decide +kernel
theorem H1394_fin : (prmOK pH1394 1394 && ptTest pH1394 (runFrom pH1394 (fmask pH1394) (cmask pH1394) (hmask pH1394) 986 408 (true, H1394_cp1.1, H1394_cp1.2)) 1394 697 true) = true := by
  decide +kernel
theorem H1394_ok : RunOK pH1394 1394 (runFrom pH1394 (fmask pH1394) (cmask pH1394) (hmask pH1394) 986 408 (true, H1394_cp1.1, H1394_cp1.2)) ∧ ptTest pH1394 (runFrom pH1394 (fmask pH1394) (cmask pH1394) (hmask pH1394) 986 408 (true, H1394_cp1.1, H1394_cp1.2)) 1394 697 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1394_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1394_fin) true) H1394_seg1) (by decide) rfl H1394_fin ptTest_fst
noncomputable def I1394_cp1 : Nat × Nat := t7val% (fastRun pI1394 1 985 (init pI1394) (init pI1394))
theorem I1394_seg1 : segOK pI1394 1 985 (init pI1394) (init pI1394) I1394_cp1.1 I1394_cp1.2 = true := by
  decide +kernel
theorem I1394_fin : (prmOK pI1394 1394 && intTest pI1394 (runFrom pI1394 (fmask pI1394) (cmask pI1394) (hmask pI1394) 986 408 (true, I1394_cp1.1, I1394_cp1.2)) 1394 20 true) = true := by
  decide +kernel
theorem I1394_ok : RunOK pI1394 1394 (runFrom pI1394 (fmask pI1394) (cmask pI1394) (hmask pI1394) 986 408 (true, I1394_cp1.1, I1394_cp1.2)) ∧ intTest pI1394 (runFrom pI1394 (fmask pI1394) (cmask pI1394) (hmask pI1394) 986 408 (true, I1394_cp1.1, I1394_cp1.2)) 1394 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1394_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1394_fin) true) I1394_seg1) (by decide) rfl I1394_fin intTest_fst
theorem link1394 : linkOK pL1394 pH1394 pI1394 = true := by decide +kernel
theorem cvx1394 : ConvexBetweenHumps 1394 :=
  cvx_of L1394_ok H1394_ok I1394_ok link1394 (by decide)
theorem cenlink1394 : cenLinkOK pI1394 1394 = true := by decide +kernel
theorem cen1394 : CenterUniqueMin 1394 ∧ DipHyp 1394 ∧ OnePointHyps 1394 :=
  cen_of L1394_ok H1394_ok I1394_ok link1394 cenlink1394

/-! ### `N = 1395` -/

def pL1395 : Prm := ⟨79, 37, 39, 1397, 11, 18446744073709551616, 131996670054436376, 131996670054436376⟩
def pH1395 : Prm := ⟨79, 37, 39, 1397, 11, 18446744073709551616, 131997769566064152, 131997769566064152⟩
def pI1395 : Prm := ⟨65, 33, 29, 1397, 11, 18446744073709551616, 131996670054436376, 131997769566064152⟩
noncomputable def L1395_cp1 : Nat × Nat := t7val% (fastRun pL1395 1 985 (init pL1395) (init pL1395))
theorem L1395_seg1 : segOK pL1395 1 985 (init pL1395) (init pL1395) L1395_cp1.1 L1395_cp1.2 = true := by
  decide +kernel
theorem L1395_fin : (prmOK pL1395 1395 && ptTest pL1395 (runFrom pL1395 (fmask pL1395) (cmask pL1395) (hmask pL1395) 986 409 (true, L1395_cp1.1, L1395_cp1.2)) 1395 698 false) = true := by
  decide +kernel
theorem L1395_ok : RunOK pL1395 1395 (runFrom pL1395 (fmask pL1395) (cmask pL1395) (hmask pL1395) 986 409 (true, L1395_cp1.1, L1395_cp1.2)) ∧ ptTest pL1395 (runFrom pL1395 (fmask pL1395) (cmask pL1395) (hmask pL1395) 986 409 (true, L1395_cp1.1, L1395_cp1.2)) 1395 698 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1395_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1395_fin) true) L1395_seg1) (by decide) rfl L1395_fin ptTest_fst
noncomputable def H1395_cp1 : Nat × Nat := t7val% (fastRun pH1395 1 985 (init pH1395) (init pH1395))
theorem H1395_seg1 : segOK pH1395 1 985 (init pH1395) (init pH1395) H1395_cp1.1 H1395_cp1.2 = true := by
  decide +kernel
theorem H1395_fin : (prmOK pH1395 1395 && ptTest pH1395 (runFrom pH1395 (fmask pH1395) (cmask pH1395) (hmask pH1395) 986 409 (true, H1395_cp1.1, H1395_cp1.2)) 1395 698 true) = true := by
  decide +kernel
theorem H1395_ok : RunOK pH1395 1395 (runFrom pH1395 (fmask pH1395) (cmask pH1395) (hmask pH1395) 986 409 (true, H1395_cp1.1, H1395_cp1.2)) ∧ ptTest pH1395 (runFrom pH1395 (fmask pH1395) (cmask pH1395) (hmask pH1395) 986 409 (true, H1395_cp1.1, H1395_cp1.2)) 1395 698 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1395_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1395_fin) true) H1395_seg1) (by decide) rfl H1395_fin ptTest_fst
noncomputable def I1395_cp1 : Nat × Nat := t7val% (fastRun pI1395 1 985 (init pI1395) (init pI1395))
theorem I1395_seg1 : segOK pI1395 1 985 (init pI1395) (init pI1395) I1395_cp1.1 I1395_cp1.2 = true := by
  decide +kernel
theorem I1395_fin : (prmOK pI1395 1395 && intTest pI1395 (runFrom pI1395 (fmask pI1395) (cmask pI1395) (hmask pI1395) 986 409 (true, I1395_cp1.1, I1395_cp1.2)) 1395 20 false) = true := by
  decide +kernel
theorem I1395_ok : RunOK pI1395 1395 (runFrom pI1395 (fmask pI1395) (cmask pI1395) (hmask pI1395) 986 409 (true, I1395_cp1.1, I1395_cp1.2)) ∧ intTest pI1395 (runFrom pI1395 (fmask pI1395) (cmask pI1395) (hmask pI1395) 986 409 (true, I1395_cp1.1, I1395_cp1.2)) 1395 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1395_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1395_fin) true) I1395_seg1) (by decide) rfl I1395_fin intTest_fst
theorem link1395 : linkOK pL1395 pH1395 pI1395 = true := by decide +kernel
theorem cvx1395 : ConvexBetweenHumps 1395 :=
  cvx_of L1395_ok H1395_ok I1395_ok link1395 (by decide)

/-! ### `N = 1396` -/

def pL1396 : Prm := ⟨79, 37, 39, 1398, 11, 18446744073709551616, 131919992557333214, 131919992557333214⟩
def pH1396 : Prm := ⟨79, 37, 39, 1398, 11, 18446744073709551616, 131921092068960990, 131921092068960990⟩
def pI1396 : Prm := ⟨65, 33, 29, 1398, 11, 18446744073709551616, 131919992557333214, 131921092068960990⟩
noncomputable def L1396_cp1 : Nat × Nat := t7val% (fastRun pL1396 1 986 (init pL1396) (init pL1396))
theorem L1396_seg1 : segOK pL1396 1 986 (init pL1396) (init pL1396) L1396_cp1.1 L1396_cp1.2 = true := by
  decide +kernel
theorem L1396_fin : (prmOK pL1396 1396 && ptTest pL1396 (runFrom pL1396 (fmask pL1396) (cmask pL1396) (hmask pL1396) 987 409 (true, L1396_cp1.1, L1396_cp1.2)) 1396 698 false) = true := by
  decide +kernel
theorem L1396_ok : RunOK pL1396 1396 (runFrom pL1396 (fmask pL1396) (cmask pL1396) (hmask pL1396) 987 409 (true, L1396_cp1.1, L1396_cp1.2)) ∧ ptTest pL1396 (runFrom pL1396 (fmask pL1396) (cmask pL1396) (hmask pL1396) 987 409 (true, L1396_cp1.1, L1396_cp1.2)) 1396 698 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1396_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1396_fin) true) L1396_seg1) (by decide) rfl L1396_fin ptTest_fst
noncomputable def H1396_cp1 : Nat × Nat := t7val% (fastRun pH1396 1 986 (init pH1396) (init pH1396))
theorem H1396_seg1 : segOK pH1396 1 986 (init pH1396) (init pH1396) H1396_cp1.1 H1396_cp1.2 = true := by
  decide +kernel
theorem H1396_fin : (prmOK pH1396 1396 && ptTest pH1396 (runFrom pH1396 (fmask pH1396) (cmask pH1396) (hmask pH1396) 987 409 (true, H1396_cp1.1, H1396_cp1.2)) 1396 698 true) = true := by
  decide +kernel
theorem H1396_ok : RunOK pH1396 1396 (runFrom pH1396 (fmask pH1396) (cmask pH1396) (hmask pH1396) 987 409 (true, H1396_cp1.1, H1396_cp1.2)) ∧ ptTest pH1396 (runFrom pH1396 (fmask pH1396) (cmask pH1396) (hmask pH1396) 987 409 (true, H1396_cp1.1, H1396_cp1.2)) 1396 698 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1396_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1396_fin) true) H1396_seg1) (by decide) rfl H1396_fin ptTest_fst
noncomputable def I1396_cp1 : Nat × Nat := t7val% (fastRun pI1396 1 986 (init pI1396) (init pI1396))
theorem I1396_seg1 : segOK pI1396 1 986 (init pI1396) (init pI1396) I1396_cp1.1 I1396_cp1.2 = true := by
  decide +kernel
theorem I1396_fin : (prmOK pI1396 1396 && intTest pI1396 (runFrom pI1396 (fmask pI1396) (cmask pI1396) (hmask pI1396) 987 409 (true, I1396_cp1.1, I1396_cp1.2)) 1396 20 true) = true := by
  decide +kernel
theorem I1396_ok : RunOK pI1396 1396 (runFrom pI1396 (fmask pI1396) (cmask pI1396) (hmask pI1396) 987 409 (true, I1396_cp1.1, I1396_cp1.2)) ∧ intTest pI1396 (runFrom pI1396 (fmask pI1396) (cmask pI1396) (hmask pI1396) 987 409 (true, I1396_cp1.1, I1396_cp1.2)) 1396 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1396_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1396_fin) true) I1396_seg1) (by decide) rfl I1396_fin intTest_fst
theorem link1396 : linkOK pL1396 pH1396 pI1396 = true := by decide +kernel
theorem cvx1396 : ConvexBetweenHumps 1396 :=
  cvx_of L1396_ok H1396_ok I1396_ok link1396 (by decide)
theorem cenlink1396 : cenLinkOK pI1396 1396 = true := by decide +kernel
theorem cen1396 : CenterUniqueMin 1396 ∧ DipHyp 1396 ∧ OnePointHyps 1396 :=
  cen_of L1396_ok H1396_ok I1396_ok link1396 cenlink1396

/-! ### `N = 1397` -/

def pL1397 : Prm := ⟨79, 37, 39, 1399, 11, 18446744073709551616, 131843370318872323, 131843370318872323⟩
def pH1397 : Prm := ⟨79, 37, 39, 1399, 11, 18446744073709551616, 131844469830500099, 131844469830500099⟩
def pI1397 : Prm := ⟨67, 32, 32, 1399, 11, 18446744073709551616, 131843370318872323, 131844469830500099⟩
noncomputable def L1397_cp1 : Nat × Nat := t7val% (fastRun pL1397 1 987 (init pL1397) (init pL1397))
theorem L1397_seg1 : segOK pL1397 1 987 (init pL1397) (init pL1397) L1397_cp1.1 L1397_cp1.2 = true := by
  decide +kernel
theorem L1397_fin : (prmOK pL1397 1397 && ptTest pL1397 (runFrom pL1397 (fmask pL1397) (cmask pL1397) (hmask pL1397) 988 409 (true, L1397_cp1.1, L1397_cp1.2)) 1397 699 false) = true := by
  decide +kernel
theorem L1397_ok : RunOK pL1397 1397 (runFrom pL1397 (fmask pL1397) (cmask pL1397) (hmask pL1397) 988 409 (true, L1397_cp1.1, L1397_cp1.2)) ∧ ptTest pL1397 (runFrom pL1397 (fmask pL1397) (cmask pL1397) (hmask pL1397) 988 409 (true, L1397_cp1.1, L1397_cp1.2)) 1397 699 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1397_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1397_fin) true) L1397_seg1) (by decide) rfl L1397_fin ptTest_fst
noncomputable def H1397_cp1 : Nat × Nat := t7val% (fastRun pH1397 1 987 (init pH1397) (init pH1397))
theorem H1397_seg1 : segOK pH1397 1 987 (init pH1397) (init pH1397) H1397_cp1.1 H1397_cp1.2 = true := by
  decide +kernel
theorem H1397_fin : (prmOK pH1397 1397 && ptTest pH1397 (runFrom pH1397 (fmask pH1397) (cmask pH1397) (hmask pH1397) 988 409 (true, H1397_cp1.1, H1397_cp1.2)) 1397 699 true) = true := by
  decide +kernel
theorem H1397_ok : RunOK pH1397 1397 (runFrom pH1397 (fmask pH1397) (cmask pH1397) (hmask pH1397) 988 409 (true, H1397_cp1.1, H1397_cp1.2)) ∧ ptTest pH1397 (runFrom pH1397 (fmask pH1397) (cmask pH1397) (hmask pH1397) 988 409 (true, H1397_cp1.1, H1397_cp1.2)) 1397 699 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1397_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1397_fin) true) H1397_seg1) (by decide) rfl H1397_fin ptTest_fst
noncomputable def I1397_cp1 : Nat × Nat := t7val% (fastRun pI1397 1 987 (init pI1397) (init pI1397))
theorem I1397_seg1 : segOK pI1397 1 987 (init pI1397) (init pI1397) I1397_cp1.1 I1397_cp1.2 = true := by
  decide +kernel
theorem I1397_fin : (prmOK pI1397 1397 && intTest pI1397 (runFrom pI1397 (fmask pI1397) (cmask pI1397) (hmask pI1397) 988 409 (true, I1397_cp1.1, I1397_cp1.2)) 1397 20 false) = true := by
  decide +kernel
theorem I1397_ok : RunOK pI1397 1397 (runFrom pI1397 (fmask pI1397) (cmask pI1397) (hmask pI1397) 988 409 (true, I1397_cp1.1, I1397_cp1.2)) ∧ intTest pI1397 (runFrom pI1397 (fmask pI1397) (cmask pI1397) (hmask pI1397) 988 409 (true, I1397_cp1.1, I1397_cp1.2)) 1397 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1397_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1397_fin) true) I1397_seg1) (by decide) rfl I1397_fin intTest_fst
theorem link1397 : linkOK pL1397 pH1397 pI1397 = true := by decide +kernel
theorem cvx1397 : ConvexBetweenHumps 1397 :=
  cvx_of L1397_ok H1397_ok I1397_ok link1397 (by decide)

/-! ### `N = 1398` -/

def pL1398 : Prm := ⟨79, 37, 39, 1400, 11, 18446744073709551616, 131766886570596944, 131766886570596944⟩
def pH1398 : Prm := ⟨79, 37, 39, 1400, 11, 18446744073709551616, 131767986082224720, 131767986082224720⟩
def pI1398 : Prm := ⟨65, 33, 29, 1400, 11, 18446744073709551616, 131766886570596944, 131767986082224720⟩
noncomputable def L1398_cp1 : Nat × Nat := t7val% (fastRun pL1398 1 988 (init pL1398) (init pL1398))
theorem L1398_seg1 : segOK pL1398 1 988 (init pL1398) (init pL1398) L1398_cp1.1 L1398_cp1.2 = true := by
  decide +kernel
theorem L1398_fin : (prmOK pL1398 1398 && ptTest pL1398 (runFrom pL1398 (fmask pL1398) (cmask pL1398) (hmask pL1398) 989 409 (true, L1398_cp1.1, L1398_cp1.2)) 1398 699 false) = true := by
  decide +kernel
theorem L1398_ok : RunOK pL1398 1398 (runFrom pL1398 (fmask pL1398) (cmask pL1398) (hmask pL1398) 989 409 (true, L1398_cp1.1, L1398_cp1.2)) ∧ ptTest pL1398 (runFrom pL1398 (fmask pL1398) (cmask pL1398) (hmask pL1398) 989 409 (true, L1398_cp1.1, L1398_cp1.2)) 1398 699 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1398_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1398_fin) true) L1398_seg1) (by decide) rfl L1398_fin ptTest_fst
noncomputable def H1398_cp1 : Nat × Nat := t7val% (fastRun pH1398 1 988 (init pH1398) (init pH1398))
theorem H1398_seg1 : segOK pH1398 1 988 (init pH1398) (init pH1398) H1398_cp1.1 H1398_cp1.2 = true := by
  decide +kernel
theorem H1398_fin : (prmOK pH1398 1398 && ptTest pH1398 (runFrom pH1398 (fmask pH1398) (cmask pH1398) (hmask pH1398) 989 409 (true, H1398_cp1.1, H1398_cp1.2)) 1398 699 true) = true := by
  decide +kernel
theorem H1398_ok : RunOK pH1398 1398 (runFrom pH1398 (fmask pH1398) (cmask pH1398) (hmask pH1398) 989 409 (true, H1398_cp1.1, H1398_cp1.2)) ∧ ptTest pH1398 (runFrom pH1398 (fmask pH1398) (cmask pH1398) (hmask pH1398) 989 409 (true, H1398_cp1.1, H1398_cp1.2)) 1398 699 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1398_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1398_fin) true) H1398_seg1) (by decide) rfl H1398_fin ptTest_fst
noncomputable def I1398_cp1 : Nat × Nat := t7val% (fastRun pI1398 1 988 (init pI1398) (init pI1398))
theorem I1398_seg1 : segOK pI1398 1 988 (init pI1398) (init pI1398) I1398_cp1.1 I1398_cp1.2 = true := by
  decide +kernel
theorem I1398_fin : (prmOK pI1398 1398 && intTest pI1398 (runFrom pI1398 (fmask pI1398) (cmask pI1398) (hmask pI1398) 989 409 (true, I1398_cp1.1, I1398_cp1.2)) 1398 20 true) = true := by
  decide +kernel
theorem I1398_ok : RunOK pI1398 1398 (runFrom pI1398 (fmask pI1398) (cmask pI1398) (hmask pI1398) 989 409 (true, I1398_cp1.1, I1398_cp1.2)) ∧ intTest pI1398 (runFrom pI1398 (fmask pI1398) (cmask pI1398) (hmask pI1398) 989 409 (true, I1398_cp1.1, I1398_cp1.2)) 1398 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1398_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1398_fin) true) I1398_seg1) (by decide) rfl I1398_fin intTest_fst
theorem link1398 : linkOK pL1398 pH1398 pI1398 = true := by decide +kernel
theorem cvx1398 : ConvexBetweenHumps 1398 :=
  cvx_of L1398_ok H1398_ok I1398_ok link1398 (by decide)
theorem cenlink1398 : cenLinkOK pI1398 1398 = true := by decide +kernel
theorem cen1398 : CenterUniqueMin 1398 ∧ DipHyp 1398 ∧ OnePointHyps 1398 :=
  cen_of L1398_ok H1398_ok I1398_ok link1398 cenlink1398

/-! ### `N = 1399` -/

def pL1399 : Prm := ⟨79, 37, 39, 1401, 11, 18446744073709551616, 131690457883565229, 131690457883565229⟩
def pH1399 : Prm := ⟨79, 37, 39, 1401, 11, 18446744073709551616, 131691557395193005, 131691557395193005⟩
def pI1399 : Prm := ⟨65, 33, 29, 1401, 11, 18446744073709551616, 131690457883565229, 131691557395193005⟩
noncomputable def L1399_cp1 : Nat × Nat := t7val% (fastRun pL1399 1 988 (init pL1399) (init pL1399))
theorem L1399_seg1 : segOK pL1399 1 988 (init pL1399) (init pL1399) L1399_cp1.1 L1399_cp1.2 = true := by
  decide +kernel
theorem L1399_fin : (prmOK pL1399 1399 && ptTest pL1399 (runFrom pL1399 (fmask pL1399) (cmask pL1399) (hmask pL1399) 989 410 (true, L1399_cp1.1, L1399_cp1.2)) 1399 700 false) = true := by
  decide +kernel
theorem L1399_ok : RunOK pL1399 1399 (runFrom pL1399 (fmask pL1399) (cmask pL1399) (hmask pL1399) 989 410 (true, L1399_cp1.1, L1399_cp1.2)) ∧ ptTest pL1399 (runFrom pL1399 (fmask pL1399) (cmask pL1399) (hmask pL1399) 989 410 (true, L1399_cp1.1, L1399_cp1.2)) 1399 700 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1399_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1399_fin) true) L1399_seg1) (by decide) rfl L1399_fin ptTest_fst
noncomputable def H1399_cp1 : Nat × Nat := t7val% (fastRun pH1399 1 988 (init pH1399) (init pH1399))
theorem H1399_seg1 : segOK pH1399 1 988 (init pH1399) (init pH1399) H1399_cp1.1 H1399_cp1.2 = true := by
  decide +kernel
theorem H1399_fin : (prmOK pH1399 1399 && ptTest pH1399 (runFrom pH1399 (fmask pH1399) (cmask pH1399) (hmask pH1399) 989 410 (true, H1399_cp1.1, H1399_cp1.2)) 1399 700 true) = true := by
  decide +kernel
theorem H1399_ok : RunOK pH1399 1399 (runFrom pH1399 (fmask pH1399) (cmask pH1399) (hmask pH1399) 989 410 (true, H1399_cp1.1, H1399_cp1.2)) ∧ ptTest pH1399 (runFrom pH1399 (fmask pH1399) (cmask pH1399) (hmask pH1399) 989 410 (true, H1399_cp1.1, H1399_cp1.2)) 1399 700 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1399_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1399_fin) true) H1399_seg1) (by decide) rfl H1399_fin ptTest_fst
noncomputable def I1399_cp1 : Nat × Nat := t7val% (fastRun pI1399 1 988 (init pI1399) (init pI1399))
theorem I1399_seg1 : segOK pI1399 1 988 (init pI1399) (init pI1399) I1399_cp1.1 I1399_cp1.2 = true := by
  decide +kernel
theorem I1399_fin : (prmOK pI1399 1399 && intTest pI1399 (runFrom pI1399 (fmask pI1399) (cmask pI1399) (hmask pI1399) 989 410 (true, I1399_cp1.1, I1399_cp1.2)) 1399 20 false) = true := by
  decide +kernel
theorem I1399_ok : RunOK pI1399 1399 (runFrom pI1399 (fmask pI1399) (cmask pI1399) (hmask pI1399) 989 410 (true, I1399_cp1.1, I1399_cp1.2)) ∧ intTest pI1399 (runFrom pI1399 (fmask pI1399) (cmask pI1399) (hmask pI1399) 989 410 (true, I1399_cp1.1, I1399_cp1.2)) 1399 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1399_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1399_fin) true) I1399_seg1) (by decide) rfl I1399_fin intTest_fst
theorem link1399 : linkOK pL1399 pH1399 pI1399 = true := by decide +kernel
theorem cvx1399 : ConvexBetweenHumps 1399 :=
  cvx_of L1399_ok H1399_ok I1399_ok link1399 (by decide)

/-! ### `N = 1400` -/

def pL1400 : Prm := ⟨79, 37, 39, 1402, 11, 18446744073709551616, 131614167127026364, 131614167127026364⟩
def pH1400 : Prm := ⟨79, 37, 39, 1402, 11, 18446744073709551616, 131615266638654140, 131615266638654140⟩
def pI1400 : Prm := ⟨65, 33, 29, 1402, 11, 18446744073709551616, 131614167127026364, 131615266638654140⟩
noncomputable def L1400_cp1 : Nat × Nat := t7val% (fastRun pL1400 1 989 (init pL1400) (init pL1400))
theorem L1400_seg1 : segOK pL1400 1 989 (init pL1400) (init pL1400) L1400_cp1.1 L1400_cp1.2 = true := by
  decide +kernel
theorem L1400_fin : (prmOK pL1400 1400 && ptTest pL1400 (runFrom pL1400 (fmask pL1400) (cmask pL1400) (hmask pL1400) 990 410 (true, L1400_cp1.1, L1400_cp1.2)) 1400 700 false) = true := by
  decide +kernel
theorem L1400_ok : RunOK pL1400 1400 (runFrom pL1400 (fmask pL1400) (cmask pL1400) (hmask pL1400) 990 410 (true, L1400_cp1.1, L1400_cp1.2)) ∧ ptTest pL1400 (runFrom pL1400 (fmask pL1400) (cmask pL1400) (hmask pL1400) 990 410 (true, L1400_cp1.1, L1400_cp1.2)) 1400 700 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1400_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1400_fin) true) L1400_seg1) (by decide) rfl L1400_fin ptTest_fst
noncomputable def H1400_cp1 : Nat × Nat := t7val% (fastRun pH1400 1 989 (init pH1400) (init pH1400))
theorem H1400_seg1 : segOK pH1400 1 989 (init pH1400) (init pH1400) H1400_cp1.1 H1400_cp1.2 = true := by
  decide +kernel
theorem H1400_fin : (prmOK pH1400 1400 && ptTest pH1400 (runFrom pH1400 (fmask pH1400) (cmask pH1400) (hmask pH1400) 990 410 (true, H1400_cp1.1, H1400_cp1.2)) 1400 700 true) = true := by
  decide +kernel
theorem H1400_ok : RunOK pH1400 1400 (runFrom pH1400 (fmask pH1400) (cmask pH1400) (hmask pH1400) 990 410 (true, H1400_cp1.1, H1400_cp1.2)) ∧ ptTest pH1400 (runFrom pH1400 (fmask pH1400) (cmask pH1400) (hmask pH1400) 990 410 (true, H1400_cp1.1, H1400_cp1.2)) 1400 700 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1400_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1400_fin) true) H1400_seg1) (by decide) rfl H1400_fin ptTest_fst
noncomputable def I1400_cp1 : Nat × Nat := t7val% (fastRun pI1400 1 989 (init pI1400) (init pI1400))
theorem I1400_seg1 : segOK pI1400 1 989 (init pI1400) (init pI1400) I1400_cp1.1 I1400_cp1.2 = true := by
  decide +kernel
theorem I1400_fin : (prmOK pI1400 1400 && intTest pI1400 (runFrom pI1400 (fmask pI1400) (cmask pI1400) (hmask pI1400) 990 410 (true, I1400_cp1.1, I1400_cp1.2)) 1400 20 true) = true := by
  decide +kernel
theorem I1400_ok : RunOK pI1400 1400 (runFrom pI1400 (fmask pI1400) (cmask pI1400) (hmask pI1400) 990 410 (true, I1400_cp1.1, I1400_cp1.2)) ∧ intTest pI1400 (runFrom pI1400 (fmask pI1400) (cmask pI1400) (hmask pI1400) 990 410 (true, I1400_cp1.1, I1400_cp1.2)) 1400 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1400_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1400_fin) true) I1400_seg1) (by decide) rfl I1400_fin intTest_fst
theorem link1400 : linkOK pL1400 pH1400 pI1400 = true := by decide +kernel
theorem cvx1400 : ConvexBetweenHumps 1400 :=
  cvx_of L1400_ok H1400_ok I1400_ok link1400 (by decide)
theorem cenlink1400 : cenLinkOK pI1400 1400 = true := by decide +kernel
theorem cen1400 : CenterUniqueMin 1400 ∧ DipHyp 1400 ∧ OnePointHyps 1400 :=
  cen_of L1400_ok H1400_ok I1400_ok link1400 cenlink1400

/-! ### `N = 1401` -/

def pL1401 : Prm := ⟨79, 37, 39, 1403, 11, 18446744073709551616, 131537931235291786, 131537931235291786⟩
def pH1401 : Prm := ⟨79, 37, 39, 1403, 11, 18446744073709551616, 131539030746919562, 131539030746919562⟩
def pI1401 : Prm := ⟨65, 33, 29, 1403, 11, 18446744073709551616, 131537931235291786, 131539030746919562⟩
noncomputable def L1401_cp1 : Nat × Nat := t7val% (fastRun pL1401 1 990 (init pL1401) (init pL1401))
theorem L1401_seg1 : segOK pL1401 1 990 (init pL1401) (init pL1401) L1401_cp1.1 L1401_cp1.2 = true := by
  decide +kernel
theorem L1401_fin : (prmOK pL1401 1401 && ptTest pL1401 (runFrom pL1401 (fmask pL1401) (cmask pL1401) (hmask pL1401) 991 410 (true, L1401_cp1.1, L1401_cp1.2)) 1401 701 false) = true := by
  decide +kernel
theorem L1401_ok : RunOK pL1401 1401 (runFrom pL1401 (fmask pL1401) (cmask pL1401) (hmask pL1401) 991 410 (true, L1401_cp1.1, L1401_cp1.2)) ∧ ptTest pL1401 (runFrom pL1401 (fmask pL1401) (cmask pL1401) (hmask pL1401) 991 410 (true, L1401_cp1.1, L1401_cp1.2)) 1401 701 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1401_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1401_fin) true) L1401_seg1) (by decide) rfl L1401_fin ptTest_fst
noncomputable def H1401_cp1 : Nat × Nat := t7val% (fastRun pH1401 1 990 (init pH1401) (init pH1401))
theorem H1401_seg1 : segOK pH1401 1 990 (init pH1401) (init pH1401) H1401_cp1.1 H1401_cp1.2 = true := by
  decide +kernel
theorem H1401_fin : (prmOK pH1401 1401 && ptTest pH1401 (runFrom pH1401 (fmask pH1401) (cmask pH1401) (hmask pH1401) 991 410 (true, H1401_cp1.1, H1401_cp1.2)) 1401 701 true) = true := by
  decide +kernel
theorem H1401_ok : RunOK pH1401 1401 (runFrom pH1401 (fmask pH1401) (cmask pH1401) (hmask pH1401) 991 410 (true, H1401_cp1.1, H1401_cp1.2)) ∧ ptTest pH1401 (runFrom pH1401 (fmask pH1401) (cmask pH1401) (hmask pH1401) 991 410 (true, H1401_cp1.1, H1401_cp1.2)) 1401 701 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1401_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1401_fin) true) H1401_seg1) (by decide) rfl H1401_fin ptTest_fst
noncomputable def I1401_cp1 : Nat × Nat := t7val% (fastRun pI1401 1 990 (init pI1401) (init pI1401))
theorem I1401_seg1 : segOK pI1401 1 990 (init pI1401) (init pI1401) I1401_cp1.1 I1401_cp1.2 = true := by
  decide +kernel
theorem I1401_fin : (prmOK pI1401 1401 && intTest pI1401 (runFrom pI1401 (fmask pI1401) (cmask pI1401) (hmask pI1401) 991 410 (true, I1401_cp1.1, I1401_cp1.2)) 1401 20 false) = true := by
  decide +kernel
theorem I1401_ok : RunOK pI1401 1401 (runFrom pI1401 (fmask pI1401) (cmask pI1401) (hmask pI1401) 991 410 (true, I1401_cp1.1, I1401_cp1.2)) ∧ intTest pI1401 (runFrom pI1401 (fmask pI1401) (cmask pI1401) (hmask pI1401) 991 410 (true, I1401_cp1.1, I1401_cp1.2)) 1401 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1401_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1401_fin) true) I1401_seg1) (by decide) rfl I1401_fin intTest_fst
theorem link1401 : linkOK pL1401 pH1401 pI1401 = true := by decide +kernel
theorem cvx1401 : ConvexBetweenHumps 1401 :=
  cvx_of L1401_ok H1401_ok I1401_ok link1401 (by decide)

/-! ### The range -/

theorem cvx_1381_1401 {N : ℕ} (h1 : 1381 ≤ N) (h2 : N ≤ 1401) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1390
  · by_cases h4 : N ≤ 1385
    · by_cases h6 : N ≤ 1382
      · by_cases h8 : N ≤ 1381
        · obtain rfl : N = 1381 := by omega
          exact cvx1381
        · obtain rfl : N = 1382 := by omega
          exact cvx1382
      · by_cases h8 : N ≤ 1383
        · obtain rfl : N = 1383 := by omega
          exact cvx1383
        · by_cases h10 : N ≤ 1384
          · obtain rfl : N = 1384 := by omega
            exact cvx1384
          · obtain rfl : N = 1385 := by omega
            exact cvx1385
    · by_cases h6 : N ≤ 1387
      · by_cases h8 : N ≤ 1386
        · obtain rfl : N = 1386 := by omega
          exact cvx1386
        · obtain rfl : N = 1387 := by omega
          exact cvx1387
      · by_cases h8 : N ≤ 1388
        · obtain rfl : N = 1388 := by omega
          exact cvx1388
        · by_cases h10 : N ≤ 1389
          · obtain rfl : N = 1389 := by omega
            exact cvx1389
          · obtain rfl : N = 1390 := by omega
            exact cvx1390
  · by_cases h4 : N ≤ 1395
    · by_cases h6 : N ≤ 1392
      · by_cases h8 : N ≤ 1391
        · obtain rfl : N = 1391 := by omega
          exact cvx1391
        · obtain rfl : N = 1392 := by omega
          exact cvx1392
      · by_cases h8 : N ≤ 1393
        · obtain rfl : N = 1393 := by omega
          exact cvx1393
        · by_cases h10 : N ≤ 1394
          · obtain rfl : N = 1394 := by omega
            exact cvx1394
          · obtain rfl : N = 1395 := by omega
            exact cvx1395
    · by_cases h6 : N ≤ 1398
      · by_cases h8 : N ≤ 1396
        · obtain rfl : N = 1396 := by omega
          exact cvx1396
        · by_cases h10 : N ≤ 1397
          · obtain rfl : N = 1397 := by omega
            exact cvx1397
          · obtain rfl : N = 1398 := by omega
            exact cvx1398
      · by_cases h8 : N ≤ 1399
        · obtain rfl : N = 1399 := by omega
          exact cvx1399
        · by_cases h10 : N ≤ 1400
          · obtain rfl : N = 1400 := by omega
            exact cvx1400
          · obtain rfl : N = 1401 := by omega
            exact cvx1401

theorem cen_1381_1401 {N : ℕ} (h1 : 1381 ≤ N) (h2 : N ≤ 1401) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1390
  · by_cases h4 : N ≤ 1384
    · by_cases h6 : N ≤ 1382
      · obtain rfl : N = 1382 := by omega
        exact cen1382
      · obtain rfl : N = 1384 := by omega
        exact cen1384
    · by_cases h6 : N ≤ 1386
      · obtain rfl : N = 1386 := by omega
        exact cen1386
      · by_cases h8 : N ≤ 1388
        · obtain rfl : N = 1388 := by omega
          exact cen1388
        · obtain rfl : N = 1390 := by omega
          exact cen1390
  · by_cases h4 : N ≤ 1394
    · by_cases h6 : N ≤ 1392
      · obtain rfl : N = 1392 := by omega
        exact cen1392
      · obtain rfl : N = 1394 := by omega
        exact cen1394
    · by_cases h6 : N ≤ 1396
      · obtain rfl : N = 1396 := by omega
        exact cen1396
      · by_cases h8 : N ≤ 1398
        · obtain rfl : N = 1398 := by omega
          exact cen1398
        · obtain rfl : N = 1400 := by omega
          exact cen1400

end Kagey131.PaperD.T7
