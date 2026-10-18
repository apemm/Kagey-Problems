import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1212, …, 1239` (generated)

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

/-! ### `N = 1212` -/

def pL1212 : Prm := ⟨76, 35, 38, 1214, 11, 18446744073709551616, 147890283943411159, 147890283943411159⟩
def pH1212 : Prm := ⟨76, 35, 38, 1214, 11, 18446744073709551616, 147892482966666711, 147892482966666711⟩
def pI1212 : Prm := ⟨67, 32, 32, 1214, 11, 18446744073709551616, 147890283943411159, 147892482966666711⟩
noncomputable def L1212_cp1 : Nat × Nat := t7val% (fastRun pL1212 1 856 (init pL1212) (init pL1212))
theorem L1212_seg1 : segOK pL1212 1 856 (init pL1212) (init pL1212) L1212_cp1.1 L1212_cp1.2 = true := by
  decide +kernel
theorem L1212_fin : (prmOK pL1212 1212 && ptTest pL1212 (runFrom pL1212 (fmask pL1212) (cmask pL1212) (hmask pL1212) 857 355 (true, L1212_cp1.1, L1212_cp1.2)) 1212 606 false) = true := by
  decide +kernel
theorem L1212_ok : RunOK pL1212 1212 (runFrom pL1212 (fmask pL1212) (cmask pL1212) (hmask pL1212) 857 355 (true, L1212_cp1.1, L1212_cp1.2)) ∧ ptTest pL1212 (runFrom pL1212 (fmask pL1212) (cmask pL1212) (hmask pL1212) 857 355 (true, L1212_cp1.1, L1212_cp1.2)) 1212 606 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1212_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1212_fin) true) L1212_seg1) (by decide) rfl L1212_fin ptTest_fst
noncomputable def H1212_cp1 : Nat × Nat := t7val% (fastRun pH1212 1 856 (init pH1212) (init pH1212))
theorem H1212_seg1 : segOK pH1212 1 856 (init pH1212) (init pH1212) H1212_cp1.1 H1212_cp1.2 = true := by
  decide +kernel
theorem H1212_fin : (prmOK pH1212 1212 && ptTest pH1212 (runFrom pH1212 (fmask pH1212) (cmask pH1212) (hmask pH1212) 857 355 (true, H1212_cp1.1, H1212_cp1.2)) 1212 606 true) = true := by
  decide +kernel
theorem H1212_ok : RunOK pH1212 1212 (runFrom pH1212 (fmask pH1212) (cmask pH1212) (hmask pH1212) 857 355 (true, H1212_cp1.1, H1212_cp1.2)) ∧ ptTest pH1212 (runFrom pH1212 (fmask pH1212) (cmask pH1212) (hmask pH1212) 857 355 (true, H1212_cp1.1, H1212_cp1.2)) 1212 606 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1212_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1212_fin) true) H1212_seg1) (by decide) rfl H1212_fin ptTest_fst
theorem I1212_fin : (prmOK pI1212 1212 && intTest pI1212 (runFrom pI1212 (fmask pI1212) (cmask pI1212) (hmask pI1212) 1 1211 (true, (init pI1212), (init pI1212))) 1212 19 true) = true := by
  decide +kernel
theorem I1212_ok : RunOK pI1212 1212 (runFrom pI1212 (fmask pI1212) (cmask pI1212) (hmask pI1212) 1 1211 (true, (init pI1212), (init pI1212))) ∧ intTest pI1212 (runFrom pI1212 (fmask pI1212) (cmask pI1212) (hmask pI1212) 1 1211 (true, (init pI1212), (init pI1212))) 1212 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1212_fin) true) (by decide) rfl I1212_fin intTest_fst
theorem link1212 : linkOK pL1212 pH1212 pI1212 = true := by decide +kernel
theorem cvx1212 : ConvexBetweenHumps 1212 :=
  cvx_of L1212_ok H1212_ok I1212_ok link1212 (by decide)
theorem cenlink1212 : cenLinkOK pI1212 1212 = true := by decide +kernel
theorem cen1212 : CenterUniqueMin 1212 ∧ DipHyp 1212 ∧ OnePointHyps 1212 :=
  cen_of L1212_ok H1212_ok I1212_ok link1212 cenlink1212

/-! ### `N = 1213` -/

def pL1213 : Prm := ⟨76, 35, 38, 1215, 11, 18446744073709551616, 147791983234480025, 147791983234480025⟩
def pH1213 : Prm := ⟨76, 35, 38, 1215, 11, 18446744073709551616, 147794182257735577, 147794182257735577⟩
def pI1213 : Prm := ⟨67, 32, 32, 1215, 11, 18446744073709551616, 147791983234480025, 147794182257735577⟩
noncomputable def L1213_cp1 : Nat × Nat := t7val% (fastRun pL1213 1 857 (init pL1213) (init pL1213))
theorem L1213_seg1 : segOK pL1213 1 857 (init pL1213) (init pL1213) L1213_cp1.1 L1213_cp1.2 = true := by
  decide +kernel
theorem L1213_fin : (prmOK pL1213 1213 && ptTest pL1213 (runFrom pL1213 (fmask pL1213) (cmask pL1213) (hmask pL1213) 858 355 (true, L1213_cp1.1, L1213_cp1.2)) 1213 607 false) = true := by
  decide +kernel
theorem L1213_ok : RunOK pL1213 1213 (runFrom pL1213 (fmask pL1213) (cmask pL1213) (hmask pL1213) 858 355 (true, L1213_cp1.1, L1213_cp1.2)) ∧ ptTest pL1213 (runFrom pL1213 (fmask pL1213) (cmask pL1213) (hmask pL1213) 858 355 (true, L1213_cp1.1, L1213_cp1.2)) 1213 607 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1213_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1213_fin) true) L1213_seg1) (by decide) rfl L1213_fin ptTest_fst
noncomputable def H1213_cp1 : Nat × Nat := t7val% (fastRun pH1213 1 857 (init pH1213) (init pH1213))
theorem H1213_seg1 : segOK pH1213 1 857 (init pH1213) (init pH1213) H1213_cp1.1 H1213_cp1.2 = true := by
  decide +kernel
theorem H1213_fin : (prmOK pH1213 1213 && ptTest pH1213 (runFrom pH1213 (fmask pH1213) (cmask pH1213) (hmask pH1213) 858 355 (true, H1213_cp1.1, H1213_cp1.2)) 1213 607 true) = true := by
  decide +kernel
theorem H1213_ok : RunOK pH1213 1213 (runFrom pH1213 (fmask pH1213) (cmask pH1213) (hmask pH1213) 858 355 (true, H1213_cp1.1, H1213_cp1.2)) ∧ ptTest pH1213 (runFrom pH1213 (fmask pH1213) (cmask pH1213) (hmask pH1213) 858 355 (true, H1213_cp1.1, H1213_cp1.2)) 1213 607 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1213_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1213_fin) true) H1213_seg1) (by decide) rfl H1213_fin ptTest_fst
theorem I1213_fin : (prmOK pI1213 1213 && intTest pI1213 (runFrom pI1213 (fmask pI1213) (cmask pI1213) (hmask pI1213) 1 1212 (true, (init pI1213), (init pI1213))) 1213 19 false) = true := by
  decide +kernel
theorem I1213_ok : RunOK pI1213 1213 (runFrom pI1213 (fmask pI1213) (cmask pI1213) (hmask pI1213) 1 1212 (true, (init pI1213), (init pI1213))) ∧ intTest pI1213 (runFrom pI1213 (fmask pI1213) (cmask pI1213) (hmask pI1213) 1 1212 (true, (init pI1213), (init pI1213))) 1213 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1213_fin) true) (by decide) rfl I1213_fin intTest_fst
theorem link1213 : linkOK pL1213 pH1213 pI1213 = true := by decide +kernel
theorem cvx1213 : ConvexBetweenHumps 1213 :=
  cvx_of L1213_ok H1213_ok I1213_ok link1213 (by decide)

/-! ### `N = 1214` -/

def pL1214 : Prm := ⟨76, 35, 38, 1216, 11, 18446744073709551616, 147693889037180838, 147693889037180838⟩
def pH1214 : Prm := ⟨76, 35, 38, 1216, 11, 18446744073709551616, 147696088060436390, 147696088060436390⟩
def pI1214 : Prm := ⟨67, 32, 32, 1216, 11, 18446744073709551616, 147693889037180838, 147696088060436390⟩
noncomputable def L1214_cp1 : Nat × Nat := t7val% (fastRun pL1214 1 857 (init pL1214) (init pL1214))
theorem L1214_seg1 : segOK pL1214 1 857 (init pL1214) (init pL1214) L1214_cp1.1 L1214_cp1.2 = true := by
  decide +kernel
theorem L1214_fin : (prmOK pL1214 1214 && ptTest pL1214 (runFrom pL1214 (fmask pL1214) (cmask pL1214) (hmask pL1214) 858 356 (true, L1214_cp1.1, L1214_cp1.2)) 1214 607 false) = true := by
  decide +kernel
theorem L1214_ok : RunOK pL1214 1214 (runFrom pL1214 (fmask pL1214) (cmask pL1214) (hmask pL1214) 858 356 (true, L1214_cp1.1, L1214_cp1.2)) ∧ ptTest pL1214 (runFrom pL1214 (fmask pL1214) (cmask pL1214) (hmask pL1214) 858 356 (true, L1214_cp1.1, L1214_cp1.2)) 1214 607 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1214_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1214_fin) true) L1214_seg1) (by decide) rfl L1214_fin ptTest_fst
noncomputable def H1214_cp1 : Nat × Nat := t7val% (fastRun pH1214 1 857 (init pH1214) (init pH1214))
theorem H1214_seg1 : segOK pH1214 1 857 (init pH1214) (init pH1214) H1214_cp1.1 H1214_cp1.2 = true := by
  decide +kernel
theorem H1214_fin : (prmOK pH1214 1214 && ptTest pH1214 (runFrom pH1214 (fmask pH1214) (cmask pH1214) (hmask pH1214) 858 356 (true, H1214_cp1.1, H1214_cp1.2)) 1214 607 true) = true := by
  decide +kernel
theorem H1214_ok : RunOK pH1214 1214 (runFrom pH1214 (fmask pH1214) (cmask pH1214) (hmask pH1214) 858 356 (true, H1214_cp1.1, H1214_cp1.2)) ∧ ptTest pH1214 (runFrom pH1214 (fmask pH1214) (cmask pH1214) (hmask pH1214) 858 356 (true, H1214_cp1.1, H1214_cp1.2)) 1214 607 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1214_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1214_fin) true) H1214_seg1) (by decide) rfl H1214_fin ptTest_fst
theorem I1214_fin : (prmOK pI1214 1214 && intTest pI1214 (runFrom pI1214 (fmask pI1214) (cmask pI1214) (hmask pI1214) 1 1213 (true, (init pI1214), (init pI1214))) 1214 19 true) = true := by
  decide +kernel
theorem I1214_ok : RunOK pI1214 1214 (runFrom pI1214 (fmask pI1214) (cmask pI1214) (hmask pI1214) 1 1213 (true, (init pI1214), (init pI1214))) ∧ intTest pI1214 (runFrom pI1214 (fmask pI1214) (cmask pI1214) (hmask pI1214) 1 1213 (true, (init pI1214), (init pI1214))) 1214 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1214_fin) true) (by decide) rfl I1214_fin intTest_fst
theorem link1214 : linkOK pL1214 pH1214 pI1214 = true := by decide +kernel
theorem cvx1214 : ConvexBetweenHumps 1214 :=
  cvx_of L1214_ok H1214_ok I1214_ok link1214 (by decide)
theorem cenlink1214 : cenLinkOK pI1214 1214 = true := by decide +kernel
theorem cen1214 : CenterUniqueMin 1214 ∧ DipHyp 1214 ∧ OnePointHyps 1214 :=
  cen_of L1214_ok H1214_ok I1214_ok link1214 cenlink1214

/-! ### `N = 1215` -/

def pL1215 : Prm := ⟨76, 35, 38, 1217, 11, 18446744073709551616, 147595872981045865, 147595872981045865⟩
def pH1215 : Prm := ⟨76, 35, 38, 1217, 11, 18446744073709551616, 147598072004301417, 147598072004301417⟩
def pI1215 : Prm := ⟨67, 32, 32, 1217, 11, 18446744073709551616, 147595872981045865, 147598072004301417⟩
noncomputable def L1215_cp1 : Nat × Nat := t7val% (fastRun pL1215 1 858 (init pL1215) (init pL1215))
theorem L1215_seg1 : segOK pL1215 1 858 (init pL1215) (init pL1215) L1215_cp1.1 L1215_cp1.2 = true := by
  decide +kernel
theorem L1215_fin : (prmOK pL1215 1215 && ptTest pL1215 (runFrom pL1215 (fmask pL1215) (cmask pL1215) (hmask pL1215) 859 356 (true, L1215_cp1.1, L1215_cp1.2)) 1215 608 false) = true := by
  decide +kernel
theorem L1215_ok : RunOK pL1215 1215 (runFrom pL1215 (fmask pL1215) (cmask pL1215) (hmask pL1215) 859 356 (true, L1215_cp1.1, L1215_cp1.2)) ∧ ptTest pL1215 (runFrom pL1215 (fmask pL1215) (cmask pL1215) (hmask pL1215) 859 356 (true, L1215_cp1.1, L1215_cp1.2)) 1215 608 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1215_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1215_fin) true) L1215_seg1) (by decide) rfl L1215_fin ptTest_fst
noncomputable def H1215_cp1 : Nat × Nat := t7val% (fastRun pH1215 1 858 (init pH1215) (init pH1215))
theorem H1215_seg1 : segOK pH1215 1 858 (init pH1215) (init pH1215) H1215_cp1.1 H1215_cp1.2 = true := by
  decide +kernel
theorem H1215_fin : (prmOK pH1215 1215 && ptTest pH1215 (runFrom pH1215 (fmask pH1215) (cmask pH1215) (hmask pH1215) 859 356 (true, H1215_cp1.1, H1215_cp1.2)) 1215 608 true) = true := by
  decide +kernel
theorem H1215_ok : RunOK pH1215 1215 (runFrom pH1215 (fmask pH1215) (cmask pH1215) (hmask pH1215) 859 356 (true, H1215_cp1.1, H1215_cp1.2)) ∧ ptTest pH1215 (runFrom pH1215 (fmask pH1215) (cmask pH1215) (hmask pH1215) 859 356 (true, H1215_cp1.1, H1215_cp1.2)) 1215 608 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1215_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1215_fin) true) H1215_seg1) (by decide) rfl H1215_fin ptTest_fst
theorem I1215_fin : (prmOK pI1215 1215 && intTest pI1215 (runFrom pI1215 (fmask pI1215) (cmask pI1215) (hmask pI1215) 1 1214 (true, (init pI1215), (init pI1215))) 1215 19 false) = true := by
  decide +kernel
theorem I1215_ok : RunOK pI1215 1215 (runFrom pI1215 (fmask pI1215) (cmask pI1215) (hmask pI1215) 1 1214 (true, (init pI1215), (init pI1215))) ∧ intTest pI1215 (runFrom pI1215 (fmask pI1215) (cmask pI1215) (hmask pI1215) 1 1214 (true, (init pI1215), (init pI1215))) 1215 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1215_fin) true) (by decide) rfl I1215_fin intTest_fst
theorem link1215 : linkOK pL1215 pH1215 pI1215 = true := by decide +kernel
theorem cvx1215 : ConvexBetweenHumps 1215 :=
  cvx_of L1215_ok H1215_ok I1215_ok link1215 (by decide)

/-! ### `N = 1216` -/

def pL1216 : Prm := ⟨76, 35, 38, 1218, 11, 18446744073709551616, 147498062476795637, 147498062476795637⟩
def pH1216 : Prm := ⟨76, 35, 38, 1218, 11, 18446744073709551616, 147500261500051189, 147500261500051189⟩
def pI1216 : Prm := ⟨65, 33, 29, 1218, 11, 18446744073709551616, 147498062476795637, 147500261500051189⟩
noncomputable def L1216_cp1 : Nat × Nat := t7val% (fastRun pL1216 1 859 (init pL1216) (init pL1216))
theorem L1216_seg1 : segOK pL1216 1 859 (init pL1216) (init pL1216) L1216_cp1.1 L1216_cp1.2 = true := by
  decide +kernel
theorem L1216_fin : (prmOK pL1216 1216 && ptTest pL1216 (runFrom pL1216 (fmask pL1216) (cmask pL1216) (hmask pL1216) 860 356 (true, L1216_cp1.1, L1216_cp1.2)) 1216 608 false) = true := by
  decide +kernel
theorem L1216_ok : RunOK pL1216 1216 (runFrom pL1216 (fmask pL1216) (cmask pL1216) (hmask pL1216) 860 356 (true, L1216_cp1.1, L1216_cp1.2)) ∧ ptTest pL1216 (runFrom pL1216 (fmask pL1216) (cmask pL1216) (hmask pL1216) 860 356 (true, L1216_cp1.1, L1216_cp1.2)) 1216 608 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1216_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1216_fin) true) L1216_seg1) (by decide) rfl L1216_fin ptTest_fst
noncomputable def H1216_cp1 : Nat × Nat := t7val% (fastRun pH1216 1 859 (init pH1216) (init pH1216))
theorem H1216_seg1 : segOK pH1216 1 859 (init pH1216) (init pH1216) H1216_cp1.1 H1216_cp1.2 = true := by
  decide +kernel
theorem H1216_fin : (prmOK pH1216 1216 && ptTest pH1216 (runFrom pH1216 (fmask pH1216) (cmask pH1216) (hmask pH1216) 860 356 (true, H1216_cp1.1, H1216_cp1.2)) 1216 608 true) = true := by
  decide +kernel
theorem H1216_ok : RunOK pH1216 1216 (runFrom pH1216 (fmask pH1216) (cmask pH1216) (hmask pH1216) 860 356 (true, H1216_cp1.1, H1216_cp1.2)) ∧ ptTest pH1216 (runFrom pH1216 (fmask pH1216) (cmask pH1216) (hmask pH1216) 860 356 (true, H1216_cp1.1, H1216_cp1.2)) 1216 608 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1216_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1216_fin) true) H1216_seg1) (by decide) rfl H1216_fin ptTest_fst
theorem I1216_fin : (prmOK pI1216 1216 && intTest pI1216 (runFrom pI1216 (fmask pI1216) (cmask pI1216) (hmask pI1216) 1 1215 (true, (init pI1216), (init pI1216))) 1216 19 true) = true := by
  decide +kernel
theorem I1216_ok : RunOK pI1216 1216 (runFrom pI1216 (fmask pI1216) (cmask pI1216) (hmask pI1216) 1 1215 (true, (init pI1216), (init pI1216))) ∧ intTest pI1216 (runFrom pI1216 (fmask pI1216) (cmask pI1216) (hmask pI1216) 1 1215 (true, (init pI1216), (init pI1216))) 1216 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1216_fin) true) (by decide) rfl I1216_fin intTest_fst
theorem link1216 : linkOK pL1216 pH1216 pI1216 = true := by decide +kernel
theorem cvx1216 : ConvexBetweenHumps 1216 :=
  cvx_of L1216_ok H1216_ok I1216_ok link1216 (by decide)
theorem cenlink1216 : cenLinkOK pI1216 1216 = true := by decide +kernel
theorem cen1216 : CenterUniqueMin 1216 ∧ DipHyp 1216 ∧ OnePointHyps 1216 :=
  cen_of L1216_ok H1216_ok I1216_ok link1216 cenlink1216

/-! ### `N = 1217` -/

def pL1217 : Prm := ⟨76, 35, 38, 1219, 11, 18446744073709551616, 147400329797827576, 147400329797827576⟩
def pH1217 : Prm := ⟨76, 35, 38, 1219, 11, 18446744073709551616, 147402528821083128, 147402528821083128⟩
def pI1217 : Prm := ⟨67, 32, 32, 1219, 11, 18446744073709551616, 147400329797827576, 147402528821083128⟩
noncomputable def L1217_cp1 : Nat × Nat := t7val% (fastRun pL1217 1 860 (init pL1217) (init pL1217))
theorem L1217_seg1 : segOK pL1217 1 860 (init pL1217) (init pL1217) L1217_cp1.1 L1217_cp1.2 = true := by
  decide +kernel
theorem L1217_fin : (prmOK pL1217 1217 && ptTest pL1217 (runFrom pL1217 (fmask pL1217) (cmask pL1217) (hmask pL1217) 861 356 (true, L1217_cp1.1, L1217_cp1.2)) 1217 609 false) = true := by
  decide +kernel
theorem L1217_ok : RunOK pL1217 1217 (runFrom pL1217 (fmask pL1217) (cmask pL1217) (hmask pL1217) 861 356 (true, L1217_cp1.1, L1217_cp1.2)) ∧ ptTest pL1217 (runFrom pL1217 (fmask pL1217) (cmask pL1217) (hmask pL1217) 861 356 (true, L1217_cp1.1, L1217_cp1.2)) 1217 609 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1217_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1217_fin) true) L1217_seg1) (by decide) rfl L1217_fin ptTest_fst
noncomputable def H1217_cp1 : Nat × Nat := t7val% (fastRun pH1217 1 860 (init pH1217) (init pH1217))
theorem H1217_seg1 : segOK pH1217 1 860 (init pH1217) (init pH1217) H1217_cp1.1 H1217_cp1.2 = true := by
  decide +kernel
theorem H1217_fin : (prmOK pH1217 1217 && ptTest pH1217 (runFrom pH1217 (fmask pH1217) (cmask pH1217) (hmask pH1217) 861 356 (true, H1217_cp1.1, H1217_cp1.2)) 1217 609 true) = true := by
  decide +kernel
theorem H1217_ok : RunOK pH1217 1217 (runFrom pH1217 (fmask pH1217) (cmask pH1217) (hmask pH1217) 861 356 (true, H1217_cp1.1, H1217_cp1.2)) ∧ ptTest pH1217 (runFrom pH1217 (fmask pH1217) (cmask pH1217) (hmask pH1217) 861 356 (true, H1217_cp1.1, H1217_cp1.2)) 1217 609 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1217_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1217_fin) true) H1217_seg1) (by decide) rfl H1217_fin ptTest_fst
theorem I1217_fin : (prmOK pI1217 1217 && intTest pI1217 (runFrom pI1217 (fmask pI1217) (cmask pI1217) (hmask pI1217) 1 1216 (true, (init pI1217), (init pI1217))) 1217 19 false) = true := by
  decide +kernel
theorem I1217_ok : RunOK pI1217 1217 (runFrom pI1217 (fmask pI1217) (cmask pI1217) (hmask pI1217) 1 1216 (true, (init pI1217), (init pI1217))) ∧ intTest pI1217 (runFrom pI1217 (fmask pI1217) (cmask pI1217) (hmask pI1217) 1 1216 (true, (init pI1217), (init pI1217))) 1217 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1217_fin) true) (by decide) rfl I1217_fin intTest_fst
theorem link1217 : linkOK pL1217 pH1217 pI1217 = true := by decide +kernel
theorem cvx1217 : ConvexBetweenHumps 1217 :=
  cvx_of L1217_ok H1217_ok I1217_ok link1217 (by decide)

/-! ### `N = 1218` -/

def pL1218 : Prm := ⟨76, 35, 38, 1220, 11, 18446744073709551616, 147302801717010698, 147302801717010698⟩
def pH1218 : Prm := ⟨76, 35, 38, 1220, 11, 18446744073709551616, 147305000740266250, 147305000740266250⟩
def pI1218 : Prm := ⟨67, 32, 32, 1220, 11, 18446744073709551616, 147302801717010698, 147305000740266250⟩
noncomputable def L1218_cp1 : Nat × Nat := t7val% (fastRun pL1218 1 860 (init pL1218) (init pL1218))
theorem L1218_seg1 : segOK pL1218 1 860 (init pL1218) (init pL1218) L1218_cp1.1 L1218_cp1.2 = true := by
  decide +kernel
theorem L1218_fin : (prmOK pL1218 1218 && ptTest pL1218 (runFrom pL1218 (fmask pL1218) (cmask pL1218) (hmask pL1218) 861 357 (true, L1218_cp1.1, L1218_cp1.2)) 1218 609 false) = true := by
  decide +kernel
theorem L1218_ok : RunOK pL1218 1218 (runFrom pL1218 (fmask pL1218) (cmask pL1218) (hmask pL1218) 861 357 (true, L1218_cp1.1, L1218_cp1.2)) ∧ ptTest pL1218 (runFrom pL1218 (fmask pL1218) (cmask pL1218) (hmask pL1218) 861 357 (true, L1218_cp1.1, L1218_cp1.2)) 1218 609 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1218_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1218_fin) true) L1218_seg1) (by decide) rfl L1218_fin ptTest_fst
noncomputable def H1218_cp1 : Nat × Nat := t7val% (fastRun pH1218 1 860 (init pH1218) (init pH1218))
theorem H1218_seg1 : segOK pH1218 1 860 (init pH1218) (init pH1218) H1218_cp1.1 H1218_cp1.2 = true := by
  decide +kernel
theorem H1218_fin : (prmOK pH1218 1218 && ptTest pH1218 (runFrom pH1218 (fmask pH1218) (cmask pH1218) (hmask pH1218) 861 357 (true, H1218_cp1.1, H1218_cp1.2)) 1218 609 true) = true := by
  decide +kernel
theorem H1218_ok : RunOK pH1218 1218 (runFrom pH1218 (fmask pH1218) (cmask pH1218) (hmask pH1218) 861 357 (true, H1218_cp1.1, H1218_cp1.2)) ∧ ptTest pH1218 (runFrom pH1218 (fmask pH1218) (cmask pH1218) (hmask pH1218) 861 357 (true, H1218_cp1.1, H1218_cp1.2)) 1218 609 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1218_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1218_fin) true) H1218_seg1) (by decide) rfl H1218_fin ptTest_fst
theorem I1218_fin : (prmOK pI1218 1218 && intTest pI1218 (runFrom pI1218 (fmask pI1218) (cmask pI1218) (hmask pI1218) 1 1217 (true, (init pI1218), (init pI1218))) 1218 19 true) = true := by
  decide +kernel
theorem I1218_ok : RunOK pI1218 1218 (runFrom pI1218 (fmask pI1218) (cmask pI1218) (hmask pI1218) 1 1217 (true, (init pI1218), (init pI1218))) ∧ intTest pI1218 (runFrom pI1218 (fmask pI1218) (cmask pI1218) (hmask pI1218) 1 1217 (true, (init pI1218), (init pI1218))) 1218 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1218_fin) true) (by decide) rfl I1218_fin intTest_fst
theorem link1218 : linkOK pL1218 pH1218 pI1218 = true := by decide +kernel
theorem cvx1218 : ConvexBetweenHumps 1218 :=
  cvx_of L1218_ok H1218_ok I1218_ok link1218 (by decide)
theorem cenlink1218 : cenLinkOK pI1218 1218 = true := by decide +kernel
theorem cen1218 : CenterUniqueMin 1218 ∧ DipHyp 1218 ∧ OnePointHyps 1218 :=
  cen_of L1218_ok H1218_ok I1218_ok link1218 cenlink1218

/-! ### `N = 1219` -/

def pL1219 : Prm := ⟨76, 35, 38, 1221, 11, 18446744073709551616, 147205351147327937, 147205351147327937⟩
def pH1219 : Prm := ⟨76, 35, 38, 1221, 11, 18446744073709551616, 147207550170583489, 147207550170583489⟩
def pI1219 : Prm := ⟨65, 33, 29, 1221, 11, 18446744073709551616, 147205351147327937, 147207550170583489⟩
noncomputable def L1219_cp1 : Nat × Nat := t7val% (fastRun pL1219 1 861 (init pL1219) (init pL1219))
theorem L1219_seg1 : segOK pL1219 1 861 (init pL1219) (init pL1219) L1219_cp1.1 L1219_cp1.2 = true := by
  decide +kernel
theorem L1219_fin : (prmOK pL1219 1219 && ptTest pL1219 (runFrom pL1219 (fmask pL1219) (cmask pL1219) (hmask pL1219) 862 357 (true, L1219_cp1.1, L1219_cp1.2)) 1219 610 false) = true := by
  decide +kernel
theorem L1219_ok : RunOK pL1219 1219 (runFrom pL1219 (fmask pL1219) (cmask pL1219) (hmask pL1219) 862 357 (true, L1219_cp1.1, L1219_cp1.2)) ∧ ptTest pL1219 (runFrom pL1219 (fmask pL1219) (cmask pL1219) (hmask pL1219) 862 357 (true, L1219_cp1.1, L1219_cp1.2)) 1219 610 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1219_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1219_fin) true) L1219_seg1) (by decide) rfl L1219_fin ptTest_fst
noncomputable def H1219_cp1 : Nat × Nat := t7val% (fastRun pH1219 1 861 (init pH1219) (init pH1219))
theorem H1219_seg1 : segOK pH1219 1 861 (init pH1219) (init pH1219) H1219_cp1.1 H1219_cp1.2 = true := by
  decide +kernel
theorem H1219_fin : (prmOK pH1219 1219 && ptTest pH1219 (runFrom pH1219 (fmask pH1219) (cmask pH1219) (hmask pH1219) 862 357 (true, H1219_cp1.1, H1219_cp1.2)) 1219 610 true) = true := by
  decide +kernel
theorem H1219_ok : RunOK pH1219 1219 (runFrom pH1219 (fmask pH1219) (cmask pH1219) (hmask pH1219) 862 357 (true, H1219_cp1.1, H1219_cp1.2)) ∧ ptTest pH1219 (runFrom pH1219 (fmask pH1219) (cmask pH1219) (hmask pH1219) 862 357 (true, H1219_cp1.1, H1219_cp1.2)) 1219 610 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1219_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1219_fin) true) H1219_seg1) (by decide) rfl H1219_fin ptTest_fst
theorem I1219_fin : (prmOK pI1219 1219 && intTest pI1219 (runFrom pI1219 (fmask pI1219) (cmask pI1219) (hmask pI1219) 1 1218 (true, (init pI1219), (init pI1219))) 1219 19 false) = true := by
  decide +kernel
theorem I1219_ok : RunOK pI1219 1219 (runFrom pI1219 (fmask pI1219) (cmask pI1219) (hmask pI1219) 1 1218 (true, (init pI1219), (init pI1219))) ∧ intTest pI1219 (runFrom pI1219 (fmask pI1219) (cmask pI1219) (hmask pI1219) 1 1218 (true, (init pI1219), (init pI1219))) 1219 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1219_fin) true) (by decide) rfl I1219_fin intTest_fst
theorem link1219 : linkOK pL1219 pH1219 pI1219 = true := by decide +kernel
theorem cvx1219 : ConvexBetweenHumps 1219 :=
  cvx_of L1219_ok H1219_ok I1219_ok link1219 (by decide)

/-! ### `N = 1220` -/

def pL1220 : Prm := ⟨76, 35, 38, 1222, 11, 18446744073709551616, 147108104228039542, 147108104228039542⟩
def pH1220 : Prm := ⟨76, 35, 38, 1222, 11, 18446744073709551616, 147110303251295094, 147110303251295094⟩
def pI1220 : Prm := ⟨65, 33, 29, 1222, 11, 18446744073709551616, 147108104228039542, 147110303251295094⟩
noncomputable def L1220_cp1 : Nat × Nat := t7val% (fastRun pL1220 1 862 (init pL1220) (init pL1220))
theorem L1220_seg1 : segOK pL1220 1 862 (init pL1220) (init pL1220) L1220_cp1.1 L1220_cp1.2 = true := by
  decide +kernel
theorem L1220_fin : (prmOK pL1220 1220 && ptTest pL1220 (runFrom pL1220 (fmask pL1220) (cmask pL1220) (hmask pL1220) 863 357 (true, L1220_cp1.1, L1220_cp1.2)) 1220 610 false) = true := by
  decide +kernel
theorem L1220_ok : RunOK pL1220 1220 (runFrom pL1220 (fmask pL1220) (cmask pL1220) (hmask pL1220) 863 357 (true, L1220_cp1.1, L1220_cp1.2)) ∧ ptTest pL1220 (runFrom pL1220 (fmask pL1220) (cmask pL1220) (hmask pL1220) 863 357 (true, L1220_cp1.1, L1220_cp1.2)) 1220 610 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1220_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1220_fin) true) L1220_seg1) (by decide) rfl L1220_fin ptTest_fst
noncomputable def H1220_cp1 : Nat × Nat := t7val% (fastRun pH1220 1 862 (init pH1220) (init pH1220))
theorem H1220_seg1 : segOK pH1220 1 862 (init pH1220) (init pH1220) H1220_cp1.1 H1220_cp1.2 = true := by
  decide +kernel
theorem H1220_fin : (prmOK pH1220 1220 && ptTest pH1220 (runFrom pH1220 (fmask pH1220) (cmask pH1220) (hmask pH1220) 863 357 (true, H1220_cp1.1, H1220_cp1.2)) 1220 610 true) = true := by
  decide +kernel
theorem H1220_ok : RunOK pH1220 1220 (runFrom pH1220 (fmask pH1220) (cmask pH1220) (hmask pH1220) 863 357 (true, H1220_cp1.1, H1220_cp1.2)) ∧ ptTest pH1220 (runFrom pH1220 (fmask pH1220) (cmask pH1220) (hmask pH1220) 863 357 (true, H1220_cp1.1, H1220_cp1.2)) 1220 610 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1220_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1220_fin) true) H1220_seg1) (by decide) rfl H1220_fin ptTest_fst
theorem I1220_fin : (prmOK pI1220 1220 && intTest pI1220 (runFrom pI1220 (fmask pI1220) (cmask pI1220) (hmask pI1220) 1 1219 (true, (init pI1220), (init pI1220))) 1220 19 true) = true := by
  decide +kernel
theorem I1220_ok : RunOK pI1220 1220 (runFrom pI1220 (fmask pI1220) (cmask pI1220) (hmask pI1220) 1 1219 (true, (init pI1220), (init pI1220))) ∧ intTest pI1220 (runFrom pI1220 (fmask pI1220) (cmask pI1220) (hmask pI1220) 1 1219 (true, (init pI1220), (init pI1220))) 1220 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1220_fin) true) (by decide) rfl I1220_fin intTest_fst
theorem link1220 : linkOK pL1220 pH1220 pI1220 = true := by decide +kernel
theorem cvx1220 : ConvexBetweenHumps 1220 :=
  cvx_of L1220_ok H1220_ok I1220_ok link1220 (by decide)
theorem cenlink1220 : cenLinkOK pI1220 1220 = true := by decide +kernel
theorem cen1220 : CenterUniqueMin 1220 ∧ DipHyp 1220 ∧ OnePointHyps 1220 :=
  cen_of L1220_ok H1220_ok I1220_ok link1220 cenlink1220

/-! ### `N = 1221` -/

def pL1221 : Prm := ⟨76, 35, 38, 1223, 11, 18446744073709551616, 147010934507471206, 147010934507471206⟩
def pH1221 : Prm := ⟨76, 35, 38, 1223, 11, 18446744073709551616, 147013133530726758, 147013133530726758⟩
def pI1221 : Prm := ⟨65, 33, 29, 1223, 11, 18446744073709551616, 147010934507471206, 147013133530726758⟩
noncomputable def L1221_cp1 : Nat × Nat := t7val% (fastRun pL1221 1 862 (init pL1221) (init pL1221))
theorem L1221_seg1 : segOK pL1221 1 862 (init pL1221) (init pL1221) L1221_cp1.1 L1221_cp1.2 = true := by
  decide +kernel
theorem L1221_fin : (prmOK pL1221 1221 && ptTest pL1221 (runFrom pL1221 (fmask pL1221) (cmask pL1221) (hmask pL1221) 863 358 (true, L1221_cp1.1, L1221_cp1.2)) 1221 611 false) = true := by
  decide +kernel
theorem L1221_ok : RunOK pL1221 1221 (runFrom pL1221 (fmask pL1221) (cmask pL1221) (hmask pL1221) 863 358 (true, L1221_cp1.1, L1221_cp1.2)) ∧ ptTest pL1221 (runFrom pL1221 (fmask pL1221) (cmask pL1221) (hmask pL1221) 863 358 (true, L1221_cp1.1, L1221_cp1.2)) 1221 611 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1221_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1221_fin) true) L1221_seg1) (by decide) rfl L1221_fin ptTest_fst
noncomputable def H1221_cp1 : Nat × Nat := t7val% (fastRun pH1221 1 862 (init pH1221) (init pH1221))
theorem H1221_seg1 : segOK pH1221 1 862 (init pH1221) (init pH1221) H1221_cp1.1 H1221_cp1.2 = true := by
  decide +kernel
theorem H1221_fin : (prmOK pH1221 1221 && ptTest pH1221 (runFrom pH1221 (fmask pH1221) (cmask pH1221) (hmask pH1221) 863 358 (true, H1221_cp1.1, H1221_cp1.2)) 1221 611 true) = true := by
  decide +kernel
theorem H1221_ok : RunOK pH1221 1221 (runFrom pH1221 (fmask pH1221) (cmask pH1221) (hmask pH1221) 863 358 (true, H1221_cp1.1, H1221_cp1.2)) ∧ ptTest pH1221 (runFrom pH1221 (fmask pH1221) (cmask pH1221) (hmask pH1221) 863 358 (true, H1221_cp1.1, H1221_cp1.2)) 1221 611 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1221_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1221_fin) true) H1221_seg1) (by decide) rfl H1221_fin ptTest_fst
theorem I1221_fin : (prmOK pI1221 1221 && intTest pI1221 (runFrom pI1221 (fmask pI1221) (cmask pI1221) (hmask pI1221) 1 1220 (true, (init pI1221), (init pI1221))) 1221 19 false) = true := by
  decide +kernel
theorem I1221_ok : RunOK pI1221 1221 (runFrom pI1221 (fmask pI1221) (cmask pI1221) (hmask pI1221) 1 1220 (true, (init pI1221), (init pI1221))) ∧ intTest pI1221 (runFrom pI1221 (fmask pI1221) (cmask pI1221) (hmask pI1221) 1 1220 (true, (init pI1221), (init pI1221))) 1221 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1221_fin) true) (by decide) rfl I1221_fin intTest_fst
theorem link1221 : linkOK pL1221 pH1221 pI1221 = true := by decide +kernel
theorem cvx1221 : ConvexBetweenHumps 1221 :=
  cvx_of L1221_ok H1221_ok I1221_ok link1221 (by decide)

/-! ### `N = 1222` -/

def pL1222 : Prm := ⟨76, 35, 38, 1224, 11, 18446744073709551616, 146913967495443377, 146913967495443377⟩
def pH1222 : Prm := ⟨76, 35, 38, 1224, 11, 18446744073709551616, 146916166518698929, 146916166518698929⟩
def pI1222 : Prm := ⟨65, 33, 29, 1224, 11, 18446744073709551616, 146913967495443377, 146916166518698929⟩
noncomputable def L1222_cp1 : Nat × Nat := t7val% (fastRun pL1222 1 863 (init pL1222) (init pL1222))
theorem L1222_seg1 : segOK pL1222 1 863 (init pL1222) (init pL1222) L1222_cp1.1 L1222_cp1.2 = true := by
  decide +kernel
theorem L1222_fin : (prmOK pL1222 1222 && ptTest pL1222 (runFrom pL1222 (fmask pL1222) (cmask pL1222) (hmask pL1222) 864 358 (true, L1222_cp1.1, L1222_cp1.2)) 1222 611 false) = true := by
  decide +kernel
theorem L1222_ok : RunOK pL1222 1222 (runFrom pL1222 (fmask pL1222) (cmask pL1222) (hmask pL1222) 864 358 (true, L1222_cp1.1, L1222_cp1.2)) ∧ ptTest pL1222 (runFrom pL1222 (fmask pL1222) (cmask pL1222) (hmask pL1222) 864 358 (true, L1222_cp1.1, L1222_cp1.2)) 1222 611 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1222_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1222_fin) true) L1222_seg1) (by decide) rfl L1222_fin ptTest_fst
noncomputable def H1222_cp1 : Nat × Nat := t7val% (fastRun pH1222 1 863 (init pH1222) (init pH1222))
theorem H1222_seg1 : segOK pH1222 1 863 (init pH1222) (init pH1222) H1222_cp1.1 H1222_cp1.2 = true := by
  decide +kernel
theorem H1222_fin : (prmOK pH1222 1222 && ptTest pH1222 (runFrom pH1222 (fmask pH1222) (cmask pH1222) (hmask pH1222) 864 358 (true, H1222_cp1.1, H1222_cp1.2)) 1222 611 true) = true := by
  decide +kernel
theorem H1222_ok : RunOK pH1222 1222 (runFrom pH1222 (fmask pH1222) (cmask pH1222) (hmask pH1222) 864 358 (true, H1222_cp1.1, H1222_cp1.2)) ∧ ptTest pH1222 (runFrom pH1222 (fmask pH1222) (cmask pH1222) (hmask pH1222) 864 358 (true, H1222_cp1.1, H1222_cp1.2)) 1222 611 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1222_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1222_fin) true) H1222_seg1) (by decide) rfl H1222_fin ptTest_fst
theorem I1222_fin : (prmOK pI1222 1222 && intTest pI1222 (runFrom pI1222 (fmask pI1222) (cmask pI1222) (hmask pI1222) 1 1221 (true, (init pI1222), (init pI1222))) 1222 19 true) = true := by
  decide +kernel
theorem I1222_ok : RunOK pI1222 1222 (runFrom pI1222 (fmask pI1222) (cmask pI1222) (hmask pI1222) 1 1221 (true, (init pI1222), (init pI1222))) ∧ intTest pI1222 (runFrom pI1222 (fmask pI1222) (cmask pI1222) (hmask pI1222) 1 1221 (true, (init pI1222), (init pI1222))) 1222 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1222_fin) true) (by decide) rfl I1222_fin intTest_fst
theorem link1222 : linkOK pL1222 pH1222 pI1222 = true := by decide +kernel
theorem cvx1222 : ConvexBetweenHumps 1222 :=
  cvx_of L1222_ok H1222_ok I1222_ok link1222 (by decide)
theorem cenlink1222 : cenLinkOK pI1222 1222 = true := by decide +kernel
theorem cen1222 : CenterUniqueMin 1222 ∧ DipHyp 1222 ∧ OnePointHyps 1222 :=
  cen_of L1222_ok H1222_ok I1222_ok link1222 cenlink1222

/-! ### `N = 1223` -/

def pL1223 : Prm := ⟨76, 35, 38, 1225, 11, 18446744073709551616, 146817077371400202, 146817077371400202⟩
def pH1223 : Prm := ⟨76, 35, 38, 1225, 11, 18446744073709551616, 146819276394655754, 146819276394655754⟩
def pI1223 : Prm := ⟨67, 32, 32, 1225, 11, 18446744073709551616, 146817077371400202, 146819276394655754⟩
noncomputable def L1223_cp1 : Nat × Nat := t7val% (fastRun pL1223 1 864 (init pL1223) (init pL1223))
theorem L1223_seg1 : segOK pL1223 1 864 (init pL1223) (init pL1223) L1223_cp1.1 L1223_cp1.2 = true := by
  decide +kernel
theorem L1223_fin : (prmOK pL1223 1223 && ptTest pL1223 (runFrom pL1223 (fmask pL1223) (cmask pL1223) (hmask pL1223) 865 358 (true, L1223_cp1.1, L1223_cp1.2)) 1223 612 false) = true := by
  decide +kernel
theorem L1223_ok : RunOK pL1223 1223 (runFrom pL1223 (fmask pL1223) (cmask pL1223) (hmask pL1223) 865 358 (true, L1223_cp1.1, L1223_cp1.2)) ∧ ptTest pL1223 (runFrom pL1223 (fmask pL1223) (cmask pL1223) (hmask pL1223) 865 358 (true, L1223_cp1.1, L1223_cp1.2)) 1223 612 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1223_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1223_fin) true) L1223_seg1) (by decide) rfl L1223_fin ptTest_fst
noncomputable def H1223_cp1 : Nat × Nat := t7val% (fastRun pH1223 1 864 (init pH1223) (init pH1223))
theorem H1223_seg1 : segOK pH1223 1 864 (init pH1223) (init pH1223) H1223_cp1.1 H1223_cp1.2 = true := by
  decide +kernel
theorem H1223_fin : (prmOK pH1223 1223 && ptTest pH1223 (runFrom pH1223 (fmask pH1223) (cmask pH1223) (hmask pH1223) 865 358 (true, H1223_cp1.1, H1223_cp1.2)) 1223 612 true) = true := by
  decide +kernel
theorem H1223_ok : RunOK pH1223 1223 (runFrom pH1223 (fmask pH1223) (cmask pH1223) (hmask pH1223) 865 358 (true, H1223_cp1.1, H1223_cp1.2)) ∧ ptTest pH1223 (runFrom pH1223 (fmask pH1223) (cmask pH1223) (hmask pH1223) 865 358 (true, H1223_cp1.1, H1223_cp1.2)) 1223 612 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1223_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1223_fin) true) H1223_seg1) (by decide) rfl H1223_fin ptTest_fst
theorem I1223_fin : (prmOK pI1223 1223 && intTest pI1223 (runFrom pI1223 (fmask pI1223) (cmask pI1223) (hmask pI1223) 1 1222 (true, (init pI1223), (init pI1223))) 1223 19 false) = true := by
  decide +kernel
theorem I1223_ok : RunOK pI1223 1223 (runFrom pI1223 (fmask pI1223) (cmask pI1223) (hmask pI1223) 1 1222 (true, (init pI1223), (init pI1223))) ∧ intTest pI1223 (runFrom pI1223 (fmask pI1223) (cmask pI1223) (hmask pI1223) 1 1222 (true, (init pI1223), (init pI1223))) 1223 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1223_fin) true) (by decide) rfl I1223_fin intTest_fst
theorem link1223 : linkOK pL1223 pH1223 pI1223 = true := by decide +kernel
theorem cvx1223 : ConvexBetweenHumps 1223 :=
  cvx_of L1223_ok H1223_ok I1223_ok link1223 (by decide)

/-! ### `N = 1224` -/

def pL1224 : Prm := ⟨76, 35, 38, 1226, 11, 18446744073709551616, 146720389019928188, 146720389019928188⟩
def pH1224 : Prm := ⟨76, 35, 38, 1226, 11, 18446744073709551616, 146722588043183740, 146722588043183740⟩
def pI1224 : Prm := ⟨65, 33, 29, 1226, 11, 18446744073709551616, 146720389019928188, 146722588043183740⟩
noncomputable def L1224_cp1 : Nat × Nat := t7val% (fastRun pL1224 1 864 (init pL1224) (init pL1224))
theorem L1224_seg1 : segOK pL1224 1 864 (init pL1224) (init pL1224) L1224_cp1.1 L1224_cp1.2 = true := by
  decide +kernel
theorem L1224_fin : (prmOK pL1224 1224 && ptTest pL1224 (runFrom pL1224 (fmask pL1224) (cmask pL1224) (hmask pL1224) 865 359 (true, L1224_cp1.1, L1224_cp1.2)) 1224 612 false) = true := by
  decide +kernel
theorem L1224_ok : RunOK pL1224 1224 (runFrom pL1224 (fmask pL1224) (cmask pL1224) (hmask pL1224) 865 359 (true, L1224_cp1.1, L1224_cp1.2)) ∧ ptTest pL1224 (runFrom pL1224 (fmask pL1224) (cmask pL1224) (hmask pL1224) 865 359 (true, L1224_cp1.1, L1224_cp1.2)) 1224 612 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1224_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1224_fin) true) L1224_seg1) (by decide) rfl L1224_fin ptTest_fst
noncomputable def H1224_cp1 : Nat × Nat := t7val% (fastRun pH1224 1 864 (init pH1224) (init pH1224))
theorem H1224_seg1 : segOK pH1224 1 864 (init pH1224) (init pH1224) H1224_cp1.1 H1224_cp1.2 = true := by
  decide +kernel
theorem H1224_fin : (prmOK pH1224 1224 && ptTest pH1224 (runFrom pH1224 (fmask pH1224) (cmask pH1224) (hmask pH1224) 865 359 (true, H1224_cp1.1, H1224_cp1.2)) 1224 612 true) = true := by
  decide +kernel
theorem H1224_ok : RunOK pH1224 1224 (runFrom pH1224 (fmask pH1224) (cmask pH1224) (hmask pH1224) 865 359 (true, H1224_cp1.1, H1224_cp1.2)) ∧ ptTest pH1224 (runFrom pH1224 (fmask pH1224) (cmask pH1224) (hmask pH1224) 865 359 (true, H1224_cp1.1, H1224_cp1.2)) 1224 612 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1224_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1224_fin) true) H1224_seg1) (by decide) rfl H1224_fin ptTest_fst
theorem I1224_fin : (prmOK pI1224 1224 && intTest pI1224 (runFrom pI1224 (fmask pI1224) (cmask pI1224) (hmask pI1224) 1 1223 (true, (init pI1224), (init pI1224))) 1224 19 true) = true := by
  decide +kernel
theorem I1224_ok : RunOK pI1224 1224 (runFrom pI1224 (fmask pI1224) (cmask pI1224) (hmask pI1224) 1 1223 (true, (init pI1224), (init pI1224))) ∧ intTest pI1224 (runFrom pI1224 (fmask pI1224) (cmask pI1224) (hmask pI1224) 1 1223 (true, (init pI1224), (init pI1224))) 1224 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1224_fin) true) (by decide) rfl I1224_fin intTest_fst
theorem link1224 : linkOK pL1224 pH1224 pI1224 = true := by decide +kernel
theorem cvx1224 : ConvexBetweenHumps 1224 :=
  cvx_of L1224_ok H1224_ok I1224_ok link1224 (by decide)
theorem cenlink1224 : cenLinkOK pI1224 1224 = true := by decide +kernel
theorem cen1224 : CenterUniqueMin 1224 ∧ DipHyp 1224 ∧ OnePointHyps 1224 :=
  cen_of L1224_ok H1224_ok I1224_ok link1224 cenlink1224

/-! ### `N = 1225` -/

def pL1225 : Prm := ⟨76, 35, 38, 1227, 11, 18446744073709551616, 146623777247420971, 146623777247420971⟩
def pH1225 : Prm := ⟨76, 35, 38, 1227, 11, 18446744073709551616, 146625976270676523, 146625976270676523⟩
def pI1225 : Prm := ⟨65, 33, 29, 1227, 11, 18446744073709551616, 146623777247420971, 146625976270676523⟩
noncomputable def L1225_cp1 : Nat × Nat := t7val% (fastRun pL1225 1 865 (init pL1225) (init pL1225))
theorem L1225_seg1 : segOK pL1225 1 865 (init pL1225) (init pL1225) L1225_cp1.1 L1225_cp1.2 = true := by
  decide +kernel
theorem L1225_fin : (prmOK pL1225 1225 && ptTest pL1225 (runFrom pL1225 (fmask pL1225) (cmask pL1225) (hmask pL1225) 866 359 (true, L1225_cp1.1, L1225_cp1.2)) 1225 613 false) = true := by
  decide +kernel
theorem L1225_ok : RunOK pL1225 1225 (runFrom pL1225 (fmask pL1225) (cmask pL1225) (hmask pL1225) 866 359 (true, L1225_cp1.1, L1225_cp1.2)) ∧ ptTest pL1225 (runFrom pL1225 (fmask pL1225) (cmask pL1225) (hmask pL1225) 866 359 (true, L1225_cp1.1, L1225_cp1.2)) 1225 613 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1225_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1225_fin) true) L1225_seg1) (by decide) rfl L1225_fin ptTest_fst
noncomputable def H1225_cp1 : Nat × Nat := t7val% (fastRun pH1225 1 865 (init pH1225) (init pH1225))
theorem H1225_seg1 : segOK pH1225 1 865 (init pH1225) (init pH1225) H1225_cp1.1 H1225_cp1.2 = true := by
  decide +kernel
theorem H1225_fin : (prmOK pH1225 1225 && ptTest pH1225 (runFrom pH1225 (fmask pH1225) (cmask pH1225) (hmask pH1225) 866 359 (true, H1225_cp1.1, H1225_cp1.2)) 1225 613 true) = true := by
  decide +kernel
theorem H1225_ok : RunOK pH1225 1225 (runFrom pH1225 (fmask pH1225) (cmask pH1225) (hmask pH1225) 866 359 (true, H1225_cp1.1, H1225_cp1.2)) ∧ ptTest pH1225 (runFrom pH1225 (fmask pH1225) (cmask pH1225) (hmask pH1225) 866 359 (true, H1225_cp1.1, H1225_cp1.2)) 1225 613 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1225_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1225_fin) true) H1225_seg1) (by decide) rfl H1225_fin ptTest_fst
theorem I1225_fin : (prmOK pI1225 1225 && intTest pI1225 (runFrom pI1225 (fmask pI1225) (cmask pI1225) (hmask pI1225) 1 1224 (true, (init pI1225), (init pI1225))) 1225 19 false) = true := by
  decide +kernel
theorem I1225_ok : RunOK pI1225 1225 (runFrom pI1225 (fmask pI1225) (cmask pI1225) (hmask pI1225) 1 1224 (true, (init pI1225), (init pI1225))) ∧ intTest pI1225 (runFrom pI1225 (fmask pI1225) (cmask pI1225) (hmask pI1225) 1 1224 (true, (init pI1225), (init pI1225))) 1225 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1225_fin) true) (by decide) rfl I1225_fin intTest_fst
theorem link1225 : linkOK pL1225 pH1225 pI1225 = true := by decide +kernel
theorem cvx1225 : ConvexBetweenHumps 1225 :=
  cvx_of L1225_ok H1225_ok I1225_ok link1225 (by decide)

/-! ### `N = 1226` -/

def pL1226 : Prm := ⟨76, 35, 38, 1228, 11, 18446744073709551616, 146527366317363185, 146527366317363185⟩
def pH1226 : Prm := ⟨76, 35, 38, 1228, 11, 18446744073709551616, 146529565340618737, 146529565340618737⟩
def pI1226 : Prm := ⟨65, 33, 29, 1228, 11, 18446744073709551616, 146527366317363185, 146529565340618737⟩
noncomputable def L1226_cp1 : Nat × Nat := t7val% (fastRun pL1226 1 866 (init pL1226) (init pL1226))
theorem L1226_seg1 : segOK pL1226 1 866 (init pL1226) (init pL1226) L1226_cp1.1 L1226_cp1.2 = true := by
  decide +kernel
theorem L1226_fin : (prmOK pL1226 1226 && ptTest pL1226 (runFrom pL1226 (fmask pL1226) (cmask pL1226) (hmask pL1226) 867 359 (true, L1226_cp1.1, L1226_cp1.2)) 1226 613 false) = true := by
  decide +kernel
theorem L1226_ok : RunOK pL1226 1226 (runFrom pL1226 (fmask pL1226) (cmask pL1226) (hmask pL1226) 867 359 (true, L1226_cp1.1, L1226_cp1.2)) ∧ ptTest pL1226 (runFrom pL1226 (fmask pL1226) (cmask pL1226) (hmask pL1226) 867 359 (true, L1226_cp1.1, L1226_cp1.2)) 1226 613 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1226_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1226_fin) true) L1226_seg1) (by decide) rfl L1226_fin ptTest_fst
noncomputable def H1226_cp1 : Nat × Nat := t7val% (fastRun pH1226 1 866 (init pH1226) (init pH1226))
theorem H1226_seg1 : segOK pH1226 1 866 (init pH1226) (init pH1226) H1226_cp1.1 H1226_cp1.2 = true := by
  decide +kernel
theorem H1226_fin : (prmOK pH1226 1226 && ptTest pH1226 (runFrom pH1226 (fmask pH1226) (cmask pH1226) (hmask pH1226) 867 359 (true, H1226_cp1.1, H1226_cp1.2)) 1226 613 true) = true := by
  decide +kernel
theorem H1226_ok : RunOK pH1226 1226 (runFrom pH1226 (fmask pH1226) (cmask pH1226) (hmask pH1226) 867 359 (true, H1226_cp1.1, H1226_cp1.2)) ∧ ptTest pH1226 (runFrom pH1226 (fmask pH1226) (cmask pH1226) (hmask pH1226) 867 359 (true, H1226_cp1.1, H1226_cp1.2)) 1226 613 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1226_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1226_fin) true) H1226_seg1) (by decide) rfl H1226_fin ptTest_fst
theorem I1226_fin : (prmOK pI1226 1226 && intTest pI1226 (runFrom pI1226 (fmask pI1226) (cmask pI1226) (hmask pI1226) 1 1225 (true, (init pI1226), (init pI1226))) 1226 19 true) = true := by
  decide +kernel
theorem I1226_ok : RunOK pI1226 1226 (runFrom pI1226 (fmask pI1226) (cmask pI1226) (hmask pI1226) 1 1225 (true, (init pI1226), (init pI1226))) ∧ intTest pI1226 (runFrom pI1226 (fmask pI1226) (cmask pI1226) (hmask pI1226) 1 1225 (true, (init pI1226), (init pI1226))) 1226 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1226_fin) true) (by decide) rfl I1226_fin intTest_fst
theorem link1226 : linkOK pL1226 pH1226 pI1226 = true := by decide +kernel
theorem cvx1226 : ConvexBetweenHumps 1226 :=
  cvx_of L1226_ok H1226_ok I1226_ok link1226 (by decide)
theorem cenlink1226 : cenLinkOK pI1226 1226 = true := by decide +kernel
theorem cen1226 : CenterUniqueMin 1226 ∧ DipHyp 1226 ∧ OnePointHyps 1226 :=
  cen_of L1226_ok H1226_ok I1226_ok link1226 cenlink1226

/-! ### `N = 1227` -/

def pL1227 : Prm := ⟨76, 35, 38, 1229, 11, 18446744073709551616, 146431031658910546, 146431031658910546⟩
def pH1227 : Prm := ⟨76, 35, 38, 1229, 11, 18446744073709551616, 146433230682166098, 146433230682166098⟩
def pI1227 : Prm := ⟨65, 33, 29, 1229, 11, 18446744073709551616, 146431031658910546, 146433230682166098⟩
noncomputable def L1227_cp1 : Nat × Nat := t7val% (fastRun pL1227 1 867 (init pL1227) (init pL1227))
theorem L1227_seg1 : segOK pL1227 1 867 (init pL1227) (init pL1227) L1227_cp1.1 L1227_cp1.2 = true := by
  decide +kernel
theorem L1227_fin : (prmOK pL1227 1227 && ptTest pL1227 (runFrom pL1227 (fmask pL1227) (cmask pL1227) (hmask pL1227) 868 359 (true, L1227_cp1.1, L1227_cp1.2)) 1227 614 false) = true := by
  decide +kernel
theorem L1227_ok : RunOK pL1227 1227 (runFrom pL1227 (fmask pL1227) (cmask pL1227) (hmask pL1227) 868 359 (true, L1227_cp1.1, L1227_cp1.2)) ∧ ptTest pL1227 (runFrom pL1227 (fmask pL1227) (cmask pL1227) (hmask pL1227) 868 359 (true, L1227_cp1.1, L1227_cp1.2)) 1227 614 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1227_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1227_fin) true) L1227_seg1) (by decide) rfl L1227_fin ptTest_fst
noncomputable def H1227_cp1 : Nat × Nat := t7val% (fastRun pH1227 1 867 (init pH1227) (init pH1227))
theorem H1227_seg1 : segOK pH1227 1 867 (init pH1227) (init pH1227) H1227_cp1.1 H1227_cp1.2 = true := by
  decide +kernel
theorem H1227_fin : (prmOK pH1227 1227 && ptTest pH1227 (runFrom pH1227 (fmask pH1227) (cmask pH1227) (hmask pH1227) 868 359 (true, H1227_cp1.1, H1227_cp1.2)) 1227 614 true) = true := by
  decide +kernel
theorem H1227_ok : RunOK pH1227 1227 (runFrom pH1227 (fmask pH1227) (cmask pH1227) (hmask pH1227) 868 359 (true, H1227_cp1.1, H1227_cp1.2)) ∧ ptTest pH1227 (runFrom pH1227 (fmask pH1227) (cmask pH1227) (hmask pH1227) 868 359 (true, H1227_cp1.1, H1227_cp1.2)) 1227 614 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1227_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1227_fin) true) H1227_seg1) (by decide) rfl H1227_fin ptTest_fst
theorem I1227_fin : (prmOK pI1227 1227 && intTest pI1227 (runFrom pI1227 (fmask pI1227) (cmask pI1227) (hmask pI1227) 1 1226 (true, (init pI1227), (init pI1227))) 1227 19 false) = true := by
  decide +kernel
theorem I1227_ok : RunOK pI1227 1227 (runFrom pI1227 (fmask pI1227) (cmask pI1227) (hmask pI1227) 1 1226 (true, (init pI1227), (init pI1227))) ∧ intTest pI1227 (runFrom pI1227 (fmask pI1227) (cmask pI1227) (hmask pI1227) 1 1226 (true, (init pI1227), (init pI1227))) 1227 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1227_fin) true) (by decide) rfl I1227_fin intTest_fst
theorem link1227 : linkOK pL1227 pH1227 pI1227 = true := by decide +kernel
theorem cvx1227 : ConvexBetweenHumps 1227 :=
  cvx_of L1227_ok H1227_ok I1227_ok link1227 (by decide)

/-! ### `N = 1228` -/

def pL1228 : Prm := ⟨76, 35, 38, 1230, 11, 18446744073709551616, 146334896918540992, 146334896918540992⟩
def pH1228 : Prm := ⟨76, 35, 38, 1230, 11, 18446744073709551616, 146337095941796544, 146337095941796544⟩
def pI1228 : Prm := ⟨65, 33, 29, 1230, 11, 18446744073709551616, 146334896918540992, 146337095941796544⟩
noncomputable def L1228_cp1 : Nat × Nat := t7val% (fastRun pL1228 1 867 (init pL1228) (init pL1228))
theorem L1228_seg1 : segOK pL1228 1 867 (init pL1228) (init pL1228) L1228_cp1.1 L1228_cp1.2 = true := by
  decide +kernel
theorem L1228_fin : (prmOK pL1228 1228 && ptTest pL1228 (runFrom pL1228 (fmask pL1228) (cmask pL1228) (hmask pL1228) 868 360 (true, L1228_cp1.1, L1228_cp1.2)) 1228 614 false) = true := by
  decide +kernel
theorem L1228_ok : RunOK pL1228 1228 (runFrom pL1228 (fmask pL1228) (cmask pL1228) (hmask pL1228) 868 360 (true, L1228_cp1.1, L1228_cp1.2)) ∧ ptTest pL1228 (runFrom pL1228 (fmask pL1228) (cmask pL1228) (hmask pL1228) 868 360 (true, L1228_cp1.1, L1228_cp1.2)) 1228 614 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1228_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1228_fin) true) L1228_seg1) (by decide) rfl L1228_fin ptTest_fst
noncomputable def H1228_cp1 : Nat × Nat := t7val% (fastRun pH1228 1 867 (init pH1228) (init pH1228))
theorem H1228_seg1 : segOK pH1228 1 867 (init pH1228) (init pH1228) H1228_cp1.1 H1228_cp1.2 = true := by
  decide +kernel
theorem H1228_fin : (prmOK pH1228 1228 && ptTest pH1228 (runFrom pH1228 (fmask pH1228) (cmask pH1228) (hmask pH1228) 868 360 (true, H1228_cp1.1, H1228_cp1.2)) 1228 614 true) = true := by
  decide +kernel
theorem H1228_ok : RunOK pH1228 1228 (runFrom pH1228 (fmask pH1228) (cmask pH1228) (hmask pH1228) 868 360 (true, H1228_cp1.1, H1228_cp1.2)) ∧ ptTest pH1228 (runFrom pH1228 (fmask pH1228) (cmask pH1228) (hmask pH1228) 868 360 (true, H1228_cp1.1, H1228_cp1.2)) 1228 614 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1228_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1228_fin) true) H1228_seg1) (by decide) rfl H1228_fin ptTest_fst
theorem I1228_fin : (prmOK pI1228 1228 && intTest pI1228 (runFrom pI1228 (fmask pI1228) (cmask pI1228) (hmask pI1228) 1 1227 (true, (init pI1228), (init pI1228))) 1228 19 true) = true := by
  decide +kernel
theorem I1228_ok : RunOK pI1228 1228 (runFrom pI1228 (fmask pI1228) (cmask pI1228) (hmask pI1228) 1 1227 (true, (init pI1228), (init pI1228))) ∧ intTest pI1228 (runFrom pI1228 (fmask pI1228) (cmask pI1228) (hmask pI1228) 1 1227 (true, (init pI1228), (init pI1228))) 1228 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1228_fin) true) (by decide) rfl I1228_fin intTest_fst
theorem link1228 : linkOK pL1228 pH1228 pI1228 = true := by decide +kernel
theorem cvx1228 : ConvexBetweenHumps 1228 :=
  cvx_of L1228_ok H1228_ok I1228_ok link1228 (by decide)
theorem cenlink1228 : cenLinkOK pI1228 1228 = true := by decide +kernel
theorem cen1228 : CenterUniqueMin 1228 ∧ DipHyp 1228 ∧ OnePointHyps 1228 :=
  cen_of L1228_ok H1228_ok I1228_ok link1228 cenlink1228

/-! ### `N = 1229` -/

def pL1229 : Prm := ⟨76, 35, 38, 1231, 11, 18446744073709551616, 146238838144095590, 146238838144095590⟩
def pH1229 : Prm := ⟨76, 35, 38, 1231, 11, 18446744073709551616, 146241037167351142, 146241037167351142⟩
def pI1229 : Prm := ⟨65, 33, 29, 1231, 11, 18446744073709551616, 146238838144095590, 146241037167351142⟩
noncomputable def L1229_cp1 : Nat × Nat := t7val% (fastRun pL1229 1 868 (init pL1229) (init pL1229))
theorem L1229_seg1 : segOK pL1229 1 868 (init pL1229) (init pL1229) L1229_cp1.1 L1229_cp1.2 = true := by
  decide +kernel
theorem L1229_fin : (prmOK pL1229 1229 && ptTest pL1229 (runFrom pL1229 (fmask pL1229) (cmask pL1229) (hmask pL1229) 869 360 (true, L1229_cp1.1, L1229_cp1.2)) 1229 615 false) = true := by
  decide +kernel
theorem L1229_ok : RunOK pL1229 1229 (runFrom pL1229 (fmask pL1229) (cmask pL1229) (hmask pL1229) 869 360 (true, L1229_cp1.1, L1229_cp1.2)) ∧ ptTest pL1229 (runFrom pL1229 (fmask pL1229) (cmask pL1229) (hmask pL1229) 869 360 (true, L1229_cp1.1, L1229_cp1.2)) 1229 615 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1229_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1229_fin) true) L1229_seg1) (by decide) rfl L1229_fin ptTest_fst
noncomputable def H1229_cp1 : Nat × Nat := t7val% (fastRun pH1229 1 868 (init pH1229) (init pH1229))
theorem H1229_seg1 : segOK pH1229 1 868 (init pH1229) (init pH1229) H1229_cp1.1 H1229_cp1.2 = true := by
  decide +kernel
theorem H1229_fin : (prmOK pH1229 1229 && ptTest pH1229 (runFrom pH1229 (fmask pH1229) (cmask pH1229) (hmask pH1229) 869 360 (true, H1229_cp1.1, H1229_cp1.2)) 1229 615 true) = true := by
  decide +kernel
theorem H1229_ok : RunOK pH1229 1229 (runFrom pH1229 (fmask pH1229) (cmask pH1229) (hmask pH1229) 869 360 (true, H1229_cp1.1, H1229_cp1.2)) ∧ ptTest pH1229 (runFrom pH1229 (fmask pH1229) (cmask pH1229) (hmask pH1229) 869 360 (true, H1229_cp1.1, H1229_cp1.2)) 1229 615 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1229_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1229_fin) true) H1229_seg1) (by decide) rfl H1229_fin ptTest_fst
theorem I1229_fin : (prmOK pI1229 1229 && intTest pI1229 (runFrom pI1229 (fmask pI1229) (cmask pI1229) (hmask pI1229) 1 1228 (true, (init pI1229), (init pI1229))) 1229 19 false) = true := by
  decide +kernel
theorem I1229_ok : RunOK pI1229 1229 (runFrom pI1229 (fmask pI1229) (cmask pI1229) (hmask pI1229) 1 1228 (true, (init pI1229), (init pI1229))) ∧ intTest pI1229 (runFrom pI1229 (fmask pI1229) (cmask pI1229) (hmask pI1229) 1 1228 (true, (init pI1229), (init pI1229))) 1229 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1229_fin) true) (by decide) rfl I1229_fin intTest_fst
theorem link1229 : linkOK pL1229 pH1229 pI1229 = true := by decide +kernel
theorem cvx1229 : ConvexBetweenHumps 1229 :=
  cvx_of L1229_ok H1229_ok I1229_ok link1229 (by decide)

/-! ### `N = 1230` -/

def pL1230 : Prm := ⟨76, 35, 38, 1232, 11, 18446744073709551616, 146142978369140758, 146142978369140758⟩
def pH1230 : Prm := ⟨76, 35, 38, 1232, 11, 18446744073709551616, 146145177392396310, 146145177392396310⟩
def pI1230 : Prm := ⟨65, 33, 29, 1232, 11, 18446744073709551616, 146142978369140758, 146145177392396310⟩
noncomputable def L1230_cp1 : Nat × Nat := t7val% (fastRun pL1230 1 869 (init pL1230) (init pL1230))
theorem L1230_seg1 : segOK pL1230 1 869 (init pL1230) (init pL1230) L1230_cp1.1 L1230_cp1.2 = true := by
  decide +kernel
theorem L1230_fin : (prmOK pL1230 1230 && ptTest pL1230 (runFrom pL1230 (fmask pL1230) (cmask pL1230) (hmask pL1230) 870 360 (true, L1230_cp1.1, L1230_cp1.2)) 1230 615 false) = true := by
  decide +kernel
theorem L1230_ok : RunOK pL1230 1230 (runFrom pL1230 (fmask pL1230) (cmask pL1230) (hmask pL1230) 870 360 (true, L1230_cp1.1, L1230_cp1.2)) ∧ ptTest pL1230 (runFrom pL1230 (fmask pL1230) (cmask pL1230) (hmask pL1230) 870 360 (true, L1230_cp1.1, L1230_cp1.2)) 1230 615 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1230_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1230_fin) true) L1230_seg1) (by decide) rfl L1230_fin ptTest_fst
noncomputable def H1230_cp1 : Nat × Nat := t7val% (fastRun pH1230 1 869 (init pH1230) (init pH1230))
theorem H1230_seg1 : segOK pH1230 1 869 (init pH1230) (init pH1230) H1230_cp1.1 H1230_cp1.2 = true := by
  decide +kernel
theorem H1230_fin : (prmOK pH1230 1230 && ptTest pH1230 (runFrom pH1230 (fmask pH1230) (cmask pH1230) (hmask pH1230) 870 360 (true, H1230_cp1.1, H1230_cp1.2)) 1230 615 true) = true := by
  decide +kernel
theorem H1230_ok : RunOK pH1230 1230 (runFrom pH1230 (fmask pH1230) (cmask pH1230) (hmask pH1230) 870 360 (true, H1230_cp1.1, H1230_cp1.2)) ∧ ptTest pH1230 (runFrom pH1230 (fmask pH1230) (cmask pH1230) (hmask pH1230) 870 360 (true, H1230_cp1.1, H1230_cp1.2)) 1230 615 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1230_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1230_fin) true) H1230_seg1) (by decide) rfl H1230_fin ptTest_fst
theorem I1230_fin : (prmOK pI1230 1230 && intTest pI1230 (runFrom pI1230 (fmask pI1230) (cmask pI1230) (hmask pI1230) 1 1229 (true, (init pI1230), (init pI1230))) 1230 19 true) = true := by
  decide +kernel
theorem I1230_ok : RunOK pI1230 1230 (runFrom pI1230 (fmask pI1230) (cmask pI1230) (hmask pI1230) 1 1229 (true, (init pI1230), (init pI1230))) ∧ intTest pI1230 (runFrom pI1230 (fmask pI1230) (cmask pI1230) (hmask pI1230) 1 1229 (true, (init pI1230), (init pI1230))) 1230 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1230_fin) true) (by decide) rfl I1230_fin intTest_fst
theorem link1230 : linkOK pL1230 pH1230 pI1230 = true := by decide +kernel
theorem cvx1230 : ConvexBetweenHumps 1230 :=
  cvx_of L1230_ok H1230_ok I1230_ok link1230 (by decide)
theorem cenlink1230 : cenLinkOK pI1230 1230 = true := by decide +kernel
theorem cen1230 : CenterUniqueMin 1230 ∧ DipHyp 1230 ∧ OnePointHyps 1230 :=
  cen_of L1230_ok H1230_ok I1230_ok link1230 cenlink1230

/-! ### `N = 1231` -/

def pL1231 : Prm := ⟨76, 35, 38, 1233, 11, 18446744073709551616, 146047194256107736, 146047194256107736⟩
def pH1231 : Prm := ⟨77, 36, 38, 1233, 11, 18446744073709551616, 146049393279363288, 146049393279363288⟩
def pI1231 : Prm := ⟨65, 33, 29, 1233, 11, 18446744073709551616, 146047194256107736, 146049393279363288⟩
noncomputable def L1231_cp1 : Nat × Nat := t7val% (fastRun pL1231 1 869 (init pL1231) (init pL1231))
theorem L1231_seg1 : segOK pL1231 1 869 (init pL1231) (init pL1231) L1231_cp1.1 L1231_cp1.2 = true := by
  decide +kernel
theorem L1231_fin : (prmOK pL1231 1231 && ptTest pL1231 (runFrom pL1231 (fmask pL1231) (cmask pL1231) (hmask pL1231) 870 361 (true, L1231_cp1.1, L1231_cp1.2)) 1231 616 false) = true := by
  decide +kernel
theorem L1231_ok : RunOK pL1231 1231 (runFrom pL1231 (fmask pL1231) (cmask pL1231) (hmask pL1231) 870 361 (true, L1231_cp1.1, L1231_cp1.2)) ∧ ptTest pL1231 (runFrom pL1231 (fmask pL1231) (cmask pL1231) (hmask pL1231) 870 361 (true, L1231_cp1.1, L1231_cp1.2)) 1231 616 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1231_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1231_fin) true) L1231_seg1) (by decide) rfl L1231_fin ptTest_fst
noncomputable def H1231_cp1 : Nat × Nat := t7val% (fastRun pH1231 1 869 (init pH1231) (init pH1231))
theorem H1231_seg1 : segOK pH1231 1 869 (init pH1231) (init pH1231) H1231_cp1.1 H1231_cp1.2 = true := by
  decide +kernel
theorem H1231_fin : (prmOK pH1231 1231 && ptTest pH1231 (runFrom pH1231 (fmask pH1231) (cmask pH1231) (hmask pH1231) 870 361 (true, H1231_cp1.1, H1231_cp1.2)) 1231 616 true) = true := by
  decide +kernel
theorem H1231_ok : RunOK pH1231 1231 (runFrom pH1231 (fmask pH1231) (cmask pH1231) (hmask pH1231) 870 361 (true, H1231_cp1.1, H1231_cp1.2)) ∧ ptTest pH1231 (runFrom pH1231 (fmask pH1231) (cmask pH1231) (hmask pH1231) 870 361 (true, H1231_cp1.1, H1231_cp1.2)) 1231 616 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1231_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1231_fin) true) H1231_seg1) (by decide) rfl H1231_fin ptTest_fst
theorem I1231_fin : (prmOK pI1231 1231 && intTest pI1231 (runFrom pI1231 (fmask pI1231) (cmask pI1231) (hmask pI1231) 1 1230 (true, (init pI1231), (init pI1231))) 1231 19 false) = true := by
  decide +kernel
theorem I1231_ok : RunOK pI1231 1231 (runFrom pI1231 (fmask pI1231) (cmask pI1231) (hmask pI1231) 1 1230 (true, (init pI1231), (init pI1231))) ∧ intTest pI1231 (runFrom pI1231 (fmask pI1231) (cmask pI1231) (hmask pI1231) 1 1230 (true, (init pI1231), (init pI1231))) 1231 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1231_fin) true) (by decide) rfl I1231_fin intTest_fst
theorem link1231 : linkOK pL1231 pH1231 pI1231 = true := by decide +kernel
theorem cvx1231 : ConvexBetweenHumps 1231 :=
  cvx_of L1231_ok H1231_ok I1231_ok link1231 (by decide)

/-! ### `N = 1232` -/

def pL1232 : Prm := ⟨76, 35, 38, 1234, 11, 18446744073709551616, 145951608229599026, 145951608229599026⟩
def pH1232 : Prm := ⟨76, 35, 38, 1234, 11, 18446744073709551616, 145953807252854578, 145953807252854578⟩
def pI1232 : Prm := ⟨65, 33, 29, 1234, 11, 18446744073709551616, 145951608229599026, 145953807252854578⟩
noncomputable def L1232_cp1 : Nat × Nat := t7val% (fastRun pL1232 1 870 (init pL1232) (init pL1232))
theorem L1232_seg1 : segOK pL1232 1 870 (init pL1232) (init pL1232) L1232_cp1.1 L1232_cp1.2 = true := by
  decide +kernel
theorem L1232_fin : (prmOK pL1232 1232 && ptTest pL1232 (runFrom pL1232 (fmask pL1232) (cmask pL1232) (hmask pL1232) 871 361 (true, L1232_cp1.1, L1232_cp1.2)) 1232 616 false) = true := by
  decide +kernel
theorem L1232_ok : RunOK pL1232 1232 (runFrom pL1232 (fmask pL1232) (cmask pL1232) (hmask pL1232) 871 361 (true, L1232_cp1.1, L1232_cp1.2)) ∧ ptTest pL1232 (runFrom pL1232 (fmask pL1232) (cmask pL1232) (hmask pL1232) 871 361 (true, L1232_cp1.1, L1232_cp1.2)) 1232 616 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1232_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1232_fin) true) L1232_seg1) (by decide) rfl L1232_fin ptTest_fst
noncomputable def H1232_cp1 : Nat × Nat := t7val% (fastRun pH1232 1 870 (init pH1232) (init pH1232))
theorem H1232_seg1 : segOK pH1232 1 870 (init pH1232) (init pH1232) H1232_cp1.1 H1232_cp1.2 = true := by
  decide +kernel
theorem H1232_fin : (prmOK pH1232 1232 && ptTest pH1232 (runFrom pH1232 (fmask pH1232) (cmask pH1232) (hmask pH1232) 871 361 (true, H1232_cp1.1, H1232_cp1.2)) 1232 616 true) = true := by
  decide +kernel
theorem H1232_ok : RunOK pH1232 1232 (runFrom pH1232 (fmask pH1232) (cmask pH1232) (hmask pH1232) 871 361 (true, H1232_cp1.1, H1232_cp1.2)) ∧ ptTest pH1232 (runFrom pH1232 (fmask pH1232) (cmask pH1232) (hmask pH1232) 871 361 (true, H1232_cp1.1, H1232_cp1.2)) 1232 616 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1232_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1232_fin) true) H1232_seg1) (by decide) rfl H1232_fin ptTest_fst
theorem I1232_fin : (prmOK pI1232 1232 && intTest pI1232 (runFrom pI1232 (fmask pI1232) (cmask pI1232) (hmask pI1232) 1 1231 (true, (init pI1232), (init pI1232))) 1232 19 true) = true := by
  decide +kernel
theorem I1232_ok : RunOK pI1232 1232 (runFrom pI1232 (fmask pI1232) (cmask pI1232) (hmask pI1232) 1 1231 (true, (init pI1232), (init pI1232))) ∧ intTest pI1232 (runFrom pI1232 (fmask pI1232) (cmask pI1232) (hmask pI1232) 1 1231 (true, (init pI1232), (init pI1232))) 1232 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1232_fin) true) (by decide) rfl I1232_fin intTest_fst
theorem link1232 : linkOK pL1232 pH1232 pI1232 = true := by decide +kernel
theorem cvx1232 : ConvexBetweenHumps 1232 :=
  cvx_of L1232_ok H1232_ok I1232_ok link1232 (by decide)
theorem cenlink1232 : cenLinkOK pI1232 1232 = true := by decide +kernel
theorem cen1232 : CenterUniqueMin 1232 ∧ DipHyp 1232 ∧ OnePointHyps 1232 :=
  cen_of L1232_ok H1232_ok I1232_ok link1232 cenlink1232

/-! ### `N = 1233` -/

def pL1233 : Prm := ⟨76, 35, 38, 1235, 11, 18446744073709551616, 145856097562669990, 145856097562669990⟩
def pH1233 : Prm := ⟨76, 35, 38, 1235, 11, 18446744073709551616, 145858296585925542, 145858296585925542⟩
def pI1233 : Prm := ⟨66, 33, 30, 1235, 11, 18446744073709551616, 145856097562669990, 145858296585925542⟩
noncomputable def L1233_cp1 : Nat × Nat := t7val% (fastRun pL1233 1 871 (init pL1233) (init pL1233))
theorem L1233_seg1 : segOK pL1233 1 871 (init pL1233) (init pL1233) L1233_cp1.1 L1233_cp1.2 = true := by
  decide +kernel
theorem L1233_fin : (prmOK pL1233 1233 && ptTest pL1233 (runFrom pL1233 (fmask pL1233) (cmask pL1233) (hmask pL1233) 872 361 (true, L1233_cp1.1, L1233_cp1.2)) 1233 617 false) = true := by
  decide +kernel
theorem L1233_ok : RunOK pL1233 1233 (runFrom pL1233 (fmask pL1233) (cmask pL1233) (hmask pL1233) 872 361 (true, L1233_cp1.1, L1233_cp1.2)) ∧ ptTest pL1233 (runFrom pL1233 (fmask pL1233) (cmask pL1233) (hmask pL1233) 872 361 (true, L1233_cp1.1, L1233_cp1.2)) 1233 617 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1233_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1233_fin) true) L1233_seg1) (by decide) rfl L1233_fin ptTest_fst
noncomputable def H1233_cp1 : Nat × Nat := t7val% (fastRun pH1233 1 871 (init pH1233) (init pH1233))
theorem H1233_seg1 : segOK pH1233 1 871 (init pH1233) (init pH1233) H1233_cp1.1 H1233_cp1.2 = true := by
  decide +kernel
theorem H1233_fin : (prmOK pH1233 1233 && ptTest pH1233 (runFrom pH1233 (fmask pH1233) (cmask pH1233) (hmask pH1233) 872 361 (true, H1233_cp1.1, H1233_cp1.2)) 1233 617 true) = true := by
  decide +kernel
theorem H1233_ok : RunOK pH1233 1233 (runFrom pH1233 (fmask pH1233) (cmask pH1233) (hmask pH1233) 872 361 (true, H1233_cp1.1, H1233_cp1.2)) ∧ ptTest pH1233 (runFrom pH1233 (fmask pH1233) (cmask pH1233) (hmask pH1233) 872 361 (true, H1233_cp1.1, H1233_cp1.2)) 1233 617 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1233_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1233_fin) true) H1233_seg1) (by decide) rfl H1233_fin ptTest_fst
theorem I1233_fin : (prmOK pI1233 1233 && intTest pI1233 (runFrom pI1233 (fmask pI1233) (cmask pI1233) (hmask pI1233) 1 1232 (true, (init pI1233), (init pI1233))) 1233 19 false) = true := by
  decide +kernel
theorem I1233_ok : RunOK pI1233 1233 (runFrom pI1233 (fmask pI1233) (cmask pI1233) (hmask pI1233) 1 1232 (true, (init pI1233), (init pI1233))) ∧ intTest pI1233 (runFrom pI1233 (fmask pI1233) (cmask pI1233) (hmask pI1233) 1 1232 (true, (init pI1233), (init pI1233))) 1233 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1233_fin) true) (by decide) rfl I1233_fin intTest_fst
theorem link1233 : linkOK pL1233 pH1233 pI1233 = true := by decide +kernel
theorem cvx1233 : ConvexBetweenHumps 1233 :=
  cvx_of L1233_ok H1233_ok I1233_ok link1233 (by decide)

/-! ### `N = 1234` -/

def pL1234 : Prm := ⟨76, 35, 38, 1236, 11, 18446744073709551616, 145760784074999054, 145760784074999054⟩
def pH1234 : Prm := ⟨76, 35, 38, 1236, 11, 18446744073709551616, 145762983098254606, 145762983098254606⟩
def pI1234 : Prm := ⟨66, 33, 30, 1236, 11, 18446744073709551616, 145760784074999054, 145762983098254606⟩
noncomputable def L1234_cp1 : Nat × Nat := t7val% (fastRun pL1234 1 872 (init pL1234) (init pL1234))
theorem L1234_seg1 : segOK pL1234 1 872 (init pL1234) (init pL1234) L1234_cp1.1 L1234_cp1.2 = true := by
  decide +kernel
theorem L1234_fin : (prmOK pL1234 1234 && ptTest pL1234 (runFrom pL1234 (fmask pL1234) (cmask pL1234) (hmask pL1234) 873 361 (true, L1234_cp1.1, L1234_cp1.2)) 1234 617 false) = true := by
  decide +kernel
theorem L1234_ok : RunOK pL1234 1234 (runFrom pL1234 (fmask pL1234) (cmask pL1234) (hmask pL1234) 873 361 (true, L1234_cp1.1, L1234_cp1.2)) ∧ ptTest pL1234 (runFrom pL1234 (fmask pL1234) (cmask pL1234) (hmask pL1234) 873 361 (true, L1234_cp1.1, L1234_cp1.2)) 1234 617 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1234_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1234_fin) true) L1234_seg1) (by decide) rfl L1234_fin ptTest_fst
noncomputable def H1234_cp1 : Nat × Nat := t7val% (fastRun pH1234 1 872 (init pH1234) (init pH1234))
theorem H1234_seg1 : segOK pH1234 1 872 (init pH1234) (init pH1234) H1234_cp1.1 H1234_cp1.2 = true := by
  decide +kernel
theorem H1234_fin : (prmOK pH1234 1234 && ptTest pH1234 (runFrom pH1234 (fmask pH1234) (cmask pH1234) (hmask pH1234) 873 361 (true, H1234_cp1.1, H1234_cp1.2)) 1234 617 true) = true := by
  decide +kernel
theorem H1234_ok : RunOK pH1234 1234 (runFrom pH1234 (fmask pH1234) (cmask pH1234) (hmask pH1234) 873 361 (true, H1234_cp1.1, H1234_cp1.2)) ∧ ptTest pH1234 (runFrom pH1234 (fmask pH1234) (cmask pH1234) (hmask pH1234) 873 361 (true, H1234_cp1.1, H1234_cp1.2)) 1234 617 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1234_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1234_fin) true) H1234_seg1) (by decide) rfl H1234_fin ptTest_fst
theorem I1234_fin : (prmOK pI1234 1234 && intTest pI1234 (runFrom pI1234 (fmask pI1234) (cmask pI1234) (hmask pI1234) 1 1233 (true, (init pI1234), (init pI1234))) 1234 19 true) = true := by
  decide +kernel
theorem I1234_ok : RunOK pI1234 1234 (runFrom pI1234 (fmask pI1234) (cmask pI1234) (hmask pI1234) 1 1233 (true, (init pI1234), (init pI1234))) ∧ intTest pI1234 (runFrom pI1234 (fmask pI1234) (cmask pI1234) (hmask pI1234) 1 1233 (true, (init pI1234), (init pI1234))) 1234 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1234_fin) true) (by decide) rfl I1234_fin intTest_fst
theorem link1234 : linkOK pL1234 pH1234 pI1234 = true := by decide +kernel
theorem cvx1234 : ConvexBetweenHumps 1234 :=
  cvx_of L1234_ok H1234_ok I1234_ok link1234 (by decide)
theorem cenlink1234 : cenLinkOK pI1234 1234 = true := by decide +kernel
theorem cen1234 : CenterUniqueMin 1234 ∧ DipHyp 1234 ∧ OnePointHyps 1234 :=
  cen_of L1234_ok H1234_ok I1234_ok link1234 cenlink1234

/-! ### `N = 1235` -/

def pL1235 : Prm := ⟨76, 35, 38, 1237, 11, 18446744073709551616, 145665545646152076, 145665545646152076⟩
def pH1235 : Prm := ⟨76, 35, 38, 1237, 11, 18446744073709551616, 145667744669407628, 145667744669407628⟩
def pI1235 : Prm := ⟨65, 33, 29, 1237, 11, 18446744073709551616, 145665545646152076, 145667744669407628⟩
noncomputable def L1235_cp1 : Nat × Nat := t7val% (fastRun pL1235 1 872 (init pL1235) (init pL1235))
theorem L1235_seg1 : segOK pL1235 1 872 (init pL1235) (init pL1235) L1235_cp1.1 L1235_cp1.2 = true := by
  decide +kernel
theorem L1235_fin : (prmOK pL1235 1235 && ptTest pL1235 (runFrom pL1235 (fmask pL1235) (cmask pL1235) (hmask pL1235) 873 362 (true, L1235_cp1.1, L1235_cp1.2)) 1235 618 false) = true := by
  decide +kernel
theorem L1235_ok : RunOK pL1235 1235 (runFrom pL1235 (fmask pL1235) (cmask pL1235) (hmask pL1235) 873 362 (true, L1235_cp1.1, L1235_cp1.2)) ∧ ptTest pL1235 (runFrom pL1235 (fmask pL1235) (cmask pL1235) (hmask pL1235) 873 362 (true, L1235_cp1.1, L1235_cp1.2)) 1235 618 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1235_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1235_fin) true) L1235_seg1) (by decide) rfl L1235_fin ptTest_fst
noncomputable def H1235_cp1 : Nat × Nat := t7val% (fastRun pH1235 1 872 (init pH1235) (init pH1235))
theorem H1235_seg1 : segOK pH1235 1 872 (init pH1235) (init pH1235) H1235_cp1.1 H1235_cp1.2 = true := by
  decide +kernel
theorem H1235_fin : (prmOK pH1235 1235 && ptTest pH1235 (runFrom pH1235 (fmask pH1235) (cmask pH1235) (hmask pH1235) 873 362 (true, H1235_cp1.1, H1235_cp1.2)) 1235 618 true) = true := by
  decide +kernel
theorem H1235_ok : RunOK pH1235 1235 (runFrom pH1235 (fmask pH1235) (cmask pH1235) (hmask pH1235) 873 362 (true, H1235_cp1.1, H1235_cp1.2)) ∧ ptTest pH1235 (runFrom pH1235 (fmask pH1235) (cmask pH1235) (hmask pH1235) 873 362 (true, H1235_cp1.1, H1235_cp1.2)) 1235 618 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1235_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1235_fin) true) H1235_seg1) (by decide) rfl H1235_fin ptTest_fst
theorem I1235_fin : (prmOK pI1235 1235 && intTest pI1235 (runFrom pI1235 (fmask pI1235) (cmask pI1235) (hmask pI1235) 1 1234 (true, (init pI1235), (init pI1235))) 1235 19 false) = true := by
  decide +kernel
theorem I1235_ok : RunOK pI1235 1235 (runFrom pI1235 (fmask pI1235) (cmask pI1235) (hmask pI1235) 1 1234 (true, (init pI1235), (init pI1235))) ∧ intTest pI1235 (runFrom pI1235 (fmask pI1235) (cmask pI1235) (hmask pI1235) 1 1234 (true, (init pI1235), (init pI1235))) 1235 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1235_fin) true) (by decide) rfl I1235_fin intTest_fst
theorem link1235 : linkOK pL1235 pH1235 pI1235 = true := by decide +kernel
theorem cvx1235 : ConvexBetweenHumps 1235 :=
  cvx_of L1235_ok H1235_ok I1235_ok link1235 (by decide)

/-! ### `N = 1236` -/

def pL1236 : Prm := ⟨76, 35, 38, 1238, 11, 18446744073709551616, 145570503494904792, 145570503494904792⟩
def pH1236 : Prm := ⟨76, 35, 38, 1238, 11, 18446744073709551616, 145572702518160344, 145572702518160344⟩
def pI1236 : Prm := ⟨66, 33, 30, 1238, 11, 18446744073709551616, 145570503494904792, 145572702518160344⟩
noncomputable def L1236_cp1 : Nat × Nat := t7val% (fastRun pL1236 1 873 (init pL1236) (init pL1236))
theorem L1236_seg1 : segOK pL1236 1 873 (init pL1236) (init pL1236) L1236_cp1.1 L1236_cp1.2 = true := by
  decide +kernel
theorem L1236_fin : (prmOK pL1236 1236 && ptTest pL1236 (runFrom pL1236 (fmask pL1236) (cmask pL1236) (hmask pL1236) 874 362 (true, L1236_cp1.1, L1236_cp1.2)) 1236 618 false) = true := by
  decide +kernel
theorem L1236_ok : RunOK pL1236 1236 (runFrom pL1236 (fmask pL1236) (cmask pL1236) (hmask pL1236) 874 362 (true, L1236_cp1.1, L1236_cp1.2)) ∧ ptTest pL1236 (runFrom pL1236 (fmask pL1236) (cmask pL1236) (hmask pL1236) 874 362 (true, L1236_cp1.1, L1236_cp1.2)) 1236 618 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1236_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1236_fin) true) L1236_seg1) (by decide) rfl L1236_fin ptTest_fst
noncomputable def H1236_cp1 : Nat × Nat := t7val% (fastRun pH1236 1 873 (init pH1236) (init pH1236))
theorem H1236_seg1 : segOK pH1236 1 873 (init pH1236) (init pH1236) H1236_cp1.1 H1236_cp1.2 = true := by
  decide +kernel
theorem H1236_fin : (prmOK pH1236 1236 && ptTest pH1236 (runFrom pH1236 (fmask pH1236) (cmask pH1236) (hmask pH1236) 874 362 (true, H1236_cp1.1, H1236_cp1.2)) 1236 618 true) = true := by
  decide +kernel
theorem H1236_ok : RunOK pH1236 1236 (runFrom pH1236 (fmask pH1236) (cmask pH1236) (hmask pH1236) 874 362 (true, H1236_cp1.1, H1236_cp1.2)) ∧ ptTest pH1236 (runFrom pH1236 (fmask pH1236) (cmask pH1236) (hmask pH1236) 874 362 (true, H1236_cp1.1, H1236_cp1.2)) 1236 618 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1236_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1236_fin) true) H1236_seg1) (by decide) rfl H1236_fin ptTest_fst
theorem I1236_fin : (prmOK pI1236 1236 && intTest pI1236 (runFrom pI1236 (fmask pI1236) (cmask pI1236) (hmask pI1236) 1 1235 (true, (init pI1236), (init pI1236))) 1236 19 true) = true := by
  decide +kernel
theorem I1236_ok : RunOK pI1236 1236 (runFrom pI1236 (fmask pI1236) (cmask pI1236) (hmask pI1236) 1 1235 (true, (init pI1236), (init pI1236))) ∧ intTest pI1236 (runFrom pI1236 (fmask pI1236) (cmask pI1236) (hmask pI1236) 1 1235 (true, (init pI1236), (init pI1236))) 1236 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1236_fin) true) (by decide) rfl I1236_fin intTest_fst
theorem link1236 : linkOK pL1236 pH1236 pI1236 = true := by decide +kernel
theorem cvx1236 : ConvexBetweenHumps 1236 :=
  cvx_of L1236_ok H1236_ok I1236_ok link1236 (by decide)
theorem cenlink1236 : cenLinkOK pI1236 1236 = true := by decide +kernel
theorem cen1236 : CenterUniqueMin 1236 ∧ DipHyp 1236 ∧ OnePointHyps 1236 :=
  cen_of L1236_ok H1236_ok I1236_ok link1236 cenlink1236

/-! ### `N = 1237` -/

def pL1237 : Prm := ⟨76, 35, 38, 1239, 11, 18446744073709551616, 145475536103385960, 145475536103385960⟩
def pH1237 : Prm := ⟨76, 35, 38, 1239, 11, 18446744073709551616, 145477735126641512, 145477735126641512⟩
def pI1237 : Prm := ⟨66, 33, 30, 1239, 11, 18446744073709551616, 145475536103385960, 145477735126641512⟩
noncomputable def L1237_cp1 : Nat × Nat := t7val% (fastRun pL1237 1 874 (init pL1237) (init pL1237))
theorem L1237_seg1 : segOK pL1237 1 874 (init pL1237) (init pL1237) L1237_cp1.1 L1237_cp1.2 = true := by
  decide +kernel
theorem L1237_fin : (prmOK pL1237 1237 && ptTest pL1237 (runFrom pL1237 (fmask pL1237) (cmask pL1237) (hmask pL1237) 875 362 (true, L1237_cp1.1, L1237_cp1.2)) 1237 619 false) = true := by
  decide +kernel
theorem L1237_ok : RunOK pL1237 1237 (runFrom pL1237 (fmask pL1237) (cmask pL1237) (hmask pL1237) 875 362 (true, L1237_cp1.1, L1237_cp1.2)) ∧ ptTest pL1237 (runFrom pL1237 (fmask pL1237) (cmask pL1237) (hmask pL1237) 875 362 (true, L1237_cp1.1, L1237_cp1.2)) 1237 619 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1237_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1237_fin) true) L1237_seg1) (by decide) rfl L1237_fin ptTest_fst
noncomputable def H1237_cp1 : Nat × Nat := t7val% (fastRun pH1237 1 874 (init pH1237) (init pH1237))
theorem H1237_seg1 : segOK pH1237 1 874 (init pH1237) (init pH1237) H1237_cp1.1 H1237_cp1.2 = true := by
  decide +kernel
theorem H1237_fin : (prmOK pH1237 1237 && ptTest pH1237 (runFrom pH1237 (fmask pH1237) (cmask pH1237) (hmask pH1237) 875 362 (true, H1237_cp1.1, H1237_cp1.2)) 1237 619 true) = true := by
  decide +kernel
theorem H1237_ok : RunOK pH1237 1237 (runFrom pH1237 (fmask pH1237) (cmask pH1237) (hmask pH1237) 875 362 (true, H1237_cp1.1, H1237_cp1.2)) ∧ ptTest pH1237 (runFrom pH1237 (fmask pH1237) (cmask pH1237) (hmask pH1237) 875 362 (true, H1237_cp1.1, H1237_cp1.2)) 1237 619 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1237_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1237_fin) true) H1237_seg1) (by decide) rfl H1237_fin ptTest_fst
theorem I1237_fin : (prmOK pI1237 1237 && intTest pI1237 (runFrom pI1237 (fmask pI1237) (cmask pI1237) (hmask pI1237) 1 1236 (true, (init pI1237), (init pI1237))) 1237 19 false) = true := by
  decide +kernel
theorem I1237_ok : RunOK pI1237 1237 (runFrom pI1237 (fmask pI1237) (cmask pI1237) (hmask pI1237) 1 1236 (true, (init pI1237), (init pI1237))) ∧ intTest pI1237 (runFrom pI1237 (fmask pI1237) (cmask pI1237) (hmask pI1237) 1 1236 (true, (init pI1237), (init pI1237))) 1237 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1237_fin) true) (by decide) rfl I1237_fin intTest_fst
theorem link1237 : linkOK pL1237 pH1237 pI1237 = true := by decide +kernel
theorem cvx1237 : ConvexBetweenHumps 1237 :=
  cvx_of L1237_ok H1237_ok I1237_ok link1237 (by decide)

/-! ### `N = 1238` -/

def pL1238 : Prm := ⟨76, 35, 38, 1240, 11, 18446744073709551616, 145380764093342442, 145380764093342442⟩
def pH1238 : Prm := ⟨77, 36, 38, 1240, 11, 18446744073709551616, 145382963116597994, 145382963116597994⟩
def pI1238 : Prm := ⟨66, 33, 30, 1240, 11, 18446744073709551616, 145380764093342442, 145382963116597994⟩
noncomputable def L1238_cp1 : Nat × Nat := t7val% (fastRun pL1238 1 874 (init pL1238) (init pL1238))
theorem L1238_seg1 : segOK pL1238 1 874 (init pL1238) (init pL1238) L1238_cp1.1 L1238_cp1.2 = true := by
  decide +kernel
theorem L1238_fin : (prmOK pL1238 1238 && ptTest pL1238 (runFrom pL1238 (fmask pL1238) (cmask pL1238) (hmask pL1238) 875 363 (true, L1238_cp1.1, L1238_cp1.2)) 1238 619 false) = true := by
  decide +kernel
theorem L1238_ok : RunOK pL1238 1238 (runFrom pL1238 (fmask pL1238) (cmask pL1238) (hmask pL1238) 875 363 (true, L1238_cp1.1, L1238_cp1.2)) ∧ ptTest pL1238 (runFrom pL1238 (fmask pL1238) (cmask pL1238) (hmask pL1238) 875 363 (true, L1238_cp1.1, L1238_cp1.2)) 1238 619 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1238_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1238_fin) true) L1238_seg1) (by decide) rfl L1238_fin ptTest_fst
noncomputable def H1238_cp1 : Nat × Nat := t7val% (fastRun pH1238 1 874 (init pH1238) (init pH1238))
theorem H1238_seg1 : segOK pH1238 1 874 (init pH1238) (init pH1238) H1238_cp1.1 H1238_cp1.2 = true := by
  decide +kernel
theorem H1238_fin : (prmOK pH1238 1238 && ptTest pH1238 (runFrom pH1238 (fmask pH1238) (cmask pH1238) (hmask pH1238) 875 363 (true, H1238_cp1.1, H1238_cp1.2)) 1238 619 true) = true := by
  decide +kernel
theorem H1238_ok : RunOK pH1238 1238 (runFrom pH1238 (fmask pH1238) (cmask pH1238) (hmask pH1238) 875 363 (true, H1238_cp1.1, H1238_cp1.2)) ∧ ptTest pH1238 (runFrom pH1238 (fmask pH1238) (cmask pH1238) (hmask pH1238) 875 363 (true, H1238_cp1.1, H1238_cp1.2)) 1238 619 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1238_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1238_fin) true) H1238_seg1) (by decide) rfl H1238_fin ptTest_fst
theorem I1238_fin : (prmOK pI1238 1238 && intTest pI1238 (runFrom pI1238 (fmask pI1238) (cmask pI1238) (hmask pI1238) 1 1237 (true, (init pI1238), (init pI1238))) 1238 19 true) = true := by
  decide +kernel
theorem I1238_ok : RunOK pI1238 1238 (runFrom pI1238 (fmask pI1238) (cmask pI1238) (hmask pI1238) 1 1237 (true, (init pI1238), (init pI1238))) ∧ intTest pI1238 (runFrom pI1238 (fmask pI1238) (cmask pI1238) (hmask pI1238) 1 1237 (true, (init pI1238), (init pI1238))) 1238 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1238_fin) true) (by decide) rfl I1238_fin intTest_fst
theorem link1238 : linkOK pL1238 pH1238 pI1238 = true := by decide +kernel
theorem cvx1238 : ConvexBetweenHumps 1238 :=
  cvx_of L1238_ok H1238_ok I1238_ok link1238 (by decide)
theorem cenlink1238 : cenLinkOK pI1238 1238 = true := by decide +kernel
theorem cen1238 : CenterUniqueMin 1238 ∧ DipHyp 1238 ∧ OnePointHyps 1238 :=
  cen_of L1238_ok H1238_ok I1238_ok link1238 cenlink1238

/-! ### `N = 1239` -/

def pL1239 : Prm := ⟨76, 35, 38, 1241, 11, 18446744073709551616, 145286066545555179, 145286066545555179⟩
def pH1239 : Prm := ⟨76, 35, 38, 1241, 11, 18446744073709551616, 145288265568810731, 145288265568810731⟩
def pI1239 : Prm := ⟨66, 33, 30, 1241, 11, 18446744073709551616, 145286066545555179, 145288265568810731⟩
noncomputable def L1239_cp1 : Nat × Nat := t7val% (fastRun pL1239 1 875 (init pL1239) (init pL1239))
theorem L1239_seg1 : segOK pL1239 1 875 (init pL1239) (init pL1239) L1239_cp1.1 L1239_cp1.2 = true := by
  decide +kernel
theorem L1239_fin : (prmOK pL1239 1239 && ptTest pL1239 (runFrom pL1239 (fmask pL1239) (cmask pL1239) (hmask pL1239) 876 363 (true, L1239_cp1.1, L1239_cp1.2)) 1239 620 false) = true := by
  decide +kernel
theorem L1239_ok : RunOK pL1239 1239 (runFrom pL1239 (fmask pL1239) (cmask pL1239) (hmask pL1239) 876 363 (true, L1239_cp1.1, L1239_cp1.2)) ∧ ptTest pL1239 (runFrom pL1239 (fmask pL1239) (cmask pL1239) (hmask pL1239) 876 363 (true, L1239_cp1.1, L1239_cp1.2)) 1239 620 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1239_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1239_fin) true) L1239_seg1) (by decide) rfl L1239_fin ptTest_fst
noncomputable def H1239_cp1 : Nat × Nat := t7val% (fastRun pH1239 1 875 (init pH1239) (init pH1239))
theorem H1239_seg1 : segOK pH1239 1 875 (init pH1239) (init pH1239) H1239_cp1.1 H1239_cp1.2 = true := by
  decide +kernel
theorem H1239_fin : (prmOK pH1239 1239 && ptTest pH1239 (runFrom pH1239 (fmask pH1239) (cmask pH1239) (hmask pH1239) 876 363 (true, H1239_cp1.1, H1239_cp1.2)) 1239 620 true) = true := by
  decide +kernel
theorem H1239_ok : RunOK pH1239 1239 (runFrom pH1239 (fmask pH1239) (cmask pH1239) (hmask pH1239) 876 363 (true, H1239_cp1.1, H1239_cp1.2)) ∧ ptTest pH1239 (runFrom pH1239 (fmask pH1239) (cmask pH1239) (hmask pH1239) 876 363 (true, H1239_cp1.1, H1239_cp1.2)) 1239 620 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1239_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1239_fin) true) H1239_seg1) (by decide) rfl H1239_fin ptTest_fst
theorem I1239_fin : (prmOK pI1239 1239 && intTest pI1239 (runFrom pI1239 (fmask pI1239) (cmask pI1239) (hmask pI1239) 1 1238 (true, (init pI1239), (init pI1239))) 1239 19 false) = true := by
  decide +kernel
theorem I1239_ok : RunOK pI1239 1239 (runFrom pI1239 (fmask pI1239) (cmask pI1239) (hmask pI1239) 1 1238 (true, (init pI1239), (init pI1239))) ∧ intTest pI1239 (runFrom pI1239 (fmask pI1239) (cmask pI1239) (hmask pI1239) 1 1238 (true, (init pI1239), (init pI1239))) 1239 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1239_fin) true) (by decide) rfl I1239_fin intTest_fst
theorem link1239 : linkOK pL1239 pH1239 pI1239 = true := by decide +kernel
theorem cvx1239 : ConvexBetweenHumps 1239 :=
  cvx_of L1239_ok H1239_ok I1239_ok link1239 (by decide)

/-! ### The range -/

theorem cvx_1212_1239 {N : ℕ} (h1 : 1212 ≤ N) (h2 : N ≤ 1239) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1225
  · by_cases h4 : N ≤ 1218
    · by_cases h6 : N ≤ 1214
      · by_cases h8 : N ≤ 1212
        · obtain rfl : N = 1212 := by omega
          exact cvx1212
        · by_cases h10 : N ≤ 1213
          · obtain rfl : N = 1213 := by omega
            exact cvx1213
          · obtain rfl : N = 1214 := by omega
            exact cvx1214
      · by_cases h8 : N ≤ 1216
        · by_cases h10 : N ≤ 1215
          · obtain rfl : N = 1215 := by omega
            exact cvx1215
          · obtain rfl : N = 1216 := by omega
            exact cvx1216
        · by_cases h10 : N ≤ 1217
          · obtain rfl : N = 1217 := by omega
            exact cvx1217
          · obtain rfl : N = 1218 := by omega
            exact cvx1218
    · by_cases h6 : N ≤ 1221
      · by_cases h8 : N ≤ 1219
        · obtain rfl : N = 1219 := by omega
          exact cvx1219
        · by_cases h10 : N ≤ 1220
          · obtain rfl : N = 1220 := by omega
            exact cvx1220
          · obtain rfl : N = 1221 := by omega
            exact cvx1221
      · by_cases h8 : N ≤ 1223
        · by_cases h10 : N ≤ 1222
          · obtain rfl : N = 1222 := by omega
            exact cvx1222
          · obtain rfl : N = 1223 := by omega
            exact cvx1223
        · by_cases h10 : N ≤ 1224
          · obtain rfl : N = 1224 := by omega
            exact cvx1224
          · obtain rfl : N = 1225 := by omega
            exact cvx1225
  · by_cases h4 : N ≤ 1232
    · by_cases h6 : N ≤ 1228
      · by_cases h8 : N ≤ 1226
        · obtain rfl : N = 1226 := by omega
          exact cvx1226
        · by_cases h10 : N ≤ 1227
          · obtain rfl : N = 1227 := by omega
            exact cvx1227
          · obtain rfl : N = 1228 := by omega
            exact cvx1228
      · by_cases h8 : N ≤ 1230
        · by_cases h10 : N ≤ 1229
          · obtain rfl : N = 1229 := by omega
            exact cvx1229
          · obtain rfl : N = 1230 := by omega
            exact cvx1230
        · by_cases h10 : N ≤ 1231
          · obtain rfl : N = 1231 := by omega
            exact cvx1231
          · obtain rfl : N = 1232 := by omega
            exact cvx1232
    · by_cases h6 : N ≤ 1235
      · by_cases h8 : N ≤ 1233
        · obtain rfl : N = 1233 := by omega
          exact cvx1233
        · by_cases h10 : N ≤ 1234
          · obtain rfl : N = 1234 := by omega
            exact cvx1234
          · obtain rfl : N = 1235 := by omega
            exact cvx1235
      · by_cases h8 : N ≤ 1237
        · by_cases h10 : N ≤ 1236
          · obtain rfl : N = 1236 := by omega
            exact cvx1236
          · obtain rfl : N = 1237 := by omega
            exact cvx1237
        · by_cases h10 : N ≤ 1238
          · obtain rfl : N = 1238 := by omega
            exact cvx1238
          · obtain rfl : N = 1239 := by omega
            exact cvx1239

theorem cen_1212_1239 {N : ℕ} (h1 : 1212 ≤ N) (h2 : N ≤ 1239) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1224
  · by_cases h4 : N ≤ 1216
    · by_cases h6 : N ≤ 1212
      · obtain rfl : N = 1212 := by omega
        exact cen1212
      · by_cases h8 : N ≤ 1214
        · obtain rfl : N = 1214 := by omega
          exact cen1214
        · obtain rfl : N = 1216 := by omega
          exact cen1216
    · by_cases h6 : N ≤ 1220
      · by_cases h8 : N ≤ 1218
        · obtain rfl : N = 1218 := by omega
          exact cen1218
        · obtain rfl : N = 1220 := by omega
          exact cen1220
      · by_cases h8 : N ≤ 1222
        · obtain rfl : N = 1222 := by omega
          exact cen1222
        · obtain rfl : N = 1224 := by omega
          exact cen1224
  · by_cases h4 : N ≤ 1230
    · by_cases h6 : N ≤ 1226
      · obtain rfl : N = 1226 := by omega
        exact cen1226
      · by_cases h8 : N ≤ 1228
        · obtain rfl : N = 1228 := by omega
          exact cen1228
        · obtain rfl : N = 1230 := by omega
          exact cen1230
    · by_cases h6 : N ≤ 1234
      · by_cases h8 : N ≤ 1232
        · obtain rfl : N = 1232 := by omega
          exact cen1232
        · obtain rfl : N = 1234 := by omega
          exact cen1234
      · by_cases h8 : N ≤ 1236
        · obtain rfl : N = 1236 := by omega
          exact cen1236
        · obtain rfl : N = 1238 := by omega
          exact cen1238

end Kagey131.PaperD.T7
