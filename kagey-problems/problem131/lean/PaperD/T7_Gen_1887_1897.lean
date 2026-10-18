import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1887, …, 1897` (generated)

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

/-! ### `N = 1887` -/

def pL1887 : Prm := ⟨80, 37, 40, 1889, 11, 18446744073709551616, 103148617112061213, 103148617112061213⟩
def pH1887 : Prm := ⟨80, 37, 40, 1889, 11, 18446744073709551616, 103149716623688989, 103149716623688989⟩
def pI1887 : Prm := ⟨68, 34, 31, 1889, 11, 18446744073709551616, 103148617112061213, 103149716623688989⟩
noncomputable def L1887_cp1 : Nat × Nat := t7val% (fastRun pL1887 1 1088 (init pL1887) (init pL1887))
theorem L1887_seg1 : segOK pL1887 1 1088 (init pL1887) (init pL1887) L1887_cp1.1 L1887_cp1.2 = true := by
  decide +kernel
noncomputable def L1887_cp2 : Nat × Nat := t7val% (fastRun pL1887 1 1540 (init pL1887) (init pL1887))
theorem L1887_seg2 : segOK pL1887 1089 452 L1887_cp1.1 L1887_cp1.2 L1887_cp2.1 L1887_cp2.2 = true := by
  decide +kernel
theorem L1887_fin : (prmOK pL1887 1887 && ptTest pL1887 (runFrom pL1887 (fmask pL1887) (cmask pL1887) (hmask pL1887) 1541 346 (true, L1887_cp2.1, L1887_cp2.2)) 1887 944 false) = true := by
  decide +kernel
theorem L1887_ok : RunOK pL1887 1887 (runFrom pL1887 (fmask pL1887) (cmask pL1887) (hmask pL1887) 1541 346 (true, L1887_cp2.1, L1887_cp2.2)) ∧ ptTest pL1887 (runFrom pL1887 (fmask pL1887) (cmask pL1887) (hmask pL1887) 1541 346 (true, L1887_cp2.1, L1887_cp2.2)) 1887 944 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1887_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1887_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1887_fin) true) L1887_seg1) L1887_seg2) (by decide) rfl L1887_fin ptTest_fst
noncomputable def H1887_cp1 : Nat × Nat := t7val% (fastRun pH1887 1 1088 (init pH1887) (init pH1887))
theorem H1887_seg1 : segOK pH1887 1 1088 (init pH1887) (init pH1887) H1887_cp1.1 H1887_cp1.2 = true := by
  decide +kernel
noncomputable def H1887_cp2 : Nat × Nat := t7val% (fastRun pH1887 1 1540 (init pH1887) (init pH1887))
theorem H1887_seg2 : segOK pH1887 1089 452 H1887_cp1.1 H1887_cp1.2 H1887_cp2.1 H1887_cp2.2 = true := by
  decide +kernel
theorem H1887_fin : (prmOK pH1887 1887 && ptTest pH1887 (runFrom pH1887 (fmask pH1887) (cmask pH1887) (hmask pH1887) 1541 346 (true, H1887_cp2.1, H1887_cp2.2)) 1887 944 true) = true := by
  decide +kernel
theorem H1887_ok : RunOK pH1887 1887 (runFrom pH1887 (fmask pH1887) (cmask pH1887) (hmask pH1887) 1541 346 (true, H1887_cp2.1, H1887_cp2.2)) ∧ ptTest pH1887 (runFrom pH1887 (fmask pH1887) (cmask pH1887) (hmask pH1887) 1541 346 (true, H1887_cp2.1, H1887_cp2.2)) 1887 944 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1887_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1887_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1887_fin) true) H1887_seg1) H1887_seg2) (by decide) rfl H1887_fin ptTest_fst
noncomputable def I1887_cp1 : Nat × Nat := t7val% (fastRun pI1887 1 1088 (init pI1887) (init pI1887))
theorem I1887_seg1 : segOK pI1887 1 1088 (init pI1887) (init pI1887) I1887_cp1.1 I1887_cp1.2 = true := by
  decide +kernel
noncomputable def I1887_cp2 : Nat × Nat := t7val% (fastRun pI1887 1 1540 (init pI1887) (init pI1887))
theorem I1887_seg2 : segOK pI1887 1089 452 I1887_cp1.1 I1887_cp1.2 I1887_cp2.1 I1887_cp2.2 = true := by
  decide +kernel
theorem I1887_fin : (prmOK pI1887 1887 && intTest pI1887 (runFrom pI1887 (fmask pI1887) (cmask pI1887) (hmask pI1887) 1541 346 (true, I1887_cp2.1, I1887_cp2.2)) 1887 21 false) = true := by
  decide +kernel
theorem I1887_ok : RunOK pI1887 1887 (runFrom pI1887 (fmask pI1887) (cmask pI1887) (hmask pI1887) 1541 346 (true, I1887_cp2.1, I1887_cp2.2)) ∧ intTest pI1887 (runFrom pI1887 (fmask pI1887) (cmask pI1887) (hmask pI1887) 1541 346 (true, I1887_cp2.1, I1887_cp2.2)) 1887 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1887_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1887_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1887_fin) true) I1887_seg1) I1887_seg2) (by decide) rfl I1887_fin intTest_fst
theorem link1887 : linkOK pL1887 pH1887 pI1887 = true := by decide +kernel
theorem cvx1887 : ConvexBetweenHumps 1887 :=
  cvx_of L1887_ok H1887_ok I1887_ok link1887 (by decide)

/-! ### `N = 1888` -/

def pL1888 : Prm := ⟨80, 37, 40, 1890, 11, 18446744073709551616, 103103748786490089, 103103748786490089⟩
def pH1888 : Prm := ⟨80, 37, 40, 1890, 11, 18446744073709551616, 103104848298117865, 103104848298117865⟩
def pI1888 : Prm := ⟨68, 34, 31, 1890, 11, 18446744073709551616, 103103748786490089, 103104848298117865⟩
noncomputable def L1888_cp1 : Nat × Nat := t7val% (fastRun pL1888 1 1089 (init pL1888) (init pL1888))
theorem L1888_seg1 : segOK pL1888 1 1089 (init pL1888) (init pL1888) L1888_cp1.1 L1888_cp1.2 = true := by
  decide +kernel
noncomputable def L1888_cp2 : Nat × Nat := t7val% (fastRun pL1888 1 1541 (init pL1888) (init pL1888))
theorem L1888_seg2 : segOK pL1888 1090 452 L1888_cp1.1 L1888_cp1.2 L1888_cp2.1 L1888_cp2.2 = true := by
  decide +kernel
theorem L1888_fin : (prmOK pL1888 1888 && ptTest pL1888 (runFrom pL1888 (fmask pL1888) (cmask pL1888) (hmask pL1888) 1542 346 (true, L1888_cp2.1, L1888_cp2.2)) 1888 944 false) = true := by
  decide +kernel
theorem L1888_ok : RunOK pL1888 1888 (runFrom pL1888 (fmask pL1888) (cmask pL1888) (hmask pL1888) 1542 346 (true, L1888_cp2.1, L1888_cp2.2)) ∧ ptTest pL1888 (runFrom pL1888 (fmask pL1888) (cmask pL1888) (hmask pL1888) 1542 346 (true, L1888_cp2.1, L1888_cp2.2)) 1888 944 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1888_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1888_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1888_fin) true) L1888_seg1) L1888_seg2) (by decide) rfl L1888_fin ptTest_fst
noncomputable def H1888_cp1 : Nat × Nat := t7val% (fastRun pH1888 1 1089 (init pH1888) (init pH1888))
theorem H1888_seg1 : segOK pH1888 1 1089 (init pH1888) (init pH1888) H1888_cp1.1 H1888_cp1.2 = true := by
  decide +kernel
noncomputable def H1888_cp2 : Nat × Nat := t7val% (fastRun pH1888 1 1541 (init pH1888) (init pH1888))
theorem H1888_seg2 : segOK pH1888 1090 452 H1888_cp1.1 H1888_cp1.2 H1888_cp2.1 H1888_cp2.2 = true := by
  decide +kernel
theorem H1888_fin : (prmOK pH1888 1888 && ptTest pH1888 (runFrom pH1888 (fmask pH1888) (cmask pH1888) (hmask pH1888) 1542 346 (true, H1888_cp2.1, H1888_cp2.2)) 1888 944 true) = true := by
  decide +kernel
theorem H1888_ok : RunOK pH1888 1888 (runFrom pH1888 (fmask pH1888) (cmask pH1888) (hmask pH1888) 1542 346 (true, H1888_cp2.1, H1888_cp2.2)) ∧ ptTest pH1888 (runFrom pH1888 (fmask pH1888) (cmask pH1888) (hmask pH1888) 1542 346 (true, H1888_cp2.1, H1888_cp2.2)) 1888 944 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1888_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1888_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1888_fin) true) H1888_seg1) H1888_seg2) (by decide) rfl H1888_fin ptTest_fst
noncomputable def I1888_cp1 : Nat × Nat := t7val% (fastRun pI1888 1 1089 (init pI1888) (init pI1888))
theorem I1888_seg1 : segOK pI1888 1 1089 (init pI1888) (init pI1888) I1888_cp1.1 I1888_cp1.2 = true := by
  decide +kernel
noncomputable def I1888_cp2 : Nat × Nat := t7val% (fastRun pI1888 1 1541 (init pI1888) (init pI1888))
theorem I1888_seg2 : segOK pI1888 1090 452 I1888_cp1.1 I1888_cp1.2 I1888_cp2.1 I1888_cp2.2 = true := by
  decide +kernel
theorem I1888_fin : (prmOK pI1888 1888 && intTest pI1888 (runFrom pI1888 (fmask pI1888) (cmask pI1888) (hmask pI1888) 1542 346 (true, I1888_cp2.1, I1888_cp2.2)) 1888 21 true) = true := by
  decide +kernel
theorem I1888_ok : RunOK pI1888 1888 (runFrom pI1888 (fmask pI1888) (cmask pI1888) (hmask pI1888) 1542 346 (true, I1888_cp2.1, I1888_cp2.2)) ∧ intTest pI1888 (runFrom pI1888 (fmask pI1888) (cmask pI1888) (hmask pI1888) 1542 346 (true, I1888_cp2.1, I1888_cp2.2)) 1888 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1888_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1888_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1888_fin) true) I1888_seg1) I1888_seg2) (by decide) rfl I1888_fin intTest_fst
theorem link1888 : linkOK pL1888 pH1888 pI1888 = true := by decide +kernel
theorem cvx1888 : ConvexBetweenHumps 1888 :=
  cvx_of L1888_ok H1888_ok I1888_ok link1888 (by decide)
theorem cenlink1888 : cenLinkOK pI1888 1888 = true := by decide +kernel
theorem cen1888 : CenterUniqueMin 1888 ∧ DipHyp 1888 ∧ OnePointHyps 1888 :=
  cen_of L1888_ok H1888_ok I1888_ok link1888 cenlink1888

/-! ### `N = 1889` -/

def pL1889 : Prm := ⟨80, 37, 40, 1891, 11, 18446744073709551616, 103058906162214080, 103058906162214080⟩
def pH1889 : Prm := ⟨80, 37, 40, 1891, 11, 18446744073709551616, 103060005673841856, 103060005673841856⟩
def pI1889 : Prm := ⟨68, 34, 31, 1891, 11, 18446744073709551616, 103058906162214080, 103060005673841856⟩
noncomputable def L1889_cp1 : Nat × Nat := t7val% (fastRun pL1889 1 1090 (init pL1889) (init pL1889))
theorem L1889_seg1 : segOK pL1889 1 1090 (init pL1889) (init pL1889) L1889_cp1.1 L1889_cp1.2 = true := by
  decide +kernel
noncomputable def L1889_cp2 : Nat × Nat := t7val% (fastRun pL1889 1 1541 (init pL1889) (init pL1889))
theorem L1889_seg2 : segOK pL1889 1091 451 L1889_cp1.1 L1889_cp1.2 L1889_cp2.1 L1889_cp2.2 = true := by
  decide +kernel
theorem L1889_fin : (prmOK pL1889 1889 && ptTest pL1889 (runFrom pL1889 (fmask pL1889) (cmask pL1889) (hmask pL1889) 1542 347 (true, L1889_cp2.1, L1889_cp2.2)) 1889 945 false) = true := by
  decide +kernel
theorem L1889_ok : RunOK pL1889 1889 (runFrom pL1889 (fmask pL1889) (cmask pL1889) (hmask pL1889) 1542 347 (true, L1889_cp2.1, L1889_cp2.2)) ∧ ptTest pL1889 (runFrom pL1889 (fmask pL1889) (cmask pL1889) (hmask pL1889) 1542 347 (true, L1889_cp2.1, L1889_cp2.2)) 1889 945 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1889_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1889_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1889_fin) true) L1889_seg1) L1889_seg2) (by decide) rfl L1889_fin ptTest_fst
noncomputable def H1889_cp1 : Nat × Nat := t7val% (fastRun pH1889 1 1090 (init pH1889) (init pH1889))
theorem H1889_seg1 : segOK pH1889 1 1090 (init pH1889) (init pH1889) H1889_cp1.1 H1889_cp1.2 = true := by
  decide +kernel
noncomputable def H1889_cp2 : Nat × Nat := t7val% (fastRun pH1889 1 1541 (init pH1889) (init pH1889))
theorem H1889_seg2 : segOK pH1889 1091 451 H1889_cp1.1 H1889_cp1.2 H1889_cp2.1 H1889_cp2.2 = true := by
  decide +kernel
theorem H1889_fin : (prmOK pH1889 1889 && ptTest pH1889 (runFrom pH1889 (fmask pH1889) (cmask pH1889) (hmask pH1889) 1542 347 (true, H1889_cp2.1, H1889_cp2.2)) 1889 945 true) = true := by
  decide +kernel
theorem H1889_ok : RunOK pH1889 1889 (runFrom pH1889 (fmask pH1889) (cmask pH1889) (hmask pH1889) 1542 347 (true, H1889_cp2.1, H1889_cp2.2)) ∧ ptTest pH1889 (runFrom pH1889 (fmask pH1889) (cmask pH1889) (hmask pH1889) 1542 347 (true, H1889_cp2.1, H1889_cp2.2)) 1889 945 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1889_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1889_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1889_fin) true) H1889_seg1) H1889_seg2) (by decide) rfl H1889_fin ptTest_fst
noncomputable def I1889_cp1 : Nat × Nat := t7val% (fastRun pI1889 1 1090 (init pI1889) (init pI1889))
theorem I1889_seg1 : segOK pI1889 1 1090 (init pI1889) (init pI1889) I1889_cp1.1 I1889_cp1.2 = true := by
  decide +kernel
noncomputable def I1889_cp2 : Nat × Nat := t7val% (fastRun pI1889 1 1541 (init pI1889) (init pI1889))
theorem I1889_seg2 : segOK pI1889 1091 451 I1889_cp1.1 I1889_cp1.2 I1889_cp2.1 I1889_cp2.2 = true := by
  decide +kernel
theorem I1889_fin : (prmOK pI1889 1889 && intTest pI1889 (runFrom pI1889 (fmask pI1889) (cmask pI1889) (hmask pI1889) 1542 347 (true, I1889_cp2.1, I1889_cp2.2)) 1889 21 false) = true := by
  decide +kernel
theorem I1889_ok : RunOK pI1889 1889 (runFrom pI1889 (fmask pI1889) (cmask pI1889) (hmask pI1889) 1542 347 (true, I1889_cp2.1, I1889_cp2.2)) ∧ intTest pI1889 (runFrom pI1889 (fmask pI1889) (cmask pI1889) (hmask pI1889) 1542 347 (true, I1889_cp2.1, I1889_cp2.2)) 1889 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1889_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1889_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1889_fin) true) I1889_seg1) I1889_seg2) (by decide) rfl I1889_fin intTest_fst
theorem link1889 : linkOK pL1889 pH1889 pI1889 = true := by decide +kernel
theorem cvx1889 : ConvexBetweenHumps 1889 :=
  cvx_of L1889_ok H1889_ok I1889_ok link1889 (by decide)

/-! ### `N = 1890` -/

def pL1890 : Prm := ⟨80, 37, 40, 1892, 11, 18446744073709551616, 103014122433374384, 103014122433374384⟩
def pH1890 : Prm := ⟨80, 37, 40, 1892, 11, 18446744073709551616, 103015221945002160, 103015221945002160⟩
def pI1890 : Prm := ⟨68, 34, 31, 1892, 11, 18446744073709551616, 103014122433374384, 103015221945002160⟩
noncomputable def L1890_cp1 : Nat × Nat := t7val% (fastRun pL1890 1 1090 (init pL1890) (init pL1890))
theorem L1890_seg1 : segOK pL1890 1 1090 (init pL1890) (init pL1890) L1890_cp1.1 L1890_cp1.2 = true := by
  decide +kernel
noncomputable def L1890_cp2 : Nat × Nat := t7val% (fastRun pL1890 1 1542 (init pL1890) (init pL1890))
theorem L1890_seg2 : segOK pL1890 1091 452 L1890_cp1.1 L1890_cp1.2 L1890_cp2.1 L1890_cp2.2 = true := by
  decide +kernel
theorem L1890_fin : (prmOK pL1890 1890 && ptTest pL1890 (runFrom pL1890 (fmask pL1890) (cmask pL1890) (hmask pL1890) 1543 347 (true, L1890_cp2.1, L1890_cp2.2)) 1890 945 false) = true := by
  decide +kernel
theorem L1890_ok : RunOK pL1890 1890 (runFrom pL1890 (fmask pL1890) (cmask pL1890) (hmask pL1890) 1543 347 (true, L1890_cp2.1, L1890_cp2.2)) ∧ ptTest pL1890 (runFrom pL1890 (fmask pL1890) (cmask pL1890) (hmask pL1890) 1543 347 (true, L1890_cp2.1, L1890_cp2.2)) 1890 945 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1890_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1890_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1890_fin) true) L1890_seg1) L1890_seg2) (by decide) rfl L1890_fin ptTest_fst
noncomputable def H1890_cp1 : Nat × Nat := t7val% (fastRun pH1890 1 1090 (init pH1890) (init pH1890))
theorem H1890_seg1 : segOK pH1890 1 1090 (init pH1890) (init pH1890) H1890_cp1.1 H1890_cp1.2 = true := by
  decide +kernel
noncomputable def H1890_cp2 : Nat × Nat := t7val% (fastRun pH1890 1 1542 (init pH1890) (init pH1890))
theorem H1890_seg2 : segOK pH1890 1091 452 H1890_cp1.1 H1890_cp1.2 H1890_cp2.1 H1890_cp2.2 = true := by
  decide +kernel
theorem H1890_fin : (prmOK pH1890 1890 && ptTest pH1890 (runFrom pH1890 (fmask pH1890) (cmask pH1890) (hmask pH1890) 1543 347 (true, H1890_cp2.1, H1890_cp2.2)) 1890 945 true) = true := by
  decide +kernel
theorem H1890_ok : RunOK pH1890 1890 (runFrom pH1890 (fmask pH1890) (cmask pH1890) (hmask pH1890) 1543 347 (true, H1890_cp2.1, H1890_cp2.2)) ∧ ptTest pH1890 (runFrom pH1890 (fmask pH1890) (cmask pH1890) (hmask pH1890) 1543 347 (true, H1890_cp2.1, H1890_cp2.2)) 1890 945 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1890_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1890_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1890_fin) true) H1890_seg1) H1890_seg2) (by decide) rfl H1890_fin ptTest_fst
noncomputable def I1890_cp1 : Nat × Nat := t7val% (fastRun pI1890 1 1090 (init pI1890) (init pI1890))
theorem I1890_seg1 : segOK pI1890 1 1090 (init pI1890) (init pI1890) I1890_cp1.1 I1890_cp1.2 = true := by
  decide +kernel
noncomputable def I1890_cp2 : Nat × Nat := t7val% (fastRun pI1890 1 1542 (init pI1890) (init pI1890))
theorem I1890_seg2 : segOK pI1890 1091 452 I1890_cp1.1 I1890_cp1.2 I1890_cp2.1 I1890_cp2.2 = true := by
  decide +kernel
theorem I1890_fin : (prmOK pI1890 1890 && intTest pI1890 (runFrom pI1890 (fmask pI1890) (cmask pI1890) (hmask pI1890) 1543 347 (true, I1890_cp2.1, I1890_cp2.2)) 1890 21 true) = true := by
  decide +kernel
theorem I1890_ok : RunOK pI1890 1890 (runFrom pI1890 (fmask pI1890) (cmask pI1890) (hmask pI1890) 1543 347 (true, I1890_cp2.1, I1890_cp2.2)) ∧ intTest pI1890 (runFrom pI1890 (fmask pI1890) (cmask pI1890) (hmask pI1890) 1543 347 (true, I1890_cp2.1, I1890_cp2.2)) 1890 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1890_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1890_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1890_fin) true) I1890_seg1) I1890_seg2) (by decide) rfl I1890_fin intTest_fst
theorem link1890 : linkOK pL1890 pH1890 pI1890 = true := by decide +kernel
theorem cvx1890 : ConvexBetweenHumps 1890 :=
  cvx_of L1890_ok H1890_ok I1890_ok link1890 (by decide)
theorem cenlink1890 : cenLinkOK pI1890 1890 = true := by decide +kernel
theorem cen1890 : CenterUniqueMin 1890 ∧ DipHyp 1890 ∧ OnePointHyps 1890 :=
  cen_of L1890_ok H1890_ok I1890_ok link1890 cenlink1890

/-! ### `N = 1891` -/

def pL1891 : Prm := ⟨80, 37, 40, 1893, 11, 18446744073709551616, 102969364336045771, 102969364336045771⟩
def pH1891 : Prm := ⟨80, 37, 40, 1893, 11, 18446744073709551616, 102970463847673547, 102970463847673547⟩
def pI1891 : Prm := ⟨68, 34, 31, 1893, 11, 18446744073709551616, 102969364336045771, 102970463847673547⟩
noncomputable def L1891_cp1 : Nat × Nat := t7val% (fastRun pL1891 1 1091 (init pL1891) (init pL1891))
theorem L1891_seg1 : segOK pL1891 1 1091 (init pL1891) (init pL1891) L1891_cp1.1 L1891_cp1.2 = true := by
  decide +kernel
noncomputable def L1891_cp2 : Nat × Nat := t7val% (fastRun pL1891 1 1543 (init pL1891) (init pL1891))
theorem L1891_seg2 : segOK pL1891 1092 452 L1891_cp1.1 L1891_cp1.2 L1891_cp2.1 L1891_cp2.2 = true := by
  decide +kernel
theorem L1891_fin : (prmOK pL1891 1891 && ptTest pL1891 (runFrom pL1891 (fmask pL1891) (cmask pL1891) (hmask pL1891) 1544 347 (true, L1891_cp2.1, L1891_cp2.2)) 1891 946 false) = true := by
  decide +kernel
theorem L1891_ok : RunOK pL1891 1891 (runFrom pL1891 (fmask pL1891) (cmask pL1891) (hmask pL1891) 1544 347 (true, L1891_cp2.1, L1891_cp2.2)) ∧ ptTest pL1891 (runFrom pL1891 (fmask pL1891) (cmask pL1891) (hmask pL1891) 1544 347 (true, L1891_cp2.1, L1891_cp2.2)) 1891 946 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1891_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1891_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1891_fin) true) L1891_seg1) L1891_seg2) (by decide) rfl L1891_fin ptTest_fst
noncomputable def H1891_cp1 : Nat × Nat := t7val% (fastRun pH1891 1 1091 (init pH1891) (init pH1891))
theorem H1891_seg1 : segOK pH1891 1 1091 (init pH1891) (init pH1891) H1891_cp1.1 H1891_cp1.2 = true := by
  decide +kernel
noncomputable def H1891_cp2 : Nat × Nat := t7val% (fastRun pH1891 1 1543 (init pH1891) (init pH1891))
theorem H1891_seg2 : segOK pH1891 1092 452 H1891_cp1.1 H1891_cp1.2 H1891_cp2.1 H1891_cp2.2 = true := by
  decide +kernel
theorem H1891_fin : (prmOK pH1891 1891 && ptTest pH1891 (runFrom pH1891 (fmask pH1891) (cmask pH1891) (hmask pH1891) 1544 347 (true, H1891_cp2.1, H1891_cp2.2)) 1891 946 true) = true := by
  decide +kernel
theorem H1891_ok : RunOK pH1891 1891 (runFrom pH1891 (fmask pH1891) (cmask pH1891) (hmask pH1891) 1544 347 (true, H1891_cp2.1, H1891_cp2.2)) ∧ ptTest pH1891 (runFrom pH1891 (fmask pH1891) (cmask pH1891) (hmask pH1891) 1544 347 (true, H1891_cp2.1, H1891_cp2.2)) 1891 946 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1891_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1891_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1891_fin) true) H1891_seg1) H1891_seg2) (by decide) rfl H1891_fin ptTest_fst
noncomputable def I1891_cp1 : Nat × Nat := t7val% (fastRun pI1891 1 1091 (init pI1891) (init pI1891))
theorem I1891_seg1 : segOK pI1891 1 1091 (init pI1891) (init pI1891) I1891_cp1.1 I1891_cp1.2 = true := by
  decide +kernel
noncomputable def I1891_cp2 : Nat × Nat := t7val% (fastRun pI1891 1 1543 (init pI1891) (init pI1891))
theorem I1891_seg2 : segOK pI1891 1092 452 I1891_cp1.1 I1891_cp1.2 I1891_cp2.1 I1891_cp2.2 = true := by
  decide +kernel
theorem I1891_fin : (prmOK pI1891 1891 && intTest pI1891 (runFrom pI1891 (fmask pI1891) (cmask pI1891) (hmask pI1891) 1544 347 (true, I1891_cp2.1, I1891_cp2.2)) 1891 21 false) = true := by
  decide +kernel
theorem I1891_ok : RunOK pI1891 1891 (runFrom pI1891 (fmask pI1891) (cmask pI1891) (hmask pI1891) 1544 347 (true, I1891_cp2.1, I1891_cp2.2)) ∧ intTest pI1891 (runFrom pI1891 (fmask pI1891) (cmask pI1891) (hmask pI1891) 1544 347 (true, I1891_cp2.1, I1891_cp2.2)) 1891 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1891_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1891_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1891_fin) true) I1891_seg1) I1891_seg2) (by decide) rfl I1891_fin intTest_fst
theorem link1891 : linkOK pL1891 pH1891 pI1891 = true := by decide +kernel
theorem cvx1891 : ConvexBetweenHumps 1891 :=
  cvx_of L1891_ok H1891_ok I1891_ok link1891 (by decide)

/-! ### `N = 1892` -/

def pL1892 : Prm := ⟨80, 37, 40, 1894, 11, 18446744073709551616, 102924664957599683, 102924664957599683⟩
def pH1892 : Prm := ⟨80, 37, 40, 1894, 11, 18446744073709551616, 102925764469227459, 102925764469227459⟩
def pI1892 : Prm := ⟨68, 34, 31, 1894, 11, 18446744073709551616, 102924664957599683, 102925764469227459⟩
noncomputable def L1892_cp1 : Nat × Nat := t7val% (fastRun pL1892 1 1091 (init pL1892) (init pL1892))
theorem L1892_seg1 : segOK pL1892 1 1091 (init pL1892) (init pL1892) L1892_cp1.1 L1892_cp1.2 = true := by
  decide +kernel
noncomputable def L1892_cp2 : Nat × Nat := t7val% (fastRun pL1892 1 1544 (init pL1892) (init pL1892))
theorem L1892_seg2 : segOK pL1892 1092 453 L1892_cp1.1 L1892_cp1.2 L1892_cp2.1 L1892_cp2.2 = true := by
  decide +kernel
theorem L1892_fin : (prmOK pL1892 1892 && ptTest pL1892 (runFrom pL1892 (fmask pL1892) (cmask pL1892) (hmask pL1892) 1545 347 (true, L1892_cp2.1, L1892_cp2.2)) 1892 946 false) = true := by
  decide +kernel
theorem L1892_ok : RunOK pL1892 1892 (runFrom pL1892 (fmask pL1892) (cmask pL1892) (hmask pL1892) 1545 347 (true, L1892_cp2.1, L1892_cp2.2)) ∧ ptTest pL1892 (runFrom pL1892 (fmask pL1892) (cmask pL1892) (hmask pL1892) 1545 347 (true, L1892_cp2.1, L1892_cp2.2)) 1892 946 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1892_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1892_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1892_fin) true) L1892_seg1) L1892_seg2) (by decide) rfl L1892_fin ptTest_fst
noncomputable def H1892_cp1 : Nat × Nat := t7val% (fastRun pH1892 1 1091 (init pH1892) (init pH1892))
theorem H1892_seg1 : segOK pH1892 1 1091 (init pH1892) (init pH1892) H1892_cp1.1 H1892_cp1.2 = true := by
  decide +kernel
noncomputable def H1892_cp2 : Nat × Nat := t7val% (fastRun pH1892 1 1544 (init pH1892) (init pH1892))
theorem H1892_seg2 : segOK pH1892 1092 453 H1892_cp1.1 H1892_cp1.2 H1892_cp2.1 H1892_cp2.2 = true := by
  decide +kernel
theorem H1892_fin : (prmOK pH1892 1892 && ptTest pH1892 (runFrom pH1892 (fmask pH1892) (cmask pH1892) (hmask pH1892) 1545 347 (true, H1892_cp2.1, H1892_cp2.2)) 1892 946 true) = true := by
  decide +kernel
theorem H1892_ok : RunOK pH1892 1892 (runFrom pH1892 (fmask pH1892) (cmask pH1892) (hmask pH1892) 1545 347 (true, H1892_cp2.1, H1892_cp2.2)) ∧ ptTest pH1892 (runFrom pH1892 (fmask pH1892) (cmask pH1892) (hmask pH1892) 1545 347 (true, H1892_cp2.1, H1892_cp2.2)) 1892 946 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1892_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1892_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1892_fin) true) H1892_seg1) H1892_seg2) (by decide) rfl H1892_fin ptTest_fst
noncomputable def I1892_cp1 : Nat × Nat := t7val% (fastRun pI1892 1 1091 (init pI1892) (init pI1892))
theorem I1892_seg1 : segOK pI1892 1 1091 (init pI1892) (init pI1892) I1892_cp1.1 I1892_cp1.2 = true := by
  decide +kernel
noncomputable def I1892_cp2 : Nat × Nat := t7val% (fastRun pI1892 1 1544 (init pI1892) (init pI1892))
theorem I1892_seg2 : segOK pI1892 1092 453 I1892_cp1.1 I1892_cp1.2 I1892_cp2.1 I1892_cp2.2 = true := by
  decide +kernel
theorem I1892_fin : (prmOK pI1892 1892 && intTest pI1892 (runFrom pI1892 (fmask pI1892) (cmask pI1892) (hmask pI1892) 1545 347 (true, I1892_cp2.1, I1892_cp2.2)) 1892 21 true) = true := by
  decide +kernel
theorem I1892_ok : RunOK pI1892 1892 (runFrom pI1892 (fmask pI1892) (cmask pI1892) (hmask pI1892) 1545 347 (true, I1892_cp2.1, I1892_cp2.2)) ∧ intTest pI1892 (runFrom pI1892 (fmask pI1892) (cmask pI1892) (hmask pI1892) 1545 347 (true, I1892_cp2.1, I1892_cp2.2)) 1892 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1892_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1892_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1892_fin) true) I1892_seg1) I1892_seg2) (by decide) rfl I1892_fin intTest_fst
theorem link1892 : linkOK pL1892 pH1892 pI1892 = true := by decide +kernel
theorem cvx1892 : ConvexBetweenHumps 1892 :=
  cvx_of L1892_ok H1892_ok I1892_ok link1892 (by decide)
theorem cenlink1892 : cenLinkOK pI1892 1892 = true := by decide +kernel
theorem cen1892 : CenterUniqueMin 1892 ∧ DipHyp 1892 ∧ OnePointHyps 1892 :=
  cen_of L1892_ok H1892_ok I1892_ok link1892 cenlink1892

/-! ### `N = 1893` -/

def pL1893 : Prm := ⟨80, 37, 40, 1895, 11, 18446744073709551616, 102879991141102007, 102879991141102007⟩
def pH1893 : Prm := ⟨80, 37, 40, 1895, 11, 18446744073709551616, 102881090652729783, 102881090652729783⟩
def pI1893 : Prm := ⟨68, 34, 31, 1895, 11, 18446744073709551616, 102879991141102007, 102881090652729783⟩
noncomputable def L1893_cp1 : Nat × Nat := t7val% (fastRun pL1893 1 1092 (init pL1893) (init pL1893))
theorem L1893_seg1 : segOK pL1893 1 1092 (init pL1893) (init pL1893) L1893_cp1.1 L1893_cp1.2 = true := by
  decide +kernel
noncomputable def L1893_cp2 : Nat × Nat := t7val% (fastRun pL1893 1 1545 (init pL1893) (init pL1893))
theorem L1893_seg2 : segOK pL1893 1093 453 L1893_cp1.1 L1893_cp1.2 L1893_cp2.1 L1893_cp2.2 = true := by
  decide +kernel
theorem L1893_fin : (prmOK pL1893 1893 && ptTest pL1893 (runFrom pL1893 (fmask pL1893) (cmask pL1893) (hmask pL1893) 1546 347 (true, L1893_cp2.1, L1893_cp2.2)) 1893 947 false) = true := by
  decide +kernel
theorem L1893_ok : RunOK pL1893 1893 (runFrom pL1893 (fmask pL1893) (cmask pL1893) (hmask pL1893) 1546 347 (true, L1893_cp2.1, L1893_cp2.2)) ∧ ptTest pL1893 (runFrom pL1893 (fmask pL1893) (cmask pL1893) (hmask pL1893) 1546 347 (true, L1893_cp2.1, L1893_cp2.2)) 1893 947 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1893_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1893_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1893_fin) true) L1893_seg1) L1893_seg2) (by decide) rfl L1893_fin ptTest_fst
noncomputable def H1893_cp1 : Nat × Nat := t7val% (fastRun pH1893 1 1092 (init pH1893) (init pH1893))
theorem H1893_seg1 : segOK pH1893 1 1092 (init pH1893) (init pH1893) H1893_cp1.1 H1893_cp1.2 = true := by
  decide +kernel
noncomputable def H1893_cp2 : Nat × Nat := t7val% (fastRun pH1893 1 1545 (init pH1893) (init pH1893))
theorem H1893_seg2 : segOK pH1893 1093 453 H1893_cp1.1 H1893_cp1.2 H1893_cp2.1 H1893_cp2.2 = true := by
  decide +kernel
theorem H1893_fin : (prmOK pH1893 1893 && ptTest pH1893 (runFrom pH1893 (fmask pH1893) (cmask pH1893) (hmask pH1893) 1546 347 (true, H1893_cp2.1, H1893_cp2.2)) 1893 947 true) = true := by
  decide +kernel
theorem H1893_ok : RunOK pH1893 1893 (runFrom pH1893 (fmask pH1893) (cmask pH1893) (hmask pH1893) 1546 347 (true, H1893_cp2.1, H1893_cp2.2)) ∧ ptTest pH1893 (runFrom pH1893 (fmask pH1893) (cmask pH1893) (hmask pH1893) 1546 347 (true, H1893_cp2.1, H1893_cp2.2)) 1893 947 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1893_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1893_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1893_fin) true) H1893_seg1) H1893_seg2) (by decide) rfl H1893_fin ptTest_fst
noncomputable def I1893_cp1 : Nat × Nat := t7val% (fastRun pI1893 1 1092 (init pI1893) (init pI1893))
theorem I1893_seg1 : segOK pI1893 1 1092 (init pI1893) (init pI1893) I1893_cp1.1 I1893_cp1.2 = true := by
  decide +kernel
noncomputable def I1893_cp2 : Nat × Nat := t7val% (fastRun pI1893 1 1545 (init pI1893) (init pI1893))
theorem I1893_seg2 : segOK pI1893 1093 453 I1893_cp1.1 I1893_cp1.2 I1893_cp2.1 I1893_cp2.2 = true := by
  decide +kernel
theorem I1893_fin : (prmOK pI1893 1893 && intTest pI1893 (runFrom pI1893 (fmask pI1893) (cmask pI1893) (hmask pI1893) 1546 347 (true, I1893_cp2.1, I1893_cp2.2)) 1893 21 false) = true := by
  decide +kernel
theorem I1893_ok : RunOK pI1893 1893 (runFrom pI1893 (fmask pI1893) (cmask pI1893) (hmask pI1893) 1546 347 (true, I1893_cp2.1, I1893_cp2.2)) ∧ intTest pI1893 (runFrom pI1893 (fmask pI1893) (cmask pI1893) (hmask pI1893) 1546 347 (true, I1893_cp2.1, I1893_cp2.2)) 1893 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1893_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1893_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1893_fin) true) I1893_seg1) I1893_seg2) (by decide) rfl I1893_fin intTest_fst
theorem link1893 : linkOK pL1893 pH1893 pI1893 = true := by decide +kernel
theorem cvx1893 : ConvexBetweenHumps 1893 :=
  cvx_of L1893_ok H1893_ok I1893_ok link1893 (by decide)

/-! ### `N = 1894` -/

def pL1894 : Prm := ⟨80, 37, 40, 1896, 11, 18446744073709551616, 102835375867689384, 102835375867689384⟩
def pH1894 : Prm := ⟨80, 37, 40, 1896, 11, 18446744073709551616, 102836475379317160, 102836475379317160⟩
def pI1894 : Prm := ⟨68, 34, 31, 1896, 11, 18446744073709551616, 102835375867689384, 102836475379317160⟩
noncomputable def L1894_cp1 : Nat × Nat := t7val% (fastRun pL1894 1 1093 (init pL1894) (init pL1894))
theorem L1894_seg1 : segOK pL1894 1 1093 (init pL1894) (init pL1894) L1894_cp1.1 L1894_cp1.2 = true := by
  decide +kernel
noncomputable def L1894_cp2 : Nat × Nat := t7val% (fastRun pL1894 1 1545 (init pL1894) (init pL1894))
theorem L1894_seg2 : segOK pL1894 1094 452 L1894_cp1.1 L1894_cp1.2 L1894_cp2.1 L1894_cp2.2 = true := by
  decide +kernel
theorem L1894_fin : (prmOK pL1894 1894 && ptTest pL1894 (runFrom pL1894 (fmask pL1894) (cmask pL1894) (hmask pL1894) 1546 348 (true, L1894_cp2.1, L1894_cp2.2)) 1894 947 false) = true := by
  decide +kernel
theorem L1894_ok : RunOK pL1894 1894 (runFrom pL1894 (fmask pL1894) (cmask pL1894) (hmask pL1894) 1546 348 (true, L1894_cp2.1, L1894_cp2.2)) ∧ ptTest pL1894 (runFrom pL1894 (fmask pL1894) (cmask pL1894) (hmask pL1894) 1546 348 (true, L1894_cp2.1, L1894_cp2.2)) 1894 947 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1894_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1894_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1894_fin) true) L1894_seg1) L1894_seg2) (by decide) rfl L1894_fin ptTest_fst
noncomputable def H1894_cp1 : Nat × Nat := t7val% (fastRun pH1894 1 1093 (init pH1894) (init pH1894))
theorem H1894_seg1 : segOK pH1894 1 1093 (init pH1894) (init pH1894) H1894_cp1.1 H1894_cp1.2 = true := by
  decide +kernel
noncomputable def H1894_cp2 : Nat × Nat := t7val% (fastRun pH1894 1 1545 (init pH1894) (init pH1894))
theorem H1894_seg2 : segOK pH1894 1094 452 H1894_cp1.1 H1894_cp1.2 H1894_cp2.1 H1894_cp2.2 = true := by
  decide +kernel
theorem H1894_fin : (prmOK pH1894 1894 && ptTest pH1894 (runFrom pH1894 (fmask pH1894) (cmask pH1894) (hmask pH1894) 1546 348 (true, H1894_cp2.1, H1894_cp2.2)) 1894 947 true) = true := by
  decide +kernel
theorem H1894_ok : RunOK pH1894 1894 (runFrom pH1894 (fmask pH1894) (cmask pH1894) (hmask pH1894) 1546 348 (true, H1894_cp2.1, H1894_cp2.2)) ∧ ptTest pH1894 (runFrom pH1894 (fmask pH1894) (cmask pH1894) (hmask pH1894) 1546 348 (true, H1894_cp2.1, H1894_cp2.2)) 1894 947 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1894_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1894_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1894_fin) true) H1894_seg1) H1894_seg2) (by decide) rfl H1894_fin ptTest_fst
noncomputable def I1894_cp1 : Nat × Nat := t7val% (fastRun pI1894 1 1093 (init pI1894) (init pI1894))
theorem I1894_seg1 : segOK pI1894 1 1093 (init pI1894) (init pI1894) I1894_cp1.1 I1894_cp1.2 = true := by
  decide +kernel
noncomputable def I1894_cp2 : Nat × Nat := t7val% (fastRun pI1894 1 1545 (init pI1894) (init pI1894))
theorem I1894_seg2 : segOK pI1894 1094 452 I1894_cp1.1 I1894_cp1.2 I1894_cp2.1 I1894_cp2.2 = true := by
  decide +kernel
theorem I1894_fin : (prmOK pI1894 1894 && intTest pI1894 (runFrom pI1894 (fmask pI1894) (cmask pI1894) (hmask pI1894) 1546 348 (true, I1894_cp2.1, I1894_cp2.2)) 1894 21 true) = true := by
  decide +kernel
theorem I1894_ok : RunOK pI1894 1894 (runFrom pI1894 (fmask pI1894) (cmask pI1894) (hmask pI1894) 1546 348 (true, I1894_cp2.1, I1894_cp2.2)) ∧ intTest pI1894 (runFrom pI1894 (fmask pI1894) (cmask pI1894) (hmask pI1894) 1546 348 (true, I1894_cp2.1, I1894_cp2.2)) 1894 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1894_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1894_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1894_fin) true) I1894_seg1) I1894_seg2) (by decide) rfl I1894_fin intTest_fst
theorem link1894 : linkOK pL1894 pH1894 pI1894 = true := by decide +kernel
theorem cvx1894 : ConvexBetweenHumps 1894 :=
  cvx_of L1894_ok H1894_ok I1894_ok link1894 (by decide)
theorem cenlink1894 : cenLinkOK pI1894 1894 = true := by decide +kernel
theorem cen1894 : CenterUniqueMin 1894 ∧ DipHyp 1894 ∧ OnePointHyps 1894 :=
  cen_of L1894_ok H1894_ok I1894_ok link1894 cenlink1894

/-! ### `N = 1895` -/

def pL1895 : Prm := ⟨80, 37, 40, 1897, 11, 18446744073709551616, 102790786086939202, 102790786086939202⟩
def pH1895 : Prm := ⟨80, 37, 40, 1897, 11, 18446744073709551616, 102791885598566978, 102791885598566978⟩
def pI1895 : Prm := ⟨68, 34, 31, 1897, 11, 18446744073709551616, 102790786086939202, 102791885598566978⟩
noncomputable def L1895_cp1 : Nat × Nat := t7val% (fastRun pL1895 1 1093 (init pL1895) (init pL1895))
theorem L1895_seg1 : segOK pL1895 1 1093 (init pL1895) (init pL1895) L1895_cp1.1 L1895_cp1.2 = true := by
  decide +kernel
noncomputable def L1895_cp2 : Nat × Nat := t7val% (fastRun pL1895 1 1546 (init pL1895) (init pL1895))
theorem L1895_seg2 : segOK pL1895 1094 453 L1895_cp1.1 L1895_cp1.2 L1895_cp2.1 L1895_cp2.2 = true := by
  decide +kernel
theorem L1895_fin : (prmOK pL1895 1895 && ptTest pL1895 (runFrom pL1895 (fmask pL1895) (cmask pL1895) (hmask pL1895) 1547 348 (true, L1895_cp2.1, L1895_cp2.2)) 1895 948 false) = true := by
  decide +kernel
theorem L1895_ok : RunOK pL1895 1895 (runFrom pL1895 (fmask pL1895) (cmask pL1895) (hmask pL1895) 1547 348 (true, L1895_cp2.1, L1895_cp2.2)) ∧ ptTest pL1895 (runFrom pL1895 (fmask pL1895) (cmask pL1895) (hmask pL1895) 1547 348 (true, L1895_cp2.1, L1895_cp2.2)) 1895 948 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1895_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1895_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1895_fin) true) L1895_seg1) L1895_seg2) (by decide) rfl L1895_fin ptTest_fst
noncomputable def H1895_cp1 : Nat × Nat := t7val% (fastRun pH1895 1 1093 (init pH1895) (init pH1895))
theorem H1895_seg1 : segOK pH1895 1 1093 (init pH1895) (init pH1895) H1895_cp1.1 H1895_cp1.2 = true := by
  decide +kernel
noncomputable def H1895_cp2 : Nat × Nat := t7val% (fastRun pH1895 1 1546 (init pH1895) (init pH1895))
theorem H1895_seg2 : segOK pH1895 1094 453 H1895_cp1.1 H1895_cp1.2 H1895_cp2.1 H1895_cp2.2 = true := by
  decide +kernel
theorem H1895_fin : (prmOK pH1895 1895 && ptTest pH1895 (runFrom pH1895 (fmask pH1895) (cmask pH1895) (hmask pH1895) 1547 348 (true, H1895_cp2.1, H1895_cp2.2)) 1895 948 true) = true := by
  decide +kernel
theorem H1895_ok : RunOK pH1895 1895 (runFrom pH1895 (fmask pH1895) (cmask pH1895) (hmask pH1895) 1547 348 (true, H1895_cp2.1, H1895_cp2.2)) ∧ ptTest pH1895 (runFrom pH1895 (fmask pH1895) (cmask pH1895) (hmask pH1895) 1547 348 (true, H1895_cp2.1, H1895_cp2.2)) 1895 948 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1895_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1895_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1895_fin) true) H1895_seg1) H1895_seg2) (by decide) rfl H1895_fin ptTest_fst
noncomputable def I1895_cp1 : Nat × Nat := t7val% (fastRun pI1895 1 1093 (init pI1895) (init pI1895))
theorem I1895_seg1 : segOK pI1895 1 1093 (init pI1895) (init pI1895) I1895_cp1.1 I1895_cp1.2 = true := by
  decide +kernel
noncomputable def I1895_cp2 : Nat × Nat := t7val% (fastRun pI1895 1 1546 (init pI1895) (init pI1895))
theorem I1895_seg2 : segOK pI1895 1094 453 I1895_cp1.1 I1895_cp1.2 I1895_cp2.1 I1895_cp2.2 = true := by
  decide +kernel
theorem I1895_fin : (prmOK pI1895 1895 && intTest pI1895 (runFrom pI1895 (fmask pI1895) (cmask pI1895) (hmask pI1895) 1547 348 (true, I1895_cp2.1, I1895_cp2.2)) 1895 21 false) = true := by
  decide +kernel
theorem I1895_ok : RunOK pI1895 1895 (runFrom pI1895 (fmask pI1895) (cmask pI1895) (hmask pI1895) 1547 348 (true, I1895_cp2.1, I1895_cp2.2)) ∧ intTest pI1895 (runFrom pI1895 (fmask pI1895) (cmask pI1895) (hmask pI1895) 1547 348 (true, I1895_cp2.1, I1895_cp2.2)) 1895 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1895_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1895_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1895_fin) true) I1895_seg1) I1895_seg2) (by decide) rfl I1895_fin intTest_fst
theorem link1895 : linkOK pL1895 pH1895 pI1895 = true := by decide +kernel
theorem cvx1895 : ConvexBetweenHumps 1895 :=
  cvx_of L1895_ok H1895_ok I1895_ok link1895 (by decide)

/-! ### `N = 1896` -/

def pL1896 : Prm := ⟨80, 37, 40, 1898, 11, 18446744073709551616, 102746254674122239, 102746254674122239⟩
def pH1896 : Prm := ⟨80, 37, 40, 1898, 11, 18446744073709551616, 102747354185750015, 102747354185750015⟩
def pI1896 : Prm := ⟨68, 34, 31, 1898, 11, 18446744073709551616, 102746254674122239, 102747354185750015⟩
noncomputable def L1896_cp1 : Nat × Nat := t7val% (fastRun pL1896 1 1094 (init pL1896) (init pL1896))
theorem L1896_seg1 : segOK pL1896 1 1094 (init pL1896) (init pL1896) L1896_cp1.1 L1896_cp1.2 = true := by
  decide +kernel
noncomputable def L1896_cp2 : Nat × Nat := t7val% (fastRun pL1896 1 1547 (init pL1896) (init pL1896))
theorem L1896_seg2 : segOK pL1896 1095 453 L1896_cp1.1 L1896_cp1.2 L1896_cp2.1 L1896_cp2.2 = true := by
  decide +kernel
theorem L1896_fin : (prmOK pL1896 1896 && ptTest pL1896 (runFrom pL1896 (fmask pL1896) (cmask pL1896) (hmask pL1896) 1548 348 (true, L1896_cp2.1, L1896_cp2.2)) 1896 948 false) = true := by
  decide +kernel
theorem L1896_ok : RunOK pL1896 1896 (runFrom pL1896 (fmask pL1896) (cmask pL1896) (hmask pL1896) 1548 348 (true, L1896_cp2.1, L1896_cp2.2)) ∧ ptTest pL1896 (runFrom pL1896 (fmask pL1896) (cmask pL1896) (hmask pL1896) 1548 348 (true, L1896_cp2.1, L1896_cp2.2)) 1896 948 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1896_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1896_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1896_fin) true) L1896_seg1) L1896_seg2) (by decide) rfl L1896_fin ptTest_fst
noncomputable def H1896_cp1 : Nat × Nat := t7val% (fastRun pH1896 1 1094 (init pH1896) (init pH1896))
theorem H1896_seg1 : segOK pH1896 1 1094 (init pH1896) (init pH1896) H1896_cp1.1 H1896_cp1.2 = true := by
  decide +kernel
noncomputable def H1896_cp2 : Nat × Nat := t7val% (fastRun pH1896 1 1547 (init pH1896) (init pH1896))
theorem H1896_seg2 : segOK pH1896 1095 453 H1896_cp1.1 H1896_cp1.2 H1896_cp2.1 H1896_cp2.2 = true := by
  decide +kernel
theorem H1896_fin : (prmOK pH1896 1896 && ptTest pH1896 (runFrom pH1896 (fmask pH1896) (cmask pH1896) (hmask pH1896) 1548 348 (true, H1896_cp2.1, H1896_cp2.2)) 1896 948 true) = true := by
  decide +kernel
theorem H1896_ok : RunOK pH1896 1896 (runFrom pH1896 (fmask pH1896) (cmask pH1896) (hmask pH1896) 1548 348 (true, H1896_cp2.1, H1896_cp2.2)) ∧ ptTest pH1896 (runFrom pH1896 (fmask pH1896) (cmask pH1896) (hmask pH1896) 1548 348 (true, H1896_cp2.1, H1896_cp2.2)) 1896 948 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1896_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1896_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1896_fin) true) H1896_seg1) H1896_seg2) (by decide) rfl H1896_fin ptTest_fst
noncomputable def I1896_cp1 : Nat × Nat := t7val% (fastRun pI1896 1 1094 (init pI1896) (init pI1896))
theorem I1896_seg1 : segOK pI1896 1 1094 (init pI1896) (init pI1896) I1896_cp1.1 I1896_cp1.2 = true := by
  decide +kernel
noncomputable def I1896_cp2 : Nat × Nat := t7val% (fastRun pI1896 1 1547 (init pI1896) (init pI1896))
theorem I1896_seg2 : segOK pI1896 1095 453 I1896_cp1.1 I1896_cp1.2 I1896_cp2.1 I1896_cp2.2 = true := by
  decide +kernel
theorem I1896_fin : (prmOK pI1896 1896 && intTest pI1896 (runFrom pI1896 (fmask pI1896) (cmask pI1896) (hmask pI1896) 1548 348 (true, I1896_cp2.1, I1896_cp2.2)) 1896 21 true) = true := by
  decide +kernel
theorem I1896_ok : RunOK pI1896 1896 (runFrom pI1896 (fmask pI1896) (cmask pI1896) (hmask pI1896) 1548 348 (true, I1896_cp2.1, I1896_cp2.2)) ∧ intTest pI1896 (runFrom pI1896 (fmask pI1896) (cmask pI1896) (hmask pI1896) 1548 348 (true, I1896_cp2.1, I1896_cp2.2)) 1896 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1896_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1896_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1896_fin) true) I1896_seg1) I1896_seg2) (by decide) rfl I1896_fin intTest_fst
theorem link1896 : linkOK pL1896 pH1896 pI1896 = true := by decide +kernel
theorem cvx1896 : ConvexBetweenHumps 1896 :=
  cvx_of L1896_ok H1896_ok I1896_ok link1896 (by decide)
theorem cenlink1896 : cenLinkOK pI1896 1896 = true := by decide +kernel
theorem cen1896 : CenterUniqueMin 1896 ∧ DipHyp 1896 ∧ OnePointHyps 1896 :=
  cen_of L1896_ok H1896_ok I1896_ok link1896 cenlink1896

/-! ### `N = 1897` -/

def pL1897 : Prm := ⟨80, 37, 40, 1899, 11, 18446744073709551616, 102701748684958446, 102701748684958446⟩
def pH1897 : Prm := ⟨80, 37, 40, 1899, 11, 18446744073709551616, 102702848196586222, 102702848196586222⟩
def pI1897 : Prm := ⟨68, 34, 31, 1899, 11, 18446744073709551616, 102701748684958446, 102702848196586222⟩
noncomputable def L1897_cp1 : Nat × Nat := t7val% (fastRun pL1897 1 1094 (init pL1897) (init pL1897))
theorem L1897_seg1 : segOK pL1897 1 1094 (init pL1897) (init pL1897) L1897_cp1.1 L1897_cp1.2 = true := by
  decide +kernel
noncomputable def L1897_cp2 : Nat × Nat := t7val% (fastRun pL1897 1 1548 (init pL1897) (init pL1897))
theorem L1897_seg2 : segOK pL1897 1095 454 L1897_cp1.1 L1897_cp1.2 L1897_cp2.1 L1897_cp2.2 = true := by
  decide +kernel
theorem L1897_fin : (prmOK pL1897 1897 && ptTest pL1897 (runFrom pL1897 (fmask pL1897) (cmask pL1897) (hmask pL1897) 1549 348 (true, L1897_cp2.1, L1897_cp2.2)) 1897 949 false) = true := by
  decide +kernel
theorem L1897_ok : RunOK pL1897 1897 (runFrom pL1897 (fmask pL1897) (cmask pL1897) (hmask pL1897) 1549 348 (true, L1897_cp2.1, L1897_cp2.2)) ∧ ptTest pL1897 (runFrom pL1897 (fmask pL1897) (cmask pL1897) (hmask pL1897) 1549 348 (true, L1897_cp2.1, L1897_cp2.2)) 1897 949 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1897_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1897_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1897_fin) true) L1897_seg1) L1897_seg2) (by decide) rfl L1897_fin ptTest_fst
noncomputable def H1897_cp1 : Nat × Nat := t7val% (fastRun pH1897 1 1094 (init pH1897) (init pH1897))
theorem H1897_seg1 : segOK pH1897 1 1094 (init pH1897) (init pH1897) H1897_cp1.1 H1897_cp1.2 = true := by
  decide +kernel
noncomputable def H1897_cp2 : Nat × Nat := t7val% (fastRun pH1897 1 1548 (init pH1897) (init pH1897))
theorem H1897_seg2 : segOK pH1897 1095 454 H1897_cp1.1 H1897_cp1.2 H1897_cp2.1 H1897_cp2.2 = true := by
  decide +kernel
theorem H1897_fin : (prmOK pH1897 1897 && ptTest pH1897 (runFrom pH1897 (fmask pH1897) (cmask pH1897) (hmask pH1897) 1549 348 (true, H1897_cp2.1, H1897_cp2.2)) 1897 949 true) = true := by
  decide +kernel
theorem H1897_ok : RunOK pH1897 1897 (runFrom pH1897 (fmask pH1897) (cmask pH1897) (hmask pH1897) 1549 348 (true, H1897_cp2.1, H1897_cp2.2)) ∧ ptTest pH1897 (runFrom pH1897 (fmask pH1897) (cmask pH1897) (hmask pH1897) 1549 348 (true, H1897_cp2.1, H1897_cp2.2)) 1897 949 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1897_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1897_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1897_fin) true) H1897_seg1) H1897_seg2) (by decide) rfl H1897_fin ptTest_fst
noncomputable def I1897_cp1 : Nat × Nat := t7val% (fastRun pI1897 1 1094 (init pI1897) (init pI1897))
theorem I1897_seg1 : segOK pI1897 1 1094 (init pI1897) (init pI1897) I1897_cp1.1 I1897_cp1.2 = true := by
  decide +kernel
noncomputable def I1897_cp2 : Nat × Nat := t7val% (fastRun pI1897 1 1548 (init pI1897) (init pI1897))
theorem I1897_seg2 : segOK pI1897 1095 454 I1897_cp1.1 I1897_cp1.2 I1897_cp2.1 I1897_cp2.2 = true := by
  decide +kernel
theorem I1897_fin : (prmOK pI1897 1897 && intTest pI1897 (runFrom pI1897 (fmask pI1897) (cmask pI1897) (hmask pI1897) 1549 348 (true, I1897_cp2.1, I1897_cp2.2)) 1897 21 false) = true := by
  decide +kernel
theorem I1897_ok : RunOK pI1897 1897 (runFrom pI1897 (fmask pI1897) (cmask pI1897) (hmask pI1897) 1549 348 (true, I1897_cp2.1, I1897_cp2.2)) ∧ intTest pI1897 (runFrom pI1897 (fmask pI1897) (cmask pI1897) (hmask pI1897) 1549 348 (true, I1897_cp2.1, I1897_cp2.2)) 1897 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1897_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1897_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1897_fin) true) I1897_seg1) I1897_seg2) (by decide) rfl I1897_fin intTest_fst
theorem link1897 : linkOK pL1897 pH1897 pI1897 = true := by decide +kernel
theorem cvx1897 : ConvexBetweenHumps 1897 :=
  cvx_of L1897_ok H1897_ok I1897_ok link1897 (by decide)

/-! ### The range -/

theorem cvx_1887_1897 {N : ℕ} (h1 : 1887 ≤ N) (h2 : N ≤ 1897) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1891
  · by_cases h4 : N ≤ 1888
    · by_cases h6 : N ≤ 1887
      · obtain rfl : N = 1887 := by omega
        exact cvx1887
      · obtain rfl : N = 1888 := by omega
        exact cvx1888
    · by_cases h6 : N ≤ 1889
      · obtain rfl : N = 1889 := by omega
        exact cvx1889
      · by_cases h8 : N ≤ 1890
        · obtain rfl : N = 1890 := by omega
          exact cvx1890
        · obtain rfl : N = 1891 := by omega
          exact cvx1891
  · by_cases h4 : N ≤ 1894
    · by_cases h6 : N ≤ 1892
      · obtain rfl : N = 1892 := by omega
        exact cvx1892
      · by_cases h8 : N ≤ 1893
        · obtain rfl : N = 1893 := by omega
          exact cvx1893
        · obtain rfl : N = 1894 := by omega
          exact cvx1894
    · by_cases h6 : N ≤ 1895
      · obtain rfl : N = 1895 := by omega
        exact cvx1895
      · by_cases h8 : N ≤ 1896
        · obtain rfl : N = 1896 := by omega
          exact cvx1896
        · obtain rfl : N = 1897 := by omega
          exact cvx1897

theorem cen_1887_1897 {N : ℕ} (h1 : 1887 ≤ N) (h2 : N ≤ 1897) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1890
  · by_cases h4 : N ≤ 1888
    · obtain rfl : N = 1888 := by omega
      exact cen1888
    · obtain rfl : N = 1890 := by omega
      exact cen1890
  · by_cases h4 : N ≤ 1892
    · obtain rfl : N = 1892 := by omega
      exact cen1892
    · by_cases h6 : N ≤ 1894
      · obtain rfl : N = 1894 := by omega
        exact cen1894
      · obtain rfl : N = 1896 := by omega
        exact cen1896

end Kagey131.PaperD.T7
