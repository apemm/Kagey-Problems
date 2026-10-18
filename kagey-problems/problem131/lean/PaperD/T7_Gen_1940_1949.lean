import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1940, …, 1949` (generated)

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

/-! ### `N = 1940` -/

def pL1940 : Prm := ⟨81, 38, 40, 1942, 11, 18446744073709551616, 100827099267442016, 100827099267442016⟩
def pH1940 : Prm := ⟨81, 38, 40, 1942, 11, 18446744073709551616, 100828198779069792, 100828198779069792⟩
def pI1940 : Prm := ⟨68, 34, 31, 1942, 11, 18446744073709551616, 100827099267442016, 100828198779069792⟩
noncomputable def L1940_cp1 : Nat × Nat := t7val% (fastRun pL1940 1 1119 (init pL1940) (init pL1940))
theorem L1940_seg1 : segOK pL1940 1 1119 (init pL1940) (init pL1940) L1940_cp1.1 L1940_cp1.2 = true := by
  decide +kernel
noncomputable def L1940_cp2 : Nat × Nat := t7val% (fastRun pL1940 1 1583 (init pL1940) (init pL1940))
theorem L1940_seg2 : segOK pL1940 1120 464 L1940_cp1.1 L1940_cp1.2 L1940_cp2.1 L1940_cp2.2 = true := by
  decide +kernel
theorem L1940_fin : (prmOK pL1940 1940 && ptTest pL1940 (runFrom pL1940 (fmask pL1940) (cmask pL1940) (hmask pL1940) 1584 356 (true, L1940_cp2.1, L1940_cp2.2)) 1940 970 false) = true := by
  decide +kernel
theorem L1940_ok : RunOK pL1940 1940 (runFrom pL1940 (fmask pL1940) (cmask pL1940) (hmask pL1940) 1584 356 (true, L1940_cp2.1, L1940_cp2.2)) ∧ ptTest pL1940 (runFrom pL1940 (fmask pL1940) (cmask pL1940) (hmask pL1940) 1584 356 (true, L1940_cp2.1, L1940_cp2.2)) 1940 970 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1940_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1940_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1940_fin) true) L1940_seg1) L1940_seg2) (by decide) rfl L1940_fin ptTest_fst
noncomputable def H1940_cp1 : Nat × Nat := t7val% (fastRun pH1940 1 1119 (init pH1940) (init pH1940))
theorem H1940_seg1 : segOK pH1940 1 1119 (init pH1940) (init pH1940) H1940_cp1.1 H1940_cp1.2 = true := by
  decide +kernel
noncomputable def H1940_cp2 : Nat × Nat := t7val% (fastRun pH1940 1 1583 (init pH1940) (init pH1940))
theorem H1940_seg2 : segOK pH1940 1120 464 H1940_cp1.1 H1940_cp1.2 H1940_cp2.1 H1940_cp2.2 = true := by
  decide +kernel
theorem H1940_fin : (prmOK pH1940 1940 && ptTest pH1940 (runFrom pH1940 (fmask pH1940) (cmask pH1940) (hmask pH1940) 1584 356 (true, H1940_cp2.1, H1940_cp2.2)) 1940 970 true) = true := by
  decide +kernel
theorem H1940_ok : RunOK pH1940 1940 (runFrom pH1940 (fmask pH1940) (cmask pH1940) (hmask pH1940) 1584 356 (true, H1940_cp2.1, H1940_cp2.2)) ∧ ptTest pH1940 (runFrom pH1940 (fmask pH1940) (cmask pH1940) (hmask pH1940) 1584 356 (true, H1940_cp2.1, H1940_cp2.2)) 1940 970 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1940_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1940_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1940_fin) true) H1940_seg1) H1940_seg2) (by decide) rfl H1940_fin ptTest_fst
noncomputable def I1940_cp1 : Nat × Nat := t7val% (fastRun pI1940 1 1119 (init pI1940) (init pI1940))
theorem I1940_seg1 : segOK pI1940 1 1119 (init pI1940) (init pI1940) I1940_cp1.1 I1940_cp1.2 = true := by
  decide +kernel
noncomputable def I1940_cp2 : Nat × Nat := t7val% (fastRun pI1940 1 1583 (init pI1940) (init pI1940))
theorem I1940_seg2 : segOK pI1940 1120 464 I1940_cp1.1 I1940_cp1.2 I1940_cp2.1 I1940_cp2.2 = true := by
  decide +kernel
theorem I1940_fin : (prmOK pI1940 1940 && intTest pI1940 (runFrom pI1940 (fmask pI1940) (cmask pI1940) (hmask pI1940) 1584 356 (true, I1940_cp2.1, I1940_cp2.2)) 1940 22 true) = true := by
  decide +kernel
theorem I1940_ok : RunOK pI1940 1940 (runFrom pI1940 (fmask pI1940) (cmask pI1940) (hmask pI1940) 1584 356 (true, I1940_cp2.1, I1940_cp2.2)) ∧ intTest pI1940 (runFrom pI1940 (fmask pI1940) (cmask pI1940) (hmask pI1940) 1584 356 (true, I1940_cp2.1, I1940_cp2.2)) 1940 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1940_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1940_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1940_fin) true) I1940_seg1) I1940_seg2) (by decide) rfl I1940_fin intTest_fst
theorem link1940 : linkOK pL1940 pH1940 pI1940 = true := by decide +kernel
theorem cvx1940 : ConvexBetweenHumps 1940 :=
  cvx_of L1940_ok H1940_ok I1940_ok link1940 (by decide)
theorem cenlink1940 : cenLinkOK pI1940 1940 = true := by decide +kernel
theorem cen1940 : CenterUniqueMin 1940 ∧ DipHyp 1940 ∧ OnePointHyps 1940 :=
  cen_of L1940_ok H1940_ok I1940_ok link1940 cenlink1940

/-! ### `N = 1941` -/

def pL1941 : Prm := ⟨80, 37, 40, 1943, 11, 18446744073709551616, 100784376816781533, 100784376816781533⟩
def pH1941 : Prm := ⟨81, 38, 40, 1943, 11, 18446744073709551616, 100785476328409309, 100785476328409309⟩
def pI1941 : Prm := ⟨68, 34, 31, 1943, 11, 18446744073709551616, 100784376816781533, 100785476328409309⟩
noncomputable def L1941_cp1 : Nat × Nat := t7val% (fastRun pL1941 1 1120 (init pL1941) (init pL1941))
theorem L1941_seg1 : segOK pL1941 1 1120 (init pL1941) (init pL1941) L1941_cp1.1 L1941_cp1.2 = true := by
  decide +kernel
noncomputable def L1941_cp2 : Nat × Nat := t7val% (fastRun pL1941 1 1584 (init pL1941) (init pL1941))
theorem L1941_seg2 : segOK pL1941 1121 464 L1941_cp1.1 L1941_cp1.2 L1941_cp2.1 L1941_cp2.2 = true := by
  decide +kernel
theorem L1941_fin : (prmOK pL1941 1941 && ptTest pL1941 (runFrom pL1941 (fmask pL1941) (cmask pL1941) (hmask pL1941) 1585 356 (true, L1941_cp2.1, L1941_cp2.2)) 1941 971 false) = true := by
  decide +kernel
theorem L1941_ok : RunOK pL1941 1941 (runFrom pL1941 (fmask pL1941) (cmask pL1941) (hmask pL1941) 1585 356 (true, L1941_cp2.1, L1941_cp2.2)) ∧ ptTest pL1941 (runFrom pL1941 (fmask pL1941) (cmask pL1941) (hmask pL1941) 1585 356 (true, L1941_cp2.1, L1941_cp2.2)) 1941 971 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1941_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1941_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1941_fin) true) L1941_seg1) L1941_seg2) (by decide) rfl L1941_fin ptTest_fst
noncomputable def H1941_cp1 : Nat × Nat := t7val% (fastRun pH1941 1 1120 (init pH1941) (init pH1941))
theorem H1941_seg1 : segOK pH1941 1 1120 (init pH1941) (init pH1941) H1941_cp1.1 H1941_cp1.2 = true := by
  decide +kernel
noncomputable def H1941_cp2 : Nat × Nat := t7val% (fastRun pH1941 1 1584 (init pH1941) (init pH1941))
theorem H1941_seg2 : segOK pH1941 1121 464 H1941_cp1.1 H1941_cp1.2 H1941_cp2.1 H1941_cp2.2 = true := by
  decide +kernel
theorem H1941_fin : (prmOK pH1941 1941 && ptTest pH1941 (runFrom pH1941 (fmask pH1941) (cmask pH1941) (hmask pH1941) 1585 356 (true, H1941_cp2.1, H1941_cp2.2)) 1941 971 true) = true := by
  decide +kernel
theorem H1941_ok : RunOK pH1941 1941 (runFrom pH1941 (fmask pH1941) (cmask pH1941) (hmask pH1941) 1585 356 (true, H1941_cp2.1, H1941_cp2.2)) ∧ ptTest pH1941 (runFrom pH1941 (fmask pH1941) (cmask pH1941) (hmask pH1941) 1585 356 (true, H1941_cp2.1, H1941_cp2.2)) 1941 971 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1941_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1941_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1941_fin) true) H1941_seg1) H1941_seg2) (by decide) rfl H1941_fin ptTest_fst
noncomputable def I1941_cp1 : Nat × Nat := t7val% (fastRun pI1941 1 1120 (init pI1941) (init pI1941))
theorem I1941_seg1 : segOK pI1941 1 1120 (init pI1941) (init pI1941) I1941_cp1.1 I1941_cp1.2 = true := by
  decide +kernel
noncomputable def I1941_cp2 : Nat × Nat := t7val% (fastRun pI1941 1 1584 (init pI1941) (init pI1941))
theorem I1941_seg2 : segOK pI1941 1121 464 I1941_cp1.1 I1941_cp1.2 I1941_cp2.1 I1941_cp2.2 = true := by
  decide +kernel
theorem I1941_fin : (prmOK pI1941 1941 && intTest pI1941 (runFrom pI1941 (fmask pI1941) (cmask pI1941) (hmask pI1941) 1585 356 (true, I1941_cp2.1, I1941_cp2.2)) 1941 22 false) = true := by
  decide +kernel
theorem I1941_ok : RunOK pI1941 1941 (runFrom pI1941 (fmask pI1941) (cmask pI1941) (hmask pI1941) 1585 356 (true, I1941_cp2.1, I1941_cp2.2)) ∧ intTest pI1941 (runFrom pI1941 (fmask pI1941) (cmask pI1941) (hmask pI1941) 1585 356 (true, I1941_cp2.1, I1941_cp2.2)) 1941 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1941_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1941_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1941_fin) true) I1941_seg1) I1941_seg2) (by decide) rfl I1941_fin intTest_fst
theorem link1941 : linkOK pL1941 pH1941 pI1941 = true := by decide +kernel
theorem cvx1941 : ConvexBetweenHumps 1941 :=
  cvx_of L1941_ok H1941_ok I1941_ok link1941 (by decide)

/-! ### `N = 1942` -/

def pL1942 : Prm := ⟨80, 37, 40, 1944, 11, 18446744073709551616, 100741708894198470, 100741708894198470⟩
def pH1942 : Prm := ⟨80, 37, 40, 1944, 11, 18446744073709551616, 100742808405826246, 100742808405826246⟩
def pI1942 : Prm := ⟨68, 34, 31, 1944, 11, 18446744073709551616, 100741708894198470, 100742808405826246⟩
noncomputable def L1942_cp1 : Nat × Nat := t7val% (fastRun pL1942 1 1120 (init pL1942) (init pL1942))
theorem L1942_seg1 : segOK pL1942 1 1120 (init pL1942) (init pL1942) L1942_cp1.1 L1942_cp1.2 = true := by
  decide +kernel
noncomputable def L1942_cp2 : Nat × Nat := t7val% (fastRun pL1942 1 1585 (init pL1942) (init pL1942))
theorem L1942_seg2 : segOK pL1942 1121 465 L1942_cp1.1 L1942_cp1.2 L1942_cp2.1 L1942_cp2.2 = true := by
  decide +kernel
theorem L1942_fin : (prmOK pL1942 1942 && ptTest pL1942 (runFrom pL1942 (fmask pL1942) (cmask pL1942) (hmask pL1942) 1586 356 (true, L1942_cp2.1, L1942_cp2.2)) 1942 971 false) = true := by
  decide +kernel
theorem L1942_ok : RunOK pL1942 1942 (runFrom pL1942 (fmask pL1942) (cmask pL1942) (hmask pL1942) 1586 356 (true, L1942_cp2.1, L1942_cp2.2)) ∧ ptTest pL1942 (runFrom pL1942 (fmask pL1942) (cmask pL1942) (hmask pL1942) 1586 356 (true, L1942_cp2.1, L1942_cp2.2)) 1942 971 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1942_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1942_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1942_fin) true) L1942_seg1) L1942_seg2) (by decide) rfl L1942_fin ptTest_fst
noncomputable def H1942_cp1 : Nat × Nat := t7val% (fastRun pH1942 1 1120 (init pH1942) (init pH1942))
theorem H1942_seg1 : segOK pH1942 1 1120 (init pH1942) (init pH1942) H1942_cp1.1 H1942_cp1.2 = true := by
  decide +kernel
noncomputable def H1942_cp2 : Nat × Nat := t7val% (fastRun pH1942 1 1585 (init pH1942) (init pH1942))
theorem H1942_seg2 : segOK pH1942 1121 465 H1942_cp1.1 H1942_cp1.2 H1942_cp2.1 H1942_cp2.2 = true := by
  decide +kernel
theorem H1942_fin : (prmOK pH1942 1942 && ptTest pH1942 (runFrom pH1942 (fmask pH1942) (cmask pH1942) (hmask pH1942) 1586 356 (true, H1942_cp2.1, H1942_cp2.2)) 1942 971 true) = true := by
  decide +kernel
theorem H1942_ok : RunOK pH1942 1942 (runFrom pH1942 (fmask pH1942) (cmask pH1942) (hmask pH1942) 1586 356 (true, H1942_cp2.1, H1942_cp2.2)) ∧ ptTest pH1942 (runFrom pH1942 (fmask pH1942) (cmask pH1942) (hmask pH1942) 1586 356 (true, H1942_cp2.1, H1942_cp2.2)) 1942 971 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1942_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1942_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1942_fin) true) H1942_seg1) H1942_seg2) (by decide) rfl H1942_fin ptTest_fst
noncomputable def I1942_cp1 : Nat × Nat := t7val% (fastRun pI1942 1 1120 (init pI1942) (init pI1942))
theorem I1942_seg1 : segOK pI1942 1 1120 (init pI1942) (init pI1942) I1942_cp1.1 I1942_cp1.2 = true := by
  decide +kernel
noncomputable def I1942_cp2 : Nat × Nat := t7val% (fastRun pI1942 1 1585 (init pI1942) (init pI1942))
theorem I1942_seg2 : segOK pI1942 1121 465 I1942_cp1.1 I1942_cp1.2 I1942_cp2.1 I1942_cp2.2 = true := by
  decide +kernel
theorem I1942_fin : (prmOK pI1942 1942 && intTest pI1942 (runFrom pI1942 (fmask pI1942) (cmask pI1942) (hmask pI1942) 1586 356 (true, I1942_cp2.1, I1942_cp2.2)) 1942 22 true) = true := by
  decide +kernel
theorem I1942_ok : RunOK pI1942 1942 (runFrom pI1942 (fmask pI1942) (cmask pI1942) (hmask pI1942) 1586 356 (true, I1942_cp2.1, I1942_cp2.2)) ∧ intTest pI1942 (runFrom pI1942 (fmask pI1942) (cmask pI1942) (hmask pI1942) 1586 356 (true, I1942_cp2.1, I1942_cp2.2)) 1942 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1942_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1942_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1942_fin) true) I1942_seg1) I1942_seg2) (by decide) rfl I1942_fin intTest_fst
theorem link1942 : linkOK pL1942 pH1942 pI1942 = true := by decide +kernel
theorem cvx1942 : ConvexBetweenHumps 1942 :=
  cvx_of L1942_ok H1942_ok I1942_ok link1942 (by decide)
theorem cenlink1942 : cenLinkOK pI1942 1942 = true := by decide +kernel
theorem cen1942 : CenterUniqueMin 1942 ∧ DipHyp 1942 ∧ OnePointHyps 1942 :=
  cen_of L1942_ok H1942_ok I1942_ok link1942 cenlink1942

/-! ### `N = 1943` -/

def pL1943 : Prm := ⟨80, 37, 40, 1945, 11, 18446744073709551616, 100699064875330653, 100699064875330653⟩
def pH1943 : Prm := ⟨81, 38, 40, 1945, 11, 18446744073709551616, 100700164386958429, 100700164386958429⟩
def pI1943 : Prm := ⟨68, 34, 31, 1945, 11, 18446744073709551616, 100699064875330653, 100700164386958429⟩
noncomputable def L1943_cp1 : Nat × Nat := t7val% (fastRun pL1943 1 1121 (init pL1943) (init pL1943))
theorem L1943_seg1 : segOK pL1943 1 1121 (init pL1943) (init pL1943) L1943_cp1.1 L1943_cp1.2 = true := by
  decide +kernel
noncomputable def L1943_cp2 : Nat × Nat := t7val% (fastRun pL1943 1 1585 (init pL1943) (init pL1943))
theorem L1943_seg2 : segOK pL1943 1122 464 L1943_cp1.1 L1943_cp1.2 L1943_cp2.1 L1943_cp2.2 = true := by
  decide +kernel
theorem L1943_fin : (prmOK pL1943 1943 && ptTest pL1943 (runFrom pL1943 (fmask pL1943) (cmask pL1943) (hmask pL1943) 1586 357 (true, L1943_cp2.1, L1943_cp2.2)) 1943 972 false) = true := by
  decide +kernel
theorem L1943_ok : RunOK pL1943 1943 (runFrom pL1943 (fmask pL1943) (cmask pL1943) (hmask pL1943) 1586 357 (true, L1943_cp2.1, L1943_cp2.2)) ∧ ptTest pL1943 (runFrom pL1943 (fmask pL1943) (cmask pL1943) (hmask pL1943) 1586 357 (true, L1943_cp2.1, L1943_cp2.2)) 1943 972 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1943_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1943_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1943_fin) true) L1943_seg1) L1943_seg2) (by decide) rfl L1943_fin ptTest_fst
noncomputable def H1943_cp1 : Nat × Nat := t7val% (fastRun pH1943 1 1121 (init pH1943) (init pH1943))
theorem H1943_seg1 : segOK pH1943 1 1121 (init pH1943) (init pH1943) H1943_cp1.1 H1943_cp1.2 = true := by
  decide +kernel
noncomputable def H1943_cp2 : Nat × Nat := t7val% (fastRun pH1943 1 1585 (init pH1943) (init pH1943))
theorem H1943_seg2 : segOK pH1943 1122 464 H1943_cp1.1 H1943_cp1.2 H1943_cp2.1 H1943_cp2.2 = true := by
  decide +kernel
theorem H1943_fin : (prmOK pH1943 1943 && ptTest pH1943 (runFrom pH1943 (fmask pH1943) (cmask pH1943) (hmask pH1943) 1586 357 (true, H1943_cp2.1, H1943_cp2.2)) 1943 972 true) = true := by
  decide +kernel
theorem H1943_ok : RunOK pH1943 1943 (runFrom pH1943 (fmask pH1943) (cmask pH1943) (hmask pH1943) 1586 357 (true, H1943_cp2.1, H1943_cp2.2)) ∧ ptTest pH1943 (runFrom pH1943 (fmask pH1943) (cmask pH1943) (hmask pH1943) 1586 357 (true, H1943_cp2.1, H1943_cp2.2)) 1943 972 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1943_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1943_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1943_fin) true) H1943_seg1) H1943_seg2) (by decide) rfl H1943_fin ptTest_fst
noncomputable def I1943_cp1 : Nat × Nat := t7val% (fastRun pI1943 1 1121 (init pI1943) (init pI1943))
theorem I1943_seg1 : segOK pI1943 1 1121 (init pI1943) (init pI1943) I1943_cp1.1 I1943_cp1.2 = true := by
  decide +kernel
noncomputable def I1943_cp2 : Nat × Nat := t7val% (fastRun pI1943 1 1585 (init pI1943) (init pI1943))
theorem I1943_seg2 : segOK pI1943 1122 464 I1943_cp1.1 I1943_cp1.2 I1943_cp2.1 I1943_cp2.2 = true := by
  decide +kernel
theorem I1943_fin : (prmOK pI1943 1943 && intTest pI1943 (runFrom pI1943 (fmask pI1943) (cmask pI1943) (hmask pI1943) 1586 357 (true, I1943_cp2.1, I1943_cp2.2)) 1943 22 false) = true := by
  decide +kernel
theorem I1943_ok : RunOK pI1943 1943 (runFrom pI1943 (fmask pI1943) (cmask pI1943) (hmask pI1943) 1586 357 (true, I1943_cp2.1, I1943_cp2.2)) ∧ intTest pI1943 (runFrom pI1943 (fmask pI1943) (cmask pI1943) (hmask pI1943) 1586 357 (true, I1943_cp2.1, I1943_cp2.2)) 1943 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1943_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1943_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1943_fin) true) I1943_seg1) I1943_seg2) (by decide) rfl I1943_fin intTest_fst
theorem link1943 : linkOK pL1943 pH1943 pI1943 = true := by decide +kernel
theorem cvx1943 : ConvexBetweenHumps 1943 :=
  cvx_of L1943_ok H1943_ok I1943_ok link1943 (by decide)

/-! ### `N = 1944` -/

def pL1944 : Prm := ⟨81, 38, 40, 1946, 11, 18446744073709551616, 100656475225400195, 100656475225400195⟩
def pH1944 : Prm := ⟨81, 38, 40, 1946, 11, 18446744073709551616, 100657574737027971, 100657574737027971⟩
def pI1944 : Prm := ⟨68, 34, 31, 1946, 11, 18446744073709551616, 100656475225400195, 100657574737027971⟩
noncomputable def L1944_cp1 : Nat × Nat := t7val% (fastRun pL1944 1 1121 (init pL1944) (init pL1944))
theorem L1944_seg1 : segOK pL1944 1 1121 (init pL1944) (init pL1944) L1944_cp1.1 L1944_cp1.2 = true := by
  decide +kernel
noncomputable def L1944_cp2 : Nat × Nat := t7val% (fastRun pL1944 1 1586 (init pL1944) (init pL1944))
theorem L1944_seg2 : segOK pL1944 1122 465 L1944_cp1.1 L1944_cp1.2 L1944_cp2.1 L1944_cp2.2 = true := by
  decide +kernel
theorem L1944_fin : (prmOK pL1944 1944 && ptTest pL1944 (runFrom pL1944 (fmask pL1944) (cmask pL1944) (hmask pL1944) 1587 357 (true, L1944_cp2.1, L1944_cp2.2)) 1944 972 false) = true := by
  decide +kernel
theorem L1944_ok : RunOK pL1944 1944 (runFrom pL1944 (fmask pL1944) (cmask pL1944) (hmask pL1944) 1587 357 (true, L1944_cp2.1, L1944_cp2.2)) ∧ ptTest pL1944 (runFrom pL1944 (fmask pL1944) (cmask pL1944) (hmask pL1944) 1587 357 (true, L1944_cp2.1, L1944_cp2.2)) 1944 972 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1944_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1944_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1944_fin) true) L1944_seg1) L1944_seg2) (by decide) rfl L1944_fin ptTest_fst
noncomputable def H1944_cp1 : Nat × Nat := t7val% (fastRun pH1944 1 1121 (init pH1944) (init pH1944))
theorem H1944_seg1 : segOK pH1944 1 1121 (init pH1944) (init pH1944) H1944_cp1.1 H1944_cp1.2 = true := by
  decide +kernel
noncomputable def H1944_cp2 : Nat × Nat := t7val% (fastRun pH1944 1 1586 (init pH1944) (init pH1944))
theorem H1944_seg2 : segOK pH1944 1122 465 H1944_cp1.1 H1944_cp1.2 H1944_cp2.1 H1944_cp2.2 = true := by
  decide +kernel
theorem H1944_fin : (prmOK pH1944 1944 && ptTest pH1944 (runFrom pH1944 (fmask pH1944) (cmask pH1944) (hmask pH1944) 1587 357 (true, H1944_cp2.1, H1944_cp2.2)) 1944 972 true) = true := by
  decide +kernel
theorem H1944_ok : RunOK pH1944 1944 (runFrom pH1944 (fmask pH1944) (cmask pH1944) (hmask pH1944) 1587 357 (true, H1944_cp2.1, H1944_cp2.2)) ∧ ptTest pH1944 (runFrom pH1944 (fmask pH1944) (cmask pH1944) (hmask pH1944) 1587 357 (true, H1944_cp2.1, H1944_cp2.2)) 1944 972 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1944_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1944_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1944_fin) true) H1944_seg1) H1944_seg2) (by decide) rfl H1944_fin ptTest_fst
noncomputable def I1944_cp1 : Nat × Nat := t7val% (fastRun pI1944 1 1121 (init pI1944) (init pI1944))
theorem I1944_seg1 : segOK pI1944 1 1121 (init pI1944) (init pI1944) I1944_cp1.1 I1944_cp1.2 = true := by
  decide +kernel
noncomputable def I1944_cp2 : Nat × Nat := t7val% (fastRun pI1944 1 1586 (init pI1944) (init pI1944))
theorem I1944_seg2 : segOK pI1944 1122 465 I1944_cp1.1 I1944_cp1.2 I1944_cp2.1 I1944_cp2.2 = true := by
  decide +kernel
theorem I1944_fin : (prmOK pI1944 1944 && intTest pI1944 (runFrom pI1944 (fmask pI1944) (cmask pI1944) (hmask pI1944) 1587 357 (true, I1944_cp2.1, I1944_cp2.2)) 1944 22 true) = true := by
  decide +kernel
theorem I1944_ok : RunOK pI1944 1944 (runFrom pI1944 (fmask pI1944) (cmask pI1944) (hmask pI1944) 1587 357 (true, I1944_cp2.1, I1944_cp2.2)) ∧ intTest pI1944 (runFrom pI1944 (fmask pI1944) (cmask pI1944) (hmask pI1944) 1587 357 (true, I1944_cp2.1, I1944_cp2.2)) 1944 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1944_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1944_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1944_fin) true) I1944_seg1) I1944_seg2) (by decide) rfl I1944_fin intTest_fst
theorem link1944 : linkOK pL1944 pH1944 pI1944 = true := by decide +kernel
theorem cvx1944 : ConvexBetweenHumps 1944 :=
  cvx_of L1944_ok H1944_ok I1944_ok link1944 (by decide)
theorem cenlink1944 : cenLinkOK pI1944 1944 = true := by decide +kernel
theorem cen1944 : CenterUniqueMin 1944 ∧ DipHyp 1944 ∧ OnePointHyps 1944 :=
  cen_of L1944_ok H1944_ok I1944_ok link1944 cenlink1944

/-! ### `N = 1945` -/

def pL1945 : Prm := ⟨81, 38, 40, 1947, 11, 18446744073709551616, 100613909415931097, 100613909415931097⟩
def pH1945 : Prm := ⟨81, 38, 40, 1947, 11, 18446744073709551616, 100615008927558873, 100615008927558873⟩
def pI1945 : Prm := ⟨68, 34, 31, 1947, 11, 18446744073709551616, 100613909415931097, 100615008927558873⟩
noncomputable def L1945_cp1 : Nat × Nat := t7val% (fastRun pL1945 1 1122 (init pL1945) (init pL1945))
theorem L1945_seg1 : segOK pL1945 1 1122 (init pL1945) (init pL1945) L1945_cp1.1 L1945_cp1.2 = true := by
  decide +kernel
noncomputable def L1945_cp2 : Nat × Nat := t7val% (fastRun pL1945 1 1587 (init pL1945) (init pL1945))
theorem L1945_seg2 : segOK pL1945 1123 465 L1945_cp1.1 L1945_cp1.2 L1945_cp2.1 L1945_cp2.2 = true := by
  decide +kernel
theorem L1945_fin : (prmOK pL1945 1945 && ptTest pL1945 (runFrom pL1945 (fmask pL1945) (cmask pL1945) (hmask pL1945) 1588 357 (true, L1945_cp2.1, L1945_cp2.2)) 1945 973 false) = true := by
  decide +kernel
theorem L1945_ok : RunOK pL1945 1945 (runFrom pL1945 (fmask pL1945) (cmask pL1945) (hmask pL1945) 1588 357 (true, L1945_cp2.1, L1945_cp2.2)) ∧ ptTest pL1945 (runFrom pL1945 (fmask pL1945) (cmask pL1945) (hmask pL1945) 1588 357 (true, L1945_cp2.1, L1945_cp2.2)) 1945 973 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1945_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1945_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1945_fin) true) L1945_seg1) L1945_seg2) (by decide) rfl L1945_fin ptTest_fst
noncomputable def H1945_cp1 : Nat × Nat := t7val% (fastRun pH1945 1 1122 (init pH1945) (init pH1945))
theorem H1945_seg1 : segOK pH1945 1 1122 (init pH1945) (init pH1945) H1945_cp1.1 H1945_cp1.2 = true := by
  decide +kernel
noncomputable def H1945_cp2 : Nat × Nat := t7val% (fastRun pH1945 1 1587 (init pH1945) (init pH1945))
theorem H1945_seg2 : segOK pH1945 1123 465 H1945_cp1.1 H1945_cp1.2 H1945_cp2.1 H1945_cp2.2 = true := by
  decide +kernel
theorem H1945_fin : (prmOK pH1945 1945 && ptTest pH1945 (runFrom pH1945 (fmask pH1945) (cmask pH1945) (hmask pH1945) 1588 357 (true, H1945_cp2.1, H1945_cp2.2)) 1945 973 true) = true := by
  decide +kernel
theorem H1945_ok : RunOK pH1945 1945 (runFrom pH1945 (fmask pH1945) (cmask pH1945) (hmask pH1945) 1588 357 (true, H1945_cp2.1, H1945_cp2.2)) ∧ ptTest pH1945 (runFrom pH1945 (fmask pH1945) (cmask pH1945) (hmask pH1945) 1588 357 (true, H1945_cp2.1, H1945_cp2.2)) 1945 973 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1945_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1945_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1945_fin) true) H1945_seg1) H1945_seg2) (by decide) rfl H1945_fin ptTest_fst
noncomputable def I1945_cp1 : Nat × Nat := t7val% (fastRun pI1945 1 1122 (init pI1945) (init pI1945))
theorem I1945_seg1 : segOK pI1945 1 1122 (init pI1945) (init pI1945) I1945_cp1.1 I1945_cp1.2 = true := by
  decide +kernel
noncomputable def I1945_cp2 : Nat × Nat := t7val% (fastRun pI1945 1 1587 (init pI1945) (init pI1945))
theorem I1945_seg2 : segOK pI1945 1123 465 I1945_cp1.1 I1945_cp1.2 I1945_cp2.1 I1945_cp2.2 = true := by
  decide +kernel
theorem I1945_fin : (prmOK pI1945 1945 && intTest pI1945 (runFrom pI1945 (fmask pI1945) (cmask pI1945) (hmask pI1945) 1588 357 (true, I1945_cp2.1, I1945_cp2.2)) 1945 22 false) = true := by
  decide +kernel
theorem I1945_ok : RunOK pI1945 1945 (runFrom pI1945 (fmask pI1945) (cmask pI1945) (hmask pI1945) 1588 357 (true, I1945_cp2.1, I1945_cp2.2)) ∧ intTest pI1945 (runFrom pI1945 (fmask pI1945) (cmask pI1945) (hmask pI1945) 1588 357 (true, I1945_cp2.1, I1945_cp2.2)) 1945 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1945_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1945_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1945_fin) true) I1945_seg1) I1945_seg2) (by decide) rfl I1945_fin intTest_fst
theorem link1945 : linkOK pL1945 pH1945 pI1945 = true := by decide +kernel
theorem cvx1945 : ConvexBetweenHumps 1945 :=
  cvx_of L1945_ok H1945_ok I1945_ok link1945 (by decide)

/-! ### `N = 1946` -/

def pL1946 : Prm := ⟨81, 38, 40, 1948, 11, 18446744073709551616, 100571397816923380, 100571397816923380⟩
def pH1946 : Prm := ⟨81, 38, 40, 1948, 11, 18446744073709551616, 100572497328551156, 100572497328551156⟩
def pI1946 : Prm := ⟨68, 34, 31, 1948, 11, 18446744073709551616, 100571397816923380, 100572497328551156⟩
noncomputable def L1946_cp1 : Nat × Nat := t7val% (fastRun pL1946 1 1123 (init pL1946) (init pL1946))
theorem L1946_seg1 : segOK pL1946 1 1123 (init pL1946) (init pL1946) L1946_cp1.1 L1946_cp1.2 = true := by
  decide +kernel
noncomputable def L1946_cp2 : Nat × Nat := t7val% (fastRun pL1946 1 1588 (init pL1946) (init pL1946))
theorem L1946_seg2 : segOK pL1946 1124 465 L1946_cp1.1 L1946_cp1.2 L1946_cp2.1 L1946_cp2.2 = true := by
  decide +kernel
theorem L1946_fin : (prmOK pL1946 1946 && ptTest pL1946 (runFrom pL1946 (fmask pL1946) (cmask pL1946) (hmask pL1946) 1589 357 (true, L1946_cp2.1, L1946_cp2.2)) 1946 973 false) = true := by
  decide +kernel
theorem L1946_ok : RunOK pL1946 1946 (runFrom pL1946 (fmask pL1946) (cmask pL1946) (hmask pL1946) 1589 357 (true, L1946_cp2.1, L1946_cp2.2)) ∧ ptTest pL1946 (runFrom pL1946 (fmask pL1946) (cmask pL1946) (hmask pL1946) 1589 357 (true, L1946_cp2.1, L1946_cp2.2)) 1946 973 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1946_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1946_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1946_fin) true) L1946_seg1) L1946_seg2) (by decide) rfl L1946_fin ptTest_fst
noncomputable def H1946_cp1 : Nat × Nat := t7val% (fastRun pH1946 1 1123 (init pH1946) (init pH1946))
theorem H1946_seg1 : segOK pH1946 1 1123 (init pH1946) (init pH1946) H1946_cp1.1 H1946_cp1.2 = true := by
  decide +kernel
noncomputable def H1946_cp2 : Nat × Nat := t7val% (fastRun pH1946 1 1588 (init pH1946) (init pH1946))
theorem H1946_seg2 : segOK pH1946 1124 465 H1946_cp1.1 H1946_cp1.2 H1946_cp2.1 H1946_cp2.2 = true := by
  decide +kernel
theorem H1946_fin : (prmOK pH1946 1946 && ptTest pH1946 (runFrom pH1946 (fmask pH1946) (cmask pH1946) (hmask pH1946) 1589 357 (true, H1946_cp2.1, H1946_cp2.2)) 1946 973 true) = true := by
  decide +kernel
theorem H1946_ok : RunOK pH1946 1946 (runFrom pH1946 (fmask pH1946) (cmask pH1946) (hmask pH1946) 1589 357 (true, H1946_cp2.1, H1946_cp2.2)) ∧ ptTest pH1946 (runFrom pH1946 (fmask pH1946) (cmask pH1946) (hmask pH1946) 1589 357 (true, H1946_cp2.1, H1946_cp2.2)) 1946 973 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1946_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1946_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1946_fin) true) H1946_seg1) H1946_seg2) (by decide) rfl H1946_fin ptTest_fst
noncomputable def I1946_cp1 : Nat × Nat := t7val% (fastRun pI1946 1 1123 (init pI1946) (init pI1946))
theorem I1946_seg1 : segOK pI1946 1 1123 (init pI1946) (init pI1946) I1946_cp1.1 I1946_cp1.2 = true := by
  decide +kernel
noncomputable def I1946_cp2 : Nat × Nat := t7val% (fastRun pI1946 1 1588 (init pI1946) (init pI1946))
theorem I1946_seg2 : segOK pI1946 1124 465 I1946_cp1.1 I1946_cp1.2 I1946_cp2.1 I1946_cp2.2 = true := by
  decide +kernel
theorem I1946_fin : (prmOK pI1946 1946 && intTest pI1946 (runFrom pI1946 (fmask pI1946) (cmask pI1946) (hmask pI1946) 1589 357 (true, I1946_cp2.1, I1946_cp2.2)) 1946 22 true) = true := by
  decide +kernel
theorem I1946_ok : RunOK pI1946 1946 (runFrom pI1946 (fmask pI1946) (cmask pI1946) (hmask pI1946) 1589 357 (true, I1946_cp2.1, I1946_cp2.2)) ∧ intTest pI1946 (runFrom pI1946 (fmask pI1946) (cmask pI1946) (hmask pI1946) 1589 357 (true, I1946_cp2.1, I1946_cp2.2)) 1946 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1946_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1946_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1946_fin) true) I1946_seg1) I1946_seg2) (by decide) rfl I1946_fin intTest_fst
theorem link1946 : linkOK pL1946 pH1946 pI1946 = true := by decide +kernel
theorem cvx1946 : ConvexBetweenHumps 1946 :=
  cvx_of L1946_ok H1946_ok I1946_ok link1946 (by decide)
theorem cenlink1946 : cenLinkOK pI1946 1946 = true := by decide +kernel
theorem cen1946 : CenterUniqueMin 1946 ∧ DipHyp 1946 ∧ OnePointHyps 1946 :=
  cen_of L1946_ok H1946_ok I1946_ok link1946 cenlink1946

/-! ### `N = 1947` -/

def pL1947 : Prm := ⟨81, 38, 40, 1949, 11, 18446744073709551616, 100528909995344498, 100528909995344498⟩
def pH1947 : Prm := ⟨81, 38, 40, 1949, 11, 18446744073709551616, 100530009506972274, 100530009506972274⟩
def pI1947 : Prm := ⟨68, 34, 31, 1949, 11, 18446744073709551616, 100528909995344498, 100530009506972274⟩
noncomputable def L1947_cp1 : Nat × Nat := t7val% (fastRun pL1947 1 1123 (init pL1947) (init pL1947))
theorem L1947_seg1 : segOK pL1947 1 1123 (init pL1947) (init pL1947) L1947_cp1.1 L1947_cp1.2 = true := by
  decide +kernel
noncomputable def L1947_cp2 : Nat × Nat := t7val% (fastRun pL1947 1 1589 (init pL1947) (init pL1947))
theorem L1947_seg2 : segOK pL1947 1124 466 L1947_cp1.1 L1947_cp1.2 L1947_cp2.1 L1947_cp2.2 = true := by
  decide +kernel
theorem L1947_fin : (prmOK pL1947 1947 && ptTest pL1947 (runFrom pL1947 (fmask pL1947) (cmask pL1947) (hmask pL1947) 1590 357 (true, L1947_cp2.1, L1947_cp2.2)) 1947 974 false) = true := by
  decide +kernel
theorem L1947_ok : RunOK pL1947 1947 (runFrom pL1947 (fmask pL1947) (cmask pL1947) (hmask pL1947) 1590 357 (true, L1947_cp2.1, L1947_cp2.2)) ∧ ptTest pL1947 (runFrom pL1947 (fmask pL1947) (cmask pL1947) (hmask pL1947) 1590 357 (true, L1947_cp2.1, L1947_cp2.2)) 1947 974 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1947_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1947_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1947_fin) true) L1947_seg1) L1947_seg2) (by decide) rfl L1947_fin ptTest_fst
noncomputable def H1947_cp1 : Nat × Nat := t7val% (fastRun pH1947 1 1123 (init pH1947) (init pH1947))
theorem H1947_seg1 : segOK pH1947 1 1123 (init pH1947) (init pH1947) H1947_cp1.1 H1947_cp1.2 = true := by
  decide +kernel
noncomputable def H1947_cp2 : Nat × Nat := t7val% (fastRun pH1947 1 1589 (init pH1947) (init pH1947))
theorem H1947_seg2 : segOK pH1947 1124 466 H1947_cp1.1 H1947_cp1.2 H1947_cp2.1 H1947_cp2.2 = true := by
  decide +kernel
theorem H1947_fin : (prmOK pH1947 1947 && ptTest pH1947 (runFrom pH1947 (fmask pH1947) (cmask pH1947) (hmask pH1947) 1590 357 (true, H1947_cp2.1, H1947_cp2.2)) 1947 974 true) = true := by
  decide +kernel
theorem H1947_ok : RunOK pH1947 1947 (runFrom pH1947 (fmask pH1947) (cmask pH1947) (hmask pH1947) 1590 357 (true, H1947_cp2.1, H1947_cp2.2)) ∧ ptTest pH1947 (runFrom pH1947 (fmask pH1947) (cmask pH1947) (hmask pH1947) 1590 357 (true, H1947_cp2.1, H1947_cp2.2)) 1947 974 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1947_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1947_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1947_fin) true) H1947_seg1) H1947_seg2) (by decide) rfl H1947_fin ptTest_fst
noncomputable def I1947_cp1 : Nat × Nat := t7val% (fastRun pI1947 1 1123 (init pI1947) (init pI1947))
theorem I1947_seg1 : segOK pI1947 1 1123 (init pI1947) (init pI1947) I1947_cp1.1 I1947_cp1.2 = true := by
  decide +kernel
noncomputable def I1947_cp2 : Nat × Nat := t7val% (fastRun pI1947 1 1589 (init pI1947) (init pI1947))
theorem I1947_seg2 : segOK pI1947 1124 466 I1947_cp1.1 I1947_cp1.2 I1947_cp2.1 I1947_cp2.2 = true := by
  decide +kernel
theorem I1947_fin : (prmOK pI1947 1947 && intTest pI1947 (runFrom pI1947 (fmask pI1947) (cmask pI1947) (hmask pI1947) 1590 357 (true, I1947_cp2.1, I1947_cp2.2)) 1947 22 false) = true := by
  decide +kernel
theorem I1947_ok : RunOK pI1947 1947 (runFrom pI1947 (fmask pI1947) (cmask pI1947) (hmask pI1947) 1590 357 (true, I1947_cp2.1, I1947_cp2.2)) ∧ intTest pI1947 (runFrom pI1947 (fmask pI1947) (cmask pI1947) (hmask pI1947) 1590 357 (true, I1947_cp2.1, I1947_cp2.2)) 1947 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1947_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1947_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1947_fin) true) I1947_seg1) I1947_seg2) (by decide) rfl I1947_fin intTest_fst
theorem link1947 : linkOK pL1947 pH1947 pI1947 = true := by decide +kernel
theorem cvx1947 : ConvexBetweenHumps 1947 :=
  cvx_of L1947_ok H1947_ok I1947_ok link1947 (by decide)

/-! ### `N = 1948` -/

def pL1948 : Prm := ⟨81, 38, 40, 1950, 11, 18446744073709551616, 100486476226359761, 100486476226359761⟩
def pH1948 : Prm := ⟨81, 38, 40, 1950, 11, 18446744073709551616, 100487575737987537, 100487575737987537⟩
def pI1948 : Prm := ⟨68, 34, 31, 1950, 11, 18446744073709551616, 100486476226359761, 100487575737987537⟩
noncomputable def L1948_cp1 : Nat × Nat := t7val% (fastRun pL1948 1 1124 (init pL1948) (init pL1948))
theorem L1948_seg1 : segOK pL1948 1 1124 (init pL1948) (init pL1948) L1948_cp1.1 L1948_cp1.2 = true := by
  decide +kernel
noncomputable def L1948_cp2 : Nat × Nat := t7val% (fastRun pL1948 1 1590 (init pL1948) (init pL1948))
theorem L1948_seg2 : segOK pL1948 1125 466 L1948_cp1.1 L1948_cp1.2 L1948_cp2.1 L1948_cp2.2 = true := by
  decide +kernel
theorem L1948_fin : (prmOK pL1948 1948 && ptTest pL1948 (runFrom pL1948 (fmask pL1948) (cmask pL1948) (hmask pL1948) 1591 357 (true, L1948_cp2.1, L1948_cp2.2)) 1948 974 false) = true := by
  decide +kernel
theorem L1948_ok : RunOK pL1948 1948 (runFrom pL1948 (fmask pL1948) (cmask pL1948) (hmask pL1948) 1591 357 (true, L1948_cp2.1, L1948_cp2.2)) ∧ ptTest pL1948 (runFrom pL1948 (fmask pL1948) (cmask pL1948) (hmask pL1948) 1591 357 (true, L1948_cp2.1, L1948_cp2.2)) 1948 974 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1948_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1948_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1948_fin) true) L1948_seg1) L1948_seg2) (by decide) rfl L1948_fin ptTest_fst
noncomputable def H1948_cp1 : Nat × Nat := t7val% (fastRun pH1948 1 1124 (init pH1948) (init pH1948))
theorem H1948_seg1 : segOK pH1948 1 1124 (init pH1948) (init pH1948) H1948_cp1.1 H1948_cp1.2 = true := by
  decide +kernel
noncomputable def H1948_cp2 : Nat × Nat := t7val% (fastRun pH1948 1 1590 (init pH1948) (init pH1948))
theorem H1948_seg2 : segOK pH1948 1125 466 H1948_cp1.1 H1948_cp1.2 H1948_cp2.1 H1948_cp2.2 = true := by
  decide +kernel
theorem H1948_fin : (prmOK pH1948 1948 && ptTest pH1948 (runFrom pH1948 (fmask pH1948) (cmask pH1948) (hmask pH1948) 1591 357 (true, H1948_cp2.1, H1948_cp2.2)) 1948 974 true) = true := by
  decide +kernel
theorem H1948_ok : RunOK pH1948 1948 (runFrom pH1948 (fmask pH1948) (cmask pH1948) (hmask pH1948) 1591 357 (true, H1948_cp2.1, H1948_cp2.2)) ∧ ptTest pH1948 (runFrom pH1948 (fmask pH1948) (cmask pH1948) (hmask pH1948) 1591 357 (true, H1948_cp2.1, H1948_cp2.2)) 1948 974 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1948_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1948_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1948_fin) true) H1948_seg1) H1948_seg2) (by decide) rfl H1948_fin ptTest_fst
noncomputable def I1948_cp1 : Nat × Nat := t7val% (fastRun pI1948 1 1124 (init pI1948) (init pI1948))
theorem I1948_seg1 : segOK pI1948 1 1124 (init pI1948) (init pI1948) I1948_cp1.1 I1948_cp1.2 = true := by
  decide +kernel
noncomputable def I1948_cp2 : Nat × Nat := t7val% (fastRun pI1948 1 1590 (init pI1948) (init pI1948))
theorem I1948_seg2 : segOK pI1948 1125 466 I1948_cp1.1 I1948_cp1.2 I1948_cp2.1 I1948_cp2.2 = true := by
  decide +kernel
theorem I1948_fin : (prmOK pI1948 1948 && intTest pI1948 (runFrom pI1948 (fmask pI1948) (cmask pI1948) (hmask pI1948) 1591 357 (true, I1948_cp2.1, I1948_cp2.2)) 1948 22 true) = true := by
  decide +kernel
theorem I1948_ok : RunOK pI1948 1948 (runFrom pI1948 (fmask pI1948) (cmask pI1948) (hmask pI1948) 1591 357 (true, I1948_cp2.1, I1948_cp2.2)) ∧ intTest pI1948 (runFrom pI1948 (fmask pI1948) (cmask pI1948) (hmask pI1948) 1591 357 (true, I1948_cp2.1, I1948_cp2.2)) 1948 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1948_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1948_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1948_fin) true) I1948_seg1) I1948_seg2) (by decide) rfl I1948_fin intTest_fst
theorem link1948 : linkOK pL1948 pH1948 pI1948 = true := by decide +kernel
theorem cvx1948 : ConvexBetweenHumps 1948 :=
  cvx_of L1948_ok H1948_ok I1948_ok link1948 (by decide)
theorem cenlink1948 : cenLinkOK pI1948 1948 = true := by decide +kernel
theorem cen1948 : CenterUniqueMin 1948 ∧ DipHyp 1948 ∧ OnePointHyps 1948 :=
  cen_of L1948_ok H1948_ok I1948_ok link1948 cenlink1948

/-! ### `N = 1949` -/

def pL1949 : Prm := ⟨81, 38, 40, 1951, 11, 18446744073709551616, 100444066172011142, 100444066172011142⟩
def pH1949 : Prm := ⟨81, 38, 40, 1951, 11, 18446744073709551616, 100445165683638918, 100445165683638918⟩
def pI1949 : Prm := ⟨68, 34, 31, 1951, 11, 18446744073709551616, 100444066172011142, 100445165683638918⟩
noncomputable def L1949_cp1 : Nat × Nat := t7val% (fastRun pL1949 1 1124 (init pL1949) (init pL1949))
theorem L1949_seg1 : segOK pL1949 1 1124 (init pL1949) (init pL1949) L1949_cp1.1 L1949_cp1.2 = true := by
  decide +kernel
noncomputable def L1949_cp2 : Nat × Nat := t7val% (fastRun pL1949 1 1590 (init pL1949) (init pL1949))
theorem L1949_seg2 : segOK pL1949 1125 466 L1949_cp1.1 L1949_cp1.2 L1949_cp2.1 L1949_cp2.2 = true := by
  decide +kernel
theorem L1949_fin : (prmOK pL1949 1949 && ptTest pL1949 (runFrom pL1949 (fmask pL1949) (cmask pL1949) (hmask pL1949) 1591 358 (true, L1949_cp2.1, L1949_cp2.2)) 1949 975 false) = true := by
  decide +kernel
theorem L1949_ok : RunOK pL1949 1949 (runFrom pL1949 (fmask pL1949) (cmask pL1949) (hmask pL1949) 1591 358 (true, L1949_cp2.1, L1949_cp2.2)) ∧ ptTest pL1949 (runFrom pL1949 (fmask pL1949) (cmask pL1949) (hmask pL1949) 1591 358 (true, L1949_cp2.1, L1949_cp2.2)) 1949 975 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1949_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1949_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1949_fin) true) L1949_seg1) L1949_seg2) (by decide) rfl L1949_fin ptTest_fst
noncomputable def H1949_cp1 : Nat × Nat := t7val% (fastRun pH1949 1 1124 (init pH1949) (init pH1949))
theorem H1949_seg1 : segOK pH1949 1 1124 (init pH1949) (init pH1949) H1949_cp1.1 H1949_cp1.2 = true := by
  decide +kernel
noncomputable def H1949_cp2 : Nat × Nat := t7val% (fastRun pH1949 1 1590 (init pH1949) (init pH1949))
theorem H1949_seg2 : segOK pH1949 1125 466 H1949_cp1.1 H1949_cp1.2 H1949_cp2.1 H1949_cp2.2 = true := by
  decide +kernel
theorem H1949_fin : (prmOK pH1949 1949 && ptTest pH1949 (runFrom pH1949 (fmask pH1949) (cmask pH1949) (hmask pH1949) 1591 358 (true, H1949_cp2.1, H1949_cp2.2)) 1949 975 true) = true := by
  decide +kernel
theorem H1949_ok : RunOK pH1949 1949 (runFrom pH1949 (fmask pH1949) (cmask pH1949) (hmask pH1949) 1591 358 (true, H1949_cp2.1, H1949_cp2.2)) ∧ ptTest pH1949 (runFrom pH1949 (fmask pH1949) (cmask pH1949) (hmask pH1949) 1591 358 (true, H1949_cp2.1, H1949_cp2.2)) 1949 975 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1949_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1949_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1949_fin) true) H1949_seg1) H1949_seg2) (by decide) rfl H1949_fin ptTest_fst
noncomputable def I1949_cp1 : Nat × Nat := t7val% (fastRun pI1949 1 1124 (init pI1949) (init pI1949))
theorem I1949_seg1 : segOK pI1949 1 1124 (init pI1949) (init pI1949) I1949_cp1.1 I1949_cp1.2 = true := by
  decide +kernel
noncomputable def I1949_cp2 : Nat × Nat := t7val% (fastRun pI1949 1 1590 (init pI1949) (init pI1949))
theorem I1949_seg2 : segOK pI1949 1125 466 I1949_cp1.1 I1949_cp1.2 I1949_cp2.1 I1949_cp2.2 = true := by
  decide +kernel
theorem I1949_fin : (prmOK pI1949 1949 && intTest pI1949 (runFrom pI1949 (fmask pI1949) (cmask pI1949) (hmask pI1949) 1591 358 (true, I1949_cp2.1, I1949_cp2.2)) 1949 22 false) = true := by
  decide +kernel
theorem I1949_ok : RunOK pI1949 1949 (runFrom pI1949 (fmask pI1949) (cmask pI1949) (hmask pI1949) 1591 358 (true, I1949_cp2.1, I1949_cp2.2)) ∧ intTest pI1949 (runFrom pI1949 (fmask pI1949) (cmask pI1949) (hmask pI1949) 1591 358 (true, I1949_cp2.1, I1949_cp2.2)) 1949 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1949_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1949_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1949_fin) true) I1949_seg1) I1949_seg2) (by decide) rfl I1949_fin intTest_fst
theorem link1949 : linkOK pL1949 pH1949 pI1949 = true := by decide +kernel
theorem cvx1949 : ConvexBetweenHumps 1949 :=
  cvx_of L1949_ok H1949_ok I1949_ok link1949 (by decide)

/-! ### The range -/

theorem cvx_1940_1949 {N : ℕ} (h1 : 1940 ≤ N) (h2 : N ≤ 1949) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1944
  · by_cases h4 : N ≤ 1941
    · by_cases h6 : N ≤ 1940
      · obtain rfl : N = 1940 := by omega
        exact cvx1940
      · obtain rfl : N = 1941 := by omega
        exact cvx1941
    · by_cases h6 : N ≤ 1942
      · obtain rfl : N = 1942 := by omega
        exact cvx1942
      · by_cases h8 : N ≤ 1943
        · obtain rfl : N = 1943 := by omega
          exact cvx1943
        · obtain rfl : N = 1944 := by omega
          exact cvx1944
  · by_cases h4 : N ≤ 1946
    · by_cases h6 : N ≤ 1945
      · obtain rfl : N = 1945 := by omega
        exact cvx1945
      · obtain rfl : N = 1946 := by omega
        exact cvx1946
    · by_cases h6 : N ≤ 1947
      · obtain rfl : N = 1947 := by omega
        exact cvx1947
      · by_cases h8 : N ≤ 1948
        · obtain rfl : N = 1948 := by omega
          exact cvx1948
        · obtain rfl : N = 1949 := by omega
          exact cvx1949

theorem cen_1940_1949 {N : ℕ} (h1 : 1940 ≤ N) (h2 : N ≤ 1949) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1942
  · by_cases h4 : N ≤ 1940
    · obtain rfl : N = 1940 := by omega
      exact cen1940
    · obtain rfl : N = 1942 := by omega
      exact cen1942
  · by_cases h4 : N ≤ 1944
    · obtain rfl : N = 1944 := by omega
      exact cen1944
    · by_cases h6 : N ≤ 1946
      · obtain rfl : N = 1946 := by omega
        exact cen1946
      · obtain rfl : N = 1948 := by omega
        exact cen1948

end Kagey131.PaperD.T7
