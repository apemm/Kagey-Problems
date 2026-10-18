import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1930, …, 1939` (generated)

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

/-! ### `N = 1930` -/

def pL1930 : Prm := ⟨80, 37, 40, 1932, 11, 18446744073709551616, 101256417363948803, 101256417363948803⟩
def pH1930 : Prm := ⟨80, 37, 40, 1932, 11, 18446744073709551616, 101257516875576579, 101257516875576579⟩
def pI1930 : Prm := ⟨68, 34, 31, 1932, 11, 18446744073709551616, 101256417363948803, 101257516875576579⟩
noncomputable def L1930_cp1 : Nat × Nat := t7val% (fastRun pL1930 1 1113 (init pL1930) (init pL1930))
theorem L1930_seg1 : segOK pL1930 1 1113 (init pL1930) (init pL1930) L1930_cp1.1 L1930_cp1.2 = true := by
  decide +kernel
noncomputable def L1930_cp2 : Nat × Nat := t7val% (fastRun pL1930 1 1575 (init pL1930) (init pL1930))
theorem L1930_seg2 : segOK pL1930 1114 462 L1930_cp1.1 L1930_cp1.2 L1930_cp2.1 L1930_cp2.2 = true := by
  decide +kernel
theorem L1930_fin : (prmOK pL1930 1930 && ptTest pL1930 (runFrom pL1930 (fmask pL1930) (cmask pL1930) (hmask pL1930) 1576 354 (true, L1930_cp2.1, L1930_cp2.2)) 1930 965 false) = true := by
  decide +kernel
theorem L1930_ok : RunOK pL1930 1930 (runFrom pL1930 (fmask pL1930) (cmask pL1930) (hmask pL1930) 1576 354 (true, L1930_cp2.1, L1930_cp2.2)) ∧ ptTest pL1930 (runFrom pL1930 (fmask pL1930) (cmask pL1930) (hmask pL1930) 1576 354 (true, L1930_cp2.1, L1930_cp2.2)) 1930 965 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1930_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1930_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1930_fin) true) L1930_seg1) L1930_seg2) (by decide) rfl L1930_fin ptTest_fst
noncomputable def H1930_cp1 : Nat × Nat := t7val% (fastRun pH1930 1 1113 (init pH1930) (init pH1930))
theorem H1930_seg1 : segOK pH1930 1 1113 (init pH1930) (init pH1930) H1930_cp1.1 H1930_cp1.2 = true := by
  decide +kernel
noncomputable def H1930_cp2 : Nat × Nat := t7val% (fastRun pH1930 1 1575 (init pH1930) (init pH1930))
theorem H1930_seg2 : segOK pH1930 1114 462 H1930_cp1.1 H1930_cp1.2 H1930_cp2.1 H1930_cp2.2 = true := by
  decide +kernel
theorem H1930_fin : (prmOK pH1930 1930 && ptTest pH1930 (runFrom pH1930 (fmask pH1930) (cmask pH1930) (hmask pH1930) 1576 354 (true, H1930_cp2.1, H1930_cp2.2)) 1930 965 true) = true := by
  decide +kernel
theorem H1930_ok : RunOK pH1930 1930 (runFrom pH1930 (fmask pH1930) (cmask pH1930) (hmask pH1930) 1576 354 (true, H1930_cp2.1, H1930_cp2.2)) ∧ ptTest pH1930 (runFrom pH1930 (fmask pH1930) (cmask pH1930) (hmask pH1930) 1576 354 (true, H1930_cp2.1, H1930_cp2.2)) 1930 965 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1930_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1930_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1930_fin) true) H1930_seg1) H1930_seg2) (by decide) rfl H1930_fin ptTest_fst
noncomputable def I1930_cp1 : Nat × Nat := t7val% (fastRun pI1930 1 1113 (init pI1930) (init pI1930))
theorem I1930_seg1 : segOK pI1930 1 1113 (init pI1930) (init pI1930) I1930_cp1.1 I1930_cp1.2 = true := by
  decide +kernel
noncomputable def I1930_cp2 : Nat × Nat := t7val% (fastRun pI1930 1 1575 (init pI1930) (init pI1930))
theorem I1930_seg2 : segOK pI1930 1114 462 I1930_cp1.1 I1930_cp1.2 I1930_cp2.1 I1930_cp2.2 = true := by
  decide +kernel
theorem I1930_fin : (prmOK pI1930 1930 && intTest pI1930 (runFrom pI1930 (fmask pI1930) (cmask pI1930) (hmask pI1930) 1576 354 (true, I1930_cp2.1, I1930_cp2.2)) 1930 22 true) = true := by
  decide +kernel
theorem I1930_ok : RunOK pI1930 1930 (runFrom pI1930 (fmask pI1930) (cmask pI1930) (hmask pI1930) 1576 354 (true, I1930_cp2.1, I1930_cp2.2)) ∧ intTest pI1930 (runFrom pI1930 (fmask pI1930) (cmask pI1930) (hmask pI1930) 1576 354 (true, I1930_cp2.1, I1930_cp2.2)) 1930 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1930_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1930_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1930_fin) true) I1930_seg1) I1930_seg2) (by decide) rfl I1930_fin intTest_fst
theorem link1930 : linkOK pL1930 pH1930 pI1930 = true := by decide +kernel
theorem cvx1930 : ConvexBetweenHumps 1930 :=
  cvx_of L1930_ok H1930_ok I1930_ok link1930 (by decide)
theorem cenlink1930 : cenLinkOK pI1930 1930 = true := by decide +kernel
theorem cen1930 : CenterUniqueMin 1930 ∧ DipHyp 1930 ∧ OnePointHyps 1930 :=
  cen_of L1930_ok H1930_ok I1930_ok link1930 cenlink1930

/-! ### `N = 1931` -/

def pL1931 : Prm := ⟨80, 37, 40, 1933, 11, 18446744073709551616, 101213299388808770, 101213299388808770⟩
def pH1931 : Prm := ⟨81, 38, 40, 1933, 11, 18446744073709551616, 101214398900436546, 101214398900436546⟩
def pI1931 : Prm := ⟨68, 34, 31, 1933, 11, 18446744073709551616, 101213299388808770, 101214398900436546⟩
noncomputable def L1931_cp1 : Nat × Nat := t7val% (fastRun pL1931 1 1114 (init pL1931) (init pL1931))
theorem L1931_seg1 : segOK pL1931 1 1114 (init pL1931) (init pL1931) L1931_cp1.1 L1931_cp1.2 = true := by
  decide +kernel
noncomputable def L1931_cp2 : Nat × Nat := t7val% (fastRun pL1931 1 1576 (init pL1931) (init pL1931))
theorem L1931_seg2 : segOK pL1931 1115 462 L1931_cp1.1 L1931_cp1.2 L1931_cp2.1 L1931_cp2.2 = true := by
  decide +kernel
theorem L1931_fin : (prmOK pL1931 1931 && ptTest pL1931 (runFrom pL1931 (fmask pL1931) (cmask pL1931) (hmask pL1931) 1577 354 (true, L1931_cp2.1, L1931_cp2.2)) 1931 966 false) = true := by
  decide +kernel
theorem L1931_ok : RunOK pL1931 1931 (runFrom pL1931 (fmask pL1931) (cmask pL1931) (hmask pL1931) 1577 354 (true, L1931_cp2.1, L1931_cp2.2)) ∧ ptTest pL1931 (runFrom pL1931 (fmask pL1931) (cmask pL1931) (hmask pL1931) 1577 354 (true, L1931_cp2.1, L1931_cp2.2)) 1931 966 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1931_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1931_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1931_fin) true) L1931_seg1) L1931_seg2) (by decide) rfl L1931_fin ptTest_fst
noncomputable def H1931_cp1 : Nat × Nat := t7val% (fastRun pH1931 1 1114 (init pH1931) (init pH1931))
theorem H1931_seg1 : segOK pH1931 1 1114 (init pH1931) (init pH1931) H1931_cp1.1 H1931_cp1.2 = true := by
  decide +kernel
noncomputable def H1931_cp2 : Nat × Nat := t7val% (fastRun pH1931 1 1576 (init pH1931) (init pH1931))
theorem H1931_seg2 : segOK pH1931 1115 462 H1931_cp1.1 H1931_cp1.2 H1931_cp2.1 H1931_cp2.2 = true := by
  decide +kernel
theorem H1931_fin : (prmOK pH1931 1931 && ptTest pH1931 (runFrom pH1931 (fmask pH1931) (cmask pH1931) (hmask pH1931) 1577 354 (true, H1931_cp2.1, H1931_cp2.2)) 1931 966 true) = true := by
  decide +kernel
theorem H1931_ok : RunOK pH1931 1931 (runFrom pH1931 (fmask pH1931) (cmask pH1931) (hmask pH1931) 1577 354 (true, H1931_cp2.1, H1931_cp2.2)) ∧ ptTest pH1931 (runFrom pH1931 (fmask pH1931) (cmask pH1931) (hmask pH1931) 1577 354 (true, H1931_cp2.1, H1931_cp2.2)) 1931 966 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1931_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1931_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1931_fin) true) H1931_seg1) H1931_seg2) (by decide) rfl H1931_fin ptTest_fst
noncomputable def I1931_cp1 : Nat × Nat := t7val% (fastRun pI1931 1 1114 (init pI1931) (init pI1931))
theorem I1931_seg1 : segOK pI1931 1 1114 (init pI1931) (init pI1931) I1931_cp1.1 I1931_cp1.2 = true := by
  decide +kernel
noncomputable def I1931_cp2 : Nat × Nat := t7val% (fastRun pI1931 1 1576 (init pI1931) (init pI1931))
theorem I1931_seg2 : segOK pI1931 1115 462 I1931_cp1.1 I1931_cp1.2 I1931_cp2.1 I1931_cp2.2 = true := by
  decide +kernel
theorem I1931_fin : (prmOK pI1931 1931 && intTest pI1931 (runFrom pI1931 (fmask pI1931) (cmask pI1931) (hmask pI1931) 1577 354 (true, I1931_cp2.1, I1931_cp2.2)) 1931 22 false) = true := by
  decide +kernel
theorem I1931_ok : RunOK pI1931 1931 (runFrom pI1931 (fmask pI1931) (cmask pI1931) (hmask pI1931) 1577 354 (true, I1931_cp2.1, I1931_cp2.2)) ∧ intTest pI1931 (runFrom pI1931 (fmask pI1931) (cmask pI1931) (hmask pI1931) 1577 354 (true, I1931_cp2.1, I1931_cp2.2)) 1931 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1931_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1931_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1931_fin) true) I1931_seg1) I1931_seg2) (by decide) rfl I1931_fin intTest_fst
theorem link1931 : linkOK pL1931 pH1931 pI1931 = true := by decide +kernel
theorem cvx1931 : ConvexBetweenHumps 1931 :=
  cvx_of L1931_ok H1931_ok I1931_ok link1931 (by decide)

/-! ### `N = 1932` -/

def pL1932 : Prm := ⟨80, 37, 40, 1934, 11, 18446744073709551616, 101170236746817407, 101170236746817407⟩
def pH1932 : Prm := ⟨80, 37, 40, 1934, 11, 18446744073709551616, 101171336258445183, 101171336258445183⟩
def pI1932 : Prm := ⟨68, 34, 31, 1934, 11, 18446744073709551616, 101170236746817407, 101171336258445183⟩
noncomputable def L1932_cp1 : Nat × Nat := t7val% (fastRun pL1932 1 1114 (init pL1932) (init pL1932))
theorem L1932_seg1 : segOK pL1932 1 1114 (init pL1932) (init pL1932) L1932_cp1.1 L1932_cp1.2 = true := by
  decide +kernel
noncomputable def L1932_cp2 : Nat × Nat := t7val% (fastRun pL1932 1 1576 (init pL1932) (init pL1932))
theorem L1932_seg2 : segOK pL1932 1115 462 L1932_cp1.1 L1932_cp1.2 L1932_cp2.1 L1932_cp2.2 = true := by
  decide +kernel
theorem L1932_fin : (prmOK pL1932 1932 && ptTest pL1932 (runFrom pL1932 (fmask pL1932) (cmask pL1932) (hmask pL1932) 1577 355 (true, L1932_cp2.1, L1932_cp2.2)) 1932 966 false) = true := by
  decide +kernel
theorem L1932_ok : RunOK pL1932 1932 (runFrom pL1932 (fmask pL1932) (cmask pL1932) (hmask pL1932) 1577 355 (true, L1932_cp2.1, L1932_cp2.2)) ∧ ptTest pL1932 (runFrom pL1932 (fmask pL1932) (cmask pL1932) (hmask pL1932) 1577 355 (true, L1932_cp2.1, L1932_cp2.2)) 1932 966 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1932_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1932_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1932_fin) true) L1932_seg1) L1932_seg2) (by decide) rfl L1932_fin ptTest_fst
noncomputable def H1932_cp1 : Nat × Nat := t7val% (fastRun pH1932 1 1114 (init pH1932) (init pH1932))
theorem H1932_seg1 : segOK pH1932 1 1114 (init pH1932) (init pH1932) H1932_cp1.1 H1932_cp1.2 = true := by
  decide +kernel
noncomputable def H1932_cp2 : Nat × Nat := t7val% (fastRun pH1932 1 1576 (init pH1932) (init pH1932))
theorem H1932_seg2 : segOK pH1932 1115 462 H1932_cp1.1 H1932_cp1.2 H1932_cp2.1 H1932_cp2.2 = true := by
  decide +kernel
theorem H1932_fin : (prmOK pH1932 1932 && ptTest pH1932 (runFrom pH1932 (fmask pH1932) (cmask pH1932) (hmask pH1932) 1577 355 (true, H1932_cp2.1, H1932_cp2.2)) 1932 966 true) = true := by
  decide +kernel
theorem H1932_ok : RunOK pH1932 1932 (runFrom pH1932 (fmask pH1932) (cmask pH1932) (hmask pH1932) 1577 355 (true, H1932_cp2.1, H1932_cp2.2)) ∧ ptTest pH1932 (runFrom pH1932 (fmask pH1932) (cmask pH1932) (hmask pH1932) 1577 355 (true, H1932_cp2.1, H1932_cp2.2)) 1932 966 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1932_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1932_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1932_fin) true) H1932_seg1) H1932_seg2) (by decide) rfl H1932_fin ptTest_fst
noncomputable def I1932_cp1 : Nat × Nat := t7val% (fastRun pI1932 1 1114 (init pI1932) (init pI1932))
theorem I1932_seg1 : segOK pI1932 1 1114 (init pI1932) (init pI1932) I1932_cp1.1 I1932_cp1.2 = true := by
  decide +kernel
noncomputable def I1932_cp2 : Nat × Nat := t7val% (fastRun pI1932 1 1576 (init pI1932) (init pI1932))
theorem I1932_seg2 : segOK pI1932 1115 462 I1932_cp1.1 I1932_cp1.2 I1932_cp2.1 I1932_cp2.2 = true := by
  decide +kernel
theorem I1932_fin : (prmOK pI1932 1932 && intTest pI1932 (runFrom pI1932 (fmask pI1932) (cmask pI1932) (hmask pI1932) 1577 355 (true, I1932_cp2.1, I1932_cp2.2)) 1932 22 true) = true := by
  decide +kernel
theorem I1932_ok : RunOK pI1932 1932 (runFrom pI1932 (fmask pI1932) (cmask pI1932) (hmask pI1932) 1577 355 (true, I1932_cp2.1, I1932_cp2.2)) ∧ intTest pI1932 (runFrom pI1932 (fmask pI1932) (cmask pI1932) (hmask pI1932) 1577 355 (true, I1932_cp2.1, I1932_cp2.2)) 1932 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1932_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1932_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1932_fin) true) I1932_seg1) I1932_seg2) (by decide) rfl I1932_fin intTest_fst
theorem link1932 : linkOK pL1932 pH1932 pI1932 = true := by decide +kernel
theorem cvx1932 : ConvexBetweenHumps 1932 :=
  cvx_of L1932_ok H1932_ok I1932_ok link1932 (by decide)
theorem cenlink1932 : cenLinkOK pI1932 1932 = true := by decide +kernel
theorem cen1932 : CenterUniqueMin 1932 ∧ DipHyp 1932 ∧ OnePointHyps 1932 :=
  cen_of L1932_ok H1932_ok I1932_ok link1932 cenlink1932

/-! ### `N = 1933` -/

def pL1933 : Prm := ⟨80, 37, 40, 1935, 11, 18446744073709551616, 101127198328204920, 101127198328204920⟩
def pH1933 : Prm := ⟨81, 38, 40, 1935, 11, 18446744073709551616, 101128297839832696, 101128297839832696⟩
def pI1933 : Prm := ⟨68, 34, 31, 1935, 11, 18446744073709551616, 101127198328204920, 101128297839832696⟩
noncomputable def L1933_cp1 : Nat × Nat := t7val% (fastRun pL1933 1 1115 (init pL1933) (init pL1933))
theorem L1933_seg1 : segOK pL1933 1 1115 (init pL1933) (init pL1933) L1933_cp1.1 L1933_cp1.2 = true := by
  decide +kernel
noncomputable def L1933_cp2 : Nat × Nat := t7val% (fastRun pL1933 1 1577 (init pL1933) (init pL1933))
theorem L1933_seg2 : segOK pL1933 1116 462 L1933_cp1.1 L1933_cp1.2 L1933_cp2.1 L1933_cp2.2 = true := by
  decide +kernel
theorem L1933_fin : (prmOK pL1933 1933 && ptTest pL1933 (runFrom pL1933 (fmask pL1933) (cmask pL1933) (hmask pL1933) 1578 355 (true, L1933_cp2.1, L1933_cp2.2)) 1933 967 false) = true := by
  decide +kernel
theorem L1933_ok : RunOK pL1933 1933 (runFrom pL1933 (fmask pL1933) (cmask pL1933) (hmask pL1933) 1578 355 (true, L1933_cp2.1, L1933_cp2.2)) ∧ ptTest pL1933 (runFrom pL1933 (fmask pL1933) (cmask pL1933) (hmask pL1933) 1578 355 (true, L1933_cp2.1, L1933_cp2.2)) 1933 967 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1933_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1933_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1933_fin) true) L1933_seg1) L1933_seg2) (by decide) rfl L1933_fin ptTest_fst
noncomputable def H1933_cp1 : Nat × Nat := t7val% (fastRun pH1933 1 1115 (init pH1933) (init pH1933))
theorem H1933_seg1 : segOK pH1933 1 1115 (init pH1933) (init pH1933) H1933_cp1.1 H1933_cp1.2 = true := by
  decide +kernel
noncomputable def H1933_cp2 : Nat × Nat := t7val% (fastRun pH1933 1 1577 (init pH1933) (init pH1933))
theorem H1933_seg2 : segOK pH1933 1116 462 H1933_cp1.1 H1933_cp1.2 H1933_cp2.1 H1933_cp2.2 = true := by
  decide +kernel
theorem H1933_fin : (prmOK pH1933 1933 && ptTest pH1933 (runFrom pH1933 (fmask pH1933) (cmask pH1933) (hmask pH1933) 1578 355 (true, H1933_cp2.1, H1933_cp2.2)) 1933 967 true) = true := by
  decide +kernel
theorem H1933_ok : RunOK pH1933 1933 (runFrom pH1933 (fmask pH1933) (cmask pH1933) (hmask pH1933) 1578 355 (true, H1933_cp2.1, H1933_cp2.2)) ∧ ptTest pH1933 (runFrom pH1933 (fmask pH1933) (cmask pH1933) (hmask pH1933) 1578 355 (true, H1933_cp2.1, H1933_cp2.2)) 1933 967 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1933_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1933_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1933_fin) true) H1933_seg1) H1933_seg2) (by decide) rfl H1933_fin ptTest_fst
noncomputable def I1933_cp1 : Nat × Nat := t7val% (fastRun pI1933 1 1115 (init pI1933) (init pI1933))
theorem I1933_seg1 : segOK pI1933 1 1115 (init pI1933) (init pI1933) I1933_cp1.1 I1933_cp1.2 = true := by
  decide +kernel
noncomputable def I1933_cp2 : Nat × Nat := t7val% (fastRun pI1933 1 1577 (init pI1933) (init pI1933))
theorem I1933_seg2 : segOK pI1933 1116 462 I1933_cp1.1 I1933_cp1.2 I1933_cp2.1 I1933_cp2.2 = true := by
  decide +kernel
theorem I1933_fin : (prmOK pI1933 1933 && intTest pI1933 (runFrom pI1933 (fmask pI1933) (cmask pI1933) (hmask pI1933) 1578 355 (true, I1933_cp2.1, I1933_cp2.2)) 1933 22 false) = true := by
  decide +kernel
theorem I1933_ok : RunOK pI1933 1933 (runFrom pI1933 (fmask pI1933) (cmask pI1933) (hmask pI1933) 1578 355 (true, I1933_cp2.1, I1933_cp2.2)) ∧ intTest pI1933 (runFrom pI1933 (fmask pI1933) (cmask pI1933) (hmask pI1933) 1578 355 (true, I1933_cp2.1, I1933_cp2.2)) 1933 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1933_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1933_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1933_fin) true) I1933_seg1) I1933_seg2) (by decide) rfl I1933_fin intTest_fst
theorem link1933 : linkOK pL1933 pH1933 pI1933 = true := by decide +kernel
theorem cvx1933 : ConvexBetweenHumps 1933 :=
  cvx_of L1933_ok H1933_ok I1933_ok link1933 (by decide)

/-! ### `N = 1934` -/

def pL1934 : Prm := ⟨81, 38, 40, 1936, 11, 18446744073709551616, 101084215080465095, 101084215080465095⟩
def pH1934 : Prm := ⟨81, 38, 40, 1936, 11, 18446744073709551616, 101085314592092871, 101085314592092871⟩
def pI1934 : Prm := ⟨68, 34, 31, 1936, 11, 18446744073709551616, 101084215080465095, 101085314592092871⟩
noncomputable def L1934_cp1 : Nat × Nat := t7val% (fastRun pL1934 1 1116 (init pL1934) (init pL1934))
theorem L1934_seg1 : segOK pL1934 1 1116 (init pL1934) (init pL1934) L1934_cp1.1 L1934_cp1.2 = true := by
  decide +kernel
noncomputable def L1934_cp2 : Nat × Nat := t7val% (fastRun pL1934 1 1578 (init pL1934) (init pL1934))
theorem L1934_seg2 : segOK pL1934 1117 462 L1934_cp1.1 L1934_cp1.2 L1934_cp2.1 L1934_cp2.2 = true := by
  decide +kernel
theorem L1934_fin : (prmOK pL1934 1934 && ptTest pL1934 (runFrom pL1934 (fmask pL1934) (cmask pL1934) (hmask pL1934) 1579 355 (true, L1934_cp2.1, L1934_cp2.2)) 1934 967 false) = true := by
  decide +kernel
theorem L1934_ok : RunOK pL1934 1934 (runFrom pL1934 (fmask pL1934) (cmask pL1934) (hmask pL1934) 1579 355 (true, L1934_cp2.1, L1934_cp2.2)) ∧ ptTest pL1934 (runFrom pL1934 (fmask pL1934) (cmask pL1934) (hmask pL1934) 1579 355 (true, L1934_cp2.1, L1934_cp2.2)) 1934 967 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1934_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1934_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1934_fin) true) L1934_seg1) L1934_seg2) (by decide) rfl L1934_fin ptTest_fst
noncomputable def H1934_cp1 : Nat × Nat := t7val% (fastRun pH1934 1 1116 (init pH1934) (init pH1934))
theorem H1934_seg1 : segOK pH1934 1 1116 (init pH1934) (init pH1934) H1934_cp1.1 H1934_cp1.2 = true := by
  decide +kernel
noncomputable def H1934_cp2 : Nat × Nat := t7val% (fastRun pH1934 1 1578 (init pH1934) (init pH1934))
theorem H1934_seg2 : segOK pH1934 1117 462 H1934_cp1.1 H1934_cp1.2 H1934_cp2.1 H1934_cp2.2 = true := by
  decide +kernel
theorem H1934_fin : (prmOK pH1934 1934 && ptTest pH1934 (runFrom pH1934 (fmask pH1934) (cmask pH1934) (hmask pH1934) 1579 355 (true, H1934_cp2.1, H1934_cp2.2)) 1934 967 true) = true := by
  decide +kernel
theorem H1934_ok : RunOK pH1934 1934 (runFrom pH1934 (fmask pH1934) (cmask pH1934) (hmask pH1934) 1579 355 (true, H1934_cp2.1, H1934_cp2.2)) ∧ ptTest pH1934 (runFrom pH1934 (fmask pH1934) (cmask pH1934) (hmask pH1934) 1579 355 (true, H1934_cp2.1, H1934_cp2.2)) 1934 967 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1934_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1934_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1934_fin) true) H1934_seg1) H1934_seg2) (by decide) rfl H1934_fin ptTest_fst
noncomputable def I1934_cp1 : Nat × Nat := t7val% (fastRun pI1934 1 1116 (init pI1934) (init pI1934))
theorem I1934_seg1 : segOK pI1934 1 1116 (init pI1934) (init pI1934) I1934_cp1.1 I1934_cp1.2 = true := by
  decide +kernel
noncomputable def I1934_cp2 : Nat × Nat := t7val% (fastRun pI1934 1 1578 (init pI1934) (init pI1934))
theorem I1934_seg2 : segOK pI1934 1117 462 I1934_cp1.1 I1934_cp1.2 I1934_cp2.1 I1934_cp2.2 = true := by
  decide +kernel
theorem I1934_fin : (prmOK pI1934 1934 && intTest pI1934 (runFrom pI1934 (fmask pI1934) (cmask pI1934) (hmask pI1934) 1579 355 (true, I1934_cp2.1, I1934_cp2.2)) 1934 22 true) = true := by
  decide +kernel
theorem I1934_ok : RunOK pI1934 1934 (runFrom pI1934 (fmask pI1934) (cmask pI1934) (hmask pI1934) 1579 355 (true, I1934_cp2.1, I1934_cp2.2)) ∧ intTest pI1934 (runFrom pI1934 (fmask pI1934) (cmask pI1934) (hmask pI1934) 1579 355 (true, I1934_cp2.1, I1934_cp2.2)) 1934 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1934_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1934_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1934_fin) true) I1934_seg1) I1934_seg2) (by decide) rfl I1934_fin intTest_fst
theorem link1934 : linkOK pL1934 pH1934 pI1934 = true := by decide +kernel
theorem cvx1934 : ConvexBetweenHumps 1934 :=
  cvx_of L1934_ok H1934_ok I1934_ok link1934 (by decide)
theorem cenlink1934 : cenLinkOK pI1934 1934 = true := by decide +kernel
theorem cen1934 : CenterUniqueMin 1934 ∧ DipHyp 1934 ∧ OnePointHyps 1934 :=
  cen_of L1934_ok H1934_ok I1934_ok link1934 cenlink1934

/-! ### `N = 1935` -/

def pL1935 : Prm := ⟨80, 37, 40, 1937, 11, 18446744073709551616, 101041255991706561, 101041255991706561⟩
def pH1935 : Prm := ⟨81, 38, 40, 1937, 11, 18446744073709551616, 101042355503334337, 101042355503334337⟩
def pI1935 : Prm := ⟨68, 34, 31, 1937, 11, 18446744073709551616, 101041255991706561, 101042355503334337⟩
noncomputable def L1935_cp1 : Nat × Nat := t7val% (fastRun pL1935 1 1116 (init pL1935) (init pL1935))
theorem L1935_seg1 : segOK pL1935 1 1116 (init pL1935) (init pL1935) L1935_cp1.1 L1935_cp1.2 = true := by
  decide +kernel
noncomputable def L1935_cp2 : Nat × Nat := t7val% (fastRun pL1935 1 1579 (init pL1935) (init pL1935))
theorem L1935_seg2 : segOK pL1935 1117 463 L1935_cp1.1 L1935_cp1.2 L1935_cp2.1 L1935_cp2.2 = true := by
  decide +kernel
theorem L1935_fin : (prmOK pL1935 1935 && ptTest pL1935 (runFrom pL1935 (fmask pL1935) (cmask pL1935) (hmask pL1935) 1580 355 (true, L1935_cp2.1, L1935_cp2.2)) 1935 968 false) = true := by
  decide +kernel
theorem L1935_ok : RunOK pL1935 1935 (runFrom pL1935 (fmask pL1935) (cmask pL1935) (hmask pL1935) 1580 355 (true, L1935_cp2.1, L1935_cp2.2)) ∧ ptTest pL1935 (runFrom pL1935 (fmask pL1935) (cmask pL1935) (hmask pL1935) 1580 355 (true, L1935_cp2.1, L1935_cp2.2)) 1935 968 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1935_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1935_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1935_fin) true) L1935_seg1) L1935_seg2) (by decide) rfl L1935_fin ptTest_fst
noncomputable def H1935_cp1 : Nat × Nat := t7val% (fastRun pH1935 1 1116 (init pH1935) (init pH1935))
theorem H1935_seg1 : segOK pH1935 1 1116 (init pH1935) (init pH1935) H1935_cp1.1 H1935_cp1.2 = true := by
  decide +kernel
noncomputable def H1935_cp2 : Nat × Nat := t7val% (fastRun pH1935 1 1579 (init pH1935) (init pH1935))
theorem H1935_seg2 : segOK pH1935 1117 463 H1935_cp1.1 H1935_cp1.2 H1935_cp2.1 H1935_cp2.2 = true := by
  decide +kernel
theorem H1935_fin : (prmOK pH1935 1935 && ptTest pH1935 (runFrom pH1935 (fmask pH1935) (cmask pH1935) (hmask pH1935) 1580 355 (true, H1935_cp2.1, H1935_cp2.2)) 1935 968 true) = true := by
  decide +kernel
theorem H1935_ok : RunOK pH1935 1935 (runFrom pH1935 (fmask pH1935) (cmask pH1935) (hmask pH1935) 1580 355 (true, H1935_cp2.1, H1935_cp2.2)) ∧ ptTest pH1935 (runFrom pH1935 (fmask pH1935) (cmask pH1935) (hmask pH1935) 1580 355 (true, H1935_cp2.1, H1935_cp2.2)) 1935 968 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1935_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1935_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1935_fin) true) H1935_seg1) H1935_seg2) (by decide) rfl H1935_fin ptTest_fst
noncomputable def I1935_cp1 : Nat × Nat := t7val% (fastRun pI1935 1 1116 (init pI1935) (init pI1935))
theorem I1935_seg1 : segOK pI1935 1 1116 (init pI1935) (init pI1935) I1935_cp1.1 I1935_cp1.2 = true := by
  decide +kernel
noncomputable def I1935_cp2 : Nat × Nat := t7val% (fastRun pI1935 1 1579 (init pI1935) (init pI1935))
theorem I1935_seg2 : segOK pI1935 1117 463 I1935_cp1.1 I1935_cp1.2 I1935_cp2.1 I1935_cp2.2 = true := by
  decide +kernel
theorem I1935_fin : (prmOK pI1935 1935 && intTest pI1935 (runFrom pI1935 (fmask pI1935) (cmask pI1935) (hmask pI1935) 1580 355 (true, I1935_cp2.1, I1935_cp2.2)) 1935 22 false) = true := by
  decide +kernel
theorem I1935_ok : RunOK pI1935 1935 (runFrom pI1935 (fmask pI1935) (cmask pI1935) (hmask pI1935) 1580 355 (true, I1935_cp2.1, I1935_cp2.2)) ∧ intTest pI1935 (runFrom pI1935 (fmask pI1935) (cmask pI1935) (hmask pI1935) 1580 355 (true, I1935_cp2.1, I1935_cp2.2)) 1935 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1935_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1935_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1935_fin) true) I1935_seg1) I1935_seg2) (by decide) rfl I1935_fin intTest_fst
theorem link1935 : linkOK pL1935 pH1935 pI1935 = true := by decide +kernel
theorem cvx1935 : ConvexBetweenHumps 1935 :=
  cvx_of L1935_ok H1935_ok I1935_ok link1935 (by decide)

/-! ### `N = 1936` -/

def pL1936 : Prm := ⟨80, 37, 40, 1938, 11, 18446744073709551616, 100998351912171873, 100998351912171873⟩
def pH1936 : Prm := ⟨80, 37, 40, 1938, 11, 18446744073709551616, 100999451423799649, 100999451423799649⟩
def pI1936 : Prm := ⟨68, 34, 31, 1938, 11, 18446744073709551616, 100998351912171873, 100999451423799649⟩
noncomputable def L1936_cp1 : Nat × Nat := t7val% (fastRun pL1936 1 1117 (init pL1936) (init pL1936))
theorem L1936_seg1 : segOK pL1936 1 1117 (init pL1936) (init pL1936) L1936_cp1.1 L1936_cp1.2 = true := by
  decide +kernel
noncomputable def L1936_cp2 : Nat × Nat := t7val% (fastRun pL1936 1 1580 (init pL1936) (init pL1936))
theorem L1936_seg2 : segOK pL1936 1118 463 L1936_cp1.1 L1936_cp1.2 L1936_cp2.1 L1936_cp2.2 = true := by
  decide +kernel
theorem L1936_fin : (prmOK pL1936 1936 && ptTest pL1936 (runFrom pL1936 (fmask pL1936) (cmask pL1936) (hmask pL1936) 1581 355 (true, L1936_cp2.1, L1936_cp2.2)) 1936 968 false) = true := by
  decide +kernel
theorem L1936_ok : RunOK pL1936 1936 (runFrom pL1936 (fmask pL1936) (cmask pL1936) (hmask pL1936) 1581 355 (true, L1936_cp2.1, L1936_cp2.2)) ∧ ptTest pL1936 (runFrom pL1936 (fmask pL1936) (cmask pL1936) (hmask pL1936) 1581 355 (true, L1936_cp2.1, L1936_cp2.2)) 1936 968 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1936_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1936_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1936_fin) true) L1936_seg1) L1936_seg2) (by decide) rfl L1936_fin ptTest_fst
noncomputable def H1936_cp1 : Nat × Nat := t7val% (fastRun pH1936 1 1117 (init pH1936) (init pH1936))
theorem H1936_seg1 : segOK pH1936 1 1117 (init pH1936) (init pH1936) H1936_cp1.1 H1936_cp1.2 = true := by
  decide +kernel
noncomputable def H1936_cp2 : Nat × Nat := t7val% (fastRun pH1936 1 1580 (init pH1936) (init pH1936))
theorem H1936_seg2 : segOK pH1936 1118 463 H1936_cp1.1 H1936_cp1.2 H1936_cp2.1 H1936_cp2.2 = true := by
  decide +kernel
theorem H1936_fin : (prmOK pH1936 1936 && ptTest pH1936 (runFrom pH1936 (fmask pH1936) (cmask pH1936) (hmask pH1936) 1581 355 (true, H1936_cp2.1, H1936_cp2.2)) 1936 968 true) = true := by
  decide +kernel
theorem H1936_ok : RunOK pH1936 1936 (runFrom pH1936 (fmask pH1936) (cmask pH1936) (hmask pH1936) 1581 355 (true, H1936_cp2.1, H1936_cp2.2)) ∧ ptTest pH1936 (runFrom pH1936 (fmask pH1936) (cmask pH1936) (hmask pH1936) 1581 355 (true, H1936_cp2.1, H1936_cp2.2)) 1936 968 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1936_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1936_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1936_fin) true) H1936_seg1) H1936_seg2) (by decide) rfl H1936_fin ptTest_fst
noncomputable def I1936_cp1 : Nat × Nat := t7val% (fastRun pI1936 1 1117 (init pI1936) (init pI1936))
theorem I1936_seg1 : segOK pI1936 1 1117 (init pI1936) (init pI1936) I1936_cp1.1 I1936_cp1.2 = true := by
  decide +kernel
noncomputable def I1936_cp2 : Nat × Nat := t7val% (fastRun pI1936 1 1580 (init pI1936) (init pI1936))
theorem I1936_seg2 : segOK pI1936 1118 463 I1936_cp1.1 I1936_cp1.2 I1936_cp2.1 I1936_cp2.2 = true := by
  decide +kernel
theorem I1936_fin : (prmOK pI1936 1936 && intTest pI1936 (runFrom pI1936 (fmask pI1936) (cmask pI1936) (hmask pI1936) 1581 355 (true, I1936_cp2.1, I1936_cp2.2)) 1936 22 true) = true := by
  decide +kernel
theorem I1936_ok : RunOK pI1936 1936 (runFrom pI1936 (fmask pI1936) (cmask pI1936) (hmask pI1936) 1581 355 (true, I1936_cp2.1, I1936_cp2.2)) ∧ intTest pI1936 (runFrom pI1936 (fmask pI1936) (cmask pI1936) (hmask pI1936) 1581 355 (true, I1936_cp2.1, I1936_cp2.2)) 1936 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1936_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1936_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1936_fin) true) I1936_seg1) I1936_seg2) (by decide) rfl I1936_fin intTest_fst
theorem link1936 : linkOK pL1936 pH1936 pI1936 = true := by decide +kernel
theorem cvx1936 : ConvexBetweenHumps 1936 :=
  cvx_of L1936_ok H1936_ok I1936_ok link1936 (by decide)
theorem cenlink1936 : cenLinkOK pI1936 1936 = true := by decide +kernel
theorem cen1936 : CenterUniqueMin 1936 ∧ DipHyp 1936 ∧ OnePointHyps 1936 :=
  cen_of L1936_ok H1936_ok I1936_ok link1936 cenlink1936

/-! ### `N = 1937` -/

def pL1937 : Prm := ⟨81, 38, 40, 1939, 11, 18446744073709551616, 100955471927442252, 100955471927442252⟩
def pH1937 : Prm := ⟨81, 38, 40, 1939, 11, 18446744073709551616, 100956571439070028, 100956571439070028⟩
def pI1937 : Prm := ⟨68, 34, 31, 1939, 11, 18446744073709551616, 100955471927442252, 100956571439070028⟩
noncomputable def L1937_cp1 : Nat × Nat := t7val% (fastRun pL1937 1 1117 (init pL1937) (init pL1937))
theorem L1937_seg1 : segOK pL1937 1 1117 (init pL1937) (init pL1937) L1937_cp1.1 L1937_cp1.2 = true := by
  decide +kernel
noncomputable def L1937_cp2 : Nat × Nat := t7val% (fastRun pL1937 1 1581 (init pL1937) (init pL1937))
theorem L1937_seg2 : segOK pL1937 1118 464 L1937_cp1.1 L1937_cp1.2 L1937_cp2.1 L1937_cp2.2 = true := by
  decide +kernel
theorem L1937_fin : (prmOK pL1937 1937 && ptTest pL1937 (runFrom pL1937 (fmask pL1937) (cmask pL1937) (hmask pL1937) 1582 355 (true, L1937_cp2.1, L1937_cp2.2)) 1937 969 false) = true := by
  decide +kernel
theorem L1937_ok : RunOK pL1937 1937 (runFrom pL1937 (fmask pL1937) (cmask pL1937) (hmask pL1937) 1582 355 (true, L1937_cp2.1, L1937_cp2.2)) ∧ ptTest pL1937 (runFrom pL1937 (fmask pL1937) (cmask pL1937) (hmask pL1937) 1582 355 (true, L1937_cp2.1, L1937_cp2.2)) 1937 969 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1937_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1937_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1937_fin) true) L1937_seg1) L1937_seg2) (by decide) rfl L1937_fin ptTest_fst
noncomputable def H1937_cp1 : Nat × Nat := t7val% (fastRun pH1937 1 1117 (init pH1937) (init pH1937))
theorem H1937_seg1 : segOK pH1937 1 1117 (init pH1937) (init pH1937) H1937_cp1.1 H1937_cp1.2 = true := by
  decide +kernel
noncomputable def H1937_cp2 : Nat × Nat := t7val% (fastRun pH1937 1 1581 (init pH1937) (init pH1937))
theorem H1937_seg2 : segOK pH1937 1118 464 H1937_cp1.1 H1937_cp1.2 H1937_cp2.1 H1937_cp2.2 = true := by
  decide +kernel
theorem H1937_fin : (prmOK pH1937 1937 && ptTest pH1937 (runFrom pH1937 (fmask pH1937) (cmask pH1937) (hmask pH1937) 1582 355 (true, H1937_cp2.1, H1937_cp2.2)) 1937 969 true) = true := by
  decide +kernel
theorem H1937_ok : RunOK pH1937 1937 (runFrom pH1937 (fmask pH1937) (cmask pH1937) (hmask pH1937) 1582 355 (true, H1937_cp2.1, H1937_cp2.2)) ∧ ptTest pH1937 (runFrom pH1937 (fmask pH1937) (cmask pH1937) (hmask pH1937) 1582 355 (true, H1937_cp2.1, H1937_cp2.2)) 1937 969 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1937_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1937_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1937_fin) true) H1937_seg1) H1937_seg2) (by decide) rfl H1937_fin ptTest_fst
noncomputable def I1937_cp1 : Nat × Nat := t7val% (fastRun pI1937 1 1117 (init pI1937) (init pI1937))
theorem I1937_seg1 : segOK pI1937 1 1117 (init pI1937) (init pI1937) I1937_cp1.1 I1937_cp1.2 = true := by
  decide +kernel
noncomputable def I1937_cp2 : Nat × Nat := t7val% (fastRun pI1937 1 1581 (init pI1937) (init pI1937))
theorem I1937_seg2 : segOK pI1937 1118 464 I1937_cp1.1 I1937_cp1.2 I1937_cp2.1 I1937_cp2.2 = true := by
  decide +kernel
theorem I1937_fin : (prmOK pI1937 1937 && intTest pI1937 (runFrom pI1937 (fmask pI1937) (cmask pI1937) (hmask pI1937) 1582 355 (true, I1937_cp2.1, I1937_cp2.2)) 1937 22 false) = true := by
  decide +kernel
theorem I1937_ok : RunOK pI1937 1937 (runFrom pI1937 (fmask pI1937) (cmask pI1937) (hmask pI1937) 1582 355 (true, I1937_cp2.1, I1937_cp2.2)) ∧ intTest pI1937 (runFrom pI1937 (fmask pI1937) (cmask pI1937) (hmask pI1937) 1582 355 (true, I1937_cp2.1, I1937_cp2.2)) 1937 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1937_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1937_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1937_fin) true) I1937_seg1) I1937_seg2) (by decide) rfl I1937_fin intTest_fst
theorem link1937 : linkOK pL1937 pH1937 pI1937 = true := by decide +kernel
theorem cvx1937 : ConvexBetweenHumps 1937 :=
  cvx_of L1937_ok H1937_ok I1937_ok link1937 (by decide)

/-! ### `N = 1938` -/

def pL1938 : Prm := ⟨81, 38, 40, 1940, 11, 18446744073709551616, 100912646790914848, 100912646790914848⟩
def pH1938 : Prm := ⟨80, 37, 40, 1940, 11, 18446744073709551616, 100913746302542624, 100913746302542624⟩
def pI1938 : Prm := ⟨68, 34, 31, 1940, 11, 18446744073709551616, 100912646790914848, 100913746302542624⟩
noncomputable def L1938_cp1 : Nat × Nat := t7val% (fastRun pL1938 1 1118 (init pL1938) (init pL1938))
theorem L1938_seg1 : segOK pL1938 1 1118 (init pL1938) (init pL1938) L1938_cp1.1 L1938_cp1.2 = true := by
  decide +kernel
noncomputable def L1938_cp2 : Nat × Nat := t7val% (fastRun pL1938 1 1581 (init pL1938) (init pL1938))
theorem L1938_seg2 : segOK pL1938 1119 463 L1938_cp1.1 L1938_cp1.2 L1938_cp2.1 L1938_cp2.2 = true := by
  decide +kernel
theorem L1938_fin : (prmOK pL1938 1938 && ptTest pL1938 (runFrom pL1938 (fmask pL1938) (cmask pL1938) (hmask pL1938) 1582 356 (true, L1938_cp2.1, L1938_cp2.2)) 1938 969 false) = true := by
  decide +kernel
theorem L1938_ok : RunOK pL1938 1938 (runFrom pL1938 (fmask pL1938) (cmask pL1938) (hmask pL1938) 1582 356 (true, L1938_cp2.1, L1938_cp2.2)) ∧ ptTest pL1938 (runFrom pL1938 (fmask pL1938) (cmask pL1938) (hmask pL1938) 1582 356 (true, L1938_cp2.1, L1938_cp2.2)) 1938 969 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1938_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1938_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1938_fin) true) L1938_seg1) L1938_seg2) (by decide) rfl L1938_fin ptTest_fst
noncomputable def H1938_cp1 : Nat × Nat := t7val% (fastRun pH1938 1 1118 (init pH1938) (init pH1938))
theorem H1938_seg1 : segOK pH1938 1 1118 (init pH1938) (init pH1938) H1938_cp1.1 H1938_cp1.2 = true := by
  decide +kernel
noncomputable def H1938_cp2 : Nat × Nat := t7val% (fastRun pH1938 1 1581 (init pH1938) (init pH1938))
theorem H1938_seg2 : segOK pH1938 1119 463 H1938_cp1.1 H1938_cp1.2 H1938_cp2.1 H1938_cp2.2 = true := by
  decide +kernel
theorem H1938_fin : (prmOK pH1938 1938 && ptTest pH1938 (runFrom pH1938 (fmask pH1938) (cmask pH1938) (hmask pH1938) 1582 356 (true, H1938_cp2.1, H1938_cp2.2)) 1938 969 true) = true := by
  decide +kernel
theorem H1938_ok : RunOK pH1938 1938 (runFrom pH1938 (fmask pH1938) (cmask pH1938) (hmask pH1938) 1582 356 (true, H1938_cp2.1, H1938_cp2.2)) ∧ ptTest pH1938 (runFrom pH1938 (fmask pH1938) (cmask pH1938) (hmask pH1938) 1582 356 (true, H1938_cp2.1, H1938_cp2.2)) 1938 969 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1938_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1938_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1938_fin) true) H1938_seg1) H1938_seg2) (by decide) rfl H1938_fin ptTest_fst
noncomputable def I1938_cp1 : Nat × Nat := t7val% (fastRun pI1938 1 1118 (init pI1938) (init pI1938))
theorem I1938_seg1 : segOK pI1938 1 1118 (init pI1938) (init pI1938) I1938_cp1.1 I1938_cp1.2 = true := by
  decide +kernel
noncomputable def I1938_cp2 : Nat × Nat := t7val% (fastRun pI1938 1 1581 (init pI1938) (init pI1938))
theorem I1938_seg2 : segOK pI1938 1119 463 I1938_cp1.1 I1938_cp1.2 I1938_cp2.1 I1938_cp2.2 = true := by
  decide +kernel
theorem I1938_fin : (prmOK pI1938 1938 && intTest pI1938 (runFrom pI1938 (fmask pI1938) (cmask pI1938) (hmask pI1938) 1582 356 (true, I1938_cp2.1, I1938_cp2.2)) 1938 22 true) = true := by
  decide +kernel
theorem I1938_ok : RunOK pI1938 1938 (runFrom pI1938 (fmask pI1938) (cmask pI1938) (hmask pI1938) 1582 356 (true, I1938_cp2.1, I1938_cp2.2)) ∧ intTest pI1938 (runFrom pI1938 (fmask pI1938) (cmask pI1938) (hmask pI1938) 1582 356 (true, I1938_cp2.1, I1938_cp2.2)) 1938 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1938_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1938_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1938_fin) true) I1938_seg1) I1938_seg2) (by decide) rfl I1938_fin intTest_fst
theorem link1938 : linkOK pL1938 pH1938 pI1938 = true := by decide +kernel
theorem cvx1938 : ConvexBetweenHumps 1938 :=
  cvx_of L1938_ok H1938_ok I1938_ok link1938 (by decide)
theorem cenlink1938 : cenLinkOK pI1938 1938 = true := by decide +kernel
theorem cen1938 : CenterUniqueMin 1938 ∧ DipHyp 1938 ∧ OnePointHyps 1938 :=
  cen_of L1938_ok H1938_ok I1938_ok link1938 cenlink1938

/-! ### `N = 1939` -/

def pL1939 : Prm := ⟨80, 37, 40, 1941, 11, 18446744073709551616, 100869845685274543, 100869845685274543⟩
def pH1939 : Prm := ⟨80, 37, 40, 1941, 11, 18446744073709551616, 100870945196902319, 100870945196902319⟩
def pI1939 : Prm := ⟨68, 34, 31, 1941, 11, 18446744073709551616, 100869845685274543, 100870945196902319⟩
noncomputable def L1939_cp1 : Nat × Nat := t7val% (fastRun pL1939 1 1118 (init pL1939) (init pL1939))
theorem L1939_seg1 : segOK pL1939 1 1118 (init pL1939) (init pL1939) L1939_cp1.1 L1939_cp1.2 = true := by
  decide +kernel
noncomputable def L1939_cp2 : Nat × Nat := t7val% (fastRun pL1939 1 1582 (init pL1939) (init pL1939))
theorem L1939_seg2 : segOK pL1939 1119 464 L1939_cp1.1 L1939_cp1.2 L1939_cp2.1 L1939_cp2.2 = true := by
  decide +kernel
theorem L1939_fin : (prmOK pL1939 1939 && ptTest pL1939 (runFrom pL1939 (fmask pL1939) (cmask pL1939) (hmask pL1939) 1583 356 (true, L1939_cp2.1, L1939_cp2.2)) 1939 970 false) = true := by
  decide +kernel
theorem L1939_ok : RunOK pL1939 1939 (runFrom pL1939 (fmask pL1939) (cmask pL1939) (hmask pL1939) 1583 356 (true, L1939_cp2.1, L1939_cp2.2)) ∧ ptTest pL1939 (runFrom pL1939 (fmask pL1939) (cmask pL1939) (hmask pL1939) 1583 356 (true, L1939_cp2.1, L1939_cp2.2)) 1939 970 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1939_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1939_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1939_fin) true) L1939_seg1) L1939_seg2) (by decide) rfl L1939_fin ptTest_fst
noncomputable def H1939_cp1 : Nat × Nat := t7val% (fastRun pH1939 1 1118 (init pH1939) (init pH1939))
theorem H1939_seg1 : segOK pH1939 1 1118 (init pH1939) (init pH1939) H1939_cp1.1 H1939_cp1.2 = true := by
  decide +kernel
noncomputable def H1939_cp2 : Nat × Nat := t7val% (fastRun pH1939 1 1582 (init pH1939) (init pH1939))
theorem H1939_seg2 : segOK pH1939 1119 464 H1939_cp1.1 H1939_cp1.2 H1939_cp2.1 H1939_cp2.2 = true := by
  decide +kernel
theorem H1939_fin : (prmOK pH1939 1939 && ptTest pH1939 (runFrom pH1939 (fmask pH1939) (cmask pH1939) (hmask pH1939) 1583 356 (true, H1939_cp2.1, H1939_cp2.2)) 1939 970 true) = true := by
  decide +kernel
theorem H1939_ok : RunOK pH1939 1939 (runFrom pH1939 (fmask pH1939) (cmask pH1939) (hmask pH1939) 1583 356 (true, H1939_cp2.1, H1939_cp2.2)) ∧ ptTest pH1939 (runFrom pH1939 (fmask pH1939) (cmask pH1939) (hmask pH1939) 1583 356 (true, H1939_cp2.1, H1939_cp2.2)) 1939 970 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1939_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1939_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1939_fin) true) H1939_seg1) H1939_seg2) (by decide) rfl H1939_fin ptTest_fst
noncomputable def I1939_cp1 : Nat × Nat := t7val% (fastRun pI1939 1 1118 (init pI1939) (init pI1939))
theorem I1939_seg1 : segOK pI1939 1 1118 (init pI1939) (init pI1939) I1939_cp1.1 I1939_cp1.2 = true := by
  decide +kernel
noncomputable def I1939_cp2 : Nat × Nat := t7val% (fastRun pI1939 1 1582 (init pI1939) (init pI1939))
theorem I1939_seg2 : segOK pI1939 1119 464 I1939_cp1.1 I1939_cp1.2 I1939_cp2.1 I1939_cp2.2 = true := by
  decide +kernel
theorem I1939_fin : (prmOK pI1939 1939 && intTest pI1939 (runFrom pI1939 (fmask pI1939) (cmask pI1939) (hmask pI1939) 1583 356 (true, I1939_cp2.1, I1939_cp2.2)) 1939 22 false) = true := by
  decide +kernel
theorem I1939_ok : RunOK pI1939 1939 (runFrom pI1939 (fmask pI1939) (cmask pI1939) (hmask pI1939) 1583 356 (true, I1939_cp2.1, I1939_cp2.2)) ∧ intTest pI1939 (runFrom pI1939 (fmask pI1939) (cmask pI1939) (hmask pI1939) 1583 356 (true, I1939_cp2.1, I1939_cp2.2)) 1939 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1939_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1939_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1939_fin) true) I1939_seg1) I1939_seg2) (by decide) rfl I1939_fin intTest_fst
theorem link1939 : linkOK pL1939 pH1939 pI1939 = true := by decide +kernel
theorem cvx1939 : ConvexBetweenHumps 1939 :=
  cvx_of L1939_ok H1939_ok I1939_ok link1939 (by decide)

/-! ### The range -/

theorem cvx_1930_1939 {N : ℕ} (h1 : 1930 ≤ N) (h2 : N ≤ 1939) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1934
  · by_cases h4 : N ≤ 1931
    · by_cases h6 : N ≤ 1930
      · obtain rfl : N = 1930 := by omega
        exact cvx1930
      · obtain rfl : N = 1931 := by omega
        exact cvx1931
    · by_cases h6 : N ≤ 1932
      · obtain rfl : N = 1932 := by omega
        exact cvx1932
      · by_cases h8 : N ≤ 1933
        · obtain rfl : N = 1933 := by omega
          exact cvx1933
        · obtain rfl : N = 1934 := by omega
          exact cvx1934
  · by_cases h4 : N ≤ 1936
    · by_cases h6 : N ≤ 1935
      · obtain rfl : N = 1935 := by omega
        exact cvx1935
      · obtain rfl : N = 1936 := by omega
        exact cvx1936
    · by_cases h6 : N ≤ 1937
      · obtain rfl : N = 1937 := by omega
        exact cvx1937
      · by_cases h8 : N ≤ 1938
        · obtain rfl : N = 1938 := by omega
          exact cvx1938
        · obtain rfl : N = 1939 := by omega
          exact cvx1939

theorem cen_1930_1939 {N : ℕ} (h1 : 1930 ≤ N) (h2 : N ≤ 1939) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1932
  · by_cases h4 : N ≤ 1930
    · obtain rfl : N = 1930 := by omega
      exact cen1930
    · obtain rfl : N = 1932 := by omega
      exact cen1932
  · by_cases h4 : N ≤ 1934
    · obtain rfl : N = 1934 := by omega
      exact cen1934
    · by_cases h6 : N ≤ 1936
      · obtain rfl : N = 1936 := by omega
        exact cen1936
      · obtain rfl : N = 1938 := by omega
        exact cen1938

end Kagey131.PaperD.T7
