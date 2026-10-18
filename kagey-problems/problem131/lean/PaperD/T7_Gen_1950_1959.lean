import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1950, …, 1959` (generated)

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

/-! ### `N = 1950` -/

def pL1950 : Prm := ⟨81, 38, 40, 1952, 11, 18446744073709551616, 100401710013016623, 100401710013016623⟩
def pH1950 : Prm := ⟨81, 38, 40, 1952, 11, 18446744073709551616, 100402809524644399, 100402809524644399⟩
def pI1950 : Prm := ⟨68, 34, 31, 1952, 11, 18446744073709551616, 100401710013016623, 100402809524644399⟩
noncomputable def L1950_cp1 : Nat × Nat := t7val% (fastRun pL1950 1 1125 (init pL1950) (init pL1950))
theorem L1950_seg1 : segOK pL1950 1 1125 (init pL1950) (init pL1950) L1950_cp1.1 L1950_cp1.2 = true := by
  decide +kernel
noncomputable def L1950_cp2 : Nat × Nat := t7val% (fastRun pL1950 1 1591 (init pL1950) (init pL1950))
theorem L1950_seg2 : segOK pL1950 1126 466 L1950_cp1.1 L1950_cp1.2 L1950_cp2.1 L1950_cp2.2 = true := by
  decide +kernel
theorem L1950_fin : (prmOK pL1950 1950 && ptTest pL1950 (runFrom pL1950 (fmask pL1950) (cmask pL1950) (hmask pL1950) 1592 358 (true, L1950_cp2.1, L1950_cp2.2)) 1950 975 false) = true := by
  decide +kernel
theorem L1950_ok : RunOK pL1950 1950 (runFrom pL1950 (fmask pL1950) (cmask pL1950) (hmask pL1950) 1592 358 (true, L1950_cp2.1, L1950_cp2.2)) ∧ ptTest pL1950 (runFrom pL1950 (fmask pL1950) (cmask pL1950) (hmask pL1950) 1592 358 (true, L1950_cp2.1, L1950_cp2.2)) 1950 975 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1950_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1950_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1950_fin) true) L1950_seg1) L1950_seg2) (by decide) rfl L1950_fin ptTest_fst
noncomputable def H1950_cp1 : Nat × Nat := t7val% (fastRun pH1950 1 1125 (init pH1950) (init pH1950))
theorem H1950_seg1 : segOK pH1950 1 1125 (init pH1950) (init pH1950) H1950_cp1.1 H1950_cp1.2 = true := by
  decide +kernel
noncomputable def H1950_cp2 : Nat × Nat := t7val% (fastRun pH1950 1 1591 (init pH1950) (init pH1950))
theorem H1950_seg2 : segOK pH1950 1126 466 H1950_cp1.1 H1950_cp1.2 H1950_cp2.1 H1950_cp2.2 = true := by
  decide +kernel
theorem H1950_fin : (prmOK pH1950 1950 && ptTest pH1950 (runFrom pH1950 (fmask pH1950) (cmask pH1950) (hmask pH1950) 1592 358 (true, H1950_cp2.1, H1950_cp2.2)) 1950 975 true) = true := by
  decide +kernel
theorem H1950_ok : RunOK pH1950 1950 (runFrom pH1950 (fmask pH1950) (cmask pH1950) (hmask pH1950) 1592 358 (true, H1950_cp2.1, H1950_cp2.2)) ∧ ptTest pH1950 (runFrom pH1950 (fmask pH1950) (cmask pH1950) (hmask pH1950) 1592 358 (true, H1950_cp2.1, H1950_cp2.2)) 1950 975 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1950_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1950_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1950_fin) true) H1950_seg1) H1950_seg2) (by decide) rfl H1950_fin ptTest_fst
noncomputable def I1950_cp1 : Nat × Nat := t7val% (fastRun pI1950 1 1125 (init pI1950) (init pI1950))
theorem I1950_seg1 : segOK pI1950 1 1125 (init pI1950) (init pI1950) I1950_cp1.1 I1950_cp1.2 = true := by
  decide +kernel
noncomputable def I1950_cp2 : Nat × Nat := t7val% (fastRun pI1950 1 1591 (init pI1950) (init pI1950))
theorem I1950_seg2 : segOK pI1950 1126 466 I1950_cp1.1 I1950_cp1.2 I1950_cp2.1 I1950_cp2.2 = true := by
  decide +kernel
theorem I1950_fin : (prmOK pI1950 1950 && intTest pI1950 (runFrom pI1950 (fmask pI1950) (cmask pI1950) (hmask pI1950) 1592 358 (true, I1950_cp2.1, I1950_cp2.2)) 1950 22 true) = true := by
  decide +kernel
theorem I1950_ok : RunOK pI1950 1950 (runFrom pI1950 (fmask pI1950) (cmask pI1950) (hmask pI1950) 1592 358 (true, I1950_cp2.1, I1950_cp2.2)) ∧ intTest pI1950 (runFrom pI1950 (fmask pI1950) (cmask pI1950) (hmask pI1950) 1592 358 (true, I1950_cp2.1, I1950_cp2.2)) 1950 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1950_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1950_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1950_fin) true) I1950_seg1) I1950_seg2) (by decide) rfl I1950_fin intTest_fst
theorem link1950 : linkOK pL1950 pH1950 pI1950 = true := by decide +kernel
theorem cvx1950 : ConvexBetweenHumps 1950 :=
  cvx_of L1950_ok H1950_ok I1950_ok link1950 (by decide)
theorem cenlink1950 : cenLinkOK pI1950 1950 = true := by decide +kernel
theorem cen1950 : CenterUniqueMin 1950 ∧ DipHyp 1950 ∧ OnePointHyps 1950 :=
  cen_of L1950_ok H1950_ok I1950_ok link1950 cenlink1950

/-! ### `N = 1951` -/

def pL1951 : Prm := ⟨81, 38, 40, 1953, 11, 18446744073709551616, 100359377506068419, 100359377506068419⟩
def pH1951 : Prm := ⟨81, 38, 40, 1953, 11, 18446744073709551616, 100360477017696195, 100360477017696195⟩
def pI1951 : Prm := ⟨68, 34, 31, 1953, 11, 18446744073709551616, 100359377506068419, 100360477017696195⟩
noncomputable def L1951_cp1 : Nat × Nat := t7val% (fastRun pL1951 1 1125 (init pL1951) (init pL1951))
theorem L1951_seg1 : segOK pL1951 1 1125 (init pL1951) (init pL1951) L1951_cp1.1 L1951_cp1.2 = true := by
  decide +kernel
noncomputable def L1951_cp2 : Nat × Nat := t7val% (fastRun pL1951 1 1592 (init pL1951) (init pL1951))
theorem L1951_seg2 : segOK pL1951 1126 467 L1951_cp1.1 L1951_cp1.2 L1951_cp2.1 L1951_cp2.2 = true := by
  decide +kernel
theorem L1951_fin : (prmOK pL1951 1951 && ptTest pL1951 (runFrom pL1951 (fmask pL1951) (cmask pL1951) (hmask pL1951) 1593 358 (true, L1951_cp2.1, L1951_cp2.2)) 1951 976 false) = true := by
  decide +kernel
theorem L1951_ok : RunOK pL1951 1951 (runFrom pL1951 (fmask pL1951) (cmask pL1951) (hmask pL1951) 1593 358 (true, L1951_cp2.1, L1951_cp2.2)) ∧ ptTest pL1951 (runFrom pL1951 (fmask pL1951) (cmask pL1951) (hmask pL1951) 1593 358 (true, L1951_cp2.1, L1951_cp2.2)) 1951 976 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1951_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1951_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1951_fin) true) L1951_seg1) L1951_seg2) (by decide) rfl L1951_fin ptTest_fst
noncomputable def H1951_cp1 : Nat × Nat := t7val% (fastRun pH1951 1 1125 (init pH1951) (init pH1951))
theorem H1951_seg1 : segOK pH1951 1 1125 (init pH1951) (init pH1951) H1951_cp1.1 H1951_cp1.2 = true := by
  decide +kernel
noncomputable def H1951_cp2 : Nat × Nat := t7val% (fastRun pH1951 1 1592 (init pH1951) (init pH1951))
theorem H1951_seg2 : segOK pH1951 1126 467 H1951_cp1.1 H1951_cp1.2 H1951_cp2.1 H1951_cp2.2 = true := by
  decide +kernel
theorem H1951_fin : (prmOK pH1951 1951 && ptTest pH1951 (runFrom pH1951 (fmask pH1951) (cmask pH1951) (hmask pH1951) 1593 358 (true, H1951_cp2.1, H1951_cp2.2)) 1951 976 true) = true := by
  decide +kernel
theorem H1951_ok : RunOK pH1951 1951 (runFrom pH1951 (fmask pH1951) (cmask pH1951) (hmask pH1951) 1593 358 (true, H1951_cp2.1, H1951_cp2.2)) ∧ ptTest pH1951 (runFrom pH1951 (fmask pH1951) (cmask pH1951) (hmask pH1951) 1593 358 (true, H1951_cp2.1, H1951_cp2.2)) 1951 976 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1951_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1951_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1951_fin) true) H1951_seg1) H1951_seg2) (by decide) rfl H1951_fin ptTest_fst
noncomputable def I1951_cp1 : Nat × Nat := t7val% (fastRun pI1951 1 1125 (init pI1951) (init pI1951))
theorem I1951_seg1 : segOK pI1951 1 1125 (init pI1951) (init pI1951) I1951_cp1.1 I1951_cp1.2 = true := by
  decide +kernel
noncomputable def I1951_cp2 : Nat × Nat := t7val% (fastRun pI1951 1 1592 (init pI1951) (init pI1951))
theorem I1951_seg2 : segOK pI1951 1126 467 I1951_cp1.1 I1951_cp1.2 I1951_cp2.1 I1951_cp2.2 = true := by
  decide +kernel
theorem I1951_fin : (prmOK pI1951 1951 && intTest pI1951 (runFrom pI1951 (fmask pI1951) (cmask pI1951) (hmask pI1951) 1593 358 (true, I1951_cp2.1, I1951_cp2.2)) 1951 22 false) = true := by
  decide +kernel
theorem I1951_ok : RunOK pI1951 1951 (runFrom pI1951 (fmask pI1951) (cmask pI1951) (hmask pI1951) 1593 358 (true, I1951_cp2.1, I1951_cp2.2)) ∧ intTest pI1951 (runFrom pI1951 (fmask pI1951) (cmask pI1951) (hmask pI1951) 1593 358 (true, I1951_cp2.1, I1951_cp2.2)) 1951 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1951_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1951_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1951_fin) true) I1951_seg1) I1951_seg2) (by decide) rfl I1951_fin intTest_fst
theorem link1951 : linkOK pL1951 pH1951 pI1951 = true := by decide +kernel
theorem cvx1951 : ConvexBetweenHumps 1951 :=
  cvx_of L1951_ok H1951_ok I1951_ok link1951 (by decide)

/-! ### `N = 1952` -/

def pL1952 : Prm := ⟨81, 38, 40, 1954, 11, 18446744073709551616, 100317098737861457, 100317098737861457⟩
def pH1952 : Prm := ⟨81, 38, 40, 1954, 11, 18446744073709551616, 100318198249489233, 100318198249489233⟩
def pI1952 : Prm := ⟨68, 34, 31, 1954, 11, 18446744073709551616, 100317098737861457, 100318198249489233⟩
noncomputable def L1952_cp1 : Nat × Nat := t7val% (fastRun pL1952 1 1126 (init pL1952) (init pL1952))
theorem L1952_seg1 : segOK pL1952 1 1126 (init pL1952) (init pL1952) L1952_cp1.1 L1952_cp1.2 = true := by
  decide +kernel
noncomputable def L1952_cp2 : Nat × Nat := t7val% (fastRun pL1952 1 1593 (init pL1952) (init pL1952))
theorem L1952_seg2 : segOK pL1952 1127 467 L1952_cp1.1 L1952_cp1.2 L1952_cp2.1 L1952_cp2.2 = true := by
  decide +kernel
theorem L1952_fin : (prmOK pL1952 1952 && ptTest pL1952 (runFrom pL1952 (fmask pL1952) (cmask pL1952) (hmask pL1952) 1594 358 (true, L1952_cp2.1, L1952_cp2.2)) 1952 976 false) = true := by
  decide +kernel
theorem L1952_ok : RunOK pL1952 1952 (runFrom pL1952 (fmask pL1952) (cmask pL1952) (hmask pL1952) 1594 358 (true, L1952_cp2.1, L1952_cp2.2)) ∧ ptTest pL1952 (runFrom pL1952 (fmask pL1952) (cmask pL1952) (hmask pL1952) 1594 358 (true, L1952_cp2.1, L1952_cp2.2)) 1952 976 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1952_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1952_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1952_fin) true) L1952_seg1) L1952_seg2) (by decide) rfl L1952_fin ptTest_fst
noncomputable def H1952_cp1 : Nat × Nat := t7val% (fastRun pH1952 1 1126 (init pH1952) (init pH1952))
theorem H1952_seg1 : segOK pH1952 1 1126 (init pH1952) (init pH1952) H1952_cp1.1 H1952_cp1.2 = true := by
  decide +kernel
noncomputable def H1952_cp2 : Nat × Nat := t7val% (fastRun pH1952 1 1593 (init pH1952) (init pH1952))
theorem H1952_seg2 : segOK pH1952 1127 467 H1952_cp1.1 H1952_cp1.2 H1952_cp2.1 H1952_cp2.2 = true := by
  decide +kernel
theorem H1952_fin : (prmOK pH1952 1952 && ptTest pH1952 (runFrom pH1952 (fmask pH1952) (cmask pH1952) (hmask pH1952) 1594 358 (true, H1952_cp2.1, H1952_cp2.2)) 1952 976 true) = true := by
  decide +kernel
theorem H1952_ok : RunOK pH1952 1952 (runFrom pH1952 (fmask pH1952) (cmask pH1952) (hmask pH1952) 1594 358 (true, H1952_cp2.1, H1952_cp2.2)) ∧ ptTest pH1952 (runFrom pH1952 (fmask pH1952) (cmask pH1952) (hmask pH1952) 1594 358 (true, H1952_cp2.1, H1952_cp2.2)) 1952 976 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1952_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1952_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1952_fin) true) H1952_seg1) H1952_seg2) (by decide) rfl H1952_fin ptTest_fst
noncomputable def I1952_cp1 : Nat × Nat := t7val% (fastRun pI1952 1 1126 (init pI1952) (init pI1952))
theorem I1952_seg1 : segOK pI1952 1 1126 (init pI1952) (init pI1952) I1952_cp1.1 I1952_cp1.2 = true := by
  decide +kernel
noncomputable def I1952_cp2 : Nat × Nat := t7val% (fastRun pI1952 1 1593 (init pI1952) (init pI1952))
theorem I1952_seg2 : segOK pI1952 1127 467 I1952_cp1.1 I1952_cp1.2 I1952_cp2.1 I1952_cp2.2 = true := by
  decide +kernel
theorem I1952_fin : (prmOK pI1952 1952 && intTest pI1952 (runFrom pI1952 (fmask pI1952) (cmask pI1952) (hmask pI1952) 1594 358 (true, I1952_cp2.1, I1952_cp2.2)) 1952 22 true) = true := by
  decide +kernel
theorem I1952_ok : RunOK pI1952 1952 (runFrom pI1952 (fmask pI1952) (cmask pI1952) (hmask pI1952) 1594 358 (true, I1952_cp2.1, I1952_cp2.2)) ∧ intTest pI1952 (runFrom pI1952 (fmask pI1952) (cmask pI1952) (hmask pI1952) 1594 358 (true, I1952_cp2.1, I1952_cp2.2)) 1952 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1952_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1952_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1952_fin) true) I1952_seg1) I1952_seg2) (by decide) rfl I1952_fin intTest_fst
theorem link1952 : linkOK pL1952 pH1952 pI1952 = true := by decide +kernel
theorem cvx1952 : ConvexBetweenHumps 1952 :=
  cvx_of L1952_ok H1952_ok I1952_ok link1952 (by decide)
theorem cenlink1952 : cenLinkOK pI1952 1952 = true := by decide +kernel
theorem cen1952 : CenterUniqueMin 1952 ∧ DipHyp 1952 ∧ OnePointHyps 1952 :=
  cen_of L1952_ok H1952_ok I1952_ok link1952 cenlink1952

/-! ### `N = 1953` -/

def pL1953 : Prm := ⟨81, 38, 40, 1955, 11, 18446744073709551616, 100274843559350815, 100274843559350815⟩
def pH1953 : Prm := ⟨81, 38, 40, 1955, 11, 18446744073709551616, 100275943070978591, 100275943070978591⟩
def pI1953 : Prm := ⟨68, 34, 31, 1955, 11, 18446744073709551616, 100274843559350815, 100275943070978591⟩
noncomputable def L1953_cp1 : Nat × Nat := t7val% (fastRun pL1953 1 1127 (init pL1953) (init pL1953))
theorem L1953_seg1 : segOK pL1953 1 1127 (init pL1953) (init pL1953) L1953_cp1.1 L1953_cp1.2 = true := by
  decide +kernel
noncomputable def L1953_cp2 : Nat × Nat := t7val% (fastRun pL1953 1 1594 (init pL1953) (init pL1953))
theorem L1953_seg2 : segOK pL1953 1128 467 L1953_cp1.1 L1953_cp1.2 L1953_cp2.1 L1953_cp2.2 = true := by
  decide +kernel
theorem L1953_fin : (prmOK pL1953 1953 && ptTest pL1953 (runFrom pL1953 (fmask pL1953) (cmask pL1953) (hmask pL1953) 1595 358 (true, L1953_cp2.1, L1953_cp2.2)) 1953 977 false) = true := by
  decide +kernel
theorem L1953_ok : RunOK pL1953 1953 (runFrom pL1953 (fmask pL1953) (cmask pL1953) (hmask pL1953) 1595 358 (true, L1953_cp2.1, L1953_cp2.2)) ∧ ptTest pL1953 (runFrom pL1953 (fmask pL1953) (cmask pL1953) (hmask pL1953) 1595 358 (true, L1953_cp2.1, L1953_cp2.2)) 1953 977 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1953_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1953_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1953_fin) true) L1953_seg1) L1953_seg2) (by decide) rfl L1953_fin ptTest_fst
noncomputable def H1953_cp1 : Nat × Nat := t7val% (fastRun pH1953 1 1127 (init pH1953) (init pH1953))
theorem H1953_seg1 : segOK pH1953 1 1127 (init pH1953) (init pH1953) H1953_cp1.1 H1953_cp1.2 = true := by
  decide +kernel
noncomputable def H1953_cp2 : Nat × Nat := t7val% (fastRun pH1953 1 1594 (init pH1953) (init pH1953))
theorem H1953_seg2 : segOK pH1953 1128 467 H1953_cp1.1 H1953_cp1.2 H1953_cp2.1 H1953_cp2.2 = true := by
  decide +kernel
theorem H1953_fin : (prmOK pH1953 1953 && ptTest pH1953 (runFrom pH1953 (fmask pH1953) (cmask pH1953) (hmask pH1953) 1595 358 (true, H1953_cp2.1, H1953_cp2.2)) 1953 977 true) = true := by
  decide +kernel
theorem H1953_ok : RunOK pH1953 1953 (runFrom pH1953 (fmask pH1953) (cmask pH1953) (hmask pH1953) 1595 358 (true, H1953_cp2.1, H1953_cp2.2)) ∧ ptTest pH1953 (runFrom pH1953 (fmask pH1953) (cmask pH1953) (hmask pH1953) 1595 358 (true, H1953_cp2.1, H1953_cp2.2)) 1953 977 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1953_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1953_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1953_fin) true) H1953_seg1) H1953_seg2) (by decide) rfl H1953_fin ptTest_fst
noncomputable def I1953_cp1 : Nat × Nat := t7val% (fastRun pI1953 1 1127 (init pI1953) (init pI1953))
theorem I1953_seg1 : segOK pI1953 1 1127 (init pI1953) (init pI1953) I1953_cp1.1 I1953_cp1.2 = true := by
  decide +kernel
noncomputable def I1953_cp2 : Nat × Nat := t7val% (fastRun pI1953 1 1594 (init pI1953) (init pI1953))
theorem I1953_seg2 : segOK pI1953 1128 467 I1953_cp1.1 I1953_cp1.2 I1953_cp2.1 I1953_cp2.2 = true := by
  decide +kernel
theorem I1953_fin : (prmOK pI1953 1953 && intTest pI1953 (runFrom pI1953 (fmask pI1953) (cmask pI1953) (hmask pI1953) 1595 358 (true, I1953_cp2.1, I1953_cp2.2)) 1953 22 false) = true := by
  decide +kernel
theorem I1953_ok : RunOK pI1953 1953 (runFrom pI1953 (fmask pI1953) (cmask pI1953) (hmask pI1953) 1595 358 (true, I1953_cp2.1, I1953_cp2.2)) ∧ intTest pI1953 (runFrom pI1953 (fmask pI1953) (cmask pI1953) (hmask pI1953) 1595 358 (true, I1953_cp2.1, I1953_cp2.2)) 1953 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1953_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1953_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1953_fin) true) I1953_seg1) I1953_seg2) (by decide) rfl I1953_fin intTest_fst
theorem link1953 : linkOK pL1953 pH1953 pI1953 = true := by decide +kernel
theorem cvx1953 : ConvexBetweenHumps 1953 :=
  cvx_of L1953_ok H1953_ok I1953_ok link1953 (by decide)

/-! ### `N = 1954` -/

def pL1954 : Prm := ⟨81, 38, 40, 1956, 11, 18446744073709551616, 100232641963577300, 100232641963577300⟩
def pH1954 : Prm := ⟨81, 38, 40, 1956, 11, 18446744073709551616, 100233741475205076, 100233741475205076⟩
def pI1954 : Prm := ⟨68, 34, 31, 1956, 11, 18446744073709551616, 100232641963577300, 100233741475205076⟩
noncomputable def L1954_cp1 : Nat × Nat := t7val% (fastRun pL1954 1 1127 (init pL1954) (init pL1954))
theorem L1954_seg1 : segOK pL1954 1 1127 (init pL1954) (init pL1954) L1954_cp1.1 L1954_cp1.2 = true := by
  decide +kernel
noncomputable def L1954_cp2 : Nat × Nat := t7val% (fastRun pL1954 1 1594 (init pL1954) (init pL1954))
theorem L1954_seg2 : segOK pL1954 1128 467 L1954_cp1.1 L1954_cp1.2 L1954_cp2.1 L1954_cp2.2 = true := by
  decide +kernel
theorem L1954_fin : (prmOK pL1954 1954 && ptTest pL1954 (runFrom pL1954 (fmask pL1954) (cmask pL1954) (hmask pL1954) 1595 359 (true, L1954_cp2.1, L1954_cp2.2)) 1954 977 false) = true := by
  decide +kernel
theorem L1954_ok : RunOK pL1954 1954 (runFrom pL1954 (fmask pL1954) (cmask pL1954) (hmask pL1954) 1595 359 (true, L1954_cp2.1, L1954_cp2.2)) ∧ ptTest pL1954 (runFrom pL1954 (fmask pL1954) (cmask pL1954) (hmask pL1954) 1595 359 (true, L1954_cp2.1, L1954_cp2.2)) 1954 977 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1954_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1954_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1954_fin) true) L1954_seg1) L1954_seg2) (by decide) rfl L1954_fin ptTest_fst
noncomputable def H1954_cp1 : Nat × Nat := t7val% (fastRun pH1954 1 1127 (init pH1954) (init pH1954))
theorem H1954_seg1 : segOK pH1954 1 1127 (init pH1954) (init pH1954) H1954_cp1.1 H1954_cp1.2 = true := by
  decide +kernel
noncomputable def H1954_cp2 : Nat × Nat := t7val% (fastRun pH1954 1 1594 (init pH1954) (init pH1954))
theorem H1954_seg2 : segOK pH1954 1128 467 H1954_cp1.1 H1954_cp1.2 H1954_cp2.1 H1954_cp2.2 = true := by
  decide +kernel
theorem H1954_fin : (prmOK pH1954 1954 && ptTest pH1954 (runFrom pH1954 (fmask pH1954) (cmask pH1954) (hmask pH1954) 1595 359 (true, H1954_cp2.1, H1954_cp2.2)) 1954 977 true) = true := by
  decide +kernel
theorem H1954_ok : RunOK pH1954 1954 (runFrom pH1954 (fmask pH1954) (cmask pH1954) (hmask pH1954) 1595 359 (true, H1954_cp2.1, H1954_cp2.2)) ∧ ptTest pH1954 (runFrom pH1954 (fmask pH1954) (cmask pH1954) (hmask pH1954) 1595 359 (true, H1954_cp2.1, H1954_cp2.2)) 1954 977 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1954_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1954_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1954_fin) true) H1954_seg1) H1954_seg2) (by decide) rfl H1954_fin ptTest_fst
noncomputable def I1954_cp1 : Nat × Nat := t7val% (fastRun pI1954 1 1127 (init pI1954) (init pI1954))
theorem I1954_seg1 : segOK pI1954 1 1127 (init pI1954) (init pI1954) I1954_cp1.1 I1954_cp1.2 = true := by
  decide +kernel
noncomputable def I1954_cp2 : Nat × Nat := t7val% (fastRun pI1954 1 1594 (init pI1954) (init pI1954))
theorem I1954_seg2 : segOK pI1954 1128 467 I1954_cp1.1 I1954_cp1.2 I1954_cp2.1 I1954_cp2.2 = true := by
  decide +kernel
theorem I1954_fin : (prmOK pI1954 1954 && intTest pI1954 (runFrom pI1954 (fmask pI1954) (cmask pI1954) (hmask pI1954) 1595 359 (true, I1954_cp2.1, I1954_cp2.2)) 1954 22 true) = true := by
  decide +kernel
theorem I1954_ok : RunOK pI1954 1954 (runFrom pI1954 (fmask pI1954) (cmask pI1954) (hmask pI1954) 1595 359 (true, I1954_cp2.1, I1954_cp2.2)) ∧ intTest pI1954 (runFrom pI1954 (fmask pI1954) (cmask pI1954) (hmask pI1954) 1595 359 (true, I1954_cp2.1, I1954_cp2.2)) 1954 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1954_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1954_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1954_fin) true) I1954_seg1) I1954_seg2) (by decide) rfl I1954_fin intTest_fst
theorem link1954 : linkOK pL1954 pH1954 pI1954 = true := by decide +kernel
theorem cvx1954 : ConvexBetweenHumps 1954 :=
  cvx_of L1954_ok H1954_ok I1954_ok link1954 (by decide)
theorem cenlink1954 : cenLinkOK pI1954 1954 = true := by decide +kernel
theorem cen1954 : CenterUniqueMin 1954 ∧ DipHyp 1954 ∧ OnePointHyps 1954 :=
  cen_of L1954_ok H1954_ok I1954_ok link1954 cenlink1954

/-! ### `N = 1955` -/

def pL1955 : Prm := ⟨81, 38, 40, 1957, 11, 18446744073709551616, 100190463895371473, 100190463895371473⟩
def pH1955 : Prm := ⟨81, 38, 40, 1957, 11, 18446744073709551616, 100191563406999249, 100191563406999249⟩
def pI1955 : Prm := ⟨68, 34, 31, 1957, 11, 18446744073709551616, 100190463895371473, 100191563406999249⟩
noncomputable def L1955_cp1 : Nat × Nat := t7val% (fastRun pL1955 1 1128 (init pL1955) (init pL1955))
theorem L1955_seg1 : segOK pL1955 1 1128 (init pL1955) (init pL1955) L1955_cp1.1 L1955_cp1.2 = true := by
  decide +kernel
noncomputable def L1955_cp2 : Nat × Nat := t7val% (fastRun pL1955 1 1595 (init pL1955) (init pL1955))
theorem L1955_seg2 : segOK pL1955 1129 467 L1955_cp1.1 L1955_cp1.2 L1955_cp2.1 L1955_cp2.2 = true := by
  decide +kernel
theorem L1955_fin : (prmOK pL1955 1955 && ptTest pL1955 (runFrom pL1955 (fmask pL1955) (cmask pL1955) (hmask pL1955) 1596 359 (true, L1955_cp2.1, L1955_cp2.2)) 1955 978 false) = true := by
  decide +kernel
theorem L1955_ok : RunOK pL1955 1955 (runFrom pL1955 (fmask pL1955) (cmask pL1955) (hmask pL1955) 1596 359 (true, L1955_cp2.1, L1955_cp2.2)) ∧ ptTest pL1955 (runFrom pL1955 (fmask pL1955) (cmask pL1955) (hmask pL1955) 1596 359 (true, L1955_cp2.1, L1955_cp2.2)) 1955 978 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1955_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1955_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1955_fin) true) L1955_seg1) L1955_seg2) (by decide) rfl L1955_fin ptTest_fst
noncomputable def H1955_cp1 : Nat × Nat := t7val% (fastRun pH1955 1 1128 (init pH1955) (init pH1955))
theorem H1955_seg1 : segOK pH1955 1 1128 (init pH1955) (init pH1955) H1955_cp1.1 H1955_cp1.2 = true := by
  decide +kernel
noncomputable def H1955_cp2 : Nat × Nat := t7val% (fastRun pH1955 1 1595 (init pH1955) (init pH1955))
theorem H1955_seg2 : segOK pH1955 1129 467 H1955_cp1.1 H1955_cp1.2 H1955_cp2.1 H1955_cp2.2 = true := by
  decide +kernel
theorem H1955_fin : (prmOK pH1955 1955 && ptTest pH1955 (runFrom pH1955 (fmask pH1955) (cmask pH1955) (hmask pH1955) 1596 359 (true, H1955_cp2.1, H1955_cp2.2)) 1955 978 true) = true := by
  decide +kernel
theorem H1955_ok : RunOK pH1955 1955 (runFrom pH1955 (fmask pH1955) (cmask pH1955) (hmask pH1955) 1596 359 (true, H1955_cp2.1, H1955_cp2.2)) ∧ ptTest pH1955 (runFrom pH1955 (fmask pH1955) (cmask pH1955) (hmask pH1955) 1596 359 (true, H1955_cp2.1, H1955_cp2.2)) 1955 978 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1955_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1955_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1955_fin) true) H1955_seg1) H1955_seg2) (by decide) rfl H1955_fin ptTest_fst
noncomputable def I1955_cp1 : Nat × Nat := t7val% (fastRun pI1955 1 1128 (init pI1955) (init pI1955))
theorem I1955_seg1 : segOK pI1955 1 1128 (init pI1955) (init pI1955) I1955_cp1.1 I1955_cp1.2 = true := by
  decide +kernel
noncomputable def I1955_cp2 : Nat × Nat := t7val% (fastRun pI1955 1 1595 (init pI1955) (init pI1955))
theorem I1955_seg2 : segOK pI1955 1129 467 I1955_cp1.1 I1955_cp1.2 I1955_cp2.1 I1955_cp2.2 = true := by
  decide +kernel
theorem I1955_fin : (prmOK pI1955 1955 && intTest pI1955 (runFrom pI1955 (fmask pI1955) (cmask pI1955) (hmask pI1955) 1596 359 (true, I1955_cp2.1, I1955_cp2.2)) 1955 22 false) = true := by
  decide +kernel
theorem I1955_ok : RunOK pI1955 1955 (runFrom pI1955 (fmask pI1955) (cmask pI1955) (hmask pI1955) 1596 359 (true, I1955_cp2.1, I1955_cp2.2)) ∧ intTest pI1955 (runFrom pI1955 (fmask pI1955) (cmask pI1955) (hmask pI1955) 1596 359 (true, I1955_cp2.1, I1955_cp2.2)) 1955 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1955_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1955_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1955_fin) true) I1955_seg1) I1955_seg2) (by decide) rfl I1955_fin intTest_fst
theorem link1955 : linkOK pL1955 pH1955 pI1955 = true := by decide +kernel
theorem cvx1955 : ConvexBetweenHumps 1955 :=
  cvx_of L1955_ok H1955_ok I1955_ok link1955 (by decide)

/-! ### `N = 1956` -/

def pL1956 : Prm := ⟨81, 38, 40, 1958, 11, 18446744073709551616, 100148339254470506, 100148339254470506⟩
def pH1956 : Prm := ⟨81, 38, 40, 1958, 11, 18446744073709551616, 100149438766098282, 100149438766098282⟩
def pI1956 : Prm := ⟨68, 34, 31, 1958, 11, 18446744073709551616, 100148339254470506, 100149438766098282⟩
noncomputable def L1956_cp1 : Nat × Nat := t7val% (fastRun pL1956 1 1128 (init pL1956) (init pL1956))
theorem L1956_seg1 : segOK pL1956 1 1128 (init pL1956) (init pL1956) L1956_cp1.1 L1956_cp1.2 = true := by
  decide +kernel
noncomputable def L1956_cp2 : Nat × Nat := t7val% (fastRun pL1956 1 1596 (init pL1956) (init pL1956))
theorem L1956_seg2 : segOK pL1956 1129 468 L1956_cp1.1 L1956_cp1.2 L1956_cp2.1 L1956_cp2.2 = true := by
  decide +kernel
theorem L1956_fin : (prmOK pL1956 1956 && ptTest pL1956 (runFrom pL1956 (fmask pL1956) (cmask pL1956) (hmask pL1956) 1597 359 (true, L1956_cp2.1, L1956_cp2.2)) 1956 978 false) = true := by
  decide +kernel
theorem L1956_ok : RunOK pL1956 1956 (runFrom pL1956 (fmask pL1956) (cmask pL1956) (hmask pL1956) 1597 359 (true, L1956_cp2.1, L1956_cp2.2)) ∧ ptTest pL1956 (runFrom pL1956 (fmask pL1956) (cmask pL1956) (hmask pL1956) 1597 359 (true, L1956_cp2.1, L1956_cp2.2)) 1956 978 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1956_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1956_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1956_fin) true) L1956_seg1) L1956_seg2) (by decide) rfl L1956_fin ptTest_fst
noncomputable def H1956_cp1 : Nat × Nat := t7val% (fastRun pH1956 1 1128 (init pH1956) (init pH1956))
theorem H1956_seg1 : segOK pH1956 1 1128 (init pH1956) (init pH1956) H1956_cp1.1 H1956_cp1.2 = true := by
  decide +kernel
noncomputable def H1956_cp2 : Nat × Nat := t7val% (fastRun pH1956 1 1596 (init pH1956) (init pH1956))
theorem H1956_seg2 : segOK pH1956 1129 468 H1956_cp1.1 H1956_cp1.2 H1956_cp2.1 H1956_cp2.2 = true := by
  decide +kernel
theorem H1956_fin : (prmOK pH1956 1956 && ptTest pH1956 (runFrom pH1956 (fmask pH1956) (cmask pH1956) (hmask pH1956) 1597 359 (true, H1956_cp2.1, H1956_cp2.2)) 1956 978 true) = true := by
  decide +kernel
theorem H1956_ok : RunOK pH1956 1956 (runFrom pH1956 (fmask pH1956) (cmask pH1956) (hmask pH1956) 1597 359 (true, H1956_cp2.1, H1956_cp2.2)) ∧ ptTest pH1956 (runFrom pH1956 (fmask pH1956) (cmask pH1956) (hmask pH1956) 1597 359 (true, H1956_cp2.1, H1956_cp2.2)) 1956 978 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1956_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1956_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1956_fin) true) H1956_seg1) H1956_seg2) (by decide) rfl H1956_fin ptTest_fst
noncomputable def I1956_cp1 : Nat × Nat := t7val% (fastRun pI1956 1 1128 (init pI1956) (init pI1956))
theorem I1956_seg1 : segOK pI1956 1 1128 (init pI1956) (init pI1956) I1956_cp1.1 I1956_cp1.2 = true := by
  decide +kernel
noncomputable def I1956_cp2 : Nat × Nat := t7val% (fastRun pI1956 1 1596 (init pI1956) (init pI1956))
theorem I1956_seg2 : segOK pI1956 1129 468 I1956_cp1.1 I1956_cp1.2 I1956_cp2.1 I1956_cp2.2 = true := by
  decide +kernel
theorem I1956_fin : (prmOK pI1956 1956 && intTest pI1956 (runFrom pI1956 (fmask pI1956) (cmask pI1956) (hmask pI1956) 1597 359 (true, I1956_cp2.1, I1956_cp2.2)) 1956 22 true) = true := by
  decide +kernel
theorem I1956_ok : RunOK pI1956 1956 (runFrom pI1956 (fmask pI1956) (cmask pI1956) (hmask pI1956) 1597 359 (true, I1956_cp2.1, I1956_cp2.2)) ∧ intTest pI1956 (runFrom pI1956 (fmask pI1956) (cmask pI1956) (hmask pI1956) 1597 359 (true, I1956_cp2.1, I1956_cp2.2)) 1956 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1956_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1956_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1956_fin) true) I1956_seg1) I1956_seg2) (by decide) rfl I1956_fin intTest_fst
theorem link1956 : linkOK pL1956 pH1956 pI1956 = true := by decide +kernel
theorem cvx1956 : ConvexBetweenHumps 1956 :=
  cvx_of L1956_ok H1956_ok I1956_ok link1956 (by decide)
theorem cenlink1956 : cenLinkOK pI1956 1956 = true := by decide +kernel
theorem cen1956 : CenterUniqueMin 1956 ∧ DipHyp 1956 ∧ OnePointHyps 1956 :=
  cen_of L1956_ok H1956_ok I1956_ok link1956 cenlink1956

/-! ### `N = 1957` -/

def pL1957 : Prm := ⟨81, 38, 40, 1959, 11, 18446744073709551616, 100106238079266847, 100106238079266847⟩
def pH1957 : Prm := ⟨81, 38, 40, 1959, 11, 18446744073709551616, 100107337590894623, 100107337590894623⟩
def pI1957 : Prm := ⟨68, 34, 31, 1959, 11, 18446744073709551616, 100106238079266847, 100107337590894623⟩
noncomputable def L1957_cp1 : Nat × Nat := t7val% (fastRun pL1957 1 1129 (init pL1957) (init pL1957))
theorem L1957_seg1 : segOK pL1957 1 1129 (init pL1957) (init pL1957) L1957_cp1.1 L1957_cp1.2 = true := by
  decide +kernel
noncomputable def L1957_cp2 : Nat × Nat := t7val% (fastRun pL1957 1 1597 (init pL1957) (init pL1957))
theorem L1957_seg2 : segOK pL1957 1130 468 L1957_cp1.1 L1957_cp1.2 L1957_cp2.1 L1957_cp2.2 = true := by
  decide +kernel
theorem L1957_fin : (prmOK pL1957 1957 && ptTest pL1957 (runFrom pL1957 (fmask pL1957) (cmask pL1957) (hmask pL1957) 1598 359 (true, L1957_cp2.1, L1957_cp2.2)) 1957 979 false) = true := by
  decide +kernel
theorem L1957_ok : RunOK pL1957 1957 (runFrom pL1957 (fmask pL1957) (cmask pL1957) (hmask pL1957) 1598 359 (true, L1957_cp2.1, L1957_cp2.2)) ∧ ptTest pL1957 (runFrom pL1957 (fmask pL1957) (cmask pL1957) (hmask pL1957) 1598 359 (true, L1957_cp2.1, L1957_cp2.2)) 1957 979 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1957_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1957_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1957_fin) true) L1957_seg1) L1957_seg2) (by decide) rfl L1957_fin ptTest_fst
noncomputable def H1957_cp1 : Nat × Nat := t7val% (fastRun pH1957 1 1129 (init pH1957) (init pH1957))
theorem H1957_seg1 : segOK pH1957 1 1129 (init pH1957) (init pH1957) H1957_cp1.1 H1957_cp1.2 = true := by
  decide +kernel
noncomputable def H1957_cp2 : Nat × Nat := t7val% (fastRun pH1957 1 1597 (init pH1957) (init pH1957))
theorem H1957_seg2 : segOK pH1957 1130 468 H1957_cp1.1 H1957_cp1.2 H1957_cp2.1 H1957_cp2.2 = true := by
  decide +kernel
theorem H1957_fin : (prmOK pH1957 1957 && ptTest pH1957 (runFrom pH1957 (fmask pH1957) (cmask pH1957) (hmask pH1957) 1598 359 (true, H1957_cp2.1, H1957_cp2.2)) 1957 979 true) = true := by
  decide +kernel
theorem H1957_ok : RunOK pH1957 1957 (runFrom pH1957 (fmask pH1957) (cmask pH1957) (hmask pH1957) 1598 359 (true, H1957_cp2.1, H1957_cp2.2)) ∧ ptTest pH1957 (runFrom pH1957 (fmask pH1957) (cmask pH1957) (hmask pH1957) 1598 359 (true, H1957_cp2.1, H1957_cp2.2)) 1957 979 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1957_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1957_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1957_fin) true) H1957_seg1) H1957_seg2) (by decide) rfl H1957_fin ptTest_fst
noncomputable def I1957_cp1 : Nat × Nat := t7val% (fastRun pI1957 1 1129 (init pI1957) (init pI1957))
theorem I1957_seg1 : segOK pI1957 1 1129 (init pI1957) (init pI1957) I1957_cp1.1 I1957_cp1.2 = true := by
  decide +kernel
noncomputable def I1957_cp2 : Nat × Nat := t7val% (fastRun pI1957 1 1597 (init pI1957) (init pI1957))
theorem I1957_seg2 : segOK pI1957 1130 468 I1957_cp1.1 I1957_cp1.2 I1957_cp2.1 I1957_cp2.2 = true := by
  decide +kernel
theorem I1957_fin : (prmOK pI1957 1957 && intTest pI1957 (runFrom pI1957 (fmask pI1957) (cmask pI1957) (hmask pI1957) 1598 359 (true, I1957_cp2.1, I1957_cp2.2)) 1957 22 false) = true := by
  decide +kernel
theorem I1957_ok : RunOK pI1957 1957 (runFrom pI1957 (fmask pI1957) (cmask pI1957) (hmask pI1957) 1598 359 (true, I1957_cp2.1, I1957_cp2.2)) ∧ intTest pI1957 (runFrom pI1957 (fmask pI1957) (cmask pI1957) (hmask pI1957) 1598 359 (true, I1957_cp2.1, I1957_cp2.2)) 1957 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1957_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1957_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1957_fin) true) I1957_seg1) I1957_seg2) (by decide) rfl I1957_fin intTest_fst
theorem link1957 : linkOK pL1957 pH1957 pI1957 = true := by decide +kernel
theorem cvx1957 : ConvexBetweenHumps 1957 :=
  cvx_of L1957_ok H1957_ok I1957_ok link1957 (by decide)

/-! ### `N = 1958` -/

def pL1958 : Prm := ⟨81, 38, 40, 1960, 11, 18446744073709551616, 100064190176562972, 100064190176562972⟩
def pH1958 : Prm := ⟨81, 38, 40, 1960, 11, 18446744073709551616, 100065289688190748, 100065289688190748⟩
def pI1958 : Prm := ⟨68, 34, 31, 1960, 11, 18446744073709551616, 100064190176562972, 100065289688190748⟩
noncomputable def L1958_cp1 : Nat × Nat := t7val% (fastRun pL1958 1 1129 (init pL1958) (init pL1958))
theorem L1958_seg1 : segOK pL1958 1 1129 (init pL1958) (init pL1958) L1958_cp1.1 L1958_cp1.2 = true := by
  decide +kernel
noncomputable def L1958_cp2 : Nat × Nat := t7val% (fastRun pL1958 1 1598 (init pL1958) (init pL1958))
theorem L1958_seg2 : segOK pL1958 1130 469 L1958_cp1.1 L1958_cp1.2 L1958_cp2.1 L1958_cp2.2 = true := by
  decide +kernel
theorem L1958_fin : (prmOK pL1958 1958 && ptTest pL1958 (runFrom pL1958 (fmask pL1958) (cmask pL1958) (hmask pL1958) 1599 359 (true, L1958_cp2.1, L1958_cp2.2)) 1958 979 false) = true := by
  decide +kernel
theorem L1958_ok : RunOK pL1958 1958 (runFrom pL1958 (fmask pL1958) (cmask pL1958) (hmask pL1958) 1599 359 (true, L1958_cp2.1, L1958_cp2.2)) ∧ ptTest pL1958 (runFrom pL1958 (fmask pL1958) (cmask pL1958) (hmask pL1958) 1599 359 (true, L1958_cp2.1, L1958_cp2.2)) 1958 979 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1958_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1958_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1958_fin) true) L1958_seg1) L1958_seg2) (by decide) rfl L1958_fin ptTest_fst
noncomputable def H1958_cp1 : Nat × Nat := t7val% (fastRun pH1958 1 1129 (init pH1958) (init pH1958))
theorem H1958_seg1 : segOK pH1958 1 1129 (init pH1958) (init pH1958) H1958_cp1.1 H1958_cp1.2 = true := by
  decide +kernel
noncomputable def H1958_cp2 : Nat × Nat := t7val% (fastRun pH1958 1 1598 (init pH1958) (init pH1958))
theorem H1958_seg2 : segOK pH1958 1130 469 H1958_cp1.1 H1958_cp1.2 H1958_cp2.1 H1958_cp2.2 = true := by
  decide +kernel
theorem H1958_fin : (prmOK pH1958 1958 && ptTest pH1958 (runFrom pH1958 (fmask pH1958) (cmask pH1958) (hmask pH1958) 1599 359 (true, H1958_cp2.1, H1958_cp2.2)) 1958 979 true) = true := by
  decide +kernel
theorem H1958_ok : RunOK pH1958 1958 (runFrom pH1958 (fmask pH1958) (cmask pH1958) (hmask pH1958) 1599 359 (true, H1958_cp2.1, H1958_cp2.2)) ∧ ptTest pH1958 (runFrom pH1958 (fmask pH1958) (cmask pH1958) (hmask pH1958) 1599 359 (true, H1958_cp2.1, H1958_cp2.2)) 1958 979 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1958_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1958_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1958_fin) true) H1958_seg1) H1958_seg2) (by decide) rfl H1958_fin ptTest_fst
noncomputable def I1958_cp1 : Nat × Nat := t7val% (fastRun pI1958 1 1129 (init pI1958) (init pI1958))
theorem I1958_seg1 : segOK pI1958 1 1129 (init pI1958) (init pI1958) I1958_cp1.1 I1958_cp1.2 = true := by
  decide +kernel
noncomputable def I1958_cp2 : Nat × Nat := t7val% (fastRun pI1958 1 1598 (init pI1958) (init pI1958))
theorem I1958_seg2 : segOK pI1958 1130 469 I1958_cp1.1 I1958_cp1.2 I1958_cp2.1 I1958_cp2.2 = true := by
  decide +kernel
theorem I1958_fin : (prmOK pI1958 1958 && intTest pI1958 (runFrom pI1958 (fmask pI1958) (cmask pI1958) (hmask pI1958) 1599 359 (true, I1958_cp2.1, I1958_cp2.2)) 1958 22 true) = true := by
  decide +kernel
theorem I1958_ok : RunOK pI1958 1958 (runFrom pI1958 (fmask pI1958) (cmask pI1958) (hmask pI1958) 1599 359 (true, I1958_cp2.1, I1958_cp2.2)) ∧ intTest pI1958 (runFrom pI1958 (fmask pI1958) (cmask pI1958) (hmask pI1958) 1599 359 (true, I1958_cp2.1, I1958_cp2.2)) 1958 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1958_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1958_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1958_fin) true) I1958_seg1) I1958_seg2) (by decide) rfl I1958_fin intTest_fst
theorem link1958 : linkOK pL1958 pH1958 pI1958 = true := by decide +kernel
theorem cvx1958 : ConvexBetweenHumps 1958 :=
  cvx_of L1958_ok H1958_ok I1958_ok link1958 (by decide)
theorem cenlink1958 : cenLinkOK pI1958 1958 = true := by decide +kernel
theorem cen1958 : CenterUniqueMin 1958 ∧ DipHyp 1958 ∧ OnePointHyps 1958 :=
  cen_of L1958_ok H1958_ok I1958_ok link1958 cenlink1958

/-! ### `N = 1959` -/

def pL1959 : Prm := ⟨81, 38, 40, 1961, 11, 18446744073709551616, 100022165677852046, 100022165677852046⟩
def pH1959 : Prm := ⟨81, 38, 40, 1961, 11, 18446744073709551616, 100023265189479822, 100023265189479822⟩
def pI1959 : Prm := ⟨68, 34, 31, 1961, 11, 18446744073709551616, 100022165677852046, 100023265189479822⟩
noncomputable def L1959_cp1 : Nat × Nat := t7val% (fastRun pL1959 1 1130 (init pL1959) (init pL1959))
theorem L1959_seg1 : segOK pL1959 1 1130 (init pL1959) (init pL1959) L1959_cp1.1 L1959_cp1.2 = true := by
  decide +kernel
noncomputable def L1959_cp2 : Nat × Nat := t7val% (fastRun pL1959 1 1599 (init pL1959) (init pL1959))
theorem L1959_seg2 : segOK pL1959 1131 469 L1959_cp1.1 L1959_cp1.2 L1959_cp2.1 L1959_cp2.2 = true := by
  decide +kernel
theorem L1959_fin : (prmOK pL1959 1959 && ptTest pL1959 (runFrom pL1959 (fmask pL1959) (cmask pL1959) (hmask pL1959) 1600 359 (true, L1959_cp2.1, L1959_cp2.2)) 1959 980 false) = true := by
  decide +kernel
theorem L1959_ok : RunOK pL1959 1959 (runFrom pL1959 (fmask pL1959) (cmask pL1959) (hmask pL1959) 1600 359 (true, L1959_cp2.1, L1959_cp2.2)) ∧ ptTest pL1959 (runFrom pL1959 (fmask pL1959) (cmask pL1959) (hmask pL1959) 1600 359 (true, L1959_cp2.1, L1959_cp2.2)) 1959 980 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1959_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1959_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1959_fin) true) L1959_seg1) L1959_seg2) (by decide) rfl L1959_fin ptTest_fst
noncomputable def H1959_cp1 : Nat × Nat := t7val% (fastRun pH1959 1 1130 (init pH1959) (init pH1959))
theorem H1959_seg1 : segOK pH1959 1 1130 (init pH1959) (init pH1959) H1959_cp1.1 H1959_cp1.2 = true := by
  decide +kernel
noncomputable def H1959_cp2 : Nat × Nat := t7val% (fastRun pH1959 1 1599 (init pH1959) (init pH1959))
theorem H1959_seg2 : segOK pH1959 1131 469 H1959_cp1.1 H1959_cp1.2 H1959_cp2.1 H1959_cp2.2 = true := by
  decide +kernel
theorem H1959_fin : (prmOK pH1959 1959 && ptTest pH1959 (runFrom pH1959 (fmask pH1959) (cmask pH1959) (hmask pH1959) 1600 359 (true, H1959_cp2.1, H1959_cp2.2)) 1959 980 true) = true := by
  decide +kernel
theorem H1959_ok : RunOK pH1959 1959 (runFrom pH1959 (fmask pH1959) (cmask pH1959) (hmask pH1959) 1600 359 (true, H1959_cp2.1, H1959_cp2.2)) ∧ ptTest pH1959 (runFrom pH1959 (fmask pH1959) (cmask pH1959) (hmask pH1959) 1600 359 (true, H1959_cp2.1, H1959_cp2.2)) 1959 980 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1959_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1959_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1959_fin) true) H1959_seg1) H1959_seg2) (by decide) rfl H1959_fin ptTest_fst
noncomputable def I1959_cp1 : Nat × Nat := t7val% (fastRun pI1959 1 1130 (init pI1959) (init pI1959))
theorem I1959_seg1 : segOK pI1959 1 1130 (init pI1959) (init pI1959) I1959_cp1.1 I1959_cp1.2 = true := by
  decide +kernel
noncomputable def I1959_cp2 : Nat × Nat := t7val% (fastRun pI1959 1 1599 (init pI1959) (init pI1959))
theorem I1959_seg2 : segOK pI1959 1131 469 I1959_cp1.1 I1959_cp1.2 I1959_cp2.1 I1959_cp2.2 = true := by
  decide +kernel
theorem I1959_fin : (prmOK pI1959 1959 && intTest pI1959 (runFrom pI1959 (fmask pI1959) (cmask pI1959) (hmask pI1959) 1600 359 (true, I1959_cp2.1, I1959_cp2.2)) 1959 22 false) = true := by
  decide +kernel
theorem I1959_ok : RunOK pI1959 1959 (runFrom pI1959 (fmask pI1959) (cmask pI1959) (hmask pI1959) 1600 359 (true, I1959_cp2.1, I1959_cp2.2)) ∧ intTest pI1959 (runFrom pI1959 (fmask pI1959) (cmask pI1959) (hmask pI1959) 1600 359 (true, I1959_cp2.1, I1959_cp2.2)) 1959 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1959_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1959_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1959_fin) true) I1959_seg1) I1959_seg2) (by decide) rfl I1959_fin intTest_fst
theorem link1959 : linkOK pL1959 pH1959 pI1959 = true := by decide +kernel
theorem cvx1959 : ConvexBetweenHumps 1959 :=
  cvx_of L1959_ok H1959_ok I1959_ok link1959 (by decide)

/-! ### The range -/

theorem cvx_1950_1959 {N : ℕ} (h1 : 1950 ≤ N) (h2 : N ≤ 1959) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1954
  · by_cases h4 : N ≤ 1951
    · by_cases h6 : N ≤ 1950
      · obtain rfl : N = 1950 := by omega
        exact cvx1950
      · obtain rfl : N = 1951 := by omega
        exact cvx1951
    · by_cases h6 : N ≤ 1952
      · obtain rfl : N = 1952 := by omega
        exact cvx1952
      · by_cases h8 : N ≤ 1953
        · obtain rfl : N = 1953 := by omega
          exact cvx1953
        · obtain rfl : N = 1954 := by omega
          exact cvx1954
  · by_cases h4 : N ≤ 1956
    · by_cases h6 : N ≤ 1955
      · obtain rfl : N = 1955 := by omega
        exact cvx1955
      · obtain rfl : N = 1956 := by omega
        exact cvx1956
    · by_cases h6 : N ≤ 1957
      · obtain rfl : N = 1957 := by omega
        exact cvx1957
      · by_cases h8 : N ≤ 1958
        · obtain rfl : N = 1958 := by omega
          exact cvx1958
        · obtain rfl : N = 1959 := by omega
          exact cvx1959

theorem cen_1950_1959 {N : ℕ} (h1 : 1950 ≤ N) (h2 : N ≤ 1959) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1952
  · by_cases h4 : N ≤ 1950
    · obtain rfl : N = 1950 := by omega
      exact cen1950
    · obtain rfl : N = 1952 := by omega
      exact cen1952
  · by_cases h4 : N ≤ 1954
    · obtain rfl : N = 1954 := by omega
      exact cen1954
    · by_cases h6 : N ≤ 1956
      · obtain rfl : N = 1956 := by omega
        exact cen1956
      · obtain rfl : N = 1958 := by omega
        exact cen1958

end Kagey131.PaperD.T7
