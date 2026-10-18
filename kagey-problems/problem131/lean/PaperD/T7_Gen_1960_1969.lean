import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1960, …, 1969` (generated)

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

/-! ### `N = 1960` -/

def pL1960 : Prm := ⟨81, 38, 40, 1962, 11, 18446744073709551616, 99980194297481465, 99980194297481465⟩
def pH1960 : Prm := ⟨81, 38, 40, 1962, 11, 18446744073709551616, 99981293809109241, 99981293809109241⟩
def pI1960 : Prm := ⟨68, 34, 31, 1962, 11, 18446744073709551616, 99980194297481465, 99981293809109241⟩
noncomputable def L1960_cp1 : Nat × Nat := t7val% (fastRun pL1960 1 1131 (init pL1960) (init pL1960))
theorem L1960_seg1 : segOK pL1960 1 1131 (init pL1960) (init pL1960) L1960_cp1.1 L1960_cp1.2 = true := by
  decide +kernel
noncomputable def L1960_cp2 : Nat × Nat := t7val% (fastRun pL1960 1 1599 (init pL1960) (init pL1960))
theorem L1960_seg2 : segOK pL1960 1132 468 L1960_cp1.1 L1960_cp1.2 L1960_cp2.1 L1960_cp2.2 = true := by
  decide +kernel
theorem L1960_fin : (prmOK pL1960 1960 && ptTest pL1960 (runFrom pL1960 (fmask pL1960) (cmask pL1960) (hmask pL1960) 1600 360 (true, L1960_cp2.1, L1960_cp2.2)) 1960 980 false) = true := by
  decide +kernel
theorem L1960_ok : RunOK pL1960 1960 (runFrom pL1960 (fmask pL1960) (cmask pL1960) (hmask pL1960) 1600 360 (true, L1960_cp2.1, L1960_cp2.2)) ∧ ptTest pL1960 (runFrom pL1960 (fmask pL1960) (cmask pL1960) (hmask pL1960) 1600 360 (true, L1960_cp2.1, L1960_cp2.2)) 1960 980 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1960_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1960_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1960_fin) true) L1960_seg1) L1960_seg2) (by decide) rfl L1960_fin ptTest_fst
noncomputable def H1960_cp1 : Nat × Nat := t7val% (fastRun pH1960 1 1131 (init pH1960) (init pH1960))
theorem H1960_seg1 : segOK pH1960 1 1131 (init pH1960) (init pH1960) H1960_cp1.1 H1960_cp1.2 = true := by
  decide +kernel
noncomputable def H1960_cp2 : Nat × Nat := t7val% (fastRun pH1960 1 1599 (init pH1960) (init pH1960))
theorem H1960_seg2 : segOK pH1960 1132 468 H1960_cp1.1 H1960_cp1.2 H1960_cp2.1 H1960_cp2.2 = true := by
  decide +kernel
theorem H1960_fin : (prmOK pH1960 1960 && ptTest pH1960 (runFrom pH1960 (fmask pH1960) (cmask pH1960) (hmask pH1960) 1600 360 (true, H1960_cp2.1, H1960_cp2.2)) 1960 980 true) = true := by
  decide +kernel
theorem H1960_ok : RunOK pH1960 1960 (runFrom pH1960 (fmask pH1960) (cmask pH1960) (hmask pH1960) 1600 360 (true, H1960_cp2.1, H1960_cp2.2)) ∧ ptTest pH1960 (runFrom pH1960 (fmask pH1960) (cmask pH1960) (hmask pH1960) 1600 360 (true, H1960_cp2.1, H1960_cp2.2)) 1960 980 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1960_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1960_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1960_fin) true) H1960_seg1) H1960_seg2) (by decide) rfl H1960_fin ptTest_fst
noncomputable def I1960_cp1 : Nat × Nat := t7val% (fastRun pI1960 1 1131 (init pI1960) (init pI1960))
theorem I1960_seg1 : segOK pI1960 1 1131 (init pI1960) (init pI1960) I1960_cp1.1 I1960_cp1.2 = true := by
  decide +kernel
noncomputable def I1960_cp2 : Nat × Nat := t7val% (fastRun pI1960 1 1599 (init pI1960) (init pI1960))
theorem I1960_seg2 : segOK pI1960 1132 468 I1960_cp1.1 I1960_cp1.2 I1960_cp2.1 I1960_cp2.2 = true := by
  decide +kernel
theorem I1960_fin : (prmOK pI1960 1960 && intTest pI1960 (runFrom pI1960 (fmask pI1960) (cmask pI1960) (hmask pI1960) 1600 360 (true, I1960_cp2.1, I1960_cp2.2)) 1960 22 true) = true := by
  decide +kernel
theorem I1960_ok : RunOK pI1960 1960 (runFrom pI1960 (fmask pI1960) (cmask pI1960) (hmask pI1960) 1600 360 (true, I1960_cp2.1, I1960_cp2.2)) ∧ intTest pI1960 (runFrom pI1960 (fmask pI1960) (cmask pI1960) (hmask pI1960) 1600 360 (true, I1960_cp2.1, I1960_cp2.2)) 1960 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1960_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1960_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1960_fin) true) I1960_seg1) I1960_seg2) (by decide) rfl I1960_fin intTest_fst
theorem link1960 : linkOK pL1960 pH1960 pI1960 = true := by decide +kernel
theorem cvx1960 : ConvexBetweenHumps 1960 :=
  cvx_of L1960_ok H1960_ok I1960_ok link1960 (by decide)
theorem cenlink1960 : cenLinkOK pI1960 1960 = true := by decide +kernel
theorem cen1960 : CenterUniqueMin 1960 ∧ DipHyp 1960 ∧ OnePointHyps 1960 :=
  cen_of L1960_ok H1960_ok I1960_ok link1960 cenlink1960

/-! ### `N = 1961` -/

def pL1961 : Prm := ⟨81, 38, 40, 1963, 11, 18446744073709551616, 99938246259639281, 99938246259639281⟩
def pH1961 : Prm := ⟨81, 38, 40, 1963, 11, 18446744073709551616, 99939345771267057, 99939345771267057⟩
def pI1961 : Prm := ⟨68, 34, 31, 1963, 11, 18446744073709551616, 99938246259639281, 99939345771267057⟩
noncomputable def L1961_cp1 : Nat × Nat := t7val% (fastRun pL1961 1 1131 (init pL1961) (init pL1961))
theorem L1961_seg1 : segOK pL1961 1 1131 (init pL1961) (init pL1961) L1961_cp1.1 L1961_cp1.2 = true := by
  decide +kernel
noncomputable def L1961_cp2 : Nat × Nat := t7val% (fastRun pL1961 1 1600 (init pL1961) (init pL1961))
theorem L1961_seg2 : segOK pL1961 1132 469 L1961_cp1.1 L1961_cp1.2 L1961_cp2.1 L1961_cp2.2 = true := by
  decide +kernel
theorem L1961_fin : (prmOK pL1961 1961 && ptTest pL1961 (runFrom pL1961 (fmask pL1961) (cmask pL1961) (hmask pL1961) 1601 360 (true, L1961_cp2.1, L1961_cp2.2)) 1961 981 false) = true := by
  decide +kernel
theorem L1961_ok : RunOK pL1961 1961 (runFrom pL1961 (fmask pL1961) (cmask pL1961) (hmask pL1961) 1601 360 (true, L1961_cp2.1, L1961_cp2.2)) ∧ ptTest pL1961 (runFrom pL1961 (fmask pL1961) (cmask pL1961) (hmask pL1961) 1601 360 (true, L1961_cp2.1, L1961_cp2.2)) 1961 981 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1961_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1961_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1961_fin) true) L1961_seg1) L1961_seg2) (by decide) rfl L1961_fin ptTest_fst
noncomputable def H1961_cp1 : Nat × Nat := t7val% (fastRun pH1961 1 1131 (init pH1961) (init pH1961))
theorem H1961_seg1 : segOK pH1961 1 1131 (init pH1961) (init pH1961) H1961_cp1.1 H1961_cp1.2 = true := by
  decide +kernel
noncomputable def H1961_cp2 : Nat × Nat := t7val% (fastRun pH1961 1 1600 (init pH1961) (init pH1961))
theorem H1961_seg2 : segOK pH1961 1132 469 H1961_cp1.1 H1961_cp1.2 H1961_cp2.1 H1961_cp2.2 = true := by
  decide +kernel
theorem H1961_fin : (prmOK pH1961 1961 && ptTest pH1961 (runFrom pH1961 (fmask pH1961) (cmask pH1961) (hmask pH1961) 1601 360 (true, H1961_cp2.1, H1961_cp2.2)) 1961 981 true) = true := by
  decide +kernel
theorem H1961_ok : RunOK pH1961 1961 (runFrom pH1961 (fmask pH1961) (cmask pH1961) (hmask pH1961) 1601 360 (true, H1961_cp2.1, H1961_cp2.2)) ∧ ptTest pH1961 (runFrom pH1961 (fmask pH1961) (cmask pH1961) (hmask pH1961) 1601 360 (true, H1961_cp2.1, H1961_cp2.2)) 1961 981 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1961_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1961_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1961_fin) true) H1961_seg1) H1961_seg2) (by decide) rfl H1961_fin ptTest_fst
noncomputable def I1961_cp1 : Nat × Nat := t7val% (fastRun pI1961 1 1131 (init pI1961) (init pI1961))
theorem I1961_seg1 : segOK pI1961 1 1131 (init pI1961) (init pI1961) I1961_cp1.1 I1961_cp1.2 = true := by
  decide +kernel
noncomputable def I1961_cp2 : Nat × Nat := t7val% (fastRun pI1961 1 1600 (init pI1961) (init pI1961))
theorem I1961_seg2 : segOK pI1961 1132 469 I1961_cp1.1 I1961_cp1.2 I1961_cp2.1 I1961_cp2.2 = true := by
  decide +kernel
theorem I1961_fin : (prmOK pI1961 1961 && intTest pI1961 (runFrom pI1961 (fmask pI1961) (cmask pI1961) (hmask pI1961) 1601 360 (true, I1961_cp2.1, I1961_cp2.2)) 1961 22 false) = true := by
  decide +kernel
theorem I1961_ok : RunOK pI1961 1961 (runFrom pI1961 (fmask pI1961) (cmask pI1961) (hmask pI1961) 1601 360 (true, I1961_cp2.1, I1961_cp2.2)) ∧ intTest pI1961 (runFrom pI1961 (fmask pI1961) (cmask pI1961) (hmask pI1961) 1601 360 (true, I1961_cp2.1, I1961_cp2.2)) 1961 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1961_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1961_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1961_fin) true) I1961_seg1) I1961_seg2) (by decide) rfl I1961_fin intTest_fst
theorem link1961 : linkOK pL1961 pH1961 pI1961 = true := by decide +kernel
theorem cvx1961 : ConvexBetweenHumps 1961 :=
  cvx_of L1961_ok H1961_ok I1961_ok link1961 (by decide)

/-! ### `N = 1962` -/

def pL1962 : Prm := ⟨81, 38, 40, 1964, 11, 18446744073709551616, 99896351186531403, 99896351186531403⟩
def pH1962 : Prm := ⟨81, 38, 40, 1964, 11, 18446744073709551616, 99897450698159179, 99897450698159179⟩
def pI1962 : Prm := ⟨68, 34, 31, 1964, 11, 18446744073709551616, 99896351186531403, 99897450698159179⟩
noncomputable def L1962_cp1 : Nat × Nat := t7val% (fastRun pL1962 1 1132 (init pL1962) (init pL1962))
theorem L1962_seg1 : segOK pL1962 1 1132 (init pL1962) (init pL1962) L1962_cp1.1 L1962_cp1.2 = true := by
  decide +kernel
noncomputable def L1962_cp2 : Nat × Nat := t7val% (fastRun pL1962 1 1601 (init pL1962) (init pL1962))
theorem L1962_seg2 : segOK pL1962 1133 469 L1962_cp1.1 L1962_cp1.2 L1962_cp2.1 L1962_cp2.2 = true := by
  decide +kernel
theorem L1962_fin : (prmOK pL1962 1962 && ptTest pL1962 (runFrom pL1962 (fmask pL1962) (cmask pL1962) (hmask pL1962) 1602 360 (true, L1962_cp2.1, L1962_cp2.2)) 1962 981 false) = true := by
  decide +kernel
theorem L1962_ok : RunOK pL1962 1962 (runFrom pL1962 (fmask pL1962) (cmask pL1962) (hmask pL1962) 1602 360 (true, L1962_cp2.1, L1962_cp2.2)) ∧ ptTest pL1962 (runFrom pL1962 (fmask pL1962) (cmask pL1962) (hmask pL1962) 1602 360 (true, L1962_cp2.1, L1962_cp2.2)) 1962 981 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1962_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1962_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1962_fin) true) L1962_seg1) L1962_seg2) (by decide) rfl L1962_fin ptTest_fst
noncomputable def H1962_cp1 : Nat × Nat := t7val% (fastRun pH1962 1 1132 (init pH1962) (init pH1962))
theorem H1962_seg1 : segOK pH1962 1 1132 (init pH1962) (init pH1962) H1962_cp1.1 H1962_cp1.2 = true := by
  decide +kernel
noncomputable def H1962_cp2 : Nat × Nat := t7val% (fastRun pH1962 1 1601 (init pH1962) (init pH1962))
theorem H1962_seg2 : segOK pH1962 1133 469 H1962_cp1.1 H1962_cp1.2 H1962_cp2.1 H1962_cp2.2 = true := by
  decide +kernel
theorem H1962_fin : (prmOK pH1962 1962 && ptTest pH1962 (runFrom pH1962 (fmask pH1962) (cmask pH1962) (hmask pH1962) 1602 360 (true, H1962_cp2.1, H1962_cp2.2)) 1962 981 true) = true := by
  decide +kernel
theorem H1962_ok : RunOK pH1962 1962 (runFrom pH1962 (fmask pH1962) (cmask pH1962) (hmask pH1962) 1602 360 (true, H1962_cp2.1, H1962_cp2.2)) ∧ ptTest pH1962 (runFrom pH1962 (fmask pH1962) (cmask pH1962) (hmask pH1962) 1602 360 (true, H1962_cp2.1, H1962_cp2.2)) 1962 981 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1962_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1962_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1962_fin) true) H1962_seg1) H1962_seg2) (by decide) rfl H1962_fin ptTest_fst
noncomputable def I1962_cp1 : Nat × Nat := t7val% (fastRun pI1962 1 1132 (init pI1962) (init pI1962))
theorem I1962_seg1 : segOK pI1962 1 1132 (init pI1962) (init pI1962) I1962_cp1.1 I1962_cp1.2 = true := by
  decide +kernel
noncomputable def I1962_cp2 : Nat × Nat := t7val% (fastRun pI1962 1 1601 (init pI1962) (init pI1962))
theorem I1962_seg2 : segOK pI1962 1133 469 I1962_cp1.1 I1962_cp1.2 I1962_cp2.1 I1962_cp2.2 = true := by
  decide +kernel
theorem I1962_fin : (prmOK pI1962 1962 && intTest pI1962 (runFrom pI1962 (fmask pI1962) (cmask pI1962) (hmask pI1962) 1602 360 (true, I1962_cp2.1, I1962_cp2.2)) 1962 22 true) = true := by
  decide +kernel
theorem I1962_ok : RunOK pI1962 1962 (runFrom pI1962 (fmask pI1962) (cmask pI1962) (hmask pI1962) 1602 360 (true, I1962_cp2.1, I1962_cp2.2)) ∧ intTest pI1962 (runFrom pI1962 (fmask pI1962) (cmask pI1962) (hmask pI1962) 1602 360 (true, I1962_cp2.1, I1962_cp2.2)) 1962 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1962_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1962_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1962_fin) true) I1962_seg1) I1962_seg2) (by decide) rfl I1962_fin intTest_fst
theorem link1962 : linkOK pL1962 pH1962 pI1962 = true := by decide +kernel
theorem cvx1962 : ConvexBetweenHumps 1962 :=
  cvx_of L1962_ok H1962_ok I1962_ok link1962 (by decide)
theorem cenlink1962 : cenLinkOK pI1962 1962 = true := by decide +kernel
theorem cen1962 : CenterUniqueMin 1962 ∧ DipHyp 1962 ∧ OnePointHyps 1962 :=
  cen_of L1962_ok H1962_ok I1962_ok link1962 cenlink1962

/-! ### `N = 1963` -/

def pL1963 : Prm := ⟨81, 38, 40, 1965, 11, 18446744073709551616, 99854479394727180, 99854479394727180⟩
def pH1963 : Prm := ⟨81, 38, 40, 1965, 11, 18446744073709551616, 99855578906354956, 99855578906354956⟩
def pI1963 : Prm := ⟨68, 34, 31, 1965, 11, 18446744073709551616, 99854479394727180, 99855578906354956⟩
noncomputable def L1963_cp1 : Nat × Nat := t7val% (fastRun pL1963 1 1132 (init pL1963) (init pL1963))
theorem L1963_seg1 : segOK pL1963 1 1132 (init pL1963) (init pL1963) L1963_cp1.1 L1963_cp1.2 = true := by
  decide +kernel
noncomputable def L1963_cp2 : Nat × Nat := t7val% (fastRun pL1963 1 1602 (init pL1963) (init pL1963))
theorem L1963_seg2 : segOK pL1963 1133 470 L1963_cp1.1 L1963_cp1.2 L1963_cp2.1 L1963_cp2.2 = true := by
  decide +kernel
theorem L1963_fin : (prmOK pL1963 1963 && ptTest pL1963 (runFrom pL1963 (fmask pL1963) (cmask pL1963) (hmask pL1963) 1603 360 (true, L1963_cp2.1, L1963_cp2.2)) 1963 982 false) = true := by
  decide +kernel
theorem L1963_ok : RunOK pL1963 1963 (runFrom pL1963 (fmask pL1963) (cmask pL1963) (hmask pL1963) 1603 360 (true, L1963_cp2.1, L1963_cp2.2)) ∧ ptTest pL1963 (runFrom pL1963 (fmask pL1963) (cmask pL1963) (hmask pL1963) 1603 360 (true, L1963_cp2.1, L1963_cp2.2)) 1963 982 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1963_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1963_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1963_fin) true) L1963_seg1) L1963_seg2) (by decide) rfl L1963_fin ptTest_fst
noncomputable def H1963_cp1 : Nat × Nat := t7val% (fastRun pH1963 1 1132 (init pH1963) (init pH1963))
theorem H1963_seg1 : segOK pH1963 1 1132 (init pH1963) (init pH1963) H1963_cp1.1 H1963_cp1.2 = true := by
  decide +kernel
noncomputable def H1963_cp2 : Nat × Nat := t7val% (fastRun pH1963 1 1602 (init pH1963) (init pH1963))
theorem H1963_seg2 : segOK pH1963 1133 470 H1963_cp1.1 H1963_cp1.2 H1963_cp2.1 H1963_cp2.2 = true := by
  decide +kernel
theorem H1963_fin : (prmOK pH1963 1963 && ptTest pH1963 (runFrom pH1963 (fmask pH1963) (cmask pH1963) (hmask pH1963) 1603 360 (true, H1963_cp2.1, H1963_cp2.2)) 1963 982 true) = true := by
  decide +kernel
theorem H1963_ok : RunOK pH1963 1963 (runFrom pH1963 (fmask pH1963) (cmask pH1963) (hmask pH1963) 1603 360 (true, H1963_cp2.1, H1963_cp2.2)) ∧ ptTest pH1963 (runFrom pH1963 (fmask pH1963) (cmask pH1963) (hmask pH1963) 1603 360 (true, H1963_cp2.1, H1963_cp2.2)) 1963 982 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1963_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1963_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1963_fin) true) H1963_seg1) H1963_seg2) (by decide) rfl H1963_fin ptTest_fst
noncomputable def I1963_cp1 : Nat × Nat := t7val% (fastRun pI1963 1 1132 (init pI1963) (init pI1963))
theorem I1963_seg1 : segOK pI1963 1 1132 (init pI1963) (init pI1963) I1963_cp1.1 I1963_cp1.2 = true := by
  decide +kernel
noncomputable def I1963_cp2 : Nat × Nat := t7val% (fastRun pI1963 1 1602 (init pI1963) (init pI1963))
theorem I1963_seg2 : segOK pI1963 1133 470 I1963_cp1.1 I1963_cp1.2 I1963_cp2.1 I1963_cp2.2 = true := by
  decide +kernel
theorem I1963_fin : (prmOK pI1963 1963 && intTest pI1963 (runFrom pI1963 (fmask pI1963) (cmask pI1963) (hmask pI1963) 1603 360 (true, I1963_cp2.1, I1963_cp2.2)) 1963 22 false) = true := by
  decide +kernel
theorem I1963_ok : RunOK pI1963 1963 (runFrom pI1963 (fmask pI1963) (cmask pI1963) (hmask pI1963) 1603 360 (true, I1963_cp2.1, I1963_cp2.2)) ∧ intTest pI1963 (runFrom pI1963 (fmask pI1963) (cmask pI1963) (hmask pI1963) 1603 360 (true, I1963_cp2.1, I1963_cp2.2)) 1963 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1963_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1963_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1963_fin) true) I1963_seg1) I1963_seg2) (by decide) rfl I1963_fin intTest_fst
theorem link1963 : linkOK pL1963 pH1963 pI1963 = true := by decide +kernel
theorem cvx1963 : ConvexBetweenHumps 1963 :=
  cvx_of L1963_ok H1963_ok I1963_ok link1963 (by decide)

/-! ### `N = 1964` -/

def pL1964 : Prm := ⟨81, 38, 40, 1966, 11, 18446744073709551616, 99812660414659967, 99812660414659967⟩
def pH1964 : Prm := ⟨81, 38, 40, 1966, 11, 18446744073709551616, 99813759926287743, 99813759926287743⟩
def pI1964 : Prm := ⟨68, 34, 31, 1966, 11, 18446744073709551616, 99812660414659967, 99813759926287743⟩
noncomputable def L1964_cp1 : Nat × Nat := t7val% (fastRun pL1964 1 1133 (init pL1964) (init pL1964))
theorem L1964_seg1 : segOK pL1964 1 1133 (init pL1964) (init pL1964) L1964_cp1.1 L1964_cp1.2 = true := by
  decide +kernel
noncomputable def L1964_cp2 : Nat × Nat := t7val% (fastRun pL1964 1 1603 (init pL1964) (init pL1964))
theorem L1964_seg2 : segOK pL1964 1134 470 L1964_cp1.1 L1964_cp1.2 L1964_cp2.1 L1964_cp2.2 = true := by
  decide +kernel
theorem L1964_fin : (prmOK pL1964 1964 && ptTest pL1964 (runFrom pL1964 (fmask pL1964) (cmask pL1964) (hmask pL1964) 1604 360 (true, L1964_cp2.1, L1964_cp2.2)) 1964 982 false) = true := by
  decide +kernel
theorem L1964_ok : RunOK pL1964 1964 (runFrom pL1964 (fmask pL1964) (cmask pL1964) (hmask pL1964) 1604 360 (true, L1964_cp2.1, L1964_cp2.2)) ∧ ptTest pL1964 (runFrom pL1964 (fmask pL1964) (cmask pL1964) (hmask pL1964) 1604 360 (true, L1964_cp2.1, L1964_cp2.2)) 1964 982 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1964_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1964_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1964_fin) true) L1964_seg1) L1964_seg2) (by decide) rfl L1964_fin ptTest_fst
noncomputable def H1964_cp1 : Nat × Nat := t7val% (fastRun pH1964 1 1133 (init pH1964) (init pH1964))
theorem H1964_seg1 : segOK pH1964 1 1133 (init pH1964) (init pH1964) H1964_cp1.1 H1964_cp1.2 = true := by
  decide +kernel
noncomputable def H1964_cp2 : Nat × Nat := t7val% (fastRun pH1964 1 1603 (init pH1964) (init pH1964))
theorem H1964_seg2 : segOK pH1964 1134 470 H1964_cp1.1 H1964_cp1.2 H1964_cp2.1 H1964_cp2.2 = true := by
  decide +kernel
theorem H1964_fin : (prmOK pH1964 1964 && ptTest pH1964 (runFrom pH1964 (fmask pH1964) (cmask pH1964) (hmask pH1964) 1604 360 (true, H1964_cp2.1, H1964_cp2.2)) 1964 982 true) = true := by
  decide +kernel
theorem H1964_ok : RunOK pH1964 1964 (runFrom pH1964 (fmask pH1964) (cmask pH1964) (hmask pH1964) 1604 360 (true, H1964_cp2.1, H1964_cp2.2)) ∧ ptTest pH1964 (runFrom pH1964 (fmask pH1964) (cmask pH1964) (hmask pH1964) 1604 360 (true, H1964_cp2.1, H1964_cp2.2)) 1964 982 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1964_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1964_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1964_fin) true) H1964_seg1) H1964_seg2) (by decide) rfl H1964_fin ptTest_fst
noncomputable def I1964_cp1 : Nat × Nat := t7val% (fastRun pI1964 1 1133 (init pI1964) (init pI1964))
theorem I1964_seg1 : segOK pI1964 1 1133 (init pI1964) (init pI1964) I1964_cp1.1 I1964_cp1.2 = true := by
  decide +kernel
noncomputable def I1964_cp2 : Nat × Nat := t7val% (fastRun pI1964 1 1603 (init pI1964) (init pI1964))
theorem I1964_seg2 : segOK pI1964 1134 470 I1964_cp1.1 I1964_cp1.2 I1964_cp2.1 I1964_cp2.2 = true := by
  decide +kernel
theorem I1964_fin : (prmOK pI1964 1964 && intTest pI1964 (runFrom pI1964 (fmask pI1964) (cmask pI1964) (hmask pI1964) 1604 360 (true, I1964_cp2.1, I1964_cp2.2)) 1964 22 true) = true := by
  decide +kernel
theorem I1964_ok : RunOK pI1964 1964 (runFrom pI1964 (fmask pI1964) (cmask pI1964) (hmask pI1964) 1604 360 (true, I1964_cp2.1, I1964_cp2.2)) ∧ intTest pI1964 (runFrom pI1964 (fmask pI1964) (cmask pI1964) (hmask pI1964) 1604 360 (true, I1964_cp2.1, I1964_cp2.2)) 1964 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1964_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1964_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1964_fin) true) I1964_seg1) I1964_seg2) (by decide) rfl I1964_fin intTest_fst
theorem link1964 : linkOK pL1964 pH1964 pI1964 = true := by decide +kernel
theorem cvx1964 : ConvexBetweenHumps 1964 :=
  cvx_of L1964_ok H1964_ok I1964_ok link1964 (by decide)
theorem cenlink1964 : cenLinkOK pI1964 1964 = true := by decide +kernel
theorem cen1964 : CenterUniqueMin 1964 ∧ DipHyp 1964 ∧ OnePointHyps 1964 :=
  cen_of L1964_ok H1964_ok I1964_ok link1964 cenlink1964

/-! ### `N = 1965` -/

def pL1965 : Prm := ⟨81, 38, 40, 1967, 11, 18446744073709551616, 99770864654856132, 99770864654856132⟩
def pH1965 : Prm := ⟨81, 38, 40, 1967, 11, 18446744073709551616, 99771964166483908, 99771964166483908⟩
def pI1965 : Prm := ⟨68, 34, 31, 1967, 11, 18446744073709551616, 99770864654856132, 99771964166483908⟩
noncomputable def L1965_cp1 : Nat × Nat := t7val% (fastRun pL1965 1 1133 (init pL1965) (init pL1965))
theorem L1965_seg1 : segOK pL1965 1 1133 (init pL1965) (init pL1965) L1965_cp1.1 L1965_cp1.2 = true := by
  decide +kernel
noncomputable def L1965_cp2 : Nat × Nat := t7val% (fastRun pL1965 1 1603 (init pL1965) (init pL1965))
theorem L1965_seg2 : segOK pL1965 1134 470 L1965_cp1.1 L1965_cp1.2 L1965_cp2.1 L1965_cp2.2 = true := by
  decide +kernel
theorem L1965_fin : (prmOK pL1965 1965 && ptTest pL1965 (runFrom pL1965 (fmask pL1965) (cmask pL1965) (hmask pL1965) 1604 361 (true, L1965_cp2.1, L1965_cp2.2)) 1965 983 false) = true := by
  decide +kernel
theorem L1965_ok : RunOK pL1965 1965 (runFrom pL1965 (fmask pL1965) (cmask pL1965) (hmask pL1965) 1604 361 (true, L1965_cp2.1, L1965_cp2.2)) ∧ ptTest pL1965 (runFrom pL1965 (fmask pL1965) (cmask pL1965) (hmask pL1965) 1604 361 (true, L1965_cp2.1, L1965_cp2.2)) 1965 983 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1965_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1965_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1965_fin) true) L1965_seg1) L1965_seg2) (by decide) rfl L1965_fin ptTest_fst
noncomputable def H1965_cp1 : Nat × Nat := t7val% (fastRun pH1965 1 1133 (init pH1965) (init pH1965))
theorem H1965_seg1 : segOK pH1965 1 1133 (init pH1965) (init pH1965) H1965_cp1.1 H1965_cp1.2 = true := by
  decide +kernel
noncomputable def H1965_cp2 : Nat × Nat := t7val% (fastRun pH1965 1 1603 (init pH1965) (init pH1965))
theorem H1965_seg2 : segOK pH1965 1134 470 H1965_cp1.1 H1965_cp1.2 H1965_cp2.1 H1965_cp2.2 = true := by
  decide +kernel
theorem H1965_fin : (prmOK pH1965 1965 && ptTest pH1965 (runFrom pH1965 (fmask pH1965) (cmask pH1965) (hmask pH1965) 1604 361 (true, H1965_cp2.1, H1965_cp2.2)) 1965 983 true) = true := by
  decide +kernel
theorem H1965_ok : RunOK pH1965 1965 (runFrom pH1965 (fmask pH1965) (cmask pH1965) (hmask pH1965) 1604 361 (true, H1965_cp2.1, H1965_cp2.2)) ∧ ptTest pH1965 (runFrom pH1965 (fmask pH1965) (cmask pH1965) (hmask pH1965) 1604 361 (true, H1965_cp2.1, H1965_cp2.2)) 1965 983 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1965_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1965_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1965_fin) true) H1965_seg1) H1965_seg2) (by decide) rfl H1965_fin ptTest_fst
noncomputable def I1965_cp1 : Nat × Nat := t7val% (fastRun pI1965 1 1133 (init pI1965) (init pI1965))
theorem I1965_seg1 : segOK pI1965 1 1133 (init pI1965) (init pI1965) I1965_cp1.1 I1965_cp1.2 = true := by
  decide +kernel
noncomputable def I1965_cp2 : Nat × Nat := t7val% (fastRun pI1965 1 1603 (init pI1965) (init pI1965))
theorem I1965_seg2 : segOK pI1965 1134 470 I1965_cp1.1 I1965_cp1.2 I1965_cp2.1 I1965_cp2.2 = true := by
  decide +kernel
theorem I1965_fin : (prmOK pI1965 1965 && intTest pI1965 (runFrom pI1965 (fmask pI1965) (cmask pI1965) (hmask pI1965) 1604 361 (true, I1965_cp2.1, I1965_cp2.2)) 1965 22 false) = true := by
  decide +kernel
theorem I1965_ok : RunOK pI1965 1965 (runFrom pI1965 (fmask pI1965) (cmask pI1965) (hmask pI1965) 1604 361 (true, I1965_cp2.1, I1965_cp2.2)) ∧ intTest pI1965 (runFrom pI1965 (fmask pI1965) (cmask pI1965) (hmask pI1965) 1604 361 (true, I1965_cp2.1, I1965_cp2.2)) 1965 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1965_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1965_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1965_fin) true) I1965_seg1) I1965_seg2) (by decide) rfl I1965_fin intTest_fst
theorem link1965 : linkOK pL1965 pH1965 pI1965 = true := by decide +kernel
theorem cvx1965 : ConvexBetweenHumps 1965 :=
  cvx_of L1965_ok H1965_ok I1965_ok link1965 (by decide)

/-! ### `N = 1966` -/

def pL1966 : Prm := ⟨81, 38, 40, 1968, 11, 18446744073709551616, 99729121554419202, 99729121554419202⟩
def pH1966 : Prm := ⟨81, 38, 40, 1968, 11, 18446744073709551616, 99730221066046978, 99730221066046978⟩
def pI1966 : Prm := ⟨68, 34, 31, 1968, 11, 18446744073709551616, 99729121554419202, 99730221066046978⟩
noncomputable def L1966_cp1 : Nat × Nat := t7val% (fastRun pL1966 1 1134 (init pL1966) (init pL1966))
theorem L1966_seg1 : segOK pL1966 1 1134 (init pL1966) (init pL1966) L1966_cp1.1 L1966_cp1.2 = true := by
  decide +kernel
noncomputable def L1966_cp2 : Nat × Nat := t7val% (fastRun pL1966 1 1604 (init pL1966) (init pL1966))
theorem L1966_seg2 : segOK pL1966 1135 470 L1966_cp1.1 L1966_cp1.2 L1966_cp2.1 L1966_cp2.2 = true := by
  decide +kernel
theorem L1966_fin : (prmOK pL1966 1966 && ptTest pL1966 (runFrom pL1966 (fmask pL1966) (cmask pL1966) (hmask pL1966) 1605 361 (true, L1966_cp2.1, L1966_cp2.2)) 1966 983 false) = true := by
  decide +kernel
theorem L1966_ok : RunOK pL1966 1966 (runFrom pL1966 (fmask pL1966) (cmask pL1966) (hmask pL1966) 1605 361 (true, L1966_cp2.1, L1966_cp2.2)) ∧ ptTest pL1966 (runFrom pL1966 (fmask pL1966) (cmask pL1966) (hmask pL1966) 1605 361 (true, L1966_cp2.1, L1966_cp2.2)) 1966 983 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1966_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1966_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1966_fin) true) L1966_seg1) L1966_seg2) (by decide) rfl L1966_fin ptTest_fst
noncomputable def H1966_cp1 : Nat × Nat := t7val% (fastRun pH1966 1 1134 (init pH1966) (init pH1966))
theorem H1966_seg1 : segOK pH1966 1 1134 (init pH1966) (init pH1966) H1966_cp1.1 H1966_cp1.2 = true := by
  decide +kernel
noncomputable def H1966_cp2 : Nat × Nat := t7val% (fastRun pH1966 1 1604 (init pH1966) (init pH1966))
theorem H1966_seg2 : segOK pH1966 1135 470 H1966_cp1.1 H1966_cp1.2 H1966_cp2.1 H1966_cp2.2 = true := by
  decide +kernel
theorem H1966_fin : (prmOK pH1966 1966 && ptTest pH1966 (runFrom pH1966 (fmask pH1966) (cmask pH1966) (hmask pH1966) 1605 361 (true, H1966_cp2.1, H1966_cp2.2)) 1966 983 true) = true := by
  decide +kernel
theorem H1966_ok : RunOK pH1966 1966 (runFrom pH1966 (fmask pH1966) (cmask pH1966) (hmask pH1966) 1605 361 (true, H1966_cp2.1, H1966_cp2.2)) ∧ ptTest pH1966 (runFrom pH1966 (fmask pH1966) (cmask pH1966) (hmask pH1966) 1605 361 (true, H1966_cp2.1, H1966_cp2.2)) 1966 983 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1966_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1966_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1966_fin) true) H1966_seg1) H1966_seg2) (by decide) rfl H1966_fin ptTest_fst
noncomputable def I1966_cp1 : Nat × Nat := t7val% (fastRun pI1966 1 1134 (init pI1966) (init pI1966))
theorem I1966_seg1 : segOK pI1966 1 1134 (init pI1966) (init pI1966) I1966_cp1.1 I1966_cp1.2 = true := by
  decide +kernel
noncomputable def I1966_cp2 : Nat × Nat := t7val% (fastRun pI1966 1 1604 (init pI1966) (init pI1966))
theorem I1966_seg2 : segOK pI1966 1135 470 I1966_cp1.1 I1966_cp1.2 I1966_cp2.1 I1966_cp2.2 = true := by
  decide +kernel
theorem I1966_fin : (prmOK pI1966 1966 && intTest pI1966 (runFrom pI1966 (fmask pI1966) (cmask pI1966) (hmask pI1966) 1605 361 (true, I1966_cp2.1, I1966_cp2.2)) 1966 22 true) = true := by
  decide +kernel
theorem I1966_ok : RunOK pI1966 1966 (runFrom pI1966 (fmask pI1966) (cmask pI1966) (hmask pI1966) 1605 361 (true, I1966_cp2.1, I1966_cp2.2)) ∧ intTest pI1966 (runFrom pI1966 (fmask pI1966) (cmask pI1966) (hmask pI1966) 1605 361 (true, I1966_cp2.1, I1966_cp2.2)) 1966 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1966_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1966_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1966_fin) true) I1966_seg1) I1966_seg2) (by decide) rfl I1966_fin intTest_fst
theorem link1966 : linkOK pL1966 pH1966 pI1966 = true := by decide +kernel
theorem cvx1966 : ConvexBetweenHumps 1966 :=
  cvx_of L1966_ok H1966_ok I1966_ok link1966 (by decide)
theorem cenlink1966 : cenLinkOK pI1966 1966 = true := by decide +kernel
theorem cen1966 : CenterUniqueMin 1966 ∧ DipHyp 1966 ∧ OnePointHyps 1966 :=
  cen_of L1966_ok H1966_ok I1966_ok link1966 cenlink1966

/-! ### `N = 1967` -/

def pL1967 : Prm := ⟨81, 38, 40, 1969, 11, 18446744073709551616, 99687401613426735, 99687401613426735⟩
def pH1967 : Prm := ⟨81, 38, 40, 1969, 11, 18446744073709551616, 99688501125054511, 99688501125054511⟩
def pI1967 : Prm := ⟨68, 34, 31, 1969, 11, 18446744073709551616, 99687401613426735, 99688501125054511⟩
noncomputable def L1967_cp1 : Nat × Nat := t7val% (fastRun pL1967 1 1135 (init pL1967) (init pL1967))
theorem L1967_seg1 : segOK pL1967 1 1135 (init pL1967) (init pL1967) L1967_cp1.1 L1967_cp1.2 = true := by
  decide +kernel
noncomputable def L1967_cp2 : Nat × Nat := t7val% (fastRun pL1967 1 1605 (init pL1967) (init pL1967))
theorem L1967_seg2 : segOK pL1967 1136 470 L1967_cp1.1 L1967_cp1.2 L1967_cp2.1 L1967_cp2.2 = true := by
  decide +kernel
theorem L1967_fin : (prmOK pL1967 1967 && ptTest pL1967 (runFrom pL1967 (fmask pL1967) (cmask pL1967) (hmask pL1967) 1606 361 (true, L1967_cp2.1, L1967_cp2.2)) 1967 984 false) = true := by
  decide +kernel
theorem L1967_ok : RunOK pL1967 1967 (runFrom pL1967 (fmask pL1967) (cmask pL1967) (hmask pL1967) 1606 361 (true, L1967_cp2.1, L1967_cp2.2)) ∧ ptTest pL1967 (runFrom pL1967 (fmask pL1967) (cmask pL1967) (hmask pL1967) 1606 361 (true, L1967_cp2.1, L1967_cp2.2)) 1967 984 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1967_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1967_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1967_fin) true) L1967_seg1) L1967_seg2) (by decide) rfl L1967_fin ptTest_fst
noncomputable def H1967_cp1 : Nat × Nat := t7val% (fastRun pH1967 1 1135 (init pH1967) (init pH1967))
theorem H1967_seg1 : segOK pH1967 1 1135 (init pH1967) (init pH1967) H1967_cp1.1 H1967_cp1.2 = true := by
  decide +kernel
noncomputable def H1967_cp2 : Nat × Nat := t7val% (fastRun pH1967 1 1605 (init pH1967) (init pH1967))
theorem H1967_seg2 : segOK pH1967 1136 470 H1967_cp1.1 H1967_cp1.2 H1967_cp2.1 H1967_cp2.2 = true := by
  decide +kernel
theorem H1967_fin : (prmOK pH1967 1967 && ptTest pH1967 (runFrom pH1967 (fmask pH1967) (cmask pH1967) (hmask pH1967) 1606 361 (true, H1967_cp2.1, H1967_cp2.2)) 1967 984 true) = true := by
  decide +kernel
theorem H1967_ok : RunOK pH1967 1967 (runFrom pH1967 (fmask pH1967) (cmask pH1967) (hmask pH1967) 1606 361 (true, H1967_cp2.1, H1967_cp2.2)) ∧ ptTest pH1967 (runFrom pH1967 (fmask pH1967) (cmask pH1967) (hmask pH1967) 1606 361 (true, H1967_cp2.1, H1967_cp2.2)) 1967 984 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1967_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1967_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1967_fin) true) H1967_seg1) H1967_seg2) (by decide) rfl H1967_fin ptTest_fst
noncomputable def I1967_cp1 : Nat × Nat := t7val% (fastRun pI1967 1 1135 (init pI1967) (init pI1967))
theorem I1967_seg1 : segOK pI1967 1 1135 (init pI1967) (init pI1967) I1967_cp1.1 I1967_cp1.2 = true := by
  decide +kernel
noncomputable def I1967_cp2 : Nat × Nat := t7val% (fastRun pI1967 1 1605 (init pI1967) (init pI1967))
theorem I1967_seg2 : segOK pI1967 1136 470 I1967_cp1.1 I1967_cp1.2 I1967_cp2.1 I1967_cp2.2 = true := by
  decide +kernel
theorem I1967_fin : (prmOK pI1967 1967 && intTest pI1967 (runFrom pI1967 (fmask pI1967) (cmask pI1967) (hmask pI1967) 1606 361 (true, I1967_cp2.1, I1967_cp2.2)) 1967 22 false) = true := by
  decide +kernel
theorem I1967_ok : RunOK pI1967 1967 (runFrom pI1967 (fmask pI1967) (cmask pI1967) (hmask pI1967) 1606 361 (true, I1967_cp2.1, I1967_cp2.2)) ∧ intTest pI1967 (runFrom pI1967 (fmask pI1967) (cmask pI1967) (hmask pI1967) 1606 361 (true, I1967_cp2.1, I1967_cp2.2)) 1967 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1967_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1967_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1967_fin) true) I1967_seg1) I1967_seg2) (by decide) rfl I1967_fin intTest_fst
theorem link1967 : linkOK pL1967 pH1967 pI1967 = true := by decide +kernel
theorem cvx1967 : ConvexBetweenHumps 1967 :=
  cvx_of L1967_ok H1967_ok I1967_ok link1967 (by decide)

/-! ### `N = 1968` -/

def pL1968 : Prm := ⟨81, 38, 40, 1970, 11, 18446744073709551616, 99645734180002916, 99645734180002916⟩
def pH1968 : Prm := ⟨81, 38, 40, 1970, 11, 18446744073709551616, 99646833691630692, 99646833691630692⟩
def pI1968 : Prm := ⟨68, 34, 31, 1970, 11, 18446744073709551616, 99645734180002916, 99646833691630692⟩
noncomputable def L1968_cp1 : Nat × Nat := t7val% (fastRun pL1968 1 1135 (init pL1968) (init pL1968))
theorem L1968_seg1 : segOK pL1968 1 1135 (init pL1968) (init pL1968) L1968_cp1.1 L1968_cp1.2 = true := by
  decide +kernel
noncomputable def L1968_cp2 : Nat × Nat := t7val% (fastRun pL1968 1 1606 (init pL1968) (init pL1968))
theorem L1968_seg2 : segOK pL1968 1136 471 L1968_cp1.1 L1968_cp1.2 L1968_cp2.1 L1968_cp2.2 = true := by
  decide +kernel
theorem L1968_fin : (prmOK pL1968 1968 && ptTest pL1968 (runFrom pL1968 (fmask pL1968) (cmask pL1968) (hmask pL1968) 1607 361 (true, L1968_cp2.1, L1968_cp2.2)) 1968 984 false) = true := by
  decide +kernel
theorem L1968_ok : RunOK pL1968 1968 (runFrom pL1968 (fmask pL1968) (cmask pL1968) (hmask pL1968) 1607 361 (true, L1968_cp2.1, L1968_cp2.2)) ∧ ptTest pL1968 (runFrom pL1968 (fmask pL1968) (cmask pL1968) (hmask pL1968) 1607 361 (true, L1968_cp2.1, L1968_cp2.2)) 1968 984 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1968_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1968_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1968_fin) true) L1968_seg1) L1968_seg2) (by decide) rfl L1968_fin ptTest_fst
noncomputable def H1968_cp1 : Nat × Nat := t7val% (fastRun pH1968 1 1135 (init pH1968) (init pH1968))
theorem H1968_seg1 : segOK pH1968 1 1135 (init pH1968) (init pH1968) H1968_cp1.1 H1968_cp1.2 = true := by
  decide +kernel
noncomputable def H1968_cp2 : Nat × Nat := t7val% (fastRun pH1968 1 1606 (init pH1968) (init pH1968))
theorem H1968_seg2 : segOK pH1968 1136 471 H1968_cp1.1 H1968_cp1.2 H1968_cp2.1 H1968_cp2.2 = true := by
  decide +kernel
theorem H1968_fin : (prmOK pH1968 1968 && ptTest pH1968 (runFrom pH1968 (fmask pH1968) (cmask pH1968) (hmask pH1968) 1607 361 (true, H1968_cp2.1, H1968_cp2.2)) 1968 984 true) = true := by
  decide +kernel
theorem H1968_ok : RunOK pH1968 1968 (runFrom pH1968 (fmask pH1968) (cmask pH1968) (hmask pH1968) 1607 361 (true, H1968_cp2.1, H1968_cp2.2)) ∧ ptTest pH1968 (runFrom pH1968 (fmask pH1968) (cmask pH1968) (hmask pH1968) 1607 361 (true, H1968_cp2.1, H1968_cp2.2)) 1968 984 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1968_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1968_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1968_fin) true) H1968_seg1) H1968_seg2) (by decide) rfl H1968_fin ptTest_fst
noncomputable def I1968_cp1 : Nat × Nat := t7val% (fastRun pI1968 1 1135 (init pI1968) (init pI1968))
theorem I1968_seg1 : segOK pI1968 1 1135 (init pI1968) (init pI1968) I1968_cp1.1 I1968_cp1.2 = true := by
  decide +kernel
noncomputable def I1968_cp2 : Nat × Nat := t7val% (fastRun pI1968 1 1606 (init pI1968) (init pI1968))
theorem I1968_seg2 : segOK pI1968 1136 471 I1968_cp1.1 I1968_cp1.2 I1968_cp2.1 I1968_cp2.2 = true := by
  decide +kernel
theorem I1968_fin : (prmOK pI1968 1968 && intTest pI1968 (runFrom pI1968 (fmask pI1968) (cmask pI1968) (hmask pI1968) 1607 361 (true, I1968_cp2.1, I1968_cp2.2)) 1968 22 true) = true := by
  decide +kernel
theorem I1968_ok : RunOK pI1968 1968 (runFrom pI1968 (fmask pI1968) (cmask pI1968) (hmask pI1968) 1607 361 (true, I1968_cp2.1, I1968_cp2.2)) ∧ intTest pI1968 (runFrom pI1968 (fmask pI1968) (cmask pI1968) (hmask pI1968) 1607 361 (true, I1968_cp2.1, I1968_cp2.2)) 1968 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1968_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1968_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1968_fin) true) I1968_seg1) I1968_seg2) (by decide) rfl I1968_fin intTest_fst
theorem link1968 : linkOK pL1968 pH1968 pI1968 = true := by decide +kernel
theorem cvx1968 : ConvexBetweenHumps 1968 :=
  cvx_of L1968_ok H1968_ok I1968_ok link1968 (by decide)
theorem cenlink1968 : cenLinkOK pI1968 1968 = true := by decide +kernel
theorem cen1968 : CenterUniqueMin 1968 ∧ DipHyp 1968 ∧ OnePointHyps 1968 :=
  cen_of L1968_ok H1968_ok I1968_ok link1968 cenlink1968

/-! ### `N = 1969` -/

def pL1969 : Prm := ⟨81, 38, 40, 1971, 11, 18446744073709551616, 99604089845444452, 99604089845444452⟩
def pH1969 : Prm := ⟨81, 38, 40, 1971, 11, 18446744073709551616, 99605189357072228, 99605189357072228⟩
def pI1969 : Prm := ⟨68, 34, 31, 1971, 11, 18446744073709551616, 99604089845444452, 99605189357072228⟩
noncomputable def L1969_cp1 : Nat × Nat := t7val% (fastRun pL1969 1 1136 (init pL1969) (init pL1969))
theorem L1969_seg1 : segOK pL1969 1 1136 (init pL1969) (init pL1969) L1969_cp1.1 L1969_cp1.2 = true := by
  decide +kernel
noncomputable def L1969_cp2 : Nat × Nat := t7val% (fastRun pL1969 1 1607 (init pL1969) (init pL1969))
theorem L1969_seg2 : segOK pL1969 1137 471 L1969_cp1.1 L1969_cp1.2 L1969_cp2.1 L1969_cp2.2 = true := by
  decide +kernel
theorem L1969_fin : (prmOK pL1969 1969 && ptTest pL1969 (runFrom pL1969 (fmask pL1969) (cmask pL1969) (hmask pL1969) 1608 361 (true, L1969_cp2.1, L1969_cp2.2)) 1969 985 false) = true := by
  decide +kernel
theorem L1969_ok : RunOK pL1969 1969 (runFrom pL1969 (fmask pL1969) (cmask pL1969) (hmask pL1969) 1608 361 (true, L1969_cp2.1, L1969_cp2.2)) ∧ ptTest pL1969 (runFrom pL1969 (fmask pL1969) (cmask pL1969) (hmask pL1969) 1608 361 (true, L1969_cp2.1, L1969_cp2.2)) 1969 985 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1969_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1969_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1969_fin) true) L1969_seg1) L1969_seg2) (by decide) rfl L1969_fin ptTest_fst
noncomputable def H1969_cp1 : Nat × Nat := t7val% (fastRun pH1969 1 1136 (init pH1969) (init pH1969))
theorem H1969_seg1 : segOK pH1969 1 1136 (init pH1969) (init pH1969) H1969_cp1.1 H1969_cp1.2 = true := by
  decide +kernel
noncomputable def H1969_cp2 : Nat × Nat := t7val% (fastRun pH1969 1 1607 (init pH1969) (init pH1969))
theorem H1969_seg2 : segOK pH1969 1137 471 H1969_cp1.1 H1969_cp1.2 H1969_cp2.1 H1969_cp2.2 = true := by
  decide +kernel
theorem H1969_fin : (prmOK pH1969 1969 && ptTest pH1969 (runFrom pH1969 (fmask pH1969) (cmask pH1969) (hmask pH1969) 1608 361 (true, H1969_cp2.1, H1969_cp2.2)) 1969 985 true) = true := by
  decide +kernel
theorem H1969_ok : RunOK pH1969 1969 (runFrom pH1969 (fmask pH1969) (cmask pH1969) (hmask pH1969) 1608 361 (true, H1969_cp2.1, H1969_cp2.2)) ∧ ptTest pH1969 (runFrom pH1969 (fmask pH1969) (cmask pH1969) (hmask pH1969) 1608 361 (true, H1969_cp2.1, H1969_cp2.2)) 1969 985 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1969_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1969_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1969_fin) true) H1969_seg1) H1969_seg2) (by decide) rfl H1969_fin ptTest_fst
noncomputable def I1969_cp1 : Nat × Nat := t7val% (fastRun pI1969 1 1136 (init pI1969) (init pI1969))
theorem I1969_seg1 : segOK pI1969 1 1136 (init pI1969) (init pI1969) I1969_cp1.1 I1969_cp1.2 = true := by
  decide +kernel
noncomputable def I1969_cp2 : Nat × Nat := t7val% (fastRun pI1969 1 1607 (init pI1969) (init pI1969))
theorem I1969_seg2 : segOK pI1969 1137 471 I1969_cp1.1 I1969_cp1.2 I1969_cp2.1 I1969_cp2.2 = true := by
  decide +kernel
theorem I1969_fin : (prmOK pI1969 1969 && intTest pI1969 (runFrom pI1969 (fmask pI1969) (cmask pI1969) (hmask pI1969) 1608 361 (true, I1969_cp2.1, I1969_cp2.2)) 1969 22 false) = true := by
  decide +kernel
theorem I1969_ok : RunOK pI1969 1969 (runFrom pI1969 (fmask pI1969) (cmask pI1969) (hmask pI1969) 1608 361 (true, I1969_cp2.1, I1969_cp2.2)) ∧ intTest pI1969 (runFrom pI1969 (fmask pI1969) (cmask pI1969) (hmask pI1969) 1608 361 (true, I1969_cp2.1, I1969_cp2.2)) 1969 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1969_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1969_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1969_fin) true) I1969_seg1) I1969_seg2) (by decide) rfl I1969_fin intTest_fst
theorem link1969 : linkOK pL1969 pH1969 pI1969 = true := by decide +kernel
theorem cvx1969 : ConvexBetweenHumps 1969 :=
  cvx_of L1969_ok H1969_ok I1969_ok link1969 (by decide)

/-! ### The range -/

theorem cvx_1960_1969 {N : ℕ} (h1 : 1960 ≤ N) (h2 : N ≤ 1969) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1964
  · by_cases h4 : N ≤ 1961
    · by_cases h6 : N ≤ 1960
      · obtain rfl : N = 1960 := by omega
        exact cvx1960
      · obtain rfl : N = 1961 := by omega
        exact cvx1961
    · by_cases h6 : N ≤ 1962
      · obtain rfl : N = 1962 := by omega
        exact cvx1962
      · by_cases h8 : N ≤ 1963
        · obtain rfl : N = 1963 := by omega
          exact cvx1963
        · obtain rfl : N = 1964 := by omega
          exact cvx1964
  · by_cases h4 : N ≤ 1966
    · by_cases h6 : N ≤ 1965
      · obtain rfl : N = 1965 := by omega
        exact cvx1965
      · obtain rfl : N = 1966 := by omega
        exact cvx1966
    · by_cases h6 : N ≤ 1967
      · obtain rfl : N = 1967 := by omega
        exact cvx1967
      · by_cases h8 : N ≤ 1968
        · obtain rfl : N = 1968 := by omega
          exact cvx1968
        · obtain rfl : N = 1969 := by omega
          exact cvx1969

theorem cen_1960_1969 {N : ℕ} (h1 : 1960 ≤ N) (h2 : N ≤ 1969) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1962
  · by_cases h4 : N ≤ 1960
    · obtain rfl : N = 1960 := by omega
      exact cen1960
    · obtain rfl : N = 1962 := by omega
      exact cen1962
  · by_cases h4 : N ≤ 1964
    · obtain rfl : N = 1964 := by omega
      exact cen1964
    · by_cases h6 : N ≤ 1966
      · obtain rfl : N = 1966 := by omega
        exact cen1966
      · obtain rfl : N = 1968 := by omega
        exact cen1968

end Kagey131.PaperD.T7
