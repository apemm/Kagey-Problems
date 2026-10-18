import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1980, …, 1989` (generated)

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

/-! ### `N = 1980` -/

def pL1980 : Prm := ⟨81, 38, 40, 1982, 11, 18446744073709551616, 99148567493051634, 99148567493051634⟩
def pH1980 : Prm := ⟨81, 38, 40, 1982, 11, 18446744073709551616, 99149667004679410, 99149667004679410⟩
def pI1980 : Prm := ⟨68, 34, 31, 1982, 11, 18446744073709551616, 99148567493051634, 99149667004679410⟩
noncomputable def L1980_cp1 : Nat × Nat := t7val% (fastRun pL1980 1 1142 (init pL1980) (init pL1980))
theorem L1980_seg1 : segOK pL1980 1 1142 (init pL1980) (init pL1980) L1980_cp1.1 L1980_cp1.2 = true := by
  decide +kernel
noncomputable def L1980_cp2 : Nat × Nat := t7val% (fastRun pL1980 1 1616 (init pL1980) (init pL1980))
theorem L1980_seg2 : segOK pL1980 1143 474 L1980_cp1.1 L1980_cp1.2 L1980_cp2.1 L1980_cp2.2 = true := by
  decide +kernel
theorem L1980_fin : (prmOK pL1980 1980 && ptTest pL1980 (runFrom pL1980 (fmask pL1980) (cmask pL1980) (hmask pL1980) 1617 363 (true, L1980_cp2.1, L1980_cp2.2)) 1980 990 false) = true := by
  decide +kernel
theorem L1980_ok : RunOK pL1980 1980 (runFrom pL1980 (fmask pL1980) (cmask pL1980) (hmask pL1980) 1617 363 (true, L1980_cp2.1, L1980_cp2.2)) ∧ ptTest pL1980 (runFrom pL1980 (fmask pL1980) (cmask pL1980) (hmask pL1980) 1617 363 (true, L1980_cp2.1, L1980_cp2.2)) 1980 990 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1980_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1980_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1980_fin) true) L1980_seg1) L1980_seg2) (by decide) rfl L1980_fin ptTest_fst
noncomputable def H1980_cp1 : Nat × Nat := t7val% (fastRun pH1980 1 1142 (init pH1980) (init pH1980))
theorem H1980_seg1 : segOK pH1980 1 1142 (init pH1980) (init pH1980) H1980_cp1.1 H1980_cp1.2 = true := by
  decide +kernel
noncomputable def H1980_cp2 : Nat × Nat := t7val% (fastRun pH1980 1 1616 (init pH1980) (init pH1980))
theorem H1980_seg2 : segOK pH1980 1143 474 H1980_cp1.1 H1980_cp1.2 H1980_cp2.1 H1980_cp2.2 = true := by
  decide +kernel
theorem H1980_fin : (prmOK pH1980 1980 && ptTest pH1980 (runFrom pH1980 (fmask pH1980) (cmask pH1980) (hmask pH1980) 1617 363 (true, H1980_cp2.1, H1980_cp2.2)) 1980 990 true) = true := by
  decide +kernel
theorem H1980_ok : RunOK pH1980 1980 (runFrom pH1980 (fmask pH1980) (cmask pH1980) (hmask pH1980) 1617 363 (true, H1980_cp2.1, H1980_cp2.2)) ∧ ptTest pH1980 (runFrom pH1980 (fmask pH1980) (cmask pH1980) (hmask pH1980) 1617 363 (true, H1980_cp2.1, H1980_cp2.2)) 1980 990 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1980_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1980_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1980_fin) true) H1980_seg1) H1980_seg2) (by decide) rfl H1980_fin ptTest_fst
noncomputable def I1980_cp1 : Nat × Nat := t7val% (fastRun pI1980 1 1142 (init pI1980) (init pI1980))
theorem I1980_seg1 : segOK pI1980 1 1142 (init pI1980) (init pI1980) I1980_cp1.1 I1980_cp1.2 = true := by
  decide +kernel
noncomputable def I1980_cp2 : Nat × Nat := t7val% (fastRun pI1980 1 1616 (init pI1980) (init pI1980))
theorem I1980_seg2 : segOK pI1980 1143 474 I1980_cp1.1 I1980_cp1.2 I1980_cp2.1 I1980_cp2.2 = true := by
  decide +kernel
theorem I1980_fin : (prmOK pI1980 1980 && intTest pI1980 (runFrom pI1980 (fmask pI1980) (cmask pI1980) (hmask pI1980) 1617 363 (true, I1980_cp2.1, I1980_cp2.2)) 1980 22 true) = true := by
  decide +kernel
theorem I1980_ok : RunOK pI1980 1980 (runFrom pI1980 (fmask pI1980) (cmask pI1980) (hmask pI1980) 1617 363 (true, I1980_cp2.1, I1980_cp2.2)) ∧ intTest pI1980 (runFrom pI1980 (fmask pI1980) (cmask pI1980) (hmask pI1980) 1617 363 (true, I1980_cp2.1, I1980_cp2.2)) 1980 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1980_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1980_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1980_fin) true) I1980_seg1) I1980_seg2) (by decide) rfl I1980_fin intTest_fst
theorem link1980 : linkOK pL1980 pH1980 pI1980 = true := by decide +kernel
theorem cvx1980 : ConvexBetweenHumps 1980 :=
  cvx_of L1980_ok H1980_ok I1980_ok link1980 (by decide)
theorem cenlink1980 : cenLinkOK pI1980 1980 = true := by decide +kernel
theorem cen1980 : CenterUniqueMin 1980 ∧ DipHyp 1980 ∧ OnePointHyps 1980 :=
  cen_of L1980_ok H1980_ok I1980_ok link1980 cenlink1980

/-! ### `N = 1981` -/

def pL1981 : Prm := ⟨81, 38, 40, 1983, 11, 18446744073709551616, 99107372381629187, 99107372381629187⟩
def pH1981 : Prm := ⟨81, 38, 40, 1983, 11, 18446744073709551616, 99108471893256963, 99108471893256963⟩
def pI1981 : Prm := ⟨68, 34, 31, 1983, 11, 18446744073709551616, 99107372381629187, 99108471893256963⟩
noncomputable def L1981_cp1 : Nat × Nat := t7val% (fastRun pL1981 1 1143 (init pL1981) (init pL1981))
theorem L1981_seg1 : segOK pL1981 1 1143 (init pL1981) (init pL1981) L1981_cp1.1 L1981_cp1.2 = true := by
  decide +kernel
noncomputable def L1981_cp2 : Nat × Nat := t7val% (fastRun pL1981 1 1616 (init pL1981) (init pL1981))
theorem L1981_seg2 : segOK pL1981 1144 473 L1981_cp1.1 L1981_cp1.2 L1981_cp2.1 L1981_cp2.2 = true := by
  decide +kernel
theorem L1981_fin : (prmOK pL1981 1981 && ptTest pL1981 (runFrom pL1981 (fmask pL1981) (cmask pL1981) (hmask pL1981) 1617 364 (true, L1981_cp2.1, L1981_cp2.2)) 1981 991 false) = true := by
  decide +kernel
theorem L1981_ok : RunOK pL1981 1981 (runFrom pL1981 (fmask pL1981) (cmask pL1981) (hmask pL1981) 1617 364 (true, L1981_cp2.1, L1981_cp2.2)) ∧ ptTest pL1981 (runFrom pL1981 (fmask pL1981) (cmask pL1981) (hmask pL1981) 1617 364 (true, L1981_cp2.1, L1981_cp2.2)) 1981 991 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1981_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1981_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1981_fin) true) L1981_seg1) L1981_seg2) (by decide) rfl L1981_fin ptTest_fst
noncomputable def H1981_cp1 : Nat × Nat := t7val% (fastRun pH1981 1 1143 (init pH1981) (init pH1981))
theorem H1981_seg1 : segOK pH1981 1 1143 (init pH1981) (init pH1981) H1981_cp1.1 H1981_cp1.2 = true := by
  decide +kernel
noncomputable def H1981_cp2 : Nat × Nat := t7val% (fastRun pH1981 1 1616 (init pH1981) (init pH1981))
theorem H1981_seg2 : segOK pH1981 1144 473 H1981_cp1.1 H1981_cp1.2 H1981_cp2.1 H1981_cp2.2 = true := by
  decide +kernel
theorem H1981_fin : (prmOK pH1981 1981 && ptTest pH1981 (runFrom pH1981 (fmask pH1981) (cmask pH1981) (hmask pH1981) 1617 364 (true, H1981_cp2.1, H1981_cp2.2)) 1981 991 true) = true := by
  decide +kernel
theorem H1981_ok : RunOK pH1981 1981 (runFrom pH1981 (fmask pH1981) (cmask pH1981) (hmask pH1981) 1617 364 (true, H1981_cp2.1, H1981_cp2.2)) ∧ ptTest pH1981 (runFrom pH1981 (fmask pH1981) (cmask pH1981) (hmask pH1981) 1617 364 (true, H1981_cp2.1, H1981_cp2.2)) 1981 991 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1981_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1981_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1981_fin) true) H1981_seg1) H1981_seg2) (by decide) rfl H1981_fin ptTest_fst
noncomputable def I1981_cp1 : Nat × Nat := t7val% (fastRun pI1981 1 1143 (init pI1981) (init pI1981))
theorem I1981_seg1 : segOK pI1981 1 1143 (init pI1981) (init pI1981) I1981_cp1.1 I1981_cp1.2 = true := by
  decide +kernel
noncomputable def I1981_cp2 : Nat × Nat := t7val% (fastRun pI1981 1 1616 (init pI1981) (init pI1981))
theorem I1981_seg2 : segOK pI1981 1144 473 I1981_cp1.1 I1981_cp1.2 I1981_cp2.1 I1981_cp2.2 = true := by
  decide +kernel
theorem I1981_fin : (prmOK pI1981 1981 && intTest pI1981 (runFrom pI1981 (fmask pI1981) (cmask pI1981) (hmask pI1981) 1617 364 (true, I1981_cp2.1, I1981_cp2.2)) 1981 22 false) = true := by
  decide +kernel
theorem I1981_ok : RunOK pI1981 1981 (runFrom pI1981 (fmask pI1981) (cmask pI1981) (hmask pI1981) 1617 364 (true, I1981_cp2.1, I1981_cp2.2)) ∧ intTest pI1981 (runFrom pI1981 (fmask pI1981) (cmask pI1981) (hmask pI1981) 1617 364 (true, I1981_cp2.1, I1981_cp2.2)) 1981 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1981_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1981_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1981_fin) true) I1981_seg1) I1981_seg2) (by decide) rfl I1981_fin intTest_fst
theorem link1981 : linkOK pL1981 pH1981 pI1981 = true := by decide +kernel
theorem cvx1981 : ConvexBetweenHumps 1981 :=
  cvx_of L1981_ok H1981_ok I1981_ok link1981 (by decide)

/-! ### `N = 1982` -/

def pL1982 : Prm := ⟨81, 38, 40, 1984, 11, 18446744073709551616, 99066228731476063, 99066228731476063⟩
def pH1982 : Prm := ⟨81, 38, 40, 1984, 11, 18446744073709551616, 99067328243103839, 99067328243103839⟩
def pI1982 : Prm := ⟨68, 34, 31, 1984, 11, 18446744073709551616, 99066228731476063, 99067328243103839⟩
noncomputable def L1982_cp1 : Nat × Nat := t7val% (fastRun pL1982 1 1143 (init pL1982) (init pL1982))
theorem L1982_seg1 : segOK pL1982 1 1143 (init pL1982) (init pL1982) L1982_cp1.1 L1982_cp1.2 = true := by
  decide +kernel
noncomputable def L1982_cp2 : Nat × Nat := t7val% (fastRun pL1982 1 1617 (init pL1982) (init pL1982))
theorem L1982_seg2 : segOK pL1982 1144 474 L1982_cp1.1 L1982_cp1.2 L1982_cp2.1 L1982_cp2.2 = true := by
  decide +kernel
theorem L1982_fin : (prmOK pL1982 1982 && ptTest pL1982 (runFrom pL1982 (fmask pL1982) (cmask pL1982) (hmask pL1982) 1618 364 (true, L1982_cp2.1, L1982_cp2.2)) 1982 991 false) = true := by
  decide +kernel
theorem L1982_ok : RunOK pL1982 1982 (runFrom pL1982 (fmask pL1982) (cmask pL1982) (hmask pL1982) 1618 364 (true, L1982_cp2.1, L1982_cp2.2)) ∧ ptTest pL1982 (runFrom pL1982 (fmask pL1982) (cmask pL1982) (hmask pL1982) 1618 364 (true, L1982_cp2.1, L1982_cp2.2)) 1982 991 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1982_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1982_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1982_fin) true) L1982_seg1) L1982_seg2) (by decide) rfl L1982_fin ptTest_fst
noncomputable def H1982_cp1 : Nat × Nat := t7val% (fastRun pH1982 1 1143 (init pH1982) (init pH1982))
theorem H1982_seg1 : segOK pH1982 1 1143 (init pH1982) (init pH1982) H1982_cp1.1 H1982_cp1.2 = true := by
  decide +kernel
noncomputable def H1982_cp2 : Nat × Nat := t7val% (fastRun pH1982 1 1617 (init pH1982) (init pH1982))
theorem H1982_seg2 : segOK pH1982 1144 474 H1982_cp1.1 H1982_cp1.2 H1982_cp2.1 H1982_cp2.2 = true := by
  decide +kernel
theorem H1982_fin : (prmOK pH1982 1982 && ptTest pH1982 (runFrom pH1982 (fmask pH1982) (cmask pH1982) (hmask pH1982) 1618 364 (true, H1982_cp2.1, H1982_cp2.2)) 1982 991 true) = true := by
  decide +kernel
theorem H1982_ok : RunOK pH1982 1982 (runFrom pH1982 (fmask pH1982) (cmask pH1982) (hmask pH1982) 1618 364 (true, H1982_cp2.1, H1982_cp2.2)) ∧ ptTest pH1982 (runFrom pH1982 (fmask pH1982) (cmask pH1982) (hmask pH1982) 1618 364 (true, H1982_cp2.1, H1982_cp2.2)) 1982 991 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1982_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1982_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1982_fin) true) H1982_seg1) H1982_seg2) (by decide) rfl H1982_fin ptTest_fst
noncomputable def I1982_cp1 : Nat × Nat := t7val% (fastRun pI1982 1 1143 (init pI1982) (init pI1982))
theorem I1982_seg1 : segOK pI1982 1 1143 (init pI1982) (init pI1982) I1982_cp1.1 I1982_cp1.2 = true := by
  decide +kernel
noncomputable def I1982_cp2 : Nat × Nat := t7val% (fastRun pI1982 1 1617 (init pI1982) (init pI1982))
theorem I1982_seg2 : segOK pI1982 1144 474 I1982_cp1.1 I1982_cp1.2 I1982_cp2.1 I1982_cp2.2 = true := by
  decide +kernel
theorem I1982_fin : (prmOK pI1982 1982 && intTest pI1982 (runFrom pI1982 (fmask pI1982) (cmask pI1982) (hmask pI1982) 1618 364 (true, I1982_cp2.1, I1982_cp2.2)) 1982 22 true) = true := by
  decide +kernel
theorem I1982_ok : RunOK pI1982 1982 (runFrom pI1982 (fmask pI1982) (cmask pI1982) (hmask pI1982) 1618 364 (true, I1982_cp2.1, I1982_cp2.2)) ∧ intTest pI1982 (runFrom pI1982 (fmask pI1982) (cmask pI1982) (hmask pI1982) 1618 364 (true, I1982_cp2.1, I1982_cp2.2)) 1982 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1982_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1982_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1982_fin) true) I1982_seg1) I1982_seg2) (by decide) rfl I1982_fin intTest_fst
theorem link1982 : linkOK pL1982 pH1982 pI1982 = true := by decide +kernel
theorem cvx1982 : ConvexBetweenHumps 1982 :=
  cvx_of L1982_ok H1982_ok I1982_ok link1982 (by decide)
theorem cenlink1982 : cenLinkOK pI1982 1982 = true := by decide +kernel
theorem cen1982 : CenterUniqueMin 1982 ∧ DipHyp 1982 ∧ OnePointHyps 1982 :=
  cen_of L1982_ok H1982_ok I1982_ok link1982 cenlink1982

/-! ### `N = 1983` -/

def pL1983 : Prm := ⟨81, 38, 40, 1985, 11, 18446744073709551616, 99025107762055947, 99025107762055947⟩
def pH1983 : Prm := ⟨81, 38, 40, 1985, 11, 18446744073709551616, 99026207273683723, 99026207273683723⟩
def pI1983 : Prm := ⟨68, 34, 31, 1985, 11, 18446744073709551616, 99025107762055947, 99026207273683723⟩
noncomputable def L1983_cp1 : Nat × Nat := t7val% (fastRun pL1983 1 1144 (init pL1983) (init pL1983))
theorem L1983_seg1 : segOK pL1983 1 1144 (init pL1983) (init pL1983) L1983_cp1.1 L1983_cp1.2 = true := by
  decide +kernel
noncomputable def L1983_cp2 : Nat × Nat := t7val% (fastRun pL1983 1 1618 (init pL1983) (init pL1983))
theorem L1983_seg2 : segOK pL1983 1145 474 L1983_cp1.1 L1983_cp1.2 L1983_cp2.1 L1983_cp2.2 = true := by
  decide +kernel
theorem L1983_fin : (prmOK pL1983 1983 && ptTest pL1983 (runFrom pL1983 (fmask pL1983) (cmask pL1983) (hmask pL1983) 1619 364 (true, L1983_cp2.1, L1983_cp2.2)) 1983 992 false) = true := by
  decide +kernel
theorem L1983_ok : RunOK pL1983 1983 (runFrom pL1983 (fmask pL1983) (cmask pL1983) (hmask pL1983) 1619 364 (true, L1983_cp2.1, L1983_cp2.2)) ∧ ptTest pL1983 (runFrom pL1983 (fmask pL1983) (cmask pL1983) (hmask pL1983) 1619 364 (true, L1983_cp2.1, L1983_cp2.2)) 1983 992 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1983_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1983_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1983_fin) true) L1983_seg1) L1983_seg2) (by decide) rfl L1983_fin ptTest_fst
noncomputable def H1983_cp1 : Nat × Nat := t7val% (fastRun pH1983 1 1144 (init pH1983) (init pH1983))
theorem H1983_seg1 : segOK pH1983 1 1144 (init pH1983) (init pH1983) H1983_cp1.1 H1983_cp1.2 = true := by
  decide +kernel
noncomputable def H1983_cp2 : Nat × Nat := t7val% (fastRun pH1983 1 1618 (init pH1983) (init pH1983))
theorem H1983_seg2 : segOK pH1983 1145 474 H1983_cp1.1 H1983_cp1.2 H1983_cp2.1 H1983_cp2.2 = true := by
  decide +kernel
theorem H1983_fin : (prmOK pH1983 1983 && ptTest pH1983 (runFrom pH1983 (fmask pH1983) (cmask pH1983) (hmask pH1983) 1619 364 (true, H1983_cp2.1, H1983_cp2.2)) 1983 992 true) = true := by
  decide +kernel
theorem H1983_ok : RunOK pH1983 1983 (runFrom pH1983 (fmask pH1983) (cmask pH1983) (hmask pH1983) 1619 364 (true, H1983_cp2.1, H1983_cp2.2)) ∧ ptTest pH1983 (runFrom pH1983 (fmask pH1983) (cmask pH1983) (hmask pH1983) 1619 364 (true, H1983_cp2.1, H1983_cp2.2)) 1983 992 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1983_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1983_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1983_fin) true) H1983_seg1) H1983_seg2) (by decide) rfl H1983_fin ptTest_fst
noncomputable def I1983_cp1 : Nat × Nat := t7val% (fastRun pI1983 1 1144 (init pI1983) (init pI1983))
theorem I1983_seg1 : segOK pI1983 1 1144 (init pI1983) (init pI1983) I1983_cp1.1 I1983_cp1.2 = true := by
  decide +kernel
noncomputable def I1983_cp2 : Nat × Nat := t7val% (fastRun pI1983 1 1618 (init pI1983) (init pI1983))
theorem I1983_seg2 : segOK pI1983 1145 474 I1983_cp1.1 I1983_cp1.2 I1983_cp2.1 I1983_cp2.2 = true := by
  decide +kernel
theorem I1983_fin : (prmOK pI1983 1983 && intTest pI1983 (runFrom pI1983 (fmask pI1983) (cmask pI1983) (hmask pI1983) 1619 364 (true, I1983_cp2.1, I1983_cp2.2)) 1983 22 false) = true := by
  decide +kernel
theorem I1983_ok : RunOK pI1983 1983 (runFrom pI1983 (fmask pI1983) (cmask pI1983) (hmask pI1983) 1619 364 (true, I1983_cp2.1, I1983_cp2.2)) ∧ intTest pI1983 (runFrom pI1983 (fmask pI1983) (cmask pI1983) (hmask pI1983) 1619 364 (true, I1983_cp2.1, I1983_cp2.2)) 1983 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1983_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1983_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1983_fin) true) I1983_seg1) I1983_seg2) (by decide) rfl I1983_fin intTest_fst
theorem link1983 : linkOK pL1983 pH1983 pI1983 = true := by decide +kernel
theorem cvx1983 : ConvexBetweenHumps 1983 :=
  cvx_of L1983_ok H1983_ok I1983_ok link1983 (by decide)

/-! ### `N = 1984` -/

def pL1984 : Prm := ⟨81, 38, 40, 1986, 11, 18446744073709551616, 98984038106773924, 98984038106773924⟩
def pH1984 : Prm := ⟨81, 38, 40, 1986, 11, 18446744073709551616, 98985137618401700, 98985137618401700⟩
def pI1984 : Prm := ⟨68, 34, 31, 1986, 11, 18446744073709551616, 98984038106773924, 98985137618401700⟩
noncomputable def L1984_cp1 : Nat × Nat := t7val% (fastRun pL1984 1 1144 (init pL1984) (init pL1984))
theorem L1984_seg1 : segOK pL1984 1 1144 (init pL1984) (init pL1984) L1984_cp1.1 L1984_cp1.2 = true := by
  decide +kernel
noncomputable def L1984_cp2 : Nat × Nat := t7val% (fastRun pL1984 1 1619 (init pL1984) (init pL1984))
theorem L1984_seg2 : segOK pL1984 1145 475 L1984_cp1.1 L1984_cp1.2 L1984_cp2.1 L1984_cp2.2 = true := by
  decide +kernel
theorem L1984_fin : (prmOK pL1984 1984 && ptTest pL1984 (runFrom pL1984 (fmask pL1984) (cmask pL1984) (hmask pL1984) 1620 364 (true, L1984_cp2.1, L1984_cp2.2)) 1984 992 false) = true := by
  decide +kernel
theorem L1984_ok : RunOK pL1984 1984 (runFrom pL1984 (fmask pL1984) (cmask pL1984) (hmask pL1984) 1620 364 (true, L1984_cp2.1, L1984_cp2.2)) ∧ ptTest pL1984 (runFrom pL1984 (fmask pL1984) (cmask pL1984) (hmask pL1984) 1620 364 (true, L1984_cp2.1, L1984_cp2.2)) 1984 992 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1984_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1984_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1984_fin) true) L1984_seg1) L1984_seg2) (by decide) rfl L1984_fin ptTest_fst
noncomputable def H1984_cp1 : Nat × Nat := t7val% (fastRun pH1984 1 1144 (init pH1984) (init pH1984))
theorem H1984_seg1 : segOK pH1984 1 1144 (init pH1984) (init pH1984) H1984_cp1.1 H1984_cp1.2 = true := by
  decide +kernel
noncomputable def H1984_cp2 : Nat × Nat := t7val% (fastRun pH1984 1 1619 (init pH1984) (init pH1984))
theorem H1984_seg2 : segOK pH1984 1145 475 H1984_cp1.1 H1984_cp1.2 H1984_cp2.1 H1984_cp2.2 = true := by
  decide +kernel
theorem H1984_fin : (prmOK pH1984 1984 && ptTest pH1984 (runFrom pH1984 (fmask pH1984) (cmask pH1984) (hmask pH1984) 1620 364 (true, H1984_cp2.1, H1984_cp2.2)) 1984 992 true) = true := by
  decide +kernel
theorem H1984_ok : RunOK pH1984 1984 (runFrom pH1984 (fmask pH1984) (cmask pH1984) (hmask pH1984) 1620 364 (true, H1984_cp2.1, H1984_cp2.2)) ∧ ptTest pH1984 (runFrom pH1984 (fmask pH1984) (cmask pH1984) (hmask pH1984) 1620 364 (true, H1984_cp2.1, H1984_cp2.2)) 1984 992 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1984_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1984_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1984_fin) true) H1984_seg1) H1984_seg2) (by decide) rfl H1984_fin ptTest_fst
noncomputable def I1984_cp1 : Nat × Nat := t7val% (fastRun pI1984 1 1144 (init pI1984) (init pI1984))
theorem I1984_seg1 : segOK pI1984 1 1144 (init pI1984) (init pI1984) I1984_cp1.1 I1984_cp1.2 = true := by
  decide +kernel
noncomputable def I1984_cp2 : Nat × Nat := t7val% (fastRun pI1984 1 1619 (init pI1984) (init pI1984))
theorem I1984_seg2 : segOK pI1984 1145 475 I1984_cp1.1 I1984_cp1.2 I1984_cp2.1 I1984_cp2.2 = true := by
  decide +kernel
theorem I1984_fin : (prmOK pI1984 1984 && intTest pI1984 (runFrom pI1984 (fmask pI1984) (cmask pI1984) (hmask pI1984) 1620 364 (true, I1984_cp2.1, I1984_cp2.2)) 1984 22 true) = true := by
  decide +kernel
theorem I1984_ok : RunOK pI1984 1984 (runFrom pI1984 (fmask pI1984) (cmask pI1984) (hmask pI1984) 1620 364 (true, I1984_cp2.1, I1984_cp2.2)) ∧ intTest pI1984 (runFrom pI1984 (fmask pI1984) (cmask pI1984) (hmask pI1984) 1620 364 (true, I1984_cp2.1, I1984_cp2.2)) 1984 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1984_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1984_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1984_fin) true) I1984_seg1) I1984_seg2) (by decide) rfl I1984_fin intTest_fst
theorem link1984 : linkOK pL1984 pH1984 pI1984 = true := by decide +kernel
theorem cvx1984 : ConvexBetweenHumps 1984 :=
  cvx_of L1984_ok H1984_ok I1984_ok link1984 (by decide)
theorem cenlink1984 : cenLinkOK pI1984 1984 = true := by decide +kernel
theorem cen1984 : CenterUniqueMin 1984 ∧ DipHyp 1984 ∧ OnePointHyps 1984 :=
  cen_of L1984_ok H1984_ok I1984_ok link1984 cenlink1984

/-! ### `N = 1985` -/

def pL1985 : Prm := ⟨81, 38, 40, 1987, 11, 18446744073709551616, 98942991073306008, 98942991073306008⟩
def pH1985 : Prm := ⟨81, 38, 40, 1987, 11, 18446744073709551616, 98944090584933784, 98944090584933784⟩
def pI1985 : Prm := ⟨68, 34, 31, 1987, 11, 18446744073709551616, 98942991073306008, 98944090584933784⟩
noncomputable def L1985_cp1 : Nat × Nat := t7val% (fastRun pL1985 1 1145 (init pL1985) (init pL1985))
theorem L1985_seg1 : segOK pL1985 1 1145 (init pL1985) (init pL1985) L1985_cp1.1 L1985_cp1.2 = true := by
  decide +kernel
noncomputable def L1985_cp2 : Nat × Nat := t7val% (fastRun pL1985 1 1620 (init pL1985) (init pL1985))
theorem L1985_seg2 : segOK pL1985 1146 475 L1985_cp1.1 L1985_cp1.2 L1985_cp2.1 L1985_cp2.2 = true := by
  decide +kernel
theorem L1985_fin : (prmOK pL1985 1985 && ptTest pL1985 (runFrom pL1985 (fmask pL1985) (cmask pL1985) (hmask pL1985) 1621 364 (true, L1985_cp2.1, L1985_cp2.2)) 1985 993 false) = true := by
  decide +kernel
theorem L1985_ok : RunOK pL1985 1985 (runFrom pL1985 (fmask pL1985) (cmask pL1985) (hmask pL1985) 1621 364 (true, L1985_cp2.1, L1985_cp2.2)) ∧ ptTest pL1985 (runFrom pL1985 (fmask pL1985) (cmask pL1985) (hmask pL1985) 1621 364 (true, L1985_cp2.1, L1985_cp2.2)) 1985 993 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1985_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1985_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1985_fin) true) L1985_seg1) L1985_seg2) (by decide) rfl L1985_fin ptTest_fst
noncomputable def H1985_cp1 : Nat × Nat := t7val% (fastRun pH1985 1 1145 (init pH1985) (init pH1985))
theorem H1985_seg1 : segOK pH1985 1 1145 (init pH1985) (init pH1985) H1985_cp1.1 H1985_cp1.2 = true := by
  decide +kernel
noncomputable def H1985_cp2 : Nat × Nat := t7val% (fastRun pH1985 1 1620 (init pH1985) (init pH1985))
theorem H1985_seg2 : segOK pH1985 1146 475 H1985_cp1.1 H1985_cp1.2 H1985_cp2.1 H1985_cp2.2 = true := by
  decide +kernel
theorem H1985_fin : (prmOK pH1985 1985 && ptTest pH1985 (runFrom pH1985 (fmask pH1985) (cmask pH1985) (hmask pH1985) 1621 364 (true, H1985_cp2.1, H1985_cp2.2)) 1985 993 true) = true := by
  decide +kernel
theorem H1985_ok : RunOK pH1985 1985 (runFrom pH1985 (fmask pH1985) (cmask pH1985) (hmask pH1985) 1621 364 (true, H1985_cp2.1, H1985_cp2.2)) ∧ ptTest pH1985 (runFrom pH1985 (fmask pH1985) (cmask pH1985) (hmask pH1985) 1621 364 (true, H1985_cp2.1, H1985_cp2.2)) 1985 993 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1985_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1985_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1985_fin) true) H1985_seg1) H1985_seg2) (by decide) rfl H1985_fin ptTest_fst
noncomputable def I1985_cp1 : Nat × Nat := t7val% (fastRun pI1985 1 1145 (init pI1985) (init pI1985))
theorem I1985_seg1 : segOK pI1985 1 1145 (init pI1985) (init pI1985) I1985_cp1.1 I1985_cp1.2 = true := by
  decide +kernel
noncomputable def I1985_cp2 : Nat × Nat := t7val% (fastRun pI1985 1 1620 (init pI1985) (init pI1985))
theorem I1985_seg2 : segOK pI1985 1146 475 I1985_cp1.1 I1985_cp1.2 I1985_cp2.1 I1985_cp2.2 = true := by
  decide +kernel
theorem I1985_fin : (prmOK pI1985 1985 && intTest pI1985 (runFrom pI1985 (fmask pI1985) (cmask pI1985) (hmask pI1985) 1621 364 (true, I1985_cp2.1, I1985_cp2.2)) 1985 22 false) = true := by
  decide +kernel
theorem I1985_ok : RunOK pI1985 1985 (runFrom pI1985 (fmask pI1985) (cmask pI1985) (hmask pI1985) 1621 364 (true, I1985_cp2.1, I1985_cp2.2)) ∧ intTest pI1985 (runFrom pI1985 (fmask pI1985) (cmask pI1985) (hmask pI1985) 1621 364 (true, I1985_cp2.1, I1985_cp2.2)) 1985 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1985_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1985_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1985_fin) true) I1985_seg1) I1985_seg2) (by decide) rfl I1985_fin intTest_fst
theorem link1985 : linkOK pL1985 pH1985 pI1985 = true := by decide +kernel
theorem cvx1985 : ConvexBetweenHumps 1985 :=
  cvx_of L1985_ok H1985_ok I1985_ok link1985 (by decide)

/-! ### `N = 1986` -/

def pL1986 : Prm := ⟨81, 38, 40, 1988, 11, 18446744073709551616, 98901995207379910, 98901995207379910⟩
def pH1986 : Prm := ⟨81, 38, 40, 1988, 11, 18446744073709551616, 98903094719007686, 98903094719007686⟩
def pI1986 : Prm := ⟨68, 34, 31, 1988, 11, 18446744073709551616, 98901995207379910, 98903094719007686⟩
noncomputable def L1986_cp1 : Nat × Nat := t7val% (fastRun pL1986 1 1146 (init pL1986) (init pL1986))
theorem L1986_seg1 : segOK pL1986 1 1146 (init pL1986) (init pL1986) L1986_cp1.1 L1986_cp1.2 = true := by
  decide +kernel
noncomputable def L1986_cp2 : Nat × Nat := t7val% (fastRun pL1986 1 1621 (init pL1986) (init pL1986))
theorem L1986_seg2 : segOK pL1986 1147 475 L1986_cp1.1 L1986_cp1.2 L1986_cp2.1 L1986_cp2.2 = true := by
  decide +kernel
theorem L1986_fin : (prmOK pL1986 1986 && ptTest pL1986 (runFrom pL1986 (fmask pL1986) (cmask pL1986) (hmask pL1986) 1622 364 (true, L1986_cp2.1, L1986_cp2.2)) 1986 993 false) = true := by
  decide +kernel
theorem L1986_ok : RunOK pL1986 1986 (runFrom pL1986 (fmask pL1986) (cmask pL1986) (hmask pL1986) 1622 364 (true, L1986_cp2.1, L1986_cp2.2)) ∧ ptTest pL1986 (runFrom pL1986 (fmask pL1986) (cmask pL1986) (hmask pL1986) 1622 364 (true, L1986_cp2.1, L1986_cp2.2)) 1986 993 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1986_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1986_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1986_fin) true) L1986_seg1) L1986_seg2) (by decide) rfl L1986_fin ptTest_fst
noncomputable def H1986_cp1 : Nat × Nat := t7val% (fastRun pH1986 1 1146 (init pH1986) (init pH1986))
theorem H1986_seg1 : segOK pH1986 1 1146 (init pH1986) (init pH1986) H1986_cp1.1 H1986_cp1.2 = true := by
  decide +kernel
noncomputable def H1986_cp2 : Nat × Nat := t7val% (fastRun pH1986 1 1621 (init pH1986) (init pH1986))
theorem H1986_seg2 : segOK pH1986 1147 475 H1986_cp1.1 H1986_cp1.2 H1986_cp2.1 H1986_cp2.2 = true := by
  decide +kernel
theorem H1986_fin : (prmOK pH1986 1986 && ptTest pH1986 (runFrom pH1986 (fmask pH1986) (cmask pH1986) (hmask pH1986) 1622 364 (true, H1986_cp2.1, H1986_cp2.2)) 1986 993 true) = true := by
  decide +kernel
theorem H1986_ok : RunOK pH1986 1986 (runFrom pH1986 (fmask pH1986) (cmask pH1986) (hmask pH1986) 1622 364 (true, H1986_cp2.1, H1986_cp2.2)) ∧ ptTest pH1986 (runFrom pH1986 (fmask pH1986) (cmask pH1986) (hmask pH1986) 1622 364 (true, H1986_cp2.1, H1986_cp2.2)) 1986 993 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1986_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1986_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1986_fin) true) H1986_seg1) H1986_seg2) (by decide) rfl H1986_fin ptTest_fst
noncomputable def I1986_cp1 : Nat × Nat := t7val% (fastRun pI1986 1 1146 (init pI1986) (init pI1986))
theorem I1986_seg1 : segOK pI1986 1 1146 (init pI1986) (init pI1986) I1986_cp1.1 I1986_cp1.2 = true := by
  decide +kernel
noncomputable def I1986_cp2 : Nat × Nat := t7val% (fastRun pI1986 1 1621 (init pI1986) (init pI1986))
theorem I1986_seg2 : segOK pI1986 1147 475 I1986_cp1.1 I1986_cp1.2 I1986_cp2.1 I1986_cp2.2 = true := by
  decide +kernel
theorem I1986_fin : (prmOK pI1986 1986 && intTest pI1986 (runFrom pI1986 (fmask pI1986) (cmask pI1986) (hmask pI1986) 1622 364 (true, I1986_cp2.1, I1986_cp2.2)) 1986 22 true) = true := by
  decide +kernel
theorem I1986_ok : RunOK pI1986 1986 (runFrom pI1986 (fmask pI1986) (cmask pI1986) (hmask pI1986) 1622 364 (true, I1986_cp2.1, I1986_cp2.2)) ∧ intTest pI1986 (runFrom pI1986 (fmask pI1986) (cmask pI1986) (hmask pI1986) 1622 364 (true, I1986_cp2.1, I1986_cp2.2)) 1986 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1986_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1986_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1986_fin) true) I1986_seg1) I1986_seg2) (by decide) rfl I1986_fin intTest_fst
theorem link1986 : linkOK pL1986 pH1986 pI1986 = true := by decide +kernel
theorem cvx1986 : ConvexBetweenHumps 1986 :=
  cvx_of L1986_ok H1986_ok I1986_ok link1986 (by decide)
theorem cenlink1986 : cenLinkOK pI1986 1986 = true := by decide +kernel
theorem cen1986 : CenterUniqueMin 1986 ∧ DipHyp 1986 ∧ OnePointHyps 1986 :=
  cen_of L1986_ok H1986_ok I1986_ok link1986 cenlink1986

/-! ### `N = 1987` -/

def pL1987 : Prm := ⟨81, 38, 40, 1989, 11, 18446744073709551616, 98861021904588825, 98861021904588825⟩
def pH1987 : Prm := ⟨81, 38, 40, 1989, 11, 18446744073709551616, 98862121416216601, 98862121416216601⟩
def pI1987 : Prm := ⟨68, 34, 31, 1989, 11, 18446744073709551616, 98861021904588825, 98862121416216601⟩
noncomputable def L1987_cp1 : Nat × Nat := t7val% (fastRun pL1987 1 1146 (init pL1987) (init pL1987))
theorem L1987_seg1 : segOK pL1987 1 1146 (init pL1987) (init pL1987) L1987_cp1.1 L1987_cp1.2 = true := by
  decide +kernel
noncomputable def L1987_cp2 : Nat × Nat := t7val% (fastRun pL1987 1 1621 (init pL1987) (init pL1987))
theorem L1987_seg2 : segOK pL1987 1147 475 L1987_cp1.1 L1987_cp1.2 L1987_cp2.1 L1987_cp2.2 = true := by
  decide +kernel
theorem L1987_fin : (prmOK pL1987 1987 && ptTest pL1987 (runFrom pL1987 (fmask pL1987) (cmask pL1987) (hmask pL1987) 1622 365 (true, L1987_cp2.1, L1987_cp2.2)) 1987 994 false) = true := by
  decide +kernel
theorem L1987_ok : RunOK pL1987 1987 (runFrom pL1987 (fmask pL1987) (cmask pL1987) (hmask pL1987) 1622 365 (true, L1987_cp2.1, L1987_cp2.2)) ∧ ptTest pL1987 (runFrom pL1987 (fmask pL1987) (cmask pL1987) (hmask pL1987) 1622 365 (true, L1987_cp2.1, L1987_cp2.2)) 1987 994 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1987_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1987_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1987_fin) true) L1987_seg1) L1987_seg2) (by decide) rfl L1987_fin ptTest_fst
noncomputable def H1987_cp1 : Nat × Nat := t7val% (fastRun pH1987 1 1146 (init pH1987) (init pH1987))
theorem H1987_seg1 : segOK pH1987 1 1146 (init pH1987) (init pH1987) H1987_cp1.1 H1987_cp1.2 = true := by
  decide +kernel
noncomputable def H1987_cp2 : Nat × Nat := t7val% (fastRun pH1987 1 1621 (init pH1987) (init pH1987))
theorem H1987_seg2 : segOK pH1987 1147 475 H1987_cp1.1 H1987_cp1.2 H1987_cp2.1 H1987_cp2.2 = true := by
  decide +kernel
theorem H1987_fin : (prmOK pH1987 1987 && ptTest pH1987 (runFrom pH1987 (fmask pH1987) (cmask pH1987) (hmask pH1987) 1622 365 (true, H1987_cp2.1, H1987_cp2.2)) 1987 994 true) = true := by
  decide +kernel
theorem H1987_ok : RunOK pH1987 1987 (runFrom pH1987 (fmask pH1987) (cmask pH1987) (hmask pH1987) 1622 365 (true, H1987_cp2.1, H1987_cp2.2)) ∧ ptTest pH1987 (runFrom pH1987 (fmask pH1987) (cmask pH1987) (hmask pH1987) 1622 365 (true, H1987_cp2.1, H1987_cp2.2)) 1987 994 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1987_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1987_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1987_fin) true) H1987_seg1) H1987_seg2) (by decide) rfl H1987_fin ptTest_fst
noncomputable def I1987_cp1 : Nat × Nat := t7val% (fastRun pI1987 1 1146 (init pI1987) (init pI1987))
theorem I1987_seg1 : segOK pI1987 1 1146 (init pI1987) (init pI1987) I1987_cp1.1 I1987_cp1.2 = true := by
  decide +kernel
noncomputable def I1987_cp2 : Nat × Nat := t7val% (fastRun pI1987 1 1621 (init pI1987) (init pI1987))
theorem I1987_seg2 : segOK pI1987 1147 475 I1987_cp1.1 I1987_cp1.2 I1987_cp2.1 I1987_cp2.2 = true := by
  decide +kernel
theorem I1987_fin : (prmOK pI1987 1987 && intTest pI1987 (runFrom pI1987 (fmask pI1987) (cmask pI1987) (hmask pI1987) 1622 365 (true, I1987_cp2.1, I1987_cp2.2)) 1987 22 false) = true := by
  decide +kernel
theorem I1987_ok : RunOK pI1987 1987 (runFrom pI1987 (fmask pI1987) (cmask pI1987) (hmask pI1987) 1622 365 (true, I1987_cp2.1, I1987_cp2.2)) ∧ intTest pI1987 (runFrom pI1987 (fmask pI1987) (cmask pI1987) (hmask pI1987) 1622 365 (true, I1987_cp2.1, I1987_cp2.2)) 1987 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1987_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1987_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1987_fin) true) I1987_seg1) I1987_seg2) (by decide) rfl I1987_fin intTest_fst
theorem link1987 : linkOK pL1987 pH1987 pI1987 = true := by decide +kernel
theorem cvx1987 : ConvexBetweenHumps 1987 :=
  cvx_of L1987_ok H1987_ok I1987_ok link1987 (by decide)

/-! ### `N = 1988` -/

def pL1988 : Prm := ⟨81, 38, 40, 1990, 11, 18446744073709551616, 98820099623315133, 98820099623315133⟩
def pH1988 : Prm := ⟨81, 38, 40, 1990, 11, 18446744073709551616, 98821199134942909, 98821199134942909⟩
def pI1988 : Prm := ⟨68, 34, 31, 1990, 11, 18446744073709551616, 98820099623315133, 98821199134942909⟩
noncomputable def L1988_cp1 : Nat × Nat := t7val% (fastRun pL1988 1 1147 (init pL1988) (init pL1988))
theorem L1988_seg1 : segOK pL1988 1 1147 (init pL1988) (init pL1988) L1988_cp1.1 L1988_cp1.2 = true := by
  decide +kernel
noncomputable def L1988_cp2 : Nat × Nat := t7val% (fastRun pL1988 1 1622 (init pL1988) (init pL1988))
theorem L1988_seg2 : segOK pL1988 1148 475 L1988_cp1.1 L1988_cp1.2 L1988_cp2.1 L1988_cp2.2 = true := by
  decide +kernel
theorem L1988_fin : (prmOK pL1988 1988 && ptTest pL1988 (runFrom pL1988 (fmask pL1988) (cmask pL1988) (hmask pL1988) 1623 365 (true, L1988_cp2.1, L1988_cp2.2)) 1988 994 false) = true := by
  decide +kernel
theorem L1988_ok : RunOK pL1988 1988 (runFrom pL1988 (fmask pL1988) (cmask pL1988) (hmask pL1988) 1623 365 (true, L1988_cp2.1, L1988_cp2.2)) ∧ ptTest pL1988 (runFrom pL1988 (fmask pL1988) (cmask pL1988) (hmask pL1988) 1623 365 (true, L1988_cp2.1, L1988_cp2.2)) 1988 994 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1988_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1988_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1988_fin) true) L1988_seg1) L1988_seg2) (by decide) rfl L1988_fin ptTest_fst
noncomputable def H1988_cp1 : Nat × Nat := t7val% (fastRun pH1988 1 1147 (init pH1988) (init pH1988))
theorem H1988_seg1 : segOK pH1988 1 1147 (init pH1988) (init pH1988) H1988_cp1.1 H1988_cp1.2 = true := by
  decide +kernel
noncomputable def H1988_cp2 : Nat × Nat := t7val% (fastRun pH1988 1 1622 (init pH1988) (init pH1988))
theorem H1988_seg2 : segOK pH1988 1148 475 H1988_cp1.1 H1988_cp1.2 H1988_cp2.1 H1988_cp2.2 = true := by
  decide +kernel
theorem H1988_fin : (prmOK pH1988 1988 && ptTest pH1988 (runFrom pH1988 (fmask pH1988) (cmask pH1988) (hmask pH1988) 1623 365 (true, H1988_cp2.1, H1988_cp2.2)) 1988 994 true) = true := by
  decide +kernel
theorem H1988_ok : RunOK pH1988 1988 (runFrom pH1988 (fmask pH1988) (cmask pH1988) (hmask pH1988) 1623 365 (true, H1988_cp2.1, H1988_cp2.2)) ∧ ptTest pH1988 (runFrom pH1988 (fmask pH1988) (cmask pH1988) (hmask pH1988) 1623 365 (true, H1988_cp2.1, H1988_cp2.2)) 1988 994 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1988_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1988_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1988_fin) true) H1988_seg1) H1988_seg2) (by decide) rfl H1988_fin ptTest_fst
noncomputable def I1988_cp1 : Nat × Nat := t7val% (fastRun pI1988 1 1147 (init pI1988) (init pI1988))
theorem I1988_seg1 : segOK pI1988 1 1147 (init pI1988) (init pI1988) I1988_cp1.1 I1988_cp1.2 = true := by
  decide +kernel
noncomputable def I1988_cp2 : Nat × Nat := t7val% (fastRun pI1988 1 1622 (init pI1988) (init pI1988))
theorem I1988_seg2 : segOK pI1988 1148 475 I1988_cp1.1 I1988_cp1.2 I1988_cp2.1 I1988_cp2.2 = true := by
  decide +kernel
theorem I1988_fin : (prmOK pI1988 1988 && intTest pI1988 (runFrom pI1988 (fmask pI1988) (cmask pI1988) (hmask pI1988) 1623 365 (true, I1988_cp2.1, I1988_cp2.2)) 1988 22 true) = true := by
  decide +kernel
theorem I1988_ok : RunOK pI1988 1988 (runFrom pI1988 (fmask pI1988) (cmask pI1988) (hmask pI1988) 1623 365 (true, I1988_cp2.1, I1988_cp2.2)) ∧ intTest pI1988 (runFrom pI1988 (fmask pI1988) (cmask pI1988) (hmask pI1988) 1623 365 (true, I1988_cp2.1, I1988_cp2.2)) 1988 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1988_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1988_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1988_fin) true) I1988_seg1) I1988_seg2) (by decide) rfl I1988_fin intTest_fst
theorem link1988 : linkOK pL1988 pH1988 pI1988 = true := by decide +kernel
theorem cvx1988 : ConvexBetweenHumps 1988 :=
  cvx_of L1988_ok H1988_ok I1988_ok link1988 (by decide)
theorem cenlink1988 : cenLinkOK pI1988 1988 = true := by decide +kernel
theorem cen1988 : CenterUniqueMin 1988 ∧ DipHyp 1988 ∧ OnePointHyps 1988 :=
  cen_of L1988_ok H1988_ok I1988_ok link1988 cenlink1988

/-! ### `N = 1989` -/

def pL1989 : Prm := ⟨81, 38, 40, 1991, 11, 18446744073709551616, 98779199846681830, 98779199846681830⟩
def pH1989 : Prm := ⟨81, 38, 40, 1991, 11, 18446744073709551616, 98780299358309606, 98780299358309606⟩
def pI1989 : Prm := ⟨68, 34, 31, 1991, 11, 18446744073709551616, 98779199846681830, 98780299358309606⟩
noncomputable def L1989_cp1 : Nat × Nat := t7val% (fastRun pL1989 1 1147 (init pL1989) (init pL1989))
theorem L1989_seg1 : segOK pL1989 1 1147 (init pL1989) (init pL1989) L1989_cp1.1 L1989_cp1.2 = true := by
  decide +kernel
noncomputable def L1989_cp2 : Nat × Nat := t7val% (fastRun pL1989 1 1623 (init pL1989) (init pL1989))
theorem L1989_seg2 : segOK pL1989 1148 476 L1989_cp1.1 L1989_cp1.2 L1989_cp2.1 L1989_cp2.2 = true := by
  decide +kernel
theorem L1989_fin : (prmOK pL1989 1989 && ptTest pL1989 (runFrom pL1989 (fmask pL1989) (cmask pL1989) (hmask pL1989) 1624 365 (true, L1989_cp2.1, L1989_cp2.2)) 1989 995 false) = true := by
  decide +kernel
theorem L1989_ok : RunOK pL1989 1989 (runFrom pL1989 (fmask pL1989) (cmask pL1989) (hmask pL1989) 1624 365 (true, L1989_cp2.1, L1989_cp2.2)) ∧ ptTest pL1989 (runFrom pL1989 (fmask pL1989) (cmask pL1989) (hmask pL1989) 1624 365 (true, L1989_cp2.1, L1989_cp2.2)) 1989 995 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1989_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1989_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1989_fin) true) L1989_seg1) L1989_seg2) (by decide) rfl L1989_fin ptTest_fst
noncomputable def H1989_cp1 : Nat × Nat := t7val% (fastRun pH1989 1 1147 (init pH1989) (init pH1989))
theorem H1989_seg1 : segOK pH1989 1 1147 (init pH1989) (init pH1989) H1989_cp1.1 H1989_cp1.2 = true := by
  decide +kernel
noncomputable def H1989_cp2 : Nat × Nat := t7val% (fastRun pH1989 1 1623 (init pH1989) (init pH1989))
theorem H1989_seg2 : segOK pH1989 1148 476 H1989_cp1.1 H1989_cp1.2 H1989_cp2.1 H1989_cp2.2 = true := by
  decide +kernel
theorem H1989_fin : (prmOK pH1989 1989 && ptTest pH1989 (runFrom pH1989 (fmask pH1989) (cmask pH1989) (hmask pH1989) 1624 365 (true, H1989_cp2.1, H1989_cp2.2)) 1989 995 true) = true := by
  decide +kernel
theorem H1989_ok : RunOK pH1989 1989 (runFrom pH1989 (fmask pH1989) (cmask pH1989) (hmask pH1989) 1624 365 (true, H1989_cp2.1, H1989_cp2.2)) ∧ ptTest pH1989 (runFrom pH1989 (fmask pH1989) (cmask pH1989) (hmask pH1989) 1624 365 (true, H1989_cp2.1, H1989_cp2.2)) 1989 995 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1989_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1989_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1989_fin) true) H1989_seg1) H1989_seg2) (by decide) rfl H1989_fin ptTest_fst
noncomputable def I1989_cp1 : Nat × Nat := t7val% (fastRun pI1989 1 1147 (init pI1989) (init pI1989))
theorem I1989_seg1 : segOK pI1989 1 1147 (init pI1989) (init pI1989) I1989_cp1.1 I1989_cp1.2 = true := by
  decide +kernel
noncomputable def I1989_cp2 : Nat × Nat := t7val% (fastRun pI1989 1 1623 (init pI1989) (init pI1989))
theorem I1989_seg2 : segOK pI1989 1148 476 I1989_cp1.1 I1989_cp1.2 I1989_cp2.1 I1989_cp2.2 = true := by
  decide +kernel
theorem I1989_fin : (prmOK pI1989 1989 && intTest pI1989 (runFrom pI1989 (fmask pI1989) (cmask pI1989) (hmask pI1989) 1624 365 (true, I1989_cp2.1, I1989_cp2.2)) 1989 22 false) = true := by
  decide +kernel
theorem I1989_ok : RunOK pI1989 1989 (runFrom pI1989 (fmask pI1989) (cmask pI1989) (hmask pI1989) 1624 365 (true, I1989_cp2.1, I1989_cp2.2)) ∧ intTest pI1989 (runFrom pI1989 (fmask pI1989) (cmask pI1989) (hmask pI1989) 1624 365 (true, I1989_cp2.1, I1989_cp2.2)) 1989 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1989_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1989_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1989_fin) true) I1989_seg1) I1989_seg2) (by decide) rfl I1989_fin intTest_fst
theorem link1989 : linkOK pL1989 pH1989 pI1989 = true := by decide +kernel
theorem cvx1989 : ConvexBetweenHumps 1989 :=
  cvx_of L1989_ok H1989_ok I1989_ok link1989 (by decide)

/-! ### The range -/

theorem cvx_1980_1989 {N : ℕ} (h1 : 1980 ≤ N) (h2 : N ≤ 1989) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1984
  · by_cases h4 : N ≤ 1981
    · by_cases h6 : N ≤ 1980
      · obtain rfl : N = 1980 := by omega
        exact cvx1980
      · obtain rfl : N = 1981 := by omega
        exact cvx1981
    · by_cases h6 : N ≤ 1982
      · obtain rfl : N = 1982 := by omega
        exact cvx1982
      · by_cases h8 : N ≤ 1983
        · obtain rfl : N = 1983 := by omega
          exact cvx1983
        · obtain rfl : N = 1984 := by omega
          exact cvx1984
  · by_cases h4 : N ≤ 1986
    · by_cases h6 : N ≤ 1985
      · obtain rfl : N = 1985 := by omega
        exact cvx1985
      · obtain rfl : N = 1986 := by omega
        exact cvx1986
    · by_cases h6 : N ≤ 1987
      · obtain rfl : N = 1987 := by omega
        exact cvx1987
      · by_cases h8 : N ≤ 1988
        · obtain rfl : N = 1988 := by omega
          exact cvx1988
        · obtain rfl : N = 1989 := by omega
          exact cvx1989

theorem cen_1980_1989 {N : ℕ} (h1 : 1980 ≤ N) (h2 : N ≤ 1989) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1982
  · by_cases h4 : N ≤ 1980
    · obtain rfl : N = 1980 := by omega
      exact cen1980
    · obtain rfl : N = 1982 := by omega
      exact cen1982
  · by_cases h4 : N ≤ 1984
    · obtain rfl : N = 1984 := by omega
      exact cen1984
    · by_cases h6 : N ≤ 1986
      · obtain rfl : N = 1986 := by omega
        exact cen1986
      · obtain rfl : N = 1988 := by omega
        exact cen1988

end Kagey131.PaperD.T7
