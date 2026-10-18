import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1667, …, 1680` (generated)

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

/-! ### `N = 1667` -/

def pL1667 : Prm := ⟨80, 37, 40, 1669, 11, 18446744073709551616, 114175654799038218, 114175654799038218⟩
def pH1667 : Prm := ⟨80, 37, 40, 1669, 11, 18446744073709551616, 114176754310665994, 114176754310665994⟩
def pI1667 : Prm := ⟨67, 33, 31, 1669, 11, 18446744073709551616, 114175654799038218, 114176754310665994⟩
noncomputable def L1667_cp1 : Nat × Nat := t7val% (fastRun pL1667 1 961 (init pL1667) (init pL1667))
theorem L1667_seg1 : segOK pL1667 1 961 (init pL1667) (init pL1667) L1667_cp1.1 L1667_cp1.2 = true := by
  decide +kernel
noncomputable def L1667_cp2 : Nat × Nat := t7val% (fastRun pL1667 1 1360 (init pL1667) (init pL1667))
theorem L1667_seg2 : segOK pL1667 962 399 L1667_cp1.1 L1667_cp1.2 L1667_cp2.1 L1667_cp2.2 = true := by
  decide +kernel
theorem L1667_fin : (prmOK pL1667 1667 && ptTest pL1667 (runFrom pL1667 (fmask pL1667) (cmask pL1667) (hmask pL1667) 1361 306 (true, L1667_cp2.1, L1667_cp2.2)) 1667 834 false) = true := by
  decide +kernel
theorem L1667_ok : RunOK pL1667 1667 (runFrom pL1667 (fmask pL1667) (cmask pL1667) (hmask pL1667) 1361 306 (true, L1667_cp2.1, L1667_cp2.2)) ∧ ptTest pL1667 (runFrom pL1667 (fmask pL1667) (cmask pL1667) (hmask pL1667) 1361 306 (true, L1667_cp2.1, L1667_cp2.2)) 1667 834 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1667_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1667_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1667_fin) true) L1667_seg1) L1667_seg2) (by decide) rfl L1667_fin ptTest_fst
noncomputable def H1667_cp1 : Nat × Nat := t7val% (fastRun pH1667 1 961 (init pH1667) (init pH1667))
theorem H1667_seg1 : segOK pH1667 1 961 (init pH1667) (init pH1667) H1667_cp1.1 H1667_cp1.2 = true := by
  decide +kernel
noncomputable def H1667_cp2 : Nat × Nat := t7val% (fastRun pH1667 1 1360 (init pH1667) (init pH1667))
theorem H1667_seg2 : segOK pH1667 962 399 H1667_cp1.1 H1667_cp1.2 H1667_cp2.1 H1667_cp2.2 = true := by
  decide +kernel
theorem H1667_fin : (prmOK pH1667 1667 && ptTest pH1667 (runFrom pH1667 (fmask pH1667) (cmask pH1667) (hmask pH1667) 1361 306 (true, H1667_cp2.1, H1667_cp2.2)) 1667 834 true) = true := by
  decide +kernel
theorem H1667_ok : RunOK pH1667 1667 (runFrom pH1667 (fmask pH1667) (cmask pH1667) (hmask pH1667) 1361 306 (true, H1667_cp2.1, H1667_cp2.2)) ∧ ptTest pH1667 (runFrom pH1667 (fmask pH1667) (cmask pH1667) (hmask pH1667) 1361 306 (true, H1667_cp2.1, H1667_cp2.2)) 1667 834 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1667_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1667_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1667_fin) true) H1667_seg1) H1667_seg2) (by decide) rfl H1667_fin ptTest_fst
noncomputable def I1667_cp1 : Nat × Nat := t7val% (fastRun pI1667 1 1178 (init pI1667) (init pI1667))
theorem I1667_seg1 : segOK pI1667 1 1178 (init pI1667) (init pI1667) I1667_cp1.1 I1667_cp1.2 = true := by
  decide +kernel
theorem I1667_fin : (prmOK pI1667 1667 && intTest pI1667 (runFrom pI1667 (fmask pI1667) (cmask pI1667) (hmask pI1667) 1179 488 (true, I1667_cp1.1, I1667_cp1.2)) 1667 21 false) = true := by
  decide +kernel
theorem I1667_ok : RunOK pI1667 1667 (runFrom pI1667 (fmask pI1667) (cmask pI1667) (hmask pI1667) 1179 488 (true, I1667_cp1.1, I1667_cp1.2)) ∧ intTest pI1667 (runFrom pI1667 (fmask pI1667) (cmask pI1667) (hmask pI1667) 1179 488 (true, I1667_cp1.1, I1667_cp1.2)) 1667 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1667_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1667_fin) true) I1667_seg1) (by decide) rfl I1667_fin intTest_fst
theorem link1667 : linkOK pL1667 pH1667 pI1667 = true := by decide +kernel
theorem cvx1667 : ConvexBetweenHumps 1667 :=
  cvx_of L1667_ok H1667_ok I1667_ok link1667 (by decide)

/-! ### `N = 1668` -/

def pL1668 : Prm := ⟨80, 37, 40, 1670, 11, 18446744073709551616, 114119719569651089, 114119719569651089⟩
def pH1668 : Prm := ⟨80, 37, 40, 1670, 11, 18446744073709551616, 114120819081278865, 114120819081278865⟩
def pI1668 : Prm := ⟨67, 33, 31, 1670, 11, 18446744073709551616, 114119719569651089, 114120819081278865⟩
noncomputable def L1668_cp1 : Nat × Nat := t7val% (fastRun pL1668 1 962 (init pL1668) (init pL1668))
theorem L1668_seg1 : segOK pL1668 1 962 (init pL1668) (init pL1668) L1668_cp1.1 L1668_cp1.2 = true := by
  decide +kernel
noncomputable def L1668_cp2 : Nat × Nat := t7val% (fastRun pL1668 1 1361 (init pL1668) (init pL1668))
theorem L1668_seg2 : segOK pL1668 963 399 L1668_cp1.1 L1668_cp1.2 L1668_cp2.1 L1668_cp2.2 = true := by
  decide +kernel
theorem L1668_fin : (prmOK pL1668 1668 && ptTest pL1668 (runFrom pL1668 (fmask pL1668) (cmask pL1668) (hmask pL1668) 1362 306 (true, L1668_cp2.1, L1668_cp2.2)) 1668 834 false) = true := by
  decide +kernel
theorem L1668_ok : RunOK pL1668 1668 (runFrom pL1668 (fmask pL1668) (cmask pL1668) (hmask pL1668) 1362 306 (true, L1668_cp2.1, L1668_cp2.2)) ∧ ptTest pL1668 (runFrom pL1668 (fmask pL1668) (cmask pL1668) (hmask pL1668) 1362 306 (true, L1668_cp2.1, L1668_cp2.2)) 1668 834 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1668_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1668_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1668_fin) true) L1668_seg1) L1668_seg2) (by decide) rfl L1668_fin ptTest_fst
noncomputable def H1668_cp1 : Nat × Nat := t7val% (fastRun pH1668 1 962 (init pH1668) (init pH1668))
theorem H1668_seg1 : segOK pH1668 1 962 (init pH1668) (init pH1668) H1668_cp1.1 H1668_cp1.2 = true := by
  decide +kernel
noncomputable def H1668_cp2 : Nat × Nat := t7val% (fastRun pH1668 1 1361 (init pH1668) (init pH1668))
theorem H1668_seg2 : segOK pH1668 963 399 H1668_cp1.1 H1668_cp1.2 H1668_cp2.1 H1668_cp2.2 = true := by
  decide +kernel
theorem H1668_fin : (prmOK pH1668 1668 && ptTest pH1668 (runFrom pH1668 (fmask pH1668) (cmask pH1668) (hmask pH1668) 1362 306 (true, H1668_cp2.1, H1668_cp2.2)) 1668 834 true) = true := by
  decide +kernel
theorem H1668_ok : RunOK pH1668 1668 (runFrom pH1668 (fmask pH1668) (cmask pH1668) (hmask pH1668) 1362 306 (true, H1668_cp2.1, H1668_cp2.2)) ∧ ptTest pH1668 (runFrom pH1668 (fmask pH1668) (cmask pH1668) (hmask pH1668) 1362 306 (true, H1668_cp2.1, H1668_cp2.2)) 1668 834 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1668_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1668_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1668_fin) true) H1668_seg1) H1668_seg2) (by decide) rfl H1668_fin ptTest_fst
noncomputable def I1668_cp1 : Nat × Nat := t7val% (fastRun pI1668 1 1178 (init pI1668) (init pI1668))
theorem I1668_seg1 : segOK pI1668 1 1178 (init pI1668) (init pI1668) I1668_cp1.1 I1668_cp1.2 = true := by
  decide +kernel
theorem I1668_fin : (prmOK pI1668 1668 && intTest pI1668 (runFrom pI1668 (fmask pI1668) (cmask pI1668) (hmask pI1668) 1179 489 (true, I1668_cp1.1, I1668_cp1.2)) 1668 21 true) = true := by
  decide +kernel
theorem I1668_ok : RunOK pI1668 1668 (runFrom pI1668 (fmask pI1668) (cmask pI1668) (hmask pI1668) 1179 489 (true, I1668_cp1.1, I1668_cp1.2)) ∧ intTest pI1668 (runFrom pI1668 (fmask pI1668) (cmask pI1668) (hmask pI1668) 1179 489 (true, I1668_cp1.1, I1668_cp1.2)) 1668 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1668_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1668_fin) true) I1668_seg1) (by decide) rfl I1668_fin intTest_fst
theorem link1668 : linkOK pL1668 pH1668 pI1668 = true := by decide +kernel
theorem cvx1668 : ConvexBetweenHumps 1668 :=
  cvx_of L1668_ok H1668_ok I1668_ok link1668 (by decide)
theorem cenlink1668 : cenLinkOK pI1668 1668 = true := by decide +kernel
theorem cen1668 : CenterUniqueMin 1668 ∧ DipHyp 1668 ∧ OnePointHyps 1668 :=
  cen_of L1668_ok H1668_ok I1668_ok link1668 cenlink1668

/-! ### `N = 1669` -/

def pL1669 : Prm := ⟨80, 37, 40, 1671, 11, 18446744073709551616, 114063819614847401, 114063819614847401⟩
def pH1669 : Prm := ⟨80, 37, 40, 1671, 11, 18446744073709551616, 114064919126475177, 114064919126475177⟩
def pI1669 : Prm := ⟨67, 33, 31, 1671, 11, 18446744073709551616, 114063819614847401, 114064919126475177⟩
noncomputable def L1669_cp1 : Nat × Nat := t7val% (fastRun pL1669 1 963 (init pL1669) (init pL1669))
theorem L1669_seg1 : segOK pL1669 1 963 (init pL1669) (init pL1669) L1669_cp1.1 L1669_cp1.2 = true := by
  decide +kernel
noncomputable def L1669_cp2 : Nat × Nat := t7val% (fastRun pL1669 1 1362 (init pL1669) (init pL1669))
theorem L1669_seg2 : segOK pL1669 964 399 L1669_cp1.1 L1669_cp1.2 L1669_cp2.1 L1669_cp2.2 = true := by
  decide +kernel
theorem L1669_fin : (prmOK pL1669 1669 && ptTest pL1669 (runFrom pL1669 (fmask pL1669) (cmask pL1669) (hmask pL1669) 1363 306 (true, L1669_cp2.1, L1669_cp2.2)) 1669 835 false) = true := by
  decide +kernel
theorem L1669_ok : RunOK pL1669 1669 (runFrom pL1669 (fmask pL1669) (cmask pL1669) (hmask pL1669) 1363 306 (true, L1669_cp2.1, L1669_cp2.2)) ∧ ptTest pL1669 (runFrom pL1669 (fmask pL1669) (cmask pL1669) (hmask pL1669) 1363 306 (true, L1669_cp2.1, L1669_cp2.2)) 1669 835 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1669_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1669_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1669_fin) true) L1669_seg1) L1669_seg2) (by decide) rfl L1669_fin ptTest_fst
noncomputable def H1669_cp1 : Nat × Nat := t7val% (fastRun pH1669 1 963 (init pH1669) (init pH1669))
theorem H1669_seg1 : segOK pH1669 1 963 (init pH1669) (init pH1669) H1669_cp1.1 H1669_cp1.2 = true := by
  decide +kernel
noncomputable def H1669_cp2 : Nat × Nat := t7val% (fastRun pH1669 1 1362 (init pH1669) (init pH1669))
theorem H1669_seg2 : segOK pH1669 964 399 H1669_cp1.1 H1669_cp1.2 H1669_cp2.1 H1669_cp2.2 = true := by
  decide +kernel
theorem H1669_fin : (prmOK pH1669 1669 && ptTest pH1669 (runFrom pH1669 (fmask pH1669) (cmask pH1669) (hmask pH1669) 1363 306 (true, H1669_cp2.1, H1669_cp2.2)) 1669 835 true) = true := by
  decide +kernel
theorem H1669_ok : RunOK pH1669 1669 (runFrom pH1669 (fmask pH1669) (cmask pH1669) (hmask pH1669) 1363 306 (true, H1669_cp2.1, H1669_cp2.2)) ∧ ptTest pH1669 (runFrom pH1669 (fmask pH1669) (cmask pH1669) (hmask pH1669) 1363 306 (true, H1669_cp2.1, H1669_cp2.2)) 1669 835 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1669_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1669_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1669_fin) true) H1669_seg1) H1669_seg2) (by decide) rfl H1669_fin ptTest_fst
noncomputable def I1669_cp1 : Nat × Nat := t7val% (fastRun pI1669 1 1179 (init pI1669) (init pI1669))
theorem I1669_seg1 : segOK pI1669 1 1179 (init pI1669) (init pI1669) I1669_cp1.1 I1669_cp1.2 = true := by
  decide +kernel
theorem I1669_fin : (prmOK pI1669 1669 && intTest pI1669 (runFrom pI1669 (fmask pI1669) (cmask pI1669) (hmask pI1669) 1180 489 (true, I1669_cp1.1, I1669_cp1.2)) 1669 21 false) = true := by
  decide +kernel
theorem I1669_ok : RunOK pI1669 1669 (runFrom pI1669 (fmask pI1669) (cmask pI1669) (hmask pI1669) 1180 489 (true, I1669_cp1.1, I1669_cp1.2)) ∧ intTest pI1669 (runFrom pI1669 (fmask pI1669) (cmask pI1669) (hmask pI1669) 1180 489 (true, I1669_cp1.1, I1669_cp1.2)) 1669 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1669_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1669_fin) true) I1669_seg1) (by decide) rfl I1669_fin intTest_fst
theorem link1669 : linkOK pL1669 pH1669 pI1669 = true := by decide +kernel
theorem cvx1669 : ConvexBetweenHumps 1669 :=
  cvx_of L1669_ok H1669_ok I1669_ok link1669 (by decide)

/-! ### `N = 1670` -/

def pL1670 : Prm := ⟨80, 37, 40, 1672, 11, 18446744073709551616, 114008003330951504, 114008003330951504⟩
def pH1670 : Prm := ⟨80, 37, 40, 1672, 11, 18446744073709551616, 114009102842579280, 114009102842579280⟩
def pI1670 : Prm := ⟨67, 33, 31, 1672, 11, 18446744073709551616, 114008003330951504, 114009102842579280⟩
noncomputable def L1670_cp1 : Nat × Nat := t7val% (fastRun pL1670 1 963 (init pL1670) (init pL1670))
theorem L1670_seg1 : segOK pL1670 1 963 (init pL1670) (init pL1670) L1670_cp1.1 L1670_cp1.2 = true := by
  decide +kernel
noncomputable def L1670_cp2 : Nat × Nat := t7val% (fastRun pL1670 1 1363 (init pL1670) (init pL1670))
theorem L1670_seg2 : segOK pL1670 964 400 L1670_cp1.1 L1670_cp1.2 L1670_cp2.1 L1670_cp2.2 = true := by
  decide +kernel
theorem L1670_fin : (prmOK pL1670 1670 && ptTest pL1670 (runFrom pL1670 (fmask pL1670) (cmask pL1670) (hmask pL1670) 1364 306 (true, L1670_cp2.1, L1670_cp2.2)) 1670 835 false) = true := by
  decide +kernel
theorem L1670_ok : RunOK pL1670 1670 (runFrom pL1670 (fmask pL1670) (cmask pL1670) (hmask pL1670) 1364 306 (true, L1670_cp2.1, L1670_cp2.2)) ∧ ptTest pL1670 (runFrom pL1670 (fmask pL1670) (cmask pL1670) (hmask pL1670) 1364 306 (true, L1670_cp2.1, L1670_cp2.2)) 1670 835 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1670_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1670_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1670_fin) true) L1670_seg1) L1670_seg2) (by decide) rfl L1670_fin ptTest_fst
noncomputable def H1670_cp1 : Nat × Nat := t7val% (fastRun pH1670 1 963 (init pH1670) (init pH1670))
theorem H1670_seg1 : segOK pH1670 1 963 (init pH1670) (init pH1670) H1670_cp1.1 H1670_cp1.2 = true := by
  decide +kernel
noncomputable def H1670_cp2 : Nat × Nat := t7val% (fastRun pH1670 1 1363 (init pH1670) (init pH1670))
theorem H1670_seg2 : segOK pH1670 964 400 H1670_cp1.1 H1670_cp1.2 H1670_cp2.1 H1670_cp2.2 = true := by
  decide +kernel
theorem H1670_fin : (prmOK pH1670 1670 && ptTest pH1670 (runFrom pH1670 (fmask pH1670) (cmask pH1670) (hmask pH1670) 1364 306 (true, H1670_cp2.1, H1670_cp2.2)) 1670 835 true) = true := by
  decide +kernel
theorem H1670_ok : RunOK pH1670 1670 (runFrom pH1670 (fmask pH1670) (cmask pH1670) (hmask pH1670) 1364 306 (true, H1670_cp2.1, H1670_cp2.2)) ∧ ptTest pH1670 (runFrom pH1670 (fmask pH1670) (cmask pH1670) (hmask pH1670) 1364 306 (true, H1670_cp2.1, H1670_cp2.2)) 1670 835 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1670_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1670_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1670_fin) true) H1670_seg1) H1670_seg2) (by decide) rfl H1670_fin ptTest_fst
noncomputable def I1670_cp1 : Nat × Nat := t7val% (fastRun pI1670 1 1180 (init pI1670) (init pI1670))
theorem I1670_seg1 : segOK pI1670 1 1180 (init pI1670) (init pI1670) I1670_cp1.1 I1670_cp1.2 = true := by
  decide +kernel
theorem I1670_fin : (prmOK pI1670 1670 && intTest pI1670 (runFrom pI1670 (fmask pI1670) (cmask pI1670) (hmask pI1670) 1181 489 (true, I1670_cp1.1, I1670_cp1.2)) 1670 21 true) = true := by
  decide +kernel
theorem I1670_ok : RunOK pI1670 1670 (runFrom pI1670 (fmask pI1670) (cmask pI1670) (hmask pI1670) 1181 489 (true, I1670_cp1.1, I1670_cp1.2)) ∧ intTest pI1670 (runFrom pI1670 (fmask pI1670) (cmask pI1670) (hmask pI1670) 1181 489 (true, I1670_cp1.1, I1670_cp1.2)) 1670 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1670_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1670_fin) true) I1670_seg1) (by decide) rfl I1670_fin intTest_fst
theorem link1670 : linkOK pL1670 pH1670 pI1670 = true := by decide +kernel
theorem cvx1670 : ConvexBetweenHumps 1670 :=
  cvx_of L1670_ok H1670_ok I1670_ok link1670 (by decide)
theorem cenlink1670 : cenLinkOK pI1670 1670 = true := by decide +kernel
theorem cen1670 : CenterUniqueMin 1670 ∧ DipHyp 1670 ∧ OnePointHyps 1670 :=
  cen_of L1670_ok H1670_ok I1670_ok link1670 cenlink1670

/-! ### `N = 1671` -/

def pL1671 : Prm := ⟨80, 37, 40, 1673, 11, 18446744073709551616, 113952222214352783, 113952222214352783⟩
def pH1671 : Prm := ⟨80, 37, 40, 1673, 11, 18446744073709551616, 113953321725980559, 113953321725980559⟩
def pI1671 : Prm := ⟨67, 33, 31, 1673, 11, 18446744073709551616, 113952222214352783, 113953321725980559⟩
noncomputable def L1671_cp1 : Nat × Nat := t7val% (fastRun pL1671 1 964 (init pL1671) (init pL1671))
theorem L1671_seg1 : segOK pL1671 1 964 (init pL1671) (init pL1671) L1671_cp1.1 L1671_cp1.2 = true := by
  decide +kernel
noncomputable def L1671_cp2 : Nat × Nat := t7val% (fastRun pL1671 1 1363 (init pL1671) (init pL1671))
theorem L1671_seg2 : segOK pL1671 965 399 L1671_cp1.1 L1671_cp1.2 L1671_cp2.1 L1671_cp2.2 = true := by
  decide +kernel
theorem L1671_fin : (prmOK pL1671 1671 && ptTest pL1671 (runFrom pL1671 (fmask pL1671) (cmask pL1671) (hmask pL1671) 1364 307 (true, L1671_cp2.1, L1671_cp2.2)) 1671 836 false) = true := by
  decide +kernel
theorem L1671_ok : RunOK pL1671 1671 (runFrom pL1671 (fmask pL1671) (cmask pL1671) (hmask pL1671) 1364 307 (true, L1671_cp2.1, L1671_cp2.2)) ∧ ptTest pL1671 (runFrom pL1671 (fmask pL1671) (cmask pL1671) (hmask pL1671) 1364 307 (true, L1671_cp2.1, L1671_cp2.2)) 1671 836 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1671_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1671_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1671_fin) true) L1671_seg1) L1671_seg2) (by decide) rfl L1671_fin ptTest_fst
noncomputable def H1671_cp1 : Nat × Nat := t7val% (fastRun pH1671 1 964 (init pH1671) (init pH1671))
theorem H1671_seg1 : segOK pH1671 1 964 (init pH1671) (init pH1671) H1671_cp1.1 H1671_cp1.2 = true := by
  decide +kernel
noncomputable def H1671_cp2 : Nat × Nat := t7val% (fastRun pH1671 1 1363 (init pH1671) (init pH1671))
theorem H1671_seg2 : segOK pH1671 965 399 H1671_cp1.1 H1671_cp1.2 H1671_cp2.1 H1671_cp2.2 = true := by
  decide +kernel
theorem H1671_fin : (prmOK pH1671 1671 && ptTest pH1671 (runFrom pH1671 (fmask pH1671) (cmask pH1671) (hmask pH1671) 1364 307 (true, H1671_cp2.1, H1671_cp2.2)) 1671 836 true) = true := by
  decide +kernel
theorem H1671_ok : RunOK pH1671 1671 (runFrom pH1671 (fmask pH1671) (cmask pH1671) (hmask pH1671) 1364 307 (true, H1671_cp2.1, H1671_cp2.2)) ∧ ptTest pH1671 (runFrom pH1671 (fmask pH1671) (cmask pH1671) (hmask pH1671) 1364 307 (true, H1671_cp2.1, H1671_cp2.2)) 1671 836 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1671_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1671_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1671_fin) true) H1671_seg1) H1671_seg2) (by decide) rfl H1671_fin ptTest_fst
noncomputable def I1671_cp1 : Nat × Nat := t7val% (fastRun pI1671 1 1181 (init pI1671) (init pI1671))
theorem I1671_seg1 : segOK pI1671 1 1181 (init pI1671) (init pI1671) I1671_cp1.1 I1671_cp1.2 = true := by
  decide +kernel
theorem I1671_fin : (prmOK pI1671 1671 && intTest pI1671 (runFrom pI1671 (fmask pI1671) (cmask pI1671) (hmask pI1671) 1182 489 (true, I1671_cp1.1, I1671_cp1.2)) 1671 21 false) = true := by
  decide +kernel
theorem I1671_ok : RunOK pI1671 1671 (runFrom pI1671 (fmask pI1671) (cmask pI1671) (hmask pI1671) 1182 489 (true, I1671_cp1.1, I1671_cp1.2)) ∧ intTest pI1671 (runFrom pI1671 (fmask pI1671) (cmask pI1671) (hmask pI1671) 1182 489 (true, I1671_cp1.1, I1671_cp1.2)) 1671 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1671_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1671_fin) true) I1671_seg1) (by decide) rfl I1671_fin intTest_fst
theorem link1671 : linkOK pL1671 pH1671 pI1671 = true := by decide +kernel
theorem cvx1671 : ConvexBetweenHumps 1671 :=
  cvx_of L1671_ok H1671_ok I1671_ok link1671 (by decide)

/-! ### `N = 1672` -/

def pL1672 : Prm := ⟨80, 37, 40, 1674, 11, 18446744073709551616, 113896524485116949, 113896524485116949⟩
def pH1672 : Prm := ⟨80, 37, 40, 1674, 11, 18446744073709551616, 113897623996744725, 113897623996744725⟩
def pI1672 : Prm := ⟨67, 33, 31, 1674, 11, 18446744073709551616, 113896524485116949, 113897623996744725⟩
noncomputable def L1672_cp1 : Nat × Nat := t7val% (fastRun pL1672 1 964 (init pL1672) (init pL1672))
theorem L1672_seg1 : segOK pL1672 1 964 (init pL1672) (init pL1672) L1672_cp1.1 L1672_cp1.2 = true := by
  decide +kernel
noncomputable def L1672_cp2 : Nat × Nat := t7val% (fastRun pL1672 1 1364 (init pL1672) (init pL1672))
theorem L1672_seg2 : segOK pL1672 965 400 L1672_cp1.1 L1672_cp1.2 L1672_cp2.1 L1672_cp2.2 = true := by
  decide +kernel
theorem L1672_fin : (prmOK pL1672 1672 && ptTest pL1672 (runFrom pL1672 (fmask pL1672) (cmask pL1672) (hmask pL1672) 1365 307 (true, L1672_cp2.1, L1672_cp2.2)) 1672 836 false) = true := by
  decide +kernel
theorem L1672_ok : RunOK pL1672 1672 (runFrom pL1672 (fmask pL1672) (cmask pL1672) (hmask pL1672) 1365 307 (true, L1672_cp2.1, L1672_cp2.2)) ∧ ptTest pL1672 (runFrom pL1672 (fmask pL1672) (cmask pL1672) (hmask pL1672) 1365 307 (true, L1672_cp2.1, L1672_cp2.2)) 1672 836 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1672_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1672_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1672_fin) true) L1672_seg1) L1672_seg2) (by decide) rfl L1672_fin ptTest_fst
noncomputable def H1672_cp1 : Nat × Nat := t7val% (fastRun pH1672 1 964 (init pH1672) (init pH1672))
theorem H1672_seg1 : segOK pH1672 1 964 (init pH1672) (init pH1672) H1672_cp1.1 H1672_cp1.2 = true := by
  decide +kernel
noncomputable def H1672_cp2 : Nat × Nat := t7val% (fastRun pH1672 1 1364 (init pH1672) (init pH1672))
theorem H1672_seg2 : segOK pH1672 965 400 H1672_cp1.1 H1672_cp1.2 H1672_cp2.1 H1672_cp2.2 = true := by
  decide +kernel
theorem H1672_fin : (prmOK pH1672 1672 && ptTest pH1672 (runFrom pH1672 (fmask pH1672) (cmask pH1672) (hmask pH1672) 1365 307 (true, H1672_cp2.1, H1672_cp2.2)) 1672 836 true) = true := by
  decide +kernel
theorem H1672_ok : RunOK pH1672 1672 (runFrom pH1672 (fmask pH1672) (cmask pH1672) (hmask pH1672) 1365 307 (true, H1672_cp2.1, H1672_cp2.2)) ∧ ptTest pH1672 (runFrom pH1672 (fmask pH1672) (cmask pH1672) (hmask pH1672) 1365 307 (true, H1672_cp2.1, H1672_cp2.2)) 1672 836 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1672_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1672_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1672_fin) true) H1672_seg1) H1672_seg2) (by decide) rfl H1672_fin ptTest_fst
noncomputable def I1672_cp1 : Nat × Nat := t7val% (fastRun pI1672 1 1181 (init pI1672) (init pI1672))
theorem I1672_seg1 : segOK pI1672 1 1181 (init pI1672) (init pI1672) I1672_cp1.1 I1672_cp1.2 = true := by
  decide +kernel
theorem I1672_fin : (prmOK pI1672 1672 && intTest pI1672 (runFrom pI1672 (fmask pI1672) (cmask pI1672) (hmask pI1672) 1182 490 (true, I1672_cp1.1, I1672_cp1.2)) 1672 21 true) = true := by
  decide +kernel
theorem I1672_ok : RunOK pI1672 1672 (runFrom pI1672 (fmask pI1672) (cmask pI1672) (hmask pI1672) 1182 490 (true, I1672_cp1.1, I1672_cp1.2)) ∧ intTest pI1672 (runFrom pI1672 (fmask pI1672) (cmask pI1672) (hmask pI1672) 1182 490 (true, I1672_cp1.1, I1672_cp1.2)) 1672 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1672_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1672_fin) true) I1672_seg1) (by decide) rfl I1672_fin intTest_fst
theorem link1672 : linkOK pL1672 pH1672 pI1672 = true := by decide +kernel
theorem cvx1672 : ConvexBetweenHumps 1672 :=
  cvx_of L1672_ok H1672_ok I1672_ok link1672 (by decide)
theorem cenlink1672 : cenLinkOK pI1672 1672 = true := by decide +kernel
theorem cen1672 : CenterUniqueMin 1672 ∧ DipHyp 1672 ∧ OnePointHyps 1672 :=
  cen_of L1672_ok H1672_ok I1672_ok link1672 cenlink1672

/-! ### `N = 1673` -/

def pL1673 : Prm := ⟨80, 37, 40, 1675, 11, 18446744073709551616, 113840861816279411, 113840861816279411⟩
def pH1673 : Prm := ⟨80, 37, 40, 1675, 11, 18446744073709551616, 113841961327907187, 113841961327907187⟩
def pI1673 : Prm := ⟨67, 33, 31, 1675, 11, 18446744073709551616, 113840861816279411, 113841961327907187⟩
noncomputable def L1673_cp1 : Nat × Nat := t7val% (fastRun pL1673 1 965 (init pL1673) (init pL1673))
theorem L1673_seg1 : segOK pL1673 1 965 (init pL1673) (init pL1673) L1673_cp1.1 L1673_cp1.2 = true := by
  decide +kernel
noncomputable def L1673_cp2 : Nat × Nat := t7val% (fastRun pL1673 1 1365 (init pL1673) (init pL1673))
theorem L1673_seg2 : segOK pL1673 966 400 L1673_cp1.1 L1673_cp1.2 L1673_cp2.1 L1673_cp2.2 = true := by
  decide +kernel
theorem L1673_fin : (prmOK pL1673 1673 && ptTest pL1673 (runFrom pL1673 (fmask pL1673) (cmask pL1673) (hmask pL1673) 1366 307 (true, L1673_cp2.1, L1673_cp2.2)) 1673 837 false) = true := by
  decide +kernel
theorem L1673_ok : RunOK pL1673 1673 (runFrom pL1673 (fmask pL1673) (cmask pL1673) (hmask pL1673) 1366 307 (true, L1673_cp2.1, L1673_cp2.2)) ∧ ptTest pL1673 (runFrom pL1673 (fmask pL1673) (cmask pL1673) (hmask pL1673) 1366 307 (true, L1673_cp2.1, L1673_cp2.2)) 1673 837 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1673_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1673_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1673_fin) true) L1673_seg1) L1673_seg2) (by decide) rfl L1673_fin ptTest_fst
noncomputable def H1673_cp1 : Nat × Nat := t7val% (fastRun pH1673 1 965 (init pH1673) (init pH1673))
theorem H1673_seg1 : segOK pH1673 1 965 (init pH1673) (init pH1673) H1673_cp1.1 H1673_cp1.2 = true := by
  decide +kernel
noncomputable def H1673_cp2 : Nat × Nat := t7val% (fastRun pH1673 1 1365 (init pH1673) (init pH1673))
theorem H1673_seg2 : segOK pH1673 966 400 H1673_cp1.1 H1673_cp1.2 H1673_cp2.1 H1673_cp2.2 = true := by
  decide +kernel
theorem H1673_fin : (prmOK pH1673 1673 && ptTest pH1673 (runFrom pH1673 (fmask pH1673) (cmask pH1673) (hmask pH1673) 1366 307 (true, H1673_cp2.1, H1673_cp2.2)) 1673 837 true) = true := by
  decide +kernel
theorem H1673_ok : RunOK pH1673 1673 (runFrom pH1673 (fmask pH1673) (cmask pH1673) (hmask pH1673) 1366 307 (true, H1673_cp2.1, H1673_cp2.2)) ∧ ptTest pH1673 (runFrom pH1673 (fmask pH1673) (cmask pH1673) (hmask pH1673) 1366 307 (true, H1673_cp2.1, H1673_cp2.2)) 1673 837 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1673_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1673_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1673_fin) true) H1673_seg1) H1673_seg2) (by decide) rfl H1673_fin ptTest_fst
noncomputable def I1673_cp1 : Nat × Nat := t7val% (fastRun pI1673 1 1182 (init pI1673) (init pI1673))
theorem I1673_seg1 : segOK pI1673 1 1182 (init pI1673) (init pI1673) I1673_cp1.1 I1673_cp1.2 = true := by
  decide +kernel
theorem I1673_fin : (prmOK pI1673 1673 && intTest pI1673 (runFrom pI1673 (fmask pI1673) (cmask pI1673) (hmask pI1673) 1183 490 (true, I1673_cp1.1, I1673_cp1.2)) 1673 21 false) = true := by
  decide +kernel
theorem I1673_ok : RunOK pI1673 1673 (runFrom pI1673 (fmask pI1673) (cmask pI1673) (hmask pI1673) 1183 490 (true, I1673_cp1.1, I1673_cp1.2)) ∧ intTest pI1673 (runFrom pI1673 (fmask pI1673) (cmask pI1673) (hmask pI1673) 1183 490 (true, I1673_cp1.1, I1673_cp1.2)) 1673 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1673_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1673_fin) true) I1673_seg1) (by decide) rfl I1673_fin intTest_fst
theorem link1673 : linkOK pL1673 pH1673 pI1673 = true := by decide +kernel
theorem cvx1673 : ConvexBetweenHumps 1673 :=
  cvx_of L1673_ok H1673_ok I1673_ok link1673 (by decide)

/-! ### `N = 1674` -/

def pL1674 : Prm := ⟨80, 37, 40, 1676, 11, 18446744073709551616, 113785282252588023, 113785282252588023⟩
def pH1674 : Prm := ⟨80, 37, 40, 1676, 11, 18446744073709551616, 113786381764215799, 113786381764215799⟩
def pI1674 : Prm := ⟨68, 33, 32, 1676, 11, 18446744073709551616, 113785282252588023, 113786381764215799⟩
noncomputable def L1674_cp1 : Nat × Nat := t7val% (fastRun pL1674 1 965 (init pL1674) (init pL1674))
theorem L1674_seg1 : segOK pL1674 1 965 (init pL1674) (init pL1674) L1674_cp1.1 L1674_cp1.2 = true := by
  decide +kernel
noncomputable def L1674_cp2 : Nat × Nat := t7val% (fastRun pL1674 1 1366 (init pL1674) (init pL1674))
theorem L1674_seg2 : segOK pL1674 966 401 L1674_cp1.1 L1674_cp1.2 L1674_cp2.1 L1674_cp2.2 = true := by
  decide +kernel
theorem L1674_fin : (prmOK pL1674 1674 && ptTest pL1674 (runFrom pL1674 (fmask pL1674) (cmask pL1674) (hmask pL1674) 1367 307 (true, L1674_cp2.1, L1674_cp2.2)) 1674 837 false) = true := by
  decide +kernel
theorem L1674_ok : RunOK pL1674 1674 (runFrom pL1674 (fmask pL1674) (cmask pL1674) (hmask pL1674) 1367 307 (true, L1674_cp2.1, L1674_cp2.2)) ∧ ptTest pL1674 (runFrom pL1674 (fmask pL1674) (cmask pL1674) (hmask pL1674) 1367 307 (true, L1674_cp2.1, L1674_cp2.2)) 1674 837 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1674_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1674_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1674_fin) true) L1674_seg1) L1674_seg2) (by decide) rfl L1674_fin ptTest_fst
noncomputable def H1674_cp1 : Nat × Nat := t7val% (fastRun pH1674 1 965 (init pH1674) (init pH1674))
theorem H1674_seg1 : segOK pH1674 1 965 (init pH1674) (init pH1674) H1674_cp1.1 H1674_cp1.2 = true := by
  decide +kernel
noncomputable def H1674_cp2 : Nat × Nat := t7val% (fastRun pH1674 1 1366 (init pH1674) (init pH1674))
theorem H1674_seg2 : segOK pH1674 966 401 H1674_cp1.1 H1674_cp1.2 H1674_cp2.1 H1674_cp2.2 = true := by
  decide +kernel
theorem H1674_fin : (prmOK pH1674 1674 && ptTest pH1674 (runFrom pH1674 (fmask pH1674) (cmask pH1674) (hmask pH1674) 1367 307 (true, H1674_cp2.1, H1674_cp2.2)) 1674 837 true) = true := by
  decide +kernel
theorem H1674_ok : RunOK pH1674 1674 (runFrom pH1674 (fmask pH1674) (cmask pH1674) (hmask pH1674) 1367 307 (true, H1674_cp2.1, H1674_cp2.2)) ∧ ptTest pH1674 (runFrom pH1674 (fmask pH1674) (cmask pH1674) (hmask pH1674) 1367 307 (true, H1674_cp2.1, H1674_cp2.2)) 1674 837 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1674_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1674_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1674_fin) true) H1674_seg1) H1674_seg2) (by decide) rfl H1674_fin ptTest_fst
noncomputable def I1674_cp1 : Nat × Nat := t7val% (fastRun pI1674 1 1183 (init pI1674) (init pI1674))
theorem I1674_seg1 : segOK pI1674 1 1183 (init pI1674) (init pI1674) I1674_cp1.1 I1674_cp1.2 = true := by
  decide +kernel
theorem I1674_fin : (prmOK pI1674 1674 && intTest pI1674 (runFrom pI1674 (fmask pI1674) (cmask pI1674) (hmask pI1674) 1184 490 (true, I1674_cp1.1, I1674_cp1.2)) 1674 21 true) = true := by
  decide +kernel
theorem I1674_ok : RunOK pI1674 1674 (runFrom pI1674 (fmask pI1674) (cmask pI1674) (hmask pI1674) 1184 490 (true, I1674_cp1.1, I1674_cp1.2)) ∧ intTest pI1674 (runFrom pI1674 (fmask pI1674) (cmask pI1674) (hmask pI1674) 1184 490 (true, I1674_cp1.1, I1674_cp1.2)) 1674 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1674_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1674_fin) true) I1674_seg1) (by decide) rfl I1674_fin intTest_fst
theorem link1674 : linkOK pL1674 pH1674 pI1674 = true := by decide +kernel
theorem cvx1674 : ConvexBetweenHumps 1674 :=
  cvx_of L1674_ok H1674_ok I1674_ok link1674 (by decide)
theorem cenlink1674 : cenLinkOK pI1674 1674 = true := by decide +kernel
theorem cen1674 : CenterUniqueMin 1674 ∧ DipHyp 1674 ∧ OnePointHyps 1674 :=
  cen_of L1674_ok H1674_ok I1674_ok link1674 cenlink1674

/-! ### `N = 1675` -/

def pL1675 : Prm := ⟨80, 37, 40, 1677, 11, 18446744073709551616, 113729737642875663, 113729737642875663⟩
def pH1675 : Prm := ⟨80, 37, 40, 1677, 11, 18446744073709551616, 113730837154503439, 113730837154503439⟩
def pI1675 : Prm := ⟨68, 33, 32, 1677, 11, 18446744073709551616, 113729737642875663, 113730837154503439⟩
noncomputable def L1675_cp1 : Nat × Nat := t7val% (fastRun pL1675 1 966 (init pL1675) (init pL1675))
theorem L1675_seg1 : segOK pL1675 1 966 (init pL1675) (init pL1675) L1675_cp1.1 L1675_cp1.2 = true := by
  decide +kernel
noncomputable def L1675_cp2 : Nat × Nat := t7val% (fastRun pL1675 1 1367 (init pL1675) (init pL1675))
theorem L1675_seg2 : segOK pL1675 967 401 L1675_cp1.1 L1675_cp1.2 L1675_cp2.1 L1675_cp2.2 = true := by
  decide +kernel
theorem L1675_fin : (prmOK pL1675 1675 && ptTest pL1675 (runFrom pL1675 (fmask pL1675) (cmask pL1675) (hmask pL1675) 1368 307 (true, L1675_cp2.1, L1675_cp2.2)) 1675 838 false) = true := by
  decide +kernel
theorem L1675_ok : RunOK pL1675 1675 (runFrom pL1675 (fmask pL1675) (cmask pL1675) (hmask pL1675) 1368 307 (true, L1675_cp2.1, L1675_cp2.2)) ∧ ptTest pL1675 (runFrom pL1675 (fmask pL1675) (cmask pL1675) (hmask pL1675) 1368 307 (true, L1675_cp2.1, L1675_cp2.2)) 1675 838 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1675_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1675_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1675_fin) true) L1675_seg1) L1675_seg2) (by decide) rfl L1675_fin ptTest_fst
noncomputable def H1675_cp1 : Nat × Nat := t7val% (fastRun pH1675 1 966 (init pH1675) (init pH1675))
theorem H1675_seg1 : segOK pH1675 1 966 (init pH1675) (init pH1675) H1675_cp1.1 H1675_cp1.2 = true := by
  decide +kernel
noncomputable def H1675_cp2 : Nat × Nat := t7val% (fastRun pH1675 1 1367 (init pH1675) (init pH1675))
theorem H1675_seg2 : segOK pH1675 967 401 H1675_cp1.1 H1675_cp1.2 H1675_cp2.1 H1675_cp2.2 = true := by
  decide +kernel
theorem H1675_fin : (prmOK pH1675 1675 && ptTest pH1675 (runFrom pH1675 (fmask pH1675) (cmask pH1675) (hmask pH1675) 1368 307 (true, H1675_cp2.1, H1675_cp2.2)) 1675 838 true) = true := by
  decide +kernel
theorem H1675_ok : RunOK pH1675 1675 (runFrom pH1675 (fmask pH1675) (cmask pH1675) (hmask pH1675) 1368 307 (true, H1675_cp2.1, H1675_cp2.2)) ∧ ptTest pH1675 (runFrom pH1675 (fmask pH1675) (cmask pH1675) (hmask pH1675) 1368 307 (true, H1675_cp2.1, H1675_cp2.2)) 1675 838 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1675_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1675_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1675_fin) true) H1675_seg1) H1675_seg2) (by decide) rfl H1675_fin ptTest_fst
noncomputable def I1675_cp1 : Nat × Nat := t7val% (fastRun pI1675 1 1183 (init pI1675) (init pI1675))
theorem I1675_seg1 : segOK pI1675 1 1183 (init pI1675) (init pI1675) I1675_cp1.1 I1675_cp1.2 = true := by
  decide +kernel
theorem I1675_fin : (prmOK pI1675 1675 && intTest pI1675 (runFrom pI1675 (fmask pI1675) (cmask pI1675) (hmask pI1675) 1184 491 (true, I1675_cp1.1, I1675_cp1.2)) 1675 21 false) = true := by
  decide +kernel
theorem I1675_ok : RunOK pI1675 1675 (runFrom pI1675 (fmask pI1675) (cmask pI1675) (hmask pI1675) 1184 491 (true, I1675_cp1.1, I1675_cp1.2)) ∧ intTest pI1675 (runFrom pI1675 (fmask pI1675) (cmask pI1675) (hmask pI1675) 1184 491 (true, I1675_cp1.1, I1675_cp1.2)) 1675 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1675_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1675_fin) true) I1675_seg1) (by decide) rfl I1675_fin intTest_fst
theorem link1675 : linkOK pL1675 pH1675 pI1675 = true := by decide +kernel
theorem cvx1675 : ConvexBetweenHumps 1675 :=
  cvx_of L1675_ok H1675_ok I1675_ok link1675 (by decide)

/-! ### `N = 1676` -/

def pL1676 : Prm := ⟨80, 37, 40, 1678, 11, 18446744073709551616, 113674275857328647, 113674275857328647⟩
def pH1676 : Prm := ⟨80, 37, 40, 1678, 11, 18446744073709551616, 113675375368956423, 113675375368956423⟩
def pI1676 : Prm := ⟨68, 33, 32, 1678, 11, 18446744073709551616, 113674275857328647, 113675375368956423⟩
noncomputable def L1676_cp1 : Nat × Nat := t7val% (fastRun pL1676 1 967 (init pL1676) (init pL1676))
theorem L1676_seg1 : segOK pL1676 1 967 (init pL1676) (init pL1676) L1676_cp1.1 L1676_cp1.2 = true := by
  decide +kernel
noncomputable def L1676_cp2 : Nat × Nat := t7val% (fastRun pL1676 1 1367 (init pL1676) (init pL1676))
theorem L1676_seg2 : segOK pL1676 968 400 L1676_cp1.1 L1676_cp1.2 L1676_cp2.1 L1676_cp2.2 = true := by
  decide +kernel
theorem L1676_fin : (prmOK pL1676 1676 && ptTest pL1676 (runFrom pL1676 (fmask pL1676) (cmask pL1676) (hmask pL1676) 1368 308 (true, L1676_cp2.1, L1676_cp2.2)) 1676 838 false) = true := by
  decide +kernel
theorem L1676_ok : RunOK pL1676 1676 (runFrom pL1676 (fmask pL1676) (cmask pL1676) (hmask pL1676) 1368 308 (true, L1676_cp2.1, L1676_cp2.2)) ∧ ptTest pL1676 (runFrom pL1676 (fmask pL1676) (cmask pL1676) (hmask pL1676) 1368 308 (true, L1676_cp2.1, L1676_cp2.2)) 1676 838 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1676_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1676_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1676_fin) true) L1676_seg1) L1676_seg2) (by decide) rfl L1676_fin ptTest_fst
noncomputable def H1676_cp1 : Nat × Nat := t7val% (fastRun pH1676 1 967 (init pH1676) (init pH1676))
theorem H1676_seg1 : segOK pH1676 1 967 (init pH1676) (init pH1676) H1676_cp1.1 H1676_cp1.2 = true := by
  decide +kernel
noncomputable def H1676_cp2 : Nat × Nat := t7val% (fastRun pH1676 1 1367 (init pH1676) (init pH1676))
theorem H1676_seg2 : segOK pH1676 968 400 H1676_cp1.1 H1676_cp1.2 H1676_cp2.1 H1676_cp2.2 = true := by
  decide +kernel
theorem H1676_fin : (prmOK pH1676 1676 && ptTest pH1676 (runFrom pH1676 (fmask pH1676) (cmask pH1676) (hmask pH1676) 1368 308 (true, H1676_cp2.1, H1676_cp2.2)) 1676 838 true) = true := by
  decide +kernel
theorem H1676_ok : RunOK pH1676 1676 (runFrom pH1676 (fmask pH1676) (cmask pH1676) (hmask pH1676) 1368 308 (true, H1676_cp2.1, H1676_cp2.2)) ∧ ptTest pH1676 (runFrom pH1676 (fmask pH1676) (cmask pH1676) (hmask pH1676) 1368 308 (true, H1676_cp2.1, H1676_cp2.2)) 1676 838 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1676_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1676_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1676_fin) true) H1676_seg1) H1676_seg2) (by decide) rfl H1676_fin ptTest_fst
noncomputable def I1676_cp1 : Nat × Nat := t7val% (fastRun pI1676 1 1184 (init pI1676) (init pI1676))
theorem I1676_seg1 : segOK pI1676 1 1184 (init pI1676) (init pI1676) I1676_cp1.1 I1676_cp1.2 = true := by
  decide +kernel
theorem I1676_fin : (prmOK pI1676 1676 && intTest pI1676 (runFrom pI1676 (fmask pI1676) (cmask pI1676) (hmask pI1676) 1185 491 (true, I1676_cp1.1, I1676_cp1.2)) 1676 21 true) = true := by
  decide +kernel
theorem I1676_ok : RunOK pI1676 1676 (runFrom pI1676 (fmask pI1676) (cmask pI1676) (hmask pI1676) 1185 491 (true, I1676_cp1.1, I1676_cp1.2)) ∧ intTest pI1676 (runFrom pI1676 (fmask pI1676) (cmask pI1676) (hmask pI1676) 1185 491 (true, I1676_cp1.1, I1676_cp1.2)) 1676 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1676_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1676_fin) true) I1676_seg1) (by decide) rfl I1676_fin intTest_fst
theorem link1676 : linkOK pL1676 pH1676 pI1676 = true := by decide +kernel
theorem cvx1676 : ConvexBetweenHumps 1676 :=
  cvx_of L1676_ok H1676_ok I1676_ok link1676 (by decide)
theorem cenlink1676 : cenLinkOK pI1676 1676 = true := by decide +kernel
theorem cen1676 : CenterUniqueMin 1676 ∧ DipHyp 1676 ∧ OnePointHyps 1676 :=
  cen_of L1676_ok H1676_ok I1676_ok link1676 cenlink1676

/-! ### `N = 1677` -/

def pL1677 : Prm := ⟨80, 37, 40, 1679, 11, 18446744073709551616, 113618848919784114, 113618848919784114⟩
def pH1677 : Prm := ⟨80, 37, 40, 1679, 11, 18446744073709551616, 113619948431411890, 113619948431411890⟩
def pI1677 : Prm := ⟨67, 33, 31, 1679, 11, 18446744073709551616, 113618848919784114, 113619948431411890⟩
noncomputable def L1677_cp1 : Nat × Nat := t7val% (fastRun pL1677 1 967 (init pL1677) (init pL1677))
theorem L1677_seg1 : segOK pL1677 1 967 (init pL1677) (init pL1677) L1677_cp1.1 L1677_cp1.2 = true := by
  decide +kernel
noncomputable def L1677_cp2 : Nat × Nat := t7val% (fastRun pL1677 1 1368 (init pL1677) (init pL1677))
theorem L1677_seg2 : segOK pL1677 968 401 L1677_cp1.1 L1677_cp1.2 L1677_cp2.1 L1677_cp2.2 = true := by
  decide +kernel
theorem L1677_fin : (prmOK pL1677 1677 && ptTest pL1677 (runFrom pL1677 (fmask pL1677) (cmask pL1677) (hmask pL1677) 1369 308 (true, L1677_cp2.1, L1677_cp2.2)) 1677 839 false) = true := by
  decide +kernel
theorem L1677_ok : RunOK pL1677 1677 (runFrom pL1677 (fmask pL1677) (cmask pL1677) (hmask pL1677) 1369 308 (true, L1677_cp2.1, L1677_cp2.2)) ∧ ptTest pL1677 (runFrom pL1677 (fmask pL1677) (cmask pL1677) (hmask pL1677) 1369 308 (true, L1677_cp2.1, L1677_cp2.2)) 1677 839 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1677_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1677_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1677_fin) true) L1677_seg1) L1677_seg2) (by decide) rfl L1677_fin ptTest_fst
noncomputable def H1677_cp1 : Nat × Nat := t7val% (fastRun pH1677 1 967 (init pH1677) (init pH1677))
theorem H1677_seg1 : segOK pH1677 1 967 (init pH1677) (init pH1677) H1677_cp1.1 H1677_cp1.2 = true := by
  decide +kernel
noncomputable def H1677_cp2 : Nat × Nat := t7val% (fastRun pH1677 1 1368 (init pH1677) (init pH1677))
theorem H1677_seg2 : segOK pH1677 968 401 H1677_cp1.1 H1677_cp1.2 H1677_cp2.1 H1677_cp2.2 = true := by
  decide +kernel
theorem H1677_fin : (prmOK pH1677 1677 && ptTest pH1677 (runFrom pH1677 (fmask pH1677) (cmask pH1677) (hmask pH1677) 1369 308 (true, H1677_cp2.1, H1677_cp2.2)) 1677 839 true) = true := by
  decide +kernel
theorem H1677_ok : RunOK pH1677 1677 (runFrom pH1677 (fmask pH1677) (cmask pH1677) (hmask pH1677) 1369 308 (true, H1677_cp2.1, H1677_cp2.2)) ∧ ptTest pH1677 (runFrom pH1677 (fmask pH1677) (cmask pH1677) (hmask pH1677) 1369 308 (true, H1677_cp2.1, H1677_cp2.2)) 1677 839 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1677_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1677_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1677_fin) true) H1677_seg1) H1677_seg2) (by decide) rfl H1677_fin ptTest_fst
noncomputable def I1677_cp1 : Nat × Nat := t7val% (fastRun pI1677 1 1185 (init pI1677) (init pI1677))
theorem I1677_seg1 : segOK pI1677 1 1185 (init pI1677) (init pI1677) I1677_cp1.1 I1677_cp1.2 = true := by
  decide +kernel
theorem I1677_fin : (prmOK pI1677 1677 && intTest pI1677 (runFrom pI1677 (fmask pI1677) (cmask pI1677) (hmask pI1677) 1186 491 (true, I1677_cp1.1, I1677_cp1.2)) 1677 21 false) = true := by
  decide +kernel
theorem I1677_ok : RunOK pI1677 1677 (runFrom pI1677 (fmask pI1677) (cmask pI1677) (hmask pI1677) 1186 491 (true, I1677_cp1.1, I1677_cp1.2)) ∧ intTest pI1677 (runFrom pI1677 (fmask pI1677) (cmask pI1677) (hmask pI1677) 1186 491 (true, I1677_cp1.1, I1677_cp1.2)) 1677 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1677_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1677_fin) true) I1677_seg1) (by decide) rfl I1677_fin intTest_fst
theorem link1677 : linkOK pL1677 pH1677 pI1677 = true := by decide +kernel
theorem cvx1677 : ConvexBetweenHumps 1677 :=
  cvx_of L1677_ok H1677_ok I1677_ok link1677 (by decide)

/-! ### `N = 1678` -/

def pL1678 : Prm := ⟨80, 37, 40, 1680, 11, 18446744073709551616, 113563504526715393, 113563504526715393⟩
def pH1678 : Prm := ⟨80, 37, 40, 1680, 11, 18446744073709551616, 113564604038343169, 113564604038343169⟩
def pI1678 : Prm := ⟨67, 33, 31, 1680, 11, 18446744073709551616, 113563504526715393, 113564604038343169⟩
noncomputable def L1678_cp1 : Nat × Nat := t7val% (fastRun pL1678 1 968 (init pL1678) (init pL1678))
theorem L1678_seg1 : segOK pL1678 1 968 (init pL1678) (init pL1678) L1678_cp1.1 L1678_cp1.2 = true := by
  decide +kernel
noncomputable def L1678_cp2 : Nat × Nat := t7val% (fastRun pL1678 1 1369 (init pL1678) (init pL1678))
theorem L1678_seg2 : segOK pL1678 969 401 L1678_cp1.1 L1678_cp1.2 L1678_cp2.1 L1678_cp2.2 = true := by
  decide +kernel
theorem L1678_fin : (prmOK pL1678 1678 && ptTest pL1678 (runFrom pL1678 (fmask pL1678) (cmask pL1678) (hmask pL1678) 1370 308 (true, L1678_cp2.1, L1678_cp2.2)) 1678 839 false) = true := by
  decide +kernel
theorem L1678_ok : RunOK pL1678 1678 (runFrom pL1678 (fmask pL1678) (cmask pL1678) (hmask pL1678) 1370 308 (true, L1678_cp2.1, L1678_cp2.2)) ∧ ptTest pL1678 (runFrom pL1678 (fmask pL1678) (cmask pL1678) (hmask pL1678) 1370 308 (true, L1678_cp2.1, L1678_cp2.2)) 1678 839 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1678_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1678_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1678_fin) true) L1678_seg1) L1678_seg2) (by decide) rfl L1678_fin ptTest_fst
noncomputable def H1678_cp1 : Nat × Nat := t7val% (fastRun pH1678 1 968 (init pH1678) (init pH1678))
theorem H1678_seg1 : segOK pH1678 1 968 (init pH1678) (init pH1678) H1678_cp1.1 H1678_cp1.2 = true := by
  decide +kernel
noncomputable def H1678_cp2 : Nat × Nat := t7val% (fastRun pH1678 1 1369 (init pH1678) (init pH1678))
theorem H1678_seg2 : segOK pH1678 969 401 H1678_cp1.1 H1678_cp1.2 H1678_cp2.1 H1678_cp2.2 = true := by
  decide +kernel
theorem H1678_fin : (prmOK pH1678 1678 && ptTest pH1678 (runFrom pH1678 (fmask pH1678) (cmask pH1678) (hmask pH1678) 1370 308 (true, H1678_cp2.1, H1678_cp2.2)) 1678 839 true) = true := by
  decide +kernel
theorem H1678_ok : RunOK pH1678 1678 (runFrom pH1678 (fmask pH1678) (cmask pH1678) (hmask pH1678) 1370 308 (true, H1678_cp2.1, H1678_cp2.2)) ∧ ptTest pH1678 (runFrom pH1678 (fmask pH1678) (cmask pH1678) (hmask pH1678) 1370 308 (true, H1678_cp2.1, H1678_cp2.2)) 1678 839 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1678_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1678_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1678_fin) true) H1678_seg1) H1678_seg2) (by decide) rfl H1678_fin ptTest_fst
noncomputable def I1678_cp1 : Nat × Nat := t7val% (fastRun pI1678 1 1186 (init pI1678) (init pI1678))
theorem I1678_seg1 : segOK pI1678 1 1186 (init pI1678) (init pI1678) I1678_cp1.1 I1678_cp1.2 = true := by
  decide +kernel
theorem I1678_fin : (prmOK pI1678 1678 && intTest pI1678 (runFrom pI1678 (fmask pI1678) (cmask pI1678) (hmask pI1678) 1187 491 (true, I1678_cp1.1, I1678_cp1.2)) 1678 21 true) = true := by
  decide +kernel
theorem I1678_ok : RunOK pI1678 1678 (runFrom pI1678 (fmask pI1678) (cmask pI1678) (hmask pI1678) 1187 491 (true, I1678_cp1.1, I1678_cp1.2)) ∧ intTest pI1678 (runFrom pI1678 (fmask pI1678) (cmask pI1678) (hmask pI1678) 1187 491 (true, I1678_cp1.1, I1678_cp1.2)) 1678 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1678_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1678_fin) true) I1678_seg1) (by decide) rfl I1678_fin intTest_fst
theorem link1678 : linkOK pL1678 pH1678 pI1678 = true := by decide +kernel
theorem cvx1678 : ConvexBetweenHumps 1678 :=
  cvx_of L1678_ok H1678_ok I1678_ok link1678 (by decide)
theorem cenlink1678 : cenLinkOK pI1678 1678 = true := by decide +kernel
theorem cen1678 : CenterUniqueMin 1678 ∧ DipHyp 1678 ∧ OnePointHyps 1678 :=
  cen_of L1678_ok H1678_ok I1678_ok link1678 cenlink1678

/-! ### `N = 1679` -/

def pL1679 : Prm := ⟨80, 37, 40, 1681, 11, 18446744073709551616, 113508194876115332, 113508194876115332⟩
def pH1679 : Prm := ⟨80, 37, 40, 1681, 11, 18446744073709551616, 113509294387743108, 113509294387743108⟩
def pI1679 : Prm := ⟨68, 33, 32, 1681, 11, 18446744073709551616, 113508194876115332, 113509294387743108⟩
noncomputable def L1679_cp1 : Nat × Nat := t7val% (fastRun pL1679 1 968 (init pL1679) (init pL1679))
theorem L1679_seg1 : segOK pL1679 1 968 (init pL1679) (init pL1679) L1679_cp1.1 L1679_cp1.2 = true := by
  decide +kernel
noncomputable def L1679_cp2 : Nat × Nat := t7val% (fastRun pL1679 1 1370 (init pL1679) (init pL1679))
theorem L1679_seg2 : segOK pL1679 969 402 L1679_cp1.1 L1679_cp1.2 L1679_cp2.1 L1679_cp2.2 = true := by
  decide +kernel
theorem L1679_fin : (prmOK pL1679 1679 && ptTest pL1679 (runFrom pL1679 (fmask pL1679) (cmask pL1679) (hmask pL1679) 1371 308 (true, L1679_cp2.1, L1679_cp2.2)) 1679 840 false) = true := by
  decide +kernel
theorem L1679_ok : RunOK pL1679 1679 (runFrom pL1679 (fmask pL1679) (cmask pL1679) (hmask pL1679) 1371 308 (true, L1679_cp2.1, L1679_cp2.2)) ∧ ptTest pL1679 (runFrom pL1679 (fmask pL1679) (cmask pL1679) (hmask pL1679) 1371 308 (true, L1679_cp2.1, L1679_cp2.2)) 1679 840 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1679_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1679_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1679_fin) true) L1679_seg1) L1679_seg2) (by decide) rfl L1679_fin ptTest_fst
noncomputable def H1679_cp1 : Nat × Nat := t7val% (fastRun pH1679 1 968 (init pH1679) (init pH1679))
theorem H1679_seg1 : segOK pH1679 1 968 (init pH1679) (init pH1679) H1679_cp1.1 H1679_cp1.2 = true := by
  decide +kernel
noncomputable def H1679_cp2 : Nat × Nat := t7val% (fastRun pH1679 1 1370 (init pH1679) (init pH1679))
theorem H1679_seg2 : segOK pH1679 969 402 H1679_cp1.1 H1679_cp1.2 H1679_cp2.1 H1679_cp2.2 = true := by
  decide +kernel
theorem H1679_fin : (prmOK pH1679 1679 && ptTest pH1679 (runFrom pH1679 (fmask pH1679) (cmask pH1679) (hmask pH1679) 1371 308 (true, H1679_cp2.1, H1679_cp2.2)) 1679 840 true) = true := by
  decide +kernel
theorem H1679_ok : RunOK pH1679 1679 (runFrom pH1679 (fmask pH1679) (cmask pH1679) (hmask pH1679) 1371 308 (true, H1679_cp2.1, H1679_cp2.2)) ∧ ptTest pH1679 (runFrom pH1679 (fmask pH1679) (cmask pH1679) (hmask pH1679) 1371 308 (true, H1679_cp2.1, H1679_cp2.2)) 1679 840 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1679_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1679_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1679_fin) true) H1679_seg1) H1679_seg2) (by decide) rfl H1679_fin ptTest_fst
noncomputable def I1679_cp1 : Nat × Nat := t7val% (fastRun pI1679 1 1186 (init pI1679) (init pI1679))
theorem I1679_seg1 : segOK pI1679 1 1186 (init pI1679) (init pI1679) I1679_cp1.1 I1679_cp1.2 = true := by
  decide +kernel
theorem I1679_fin : (prmOK pI1679 1679 && intTest pI1679 (runFrom pI1679 (fmask pI1679) (cmask pI1679) (hmask pI1679) 1187 492 (true, I1679_cp1.1, I1679_cp1.2)) 1679 21 false) = true := by
  decide +kernel
theorem I1679_ok : RunOK pI1679 1679 (runFrom pI1679 (fmask pI1679) (cmask pI1679) (hmask pI1679) 1187 492 (true, I1679_cp1.1, I1679_cp1.2)) ∧ intTest pI1679 (runFrom pI1679 (fmask pI1679) (cmask pI1679) (hmask pI1679) 1187 492 (true, I1679_cp1.1, I1679_cp1.2)) 1679 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1679_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1679_fin) true) I1679_seg1) (by decide) rfl I1679_fin intTest_fst
theorem link1679 : linkOK pL1679 pH1679 pI1679 = true := by decide +kernel
theorem cvx1679 : ConvexBetweenHumps 1679 :=
  cvx_of L1679_ok H1679_ok I1679_ok link1679 (by decide)

/-! ### `N = 1680` -/

def pL1680 : Prm := ⟨80, 37, 40, 1682, 11, 18446744073709551616, 113452967491574373, 113452967491574373⟩
def pH1680 : Prm := ⟨80, 37, 40, 1682, 11, 18446744073709551616, 113454067003202149, 113454067003202149⟩
def pI1680 : Prm := ⟨68, 33, 32, 1682, 11, 18446744073709551616, 113452967491574373, 113454067003202149⟩
noncomputable def L1680_cp1 : Nat × Nat := t7val% (fastRun pL1680 1 969 (init pL1680) (init pL1680))
theorem L1680_seg1 : segOK pL1680 1 969 (init pL1680) (init pL1680) L1680_cp1.1 L1680_cp1.2 = true := by
  decide +kernel
noncomputable def L1680_cp2 : Nat × Nat := t7val% (fastRun pL1680 1 1371 (init pL1680) (init pL1680))
theorem L1680_seg2 : segOK pL1680 970 402 L1680_cp1.1 L1680_cp1.2 L1680_cp2.1 L1680_cp2.2 = true := by
  decide +kernel
theorem L1680_fin : (prmOK pL1680 1680 && ptTest pL1680 (runFrom pL1680 (fmask pL1680) (cmask pL1680) (hmask pL1680) 1372 308 (true, L1680_cp2.1, L1680_cp2.2)) 1680 840 false) = true := by
  decide +kernel
theorem L1680_ok : RunOK pL1680 1680 (runFrom pL1680 (fmask pL1680) (cmask pL1680) (hmask pL1680) 1372 308 (true, L1680_cp2.1, L1680_cp2.2)) ∧ ptTest pL1680 (runFrom pL1680 (fmask pL1680) (cmask pL1680) (hmask pL1680) 1372 308 (true, L1680_cp2.1, L1680_cp2.2)) 1680 840 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1680_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1680_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1680_fin) true) L1680_seg1) L1680_seg2) (by decide) rfl L1680_fin ptTest_fst
noncomputable def H1680_cp1 : Nat × Nat := t7val% (fastRun pH1680 1 969 (init pH1680) (init pH1680))
theorem H1680_seg1 : segOK pH1680 1 969 (init pH1680) (init pH1680) H1680_cp1.1 H1680_cp1.2 = true := by
  decide +kernel
noncomputable def H1680_cp2 : Nat × Nat := t7val% (fastRun pH1680 1 1371 (init pH1680) (init pH1680))
theorem H1680_seg2 : segOK pH1680 970 402 H1680_cp1.1 H1680_cp1.2 H1680_cp2.1 H1680_cp2.2 = true := by
  decide +kernel
theorem H1680_fin : (prmOK pH1680 1680 && ptTest pH1680 (runFrom pH1680 (fmask pH1680) (cmask pH1680) (hmask pH1680) 1372 308 (true, H1680_cp2.1, H1680_cp2.2)) 1680 840 true) = true := by
  decide +kernel
theorem H1680_ok : RunOK pH1680 1680 (runFrom pH1680 (fmask pH1680) (cmask pH1680) (hmask pH1680) 1372 308 (true, H1680_cp2.1, H1680_cp2.2)) ∧ ptTest pH1680 (runFrom pH1680 (fmask pH1680) (cmask pH1680) (hmask pH1680) 1372 308 (true, H1680_cp2.1, H1680_cp2.2)) 1680 840 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1680_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1680_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1680_fin) true) H1680_seg1) H1680_seg2) (by decide) rfl H1680_fin ptTest_fst
noncomputable def I1680_cp1 : Nat × Nat := t7val% (fastRun pI1680 1 1187 (init pI1680) (init pI1680))
theorem I1680_seg1 : segOK pI1680 1 1187 (init pI1680) (init pI1680) I1680_cp1.1 I1680_cp1.2 = true := by
  decide +kernel
theorem I1680_fin : (prmOK pI1680 1680 && intTest pI1680 (runFrom pI1680 (fmask pI1680) (cmask pI1680) (hmask pI1680) 1188 492 (true, I1680_cp1.1, I1680_cp1.2)) 1680 21 true) = true := by
  decide +kernel
theorem I1680_ok : RunOK pI1680 1680 (runFrom pI1680 (fmask pI1680) (cmask pI1680) (hmask pI1680) 1188 492 (true, I1680_cp1.1, I1680_cp1.2)) ∧ intTest pI1680 (runFrom pI1680 (fmask pI1680) (cmask pI1680) (hmask pI1680) 1188 492 (true, I1680_cp1.1, I1680_cp1.2)) 1680 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1680_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1680_fin) true) I1680_seg1) (by decide) rfl I1680_fin intTest_fst
theorem link1680 : linkOK pL1680 pH1680 pI1680 = true := by decide +kernel
theorem cvx1680 : ConvexBetweenHumps 1680 :=
  cvx_of L1680_ok H1680_ok I1680_ok link1680 (by decide)
theorem cenlink1680 : cenLinkOK pI1680 1680 = true := by decide +kernel
theorem cen1680 : CenterUniqueMin 1680 ∧ DipHyp 1680 ∧ OnePointHyps 1680 :=
  cen_of L1680_ok H1680_ok I1680_ok link1680 cenlink1680

/-! ### The range -/

theorem cvx_1667_1680 {N : ℕ} (h1 : 1667 ≤ N) (h2 : N ≤ 1680) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1673
  · by_cases h4 : N ≤ 1669
    · by_cases h6 : N ≤ 1667
      · obtain rfl : N = 1667 := by omega
        exact cvx1667
      · by_cases h8 : N ≤ 1668
        · obtain rfl : N = 1668 := by omega
          exact cvx1668
        · obtain rfl : N = 1669 := by omega
          exact cvx1669
    · by_cases h6 : N ≤ 1671
      · by_cases h8 : N ≤ 1670
        · obtain rfl : N = 1670 := by omega
          exact cvx1670
        · obtain rfl : N = 1671 := by omega
          exact cvx1671
      · by_cases h8 : N ≤ 1672
        · obtain rfl : N = 1672 := by omega
          exact cvx1672
        · obtain rfl : N = 1673 := by omega
          exact cvx1673
  · by_cases h4 : N ≤ 1676
    · by_cases h6 : N ≤ 1674
      · obtain rfl : N = 1674 := by omega
        exact cvx1674
      · by_cases h8 : N ≤ 1675
        · obtain rfl : N = 1675 := by omega
          exact cvx1675
        · obtain rfl : N = 1676 := by omega
          exact cvx1676
    · by_cases h6 : N ≤ 1678
      · by_cases h8 : N ≤ 1677
        · obtain rfl : N = 1677 := by omega
          exact cvx1677
        · obtain rfl : N = 1678 := by omega
          exact cvx1678
      · by_cases h8 : N ≤ 1679
        · obtain rfl : N = 1679 := by omega
          exact cvx1679
        · obtain rfl : N = 1680 := by omega
          exact cvx1680

theorem cen_1667_1680 {N : ℕ} (h1 : 1667 ≤ N) (h2 : N ≤ 1680) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1672
  · by_cases h4 : N ≤ 1668
    · obtain rfl : N = 1668 := by omega
      exact cen1668
    · by_cases h6 : N ≤ 1670
      · obtain rfl : N = 1670 := by omega
        exact cen1670
      · obtain rfl : N = 1672 := by omega
        exact cen1672
  · by_cases h4 : N ≤ 1676
    · by_cases h6 : N ≤ 1674
      · obtain rfl : N = 1674 := by omega
        exact cen1674
      · obtain rfl : N = 1676 := by omega
        exact cen1676
    · by_cases h6 : N ≤ 1678
      · obtain rfl : N = 1678 := by omega
        exact cen1678
      · obtain rfl : N = 1680 := by omega
        exact cen1680

end Kagey131.PaperD.T7
