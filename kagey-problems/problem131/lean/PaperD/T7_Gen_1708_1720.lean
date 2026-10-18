import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1708, …, 1720` (generated)

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

/-! ### `N = 1708` -/

def pL1708 : Prm := ⟨80, 37, 40, 1710, 11, 18446744073709551616, 111929627275889570, 111929627275889570⟩
def pH1708 : Prm := ⟨80, 37, 40, 1710, 11, 18446744073709551616, 111930726787517346, 111930726787517346⟩
def pI1708 : Prm := ⟨68, 33, 32, 1710, 11, 18446744073709551616, 111929627275889570, 111930726787517346⟩
noncomputable def L1708_cp1 : Nat × Nat := t7val% (fastRun pL1708 1 985 (init pL1708) (init pL1708))
theorem L1708_seg1 : segOK pL1708 1 985 (init pL1708) (init pL1708) L1708_cp1.1 L1708_cp1.2 = true := by
  decide +kernel
noncomputable def L1708_cp2 : Nat × Nat := t7val% (fastRun pL1708 1 1394 (init pL1708) (init pL1708))
theorem L1708_seg2 : segOK pL1708 986 409 L1708_cp1.1 L1708_cp1.2 L1708_cp2.1 L1708_cp2.2 = true := by
  decide +kernel
theorem L1708_fin : (prmOK pL1708 1708 && ptTest pL1708 (runFrom pL1708 (fmask pL1708) (cmask pL1708) (hmask pL1708) 1395 313 (true, L1708_cp2.1, L1708_cp2.2)) 1708 854 false) = true := by
  decide +kernel
theorem L1708_ok : RunOK pL1708 1708 (runFrom pL1708 (fmask pL1708) (cmask pL1708) (hmask pL1708) 1395 313 (true, L1708_cp2.1, L1708_cp2.2)) ∧ ptTest pL1708 (runFrom pL1708 (fmask pL1708) (cmask pL1708) (hmask pL1708) 1395 313 (true, L1708_cp2.1, L1708_cp2.2)) 1708 854 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1708_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1708_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1708_fin) true) L1708_seg1) L1708_seg2) (by decide) rfl L1708_fin ptTest_fst
noncomputable def H1708_cp1 : Nat × Nat := t7val% (fastRun pH1708 1 985 (init pH1708) (init pH1708))
theorem H1708_seg1 : segOK pH1708 1 985 (init pH1708) (init pH1708) H1708_cp1.1 H1708_cp1.2 = true := by
  decide +kernel
noncomputable def H1708_cp2 : Nat × Nat := t7val% (fastRun pH1708 1 1394 (init pH1708) (init pH1708))
theorem H1708_seg2 : segOK pH1708 986 409 H1708_cp1.1 H1708_cp1.2 H1708_cp2.1 H1708_cp2.2 = true := by
  decide +kernel
theorem H1708_fin : (prmOK pH1708 1708 && ptTest pH1708 (runFrom pH1708 (fmask pH1708) (cmask pH1708) (hmask pH1708) 1395 313 (true, H1708_cp2.1, H1708_cp2.2)) 1708 854 true) = true := by
  decide +kernel
theorem H1708_ok : RunOK pH1708 1708 (runFrom pH1708 (fmask pH1708) (cmask pH1708) (hmask pH1708) 1395 313 (true, H1708_cp2.1, H1708_cp2.2)) ∧ ptTest pH1708 (runFrom pH1708 (fmask pH1708) (cmask pH1708) (hmask pH1708) 1395 313 (true, H1708_cp2.1, H1708_cp2.2)) 1708 854 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1708_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1708_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1708_fin) true) H1708_seg1) H1708_seg2) (by decide) rfl H1708_fin ptTest_fst
noncomputable def I1708_cp1 : Nat × Nat := t7val% (fastRun pI1708 1 1207 (init pI1708) (init pI1708))
theorem I1708_seg1 : segOK pI1708 1 1207 (init pI1708) (init pI1708) I1708_cp1.1 I1708_cp1.2 = true := by
  decide +kernel
theorem I1708_fin : (prmOK pI1708 1708 && intTest pI1708 (runFrom pI1708 (fmask pI1708) (cmask pI1708) (hmask pI1708) 1208 500 (true, I1708_cp1.1, I1708_cp1.2)) 1708 21 true) = true := by
  decide +kernel
theorem I1708_ok : RunOK pI1708 1708 (runFrom pI1708 (fmask pI1708) (cmask pI1708) (hmask pI1708) 1208 500 (true, I1708_cp1.1, I1708_cp1.2)) ∧ intTest pI1708 (runFrom pI1708 (fmask pI1708) (cmask pI1708) (hmask pI1708) 1208 500 (true, I1708_cp1.1, I1708_cp1.2)) 1708 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1708_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1708_fin) true) I1708_seg1) (by decide) rfl I1708_fin intTest_fst
theorem link1708 : linkOK pL1708 pH1708 pI1708 = true := by decide +kernel
theorem cvx1708 : ConvexBetweenHumps 1708 :=
  cvx_of L1708_ok H1708_ok I1708_ok link1708 (by decide)
theorem cenlink1708 : cenLinkOK pI1708 1708 = true := by decide +kernel
theorem cen1708 : CenterUniqueMin 1708 ∧ DipHyp 1708 ∧ OnePointHyps 1708 :=
  cen_of L1708_ok H1708_ok I1708_ok link1708 cenlink1708

/-! ### `N = 1709` -/

def pL1709 : Prm := ⟨80, 37, 40, 1711, 11, 18446744073709551616, 111876031840781016, 111876031840781016⟩
def pH1709 : Prm := ⟨80, 37, 40, 1711, 11, 18446744073709551616, 111877131352408792, 111877131352408792⟩
def pI1709 : Prm := ⟨68, 33, 32, 1711, 11, 18446744073709551616, 111876031840781016, 111877131352408792⟩
noncomputable def L1709_cp1 : Nat × Nat := t7val% (fastRun pL1709 1 986 (init pL1709) (init pL1709))
theorem L1709_seg1 : segOK pL1709 1 986 (init pL1709) (init pL1709) L1709_cp1.1 L1709_cp1.2 = true := by
  decide +kernel
noncomputable def L1709_cp2 : Nat × Nat := t7val% (fastRun pL1709 1 1394 (init pL1709) (init pL1709))
theorem L1709_seg2 : segOK pL1709 987 408 L1709_cp1.1 L1709_cp1.2 L1709_cp2.1 L1709_cp2.2 = true := by
  decide +kernel
theorem L1709_fin : (prmOK pL1709 1709 && ptTest pL1709 (runFrom pL1709 (fmask pL1709) (cmask pL1709) (hmask pL1709) 1395 314 (true, L1709_cp2.1, L1709_cp2.2)) 1709 855 false) = true := by
  decide +kernel
theorem L1709_ok : RunOK pL1709 1709 (runFrom pL1709 (fmask pL1709) (cmask pL1709) (hmask pL1709) 1395 314 (true, L1709_cp2.1, L1709_cp2.2)) ∧ ptTest pL1709 (runFrom pL1709 (fmask pL1709) (cmask pL1709) (hmask pL1709) 1395 314 (true, L1709_cp2.1, L1709_cp2.2)) 1709 855 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1709_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1709_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1709_fin) true) L1709_seg1) L1709_seg2) (by decide) rfl L1709_fin ptTest_fst
noncomputable def H1709_cp1 : Nat × Nat := t7val% (fastRun pH1709 1 986 (init pH1709) (init pH1709))
theorem H1709_seg1 : segOK pH1709 1 986 (init pH1709) (init pH1709) H1709_cp1.1 H1709_cp1.2 = true := by
  decide +kernel
noncomputable def H1709_cp2 : Nat × Nat := t7val% (fastRun pH1709 1 1394 (init pH1709) (init pH1709))
theorem H1709_seg2 : segOK pH1709 987 408 H1709_cp1.1 H1709_cp1.2 H1709_cp2.1 H1709_cp2.2 = true := by
  decide +kernel
theorem H1709_fin : (prmOK pH1709 1709 && ptTest pH1709 (runFrom pH1709 (fmask pH1709) (cmask pH1709) (hmask pH1709) 1395 314 (true, H1709_cp2.1, H1709_cp2.2)) 1709 855 true) = true := by
  decide +kernel
theorem H1709_ok : RunOK pH1709 1709 (runFrom pH1709 (fmask pH1709) (cmask pH1709) (hmask pH1709) 1395 314 (true, H1709_cp2.1, H1709_cp2.2)) ∧ ptTest pH1709 (runFrom pH1709 (fmask pH1709) (cmask pH1709) (hmask pH1709) 1395 314 (true, H1709_cp2.1, H1709_cp2.2)) 1709 855 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1709_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1709_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1709_fin) true) H1709_seg1) H1709_seg2) (by decide) rfl H1709_fin ptTest_fst
noncomputable def I1709_cp1 : Nat × Nat := t7val% (fastRun pI1709 1 1207 (init pI1709) (init pI1709))
theorem I1709_seg1 : segOK pI1709 1 1207 (init pI1709) (init pI1709) I1709_cp1.1 I1709_cp1.2 = true := by
  decide +kernel
theorem I1709_fin : (prmOK pI1709 1709 && intTest pI1709 (runFrom pI1709 (fmask pI1709) (cmask pI1709) (hmask pI1709) 1208 501 (true, I1709_cp1.1, I1709_cp1.2)) 1709 21 false) = true := by
  decide +kernel
theorem I1709_ok : RunOK pI1709 1709 (runFrom pI1709 (fmask pI1709) (cmask pI1709) (hmask pI1709) 1208 501 (true, I1709_cp1.1, I1709_cp1.2)) ∧ intTest pI1709 (runFrom pI1709 (fmask pI1709) (cmask pI1709) (hmask pI1709) 1208 501 (true, I1709_cp1.1, I1709_cp1.2)) 1709 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1709_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1709_fin) true) I1709_seg1) (by decide) rfl I1709_fin intTest_fst
theorem link1709 : linkOK pL1709 pH1709 pI1709 = true := by decide +kernel
theorem cvx1709 : ConvexBetweenHumps 1709 :=
  cvx_of L1709_ok H1709_ok I1709_ok link1709 (by decide)

/-! ### `N = 1710` -/

def pL1710 : Prm := ⟨80, 37, 40, 1712, 11, 18446744073709551616, 111822514643645188, 111822514643645188⟩
def pH1710 : Prm := ⟨80, 37, 40, 1712, 11, 18446744073709551616, 111823614155272964, 111823614155272964⟩
def pI1710 : Prm := ⟨68, 33, 32, 1712, 11, 18446744073709551616, 111822514643645188, 111823614155272964⟩
noncomputable def L1710_cp1 : Nat × Nat := t7val% (fastRun pL1710 1 986 (init pL1710) (init pL1710))
theorem L1710_seg1 : segOK pL1710 1 986 (init pL1710) (init pL1710) L1710_cp1.1 L1710_cp1.2 = true := by
  decide +kernel
noncomputable def L1710_cp2 : Nat × Nat := t7val% (fastRun pL1710 1 1395 (init pL1710) (init pL1710))
theorem L1710_seg2 : segOK pL1710 987 409 L1710_cp1.1 L1710_cp1.2 L1710_cp2.1 L1710_cp2.2 = true := by
  decide +kernel
theorem L1710_fin : (prmOK pL1710 1710 && ptTest pL1710 (runFrom pL1710 (fmask pL1710) (cmask pL1710) (hmask pL1710) 1396 314 (true, L1710_cp2.1, L1710_cp2.2)) 1710 855 false) = true := by
  decide +kernel
theorem L1710_ok : RunOK pL1710 1710 (runFrom pL1710 (fmask pL1710) (cmask pL1710) (hmask pL1710) 1396 314 (true, L1710_cp2.1, L1710_cp2.2)) ∧ ptTest pL1710 (runFrom pL1710 (fmask pL1710) (cmask pL1710) (hmask pL1710) 1396 314 (true, L1710_cp2.1, L1710_cp2.2)) 1710 855 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1710_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1710_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1710_fin) true) L1710_seg1) L1710_seg2) (by decide) rfl L1710_fin ptTest_fst
noncomputable def H1710_cp1 : Nat × Nat := t7val% (fastRun pH1710 1 986 (init pH1710) (init pH1710))
theorem H1710_seg1 : segOK pH1710 1 986 (init pH1710) (init pH1710) H1710_cp1.1 H1710_cp1.2 = true := by
  decide +kernel
noncomputable def H1710_cp2 : Nat × Nat := t7val% (fastRun pH1710 1 1395 (init pH1710) (init pH1710))
theorem H1710_seg2 : segOK pH1710 987 409 H1710_cp1.1 H1710_cp1.2 H1710_cp2.1 H1710_cp2.2 = true := by
  decide +kernel
theorem H1710_fin : (prmOK pH1710 1710 && ptTest pH1710 (runFrom pH1710 (fmask pH1710) (cmask pH1710) (hmask pH1710) 1396 314 (true, H1710_cp2.1, H1710_cp2.2)) 1710 855 true) = true := by
  decide +kernel
theorem H1710_ok : RunOK pH1710 1710 (runFrom pH1710 (fmask pH1710) (cmask pH1710) (hmask pH1710) 1396 314 (true, H1710_cp2.1, H1710_cp2.2)) ∧ ptTest pH1710 (runFrom pH1710 (fmask pH1710) (cmask pH1710) (hmask pH1710) 1396 314 (true, H1710_cp2.1, H1710_cp2.2)) 1710 855 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1710_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1710_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1710_fin) true) H1710_seg1) H1710_seg2) (by decide) rfl H1710_fin ptTest_fst
noncomputable def I1710_cp1 : Nat × Nat := t7val% (fastRun pI1710 1 1208 (init pI1710) (init pI1710))
theorem I1710_seg1 : segOK pI1710 1 1208 (init pI1710) (init pI1710) I1710_cp1.1 I1710_cp1.2 = true := by
  decide +kernel
theorem I1710_fin : (prmOK pI1710 1710 && intTest pI1710 (runFrom pI1710 (fmask pI1710) (cmask pI1710) (hmask pI1710) 1209 501 (true, I1710_cp1.1, I1710_cp1.2)) 1710 21 true) = true := by
  decide +kernel
theorem I1710_ok : RunOK pI1710 1710 (runFrom pI1710 (fmask pI1710) (cmask pI1710) (hmask pI1710) 1209 501 (true, I1710_cp1.1, I1710_cp1.2)) ∧ intTest pI1710 (runFrom pI1710 (fmask pI1710) (cmask pI1710) (hmask pI1710) 1209 501 (true, I1710_cp1.1, I1710_cp1.2)) 1710 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1710_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1710_fin) true) I1710_seg1) (by decide) rfl I1710_fin intTest_fst
theorem link1710 : linkOK pL1710 pH1710 pI1710 = true := by decide +kernel
theorem cvx1710 : ConvexBetweenHumps 1710 :=
  cvx_of L1710_ok H1710_ok I1710_ok link1710 (by decide)
theorem cenlink1710 : cenLinkOK pI1710 1710 = true := by decide +kernel
theorem cen1710 : CenterUniqueMin 1710 ∧ DipHyp 1710 ∧ OnePointHyps 1710 :=
  cen_of L1710_ok H1710_ok I1710_ok link1710 cenlink1710

/-! ### `N = 1711` -/

def pL1711 : Prm := ⟨80, 37, 40, 1713, 11, 18446744073709551616, 111769030557713996, 111769030557713996⟩
def pH1711 : Prm := ⟨80, 37, 40, 1713, 11, 18446744073709551616, 111770130069341772, 111770130069341772⟩
def pI1711 : Prm := ⟨68, 33, 32, 1713, 11, 18446744073709551616, 111769030557713996, 111770130069341772⟩
noncomputable def L1711_cp1 : Nat × Nat := t7val% (fastRun pL1711 1 987 (init pL1711) (init pL1711))
theorem L1711_seg1 : segOK pL1711 1 987 (init pL1711) (init pL1711) L1711_cp1.1 L1711_cp1.2 = true := by
  decide +kernel
noncomputable def L1711_cp2 : Nat × Nat := t7val% (fastRun pL1711 1 1396 (init pL1711) (init pL1711))
theorem L1711_seg2 : segOK pL1711 988 409 L1711_cp1.1 L1711_cp1.2 L1711_cp2.1 L1711_cp2.2 = true := by
  decide +kernel
theorem L1711_fin : (prmOK pL1711 1711 && ptTest pL1711 (runFrom pL1711 (fmask pL1711) (cmask pL1711) (hmask pL1711) 1397 314 (true, L1711_cp2.1, L1711_cp2.2)) 1711 856 false) = true := by
  decide +kernel
theorem L1711_ok : RunOK pL1711 1711 (runFrom pL1711 (fmask pL1711) (cmask pL1711) (hmask pL1711) 1397 314 (true, L1711_cp2.1, L1711_cp2.2)) ∧ ptTest pL1711 (runFrom pL1711 (fmask pL1711) (cmask pL1711) (hmask pL1711) 1397 314 (true, L1711_cp2.1, L1711_cp2.2)) 1711 856 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1711_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1711_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1711_fin) true) L1711_seg1) L1711_seg2) (by decide) rfl L1711_fin ptTest_fst
noncomputable def H1711_cp1 : Nat × Nat := t7val% (fastRun pH1711 1 987 (init pH1711) (init pH1711))
theorem H1711_seg1 : segOK pH1711 1 987 (init pH1711) (init pH1711) H1711_cp1.1 H1711_cp1.2 = true := by
  decide +kernel
noncomputable def H1711_cp2 : Nat × Nat := t7val% (fastRun pH1711 1 1396 (init pH1711) (init pH1711))
theorem H1711_seg2 : segOK pH1711 988 409 H1711_cp1.1 H1711_cp1.2 H1711_cp2.1 H1711_cp2.2 = true := by
  decide +kernel
theorem H1711_fin : (prmOK pH1711 1711 && ptTest pH1711 (runFrom pH1711 (fmask pH1711) (cmask pH1711) (hmask pH1711) 1397 314 (true, H1711_cp2.1, H1711_cp2.2)) 1711 856 true) = true := by
  decide +kernel
theorem H1711_ok : RunOK pH1711 1711 (runFrom pH1711 (fmask pH1711) (cmask pH1711) (hmask pH1711) 1397 314 (true, H1711_cp2.1, H1711_cp2.2)) ∧ ptTest pH1711 (runFrom pH1711 (fmask pH1711) (cmask pH1711) (hmask pH1711) 1397 314 (true, H1711_cp2.1, H1711_cp2.2)) 1711 856 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1711_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1711_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1711_fin) true) H1711_seg1) H1711_seg2) (by decide) rfl H1711_fin ptTest_fst
noncomputable def I1711_cp1 : Nat × Nat := t7val% (fastRun pI1711 1 1209 (init pI1711) (init pI1711))
theorem I1711_seg1 : segOK pI1711 1 1209 (init pI1711) (init pI1711) I1711_cp1.1 I1711_cp1.2 = true := by
  decide +kernel
theorem I1711_fin : (prmOK pI1711 1711 && intTest pI1711 (runFrom pI1711 (fmask pI1711) (cmask pI1711) (hmask pI1711) 1210 501 (true, I1711_cp1.1, I1711_cp1.2)) 1711 21 false) = true := by
  decide +kernel
theorem I1711_ok : RunOK pI1711 1711 (runFrom pI1711 (fmask pI1711) (cmask pI1711) (hmask pI1711) 1210 501 (true, I1711_cp1.1, I1711_cp1.2)) ∧ intTest pI1711 (runFrom pI1711 (fmask pI1711) (cmask pI1711) (hmask pI1711) 1210 501 (true, I1711_cp1.1, I1711_cp1.2)) 1711 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1711_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1711_fin) true) I1711_seg1) (by decide) rfl I1711_fin intTest_fst
theorem link1711 : linkOK pL1711 pH1711 pI1711 = true := by decide +kernel
theorem cvx1711 : ConvexBetweenHumps 1711 :=
  cvx_of L1711_ok H1711_ok I1711_ok link1711 (by decide)

/-! ### `N = 1712` -/

def pL1712 : Prm := ⟨80, 37, 40, 1714, 11, 18446744073709551616, 111715624450781689, 111715624450781689⟩
def pH1712 : Prm := ⟨80, 37, 40, 1714, 11, 18446744073709551616, 111716723962409465, 111716723962409465⟩
def pI1712 : Prm := ⟨68, 33, 32, 1714, 11, 18446744073709551616, 111715624450781689, 111716723962409465⟩
noncomputable def L1712_cp1 : Nat × Nat := t7val% (fastRun pL1712 1 987 (init pL1712) (init pL1712))
theorem L1712_seg1 : segOK pL1712 1 987 (init pL1712) (init pL1712) L1712_cp1.1 L1712_cp1.2 = true := by
  decide +kernel
noncomputable def L1712_cp2 : Nat × Nat := t7val% (fastRun pL1712 1 1397 (init pL1712) (init pL1712))
theorem L1712_seg2 : segOK pL1712 988 410 L1712_cp1.1 L1712_cp1.2 L1712_cp2.1 L1712_cp2.2 = true := by
  decide +kernel
theorem L1712_fin : (prmOK pL1712 1712 && ptTest pL1712 (runFrom pL1712 (fmask pL1712) (cmask pL1712) (hmask pL1712) 1398 314 (true, L1712_cp2.1, L1712_cp2.2)) 1712 856 false) = true := by
  decide +kernel
theorem L1712_ok : RunOK pL1712 1712 (runFrom pL1712 (fmask pL1712) (cmask pL1712) (hmask pL1712) 1398 314 (true, L1712_cp2.1, L1712_cp2.2)) ∧ ptTest pL1712 (runFrom pL1712 (fmask pL1712) (cmask pL1712) (hmask pL1712) 1398 314 (true, L1712_cp2.1, L1712_cp2.2)) 1712 856 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1712_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1712_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1712_fin) true) L1712_seg1) L1712_seg2) (by decide) rfl L1712_fin ptTest_fst
noncomputable def H1712_cp1 : Nat × Nat := t7val% (fastRun pH1712 1 987 (init pH1712) (init pH1712))
theorem H1712_seg1 : segOK pH1712 1 987 (init pH1712) (init pH1712) H1712_cp1.1 H1712_cp1.2 = true := by
  decide +kernel
noncomputable def H1712_cp2 : Nat × Nat := t7val% (fastRun pH1712 1 1397 (init pH1712) (init pH1712))
theorem H1712_seg2 : segOK pH1712 988 410 H1712_cp1.1 H1712_cp1.2 H1712_cp2.1 H1712_cp2.2 = true := by
  decide +kernel
theorem H1712_fin : (prmOK pH1712 1712 && ptTest pH1712 (runFrom pH1712 (fmask pH1712) (cmask pH1712) (hmask pH1712) 1398 314 (true, H1712_cp2.1, H1712_cp2.2)) 1712 856 true) = true := by
  decide +kernel
theorem H1712_ok : RunOK pH1712 1712 (runFrom pH1712 (fmask pH1712) (cmask pH1712) (hmask pH1712) 1398 314 (true, H1712_cp2.1, H1712_cp2.2)) ∧ ptTest pH1712 (runFrom pH1712 (fmask pH1712) (cmask pH1712) (hmask pH1712) 1398 314 (true, H1712_cp2.1, H1712_cp2.2)) 1712 856 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1712_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1712_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1712_fin) true) H1712_seg1) H1712_seg2) (by decide) rfl H1712_fin ptTest_fst
noncomputable def I1712_cp1 : Nat × Nat := t7val% (fastRun pI1712 1 1210 (init pI1712) (init pI1712))
theorem I1712_seg1 : segOK pI1712 1 1210 (init pI1712) (init pI1712) I1712_cp1.1 I1712_cp1.2 = true := by
  decide +kernel
theorem I1712_fin : (prmOK pI1712 1712 && intTest pI1712 (runFrom pI1712 (fmask pI1712) (cmask pI1712) (hmask pI1712) 1211 501 (true, I1712_cp1.1, I1712_cp1.2)) 1712 21 true) = true := by
  decide +kernel
theorem I1712_ok : RunOK pI1712 1712 (runFrom pI1712 (fmask pI1712) (cmask pI1712) (hmask pI1712) 1211 501 (true, I1712_cp1.1, I1712_cp1.2)) ∧ intTest pI1712 (runFrom pI1712 (fmask pI1712) (cmask pI1712) (hmask pI1712) 1211 501 (true, I1712_cp1.1, I1712_cp1.2)) 1712 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1712_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1712_fin) true) I1712_seg1) (by decide) rfl I1712_fin intTest_fst
theorem link1712 : linkOK pL1712 pH1712 pI1712 = true := by decide +kernel
theorem cvx1712 : ConvexBetweenHumps 1712 :=
  cvx_of L1712_ok H1712_ok I1712_ok link1712 (by decide)
theorem cenlink1712 : cenLinkOK pI1712 1712 = true := by decide +kernel
theorem cen1712 : CenterUniqueMin 1712 ∧ DipHyp 1712 ∧ OnePointHyps 1712 :=
  cen_of L1712_ok H1712_ok I1712_ok link1712 cenlink1712

/-! ### `N = 1713` -/

def pL1713 : Prm := ⟨80, 37, 40, 1715, 11, 18446744073709551616, 111662251356566852, 111662251356566852⟩
def pH1713 : Prm := ⟨80, 37, 40, 1715, 11, 18446744073709551616, 111663350868194628, 111663350868194628⟩
def pI1713 : Prm := ⟨69, 33, 33, 1715, 11, 18446744073709551616, 111662251356566852, 111663350868194628⟩
noncomputable def L1713_cp1 : Nat × Nat := t7val% (fastRun pL1713 1 988 (init pL1713) (init pL1713))
theorem L1713_seg1 : segOK pL1713 1 988 (init pL1713) (init pL1713) L1713_cp1.1 L1713_cp1.2 = true := by
  decide +kernel
noncomputable def L1713_cp2 : Nat × Nat := t7val% (fastRun pL1713 1 1398 (init pL1713) (init pL1713))
theorem L1713_seg2 : segOK pL1713 989 410 L1713_cp1.1 L1713_cp1.2 L1713_cp2.1 L1713_cp2.2 = true := by
  decide +kernel
theorem L1713_fin : (prmOK pL1713 1713 && ptTest pL1713 (runFrom pL1713 (fmask pL1713) (cmask pL1713) (hmask pL1713) 1399 314 (true, L1713_cp2.1, L1713_cp2.2)) 1713 857 false) = true := by
  decide +kernel
theorem L1713_ok : RunOK pL1713 1713 (runFrom pL1713 (fmask pL1713) (cmask pL1713) (hmask pL1713) 1399 314 (true, L1713_cp2.1, L1713_cp2.2)) ∧ ptTest pL1713 (runFrom pL1713 (fmask pL1713) (cmask pL1713) (hmask pL1713) 1399 314 (true, L1713_cp2.1, L1713_cp2.2)) 1713 857 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1713_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1713_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1713_fin) true) L1713_seg1) L1713_seg2) (by decide) rfl L1713_fin ptTest_fst
noncomputable def H1713_cp1 : Nat × Nat := t7val% (fastRun pH1713 1 988 (init pH1713) (init pH1713))
theorem H1713_seg1 : segOK pH1713 1 988 (init pH1713) (init pH1713) H1713_cp1.1 H1713_cp1.2 = true := by
  decide +kernel
noncomputable def H1713_cp2 : Nat × Nat := t7val% (fastRun pH1713 1 1398 (init pH1713) (init pH1713))
theorem H1713_seg2 : segOK pH1713 989 410 H1713_cp1.1 H1713_cp1.2 H1713_cp2.1 H1713_cp2.2 = true := by
  decide +kernel
theorem H1713_fin : (prmOK pH1713 1713 && ptTest pH1713 (runFrom pH1713 (fmask pH1713) (cmask pH1713) (hmask pH1713) 1399 314 (true, H1713_cp2.1, H1713_cp2.2)) 1713 857 true) = true := by
  decide +kernel
theorem H1713_ok : RunOK pH1713 1713 (runFrom pH1713 (fmask pH1713) (cmask pH1713) (hmask pH1713) 1399 314 (true, H1713_cp2.1, H1713_cp2.2)) ∧ ptTest pH1713 (runFrom pH1713 (fmask pH1713) (cmask pH1713) (hmask pH1713) 1399 314 (true, H1713_cp2.1, H1713_cp2.2)) 1713 857 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1713_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1713_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1713_fin) true) H1713_seg1) H1713_seg2) (by decide) rfl H1713_fin ptTest_fst
noncomputable def I1713_cp1 : Nat × Nat := t7val% (fastRun pI1713 1 1210 (init pI1713) (init pI1713))
theorem I1713_seg1 : segOK pI1713 1 1210 (init pI1713) (init pI1713) I1713_cp1.1 I1713_cp1.2 = true := by
  decide +kernel
theorem I1713_fin : (prmOK pI1713 1713 && intTest pI1713 (runFrom pI1713 (fmask pI1713) (cmask pI1713) (hmask pI1713) 1211 502 (true, I1713_cp1.1, I1713_cp1.2)) 1713 21 false) = true := by
  decide +kernel
theorem I1713_ok : RunOK pI1713 1713 (runFrom pI1713 (fmask pI1713) (cmask pI1713) (hmask pI1713) 1211 502 (true, I1713_cp1.1, I1713_cp1.2)) ∧ intTest pI1713 (runFrom pI1713 (fmask pI1713) (cmask pI1713) (hmask pI1713) 1211 502 (true, I1713_cp1.1, I1713_cp1.2)) 1713 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1713_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1713_fin) true) I1713_seg1) (by decide) rfl I1713_fin intTest_fst
theorem link1713 : linkOK pL1713 pH1713 pI1713 = true := by decide +kernel
theorem cvx1713 : ConvexBetweenHumps 1713 :=
  cvx_of L1713_ok H1713_ok I1713_ok link1713 (by decide)

/-! ### `N = 1714` -/

def pL1714 : Prm := ⟨80, 37, 40, 1716, 11, 18446744073709551616, 111608955983520759, 111608955983520759⟩
def pH1714 : Prm := ⟨80, 37, 40, 1716, 11, 18446744073709551616, 111610055495148535, 111610055495148535⟩
def pI1714 : Prm := ⟨68, 33, 32, 1716, 11, 18446744073709551616, 111608955983520759, 111610055495148535⟩
noncomputable def L1714_cp1 : Nat × Nat := t7val% (fastRun pL1714 1 989 (init pL1714) (init pL1714))
theorem L1714_seg1 : segOK pL1714 1 989 (init pL1714) (init pL1714) L1714_cp1.1 L1714_cp1.2 = true := by
  decide +kernel
noncomputable def L1714_cp2 : Nat × Nat := t7val% (fastRun pL1714 1 1398 (init pL1714) (init pL1714))
theorem L1714_seg2 : segOK pL1714 990 409 L1714_cp1.1 L1714_cp1.2 L1714_cp2.1 L1714_cp2.2 = true := by
  decide +kernel
theorem L1714_fin : (prmOK pL1714 1714 && ptTest pL1714 (runFrom pL1714 (fmask pL1714) (cmask pL1714) (hmask pL1714) 1399 315 (true, L1714_cp2.1, L1714_cp2.2)) 1714 857 false) = true := by
  decide +kernel
theorem L1714_ok : RunOK pL1714 1714 (runFrom pL1714 (fmask pL1714) (cmask pL1714) (hmask pL1714) 1399 315 (true, L1714_cp2.1, L1714_cp2.2)) ∧ ptTest pL1714 (runFrom pL1714 (fmask pL1714) (cmask pL1714) (hmask pL1714) 1399 315 (true, L1714_cp2.1, L1714_cp2.2)) 1714 857 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1714_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1714_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1714_fin) true) L1714_seg1) L1714_seg2) (by decide) rfl L1714_fin ptTest_fst
noncomputable def H1714_cp1 : Nat × Nat := t7val% (fastRun pH1714 1 989 (init pH1714) (init pH1714))
theorem H1714_seg1 : segOK pH1714 1 989 (init pH1714) (init pH1714) H1714_cp1.1 H1714_cp1.2 = true := by
  decide +kernel
noncomputable def H1714_cp2 : Nat × Nat := t7val% (fastRun pH1714 1 1398 (init pH1714) (init pH1714))
theorem H1714_seg2 : segOK pH1714 990 409 H1714_cp1.1 H1714_cp1.2 H1714_cp2.1 H1714_cp2.2 = true := by
  decide +kernel
theorem H1714_fin : (prmOK pH1714 1714 && ptTest pH1714 (runFrom pH1714 (fmask pH1714) (cmask pH1714) (hmask pH1714) 1399 315 (true, H1714_cp2.1, H1714_cp2.2)) 1714 857 true) = true := by
  decide +kernel
theorem H1714_ok : RunOK pH1714 1714 (runFrom pH1714 (fmask pH1714) (cmask pH1714) (hmask pH1714) 1399 315 (true, H1714_cp2.1, H1714_cp2.2)) ∧ ptTest pH1714 (runFrom pH1714 (fmask pH1714) (cmask pH1714) (hmask pH1714) 1399 315 (true, H1714_cp2.1, H1714_cp2.2)) 1714 857 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1714_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1714_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1714_fin) true) H1714_seg1) H1714_seg2) (by decide) rfl H1714_fin ptTest_fst
noncomputable def I1714_cp1 : Nat × Nat := t7val% (fastRun pI1714 1 1211 (init pI1714) (init pI1714))
theorem I1714_seg1 : segOK pI1714 1 1211 (init pI1714) (init pI1714) I1714_cp1.1 I1714_cp1.2 = true := by
  decide +kernel
theorem I1714_fin : (prmOK pI1714 1714 && intTest pI1714 (runFrom pI1714 (fmask pI1714) (cmask pI1714) (hmask pI1714) 1212 502 (true, I1714_cp1.1, I1714_cp1.2)) 1714 21 true) = true := by
  decide +kernel
theorem I1714_ok : RunOK pI1714 1714 (runFrom pI1714 (fmask pI1714) (cmask pI1714) (hmask pI1714) 1212 502 (true, I1714_cp1.1, I1714_cp1.2)) ∧ intTest pI1714 (runFrom pI1714 (fmask pI1714) (cmask pI1714) (hmask pI1714) 1212 502 (true, I1714_cp1.1, I1714_cp1.2)) 1714 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1714_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1714_fin) true) I1714_seg1) (by decide) rfl I1714_fin intTest_fst
theorem link1714 : linkOK pL1714 pH1714 pI1714 = true := by decide +kernel
theorem cvx1714 : ConvexBetweenHumps 1714 :=
  cvx_of L1714_ok H1714_ok I1714_ok link1714 (by decide)
theorem cenlink1714 : cenLinkOK pI1714 1714 = true := by decide +kernel
theorem cen1714 : CenterUniqueMin 1714 ∧ DipHyp 1714 ∧ OnePointHyps 1714 :=
  cen_of L1714_ok H1714_ok I1714_ok link1714 cenlink1714

/-! ### `N = 1715` -/

def pL1715 : Prm := ⟨80, 37, 40, 1717, 11, 18446744073709551616, 111555693525129243, 111555693525129243⟩
def pH1715 : Prm := ⟨80, 37, 40, 1717, 11, 18446744073709551616, 111556793036757019, 111556793036757019⟩
def pI1715 : Prm := ⟨68, 33, 32, 1717, 11, 18446744073709551616, 111555693525129243, 111556793036757019⟩
noncomputable def L1715_cp1 : Nat × Nat := t7val% (fastRun pL1715 1 989 (init pL1715) (init pL1715))
theorem L1715_seg1 : segOK pL1715 1 989 (init pL1715) (init pL1715) L1715_cp1.1 L1715_cp1.2 = true := by
  decide +kernel
noncomputable def L1715_cp2 : Nat × Nat := t7val% (fastRun pL1715 1 1399 (init pL1715) (init pL1715))
theorem L1715_seg2 : segOK pL1715 990 410 L1715_cp1.1 L1715_cp1.2 L1715_cp2.1 L1715_cp2.2 = true := by
  decide +kernel
theorem L1715_fin : (prmOK pL1715 1715 && ptTest pL1715 (runFrom pL1715 (fmask pL1715) (cmask pL1715) (hmask pL1715) 1400 315 (true, L1715_cp2.1, L1715_cp2.2)) 1715 858 false) = true := by
  decide +kernel
theorem L1715_ok : RunOK pL1715 1715 (runFrom pL1715 (fmask pL1715) (cmask pL1715) (hmask pL1715) 1400 315 (true, L1715_cp2.1, L1715_cp2.2)) ∧ ptTest pL1715 (runFrom pL1715 (fmask pL1715) (cmask pL1715) (hmask pL1715) 1400 315 (true, L1715_cp2.1, L1715_cp2.2)) 1715 858 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1715_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1715_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1715_fin) true) L1715_seg1) L1715_seg2) (by decide) rfl L1715_fin ptTest_fst
noncomputable def H1715_cp1 : Nat × Nat := t7val% (fastRun pH1715 1 989 (init pH1715) (init pH1715))
theorem H1715_seg1 : segOK pH1715 1 989 (init pH1715) (init pH1715) H1715_cp1.1 H1715_cp1.2 = true := by
  decide +kernel
noncomputable def H1715_cp2 : Nat × Nat := t7val% (fastRun pH1715 1 1399 (init pH1715) (init pH1715))
theorem H1715_seg2 : segOK pH1715 990 410 H1715_cp1.1 H1715_cp1.2 H1715_cp2.1 H1715_cp2.2 = true := by
  decide +kernel
theorem H1715_fin : (prmOK pH1715 1715 && ptTest pH1715 (runFrom pH1715 (fmask pH1715) (cmask pH1715) (hmask pH1715) 1400 315 (true, H1715_cp2.1, H1715_cp2.2)) 1715 858 true) = true := by
  decide +kernel
theorem H1715_ok : RunOK pH1715 1715 (runFrom pH1715 (fmask pH1715) (cmask pH1715) (hmask pH1715) 1400 315 (true, H1715_cp2.1, H1715_cp2.2)) ∧ ptTest pH1715 (runFrom pH1715 (fmask pH1715) (cmask pH1715) (hmask pH1715) 1400 315 (true, H1715_cp2.1, H1715_cp2.2)) 1715 858 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1715_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1715_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1715_fin) true) H1715_seg1) H1715_seg2) (by decide) rfl H1715_fin ptTest_fst
noncomputable def I1715_cp1 : Nat × Nat := t7val% (fastRun pI1715 1 1212 (init pI1715) (init pI1715))
theorem I1715_seg1 : segOK pI1715 1 1212 (init pI1715) (init pI1715) I1715_cp1.1 I1715_cp1.2 = true := by
  decide +kernel
theorem I1715_fin : (prmOK pI1715 1715 && intTest pI1715 (runFrom pI1715 (fmask pI1715) (cmask pI1715) (hmask pI1715) 1213 502 (true, I1715_cp1.1, I1715_cp1.2)) 1715 21 false) = true := by
  decide +kernel
theorem I1715_ok : RunOK pI1715 1715 (runFrom pI1715 (fmask pI1715) (cmask pI1715) (hmask pI1715) 1213 502 (true, I1715_cp1.1, I1715_cp1.2)) ∧ intTest pI1715 (runFrom pI1715 (fmask pI1715) (cmask pI1715) (hmask pI1715) 1213 502 (true, I1715_cp1.1, I1715_cp1.2)) 1715 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1715_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1715_fin) true) I1715_seg1) (by decide) rfl I1715_fin intTest_fst
theorem link1715 : linkOK pL1715 pH1715 pI1715 = true := by decide +kernel
theorem cvx1715 : ConvexBetweenHumps 1715 :=
  cvx_of L1715_ok H1715_ok I1715_ok link1715 (by decide)

/-! ### `N = 1716` -/

def pL1716 : Prm := ⟨80, 37, 40, 1718, 11, 18446744073709551616, 111502508531220028, 111502508531220028⟩
def pH1716 : Prm := ⟨80, 37, 40, 1718, 11, 18446744073709551616, 111503608042847804, 111503608042847804⟩
def pI1716 : Prm := ⟨68, 33, 32, 1718, 11, 18446744073709551616, 111502508531220028, 111503608042847804⟩
noncomputable def L1716_cp1 : Nat × Nat := t7val% (fastRun pL1716 1 990 (init pL1716) (init pL1716))
theorem L1716_seg1 : segOK pL1716 1 990 (init pL1716) (init pL1716) L1716_cp1.1 L1716_cp1.2 = true := by
  decide +kernel
noncomputable def L1716_cp2 : Nat × Nat := t7val% (fastRun pL1716 1 1400 (init pL1716) (init pL1716))
theorem L1716_seg2 : segOK pL1716 991 410 L1716_cp1.1 L1716_cp1.2 L1716_cp2.1 L1716_cp2.2 = true := by
  decide +kernel
theorem L1716_fin : (prmOK pL1716 1716 && ptTest pL1716 (runFrom pL1716 (fmask pL1716) (cmask pL1716) (hmask pL1716) 1401 315 (true, L1716_cp2.1, L1716_cp2.2)) 1716 858 false) = true := by
  decide +kernel
theorem L1716_ok : RunOK pL1716 1716 (runFrom pL1716 (fmask pL1716) (cmask pL1716) (hmask pL1716) 1401 315 (true, L1716_cp2.1, L1716_cp2.2)) ∧ ptTest pL1716 (runFrom pL1716 (fmask pL1716) (cmask pL1716) (hmask pL1716) 1401 315 (true, L1716_cp2.1, L1716_cp2.2)) 1716 858 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1716_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1716_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1716_fin) true) L1716_seg1) L1716_seg2) (by decide) rfl L1716_fin ptTest_fst
noncomputable def H1716_cp1 : Nat × Nat := t7val% (fastRun pH1716 1 990 (init pH1716) (init pH1716))
theorem H1716_seg1 : segOK pH1716 1 990 (init pH1716) (init pH1716) H1716_cp1.1 H1716_cp1.2 = true := by
  decide +kernel
noncomputable def H1716_cp2 : Nat × Nat := t7val% (fastRun pH1716 1 1400 (init pH1716) (init pH1716))
theorem H1716_seg2 : segOK pH1716 991 410 H1716_cp1.1 H1716_cp1.2 H1716_cp2.1 H1716_cp2.2 = true := by
  decide +kernel
theorem H1716_fin : (prmOK pH1716 1716 && ptTest pH1716 (runFrom pH1716 (fmask pH1716) (cmask pH1716) (hmask pH1716) 1401 315 (true, H1716_cp2.1, H1716_cp2.2)) 1716 858 true) = true := by
  decide +kernel
theorem H1716_ok : RunOK pH1716 1716 (runFrom pH1716 (fmask pH1716) (cmask pH1716) (hmask pH1716) 1401 315 (true, H1716_cp2.1, H1716_cp2.2)) ∧ ptTest pH1716 (runFrom pH1716 (fmask pH1716) (cmask pH1716) (hmask pH1716) 1401 315 (true, H1716_cp2.1, H1716_cp2.2)) 1716 858 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1716_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1716_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1716_fin) true) H1716_seg1) H1716_seg2) (by decide) rfl H1716_fin ptTest_fst
noncomputable def I1716_cp1 : Nat × Nat := t7val% (fastRun pI1716 1 1212 (init pI1716) (init pI1716))
theorem I1716_seg1 : segOK pI1716 1 1212 (init pI1716) (init pI1716) I1716_cp1.1 I1716_cp1.2 = true := by
  decide +kernel
theorem I1716_fin : (prmOK pI1716 1716 && intTest pI1716 (runFrom pI1716 (fmask pI1716) (cmask pI1716) (hmask pI1716) 1213 503 (true, I1716_cp1.1, I1716_cp1.2)) 1716 21 true) = true := by
  decide +kernel
theorem I1716_ok : RunOK pI1716 1716 (runFrom pI1716 (fmask pI1716) (cmask pI1716) (hmask pI1716) 1213 503 (true, I1716_cp1.1, I1716_cp1.2)) ∧ intTest pI1716 (runFrom pI1716 (fmask pI1716) (cmask pI1716) (hmask pI1716) 1213 503 (true, I1716_cp1.1, I1716_cp1.2)) 1716 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1716_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1716_fin) true) I1716_seg1) (by decide) rfl I1716_fin intTest_fst
theorem link1716 : linkOK pL1716 pH1716 pI1716 = true := by decide +kernel
theorem cvx1716 : ConvexBetweenHumps 1716 :=
  cvx_of L1716_ok H1716_ok I1716_ok link1716 (by decide)
theorem cenlink1716 : cenLinkOK pI1716 1716 = true := by decide +kernel
theorem cen1716 : CenterUniqueMin 1716 ∧ DipHyp 1716 ∧ OnePointHyps 1716 :=
  cen_of L1716_ok H1716_ok I1716_ok link1716 cenlink1716

/-! ### `N = 1717` -/

def pL1717 : Prm := ⟨80, 37, 40, 1719, 11, 18446744073709551616, 111449356354289880, 111449356354289880⟩
def pH1717 : Prm := ⟨80, 37, 40, 1719, 11, 18446744073709551616, 111450455865917656, 111450455865917656⟩
def pI1717 : Prm := ⟨68, 33, 32, 1719, 11, 18446744073709551616, 111449356354289880, 111450455865917656⟩
noncomputable def L1717_cp1 : Nat × Nat := t7val% (fastRun pL1717 1 990 (init pL1717) (init pL1717))
theorem L1717_seg1 : segOK pL1717 1 990 (init pL1717) (init pL1717) L1717_cp1.1 L1717_cp1.2 = true := by
  decide +kernel
noncomputable def L1717_cp2 : Nat × Nat := t7val% (fastRun pL1717 1 1401 (init pL1717) (init pL1717))
theorem L1717_seg2 : segOK pL1717 991 411 L1717_cp1.1 L1717_cp1.2 L1717_cp2.1 L1717_cp2.2 = true := by
  decide +kernel
theorem L1717_fin : (prmOK pL1717 1717 && ptTest pL1717 (runFrom pL1717 (fmask pL1717) (cmask pL1717) (hmask pL1717) 1402 315 (true, L1717_cp2.1, L1717_cp2.2)) 1717 859 false) = true := by
  decide +kernel
theorem L1717_ok : RunOK pL1717 1717 (runFrom pL1717 (fmask pL1717) (cmask pL1717) (hmask pL1717) 1402 315 (true, L1717_cp2.1, L1717_cp2.2)) ∧ ptTest pL1717 (runFrom pL1717 (fmask pL1717) (cmask pL1717) (hmask pL1717) 1402 315 (true, L1717_cp2.1, L1717_cp2.2)) 1717 859 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1717_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1717_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1717_fin) true) L1717_seg1) L1717_seg2) (by decide) rfl L1717_fin ptTest_fst
noncomputable def H1717_cp1 : Nat × Nat := t7val% (fastRun pH1717 1 990 (init pH1717) (init pH1717))
theorem H1717_seg1 : segOK pH1717 1 990 (init pH1717) (init pH1717) H1717_cp1.1 H1717_cp1.2 = true := by
  decide +kernel
noncomputable def H1717_cp2 : Nat × Nat := t7val% (fastRun pH1717 1 1401 (init pH1717) (init pH1717))
theorem H1717_seg2 : segOK pH1717 991 411 H1717_cp1.1 H1717_cp1.2 H1717_cp2.1 H1717_cp2.2 = true := by
  decide +kernel
theorem H1717_fin : (prmOK pH1717 1717 && ptTest pH1717 (runFrom pH1717 (fmask pH1717) (cmask pH1717) (hmask pH1717) 1402 315 (true, H1717_cp2.1, H1717_cp2.2)) 1717 859 true) = true := by
  decide +kernel
theorem H1717_ok : RunOK pH1717 1717 (runFrom pH1717 (fmask pH1717) (cmask pH1717) (hmask pH1717) 1402 315 (true, H1717_cp2.1, H1717_cp2.2)) ∧ ptTest pH1717 (runFrom pH1717 (fmask pH1717) (cmask pH1717) (hmask pH1717) 1402 315 (true, H1717_cp2.1, H1717_cp2.2)) 1717 859 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1717_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1717_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1717_fin) true) H1717_seg1) H1717_seg2) (by decide) rfl H1717_fin ptTest_fst
noncomputable def I1717_cp1 : Nat × Nat := t7val% (fastRun pI1717 1 1213 (init pI1717) (init pI1717))
theorem I1717_seg1 : segOK pI1717 1 1213 (init pI1717) (init pI1717) I1717_cp1.1 I1717_cp1.2 = true := by
  decide +kernel
theorem I1717_fin : (prmOK pI1717 1717 && intTest pI1717 (runFrom pI1717 (fmask pI1717) (cmask pI1717) (hmask pI1717) 1214 503 (true, I1717_cp1.1, I1717_cp1.2)) 1717 21 false) = true := by
  decide +kernel
theorem I1717_ok : RunOK pI1717 1717 (runFrom pI1717 (fmask pI1717) (cmask pI1717) (hmask pI1717) 1214 503 (true, I1717_cp1.1, I1717_cp1.2)) ∧ intTest pI1717 (runFrom pI1717 (fmask pI1717) (cmask pI1717) (hmask pI1717) 1214 503 (true, I1717_cp1.1, I1717_cp1.2)) 1717 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1717_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1717_fin) true) I1717_seg1) (by decide) rfl I1717_fin intTest_fst
theorem link1717 : linkOK pL1717 pH1717 pI1717 = true := by decide +kernel
theorem cvx1717 : ConvexBetweenHumps 1717 :=
  cvx_of L1717_ok H1717_ok I1717_ok link1717 (by decide)

/-! ### `N = 1718` -/

def pL1718 : Prm := ⟨80, 37, 40, 1720, 11, 18446744073709551616, 111396281386299286, 111396281386299286⟩
def pH1718 : Prm := ⟨80, 37, 40, 1720, 11, 18446744073709551616, 111397380897927062, 111397380897927062⟩
def pI1718 : Prm := ⟨68, 33, 32, 1720, 11, 18446744073709551616, 111396281386299286, 111397380897927062⟩
noncomputable def L1718_cp1 : Nat × Nat := t7val% (fastRun pL1718 1 991 (init pL1718) (init pL1718))
theorem L1718_seg1 : segOK pL1718 1 991 (init pL1718) (init pL1718) L1718_cp1.1 L1718_cp1.2 = true := by
  decide +kernel
noncomputable def L1718_cp2 : Nat × Nat := t7val% (fastRun pL1718 1 1402 (init pL1718) (init pL1718))
theorem L1718_seg2 : segOK pL1718 992 411 L1718_cp1.1 L1718_cp1.2 L1718_cp2.1 L1718_cp2.2 = true := by
  decide +kernel
theorem L1718_fin : (prmOK pL1718 1718 && ptTest pL1718 (runFrom pL1718 (fmask pL1718) (cmask pL1718) (hmask pL1718) 1403 315 (true, L1718_cp2.1, L1718_cp2.2)) 1718 859 false) = true := by
  decide +kernel
theorem L1718_ok : RunOK pL1718 1718 (runFrom pL1718 (fmask pL1718) (cmask pL1718) (hmask pL1718) 1403 315 (true, L1718_cp2.1, L1718_cp2.2)) ∧ ptTest pL1718 (runFrom pL1718 (fmask pL1718) (cmask pL1718) (hmask pL1718) 1403 315 (true, L1718_cp2.1, L1718_cp2.2)) 1718 859 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1718_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1718_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1718_fin) true) L1718_seg1) L1718_seg2) (by decide) rfl L1718_fin ptTest_fst
noncomputable def H1718_cp1 : Nat × Nat := t7val% (fastRun pH1718 1 991 (init pH1718) (init pH1718))
theorem H1718_seg1 : segOK pH1718 1 991 (init pH1718) (init pH1718) H1718_cp1.1 H1718_cp1.2 = true := by
  decide +kernel
noncomputable def H1718_cp2 : Nat × Nat := t7val% (fastRun pH1718 1 1402 (init pH1718) (init pH1718))
theorem H1718_seg2 : segOK pH1718 992 411 H1718_cp1.1 H1718_cp1.2 H1718_cp2.1 H1718_cp2.2 = true := by
  decide +kernel
theorem H1718_fin : (prmOK pH1718 1718 && ptTest pH1718 (runFrom pH1718 (fmask pH1718) (cmask pH1718) (hmask pH1718) 1403 315 (true, H1718_cp2.1, H1718_cp2.2)) 1718 859 true) = true := by
  decide +kernel
theorem H1718_ok : RunOK pH1718 1718 (runFrom pH1718 (fmask pH1718) (cmask pH1718) (hmask pH1718) 1403 315 (true, H1718_cp2.1, H1718_cp2.2)) ∧ ptTest pH1718 (runFrom pH1718 (fmask pH1718) (cmask pH1718) (hmask pH1718) 1403 315 (true, H1718_cp2.1, H1718_cp2.2)) 1718 859 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1718_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1718_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1718_fin) true) H1718_seg1) H1718_seg2) (by decide) rfl H1718_fin ptTest_fst
noncomputable def I1718_cp1 : Nat × Nat := t7val% (fastRun pI1718 1 1214 (init pI1718) (init pI1718))
theorem I1718_seg1 : segOK pI1718 1 1214 (init pI1718) (init pI1718) I1718_cp1.1 I1718_cp1.2 = true := by
  decide +kernel
theorem I1718_fin : (prmOK pI1718 1718 && intTest pI1718 (runFrom pI1718 (fmask pI1718) (cmask pI1718) (hmask pI1718) 1215 503 (true, I1718_cp1.1, I1718_cp1.2)) 1718 21 true) = true := by
  decide +kernel
theorem I1718_ok : RunOK pI1718 1718 (runFrom pI1718 (fmask pI1718) (cmask pI1718) (hmask pI1718) 1215 503 (true, I1718_cp1.1, I1718_cp1.2)) ∧ intTest pI1718 (runFrom pI1718 (fmask pI1718) (cmask pI1718) (hmask pI1718) 1215 503 (true, I1718_cp1.1, I1718_cp1.2)) 1718 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1718_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1718_fin) true) I1718_seg1) (by decide) rfl I1718_fin intTest_fst
theorem link1718 : linkOK pL1718 pH1718 pI1718 = true := by decide +kernel
theorem cvx1718 : ConvexBetweenHumps 1718 :=
  cvx_of L1718_ok H1718_ok I1718_ok link1718 (by decide)
theorem cenlink1718 : cenLinkOK pI1718 1718 = true := by decide +kernel
theorem cen1718 : CenterUniqueMin 1718 ∧ DipHyp 1718 ∧ OnePointHyps 1718 :=
  cen_of L1718_ok H1718_ok I1718_ok link1718 cenlink1718

/-! ### `N = 1719` -/

def pL1719 : Prm := ⟨80, 37, 40, 1721, 11, 18446744073709551616, 111343239138018079, 111343239138018079⟩
def pH1719 : Prm := ⟨80, 37, 40, 1721, 11, 18446744073709551616, 111344338649645855, 111344338649645855⟩
def pI1719 : Prm := ⟨69, 33, 33, 1721, 11, 18446744073709551616, 111343239138018079, 111344338649645855⟩
noncomputable def L1719_cp1 : Nat × Nat := t7val% (fastRun pL1719 1 991 (init pL1719) (init pL1719))
theorem L1719_seg1 : segOK pL1719 1 991 (init pL1719) (init pL1719) L1719_cp1.1 L1719_cp1.2 = true := by
  decide +kernel
noncomputable def L1719_cp2 : Nat × Nat := t7val% (fastRun pL1719 1 1403 (init pL1719) (init pL1719))
theorem L1719_seg2 : segOK pL1719 992 412 L1719_cp1.1 L1719_cp1.2 L1719_cp2.1 L1719_cp2.2 = true := by
  decide +kernel
theorem L1719_fin : (prmOK pL1719 1719 && ptTest pL1719 (runFrom pL1719 (fmask pL1719) (cmask pL1719) (hmask pL1719) 1404 315 (true, L1719_cp2.1, L1719_cp2.2)) 1719 860 false) = true := by
  decide +kernel
theorem L1719_ok : RunOK pL1719 1719 (runFrom pL1719 (fmask pL1719) (cmask pL1719) (hmask pL1719) 1404 315 (true, L1719_cp2.1, L1719_cp2.2)) ∧ ptTest pL1719 (runFrom pL1719 (fmask pL1719) (cmask pL1719) (hmask pL1719) 1404 315 (true, L1719_cp2.1, L1719_cp2.2)) 1719 860 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1719_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1719_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1719_fin) true) L1719_seg1) L1719_seg2) (by decide) rfl L1719_fin ptTest_fst
noncomputable def H1719_cp1 : Nat × Nat := t7val% (fastRun pH1719 1 991 (init pH1719) (init pH1719))
theorem H1719_seg1 : segOK pH1719 1 991 (init pH1719) (init pH1719) H1719_cp1.1 H1719_cp1.2 = true := by
  decide +kernel
noncomputable def H1719_cp2 : Nat × Nat := t7val% (fastRun pH1719 1 1403 (init pH1719) (init pH1719))
theorem H1719_seg2 : segOK pH1719 992 412 H1719_cp1.1 H1719_cp1.2 H1719_cp2.1 H1719_cp2.2 = true := by
  decide +kernel
theorem H1719_fin : (prmOK pH1719 1719 && ptTest pH1719 (runFrom pH1719 (fmask pH1719) (cmask pH1719) (hmask pH1719) 1404 315 (true, H1719_cp2.1, H1719_cp2.2)) 1719 860 true) = true := by
  decide +kernel
theorem H1719_ok : RunOK pH1719 1719 (runFrom pH1719 (fmask pH1719) (cmask pH1719) (hmask pH1719) 1404 315 (true, H1719_cp2.1, H1719_cp2.2)) ∧ ptTest pH1719 (runFrom pH1719 (fmask pH1719) (cmask pH1719) (hmask pH1719) 1404 315 (true, H1719_cp2.1, H1719_cp2.2)) 1719 860 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1719_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1719_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1719_fin) true) H1719_seg1) H1719_seg2) (by decide) rfl H1719_fin ptTest_fst
noncomputable def I1719_cp1 : Nat × Nat := t7val% (fastRun pI1719 1 1215 (init pI1719) (init pI1719))
theorem I1719_seg1 : segOK pI1719 1 1215 (init pI1719) (init pI1719) I1719_cp1.1 I1719_cp1.2 = true := by
  decide +kernel
theorem I1719_fin : (prmOK pI1719 1719 && intTest pI1719 (runFrom pI1719 (fmask pI1719) (cmask pI1719) (hmask pI1719) 1216 503 (true, I1719_cp1.1, I1719_cp1.2)) 1719 21 false) = true := by
  decide +kernel
theorem I1719_ok : RunOK pI1719 1719 (runFrom pI1719 (fmask pI1719) (cmask pI1719) (hmask pI1719) 1216 503 (true, I1719_cp1.1, I1719_cp1.2)) ∧ intTest pI1719 (runFrom pI1719 (fmask pI1719) (cmask pI1719) (hmask pI1719) 1216 503 (true, I1719_cp1.1, I1719_cp1.2)) 1719 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1719_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1719_fin) true) I1719_seg1) (by decide) rfl I1719_fin intTest_fst
theorem link1719 : linkOK pL1719 pH1719 pI1719 = true := by decide +kernel
theorem cvx1719 : ConvexBetweenHumps 1719 :=
  cvx_of L1719_ok H1719_ok I1719_ok link1719 (by decide)

/-! ### `N = 1720` -/

def pL1720 : Prm := ⟨80, 37, 40, 1722, 11, 18446744073709551616, 111290273844277379, 111290273844277379⟩
def pH1720 : Prm := ⟨80, 37, 40, 1722, 11, 18446744073709551616, 111291373355905155, 111291373355905155⟩
def pI1720 : Prm := ⟨68, 33, 32, 1722, 11, 18446744073709551616, 111290273844277379, 111291373355905155⟩
noncomputable def L1720_cp1 : Nat × Nat := t7val% (fastRun pL1720 1 992 (init pL1720) (init pL1720))
theorem L1720_seg1 : segOK pL1720 1 992 (init pL1720) (init pL1720) L1720_cp1.1 L1720_cp1.2 = true := by
  decide +kernel
noncomputable def L1720_cp2 : Nat × Nat := t7val% (fastRun pL1720 1 1403 (init pL1720) (init pL1720))
theorem L1720_seg2 : segOK pL1720 993 411 L1720_cp1.1 L1720_cp1.2 L1720_cp2.1 L1720_cp2.2 = true := by
  decide +kernel
theorem L1720_fin : (prmOK pL1720 1720 && ptTest pL1720 (runFrom pL1720 (fmask pL1720) (cmask pL1720) (hmask pL1720) 1404 316 (true, L1720_cp2.1, L1720_cp2.2)) 1720 860 false) = true := by
  decide +kernel
theorem L1720_ok : RunOK pL1720 1720 (runFrom pL1720 (fmask pL1720) (cmask pL1720) (hmask pL1720) 1404 316 (true, L1720_cp2.1, L1720_cp2.2)) ∧ ptTest pL1720 (runFrom pL1720 (fmask pL1720) (cmask pL1720) (hmask pL1720) 1404 316 (true, L1720_cp2.1, L1720_cp2.2)) 1720 860 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1720_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1720_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1720_fin) true) L1720_seg1) L1720_seg2) (by decide) rfl L1720_fin ptTest_fst
noncomputable def H1720_cp1 : Nat × Nat := t7val% (fastRun pH1720 1 992 (init pH1720) (init pH1720))
theorem H1720_seg1 : segOK pH1720 1 992 (init pH1720) (init pH1720) H1720_cp1.1 H1720_cp1.2 = true := by
  decide +kernel
noncomputable def H1720_cp2 : Nat × Nat := t7val% (fastRun pH1720 1 1403 (init pH1720) (init pH1720))
theorem H1720_seg2 : segOK pH1720 993 411 H1720_cp1.1 H1720_cp1.2 H1720_cp2.1 H1720_cp2.2 = true := by
  decide +kernel
theorem H1720_fin : (prmOK pH1720 1720 && ptTest pH1720 (runFrom pH1720 (fmask pH1720) (cmask pH1720) (hmask pH1720) 1404 316 (true, H1720_cp2.1, H1720_cp2.2)) 1720 860 true) = true := by
  decide +kernel
theorem H1720_ok : RunOK pH1720 1720 (runFrom pH1720 (fmask pH1720) (cmask pH1720) (hmask pH1720) 1404 316 (true, H1720_cp2.1, H1720_cp2.2)) ∧ ptTest pH1720 (runFrom pH1720 (fmask pH1720) (cmask pH1720) (hmask pH1720) 1404 316 (true, H1720_cp2.1, H1720_cp2.2)) 1720 860 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1720_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1720_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1720_fin) true) H1720_seg1) H1720_seg2) (by decide) rfl H1720_fin ptTest_fst
noncomputable def I1720_cp1 : Nat × Nat := t7val% (fastRun pI1720 1 1215 (init pI1720) (init pI1720))
theorem I1720_seg1 : segOK pI1720 1 1215 (init pI1720) (init pI1720) I1720_cp1.1 I1720_cp1.2 = true := by
  decide +kernel
theorem I1720_fin : (prmOK pI1720 1720 && intTest pI1720 (runFrom pI1720 (fmask pI1720) (cmask pI1720) (hmask pI1720) 1216 504 (true, I1720_cp1.1, I1720_cp1.2)) 1720 21 true) = true := by
  decide +kernel
theorem I1720_ok : RunOK pI1720 1720 (runFrom pI1720 (fmask pI1720) (cmask pI1720) (hmask pI1720) 1216 504 (true, I1720_cp1.1, I1720_cp1.2)) ∧ intTest pI1720 (runFrom pI1720 (fmask pI1720) (cmask pI1720) (hmask pI1720) 1216 504 (true, I1720_cp1.1, I1720_cp1.2)) 1720 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1720_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1720_fin) true) I1720_seg1) (by decide) rfl I1720_fin intTest_fst
theorem link1720 : linkOK pL1720 pH1720 pI1720 = true := by decide +kernel
theorem cvx1720 : ConvexBetweenHumps 1720 :=
  cvx_of L1720_ok H1720_ok I1720_ok link1720 (by decide)
theorem cenlink1720 : cenLinkOK pI1720 1720 = true := by decide +kernel
theorem cen1720 : CenterUniqueMin 1720 ∧ DipHyp 1720 ∧ OnePointHyps 1720 :=
  cen_of L1720_ok H1720_ok I1720_ok link1720 cenlink1720

/-! ### The range -/

theorem cvx_1708_1720 {N : ℕ} (h1 : 1708 ≤ N) (h2 : N ≤ 1720) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1713
  · by_cases h4 : N ≤ 1710
    · by_cases h6 : N ≤ 1708
      · obtain rfl : N = 1708 := by omega
        exact cvx1708
      · by_cases h8 : N ≤ 1709
        · obtain rfl : N = 1709 := by omega
          exact cvx1709
        · obtain rfl : N = 1710 := by omega
          exact cvx1710
    · by_cases h6 : N ≤ 1711
      · obtain rfl : N = 1711 := by omega
        exact cvx1711
      · by_cases h8 : N ≤ 1712
        · obtain rfl : N = 1712 := by omega
          exact cvx1712
        · obtain rfl : N = 1713 := by omega
          exact cvx1713
  · by_cases h4 : N ≤ 1716
    · by_cases h6 : N ≤ 1714
      · obtain rfl : N = 1714 := by omega
        exact cvx1714
      · by_cases h8 : N ≤ 1715
        · obtain rfl : N = 1715 := by omega
          exact cvx1715
        · obtain rfl : N = 1716 := by omega
          exact cvx1716
    · by_cases h6 : N ≤ 1718
      · by_cases h8 : N ≤ 1717
        · obtain rfl : N = 1717 := by omega
          exact cvx1717
        · obtain rfl : N = 1718 := by omega
          exact cvx1718
      · by_cases h8 : N ≤ 1719
        · obtain rfl : N = 1719 := by omega
          exact cvx1719
        · obtain rfl : N = 1720 := by omega
          exact cvx1720

theorem cen_1708_1720 {N : ℕ} (h1 : 1708 ≤ N) (h2 : N ≤ 1720) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1712
  · by_cases h4 : N ≤ 1708
    · obtain rfl : N = 1708 := by omega
      exact cen1708
    · by_cases h6 : N ≤ 1710
      · obtain rfl : N = 1710 := by omega
        exact cen1710
      · obtain rfl : N = 1712 := by omega
        exact cen1712
  · by_cases h4 : N ≤ 1716
    · by_cases h6 : N ≤ 1714
      · obtain rfl : N = 1714 := by omega
        exact cen1714
      · obtain rfl : N = 1716 := by omega
        exact cen1716
    · by_cases h6 : N ≤ 1718
      · obtain rfl : N = 1718 := by omega
        exact cen1718
      · obtain rfl : N = 1720 := by omega
        exact cen1720

end Kagey131.PaperD.T7
