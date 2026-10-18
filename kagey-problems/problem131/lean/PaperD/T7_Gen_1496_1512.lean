import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1496, …, 1512` (generated)

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

/-! ### `N = 1496` -/

def pL1496 : Prm := ⟨80, 38, 39, 1498, 11, 18446744073709551616, 124710359509595977, 124710359509595977⟩
def pH1496 : Prm := ⟨80, 38, 39, 1498, 11, 18446744073709551616, 124711459021223753, 124711459021223753⟩
def pI1496 : Prm := ⟨66, 33, 30, 1498, 11, 18446744073709551616, 124710359509595977, 124711459021223753⟩
noncomputable def L1496_cp1 : Nat × Nat := t7val% (fastRun pL1496 1 1057 (init pL1496) (init pL1496))
theorem L1496_seg1 : segOK pL1496 1 1057 (init pL1496) (init pL1496) L1496_cp1.1 L1496_cp1.2 = true := by
  decide +kernel
theorem L1496_fin : (prmOK pL1496 1496 && ptTest pL1496 (runFrom pL1496 (fmask pL1496) (cmask pL1496) (hmask pL1496) 1058 438 (true, L1496_cp1.1, L1496_cp1.2)) 1496 748 false) = true := by
  decide +kernel
theorem L1496_ok : RunOK pL1496 1496 (runFrom pL1496 (fmask pL1496) (cmask pL1496) (hmask pL1496) 1058 438 (true, L1496_cp1.1, L1496_cp1.2)) ∧ ptTest pL1496 (runFrom pL1496 (fmask pL1496) (cmask pL1496) (hmask pL1496) 1058 438 (true, L1496_cp1.1, L1496_cp1.2)) 1496 748 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1496_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1496_fin) true) L1496_seg1) (by decide) rfl L1496_fin ptTest_fst
noncomputable def H1496_cp1 : Nat × Nat := t7val% (fastRun pH1496 1 1057 (init pH1496) (init pH1496))
theorem H1496_seg1 : segOK pH1496 1 1057 (init pH1496) (init pH1496) H1496_cp1.1 H1496_cp1.2 = true := by
  decide +kernel
theorem H1496_fin : (prmOK pH1496 1496 && ptTest pH1496 (runFrom pH1496 (fmask pH1496) (cmask pH1496) (hmask pH1496) 1058 438 (true, H1496_cp1.1, H1496_cp1.2)) 1496 748 true) = true := by
  decide +kernel
theorem H1496_ok : RunOK pH1496 1496 (runFrom pH1496 (fmask pH1496) (cmask pH1496) (hmask pH1496) 1058 438 (true, H1496_cp1.1, H1496_cp1.2)) ∧ ptTest pH1496 (runFrom pH1496 (fmask pH1496) (cmask pH1496) (hmask pH1496) 1058 438 (true, H1496_cp1.1, H1496_cp1.2)) 1496 748 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1496_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1496_fin) true) H1496_seg1) (by decide) rfl H1496_fin ptTest_fst
noncomputable def I1496_cp1 : Nat × Nat := t7val% (fastRun pI1496 1 1057 (init pI1496) (init pI1496))
theorem I1496_seg1 : segOK pI1496 1 1057 (init pI1496) (init pI1496) I1496_cp1.1 I1496_cp1.2 = true := by
  decide +kernel
theorem I1496_fin : (prmOK pI1496 1496 && intTest pI1496 (runFrom pI1496 (fmask pI1496) (cmask pI1496) (hmask pI1496) 1058 438 (true, I1496_cp1.1, I1496_cp1.2)) 1496 20 true) = true := by
  decide +kernel
theorem I1496_ok : RunOK pI1496 1496 (runFrom pI1496 (fmask pI1496) (cmask pI1496) (hmask pI1496) 1058 438 (true, I1496_cp1.1, I1496_cp1.2)) ∧ intTest pI1496 (runFrom pI1496 (fmask pI1496) (cmask pI1496) (hmask pI1496) 1058 438 (true, I1496_cp1.1, I1496_cp1.2)) 1496 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1496_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1496_fin) true) I1496_seg1) (by decide) rfl I1496_fin intTest_fst
theorem link1496 : linkOK pL1496 pH1496 pI1496 = true := by decide +kernel
theorem cvx1496 : ConvexBetweenHumps 1496 :=
  cvx_of L1496_ok H1496_ok I1496_ok link1496 (by decide)
theorem cenlink1496 : cenLinkOK pI1496 1496 = true := by decide +kernel
theorem cen1496 : CenterUniqueMin 1496 ∧ DipHyp 1496 ∧ OnePointHyps 1496 :=
  cen_of L1496_ok H1496_ok I1496_ok link1496 cenlink1496

/-! ### `N = 1497` -/

def pL1497 : Prm := ⟨80, 38, 39, 1499, 11, 18446744073709551616, 124642561270996725, 124642561270996725⟩
def pH1497 : Prm := ⟨80, 38, 39, 1499, 11, 18446744073709551616, 124643660782624501, 124643660782624501⟩
def pI1497 : Prm := ⟨66, 33, 30, 1499, 11, 18446744073709551616, 124642561270996725, 124643660782624501⟩
noncomputable def L1497_cp1 : Nat × Nat := t7val% (fastRun pL1497 1 1058 (init pL1497) (init pL1497))
theorem L1497_seg1 : segOK pL1497 1 1058 (init pL1497) (init pL1497) L1497_cp1.1 L1497_cp1.2 = true := by
  decide +kernel
theorem L1497_fin : (prmOK pL1497 1497 && ptTest pL1497 (runFrom pL1497 (fmask pL1497) (cmask pL1497) (hmask pL1497) 1059 438 (true, L1497_cp1.1, L1497_cp1.2)) 1497 749 false) = true := by
  decide +kernel
theorem L1497_ok : RunOK pL1497 1497 (runFrom pL1497 (fmask pL1497) (cmask pL1497) (hmask pL1497) 1059 438 (true, L1497_cp1.1, L1497_cp1.2)) ∧ ptTest pL1497 (runFrom pL1497 (fmask pL1497) (cmask pL1497) (hmask pL1497) 1059 438 (true, L1497_cp1.1, L1497_cp1.2)) 1497 749 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1497_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1497_fin) true) L1497_seg1) (by decide) rfl L1497_fin ptTest_fst
noncomputable def H1497_cp1 : Nat × Nat := t7val% (fastRun pH1497 1 1058 (init pH1497) (init pH1497))
theorem H1497_seg1 : segOK pH1497 1 1058 (init pH1497) (init pH1497) H1497_cp1.1 H1497_cp1.2 = true := by
  decide +kernel
theorem H1497_fin : (prmOK pH1497 1497 && ptTest pH1497 (runFrom pH1497 (fmask pH1497) (cmask pH1497) (hmask pH1497) 1059 438 (true, H1497_cp1.1, H1497_cp1.2)) 1497 749 true) = true := by
  decide +kernel
theorem H1497_ok : RunOK pH1497 1497 (runFrom pH1497 (fmask pH1497) (cmask pH1497) (hmask pH1497) 1059 438 (true, H1497_cp1.1, H1497_cp1.2)) ∧ ptTest pH1497 (runFrom pH1497 (fmask pH1497) (cmask pH1497) (hmask pH1497) 1059 438 (true, H1497_cp1.1, H1497_cp1.2)) 1497 749 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1497_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1497_fin) true) H1497_seg1) (by decide) rfl H1497_fin ptTest_fst
noncomputable def I1497_cp1 : Nat × Nat := t7val% (fastRun pI1497 1 1058 (init pI1497) (init pI1497))
theorem I1497_seg1 : segOK pI1497 1 1058 (init pI1497) (init pI1497) I1497_cp1.1 I1497_cp1.2 = true := by
  decide +kernel
theorem I1497_fin : (prmOK pI1497 1497 && intTest pI1497 (runFrom pI1497 (fmask pI1497) (cmask pI1497) (hmask pI1497) 1059 438 (true, I1497_cp1.1, I1497_cp1.2)) 1497 20 false) = true := by
  decide +kernel
theorem I1497_ok : RunOK pI1497 1497 (runFrom pI1497 (fmask pI1497) (cmask pI1497) (hmask pI1497) 1059 438 (true, I1497_cp1.1, I1497_cp1.2)) ∧ intTest pI1497 (runFrom pI1497 (fmask pI1497) (cmask pI1497) (hmask pI1497) 1059 438 (true, I1497_cp1.1, I1497_cp1.2)) 1497 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1497_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1497_fin) true) I1497_seg1) (by decide) rfl I1497_fin intTest_fst
theorem link1497 : linkOK pL1497 pH1497 pI1497 = true := by decide +kernel
theorem cvx1497 : ConvexBetweenHumps 1497 :=
  cvx_of L1497_ok H1497_ok I1497_ok link1497 (by decide)

/-! ### `N = 1498` -/

def pL1498 : Prm := ⟨80, 38, 39, 1500, 11, 18446744073709551616, 124574876901178714, 124574876901178714⟩
def pH1498 : Prm := ⟨80, 38, 39, 1500, 11, 18446744073709551616, 124575976412806490, 124575976412806490⟩
def pI1498 : Prm := ⟨66, 33, 30, 1500, 11, 18446744073709551616, 124574876901178714, 124575976412806490⟩
noncomputable def L1498_cp1 : Nat × Nat := t7val% (fastRun pL1498 1 1058 (init pL1498) (init pL1498))
theorem L1498_seg1 : segOK pL1498 1 1058 (init pL1498) (init pL1498) L1498_cp1.1 L1498_cp1.2 = true := by
  decide +kernel
theorem L1498_fin : (prmOK pL1498 1498 && ptTest pL1498 (runFrom pL1498 (fmask pL1498) (cmask pL1498) (hmask pL1498) 1059 439 (true, L1498_cp1.1, L1498_cp1.2)) 1498 749 false) = true := by
  decide +kernel
theorem L1498_ok : RunOK pL1498 1498 (runFrom pL1498 (fmask pL1498) (cmask pL1498) (hmask pL1498) 1059 439 (true, L1498_cp1.1, L1498_cp1.2)) ∧ ptTest pL1498 (runFrom pL1498 (fmask pL1498) (cmask pL1498) (hmask pL1498) 1059 439 (true, L1498_cp1.1, L1498_cp1.2)) 1498 749 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1498_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1498_fin) true) L1498_seg1) (by decide) rfl L1498_fin ptTest_fst
noncomputable def H1498_cp1 : Nat × Nat := t7val% (fastRun pH1498 1 1058 (init pH1498) (init pH1498))
theorem H1498_seg1 : segOK pH1498 1 1058 (init pH1498) (init pH1498) H1498_cp1.1 H1498_cp1.2 = true := by
  decide +kernel
theorem H1498_fin : (prmOK pH1498 1498 && ptTest pH1498 (runFrom pH1498 (fmask pH1498) (cmask pH1498) (hmask pH1498) 1059 439 (true, H1498_cp1.1, H1498_cp1.2)) 1498 749 true) = true := by
  decide +kernel
theorem H1498_ok : RunOK pH1498 1498 (runFrom pH1498 (fmask pH1498) (cmask pH1498) (hmask pH1498) 1059 439 (true, H1498_cp1.1, H1498_cp1.2)) ∧ ptTest pH1498 (runFrom pH1498 (fmask pH1498) (cmask pH1498) (hmask pH1498) 1059 439 (true, H1498_cp1.1, H1498_cp1.2)) 1498 749 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1498_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1498_fin) true) H1498_seg1) (by decide) rfl H1498_fin ptTest_fst
noncomputable def I1498_cp1 : Nat × Nat := t7val% (fastRun pI1498 1 1058 (init pI1498) (init pI1498))
theorem I1498_seg1 : segOK pI1498 1 1058 (init pI1498) (init pI1498) I1498_cp1.1 I1498_cp1.2 = true := by
  decide +kernel
theorem I1498_fin : (prmOK pI1498 1498 && intTest pI1498 (runFrom pI1498 (fmask pI1498) (cmask pI1498) (hmask pI1498) 1059 439 (true, I1498_cp1.1, I1498_cp1.2)) 1498 20 true) = true := by
  decide +kernel
theorem I1498_ok : RunOK pI1498 1498 (runFrom pI1498 (fmask pI1498) (cmask pI1498) (hmask pI1498) 1059 439 (true, I1498_cp1.1, I1498_cp1.2)) ∧ intTest pI1498 (runFrom pI1498 (fmask pI1498) (cmask pI1498) (hmask pI1498) 1059 439 (true, I1498_cp1.1, I1498_cp1.2)) 1498 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1498_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1498_fin) true) I1498_seg1) (by decide) rfl I1498_fin intTest_fst
theorem link1498 : linkOK pL1498 pH1498 pI1498 = true := by decide +kernel
theorem cvx1498 : ConvexBetweenHumps 1498 :=
  cvx_of L1498_ok H1498_ok I1498_ok link1498 (by decide)
theorem cenlink1498 : cenLinkOK pI1498 1498 = true := by decide +kernel
theorem cen1498 : CenterUniqueMin 1498 ∧ DipHyp 1498 ∧ OnePointHyps 1498 :=
  cen_of L1498_ok H1498_ok I1498_ok link1498 cenlink1498

/-! ### `N = 1499` -/

def pL1499 : Prm := ⟨80, 38, 39, 1501, 11, 18446744073709551616, 124507238830603845, 124507238830603845⟩
def pH1499 : Prm := ⟨80, 38, 39, 1501, 11, 18446744073709551616, 124508338342231621, 124508338342231621⟩
def pI1499 : Prm := ⟨66, 33, 30, 1501, 11, 18446744073709551616, 124507238830603845, 124508338342231621⟩
noncomputable def L1499_cp1 : Nat × Nat := t7val% (fastRun pL1499 1 1059 (init pL1499) (init pL1499))
theorem L1499_seg1 : segOK pL1499 1 1059 (init pL1499) (init pL1499) L1499_cp1.1 L1499_cp1.2 = true := by
  decide +kernel
theorem L1499_fin : (prmOK pL1499 1499 && ptTest pL1499 (runFrom pL1499 (fmask pL1499) (cmask pL1499) (hmask pL1499) 1060 439 (true, L1499_cp1.1, L1499_cp1.2)) 1499 750 false) = true := by
  decide +kernel
theorem L1499_ok : RunOK pL1499 1499 (runFrom pL1499 (fmask pL1499) (cmask pL1499) (hmask pL1499) 1060 439 (true, L1499_cp1.1, L1499_cp1.2)) ∧ ptTest pL1499 (runFrom pL1499 (fmask pL1499) (cmask pL1499) (hmask pL1499) 1060 439 (true, L1499_cp1.1, L1499_cp1.2)) 1499 750 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1499_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1499_fin) true) L1499_seg1) (by decide) rfl L1499_fin ptTest_fst
noncomputable def H1499_cp1 : Nat × Nat := t7val% (fastRun pH1499 1 1059 (init pH1499) (init pH1499))
theorem H1499_seg1 : segOK pH1499 1 1059 (init pH1499) (init pH1499) H1499_cp1.1 H1499_cp1.2 = true := by
  decide +kernel
theorem H1499_fin : (prmOK pH1499 1499 && ptTest pH1499 (runFrom pH1499 (fmask pH1499) (cmask pH1499) (hmask pH1499) 1060 439 (true, H1499_cp1.1, H1499_cp1.2)) 1499 750 true) = true := by
  decide +kernel
theorem H1499_ok : RunOK pH1499 1499 (runFrom pH1499 (fmask pH1499) (cmask pH1499) (hmask pH1499) 1060 439 (true, H1499_cp1.1, H1499_cp1.2)) ∧ ptTest pH1499 (runFrom pH1499 (fmask pH1499) (cmask pH1499) (hmask pH1499) 1060 439 (true, H1499_cp1.1, H1499_cp1.2)) 1499 750 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1499_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1499_fin) true) H1499_seg1) (by decide) rfl H1499_fin ptTest_fst
noncomputable def I1499_cp1 : Nat × Nat := t7val% (fastRun pI1499 1 1059 (init pI1499) (init pI1499))
theorem I1499_seg1 : segOK pI1499 1 1059 (init pI1499) (init pI1499) I1499_cp1.1 I1499_cp1.2 = true := by
  decide +kernel
theorem I1499_fin : (prmOK pI1499 1499 && intTest pI1499 (runFrom pI1499 (fmask pI1499) (cmask pI1499) (hmask pI1499) 1060 439 (true, I1499_cp1.1, I1499_cp1.2)) 1499 20 false) = true := by
  decide +kernel
theorem I1499_ok : RunOK pI1499 1499 (runFrom pI1499 (fmask pI1499) (cmask pI1499) (hmask pI1499) 1060 439 (true, I1499_cp1.1, I1499_cp1.2)) ∧ intTest pI1499 (runFrom pI1499 (fmask pI1499) (cmask pI1499) (hmask pI1499) 1060 439 (true, I1499_cp1.1, I1499_cp1.2)) 1499 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1499_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1499_fin) true) I1499_seg1) (by decide) rfl I1499_fin intTest_fst
theorem link1499 : linkOK pL1499 pH1499 pI1499 = true := by decide +kernel
theorem cvx1499 : ConvexBetweenHumps 1499 :=
  cvx_of L1499_ok H1499_ok I1499_ok link1499 (by decide)

/-! ### `N = 1500` -/

def pL1500 : Prm := ⟨80, 38, 39, 1502, 11, 18446744073709551616, 124439714199037975, 124439714199037975⟩
def pH1500 : Prm := ⟨80, 38, 39, 1502, 11, 18446744073709551616, 124440813710665751, 124440813710665751⟩
def pI1500 : Prm := ⟨66, 33, 30, 1502, 11, 18446744073709551616, 124439714199037975, 124440813710665751⟩
noncomputable def L1500_cp1 : Nat × Nat := t7val% (fastRun pL1500 1 1060 (init pL1500) (init pL1500))
theorem L1500_seg1 : segOK pL1500 1 1060 (init pL1500) (init pL1500) L1500_cp1.1 L1500_cp1.2 = true := by
  decide +kernel
theorem L1500_fin : (prmOK pL1500 1500 && ptTest pL1500 (runFrom pL1500 (fmask pL1500) (cmask pL1500) (hmask pL1500) 1061 439 (true, L1500_cp1.1, L1500_cp1.2)) 1500 750 false) = true := by
  decide +kernel
theorem L1500_ok : RunOK pL1500 1500 (runFrom pL1500 (fmask pL1500) (cmask pL1500) (hmask pL1500) 1061 439 (true, L1500_cp1.1, L1500_cp1.2)) ∧ ptTest pL1500 (runFrom pL1500 (fmask pL1500) (cmask pL1500) (hmask pL1500) 1061 439 (true, L1500_cp1.1, L1500_cp1.2)) 1500 750 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1500_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1500_fin) true) L1500_seg1) (by decide) rfl L1500_fin ptTest_fst
noncomputable def H1500_cp1 : Nat × Nat := t7val% (fastRun pH1500 1 1060 (init pH1500) (init pH1500))
theorem H1500_seg1 : segOK pH1500 1 1060 (init pH1500) (init pH1500) H1500_cp1.1 H1500_cp1.2 = true := by
  decide +kernel
theorem H1500_fin : (prmOK pH1500 1500 && ptTest pH1500 (runFrom pH1500 (fmask pH1500) (cmask pH1500) (hmask pH1500) 1061 439 (true, H1500_cp1.1, H1500_cp1.2)) 1500 750 true) = true := by
  decide +kernel
theorem H1500_ok : RunOK pH1500 1500 (runFrom pH1500 (fmask pH1500) (cmask pH1500) (hmask pH1500) 1061 439 (true, H1500_cp1.1, H1500_cp1.2)) ∧ ptTest pH1500 (runFrom pH1500 (fmask pH1500) (cmask pH1500) (hmask pH1500) 1061 439 (true, H1500_cp1.1, H1500_cp1.2)) 1500 750 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1500_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1500_fin) true) H1500_seg1) (by decide) rfl H1500_fin ptTest_fst
noncomputable def I1500_cp1 : Nat × Nat := t7val% (fastRun pI1500 1 1060 (init pI1500) (init pI1500))
theorem I1500_seg1 : segOK pI1500 1 1060 (init pI1500) (init pI1500) I1500_cp1.1 I1500_cp1.2 = true := by
  decide +kernel
theorem I1500_fin : (prmOK pI1500 1500 && intTest pI1500 (runFrom pI1500 (fmask pI1500) (cmask pI1500) (hmask pI1500) 1061 439 (true, I1500_cp1.1, I1500_cp1.2)) 1500 20 true) = true := by
  decide +kernel
theorem I1500_ok : RunOK pI1500 1500 (runFrom pI1500 (fmask pI1500) (cmask pI1500) (hmask pI1500) 1061 439 (true, I1500_cp1.1, I1500_cp1.2)) ∧ intTest pI1500 (runFrom pI1500 (fmask pI1500) (cmask pI1500) (hmask pI1500) 1061 439 (true, I1500_cp1.1, I1500_cp1.2)) 1500 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1500_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1500_fin) true) I1500_seg1) (by decide) rfl I1500_fin intTest_fst
theorem link1500 : linkOK pL1500 pH1500 pI1500 = true := by decide +kernel
theorem cvx1500 : ConvexBetweenHumps 1500 :=
  cvx_of L1500_ok H1500_ok I1500_ok link1500 (by decide)
theorem cenlink1500 : cenLinkOK pI1500 1500 = true := by decide +kernel
theorem cen1500 : CenterUniqueMin 1500 ∧ DipHyp 1500 ∧ OnePointHyps 1500 :=
  cen_of L1500_ok H1500_ok I1500_ok link1500 cenlink1500

/-! ### `N = 1501` -/

def pL1501 : Prm := ⟨80, 38, 39, 1503, 11, 18446744073709551616, 124372235711485896, 124372235711485896⟩
def pH1501 : Prm := ⟨80, 38, 39, 1503, 11, 18446744073709551616, 124373335223113672, 124373335223113672⟩
def pI1501 : Prm := ⟨66, 33, 30, 1503, 11, 18446744073709551616, 124372235711485896, 124373335223113672⟩
noncomputable def L1501_cp1 : Nat × Nat := t7val% (fastRun pL1501 1 1060 (init pL1501) (init pL1501))
theorem L1501_seg1 : segOK pL1501 1 1060 (init pL1501) (init pL1501) L1501_cp1.1 L1501_cp1.2 = true := by
  decide +kernel
theorem L1501_fin : (prmOK pL1501 1501 && ptTest pL1501 (runFrom pL1501 (fmask pL1501) (cmask pL1501) (hmask pL1501) 1061 440 (true, L1501_cp1.1, L1501_cp1.2)) 1501 751 false) = true := by
  decide +kernel
theorem L1501_ok : RunOK pL1501 1501 (runFrom pL1501 (fmask pL1501) (cmask pL1501) (hmask pL1501) 1061 440 (true, L1501_cp1.1, L1501_cp1.2)) ∧ ptTest pL1501 (runFrom pL1501 (fmask pL1501) (cmask pL1501) (hmask pL1501) 1061 440 (true, L1501_cp1.1, L1501_cp1.2)) 1501 751 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1501_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1501_fin) true) L1501_seg1) (by decide) rfl L1501_fin ptTest_fst
noncomputable def H1501_cp1 : Nat × Nat := t7val% (fastRun pH1501 1 1060 (init pH1501) (init pH1501))
theorem H1501_seg1 : segOK pH1501 1 1060 (init pH1501) (init pH1501) H1501_cp1.1 H1501_cp1.2 = true := by
  decide +kernel
theorem H1501_fin : (prmOK pH1501 1501 && ptTest pH1501 (runFrom pH1501 (fmask pH1501) (cmask pH1501) (hmask pH1501) 1061 440 (true, H1501_cp1.1, H1501_cp1.2)) 1501 751 true) = true := by
  decide +kernel
theorem H1501_ok : RunOK pH1501 1501 (runFrom pH1501 (fmask pH1501) (cmask pH1501) (hmask pH1501) 1061 440 (true, H1501_cp1.1, H1501_cp1.2)) ∧ ptTest pH1501 (runFrom pH1501 (fmask pH1501) (cmask pH1501) (hmask pH1501) 1061 440 (true, H1501_cp1.1, H1501_cp1.2)) 1501 751 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1501_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1501_fin) true) H1501_seg1) (by decide) rfl H1501_fin ptTest_fst
noncomputable def I1501_cp1 : Nat × Nat := t7val% (fastRun pI1501 1 1060 (init pI1501) (init pI1501))
theorem I1501_seg1 : segOK pI1501 1 1060 (init pI1501) (init pI1501) I1501_cp1.1 I1501_cp1.2 = true := by
  decide +kernel
theorem I1501_fin : (prmOK pI1501 1501 && intTest pI1501 (runFrom pI1501 (fmask pI1501) (cmask pI1501) (hmask pI1501) 1061 440 (true, I1501_cp1.1, I1501_cp1.2)) 1501 20 false) = true := by
  decide +kernel
theorem I1501_ok : RunOK pI1501 1501 (runFrom pI1501 (fmask pI1501) (cmask pI1501) (hmask pI1501) 1061 440 (true, I1501_cp1.1, I1501_cp1.2)) ∧ intTest pI1501 (runFrom pI1501 (fmask pI1501) (cmask pI1501) (hmask pI1501) 1061 440 (true, I1501_cp1.1, I1501_cp1.2)) 1501 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1501_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1501_fin) true) I1501_seg1) (by decide) rfl I1501_fin intTest_fst
theorem link1501 : linkOK pL1501 pH1501 pI1501 = true := by decide +kernel
theorem cvx1501 : ConvexBetweenHumps 1501 :=
  cvx_of L1501_ok H1501_ok I1501_ok link1501 (by decide)

/-! ### `N = 1502` -/

def pL1502 : Prm := ⟨80, 38, 39, 1504, 11, 18446744073709551616, 124304870235384181, 124304870235384181⟩
def pH1502 : Prm := ⟨80, 38, 39, 1504, 11, 18446744073709551616, 124305969747011957, 124305969747011957⟩
def pI1502 : Prm := ⟨66, 33, 30, 1504, 11, 18446744073709551616, 124304870235384181, 124305969747011957⟩
noncomputable def L1502_cp1 : Nat × Nat := t7val% (fastRun pL1502 1 1061 (init pL1502) (init pL1502))
theorem L1502_seg1 : segOK pL1502 1 1061 (init pL1502) (init pL1502) L1502_cp1.1 L1502_cp1.2 = true := by
  decide +kernel
theorem L1502_fin : (prmOK pL1502 1502 && ptTest pL1502 (runFrom pL1502 (fmask pL1502) (cmask pL1502) (hmask pL1502) 1062 440 (true, L1502_cp1.1, L1502_cp1.2)) 1502 751 false) = true := by
  decide +kernel
theorem L1502_ok : RunOK pL1502 1502 (runFrom pL1502 (fmask pL1502) (cmask pL1502) (hmask pL1502) 1062 440 (true, L1502_cp1.1, L1502_cp1.2)) ∧ ptTest pL1502 (runFrom pL1502 (fmask pL1502) (cmask pL1502) (hmask pL1502) 1062 440 (true, L1502_cp1.1, L1502_cp1.2)) 1502 751 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1502_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1502_fin) true) L1502_seg1) (by decide) rfl L1502_fin ptTest_fst
noncomputable def H1502_cp1 : Nat × Nat := t7val% (fastRun pH1502 1 1061 (init pH1502) (init pH1502))
theorem H1502_seg1 : segOK pH1502 1 1061 (init pH1502) (init pH1502) H1502_cp1.1 H1502_cp1.2 = true := by
  decide +kernel
theorem H1502_fin : (prmOK pH1502 1502 && ptTest pH1502 (runFrom pH1502 (fmask pH1502) (cmask pH1502) (hmask pH1502) 1062 440 (true, H1502_cp1.1, H1502_cp1.2)) 1502 751 true) = true := by
  decide +kernel
theorem H1502_ok : RunOK pH1502 1502 (runFrom pH1502 (fmask pH1502) (cmask pH1502) (hmask pH1502) 1062 440 (true, H1502_cp1.1, H1502_cp1.2)) ∧ ptTest pH1502 (runFrom pH1502 (fmask pH1502) (cmask pH1502) (hmask pH1502) 1062 440 (true, H1502_cp1.1, H1502_cp1.2)) 1502 751 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1502_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1502_fin) true) H1502_seg1) (by decide) rfl H1502_fin ptTest_fst
noncomputable def I1502_cp1 : Nat × Nat := t7val% (fastRun pI1502 1 1061 (init pI1502) (init pI1502))
theorem I1502_seg1 : segOK pI1502 1 1061 (init pI1502) (init pI1502) I1502_cp1.1 I1502_cp1.2 = true := by
  decide +kernel
theorem I1502_fin : (prmOK pI1502 1502 && intTest pI1502 (runFrom pI1502 (fmask pI1502) (cmask pI1502) (hmask pI1502) 1062 440 (true, I1502_cp1.1, I1502_cp1.2)) 1502 20 true) = true := by
  decide +kernel
theorem I1502_ok : RunOK pI1502 1502 (runFrom pI1502 (fmask pI1502) (cmask pI1502) (hmask pI1502) 1062 440 (true, I1502_cp1.1, I1502_cp1.2)) ∧ intTest pI1502 (runFrom pI1502 (fmask pI1502) (cmask pI1502) (hmask pI1502) 1062 440 (true, I1502_cp1.1, I1502_cp1.2)) 1502 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1502_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1502_fin) true) I1502_seg1) (by decide) rfl I1502_fin intTest_fst
theorem link1502 : linkOK pL1502 pH1502 pI1502 = true := by decide +kernel
theorem cvx1502 : ConvexBetweenHumps 1502 :=
  cvx_of L1502_ok H1502_ok I1502_ok link1502 (by decide)
theorem cenlink1502 : cenLinkOK pI1502 1502 = true := by decide +kernel
theorem cen1502 : CenterUniqueMin 1502 ∧ DipHyp 1502 ∧ OnePointHyps 1502 :=
  cen_of L1502_ok H1502_ok I1502_ok link1502 cenlink1502

/-! ### `N = 1503` -/

def pL1503 : Prm := ⟨80, 38, 39, 1505, 11, 18446744073709551616, 124237550748730988, 124237550748730988⟩
def pH1503 : Prm := ⟨80, 38, 39, 1505, 11, 18446744073709551616, 124238650260358764, 124238650260358764⟩
def pI1503 : Prm := ⟨66, 33, 30, 1505, 11, 18446744073709551616, 124237550748730988, 124238650260358764⟩
noncomputable def L1503_cp1 : Nat × Nat := t7val% (fastRun pL1503 1 1062 (init pL1503) (init pL1503))
theorem L1503_seg1 : segOK pL1503 1 1062 (init pL1503) (init pL1503) L1503_cp1.1 L1503_cp1.2 = true := by
  decide +kernel
theorem L1503_fin : (prmOK pL1503 1503 && ptTest pL1503 (runFrom pL1503 (fmask pL1503) (cmask pL1503) (hmask pL1503) 1063 440 (true, L1503_cp1.1, L1503_cp1.2)) 1503 752 false) = true := by
  decide +kernel
theorem L1503_ok : RunOK pL1503 1503 (runFrom pL1503 (fmask pL1503) (cmask pL1503) (hmask pL1503) 1063 440 (true, L1503_cp1.1, L1503_cp1.2)) ∧ ptTest pL1503 (runFrom pL1503 (fmask pL1503) (cmask pL1503) (hmask pL1503) 1063 440 (true, L1503_cp1.1, L1503_cp1.2)) 1503 752 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1503_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1503_fin) true) L1503_seg1) (by decide) rfl L1503_fin ptTest_fst
noncomputable def H1503_cp1 : Nat × Nat := t7val% (fastRun pH1503 1 1062 (init pH1503) (init pH1503))
theorem H1503_seg1 : segOK pH1503 1 1062 (init pH1503) (init pH1503) H1503_cp1.1 H1503_cp1.2 = true := by
  decide +kernel
theorem H1503_fin : (prmOK pH1503 1503 && ptTest pH1503 (runFrom pH1503 (fmask pH1503) (cmask pH1503) (hmask pH1503) 1063 440 (true, H1503_cp1.1, H1503_cp1.2)) 1503 752 true) = true := by
  decide +kernel
theorem H1503_ok : RunOK pH1503 1503 (runFrom pH1503 (fmask pH1503) (cmask pH1503) (hmask pH1503) 1063 440 (true, H1503_cp1.1, H1503_cp1.2)) ∧ ptTest pH1503 (runFrom pH1503 (fmask pH1503) (cmask pH1503) (hmask pH1503) 1063 440 (true, H1503_cp1.1, H1503_cp1.2)) 1503 752 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1503_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1503_fin) true) H1503_seg1) (by decide) rfl H1503_fin ptTest_fst
noncomputable def I1503_cp1 : Nat × Nat := t7val% (fastRun pI1503 1 1062 (init pI1503) (init pI1503))
theorem I1503_seg1 : segOK pI1503 1 1062 (init pI1503) (init pI1503) I1503_cp1.1 I1503_cp1.2 = true := by
  decide +kernel
theorem I1503_fin : (prmOK pI1503 1503 && intTest pI1503 (runFrom pI1503 (fmask pI1503) (cmask pI1503) (hmask pI1503) 1063 440 (true, I1503_cp1.1, I1503_cp1.2)) 1503 20 false) = true := by
  decide +kernel
theorem I1503_ok : RunOK pI1503 1503 (runFrom pI1503 (fmask pI1503) (cmask pI1503) (hmask pI1503) 1063 440 (true, I1503_cp1.1, I1503_cp1.2)) ∧ intTest pI1503 (runFrom pI1503 (fmask pI1503) (cmask pI1503) (hmask pI1503) 1063 440 (true, I1503_cp1.1, I1503_cp1.2)) 1503 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1503_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1503_fin) true) I1503_seg1) (by decide) rfl I1503_fin intTest_fst
theorem link1503 : linkOK pL1503 pH1503 pI1503 = true := by decide +kernel
theorem cvx1503 : ConvexBetweenHumps 1503 :=
  cvx_of L1503_ok H1503_ok I1503_ok link1503 (by decide)

/-! ### `N = 1504` -/

def pL1504 : Prm := ⟨80, 38, 39, 1506, 11, 18446744073709551616, 124170343848127795, 124170343848127795⟩
def pH1504 : Prm := ⟨80, 38, 39, 1506, 11, 18446744073709551616, 124171443359755571, 124171443359755571⟩
def pI1504 : Prm := ⟨66, 33, 30, 1506, 11, 18446744073709551616, 124170343848127795, 124171443359755571⟩
noncomputable def L1504_cp1 : Nat × Nat := t7val% (fastRun pL1504 1 1062 (init pL1504) (init pL1504))
theorem L1504_seg1 : segOK pL1504 1 1062 (init pL1504) (init pL1504) L1504_cp1.1 L1504_cp1.2 = true := by
  decide +kernel
theorem L1504_fin : (prmOK pL1504 1504 && ptTest pL1504 (runFrom pL1504 (fmask pL1504) (cmask pL1504) (hmask pL1504) 1063 441 (true, L1504_cp1.1, L1504_cp1.2)) 1504 752 false) = true := by
  decide +kernel
theorem L1504_ok : RunOK pL1504 1504 (runFrom pL1504 (fmask pL1504) (cmask pL1504) (hmask pL1504) 1063 441 (true, L1504_cp1.1, L1504_cp1.2)) ∧ ptTest pL1504 (runFrom pL1504 (fmask pL1504) (cmask pL1504) (hmask pL1504) 1063 441 (true, L1504_cp1.1, L1504_cp1.2)) 1504 752 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1504_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1504_fin) true) L1504_seg1) (by decide) rfl L1504_fin ptTest_fst
noncomputable def H1504_cp1 : Nat × Nat := t7val% (fastRun pH1504 1 1062 (init pH1504) (init pH1504))
theorem H1504_seg1 : segOK pH1504 1 1062 (init pH1504) (init pH1504) H1504_cp1.1 H1504_cp1.2 = true := by
  decide +kernel
theorem H1504_fin : (prmOK pH1504 1504 && ptTest pH1504 (runFrom pH1504 (fmask pH1504) (cmask pH1504) (hmask pH1504) 1063 441 (true, H1504_cp1.1, H1504_cp1.2)) 1504 752 true) = true := by
  decide +kernel
theorem H1504_ok : RunOK pH1504 1504 (runFrom pH1504 (fmask pH1504) (cmask pH1504) (hmask pH1504) 1063 441 (true, H1504_cp1.1, H1504_cp1.2)) ∧ ptTest pH1504 (runFrom pH1504 (fmask pH1504) (cmask pH1504) (hmask pH1504) 1063 441 (true, H1504_cp1.1, H1504_cp1.2)) 1504 752 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1504_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1504_fin) true) H1504_seg1) (by decide) rfl H1504_fin ptTest_fst
noncomputable def I1504_cp1 : Nat × Nat := t7val% (fastRun pI1504 1 1062 (init pI1504) (init pI1504))
theorem I1504_seg1 : segOK pI1504 1 1062 (init pI1504) (init pI1504) I1504_cp1.1 I1504_cp1.2 = true := by
  decide +kernel
theorem I1504_fin : (prmOK pI1504 1504 && intTest pI1504 (runFrom pI1504 (fmask pI1504) (cmask pI1504) (hmask pI1504) 1063 441 (true, I1504_cp1.1, I1504_cp1.2)) 1504 20 true) = true := by
  decide +kernel
theorem I1504_ok : RunOK pI1504 1504 (runFrom pI1504 (fmask pI1504) (cmask pI1504) (hmask pI1504) 1063 441 (true, I1504_cp1.1, I1504_cp1.2)) ∧ intTest pI1504 (runFrom pI1504 (fmask pI1504) (cmask pI1504) (hmask pI1504) 1063 441 (true, I1504_cp1.1, I1504_cp1.2)) 1504 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1504_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1504_fin) true) I1504_seg1) (by decide) rfl I1504_fin intTest_fst
theorem link1504 : linkOK pL1504 pH1504 pI1504 = true := by decide +kernel
theorem cvx1504 : ConvexBetweenHumps 1504 :=
  cvx_of L1504_ok H1504_ok I1504_ok link1504 (by decide)
theorem cenlink1504 : cenLinkOK pI1504 1504 = true := by decide +kernel
theorem cen1504 : CenterUniqueMin 1504 ∧ DipHyp 1504 ∧ OnePointHyps 1504 :=
  cen_of L1504_ok H1504_ok I1504_ok link1504 cenlink1504

/-! ### `N = 1505` -/

def pL1505 : Prm := ⟨80, 38, 39, 1507, 11, 18446744073709551616, 124103182783164172, 124103182783164172⟩
def pH1505 : Prm := ⟨80, 38, 39, 1507, 11, 18446744073709551616, 124104282294791948, 124104282294791948⟩
def pI1505 : Prm := ⟨66, 33, 30, 1507, 11, 18446744073709551616, 124103182783164172, 124104282294791948⟩
noncomputable def L1505_cp1 : Nat × Nat := t7val% (fastRun pL1505 1 1063 (init pL1505) (init pL1505))
theorem L1505_seg1 : segOK pL1505 1 1063 (init pL1505) (init pL1505) L1505_cp1.1 L1505_cp1.2 = true := by
  decide +kernel
theorem L1505_fin : (prmOK pL1505 1505 && ptTest pL1505 (runFrom pL1505 (fmask pL1505) (cmask pL1505) (hmask pL1505) 1064 441 (true, L1505_cp1.1, L1505_cp1.2)) 1505 753 false) = true := by
  decide +kernel
theorem L1505_ok : RunOK pL1505 1505 (runFrom pL1505 (fmask pL1505) (cmask pL1505) (hmask pL1505) 1064 441 (true, L1505_cp1.1, L1505_cp1.2)) ∧ ptTest pL1505 (runFrom pL1505 (fmask pL1505) (cmask pL1505) (hmask pL1505) 1064 441 (true, L1505_cp1.1, L1505_cp1.2)) 1505 753 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1505_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1505_fin) true) L1505_seg1) (by decide) rfl L1505_fin ptTest_fst
noncomputable def H1505_cp1 : Nat × Nat := t7val% (fastRun pH1505 1 1063 (init pH1505) (init pH1505))
theorem H1505_seg1 : segOK pH1505 1 1063 (init pH1505) (init pH1505) H1505_cp1.1 H1505_cp1.2 = true := by
  decide +kernel
theorem H1505_fin : (prmOK pH1505 1505 && ptTest pH1505 (runFrom pH1505 (fmask pH1505) (cmask pH1505) (hmask pH1505) 1064 441 (true, H1505_cp1.1, H1505_cp1.2)) 1505 753 true) = true := by
  decide +kernel
theorem H1505_ok : RunOK pH1505 1505 (runFrom pH1505 (fmask pH1505) (cmask pH1505) (hmask pH1505) 1064 441 (true, H1505_cp1.1, H1505_cp1.2)) ∧ ptTest pH1505 (runFrom pH1505 (fmask pH1505) (cmask pH1505) (hmask pH1505) 1064 441 (true, H1505_cp1.1, H1505_cp1.2)) 1505 753 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1505_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1505_fin) true) H1505_seg1) (by decide) rfl H1505_fin ptTest_fst
noncomputable def I1505_cp1 : Nat × Nat := t7val% (fastRun pI1505 1 1063 (init pI1505) (init pI1505))
theorem I1505_seg1 : segOK pI1505 1 1063 (init pI1505) (init pI1505) I1505_cp1.1 I1505_cp1.2 = true := by
  decide +kernel
theorem I1505_fin : (prmOK pI1505 1505 && intTest pI1505 (runFrom pI1505 (fmask pI1505) (cmask pI1505) (hmask pI1505) 1064 441 (true, I1505_cp1.1, I1505_cp1.2)) 1505 20 false) = true := by
  decide +kernel
theorem I1505_ok : RunOK pI1505 1505 (runFrom pI1505 (fmask pI1505) (cmask pI1505) (hmask pI1505) 1064 441 (true, I1505_cp1.1, I1505_cp1.2)) ∧ intTest pI1505 (runFrom pI1505 (fmask pI1505) (cmask pI1505) (hmask pI1505) 1064 441 (true, I1505_cp1.1, I1505_cp1.2)) 1505 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1505_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1505_fin) true) I1505_seg1) (by decide) rfl I1505_fin intTest_fst
theorem link1505 : linkOK pL1505 pH1505 pI1505 = true := by decide +kernel
theorem cvx1505 : ConvexBetweenHumps 1505 :=
  cvx_of L1505_ok H1505_ok I1505_ok link1505 (by decide)

/-! ### `N = 1506` -/

def pL1506 : Prm := ⟨80, 38, 39, 1508, 11, 18446744073709551616, 124036133880990005, 124036133880990005⟩
def pH1506 : Prm := ⟨80, 38, 39, 1508, 11, 18446744073709551616, 124037233392617781, 124037233392617781⟩
def pI1506 : Prm := ⟨66, 33, 30, 1508, 11, 18446744073709551616, 124036133880990005, 124037233392617781⟩
noncomputable def L1506_cp1 : Nat × Nat := t7val% (fastRun pL1506 1 1064 (init pL1506) (init pL1506))
theorem L1506_seg1 : segOK pL1506 1 1064 (init pL1506) (init pL1506) L1506_cp1.1 L1506_cp1.2 = true := by
  decide +kernel
theorem L1506_fin : (prmOK pL1506 1506 && ptTest pL1506 (runFrom pL1506 (fmask pL1506) (cmask pL1506) (hmask pL1506) 1065 441 (true, L1506_cp1.1, L1506_cp1.2)) 1506 753 false) = true := by
  decide +kernel
theorem L1506_ok : RunOK pL1506 1506 (runFrom pL1506 (fmask pL1506) (cmask pL1506) (hmask pL1506) 1065 441 (true, L1506_cp1.1, L1506_cp1.2)) ∧ ptTest pL1506 (runFrom pL1506 (fmask pL1506) (cmask pL1506) (hmask pL1506) 1065 441 (true, L1506_cp1.1, L1506_cp1.2)) 1506 753 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1506_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1506_fin) true) L1506_seg1) (by decide) rfl L1506_fin ptTest_fst
noncomputable def H1506_cp1 : Nat × Nat := t7val% (fastRun pH1506 1 1064 (init pH1506) (init pH1506))
theorem H1506_seg1 : segOK pH1506 1 1064 (init pH1506) (init pH1506) H1506_cp1.1 H1506_cp1.2 = true := by
  decide +kernel
theorem H1506_fin : (prmOK pH1506 1506 && ptTest pH1506 (runFrom pH1506 (fmask pH1506) (cmask pH1506) (hmask pH1506) 1065 441 (true, H1506_cp1.1, H1506_cp1.2)) 1506 753 true) = true := by
  decide +kernel
theorem H1506_ok : RunOK pH1506 1506 (runFrom pH1506 (fmask pH1506) (cmask pH1506) (hmask pH1506) 1065 441 (true, H1506_cp1.1, H1506_cp1.2)) ∧ ptTest pH1506 (runFrom pH1506 (fmask pH1506) (cmask pH1506) (hmask pH1506) 1065 441 (true, H1506_cp1.1, H1506_cp1.2)) 1506 753 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1506_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1506_fin) true) H1506_seg1) (by decide) rfl H1506_fin ptTest_fst
noncomputable def I1506_cp1 : Nat × Nat := t7val% (fastRun pI1506 1 1064 (init pI1506) (init pI1506))
theorem I1506_seg1 : segOK pI1506 1 1064 (init pI1506) (init pI1506) I1506_cp1.1 I1506_cp1.2 = true := by
  decide +kernel
theorem I1506_fin : (prmOK pI1506 1506 && intTest pI1506 (runFrom pI1506 (fmask pI1506) (cmask pI1506) (hmask pI1506) 1065 441 (true, I1506_cp1.1, I1506_cp1.2)) 1506 20 true) = true := by
  decide +kernel
theorem I1506_ok : RunOK pI1506 1506 (runFrom pI1506 (fmask pI1506) (cmask pI1506) (hmask pI1506) 1065 441 (true, I1506_cp1.1, I1506_cp1.2)) ∧ intTest pI1506 (runFrom pI1506 (fmask pI1506) (cmask pI1506) (hmask pI1506) 1065 441 (true, I1506_cp1.1, I1506_cp1.2)) 1506 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1506_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1506_fin) true) I1506_seg1) (by decide) rfl I1506_fin intTest_fst
theorem link1506 : linkOK pL1506 pH1506 pI1506 = true := by decide +kernel
theorem cvx1506 : ConvexBetweenHumps 1506 :=
  cvx_of L1506_ok H1506_ok I1506_ok link1506 (by decide)
theorem cenlink1506 : cenLinkOK pI1506 1506 = true := by decide +kernel
theorem cen1506 : CenterUniqueMin 1506 ∧ DipHyp 1506 ∧ OnePointHyps 1506 :=
  cen_of L1506_ok H1506_ok I1506_ok link1506 cenlink1506

/-! ### `N = 1507` -/

def pL1507 : Prm := ⟨80, 38, 39, 1509, 11, 18446744073709551616, 123969130661292093, 123969130661292093⟩
def pH1507 : Prm := ⟨80, 38, 39, 1509, 11, 18446744073709551616, 123970230172919869, 123970230172919869⟩
def pI1507 : Prm := ⟨66, 33, 30, 1509, 11, 18446744073709551616, 123969130661292093, 123970230172919869⟩
noncomputable def L1507_cp1 : Nat × Nat := t7val% (fastRun pL1507 1 1065 (init pL1507) (init pL1507))
theorem L1507_seg1 : segOK pL1507 1 1065 (init pL1507) (init pL1507) L1507_cp1.1 L1507_cp1.2 = true := by
  decide +kernel
theorem L1507_fin : (prmOK pL1507 1507 && ptTest pL1507 (runFrom pL1507 (fmask pL1507) (cmask pL1507) (hmask pL1507) 1066 441 (true, L1507_cp1.1, L1507_cp1.2)) 1507 754 false) = true := by
  decide +kernel
theorem L1507_ok : RunOK pL1507 1507 (runFrom pL1507 (fmask pL1507) (cmask pL1507) (hmask pL1507) 1066 441 (true, L1507_cp1.1, L1507_cp1.2)) ∧ ptTest pL1507 (runFrom pL1507 (fmask pL1507) (cmask pL1507) (hmask pL1507) 1066 441 (true, L1507_cp1.1, L1507_cp1.2)) 1507 754 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1507_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1507_fin) true) L1507_seg1) (by decide) rfl L1507_fin ptTest_fst
noncomputable def H1507_cp1 : Nat × Nat := t7val% (fastRun pH1507 1 1065 (init pH1507) (init pH1507))
theorem H1507_seg1 : segOK pH1507 1 1065 (init pH1507) (init pH1507) H1507_cp1.1 H1507_cp1.2 = true := by
  decide +kernel
theorem H1507_fin : (prmOK pH1507 1507 && ptTest pH1507 (runFrom pH1507 (fmask pH1507) (cmask pH1507) (hmask pH1507) 1066 441 (true, H1507_cp1.1, H1507_cp1.2)) 1507 754 true) = true := by
  decide +kernel
theorem H1507_ok : RunOK pH1507 1507 (runFrom pH1507 (fmask pH1507) (cmask pH1507) (hmask pH1507) 1066 441 (true, H1507_cp1.1, H1507_cp1.2)) ∧ ptTest pH1507 (runFrom pH1507 (fmask pH1507) (cmask pH1507) (hmask pH1507) 1066 441 (true, H1507_cp1.1, H1507_cp1.2)) 1507 754 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1507_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1507_fin) true) H1507_seg1) (by decide) rfl H1507_fin ptTest_fst
noncomputable def I1507_cp1 : Nat × Nat := t7val% (fastRun pI1507 1 1065 (init pI1507) (init pI1507))
theorem I1507_seg1 : segOK pI1507 1 1065 (init pI1507) (init pI1507) I1507_cp1.1 I1507_cp1.2 = true := by
  decide +kernel
theorem I1507_fin : (prmOK pI1507 1507 && intTest pI1507 (runFrom pI1507 (fmask pI1507) (cmask pI1507) (hmask pI1507) 1066 441 (true, I1507_cp1.1, I1507_cp1.2)) 1507 20 false) = true := by
  decide +kernel
theorem I1507_ok : RunOK pI1507 1507 (runFrom pI1507 (fmask pI1507) (cmask pI1507) (hmask pI1507) 1066 441 (true, I1507_cp1.1, I1507_cp1.2)) ∧ intTest pI1507 (runFrom pI1507 (fmask pI1507) (cmask pI1507) (hmask pI1507) 1066 441 (true, I1507_cp1.1, I1507_cp1.2)) 1507 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1507_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1507_fin) true) I1507_seg1) (by decide) rfl I1507_fin intTest_fst
theorem link1507 : linkOK pL1507 pH1507 pI1507 = true := by decide +kernel
theorem cvx1507 : ConvexBetweenHumps 1507 :=
  cvx_of L1507_ok H1507_ok I1507_ok link1507 (by decide)

/-! ### `N = 1508` -/

def pL1508 : Prm := ⟨80, 38, 39, 1510, 11, 18446744073709551616, 123902239183318256, 123902239183318256⟩
def pH1508 : Prm := ⟨80, 38, 39, 1510, 11, 18446744073709551616, 123903338694946032, 123903338694946032⟩
def pI1508 : Prm := ⟨66, 33, 30, 1510, 11, 18446744073709551616, 123902239183318256, 123903338694946032⟩
noncomputable def L1508_cp1 : Nat × Nat := t7val% (fastRun pL1508 1 1065 (init pL1508) (init pL1508))
theorem L1508_seg1 : segOK pL1508 1 1065 (init pL1508) (init pL1508) L1508_cp1.1 L1508_cp1.2 = true := by
  decide +kernel
theorem L1508_fin : (prmOK pL1508 1508 && ptTest pL1508 (runFrom pL1508 (fmask pL1508) (cmask pL1508) (hmask pL1508) 1066 442 (true, L1508_cp1.1, L1508_cp1.2)) 1508 754 false) = true := by
  decide +kernel
theorem L1508_ok : RunOK pL1508 1508 (runFrom pL1508 (fmask pL1508) (cmask pL1508) (hmask pL1508) 1066 442 (true, L1508_cp1.1, L1508_cp1.2)) ∧ ptTest pL1508 (runFrom pL1508 (fmask pL1508) (cmask pL1508) (hmask pL1508) 1066 442 (true, L1508_cp1.1, L1508_cp1.2)) 1508 754 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1508_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1508_fin) true) L1508_seg1) (by decide) rfl L1508_fin ptTest_fst
noncomputable def H1508_cp1 : Nat × Nat := t7val% (fastRun pH1508 1 1065 (init pH1508) (init pH1508))
theorem H1508_seg1 : segOK pH1508 1 1065 (init pH1508) (init pH1508) H1508_cp1.1 H1508_cp1.2 = true := by
  decide +kernel
theorem H1508_fin : (prmOK pH1508 1508 && ptTest pH1508 (runFrom pH1508 (fmask pH1508) (cmask pH1508) (hmask pH1508) 1066 442 (true, H1508_cp1.1, H1508_cp1.2)) 1508 754 true) = true := by
  decide +kernel
theorem H1508_ok : RunOK pH1508 1508 (runFrom pH1508 (fmask pH1508) (cmask pH1508) (hmask pH1508) 1066 442 (true, H1508_cp1.1, H1508_cp1.2)) ∧ ptTest pH1508 (runFrom pH1508 (fmask pH1508) (cmask pH1508) (hmask pH1508) 1066 442 (true, H1508_cp1.1, H1508_cp1.2)) 1508 754 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1508_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1508_fin) true) H1508_seg1) (by decide) rfl H1508_fin ptTest_fst
noncomputable def I1508_cp1 : Nat × Nat := t7val% (fastRun pI1508 1 1065 (init pI1508) (init pI1508))
theorem I1508_seg1 : segOK pI1508 1 1065 (init pI1508) (init pI1508) I1508_cp1.1 I1508_cp1.2 = true := by
  decide +kernel
theorem I1508_fin : (prmOK pI1508 1508 && intTest pI1508 (runFrom pI1508 (fmask pI1508) (cmask pI1508) (hmask pI1508) 1066 442 (true, I1508_cp1.1, I1508_cp1.2)) 1508 20 true) = true := by
  decide +kernel
theorem I1508_ok : RunOK pI1508 1508 (runFrom pI1508 (fmask pI1508) (cmask pI1508) (hmask pI1508) 1066 442 (true, I1508_cp1.1, I1508_cp1.2)) ∧ intTest pI1508 (runFrom pI1508 (fmask pI1508) (cmask pI1508) (hmask pI1508) 1066 442 (true, I1508_cp1.1, I1508_cp1.2)) 1508 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1508_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1508_fin) true) I1508_seg1) (by decide) rfl I1508_fin intTest_fst
theorem link1508 : linkOK pL1508 pH1508 pI1508 = true := by decide +kernel
theorem cvx1508 : ConvexBetweenHumps 1508 :=
  cvx_of L1508_ok H1508_ok I1508_ok link1508 (by decide)
theorem cenlink1508 : cenLinkOK pI1508 1508 = true := by decide +kernel
theorem cen1508 : CenterUniqueMin 1508 ∧ DipHyp 1508 ∧ OnePointHyps 1508 :=
  cen_of L1508_ok H1508_ok I1508_ok link1508 cenlink1508

/-! ### `N = 1509` -/

def pL1509 : Prm := ⟨80, 38, 39, 1511, 11, 18446744073709551616, 123835393235376781, 123835393235376781⟩
def pH1509 : Prm := ⟨80, 38, 39, 1511, 11, 18446744073709551616, 123836492747004557, 123836492747004557⟩
def pI1509 : Prm := ⟨66, 33, 30, 1511, 11, 18446744073709551616, 123835393235376781, 123836492747004557⟩
noncomputable def L1509_cp1 : Nat × Nat := t7val% (fastRun pL1509 1 1066 (init pL1509) (init pL1509))
theorem L1509_seg1 : segOK pL1509 1 1066 (init pL1509) (init pL1509) L1509_cp1.1 L1509_cp1.2 = true := by
  decide +kernel
theorem L1509_fin : (prmOK pL1509 1509 && ptTest pL1509 (runFrom pL1509 (fmask pL1509) (cmask pL1509) (hmask pL1509) 1067 442 (true, L1509_cp1.1, L1509_cp1.2)) 1509 755 false) = true := by
  decide +kernel
theorem L1509_ok : RunOK pL1509 1509 (runFrom pL1509 (fmask pL1509) (cmask pL1509) (hmask pL1509) 1067 442 (true, L1509_cp1.1, L1509_cp1.2)) ∧ ptTest pL1509 (runFrom pL1509 (fmask pL1509) (cmask pL1509) (hmask pL1509) 1067 442 (true, L1509_cp1.1, L1509_cp1.2)) 1509 755 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1509_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1509_fin) true) L1509_seg1) (by decide) rfl L1509_fin ptTest_fst
noncomputable def H1509_cp1 : Nat × Nat := t7val% (fastRun pH1509 1 1066 (init pH1509) (init pH1509))
theorem H1509_seg1 : segOK pH1509 1 1066 (init pH1509) (init pH1509) H1509_cp1.1 H1509_cp1.2 = true := by
  decide +kernel
theorem H1509_fin : (prmOK pH1509 1509 && ptTest pH1509 (runFrom pH1509 (fmask pH1509) (cmask pH1509) (hmask pH1509) 1067 442 (true, H1509_cp1.1, H1509_cp1.2)) 1509 755 true) = true := by
  decide +kernel
theorem H1509_ok : RunOK pH1509 1509 (runFrom pH1509 (fmask pH1509) (cmask pH1509) (hmask pH1509) 1067 442 (true, H1509_cp1.1, H1509_cp1.2)) ∧ ptTest pH1509 (runFrom pH1509 (fmask pH1509) (cmask pH1509) (hmask pH1509) 1067 442 (true, H1509_cp1.1, H1509_cp1.2)) 1509 755 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1509_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1509_fin) true) H1509_seg1) (by decide) rfl H1509_fin ptTest_fst
noncomputable def I1509_cp1 : Nat × Nat := t7val% (fastRun pI1509 1 1066 (init pI1509) (init pI1509))
theorem I1509_seg1 : segOK pI1509 1 1066 (init pI1509) (init pI1509) I1509_cp1.1 I1509_cp1.2 = true := by
  decide +kernel
theorem I1509_fin : (prmOK pI1509 1509 && intTest pI1509 (runFrom pI1509 (fmask pI1509) (cmask pI1509) (hmask pI1509) 1067 442 (true, I1509_cp1.1, I1509_cp1.2)) 1509 20 false) = true := by
  decide +kernel
theorem I1509_ok : RunOK pI1509 1509 (runFrom pI1509 (fmask pI1509) (cmask pI1509) (hmask pI1509) 1067 442 (true, I1509_cp1.1, I1509_cp1.2)) ∧ intTest pI1509 (runFrom pI1509 (fmask pI1509) (cmask pI1509) (hmask pI1509) 1067 442 (true, I1509_cp1.1, I1509_cp1.2)) 1509 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1509_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1509_fin) true) I1509_seg1) (by decide) rfl I1509_fin intTest_fst
theorem link1509 : linkOK pL1509 pH1509 pI1509 = true := by decide +kernel
theorem cvx1509 : ConvexBetweenHumps 1509 :=
  cvx_of L1509_ok H1509_ok I1509_ok link1509 (by decide)

/-! ### `N = 1510` -/

def pL1510 : Prm := ⟨80, 38, 39, 1512, 11, 18446744073709551616, 123768658610196930, 123768658610196930⟩
def pH1510 : Prm := ⟨80, 38, 39, 1512, 11, 18446744073709551616, 123769758121824706, 123769758121824706⟩
def pI1510 : Prm := ⟨66, 33, 30, 1512, 11, 18446744073709551616, 123768658610196930, 123769758121824706⟩
noncomputable def L1510_cp1 : Nat × Nat := t7val% (fastRun pL1510 1 1067 (init pL1510) (init pL1510))
theorem L1510_seg1 : segOK pL1510 1 1067 (init pL1510) (init pL1510) L1510_cp1.1 L1510_cp1.2 = true := by
  decide +kernel
theorem L1510_fin : (prmOK pL1510 1510 && ptTest pL1510 (runFrom pL1510 (fmask pL1510) (cmask pL1510) (hmask pL1510) 1068 442 (true, L1510_cp1.1, L1510_cp1.2)) 1510 755 false) = true := by
  decide +kernel
theorem L1510_ok : RunOK pL1510 1510 (runFrom pL1510 (fmask pL1510) (cmask pL1510) (hmask pL1510) 1068 442 (true, L1510_cp1.1, L1510_cp1.2)) ∧ ptTest pL1510 (runFrom pL1510 (fmask pL1510) (cmask pL1510) (hmask pL1510) 1068 442 (true, L1510_cp1.1, L1510_cp1.2)) 1510 755 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1510_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1510_fin) true) L1510_seg1) (by decide) rfl L1510_fin ptTest_fst
noncomputable def H1510_cp1 : Nat × Nat := t7val% (fastRun pH1510 1 1067 (init pH1510) (init pH1510))
theorem H1510_seg1 : segOK pH1510 1 1067 (init pH1510) (init pH1510) H1510_cp1.1 H1510_cp1.2 = true := by
  decide +kernel
theorem H1510_fin : (prmOK pH1510 1510 && ptTest pH1510 (runFrom pH1510 (fmask pH1510) (cmask pH1510) (hmask pH1510) 1068 442 (true, H1510_cp1.1, H1510_cp1.2)) 1510 755 true) = true := by
  decide +kernel
theorem H1510_ok : RunOK pH1510 1510 (runFrom pH1510 (fmask pH1510) (cmask pH1510) (hmask pH1510) 1068 442 (true, H1510_cp1.1, H1510_cp1.2)) ∧ ptTest pH1510 (runFrom pH1510 (fmask pH1510) (cmask pH1510) (hmask pH1510) 1068 442 (true, H1510_cp1.1, H1510_cp1.2)) 1510 755 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1510_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1510_fin) true) H1510_seg1) (by decide) rfl H1510_fin ptTest_fst
noncomputable def I1510_cp1 : Nat × Nat := t7val% (fastRun pI1510 1 1067 (init pI1510) (init pI1510))
theorem I1510_seg1 : segOK pI1510 1 1067 (init pI1510) (init pI1510) I1510_cp1.1 I1510_cp1.2 = true := by
  decide +kernel
theorem I1510_fin : (prmOK pI1510 1510 && intTest pI1510 (runFrom pI1510 (fmask pI1510) (cmask pI1510) (hmask pI1510) 1068 442 (true, I1510_cp1.1, I1510_cp1.2)) 1510 20 true) = true := by
  decide +kernel
theorem I1510_ok : RunOK pI1510 1510 (runFrom pI1510 (fmask pI1510) (cmask pI1510) (hmask pI1510) 1068 442 (true, I1510_cp1.1, I1510_cp1.2)) ∧ intTest pI1510 (runFrom pI1510 (fmask pI1510) (cmask pI1510) (hmask pI1510) 1068 442 (true, I1510_cp1.1, I1510_cp1.2)) 1510 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1510_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1510_fin) true) I1510_seg1) (by decide) rfl I1510_fin intTest_fst
theorem link1510 : linkOK pL1510 pH1510 pI1510 = true := by decide +kernel
theorem cvx1510 : ConvexBetweenHumps 1510 :=
  cvx_of L1510_ok H1510_ok I1510_ok link1510 (by decide)
theorem cenlink1510 : cenLinkOK pI1510 1510 = true := by decide +kernel
theorem cen1510 : CenterUniqueMin 1510 ∧ DipHyp 1510 ∧ OnePointHyps 1510 :=
  cen_of L1510_ok H1510_ok I1510_ok link1510 cenlink1510

/-! ### `N = 1511` -/

def pL1511 : Prm := ⟨80, 38, 39, 1513, 11, 18446744073709551616, 123701969363288078, 123701969363288078⟩
def pH1511 : Prm := ⟨80, 38, 39, 1513, 11, 18446744073709551616, 123703068874915854, 123703068874915854⟩
def pI1511 : Prm := ⟨66, 33, 30, 1513, 11, 18446744073709551616, 123701969363288078, 123703068874915854⟩
noncomputable def L1511_cp1 : Nat × Nat := t7val% (fastRun pL1511 1 1067 (init pL1511) (init pL1511))
theorem L1511_seg1 : segOK pL1511 1 1067 (init pL1511) (init pL1511) L1511_cp1.1 L1511_cp1.2 = true := by
  decide +kernel
theorem L1511_fin : (prmOK pL1511 1511 && ptTest pL1511 (runFrom pL1511 (fmask pL1511) (cmask pL1511) (hmask pL1511) 1068 443 (true, L1511_cp1.1, L1511_cp1.2)) 1511 756 false) = true := by
  decide +kernel
theorem L1511_ok : RunOK pL1511 1511 (runFrom pL1511 (fmask pL1511) (cmask pL1511) (hmask pL1511) 1068 443 (true, L1511_cp1.1, L1511_cp1.2)) ∧ ptTest pL1511 (runFrom pL1511 (fmask pL1511) (cmask pL1511) (hmask pL1511) 1068 443 (true, L1511_cp1.1, L1511_cp1.2)) 1511 756 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1511_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1511_fin) true) L1511_seg1) (by decide) rfl L1511_fin ptTest_fst
noncomputable def H1511_cp1 : Nat × Nat := t7val% (fastRun pH1511 1 1067 (init pH1511) (init pH1511))
theorem H1511_seg1 : segOK pH1511 1 1067 (init pH1511) (init pH1511) H1511_cp1.1 H1511_cp1.2 = true := by
  decide +kernel
theorem H1511_fin : (prmOK pH1511 1511 && ptTest pH1511 (runFrom pH1511 (fmask pH1511) (cmask pH1511) (hmask pH1511) 1068 443 (true, H1511_cp1.1, H1511_cp1.2)) 1511 756 true) = true := by
  decide +kernel
theorem H1511_ok : RunOK pH1511 1511 (runFrom pH1511 (fmask pH1511) (cmask pH1511) (hmask pH1511) 1068 443 (true, H1511_cp1.1, H1511_cp1.2)) ∧ ptTest pH1511 (runFrom pH1511 (fmask pH1511) (cmask pH1511) (hmask pH1511) 1068 443 (true, H1511_cp1.1, H1511_cp1.2)) 1511 756 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1511_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1511_fin) true) H1511_seg1) (by decide) rfl H1511_fin ptTest_fst
noncomputable def I1511_cp1 : Nat × Nat := t7val% (fastRun pI1511 1 1067 (init pI1511) (init pI1511))
theorem I1511_seg1 : segOK pI1511 1 1067 (init pI1511) (init pI1511) I1511_cp1.1 I1511_cp1.2 = true := by
  decide +kernel
theorem I1511_fin : (prmOK pI1511 1511 && intTest pI1511 (runFrom pI1511 (fmask pI1511) (cmask pI1511) (hmask pI1511) 1068 443 (true, I1511_cp1.1, I1511_cp1.2)) 1511 20 false) = true := by
  decide +kernel
theorem I1511_ok : RunOK pI1511 1511 (runFrom pI1511 (fmask pI1511) (cmask pI1511) (hmask pI1511) 1068 443 (true, I1511_cp1.1, I1511_cp1.2)) ∧ intTest pI1511 (runFrom pI1511 (fmask pI1511) (cmask pI1511) (hmask pI1511) 1068 443 (true, I1511_cp1.1, I1511_cp1.2)) 1511 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1511_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1511_fin) true) I1511_seg1) (by decide) rfl I1511_fin intTest_fst
theorem link1511 : linkOK pL1511 pH1511 pI1511 = true := by decide +kernel
theorem cvx1511 : ConvexBetweenHumps 1511 :=
  cvx_of L1511_ok H1511_ok I1511_ok link1511 (by decide)

/-! ### `N = 1512` -/

def pL1512 : Prm := ⟨80, 38, 39, 1514, 11, 18446744073709551616, 123635391022299774, 123635391022299774⟩
def pH1512 : Prm := ⟨80, 38, 39, 1514, 11, 18446744073709551616, 123636490533927550, 123636490533927550⟩
def pI1512 : Prm := ⟨66, 33, 30, 1514, 11, 18446744073709551616, 123635391022299774, 123636490533927550⟩
noncomputable def L1512_cp1 : Nat × Nat := t7val% (fastRun pL1512 1 1068 (init pL1512) (init pL1512))
theorem L1512_seg1 : segOK pL1512 1 1068 (init pL1512) (init pL1512) L1512_cp1.1 L1512_cp1.2 = true := by
  decide +kernel
theorem L1512_fin : (prmOK pL1512 1512 && ptTest pL1512 (runFrom pL1512 (fmask pL1512) (cmask pL1512) (hmask pL1512) 1069 443 (true, L1512_cp1.1, L1512_cp1.2)) 1512 756 false) = true := by
  decide +kernel
theorem L1512_ok : RunOK pL1512 1512 (runFrom pL1512 (fmask pL1512) (cmask pL1512) (hmask pL1512) 1069 443 (true, L1512_cp1.1, L1512_cp1.2)) ∧ ptTest pL1512 (runFrom pL1512 (fmask pL1512) (cmask pL1512) (hmask pL1512) 1069 443 (true, L1512_cp1.1, L1512_cp1.2)) 1512 756 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1512_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1512_fin) true) L1512_seg1) (by decide) rfl L1512_fin ptTest_fst
noncomputable def H1512_cp1 : Nat × Nat := t7val% (fastRun pH1512 1 1068 (init pH1512) (init pH1512))
theorem H1512_seg1 : segOK pH1512 1 1068 (init pH1512) (init pH1512) H1512_cp1.1 H1512_cp1.2 = true := by
  decide +kernel
theorem H1512_fin : (prmOK pH1512 1512 && ptTest pH1512 (runFrom pH1512 (fmask pH1512) (cmask pH1512) (hmask pH1512) 1069 443 (true, H1512_cp1.1, H1512_cp1.2)) 1512 756 true) = true := by
  decide +kernel
theorem H1512_ok : RunOK pH1512 1512 (runFrom pH1512 (fmask pH1512) (cmask pH1512) (hmask pH1512) 1069 443 (true, H1512_cp1.1, H1512_cp1.2)) ∧ ptTest pH1512 (runFrom pH1512 (fmask pH1512) (cmask pH1512) (hmask pH1512) 1069 443 (true, H1512_cp1.1, H1512_cp1.2)) 1512 756 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1512_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1512_fin) true) H1512_seg1) (by decide) rfl H1512_fin ptTest_fst
noncomputable def I1512_cp1 : Nat × Nat := t7val% (fastRun pI1512 1 1068 (init pI1512) (init pI1512))
theorem I1512_seg1 : segOK pI1512 1 1068 (init pI1512) (init pI1512) I1512_cp1.1 I1512_cp1.2 = true := by
  decide +kernel
theorem I1512_fin : (prmOK pI1512 1512 && intTest pI1512 (runFrom pI1512 (fmask pI1512) (cmask pI1512) (hmask pI1512) 1069 443 (true, I1512_cp1.1, I1512_cp1.2)) 1512 20 true) = true := by
  decide +kernel
theorem I1512_ok : RunOK pI1512 1512 (runFrom pI1512 (fmask pI1512) (cmask pI1512) (hmask pI1512) 1069 443 (true, I1512_cp1.1, I1512_cp1.2)) ∧ intTest pI1512 (runFrom pI1512 (fmask pI1512) (cmask pI1512) (hmask pI1512) 1069 443 (true, I1512_cp1.1, I1512_cp1.2)) 1512 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1512_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1512_fin) true) I1512_seg1) (by decide) rfl I1512_fin intTest_fst
theorem link1512 : linkOK pL1512 pH1512 pI1512 = true := by decide +kernel
theorem cvx1512 : ConvexBetweenHumps 1512 :=
  cvx_of L1512_ok H1512_ok I1512_ok link1512 (by decide)
theorem cenlink1512 : cenLinkOK pI1512 1512 = true := by decide +kernel
theorem cen1512 : CenterUniqueMin 1512 ∧ DipHyp 1512 ∧ OnePointHyps 1512 :=
  cen_of L1512_ok H1512_ok I1512_ok link1512 cenlink1512

/-! ### The range -/

theorem cvx_1496_1512 {N : ℕ} (h1 : 1496 ≤ N) (h2 : N ≤ 1512) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1503
  · by_cases h4 : N ≤ 1499
    · by_cases h6 : N ≤ 1497
      · by_cases h8 : N ≤ 1496
        · obtain rfl : N = 1496 := by omega
          exact cvx1496
        · obtain rfl : N = 1497 := by omega
          exact cvx1497
      · by_cases h8 : N ≤ 1498
        · obtain rfl : N = 1498 := by omega
          exact cvx1498
        · obtain rfl : N = 1499 := by omega
          exact cvx1499
    · by_cases h6 : N ≤ 1501
      · by_cases h8 : N ≤ 1500
        · obtain rfl : N = 1500 := by omega
          exact cvx1500
        · obtain rfl : N = 1501 := by omega
          exact cvx1501
      · by_cases h8 : N ≤ 1502
        · obtain rfl : N = 1502 := by omega
          exact cvx1502
        · obtain rfl : N = 1503 := by omega
          exact cvx1503
  · by_cases h4 : N ≤ 1507
    · by_cases h6 : N ≤ 1505
      · by_cases h8 : N ≤ 1504
        · obtain rfl : N = 1504 := by omega
          exact cvx1504
        · obtain rfl : N = 1505 := by omega
          exact cvx1505
      · by_cases h8 : N ≤ 1506
        · obtain rfl : N = 1506 := by omega
          exact cvx1506
        · obtain rfl : N = 1507 := by omega
          exact cvx1507
    · by_cases h6 : N ≤ 1509
      · by_cases h8 : N ≤ 1508
        · obtain rfl : N = 1508 := by omega
          exact cvx1508
        · obtain rfl : N = 1509 := by omega
          exact cvx1509
      · by_cases h8 : N ≤ 1510
        · obtain rfl : N = 1510 := by omega
          exact cvx1510
        · by_cases h10 : N ≤ 1511
          · obtain rfl : N = 1511 := by omega
            exact cvx1511
          · obtain rfl : N = 1512 := by omega
            exact cvx1512

theorem cen_1496_1512 {N : ℕ} (h1 : 1496 ≤ N) (h2 : N ≤ 1512) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1502
  · by_cases h4 : N ≤ 1498
    · by_cases h6 : N ≤ 1496
      · obtain rfl : N = 1496 := by omega
        exact cen1496
      · obtain rfl : N = 1498 := by omega
        exact cen1498
    · by_cases h6 : N ≤ 1500
      · obtain rfl : N = 1500 := by omega
        exact cen1500
      · obtain rfl : N = 1502 := by omega
        exact cen1502
  · by_cases h4 : N ≤ 1506
    · by_cases h6 : N ≤ 1504
      · obtain rfl : N = 1504 := by omega
        exact cen1504
      · obtain rfl : N = 1506 := by omega
        exact cen1506
    · by_cases h6 : N ≤ 1508
      · obtain rfl : N = 1508 := by omega
        exact cen1508
      · by_cases h8 : N ≤ 1510
        · obtain rfl : N = 1510 := by omega
          exact cen1510
        · obtain rfl : N = 1512 := by omega
          exact cen1512

end Kagey131.PaperD.T7
