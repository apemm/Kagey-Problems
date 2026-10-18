import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1876, …, 1886` (generated)

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

/-! ### `N = 1876` -/

def pL1876 : Prm := ⟨80, 37, 40, 1878, 11, 18446744073709551616, 103645081097229253, 103645081097229253⟩
def pH1876 : Prm := ⟨80, 37, 40, 1878, 11, 18446744073709551616, 103646180608857029, 103646180608857029⟩
def pI1876 : Prm := ⟨68, 34, 31, 1878, 11, 18446744073709551616, 103645081097229253, 103646180608857029⟩
noncomputable def L1876_cp1 : Nat × Nat := t7val% (fastRun pL1876 1 1082 (init pL1876) (init pL1876))
theorem L1876_seg1 : segOK pL1876 1 1082 (init pL1876) (init pL1876) L1876_cp1.1 L1876_cp1.2 = true := by
  decide +kernel
noncomputable def L1876_cp2 : Nat × Nat := t7val% (fastRun pL1876 1 1531 (init pL1876) (init pL1876))
theorem L1876_seg2 : segOK pL1876 1083 449 L1876_cp1.1 L1876_cp1.2 L1876_cp2.1 L1876_cp2.2 = true := by
  decide +kernel
theorem L1876_fin : (prmOK pL1876 1876 && ptTest pL1876 (runFrom pL1876 (fmask pL1876) (cmask pL1876) (hmask pL1876) 1532 344 (true, L1876_cp2.1, L1876_cp2.2)) 1876 938 false) = true := by
  decide +kernel
theorem L1876_ok : RunOK pL1876 1876 (runFrom pL1876 (fmask pL1876) (cmask pL1876) (hmask pL1876) 1532 344 (true, L1876_cp2.1, L1876_cp2.2)) ∧ ptTest pL1876 (runFrom pL1876 (fmask pL1876) (cmask pL1876) (hmask pL1876) 1532 344 (true, L1876_cp2.1, L1876_cp2.2)) 1876 938 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1876_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1876_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1876_fin) true) L1876_seg1) L1876_seg2) (by decide) rfl L1876_fin ptTest_fst
noncomputable def H1876_cp1 : Nat × Nat := t7val% (fastRun pH1876 1 1082 (init pH1876) (init pH1876))
theorem H1876_seg1 : segOK pH1876 1 1082 (init pH1876) (init pH1876) H1876_cp1.1 H1876_cp1.2 = true := by
  decide +kernel
noncomputable def H1876_cp2 : Nat × Nat := t7val% (fastRun pH1876 1 1531 (init pH1876) (init pH1876))
theorem H1876_seg2 : segOK pH1876 1083 449 H1876_cp1.1 H1876_cp1.2 H1876_cp2.1 H1876_cp2.2 = true := by
  decide +kernel
theorem H1876_fin : (prmOK pH1876 1876 && ptTest pH1876 (runFrom pH1876 (fmask pH1876) (cmask pH1876) (hmask pH1876) 1532 344 (true, H1876_cp2.1, H1876_cp2.2)) 1876 938 true) = true := by
  decide +kernel
theorem H1876_ok : RunOK pH1876 1876 (runFrom pH1876 (fmask pH1876) (cmask pH1876) (hmask pH1876) 1532 344 (true, H1876_cp2.1, H1876_cp2.2)) ∧ ptTest pH1876 (runFrom pH1876 (fmask pH1876) (cmask pH1876) (hmask pH1876) 1532 344 (true, H1876_cp2.1, H1876_cp2.2)) 1876 938 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1876_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1876_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1876_fin) true) H1876_seg1) H1876_seg2) (by decide) rfl H1876_fin ptTest_fst
noncomputable def I1876_cp1 : Nat × Nat := t7val% (fastRun pI1876 1 1082 (init pI1876) (init pI1876))
theorem I1876_seg1 : segOK pI1876 1 1082 (init pI1876) (init pI1876) I1876_cp1.1 I1876_cp1.2 = true := by
  decide +kernel
noncomputable def I1876_cp2 : Nat × Nat := t7val% (fastRun pI1876 1 1531 (init pI1876) (init pI1876))
theorem I1876_seg2 : segOK pI1876 1083 449 I1876_cp1.1 I1876_cp1.2 I1876_cp2.1 I1876_cp2.2 = true := by
  decide +kernel
theorem I1876_fin : (prmOK pI1876 1876 && intTest pI1876 (runFrom pI1876 (fmask pI1876) (cmask pI1876) (hmask pI1876) 1532 344 (true, I1876_cp2.1, I1876_cp2.2)) 1876 21 true) = true := by
  decide +kernel
theorem I1876_ok : RunOK pI1876 1876 (runFrom pI1876 (fmask pI1876) (cmask pI1876) (hmask pI1876) 1532 344 (true, I1876_cp2.1, I1876_cp2.2)) ∧ intTest pI1876 (runFrom pI1876 (fmask pI1876) (cmask pI1876) (hmask pI1876) 1532 344 (true, I1876_cp2.1, I1876_cp2.2)) 1876 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1876_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1876_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1876_fin) true) I1876_seg1) I1876_seg2) (by decide) rfl I1876_fin intTest_fst
theorem link1876 : linkOK pL1876 pH1876 pI1876 = true := by decide +kernel
theorem cvx1876 : ConvexBetweenHumps 1876 :=
  cvx_of L1876_ok H1876_ok I1876_ok link1876 (by decide)
theorem cenlink1876 : cenLinkOK pI1876 1876 = true := by decide +kernel
theorem cen1876 : CenterUniqueMin 1876 ∧ DipHyp 1876 ∧ OnePointHyps 1876 :=
  cen_of L1876_ok H1876_ok I1876_ok link1876 cenlink1876

/-! ### `N = 1877` -/

def pL1877 : Prm := ⟨80, 37, 40, 1879, 11, 18446744073709551616, 103599726088589794, 103599726088589794⟩
def pH1877 : Prm := ⟨80, 37, 40, 1879, 11, 18446744073709551616, 103600825600217570, 103600825600217570⟩
def pI1877 : Prm := ⟨68, 34, 31, 1879, 11, 18446744073709551616, 103599726088589794, 103600825600217570⟩
noncomputable def L1877_cp1 : Nat × Nat := t7val% (fastRun pL1877 1 1083 (init pL1877) (init pL1877))
theorem L1877_seg1 : segOK pL1877 1 1083 (init pL1877) (init pL1877) L1877_cp1.1 L1877_cp1.2 = true := by
  decide +kernel
noncomputable def L1877_cp2 : Nat × Nat := t7val% (fastRun pL1877 1 1532 (init pL1877) (init pL1877))
theorem L1877_seg2 : segOK pL1877 1084 449 L1877_cp1.1 L1877_cp1.2 L1877_cp2.1 L1877_cp2.2 = true := by
  decide +kernel
theorem L1877_fin : (prmOK pL1877 1877 && ptTest pL1877 (runFrom pL1877 (fmask pL1877) (cmask pL1877) (hmask pL1877) 1533 344 (true, L1877_cp2.1, L1877_cp2.2)) 1877 939 false) = true := by
  decide +kernel
theorem L1877_ok : RunOK pL1877 1877 (runFrom pL1877 (fmask pL1877) (cmask pL1877) (hmask pL1877) 1533 344 (true, L1877_cp2.1, L1877_cp2.2)) ∧ ptTest pL1877 (runFrom pL1877 (fmask pL1877) (cmask pL1877) (hmask pL1877) 1533 344 (true, L1877_cp2.1, L1877_cp2.2)) 1877 939 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1877_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1877_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1877_fin) true) L1877_seg1) L1877_seg2) (by decide) rfl L1877_fin ptTest_fst
noncomputable def H1877_cp1 : Nat × Nat := t7val% (fastRun pH1877 1 1083 (init pH1877) (init pH1877))
theorem H1877_seg1 : segOK pH1877 1 1083 (init pH1877) (init pH1877) H1877_cp1.1 H1877_cp1.2 = true := by
  decide +kernel
noncomputable def H1877_cp2 : Nat × Nat := t7val% (fastRun pH1877 1 1532 (init pH1877) (init pH1877))
theorem H1877_seg2 : segOK pH1877 1084 449 H1877_cp1.1 H1877_cp1.2 H1877_cp2.1 H1877_cp2.2 = true := by
  decide +kernel
theorem H1877_fin : (prmOK pH1877 1877 && ptTest pH1877 (runFrom pH1877 (fmask pH1877) (cmask pH1877) (hmask pH1877) 1533 344 (true, H1877_cp2.1, H1877_cp2.2)) 1877 939 true) = true := by
  decide +kernel
theorem H1877_ok : RunOK pH1877 1877 (runFrom pH1877 (fmask pH1877) (cmask pH1877) (hmask pH1877) 1533 344 (true, H1877_cp2.1, H1877_cp2.2)) ∧ ptTest pH1877 (runFrom pH1877 (fmask pH1877) (cmask pH1877) (hmask pH1877) 1533 344 (true, H1877_cp2.1, H1877_cp2.2)) 1877 939 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1877_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1877_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1877_fin) true) H1877_seg1) H1877_seg2) (by decide) rfl H1877_fin ptTest_fst
noncomputable def I1877_cp1 : Nat × Nat := t7val% (fastRun pI1877 1 1083 (init pI1877) (init pI1877))
theorem I1877_seg1 : segOK pI1877 1 1083 (init pI1877) (init pI1877) I1877_cp1.1 I1877_cp1.2 = true := by
  decide +kernel
noncomputable def I1877_cp2 : Nat × Nat := t7val% (fastRun pI1877 1 1532 (init pI1877) (init pI1877))
theorem I1877_seg2 : segOK pI1877 1084 449 I1877_cp1.1 I1877_cp1.2 I1877_cp2.1 I1877_cp2.2 = true := by
  decide +kernel
theorem I1877_fin : (prmOK pI1877 1877 && intTest pI1877 (runFrom pI1877 (fmask pI1877) (cmask pI1877) (hmask pI1877) 1533 344 (true, I1877_cp2.1, I1877_cp2.2)) 1877 21 false) = true := by
  decide +kernel
theorem I1877_ok : RunOK pI1877 1877 (runFrom pI1877 (fmask pI1877) (cmask pI1877) (hmask pI1877) 1533 344 (true, I1877_cp2.1, I1877_cp2.2)) ∧ intTest pI1877 (runFrom pI1877 (fmask pI1877) (cmask pI1877) (hmask pI1877) 1533 344 (true, I1877_cp2.1, I1877_cp2.2)) 1877 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1877_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1877_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1877_fin) true) I1877_seg1) I1877_seg2) (by decide) rfl I1877_fin intTest_fst
theorem link1877 : linkOK pL1877 pH1877 pI1877 = true := by decide +kernel
theorem cvx1877 : ConvexBetweenHumps 1877 :=
  cvx_of L1877_ok H1877_ok I1877_ok link1877 (by decide)

/-! ### `N = 1878` -/

def pL1878 : Prm := ⟨80, 37, 40, 1880, 11, 18446744073709551616, 103554431049835704, 103554431049835704⟩
def pH1878 : Prm := ⟨80, 37, 40, 1880, 11, 18446744073709551616, 103555530561463480, 103555530561463480⟩
def pI1878 : Prm := ⟨68, 34, 31, 1880, 11, 18446744073709551616, 103554431049835704, 103555530561463480⟩
noncomputable def L1878_cp1 : Nat × Nat := t7val% (fastRun pL1878 1 1083 (init pL1878) (init pL1878))
theorem L1878_seg1 : segOK pL1878 1 1083 (init pL1878) (init pL1878) L1878_cp1.1 L1878_cp1.2 = true := by
  decide +kernel
noncomputable def L1878_cp2 : Nat × Nat := t7val% (fastRun pL1878 1 1532 (init pL1878) (init pL1878))
theorem L1878_seg2 : segOK pL1878 1084 449 L1878_cp1.1 L1878_cp1.2 L1878_cp2.1 L1878_cp2.2 = true := by
  decide +kernel
theorem L1878_fin : (prmOK pL1878 1878 && ptTest pL1878 (runFrom pL1878 (fmask pL1878) (cmask pL1878) (hmask pL1878) 1533 345 (true, L1878_cp2.1, L1878_cp2.2)) 1878 939 false) = true := by
  decide +kernel
theorem L1878_ok : RunOK pL1878 1878 (runFrom pL1878 (fmask pL1878) (cmask pL1878) (hmask pL1878) 1533 345 (true, L1878_cp2.1, L1878_cp2.2)) ∧ ptTest pL1878 (runFrom pL1878 (fmask pL1878) (cmask pL1878) (hmask pL1878) 1533 345 (true, L1878_cp2.1, L1878_cp2.2)) 1878 939 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1878_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1878_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1878_fin) true) L1878_seg1) L1878_seg2) (by decide) rfl L1878_fin ptTest_fst
noncomputable def H1878_cp1 : Nat × Nat := t7val% (fastRun pH1878 1 1083 (init pH1878) (init pH1878))
theorem H1878_seg1 : segOK pH1878 1 1083 (init pH1878) (init pH1878) H1878_cp1.1 H1878_cp1.2 = true := by
  decide +kernel
noncomputable def H1878_cp2 : Nat × Nat := t7val% (fastRun pH1878 1 1532 (init pH1878) (init pH1878))
theorem H1878_seg2 : segOK pH1878 1084 449 H1878_cp1.1 H1878_cp1.2 H1878_cp2.1 H1878_cp2.2 = true := by
  decide +kernel
theorem H1878_fin : (prmOK pH1878 1878 && ptTest pH1878 (runFrom pH1878 (fmask pH1878) (cmask pH1878) (hmask pH1878) 1533 345 (true, H1878_cp2.1, H1878_cp2.2)) 1878 939 true) = true := by
  decide +kernel
theorem H1878_ok : RunOK pH1878 1878 (runFrom pH1878 (fmask pH1878) (cmask pH1878) (hmask pH1878) 1533 345 (true, H1878_cp2.1, H1878_cp2.2)) ∧ ptTest pH1878 (runFrom pH1878 (fmask pH1878) (cmask pH1878) (hmask pH1878) 1533 345 (true, H1878_cp2.1, H1878_cp2.2)) 1878 939 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1878_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1878_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1878_fin) true) H1878_seg1) H1878_seg2) (by decide) rfl H1878_fin ptTest_fst
noncomputable def I1878_cp1 : Nat × Nat := t7val% (fastRun pI1878 1 1083 (init pI1878) (init pI1878))
theorem I1878_seg1 : segOK pI1878 1 1083 (init pI1878) (init pI1878) I1878_cp1.1 I1878_cp1.2 = true := by
  decide +kernel
noncomputable def I1878_cp2 : Nat × Nat := t7val% (fastRun pI1878 1 1532 (init pI1878) (init pI1878))
theorem I1878_seg2 : segOK pI1878 1084 449 I1878_cp1.1 I1878_cp1.2 I1878_cp2.1 I1878_cp2.2 = true := by
  decide +kernel
theorem I1878_fin : (prmOK pI1878 1878 && intTest pI1878 (runFrom pI1878 (fmask pI1878) (cmask pI1878) (hmask pI1878) 1533 345 (true, I1878_cp2.1, I1878_cp2.2)) 1878 21 true) = true := by
  decide +kernel
theorem I1878_ok : RunOK pI1878 1878 (runFrom pI1878 (fmask pI1878) (cmask pI1878) (hmask pI1878) 1533 345 (true, I1878_cp2.1, I1878_cp2.2)) ∧ intTest pI1878 (runFrom pI1878 (fmask pI1878) (cmask pI1878) (hmask pI1878) 1533 345 (true, I1878_cp2.1, I1878_cp2.2)) 1878 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1878_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1878_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1878_fin) true) I1878_seg1) I1878_seg2) (by decide) rfl I1878_fin intTest_fst
theorem link1878 : linkOK pL1878 pH1878 pI1878 = true := by decide +kernel
theorem cvx1878 : ConvexBetweenHumps 1878 :=
  cvx_of L1878_ok H1878_ok I1878_ok link1878 (by decide)
theorem cenlink1878 : cenLinkOK pI1878 1878 = true := by decide +kernel
theorem cen1878 : CenterUniqueMin 1878 ∧ DipHyp 1878 ∧ OnePointHyps 1878 :=
  cen_of L1878_ok H1878_ok I1878_ok link1878 cenlink1878

/-! ### `N = 1879` -/

def pL1879 : Prm := ⟨80, 37, 40, 1881, 11, 18446744073709551616, 103509162065281390, 103509162065281390⟩
def pH1879 : Prm := ⟨80, 37, 40, 1881, 11, 18446744073709551616, 103510261576909166, 103510261576909166⟩
def pI1879 : Prm := ⟨68, 34, 31, 1881, 11, 18446744073709551616, 103509162065281390, 103510261576909166⟩
noncomputable def L1879_cp1 : Nat × Nat := t7val% (fastRun pL1879 1 1084 (init pL1879) (init pL1879))
theorem L1879_seg1 : segOK pL1879 1 1084 (init pL1879) (init pL1879) L1879_cp1.1 L1879_cp1.2 = true := by
  decide +kernel
noncomputable def L1879_cp2 : Nat × Nat := t7val% (fastRun pL1879 1 1533 (init pL1879) (init pL1879))
theorem L1879_seg2 : segOK pL1879 1085 449 L1879_cp1.1 L1879_cp1.2 L1879_cp2.1 L1879_cp2.2 = true := by
  decide +kernel
theorem L1879_fin : (prmOK pL1879 1879 && ptTest pL1879 (runFrom pL1879 (fmask pL1879) (cmask pL1879) (hmask pL1879) 1534 345 (true, L1879_cp2.1, L1879_cp2.2)) 1879 940 false) = true := by
  decide +kernel
theorem L1879_ok : RunOK pL1879 1879 (runFrom pL1879 (fmask pL1879) (cmask pL1879) (hmask pL1879) 1534 345 (true, L1879_cp2.1, L1879_cp2.2)) ∧ ptTest pL1879 (runFrom pL1879 (fmask pL1879) (cmask pL1879) (hmask pL1879) 1534 345 (true, L1879_cp2.1, L1879_cp2.2)) 1879 940 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1879_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1879_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1879_fin) true) L1879_seg1) L1879_seg2) (by decide) rfl L1879_fin ptTest_fst
noncomputable def H1879_cp1 : Nat × Nat := t7val% (fastRun pH1879 1 1084 (init pH1879) (init pH1879))
theorem H1879_seg1 : segOK pH1879 1 1084 (init pH1879) (init pH1879) H1879_cp1.1 H1879_cp1.2 = true := by
  decide +kernel
noncomputable def H1879_cp2 : Nat × Nat := t7val% (fastRun pH1879 1 1533 (init pH1879) (init pH1879))
theorem H1879_seg2 : segOK pH1879 1085 449 H1879_cp1.1 H1879_cp1.2 H1879_cp2.1 H1879_cp2.2 = true := by
  decide +kernel
theorem H1879_fin : (prmOK pH1879 1879 && ptTest pH1879 (runFrom pH1879 (fmask pH1879) (cmask pH1879) (hmask pH1879) 1534 345 (true, H1879_cp2.1, H1879_cp2.2)) 1879 940 true) = true := by
  decide +kernel
theorem H1879_ok : RunOK pH1879 1879 (runFrom pH1879 (fmask pH1879) (cmask pH1879) (hmask pH1879) 1534 345 (true, H1879_cp2.1, H1879_cp2.2)) ∧ ptTest pH1879 (runFrom pH1879 (fmask pH1879) (cmask pH1879) (hmask pH1879) 1534 345 (true, H1879_cp2.1, H1879_cp2.2)) 1879 940 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1879_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1879_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1879_fin) true) H1879_seg1) H1879_seg2) (by decide) rfl H1879_fin ptTest_fst
noncomputable def I1879_cp1 : Nat × Nat := t7val% (fastRun pI1879 1 1084 (init pI1879) (init pI1879))
theorem I1879_seg1 : segOK pI1879 1 1084 (init pI1879) (init pI1879) I1879_cp1.1 I1879_cp1.2 = true := by
  decide +kernel
noncomputable def I1879_cp2 : Nat × Nat := t7val% (fastRun pI1879 1 1533 (init pI1879) (init pI1879))
theorem I1879_seg2 : segOK pI1879 1085 449 I1879_cp1.1 I1879_cp1.2 I1879_cp2.1 I1879_cp2.2 = true := by
  decide +kernel
theorem I1879_fin : (prmOK pI1879 1879 && intTest pI1879 (runFrom pI1879 (fmask pI1879) (cmask pI1879) (hmask pI1879) 1534 345 (true, I1879_cp2.1, I1879_cp2.2)) 1879 21 false) = true := by
  decide +kernel
theorem I1879_ok : RunOK pI1879 1879 (runFrom pI1879 (fmask pI1879) (cmask pI1879) (hmask pI1879) 1534 345 (true, I1879_cp2.1, I1879_cp2.2)) ∧ intTest pI1879 (runFrom pI1879 (fmask pI1879) (cmask pI1879) (hmask pI1879) 1534 345 (true, I1879_cp2.1, I1879_cp2.2)) 1879 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1879_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1879_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1879_fin) true) I1879_seg1) I1879_seg2) (by decide) rfl I1879_fin intTest_fst
theorem link1879 : linkOK pL1879 pH1879 pI1879 = true := by decide +kernel
theorem cvx1879 : ConvexBetweenHumps 1879 :=
  cvx_of L1879_ok H1879_ok I1879_ok link1879 (by decide)

/-! ### `N = 1880` -/

def pL1880 : Prm := ⟨80, 37, 40, 1882, 11, 18446744073709551616, 103463952869742118, 103463952869742118⟩
def pH1880 : Prm := ⟨80, 37, 40, 1882, 11, 18446744073709551616, 103465052381369894, 103465052381369894⟩
def pI1880 : Prm := ⟨68, 34, 31, 1882, 11, 18446744073709551616, 103463952869742118, 103465052381369894⟩
noncomputable def L1880_cp1 : Nat × Nat := t7val% (fastRun pL1880 1 1084 (init pL1880) (init pL1880))
theorem L1880_seg1 : segOK pL1880 1 1084 (init pL1880) (init pL1880) L1880_cp1.1 L1880_cp1.2 = true := by
  decide +kernel
noncomputable def L1880_cp2 : Nat × Nat := t7val% (fastRun pL1880 1 1534 (init pL1880) (init pL1880))
theorem L1880_seg2 : segOK pL1880 1085 450 L1880_cp1.1 L1880_cp1.2 L1880_cp2.1 L1880_cp2.2 = true := by
  decide +kernel
theorem L1880_fin : (prmOK pL1880 1880 && ptTest pL1880 (runFrom pL1880 (fmask pL1880) (cmask pL1880) (hmask pL1880) 1535 345 (true, L1880_cp2.1, L1880_cp2.2)) 1880 940 false) = true := by
  decide +kernel
theorem L1880_ok : RunOK pL1880 1880 (runFrom pL1880 (fmask pL1880) (cmask pL1880) (hmask pL1880) 1535 345 (true, L1880_cp2.1, L1880_cp2.2)) ∧ ptTest pL1880 (runFrom pL1880 (fmask pL1880) (cmask pL1880) (hmask pL1880) 1535 345 (true, L1880_cp2.1, L1880_cp2.2)) 1880 940 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1880_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1880_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1880_fin) true) L1880_seg1) L1880_seg2) (by decide) rfl L1880_fin ptTest_fst
noncomputable def H1880_cp1 : Nat × Nat := t7val% (fastRun pH1880 1 1084 (init pH1880) (init pH1880))
theorem H1880_seg1 : segOK pH1880 1 1084 (init pH1880) (init pH1880) H1880_cp1.1 H1880_cp1.2 = true := by
  decide +kernel
noncomputable def H1880_cp2 : Nat × Nat := t7val% (fastRun pH1880 1 1534 (init pH1880) (init pH1880))
theorem H1880_seg2 : segOK pH1880 1085 450 H1880_cp1.1 H1880_cp1.2 H1880_cp2.1 H1880_cp2.2 = true := by
  decide +kernel
theorem H1880_fin : (prmOK pH1880 1880 && ptTest pH1880 (runFrom pH1880 (fmask pH1880) (cmask pH1880) (hmask pH1880) 1535 345 (true, H1880_cp2.1, H1880_cp2.2)) 1880 940 true) = true := by
  decide +kernel
theorem H1880_ok : RunOK pH1880 1880 (runFrom pH1880 (fmask pH1880) (cmask pH1880) (hmask pH1880) 1535 345 (true, H1880_cp2.1, H1880_cp2.2)) ∧ ptTest pH1880 (runFrom pH1880 (fmask pH1880) (cmask pH1880) (hmask pH1880) 1535 345 (true, H1880_cp2.1, H1880_cp2.2)) 1880 940 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1880_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1880_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1880_fin) true) H1880_seg1) H1880_seg2) (by decide) rfl H1880_fin ptTest_fst
noncomputable def I1880_cp1 : Nat × Nat := t7val% (fastRun pI1880 1 1084 (init pI1880) (init pI1880))
theorem I1880_seg1 : segOK pI1880 1 1084 (init pI1880) (init pI1880) I1880_cp1.1 I1880_cp1.2 = true := by
  decide +kernel
noncomputable def I1880_cp2 : Nat × Nat := t7val% (fastRun pI1880 1 1534 (init pI1880) (init pI1880))
theorem I1880_seg2 : segOK pI1880 1085 450 I1880_cp1.1 I1880_cp1.2 I1880_cp2.1 I1880_cp2.2 = true := by
  decide +kernel
theorem I1880_fin : (prmOK pI1880 1880 && intTest pI1880 (runFrom pI1880 (fmask pI1880) (cmask pI1880) (hmask pI1880) 1535 345 (true, I1880_cp2.1, I1880_cp2.2)) 1880 21 true) = true := by
  decide +kernel
theorem I1880_ok : RunOK pI1880 1880 (runFrom pI1880 (fmask pI1880) (cmask pI1880) (hmask pI1880) 1535 345 (true, I1880_cp2.1, I1880_cp2.2)) ∧ intTest pI1880 (runFrom pI1880 (fmask pI1880) (cmask pI1880) (hmask pI1880) 1535 345 (true, I1880_cp2.1, I1880_cp2.2)) 1880 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1880_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1880_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1880_fin) true) I1880_seg1) I1880_seg2) (by decide) rfl I1880_fin intTest_fst
theorem link1880 : linkOK pL1880 pH1880 pI1880 = true := by decide +kernel
theorem cvx1880 : ConvexBetweenHumps 1880 :=
  cvx_of L1880_ok H1880_ok I1880_ok link1880 (by decide)
theorem cenlink1880 : cenLinkOK pI1880 1880 = true := by decide +kernel
theorem cen1880 : CenterUniqueMin 1880 ∧ DipHyp 1880 ∧ OnePointHyps 1880 :=
  cen_of L1880_ok H1880_ok I1880_ok link1880 cenlink1880

/-! ### `N = 1881` -/

def pL1881 : Prm := ⟨80, 37, 40, 1883, 11, 18446744073709551616, 103418769657271978, 103418769657271978⟩
def pH1881 : Prm := ⟨80, 37, 40, 1883, 11, 18446744073709551616, 103419869168899754, 103419869168899754⟩
def pI1881 : Prm := ⟨68, 34, 31, 1883, 11, 18446744073709551616, 103418769657271978, 103419869168899754⟩
noncomputable def L1881_cp1 : Nat × Nat := t7val% (fastRun pL1881 1 1085 (init pL1881) (init pL1881))
theorem L1881_seg1 : segOK pL1881 1 1085 (init pL1881) (init pL1881) L1881_cp1.1 L1881_cp1.2 = true := by
  decide +kernel
noncomputable def L1881_cp2 : Nat × Nat := t7val% (fastRun pL1881 1 1535 (init pL1881) (init pL1881))
theorem L1881_seg2 : segOK pL1881 1086 450 L1881_cp1.1 L1881_cp1.2 L1881_cp2.1 L1881_cp2.2 = true := by
  decide +kernel
theorem L1881_fin : (prmOK pL1881 1881 && ptTest pL1881 (runFrom pL1881 (fmask pL1881) (cmask pL1881) (hmask pL1881) 1536 345 (true, L1881_cp2.1, L1881_cp2.2)) 1881 941 false) = true := by
  decide +kernel
theorem L1881_ok : RunOK pL1881 1881 (runFrom pL1881 (fmask pL1881) (cmask pL1881) (hmask pL1881) 1536 345 (true, L1881_cp2.1, L1881_cp2.2)) ∧ ptTest pL1881 (runFrom pL1881 (fmask pL1881) (cmask pL1881) (hmask pL1881) 1536 345 (true, L1881_cp2.1, L1881_cp2.2)) 1881 941 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1881_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1881_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1881_fin) true) L1881_seg1) L1881_seg2) (by decide) rfl L1881_fin ptTest_fst
noncomputable def H1881_cp1 : Nat × Nat := t7val% (fastRun pH1881 1 1085 (init pH1881) (init pH1881))
theorem H1881_seg1 : segOK pH1881 1 1085 (init pH1881) (init pH1881) H1881_cp1.1 H1881_cp1.2 = true := by
  decide +kernel
noncomputable def H1881_cp2 : Nat × Nat := t7val% (fastRun pH1881 1 1535 (init pH1881) (init pH1881))
theorem H1881_seg2 : segOK pH1881 1086 450 H1881_cp1.1 H1881_cp1.2 H1881_cp2.1 H1881_cp2.2 = true := by
  decide +kernel
theorem H1881_fin : (prmOK pH1881 1881 && ptTest pH1881 (runFrom pH1881 (fmask pH1881) (cmask pH1881) (hmask pH1881) 1536 345 (true, H1881_cp2.1, H1881_cp2.2)) 1881 941 true) = true := by
  decide +kernel
theorem H1881_ok : RunOK pH1881 1881 (runFrom pH1881 (fmask pH1881) (cmask pH1881) (hmask pH1881) 1536 345 (true, H1881_cp2.1, H1881_cp2.2)) ∧ ptTest pH1881 (runFrom pH1881 (fmask pH1881) (cmask pH1881) (hmask pH1881) 1536 345 (true, H1881_cp2.1, H1881_cp2.2)) 1881 941 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1881_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1881_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1881_fin) true) H1881_seg1) H1881_seg2) (by decide) rfl H1881_fin ptTest_fst
noncomputable def I1881_cp1 : Nat × Nat := t7val% (fastRun pI1881 1 1085 (init pI1881) (init pI1881))
theorem I1881_seg1 : segOK pI1881 1 1085 (init pI1881) (init pI1881) I1881_cp1.1 I1881_cp1.2 = true := by
  decide +kernel
noncomputable def I1881_cp2 : Nat × Nat := t7val% (fastRun pI1881 1 1535 (init pI1881) (init pI1881))
theorem I1881_seg2 : segOK pI1881 1086 450 I1881_cp1.1 I1881_cp1.2 I1881_cp2.1 I1881_cp2.2 = true := by
  decide +kernel
theorem I1881_fin : (prmOK pI1881 1881 && intTest pI1881 (runFrom pI1881 (fmask pI1881) (cmask pI1881) (hmask pI1881) 1536 345 (true, I1881_cp2.1, I1881_cp2.2)) 1881 21 false) = true := by
  decide +kernel
theorem I1881_ok : RunOK pI1881 1881 (runFrom pI1881 (fmask pI1881) (cmask pI1881) (hmask pI1881) 1536 345 (true, I1881_cp2.1, I1881_cp2.2)) ∧ intTest pI1881 (runFrom pI1881 (fmask pI1881) (cmask pI1881) (hmask pI1881) 1536 345 (true, I1881_cp2.1, I1881_cp2.2)) 1881 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1881_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1881_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1881_fin) true) I1881_seg1) I1881_seg2) (by decide) rfl I1881_fin intTest_fst
theorem link1881 : linkOK pL1881 pH1881 pI1881 = true := by decide +kernel
theorem cvx1881 : ConvexBetweenHumps 1881 :=
  cvx_of L1881_ok H1881_ok I1881_ok link1881 (by decide)

/-! ### `N = 1882` -/

def pL1882 : Prm := ⟨80, 37, 40, 1884, 11, 18446744073709551616, 103373646053647531, 103373646053647531⟩
def pH1882 : Prm := ⟨80, 37, 40, 1884, 11, 18446744073709551616, 103374745565275307, 103374745565275307⟩
def pI1882 : Prm := ⟨68, 34, 31, 1884, 11, 18446744073709551616, 103373646053647531, 103374745565275307⟩
noncomputable def L1882_cp1 : Nat × Nat := t7val% (fastRun pL1882 1 1086 (init pL1882) (init pL1882))
theorem L1882_seg1 : segOK pL1882 1 1086 (init pL1882) (init pL1882) L1882_cp1.1 L1882_cp1.2 = true := by
  decide +kernel
noncomputable def L1882_cp2 : Nat × Nat := t7val% (fastRun pL1882 1 1536 (init pL1882) (init pL1882))
theorem L1882_seg2 : segOK pL1882 1087 450 L1882_cp1.1 L1882_cp1.2 L1882_cp2.1 L1882_cp2.2 = true := by
  decide +kernel
theorem L1882_fin : (prmOK pL1882 1882 && ptTest pL1882 (runFrom pL1882 (fmask pL1882) (cmask pL1882) (hmask pL1882) 1537 345 (true, L1882_cp2.1, L1882_cp2.2)) 1882 941 false) = true := by
  decide +kernel
theorem L1882_ok : RunOK pL1882 1882 (runFrom pL1882 (fmask pL1882) (cmask pL1882) (hmask pL1882) 1537 345 (true, L1882_cp2.1, L1882_cp2.2)) ∧ ptTest pL1882 (runFrom pL1882 (fmask pL1882) (cmask pL1882) (hmask pL1882) 1537 345 (true, L1882_cp2.1, L1882_cp2.2)) 1882 941 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1882_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1882_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1882_fin) true) L1882_seg1) L1882_seg2) (by decide) rfl L1882_fin ptTest_fst
noncomputable def H1882_cp1 : Nat × Nat := t7val% (fastRun pH1882 1 1086 (init pH1882) (init pH1882))
theorem H1882_seg1 : segOK pH1882 1 1086 (init pH1882) (init pH1882) H1882_cp1.1 H1882_cp1.2 = true := by
  decide +kernel
noncomputable def H1882_cp2 : Nat × Nat := t7val% (fastRun pH1882 1 1536 (init pH1882) (init pH1882))
theorem H1882_seg2 : segOK pH1882 1087 450 H1882_cp1.1 H1882_cp1.2 H1882_cp2.1 H1882_cp2.2 = true := by
  decide +kernel
theorem H1882_fin : (prmOK pH1882 1882 && ptTest pH1882 (runFrom pH1882 (fmask pH1882) (cmask pH1882) (hmask pH1882) 1537 345 (true, H1882_cp2.1, H1882_cp2.2)) 1882 941 true) = true := by
  decide +kernel
theorem H1882_ok : RunOK pH1882 1882 (runFrom pH1882 (fmask pH1882) (cmask pH1882) (hmask pH1882) 1537 345 (true, H1882_cp2.1, H1882_cp2.2)) ∧ ptTest pH1882 (runFrom pH1882 (fmask pH1882) (cmask pH1882) (hmask pH1882) 1537 345 (true, H1882_cp2.1, H1882_cp2.2)) 1882 941 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1882_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1882_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1882_fin) true) H1882_seg1) H1882_seg2) (by decide) rfl H1882_fin ptTest_fst
noncomputable def I1882_cp1 : Nat × Nat := t7val% (fastRun pI1882 1 1086 (init pI1882) (init pI1882))
theorem I1882_seg1 : segOK pI1882 1 1086 (init pI1882) (init pI1882) I1882_cp1.1 I1882_cp1.2 = true := by
  decide +kernel
noncomputable def I1882_cp2 : Nat × Nat := t7val% (fastRun pI1882 1 1536 (init pI1882) (init pI1882))
theorem I1882_seg2 : segOK pI1882 1087 450 I1882_cp1.1 I1882_cp1.2 I1882_cp2.1 I1882_cp2.2 = true := by
  decide +kernel
theorem I1882_fin : (prmOK pI1882 1882 && intTest pI1882 (runFrom pI1882 (fmask pI1882) (cmask pI1882) (hmask pI1882) 1537 345 (true, I1882_cp2.1, I1882_cp2.2)) 1882 21 true) = true := by
  decide +kernel
theorem I1882_ok : RunOK pI1882 1882 (runFrom pI1882 (fmask pI1882) (cmask pI1882) (hmask pI1882) 1537 345 (true, I1882_cp2.1, I1882_cp2.2)) ∧ intTest pI1882 (runFrom pI1882 (fmask pI1882) (cmask pI1882) (hmask pI1882) 1537 345 (true, I1882_cp2.1, I1882_cp2.2)) 1882 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1882_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1882_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1882_fin) true) I1882_seg1) I1882_seg2) (by decide) rfl I1882_fin intTest_fst
theorem link1882 : linkOK pL1882 pH1882 pI1882 = true := by decide +kernel
theorem cvx1882 : ConvexBetweenHumps 1882 :=
  cvx_of L1882_ok H1882_ok I1882_ok link1882 (by decide)
theorem cenlink1882 : cenLinkOK pI1882 1882 = true := by decide +kernel
theorem cen1882 : CenterUniqueMin 1882 ∧ DipHyp 1882 ∧ OnePointHyps 1882 :=
  cen_of L1882_ok H1882_ok I1882_ok link1882 cenlink1882

/-! ### `N = 1883` -/

def pL1883 : Prm := ⟨80, 37, 40, 1885, 11, 18446744073709551616, 103328548362275165, 103328548362275165⟩
def pH1883 : Prm := ⟨80, 37, 40, 1885, 11, 18446744073709551616, 103329647873902941, 103329647873902941⟩
def pI1883 : Prm := ⟨68, 34, 31, 1885, 11, 18446744073709551616, 103328548362275165, 103329647873902941⟩
noncomputable def L1883_cp1 : Nat × Nat := t7val% (fastRun pL1883 1 1086 (init pL1883) (init pL1883))
theorem L1883_seg1 : segOK pL1883 1 1086 (init pL1883) (init pL1883) L1883_cp1.1 L1883_cp1.2 = true := by
  decide +kernel
noncomputable def L1883_cp2 : Nat × Nat := t7val% (fastRun pL1883 1 1536 (init pL1883) (init pL1883))
theorem L1883_seg2 : segOK pL1883 1087 450 L1883_cp1.1 L1883_cp1.2 L1883_cp2.1 L1883_cp2.2 = true := by
  decide +kernel
theorem L1883_fin : (prmOK pL1883 1883 && ptTest pL1883 (runFrom pL1883 (fmask pL1883) (cmask pL1883) (hmask pL1883) 1537 346 (true, L1883_cp2.1, L1883_cp2.2)) 1883 942 false) = true := by
  decide +kernel
theorem L1883_ok : RunOK pL1883 1883 (runFrom pL1883 (fmask pL1883) (cmask pL1883) (hmask pL1883) 1537 346 (true, L1883_cp2.1, L1883_cp2.2)) ∧ ptTest pL1883 (runFrom pL1883 (fmask pL1883) (cmask pL1883) (hmask pL1883) 1537 346 (true, L1883_cp2.1, L1883_cp2.2)) 1883 942 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1883_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1883_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1883_fin) true) L1883_seg1) L1883_seg2) (by decide) rfl L1883_fin ptTest_fst
noncomputable def H1883_cp1 : Nat × Nat := t7val% (fastRun pH1883 1 1086 (init pH1883) (init pH1883))
theorem H1883_seg1 : segOK pH1883 1 1086 (init pH1883) (init pH1883) H1883_cp1.1 H1883_cp1.2 = true := by
  decide +kernel
noncomputable def H1883_cp2 : Nat × Nat := t7val% (fastRun pH1883 1 1536 (init pH1883) (init pH1883))
theorem H1883_seg2 : segOK pH1883 1087 450 H1883_cp1.1 H1883_cp1.2 H1883_cp2.1 H1883_cp2.2 = true := by
  decide +kernel
theorem H1883_fin : (prmOK pH1883 1883 && ptTest pH1883 (runFrom pH1883 (fmask pH1883) (cmask pH1883) (hmask pH1883) 1537 346 (true, H1883_cp2.1, H1883_cp2.2)) 1883 942 true) = true := by
  decide +kernel
theorem H1883_ok : RunOK pH1883 1883 (runFrom pH1883 (fmask pH1883) (cmask pH1883) (hmask pH1883) 1537 346 (true, H1883_cp2.1, H1883_cp2.2)) ∧ ptTest pH1883 (runFrom pH1883 (fmask pH1883) (cmask pH1883) (hmask pH1883) 1537 346 (true, H1883_cp2.1, H1883_cp2.2)) 1883 942 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1883_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1883_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1883_fin) true) H1883_seg1) H1883_seg2) (by decide) rfl H1883_fin ptTest_fst
noncomputable def I1883_cp1 : Nat × Nat := t7val% (fastRun pI1883 1 1086 (init pI1883) (init pI1883))
theorem I1883_seg1 : segOK pI1883 1 1086 (init pI1883) (init pI1883) I1883_cp1.1 I1883_cp1.2 = true := by
  decide +kernel
noncomputable def I1883_cp2 : Nat × Nat := t7val% (fastRun pI1883 1 1536 (init pI1883) (init pI1883))
theorem I1883_seg2 : segOK pI1883 1087 450 I1883_cp1.1 I1883_cp1.2 I1883_cp2.1 I1883_cp2.2 = true := by
  decide +kernel
theorem I1883_fin : (prmOK pI1883 1883 && intTest pI1883 (runFrom pI1883 (fmask pI1883) (cmask pI1883) (hmask pI1883) 1537 346 (true, I1883_cp2.1, I1883_cp2.2)) 1883 21 false) = true := by
  decide +kernel
theorem I1883_ok : RunOK pI1883 1883 (runFrom pI1883 (fmask pI1883) (cmask pI1883) (hmask pI1883) 1537 346 (true, I1883_cp2.1, I1883_cp2.2)) ∧ intTest pI1883 (runFrom pI1883 (fmask pI1883) (cmask pI1883) (hmask pI1883) 1537 346 (true, I1883_cp2.1, I1883_cp2.2)) 1883 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1883_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1883_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1883_fin) true) I1883_seg1) I1883_seg2) (by decide) rfl I1883_fin intTest_fst
theorem link1883 : linkOK pL1883 pH1883 pI1883 = true := by decide +kernel
theorem cvx1883 : ConvexBetweenHumps 1883 :=
  cvx_of L1883_ok H1883_ok I1883_ok link1883 (by decide)

/-! ### `N = 1884` -/

def pL1884 : Prm := ⟨80, 37, 40, 1886, 11, 18446744073709551616, 103283510100280120, 103283510100280120⟩
def pH1884 : Prm := ⟨80, 37, 40, 1886, 11, 18446744073709551616, 103284609611907896, 103284609611907896⟩
def pI1884 : Prm := ⟨68, 34, 31, 1886, 11, 18446744073709551616, 103283510100280120, 103284609611907896⟩
noncomputable def L1884_cp1 : Nat × Nat := t7val% (fastRun pL1884 1 1087 (init pL1884) (init pL1884))
theorem L1884_seg1 : segOK pL1884 1 1087 (init pL1884) (init pL1884) L1884_cp1.1 L1884_cp1.2 = true := by
  decide +kernel
noncomputable def L1884_cp2 : Nat × Nat := t7val% (fastRun pL1884 1 1537 (init pL1884) (init pL1884))
theorem L1884_seg2 : segOK pL1884 1088 450 L1884_cp1.1 L1884_cp1.2 L1884_cp2.1 L1884_cp2.2 = true := by
  decide +kernel
theorem L1884_fin : (prmOK pL1884 1884 && ptTest pL1884 (runFrom pL1884 (fmask pL1884) (cmask pL1884) (hmask pL1884) 1538 346 (true, L1884_cp2.1, L1884_cp2.2)) 1884 942 false) = true := by
  decide +kernel
theorem L1884_ok : RunOK pL1884 1884 (runFrom pL1884 (fmask pL1884) (cmask pL1884) (hmask pL1884) 1538 346 (true, L1884_cp2.1, L1884_cp2.2)) ∧ ptTest pL1884 (runFrom pL1884 (fmask pL1884) (cmask pL1884) (hmask pL1884) 1538 346 (true, L1884_cp2.1, L1884_cp2.2)) 1884 942 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1884_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1884_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1884_fin) true) L1884_seg1) L1884_seg2) (by decide) rfl L1884_fin ptTest_fst
noncomputable def H1884_cp1 : Nat × Nat := t7val% (fastRun pH1884 1 1087 (init pH1884) (init pH1884))
theorem H1884_seg1 : segOK pH1884 1 1087 (init pH1884) (init pH1884) H1884_cp1.1 H1884_cp1.2 = true := by
  decide +kernel
noncomputable def H1884_cp2 : Nat × Nat := t7val% (fastRun pH1884 1 1537 (init pH1884) (init pH1884))
theorem H1884_seg2 : segOK pH1884 1088 450 H1884_cp1.1 H1884_cp1.2 H1884_cp2.1 H1884_cp2.2 = true := by
  decide +kernel
theorem H1884_fin : (prmOK pH1884 1884 && ptTest pH1884 (runFrom pH1884 (fmask pH1884) (cmask pH1884) (hmask pH1884) 1538 346 (true, H1884_cp2.1, H1884_cp2.2)) 1884 942 true) = true := by
  decide +kernel
theorem H1884_ok : RunOK pH1884 1884 (runFrom pH1884 (fmask pH1884) (cmask pH1884) (hmask pH1884) 1538 346 (true, H1884_cp2.1, H1884_cp2.2)) ∧ ptTest pH1884 (runFrom pH1884 (fmask pH1884) (cmask pH1884) (hmask pH1884) 1538 346 (true, H1884_cp2.1, H1884_cp2.2)) 1884 942 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1884_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1884_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1884_fin) true) H1884_seg1) H1884_seg2) (by decide) rfl H1884_fin ptTest_fst
noncomputable def I1884_cp1 : Nat × Nat := t7val% (fastRun pI1884 1 1087 (init pI1884) (init pI1884))
theorem I1884_seg1 : segOK pI1884 1 1087 (init pI1884) (init pI1884) I1884_cp1.1 I1884_cp1.2 = true := by
  decide +kernel
noncomputable def I1884_cp2 : Nat × Nat := t7val% (fastRun pI1884 1 1537 (init pI1884) (init pI1884))
theorem I1884_seg2 : segOK pI1884 1088 450 I1884_cp1.1 I1884_cp1.2 I1884_cp2.1 I1884_cp2.2 = true := by
  decide +kernel
theorem I1884_fin : (prmOK pI1884 1884 && intTest pI1884 (runFrom pI1884 (fmask pI1884) (cmask pI1884) (hmask pI1884) 1538 346 (true, I1884_cp2.1, I1884_cp2.2)) 1884 21 true) = true := by
  decide +kernel
theorem I1884_ok : RunOK pI1884 1884 (runFrom pI1884 (fmask pI1884) (cmask pI1884) (hmask pI1884) 1538 346 (true, I1884_cp2.1, I1884_cp2.2)) ∧ intTest pI1884 (runFrom pI1884 (fmask pI1884) (cmask pI1884) (hmask pI1884) 1538 346 (true, I1884_cp2.1, I1884_cp2.2)) 1884 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1884_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1884_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1884_fin) true) I1884_seg1) I1884_seg2) (by decide) rfl I1884_fin intTest_fst
theorem link1884 : linkOK pL1884 pH1884 pI1884 = true := by decide +kernel
theorem cvx1884 : ConvexBetweenHumps 1884 :=
  cvx_of L1884_ok H1884_ok I1884_ok link1884 (by decide)
theorem cenlink1884 : cenLinkOK pI1884 1884 = true := by decide +kernel
theorem cen1884 : CenterUniqueMin 1884 ∧ DipHyp 1884 ∧ OnePointHyps 1884 :=
  cen_of L1884_ok H1884_ok I1884_ok link1884 cenlink1884

/-! ### `N = 1885` -/

def pL1885 : Prm := ⟨80, 37, 40, 1887, 11, 18446744073709551616, 103238497679959912, 103238497679959912⟩
def pH1885 : Prm := ⟨80, 37, 40, 1887, 11, 18446744073709551616, 103239597191587688, 103239597191587688⟩
def pI1885 : Prm := ⟨68, 34, 31, 1887, 11, 18446744073709551616, 103238497679959912, 103239597191587688⟩
noncomputable def L1885_cp1 : Nat × Nat := t7val% (fastRun pL1885 1 1087 (init pL1885) (init pL1885))
theorem L1885_seg1 : segOK pL1885 1 1087 (init pL1885) (init pL1885) L1885_cp1.1 L1885_cp1.2 = true := by
  decide +kernel
noncomputable def L1885_cp2 : Nat × Nat := t7val% (fastRun pL1885 1 1538 (init pL1885) (init pL1885))
theorem L1885_seg2 : segOK pL1885 1088 451 L1885_cp1.1 L1885_cp1.2 L1885_cp2.1 L1885_cp2.2 = true := by
  decide +kernel
theorem L1885_fin : (prmOK pL1885 1885 && ptTest pL1885 (runFrom pL1885 (fmask pL1885) (cmask pL1885) (hmask pL1885) 1539 346 (true, L1885_cp2.1, L1885_cp2.2)) 1885 943 false) = true := by
  decide +kernel
theorem L1885_ok : RunOK pL1885 1885 (runFrom pL1885 (fmask pL1885) (cmask pL1885) (hmask pL1885) 1539 346 (true, L1885_cp2.1, L1885_cp2.2)) ∧ ptTest pL1885 (runFrom pL1885 (fmask pL1885) (cmask pL1885) (hmask pL1885) 1539 346 (true, L1885_cp2.1, L1885_cp2.2)) 1885 943 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1885_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1885_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1885_fin) true) L1885_seg1) L1885_seg2) (by decide) rfl L1885_fin ptTest_fst
noncomputable def H1885_cp1 : Nat × Nat := t7val% (fastRun pH1885 1 1087 (init pH1885) (init pH1885))
theorem H1885_seg1 : segOK pH1885 1 1087 (init pH1885) (init pH1885) H1885_cp1.1 H1885_cp1.2 = true := by
  decide +kernel
noncomputable def H1885_cp2 : Nat × Nat := t7val% (fastRun pH1885 1 1538 (init pH1885) (init pH1885))
theorem H1885_seg2 : segOK pH1885 1088 451 H1885_cp1.1 H1885_cp1.2 H1885_cp2.1 H1885_cp2.2 = true := by
  decide +kernel
theorem H1885_fin : (prmOK pH1885 1885 && ptTest pH1885 (runFrom pH1885 (fmask pH1885) (cmask pH1885) (hmask pH1885) 1539 346 (true, H1885_cp2.1, H1885_cp2.2)) 1885 943 true) = true := by
  decide +kernel
theorem H1885_ok : RunOK pH1885 1885 (runFrom pH1885 (fmask pH1885) (cmask pH1885) (hmask pH1885) 1539 346 (true, H1885_cp2.1, H1885_cp2.2)) ∧ ptTest pH1885 (runFrom pH1885 (fmask pH1885) (cmask pH1885) (hmask pH1885) 1539 346 (true, H1885_cp2.1, H1885_cp2.2)) 1885 943 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1885_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1885_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1885_fin) true) H1885_seg1) H1885_seg2) (by decide) rfl H1885_fin ptTest_fst
noncomputable def I1885_cp1 : Nat × Nat := t7val% (fastRun pI1885 1 1087 (init pI1885) (init pI1885))
theorem I1885_seg1 : segOK pI1885 1 1087 (init pI1885) (init pI1885) I1885_cp1.1 I1885_cp1.2 = true := by
  decide +kernel
noncomputable def I1885_cp2 : Nat × Nat := t7val% (fastRun pI1885 1 1538 (init pI1885) (init pI1885))
theorem I1885_seg2 : segOK pI1885 1088 451 I1885_cp1.1 I1885_cp1.2 I1885_cp2.1 I1885_cp2.2 = true := by
  decide +kernel
theorem I1885_fin : (prmOK pI1885 1885 && intTest pI1885 (runFrom pI1885 (fmask pI1885) (cmask pI1885) (hmask pI1885) 1539 346 (true, I1885_cp2.1, I1885_cp2.2)) 1885 21 false) = true := by
  decide +kernel
theorem I1885_ok : RunOK pI1885 1885 (runFrom pI1885 (fmask pI1885) (cmask pI1885) (hmask pI1885) 1539 346 (true, I1885_cp2.1, I1885_cp2.2)) ∧ intTest pI1885 (runFrom pI1885 (fmask pI1885) (cmask pI1885) (hmask pI1885) 1539 346 (true, I1885_cp2.1, I1885_cp2.2)) 1885 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1885_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1885_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1885_fin) true) I1885_seg1) I1885_seg2) (by decide) rfl I1885_fin intTest_fst
theorem link1885 : linkOK pL1885 pH1885 pI1885 = true := by decide +kernel
theorem cvx1885 : ConvexBetweenHumps 1885 :=
  cvx_of L1885_ok H1885_ok I1885_ok link1885 (by decide)

/-! ### `N = 1886` -/

def pL1886 : Prm := ⟨80, 37, 40, 1888, 11, 18446744073709551616, 103193544510341861, 103193544510341861⟩
def pH1886 : Prm := ⟨80, 37, 40, 1888, 11, 18446744073709551616, 103194644021969637, 103194644021969637⟩
def pI1886 : Prm := ⟨68, 34, 31, 1888, 11, 18446744073709551616, 103193544510341861, 103194644021969637⟩
noncomputable def L1886_cp1 : Nat × Nat := t7val% (fastRun pL1886 1 1088 (init pL1886) (init pL1886))
theorem L1886_seg1 : segOK pL1886 1 1088 (init pL1886) (init pL1886) L1886_cp1.1 L1886_cp1.2 = true := by
  decide +kernel
noncomputable def L1886_cp2 : Nat × Nat := t7val% (fastRun pL1886 1 1539 (init pL1886) (init pL1886))
theorem L1886_seg2 : segOK pL1886 1089 451 L1886_cp1.1 L1886_cp1.2 L1886_cp2.1 L1886_cp2.2 = true := by
  decide +kernel
theorem L1886_fin : (prmOK pL1886 1886 && ptTest pL1886 (runFrom pL1886 (fmask pL1886) (cmask pL1886) (hmask pL1886) 1540 346 (true, L1886_cp2.1, L1886_cp2.2)) 1886 943 false) = true := by
  decide +kernel
theorem L1886_ok : RunOK pL1886 1886 (runFrom pL1886 (fmask pL1886) (cmask pL1886) (hmask pL1886) 1540 346 (true, L1886_cp2.1, L1886_cp2.2)) ∧ ptTest pL1886 (runFrom pL1886 (fmask pL1886) (cmask pL1886) (hmask pL1886) 1540 346 (true, L1886_cp2.1, L1886_cp2.2)) 1886 943 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1886_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1886_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1886_fin) true) L1886_seg1) L1886_seg2) (by decide) rfl L1886_fin ptTest_fst
noncomputable def H1886_cp1 : Nat × Nat := t7val% (fastRun pH1886 1 1088 (init pH1886) (init pH1886))
theorem H1886_seg1 : segOK pH1886 1 1088 (init pH1886) (init pH1886) H1886_cp1.1 H1886_cp1.2 = true := by
  decide +kernel
noncomputable def H1886_cp2 : Nat × Nat := t7val% (fastRun pH1886 1 1539 (init pH1886) (init pH1886))
theorem H1886_seg2 : segOK pH1886 1089 451 H1886_cp1.1 H1886_cp1.2 H1886_cp2.1 H1886_cp2.2 = true := by
  decide +kernel
theorem H1886_fin : (prmOK pH1886 1886 && ptTest pH1886 (runFrom pH1886 (fmask pH1886) (cmask pH1886) (hmask pH1886) 1540 346 (true, H1886_cp2.1, H1886_cp2.2)) 1886 943 true) = true := by
  decide +kernel
theorem H1886_ok : RunOK pH1886 1886 (runFrom pH1886 (fmask pH1886) (cmask pH1886) (hmask pH1886) 1540 346 (true, H1886_cp2.1, H1886_cp2.2)) ∧ ptTest pH1886 (runFrom pH1886 (fmask pH1886) (cmask pH1886) (hmask pH1886) 1540 346 (true, H1886_cp2.1, H1886_cp2.2)) 1886 943 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1886_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1886_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1886_fin) true) H1886_seg1) H1886_seg2) (by decide) rfl H1886_fin ptTest_fst
noncomputable def I1886_cp1 : Nat × Nat := t7val% (fastRun pI1886 1 1088 (init pI1886) (init pI1886))
theorem I1886_seg1 : segOK pI1886 1 1088 (init pI1886) (init pI1886) I1886_cp1.1 I1886_cp1.2 = true := by
  decide +kernel
noncomputable def I1886_cp2 : Nat × Nat := t7val% (fastRun pI1886 1 1539 (init pI1886) (init pI1886))
theorem I1886_seg2 : segOK pI1886 1089 451 I1886_cp1.1 I1886_cp1.2 I1886_cp2.1 I1886_cp2.2 = true := by
  decide +kernel
theorem I1886_fin : (prmOK pI1886 1886 && intTest pI1886 (runFrom pI1886 (fmask pI1886) (cmask pI1886) (hmask pI1886) 1540 346 (true, I1886_cp2.1, I1886_cp2.2)) 1886 21 true) = true := by
  decide +kernel
theorem I1886_ok : RunOK pI1886 1886 (runFrom pI1886 (fmask pI1886) (cmask pI1886) (hmask pI1886) 1540 346 (true, I1886_cp2.1, I1886_cp2.2)) ∧ intTest pI1886 (runFrom pI1886 (fmask pI1886) (cmask pI1886) (hmask pI1886) 1540 346 (true, I1886_cp2.1, I1886_cp2.2)) 1886 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1886_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1886_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1886_fin) true) I1886_seg1) I1886_seg2) (by decide) rfl I1886_fin intTest_fst
theorem link1886 : linkOK pL1886 pH1886 pI1886 = true := by decide +kernel
theorem cvx1886 : ConvexBetweenHumps 1886 :=
  cvx_of L1886_ok H1886_ok I1886_ok link1886 (by decide)
theorem cenlink1886 : cenLinkOK pI1886 1886 = true := by decide +kernel
theorem cen1886 : CenterUniqueMin 1886 ∧ DipHyp 1886 ∧ OnePointHyps 1886 :=
  cen_of L1886_ok H1886_ok I1886_ok link1886 cenlink1886

/-! ### The range -/

theorem cvx_1876_1886 {N : ℕ} (h1 : 1876 ≤ N) (h2 : N ≤ 1886) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1880
  · by_cases h4 : N ≤ 1877
    · by_cases h6 : N ≤ 1876
      · obtain rfl : N = 1876 := by omega
        exact cvx1876
      · obtain rfl : N = 1877 := by omega
        exact cvx1877
    · by_cases h6 : N ≤ 1878
      · obtain rfl : N = 1878 := by omega
        exact cvx1878
      · by_cases h8 : N ≤ 1879
        · obtain rfl : N = 1879 := by omega
          exact cvx1879
        · obtain rfl : N = 1880 := by omega
          exact cvx1880
  · by_cases h4 : N ≤ 1883
    · by_cases h6 : N ≤ 1881
      · obtain rfl : N = 1881 := by omega
        exact cvx1881
      · by_cases h8 : N ≤ 1882
        · obtain rfl : N = 1882 := by omega
          exact cvx1882
        · obtain rfl : N = 1883 := by omega
          exact cvx1883
    · by_cases h6 : N ≤ 1884
      · obtain rfl : N = 1884 := by omega
        exact cvx1884
      · by_cases h8 : N ≤ 1885
        · obtain rfl : N = 1885 := by omega
          exact cvx1885
        · obtain rfl : N = 1886 := by omega
          exact cvx1886

theorem cen_1876_1886 {N : ℕ} (h1 : 1876 ≤ N) (h2 : N ≤ 1886) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1880
  · by_cases h4 : N ≤ 1876
    · obtain rfl : N = 1876 := by omega
      exact cen1876
    · by_cases h6 : N ≤ 1878
      · obtain rfl : N = 1878 := by omega
        exact cen1878
      · obtain rfl : N = 1880 := by omega
        exact cen1880
  · by_cases h4 : N ≤ 1882
    · obtain rfl : N = 1882 := by omega
      exact cen1882
    · by_cases h6 : N ≤ 1884
      · obtain rfl : N = 1884 := by omega
        exact cen1884
      · obtain rfl : N = 1886 := by omega
        exact cen1886

end Kagey131.PaperD.T7
