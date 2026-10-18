import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1747, …, 1759` (generated)

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

/-! ### `N = 1747` -/

def pL1747 : Prm := ⟨80, 37, 40, 1749, 11, 18446744073709551616, 109880305139828544, 109880305139828544⟩
def pH1747 : Prm := ⟨80, 37, 40, 1749, 11, 18446744073709551616, 109881404651456320, 109881404651456320⟩
def pI1747 : Prm := ⟨67, 34, 30, 1749, 11, 18446744073709551616, 109880305139828544, 109881404651456320⟩
noncomputable def L1747_cp1 : Nat × Nat := t7val% (fastRun pL1747 1 1008 (init pL1747) (init pL1747))
theorem L1747_seg1 : segOK pL1747 1 1008 (init pL1747) (init pL1747) L1747_cp1.1 L1747_cp1.2 = true := by
  decide +kernel
noncomputable def L1747_cp2 : Nat × Nat := t7val% (fastRun pL1747 1 1425 (init pL1747) (init pL1747))
theorem L1747_seg2 : segOK pL1747 1009 417 L1747_cp1.1 L1747_cp1.2 L1747_cp2.1 L1747_cp2.2 = true := by
  decide +kernel
theorem L1747_fin : (prmOK pL1747 1747 && ptTest pL1747 (runFrom pL1747 (fmask pL1747) (cmask pL1747) (hmask pL1747) 1426 321 (true, L1747_cp2.1, L1747_cp2.2)) 1747 874 false) = true := by
  decide +kernel
theorem L1747_ok : RunOK pL1747 1747 (runFrom pL1747 (fmask pL1747) (cmask pL1747) (hmask pL1747) 1426 321 (true, L1747_cp2.1, L1747_cp2.2)) ∧ ptTest pL1747 (runFrom pL1747 (fmask pL1747) (cmask pL1747) (hmask pL1747) 1426 321 (true, L1747_cp2.1, L1747_cp2.2)) 1747 874 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1747_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1747_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1747_fin) true) L1747_seg1) L1747_seg2) (by decide) rfl L1747_fin ptTest_fst
noncomputable def H1747_cp1 : Nat × Nat := t7val% (fastRun pH1747 1 1008 (init pH1747) (init pH1747))
theorem H1747_seg1 : segOK pH1747 1 1008 (init pH1747) (init pH1747) H1747_cp1.1 H1747_cp1.2 = true := by
  decide +kernel
noncomputable def H1747_cp2 : Nat × Nat := t7val% (fastRun pH1747 1 1425 (init pH1747) (init pH1747))
theorem H1747_seg2 : segOK pH1747 1009 417 H1747_cp1.1 H1747_cp1.2 H1747_cp2.1 H1747_cp2.2 = true := by
  decide +kernel
theorem H1747_fin : (prmOK pH1747 1747 && ptTest pH1747 (runFrom pH1747 (fmask pH1747) (cmask pH1747) (hmask pH1747) 1426 321 (true, H1747_cp2.1, H1747_cp2.2)) 1747 874 true) = true := by
  decide +kernel
theorem H1747_ok : RunOK pH1747 1747 (runFrom pH1747 (fmask pH1747) (cmask pH1747) (hmask pH1747) 1426 321 (true, H1747_cp2.1, H1747_cp2.2)) ∧ ptTest pH1747 (runFrom pH1747 (fmask pH1747) (cmask pH1747) (hmask pH1747) 1426 321 (true, H1747_cp2.1, H1747_cp2.2)) 1747 874 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1747_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1747_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1747_fin) true) H1747_seg1) H1747_seg2) (by decide) rfl H1747_fin ptTest_fst
noncomputable def I1747_cp1 : Nat × Nat := t7val% (fastRun pI1747 1 1234 (init pI1747) (init pI1747))
theorem I1747_seg1 : segOK pI1747 1 1234 (init pI1747) (init pI1747) I1747_cp1.1 I1747_cp1.2 = true := by
  decide +kernel
theorem I1747_fin : (prmOK pI1747 1747 && intTest pI1747 (runFrom pI1747 (fmask pI1747) (cmask pI1747) (hmask pI1747) 1235 512 (true, I1747_cp1.1, I1747_cp1.2)) 1747 21 false) = true := by
  decide +kernel
theorem I1747_ok : RunOK pI1747 1747 (runFrom pI1747 (fmask pI1747) (cmask pI1747) (hmask pI1747) 1235 512 (true, I1747_cp1.1, I1747_cp1.2)) ∧ intTest pI1747 (runFrom pI1747 (fmask pI1747) (cmask pI1747) (hmask pI1747) 1235 512 (true, I1747_cp1.1, I1747_cp1.2)) 1747 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1747_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1747_fin) true) I1747_seg1) (by decide) rfl I1747_fin intTest_fst
theorem link1747 : linkOK pL1747 pH1747 pI1747 = true := by decide +kernel
theorem cvx1747 : ConvexBetweenHumps 1747 :=
  cvx_of L1747_ok H1747_ok I1747_ok link1747 (by decide)

/-! ### `N = 1748` -/

def pL1748 : Prm := ⟨80, 37, 40, 1750, 11, 18446744073709551616, 109828839196265563, 109828839196265563⟩
def pH1748 : Prm := ⟨80, 37, 40, 1750, 11, 18446744073709551616, 109829938707893339, 109829938707893339⟩
def pI1748 : Prm := ⟨67, 34, 30, 1750, 11, 18446744073709551616, 109828839196265563, 109829938707893339⟩
noncomputable def L1748_cp1 : Nat × Nat := t7val% (fastRun pL1748 1 1008 (init pL1748) (init pL1748))
theorem L1748_seg1 : segOK pL1748 1 1008 (init pL1748) (init pL1748) L1748_cp1.1 L1748_cp1.2 = true := by
  decide +kernel
noncomputable def L1748_cp2 : Nat × Nat := t7val% (fastRun pL1748 1 1426 (init pL1748) (init pL1748))
theorem L1748_seg2 : segOK pL1748 1009 418 L1748_cp1.1 L1748_cp1.2 L1748_cp2.1 L1748_cp2.2 = true := by
  decide +kernel
theorem L1748_fin : (prmOK pL1748 1748 && ptTest pL1748 (runFrom pL1748 (fmask pL1748) (cmask pL1748) (hmask pL1748) 1427 321 (true, L1748_cp2.1, L1748_cp2.2)) 1748 874 false) = true := by
  decide +kernel
theorem L1748_ok : RunOK pL1748 1748 (runFrom pL1748 (fmask pL1748) (cmask pL1748) (hmask pL1748) 1427 321 (true, L1748_cp2.1, L1748_cp2.2)) ∧ ptTest pL1748 (runFrom pL1748 (fmask pL1748) (cmask pL1748) (hmask pL1748) 1427 321 (true, L1748_cp2.1, L1748_cp2.2)) 1748 874 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1748_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1748_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1748_fin) true) L1748_seg1) L1748_seg2) (by decide) rfl L1748_fin ptTest_fst
noncomputable def H1748_cp1 : Nat × Nat := t7val% (fastRun pH1748 1 1008 (init pH1748) (init pH1748))
theorem H1748_seg1 : segOK pH1748 1 1008 (init pH1748) (init pH1748) H1748_cp1.1 H1748_cp1.2 = true := by
  decide +kernel
noncomputable def H1748_cp2 : Nat × Nat := t7val% (fastRun pH1748 1 1426 (init pH1748) (init pH1748))
theorem H1748_seg2 : segOK pH1748 1009 418 H1748_cp1.1 H1748_cp1.2 H1748_cp2.1 H1748_cp2.2 = true := by
  decide +kernel
theorem H1748_fin : (prmOK pH1748 1748 && ptTest pH1748 (runFrom pH1748 (fmask pH1748) (cmask pH1748) (hmask pH1748) 1427 321 (true, H1748_cp2.1, H1748_cp2.2)) 1748 874 true) = true := by
  decide +kernel
theorem H1748_ok : RunOK pH1748 1748 (runFrom pH1748 (fmask pH1748) (cmask pH1748) (hmask pH1748) 1427 321 (true, H1748_cp2.1, H1748_cp2.2)) ∧ ptTest pH1748 (runFrom pH1748 (fmask pH1748) (cmask pH1748) (hmask pH1748) 1427 321 (true, H1748_cp2.1, H1748_cp2.2)) 1748 874 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1748_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1748_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1748_fin) true) H1748_seg1) H1748_seg2) (by decide) rfl H1748_fin ptTest_fst
noncomputable def I1748_cp1 : Nat × Nat := t7val% (fastRun pI1748 1 1235 (init pI1748) (init pI1748))
theorem I1748_seg1 : segOK pI1748 1 1235 (init pI1748) (init pI1748) I1748_cp1.1 I1748_cp1.2 = true := by
  decide +kernel
theorem I1748_fin : (prmOK pI1748 1748 && intTest pI1748 (runFrom pI1748 (fmask pI1748) (cmask pI1748) (hmask pI1748) 1236 512 (true, I1748_cp1.1, I1748_cp1.2)) 1748 21 true) = true := by
  decide +kernel
theorem I1748_ok : RunOK pI1748 1748 (runFrom pI1748 (fmask pI1748) (cmask pI1748) (hmask pI1748) 1236 512 (true, I1748_cp1.1, I1748_cp1.2)) ∧ intTest pI1748 (runFrom pI1748 (fmask pI1748) (cmask pI1748) (hmask pI1748) 1236 512 (true, I1748_cp1.1, I1748_cp1.2)) 1748 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1748_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1748_fin) true) I1748_seg1) (by decide) rfl I1748_fin intTest_fst
theorem link1748 : linkOK pL1748 pH1748 pI1748 = true := by decide +kernel
theorem cvx1748 : ConvexBetweenHumps 1748 :=
  cvx_of L1748_ok H1748_ok I1748_ok link1748 (by decide)
theorem cenlink1748 : cenLinkOK pI1748 1748 = true := by decide +kernel
theorem cen1748 : CenterUniqueMin 1748 ∧ DipHyp 1748 ∧ OnePointHyps 1748 :=
  cen_of L1748_ok H1748_ok I1748_ok link1748 cenlink1748

/-! ### `N = 1749` -/

def pL1749 : Prm := ⟨80, 37, 40, 1751, 11, 18446744073709551616, 109777404559059331, 109777404559059331⟩
def pH1749 : Prm := ⟨80, 37, 40, 1751, 11, 18446744073709551616, 109778504070687107, 109778504070687107⟩
def pI1749 : Prm := ⟨67, 34, 30, 1751, 11, 18446744073709551616, 109777404559059331, 109778504070687107⟩
noncomputable def L1749_cp1 : Nat × Nat := t7val% (fastRun pL1749 1 1009 (init pL1749) (init pL1749))
theorem L1749_seg1 : segOK pL1749 1 1009 (init pL1749) (init pL1749) L1749_cp1.1 L1749_cp1.2 = true := by
  decide +kernel
noncomputable def L1749_cp2 : Nat × Nat := t7val% (fastRun pL1749 1 1427 (init pL1749) (init pL1749))
theorem L1749_seg2 : segOK pL1749 1010 418 L1749_cp1.1 L1749_cp1.2 L1749_cp2.1 L1749_cp2.2 = true := by
  decide +kernel
theorem L1749_fin : (prmOK pL1749 1749 && ptTest pL1749 (runFrom pL1749 (fmask pL1749) (cmask pL1749) (hmask pL1749) 1428 321 (true, L1749_cp2.1, L1749_cp2.2)) 1749 875 false) = true := by
  decide +kernel
theorem L1749_ok : RunOK pL1749 1749 (runFrom pL1749 (fmask pL1749) (cmask pL1749) (hmask pL1749) 1428 321 (true, L1749_cp2.1, L1749_cp2.2)) ∧ ptTest pL1749 (runFrom pL1749 (fmask pL1749) (cmask pL1749) (hmask pL1749) 1428 321 (true, L1749_cp2.1, L1749_cp2.2)) 1749 875 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1749_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1749_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1749_fin) true) L1749_seg1) L1749_seg2) (by decide) rfl L1749_fin ptTest_fst
noncomputable def H1749_cp1 : Nat × Nat := t7val% (fastRun pH1749 1 1009 (init pH1749) (init pH1749))
theorem H1749_seg1 : segOK pH1749 1 1009 (init pH1749) (init pH1749) H1749_cp1.1 H1749_cp1.2 = true := by
  decide +kernel
noncomputable def H1749_cp2 : Nat × Nat := t7val% (fastRun pH1749 1 1427 (init pH1749) (init pH1749))
theorem H1749_seg2 : segOK pH1749 1010 418 H1749_cp1.1 H1749_cp1.2 H1749_cp2.1 H1749_cp2.2 = true := by
  decide +kernel
theorem H1749_fin : (prmOK pH1749 1749 && ptTest pH1749 (runFrom pH1749 (fmask pH1749) (cmask pH1749) (hmask pH1749) 1428 321 (true, H1749_cp2.1, H1749_cp2.2)) 1749 875 true) = true := by
  decide +kernel
theorem H1749_ok : RunOK pH1749 1749 (runFrom pH1749 (fmask pH1749) (cmask pH1749) (hmask pH1749) 1428 321 (true, H1749_cp2.1, H1749_cp2.2)) ∧ ptTest pH1749 (runFrom pH1749 (fmask pH1749) (cmask pH1749) (hmask pH1749) 1428 321 (true, H1749_cp2.1, H1749_cp2.2)) 1749 875 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1749_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1749_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1749_fin) true) H1749_seg1) H1749_seg2) (by decide) rfl H1749_fin ptTest_fst
noncomputable def I1749_cp1 : Nat × Nat := t7val% (fastRun pI1749 1 1236 (init pI1749) (init pI1749))
theorem I1749_seg1 : segOK pI1749 1 1236 (init pI1749) (init pI1749) I1749_cp1.1 I1749_cp1.2 = true := by
  decide +kernel
theorem I1749_fin : (prmOK pI1749 1749 && intTest pI1749 (runFrom pI1749 (fmask pI1749) (cmask pI1749) (hmask pI1749) 1237 512 (true, I1749_cp1.1, I1749_cp1.2)) 1749 21 false) = true := by
  decide +kernel
theorem I1749_ok : RunOK pI1749 1749 (runFrom pI1749 (fmask pI1749) (cmask pI1749) (hmask pI1749) 1237 512 (true, I1749_cp1.1, I1749_cp1.2)) ∧ intTest pI1749 (runFrom pI1749 (fmask pI1749) (cmask pI1749) (hmask pI1749) 1237 512 (true, I1749_cp1.1, I1749_cp1.2)) 1749 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1749_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1749_fin) true) I1749_seg1) (by decide) rfl I1749_fin intTest_fst
theorem link1749 : linkOK pL1749 pH1749 pI1749 = true := by decide +kernel
theorem cvx1749 : ConvexBetweenHumps 1749 :=
  cvx_of L1749_ok H1749_ok I1749_ok link1749 (by decide)

/-! ### `N = 1750` -/

def pL1750 : Prm := ⟨80, 37, 40, 1752, 11, 18446744073709551616, 109726043192578815, 109726043192578815⟩
def pH1750 : Prm := ⟨80, 37, 40, 1752, 11, 18446744073709551616, 109727142704206591, 109727142704206591⟩
def pI1750 : Prm := ⟨67, 34, 30, 1752, 11, 18446744073709551616, 109726043192578815, 109727142704206591⟩
noncomputable def L1750_cp1 : Nat × Nat := t7val% (fastRun pL1750 1 1009 (init pL1750) (init pL1750))
theorem L1750_seg1 : segOK pL1750 1 1009 (init pL1750) (init pL1750) L1750_cp1.1 L1750_cp1.2 = true := by
  decide +kernel
noncomputable def L1750_cp2 : Nat × Nat := t7val% (fastRun pL1750 1 1428 (init pL1750) (init pL1750))
theorem L1750_seg2 : segOK pL1750 1010 419 L1750_cp1.1 L1750_cp1.2 L1750_cp2.1 L1750_cp2.2 = true := by
  decide +kernel
theorem L1750_fin : (prmOK pL1750 1750 && ptTest pL1750 (runFrom pL1750 (fmask pL1750) (cmask pL1750) (hmask pL1750) 1429 321 (true, L1750_cp2.1, L1750_cp2.2)) 1750 875 false) = true := by
  decide +kernel
theorem L1750_ok : RunOK pL1750 1750 (runFrom pL1750 (fmask pL1750) (cmask pL1750) (hmask pL1750) 1429 321 (true, L1750_cp2.1, L1750_cp2.2)) ∧ ptTest pL1750 (runFrom pL1750 (fmask pL1750) (cmask pL1750) (hmask pL1750) 1429 321 (true, L1750_cp2.1, L1750_cp2.2)) 1750 875 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1750_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1750_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1750_fin) true) L1750_seg1) L1750_seg2) (by decide) rfl L1750_fin ptTest_fst
noncomputable def H1750_cp1 : Nat × Nat := t7val% (fastRun pH1750 1 1009 (init pH1750) (init pH1750))
theorem H1750_seg1 : segOK pH1750 1 1009 (init pH1750) (init pH1750) H1750_cp1.1 H1750_cp1.2 = true := by
  decide +kernel
noncomputable def H1750_cp2 : Nat × Nat := t7val% (fastRun pH1750 1 1428 (init pH1750) (init pH1750))
theorem H1750_seg2 : segOK pH1750 1010 419 H1750_cp1.1 H1750_cp1.2 H1750_cp2.1 H1750_cp2.2 = true := by
  decide +kernel
theorem H1750_fin : (prmOK pH1750 1750 && ptTest pH1750 (runFrom pH1750 (fmask pH1750) (cmask pH1750) (hmask pH1750) 1429 321 (true, H1750_cp2.1, H1750_cp2.2)) 1750 875 true) = true := by
  decide +kernel
theorem H1750_ok : RunOK pH1750 1750 (runFrom pH1750 (fmask pH1750) (cmask pH1750) (hmask pH1750) 1429 321 (true, H1750_cp2.1, H1750_cp2.2)) ∧ ptTest pH1750 (runFrom pH1750 (fmask pH1750) (cmask pH1750) (hmask pH1750) 1429 321 (true, H1750_cp2.1, H1750_cp2.2)) 1750 875 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1750_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1750_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1750_fin) true) H1750_seg1) H1750_seg2) (by decide) rfl H1750_fin ptTest_fst
noncomputable def I1750_cp1 : Nat × Nat := t7val% (fastRun pI1750 1 1236 (init pI1750) (init pI1750))
theorem I1750_seg1 : segOK pI1750 1 1236 (init pI1750) (init pI1750) I1750_cp1.1 I1750_cp1.2 = true := by
  decide +kernel
theorem I1750_fin : (prmOK pI1750 1750 && intTest pI1750 (runFrom pI1750 (fmask pI1750) (cmask pI1750) (hmask pI1750) 1237 513 (true, I1750_cp1.1, I1750_cp1.2)) 1750 21 true) = true := by
  decide +kernel
theorem I1750_ok : RunOK pI1750 1750 (runFrom pI1750 (fmask pI1750) (cmask pI1750) (hmask pI1750) 1237 513 (true, I1750_cp1.1, I1750_cp1.2)) ∧ intTest pI1750 (runFrom pI1750 (fmask pI1750) (cmask pI1750) (hmask pI1750) 1237 513 (true, I1750_cp1.1, I1750_cp1.2)) 1750 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1750_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1750_fin) true) I1750_seg1) (by decide) rfl I1750_fin intTest_fst
theorem link1750 : linkOK pL1750 pH1750 pI1750 = true := by decide +kernel
theorem cvx1750 : ConvexBetweenHumps 1750 :=
  cvx_of L1750_ok H1750_ok I1750_ok link1750 (by decide)
theorem cenlink1750 : cenLinkOK pI1750 1750 = true := by decide +kernel
theorem cen1750 : CenterUniqueMin 1750 ∧ DipHyp 1750 ∧ OnePointHyps 1750 :=
  cen_of L1750_ok H1750_ok I1750_ok link1750 cenlink1750

/-! ### `N = 1751` -/

def pL1751 : Prm := ⟨80, 37, 40, 1753, 11, 18446744073709551616, 109674713041217452, 109674713041217452⟩
def pH1751 : Prm := ⟨80, 37, 40, 1753, 11, 18446744073709551616, 109675812552845228, 109675812552845228⟩
def pI1751 : Prm := ⟨67, 34, 30, 1753, 11, 18446744073709551616, 109674713041217452, 109675812552845228⟩
noncomputable def L1751_cp1 : Nat × Nat := t7val% (fastRun pL1751 1 1010 (init pL1751) (init pL1751))
theorem L1751_seg1 : segOK pL1751 1 1010 (init pL1751) (init pL1751) L1751_cp1.1 L1751_cp1.2 = true := by
  decide +kernel
noncomputable def L1751_cp2 : Nat × Nat := t7val% (fastRun pL1751 1 1429 (init pL1751) (init pL1751))
theorem L1751_seg2 : segOK pL1751 1011 419 L1751_cp1.1 L1751_cp1.2 L1751_cp2.1 L1751_cp2.2 = true := by
  decide +kernel
theorem L1751_fin : (prmOK pL1751 1751 && ptTest pL1751 (runFrom pL1751 (fmask pL1751) (cmask pL1751) (hmask pL1751) 1430 321 (true, L1751_cp2.1, L1751_cp2.2)) 1751 876 false) = true := by
  decide +kernel
theorem L1751_ok : RunOK pL1751 1751 (runFrom pL1751 (fmask pL1751) (cmask pL1751) (hmask pL1751) 1430 321 (true, L1751_cp2.1, L1751_cp2.2)) ∧ ptTest pL1751 (runFrom pL1751 (fmask pL1751) (cmask pL1751) (hmask pL1751) 1430 321 (true, L1751_cp2.1, L1751_cp2.2)) 1751 876 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1751_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1751_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1751_fin) true) L1751_seg1) L1751_seg2) (by decide) rfl L1751_fin ptTest_fst
noncomputable def H1751_cp1 : Nat × Nat := t7val% (fastRun pH1751 1 1010 (init pH1751) (init pH1751))
theorem H1751_seg1 : segOK pH1751 1 1010 (init pH1751) (init pH1751) H1751_cp1.1 H1751_cp1.2 = true := by
  decide +kernel
noncomputable def H1751_cp2 : Nat × Nat := t7val% (fastRun pH1751 1 1429 (init pH1751) (init pH1751))
theorem H1751_seg2 : segOK pH1751 1011 419 H1751_cp1.1 H1751_cp1.2 H1751_cp2.1 H1751_cp2.2 = true := by
  decide +kernel
theorem H1751_fin : (prmOK pH1751 1751 && ptTest pH1751 (runFrom pH1751 (fmask pH1751) (cmask pH1751) (hmask pH1751) 1430 321 (true, H1751_cp2.1, H1751_cp2.2)) 1751 876 true) = true := by
  decide +kernel
theorem H1751_ok : RunOK pH1751 1751 (runFrom pH1751 (fmask pH1751) (cmask pH1751) (hmask pH1751) 1430 321 (true, H1751_cp2.1, H1751_cp2.2)) ∧ ptTest pH1751 (runFrom pH1751 (fmask pH1751) (cmask pH1751) (hmask pH1751) 1430 321 (true, H1751_cp2.1, H1751_cp2.2)) 1751 876 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1751_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1751_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1751_fin) true) H1751_seg1) H1751_seg2) (by decide) rfl H1751_fin ptTest_fst
noncomputable def I1751_cp1 : Nat × Nat := t7val% (fastRun pI1751 1 1237 (init pI1751) (init pI1751))
theorem I1751_seg1 : segOK pI1751 1 1237 (init pI1751) (init pI1751) I1751_cp1.1 I1751_cp1.2 = true := by
  decide +kernel
theorem I1751_fin : (prmOK pI1751 1751 && intTest pI1751 (runFrom pI1751 (fmask pI1751) (cmask pI1751) (hmask pI1751) 1238 513 (true, I1751_cp1.1, I1751_cp1.2)) 1751 21 false) = true := by
  decide +kernel
theorem I1751_ok : RunOK pI1751 1751 (runFrom pI1751 (fmask pI1751) (cmask pI1751) (hmask pI1751) 1238 513 (true, I1751_cp1.1, I1751_cp1.2)) ∧ intTest pI1751 (runFrom pI1751 (fmask pI1751) (cmask pI1751) (hmask pI1751) 1238 513 (true, I1751_cp1.1, I1751_cp1.2)) 1751 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1751_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1751_fin) true) I1751_seg1) (by decide) rfl I1751_fin intTest_fst
theorem link1751 : linkOK pL1751 pH1751 pI1751 = true := by decide +kernel
theorem cvx1751 : ConvexBetweenHumps 1751 :=
  cvx_of L1751_ok H1751_ok I1751_ok link1751 (by decide)

/-! ### `N = 1752` -/

def pL1752 : Prm := ⟨80, 37, 40, 1754, 11, 18446744073709551616, 109623455923522695, 109623455923522695⟩
def pH1752 : Prm := ⟨80, 37, 40, 1754, 11, 18446744073709551616, 109624555435150471, 109624555435150471⟩
def pI1752 : Prm := ⟨67, 34, 30, 1754, 11, 18446744073709551616, 109623455923522695, 109624555435150471⟩
noncomputable def L1752_cp1 : Nat × Nat := t7val% (fastRun pL1752 1 1011 (init pL1752) (init pL1752))
theorem L1752_seg1 : segOK pL1752 1 1011 (init pL1752) (init pL1752) L1752_cp1.1 L1752_cp1.2 = true := by
  decide +kernel
noncomputable def L1752_cp2 : Nat × Nat := t7val% (fastRun pL1752 1 1430 (init pL1752) (init pL1752))
theorem L1752_seg2 : segOK pL1752 1012 419 L1752_cp1.1 L1752_cp1.2 L1752_cp2.1 L1752_cp2.2 = true := by
  decide +kernel
theorem L1752_fin : (prmOK pL1752 1752 && ptTest pL1752 (runFrom pL1752 (fmask pL1752) (cmask pL1752) (hmask pL1752) 1431 321 (true, L1752_cp2.1, L1752_cp2.2)) 1752 876 false) = true := by
  decide +kernel
theorem L1752_ok : RunOK pL1752 1752 (runFrom pL1752 (fmask pL1752) (cmask pL1752) (hmask pL1752) 1431 321 (true, L1752_cp2.1, L1752_cp2.2)) ∧ ptTest pL1752 (runFrom pL1752 (fmask pL1752) (cmask pL1752) (hmask pL1752) 1431 321 (true, L1752_cp2.1, L1752_cp2.2)) 1752 876 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1752_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1752_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1752_fin) true) L1752_seg1) L1752_seg2) (by decide) rfl L1752_fin ptTest_fst
noncomputable def H1752_cp1 : Nat × Nat := t7val% (fastRun pH1752 1 1011 (init pH1752) (init pH1752))
theorem H1752_seg1 : segOK pH1752 1 1011 (init pH1752) (init pH1752) H1752_cp1.1 H1752_cp1.2 = true := by
  decide +kernel
noncomputable def H1752_cp2 : Nat × Nat := t7val% (fastRun pH1752 1 1430 (init pH1752) (init pH1752))
theorem H1752_seg2 : segOK pH1752 1012 419 H1752_cp1.1 H1752_cp1.2 H1752_cp2.1 H1752_cp2.2 = true := by
  decide +kernel
theorem H1752_fin : (prmOK pH1752 1752 && ptTest pH1752 (runFrom pH1752 (fmask pH1752) (cmask pH1752) (hmask pH1752) 1431 321 (true, H1752_cp2.1, H1752_cp2.2)) 1752 876 true) = true := by
  decide +kernel
theorem H1752_ok : RunOK pH1752 1752 (runFrom pH1752 (fmask pH1752) (cmask pH1752) (hmask pH1752) 1431 321 (true, H1752_cp2.1, H1752_cp2.2)) ∧ ptTest pH1752 (runFrom pH1752 (fmask pH1752) (cmask pH1752) (hmask pH1752) 1431 321 (true, H1752_cp2.1, H1752_cp2.2)) 1752 876 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1752_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1752_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1752_fin) true) H1752_seg1) H1752_seg2) (by decide) rfl H1752_fin ptTest_fst
noncomputable def I1752_cp1 : Nat × Nat := t7val% (fastRun pI1752 1 1238 (init pI1752) (init pI1752))
theorem I1752_seg1 : segOK pI1752 1 1238 (init pI1752) (init pI1752) I1752_cp1.1 I1752_cp1.2 = true := by
  decide +kernel
theorem I1752_fin : (prmOK pI1752 1752 && intTest pI1752 (runFrom pI1752 (fmask pI1752) (cmask pI1752) (hmask pI1752) 1239 513 (true, I1752_cp1.1, I1752_cp1.2)) 1752 21 true) = true := by
  decide +kernel
theorem I1752_ok : RunOK pI1752 1752 (runFrom pI1752 (fmask pI1752) (cmask pI1752) (hmask pI1752) 1239 513 (true, I1752_cp1.1, I1752_cp1.2)) ∧ intTest pI1752 (runFrom pI1752 (fmask pI1752) (cmask pI1752) (hmask pI1752) 1239 513 (true, I1752_cp1.1, I1752_cp1.2)) 1752 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1752_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1752_fin) true) I1752_seg1) (by decide) rfl I1752_fin intTest_fst
theorem link1752 : linkOK pL1752 pH1752 pI1752 = true := by decide +kernel
theorem cvx1752 : ConvexBetweenHumps 1752 :=
  cvx_of L1752_ok H1752_ok I1752_ok link1752 (by decide)
theorem cenlink1752 : cenLinkOK pI1752 1752 = true := by decide +kernel
theorem cen1752 : CenterUniqueMin 1752 ∧ DipHyp 1752 ∧ OnePointHyps 1752 :=
  cen_of L1752_ok H1752_ok I1752_ok link1752 cenlink1752

/-! ### `N = 1753` -/

def pL1753 : Prm := ⟨80, 37, 40, 1755, 11, 18446744073709551616, 109572229930059984, 109572229930059984⟩
def pH1753 : Prm := ⟨80, 37, 40, 1755, 11, 18446744073709551616, 109573329441687760, 109573329441687760⟩
def pI1753 : Prm := ⟨67, 34, 30, 1755, 11, 18446744073709551616, 109572229930059984, 109573329441687760⟩
noncomputable def L1753_cp1 : Nat × Nat := t7val% (fastRun pL1753 1 1011 (init pL1753) (init pL1753))
theorem L1753_seg1 : segOK pL1753 1 1011 (init pL1753) (init pL1753) L1753_cp1.1 L1753_cp1.2 = true := by
  decide +kernel
noncomputable def L1753_cp2 : Nat × Nat := t7val% (fastRun pL1753 1 1430 (init pL1753) (init pL1753))
theorem L1753_seg2 : segOK pL1753 1012 419 L1753_cp1.1 L1753_cp1.2 L1753_cp2.1 L1753_cp2.2 = true := by
  decide +kernel
theorem L1753_fin : (prmOK pL1753 1753 && ptTest pL1753 (runFrom pL1753 (fmask pL1753) (cmask pL1753) (hmask pL1753) 1431 322 (true, L1753_cp2.1, L1753_cp2.2)) 1753 877 false) = true := by
  decide +kernel
theorem L1753_ok : RunOK pL1753 1753 (runFrom pL1753 (fmask pL1753) (cmask pL1753) (hmask pL1753) 1431 322 (true, L1753_cp2.1, L1753_cp2.2)) ∧ ptTest pL1753 (runFrom pL1753 (fmask pL1753) (cmask pL1753) (hmask pL1753) 1431 322 (true, L1753_cp2.1, L1753_cp2.2)) 1753 877 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1753_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1753_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1753_fin) true) L1753_seg1) L1753_seg2) (by decide) rfl L1753_fin ptTest_fst
noncomputable def H1753_cp1 : Nat × Nat := t7val% (fastRun pH1753 1 1011 (init pH1753) (init pH1753))
theorem H1753_seg1 : segOK pH1753 1 1011 (init pH1753) (init pH1753) H1753_cp1.1 H1753_cp1.2 = true := by
  decide +kernel
noncomputable def H1753_cp2 : Nat × Nat := t7val% (fastRun pH1753 1 1430 (init pH1753) (init pH1753))
theorem H1753_seg2 : segOK pH1753 1012 419 H1753_cp1.1 H1753_cp1.2 H1753_cp2.1 H1753_cp2.2 = true := by
  decide +kernel
theorem H1753_fin : (prmOK pH1753 1753 && ptTest pH1753 (runFrom pH1753 (fmask pH1753) (cmask pH1753) (hmask pH1753) 1431 322 (true, H1753_cp2.1, H1753_cp2.2)) 1753 877 true) = true := by
  decide +kernel
theorem H1753_ok : RunOK pH1753 1753 (runFrom pH1753 (fmask pH1753) (cmask pH1753) (hmask pH1753) 1431 322 (true, H1753_cp2.1, H1753_cp2.2)) ∧ ptTest pH1753 (runFrom pH1753 (fmask pH1753) (cmask pH1753) (hmask pH1753) 1431 322 (true, H1753_cp2.1, H1753_cp2.2)) 1753 877 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1753_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1753_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1753_fin) true) H1753_seg1) H1753_seg2) (by decide) rfl H1753_fin ptTest_fst
noncomputable def I1753_cp1 : Nat × Nat := t7val% (fastRun pI1753 1 1239 (init pI1753) (init pI1753))
theorem I1753_seg1 : segOK pI1753 1 1239 (init pI1753) (init pI1753) I1753_cp1.1 I1753_cp1.2 = true := by
  decide +kernel
theorem I1753_fin : (prmOK pI1753 1753 && intTest pI1753 (runFrom pI1753 (fmask pI1753) (cmask pI1753) (hmask pI1753) 1240 513 (true, I1753_cp1.1, I1753_cp1.2)) 1753 21 false) = true := by
  decide +kernel
theorem I1753_ok : RunOK pI1753 1753 (runFrom pI1753 (fmask pI1753) (cmask pI1753) (hmask pI1753) 1240 513 (true, I1753_cp1.1, I1753_cp1.2)) ∧ intTest pI1753 (runFrom pI1753 (fmask pI1753) (cmask pI1753) (hmask pI1753) 1240 513 (true, I1753_cp1.1, I1753_cp1.2)) 1753 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1753_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1753_fin) true) I1753_seg1) (by decide) rfl I1753_fin intTest_fst
theorem link1753 : linkOK pL1753 pH1753 pI1753 = true := by decide +kernel
theorem cvx1753 : ConvexBetweenHumps 1753 :=
  cvx_of L1753_ok H1753_ok I1753_ok link1753 (by decide)

/-! ### `N = 1754` -/

def pL1754 : Prm := ⟨80, 37, 40, 1756, 11, 18446744073709551616, 109521076734237789, 109521076734237789⟩
def pH1754 : Prm := ⟨80, 37, 40, 1756, 11, 18446744073709551616, 109522176245865565, 109522176245865565⟩
def pI1754 : Prm := ⟨67, 34, 30, 1756, 11, 18446744073709551616, 109521076734237789, 109522176245865565⟩
noncomputable def L1754_cp1 : Nat × Nat := t7val% (fastRun pL1754 1 1012 (init pL1754) (init pL1754))
theorem L1754_seg1 : segOK pL1754 1 1012 (init pL1754) (init pL1754) L1754_cp1.1 L1754_cp1.2 = true := by
  decide +kernel
noncomputable def L1754_cp2 : Nat × Nat := t7val% (fastRun pL1754 1 1431 (init pL1754) (init pL1754))
theorem L1754_seg2 : segOK pL1754 1013 419 L1754_cp1.1 L1754_cp1.2 L1754_cp2.1 L1754_cp2.2 = true := by
  decide +kernel
theorem L1754_fin : (prmOK pL1754 1754 && ptTest pL1754 (runFrom pL1754 (fmask pL1754) (cmask pL1754) (hmask pL1754) 1432 322 (true, L1754_cp2.1, L1754_cp2.2)) 1754 877 false) = true := by
  decide +kernel
theorem L1754_ok : RunOK pL1754 1754 (runFrom pL1754 (fmask pL1754) (cmask pL1754) (hmask pL1754) 1432 322 (true, L1754_cp2.1, L1754_cp2.2)) ∧ ptTest pL1754 (runFrom pL1754 (fmask pL1754) (cmask pL1754) (hmask pL1754) 1432 322 (true, L1754_cp2.1, L1754_cp2.2)) 1754 877 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1754_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1754_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1754_fin) true) L1754_seg1) L1754_seg2) (by decide) rfl L1754_fin ptTest_fst
noncomputable def H1754_cp1 : Nat × Nat := t7val% (fastRun pH1754 1 1012 (init pH1754) (init pH1754))
theorem H1754_seg1 : segOK pH1754 1 1012 (init pH1754) (init pH1754) H1754_cp1.1 H1754_cp1.2 = true := by
  decide +kernel
noncomputable def H1754_cp2 : Nat × Nat := t7val% (fastRun pH1754 1 1431 (init pH1754) (init pH1754))
theorem H1754_seg2 : segOK pH1754 1013 419 H1754_cp1.1 H1754_cp1.2 H1754_cp2.1 H1754_cp2.2 = true := by
  decide +kernel
theorem H1754_fin : (prmOK pH1754 1754 && ptTest pH1754 (runFrom pH1754 (fmask pH1754) (cmask pH1754) (hmask pH1754) 1432 322 (true, H1754_cp2.1, H1754_cp2.2)) 1754 877 true) = true := by
  decide +kernel
theorem H1754_ok : RunOK pH1754 1754 (runFrom pH1754 (fmask pH1754) (cmask pH1754) (hmask pH1754) 1432 322 (true, H1754_cp2.1, H1754_cp2.2)) ∧ ptTest pH1754 (runFrom pH1754 (fmask pH1754) (cmask pH1754) (hmask pH1754) 1432 322 (true, H1754_cp2.1, H1754_cp2.2)) 1754 877 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1754_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1754_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1754_fin) true) H1754_seg1) H1754_seg2) (by decide) rfl H1754_fin ptTest_fst
noncomputable def I1754_cp1 : Nat × Nat := t7val% (fastRun pI1754 1 1239 (init pI1754) (init pI1754))
theorem I1754_seg1 : segOK pI1754 1 1239 (init pI1754) (init pI1754) I1754_cp1.1 I1754_cp1.2 = true := by
  decide +kernel
theorem I1754_fin : (prmOK pI1754 1754 && intTest pI1754 (runFrom pI1754 (fmask pI1754) (cmask pI1754) (hmask pI1754) 1240 514 (true, I1754_cp1.1, I1754_cp1.2)) 1754 21 true) = true := by
  decide +kernel
theorem I1754_ok : RunOK pI1754 1754 (runFrom pI1754 (fmask pI1754) (cmask pI1754) (hmask pI1754) 1240 514 (true, I1754_cp1.1, I1754_cp1.2)) ∧ intTest pI1754 (runFrom pI1754 (fmask pI1754) (cmask pI1754) (hmask pI1754) 1240 514 (true, I1754_cp1.1, I1754_cp1.2)) 1754 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1754_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1754_fin) true) I1754_seg1) (by decide) rfl I1754_fin intTest_fst
theorem link1754 : linkOK pL1754 pH1754 pI1754 = true := by decide +kernel
theorem cvx1754 : ConvexBetweenHumps 1754 :=
  cvx_of L1754_ok H1754_ok I1754_ok link1754 (by decide)
theorem cenlink1754 : cenLinkOK pI1754 1754 = true := by decide +kernel
theorem cen1754 : CenterUniqueMin 1754 ∧ DipHyp 1754 ∧ OnePointHyps 1754 :=
  cen_of L1754_ok H1754_ok I1754_ok link1754 cenlink1754

/-! ### `N = 1755` -/

def pL1755 : Prm := ⟨80, 37, 40, 1757, 11, 18446744073709551616, 109469954572129466, 109469954572129466⟩
def pH1755 : Prm := ⟨80, 37, 40, 1757, 11, 18446744073709551616, 109471054083757242, 109471054083757242⟩
def pI1755 : Prm := ⟨67, 34, 30, 1757, 11, 18446744073709551616, 109469954572129466, 109471054083757242⟩
noncomputable def L1755_cp1 : Nat × Nat := t7val% (fastRun pL1755 1 1012 (init pL1755) (init pL1755))
theorem L1755_seg1 : segOK pL1755 1 1012 (init pL1755) (init pL1755) L1755_cp1.1 L1755_cp1.2 = true := by
  decide +kernel
noncomputable def L1755_cp2 : Nat × Nat := t7val% (fastRun pL1755 1 1432 (init pL1755) (init pL1755))
theorem L1755_seg2 : segOK pL1755 1013 420 L1755_cp1.1 L1755_cp1.2 L1755_cp2.1 L1755_cp2.2 = true := by
  decide +kernel
theorem L1755_fin : (prmOK pL1755 1755 && ptTest pL1755 (runFrom pL1755 (fmask pL1755) (cmask pL1755) (hmask pL1755) 1433 322 (true, L1755_cp2.1, L1755_cp2.2)) 1755 878 false) = true := by
  decide +kernel
theorem L1755_ok : RunOK pL1755 1755 (runFrom pL1755 (fmask pL1755) (cmask pL1755) (hmask pL1755) 1433 322 (true, L1755_cp2.1, L1755_cp2.2)) ∧ ptTest pL1755 (runFrom pL1755 (fmask pL1755) (cmask pL1755) (hmask pL1755) 1433 322 (true, L1755_cp2.1, L1755_cp2.2)) 1755 878 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1755_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1755_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1755_fin) true) L1755_seg1) L1755_seg2) (by decide) rfl L1755_fin ptTest_fst
noncomputable def H1755_cp1 : Nat × Nat := t7val% (fastRun pH1755 1 1012 (init pH1755) (init pH1755))
theorem H1755_seg1 : segOK pH1755 1 1012 (init pH1755) (init pH1755) H1755_cp1.1 H1755_cp1.2 = true := by
  decide +kernel
noncomputable def H1755_cp2 : Nat × Nat := t7val% (fastRun pH1755 1 1432 (init pH1755) (init pH1755))
theorem H1755_seg2 : segOK pH1755 1013 420 H1755_cp1.1 H1755_cp1.2 H1755_cp2.1 H1755_cp2.2 = true := by
  decide +kernel
theorem H1755_fin : (prmOK pH1755 1755 && ptTest pH1755 (runFrom pH1755 (fmask pH1755) (cmask pH1755) (hmask pH1755) 1433 322 (true, H1755_cp2.1, H1755_cp2.2)) 1755 878 true) = true := by
  decide +kernel
theorem H1755_ok : RunOK pH1755 1755 (runFrom pH1755 (fmask pH1755) (cmask pH1755) (hmask pH1755) 1433 322 (true, H1755_cp2.1, H1755_cp2.2)) ∧ ptTest pH1755 (runFrom pH1755 (fmask pH1755) (cmask pH1755) (hmask pH1755) 1433 322 (true, H1755_cp2.1, H1755_cp2.2)) 1755 878 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1755_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1755_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1755_fin) true) H1755_seg1) H1755_seg2) (by decide) rfl H1755_fin ptTest_fst
noncomputable def I1755_cp1 : Nat × Nat := t7val% (fastRun pI1755 1 1240 (init pI1755) (init pI1755))
theorem I1755_seg1 : segOK pI1755 1 1240 (init pI1755) (init pI1755) I1755_cp1.1 I1755_cp1.2 = true := by
  decide +kernel
theorem I1755_fin : (prmOK pI1755 1755 && intTest pI1755 (runFrom pI1755 (fmask pI1755) (cmask pI1755) (hmask pI1755) 1241 514 (true, I1755_cp1.1, I1755_cp1.2)) 1755 21 false) = true := by
  decide +kernel
theorem I1755_ok : RunOK pI1755 1755 (runFrom pI1755 (fmask pI1755) (cmask pI1755) (hmask pI1755) 1241 514 (true, I1755_cp1.1, I1755_cp1.2)) ∧ intTest pI1755 (runFrom pI1755 (fmask pI1755) (cmask pI1755) (hmask pI1755) 1241 514 (true, I1755_cp1.1, I1755_cp1.2)) 1755 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1755_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1755_fin) true) I1755_seg1) (by decide) rfl I1755_fin intTest_fst
theorem link1755 : linkOK pL1755 pH1755 pI1755 = true := by decide +kernel
theorem cvx1755 : ConvexBetweenHumps 1755 :=
  cvx_of L1755_ok H1755_ok I1755_ok link1755 (by decide)

/-! ### `N = 1756` -/

def pL1756 : Prm := ⟨80, 37, 40, 1758, 11, 18446744073709551616, 109418904972705480, 109418904972705480⟩
def pH1756 : Prm := ⟨80, 37, 40, 1758, 11, 18446744073709551616, 109420004484333256, 109420004484333256⟩
def pI1756 : Prm := ⟨67, 34, 30, 1758, 11, 18446744073709551616, 109418904972705480, 109420004484333256⟩
noncomputable def L1756_cp1 : Nat × Nat := t7val% (fastRun pL1756 1 1013 (init pL1756) (init pL1756))
theorem L1756_seg1 : segOK pL1756 1 1013 (init pL1756) (init pL1756) L1756_cp1.1 L1756_cp1.2 = true := by
  decide +kernel
noncomputable def L1756_cp2 : Nat × Nat := t7val% (fastRun pL1756 1 1433 (init pL1756) (init pL1756))
theorem L1756_seg2 : segOK pL1756 1014 420 L1756_cp1.1 L1756_cp1.2 L1756_cp2.1 L1756_cp2.2 = true := by
  decide +kernel
theorem L1756_fin : (prmOK pL1756 1756 && ptTest pL1756 (runFrom pL1756 (fmask pL1756) (cmask pL1756) (hmask pL1756) 1434 322 (true, L1756_cp2.1, L1756_cp2.2)) 1756 878 false) = true := by
  decide +kernel
theorem L1756_ok : RunOK pL1756 1756 (runFrom pL1756 (fmask pL1756) (cmask pL1756) (hmask pL1756) 1434 322 (true, L1756_cp2.1, L1756_cp2.2)) ∧ ptTest pL1756 (runFrom pL1756 (fmask pL1756) (cmask pL1756) (hmask pL1756) 1434 322 (true, L1756_cp2.1, L1756_cp2.2)) 1756 878 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1756_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1756_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1756_fin) true) L1756_seg1) L1756_seg2) (by decide) rfl L1756_fin ptTest_fst
noncomputable def H1756_cp1 : Nat × Nat := t7val% (fastRun pH1756 1 1013 (init pH1756) (init pH1756))
theorem H1756_seg1 : segOK pH1756 1 1013 (init pH1756) (init pH1756) H1756_cp1.1 H1756_cp1.2 = true := by
  decide +kernel
noncomputable def H1756_cp2 : Nat × Nat := t7val% (fastRun pH1756 1 1433 (init pH1756) (init pH1756))
theorem H1756_seg2 : segOK pH1756 1014 420 H1756_cp1.1 H1756_cp1.2 H1756_cp2.1 H1756_cp2.2 = true := by
  decide +kernel
theorem H1756_fin : (prmOK pH1756 1756 && ptTest pH1756 (runFrom pH1756 (fmask pH1756) (cmask pH1756) (hmask pH1756) 1434 322 (true, H1756_cp2.1, H1756_cp2.2)) 1756 878 true) = true := by
  decide +kernel
theorem H1756_ok : RunOK pH1756 1756 (runFrom pH1756 (fmask pH1756) (cmask pH1756) (hmask pH1756) 1434 322 (true, H1756_cp2.1, H1756_cp2.2)) ∧ ptTest pH1756 (runFrom pH1756 (fmask pH1756) (cmask pH1756) (hmask pH1756) 1434 322 (true, H1756_cp2.1, H1756_cp2.2)) 1756 878 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1756_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1756_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1756_fin) true) H1756_seg1) H1756_seg2) (by decide) rfl H1756_fin ptTest_fst
noncomputable def I1756_cp1 : Nat × Nat := t7val% (fastRun pI1756 1 1241 (init pI1756) (init pI1756))
theorem I1756_seg1 : segOK pI1756 1 1241 (init pI1756) (init pI1756) I1756_cp1.1 I1756_cp1.2 = true := by
  decide +kernel
theorem I1756_fin : (prmOK pI1756 1756 && intTest pI1756 (runFrom pI1756 (fmask pI1756) (cmask pI1756) (hmask pI1756) 1242 514 (true, I1756_cp1.1, I1756_cp1.2)) 1756 21 true) = true := by
  decide +kernel
theorem I1756_ok : RunOK pI1756 1756 (runFrom pI1756 (fmask pI1756) (cmask pI1756) (hmask pI1756) 1242 514 (true, I1756_cp1.1, I1756_cp1.2)) ∧ intTest pI1756 (runFrom pI1756 (fmask pI1756) (cmask pI1756) (hmask pI1756) 1242 514 (true, I1756_cp1.1, I1756_cp1.2)) 1756 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1756_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1756_fin) true) I1756_seg1) (by decide) rfl I1756_fin intTest_fst
theorem link1756 : linkOK pL1756 pH1756 pI1756 = true := by decide +kernel
theorem cvx1756 : ConvexBetweenHumps 1756 :=
  cvx_of L1756_ok H1756_ok I1756_ok link1756 (by decide)
theorem cenlink1756 : cenLinkOK pI1756 1756 = true := by decide +kernel
theorem cen1756 : CenterUniqueMin 1756 ∧ DipHyp 1756 ∧ OnePointHyps 1756 :=
  cen_of L1756_ok H1756_ok I1756_ok link1756 cenlink1756

/-! ### `N = 1757` -/

def pL1757 : Prm := ⟨80, 37, 40, 1759, 11, 18446744073709551616, 109367886316790788, 109367886316790788⟩
def pH1757 : Prm := ⟨80, 37, 40, 1759, 11, 18446744073709551616, 109368985828418564, 109368985828418564⟩
def pI1757 : Prm := ⟨67, 34, 30, 1759, 11, 18446744073709551616, 109367886316790788, 109368985828418564⟩
noncomputable def L1757_cp1 : Nat × Nat := t7val% (fastRun pL1757 1 1013 (init pL1757) (init pL1757))
theorem L1757_seg1 : segOK pL1757 1 1013 (init pL1757) (init pL1757) L1757_cp1.1 L1757_cp1.2 = true := by
  decide +kernel
noncomputable def L1757_cp2 : Nat × Nat := t7val% (fastRun pL1757 1 1434 (init pL1757) (init pL1757))
theorem L1757_seg2 : segOK pL1757 1014 421 L1757_cp1.1 L1757_cp1.2 L1757_cp2.1 L1757_cp2.2 = true := by
  decide +kernel
theorem L1757_fin : (prmOK pL1757 1757 && ptTest pL1757 (runFrom pL1757 (fmask pL1757) (cmask pL1757) (hmask pL1757) 1435 322 (true, L1757_cp2.1, L1757_cp2.2)) 1757 879 false) = true := by
  decide +kernel
theorem L1757_ok : RunOK pL1757 1757 (runFrom pL1757 (fmask pL1757) (cmask pL1757) (hmask pL1757) 1435 322 (true, L1757_cp2.1, L1757_cp2.2)) ∧ ptTest pL1757 (runFrom pL1757 (fmask pL1757) (cmask pL1757) (hmask pL1757) 1435 322 (true, L1757_cp2.1, L1757_cp2.2)) 1757 879 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1757_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1757_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1757_fin) true) L1757_seg1) L1757_seg2) (by decide) rfl L1757_fin ptTest_fst
noncomputable def H1757_cp1 : Nat × Nat := t7val% (fastRun pH1757 1 1013 (init pH1757) (init pH1757))
theorem H1757_seg1 : segOK pH1757 1 1013 (init pH1757) (init pH1757) H1757_cp1.1 H1757_cp1.2 = true := by
  decide +kernel
noncomputable def H1757_cp2 : Nat × Nat := t7val% (fastRun pH1757 1 1434 (init pH1757) (init pH1757))
theorem H1757_seg2 : segOK pH1757 1014 421 H1757_cp1.1 H1757_cp1.2 H1757_cp2.1 H1757_cp2.2 = true := by
  decide +kernel
theorem H1757_fin : (prmOK pH1757 1757 && ptTest pH1757 (runFrom pH1757 (fmask pH1757) (cmask pH1757) (hmask pH1757) 1435 322 (true, H1757_cp2.1, H1757_cp2.2)) 1757 879 true) = true := by
  decide +kernel
theorem H1757_ok : RunOK pH1757 1757 (runFrom pH1757 (fmask pH1757) (cmask pH1757) (hmask pH1757) 1435 322 (true, H1757_cp2.1, H1757_cp2.2)) ∧ ptTest pH1757 (runFrom pH1757 (fmask pH1757) (cmask pH1757) (hmask pH1757) 1435 322 (true, H1757_cp2.1, H1757_cp2.2)) 1757 879 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1757_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1757_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1757_fin) true) H1757_seg1) H1757_seg2) (by decide) rfl H1757_fin ptTest_fst
noncomputable def I1757_cp1 : Nat × Nat := t7val% (fastRun pI1757 1 1241 (init pI1757) (init pI1757))
theorem I1757_seg1 : segOK pI1757 1 1241 (init pI1757) (init pI1757) I1757_cp1.1 I1757_cp1.2 = true := by
  decide +kernel
theorem I1757_fin : (prmOK pI1757 1757 && intTest pI1757 (runFrom pI1757 (fmask pI1757) (cmask pI1757) (hmask pI1757) 1242 515 (true, I1757_cp1.1, I1757_cp1.2)) 1757 21 false) = true := by
  decide +kernel
theorem I1757_ok : RunOK pI1757 1757 (runFrom pI1757 (fmask pI1757) (cmask pI1757) (hmask pI1757) 1242 515 (true, I1757_cp1.1, I1757_cp1.2)) ∧ intTest pI1757 (runFrom pI1757 (fmask pI1757) (cmask pI1757) (hmask pI1757) 1242 515 (true, I1757_cp1.1, I1757_cp1.2)) 1757 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1757_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1757_fin) true) I1757_seg1) (by decide) rfl I1757_fin intTest_fst
theorem link1757 : linkOK pL1757 pH1757 pI1757 = true := by decide +kernel
theorem cvx1757 : ConvexBetweenHumps 1757 :=
  cvx_of L1757_ok H1757_ok I1757_ok link1757 (by decide)

/-! ### `N = 1758` -/

def pL1758 : Prm := ⟨80, 37, 40, 1760, 11, 18446744073709551616, 109316939989600377, 109316939989600377⟩
def pH1758 : Prm := ⟨80, 37, 40, 1760, 11, 18446744073709551616, 109318039501228153, 109318039501228153⟩
def pI1758 : Prm := ⟨67, 34, 30, 1760, 11, 18446744073709551616, 109316939989600377, 109318039501228153⟩
noncomputable def L1758_cp1 : Nat × Nat := t7val% (fastRun pL1758 1 1014 (init pL1758) (init pL1758))
theorem L1758_seg1 : segOK pL1758 1 1014 (init pL1758) (init pL1758) L1758_cp1.1 L1758_cp1.2 = true := by
  decide +kernel
noncomputable def L1758_cp2 : Nat × Nat := t7val% (fastRun pL1758 1 1434 (init pL1758) (init pL1758))
theorem L1758_seg2 : segOK pL1758 1015 420 L1758_cp1.1 L1758_cp1.2 L1758_cp2.1 L1758_cp2.2 = true := by
  decide +kernel
theorem L1758_fin : (prmOK pL1758 1758 && ptTest pL1758 (runFrom pL1758 (fmask pL1758) (cmask pL1758) (hmask pL1758) 1435 323 (true, L1758_cp2.1, L1758_cp2.2)) 1758 879 false) = true := by
  decide +kernel
theorem L1758_ok : RunOK pL1758 1758 (runFrom pL1758 (fmask pL1758) (cmask pL1758) (hmask pL1758) 1435 323 (true, L1758_cp2.1, L1758_cp2.2)) ∧ ptTest pL1758 (runFrom pL1758 (fmask pL1758) (cmask pL1758) (hmask pL1758) 1435 323 (true, L1758_cp2.1, L1758_cp2.2)) 1758 879 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1758_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1758_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1758_fin) true) L1758_seg1) L1758_seg2) (by decide) rfl L1758_fin ptTest_fst
noncomputable def H1758_cp1 : Nat × Nat := t7val% (fastRun pH1758 1 1014 (init pH1758) (init pH1758))
theorem H1758_seg1 : segOK pH1758 1 1014 (init pH1758) (init pH1758) H1758_cp1.1 H1758_cp1.2 = true := by
  decide +kernel
noncomputable def H1758_cp2 : Nat × Nat := t7val% (fastRun pH1758 1 1434 (init pH1758) (init pH1758))
theorem H1758_seg2 : segOK pH1758 1015 420 H1758_cp1.1 H1758_cp1.2 H1758_cp2.1 H1758_cp2.2 = true := by
  decide +kernel
theorem H1758_fin : (prmOK pH1758 1758 && ptTest pH1758 (runFrom pH1758 (fmask pH1758) (cmask pH1758) (hmask pH1758) 1435 323 (true, H1758_cp2.1, H1758_cp2.2)) 1758 879 true) = true := by
  decide +kernel
theorem H1758_ok : RunOK pH1758 1758 (runFrom pH1758 (fmask pH1758) (cmask pH1758) (hmask pH1758) 1435 323 (true, H1758_cp2.1, H1758_cp2.2)) ∧ ptTest pH1758 (runFrom pH1758 (fmask pH1758) (cmask pH1758) (hmask pH1758) 1435 323 (true, H1758_cp2.1, H1758_cp2.2)) 1758 879 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1758_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1758_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1758_fin) true) H1758_seg1) H1758_seg2) (by decide) rfl H1758_fin ptTest_fst
noncomputable def I1758_cp1 : Nat × Nat := t7val% (fastRun pI1758 1 1242 (init pI1758) (init pI1758))
theorem I1758_seg1 : segOK pI1758 1 1242 (init pI1758) (init pI1758) I1758_cp1.1 I1758_cp1.2 = true := by
  decide +kernel
theorem I1758_fin : (prmOK pI1758 1758 && intTest pI1758 (runFrom pI1758 (fmask pI1758) (cmask pI1758) (hmask pI1758) 1243 515 (true, I1758_cp1.1, I1758_cp1.2)) 1758 21 true) = true := by
  decide +kernel
theorem I1758_ok : RunOK pI1758 1758 (runFrom pI1758 (fmask pI1758) (cmask pI1758) (hmask pI1758) 1243 515 (true, I1758_cp1.1, I1758_cp1.2)) ∧ intTest pI1758 (runFrom pI1758 (fmask pI1758) (cmask pI1758) (hmask pI1758) 1243 515 (true, I1758_cp1.1, I1758_cp1.2)) 1758 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1758_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1758_fin) true) I1758_seg1) (by decide) rfl I1758_fin intTest_fst
theorem link1758 : linkOK pL1758 pH1758 pI1758 = true := by decide +kernel
theorem cvx1758 : ConvexBetweenHumps 1758 :=
  cvx_of L1758_ok H1758_ok I1758_ok link1758 (by decide)
theorem cenlink1758 : cenLinkOK pI1758 1758 = true := by decide +kernel
theorem cen1758 : CenterUniqueMin 1758 ∧ DipHyp 1758 ∧ OnePointHyps 1758 :=
  cen_of L1758_ok H1758_ok I1758_ok link1758 cenlink1758

/-! ### `N = 1759` -/

def pL1759 : Prm := ⟨80, 37, 40, 1761, 11, 18446744073709551616, 109266024516102064, 109266024516102064⟩
def pH1759 : Prm := ⟨80, 37, 40, 1761, 11, 18446744073709551616, 109267124027729840, 109267124027729840⟩
def pI1759 : Prm := ⟨67, 34, 30, 1761, 11, 18446744073709551616, 109266024516102064, 109267124027729840⟩
noncomputable def L1759_cp1 : Nat × Nat := t7val% (fastRun pL1759 1 1015 (init pL1759) (init pL1759))
theorem L1759_seg1 : segOK pL1759 1 1015 (init pL1759) (init pL1759) L1759_cp1.1 L1759_cp1.2 = true := by
  decide +kernel
noncomputable def L1759_cp2 : Nat × Nat := t7val% (fastRun pL1759 1 1435 (init pL1759) (init pL1759))
theorem L1759_seg2 : segOK pL1759 1016 420 L1759_cp1.1 L1759_cp1.2 L1759_cp2.1 L1759_cp2.2 = true := by
  decide +kernel
theorem L1759_fin : (prmOK pL1759 1759 && ptTest pL1759 (runFrom pL1759 (fmask pL1759) (cmask pL1759) (hmask pL1759) 1436 323 (true, L1759_cp2.1, L1759_cp2.2)) 1759 880 false) = true := by
  decide +kernel
theorem L1759_ok : RunOK pL1759 1759 (runFrom pL1759 (fmask pL1759) (cmask pL1759) (hmask pL1759) 1436 323 (true, L1759_cp2.1, L1759_cp2.2)) ∧ ptTest pL1759 (runFrom pL1759 (fmask pL1759) (cmask pL1759) (hmask pL1759) 1436 323 (true, L1759_cp2.1, L1759_cp2.2)) 1759 880 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1759_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1759_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1759_fin) true) L1759_seg1) L1759_seg2) (by decide) rfl L1759_fin ptTest_fst
noncomputable def H1759_cp1 : Nat × Nat := t7val% (fastRun pH1759 1 1015 (init pH1759) (init pH1759))
theorem H1759_seg1 : segOK pH1759 1 1015 (init pH1759) (init pH1759) H1759_cp1.1 H1759_cp1.2 = true := by
  decide +kernel
noncomputable def H1759_cp2 : Nat × Nat := t7val% (fastRun pH1759 1 1435 (init pH1759) (init pH1759))
theorem H1759_seg2 : segOK pH1759 1016 420 H1759_cp1.1 H1759_cp1.2 H1759_cp2.1 H1759_cp2.2 = true := by
  decide +kernel
theorem H1759_fin : (prmOK pH1759 1759 && ptTest pH1759 (runFrom pH1759 (fmask pH1759) (cmask pH1759) (hmask pH1759) 1436 323 (true, H1759_cp2.1, H1759_cp2.2)) 1759 880 true) = true := by
  decide +kernel
theorem H1759_ok : RunOK pH1759 1759 (runFrom pH1759 (fmask pH1759) (cmask pH1759) (hmask pH1759) 1436 323 (true, H1759_cp2.1, H1759_cp2.2)) ∧ ptTest pH1759 (runFrom pH1759 (fmask pH1759) (cmask pH1759) (hmask pH1759) 1436 323 (true, H1759_cp2.1, H1759_cp2.2)) 1759 880 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1759_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1759_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1759_fin) true) H1759_seg1) H1759_seg2) (by decide) rfl H1759_fin ptTest_fst
noncomputable def I1759_cp1 : Nat × Nat := t7val% (fastRun pI1759 1 1243 (init pI1759) (init pI1759))
theorem I1759_seg1 : segOK pI1759 1 1243 (init pI1759) (init pI1759) I1759_cp1.1 I1759_cp1.2 = true := by
  decide +kernel
theorem I1759_fin : (prmOK pI1759 1759 && intTest pI1759 (runFrom pI1759 (fmask pI1759) (cmask pI1759) (hmask pI1759) 1244 515 (true, I1759_cp1.1, I1759_cp1.2)) 1759 21 false) = true := by
  decide +kernel
theorem I1759_ok : RunOK pI1759 1759 (runFrom pI1759 (fmask pI1759) (cmask pI1759) (hmask pI1759) 1244 515 (true, I1759_cp1.1, I1759_cp1.2)) ∧ intTest pI1759 (runFrom pI1759 (fmask pI1759) (cmask pI1759) (hmask pI1759) 1244 515 (true, I1759_cp1.1, I1759_cp1.2)) 1759 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1759_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1759_fin) true) I1759_seg1) (by decide) rfl I1759_fin intTest_fst
theorem link1759 : linkOK pL1759 pH1759 pI1759 = true := by decide +kernel
theorem cvx1759 : ConvexBetweenHumps 1759 :=
  cvx_of L1759_ok H1759_ok I1759_ok link1759 (by decide)

/-! ### The range -/

theorem cvx_1747_1759 {N : ℕ} (h1 : 1747 ≤ N) (h2 : N ≤ 1759) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1752
  · by_cases h4 : N ≤ 1749
    · by_cases h6 : N ≤ 1747
      · obtain rfl : N = 1747 := by omega
        exact cvx1747
      · by_cases h8 : N ≤ 1748
        · obtain rfl : N = 1748 := by omega
          exact cvx1748
        · obtain rfl : N = 1749 := by omega
          exact cvx1749
    · by_cases h6 : N ≤ 1750
      · obtain rfl : N = 1750 := by omega
        exact cvx1750
      · by_cases h8 : N ≤ 1751
        · obtain rfl : N = 1751 := by omega
          exact cvx1751
        · obtain rfl : N = 1752 := by omega
          exact cvx1752
  · by_cases h4 : N ≤ 1755
    · by_cases h6 : N ≤ 1753
      · obtain rfl : N = 1753 := by omega
        exact cvx1753
      · by_cases h8 : N ≤ 1754
        · obtain rfl : N = 1754 := by omega
          exact cvx1754
        · obtain rfl : N = 1755 := by omega
          exact cvx1755
    · by_cases h6 : N ≤ 1757
      · by_cases h8 : N ≤ 1756
        · obtain rfl : N = 1756 := by omega
          exact cvx1756
        · obtain rfl : N = 1757 := by omega
          exact cvx1757
      · by_cases h8 : N ≤ 1758
        · obtain rfl : N = 1758 := by omega
          exact cvx1758
        · obtain rfl : N = 1759 := by omega
          exact cvx1759

theorem cen_1747_1759 {N : ℕ} (h1 : 1747 ≤ N) (h2 : N ≤ 1759) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1752
  · by_cases h4 : N ≤ 1748
    · obtain rfl : N = 1748 := by omega
      exact cen1748
    · by_cases h6 : N ≤ 1750
      · obtain rfl : N = 1750 := by omega
        exact cen1750
      · obtain rfl : N = 1752 := by omega
        exact cen1752
  · by_cases h4 : N ≤ 1754
    · obtain rfl : N = 1754 := by omega
      exact cen1754
    · by_cases h6 : N ≤ 1756
      · obtain rfl : N = 1756 := by omega
        exact cen1756
      · obtain rfl : N = 1758 := by omega
        exact cen1758

end Kagey131.PaperD.T7
