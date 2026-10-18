import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1460, …, 1477` (generated)

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

/-! ### `N = 1460` -/

def pL1460 : Prm := ⟨80, 38, 39, 1462, 11, 18446744073709551616, 127205117295258100, 127205117295258100⟩
def pH1460 : Prm := ⟨80, 38, 39, 1462, 11, 18446744073709551616, 127206216806885876, 127206216806885876⟩
def pI1460 : Prm := ⟨66, 33, 30, 1462, 11, 18446744073709551616, 127205117295258100, 127206216806885876⟩
noncomputable def L1460_cp1 : Nat × Nat := t7val% (fastRun pL1460 1 1031 (init pL1460) (init pL1460))
theorem L1460_seg1 : segOK pL1460 1 1031 (init pL1460) (init pL1460) L1460_cp1.1 L1460_cp1.2 = true := by
  decide +kernel
theorem L1460_fin : (prmOK pL1460 1460 && ptTest pL1460 (runFrom pL1460 (fmask pL1460) (cmask pL1460) (hmask pL1460) 1032 428 (true, L1460_cp1.1, L1460_cp1.2)) 1460 730 false) = true := by
  decide +kernel
theorem L1460_ok : RunOK pL1460 1460 (runFrom pL1460 (fmask pL1460) (cmask pL1460) (hmask pL1460) 1032 428 (true, L1460_cp1.1, L1460_cp1.2)) ∧ ptTest pL1460 (runFrom pL1460 (fmask pL1460) (cmask pL1460) (hmask pL1460) 1032 428 (true, L1460_cp1.1, L1460_cp1.2)) 1460 730 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1460_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1460_fin) true) L1460_seg1) (by decide) rfl L1460_fin ptTest_fst
noncomputable def H1460_cp1 : Nat × Nat := t7val% (fastRun pH1460 1 1031 (init pH1460) (init pH1460))
theorem H1460_seg1 : segOK pH1460 1 1031 (init pH1460) (init pH1460) H1460_cp1.1 H1460_cp1.2 = true := by
  decide +kernel
theorem H1460_fin : (prmOK pH1460 1460 && ptTest pH1460 (runFrom pH1460 (fmask pH1460) (cmask pH1460) (hmask pH1460) 1032 428 (true, H1460_cp1.1, H1460_cp1.2)) 1460 730 true) = true := by
  decide +kernel
theorem H1460_ok : RunOK pH1460 1460 (runFrom pH1460 (fmask pH1460) (cmask pH1460) (hmask pH1460) 1032 428 (true, H1460_cp1.1, H1460_cp1.2)) ∧ ptTest pH1460 (runFrom pH1460 (fmask pH1460) (cmask pH1460) (hmask pH1460) 1032 428 (true, H1460_cp1.1, H1460_cp1.2)) 1460 730 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1460_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1460_fin) true) H1460_seg1) (by decide) rfl H1460_fin ptTest_fst
noncomputable def I1460_cp1 : Nat × Nat := t7val% (fastRun pI1460 1 1031 (init pI1460) (init pI1460))
theorem I1460_seg1 : segOK pI1460 1 1031 (init pI1460) (init pI1460) I1460_cp1.1 I1460_cp1.2 = true := by
  decide +kernel
theorem I1460_fin : (prmOK pI1460 1460 && intTest pI1460 (runFrom pI1460 (fmask pI1460) (cmask pI1460) (hmask pI1460) 1032 428 (true, I1460_cp1.1, I1460_cp1.2)) 1460 20 true) = true := by
  decide +kernel
theorem I1460_ok : RunOK pI1460 1460 (runFrom pI1460 (fmask pI1460) (cmask pI1460) (hmask pI1460) 1032 428 (true, I1460_cp1.1, I1460_cp1.2)) ∧ intTest pI1460 (runFrom pI1460 (fmask pI1460) (cmask pI1460) (hmask pI1460) 1032 428 (true, I1460_cp1.1, I1460_cp1.2)) 1460 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1460_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1460_fin) true) I1460_seg1) (by decide) rfl I1460_fin intTest_fst
theorem link1460 : linkOK pL1460 pH1460 pI1460 = true := by decide +kernel
theorem cvx1460 : ConvexBetweenHumps 1460 :=
  cvx_of L1460_ok H1460_ok I1460_ok link1460 (by decide)
theorem cenlink1460 : cenLinkOK pI1460 1460 = true := by decide +kernel
theorem cen1460 : CenterUniqueMin 1460 ∧ DipHyp 1460 ∧ OnePointHyps 1460 :=
  cen_of L1460_ok H1460_ok I1460_ok link1460 cenlink1460

/-! ### `N = 1461` -/

def pL1461 : Prm := ⟨80, 38, 39, 1463, 11, 18446744073709551616, 127134332584963650, 127134332584963650⟩
def pH1461 : Prm := ⟨80, 38, 39, 1463, 11, 18446744073709551616, 127135432096591426, 127135432096591426⟩
def pI1461 : Prm := ⟨66, 33, 30, 1463, 11, 18446744073709551616, 127134332584963650, 127135432096591426⟩
noncomputable def L1461_cp1 : Nat × Nat := t7val% (fastRun pL1461 1 1032 (init pL1461) (init pL1461))
theorem L1461_seg1 : segOK pL1461 1 1032 (init pL1461) (init pL1461) L1461_cp1.1 L1461_cp1.2 = true := by
  decide +kernel
theorem L1461_fin : (prmOK pL1461 1461 && ptTest pL1461 (runFrom pL1461 (fmask pL1461) (cmask pL1461) (hmask pL1461) 1033 428 (true, L1461_cp1.1, L1461_cp1.2)) 1461 731 false) = true := by
  decide +kernel
theorem L1461_ok : RunOK pL1461 1461 (runFrom pL1461 (fmask pL1461) (cmask pL1461) (hmask pL1461) 1033 428 (true, L1461_cp1.1, L1461_cp1.2)) ∧ ptTest pL1461 (runFrom pL1461 (fmask pL1461) (cmask pL1461) (hmask pL1461) 1033 428 (true, L1461_cp1.1, L1461_cp1.2)) 1461 731 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1461_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1461_fin) true) L1461_seg1) (by decide) rfl L1461_fin ptTest_fst
noncomputable def H1461_cp1 : Nat × Nat := t7val% (fastRun pH1461 1 1032 (init pH1461) (init pH1461))
theorem H1461_seg1 : segOK pH1461 1 1032 (init pH1461) (init pH1461) H1461_cp1.1 H1461_cp1.2 = true := by
  decide +kernel
theorem H1461_fin : (prmOK pH1461 1461 && ptTest pH1461 (runFrom pH1461 (fmask pH1461) (cmask pH1461) (hmask pH1461) 1033 428 (true, H1461_cp1.1, H1461_cp1.2)) 1461 731 true) = true := by
  decide +kernel
theorem H1461_ok : RunOK pH1461 1461 (runFrom pH1461 (fmask pH1461) (cmask pH1461) (hmask pH1461) 1033 428 (true, H1461_cp1.1, H1461_cp1.2)) ∧ ptTest pH1461 (runFrom pH1461 (fmask pH1461) (cmask pH1461) (hmask pH1461) 1033 428 (true, H1461_cp1.1, H1461_cp1.2)) 1461 731 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1461_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1461_fin) true) H1461_seg1) (by decide) rfl H1461_fin ptTest_fst
noncomputable def I1461_cp1 : Nat × Nat := t7val% (fastRun pI1461 1 1032 (init pI1461) (init pI1461))
theorem I1461_seg1 : segOK pI1461 1 1032 (init pI1461) (init pI1461) I1461_cp1.1 I1461_cp1.2 = true := by
  decide +kernel
theorem I1461_fin : (prmOK pI1461 1461 && intTest pI1461 (runFrom pI1461 (fmask pI1461) (cmask pI1461) (hmask pI1461) 1033 428 (true, I1461_cp1.1, I1461_cp1.2)) 1461 20 false) = true := by
  decide +kernel
theorem I1461_ok : RunOK pI1461 1461 (runFrom pI1461 (fmask pI1461) (cmask pI1461) (hmask pI1461) 1033 428 (true, I1461_cp1.1, I1461_cp1.2)) ∧ intTest pI1461 (runFrom pI1461 (fmask pI1461) (cmask pI1461) (hmask pI1461) 1033 428 (true, I1461_cp1.1, I1461_cp1.2)) 1461 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1461_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1461_fin) true) I1461_seg1) (by decide) rfl I1461_fin intTest_fst
theorem link1461 : linkOK pL1461 pH1461 pI1461 = true := by decide +kernel
theorem cvx1461 : ConvexBetweenHumps 1461 :=
  cvx_of L1461_ok H1461_ok I1461_ok link1461 (by decide)

/-! ### `N = 1462` -/

def pL1462 : Prm := ⟨80, 38, 39, 1464, 11, 18446744073709551616, 127063669869739267, 127063669869739267⟩
def pH1462 : Prm := ⟨80, 38, 39, 1464, 11, 18446744073709551616, 127064769381367043, 127064769381367043⟩
def pI1462 : Prm := ⟨66, 33, 30, 1464, 11, 18446744073709551616, 127063669869739267, 127064769381367043⟩
noncomputable def L1462_cp1 : Nat × Nat := t7val% (fastRun pL1462 1 1033 (init pL1462) (init pL1462))
theorem L1462_seg1 : segOK pL1462 1 1033 (init pL1462) (init pL1462) L1462_cp1.1 L1462_cp1.2 = true := by
  decide +kernel
theorem L1462_fin : (prmOK pL1462 1462 && ptTest pL1462 (runFrom pL1462 (fmask pL1462) (cmask pL1462) (hmask pL1462) 1034 428 (true, L1462_cp1.1, L1462_cp1.2)) 1462 731 false) = true := by
  decide +kernel
theorem L1462_ok : RunOK pL1462 1462 (runFrom pL1462 (fmask pL1462) (cmask pL1462) (hmask pL1462) 1034 428 (true, L1462_cp1.1, L1462_cp1.2)) ∧ ptTest pL1462 (runFrom pL1462 (fmask pL1462) (cmask pL1462) (hmask pL1462) 1034 428 (true, L1462_cp1.1, L1462_cp1.2)) 1462 731 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1462_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1462_fin) true) L1462_seg1) (by decide) rfl L1462_fin ptTest_fst
noncomputable def H1462_cp1 : Nat × Nat := t7val% (fastRun pH1462 1 1033 (init pH1462) (init pH1462))
theorem H1462_seg1 : segOK pH1462 1 1033 (init pH1462) (init pH1462) H1462_cp1.1 H1462_cp1.2 = true := by
  decide +kernel
theorem H1462_fin : (prmOK pH1462 1462 && ptTest pH1462 (runFrom pH1462 (fmask pH1462) (cmask pH1462) (hmask pH1462) 1034 428 (true, H1462_cp1.1, H1462_cp1.2)) 1462 731 true) = true := by
  decide +kernel
theorem H1462_ok : RunOK pH1462 1462 (runFrom pH1462 (fmask pH1462) (cmask pH1462) (hmask pH1462) 1034 428 (true, H1462_cp1.1, H1462_cp1.2)) ∧ ptTest pH1462 (runFrom pH1462 (fmask pH1462) (cmask pH1462) (hmask pH1462) 1034 428 (true, H1462_cp1.1, H1462_cp1.2)) 1462 731 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1462_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1462_fin) true) H1462_seg1) (by decide) rfl H1462_fin ptTest_fst
noncomputable def I1462_cp1 : Nat × Nat := t7val% (fastRun pI1462 1 1033 (init pI1462) (init pI1462))
theorem I1462_seg1 : segOK pI1462 1 1033 (init pI1462) (init pI1462) I1462_cp1.1 I1462_cp1.2 = true := by
  decide +kernel
theorem I1462_fin : (prmOK pI1462 1462 && intTest pI1462 (runFrom pI1462 (fmask pI1462) (cmask pI1462) (hmask pI1462) 1034 428 (true, I1462_cp1.1, I1462_cp1.2)) 1462 20 true) = true := by
  decide +kernel
theorem I1462_ok : RunOK pI1462 1462 (runFrom pI1462 (fmask pI1462) (cmask pI1462) (hmask pI1462) 1034 428 (true, I1462_cp1.1, I1462_cp1.2)) ∧ intTest pI1462 (runFrom pI1462 (fmask pI1462) (cmask pI1462) (hmask pI1462) 1034 428 (true, I1462_cp1.1, I1462_cp1.2)) 1462 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1462_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1462_fin) true) I1462_seg1) (by decide) rfl I1462_fin intTest_fst
theorem link1462 : linkOK pL1462 pH1462 pI1462 = true := by decide +kernel
theorem cvx1462 : ConvexBetweenHumps 1462 :=
  cvx_of L1462_ok H1462_ok I1462_ok link1462 (by decide)
theorem cenlink1462 : cenLinkOK pI1462 1462 = true := by decide +kernel
theorem cen1462 : CenterUniqueMin 1462 ∧ DipHyp 1462 ∧ OnePointHyps 1462 :=
  cen_of L1462_ok H1462_ok I1462_ok link1462 cenlink1462

/-! ### `N = 1463` -/

def pL1463 : Prm := ⟨80, 38, 39, 1465, 11, 18446744073709551616, 126993056373932955, 126993056373932955⟩
def pH1463 : Prm := ⟨80, 38, 39, 1465, 11, 18446744073709551616, 126994155885560731, 126994155885560731⟩
def pI1463 : Prm := ⟨66, 33, 30, 1465, 11, 18446744073709551616, 126993056373932955, 126994155885560731⟩
noncomputable def L1463_cp1 : Nat × Nat := t7val% (fastRun pL1463 1 1033 (init pL1463) (init pL1463))
theorem L1463_seg1 : segOK pL1463 1 1033 (init pL1463) (init pL1463) L1463_cp1.1 L1463_cp1.2 = true := by
  decide +kernel
theorem L1463_fin : (prmOK pL1463 1463 && ptTest pL1463 (runFrom pL1463 (fmask pL1463) (cmask pL1463) (hmask pL1463) 1034 429 (true, L1463_cp1.1, L1463_cp1.2)) 1463 732 false) = true := by
  decide +kernel
theorem L1463_ok : RunOK pL1463 1463 (runFrom pL1463 (fmask pL1463) (cmask pL1463) (hmask pL1463) 1034 429 (true, L1463_cp1.1, L1463_cp1.2)) ∧ ptTest pL1463 (runFrom pL1463 (fmask pL1463) (cmask pL1463) (hmask pL1463) 1034 429 (true, L1463_cp1.1, L1463_cp1.2)) 1463 732 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1463_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1463_fin) true) L1463_seg1) (by decide) rfl L1463_fin ptTest_fst
noncomputable def H1463_cp1 : Nat × Nat := t7val% (fastRun pH1463 1 1033 (init pH1463) (init pH1463))
theorem H1463_seg1 : segOK pH1463 1 1033 (init pH1463) (init pH1463) H1463_cp1.1 H1463_cp1.2 = true := by
  decide +kernel
theorem H1463_fin : (prmOK pH1463 1463 && ptTest pH1463 (runFrom pH1463 (fmask pH1463) (cmask pH1463) (hmask pH1463) 1034 429 (true, H1463_cp1.1, H1463_cp1.2)) 1463 732 true) = true := by
  decide +kernel
theorem H1463_ok : RunOK pH1463 1463 (runFrom pH1463 (fmask pH1463) (cmask pH1463) (hmask pH1463) 1034 429 (true, H1463_cp1.1, H1463_cp1.2)) ∧ ptTest pH1463 (runFrom pH1463 (fmask pH1463) (cmask pH1463) (hmask pH1463) 1034 429 (true, H1463_cp1.1, H1463_cp1.2)) 1463 732 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1463_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1463_fin) true) H1463_seg1) (by decide) rfl H1463_fin ptTest_fst
noncomputable def I1463_cp1 : Nat × Nat := t7val% (fastRun pI1463 1 1033 (init pI1463) (init pI1463))
theorem I1463_seg1 : segOK pI1463 1 1033 (init pI1463) (init pI1463) I1463_cp1.1 I1463_cp1.2 = true := by
  decide +kernel
theorem I1463_fin : (prmOK pI1463 1463 && intTest pI1463 (runFrom pI1463 (fmask pI1463) (cmask pI1463) (hmask pI1463) 1034 429 (true, I1463_cp1.1, I1463_cp1.2)) 1463 20 false) = true := by
  decide +kernel
theorem I1463_ok : RunOK pI1463 1463 (runFrom pI1463 (fmask pI1463) (cmask pI1463) (hmask pI1463) 1034 429 (true, I1463_cp1.1, I1463_cp1.2)) ∧ intTest pI1463 (runFrom pI1463 (fmask pI1463) (cmask pI1463) (hmask pI1463) 1034 429 (true, I1463_cp1.1, I1463_cp1.2)) 1463 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1463_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1463_fin) true) I1463_seg1) (by decide) rfl I1463_fin intTest_fst
theorem link1463 : linkOK pL1463 pH1463 pI1463 = true := by decide +kernel
theorem cvx1463 : ConvexBetweenHumps 1463 :=
  cvx_of L1463_ok H1463_ok I1463_ok link1463 (by decide)

/-! ### `N = 1464` -/

def pL1464 : Prm := ⟨80, 38, 39, 1466, 11, 18446744073709551616, 126922564401513464, 126922564401513464⟩
def pH1464 : Prm := ⟨80, 38, 39, 1466, 11, 18446744073709551616, 126923663913141240, 126923663913141240⟩
def pI1464 : Prm := ⟨66, 33, 30, 1466, 11, 18446744073709551616, 126922564401513464, 126923663913141240⟩
noncomputable def L1464_cp1 : Nat × Nat := t7val% (fastRun pL1464 1 1034 (init pL1464) (init pL1464))
theorem L1464_seg1 : segOK pL1464 1 1034 (init pL1464) (init pL1464) L1464_cp1.1 L1464_cp1.2 = true := by
  decide +kernel
theorem L1464_fin : (prmOK pL1464 1464 && ptTest pL1464 (runFrom pL1464 (fmask pL1464) (cmask pL1464) (hmask pL1464) 1035 429 (true, L1464_cp1.1, L1464_cp1.2)) 1464 732 false) = true := by
  decide +kernel
theorem L1464_ok : RunOK pL1464 1464 (runFrom pL1464 (fmask pL1464) (cmask pL1464) (hmask pL1464) 1035 429 (true, L1464_cp1.1, L1464_cp1.2)) ∧ ptTest pL1464 (runFrom pL1464 (fmask pL1464) (cmask pL1464) (hmask pL1464) 1035 429 (true, L1464_cp1.1, L1464_cp1.2)) 1464 732 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1464_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1464_fin) true) L1464_seg1) (by decide) rfl L1464_fin ptTest_fst
noncomputable def H1464_cp1 : Nat × Nat := t7val% (fastRun pH1464 1 1034 (init pH1464) (init pH1464))
theorem H1464_seg1 : segOK pH1464 1 1034 (init pH1464) (init pH1464) H1464_cp1.1 H1464_cp1.2 = true := by
  decide +kernel
theorem H1464_fin : (prmOK pH1464 1464 && ptTest pH1464 (runFrom pH1464 (fmask pH1464) (cmask pH1464) (hmask pH1464) 1035 429 (true, H1464_cp1.1, H1464_cp1.2)) 1464 732 true) = true := by
  decide +kernel
theorem H1464_ok : RunOK pH1464 1464 (runFrom pH1464 (fmask pH1464) (cmask pH1464) (hmask pH1464) 1035 429 (true, H1464_cp1.1, H1464_cp1.2)) ∧ ptTest pH1464 (runFrom pH1464 (fmask pH1464) (cmask pH1464) (hmask pH1464) 1035 429 (true, H1464_cp1.1, H1464_cp1.2)) 1464 732 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1464_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1464_fin) true) H1464_seg1) (by decide) rfl H1464_fin ptTest_fst
noncomputable def I1464_cp1 : Nat × Nat := t7val% (fastRun pI1464 1 1034 (init pI1464) (init pI1464))
theorem I1464_seg1 : segOK pI1464 1 1034 (init pI1464) (init pI1464) I1464_cp1.1 I1464_cp1.2 = true := by
  decide +kernel
theorem I1464_fin : (prmOK pI1464 1464 && intTest pI1464 (runFrom pI1464 (fmask pI1464) (cmask pI1464) (hmask pI1464) 1035 429 (true, I1464_cp1.1, I1464_cp1.2)) 1464 20 true) = true := by
  decide +kernel
theorem I1464_ok : RunOK pI1464 1464 (runFrom pI1464 (fmask pI1464) (cmask pI1464) (hmask pI1464) 1035 429 (true, I1464_cp1.1, I1464_cp1.2)) ∧ intTest pI1464 (runFrom pI1464 (fmask pI1464) (cmask pI1464) (hmask pI1464) 1035 429 (true, I1464_cp1.1, I1464_cp1.2)) 1464 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1464_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1464_fin) true) I1464_seg1) (by decide) rfl I1464_fin intTest_fst
theorem link1464 : linkOK pL1464 pH1464 pI1464 = true := by decide +kernel
theorem cvx1464 : ConvexBetweenHumps 1464 :=
  cvx_of L1464_ok H1464_ok I1464_ok link1464 (by decide)
theorem cenlink1464 : cenLinkOK pI1464 1464 = true := by decide +kernel
theorem cen1464 : CenterUniqueMin 1464 ∧ DipHyp 1464 ∧ OnePointHyps 1464 :=
  cen_of L1464_ok H1464_ok I1464_ok link1464 cenlink1464

/-! ### `N = 1465` -/

def pL1465 : Prm := ⟨80, 38, 39, 1467, 11, 18446744073709551616, 126852121479816569, 126852121479816569⟩
def pH1465 : Prm := ⟨80, 38, 39, 1467, 11, 18446744073709551616, 126853220991444345, 126853220991444345⟩
def pI1465 : Prm := ⟨66, 33, 30, 1467, 11, 18446744073709551616, 126852121479816569, 126853220991444345⟩
noncomputable def L1465_cp1 : Nat × Nat := t7val% (fastRun pL1465 1 1035 (init pL1465) (init pL1465))
theorem L1465_seg1 : segOK pL1465 1 1035 (init pL1465) (init pL1465) L1465_cp1.1 L1465_cp1.2 = true := by
  decide +kernel
theorem L1465_fin : (prmOK pL1465 1465 && ptTest pL1465 (runFrom pL1465 (fmask pL1465) (cmask pL1465) (hmask pL1465) 1036 429 (true, L1465_cp1.1, L1465_cp1.2)) 1465 733 false) = true := by
  decide +kernel
theorem L1465_ok : RunOK pL1465 1465 (runFrom pL1465 (fmask pL1465) (cmask pL1465) (hmask pL1465) 1036 429 (true, L1465_cp1.1, L1465_cp1.2)) ∧ ptTest pL1465 (runFrom pL1465 (fmask pL1465) (cmask pL1465) (hmask pL1465) 1036 429 (true, L1465_cp1.1, L1465_cp1.2)) 1465 733 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1465_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1465_fin) true) L1465_seg1) (by decide) rfl L1465_fin ptTest_fst
noncomputable def H1465_cp1 : Nat × Nat := t7val% (fastRun pH1465 1 1035 (init pH1465) (init pH1465))
theorem H1465_seg1 : segOK pH1465 1 1035 (init pH1465) (init pH1465) H1465_cp1.1 H1465_cp1.2 = true := by
  decide +kernel
theorem H1465_fin : (prmOK pH1465 1465 && ptTest pH1465 (runFrom pH1465 (fmask pH1465) (cmask pH1465) (hmask pH1465) 1036 429 (true, H1465_cp1.1, H1465_cp1.2)) 1465 733 true) = true := by
  decide +kernel
theorem H1465_ok : RunOK pH1465 1465 (runFrom pH1465 (fmask pH1465) (cmask pH1465) (hmask pH1465) 1036 429 (true, H1465_cp1.1, H1465_cp1.2)) ∧ ptTest pH1465 (runFrom pH1465 (fmask pH1465) (cmask pH1465) (hmask pH1465) 1036 429 (true, H1465_cp1.1, H1465_cp1.2)) 1465 733 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1465_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1465_fin) true) H1465_seg1) (by decide) rfl H1465_fin ptTest_fst
noncomputable def I1465_cp1 : Nat × Nat := t7val% (fastRun pI1465 1 1035 (init pI1465) (init pI1465))
theorem I1465_seg1 : segOK pI1465 1 1035 (init pI1465) (init pI1465) I1465_cp1.1 I1465_cp1.2 = true := by
  decide +kernel
theorem I1465_fin : (prmOK pI1465 1465 && intTest pI1465 (runFrom pI1465 (fmask pI1465) (cmask pI1465) (hmask pI1465) 1036 429 (true, I1465_cp1.1, I1465_cp1.2)) 1465 20 false) = true := by
  decide +kernel
theorem I1465_ok : RunOK pI1465 1465 (runFrom pI1465 (fmask pI1465) (cmask pI1465) (hmask pI1465) 1036 429 (true, I1465_cp1.1, I1465_cp1.2)) ∧ intTest pI1465 (runFrom pI1465 (fmask pI1465) (cmask pI1465) (hmask pI1465) 1036 429 (true, I1465_cp1.1, I1465_cp1.2)) 1465 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1465_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1465_fin) true) I1465_seg1) (by decide) rfl I1465_fin intTest_fst
theorem link1465 : linkOK pL1465 pH1465 pI1465 = true := by decide +kernel
theorem cvx1465 : ConvexBetweenHumps 1465 :=
  cvx_of L1465_ok H1465_ok I1465_ok link1465 (by decide)

/-! ### `N = 1466` -/

def pL1466 : Prm := ⟨80, 38, 39, 1468, 11, 18446744073709551616, 126781799612313560, 126781799612313560⟩
def pH1466 : Prm := ⟨80, 38, 39, 1468, 11, 18446744073709551616, 126782899123941336, 126782899123941336⟩
def pI1466 : Prm := ⟨66, 33, 30, 1468, 11, 18446744073709551616, 126781799612313560, 126782899123941336⟩
noncomputable def L1466_cp1 : Nat × Nat := t7val% (fastRun pL1466 1 1036 (init pL1466) (init pL1466))
theorem L1466_seg1 : segOK pL1466 1 1036 (init pL1466) (init pL1466) L1466_cp1.1 L1466_cp1.2 = true := by
  decide +kernel
theorem L1466_fin : (prmOK pL1466 1466 && ptTest pL1466 (runFrom pL1466 (fmask pL1466) (cmask pL1466) (hmask pL1466) 1037 429 (true, L1466_cp1.1, L1466_cp1.2)) 1466 733 false) = true := by
  decide +kernel
theorem L1466_ok : RunOK pL1466 1466 (runFrom pL1466 (fmask pL1466) (cmask pL1466) (hmask pL1466) 1037 429 (true, L1466_cp1.1, L1466_cp1.2)) ∧ ptTest pL1466 (runFrom pL1466 (fmask pL1466) (cmask pL1466) (hmask pL1466) 1037 429 (true, L1466_cp1.1, L1466_cp1.2)) 1466 733 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1466_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1466_fin) true) L1466_seg1) (by decide) rfl L1466_fin ptTest_fst
noncomputable def H1466_cp1 : Nat × Nat := t7val% (fastRun pH1466 1 1036 (init pH1466) (init pH1466))
theorem H1466_seg1 : segOK pH1466 1 1036 (init pH1466) (init pH1466) H1466_cp1.1 H1466_cp1.2 = true := by
  decide +kernel
theorem H1466_fin : (prmOK pH1466 1466 && ptTest pH1466 (runFrom pH1466 (fmask pH1466) (cmask pH1466) (hmask pH1466) 1037 429 (true, H1466_cp1.1, H1466_cp1.2)) 1466 733 true) = true := by
  decide +kernel
theorem H1466_ok : RunOK pH1466 1466 (runFrom pH1466 (fmask pH1466) (cmask pH1466) (hmask pH1466) 1037 429 (true, H1466_cp1.1, H1466_cp1.2)) ∧ ptTest pH1466 (runFrom pH1466 (fmask pH1466) (cmask pH1466) (hmask pH1466) 1037 429 (true, H1466_cp1.1, H1466_cp1.2)) 1466 733 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1466_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1466_fin) true) H1466_seg1) (by decide) rfl H1466_fin ptTest_fst
noncomputable def I1466_cp1 : Nat × Nat := t7val% (fastRun pI1466 1 1036 (init pI1466) (init pI1466))
theorem I1466_seg1 : segOK pI1466 1 1036 (init pI1466) (init pI1466) I1466_cp1.1 I1466_cp1.2 = true := by
  decide +kernel
theorem I1466_fin : (prmOK pI1466 1466 && intTest pI1466 (runFrom pI1466 (fmask pI1466) (cmask pI1466) (hmask pI1466) 1037 429 (true, I1466_cp1.1, I1466_cp1.2)) 1466 20 true) = true := by
  decide +kernel
theorem I1466_ok : RunOK pI1466 1466 (runFrom pI1466 (fmask pI1466) (cmask pI1466) (hmask pI1466) 1037 429 (true, I1466_cp1.1, I1466_cp1.2)) ∧ intTest pI1466 (runFrom pI1466 (fmask pI1466) (cmask pI1466) (hmask pI1466) 1037 429 (true, I1466_cp1.1, I1466_cp1.2)) 1466 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1466_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1466_fin) true) I1466_seg1) (by decide) rfl I1466_fin intTest_fst
theorem link1466 : linkOK pL1466 pH1466 pI1466 = true := by decide +kernel
theorem cvx1466 : ConvexBetweenHumps 1466 :=
  cvx_of L1466_ok H1466_ok I1466_ok link1466 (by decide)
theorem cenlink1466 : cenLinkOK pI1466 1466 = true := by decide +kernel
theorem cen1466 : CenterUniqueMin 1466 ∧ DipHyp 1466 ∧ OnePointHyps 1466 :=
  cen_of L1466_ok H1466_ok I1466_ok link1466 cenlink1466

/-! ### `N = 1467` -/

def pL1467 : Prm := ⟨80, 38, 39, 1469, 11, 18446744073709551616, 126711526627630882, 126711526627630882⟩
def pH1467 : Prm := ⟨80, 38, 39, 1469, 11, 18446744073709551616, 126712626139258658, 126712626139258658⟩
def pI1467 : Prm := ⟨66, 33, 30, 1469, 11, 18446744073709551616, 126711526627630882, 126712626139258658⟩
noncomputable def L1467_cp1 : Nat × Nat := t7val% (fastRun pL1467 1 1036 (init pL1467) (init pL1467))
theorem L1467_seg1 : segOK pL1467 1 1036 (init pL1467) (init pL1467) L1467_cp1.1 L1467_cp1.2 = true := by
  decide +kernel
theorem L1467_fin : (prmOK pL1467 1467 && ptTest pL1467 (runFrom pL1467 (fmask pL1467) (cmask pL1467) (hmask pL1467) 1037 430 (true, L1467_cp1.1, L1467_cp1.2)) 1467 734 false) = true := by
  decide +kernel
theorem L1467_ok : RunOK pL1467 1467 (runFrom pL1467 (fmask pL1467) (cmask pL1467) (hmask pL1467) 1037 430 (true, L1467_cp1.1, L1467_cp1.2)) ∧ ptTest pL1467 (runFrom pL1467 (fmask pL1467) (cmask pL1467) (hmask pL1467) 1037 430 (true, L1467_cp1.1, L1467_cp1.2)) 1467 734 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1467_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1467_fin) true) L1467_seg1) (by decide) rfl L1467_fin ptTest_fst
noncomputable def H1467_cp1 : Nat × Nat := t7val% (fastRun pH1467 1 1036 (init pH1467) (init pH1467))
theorem H1467_seg1 : segOK pH1467 1 1036 (init pH1467) (init pH1467) H1467_cp1.1 H1467_cp1.2 = true := by
  decide +kernel
theorem H1467_fin : (prmOK pH1467 1467 && ptTest pH1467 (runFrom pH1467 (fmask pH1467) (cmask pH1467) (hmask pH1467) 1037 430 (true, H1467_cp1.1, H1467_cp1.2)) 1467 734 true) = true := by
  decide +kernel
theorem H1467_ok : RunOK pH1467 1467 (runFrom pH1467 (fmask pH1467) (cmask pH1467) (hmask pH1467) 1037 430 (true, H1467_cp1.1, H1467_cp1.2)) ∧ ptTest pH1467 (runFrom pH1467 (fmask pH1467) (cmask pH1467) (hmask pH1467) 1037 430 (true, H1467_cp1.1, H1467_cp1.2)) 1467 734 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1467_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1467_fin) true) H1467_seg1) (by decide) rfl H1467_fin ptTest_fst
noncomputable def I1467_cp1 : Nat × Nat := t7val% (fastRun pI1467 1 1036 (init pI1467) (init pI1467))
theorem I1467_seg1 : segOK pI1467 1 1036 (init pI1467) (init pI1467) I1467_cp1.1 I1467_cp1.2 = true := by
  decide +kernel
theorem I1467_fin : (prmOK pI1467 1467 && intTest pI1467 (runFrom pI1467 (fmask pI1467) (cmask pI1467) (hmask pI1467) 1037 430 (true, I1467_cp1.1, I1467_cp1.2)) 1467 20 false) = true := by
  decide +kernel
theorem I1467_ok : RunOK pI1467 1467 (runFrom pI1467 (fmask pI1467) (cmask pI1467) (hmask pI1467) 1037 430 (true, I1467_cp1.1, I1467_cp1.2)) ∧ intTest pI1467 (runFrom pI1467 (fmask pI1467) (cmask pI1467) (hmask pI1467) 1037 430 (true, I1467_cp1.1, I1467_cp1.2)) 1467 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1467_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1467_fin) true) I1467_seg1) (by decide) rfl I1467_fin intTest_fst
theorem link1467 : linkOK pL1467 pH1467 pI1467 = true := by decide +kernel
theorem cvx1467 : ConvexBetweenHumps 1467 :=
  cvx_of L1467_ok H1467_ok I1467_ok link1467 (by decide)

/-! ### `N = 1468` -/

def pL1468 : Prm := ⟨80, 38, 39, 1470, 11, 18446744073709551616, 126641374230402572, 126641374230402572⟩
def pH1468 : Prm := ⟨80, 38, 39, 1470, 11, 18446744073709551616, 126642473742030348, 126642473742030348⟩
def pI1468 : Prm := ⟨66, 33, 30, 1470, 11, 18446744073709551616, 126641374230402572, 126642473742030348⟩
noncomputable def L1468_cp1 : Nat × Nat := t7val% (fastRun pL1468 1 1037 (init pL1468) (init pL1468))
theorem L1468_seg1 : segOK pL1468 1 1037 (init pL1468) (init pL1468) L1468_cp1.1 L1468_cp1.2 = true := by
  decide +kernel
theorem L1468_fin : (prmOK pL1468 1468 && ptTest pL1468 (runFrom pL1468 (fmask pL1468) (cmask pL1468) (hmask pL1468) 1038 430 (true, L1468_cp1.1, L1468_cp1.2)) 1468 734 false) = true := by
  decide +kernel
theorem L1468_ok : RunOK pL1468 1468 (runFrom pL1468 (fmask pL1468) (cmask pL1468) (hmask pL1468) 1038 430 (true, L1468_cp1.1, L1468_cp1.2)) ∧ ptTest pL1468 (runFrom pL1468 (fmask pL1468) (cmask pL1468) (hmask pL1468) 1038 430 (true, L1468_cp1.1, L1468_cp1.2)) 1468 734 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1468_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1468_fin) true) L1468_seg1) (by decide) rfl L1468_fin ptTest_fst
noncomputable def H1468_cp1 : Nat × Nat := t7val% (fastRun pH1468 1 1037 (init pH1468) (init pH1468))
theorem H1468_seg1 : segOK pH1468 1 1037 (init pH1468) (init pH1468) H1468_cp1.1 H1468_cp1.2 = true := by
  decide +kernel
theorem H1468_fin : (prmOK pH1468 1468 && ptTest pH1468 (runFrom pH1468 (fmask pH1468) (cmask pH1468) (hmask pH1468) 1038 430 (true, H1468_cp1.1, H1468_cp1.2)) 1468 734 true) = true := by
  decide +kernel
theorem H1468_ok : RunOK pH1468 1468 (runFrom pH1468 (fmask pH1468) (cmask pH1468) (hmask pH1468) 1038 430 (true, H1468_cp1.1, H1468_cp1.2)) ∧ ptTest pH1468 (runFrom pH1468 (fmask pH1468) (cmask pH1468) (hmask pH1468) 1038 430 (true, H1468_cp1.1, H1468_cp1.2)) 1468 734 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1468_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1468_fin) true) H1468_seg1) (by decide) rfl H1468_fin ptTest_fst
noncomputable def I1468_cp1 : Nat × Nat := t7val% (fastRun pI1468 1 1037 (init pI1468) (init pI1468))
theorem I1468_seg1 : segOK pI1468 1 1037 (init pI1468) (init pI1468) I1468_cp1.1 I1468_cp1.2 = true := by
  decide +kernel
theorem I1468_fin : (prmOK pI1468 1468 && intTest pI1468 (runFrom pI1468 (fmask pI1468) (cmask pI1468) (hmask pI1468) 1038 430 (true, I1468_cp1.1, I1468_cp1.2)) 1468 20 true) = true := by
  decide +kernel
theorem I1468_ok : RunOK pI1468 1468 (runFrom pI1468 (fmask pI1468) (cmask pI1468) (hmask pI1468) 1038 430 (true, I1468_cp1.1, I1468_cp1.2)) ∧ intTest pI1468 (runFrom pI1468 (fmask pI1468) (cmask pI1468) (hmask pI1468) 1038 430 (true, I1468_cp1.1, I1468_cp1.2)) 1468 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1468_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1468_fin) true) I1468_seg1) (by decide) rfl I1468_fin intTest_fst
theorem link1468 : linkOK pL1468 pH1468 pI1468 = true := by decide +kernel
theorem cvx1468 : ConvexBetweenHumps 1468 :=
  cvx_of L1468_ok H1468_ok I1468_ok link1468 (by decide)
theorem cenlink1468 : cenLinkOK pI1468 1468 = true := by decide +kernel
theorem cen1468 : CenterUniqueMin 1468 ∧ DipHyp 1468 ∧ OnePointHyps 1468 :=
  cen_of L1468_ok H1468_ok I1468_ok link1468 cenlink1468

/-! ### `N = 1469` -/

def pL1469 : Prm := ⟨80, 38, 39, 1471, 11, 18446744073709551616, 126571270548830198, 126571270548830198⟩
def pH1469 : Prm := ⟨80, 38, 39, 1471, 11, 18446744073709551616, 126572370060457974, 126572370060457974⟩
def pI1469 : Prm := ⟨66, 33, 30, 1471, 11, 18446744073709551616, 126571270548830198, 126572370060457974⟩
noncomputable def L1469_cp1 : Nat × Nat := t7val% (fastRun pL1469 1 1038 (init pL1469) (init pL1469))
theorem L1469_seg1 : segOK pL1469 1 1038 (init pL1469) (init pL1469) L1469_cp1.1 L1469_cp1.2 = true := by
  decide +kernel
theorem L1469_fin : (prmOK pL1469 1469 && ptTest pL1469 (runFrom pL1469 (fmask pL1469) (cmask pL1469) (hmask pL1469) 1039 430 (true, L1469_cp1.1, L1469_cp1.2)) 1469 735 false) = true := by
  decide +kernel
theorem L1469_ok : RunOK pL1469 1469 (runFrom pL1469 (fmask pL1469) (cmask pL1469) (hmask pL1469) 1039 430 (true, L1469_cp1.1, L1469_cp1.2)) ∧ ptTest pL1469 (runFrom pL1469 (fmask pL1469) (cmask pL1469) (hmask pL1469) 1039 430 (true, L1469_cp1.1, L1469_cp1.2)) 1469 735 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1469_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1469_fin) true) L1469_seg1) (by decide) rfl L1469_fin ptTest_fst
noncomputable def H1469_cp1 : Nat × Nat := t7val% (fastRun pH1469 1 1038 (init pH1469) (init pH1469))
theorem H1469_seg1 : segOK pH1469 1 1038 (init pH1469) (init pH1469) H1469_cp1.1 H1469_cp1.2 = true := by
  decide +kernel
theorem H1469_fin : (prmOK pH1469 1469 && ptTest pH1469 (runFrom pH1469 (fmask pH1469) (cmask pH1469) (hmask pH1469) 1039 430 (true, H1469_cp1.1, H1469_cp1.2)) 1469 735 true) = true := by
  decide +kernel
theorem H1469_ok : RunOK pH1469 1469 (runFrom pH1469 (fmask pH1469) (cmask pH1469) (hmask pH1469) 1039 430 (true, H1469_cp1.1, H1469_cp1.2)) ∧ ptTest pH1469 (runFrom pH1469 (fmask pH1469) (cmask pH1469) (hmask pH1469) 1039 430 (true, H1469_cp1.1, H1469_cp1.2)) 1469 735 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1469_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1469_fin) true) H1469_seg1) (by decide) rfl H1469_fin ptTest_fst
noncomputable def I1469_cp1 : Nat × Nat := t7val% (fastRun pI1469 1 1038 (init pI1469) (init pI1469))
theorem I1469_seg1 : segOK pI1469 1 1038 (init pI1469) (init pI1469) I1469_cp1.1 I1469_cp1.2 = true := by
  decide +kernel
theorem I1469_fin : (prmOK pI1469 1469 && intTest pI1469 (runFrom pI1469 (fmask pI1469) (cmask pI1469) (hmask pI1469) 1039 430 (true, I1469_cp1.1, I1469_cp1.2)) 1469 20 false) = true := by
  decide +kernel
theorem I1469_ok : RunOK pI1469 1469 (runFrom pI1469 (fmask pI1469) (cmask pI1469) (hmask pI1469) 1039 430 (true, I1469_cp1.1, I1469_cp1.2)) ∧ intTest pI1469 (runFrom pI1469 (fmask pI1469) (cmask pI1469) (hmask pI1469) 1039 430 (true, I1469_cp1.1, I1469_cp1.2)) 1469 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1469_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1469_fin) true) I1469_seg1) (by decide) rfl I1469_fin intTest_fst
theorem link1469 : linkOK pL1469 pH1469 pI1469 = true := by decide +kernel
theorem cvx1469 : ConvexBetweenHumps 1469 :=
  cvx_of L1469_ok H1469_ok I1469_ok link1469 (by decide)

/-! ### `N = 1470` -/

def pL1470 : Prm := ⟨80, 38, 39, 1472, 11, 18446744073709551616, 126501286990407643, 126501286990407643⟩
def pH1470 : Prm := ⟨80, 38, 39, 1472, 11, 18446744073709551616, 126502386502035419, 126502386502035419⟩
def pI1470 : Prm := ⟨66, 33, 30, 1472, 11, 18446744073709551616, 126501286990407643, 126502386502035419⟩
noncomputable def L1470_cp1 : Nat × Nat := t7val% (fastRun pL1470 1 1038 (init pL1470) (init pL1470))
theorem L1470_seg1 : segOK pL1470 1 1038 (init pL1470) (init pL1470) L1470_cp1.1 L1470_cp1.2 = true := by
  decide +kernel
theorem L1470_fin : (prmOK pL1470 1470 && ptTest pL1470 (runFrom pL1470 (fmask pL1470) (cmask pL1470) (hmask pL1470) 1039 431 (true, L1470_cp1.1, L1470_cp1.2)) 1470 735 false) = true := by
  decide +kernel
theorem L1470_ok : RunOK pL1470 1470 (runFrom pL1470 (fmask pL1470) (cmask pL1470) (hmask pL1470) 1039 431 (true, L1470_cp1.1, L1470_cp1.2)) ∧ ptTest pL1470 (runFrom pL1470 (fmask pL1470) (cmask pL1470) (hmask pL1470) 1039 431 (true, L1470_cp1.1, L1470_cp1.2)) 1470 735 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1470_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1470_fin) true) L1470_seg1) (by decide) rfl L1470_fin ptTest_fst
noncomputable def H1470_cp1 : Nat × Nat := t7val% (fastRun pH1470 1 1038 (init pH1470) (init pH1470))
theorem H1470_seg1 : segOK pH1470 1 1038 (init pH1470) (init pH1470) H1470_cp1.1 H1470_cp1.2 = true := by
  decide +kernel
theorem H1470_fin : (prmOK pH1470 1470 && ptTest pH1470 (runFrom pH1470 (fmask pH1470) (cmask pH1470) (hmask pH1470) 1039 431 (true, H1470_cp1.1, H1470_cp1.2)) 1470 735 true) = true := by
  decide +kernel
theorem H1470_ok : RunOK pH1470 1470 (runFrom pH1470 (fmask pH1470) (cmask pH1470) (hmask pH1470) 1039 431 (true, H1470_cp1.1, H1470_cp1.2)) ∧ ptTest pH1470 (runFrom pH1470 (fmask pH1470) (cmask pH1470) (hmask pH1470) 1039 431 (true, H1470_cp1.1, H1470_cp1.2)) 1470 735 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1470_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1470_fin) true) H1470_seg1) (by decide) rfl H1470_fin ptTest_fst
noncomputable def I1470_cp1 : Nat × Nat := t7val% (fastRun pI1470 1 1038 (init pI1470) (init pI1470))
theorem I1470_seg1 : segOK pI1470 1 1038 (init pI1470) (init pI1470) I1470_cp1.1 I1470_cp1.2 = true := by
  decide +kernel
theorem I1470_fin : (prmOK pI1470 1470 && intTest pI1470 (runFrom pI1470 (fmask pI1470) (cmask pI1470) (hmask pI1470) 1039 431 (true, I1470_cp1.1, I1470_cp1.2)) 1470 20 true) = true := by
  decide +kernel
theorem I1470_ok : RunOK pI1470 1470 (runFrom pI1470 (fmask pI1470) (cmask pI1470) (hmask pI1470) 1039 431 (true, I1470_cp1.1, I1470_cp1.2)) ∧ intTest pI1470 (runFrom pI1470 (fmask pI1470) (cmask pI1470) (hmask pI1470) 1039 431 (true, I1470_cp1.1, I1470_cp1.2)) 1470 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1470_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1470_fin) true) I1470_seg1) (by decide) rfl I1470_fin intTest_fst
theorem link1470 : linkOK pL1470 pH1470 pI1470 = true := by decide +kernel
theorem cvx1470 : ConvexBetweenHumps 1470 :=
  cvx_of L1470_ok H1470_ok I1470_ok link1470 (by decide)
theorem cenlink1470 : cenLinkOK pI1470 1470 = true := by decide +kernel
theorem cen1470 : CenterUniqueMin 1470 ∧ DipHyp 1470 ∧ OnePointHyps 1470 :=
  cen_of L1470_ok H1470_ok I1470_ok link1470 cenlink1470

/-! ### `N = 1471` -/

def pL1471 : Prm := ⟨80, 38, 39, 1473, 11, 18446744073709551616, 126431351981288287, 126431351981288287⟩
def pH1471 : Prm := ⟨80, 38, 39, 1473, 11, 18446744073709551616, 126432451492916063, 126432451492916063⟩
def pI1471 : Prm := ⟨66, 33, 30, 1473, 11, 18446744073709551616, 126431351981288287, 126432451492916063⟩
noncomputable def L1471_cp1 : Nat × Nat := t7val% (fastRun pL1471 1 1039 (init pL1471) (init pL1471))
theorem L1471_seg1 : segOK pL1471 1 1039 (init pL1471) (init pL1471) L1471_cp1.1 L1471_cp1.2 = true := by
  decide +kernel
theorem L1471_fin : (prmOK pL1471 1471 && ptTest pL1471 (runFrom pL1471 (fmask pL1471) (cmask pL1471) (hmask pL1471) 1040 431 (true, L1471_cp1.1, L1471_cp1.2)) 1471 736 false) = true := by
  decide +kernel
theorem L1471_ok : RunOK pL1471 1471 (runFrom pL1471 (fmask pL1471) (cmask pL1471) (hmask pL1471) 1040 431 (true, L1471_cp1.1, L1471_cp1.2)) ∧ ptTest pL1471 (runFrom pL1471 (fmask pL1471) (cmask pL1471) (hmask pL1471) 1040 431 (true, L1471_cp1.1, L1471_cp1.2)) 1471 736 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1471_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1471_fin) true) L1471_seg1) (by decide) rfl L1471_fin ptTest_fst
noncomputable def H1471_cp1 : Nat × Nat := t7val% (fastRun pH1471 1 1039 (init pH1471) (init pH1471))
theorem H1471_seg1 : segOK pH1471 1 1039 (init pH1471) (init pH1471) H1471_cp1.1 H1471_cp1.2 = true := by
  decide +kernel
theorem H1471_fin : (prmOK pH1471 1471 && ptTest pH1471 (runFrom pH1471 (fmask pH1471) (cmask pH1471) (hmask pH1471) 1040 431 (true, H1471_cp1.1, H1471_cp1.2)) 1471 736 true) = true := by
  decide +kernel
theorem H1471_ok : RunOK pH1471 1471 (runFrom pH1471 (fmask pH1471) (cmask pH1471) (hmask pH1471) 1040 431 (true, H1471_cp1.1, H1471_cp1.2)) ∧ ptTest pH1471 (runFrom pH1471 (fmask pH1471) (cmask pH1471) (hmask pH1471) 1040 431 (true, H1471_cp1.1, H1471_cp1.2)) 1471 736 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1471_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1471_fin) true) H1471_seg1) (by decide) rfl H1471_fin ptTest_fst
noncomputable def I1471_cp1 : Nat × Nat := t7val% (fastRun pI1471 1 1039 (init pI1471) (init pI1471))
theorem I1471_seg1 : segOK pI1471 1 1039 (init pI1471) (init pI1471) I1471_cp1.1 I1471_cp1.2 = true := by
  decide +kernel
theorem I1471_fin : (prmOK pI1471 1471 && intTest pI1471 (runFrom pI1471 (fmask pI1471) (cmask pI1471) (hmask pI1471) 1040 431 (true, I1471_cp1.1, I1471_cp1.2)) 1471 20 false) = true := by
  decide +kernel
theorem I1471_ok : RunOK pI1471 1471 (runFrom pI1471 (fmask pI1471) (cmask pI1471) (hmask pI1471) 1040 431 (true, I1471_cp1.1, I1471_cp1.2)) ∧ intTest pI1471 (runFrom pI1471 (fmask pI1471) (cmask pI1471) (hmask pI1471) 1040 431 (true, I1471_cp1.1, I1471_cp1.2)) 1471 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1471_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1471_fin) true) I1471_seg1) (by decide) rfl I1471_fin intTest_fst
theorem link1471 : linkOK pL1471 pH1471 pI1471 = true := by decide +kernel
theorem cvx1471 : ConvexBetweenHumps 1471 :=
  cvx_of L1471_ok H1471_ok I1471_ok link1471 (by decide)

/-! ### `N = 1472` -/

def pL1472 : Prm := ⟨80, 38, 39, 1474, 11, 18446744073709551616, 126361536633375384, 126361536633375384⟩
def pH1472 : Prm := ⟨80, 38, 39, 1474, 11, 18446744073709551616, 126362636145003160, 126362636145003160⟩
def pI1472 : Prm := ⟨66, 33, 30, 1474, 11, 18446744073709551616, 126361536633375384, 126362636145003160⟩
noncomputable def L1472_cp1 : Nat × Nat := t7val% (fastRun pL1472 1 1040 (init pL1472) (init pL1472))
theorem L1472_seg1 : segOK pL1472 1 1040 (init pL1472) (init pL1472) L1472_cp1.1 L1472_cp1.2 = true := by
  decide +kernel
theorem L1472_fin : (prmOK pL1472 1472 && ptTest pL1472 (runFrom pL1472 (fmask pL1472) (cmask pL1472) (hmask pL1472) 1041 431 (true, L1472_cp1.1, L1472_cp1.2)) 1472 736 false) = true := by
  decide +kernel
theorem L1472_ok : RunOK pL1472 1472 (runFrom pL1472 (fmask pL1472) (cmask pL1472) (hmask pL1472) 1041 431 (true, L1472_cp1.1, L1472_cp1.2)) ∧ ptTest pL1472 (runFrom pL1472 (fmask pL1472) (cmask pL1472) (hmask pL1472) 1041 431 (true, L1472_cp1.1, L1472_cp1.2)) 1472 736 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1472_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1472_fin) true) L1472_seg1) (by decide) rfl L1472_fin ptTest_fst
noncomputable def H1472_cp1 : Nat × Nat := t7val% (fastRun pH1472 1 1040 (init pH1472) (init pH1472))
theorem H1472_seg1 : segOK pH1472 1 1040 (init pH1472) (init pH1472) H1472_cp1.1 H1472_cp1.2 = true := by
  decide +kernel
theorem H1472_fin : (prmOK pH1472 1472 && ptTest pH1472 (runFrom pH1472 (fmask pH1472) (cmask pH1472) (hmask pH1472) 1041 431 (true, H1472_cp1.1, H1472_cp1.2)) 1472 736 true) = true := by
  decide +kernel
theorem H1472_ok : RunOK pH1472 1472 (runFrom pH1472 (fmask pH1472) (cmask pH1472) (hmask pH1472) 1041 431 (true, H1472_cp1.1, H1472_cp1.2)) ∧ ptTest pH1472 (runFrom pH1472 (fmask pH1472) (cmask pH1472) (hmask pH1472) 1041 431 (true, H1472_cp1.1, H1472_cp1.2)) 1472 736 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1472_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1472_fin) true) H1472_seg1) (by decide) rfl H1472_fin ptTest_fst
noncomputable def I1472_cp1 : Nat × Nat := t7val% (fastRun pI1472 1 1040 (init pI1472) (init pI1472))
theorem I1472_seg1 : segOK pI1472 1 1040 (init pI1472) (init pI1472) I1472_cp1.1 I1472_cp1.2 = true := by
  decide +kernel
theorem I1472_fin : (prmOK pI1472 1472 && intTest pI1472 (runFrom pI1472 (fmask pI1472) (cmask pI1472) (hmask pI1472) 1041 431 (true, I1472_cp1.1, I1472_cp1.2)) 1472 20 true) = true := by
  decide +kernel
theorem I1472_ok : RunOK pI1472 1472 (runFrom pI1472 (fmask pI1472) (cmask pI1472) (hmask pI1472) 1041 431 (true, I1472_cp1.1, I1472_cp1.2)) ∧ intTest pI1472 (runFrom pI1472 (fmask pI1472) (cmask pI1472) (hmask pI1472) 1041 431 (true, I1472_cp1.1, I1472_cp1.2)) 1472 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1472_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1472_fin) true) I1472_seg1) (by decide) rfl I1472_fin intTest_fst
theorem link1472 : linkOK pL1472 pH1472 pI1472 = true := by decide +kernel
theorem cvx1472 : ConvexBetweenHumps 1472 :=
  cvx_of L1472_ok H1472_ok I1472_ok link1472 (by decide)
theorem cenlink1472 : cenLinkOK pI1472 1472 = true := by decide +kernel
theorem cen1472 : CenterUniqueMin 1472 ∧ DipHyp 1472 ∧ OnePointHyps 1472 :=
  cen_of L1472_ok H1472_ok I1472_ok link1472 cenlink1472

/-! ### `N = 1473` -/

def pL1473 : Prm := ⟨80, 38, 39, 1475, 11, 18446744073709551616, 126291769669206152, 126291769669206152⟩
def pH1473 : Prm := ⟨80, 38, 39, 1475, 11, 18446744073709551616, 126292869180833928, 126292869180833928⟩
def pI1473 : Prm := ⟨66, 33, 30, 1475, 11, 18446744073709551616, 126291769669206152, 126292869180833928⟩
noncomputable def L1473_cp1 : Nat × Nat := t7val% (fastRun pL1473 1 1041 (init pL1473) (init pL1473))
theorem L1473_seg1 : segOK pL1473 1 1041 (init pL1473) (init pL1473) L1473_cp1.1 L1473_cp1.2 = true := by
  decide +kernel
theorem L1473_fin : (prmOK pL1473 1473 && ptTest pL1473 (runFrom pL1473 (fmask pL1473) (cmask pL1473) (hmask pL1473) 1042 431 (true, L1473_cp1.1, L1473_cp1.2)) 1473 737 false) = true := by
  decide +kernel
theorem L1473_ok : RunOK pL1473 1473 (runFrom pL1473 (fmask pL1473) (cmask pL1473) (hmask pL1473) 1042 431 (true, L1473_cp1.1, L1473_cp1.2)) ∧ ptTest pL1473 (runFrom pL1473 (fmask pL1473) (cmask pL1473) (hmask pL1473) 1042 431 (true, L1473_cp1.1, L1473_cp1.2)) 1473 737 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1473_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1473_fin) true) L1473_seg1) (by decide) rfl L1473_fin ptTest_fst
noncomputable def H1473_cp1 : Nat × Nat := t7val% (fastRun pH1473 1 1041 (init pH1473) (init pH1473))
theorem H1473_seg1 : segOK pH1473 1 1041 (init pH1473) (init pH1473) H1473_cp1.1 H1473_cp1.2 = true := by
  decide +kernel
theorem H1473_fin : (prmOK pH1473 1473 && ptTest pH1473 (runFrom pH1473 (fmask pH1473) (cmask pH1473) (hmask pH1473) 1042 431 (true, H1473_cp1.1, H1473_cp1.2)) 1473 737 true) = true := by
  decide +kernel
theorem H1473_ok : RunOK pH1473 1473 (runFrom pH1473 (fmask pH1473) (cmask pH1473) (hmask pH1473) 1042 431 (true, H1473_cp1.1, H1473_cp1.2)) ∧ ptTest pH1473 (runFrom pH1473 (fmask pH1473) (cmask pH1473) (hmask pH1473) 1042 431 (true, H1473_cp1.1, H1473_cp1.2)) 1473 737 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1473_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1473_fin) true) H1473_seg1) (by decide) rfl H1473_fin ptTest_fst
noncomputable def I1473_cp1 : Nat × Nat := t7val% (fastRun pI1473 1 1041 (init pI1473) (init pI1473))
theorem I1473_seg1 : segOK pI1473 1 1041 (init pI1473) (init pI1473) I1473_cp1.1 I1473_cp1.2 = true := by
  decide +kernel
theorem I1473_fin : (prmOK pI1473 1473 && intTest pI1473 (runFrom pI1473 (fmask pI1473) (cmask pI1473) (hmask pI1473) 1042 431 (true, I1473_cp1.1, I1473_cp1.2)) 1473 20 false) = true := by
  decide +kernel
theorem I1473_ok : RunOK pI1473 1473 (runFrom pI1473 (fmask pI1473) (cmask pI1473) (hmask pI1473) 1042 431 (true, I1473_cp1.1, I1473_cp1.2)) ∧ intTest pI1473 (runFrom pI1473 (fmask pI1473) (cmask pI1473) (hmask pI1473) 1042 431 (true, I1473_cp1.1, I1473_cp1.2)) 1473 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1473_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1473_fin) true) I1473_seg1) (by decide) rfl I1473_fin intTest_fst
theorem link1473 : linkOK pL1473 pH1473 pI1473 = true := by decide +kernel
theorem cvx1473 : ConvexBetweenHumps 1473 :=
  cvx_of L1473_ok H1473_ok I1473_ok link1473 (by decide)

/-! ### `N = 1474` -/

def pL1474 : Prm := ⟨80, 38, 39, 1476, 11, 18446744073709551616, 126222121906734979, 126222121906734979⟩
def pH1474 : Prm := ⟨80, 38, 39, 1476, 11, 18446744073709551616, 126223221418362755, 126223221418362755⟩
def pI1474 : Prm := ⟨66, 33, 30, 1476, 11, 18446744073709551616, 126222121906734979, 126223221418362755⟩
noncomputable def L1474_cp1 : Nat × Nat := t7val% (fastRun pL1474 1 1041 (init pL1474) (init pL1474))
theorem L1474_seg1 : segOK pL1474 1 1041 (init pL1474) (init pL1474) L1474_cp1.1 L1474_cp1.2 = true := by
  decide +kernel
theorem L1474_fin : (prmOK pL1474 1474 && ptTest pL1474 (runFrom pL1474 (fmask pL1474) (cmask pL1474) (hmask pL1474) 1042 432 (true, L1474_cp1.1, L1474_cp1.2)) 1474 737 false) = true := by
  decide +kernel
theorem L1474_ok : RunOK pL1474 1474 (runFrom pL1474 (fmask pL1474) (cmask pL1474) (hmask pL1474) 1042 432 (true, L1474_cp1.1, L1474_cp1.2)) ∧ ptTest pL1474 (runFrom pL1474 (fmask pL1474) (cmask pL1474) (hmask pL1474) 1042 432 (true, L1474_cp1.1, L1474_cp1.2)) 1474 737 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1474_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1474_fin) true) L1474_seg1) (by decide) rfl L1474_fin ptTest_fst
noncomputable def H1474_cp1 : Nat × Nat := t7val% (fastRun pH1474 1 1041 (init pH1474) (init pH1474))
theorem H1474_seg1 : segOK pH1474 1 1041 (init pH1474) (init pH1474) H1474_cp1.1 H1474_cp1.2 = true := by
  decide +kernel
theorem H1474_fin : (prmOK pH1474 1474 && ptTest pH1474 (runFrom pH1474 (fmask pH1474) (cmask pH1474) (hmask pH1474) 1042 432 (true, H1474_cp1.1, H1474_cp1.2)) 1474 737 true) = true := by
  decide +kernel
theorem H1474_ok : RunOK pH1474 1474 (runFrom pH1474 (fmask pH1474) (cmask pH1474) (hmask pH1474) 1042 432 (true, H1474_cp1.1, H1474_cp1.2)) ∧ ptTest pH1474 (runFrom pH1474 (fmask pH1474) (cmask pH1474) (hmask pH1474) 1042 432 (true, H1474_cp1.1, H1474_cp1.2)) 1474 737 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1474_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1474_fin) true) H1474_seg1) (by decide) rfl H1474_fin ptTest_fst
noncomputable def I1474_cp1 : Nat × Nat := t7val% (fastRun pI1474 1 1041 (init pI1474) (init pI1474))
theorem I1474_seg1 : segOK pI1474 1 1041 (init pI1474) (init pI1474) I1474_cp1.1 I1474_cp1.2 = true := by
  decide +kernel
theorem I1474_fin : (prmOK pI1474 1474 && intTest pI1474 (runFrom pI1474 (fmask pI1474) (cmask pI1474) (hmask pI1474) 1042 432 (true, I1474_cp1.1, I1474_cp1.2)) 1474 20 true) = true := by
  decide +kernel
theorem I1474_ok : RunOK pI1474 1474 (runFrom pI1474 (fmask pI1474) (cmask pI1474) (hmask pI1474) 1042 432 (true, I1474_cp1.1, I1474_cp1.2)) ∧ intTest pI1474 (runFrom pI1474 (fmask pI1474) (cmask pI1474) (hmask pI1474) 1042 432 (true, I1474_cp1.1, I1474_cp1.2)) 1474 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1474_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1474_fin) true) I1474_seg1) (by decide) rfl I1474_fin intTest_fst
theorem link1474 : linkOK pL1474 pH1474 pI1474 = true := by decide +kernel
theorem cvx1474 : ConvexBetweenHumps 1474 :=
  cvx_of L1474_ok H1474_ok I1474_ok link1474 (by decide)
theorem cenlink1474 : cenLinkOK pI1474 1474 = true := by decide +kernel
theorem cen1474 : CenterUniqueMin 1474 ∧ DipHyp 1474 ∧ OnePointHyps 1474 :=
  cen_of L1474_ok H1474_ok I1474_ok link1474 cenlink1474

/-! ### `N = 1475` -/

def pL1475 : Prm := ⟨80, 38, 39, 1477, 11, 18446744073709551616, 126152522363185818, 126152522363185818⟩
def pH1475 : Prm := ⟨80, 38, 39, 1477, 11, 18446744073709551616, 126153621874813594, 126153621874813594⟩
def pI1475 : Prm := ⟨66, 33, 30, 1477, 11, 18446744073709551616, 126152522363185818, 126153621874813594⟩
noncomputable def L1475_cp1 : Nat × Nat := t7val% (fastRun pL1475 1 1042 (init pL1475) (init pL1475))
theorem L1475_seg1 : segOK pL1475 1 1042 (init pL1475) (init pL1475) L1475_cp1.1 L1475_cp1.2 = true := by
  decide +kernel
theorem L1475_fin : (prmOK pL1475 1475 && ptTest pL1475 (runFrom pL1475 (fmask pL1475) (cmask pL1475) (hmask pL1475) 1043 432 (true, L1475_cp1.1, L1475_cp1.2)) 1475 738 false) = true := by
  decide +kernel
theorem L1475_ok : RunOK pL1475 1475 (runFrom pL1475 (fmask pL1475) (cmask pL1475) (hmask pL1475) 1043 432 (true, L1475_cp1.1, L1475_cp1.2)) ∧ ptTest pL1475 (runFrom pL1475 (fmask pL1475) (cmask pL1475) (hmask pL1475) 1043 432 (true, L1475_cp1.1, L1475_cp1.2)) 1475 738 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1475_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1475_fin) true) L1475_seg1) (by decide) rfl L1475_fin ptTest_fst
noncomputable def H1475_cp1 : Nat × Nat := t7val% (fastRun pH1475 1 1042 (init pH1475) (init pH1475))
theorem H1475_seg1 : segOK pH1475 1 1042 (init pH1475) (init pH1475) H1475_cp1.1 H1475_cp1.2 = true := by
  decide +kernel
theorem H1475_fin : (prmOK pH1475 1475 && ptTest pH1475 (runFrom pH1475 (fmask pH1475) (cmask pH1475) (hmask pH1475) 1043 432 (true, H1475_cp1.1, H1475_cp1.2)) 1475 738 true) = true := by
  decide +kernel
theorem H1475_ok : RunOK pH1475 1475 (runFrom pH1475 (fmask pH1475) (cmask pH1475) (hmask pH1475) 1043 432 (true, H1475_cp1.1, H1475_cp1.2)) ∧ ptTest pH1475 (runFrom pH1475 (fmask pH1475) (cmask pH1475) (hmask pH1475) 1043 432 (true, H1475_cp1.1, H1475_cp1.2)) 1475 738 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1475_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1475_fin) true) H1475_seg1) (by decide) rfl H1475_fin ptTest_fst
noncomputable def I1475_cp1 : Nat × Nat := t7val% (fastRun pI1475 1 1042 (init pI1475) (init pI1475))
theorem I1475_seg1 : segOK pI1475 1 1042 (init pI1475) (init pI1475) I1475_cp1.1 I1475_cp1.2 = true := by
  decide +kernel
theorem I1475_fin : (prmOK pI1475 1475 && intTest pI1475 (runFrom pI1475 (fmask pI1475) (cmask pI1475) (hmask pI1475) 1043 432 (true, I1475_cp1.1, I1475_cp1.2)) 1475 20 false) = true := by
  decide +kernel
theorem I1475_ok : RunOK pI1475 1475 (runFrom pI1475 (fmask pI1475) (cmask pI1475) (hmask pI1475) 1043 432 (true, I1475_cp1.1, I1475_cp1.2)) ∧ intTest pI1475 (runFrom pI1475 (fmask pI1475) (cmask pI1475) (hmask pI1475) 1043 432 (true, I1475_cp1.1, I1475_cp1.2)) 1475 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1475_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1475_fin) true) I1475_seg1) (by decide) rfl I1475_fin intTest_fst
theorem link1475 : linkOK pL1475 pH1475 pI1475 = true := by decide +kernel
theorem cvx1475 : ConvexBetweenHumps 1475 :=
  cvx_of L1475_ok H1475_ok I1475_ok link1475 (by decide)

/-! ### `N = 1476` -/

def pL1476 : Prm := ⟨80, 38, 39, 1478, 11, 18446744073709551616, 126083041564187505, 126083041564187505⟩
def pH1476 : Prm := ⟨80, 38, 39, 1478, 11, 18446744073709551616, 126084141075815281, 126084141075815281⟩
def pI1476 : Prm := ⟨66, 33, 30, 1478, 11, 18446744073709551616, 126083041564187505, 126084141075815281⟩
noncomputable def L1476_cp1 : Nat × Nat := t7val% (fastRun pL1476 1 1043 (init pL1476) (init pL1476))
theorem L1476_seg1 : segOK pL1476 1 1043 (init pL1476) (init pL1476) L1476_cp1.1 L1476_cp1.2 = true := by
  decide +kernel
theorem L1476_fin : (prmOK pL1476 1476 && ptTest pL1476 (runFrom pL1476 (fmask pL1476) (cmask pL1476) (hmask pL1476) 1044 432 (true, L1476_cp1.1, L1476_cp1.2)) 1476 738 false) = true := by
  decide +kernel
theorem L1476_ok : RunOK pL1476 1476 (runFrom pL1476 (fmask pL1476) (cmask pL1476) (hmask pL1476) 1044 432 (true, L1476_cp1.1, L1476_cp1.2)) ∧ ptTest pL1476 (runFrom pL1476 (fmask pL1476) (cmask pL1476) (hmask pL1476) 1044 432 (true, L1476_cp1.1, L1476_cp1.2)) 1476 738 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1476_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1476_fin) true) L1476_seg1) (by decide) rfl L1476_fin ptTest_fst
noncomputable def H1476_cp1 : Nat × Nat := t7val% (fastRun pH1476 1 1043 (init pH1476) (init pH1476))
theorem H1476_seg1 : segOK pH1476 1 1043 (init pH1476) (init pH1476) H1476_cp1.1 H1476_cp1.2 = true := by
  decide +kernel
theorem H1476_fin : (prmOK pH1476 1476 && ptTest pH1476 (runFrom pH1476 (fmask pH1476) (cmask pH1476) (hmask pH1476) 1044 432 (true, H1476_cp1.1, H1476_cp1.2)) 1476 738 true) = true := by
  decide +kernel
theorem H1476_ok : RunOK pH1476 1476 (runFrom pH1476 (fmask pH1476) (cmask pH1476) (hmask pH1476) 1044 432 (true, H1476_cp1.1, H1476_cp1.2)) ∧ ptTest pH1476 (runFrom pH1476 (fmask pH1476) (cmask pH1476) (hmask pH1476) 1044 432 (true, H1476_cp1.1, H1476_cp1.2)) 1476 738 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1476_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1476_fin) true) H1476_seg1) (by decide) rfl H1476_fin ptTest_fst
noncomputable def I1476_cp1 : Nat × Nat := t7val% (fastRun pI1476 1 1043 (init pI1476) (init pI1476))
theorem I1476_seg1 : segOK pI1476 1 1043 (init pI1476) (init pI1476) I1476_cp1.1 I1476_cp1.2 = true := by
  decide +kernel
theorem I1476_fin : (prmOK pI1476 1476 && intTest pI1476 (runFrom pI1476 (fmask pI1476) (cmask pI1476) (hmask pI1476) 1044 432 (true, I1476_cp1.1, I1476_cp1.2)) 1476 20 true) = true := by
  decide +kernel
theorem I1476_ok : RunOK pI1476 1476 (runFrom pI1476 (fmask pI1476) (cmask pI1476) (hmask pI1476) 1044 432 (true, I1476_cp1.1, I1476_cp1.2)) ∧ intTest pI1476 (runFrom pI1476 (fmask pI1476) (cmask pI1476) (hmask pI1476) 1044 432 (true, I1476_cp1.1, I1476_cp1.2)) 1476 20 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1476_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1476_fin) true) I1476_seg1) (by decide) rfl I1476_fin intTest_fst
theorem link1476 : linkOK pL1476 pH1476 pI1476 = true := by decide +kernel
theorem cvx1476 : ConvexBetweenHumps 1476 :=
  cvx_of L1476_ok H1476_ok I1476_ok link1476 (by decide)
theorem cenlink1476 : cenLinkOK pI1476 1476 = true := by decide +kernel
theorem cen1476 : CenterUniqueMin 1476 ∧ DipHyp 1476 ∧ OnePointHyps 1476 :=
  cen_of L1476_ok H1476_ok I1476_ok link1476 cenlink1476

/-! ### `N = 1477` -/

def pL1477 : Prm := ⟨80, 38, 39, 1479, 11, 18446744073709551616, 126013608820045861, 126013608820045861⟩
def pH1477 : Prm := ⟨80, 38, 39, 1479, 11, 18446744073709551616, 126014708331673637, 126014708331673637⟩
def pI1477 : Prm := ⟨66, 33, 30, 1479, 11, 18446744073709551616, 126013608820045861, 126014708331673637⟩
noncomputable def L1477_cp1 : Nat × Nat := t7val% (fastRun pL1477 1 1043 (init pL1477) (init pL1477))
theorem L1477_seg1 : segOK pL1477 1 1043 (init pL1477) (init pL1477) L1477_cp1.1 L1477_cp1.2 = true := by
  decide +kernel
theorem L1477_fin : (prmOK pL1477 1477 && ptTest pL1477 (runFrom pL1477 (fmask pL1477) (cmask pL1477) (hmask pL1477) 1044 433 (true, L1477_cp1.1, L1477_cp1.2)) 1477 739 false) = true := by
  decide +kernel
theorem L1477_ok : RunOK pL1477 1477 (runFrom pL1477 (fmask pL1477) (cmask pL1477) (hmask pL1477) 1044 433 (true, L1477_cp1.1, L1477_cp1.2)) ∧ ptTest pL1477 (runFrom pL1477 (fmask pL1477) (cmask pL1477) (hmask pL1477) 1044 433 (true, L1477_cp1.1, L1477_cp1.2)) 1477 739 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1477_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1477_fin) true) L1477_seg1) (by decide) rfl L1477_fin ptTest_fst
noncomputable def H1477_cp1 : Nat × Nat := t7val% (fastRun pH1477 1 1043 (init pH1477) (init pH1477))
theorem H1477_seg1 : segOK pH1477 1 1043 (init pH1477) (init pH1477) H1477_cp1.1 H1477_cp1.2 = true := by
  decide +kernel
theorem H1477_fin : (prmOK pH1477 1477 && ptTest pH1477 (runFrom pH1477 (fmask pH1477) (cmask pH1477) (hmask pH1477) 1044 433 (true, H1477_cp1.1, H1477_cp1.2)) 1477 739 true) = true := by
  decide +kernel
theorem H1477_ok : RunOK pH1477 1477 (runFrom pH1477 (fmask pH1477) (cmask pH1477) (hmask pH1477) 1044 433 (true, H1477_cp1.1, H1477_cp1.2)) ∧ ptTest pH1477 (runFrom pH1477 (fmask pH1477) (cmask pH1477) (hmask pH1477) 1044 433 (true, H1477_cp1.1, H1477_cp1.2)) 1477 739 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1477_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1477_fin) true) H1477_seg1) (by decide) rfl H1477_fin ptTest_fst
noncomputable def I1477_cp1 : Nat × Nat := t7val% (fastRun pI1477 1 1043 (init pI1477) (init pI1477))
theorem I1477_seg1 : segOK pI1477 1 1043 (init pI1477) (init pI1477) I1477_cp1.1 I1477_cp1.2 = true := by
  decide +kernel
theorem I1477_fin : (prmOK pI1477 1477 && intTest pI1477 (runFrom pI1477 (fmask pI1477) (cmask pI1477) (hmask pI1477) 1044 433 (true, I1477_cp1.1, I1477_cp1.2)) 1477 20 false) = true := by
  decide +kernel
theorem I1477_ok : RunOK pI1477 1477 (runFrom pI1477 (fmask pI1477) (cmask pI1477) (hmask pI1477) 1044 433 (true, I1477_cp1.1, I1477_cp1.2)) ∧ intTest pI1477 (runFrom pI1477 (fmask pI1477) (cmask pI1477) (hmask pI1477) 1044 433 (true, I1477_cp1.1, I1477_cp1.2)) 1477 20 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1477_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1477_fin) true) I1477_seg1) (by decide) rfl I1477_fin intTest_fst
theorem link1477 : linkOK pL1477 pH1477 pI1477 = true := by decide +kernel
theorem cvx1477 : ConvexBetweenHumps 1477 :=
  cvx_of L1477_ok H1477_ok I1477_ok link1477 (by decide)

/-! ### The range -/

theorem cvx_1460_1477 {N : ℕ} (h1 : 1460 ≤ N) (h2 : N ≤ 1477) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1468
  · by_cases h4 : N ≤ 1463
    · by_cases h6 : N ≤ 1461
      · by_cases h8 : N ≤ 1460
        · obtain rfl : N = 1460 := by omega
          exact cvx1460
        · obtain rfl : N = 1461 := by omega
          exact cvx1461
      · by_cases h8 : N ≤ 1462
        · obtain rfl : N = 1462 := by omega
          exact cvx1462
        · obtain rfl : N = 1463 := by omega
          exact cvx1463
    · by_cases h6 : N ≤ 1465
      · by_cases h8 : N ≤ 1464
        · obtain rfl : N = 1464 := by omega
          exact cvx1464
        · obtain rfl : N = 1465 := by omega
          exact cvx1465
      · by_cases h8 : N ≤ 1466
        · obtain rfl : N = 1466 := by omega
          exact cvx1466
        · by_cases h10 : N ≤ 1467
          · obtain rfl : N = 1467 := by omega
            exact cvx1467
          · obtain rfl : N = 1468 := by omega
            exact cvx1468
  · by_cases h4 : N ≤ 1472
    · by_cases h6 : N ≤ 1470
      · by_cases h8 : N ≤ 1469
        · obtain rfl : N = 1469 := by omega
          exact cvx1469
        · obtain rfl : N = 1470 := by omega
          exact cvx1470
      · by_cases h8 : N ≤ 1471
        · obtain rfl : N = 1471 := by omega
          exact cvx1471
        · obtain rfl : N = 1472 := by omega
          exact cvx1472
    · by_cases h6 : N ≤ 1474
      · by_cases h8 : N ≤ 1473
        · obtain rfl : N = 1473 := by omega
          exact cvx1473
        · obtain rfl : N = 1474 := by omega
          exact cvx1474
      · by_cases h8 : N ≤ 1475
        · obtain rfl : N = 1475 := by omega
          exact cvx1475
        · by_cases h10 : N ≤ 1476
          · obtain rfl : N = 1476 := by omega
            exact cvx1476
          · obtain rfl : N = 1477 := by omega
            exact cvx1477

theorem cen_1460_1477 {N : ℕ} (h1 : 1460 ≤ N) (h2 : N ≤ 1477) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1466
  · by_cases h4 : N ≤ 1462
    · by_cases h6 : N ≤ 1460
      · obtain rfl : N = 1460 := by omega
        exact cen1460
      · obtain rfl : N = 1462 := by omega
        exact cen1462
    · by_cases h6 : N ≤ 1464
      · obtain rfl : N = 1464 := by omega
        exact cen1464
      · obtain rfl : N = 1466 := by omega
        exact cen1466
  · by_cases h4 : N ≤ 1470
    · by_cases h6 : N ≤ 1468
      · obtain rfl : N = 1468 := by omega
        exact cen1468
      · obtain rfl : N = 1470 := by omega
        exact cen1470
    · by_cases h6 : N ≤ 1472
      · obtain rfl : N = 1472 := by omega
        exact cen1472
      · by_cases h8 : N ≤ 1474
        · obtain rfl : N = 1474 := by omega
          exact cen1474
        · obtain rfl : N = 1476 := by omega
          exact cen1476

end Kagey131.PaperD.T7
