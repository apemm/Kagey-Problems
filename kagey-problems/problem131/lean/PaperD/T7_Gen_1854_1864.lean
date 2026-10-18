import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1854, …, 1864` (generated)

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

/-! ### `N = 1854` -/

def pL1854 : Prm := ⟨80, 37, 40, 1856, 11, 18446744073709551616, 104653720825863094, 104653720825863094⟩
def pH1854 : Prm := ⟨80, 37, 40, 1856, 11, 18446744073709551616, 104654820337490870, 104654820337490870⟩
def pI1854 : Prm := ⟨68, 34, 31, 1856, 11, 18446744073709551616, 104653720825863094, 104654820337490870⟩
noncomputable def L1854_cp1 : Nat × Nat := t7val% (fastRun pL1854 1 1069 (init pL1854) (init pL1854))
theorem L1854_seg1 : segOK pL1854 1 1069 (init pL1854) (init pL1854) L1854_cp1.1 L1854_cp1.2 = true := by
  decide +kernel
noncomputable def L1854_cp2 : Nat × Nat := t7val% (fastRun pL1854 1 1513 (init pL1854) (init pL1854))
theorem L1854_seg2 : segOK pL1854 1070 444 L1854_cp1.1 L1854_cp1.2 L1854_cp2.1 L1854_cp2.2 = true := by
  decide +kernel
theorem L1854_fin : (prmOK pL1854 1854 && ptTest pL1854 (runFrom pL1854 (fmask pL1854) (cmask pL1854) (hmask pL1854) 1514 340 (true, L1854_cp2.1, L1854_cp2.2)) 1854 927 false) = true := by
  decide +kernel
theorem L1854_ok : RunOK pL1854 1854 (runFrom pL1854 (fmask pL1854) (cmask pL1854) (hmask pL1854) 1514 340 (true, L1854_cp2.1, L1854_cp2.2)) ∧ ptTest pL1854 (runFrom pL1854 (fmask pL1854) (cmask pL1854) (hmask pL1854) 1514 340 (true, L1854_cp2.1, L1854_cp2.2)) 1854 927 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1854_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1854_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1854_fin) true) L1854_seg1) L1854_seg2) (by decide) rfl L1854_fin ptTest_fst
noncomputable def H1854_cp1 : Nat × Nat := t7val% (fastRun pH1854 1 1069 (init pH1854) (init pH1854))
theorem H1854_seg1 : segOK pH1854 1 1069 (init pH1854) (init pH1854) H1854_cp1.1 H1854_cp1.2 = true := by
  decide +kernel
noncomputable def H1854_cp2 : Nat × Nat := t7val% (fastRun pH1854 1 1513 (init pH1854) (init pH1854))
theorem H1854_seg2 : segOK pH1854 1070 444 H1854_cp1.1 H1854_cp1.2 H1854_cp2.1 H1854_cp2.2 = true := by
  decide +kernel
theorem H1854_fin : (prmOK pH1854 1854 && ptTest pH1854 (runFrom pH1854 (fmask pH1854) (cmask pH1854) (hmask pH1854) 1514 340 (true, H1854_cp2.1, H1854_cp2.2)) 1854 927 true) = true := by
  decide +kernel
theorem H1854_ok : RunOK pH1854 1854 (runFrom pH1854 (fmask pH1854) (cmask pH1854) (hmask pH1854) 1514 340 (true, H1854_cp2.1, H1854_cp2.2)) ∧ ptTest pH1854 (runFrom pH1854 (fmask pH1854) (cmask pH1854) (hmask pH1854) 1514 340 (true, H1854_cp2.1, H1854_cp2.2)) 1854 927 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1854_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1854_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1854_fin) true) H1854_seg1) H1854_seg2) (by decide) rfl H1854_fin ptTest_fst
noncomputable def I1854_cp1 : Nat × Nat := t7val% (fastRun pI1854 1 1069 (init pI1854) (init pI1854))
theorem I1854_seg1 : segOK pI1854 1 1069 (init pI1854) (init pI1854) I1854_cp1.1 I1854_cp1.2 = true := by
  decide +kernel
noncomputable def I1854_cp2 : Nat × Nat := t7val% (fastRun pI1854 1 1513 (init pI1854) (init pI1854))
theorem I1854_seg2 : segOK pI1854 1070 444 I1854_cp1.1 I1854_cp1.2 I1854_cp2.1 I1854_cp2.2 = true := by
  decide +kernel
theorem I1854_fin : (prmOK pI1854 1854 && intTest pI1854 (runFrom pI1854 (fmask pI1854) (cmask pI1854) (hmask pI1854) 1514 340 (true, I1854_cp2.1, I1854_cp2.2)) 1854 21 true) = true := by
  decide +kernel
theorem I1854_ok : RunOK pI1854 1854 (runFrom pI1854 (fmask pI1854) (cmask pI1854) (hmask pI1854) 1514 340 (true, I1854_cp2.1, I1854_cp2.2)) ∧ intTest pI1854 (runFrom pI1854 (fmask pI1854) (cmask pI1854) (hmask pI1854) 1514 340 (true, I1854_cp2.1, I1854_cp2.2)) 1854 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1854_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1854_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1854_fin) true) I1854_seg1) I1854_seg2) (by decide) rfl I1854_fin intTest_fst
theorem link1854 : linkOK pL1854 pH1854 pI1854 = true := by decide +kernel
theorem cvx1854 : ConvexBetweenHumps 1854 :=
  cvx_of L1854_ok H1854_ok I1854_ok link1854 (by decide)
theorem cenlink1854 : cenLinkOK pI1854 1854 = true := by decide +kernel
theorem cen1854 : CenterUniqueMin 1854 ∧ DipHyp 1854 ∧ OnePointHyps 1854 :=
  cen_of L1854_ok H1854_ok I1854_ok link1854 cenlink1854

/-! ### `N = 1855` -/

def pL1855 : Prm := ⟨80, 37, 40, 1857, 11, 18446744073709551616, 104607402628616841, 104607402628616841⟩
def pH1855 : Prm := ⟨80, 37, 40, 1857, 11, 18446744073709551616, 104608502140244617, 104608502140244617⟩
def pI1855 : Prm := ⟨68, 34, 31, 1857, 11, 18446744073709551616, 104607402628616841, 104608502140244617⟩
noncomputable def L1855_cp1 : Nat × Nat := t7val% (fastRun pL1855 1 1070 (init pL1855) (init pL1855))
theorem L1855_seg1 : segOK pL1855 1 1070 (init pL1855) (init pL1855) L1855_cp1.1 L1855_cp1.2 = true := by
  decide +kernel
noncomputable def L1855_cp2 : Nat × Nat := t7val% (fastRun pL1855 1 1514 (init pL1855) (init pL1855))
theorem L1855_seg2 : segOK pL1855 1071 444 L1855_cp1.1 L1855_cp1.2 L1855_cp2.1 L1855_cp2.2 = true := by
  decide +kernel
theorem L1855_fin : (prmOK pL1855 1855 && ptTest pL1855 (runFrom pL1855 (fmask pL1855) (cmask pL1855) (hmask pL1855) 1515 340 (true, L1855_cp2.1, L1855_cp2.2)) 1855 928 false) = true := by
  decide +kernel
theorem L1855_ok : RunOK pL1855 1855 (runFrom pL1855 (fmask pL1855) (cmask pL1855) (hmask pL1855) 1515 340 (true, L1855_cp2.1, L1855_cp2.2)) ∧ ptTest pL1855 (runFrom pL1855 (fmask pL1855) (cmask pL1855) (hmask pL1855) 1515 340 (true, L1855_cp2.1, L1855_cp2.2)) 1855 928 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1855_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1855_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1855_fin) true) L1855_seg1) L1855_seg2) (by decide) rfl L1855_fin ptTest_fst
noncomputable def H1855_cp1 : Nat × Nat := t7val% (fastRun pH1855 1 1070 (init pH1855) (init pH1855))
theorem H1855_seg1 : segOK pH1855 1 1070 (init pH1855) (init pH1855) H1855_cp1.1 H1855_cp1.2 = true := by
  decide +kernel
noncomputable def H1855_cp2 : Nat × Nat := t7val% (fastRun pH1855 1 1514 (init pH1855) (init pH1855))
theorem H1855_seg2 : segOK pH1855 1071 444 H1855_cp1.1 H1855_cp1.2 H1855_cp2.1 H1855_cp2.2 = true := by
  decide +kernel
theorem H1855_fin : (prmOK pH1855 1855 && ptTest pH1855 (runFrom pH1855 (fmask pH1855) (cmask pH1855) (hmask pH1855) 1515 340 (true, H1855_cp2.1, H1855_cp2.2)) 1855 928 true) = true := by
  decide +kernel
theorem H1855_ok : RunOK pH1855 1855 (runFrom pH1855 (fmask pH1855) (cmask pH1855) (hmask pH1855) 1515 340 (true, H1855_cp2.1, H1855_cp2.2)) ∧ ptTest pH1855 (runFrom pH1855 (fmask pH1855) (cmask pH1855) (hmask pH1855) 1515 340 (true, H1855_cp2.1, H1855_cp2.2)) 1855 928 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1855_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1855_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1855_fin) true) H1855_seg1) H1855_seg2) (by decide) rfl H1855_fin ptTest_fst
noncomputable def I1855_cp1 : Nat × Nat := t7val% (fastRun pI1855 1 1070 (init pI1855) (init pI1855))
theorem I1855_seg1 : segOK pI1855 1 1070 (init pI1855) (init pI1855) I1855_cp1.1 I1855_cp1.2 = true := by
  decide +kernel
noncomputable def I1855_cp2 : Nat × Nat := t7val% (fastRun pI1855 1 1514 (init pI1855) (init pI1855))
theorem I1855_seg2 : segOK pI1855 1071 444 I1855_cp1.1 I1855_cp1.2 I1855_cp2.1 I1855_cp2.2 = true := by
  decide +kernel
theorem I1855_fin : (prmOK pI1855 1855 && intTest pI1855 (runFrom pI1855 (fmask pI1855) (cmask pI1855) (hmask pI1855) 1515 340 (true, I1855_cp2.1, I1855_cp2.2)) 1855 21 false) = true := by
  decide +kernel
theorem I1855_ok : RunOK pI1855 1855 (runFrom pI1855 (fmask pI1855) (cmask pI1855) (hmask pI1855) 1515 340 (true, I1855_cp2.1, I1855_cp2.2)) ∧ intTest pI1855 (runFrom pI1855 (fmask pI1855) (cmask pI1855) (hmask pI1855) 1515 340 (true, I1855_cp2.1, I1855_cp2.2)) 1855 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1855_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1855_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1855_fin) true) I1855_seg1) I1855_seg2) (by decide) rfl I1855_fin intTest_fst
theorem link1855 : linkOK pL1855 pH1855 pI1855 = true := by decide +kernel
theorem cvx1855 : ConvexBetweenHumps 1855 :=
  cvx_of L1855_ok H1855_ok I1855_ok link1855 (by decide)

/-! ### `N = 1856` -/

def pL1856 : Prm := ⟨80, 37, 40, 1858, 11, 18446744073709551616, 104561146440912448, 104561146440912448⟩
def pH1856 : Prm := ⟨80, 37, 40, 1858, 11, 18446744073709551616, 104562245952540224, 104562245952540224⟩
def pI1856 : Prm := ⟨68, 34, 31, 1858, 11, 18446744073709551616, 104561146440912448, 104562245952540224⟩
noncomputable def L1856_cp1 : Nat × Nat := t7val% (fastRun pL1856 1 1071 (init pL1856) (init pL1856))
theorem L1856_seg1 : segOK pL1856 1 1071 (init pL1856) (init pL1856) L1856_cp1.1 L1856_cp1.2 = true := by
  decide +kernel
noncomputable def L1856_cp2 : Nat × Nat := t7val% (fastRun pL1856 1 1514 (init pL1856) (init pL1856))
theorem L1856_seg2 : segOK pL1856 1072 443 L1856_cp1.1 L1856_cp1.2 L1856_cp2.1 L1856_cp2.2 = true := by
  decide +kernel
theorem L1856_fin : (prmOK pL1856 1856 && ptTest pL1856 (runFrom pL1856 (fmask pL1856) (cmask pL1856) (hmask pL1856) 1515 341 (true, L1856_cp2.1, L1856_cp2.2)) 1856 928 false) = true := by
  decide +kernel
theorem L1856_ok : RunOK pL1856 1856 (runFrom pL1856 (fmask pL1856) (cmask pL1856) (hmask pL1856) 1515 341 (true, L1856_cp2.1, L1856_cp2.2)) ∧ ptTest pL1856 (runFrom pL1856 (fmask pL1856) (cmask pL1856) (hmask pL1856) 1515 341 (true, L1856_cp2.1, L1856_cp2.2)) 1856 928 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1856_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1856_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1856_fin) true) L1856_seg1) L1856_seg2) (by decide) rfl L1856_fin ptTest_fst
noncomputable def H1856_cp1 : Nat × Nat := t7val% (fastRun pH1856 1 1071 (init pH1856) (init pH1856))
theorem H1856_seg1 : segOK pH1856 1 1071 (init pH1856) (init pH1856) H1856_cp1.1 H1856_cp1.2 = true := by
  decide +kernel
noncomputable def H1856_cp2 : Nat × Nat := t7val% (fastRun pH1856 1 1514 (init pH1856) (init pH1856))
theorem H1856_seg2 : segOK pH1856 1072 443 H1856_cp1.1 H1856_cp1.2 H1856_cp2.1 H1856_cp2.2 = true := by
  decide +kernel
theorem H1856_fin : (prmOK pH1856 1856 && ptTest pH1856 (runFrom pH1856 (fmask pH1856) (cmask pH1856) (hmask pH1856) 1515 341 (true, H1856_cp2.1, H1856_cp2.2)) 1856 928 true) = true := by
  decide +kernel
theorem H1856_ok : RunOK pH1856 1856 (runFrom pH1856 (fmask pH1856) (cmask pH1856) (hmask pH1856) 1515 341 (true, H1856_cp2.1, H1856_cp2.2)) ∧ ptTest pH1856 (runFrom pH1856 (fmask pH1856) (cmask pH1856) (hmask pH1856) 1515 341 (true, H1856_cp2.1, H1856_cp2.2)) 1856 928 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1856_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1856_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1856_fin) true) H1856_seg1) H1856_seg2) (by decide) rfl H1856_fin ptTest_fst
noncomputable def I1856_cp1 : Nat × Nat := t7val% (fastRun pI1856 1 1071 (init pI1856) (init pI1856))
theorem I1856_seg1 : segOK pI1856 1 1071 (init pI1856) (init pI1856) I1856_cp1.1 I1856_cp1.2 = true := by
  decide +kernel
noncomputable def I1856_cp2 : Nat × Nat := t7val% (fastRun pI1856 1 1514 (init pI1856) (init pI1856))
theorem I1856_seg2 : segOK pI1856 1072 443 I1856_cp1.1 I1856_cp1.2 I1856_cp2.1 I1856_cp2.2 = true := by
  decide +kernel
theorem I1856_fin : (prmOK pI1856 1856 && intTest pI1856 (runFrom pI1856 (fmask pI1856) (cmask pI1856) (hmask pI1856) 1515 341 (true, I1856_cp2.1, I1856_cp2.2)) 1856 21 true) = true := by
  decide +kernel
theorem I1856_ok : RunOK pI1856 1856 (runFrom pI1856 (fmask pI1856) (cmask pI1856) (hmask pI1856) 1515 341 (true, I1856_cp2.1, I1856_cp2.2)) ∧ intTest pI1856 (runFrom pI1856 (fmask pI1856) (cmask pI1856) (hmask pI1856) 1515 341 (true, I1856_cp2.1, I1856_cp2.2)) 1856 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1856_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1856_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1856_fin) true) I1856_seg1) I1856_seg2) (by decide) rfl I1856_fin intTest_fst
theorem link1856 : linkOK pL1856 pH1856 pI1856 = true := by decide +kernel
theorem cvx1856 : ConvexBetweenHumps 1856 :=
  cvx_of L1856_ok H1856_ok I1856_ok link1856 (by decide)
theorem cenlink1856 : cenLinkOK pI1856 1856 = true := by decide +kernel
theorem cen1856 : CenterUniqueMin 1856 ∧ DipHyp 1856 ∧ OnePointHyps 1856 :=
  cen_of L1856_ok H1856_ok I1856_ok link1856 cenlink1856

/-! ### `N = 1857` -/

def pL1857 : Prm := ⟨80, 37, 40, 1859, 11, 18446744073709551616, 104514917107295548, 104514917107295548⟩
def pH1857 : Prm := ⟨80, 37, 40, 1859, 11, 18446744073709551616, 104516016618923324, 104516016618923324⟩
def pI1857 : Prm := ⟨68, 34, 31, 1859, 11, 18446744073709551616, 104514917107295548, 104516016618923324⟩
noncomputable def L1857_cp1 : Nat × Nat := t7val% (fastRun pL1857 1 1071 (init pL1857) (init pL1857))
theorem L1857_seg1 : segOK pL1857 1 1071 (init pL1857) (init pL1857) L1857_cp1.1 L1857_cp1.2 = true := by
  decide +kernel
noncomputable def L1857_cp2 : Nat × Nat := t7val% (fastRun pL1857 1 1515 (init pL1857) (init pL1857))
theorem L1857_seg2 : segOK pL1857 1072 444 L1857_cp1.1 L1857_cp1.2 L1857_cp2.1 L1857_cp2.2 = true := by
  decide +kernel
theorem L1857_fin : (prmOK pL1857 1857 && ptTest pL1857 (runFrom pL1857 (fmask pL1857) (cmask pL1857) (hmask pL1857) 1516 341 (true, L1857_cp2.1, L1857_cp2.2)) 1857 929 false) = true := by
  decide +kernel
theorem L1857_ok : RunOK pL1857 1857 (runFrom pL1857 (fmask pL1857) (cmask pL1857) (hmask pL1857) 1516 341 (true, L1857_cp2.1, L1857_cp2.2)) ∧ ptTest pL1857 (runFrom pL1857 (fmask pL1857) (cmask pL1857) (hmask pL1857) 1516 341 (true, L1857_cp2.1, L1857_cp2.2)) 1857 929 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1857_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1857_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1857_fin) true) L1857_seg1) L1857_seg2) (by decide) rfl L1857_fin ptTest_fst
noncomputable def H1857_cp1 : Nat × Nat := t7val% (fastRun pH1857 1 1071 (init pH1857) (init pH1857))
theorem H1857_seg1 : segOK pH1857 1 1071 (init pH1857) (init pH1857) H1857_cp1.1 H1857_cp1.2 = true := by
  decide +kernel
noncomputable def H1857_cp2 : Nat × Nat := t7val% (fastRun pH1857 1 1515 (init pH1857) (init pH1857))
theorem H1857_seg2 : segOK pH1857 1072 444 H1857_cp1.1 H1857_cp1.2 H1857_cp2.1 H1857_cp2.2 = true := by
  decide +kernel
theorem H1857_fin : (prmOK pH1857 1857 && ptTest pH1857 (runFrom pH1857 (fmask pH1857) (cmask pH1857) (hmask pH1857) 1516 341 (true, H1857_cp2.1, H1857_cp2.2)) 1857 929 true) = true := by
  decide +kernel
theorem H1857_ok : RunOK pH1857 1857 (runFrom pH1857 (fmask pH1857) (cmask pH1857) (hmask pH1857) 1516 341 (true, H1857_cp2.1, H1857_cp2.2)) ∧ ptTest pH1857 (runFrom pH1857 (fmask pH1857) (cmask pH1857) (hmask pH1857) 1516 341 (true, H1857_cp2.1, H1857_cp2.2)) 1857 929 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1857_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1857_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1857_fin) true) H1857_seg1) H1857_seg2) (by decide) rfl H1857_fin ptTest_fst
noncomputable def I1857_cp1 : Nat × Nat := t7val% (fastRun pI1857 1 1071 (init pI1857) (init pI1857))
theorem I1857_seg1 : segOK pI1857 1 1071 (init pI1857) (init pI1857) I1857_cp1.1 I1857_cp1.2 = true := by
  decide +kernel
noncomputable def I1857_cp2 : Nat × Nat := t7val% (fastRun pI1857 1 1515 (init pI1857) (init pI1857))
theorem I1857_seg2 : segOK pI1857 1072 444 I1857_cp1.1 I1857_cp1.2 I1857_cp2.1 I1857_cp2.2 = true := by
  decide +kernel
theorem I1857_fin : (prmOK pI1857 1857 && intTest pI1857 (runFrom pI1857 (fmask pI1857) (cmask pI1857) (hmask pI1857) 1516 341 (true, I1857_cp2.1, I1857_cp2.2)) 1857 21 false) = true := by
  decide +kernel
theorem I1857_ok : RunOK pI1857 1857 (runFrom pI1857 (fmask pI1857) (cmask pI1857) (hmask pI1857) 1516 341 (true, I1857_cp2.1, I1857_cp2.2)) ∧ intTest pI1857 (runFrom pI1857 (fmask pI1857) (cmask pI1857) (hmask pI1857) 1516 341 (true, I1857_cp2.1, I1857_cp2.2)) 1857 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1857_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1857_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1857_fin) true) I1857_seg1) I1857_seg2) (by decide) rfl I1857_fin intTest_fst
theorem link1857 : linkOK pL1857 pH1857 pI1857 = true := by decide +kernel
theorem cvx1857 : ConvexBetweenHumps 1857 :=
  cvx_of L1857_ok H1857_ok I1857_ok link1857 (by decide)

/-! ### `N = 1858` -/

def pL1858 : Prm := ⟨80, 37, 40, 1860, 11, 18446744073709551616, 104468749593956914, 104468749593956914⟩
def pH1858 : Prm := ⟨80, 37, 40, 1860, 11, 18446744073709551616, 104469849105584690, 104469849105584690⟩
def pI1858 : Prm := ⟨68, 34, 31, 1860, 11, 18446744073709551616, 104468749593956914, 104469849105584690⟩
noncomputable def L1858_cp1 : Nat × Nat := t7val% (fastRun pL1858 1 1072 (init pL1858) (init pL1858))
theorem L1858_seg1 : segOK pL1858 1 1072 (init pL1858) (init pL1858) L1858_cp1.1 L1858_cp1.2 = true := by
  decide +kernel
noncomputable def L1858_cp2 : Nat × Nat := t7val% (fastRun pL1858 1 1516 (init pL1858) (init pL1858))
theorem L1858_seg2 : segOK pL1858 1073 444 L1858_cp1.1 L1858_cp1.2 L1858_cp2.1 L1858_cp2.2 = true := by
  decide +kernel
theorem L1858_fin : (prmOK pL1858 1858 && ptTest pL1858 (runFrom pL1858 (fmask pL1858) (cmask pL1858) (hmask pL1858) 1517 341 (true, L1858_cp2.1, L1858_cp2.2)) 1858 929 false) = true := by
  decide +kernel
theorem L1858_ok : RunOK pL1858 1858 (runFrom pL1858 (fmask pL1858) (cmask pL1858) (hmask pL1858) 1517 341 (true, L1858_cp2.1, L1858_cp2.2)) ∧ ptTest pL1858 (runFrom pL1858 (fmask pL1858) (cmask pL1858) (hmask pL1858) 1517 341 (true, L1858_cp2.1, L1858_cp2.2)) 1858 929 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1858_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1858_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1858_fin) true) L1858_seg1) L1858_seg2) (by decide) rfl L1858_fin ptTest_fst
noncomputable def H1858_cp1 : Nat × Nat := t7val% (fastRun pH1858 1 1072 (init pH1858) (init pH1858))
theorem H1858_seg1 : segOK pH1858 1 1072 (init pH1858) (init pH1858) H1858_cp1.1 H1858_cp1.2 = true := by
  decide +kernel
noncomputable def H1858_cp2 : Nat × Nat := t7val% (fastRun pH1858 1 1516 (init pH1858) (init pH1858))
theorem H1858_seg2 : segOK pH1858 1073 444 H1858_cp1.1 H1858_cp1.2 H1858_cp2.1 H1858_cp2.2 = true := by
  decide +kernel
theorem H1858_fin : (prmOK pH1858 1858 && ptTest pH1858 (runFrom pH1858 (fmask pH1858) (cmask pH1858) (hmask pH1858) 1517 341 (true, H1858_cp2.1, H1858_cp2.2)) 1858 929 true) = true := by
  decide +kernel
theorem H1858_ok : RunOK pH1858 1858 (runFrom pH1858 (fmask pH1858) (cmask pH1858) (hmask pH1858) 1517 341 (true, H1858_cp2.1, H1858_cp2.2)) ∧ ptTest pH1858 (runFrom pH1858 (fmask pH1858) (cmask pH1858) (hmask pH1858) 1517 341 (true, H1858_cp2.1, H1858_cp2.2)) 1858 929 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1858_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1858_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1858_fin) true) H1858_seg1) H1858_seg2) (by decide) rfl H1858_fin ptTest_fst
noncomputable def I1858_cp1 : Nat × Nat := t7val% (fastRun pI1858 1 1072 (init pI1858) (init pI1858))
theorem I1858_seg1 : segOK pI1858 1 1072 (init pI1858) (init pI1858) I1858_cp1.1 I1858_cp1.2 = true := by
  decide +kernel
noncomputable def I1858_cp2 : Nat × Nat := t7val% (fastRun pI1858 1 1516 (init pI1858) (init pI1858))
theorem I1858_seg2 : segOK pI1858 1073 444 I1858_cp1.1 I1858_cp1.2 I1858_cp2.1 I1858_cp2.2 = true := by
  decide +kernel
theorem I1858_fin : (prmOK pI1858 1858 && intTest pI1858 (runFrom pI1858 (fmask pI1858) (cmask pI1858) (hmask pI1858) 1517 341 (true, I1858_cp2.1, I1858_cp2.2)) 1858 21 true) = true := by
  decide +kernel
theorem I1858_ok : RunOK pI1858 1858 (runFrom pI1858 (fmask pI1858) (cmask pI1858) (hmask pI1858) 1517 341 (true, I1858_cp2.1, I1858_cp2.2)) ∧ intTest pI1858 (runFrom pI1858 (fmask pI1858) (cmask pI1858) (hmask pI1858) 1517 341 (true, I1858_cp2.1, I1858_cp2.2)) 1858 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1858_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1858_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1858_fin) true) I1858_seg1) I1858_seg2) (by decide) rfl I1858_fin intTest_fst
theorem link1858 : linkOK pL1858 pH1858 pI1858 = true := by decide +kernel
theorem cvx1858 : ConvexBetweenHumps 1858 :=
  cvx_of L1858_ok H1858_ok I1858_ok link1858 (by decide)
theorem cenlink1858 : cenLinkOK pI1858 1858 = true := by decide +kernel
theorem cen1858 : CenterUniqueMin 1858 ∧ DipHyp 1858 ∧ OnePointHyps 1858 :=
  cen_of L1858_ok H1858_ok I1858_ok link1858 cenlink1858

/-! ### `N = 1859` -/

def pL1859 : Prm := ⟨80, 37, 40, 1861, 11, 18446744073709551616, 104422608860605203, 104422608860605203⟩
def pH1859 : Prm := ⟨80, 37, 40, 1861, 11, 18446744073709551616, 104423708372232979, 104423708372232979⟩
def pI1859 : Prm := ⟨68, 34, 31, 1861, 11, 18446744073709551616, 104422608860605203, 104423708372232979⟩
noncomputable def L1859_cp1 : Nat × Nat := t7val% (fastRun pL1859 1 1072 (init pL1859) (init pL1859))
theorem L1859_seg1 : segOK pL1859 1 1072 (init pL1859) (init pL1859) L1859_cp1.1 L1859_cp1.2 = true := by
  decide +kernel
noncomputable def L1859_cp2 : Nat × Nat := t7val% (fastRun pL1859 1 1517 (init pL1859) (init pL1859))
theorem L1859_seg2 : segOK pL1859 1073 445 L1859_cp1.1 L1859_cp1.2 L1859_cp2.1 L1859_cp2.2 = true := by
  decide +kernel
theorem L1859_fin : (prmOK pL1859 1859 && ptTest pL1859 (runFrom pL1859 (fmask pL1859) (cmask pL1859) (hmask pL1859) 1518 341 (true, L1859_cp2.1, L1859_cp2.2)) 1859 930 false) = true := by
  decide +kernel
theorem L1859_ok : RunOK pL1859 1859 (runFrom pL1859 (fmask pL1859) (cmask pL1859) (hmask pL1859) 1518 341 (true, L1859_cp2.1, L1859_cp2.2)) ∧ ptTest pL1859 (runFrom pL1859 (fmask pL1859) (cmask pL1859) (hmask pL1859) 1518 341 (true, L1859_cp2.1, L1859_cp2.2)) 1859 930 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1859_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1859_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1859_fin) true) L1859_seg1) L1859_seg2) (by decide) rfl L1859_fin ptTest_fst
noncomputable def H1859_cp1 : Nat × Nat := t7val% (fastRun pH1859 1 1072 (init pH1859) (init pH1859))
theorem H1859_seg1 : segOK pH1859 1 1072 (init pH1859) (init pH1859) H1859_cp1.1 H1859_cp1.2 = true := by
  decide +kernel
noncomputable def H1859_cp2 : Nat × Nat := t7val% (fastRun pH1859 1 1517 (init pH1859) (init pH1859))
theorem H1859_seg2 : segOK pH1859 1073 445 H1859_cp1.1 H1859_cp1.2 H1859_cp2.1 H1859_cp2.2 = true := by
  decide +kernel
theorem H1859_fin : (prmOK pH1859 1859 && ptTest pH1859 (runFrom pH1859 (fmask pH1859) (cmask pH1859) (hmask pH1859) 1518 341 (true, H1859_cp2.1, H1859_cp2.2)) 1859 930 true) = true := by
  decide +kernel
theorem H1859_ok : RunOK pH1859 1859 (runFrom pH1859 (fmask pH1859) (cmask pH1859) (hmask pH1859) 1518 341 (true, H1859_cp2.1, H1859_cp2.2)) ∧ ptTest pH1859 (runFrom pH1859 (fmask pH1859) (cmask pH1859) (hmask pH1859) 1518 341 (true, H1859_cp2.1, H1859_cp2.2)) 1859 930 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1859_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1859_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1859_fin) true) H1859_seg1) H1859_seg2) (by decide) rfl H1859_fin ptTest_fst
noncomputable def I1859_cp1 : Nat × Nat := t7val% (fastRun pI1859 1 1072 (init pI1859) (init pI1859))
theorem I1859_seg1 : segOK pI1859 1 1072 (init pI1859) (init pI1859) I1859_cp1.1 I1859_cp1.2 = true := by
  decide +kernel
noncomputable def I1859_cp2 : Nat × Nat := t7val% (fastRun pI1859 1 1517 (init pI1859) (init pI1859))
theorem I1859_seg2 : segOK pI1859 1073 445 I1859_cp1.1 I1859_cp1.2 I1859_cp2.1 I1859_cp2.2 = true := by
  decide +kernel
theorem I1859_fin : (prmOK pI1859 1859 && intTest pI1859 (runFrom pI1859 (fmask pI1859) (cmask pI1859) (hmask pI1859) 1518 341 (true, I1859_cp2.1, I1859_cp2.2)) 1859 21 false) = true := by
  decide +kernel
theorem I1859_ok : RunOK pI1859 1859 (runFrom pI1859 (fmask pI1859) (cmask pI1859) (hmask pI1859) 1518 341 (true, I1859_cp2.1, I1859_cp2.2)) ∧ intTest pI1859 (runFrom pI1859 (fmask pI1859) (cmask pI1859) (hmask pI1859) 1518 341 (true, I1859_cp2.1, I1859_cp2.2)) 1859 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1859_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1859_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1859_fin) true) I1859_seg1) I1859_seg2) (by decide) rfl I1859_fin intTest_fst
theorem link1859 : linkOK pL1859 pH1859 pI1859 = true := by decide +kernel
theorem cvx1859 : ConvexBetweenHumps 1859 :=
  cvx_of L1859_ok H1859_ok I1859_ok link1859 (by decide)

/-! ### `N = 1860` -/

def pL1860 : Prm := ⟨80, 37, 40, 1862, 11, 18446744073709551616, 104376529759061373, 104376529759061373⟩
def pH1860 : Prm := ⟨80, 37, 40, 1862, 11, 18446744073709551616, 104377629270689149, 104377629270689149⟩
def pI1860 : Prm := ⟨68, 34, 31, 1862, 11, 18446744073709551616, 104376529759061373, 104377629270689149⟩
noncomputable def L1860_cp1 : Nat × Nat := t7val% (fastRun pL1860 1 1073 (init pL1860) (init pL1860))
theorem L1860_seg1 : segOK pL1860 1 1073 (init pL1860) (init pL1860) L1860_cp1.1 L1860_cp1.2 = true := by
  decide +kernel
noncomputable def L1860_cp2 : Nat × Nat := t7val% (fastRun pL1860 1 1518 (init pL1860) (init pL1860))
theorem L1860_seg2 : segOK pL1860 1074 445 L1860_cp1.1 L1860_cp1.2 L1860_cp2.1 L1860_cp2.2 = true := by
  decide +kernel
theorem L1860_fin : (prmOK pL1860 1860 && ptTest pL1860 (runFrom pL1860 (fmask pL1860) (cmask pL1860) (hmask pL1860) 1519 341 (true, L1860_cp2.1, L1860_cp2.2)) 1860 930 false) = true := by
  decide +kernel
theorem L1860_ok : RunOK pL1860 1860 (runFrom pL1860 (fmask pL1860) (cmask pL1860) (hmask pL1860) 1519 341 (true, L1860_cp2.1, L1860_cp2.2)) ∧ ptTest pL1860 (runFrom pL1860 (fmask pL1860) (cmask pL1860) (hmask pL1860) 1519 341 (true, L1860_cp2.1, L1860_cp2.2)) 1860 930 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1860_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1860_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1860_fin) true) L1860_seg1) L1860_seg2) (by decide) rfl L1860_fin ptTest_fst
noncomputable def H1860_cp1 : Nat × Nat := t7val% (fastRun pH1860 1 1073 (init pH1860) (init pH1860))
theorem H1860_seg1 : segOK pH1860 1 1073 (init pH1860) (init pH1860) H1860_cp1.1 H1860_cp1.2 = true := by
  decide +kernel
noncomputable def H1860_cp2 : Nat × Nat := t7val% (fastRun pH1860 1 1518 (init pH1860) (init pH1860))
theorem H1860_seg2 : segOK pH1860 1074 445 H1860_cp1.1 H1860_cp1.2 H1860_cp2.1 H1860_cp2.2 = true := by
  decide +kernel
theorem H1860_fin : (prmOK pH1860 1860 && ptTest pH1860 (runFrom pH1860 (fmask pH1860) (cmask pH1860) (hmask pH1860) 1519 341 (true, H1860_cp2.1, H1860_cp2.2)) 1860 930 true) = true := by
  decide +kernel
theorem H1860_ok : RunOK pH1860 1860 (runFrom pH1860 (fmask pH1860) (cmask pH1860) (hmask pH1860) 1519 341 (true, H1860_cp2.1, H1860_cp2.2)) ∧ ptTest pH1860 (runFrom pH1860 (fmask pH1860) (cmask pH1860) (hmask pH1860) 1519 341 (true, H1860_cp2.1, H1860_cp2.2)) 1860 930 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1860_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1860_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1860_fin) true) H1860_seg1) H1860_seg2) (by decide) rfl H1860_fin ptTest_fst
noncomputable def I1860_cp1 : Nat × Nat := t7val% (fastRun pI1860 1 1073 (init pI1860) (init pI1860))
theorem I1860_seg1 : segOK pI1860 1 1073 (init pI1860) (init pI1860) I1860_cp1.1 I1860_cp1.2 = true := by
  decide +kernel
noncomputable def I1860_cp2 : Nat × Nat := t7val% (fastRun pI1860 1 1518 (init pI1860) (init pI1860))
theorem I1860_seg2 : segOK pI1860 1074 445 I1860_cp1.1 I1860_cp1.2 I1860_cp2.1 I1860_cp2.2 = true := by
  decide +kernel
theorem I1860_fin : (prmOK pI1860 1860 && intTest pI1860 (runFrom pI1860 (fmask pI1860) (cmask pI1860) (hmask pI1860) 1519 341 (true, I1860_cp2.1, I1860_cp2.2)) 1860 21 true) = true := by
  decide +kernel
theorem I1860_ok : RunOK pI1860 1860 (runFrom pI1860 (fmask pI1860) (cmask pI1860) (hmask pI1860) 1519 341 (true, I1860_cp2.1, I1860_cp2.2)) ∧ intTest pI1860 (runFrom pI1860 (fmask pI1860) (cmask pI1860) (hmask pI1860) 1519 341 (true, I1860_cp2.1, I1860_cp2.2)) 1860 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1860_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1860_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1860_fin) true) I1860_seg1) I1860_seg2) (by decide) rfl I1860_fin intTest_fst
theorem link1860 : linkOK pL1860 pH1860 pI1860 = true := by decide +kernel
theorem cvx1860 : ConvexBetweenHumps 1860 :=
  cvx_of L1860_ok H1860_ok I1860_ok link1860 (by decide)
theorem cenlink1860 : cenLinkOK pI1860 1860 = true := by decide +kernel
theorem cen1860 : CenterUniqueMin 1860 ∧ DipHyp 1860 ∧ OnePointHyps 1860 :=
  cen_of L1860_ok H1860_ok I1860_ok link1860 cenlink1860

/-! ### `N = 1861` -/

def pL1861 : Prm := ⟨80, 37, 40, 1863, 11, 18446744073709551616, 104330477363699043, 104330477363699043⟩
def pH1861 : Prm := ⟨80, 37, 40, 1863, 11, 18446744073709551616, 104331576875326819, 104331576875326819⟩
def pI1861 : Prm := ⟨68, 34, 31, 1863, 11, 18446744073709551616, 104330477363699043, 104331576875326819⟩
noncomputable def L1861_cp1 : Nat × Nat := t7val% (fastRun pL1861 1 1073 (init pL1861) (init pL1861))
theorem L1861_seg1 : segOK pL1861 1 1073 (init pL1861) (init pL1861) L1861_cp1.1 L1861_cp1.2 = true := by
  decide +kernel
noncomputable def L1861_cp2 : Nat × Nat := t7val% (fastRun pL1861 1 1519 (init pL1861) (init pL1861))
theorem L1861_seg2 : segOK pL1861 1074 446 L1861_cp1.1 L1861_cp1.2 L1861_cp2.1 L1861_cp2.2 = true := by
  decide +kernel
theorem L1861_fin : (prmOK pL1861 1861 && ptTest pL1861 (runFrom pL1861 (fmask pL1861) (cmask pL1861) (hmask pL1861) 1520 341 (true, L1861_cp2.1, L1861_cp2.2)) 1861 931 false) = true := by
  decide +kernel
theorem L1861_ok : RunOK pL1861 1861 (runFrom pL1861 (fmask pL1861) (cmask pL1861) (hmask pL1861) 1520 341 (true, L1861_cp2.1, L1861_cp2.2)) ∧ ptTest pL1861 (runFrom pL1861 (fmask pL1861) (cmask pL1861) (hmask pL1861) 1520 341 (true, L1861_cp2.1, L1861_cp2.2)) 1861 931 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1861_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1861_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1861_fin) true) L1861_seg1) L1861_seg2) (by decide) rfl L1861_fin ptTest_fst
noncomputable def H1861_cp1 : Nat × Nat := t7val% (fastRun pH1861 1 1073 (init pH1861) (init pH1861))
theorem H1861_seg1 : segOK pH1861 1 1073 (init pH1861) (init pH1861) H1861_cp1.1 H1861_cp1.2 = true := by
  decide +kernel
noncomputable def H1861_cp2 : Nat × Nat := t7val% (fastRun pH1861 1 1519 (init pH1861) (init pH1861))
theorem H1861_seg2 : segOK pH1861 1074 446 H1861_cp1.1 H1861_cp1.2 H1861_cp2.1 H1861_cp2.2 = true := by
  decide +kernel
theorem H1861_fin : (prmOK pH1861 1861 && ptTest pH1861 (runFrom pH1861 (fmask pH1861) (cmask pH1861) (hmask pH1861) 1520 341 (true, H1861_cp2.1, H1861_cp2.2)) 1861 931 true) = true := by
  decide +kernel
theorem H1861_ok : RunOK pH1861 1861 (runFrom pH1861 (fmask pH1861) (cmask pH1861) (hmask pH1861) 1520 341 (true, H1861_cp2.1, H1861_cp2.2)) ∧ ptTest pH1861 (runFrom pH1861 (fmask pH1861) (cmask pH1861) (hmask pH1861) 1520 341 (true, H1861_cp2.1, H1861_cp2.2)) 1861 931 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1861_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1861_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1861_fin) true) H1861_seg1) H1861_seg2) (by decide) rfl H1861_fin ptTest_fst
noncomputable def I1861_cp1 : Nat × Nat := t7val% (fastRun pI1861 1 1073 (init pI1861) (init pI1861))
theorem I1861_seg1 : segOK pI1861 1 1073 (init pI1861) (init pI1861) I1861_cp1.1 I1861_cp1.2 = true := by
  decide +kernel
noncomputable def I1861_cp2 : Nat × Nat := t7val% (fastRun pI1861 1 1519 (init pI1861) (init pI1861))
theorem I1861_seg2 : segOK pI1861 1074 446 I1861_cp1.1 I1861_cp1.2 I1861_cp2.1 I1861_cp2.2 = true := by
  decide +kernel
theorem I1861_fin : (prmOK pI1861 1861 && intTest pI1861 (runFrom pI1861 (fmask pI1861) (cmask pI1861) (hmask pI1861) 1520 341 (true, I1861_cp2.1, I1861_cp2.2)) 1861 21 false) = true := by
  decide +kernel
theorem I1861_ok : RunOK pI1861 1861 (runFrom pI1861 (fmask pI1861) (cmask pI1861) (hmask pI1861) 1520 341 (true, I1861_cp2.1, I1861_cp2.2)) ∧ intTest pI1861 (runFrom pI1861 (fmask pI1861) (cmask pI1861) (hmask pI1861) 1520 341 (true, I1861_cp2.1, I1861_cp2.2)) 1861 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1861_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1861_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1861_fin) true) I1861_seg1) I1861_seg2) (by decide) rfl I1861_fin intTest_fst
theorem link1861 : linkOK pL1861 pH1861 pI1861 = true := by decide +kernel
theorem cvx1861 : ConvexBetweenHumps 1861 :=
  cvx_of L1861_ok H1861_ok I1861_ok link1861 (by decide)

/-! ### `N = 1862` -/

def pL1862 : Prm := ⟨80, 37, 40, 1864, 11, 18446744073709551616, 104284486412448974, 104284486412448974⟩
def pH1862 : Prm := ⟨80, 37, 40, 1864, 11, 18446744073709551616, 104285585924076750, 104285585924076750⟩
def pI1862 : Prm := ⟨68, 34, 31, 1864, 11, 18446744073709551616, 104284486412448974, 104285585924076750⟩
noncomputable def L1862_cp1 : Nat × Nat := t7val% (fastRun pL1862 1 1074 (init pL1862) (init pL1862))
theorem L1862_seg1 : segOK pL1862 1 1074 (init pL1862) (init pL1862) L1862_cp1.1 L1862_cp1.2 = true := by
  decide +kernel
noncomputable def L1862_cp2 : Nat × Nat := t7val% (fastRun pL1862 1 1519 (init pL1862) (init pL1862))
theorem L1862_seg2 : segOK pL1862 1075 445 L1862_cp1.1 L1862_cp1.2 L1862_cp2.1 L1862_cp2.2 = true := by
  decide +kernel
theorem L1862_fin : (prmOK pL1862 1862 && ptTest pL1862 (runFrom pL1862 (fmask pL1862) (cmask pL1862) (hmask pL1862) 1520 342 (true, L1862_cp2.1, L1862_cp2.2)) 1862 931 false) = true := by
  decide +kernel
theorem L1862_ok : RunOK pL1862 1862 (runFrom pL1862 (fmask pL1862) (cmask pL1862) (hmask pL1862) 1520 342 (true, L1862_cp2.1, L1862_cp2.2)) ∧ ptTest pL1862 (runFrom pL1862 (fmask pL1862) (cmask pL1862) (hmask pL1862) 1520 342 (true, L1862_cp2.1, L1862_cp2.2)) 1862 931 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1862_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1862_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1862_fin) true) L1862_seg1) L1862_seg2) (by decide) rfl L1862_fin ptTest_fst
noncomputable def H1862_cp1 : Nat × Nat := t7val% (fastRun pH1862 1 1074 (init pH1862) (init pH1862))
theorem H1862_seg1 : segOK pH1862 1 1074 (init pH1862) (init pH1862) H1862_cp1.1 H1862_cp1.2 = true := by
  decide +kernel
noncomputable def H1862_cp2 : Nat × Nat := t7val% (fastRun pH1862 1 1519 (init pH1862) (init pH1862))
theorem H1862_seg2 : segOK pH1862 1075 445 H1862_cp1.1 H1862_cp1.2 H1862_cp2.1 H1862_cp2.2 = true := by
  decide +kernel
theorem H1862_fin : (prmOK pH1862 1862 && ptTest pH1862 (runFrom pH1862 (fmask pH1862) (cmask pH1862) (hmask pH1862) 1520 342 (true, H1862_cp2.1, H1862_cp2.2)) 1862 931 true) = true := by
  decide +kernel
theorem H1862_ok : RunOK pH1862 1862 (runFrom pH1862 (fmask pH1862) (cmask pH1862) (hmask pH1862) 1520 342 (true, H1862_cp2.1, H1862_cp2.2)) ∧ ptTest pH1862 (runFrom pH1862 (fmask pH1862) (cmask pH1862) (hmask pH1862) 1520 342 (true, H1862_cp2.1, H1862_cp2.2)) 1862 931 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1862_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1862_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1862_fin) true) H1862_seg1) H1862_seg2) (by decide) rfl H1862_fin ptTest_fst
noncomputable def I1862_cp1 : Nat × Nat := t7val% (fastRun pI1862 1 1074 (init pI1862) (init pI1862))
theorem I1862_seg1 : segOK pI1862 1 1074 (init pI1862) (init pI1862) I1862_cp1.1 I1862_cp1.2 = true := by
  decide +kernel
noncomputable def I1862_cp2 : Nat × Nat := t7val% (fastRun pI1862 1 1519 (init pI1862) (init pI1862))
theorem I1862_seg2 : segOK pI1862 1075 445 I1862_cp1.1 I1862_cp1.2 I1862_cp2.1 I1862_cp2.2 = true := by
  decide +kernel
theorem I1862_fin : (prmOK pI1862 1862 && intTest pI1862 (runFrom pI1862 (fmask pI1862) (cmask pI1862) (hmask pI1862) 1520 342 (true, I1862_cp2.1, I1862_cp2.2)) 1862 21 true) = true := by
  decide +kernel
theorem I1862_ok : RunOK pI1862 1862 (runFrom pI1862 (fmask pI1862) (cmask pI1862) (hmask pI1862) 1520 342 (true, I1862_cp2.1, I1862_cp2.2)) ∧ intTest pI1862 (runFrom pI1862 (fmask pI1862) (cmask pI1862) (hmask pI1862) 1520 342 (true, I1862_cp2.1, I1862_cp2.2)) 1862 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1862_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1862_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1862_fin) true) I1862_seg1) I1862_seg2) (by decide) rfl I1862_fin intTest_fst
theorem link1862 : linkOK pL1862 pH1862 pI1862 = true := by decide +kernel
theorem cvx1862 : ConvexBetweenHumps 1862 :=
  cvx_of L1862_ok H1862_ok I1862_ok link1862 (by decide)
theorem cenlink1862 : cenLinkOK pI1862 1862 = true := by decide +kernel
theorem cen1862 : CenterUniqueMin 1862 ∧ DipHyp 1862 ∧ OnePointHyps 1862 :=
  cen_of L1862_ok H1862_ok I1862_ok link1862 cenlink1862

/-! ### `N = 1863` -/

def pL1863 : Prm := ⟨80, 37, 40, 1865, 11, 18446744073709551616, 104238522093851682, 104238522093851682⟩
def pH1863 : Prm := ⟨80, 37, 40, 1865, 11, 18446744073709551616, 104239621605479458, 104239621605479458⟩
def pI1863 : Prm := ⟨68, 34, 31, 1865, 11, 18446744073709551616, 104238522093851682, 104239621605479458⟩
noncomputable def L1863_cp1 : Nat × Nat := t7val% (fastRun pL1863 1 1075 (init pL1863) (init pL1863))
theorem L1863_seg1 : segOK pL1863 1 1075 (init pL1863) (init pL1863) L1863_cp1.1 L1863_cp1.2 = true := by
  decide +kernel
noncomputable def L1863_cp2 : Nat × Nat := t7val% (fastRun pL1863 1 1520 (init pL1863) (init pL1863))
theorem L1863_seg2 : segOK pL1863 1076 445 L1863_cp1.1 L1863_cp1.2 L1863_cp2.1 L1863_cp2.2 = true := by
  decide +kernel
theorem L1863_fin : (prmOK pL1863 1863 && ptTest pL1863 (runFrom pL1863 (fmask pL1863) (cmask pL1863) (hmask pL1863) 1521 342 (true, L1863_cp2.1, L1863_cp2.2)) 1863 932 false) = true := by
  decide +kernel
theorem L1863_ok : RunOK pL1863 1863 (runFrom pL1863 (fmask pL1863) (cmask pL1863) (hmask pL1863) 1521 342 (true, L1863_cp2.1, L1863_cp2.2)) ∧ ptTest pL1863 (runFrom pL1863 (fmask pL1863) (cmask pL1863) (hmask pL1863) 1521 342 (true, L1863_cp2.1, L1863_cp2.2)) 1863 932 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1863_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1863_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1863_fin) true) L1863_seg1) L1863_seg2) (by decide) rfl L1863_fin ptTest_fst
noncomputable def H1863_cp1 : Nat × Nat := t7val% (fastRun pH1863 1 1075 (init pH1863) (init pH1863))
theorem H1863_seg1 : segOK pH1863 1 1075 (init pH1863) (init pH1863) H1863_cp1.1 H1863_cp1.2 = true := by
  decide +kernel
noncomputable def H1863_cp2 : Nat × Nat := t7val% (fastRun pH1863 1 1520 (init pH1863) (init pH1863))
theorem H1863_seg2 : segOK pH1863 1076 445 H1863_cp1.1 H1863_cp1.2 H1863_cp2.1 H1863_cp2.2 = true := by
  decide +kernel
theorem H1863_fin : (prmOK pH1863 1863 && ptTest pH1863 (runFrom pH1863 (fmask pH1863) (cmask pH1863) (hmask pH1863) 1521 342 (true, H1863_cp2.1, H1863_cp2.2)) 1863 932 true) = true := by
  decide +kernel
theorem H1863_ok : RunOK pH1863 1863 (runFrom pH1863 (fmask pH1863) (cmask pH1863) (hmask pH1863) 1521 342 (true, H1863_cp2.1, H1863_cp2.2)) ∧ ptTest pH1863 (runFrom pH1863 (fmask pH1863) (cmask pH1863) (hmask pH1863) 1521 342 (true, H1863_cp2.1, H1863_cp2.2)) 1863 932 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1863_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1863_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1863_fin) true) H1863_seg1) H1863_seg2) (by decide) rfl H1863_fin ptTest_fst
noncomputable def I1863_cp1 : Nat × Nat := t7val% (fastRun pI1863 1 1075 (init pI1863) (init pI1863))
theorem I1863_seg1 : segOK pI1863 1 1075 (init pI1863) (init pI1863) I1863_cp1.1 I1863_cp1.2 = true := by
  decide +kernel
noncomputable def I1863_cp2 : Nat × Nat := t7val% (fastRun pI1863 1 1520 (init pI1863) (init pI1863))
theorem I1863_seg2 : segOK pI1863 1076 445 I1863_cp1.1 I1863_cp1.2 I1863_cp2.1 I1863_cp2.2 = true := by
  decide +kernel
theorem I1863_fin : (prmOK pI1863 1863 && intTest pI1863 (runFrom pI1863 (fmask pI1863) (cmask pI1863) (hmask pI1863) 1521 342 (true, I1863_cp2.1, I1863_cp2.2)) 1863 21 false) = true := by
  decide +kernel
theorem I1863_ok : RunOK pI1863 1863 (runFrom pI1863 (fmask pI1863) (cmask pI1863) (hmask pI1863) 1521 342 (true, I1863_cp2.1, I1863_cp2.2)) ∧ intTest pI1863 (runFrom pI1863 (fmask pI1863) (cmask pI1863) (hmask pI1863) 1521 342 (true, I1863_cp2.1, I1863_cp2.2)) 1863 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1863_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1863_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1863_fin) true) I1863_seg1) I1863_seg2) (by decide) rfl I1863_fin intTest_fst
theorem link1863 : linkOK pL1863 pH1863 pI1863 = true := by decide +kernel
theorem cvx1863 : ConvexBetweenHumps 1863 :=
  cvx_of L1863_ok H1863_ok I1863_ok link1863 (by decide)

/-! ### `N = 1864` -/

def pL1864 : Prm := ⟨80, 37, 40, 1866, 11, 18446744073709551616, 104192619032427346, 104192619032427346⟩
def pH1864 : Prm := ⟨80, 37, 40, 1866, 11, 18446744073709551616, 104193718544055122, 104193718544055122⟩
def pI1864 : Prm := ⟨68, 34, 31, 1866, 11, 18446744073709551616, 104192619032427346, 104193718544055122⟩
noncomputable def L1864_cp1 : Nat × Nat := t7val% (fastRun pL1864 1 1075 (init pL1864) (init pL1864))
theorem L1864_seg1 : segOK pL1864 1 1075 (init pL1864) (init pL1864) L1864_cp1.1 L1864_cp1.2 = true := by
  decide +kernel
noncomputable def L1864_cp2 : Nat × Nat := t7val% (fastRun pL1864 1 1521 (init pL1864) (init pL1864))
theorem L1864_seg2 : segOK pL1864 1076 446 L1864_cp1.1 L1864_cp1.2 L1864_cp2.1 L1864_cp2.2 = true := by
  decide +kernel
theorem L1864_fin : (prmOK pL1864 1864 && ptTest pL1864 (runFrom pL1864 (fmask pL1864) (cmask pL1864) (hmask pL1864) 1522 342 (true, L1864_cp2.1, L1864_cp2.2)) 1864 932 false) = true := by
  decide +kernel
theorem L1864_ok : RunOK pL1864 1864 (runFrom pL1864 (fmask pL1864) (cmask pL1864) (hmask pL1864) 1522 342 (true, L1864_cp2.1, L1864_cp2.2)) ∧ ptTest pL1864 (runFrom pL1864 (fmask pL1864) (cmask pL1864) (hmask pL1864) 1522 342 (true, L1864_cp2.1, L1864_cp2.2)) 1864 932 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1864_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1864_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1864_fin) true) L1864_seg1) L1864_seg2) (by decide) rfl L1864_fin ptTest_fst
noncomputable def H1864_cp1 : Nat × Nat := t7val% (fastRun pH1864 1 1075 (init pH1864) (init pH1864))
theorem H1864_seg1 : segOK pH1864 1 1075 (init pH1864) (init pH1864) H1864_cp1.1 H1864_cp1.2 = true := by
  decide +kernel
noncomputable def H1864_cp2 : Nat × Nat := t7val% (fastRun pH1864 1 1521 (init pH1864) (init pH1864))
theorem H1864_seg2 : segOK pH1864 1076 446 H1864_cp1.1 H1864_cp1.2 H1864_cp2.1 H1864_cp2.2 = true := by
  decide +kernel
theorem H1864_fin : (prmOK pH1864 1864 && ptTest pH1864 (runFrom pH1864 (fmask pH1864) (cmask pH1864) (hmask pH1864) 1522 342 (true, H1864_cp2.1, H1864_cp2.2)) 1864 932 true) = true := by
  decide +kernel
theorem H1864_ok : RunOK pH1864 1864 (runFrom pH1864 (fmask pH1864) (cmask pH1864) (hmask pH1864) 1522 342 (true, H1864_cp2.1, H1864_cp2.2)) ∧ ptTest pH1864 (runFrom pH1864 (fmask pH1864) (cmask pH1864) (hmask pH1864) 1522 342 (true, H1864_cp2.1, H1864_cp2.2)) 1864 932 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1864_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1864_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1864_fin) true) H1864_seg1) H1864_seg2) (by decide) rfl H1864_fin ptTest_fst
noncomputable def I1864_cp1 : Nat × Nat := t7val% (fastRun pI1864 1 1075 (init pI1864) (init pI1864))
theorem I1864_seg1 : segOK pI1864 1 1075 (init pI1864) (init pI1864) I1864_cp1.1 I1864_cp1.2 = true := by
  decide +kernel
noncomputable def I1864_cp2 : Nat × Nat := t7val% (fastRun pI1864 1 1521 (init pI1864) (init pI1864))
theorem I1864_seg2 : segOK pI1864 1076 446 I1864_cp1.1 I1864_cp1.2 I1864_cp2.1 I1864_cp2.2 = true := by
  decide +kernel
theorem I1864_fin : (prmOK pI1864 1864 && intTest pI1864 (runFrom pI1864 (fmask pI1864) (cmask pI1864) (hmask pI1864) 1522 342 (true, I1864_cp2.1, I1864_cp2.2)) 1864 21 true) = true := by
  decide +kernel
theorem I1864_ok : RunOK pI1864 1864 (runFrom pI1864 (fmask pI1864) (cmask pI1864) (hmask pI1864) 1522 342 (true, I1864_cp2.1, I1864_cp2.2)) ∧ intTest pI1864 (runFrom pI1864 (fmask pI1864) (cmask pI1864) (hmask pI1864) 1522 342 (true, I1864_cp2.1, I1864_cp2.2)) 1864 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1864_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1864_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1864_fin) true) I1864_seg1) I1864_seg2) (by decide) rfl I1864_fin intTest_fst
theorem link1864 : linkOK pL1864 pH1864 pI1864 = true := by decide +kernel
theorem cvx1864 : ConvexBetweenHumps 1864 :=
  cvx_of L1864_ok H1864_ok I1864_ok link1864 (by decide)
theorem cenlink1864 : cenLinkOK pI1864 1864 = true := by decide +kernel
theorem cen1864 : CenterUniqueMin 1864 ∧ DipHyp 1864 ∧ OnePointHyps 1864 :=
  cen_of L1864_ok H1864_ok I1864_ok link1864 cenlink1864

/-! ### The range -/

theorem cvx_1854_1864 {N : ℕ} (h1 : 1854 ≤ N) (h2 : N ≤ 1864) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1858
  · by_cases h4 : N ≤ 1855
    · by_cases h6 : N ≤ 1854
      · obtain rfl : N = 1854 := by omega
        exact cvx1854
      · obtain rfl : N = 1855 := by omega
        exact cvx1855
    · by_cases h6 : N ≤ 1856
      · obtain rfl : N = 1856 := by omega
        exact cvx1856
      · by_cases h8 : N ≤ 1857
        · obtain rfl : N = 1857 := by omega
          exact cvx1857
        · obtain rfl : N = 1858 := by omega
          exact cvx1858
  · by_cases h4 : N ≤ 1861
    · by_cases h6 : N ≤ 1859
      · obtain rfl : N = 1859 := by omega
        exact cvx1859
      · by_cases h8 : N ≤ 1860
        · obtain rfl : N = 1860 := by omega
          exact cvx1860
        · obtain rfl : N = 1861 := by omega
          exact cvx1861
    · by_cases h6 : N ≤ 1862
      · obtain rfl : N = 1862 := by omega
        exact cvx1862
      · by_cases h8 : N ≤ 1863
        · obtain rfl : N = 1863 := by omega
          exact cvx1863
        · obtain rfl : N = 1864 := by omega
          exact cvx1864

theorem cen_1854_1864 {N : ℕ} (h1 : 1854 ≤ N) (h2 : N ≤ 1864) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1858
  · by_cases h4 : N ≤ 1854
    · obtain rfl : N = 1854 := by omega
      exact cen1854
    · by_cases h6 : N ≤ 1856
      · obtain rfl : N = 1856 := by omega
        exact cen1856
      · obtain rfl : N = 1858 := by omega
        exact cen1858
  · by_cases h4 : N ≤ 1860
    · obtain rfl : N = 1860 := by omega
      exact cen1860
    · by_cases h6 : N ≤ 1862
      · obtain rfl : N = 1862 := by omega
        exact cen1862
      · obtain rfl : N = 1864 := by omega
        exact cen1864

end Kagey131.PaperD.T7
