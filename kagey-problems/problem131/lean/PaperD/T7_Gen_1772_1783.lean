import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1772, …, 1783` (generated)

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

/-! ### `N = 1772` -/

def pL1772 : Prm := ⟨80, 37, 40, 1774, 11, 18446744073709551616, 108608920937599942, 108608920937599942⟩
def pH1772 : Prm := ⟨80, 37, 40, 1774, 11, 18446744073709551616, 108610020449227718, 108610020449227718⟩
def pI1772 : Prm := ⟨67, 34, 30, 1774, 11, 18446744073709551616, 108608920937599942, 108610020449227718⟩
noncomputable def L1772_cp1 : Nat × Nat := t7val% (fastRun pL1772 1 1022 (init pL1772) (init pL1772))
theorem L1772_seg1 : segOK pL1772 1 1022 (init pL1772) (init pL1772) L1772_cp1.1 L1772_cp1.2 = true := by
  decide +kernel
noncomputable def L1772_cp2 : Nat × Nat := t7val% (fastRun pL1772 1 1446 (init pL1772) (init pL1772))
theorem L1772_seg2 : segOK pL1772 1023 424 L1772_cp1.1 L1772_cp1.2 L1772_cp2.1 L1772_cp2.2 = true := by
  decide +kernel
theorem L1772_fin : (prmOK pL1772 1772 && ptTest pL1772 (runFrom pL1772 (fmask pL1772) (cmask pL1772) (hmask pL1772) 1447 325 (true, L1772_cp2.1, L1772_cp2.2)) 1772 886 false) = true := by
  decide +kernel
theorem L1772_ok : RunOK pL1772 1772 (runFrom pL1772 (fmask pL1772) (cmask pL1772) (hmask pL1772) 1447 325 (true, L1772_cp2.1, L1772_cp2.2)) ∧ ptTest pL1772 (runFrom pL1772 (fmask pL1772) (cmask pL1772) (hmask pL1772) 1447 325 (true, L1772_cp2.1, L1772_cp2.2)) 1772 886 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1772_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1772_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1772_fin) true) L1772_seg1) L1772_seg2) (by decide) rfl L1772_fin ptTest_fst
noncomputable def H1772_cp1 : Nat × Nat := t7val% (fastRun pH1772 1 1022 (init pH1772) (init pH1772))
theorem H1772_seg1 : segOK pH1772 1 1022 (init pH1772) (init pH1772) H1772_cp1.1 H1772_cp1.2 = true := by
  decide +kernel
noncomputable def H1772_cp2 : Nat × Nat := t7val% (fastRun pH1772 1 1446 (init pH1772) (init pH1772))
theorem H1772_seg2 : segOK pH1772 1023 424 H1772_cp1.1 H1772_cp1.2 H1772_cp2.1 H1772_cp2.2 = true := by
  decide +kernel
theorem H1772_fin : (prmOK pH1772 1772 && ptTest pH1772 (runFrom pH1772 (fmask pH1772) (cmask pH1772) (hmask pH1772) 1447 325 (true, H1772_cp2.1, H1772_cp2.2)) 1772 886 true) = true := by
  decide +kernel
theorem H1772_ok : RunOK pH1772 1772 (runFrom pH1772 (fmask pH1772) (cmask pH1772) (hmask pH1772) 1447 325 (true, H1772_cp2.1, H1772_cp2.2)) ∧ ptTest pH1772 (runFrom pH1772 (fmask pH1772) (cmask pH1772) (hmask pH1772) 1447 325 (true, H1772_cp2.1, H1772_cp2.2)) 1772 886 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1772_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1772_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1772_fin) true) H1772_seg1) H1772_seg2) (by decide) rfl H1772_fin ptTest_fst
noncomputable def I1772_cp1 : Nat × Nat := t7val% (fastRun pI1772 1 1252 (init pI1772) (init pI1772))
theorem I1772_seg1 : segOK pI1772 1 1252 (init pI1772) (init pI1772) I1772_cp1.1 I1772_cp1.2 = true := by
  decide +kernel
theorem I1772_fin : (prmOK pI1772 1772 && intTest pI1772 (runFrom pI1772 (fmask pI1772) (cmask pI1772) (hmask pI1772) 1253 519 (true, I1772_cp1.1, I1772_cp1.2)) 1772 21 true) = true := by
  decide +kernel
theorem I1772_ok : RunOK pI1772 1772 (runFrom pI1772 (fmask pI1772) (cmask pI1772) (hmask pI1772) 1253 519 (true, I1772_cp1.1, I1772_cp1.2)) ∧ intTest pI1772 (runFrom pI1772 (fmask pI1772) (cmask pI1772) (hmask pI1772) 1253 519 (true, I1772_cp1.1, I1772_cp1.2)) 1772 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1772_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1772_fin) true) I1772_seg1) (by decide) rfl I1772_fin intTest_fst
theorem link1772 : linkOK pL1772 pH1772 pI1772 = true := by decide +kernel
theorem cvx1772 : ConvexBetweenHumps 1772 :=
  cvx_of L1772_ok H1772_ok I1772_ok link1772 (by decide)
theorem cenlink1772 : cenLinkOK pI1772 1772 = true := by decide +kernel
theorem cen1772 : CenterUniqueMin 1772 ∧ DipHyp 1772 ∧ OnePointHyps 1772 :=
  cen_of L1772_ok H1772_ok I1772_ok link1772 cenlink1772

/-! ### `N = 1773` -/

def pL1773 : Prm := ⟨80, 37, 40, 1775, 11, 18446744073709551616, 108558718789512355, 108558718789512355⟩
def pH1773 : Prm := ⟨80, 37, 40, 1775, 11, 18446744073709551616, 108559818301140131, 108559818301140131⟩
def pI1773 : Prm := ⟨67, 34, 30, 1775, 11, 18446744073709551616, 108558718789512355, 108559818301140131⟩
noncomputable def L1773_cp1 : Nat × Nat := t7val% (fastRun pL1773 1 1023 (init pL1773) (init pL1773))
theorem L1773_seg1 : segOK pL1773 1 1023 (init pL1773) (init pL1773) L1773_cp1.1 L1773_cp1.2 = true := by
  decide +kernel
noncomputable def L1773_cp2 : Nat × Nat := t7val% (fastRun pL1773 1 1447 (init pL1773) (init pL1773))
theorem L1773_seg2 : segOK pL1773 1024 424 L1773_cp1.1 L1773_cp1.2 L1773_cp2.1 L1773_cp2.2 = true := by
  decide +kernel
theorem L1773_fin : (prmOK pL1773 1773 && ptTest pL1773 (runFrom pL1773 (fmask pL1773) (cmask pL1773) (hmask pL1773) 1448 325 (true, L1773_cp2.1, L1773_cp2.2)) 1773 887 false) = true := by
  decide +kernel
theorem L1773_ok : RunOK pL1773 1773 (runFrom pL1773 (fmask pL1773) (cmask pL1773) (hmask pL1773) 1448 325 (true, L1773_cp2.1, L1773_cp2.2)) ∧ ptTest pL1773 (runFrom pL1773 (fmask pL1773) (cmask pL1773) (hmask pL1773) 1448 325 (true, L1773_cp2.1, L1773_cp2.2)) 1773 887 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1773_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1773_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1773_fin) true) L1773_seg1) L1773_seg2) (by decide) rfl L1773_fin ptTest_fst
noncomputable def H1773_cp1 : Nat × Nat := t7val% (fastRun pH1773 1 1023 (init pH1773) (init pH1773))
theorem H1773_seg1 : segOK pH1773 1 1023 (init pH1773) (init pH1773) H1773_cp1.1 H1773_cp1.2 = true := by
  decide +kernel
noncomputable def H1773_cp2 : Nat × Nat := t7val% (fastRun pH1773 1 1447 (init pH1773) (init pH1773))
theorem H1773_seg2 : segOK pH1773 1024 424 H1773_cp1.1 H1773_cp1.2 H1773_cp2.1 H1773_cp2.2 = true := by
  decide +kernel
theorem H1773_fin : (prmOK pH1773 1773 && ptTest pH1773 (runFrom pH1773 (fmask pH1773) (cmask pH1773) (hmask pH1773) 1448 325 (true, H1773_cp2.1, H1773_cp2.2)) 1773 887 true) = true := by
  decide +kernel
theorem H1773_ok : RunOK pH1773 1773 (runFrom pH1773 (fmask pH1773) (cmask pH1773) (hmask pH1773) 1448 325 (true, H1773_cp2.1, H1773_cp2.2)) ∧ ptTest pH1773 (runFrom pH1773 (fmask pH1773) (cmask pH1773) (hmask pH1773) 1448 325 (true, H1773_cp2.1, H1773_cp2.2)) 1773 887 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1773_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1773_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1773_fin) true) H1773_seg1) H1773_seg2) (by decide) rfl H1773_fin ptTest_fst
noncomputable def I1773_cp1 : Nat × Nat := t7val% (fastRun pI1773 1 1253 (init pI1773) (init pI1773))
theorem I1773_seg1 : segOK pI1773 1 1253 (init pI1773) (init pI1773) I1773_cp1.1 I1773_cp1.2 = true := by
  decide +kernel
theorem I1773_fin : (prmOK pI1773 1773 && intTest pI1773 (runFrom pI1773 (fmask pI1773) (cmask pI1773) (hmask pI1773) 1254 519 (true, I1773_cp1.1, I1773_cp1.2)) 1773 21 false) = true := by
  decide +kernel
theorem I1773_ok : RunOK pI1773 1773 (runFrom pI1773 (fmask pI1773) (cmask pI1773) (hmask pI1773) 1254 519 (true, I1773_cp1.1, I1773_cp1.2)) ∧ intTest pI1773 (runFrom pI1773 (fmask pI1773) (cmask pI1773) (hmask pI1773) 1254 519 (true, I1773_cp1.1, I1773_cp1.2)) 1773 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1773_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1773_fin) true) I1773_seg1) (by decide) rfl I1773_fin intTest_fst
theorem link1773 : linkOK pL1773 pH1773 pI1773 = true := by decide +kernel
theorem cvx1773 : ConvexBetweenHumps 1773 :=
  cvx_of L1773_ok H1773_ok I1773_ok link1773 (by decide)

/-! ### `N = 1774` -/

def pL1774 : Prm := ⟨80, 37, 40, 1776, 11, 18446744073709551616, 108508587134587336, 108508587134587336⟩
def pH1774 : Prm := ⟨80, 37, 40, 1776, 11, 18446744073709551616, 108509686646215112, 108509686646215112⟩
def pI1774 : Prm := ⟨67, 34, 30, 1776, 11, 18446744073709551616, 108508587134587336, 108509686646215112⟩
noncomputable def L1774_cp1 : Nat × Nat := t7val% (fastRun pL1774 1 1023 (init pL1774) (init pL1774))
theorem L1774_seg1 : segOK pL1774 1 1023 (init pL1774) (init pL1774) L1774_cp1.1 L1774_cp1.2 = true := by
  decide +kernel
noncomputable def L1774_cp2 : Nat × Nat := t7val% (fastRun pL1774 1 1447 (init pL1774) (init pL1774))
theorem L1774_seg2 : segOK pL1774 1024 424 L1774_cp1.1 L1774_cp1.2 L1774_cp2.1 L1774_cp2.2 = true := by
  decide +kernel
theorem L1774_fin : (prmOK pL1774 1774 && ptTest pL1774 (runFrom pL1774 (fmask pL1774) (cmask pL1774) (hmask pL1774) 1448 326 (true, L1774_cp2.1, L1774_cp2.2)) 1774 887 false) = true := by
  decide +kernel
theorem L1774_ok : RunOK pL1774 1774 (runFrom pL1774 (fmask pL1774) (cmask pL1774) (hmask pL1774) 1448 326 (true, L1774_cp2.1, L1774_cp2.2)) ∧ ptTest pL1774 (runFrom pL1774 (fmask pL1774) (cmask pL1774) (hmask pL1774) 1448 326 (true, L1774_cp2.1, L1774_cp2.2)) 1774 887 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1774_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1774_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1774_fin) true) L1774_seg1) L1774_seg2) (by decide) rfl L1774_fin ptTest_fst
noncomputable def H1774_cp1 : Nat × Nat := t7val% (fastRun pH1774 1 1023 (init pH1774) (init pH1774))
theorem H1774_seg1 : segOK pH1774 1 1023 (init pH1774) (init pH1774) H1774_cp1.1 H1774_cp1.2 = true := by
  decide +kernel
noncomputable def H1774_cp2 : Nat × Nat := t7val% (fastRun pH1774 1 1447 (init pH1774) (init pH1774))
theorem H1774_seg2 : segOK pH1774 1024 424 H1774_cp1.1 H1774_cp1.2 H1774_cp2.1 H1774_cp2.2 = true := by
  decide +kernel
theorem H1774_fin : (prmOK pH1774 1774 && ptTest pH1774 (runFrom pH1774 (fmask pH1774) (cmask pH1774) (hmask pH1774) 1448 326 (true, H1774_cp2.1, H1774_cp2.2)) 1774 887 true) = true := by
  decide +kernel
theorem H1774_ok : RunOK pH1774 1774 (runFrom pH1774 (fmask pH1774) (cmask pH1774) (hmask pH1774) 1448 326 (true, H1774_cp2.1, H1774_cp2.2)) ∧ ptTest pH1774 (runFrom pH1774 (fmask pH1774) (cmask pH1774) (hmask pH1774) 1448 326 (true, H1774_cp2.1, H1774_cp2.2)) 1774 887 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1774_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1774_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1774_fin) true) H1774_seg1) H1774_seg2) (by decide) rfl H1774_fin ptTest_fst
noncomputable def I1774_cp1 : Nat × Nat := t7val% (fastRun pI1774 1 1253 (init pI1774) (init pI1774))
theorem I1774_seg1 : segOK pI1774 1 1253 (init pI1774) (init pI1774) I1774_cp1.1 I1774_cp1.2 = true := by
  decide +kernel
theorem I1774_fin : (prmOK pI1774 1774 && intTest pI1774 (runFrom pI1774 (fmask pI1774) (cmask pI1774) (hmask pI1774) 1254 520 (true, I1774_cp1.1, I1774_cp1.2)) 1774 21 true) = true := by
  decide +kernel
theorem I1774_ok : RunOK pI1774 1774 (runFrom pI1774 (fmask pI1774) (cmask pI1774) (hmask pI1774) 1254 520 (true, I1774_cp1.1, I1774_cp1.2)) ∧ intTest pI1774 (runFrom pI1774 (fmask pI1774) (cmask pI1774) (hmask pI1774) 1254 520 (true, I1774_cp1.1, I1774_cp1.2)) 1774 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1774_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1774_fin) true) I1774_seg1) (by decide) rfl I1774_fin intTest_fst
theorem link1774 : linkOK pL1774 pH1774 pI1774 = true := by decide +kernel
theorem cvx1774 : ConvexBetweenHumps 1774 :=
  cvx_of L1774_ok H1774_ok I1774_ok link1774 (by decide)
theorem cenlink1774 : cenLinkOK pI1774 1774 = true := by decide +kernel
theorem cen1774 : CenterUniqueMin 1774 ∧ DipHyp 1774 ∧ OnePointHyps 1774 :=
  cen_of L1774_ok H1774_ok I1774_ok link1774 cenlink1774

/-! ### `N = 1775` -/

def pL1775 : Prm := ⟨80, 37, 40, 1777, 11, 18446744073709551616, 108458485627434410, 108458485627434410⟩
def pH1775 : Prm := ⟨80, 37, 40, 1777, 11, 18446744073709551616, 108459585139062186, 108459585139062186⟩
def pI1775 : Prm := ⟨67, 34, 30, 1777, 11, 18446744073709551616, 108458485627434410, 108459585139062186⟩
noncomputable def L1775_cp1 : Nat × Nat := t7val% (fastRun pL1775 1 1024 (init pL1775) (init pL1775))
theorem L1775_seg1 : segOK pL1775 1 1024 (init pL1775) (init pL1775) L1775_cp1.1 L1775_cp1.2 = true := by
  decide +kernel
noncomputable def L1775_cp2 : Nat × Nat := t7val% (fastRun pL1775 1 1448 (init pL1775) (init pL1775))
theorem L1775_seg2 : segOK pL1775 1025 424 L1775_cp1.1 L1775_cp1.2 L1775_cp2.1 L1775_cp2.2 = true := by
  decide +kernel
theorem L1775_fin : (prmOK pL1775 1775 && ptTest pL1775 (runFrom pL1775 (fmask pL1775) (cmask pL1775) (hmask pL1775) 1449 326 (true, L1775_cp2.1, L1775_cp2.2)) 1775 888 false) = true := by
  decide +kernel
theorem L1775_ok : RunOK pL1775 1775 (runFrom pL1775 (fmask pL1775) (cmask pL1775) (hmask pL1775) 1449 326 (true, L1775_cp2.1, L1775_cp2.2)) ∧ ptTest pL1775 (runFrom pL1775 (fmask pL1775) (cmask pL1775) (hmask pL1775) 1449 326 (true, L1775_cp2.1, L1775_cp2.2)) 1775 888 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1775_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1775_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1775_fin) true) L1775_seg1) L1775_seg2) (by decide) rfl L1775_fin ptTest_fst
noncomputable def H1775_cp1 : Nat × Nat := t7val% (fastRun pH1775 1 1024 (init pH1775) (init pH1775))
theorem H1775_seg1 : segOK pH1775 1 1024 (init pH1775) (init pH1775) H1775_cp1.1 H1775_cp1.2 = true := by
  decide +kernel
noncomputable def H1775_cp2 : Nat × Nat := t7val% (fastRun pH1775 1 1448 (init pH1775) (init pH1775))
theorem H1775_seg2 : segOK pH1775 1025 424 H1775_cp1.1 H1775_cp1.2 H1775_cp2.1 H1775_cp2.2 = true := by
  decide +kernel
theorem H1775_fin : (prmOK pH1775 1775 && ptTest pH1775 (runFrom pH1775 (fmask pH1775) (cmask pH1775) (hmask pH1775) 1449 326 (true, H1775_cp2.1, H1775_cp2.2)) 1775 888 true) = true := by
  decide +kernel
theorem H1775_ok : RunOK pH1775 1775 (runFrom pH1775 (fmask pH1775) (cmask pH1775) (hmask pH1775) 1449 326 (true, H1775_cp2.1, H1775_cp2.2)) ∧ ptTest pH1775 (runFrom pH1775 (fmask pH1775) (cmask pH1775) (hmask pH1775) 1449 326 (true, H1775_cp2.1, H1775_cp2.2)) 1775 888 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1775_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1775_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1775_fin) true) H1775_seg1) H1775_seg2) (by decide) rfl H1775_fin ptTest_fst
noncomputable def I1775_cp1 : Nat × Nat := t7val% (fastRun pI1775 1 1254 (init pI1775) (init pI1775))
theorem I1775_seg1 : segOK pI1775 1 1254 (init pI1775) (init pI1775) I1775_cp1.1 I1775_cp1.2 = true := by
  decide +kernel
theorem I1775_fin : (prmOK pI1775 1775 && intTest pI1775 (runFrom pI1775 (fmask pI1775) (cmask pI1775) (hmask pI1775) 1255 520 (true, I1775_cp1.1, I1775_cp1.2)) 1775 21 false) = true := by
  decide +kernel
theorem I1775_ok : RunOK pI1775 1775 (runFrom pI1775 (fmask pI1775) (cmask pI1775) (hmask pI1775) 1255 520 (true, I1775_cp1.1, I1775_cp1.2)) ∧ intTest pI1775 (runFrom pI1775 (fmask pI1775) (cmask pI1775) (hmask pI1775) 1255 520 (true, I1775_cp1.1, I1775_cp1.2)) 1775 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1775_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1775_fin) true) I1775_seg1) (by decide) rfl I1775_fin intTest_fst
theorem link1775 : linkOK pL1775 pH1775 pI1775 = true := by decide +kernel
theorem cvx1775 : ConvexBetweenHumps 1775 :=
  cvx_of L1775_ok H1775_ok I1775_ok link1775 (by decide)

/-! ### `N = 1776` -/

def pL1776 : Prm := ⟨80, 37, 40, 1778, 11, 18446744073709551616, 108408454388449113, 108408454388449113⟩
def pH1776 : Prm := ⟨80, 37, 40, 1778, 11, 18446744073709551616, 108409553900076889, 108409553900076889⟩
def pI1776 : Prm := ⟨67, 34, 30, 1778, 11, 18446744073709551616, 108408454388449113, 108409553900076889⟩
noncomputable def L1776_cp1 : Nat × Nat := t7val% (fastRun pL1776 1 1024 (init pL1776) (init pL1776))
theorem L1776_seg1 : segOK pL1776 1 1024 (init pL1776) (init pL1776) L1776_cp1.1 L1776_cp1.2 = true := by
  decide +kernel
noncomputable def L1776_cp2 : Nat × Nat := t7val% (fastRun pL1776 1 1449 (init pL1776) (init pL1776))
theorem L1776_seg2 : segOK pL1776 1025 425 L1776_cp1.1 L1776_cp1.2 L1776_cp2.1 L1776_cp2.2 = true := by
  decide +kernel
theorem L1776_fin : (prmOK pL1776 1776 && ptTest pL1776 (runFrom pL1776 (fmask pL1776) (cmask pL1776) (hmask pL1776) 1450 326 (true, L1776_cp2.1, L1776_cp2.2)) 1776 888 false) = true := by
  decide +kernel
theorem L1776_ok : RunOK pL1776 1776 (runFrom pL1776 (fmask pL1776) (cmask pL1776) (hmask pL1776) 1450 326 (true, L1776_cp2.1, L1776_cp2.2)) ∧ ptTest pL1776 (runFrom pL1776 (fmask pL1776) (cmask pL1776) (hmask pL1776) 1450 326 (true, L1776_cp2.1, L1776_cp2.2)) 1776 888 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1776_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1776_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1776_fin) true) L1776_seg1) L1776_seg2) (by decide) rfl L1776_fin ptTest_fst
noncomputable def H1776_cp1 : Nat × Nat := t7val% (fastRun pH1776 1 1024 (init pH1776) (init pH1776))
theorem H1776_seg1 : segOK pH1776 1 1024 (init pH1776) (init pH1776) H1776_cp1.1 H1776_cp1.2 = true := by
  decide +kernel
noncomputable def H1776_cp2 : Nat × Nat := t7val% (fastRun pH1776 1 1449 (init pH1776) (init pH1776))
theorem H1776_seg2 : segOK pH1776 1025 425 H1776_cp1.1 H1776_cp1.2 H1776_cp2.1 H1776_cp2.2 = true := by
  decide +kernel
theorem H1776_fin : (prmOK pH1776 1776 && ptTest pH1776 (runFrom pH1776 (fmask pH1776) (cmask pH1776) (hmask pH1776) 1450 326 (true, H1776_cp2.1, H1776_cp2.2)) 1776 888 true) = true := by
  decide +kernel
theorem H1776_ok : RunOK pH1776 1776 (runFrom pH1776 (fmask pH1776) (cmask pH1776) (hmask pH1776) 1450 326 (true, H1776_cp2.1, H1776_cp2.2)) ∧ ptTest pH1776 (runFrom pH1776 (fmask pH1776) (cmask pH1776) (hmask pH1776) 1450 326 (true, H1776_cp2.1, H1776_cp2.2)) 1776 888 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1776_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1776_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1776_fin) true) H1776_seg1) H1776_seg2) (by decide) rfl H1776_fin ptTest_fst
noncomputable def I1776_cp1 : Nat × Nat := t7val% (fastRun pI1776 1 1255 (init pI1776) (init pI1776))
theorem I1776_seg1 : segOK pI1776 1 1255 (init pI1776) (init pI1776) I1776_cp1.1 I1776_cp1.2 = true := by
  decide +kernel
theorem I1776_fin : (prmOK pI1776 1776 && intTest pI1776 (runFrom pI1776 (fmask pI1776) (cmask pI1776) (hmask pI1776) 1256 520 (true, I1776_cp1.1, I1776_cp1.2)) 1776 21 true) = true := by
  decide +kernel
theorem I1776_ok : RunOK pI1776 1776 (runFrom pI1776 (fmask pI1776) (cmask pI1776) (hmask pI1776) 1256 520 (true, I1776_cp1.1, I1776_cp1.2)) ∧ intTest pI1776 (runFrom pI1776 (fmask pI1776) (cmask pI1776) (hmask pI1776) 1256 520 (true, I1776_cp1.1, I1776_cp1.2)) 1776 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1776_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1776_fin) true) I1776_seg1) (by decide) rfl I1776_fin intTest_fst
theorem link1776 : linkOK pL1776 pH1776 pI1776 = true := by decide +kernel
theorem cvx1776 : ConvexBetweenHumps 1776 :=
  cvx_of L1776_ok H1776_ok I1776_ok link1776 (by decide)
theorem cenlink1776 : cenLinkOK pI1776 1776 = true := by decide +kernel
theorem cen1776 : CenterUniqueMin 1776 ∧ DipHyp 1776 ∧ OnePointHyps 1776 :=
  cen_of L1776_ok H1776_ok I1776_ok link1776 cenlink1776

/-! ### `N = 1777` -/

def pL1777 : Prm := ⟨80, 37, 40, 1779, 11, 18446744073709551616, 108358453210554660, 108358453210554660⟩
def pH1777 : Prm := ⟨80, 37, 40, 1779, 11, 18446744073709551616, 108359552722182436, 108359552722182436⟩
def pI1777 : Prm := ⟨67, 34, 30, 1779, 11, 18446744073709551616, 108358453210554660, 108359552722182436⟩
noncomputable def L1777_cp1 : Nat × Nat := t7val% (fastRun pL1777 1 1025 (init pL1777) (init pL1777))
theorem L1777_seg1 : segOK pL1777 1 1025 (init pL1777) (init pL1777) L1777_cp1.1 L1777_cp1.2 = true := by
  decide +kernel
noncomputable def L1777_cp2 : Nat × Nat := t7val% (fastRun pL1777 1 1450 (init pL1777) (init pL1777))
theorem L1777_seg2 : segOK pL1777 1026 425 L1777_cp1.1 L1777_cp1.2 L1777_cp2.1 L1777_cp2.2 = true := by
  decide +kernel
theorem L1777_fin : (prmOK pL1777 1777 && ptTest pL1777 (runFrom pL1777 (fmask pL1777) (cmask pL1777) (hmask pL1777) 1451 326 (true, L1777_cp2.1, L1777_cp2.2)) 1777 889 false) = true := by
  decide +kernel
theorem L1777_ok : RunOK pL1777 1777 (runFrom pL1777 (fmask pL1777) (cmask pL1777) (hmask pL1777) 1451 326 (true, L1777_cp2.1, L1777_cp2.2)) ∧ ptTest pL1777 (runFrom pL1777 (fmask pL1777) (cmask pL1777) (hmask pL1777) 1451 326 (true, L1777_cp2.1, L1777_cp2.2)) 1777 889 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1777_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1777_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1777_fin) true) L1777_seg1) L1777_seg2) (by decide) rfl L1777_fin ptTest_fst
noncomputable def H1777_cp1 : Nat × Nat := t7val% (fastRun pH1777 1 1025 (init pH1777) (init pH1777))
theorem H1777_seg1 : segOK pH1777 1 1025 (init pH1777) (init pH1777) H1777_cp1.1 H1777_cp1.2 = true := by
  decide +kernel
noncomputable def H1777_cp2 : Nat × Nat := t7val% (fastRun pH1777 1 1450 (init pH1777) (init pH1777))
theorem H1777_seg2 : segOK pH1777 1026 425 H1777_cp1.1 H1777_cp1.2 H1777_cp2.1 H1777_cp2.2 = true := by
  decide +kernel
theorem H1777_fin : (prmOK pH1777 1777 && ptTest pH1777 (runFrom pH1777 (fmask pH1777) (cmask pH1777) (hmask pH1777) 1451 326 (true, H1777_cp2.1, H1777_cp2.2)) 1777 889 true) = true := by
  decide +kernel
theorem H1777_ok : RunOK pH1777 1777 (runFrom pH1777 (fmask pH1777) (cmask pH1777) (hmask pH1777) 1451 326 (true, H1777_cp2.1, H1777_cp2.2)) ∧ ptTest pH1777 (runFrom pH1777 (fmask pH1777) (cmask pH1777) (hmask pH1777) 1451 326 (true, H1777_cp2.1, H1777_cp2.2)) 1777 889 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1777_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1777_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1777_fin) true) H1777_seg1) H1777_seg2) (by decide) rfl H1777_fin ptTest_fst
noncomputable def I1777_cp1 : Nat × Nat := t7val% (fastRun pI1777 1 1256 (init pI1777) (init pI1777))
theorem I1777_seg1 : segOK pI1777 1 1256 (init pI1777) (init pI1777) I1777_cp1.1 I1777_cp1.2 = true := by
  decide +kernel
theorem I1777_fin : (prmOK pI1777 1777 && intTest pI1777 (runFrom pI1777 (fmask pI1777) (cmask pI1777) (hmask pI1777) 1257 520 (true, I1777_cp1.1, I1777_cp1.2)) 1777 21 false) = true := by
  decide +kernel
theorem I1777_ok : RunOK pI1777 1777 (runFrom pI1777 (fmask pI1777) (cmask pI1777) (hmask pI1777) 1257 520 (true, I1777_cp1.1, I1777_cp1.2)) ∧ intTest pI1777 (runFrom pI1777 (fmask pI1777) (cmask pI1777) (hmask pI1777) 1257 520 (true, I1777_cp1.1, I1777_cp1.2)) 1777 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1777_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1777_fin) true) I1777_seg1) (by decide) rfl I1777_fin intTest_fst
theorem link1777 : linkOK pL1777 pH1777 pI1777 = true := by decide +kernel
theorem cvx1777 : ConvexBetweenHumps 1777 :=
  cvx_of L1777_ok H1777_ok I1777_ok link1777 (by decide)

/-! ### `N = 1778` -/

def pL1778 : Prm := ⟨80, 37, 40, 1780, 11, 18446744073709551616, 108308522076773683, 108308522076773683⟩
def pH1778 : Prm := ⟨80, 37, 40, 1780, 11, 18446744073709551616, 108309621588401459, 108309621588401459⟩
def pI1778 : Prm := ⟨67, 34, 30, 1780, 11, 18446744073709551616, 108308522076773683, 108309621588401459⟩
noncomputable def L1778_cp1 : Nat × Nat := t7val% (fastRun pL1778 1 1026 (init pL1778) (init pL1778))
theorem L1778_seg1 : segOK pL1778 1 1026 (init pL1778) (init pL1778) L1778_cp1.1 L1778_cp1.2 = true := by
  decide +kernel
noncomputable def L1778_cp2 : Nat × Nat := t7val% (fastRun pL1778 1 1451 (init pL1778) (init pL1778))
theorem L1778_seg2 : segOK pL1778 1027 425 L1778_cp1.1 L1778_cp1.2 L1778_cp2.1 L1778_cp2.2 = true := by
  decide +kernel
theorem L1778_fin : (prmOK pL1778 1778 && ptTest pL1778 (runFrom pL1778 (fmask pL1778) (cmask pL1778) (hmask pL1778) 1452 326 (true, L1778_cp2.1, L1778_cp2.2)) 1778 889 false) = true := by
  decide +kernel
theorem L1778_ok : RunOK pL1778 1778 (runFrom pL1778 (fmask pL1778) (cmask pL1778) (hmask pL1778) 1452 326 (true, L1778_cp2.1, L1778_cp2.2)) ∧ ptTest pL1778 (runFrom pL1778 (fmask pL1778) (cmask pL1778) (hmask pL1778) 1452 326 (true, L1778_cp2.1, L1778_cp2.2)) 1778 889 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1778_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1778_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1778_fin) true) L1778_seg1) L1778_seg2) (by decide) rfl L1778_fin ptTest_fst
noncomputable def H1778_cp1 : Nat × Nat := t7val% (fastRun pH1778 1 1026 (init pH1778) (init pH1778))
theorem H1778_seg1 : segOK pH1778 1 1026 (init pH1778) (init pH1778) H1778_cp1.1 H1778_cp1.2 = true := by
  decide +kernel
noncomputable def H1778_cp2 : Nat × Nat := t7val% (fastRun pH1778 1 1451 (init pH1778) (init pH1778))
theorem H1778_seg2 : segOK pH1778 1027 425 H1778_cp1.1 H1778_cp1.2 H1778_cp2.1 H1778_cp2.2 = true := by
  decide +kernel
theorem H1778_fin : (prmOK pH1778 1778 && ptTest pH1778 (runFrom pH1778 (fmask pH1778) (cmask pH1778) (hmask pH1778) 1452 326 (true, H1778_cp2.1, H1778_cp2.2)) 1778 889 true) = true := by
  decide +kernel
theorem H1778_ok : RunOK pH1778 1778 (runFrom pH1778 (fmask pH1778) (cmask pH1778) (hmask pH1778) 1452 326 (true, H1778_cp2.1, H1778_cp2.2)) ∧ ptTest pH1778 (runFrom pH1778 (fmask pH1778) (cmask pH1778) (hmask pH1778) 1452 326 (true, H1778_cp2.1, H1778_cp2.2)) 1778 889 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1778_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1778_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1778_fin) true) H1778_seg1) H1778_seg2) (by decide) rfl H1778_fin ptTest_fst
noncomputable def I1778_cp1 : Nat × Nat := t7val% (fastRun pI1778 1 1256 (init pI1778) (init pI1778))
theorem I1778_seg1 : segOK pI1778 1 1256 (init pI1778) (init pI1778) I1778_cp1.1 I1778_cp1.2 = true := by
  decide +kernel
theorem I1778_fin : (prmOK pI1778 1778 && intTest pI1778 (runFrom pI1778 (fmask pI1778) (cmask pI1778) (hmask pI1778) 1257 521 (true, I1778_cp1.1, I1778_cp1.2)) 1778 21 true) = true := by
  decide +kernel
theorem I1778_ok : RunOK pI1778 1778 (runFrom pI1778 (fmask pI1778) (cmask pI1778) (hmask pI1778) 1257 521 (true, I1778_cp1.1, I1778_cp1.2)) ∧ intTest pI1778 (runFrom pI1778 (fmask pI1778) (cmask pI1778) (hmask pI1778) 1257 521 (true, I1778_cp1.1, I1778_cp1.2)) 1778 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1778_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1778_fin) true) I1778_seg1) (by decide) rfl I1778_fin intTest_fst
theorem link1778 : linkOK pL1778 pH1778 pI1778 = true := by decide +kernel
theorem cvx1778 : ConvexBetweenHumps 1778 :=
  cvx_of L1778_ok H1778_ok I1778_ok link1778 (by decide)
theorem cenlink1778 : cenLinkOK pI1778 1778 = true := by decide +kernel
theorem cen1778 : CenterUniqueMin 1778 ∧ DipHyp 1778 ∧ OnePointHyps 1778 :=
  cen_of L1778_ok H1778_ok I1778_ok link1778 cenlink1778

/-! ### `N = 1779` -/

def pL1779 : Prm := ⟨80, 37, 40, 1781, 11, 18446744073709551616, 108258620917734341, 108258620917734341⟩
def pH1779 : Prm := ⟨80, 37, 40, 1781, 11, 18446744073709551616, 108259720429362117, 108259720429362117⟩
def pI1779 : Prm := ⟨67, 34, 30, 1781, 11, 18446744073709551616, 108258620917734341, 108259720429362117⟩
noncomputable def L1779_cp1 : Nat × Nat := t7val% (fastRun pL1779 1 1026 (init pL1779) (init pL1779))
theorem L1779_seg1 : segOK pL1779 1 1026 (init pL1779) (init pL1779) L1779_cp1.1 L1779_cp1.2 = true := by
  decide +kernel
noncomputable def L1779_cp2 : Nat × Nat := t7val% (fastRun pL1779 1 1452 (init pL1779) (init pL1779))
theorem L1779_seg2 : segOK pL1779 1027 426 L1779_cp1.1 L1779_cp1.2 L1779_cp2.1 L1779_cp2.2 = true := by
  decide +kernel
theorem L1779_fin : (prmOK pL1779 1779 && ptTest pL1779 (runFrom pL1779 (fmask pL1779) (cmask pL1779) (hmask pL1779) 1453 326 (true, L1779_cp2.1, L1779_cp2.2)) 1779 890 false) = true := by
  decide +kernel
theorem L1779_ok : RunOK pL1779 1779 (runFrom pL1779 (fmask pL1779) (cmask pL1779) (hmask pL1779) 1453 326 (true, L1779_cp2.1, L1779_cp2.2)) ∧ ptTest pL1779 (runFrom pL1779 (fmask pL1779) (cmask pL1779) (hmask pL1779) 1453 326 (true, L1779_cp2.1, L1779_cp2.2)) 1779 890 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1779_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1779_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1779_fin) true) L1779_seg1) L1779_seg2) (by decide) rfl L1779_fin ptTest_fst
noncomputable def H1779_cp1 : Nat × Nat := t7val% (fastRun pH1779 1 1026 (init pH1779) (init pH1779))
theorem H1779_seg1 : segOK pH1779 1 1026 (init pH1779) (init pH1779) H1779_cp1.1 H1779_cp1.2 = true := by
  decide +kernel
noncomputable def H1779_cp2 : Nat × Nat := t7val% (fastRun pH1779 1 1452 (init pH1779) (init pH1779))
theorem H1779_seg2 : segOK pH1779 1027 426 H1779_cp1.1 H1779_cp1.2 H1779_cp2.1 H1779_cp2.2 = true := by
  decide +kernel
theorem H1779_fin : (prmOK pH1779 1779 && ptTest pH1779 (runFrom pH1779 (fmask pH1779) (cmask pH1779) (hmask pH1779) 1453 326 (true, H1779_cp2.1, H1779_cp2.2)) 1779 890 true) = true := by
  decide +kernel
theorem H1779_ok : RunOK pH1779 1779 (runFrom pH1779 (fmask pH1779) (cmask pH1779) (hmask pH1779) 1453 326 (true, H1779_cp2.1, H1779_cp2.2)) ∧ ptTest pH1779 (runFrom pH1779 (fmask pH1779) (cmask pH1779) (hmask pH1779) 1453 326 (true, H1779_cp2.1, H1779_cp2.2)) 1779 890 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1779_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1779_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1779_fin) true) H1779_seg1) H1779_seg2) (by decide) rfl H1779_fin ptTest_fst
noncomputable def I1779_cp1 : Nat × Nat := t7val% (fastRun pI1779 1 1257 (init pI1779) (init pI1779))
theorem I1779_seg1 : segOK pI1779 1 1257 (init pI1779) (init pI1779) I1779_cp1.1 I1779_cp1.2 = true := by
  decide +kernel
theorem I1779_fin : (prmOK pI1779 1779 && intTest pI1779 (runFrom pI1779 (fmask pI1779) (cmask pI1779) (hmask pI1779) 1258 521 (true, I1779_cp1.1, I1779_cp1.2)) 1779 21 false) = true := by
  decide +kernel
theorem I1779_ok : RunOK pI1779 1779 (runFrom pI1779 (fmask pI1779) (cmask pI1779) (hmask pI1779) 1258 521 (true, I1779_cp1.1, I1779_cp1.2)) ∧ intTest pI1779 (runFrom pI1779 (fmask pI1779) (cmask pI1779) (hmask pI1779) 1258 521 (true, I1779_cp1.1, I1779_cp1.2)) 1779 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1779_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1779_fin) true) I1779_seg1) (by decide) rfl I1779_fin intTest_fst
theorem link1779 : linkOK pL1779 pH1779 pI1779 = true := by decide +kernel
theorem cvx1779 : ConvexBetweenHumps 1779 :=
  cvx_of L1779_ok H1779_ok I1779_ok link1779 (by decide)

/-! ### `N = 1780` -/

def pL1780 : Prm := ⟨80, 37, 40, 1782, 11, 18446744073709551616, 108208789579731997, 108208789579731997⟩
def pH1780 : Prm := ⟨80, 37, 40, 1782, 11, 18446744073709551616, 108209889091359773, 108209889091359773⟩
def pI1780 : Prm := ⟨67, 34, 30, 1782, 11, 18446744073709551616, 108208789579731997, 108209889091359773⟩
noncomputable def L1780_cp1 : Nat × Nat := t7val% (fastRun pL1780 1 1027 (init pL1780) (init pL1780))
theorem L1780_seg1 : segOK pL1780 1 1027 (init pL1780) (init pL1780) L1780_cp1.1 L1780_cp1.2 = true := by
  decide +kernel
noncomputable def L1780_cp2 : Nat × Nat := t7val% (fastRun pL1780 1 1452 (init pL1780) (init pL1780))
theorem L1780_seg2 : segOK pL1780 1028 425 L1780_cp1.1 L1780_cp1.2 L1780_cp2.1 L1780_cp2.2 = true := by
  decide +kernel
theorem L1780_fin : (prmOK pL1780 1780 && ptTest pL1780 (runFrom pL1780 (fmask pL1780) (cmask pL1780) (hmask pL1780) 1453 327 (true, L1780_cp2.1, L1780_cp2.2)) 1780 890 false) = true := by
  decide +kernel
theorem L1780_ok : RunOK pL1780 1780 (runFrom pL1780 (fmask pL1780) (cmask pL1780) (hmask pL1780) 1453 327 (true, L1780_cp2.1, L1780_cp2.2)) ∧ ptTest pL1780 (runFrom pL1780 (fmask pL1780) (cmask pL1780) (hmask pL1780) 1453 327 (true, L1780_cp2.1, L1780_cp2.2)) 1780 890 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1780_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1780_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1780_fin) true) L1780_seg1) L1780_seg2) (by decide) rfl L1780_fin ptTest_fst
noncomputable def H1780_cp1 : Nat × Nat := t7val% (fastRun pH1780 1 1027 (init pH1780) (init pH1780))
theorem H1780_seg1 : segOK pH1780 1 1027 (init pH1780) (init pH1780) H1780_cp1.1 H1780_cp1.2 = true := by
  decide +kernel
noncomputable def H1780_cp2 : Nat × Nat := t7val% (fastRun pH1780 1 1452 (init pH1780) (init pH1780))
theorem H1780_seg2 : segOK pH1780 1028 425 H1780_cp1.1 H1780_cp1.2 H1780_cp2.1 H1780_cp2.2 = true := by
  decide +kernel
theorem H1780_fin : (prmOK pH1780 1780 && ptTest pH1780 (runFrom pH1780 (fmask pH1780) (cmask pH1780) (hmask pH1780) 1453 327 (true, H1780_cp2.1, H1780_cp2.2)) 1780 890 true) = true := by
  decide +kernel
theorem H1780_ok : RunOK pH1780 1780 (runFrom pH1780 (fmask pH1780) (cmask pH1780) (hmask pH1780) 1453 327 (true, H1780_cp2.1, H1780_cp2.2)) ∧ ptTest pH1780 (runFrom pH1780 (fmask pH1780) (cmask pH1780) (hmask pH1780) 1453 327 (true, H1780_cp2.1, H1780_cp2.2)) 1780 890 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1780_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1780_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1780_fin) true) H1780_seg1) H1780_seg2) (by decide) rfl H1780_fin ptTest_fst
noncomputable def I1780_cp1 : Nat × Nat := t7val% (fastRun pI1780 1 1258 (init pI1780) (init pI1780))
theorem I1780_seg1 : segOK pI1780 1 1258 (init pI1780) (init pI1780) I1780_cp1.1 I1780_cp1.2 = true := by
  decide +kernel
theorem I1780_fin : (prmOK pI1780 1780 && intTest pI1780 (runFrom pI1780 (fmask pI1780) (cmask pI1780) (hmask pI1780) 1259 521 (true, I1780_cp1.1, I1780_cp1.2)) 1780 21 true) = true := by
  decide +kernel
theorem I1780_ok : RunOK pI1780 1780 (runFrom pI1780 (fmask pI1780) (cmask pI1780) (hmask pI1780) 1259 521 (true, I1780_cp1.1, I1780_cp1.2)) ∧ intTest pI1780 (runFrom pI1780 (fmask pI1780) (cmask pI1780) (hmask pI1780) 1259 521 (true, I1780_cp1.1, I1780_cp1.2)) 1780 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1780_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1780_fin) true) I1780_seg1) (by decide) rfl I1780_fin intTest_fst
theorem link1780 : linkOK pL1780 pH1780 pI1780 = true := by decide +kernel
theorem cvx1780 : ConvexBetweenHumps 1780 :=
  cvx_of L1780_ok H1780_ok I1780_ok link1780 (by decide)
theorem cenlink1780 : cenLinkOK pI1780 1780 = true := by decide +kernel
theorem cen1780 : CenterUniqueMin 1780 ∧ DipHyp 1780 ∧ OnePointHyps 1780 :=
  cen_of L1780_ok H1780_ok I1780_ok link1780 cenlink1780

/-! ### `N = 1781` -/

def pL1781 : Prm := ⟨80, 37, 40, 1783, 11, 18446744073709551616, 108158988130454121, 108158988130454121⟩
def pH1781 : Prm := ⟨80, 37, 40, 1783, 11, 18446744073709551616, 108160087642081897, 108160087642081897⟩
def pI1781 : Prm := ⟨67, 34, 30, 1783, 11, 18446744073709551616, 108158988130454121, 108160087642081897⟩
noncomputable def L1781_cp1 : Nat × Nat := t7val% (fastRun pL1781 1 1027 (init pL1781) (init pL1781))
theorem L1781_seg1 : segOK pL1781 1 1027 (init pL1781) (init pL1781) L1781_cp1.1 L1781_cp1.2 = true := by
  decide +kernel
noncomputable def L1781_cp2 : Nat × Nat := t7val% (fastRun pL1781 1 1453 (init pL1781) (init pL1781))
theorem L1781_seg2 : segOK pL1781 1028 426 L1781_cp1.1 L1781_cp1.2 L1781_cp2.1 L1781_cp2.2 = true := by
  decide +kernel
theorem L1781_fin : (prmOK pL1781 1781 && ptTest pL1781 (runFrom pL1781 (fmask pL1781) (cmask pL1781) (hmask pL1781) 1454 327 (true, L1781_cp2.1, L1781_cp2.2)) 1781 891 false) = true := by
  decide +kernel
theorem L1781_ok : RunOK pL1781 1781 (runFrom pL1781 (fmask pL1781) (cmask pL1781) (hmask pL1781) 1454 327 (true, L1781_cp2.1, L1781_cp2.2)) ∧ ptTest pL1781 (runFrom pL1781 (fmask pL1781) (cmask pL1781) (hmask pL1781) 1454 327 (true, L1781_cp2.1, L1781_cp2.2)) 1781 891 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1781_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1781_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1781_fin) true) L1781_seg1) L1781_seg2) (by decide) rfl L1781_fin ptTest_fst
noncomputable def H1781_cp1 : Nat × Nat := t7val% (fastRun pH1781 1 1027 (init pH1781) (init pH1781))
theorem H1781_seg1 : segOK pH1781 1 1027 (init pH1781) (init pH1781) H1781_cp1.1 H1781_cp1.2 = true := by
  decide +kernel
noncomputable def H1781_cp2 : Nat × Nat := t7val% (fastRun pH1781 1 1453 (init pH1781) (init pH1781))
theorem H1781_seg2 : segOK pH1781 1028 426 H1781_cp1.1 H1781_cp1.2 H1781_cp2.1 H1781_cp2.2 = true := by
  decide +kernel
theorem H1781_fin : (prmOK pH1781 1781 && ptTest pH1781 (runFrom pH1781 (fmask pH1781) (cmask pH1781) (hmask pH1781) 1454 327 (true, H1781_cp2.1, H1781_cp2.2)) 1781 891 true) = true := by
  decide +kernel
theorem H1781_ok : RunOK pH1781 1781 (runFrom pH1781 (fmask pH1781) (cmask pH1781) (hmask pH1781) 1454 327 (true, H1781_cp2.1, H1781_cp2.2)) ∧ ptTest pH1781 (runFrom pH1781 (fmask pH1781) (cmask pH1781) (hmask pH1781) 1454 327 (true, H1781_cp2.1, H1781_cp2.2)) 1781 891 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1781_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1781_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1781_fin) true) H1781_seg1) H1781_seg2) (by decide) rfl H1781_fin ptTest_fst
noncomputable def I1781_cp1 : Nat × Nat := t7val% (fastRun pI1781 1 1258 (init pI1781) (init pI1781))
theorem I1781_seg1 : segOK pI1781 1 1258 (init pI1781) (init pI1781) I1781_cp1.1 I1781_cp1.2 = true := by
  decide +kernel
theorem I1781_fin : (prmOK pI1781 1781 && intTest pI1781 (runFrom pI1781 (fmask pI1781) (cmask pI1781) (hmask pI1781) 1259 522 (true, I1781_cp1.1, I1781_cp1.2)) 1781 21 false) = true := by
  decide +kernel
theorem I1781_ok : RunOK pI1781 1781 (runFrom pI1781 (fmask pI1781) (cmask pI1781) (hmask pI1781) 1259 522 (true, I1781_cp1.1, I1781_cp1.2)) ∧ intTest pI1781 (runFrom pI1781 (fmask pI1781) (cmask pI1781) (hmask pI1781) 1259 522 (true, I1781_cp1.1, I1781_cp1.2)) 1781 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1781_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1781_fin) true) I1781_seg1) (by decide) rfl I1781_fin intTest_fst
theorem link1781 : linkOK pL1781 pH1781 pI1781 = true := by decide +kernel
theorem cvx1781 : ConvexBetweenHumps 1781 :=
  cvx_of L1781_ok H1781_ok I1781_ok link1781 (by decide)

/-! ### `N = 1782` -/

def pL1782 : Prm := ⟨80, 37, 40, 1784, 11, 18446744073709551616, 108109256280114446, 108109256280114446⟩
def pH1782 : Prm := ⟨80, 37, 40, 1784, 11, 18446744073709551616, 108110355791742222, 108110355791742222⟩
def pI1782 : Prm := ⟨67, 34, 30, 1784, 11, 18446744073709551616, 108109256280114446, 108110355791742222⟩
noncomputable def L1782_cp1 : Nat × Nat := t7val% (fastRun pL1782 1 1028 (init pL1782) (init pL1782))
theorem L1782_seg1 : segOK pL1782 1 1028 (init pL1782) (init pL1782) L1782_cp1.1 L1782_cp1.2 = true := by
  decide +kernel
noncomputable def L1782_cp2 : Nat × Nat := t7val% (fastRun pL1782 1 1454 (init pL1782) (init pL1782))
theorem L1782_seg2 : segOK pL1782 1029 426 L1782_cp1.1 L1782_cp1.2 L1782_cp2.1 L1782_cp2.2 = true := by
  decide +kernel
theorem L1782_fin : (prmOK pL1782 1782 && ptTest pL1782 (runFrom pL1782 (fmask pL1782) (cmask pL1782) (hmask pL1782) 1455 327 (true, L1782_cp2.1, L1782_cp2.2)) 1782 891 false) = true := by
  decide +kernel
theorem L1782_ok : RunOK pL1782 1782 (runFrom pL1782 (fmask pL1782) (cmask pL1782) (hmask pL1782) 1455 327 (true, L1782_cp2.1, L1782_cp2.2)) ∧ ptTest pL1782 (runFrom pL1782 (fmask pL1782) (cmask pL1782) (hmask pL1782) 1455 327 (true, L1782_cp2.1, L1782_cp2.2)) 1782 891 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1782_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1782_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1782_fin) true) L1782_seg1) L1782_seg2) (by decide) rfl L1782_fin ptTest_fst
noncomputable def H1782_cp1 : Nat × Nat := t7val% (fastRun pH1782 1 1028 (init pH1782) (init pH1782))
theorem H1782_seg1 : segOK pH1782 1 1028 (init pH1782) (init pH1782) H1782_cp1.1 H1782_cp1.2 = true := by
  decide +kernel
noncomputable def H1782_cp2 : Nat × Nat := t7val% (fastRun pH1782 1 1454 (init pH1782) (init pH1782))
theorem H1782_seg2 : segOK pH1782 1029 426 H1782_cp1.1 H1782_cp1.2 H1782_cp2.1 H1782_cp2.2 = true := by
  decide +kernel
theorem H1782_fin : (prmOK pH1782 1782 && ptTest pH1782 (runFrom pH1782 (fmask pH1782) (cmask pH1782) (hmask pH1782) 1455 327 (true, H1782_cp2.1, H1782_cp2.2)) 1782 891 true) = true := by
  decide +kernel
theorem H1782_ok : RunOK pH1782 1782 (runFrom pH1782 (fmask pH1782) (cmask pH1782) (hmask pH1782) 1455 327 (true, H1782_cp2.1, H1782_cp2.2)) ∧ ptTest pH1782 (runFrom pH1782 (fmask pH1782) (cmask pH1782) (hmask pH1782) 1455 327 (true, H1782_cp2.1, H1782_cp2.2)) 1782 891 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1782_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1782_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1782_fin) true) H1782_seg1) H1782_seg2) (by decide) rfl H1782_fin ptTest_fst
noncomputable def I1782_cp1 : Nat × Nat := t7val% (fastRun pI1782 1 1259 (init pI1782) (init pI1782))
theorem I1782_seg1 : segOK pI1782 1 1259 (init pI1782) (init pI1782) I1782_cp1.1 I1782_cp1.2 = true := by
  decide +kernel
theorem I1782_fin : (prmOK pI1782 1782 && intTest pI1782 (runFrom pI1782 (fmask pI1782) (cmask pI1782) (hmask pI1782) 1260 522 (true, I1782_cp1.1, I1782_cp1.2)) 1782 21 true) = true := by
  decide +kernel
theorem I1782_ok : RunOK pI1782 1782 (runFrom pI1782 (fmask pI1782) (cmask pI1782) (hmask pI1782) 1260 522 (true, I1782_cp1.1, I1782_cp1.2)) ∧ intTest pI1782 (runFrom pI1782 (fmask pI1782) (cmask pI1782) (hmask pI1782) 1260 522 (true, I1782_cp1.1, I1782_cp1.2)) 1782 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1782_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1782_fin) true) I1782_seg1) (by decide) rfl I1782_fin intTest_fst
theorem link1782 : linkOK pL1782 pH1782 pI1782 = true := by decide +kernel
theorem cvx1782 : ConvexBetweenHumps 1782 :=
  cvx_of L1782_ok H1782_ok I1782_ok link1782 (by decide)
theorem cenlink1782 : cenLinkOK pI1782 1782 = true := by decide +kernel
theorem cen1782 : CenterUniqueMin 1782 ∧ DipHyp 1782 ∧ OnePointHyps 1782 :=
  cen_of L1782_ok H1782_ok I1782_ok link1782 cenlink1782

/-! ### `N = 1783` -/

def pL1783 : Prm := ⟨80, 37, 40, 1785, 11, 18446744073709551616, 108059554232795664, 108059554232795664⟩
def pH1783 : Prm := ⟨80, 37, 40, 1785, 11, 18446744073709551616, 108060653744423440, 108060653744423440⟩
def pI1783 : Prm := ⟨67, 34, 30, 1785, 11, 18446744073709551616, 108059554232795664, 108060653744423440⟩
noncomputable def L1783_cp1 : Nat × Nat := t7val% (fastRun pL1783 1 1028 (init pL1783) (init pL1783))
theorem L1783_seg1 : segOK pL1783 1 1028 (init pL1783) (init pL1783) L1783_cp1.1 L1783_cp1.2 = true := by
  decide +kernel
noncomputable def L1783_cp2 : Nat × Nat := t7val% (fastRun pL1783 1 1455 (init pL1783) (init pL1783))
theorem L1783_seg2 : segOK pL1783 1029 427 L1783_cp1.1 L1783_cp1.2 L1783_cp2.1 L1783_cp2.2 = true := by
  decide +kernel
theorem L1783_fin : (prmOK pL1783 1783 && ptTest pL1783 (runFrom pL1783 (fmask pL1783) (cmask pL1783) (hmask pL1783) 1456 327 (true, L1783_cp2.1, L1783_cp2.2)) 1783 892 false) = true := by
  decide +kernel
theorem L1783_ok : RunOK pL1783 1783 (runFrom pL1783 (fmask pL1783) (cmask pL1783) (hmask pL1783) 1456 327 (true, L1783_cp2.1, L1783_cp2.2)) ∧ ptTest pL1783 (runFrom pL1783 (fmask pL1783) (cmask pL1783) (hmask pL1783) 1456 327 (true, L1783_cp2.1, L1783_cp2.2)) 1783 892 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1783_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1783_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1783_fin) true) L1783_seg1) L1783_seg2) (by decide) rfl L1783_fin ptTest_fst
noncomputable def H1783_cp1 : Nat × Nat := t7val% (fastRun pH1783 1 1028 (init pH1783) (init pH1783))
theorem H1783_seg1 : segOK pH1783 1 1028 (init pH1783) (init pH1783) H1783_cp1.1 H1783_cp1.2 = true := by
  decide +kernel
noncomputable def H1783_cp2 : Nat × Nat := t7val% (fastRun pH1783 1 1455 (init pH1783) (init pH1783))
theorem H1783_seg2 : segOK pH1783 1029 427 H1783_cp1.1 H1783_cp1.2 H1783_cp2.1 H1783_cp2.2 = true := by
  decide +kernel
theorem H1783_fin : (prmOK pH1783 1783 && ptTest pH1783 (runFrom pH1783 (fmask pH1783) (cmask pH1783) (hmask pH1783) 1456 327 (true, H1783_cp2.1, H1783_cp2.2)) 1783 892 true) = true := by
  decide +kernel
theorem H1783_ok : RunOK pH1783 1783 (runFrom pH1783 (fmask pH1783) (cmask pH1783) (hmask pH1783) 1456 327 (true, H1783_cp2.1, H1783_cp2.2)) ∧ ptTest pH1783 (runFrom pH1783 (fmask pH1783) (cmask pH1783) (hmask pH1783) 1456 327 (true, H1783_cp2.1, H1783_cp2.2)) 1783 892 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1783_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1783_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1783_fin) true) H1783_seg1) H1783_seg2) (by decide) rfl H1783_fin ptTest_fst
noncomputable def I1783_cp1 : Nat × Nat := t7val% (fastRun pI1783 1 1260 (init pI1783) (init pI1783))
theorem I1783_seg1 : segOK pI1783 1 1260 (init pI1783) (init pI1783) I1783_cp1.1 I1783_cp1.2 = true := by
  decide +kernel
theorem I1783_fin : (prmOK pI1783 1783 && intTest pI1783 (runFrom pI1783 (fmask pI1783) (cmask pI1783) (hmask pI1783) 1261 522 (true, I1783_cp1.1, I1783_cp1.2)) 1783 21 false) = true := by
  decide +kernel
theorem I1783_ok : RunOK pI1783 1783 (runFrom pI1783 (fmask pI1783) (cmask pI1783) (hmask pI1783) 1261 522 (true, I1783_cp1.1, I1783_cp1.2)) ∧ intTest pI1783 (runFrom pI1783 (fmask pI1783) (cmask pI1783) (hmask pI1783) 1261 522 (true, I1783_cp1.1, I1783_cp1.2)) 1783 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1783_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1783_fin) true) I1783_seg1) (by decide) rfl I1783_fin intTest_fst
theorem link1783 : linkOK pL1783 pH1783 pI1783 = true := by decide +kernel
theorem cvx1783 : ConvexBetweenHumps 1783 :=
  cvx_of L1783_ok H1783_ok I1783_ok link1783 (by decide)

/-! ### The range -/

theorem cvx_1772_1783 {N : ℕ} (h1 : 1772 ≤ N) (h2 : N ≤ 1783) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1777
  · by_cases h4 : N ≤ 1774
    · by_cases h6 : N ≤ 1772
      · obtain rfl : N = 1772 := by omega
        exact cvx1772
      · by_cases h8 : N ≤ 1773
        · obtain rfl : N = 1773 := by omega
          exact cvx1773
        · obtain rfl : N = 1774 := by omega
          exact cvx1774
    · by_cases h6 : N ≤ 1775
      · obtain rfl : N = 1775 := by omega
        exact cvx1775
      · by_cases h8 : N ≤ 1776
        · obtain rfl : N = 1776 := by omega
          exact cvx1776
        · obtain rfl : N = 1777 := by omega
          exact cvx1777
  · by_cases h4 : N ≤ 1780
    · by_cases h6 : N ≤ 1778
      · obtain rfl : N = 1778 := by omega
        exact cvx1778
      · by_cases h8 : N ≤ 1779
        · obtain rfl : N = 1779 := by omega
          exact cvx1779
        · obtain rfl : N = 1780 := by omega
          exact cvx1780
    · by_cases h6 : N ≤ 1781
      · obtain rfl : N = 1781 := by omega
        exact cvx1781
      · by_cases h8 : N ≤ 1782
        · obtain rfl : N = 1782 := by omega
          exact cvx1782
        · obtain rfl : N = 1783 := by omega
          exact cvx1783

theorem cen_1772_1783 {N : ℕ} (h1 : 1772 ≤ N) (h2 : N ≤ 1783) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1776
  · by_cases h4 : N ≤ 1772
    · obtain rfl : N = 1772 := by omega
      exact cen1772
    · by_cases h6 : N ≤ 1774
      · obtain rfl : N = 1774 := by omega
        exact cen1774
      · obtain rfl : N = 1776 := by omega
        exact cen1776
  · by_cases h4 : N ≤ 1778
    · obtain rfl : N = 1778 := by omega
      exact cen1778
    · by_cases h6 : N ≤ 1780
      · obtain rfl : N = 1780 := by omega
        exact cen1780
      · obtain rfl : N = 1782 := by omega
        exact cen1782

end Kagey131.PaperD.T7
