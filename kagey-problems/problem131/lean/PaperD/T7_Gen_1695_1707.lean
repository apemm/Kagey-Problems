import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1695, …, 1707` (generated)

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

/-! ### `N = 1695` -/

def pL1695 : Prm := ⟨80, 37, 40, 1697, 11, 18446744073709551616, 112631319597844562, 112631319597844562⟩
def pH1695 : Prm := ⟨80, 37, 40, 1697, 11, 18446744073709551616, 112632419109472338, 112632419109472338⟩
def pI1695 : Prm := ⟨68, 33, 32, 1697, 11, 18446744073709551616, 112631319597844562, 112632419109472338⟩
noncomputable def L1695_cp1 : Nat × Nat := t7val% (fastRun pL1695 1 978 (init pL1695) (init pL1695))
theorem L1695_seg1 : segOK pL1695 1 978 (init pL1695) (init pL1695) L1695_cp1.1 L1695_cp1.2 = true := by
  decide +kernel
noncomputable def L1695_cp2 : Nat × Nat := t7val% (fastRun pL1695 1 1383 (init pL1695) (init pL1695))
theorem L1695_seg2 : segOK pL1695 979 405 L1695_cp1.1 L1695_cp1.2 L1695_cp2.1 L1695_cp2.2 = true := by
  decide +kernel
theorem L1695_fin : (prmOK pL1695 1695 && ptTest pL1695 (runFrom pL1695 (fmask pL1695) (cmask pL1695) (hmask pL1695) 1384 311 (true, L1695_cp2.1, L1695_cp2.2)) 1695 848 false) = true := by
  decide +kernel
theorem L1695_ok : RunOK pL1695 1695 (runFrom pL1695 (fmask pL1695) (cmask pL1695) (hmask pL1695) 1384 311 (true, L1695_cp2.1, L1695_cp2.2)) ∧ ptTest pL1695 (runFrom pL1695 (fmask pL1695) (cmask pL1695) (hmask pL1695) 1384 311 (true, L1695_cp2.1, L1695_cp2.2)) 1695 848 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1695_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1695_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1695_fin) true) L1695_seg1) L1695_seg2) (by decide) rfl L1695_fin ptTest_fst
noncomputable def H1695_cp1 : Nat × Nat := t7val% (fastRun pH1695 1 978 (init pH1695) (init pH1695))
theorem H1695_seg1 : segOK pH1695 1 978 (init pH1695) (init pH1695) H1695_cp1.1 H1695_cp1.2 = true := by
  decide +kernel
noncomputable def H1695_cp2 : Nat × Nat := t7val% (fastRun pH1695 1 1383 (init pH1695) (init pH1695))
theorem H1695_seg2 : segOK pH1695 979 405 H1695_cp1.1 H1695_cp1.2 H1695_cp2.1 H1695_cp2.2 = true := by
  decide +kernel
theorem H1695_fin : (prmOK pH1695 1695 && ptTest pH1695 (runFrom pH1695 (fmask pH1695) (cmask pH1695) (hmask pH1695) 1384 311 (true, H1695_cp2.1, H1695_cp2.2)) 1695 848 true) = true := by
  decide +kernel
theorem H1695_ok : RunOK pH1695 1695 (runFrom pH1695 (fmask pH1695) (cmask pH1695) (hmask pH1695) 1384 311 (true, H1695_cp2.1, H1695_cp2.2)) ∧ ptTest pH1695 (runFrom pH1695 (fmask pH1695) (cmask pH1695) (hmask pH1695) 1384 311 (true, H1695_cp2.1, H1695_cp2.2)) 1695 848 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1695_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1695_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1695_fin) true) H1695_seg1) H1695_seg2) (by decide) rfl H1695_fin ptTest_fst
noncomputable def I1695_cp1 : Nat × Nat := t7val% (fastRun pI1695 1 1198 (init pI1695) (init pI1695))
theorem I1695_seg1 : segOK pI1695 1 1198 (init pI1695) (init pI1695) I1695_cp1.1 I1695_cp1.2 = true := by
  decide +kernel
theorem I1695_fin : (prmOK pI1695 1695 && intTest pI1695 (runFrom pI1695 (fmask pI1695) (cmask pI1695) (hmask pI1695) 1199 496 (true, I1695_cp1.1, I1695_cp1.2)) 1695 21 false) = true := by
  decide +kernel
theorem I1695_ok : RunOK pI1695 1695 (runFrom pI1695 (fmask pI1695) (cmask pI1695) (hmask pI1695) 1199 496 (true, I1695_cp1.1, I1695_cp1.2)) ∧ intTest pI1695 (runFrom pI1695 (fmask pI1695) (cmask pI1695) (hmask pI1695) 1199 496 (true, I1695_cp1.1, I1695_cp1.2)) 1695 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1695_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1695_fin) true) I1695_seg1) (by decide) rfl I1695_fin intTest_fst
theorem link1695 : linkOK pL1695 pH1695 pI1695 = true := by decide +kernel
theorem cvx1695 : ConvexBetweenHumps 1695 :=
  cvx_of L1695_ok H1695_ok I1695_ok link1695 (by decide)

/-! ### `N = 1696` -/

def pL1696 : Prm := ⟨80, 37, 40, 1698, 11, 18446744073709551616, 112577014661243093, 112577014661243093⟩
def pH1696 : Prm := ⟨80, 37, 40, 1698, 11, 18446744073709551616, 112578114172870869, 112578114172870869⟩
def pI1696 : Prm := ⟨68, 33, 32, 1698, 11, 18446744073709551616, 112577014661243093, 112578114172870869⟩
noncomputable def L1696_cp1 : Nat × Nat := t7val% (fastRun pL1696 1 978 (init pL1696) (init pL1696))
theorem L1696_seg1 : segOK pL1696 1 978 (init pL1696) (init pL1696) L1696_cp1.1 L1696_cp1.2 = true := by
  decide +kernel
noncomputable def L1696_cp2 : Nat × Nat := t7val% (fastRun pL1696 1 1384 (init pL1696) (init pL1696))
theorem L1696_seg2 : segOK pL1696 979 406 L1696_cp1.1 L1696_cp1.2 L1696_cp2.1 L1696_cp2.2 = true := by
  decide +kernel
theorem L1696_fin : (prmOK pL1696 1696 && ptTest pL1696 (runFrom pL1696 (fmask pL1696) (cmask pL1696) (hmask pL1696) 1385 311 (true, L1696_cp2.1, L1696_cp2.2)) 1696 848 false) = true := by
  decide +kernel
theorem L1696_ok : RunOK pL1696 1696 (runFrom pL1696 (fmask pL1696) (cmask pL1696) (hmask pL1696) 1385 311 (true, L1696_cp2.1, L1696_cp2.2)) ∧ ptTest pL1696 (runFrom pL1696 (fmask pL1696) (cmask pL1696) (hmask pL1696) 1385 311 (true, L1696_cp2.1, L1696_cp2.2)) 1696 848 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1696_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1696_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1696_fin) true) L1696_seg1) L1696_seg2) (by decide) rfl L1696_fin ptTest_fst
noncomputable def H1696_cp1 : Nat × Nat := t7val% (fastRun pH1696 1 978 (init pH1696) (init pH1696))
theorem H1696_seg1 : segOK pH1696 1 978 (init pH1696) (init pH1696) H1696_cp1.1 H1696_cp1.2 = true := by
  decide +kernel
noncomputable def H1696_cp2 : Nat × Nat := t7val% (fastRun pH1696 1 1384 (init pH1696) (init pH1696))
theorem H1696_seg2 : segOK pH1696 979 406 H1696_cp1.1 H1696_cp1.2 H1696_cp2.1 H1696_cp2.2 = true := by
  decide +kernel
theorem H1696_fin : (prmOK pH1696 1696 && ptTest pH1696 (runFrom pH1696 (fmask pH1696) (cmask pH1696) (hmask pH1696) 1385 311 (true, H1696_cp2.1, H1696_cp2.2)) 1696 848 true) = true := by
  decide +kernel
theorem H1696_ok : RunOK pH1696 1696 (runFrom pH1696 (fmask pH1696) (cmask pH1696) (hmask pH1696) 1385 311 (true, H1696_cp2.1, H1696_cp2.2)) ∧ ptTest pH1696 (runFrom pH1696 (fmask pH1696) (cmask pH1696) (hmask pH1696) 1385 311 (true, H1696_cp2.1, H1696_cp2.2)) 1696 848 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1696_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1696_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1696_fin) true) H1696_seg1) H1696_seg2) (by decide) rfl H1696_fin ptTest_fst
noncomputable def I1696_cp1 : Nat × Nat := t7val% (fastRun pI1696 1 1198 (init pI1696) (init pI1696))
theorem I1696_seg1 : segOK pI1696 1 1198 (init pI1696) (init pI1696) I1696_cp1.1 I1696_cp1.2 = true := by
  decide +kernel
theorem I1696_fin : (prmOK pI1696 1696 && intTest pI1696 (runFrom pI1696 (fmask pI1696) (cmask pI1696) (hmask pI1696) 1199 497 (true, I1696_cp1.1, I1696_cp1.2)) 1696 21 true) = true := by
  decide +kernel
theorem I1696_ok : RunOK pI1696 1696 (runFrom pI1696 (fmask pI1696) (cmask pI1696) (hmask pI1696) 1199 497 (true, I1696_cp1.1, I1696_cp1.2)) ∧ intTest pI1696 (runFrom pI1696 (fmask pI1696) (cmask pI1696) (hmask pI1696) 1199 497 (true, I1696_cp1.1, I1696_cp1.2)) 1696 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1696_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1696_fin) true) I1696_seg1) (by decide) rfl I1696_fin intTest_fst
theorem link1696 : linkOK pL1696 pH1696 pI1696 = true := by decide +kernel
theorem cvx1696 : ConvexBetweenHumps 1696 :=
  cvx_of L1696_ok H1696_ok I1696_ok link1696 (by decide)
theorem cenlink1696 : cenLinkOK pI1696 1696 = true := by decide +kernel
theorem cen1696 : CenterUniqueMin 1696 ∧ DipHyp 1696 ∧ OnePointHyps 1696 :=
  cen_of L1696_ok H1696_ok I1696_ok link1696 cenlink1696

/-! ### `N = 1697` -/

def pL1697 : Prm := ⟨80, 37, 40, 1699, 11, 18446744073709551616, 112522743536435154, 112522743536435154⟩
def pH1697 : Prm := ⟨80, 37, 40, 1699, 11, 18446744073709551616, 112523843048062930, 112523843048062930⟩
def pI1697 : Prm := ⟨68, 33, 32, 1699, 11, 18446744073709551616, 112522743536435154, 112523843048062930⟩
noncomputable def L1697_cp1 : Nat × Nat := t7val% (fastRun pL1697 1 979 (init pL1697) (init pL1697))
theorem L1697_seg1 : segOK pL1697 1 979 (init pL1697) (init pL1697) L1697_cp1.1 L1697_cp1.2 = true := by
  decide +kernel
noncomputable def L1697_cp2 : Nat × Nat := t7val% (fastRun pL1697 1 1385 (init pL1697) (init pL1697))
theorem L1697_seg2 : segOK pL1697 980 406 L1697_cp1.1 L1697_cp1.2 L1697_cp2.1 L1697_cp2.2 = true := by
  decide +kernel
theorem L1697_fin : (prmOK pL1697 1697 && ptTest pL1697 (runFrom pL1697 (fmask pL1697) (cmask pL1697) (hmask pL1697) 1386 311 (true, L1697_cp2.1, L1697_cp2.2)) 1697 849 false) = true := by
  decide +kernel
theorem L1697_ok : RunOK pL1697 1697 (runFrom pL1697 (fmask pL1697) (cmask pL1697) (hmask pL1697) 1386 311 (true, L1697_cp2.1, L1697_cp2.2)) ∧ ptTest pL1697 (runFrom pL1697 (fmask pL1697) (cmask pL1697) (hmask pL1697) 1386 311 (true, L1697_cp2.1, L1697_cp2.2)) 1697 849 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1697_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1697_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1697_fin) true) L1697_seg1) L1697_seg2) (by decide) rfl L1697_fin ptTest_fst
noncomputable def H1697_cp1 : Nat × Nat := t7val% (fastRun pH1697 1 979 (init pH1697) (init pH1697))
theorem H1697_seg1 : segOK pH1697 1 979 (init pH1697) (init pH1697) H1697_cp1.1 H1697_cp1.2 = true := by
  decide +kernel
noncomputable def H1697_cp2 : Nat × Nat := t7val% (fastRun pH1697 1 1385 (init pH1697) (init pH1697))
theorem H1697_seg2 : segOK pH1697 980 406 H1697_cp1.1 H1697_cp1.2 H1697_cp2.1 H1697_cp2.2 = true := by
  decide +kernel
theorem H1697_fin : (prmOK pH1697 1697 && ptTest pH1697 (runFrom pH1697 (fmask pH1697) (cmask pH1697) (hmask pH1697) 1386 311 (true, H1697_cp2.1, H1697_cp2.2)) 1697 849 true) = true := by
  decide +kernel
theorem H1697_ok : RunOK pH1697 1697 (runFrom pH1697 (fmask pH1697) (cmask pH1697) (hmask pH1697) 1386 311 (true, H1697_cp2.1, H1697_cp2.2)) ∧ ptTest pH1697 (runFrom pH1697 (fmask pH1697) (cmask pH1697) (hmask pH1697) 1386 311 (true, H1697_cp2.1, H1697_cp2.2)) 1697 849 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1697_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1697_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1697_fin) true) H1697_seg1) H1697_seg2) (by decide) rfl H1697_fin ptTest_fst
noncomputable def I1697_cp1 : Nat × Nat := t7val% (fastRun pI1697 1 1199 (init pI1697) (init pI1697))
theorem I1697_seg1 : segOK pI1697 1 1199 (init pI1697) (init pI1697) I1697_cp1.1 I1697_cp1.2 = true := by
  decide +kernel
theorem I1697_fin : (prmOK pI1697 1697 && intTest pI1697 (runFrom pI1697 (fmask pI1697) (cmask pI1697) (hmask pI1697) 1200 497 (true, I1697_cp1.1, I1697_cp1.2)) 1697 21 false) = true := by
  decide +kernel
theorem I1697_ok : RunOK pI1697 1697 (runFrom pI1697 (fmask pI1697) (cmask pI1697) (hmask pI1697) 1200 497 (true, I1697_cp1.1, I1697_cp1.2)) ∧ intTest pI1697 (runFrom pI1697 (fmask pI1697) (cmask pI1697) (hmask pI1697) 1200 497 (true, I1697_cp1.1, I1697_cp1.2)) 1697 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1697_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1697_fin) true) I1697_seg1) (by decide) rfl I1697_fin intTest_fst
theorem link1697 : linkOK pL1697 pH1697 pI1697 = true := by decide +kernel
theorem cvx1697 : ConvexBetweenHumps 1697 :=
  cvx_of L1697_ok H1697_ok I1697_ok link1697 (by decide)

/-! ### `N = 1698` -/

def pL1698 : Prm := ⟨80, 37, 40, 1700, 11, 18446744073709551616, 112468552228180064, 112468552228180064⟩
def pH1698 : Prm := ⟨80, 37, 40, 1700, 11, 18446744073709551616, 112469651739807840, 112469651739807840⟩
def pI1698 : Prm := ⟨68, 33, 32, 1700, 11, 18446744073709551616, 112468552228180064, 112469651739807840⟩
noncomputable def L1698_cp1 : Nat × Nat := t7val% (fastRun pL1698 1 979 (init pL1698) (init pL1698))
theorem L1698_seg1 : segOK pL1698 1 979 (init pL1698) (init pL1698) L1698_cp1.1 L1698_cp1.2 = true := by
  decide +kernel
noncomputable def L1698_cp2 : Nat × Nat := t7val% (fastRun pL1698 1 1385 (init pL1698) (init pL1698))
theorem L1698_seg2 : segOK pL1698 980 406 L1698_cp1.1 L1698_cp1.2 L1698_cp2.1 L1698_cp2.2 = true := by
  decide +kernel
theorem L1698_fin : (prmOK pL1698 1698 && ptTest pL1698 (runFrom pL1698 (fmask pL1698) (cmask pL1698) (hmask pL1698) 1386 312 (true, L1698_cp2.1, L1698_cp2.2)) 1698 849 false) = true := by
  decide +kernel
theorem L1698_ok : RunOK pL1698 1698 (runFrom pL1698 (fmask pL1698) (cmask pL1698) (hmask pL1698) 1386 312 (true, L1698_cp2.1, L1698_cp2.2)) ∧ ptTest pL1698 (runFrom pL1698 (fmask pL1698) (cmask pL1698) (hmask pL1698) 1386 312 (true, L1698_cp2.1, L1698_cp2.2)) 1698 849 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1698_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1698_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1698_fin) true) L1698_seg1) L1698_seg2) (by decide) rfl L1698_fin ptTest_fst
noncomputable def H1698_cp1 : Nat × Nat := t7val% (fastRun pH1698 1 979 (init pH1698) (init pH1698))
theorem H1698_seg1 : segOK pH1698 1 979 (init pH1698) (init pH1698) H1698_cp1.1 H1698_cp1.2 = true := by
  decide +kernel
noncomputable def H1698_cp2 : Nat × Nat := t7val% (fastRun pH1698 1 1385 (init pH1698) (init pH1698))
theorem H1698_seg2 : segOK pH1698 980 406 H1698_cp1.1 H1698_cp1.2 H1698_cp2.1 H1698_cp2.2 = true := by
  decide +kernel
theorem H1698_fin : (prmOK pH1698 1698 && ptTest pH1698 (runFrom pH1698 (fmask pH1698) (cmask pH1698) (hmask pH1698) 1386 312 (true, H1698_cp2.1, H1698_cp2.2)) 1698 849 true) = true := by
  decide +kernel
theorem H1698_ok : RunOK pH1698 1698 (runFrom pH1698 (fmask pH1698) (cmask pH1698) (hmask pH1698) 1386 312 (true, H1698_cp2.1, H1698_cp2.2)) ∧ ptTest pH1698 (runFrom pH1698 (fmask pH1698) (cmask pH1698) (hmask pH1698) 1386 312 (true, H1698_cp2.1, H1698_cp2.2)) 1698 849 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1698_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1698_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1698_fin) true) H1698_seg1) H1698_seg2) (by decide) rfl H1698_fin ptTest_fst
noncomputable def I1698_cp1 : Nat × Nat := t7val% (fastRun pI1698 1 1200 (init pI1698) (init pI1698))
theorem I1698_seg1 : segOK pI1698 1 1200 (init pI1698) (init pI1698) I1698_cp1.1 I1698_cp1.2 = true := by
  decide +kernel
theorem I1698_fin : (prmOK pI1698 1698 && intTest pI1698 (runFrom pI1698 (fmask pI1698) (cmask pI1698) (hmask pI1698) 1201 497 (true, I1698_cp1.1, I1698_cp1.2)) 1698 21 true) = true := by
  decide +kernel
theorem I1698_ok : RunOK pI1698 1698 (runFrom pI1698 (fmask pI1698) (cmask pI1698) (hmask pI1698) 1201 497 (true, I1698_cp1.1, I1698_cp1.2)) ∧ intTest pI1698 (runFrom pI1698 (fmask pI1698) (cmask pI1698) (hmask pI1698) 1201 497 (true, I1698_cp1.1, I1698_cp1.2)) 1698 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1698_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1698_fin) true) I1698_seg1) (by decide) rfl I1698_fin intTest_fst
theorem link1698 : linkOK pL1698 pH1698 pI1698 = true := by decide +kernel
theorem cvx1698 : ConvexBetweenHumps 1698 :=
  cvx_of L1698_ok H1698_ok I1698_ok link1698 (by decide)
theorem cenlink1698 : cenLinkOK pI1698 1698 = true := by decide +kernel
theorem cen1698 : CenterUniqueMin 1698 ∧ DipHyp 1698 ∧ OnePointHyps 1698 :=
  cen_of L1698_ok H1698_ok I1698_ok link1698 cenlink1698

/-! ### `N = 1699` -/

def pL1699 : Prm := ⟨80, 37, 40, 1701, 11, 18446744073709551616, 112414394630372092, 112414394630372092⟩
def pH1699 : Prm := ⟨80, 37, 40, 1701, 11, 18446744073709551616, 112415494141999868, 112415494141999868⟩
def pI1699 : Prm := ⟨68, 33, 32, 1701, 11, 18446744073709551616, 112414394630372092, 112415494141999868⟩
noncomputable def L1699_cp1 : Nat × Nat := t7val% (fastRun pL1699 1 980 (init pL1699) (init pL1699))
theorem L1699_seg1 : segOK pL1699 1 980 (init pL1699) (init pL1699) L1699_cp1.1 L1699_cp1.2 = true := by
  decide +kernel
noncomputable def L1699_cp2 : Nat × Nat := t7val% (fastRun pL1699 1 1386 (init pL1699) (init pL1699))
theorem L1699_seg2 : segOK pL1699 981 406 L1699_cp1.1 L1699_cp1.2 L1699_cp2.1 L1699_cp2.2 = true := by
  decide +kernel
theorem L1699_fin : (prmOK pL1699 1699 && ptTest pL1699 (runFrom pL1699 (fmask pL1699) (cmask pL1699) (hmask pL1699) 1387 312 (true, L1699_cp2.1, L1699_cp2.2)) 1699 850 false) = true := by
  decide +kernel
theorem L1699_ok : RunOK pL1699 1699 (runFrom pL1699 (fmask pL1699) (cmask pL1699) (hmask pL1699) 1387 312 (true, L1699_cp2.1, L1699_cp2.2)) ∧ ptTest pL1699 (runFrom pL1699 (fmask pL1699) (cmask pL1699) (hmask pL1699) 1387 312 (true, L1699_cp2.1, L1699_cp2.2)) 1699 850 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1699_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1699_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1699_fin) true) L1699_seg1) L1699_seg2) (by decide) rfl L1699_fin ptTest_fst
noncomputable def H1699_cp1 : Nat × Nat := t7val% (fastRun pH1699 1 980 (init pH1699) (init pH1699))
theorem H1699_seg1 : segOK pH1699 1 980 (init pH1699) (init pH1699) H1699_cp1.1 H1699_cp1.2 = true := by
  decide +kernel
noncomputable def H1699_cp2 : Nat × Nat := t7val% (fastRun pH1699 1 1386 (init pH1699) (init pH1699))
theorem H1699_seg2 : segOK pH1699 981 406 H1699_cp1.1 H1699_cp1.2 H1699_cp2.1 H1699_cp2.2 = true := by
  decide +kernel
theorem H1699_fin : (prmOK pH1699 1699 && ptTest pH1699 (runFrom pH1699 (fmask pH1699) (cmask pH1699) (hmask pH1699) 1387 312 (true, H1699_cp2.1, H1699_cp2.2)) 1699 850 true) = true := by
  decide +kernel
theorem H1699_ok : RunOK pH1699 1699 (runFrom pH1699 (fmask pH1699) (cmask pH1699) (hmask pH1699) 1387 312 (true, H1699_cp2.1, H1699_cp2.2)) ∧ ptTest pH1699 (runFrom pH1699 (fmask pH1699) (cmask pH1699) (hmask pH1699) 1387 312 (true, H1699_cp2.1, H1699_cp2.2)) 1699 850 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1699_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1699_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1699_fin) true) H1699_seg1) H1699_seg2) (by decide) rfl H1699_fin ptTest_fst
noncomputable def I1699_cp1 : Nat × Nat := t7val% (fastRun pI1699 1 1200 (init pI1699) (init pI1699))
theorem I1699_seg1 : segOK pI1699 1 1200 (init pI1699) (init pI1699) I1699_cp1.1 I1699_cp1.2 = true := by
  decide +kernel
theorem I1699_fin : (prmOK pI1699 1699 && intTest pI1699 (runFrom pI1699 (fmask pI1699) (cmask pI1699) (hmask pI1699) 1201 498 (true, I1699_cp1.1, I1699_cp1.2)) 1699 21 false) = true := by
  decide +kernel
theorem I1699_ok : RunOK pI1699 1699 (runFrom pI1699 (fmask pI1699) (cmask pI1699) (hmask pI1699) 1201 498 (true, I1699_cp1.1, I1699_cp1.2)) ∧ intTest pI1699 (runFrom pI1699 (fmask pI1699) (cmask pI1699) (hmask pI1699) 1201 498 (true, I1699_cp1.1, I1699_cp1.2)) 1699 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1699_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1699_fin) true) I1699_seg1) (by decide) rfl I1699_fin intTest_fst
theorem link1699 : linkOK pL1699 pH1699 pI1699 = true := by decide +kernel
theorem cvx1699 : ConvexBetweenHumps 1699 :=
  cvx_of L1699_ok H1699_ok I1699_ok link1699 (by decide)

/-! ### `N = 1700` -/

def pL1700 : Prm := ⟨80, 37, 40, 1702, 11, 18446744073709551616, 112360316583059579, 112360316583059579⟩
def pH1700 : Prm := ⟨80, 37, 40, 1702, 11, 18446744073709551616, 112361416094687355, 112361416094687355⟩
def pI1700 : Prm := ⟨68, 33, 32, 1702, 11, 18446744073709551616, 112360316583059579, 112361416094687355⟩
noncomputable def L1700_cp1 : Nat × Nat := t7val% (fastRun pL1700 1 980 (init pL1700) (init pL1700))
theorem L1700_seg1 : segOK pL1700 1 980 (init pL1700) (init pL1700) L1700_cp1.1 L1700_cp1.2 = true := by
  decide +kernel
noncomputable def L1700_cp2 : Nat × Nat := t7val% (fastRun pL1700 1 1387 (init pL1700) (init pL1700))
theorem L1700_seg2 : segOK pL1700 981 407 L1700_cp1.1 L1700_cp1.2 L1700_cp2.1 L1700_cp2.2 = true := by
  decide +kernel
theorem L1700_fin : (prmOK pL1700 1700 && ptTest pL1700 (runFrom pL1700 (fmask pL1700) (cmask pL1700) (hmask pL1700) 1388 312 (true, L1700_cp2.1, L1700_cp2.2)) 1700 850 false) = true := by
  decide +kernel
theorem L1700_ok : RunOK pL1700 1700 (runFrom pL1700 (fmask pL1700) (cmask pL1700) (hmask pL1700) 1388 312 (true, L1700_cp2.1, L1700_cp2.2)) ∧ ptTest pL1700 (runFrom pL1700 (fmask pL1700) (cmask pL1700) (hmask pL1700) 1388 312 (true, L1700_cp2.1, L1700_cp2.2)) 1700 850 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1700_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1700_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1700_fin) true) L1700_seg1) L1700_seg2) (by decide) rfl L1700_fin ptTest_fst
noncomputable def H1700_cp1 : Nat × Nat := t7val% (fastRun pH1700 1 980 (init pH1700) (init pH1700))
theorem H1700_seg1 : segOK pH1700 1 980 (init pH1700) (init pH1700) H1700_cp1.1 H1700_cp1.2 = true := by
  decide +kernel
noncomputable def H1700_cp2 : Nat × Nat := t7val% (fastRun pH1700 1 1387 (init pH1700) (init pH1700))
theorem H1700_seg2 : segOK pH1700 981 407 H1700_cp1.1 H1700_cp1.2 H1700_cp2.1 H1700_cp2.2 = true := by
  decide +kernel
theorem H1700_fin : (prmOK pH1700 1700 && ptTest pH1700 (runFrom pH1700 (fmask pH1700) (cmask pH1700) (hmask pH1700) 1388 312 (true, H1700_cp2.1, H1700_cp2.2)) 1700 850 true) = true := by
  decide +kernel
theorem H1700_ok : RunOK pH1700 1700 (runFrom pH1700 (fmask pH1700) (cmask pH1700) (hmask pH1700) 1388 312 (true, H1700_cp2.1, H1700_cp2.2)) ∧ ptTest pH1700 (runFrom pH1700 (fmask pH1700) (cmask pH1700) (hmask pH1700) 1388 312 (true, H1700_cp2.1, H1700_cp2.2)) 1700 850 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1700_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1700_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1700_fin) true) H1700_seg1) H1700_seg2) (by decide) rfl H1700_fin ptTest_fst
noncomputable def I1700_cp1 : Nat × Nat := t7val% (fastRun pI1700 1 1201 (init pI1700) (init pI1700))
theorem I1700_seg1 : segOK pI1700 1 1201 (init pI1700) (init pI1700) I1700_cp1.1 I1700_cp1.2 = true := by
  decide +kernel
theorem I1700_fin : (prmOK pI1700 1700 && intTest pI1700 (runFrom pI1700 (fmask pI1700) (cmask pI1700) (hmask pI1700) 1202 498 (true, I1700_cp1.1, I1700_cp1.2)) 1700 21 true) = true := by
  decide +kernel
theorem I1700_ok : RunOK pI1700 1700 (runFrom pI1700 (fmask pI1700) (cmask pI1700) (hmask pI1700) 1202 498 (true, I1700_cp1.1, I1700_cp1.2)) ∧ intTest pI1700 (runFrom pI1700 (fmask pI1700) (cmask pI1700) (hmask pI1700) 1202 498 (true, I1700_cp1.1, I1700_cp1.2)) 1700 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1700_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1700_fin) true) I1700_seg1) (by decide) rfl I1700_fin intTest_fst
theorem link1700 : linkOK pL1700 pH1700 pI1700 = true := by decide +kernel
theorem cvx1700 : ConvexBetweenHumps 1700 :=
  cvx_of L1700_ok H1700_ok I1700_ok link1700 (by decide)
theorem cenlink1700 : cenLinkOK pI1700 1700 = true := by decide +kernel
theorem cen1700 : CenterUniqueMin 1700 ∧ DipHyp 1700 ∧ OnePointHyps 1700 :=
  cen_of L1700_ok H1700_ok I1700_ok link1700 cenlink1700

/-! ### `N = 1701` -/

def pL1701 : Prm := ⟨80, 37, 40, 1703, 11, 18446744073709551616, 112306272145327387, 112306272145327387⟩
def pH1701 : Prm := ⟨80, 37, 40, 1703, 11, 18446744073709551616, 112307371656955163, 112307371656955163⟩
def pI1701 : Prm := ⟨68, 33, 32, 1703, 11, 18446744073709551616, 112306272145327387, 112307371656955163⟩
noncomputable def L1701_cp1 : Nat × Nat := t7val% (fastRun pL1701 1 981 (init pL1701) (init pL1701))
theorem L1701_seg1 : segOK pL1701 1 981 (init pL1701) (init pL1701) L1701_cp1.1 L1701_cp1.2 = true := by
  decide +kernel
noncomputable def L1701_cp2 : Nat × Nat := t7val% (fastRun pL1701 1 1388 (init pL1701) (init pL1701))
theorem L1701_seg2 : segOK pL1701 982 407 L1701_cp1.1 L1701_cp1.2 L1701_cp2.1 L1701_cp2.2 = true := by
  decide +kernel
theorem L1701_fin : (prmOK pL1701 1701 && ptTest pL1701 (runFrom pL1701 (fmask pL1701) (cmask pL1701) (hmask pL1701) 1389 312 (true, L1701_cp2.1, L1701_cp2.2)) 1701 851 false) = true := by
  decide +kernel
theorem L1701_ok : RunOK pL1701 1701 (runFrom pL1701 (fmask pL1701) (cmask pL1701) (hmask pL1701) 1389 312 (true, L1701_cp2.1, L1701_cp2.2)) ∧ ptTest pL1701 (runFrom pL1701 (fmask pL1701) (cmask pL1701) (hmask pL1701) 1389 312 (true, L1701_cp2.1, L1701_cp2.2)) 1701 851 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1701_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1701_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1701_fin) true) L1701_seg1) L1701_seg2) (by decide) rfl L1701_fin ptTest_fst
noncomputable def H1701_cp1 : Nat × Nat := t7val% (fastRun pH1701 1 981 (init pH1701) (init pH1701))
theorem H1701_seg1 : segOK pH1701 1 981 (init pH1701) (init pH1701) H1701_cp1.1 H1701_cp1.2 = true := by
  decide +kernel
noncomputable def H1701_cp2 : Nat × Nat := t7val% (fastRun pH1701 1 1388 (init pH1701) (init pH1701))
theorem H1701_seg2 : segOK pH1701 982 407 H1701_cp1.1 H1701_cp1.2 H1701_cp2.1 H1701_cp2.2 = true := by
  decide +kernel
theorem H1701_fin : (prmOK pH1701 1701 && ptTest pH1701 (runFrom pH1701 (fmask pH1701) (cmask pH1701) (hmask pH1701) 1389 312 (true, H1701_cp2.1, H1701_cp2.2)) 1701 851 true) = true := by
  decide +kernel
theorem H1701_ok : RunOK pH1701 1701 (runFrom pH1701 (fmask pH1701) (cmask pH1701) (hmask pH1701) 1389 312 (true, H1701_cp2.1, H1701_cp2.2)) ∧ ptTest pH1701 (runFrom pH1701 (fmask pH1701) (cmask pH1701) (hmask pH1701) 1389 312 (true, H1701_cp2.1, H1701_cp2.2)) 1701 851 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1701_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1701_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1701_fin) true) H1701_seg1) H1701_seg2) (by decide) rfl H1701_fin ptTest_fst
noncomputable def I1701_cp1 : Nat × Nat := t7val% (fastRun pI1701 1 1202 (init pI1701) (init pI1701))
theorem I1701_seg1 : segOK pI1701 1 1202 (init pI1701) (init pI1701) I1701_cp1.1 I1701_cp1.2 = true := by
  decide +kernel
theorem I1701_fin : (prmOK pI1701 1701 && intTest pI1701 (runFrom pI1701 (fmask pI1701) (cmask pI1701) (hmask pI1701) 1203 498 (true, I1701_cp1.1, I1701_cp1.2)) 1701 21 false) = true := by
  decide +kernel
theorem I1701_ok : RunOK pI1701 1701 (runFrom pI1701 (fmask pI1701) (cmask pI1701) (hmask pI1701) 1203 498 (true, I1701_cp1.1, I1701_cp1.2)) ∧ intTest pI1701 (runFrom pI1701 (fmask pI1701) (cmask pI1701) (hmask pI1701) 1203 498 (true, I1701_cp1.1, I1701_cp1.2)) 1701 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1701_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1701_fin) true) I1701_seg1) (by decide) rfl I1701_fin intTest_fst
theorem link1701 : linkOK pL1701 pH1701 pI1701 = true := by decide +kernel
theorem cvx1701 : ConvexBetweenHumps 1701 :=
  cvx_of L1701_ok H1701_ok I1701_ok link1701 (by decide)

/-! ### `N = 1702` -/

def pL1702 : Prm := ⟨80, 37, 40, 1704, 11, 18446744073709551616, 112252306993213857, 112252306993213857⟩
def pH1702 : Prm := ⟨80, 37, 40, 1704, 11, 18446744073709551616, 112253406504841633, 112253406504841633⟩
def pI1702 : Prm := ⟨68, 33, 32, 1704, 11, 18446744073709551616, 112252306993213857, 112253406504841633⟩
noncomputable def L1702_cp1 : Nat × Nat := t7val% (fastRun pL1702 1 982 (init pL1702) (init pL1702))
theorem L1702_seg1 : segOK pL1702 1 982 (init pL1702) (init pL1702) L1702_cp1.1 L1702_cp1.2 = true := by
  decide +kernel
noncomputable def L1702_cp2 : Nat × Nat := t7val% (fastRun pL1702 1 1389 (init pL1702) (init pL1702))
theorem L1702_seg2 : segOK pL1702 983 407 L1702_cp1.1 L1702_cp1.2 L1702_cp2.1 L1702_cp2.2 = true := by
  decide +kernel
theorem L1702_fin : (prmOK pL1702 1702 && ptTest pL1702 (runFrom pL1702 (fmask pL1702) (cmask pL1702) (hmask pL1702) 1390 312 (true, L1702_cp2.1, L1702_cp2.2)) 1702 851 false) = true := by
  decide +kernel
theorem L1702_ok : RunOK pL1702 1702 (runFrom pL1702 (fmask pL1702) (cmask pL1702) (hmask pL1702) 1390 312 (true, L1702_cp2.1, L1702_cp2.2)) ∧ ptTest pL1702 (runFrom pL1702 (fmask pL1702) (cmask pL1702) (hmask pL1702) 1390 312 (true, L1702_cp2.1, L1702_cp2.2)) 1702 851 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1702_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1702_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1702_fin) true) L1702_seg1) L1702_seg2) (by decide) rfl L1702_fin ptTest_fst
noncomputable def H1702_cp1 : Nat × Nat := t7val% (fastRun pH1702 1 982 (init pH1702) (init pH1702))
theorem H1702_seg1 : segOK pH1702 1 982 (init pH1702) (init pH1702) H1702_cp1.1 H1702_cp1.2 = true := by
  decide +kernel
noncomputable def H1702_cp2 : Nat × Nat := t7val% (fastRun pH1702 1 1389 (init pH1702) (init pH1702))
theorem H1702_seg2 : segOK pH1702 983 407 H1702_cp1.1 H1702_cp1.2 H1702_cp2.1 H1702_cp2.2 = true := by
  decide +kernel
theorem H1702_fin : (prmOK pH1702 1702 && ptTest pH1702 (runFrom pH1702 (fmask pH1702) (cmask pH1702) (hmask pH1702) 1390 312 (true, H1702_cp2.1, H1702_cp2.2)) 1702 851 true) = true := by
  decide +kernel
theorem H1702_ok : RunOK pH1702 1702 (runFrom pH1702 (fmask pH1702) (cmask pH1702) (hmask pH1702) 1390 312 (true, H1702_cp2.1, H1702_cp2.2)) ∧ ptTest pH1702 (runFrom pH1702 (fmask pH1702) (cmask pH1702) (hmask pH1702) 1390 312 (true, H1702_cp2.1, H1702_cp2.2)) 1702 851 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1702_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1702_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1702_fin) true) H1702_seg1) H1702_seg2) (by decide) rfl H1702_fin ptTest_fst
noncomputable def I1702_cp1 : Nat × Nat := t7val% (fastRun pI1702 1 1202 (init pI1702) (init pI1702))
theorem I1702_seg1 : segOK pI1702 1 1202 (init pI1702) (init pI1702) I1702_cp1.1 I1702_cp1.2 = true := by
  decide +kernel
theorem I1702_fin : (prmOK pI1702 1702 && intTest pI1702 (runFrom pI1702 (fmask pI1702) (cmask pI1702) (hmask pI1702) 1203 499 (true, I1702_cp1.1, I1702_cp1.2)) 1702 21 true) = true := by
  decide +kernel
theorem I1702_ok : RunOK pI1702 1702 (runFrom pI1702 (fmask pI1702) (cmask pI1702) (hmask pI1702) 1203 499 (true, I1702_cp1.1, I1702_cp1.2)) ∧ intTest pI1702 (runFrom pI1702 (fmask pI1702) (cmask pI1702) (hmask pI1702) 1203 499 (true, I1702_cp1.1, I1702_cp1.2)) 1702 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1702_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1702_fin) true) I1702_seg1) (by decide) rfl I1702_fin intTest_fst
theorem link1702 : linkOK pL1702 pH1702 pI1702 = true := by decide +kernel
theorem cvx1702 : ConvexBetweenHumps 1702 :=
  cvx_of L1702_ok H1702_ok I1702_ok link1702 (by decide)
theorem cenlink1702 : cenLinkOK pI1702 1702 = true := by decide +kernel
theorem cen1702 : CenterUniqueMin 1702 ∧ DipHyp 1702 ∧ OnePointHyps 1702 :=
  cen_of L1702_ok H1702_ok I1702_ok link1702 cenlink1702

/-! ### `N = 1703` -/

def pL1703 : Prm := ⟨80, 37, 40, 1705, 11, 18446744073709551616, 112198375350182786, 112198375350182786⟩
def pH1703 : Prm := ⟨80, 37, 40, 1705, 11, 18446744073709551616, 112199474861810562, 112199474861810562⟩
def pI1703 : Prm := ⟨68, 33, 32, 1705, 11, 18446744073709551616, 112198375350182786, 112199474861810562⟩
noncomputable def L1703_cp1 : Nat × Nat := t7val% (fastRun pL1703 1 982 (init pL1703) (init pL1703))
theorem L1703_seg1 : segOK pL1703 1 982 (init pL1703) (init pL1703) L1703_cp1.1 L1703_cp1.2 = true := by
  decide +kernel
noncomputable def L1703_cp2 : Nat × Nat := t7val% (fastRun pL1703 1 1389 (init pL1703) (init pL1703))
theorem L1703_seg2 : segOK pL1703 983 407 L1703_cp1.1 L1703_cp1.2 L1703_cp2.1 L1703_cp2.2 = true := by
  decide +kernel
theorem L1703_fin : (prmOK pL1703 1703 && ptTest pL1703 (runFrom pL1703 (fmask pL1703) (cmask pL1703) (hmask pL1703) 1390 313 (true, L1703_cp2.1, L1703_cp2.2)) 1703 852 false) = true := by
  decide +kernel
theorem L1703_ok : RunOK pL1703 1703 (runFrom pL1703 (fmask pL1703) (cmask pL1703) (hmask pL1703) 1390 313 (true, L1703_cp2.1, L1703_cp2.2)) ∧ ptTest pL1703 (runFrom pL1703 (fmask pL1703) (cmask pL1703) (hmask pL1703) 1390 313 (true, L1703_cp2.1, L1703_cp2.2)) 1703 852 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1703_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1703_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1703_fin) true) L1703_seg1) L1703_seg2) (by decide) rfl L1703_fin ptTest_fst
noncomputable def H1703_cp1 : Nat × Nat := t7val% (fastRun pH1703 1 982 (init pH1703) (init pH1703))
theorem H1703_seg1 : segOK pH1703 1 982 (init pH1703) (init pH1703) H1703_cp1.1 H1703_cp1.2 = true := by
  decide +kernel
noncomputable def H1703_cp2 : Nat × Nat := t7val% (fastRun pH1703 1 1389 (init pH1703) (init pH1703))
theorem H1703_seg2 : segOK pH1703 983 407 H1703_cp1.1 H1703_cp1.2 H1703_cp2.1 H1703_cp2.2 = true := by
  decide +kernel
theorem H1703_fin : (prmOK pH1703 1703 && ptTest pH1703 (runFrom pH1703 (fmask pH1703) (cmask pH1703) (hmask pH1703) 1390 313 (true, H1703_cp2.1, H1703_cp2.2)) 1703 852 true) = true := by
  decide +kernel
theorem H1703_ok : RunOK pH1703 1703 (runFrom pH1703 (fmask pH1703) (cmask pH1703) (hmask pH1703) 1390 313 (true, H1703_cp2.1, H1703_cp2.2)) ∧ ptTest pH1703 (runFrom pH1703 (fmask pH1703) (cmask pH1703) (hmask pH1703) 1390 313 (true, H1703_cp2.1, H1703_cp2.2)) 1703 852 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1703_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1703_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1703_fin) true) H1703_seg1) H1703_seg2) (by decide) rfl H1703_fin ptTest_fst
noncomputable def I1703_cp1 : Nat × Nat := t7val% (fastRun pI1703 1 1203 (init pI1703) (init pI1703))
theorem I1703_seg1 : segOK pI1703 1 1203 (init pI1703) (init pI1703) I1703_cp1.1 I1703_cp1.2 = true := by
  decide +kernel
theorem I1703_fin : (prmOK pI1703 1703 && intTest pI1703 (runFrom pI1703 (fmask pI1703) (cmask pI1703) (hmask pI1703) 1204 499 (true, I1703_cp1.1, I1703_cp1.2)) 1703 21 false) = true := by
  decide +kernel
theorem I1703_ok : RunOK pI1703 1703 (runFrom pI1703 (fmask pI1703) (cmask pI1703) (hmask pI1703) 1204 499 (true, I1703_cp1.1, I1703_cp1.2)) ∧ intTest pI1703 (runFrom pI1703 (fmask pI1703) (cmask pI1703) (hmask pI1703) 1204 499 (true, I1703_cp1.1, I1703_cp1.2)) 1703 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1703_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1703_fin) true) I1703_seg1) (by decide) rfl I1703_fin intTest_fst
theorem link1703 : linkOK pL1703 pH1703 pI1703 = true := by decide +kernel
theorem cvx1703 : ConvexBetweenHumps 1703 :=
  cvx_of L1703_ok H1703_ok I1703_ok link1703 (by decide)

/-! ### `N = 1704` -/

def pL1704 : Prm := ⟨80, 37, 40, 1706, 11, 18446744073709551616, 112144522729092617, 112144522729092617⟩
def pH1704 : Prm := ⟨80, 37, 40, 1706, 11, 18446744073709551616, 112145622240720393, 112145622240720393⟩
def pI1704 : Prm := ⟨68, 33, 32, 1706, 11, 18446744073709551616, 112144522729092617, 112145622240720393⟩
noncomputable def L1704_cp1 : Nat × Nat := t7val% (fastRun pL1704 1 983 (init pL1704) (init pL1704))
theorem L1704_seg1 : segOK pL1704 1 983 (init pL1704) (init pL1704) L1704_cp1.1 L1704_cp1.2 = true := by
  decide +kernel
noncomputable def L1704_cp2 : Nat × Nat := t7val% (fastRun pL1704 1 1390 (init pL1704) (init pL1704))
theorem L1704_seg2 : segOK pL1704 984 407 L1704_cp1.1 L1704_cp1.2 L1704_cp2.1 L1704_cp2.2 = true := by
  decide +kernel
theorem L1704_fin : (prmOK pL1704 1704 && ptTest pL1704 (runFrom pL1704 (fmask pL1704) (cmask pL1704) (hmask pL1704) 1391 313 (true, L1704_cp2.1, L1704_cp2.2)) 1704 852 false) = true := by
  decide +kernel
theorem L1704_ok : RunOK pL1704 1704 (runFrom pL1704 (fmask pL1704) (cmask pL1704) (hmask pL1704) 1391 313 (true, L1704_cp2.1, L1704_cp2.2)) ∧ ptTest pL1704 (runFrom pL1704 (fmask pL1704) (cmask pL1704) (hmask pL1704) 1391 313 (true, L1704_cp2.1, L1704_cp2.2)) 1704 852 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1704_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1704_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1704_fin) true) L1704_seg1) L1704_seg2) (by decide) rfl L1704_fin ptTest_fst
noncomputable def H1704_cp1 : Nat × Nat := t7val% (fastRun pH1704 1 983 (init pH1704) (init pH1704))
theorem H1704_seg1 : segOK pH1704 1 983 (init pH1704) (init pH1704) H1704_cp1.1 H1704_cp1.2 = true := by
  decide +kernel
noncomputable def H1704_cp2 : Nat × Nat := t7val% (fastRun pH1704 1 1390 (init pH1704) (init pH1704))
theorem H1704_seg2 : segOK pH1704 984 407 H1704_cp1.1 H1704_cp1.2 H1704_cp2.1 H1704_cp2.2 = true := by
  decide +kernel
theorem H1704_fin : (prmOK pH1704 1704 && ptTest pH1704 (runFrom pH1704 (fmask pH1704) (cmask pH1704) (hmask pH1704) 1391 313 (true, H1704_cp2.1, H1704_cp2.2)) 1704 852 true) = true := by
  decide +kernel
theorem H1704_ok : RunOK pH1704 1704 (runFrom pH1704 (fmask pH1704) (cmask pH1704) (hmask pH1704) 1391 313 (true, H1704_cp2.1, H1704_cp2.2)) ∧ ptTest pH1704 (runFrom pH1704 (fmask pH1704) (cmask pH1704) (hmask pH1704) 1391 313 (true, H1704_cp2.1, H1704_cp2.2)) 1704 852 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1704_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1704_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1704_fin) true) H1704_seg1) H1704_seg2) (by decide) rfl H1704_fin ptTest_fst
noncomputable def I1704_cp1 : Nat × Nat := t7val% (fastRun pI1704 1 1204 (init pI1704) (init pI1704))
theorem I1704_seg1 : segOK pI1704 1 1204 (init pI1704) (init pI1704) I1704_cp1.1 I1704_cp1.2 = true := by
  decide +kernel
theorem I1704_fin : (prmOK pI1704 1704 && intTest pI1704 (runFrom pI1704 (fmask pI1704) (cmask pI1704) (hmask pI1704) 1205 499 (true, I1704_cp1.1, I1704_cp1.2)) 1704 21 true) = true := by
  decide +kernel
theorem I1704_ok : RunOK pI1704 1704 (runFrom pI1704 (fmask pI1704) (cmask pI1704) (hmask pI1704) 1205 499 (true, I1704_cp1.1, I1704_cp1.2)) ∧ intTest pI1704 (runFrom pI1704 (fmask pI1704) (cmask pI1704) (hmask pI1704) 1205 499 (true, I1704_cp1.1, I1704_cp1.2)) 1704 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1704_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1704_fin) true) I1704_seg1) (by decide) rfl I1704_fin intTest_fst
theorem link1704 : linkOK pL1704 pH1704 pI1704 = true := by decide +kernel
theorem cvx1704 : ConvexBetweenHumps 1704 :=
  cvx_of L1704_ok H1704_ok I1704_ok link1704 (by decide)
theorem cenlink1704 : cenLinkOK pI1704 1704 = true := by decide +kernel
theorem cen1704 : CenterUniqueMin 1704 ∧ DipHyp 1704 ∧ OnePointHyps 1704 :=
  cen_of L1704_ok H1704_ok I1704_ok link1704 cenlink1704

/-! ### `N = 1705` -/

def pL1705 : Prm := ⟨80, 37, 40, 1707, 11, 18446744073709551616, 112090703516992874, 112090703516992874⟩
def pH1705 : Prm := ⟨80, 37, 40, 1707, 11, 18446744073709551616, 112091803028620650, 112091803028620650⟩
def pI1705 : Prm := ⟨68, 33, 32, 1707, 11, 18446744073709551616, 112090703516992874, 112091803028620650⟩
noncomputable def L1705_cp1 : Nat × Nat := t7val% (fastRun pL1705 1 983 (init pL1705) (init pL1705))
theorem L1705_seg1 : segOK pL1705 1 983 (init pL1705) (init pL1705) L1705_cp1.1 L1705_cp1.2 = true := by
  decide +kernel
noncomputable def L1705_cp2 : Nat × Nat := t7val% (fastRun pL1705 1 1391 (init pL1705) (init pL1705))
theorem L1705_seg2 : segOK pL1705 984 408 L1705_cp1.1 L1705_cp1.2 L1705_cp2.1 L1705_cp2.2 = true := by
  decide +kernel
theorem L1705_fin : (prmOK pL1705 1705 && ptTest pL1705 (runFrom pL1705 (fmask pL1705) (cmask pL1705) (hmask pL1705) 1392 313 (true, L1705_cp2.1, L1705_cp2.2)) 1705 853 false) = true := by
  decide +kernel
theorem L1705_ok : RunOK pL1705 1705 (runFrom pL1705 (fmask pL1705) (cmask pL1705) (hmask pL1705) 1392 313 (true, L1705_cp2.1, L1705_cp2.2)) ∧ ptTest pL1705 (runFrom pL1705 (fmask pL1705) (cmask pL1705) (hmask pL1705) 1392 313 (true, L1705_cp2.1, L1705_cp2.2)) 1705 853 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1705_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1705_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1705_fin) true) L1705_seg1) L1705_seg2) (by decide) rfl L1705_fin ptTest_fst
noncomputable def H1705_cp1 : Nat × Nat := t7val% (fastRun pH1705 1 983 (init pH1705) (init pH1705))
theorem H1705_seg1 : segOK pH1705 1 983 (init pH1705) (init pH1705) H1705_cp1.1 H1705_cp1.2 = true := by
  decide +kernel
noncomputable def H1705_cp2 : Nat × Nat := t7val% (fastRun pH1705 1 1391 (init pH1705) (init pH1705))
theorem H1705_seg2 : segOK pH1705 984 408 H1705_cp1.1 H1705_cp1.2 H1705_cp2.1 H1705_cp2.2 = true := by
  decide +kernel
theorem H1705_fin : (prmOK pH1705 1705 && ptTest pH1705 (runFrom pH1705 (fmask pH1705) (cmask pH1705) (hmask pH1705) 1392 313 (true, H1705_cp2.1, H1705_cp2.2)) 1705 853 true) = true := by
  decide +kernel
theorem H1705_ok : RunOK pH1705 1705 (runFrom pH1705 (fmask pH1705) (cmask pH1705) (hmask pH1705) 1392 313 (true, H1705_cp2.1, H1705_cp2.2)) ∧ ptTest pH1705 (runFrom pH1705 (fmask pH1705) (cmask pH1705) (hmask pH1705) 1392 313 (true, H1705_cp2.1, H1705_cp2.2)) 1705 853 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1705_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1705_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1705_fin) true) H1705_seg1) H1705_seg2) (by decide) rfl H1705_fin ptTest_fst
noncomputable def I1705_cp1 : Nat × Nat := t7val% (fastRun pI1705 1 1205 (init pI1705) (init pI1705))
theorem I1705_seg1 : segOK pI1705 1 1205 (init pI1705) (init pI1705) I1705_cp1.1 I1705_cp1.2 = true := by
  decide +kernel
theorem I1705_fin : (prmOK pI1705 1705 && intTest pI1705 (runFrom pI1705 (fmask pI1705) (cmask pI1705) (hmask pI1705) 1206 499 (true, I1705_cp1.1, I1705_cp1.2)) 1705 21 false) = true := by
  decide +kernel
theorem I1705_ok : RunOK pI1705 1705 (runFrom pI1705 (fmask pI1705) (cmask pI1705) (hmask pI1705) 1206 499 (true, I1705_cp1.1, I1705_cp1.2)) ∧ intTest pI1705 (runFrom pI1705 (fmask pI1705) (cmask pI1705) (hmask pI1705) 1206 499 (true, I1705_cp1.1, I1705_cp1.2)) 1705 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1705_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1705_fin) true) I1705_seg1) (by decide) rfl I1705_fin intTest_fst
theorem link1705 : linkOK pL1705 pH1705 pI1705 = true := by decide +kernel
theorem cvx1705 : ConvexBetweenHumps 1705 :=
  cvx_of L1705_ok H1705_ok I1705_ok link1705 (by decide)

/-! ### `N = 1706` -/

def pL1706 : Prm := ⟨80, 37, 40, 1708, 11, 18446744073709551616, 112036963064373757, 112036963064373757⟩
def pH1706 : Prm := ⟨80, 37, 40, 1708, 11, 18446744073709551616, 112038062576001533, 112038062576001533⟩
def pI1706 : Prm := ⟨68, 33, 32, 1708, 11, 18446744073709551616, 112036963064373757, 112038062576001533⟩
noncomputable def L1706_cp1 : Nat × Nat := t7val% (fastRun pL1706 1 984 (init pL1706) (init pL1706))
theorem L1706_seg1 : segOK pL1706 1 984 (init pL1706) (init pL1706) L1706_cp1.1 L1706_cp1.2 = true := by
  decide +kernel
noncomputable def L1706_cp2 : Nat × Nat := t7val% (fastRun pL1706 1 1392 (init pL1706) (init pL1706))
theorem L1706_seg2 : segOK pL1706 985 408 L1706_cp1.1 L1706_cp1.2 L1706_cp2.1 L1706_cp2.2 = true := by
  decide +kernel
theorem L1706_fin : (prmOK pL1706 1706 && ptTest pL1706 (runFrom pL1706 (fmask pL1706) (cmask pL1706) (hmask pL1706) 1393 313 (true, L1706_cp2.1, L1706_cp2.2)) 1706 853 false) = true := by
  decide +kernel
theorem L1706_ok : RunOK pL1706 1706 (runFrom pL1706 (fmask pL1706) (cmask pL1706) (hmask pL1706) 1393 313 (true, L1706_cp2.1, L1706_cp2.2)) ∧ ptTest pL1706 (runFrom pL1706 (fmask pL1706) (cmask pL1706) (hmask pL1706) 1393 313 (true, L1706_cp2.1, L1706_cp2.2)) 1706 853 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1706_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1706_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1706_fin) true) L1706_seg1) L1706_seg2) (by decide) rfl L1706_fin ptTest_fst
noncomputable def H1706_cp1 : Nat × Nat := t7val% (fastRun pH1706 1 984 (init pH1706) (init pH1706))
theorem H1706_seg1 : segOK pH1706 1 984 (init pH1706) (init pH1706) H1706_cp1.1 H1706_cp1.2 = true := by
  decide +kernel
noncomputable def H1706_cp2 : Nat × Nat := t7val% (fastRun pH1706 1 1392 (init pH1706) (init pH1706))
theorem H1706_seg2 : segOK pH1706 985 408 H1706_cp1.1 H1706_cp1.2 H1706_cp2.1 H1706_cp2.2 = true := by
  decide +kernel
theorem H1706_fin : (prmOK pH1706 1706 && ptTest pH1706 (runFrom pH1706 (fmask pH1706) (cmask pH1706) (hmask pH1706) 1393 313 (true, H1706_cp2.1, H1706_cp2.2)) 1706 853 true) = true := by
  decide +kernel
theorem H1706_ok : RunOK pH1706 1706 (runFrom pH1706 (fmask pH1706) (cmask pH1706) (hmask pH1706) 1393 313 (true, H1706_cp2.1, H1706_cp2.2)) ∧ ptTest pH1706 (runFrom pH1706 (fmask pH1706) (cmask pH1706) (hmask pH1706) 1393 313 (true, H1706_cp2.1, H1706_cp2.2)) 1706 853 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1706_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1706_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1706_fin) true) H1706_seg1) H1706_seg2) (by decide) rfl H1706_fin ptTest_fst
noncomputable def I1706_cp1 : Nat × Nat := t7val% (fastRun pI1706 1 1205 (init pI1706) (init pI1706))
theorem I1706_seg1 : segOK pI1706 1 1205 (init pI1706) (init pI1706) I1706_cp1.1 I1706_cp1.2 = true := by
  decide +kernel
theorem I1706_fin : (prmOK pI1706 1706 && intTest pI1706 (runFrom pI1706 (fmask pI1706) (cmask pI1706) (hmask pI1706) 1206 500 (true, I1706_cp1.1, I1706_cp1.2)) 1706 21 true) = true := by
  decide +kernel
theorem I1706_ok : RunOK pI1706 1706 (runFrom pI1706 (fmask pI1706) (cmask pI1706) (hmask pI1706) 1206 500 (true, I1706_cp1.1, I1706_cp1.2)) ∧ intTest pI1706 (runFrom pI1706 (fmask pI1706) (cmask pI1706) (hmask pI1706) 1206 500 (true, I1706_cp1.1, I1706_cp1.2)) 1706 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1706_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1706_fin) true) I1706_seg1) (by decide) rfl I1706_fin intTest_fst
theorem link1706 : linkOK pL1706 pH1706 pI1706 = true := by decide +kernel
theorem cvx1706 : ConvexBetweenHumps 1706 :=
  cvx_of L1706_ok H1706_ok I1706_ok link1706 (by decide)
theorem cenlink1706 : cenLinkOK pI1706 1706 = true := by decide +kernel
theorem cen1706 : CenterUniqueMin 1706 ∧ DipHyp 1706 ∧ OnePointHyps 1706 :=
  cen_of L1706_ok H1706_ok I1706_ok link1706 cenlink1706

/-! ### `N = 1707` -/

def pL1707 : Prm := ⟨80, 37, 40, 1709, 11, 18446744073709551616, 111983255921058862, 111983255921058862⟩
def pH1707 : Prm := ⟨80, 37, 40, 1709, 11, 18446744073709551616, 111984355432686638, 111984355432686638⟩
def pI1707 : Prm := ⟨68, 33, 32, 1709, 11, 18446744073709551616, 111983255921058862, 111984355432686638⟩
noncomputable def L1707_cp1 : Nat × Nat := t7val% (fastRun pL1707 1 985 (init pL1707) (init pL1707))
theorem L1707_seg1 : segOK pL1707 1 985 (init pL1707) (init pL1707) L1707_cp1.1 L1707_cp1.2 = true := by
  decide +kernel
noncomputable def L1707_cp2 : Nat × Nat := t7val% (fastRun pL1707 1 1393 (init pL1707) (init pL1707))
theorem L1707_seg2 : segOK pL1707 986 408 L1707_cp1.1 L1707_cp1.2 L1707_cp2.1 L1707_cp2.2 = true := by
  decide +kernel
theorem L1707_fin : (prmOK pL1707 1707 && ptTest pL1707 (runFrom pL1707 (fmask pL1707) (cmask pL1707) (hmask pL1707) 1394 313 (true, L1707_cp2.1, L1707_cp2.2)) 1707 854 false) = true := by
  decide +kernel
theorem L1707_ok : RunOK pL1707 1707 (runFrom pL1707 (fmask pL1707) (cmask pL1707) (hmask pL1707) 1394 313 (true, L1707_cp2.1, L1707_cp2.2)) ∧ ptTest pL1707 (runFrom pL1707 (fmask pL1707) (cmask pL1707) (hmask pL1707) 1394 313 (true, L1707_cp2.1, L1707_cp2.2)) 1707 854 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1707_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1707_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1707_fin) true) L1707_seg1) L1707_seg2) (by decide) rfl L1707_fin ptTest_fst
noncomputable def H1707_cp1 : Nat × Nat := t7val% (fastRun pH1707 1 985 (init pH1707) (init pH1707))
theorem H1707_seg1 : segOK pH1707 1 985 (init pH1707) (init pH1707) H1707_cp1.1 H1707_cp1.2 = true := by
  decide +kernel
noncomputable def H1707_cp2 : Nat × Nat := t7val% (fastRun pH1707 1 1393 (init pH1707) (init pH1707))
theorem H1707_seg2 : segOK pH1707 986 408 H1707_cp1.1 H1707_cp1.2 H1707_cp2.1 H1707_cp2.2 = true := by
  decide +kernel
theorem H1707_fin : (prmOK pH1707 1707 && ptTest pH1707 (runFrom pH1707 (fmask pH1707) (cmask pH1707) (hmask pH1707) 1394 313 (true, H1707_cp2.1, H1707_cp2.2)) 1707 854 true) = true := by
  decide +kernel
theorem H1707_ok : RunOK pH1707 1707 (runFrom pH1707 (fmask pH1707) (cmask pH1707) (hmask pH1707) 1394 313 (true, H1707_cp2.1, H1707_cp2.2)) ∧ ptTest pH1707 (runFrom pH1707 (fmask pH1707) (cmask pH1707) (hmask pH1707) 1394 313 (true, H1707_cp2.1, H1707_cp2.2)) 1707 854 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1707_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1707_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1707_fin) true) H1707_seg1) H1707_seg2) (by decide) rfl H1707_fin ptTest_fst
noncomputable def I1707_cp1 : Nat × Nat := t7val% (fastRun pI1707 1 1206 (init pI1707) (init pI1707))
theorem I1707_seg1 : segOK pI1707 1 1206 (init pI1707) (init pI1707) I1707_cp1.1 I1707_cp1.2 = true := by
  decide +kernel
theorem I1707_fin : (prmOK pI1707 1707 && intTest pI1707 (runFrom pI1707 (fmask pI1707) (cmask pI1707) (hmask pI1707) 1207 500 (true, I1707_cp1.1, I1707_cp1.2)) 1707 21 false) = true := by
  decide +kernel
theorem I1707_ok : RunOK pI1707 1707 (runFrom pI1707 (fmask pI1707) (cmask pI1707) (hmask pI1707) 1207 500 (true, I1707_cp1.1, I1707_cp1.2)) ∧ intTest pI1707 (runFrom pI1707 (fmask pI1707) (cmask pI1707) (hmask pI1707) 1207 500 (true, I1707_cp1.1, I1707_cp1.2)) 1707 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1707_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1707_fin) true) I1707_seg1) (by decide) rfl I1707_fin intTest_fst
theorem link1707 : linkOK pL1707 pH1707 pI1707 = true := by decide +kernel
theorem cvx1707 : ConvexBetweenHumps 1707 :=
  cvx_of L1707_ok H1707_ok I1707_ok link1707 (by decide)

/-! ### The range -/

theorem cvx_1695_1707 {N : ℕ} (h1 : 1695 ≤ N) (h2 : N ≤ 1707) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1700
  · by_cases h4 : N ≤ 1697
    · by_cases h6 : N ≤ 1695
      · obtain rfl : N = 1695 := by omega
        exact cvx1695
      · by_cases h8 : N ≤ 1696
        · obtain rfl : N = 1696 := by omega
          exact cvx1696
        · obtain rfl : N = 1697 := by omega
          exact cvx1697
    · by_cases h6 : N ≤ 1698
      · obtain rfl : N = 1698 := by omega
        exact cvx1698
      · by_cases h8 : N ≤ 1699
        · obtain rfl : N = 1699 := by omega
          exact cvx1699
        · obtain rfl : N = 1700 := by omega
          exact cvx1700
  · by_cases h4 : N ≤ 1703
    · by_cases h6 : N ≤ 1701
      · obtain rfl : N = 1701 := by omega
        exact cvx1701
      · by_cases h8 : N ≤ 1702
        · obtain rfl : N = 1702 := by omega
          exact cvx1702
        · obtain rfl : N = 1703 := by omega
          exact cvx1703
    · by_cases h6 : N ≤ 1705
      · by_cases h8 : N ≤ 1704
        · obtain rfl : N = 1704 := by omega
          exact cvx1704
        · obtain rfl : N = 1705 := by omega
          exact cvx1705
      · by_cases h8 : N ≤ 1706
        · obtain rfl : N = 1706 := by omega
          exact cvx1706
        · obtain rfl : N = 1707 := by omega
          exact cvx1707

theorem cen_1695_1707 {N : ℕ} (h1 : 1695 ≤ N) (h2 : N ≤ 1707) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1700
  · by_cases h4 : N ≤ 1696
    · obtain rfl : N = 1696 := by omega
      exact cen1696
    · by_cases h6 : N ≤ 1698
      · obtain rfl : N = 1698 := by omega
        exact cen1698
      · obtain rfl : N = 1700 := by omega
        exact cen1700
  · by_cases h4 : N ≤ 1702
    · obtain rfl : N = 1702 := by omega
      exact cen1702
    · by_cases h6 : N ≤ 1704
      · obtain rfl : N = 1704 := by omega
        exact cen1704
      · obtain rfl : N = 1706 := by omega
        exact cen1706

end Kagey131.PaperD.T7
