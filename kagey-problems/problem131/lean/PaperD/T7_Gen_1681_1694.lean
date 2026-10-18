import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1681, …, 1694` (generated)

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

/-! ### `N = 1681` -/

def pL1681 : Prm := ⟨80, 37, 40, 1683, 11, 18446744073709551616, 113397774744392528, 113397774744392528⟩
def pH1681 : Prm := ⟨80, 37, 40, 1683, 11, 18446744073709551616, 113398874256020304, 113398874256020304⟩
def pI1681 : Prm := ⟨68, 33, 32, 1683, 11, 18446744073709551616, 113397774744392528, 113398874256020304⟩
noncomputable def L1681_cp1 : Nat × Nat := t7val% (fastRun pL1681 1 970 (init pL1681) (init pL1681))
theorem L1681_seg1 : segOK pL1681 1 970 (init pL1681) (init pL1681) L1681_cp1.1 L1681_cp1.2 = true := by
  decide +kernel
noncomputable def L1681_cp2 : Nat × Nat := t7val% (fastRun pL1681 1 1372 (init pL1681) (init pL1681))
theorem L1681_seg2 : segOK pL1681 971 402 L1681_cp1.1 L1681_cp1.2 L1681_cp2.1 L1681_cp2.2 = true := by
  decide +kernel
theorem L1681_fin : (prmOK pL1681 1681 && ptTest pL1681 (runFrom pL1681 (fmask pL1681) (cmask pL1681) (hmask pL1681) 1373 308 (true, L1681_cp2.1, L1681_cp2.2)) 1681 841 false) = true := by
  decide +kernel
theorem L1681_ok : RunOK pL1681 1681 (runFrom pL1681 (fmask pL1681) (cmask pL1681) (hmask pL1681) 1373 308 (true, L1681_cp2.1, L1681_cp2.2)) ∧ ptTest pL1681 (runFrom pL1681 (fmask pL1681) (cmask pL1681) (hmask pL1681) 1373 308 (true, L1681_cp2.1, L1681_cp2.2)) 1681 841 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1681_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1681_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1681_fin) true) L1681_seg1) L1681_seg2) (by decide) rfl L1681_fin ptTest_fst
noncomputable def H1681_cp1 : Nat × Nat := t7val% (fastRun pH1681 1 970 (init pH1681) (init pH1681))
theorem H1681_seg1 : segOK pH1681 1 970 (init pH1681) (init pH1681) H1681_cp1.1 H1681_cp1.2 = true := by
  decide +kernel
noncomputable def H1681_cp2 : Nat × Nat := t7val% (fastRun pH1681 1 1372 (init pH1681) (init pH1681))
theorem H1681_seg2 : segOK pH1681 971 402 H1681_cp1.1 H1681_cp1.2 H1681_cp2.1 H1681_cp2.2 = true := by
  decide +kernel
theorem H1681_fin : (prmOK pH1681 1681 && ptTest pH1681 (runFrom pH1681 (fmask pH1681) (cmask pH1681) (hmask pH1681) 1373 308 (true, H1681_cp2.1, H1681_cp2.2)) 1681 841 true) = true := by
  decide +kernel
theorem H1681_ok : RunOK pH1681 1681 (runFrom pH1681 (fmask pH1681) (cmask pH1681) (hmask pH1681) 1373 308 (true, H1681_cp2.1, H1681_cp2.2)) ∧ ptTest pH1681 (runFrom pH1681 (fmask pH1681) (cmask pH1681) (hmask pH1681) 1373 308 (true, H1681_cp2.1, H1681_cp2.2)) 1681 841 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1681_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1681_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1681_fin) true) H1681_seg1) H1681_seg2) (by decide) rfl H1681_fin ptTest_fst
noncomputable def I1681_cp1 : Nat × Nat := t7val% (fastRun pI1681 1 1188 (init pI1681) (init pI1681))
theorem I1681_seg1 : segOK pI1681 1 1188 (init pI1681) (init pI1681) I1681_cp1.1 I1681_cp1.2 = true := by
  decide +kernel
theorem I1681_fin : (prmOK pI1681 1681 && intTest pI1681 (runFrom pI1681 (fmask pI1681) (cmask pI1681) (hmask pI1681) 1189 492 (true, I1681_cp1.1, I1681_cp1.2)) 1681 21 false) = true := by
  decide +kernel
theorem I1681_ok : RunOK pI1681 1681 (runFrom pI1681 (fmask pI1681) (cmask pI1681) (hmask pI1681) 1189 492 (true, I1681_cp1.1, I1681_cp1.2)) ∧ intTest pI1681 (runFrom pI1681 (fmask pI1681) (cmask pI1681) (hmask pI1681) 1189 492 (true, I1681_cp1.1, I1681_cp1.2)) 1681 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1681_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1681_fin) true) I1681_seg1) (by decide) rfl I1681_fin intTest_fst
theorem link1681 : linkOK pL1681 pH1681 pI1681 = true := by decide +kernel
theorem cvx1681 : ConvexBetweenHumps 1681 :=
  cvx_of L1681_ok H1681_ok I1681_ok link1681 (by decide)

/-! ### `N = 1682` -/

def pL1682 : Prm := ⟨80, 37, 40, 1684, 11, 18446744073709551616, 113342663986125901, 113342663986125901⟩
def pH1682 : Prm := ⟨80, 37, 40, 1684, 11, 18446744073709551616, 113343763497753677, 113343763497753677⟩
def pI1682 : Prm := ⟨68, 33, 32, 1684, 11, 18446744073709551616, 113342663986125901, 113343763497753677⟩
noncomputable def L1682_cp1 : Nat × Nat := t7val% (fastRun pL1682 1 970 (init pL1682) (init pL1682))
theorem L1682_seg1 : segOK pL1682 1 970 (init pL1682) (init pL1682) L1682_cp1.1 L1682_cp1.2 = true := by
  decide +kernel
noncomputable def L1682_cp2 : Nat × Nat := t7val% (fastRun pL1682 1 1372 (init pL1682) (init pL1682))
theorem L1682_seg2 : segOK pL1682 971 402 L1682_cp1.1 L1682_cp1.2 L1682_cp2.1 L1682_cp2.2 = true := by
  decide +kernel
theorem L1682_fin : (prmOK pL1682 1682 && ptTest pL1682 (runFrom pL1682 (fmask pL1682) (cmask pL1682) (hmask pL1682) 1373 309 (true, L1682_cp2.1, L1682_cp2.2)) 1682 841 false) = true := by
  decide +kernel
theorem L1682_ok : RunOK pL1682 1682 (runFrom pL1682 (fmask pL1682) (cmask pL1682) (hmask pL1682) 1373 309 (true, L1682_cp2.1, L1682_cp2.2)) ∧ ptTest pL1682 (runFrom pL1682 (fmask pL1682) (cmask pL1682) (hmask pL1682) 1373 309 (true, L1682_cp2.1, L1682_cp2.2)) 1682 841 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1682_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1682_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1682_fin) true) L1682_seg1) L1682_seg2) (by decide) rfl L1682_fin ptTest_fst
noncomputable def H1682_cp1 : Nat × Nat := t7val% (fastRun pH1682 1 970 (init pH1682) (init pH1682))
theorem H1682_seg1 : segOK pH1682 1 970 (init pH1682) (init pH1682) H1682_cp1.1 H1682_cp1.2 = true := by
  decide +kernel
noncomputable def H1682_cp2 : Nat × Nat := t7val% (fastRun pH1682 1 1372 (init pH1682) (init pH1682))
theorem H1682_seg2 : segOK pH1682 971 402 H1682_cp1.1 H1682_cp1.2 H1682_cp2.1 H1682_cp2.2 = true := by
  decide +kernel
theorem H1682_fin : (prmOK pH1682 1682 && ptTest pH1682 (runFrom pH1682 (fmask pH1682) (cmask pH1682) (hmask pH1682) 1373 309 (true, H1682_cp2.1, H1682_cp2.2)) 1682 841 true) = true := by
  decide +kernel
theorem H1682_ok : RunOK pH1682 1682 (runFrom pH1682 (fmask pH1682) (cmask pH1682) (hmask pH1682) 1373 309 (true, H1682_cp2.1, H1682_cp2.2)) ∧ ptTest pH1682 (runFrom pH1682 (fmask pH1682) (cmask pH1682) (hmask pH1682) 1373 309 (true, H1682_cp2.1, H1682_cp2.2)) 1682 841 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1682_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1682_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1682_fin) true) H1682_seg1) H1682_seg2) (by decide) rfl H1682_fin ptTest_fst
noncomputable def I1682_cp1 : Nat × Nat := t7val% (fastRun pI1682 1 1188 (init pI1682) (init pI1682))
theorem I1682_seg1 : segOK pI1682 1 1188 (init pI1682) (init pI1682) I1682_cp1.1 I1682_cp1.2 = true := by
  decide +kernel
theorem I1682_fin : (prmOK pI1682 1682 && intTest pI1682 (runFrom pI1682 (fmask pI1682) (cmask pI1682) (hmask pI1682) 1189 493 (true, I1682_cp1.1, I1682_cp1.2)) 1682 21 true) = true := by
  decide +kernel
theorem I1682_ok : RunOK pI1682 1682 (runFrom pI1682 (fmask pI1682) (cmask pI1682) (hmask pI1682) 1189 493 (true, I1682_cp1.1, I1682_cp1.2)) ∧ intTest pI1682 (runFrom pI1682 (fmask pI1682) (cmask pI1682) (hmask pI1682) 1189 493 (true, I1682_cp1.1, I1682_cp1.2)) 1682 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1682_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1682_fin) true) I1682_seg1) (by decide) rfl I1682_fin intTest_fst
theorem link1682 : linkOK pL1682 pH1682 pI1682 = true := by decide +kernel
theorem cvx1682 : ConvexBetweenHumps 1682 :=
  cvx_of L1682_ok H1682_ok I1682_ok link1682 (by decide)
theorem cenlink1682 : cenLinkOK pI1682 1682 = true := by decide +kernel
theorem cen1682 : CenterUniqueMin 1682 ∧ DipHyp 1682 ∧ OnePointHyps 1682 :=
  cen_of L1682_ok H1682_ok I1682_ok link1682 cenlink1682

/-! ### `N = 1683` -/

def pL1683 : Prm := ⟨80, 37, 40, 1685, 11, 18446744073709551616, 113287587760533116, 113287587760533116⟩
def pH1683 : Prm := ⟨80, 37, 40, 1685, 11, 18446744073709551616, 113288687272160892, 113288687272160892⟩
def pI1683 : Prm := ⟨68, 33, 32, 1685, 11, 18446744073709551616, 113287587760533116, 113288687272160892⟩
noncomputable def L1683_cp1 : Nat × Nat := t7val% (fastRun pL1683 1 971 (init pL1683) (init pL1683))
theorem L1683_seg1 : segOK pL1683 1 971 (init pL1683) (init pL1683) L1683_cp1.1 L1683_cp1.2 = true := by
  decide +kernel
noncomputable def L1683_cp2 : Nat × Nat := t7val% (fastRun pL1683 1 1373 (init pL1683) (init pL1683))
theorem L1683_seg2 : segOK pL1683 972 402 L1683_cp1.1 L1683_cp1.2 L1683_cp2.1 L1683_cp2.2 = true := by
  decide +kernel
theorem L1683_fin : (prmOK pL1683 1683 && ptTest pL1683 (runFrom pL1683 (fmask pL1683) (cmask pL1683) (hmask pL1683) 1374 309 (true, L1683_cp2.1, L1683_cp2.2)) 1683 842 false) = true := by
  decide +kernel
theorem L1683_ok : RunOK pL1683 1683 (runFrom pL1683 (fmask pL1683) (cmask pL1683) (hmask pL1683) 1374 309 (true, L1683_cp2.1, L1683_cp2.2)) ∧ ptTest pL1683 (runFrom pL1683 (fmask pL1683) (cmask pL1683) (hmask pL1683) 1374 309 (true, L1683_cp2.1, L1683_cp2.2)) 1683 842 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1683_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1683_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1683_fin) true) L1683_seg1) L1683_seg2) (by decide) rfl L1683_fin ptTest_fst
noncomputable def H1683_cp1 : Nat × Nat := t7val% (fastRun pH1683 1 971 (init pH1683) (init pH1683))
theorem H1683_seg1 : segOK pH1683 1 971 (init pH1683) (init pH1683) H1683_cp1.1 H1683_cp1.2 = true := by
  decide +kernel
noncomputable def H1683_cp2 : Nat × Nat := t7val% (fastRun pH1683 1 1373 (init pH1683) (init pH1683))
theorem H1683_seg2 : segOK pH1683 972 402 H1683_cp1.1 H1683_cp1.2 H1683_cp2.1 H1683_cp2.2 = true := by
  decide +kernel
theorem H1683_fin : (prmOK pH1683 1683 && ptTest pH1683 (runFrom pH1683 (fmask pH1683) (cmask pH1683) (hmask pH1683) 1374 309 (true, H1683_cp2.1, H1683_cp2.2)) 1683 842 true) = true := by
  decide +kernel
theorem H1683_ok : RunOK pH1683 1683 (runFrom pH1683 (fmask pH1683) (cmask pH1683) (hmask pH1683) 1374 309 (true, H1683_cp2.1, H1683_cp2.2)) ∧ ptTest pH1683 (runFrom pH1683 (fmask pH1683) (cmask pH1683) (hmask pH1683) 1374 309 (true, H1683_cp2.1, H1683_cp2.2)) 1683 842 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1683_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1683_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1683_fin) true) H1683_seg1) H1683_seg2) (by decide) rfl H1683_fin ptTest_fst
noncomputable def I1683_cp1 : Nat × Nat := t7val% (fastRun pI1683 1 1189 (init pI1683) (init pI1683))
theorem I1683_seg1 : segOK pI1683 1 1189 (init pI1683) (init pI1683) I1683_cp1.1 I1683_cp1.2 = true := by
  decide +kernel
theorem I1683_fin : (prmOK pI1683 1683 && intTest pI1683 (runFrom pI1683 (fmask pI1683) (cmask pI1683) (hmask pI1683) 1190 493 (true, I1683_cp1.1, I1683_cp1.2)) 1683 21 false) = true := by
  decide +kernel
theorem I1683_ok : RunOK pI1683 1683 (runFrom pI1683 (fmask pI1683) (cmask pI1683) (hmask pI1683) 1190 493 (true, I1683_cp1.1, I1683_cp1.2)) ∧ intTest pI1683 (runFrom pI1683 (fmask pI1683) (cmask pI1683) (hmask pI1683) 1190 493 (true, I1683_cp1.1, I1683_cp1.2)) 1683 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1683_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1683_fin) true) I1683_seg1) (by decide) rfl I1683_fin intTest_fst
theorem link1683 : linkOK pL1683 pH1683 pI1683 = true := by decide +kernel
theorem cvx1683 : ConvexBetweenHumps 1683 :=
  cvx_of L1683_ok H1683_ok I1683_ok link1683 (by decide)

/-! ### `N = 1684` -/

def pL1684 : Prm := ⟨80, 37, 40, 1686, 11, 18446744073709551616, 113232593248002938, 113232593248002938⟩
def pH1684 : Prm := ⟨80, 37, 40, 1686, 11, 18446744073709551616, 113233692759630714, 113233692759630714⟩
def pI1684 : Prm := ⟨68, 33, 32, 1686, 11, 18446744073709551616, 113232593248002938, 113233692759630714⟩
noncomputable def L1684_cp1 : Nat × Nat := t7val% (fastRun pL1684 1 971 (init pL1684) (init pL1684))
theorem L1684_seg1 : segOK pL1684 1 971 (init pL1684) (init pL1684) L1684_cp1.1 L1684_cp1.2 = true := by
  decide +kernel
noncomputable def L1684_cp2 : Nat × Nat := t7val% (fastRun pL1684 1 1374 (init pL1684) (init pL1684))
theorem L1684_seg2 : segOK pL1684 972 403 L1684_cp1.1 L1684_cp1.2 L1684_cp2.1 L1684_cp2.2 = true := by
  decide +kernel
theorem L1684_fin : (prmOK pL1684 1684 && ptTest pL1684 (runFrom pL1684 (fmask pL1684) (cmask pL1684) (hmask pL1684) 1375 309 (true, L1684_cp2.1, L1684_cp2.2)) 1684 842 false) = true := by
  decide +kernel
theorem L1684_ok : RunOK pL1684 1684 (runFrom pL1684 (fmask pL1684) (cmask pL1684) (hmask pL1684) 1375 309 (true, L1684_cp2.1, L1684_cp2.2)) ∧ ptTest pL1684 (runFrom pL1684 (fmask pL1684) (cmask pL1684) (hmask pL1684) 1375 309 (true, L1684_cp2.1, L1684_cp2.2)) 1684 842 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1684_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1684_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1684_fin) true) L1684_seg1) L1684_seg2) (by decide) rfl L1684_fin ptTest_fst
noncomputable def H1684_cp1 : Nat × Nat := t7val% (fastRun pH1684 1 971 (init pH1684) (init pH1684))
theorem H1684_seg1 : segOK pH1684 1 971 (init pH1684) (init pH1684) H1684_cp1.1 H1684_cp1.2 = true := by
  decide +kernel
noncomputable def H1684_cp2 : Nat × Nat := t7val% (fastRun pH1684 1 1374 (init pH1684) (init pH1684))
theorem H1684_seg2 : segOK pH1684 972 403 H1684_cp1.1 H1684_cp1.2 H1684_cp2.1 H1684_cp2.2 = true := by
  decide +kernel
theorem H1684_fin : (prmOK pH1684 1684 && ptTest pH1684 (runFrom pH1684 (fmask pH1684) (cmask pH1684) (hmask pH1684) 1375 309 (true, H1684_cp2.1, H1684_cp2.2)) 1684 842 true) = true := by
  decide +kernel
theorem H1684_ok : RunOK pH1684 1684 (runFrom pH1684 (fmask pH1684) (cmask pH1684) (hmask pH1684) 1375 309 (true, H1684_cp2.1, H1684_cp2.2)) ∧ ptTest pH1684 (runFrom pH1684 (fmask pH1684) (cmask pH1684) (hmask pH1684) 1375 309 (true, H1684_cp2.1, H1684_cp2.2)) 1684 842 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1684_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1684_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1684_fin) true) H1684_seg1) H1684_seg2) (by decide) rfl H1684_fin ptTest_fst
noncomputable def I1684_cp1 : Nat × Nat := t7val% (fastRun pI1684 1 1190 (init pI1684) (init pI1684))
theorem I1684_seg1 : segOK pI1684 1 1190 (init pI1684) (init pI1684) I1684_cp1.1 I1684_cp1.2 = true := by
  decide +kernel
theorem I1684_fin : (prmOK pI1684 1684 && intTest pI1684 (runFrom pI1684 (fmask pI1684) (cmask pI1684) (hmask pI1684) 1191 493 (true, I1684_cp1.1, I1684_cp1.2)) 1684 21 true) = true := by
  decide +kernel
theorem I1684_ok : RunOK pI1684 1684 (runFrom pI1684 (fmask pI1684) (cmask pI1684) (hmask pI1684) 1191 493 (true, I1684_cp1.1, I1684_cp1.2)) ∧ intTest pI1684 (runFrom pI1684 (fmask pI1684) (cmask pI1684) (hmask pI1684) 1191 493 (true, I1684_cp1.1, I1684_cp1.2)) 1684 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1684_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1684_fin) true) I1684_seg1) (by decide) rfl I1684_fin intTest_fst
theorem link1684 : linkOK pL1684 pH1684 pI1684 = true := by decide +kernel
theorem cvx1684 : ConvexBetweenHumps 1684 :=
  cvx_of L1684_ok H1684_ok I1684_ok link1684 (by decide)
theorem cenlink1684 : cenLinkOK pI1684 1684 = true := by decide +kernel
theorem cen1684 : CenterUniqueMin 1684 ∧ DipHyp 1684 ∧ OnePointHyps 1684 :=
  cen_of L1684_ok H1684_ok I1684_ok link1684 cenlink1684

/-! ### `N = 1685` -/

def pL1685 : Prm := ⟨80, 37, 40, 1687, 11, 18446744073709551616, 113177633163867157, 113177633163867157⟩
def pH1685 : Prm := ⟨80, 37, 40, 1687, 11, 18446744073709551616, 113178732675494933, 113178732675494933⟩
def pI1685 : Prm := ⟨68, 33, 32, 1687, 11, 18446744073709551616, 113177633163867157, 113178732675494933⟩
noncomputable def L1685_cp1 : Nat × Nat := t7val% (fastRun pL1685 1 972 (init pL1685) (init pL1685))
theorem L1685_seg1 : segOK pL1685 1 972 (init pL1685) (init pL1685) L1685_cp1.1 L1685_cp1.2 = true := by
  decide +kernel
noncomputable def L1685_cp2 : Nat × Nat := t7val% (fastRun pL1685 1 1375 (init pL1685) (init pL1685))
theorem L1685_seg2 : segOK pL1685 973 403 L1685_cp1.1 L1685_cp1.2 L1685_cp2.1 L1685_cp2.2 = true := by
  decide +kernel
theorem L1685_fin : (prmOK pL1685 1685 && ptTest pL1685 (runFrom pL1685 (fmask pL1685) (cmask pL1685) (hmask pL1685) 1376 309 (true, L1685_cp2.1, L1685_cp2.2)) 1685 843 false) = true := by
  decide +kernel
theorem L1685_ok : RunOK pL1685 1685 (runFrom pL1685 (fmask pL1685) (cmask pL1685) (hmask pL1685) 1376 309 (true, L1685_cp2.1, L1685_cp2.2)) ∧ ptTest pL1685 (runFrom pL1685 (fmask pL1685) (cmask pL1685) (hmask pL1685) 1376 309 (true, L1685_cp2.1, L1685_cp2.2)) 1685 843 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1685_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1685_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1685_fin) true) L1685_seg1) L1685_seg2) (by decide) rfl L1685_fin ptTest_fst
noncomputable def H1685_cp1 : Nat × Nat := t7val% (fastRun pH1685 1 972 (init pH1685) (init pH1685))
theorem H1685_seg1 : segOK pH1685 1 972 (init pH1685) (init pH1685) H1685_cp1.1 H1685_cp1.2 = true := by
  decide +kernel
noncomputable def H1685_cp2 : Nat × Nat := t7val% (fastRun pH1685 1 1375 (init pH1685) (init pH1685))
theorem H1685_seg2 : segOK pH1685 973 403 H1685_cp1.1 H1685_cp1.2 H1685_cp2.1 H1685_cp2.2 = true := by
  decide +kernel
theorem H1685_fin : (prmOK pH1685 1685 && ptTest pH1685 (runFrom pH1685 (fmask pH1685) (cmask pH1685) (hmask pH1685) 1376 309 (true, H1685_cp2.1, H1685_cp2.2)) 1685 843 true) = true := by
  decide +kernel
theorem H1685_ok : RunOK pH1685 1685 (runFrom pH1685 (fmask pH1685) (cmask pH1685) (hmask pH1685) 1376 309 (true, H1685_cp2.1, H1685_cp2.2)) ∧ ptTest pH1685 (runFrom pH1685 (fmask pH1685) (cmask pH1685) (hmask pH1685) 1376 309 (true, H1685_cp2.1, H1685_cp2.2)) 1685 843 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1685_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1685_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1685_fin) true) H1685_seg1) H1685_seg2) (by decide) rfl H1685_fin ptTest_fst
noncomputable def I1685_cp1 : Nat × Nat := t7val% (fastRun pI1685 1 1190 (init pI1685) (init pI1685))
theorem I1685_seg1 : segOK pI1685 1 1190 (init pI1685) (init pI1685) I1685_cp1.1 I1685_cp1.2 = true := by
  decide +kernel
theorem I1685_fin : (prmOK pI1685 1685 && intTest pI1685 (runFrom pI1685 (fmask pI1685) (cmask pI1685) (hmask pI1685) 1191 494 (true, I1685_cp1.1, I1685_cp1.2)) 1685 21 false) = true := by
  decide +kernel
theorem I1685_ok : RunOK pI1685 1685 (runFrom pI1685 (fmask pI1685) (cmask pI1685) (hmask pI1685) 1191 494 (true, I1685_cp1.1, I1685_cp1.2)) ∧ intTest pI1685 (runFrom pI1685 (fmask pI1685) (cmask pI1685) (hmask pI1685) 1191 494 (true, I1685_cp1.1, I1685_cp1.2)) 1685 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1685_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1685_fin) true) I1685_seg1) (by decide) rfl I1685_fin intTest_fst
theorem link1685 : linkOK pL1685 pH1685 pI1685 = true := by decide +kernel
theorem cvx1685 : ConvexBetweenHumps 1685 :=
  cvx_of L1685_ok H1685_ok I1685_ok link1685 (by decide)

/-! ### `N = 1686` -/

def pL1686 : Prm := ⟨80, 37, 40, 1688, 11, 18446744073709551616, 113122754518158857, 113122754518158857⟩
def pH1686 : Prm := ⟨80, 37, 40, 1688, 11, 18446744073709551616, 113123854029786633, 113123854029786633⟩
def pI1686 : Prm := ⟨68, 33, 32, 1688, 11, 18446744073709551616, 113122754518158857, 113123854029786633⟩
noncomputable def L1686_cp1 : Nat × Nat := t7val% (fastRun pL1686 1 972 (init pL1686) (init pL1686))
theorem L1686_seg1 : segOK pL1686 1 972 (init pL1686) (init pL1686) L1686_cp1.1 L1686_cp1.2 = true := by
  decide +kernel
noncomputable def L1686_cp2 : Nat × Nat := t7val% (fastRun pL1686 1 1376 (init pL1686) (init pL1686))
theorem L1686_seg2 : segOK pL1686 973 404 L1686_cp1.1 L1686_cp1.2 L1686_cp2.1 L1686_cp2.2 = true := by
  decide +kernel
theorem L1686_fin : (prmOK pL1686 1686 && ptTest pL1686 (runFrom pL1686 (fmask pL1686) (cmask pL1686) (hmask pL1686) 1377 309 (true, L1686_cp2.1, L1686_cp2.2)) 1686 843 false) = true := by
  decide +kernel
theorem L1686_ok : RunOK pL1686 1686 (runFrom pL1686 (fmask pL1686) (cmask pL1686) (hmask pL1686) 1377 309 (true, L1686_cp2.1, L1686_cp2.2)) ∧ ptTest pL1686 (runFrom pL1686 (fmask pL1686) (cmask pL1686) (hmask pL1686) 1377 309 (true, L1686_cp2.1, L1686_cp2.2)) 1686 843 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1686_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1686_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1686_fin) true) L1686_seg1) L1686_seg2) (by decide) rfl L1686_fin ptTest_fst
noncomputable def H1686_cp1 : Nat × Nat := t7val% (fastRun pH1686 1 972 (init pH1686) (init pH1686))
theorem H1686_seg1 : segOK pH1686 1 972 (init pH1686) (init pH1686) H1686_cp1.1 H1686_cp1.2 = true := by
  decide +kernel
noncomputable def H1686_cp2 : Nat × Nat := t7val% (fastRun pH1686 1 1376 (init pH1686) (init pH1686))
theorem H1686_seg2 : segOK pH1686 973 404 H1686_cp1.1 H1686_cp1.2 H1686_cp2.1 H1686_cp2.2 = true := by
  decide +kernel
theorem H1686_fin : (prmOK pH1686 1686 && ptTest pH1686 (runFrom pH1686 (fmask pH1686) (cmask pH1686) (hmask pH1686) 1377 309 (true, H1686_cp2.1, H1686_cp2.2)) 1686 843 true) = true := by
  decide +kernel
theorem H1686_ok : RunOK pH1686 1686 (runFrom pH1686 (fmask pH1686) (cmask pH1686) (hmask pH1686) 1377 309 (true, H1686_cp2.1, H1686_cp2.2)) ∧ ptTest pH1686 (runFrom pH1686 (fmask pH1686) (cmask pH1686) (hmask pH1686) 1377 309 (true, H1686_cp2.1, H1686_cp2.2)) 1686 843 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1686_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1686_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1686_fin) true) H1686_seg1) H1686_seg2) (by decide) rfl H1686_fin ptTest_fst
noncomputable def I1686_cp1 : Nat × Nat := t7val% (fastRun pI1686 1 1191 (init pI1686) (init pI1686))
theorem I1686_seg1 : segOK pI1686 1 1191 (init pI1686) (init pI1686) I1686_cp1.1 I1686_cp1.2 = true := by
  decide +kernel
theorem I1686_fin : (prmOK pI1686 1686 && intTest pI1686 (runFrom pI1686 (fmask pI1686) (cmask pI1686) (hmask pI1686) 1192 494 (true, I1686_cp1.1, I1686_cp1.2)) 1686 21 true) = true := by
  decide +kernel
theorem I1686_ok : RunOK pI1686 1686 (runFrom pI1686 (fmask pI1686) (cmask pI1686) (hmask pI1686) 1192 494 (true, I1686_cp1.1, I1686_cp1.2)) ∧ intTest pI1686 (runFrom pI1686 (fmask pI1686) (cmask pI1686) (hmask pI1686) 1192 494 (true, I1686_cp1.1, I1686_cp1.2)) 1686 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1686_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1686_fin) true) I1686_seg1) (by decide) rfl I1686_fin intTest_fst
theorem link1686 : linkOK pL1686 pH1686 pI1686 = true := by decide +kernel
theorem cvx1686 : ConvexBetweenHumps 1686 :=
  cvx_of L1686_ok H1686_ok I1686_ok link1686 (by decide)
theorem cenlink1686 : cenLinkOK pI1686 1686 = true := by decide +kernel
theorem cen1686 : CenterUniqueMin 1686 ∧ DipHyp 1686 ∧ OnePointHyps 1686 :=
  cen_of L1686_ok H1686_ok I1686_ok link1686 cenlink1686

/-! ### `N = 1687` -/

def pL1687 : Prm := ⟨80, 37, 40, 1689, 11, 18446744073709551616, 113067910197008233, 113067910197008233⟩
def pH1687 : Prm := ⟨80, 37, 40, 1689, 11, 18446744073709551616, 113069009708636009, 113069009708636009⟩
def pI1687 : Prm := ⟨68, 33, 32, 1689, 11, 18446744073709551616, 113067910197008233, 113069009708636009⟩
noncomputable def L1687_cp1 : Nat × Nat := t7val% (fastRun pL1687 1 973 (init pL1687) (init pL1687))
theorem L1687_seg1 : segOK pL1687 1 973 (init pL1687) (init pL1687) L1687_cp1.1 L1687_cp1.2 = true := by
  decide +kernel
noncomputable def L1687_cp2 : Nat × Nat := t7val% (fastRun pL1687 1 1376 (init pL1687) (init pL1687))
theorem L1687_seg2 : segOK pL1687 974 403 L1687_cp1.1 L1687_cp1.2 L1687_cp2.1 L1687_cp2.2 = true := by
  decide +kernel
theorem L1687_fin : (prmOK pL1687 1687 && ptTest pL1687 (runFrom pL1687 (fmask pL1687) (cmask pL1687) (hmask pL1687) 1377 310 (true, L1687_cp2.1, L1687_cp2.2)) 1687 844 false) = true := by
  decide +kernel
theorem L1687_ok : RunOK pL1687 1687 (runFrom pL1687 (fmask pL1687) (cmask pL1687) (hmask pL1687) 1377 310 (true, L1687_cp2.1, L1687_cp2.2)) ∧ ptTest pL1687 (runFrom pL1687 (fmask pL1687) (cmask pL1687) (hmask pL1687) 1377 310 (true, L1687_cp2.1, L1687_cp2.2)) 1687 844 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1687_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1687_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1687_fin) true) L1687_seg1) L1687_seg2) (by decide) rfl L1687_fin ptTest_fst
noncomputable def H1687_cp1 : Nat × Nat := t7val% (fastRun pH1687 1 973 (init pH1687) (init pH1687))
theorem H1687_seg1 : segOK pH1687 1 973 (init pH1687) (init pH1687) H1687_cp1.1 H1687_cp1.2 = true := by
  decide +kernel
noncomputable def H1687_cp2 : Nat × Nat := t7val% (fastRun pH1687 1 1376 (init pH1687) (init pH1687))
theorem H1687_seg2 : segOK pH1687 974 403 H1687_cp1.1 H1687_cp1.2 H1687_cp2.1 H1687_cp2.2 = true := by
  decide +kernel
theorem H1687_fin : (prmOK pH1687 1687 && ptTest pH1687 (runFrom pH1687 (fmask pH1687) (cmask pH1687) (hmask pH1687) 1377 310 (true, H1687_cp2.1, H1687_cp2.2)) 1687 844 true) = true := by
  decide +kernel
theorem H1687_ok : RunOK pH1687 1687 (runFrom pH1687 (fmask pH1687) (cmask pH1687) (hmask pH1687) 1377 310 (true, H1687_cp2.1, H1687_cp2.2)) ∧ ptTest pH1687 (runFrom pH1687 (fmask pH1687) (cmask pH1687) (hmask pH1687) 1377 310 (true, H1687_cp2.1, H1687_cp2.2)) 1687 844 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1687_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1687_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1687_fin) true) H1687_seg1) H1687_seg2) (by decide) rfl H1687_fin ptTest_fst
noncomputable def I1687_cp1 : Nat × Nat := t7val% (fastRun pI1687 1 1192 (init pI1687) (init pI1687))
theorem I1687_seg1 : segOK pI1687 1 1192 (init pI1687) (init pI1687) I1687_cp1.1 I1687_cp1.2 = true := by
  decide +kernel
theorem I1687_fin : (prmOK pI1687 1687 && intTest pI1687 (runFrom pI1687 (fmask pI1687) (cmask pI1687) (hmask pI1687) 1193 494 (true, I1687_cp1.1, I1687_cp1.2)) 1687 21 false) = true := by
  decide +kernel
theorem I1687_ok : RunOK pI1687 1687 (runFrom pI1687 (fmask pI1687) (cmask pI1687) (hmask pI1687) 1193 494 (true, I1687_cp1.1, I1687_cp1.2)) ∧ intTest pI1687 (runFrom pI1687 (fmask pI1687) (cmask pI1687) (hmask pI1687) 1193 494 (true, I1687_cp1.1, I1687_cp1.2)) 1687 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1687_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1687_fin) true) I1687_seg1) (by decide) rfl I1687_fin intTest_fst
theorem link1687 : linkOK pL1687 pH1687 pI1687 = true := by decide +kernel
theorem cvx1687 : ConvexBetweenHumps 1687 :=
  cvx_of L1687_ok H1687_ok I1687_ok link1687 (by decide)

/-! ### `N = 1688` -/

def pL1688 : Prm := ⟨80, 37, 40, 1690, 11, 18446744073709551616, 113013147040922790, 113013147040922790⟩
def pH1688 : Prm := ⟨80, 37, 40, 1690, 11, 18446744073709551616, 113014246552550566, 113014246552550566⟩
def pI1688 : Prm := ⟨68, 33, 32, 1690, 11, 18446744073709551616, 113013147040922790, 113014246552550566⟩
noncomputable def L1688_cp1 : Nat × Nat := t7val% (fastRun pL1688 1 974 (init pL1688) (init pL1688))
theorem L1688_seg1 : segOK pL1688 1 974 (init pL1688) (init pL1688) L1688_cp1.1 L1688_cp1.2 = true := by
  decide +kernel
noncomputable def L1688_cp2 : Nat × Nat := t7val% (fastRun pL1688 1 1377 (init pL1688) (init pL1688))
theorem L1688_seg2 : segOK pL1688 975 403 L1688_cp1.1 L1688_cp1.2 L1688_cp2.1 L1688_cp2.2 = true := by
  decide +kernel
theorem L1688_fin : (prmOK pL1688 1688 && ptTest pL1688 (runFrom pL1688 (fmask pL1688) (cmask pL1688) (hmask pL1688) 1378 310 (true, L1688_cp2.1, L1688_cp2.2)) 1688 844 false) = true := by
  decide +kernel
theorem L1688_ok : RunOK pL1688 1688 (runFrom pL1688 (fmask pL1688) (cmask pL1688) (hmask pL1688) 1378 310 (true, L1688_cp2.1, L1688_cp2.2)) ∧ ptTest pL1688 (runFrom pL1688 (fmask pL1688) (cmask pL1688) (hmask pL1688) 1378 310 (true, L1688_cp2.1, L1688_cp2.2)) 1688 844 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1688_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1688_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1688_fin) true) L1688_seg1) L1688_seg2) (by decide) rfl L1688_fin ptTest_fst
noncomputable def H1688_cp1 : Nat × Nat := t7val% (fastRun pH1688 1 974 (init pH1688) (init pH1688))
theorem H1688_seg1 : segOK pH1688 1 974 (init pH1688) (init pH1688) H1688_cp1.1 H1688_cp1.2 = true := by
  decide +kernel
noncomputable def H1688_cp2 : Nat × Nat := t7val% (fastRun pH1688 1 1377 (init pH1688) (init pH1688))
theorem H1688_seg2 : segOK pH1688 975 403 H1688_cp1.1 H1688_cp1.2 H1688_cp2.1 H1688_cp2.2 = true := by
  decide +kernel
theorem H1688_fin : (prmOK pH1688 1688 && ptTest pH1688 (runFrom pH1688 (fmask pH1688) (cmask pH1688) (hmask pH1688) 1378 310 (true, H1688_cp2.1, H1688_cp2.2)) 1688 844 true) = true := by
  decide +kernel
theorem H1688_ok : RunOK pH1688 1688 (runFrom pH1688 (fmask pH1688) (cmask pH1688) (hmask pH1688) 1378 310 (true, H1688_cp2.1, H1688_cp2.2)) ∧ ptTest pH1688 (runFrom pH1688 (fmask pH1688) (cmask pH1688) (hmask pH1688) 1378 310 (true, H1688_cp2.1, H1688_cp2.2)) 1688 844 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1688_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1688_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1688_fin) true) H1688_seg1) H1688_seg2) (by decide) rfl H1688_fin ptTest_fst
noncomputable def I1688_cp1 : Nat × Nat := t7val% (fastRun pI1688 1 1193 (init pI1688) (init pI1688))
theorem I1688_seg1 : segOK pI1688 1 1193 (init pI1688) (init pI1688) I1688_cp1.1 I1688_cp1.2 = true := by
  decide +kernel
theorem I1688_fin : (prmOK pI1688 1688 && intTest pI1688 (runFrom pI1688 (fmask pI1688) (cmask pI1688) (hmask pI1688) 1194 494 (true, I1688_cp1.1, I1688_cp1.2)) 1688 21 true) = true := by
  decide +kernel
theorem I1688_ok : RunOK pI1688 1688 (runFrom pI1688 (fmask pI1688) (cmask pI1688) (hmask pI1688) 1194 494 (true, I1688_cp1.1, I1688_cp1.2)) ∧ intTest pI1688 (runFrom pI1688 (fmask pI1688) (cmask pI1688) (hmask pI1688) 1194 494 (true, I1688_cp1.1, I1688_cp1.2)) 1688 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1688_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1688_fin) true) I1688_seg1) (by decide) rfl I1688_fin intTest_fst
theorem link1688 : linkOK pL1688 pH1688 pI1688 = true := by decide +kernel
theorem cvx1688 : ConvexBetweenHumps 1688 :=
  cvx_of L1688_ok H1688_ok I1688_ok link1688 (by decide)
theorem cenlink1688 : cenLinkOK pI1688 1688 = true := by decide +kernel
theorem cen1688 : CenterUniqueMin 1688 ∧ DipHyp 1688 ∧ OnePointHyps 1688 :=
  cen_of L1688_ok H1688_ok I1688_ok link1688 cenlink1688

/-! ### `N = 1689` -/

def pL1689 : Prm := ⟨80, 37, 40, 1691, 11, 18446744073709551616, 112958418106019468, 112958418106019468⟩
def pH1689 : Prm := ⟨80, 37, 40, 1691, 11, 18446744073709551616, 112959517617647244, 112959517617647244⟩
def pI1689 : Prm := ⟨68, 33, 32, 1691, 11, 18446744073709551616, 112958418106019468, 112959517617647244⟩
noncomputable def L1689_cp1 : Nat × Nat := t7val% (fastRun pL1689 1 974 (init pL1689) (init pL1689))
theorem L1689_seg1 : segOK pL1689 1 974 (init pL1689) (init pL1689) L1689_cp1.1 L1689_cp1.2 = true := by
  decide +kernel
noncomputable def L1689_cp2 : Nat × Nat := t7val% (fastRun pL1689 1 1378 (init pL1689) (init pL1689))
theorem L1689_seg2 : segOK pL1689 975 404 L1689_cp1.1 L1689_cp1.2 L1689_cp2.1 L1689_cp2.2 = true := by
  decide +kernel
theorem L1689_fin : (prmOK pL1689 1689 && ptTest pL1689 (runFrom pL1689 (fmask pL1689) (cmask pL1689) (hmask pL1689) 1379 310 (true, L1689_cp2.1, L1689_cp2.2)) 1689 845 false) = true := by
  decide +kernel
theorem L1689_ok : RunOK pL1689 1689 (runFrom pL1689 (fmask pL1689) (cmask pL1689) (hmask pL1689) 1379 310 (true, L1689_cp2.1, L1689_cp2.2)) ∧ ptTest pL1689 (runFrom pL1689 (fmask pL1689) (cmask pL1689) (hmask pL1689) 1379 310 (true, L1689_cp2.1, L1689_cp2.2)) 1689 845 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1689_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1689_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1689_fin) true) L1689_seg1) L1689_seg2) (by decide) rfl L1689_fin ptTest_fst
noncomputable def H1689_cp1 : Nat × Nat := t7val% (fastRun pH1689 1 974 (init pH1689) (init pH1689))
theorem H1689_seg1 : segOK pH1689 1 974 (init pH1689) (init pH1689) H1689_cp1.1 H1689_cp1.2 = true := by
  decide +kernel
noncomputable def H1689_cp2 : Nat × Nat := t7val% (fastRun pH1689 1 1378 (init pH1689) (init pH1689))
theorem H1689_seg2 : segOK pH1689 975 404 H1689_cp1.1 H1689_cp1.2 H1689_cp2.1 H1689_cp2.2 = true := by
  decide +kernel
theorem H1689_fin : (prmOK pH1689 1689 && ptTest pH1689 (runFrom pH1689 (fmask pH1689) (cmask pH1689) (hmask pH1689) 1379 310 (true, H1689_cp2.1, H1689_cp2.2)) 1689 845 true) = true := by
  decide +kernel
theorem H1689_ok : RunOK pH1689 1689 (runFrom pH1689 (fmask pH1689) (cmask pH1689) (hmask pH1689) 1379 310 (true, H1689_cp2.1, H1689_cp2.2)) ∧ ptTest pH1689 (runFrom pH1689 (fmask pH1689) (cmask pH1689) (hmask pH1689) 1379 310 (true, H1689_cp2.1, H1689_cp2.2)) 1689 845 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1689_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1689_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1689_fin) true) H1689_seg1) H1689_seg2) (by decide) rfl H1689_fin ptTest_fst
noncomputable def I1689_cp1 : Nat × Nat := t7val% (fastRun pI1689 1 1193 (init pI1689) (init pI1689))
theorem I1689_seg1 : segOK pI1689 1 1193 (init pI1689) (init pI1689) I1689_cp1.1 I1689_cp1.2 = true := by
  decide +kernel
theorem I1689_fin : (prmOK pI1689 1689 && intTest pI1689 (runFrom pI1689 (fmask pI1689) (cmask pI1689) (hmask pI1689) 1194 495 (true, I1689_cp1.1, I1689_cp1.2)) 1689 21 false) = true := by
  decide +kernel
theorem I1689_ok : RunOK pI1689 1689 (runFrom pI1689 (fmask pI1689) (cmask pI1689) (hmask pI1689) 1194 495 (true, I1689_cp1.1, I1689_cp1.2)) ∧ intTest pI1689 (runFrom pI1689 (fmask pI1689) (cmask pI1689) (hmask pI1689) 1194 495 (true, I1689_cp1.1, I1689_cp1.2)) 1689 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1689_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1689_fin) true) I1689_seg1) (by decide) rfl I1689_fin intTest_fst
theorem link1689 : linkOK pL1689 pH1689 pI1689 = true := by decide +kernel
theorem cvx1689 : ConvexBetweenHumps 1689 :=
  cvx_of L1689_ok H1689_ok I1689_ok link1689 (by decide)

/-! ### `N = 1690` -/

def pL1690 : Prm := ⟨80, 37, 40, 1692, 11, 18446744073709551616, 112903770063999618, 112903770063999618⟩
def pH1690 : Prm := ⟨80, 37, 40, 1692, 11, 18446744073709551616, 112904869575627394, 112904869575627394⟩
def pI1690 : Prm := ⟨68, 33, 32, 1692, 11, 18446744073709551616, 112903770063999618, 112904869575627394⟩
noncomputable def L1690_cp1 : Nat × Nat := t7val% (fastRun pL1690 1 975 (init pL1690) (init pL1690))
theorem L1690_seg1 : segOK pL1690 1 975 (init pL1690) (init pL1690) L1690_cp1.1 L1690_cp1.2 = true := by
  decide +kernel
noncomputable def L1690_cp2 : Nat × Nat := t7val% (fastRun pL1690 1 1379 (init pL1690) (init pL1690))
theorem L1690_seg2 : segOK pL1690 976 404 L1690_cp1.1 L1690_cp1.2 L1690_cp2.1 L1690_cp2.2 = true := by
  decide +kernel
theorem L1690_fin : (prmOK pL1690 1690 && ptTest pL1690 (runFrom pL1690 (fmask pL1690) (cmask pL1690) (hmask pL1690) 1380 310 (true, L1690_cp2.1, L1690_cp2.2)) 1690 845 false) = true := by
  decide +kernel
theorem L1690_ok : RunOK pL1690 1690 (runFrom pL1690 (fmask pL1690) (cmask pL1690) (hmask pL1690) 1380 310 (true, L1690_cp2.1, L1690_cp2.2)) ∧ ptTest pL1690 (runFrom pL1690 (fmask pL1690) (cmask pL1690) (hmask pL1690) 1380 310 (true, L1690_cp2.1, L1690_cp2.2)) 1690 845 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1690_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1690_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1690_fin) true) L1690_seg1) L1690_seg2) (by decide) rfl L1690_fin ptTest_fst
noncomputable def H1690_cp1 : Nat × Nat := t7val% (fastRun pH1690 1 975 (init pH1690) (init pH1690))
theorem H1690_seg1 : segOK pH1690 1 975 (init pH1690) (init pH1690) H1690_cp1.1 H1690_cp1.2 = true := by
  decide +kernel
noncomputable def H1690_cp2 : Nat × Nat := t7val% (fastRun pH1690 1 1379 (init pH1690) (init pH1690))
theorem H1690_seg2 : segOK pH1690 976 404 H1690_cp1.1 H1690_cp1.2 H1690_cp2.1 H1690_cp2.2 = true := by
  decide +kernel
theorem H1690_fin : (prmOK pH1690 1690 && ptTest pH1690 (runFrom pH1690 (fmask pH1690) (cmask pH1690) (hmask pH1690) 1380 310 (true, H1690_cp2.1, H1690_cp2.2)) 1690 845 true) = true := by
  decide +kernel
theorem H1690_ok : RunOK pH1690 1690 (runFrom pH1690 (fmask pH1690) (cmask pH1690) (hmask pH1690) 1380 310 (true, H1690_cp2.1, H1690_cp2.2)) ∧ ptTest pH1690 (runFrom pH1690 (fmask pH1690) (cmask pH1690) (hmask pH1690) 1380 310 (true, H1690_cp2.1, H1690_cp2.2)) 1690 845 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1690_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1690_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1690_fin) true) H1690_seg1) H1690_seg2) (by decide) rfl H1690_fin ptTest_fst
noncomputable def I1690_cp1 : Nat × Nat := t7val% (fastRun pI1690 1 1194 (init pI1690) (init pI1690))
theorem I1690_seg1 : segOK pI1690 1 1194 (init pI1690) (init pI1690) I1690_cp1.1 I1690_cp1.2 = true := by
  decide +kernel
theorem I1690_fin : (prmOK pI1690 1690 && intTest pI1690 (runFrom pI1690 (fmask pI1690) (cmask pI1690) (hmask pI1690) 1195 495 (true, I1690_cp1.1, I1690_cp1.2)) 1690 21 true) = true := by
  decide +kernel
theorem I1690_ok : RunOK pI1690 1690 (runFrom pI1690 (fmask pI1690) (cmask pI1690) (hmask pI1690) 1195 495 (true, I1690_cp1.1, I1690_cp1.2)) ∧ intTest pI1690 (runFrom pI1690 (fmask pI1690) (cmask pI1690) (hmask pI1690) 1195 495 (true, I1690_cp1.1, I1690_cp1.2)) 1690 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1690_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1690_fin) true) I1690_seg1) (by decide) rfl I1690_fin intTest_fst
theorem link1690 : linkOK pL1690 pH1690 pI1690 = true := by decide +kernel
theorem cvx1690 : ConvexBetweenHumps 1690 :=
  cvx_of L1690_ok H1690_ok I1690_ok link1690 (by decide)
theorem cenlink1690 : cenLinkOK pI1690 1690 = true := by decide +kernel
theorem cen1690 : CenterUniqueMin 1690 ∧ DipHyp 1690 ∧ OnePointHyps 1690 :=
  cen_of L1690_ok H1690_ok I1690_ok link1690 cenlink1690

/-! ### `N = 1691` -/

def pL1691 : Prm := ⟨80, 37, 40, 1693, 11, 18446744073709551616, 112849156140192163, 112849156140192163⟩
def pH1691 : Prm := ⟨80, 37, 40, 1693, 11, 18446744073709551616, 112850255651819939, 112850255651819939⟩
def pI1691 : Prm := ⟨68, 33, 32, 1693, 11, 18446744073709551616, 112849156140192163, 112850255651819939⟩
noncomputable def L1691_cp1 : Nat × Nat := t7val% (fastRun pL1691 1 975 (init pL1691) (init pL1691))
theorem L1691_seg1 : segOK pL1691 1 975 (init pL1691) (init pL1691) L1691_cp1.1 L1691_cp1.2 = true := by
  decide +kernel
noncomputable def L1691_cp2 : Nat × Nat := t7val% (fastRun pL1691 1 1380 (init pL1691) (init pL1691))
theorem L1691_seg2 : segOK pL1691 976 405 L1691_cp1.1 L1691_cp1.2 L1691_cp2.1 L1691_cp2.2 = true := by
  decide +kernel
theorem L1691_fin : (prmOK pL1691 1691 && ptTest pL1691 (runFrom pL1691 (fmask pL1691) (cmask pL1691) (hmask pL1691) 1381 310 (true, L1691_cp2.1, L1691_cp2.2)) 1691 846 false) = true := by
  decide +kernel
theorem L1691_ok : RunOK pL1691 1691 (runFrom pL1691 (fmask pL1691) (cmask pL1691) (hmask pL1691) 1381 310 (true, L1691_cp2.1, L1691_cp2.2)) ∧ ptTest pL1691 (runFrom pL1691 (fmask pL1691) (cmask pL1691) (hmask pL1691) 1381 310 (true, L1691_cp2.1, L1691_cp2.2)) 1691 846 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1691_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1691_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1691_fin) true) L1691_seg1) L1691_seg2) (by decide) rfl L1691_fin ptTest_fst
noncomputable def H1691_cp1 : Nat × Nat := t7val% (fastRun pH1691 1 975 (init pH1691) (init pH1691))
theorem H1691_seg1 : segOK pH1691 1 975 (init pH1691) (init pH1691) H1691_cp1.1 H1691_cp1.2 = true := by
  decide +kernel
noncomputable def H1691_cp2 : Nat × Nat := t7val% (fastRun pH1691 1 1380 (init pH1691) (init pH1691))
theorem H1691_seg2 : segOK pH1691 976 405 H1691_cp1.1 H1691_cp1.2 H1691_cp2.1 H1691_cp2.2 = true := by
  decide +kernel
theorem H1691_fin : (prmOK pH1691 1691 && ptTest pH1691 (runFrom pH1691 (fmask pH1691) (cmask pH1691) (hmask pH1691) 1381 310 (true, H1691_cp2.1, H1691_cp2.2)) 1691 846 true) = true := by
  decide +kernel
theorem H1691_ok : RunOK pH1691 1691 (runFrom pH1691 (fmask pH1691) (cmask pH1691) (hmask pH1691) 1381 310 (true, H1691_cp2.1, H1691_cp2.2)) ∧ ptTest pH1691 (runFrom pH1691 (fmask pH1691) (cmask pH1691) (hmask pH1691) 1381 310 (true, H1691_cp2.1, H1691_cp2.2)) 1691 846 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1691_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1691_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1691_fin) true) H1691_seg1) H1691_seg2) (by decide) rfl H1691_fin ptTest_fst
noncomputable def I1691_cp1 : Nat × Nat := t7val% (fastRun pI1691 1 1195 (init pI1691) (init pI1691))
theorem I1691_seg1 : segOK pI1691 1 1195 (init pI1691) (init pI1691) I1691_cp1.1 I1691_cp1.2 = true := by
  decide +kernel
theorem I1691_fin : (prmOK pI1691 1691 && intTest pI1691 (runFrom pI1691 (fmask pI1691) (cmask pI1691) (hmask pI1691) 1196 495 (true, I1691_cp1.1, I1691_cp1.2)) 1691 21 false) = true := by
  decide +kernel
theorem I1691_ok : RunOK pI1691 1691 (runFrom pI1691 (fmask pI1691) (cmask pI1691) (hmask pI1691) 1196 495 (true, I1691_cp1.1, I1691_cp1.2)) ∧ intTest pI1691 (runFrom pI1691 (fmask pI1691) (cmask pI1691) (hmask pI1691) 1196 495 (true, I1691_cp1.1, I1691_cp1.2)) 1691 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1691_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1691_fin) true) I1691_seg1) (by decide) rfl I1691_fin intTest_fst
theorem link1691 : linkOK pL1691 pH1691 pI1691 = true := by decide +kernel
theorem cvx1691 : ConvexBetweenHumps 1691 :=
  cvx_of L1691_ok H1691_ok I1691_ok link1691 (by decide)

/-! ### `N = 1692` -/

def pL1692 : Prm := ⟨80, 37, 40, 1694, 11, 18446744073709551616, 112794622838359298, 112794622838359298⟩
def pH1692 : Prm := ⟨80, 37, 40, 1694, 11, 18446744073709551616, 112795722349987074, 112795722349987074⟩
def pI1692 : Prm := ⟨68, 33, 32, 1694, 11, 18446744073709551616, 112794622838359298, 112795722349987074⟩
noncomputable def L1692_cp1 : Nat × Nat := t7val% (fastRun pL1692 1 976 (init pL1692) (init pL1692))
theorem L1692_seg1 : segOK pL1692 1 976 (init pL1692) (init pL1692) L1692_cp1.1 L1692_cp1.2 = true := by
  decide +kernel
noncomputable def L1692_cp2 : Nat × Nat := t7val% (fastRun pL1692 1 1381 (init pL1692) (init pL1692))
theorem L1692_seg2 : segOK pL1692 977 405 L1692_cp1.1 L1692_cp1.2 L1692_cp2.1 L1692_cp2.2 = true := by
  decide +kernel
theorem L1692_fin : (prmOK pL1692 1692 && ptTest pL1692 (runFrom pL1692 (fmask pL1692) (cmask pL1692) (hmask pL1692) 1382 310 (true, L1692_cp2.1, L1692_cp2.2)) 1692 846 false) = true := by
  decide +kernel
theorem L1692_ok : RunOK pL1692 1692 (runFrom pL1692 (fmask pL1692) (cmask pL1692) (hmask pL1692) 1382 310 (true, L1692_cp2.1, L1692_cp2.2)) ∧ ptTest pL1692 (runFrom pL1692 (fmask pL1692) (cmask pL1692) (hmask pL1692) 1382 310 (true, L1692_cp2.1, L1692_cp2.2)) 1692 846 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1692_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1692_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1692_fin) true) L1692_seg1) L1692_seg2) (by decide) rfl L1692_fin ptTest_fst
noncomputable def H1692_cp1 : Nat × Nat := t7val% (fastRun pH1692 1 976 (init pH1692) (init pH1692))
theorem H1692_seg1 : segOK pH1692 1 976 (init pH1692) (init pH1692) H1692_cp1.1 H1692_cp1.2 = true := by
  decide +kernel
noncomputable def H1692_cp2 : Nat × Nat := t7val% (fastRun pH1692 1 1381 (init pH1692) (init pH1692))
theorem H1692_seg2 : segOK pH1692 977 405 H1692_cp1.1 H1692_cp1.2 H1692_cp2.1 H1692_cp2.2 = true := by
  decide +kernel
theorem H1692_fin : (prmOK pH1692 1692 && ptTest pH1692 (runFrom pH1692 (fmask pH1692) (cmask pH1692) (hmask pH1692) 1382 310 (true, H1692_cp2.1, H1692_cp2.2)) 1692 846 true) = true := by
  decide +kernel
theorem H1692_ok : RunOK pH1692 1692 (runFrom pH1692 (fmask pH1692) (cmask pH1692) (hmask pH1692) 1382 310 (true, H1692_cp2.1, H1692_cp2.2)) ∧ ptTest pH1692 (runFrom pH1692 (fmask pH1692) (cmask pH1692) (hmask pH1692) 1382 310 (true, H1692_cp2.1, H1692_cp2.2)) 1692 846 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1692_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1692_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1692_fin) true) H1692_seg1) H1692_seg2) (by decide) rfl H1692_fin ptTest_fst
noncomputable def I1692_cp1 : Nat × Nat := t7val% (fastRun pI1692 1 1195 (init pI1692) (init pI1692))
theorem I1692_seg1 : segOK pI1692 1 1195 (init pI1692) (init pI1692) I1692_cp1.1 I1692_cp1.2 = true := by
  decide +kernel
theorem I1692_fin : (prmOK pI1692 1692 && intTest pI1692 (runFrom pI1692 (fmask pI1692) (cmask pI1692) (hmask pI1692) 1196 496 (true, I1692_cp1.1, I1692_cp1.2)) 1692 21 true) = true := by
  decide +kernel
theorem I1692_ok : RunOK pI1692 1692 (runFrom pI1692 (fmask pI1692) (cmask pI1692) (hmask pI1692) 1196 496 (true, I1692_cp1.1, I1692_cp1.2)) ∧ intTest pI1692 (runFrom pI1692 (fmask pI1692) (cmask pI1692) (hmask pI1692) 1196 496 (true, I1692_cp1.1, I1692_cp1.2)) 1692 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1692_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1692_fin) true) I1692_seg1) (by decide) rfl I1692_fin intTest_fst
theorem link1692 : linkOK pL1692 pH1692 pI1692 = true := by decide +kernel
theorem cvx1692 : ConvexBetweenHumps 1692 :=
  cvx_of L1692_ok H1692_ok I1692_ok link1692 (by decide)
theorem cenlink1692 : cenLinkOK pI1692 1692 = true := by decide +kernel
theorem cen1692 : CenterUniqueMin 1692 ∧ DipHyp 1692 ∧ OnePointHyps 1692 :=
  cen_of L1692_ok H1692_ok I1692_ok link1692 cenlink1692

/-! ### `N = 1693` -/

def pL1693 : Prm := ⟨80, 37, 40, 1695, 11, 18446744073709551616, 112740123552156485, 112740123552156485⟩
def pH1693 : Prm := ⟨80, 37, 40, 1695, 11, 18446744073709551616, 112741223063784261, 112741223063784261⟩
def pI1693 : Prm := ⟨68, 33, 32, 1695, 11, 18446744073709551616, 112740123552156485, 112741223063784261⟩
noncomputable def L1693_cp1 : Nat × Nat := t7val% (fastRun pL1693 1 976 (init pL1693) (init pL1693))
theorem L1693_seg1 : segOK pL1693 1 976 (init pL1693) (init pL1693) L1693_cp1.1 L1693_cp1.2 = true := by
  decide +kernel
noncomputable def L1693_cp2 : Nat × Nat := t7val% (fastRun pL1693 1 1381 (init pL1693) (init pL1693))
theorem L1693_seg2 : segOK pL1693 977 405 L1693_cp1.1 L1693_cp1.2 L1693_cp2.1 L1693_cp2.2 = true := by
  decide +kernel
theorem L1693_fin : (prmOK pL1693 1693 && ptTest pL1693 (runFrom pL1693 (fmask pL1693) (cmask pL1693) (hmask pL1693) 1382 311 (true, L1693_cp2.1, L1693_cp2.2)) 1693 847 false) = true := by
  decide +kernel
theorem L1693_ok : RunOK pL1693 1693 (runFrom pL1693 (fmask pL1693) (cmask pL1693) (hmask pL1693) 1382 311 (true, L1693_cp2.1, L1693_cp2.2)) ∧ ptTest pL1693 (runFrom pL1693 (fmask pL1693) (cmask pL1693) (hmask pL1693) 1382 311 (true, L1693_cp2.1, L1693_cp2.2)) 1693 847 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1693_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1693_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1693_fin) true) L1693_seg1) L1693_seg2) (by decide) rfl L1693_fin ptTest_fst
noncomputable def H1693_cp1 : Nat × Nat := t7val% (fastRun pH1693 1 976 (init pH1693) (init pH1693))
theorem H1693_seg1 : segOK pH1693 1 976 (init pH1693) (init pH1693) H1693_cp1.1 H1693_cp1.2 = true := by
  decide +kernel
noncomputable def H1693_cp2 : Nat × Nat := t7val% (fastRun pH1693 1 1381 (init pH1693) (init pH1693))
theorem H1693_seg2 : segOK pH1693 977 405 H1693_cp1.1 H1693_cp1.2 H1693_cp2.1 H1693_cp2.2 = true := by
  decide +kernel
theorem H1693_fin : (prmOK pH1693 1693 && ptTest pH1693 (runFrom pH1693 (fmask pH1693) (cmask pH1693) (hmask pH1693) 1382 311 (true, H1693_cp2.1, H1693_cp2.2)) 1693 847 true) = true := by
  decide +kernel
theorem H1693_ok : RunOK pH1693 1693 (runFrom pH1693 (fmask pH1693) (cmask pH1693) (hmask pH1693) 1382 311 (true, H1693_cp2.1, H1693_cp2.2)) ∧ ptTest pH1693 (runFrom pH1693 (fmask pH1693) (cmask pH1693) (hmask pH1693) 1382 311 (true, H1693_cp2.1, H1693_cp2.2)) 1693 847 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1693_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1693_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1693_fin) true) H1693_seg1) H1693_seg2) (by decide) rfl H1693_fin ptTest_fst
noncomputable def I1693_cp1 : Nat × Nat := t7val% (fastRun pI1693 1 1196 (init pI1693) (init pI1693))
theorem I1693_seg1 : segOK pI1693 1 1196 (init pI1693) (init pI1693) I1693_cp1.1 I1693_cp1.2 = true := by
  decide +kernel
theorem I1693_fin : (prmOK pI1693 1693 && intTest pI1693 (runFrom pI1693 (fmask pI1693) (cmask pI1693) (hmask pI1693) 1197 496 (true, I1693_cp1.1, I1693_cp1.2)) 1693 21 false) = true := by
  decide +kernel
theorem I1693_ok : RunOK pI1693 1693 (runFrom pI1693 (fmask pI1693) (cmask pI1693) (hmask pI1693) 1197 496 (true, I1693_cp1.1, I1693_cp1.2)) ∧ intTest pI1693 (runFrom pI1693 (fmask pI1693) (cmask pI1693) (hmask pI1693) 1197 496 (true, I1693_cp1.1, I1693_cp1.2)) 1693 21 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1693_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1693_fin) true) I1693_seg1) (by decide) rfl I1693_fin intTest_fst
theorem link1693 : linkOK pL1693 pH1693 pI1693 = true := by decide +kernel
theorem cvx1693 : ConvexBetweenHumps 1693 :=
  cvx_of L1693_ok H1693_ok I1693_ok link1693 (by decide)

/-! ### `N = 1694` -/

def pL1694 : Prm := ⟨80, 37, 40, 1696, 11, 18446744073709551616, 112685704618255309, 112685704618255309⟩
def pH1694 : Prm := ⟨80, 37, 40, 1696, 11, 18446744073709551616, 112686804129883085, 112686804129883085⟩
def pI1694 : Prm := ⟨68, 33, 32, 1696, 11, 18446744073709551616, 112685704618255309, 112686804129883085⟩
noncomputable def L1694_cp1 : Nat × Nat := t7val% (fastRun pL1694 1 977 (init pL1694) (init pL1694))
theorem L1694_seg1 : segOK pL1694 1 977 (init pL1694) (init pL1694) L1694_cp1.1 L1694_cp1.2 = true := by
  decide +kernel
noncomputable def L1694_cp2 : Nat × Nat := t7val% (fastRun pL1694 1 1382 (init pL1694) (init pL1694))
theorem L1694_seg2 : segOK pL1694 978 405 L1694_cp1.1 L1694_cp1.2 L1694_cp2.1 L1694_cp2.2 = true := by
  decide +kernel
theorem L1694_fin : (prmOK pL1694 1694 && ptTest pL1694 (runFrom pL1694 (fmask pL1694) (cmask pL1694) (hmask pL1694) 1383 311 (true, L1694_cp2.1, L1694_cp2.2)) 1694 847 false) = true := by
  decide +kernel
theorem L1694_ok : RunOK pL1694 1694 (runFrom pL1694 (fmask pL1694) (cmask pL1694) (hmask pL1694) 1383 311 (true, L1694_cp2.1, L1694_cp2.2)) ∧ ptTest pL1694 (runFrom pL1694 (fmask pL1694) (cmask pL1694) (hmask pL1694) 1383 311 (true, L1694_cp2.1, L1694_cp2.2)) 1694 847 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1694_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1694_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1694_fin) true) L1694_seg1) L1694_seg2) (by decide) rfl L1694_fin ptTest_fst
noncomputable def H1694_cp1 : Nat × Nat := t7val% (fastRun pH1694 1 977 (init pH1694) (init pH1694))
theorem H1694_seg1 : segOK pH1694 1 977 (init pH1694) (init pH1694) H1694_cp1.1 H1694_cp1.2 = true := by
  decide +kernel
noncomputable def H1694_cp2 : Nat × Nat := t7val% (fastRun pH1694 1 1382 (init pH1694) (init pH1694))
theorem H1694_seg2 : segOK pH1694 978 405 H1694_cp1.1 H1694_cp1.2 H1694_cp2.1 H1694_cp2.2 = true := by
  decide +kernel
theorem H1694_fin : (prmOK pH1694 1694 && ptTest pH1694 (runFrom pH1694 (fmask pH1694) (cmask pH1694) (hmask pH1694) 1383 311 (true, H1694_cp2.1, H1694_cp2.2)) 1694 847 true) = true := by
  decide +kernel
theorem H1694_ok : RunOK pH1694 1694 (runFrom pH1694 (fmask pH1694) (cmask pH1694) (hmask pH1694) 1383 311 (true, H1694_cp2.1, H1694_cp2.2)) ∧ ptTest pH1694 (runFrom pH1694 (fmask pH1694) (cmask pH1694) (hmask pH1694) 1383 311 (true, H1694_cp2.1, H1694_cp2.2)) 1694 847 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1694_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1694_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1694_fin) true) H1694_seg1) H1694_seg2) (by decide) rfl H1694_fin ptTest_fst
noncomputable def I1694_cp1 : Nat × Nat := t7val% (fastRun pI1694 1 1197 (init pI1694) (init pI1694))
theorem I1694_seg1 : segOK pI1694 1 1197 (init pI1694) (init pI1694) I1694_cp1.1 I1694_cp1.2 = true := by
  decide +kernel
theorem I1694_fin : (prmOK pI1694 1694 && intTest pI1694 (runFrom pI1694 (fmask pI1694) (cmask pI1694) (hmask pI1694) 1198 496 (true, I1694_cp1.1, I1694_cp1.2)) 1694 21 true) = true := by
  decide +kernel
theorem I1694_ok : RunOK pI1694 1694 (runFrom pI1694 (fmask pI1694) (cmask pI1694) (hmask pI1694) 1198 496 (true, I1694_cp1.1, I1694_cp1.2)) ∧ intTest pI1694 (runFrom pI1694 (fmask pI1694) (cmask pI1694) (hmask pI1694) 1198 496 (true, I1694_cp1.1, I1694_cp1.2)) 1694 21 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1694_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1694_fin) true) I1694_seg1) (by decide) rfl I1694_fin intTest_fst
theorem link1694 : linkOK pL1694 pH1694 pI1694 = true := by decide +kernel
theorem cvx1694 : ConvexBetweenHumps 1694 :=
  cvx_of L1694_ok H1694_ok I1694_ok link1694 (by decide)
theorem cenlink1694 : cenLinkOK pI1694 1694 = true := by decide +kernel
theorem cen1694 : CenterUniqueMin 1694 ∧ DipHyp 1694 ∧ OnePointHyps 1694 :=
  cen_of L1694_ok H1694_ok I1694_ok link1694 cenlink1694

/-! ### The range -/

theorem cvx_1681_1694 {N : ℕ} (h1 : 1681 ≤ N) (h2 : N ≤ 1694) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1687
  · by_cases h4 : N ≤ 1683
    · by_cases h6 : N ≤ 1681
      · obtain rfl : N = 1681 := by omega
        exact cvx1681
      · by_cases h8 : N ≤ 1682
        · obtain rfl : N = 1682 := by omega
          exact cvx1682
        · obtain rfl : N = 1683 := by omega
          exact cvx1683
    · by_cases h6 : N ≤ 1685
      · by_cases h8 : N ≤ 1684
        · obtain rfl : N = 1684 := by omega
          exact cvx1684
        · obtain rfl : N = 1685 := by omega
          exact cvx1685
      · by_cases h8 : N ≤ 1686
        · obtain rfl : N = 1686 := by omega
          exact cvx1686
        · obtain rfl : N = 1687 := by omega
          exact cvx1687
  · by_cases h4 : N ≤ 1690
    · by_cases h6 : N ≤ 1688
      · obtain rfl : N = 1688 := by omega
        exact cvx1688
      · by_cases h8 : N ≤ 1689
        · obtain rfl : N = 1689 := by omega
          exact cvx1689
        · obtain rfl : N = 1690 := by omega
          exact cvx1690
    · by_cases h6 : N ≤ 1692
      · by_cases h8 : N ≤ 1691
        · obtain rfl : N = 1691 := by omega
          exact cvx1691
        · obtain rfl : N = 1692 := by omega
          exact cvx1692
      · by_cases h8 : N ≤ 1693
        · obtain rfl : N = 1693 := by omega
          exact cvx1693
        · obtain rfl : N = 1694 := by omega
          exact cvx1694

theorem cen_1681_1694 {N : ℕ} (h1 : 1681 ≤ N) (h2 : N ≤ 1694) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1686
  · by_cases h4 : N ≤ 1682
    · obtain rfl : N = 1682 := by omega
      exact cen1682
    · by_cases h6 : N ≤ 1684
      · obtain rfl : N = 1684 := by omega
        exact cen1684
      · obtain rfl : N = 1686 := by omega
        exact cen1686
  · by_cases h4 : N ≤ 1690
    · by_cases h6 : N ≤ 1688
      · obtain rfl : N = 1688 := by omega
        exact cen1688
      · obtain rfl : N = 1690 := by omega
        exact cen1690
    · by_cases h6 : N ≤ 1692
      · obtain rfl : N = 1692 := by omega
        exact cen1692
      · obtain rfl : N = 1694 := by omega
        exact cen1694

end Kagey131.PaperD.T7
