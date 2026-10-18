import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1909, …, 1919` (generated)

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

/-! ### `N = 1909` -/

def pL1909 : Prm := ⟨80, 37, 40, 1911, 11, 18446744073709551616, 102171017850836554, 102171017850836554⟩
def pH1909 : Prm := ⟨80, 37, 40, 1911, 11, 18446744073709551616, 102172117362464330, 102172117362464330⟩
def pI1909 : Prm := ⟨68, 34, 31, 1911, 11, 18446744073709551616, 102171017850836554, 102172117362464330⟩
noncomputable def L1909_cp1 : Nat × Nat := t7val% (fastRun pL1909 1 1101 (init pL1909) (init pL1909))
theorem L1909_seg1 : segOK pL1909 1 1101 (init pL1909) (init pL1909) L1909_cp1.1 L1909_cp1.2 = true := by
  decide +kernel
noncomputable def L1909_cp2 : Nat × Nat := t7val% (fastRun pL1909 1 1558 (init pL1909) (init pL1909))
theorem L1909_seg2 : segOK pL1909 1102 457 L1909_cp1.1 L1909_cp1.2 L1909_cp2.1 L1909_cp2.2 = true := by
  decide +kernel
theorem L1909_fin : (prmOK pL1909 1909 && ptTest pL1909 (runFrom pL1909 (fmask pL1909) (cmask pL1909) (hmask pL1909) 1559 350 (true, L1909_cp2.1, L1909_cp2.2)) 1909 955 false) = true := by
  decide +kernel
theorem L1909_ok : RunOK pL1909 1909 (runFrom pL1909 (fmask pL1909) (cmask pL1909) (hmask pL1909) 1559 350 (true, L1909_cp2.1, L1909_cp2.2)) ∧ ptTest pL1909 (runFrom pL1909 (fmask pL1909) (cmask pL1909) (hmask pL1909) 1559 350 (true, L1909_cp2.1, L1909_cp2.2)) 1909 955 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1909_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1909_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1909_fin) true) L1909_seg1) L1909_seg2) (by decide) rfl L1909_fin ptTest_fst
noncomputable def H1909_cp1 : Nat × Nat := t7val% (fastRun pH1909 1 1101 (init pH1909) (init pH1909))
theorem H1909_seg1 : segOK pH1909 1 1101 (init pH1909) (init pH1909) H1909_cp1.1 H1909_cp1.2 = true := by
  decide +kernel
noncomputable def H1909_cp2 : Nat × Nat := t7val% (fastRun pH1909 1 1558 (init pH1909) (init pH1909))
theorem H1909_seg2 : segOK pH1909 1102 457 H1909_cp1.1 H1909_cp1.2 H1909_cp2.1 H1909_cp2.2 = true := by
  decide +kernel
theorem H1909_fin : (prmOK pH1909 1909 && ptTest pH1909 (runFrom pH1909 (fmask pH1909) (cmask pH1909) (hmask pH1909) 1559 350 (true, H1909_cp2.1, H1909_cp2.2)) 1909 955 true) = true := by
  decide +kernel
theorem H1909_ok : RunOK pH1909 1909 (runFrom pH1909 (fmask pH1909) (cmask pH1909) (hmask pH1909) 1559 350 (true, H1909_cp2.1, H1909_cp2.2)) ∧ ptTest pH1909 (runFrom pH1909 (fmask pH1909) (cmask pH1909) (hmask pH1909) 1559 350 (true, H1909_cp2.1, H1909_cp2.2)) 1909 955 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1909_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1909_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1909_fin) true) H1909_seg1) H1909_seg2) (by decide) rfl H1909_fin ptTest_fst
noncomputable def I1909_cp1 : Nat × Nat := t7val% (fastRun pI1909 1 1101 (init pI1909) (init pI1909))
theorem I1909_seg1 : segOK pI1909 1 1101 (init pI1909) (init pI1909) I1909_cp1.1 I1909_cp1.2 = true := by
  decide +kernel
noncomputable def I1909_cp2 : Nat × Nat := t7val% (fastRun pI1909 1 1558 (init pI1909) (init pI1909))
theorem I1909_seg2 : segOK pI1909 1102 457 I1909_cp1.1 I1909_cp1.2 I1909_cp2.1 I1909_cp2.2 = true := by
  decide +kernel
theorem I1909_fin : (prmOK pI1909 1909 && intTest pI1909 (runFrom pI1909 (fmask pI1909) (cmask pI1909) (hmask pI1909) 1559 350 (true, I1909_cp2.1, I1909_cp2.2)) 1909 22 false) = true := by
  decide +kernel
theorem I1909_ok : RunOK pI1909 1909 (runFrom pI1909 (fmask pI1909) (cmask pI1909) (hmask pI1909) 1559 350 (true, I1909_cp2.1, I1909_cp2.2)) ∧ intTest pI1909 (runFrom pI1909 (fmask pI1909) (cmask pI1909) (hmask pI1909) 1559 350 (true, I1909_cp2.1, I1909_cp2.2)) 1909 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1909_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1909_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1909_fin) true) I1909_seg1) I1909_seg2) (by decide) rfl I1909_fin intTest_fst
theorem link1909 : linkOK pL1909 pH1909 pI1909 = true := by decide +kernel
theorem cvx1909 : ConvexBetweenHumps 1909 :=
  cvx_of L1909_ok H1909_ok I1909_ok link1909 (by decide)

/-! ### `N = 1910` -/

def pL1910 : Prm := ⟨80, 37, 40, 1912, 11, 18446744073709551616, 102127066699077875, 102127066699077875⟩
def pH1910 : Prm := ⟨80, 37, 40, 1912, 11, 18446744073709551616, 102128166210705651, 102128166210705651⟩
def pI1910 : Prm := ⟨68, 34, 31, 1912, 11, 18446744073709551616, 102127066699077875, 102128166210705651⟩
noncomputable def L1910_cp1 : Nat × Nat := t7val% (fastRun pL1910 1 1102 (init pL1910) (init pL1910))
theorem L1910_seg1 : segOK pL1910 1 1102 (init pL1910) (init pL1910) L1910_cp1.1 L1910_cp1.2 = true := by
  decide +kernel
noncomputable def L1910_cp2 : Nat × Nat := t7val% (fastRun pL1910 1 1559 (init pL1910) (init pL1910))
theorem L1910_seg2 : segOK pL1910 1103 457 L1910_cp1.1 L1910_cp1.2 L1910_cp2.1 L1910_cp2.2 = true := by
  decide +kernel
theorem L1910_fin : (prmOK pL1910 1910 && ptTest pL1910 (runFrom pL1910 (fmask pL1910) (cmask pL1910) (hmask pL1910) 1560 350 (true, L1910_cp2.1, L1910_cp2.2)) 1910 955 false) = true := by
  decide +kernel
theorem L1910_ok : RunOK pL1910 1910 (runFrom pL1910 (fmask pL1910) (cmask pL1910) (hmask pL1910) 1560 350 (true, L1910_cp2.1, L1910_cp2.2)) ∧ ptTest pL1910 (runFrom pL1910 (fmask pL1910) (cmask pL1910) (hmask pL1910) 1560 350 (true, L1910_cp2.1, L1910_cp2.2)) 1910 955 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1910_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1910_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1910_fin) true) L1910_seg1) L1910_seg2) (by decide) rfl L1910_fin ptTest_fst
noncomputable def H1910_cp1 : Nat × Nat := t7val% (fastRun pH1910 1 1102 (init pH1910) (init pH1910))
theorem H1910_seg1 : segOK pH1910 1 1102 (init pH1910) (init pH1910) H1910_cp1.1 H1910_cp1.2 = true := by
  decide +kernel
noncomputable def H1910_cp2 : Nat × Nat := t7val% (fastRun pH1910 1 1559 (init pH1910) (init pH1910))
theorem H1910_seg2 : segOK pH1910 1103 457 H1910_cp1.1 H1910_cp1.2 H1910_cp2.1 H1910_cp2.2 = true := by
  decide +kernel
theorem H1910_fin : (prmOK pH1910 1910 && ptTest pH1910 (runFrom pH1910 (fmask pH1910) (cmask pH1910) (hmask pH1910) 1560 350 (true, H1910_cp2.1, H1910_cp2.2)) 1910 955 true) = true := by
  decide +kernel
theorem H1910_ok : RunOK pH1910 1910 (runFrom pH1910 (fmask pH1910) (cmask pH1910) (hmask pH1910) 1560 350 (true, H1910_cp2.1, H1910_cp2.2)) ∧ ptTest pH1910 (runFrom pH1910 (fmask pH1910) (cmask pH1910) (hmask pH1910) 1560 350 (true, H1910_cp2.1, H1910_cp2.2)) 1910 955 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1910_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1910_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1910_fin) true) H1910_seg1) H1910_seg2) (by decide) rfl H1910_fin ptTest_fst
noncomputable def I1910_cp1 : Nat × Nat := t7val% (fastRun pI1910 1 1102 (init pI1910) (init pI1910))
theorem I1910_seg1 : segOK pI1910 1 1102 (init pI1910) (init pI1910) I1910_cp1.1 I1910_cp1.2 = true := by
  decide +kernel
noncomputable def I1910_cp2 : Nat × Nat := t7val% (fastRun pI1910 1 1559 (init pI1910) (init pI1910))
theorem I1910_seg2 : segOK pI1910 1103 457 I1910_cp1.1 I1910_cp1.2 I1910_cp2.1 I1910_cp2.2 = true := by
  decide +kernel
theorem I1910_fin : (prmOK pI1910 1910 && intTest pI1910 (runFrom pI1910 (fmask pI1910) (cmask pI1910) (hmask pI1910) 1560 350 (true, I1910_cp2.1, I1910_cp2.2)) 1910 22 true) = true := by
  decide +kernel
theorem I1910_ok : RunOK pI1910 1910 (runFrom pI1910 (fmask pI1910) (cmask pI1910) (hmask pI1910) 1560 350 (true, I1910_cp2.1, I1910_cp2.2)) ∧ intTest pI1910 (runFrom pI1910 (fmask pI1910) (cmask pI1910) (hmask pI1910) 1560 350 (true, I1910_cp2.1, I1910_cp2.2)) 1910 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1910_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1910_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1910_fin) true) I1910_seg1) I1910_seg2) (by decide) rfl I1910_fin intTest_fst
theorem link1910 : linkOK pL1910 pH1910 pI1910 = true := by decide +kernel
theorem cvx1910 : ConvexBetweenHumps 1910 :=
  cvx_of L1910_ok H1910_ok I1910_ok link1910 (by decide)
theorem cenlink1910 : cenLinkOK pI1910 1910 = true := by decide +kernel
theorem cen1910 : CenterUniqueMin 1910 ∧ DipHyp 1910 ∧ OnePointHyps 1910 :=
  cen_of L1910_ok H1910_ok I1910_ok link1910 cenlink1910

/-! ### `N = 1911` -/

def pL1911 : Prm := ⟨80, 37, 40, 1913, 11, 18446744073709551616, 102083140494806561, 102083140494806561⟩
def pH1911 : Prm := ⟨80, 37, 40, 1913, 11, 18446744073709551616, 102084240006434337, 102084240006434337⟩
def pI1911 : Prm := ⟨68, 34, 31, 1913, 11, 18446744073709551616, 102083140494806561, 102084240006434337⟩
noncomputable def L1911_cp1 : Nat × Nat := t7val% (fastRun pL1911 1 1102 (init pL1911) (init pL1911))
theorem L1911_seg1 : segOK pL1911 1 1102 (init pL1911) (init pL1911) L1911_cp1.1 L1911_cp1.2 = true := by
  decide +kernel
noncomputable def L1911_cp2 : Nat × Nat := t7val% (fastRun pL1911 1 1559 (init pL1911) (init pL1911))
theorem L1911_seg2 : segOK pL1911 1103 457 L1911_cp1.1 L1911_cp1.2 L1911_cp2.1 L1911_cp2.2 = true := by
  decide +kernel
theorem L1911_fin : (prmOK pL1911 1911 && ptTest pL1911 (runFrom pL1911 (fmask pL1911) (cmask pL1911) (hmask pL1911) 1560 351 (true, L1911_cp2.1, L1911_cp2.2)) 1911 956 false) = true := by
  decide +kernel
theorem L1911_ok : RunOK pL1911 1911 (runFrom pL1911 (fmask pL1911) (cmask pL1911) (hmask pL1911) 1560 351 (true, L1911_cp2.1, L1911_cp2.2)) ∧ ptTest pL1911 (runFrom pL1911 (fmask pL1911) (cmask pL1911) (hmask pL1911) 1560 351 (true, L1911_cp2.1, L1911_cp2.2)) 1911 956 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1911_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1911_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1911_fin) true) L1911_seg1) L1911_seg2) (by decide) rfl L1911_fin ptTest_fst
noncomputable def H1911_cp1 : Nat × Nat := t7val% (fastRun pH1911 1 1102 (init pH1911) (init pH1911))
theorem H1911_seg1 : segOK pH1911 1 1102 (init pH1911) (init pH1911) H1911_cp1.1 H1911_cp1.2 = true := by
  decide +kernel
noncomputable def H1911_cp2 : Nat × Nat := t7val% (fastRun pH1911 1 1559 (init pH1911) (init pH1911))
theorem H1911_seg2 : segOK pH1911 1103 457 H1911_cp1.1 H1911_cp1.2 H1911_cp2.1 H1911_cp2.2 = true := by
  decide +kernel
theorem H1911_fin : (prmOK pH1911 1911 && ptTest pH1911 (runFrom pH1911 (fmask pH1911) (cmask pH1911) (hmask pH1911) 1560 351 (true, H1911_cp2.1, H1911_cp2.2)) 1911 956 true) = true := by
  decide +kernel
theorem H1911_ok : RunOK pH1911 1911 (runFrom pH1911 (fmask pH1911) (cmask pH1911) (hmask pH1911) 1560 351 (true, H1911_cp2.1, H1911_cp2.2)) ∧ ptTest pH1911 (runFrom pH1911 (fmask pH1911) (cmask pH1911) (hmask pH1911) 1560 351 (true, H1911_cp2.1, H1911_cp2.2)) 1911 956 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1911_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1911_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1911_fin) true) H1911_seg1) H1911_seg2) (by decide) rfl H1911_fin ptTest_fst
noncomputable def I1911_cp1 : Nat × Nat := t7val% (fastRun pI1911 1 1102 (init pI1911) (init pI1911))
theorem I1911_seg1 : segOK pI1911 1 1102 (init pI1911) (init pI1911) I1911_cp1.1 I1911_cp1.2 = true := by
  decide +kernel
noncomputable def I1911_cp2 : Nat × Nat := t7val% (fastRun pI1911 1 1559 (init pI1911) (init pI1911))
theorem I1911_seg2 : segOK pI1911 1103 457 I1911_cp1.1 I1911_cp1.2 I1911_cp2.1 I1911_cp2.2 = true := by
  decide +kernel
theorem I1911_fin : (prmOK pI1911 1911 && intTest pI1911 (runFrom pI1911 (fmask pI1911) (cmask pI1911) (hmask pI1911) 1560 351 (true, I1911_cp2.1, I1911_cp2.2)) 1911 22 false) = true := by
  decide +kernel
theorem I1911_ok : RunOK pI1911 1911 (runFrom pI1911 (fmask pI1911) (cmask pI1911) (hmask pI1911) 1560 351 (true, I1911_cp2.1, I1911_cp2.2)) ∧ intTest pI1911 (runFrom pI1911 (fmask pI1911) (cmask pI1911) (hmask pI1911) 1560 351 (true, I1911_cp2.1, I1911_cp2.2)) 1911 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1911_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1911_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1911_fin) true) I1911_seg1) I1911_seg2) (by decide) rfl I1911_fin intTest_fst
theorem link1911 : linkOK pL1911 pH1911 pI1911 = true := by decide +kernel
theorem cvx1911 : ConvexBetweenHumps 1911 :=
  cvx_of L1911_ok H1911_ok I1911_ok link1911 (by decide)

/-! ### `N = 1912` -/

def pL1912 : Prm := ⟨80, 37, 40, 1914, 11, 18446744073709551616, 102039271282618061, 102039271282618061⟩
def pH1912 : Prm := ⟨80, 37, 40, 1914, 11, 18446744073709551616, 102040370794245837, 102040370794245837⟩
def pI1912 : Prm := ⟨68, 34, 31, 1914, 11, 18446744073709551616, 102039271282618061, 102040370794245837⟩
noncomputable def L1912_cp1 : Nat × Nat := t7val% (fastRun pL1912 1 1103 (init pL1912) (init pL1912))
theorem L1912_seg1 : segOK pL1912 1 1103 (init pL1912) (init pL1912) L1912_cp1.1 L1912_cp1.2 = true := by
  decide +kernel
noncomputable def L1912_cp2 : Nat × Nat := t7val% (fastRun pL1912 1 1560 (init pL1912) (init pL1912))
theorem L1912_seg2 : segOK pL1912 1104 457 L1912_cp1.1 L1912_cp1.2 L1912_cp2.1 L1912_cp2.2 = true := by
  decide +kernel
theorem L1912_fin : (prmOK pL1912 1912 && ptTest pL1912 (runFrom pL1912 (fmask pL1912) (cmask pL1912) (hmask pL1912) 1561 351 (true, L1912_cp2.1, L1912_cp2.2)) 1912 956 false) = true := by
  decide +kernel
theorem L1912_ok : RunOK pL1912 1912 (runFrom pL1912 (fmask pL1912) (cmask pL1912) (hmask pL1912) 1561 351 (true, L1912_cp2.1, L1912_cp2.2)) ∧ ptTest pL1912 (runFrom pL1912 (fmask pL1912) (cmask pL1912) (hmask pL1912) 1561 351 (true, L1912_cp2.1, L1912_cp2.2)) 1912 956 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1912_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1912_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1912_fin) true) L1912_seg1) L1912_seg2) (by decide) rfl L1912_fin ptTest_fst
noncomputable def H1912_cp1 : Nat × Nat := t7val% (fastRun pH1912 1 1103 (init pH1912) (init pH1912))
theorem H1912_seg1 : segOK pH1912 1 1103 (init pH1912) (init pH1912) H1912_cp1.1 H1912_cp1.2 = true := by
  decide +kernel
noncomputable def H1912_cp2 : Nat × Nat := t7val% (fastRun pH1912 1 1560 (init pH1912) (init pH1912))
theorem H1912_seg2 : segOK pH1912 1104 457 H1912_cp1.1 H1912_cp1.2 H1912_cp2.1 H1912_cp2.2 = true := by
  decide +kernel
theorem H1912_fin : (prmOK pH1912 1912 && ptTest pH1912 (runFrom pH1912 (fmask pH1912) (cmask pH1912) (hmask pH1912) 1561 351 (true, H1912_cp2.1, H1912_cp2.2)) 1912 956 true) = true := by
  decide +kernel
theorem H1912_ok : RunOK pH1912 1912 (runFrom pH1912 (fmask pH1912) (cmask pH1912) (hmask pH1912) 1561 351 (true, H1912_cp2.1, H1912_cp2.2)) ∧ ptTest pH1912 (runFrom pH1912 (fmask pH1912) (cmask pH1912) (hmask pH1912) 1561 351 (true, H1912_cp2.1, H1912_cp2.2)) 1912 956 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1912_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1912_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1912_fin) true) H1912_seg1) H1912_seg2) (by decide) rfl H1912_fin ptTest_fst
noncomputable def I1912_cp1 : Nat × Nat := t7val% (fastRun pI1912 1 1103 (init pI1912) (init pI1912))
theorem I1912_seg1 : segOK pI1912 1 1103 (init pI1912) (init pI1912) I1912_cp1.1 I1912_cp1.2 = true := by
  decide +kernel
noncomputable def I1912_cp2 : Nat × Nat := t7val% (fastRun pI1912 1 1560 (init pI1912) (init pI1912))
theorem I1912_seg2 : segOK pI1912 1104 457 I1912_cp1.1 I1912_cp1.2 I1912_cp2.1 I1912_cp2.2 = true := by
  decide +kernel
theorem I1912_fin : (prmOK pI1912 1912 && intTest pI1912 (runFrom pI1912 (fmask pI1912) (cmask pI1912) (hmask pI1912) 1561 351 (true, I1912_cp2.1, I1912_cp2.2)) 1912 22 true) = true := by
  decide +kernel
theorem I1912_ok : RunOK pI1912 1912 (runFrom pI1912 (fmask pI1912) (cmask pI1912) (hmask pI1912) 1561 351 (true, I1912_cp2.1, I1912_cp2.2)) ∧ intTest pI1912 (runFrom pI1912 (fmask pI1912) (cmask pI1912) (hmask pI1912) 1561 351 (true, I1912_cp2.1, I1912_cp2.2)) 1912 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1912_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1912_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1912_fin) true) I1912_seg1) I1912_seg2) (by decide) rfl I1912_fin intTest_fst
theorem link1912 : linkOK pL1912 pH1912 pI1912 = true := by decide +kernel
theorem cvx1912 : ConvexBetweenHumps 1912 :=
  cvx_of L1912_ok H1912_ok I1912_ok link1912 (by decide)
theorem cenlink1912 : cenLinkOK pI1912 1912 = true := by decide +kernel
theorem cen1912 : CenterUniqueMin 1912 ∧ DipHyp 1912 ∧ OnePointHyps 1912 :=
  cen_of L1912_ok H1912_ok I1912_ok link1912 cenlink1912

/-! ### `N = 1913` -/

def pL1913 : Prm := ⟨80, 37, 40, 1915, 11, 18446744073709551616, 101995426950899904, 101995426950899904⟩
def pH1913 : Prm := ⟨80, 37, 40, 1915, 11, 18446744073709551616, 101996526462527680, 101996526462527680⟩
def pI1913 : Prm := ⟨68, 34, 31, 1915, 11, 18446744073709551616, 101995426950899904, 101996526462527680⟩
noncomputable def L1913_cp1 : Nat × Nat := t7val% (fastRun pL1913 1 1103 (init pL1913) (init pL1913))
theorem L1913_seg1 : segOK pL1913 1 1103 (init pL1913) (init pL1913) L1913_cp1.1 L1913_cp1.2 = true := by
  decide +kernel
noncomputable def L1913_cp2 : Nat × Nat := t7val% (fastRun pL1913 1 1561 (init pL1913) (init pL1913))
theorem L1913_seg2 : segOK pL1913 1104 458 L1913_cp1.1 L1913_cp1.2 L1913_cp2.1 L1913_cp2.2 = true := by
  decide +kernel
theorem L1913_fin : (prmOK pL1913 1913 && ptTest pL1913 (runFrom pL1913 (fmask pL1913) (cmask pL1913) (hmask pL1913) 1562 351 (true, L1913_cp2.1, L1913_cp2.2)) 1913 957 false) = true := by
  decide +kernel
theorem L1913_ok : RunOK pL1913 1913 (runFrom pL1913 (fmask pL1913) (cmask pL1913) (hmask pL1913) 1562 351 (true, L1913_cp2.1, L1913_cp2.2)) ∧ ptTest pL1913 (runFrom pL1913 (fmask pL1913) (cmask pL1913) (hmask pL1913) 1562 351 (true, L1913_cp2.1, L1913_cp2.2)) 1913 957 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1913_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1913_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1913_fin) true) L1913_seg1) L1913_seg2) (by decide) rfl L1913_fin ptTest_fst
noncomputable def H1913_cp1 : Nat × Nat := t7val% (fastRun pH1913 1 1103 (init pH1913) (init pH1913))
theorem H1913_seg1 : segOK pH1913 1 1103 (init pH1913) (init pH1913) H1913_cp1.1 H1913_cp1.2 = true := by
  decide +kernel
noncomputable def H1913_cp2 : Nat × Nat := t7val% (fastRun pH1913 1 1561 (init pH1913) (init pH1913))
theorem H1913_seg2 : segOK pH1913 1104 458 H1913_cp1.1 H1913_cp1.2 H1913_cp2.1 H1913_cp2.2 = true := by
  decide +kernel
theorem H1913_fin : (prmOK pH1913 1913 && ptTest pH1913 (runFrom pH1913 (fmask pH1913) (cmask pH1913) (hmask pH1913) 1562 351 (true, H1913_cp2.1, H1913_cp2.2)) 1913 957 true) = true := by
  decide +kernel
theorem H1913_ok : RunOK pH1913 1913 (runFrom pH1913 (fmask pH1913) (cmask pH1913) (hmask pH1913) 1562 351 (true, H1913_cp2.1, H1913_cp2.2)) ∧ ptTest pH1913 (runFrom pH1913 (fmask pH1913) (cmask pH1913) (hmask pH1913) 1562 351 (true, H1913_cp2.1, H1913_cp2.2)) 1913 957 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1913_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1913_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1913_fin) true) H1913_seg1) H1913_seg2) (by decide) rfl H1913_fin ptTest_fst
noncomputable def I1913_cp1 : Nat × Nat := t7val% (fastRun pI1913 1 1103 (init pI1913) (init pI1913))
theorem I1913_seg1 : segOK pI1913 1 1103 (init pI1913) (init pI1913) I1913_cp1.1 I1913_cp1.2 = true := by
  decide +kernel
noncomputable def I1913_cp2 : Nat × Nat := t7val% (fastRun pI1913 1 1561 (init pI1913) (init pI1913))
theorem I1913_seg2 : segOK pI1913 1104 458 I1913_cp1.1 I1913_cp1.2 I1913_cp2.1 I1913_cp2.2 = true := by
  decide +kernel
theorem I1913_fin : (prmOK pI1913 1913 && intTest pI1913 (runFrom pI1913 (fmask pI1913) (cmask pI1913) (hmask pI1913) 1562 351 (true, I1913_cp2.1, I1913_cp2.2)) 1913 22 false) = true := by
  decide +kernel
theorem I1913_ok : RunOK pI1913 1913 (runFrom pI1913 (fmask pI1913) (cmask pI1913) (hmask pI1913) 1562 351 (true, I1913_cp2.1, I1913_cp2.2)) ∧ intTest pI1913 (runFrom pI1913 (fmask pI1913) (cmask pI1913) (hmask pI1913) 1562 351 (true, I1913_cp2.1, I1913_cp2.2)) 1913 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1913_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1913_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1913_fin) true) I1913_seg1) I1913_seg2) (by decide) rfl I1913_fin intTest_fst
theorem link1913 : linkOK pL1913 pH1913 pI1913 = true := by decide +kernel
theorem cvx1913 : ConvexBetweenHumps 1913 :=
  cvx_of L1913_ok H1913_ok I1913_ok link1913 (by decide)

/-! ### `N = 1914` -/

def pL1914 : Prm := ⟨80, 37, 40, 1916, 11, 18446744073709551616, 101951639442366172, 101951639442366172⟩
def pH1914 : Prm := ⟨80, 37, 40, 1916, 11, 18446744073709551616, 101952738953993948, 101952738953993948⟩
def pI1914 : Prm := ⟨68, 34, 31, 1916, 11, 18446744073709551616, 101951639442366172, 101952738953993948⟩
noncomputable def L1914_cp1 : Nat × Nat := t7val% (fastRun pL1914 1 1104 (init pL1914) (init pL1914))
theorem L1914_seg1 : segOK pL1914 1 1104 (init pL1914) (init pL1914) L1914_cp1.1 L1914_cp1.2 = true := by
  decide +kernel
noncomputable def L1914_cp2 : Nat × Nat := t7val% (fastRun pL1914 1 1562 (init pL1914) (init pL1914))
theorem L1914_seg2 : segOK pL1914 1105 458 L1914_cp1.1 L1914_cp1.2 L1914_cp2.1 L1914_cp2.2 = true := by
  decide +kernel
theorem L1914_fin : (prmOK pL1914 1914 && ptTest pL1914 (runFrom pL1914 (fmask pL1914) (cmask pL1914) (hmask pL1914) 1563 351 (true, L1914_cp2.1, L1914_cp2.2)) 1914 957 false) = true := by
  decide +kernel
theorem L1914_ok : RunOK pL1914 1914 (runFrom pL1914 (fmask pL1914) (cmask pL1914) (hmask pL1914) 1563 351 (true, L1914_cp2.1, L1914_cp2.2)) ∧ ptTest pL1914 (runFrom pL1914 (fmask pL1914) (cmask pL1914) (hmask pL1914) 1563 351 (true, L1914_cp2.1, L1914_cp2.2)) 1914 957 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1914_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1914_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1914_fin) true) L1914_seg1) L1914_seg2) (by decide) rfl L1914_fin ptTest_fst
noncomputable def H1914_cp1 : Nat × Nat := t7val% (fastRun pH1914 1 1104 (init pH1914) (init pH1914))
theorem H1914_seg1 : segOK pH1914 1 1104 (init pH1914) (init pH1914) H1914_cp1.1 H1914_cp1.2 = true := by
  decide +kernel
noncomputable def H1914_cp2 : Nat × Nat := t7val% (fastRun pH1914 1 1562 (init pH1914) (init pH1914))
theorem H1914_seg2 : segOK pH1914 1105 458 H1914_cp1.1 H1914_cp1.2 H1914_cp2.1 H1914_cp2.2 = true := by
  decide +kernel
theorem H1914_fin : (prmOK pH1914 1914 && ptTest pH1914 (runFrom pH1914 (fmask pH1914) (cmask pH1914) (hmask pH1914) 1563 351 (true, H1914_cp2.1, H1914_cp2.2)) 1914 957 true) = true := by
  decide +kernel
theorem H1914_ok : RunOK pH1914 1914 (runFrom pH1914 (fmask pH1914) (cmask pH1914) (hmask pH1914) 1563 351 (true, H1914_cp2.1, H1914_cp2.2)) ∧ ptTest pH1914 (runFrom pH1914 (fmask pH1914) (cmask pH1914) (hmask pH1914) 1563 351 (true, H1914_cp2.1, H1914_cp2.2)) 1914 957 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1914_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1914_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1914_fin) true) H1914_seg1) H1914_seg2) (by decide) rfl H1914_fin ptTest_fst
noncomputable def I1914_cp1 : Nat × Nat := t7val% (fastRun pI1914 1 1104 (init pI1914) (init pI1914))
theorem I1914_seg1 : segOK pI1914 1 1104 (init pI1914) (init pI1914) I1914_cp1.1 I1914_cp1.2 = true := by
  decide +kernel
noncomputable def I1914_cp2 : Nat × Nat := t7val% (fastRun pI1914 1 1562 (init pI1914) (init pI1914))
theorem I1914_seg2 : segOK pI1914 1105 458 I1914_cp1.1 I1914_cp1.2 I1914_cp2.1 I1914_cp2.2 = true := by
  decide +kernel
theorem I1914_fin : (prmOK pI1914 1914 && intTest pI1914 (runFrom pI1914 (fmask pI1914) (cmask pI1914) (hmask pI1914) 1563 351 (true, I1914_cp2.1, I1914_cp2.2)) 1914 22 true) = true := by
  decide +kernel
theorem I1914_ok : RunOK pI1914 1914 (runFrom pI1914 (fmask pI1914) (cmask pI1914) (hmask pI1914) 1563 351 (true, I1914_cp2.1, I1914_cp2.2)) ∧ intTest pI1914 (runFrom pI1914 (fmask pI1914) (cmask pI1914) (hmask pI1914) 1563 351 (true, I1914_cp2.1, I1914_cp2.2)) 1914 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1914_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1914_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1914_fin) true) I1914_seg1) I1914_seg2) (by decide) rfl I1914_fin intTest_fst
theorem link1914 : linkOK pL1914 pH1914 pI1914 = true := by decide +kernel
theorem cvx1914 : ConvexBetweenHumps 1914 :=
  cvx_of L1914_ok H1914_ok I1914_ok link1914 (by decide)
theorem cenlink1914 : cenLinkOK pI1914 1914 = true := by decide +kernel
theorem cen1914 : CenterUniqueMin 1914 ∧ DipHyp 1914 ∧ OnePointHyps 1914 :=
  cen_of L1914_ok H1914_ok I1914_ok link1914 cenlink1914

/-! ### `N = 1915` -/

def pL1915 : Prm := ⟨80, 37, 40, 1917, 11, 18446744073709551616, 101907876747488678, 101907876747488678⟩
def pH1915 : Prm := ⟨80, 37, 40, 1917, 11, 18446744073709551616, 101908976259116454, 101908976259116454⟩
def pI1915 : Prm := ⟨68, 34, 31, 1917, 11, 18446744073709551616, 101907876747488678, 101908976259116454⟩
noncomputable def L1915_cp1 : Nat × Nat := t7val% (fastRun pL1915 1 1105 (init pL1915) (init pL1915))
theorem L1915_seg1 : segOK pL1915 1 1105 (init pL1915) (init pL1915) L1915_cp1.1 L1915_cp1.2 = true := by
  decide +kernel
noncomputable def L1915_cp2 : Nat × Nat := t7val% (fastRun pL1915 1 1563 (init pL1915) (init pL1915))
theorem L1915_seg2 : segOK pL1915 1106 458 L1915_cp1.1 L1915_cp1.2 L1915_cp2.1 L1915_cp2.2 = true := by
  decide +kernel
theorem L1915_fin : (prmOK pL1915 1915 && ptTest pL1915 (runFrom pL1915 (fmask pL1915) (cmask pL1915) (hmask pL1915) 1564 351 (true, L1915_cp2.1, L1915_cp2.2)) 1915 958 false) = true := by
  decide +kernel
theorem L1915_ok : RunOK pL1915 1915 (runFrom pL1915 (fmask pL1915) (cmask pL1915) (hmask pL1915) 1564 351 (true, L1915_cp2.1, L1915_cp2.2)) ∧ ptTest pL1915 (runFrom pL1915 (fmask pL1915) (cmask pL1915) (hmask pL1915) 1564 351 (true, L1915_cp2.1, L1915_cp2.2)) 1915 958 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1915_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1915_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1915_fin) true) L1915_seg1) L1915_seg2) (by decide) rfl L1915_fin ptTest_fst
noncomputable def H1915_cp1 : Nat × Nat := t7val% (fastRun pH1915 1 1105 (init pH1915) (init pH1915))
theorem H1915_seg1 : segOK pH1915 1 1105 (init pH1915) (init pH1915) H1915_cp1.1 H1915_cp1.2 = true := by
  decide +kernel
noncomputable def H1915_cp2 : Nat × Nat := t7val% (fastRun pH1915 1 1563 (init pH1915) (init pH1915))
theorem H1915_seg2 : segOK pH1915 1106 458 H1915_cp1.1 H1915_cp1.2 H1915_cp2.1 H1915_cp2.2 = true := by
  decide +kernel
theorem H1915_fin : (prmOK pH1915 1915 && ptTest pH1915 (runFrom pH1915 (fmask pH1915) (cmask pH1915) (hmask pH1915) 1564 351 (true, H1915_cp2.1, H1915_cp2.2)) 1915 958 true) = true := by
  decide +kernel
theorem H1915_ok : RunOK pH1915 1915 (runFrom pH1915 (fmask pH1915) (cmask pH1915) (hmask pH1915) 1564 351 (true, H1915_cp2.1, H1915_cp2.2)) ∧ ptTest pH1915 (runFrom pH1915 (fmask pH1915) (cmask pH1915) (hmask pH1915) 1564 351 (true, H1915_cp2.1, H1915_cp2.2)) 1915 958 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1915_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1915_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1915_fin) true) H1915_seg1) H1915_seg2) (by decide) rfl H1915_fin ptTest_fst
noncomputable def I1915_cp1 : Nat × Nat := t7val% (fastRun pI1915 1 1105 (init pI1915) (init pI1915))
theorem I1915_seg1 : segOK pI1915 1 1105 (init pI1915) (init pI1915) I1915_cp1.1 I1915_cp1.2 = true := by
  decide +kernel
noncomputable def I1915_cp2 : Nat × Nat := t7val% (fastRun pI1915 1 1563 (init pI1915) (init pI1915))
theorem I1915_seg2 : segOK pI1915 1106 458 I1915_cp1.1 I1915_cp1.2 I1915_cp2.1 I1915_cp2.2 = true := by
  decide +kernel
theorem I1915_fin : (prmOK pI1915 1915 && intTest pI1915 (runFrom pI1915 (fmask pI1915) (cmask pI1915) (hmask pI1915) 1564 351 (true, I1915_cp2.1, I1915_cp2.2)) 1915 22 false) = true := by
  decide +kernel
theorem I1915_ok : RunOK pI1915 1915 (runFrom pI1915 (fmask pI1915) (cmask pI1915) (hmask pI1915) 1564 351 (true, I1915_cp2.1, I1915_cp2.2)) ∧ intTest pI1915 (runFrom pI1915 (fmask pI1915) (cmask pI1915) (hmask pI1915) 1564 351 (true, I1915_cp2.1, I1915_cp2.2)) 1915 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1915_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1915_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1915_fin) true) I1915_seg1) I1915_seg2) (by decide) rfl I1915_fin intTest_fst
theorem link1915 : linkOK pL1915 pH1915 pI1915 = true := by decide +kernel
theorem cvx1915 : ConvexBetweenHumps 1915 :=
  cvx_of L1915_ok H1915_ok I1915_ok link1915 (by decide)

/-! ### `N = 1916` -/

def pL1916 : Prm := ⟨80, 37, 40, 1918, 11, 18446744073709551616, 101864170707616641, 101864170707616641⟩
def pH1916 : Prm := ⟨80, 37, 40, 1918, 11, 18446744073709551616, 101865270219244417, 101865270219244417⟩
def pI1916 : Prm := ⟨68, 34, 31, 1918, 11, 18446744073709551616, 101864170707616641, 101865270219244417⟩
noncomputable def L1916_cp1 : Nat × Nat := t7val% (fastRun pL1916 1 1105 (init pL1916) (init pL1916))
theorem L1916_seg1 : segOK pL1916 1 1105 (init pL1916) (init pL1916) L1916_cp1.1 L1916_cp1.2 = true := by
  decide +kernel
noncomputable def L1916_cp2 : Nat × Nat := t7val% (fastRun pL1916 1 1563 (init pL1916) (init pL1916))
theorem L1916_seg2 : segOK pL1916 1106 458 L1916_cp1.1 L1916_cp1.2 L1916_cp2.1 L1916_cp2.2 = true := by
  decide +kernel
theorem L1916_fin : (prmOK pL1916 1916 && ptTest pL1916 (runFrom pL1916 (fmask pL1916) (cmask pL1916) (hmask pL1916) 1564 352 (true, L1916_cp2.1, L1916_cp2.2)) 1916 958 false) = true := by
  decide +kernel
theorem L1916_ok : RunOK pL1916 1916 (runFrom pL1916 (fmask pL1916) (cmask pL1916) (hmask pL1916) 1564 352 (true, L1916_cp2.1, L1916_cp2.2)) ∧ ptTest pL1916 (runFrom pL1916 (fmask pL1916) (cmask pL1916) (hmask pL1916) 1564 352 (true, L1916_cp2.1, L1916_cp2.2)) 1916 958 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1916_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1916_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1916_fin) true) L1916_seg1) L1916_seg2) (by decide) rfl L1916_fin ptTest_fst
noncomputable def H1916_cp1 : Nat × Nat := t7val% (fastRun pH1916 1 1105 (init pH1916) (init pH1916))
theorem H1916_seg1 : segOK pH1916 1 1105 (init pH1916) (init pH1916) H1916_cp1.1 H1916_cp1.2 = true := by
  decide +kernel
noncomputable def H1916_cp2 : Nat × Nat := t7val% (fastRun pH1916 1 1563 (init pH1916) (init pH1916))
theorem H1916_seg2 : segOK pH1916 1106 458 H1916_cp1.1 H1916_cp1.2 H1916_cp2.1 H1916_cp2.2 = true := by
  decide +kernel
theorem H1916_fin : (prmOK pH1916 1916 && ptTest pH1916 (runFrom pH1916 (fmask pH1916) (cmask pH1916) (hmask pH1916) 1564 352 (true, H1916_cp2.1, H1916_cp2.2)) 1916 958 true) = true := by
  decide +kernel
theorem H1916_ok : RunOK pH1916 1916 (runFrom pH1916 (fmask pH1916) (cmask pH1916) (hmask pH1916) 1564 352 (true, H1916_cp2.1, H1916_cp2.2)) ∧ ptTest pH1916 (runFrom pH1916 (fmask pH1916) (cmask pH1916) (hmask pH1916) 1564 352 (true, H1916_cp2.1, H1916_cp2.2)) 1916 958 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1916_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1916_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1916_fin) true) H1916_seg1) H1916_seg2) (by decide) rfl H1916_fin ptTest_fst
noncomputable def I1916_cp1 : Nat × Nat := t7val% (fastRun pI1916 1 1105 (init pI1916) (init pI1916))
theorem I1916_seg1 : segOK pI1916 1 1105 (init pI1916) (init pI1916) I1916_cp1.1 I1916_cp1.2 = true := by
  decide +kernel
noncomputable def I1916_cp2 : Nat × Nat := t7val% (fastRun pI1916 1 1563 (init pI1916) (init pI1916))
theorem I1916_seg2 : segOK pI1916 1106 458 I1916_cp1.1 I1916_cp1.2 I1916_cp2.1 I1916_cp2.2 = true := by
  decide +kernel
theorem I1916_fin : (prmOK pI1916 1916 && intTest pI1916 (runFrom pI1916 (fmask pI1916) (cmask pI1916) (hmask pI1916) 1564 352 (true, I1916_cp2.1, I1916_cp2.2)) 1916 22 true) = true := by
  decide +kernel
theorem I1916_ok : RunOK pI1916 1916 (runFrom pI1916 (fmask pI1916) (cmask pI1916) (hmask pI1916) 1564 352 (true, I1916_cp2.1, I1916_cp2.2)) ∧ intTest pI1916 (runFrom pI1916 (fmask pI1916) (cmask pI1916) (hmask pI1916) 1564 352 (true, I1916_cp2.1, I1916_cp2.2)) 1916 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1916_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1916_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1916_fin) true) I1916_seg1) I1916_seg2) (by decide) rfl I1916_fin intTest_fst
theorem link1916 : linkOK pL1916 pH1916 pI1916 = true := by decide +kernel
theorem cvx1916 : ConvexBetweenHumps 1916 :=
  cvx_of L1916_ok H1916_ok I1916_ok link1916 (by decide)
theorem cenlink1916 : cenLinkOK pI1916 1916 = true := by decide +kernel
theorem cen1916 : CenterUniqueMin 1916 ∧ DipHyp 1916 ∧ OnePointHyps 1916 :=
  cen_of L1916_ok H1916_ok I1916_ok link1916 cenlink1916

/-! ### `N = 1917` -/

def pL1917 : Prm := ⟨80, 37, 40, 1919, 11, 18446744073709551616, 101820489414844990, 101820489414844990⟩
def pH1917 : Prm := ⟨80, 37, 40, 1919, 11, 18446744073709551616, 101821588926472766, 101821588926472766⟩
def pI1917 : Prm := ⟨68, 34, 31, 1919, 11, 18446744073709551616, 101820489414844990, 101821588926472766⟩
noncomputable def L1917_cp1 : Nat × Nat := t7val% (fastRun pL1917 1 1106 (init pL1917) (init pL1917))
theorem L1917_seg1 : segOK pL1917 1 1106 (init pL1917) (init pL1917) L1917_cp1.1 L1917_cp1.2 = true := by
  decide +kernel
noncomputable def L1917_cp2 : Nat × Nat := t7val% (fastRun pL1917 1 1564 (init pL1917) (init pL1917))
theorem L1917_seg2 : segOK pL1917 1107 458 L1917_cp1.1 L1917_cp1.2 L1917_cp2.1 L1917_cp2.2 = true := by
  decide +kernel
theorem L1917_fin : (prmOK pL1917 1917 && ptTest pL1917 (runFrom pL1917 (fmask pL1917) (cmask pL1917) (hmask pL1917) 1565 352 (true, L1917_cp2.1, L1917_cp2.2)) 1917 959 false) = true := by
  decide +kernel
theorem L1917_ok : RunOK pL1917 1917 (runFrom pL1917 (fmask pL1917) (cmask pL1917) (hmask pL1917) 1565 352 (true, L1917_cp2.1, L1917_cp2.2)) ∧ ptTest pL1917 (runFrom pL1917 (fmask pL1917) (cmask pL1917) (hmask pL1917) 1565 352 (true, L1917_cp2.1, L1917_cp2.2)) 1917 959 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1917_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1917_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1917_fin) true) L1917_seg1) L1917_seg2) (by decide) rfl L1917_fin ptTest_fst
noncomputable def H1917_cp1 : Nat × Nat := t7val% (fastRun pH1917 1 1106 (init pH1917) (init pH1917))
theorem H1917_seg1 : segOK pH1917 1 1106 (init pH1917) (init pH1917) H1917_cp1.1 H1917_cp1.2 = true := by
  decide +kernel
noncomputable def H1917_cp2 : Nat × Nat := t7val% (fastRun pH1917 1 1564 (init pH1917) (init pH1917))
theorem H1917_seg2 : segOK pH1917 1107 458 H1917_cp1.1 H1917_cp1.2 H1917_cp2.1 H1917_cp2.2 = true := by
  decide +kernel
theorem H1917_fin : (prmOK pH1917 1917 && ptTest pH1917 (runFrom pH1917 (fmask pH1917) (cmask pH1917) (hmask pH1917) 1565 352 (true, H1917_cp2.1, H1917_cp2.2)) 1917 959 true) = true := by
  decide +kernel
theorem H1917_ok : RunOK pH1917 1917 (runFrom pH1917 (fmask pH1917) (cmask pH1917) (hmask pH1917) 1565 352 (true, H1917_cp2.1, H1917_cp2.2)) ∧ ptTest pH1917 (runFrom pH1917 (fmask pH1917) (cmask pH1917) (hmask pH1917) 1565 352 (true, H1917_cp2.1, H1917_cp2.2)) 1917 959 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1917_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1917_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1917_fin) true) H1917_seg1) H1917_seg2) (by decide) rfl H1917_fin ptTest_fst
noncomputable def I1917_cp1 : Nat × Nat := t7val% (fastRun pI1917 1 1106 (init pI1917) (init pI1917))
theorem I1917_seg1 : segOK pI1917 1 1106 (init pI1917) (init pI1917) I1917_cp1.1 I1917_cp1.2 = true := by
  decide +kernel
noncomputable def I1917_cp2 : Nat × Nat := t7val% (fastRun pI1917 1 1564 (init pI1917) (init pI1917))
theorem I1917_seg2 : segOK pI1917 1107 458 I1917_cp1.1 I1917_cp1.2 I1917_cp2.1 I1917_cp2.2 = true := by
  decide +kernel
theorem I1917_fin : (prmOK pI1917 1917 && intTest pI1917 (runFrom pI1917 (fmask pI1917) (cmask pI1917) (hmask pI1917) 1565 352 (true, I1917_cp2.1, I1917_cp2.2)) 1917 22 false) = true := by
  decide +kernel
theorem I1917_ok : RunOK pI1917 1917 (runFrom pI1917 (fmask pI1917) (cmask pI1917) (hmask pI1917) 1565 352 (true, I1917_cp2.1, I1917_cp2.2)) ∧ intTest pI1917 (runFrom pI1917 (fmask pI1917) (cmask pI1917) (hmask pI1917) 1565 352 (true, I1917_cp2.1, I1917_cp2.2)) 1917 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1917_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1917_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1917_fin) true) I1917_seg1) I1917_seg2) (by decide) rfl I1917_fin intTest_fst
theorem link1917 : linkOK pL1917 pH1917 pI1917 = true := by decide +kernel
theorem cvx1917 : ConvexBetweenHumps 1917 :=
  cvx_of L1917_ok H1917_ok I1917_ok link1917 (by decide)

/-! ### `N = 1918` -/

def pL1918 : Prm := ⟨80, 37, 40, 1920, 11, 18446744073709551616, 101776864609508573, 101776864609508573⟩
def pH1918 : Prm := ⟨80, 37, 40, 1920, 11, 18446744073709551616, 101777964121136349, 101777964121136349⟩
def pI1918 : Prm := ⟨68, 34, 31, 1920, 11, 18446744073709551616, 101776864609508573, 101777964121136349⟩
noncomputable def L1918_cp1 : Nat × Nat := t7val% (fastRun pL1918 1 1106 (init pL1918) (init pL1918))
theorem L1918_seg1 : segOK pL1918 1 1106 (init pL1918) (init pL1918) L1918_cp1.1 L1918_cp1.2 = true := by
  decide +kernel
noncomputable def L1918_cp2 : Nat × Nat := t7val% (fastRun pL1918 1 1565 (init pL1918) (init pL1918))
theorem L1918_seg2 : segOK pL1918 1107 459 L1918_cp1.1 L1918_cp1.2 L1918_cp2.1 L1918_cp2.2 = true := by
  decide +kernel
theorem L1918_fin : (prmOK pL1918 1918 && ptTest pL1918 (runFrom pL1918 (fmask pL1918) (cmask pL1918) (hmask pL1918) 1566 352 (true, L1918_cp2.1, L1918_cp2.2)) 1918 959 false) = true := by
  decide +kernel
theorem L1918_ok : RunOK pL1918 1918 (runFrom pL1918 (fmask pL1918) (cmask pL1918) (hmask pL1918) 1566 352 (true, L1918_cp2.1, L1918_cp2.2)) ∧ ptTest pL1918 (runFrom pL1918 (fmask pL1918) (cmask pL1918) (hmask pL1918) 1566 352 (true, L1918_cp2.1, L1918_cp2.2)) 1918 959 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1918_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1918_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1918_fin) true) L1918_seg1) L1918_seg2) (by decide) rfl L1918_fin ptTest_fst
noncomputable def H1918_cp1 : Nat × Nat := t7val% (fastRun pH1918 1 1106 (init pH1918) (init pH1918))
theorem H1918_seg1 : segOK pH1918 1 1106 (init pH1918) (init pH1918) H1918_cp1.1 H1918_cp1.2 = true := by
  decide +kernel
noncomputable def H1918_cp2 : Nat × Nat := t7val% (fastRun pH1918 1 1565 (init pH1918) (init pH1918))
theorem H1918_seg2 : segOK pH1918 1107 459 H1918_cp1.1 H1918_cp1.2 H1918_cp2.1 H1918_cp2.2 = true := by
  decide +kernel
theorem H1918_fin : (prmOK pH1918 1918 && ptTest pH1918 (runFrom pH1918 (fmask pH1918) (cmask pH1918) (hmask pH1918) 1566 352 (true, H1918_cp2.1, H1918_cp2.2)) 1918 959 true) = true := by
  decide +kernel
theorem H1918_ok : RunOK pH1918 1918 (runFrom pH1918 (fmask pH1918) (cmask pH1918) (hmask pH1918) 1566 352 (true, H1918_cp2.1, H1918_cp2.2)) ∧ ptTest pH1918 (runFrom pH1918 (fmask pH1918) (cmask pH1918) (hmask pH1918) 1566 352 (true, H1918_cp2.1, H1918_cp2.2)) 1918 959 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1918_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1918_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1918_fin) true) H1918_seg1) H1918_seg2) (by decide) rfl H1918_fin ptTest_fst
noncomputable def I1918_cp1 : Nat × Nat := t7val% (fastRun pI1918 1 1106 (init pI1918) (init pI1918))
theorem I1918_seg1 : segOK pI1918 1 1106 (init pI1918) (init pI1918) I1918_cp1.1 I1918_cp1.2 = true := by
  decide +kernel
noncomputable def I1918_cp2 : Nat × Nat := t7val% (fastRun pI1918 1 1565 (init pI1918) (init pI1918))
theorem I1918_seg2 : segOK pI1918 1107 459 I1918_cp1.1 I1918_cp1.2 I1918_cp2.1 I1918_cp2.2 = true := by
  decide +kernel
theorem I1918_fin : (prmOK pI1918 1918 && intTest pI1918 (runFrom pI1918 (fmask pI1918) (cmask pI1918) (hmask pI1918) 1566 352 (true, I1918_cp2.1, I1918_cp2.2)) 1918 22 true) = true := by
  decide +kernel
theorem I1918_ok : RunOK pI1918 1918 (runFrom pI1918 (fmask pI1918) (cmask pI1918) (hmask pI1918) 1566 352 (true, I1918_cp2.1, I1918_cp2.2)) ∧ intTest pI1918 (runFrom pI1918 (fmask pI1918) (cmask pI1918) (hmask pI1918) 1566 352 (true, I1918_cp2.1, I1918_cp2.2)) 1918 22 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1918_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1918_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1918_fin) true) I1918_seg1) I1918_seg2) (by decide) rfl I1918_fin intTest_fst
theorem link1918 : linkOK pL1918 pH1918 pI1918 = true := by decide +kernel
theorem cvx1918 : ConvexBetweenHumps 1918 :=
  cvx_of L1918_ok H1918_ok I1918_ok link1918 (by decide)
theorem cenlink1918 : cenLinkOK pI1918 1918 = true := by decide +kernel
theorem cen1918 : CenterUniqueMin 1918 ∧ DipHyp 1918 ∧ OnePointHyps 1918 :=
  cen_of L1918_ok H1918_ok I1918_ok link1918 cenlink1918

/-! ### `N = 1919` -/

def pL1919 : Prm := ⟨80, 37, 40, 1921, 11, 18446744073709551616, 101733264484993390, 101733264484993390⟩
def pH1919 : Prm := ⟨80, 37, 40, 1921, 11, 18446744073709551616, 101734363996621166, 101734363996621166⟩
def pI1919 : Prm := ⟨68, 34, 31, 1921, 11, 18446744073709551616, 101733264484993390, 101734363996621166⟩
noncomputable def L1919_cp1 : Nat × Nat := t7val% (fastRun pL1919 1 1107 (init pL1919) (init pL1919))
theorem L1919_seg1 : segOK pL1919 1 1107 (init pL1919) (init pL1919) L1919_cp1.1 L1919_cp1.2 = true := by
  decide +kernel
noncomputable def L1919_cp2 : Nat × Nat := t7val% (fastRun pL1919 1 1566 (init pL1919) (init pL1919))
theorem L1919_seg2 : segOK pL1919 1108 459 L1919_cp1.1 L1919_cp1.2 L1919_cp2.1 L1919_cp2.2 = true := by
  decide +kernel
theorem L1919_fin : (prmOK pL1919 1919 && ptTest pL1919 (runFrom pL1919 (fmask pL1919) (cmask pL1919) (hmask pL1919) 1567 352 (true, L1919_cp2.1, L1919_cp2.2)) 1919 960 false) = true := by
  decide +kernel
theorem L1919_ok : RunOK pL1919 1919 (runFrom pL1919 (fmask pL1919) (cmask pL1919) (hmask pL1919) 1567 352 (true, L1919_cp2.1, L1919_cp2.2)) ∧ ptTest pL1919 (runFrom pL1919 (fmask pL1919) (cmask pL1919) (hmask pL1919) 1567 352 (true, L1919_cp2.1, L1919_cp2.2)) 1919 960 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1919_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and L1919_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1919_fin) true) L1919_seg1) L1919_seg2) (by decide) rfl L1919_fin ptTest_fst
noncomputable def H1919_cp1 : Nat × Nat := t7val% (fastRun pH1919 1 1107 (init pH1919) (init pH1919))
theorem H1919_seg1 : segOK pH1919 1 1107 (init pH1919) (init pH1919) H1919_cp1.1 H1919_cp1.2 = true := by
  decide +kernel
noncomputable def H1919_cp2 : Nat × Nat := t7val% (fastRun pH1919 1 1566 (init pH1919) (init pH1919))
theorem H1919_seg2 : segOK pH1919 1108 459 H1919_cp1.1 H1919_cp1.2 H1919_cp2.1 H1919_cp2.2 = true := by
  decide +kernel
theorem H1919_fin : (prmOK pH1919 1919 && ptTest pH1919 (runFrom pH1919 (fmask pH1919) (cmask pH1919) (hmask pH1919) 1567 352 (true, H1919_cp2.1, H1919_cp2.2)) 1919 960 true) = true := by
  decide +kernel
theorem H1919_ok : RunOK pH1919 1919 (runFrom pH1919 (fmask pH1919) (cmask pH1919) (hmask pH1919) 1567 352 (true, H1919_cp2.1, H1919_cp2.2)) ∧ ptTest pH1919 (runFrom pH1919 (fmask pH1919) (cmask pH1919) (hmask pH1919) 1567 352 (true, H1919_cp2.1, H1919_cp2.2)) 1919 960 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1919_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and H1919_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1919_fin) true) H1919_seg1) H1919_seg2) (by decide) rfl H1919_fin ptTest_fst
noncomputable def I1919_cp1 : Nat × Nat := t7val% (fastRun pI1919 1 1107 (init pI1919) (init pI1919))
theorem I1919_seg1 : segOK pI1919 1 1107 (init pI1919) (init pI1919) I1919_cp1.1 I1919_cp1.2 = true := by
  decide +kernel
noncomputable def I1919_cp2 : Nat × Nat := t7val% (fastRun pI1919 1 1566 (init pI1919) (init pI1919))
theorem I1919_seg2 : segOK pI1919 1108 459 I1919_cp1.1 I1919_cp1.2 I1919_cp2.1 I1919_cp2.2 = true := by
  decide +kernel
theorem I1919_fin : (prmOK pI1919 1919 && intTest pI1919 (runFrom pI1919 (fmask pI1919) (cmask pI1919) (hmask pI1919) 1567 352 (true, I1919_cp2.1, I1919_cp2.2)) 1919 22 false) = true := by
  decide +kernel
theorem I1919_ok : RunOK pI1919 1919 (runFrom pI1919 (fmask pI1919) (cmask pI1919) (hmask pI1919) 1567 352 (true, I1919_cp2.1, I1919_cp2.2)) ∧ intTest pI1919 (runFrom pI1919 (fmask pI1919) (cmask pI1919) (hmask pI1919) 1567 352 (true, I1919_cp2.1, I1919_cp2.2)) 1919 22 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1919_fin) (by decide) (by decide) (runOK_seg (prmOK_of_and I1919_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1919_fin) true) I1919_seg1) I1919_seg2) (by decide) rfl I1919_fin intTest_fst
theorem link1919 : linkOK pL1919 pH1919 pI1919 = true := by decide +kernel
theorem cvx1919 : ConvexBetweenHumps 1919 :=
  cvx_of L1919_ok H1919_ok I1919_ok link1919 (by decide)

/-! ### The range -/

theorem cvx_1909_1919 {N : ℕ} (h1 : 1909 ≤ N) (h2 : N ≤ 1919) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1913
  · by_cases h4 : N ≤ 1910
    · by_cases h6 : N ≤ 1909
      · obtain rfl : N = 1909 := by omega
        exact cvx1909
      · obtain rfl : N = 1910 := by omega
        exact cvx1910
    · by_cases h6 : N ≤ 1911
      · obtain rfl : N = 1911 := by omega
        exact cvx1911
      · by_cases h8 : N ≤ 1912
        · obtain rfl : N = 1912 := by omega
          exact cvx1912
        · obtain rfl : N = 1913 := by omega
          exact cvx1913
  · by_cases h4 : N ≤ 1916
    · by_cases h6 : N ≤ 1914
      · obtain rfl : N = 1914 := by omega
        exact cvx1914
      · by_cases h8 : N ≤ 1915
        · obtain rfl : N = 1915 := by omega
          exact cvx1915
        · obtain rfl : N = 1916 := by omega
          exact cvx1916
    · by_cases h6 : N ≤ 1917
      · obtain rfl : N = 1917 := by omega
        exact cvx1917
      · by_cases h8 : N ≤ 1918
        · obtain rfl : N = 1918 := by omega
          exact cvx1918
        · obtain rfl : N = 1919 := by omega
          exact cvx1919

theorem cen_1909_1919 {N : ℕ} (h1 : 1909 ≤ N) (h2 : N ≤ 1919) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1912
  · by_cases h4 : N ≤ 1910
    · obtain rfl : N = 1910 := by omega
      exact cen1910
    · obtain rfl : N = 1912 := by omega
      exact cen1912
  · by_cases h4 : N ≤ 1914
    · obtain rfl : N = 1914 := by omega
      exact cen1914
    · by_cases h6 : N ≤ 1916
      · obtain rfl : N = 1916 := by omega
        exact cen1916
      · obtain rfl : N = 1918 := by omega
        exact cen1918

end Kagey131.PaperD.T7
