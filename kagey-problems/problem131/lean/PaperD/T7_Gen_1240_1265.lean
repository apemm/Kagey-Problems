import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1240, …, 1265` (generated)

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

/-! ### `N = 1240` -/

def pL1240 : Prm := ⟨76, 35, 38, 1242, 11, 18446744073709551616, 145191563488634428, 145191563488634428⟩
def pH1240 : Prm := ⟨76, 35, 38, 1242, 11, 18446744073709551616, 145193762511889980, 145193762511889980⟩
def pI1240 : Prm := ⟨66, 33, 30, 1242, 11, 18446744073709551616, 145191563488634428, 145193762511889980⟩
noncomputable def L1240_cp1 : Nat × Nat := t7val% (fastRun pL1240 1 876 (init pL1240) (init pL1240))
theorem L1240_seg1 : segOK pL1240 1 876 (init pL1240) (init pL1240) L1240_cp1.1 L1240_cp1.2 = true := by
  decide +kernel
theorem L1240_fin : (prmOK pL1240 1240 && ptTest pL1240 (runFrom pL1240 (fmask pL1240) (cmask pL1240) (hmask pL1240) 877 363 (true, L1240_cp1.1, L1240_cp1.2)) 1240 620 false) = true := by
  decide +kernel
theorem L1240_ok : RunOK pL1240 1240 (runFrom pL1240 (fmask pL1240) (cmask pL1240) (hmask pL1240) 877 363 (true, L1240_cp1.1, L1240_cp1.2)) ∧ ptTest pL1240 (runFrom pL1240 (fmask pL1240) (cmask pL1240) (hmask pL1240) 877 363 (true, L1240_cp1.1, L1240_cp1.2)) 1240 620 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1240_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1240_fin) true) L1240_seg1) (by decide) rfl L1240_fin ptTest_fst
noncomputable def H1240_cp1 : Nat × Nat := t7val% (fastRun pH1240 1 876 (init pH1240) (init pH1240))
theorem H1240_seg1 : segOK pH1240 1 876 (init pH1240) (init pH1240) H1240_cp1.1 H1240_cp1.2 = true := by
  decide +kernel
theorem H1240_fin : (prmOK pH1240 1240 && ptTest pH1240 (runFrom pH1240 (fmask pH1240) (cmask pH1240) (hmask pH1240) 877 363 (true, H1240_cp1.1, H1240_cp1.2)) 1240 620 true) = true := by
  decide +kernel
theorem H1240_ok : RunOK pH1240 1240 (runFrom pH1240 (fmask pH1240) (cmask pH1240) (hmask pH1240) 877 363 (true, H1240_cp1.1, H1240_cp1.2)) ∧ ptTest pH1240 (runFrom pH1240 (fmask pH1240) (cmask pH1240) (hmask pH1240) 877 363 (true, H1240_cp1.1, H1240_cp1.2)) 1240 620 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1240_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1240_fin) true) H1240_seg1) (by decide) rfl H1240_fin ptTest_fst
theorem I1240_fin : (prmOK pI1240 1240 && intTest pI1240 (runFrom pI1240 (fmask pI1240) (cmask pI1240) (hmask pI1240) 1 1239 (true, (init pI1240), (init pI1240))) 1240 19 true) = true := by
  decide +kernel
theorem I1240_ok : RunOK pI1240 1240 (runFrom pI1240 (fmask pI1240) (cmask pI1240) (hmask pI1240) 1 1239 (true, (init pI1240), (init pI1240))) ∧ intTest pI1240 (runFrom pI1240 (fmask pI1240) (cmask pI1240) (hmask pI1240) 1 1239 (true, (init pI1240), (init pI1240))) 1240 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1240_fin) true) (by decide) rfl I1240_fin intTest_fst
theorem link1240 : linkOK pL1240 pH1240 pI1240 = true := by decide +kernel
theorem cvx1240 : ConvexBetweenHumps 1240 :=
  cvx_of L1240_ok H1240_ok I1240_ok link1240 (by decide)
theorem cenlink1240 : cenLinkOK pI1240 1240 = true := by decide +kernel
theorem cen1240 : CenterUniqueMin 1240 ∧ DipHyp 1240 ∧ OnePointHyps 1240 :=
  cen_of L1240_ok H1240_ok I1240_ok link1240 cenlink1240

/-! ### `N = 1241` -/

def pL1241 : Prm := ⟨77, 36, 38, 1243, 11, 18446744073709551616, 145097134598102604, 145097134598102604⟩
def pH1241 : Prm := ⟨76, 35, 38, 1243, 11, 18446744073709551616, 145099333621358156, 145099333621358156⟩
def pI1241 : Prm := ⟨66, 33, 30, 1243, 11, 18446744073709551616, 145097134598102604, 145099333621358156⟩
noncomputable def L1241_cp1 : Nat × Nat := t7val% (fastRun pL1241 1 877 (init pL1241) (init pL1241))
theorem L1241_seg1 : segOK pL1241 1 877 (init pL1241) (init pL1241) L1241_cp1.1 L1241_cp1.2 = true := by
  decide +kernel
theorem L1241_fin : (prmOK pL1241 1241 && ptTest pL1241 (runFrom pL1241 (fmask pL1241) (cmask pL1241) (hmask pL1241) 878 363 (true, L1241_cp1.1, L1241_cp1.2)) 1241 621 false) = true := by
  decide +kernel
theorem L1241_ok : RunOK pL1241 1241 (runFrom pL1241 (fmask pL1241) (cmask pL1241) (hmask pL1241) 878 363 (true, L1241_cp1.1, L1241_cp1.2)) ∧ ptTest pL1241 (runFrom pL1241 (fmask pL1241) (cmask pL1241) (hmask pL1241) 878 363 (true, L1241_cp1.1, L1241_cp1.2)) 1241 621 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1241_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1241_fin) true) L1241_seg1) (by decide) rfl L1241_fin ptTest_fst
noncomputable def H1241_cp1 : Nat × Nat := t7val% (fastRun pH1241 1 877 (init pH1241) (init pH1241))
theorem H1241_seg1 : segOK pH1241 1 877 (init pH1241) (init pH1241) H1241_cp1.1 H1241_cp1.2 = true := by
  decide +kernel
theorem H1241_fin : (prmOK pH1241 1241 && ptTest pH1241 (runFrom pH1241 (fmask pH1241) (cmask pH1241) (hmask pH1241) 878 363 (true, H1241_cp1.1, H1241_cp1.2)) 1241 621 true) = true := by
  decide +kernel
theorem H1241_ok : RunOK pH1241 1241 (runFrom pH1241 (fmask pH1241) (cmask pH1241) (hmask pH1241) 878 363 (true, H1241_cp1.1, H1241_cp1.2)) ∧ ptTest pH1241 (runFrom pH1241 (fmask pH1241) (cmask pH1241) (hmask pH1241) 878 363 (true, H1241_cp1.1, H1241_cp1.2)) 1241 621 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1241_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1241_fin) true) H1241_seg1) (by decide) rfl H1241_fin ptTest_fst
theorem I1241_fin : (prmOK pI1241 1241 && intTest pI1241 (runFrom pI1241 (fmask pI1241) (cmask pI1241) (hmask pI1241) 1 1240 (true, (init pI1241), (init pI1241))) 1241 19 false) = true := by
  decide +kernel
theorem I1241_ok : RunOK pI1241 1241 (runFrom pI1241 (fmask pI1241) (cmask pI1241) (hmask pI1241) 1 1240 (true, (init pI1241), (init pI1241))) ∧ intTest pI1241 (runFrom pI1241 (fmask pI1241) (cmask pI1241) (hmask pI1241) 1 1240 (true, (init pI1241), (init pI1241))) 1241 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1241_fin) true) (by decide) rfl I1241_fin intTest_fst
theorem link1241 : linkOK pL1241 pH1241 pI1241 = true := by decide +kernel
theorem cvx1241 : ConvexBetweenHumps 1241 :=
  cvx_of L1241_ok H1241_ok I1241_ok link1241 (by decide)

/-! ### `N = 1242` -/

def pL1242 : Prm := ⟨76, 35, 38, 1244, 11, 18446744073709551616, 145002899313307169, 145002899313307169⟩
def pH1242 : Prm := ⟨77, 36, 38, 1244, 11, 18446744073709551616, 145005098336562721, 145005098336562721⟩
def pI1242 : Prm := ⟨66, 33, 30, 1244, 11, 18446744073709551616, 145002899313307169, 145005098336562721⟩
noncomputable def L1242_cp1 : Nat × Nat := t7val% (fastRun pL1242 1 877 (init pL1242) (init pL1242))
theorem L1242_seg1 : segOK pL1242 1 877 (init pL1242) (init pL1242) L1242_cp1.1 L1242_cp1.2 = true := by
  decide +kernel
theorem L1242_fin : (prmOK pL1242 1242 && ptTest pL1242 (runFrom pL1242 (fmask pL1242) (cmask pL1242) (hmask pL1242) 878 364 (true, L1242_cp1.1, L1242_cp1.2)) 1242 621 false) = true := by
  decide +kernel
theorem L1242_ok : RunOK pL1242 1242 (runFrom pL1242 (fmask pL1242) (cmask pL1242) (hmask pL1242) 878 364 (true, L1242_cp1.1, L1242_cp1.2)) ∧ ptTest pL1242 (runFrom pL1242 (fmask pL1242) (cmask pL1242) (hmask pL1242) 878 364 (true, L1242_cp1.1, L1242_cp1.2)) 1242 621 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1242_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1242_fin) true) L1242_seg1) (by decide) rfl L1242_fin ptTest_fst
noncomputable def H1242_cp1 : Nat × Nat := t7val% (fastRun pH1242 1 877 (init pH1242) (init pH1242))
theorem H1242_seg1 : segOK pH1242 1 877 (init pH1242) (init pH1242) H1242_cp1.1 H1242_cp1.2 = true := by
  decide +kernel
theorem H1242_fin : (prmOK pH1242 1242 && ptTest pH1242 (runFrom pH1242 (fmask pH1242) (cmask pH1242) (hmask pH1242) 878 364 (true, H1242_cp1.1, H1242_cp1.2)) 1242 621 true) = true := by
  decide +kernel
theorem H1242_ok : RunOK pH1242 1242 (runFrom pH1242 (fmask pH1242) (cmask pH1242) (hmask pH1242) 878 364 (true, H1242_cp1.1, H1242_cp1.2)) ∧ ptTest pH1242 (runFrom pH1242 (fmask pH1242) (cmask pH1242) (hmask pH1242) 878 364 (true, H1242_cp1.1, H1242_cp1.2)) 1242 621 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1242_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1242_fin) true) H1242_seg1) (by decide) rfl H1242_fin ptTest_fst
theorem I1242_fin : (prmOK pI1242 1242 && intTest pI1242 (runFrom pI1242 (fmask pI1242) (cmask pI1242) (hmask pI1242) 1 1241 (true, (init pI1242), (init pI1242))) 1242 19 true) = true := by
  decide +kernel
theorem I1242_ok : RunOK pI1242 1242 (runFrom pI1242 (fmask pI1242) (cmask pI1242) (hmask pI1242) 1 1241 (true, (init pI1242), (init pI1242))) ∧ intTest pI1242 (runFrom pI1242 (fmask pI1242) (cmask pI1242) (hmask pI1242) 1 1241 (true, (init pI1242), (init pI1242))) 1242 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1242_fin) true) (by decide) rfl I1242_fin intTest_fst
theorem link1242 : linkOK pL1242 pH1242 pI1242 = true := by decide +kernel
theorem cvx1242 : ConvexBetweenHumps 1242 :=
  cvx_of L1242_ok H1242_ok I1242_ok link1242 (by decide)
theorem cenlink1242 : cenLinkOK pI1242 1242 = true := by decide +kernel
theorem cen1242 : CenterUniqueMin 1242 ∧ DipHyp 1242 ∧ OnePointHyps 1242 :=
  cen_of L1242_ok H1242_ok I1242_ok link1242 cenlink1242

/-! ### `N = 1243` -/

def pL1243 : Prm := ⟨76, 35, 38, 1245, 11, 18446744073709551616, 144908737900619754, 144908737900619754⟩
def pH1243 : Prm := ⟨77, 36, 38, 1245, 11, 18446744073709551616, 144910936923875306, 144910936923875306⟩
def pI1243 : Prm := ⟨66, 33, 30, 1245, 11, 18446744073709551616, 144908737900619754, 144910936923875306⟩
noncomputable def L1243_cp1 : Nat × Nat := t7val% (fastRun pL1243 1 878 (init pL1243) (init pL1243))
theorem L1243_seg1 : segOK pL1243 1 878 (init pL1243) (init pL1243) L1243_cp1.1 L1243_cp1.2 = true := by
  decide +kernel
theorem L1243_fin : (prmOK pL1243 1243 && ptTest pL1243 (runFrom pL1243 (fmask pL1243) (cmask pL1243) (hmask pL1243) 879 364 (true, L1243_cp1.1, L1243_cp1.2)) 1243 622 false) = true := by
  decide +kernel
theorem L1243_ok : RunOK pL1243 1243 (runFrom pL1243 (fmask pL1243) (cmask pL1243) (hmask pL1243) 879 364 (true, L1243_cp1.1, L1243_cp1.2)) ∧ ptTest pL1243 (runFrom pL1243 (fmask pL1243) (cmask pL1243) (hmask pL1243) 879 364 (true, L1243_cp1.1, L1243_cp1.2)) 1243 622 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1243_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1243_fin) true) L1243_seg1) (by decide) rfl L1243_fin ptTest_fst
noncomputable def H1243_cp1 : Nat × Nat := t7val% (fastRun pH1243 1 878 (init pH1243) (init pH1243))
theorem H1243_seg1 : segOK pH1243 1 878 (init pH1243) (init pH1243) H1243_cp1.1 H1243_cp1.2 = true := by
  decide +kernel
theorem H1243_fin : (prmOK pH1243 1243 && ptTest pH1243 (runFrom pH1243 (fmask pH1243) (cmask pH1243) (hmask pH1243) 879 364 (true, H1243_cp1.1, H1243_cp1.2)) 1243 622 true) = true := by
  decide +kernel
theorem H1243_ok : RunOK pH1243 1243 (runFrom pH1243 (fmask pH1243) (cmask pH1243) (hmask pH1243) 879 364 (true, H1243_cp1.1, H1243_cp1.2)) ∧ ptTest pH1243 (runFrom pH1243 (fmask pH1243) (cmask pH1243) (hmask pH1243) 879 364 (true, H1243_cp1.1, H1243_cp1.2)) 1243 622 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1243_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1243_fin) true) H1243_seg1) (by decide) rfl H1243_fin ptTest_fst
theorem I1243_fin : (prmOK pI1243 1243 && intTest pI1243 (runFrom pI1243 (fmask pI1243) (cmask pI1243) (hmask pI1243) 1 1242 (true, (init pI1243), (init pI1243))) 1243 19 false) = true := by
  decide +kernel
theorem I1243_ok : RunOK pI1243 1243 (runFrom pI1243 (fmask pI1243) (cmask pI1243) (hmask pI1243) 1 1242 (true, (init pI1243), (init pI1243))) ∧ intTest pI1243 (runFrom pI1243 (fmask pI1243) (cmask pI1243) (hmask pI1243) 1 1242 (true, (init pI1243), (init pI1243))) 1243 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1243_fin) true) (by decide) rfl I1243_fin intTest_fst
theorem link1243 : linkOK pL1243 pH1243 pI1243 = true := by decide +kernel
theorem cvx1243 : ConvexBetweenHumps 1243 :=
  cvx_of L1243_ok H1243_ok I1243_ok link1243 (by decide)

/-! ### `N = 1244` -/

def pL1244 : Prm := ⟨76, 35, 38, 1246, 11, 18446744073709551616, 144814769213980397, 144814769213980397⟩
def pH1244 : Prm := ⟨77, 36, 38, 1246, 11, 18446744073709551616, 144816968237235949, 144816968237235949⟩
def pI1244 : Prm := ⟨66, 33, 30, 1246, 11, 18446744073709551616, 144814769213980397, 144816968237235949⟩
noncomputable def L1244_cp1 : Nat × Nat := t7val% (fastRun pL1244 1 879 (init pL1244) (init pL1244))
theorem L1244_seg1 : segOK pL1244 1 879 (init pL1244) (init pL1244) L1244_cp1.1 L1244_cp1.2 = true := by
  decide +kernel
theorem L1244_fin : (prmOK pL1244 1244 && ptTest pL1244 (runFrom pL1244 (fmask pL1244) (cmask pL1244) (hmask pL1244) 880 364 (true, L1244_cp1.1, L1244_cp1.2)) 1244 622 false) = true := by
  decide +kernel
theorem L1244_ok : RunOK pL1244 1244 (runFrom pL1244 (fmask pL1244) (cmask pL1244) (hmask pL1244) 880 364 (true, L1244_cp1.1, L1244_cp1.2)) ∧ ptTest pL1244 (runFrom pL1244 (fmask pL1244) (cmask pL1244) (hmask pL1244) 880 364 (true, L1244_cp1.1, L1244_cp1.2)) 1244 622 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1244_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1244_fin) true) L1244_seg1) (by decide) rfl L1244_fin ptTest_fst
noncomputable def H1244_cp1 : Nat × Nat := t7val% (fastRun pH1244 1 879 (init pH1244) (init pH1244))
theorem H1244_seg1 : segOK pH1244 1 879 (init pH1244) (init pH1244) H1244_cp1.1 H1244_cp1.2 = true := by
  decide +kernel
theorem H1244_fin : (prmOK pH1244 1244 && ptTest pH1244 (runFrom pH1244 (fmask pH1244) (cmask pH1244) (hmask pH1244) 880 364 (true, H1244_cp1.1, H1244_cp1.2)) 1244 622 true) = true := by
  decide +kernel
theorem H1244_ok : RunOK pH1244 1244 (runFrom pH1244 (fmask pH1244) (cmask pH1244) (hmask pH1244) 880 364 (true, H1244_cp1.1, H1244_cp1.2)) ∧ ptTest pH1244 (runFrom pH1244 (fmask pH1244) (cmask pH1244) (hmask pH1244) 880 364 (true, H1244_cp1.1, H1244_cp1.2)) 1244 622 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1244_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1244_fin) true) H1244_seg1) (by decide) rfl H1244_fin ptTest_fst
theorem I1244_fin : (prmOK pI1244 1244 && intTest pI1244 (runFrom pI1244 (fmask pI1244) (cmask pI1244) (hmask pI1244) 1 1243 (true, (init pI1244), (init pI1244))) 1244 19 true) = true := by
  decide +kernel
theorem I1244_ok : RunOK pI1244 1244 (runFrom pI1244 (fmask pI1244) (cmask pI1244) (hmask pI1244) 1 1243 (true, (init pI1244), (init pI1244))) ∧ intTest pI1244 (runFrom pI1244 (fmask pI1244) (cmask pI1244) (hmask pI1244) 1 1243 (true, (init pI1244), (init pI1244))) 1244 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1244_fin) true) (by decide) rfl I1244_fin intTest_fst
theorem link1244 : linkOK pL1244 pH1244 pI1244 = true := by decide +kernel
theorem cvx1244 : ConvexBetweenHumps 1244 :=
  cvx_of L1244_ok H1244_ok I1244_ok link1244 (by decide)
theorem cenlink1244 : cenLinkOK pI1244 1244 = true := by decide +kernel
theorem cen1244 : CenterUniqueMin 1244 ∧ DipHyp 1244 ∧ OnePointHyps 1244 :=
  cen_of L1244_ok H1244_ok I1244_ok link1244 cenlink1244

/-! ### `N = 1245` -/

def pL1245 : Prm := ⟨77, 36, 38, 1247, 11, 18446744073709551616, 144720874106736124, 144720874106736124⟩
def pH1245 : Prm := ⟨77, 36, 38, 1247, 11, 18446744073709551616, 144723073129991676, 144723073129991676⟩
def pI1245 : Prm := ⟨66, 33, 30, 1247, 11, 18446744073709551616, 144720874106736124, 144723073129991676⟩
noncomputable def L1245_cp1 : Nat × Nat := t7val% (fastRun pL1245 1 879 (init pL1245) (init pL1245))
theorem L1245_seg1 : segOK pL1245 1 879 (init pL1245) (init pL1245) L1245_cp1.1 L1245_cp1.2 = true := by
  decide +kernel
theorem L1245_fin : (prmOK pL1245 1245 && ptTest pL1245 (runFrom pL1245 (fmask pL1245) (cmask pL1245) (hmask pL1245) 880 365 (true, L1245_cp1.1, L1245_cp1.2)) 1245 623 false) = true := by
  decide +kernel
theorem L1245_ok : RunOK pL1245 1245 (runFrom pL1245 (fmask pL1245) (cmask pL1245) (hmask pL1245) 880 365 (true, L1245_cp1.1, L1245_cp1.2)) ∧ ptTest pL1245 (runFrom pL1245 (fmask pL1245) (cmask pL1245) (hmask pL1245) 880 365 (true, L1245_cp1.1, L1245_cp1.2)) 1245 623 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1245_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1245_fin) true) L1245_seg1) (by decide) rfl L1245_fin ptTest_fst
noncomputable def H1245_cp1 : Nat × Nat := t7val% (fastRun pH1245 1 879 (init pH1245) (init pH1245))
theorem H1245_seg1 : segOK pH1245 1 879 (init pH1245) (init pH1245) H1245_cp1.1 H1245_cp1.2 = true := by
  decide +kernel
theorem H1245_fin : (prmOK pH1245 1245 && ptTest pH1245 (runFrom pH1245 (fmask pH1245) (cmask pH1245) (hmask pH1245) 880 365 (true, H1245_cp1.1, H1245_cp1.2)) 1245 623 true) = true := by
  decide +kernel
theorem H1245_ok : RunOK pH1245 1245 (runFrom pH1245 (fmask pH1245) (cmask pH1245) (hmask pH1245) 880 365 (true, H1245_cp1.1, H1245_cp1.2)) ∧ ptTest pH1245 (runFrom pH1245 (fmask pH1245) (cmask pH1245) (hmask pH1245) 880 365 (true, H1245_cp1.1, H1245_cp1.2)) 1245 623 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1245_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1245_fin) true) H1245_seg1) (by decide) rfl H1245_fin ptTest_fst
theorem I1245_fin : (prmOK pI1245 1245 && intTest pI1245 (runFrom pI1245 (fmask pI1245) (cmask pI1245) (hmask pI1245) 1 1244 (true, (init pI1245), (init pI1245))) 1245 19 false) = true := by
  decide +kernel
theorem I1245_ok : RunOK pI1245 1245 (runFrom pI1245 (fmask pI1245) (cmask pI1245) (hmask pI1245) 1 1244 (true, (init pI1245), (init pI1245))) ∧ intTest pI1245 (runFrom pI1245 (fmask pI1245) (cmask pI1245) (hmask pI1245) 1 1244 (true, (init pI1245), (init pI1245))) 1245 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1245_fin) true) (by decide) rfl I1245_fin intTest_fst
theorem link1245 : linkOK pL1245 pH1245 pI1245 = true := by decide +kernel
theorem cvx1245 : ConvexBetweenHumps 1245 :=
  cvx_of L1245_ok H1245_ok I1245_ok link1245 (by decide)

/-! ### `N = 1246` -/

def pL1246 : Prm := ⟨76, 35, 38, 1248, 11, 18446744073709551616, 144627170851274922, 144627170851274922⟩
def pH1246 : Prm := ⟨77, 36, 38, 1248, 11, 18446744073709551616, 144629369874530474, 144629369874530474⟩
def pI1246 : Prm := ⟨66, 33, 30, 1248, 11, 18446744073709551616, 144627170851274922, 144629369874530474⟩
noncomputable def L1246_cp1 : Nat × Nat := t7val% (fastRun pL1246 1 880 (init pL1246) (init pL1246))
theorem L1246_seg1 : segOK pL1246 1 880 (init pL1246) (init pL1246) L1246_cp1.1 L1246_cp1.2 = true := by
  decide +kernel
theorem L1246_fin : (prmOK pL1246 1246 && ptTest pL1246 (runFrom pL1246 (fmask pL1246) (cmask pL1246) (hmask pL1246) 881 365 (true, L1246_cp1.1, L1246_cp1.2)) 1246 623 false) = true := by
  decide +kernel
theorem L1246_ok : RunOK pL1246 1246 (runFrom pL1246 (fmask pL1246) (cmask pL1246) (hmask pL1246) 881 365 (true, L1246_cp1.1, L1246_cp1.2)) ∧ ptTest pL1246 (runFrom pL1246 (fmask pL1246) (cmask pL1246) (hmask pL1246) 881 365 (true, L1246_cp1.1, L1246_cp1.2)) 1246 623 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1246_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1246_fin) true) L1246_seg1) (by decide) rfl L1246_fin ptTest_fst
noncomputable def H1246_cp1 : Nat × Nat := t7val% (fastRun pH1246 1 880 (init pH1246) (init pH1246))
theorem H1246_seg1 : segOK pH1246 1 880 (init pH1246) (init pH1246) H1246_cp1.1 H1246_cp1.2 = true := by
  decide +kernel
theorem H1246_fin : (prmOK pH1246 1246 && ptTest pH1246 (runFrom pH1246 (fmask pH1246) (cmask pH1246) (hmask pH1246) 881 365 (true, H1246_cp1.1, H1246_cp1.2)) 1246 623 true) = true := by
  decide +kernel
theorem H1246_ok : RunOK pH1246 1246 (runFrom pH1246 (fmask pH1246) (cmask pH1246) (hmask pH1246) 881 365 (true, H1246_cp1.1, H1246_cp1.2)) ∧ ptTest pH1246 (runFrom pH1246 (fmask pH1246) (cmask pH1246) (hmask pH1246) 881 365 (true, H1246_cp1.1, H1246_cp1.2)) 1246 623 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1246_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1246_fin) true) H1246_seg1) (by decide) rfl H1246_fin ptTest_fst
theorem I1246_fin : (prmOK pI1246 1246 && intTest pI1246 (runFrom pI1246 (fmask pI1246) (cmask pI1246) (hmask pI1246) 1 1245 (true, (init pI1246), (init pI1246))) 1246 19 true) = true := by
  decide +kernel
theorem I1246_ok : RunOK pI1246 1246 (runFrom pI1246 (fmask pI1246) (cmask pI1246) (hmask pI1246) 1 1245 (true, (init pI1246), (init pI1246))) ∧ intTest pI1246 (runFrom pI1246 (fmask pI1246) (cmask pI1246) (hmask pI1246) 1 1245 (true, (init pI1246), (init pI1246))) 1246 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1246_fin) true) (by decide) rfl I1246_fin intTest_fst
theorem link1246 : linkOK pL1246 pH1246 pI1246 = true := by decide +kernel
theorem cvx1246 : ConvexBetweenHumps 1246 :=
  cvx_of L1246_ok H1246_ok I1246_ok link1246 (by decide)
theorem cenlink1246 : cenLinkOK pI1246 1246 = true := by decide +kernel
theorem cen1246 : CenterUniqueMin 1246 ∧ DipHyp 1246 ∧ OnePointHyps 1246 :=
  cen_of L1246_ok H1246_ok I1246_ok link1246 cenlink1246

/-! ### `N = 1247` -/

def pL1247 : Prm := ⟨77, 36, 38, 1249, 11, 18446744073709551616, 144533540884045395, 144533540884045395⟩
def pH1247 : Prm := ⟨77, 36, 38, 1249, 11, 18446744073709551616, 144535739907300947, 144535739907300947⟩
def pI1247 : Prm := ⟨66, 33, 30, 1249, 11, 18446744073709551616, 144533540884045395, 144535739907300947⟩
noncomputable def L1247_cp1 : Nat × Nat := t7val% (fastRun pL1247 1 881 (init pL1247) (init pL1247))
theorem L1247_seg1 : segOK pL1247 1 881 (init pL1247) (init pL1247) L1247_cp1.1 L1247_cp1.2 = true := by
  decide +kernel
theorem L1247_fin : (prmOK pL1247 1247 && ptTest pL1247 (runFrom pL1247 (fmask pL1247) (cmask pL1247) (hmask pL1247) 882 365 (true, L1247_cp1.1, L1247_cp1.2)) 1247 624 false) = true := by
  decide +kernel
theorem L1247_ok : RunOK pL1247 1247 (runFrom pL1247 (fmask pL1247) (cmask pL1247) (hmask pL1247) 882 365 (true, L1247_cp1.1, L1247_cp1.2)) ∧ ptTest pL1247 (runFrom pL1247 (fmask pL1247) (cmask pL1247) (hmask pL1247) 882 365 (true, L1247_cp1.1, L1247_cp1.2)) 1247 624 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1247_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1247_fin) true) L1247_seg1) (by decide) rfl L1247_fin ptTest_fst
noncomputable def H1247_cp1 : Nat × Nat := t7val% (fastRun pH1247 1 881 (init pH1247) (init pH1247))
theorem H1247_seg1 : segOK pH1247 1 881 (init pH1247) (init pH1247) H1247_cp1.1 H1247_cp1.2 = true := by
  decide +kernel
theorem H1247_fin : (prmOK pH1247 1247 && ptTest pH1247 (runFrom pH1247 (fmask pH1247) (cmask pH1247) (hmask pH1247) 882 365 (true, H1247_cp1.1, H1247_cp1.2)) 1247 624 true) = true := by
  decide +kernel
theorem H1247_ok : RunOK pH1247 1247 (runFrom pH1247 (fmask pH1247) (cmask pH1247) (hmask pH1247) 882 365 (true, H1247_cp1.1, H1247_cp1.2)) ∧ ptTest pH1247 (runFrom pH1247 (fmask pH1247) (cmask pH1247) (hmask pH1247) 882 365 (true, H1247_cp1.1, H1247_cp1.2)) 1247 624 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1247_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1247_fin) true) H1247_seg1) (by decide) rfl H1247_fin ptTest_fst
theorem I1247_fin : (prmOK pI1247 1247 && intTest pI1247 (runFrom pI1247 (fmask pI1247) (cmask pI1247) (hmask pI1247) 1 1246 (true, (init pI1247), (init pI1247))) 1247 19 false) = true := by
  decide +kernel
theorem I1247_ok : RunOK pI1247 1247 (runFrom pI1247 (fmask pI1247) (cmask pI1247) (hmask pI1247) 1 1246 (true, (init pI1247), (init pI1247))) ∧ intTest pI1247 (runFrom pI1247 (fmask pI1247) (cmask pI1247) (hmask pI1247) 1 1246 (true, (init pI1247), (init pI1247))) 1247 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1247_fin) true) (by decide) rfl I1247_fin intTest_fst
theorem link1247 : linkOK pL1247 pH1247 pI1247 = true := by decide +kernel
theorem cvx1247 : ConvexBetweenHumps 1247 :=
  cvx_of L1247_ok H1247_ok I1247_ok link1247 (by decide)

/-! ### `N = 1248` -/

def pL1248 : Prm := ⟨77, 36, 38, 1250, 11, 18446744073709551616, 144440101899646611, 144440101899646611⟩
def pH1248 : Prm := ⟨77, 36, 38, 1250, 11, 18446744073709551616, 144442300922902163, 144442300922902163⟩
def pI1248 : Prm := ⟨66, 33, 30, 1250, 11, 18446744073709551616, 144440101899646611, 144442300922902163⟩
noncomputable def L1248_cp1 : Nat × Nat := t7val% (fastRun pL1248 1 881 (init pL1248) (init pL1248))
theorem L1248_seg1 : segOK pL1248 1 881 (init pL1248) (init pL1248) L1248_cp1.1 L1248_cp1.2 = true := by
  decide +kernel
theorem L1248_fin : (prmOK pL1248 1248 && ptTest pL1248 (runFrom pL1248 (fmask pL1248) (cmask pL1248) (hmask pL1248) 882 366 (true, L1248_cp1.1, L1248_cp1.2)) 1248 624 false) = true := by
  decide +kernel
theorem L1248_ok : RunOK pL1248 1248 (runFrom pL1248 (fmask pL1248) (cmask pL1248) (hmask pL1248) 882 366 (true, L1248_cp1.1, L1248_cp1.2)) ∧ ptTest pL1248 (runFrom pL1248 (fmask pL1248) (cmask pL1248) (hmask pL1248) 882 366 (true, L1248_cp1.1, L1248_cp1.2)) 1248 624 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1248_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1248_fin) true) L1248_seg1) (by decide) rfl L1248_fin ptTest_fst
noncomputable def H1248_cp1 : Nat × Nat := t7val% (fastRun pH1248 1 881 (init pH1248) (init pH1248))
theorem H1248_seg1 : segOK pH1248 1 881 (init pH1248) (init pH1248) H1248_cp1.1 H1248_cp1.2 = true := by
  decide +kernel
theorem H1248_fin : (prmOK pH1248 1248 && ptTest pH1248 (runFrom pH1248 (fmask pH1248) (cmask pH1248) (hmask pH1248) 882 366 (true, H1248_cp1.1, H1248_cp1.2)) 1248 624 true) = true := by
  decide +kernel
theorem H1248_ok : RunOK pH1248 1248 (runFrom pH1248 (fmask pH1248) (cmask pH1248) (hmask pH1248) 882 366 (true, H1248_cp1.1, H1248_cp1.2)) ∧ ptTest pH1248 (runFrom pH1248 (fmask pH1248) (cmask pH1248) (hmask pH1248) 882 366 (true, H1248_cp1.1, H1248_cp1.2)) 1248 624 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1248_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1248_fin) true) H1248_seg1) (by decide) rfl H1248_fin ptTest_fst
theorem I1248_fin : (prmOK pI1248 1248 && intTest pI1248 (runFrom pI1248 (fmask pI1248) (cmask pI1248) (hmask pI1248) 1 1247 (true, (init pI1248), (init pI1248))) 1248 19 true) = true := by
  decide +kernel
theorem I1248_ok : RunOK pI1248 1248 (runFrom pI1248 (fmask pI1248) (cmask pI1248) (hmask pI1248) 1 1247 (true, (init pI1248), (init pI1248))) ∧ intTest pI1248 (runFrom pI1248 (fmask pI1248) (cmask pI1248) (hmask pI1248) 1 1247 (true, (init pI1248), (init pI1248))) 1248 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1248_fin) true) (by decide) rfl I1248_fin intTest_fst
theorem link1248 : linkOK pL1248 pH1248 pI1248 = true := by decide +kernel
theorem cvx1248 : ConvexBetweenHumps 1248 :=
  cvx_of L1248_ok H1248_ok I1248_ok link1248 (by decide)
theorem cenlink1248 : cenLinkOK pI1248 1248 = true := by decide +kernel
theorem cen1248 : CenterUniqueMin 1248 ∧ DipHyp 1248 ∧ OnePointHyps 1248 :=
  cen_of L1248_ok H1248_ok I1248_ok link1248 cenlink1248

/-! ### `N = 1249` -/

def pL1249 : Prm := ⟨77, 36, 38, 1251, 11, 18446744073709551616, 144346735913920962, 144346735913920962⟩
def pH1249 : Prm := ⟨77, 36, 38, 1251, 11, 18446744073709551616, 144348934937176514, 144348934937176514⟩
def pI1249 : Prm := ⟨66, 33, 30, 1251, 11, 18446744073709551616, 144346735913920962, 144348934937176514⟩
noncomputable def L1249_cp1 : Nat × Nat := t7val% (fastRun pL1249 1 882 (init pL1249) (init pL1249))
theorem L1249_seg1 : segOK pL1249 1 882 (init pL1249) (init pL1249) L1249_cp1.1 L1249_cp1.2 = true := by
  decide +kernel
theorem L1249_fin : (prmOK pL1249 1249 && ptTest pL1249 (runFrom pL1249 (fmask pL1249) (cmask pL1249) (hmask pL1249) 883 366 (true, L1249_cp1.1, L1249_cp1.2)) 1249 625 false) = true := by
  decide +kernel
theorem L1249_ok : RunOK pL1249 1249 (runFrom pL1249 (fmask pL1249) (cmask pL1249) (hmask pL1249) 883 366 (true, L1249_cp1.1, L1249_cp1.2)) ∧ ptTest pL1249 (runFrom pL1249 (fmask pL1249) (cmask pL1249) (hmask pL1249) 883 366 (true, L1249_cp1.1, L1249_cp1.2)) 1249 625 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1249_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1249_fin) true) L1249_seg1) (by decide) rfl L1249_fin ptTest_fst
noncomputable def H1249_cp1 : Nat × Nat := t7val% (fastRun pH1249 1 882 (init pH1249) (init pH1249))
theorem H1249_seg1 : segOK pH1249 1 882 (init pH1249) (init pH1249) H1249_cp1.1 H1249_cp1.2 = true := by
  decide +kernel
theorem H1249_fin : (prmOK pH1249 1249 && ptTest pH1249 (runFrom pH1249 (fmask pH1249) (cmask pH1249) (hmask pH1249) 883 366 (true, H1249_cp1.1, H1249_cp1.2)) 1249 625 true) = true := by
  decide +kernel
theorem H1249_ok : RunOK pH1249 1249 (runFrom pH1249 (fmask pH1249) (cmask pH1249) (hmask pH1249) 883 366 (true, H1249_cp1.1, H1249_cp1.2)) ∧ ptTest pH1249 (runFrom pH1249 (fmask pH1249) (cmask pH1249) (hmask pH1249) 883 366 (true, H1249_cp1.1, H1249_cp1.2)) 1249 625 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1249_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1249_fin) true) H1249_seg1) (by decide) rfl H1249_fin ptTest_fst
theorem I1249_fin : (prmOK pI1249 1249 && intTest pI1249 (runFrom pI1249 (fmask pI1249) (cmask pI1249) (hmask pI1249) 1 1248 (true, (init pI1249), (init pI1249))) 1249 19 false) = true := by
  decide +kernel
theorem I1249_ok : RunOK pI1249 1249 (runFrom pI1249 (fmask pI1249) (cmask pI1249) (hmask pI1249) 1 1248 (true, (init pI1249), (init pI1249))) ∧ intTest pI1249 (runFrom pI1249 (fmask pI1249) (cmask pI1249) (hmask pI1249) 1 1248 (true, (init pI1249), (init pI1249))) 1249 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1249_fin) true) (by decide) rfl I1249_fin intTest_fst
theorem link1249 : linkOK pL1249 pH1249 pI1249 = true := by decide +kernel
theorem cvx1249 : ConvexBetweenHumps 1249 :=
  cvx_of L1249_ok H1249_ok I1249_ok link1249 (by decide)

/-! ### `N = 1250` -/

def pL1250 : Prm := ⟨77, 36, 38, 1252, 11, 18446744073709551616, 144253560047386392, 144253560047386392⟩
def pH1250 : Prm := ⟨77, 36, 38, 1252, 11, 18446744073709551616, 144255759070641944, 144255759070641944⟩
def pI1250 : Prm := ⟨66, 33, 30, 1252, 11, 18446744073709551616, 144253560047386392, 144255759070641944⟩
noncomputable def L1250_cp1 : Nat × Nat := t7val% (fastRun pL1250 1 883 (init pL1250) (init pL1250))
theorem L1250_seg1 : segOK pL1250 1 883 (init pL1250) (init pL1250) L1250_cp1.1 L1250_cp1.2 = true := by
  decide +kernel
theorem L1250_fin : (prmOK pL1250 1250 && ptTest pL1250 (runFrom pL1250 (fmask pL1250) (cmask pL1250) (hmask pL1250) 884 366 (true, L1250_cp1.1, L1250_cp1.2)) 1250 625 false) = true := by
  decide +kernel
theorem L1250_ok : RunOK pL1250 1250 (runFrom pL1250 (fmask pL1250) (cmask pL1250) (hmask pL1250) 884 366 (true, L1250_cp1.1, L1250_cp1.2)) ∧ ptTest pL1250 (runFrom pL1250 (fmask pL1250) (cmask pL1250) (hmask pL1250) 884 366 (true, L1250_cp1.1, L1250_cp1.2)) 1250 625 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1250_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1250_fin) true) L1250_seg1) (by decide) rfl L1250_fin ptTest_fst
noncomputable def H1250_cp1 : Nat × Nat := t7val% (fastRun pH1250 1 883 (init pH1250) (init pH1250))
theorem H1250_seg1 : segOK pH1250 1 883 (init pH1250) (init pH1250) H1250_cp1.1 H1250_cp1.2 = true := by
  decide +kernel
theorem H1250_fin : (prmOK pH1250 1250 && ptTest pH1250 (runFrom pH1250 (fmask pH1250) (cmask pH1250) (hmask pH1250) 884 366 (true, H1250_cp1.1, H1250_cp1.2)) 1250 625 true) = true := by
  decide +kernel
theorem H1250_ok : RunOK pH1250 1250 (runFrom pH1250 (fmask pH1250) (cmask pH1250) (hmask pH1250) 884 366 (true, H1250_cp1.1, H1250_cp1.2)) ∧ ptTest pH1250 (runFrom pH1250 (fmask pH1250) (cmask pH1250) (hmask pH1250) 884 366 (true, H1250_cp1.1, H1250_cp1.2)) 1250 625 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1250_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1250_fin) true) H1250_seg1) (by decide) rfl H1250_fin ptTest_fst
theorem I1250_fin : (prmOK pI1250 1250 && intTest pI1250 (runFrom pI1250 (fmask pI1250) (cmask pI1250) (hmask pI1250) 1 1249 (true, (init pI1250), (init pI1250))) 1250 19 true) = true := by
  decide +kernel
theorem I1250_ok : RunOK pI1250 1250 (runFrom pI1250 (fmask pI1250) (cmask pI1250) (hmask pI1250) 1 1249 (true, (init pI1250), (init pI1250))) ∧ intTest pI1250 (runFrom pI1250 (fmask pI1250) (cmask pI1250) (hmask pI1250) 1 1249 (true, (init pI1250), (init pI1250))) 1250 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1250_fin) true) (by decide) rfl I1250_fin intTest_fst
theorem link1250 : linkOK pL1250 pH1250 pI1250 = true := by decide +kernel
theorem cvx1250 : ConvexBetweenHumps 1250 :=
  cvx_of L1250_ok H1250_ok I1250_ok link1250 (by decide)
theorem cenlink1250 : cenLinkOK pI1250 1250 = true := by decide +kernel
theorem cen1250 : CenterUniqueMin 1250 ∧ DipHyp 1250 ∧ OnePointHyps 1250 :=
  cen_of L1250_ok H1250_ok I1250_ok link1250 cenlink1250

/-! ### `N = 1251` -/

def pL1251 : Prm := ⟨77, 36, 38, 1253, 11, 18446744073709551616, 144160456891497494, 144160456891497494⟩
def pH1251 : Prm := ⟨77, 36, 38, 1253, 11, 18446744073709551616, 144162655914753046, 144162655914753046⟩
def pI1251 : Prm := ⟨66, 33, 30, 1253, 11, 18446744073709551616, 144160456891497494, 144162655914753046⟩
noncomputable def L1251_cp1 : Nat × Nat := t7val% (fastRun pL1251 1 884 (init pL1251) (init pL1251))
theorem L1251_seg1 : segOK pL1251 1 884 (init pL1251) (init pL1251) L1251_cp1.1 L1251_cp1.2 = true := by
  decide +kernel
theorem L1251_fin : (prmOK pL1251 1251 && ptTest pL1251 (runFrom pL1251 (fmask pL1251) (cmask pL1251) (hmask pL1251) 885 366 (true, L1251_cp1.1, L1251_cp1.2)) 1251 626 false) = true := by
  decide +kernel
theorem L1251_ok : RunOK pL1251 1251 (runFrom pL1251 (fmask pL1251) (cmask pL1251) (hmask pL1251) 885 366 (true, L1251_cp1.1, L1251_cp1.2)) ∧ ptTest pL1251 (runFrom pL1251 (fmask pL1251) (cmask pL1251) (hmask pL1251) 885 366 (true, L1251_cp1.1, L1251_cp1.2)) 1251 626 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1251_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1251_fin) true) L1251_seg1) (by decide) rfl L1251_fin ptTest_fst
noncomputable def H1251_cp1 : Nat × Nat := t7val% (fastRun pH1251 1 884 (init pH1251) (init pH1251))
theorem H1251_seg1 : segOK pH1251 1 884 (init pH1251) (init pH1251) H1251_cp1.1 H1251_cp1.2 = true := by
  decide +kernel
theorem H1251_fin : (prmOK pH1251 1251 && ptTest pH1251 (runFrom pH1251 (fmask pH1251) (cmask pH1251) (hmask pH1251) 885 366 (true, H1251_cp1.1, H1251_cp1.2)) 1251 626 true) = true := by
  decide +kernel
theorem H1251_ok : RunOK pH1251 1251 (runFrom pH1251 (fmask pH1251) (cmask pH1251) (hmask pH1251) 885 366 (true, H1251_cp1.1, H1251_cp1.2)) ∧ ptTest pH1251 (runFrom pH1251 (fmask pH1251) (cmask pH1251) (hmask pH1251) 885 366 (true, H1251_cp1.1, H1251_cp1.2)) 1251 626 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1251_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1251_fin) true) H1251_seg1) (by decide) rfl H1251_fin ptTest_fst
theorem I1251_fin : (prmOK pI1251 1251 && intTest pI1251 (runFrom pI1251 (fmask pI1251) (cmask pI1251) (hmask pI1251) 1 1250 (true, (init pI1251), (init pI1251))) 1251 19 false) = true := by
  decide +kernel
theorem I1251_ok : RunOK pI1251 1251 (runFrom pI1251 (fmask pI1251) (cmask pI1251) (hmask pI1251) 1 1250 (true, (init pI1251), (init pI1251))) ∧ intTest pI1251 (runFrom pI1251 (fmask pI1251) (cmask pI1251) (hmask pI1251) 1 1250 (true, (init pI1251), (init pI1251))) 1251 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1251_fin) true) (by decide) rfl I1251_fin intTest_fst
theorem link1251 : linkOK pL1251 pH1251 pI1251 = true := by decide +kernel
theorem cvx1251 : ConvexBetweenHumps 1251 :=
  cvx_of L1251_ok H1251_ok I1251_ok link1251 (by decide)

/-! ### `N = 1252` -/

def pL1252 : Prm := ⟨77, 36, 38, 1254, 11, 18446744073709551616, 144067542996435780, 144067542996435780⟩
def pH1252 : Prm := ⟨77, 36, 38, 1254, 11, 18446744073709551616, 144069742019691332, 144069742019691332⟩
def pI1252 : Prm := ⟨66, 33, 30, 1254, 11, 18446744073709551616, 144067542996435780, 144069742019691332⟩
noncomputable def L1252_cp1 : Nat × Nat := t7val% (fastRun pL1252 1 884 (init pL1252) (init pL1252))
theorem L1252_seg1 : segOK pL1252 1 884 (init pL1252) (init pL1252) L1252_cp1.1 L1252_cp1.2 = true := by
  decide +kernel
theorem L1252_fin : (prmOK pL1252 1252 && ptTest pL1252 (runFrom pL1252 (fmask pL1252) (cmask pL1252) (hmask pL1252) 885 367 (true, L1252_cp1.1, L1252_cp1.2)) 1252 626 false) = true := by
  decide +kernel
theorem L1252_ok : RunOK pL1252 1252 (runFrom pL1252 (fmask pL1252) (cmask pL1252) (hmask pL1252) 885 367 (true, L1252_cp1.1, L1252_cp1.2)) ∧ ptTest pL1252 (runFrom pL1252 (fmask pL1252) (cmask pL1252) (hmask pL1252) 885 367 (true, L1252_cp1.1, L1252_cp1.2)) 1252 626 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1252_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1252_fin) true) L1252_seg1) (by decide) rfl L1252_fin ptTest_fst
noncomputable def H1252_cp1 : Nat × Nat := t7val% (fastRun pH1252 1 884 (init pH1252) (init pH1252))
theorem H1252_seg1 : segOK pH1252 1 884 (init pH1252) (init pH1252) H1252_cp1.1 H1252_cp1.2 = true := by
  decide +kernel
theorem H1252_fin : (prmOK pH1252 1252 && ptTest pH1252 (runFrom pH1252 (fmask pH1252) (cmask pH1252) (hmask pH1252) 885 367 (true, H1252_cp1.1, H1252_cp1.2)) 1252 626 true) = true := by
  decide +kernel
theorem H1252_ok : RunOK pH1252 1252 (runFrom pH1252 (fmask pH1252) (cmask pH1252) (hmask pH1252) 885 367 (true, H1252_cp1.1, H1252_cp1.2)) ∧ ptTest pH1252 (runFrom pH1252 (fmask pH1252) (cmask pH1252) (hmask pH1252) 885 367 (true, H1252_cp1.1, H1252_cp1.2)) 1252 626 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1252_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1252_fin) true) H1252_seg1) (by decide) rfl H1252_fin ptTest_fst
theorem I1252_fin : (prmOK pI1252 1252 && intTest pI1252 (runFrom pI1252 (fmask pI1252) (cmask pI1252) (hmask pI1252) 1 1251 (true, (init pI1252), (init pI1252))) 1252 19 true) = true := by
  decide +kernel
theorem I1252_ok : RunOK pI1252 1252 (runFrom pI1252 (fmask pI1252) (cmask pI1252) (hmask pI1252) 1 1251 (true, (init pI1252), (init pI1252))) ∧ intTest pI1252 (runFrom pI1252 (fmask pI1252) (cmask pI1252) (hmask pI1252) 1 1251 (true, (init pI1252), (init pI1252))) 1252 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1252_fin) true) (by decide) rfl I1252_fin intTest_fst
theorem link1252 : linkOK pL1252 pH1252 pI1252 = true := by decide +kernel
theorem cvx1252 : ConvexBetweenHumps 1252 :=
  cvx_of L1252_ok H1252_ok I1252_ok link1252 (by decide)
theorem cenlink1252 : cenLinkOK pI1252 1252 = true := by decide +kernel
theorem cen1252 : CenterUniqueMin 1252 ∧ DipHyp 1252 ∧ OnePointHyps 1252 :=
  cen_of L1252_ok H1252_ok I1252_ok link1252 cenlink1252

/-! ### `N = 1253` -/

def pL1253 : Prm := ⟨77, 36, 38, 1255, 11, 18446744073709551616, 143974701525541802, 143974701525541802⟩
def pH1253 : Prm := ⟨77, 36, 38, 1255, 11, 18446744073709551616, 143976900548797354, 143976900548797354⟩
def pI1253 : Prm := ⟨66, 33, 30, 1255, 11, 18446744073709551616, 143974701525541802, 143976900548797354⟩
noncomputable def L1253_cp1 : Nat × Nat := t7val% (fastRun pL1253 1 885 (init pL1253) (init pL1253))
theorem L1253_seg1 : segOK pL1253 1 885 (init pL1253) (init pL1253) L1253_cp1.1 L1253_cp1.2 = true := by
  decide +kernel
theorem L1253_fin : (prmOK pL1253 1253 && ptTest pL1253 (runFrom pL1253 (fmask pL1253) (cmask pL1253) (hmask pL1253) 886 367 (true, L1253_cp1.1, L1253_cp1.2)) 1253 627 false) = true := by
  decide +kernel
theorem L1253_ok : RunOK pL1253 1253 (runFrom pL1253 (fmask pL1253) (cmask pL1253) (hmask pL1253) 886 367 (true, L1253_cp1.1, L1253_cp1.2)) ∧ ptTest pL1253 (runFrom pL1253 (fmask pL1253) (cmask pL1253) (hmask pL1253) 886 367 (true, L1253_cp1.1, L1253_cp1.2)) 1253 627 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1253_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1253_fin) true) L1253_seg1) (by decide) rfl L1253_fin ptTest_fst
noncomputable def H1253_cp1 : Nat × Nat := t7val% (fastRun pH1253 1 885 (init pH1253) (init pH1253))
theorem H1253_seg1 : segOK pH1253 1 885 (init pH1253) (init pH1253) H1253_cp1.1 H1253_cp1.2 = true := by
  decide +kernel
theorem H1253_fin : (prmOK pH1253 1253 && ptTest pH1253 (runFrom pH1253 (fmask pH1253) (cmask pH1253) (hmask pH1253) 886 367 (true, H1253_cp1.1, H1253_cp1.2)) 1253 627 true) = true := by
  decide +kernel
theorem H1253_ok : RunOK pH1253 1253 (runFrom pH1253 (fmask pH1253) (cmask pH1253) (hmask pH1253) 886 367 (true, H1253_cp1.1, H1253_cp1.2)) ∧ ptTest pH1253 (runFrom pH1253 (fmask pH1253) (cmask pH1253) (hmask pH1253) 886 367 (true, H1253_cp1.1, H1253_cp1.2)) 1253 627 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1253_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1253_fin) true) H1253_seg1) (by decide) rfl H1253_fin ptTest_fst
theorem I1253_fin : (prmOK pI1253 1253 && intTest pI1253 (runFrom pI1253 (fmask pI1253) (cmask pI1253) (hmask pI1253) 1 1252 (true, (init pI1253), (init pI1253))) 1253 19 false) = true := by
  decide +kernel
theorem I1253_ok : RunOK pI1253 1253 (runFrom pI1253 (fmask pI1253) (cmask pI1253) (hmask pI1253) 1 1252 (true, (init pI1253), (init pI1253))) ∧ intTest pI1253 (runFrom pI1253 (fmask pI1253) (cmask pI1253) (hmask pI1253) 1 1252 (true, (init pI1253), (init pI1253))) 1253 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1253_fin) true) (by decide) rfl I1253_fin intTest_fst
theorem link1253 : linkOK pL1253 pH1253 pI1253 = true := by decide +kernel
theorem cvx1253 : ConvexBetweenHumps 1253 :=
  cvx_of L1253_ok H1253_ok I1253_ok link1253 (by decide)

/-! ### `N = 1254` -/

def pL1254 : Prm := ⟨77, 36, 38, 1256, 11, 18446744073709551616, 143882048462331544, 143882048462331544⟩
def pH1254 : Prm := ⟨77, 36, 38, 1256, 11, 18446744073709551616, 143884247485587096, 143884247485587096⟩
def pI1254 : Prm := ⟨66, 33, 30, 1256, 11, 18446744073709551616, 143882048462331544, 143884247485587096⟩
noncomputable def L1254_cp1 : Nat × Nat := t7val% (fastRun pL1254 1 886 (init pL1254) (init pL1254))
theorem L1254_seg1 : segOK pL1254 1 886 (init pL1254) (init pL1254) L1254_cp1.1 L1254_cp1.2 = true := by
  decide +kernel
theorem L1254_fin : (prmOK pL1254 1254 && ptTest pL1254 (runFrom pL1254 (fmask pL1254) (cmask pL1254) (hmask pL1254) 887 367 (true, L1254_cp1.1, L1254_cp1.2)) 1254 627 false) = true := by
  decide +kernel
theorem L1254_ok : RunOK pL1254 1254 (runFrom pL1254 (fmask pL1254) (cmask pL1254) (hmask pL1254) 887 367 (true, L1254_cp1.1, L1254_cp1.2)) ∧ ptTest pL1254 (runFrom pL1254 (fmask pL1254) (cmask pL1254) (hmask pL1254) 887 367 (true, L1254_cp1.1, L1254_cp1.2)) 1254 627 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1254_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1254_fin) true) L1254_seg1) (by decide) rfl L1254_fin ptTest_fst
noncomputable def H1254_cp1 : Nat × Nat := t7val% (fastRun pH1254 1 886 (init pH1254) (init pH1254))
theorem H1254_seg1 : segOK pH1254 1 886 (init pH1254) (init pH1254) H1254_cp1.1 H1254_cp1.2 = true := by
  decide +kernel
theorem H1254_fin : (prmOK pH1254 1254 && ptTest pH1254 (runFrom pH1254 (fmask pH1254) (cmask pH1254) (hmask pH1254) 887 367 (true, H1254_cp1.1, H1254_cp1.2)) 1254 627 true) = true := by
  decide +kernel
theorem H1254_ok : RunOK pH1254 1254 (runFrom pH1254 (fmask pH1254) (cmask pH1254) (hmask pH1254) 887 367 (true, H1254_cp1.1, H1254_cp1.2)) ∧ ptTest pH1254 (runFrom pH1254 (fmask pH1254) (cmask pH1254) (hmask pH1254) 887 367 (true, H1254_cp1.1, H1254_cp1.2)) 1254 627 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1254_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1254_fin) true) H1254_seg1) (by decide) rfl H1254_fin ptTest_fst
theorem I1254_fin : (prmOK pI1254 1254 && intTest pI1254 (runFrom pI1254 (fmask pI1254) (cmask pI1254) (hmask pI1254) 1 1253 (true, (init pI1254), (init pI1254))) 1254 19 true) = true := by
  decide +kernel
theorem I1254_ok : RunOK pI1254 1254 (runFrom pI1254 (fmask pI1254) (cmask pI1254) (hmask pI1254) 1 1253 (true, (init pI1254), (init pI1254))) ∧ intTest pI1254 (runFrom pI1254 (fmask pI1254) (cmask pI1254) (hmask pI1254) 1 1253 (true, (init pI1254), (init pI1254))) 1254 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1254_fin) true) (by decide) rfl I1254_fin intTest_fst
theorem link1254 : linkOK pL1254 pH1254 pI1254 = true := by decide +kernel
theorem cvx1254 : ConvexBetweenHumps 1254 :=
  cvx_of L1254_ok H1254_ok I1254_ok link1254 (by decide)
theorem cenlink1254 : cenLinkOK pI1254 1254 = true := by decide +kernel
theorem cen1254 : CenterUniqueMin 1254 ∧ DipHyp 1254 ∧ OnePointHyps 1254 :=
  cen_of L1254_ok H1254_ok I1254_ok link1254 cenlink1254

/-! ### `N = 1255` -/

def pL1255 : Prm := ⟨77, 36, 38, 1257, 11, 18446744073709551616, 143789467538342164, 143789467538342164⟩
def pH1255 : Prm := ⟨77, 36, 38, 1257, 11, 18446744073709551616, 143791666561597716, 143791666561597716⟩
def pI1255 : Prm := ⟨66, 33, 30, 1257, 11, 18446744073709551616, 143789467538342164, 143791666561597716⟩
noncomputable def L1255_cp1 : Nat × Nat := t7val% (fastRun pL1255 1 886 (init pL1255) (init pL1255))
theorem L1255_seg1 : segOK pL1255 1 886 (init pL1255) (init pL1255) L1255_cp1.1 L1255_cp1.2 = true := by
  decide +kernel
theorem L1255_fin : (prmOK pL1255 1255 && ptTest pL1255 (runFrom pL1255 (fmask pL1255) (cmask pL1255) (hmask pL1255) 887 368 (true, L1255_cp1.1, L1255_cp1.2)) 1255 628 false) = true := by
  decide +kernel
theorem L1255_ok : RunOK pL1255 1255 (runFrom pL1255 (fmask pL1255) (cmask pL1255) (hmask pL1255) 887 368 (true, L1255_cp1.1, L1255_cp1.2)) ∧ ptTest pL1255 (runFrom pL1255 (fmask pL1255) (cmask pL1255) (hmask pL1255) 887 368 (true, L1255_cp1.1, L1255_cp1.2)) 1255 628 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1255_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1255_fin) true) L1255_seg1) (by decide) rfl L1255_fin ptTest_fst
noncomputable def H1255_cp1 : Nat × Nat := t7val% (fastRun pH1255 1 886 (init pH1255) (init pH1255))
theorem H1255_seg1 : segOK pH1255 1 886 (init pH1255) (init pH1255) H1255_cp1.1 H1255_cp1.2 = true := by
  decide +kernel
theorem H1255_fin : (prmOK pH1255 1255 && ptTest pH1255 (runFrom pH1255 (fmask pH1255) (cmask pH1255) (hmask pH1255) 887 368 (true, H1255_cp1.1, H1255_cp1.2)) 1255 628 true) = true := by
  decide +kernel
theorem H1255_ok : RunOK pH1255 1255 (runFrom pH1255 (fmask pH1255) (cmask pH1255) (hmask pH1255) 887 368 (true, H1255_cp1.1, H1255_cp1.2)) ∧ ptTest pH1255 (runFrom pH1255 (fmask pH1255) (cmask pH1255) (hmask pH1255) 887 368 (true, H1255_cp1.1, H1255_cp1.2)) 1255 628 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1255_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1255_fin) true) H1255_seg1) (by decide) rfl H1255_fin ptTest_fst
theorem I1255_fin : (prmOK pI1255 1255 && intTest pI1255 (runFrom pI1255 (fmask pI1255) (cmask pI1255) (hmask pI1255) 1 1254 (true, (init pI1255), (init pI1255))) 1255 19 false) = true := by
  decide +kernel
theorem I1255_ok : RunOK pI1255 1255 (runFrom pI1255 (fmask pI1255) (cmask pI1255) (hmask pI1255) 1 1254 (true, (init pI1255), (init pI1255))) ∧ intTest pI1255 (runFrom pI1255 (fmask pI1255) (cmask pI1255) (hmask pI1255) 1 1254 (true, (init pI1255), (init pI1255))) 1255 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1255_fin) true) (by decide) rfl I1255_fin intTest_fst
theorem link1255 : linkOK pL1255 pH1255 pI1255 = true := by decide +kernel
theorem cvx1255 : ConvexBetweenHumps 1255 :=
  cvx_of L1255_ok H1255_ok I1255_ok link1255 (by decide)

/-! ### `N = 1256` -/

def pL1256 : Prm := ⟨77, 36, 38, 1258, 11, 18446744073709551616, 143697074174039678, 143697074174039678⟩
def pH1256 : Prm := ⟨77, 36, 38, 1258, 11, 18446744073709551616, 143699273197295230, 143699273197295230⟩
def pI1256 : Prm := ⟨66, 33, 30, 1258, 11, 18446744073709551616, 143697074174039678, 143699273197295230⟩
noncomputable def L1256_cp1 : Nat × Nat := t7val% (fastRun pL1256 1 887 (init pL1256) (init pL1256))
theorem L1256_seg1 : segOK pL1256 1 887 (init pL1256) (init pL1256) L1256_cp1.1 L1256_cp1.2 = true := by
  decide +kernel
theorem L1256_fin : (prmOK pL1256 1256 && ptTest pL1256 (runFrom pL1256 (fmask pL1256) (cmask pL1256) (hmask pL1256) 888 368 (true, L1256_cp1.1, L1256_cp1.2)) 1256 628 false) = true := by
  decide +kernel
theorem L1256_ok : RunOK pL1256 1256 (runFrom pL1256 (fmask pL1256) (cmask pL1256) (hmask pL1256) 888 368 (true, L1256_cp1.1, L1256_cp1.2)) ∧ ptTest pL1256 (runFrom pL1256 (fmask pL1256) (cmask pL1256) (hmask pL1256) 888 368 (true, L1256_cp1.1, L1256_cp1.2)) 1256 628 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1256_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1256_fin) true) L1256_seg1) (by decide) rfl L1256_fin ptTest_fst
noncomputable def H1256_cp1 : Nat × Nat := t7val% (fastRun pH1256 1 887 (init pH1256) (init pH1256))
theorem H1256_seg1 : segOK pH1256 1 887 (init pH1256) (init pH1256) H1256_cp1.1 H1256_cp1.2 = true := by
  decide +kernel
theorem H1256_fin : (prmOK pH1256 1256 && ptTest pH1256 (runFrom pH1256 (fmask pH1256) (cmask pH1256) (hmask pH1256) 888 368 (true, H1256_cp1.1, H1256_cp1.2)) 1256 628 true) = true := by
  decide +kernel
theorem H1256_ok : RunOK pH1256 1256 (runFrom pH1256 (fmask pH1256) (cmask pH1256) (hmask pH1256) 888 368 (true, H1256_cp1.1, H1256_cp1.2)) ∧ ptTest pH1256 (runFrom pH1256 (fmask pH1256) (cmask pH1256) (hmask pH1256) 888 368 (true, H1256_cp1.1, H1256_cp1.2)) 1256 628 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1256_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1256_fin) true) H1256_seg1) (by decide) rfl H1256_fin ptTest_fst
theorem I1256_fin : (prmOK pI1256 1256 && intTest pI1256 (runFrom pI1256 (fmask pI1256) (cmask pI1256) (hmask pI1256) 1 1255 (true, (init pI1256), (init pI1256))) 1256 19 true) = true := by
  decide +kernel
theorem I1256_ok : RunOK pI1256 1256 (runFrom pI1256 (fmask pI1256) (cmask pI1256) (hmask pI1256) 1 1255 (true, (init pI1256), (init pI1256))) ∧ intTest pI1256 (runFrom pI1256 (fmask pI1256) (cmask pI1256) (hmask pI1256) 1 1255 (true, (init pI1256), (init pI1256))) 1256 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1256_fin) true) (by decide) rfl I1256_fin intTest_fst
theorem link1256 : linkOK pL1256 pH1256 pI1256 = true := by decide +kernel
theorem cvx1256 : ConvexBetweenHumps 1256 :=
  cvx_of L1256_ok H1256_ok I1256_ok link1256 (by decide)
theorem cenlink1256 : cenLinkOK pI1256 1256 = true := by decide +kernel
theorem cen1256 : CenterUniqueMin 1256 ∧ DipHyp 1256 ∧ OnePointHyps 1256 :=
  cen_of L1256_ok H1256_ok I1256_ok link1256 cenlink1256

/-! ### `N = 1257` -/

def pL1257 : Prm := ⟨77, 36, 38, 1259, 11, 18446744073709551616, 143604752665560744, 143604752665560744⟩
def pH1257 : Prm := ⟨77, 36, 38, 1259, 11, 18446744073709551616, 143606951688816296, 143606951688816296⟩
def pI1257 : Prm := ⟨66, 33, 30, 1259, 11, 18446744073709551616, 143604752665560744, 143606951688816296⟩
noncomputable def L1257_cp1 : Nat × Nat := t7val% (fastRun pL1257 1 888 (init pL1257) (init pL1257))
theorem L1257_seg1 : segOK pL1257 1 888 (init pL1257) (init pL1257) L1257_cp1.1 L1257_cp1.2 = true := by
  decide +kernel
theorem L1257_fin : (prmOK pL1257 1257 && ptTest pL1257 (runFrom pL1257 (fmask pL1257) (cmask pL1257) (hmask pL1257) 889 368 (true, L1257_cp1.1, L1257_cp1.2)) 1257 629 false) = true := by
  decide +kernel
theorem L1257_ok : RunOK pL1257 1257 (runFrom pL1257 (fmask pL1257) (cmask pL1257) (hmask pL1257) 889 368 (true, L1257_cp1.1, L1257_cp1.2)) ∧ ptTest pL1257 (runFrom pL1257 (fmask pL1257) (cmask pL1257) (hmask pL1257) 889 368 (true, L1257_cp1.1, L1257_cp1.2)) 1257 629 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1257_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1257_fin) true) L1257_seg1) (by decide) rfl L1257_fin ptTest_fst
noncomputable def H1257_cp1 : Nat × Nat := t7val% (fastRun pH1257 1 888 (init pH1257) (init pH1257))
theorem H1257_seg1 : segOK pH1257 1 888 (init pH1257) (init pH1257) H1257_cp1.1 H1257_cp1.2 = true := by
  decide +kernel
theorem H1257_fin : (prmOK pH1257 1257 && ptTest pH1257 (runFrom pH1257 (fmask pH1257) (cmask pH1257) (hmask pH1257) 889 368 (true, H1257_cp1.1, H1257_cp1.2)) 1257 629 true) = true := by
  decide +kernel
theorem H1257_ok : RunOK pH1257 1257 (runFrom pH1257 (fmask pH1257) (cmask pH1257) (hmask pH1257) 889 368 (true, H1257_cp1.1, H1257_cp1.2)) ∧ ptTest pH1257 (runFrom pH1257 (fmask pH1257) (cmask pH1257) (hmask pH1257) 889 368 (true, H1257_cp1.1, H1257_cp1.2)) 1257 629 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1257_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1257_fin) true) H1257_seg1) (by decide) rfl H1257_fin ptTest_fst
theorem I1257_fin : (prmOK pI1257 1257 && intTest pI1257 (runFrom pI1257 (fmask pI1257) (cmask pI1257) (hmask pI1257) 1 1256 (true, (init pI1257), (init pI1257))) 1257 19 false) = true := by
  decide +kernel
theorem I1257_ok : RunOK pI1257 1257 (runFrom pI1257 (fmask pI1257) (cmask pI1257) (hmask pI1257) 1 1256 (true, (init pI1257), (init pI1257))) ∧ intTest pI1257 (runFrom pI1257 (fmask pI1257) (cmask pI1257) (hmask pI1257) 1 1256 (true, (init pI1257), (init pI1257))) 1257 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1257_fin) true) (by decide) rfl I1257_fin intTest_fst
theorem link1257 : linkOK pL1257 pH1257 pI1257 = true := by decide +kernel
theorem cvx1257 : ConvexBetweenHumps 1257 :=
  cvx_of L1257_ok H1257_ok I1257_ok link1257 (by decide)

/-! ### `N = 1258` -/

def pL1258 : Prm := ⟨77, 36, 38, 1260, 11, 18446744073709551616, 143512617873955412, 143512617873955412⟩
def pH1258 : Prm := ⟨77, 36, 38, 1260, 11, 18446744073709551616, 143514816897210964, 143514816897210964⟩
def pI1258 : Prm := ⟨66, 33, 30, 1260, 11, 18446744073709551616, 143512617873955412, 143514816897210964⟩
noncomputable def L1258_cp1 : Nat × Nat := t7val% (fastRun pL1258 1 889 (init pL1258) (init pL1258))
theorem L1258_seg1 : segOK pL1258 1 889 (init pL1258) (init pL1258) L1258_cp1.1 L1258_cp1.2 = true := by
  decide +kernel
theorem L1258_fin : (prmOK pL1258 1258 && ptTest pL1258 (runFrom pL1258 (fmask pL1258) (cmask pL1258) (hmask pL1258) 890 368 (true, L1258_cp1.1, L1258_cp1.2)) 1258 629 false) = true := by
  decide +kernel
theorem L1258_ok : RunOK pL1258 1258 (runFrom pL1258 (fmask pL1258) (cmask pL1258) (hmask pL1258) 890 368 (true, L1258_cp1.1, L1258_cp1.2)) ∧ ptTest pL1258 (runFrom pL1258 (fmask pL1258) (cmask pL1258) (hmask pL1258) 890 368 (true, L1258_cp1.1, L1258_cp1.2)) 1258 629 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1258_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1258_fin) true) L1258_seg1) (by decide) rfl L1258_fin ptTest_fst
noncomputable def H1258_cp1 : Nat × Nat := t7val% (fastRun pH1258 1 889 (init pH1258) (init pH1258))
theorem H1258_seg1 : segOK pH1258 1 889 (init pH1258) (init pH1258) H1258_cp1.1 H1258_cp1.2 = true := by
  decide +kernel
theorem H1258_fin : (prmOK pH1258 1258 && ptTest pH1258 (runFrom pH1258 (fmask pH1258) (cmask pH1258) (hmask pH1258) 890 368 (true, H1258_cp1.1, H1258_cp1.2)) 1258 629 true) = true := by
  decide +kernel
theorem H1258_ok : RunOK pH1258 1258 (runFrom pH1258 (fmask pH1258) (cmask pH1258) (hmask pH1258) 890 368 (true, H1258_cp1.1, H1258_cp1.2)) ∧ ptTest pH1258 (runFrom pH1258 (fmask pH1258) (cmask pH1258) (hmask pH1258) 890 368 (true, H1258_cp1.1, H1258_cp1.2)) 1258 629 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1258_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1258_fin) true) H1258_seg1) (by decide) rfl H1258_fin ptTest_fst
theorem I1258_fin : (prmOK pI1258 1258 && intTest pI1258 (runFrom pI1258 (fmask pI1258) (cmask pI1258) (hmask pI1258) 1 1257 (true, (init pI1258), (init pI1258))) 1258 19 true) = true := by
  decide +kernel
theorem I1258_ok : RunOK pI1258 1258 (runFrom pI1258 (fmask pI1258) (cmask pI1258) (hmask pI1258) 1 1257 (true, (init pI1258), (init pI1258))) ∧ intTest pI1258 (runFrom pI1258 (fmask pI1258) (cmask pI1258) (hmask pI1258) 1 1257 (true, (init pI1258), (init pI1258))) 1258 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1258_fin) true) (by decide) rfl I1258_fin intTest_fst
theorem link1258 : linkOK pL1258 pH1258 pI1258 = true := by decide +kernel
theorem cvx1258 : ConvexBetweenHumps 1258 :=
  cvx_of L1258_ok H1258_ok I1258_ok link1258 (by decide)
theorem cenlink1258 : cenLinkOK pI1258 1258 = true := by decide +kernel
theorem cen1258 : CenterUniqueMin 1258 ∧ DipHyp 1258 ∧ OnePointHyps 1258 :=
  cen_of L1258_ok H1258_ok I1258_ok link1258 cenlink1258

/-! ### `N = 1259` -/

def pL1259 : Prm := ⟨77, 36, 38, 1261, 11, 18446744073709551616, 143420554656252042, 143420554656252042⟩
def pH1259 : Prm := ⟨77, 36, 38, 1261, 11, 18446744073709551616, 143422753679507594, 143422753679507594⟩
def pI1259 : Prm := ⟨66, 33, 30, 1261, 11, 18446744073709551616, 143420554656252042, 143422753679507594⟩
noncomputable def L1259_cp1 : Nat × Nat := t7val% (fastRun pL1259 1 889 (init pL1259) (init pL1259))
theorem L1259_seg1 : segOK pL1259 1 889 (init pL1259) (init pL1259) L1259_cp1.1 L1259_cp1.2 = true := by
  decide +kernel
theorem L1259_fin : (prmOK pL1259 1259 && ptTest pL1259 (runFrom pL1259 (fmask pL1259) (cmask pL1259) (hmask pL1259) 890 369 (true, L1259_cp1.1, L1259_cp1.2)) 1259 630 false) = true := by
  decide +kernel
theorem L1259_ok : RunOK pL1259 1259 (runFrom pL1259 (fmask pL1259) (cmask pL1259) (hmask pL1259) 890 369 (true, L1259_cp1.1, L1259_cp1.2)) ∧ ptTest pL1259 (runFrom pL1259 (fmask pL1259) (cmask pL1259) (hmask pL1259) 890 369 (true, L1259_cp1.1, L1259_cp1.2)) 1259 630 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1259_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1259_fin) true) L1259_seg1) (by decide) rfl L1259_fin ptTest_fst
noncomputable def H1259_cp1 : Nat × Nat := t7val% (fastRun pH1259 1 889 (init pH1259) (init pH1259))
theorem H1259_seg1 : segOK pH1259 1 889 (init pH1259) (init pH1259) H1259_cp1.1 H1259_cp1.2 = true := by
  decide +kernel
theorem H1259_fin : (prmOK pH1259 1259 && ptTest pH1259 (runFrom pH1259 (fmask pH1259) (cmask pH1259) (hmask pH1259) 890 369 (true, H1259_cp1.1, H1259_cp1.2)) 1259 630 true) = true := by
  decide +kernel
theorem H1259_ok : RunOK pH1259 1259 (runFrom pH1259 (fmask pH1259) (cmask pH1259) (hmask pH1259) 890 369 (true, H1259_cp1.1, H1259_cp1.2)) ∧ ptTest pH1259 (runFrom pH1259 (fmask pH1259) (cmask pH1259) (hmask pH1259) 890 369 (true, H1259_cp1.1, H1259_cp1.2)) 1259 630 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1259_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1259_fin) true) H1259_seg1) (by decide) rfl H1259_fin ptTest_fst
theorem I1259_fin : (prmOK pI1259 1259 && intTest pI1259 (runFrom pI1259 (fmask pI1259) (cmask pI1259) (hmask pI1259) 1 1258 (true, (init pI1259), (init pI1259))) 1259 19 false) = true := by
  decide +kernel
theorem I1259_ok : RunOK pI1259 1259 (runFrom pI1259 (fmask pI1259) (cmask pI1259) (hmask pI1259) 1 1258 (true, (init pI1259), (init pI1259))) ∧ intTest pI1259 (runFrom pI1259 (fmask pI1259) (cmask pI1259) (hmask pI1259) 1 1258 (true, (init pI1259), (init pI1259))) 1259 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1259_fin) true) (by decide) rfl I1259_fin intTest_fst
theorem link1259 : linkOK pL1259 pH1259 pI1259 = true := by decide +kernel
theorem cvx1259 : ConvexBetweenHumps 1259 :=
  cvx_of L1259_ok H1259_ok I1259_ok link1259 (by decide)

/-! ### `N = 1260` -/

def pL1260 : Prm := ⟨77, 36, 38, 1262, 11, 18446744073709551616, 143328677317718732, 143328677317718732⟩
def pH1260 : Prm := ⟨77, 36, 38, 1262, 11, 18446744073709551616, 143330876340974284, 143330876340974284⟩
def pI1260 : Prm := ⟨66, 33, 30, 1262, 11, 18446744073709551616, 143328677317718732, 143330876340974284⟩
noncomputable def L1260_cp1 : Nat × Nat := t7val% (fastRun pL1260 1 890 (init pL1260) (init pL1260))
theorem L1260_seg1 : segOK pL1260 1 890 (init pL1260) (init pL1260) L1260_cp1.1 L1260_cp1.2 = true := by
  decide +kernel
theorem L1260_fin : (prmOK pL1260 1260 && ptTest pL1260 (runFrom pL1260 (fmask pL1260) (cmask pL1260) (hmask pL1260) 891 369 (true, L1260_cp1.1, L1260_cp1.2)) 1260 630 false) = true := by
  decide +kernel
theorem L1260_ok : RunOK pL1260 1260 (runFrom pL1260 (fmask pL1260) (cmask pL1260) (hmask pL1260) 891 369 (true, L1260_cp1.1, L1260_cp1.2)) ∧ ptTest pL1260 (runFrom pL1260 (fmask pL1260) (cmask pL1260) (hmask pL1260) 891 369 (true, L1260_cp1.1, L1260_cp1.2)) 1260 630 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1260_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1260_fin) true) L1260_seg1) (by decide) rfl L1260_fin ptTest_fst
noncomputable def H1260_cp1 : Nat × Nat := t7val% (fastRun pH1260 1 890 (init pH1260) (init pH1260))
theorem H1260_seg1 : segOK pH1260 1 890 (init pH1260) (init pH1260) H1260_cp1.1 H1260_cp1.2 = true := by
  decide +kernel
theorem H1260_fin : (prmOK pH1260 1260 && ptTest pH1260 (runFrom pH1260 (fmask pH1260) (cmask pH1260) (hmask pH1260) 891 369 (true, H1260_cp1.1, H1260_cp1.2)) 1260 630 true) = true := by
  decide +kernel
theorem H1260_ok : RunOK pH1260 1260 (runFrom pH1260 (fmask pH1260) (cmask pH1260) (hmask pH1260) 891 369 (true, H1260_cp1.1, H1260_cp1.2)) ∧ ptTest pH1260 (runFrom pH1260 (fmask pH1260) (cmask pH1260) (hmask pH1260) 891 369 (true, H1260_cp1.1, H1260_cp1.2)) 1260 630 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1260_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1260_fin) true) H1260_seg1) (by decide) rfl H1260_fin ptTest_fst
theorem I1260_fin : (prmOK pI1260 1260 && intTest pI1260 (runFrom pI1260 (fmask pI1260) (cmask pI1260) (hmask pI1260) 1 1259 (true, (init pI1260), (init pI1260))) 1260 19 true) = true := by
  decide +kernel
theorem I1260_ok : RunOK pI1260 1260 (runFrom pI1260 (fmask pI1260) (cmask pI1260) (hmask pI1260) 1 1259 (true, (init pI1260), (init pI1260))) ∧ intTest pI1260 (runFrom pI1260 (fmask pI1260) (cmask pI1260) (hmask pI1260) 1 1259 (true, (init pI1260), (init pI1260))) 1260 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1260_fin) true) (by decide) rfl I1260_fin intTest_fst
theorem link1260 : linkOK pL1260 pH1260 pI1260 = true := by decide +kernel
theorem cvx1260 : ConvexBetweenHumps 1260 :=
  cvx_of L1260_ok H1260_ok I1260_ok link1260 (by decide)
theorem cenlink1260 : cenLinkOK pI1260 1260 = true := by decide +kernel
theorem cen1260 : CenterUniqueMin 1260 ∧ DipHyp 1260 ∧ OnePointHyps 1260 :=
  cen_of L1260_ok H1260_ok I1260_ok link1260 cenlink1260

/-! ### `N = 1261` -/

def pL1261 : Prm := ⟨77, 36, 38, 1263, 11, 18446744073709551616, 143236871272641534, 143236871272641534⟩
def pH1261 : Prm := ⟨77, 36, 38, 1263, 11, 18446744073709551616, 143239070295897086, 143239070295897086⟩
def pI1261 : Prm := ⟨66, 33, 30, 1263, 11, 18446744073709551616, 143236871272641534, 143239070295897086⟩
noncomputable def L1261_cp1 : Nat × Nat := t7val% (fastRun pL1261 1 891 (init pL1261) (init pL1261))
theorem L1261_seg1 : segOK pL1261 1 891 (init pL1261) (init pL1261) L1261_cp1.1 L1261_cp1.2 = true := by
  decide +kernel
theorem L1261_fin : (prmOK pL1261 1261 && ptTest pL1261 (runFrom pL1261 (fmask pL1261) (cmask pL1261) (hmask pL1261) 892 369 (true, L1261_cp1.1, L1261_cp1.2)) 1261 631 false) = true := by
  decide +kernel
theorem L1261_ok : RunOK pL1261 1261 (runFrom pL1261 (fmask pL1261) (cmask pL1261) (hmask pL1261) 892 369 (true, L1261_cp1.1, L1261_cp1.2)) ∧ ptTest pL1261 (runFrom pL1261 (fmask pL1261) (cmask pL1261) (hmask pL1261) 892 369 (true, L1261_cp1.1, L1261_cp1.2)) 1261 631 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1261_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1261_fin) true) L1261_seg1) (by decide) rfl L1261_fin ptTest_fst
noncomputable def H1261_cp1 : Nat × Nat := t7val% (fastRun pH1261 1 891 (init pH1261) (init pH1261))
theorem H1261_seg1 : segOK pH1261 1 891 (init pH1261) (init pH1261) H1261_cp1.1 H1261_cp1.2 = true := by
  decide +kernel
theorem H1261_fin : (prmOK pH1261 1261 && ptTest pH1261 (runFrom pH1261 (fmask pH1261) (cmask pH1261) (hmask pH1261) 892 369 (true, H1261_cp1.1, H1261_cp1.2)) 1261 631 true) = true := by
  decide +kernel
theorem H1261_ok : RunOK pH1261 1261 (runFrom pH1261 (fmask pH1261) (cmask pH1261) (hmask pH1261) 892 369 (true, H1261_cp1.1, H1261_cp1.2)) ∧ ptTest pH1261 (runFrom pH1261 (fmask pH1261) (cmask pH1261) (hmask pH1261) 892 369 (true, H1261_cp1.1, H1261_cp1.2)) 1261 631 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1261_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1261_fin) true) H1261_seg1) (by decide) rfl H1261_fin ptTest_fst
theorem I1261_fin : (prmOK pI1261 1261 && intTest pI1261 (runFrom pI1261 (fmask pI1261) (cmask pI1261) (hmask pI1261) 1 1260 (true, (init pI1261), (init pI1261))) 1261 19 false) = true := by
  decide +kernel
theorem I1261_ok : RunOK pI1261 1261 (runFrom pI1261 (fmask pI1261) (cmask pI1261) (hmask pI1261) 1 1260 (true, (init pI1261), (init pI1261))) ∧ intTest pI1261 (runFrom pI1261 (fmask pI1261) (cmask pI1261) (hmask pI1261) 1 1260 (true, (init pI1261), (init pI1261))) 1261 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1261_fin) true) (by decide) rfl I1261_fin intTest_fst
theorem link1261 : linkOK pL1261 pH1261 pI1261 = true := by decide +kernel
theorem cvx1261 : ConvexBetweenHumps 1261 :=
  cvx_of L1261_ok H1261_ok I1261_ok link1261 (by decide)

/-! ### `N = 1262` -/

def pL1262 : Prm := ⟨77, 36, 38, 1264, 11, 18446744073709551616, 143145250274122157, 143145250274122157⟩
def pH1262 : Prm := ⟨77, 36, 38, 1264, 11, 18446744073709551616, 143147449297377709, 143147449297377709⟩
def pI1262 : Prm := ⟨66, 33, 30, 1264, 11, 18446744073709551616, 143145250274122157, 143147449297377709⟩
noncomputable def L1262_cp1 : Nat × Nat := t7val% (fastRun pL1262 1 891 (init pL1262) (init pL1262))
theorem L1262_seg1 : segOK pL1262 1 891 (init pL1262) (init pL1262) L1262_cp1.1 L1262_cp1.2 = true := by
  decide +kernel
theorem L1262_fin : (prmOK pL1262 1262 && ptTest pL1262 (runFrom pL1262 (fmask pL1262) (cmask pL1262) (hmask pL1262) 892 370 (true, L1262_cp1.1, L1262_cp1.2)) 1262 631 false) = true := by
  decide +kernel
theorem L1262_ok : RunOK pL1262 1262 (runFrom pL1262 (fmask pL1262) (cmask pL1262) (hmask pL1262) 892 370 (true, L1262_cp1.1, L1262_cp1.2)) ∧ ptTest pL1262 (runFrom pL1262 (fmask pL1262) (cmask pL1262) (hmask pL1262) 892 370 (true, L1262_cp1.1, L1262_cp1.2)) 1262 631 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1262_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1262_fin) true) L1262_seg1) (by decide) rfl L1262_fin ptTest_fst
noncomputable def H1262_cp1 : Nat × Nat := t7val% (fastRun pH1262 1 891 (init pH1262) (init pH1262))
theorem H1262_seg1 : segOK pH1262 1 891 (init pH1262) (init pH1262) H1262_cp1.1 H1262_cp1.2 = true := by
  decide +kernel
theorem H1262_fin : (prmOK pH1262 1262 && ptTest pH1262 (runFrom pH1262 (fmask pH1262) (cmask pH1262) (hmask pH1262) 892 370 (true, H1262_cp1.1, H1262_cp1.2)) 1262 631 true) = true := by
  decide +kernel
theorem H1262_ok : RunOK pH1262 1262 (runFrom pH1262 (fmask pH1262) (cmask pH1262) (hmask pH1262) 892 370 (true, H1262_cp1.1, H1262_cp1.2)) ∧ ptTest pH1262 (runFrom pH1262 (fmask pH1262) (cmask pH1262) (hmask pH1262) 892 370 (true, H1262_cp1.1, H1262_cp1.2)) 1262 631 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1262_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1262_fin) true) H1262_seg1) (by decide) rfl H1262_fin ptTest_fst
theorem I1262_fin : (prmOK pI1262 1262 && intTest pI1262 (runFrom pI1262 (fmask pI1262) (cmask pI1262) (hmask pI1262) 1 1261 (true, (init pI1262), (init pI1262))) 1262 19 true) = true := by
  decide +kernel
theorem I1262_ok : RunOK pI1262 1262 (runFrom pI1262 (fmask pI1262) (cmask pI1262) (hmask pI1262) 1 1261 (true, (init pI1262), (init pI1262))) ∧ intTest pI1262 (runFrom pI1262 (fmask pI1262) (cmask pI1262) (hmask pI1262) 1 1261 (true, (init pI1262), (init pI1262))) 1262 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1262_fin) true) (by decide) rfl I1262_fin intTest_fst
theorem link1262 : linkOK pL1262 pH1262 pI1262 = true := by decide +kernel
theorem cvx1262 : ConvexBetweenHumps 1262 :=
  cvx_of L1262_ok H1262_ok I1262_ok link1262 (by decide)
theorem cenlink1262 : cenLinkOK pI1262 1262 = true := by decide +kernel
theorem cen1262 : CenterUniqueMin 1262 ∧ DipHyp 1262 ∧ OnePointHyps 1262 :=
  cen_of L1262_ok H1262_ok I1262_ok link1262 cenlink1262

/-! ### `N = 1263` -/

def pL1263 : Prm := ⟨77, 36, 38, 1265, 11, 18446744073709551616, 143053700290125674, 143053700290125674⟩
def pH1263 : Prm := ⟨77, 36, 38, 1265, 11, 18446744073709551616, 143055899313381226, 143055899313381226⟩
def pI1263 : Prm := ⟨66, 33, 30, 1265, 11, 18446744073709551616, 143053700290125674, 143055899313381226⟩
noncomputable def L1263_cp1 : Nat × Nat := t7val% (fastRun pL1263 1 892 (init pL1263) (init pL1263))
theorem L1263_seg1 : segOK pL1263 1 892 (init pL1263) (init pL1263) L1263_cp1.1 L1263_cp1.2 = true := by
  decide +kernel
theorem L1263_fin : (prmOK pL1263 1263 && ptTest pL1263 (runFrom pL1263 (fmask pL1263) (cmask pL1263) (hmask pL1263) 893 370 (true, L1263_cp1.1, L1263_cp1.2)) 1263 632 false) = true := by
  decide +kernel
theorem L1263_ok : RunOK pL1263 1263 (runFrom pL1263 (fmask pL1263) (cmask pL1263) (hmask pL1263) 893 370 (true, L1263_cp1.1, L1263_cp1.2)) ∧ ptTest pL1263 (runFrom pL1263 (fmask pL1263) (cmask pL1263) (hmask pL1263) 893 370 (true, L1263_cp1.1, L1263_cp1.2)) 1263 632 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1263_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1263_fin) true) L1263_seg1) (by decide) rfl L1263_fin ptTest_fst
noncomputable def H1263_cp1 : Nat × Nat := t7val% (fastRun pH1263 1 892 (init pH1263) (init pH1263))
theorem H1263_seg1 : segOK pH1263 1 892 (init pH1263) (init pH1263) H1263_cp1.1 H1263_cp1.2 = true := by
  decide +kernel
theorem H1263_fin : (prmOK pH1263 1263 && ptTest pH1263 (runFrom pH1263 (fmask pH1263) (cmask pH1263) (hmask pH1263) 893 370 (true, H1263_cp1.1, H1263_cp1.2)) 1263 632 true) = true := by
  decide +kernel
theorem H1263_ok : RunOK pH1263 1263 (runFrom pH1263 (fmask pH1263) (cmask pH1263) (hmask pH1263) 893 370 (true, H1263_cp1.1, H1263_cp1.2)) ∧ ptTest pH1263 (runFrom pH1263 (fmask pH1263) (cmask pH1263) (hmask pH1263) 893 370 (true, H1263_cp1.1, H1263_cp1.2)) 1263 632 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1263_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1263_fin) true) H1263_seg1) (by decide) rfl H1263_fin ptTest_fst
theorem I1263_fin : (prmOK pI1263 1263 && intTest pI1263 (runFrom pI1263 (fmask pI1263) (cmask pI1263) (hmask pI1263) 1 1262 (true, (init pI1263), (init pI1263))) 1263 19 false) = true := by
  decide +kernel
theorem I1263_ok : RunOK pI1263 1263 (runFrom pI1263 (fmask pI1263) (cmask pI1263) (hmask pI1263) 1 1262 (true, (init pI1263), (init pI1263))) ∧ intTest pI1263 (runFrom pI1263 (fmask pI1263) (cmask pI1263) (hmask pI1263) 1 1262 (true, (init pI1263), (init pI1263))) 1263 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1263_fin) true) (by decide) rfl I1263_fin intTest_fst
theorem link1263 : linkOK pL1263 pH1263 pI1263 = true := by decide +kernel
theorem cvx1263 : ConvexBetweenHumps 1263 :=
  cvx_of L1263_ok H1263_ok I1263_ok link1263 (by decide)

/-! ### `N = 1264` -/

def pL1264 : Prm := ⟨77, 36, 38, 1266, 11, 18446744073709551616, 142962334525073839, 142962334525073839⟩
def pH1264 : Prm := ⟨77, 36, 38, 1266, 11, 18446744073709551616, 142964533548329391, 142964533548329391⟩
def pI1264 : Prm := ⟨66, 33, 30, 1266, 11, 18446744073709551616, 142962334525073839, 142964533548329391⟩
noncomputable def L1264_cp1 : Nat × Nat := t7val% (fastRun pL1264 1 893 (init pL1264) (init pL1264))
theorem L1264_seg1 : segOK pL1264 1 893 (init pL1264) (init pL1264) L1264_cp1.1 L1264_cp1.2 = true := by
  decide +kernel
theorem L1264_fin : (prmOK pL1264 1264 && ptTest pL1264 (runFrom pL1264 (fmask pL1264) (cmask pL1264) (hmask pL1264) 894 370 (true, L1264_cp1.1, L1264_cp1.2)) 1264 632 false) = true := by
  decide +kernel
theorem L1264_ok : RunOK pL1264 1264 (runFrom pL1264 (fmask pL1264) (cmask pL1264) (hmask pL1264) 894 370 (true, L1264_cp1.1, L1264_cp1.2)) ∧ ptTest pL1264 (runFrom pL1264 (fmask pL1264) (cmask pL1264) (hmask pL1264) 894 370 (true, L1264_cp1.1, L1264_cp1.2)) 1264 632 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1264_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1264_fin) true) L1264_seg1) (by decide) rfl L1264_fin ptTest_fst
noncomputable def H1264_cp1 : Nat × Nat := t7val% (fastRun pH1264 1 893 (init pH1264) (init pH1264))
theorem H1264_seg1 : segOK pH1264 1 893 (init pH1264) (init pH1264) H1264_cp1.1 H1264_cp1.2 = true := by
  decide +kernel
theorem H1264_fin : (prmOK pH1264 1264 && ptTest pH1264 (runFrom pH1264 (fmask pH1264) (cmask pH1264) (hmask pH1264) 894 370 (true, H1264_cp1.1, H1264_cp1.2)) 1264 632 true) = true := by
  decide +kernel
theorem H1264_ok : RunOK pH1264 1264 (runFrom pH1264 (fmask pH1264) (cmask pH1264) (hmask pH1264) 894 370 (true, H1264_cp1.1, H1264_cp1.2)) ∧ ptTest pH1264 (runFrom pH1264 (fmask pH1264) (cmask pH1264) (hmask pH1264) 894 370 (true, H1264_cp1.1, H1264_cp1.2)) 1264 632 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1264_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1264_fin) true) H1264_seg1) (by decide) rfl H1264_fin ptTest_fst
theorem I1264_fin : (prmOK pI1264 1264 && intTest pI1264 (runFrom pI1264 (fmask pI1264) (cmask pI1264) (hmask pI1264) 1 1263 (true, (init pI1264), (init pI1264))) 1264 19 true) = true := by
  decide +kernel
theorem I1264_ok : RunOK pI1264 1264 (runFrom pI1264 (fmask pI1264) (cmask pI1264) (hmask pI1264) 1 1263 (true, (init pI1264), (init pI1264))) ∧ intTest pI1264 (runFrom pI1264 (fmask pI1264) (cmask pI1264) (hmask pI1264) 1 1263 (true, (init pI1264), (init pI1264))) 1264 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1264_fin) true) (by decide) rfl I1264_fin intTest_fst
theorem link1264 : linkOK pL1264 pH1264 pI1264 = true := by decide +kernel
theorem cvx1264 : ConvexBetweenHumps 1264 :=
  cvx_of L1264_ok H1264_ok I1264_ok link1264 (by decide)
theorem cenlink1264 : cenLinkOK pI1264 1264 = true := by decide +kernel
theorem cen1264 : CenterUniqueMin 1264 ∧ DipHyp 1264 ∧ OnePointHyps 1264 :=
  cen_of L1264_ok H1264_ok I1264_ok link1264 cenlink1264

/-! ### `N = 1265` -/

def pL1265 : Prm := ⟨77, 36, 38, 1267, 11, 18446744073709551616, 142871039497105867, 142871039497105867⟩
def pH1265 : Prm := ⟨77, 36, 38, 1267, 11, 18446744073709551616, 142873238520361419, 142873238520361419⟩
def pI1265 : Prm := ⟨66, 33, 30, 1267, 11, 18446744073709551616, 142871039497105867, 142873238520361419⟩
noncomputable def L1265_cp1 : Nat × Nat := t7val% (fastRun pL1265 1 893 (init pL1265) (init pL1265))
theorem L1265_seg1 : segOK pL1265 1 893 (init pL1265) (init pL1265) L1265_cp1.1 L1265_cp1.2 = true := by
  decide +kernel
theorem L1265_fin : (prmOK pL1265 1265 && ptTest pL1265 (runFrom pL1265 (fmask pL1265) (cmask pL1265) (hmask pL1265) 894 371 (true, L1265_cp1.1, L1265_cp1.2)) 1265 633 false) = true := by
  decide +kernel
theorem L1265_ok : RunOK pL1265 1265 (runFrom pL1265 (fmask pL1265) (cmask pL1265) (hmask pL1265) 894 371 (true, L1265_cp1.1, L1265_cp1.2)) ∧ ptTest pL1265 (runFrom pL1265 (fmask pL1265) (cmask pL1265) (hmask pL1265) 894 371 (true, L1265_cp1.1, L1265_cp1.2)) 1265 633 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1265_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1265_fin) true) L1265_seg1) (by decide) rfl L1265_fin ptTest_fst
noncomputable def H1265_cp1 : Nat × Nat := t7val% (fastRun pH1265 1 893 (init pH1265) (init pH1265))
theorem H1265_seg1 : segOK pH1265 1 893 (init pH1265) (init pH1265) H1265_cp1.1 H1265_cp1.2 = true := by
  decide +kernel
theorem H1265_fin : (prmOK pH1265 1265 && ptTest pH1265 (runFrom pH1265 (fmask pH1265) (cmask pH1265) (hmask pH1265) 894 371 (true, H1265_cp1.1, H1265_cp1.2)) 1265 633 true) = true := by
  decide +kernel
theorem H1265_ok : RunOK pH1265 1265 (runFrom pH1265 (fmask pH1265) (cmask pH1265) (hmask pH1265) 894 371 (true, H1265_cp1.1, H1265_cp1.2)) ∧ ptTest pH1265 (runFrom pH1265 (fmask pH1265) (cmask pH1265) (hmask pH1265) 894 371 (true, H1265_cp1.1, H1265_cp1.2)) 1265 633 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1265_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1265_fin) true) H1265_seg1) (by decide) rfl H1265_fin ptTest_fst
theorem I1265_fin : (prmOK pI1265 1265 && intTest pI1265 (runFrom pI1265 (fmask pI1265) (cmask pI1265) (hmask pI1265) 1 1264 (true, (init pI1265), (init pI1265))) 1265 19 false) = true := by
  decide +kernel
theorem I1265_ok : RunOK pI1265 1265 (runFrom pI1265 (fmask pI1265) (cmask pI1265) (hmask pI1265) 1 1264 (true, (init pI1265), (init pI1265))) ∧ intTest pI1265 (runFrom pI1265 (fmask pI1265) (cmask pI1265) (hmask pI1265) 1 1264 (true, (init pI1265), (init pI1265))) 1265 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1265_fin) true) (by decide) rfl I1265_fin intTest_fst
theorem link1265 : linkOK pL1265 pH1265 pI1265 = true := by decide +kernel
theorem cvx1265 : ConvexBetweenHumps 1265 :=
  cvx_of L1265_ok H1265_ok I1265_ok link1265 (by decide)

/-! ### The range -/

theorem cvx_1240_1265 {N : ℕ} (h1 : 1240 ≤ N) (h2 : N ≤ 1265) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1252
  · by_cases h4 : N ≤ 1245
    · by_cases h6 : N ≤ 1242
      · by_cases h8 : N ≤ 1240
        · obtain rfl : N = 1240 := by omega
          exact cvx1240
        · by_cases h10 : N ≤ 1241
          · obtain rfl : N = 1241 := by omega
            exact cvx1241
          · obtain rfl : N = 1242 := by omega
            exact cvx1242
      · by_cases h8 : N ≤ 1243
        · obtain rfl : N = 1243 := by omega
          exact cvx1243
        · by_cases h10 : N ≤ 1244
          · obtain rfl : N = 1244 := by omega
            exact cvx1244
          · obtain rfl : N = 1245 := by omega
            exact cvx1245
    · by_cases h6 : N ≤ 1248
      · by_cases h8 : N ≤ 1246
        · obtain rfl : N = 1246 := by omega
          exact cvx1246
        · by_cases h10 : N ≤ 1247
          · obtain rfl : N = 1247 := by omega
            exact cvx1247
          · obtain rfl : N = 1248 := by omega
            exact cvx1248
      · by_cases h8 : N ≤ 1250
        · by_cases h10 : N ≤ 1249
          · obtain rfl : N = 1249 := by omega
            exact cvx1249
          · obtain rfl : N = 1250 := by omega
            exact cvx1250
        · by_cases h10 : N ≤ 1251
          · obtain rfl : N = 1251 := by omega
            exact cvx1251
          · obtain rfl : N = 1252 := by omega
            exact cvx1252
  · by_cases h4 : N ≤ 1258
    · by_cases h6 : N ≤ 1255
      · by_cases h8 : N ≤ 1253
        · obtain rfl : N = 1253 := by omega
          exact cvx1253
        · by_cases h10 : N ≤ 1254
          · obtain rfl : N = 1254 := by omega
            exact cvx1254
          · obtain rfl : N = 1255 := by omega
            exact cvx1255
      · by_cases h8 : N ≤ 1256
        · obtain rfl : N = 1256 := by omega
          exact cvx1256
        · by_cases h10 : N ≤ 1257
          · obtain rfl : N = 1257 := by omega
            exact cvx1257
          · obtain rfl : N = 1258 := by omega
            exact cvx1258
    · by_cases h6 : N ≤ 1261
      · by_cases h8 : N ≤ 1259
        · obtain rfl : N = 1259 := by omega
          exact cvx1259
        · by_cases h10 : N ≤ 1260
          · obtain rfl : N = 1260 := by omega
            exact cvx1260
          · obtain rfl : N = 1261 := by omega
            exact cvx1261
      · by_cases h8 : N ≤ 1263
        · by_cases h10 : N ≤ 1262
          · obtain rfl : N = 1262 := by omega
            exact cvx1262
          · obtain rfl : N = 1263 := by omega
            exact cvx1263
        · by_cases h10 : N ≤ 1264
          · obtain rfl : N = 1264 := by omega
            exact cvx1264
          · obtain rfl : N = 1265 := by omega
            exact cvx1265

theorem cen_1240_1265 {N : ℕ} (h1 : 1240 ≤ N) (h2 : N ≤ 1265) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1250
  · by_cases h4 : N ≤ 1244
    · by_cases h6 : N ≤ 1240
      · obtain rfl : N = 1240 := by omega
        exact cen1240
      · by_cases h8 : N ≤ 1242
        · obtain rfl : N = 1242 := by omega
          exact cen1242
        · obtain rfl : N = 1244 := by omega
          exact cen1244
    · by_cases h6 : N ≤ 1246
      · obtain rfl : N = 1246 := by omega
        exact cen1246
      · by_cases h8 : N ≤ 1248
        · obtain rfl : N = 1248 := by omega
          exact cen1248
        · obtain rfl : N = 1250 := by omega
          exact cen1250
  · by_cases h4 : N ≤ 1256
    · by_cases h6 : N ≤ 1252
      · obtain rfl : N = 1252 := by omega
        exact cen1252
      · by_cases h8 : N ≤ 1254
        · obtain rfl : N = 1254 := by omega
          exact cen1254
        · obtain rfl : N = 1256 := by omega
          exact cen1256
    · by_cases h6 : N ≤ 1260
      · by_cases h8 : N ≤ 1258
        · obtain rfl : N = 1258 := by omega
          exact cen1258
        · obtain rfl : N = 1260 := by omega
          exact cen1260
      · by_cases h8 : N ≤ 1262
        · obtain rfl : N = 1262 := by omega
          exact cen1262
        · obtain rfl : N = 1264 := by omega
          exact cen1264

end Kagey131.PaperD.T7
