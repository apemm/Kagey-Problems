import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1266, …, 1290` (generated)

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

/-! ### `N = 1266` -/

def pL1266 : Prm := ⟨77, 36, 38, 1268, 11, 18446744073709551616, 142779927865449991, 142779927865449991⟩
def pH1266 : Prm := ⟨77, 36, 38, 1268, 11, 18446744073709551616, 142782126888705543, 142782126888705543⟩
def pI1266 : Prm := ⟨66, 33, 30, 1268, 11, 18446744073709551616, 142779927865449991, 142782126888705543⟩
noncomputable def L1266_cp1 : Nat × Nat := t7val% (fastRun pL1266 1 894 (init pL1266) (init pL1266))
theorem L1266_seg1 : segOK pL1266 1 894 (init pL1266) (init pL1266) L1266_cp1.1 L1266_cp1.2 = true := by
  decide +kernel
theorem L1266_fin : (prmOK pL1266 1266 && ptTest pL1266 (runFrom pL1266 (fmask pL1266) (cmask pL1266) (hmask pL1266) 895 371 (true, L1266_cp1.1, L1266_cp1.2)) 1266 633 false) = true := by
  decide +kernel
theorem L1266_ok : RunOK pL1266 1266 (runFrom pL1266 (fmask pL1266) (cmask pL1266) (hmask pL1266) 895 371 (true, L1266_cp1.1, L1266_cp1.2)) ∧ ptTest pL1266 (runFrom pL1266 (fmask pL1266) (cmask pL1266) (hmask pL1266) 895 371 (true, L1266_cp1.1, L1266_cp1.2)) 1266 633 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1266_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1266_fin) true) L1266_seg1) (by decide) rfl L1266_fin ptTest_fst
noncomputable def H1266_cp1 : Nat × Nat := t7val% (fastRun pH1266 1 894 (init pH1266) (init pH1266))
theorem H1266_seg1 : segOK pH1266 1 894 (init pH1266) (init pH1266) H1266_cp1.1 H1266_cp1.2 = true := by
  decide +kernel
theorem H1266_fin : (prmOK pH1266 1266 && ptTest pH1266 (runFrom pH1266 (fmask pH1266) (cmask pH1266) (hmask pH1266) 895 371 (true, H1266_cp1.1, H1266_cp1.2)) 1266 633 true) = true := by
  decide +kernel
theorem H1266_ok : RunOK pH1266 1266 (runFrom pH1266 (fmask pH1266) (cmask pH1266) (hmask pH1266) 895 371 (true, H1266_cp1.1, H1266_cp1.2)) ∧ ptTest pH1266 (runFrom pH1266 (fmask pH1266) (cmask pH1266) (hmask pH1266) 895 371 (true, H1266_cp1.1, H1266_cp1.2)) 1266 633 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1266_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1266_fin) true) H1266_seg1) (by decide) rfl H1266_fin ptTest_fst
theorem I1266_fin : (prmOK pI1266 1266 && intTest pI1266 (runFrom pI1266 (fmask pI1266) (cmask pI1266) (hmask pI1266) 1 1265 (true, (init pI1266), (init pI1266))) 1266 19 true) = true := by
  decide +kernel
theorem I1266_ok : RunOK pI1266 1266 (runFrom pI1266 (fmask pI1266) (cmask pI1266) (hmask pI1266) 1 1265 (true, (init pI1266), (init pI1266))) ∧ intTest pI1266 (runFrom pI1266 (fmask pI1266) (cmask pI1266) (hmask pI1266) 1 1265 (true, (init pI1266), (init pI1266))) 1266 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1266_fin) true) (by decide) rfl I1266_fin intTest_fst
theorem link1266 : linkOK pL1266 pH1266 pI1266 = true := by decide +kernel
theorem cvx1266 : ConvexBetweenHumps 1266 :=
  cvx_of L1266_ok H1266_ok I1266_ok link1266 (by decide)
theorem cenlink1266 : cenLinkOK pI1266 1266 = true := by decide +kernel
theorem cen1266 : CenterUniqueMin 1266 ∧ DipHyp 1266 ∧ OnePointHyps 1266 :=
  cen_of L1266_ok H1266_ok I1266_ok link1266 cenlink1266

/-! ### `N = 1267` -/

def pL1267 : Prm := ⟨77, 36, 38, 1269, 11, 18446744073709551616, 142688886694896240, 142688886694896240⟩
def pH1267 : Prm := ⟨77, 36, 38, 1269, 11, 18446744073709551616, 142691085718151792, 142691085718151792⟩
def pI1267 : Prm := ⟨66, 33, 30, 1269, 11, 18446744073709551616, 142688886694896240, 142691085718151792⟩
noncomputable def L1267_cp1 : Nat × Nat := t7val% (fastRun pL1267 1 895 (init pL1267) (init pL1267))
theorem L1267_seg1 : segOK pL1267 1 895 (init pL1267) (init pL1267) L1267_cp1.1 L1267_cp1.2 = true := by
  decide +kernel
theorem L1267_fin : (prmOK pL1267 1267 && ptTest pL1267 (runFrom pL1267 (fmask pL1267) (cmask pL1267) (hmask pL1267) 896 371 (true, L1267_cp1.1, L1267_cp1.2)) 1267 634 false) = true := by
  decide +kernel
theorem L1267_ok : RunOK pL1267 1267 (runFrom pL1267 (fmask pL1267) (cmask pL1267) (hmask pL1267) 896 371 (true, L1267_cp1.1, L1267_cp1.2)) ∧ ptTest pL1267 (runFrom pL1267 (fmask pL1267) (cmask pL1267) (hmask pL1267) 896 371 (true, L1267_cp1.1, L1267_cp1.2)) 1267 634 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1267_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1267_fin) true) L1267_seg1) (by decide) rfl L1267_fin ptTest_fst
noncomputable def H1267_cp1 : Nat × Nat := t7val% (fastRun pH1267 1 895 (init pH1267) (init pH1267))
theorem H1267_seg1 : segOK pH1267 1 895 (init pH1267) (init pH1267) H1267_cp1.1 H1267_cp1.2 = true := by
  decide +kernel
theorem H1267_fin : (prmOK pH1267 1267 && ptTest pH1267 (runFrom pH1267 (fmask pH1267) (cmask pH1267) (hmask pH1267) 896 371 (true, H1267_cp1.1, H1267_cp1.2)) 1267 634 true) = true := by
  decide +kernel
theorem H1267_ok : RunOK pH1267 1267 (runFrom pH1267 (fmask pH1267) (cmask pH1267) (hmask pH1267) 896 371 (true, H1267_cp1.1, H1267_cp1.2)) ∧ ptTest pH1267 (runFrom pH1267 (fmask pH1267) (cmask pH1267) (hmask pH1267) 896 371 (true, H1267_cp1.1, H1267_cp1.2)) 1267 634 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1267_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1267_fin) true) H1267_seg1) (by decide) rfl H1267_fin ptTest_fst
theorem I1267_fin : (prmOK pI1267 1267 && intTest pI1267 (runFrom pI1267 (fmask pI1267) (cmask pI1267) (hmask pI1267) 1 1266 (true, (init pI1267), (init pI1267))) 1267 19 false) = true := by
  decide +kernel
theorem I1267_ok : RunOK pI1267 1267 (runFrom pI1267 (fmask pI1267) (cmask pI1267) (hmask pI1267) 1 1266 (true, (init pI1267), (init pI1267))) ∧ intTest pI1267 (runFrom pI1267 (fmask pI1267) (cmask pI1267) (hmask pI1267) 1 1266 (true, (init pI1267), (init pI1267))) 1267 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1267_fin) true) (by decide) rfl I1267_fin intTest_fst
theorem link1267 : linkOK pL1267 pH1267 pI1267 = true := by decide +kernel
theorem cvx1267 : ConvexBetweenHumps 1267 :=
  cvx_of L1267_ok H1267_ok I1267_ok link1267 (by decide)

/-! ### `N = 1268` -/

def pL1268 : Prm := ⟨77, 36, 38, 1270, 11, 18446744073709551616, 142598028103021101, 142598028103021101⟩
def pH1268 : Prm := ⟨77, 36, 38, 1270, 11, 18446744073709551616, 142600227126276653, 142600227126276653⟩
def pI1268 : Prm := ⟨66, 33, 30, 1270, 11, 18446744073709551616, 142598028103021101, 142600227126276653⟩
noncomputable def L1268_cp1 : Nat × Nat := t7val% (fastRun pL1268 1 896 (init pL1268) (init pL1268))
theorem L1268_seg1 : segOK pL1268 1 896 (init pL1268) (init pL1268) L1268_cp1.1 L1268_cp1.2 = true := by
  decide +kernel
theorem L1268_fin : (prmOK pL1268 1268 && ptTest pL1268 (runFrom pL1268 (fmask pL1268) (cmask pL1268) (hmask pL1268) 897 371 (true, L1268_cp1.1, L1268_cp1.2)) 1268 634 false) = true := by
  decide +kernel
theorem L1268_ok : RunOK pL1268 1268 (runFrom pL1268 (fmask pL1268) (cmask pL1268) (hmask pL1268) 897 371 (true, L1268_cp1.1, L1268_cp1.2)) ∧ ptTest pL1268 (runFrom pL1268 (fmask pL1268) (cmask pL1268) (hmask pL1268) 897 371 (true, L1268_cp1.1, L1268_cp1.2)) 1268 634 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1268_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1268_fin) true) L1268_seg1) (by decide) rfl L1268_fin ptTest_fst
noncomputable def H1268_cp1 : Nat × Nat := t7val% (fastRun pH1268 1 896 (init pH1268) (init pH1268))
theorem H1268_seg1 : segOK pH1268 1 896 (init pH1268) (init pH1268) H1268_cp1.1 H1268_cp1.2 = true := by
  decide +kernel
theorem H1268_fin : (prmOK pH1268 1268 && ptTest pH1268 (runFrom pH1268 (fmask pH1268) (cmask pH1268) (hmask pH1268) 897 371 (true, H1268_cp1.1, H1268_cp1.2)) 1268 634 true) = true := by
  decide +kernel
theorem H1268_ok : RunOK pH1268 1268 (runFrom pH1268 (fmask pH1268) (cmask pH1268) (hmask pH1268) 897 371 (true, H1268_cp1.1, H1268_cp1.2)) ∧ ptTest pH1268 (runFrom pH1268 (fmask pH1268) (cmask pH1268) (hmask pH1268) 897 371 (true, H1268_cp1.1, H1268_cp1.2)) 1268 634 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1268_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1268_fin) true) H1268_seg1) (by decide) rfl H1268_fin ptTest_fst
theorem I1268_fin : (prmOK pI1268 1268 && intTest pI1268 (runFrom pI1268 (fmask pI1268) (cmask pI1268) (hmask pI1268) 1 1267 (true, (init pI1268), (init pI1268))) 1268 19 true) = true := by
  decide +kernel
theorem I1268_ok : RunOK pI1268 1268 (runFrom pI1268 (fmask pI1268) (cmask pI1268) (hmask pI1268) 1 1267 (true, (init pI1268), (init pI1268))) ∧ intTest pI1268 (runFrom pI1268 (fmask pI1268) (cmask pI1268) (hmask pI1268) 1 1267 (true, (init pI1268), (init pI1268))) 1268 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1268_fin) true) (by decide) rfl I1268_fin intTest_fst
theorem link1268 : linkOK pL1268 pH1268 pI1268 = true := by decide +kernel
theorem cvx1268 : ConvexBetweenHumps 1268 :=
  cvx_of L1268_ok H1268_ok I1268_ok link1268 (by decide)
theorem cenlink1268 : cenLinkOK pI1268 1268 = true := by decide +kernel
theorem cen1268 : CenterUniqueMin 1268 ∧ DipHyp 1268 ∧ OnePointHyps 1268 :=
  cen_of L1268_ok H1268_ok I1268_ok link1268 cenlink1268

/-! ### `N = 1269` -/

def pL1269 : Prm := ⟨77, 36, 38, 1271, 11, 18446744073709551616, 142507239697705195, 142507239697705195⟩
def pH1269 : Prm := ⟨77, 36, 38, 1271, 11, 18446744073709551616, 142509438720960747, 142509438720960747⟩
def pI1269 : Prm := ⟨66, 33, 30, 1271, 11, 18446744073709551616, 142507239697705195, 142509438720960747⟩
noncomputable def L1269_cp1 : Nat × Nat := t7val% (fastRun pL1269 1 896 (init pL1269) (init pL1269))
theorem L1269_seg1 : segOK pL1269 1 896 (init pL1269) (init pL1269) L1269_cp1.1 L1269_cp1.2 = true := by
  decide +kernel
theorem L1269_fin : (prmOK pL1269 1269 && ptTest pL1269 (runFrom pL1269 (fmask pL1269) (cmask pL1269) (hmask pL1269) 897 372 (true, L1269_cp1.1, L1269_cp1.2)) 1269 635 false) = true := by
  decide +kernel
theorem L1269_ok : RunOK pL1269 1269 (runFrom pL1269 (fmask pL1269) (cmask pL1269) (hmask pL1269) 897 372 (true, L1269_cp1.1, L1269_cp1.2)) ∧ ptTest pL1269 (runFrom pL1269 (fmask pL1269) (cmask pL1269) (hmask pL1269) 897 372 (true, L1269_cp1.1, L1269_cp1.2)) 1269 635 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1269_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1269_fin) true) L1269_seg1) (by decide) rfl L1269_fin ptTest_fst
noncomputable def H1269_cp1 : Nat × Nat := t7val% (fastRun pH1269 1 896 (init pH1269) (init pH1269))
theorem H1269_seg1 : segOK pH1269 1 896 (init pH1269) (init pH1269) H1269_cp1.1 H1269_cp1.2 = true := by
  decide +kernel
theorem H1269_fin : (prmOK pH1269 1269 && ptTest pH1269 (runFrom pH1269 (fmask pH1269) (cmask pH1269) (hmask pH1269) 897 372 (true, H1269_cp1.1, H1269_cp1.2)) 1269 635 true) = true := by
  decide +kernel
theorem H1269_ok : RunOK pH1269 1269 (runFrom pH1269 (fmask pH1269) (cmask pH1269) (hmask pH1269) 897 372 (true, H1269_cp1.1, H1269_cp1.2)) ∧ ptTest pH1269 (runFrom pH1269 (fmask pH1269) (cmask pH1269) (hmask pH1269) 897 372 (true, H1269_cp1.1, H1269_cp1.2)) 1269 635 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1269_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1269_fin) true) H1269_seg1) (by decide) rfl H1269_fin ptTest_fst
theorem I1269_fin : (prmOK pI1269 1269 && intTest pI1269 (runFrom pI1269 (fmask pI1269) (cmask pI1269) (hmask pI1269) 1 1268 (true, (init pI1269), (init pI1269))) 1269 19 false) = true := by
  decide +kernel
theorem I1269_ok : RunOK pI1269 1269 (runFrom pI1269 (fmask pI1269) (cmask pI1269) (hmask pI1269) 1 1268 (true, (init pI1269), (init pI1269))) ∧ intTest pI1269 (runFrom pI1269 (fmask pI1269) (cmask pI1269) (hmask pI1269) 1 1268 (true, (init pI1269), (init pI1269))) 1269 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1269_fin) true) (by decide) rfl I1269_fin intTest_fst
theorem link1269 : linkOK pL1269 pH1269 pI1269 = true := by decide +kernel
theorem cvx1269 : ConvexBetweenHumps 1269 :=
  cvx_of L1269_ok H1269_ok I1269_ok link1269 (by decide)

/-! ### `N = 1270` -/

def pL1270 : Prm := ⟨77, 36, 38, 1272, 11, 18446744073709551616, 142416633058304356, 142416633058304356⟩
def pH1270 : Prm := ⟨77, 36, 38, 1272, 11, 18446744073709551616, 142418832081559908, 142418832081559908⟩
def pI1270 : Prm := ⟨66, 33, 30, 1272, 11, 18446744073709551616, 142416633058304356, 142418832081559908⟩
noncomputable def L1270_cp1 : Nat × Nat := t7val% (fastRun pL1270 1 897 (init pL1270) (init pL1270))
theorem L1270_seg1 : segOK pL1270 1 897 (init pL1270) (init pL1270) L1270_cp1.1 L1270_cp1.2 = true := by
  decide +kernel
theorem L1270_fin : (prmOK pL1270 1270 && ptTest pL1270 (runFrom pL1270 (fmask pL1270) (cmask pL1270) (hmask pL1270) 898 372 (true, L1270_cp1.1, L1270_cp1.2)) 1270 635 false) = true := by
  decide +kernel
theorem L1270_ok : RunOK pL1270 1270 (runFrom pL1270 (fmask pL1270) (cmask pL1270) (hmask pL1270) 898 372 (true, L1270_cp1.1, L1270_cp1.2)) ∧ ptTest pL1270 (runFrom pL1270 (fmask pL1270) (cmask pL1270) (hmask pL1270) 898 372 (true, L1270_cp1.1, L1270_cp1.2)) 1270 635 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1270_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1270_fin) true) L1270_seg1) (by decide) rfl L1270_fin ptTest_fst
noncomputable def H1270_cp1 : Nat × Nat := t7val% (fastRun pH1270 1 897 (init pH1270) (init pH1270))
theorem H1270_seg1 : segOK pH1270 1 897 (init pH1270) (init pH1270) H1270_cp1.1 H1270_cp1.2 = true := by
  decide +kernel
theorem H1270_fin : (prmOK pH1270 1270 && ptTest pH1270 (runFrom pH1270 (fmask pH1270) (cmask pH1270) (hmask pH1270) 898 372 (true, H1270_cp1.1, H1270_cp1.2)) 1270 635 true) = true := by
  decide +kernel
theorem H1270_ok : RunOK pH1270 1270 (runFrom pH1270 (fmask pH1270) (cmask pH1270) (hmask pH1270) 898 372 (true, H1270_cp1.1, H1270_cp1.2)) ∧ ptTest pH1270 (runFrom pH1270 (fmask pH1270) (cmask pH1270) (hmask pH1270) 898 372 (true, H1270_cp1.1, H1270_cp1.2)) 1270 635 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1270_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1270_fin) true) H1270_seg1) (by decide) rfl H1270_fin ptTest_fst
theorem I1270_fin : (prmOK pI1270 1270 && intTest pI1270 (runFrom pI1270 (fmask pI1270) (cmask pI1270) (hmask pI1270) 1 1269 (true, (init pI1270), (init pI1270))) 1270 19 true) = true := by
  decide +kernel
theorem I1270_ok : RunOK pI1270 1270 (runFrom pI1270 (fmask pI1270) (cmask pI1270) (hmask pI1270) 1 1269 (true, (init pI1270), (init pI1270))) ∧ intTest pI1270 (runFrom pI1270 (fmask pI1270) (cmask pI1270) (hmask pI1270) 1 1269 (true, (init pI1270), (init pI1270))) 1270 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1270_fin) true) (by decide) rfl I1270_fin intTest_fst
theorem link1270 : linkOK pL1270 pH1270 pI1270 = true := by decide +kernel
theorem cvx1270 : ConvexBetweenHumps 1270 :=
  cvx_of L1270_ok H1270_ok I1270_ok link1270 (by decide)
theorem cenlink1270 : cenLinkOK pI1270 1270 = true := by decide +kernel
theorem cen1270 : CenterUniqueMin 1270 ∧ DipHyp 1270 ∧ OnePointHyps 1270 :=
  cen_of L1270_ok H1270_ok I1270_ok link1270 cenlink1270

/-! ### `N = 1271` -/

def pL1271 : Prm := ⟨77, 36, 38, 1273, 11, 18446744073709551616, 142326096332414044, 142326096332414044⟩
def pH1271 : Prm := ⟨77, 36, 38, 1273, 11, 18446744073709551616, 142328295355669596, 142328295355669596⟩
def pI1271 : Prm := ⟨66, 33, 30, 1273, 11, 18446744073709551616, 142326096332414044, 142328295355669596⟩
noncomputable def L1271_cp1 : Nat × Nat := t7val% (fastRun pL1271 1 898 (init pL1271) (init pL1271))
theorem L1271_seg1 : segOK pL1271 1 898 (init pL1271) (init pL1271) L1271_cp1.1 L1271_cp1.2 = true := by
  decide +kernel
theorem L1271_fin : (prmOK pL1271 1271 && ptTest pL1271 (runFrom pL1271 (fmask pL1271) (cmask pL1271) (hmask pL1271) 899 372 (true, L1271_cp1.1, L1271_cp1.2)) 1271 636 false) = true := by
  decide +kernel
theorem L1271_ok : RunOK pL1271 1271 (runFrom pL1271 (fmask pL1271) (cmask pL1271) (hmask pL1271) 899 372 (true, L1271_cp1.1, L1271_cp1.2)) ∧ ptTest pL1271 (runFrom pL1271 (fmask pL1271) (cmask pL1271) (hmask pL1271) 899 372 (true, L1271_cp1.1, L1271_cp1.2)) 1271 636 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1271_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1271_fin) true) L1271_seg1) (by decide) rfl L1271_fin ptTest_fst
noncomputable def H1271_cp1 : Nat × Nat := t7val% (fastRun pH1271 1 898 (init pH1271) (init pH1271))
theorem H1271_seg1 : segOK pH1271 1 898 (init pH1271) (init pH1271) H1271_cp1.1 H1271_cp1.2 = true := by
  decide +kernel
theorem H1271_fin : (prmOK pH1271 1271 && ptTest pH1271 (runFrom pH1271 (fmask pH1271) (cmask pH1271) (hmask pH1271) 899 372 (true, H1271_cp1.1, H1271_cp1.2)) 1271 636 true) = true := by
  decide +kernel
theorem H1271_ok : RunOK pH1271 1271 (runFrom pH1271 (fmask pH1271) (cmask pH1271) (hmask pH1271) 899 372 (true, H1271_cp1.1, H1271_cp1.2)) ∧ ptTest pH1271 (runFrom pH1271 (fmask pH1271) (cmask pH1271) (hmask pH1271) 899 372 (true, H1271_cp1.1, H1271_cp1.2)) 1271 636 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1271_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1271_fin) true) H1271_seg1) (by decide) rfl H1271_fin ptTest_fst
theorem I1271_fin : (prmOK pI1271 1271 && intTest pI1271 (runFrom pI1271 (fmask pI1271) (cmask pI1271) (hmask pI1271) 1 1270 (true, (init pI1271), (init pI1271))) 1271 19 false) = true := by
  decide +kernel
theorem I1271_ok : RunOK pI1271 1271 (runFrom pI1271 (fmask pI1271) (cmask pI1271) (hmask pI1271) 1 1270 (true, (init pI1271), (init pI1271))) ∧ intTest pI1271 (runFrom pI1271 (fmask pI1271) (cmask pI1271) (hmask pI1271) 1 1270 (true, (init pI1271), (init pI1271))) 1271 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1271_fin) true) (by decide) rfl I1271_fin intTest_fst
theorem link1271 : linkOK pL1271 pH1271 pI1271 = true := by decide +kernel
theorem cvx1271 : ConvexBetweenHumps 1271 :=
  cvx_of L1271_ok H1271_ok I1271_ok link1271 (by decide)

/-! ### `N = 1272` -/

def pL1272 : Prm := ⟨77, 36, 38, 1274, 11, 18446744073709551616, 142235740564582091, 142235740564582091⟩
def pH1272 : Prm := ⟨77, 36, 38, 1274, 11, 18446744073709551616, 142237939587837643, 142237939587837643⟩
def pI1272 : Prm := ⟨66, 33, 30, 1274, 11, 18446744073709551616, 142235740564582091, 142237939587837643⟩
noncomputable def L1272_cp1 : Nat × Nat := t7val% (fastRun pL1272 1 898 (init pL1272) (init pL1272))
theorem L1272_seg1 : segOK pL1272 1 898 (init pL1272) (init pL1272) L1272_cp1.1 L1272_cp1.2 = true := by
  decide +kernel
theorem L1272_fin : (prmOK pL1272 1272 && ptTest pL1272 (runFrom pL1272 (fmask pL1272) (cmask pL1272) (hmask pL1272) 899 373 (true, L1272_cp1.1, L1272_cp1.2)) 1272 636 false) = true := by
  decide +kernel
theorem L1272_ok : RunOK pL1272 1272 (runFrom pL1272 (fmask pL1272) (cmask pL1272) (hmask pL1272) 899 373 (true, L1272_cp1.1, L1272_cp1.2)) ∧ ptTest pL1272 (runFrom pL1272 (fmask pL1272) (cmask pL1272) (hmask pL1272) 899 373 (true, L1272_cp1.1, L1272_cp1.2)) 1272 636 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1272_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1272_fin) true) L1272_seg1) (by decide) rfl L1272_fin ptTest_fst
noncomputable def H1272_cp1 : Nat × Nat := t7val% (fastRun pH1272 1 898 (init pH1272) (init pH1272))
theorem H1272_seg1 : segOK pH1272 1 898 (init pH1272) (init pH1272) H1272_cp1.1 H1272_cp1.2 = true := by
  decide +kernel
theorem H1272_fin : (prmOK pH1272 1272 && ptTest pH1272 (runFrom pH1272 (fmask pH1272) (cmask pH1272) (hmask pH1272) 899 373 (true, H1272_cp1.1, H1272_cp1.2)) 1272 636 true) = true := by
  decide +kernel
theorem H1272_ok : RunOK pH1272 1272 (runFrom pH1272 (fmask pH1272) (cmask pH1272) (hmask pH1272) 899 373 (true, H1272_cp1.1, H1272_cp1.2)) ∧ ptTest pH1272 (runFrom pH1272 (fmask pH1272) (cmask pH1272) (hmask pH1272) 899 373 (true, H1272_cp1.1, H1272_cp1.2)) 1272 636 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1272_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1272_fin) true) H1272_seg1) (by decide) rfl H1272_fin ptTest_fst
theorem I1272_fin : (prmOK pI1272 1272 && intTest pI1272 (runFrom pI1272 (fmask pI1272) (cmask pI1272) (hmask pI1272) 1 1271 (true, (init pI1272), (init pI1272))) 1272 19 true) = true := by
  decide +kernel
theorem I1272_ok : RunOK pI1272 1272 (runFrom pI1272 (fmask pI1272) (cmask pI1272) (hmask pI1272) 1 1271 (true, (init pI1272), (init pI1272))) ∧ intTest pI1272 (runFrom pI1272 (fmask pI1272) (cmask pI1272) (hmask pI1272) 1 1271 (true, (init pI1272), (init pI1272))) 1272 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1272_fin) true) (by decide) rfl I1272_fin intTest_fst
theorem link1272 : linkOK pL1272 pH1272 pI1272 = true := by decide +kernel
theorem cvx1272 : ConvexBetweenHumps 1272 :=
  cvx_of L1272_ok H1272_ok I1272_ok link1272 (by decide)
theorem cenlink1272 : cenLinkOK pI1272 1272 = true := by decide +kernel
theorem cen1272 : CenterUniqueMin 1272 ∧ DipHyp 1272 ∧ OnePointHyps 1272 :=
  cen_of L1272_ok H1272_ok I1272_ok link1272 cenlink1272

/-! ### `N = 1273` -/

def pL1273 : Prm := ⟨77, 36, 38, 1275, 11, 18446744073709551616, 142145454438613912, 142145454438613912⟩
def pH1273 : Prm := ⟨77, 36, 38, 1275, 11, 18446744073709551616, 142147653461869464, 142147653461869464⟩
def pI1273 : Prm := ⟨66, 33, 30, 1275, 11, 18446744073709551616, 142145454438613912, 142147653461869464⟩
noncomputable def L1273_cp1 : Nat × Nat := t7val% (fastRun pL1273 1 899 (init pL1273) (init pL1273))
theorem L1273_seg1 : segOK pL1273 1 899 (init pL1273) (init pL1273) L1273_cp1.1 L1273_cp1.2 = true := by
  decide +kernel
theorem L1273_fin : (prmOK pL1273 1273 && ptTest pL1273 (runFrom pL1273 (fmask pL1273) (cmask pL1273) (hmask pL1273) 900 373 (true, L1273_cp1.1, L1273_cp1.2)) 1273 637 false) = true := by
  decide +kernel
theorem L1273_ok : RunOK pL1273 1273 (runFrom pL1273 (fmask pL1273) (cmask pL1273) (hmask pL1273) 900 373 (true, L1273_cp1.1, L1273_cp1.2)) ∧ ptTest pL1273 (runFrom pL1273 (fmask pL1273) (cmask pL1273) (hmask pL1273) 900 373 (true, L1273_cp1.1, L1273_cp1.2)) 1273 637 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1273_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1273_fin) true) L1273_seg1) (by decide) rfl L1273_fin ptTest_fst
noncomputable def H1273_cp1 : Nat × Nat := t7val% (fastRun pH1273 1 899 (init pH1273) (init pH1273))
theorem H1273_seg1 : segOK pH1273 1 899 (init pH1273) (init pH1273) H1273_cp1.1 H1273_cp1.2 = true := by
  decide +kernel
theorem H1273_fin : (prmOK pH1273 1273 && ptTest pH1273 (runFrom pH1273 (fmask pH1273) (cmask pH1273) (hmask pH1273) 900 373 (true, H1273_cp1.1, H1273_cp1.2)) 1273 637 true) = true := by
  decide +kernel
theorem H1273_ok : RunOK pH1273 1273 (runFrom pH1273 (fmask pH1273) (cmask pH1273) (hmask pH1273) 900 373 (true, H1273_cp1.1, H1273_cp1.2)) ∧ ptTest pH1273 (runFrom pH1273 (fmask pH1273) (cmask pH1273) (hmask pH1273) 900 373 (true, H1273_cp1.1, H1273_cp1.2)) 1273 637 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1273_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1273_fin) true) H1273_seg1) (by decide) rfl H1273_fin ptTest_fst
theorem I1273_fin : (prmOK pI1273 1273 && intTest pI1273 (runFrom pI1273 (fmask pI1273) (cmask pI1273) (hmask pI1273) 1 1272 (true, (init pI1273), (init pI1273))) 1273 19 false) = true := by
  decide +kernel
theorem I1273_ok : RunOK pI1273 1273 (runFrom pI1273 (fmask pI1273) (cmask pI1273) (hmask pI1273) 1 1272 (true, (init pI1273), (init pI1273))) ∧ intTest pI1273 (runFrom pI1273 (fmask pI1273) (cmask pI1273) (hmask pI1273) 1 1272 (true, (init pI1273), (init pI1273))) 1273 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1273_fin) true) (by decide) rfl I1273_fin intTest_fst
theorem link1273 : linkOK pL1273 pH1273 pI1273 = true := by decide +kernel
theorem cvx1273 : ConvexBetweenHumps 1273 :=
  cvx_of L1273_ok H1273_ok I1273_ok link1273 (by decide)

/-! ### `N = 1274` -/

def pL1274 : Prm := ⟨77, 36, 38, 1276, 11, 18446744073709551616, 142055348467661980, 142055348467661980⟩
def pH1274 : Prm := ⟨77, 36, 38, 1276, 11, 18446744073709551616, 142057547490917532, 142057547490917532⟩
def pI1274 : Prm := ⟨66, 33, 30, 1276, 11, 18446744073709551616, 142055348467661980, 142057547490917532⟩
noncomputable def L1274_cp1 : Nat × Nat := t7val% (fastRun pL1274 1 900 (init pL1274) (init pL1274))
theorem L1274_seg1 : segOK pL1274 1 900 (init pL1274) (init pL1274) L1274_cp1.1 L1274_cp1.2 = true := by
  decide +kernel
theorem L1274_fin : (prmOK pL1274 1274 && ptTest pL1274 (runFrom pL1274 (fmask pL1274) (cmask pL1274) (hmask pL1274) 901 373 (true, L1274_cp1.1, L1274_cp1.2)) 1274 637 false) = true := by
  decide +kernel
theorem L1274_ok : RunOK pL1274 1274 (runFrom pL1274 (fmask pL1274) (cmask pL1274) (hmask pL1274) 901 373 (true, L1274_cp1.1, L1274_cp1.2)) ∧ ptTest pL1274 (runFrom pL1274 (fmask pL1274) (cmask pL1274) (hmask pL1274) 901 373 (true, L1274_cp1.1, L1274_cp1.2)) 1274 637 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1274_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1274_fin) true) L1274_seg1) (by decide) rfl L1274_fin ptTest_fst
noncomputable def H1274_cp1 : Nat × Nat := t7val% (fastRun pH1274 1 900 (init pH1274) (init pH1274))
theorem H1274_seg1 : segOK pH1274 1 900 (init pH1274) (init pH1274) H1274_cp1.1 H1274_cp1.2 = true := by
  decide +kernel
theorem H1274_fin : (prmOK pH1274 1274 && ptTest pH1274 (runFrom pH1274 (fmask pH1274) (cmask pH1274) (hmask pH1274) 901 373 (true, H1274_cp1.1, H1274_cp1.2)) 1274 637 true) = true := by
  decide +kernel
theorem H1274_ok : RunOK pH1274 1274 (runFrom pH1274 (fmask pH1274) (cmask pH1274) (hmask pH1274) 901 373 (true, H1274_cp1.1, H1274_cp1.2)) ∧ ptTest pH1274 (runFrom pH1274 (fmask pH1274) (cmask pH1274) (hmask pH1274) 901 373 (true, H1274_cp1.1, H1274_cp1.2)) 1274 637 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1274_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1274_fin) true) H1274_seg1) (by decide) rfl H1274_fin ptTest_fst
theorem I1274_fin : (prmOK pI1274 1274 && intTest pI1274 (runFrom pI1274 (fmask pI1274) (cmask pI1274) (hmask pI1274) 1 1273 (true, (init pI1274), (init pI1274))) 1274 19 true) = true := by
  decide +kernel
theorem I1274_ok : RunOK pI1274 1274 (runFrom pI1274 (fmask pI1274) (cmask pI1274) (hmask pI1274) 1 1273 (true, (init pI1274), (init pI1274))) ∧ intTest pI1274 (runFrom pI1274 (fmask pI1274) (cmask pI1274) (hmask pI1274) 1 1273 (true, (init pI1274), (init pI1274))) 1274 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1274_fin) true) (by decide) rfl I1274_fin intTest_fst
theorem link1274 : linkOK pL1274 pH1274 pI1274 = true := by decide +kernel
theorem cvx1274 : ConvexBetweenHumps 1274 :=
  cvx_of L1274_ok H1274_ok I1274_ok link1274 (by decide)
theorem cenlink1274 : cenLinkOK pI1274 1274 = true := by decide +kernel
theorem cen1274 : CenterUniqueMin 1274 ∧ DipHyp 1274 ∧ OnePointHyps 1274 :=
  cen_of L1274_ok H1274_ok I1274_ok link1274 cenlink1274

/-! ### `N = 1275` -/

def pL1275 : Prm := ⟨77, 36, 38, 1277, 11, 18446744073709551616, 141965311868402809, 141965311868402809⟩
def pH1275 : Prm := ⟨77, 36, 38, 1277, 11, 18446744073709551616, 141967510891658361, 141967510891658361⟩
def pI1275 : Prm := ⟨66, 33, 30, 1277, 11, 18446744073709551616, 141965311868402809, 141967510891658361⟩
noncomputable def L1275_cp1 : Nat × Nat := t7val% (fastRun pL1275 1 901 (init pL1275) (init pL1275))
theorem L1275_seg1 : segOK pL1275 1 901 (init pL1275) (init pL1275) L1275_cp1.1 L1275_cp1.2 = true := by
  decide +kernel
theorem L1275_fin : (prmOK pL1275 1275 && ptTest pL1275 (runFrom pL1275 (fmask pL1275) (cmask pL1275) (hmask pL1275) 902 373 (true, L1275_cp1.1, L1275_cp1.2)) 1275 638 false) = true := by
  decide +kernel
theorem L1275_ok : RunOK pL1275 1275 (runFrom pL1275 (fmask pL1275) (cmask pL1275) (hmask pL1275) 902 373 (true, L1275_cp1.1, L1275_cp1.2)) ∧ ptTest pL1275 (runFrom pL1275 (fmask pL1275) (cmask pL1275) (hmask pL1275) 902 373 (true, L1275_cp1.1, L1275_cp1.2)) 1275 638 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1275_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1275_fin) true) L1275_seg1) (by decide) rfl L1275_fin ptTest_fst
noncomputable def H1275_cp1 : Nat × Nat := t7val% (fastRun pH1275 1 901 (init pH1275) (init pH1275))
theorem H1275_seg1 : segOK pH1275 1 901 (init pH1275) (init pH1275) H1275_cp1.1 H1275_cp1.2 = true := by
  decide +kernel
theorem H1275_fin : (prmOK pH1275 1275 && ptTest pH1275 (runFrom pH1275 (fmask pH1275) (cmask pH1275) (hmask pH1275) 902 373 (true, H1275_cp1.1, H1275_cp1.2)) 1275 638 true) = true := by
  decide +kernel
theorem H1275_ok : RunOK pH1275 1275 (runFrom pH1275 (fmask pH1275) (cmask pH1275) (hmask pH1275) 902 373 (true, H1275_cp1.1, H1275_cp1.2)) ∧ ptTest pH1275 (runFrom pH1275 (fmask pH1275) (cmask pH1275) (hmask pH1275) 902 373 (true, H1275_cp1.1, H1275_cp1.2)) 1275 638 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1275_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1275_fin) true) H1275_seg1) (by decide) rfl H1275_fin ptTest_fst
theorem I1275_fin : (prmOK pI1275 1275 && intTest pI1275 (runFrom pI1275 (fmask pI1275) (cmask pI1275) (hmask pI1275) 1 1274 (true, (init pI1275), (init pI1275))) 1275 19 false) = true := by
  decide +kernel
theorem I1275_ok : RunOK pI1275 1275 (runFrom pI1275 (fmask pI1275) (cmask pI1275) (hmask pI1275) 1 1274 (true, (init pI1275), (init pI1275))) ∧ intTest pI1275 (runFrom pI1275 (fmask pI1275) (cmask pI1275) (hmask pI1275) 1 1274 (true, (init pI1275), (init pI1275))) 1275 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1275_fin) true) (by decide) rfl I1275_fin intTest_fst
theorem link1275 : linkOK pL1275 pH1275 pI1275 = true := by decide +kernel
theorem cvx1275 : ConvexBetweenHumps 1275 :=
  cvx_of L1275_ok H1275_ok I1275_ok link1275 (by decide)

/-! ### `N = 1276` -/

def pL1276 : Prm := ⟨77, 36, 38, 1278, 11, 18446744073709551616, 141875454625932376, 141875454625932376⟩
def pH1276 : Prm := ⟨77, 36, 38, 1278, 11, 18446744073709551616, 141877653649187928, 141877653649187928⟩
def pI1276 : Prm := ⟨66, 33, 30, 1278, 11, 18446744073709551616, 141875454625932376, 141877653649187928⟩
noncomputable def L1276_cp1 : Nat × Nat := t7val% (fastRun pL1276 1 901 (init pL1276) (init pL1276))
theorem L1276_seg1 : segOK pL1276 1 901 (init pL1276) (init pL1276) L1276_cp1.1 L1276_cp1.2 = true := by
  decide +kernel
theorem L1276_fin : (prmOK pL1276 1276 && ptTest pL1276 (runFrom pL1276 (fmask pL1276) (cmask pL1276) (hmask pL1276) 902 374 (true, L1276_cp1.1, L1276_cp1.2)) 1276 638 false) = true := by
  decide +kernel
theorem L1276_ok : RunOK pL1276 1276 (runFrom pL1276 (fmask pL1276) (cmask pL1276) (hmask pL1276) 902 374 (true, L1276_cp1.1, L1276_cp1.2)) ∧ ptTest pL1276 (runFrom pL1276 (fmask pL1276) (cmask pL1276) (hmask pL1276) 902 374 (true, L1276_cp1.1, L1276_cp1.2)) 1276 638 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1276_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1276_fin) true) L1276_seg1) (by decide) rfl L1276_fin ptTest_fst
noncomputable def H1276_cp1 : Nat × Nat := t7val% (fastRun pH1276 1 901 (init pH1276) (init pH1276))
theorem H1276_seg1 : segOK pH1276 1 901 (init pH1276) (init pH1276) H1276_cp1.1 H1276_cp1.2 = true := by
  decide +kernel
theorem H1276_fin : (prmOK pH1276 1276 && ptTest pH1276 (runFrom pH1276 (fmask pH1276) (cmask pH1276) (hmask pH1276) 902 374 (true, H1276_cp1.1, H1276_cp1.2)) 1276 638 true) = true := by
  decide +kernel
theorem H1276_ok : RunOK pH1276 1276 (runFrom pH1276 (fmask pH1276) (cmask pH1276) (hmask pH1276) 902 374 (true, H1276_cp1.1, H1276_cp1.2)) ∧ ptTest pH1276 (runFrom pH1276 (fmask pH1276) (cmask pH1276) (hmask pH1276) 902 374 (true, H1276_cp1.1, H1276_cp1.2)) 1276 638 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1276_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1276_fin) true) H1276_seg1) (by decide) rfl H1276_fin ptTest_fst
theorem I1276_fin : (prmOK pI1276 1276 && intTest pI1276 (runFrom pI1276 (fmask pI1276) (cmask pI1276) (hmask pI1276) 1 1275 (true, (init pI1276), (init pI1276))) 1276 19 true) = true := by
  decide +kernel
theorem I1276_ok : RunOK pI1276 1276 (runFrom pI1276 (fmask pI1276) (cmask pI1276) (hmask pI1276) 1 1275 (true, (init pI1276), (init pI1276))) ∧ intTest pI1276 (runFrom pI1276 (fmask pI1276) (cmask pI1276) (hmask pI1276) 1 1275 (true, (init pI1276), (init pI1276))) 1276 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1276_fin) true) (by decide) rfl I1276_fin intTest_fst
theorem link1276 : linkOK pL1276 pH1276 pI1276 = true := by decide +kernel
theorem cvx1276 : ConvexBetweenHumps 1276 :=
  cvx_of L1276_ok H1276_ok I1276_ok link1276 (by decide)
theorem cenlink1276 : cenLinkOK pI1276 1276 = true := by decide +kernel
theorem cen1276 : CenterUniqueMin 1276 ∧ DipHyp 1276 ∧ OnePointHyps 1276 :=
  cen_of L1276_ok H1276_ok I1276_ok link1276 cenlink1276

/-! ### `N = 1277` -/

def pL1277 : Prm := ⟨77, 36, 38, 1279, 11, 18446744073709551616, 141785666486367196, 141785666486367196⟩
def pH1277 : Prm := ⟨77, 36, 38, 1279, 11, 18446744073709551616, 141787865509622748, 141787865509622748⟩
def pI1277 : Prm := ⟨66, 33, 30, 1279, 11, 18446744073709551616, 141785666486367196, 141787865509622748⟩
noncomputable def L1277_cp1 : Nat × Nat := t7val% (fastRun pL1277 1 902 (init pL1277) (init pL1277))
theorem L1277_seg1 : segOK pL1277 1 902 (init pL1277) (init pL1277) L1277_cp1.1 L1277_cp1.2 = true := by
  decide +kernel
theorem L1277_fin : (prmOK pL1277 1277 && ptTest pL1277 (runFrom pL1277 (fmask pL1277) (cmask pL1277) (hmask pL1277) 903 374 (true, L1277_cp1.1, L1277_cp1.2)) 1277 639 false) = true := by
  decide +kernel
theorem L1277_ok : RunOK pL1277 1277 (runFrom pL1277 (fmask pL1277) (cmask pL1277) (hmask pL1277) 903 374 (true, L1277_cp1.1, L1277_cp1.2)) ∧ ptTest pL1277 (runFrom pL1277 (fmask pL1277) (cmask pL1277) (hmask pL1277) 903 374 (true, L1277_cp1.1, L1277_cp1.2)) 1277 639 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1277_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1277_fin) true) L1277_seg1) (by decide) rfl L1277_fin ptTest_fst
noncomputable def H1277_cp1 : Nat × Nat := t7val% (fastRun pH1277 1 902 (init pH1277) (init pH1277))
theorem H1277_seg1 : segOK pH1277 1 902 (init pH1277) (init pH1277) H1277_cp1.1 H1277_cp1.2 = true := by
  decide +kernel
theorem H1277_fin : (prmOK pH1277 1277 && ptTest pH1277 (runFrom pH1277 (fmask pH1277) (cmask pH1277) (hmask pH1277) 903 374 (true, H1277_cp1.1, H1277_cp1.2)) 1277 639 true) = true := by
  decide +kernel
theorem H1277_ok : RunOK pH1277 1277 (runFrom pH1277 (fmask pH1277) (cmask pH1277) (hmask pH1277) 903 374 (true, H1277_cp1.1, H1277_cp1.2)) ∧ ptTest pH1277 (runFrom pH1277 (fmask pH1277) (cmask pH1277) (hmask pH1277) 903 374 (true, H1277_cp1.1, H1277_cp1.2)) 1277 639 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1277_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1277_fin) true) H1277_seg1) (by decide) rfl H1277_fin ptTest_fst
theorem I1277_fin : (prmOK pI1277 1277 && intTest pI1277 (runFrom pI1277 (fmask pI1277) (cmask pI1277) (hmask pI1277) 1 1276 (true, (init pI1277), (init pI1277))) 1277 19 false) = true := by
  decide +kernel
theorem I1277_ok : RunOK pI1277 1277 (runFrom pI1277 (fmask pI1277) (cmask pI1277) (hmask pI1277) 1 1276 (true, (init pI1277), (init pI1277))) ∧ intTest pI1277 (runFrom pI1277 (fmask pI1277) (cmask pI1277) (hmask pI1277) 1 1276 (true, (init pI1277), (init pI1277))) 1277 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1277_fin) true) (by decide) rfl I1277_fin intTest_fst
theorem link1277 : linkOK pL1277 pH1277 pI1277 = true := by decide +kernel
theorem cvx1277 : ConvexBetweenHumps 1277 :=
  cvx_of L1277_ok H1277_ok I1277_ok link1277 (by decide)

/-! ### `N = 1278` -/

def pL1278 : Prm := ⟨77, 36, 38, 1280, 11, 18446744073709551616, 141696056910177845, 141696056910177845⟩
def pH1278 : Prm := ⟨77, 36, 38, 1280, 11, 18446744073709551616, 141698255933433397, 141698255933433397⟩
def pI1278 : Prm := ⟨66, 33, 30, 1280, 11, 18446744073709551616, 141696056910177845, 141698255933433397⟩
noncomputable def L1278_cp1 : Nat × Nat := t7val% (fastRun pL1278 1 903 (init pL1278) (init pL1278))
theorem L1278_seg1 : segOK pL1278 1 903 (init pL1278) (init pL1278) L1278_cp1.1 L1278_cp1.2 = true := by
  decide +kernel
theorem L1278_fin : (prmOK pL1278 1278 && ptTest pL1278 (runFrom pL1278 (fmask pL1278) (cmask pL1278) (hmask pL1278) 904 374 (true, L1278_cp1.1, L1278_cp1.2)) 1278 639 false) = true := by
  decide +kernel
theorem L1278_ok : RunOK pL1278 1278 (runFrom pL1278 (fmask pL1278) (cmask pL1278) (hmask pL1278) 904 374 (true, L1278_cp1.1, L1278_cp1.2)) ∧ ptTest pL1278 (runFrom pL1278 (fmask pL1278) (cmask pL1278) (hmask pL1278) 904 374 (true, L1278_cp1.1, L1278_cp1.2)) 1278 639 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1278_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1278_fin) true) L1278_seg1) (by decide) rfl L1278_fin ptTest_fst
noncomputable def H1278_cp1 : Nat × Nat := t7val% (fastRun pH1278 1 903 (init pH1278) (init pH1278))
theorem H1278_seg1 : segOK pH1278 1 903 (init pH1278) (init pH1278) H1278_cp1.1 H1278_cp1.2 = true := by
  decide +kernel
theorem H1278_fin : (prmOK pH1278 1278 && ptTest pH1278 (runFrom pH1278 (fmask pH1278) (cmask pH1278) (hmask pH1278) 904 374 (true, H1278_cp1.1, H1278_cp1.2)) 1278 639 true) = true := by
  decide +kernel
theorem H1278_ok : RunOK pH1278 1278 (runFrom pH1278 (fmask pH1278) (cmask pH1278) (hmask pH1278) 904 374 (true, H1278_cp1.1, H1278_cp1.2)) ∧ ptTest pH1278 (runFrom pH1278 (fmask pH1278) (cmask pH1278) (hmask pH1278) 904 374 (true, H1278_cp1.1, H1278_cp1.2)) 1278 639 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1278_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1278_fin) true) H1278_seg1) (by decide) rfl H1278_fin ptTest_fst
noncomputable def I1278_cp1 : Nat × Nat := t7val% (fastRun pI1278 1 903 (init pI1278) (init pI1278))
theorem I1278_seg1 : segOK pI1278 1 903 (init pI1278) (init pI1278) I1278_cp1.1 I1278_cp1.2 = true := by
  decide +kernel
theorem I1278_fin : (prmOK pI1278 1278 && intTest pI1278 (runFrom pI1278 (fmask pI1278) (cmask pI1278) (hmask pI1278) 904 374 (true, I1278_cp1.1, I1278_cp1.2)) 1278 19 true) = true := by
  decide +kernel
theorem I1278_ok : RunOK pI1278 1278 (runFrom pI1278 (fmask pI1278) (cmask pI1278) (hmask pI1278) 904 374 (true, I1278_cp1.1, I1278_cp1.2)) ∧ intTest pI1278 (runFrom pI1278 (fmask pI1278) (cmask pI1278) (hmask pI1278) 904 374 (true, I1278_cp1.1, I1278_cp1.2)) 1278 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1278_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1278_fin) true) I1278_seg1) (by decide) rfl I1278_fin intTest_fst
theorem link1278 : linkOK pL1278 pH1278 pI1278 = true := by decide +kernel
theorem cvx1278 : ConvexBetweenHumps 1278 :=
  cvx_of L1278_ok H1278_ok I1278_ok link1278 (by decide)
theorem cenlink1278 : cenLinkOK pI1278 1278 = true := by decide +kernel
theorem cen1278 : CenterUniqueMin 1278 ∧ DipHyp 1278 ∧ OnePointHyps 1278 :=
  cen_of L1278_ok H1278_ok I1278_ok link1278 cenlink1278

/-! ### `N = 1279` -/

def pL1279 : Prm := ⟨77, 36, 38, 1281, 11, 18446744073709551616, 141606516169489744, 141606516169489744⟩
def pH1279 : Prm := ⟨77, 36, 38, 1281, 11, 18446744073709551616, 141608715192745296, 141608715192745296⟩
def pI1279 : Prm := ⟨66, 33, 30, 1281, 11, 18446744073709551616, 141606516169489744, 141608715192745296⟩
noncomputable def L1279_cp1 : Nat × Nat := t7val% (fastRun pL1279 1 903 (init pL1279) (init pL1279))
theorem L1279_seg1 : segOK pL1279 1 903 (init pL1279) (init pL1279) L1279_cp1.1 L1279_cp1.2 = true := by
  decide +kernel
theorem L1279_fin : (prmOK pL1279 1279 && ptTest pL1279 (runFrom pL1279 (fmask pL1279) (cmask pL1279) (hmask pL1279) 904 375 (true, L1279_cp1.1, L1279_cp1.2)) 1279 640 false) = true := by
  decide +kernel
theorem L1279_ok : RunOK pL1279 1279 (runFrom pL1279 (fmask pL1279) (cmask pL1279) (hmask pL1279) 904 375 (true, L1279_cp1.1, L1279_cp1.2)) ∧ ptTest pL1279 (runFrom pL1279 (fmask pL1279) (cmask pL1279) (hmask pL1279) 904 375 (true, L1279_cp1.1, L1279_cp1.2)) 1279 640 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1279_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1279_fin) true) L1279_seg1) (by decide) rfl L1279_fin ptTest_fst
noncomputable def H1279_cp1 : Nat × Nat := t7val% (fastRun pH1279 1 903 (init pH1279) (init pH1279))
theorem H1279_seg1 : segOK pH1279 1 903 (init pH1279) (init pH1279) H1279_cp1.1 H1279_cp1.2 = true := by
  decide +kernel
theorem H1279_fin : (prmOK pH1279 1279 && ptTest pH1279 (runFrom pH1279 (fmask pH1279) (cmask pH1279) (hmask pH1279) 904 375 (true, H1279_cp1.1, H1279_cp1.2)) 1279 640 true) = true := by
  decide +kernel
theorem H1279_ok : RunOK pH1279 1279 (runFrom pH1279 (fmask pH1279) (cmask pH1279) (hmask pH1279) 904 375 (true, H1279_cp1.1, H1279_cp1.2)) ∧ ptTest pH1279 (runFrom pH1279 (fmask pH1279) (cmask pH1279) (hmask pH1279) 904 375 (true, H1279_cp1.1, H1279_cp1.2)) 1279 640 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1279_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1279_fin) true) H1279_seg1) (by decide) rfl H1279_fin ptTest_fst
noncomputable def I1279_cp1 : Nat × Nat := t7val% (fastRun pI1279 1 903 (init pI1279) (init pI1279))
theorem I1279_seg1 : segOK pI1279 1 903 (init pI1279) (init pI1279) I1279_cp1.1 I1279_cp1.2 = true := by
  decide +kernel
theorem I1279_fin : (prmOK pI1279 1279 && intTest pI1279 (runFrom pI1279 (fmask pI1279) (cmask pI1279) (hmask pI1279) 904 375 (true, I1279_cp1.1, I1279_cp1.2)) 1279 19 false) = true := by
  decide +kernel
theorem I1279_ok : RunOK pI1279 1279 (runFrom pI1279 (fmask pI1279) (cmask pI1279) (hmask pI1279) 904 375 (true, I1279_cp1.1, I1279_cp1.2)) ∧ intTest pI1279 (runFrom pI1279 (fmask pI1279) (cmask pI1279) (hmask pI1279) 904 375 (true, I1279_cp1.1, I1279_cp1.2)) 1279 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1279_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1279_fin) true) I1279_seg1) (by decide) rfl I1279_fin intTest_fst
theorem link1279 : linkOK pL1279 pH1279 pI1279 = true := by decide +kernel
theorem cvx1279 : ConvexBetweenHumps 1279 :=
  cvx_of L1279_ok H1279_ok I1279_ok link1279 (by decide)

/-! ### `N = 1280` -/

def pL1280 : Prm := ⟨77, 36, 38, 1282, 11, 18446744073709551616, 141517153203468483, 141517153203468483⟩
def pH1280 : Prm := ⟨77, 36, 38, 1282, 11, 18446744073709551616, 141519352226724035, 141519352226724035⟩
def pI1280 : Prm := ⟨66, 33, 30, 1282, 11, 18446744073709551616, 141517153203468483, 141519352226724035⟩
noncomputable def L1280_cp1 : Nat × Nat := t7val% (fastRun pL1280 1 904 (init pL1280) (init pL1280))
theorem L1280_seg1 : segOK pL1280 1 904 (init pL1280) (init pL1280) L1280_cp1.1 L1280_cp1.2 = true := by
  decide +kernel
theorem L1280_fin : (prmOK pL1280 1280 && ptTest pL1280 (runFrom pL1280 (fmask pL1280) (cmask pL1280) (hmask pL1280) 905 375 (true, L1280_cp1.1, L1280_cp1.2)) 1280 640 false) = true := by
  decide +kernel
theorem L1280_ok : RunOK pL1280 1280 (runFrom pL1280 (fmask pL1280) (cmask pL1280) (hmask pL1280) 905 375 (true, L1280_cp1.1, L1280_cp1.2)) ∧ ptTest pL1280 (runFrom pL1280 (fmask pL1280) (cmask pL1280) (hmask pL1280) 905 375 (true, L1280_cp1.1, L1280_cp1.2)) 1280 640 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1280_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1280_fin) true) L1280_seg1) (by decide) rfl L1280_fin ptTest_fst
noncomputable def H1280_cp1 : Nat × Nat := t7val% (fastRun pH1280 1 904 (init pH1280) (init pH1280))
theorem H1280_seg1 : segOK pH1280 1 904 (init pH1280) (init pH1280) H1280_cp1.1 H1280_cp1.2 = true := by
  decide +kernel
theorem H1280_fin : (prmOK pH1280 1280 && ptTest pH1280 (runFrom pH1280 (fmask pH1280) (cmask pH1280) (hmask pH1280) 905 375 (true, H1280_cp1.1, H1280_cp1.2)) 1280 640 true) = true := by
  decide +kernel
theorem H1280_ok : RunOK pH1280 1280 (runFrom pH1280 (fmask pH1280) (cmask pH1280) (hmask pH1280) 905 375 (true, H1280_cp1.1, H1280_cp1.2)) ∧ ptTest pH1280 (runFrom pH1280 (fmask pH1280) (cmask pH1280) (hmask pH1280) 905 375 (true, H1280_cp1.1, H1280_cp1.2)) 1280 640 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1280_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1280_fin) true) H1280_seg1) (by decide) rfl H1280_fin ptTest_fst
noncomputable def I1280_cp1 : Nat × Nat := t7val% (fastRun pI1280 1 904 (init pI1280) (init pI1280))
theorem I1280_seg1 : segOK pI1280 1 904 (init pI1280) (init pI1280) I1280_cp1.1 I1280_cp1.2 = true := by
  decide +kernel
theorem I1280_fin : (prmOK pI1280 1280 && intTest pI1280 (runFrom pI1280 (fmask pI1280) (cmask pI1280) (hmask pI1280) 905 375 (true, I1280_cp1.1, I1280_cp1.2)) 1280 19 true) = true := by
  decide +kernel
theorem I1280_ok : RunOK pI1280 1280 (runFrom pI1280 (fmask pI1280) (cmask pI1280) (hmask pI1280) 905 375 (true, I1280_cp1.1, I1280_cp1.2)) ∧ intTest pI1280 (runFrom pI1280 (fmask pI1280) (cmask pI1280) (hmask pI1280) 905 375 (true, I1280_cp1.1, I1280_cp1.2)) 1280 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1280_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1280_fin) true) I1280_seg1) (by decide) rfl I1280_fin intTest_fst
theorem link1280 : linkOK pL1280 pH1280 pI1280 = true := by decide +kernel
theorem cvx1280 : ConvexBetweenHumps 1280 :=
  cvx_of L1280_ok H1280_ok I1280_ok link1280 (by decide)
theorem cenlink1280 : cenLinkOK pI1280 1280 = true := by decide +kernel
theorem cen1280 : CenterUniqueMin 1280 ∧ DipHyp 1280 ∧ OnePointHyps 1280 :=
  cen_of L1280_ok H1280_ok I1280_ok link1280 cenlink1280

/-! ### `N = 1281` -/

def pL1281 : Prm := ⟨77, 36, 38, 1283, 11, 18446744073709551616, 141427858806983316, 141427858806983316⟩
def pH1281 : Prm := ⟨77, 36, 38, 1283, 11, 18446744073709551616, 141430057830238868, 141430057830238868⟩
def pI1281 : Prm := ⟨66, 33, 30, 1283, 11, 18446744073709551616, 141427858806983316, 141430057830238868⟩
noncomputable def L1281_cp1 : Nat × Nat := t7val% (fastRun pL1281 1 905 (init pL1281) (init pL1281))
theorem L1281_seg1 : segOK pL1281 1 905 (init pL1281) (init pL1281) L1281_cp1.1 L1281_cp1.2 = true := by
  decide +kernel
theorem L1281_fin : (prmOK pL1281 1281 && ptTest pL1281 (runFrom pL1281 (fmask pL1281) (cmask pL1281) (hmask pL1281) 906 375 (true, L1281_cp1.1, L1281_cp1.2)) 1281 641 false) = true := by
  decide +kernel
theorem L1281_ok : RunOK pL1281 1281 (runFrom pL1281 (fmask pL1281) (cmask pL1281) (hmask pL1281) 906 375 (true, L1281_cp1.1, L1281_cp1.2)) ∧ ptTest pL1281 (runFrom pL1281 (fmask pL1281) (cmask pL1281) (hmask pL1281) 906 375 (true, L1281_cp1.1, L1281_cp1.2)) 1281 641 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1281_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1281_fin) true) L1281_seg1) (by decide) rfl L1281_fin ptTest_fst
noncomputable def H1281_cp1 : Nat × Nat := t7val% (fastRun pH1281 1 905 (init pH1281) (init pH1281))
theorem H1281_seg1 : segOK pH1281 1 905 (init pH1281) (init pH1281) H1281_cp1.1 H1281_cp1.2 = true := by
  decide +kernel
theorem H1281_fin : (prmOK pH1281 1281 && ptTest pH1281 (runFrom pH1281 (fmask pH1281) (cmask pH1281) (hmask pH1281) 906 375 (true, H1281_cp1.1, H1281_cp1.2)) 1281 641 true) = true := by
  decide +kernel
theorem H1281_ok : RunOK pH1281 1281 (runFrom pH1281 (fmask pH1281) (cmask pH1281) (hmask pH1281) 906 375 (true, H1281_cp1.1, H1281_cp1.2)) ∧ ptTest pH1281 (runFrom pH1281 (fmask pH1281) (cmask pH1281) (hmask pH1281) 906 375 (true, H1281_cp1.1, H1281_cp1.2)) 1281 641 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1281_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1281_fin) true) H1281_seg1) (by decide) rfl H1281_fin ptTest_fst
noncomputable def I1281_cp1 : Nat × Nat := t7val% (fastRun pI1281 1 905 (init pI1281) (init pI1281))
theorem I1281_seg1 : segOK pI1281 1 905 (init pI1281) (init pI1281) I1281_cp1.1 I1281_cp1.2 = true := by
  decide +kernel
theorem I1281_fin : (prmOK pI1281 1281 && intTest pI1281 (runFrom pI1281 (fmask pI1281) (cmask pI1281) (hmask pI1281) 906 375 (true, I1281_cp1.1, I1281_cp1.2)) 1281 19 false) = true := by
  decide +kernel
theorem I1281_ok : RunOK pI1281 1281 (runFrom pI1281 (fmask pI1281) (cmask pI1281) (hmask pI1281) 906 375 (true, I1281_cp1.1, I1281_cp1.2)) ∧ intTest pI1281 (runFrom pI1281 (fmask pI1281) (cmask pI1281) (hmask pI1281) 906 375 (true, I1281_cp1.1, I1281_cp1.2)) 1281 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1281_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1281_fin) true) I1281_seg1) (by decide) rfl I1281_fin intTest_fst
theorem link1281 : linkOK pL1281 pH1281 pI1281 = true := by decide +kernel
theorem cvx1281 : ConvexBetweenHumps 1281 :=
  cvx_of L1281_ok H1281_ok I1281_ok link1281 (by decide)

/-! ### `N = 1282` -/

def pL1282 : Prm := ⟨77, 36, 38, 1284, 11, 18446744073709551616, 141338741401141471, 141338741401141471⟩
def pH1282 : Prm := ⟨77, 36, 38, 1284, 11, 18446744073709551616, 141340940424397023, 141340940424397023⟩
def pI1282 : Prm := ⟨66, 33, 30, 1284, 11, 18446744073709551616, 141338741401141471, 141340940424397023⟩
noncomputable def L1282_cp1 : Nat × Nat := t7val% (fastRun pL1282 1 906 (init pL1282) (init pL1282))
theorem L1282_seg1 : segOK pL1282 1 906 (init pL1282) (init pL1282) L1282_cp1.1 L1282_cp1.2 = true := by
  decide +kernel
theorem L1282_fin : (prmOK pL1282 1282 && ptTest pL1282 (runFrom pL1282 (fmask pL1282) (cmask pL1282) (hmask pL1282) 907 375 (true, L1282_cp1.1, L1282_cp1.2)) 1282 641 false) = true := by
  decide +kernel
theorem L1282_ok : RunOK pL1282 1282 (runFrom pL1282 (fmask pL1282) (cmask pL1282) (hmask pL1282) 907 375 (true, L1282_cp1.1, L1282_cp1.2)) ∧ ptTest pL1282 (runFrom pL1282 (fmask pL1282) (cmask pL1282) (hmask pL1282) 907 375 (true, L1282_cp1.1, L1282_cp1.2)) 1282 641 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1282_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1282_fin) true) L1282_seg1) (by decide) rfl L1282_fin ptTest_fst
noncomputable def H1282_cp1 : Nat × Nat := t7val% (fastRun pH1282 1 906 (init pH1282) (init pH1282))
theorem H1282_seg1 : segOK pH1282 1 906 (init pH1282) (init pH1282) H1282_cp1.1 H1282_cp1.2 = true := by
  decide +kernel
theorem H1282_fin : (prmOK pH1282 1282 && ptTest pH1282 (runFrom pH1282 (fmask pH1282) (cmask pH1282) (hmask pH1282) 907 375 (true, H1282_cp1.1, H1282_cp1.2)) 1282 641 true) = true := by
  decide +kernel
theorem H1282_ok : RunOK pH1282 1282 (runFrom pH1282 (fmask pH1282) (cmask pH1282) (hmask pH1282) 907 375 (true, H1282_cp1.1, H1282_cp1.2)) ∧ ptTest pH1282 (runFrom pH1282 (fmask pH1282) (cmask pH1282) (hmask pH1282) 907 375 (true, H1282_cp1.1, H1282_cp1.2)) 1282 641 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1282_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1282_fin) true) H1282_seg1) (by decide) rfl H1282_fin ptTest_fst
noncomputable def I1282_cp1 : Nat × Nat := t7val% (fastRun pI1282 1 906 (init pI1282) (init pI1282))
theorem I1282_seg1 : segOK pI1282 1 906 (init pI1282) (init pI1282) I1282_cp1.1 I1282_cp1.2 = true := by
  decide +kernel
theorem I1282_fin : (prmOK pI1282 1282 && intTest pI1282 (runFrom pI1282 (fmask pI1282) (cmask pI1282) (hmask pI1282) 907 375 (true, I1282_cp1.1, I1282_cp1.2)) 1282 19 true) = true := by
  decide +kernel
theorem I1282_ok : RunOK pI1282 1282 (runFrom pI1282 (fmask pI1282) (cmask pI1282) (hmask pI1282) 907 375 (true, I1282_cp1.1, I1282_cp1.2)) ∧ intTest pI1282 (runFrom pI1282 (fmask pI1282) (cmask pI1282) (hmask pI1282) 907 375 (true, I1282_cp1.1, I1282_cp1.2)) 1282 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1282_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1282_fin) true) I1282_seg1) (by decide) rfl I1282_fin intTest_fst
theorem link1282 : linkOK pL1282 pH1282 pI1282 = true := by decide +kernel
theorem cvx1282 : ConvexBetweenHumps 1282 :=
  cvx_of L1282_ok H1282_ok I1282_ok link1282 (by decide)
theorem cenlink1282 : cenLinkOK pI1282 1282 = true := by decide +kernel
theorem cen1282 : CenterUniqueMin 1282 ∧ DipHyp 1282 ∧ OnePointHyps 1282 :=
  cen_of L1282_ok H1282_ok I1282_ok link1282 cenlink1282

/-! ### `N = 1283` -/

def pL1283 : Prm := ⟨77, 36, 38, 1285, 11, 18446744073709551616, 141249692300290964, 141249692300290964⟩
def pH1283 : Prm := ⟨77, 36, 38, 1285, 11, 18446744073709551616, 141251891323546516, 141251891323546516⟩
def pI1283 : Prm := ⟨66, 33, 30, 1285, 11, 18446744073709551616, 141249692300290964, 141251891323546516⟩
noncomputable def L1283_cp1 : Nat × Nat := t7val% (fastRun pL1283 1 906 (init pL1283) (init pL1283))
theorem L1283_seg1 : segOK pL1283 1 906 (init pL1283) (init pL1283) L1283_cp1.1 L1283_cp1.2 = true := by
  decide +kernel
theorem L1283_fin : (prmOK pL1283 1283 && ptTest pL1283 (runFrom pL1283 (fmask pL1283) (cmask pL1283) (hmask pL1283) 907 376 (true, L1283_cp1.1, L1283_cp1.2)) 1283 642 false) = true := by
  decide +kernel
theorem L1283_ok : RunOK pL1283 1283 (runFrom pL1283 (fmask pL1283) (cmask pL1283) (hmask pL1283) 907 376 (true, L1283_cp1.1, L1283_cp1.2)) ∧ ptTest pL1283 (runFrom pL1283 (fmask pL1283) (cmask pL1283) (hmask pL1283) 907 376 (true, L1283_cp1.1, L1283_cp1.2)) 1283 642 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1283_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1283_fin) true) L1283_seg1) (by decide) rfl L1283_fin ptTest_fst
noncomputable def H1283_cp1 : Nat × Nat := t7val% (fastRun pH1283 1 906 (init pH1283) (init pH1283))
theorem H1283_seg1 : segOK pH1283 1 906 (init pH1283) (init pH1283) H1283_cp1.1 H1283_cp1.2 = true := by
  decide +kernel
theorem H1283_fin : (prmOK pH1283 1283 && ptTest pH1283 (runFrom pH1283 (fmask pH1283) (cmask pH1283) (hmask pH1283) 907 376 (true, H1283_cp1.1, H1283_cp1.2)) 1283 642 true) = true := by
  decide +kernel
theorem H1283_ok : RunOK pH1283 1283 (runFrom pH1283 (fmask pH1283) (cmask pH1283) (hmask pH1283) 907 376 (true, H1283_cp1.1, H1283_cp1.2)) ∧ ptTest pH1283 (runFrom pH1283 (fmask pH1283) (cmask pH1283) (hmask pH1283) 907 376 (true, H1283_cp1.1, H1283_cp1.2)) 1283 642 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1283_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1283_fin) true) H1283_seg1) (by decide) rfl H1283_fin ptTest_fst
noncomputable def I1283_cp1 : Nat × Nat := t7val% (fastRun pI1283 1 906 (init pI1283) (init pI1283))
theorem I1283_seg1 : segOK pI1283 1 906 (init pI1283) (init pI1283) I1283_cp1.1 I1283_cp1.2 = true := by
  decide +kernel
theorem I1283_fin : (prmOK pI1283 1283 && intTest pI1283 (runFrom pI1283 (fmask pI1283) (cmask pI1283) (hmask pI1283) 907 376 (true, I1283_cp1.1, I1283_cp1.2)) 1283 19 false) = true := by
  decide +kernel
theorem I1283_ok : RunOK pI1283 1283 (runFrom pI1283 (fmask pI1283) (cmask pI1283) (hmask pI1283) 907 376 (true, I1283_cp1.1, I1283_cp1.2)) ∧ intTest pI1283 (runFrom pI1283 (fmask pI1283) (cmask pI1283) (hmask pI1283) 907 376 (true, I1283_cp1.1, I1283_cp1.2)) 1283 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1283_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1283_fin) true) I1283_seg1) (by decide) rfl I1283_fin intTest_fst
theorem link1283 : linkOK pL1283 pH1283 pI1283 = true := by decide +kernel
theorem cvx1283 : ConvexBetweenHumps 1283 :=
  cvx_of L1283_ok H1283_ok I1283_ok link1283 (by decide)

/-! ### `N = 1284` -/

def pL1284 : Prm := ⟨77, 36, 38, 1286, 11, 18446744073709551616, 141160819410727290, 141160819410727290⟩
def pH1284 : Prm := ⟨77, 36, 38, 1286, 11, 18446744073709551616, 141163018433982842, 141163018433982842⟩
def pI1284 : Prm := ⟨66, 33, 30, 1286, 11, 18446744073709551616, 141160819410727290, 141163018433982842⟩
noncomputable def L1284_cp1 : Nat × Nat := t7val% (fastRun pL1284 1 907 (init pL1284) (init pL1284))
theorem L1284_seg1 : segOK pL1284 1 907 (init pL1284) (init pL1284) L1284_cp1.1 L1284_cp1.2 = true := by
  decide +kernel
theorem L1284_fin : (prmOK pL1284 1284 && ptTest pL1284 (runFrom pL1284 (fmask pL1284) (cmask pL1284) (hmask pL1284) 908 376 (true, L1284_cp1.1, L1284_cp1.2)) 1284 642 false) = true := by
  decide +kernel
theorem L1284_ok : RunOK pL1284 1284 (runFrom pL1284 (fmask pL1284) (cmask pL1284) (hmask pL1284) 908 376 (true, L1284_cp1.1, L1284_cp1.2)) ∧ ptTest pL1284 (runFrom pL1284 (fmask pL1284) (cmask pL1284) (hmask pL1284) 908 376 (true, L1284_cp1.1, L1284_cp1.2)) 1284 642 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1284_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1284_fin) true) L1284_seg1) (by decide) rfl L1284_fin ptTest_fst
noncomputable def H1284_cp1 : Nat × Nat := t7val% (fastRun pH1284 1 907 (init pH1284) (init pH1284))
theorem H1284_seg1 : segOK pH1284 1 907 (init pH1284) (init pH1284) H1284_cp1.1 H1284_cp1.2 = true := by
  decide +kernel
theorem H1284_fin : (prmOK pH1284 1284 && ptTest pH1284 (runFrom pH1284 (fmask pH1284) (cmask pH1284) (hmask pH1284) 908 376 (true, H1284_cp1.1, H1284_cp1.2)) 1284 642 true) = true := by
  decide +kernel
theorem H1284_ok : RunOK pH1284 1284 (runFrom pH1284 (fmask pH1284) (cmask pH1284) (hmask pH1284) 908 376 (true, H1284_cp1.1, H1284_cp1.2)) ∧ ptTest pH1284 (runFrom pH1284 (fmask pH1284) (cmask pH1284) (hmask pH1284) 908 376 (true, H1284_cp1.1, H1284_cp1.2)) 1284 642 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1284_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1284_fin) true) H1284_seg1) (by decide) rfl H1284_fin ptTest_fst
noncomputable def I1284_cp1 : Nat × Nat := t7val% (fastRun pI1284 1 907 (init pI1284) (init pI1284))
theorem I1284_seg1 : segOK pI1284 1 907 (init pI1284) (init pI1284) I1284_cp1.1 I1284_cp1.2 = true := by
  decide +kernel
theorem I1284_fin : (prmOK pI1284 1284 && intTest pI1284 (runFrom pI1284 (fmask pI1284) (cmask pI1284) (hmask pI1284) 908 376 (true, I1284_cp1.1, I1284_cp1.2)) 1284 19 true) = true := by
  decide +kernel
theorem I1284_ok : RunOK pI1284 1284 (runFrom pI1284 (fmask pI1284) (cmask pI1284) (hmask pI1284) 908 376 (true, I1284_cp1.1, I1284_cp1.2)) ∧ intTest pI1284 (runFrom pI1284 (fmask pI1284) (cmask pI1284) (hmask pI1284) 908 376 (true, I1284_cp1.1, I1284_cp1.2)) 1284 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1284_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1284_fin) true) I1284_seg1) (by decide) rfl I1284_fin intTest_fst
theorem link1284 : linkOK pL1284 pH1284 pI1284 = true := by decide +kernel
theorem cvx1284 : ConvexBetweenHumps 1284 :=
  cvx_of L1284_ok H1284_ok I1284_ok link1284 (by decide)
theorem cenlink1284 : cenLinkOK pI1284 1284 = true := by decide +kernel
theorem cen1284 : CenterUniqueMin 1284 ∧ DipHyp 1284 ∧ OnePointHyps 1284 :=
  cen_of L1284_ok H1284_ok I1284_ok link1284 cenlink1284

/-! ### `N = 1285` -/

def pL1285 : Prm := ⟨77, 36, 38, 1287, 11, 18446744073709551616, 141072014562956809, 141072014562956809⟩
def pH1285 : Prm := ⟨77, 36, 38, 1287, 11, 18446744073709551616, 141074213586212361, 141074213586212361⟩
def pI1285 : Prm := ⟨66, 33, 30, 1287, 11, 18446744073709551616, 141072014562956809, 141074213586212361⟩
noncomputable def L1285_cp1 : Nat × Nat := t7val% (fastRun pL1285 1 908 (init pL1285) (init pL1285))
theorem L1285_seg1 : segOK pL1285 1 908 (init pL1285) (init pL1285) L1285_cp1.1 L1285_cp1.2 = true := by
  decide +kernel
theorem L1285_fin : (prmOK pL1285 1285 && ptTest pL1285 (runFrom pL1285 (fmask pL1285) (cmask pL1285) (hmask pL1285) 909 376 (true, L1285_cp1.1, L1285_cp1.2)) 1285 643 false) = true := by
  decide +kernel
theorem L1285_ok : RunOK pL1285 1285 (runFrom pL1285 (fmask pL1285) (cmask pL1285) (hmask pL1285) 909 376 (true, L1285_cp1.1, L1285_cp1.2)) ∧ ptTest pL1285 (runFrom pL1285 (fmask pL1285) (cmask pL1285) (hmask pL1285) 909 376 (true, L1285_cp1.1, L1285_cp1.2)) 1285 643 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1285_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1285_fin) true) L1285_seg1) (by decide) rfl L1285_fin ptTest_fst
noncomputable def H1285_cp1 : Nat × Nat := t7val% (fastRun pH1285 1 908 (init pH1285) (init pH1285))
theorem H1285_seg1 : segOK pH1285 1 908 (init pH1285) (init pH1285) H1285_cp1.1 H1285_cp1.2 = true := by
  decide +kernel
theorem H1285_fin : (prmOK pH1285 1285 && ptTest pH1285 (runFrom pH1285 (fmask pH1285) (cmask pH1285) (hmask pH1285) 909 376 (true, H1285_cp1.1, H1285_cp1.2)) 1285 643 true) = true := by
  decide +kernel
theorem H1285_ok : RunOK pH1285 1285 (runFrom pH1285 (fmask pH1285) (cmask pH1285) (hmask pH1285) 909 376 (true, H1285_cp1.1, H1285_cp1.2)) ∧ ptTest pH1285 (runFrom pH1285 (fmask pH1285) (cmask pH1285) (hmask pH1285) 909 376 (true, H1285_cp1.1, H1285_cp1.2)) 1285 643 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1285_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1285_fin) true) H1285_seg1) (by decide) rfl H1285_fin ptTest_fst
noncomputable def I1285_cp1 : Nat × Nat := t7val% (fastRun pI1285 1 908 (init pI1285) (init pI1285))
theorem I1285_seg1 : segOK pI1285 1 908 (init pI1285) (init pI1285) I1285_cp1.1 I1285_cp1.2 = true := by
  decide +kernel
theorem I1285_fin : (prmOK pI1285 1285 && intTest pI1285 (runFrom pI1285 (fmask pI1285) (cmask pI1285) (hmask pI1285) 909 376 (true, I1285_cp1.1, I1285_cp1.2)) 1285 19 false) = true := by
  decide +kernel
theorem I1285_ok : RunOK pI1285 1285 (runFrom pI1285 (fmask pI1285) (cmask pI1285) (hmask pI1285) 909 376 (true, I1285_cp1.1, I1285_cp1.2)) ∧ intTest pI1285 (runFrom pI1285 (fmask pI1285) (cmask pI1285) (hmask pI1285) 909 376 (true, I1285_cp1.1, I1285_cp1.2)) 1285 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1285_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1285_fin) true) I1285_seg1) (by decide) rfl I1285_fin intTest_fst
theorem link1285 : linkOK pL1285 pH1285 pI1285 = true := by decide +kernel
theorem cvx1285 : ConvexBetweenHumps 1285 :=
  cvx_of L1285_ok H1285_ok I1285_ok link1285 (by decide)

/-! ### `N = 1286` -/

def pL1286 : Prm := ⟨77, 36, 38, 1288, 11, 18446744073709551616, 140983385151746803, 140983385151746803⟩
def pH1286 : Prm := ⟨77, 36, 38, 1288, 11, 18446744073709551616, 140985584175002355, 140985584175002355⟩
def pI1286 : Prm := ⟨66, 33, 30, 1288, 11, 18446744073709551616, 140983385151746803, 140985584175002355⟩
noncomputable def L1286_cp1 : Nat × Nat := t7val% (fastRun pL1286 1 908 (init pL1286) (init pL1286))
theorem L1286_seg1 : segOK pL1286 1 908 (init pL1286) (init pL1286) L1286_cp1.1 L1286_cp1.2 = true := by
  decide +kernel
theorem L1286_fin : (prmOK pL1286 1286 && ptTest pL1286 (runFrom pL1286 (fmask pL1286) (cmask pL1286) (hmask pL1286) 909 377 (true, L1286_cp1.1, L1286_cp1.2)) 1286 643 false) = true := by
  decide +kernel
theorem L1286_ok : RunOK pL1286 1286 (runFrom pL1286 (fmask pL1286) (cmask pL1286) (hmask pL1286) 909 377 (true, L1286_cp1.1, L1286_cp1.2)) ∧ ptTest pL1286 (runFrom pL1286 (fmask pL1286) (cmask pL1286) (hmask pL1286) 909 377 (true, L1286_cp1.1, L1286_cp1.2)) 1286 643 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1286_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1286_fin) true) L1286_seg1) (by decide) rfl L1286_fin ptTest_fst
noncomputable def H1286_cp1 : Nat × Nat := t7val% (fastRun pH1286 1 908 (init pH1286) (init pH1286))
theorem H1286_seg1 : segOK pH1286 1 908 (init pH1286) (init pH1286) H1286_cp1.1 H1286_cp1.2 = true := by
  decide +kernel
theorem H1286_fin : (prmOK pH1286 1286 && ptTest pH1286 (runFrom pH1286 (fmask pH1286) (cmask pH1286) (hmask pH1286) 909 377 (true, H1286_cp1.1, H1286_cp1.2)) 1286 643 true) = true := by
  decide +kernel
theorem H1286_ok : RunOK pH1286 1286 (runFrom pH1286 (fmask pH1286) (cmask pH1286) (hmask pH1286) 909 377 (true, H1286_cp1.1, H1286_cp1.2)) ∧ ptTest pH1286 (runFrom pH1286 (fmask pH1286) (cmask pH1286) (hmask pH1286) 909 377 (true, H1286_cp1.1, H1286_cp1.2)) 1286 643 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1286_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1286_fin) true) H1286_seg1) (by decide) rfl H1286_fin ptTest_fst
noncomputable def I1286_cp1 : Nat × Nat := t7val% (fastRun pI1286 1 908 (init pI1286) (init pI1286))
theorem I1286_seg1 : segOK pI1286 1 908 (init pI1286) (init pI1286) I1286_cp1.1 I1286_cp1.2 = true := by
  decide +kernel
theorem I1286_fin : (prmOK pI1286 1286 && intTest pI1286 (runFrom pI1286 (fmask pI1286) (cmask pI1286) (hmask pI1286) 909 377 (true, I1286_cp1.1, I1286_cp1.2)) 1286 19 true) = true := by
  decide +kernel
theorem I1286_ok : RunOK pI1286 1286 (runFrom pI1286 (fmask pI1286) (cmask pI1286) (hmask pI1286) 909 377 (true, I1286_cp1.1, I1286_cp1.2)) ∧ intTest pI1286 (runFrom pI1286 (fmask pI1286) (cmask pI1286) (hmask pI1286) 909 377 (true, I1286_cp1.1, I1286_cp1.2)) 1286 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1286_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1286_fin) true) I1286_seg1) (by decide) rfl I1286_fin intTest_fst
theorem link1286 : linkOK pL1286 pH1286 pI1286 = true := by decide +kernel
theorem cvx1286 : ConvexBetweenHumps 1286 :=
  cvx_of L1286_ok H1286_ok I1286_ok link1286 (by decide)
theorem cenlink1286 : cenLinkOK pI1286 1286 = true := by decide +kernel
theorem cen1286 : CenterUniqueMin 1286 ∧ DipHyp 1286 ∧ OnePointHyps 1286 :=
  cen_of L1286_ok H1286_ok I1286_ok link1286 cenlink1286

/-! ### `N = 1287` -/

def pL1287 : Prm := ⟨77, 36, 38, 1289, 11, 18446744073709551616, 140894823520515351, 140894823520515351⟩
def pH1287 : Prm := ⟨77, 36, 38, 1289, 11, 18446744073709551616, 140897022543770903, 140897022543770903⟩
def pI1287 : Prm := ⟨66, 33, 30, 1289, 11, 18446744073709551616, 140894823520515351, 140897022543770903⟩
noncomputable def L1287_cp1 : Nat × Nat := t7val% (fastRun pL1287 1 909 (init pL1287) (init pL1287))
theorem L1287_seg1 : segOK pL1287 1 909 (init pL1287) (init pL1287) L1287_cp1.1 L1287_cp1.2 = true := by
  decide +kernel
theorem L1287_fin : (prmOK pL1287 1287 && ptTest pL1287 (runFrom pL1287 (fmask pL1287) (cmask pL1287) (hmask pL1287) 910 377 (true, L1287_cp1.1, L1287_cp1.2)) 1287 644 false) = true := by
  decide +kernel
theorem L1287_ok : RunOK pL1287 1287 (runFrom pL1287 (fmask pL1287) (cmask pL1287) (hmask pL1287) 910 377 (true, L1287_cp1.1, L1287_cp1.2)) ∧ ptTest pL1287 (runFrom pL1287 (fmask pL1287) (cmask pL1287) (hmask pL1287) 910 377 (true, L1287_cp1.1, L1287_cp1.2)) 1287 644 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1287_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1287_fin) true) L1287_seg1) (by decide) rfl L1287_fin ptTest_fst
noncomputable def H1287_cp1 : Nat × Nat := t7val% (fastRun pH1287 1 909 (init pH1287) (init pH1287))
theorem H1287_seg1 : segOK pH1287 1 909 (init pH1287) (init pH1287) H1287_cp1.1 H1287_cp1.2 = true := by
  decide +kernel
theorem H1287_fin : (prmOK pH1287 1287 && ptTest pH1287 (runFrom pH1287 (fmask pH1287) (cmask pH1287) (hmask pH1287) 910 377 (true, H1287_cp1.1, H1287_cp1.2)) 1287 644 true) = true := by
  decide +kernel
theorem H1287_ok : RunOK pH1287 1287 (runFrom pH1287 (fmask pH1287) (cmask pH1287) (hmask pH1287) 910 377 (true, H1287_cp1.1, H1287_cp1.2)) ∧ ptTest pH1287 (runFrom pH1287 (fmask pH1287) (cmask pH1287) (hmask pH1287) 910 377 (true, H1287_cp1.1, H1287_cp1.2)) 1287 644 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1287_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1287_fin) true) H1287_seg1) (by decide) rfl H1287_fin ptTest_fst
noncomputable def I1287_cp1 : Nat × Nat := t7val% (fastRun pI1287 1 909 (init pI1287) (init pI1287))
theorem I1287_seg1 : segOK pI1287 1 909 (init pI1287) (init pI1287) I1287_cp1.1 I1287_cp1.2 = true := by
  decide +kernel
theorem I1287_fin : (prmOK pI1287 1287 && intTest pI1287 (runFrom pI1287 (fmask pI1287) (cmask pI1287) (hmask pI1287) 910 377 (true, I1287_cp1.1, I1287_cp1.2)) 1287 19 false) = true := by
  decide +kernel
theorem I1287_ok : RunOK pI1287 1287 (runFrom pI1287 (fmask pI1287) (cmask pI1287) (hmask pI1287) 910 377 (true, I1287_cp1.1, I1287_cp1.2)) ∧ intTest pI1287 (runFrom pI1287 (fmask pI1287) (cmask pI1287) (hmask pI1287) 910 377 (true, I1287_cp1.1, I1287_cp1.2)) 1287 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1287_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1287_fin) true) I1287_seg1) (by decide) rfl I1287_fin intTest_fst
theorem link1287 : linkOK pL1287 pH1287 pI1287 = true := by decide +kernel
theorem cvx1287 : ConvexBetweenHumps 1287 :=
  cvx_of L1287_ok H1287_ok I1287_ok link1287 (by decide)

/-! ### `N = 1288` -/

def pL1288 : Prm := ⟨77, 36, 38, 1290, 11, 18446744073709551616, 140806436555711256, 140806436555711256⟩
def pH1288 : Prm := ⟨77, 36, 38, 1290, 11, 18446744073709551616, 140808635578966808, 140808635578966808⟩
def pI1288 : Prm := ⟨66, 33, 30, 1290, 11, 18446744073709551616, 140806436555711256, 140808635578966808⟩
noncomputable def L1288_cp1 : Nat × Nat := t7val% (fastRun pL1288 1 910 (init pL1288) (init pL1288))
theorem L1288_seg1 : segOK pL1288 1 910 (init pL1288) (init pL1288) L1288_cp1.1 L1288_cp1.2 = true := by
  decide +kernel
theorem L1288_fin : (prmOK pL1288 1288 && ptTest pL1288 (runFrom pL1288 (fmask pL1288) (cmask pL1288) (hmask pL1288) 911 377 (true, L1288_cp1.1, L1288_cp1.2)) 1288 644 false) = true := by
  decide +kernel
theorem L1288_ok : RunOK pL1288 1288 (runFrom pL1288 (fmask pL1288) (cmask pL1288) (hmask pL1288) 911 377 (true, L1288_cp1.1, L1288_cp1.2)) ∧ ptTest pL1288 (runFrom pL1288 (fmask pL1288) (cmask pL1288) (hmask pL1288) 911 377 (true, L1288_cp1.1, L1288_cp1.2)) 1288 644 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1288_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1288_fin) true) L1288_seg1) (by decide) rfl L1288_fin ptTest_fst
noncomputable def H1288_cp1 : Nat × Nat := t7val% (fastRun pH1288 1 910 (init pH1288) (init pH1288))
theorem H1288_seg1 : segOK pH1288 1 910 (init pH1288) (init pH1288) H1288_cp1.1 H1288_cp1.2 = true := by
  decide +kernel
theorem H1288_fin : (prmOK pH1288 1288 && ptTest pH1288 (runFrom pH1288 (fmask pH1288) (cmask pH1288) (hmask pH1288) 911 377 (true, H1288_cp1.1, H1288_cp1.2)) 1288 644 true) = true := by
  decide +kernel
theorem H1288_ok : RunOK pH1288 1288 (runFrom pH1288 (fmask pH1288) (cmask pH1288) (hmask pH1288) 911 377 (true, H1288_cp1.1, H1288_cp1.2)) ∧ ptTest pH1288 (runFrom pH1288 (fmask pH1288) (cmask pH1288) (hmask pH1288) 911 377 (true, H1288_cp1.1, H1288_cp1.2)) 1288 644 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1288_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1288_fin) true) H1288_seg1) (by decide) rfl H1288_fin ptTest_fst
noncomputable def I1288_cp1 : Nat × Nat := t7val% (fastRun pI1288 1 910 (init pI1288) (init pI1288))
theorem I1288_seg1 : segOK pI1288 1 910 (init pI1288) (init pI1288) I1288_cp1.1 I1288_cp1.2 = true := by
  decide +kernel
theorem I1288_fin : (prmOK pI1288 1288 && intTest pI1288 (runFrom pI1288 (fmask pI1288) (cmask pI1288) (hmask pI1288) 911 377 (true, I1288_cp1.1, I1288_cp1.2)) 1288 19 true) = true := by
  decide +kernel
theorem I1288_ok : RunOK pI1288 1288 (runFrom pI1288 (fmask pI1288) (cmask pI1288) (hmask pI1288) 911 377 (true, I1288_cp1.1, I1288_cp1.2)) ∧ intTest pI1288 (runFrom pI1288 (fmask pI1288) (cmask pI1288) (hmask pI1288) 911 377 (true, I1288_cp1.1, I1288_cp1.2)) 1288 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1288_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1288_fin) true) I1288_seg1) (by decide) rfl I1288_fin intTest_fst
theorem link1288 : linkOK pL1288 pH1288 pI1288 = true := by decide +kernel
theorem cvx1288 : ConvexBetweenHumps 1288 :=
  cvx_of L1288_ok H1288_ok I1288_ok link1288 (by decide)
theorem cenlink1288 : cenLinkOK pI1288 1288 = true := by decide +kernel
theorem cen1288 : CenterUniqueMin 1288 ∧ DipHyp 1288 ∧ OnePointHyps 1288 :=
  cen_of L1288_ok H1288_ok I1288_ok link1288 cenlink1288

/-! ### `N = 1289` -/

def pL1289 : Prm := ⟨77, 36, 38, 1291, 11, 18446744073709551616, 140718117110436136, 140718117110436136⟩
def pH1289 : Prm := ⟨77, 36, 38, 1291, 11, 18446744073709551616, 140720316133691688, 140720316133691688⟩
def pI1289 : Prm := ⟨66, 33, 30, 1291, 11, 18446744073709551616, 140718117110436136, 140720316133691688⟩
noncomputable def L1289_cp1 : Nat × Nat := t7val% (fastRun pL1289 1 910 (init pL1289) (init pL1289))
theorem L1289_seg1 : segOK pL1289 1 910 (init pL1289) (init pL1289) L1289_cp1.1 L1289_cp1.2 = true := by
  decide +kernel
theorem L1289_fin : (prmOK pL1289 1289 && ptTest pL1289 (runFrom pL1289 (fmask pL1289) (cmask pL1289) (hmask pL1289) 911 378 (true, L1289_cp1.1, L1289_cp1.2)) 1289 645 false) = true := by
  decide +kernel
theorem L1289_ok : RunOK pL1289 1289 (runFrom pL1289 (fmask pL1289) (cmask pL1289) (hmask pL1289) 911 378 (true, L1289_cp1.1, L1289_cp1.2)) ∧ ptTest pL1289 (runFrom pL1289 (fmask pL1289) (cmask pL1289) (hmask pL1289) 911 378 (true, L1289_cp1.1, L1289_cp1.2)) 1289 645 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1289_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1289_fin) true) L1289_seg1) (by decide) rfl L1289_fin ptTest_fst
noncomputable def H1289_cp1 : Nat × Nat := t7val% (fastRun pH1289 1 910 (init pH1289) (init pH1289))
theorem H1289_seg1 : segOK pH1289 1 910 (init pH1289) (init pH1289) H1289_cp1.1 H1289_cp1.2 = true := by
  decide +kernel
theorem H1289_fin : (prmOK pH1289 1289 && ptTest pH1289 (runFrom pH1289 (fmask pH1289) (cmask pH1289) (hmask pH1289) 911 378 (true, H1289_cp1.1, H1289_cp1.2)) 1289 645 true) = true := by
  decide +kernel
theorem H1289_ok : RunOK pH1289 1289 (runFrom pH1289 (fmask pH1289) (cmask pH1289) (hmask pH1289) 911 378 (true, H1289_cp1.1, H1289_cp1.2)) ∧ ptTest pH1289 (runFrom pH1289 (fmask pH1289) (cmask pH1289) (hmask pH1289) 911 378 (true, H1289_cp1.1, H1289_cp1.2)) 1289 645 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1289_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1289_fin) true) H1289_seg1) (by decide) rfl H1289_fin ptTest_fst
noncomputable def I1289_cp1 : Nat × Nat := t7val% (fastRun pI1289 1 910 (init pI1289) (init pI1289))
theorem I1289_seg1 : segOK pI1289 1 910 (init pI1289) (init pI1289) I1289_cp1.1 I1289_cp1.2 = true := by
  decide +kernel
theorem I1289_fin : (prmOK pI1289 1289 && intTest pI1289 (runFrom pI1289 (fmask pI1289) (cmask pI1289) (hmask pI1289) 911 378 (true, I1289_cp1.1, I1289_cp1.2)) 1289 19 false) = true := by
  decide +kernel
theorem I1289_ok : RunOK pI1289 1289 (runFrom pI1289 (fmask pI1289) (cmask pI1289) (hmask pI1289) 911 378 (true, I1289_cp1.1, I1289_cp1.2)) ∧ intTest pI1289 (runFrom pI1289 (fmask pI1289) (cmask pI1289) (hmask pI1289) 911 378 (true, I1289_cp1.1, I1289_cp1.2)) 1289 19 false = true :=
  fin_run (runOK_seg (prmOK_of_and I1289_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1289_fin) true) I1289_seg1) (by decide) rfl I1289_fin intTest_fst
theorem link1289 : linkOK pL1289 pH1289 pI1289 = true := by decide +kernel
theorem cvx1289 : ConvexBetweenHumps 1289 :=
  cvx_of L1289_ok H1289_ok I1289_ok link1289 (by decide)

/-! ### `N = 1290` -/

def pL1290 : Prm := ⟨77, 36, 38, 1292, 11, 18446744073709551616, 140629971566030046, 140629971566030046⟩
def pH1290 : Prm := ⟨77, 36, 38, 1292, 11, 18446744073709551616, 140632170589285598, 140632170589285598⟩
def pI1290 : Prm := ⟨66, 33, 30, 1292, 11, 18446744073709551616, 140629971566030046, 140632170589285598⟩
noncomputable def L1290_cp1 : Nat × Nat := t7val% (fastRun pL1290 1 911 (init pL1290) (init pL1290))
theorem L1290_seg1 : segOK pL1290 1 911 (init pL1290) (init pL1290) L1290_cp1.1 L1290_cp1.2 = true := by
  decide +kernel
theorem L1290_fin : (prmOK pL1290 1290 && ptTest pL1290 (runFrom pL1290 (fmask pL1290) (cmask pL1290) (hmask pL1290) 912 378 (true, L1290_cp1.1, L1290_cp1.2)) 1290 645 false) = true := by
  decide +kernel
theorem L1290_ok : RunOK pL1290 1290 (runFrom pL1290 (fmask pL1290) (cmask pL1290) (hmask pL1290) 912 378 (true, L1290_cp1.1, L1290_cp1.2)) ∧ ptTest pL1290 (runFrom pL1290 (fmask pL1290) (cmask pL1290) (hmask pL1290) 912 378 (true, L1290_cp1.1, L1290_cp1.2)) 1290 645 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1290_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1290_fin) true) L1290_seg1) (by decide) rfl L1290_fin ptTest_fst
noncomputable def H1290_cp1 : Nat × Nat := t7val% (fastRun pH1290 1 911 (init pH1290) (init pH1290))
theorem H1290_seg1 : segOK pH1290 1 911 (init pH1290) (init pH1290) H1290_cp1.1 H1290_cp1.2 = true := by
  decide +kernel
theorem H1290_fin : (prmOK pH1290 1290 && ptTest pH1290 (runFrom pH1290 (fmask pH1290) (cmask pH1290) (hmask pH1290) 912 378 (true, H1290_cp1.1, H1290_cp1.2)) 1290 645 true) = true := by
  decide +kernel
theorem H1290_ok : RunOK pH1290 1290 (runFrom pH1290 (fmask pH1290) (cmask pH1290) (hmask pH1290) 912 378 (true, H1290_cp1.1, H1290_cp1.2)) ∧ ptTest pH1290 (runFrom pH1290 (fmask pH1290) (cmask pH1290) (hmask pH1290) 912 378 (true, H1290_cp1.1, H1290_cp1.2)) 1290 645 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1290_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1290_fin) true) H1290_seg1) (by decide) rfl H1290_fin ptTest_fst
noncomputable def I1290_cp1 : Nat × Nat := t7val% (fastRun pI1290 1 911 (init pI1290) (init pI1290))
theorem I1290_seg1 : segOK pI1290 1 911 (init pI1290) (init pI1290) I1290_cp1.1 I1290_cp1.2 = true := by
  decide +kernel
theorem I1290_fin : (prmOK pI1290 1290 && intTest pI1290 (runFrom pI1290 (fmask pI1290) (cmask pI1290) (hmask pI1290) 912 378 (true, I1290_cp1.1, I1290_cp1.2)) 1290 19 true) = true := by
  decide +kernel
theorem I1290_ok : RunOK pI1290 1290 (runFrom pI1290 (fmask pI1290) (cmask pI1290) (hmask pI1290) 912 378 (true, I1290_cp1.1, I1290_cp1.2)) ∧ intTest pI1290 (runFrom pI1290 (fmask pI1290) (cmask pI1290) (hmask pI1290) 912 378 (true, I1290_cp1.1, I1290_cp1.2)) 1290 19 true = true :=
  fin_run (runOK_seg (prmOK_of_and I1290_fin) (by decide) (by decide) (runOK_init (prmOK_of_and I1290_fin) true) I1290_seg1) (by decide) rfl I1290_fin intTest_fst
theorem link1290 : linkOK pL1290 pH1290 pI1290 = true := by decide +kernel
theorem cvx1290 : ConvexBetweenHumps 1290 :=
  cvx_of L1290_ok H1290_ok I1290_ok link1290 (by decide)
theorem cenlink1290 : cenLinkOK pI1290 1290 = true := by decide +kernel
theorem cen1290 : CenterUniqueMin 1290 ∧ DipHyp 1290 ∧ OnePointHyps 1290 :=
  cen_of L1290_ok H1290_ok I1290_ok link1290 cenlink1290

/-! ### The range -/

theorem cvx_1266_1290 {N : ℕ} (h1 : 1266 ≤ N) (h2 : N ≤ 1290) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1277
  · by_cases h4 : N ≤ 1271
    · by_cases h6 : N ≤ 1268
      · by_cases h8 : N ≤ 1266
        · obtain rfl : N = 1266 := by omega
          exact cvx1266
        · by_cases h10 : N ≤ 1267
          · obtain rfl : N = 1267 := by omega
            exact cvx1267
          · obtain rfl : N = 1268 := by omega
            exact cvx1268
      · by_cases h8 : N ≤ 1269
        · obtain rfl : N = 1269 := by omega
          exact cvx1269
        · by_cases h10 : N ≤ 1270
          · obtain rfl : N = 1270 := by omega
            exact cvx1270
          · obtain rfl : N = 1271 := by omega
            exact cvx1271
    · by_cases h6 : N ≤ 1274
      · by_cases h8 : N ≤ 1272
        · obtain rfl : N = 1272 := by omega
          exact cvx1272
        · by_cases h10 : N ≤ 1273
          · obtain rfl : N = 1273 := by omega
            exact cvx1273
          · obtain rfl : N = 1274 := by omega
            exact cvx1274
      · by_cases h8 : N ≤ 1275
        · obtain rfl : N = 1275 := by omega
          exact cvx1275
        · by_cases h10 : N ≤ 1276
          · obtain rfl : N = 1276 := by omega
            exact cvx1276
          · obtain rfl : N = 1277 := by omega
            exact cvx1277
  · by_cases h4 : N ≤ 1283
    · by_cases h6 : N ≤ 1280
      · by_cases h8 : N ≤ 1278
        · obtain rfl : N = 1278 := by omega
          exact cvx1278
        · by_cases h10 : N ≤ 1279
          · obtain rfl : N = 1279 := by omega
            exact cvx1279
          · obtain rfl : N = 1280 := by omega
            exact cvx1280
      · by_cases h8 : N ≤ 1281
        · obtain rfl : N = 1281 := by omega
          exact cvx1281
        · by_cases h10 : N ≤ 1282
          · obtain rfl : N = 1282 := by omega
            exact cvx1282
          · obtain rfl : N = 1283 := by omega
            exact cvx1283
    · by_cases h6 : N ≤ 1286
      · by_cases h8 : N ≤ 1284
        · obtain rfl : N = 1284 := by omega
          exact cvx1284
        · by_cases h10 : N ≤ 1285
          · obtain rfl : N = 1285 := by omega
            exact cvx1285
          · obtain rfl : N = 1286 := by omega
            exact cvx1286
      · by_cases h8 : N ≤ 1288
        · by_cases h10 : N ≤ 1287
          · obtain rfl : N = 1287 := by omega
            exact cvx1287
          · obtain rfl : N = 1288 := by omega
            exact cvx1288
        · by_cases h10 : N ≤ 1289
          · obtain rfl : N = 1289 := by omega
            exact cvx1289
          · obtain rfl : N = 1290 := by omega
            exact cvx1290

theorem cen_1266_1290 {N : ℕ} (h1 : 1266 ≤ N) (h2 : N ≤ 1290) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1276
  · by_cases h4 : N ≤ 1270
    · by_cases h6 : N ≤ 1266
      · obtain rfl : N = 1266 := by omega
        exact cen1266
      · by_cases h8 : N ≤ 1268
        · obtain rfl : N = 1268 := by omega
          exact cen1268
        · obtain rfl : N = 1270 := by omega
          exact cen1270
    · by_cases h6 : N ≤ 1272
      · obtain rfl : N = 1272 := by omega
        exact cen1272
      · by_cases h8 : N ≤ 1274
        · obtain rfl : N = 1274 := by omega
          exact cen1274
        · obtain rfl : N = 1276 := by omega
          exact cen1276
  · by_cases h4 : N ≤ 1282
    · by_cases h6 : N ≤ 1278
      · obtain rfl : N = 1278 := by omega
        exact cen1278
      · by_cases h8 : N ≤ 1280
        · obtain rfl : N = 1280 := by omega
          exact cen1280
        · obtain rfl : N = 1282 := by omega
          exact cen1282
    · by_cases h6 : N ≤ 1286
      · by_cases h8 : N ≤ 1284
        · obtain rfl : N = 1284 := by omega
          exact cen1284
        · obtain rfl : N = 1286 := by omega
          exact cen1286
      · by_cases h8 : N ≤ 1288
        · obtain rfl : N = 1288 := by omega
          exact cen1288
        · obtain rfl : N = 1290 := by omega
          exact cen1290

end Kagey131.PaperD.T7
