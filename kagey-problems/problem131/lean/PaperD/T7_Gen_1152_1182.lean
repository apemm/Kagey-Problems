import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1152, …, 1182` (generated)

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

/-! ### `N = 1152` -/

def pL1152 : Prm := ⟨76, 35, 38, 1154, 11, 18446744073709551616, 154059703078262993, 154059703078262993⟩
def pH1152 : Prm := ⟨76, 35, 38, 1154, 11, 18446744073709551616, 154061902101518545, 154061902101518545⟩
def pI1152 : Prm := ⟨65, 32, 30, 1154, 11, 18446744073709551616, 154059703078262993, 154061902101518545⟩
theorem L1152_fin : (prmOK pL1152 1152 && ptTest pL1152 (runFrom pL1152 (fmask pL1152) (cmask pL1152) (hmask pL1152) 1 1151 (true, (init pL1152), (init pL1152))) 1152 576 false) = true := by
  decide +kernel
theorem L1152_ok : RunOK pL1152 1152 (runFrom pL1152 (fmask pL1152) (cmask pL1152) (hmask pL1152) 1 1151 (true, (init pL1152), (init pL1152))) ∧ ptTest pL1152 (runFrom pL1152 (fmask pL1152) (cmask pL1152) (hmask pL1152) 1 1151 (true, (init pL1152), (init pL1152))) 1152 576 false = true :=
  fin_run (runOK_init (prmOK_of_and L1152_fin) true) (by decide) rfl L1152_fin ptTest_fst
theorem H1152_fin : (prmOK pH1152 1152 && ptTest pH1152 (runFrom pH1152 (fmask pH1152) (cmask pH1152) (hmask pH1152) 1 1151 (true, (init pH1152), (init pH1152))) 1152 576 true) = true := by
  decide +kernel
theorem H1152_ok : RunOK pH1152 1152 (runFrom pH1152 (fmask pH1152) (cmask pH1152) (hmask pH1152) 1 1151 (true, (init pH1152), (init pH1152))) ∧ ptTest pH1152 (runFrom pH1152 (fmask pH1152) (cmask pH1152) (hmask pH1152) 1 1151 (true, (init pH1152), (init pH1152))) 1152 576 true = true :=
  fin_run (runOK_init (prmOK_of_and H1152_fin) true) (by decide) rfl H1152_fin ptTest_fst
theorem I1152_fin : (prmOK pI1152 1152 && intTest pI1152 (runFrom pI1152 (fmask pI1152) (cmask pI1152) (hmask pI1152) 1 1151 (true, (init pI1152), (init pI1152))) 1152 19 true) = true := by
  decide +kernel
theorem I1152_ok : RunOK pI1152 1152 (runFrom pI1152 (fmask pI1152) (cmask pI1152) (hmask pI1152) 1 1151 (true, (init pI1152), (init pI1152))) ∧ intTest pI1152 (runFrom pI1152 (fmask pI1152) (cmask pI1152) (hmask pI1152) 1 1151 (true, (init pI1152), (init pI1152))) 1152 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1152_fin) true) (by decide) rfl I1152_fin intTest_fst
theorem link1152 : linkOK pL1152 pH1152 pI1152 = true := by decide +kernel
theorem cvx1152 : ConvexBetweenHumps 1152 :=
  cvx_of L1152_ok H1152_ok I1152_ok link1152 (by decide)
theorem cenlink1152 : cenLinkOK pI1152 1152 = true := by decide +kernel
theorem cen1152 : CenterUniqueMin 1152 ∧ DipHyp 1152 ∧ OnePointHyps 1152 :=
  cen_of L1152_ok H1152_ok I1152_ok link1152 cenlink1152

/-! ### `N = 1153` -/

def pL1153 : Prm := ⟨76, 35, 38, 1155, 11, 18446744073709551616, 153952228608337452, 153952228608337452⟩
def pH1153 : Prm := ⟨76, 35, 38, 1155, 11, 18446744073709551616, 153954427631593004, 153954427631593004⟩
def pI1153 : Prm := ⟨65, 32, 30, 1155, 11, 18446744073709551616, 153952228608337452, 153954427631593004⟩
theorem L1153_fin : (prmOK pL1153 1153 && ptTest pL1153 (runFrom pL1153 (fmask pL1153) (cmask pL1153) (hmask pL1153) 1 1152 (true, (init pL1153), (init pL1153))) 1153 577 false) = true := by
  decide +kernel
theorem L1153_ok : RunOK pL1153 1153 (runFrom pL1153 (fmask pL1153) (cmask pL1153) (hmask pL1153) 1 1152 (true, (init pL1153), (init pL1153))) ∧ ptTest pL1153 (runFrom pL1153 (fmask pL1153) (cmask pL1153) (hmask pL1153) 1 1152 (true, (init pL1153), (init pL1153))) 1153 577 false = true :=
  fin_run (runOK_init (prmOK_of_and L1153_fin) true) (by decide) rfl L1153_fin ptTest_fst
theorem H1153_fin : (prmOK pH1153 1153 && ptTest pH1153 (runFrom pH1153 (fmask pH1153) (cmask pH1153) (hmask pH1153) 1 1152 (true, (init pH1153), (init pH1153))) 1153 577 true) = true := by
  decide +kernel
theorem H1153_ok : RunOK pH1153 1153 (runFrom pH1153 (fmask pH1153) (cmask pH1153) (hmask pH1153) 1 1152 (true, (init pH1153), (init pH1153))) ∧ ptTest pH1153 (runFrom pH1153 (fmask pH1153) (cmask pH1153) (hmask pH1153) 1 1152 (true, (init pH1153), (init pH1153))) 1153 577 true = true :=
  fin_run (runOK_init (prmOK_of_and H1153_fin) true) (by decide) rfl H1153_fin ptTest_fst
theorem I1153_fin : (prmOK pI1153 1153 && intTest pI1153 (runFrom pI1153 (fmask pI1153) (cmask pI1153) (hmask pI1153) 1 1152 (true, (init pI1153), (init pI1153))) 1153 19 false) = true := by
  decide +kernel
theorem I1153_ok : RunOK pI1153 1153 (runFrom pI1153 (fmask pI1153) (cmask pI1153) (hmask pI1153) 1 1152 (true, (init pI1153), (init pI1153))) ∧ intTest pI1153 (runFrom pI1153 (fmask pI1153) (cmask pI1153) (hmask pI1153) 1 1152 (true, (init pI1153), (init pI1153))) 1153 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1153_fin) true) (by decide) rfl I1153_fin intTest_fst
theorem link1153 : linkOK pL1153 pH1153 pI1153 = true := by decide +kernel
theorem cvx1153 : ConvexBetweenHumps 1153 :=
  cvx_of L1153_ok H1153_ok I1153_ok link1153 (by decide)

/-! ### `N = 1154` -/

def pL1154 : Prm := ⟨76, 35, 38, 1156, 11, 18446744073709551616, 153844992494768831, 153844992494768831⟩
def pH1154 : Prm := ⟨76, 35, 38, 1156, 11, 18446744073709551616, 153847191518024383, 153847191518024383⟩
def pI1154 : Prm := ⟨65, 32, 30, 1156, 11, 18446744073709551616, 153844992494768831, 153847191518024383⟩
theorem L1154_fin : (prmOK pL1154 1154 && ptTest pL1154 (runFrom pL1154 (fmask pL1154) (cmask pL1154) (hmask pL1154) 1 1153 (true, (init pL1154), (init pL1154))) 1154 577 false) = true := by
  decide +kernel
theorem L1154_ok : RunOK pL1154 1154 (runFrom pL1154 (fmask pL1154) (cmask pL1154) (hmask pL1154) 1 1153 (true, (init pL1154), (init pL1154))) ∧ ptTest pL1154 (runFrom pL1154 (fmask pL1154) (cmask pL1154) (hmask pL1154) 1 1153 (true, (init pL1154), (init pL1154))) 1154 577 false = true :=
  fin_run (runOK_init (prmOK_of_and L1154_fin) true) (by decide) rfl L1154_fin ptTest_fst
theorem H1154_fin : (prmOK pH1154 1154 && ptTest pH1154 (runFrom pH1154 (fmask pH1154) (cmask pH1154) (hmask pH1154) 1 1153 (true, (init pH1154), (init pH1154))) 1154 577 true) = true := by
  decide +kernel
theorem H1154_ok : RunOK pH1154 1154 (runFrom pH1154 (fmask pH1154) (cmask pH1154) (hmask pH1154) 1 1153 (true, (init pH1154), (init pH1154))) ∧ ptTest pH1154 (runFrom pH1154 (fmask pH1154) (cmask pH1154) (hmask pH1154) 1 1153 (true, (init pH1154), (init pH1154))) 1154 577 true = true :=
  fin_run (runOK_init (prmOK_of_and H1154_fin) true) (by decide) rfl H1154_fin ptTest_fst
theorem I1154_fin : (prmOK pI1154 1154 && intTest pI1154 (runFrom pI1154 (fmask pI1154) (cmask pI1154) (hmask pI1154) 1 1153 (true, (init pI1154), (init pI1154))) 1154 19 true) = true := by
  decide +kernel
theorem I1154_ok : RunOK pI1154 1154 (runFrom pI1154 (fmask pI1154) (cmask pI1154) (hmask pI1154) 1 1153 (true, (init pI1154), (init pI1154))) ∧ intTest pI1154 (runFrom pI1154 (fmask pI1154) (cmask pI1154) (hmask pI1154) 1 1153 (true, (init pI1154), (init pI1154))) 1154 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1154_fin) true) (by decide) rfl I1154_fin intTest_fst
theorem link1154 : linkOK pL1154 pH1154 pI1154 = true := by decide +kernel
theorem cvx1154 : ConvexBetweenHumps 1154 :=
  cvx_of L1154_ok H1154_ok I1154_ok link1154 (by decide)
theorem cenlink1154 : cenLinkOK pI1154 1154 = true := by decide +kernel
theorem cen1154 : CenterUniqueMin 1154 ∧ DipHyp 1154 ∧ OnePointHyps 1154 :=
  cen_of L1154_ok H1154_ok I1154_ok link1154 cenlink1154

/-! ### `N = 1155` -/

def pL1155 : Prm := ⟨76, 35, 38, 1157, 11, 18446744073709551616, 153737844866892673, 153737844866892673⟩
def pH1155 : Prm := ⟨76, 35, 38, 1157, 11, 18446744073709551616, 153740043890148225, 153740043890148225⟩
def pI1155 : Prm := ⟨65, 32, 30, 1157, 11, 18446744073709551616, 153737844866892673, 153740043890148225⟩
theorem L1155_fin : (prmOK pL1155 1155 && ptTest pL1155 (runFrom pL1155 (fmask pL1155) (cmask pL1155) (hmask pL1155) 1 1154 (true, (init pL1155), (init pL1155))) 1155 578 false) = true := by
  decide +kernel
theorem L1155_ok : RunOK pL1155 1155 (runFrom pL1155 (fmask pL1155) (cmask pL1155) (hmask pL1155) 1 1154 (true, (init pL1155), (init pL1155))) ∧ ptTest pL1155 (runFrom pL1155 (fmask pL1155) (cmask pL1155) (hmask pL1155) 1 1154 (true, (init pL1155), (init pL1155))) 1155 578 false = true :=
  fin_run (runOK_init (prmOK_of_and L1155_fin) true) (by decide) rfl L1155_fin ptTest_fst
theorem H1155_fin : (prmOK pH1155 1155 && ptTest pH1155 (runFrom pH1155 (fmask pH1155) (cmask pH1155) (hmask pH1155) 1 1154 (true, (init pH1155), (init pH1155))) 1155 578 true) = true := by
  decide +kernel
theorem H1155_ok : RunOK pH1155 1155 (runFrom pH1155 (fmask pH1155) (cmask pH1155) (hmask pH1155) 1 1154 (true, (init pH1155), (init pH1155))) ∧ ptTest pH1155 (runFrom pH1155 (fmask pH1155) (cmask pH1155) (hmask pH1155) 1 1154 (true, (init pH1155), (init pH1155))) 1155 578 true = true :=
  fin_run (runOK_init (prmOK_of_and H1155_fin) true) (by decide) rfl H1155_fin ptTest_fst
theorem I1155_fin : (prmOK pI1155 1155 && intTest pI1155 (runFrom pI1155 (fmask pI1155) (cmask pI1155) (hmask pI1155) 1 1154 (true, (init pI1155), (init pI1155))) 1155 19 false) = true := by
  decide +kernel
theorem I1155_ok : RunOK pI1155 1155 (runFrom pI1155 (fmask pI1155) (cmask pI1155) (hmask pI1155) 1 1154 (true, (init pI1155), (init pI1155))) ∧ intTest pI1155 (runFrom pI1155 (fmask pI1155) (cmask pI1155) (hmask pI1155) 1 1154 (true, (init pI1155), (init pI1155))) 1155 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1155_fin) true) (by decide) rfl I1155_fin intTest_fst
theorem link1155 : linkOK pL1155 pH1155 pI1155 = true := by decide +kernel
theorem cvx1155 : ConvexBetweenHumps 1155 :=
  cvx_of L1155_ok H1155_ok I1155_ok link1155 (by decide)

/-! ### `N = 1156` -/

def pL1156 : Prm := ⟨76, 35, 38, 1158, 11, 18446744073709551616, 153630934430664461, 153630934430664461⟩
def pH1156 : Prm := ⟨76, 35, 38, 1158, 11, 18446744073709551616, 153633133453920013, 153633133453920013⟩
def pI1156 : Prm := ⟨65, 32, 30, 1158, 11, 18446744073709551616, 153630934430664461, 153633133453920013⟩
theorem L1156_fin : (prmOK pL1156 1156 && ptTest pL1156 (runFrom pL1156 (fmask pL1156) (cmask pL1156) (hmask pL1156) 1 1155 (true, (init pL1156), (init pL1156))) 1156 578 false) = true := by
  decide +kernel
theorem L1156_ok : RunOK pL1156 1156 (runFrom pL1156 (fmask pL1156) (cmask pL1156) (hmask pL1156) 1 1155 (true, (init pL1156), (init pL1156))) ∧ ptTest pL1156 (runFrom pL1156 (fmask pL1156) (cmask pL1156) (hmask pL1156) 1 1155 (true, (init pL1156), (init pL1156))) 1156 578 false = true :=
  fin_run (runOK_init (prmOK_of_and L1156_fin) true) (by decide) rfl L1156_fin ptTest_fst
theorem H1156_fin : (prmOK pH1156 1156 && ptTest pH1156 (runFrom pH1156 (fmask pH1156) (cmask pH1156) (hmask pH1156) 1 1155 (true, (init pH1156), (init pH1156))) 1156 578 true) = true := by
  decide +kernel
theorem H1156_ok : RunOK pH1156 1156 (runFrom pH1156 (fmask pH1156) (cmask pH1156) (hmask pH1156) 1 1155 (true, (init pH1156), (init pH1156))) ∧ ptTest pH1156 (runFrom pH1156 (fmask pH1156) (cmask pH1156) (hmask pH1156) 1 1155 (true, (init pH1156), (init pH1156))) 1156 578 true = true :=
  fin_run (runOK_init (prmOK_of_and H1156_fin) true) (by decide) rfl H1156_fin ptTest_fst
theorem I1156_fin : (prmOK pI1156 1156 && intTest pI1156 (runFrom pI1156 (fmask pI1156) (cmask pI1156) (hmask pI1156) 1 1155 (true, (init pI1156), (init pI1156))) 1156 19 true) = true := by
  decide +kernel
theorem I1156_ok : RunOK pI1156 1156 (runFrom pI1156 (fmask pI1156) (cmask pI1156) (hmask pI1156) 1 1155 (true, (init pI1156), (init pI1156))) ∧ intTest pI1156 (runFrom pI1156 (fmask pI1156) (cmask pI1156) (hmask pI1156) 1 1155 (true, (init pI1156), (init pI1156))) 1156 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1156_fin) true) (by decide) rfl I1156_fin intTest_fst
theorem link1156 : linkOK pL1156 pH1156 pI1156 = true := by decide +kernel
theorem cvx1156 : ConvexBetweenHumps 1156 :=
  cvx_of L1156_ok H1156_ok I1156_ok link1156 (by decide)
theorem cenlink1156 : cenLinkOK pI1156 1156 = true := by decide +kernel
theorem cen1156 : CenterUniqueMin 1156 ∧ DipHyp 1156 ∧ OnePointHyps 1156 :=
  cen_of L1156_ok H1156_ok I1156_ok link1156 cenlink1156

/-! ### `N = 1157` -/

def pL1157 : Prm := ⟨76, 35, 38, 1159, 11, 18446744073709551616, 153524112106250101, 153524112106250101⟩
def pH1157 : Prm := ⟨76, 35, 38, 1159, 11, 18446744073709551616, 153526311129505653, 153526311129505653⟩
def pI1157 : Prm := ⟨65, 32, 30, 1159, 11, 18446744073709551616, 153524112106250101, 153526311129505653⟩
theorem L1157_fin : (prmOK pL1157 1157 && ptTest pL1157 (runFrom pL1157 (fmask pL1157) (cmask pL1157) (hmask pL1157) 1 1156 (true, (init pL1157), (init pL1157))) 1157 579 false) = true := by
  decide +kernel
theorem L1157_ok : RunOK pL1157 1157 (runFrom pL1157 (fmask pL1157) (cmask pL1157) (hmask pL1157) 1 1156 (true, (init pL1157), (init pL1157))) ∧ ptTest pL1157 (runFrom pL1157 (fmask pL1157) (cmask pL1157) (hmask pL1157) 1 1156 (true, (init pL1157), (init pL1157))) 1157 579 false = true :=
  fin_run (runOK_init (prmOK_of_and L1157_fin) true) (by decide) rfl L1157_fin ptTest_fst
theorem H1157_fin : (prmOK pH1157 1157 && ptTest pH1157 (runFrom pH1157 (fmask pH1157) (cmask pH1157) (hmask pH1157) 1 1156 (true, (init pH1157), (init pH1157))) 1157 579 true) = true := by
  decide +kernel
theorem H1157_ok : RunOK pH1157 1157 (runFrom pH1157 (fmask pH1157) (cmask pH1157) (hmask pH1157) 1 1156 (true, (init pH1157), (init pH1157))) ∧ ptTest pH1157 (runFrom pH1157 (fmask pH1157) (cmask pH1157) (hmask pH1157) 1 1156 (true, (init pH1157), (init pH1157))) 1157 579 true = true :=
  fin_run (runOK_init (prmOK_of_and H1157_fin) true) (by decide) rfl H1157_fin ptTest_fst
theorem I1157_fin : (prmOK pI1157 1157 && intTest pI1157 (runFrom pI1157 (fmask pI1157) (cmask pI1157) (hmask pI1157) 1 1156 (true, (init pI1157), (init pI1157))) 1157 19 false) = true := by
  decide +kernel
theorem I1157_ok : RunOK pI1157 1157 (runFrom pI1157 (fmask pI1157) (cmask pI1157) (hmask pI1157) 1 1156 (true, (init pI1157), (init pI1157))) ∧ intTest pI1157 (runFrom pI1157 (fmask pI1157) (cmask pI1157) (hmask pI1157) 1 1156 (true, (init pI1157), (init pI1157))) 1157 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1157_fin) true) (by decide) rfl I1157_fin intTest_fst
theorem link1157 : linkOK pL1157 pH1157 pI1157 = true := by decide +kernel
theorem cvx1157 : ConvexBetweenHumps 1157 :=
  cvx_of L1157_ok H1157_ok I1157_ok link1157 (by decide)

/-! ### `N = 1158` -/

def pL1158 : Prm := ⟨76, 35, 38, 1160, 11, 18446744073709551616, 153417525816430114, 153417525816430114⟩
def pH1158 : Prm := ⟨76, 35, 38, 1160, 11, 18446744073709551616, 153419724839685666, 153419724839685666⟩
def pI1158 : Prm := ⟨65, 32, 30, 1160, 11, 18446744073709551616, 153417525816430114, 153419724839685666⟩
theorem L1158_fin : (prmOK pL1158 1158 && ptTest pL1158 (runFrom pL1158 (fmask pL1158) (cmask pL1158) (hmask pL1158) 1 1157 (true, (init pL1158), (init pL1158))) 1158 579 false) = true := by
  decide +kernel
theorem L1158_ok : RunOK pL1158 1158 (runFrom pL1158 (fmask pL1158) (cmask pL1158) (hmask pL1158) 1 1157 (true, (init pL1158), (init pL1158))) ∧ ptTest pL1158 (runFrom pL1158 (fmask pL1158) (cmask pL1158) (hmask pL1158) 1 1157 (true, (init pL1158), (init pL1158))) 1158 579 false = true :=
  fin_run (runOK_init (prmOK_of_and L1158_fin) true) (by decide) rfl L1158_fin ptTest_fst
theorem H1158_fin : (prmOK pH1158 1158 && ptTest pH1158 (runFrom pH1158 (fmask pH1158) (cmask pH1158) (hmask pH1158) 1 1157 (true, (init pH1158), (init pH1158))) 1158 579 true) = true := by
  decide +kernel
theorem H1158_ok : RunOK pH1158 1158 (runFrom pH1158 (fmask pH1158) (cmask pH1158) (hmask pH1158) 1 1157 (true, (init pH1158), (init pH1158))) ∧ ptTest pH1158 (runFrom pH1158 (fmask pH1158) (cmask pH1158) (hmask pH1158) 1 1157 (true, (init pH1158), (init pH1158))) 1158 579 true = true :=
  fin_run (runOK_init (prmOK_of_and H1158_fin) true) (by decide) rfl H1158_fin ptTest_fst
theorem I1158_fin : (prmOK pI1158 1158 && intTest pI1158 (runFrom pI1158 (fmask pI1158) (cmask pI1158) (hmask pI1158) 1 1157 (true, (init pI1158), (init pI1158))) 1158 19 true) = true := by
  decide +kernel
theorem I1158_ok : RunOK pI1158 1158 (runFrom pI1158 (fmask pI1158) (cmask pI1158) (hmask pI1158) 1 1157 (true, (init pI1158), (init pI1158))) ∧ intTest pI1158 (runFrom pI1158 (fmask pI1158) (cmask pI1158) (hmask pI1158) 1 1157 (true, (init pI1158), (init pI1158))) 1158 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1158_fin) true) (by decide) rfl I1158_fin intTest_fst
theorem link1158 : linkOK pL1158 pH1158 pI1158 = true := by decide +kernel
theorem cvx1158 : ConvexBetweenHumps 1158 :=
  cvx_of L1158_ok H1158_ok I1158_ok link1158 (by decide)
theorem cenlink1158 : cenLinkOK pI1158 1158 = true := by decide +kernel
theorem cen1158 : CenterUniqueMin 1158 ∧ DipHyp 1158 ∧ OnePointHyps 1158 :=
  cen_of L1158_ok H1158_ok I1158_ok link1158 cenlink1158

/-! ### `N = 1159` -/

def pL1159 : Prm := ⟨76, 35, 38, 1161, 11, 18446744073709551616, 153311027266703639, 153311027266703639⟩
def pH1159 : Prm := ⟨76, 35, 38, 1161, 11, 18446744073709551616, 153313226289959191, 153313226289959191⟩
def pI1159 : Prm := ⟨65, 32, 30, 1161, 11, 18446744073709551616, 153311027266703639, 153313226289959191⟩
theorem L1159_fin : (prmOK pL1159 1159 && ptTest pL1159 (runFrom pL1159 (fmask pL1159) (cmask pL1159) (hmask pL1159) 1 1158 (true, (init pL1159), (init pL1159))) 1159 580 false) = true := by
  decide +kernel
theorem L1159_ok : RunOK pL1159 1159 (runFrom pL1159 (fmask pL1159) (cmask pL1159) (hmask pL1159) 1 1158 (true, (init pL1159), (init pL1159))) ∧ ptTest pL1159 (runFrom pL1159 (fmask pL1159) (cmask pL1159) (hmask pL1159) 1 1158 (true, (init pL1159), (init pL1159))) 1159 580 false = true :=
  fin_run (runOK_init (prmOK_of_and L1159_fin) true) (by decide) rfl L1159_fin ptTest_fst
theorem H1159_fin : (prmOK pH1159 1159 && ptTest pH1159 (runFrom pH1159 (fmask pH1159) (cmask pH1159) (hmask pH1159) 1 1158 (true, (init pH1159), (init pH1159))) 1159 580 true) = true := by
  decide +kernel
theorem H1159_ok : RunOK pH1159 1159 (runFrom pH1159 (fmask pH1159) (cmask pH1159) (hmask pH1159) 1 1158 (true, (init pH1159), (init pH1159))) ∧ ptTest pH1159 (runFrom pH1159 (fmask pH1159) (cmask pH1159) (hmask pH1159) 1 1158 (true, (init pH1159), (init pH1159))) 1159 580 true = true :=
  fin_run (runOK_init (prmOK_of_and H1159_fin) true) (by decide) rfl H1159_fin ptTest_fst
theorem I1159_fin : (prmOK pI1159 1159 && intTest pI1159 (runFrom pI1159 (fmask pI1159) (cmask pI1159) (hmask pI1159) 1 1158 (true, (init pI1159), (init pI1159))) 1159 19 false) = true := by
  decide +kernel
theorem I1159_ok : RunOK pI1159 1159 (runFrom pI1159 (fmask pI1159) (cmask pI1159) (hmask pI1159) 1 1158 (true, (init pI1159), (init pI1159))) ∧ intTest pI1159 (runFrom pI1159 (fmask pI1159) (cmask pI1159) (hmask pI1159) 1 1158 (true, (init pI1159), (init pI1159))) 1159 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1159_fin) true) (by decide) rfl I1159_fin intTest_fst
theorem link1159 : linkOK pL1159 pH1159 pI1159 = true := by decide +kernel
theorem cvx1159 : ConvexBetweenHumps 1159 :=
  cvx_of L1159_ok H1159_ok I1159_ok link1159 (by decide)

/-! ### `N = 1160` -/

def pL1160 : Prm := ⟨76, 35, 38, 1162, 11, 18446744073709551616, 153204763602136466, 153204763602136466⟩
def pH1160 : Prm := ⟨76, 35, 38, 1162, 11, 18446744073709551616, 153206962625392018, 153206962625392018⟩
def pI1160 : Prm := ⟨65, 32, 30, 1162, 11, 18446744073709551616, 153204763602136466, 153206962625392018⟩
theorem L1160_fin : (prmOK pL1160 1160 && ptTest pL1160 (runFrom pL1160 (fmask pL1160) (cmask pL1160) (hmask pL1160) 1 1159 (true, (init pL1160), (init pL1160))) 1160 580 false) = true := by
  decide +kernel
theorem L1160_ok : RunOK pL1160 1160 (runFrom pL1160 (fmask pL1160) (cmask pL1160) (hmask pL1160) 1 1159 (true, (init pL1160), (init pL1160))) ∧ ptTest pL1160 (runFrom pL1160 (fmask pL1160) (cmask pL1160) (hmask pL1160) 1 1159 (true, (init pL1160), (init pL1160))) 1160 580 false = true :=
  fin_run (runOK_init (prmOK_of_and L1160_fin) true) (by decide) rfl L1160_fin ptTest_fst
theorem H1160_fin : (prmOK pH1160 1160 && ptTest pH1160 (runFrom pH1160 (fmask pH1160) (cmask pH1160) (hmask pH1160) 1 1159 (true, (init pH1160), (init pH1160))) 1160 580 true) = true := by
  decide +kernel
theorem H1160_ok : RunOK pH1160 1160 (runFrom pH1160 (fmask pH1160) (cmask pH1160) (hmask pH1160) 1 1159 (true, (init pH1160), (init pH1160))) ∧ ptTest pH1160 (runFrom pH1160 (fmask pH1160) (cmask pH1160) (hmask pH1160) 1 1159 (true, (init pH1160), (init pH1160))) 1160 580 true = true :=
  fin_run (runOK_init (prmOK_of_and H1160_fin) true) (by decide) rfl H1160_fin ptTest_fst
theorem I1160_fin : (prmOK pI1160 1160 && intTest pI1160 (runFrom pI1160 (fmask pI1160) (cmask pI1160) (hmask pI1160) 1 1159 (true, (init pI1160), (init pI1160))) 1160 19 true) = true := by
  decide +kernel
theorem I1160_ok : RunOK pI1160 1160 (runFrom pI1160 (fmask pI1160) (cmask pI1160) (hmask pI1160) 1 1159 (true, (init pI1160), (init pI1160))) ∧ intTest pI1160 (runFrom pI1160 (fmask pI1160) (cmask pI1160) (hmask pI1160) 1 1159 (true, (init pI1160), (init pI1160))) 1160 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1160_fin) true) (by decide) rfl I1160_fin intTest_fst
theorem link1160 : linkOK pL1160 pH1160 pI1160 = true := by decide +kernel
theorem cvx1160 : ConvexBetweenHumps 1160 :=
  cvx_of L1160_ok H1160_ok I1160_ok link1160 (by decide)
theorem cenlink1160 : cenLinkOK pI1160 1160 = true := by decide +kernel
theorem cen1160 : CenterUniqueMin 1160 ∧ DipHyp 1160 ∧ OnePointHyps 1160 :=
  cen_of L1160_ok H1160_ok I1160_ok link1160 cenlink1160

/-! ### `N = 1161` -/

def pL1161 : Prm := ⟨76, 35, 38, 1163, 11, 18446744073709551616, 153098587308045394, 153098587308045394⟩
def pH1161 : Prm := ⟨76, 35, 38, 1163, 11, 18446744073709551616, 153100786331300946, 153100786331300946⟩
def pI1161 : Prm := ⟨65, 32, 30, 1163, 11, 18446744073709551616, 153098587308045394, 153100786331300946⟩
theorem L1161_fin : (prmOK pL1161 1161 && ptTest pL1161 (runFrom pL1161 (fmask pL1161) (cmask pL1161) (hmask pL1161) 1 1160 (true, (init pL1161), (init pL1161))) 1161 581 false) = true := by
  decide +kernel
theorem L1161_ok : RunOK pL1161 1161 (runFrom pL1161 (fmask pL1161) (cmask pL1161) (hmask pL1161) 1 1160 (true, (init pL1161), (init pL1161))) ∧ ptTest pL1161 (runFrom pL1161 (fmask pL1161) (cmask pL1161) (hmask pL1161) 1 1160 (true, (init pL1161), (init pL1161))) 1161 581 false = true :=
  fin_run (runOK_init (prmOK_of_and L1161_fin) true) (by decide) rfl L1161_fin ptTest_fst
theorem H1161_fin : (prmOK pH1161 1161 && ptTest pH1161 (runFrom pH1161 (fmask pH1161) (cmask pH1161) (hmask pH1161) 1 1160 (true, (init pH1161), (init pH1161))) 1161 581 true) = true := by
  decide +kernel
theorem H1161_ok : RunOK pH1161 1161 (runFrom pH1161 (fmask pH1161) (cmask pH1161) (hmask pH1161) 1 1160 (true, (init pH1161), (init pH1161))) ∧ ptTest pH1161 (runFrom pH1161 (fmask pH1161) (cmask pH1161) (hmask pH1161) 1 1160 (true, (init pH1161), (init pH1161))) 1161 581 true = true :=
  fin_run (runOK_init (prmOK_of_and H1161_fin) true) (by decide) rfl H1161_fin ptTest_fst
theorem I1161_fin : (prmOK pI1161 1161 && intTest pI1161 (runFrom pI1161 (fmask pI1161) (cmask pI1161) (hmask pI1161) 1 1160 (true, (init pI1161), (init pI1161))) 1161 19 false) = true := by
  decide +kernel
theorem I1161_ok : RunOK pI1161 1161 (runFrom pI1161 (fmask pI1161) (cmask pI1161) (hmask pI1161) 1 1160 (true, (init pI1161), (init pI1161))) ∧ intTest pI1161 (runFrom pI1161 (fmask pI1161) (cmask pI1161) (hmask pI1161) 1 1160 (true, (init pI1161), (init pI1161))) 1161 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1161_fin) true) (by decide) rfl I1161_fin intTest_fst
theorem link1161 : linkOK pL1161 pH1161 pI1161 = true := by decide +kernel
theorem cvx1161 : ConvexBetweenHumps 1161 :=
  cvx_of L1161_ok H1161_ok I1161_ok link1161 (by decide)

/-! ### `N = 1162` -/

def pL1162 : Prm := ⟨76, 35, 38, 1164, 11, 18446744073709551616, 152992644757223272, 152992644757223272⟩
def pH1162 : Prm := ⟨76, 35, 38, 1164, 11, 18446744073709551616, 152994843780478824, 152994843780478824⟩
def pI1162 : Prm := ⟨65, 32, 30, 1164, 11, 18446744073709551616, 152992644757223272, 152994843780478824⟩
theorem L1162_fin : (prmOK pL1162 1162 && ptTest pL1162 (runFrom pL1162 (fmask pL1162) (cmask pL1162) (hmask pL1162) 1 1161 (true, (init pL1162), (init pL1162))) 1162 581 false) = true := by
  decide +kernel
theorem L1162_ok : RunOK pL1162 1162 (runFrom pL1162 (fmask pL1162) (cmask pL1162) (hmask pL1162) 1 1161 (true, (init pL1162), (init pL1162))) ∧ ptTest pL1162 (runFrom pL1162 (fmask pL1162) (cmask pL1162) (hmask pL1162) 1 1161 (true, (init pL1162), (init pL1162))) 1162 581 false = true :=
  fin_run (runOK_init (prmOK_of_and L1162_fin) true) (by decide) rfl L1162_fin ptTest_fst
theorem H1162_fin : (prmOK pH1162 1162 && ptTest pH1162 (runFrom pH1162 (fmask pH1162) (cmask pH1162) (hmask pH1162) 1 1161 (true, (init pH1162), (init pH1162))) 1162 581 true) = true := by
  decide +kernel
theorem H1162_ok : RunOK pH1162 1162 (runFrom pH1162 (fmask pH1162) (cmask pH1162) (hmask pH1162) 1 1161 (true, (init pH1162), (init pH1162))) ∧ ptTest pH1162 (runFrom pH1162 (fmask pH1162) (cmask pH1162) (hmask pH1162) 1 1161 (true, (init pH1162), (init pH1162))) 1162 581 true = true :=
  fin_run (runOK_init (prmOK_of_and H1162_fin) true) (by decide) rfl H1162_fin ptTest_fst
theorem I1162_fin : (prmOK pI1162 1162 && intTest pI1162 (runFrom pI1162 (fmask pI1162) (cmask pI1162) (hmask pI1162) 1 1161 (true, (init pI1162), (init pI1162))) 1162 19 true) = true := by
  decide +kernel
theorem I1162_ok : RunOK pI1162 1162 (runFrom pI1162 (fmask pI1162) (cmask pI1162) (hmask pI1162) 1 1161 (true, (init pI1162), (init pI1162))) ∧ intTest pI1162 (runFrom pI1162 (fmask pI1162) (cmask pI1162) (hmask pI1162) 1 1161 (true, (init pI1162), (init pI1162))) 1162 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1162_fin) true) (by decide) rfl I1162_fin intTest_fst
theorem link1162 : linkOK pL1162 pH1162 pI1162 = true := by decide +kernel
theorem cvx1162 : ConvexBetweenHumps 1162 :=
  cvx_of L1162_ok H1162_ok I1162_ok link1162 (by decide)
theorem cenlink1162 : cenLinkOK pI1162 1162 = true := by decide +kernel
theorem cen1162 : CenterUniqueMin 1162 ∧ DipHyp 1162 ∧ OnePointHyps 1162 :=
  cen_of L1162_ok H1162_ok I1162_ok link1162 cenlink1162

/-! ### `N = 1163` -/

def pL1163 : Prm := ⟨76, 35, 38, 1165, 11, 18446744073709551616, 152886789209381217, 152886789209381217⟩
def pH1163 : Prm := ⟨76, 35, 38, 1165, 11, 18446744073709551616, 152888988232636769, 152888988232636769⟩
def pI1163 : Prm := ⟨65, 32, 30, 1165, 11, 18446744073709551616, 152886789209381217, 152888988232636769⟩
theorem L1163_fin : (prmOK pL1163 1163 && ptTest pL1163 (runFrom pL1163 (fmask pL1163) (cmask pL1163) (hmask pL1163) 1 1162 (true, (init pL1163), (init pL1163))) 1163 582 false) = true := by
  decide +kernel
theorem L1163_ok : RunOK pL1163 1163 (runFrom pL1163 (fmask pL1163) (cmask pL1163) (hmask pL1163) 1 1162 (true, (init pL1163), (init pL1163))) ∧ ptTest pL1163 (runFrom pL1163 (fmask pL1163) (cmask pL1163) (hmask pL1163) 1 1162 (true, (init pL1163), (init pL1163))) 1163 582 false = true :=
  fin_run (runOK_init (prmOK_of_and L1163_fin) true) (by decide) rfl L1163_fin ptTest_fst
theorem H1163_fin : (prmOK pH1163 1163 && ptTest pH1163 (runFrom pH1163 (fmask pH1163) (cmask pH1163) (hmask pH1163) 1 1162 (true, (init pH1163), (init pH1163))) 1163 582 true) = true := by
  decide +kernel
theorem H1163_ok : RunOK pH1163 1163 (runFrom pH1163 (fmask pH1163) (cmask pH1163) (hmask pH1163) 1 1162 (true, (init pH1163), (init pH1163))) ∧ ptTest pH1163 (runFrom pH1163 (fmask pH1163) (cmask pH1163) (hmask pH1163) 1 1162 (true, (init pH1163), (init pH1163))) 1163 582 true = true :=
  fin_run (runOK_init (prmOK_of_and H1163_fin) true) (by decide) rfl H1163_fin ptTest_fst
theorem I1163_fin : (prmOK pI1163 1163 && intTest pI1163 (runFrom pI1163 (fmask pI1163) (cmask pI1163) (hmask pI1163) 1 1162 (true, (init pI1163), (init pI1163))) 1163 19 false) = true := by
  decide +kernel
theorem I1163_ok : RunOK pI1163 1163 (runFrom pI1163 (fmask pI1163) (cmask pI1163) (hmask pI1163) 1 1162 (true, (init pI1163), (init pI1163))) ∧ intTest pI1163 (runFrom pI1163 (fmask pI1163) (cmask pI1163) (hmask pI1163) 1 1162 (true, (init pI1163), (init pI1163))) 1163 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1163_fin) true) (by decide) rfl I1163_fin intTest_fst
theorem link1163 : linkOK pL1163 pH1163 pI1163 = true := by decide +kernel
theorem cvx1163 : ConvexBetweenHumps 1163 :=
  cvx_of L1163_ok H1163_ok I1163_ok link1163 (by decide)

/-! ### `N = 1164` -/

def pL1164 : Prm := ⟨76, 35, 38, 1166, 11, 18446744073709551616, 152781166270407138, 152781166270407138⟩
def pH1164 : Prm := ⟨76, 35, 38, 1166, 11, 18446744073709551616, 152783365293662690, 152783365293662690⟩
def pI1164 : Prm := ⟨65, 32, 30, 1166, 11, 18446744073709551616, 152781166270407138, 152783365293662690⟩
theorem L1164_fin : (prmOK pL1164 1164 && ptTest pL1164 (runFrom pL1164 (fmask pL1164) (cmask pL1164) (hmask pL1164) 1 1163 (true, (init pL1164), (init pL1164))) 1164 582 false) = true := by
  decide +kernel
theorem L1164_ok : RunOK pL1164 1164 (runFrom pL1164 (fmask pL1164) (cmask pL1164) (hmask pL1164) 1 1163 (true, (init pL1164), (init pL1164))) ∧ ptTest pL1164 (runFrom pL1164 (fmask pL1164) (cmask pL1164) (hmask pL1164) 1 1163 (true, (init pL1164), (init pL1164))) 1164 582 false = true :=
  fin_run (runOK_init (prmOK_of_and L1164_fin) true) (by decide) rfl L1164_fin ptTest_fst
theorem H1164_fin : (prmOK pH1164 1164 && ptTest pH1164 (runFrom pH1164 (fmask pH1164) (cmask pH1164) (hmask pH1164) 1 1163 (true, (init pH1164), (init pH1164))) 1164 582 true) = true := by
  decide +kernel
theorem H1164_ok : RunOK pH1164 1164 (runFrom pH1164 (fmask pH1164) (cmask pH1164) (hmask pH1164) 1 1163 (true, (init pH1164), (init pH1164))) ∧ ptTest pH1164 (runFrom pH1164 (fmask pH1164) (cmask pH1164) (hmask pH1164) 1 1163 (true, (init pH1164), (init pH1164))) 1164 582 true = true :=
  fin_run (runOK_init (prmOK_of_and H1164_fin) true) (by decide) rfl H1164_fin ptTest_fst
theorem I1164_fin : (prmOK pI1164 1164 && intTest pI1164 (runFrom pI1164 (fmask pI1164) (cmask pI1164) (hmask pI1164) 1 1163 (true, (init pI1164), (init pI1164))) 1164 19 true) = true := by
  decide +kernel
theorem I1164_ok : RunOK pI1164 1164 (runFrom pI1164 (fmask pI1164) (cmask pI1164) (hmask pI1164) 1 1163 (true, (init pI1164), (init pI1164))) ∧ intTest pI1164 (runFrom pI1164 (fmask pI1164) (cmask pI1164) (hmask pI1164) 1 1163 (true, (init pI1164), (init pI1164))) 1164 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1164_fin) true) (by decide) rfl I1164_fin intTest_fst
theorem link1164 : linkOK pL1164 pH1164 pI1164 = true := by decide +kernel
theorem cvx1164 : ConvexBetweenHumps 1164 :=
  cvx_of L1164_ok H1164_ok I1164_ok link1164 (by decide)
theorem cenlink1164 : cenLinkOK pI1164 1164 = true := by decide +kernel
theorem cen1164 : CenterUniqueMin 1164 ∧ DipHyp 1164 ∧ OnePointHyps 1164 :=
  cen_of L1164_ok H1164_ok I1164_ok link1164 cenlink1164

/-! ### `N = 1165` -/

def pL1165 : Prm := ⟨76, 35, 38, 1167, 11, 18446744073709551616, 152675629969020018, 152675629969020018⟩
def pH1165 : Prm := ⟨76, 35, 38, 1167, 11, 18446744073709551616, 152677828992275570, 152677828992275570⟩
def pI1165 : Prm := ⟨65, 32, 30, 1167, 11, 18446744073709551616, 152675629969020018, 152677828992275570⟩
theorem L1165_fin : (prmOK pL1165 1165 && ptTest pL1165 (runFrom pL1165 (fmask pL1165) (cmask pL1165) (hmask pL1165) 1 1164 (true, (init pL1165), (init pL1165))) 1165 583 false) = true := by
  decide +kernel
theorem L1165_ok : RunOK pL1165 1165 (runFrom pL1165 (fmask pL1165) (cmask pL1165) (hmask pL1165) 1 1164 (true, (init pL1165), (init pL1165))) ∧ ptTest pL1165 (runFrom pL1165 (fmask pL1165) (cmask pL1165) (hmask pL1165) 1 1164 (true, (init pL1165), (init pL1165))) 1165 583 false = true :=
  fin_run (runOK_init (prmOK_of_and L1165_fin) true) (by decide) rfl L1165_fin ptTest_fst
theorem H1165_fin : (prmOK pH1165 1165 && ptTest pH1165 (runFrom pH1165 (fmask pH1165) (cmask pH1165) (hmask pH1165) 1 1164 (true, (init pH1165), (init pH1165))) 1165 583 true) = true := by
  decide +kernel
theorem H1165_ok : RunOK pH1165 1165 (runFrom pH1165 (fmask pH1165) (cmask pH1165) (hmask pH1165) 1 1164 (true, (init pH1165), (init pH1165))) ∧ ptTest pH1165 (runFrom pH1165 (fmask pH1165) (cmask pH1165) (hmask pH1165) 1 1164 (true, (init pH1165), (init pH1165))) 1165 583 true = true :=
  fin_run (runOK_init (prmOK_of_and H1165_fin) true) (by decide) rfl H1165_fin ptTest_fst
theorem I1165_fin : (prmOK pI1165 1165 && intTest pI1165 (runFrom pI1165 (fmask pI1165) (cmask pI1165) (hmask pI1165) 1 1164 (true, (init pI1165), (init pI1165))) 1165 19 false) = true := by
  decide +kernel
theorem I1165_ok : RunOK pI1165 1165 (runFrom pI1165 (fmask pI1165) (cmask pI1165) (hmask pI1165) 1 1164 (true, (init pI1165), (init pI1165))) ∧ intTest pI1165 (runFrom pI1165 (fmask pI1165) (cmask pI1165) (hmask pI1165) 1 1164 (true, (init pI1165), (init pI1165))) 1165 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1165_fin) true) (by decide) rfl I1165_fin intTest_fst
theorem link1165 : linkOK pL1165 pH1165 pI1165 = true := by decide +kernel
theorem cvx1165 : ConvexBetweenHumps 1165 :=
  cvx_of L1165_ok H1165_ok I1165_ok link1165 (by decide)

/-! ### `N = 1166` -/

def pL1166 : Prm := ⟨76, 35, 38, 1168, 11, 18446744073709551616, 152570325149515493, 152570325149515493⟩
def pH1166 : Prm := ⟨76, 35, 38, 1168, 11, 18446744073709551616, 152572524172771045, 152572524172771045⟩
def pI1166 : Prm := ⟨65, 32, 30, 1168, 11, 18446744073709551616, 152570325149515493, 152572524172771045⟩
theorem L1166_fin : (prmOK pL1166 1166 && ptTest pL1166 (runFrom pL1166 (fmask pL1166) (cmask pL1166) (hmask pL1166) 1 1165 (true, (init pL1166), (init pL1166))) 1166 583 false) = true := by
  decide +kernel
theorem L1166_ok : RunOK pL1166 1166 (runFrom pL1166 (fmask pL1166) (cmask pL1166) (hmask pL1166) 1 1165 (true, (init pL1166), (init pL1166))) ∧ ptTest pL1166 (runFrom pL1166 (fmask pL1166) (cmask pL1166) (hmask pL1166) 1 1165 (true, (init pL1166), (init pL1166))) 1166 583 false = true :=
  fin_run (runOK_init (prmOK_of_and L1166_fin) true) (by decide) rfl L1166_fin ptTest_fst
theorem H1166_fin : (prmOK pH1166 1166 && ptTest pH1166 (runFrom pH1166 (fmask pH1166) (cmask pH1166) (hmask pH1166) 1 1165 (true, (init pH1166), (init pH1166))) 1166 583 true) = true := by
  decide +kernel
theorem H1166_ok : RunOK pH1166 1166 (runFrom pH1166 (fmask pH1166) (cmask pH1166) (hmask pH1166) 1 1165 (true, (init pH1166), (init pH1166))) ∧ ptTest pH1166 (runFrom pH1166 (fmask pH1166) (cmask pH1166) (hmask pH1166) 1 1165 (true, (init pH1166), (init pH1166))) 1166 583 true = true :=
  fin_run (runOK_init (prmOK_of_and H1166_fin) true) (by decide) rfl H1166_fin ptTest_fst
theorem I1166_fin : (prmOK pI1166 1166 && intTest pI1166 (runFrom pI1166 (fmask pI1166) (cmask pI1166) (hmask pI1166) 1 1165 (true, (init pI1166), (init pI1166))) 1166 19 true) = true := by
  decide +kernel
theorem I1166_ok : RunOK pI1166 1166 (runFrom pI1166 (fmask pI1166) (cmask pI1166) (hmask pI1166) 1 1165 (true, (init pI1166), (init pI1166))) ∧ intTest pI1166 (runFrom pI1166 (fmask pI1166) (cmask pI1166) (hmask pI1166) 1 1165 (true, (init pI1166), (init pI1166))) 1166 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1166_fin) true) (by decide) rfl I1166_fin intTest_fst
theorem link1166 : linkOK pL1166 pH1166 pI1166 = true := by decide +kernel
theorem cvx1166 : ConvexBetweenHumps 1166 :=
  cvx_of L1166_ok H1166_ok I1166_ok link1166 (by decide)
theorem cenlink1166 : cenLinkOK pI1166 1166 = true := by decide +kernel
theorem cen1166 : CenterUniqueMin 1166 ∧ DipHyp 1166 ∧ OnePointHyps 1166 :=
  cen_of L1166_ok H1166_ok I1166_ok link1166 cenlink1166

/-! ### `N = 1167` -/

def pL1167 : Prm := ⟨76, 35, 38, 1169, 11, 18446744073709551616, 152465106604270856, 152465106604270856⟩
def pH1167 : Prm := ⟨76, 35, 38, 1169, 11, 18446744073709551616, 152467305627526408, 152467305627526408⟩
def pI1167 : Prm := ⟨65, 32, 30, 1169, 11, 18446744073709551616, 152465106604270856, 152467305627526408⟩
theorem L1167_fin : (prmOK pL1167 1167 && ptTest pL1167 (runFrom pL1167 (fmask pL1167) (cmask pL1167) (hmask pL1167) 1 1166 (true, (init pL1167), (init pL1167))) 1167 584 false) = true := by
  decide +kernel
theorem L1167_ok : RunOK pL1167 1167 (runFrom pL1167 (fmask pL1167) (cmask pL1167) (hmask pL1167) 1 1166 (true, (init pL1167), (init pL1167))) ∧ ptTest pL1167 (runFrom pL1167 (fmask pL1167) (cmask pL1167) (hmask pL1167) 1 1166 (true, (init pL1167), (init pL1167))) 1167 584 false = true :=
  fin_run (runOK_init (prmOK_of_and L1167_fin) true) (by decide) rfl L1167_fin ptTest_fst
theorem H1167_fin : (prmOK pH1167 1167 && ptTest pH1167 (runFrom pH1167 (fmask pH1167) (cmask pH1167) (hmask pH1167) 1 1166 (true, (init pH1167), (init pH1167))) 1167 584 true) = true := by
  decide +kernel
theorem H1167_ok : RunOK pH1167 1167 (runFrom pH1167 (fmask pH1167) (cmask pH1167) (hmask pH1167) 1 1166 (true, (init pH1167), (init pH1167))) ∧ ptTest pH1167 (runFrom pH1167 (fmask pH1167) (cmask pH1167) (hmask pH1167) 1 1166 (true, (init pH1167), (init pH1167))) 1167 584 true = true :=
  fin_run (runOK_init (prmOK_of_and H1167_fin) true) (by decide) rfl H1167_fin ptTest_fst
theorem I1167_fin : (prmOK pI1167 1167 && intTest pI1167 (runFrom pI1167 (fmask pI1167) (cmask pI1167) (hmask pI1167) 1 1166 (true, (init pI1167), (init pI1167))) 1167 19 false) = true := by
  decide +kernel
theorem I1167_ok : RunOK pI1167 1167 (runFrom pI1167 (fmask pI1167) (cmask pI1167) (hmask pI1167) 1 1166 (true, (init pI1167), (init pI1167))) ∧ intTest pI1167 (runFrom pI1167 (fmask pI1167) (cmask pI1167) (hmask pI1167) 1 1166 (true, (init pI1167), (init pI1167))) 1167 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1167_fin) true) (by decide) rfl I1167_fin intTest_fst
theorem link1167 : linkOK pL1167 pH1167 pI1167 = true := by decide +kernel
theorem cvx1167 : ConvexBetweenHumps 1167 :=
  cvx_of L1167_ok H1167_ok I1167_ok link1167 (by decide)

/-! ### `N = 1168` -/

def pL1168 : Prm := ⟨76, 35, 38, 1170, 11, 18446744073709551616, 152360118421302128, 152360118421302128⟩
def pH1168 : Prm := ⟨76, 35, 38, 1170, 11, 18446744073709551616, 152362317444557680, 152362317444557680⟩
def pI1168 : Prm := ⟨65, 32, 30, 1170, 11, 18446744073709551616, 152360118421302128, 152362317444557680⟩
theorem L1168_fin : (prmOK pL1168 1168 && ptTest pL1168 (runFrom pL1168 (fmask pL1168) (cmask pL1168) (hmask pL1168) 1 1167 (true, (init pL1168), (init pL1168))) 1168 584 false) = true := by
  decide +kernel
theorem L1168_ok : RunOK pL1168 1168 (runFrom pL1168 (fmask pL1168) (cmask pL1168) (hmask pL1168) 1 1167 (true, (init pL1168), (init pL1168))) ∧ ptTest pL1168 (runFrom pL1168 (fmask pL1168) (cmask pL1168) (hmask pL1168) 1 1167 (true, (init pL1168), (init pL1168))) 1168 584 false = true :=
  fin_run (runOK_init (prmOK_of_and L1168_fin) true) (by decide) rfl L1168_fin ptTest_fst
theorem H1168_fin : (prmOK pH1168 1168 && ptTest pH1168 (runFrom pH1168 (fmask pH1168) (cmask pH1168) (hmask pH1168) 1 1167 (true, (init pH1168), (init pH1168))) 1168 584 true) = true := by
  decide +kernel
theorem H1168_ok : RunOK pH1168 1168 (runFrom pH1168 (fmask pH1168) (cmask pH1168) (hmask pH1168) 1 1167 (true, (init pH1168), (init pH1168))) ∧ ptTest pH1168 (runFrom pH1168 (fmask pH1168) (cmask pH1168) (hmask pH1168) 1 1167 (true, (init pH1168), (init pH1168))) 1168 584 true = true :=
  fin_run (runOK_init (prmOK_of_and H1168_fin) true) (by decide) rfl H1168_fin ptTest_fst
theorem I1168_fin : (prmOK pI1168 1168 && intTest pI1168 (runFrom pI1168 (fmask pI1168) (cmask pI1168) (hmask pI1168) 1 1167 (true, (init pI1168), (init pI1168))) 1168 19 true) = true := by
  decide +kernel
theorem I1168_ok : RunOK pI1168 1168 (runFrom pI1168 (fmask pI1168) (cmask pI1168) (hmask pI1168) 1 1167 (true, (init pI1168), (init pI1168))) ∧ intTest pI1168 (runFrom pI1168 (fmask pI1168) (cmask pI1168) (hmask pI1168) 1 1167 (true, (init pI1168), (init pI1168))) 1168 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1168_fin) true) (by decide) rfl I1168_fin intTest_fst
theorem link1168 : linkOK pL1168 pH1168 pI1168 = true := by decide +kernel
theorem cvx1168 : ConvexBetweenHumps 1168 :=
  cvx_of L1168_ok H1168_ok I1168_ok link1168 (by decide)
theorem cenlink1168 : cenLinkOK pI1168 1168 = true := by decide +kernel
theorem cen1168 : CenterUniqueMin 1168 ∧ DipHyp 1168 ∧ OnePointHyps 1168 :=
  cen_of L1168_ok H1168_ok I1168_ok link1168 cenlink1168

/-! ### `N = 1169` -/

def pL1169 : Prm := ⟨76, 35, 38, 1171, 11, 18446744073709551616, 152255216151313806, 152255216151313806⟩
def pH1169 : Prm := ⟨76, 35, 38, 1171, 11, 18446744073709551616, 152257415174569358, 152257415174569358⟩
def pI1169 : Prm := ⟨65, 32, 30, 1171, 11, 18446744073709551616, 152255216151313806, 152257415174569358⟩
theorem L1169_fin : (prmOK pL1169 1169 && ptTest pL1169 (runFrom pL1169 (fmask pL1169) (cmask pL1169) (hmask pL1169) 1 1168 (true, (init pL1169), (init pL1169))) 1169 585 false) = true := by
  decide +kernel
theorem L1169_ok : RunOK pL1169 1169 (runFrom pL1169 (fmask pL1169) (cmask pL1169) (hmask pL1169) 1 1168 (true, (init pL1169), (init pL1169))) ∧ ptTest pL1169 (runFrom pL1169 (fmask pL1169) (cmask pL1169) (hmask pL1169) 1 1168 (true, (init pL1169), (init pL1169))) 1169 585 false = true :=
  fin_run (runOK_init (prmOK_of_and L1169_fin) true) (by decide) rfl L1169_fin ptTest_fst
theorem H1169_fin : (prmOK pH1169 1169 && ptTest pH1169 (runFrom pH1169 (fmask pH1169) (cmask pH1169) (hmask pH1169) 1 1168 (true, (init pH1169), (init pH1169))) 1169 585 true) = true := by
  decide +kernel
theorem H1169_ok : RunOK pH1169 1169 (runFrom pH1169 (fmask pH1169) (cmask pH1169) (hmask pH1169) 1 1168 (true, (init pH1169), (init pH1169))) ∧ ptTest pH1169 (runFrom pH1169 (fmask pH1169) (cmask pH1169) (hmask pH1169) 1 1168 (true, (init pH1169), (init pH1169))) 1169 585 true = true :=
  fin_run (runOK_init (prmOK_of_and H1169_fin) true) (by decide) rfl H1169_fin ptTest_fst
theorem I1169_fin : (prmOK pI1169 1169 && intTest pI1169 (runFrom pI1169 (fmask pI1169) (cmask pI1169) (hmask pI1169) 1 1168 (true, (init pI1169), (init pI1169))) 1169 19 false) = true := by
  decide +kernel
theorem I1169_ok : RunOK pI1169 1169 (runFrom pI1169 (fmask pI1169) (cmask pI1169) (hmask pI1169) 1 1168 (true, (init pI1169), (init pI1169))) ∧ intTest pI1169 (runFrom pI1169 (fmask pI1169) (cmask pI1169) (hmask pI1169) 1 1168 (true, (init pI1169), (init pI1169))) 1169 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1169_fin) true) (by decide) rfl I1169_fin intTest_fst
theorem link1169 : linkOK pL1169 pH1169 pI1169 = true := by decide +kernel
theorem cvx1169 : ConvexBetweenHumps 1169 :=
  cvx_of L1169_ok H1169_ok I1169_ok link1169 (by decide)

/-! ### `N = 1170` -/

def pL1170 : Prm := ⟨76, 35, 38, 1172, 11, 18446744073709551616, 152150543131318066, 152150543131318066⟩
def pH1170 : Prm := ⟨76, 35, 38, 1172, 11, 18446744073709551616, 152152742154573618, 152152742154573618⟩
def pI1170 : Prm := ⟨65, 32, 30, 1172, 11, 18446744073709551616, 152150543131318066, 152152742154573618⟩
theorem L1170_fin : (prmOK pL1170 1170 && ptTest pL1170 (runFrom pL1170 (fmask pL1170) (cmask pL1170) (hmask pL1170) 1 1169 (true, (init pL1170), (init pL1170))) 1170 585 false) = true := by
  decide +kernel
theorem L1170_ok : RunOK pL1170 1170 (runFrom pL1170 (fmask pL1170) (cmask pL1170) (hmask pL1170) 1 1169 (true, (init pL1170), (init pL1170))) ∧ ptTest pL1170 (runFrom pL1170 (fmask pL1170) (cmask pL1170) (hmask pL1170) 1 1169 (true, (init pL1170), (init pL1170))) 1170 585 false = true :=
  fin_run (runOK_init (prmOK_of_and L1170_fin) true) (by decide) rfl L1170_fin ptTest_fst
theorem H1170_fin : (prmOK pH1170 1170 && ptTest pH1170 (runFrom pH1170 (fmask pH1170) (cmask pH1170) (hmask pH1170) 1 1169 (true, (init pH1170), (init pH1170))) 1170 585 true) = true := by
  decide +kernel
theorem H1170_ok : RunOK pH1170 1170 (runFrom pH1170 (fmask pH1170) (cmask pH1170) (hmask pH1170) 1 1169 (true, (init pH1170), (init pH1170))) ∧ ptTest pH1170 (runFrom pH1170 (fmask pH1170) (cmask pH1170) (hmask pH1170) 1 1169 (true, (init pH1170), (init pH1170))) 1170 585 true = true :=
  fin_run (runOK_init (prmOK_of_and H1170_fin) true) (by decide) rfl H1170_fin ptTest_fst
theorem I1170_fin : (prmOK pI1170 1170 && intTest pI1170 (runFrom pI1170 (fmask pI1170) (cmask pI1170) (hmask pI1170) 1 1169 (true, (init pI1170), (init pI1170))) 1170 19 true) = true := by
  decide +kernel
theorem I1170_ok : RunOK pI1170 1170 (runFrom pI1170 (fmask pI1170) (cmask pI1170) (hmask pI1170) 1 1169 (true, (init pI1170), (init pI1170))) ∧ intTest pI1170 (runFrom pI1170 (fmask pI1170) (cmask pI1170) (hmask pI1170) 1 1169 (true, (init pI1170), (init pI1170))) 1170 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1170_fin) true) (by decide) rfl I1170_fin intTest_fst
theorem link1170 : linkOK pL1170 pH1170 pI1170 = true := by decide +kernel
theorem cvx1170 : ConvexBetweenHumps 1170 :=
  cvx_of L1170_ok H1170_ok I1170_ok link1170 (by decide)
theorem cenlink1170 : cenLinkOK pI1170 1170 = true := by decide +kernel
theorem cen1170 : CenterUniqueMin 1170 ∧ DipHyp 1170 ∧ OnePointHyps 1170 :=
  cen_of L1170_ok H1170_ok I1170_ok link1170 cenlink1170

/-! ### `N = 1171` -/

def pL1171 : Prm := ⟨76, 35, 38, 1173, 11, 18446744073709551616, 152045955665089284, 152045955665089284⟩
def pH1171 : Prm := ⟨76, 35, 38, 1173, 11, 18446744073709551616, 152048154688344836, 152048154688344836⟩
def pI1171 : Prm := ⟨66, 32, 31, 1173, 11, 18446744073709551616, 152045955665089284, 152048154688344836⟩
theorem L1171_fin : (prmOK pL1171 1171 && ptTest pL1171 (runFrom pL1171 (fmask pL1171) (cmask pL1171) (hmask pL1171) 1 1170 (true, (init pL1171), (init pL1171))) 1171 586 false) = true := by
  decide +kernel
theorem L1171_ok : RunOK pL1171 1171 (runFrom pL1171 (fmask pL1171) (cmask pL1171) (hmask pL1171) 1 1170 (true, (init pL1171), (init pL1171))) ∧ ptTest pL1171 (runFrom pL1171 (fmask pL1171) (cmask pL1171) (hmask pL1171) 1 1170 (true, (init pL1171), (init pL1171))) 1171 586 false = true :=
  fin_run (runOK_init (prmOK_of_and L1171_fin) true) (by decide) rfl L1171_fin ptTest_fst
theorem H1171_fin : (prmOK pH1171 1171 && ptTest pH1171 (runFrom pH1171 (fmask pH1171) (cmask pH1171) (hmask pH1171) 1 1170 (true, (init pH1171), (init pH1171))) 1171 586 true) = true := by
  decide +kernel
theorem H1171_ok : RunOK pH1171 1171 (runFrom pH1171 (fmask pH1171) (cmask pH1171) (hmask pH1171) 1 1170 (true, (init pH1171), (init pH1171))) ∧ ptTest pH1171 (runFrom pH1171 (fmask pH1171) (cmask pH1171) (hmask pH1171) 1 1170 (true, (init pH1171), (init pH1171))) 1171 586 true = true :=
  fin_run (runOK_init (prmOK_of_and H1171_fin) true) (by decide) rfl H1171_fin ptTest_fst
theorem I1171_fin : (prmOK pI1171 1171 && intTest pI1171 (runFrom pI1171 (fmask pI1171) (cmask pI1171) (hmask pI1171) 1 1170 (true, (init pI1171), (init pI1171))) 1171 19 false) = true := by
  decide +kernel
theorem I1171_ok : RunOK pI1171 1171 (runFrom pI1171 (fmask pI1171) (cmask pI1171) (hmask pI1171) 1 1170 (true, (init pI1171), (init pI1171))) ∧ intTest pI1171 (runFrom pI1171 (fmask pI1171) (cmask pI1171) (hmask pI1171) 1 1170 (true, (init pI1171), (init pI1171))) 1171 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1171_fin) true) (by decide) rfl I1171_fin intTest_fst
theorem link1171 : linkOK pL1171 pH1171 pI1171 = true := by decide +kernel
theorem cvx1171 : ConvexBetweenHumps 1171 :=
  cvx_of L1171_ok H1171_ok I1171_ok link1171 (by decide)

/-! ### `N = 1172` -/

def pL1172 : Prm := ⟨76, 35, 38, 1174, 11, 18446744073709551616, 151941596343782433, 151941596343782433⟩
def pH1172 : Prm := ⟨76, 35, 38, 1174, 11, 18446744073709551616, 151943795367037985, 151943795367037985⟩
def pI1172 : Prm := ⟨66, 32, 31, 1174, 11, 18446744073709551616, 151941596343782433, 151943795367037985⟩
theorem L1172_fin : (prmOK pL1172 1172 && ptTest pL1172 (runFrom pL1172 (fmask pL1172) (cmask pL1172) (hmask pL1172) 1 1171 (true, (init pL1172), (init pL1172))) 1172 586 false) = true := by
  decide +kernel
theorem L1172_ok : RunOK pL1172 1172 (runFrom pL1172 (fmask pL1172) (cmask pL1172) (hmask pL1172) 1 1171 (true, (init pL1172), (init pL1172))) ∧ ptTest pL1172 (runFrom pL1172 (fmask pL1172) (cmask pL1172) (hmask pL1172) 1 1171 (true, (init pL1172), (init pL1172))) 1172 586 false = true :=
  fin_run (runOK_init (prmOK_of_and L1172_fin) true) (by decide) rfl L1172_fin ptTest_fst
theorem H1172_fin : (prmOK pH1172 1172 && ptTest pH1172 (runFrom pH1172 (fmask pH1172) (cmask pH1172) (hmask pH1172) 1 1171 (true, (init pH1172), (init pH1172))) 1172 586 true) = true := by
  decide +kernel
theorem H1172_ok : RunOK pH1172 1172 (runFrom pH1172 (fmask pH1172) (cmask pH1172) (hmask pH1172) 1 1171 (true, (init pH1172), (init pH1172))) ∧ ptTest pH1172 (runFrom pH1172 (fmask pH1172) (cmask pH1172) (hmask pH1172) 1 1171 (true, (init pH1172), (init pH1172))) 1172 586 true = true :=
  fin_run (runOK_init (prmOK_of_and H1172_fin) true) (by decide) rfl H1172_fin ptTest_fst
theorem I1172_fin : (prmOK pI1172 1172 && intTest pI1172 (runFrom pI1172 (fmask pI1172) (cmask pI1172) (hmask pI1172) 1 1171 (true, (init pI1172), (init pI1172))) 1172 19 true) = true := by
  decide +kernel
theorem I1172_ok : RunOK pI1172 1172 (runFrom pI1172 (fmask pI1172) (cmask pI1172) (hmask pI1172) 1 1171 (true, (init pI1172), (init pI1172))) ∧ intTest pI1172 (runFrom pI1172 (fmask pI1172) (cmask pI1172) (hmask pI1172) 1 1171 (true, (init pI1172), (init pI1172))) 1172 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1172_fin) true) (by decide) rfl I1172_fin intTest_fst
theorem link1172 : linkOK pL1172 pH1172 pI1172 = true := by decide +kernel
theorem cvx1172 : ConvexBetweenHumps 1172 :=
  cvx_of L1172_ok H1172_ok I1172_ok link1172 (by decide)
theorem cenlink1172 : cenLinkOK pI1172 1172 = true := by decide +kernel
theorem cen1172 : CenterUniqueMin 1172 ∧ DipHyp 1172 ∧ OnePointHyps 1172 :=
  cen_of L1172_ok H1172_ok I1172_ok link1172 cenlink1172

/-! ### `N = 1173` -/

def pL1173 : Prm := ⟨76, 35, 38, 1175, 11, 18446744073709551616, 151837322219039789, 151837322219039789⟩
def pH1173 : Prm := ⟨76, 35, 38, 1175, 11, 18446744073709551616, 151839521242295341, 151839521242295341⟩
def pI1173 : Prm := ⟨65, 32, 30, 1175, 11, 18446744073709551616, 151837322219039789, 151839521242295341⟩
theorem L1173_fin : (prmOK pL1173 1173 && ptTest pL1173 (runFrom pL1173 (fmask pL1173) (cmask pL1173) (hmask pL1173) 1 1172 (true, (init pL1173), (init pL1173))) 1173 587 false) = true := by
  decide +kernel
theorem L1173_ok : RunOK pL1173 1173 (runFrom pL1173 (fmask pL1173) (cmask pL1173) (hmask pL1173) 1 1172 (true, (init pL1173), (init pL1173))) ∧ ptTest pL1173 (runFrom pL1173 (fmask pL1173) (cmask pL1173) (hmask pL1173) 1 1172 (true, (init pL1173), (init pL1173))) 1173 587 false = true :=
  fin_run (runOK_init (prmOK_of_and L1173_fin) true) (by decide) rfl L1173_fin ptTest_fst
theorem H1173_fin : (prmOK pH1173 1173 && ptTest pH1173 (runFrom pH1173 (fmask pH1173) (cmask pH1173) (hmask pH1173) 1 1172 (true, (init pH1173), (init pH1173))) 1173 587 true) = true := by
  decide +kernel
theorem H1173_ok : RunOK pH1173 1173 (runFrom pH1173 (fmask pH1173) (cmask pH1173) (hmask pH1173) 1 1172 (true, (init pH1173), (init pH1173))) ∧ ptTest pH1173 (runFrom pH1173 (fmask pH1173) (cmask pH1173) (hmask pH1173) 1 1172 (true, (init pH1173), (init pH1173))) 1173 587 true = true :=
  fin_run (runOK_init (prmOK_of_and H1173_fin) true) (by decide) rfl H1173_fin ptTest_fst
theorem I1173_fin : (prmOK pI1173 1173 && intTest pI1173 (runFrom pI1173 (fmask pI1173) (cmask pI1173) (hmask pI1173) 1 1172 (true, (init pI1173), (init pI1173))) 1173 19 false) = true := by
  decide +kernel
theorem I1173_ok : RunOK pI1173 1173 (runFrom pI1173 (fmask pI1173) (cmask pI1173) (hmask pI1173) 1 1172 (true, (init pI1173), (init pI1173))) ∧ intTest pI1173 (runFrom pI1173 (fmask pI1173) (cmask pI1173) (hmask pI1173) 1 1172 (true, (init pI1173), (init pI1173))) 1173 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1173_fin) true) (by decide) rfl I1173_fin intTest_fst
theorem link1173 : linkOK pL1173 pH1173 pI1173 = true := by decide +kernel
theorem cvx1173 : ConvexBetweenHumps 1173 :=
  cvx_of L1173_ok H1173_ok I1173_ok link1173 (by decide)

/-! ### `N = 1174` -/

def pL1174 : Prm := ⟨76, 35, 38, 1176, 11, 18446744073709551616, 151733275141361102, 151733275141361102⟩
def pH1174 : Prm := ⟨76, 35, 38, 1176, 11, 18446744073709551616, 151735474164616654, 151735474164616654⟩
def pI1174 : Prm := ⟨66, 32, 31, 1176, 11, 18446744073709551616, 151733275141361102, 151735474164616654⟩
theorem L1174_fin : (prmOK pL1174 1174 && ptTest pL1174 (runFrom pL1174 (fmask pL1174) (cmask pL1174) (hmask pL1174) 1 1173 (true, (init pL1174), (init pL1174))) 1174 587 false) = true := by
  decide +kernel
theorem L1174_ok : RunOK pL1174 1174 (runFrom pL1174 (fmask pL1174) (cmask pL1174) (hmask pL1174) 1 1173 (true, (init pL1174), (init pL1174))) ∧ ptTest pL1174 (runFrom pL1174 (fmask pL1174) (cmask pL1174) (hmask pL1174) 1 1173 (true, (init pL1174), (init pL1174))) 1174 587 false = true :=
  fin_run (runOK_init (prmOK_of_and L1174_fin) true) (by decide) rfl L1174_fin ptTest_fst
theorem H1174_fin : (prmOK pH1174 1174 && ptTest pH1174 (runFrom pH1174 (fmask pH1174) (cmask pH1174) (hmask pH1174) 1 1173 (true, (init pH1174), (init pH1174))) 1174 587 true) = true := by
  decide +kernel
theorem H1174_ok : RunOK pH1174 1174 (runFrom pH1174 (fmask pH1174) (cmask pH1174) (hmask pH1174) 1 1173 (true, (init pH1174), (init pH1174))) ∧ ptTest pH1174 (runFrom pH1174 (fmask pH1174) (cmask pH1174) (hmask pH1174) 1 1173 (true, (init pH1174), (init pH1174))) 1174 587 true = true :=
  fin_run (runOK_init (prmOK_of_and H1174_fin) true) (by decide) rfl H1174_fin ptTest_fst
theorem I1174_fin : (prmOK pI1174 1174 && intTest pI1174 (runFrom pI1174 (fmask pI1174) (cmask pI1174) (hmask pI1174) 1 1173 (true, (init pI1174), (init pI1174))) 1174 19 true) = true := by
  decide +kernel
theorem I1174_ok : RunOK pI1174 1174 (runFrom pI1174 (fmask pI1174) (cmask pI1174) (hmask pI1174) 1 1173 (true, (init pI1174), (init pI1174))) ∧ intTest pI1174 (runFrom pI1174 (fmask pI1174) (cmask pI1174) (hmask pI1174) 1 1173 (true, (init pI1174), (init pI1174))) 1174 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1174_fin) true) (by decide) rfl I1174_fin intTest_fst
theorem link1174 : linkOK pL1174 pH1174 pI1174 = true := by decide +kernel
theorem cvx1174 : ConvexBetweenHumps 1174 :=
  cvx_of L1174_ok H1174_ok I1174_ok link1174 (by decide)
theorem cenlink1174 : cenLinkOK pI1174 1174 = true := by decide +kernel
theorem cen1174 : CenterUniqueMin 1174 ∧ DipHyp 1174 ∧ OnePointHyps 1174 :=
  cen_of L1174_ok H1174_ok I1174_ok link1174 cenlink1174

/-! ### `N = 1175` -/

def pL1175 : Prm := ⟨76, 35, 38, 1177, 11, 18446744073709551616, 151629312905091457, 151629312905091457⟩
def pH1175 : Prm := ⟨76, 35, 38, 1177, 11, 18446744073709551616, 151631511928347009, 151631511928347009⟩
def pI1175 : Prm := ⟨66, 32, 31, 1177, 11, 18446744073709551616, 151629312905091457, 151631511928347009⟩
theorem L1175_fin : (prmOK pL1175 1175 && ptTest pL1175 (runFrom pL1175 (fmask pL1175) (cmask pL1175) (hmask pL1175) 1 1174 (true, (init pL1175), (init pL1175))) 1175 588 false) = true := by
  decide +kernel
theorem L1175_ok : RunOK pL1175 1175 (runFrom pL1175 (fmask pL1175) (cmask pL1175) (hmask pL1175) 1 1174 (true, (init pL1175), (init pL1175))) ∧ ptTest pL1175 (runFrom pL1175 (fmask pL1175) (cmask pL1175) (hmask pL1175) 1 1174 (true, (init pL1175), (init pL1175))) 1175 588 false = true :=
  fin_run (runOK_init (prmOK_of_and L1175_fin) true) (by decide) rfl L1175_fin ptTest_fst
theorem H1175_fin : (prmOK pH1175 1175 && ptTest pH1175 (runFrom pH1175 (fmask pH1175) (cmask pH1175) (hmask pH1175) 1 1174 (true, (init pH1175), (init pH1175))) 1175 588 true) = true := by
  decide +kernel
theorem H1175_ok : RunOK pH1175 1175 (runFrom pH1175 (fmask pH1175) (cmask pH1175) (hmask pH1175) 1 1174 (true, (init pH1175), (init pH1175))) ∧ ptTest pH1175 (runFrom pH1175 (fmask pH1175) (cmask pH1175) (hmask pH1175) 1 1174 (true, (init pH1175), (init pH1175))) 1175 588 true = true :=
  fin_run (runOK_init (prmOK_of_and H1175_fin) true) (by decide) rfl H1175_fin ptTest_fst
theorem I1175_fin : (prmOK pI1175 1175 && intTest pI1175 (runFrom pI1175 (fmask pI1175) (cmask pI1175) (hmask pI1175) 1 1174 (true, (init pI1175), (init pI1175))) 1175 19 false) = true := by
  decide +kernel
theorem I1175_ok : RunOK pI1175 1175 (runFrom pI1175 (fmask pI1175) (cmask pI1175) (hmask pI1175) 1 1174 (true, (init pI1175), (init pI1175))) ∧ intTest pI1175 (runFrom pI1175 (fmask pI1175) (cmask pI1175) (hmask pI1175) 1 1174 (true, (init pI1175), (init pI1175))) 1175 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1175_fin) true) (by decide) rfl I1175_fin intTest_fst
theorem link1175 : linkOK pL1175 pH1175 pI1175 = true := by decide +kernel
theorem cvx1175 : ConvexBetweenHumps 1175 :=
  cvx_of L1175_ok H1175_ok I1175_ok link1175 (by decide)

/-! ### `N = 1176` -/

def pL1176 : Prm := ⟨76, 35, 38, 1178, 11, 18446744073709551616, 151525576625111347, 151525576625111347⟩
def pH1176 : Prm := ⟨76, 35, 38, 1178, 11, 18446744073709551616, 151527775648366899, 151527775648366899⟩
def pI1176 : Prm := ⟨66, 32, 31, 1178, 11, 18446744073709551616, 151525576625111347, 151527775648366899⟩
theorem L1176_fin : (prmOK pL1176 1176 && ptTest pL1176 (runFrom pL1176 (fmask pL1176) (cmask pL1176) (hmask pL1176) 1 1175 (true, (init pL1176), (init pL1176))) 1176 588 false) = true := by
  decide +kernel
theorem L1176_ok : RunOK pL1176 1176 (runFrom pL1176 (fmask pL1176) (cmask pL1176) (hmask pL1176) 1 1175 (true, (init pL1176), (init pL1176))) ∧ ptTest pL1176 (runFrom pL1176 (fmask pL1176) (cmask pL1176) (hmask pL1176) 1 1175 (true, (init pL1176), (init pL1176))) 1176 588 false = true :=
  fin_run (runOK_init (prmOK_of_and L1176_fin) true) (by decide) rfl L1176_fin ptTest_fst
theorem H1176_fin : (prmOK pH1176 1176 && ptTest pH1176 (runFrom pH1176 (fmask pH1176) (cmask pH1176) (hmask pH1176) 1 1175 (true, (init pH1176), (init pH1176))) 1176 588 true) = true := by
  decide +kernel
theorem H1176_ok : RunOK pH1176 1176 (runFrom pH1176 (fmask pH1176) (cmask pH1176) (hmask pH1176) 1 1175 (true, (init pH1176), (init pH1176))) ∧ ptTest pH1176 (runFrom pH1176 (fmask pH1176) (cmask pH1176) (hmask pH1176) 1 1175 (true, (init pH1176), (init pH1176))) 1176 588 true = true :=
  fin_run (runOK_init (prmOK_of_and H1176_fin) true) (by decide) rfl H1176_fin ptTest_fst
theorem I1176_fin : (prmOK pI1176 1176 && intTest pI1176 (runFrom pI1176 (fmask pI1176) (cmask pI1176) (hmask pI1176) 1 1175 (true, (init pI1176), (init pI1176))) 1176 19 true) = true := by
  decide +kernel
theorem I1176_ok : RunOK pI1176 1176 (runFrom pI1176 (fmask pI1176) (cmask pI1176) (hmask pI1176) 1 1175 (true, (init pI1176), (init pI1176))) ∧ intTest pI1176 (runFrom pI1176 (fmask pI1176) (cmask pI1176) (hmask pI1176) 1 1175 (true, (init pI1176), (init pI1176))) 1176 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1176_fin) true) (by decide) rfl I1176_fin intTest_fst
theorem link1176 : linkOK pL1176 pH1176 pI1176 = true := by decide +kernel
theorem cvx1176 : ConvexBetweenHumps 1176 :=
  cvx_of L1176_ok H1176_ok I1176_ok link1176 (by decide)
theorem cenlink1176 : cenLinkOK pI1176 1176 = true := by decide +kernel
theorem cen1176 : CenterUniqueMin 1176 ∧ DipHyp 1176 ∧ OnePointHyps 1176 :=
  cen_of L1176_ok H1176_ok I1176_ok link1176 cenlink1176

/-! ### `N = 1177` -/

def pL1177 : Prm := ⟨76, 35, 38, 1179, 11, 18446744073709551616, 151421924833395811, 151421924833395811⟩
def pH1177 : Prm := ⟨76, 35, 38, 1179, 11, 18446744073709551616, 151424123856651363, 151424123856651363⟩
def pI1177 : Prm := ⟨66, 32, 31, 1179, 11, 18446744073709551616, 151421924833395811, 151424123856651363⟩
theorem L1177_fin : (prmOK pL1177 1177 && ptTest pL1177 (runFrom pL1177 (fmask pL1177) (cmask pL1177) (hmask pL1177) 1 1176 (true, (init pL1177), (init pL1177))) 1177 589 false) = true := by
  decide +kernel
theorem L1177_ok : RunOK pL1177 1177 (runFrom pL1177 (fmask pL1177) (cmask pL1177) (hmask pL1177) 1 1176 (true, (init pL1177), (init pL1177))) ∧ ptTest pL1177 (runFrom pL1177 (fmask pL1177) (cmask pL1177) (hmask pL1177) 1 1176 (true, (init pL1177), (init pL1177))) 1177 589 false = true :=
  fin_run (runOK_init (prmOK_of_and L1177_fin) true) (by decide) rfl L1177_fin ptTest_fst
theorem H1177_fin : (prmOK pH1177 1177 && ptTest pH1177 (runFrom pH1177 (fmask pH1177) (cmask pH1177) (hmask pH1177) 1 1176 (true, (init pH1177), (init pH1177))) 1177 589 true) = true := by
  decide +kernel
theorem H1177_ok : RunOK pH1177 1177 (runFrom pH1177 (fmask pH1177) (cmask pH1177) (hmask pH1177) 1 1176 (true, (init pH1177), (init pH1177))) ∧ ptTest pH1177 (runFrom pH1177 (fmask pH1177) (cmask pH1177) (hmask pH1177) 1 1176 (true, (init pH1177), (init pH1177))) 1177 589 true = true :=
  fin_run (runOK_init (prmOK_of_and H1177_fin) true) (by decide) rfl H1177_fin ptTest_fst
theorem I1177_fin : (prmOK pI1177 1177 && intTest pI1177 (runFrom pI1177 (fmask pI1177) (cmask pI1177) (hmask pI1177) 1 1176 (true, (init pI1177), (init pI1177))) 1177 19 false) = true := by
  decide +kernel
theorem I1177_ok : RunOK pI1177 1177 (runFrom pI1177 (fmask pI1177) (cmask pI1177) (hmask pI1177) 1 1176 (true, (init pI1177), (init pI1177))) ∧ intTest pI1177 (runFrom pI1177 (fmask pI1177) (cmask pI1177) (hmask pI1177) 1 1176 (true, (init pI1177), (init pI1177))) 1177 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1177_fin) true) (by decide) rfl I1177_fin intTest_fst
theorem link1177 : linkOK pL1177 pH1177 pI1177 = true := by decide +kernel
theorem cvx1177 : ConvexBetweenHumps 1177 :=
  cvx_of L1177_ok H1177_ok I1177_ok link1177 (by decide)

/-! ### `N = 1178` -/

def pL1178 : Prm := ⟨76, 35, 38, 1180, 11, 18446744073709551616, 151318497914278934, 151318497914278934⟩
def pH1178 : Prm := ⟨76, 35, 38, 1180, 11, 18446744073709551616, 151320696937534486, 151320696937534486⟩
def pI1178 : Prm := ⟨66, 32, 31, 1180, 11, 18446744073709551616, 151318497914278934, 151320696937534486⟩
theorem L1178_fin : (prmOK pL1178 1178 && ptTest pL1178 (runFrom pL1178 (fmask pL1178) (cmask pL1178) (hmask pL1178) 1 1177 (true, (init pL1178), (init pL1178))) 1178 589 false) = true := by
  decide +kernel
theorem L1178_ok : RunOK pL1178 1178 (runFrom pL1178 (fmask pL1178) (cmask pL1178) (hmask pL1178) 1 1177 (true, (init pL1178), (init pL1178))) ∧ ptTest pL1178 (runFrom pL1178 (fmask pL1178) (cmask pL1178) (hmask pL1178) 1 1177 (true, (init pL1178), (init pL1178))) 1178 589 false = true :=
  fin_run (runOK_init (prmOK_of_and L1178_fin) true) (by decide) rfl L1178_fin ptTest_fst
theorem H1178_fin : (prmOK pH1178 1178 && ptTest pH1178 (runFrom pH1178 (fmask pH1178) (cmask pH1178) (hmask pH1178) 1 1177 (true, (init pH1178), (init pH1178))) 1178 589 true) = true := by
  decide +kernel
theorem H1178_ok : RunOK pH1178 1178 (runFrom pH1178 (fmask pH1178) (cmask pH1178) (hmask pH1178) 1 1177 (true, (init pH1178), (init pH1178))) ∧ ptTest pH1178 (runFrom pH1178 (fmask pH1178) (cmask pH1178) (hmask pH1178) 1 1177 (true, (init pH1178), (init pH1178))) 1178 589 true = true :=
  fin_run (runOK_init (prmOK_of_and H1178_fin) true) (by decide) rfl H1178_fin ptTest_fst
theorem I1178_fin : (prmOK pI1178 1178 && intTest pI1178 (runFrom pI1178 (fmask pI1178) (cmask pI1178) (hmask pI1178) 1 1177 (true, (init pI1178), (init pI1178))) 1178 19 true) = true := by
  decide +kernel
theorem I1178_ok : RunOK pI1178 1178 (runFrom pI1178 (fmask pI1178) (cmask pI1178) (hmask pI1178) 1 1177 (true, (init pI1178), (init pI1178))) ∧ intTest pI1178 (runFrom pI1178 (fmask pI1178) (cmask pI1178) (hmask pI1178) 1 1177 (true, (init pI1178), (init pI1178))) 1178 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1178_fin) true) (by decide) rfl I1178_fin intTest_fst
theorem link1178 : linkOK pL1178 pH1178 pI1178 = true := by decide +kernel
theorem cvx1178 : ConvexBetweenHumps 1178 :=
  cvx_of L1178_ok H1178_ok I1178_ok link1178 (by decide)
theorem cenlink1178 : cenLinkOK pI1178 1178 = true := by decide +kernel
theorem cen1178 : CenterUniqueMin 1178 ∧ DipHyp 1178 ∧ OnePointHyps 1178 :=
  cen_of L1178_ok H1178_ok I1178_ok link1178 cenlink1178

/-! ### `N = 1179` -/

def pL1179 : Prm := ⟨76, 35, 38, 1181, 11, 18446744073709551616, 151215155132274411, 151215155132274411⟩
def pH1179 : Prm := ⟨76, 35, 38, 1181, 11, 18446744073709551616, 151217354155529963, 151217354155529963⟩
def pI1179 : Prm := ⟨66, 32, 31, 1181, 11, 18446744073709551616, 151215155132274411, 151217354155529963⟩
theorem L1179_fin : (prmOK pL1179 1179 && ptTest pL1179 (runFrom pL1179 (fmask pL1179) (cmask pL1179) (hmask pL1179) 1 1178 (true, (init pL1179), (init pL1179))) 1179 590 false) = true := by
  decide +kernel
theorem L1179_ok : RunOK pL1179 1179 (runFrom pL1179 (fmask pL1179) (cmask pL1179) (hmask pL1179) 1 1178 (true, (init pL1179), (init pL1179))) ∧ ptTest pL1179 (runFrom pL1179 (fmask pL1179) (cmask pL1179) (hmask pL1179) 1 1178 (true, (init pL1179), (init pL1179))) 1179 590 false = true :=
  fin_run (runOK_init (prmOK_of_and L1179_fin) true) (by decide) rfl L1179_fin ptTest_fst
theorem H1179_fin : (prmOK pH1179 1179 && ptTest pH1179 (runFrom pH1179 (fmask pH1179) (cmask pH1179) (hmask pH1179) 1 1178 (true, (init pH1179), (init pH1179))) 1179 590 true) = true := by
  decide +kernel
theorem H1179_ok : RunOK pH1179 1179 (runFrom pH1179 (fmask pH1179) (cmask pH1179) (hmask pH1179) 1 1178 (true, (init pH1179), (init pH1179))) ∧ ptTest pH1179 (runFrom pH1179 (fmask pH1179) (cmask pH1179) (hmask pH1179) 1 1178 (true, (init pH1179), (init pH1179))) 1179 590 true = true :=
  fin_run (runOK_init (prmOK_of_and H1179_fin) true) (by decide) rfl H1179_fin ptTest_fst
theorem I1179_fin : (prmOK pI1179 1179 && intTest pI1179 (runFrom pI1179 (fmask pI1179) (cmask pI1179) (hmask pI1179) 1 1178 (true, (init pI1179), (init pI1179))) 1179 19 false) = true := by
  decide +kernel
theorem I1179_ok : RunOK pI1179 1179 (runFrom pI1179 (fmask pI1179) (cmask pI1179) (hmask pI1179) 1 1178 (true, (init pI1179), (init pI1179))) ∧ intTest pI1179 (runFrom pI1179 (fmask pI1179) (cmask pI1179) (hmask pI1179) 1 1178 (true, (init pI1179), (init pI1179))) 1179 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1179_fin) true) (by decide) rfl I1179_fin intTest_fst
theorem link1179 : linkOK pL1179 pH1179 pI1179 = true := by decide +kernel
theorem cvx1179 : ConvexBetweenHumps 1179 :=
  cvx_of L1179_ok H1179_ok I1179_ok link1179 (by decide)

/-! ### `N = 1180` -/

def pL1180 : Prm := ⟨76, 35, 38, 1182, 11, 18446744073709551616, 151112036146187437, 151112036146187437⟩
def pH1180 : Prm := ⟨76, 35, 38, 1182, 11, 18446744073709551616, 151114235169442989, 151114235169442989⟩
def pI1180 : Prm := ⟨66, 32, 31, 1182, 11, 18446744073709551616, 151112036146187437, 151114235169442989⟩
theorem L1180_fin : (prmOK pL1180 1180 && ptTest pL1180 (runFrom pL1180 (fmask pL1180) (cmask pL1180) (hmask pL1180) 1 1179 (true, (init pL1180), (init pL1180))) 1180 590 false) = true := by
  decide +kernel
theorem L1180_ok : RunOK pL1180 1180 (runFrom pL1180 (fmask pL1180) (cmask pL1180) (hmask pL1180) 1 1179 (true, (init pL1180), (init pL1180))) ∧ ptTest pL1180 (runFrom pL1180 (fmask pL1180) (cmask pL1180) (hmask pL1180) 1 1179 (true, (init pL1180), (init pL1180))) 1180 590 false = true :=
  fin_run (runOK_init (prmOK_of_and L1180_fin) true) (by decide) rfl L1180_fin ptTest_fst
theorem H1180_fin : (prmOK pH1180 1180 && ptTest pH1180 (runFrom pH1180 (fmask pH1180) (cmask pH1180) (hmask pH1180) 1 1179 (true, (init pH1180), (init pH1180))) 1180 590 true) = true := by
  decide +kernel
theorem H1180_ok : RunOK pH1180 1180 (runFrom pH1180 (fmask pH1180) (cmask pH1180) (hmask pH1180) 1 1179 (true, (init pH1180), (init pH1180))) ∧ ptTest pH1180 (runFrom pH1180 (fmask pH1180) (cmask pH1180) (hmask pH1180) 1 1179 (true, (init pH1180), (init pH1180))) 1180 590 true = true :=
  fin_run (runOK_init (prmOK_of_and H1180_fin) true) (by decide) rfl H1180_fin ptTest_fst
theorem I1180_fin : (prmOK pI1180 1180 && intTest pI1180 (runFrom pI1180 (fmask pI1180) (cmask pI1180) (hmask pI1180) 1 1179 (true, (init pI1180), (init pI1180))) 1180 19 true) = true := by
  decide +kernel
theorem I1180_ok : RunOK pI1180 1180 (runFrom pI1180 (fmask pI1180) (cmask pI1180) (hmask pI1180) 1 1179 (true, (init pI1180), (init pI1180))) ∧ intTest pI1180 (runFrom pI1180 (fmask pI1180) (cmask pI1180) (hmask pI1180) 1 1179 (true, (init pI1180), (init pI1180))) 1180 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1180_fin) true) (by decide) rfl I1180_fin intTest_fst
theorem link1180 : linkOK pL1180 pH1180 pI1180 = true := by decide +kernel
theorem cvx1180 : ConvexBetweenHumps 1180 :=
  cvx_of L1180_ok H1180_ok I1180_ok link1180 (by decide)
theorem cenlink1180 : cenLinkOK pI1180 1180 = true := by decide +kernel
theorem cen1180 : CenterUniqueMin 1180 ∧ DipHyp 1180 ∧ OnePointHyps 1180 :=
  cen_of L1180_ok H1180_ok I1180_ok link1180 cenlink1180

/-! ### `N = 1181` -/

def pL1181 : Prm := ⟨76, 35, 38, 1183, 11, 18446744073709551616, 151009000948015950, 151009000948015950⟩
def pH1181 : Prm := ⟨76, 35, 38, 1183, 11, 18446744073709551616, 151011199971271502, 151011199971271502⟩
def pI1181 : Prm := ⟨66, 32, 31, 1183, 11, 18446744073709551616, 151009000948015950, 151011199971271502⟩
theorem L1181_fin : (prmOK pL1181 1181 && ptTest pL1181 (runFrom pL1181 (fmask pL1181) (cmask pL1181) (hmask pL1181) 1 1180 (true, (init pL1181), (init pL1181))) 1181 591 false) = true := by
  decide +kernel
theorem L1181_ok : RunOK pL1181 1181 (runFrom pL1181 (fmask pL1181) (cmask pL1181) (hmask pL1181) 1 1180 (true, (init pL1181), (init pL1181))) ∧ ptTest pL1181 (runFrom pL1181 (fmask pL1181) (cmask pL1181) (hmask pL1181) 1 1180 (true, (init pL1181), (init pL1181))) 1181 591 false = true :=
  fin_run (runOK_init (prmOK_of_and L1181_fin) true) (by decide) rfl L1181_fin ptTest_fst
theorem H1181_fin : (prmOK pH1181 1181 && ptTest pH1181 (runFrom pH1181 (fmask pH1181) (cmask pH1181) (hmask pH1181) 1 1180 (true, (init pH1181), (init pH1181))) 1181 591 true) = true := by
  decide +kernel
theorem H1181_ok : RunOK pH1181 1181 (runFrom pH1181 (fmask pH1181) (cmask pH1181) (hmask pH1181) 1 1180 (true, (init pH1181), (init pH1181))) ∧ ptTest pH1181 (runFrom pH1181 (fmask pH1181) (cmask pH1181) (hmask pH1181) 1 1180 (true, (init pH1181), (init pH1181))) 1181 591 true = true :=
  fin_run (runOK_init (prmOK_of_and H1181_fin) true) (by decide) rfl H1181_fin ptTest_fst
theorem I1181_fin : (prmOK pI1181 1181 && intTest pI1181 (runFrom pI1181 (fmask pI1181) (cmask pI1181) (hmask pI1181) 1 1180 (true, (init pI1181), (init pI1181))) 1181 19 false) = true := by
  decide +kernel
theorem I1181_ok : RunOK pI1181 1181 (runFrom pI1181 (fmask pI1181) (cmask pI1181) (hmask pI1181) 1 1180 (true, (init pI1181), (init pI1181))) ∧ intTest pI1181 (runFrom pI1181 (fmask pI1181) (cmask pI1181) (hmask pI1181) 1 1180 (true, (init pI1181), (init pI1181))) 1181 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1181_fin) true) (by decide) rfl I1181_fin intTest_fst
theorem link1181 : linkOK pL1181 pH1181 pI1181 = true := by decide +kernel
theorem cvx1181 : ConvexBetweenHumps 1181 :=
  cvx_of L1181_ok H1181_ok I1181_ok link1181 (by decide)

/-! ### `N = 1182` -/

def pL1182 : Prm := ⟨76, 35, 38, 1184, 11, 18446744073709551616, 150906188476035324, 150906188476035324⟩
def pH1182 : Prm := ⟨76, 35, 38, 1184, 11, 18446744073709551616, 150908387499290876, 150908387499290876⟩
def pI1182 : Prm := ⟨66, 32, 31, 1184, 11, 18446744073709551616, 150906188476035324, 150908387499290876⟩
theorem L1182_fin : (prmOK pL1182 1182 && ptTest pL1182 (runFrom pL1182 (fmask pL1182) (cmask pL1182) (hmask pL1182) 1 1181 (true, (init pL1182), (init pL1182))) 1182 591 false) = true := by
  decide +kernel
theorem L1182_ok : RunOK pL1182 1182 (runFrom pL1182 (fmask pL1182) (cmask pL1182) (hmask pL1182) 1 1181 (true, (init pL1182), (init pL1182))) ∧ ptTest pL1182 (runFrom pL1182 (fmask pL1182) (cmask pL1182) (hmask pL1182) 1 1181 (true, (init pL1182), (init pL1182))) 1182 591 false = true :=
  fin_run (runOK_init (prmOK_of_and L1182_fin) true) (by decide) rfl L1182_fin ptTest_fst
theorem H1182_fin : (prmOK pH1182 1182 && ptTest pH1182 (runFrom pH1182 (fmask pH1182) (cmask pH1182) (hmask pH1182) 1 1181 (true, (init pH1182), (init pH1182))) 1182 591 true) = true := by
  decide +kernel
theorem H1182_ok : RunOK pH1182 1182 (runFrom pH1182 (fmask pH1182) (cmask pH1182) (hmask pH1182) 1 1181 (true, (init pH1182), (init pH1182))) ∧ ptTest pH1182 (runFrom pH1182 (fmask pH1182) (cmask pH1182) (hmask pH1182) 1 1181 (true, (init pH1182), (init pH1182))) 1182 591 true = true :=
  fin_run (runOK_init (prmOK_of_and H1182_fin) true) (by decide) rfl H1182_fin ptTest_fst
theorem I1182_fin : (prmOK pI1182 1182 && intTest pI1182 (runFrom pI1182 (fmask pI1182) (cmask pI1182) (hmask pI1182) 1 1181 (true, (init pI1182), (init pI1182))) 1182 19 true) = true := by
  decide +kernel
theorem I1182_ok : RunOK pI1182 1182 (runFrom pI1182 (fmask pI1182) (cmask pI1182) (hmask pI1182) 1 1181 (true, (init pI1182), (init pI1182))) ∧ intTest pI1182 (runFrom pI1182 (fmask pI1182) (cmask pI1182) (hmask pI1182) 1 1181 (true, (init pI1182), (init pI1182))) 1182 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1182_fin) true) (by decide) rfl I1182_fin intTest_fst
theorem link1182 : linkOK pL1182 pH1182 pI1182 = true := by decide +kernel
theorem cvx1182 : ConvexBetweenHumps 1182 :=
  cvx_of L1182_ok H1182_ok I1182_ok link1182 (by decide)
theorem cenlink1182 : cenLinkOK pI1182 1182 = true := by decide +kernel
theorem cen1182 : CenterUniqueMin 1182 ∧ DipHyp 1182 ∧ OnePointHyps 1182 :=
  cen_of L1182_ok H1182_ok I1182_ok link1182 cenlink1182

/-! ### The range -/

theorem cvx_1152_1182 {N : ℕ} (h1 : 1152 ≤ N) (h2 : N ≤ 1182) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1166
  · by_cases h4 : N ≤ 1158
    · by_cases h6 : N ≤ 1154
      · by_cases h8 : N ≤ 1152
        · obtain rfl : N = 1152 := by omega
          exact cvx1152
        · by_cases h10 : N ≤ 1153
          · obtain rfl : N = 1153 := by omega
            exact cvx1153
          · obtain rfl : N = 1154 := by omega
            exact cvx1154
      · by_cases h8 : N ≤ 1156
        · by_cases h10 : N ≤ 1155
          · obtain rfl : N = 1155 := by omega
            exact cvx1155
          · obtain rfl : N = 1156 := by omega
            exact cvx1156
        · by_cases h10 : N ≤ 1157
          · obtain rfl : N = 1157 := by omega
            exact cvx1157
          · obtain rfl : N = 1158 := by omega
            exact cvx1158
    · by_cases h6 : N ≤ 1162
      · by_cases h8 : N ≤ 1160
        · by_cases h10 : N ≤ 1159
          · obtain rfl : N = 1159 := by omega
            exact cvx1159
          · obtain rfl : N = 1160 := by omega
            exact cvx1160
        · by_cases h10 : N ≤ 1161
          · obtain rfl : N = 1161 := by omega
            exact cvx1161
          · obtain rfl : N = 1162 := by omega
            exact cvx1162
      · by_cases h8 : N ≤ 1164
        · by_cases h10 : N ≤ 1163
          · obtain rfl : N = 1163 := by omega
            exact cvx1163
          · obtain rfl : N = 1164 := by omega
            exact cvx1164
        · by_cases h10 : N ≤ 1165
          · obtain rfl : N = 1165 := by omega
            exact cvx1165
          · obtain rfl : N = 1166 := by omega
            exact cvx1166
  · by_cases h4 : N ≤ 1174
    · by_cases h6 : N ≤ 1170
      · by_cases h8 : N ≤ 1168
        · by_cases h10 : N ≤ 1167
          · obtain rfl : N = 1167 := by omega
            exact cvx1167
          · obtain rfl : N = 1168 := by omega
            exact cvx1168
        · by_cases h10 : N ≤ 1169
          · obtain rfl : N = 1169 := by omega
            exact cvx1169
          · obtain rfl : N = 1170 := by omega
            exact cvx1170
      · by_cases h8 : N ≤ 1172
        · by_cases h10 : N ≤ 1171
          · obtain rfl : N = 1171 := by omega
            exact cvx1171
          · obtain rfl : N = 1172 := by omega
            exact cvx1172
        · by_cases h10 : N ≤ 1173
          · obtain rfl : N = 1173 := by omega
            exact cvx1173
          · obtain rfl : N = 1174 := by omega
            exact cvx1174
    · by_cases h6 : N ≤ 1178
      · by_cases h8 : N ≤ 1176
        · by_cases h10 : N ≤ 1175
          · obtain rfl : N = 1175 := by omega
            exact cvx1175
          · obtain rfl : N = 1176 := by omega
            exact cvx1176
        · by_cases h10 : N ≤ 1177
          · obtain rfl : N = 1177 := by omega
            exact cvx1177
          · obtain rfl : N = 1178 := by omega
            exact cvx1178
      · by_cases h8 : N ≤ 1180
        · by_cases h10 : N ≤ 1179
          · obtain rfl : N = 1179 := by omega
            exact cvx1179
          · obtain rfl : N = 1180 := by omega
            exact cvx1180
        · by_cases h10 : N ≤ 1181
          · obtain rfl : N = 1181 := by omega
            exact cvx1181
          · obtain rfl : N = 1182 := by omega
            exact cvx1182

theorem cen_1152_1182 {N : ℕ} (h1 : 1152 ≤ N) (h2 : N ≤ 1182) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1166
  · by_cases h4 : N ≤ 1158
    · by_cases h6 : N ≤ 1154
      · by_cases h8 : N ≤ 1152
        · obtain rfl : N = 1152 := by omega
          exact cen1152
        · obtain rfl : N = 1154 := by omega
          exact cen1154
      · by_cases h8 : N ≤ 1156
        · obtain rfl : N = 1156 := by omega
          exact cen1156
        · obtain rfl : N = 1158 := by omega
          exact cen1158
    · by_cases h6 : N ≤ 1162
      · by_cases h8 : N ≤ 1160
        · obtain rfl : N = 1160 := by omega
          exact cen1160
        · obtain rfl : N = 1162 := by omega
          exact cen1162
      · by_cases h8 : N ≤ 1164
        · obtain rfl : N = 1164 := by omega
          exact cen1164
        · obtain rfl : N = 1166 := by omega
          exact cen1166
  · by_cases h4 : N ≤ 1174
    · by_cases h6 : N ≤ 1170
      · by_cases h8 : N ≤ 1168
        · obtain rfl : N = 1168 := by omega
          exact cen1168
        · obtain rfl : N = 1170 := by omega
          exact cen1170
      · by_cases h8 : N ≤ 1172
        · obtain rfl : N = 1172 := by omega
          exact cen1172
        · obtain rfl : N = 1174 := by omega
          exact cen1174
    · by_cases h6 : N ≤ 1178
      · by_cases h8 : N ≤ 1176
        · obtain rfl : N = 1176 := by omega
          exact cen1176
        · obtain rfl : N = 1178 := by omega
          exact cen1178
      · by_cases h8 : N ≤ 1180
        · obtain rfl : N = 1180 := by omega
          exact cen1180
        · obtain rfl : N = 1182 := by omega
          exact cen1182

end Kagey131.PaperD.T7
