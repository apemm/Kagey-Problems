import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1086, …, 1119` (generated)

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

/-! ### `N = 1086` -/

def pL1086 : Prm := ⟨78, 38, 37, 1088, 11, 18446744073709551616, 161532531376260452, 161532531376260452⟩
def pH1086 : Prm := ⟨78, 38, 37, 1088, 11, 18446744073709551616, 161534730399516004, 161534730399516004⟩
def pI1086 : Prm := ⟨65, 32, 30, 1088, 11, 18446744073709551616, 161532531376260452, 161534730399516004⟩
theorem L1086_fin : (prmOK pL1086 1086 && ptTest pL1086 (runFrom pL1086 (fmask pL1086) (cmask pL1086) (hmask pL1086) 1 1085 (true, (init pL1086), (init pL1086))) 1086 543 false) = true := by
  decide +kernel
theorem L1086_ok : RunOK pL1086 1086 (runFrom pL1086 (fmask pL1086) (cmask pL1086) (hmask pL1086) 1 1085 (true, (init pL1086), (init pL1086))) ∧ ptTest pL1086 (runFrom pL1086 (fmask pL1086) (cmask pL1086) (hmask pL1086) 1 1085 (true, (init pL1086), (init pL1086))) 1086 543 false = true :=
  fin_run (runOK_init (prmOK_of_and L1086_fin) true) (by decide) rfl L1086_fin ptTest_fst
theorem H1086_fin : (prmOK pH1086 1086 && ptTest pH1086 (runFrom pH1086 (fmask pH1086) (cmask pH1086) (hmask pH1086) 1 1085 (true, (init pH1086), (init pH1086))) 1086 543 true) = true := by
  decide +kernel
theorem H1086_ok : RunOK pH1086 1086 (runFrom pH1086 (fmask pH1086) (cmask pH1086) (hmask pH1086) 1 1085 (true, (init pH1086), (init pH1086))) ∧ ptTest pH1086 (runFrom pH1086 (fmask pH1086) (cmask pH1086) (hmask pH1086) 1 1085 (true, (init pH1086), (init pH1086))) 1086 543 true = true :=
  fin_run (runOK_init (prmOK_of_and H1086_fin) true) (by decide) rfl H1086_fin ptTest_fst
theorem I1086_fin : (prmOK pI1086 1086 && intTest pI1086 (runFrom pI1086 (fmask pI1086) (cmask pI1086) (hmask pI1086) 1 1085 (true, (init pI1086), (init pI1086))) 1086 18 true) = true := by
  decide +kernel
theorem I1086_ok : RunOK pI1086 1086 (runFrom pI1086 (fmask pI1086) (cmask pI1086) (hmask pI1086) 1 1085 (true, (init pI1086), (init pI1086))) ∧ intTest pI1086 (runFrom pI1086 (fmask pI1086) (cmask pI1086) (hmask pI1086) 1 1085 (true, (init pI1086), (init pI1086))) 1086 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1086_fin) true) (by decide) rfl I1086_fin intTest_fst
theorem link1086 : linkOK pL1086 pH1086 pI1086 = true := by decide +kernel
theorem cvx1086 : ConvexBetweenHumps 1086 :=
  cvx_of L1086_ok H1086_ok I1086_ok link1086 (by decide)
theorem cenlink1086 : cenLinkOK pI1086 1086 = true := by decide +kernel
theorem cen1086 : CenterUniqueMin 1086 ∧ DipHyp 1086 ∧ OnePointHyps 1086 :=
  cen_of L1086_ok H1086_ok I1086_ok link1086 cenlink1086

/-! ### `N = 1087` -/

def pL1087 : Prm := ⟨77, 37, 37, 1089, 11, 18446744073709551616, 161413338710778381, 161413338710778381⟩
def pH1087 : Prm := ⟨78, 38, 37, 1089, 11, 18446744073709551616, 161415537734033933, 161415537734033933⟩
def pI1087 : Prm := ⟨65, 32, 30, 1089, 11, 18446744073709551616, 161413338710778381, 161415537734033933⟩
theorem L1087_fin : (prmOK pL1087 1087 && ptTest pL1087 (runFrom pL1087 (fmask pL1087) (cmask pL1087) (hmask pL1087) 1 1086 (true, (init pL1087), (init pL1087))) 1087 544 false) = true := by
  decide +kernel
theorem L1087_ok : RunOK pL1087 1087 (runFrom pL1087 (fmask pL1087) (cmask pL1087) (hmask pL1087) 1 1086 (true, (init pL1087), (init pL1087))) ∧ ptTest pL1087 (runFrom pL1087 (fmask pL1087) (cmask pL1087) (hmask pL1087) 1 1086 (true, (init pL1087), (init pL1087))) 1087 544 false = true :=
  fin_run (runOK_init (prmOK_of_and L1087_fin) true) (by decide) rfl L1087_fin ptTest_fst
theorem H1087_fin : (prmOK pH1087 1087 && ptTest pH1087 (runFrom pH1087 (fmask pH1087) (cmask pH1087) (hmask pH1087) 1 1086 (true, (init pH1087), (init pH1087))) 1087 544 true) = true := by
  decide +kernel
theorem H1087_ok : RunOK pH1087 1087 (runFrom pH1087 (fmask pH1087) (cmask pH1087) (hmask pH1087) 1 1086 (true, (init pH1087), (init pH1087))) ∧ ptTest pH1087 (runFrom pH1087 (fmask pH1087) (cmask pH1087) (hmask pH1087) 1 1086 (true, (init pH1087), (init pH1087))) 1087 544 true = true :=
  fin_run (runOK_init (prmOK_of_and H1087_fin) true) (by decide) rfl H1087_fin ptTest_fst
theorem I1087_fin : (prmOK pI1087 1087 && intTest pI1087 (runFrom pI1087 (fmask pI1087) (cmask pI1087) (hmask pI1087) 1 1086 (true, (init pI1087), (init pI1087))) 1087 18 false) = true := by
  decide +kernel
theorem I1087_ok : RunOK pI1087 1087 (runFrom pI1087 (fmask pI1087) (cmask pI1087) (hmask pI1087) 1 1086 (true, (init pI1087), (init pI1087))) ∧ intTest pI1087 (runFrom pI1087 (fmask pI1087) (cmask pI1087) (hmask pI1087) 1 1086 (true, (init pI1087), (init pI1087))) 1087 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1087_fin) true) (by decide) rfl I1087_fin intTest_fst
theorem link1087 : linkOK pL1087 pH1087 pI1087 = true := by decide +kernel
theorem cvx1087 : ConvexBetweenHumps 1087 :=
  cvx_of L1087_ok H1087_ok I1087_ok link1087 (by decide)

/-! ### `N = 1088` -/

def pL1088 : Prm := ⟨78, 38, 37, 1090, 11, 18446744073709551616, 161294427600773458, 161294427600773458⟩
def pH1088 : Prm := ⟨78, 38, 37, 1090, 11, 18446744073709551616, 161296626624029010, 161296626624029010⟩
def pI1088 : Prm := ⟨65, 32, 30, 1090, 11, 18446744073709551616, 161294427600773458, 161296626624029010⟩
theorem L1088_fin : (prmOK pL1088 1088 && ptTest pL1088 (runFrom pL1088 (fmask pL1088) (cmask pL1088) (hmask pL1088) 1 1087 (true, (init pL1088), (init pL1088))) 1088 544 false) = true := by
  decide +kernel
theorem L1088_ok : RunOK pL1088 1088 (runFrom pL1088 (fmask pL1088) (cmask pL1088) (hmask pL1088) 1 1087 (true, (init pL1088), (init pL1088))) ∧ ptTest pL1088 (runFrom pL1088 (fmask pL1088) (cmask pL1088) (hmask pL1088) 1 1087 (true, (init pL1088), (init pL1088))) 1088 544 false = true :=
  fin_run (runOK_init (prmOK_of_and L1088_fin) true) (by decide) rfl L1088_fin ptTest_fst
theorem H1088_fin : (prmOK pH1088 1088 && ptTest pH1088 (runFrom pH1088 (fmask pH1088) (cmask pH1088) (hmask pH1088) 1 1087 (true, (init pH1088), (init pH1088))) 1088 544 true) = true := by
  decide +kernel
theorem H1088_ok : RunOK pH1088 1088 (runFrom pH1088 (fmask pH1088) (cmask pH1088) (hmask pH1088) 1 1087 (true, (init pH1088), (init pH1088))) ∧ ptTest pH1088 (runFrom pH1088 (fmask pH1088) (cmask pH1088) (hmask pH1088) 1 1087 (true, (init pH1088), (init pH1088))) 1088 544 true = true :=
  fin_run (runOK_init (prmOK_of_and H1088_fin) true) (by decide) rfl H1088_fin ptTest_fst
theorem I1088_fin : (prmOK pI1088 1088 && intTest pI1088 (runFrom pI1088 (fmask pI1088) (cmask pI1088) (hmask pI1088) 1 1087 (true, (init pI1088), (init pI1088))) 1088 18 true) = true := by
  decide +kernel
theorem I1088_ok : RunOK pI1088 1088 (runFrom pI1088 (fmask pI1088) (cmask pI1088) (hmask pI1088) 1 1087 (true, (init pI1088), (init pI1088))) ∧ intTest pI1088 (runFrom pI1088 (fmask pI1088) (cmask pI1088) (hmask pI1088) 1 1087 (true, (init pI1088), (init pI1088))) 1088 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1088_fin) true) (by decide) rfl I1088_fin intTest_fst
theorem link1088 : linkOK pL1088 pH1088 pI1088 = true := by decide +kernel
theorem cvx1088 : ConvexBetweenHumps 1088 :=
  cvx_of L1088_ok H1088_ok I1088_ok link1088 (by decide)
theorem cenlink1088 : cenLinkOK pI1088 1088 = true := by decide +kernel
theorem cen1088 : CenterUniqueMin 1088 ∧ DipHyp 1088 ∧ OnePointHyps 1088 :=
  cen_of L1088_ok H1088_ok I1088_ok link1088 cenlink1088

/-! ### `N = 1089` -/

def pL1089 : Prm := ⟨78, 38, 37, 1091, 11, 18446744073709551616, 161175618623934111, 161175618623934111⟩
def pH1089 : Prm := ⟨78, 38, 37, 1091, 11, 18446744073709551616, 161177817647189663, 161177817647189663⟩
def pI1089 : Prm := ⟨65, 32, 30, 1091, 11, 18446744073709551616, 161175618623934111, 161177817647189663⟩
theorem L1089_fin : (prmOK pL1089 1089 && ptTest pL1089 (runFrom pL1089 (fmask pL1089) (cmask pL1089) (hmask pL1089) 1 1088 (true, (init pL1089), (init pL1089))) 1089 545 false) = true := by
  decide +kernel
theorem L1089_ok : RunOK pL1089 1089 (runFrom pL1089 (fmask pL1089) (cmask pL1089) (hmask pL1089) 1 1088 (true, (init pL1089), (init pL1089))) ∧ ptTest pL1089 (runFrom pL1089 (fmask pL1089) (cmask pL1089) (hmask pL1089) 1 1088 (true, (init pL1089), (init pL1089))) 1089 545 false = true :=
  fin_run (runOK_init (prmOK_of_and L1089_fin) true) (by decide) rfl L1089_fin ptTest_fst
theorem H1089_fin : (prmOK pH1089 1089 && ptTest pH1089 (runFrom pH1089 (fmask pH1089) (cmask pH1089) (hmask pH1089) 1 1088 (true, (init pH1089), (init pH1089))) 1089 545 true) = true := by
  decide +kernel
theorem H1089_ok : RunOK pH1089 1089 (runFrom pH1089 (fmask pH1089) (cmask pH1089) (hmask pH1089) 1 1088 (true, (init pH1089), (init pH1089))) ∧ ptTest pH1089 (runFrom pH1089 (fmask pH1089) (cmask pH1089) (hmask pH1089) 1 1088 (true, (init pH1089), (init pH1089))) 1089 545 true = true :=
  fin_run (runOK_init (prmOK_of_and H1089_fin) true) (by decide) rfl H1089_fin ptTest_fst
theorem I1089_fin : (prmOK pI1089 1089 && intTest pI1089 (runFrom pI1089 (fmask pI1089) (cmask pI1089) (hmask pI1089) 1 1088 (true, (init pI1089), (init pI1089))) 1089 18 false) = true := by
  decide +kernel
theorem I1089_ok : RunOK pI1089 1089 (runFrom pI1089 (fmask pI1089) (cmask pI1089) (hmask pI1089) 1 1088 (true, (init pI1089), (init pI1089))) ∧ intTest pI1089 (runFrom pI1089 (fmask pI1089) (cmask pI1089) (hmask pI1089) 1 1088 (true, (init pI1089), (init pI1089))) 1089 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1089_fin) true) (by decide) rfl I1089_fin intTest_fst
theorem link1089 : linkOK pL1089 pH1089 pI1089 = true := by decide +kernel
theorem cvx1089 : ConvexBetweenHumps 1089 :=
  cvx_of L1089_ok H1089_ok I1089_ok link1089 (by decide)

/-! ### `N = 1090` -/

def pL1090 : Prm := ⟨78, 38, 37, 1092, 11, 18446744073709551616, 161057089744227667, 161057089744227667⟩
def pH1090 : Prm := ⟨78, 38, 37, 1092, 11, 18446744073709551616, 161059288767483219, 161059288767483219⟩
def pI1090 : Prm := ⟨65, 32, 30, 1092, 11, 18446744073709551616, 161057089744227667, 161059288767483219⟩
theorem L1090_fin : (prmOK pL1090 1090 && ptTest pL1090 (runFrom pL1090 (fmask pL1090) (cmask pL1090) (hmask pL1090) 1 1089 (true, (init pL1090), (init pL1090))) 1090 545 false) = true := by
  decide +kernel
theorem L1090_ok : RunOK pL1090 1090 (runFrom pL1090 (fmask pL1090) (cmask pL1090) (hmask pL1090) 1 1089 (true, (init pL1090), (init pL1090))) ∧ ptTest pL1090 (runFrom pL1090 (fmask pL1090) (cmask pL1090) (hmask pL1090) 1 1089 (true, (init pL1090), (init pL1090))) 1090 545 false = true :=
  fin_run (runOK_init (prmOK_of_and L1090_fin) true) (by decide) rfl L1090_fin ptTest_fst
theorem H1090_fin : (prmOK pH1090 1090 && ptTest pH1090 (runFrom pH1090 (fmask pH1090) (cmask pH1090) (hmask pH1090) 1 1089 (true, (init pH1090), (init pH1090))) 1090 545 true) = true := by
  decide +kernel
theorem H1090_ok : RunOK pH1090 1090 (runFrom pH1090 (fmask pH1090) (cmask pH1090) (hmask pH1090) 1 1089 (true, (init pH1090), (init pH1090))) ∧ ptTest pH1090 (runFrom pH1090 (fmask pH1090) (cmask pH1090) (hmask pH1090) 1 1089 (true, (init pH1090), (init pH1090))) 1090 545 true = true :=
  fin_run (runOK_init (prmOK_of_and H1090_fin) true) (by decide) rfl H1090_fin ptTest_fst
theorem I1090_fin : (prmOK pI1090 1090 && intTest pI1090 (runFrom pI1090 (fmask pI1090) (cmask pI1090) (hmask pI1090) 1 1089 (true, (init pI1090), (init pI1090))) 1090 18 true) = true := by
  decide +kernel
theorem I1090_ok : RunOK pI1090 1090 (runFrom pI1090 (fmask pI1090) (cmask pI1090) (hmask pI1090) 1 1089 (true, (init pI1090), (init pI1090))) ∧ intTest pI1090 (runFrom pI1090 (fmask pI1090) (cmask pI1090) (hmask pI1090) 1 1089 (true, (init pI1090), (init pI1090))) 1090 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1090_fin) true) (by decide) rfl I1090_fin intTest_fst
theorem link1090 : linkOK pL1090 pH1090 pI1090 = true := by decide +kernel
theorem cvx1090 : ConvexBetweenHumps 1090 :=
  cvx_of L1090_ok H1090_ok I1090_ok link1090 (by decide)
theorem cenlink1090 : cenLinkOK pI1090 1090 = true := by decide +kernel
theorem cen1090 : CenterUniqueMin 1090 ∧ DipHyp 1090 ∧ OnePointHyps 1090 :=
  cen_of L1090_ok H1090_ok I1090_ok link1090 cenlink1090

/-! ### `N = 1091` -/

def pL1091 : Prm := ⟨78, 38, 37, 1093, 11, 18446744073709551616, 160938662543601746, 160938662543601746⟩
def pH1091 : Prm := ⟨78, 38, 37, 1093, 11, 18446744073709551616, 160940861566857298, 160940861566857298⟩
def pI1091 : Prm := ⟨65, 32, 30, 1093, 11, 18446744073709551616, 160938662543601746, 160940861566857298⟩
theorem L1091_fin : (prmOK pL1091 1091 && ptTest pL1091 (runFrom pL1091 (fmask pL1091) (cmask pL1091) (hmask pL1091) 1 1090 (true, (init pL1091), (init pL1091))) 1091 546 false) = true := by
  decide +kernel
theorem L1091_ok : RunOK pL1091 1091 (runFrom pL1091 (fmask pL1091) (cmask pL1091) (hmask pL1091) 1 1090 (true, (init pL1091), (init pL1091))) ∧ ptTest pL1091 (runFrom pL1091 (fmask pL1091) (cmask pL1091) (hmask pL1091) 1 1090 (true, (init pL1091), (init pL1091))) 1091 546 false = true :=
  fin_run (runOK_init (prmOK_of_and L1091_fin) true) (by decide) rfl L1091_fin ptTest_fst
theorem H1091_fin : (prmOK pH1091 1091 && ptTest pH1091 (runFrom pH1091 (fmask pH1091) (cmask pH1091) (hmask pH1091) 1 1090 (true, (init pH1091), (init pH1091))) 1091 546 true) = true := by
  decide +kernel
theorem H1091_ok : RunOK pH1091 1091 (runFrom pH1091 (fmask pH1091) (cmask pH1091) (hmask pH1091) 1 1090 (true, (init pH1091), (init pH1091))) ∧ ptTest pH1091 (runFrom pH1091 (fmask pH1091) (cmask pH1091) (hmask pH1091) 1 1090 (true, (init pH1091), (init pH1091))) 1091 546 true = true :=
  fin_run (runOK_init (prmOK_of_and H1091_fin) true) (by decide) rfl H1091_fin ptTest_fst
theorem I1091_fin : (prmOK pI1091 1091 && intTest pI1091 (runFrom pI1091 (fmask pI1091) (cmask pI1091) (hmask pI1091) 1 1090 (true, (init pI1091), (init pI1091))) 1091 18 false) = true := by
  decide +kernel
theorem I1091_ok : RunOK pI1091 1091 (runFrom pI1091 (fmask pI1091) (cmask pI1091) (hmask pI1091) 1 1090 (true, (init pI1091), (init pI1091))) ∧ intTest pI1091 (runFrom pI1091 (fmask pI1091) (cmask pI1091) (hmask pI1091) 1 1090 (true, (init pI1091), (init pI1091))) 1091 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1091_fin) true) (by decide) rfl I1091_fin intTest_fst
theorem link1091 : linkOK pL1091 pH1091 pI1091 = true := by decide +kernel
theorem cvx1091 : ConvexBetweenHumps 1091 :=
  cvx_of L1091_ok H1091_ok I1091_ok link1091 (by decide)

/-! ### `N = 1092` -/

def pL1092 : Prm := ⟨78, 38, 37, 1094, 11, 18446744073709551616, 160820513991928637, 160820513991928637⟩
def pH1092 : Prm := ⟨78, 38, 37, 1094, 11, 18446744073709551616, 160822713015184189, 160822713015184189⟩
def pI1092 : Prm := ⟨65, 32, 30, 1094, 11, 18446744073709551616, 160820513991928637, 160822713015184189⟩
theorem L1092_fin : (prmOK pL1092 1092 && ptTest pL1092 (runFrom pL1092 (fmask pL1092) (cmask pL1092) (hmask pL1092) 1 1091 (true, (init pL1092), (init pL1092))) 1092 546 false) = true := by
  decide +kernel
theorem L1092_ok : RunOK pL1092 1092 (runFrom pL1092 (fmask pL1092) (cmask pL1092) (hmask pL1092) 1 1091 (true, (init pL1092), (init pL1092))) ∧ ptTest pL1092 (runFrom pL1092 (fmask pL1092) (cmask pL1092) (hmask pL1092) 1 1091 (true, (init pL1092), (init pL1092))) 1092 546 false = true :=
  fin_run (runOK_init (prmOK_of_and L1092_fin) true) (by decide) rfl L1092_fin ptTest_fst
theorem H1092_fin : (prmOK pH1092 1092 && ptTest pH1092 (runFrom pH1092 (fmask pH1092) (cmask pH1092) (hmask pH1092) 1 1091 (true, (init pH1092), (init pH1092))) 1092 546 true) = true := by
  decide +kernel
theorem H1092_ok : RunOK pH1092 1092 (runFrom pH1092 (fmask pH1092) (cmask pH1092) (hmask pH1092) 1 1091 (true, (init pH1092), (init pH1092))) ∧ ptTest pH1092 (runFrom pH1092 (fmask pH1092) (cmask pH1092) (hmask pH1092) 1 1091 (true, (init pH1092), (init pH1092))) 1092 546 true = true :=
  fin_run (runOK_init (prmOK_of_and H1092_fin) true) (by decide) rfl H1092_fin ptTest_fst
theorem I1092_fin : (prmOK pI1092 1092 && intTest pI1092 (runFrom pI1092 (fmask pI1092) (cmask pI1092) (hmask pI1092) 1 1091 (true, (init pI1092), (init pI1092))) 1092 18 true) = true := by
  decide +kernel
theorem I1092_ok : RunOK pI1092 1092 (runFrom pI1092 (fmask pI1092) (cmask pI1092) (hmask pI1092) 1 1091 (true, (init pI1092), (init pI1092))) ∧ intTest pI1092 (runFrom pI1092 (fmask pI1092) (cmask pI1092) (hmask pI1092) 1 1091 (true, (init pI1092), (init pI1092))) 1092 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1092_fin) true) (by decide) rfl I1092_fin intTest_fst
theorem link1092 : linkOK pL1092 pH1092 pI1092 = true := by decide +kernel
theorem cvx1092 : ConvexBetweenHumps 1092 :=
  cvx_of L1092_ok H1092_ok I1092_ok link1092 (by decide)
theorem cenlink1092 : cenLinkOK pI1092 1092 = true := by decide +kernel
theorem cen1092 : CenterUniqueMin 1092 ∧ DipHyp 1092 ∧ OnePointHyps 1092 :=
  cen_of L1092_ok H1092_ok I1092_ok link1092 cenlink1092

/-! ### `N = 1093` -/

def pL1093 : Prm := ⟨78, 38, 37, 1095, 11, 18446744073709551616, 160702466667981119, 160702466667981119⟩
def pH1093 : Prm := ⟨78, 38, 37, 1095, 11, 18446744073709551616, 160704665691236671, 160704665691236671⟩
def pI1093 : Prm := ⟨65, 32, 30, 1095, 11, 18446744073709551616, 160702466667981119, 160704665691236671⟩
theorem L1093_fin : (prmOK pL1093 1093 && ptTest pL1093 (runFrom pL1093 (fmask pL1093) (cmask pL1093) (hmask pL1093) 1 1092 (true, (init pL1093), (init pL1093))) 1093 547 false) = true := by
  decide +kernel
theorem L1093_ok : RunOK pL1093 1093 (runFrom pL1093 (fmask pL1093) (cmask pL1093) (hmask pL1093) 1 1092 (true, (init pL1093), (init pL1093))) ∧ ptTest pL1093 (runFrom pL1093 (fmask pL1093) (cmask pL1093) (hmask pL1093) 1 1092 (true, (init pL1093), (init pL1093))) 1093 547 false = true :=
  fin_run (runOK_init (prmOK_of_and L1093_fin) true) (by decide) rfl L1093_fin ptTest_fst
theorem H1093_fin : (prmOK pH1093 1093 && ptTest pH1093 (runFrom pH1093 (fmask pH1093) (cmask pH1093) (hmask pH1093) 1 1092 (true, (init pH1093), (init pH1093))) 1093 547 true) = true := by
  decide +kernel
theorem H1093_ok : RunOK pH1093 1093 (runFrom pH1093 (fmask pH1093) (cmask pH1093) (hmask pH1093) 1 1092 (true, (init pH1093), (init pH1093))) ∧ ptTest pH1093 (runFrom pH1093 (fmask pH1093) (cmask pH1093) (hmask pH1093) 1 1092 (true, (init pH1093), (init pH1093))) 1093 547 true = true :=
  fin_run (runOK_init (prmOK_of_and H1093_fin) true) (by decide) rfl H1093_fin ptTest_fst
theorem I1093_fin : (prmOK pI1093 1093 && intTest pI1093 (runFrom pI1093 (fmask pI1093) (cmask pI1093) (hmask pI1093) 1 1092 (true, (init pI1093), (init pI1093))) 1093 18 false) = true := by
  decide +kernel
theorem I1093_ok : RunOK pI1093 1093 (runFrom pI1093 (fmask pI1093) (cmask pI1093) (hmask pI1093) 1 1092 (true, (init pI1093), (init pI1093))) ∧ intTest pI1093 (runFrom pI1093 (fmask pI1093) (cmask pI1093) (hmask pI1093) 1 1092 (true, (init pI1093), (init pI1093))) 1093 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1093_fin) true) (by decide) rfl I1093_fin intTest_fst
theorem link1093 : linkOK pL1093 pH1093 pI1093 = true := by decide +kernel
theorem cvx1093 : ConvexBetweenHumps 1093 :=
  cvx_of L1093_ok H1093_ok I1093_ok link1093 (by decide)

/-! ### `N = 1094` -/

def pL1094 : Prm := ⟨78, 38, 37, 1096, 11, 18446744073709551616, 160584696554952031, 160584696554952031⟩
def pH1094 : Prm := ⟨78, 38, 37, 1096, 11, 18446744073709551616, 160586895578207583, 160586895578207583⟩
def pI1094 : Prm := ⟨65, 32, 30, 1096, 11, 18446744073709551616, 160584696554952031, 160586895578207583⟩
theorem L1094_fin : (prmOK pL1094 1094 && ptTest pL1094 (runFrom pL1094 (fmask pL1094) (cmask pL1094) (hmask pL1094) 1 1093 (true, (init pL1094), (init pL1094))) 1094 547 false) = true := by
  decide +kernel
theorem L1094_ok : RunOK pL1094 1094 (runFrom pL1094 (fmask pL1094) (cmask pL1094) (hmask pL1094) 1 1093 (true, (init pL1094), (init pL1094))) ∧ ptTest pL1094 (runFrom pL1094 (fmask pL1094) (cmask pL1094) (hmask pL1094) 1 1093 (true, (init pL1094), (init pL1094))) 1094 547 false = true :=
  fin_run (runOK_init (prmOK_of_and L1094_fin) true) (by decide) rfl L1094_fin ptTest_fst
theorem H1094_fin : (prmOK pH1094 1094 && ptTest pH1094 (runFrom pH1094 (fmask pH1094) (cmask pH1094) (hmask pH1094) 1 1093 (true, (init pH1094), (init pH1094))) 1094 547 true) = true := by
  decide +kernel
theorem H1094_ok : RunOK pH1094 1094 (runFrom pH1094 (fmask pH1094) (cmask pH1094) (hmask pH1094) 1 1093 (true, (init pH1094), (init pH1094))) ∧ ptTest pH1094 (runFrom pH1094 (fmask pH1094) (cmask pH1094) (hmask pH1094) 1 1093 (true, (init pH1094), (init pH1094))) 1094 547 true = true :=
  fin_run (runOK_init (prmOK_of_and H1094_fin) true) (by decide) rfl H1094_fin ptTest_fst
theorem I1094_fin : (prmOK pI1094 1094 && intTest pI1094 (runFrom pI1094 (fmask pI1094) (cmask pI1094) (hmask pI1094) 1 1093 (true, (init pI1094), (init pI1094))) 1094 18 true) = true := by
  decide +kernel
theorem I1094_ok : RunOK pI1094 1094 (runFrom pI1094 (fmask pI1094) (cmask pI1094) (hmask pI1094) 1 1093 (true, (init pI1094), (init pI1094))) ∧ intTest pI1094 (runFrom pI1094 (fmask pI1094) (cmask pI1094) (hmask pI1094) 1 1093 (true, (init pI1094), (init pI1094))) 1094 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1094_fin) true) (by decide) rfl I1094_fin intTest_fst
theorem link1094 : linkOK pL1094 pH1094 pI1094 = true := by decide +kernel
theorem cvx1094 : ConvexBetweenHumps 1094 :=
  cvx_of L1094_ok H1094_ok I1094_ok link1094 (by decide)
theorem cenlink1094 : cenLinkOK pI1094 1094 = true := by decide +kernel
theorem cen1094 : CenterUniqueMin 1094 ∧ DipHyp 1094 ∧ OnePointHyps 1094 :=
  cen_of L1094_ok H1094_ok I1094_ok link1094 cenlink1094

/-! ### `N = 1095` -/

def pL1095 : Prm := ⟨78, 38, 37, 1097, 11, 18446744073709551616, 160467027221005271, 160467027221005271⟩
def pH1095 : Prm := ⟨78, 38, 37, 1097, 11, 18446744073709551616, 160469226244260823, 160469226244260823⟩
def pI1095 : Prm := ⟨65, 32, 30, 1097, 11, 18446744073709551616, 160467027221005271, 160469226244260823⟩
theorem L1095_fin : (prmOK pL1095 1095 && ptTest pL1095 (runFrom pL1095 (fmask pL1095) (cmask pL1095) (hmask pL1095) 1 1094 (true, (init pL1095), (init pL1095))) 1095 548 false) = true := by
  decide +kernel
theorem L1095_ok : RunOK pL1095 1095 (runFrom pL1095 (fmask pL1095) (cmask pL1095) (hmask pL1095) 1 1094 (true, (init pL1095), (init pL1095))) ∧ ptTest pL1095 (runFrom pL1095 (fmask pL1095) (cmask pL1095) (hmask pL1095) 1 1094 (true, (init pL1095), (init pL1095))) 1095 548 false = true :=
  fin_run (runOK_init (prmOK_of_and L1095_fin) true) (by decide) rfl L1095_fin ptTest_fst
theorem H1095_fin : (prmOK pH1095 1095 && ptTest pH1095 (runFrom pH1095 (fmask pH1095) (cmask pH1095) (hmask pH1095) 1 1094 (true, (init pH1095), (init pH1095))) 1095 548 true) = true := by
  decide +kernel
theorem H1095_ok : RunOK pH1095 1095 (runFrom pH1095 (fmask pH1095) (cmask pH1095) (hmask pH1095) 1 1094 (true, (init pH1095), (init pH1095))) ∧ ptTest pH1095 (runFrom pH1095 (fmask pH1095) (cmask pH1095) (hmask pH1095) 1 1094 (true, (init pH1095), (init pH1095))) 1095 548 true = true :=
  fin_run (runOK_init (prmOK_of_and H1095_fin) true) (by decide) rfl H1095_fin ptTest_fst
theorem I1095_fin : (prmOK pI1095 1095 && intTest pI1095 (runFrom pI1095 (fmask pI1095) (cmask pI1095) (hmask pI1095) 1 1094 (true, (init pI1095), (init pI1095))) 1095 18 false) = true := by
  decide +kernel
theorem I1095_ok : RunOK pI1095 1095 (runFrom pI1095 (fmask pI1095) (cmask pI1095) (hmask pI1095) 1 1094 (true, (init pI1095), (init pI1095))) ∧ intTest pI1095 (runFrom pI1095 (fmask pI1095) (cmask pI1095) (hmask pI1095) 1 1094 (true, (init pI1095), (init pI1095))) 1095 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1095_fin) true) (by decide) rfl I1095_fin intTest_fst
theorem link1095 : linkOK pL1095 pH1095 pI1095 = true := by decide +kernel
theorem cvx1095 : ConvexBetweenHumps 1095 :=
  cvx_of L1095_ok H1095_ok I1095_ok link1095 (by decide)

/-! ### `N = 1096` -/

def pL1096 : Prm := ⟨78, 38, 37, 1098, 11, 18446744073709551616, 160349633669903803, 160349633669903803⟩
def pH1096 : Prm := ⟨78, 38, 37, 1098, 11, 18446744073709551616, 160351832693159355, 160351832693159355⟩
def pI1096 : Prm := ⟨65, 32, 30, 1098, 11, 18446744073709551616, 160349633669903803, 160351832693159355⟩
theorem L1096_fin : (prmOK pL1096 1096 && ptTest pL1096 (runFrom pL1096 (fmask pL1096) (cmask pL1096) (hmask pL1096) 1 1095 (true, (init pL1096), (init pL1096))) 1096 548 false) = true := by
  decide +kernel
theorem L1096_ok : RunOK pL1096 1096 (runFrom pL1096 (fmask pL1096) (cmask pL1096) (hmask pL1096) 1 1095 (true, (init pL1096), (init pL1096))) ∧ ptTest pL1096 (runFrom pL1096 (fmask pL1096) (cmask pL1096) (hmask pL1096) 1 1095 (true, (init pL1096), (init pL1096))) 1096 548 false = true :=
  fin_run (runOK_init (prmOK_of_and L1096_fin) true) (by decide) rfl L1096_fin ptTest_fst
theorem H1096_fin : (prmOK pH1096 1096 && ptTest pH1096 (runFrom pH1096 (fmask pH1096) (cmask pH1096) (hmask pH1096) 1 1095 (true, (init pH1096), (init pH1096))) 1096 548 true) = true := by
  decide +kernel
theorem H1096_ok : RunOK pH1096 1096 (runFrom pH1096 (fmask pH1096) (cmask pH1096) (hmask pH1096) 1 1095 (true, (init pH1096), (init pH1096))) ∧ ptTest pH1096 (runFrom pH1096 (fmask pH1096) (cmask pH1096) (hmask pH1096) 1 1095 (true, (init pH1096), (init pH1096))) 1096 548 true = true :=
  fin_run (runOK_init (prmOK_of_and H1096_fin) true) (by decide) rfl H1096_fin ptTest_fst
theorem I1096_fin : (prmOK pI1096 1096 && intTest pI1096 (runFrom pI1096 (fmask pI1096) (cmask pI1096) (hmask pI1096) 1 1095 (true, (init pI1096), (init pI1096))) 1096 18 true) = true := by
  decide +kernel
theorem I1096_ok : RunOK pI1096 1096 (runFrom pI1096 (fmask pI1096) (cmask pI1096) (hmask pI1096) 1 1095 (true, (init pI1096), (init pI1096))) ∧ intTest pI1096 (runFrom pI1096 (fmask pI1096) (cmask pI1096) (hmask pI1096) 1 1095 (true, (init pI1096), (init pI1096))) 1096 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1096_fin) true) (by decide) rfl I1096_fin intTest_fst
theorem link1096 : linkOK pL1096 pH1096 pI1096 = true := by decide +kernel
theorem cvx1096 : ConvexBetweenHumps 1096 :=
  cvx_of L1096_ok H1096_ok I1096_ok link1096 (by decide)
theorem cenlink1096 : cenLinkOK pI1096 1096 = true := by decide +kernel
theorem cen1096 : CenterUniqueMin 1096 ∧ DipHyp 1096 ∧ OnePointHyps 1096 :=
  cen_of L1096_ok H1096_ok I1096_ok link1096 cenlink1096

/-! ### `N = 1097` -/

def pL1097 : Prm := ⟨78, 38, 37, 1099, 11, 18446744073709551616, 160232340451953070, 160232340451953070⟩
def pH1097 : Prm := ⟨78, 38, 37, 1099, 11, 18446744073709551616, 160234539475208622, 160234539475208622⟩
def pI1097 : Prm := ⟨65, 32, 30, 1099, 11, 18446744073709551616, 160232340451953070, 160234539475208622⟩
theorem L1097_fin : (prmOK pL1097 1097 && ptTest pL1097 (runFrom pL1097 (fmask pL1097) (cmask pL1097) (hmask pL1097) 1 1096 (true, (init pL1097), (init pL1097))) 1097 549 false) = true := by
  decide +kernel
theorem L1097_ok : RunOK pL1097 1097 (runFrom pL1097 (fmask pL1097) (cmask pL1097) (hmask pL1097) 1 1096 (true, (init pL1097), (init pL1097))) ∧ ptTest pL1097 (runFrom pL1097 (fmask pL1097) (cmask pL1097) (hmask pL1097) 1 1096 (true, (init pL1097), (init pL1097))) 1097 549 false = true :=
  fin_run (runOK_init (prmOK_of_and L1097_fin) true) (by decide) rfl L1097_fin ptTest_fst
theorem H1097_fin : (prmOK pH1097 1097 && ptTest pH1097 (runFrom pH1097 (fmask pH1097) (cmask pH1097) (hmask pH1097) 1 1096 (true, (init pH1097), (init pH1097))) 1097 549 true) = true := by
  decide +kernel
theorem H1097_ok : RunOK pH1097 1097 (runFrom pH1097 (fmask pH1097) (cmask pH1097) (hmask pH1097) 1 1096 (true, (init pH1097), (init pH1097))) ∧ ptTest pH1097 (runFrom pH1097 (fmask pH1097) (cmask pH1097) (hmask pH1097) 1 1096 (true, (init pH1097), (init pH1097))) 1097 549 true = true :=
  fin_run (runOK_init (prmOK_of_and H1097_fin) true) (by decide) rfl H1097_fin ptTest_fst
theorem I1097_fin : (prmOK pI1097 1097 && intTest pI1097 (runFrom pI1097 (fmask pI1097) (cmask pI1097) (hmask pI1097) 1 1096 (true, (init pI1097), (init pI1097))) 1097 18 false) = true := by
  decide +kernel
theorem I1097_ok : RunOK pI1097 1097 (runFrom pI1097 (fmask pI1097) (cmask pI1097) (hmask pI1097) 1 1096 (true, (init pI1097), (init pI1097))) ∧ intTest pI1097 (runFrom pI1097 (fmask pI1097) (cmask pI1097) (hmask pI1097) 1 1096 (true, (init pI1097), (init pI1097))) 1097 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1097_fin) true) (by decide) rfl I1097_fin intTest_fst
theorem link1097 : linkOK pL1097 pH1097 pI1097 = true := by decide +kernel
theorem cvx1097 : ConvexBetweenHumps 1097 :=
  cvx_of L1097_ok H1097_ok I1097_ok link1097 (by decide)

/-! ### `N = 1098` -/

def pL1098 : Prm := ⟨78, 38, 37, 1100, 11, 18446744073709551616, 160115321598698839, 160115321598698839⟩
def pH1098 : Prm := ⟨78, 38, 37, 1100, 11, 18446744073709551616, 160117520621954391, 160117520621954391⟩
def pI1098 : Prm := ⟨65, 32, 30, 1100, 11, 18446744073709551616, 160115321598698839, 160117520621954391⟩
theorem L1098_fin : (prmOK pL1098 1098 && ptTest pL1098 (runFrom pL1098 (fmask pL1098) (cmask pL1098) (hmask pL1098) 1 1097 (true, (init pL1098), (init pL1098))) 1098 549 false) = true := by
  decide +kernel
theorem L1098_ok : RunOK pL1098 1098 (runFrom pL1098 (fmask pL1098) (cmask pL1098) (hmask pL1098) 1 1097 (true, (init pL1098), (init pL1098))) ∧ ptTest pL1098 (runFrom pL1098 (fmask pL1098) (cmask pL1098) (hmask pL1098) 1 1097 (true, (init pL1098), (init pL1098))) 1098 549 false = true :=
  fin_run (runOK_init (prmOK_of_and L1098_fin) true) (by decide) rfl L1098_fin ptTest_fst
theorem H1098_fin : (prmOK pH1098 1098 && ptTest pH1098 (runFrom pH1098 (fmask pH1098) (cmask pH1098) (hmask pH1098) 1 1097 (true, (init pH1098), (init pH1098))) 1098 549 true) = true := by
  decide +kernel
theorem H1098_ok : RunOK pH1098 1098 (runFrom pH1098 (fmask pH1098) (cmask pH1098) (hmask pH1098) 1 1097 (true, (init pH1098), (init pH1098))) ∧ ptTest pH1098 (runFrom pH1098 (fmask pH1098) (cmask pH1098) (hmask pH1098) 1 1097 (true, (init pH1098), (init pH1098))) 1098 549 true = true :=
  fin_run (runOK_init (prmOK_of_and H1098_fin) true) (by decide) rfl H1098_fin ptTest_fst
theorem I1098_fin : (prmOK pI1098 1098 && intTest pI1098 (runFrom pI1098 (fmask pI1098) (cmask pI1098) (hmask pI1098) 1 1097 (true, (init pI1098), (init pI1098))) 1098 18 true) = true := by
  decide +kernel
theorem I1098_ok : RunOK pI1098 1098 (runFrom pI1098 (fmask pI1098) (cmask pI1098) (hmask pI1098) 1 1097 (true, (init pI1098), (init pI1098))) ∧ intTest pI1098 (runFrom pI1098 (fmask pI1098) (cmask pI1098) (hmask pI1098) 1 1097 (true, (init pI1098), (init pI1098))) 1098 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1098_fin) true) (by decide) rfl I1098_fin intTest_fst
theorem link1098 : linkOK pL1098 pH1098 pI1098 = true := by decide +kernel
theorem cvx1098 : ConvexBetweenHumps 1098 :=
  cvx_of L1098_ok H1098_ok I1098_ok link1098 (by decide)
theorem cenlink1098 : cenLinkOK pI1098 1098 = true := by decide +kernel
theorem cen1098 : CenterUniqueMin 1098 ∧ DipHyp 1098 ∧ OnePointHyps 1098 :=
  cen_of L1098_ok H1098_ok I1098_ok link1098 cenlink1098

/-! ### `N = 1099` -/

def pL1099 : Prm := ⟨78, 38, 37, 1101, 11, 18446744073709551616, 159998402635338530, 159998402635338530⟩
def pH1099 : Prm := ⟨78, 38, 37, 1101, 11, 18446744073709551616, 160000601658594082, 160000601658594082⟩
def pI1099 : Prm := ⟨65, 32, 30, 1101, 11, 18446744073709551616, 159998402635338530, 160000601658594082⟩
theorem L1099_fin : (prmOK pL1099 1099 && ptTest pL1099 (runFrom pL1099 (fmask pL1099) (cmask pL1099) (hmask pL1099) 1 1098 (true, (init pL1099), (init pL1099))) 1099 550 false) = true := by
  decide +kernel
theorem L1099_ok : RunOK pL1099 1099 (runFrom pL1099 (fmask pL1099) (cmask pL1099) (hmask pL1099) 1 1098 (true, (init pL1099), (init pL1099))) ∧ ptTest pL1099 (runFrom pL1099 (fmask pL1099) (cmask pL1099) (hmask pL1099) 1 1098 (true, (init pL1099), (init pL1099))) 1099 550 false = true :=
  fin_run (runOK_init (prmOK_of_and L1099_fin) true) (by decide) rfl L1099_fin ptTest_fst
theorem H1099_fin : (prmOK pH1099 1099 && ptTest pH1099 (runFrom pH1099 (fmask pH1099) (cmask pH1099) (hmask pH1099) 1 1098 (true, (init pH1099), (init pH1099))) 1099 550 true) = true := by
  decide +kernel
theorem H1099_ok : RunOK pH1099 1099 (runFrom pH1099 (fmask pH1099) (cmask pH1099) (hmask pH1099) 1 1098 (true, (init pH1099), (init pH1099))) ∧ ptTest pH1099 (runFrom pH1099 (fmask pH1099) (cmask pH1099) (hmask pH1099) 1 1098 (true, (init pH1099), (init pH1099))) 1099 550 true = true :=
  fin_run (runOK_init (prmOK_of_and H1099_fin) true) (by decide) rfl H1099_fin ptTest_fst
theorem I1099_fin : (prmOK pI1099 1099 && intTest pI1099 (runFrom pI1099 (fmask pI1099) (cmask pI1099) (hmask pI1099) 1 1098 (true, (init pI1099), (init pI1099))) 1099 18 false) = true := by
  decide +kernel
theorem I1099_ok : RunOK pI1099 1099 (runFrom pI1099 (fmask pI1099) (cmask pI1099) (hmask pI1099) 1 1098 (true, (init pI1099), (init pI1099))) ∧ intTest pI1099 (runFrom pI1099 (fmask pI1099) (cmask pI1099) (hmask pI1099) 1 1098 (true, (init pI1099), (init pI1099))) 1099 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1099_fin) true) (by decide) rfl I1099_fin intTest_fst
theorem link1099 : linkOK pL1099 pH1099 pI1099 = true := by decide +kernel
theorem cvx1099 : ConvexBetweenHumps 1099 :=
  cvx_of L1099_ok H1099_ok I1099_ok link1099 (by decide)

/-! ### `N = 1100` -/

def pL1100 : Prm := ⟨78, 38, 37, 1102, 11, 18446744073709551616, 159881756628358046, 159881756628358046⟩
def pH1100 : Prm := ⟨78, 38, 37, 1102, 11, 18446744073709551616, 159883955651613598, 159883955651613598⟩
def pI1100 : Prm := ⟨65, 32, 30, 1102, 11, 18446744073709551616, 159881756628358046, 159883955651613598⟩
theorem L1100_fin : (prmOK pL1100 1100 && ptTest pL1100 (runFrom pL1100 (fmask pL1100) (cmask pL1100) (hmask pL1100) 1 1099 (true, (init pL1100), (init pL1100))) 1100 550 false) = true := by
  decide +kernel
theorem L1100_ok : RunOK pL1100 1100 (runFrom pL1100 (fmask pL1100) (cmask pL1100) (hmask pL1100) 1 1099 (true, (init pL1100), (init pL1100))) ∧ ptTest pL1100 (runFrom pL1100 (fmask pL1100) (cmask pL1100) (hmask pL1100) 1 1099 (true, (init pL1100), (init pL1100))) 1100 550 false = true :=
  fin_run (runOK_init (prmOK_of_and L1100_fin) true) (by decide) rfl L1100_fin ptTest_fst
theorem H1100_fin : (prmOK pH1100 1100 && ptTest pH1100 (runFrom pH1100 (fmask pH1100) (cmask pH1100) (hmask pH1100) 1 1099 (true, (init pH1100), (init pH1100))) 1100 550 true) = true := by
  decide +kernel
theorem H1100_ok : RunOK pH1100 1100 (runFrom pH1100 (fmask pH1100) (cmask pH1100) (hmask pH1100) 1 1099 (true, (init pH1100), (init pH1100))) ∧ ptTest pH1100 (runFrom pH1100 (fmask pH1100) (cmask pH1100) (hmask pH1100) 1 1099 (true, (init pH1100), (init pH1100))) 1100 550 true = true :=
  fin_run (runOK_init (prmOK_of_and H1100_fin) true) (by decide) rfl H1100_fin ptTest_fst
theorem I1100_fin : (prmOK pI1100 1100 && intTest pI1100 (runFrom pI1100 (fmask pI1100) (cmask pI1100) (hmask pI1100) 1 1099 (true, (init pI1100), (init pI1100))) 1100 18 true) = true := by
  decide +kernel
theorem I1100_ok : RunOK pI1100 1100 (runFrom pI1100 (fmask pI1100) (cmask pI1100) (hmask pI1100) 1 1099 (true, (init pI1100), (init pI1100))) ∧ intTest pI1100 (runFrom pI1100 (fmask pI1100) (cmask pI1100) (hmask pI1100) 1 1099 (true, (init pI1100), (init pI1100))) 1100 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1100_fin) true) (by decide) rfl I1100_fin intTest_fst
theorem link1100 : linkOK pL1100 pH1100 pI1100 = true := by decide +kernel
theorem cvx1100 : ConvexBetweenHumps 1100 :=
  cvx_of L1100_ok H1100_ok I1100_ok link1100 (by decide)
theorem cenlink1100 : cenLinkOK pI1100 1100 = true := by decide +kernel
theorem cen1100 : CenterUniqueMin 1100 ∧ DipHyp 1100 ∧ OnePointHyps 1100 :=
  cen_of L1100_ok H1100_ok I1100_ok link1100 cenlink1100

/-! ### `N = 1101` -/

def pL1101 : Prm := ⟨78, 38, 37, 1103, 11, 18446744073709551616, 159765210070652555, 159765210070652555⟩
def pH1101 : Prm := ⟨76, 35, 38, 1103, 11, 18446744073709551616, 159767409093908107, 159767409093908107⟩
def pI1101 : Prm := ⟨65, 32, 30, 1103, 11, 18446744073709551616, 159765210070652555, 159767409093908107⟩
theorem L1101_fin : (prmOK pL1101 1101 && ptTest pL1101 (runFrom pL1101 (fmask pL1101) (cmask pL1101) (hmask pL1101) 1 1100 (true, (init pL1101), (init pL1101))) 1101 551 false) = true := by
  decide +kernel
theorem L1101_ok : RunOK pL1101 1101 (runFrom pL1101 (fmask pL1101) (cmask pL1101) (hmask pL1101) 1 1100 (true, (init pL1101), (init pL1101))) ∧ ptTest pL1101 (runFrom pL1101 (fmask pL1101) (cmask pL1101) (hmask pL1101) 1 1100 (true, (init pL1101), (init pL1101))) 1101 551 false = true :=
  fin_run (runOK_init (prmOK_of_and L1101_fin) true) (by decide) rfl L1101_fin ptTest_fst
theorem H1101_fin : (prmOK pH1101 1101 && ptTest pH1101 (runFrom pH1101 (fmask pH1101) (cmask pH1101) (hmask pH1101) 1 1100 (true, (init pH1101), (init pH1101))) 1101 551 true) = true := by
  decide +kernel
theorem H1101_ok : RunOK pH1101 1101 (runFrom pH1101 (fmask pH1101) (cmask pH1101) (hmask pH1101) 1 1100 (true, (init pH1101), (init pH1101))) ∧ ptTest pH1101 (runFrom pH1101 (fmask pH1101) (cmask pH1101) (hmask pH1101) 1 1100 (true, (init pH1101), (init pH1101))) 1101 551 true = true :=
  fin_run (runOK_init (prmOK_of_and H1101_fin) true) (by decide) rfl H1101_fin ptTest_fst
theorem I1101_fin : (prmOK pI1101 1101 && intTest pI1101 (runFrom pI1101 (fmask pI1101) (cmask pI1101) (hmask pI1101) 1 1100 (true, (init pI1101), (init pI1101))) 1101 18 false) = true := by
  decide +kernel
theorem I1101_ok : RunOK pI1101 1101 (runFrom pI1101 (fmask pI1101) (cmask pI1101) (hmask pI1101) 1 1100 (true, (init pI1101), (init pI1101))) ∧ intTest pI1101 (runFrom pI1101 (fmask pI1101) (cmask pI1101) (hmask pI1101) 1 1100 (true, (init pI1101), (init pI1101))) 1101 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1101_fin) true) (by decide) rfl I1101_fin intTest_fst
theorem link1101 : linkOK pL1101 pH1101 pI1101 = true := by decide +kernel
theorem cvx1101 : ConvexBetweenHumps 1101 :=
  cvx_of L1101_ok H1101_ok I1101_ok link1101 (by decide)

/-! ### `N = 1102` -/

def pL1102 : Prm := ⟨78, 38, 37, 1104, 11, 18446744073709551616, 159648935070786988, 159648935070786988⟩
def pH1102 : Prm := ⟨78, 38, 37, 1104, 11, 18446744073709551616, 159651134094042540, 159651134094042540⟩
def pI1102 : Prm := ⟨65, 32, 30, 1104, 11, 18446744073709551616, 159648935070786988, 159651134094042540⟩
theorem L1102_fin : (prmOK pL1102 1102 && ptTest pL1102 (runFrom pL1102 (fmask pL1102) (cmask pL1102) (hmask pL1102) 1 1101 (true, (init pL1102), (init pL1102))) 1102 551 false) = true := by
  decide +kernel
theorem L1102_ok : RunOK pL1102 1102 (runFrom pL1102 (fmask pL1102) (cmask pL1102) (hmask pL1102) 1 1101 (true, (init pL1102), (init pL1102))) ∧ ptTest pL1102 (runFrom pL1102 (fmask pL1102) (cmask pL1102) (hmask pL1102) 1 1101 (true, (init pL1102), (init pL1102))) 1102 551 false = true :=
  fin_run (runOK_init (prmOK_of_and L1102_fin) true) (by decide) rfl L1102_fin ptTest_fst
theorem H1102_fin : (prmOK pH1102 1102 && ptTest pH1102 (runFrom pH1102 (fmask pH1102) (cmask pH1102) (hmask pH1102) 1 1101 (true, (init pH1102), (init pH1102))) 1102 551 true) = true := by
  decide +kernel
theorem H1102_ok : RunOK pH1102 1102 (runFrom pH1102 (fmask pH1102) (cmask pH1102) (hmask pH1102) 1 1101 (true, (init pH1102), (init pH1102))) ∧ ptTest pH1102 (runFrom pH1102 (fmask pH1102) (cmask pH1102) (hmask pH1102) 1 1101 (true, (init pH1102), (init pH1102))) 1102 551 true = true :=
  fin_run (runOK_init (prmOK_of_and H1102_fin) true) (by decide) rfl H1102_fin ptTest_fst
theorem I1102_fin : (prmOK pI1102 1102 && intTest pI1102 (runFrom pI1102 (fmask pI1102) (cmask pI1102) (hmask pI1102) 1 1101 (true, (init pI1102), (init pI1102))) 1102 18 true) = true := by
  decide +kernel
theorem I1102_ok : RunOK pI1102 1102 (runFrom pI1102 (fmask pI1102) (cmask pI1102) (hmask pI1102) 1 1101 (true, (init pI1102), (init pI1102))) ∧ intTest pI1102 (runFrom pI1102 (fmask pI1102) (cmask pI1102) (hmask pI1102) 1 1101 (true, (init pI1102), (init pI1102))) 1102 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1102_fin) true) (by decide) rfl I1102_fin intTest_fst
theorem link1102 : linkOK pL1102 pH1102 pI1102 = true := by decide +kernel
theorem cvx1102 : ConvexBetweenHumps 1102 :=
  cvx_of L1102_ok H1102_ok I1102_ok link1102 (by decide)
theorem cenlink1102 : cenLinkOK pI1102 1102 = true := by decide +kernel
theorem cen1102 : CenterUniqueMin 1102 ∧ DipHyp 1102 ∧ OnePointHyps 1102 :=
  cen_of L1102_ok H1102_ok I1102_ok link1102 cenlink1102

/-! ### `N = 1103` -/

def pL1103 : Prm := ⟨78, 38, 37, 1105, 11, 18446744073709551616, 159532759082178476, 159532759082178476⟩
def pH1103 : Prm := ⟨78, 38, 37, 1105, 11, 18446744073709551616, 159534958105434028, 159534958105434028⟩
def pI1103 : Prm := ⟨65, 32, 30, 1105, 11, 18446744073709551616, 159532759082178476, 159534958105434028⟩
theorem L1103_fin : (prmOK pL1103 1103 && ptTest pL1103 (runFrom pL1103 (fmask pL1103) (cmask pL1103) (hmask pL1103) 1 1102 (true, (init pL1103), (init pL1103))) 1103 552 false) = true := by
  decide +kernel
theorem L1103_ok : RunOK pL1103 1103 (runFrom pL1103 (fmask pL1103) (cmask pL1103) (hmask pL1103) 1 1102 (true, (init pL1103), (init pL1103))) ∧ ptTest pL1103 (runFrom pL1103 (fmask pL1103) (cmask pL1103) (hmask pL1103) 1 1102 (true, (init pL1103), (init pL1103))) 1103 552 false = true :=
  fin_run (runOK_init (prmOK_of_and L1103_fin) true) (by decide) rfl L1103_fin ptTest_fst
theorem H1103_fin : (prmOK pH1103 1103 && ptTest pH1103 (runFrom pH1103 (fmask pH1103) (cmask pH1103) (hmask pH1103) 1 1102 (true, (init pH1103), (init pH1103))) 1103 552 true) = true := by
  decide +kernel
theorem H1103_ok : RunOK pH1103 1103 (runFrom pH1103 (fmask pH1103) (cmask pH1103) (hmask pH1103) 1 1102 (true, (init pH1103), (init pH1103))) ∧ ptTest pH1103 (runFrom pH1103 (fmask pH1103) (cmask pH1103) (hmask pH1103) 1 1102 (true, (init pH1103), (init pH1103))) 1103 552 true = true :=
  fin_run (runOK_init (prmOK_of_and H1103_fin) true) (by decide) rfl H1103_fin ptTest_fst
theorem I1103_fin : (prmOK pI1103 1103 && intTest pI1103 (runFrom pI1103 (fmask pI1103) (cmask pI1103) (hmask pI1103) 1 1102 (true, (init pI1103), (init pI1103))) 1103 18 false) = true := by
  decide +kernel
theorem I1103_ok : RunOK pI1103 1103 (runFrom pI1103 (fmask pI1103) (cmask pI1103) (hmask pI1103) 1 1102 (true, (init pI1103), (init pI1103))) ∧ intTest pI1103 (runFrom pI1103 (fmask pI1103) (cmask pI1103) (hmask pI1103) 1 1102 (true, (init pI1103), (init pI1103))) 1103 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1103_fin) true) (by decide) rfl I1103_fin intTest_fst
theorem link1103 : linkOK pL1103 pH1103 pI1103 = true := by decide +kernel
theorem cvx1103 : ConvexBetweenHumps 1103 :=
  cvx_of L1103_ok H1103_ok I1103_ok link1103 (by decide)

/-! ### `N = 1104` -/

def pL1104 : Prm := ⟨76, 35, 38, 1106, 11, 18446744073709551616, 159416853262536079, 159416853262536079⟩
def pH1104 : Prm := ⟨78, 38, 37, 1106, 11, 18446744073709551616, 159419052285791631, 159419052285791631⟩
def pI1104 : Prm := ⟨65, 32, 30, 1106, 11, 18446744073709551616, 159416853262536079, 159419052285791631⟩
theorem L1104_fin : (prmOK pL1104 1104 && ptTest pL1104 (runFrom pL1104 (fmask pL1104) (cmask pL1104) (hmask pL1104) 1 1103 (true, (init pL1104), (init pL1104))) 1104 552 false) = true := by
  decide +kernel
theorem L1104_ok : RunOK pL1104 1104 (runFrom pL1104 (fmask pL1104) (cmask pL1104) (hmask pL1104) 1 1103 (true, (init pL1104), (init pL1104))) ∧ ptTest pL1104 (runFrom pL1104 (fmask pL1104) (cmask pL1104) (hmask pL1104) 1 1103 (true, (init pL1104), (init pL1104))) 1104 552 false = true :=
  fin_run (runOK_init (prmOK_of_and L1104_fin) true) (by decide) rfl L1104_fin ptTest_fst
theorem H1104_fin : (prmOK pH1104 1104 && ptTest pH1104 (runFrom pH1104 (fmask pH1104) (cmask pH1104) (hmask pH1104) 1 1103 (true, (init pH1104), (init pH1104))) 1104 552 true) = true := by
  decide +kernel
theorem H1104_ok : RunOK pH1104 1104 (runFrom pH1104 (fmask pH1104) (cmask pH1104) (hmask pH1104) 1 1103 (true, (init pH1104), (init pH1104))) ∧ ptTest pH1104 (runFrom pH1104 (fmask pH1104) (cmask pH1104) (hmask pH1104) 1 1103 (true, (init pH1104), (init pH1104))) 1104 552 true = true :=
  fin_run (runOK_init (prmOK_of_and H1104_fin) true) (by decide) rfl H1104_fin ptTest_fst
theorem I1104_fin : (prmOK pI1104 1104 && intTest pI1104 (runFrom pI1104 (fmask pI1104) (cmask pI1104) (hmask pI1104) 1 1103 (true, (init pI1104), (init pI1104))) 1104 18 true) = true := by
  decide +kernel
theorem I1104_ok : RunOK pI1104 1104 (runFrom pI1104 (fmask pI1104) (cmask pI1104) (hmask pI1104) 1 1103 (true, (init pI1104), (init pI1104))) ∧ intTest pI1104 (runFrom pI1104 (fmask pI1104) (cmask pI1104) (hmask pI1104) 1 1103 (true, (init pI1104), (init pI1104))) 1104 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1104_fin) true) (by decide) rfl I1104_fin intTest_fst
theorem link1104 : linkOK pL1104 pH1104 pI1104 = true := by decide +kernel
theorem cvx1104 : ConvexBetweenHumps 1104 :=
  cvx_of L1104_ok H1104_ok I1104_ok link1104 (by decide)
theorem cenlink1104 : cenLinkOK pI1104 1104 = true := by decide +kernel
theorem cen1104 : CenterUniqueMin 1104 ∧ DipHyp 1104 ∧ OnePointHyps 1104 :=
  cen_of L1104_ok H1104_ok I1104_ok link1104 cenlink1104

/-! ### `N = 1105` -/

def pL1105 : Prm := ⟨78, 38, 37, 1107, 11, 18446744073709551616, 159301046018770684, 159301046018770684⟩
def pH1105 : Prm := ⟨78, 38, 37, 1107, 11, 18446744073709551616, 159303245042026236, 159303245042026236⟩
def pI1105 : Prm := ⟨65, 32, 30, 1107, 11, 18446744073709551616, 159301046018770684, 159303245042026236⟩
theorem L1105_fin : (prmOK pL1105 1105 && ptTest pL1105 (runFrom pL1105 (fmask pL1105) (cmask pL1105) (hmask pL1105) 1 1104 (true, (init pL1105), (init pL1105))) 1105 553 false) = true := by
  decide +kernel
theorem L1105_ok : RunOK pL1105 1105 (runFrom pL1105 (fmask pL1105) (cmask pL1105) (hmask pL1105) 1 1104 (true, (init pL1105), (init pL1105))) ∧ ptTest pL1105 (runFrom pL1105 (fmask pL1105) (cmask pL1105) (hmask pL1105) 1 1104 (true, (init pL1105), (init pL1105))) 1105 553 false = true :=
  fin_run (runOK_init (prmOK_of_and L1105_fin) true) (by decide) rfl L1105_fin ptTest_fst
theorem H1105_fin : (prmOK pH1105 1105 && ptTest pH1105 (runFrom pH1105 (fmask pH1105) (cmask pH1105) (hmask pH1105) 1 1104 (true, (init pH1105), (init pH1105))) 1105 553 true) = true := by
  decide +kernel
theorem H1105_ok : RunOK pH1105 1105 (runFrom pH1105 (fmask pH1105) (cmask pH1105) (hmask pH1105) 1 1104 (true, (init pH1105), (init pH1105))) ∧ ptTest pH1105 (runFrom pH1105 (fmask pH1105) (cmask pH1105) (hmask pH1105) 1 1104 (true, (init pH1105), (init pH1105))) 1105 553 true = true :=
  fin_run (runOK_init (prmOK_of_and H1105_fin) true) (by decide) rfl H1105_fin ptTest_fst
theorem I1105_fin : (prmOK pI1105 1105 && intTest pI1105 (runFrom pI1105 (fmask pI1105) (cmask pI1105) (hmask pI1105) 1 1104 (true, (init pI1105), (init pI1105))) 1105 18 false) = true := by
  decide +kernel
theorem I1105_ok : RunOK pI1105 1105 (runFrom pI1105 (fmask pI1105) (cmask pI1105) (hmask pI1105) 1 1104 (true, (init pI1105), (init pI1105))) ∧ intTest pI1105 (runFrom pI1105 (fmask pI1105) (cmask pI1105) (hmask pI1105) 1 1104 (true, (init pI1105), (init pI1105))) 1105 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1105_fin) true) (by decide) rfl I1105_fin intTest_fst
theorem link1105 : linkOK pL1105 pH1105 pI1105 = true := by decide +kernel
theorem cvx1105 : ConvexBetweenHumps 1105 :=
  cvx_of L1105_ok H1105_ok I1105_ok link1105 (by decide)

/-! ### `N = 1106` -/

def pL1106 : Prm := ⟨78, 38, 37, 1108, 11, 18446744073709551616, 159185507564653008, 159185507564653008⟩
def pH1106 : Prm := ⟨76, 35, 38, 1108, 11, 18446744073709551616, 159187706587908560, 159187706587908560⟩
def pI1106 : Prm := ⟨65, 32, 30, 1108, 11, 18446744073709551616, 159185507564653008, 159187706587908560⟩
theorem L1106_fin : (prmOK pL1106 1106 && ptTest pL1106 (runFrom pL1106 (fmask pL1106) (cmask pL1106) (hmask pL1106) 1 1105 (true, (init pL1106), (init pL1106))) 1106 553 false) = true := by
  decide +kernel
theorem L1106_ok : RunOK pL1106 1106 (runFrom pL1106 (fmask pL1106) (cmask pL1106) (hmask pL1106) 1 1105 (true, (init pL1106), (init pL1106))) ∧ ptTest pL1106 (runFrom pL1106 (fmask pL1106) (cmask pL1106) (hmask pL1106) 1 1105 (true, (init pL1106), (init pL1106))) 1106 553 false = true :=
  fin_run (runOK_init (prmOK_of_and L1106_fin) true) (by decide) rfl L1106_fin ptTest_fst
theorem H1106_fin : (prmOK pH1106 1106 && ptTest pH1106 (runFrom pH1106 (fmask pH1106) (cmask pH1106) (hmask pH1106) 1 1105 (true, (init pH1106), (init pH1106))) 1106 553 true) = true := by
  decide +kernel
theorem H1106_ok : RunOK pH1106 1106 (runFrom pH1106 (fmask pH1106) (cmask pH1106) (hmask pH1106) 1 1105 (true, (init pH1106), (init pH1106))) ∧ ptTest pH1106 (runFrom pH1106 (fmask pH1106) (cmask pH1106) (hmask pH1106) 1 1105 (true, (init pH1106), (init pH1106))) 1106 553 true = true :=
  fin_run (runOK_init (prmOK_of_and H1106_fin) true) (by decide) rfl H1106_fin ptTest_fst
theorem I1106_fin : (prmOK pI1106 1106 && intTest pI1106 (runFrom pI1106 (fmask pI1106) (cmask pI1106) (hmask pI1106) 1 1105 (true, (init pI1106), (init pI1106))) 1106 18 true) = true := by
  decide +kernel
theorem I1106_ok : RunOK pI1106 1106 (runFrom pI1106 (fmask pI1106) (cmask pI1106) (hmask pI1106) 1 1105 (true, (init pI1106), (init pI1106))) ∧ intTest pI1106 (runFrom pI1106 (fmask pI1106) (cmask pI1106) (hmask pI1106) 1 1105 (true, (init pI1106), (init pI1106))) 1106 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1106_fin) true) (by decide) rfl I1106_fin intTest_fst
theorem link1106 : linkOK pL1106 pH1106 pI1106 = true := by decide +kernel
theorem cvx1106 : ConvexBetweenHumps 1106 :=
  cvx_of L1106_ok H1106_ok I1106_ok link1106 (by decide)
theorem cenlink1106 : cenLinkOK pI1106 1106 = true := by decide +kernel
theorem cen1106 : CenterUniqueMin 1106 ∧ DipHyp 1106 ∧ OnePointHyps 1106 :=
  cen_of L1106_ok H1106_ok I1106_ok link1106 cenlink1106

/-! ### `N = 1107` -/

def pL1107 : Prm := ⟨78, 38, 37, 1109, 11, 18446744073709551616, 159070067253633273, 159070067253633273⟩
def pH1107 : Prm := ⟨76, 35, 38, 1109, 11, 18446744073709551616, 159072266276888825, 159072266276888825⟩
def pI1107 : Prm := ⟨65, 32, 30, 1109, 11, 18446744073709551616, 159070067253633273, 159072266276888825⟩
theorem L1107_fin : (prmOK pL1107 1107 && ptTest pL1107 (runFrom pL1107 (fmask pL1107) (cmask pL1107) (hmask pL1107) 1 1106 (true, (init pL1107), (init pL1107))) 1107 554 false) = true := by
  decide +kernel
theorem L1107_ok : RunOK pL1107 1107 (runFrom pL1107 (fmask pL1107) (cmask pL1107) (hmask pL1107) 1 1106 (true, (init pL1107), (init pL1107))) ∧ ptTest pL1107 (runFrom pL1107 (fmask pL1107) (cmask pL1107) (hmask pL1107) 1 1106 (true, (init pL1107), (init pL1107))) 1107 554 false = true :=
  fin_run (runOK_init (prmOK_of_and L1107_fin) true) (by decide) rfl L1107_fin ptTest_fst
theorem H1107_fin : (prmOK pH1107 1107 && ptTest pH1107 (runFrom pH1107 (fmask pH1107) (cmask pH1107) (hmask pH1107) 1 1106 (true, (init pH1107), (init pH1107))) 1107 554 true) = true := by
  decide +kernel
theorem H1107_ok : RunOK pH1107 1107 (runFrom pH1107 (fmask pH1107) (cmask pH1107) (hmask pH1107) 1 1106 (true, (init pH1107), (init pH1107))) ∧ ptTest pH1107 (runFrom pH1107 (fmask pH1107) (cmask pH1107) (hmask pH1107) 1 1106 (true, (init pH1107), (init pH1107))) 1107 554 true = true :=
  fin_run (runOK_init (prmOK_of_and H1107_fin) true) (by decide) rfl H1107_fin ptTest_fst
theorem I1107_fin : (prmOK pI1107 1107 && intTest pI1107 (runFrom pI1107 (fmask pI1107) (cmask pI1107) (hmask pI1107) 1 1106 (true, (init pI1107), (init pI1107))) 1107 18 false) = true := by
  decide +kernel
theorem I1107_ok : RunOK pI1107 1107 (runFrom pI1107 (fmask pI1107) (cmask pI1107) (hmask pI1107) 1 1106 (true, (init pI1107), (init pI1107))) ∧ intTest pI1107 (runFrom pI1107 (fmask pI1107) (cmask pI1107) (hmask pI1107) 1 1106 (true, (init pI1107), (init pI1107))) 1107 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1107_fin) true) (by decide) rfl I1107_fin intTest_fst
theorem link1107 : linkOK pL1107 pH1107 pI1107 = true := by decide +kernel
theorem cvx1107 : ConvexBetweenHumps 1107 :=
  cvx_of L1107_ok H1107_ok I1107_ok link1107 (by decide)

/-! ### `N = 1108` -/

def pL1108 : Prm := ⟨76, 35, 38, 1110, 11, 18446744073709551616, 158954894362442935, 158954894362442935⟩
def pH1108 : Prm := ⟨76, 35, 38, 1110, 11, 18446744073709551616, 158957093385698487, 158957093385698487⟩
def pI1108 : Prm := ⟨65, 32, 30, 1110, 11, 18446744073709551616, 158954894362442935, 158957093385698487⟩
theorem L1108_fin : (prmOK pL1108 1108 && ptTest pL1108 (runFrom pL1108 (fmask pL1108) (cmask pL1108) (hmask pL1108) 1 1107 (true, (init pL1108), (init pL1108))) 1108 554 false) = true := by
  decide +kernel
theorem L1108_ok : RunOK pL1108 1108 (runFrom pL1108 (fmask pL1108) (cmask pL1108) (hmask pL1108) 1 1107 (true, (init pL1108), (init pL1108))) ∧ ptTest pL1108 (runFrom pL1108 (fmask pL1108) (cmask pL1108) (hmask pL1108) 1 1107 (true, (init pL1108), (init pL1108))) 1108 554 false = true :=
  fin_run (runOK_init (prmOK_of_and L1108_fin) true) (by decide) rfl L1108_fin ptTest_fst
theorem H1108_fin : (prmOK pH1108 1108 && ptTest pH1108 (runFrom pH1108 (fmask pH1108) (cmask pH1108) (hmask pH1108) 1 1107 (true, (init pH1108), (init pH1108))) 1108 554 true) = true := by
  decide +kernel
theorem H1108_ok : RunOK pH1108 1108 (runFrom pH1108 (fmask pH1108) (cmask pH1108) (hmask pH1108) 1 1107 (true, (init pH1108), (init pH1108))) ∧ ptTest pH1108 (runFrom pH1108 (fmask pH1108) (cmask pH1108) (hmask pH1108) 1 1107 (true, (init pH1108), (init pH1108))) 1108 554 true = true :=
  fin_run (runOK_init (prmOK_of_and H1108_fin) true) (by decide) rfl H1108_fin ptTest_fst
theorem I1108_fin : (prmOK pI1108 1108 && intTest pI1108 (runFrom pI1108 (fmask pI1108) (cmask pI1108) (hmask pI1108) 1 1107 (true, (init pI1108), (init pI1108))) 1108 18 true) = true := by
  decide +kernel
theorem I1108_ok : RunOK pI1108 1108 (runFrom pI1108 (fmask pI1108) (cmask pI1108) (hmask pI1108) 1 1107 (true, (init pI1108), (init pI1108))) ∧ intTest pI1108 (runFrom pI1108 (fmask pI1108) (cmask pI1108) (hmask pI1108) 1 1107 (true, (init pI1108), (init pI1108))) 1108 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1108_fin) true) (by decide) rfl I1108_fin intTest_fst
theorem link1108 : linkOK pL1108 pH1108 pI1108 = true := by decide +kernel
theorem cvx1108 : ConvexBetweenHumps 1108 :=
  cvx_of L1108_ok H1108_ok I1108_ok link1108 (by decide)
theorem cenlink1108 : cenLinkOK pI1108 1108 = true := by decide +kernel
theorem cen1108 : CenterUniqueMin 1108 ∧ DipHyp 1108 ∧ OnePointHyps 1108 :=
  cen_of L1108_ok H1108_ok I1108_ok link1108 cenlink1108

/-! ### `N = 1109` -/

def pL1109 : Prm := ⟨78, 38, 37, 1111, 11, 18446744073709551616, 158839819184135572, 158839819184135572⟩
def pH1109 : Prm := ⟨76, 35, 38, 1111, 11, 18446744073709551616, 158842018207391124, 158842018207391124⟩
def pI1109 : Prm := ⟨65, 32, 30, 1111, 11, 18446744073709551616, 158839819184135572, 158842018207391124⟩
theorem L1109_fin : (prmOK pL1109 1109 && ptTest pL1109 (runFrom pL1109 (fmask pL1109) (cmask pL1109) (hmask pL1109) 1 1108 (true, (init pL1109), (init pL1109))) 1109 555 false) = true := by
  decide +kernel
theorem L1109_ok : RunOK pL1109 1109 (runFrom pL1109 (fmask pL1109) (cmask pL1109) (hmask pL1109) 1 1108 (true, (init pL1109), (init pL1109))) ∧ ptTest pL1109 (runFrom pL1109 (fmask pL1109) (cmask pL1109) (hmask pL1109) 1 1108 (true, (init pL1109), (init pL1109))) 1109 555 false = true :=
  fin_run (runOK_init (prmOK_of_and L1109_fin) true) (by decide) rfl L1109_fin ptTest_fst
theorem H1109_fin : (prmOK pH1109 1109 && ptTest pH1109 (runFrom pH1109 (fmask pH1109) (cmask pH1109) (hmask pH1109) 1 1108 (true, (init pH1109), (init pH1109))) 1109 555 true) = true := by
  decide +kernel
theorem H1109_ok : RunOK pH1109 1109 (runFrom pH1109 (fmask pH1109) (cmask pH1109) (hmask pH1109) 1 1108 (true, (init pH1109), (init pH1109))) ∧ ptTest pH1109 (runFrom pH1109 (fmask pH1109) (cmask pH1109) (hmask pH1109) 1 1108 (true, (init pH1109), (init pH1109))) 1109 555 true = true :=
  fin_run (runOK_init (prmOK_of_and H1109_fin) true) (by decide) rfl H1109_fin ptTest_fst
theorem I1109_fin : (prmOK pI1109 1109 && intTest pI1109 (runFrom pI1109 (fmask pI1109) (cmask pI1109) (hmask pI1109) 1 1108 (true, (init pI1109), (init pI1109))) 1109 18 false) = true := by
  decide +kernel
theorem I1109_ok : RunOK pI1109 1109 (runFrom pI1109 (fmask pI1109) (cmask pI1109) (hmask pI1109) 1 1108 (true, (init pI1109), (init pI1109))) ∧ intTest pI1109 (runFrom pI1109 (fmask pI1109) (cmask pI1109) (hmask pI1109) 1 1108 (true, (init pI1109), (init pI1109))) 1109 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1109_fin) true) (by decide) rfl I1109_fin intTest_fst
theorem link1109 : linkOK pL1109 pH1109 pI1109 = true := by decide +kernel
theorem cvx1109 : ConvexBetweenHumps 1109 :=
  cvx_of L1109_ok H1109_ok I1109_ok link1109 (by decide)

/-! ### `N = 1110` -/

def pL1110 : Prm := ⟨76, 35, 38, 1112, 11, 18446744073709551616, 158725010065265573, 158725010065265573⟩
def pH1110 : Prm := ⟨76, 35, 38, 1112, 11, 18446744073709551616, 158727209088521125, 158727209088521125⟩
def pI1110 : Prm := ⟨65, 32, 30, 1112, 11, 18446744073709551616, 158725010065265573, 158727209088521125⟩
theorem L1110_fin : (prmOK pL1110 1110 && ptTest pL1110 (runFrom pL1110 (fmask pL1110) (cmask pL1110) (hmask pL1110) 1 1109 (true, (init pL1110), (init pL1110))) 1110 555 false) = true := by
  decide +kernel
theorem L1110_ok : RunOK pL1110 1110 (runFrom pL1110 (fmask pL1110) (cmask pL1110) (hmask pL1110) 1 1109 (true, (init pL1110), (init pL1110))) ∧ ptTest pL1110 (runFrom pL1110 (fmask pL1110) (cmask pL1110) (hmask pL1110) 1 1109 (true, (init pL1110), (init pL1110))) 1110 555 false = true :=
  fin_run (runOK_init (prmOK_of_and L1110_fin) true) (by decide) rfl L1110_fin ptTest_fst
theorem H1110_fin : (prmOK pH1110 1110 && ptTest pH1110 (runFrom pH1110 (fmask pH1110) (cmask pH1110) (hmask pH1110) 1 1109 (true, (init pH1110), (init pH1110))) 1110 555 true) = true := by
  decide +kernel
theorem H1110_ok : RunOK pH1110 1110 (runFrom pH1110 (fmask pH1110) (cmask pH1110) (hmask pH1110) 1 1109 (true, (init pH1110), (init pH1110))) ∧ ptTest pH1110 (runFrom pH1110 (fmask pH1110) (cmask pH1110) (hmask pH1110) 1 1109 (true, (init pH1110), (init pH1110))) 1110 555 true = true :=
  fin_run (runOK_init (prmOK_of_and H1110_fin) true) (by decide) rfl H1110_fin ptTest_fst
theorem I1110_fin : (prmOK pI1110 1110 && intTest pI1110 (runFrom pI1110 (fmask pI1110) (cmask pI1110) (hmask pI1110) 1 1109 (true, (init pI1110), (init pI1110))) 1110 18 true) = true := by
  decide +kernel
theorem I1110_ok : RunOK pI1110 1110 (runFrom pI1110 (fmask pI1110) (cmask pI1110) (hmask pI1110) 1 1109 (true, (init pI1110), (init pI1110))) ∧ intTest pI1110 (runFrom pI1110 (fmask pI1110) (cmask pI1110) (hmask pI1110) 1 1109 (true, (init pI1110), (init pI1110))) 1110 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1110_fin) true) (by decide) rfl I1110_fin intTest_fst
theorem link1110 : linkOK pL1110 pH1110 pI1110 = true := by decide +kernel
theorem cvx1110 : ConvexBetweenHumps 1110 :=
  cvx_of L1110_ok H1110_ok I1110_ok link1110 (by decide)
theorem cenlink1110 : cenLinkOK pI1110 1110 = true := by decide +kernel
theorem cen1110 : CenterUniqueMin 1110 ∧ DipHyp 1110 ∧ OnePointHyps 1110 :=
  cen_of L1110_ok H1110_ok I1110_ok link1110 cenlink1110

/-! ### `N = 1111` -/

def pL1111 : Prm := ⟨76, 35, 38, 1113, 11, 18446744073709551616, 158610298231590785, 158610298231590785⟩
def pH1111 : Prm := ⟨76, 35, 38, 1113, 11, 18446744073709551616, 158612497254846337, 158612497254846337⟩
def pI1111 : Prm := ⟨65, 32, 30, 1113, 11, 18446744073709551616, 158610298231590785, 158612497254846337⟩
theorem L1111_fin : (prmOK pL1111 1111 && ptTest pL1111 (runFrom pL1111 (fmask pL1111) (cmask pL1111) (hmask pL1111) 1 1110 (true, (init pL1111), (init pL1111))) 1111 556 false) = true := by
  decide +kernel
theorem L1111_ok : RunOK pL1111 1111 (runFrom pL1111 (fmask pL1111) (cmask pL1111) (hmask pL1111) 1 1110 (true, (init pL1111), (init pL1111))) ∧ ptTest pL1111 (runFrom pL1111 (fmask pL1111) (cmask pL1111) (hmask pL1111) 1 1110 (true, (init pL1111), (init pL1111))) 1111 556 false = true :=
  fin_run (runOK_init (prmOK_of_and L1111_fin) true) (by decide) rfl L1111_fin ptTest_fst
theorem H1111_fin : (prmOK pH1111 1111 && ptTest pH1111 (runFrom pH1111 (fmask pH1111) (cmask pH1111) (hmask pH1111) 1 1110 (true, (init pH1111), (init pH1111))) 1111 556 true) = true := by
  decide +kernel
theorem H1111_ok : RunOK pH1111 1111 (runFrom pH1111 (fmask pH1111) (cmask pH1111) (hmask pH1111) 1 1110 (true, (init pH1111), (init pH1111))) ∧ ptTest pH1111 (runFrom pH1111 (fmask pH1111) (cmask pH1111) (hmask pH1111) 1 1110 (true, (init pH1111), (init pH1111))) 1111 556 true = true :=
  fin_run (runOK_init (prmOK_of_and H1111_fin) true) (by decide) rfl H1111_fin ptTest_fst
theorem I1111_fin : (prmOK pI1111 1111 && intTest pI1111 (runFrom pI1111 (fmask pI1111) (cmask pI1111) (hmask pI1111) 1 1110 (true, (init pI1111), (init pI1111))) 1111 18 false) = true := by
  decide +kernel
theorem I1111_ok : RunOK pI1111 1111 (runFrom pI1111 (fmask pI1111) (cmask pI1111) (hmask pI1111) 1 1110 (true, (init pI1111), (init pI1111))) ∧ intTest pI1111 (runFrom pI1111 (fmask pI1111) (cmask pI1111) (hmask pI1111) 1 1110 (true, (init pI1111), (init pI1111))) 1111 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1111_fin) true) (by decide) rfl I1111_fin intTest_fst
theorem link1111 : linkOK pL1111 pH1111 pI1111 = true := by decide +kernel
theorem cvx1111 : ConvexBetweenHumps 1111 :=
  cvx_of L1111_ok H1111_ok I1111_ok link1111 (by decide)

/-! ### `N = 1112` -/

def pL1112 : Prm := ⟨78, 38, 37, 1114, 11, 18446744073709551616, 158495851106295380, 158495851106295380⟩
def pH1112 : Prm := ⟨76, 35, 38, 1114, 11, 18446744073709551616, 158498050129550932, 158498050129550932⟩
def pI1112 : Prm := ⟨65, 32, 30, 1114, 11, 18446744073709551616, 158495851106295380, 158498050129550932⟩
theorem L1112_fin : (prmOK pL1112 1112 && ptTest pL1112 (runFrom pL1112 (fmask pL1112) (cmask pL1112) (hmask pL1112) 1 1111 (true, (init pL1112), (init pL1112))) 1112 556 false) = true := by
  decide +kernel
theorem L1112_ok : RunOK pL1112 1112 (runFrom pL1112 (fmask pL1112) (cmask pL1112) (hmask pL1112) 1 1111 (true, (init pL1112), (init pL1112))) ∧ ptTest pL1112 (runFrom pL1112 (fmask pL1112) (cmask pL1112) (hmask pL1112) 1 1111 (true, (init pL1112), (init pL1112))) 1112 556 false = true :=
  fin_run (runOK_init (prmOK_of_and L1112_fin) true) (by decide) rfl L1112_fin ptTest_fst
theorem H1112_fin : (prmOK pH1112 1112 && ptTest pH1112 (runFrom pH1112 (fmask pH1112) (cmask pH1112) (hmask pH1112) 1 1111 (true, (init pH1112), (init pH1112))) 1112 556 true) = true := by
  decide +kernel
theorem H1112_ok : RunOK pH1112 1112 (runFrom pH1112 (fmask pH1112) (cmask pH1112) (hmask pH1112) 1 1111 (true, (init pH1112), (init pH1112))) ∧ ptTest pH1112 (runFrom pH1112 (fmask pH1112) (cmask pH1112) (hmask pH1112) 1 1111 (true, (init pH1112), (init pH1112))) 1112 556 true = true :=
  fin_run (runOK_init (prmOK_of_and H1112_fin) true) (by decide) rfl H1112_fin ptTest_fst
theorem I1112_fin : (prmOK pI1112 1112 && intTest pI1112 (runFrom pI1112 (fmask pI1112) (cmask pI1112) (hmask pI1112) 1 1111 (true, (init pI1112), (init pI1112))) 1112 18 true) = true := by
  decide +kernel
theorem I1112_ok : RunOK pI1112 1112 (runFrom pI1112 (fmask pI1112) (cmask pI1112) (hmask pI1112) 1 1111 (true, (init pI1112), (init pI1112))) ∧ intTest pI1112 (runFrom pI1112 (fmask pI1112) (cmask pI1112) (hmask pI1112) 1 1111 (true, (init pI1112), (init pI1112))) 1112 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1112_fin) true) (by decide) rfl I1112_fin intTest_fst
theorem link1112 : linkOK pL1112 pH1112 pI1112 = true := by decide +kernel
theorem cvx1112 : ConvexBetweenHumps 1112 :=
  cvx_of L1112_ok H1112_ok I1112_ok link1112 (by decide)
theorem cenlink1112 : cenLinkOK pI1112 1112 = true := by decide +kernel
theorem cen1112 : CenterUniqueMin 1112 ∧ DipHyp 1112 ∧ OnePointHyps 1112 :=
  cen_of L1112_ok H1112_ok I1112_ok link1112 cenlink1112

/-! ### `N = 1113` -/

def pL1113 : Prm := ⟨76, 35, 38, 1115, 11, 18446744073709551616, 158381500841089969, 158381500841089969⟩
def pH1113 : Prm := ⟨78, 38, 37, 1115, 11, 18446744073709551616, 158383699864345521, 158383699864345521⟩
def pI1113 : Prm := ⟨65, 32, 30, 1115, 11, 18446744073709551616, 158381500841089969, 158383699864345521⟩
theorem L1113_fin : (prmOK pL1113 1113 && ptTest pL1113 (runFrom pL1113 (fmask pL1113) (cmask pL1113) (hmask pL1113) 1 1112 (true, (init pL1113), (init pL1113))) 1113 557 false) = true := by
  decide +kernel
theorem L1113_ok : RunOK pL1113 1113 (runFrom pL1113 (fmask pL1113) (cmask pL1113) (hmask pL1113) 1 1112 (true, (init pL1113), (init pL1113))) ∧ ptTest pL1113 (runFrom pL1113 (fmask pL1113) (cmask pL1113) (hmask pL1113) 1 1112 (true, (init pL1113), (init pL1113))) 1113 557 false = true :=
  fin_run (runOK_init (prmOK_of_and L1113_fin) true) (by decide) rfl L1113_fin ptTest_fst
theorem H1113_fin : (prmOK pH1113 1113 && ptTest pH1113 (runFrom pH1113 (fmask pH1113) (cmask pH1113) (hmask pH1113) 1 1112 (true, (init pH1113), (init pH1113))) 1113 557 true) = true := by
  decide +kernel
theorem H1113_ok : RunOK pH1113 1113 (runFrom pH1113 (fmask pH1113) (cmask pH1113) (hmask pH1113) 1 1112 (true, (init pH1113), (init pH1113))) ∧ ptTest pH1113 (runFrom pH1113 (fmask pH1113) (cmask pH1113) (hmask pH1113) 1 1112 (true, (init pH1113), (init pH1113))) 1113 557 true = true :=
  fin_run (runOK_init (prmOK_of_and H1113_fin) true) (by decide) rfl H1113_fin ptTest_fst
theorem I1113_fin : (prmOK pI1113 1113 && intTest pI1113 (runFrom pI1113 (fmask pI1113) (cmask pI1113) (hmask pI1113) 1 1112 (true, (init pI1113), (init pI1113))) 1113 18 false) = true := by
  decide +kernel
theorem I1113_ok : RunOK pI1113 1113 (runFrom pI1113 (fmask pI1113) (cmask pI1113) (hmask pI1113) 1 1112 (true, (init pI1113), (init pI1113))) ∧ intTest pI1113 (runFrom pI1113 (fmask pI1113) (cmask pI1113) (hmask pI1113) 1 1112 (true, (init pI1113), (init pI1113))) 1113 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1113_fin) true) (by decide) rfl I1113_fin intTest_fst
theorem link1113 : linkOK pL1113 pH1113 pI1113 = true := by decide +kernel
theorem cvx1113 : ConvexBetweenHumps 1113 :=
  cvx_of L1113_ok H1113_ok I1113_ok link1113 (by decide)

/-! ### `N = 1114` -/

def pL1114 : Prm := ⟨78, 38, 37, 1116, 11, 18446744073709551616, 158267413942429328, 158267413942429328⟩
def pH1114 : Prm := ⟨76, 35, 38, 1116, 11, 18446744073709551616, 158269612965684880, 158269612965684880⟩
def pI1114 : Prm := ⟨65, 32, 30, 1116, 11, 18446744073709551616, 158267413942429328, 158269612965684880⟩
theorem L1114_fin : (prmOK pL1114 1114 && ptTest pL1114 (runFrom pL1114 (fmask pL1114) (cmask pL1114) (hmask pL1114) 1 1113 (true, (init pL1114), (init pL1114))) 1114 557 false) = true := by
  decide +kernel
theorem L1114_ok : RunOK pL1114 1114 (runFrom pL1114 (fmask pL1114) (cmask pL1114) (hmask pL1114) 1 1113 (true, (init pL1114), (init pL1114))) ∧ ptTest pL1114 (runFrom pL1114 (fmask pL1114) (cmask pL1114) (hmask pL1114) 1 1113 (true, (init pL1114), (init pL1114))) 1114 557 false = true :=
  fin_run (runOK_init (prmOK_of_and L1114_fin) true) (by decide) rfl L1114_fin ptTest_fst
theorem H1114_fin : (prmOK pH1114 1114 && ptTest pH1114 (runFrom pH1114 (fmask pH1114) (cmask pH1114) (hmask pH1114) 1 1113 (true, (init pH1114), (init pH1114))) 1114 557 true) = true := by
  decide +kernel
theorem H1114_ok : RunOK pH1114 1114 (runFrom pH1114 (fmask pH1114) (cmask pH1114) (hmask pH1114) 1 1113 (true, (init pH1114), (init pH1114))) ∧ ptTest pH1114 (runFrom pH1114 (fmask pH1114) (cmask pH1114) (hmask pH1114) 1 1113 (true, (init pH1114), (init pH1114))) 1114 557 true = true :=
  fin_run (runOK_init (prmOK_of_and H1114_fin) true) (by decide) rfl H1114_fin ptTest_fst
theorem I1114_fin : (prmOK pI1114 1114 && intTest pI1114 (runFrom pI1114 (fmask pI1114) (cmask pI1114) (hmask pI1114) 1 1113 (true, (init pI1114), (init pI1114))) 1114 18 true) = true := by
  decide +kernel
theorem I1114_ok : RunOK pI1114 1114 (runFrom pI1114 (fmask pI1114) (cmask pI1114) (hmask pI1114) 1 1113 (true, (init pI1114), (init pI1114))) ∧ intTest pI1114 (runFrom pI1114 (fmask pI1114) (cmask pI1114) (hmask pI1114) 1 1113 (true, (init pI1114), (init pI1114))) 1114 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1114_fin) true) (by decide) rfl I1114_fin intTest_fst
theorem link1114 : linkOK pL1114 pH1114 pI1114 = true := by decide +kernel
theorem cvx1114 : ConvexBetweenHumps 1114 :=
  cvx_of L1114_ok H1114_ok I1114_ok link1114 (by decide)
theorem cenlink1114 : cenLinkOK pI1114 1114 = true := by decide +kernel
theorem cen1114 : CenterUniqueMin 1114 ∧ DipHyp 1114 ∧ OnePointHyps 1114 :=
  cen_of L1114_ok H1114_ok I1114_ok link1114 cenlink1114

/-! ### `N = 1115` -/

def pL1115 : Prm := ⟨76, 35, 38, 1117, 11, 18446744073709551616, 158153423481243776, 158153423481243776⟩
def pH1115 : Prm := ⟨76, 35, 38, 1117, 11, 18446744073709551616, 158155622504499328, 158155622504499328⟩
def pI1115 : Prm := ⟨65, 32, 30, 1117, 11, 18446744073709551616, 158153423481243776, 158155622504499328⟩
theorem L1115_fin : (prmOK pL1115 1115 && ptTest pL1115 (runFrom pL1115 (fmask pL1115) (cmask pL1115) (hmask pL1115) 1 1114 (true, (init pL1115), (init pL1115))) 1115 558 false) = true := by
  decide +kernel
theorem L1115_ok : RunOK pL1115 1115 (runFrom pL1115 (fmask pL1115) (cmask pL1115) (hmask pL1115) 1 1114 (true, (init pL1115), (init pL1115))) ∧ ptTest pL1115 (runFrom pL1115 (fmask pL1115) (cmask pL1115) (hmask pL1115) 1 1114 (true, (init pL1115), (init pL1115))) 1115 558 false = true :=
  fin_run (runOK_init (prmOK_of_and L1115_fin) true) (by decide) rfl L1115_fin ptTest_fst
theorem H1115_fin : (prmOK pH1115 1115 && ptTest pH1115 (runFrom pH1115 (fmask pH1115) (cmask pH1115) (hmask pH1115) 1 1114 (true, (init pH1115), (init pH1115))) 1115 558 true) = true := by
  decide +kernel
theorem H1115_ok : RunOK pH1115 1115 (runFrom pH1115 (fmask pH1115) (cmask pH1115) (hmask pH1115) 1 1114 (true, (init pH1115), (init pH1115))) ∧ ptTest pH1115 (runFrom pH1115 (fmask pH1115) (cmask pH1115) (hmask pH1115) 1 1114 (true, (init pH1115), (init pH1115))) 1115 558 true = true :=
  fin_run (runOK_init (prmOK_of_and H1115_fin) true) (by decide) rfl H1115_fin ptTest_fst
theorem I1115_fin : (prmOK pI1115 1115 && intTest pI1115 (runFrom pI1115 (fmask pI1115) (cmask pI1115) (hmask pI1115) 1 1114 (true, (init pI1115), (init pI1115))) 1115 18 false) = true := by
  decide +kernel
theorem I1115_ok : RunOK pI1115 1115 (runFrom pI1115 (fmask pI1115) (cmask pI1115) (hmask pI1115) 1 1114 (true, (init pI1115), (init pI1115))) ∧ intTest pI1115 (runFrom pI1115 (fmask pI1115) (cmask pI1115) (hmask pI1115) 1 1114 (true, (init pI1115), (init pI1115))) 1115 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1115_fin) true) (by decide) rfl I1115_fin intTest_fst
theorem link1115 : linkOK pL1115 pH1115 pI1115 = true := by decide +kernel
theorem cvx1115 : ConvexBetweenHumps 1115 :=
  cvx_of L1115_ok H1115_ok I1115_ok link1115 (by decide)

/-! ### `N = 1116` -/

def pL1116 : Prm := ⟨76, 35, 38, 1118, 11, 18446744073709551616, 158039695053973309, 158039695053973309⟩
def pH1116 : Prm := ⟨76, 35, 38, 1118, 11, 18446744073709551616, 158041894077228861, 158041894077228861⟩
def pI1116 : Prm := ⟨65, 32, 30, 1118, 11, 18446744073709551616, 158039695053973309, 158041894077228861⟩
theorem L1116_fin : (prmOK pL1116 1116 && ptTest pL1116 (runFrom pL1116 (fmask pL1116) (cmask pL1116) (hmask pL1116) 1 1115 (true, (init pL1116), (init pL1116))) 1116 558 false) = true := by
  decide +kernel
theorem L1116_ok : RunOK pL1116 1116 (runFrom pL1116 (fmask pL1116) (cmask pL1116) (hmask pL1116) 1 1115 (true, (init pL1116), (init pL1116))) ∧ ptTest pL1116 (runFrom pL1116 (fmask pL1116) (cmask pL1116) (hmask pL1116) 1 1115 (true, (init pL1116), (init pL1116))) 1116 558 false = true :=
  fin_run (runOK_init (prmOK_of_and L1116_fin) true) (by decide) rfl L1116_fin ptTest_fst
theorem H1116_fin : (prmOK pH1116 1116 && ptTest pH1116 (runFrom pH1116 (fmask pH1116) (cmask pH1116) (hmask pH1116) 1 1115 (true, (init pH1116), (init pH1116))) 1116 558 true) = true := by
  decide +kernel
theorem H1116_ok : RunOK pH1116 1116 (runFrom pH1116 (fmask pH1116) (cmask pH1116) (hmask pH1116) 1 1115 (true, (init pH1116), (init pH1116))) ∧ ptTest pH1116 (runFrom pH1116 (fmask pH1116) (cmask pH1116) (hmask pH1116) 1 1115 (true, (init pH1116), (init pH1116))) 1116 558 true = true :=
  fin_run (runOK_init (prmOK_of_and H1116_fin) true) (by decide) rfl H1116_fin ptTest_fst
theorem I1116_fin : (prmOK pI1116 1116 && intTest pI1116 (runFrom pI1116 (fmask pI1116) (cmask pI1116) (hmask pI1116) 1 1115 (true, (init pI1116), (init pI1116))) 1116 18 true) = true := by
  decide +kernel
theorem I1116_ok : RunOK pI1116 1116 (runFrom pI1116 (fmask pI1116) (cmask pI1116) (hmask pI1116) 1 1115 (true, (init pI1116), (init pI1116))) ∧ intTest pI1116 (runFrom pI1116 (fmask pI1116) (cmask pI1116) (hmask pI1116) 1 1115 (true, (init pI1116), (init pI1116))) 1116 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1116_fin) true) (by decide) rfl I1116_fin intTest_fst
theorem link1116 : linkOK pL1116 pH1116 pI1116 = true := by decide +kernel
theorem cvx1116 : ConvexBetweenHumps 1116 :=
  cvx_of L1116_ok H1116_ok I1116_ok link1116 (by decide)
theorem cenlink1116 : cenLinkOK pI1116 1116 = true := by decide +kernel
theorem cen1116 : CenterUniqueMin 1116 ∧ DipHyp 1116 ∧ OnePointHyps 1116 :=
  cen_of L1116_ok H1116_ok I1116_ok link1116 cenlink1116

/-! ### `N = 1117` -/

def pL1117 : Prm := ⟨76, 35, 38, 1119, 11, 18446744073709551616, 157926062644034888, 157926062644034888⟩
def pH1117 : Prm := ⟨76, 35, 38, 1119, 11, 18446744073709551616, 157928261667290440, 157928261667290440⟩
def pI1117 : Prm := ⟨65, 32, 30, 1119, 11, 18446744073709551616, 157926062644034888, 157928261667290440⟩
theorem L1117_fin : (prmOK pL1117 1117 && ptTest pL1117 (runFrom pL1117 (fmask pL1117) (cmask pL1117) (hmask pL1117) 1 1116 (true, (init pL1117), (init pL1117))) 1117 559 false) = true := by
  decide +kernel
theorem L1117_ok : RunOK pL1117 1117 (runFrom pL1117 (fmask pL1117) (cmask pL1117) (hmask pL1117) 1 1116 (true, (init pL1117), (init pL1117))) ∧ ptTest pL1117 (runFrom pL1117 (fmask pL1117) (cmask pL1117) (hmask pL1117) 1 1116 (true, (init pL1117), (init pL1117))) 1117 559 false = true :=
  fin_run (runOK_init (prmOK_of_and L1117_fin) true) (by decide) rfl L1117_fin ptTest_fst
theorem H1117_fin : (prmOK pH1117 1117 && ptTest pH1117 (runFrom pH1117 (fmask pH1117) (cmask pH1117) (hmask pH1117) 1 1116 (true, (init pH1117), (init pH1117))) 1117 559 true) = true := by
  decide +kernel
theorem H1117_ok : RunOK pH1117 1117 (runFrom pH1117 (fmask pH1117) (cmask pH1117) (hmask pH1117) 1 1116 (true, (init pH1117), (init pH1117))) ∧ ptTest pH1117 (runFrom pH1117 (fmask pH1117) (cmask pH1117) (hmask pH1117) 1 1116 (true, (init pH1117), (init pH1117))) 1117 559 true = true :=
  fin_run (runOK_init (prmOK_of_and H1117_fin) true) (by decide) rfl H1117_fin ptTest_fst
theorem I1117_fin : (prmOK pI1117 1117 && intTest pI1117 (runFrom pI1117 (fmask pI1117) (cmask pI1117) (hmask pI1117) 1 1116 (true, (init pI1117), (init pI1117))) 1117 18 false) = true := by
  decide +kernel
theorem I1117_ok : RunOK pI1117 1117 (runFrom pI1117 (fmask pI1117) (cmask pI1117) (hmask pI1117) 1 1116 (true, (init pI1117), (init pI1117))) ∧ intTest pI1117 (runFrom pI1117 (fmask pI1117) (cmask pI1117) (hmask pI1117) 1 1116 (true, (init pI1117), (init pI1117))) 1117 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1117_fin) true) (by decide) rfl I1117_fin intTest_fst
theorem link1117 : linkOK pL1117 pH1117 pI1117 = true := by decide +kernel
theorem cvx1117 : ConvexBetweenHumps 1117 :=
  cvx_of L1117_ok H1117_ok I1117_ok link1117 (by decide)

/-! ### `N = 1118` -/

def pL1118 : Prm := ⟨76, 35, 38, 1120, 11, 18446744073709551616, 157812690944476111, 157812690944476111⟩
def pH1118 : Prm := ⟨76, 35, 38, 1120, 11, 18446744073709551616, 157814889967731663, 157814889967731663⟩
def pI1118 : Prm := ⟨65, 32, 30, 1120, 11, 18446744073709551616, 157812690944476111, 157814889967731663⟩
theorem L1118_fin : (prmOK pL1118 1118 && ptTest pL1118 (runFrom pL1118 (fmask pL1118) (cmask pL1118) (hmask pL1118) 1 1117 (true, (init pL1118), (init pL1118))) 1118 559 false) = true := by
  decide +kernel
theorem L1118_ok : RunOK pL1118 1118 (runFrom pL1118 (fmask pL1118) (cmask pL1118) (hmask pL1118) 1 1117 (true, (init pL1118), (init pL1118))) ∧ ptTest pL1118 (runFrom pL1118 (fmask pL1118) (cmask pL1118) (hmask pL1118) 1 1117 (true, (init pL1118), (init pL1118))) 1118 559 false = true :=
  fin_run (runOK_init (prmOK_of_and L1118_fin) true) (by decide) rfl L1118_fin ptTest_fst
theorem H1118_fin : (prmOK pH1118 1118 && ptTest pH1118 (runFrom pH1118 (fmask pH1118) (cmask pH1118) (hmask pH1118) 1 1117 (true, (init pH1118), (init pH1118))) 1118 559 true) = true := by
  decide +kernel
theorem H1118_ok : RunOK pH1118 1118 (runFrom pH1118 (fmask pH1118) (cmask pH1118) (hmask pH1118) 1 1117 (true, (init pH1118), (init pH1118))) ∧ ptTest pH1118 (runFrom pH1118 (fmask pH1118) (cmask pH1118) (hmask pH1118) 1 1117 (true, (init pH1118), (init pH1118))) 1118 559 true = true :=
  fin_run (runOK_init (prmOK_of_and H1118_fin) true) (by decide) rfl H1118_fin ptTest_fst
theorem I1118_fin : (prmOK pI1118 1118 && intTest pI1118 (runFrom pI1118 (fmask pI1118) (cmask pI1118) (hmask pI1118) 1 1117 (true, (init pI1118), (init pI1118))) 1118 18 true) = true := by
  decide +kernel
theorem I1118_ok : RunOK pI1118 1118 (runFrom pI1118 (fmask pI1118) (cmask pI1118) (hmask pI1118) 1 1117 (true, (init pI1118), (init pI1118))) ∧ intTest pI1118 (runFrom pI1118 (fmask pI1118) (cmask pI1118) (hmask pI1118) 1 1117 (true, (init pI1118), (init pI1118))) 1118 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1118_fin) true) (by decide) rfl I1118_fin intTest_fst
theorem link1118 : linkOK pL1118 pH1118 pI1118 = true := by decide +kernel
theorem cvx1118 : ConvexBetweenHumps 1118 :=
  cvx_of L1118_ok H1118_ok I1118_ok link1118 (by decide)
theorem cenlink1118 : cenLinkOK pI1118 1118 = true := by decide +kernel
theorem cen1118 : CenterUniqueMin 1118 ∧ DipHyp 1118 ∧ OnePointHyps 1118 :=
  cen_of L1118_ok H1118_ok I1118_ok link1118 cenlink1118

/-! ### `N = 1119` -/

def pL1119 : Prm := ⟨76, 35, 38, 1121, 11, 18446744073709551616, 157699414844633540, 157699414844633540⟩
def pH1119 : Prm := ⟨76, 35, 38, 1121, 11, 18446744073709551616, 157701613867889092, 157701613867889092⟩
def pI1119 : Prm := ⟨65, 32, 30, 1121, 11, 18446744073709551616, 157699414844633540, 157701613867889092⟩
theorem L1119_fin : (prmOK pL1119 1119 && ptTest pL1119 (runFrom pL1119 (fmask pL1119) (cmask pL1119) (hmask pL1119) 1 1118 (true, (init pL1119), (init pL1119))) 1119 560 false) = true := by
  decide +kernel
theorem L1119_ok : RunOK pL1119 1119 (runFrom pL1119 (fmask pL1119) (cmask pL1119) (hmask pL1119) 1 1118 (true, (init pL1119), (init pL1119))) ∧ ptTest pL1119 (runFrom pL1119 (fmask pL1119) (cmask pL1119) (hmask pL1119) 1 1118 (true, (init pL1119), (init pL1119))) 1119 560 false = true :=
  fin_run (runOK_init (prmOK_of_and L1119_fin) true) (by decide) rfl L1119_fin ptTest_fst
theorem H1119_fin : (prmOK pH1119 1119 && ptTest pH1119 (runFrom pH1119 (fmask pH1119) (cmask pH1119) (hmask pH1119) 1 1118 (true, (init pH1119), (init pH1119))) 1119 560 true) = true := by
  decide +kernel
theorem H1119_ok : RunOK pH1119 1119 (runFrom pH1119 (fmask pH1119) (cmask pH1119) (hmask pH1119) 1 1118 (true, (init pH1119), (init pH1119))) ∧ ptTest pH1119 (runFrom pH1119 (fmask pH1119) (cmask pH1119) (hmask pH1119) 1 1118 (true, (init pH1119), (init pH1119))) 1119 560 true = true :=
  fin_run (runOK_init (prmOK_of_and H1119_fin) true) (by decide) rfl H1119_fin ptTest_fst
theorem I1119_fin : (prmOK pI1119 1119 && intTest pI1119 (runFrom pI1119 (fmask pI1119) (cmask pI1119) (hmask pI1119) 1 1118 (true, (init pI1119), (init pI1119))) 1119 18 false) = true := by
  decide +kernel
theorem I1119_ok : RunOK pI1119 1119 (runFrom pI1119 (fmask pI1119) (cmask pI1119) (hmask pI1119) 1 1118 (true, (init pI1119), (init pI1119))) ∧ intTest pI1119 (runFrom pI1119 (fmask pI1119) (cmask pI1119) (hmask pI1119) 1 1118 (true, (init pI1119), (init pI1119))) 1119 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1119_fin) true) (by decide) rfl I1119_fin intTest_fst
theorem link1119 : linkOK pL1119 pH1119 pI1119 = true := by decide +kernel
theorem cvx1119 : ConvexBetweenHumps 1119 :=
  cvx_of L1119_ok H1119_ok I1119_ok link1119 (by decide)

/-! ### The range -/

theorem cvx_1086_1119 {N : ℕ} (h1 : 1086 ≤ N) (h2 : N ≤ 1119) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1102
  · by_cases h4 : N ≤ 1093
    · by_cases h6 : N ≤ 1089
      · by_cases h8 : N ≤ 1087
        · by_cases h10 : N ≤ 1086
          · obtain rfl : N = 1086 := by omega
            exact cvx1086
          · obtain rfl : N = 1087 := by omega
            exact cvx1087
        · by_cases h10 : N ≤ 1088
          · obtain rfl : N = 1088 := by omega
            exact cvx1088
          · obtain rfl : N = 1089 := by omega
            exact cvx1089
      · by_cases h8 : N ≤ 1091
        · by_cases h10 : N ≤ 1090
          · obtain rfl : N = 1090 := by omega
            exact cvx1090
          · obtain rfl : N = 1091 := by omega
            exact cvx1091
        · by_cases h10 : N ≤ 1092
          · obtain rfl : N = 1092 := by omega
            exact cvx1092
          · obtain rfl : N = 1093 := by omega
            exact cvx1093
    · by_cases h6 : N ≤ 1097
      · by_cases h8 : N ≤ 1095
        · by_cases h10 : N ≤ 1094
          · obtain rfl : N = 1094 := by omega
            exact cvx1094
          · obtain rfl : N = 1095 := by omega
            exact cvx1095
        · by_cases h10 : N ≤ 1096
          · obtain rfl : N = 1096 := by omega
            exact cvx1096
          · obtain rfl : N = 1097 := by omega
            exact cvx1097
      · by_cases h8 : N ≤ 1099
        · by_cases h10 : N ≤ 1098
          · obtain rfl : N = 1098 := by omega
            exact cvx1098
          · obtain rfl : N = 1099 := by omega
            exact cvx1099
        · by_cases h10 : N ≤ 1100
          · obtain rfl : N = 1100 := by omega
            exact cvx1100
          · by_cases h12 : N ≤ 1101
            · obtain rfl : N = 1101 := by omega
              exact cvx1101
            · obtain rfl : N = 1102 := by omega
              exact cvx1102
  · by_cases h4 : N ≤ 1110
    · by_cases h6 : N ≤ 1106
      · by_cases h8 : N ≤ 1104
        · by_cases h10 : N ≤ 1103
          · obtain rfl : N = 1103 := by omega
            exact cvx1103
          · obtain rfl : N = 1104 := by omega
            exact cvx1104
        · by_cases h10 : N ≤ 1105
          · obtain rfl : N = 1105 := by omega
            exact cvx1105
          · obtain rfl : N = 1106 := by omega
            exact cvx1106
      · by_cases h8 : N ≤ 1108
        · by_cases h10 : N ≤ 1107
          · obtain rfl : N = 1107 := by omega
            exact cvx1107
          · obtain rfl : N = 1108 := by omega
            exact cvx1108
        · by_cases h10 : N ≤ 1109
          · obtain rfl : N = 1109 := by omega
            exact cvx1109
          · obtain rfl : N = 1110 := by omega
            exact cvx1110
    · by_cases h6 : N ≤ 1114
      · by_cases h8 : N ≤ 1112
        · by_cases h10 : N ≤ 1111
          · obtain rfl : N = 1111 := by omega
            exact cvx1111
          · obtain rfl : N = 1112 := by omega
            exact cvx1112
        · by_cases h10 : N ≤ 1113
          · obtain rfl : N = 1113 := by omega
            exact cvx1113
          · obtain rfl : N = 1114 := by omega
            exact cvx1114
      · by_cases h8 : N ≤ 1116
        · by_cases h10 : N ≤ 1115
          · obtain rfl : N = 1115 := by omega
            exact cvx1115
          · obtain rfl : N = 1116 := by omega
            exact cvx1116
        · by_cases h10 : N ≤ 1117
          · obtain rfl : N = 1117 := by omega
            exact cvx1117
          · by_cases h12 : N ≤ 1118
            · obtain rfl : N = 1118 := by omega
              exact cvx1118
            · obtain rfl : N = 1119 := by omega
              exact cvx1119

theorem cen_1086_1119 {N : ℕ} (h1 : 1086 ≤ N) (h2 : N ≤ 1119) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1100
  · by_cases h4 : N ≤ 1092
    · by_cases h6 : N ≤ 1088
      · by_cases h8 : N ≤ 1086
        · obtain rfl : N = 1086 := by omega
          exact cen1086
        · obtain rfl : N = 1088 := by omega
          exact cen1088
      · by_cases h8 : N ≤ 1090
        · obtain rfl : N = 1090 := by omega
          exact cen1090
        · obtain rfl : N = 1092 := by omega
          exact cen1092
    · by_cases h6 : N ≤ 1096
      · by_cases h8 : N ≤ 1094
        · obtain rfl : N = 1094 := by omega
          exact cen1094
        · obtain rfl : N = 1096 := by omega
          exact cen1096
      · by_cases h8 : N ≤ 1098
        · obtain rfl : N = 1098 := by omega
          exact cen1098
        · obtain rfl : N = 1100 := by omega
          exact cen1100
  · by_cases h4 : N ≤ 1108
    · by_cases h6 : N ≤ 1104
      · by_cases h8 : N ≤ 1102
        · obtain rfl : N = 1102 := by omega
          exact cen1102
        · obtain rfl : N = 1104 := by omega
          exact cen1104
      · by_cases h8 : N ≤ 1106
        · obtain rfl : N = 1106 := by omega
          exact cen1106
        · obtain rfl : N = 1108 := by omega
          exact cen1108
    · by_cases h6 : N ≤ 1112
      · by_cases h8 : N ≤ 1110
        · obtain rfl : N = 1110 := by omega
          exact cen1110
        · obtain rfl : N = 1112 := by omega
          exact cen1112
      · by_cases h8 : N ≤ 1114
        · obtain rfl : N = 1114 := by omega
          exact cen1114
        · by_cases h10 : N ≤ 1116
          · obtain rfl : N = 1116 := by omega
            exact cen1116
          · obtain rfl : N = 1118 := by omega
            exact cen1118

end Kagey131.PaperD.T7
