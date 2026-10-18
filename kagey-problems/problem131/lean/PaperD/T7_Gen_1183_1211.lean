import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1183, …, 1211` (generated)

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

/-! ### `N = 1183` -/

def pL1183 : Prm := ⟨76, 35, 38, 1185, 11, 18446744073709551616, 150803459444765569, 150803459444765569⟩
def pH1183 : Prm := ⟨76, 35, 38, 1185, 11, 18446744073709551616, 150805658468021121, 150805658468021121⟩
def pI1183 : Prm := ⟨66, 32, 31, 1185, 11, 18446744073709551616, 150803459444765569, 150805658468021121⟩
theorem L1183_fin : (prmOK pL1183 1183 && ptTest pL1183 (runFrom pL1183 (fmask pL1183) (cmask pL1183) (hmask pL1183) 1 1182 (true, (init pL1183), (init pL1183))) 1183 592 false) = true := by
  decide +kernel
theorem L1183_ok : RunOK pL1183 1183 (runFrom pL1183 (fmask pL1183) (cmask pL1183) (hmask pL1183) 1 1182 (true, (init pL1183), (init pL1183))) ∧ ptTest pL1183 (runFrom pL1183 (fmask pL1183) (cmask pL1183) (hmask pL1183) 1 1182 (true, (init pL1183), (init pL1183))) 1183 592 false = true :=
  fin_run (runOK_init (prmOK_of_and L1183_fin) true) (by decide) rfl L1183_fin ptTest_fst
theorem H1183_fin : (prmOK pH1183 1183 && ptTest pH1183 (runFrom pH1183 (fmask pH1183) (cmask pH1183) (hmask pH1183) 1 1182 (true, (init pH1183), (init pH1183))) 1183 592 true) = true := by
  decide +kernel
theorem H1183_ok : RunOK pH1183 1183 (runFrom pH1183 (fmask pH1183) (cmask pH1183) (hmask pH1183) 1 1182 (true, (init pH1183), (init pH1183))) ∧ ptTest pH1183 (runFrom pH1183 (fmask pH1183) (cmask pH1183) (hmask pH1183) 1 1182 (true, (init pH1183), (init pH1183))) 1183 592 true = true :=
  fin_run (runOK_init (prmOK_of_and H1183_fin) true) (by decide) rfl H1183_fin ptTest_fst
theorem I1183_fin : (prmOK pI1183 1183 && intTest pI1183 (runFrom pI1183 (fmask pI1183) (cmask pI1183) (hmask pI1183) 1 1182 (true, (init pI1183), (init pI1183))) 1183 19 false) = true := by
  decide +kernel
theorem I1183_ok : RunOK pI1183 1183 (runFrom pI1183 (fmask pI1183) (cmask pI1183) (hmask pI1183) 1 1182 (true, (init pI1183), (init pI1183))) ∧ intTest pI1183 (runFrom pI1183 (fmask pI1183) (cmask pI1183) (hmask pI1183) 1 1182 (true, (init pI1183), (init pI1183))) 1183 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1183_fin) true) (by decide) rfl I1183_fin intTest_fst
theorem link1183 : linkOK pL1183 pH1183 pI1183 = true := by decide +kernel
theorem cvx1183 : ConvexBetweenHumps 1183 :=
  cvx_of L1183_ok H1183_ok I1183_ok link1183 (by decide)

/-! ### `N = 1184` -/

def pL1184 : Prm := ⟨76, 35, 38, 1186, 11, 18446744073709551616, 150700952076840621, 150700952076840621⟩
def pH1184 : Prm := ⟨76, 35, 38, 1186, 11, 18446744073709551616, 150703151100096173, 150703151100096173⟩
def pI1184 : Prm := ⟨66, 32, 31, 1186, 11, 18446744073709551616, 150700952076840621, 150703151100096173⟩
theorem L1184_fin : (prmOK pL1184 1184 && ptTest pL1184 (runFrom pL1184 (fmask pL1184) (cmask pL1184) (hmask pL1184) 1 1183 (true, (init pL1184), (init pL1184))) 1184 592 false) = true := by
  decide +kernel
theorem L1184_ok : RunOK pL1184 1184 (runFrom pL1184 (fmask pL1184) (cmask pL1184) (hmask pL1184) 1 1183 (true, (init pL1184), (init pL1184))) ∧ ptTest pL1184 (runFrom pL1184 (fmask pL1184) (cmask pL1184) (hmask pL1184) 1 1183 (true, (init pL1184), (init pL1184))) 1184 592 false = true :=
  fin_run (runOK_init (prmOK_of_and L1184_fin) true) (by decide) rfl L1184_fin ptTest_fst
theorem H1184_fin : (prmOK pH1184 1184 && ptTest pH1184 (runFrom pH1184 (fmask pH1184) (cmask pH1184) (hmask pH1184) 1 1183 (true, (init pH1184), (init pH1184))) 1184 592 true) = true := by
  decide +kernel
theorem H1184_ok : RunOK pH1184 1184 (runFrom pH1184 (fmask pH1184) (cmask pH1184) (hmask pH1184) 1 1183 (true, (init pH1184), (init pH1184))) ∧ ptTest pH1184 (runFrom pH1184 (fmask pH1184) (cmask pH1184) (hmask pH1184) 1 1183 (true, (init pH1184), (init pH1184))) 1184 592 true = true :=
  fin_run (runOK_init (prmOK_of_and H1184_fin) true) (by decide) rfl H1184_fin ptTest_fst
theorem I1184_fin : (prmOK pI1184 1184 && intTest pI1184 (runFrom pI1184 (fmask pI1184) (cmask pI1184) (hmask pI1184) 1 1183 (true, (init pI1184), (init pI1184))) 1184 19 true) = true := by
  decide +kernel
theorem I1184_ok : RunOK pI1184 1184 (runFrom pI1184 (fmask pI1184) (cmask pI1184) (hmask pI1184) 1 1183 (true, (init pI1184), (init pI1184))) ∧ intTest pI1184 (runFrom pI1184 (fmask pI1184) (cmask pI1184) (hmask pI1184) 1 1183 (true, (init pI1184), (init pI1184))) 1184 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1184_fin) true) (by decide) rfl I1184_fin intTest_fst
theorem link1184 : linkOK pL1184 pH1184 pI1184 = true := by decide +kernel
theorem cvx1184 : ConvexBetweenHumps 1184 :=
  cvx_of L1184_ok H1184_ok I1184_ok link1184 (by decide)
theorem cenlink1184 : cenLinkOK pI1184 1184 = true := by decide +kernel
theorem cen1184 : CenterUniqueMin 1184 ∧ DipHyp 1184 ∧ OnePointHyps 1184 :=
  cen_of L1184_ok H1184_ok I1184_ok link1184 cenlink1184

/-! ### `N = 1185` -/

def pL1185 : Prm := ⟨76, 35, 38, 1187, 11, 18446744073709551616, 150598527804358834, 150598527804358834⟩
def pH1185 : Prm := ⟨76, 35, 38, 1187, 11, 18446744073709551616, 150600726827614386, 150600726827614386⟩
def pI1185 : Prm := ⟨66, 32, 31, 1187, 11, 18446744073709551616, 150598527804358834, 150600726827614386⟩
theorem L1185_fin : (prmOK pL1185 1185 && ptTest pL1185 (runFrom pL1185 (fmask pL1185) (cmask pL1185) (hmask pL1185) 1 1184 (true, (init pL1185), (init pL1185))) 1185 593 false) = true := by
  decide +kernel
theorem L1185_ok : RunOK pL1185 1185 (runFrom pL1185 (fmask pL1185) (cmask pL1185) (hmask pL1185) 1 1184 (true, (init pL1185), (init pL1185))) ∧ ptTest pL1185 (runFrom pL1185 (fmask pL1185) (cmask pL1185) (hmask pL1185) 1 1184 (true, (init pL1185), (init pL1185))) 1185 593 false = true :=
  fin_run (runOK_init (prmOK_of_and L1185_fin) true) (by decide) rfl L1185_fin ptTest_fst
theorem H1185_fin : (prmOK pH1185 1185 && ptTest pH1185 (runFrom pH1185 (fmask pH1185) (cmask pH1185) (hmask pH1185) 1 1184 (true, (init pH1185), (init pH1185))) 1185 593 true) = true := by
  decide +kernel
theorem H1185_ok : RunOK pH1185 1185 (runFrom pH1185 (fmask pH1185) (cmask pH1185) (hmask pH1185) 1 1184 (true, (init pH1185), (init pH1185))) ∧ ptTest pH1185 (runFrom pH1185 (fmask pH1185) (cmask pH1185) (hmask pH1185) 1 1184 (true, (init pH1185), (init pH1185))) 1185 593 true = true :=
  fin_run (runOK_init (prmOK_of_and H1185_fin) true) (by decide) rfl H1185_fin ptTest_fst
theorem I1185_fin : (prmOK pI1185 1185 && intTest pI1185 (runFrom pI1185 (fmask pI1185) (cmask pI1185) (hmask pI1185) 1 1184 (true, (init pI1185), (init pI1185))) 1185 19 false) = true := by
  decide +kernel
theorem I1185_ok : RunOK pI1185 1185 (runFrom pI1185 (fmask pI1185) (cmask pI1185) (hmask pI1185) 1 1184 (true, (init pI1185), (init pI1185))) ∧ intTest pI1185 (runFrom pI1185 (fmask pI1185) (cmask pI1185) (hmask pI1185) 1 1184 (true, (init pI1185), (init pI1185))) 1185 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1185_fin) true) (by decide) rfl I1185_fin intTest_fst
theorem link1185 : linkOK pL1185 pH1185 pI1185 = true := by decide +kernel
theorem cvx1185 : ConvexBetweenHumps 1185 :=
  cvx_of L1185_ok H1185_ok I1185_ok link1185 (by decide)

/-! ### `N = 1186` -/

def pL1186 : Prm := ⟨76, 35, 38, 1188, 11, 18446744073709551616, 150496324139219543, 150496324139219543⟩
def pH1186 : Prm := ⟨76, 35, 38, 1188, 11, 18446744073709551616, 150498523162475095, 150498523162475095⟩
def pI1186 : Prm := ⟨66, 32, 31, 1188, 11, 18446744073709551616, 150496324139219543, 150498523162475095⟩
theorem L1186_fin : (prmOK pL1186 1186 && ptTest pL1186 (runFrom pL1186 (fmask pL1186) (cmask pL1186) (hmask pL1186) 1 1185 (true, (init pL1186), (init pL1186))) 1186 593 false) = true := by
  decide +kernel
theorem L1186_ok : RunOK pL1186 1186 (runFrom pL1186 (fmask pL1186) (cmask pL1186) (hmask pL1186) 1 1185 (true, (init pL1186), (init pL1186))) ∧ ptTest pL1186 (runFrom pL1186 (fmask pL1186) (cmask pL1186) (hmask pL1186) 1 1185 (true, (init pL1186), (init pL1186))) 1186 593 false = true :=
  fin_run (runOK_init (prmOK_of_and L1186_fin) true) (by decide) rfl L1186_fin ptTest_fst
theorem H1186_fin : (prmOK pH1186 1186 && ptTest pH1186 (runFrom pH1186 (fmask pH1186) (cmask pH1186) (hmask pH1186) 1 1185 (true, (init pH1186), (init pH1186))) 1186 593 true) = true := by
  decide +kernel
theorem H1186_ok : RunOK pH1186 1186 (runFrom pH1186 (fmask pH1186) (cmask pH1186) (hmask pH1186) 1 1185 (true, (init pH1186), (init pH1186))) ∧ ptTest pH1186 (runFrom pH1186 (fmask pH1186) (cmask pH1186) (hmask pH1186) 1 1185 (true, (init pH1186), (init pH1186))) 1186 593 true = true :=
  fin_run (runOK_init (prmOK_of_and H1186_fin) true) (by decide) rfl H1186_fin ptTest_fst
theorem I1186_fin : (prmOK pI1186 1186 && intTest pI1186 (runFrom pI1186 (fmask pI1186) (cmask pI1186) (hmask pI1186) 1 1185 (true, (init pI1186), (init pI1186))) 1186 19 true) = true := by
  decide +kernel
theorem I1186_ok : RunOK pI1186 1186 (runFrom pI1186 (fmask pI1186) (cmask pI1186) (hmask pI1186) 1 1185 (true, (init pI1186), (init pI1186))) ∧ intTest pI1186 (runFrom pI1186 (fmask pI1186) (cmask pI1186) (hmask pI1186) 1 1185 (true, (init pI1186), (init pI1186))) 1186 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1186_fin) true) (by decide) rfl I1186_fin intTest_fst
theorem link1186 : linkOK pL1186 pH1186 pI1186 = true := by decide +kernel
theorem cvx1186 : ConvexBetweenHumps 1186 :=
  cvx_of L1186_ok H1186_ok I1186_ok link1186 (by decide)
theorem cenlink1186 : cenLinkOK pI1186 1186 = true := by decide +kernel
theorem cen1186 : CenterUniqueMin 1186 ∧ DipHyp 1186 ∧ OnePointHyps 1186 :=
  cen_of L1186_ok H1186_ok I1186_ok link1186 cenlink1186

/-! ### `N = 1187` -/

def pL1187 : Prm := ⟨76, 35, 38, 1189, 11, 18446744073709551616, 150394203226192614, 150394203226192614⟩
def pH1187 : Prm := ⟨76, 35, 38, 1189, 11, 18446744073709551616, 150396402249448166, 150396402249448166⟩
def pI1187 : Prm := ⟨66, 32, 31, 1189, 11, 18446744073709551616, 150394203226192614, 150396402249448166⟩
theorem L1187_fin : (prmOK pL1187 1187 && ptTest pL1187 (runFrom pL1187 (fmask pL1187) (cmask pL1187) (hmask pL1187) 1 1186 (true, (init pL1187), (init pL1187))) 1187 594 false) = true := by
  decide +kernel
theorem L1187_ok : RunOK pL1187 1187 (runFrom pL1187 (fmask pL1187) (cmask pL1187) (hmask pL1187) 1 1186 (true, (init pL1187), (init pL1187))) ∧ ptTest pL1187 (runFrom pL1187 (fmask pL1187) (cmask pL1187) (hmask pL1187) 1 1186 (true, (init pL1187), (init pL1187))) 1187 594 false = true :=
  fin_run (runOK_init (prmOK_of_and L1187_fin) true) (by decide) rfl L1187_fin ptTest_fst
theorem H1187_fin : (prmOK pH1187 1187 && ptTest pH1187 (runFrom pH1187 (fmask pH1187) (cmask pH1187) (hmask pH1187) 1 1186 (true, (init pH1187), (init pH1187))) 1187 594 true) = true := by
  decide +kernel
theorem H1187_ok : RunOK pH1187 1187 (runFrom pH1187 (fmask pH1187) (cmask pH1187) (hmask pH1187) 1 1186 (true, (init pH1187), (init pH1187))) ∧ ptTest pH1187 (runFrom pH1187 (fmask pH1187) (cmask pH1187) (hmask pH1187) 1 1186 (true, (init pH1187), (init pH1187))) 1187 594 true = true :=
  fin_run (runOK_init (prmOK_of_and H1187_fin) true) (by decide) rfl H1187_fin ptTest_fst
theorem I1187_fin : (prmOK pI1187 1187 && intTest pI1187 (runFrom pI1187 (fmask pI1187) (cmask pI1187) (hmask pI1187) 1 1186 (true, (init pI1187), (init pI1187))) 1187 19 false) = true := by
  decide +kernel
theorem I1187_ok : RunOK pI1187 1187 (runFrom pI1187 (fmask pI1187) (cmask pI1187) (hmask pI1187) 1 1186 (true, (init pI1187), (init pI1187))) ∧ intTest pI1187 (runFrom pI1187 (fmask pI1187) (cmask pI1187) (hmask pI1187) 1 1186 (true, (init pI1187), (init pI1187))) 1187 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1187_fin) true) (by decide) rfl I1187_fin intTest_fst
theorem link1187 : linkOK pL1187 pH1187 pI1187 = true := by decide +kernel
theorem cvx1187 : ConvexBetweenHumps 1187 :=
  cvx_of L1187_ok H1187_ok I1187_ok link1187 (by decide)

/-! ### `N = 1188` -/

def pL1188 : Prm := ⟨76, 35, 38, 1190, 11, 18446744073709551616, 150292301871312717, 150292301871312717⟩
def pH1188 : Prm := ⟨76, 35, 38, 1190, 11, 18446744073709551616, 150294500894568269, 150294500894568269⟩
def pI1188 : Prm := ⟨66, 32, 31, 1190, 11, 18446744073709551616, 150292301871312717, 150294500894568269⟩
theorem L1188_fin : (prmOK pL1188 1188 && ptTest pL1188 (runFrom pL1188 (fmask pL1188) (cmask pL1188) (hmask pL1188) 1 1187 (true, (init pL1188), (init pL1188))) 1188 594 false) = true := by
  decide +kernel
theorem L1188_ok : RunOK pL1188 1188 (runFrom pL1188 (fmask pL1188) (cmask pL1188) (hmask pL1188) 1 1187 (true, (init pL1188), (init pL1188))) ∧ ptTest pL1188 (runFrom pL1188 (fmask pL1188) (cmask pL1188) (hmask pL1188) 1 1187 (true, (init pL1188), (init pL1188))) 1188 594 false = true :=
  fin_run (runOK_init (prmOK_of_and L1188_fin) true) (by decide) rfl L1188_fin ptTest_fst
theorem H1188_fin : (prmOK pH1188 1188 && ptTest pH1188 (runFrom pH1188 (fmask pH1188) (cmask pH1188) (hmask pH1188) 1 1187 (true, (init pH1188), (init pH1188))) 1188 594 true) = true := by
  decide +kernel
theorem H1188_ok : RunOK pH1188 1188 (runFrom pH1188 (fmask pH1188) (cmask pH1188) (hmask pH1188) 1 1187 (true, (init pH1188), (init pH1188))) ∧ ptTest pH1188 (runFrom pH1188 (fmask pH1188) (cmask pH1188) (hmask pH1188) 1 1187 (true, (init pH1188), (init pH1188))) 1188 594 true = true :=
  fin_run (runOK_init (prmOK_of_and H1188_fin) true) (by decide) rfl H1188_fin ptTest_fst
theorem I1188_fin : (prmOK pI1188 1188 && intTest pI1188 (runFrom pI1188 (fmask pI1188) (cmask pI1188) (hmask pI1188) 1 1187 (true, (init pI1188), (init pI1188))) 1188 19 true) = true := by
  decide +kernel
theorem I1188_ok : RunOK pI1188 1188 (runFrom pI1188 (fmask pI1188) (cmask pI1188) (hmask pI1188) 1 1187 (true, (init pI1188), (init pI1188))) ∧ intTest pI1188 (runFrom pI1188 (fmask pI1188) (cmask pI1188) (hmask pI1188) 1 1187 (true, (init pI1188), (init pI1188))) 1188 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1188_fin) true) (by decide) rfl I1188_fin intTest_fst
theorem link1188 : linkOK pL1188 pH1188 pI1188 = true := by decide +kernel
theorem cvx1188 : ConvexBetweenHumps 1188 :=
  cvx_of L1188_ok H1188_ok I1188_ok link1188 (by decide)
theorem cenlink1188 : cenLinkOK pI1188 1188 = true := by decide +kernel
theorem cen1188 : CenterUniqueMin 1188 ∧ DipHyp 1188 ∧ OnePointHyps 1188 :=
  cen_of L1188_ok H1188_ok I1188_ok link1188 cenlink1188

/-! ### `N = 1189` -/

def pL1189 : Prm := ⟨76, 35, 38, 1191, 11, 18446744073709551616, 150190482927114397, 150190482927114397⟩
def pH1189 : Prm := ⟨76, 35, 38, 1191, 11, 18446744073709551616, 150192681950369949, 150192681950369949⟩
def pI1189 : Prm := ⟨66, 32, 31, 1191, 11, 18446744073709551616, 150190482927114397, 150192681950369949⟩
theorem L1189_fin : (prmOK pL1189 1189 && ptTest pL1189 (runFrom pL1189 (fmask pL1189) (cmask pL1189) (hmask pL1189) 1 1188 (true, (init pL1189), (init pL1189))) 1189 595 false) = true := by
  decide +kernel
theorem L1189_ok : RunOK pL1189 1189 (runFrom pL1189 (fmask pL1189) (cmask pL1189) (hmask pL1189) 1 1188 (true, (init pL1189), (init pL1189))) ∧ ptTest pL1189 (runFrom pL1189 (fmask pL1189) (cmask pL1189) (hmask pL1189) 1 1188 (true, (init pL1189), (init pL1189))) 1189 595 false = true :=
  fin_run (runOK_init (prmOK_of_and L1189_fin) true) (by decide) rfl L1189_fin ptTest_fst
theorem H1189_fin : (prmOK pH1189 1189 && ptTest pH1189 (runFrom pH1189 (fmask pH1189) (cmask pH1189) (hmask pH1189) 1 1188 (true, (init pH1189), (init pH1189))) 1189 595 true) = true := by
  decide +kernel
theorem H1189_ok : RunOK pH1189 1189 (runFrom pH1189 (fmask pH1189) (cmask pH1189) (hmask pH1189) 1 1188 (true, (init pH1189), (init pH1189))) ∧ ptTest pH1189 (runFrom pH1189 (fmask pH1189) (cmask pH1189) (hmask pH1189) 1 1188 (true, (init pH1189), (init pH1189))) 1189 595 true = true :=
  fin_run (runOK_init (prmOK_of_and H1189_fin) true) (by decide) rfl H1189_fin ptTest_fst
theorem I1189_fin : (prmOK pI1189 1189 && intTest pI1189 (runFrom pI1189 (fmask pI1189) (cmask pI1189) (hmask pI1189) 1 1188 (true, (init pI1189), (init pI1189))) 1189 19 false) = true := by
  decide +kernel
theorem I1189_ok : RunOK pI1189 1189 (runFrom pI1189 (fmask pI1189) (cmask pI1189) (hmask pI1189) 1 1188 (true, (init pI1189), (init pI1189))) ∧ intTest pI1189 (runFrom pI1189 (fmask pI1189) (cmask pI1189) (hmask pI1189) 1 1188 (true, (init pI1189), (init pI1189))) 1189 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1189_fin) true) (by decide) rfl I1189_fin intTest_fst
theorem link1189 : linkOK pL1189 pH1189 pI1189 = true := by decide +kernel
theorem cvx1189 : ConvexBetweenHumps 1189 :=
  cvx_of L1189_ok H1189_ok I1189_ok link1189 (by decide)

/-! ### `N = 1190` -/

def pL1190 : Prm := ⟨76, 35, 38, 1192, 11, 18446744073709551616, 150088882498600707, 150088882498600707⟩
def pH1190 : Prm := ⟨76, 35, 38, 1192, 11, 18446744073709551616, 150091081521856259, 150091081521856259⟩
def pI1190 : Prm := ⟨66, 32, 31, 1192, 11, 18446744073709551616, 150088882498600707, 150091081521856259⟩
theorem L1190_fin : (prmOK pL1190 1190 && ptTest pL1190 (runFrom pL1190 (fmask pL1190) (cmask pL1190) (hmask pL1190) 1 1189 (true, (init pL1190), (init pL1190))) 1190 595 false) = true := by
  decide +kernel
theorem L1190_ok : RunOK pL1190 1190 (runFrom pL1190 (fmask pL1190) (cmask pL1190) (hmask pL1190) 1 1189 (true, (init pL1190), (init pL1190))) ∧ ptTest pL1190 (runFrom pL1190 (fmask pL1190) (cmask pL1190) (hmask pL1190) 1 1189 (true, (init pL1190), (init pL1190))) 1190 595 false = true :=
  fin_run (runOK_init (prmOK_of_and L1190_fin) true) (by decide) rfl L1190_fin ptTest_fst
theorem H1190_fin : (prmOK pH1190 1190 && ptTest pH1190 (runFrom pH1190 (fmask pH1190) (cmask pH1190) (hmask pH1190) 1 1189 (true, (init pH1190), (init pH1190))) 1190 595 true) = true := by
  decide +kernel
theorem H1190_ok : RunOK pH1190 1190 (runFrom pH1190 (fmask pH1190) (cmask pH1190) (hmask pH1190) 1 1189 (true, (init pH1190), (init pH1190))) ∧ ptTest pH1190 (runFrom pH1190 (fmask pH1190) (cmask pH1190) (hmask pH1190) 1 1189 (true, (init pH1190), (init pH1190))) 1190 595 true = true :=
  fin_run (runOK_init (prmOK_of_and H1190_fin) true) (by decide) rfl H1190_fin ptTest_fst
theorem I1190_fin : (prmOK pI1190 1190 && intTest pI1190 (runFrom pI1190 (fmask pI1190) (cmask pI1190) (hmask pI1190) 1 1189 (true, (init pI1190), (init pI1190))) 1190 19 true) = true := by
  decide +kernel
theorem I1190_ok : RunOK pI1190 1190 (runFrom pI1190 (fmask pI1190) (cmask pI1190) (hmask pI1190) 1 1189 (true, (init pI1190), (init pI1190))) ∧ intTest pI1190 (runFrom pI1190 (fmask pI1190) (cmask pI1190) (hmask pI1190) 1 1189 (true, (init pI1190), (init pI1190))) 1190 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1190_fin) true) (by decide) rfl I1190_fin intTest_fst
theorem link1190 : linkOK pL1190 pH1190 pI1190 = true := by decide +kernel
theorem cvx1190 : ConvexBetweenHumps 1190 :=
  cvx_of L1190_ok H1190_ok I1190_ok link1190 (by decide)
theorem cenlink1190 : cenLinkOK pI1190 1190 = true := by decide +kernel
theorem cen1190 : CenterUniqueMin 1190 ∧ DipHyp 1190 ∧ OnePointHyps 1190 :=
  cen_of L1190_ok H1190_ok I1190_ok link1190 cenlink1190

/-! ### `N = 1191` -/

def pL1191 : Prm := ⟨76, 35, 38, 1193, 11, 18446744073709551616, 149987364141256269, 149987364141256269⟩
def pH1191 : Prm := ⟨76, 35, 38, 1193, 11, 18446744073709551616, 149989563164511821, 149989563164511821⟩
def pI1191 : Prm := ⟨66, 32, 31, 1193, 11, 18446744073709551616, 149987364141256269, 149989563164511821⟩
noncomputable def L1191_cp1 : Nat × Nat := t7val% (fastRun pL1191 1 841 (init pL1191) (init pL1191))
theorem L1191_seg1 : segOK pL1191 1 841 (init pL1191) (init pL1191) L1191_cp1.1 L1191_cp1.2 = true := by
  decide +kernel
theorem L1191_fin : (prmOK pL1191 1191 && ptTest pL1191 (runFrom pL1191 (fmask pL1191) (cmask pL1191) (hmask pL1191) 842 349 (true, L1191_cp1.1, L1191_cp1.2)) 1191 596 false) = true := by
  decide +kernel
theorem L1191_ok : RunOK pL1191 1191 (runFrom pL1191 (fmask pL1191) (cmask pL1191) (hmask pL1191) 842 349 (true, L1191_cp1.1, L1191_cp1.2)) ∧ ptTest pL1191 (runFrom pL1191 (fmask pL1191) (cmask pL1191) (hmask pL1191) 842 349 (true, L1191_cp1.1, L1191_cp1.2)) 1191 596 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1191_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1191_fin) true) L1191_seg1) (by decide) rfl L1191_fin ptTest_fst
noncomputable def H1191_cp1 : Nat × Nat := t7val% (fastRun pH1191 1 841 (init pH1191) (init pH1191))
theorem H1191_seg1 : segOK pH1191 1 841 (init pH1191) (init pH1191) H1191_cp1.1 H1191_cp1.2 = true := by
  decide +kernel
theorem H1191_fin : (prmOK pH1191 1191 && ptTest pH1191 (runFrom pH1191 (fmask pH1191) (cmask pH1191) (hmask pH1191) 842 349 (true, H1191_cp1.1, H1191_cp1.2)) 1191 596 true) = true := by
  decide +kernel
theorem H1191_ok : RunOK pH1191 1191 (runFrom pH1191 (fmask pH1191) (cmask pH1191) (hmask pH1191) 842 349 (true, H1191_cp1.1, H1191_cp1.2)) ∧ ptTest pH1191 (runFrom pH1191 (fmask pH1191) (cmask pH1191) (hmask pH1191) 842 349 (true, H1191_cp1.1, H1191_cp1.2)) 1191 596 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1191_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1191_fin) true) H1191_seg1) (by decide) rfl H1191_fin ptTest_fst
theorem I1191_fin : (prmOK pI1191 1191 && intTest pI1191 (runFrom pI1191 (fmask pI1191) (cmask pI1191) (hmask pI1191) 1 1190 (true, (init pI1191), (init pI1191))) 1191 19 false) = true := by
  decide +kernel
theorem I1191_ok : RunOK pI1191 1191 (runFrom pI1191 (fmask pI1191) (cmask pI1191) (hmask pI1191) 1 1190 (true, (init pI1191), (init pI1191))) ∧ intTest pI1191 (runFrom pI1191 (fmask pI1191) (cmask pI1191) (hmask pI1191) 1 1190 (true, (init pI1191), (init pI1191))) 1191 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1191_fin) true) (by decide) rfl I1191_fin intTest_fst
theorem link1191 : linkOK pL1191 pH1191 pI1191 = true := by decide +kernel
theorem cvx1191 : ConvexBetweenHumps 1191 :=
  cvx_of L1191_ok H1191_ok I1191_ok link1191 (by decide)

/-! ### `N = 1192` -/

def pL1192 : Prm := ⟨76, 35, 38, 1194, 11, 18446744073709551616, 149886063263793336, 149886063263793336⟩
def pH1192 : Prm := ⟨76, 35, 38, 1194, 11, 18446744073709551616, 149888262287048888, 149888262287048888⟩
def pI1192 : Prm := ⟨66, 32, 31, 1194, 11, 18446744073709551616, 149886063263793336, 149888262287048888⟩
noncomputable def L1192_cp1 : Nat × Nat := t7val% (fastRun pL1192 1 842 (init pL1192) (init pL1192))
theorem L1192_seg1 : segOK pL1192 1 842 (init pL1192) (init pL1192) L1192_cp1.1 L1192_cp1.2 = true := by
  decide +kernel
theorem L1192_fin : (prmOK pL1192 1192 && ptTest pL1192 (runFrom pL1192 (fmask pL1192) (cmask pL1192) (hmask pL1192) 843 349 (true, L1192_cp1.1, L1192_cp1.2)) 1192 596 false) = true := by
  decide +kernel
theorem L1192_ok : RunOK pL1192 1192 (runFrom pL1192 (fmask pL1192) (cmask pL1192) (hmask pL1192) 843 349 (true, L1192_cp1.1, L1192_cp1.2)) ∧ ptTest pL1192 (runFrom pL1192 (fmask pL1192) (cmask pL1192) (hmask pL1192) 843 349 (true, L1192_cp1.1, L1192_cp1.2)) 1192 596 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1192_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1192_fin) true) L1192_seg1) (by decide) rfl L1192_fin ptTest_fst
noncomputable def H1192_cp1 : Nat × Nat := t7val% (fastRun pH1192 1 842 (init pH1192) (init pH1192))
theorem H1192_seg1 : segOK pH1192 1 842 (init pH1192) (init pH1192) H1192_cp1.1 H1192_cp1.2 = true := by
  decide +kernel
theorem H1192_fin : (prmOK pH1192 1192 && ptTest pH1192 (runFrom pH1192 (fmask pH1192) (cmask pH1192) (hmask pH1192) 843 349 (true, H1192_cp1.1, H1192_cp1.2)) 1192 596 true) = true := by
  decide +kernel
theorem H1192_ok : RunOK pH1192 1192 (runFrom pH1192 (fmask pH1192) (cmask pH1192) (hmask pH1192) 843 349 (true, H1192_cp1.1, H1192_cp1.2)) ∧ ptTest pH1192 (runFrom pH1192 (fmask pH1192) (cmask pH1192) (hmask pH1192) 843 349 (true, H1192_cp1.1, H1192_cp1.2)) 1192 596 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1192_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1192_fin) true) H1192_seg1) (by decide) rfl H1192_fin ptTest_fst
theorem I1192_fin : (prmOK pI1192 1192 && intTest pI1192 (runFrom pI1192 (fmask pI1192) (cmask pI1192) (hmask pI1192) 1 1191 (true, (init pI1192), (init pI1192))) 1192 19 true) = true := by
  decide +kernel
theorem I1192_ok : RunOK pI1192 1192 (runFrom pI1192 (fmask pI1192) (cmask pI1192) (hmask pI1192) 1 1191 (true, (init pI1192), (init pI1192))) ∧ intTest pI1192 (runFrom pI1192 (fmask pI1192) (cmask pI1192) (hmask pI1192) 1 1191 (true, (init pI1192), (init pI1192))) 1192 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1192_fin) true) (by decide) rfl I1192_fin intTest_fst
theorem link1192 : linkOK pL1192 pH1192 pI1192 = true := by decide +kernel
theorem cvx1192 : ConvexBetweenHumps 1192 :=
  cvx_of L1192_ok H1192_ok I1192_ok link1192 (by decide)
theorem cenlink1192 : cenLinkOK pI1192 1192 = true := by decide +kernel
theorem cen1192 : CenterUniqueMin 1192 ∧ DipHyp 1192 ∧ OnePointHyps 1192 :=
  cen_of L1192_ok H1192_ok I1192_ok link1192 cenlink1192

/-! ### `N = 1193` -/

def pL1193 : Prm := ⟨76, 35, 38, 1195, 11, 18446744073709551616, 149784844119887343, 149784844119887343⟩
def pH1193 : Prm := ⟨76, 35, 38, 1195, 11, 18446744073709551616, 149787043143142895, 149787043143142895⟩
def pI1193 : Prm := ⟨66, 32, 31, 1195, 11, 18446744073709551616, 149784844119887343, 149787043143142895⟩
noncomputable def L1193_cp1 : Nat × Nat := t7val% (fastRun pL1193 1 843 (init pL1193) (init pL1193))
theorem L1193_seg1 : segOK pL1193 1 843 (init pL1193) (init pL1193) L1193_cp1.1 L1193_cp1.2 = true := by
  decide +kernel
theorem L1193_fin : (prmOK pL1193 1193 && ptTest pL1193 (runFrom pL1193 (fmask pL1193) (cmask pL1193) (hmask pL1193) 844 349 (true, L1193_cp1.1, L1193_cp1.2)) 1193 597 false) = true := by
  decide +kernel
theorem L1193_ok : RunOK pL1193 1193 (runFrom pL1193 (fmask pL1193) (cmask pL1193) (hmask pL1193) 844 349 (true, L1193_cp1.1, L1193_cp1.2)) ∧ ptTest pL1193 (runFrom pL1193 (fmask pL1193) (cmask pL1193) (hmask pL1193) 844 349 (true, L1193_cp1.1, L1193_cp1.2)) 1193 597 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1193_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1193_fin) true) L1193_seg1) (by decide) rfl L1193_fin ptTest_fst
noncomputable def H1193_cp1 : Nat × Nat := t7val% (fastRun pH1193 1 843 (init pH1193) (init pH1193))
theorem H1193_seg1 : segOK pH1193 1 843 (init pH1193) (init pH1193) H1193_cp1.1 H1193_cp1.2 = true := by
  decide +kernel
theorem H1193_fin : (prmOK pH1193 1193 && ptTest pH1193 (runFrom pH1193 (fmask pH1193) (cmask pH1193) (hmask pH1193) 844 349 (true, H1193_cp1.1, H1193_cp1.2)) 1193 597 true) = true := by
  decide +kernel
theorem H1193_ok : RunOK pH1193 1193 (runFrom pH1193 (fmask pH1193) (cmask pH1193) (hmask pH1193) 844 349 (true, H1193_cp1.1, H1193_cp1.2)) ∧ ptTest pH1193 (runFrom pH1193 (fmask pH1193) (cmask pH1193) (hmask pH1193) 844 349 (true, H1193_cp1.1, H1193_cp1.2)) 1193 597 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1193_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1193_fin) true) H1193_seg1) (by decide) rfl H1193_fin ptTest_fst
theorem I1193_fin : (prmOK pI1193 1193 && intTest pI1193 (runFrom pI1193 (fmask pI1193) (cmask pI1193) (hmask pI1193) 1 1192 (true, (init pI1193), (init pI1193))) 1193 19 false) = true := by
  decide +kernel
theorem I1193_ok : RunOK pI1193 1193 (runFrom pI1193 (fmask pI1193) (cmask pI1193) (hmask pI1193) 1 1192 (true, (init pI1193), (init pI1193))) ∧ intTest pI1193 (runFrom pI1193 (fmask pI1193) (cmask pI1193) (hmask pI1193) 1 1192 (true, (init pI1193), (init pI1193))) 1193 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1193_fin) true) (by decide) rfl I1193_fin intTest_fst
theorem link1193 : linkOK pL1193 pH1193 pI1193 = true := by decide +kernel
theorem cvx1193 : ConvexBetweenHumps 1193 :=
  cvx_of L1193_ok H1193_ok I1193_ok link1193 (by decide)

/-! ### `N = 1194` -/

def pL1194 : Prm := ⟨76, 35, 38, 1196, 11, 18446744073709551616, 149683841426682111, 149683841426682111⟩
def pH1194 : Prm := ⟨76, 35, 38, 1196, 11, 18446744073709551616, 149686040449937663, 149686040449937663⟩
def pI1194 : Prm := ⟨66, 32, 31, 1196, 11, 18446744073709551616, 149683841426682111, 149686040449937663⟩
noncomputable def L1194_cp1 : Nat × Nat := t7val% (fastRun pL1194 1 843 (init pL1194) (init pL1194))
theorem L1194_seg1 : segOK pL1194 1 843 (init pL1194) (init pL1194) L1194_cp1.1 L1194_cp1.2 = true := by
  decide +kernel
theorem L1194_fin : (prmOK pL1194 1194 && ptTest pL1194 (runFrom pL1194 (fmask pL1194) (cmask pL1194) (hmask pL1194) 844 350 (true, L1194_cp1.1, L1194_cp1.2)) 1194 597 false) = true := by
  decide +kernel
theorem L1194_ok : RunOK pL1194 1194 (runFrom pL1194 (fmask pL1194) (cmask pL1194) (hmask pL1194) 844 350 (true, L1194_cp1.1, L1194_cp1.2)) ∧ ptTest pL1194 (runFrom pL1194 (fmask pL1194) (cmask pL1194) (hmask pL1194) 844 350 (true, L1194_cp1.1, L1194_cp1.2)) 1194 597 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1194_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1194_fin) true) L1194_seg1) (by decide) rfl L1194_fin ptTest_fst
noncomputable def H1194_cp1 : Nat × Nat := t7val% (fastRun pH1194 1 843 (init pH1194) (init pH1194))
theorem H1194_seg1 : segOK pH1194 1 843 (init pH1194) (init pH1194) H1194_cp1.1 H1194_cp1.2 = true := by
  decide +kernel
theorem H1194_fin : (prmOK pH1194 1194 && ptTest pH1194 (runFrom pH1194 (fmask pH1194) (cmask pH1194) (hmask pH1194) 844 350 (true, H1194_cp1.1, H1194_cp1.2)) 1194 597 true) = true := by
  decide +kernel
theorem H1194_ok : RunOK pH1194 1194 (runFrom pH1194 (fmask pH1194) (cmask pH1194) (hmask pH1194) 844 350 (true, H1194_cp1.1, H1194_cp1.2)) ∧ ptTest pH1194 (runFrom pH1194 (fmask pH1194) (cmask pH1194) (hmask pH1194) 844 350 (true, H1194_cp1.1, H1194_cp1.2)) 1194 597 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1194_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1194_fin) true) H1194_seg1) (by decide) rfl H1194_fin ptTest_fst
theorem I1194_fin : (prmOK pI1194 1194 && intTest pI1194 (runFrom pI1194 (fmask pI1194) (cmask pI1194) (hmask pI1194) 1 1193 (true, (init pI1194), (init pI1194))) 1194 19 true) = true := by
  decide +kernel
theorem I1194_ok : RunOK pI1194 1194 (runFrom pI1194 (fmask pI1194) (cmask pI1194) (hmask pI1194) 1 1193 (true, (init pI1194), (init pI1194))) ∧ intTest pI1194 (runFrom pI1194 (fmask pI1194) (cmask pI1194) (hmask pI1194) 1 1193 (true, (init pI1194), (init pI1194))) 1194 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1194_fin) true) (by decide) rfl I1194_fin intTest_fst
theorem link1194 : linkOK pL1194 pH1194 pI1194 = true := by decide +kernel
theorem cvx1194 : ConvexBetweenHumps 1194 :=
  cvx_of L1194_ok H1194_ok I1194_ok link1194 (by decide)
theorem cenlink1194 : cenLinkOK pI1194 1194 = true := by decide +kernel
theorem cen1194 : CenterUniqueMin 1194 ∧ DipHyp 1194 ∧ OnePointHyps 1194 :=
  cen_of L1194_ok H1194_ok I1194_ok link1194 cenlink1194

/-! ### `N = 1195` -/

def pL1195 : Prm := ⟨76, 35, 38, 1197, 11, 18446744073709551616, 149582920131303077, 149582920131303077⟩
def pH1195 : Prm := ⟨76, 35, 38, 1197, 11, 18446744073709551616, 149585119154558629, 149585119154558629⟩
def pI1195 : Prm := ⟨66, 32, 31, 1197, 11, 18446744073709551616, 149582920131303077, 149585119154558629⟩
noncomputable def L1195_cp1 : Nat × Nat := t7val% (fastRun pL1195 1 844 (init pL1195) (init pL1195))
theorem L1195_seg1 : segOK pL1195 1 844 (init pL1195) (init pL1195) L1195_cp1.1 L1195_cp1.2 = true := by
  decide +kernel
theorem L1195_fin : (prmOK pL1195 1195 && ptTest pL1195 (runFrom pL1195 (fmask pL1195) (cmask pL1195) (hmask pL1195) 845 350 (true, L1195_cp1.1, L1195_cp1.2)) 1195 598 false) = true := by
  decide +kernel
theorem L1195_ok : RunOK pL1195 1195 (runFrom pL1195 (fmask pL1195) (cmask pL1195) (hmask pL1195) 845 350 (true, L1195_cp1.1, L1195_cp1.2)) ∧ ptTest pL1195 (runFrom pL1195 (fmask pL1195) (cmask pL1195) (hmask pL1195) 845 350 (true, L1195_cp1.1, L1195_cp1.2)) 1195 598 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1195_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1195_fin) true) L1195_seg1) (by decide) rfl L1195_fin ptTest_fst
noncomputable def H1195_cp1 : Nat × Nat := t7val% (fastRun pH1195 1 844 (init pH1195) (init pH1195))
theorem H1195_seg1 : segOK pH1195 1 844 (init pH1195) (init pH1195) H1195_cp1.1 H1195_cp1.2 = true := by
  decide +kernel
theorem H1195_fin : (prmOK pH1195 1195 && ptTest pH1195 (runFrom pH1195 (fmask pH1195) (cmask pH1195) (hmask pH1195) 845 350 (true, H1195_cp1.1, H1195_cp1.2)) 1195 598 true) = true := by
  decide +kernel
theorem H1195_ok : RunOK pH1195 1195 (runFrom pH1195 (fmask pH1195) (cmask pH1195) (hmask pH1195) 845 350 (true, H1195_cp1.1, H1195_cp1.2)) ∧ ptTest pH1195 (runFrom pH1195 (fmask pH1195) (cmask pH1195) (hmask pH1195) 845 350 (true, H1195_cp1.1, H1195_cp1.2)) 1195 598 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1195_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1195_fin) true) H1195_seg1) (by decide) rfl H1195_fin ptTest_fst
theorem I1195_fin : (prmOK pI1195 1195 && intTest pI1195 (runFrom pI1195 (fmask pI1195) (cmask pI1195) (hmask pI1195) 1 1194 (true, (init pI1195), (init pI1195))) 1195 19 false) = true := by
  decide +kernel
theorem I1195_ok : RunOK pI1195 1195 (runFrom pI1195 (fmask pI1195) (cmask pI1195) (hmask pI1195) 1 1194 (true, (init pI1195), (init pI1195))) ∧ intTest pI1195 (runFrom pI1195 (fmask pI1195) (cmask pI1195) (hmask pI1195) 1 1194 (true, (init pI1195), (init pI1195))) 1195 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1195_fin) true) (by decide) rfl I1195_fin intTest_fst
theorem link1195 : linkOK pL1195 pH1195 pI1195 = true := by decide +kernel
theorem cvx1195 : ConvexBetweenHumps 1195 :=
  cvx_of L1195_ok H1195_ok I1195_ok link1195 (by decide)

/-! ### `N = 1196` -/

def pL1196 : Prm := ⟨76, 35, 38, 1198, 11, 18446744073709551616, 149482214264011098, 149482214264011098⟩
def pH1196 : Prm := ⟨76, 35, 38, 1198, 11, 18446744073709551616, 149484413287266650, 149484413287266650⟩
def pI1196 : Prm := ⟨66, 32, 31, 1198, 11, 18446744073709551616, 149482214264011098, 149484413287266650⟩
noncomputable def L1196_cp1 : Nat × Nat := t7val% (fastRun pL1196 1 845 (init pL1196) (init pL1196))
theorem L1196_seg1 : segOK pL1196 1 845 (init pL1196) (init pL1196) L1196_cp1.1 L1196_cp1.2 = true := by
  decide +kernel
theorem L1196_fin : (prmOK pL1196 1196 && ptTest pL1196 (runFrom pL1196 (fmask pL1196) (cmask pL1196) (hmask pL1196) 846 350 (true, L1196_cp1.1, L1196_cp1.2)) 1196 598 false) = true := by
  decide +kernel
theorem L1196_ok : RunOK pL1196 1196 (runFrom pL1196 (fmask pL1196) (cmask pL1196) (hmask pL1196) 846 350 (true, L1196_cp1.1, L1196_cp1.2)) ∧ ptTest pL1196 (runFrom pL1196 (fmask pL1196) (cmask pL1196) (hmask pL1196) 846 350 (true, L1196_cp1.1, L1196_cp1.2)) 1196 598 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1196_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1196_fin) true) L1196_seg1) (by decide) rfl L1196_fin ptTest_fst
noncomputable def H1196_cp1 : Nat × Nat := t7val% (fastRun pH1196 1 845 (init pH1196) (init pH1196))
theorem H1196_seg1 : segOK pH1196 1 845 (init pH1196) (init pH1196) H1196_cp1.1 H1196_cp1.2 = true := by
  decide +kernel
theorem H1196_fin : (prmOK pH1196 1196 && ptTest pH1196 (runFrom pH1196 (fmask pH1196) (cmask pH1196) (hmask pH1196) 846 350 (true, H1196_cp1.1, H1196_cp1.2)) 1196 598 true) = true := by
  decide +kernel
theorem H1196_ok : RunOK pH1196 1196 (runFrom pH1196 (fmask pH1196) (cmask pH1196) (hmask pH1196) 846 350 (true, H1196_cp1.1, H1196_cp1.2)) ∧ ptTest pH1196 (runFrom pH1196 (fmask pH1196) (cmask pH1196) (hmask pH1196) 846 350 (true, H1196_cp1.1, H1196_cp1.2)) 1196 598 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1196_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1196_fin) true) H1196_seg1) (by decide) rfl H1196_fin ptTest_fst
theorem I1196_fin : (prmOK pI1196 1196 && intTest pI1196 (runFrom pI1196 (fmask pI1196) (cmask pI1196) (hmask pI1196) 1 1195 (true, (init pI1196), (init pI1196))) 1196 19 true) = true := by
  decide +kernel
theorem I1196_ok : RunOK pI1196 1196 (runFrom pI1196 (fmask pI1196) (cmask pI1196) (hmask pI1196) 1 1195 (true, (init pI1196), (init pI1196))) ∧ intTest pI1196 (runFrom pI1196 (fmask pI1196) (cmask pI1196) (hmask pI1196) 1 1195 (true, (init pI1196), (init pI1196))) 1196 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1196_fin) true) (by decide) rfl I1196_fin intTest_fst
theorem link1196 : linkOK pL1196 pH1196 pI1196 = true := by decide +kernel
theorem cvx1196 : ConvexBetweenHumps 1196 :=
  cvx_of L1196_ok H1196_ok I1196_ok link1196 (by decide)
theorem cenlink1196 : cenLinkOK pI1196 1196 = true := by decide +kernel
theorem cen1196 : CenterUniqueMin 1196 ∧ DipHyp 1196 ∧ OnePointHyps 1196 :=
  cen_of L1196_ok H1196_ok I1196_ok link1196 cenlink1196

/-! ### `N = 1197` -/

def pL1197 : Prm := ⟨76, 35, 38, 1199, 11, 18446744073709551616, 149381589460696144, 149381589460696144⟩
def pH1197 : Prm := ⟨76, 35, 38, 1199, 11, 18446744073709551616, 149383788483951696, 149383788483951696⟩
def pI1197 : Prm := ⟨66, 32, 31, 1199, 11, 18446744073709551616, 149381589460696144, 149383788483951696⟩
noncomputable def L1197_cp1 : Nat × Nat := t7val% (fastRun pL1197 1 845 (init pL1197) (init pL1197))
theorem L1197_seg1 : segOK pL1197 1 845 (init pL1197) (init pL1197) L1197_cp1.1 L1197_cp1.2 = true := by
  decide +kernel
theorem L1197_fin : (prmOK pL1197 1197 && ptTest pL1197 (runFrom pL1197 (fmask pL1197) (cmask pL1197) (hmask pL1197) 846 351 (true, L1197_cp1.1, L1197_cp1.2)) 1197 599 false) = true := by
  decide +kernel
theorem L1197_ok : RunOK pL1197 1197 (runFrom pL1197 (fmask pL1197) (cmask pL1197) (hmask pL1197) 846 351 (true, L1197_cp1.1, L1197_cp1.2)) ∧ ptTest pL1197 (runFrom pL1197 (fmask pL1197) (cmask pL1197) (hmask pL1197) 846 351 (true, L1197_cp1.1, L1197_cp1.2)) 1197 599 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1197_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1197_fin) true) L1197_seg1) (by decide) rfl L1197_fin ptTest_fst
noncomputable def H1197_cp1 : Nat × Nat := t7val% (fastRun pH1197 1 845 (init pH1197) (init pH1197))
theorem H1197_seg1 : segOK pH1197 1 845 (init pH1197) (init pH1197) H1197_cp1.1 H1197_cp1.2 = true := by
  decide +kernel
theorem H1197_fin : (prmOK pH1197 1197 && ptTest pH1197 (runFrom pH1197 (fmask pH1197) (cmask pH1197) (hmask pH1197) 846 351 (true, H1197_cp1.1, H1197_cp1.2)) 1197 599 true) = true := by
  decide +kernel
theorem H1197_ok : RunOK pH1197 1197 (runFrom pH1197 (fmask pH1197) (cmask pH1197) (hmask pH1197) 846 351 (true, H1197_cp1.1, H1197_cp1.2)) ∧ ptTest pH1197 (runFrom pH1197 (fmask pH1197) (cmask pH1197) (hmask pH1197) 846 351 (true, H1197_cp1.1, H1197_cp1.2)) 1197 599 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1197_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1197_fin) true) H1197_seg1) (by decide) rfl H1197_fin ptTest_fst
theorem I1197_fin : (prmOK pI1197 1197 && intTest pI1197 (runFrom pI1197 (fmask pI1197) (cmask pI1197) (hmask pI1197) 1 1196 (true, (init pI1197), (init pI1197))) 1197 19 false) = true := by
  decide +kernel
theorem I1197_ok : RunOK pI1197 1197 (runFrom pI1197 (fmask pI1197) (cmask pI1197) (hmask pI1197) 1 1196 (true, (init pI1197), (init pI1197))) ∧ intTest pI1197 (runFrom pI1197 (fmask pI1197) (cmask pI1197) (hmask pI1197) 1 1196 (true, (init pI1197), (init pI1197))) 1197 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1197_fin) true) (by decide) rfl I1197_fin intTest_fst
theorem link1197 : linkOK pL1197 pH1197 pI1197 = true := by decide +kernel
theorem cvx1197 : ConvexBetweenHumps 1197 :=
  cvx_of L1197_ok H1197_ok I1197_ok link1197 (by decide)

/-! ### `N = 1198` -/

def pL1198 : Prm := ⟨76, 35, 38, 1200, 11, 18446744073709551616, 149281179069366241, 149281179069366241⟩
def pH1198 : Prm := ⟨76, 35, 38, 1200, 11, 18446744073709551616, 149283378092621793, 149283378092621793⟩
def pI1198 : Prm := ⟨66, 32, 31, 1200, 11, 18446744073709551616, 149281179069366241, 149283378092621793⟩
noncomputable def L1198_cp1 : Nat × Nat := t7val% (fastRun pL1198 1 846 (init pL1198) (init pL1198))
theorem L1198_seg1 : segOK pL1198 1 846 (init pL1198) (init pL1198) L1198_cp1.1 L1198_cp1.2 = true := by
  decide +kernel
theorem L1198_fin : (prmOK pL1198 1198 && ptTest pL1198 (runFrom pL1198 (fmask pL1198) (cmask pL1198) (hmask pL1198) 847 351 (true, L1198_cp1.1, L1198_cp1.2)) 1198 599 false) = true := by
  decide +kernel
theorem L1198_ok : RunOK pL1198 1198 (runFrom pL1198 (fmask pL1198) (cmask pL1198) (hmask pL1198) 847 351 (true, L1198_cp1.1, L1198_cp1.2)) ∧ ptTest pL1198 (runFrom pL1198 (fmask pL1198) (cmask pL1198) (hmask pL1198) 847 351 (true, L1198_cp1.1, L1198_cp1.2)) 1198 599 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1198_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1198_fin) true) L1198_seg1) (by decide) rfl L1198_fin ptTest_fst
noncomputable def H1198_cp1 : Nat × Nat := t7val% (fastRun pH1198 1 846 (init pH1198) (init pH1198))
theorem H1198_seg1 : segOK pH1198 1 846 (init pH1198) (init pH1198) H1198_cp1.1 H1198_cp1.2 = true := by
  decide +kernel
theorem H1198_fin : (prmOK pH1198 1198 && ptTest pH1198 (runFrom pH1198 (fmask pH1198) (cmask pH1198) (hmask pH1198) 847 351 (true, H1198_cp1.1, H1198_cp1.2)) 1198 599 true) = true := by
  decide +kernel
theorem H1198_ok : RunOK pH1198 1198 (runFrom pH1198 (fmask pH1198) (cmask pH1198) (hmask pH1198) 847 351 (true, H1198_cp1.1, H1198_cp1.2)) ∧ ptTest pH1198 (runFrom pH1198 (fmask pH1198) (cmask pH1198) (hmask pH1198) 847 351 (true, H1198_cp1.1, H1198_cp1.2)) 1198 599 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1198_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1198_fin) true) H1198_seg1) (by decide) rfl H1198_fin ptTest_fst
theorem I1198_fin : (prmOK pI1198 1198 && intTest pI1198 (runFrom pI1198 (fmask pI1198) (cmask pI1198) (hmask pI1198) 1 1197 (true, (init pI1198), (init pI1198))) 1198 19 true) = true := by
  decide +kernel
theorem I1198_ok : RunOK pI1198 1198 (runFrom pI1198 (fmask pI1198) (cmask pI1198) (hmask pI1198) 1 1197 (true, (init pI1198), (init pI1198))) ∧ intTest pI1198 (runFrom pI1198 (fmask pI1198) (cmask pI1198) (hmask pI1198) 1 1197 (true, (init pI1198), (init pI1198))) 1198 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1198_fin) true) (by decide) rfl I1198_fin intTest_fst
theorem link1198 : linkOK pL1198 pH1198 pI1198 = true := by decide +kernel
theorem cvx1198 : ConvexBetweenHumps 1198 :=
  cvx_of L1198_ok H1198_ok I1198_ok link1198 (by decide)
theorem cenlink1198 : cenLinkOK pI1198 1198 = true := by decide +kernel
theorem cen1198 : CenterUniqueMin 1198 ∧ DipHyp 1198 ∧ OnePointHyps 1198 :=
  cen_of L1198_ok H1198_ok I1198_ok link1198 cenlink1198

/-! ### `N = 1199` -/

def pL1199 : Prm := ⟨76, 35, 38, 1201, 11, 18446744073709551616, 149180849409990417, 149180849409990417⟩
def pH1199 : Prm := ⟨76, 35, 38, 1201, 11, 18446744073709551616, 149183048433245969, 149183048433245969⟩
def pI1199 : Prm := ⟨67, 32, 32, 1201, 11, 18446744073709551616, 149180849409990417, 149183048433245969⟩
noncomputable def L1199_cp1 : Nat × Nat := t7val% (fastRun pL1199 1 847 (init pL1199) (init pL1199))
theorem L1199_seg1 : segOK pL1199 1 847 (init pL1199) (init pL1199) L1199_cp1.1 L1199_cp1.2 = true := by
  decide +kernel
theorem L1199_fin : (prmOK pL1199 1199 && ptTest pL1199 (runFrom pL1199 (fmask pL1199) (cmask pL1199) (hmask pL1199) 848 351 (true, L1199_cp1.1, L1199_cp1.2)) 1199 600 false) = true := by
  decide +kernel
theorem L1199_ok : RunOK pL1199 1199 (runFrom pL1199 (fmask pL1199) (cmask pL1199) (hmask pL1199) 848 351 (true, L1199_cp1.1, L1199_cp1.2)) ∧ ptTest pL1199 (runFrom pL1199 (fmask pL1199) (cmask pL1199) (hmask pL1199) 848 351 (true, L1199_cp1.1, L1199_cp1.2)) 1199 600 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1199_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1199_fin) true) L1199_seg1) (by decide) rfl L1199_fin ptTest_fst
noncomputable def H1199_cp1 : Nat × Nat := t7val% (fastRun pH1199 1 847 (init pH1199) (init pH1199))
theorem H1199_seg1 : segOK pH1199 1 847 (init pH1199) (init pH1199) H1199_cp1.1 H1199_cp1.2 = true := by
  decide +kernel
theorem H1199_fin : (prmOK pH1199 1199 && ptTest pH1199 (runFrom pH1199 (fmask pH1199) (cmask pH1199) (hmask pH1199) 848 351 (true, H1199_cp1.1, H1199_cp1.2)) 1199 600 true) = true := by
  decide +kernel
theorem H1199_ok : RunOK pH1199 1199 (runFrom pH1199 (fmask pH1199) (cmask pH1199) (hmask pH1199) 848 351 (true, H1199_cp1.1, H1199_cp1.2)) ∧ ptTest pH1199 (runFrom pH1199 (fmask pH1199) (cmask pH1199) (hmask pH1199) 848 351 (true, H1199_cp1.1, H1199_cp1.2)) 1199 600 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1199_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1199_fin) true) H1199_seg1) (by decide) rfl H1199_fin ptTest_fst
theorem I1199_fin : (prmOK pI1199 1199 && intTest pI1199 (runFrom pI1199 (fmask pI1199) (cmask pI1199) (hmask pI1199) 1 1198 (true, (init pI1199), (init pI1199))) 1199 19 false) = true := by
  decide +kernel
theorem I1199_ok : RunOK pI1199 1199 (runFrom pI1199 (fmask pI1199) (cmask pI1199) (hmask pI1199) 1 1198 (true, (init pI1199), (init pI1199))) ∧ intTest pI1199 (runFrom pI1199 (fmask pI1199) (cmask pI1199) (hmask pI1199) 1 1198 (true, (init pI1199), (init pI1199))) 1199 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1199_fin) true) (by decide) rfl I1199_fin intTest_fst
theorem link1199 : linkOK pL1199 pH1199 pI1199 = true := by decide +kernel
theorem cvx1199 : ConvexBetweenHumps 1199 :=
  cvx_of L1199_ok H1199_ok I1199_ok link1199 (by decide)

/-! ### `N = 1200` -/

def pL1200 : Prm := ⟨76, 35, 38, 1202, 11, 18446744073709551616, 149080733152990893, 149080733152990893⟩
def pH1200 : Prm := ⟨76, 35, 38, 1202, 11, 18446744073709551616, 149082932176246445, 149082932176246445⟩
def pI1200 : Prm := ⟨66, 32, 31, 1202, 11, 18446744073709551616, 149080733152990893, 149082932176246445⟩
noncomputable def L1200_cp1 : Nat × Nat := t7val% (fastRun pL1200 1 848 (init pL1200) (init pL1200))
theorem L1200_seg1 : segOK pL1200 1 848 (init pL1200) (init pL1200) L1200_cp1.1 L1200_cp1.2 = true := by
  decide +kernel
theorem L1200_fin : (prmOK pL1200 1200 && ptTest pL1200 (runFrom pL1200 (fmask pL1200) (cmask pL1200) (hmask pL1200) 849 351 (true, L1200_cp1.1, L1200_cp1.2)) 1200 600 false) = true := by
  decide +kernel
theorem L1200_ok : RunOK pL1200 1200 (runFrom pL1200 (fmask pL1200) (cmask pL1200) (hmask pL1200) 849 351 (true, L1200_cp1.1, L1200_cp1.2)) ∧ ptTest pL1200 (runFrom pL1200 (fmask pL1200) (cmask pL1200) (hmask pL1200) 849 351 (true, L1200_cp1.1, L1200_cp1.2)) 1200 600 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1200_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1200_fin) true) L1200_seg1) (by decide) rfl L1200_fin ptTest_fst
noncomputable def H1200_cp1 : Nat × Nat := t7val% (fastRun pH1200 1 848 (init pH1200) (init pH1200))
theorem H1200_seg1 : segOK pH1200 1 848 (init pH1200) (init pH1200) H1200_cp1.1 H1200_cp1.2 = true := by
  decide +kernel
theorem H1200_fin : (prmOK pH1200 1200 && ptTest pH1200 (runFrom pH1200 (fmask pH1200) (cmask pH1200) (hmask pH1200) 849 351 (true, H1200_cp1.1, H1200_cp1.2)) 1200 600 true) = true := by
  decide +kernel
theorem H1200_ok : RunOK pH1200 1200 (runFrom pH1200 (fmask pH1200) (cmask pH1200) (hmask pH1200) 849 351 (true, H1200_cp1.1, H1200_cp1.2)) ∧ ptTest pH1200 (runFrom pH1200 (fmask pH1200) (cmask pH1200) (hmask pH1200) 849 351 (true, H1200_cp1.1, H1200_cp1.2)) 1200 600 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1200_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1200_fin) true) H1200_seg1) (by decide) rfl H1200_fin ptTest_fst
theorem I1200_fin : (prmOK pI1200 1200 && intTest pI1200 (runFrom pI1200 (fmask pI1200) (cmask pI1200) (hmask pI1200) 1 1199 (true, (init pI1200), (init pI1200))) 1200 19 true) = true := by
  decide +kernel
theorem I1200_ok : RunOK pI1200 1200 (runFrom pI1200 (fmask pI1200) (cmask pI1200) (hmask pI1200) 1 1199 (true, (init pI1200), (init pI1200))) ∧ intTest pI1200 (runFrom pI1200 (fmask pI1200) (cmask pI1200) (hmask pI1200) 1 1199 (true, (init pI1200), (init pI1200))) 1200 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1200_fin) true) (by decide) rfl I1200_fin intTest_fst
theorem link1200 : linkOK pL1200 pH1200 pI1200 = true := by decide +kernel
theorem cvx1200 : ConvexBetweenHumps 1200 :=
  cvx_of L1200_ok H1200_ok I1200_ok link1200 (by decide)
theorem cenlink1200 : cenLinkOK pI1200 1200 = true := by decide +kernel
theorem cen1200 : CenterUniqueMin 1200 ∧ DipHyp 1200 ∧ OnePointHyps 1200 :=
  cen_of L1200_ok H1200_ok I1200_ok link1200 cenlink1200

/-! ### `N = 1201` -/

def pL1201 : Prm := ⟨76, 35, 38, 1203, 11, 18446744073709551616, 148980697297767176, 148980697297767176⟩
def pH1201 : Prm := ⟨76, 35, 38, 1203, 11, 18446744073709551616, 148982896321022728, 148982896321022728⟩
def pI1201 : Prm := ⟨67, 32, 32, 1203, 11, 18446744073709551616, 148980697297767176, 148982896321022728⟩
noncomputable def L1201_cp1 : Nat × Nat := t7val% (fastRun pL1201 1 848 (init pL1201) (init pL1201))
theorem L1201_seg1 : segOK pL1201 1 848 (init pL1201) (init pL1201) L1201_cp1.1 L1201_cp1.2 = true := by
  decide +kernel
theorem L1201_fin : (prmOK pL1201 1201 && ptTest pL1201 (runFrom pL1201 (fmask pL1201) (cmask pL1201) (hmask pL1201) 849 352 (true, L1201_cp1.1, L1201_cp1.2)) 1201 601 false) = true := by
  decide +kernel
theorem L1201_ok : RunOK pL1201 1201 (runFrom pL1201 (fmask pL1201) (cmask pL1201) (hmask pL1201) 849 352 (true, L1201_cp1.1, L1201_cp1.2)) ∧ ptTest pL1201 (runFrom pL1201 (fmask pL1201) (cmask pL1201) (hmask pL1201) 849 352 (true, L1201_cp1.1, L1201_cp1.2)) 1201 601 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1201_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1201_fin) true) L1201_seg1) (by decide) rfl L1201_fin ptTest_fst
noncomputable def H1201_cp1 : Nat × Nat := t7val% (fastRun pH1201 1 848 (init pH1201) (init pH1201))
theorem H1201_seg1 : segOK pH1201 1 848 (init pH1201) (init pH1201) H1201_cp1.1 H1201_cp1.2 = true := by
  decide +kernel
theorem H1201_fin : (prmOK pH1201 1201 && ptTest pH1201 (runFrom pH1201 (fmask pH1201) (cmask pH1201) (hmask pH1201) 849 352 (true, H1201_cp1.1, H1201_cp1.2)) 1201 601 true) = true := by
  decide +kernel
theorem H1201_ok : RunOK pH1201 1201 (runFrom pH1201 (fmask pH1201) (cmask pH1201) (hmask pH1201) 849 352 (true, H1201_cp1.1, H1201_cp1.2)) ∧ ptTest pH1201 (runFrom pH1201 (fmask pH1201) (cmask pH1201) (hmask pH1201) 849 352 (true, H1201_cp1.1, H1201_cp1.2)) 1201 601 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1201_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1201_fin) true) H1201_seg1) (by decide) rfl H1201_fin ptTest_fst
theorem I1201_fin : (prmOK pI1201 1201 && intTest pI1201 (runFrom pI1201 (fmask pI1201) (cmask pI1201) (hmask pI1201) 1 1200 (true, (init pI1201), (init pI1201))) 1201 19 false) = true := by
  decide +kernel
theorem I1201_ok : RunOK pI1201 1201 (runFrom pI1201 (fmask pI1201) (cmask pI1201) (hmask pI1201) 1 1200 (true, (init pI1201), (init pI1201))) ∧ intTest pI1201 (runFrom pI1201 (fmask pI1201) (cmask pI1201) (hmask pI1201) 1 1200 (true, (init pI1201), (init pI1201))) 1201 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1201_fin) true) (by decide) rfl I1201_fin intTest_fst
theorem link1201 : linkOK pL1201 pH1201 pI1201 = true := by decide +kernel
theorem cvx1201 : ConvexBetweenHumps 1201 :=
  cvx_of L1201_ok H1201_ok I1201_ok link1201 (by decide)

/-! ### `N = 1202` -/

def pL1202 : Prm := ⟨76, 35, 38, 1204, 11, 18446744073709551616, 148880873841712030, 148880873841712030⟩
def pH1202 : Prm := ⟨76, 35, 38, 1204, 11, 18446744073709551616, 148883072864967582, 148883072864967582⟩
def pI1202 : Prm := ⟨66, 32, 31, 1204, 11, 18446744073709551616, 148880873841712030, 148883072864967582⟩
noncomputable def L1202_cp1 : Nat × Nat := t7val% (fastRun pL1202 1 849 (init pL1202) (init pL1202))
theorem L1202_seg1 : segOK pL1202 1 849 (init pL1202) (init pL1202) L1202_cp1.1 L1202_cp1.2 = true := by
  decide +kernel
theorem L1202_fin : (prmOK pL1202 1202 && ptTest pL1202 (runFrom pL1202 (fmask pL1202) (cmask pL1202) (hmask pL1202) 850 352 (true, L1202_cp1.1, L1202_cp1.2)) 1202 601 false) = true := by
  decide +kernel
theorem L1202_ok : RunOK pL1202 1202 (runFrom pL1202 (fmask pL1202) (cmask pL1202) (hmask pL1202) 850 352 (true, L1202_cp1.1, L1202_cp1.2)) ∧ ptTest pL1202 (runFrom pL1202 (fmask pL1202) (cmask pL1202) (hmask pL1202) 850 352 (true, L1202_cp1.1, L1202_cp1.2)) 1202 601 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1202_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1202_fin) true) L1202_seg1) (by decide) rfl L1202_fin ptTest_fst
noncomputable def H1202_cp1 : Nat × Nat := t7val% (fastRun pH1202 1 849 (init pH1202) (init pH1202))
theorem H1202_seg1 : segOK pH1202 1 849 (init pH1202) (init pH1202) H1202_cp1.1 H1202_cp1.2 = true := by
  decide +kernel
theorem H1202_fin : (prmOK pH1202 1202 && ptTest pH1202 (runFrom pH1202 (fmask pH1202) (cmask pH1202) (hmask pH1202) 850 352 (true, H1202_cp1.1, H1202_cp1.2)) 1202 601 true) = true := by
  decide +kernel
theorem H1202_ok : RunOK pH1202 1202 (runFrom pH1202 (fmask pH1202) (cmask pH1202) (hmask pH1202) 850 352 (true, H1202_cp1.1, H1202_cp1.2)) ∧ ptTest pH1202 (runFrom pH1202 (fmask pH1202) (cmask pH1202) (hmask pH1202) 850 352 (true, H1202_cp1.1, H1202_cp1.2)) 1202 601 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1202_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1202_fin) true) H1202_seg1) (by decide) rfl H1202_fin ptTest_fst
theorem I1202_fin : (prmOK pI1202 1202 && intTest pI1202 (runFrom pI1202 (fmask pI1202) (cmask pI1202) (hmask pI1202) 1 1201 (true, (init pI1202), (init pI1202))) 1202 19 true) = true := by
  decide +kernel
theorem I1202_ok : RunOK pI1202 1202 (runFrom pI1202 (fmask pI1202) (cmask pI1202) (hmask pI1202) 1 1201 (true, (init pI1202), (init pI1202))) ∧ intTest pI1202 (runFrom pI1202 (fmask pI1202) (cmask pI1202) (hmask pI1202) 1 1201 (true, (init pI1202), (init pI1202))) 1202 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1202_fin) true) (by decide) rfl I1202_fin intTest_fst
theorem link1202 : linkOK pL1202 pH1202 pI1202 = true := by decide +kernel
theorem cvx1202 : ConvexBetweenHumps 1202 :=
  cvx_of L1202_ok H1202_ok I1202_ok link1202 (by decide)
theorem cenlink1202 : cenLinkOK pI1202 1202 = true := by decide +kernel
theorem cen1202 : CenterUniqueMin 1202 ∧ DipHyp 1202 ∧ OnePointHyps 1202 :=
  cen_of L1202_ok H1202_ok I1202_ok link1202 cenlink1202

/-! ### `N = 1203` -/

def pL1203 : Prm := ⟨76, 35, 38, 1205, 11, 18446744073709551616, 148781130459080646, 148781130459080646⟩
def pH1203 : Prm := ⟨76, 35, 38, 1205, 11, 18446744073709551616, 148783329482336198, 148783329482336198⟩
def pI1203 : Prm := ⟨66, 32, 31, 1205, 11, 18446744073709551616, 148781130459080646, 148783329482336198⟩
noncomputable def L1203_cp1 : Nat × Nat := t7val% (fastRun pL1203 1 850 (init pL1203) (init pL1203))
theorem L1203_seg1 : segOK pL1203 1 850 (init pL1203) (init pL1203) L1203_cp1.1 L1203_cp1.2 = true := by
  decide +kernel
theorem L1203_fin : (prmOK pL1203 1203 && ptTest pL1203 (runFrom pL1203 (fmask pL1203) (cmask pL1203) (hmask pL1203) 851 352 (true, L1203_cp1.1, L1203_cp1.2)) 1203 602 false) = true := by
  decide +kernel
theorem L1203_ok : RunOK pL1203 1203 (runFrom pL1203 (fmask pL1203) (cmask pL1203) (hmask pL1203) 851 352 (true, L1203_cp1.1, L1203_cp1.2)) ∧ ptTest pL1203 (runFrom pL1203 (fmask pL1203) (cmask pL1203) (hmask pL1203) 851 352 (true, L1203_cp1.1, L1203_cp1.2)) 1203 602 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1203_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1203_fin) true) L1203_seg1) (by decide) rfl L1203_fin ptTest_fst
noncomputable def H1203_cp1 : Nat × Nat := t7val% (fastRun pH1203 1 850 (init pH1203) (init pH1203))
theorem H1203_seg1 : segOK pH1203 1 850 (init pH1203) (init pH1203) H1203_cp1.1 H1203_cp1.2 = true := by
  decide +kernel
theorem H1203_fin : (prmOK pH1203 1203 && ptTest pH1203 (runFrom pH1203 (fmask pH1203) (cmask pH1203) (hmask pH1203) 851 352 (true, H1203_cp1.1, H1203_cp1.2)) 1203 602 true) = true := by
  decide +kernel
theorem H1203_ok : RunOK pH1203 1203 (runFrom pH1203 (fmask pH1203) (cmask pH1203) (hmask pH1203) 851 352 (true, H1203_cp1.1, H1203_cp1.2)) ∧ ptTest pH1203 (runFrom pH1203 (fmask pH1203) (cmask pH1203) (hmask pH1203) 851 352 (true, H1203_cp1.1, H1203_cp1.2)) 1203 602 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1203_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1203_fin) true) H1203_seg1) (by decide) rfl H1203_fin ptTest_fst
theorem I1203_fin : (prmOK pI1203 1203 && intTest pI1203 (runFrom pI1203 (fmask pI1203) (cmask pI1203) (hmask pI1203) 1 1202 (true, (init pI1203), (init pI1203))) 1203 19 false) = true := by
  decide +kernel
theorem I1203_ok : RunOK pI1203 1203 (runFrom pI1203 (fmask pI1203) (cmask pI1203) (hmask pI1203) 1 1202 (true, (init pI1203), (init pI1203))) ∧ intTest pI1203 (runFrom pI1203 (fmask pI1203) (cmask pI1203) (hmask pI1203) 1 1202 (true, (init pI1203), (init pI1203))) 1203 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1203_fin) true) (by decide) rfl I1203_fin intTest_fst
theorem link1203 : linkOK pL1203 pH1203 pI1203 = true := by decide +kernel
theorem cvx1203 : ConvexBetweenHumps 1203 :=
  cvx_of L1203_ok H1203_ok I1203_ok link1203 (by decide)

/-! ### `N = 1204` -/

def pL1204 : Prm := ⟨76, 35, 38, 1206, 11, 18446744073709551616, 148681598478755784, 148681598478755784⟩
def pH1204 : Prm := ⟨76, 35, 38, 1206, 11, 18446744073709551616, 148683797502011336, 148683797502011336⟩
def pI1204 : Prm := ⟨67, 32, 32, 1206, 11, 18446744073709551616, 148681598478755784, 148683797502011336⟩
noncomputable def L1204_cp1 : Nat × Nat := t7val% (fastRun pL1204 1 850 (init pL1204) (init pL1204))
theorem L1204_seg1 : segOK pL1204 1 850 (init pL1204) (init pL1204) L1204_cp1.1 L1204_cp1.2 = true := by
  decide +kernel
theorem L1204_fin : (prmOK pL1204 1204 && ptTest pL1204 (runFrom pL1204 (fmask pL1204) (cmask pL1204) (hmask pL1204) 851 353 (true, L1204_cp1.1, L1204_cp1.2)) 1204 602 false) = true := by
  decide +kernel
theorem L1204_ok : RunOK pL1204 1204 (runFrom pL1204 (fmask pL1204) (cmask pL1204) (hmask pL1204) 851 353 (true, L1204_cp1.1, L1204_cp1.2)) ∧ ptTest pL1204 (runFrom pL1204 (fmask pL1204) (cmask pL1204) (hmask pL1204) 851 353 (true, L1204_cp1.1, L1204_cp1.2)) 1204 602 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1204_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1204_fin) true) L1204_seg1) (by decide) rfl L1204_fin ptTest_fst
noncomputable def H1204_cp1 : Nat × Nat := t7val% (fastRun pH1204 1 850 (init pH1204) (init pH1204))
theorem H1204_seg1 : segOK pH1204 1 850 (init pH1204) (init pH1204) H1204_cp1.1 H1204_cp1.2 = true := by
  decide +kernel
theorem H1204_fin : (prmOK pH1204 1204 && ptTest pH1204 (runFrom pH1204 (fmask pH1204) (cmask pH1204) (hmask pH1204) 851 353 (true, H1204_cp1.1, H1204_cp1.2)) 1204 602 true) = true := by
  decide +kernel
theorem H1204_ok : RunOK pH1204 1204 (runFrom pH1204 (fmask pH1204) (cmask pH1204) (hmask pH1204) 851 353 (true, H1204_cp1.1, H1204_cp1.2)) ∧ ptTest pH1204 (runFrom pH1204 (fmask pH1204) (cmask pH1204) (hmask pH1204) 851 353 (true, H1204_cp1.1, H1204_cp1.2)) 1204 602 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1204_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1204_fin) true) H1204_seg1) (by decide) rfl H1204_fin ptTest_fst
theorem I1204_fin : (prmOK pI1204 1204 && intTest pI1204 (runFrom pI1204 (fmask pI1204) (cmask pI1204) (hmask pI1204) 1 1203 (true, (init pI1204), (init pI1204))) 1204 19 true) = true := by
  decide +kernel
theorem I1204_ok : RunOK pI1204 1204 (runFrom pI1204 (fmask pI1204) (cmask pI1204) (hmask pI1204) 1 1203 (true, (init pI1204), (init pI1204))) ∧ intTest pI1204 (runFrom pI1204 (fmask pI1204) (cmask pI1204) (hmask pI1204) 1 1203 (true, (init pI1204), (init pI1204))) 1204 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1204_fin) true) (by decide) rfl I1204_fin intTest_fst
theorem link1204 : linkOK pL1204 pH1204 pI1204 = true := by decide +kernel
theorem cvx1204 : ConvexBetweenHumps 1204 :=
  cvx_of L1204_ok H1204_ok I1204_ok link1204 (by decide)
theorem cenlink1204 : cenLinkOK pI1204 1204 = true := by decide +kernel
theorem cen1204 : CenterUniqueMin 1204 ∧ DipHyp 1204 ∧ OnePointHyps 1204 :=
  cen_of L1204_ok H1204_ok I1204_ok link1204 cenlink1204

/-! ### `N = 1205` -/

def pL1205 : Prm := ⟨76, 35, 38, 1207, 11, 18446744073709551616, 148582146245365759, 148582146245365759⟩
def pH1205 : Prm := ⟨76, 35, 38, 1207, 11, 18446744073709551616, 148584345268621311, 148584345268621311⟩
def pI1205 : Prm := ⟨67, 32, 32, 1207, 11, 18446744073709551616, 148582146245365759, 148584345268621311⟩
noncomputable def L1205_cp1 : Nat × Nat := t7val% (fastRun pL1205 1 851 (init pL1205) (init pL1205))
theorem L1205_seg1 : segOK pL1205 1 851 (init pL1205) (init pL1205) L1205_cp1.1 L1205_cp1.2 = true := by
  decide +kernel
theorem L1205_fin : (prmOK pL1205 1205 && ptTest pL1205 (runFrom pL1205 (fmask pL1205) (cmask pL1205) (hmask pL1205) 852 353 (true, L1205_cp1.1, L1205_cp1.2)) 1205 603 false) = true := by
  decide +kernel
theorem L1205_ok : RunOK pL1205 1205 (runFrom pL1205 (fmask pL1205) (cmask pL1205) (hmask pL1205) 852 353 (true, L1205_cp1.1, L1205_cp1.2)) ∧ ptTest pL1205 (runFrom pL1205 (fmask pL1205) (cmask pL1205) (hmask pL1205) 852 353 (true, L1205_cp1.1, L1205_cp1.2)) 1205 603 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1205_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1205_fin) true) L1205_seg1) (by decide) rfl L1205_fin ptTest_fst
noncomputable def H1205_cp1 : Nat × Nat := t7val% (fastRun pH1205 1 851 (init pH1205) (init pH1205))
theorem H1205_seg1 : segOK pH1205 1 851 (init pH1205) (init pH1205) H1205_cp1.1 H1205_cp1.2 = true := by
  decide +kernel
theorem H1205_fin : (prmOK pH1205 1205 && ptTest pH1205 (runFrom pH1205 (fmask pH1205) (cmask pH1205) (hmask pH1205) 852 353 (true, H1205_cp1.1, H1205_cp1.2)) 1205 603 true) = true := by
  decide +kernel
theorem H1205_ok : RunOK pH1205 1205 (runFrom pH1205 (fmask pH1205) (cmask pH1205) (hmask pH1205) 852 353 (true, H1205_cp1.1, H1205_cp1.2)) ∧ ptTest pH1205 (runFrom pH1205 (fmask pH1205) (cmask pH1205) (hmask pH1205) 852 353 (true, H1205_cp1.1, H1205_cp1.2)) 1205 603 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1205_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1205_fin) true) H1205_seg1) (by decide) rfl H1205_fin ptTest_fst
theorem I1205_fin : (prmOK pI1205 1205 && intTest pI1205 (runFrom pI1205 (fmask pI1205) (cmask pI1205) (hmask pI1205) 1 1204 (true, (init pI1205), (init pI1205))) 1205 19 false) = true := by
  decide +kernel
theorem I1205_ok : RunOK pI1205 1205 (runFrom pI1205 (fmask pI1205) (cmask pI1205) (hmask pI1205) 1 1204 (true, (init pI1205), (init pI1205))) ∧ intTest pI1205 (runFrom pI1205 (fmask pI1205) (cmask pI1205) (hmask pI1205) 1 1204 (true, (init pI1205), (init pI1205))) 1205 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1205_fin) true) (by decide) rfl I1205_fin intTest_fst
theorem link1205 : linkOK pL1205 pH1205 pI1205 = true := by decide +kernel
theorem cvx1205 : ConvexBetweenHumps 1205 :=
  cvx_of L1205_ok H1205_ok I1205_ok link1205 (by decide)

/-! ### `N = 1206` -/

def pL1206 : Prm := ⟨76, 35, 38, 1208, 11, 18446744073709551616, 148482904423710547, 148482904423710547⟩
def pH1206 : Prm := ⟨76, 35, 38, 1208, 11, 18446744073709551616, 148485103446966099, 148485103446966099⟩
def pI1206 : Prm := ⟨66, 32, 31, 1208, 11, 18446744073709551616, 148482904423710547, 148485103446966099⟩
noncomputable def L1206_cp1 : Nat × Nat := t7val% (fastRun pL1206 1 852 (init pL1206) (init pL1206))
theorem L1206_seg1 : segOK pL1206 1 852 (init pL1206) (init pL1206) L1206_cp1.1 L1206_cp1.2 = true := by
  decide +kernel
theorem L1206_fin : (prmOK pL1206 1206 && ptTest pL1206 (runFrom pL1206 (fmask pL1206) (cmask pL1206) (hmask pL1206) 853 353 (true, L1206_cp1.1, L1206_cp1.2)) 1206 603 false) = true := by
  decide +kernel
theorem L1206_ok : RunOK pL1206 1206 (runFrom pL1206 (fmask pL1206) (cmask pL1206) (hmask pL1206) 853 353 (true, L1206_cp1.1, L1206_cp1.2)) ∧ ptTest pL1206 (runFrom pL1206 (fmask pL1206) (cmask pL1206) (hmask pL1206) 853 353 (true, L1206_cp1.1, L1206_cp1.2)) 1206 603 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1206_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1206_fin) true) L1206_seg1) (by decide) rfl L1206_fin ptTest_fst
noncomputable def H1206_cp1 : Nat × Nat := t7val% (fastRun pH1206 1 852 (init pH1206) (init pH1206))
theorem H1206_seg1 : segOK pH1206 1 852 (init pH1206) (init pH1206) H1206_cp1.1 H1206_cp1.2 = true := by
  decide +kernel
theorem H1206_fin : (prmOK pH1206 1206 && ptTest pH1206 (runFrom pH1206 (fmask pH1206) (cmask pH1206) (hmask pH1206) 853 353 (true, H1206_cp1.1, H1206_cp1.2)) 1206 603 true) = true := by
  decide +kernel
theorem H1206_ok : RunOK pH1206 1206 (runFrom pH1206 (fmask pH1206) (cmask pH1206) (hmask pH1206) 853 353 (true, H1206_cp1.1, H1206_cp1.2)) ∧ ptTest pH1206 (runFrom pH1206 (fmask pH1206) (cmask pH1206) (hmask pH1206) 853 353 (true, H1206_cp1.1, H1206_cp1.2)) 1206 603 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1206_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1206_fin) true) H1206_seg1) (by decide) rfl H1206_fin ptTest_fst
theorem I1206_fin : (prmOK pI1206 1206 && intTest pI1206 (runFrom pI1206 (fmask pI1206) (cmask pI1206) (hmask pI1206) 1 1205 (true, (init pI1206), (init pI1206))) 1206 19 true) = true := by
  decide +kernel
theorem I1206_ok : RunOK pI1206 1206 (runFrom pI1206 (fmask pI1206) (cmask pI1206) (hmask pI1206) 1 1205 (true, (init pI1206), (init pI1206))) ∧ intTest pI1206 (runFrom pI1206 (fmask pI1206) (cmask pI1206) (hmask pI1206) 1 1205 (true, (init pI1206), (init pI1206))) 1206 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1206_fin) true) (by decide) rfl I1206_fin intTest_fst
theorem link1206 : linkOK pL1206 pH1206 pI1206 = true := by decide +kernel
theorem cvx1206 : ConvexBetweenHumps 1206 :=
  cvx_of L1206_ok H1206_ok I1206_ok link1206 (by decide)
theorem cenlink1206 : cenLinkOK pI1206 1206 = true := by decide +kernel
theorem cen1206 : CenterUniqueMin 1206 ∧ DipHyp 1206 ∧ OnePointHyps 1206 :=
  cen_of L1206_ok H1206_ok I1206_ok link1206 cenlink1206

/-! ### `N = 1207` -/

def pL1207 : Prm := ⟨76, 35, 38, 1209, 11, 18446744073709551616, 148383742024290584, 148383742024290584⟩
def pH1207 : Prm := ⟨76, 35, 38, 1209, 11, 18446744073709551616, 148385941047546136, 148385941047546136⟩
def pI1207 : Prm := ⟨67, 32, 32, 1209, 11, 18446744073709551616, 148383742024290584, 148385941047546136⟩
noncomputable def L1207_cp1 : Nat × Nat := t7val% (fastRun pL1207 1 852 (init pL1207) (init pL1207))
theorem L1207_seg1 : segOK pL1207 1 852 (init pL1207) (init pL1207) L1207_cp1.1 L1207_cp1.2 = true := by
  decide +kernel
theorem L1207_fin : (prmOK pL1207 1207 && ptTest pL1207 (runFrom pL1207 (fmask pL1207) (cmask pL1207) (hmask pL1207) 853 354 (true, L1207_cp1.1, L1207_cp1.2)) 1207 604 false) = true := by
  decide +kernel
theorem L1207_ok : RunOK pL1207 1207 (runFrom pL1207 (fmask pL1207) (cmask pL1207) (hmask pL1207) 853 354 (true, L1207_cp1.1, L1207_cp1.2)) ∧ ptTest pL1207 (runFrom pL1207 (fmask pL1207) (cmask pL1207) (hmask pL1207) 853 354 (true, L1207_cp1.1, L1207_cp1.2)) 1207 604 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1207_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1207_fin) true) L1207_seg1) (by decide) rfl L1207_fin ptTest_fst
noncomputable def H1207_cp1 : Nat × Nat := t7val% (fastRun pH1207 1 852 (init pH1207) (init pH1207))
theorem H1207_seg1 : segOK pH1207 1 852 (init pH1207) (init pH1207) H1207_cp1.1 H1207_cp1.2 = true := by
  decide +kernel
theorem H1207_fin : (prmOK pH1207 1207 && ptTest pH1207 (runFrom pH1207 (fmask pH1207) (cmask pH1207) (hmask pH1207) 853 354 (true, H1207_cp1.1, H1207_cp1.2)) 1207 604 true) = true := by
  decide +kernel
theorem H1207_ok : RunOK pH1207 1207 (runFrom pH1207 (fmask pH1207) (cmask pH1207) (hmask pH1207) 853 354 (true, H1207_cp1.1, H1207_cp1.2)) ∧ ptTest pH1207 (runFrom pH1207 (fmask pH1207) (cmask pH1207) (hmask pH1207) 853 354 (true, H1207_cp1.1, H1207_cp1.2)) 1207 604 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1207_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1207_fin) true) H1207_seg1) (by decide) rfl H1207_fin ptTest_fst
theorem I1207_fin : (prmOK pI1207 1207 && intTest pI1207 (runFrom pI1207 (fmask pI1207) (cmask pI1207) (hmask pI1207) 1 1206 (true, (init pI1207), (init pI1207))) 1207 19 false) = true := by
  decide +kernel
theorem I1207_ok : RunOK pI1207 1207 (runFrom pI1207 (fmask pI1207) (cmask pI1207) (hmask pI1207) 1 1206 (true, (init pI1207), (init pI1207))) ∧ intTest pI1207 (runFrom pI1207 (fmask pI1207) (cmask pI1207) (hmask pI1207) 1 1206 (true, (init pI1207), (init pI1207))) 1207 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1207_fin) true) (by decide) rfl I1207_fin intTest_fst
theorem link1207 : linkOK pL1207 pH1207 pI1207 = true := by decide +kernel
theorem cvx1207 : ConvexBetweenHumps 1207 :=
  cvx_of L1207_ok H1207_ok I1207_ok link1207 (by decide)

/-! ### `N = 1208` -/

def pL1208 : Prm := ⟨76, 35, 38, 1210, 11, 18446744073709551616, 148284789052305615, 148284789052305615⟩
def pH1208 : Prm := ⟨76, 35, 38, 1210, 11, 18446744073709551616, 148286988075561167, 148286988075561167⟩
def pI1208 : Prm := ⟨67, 32, 32, 1210, 11, 18446744073709551616, 148284789052305615, 148286988075561167⟩
noncomputable def L1208_cp1 : Nat × Nat := t7val% (fastRun pL1208 1 853 (init pL1208) (init pL1208))
theorem L1208_seg1 : segOK pL1208 1 853 (init pL1208) (init pL1208) L1208_cp1.1 L1208_cp1.2 = true := by
  decide +kernel
theorem L1208_fin : (prmOK pL1208 1208 && ptTest pL1208 (runFrom pL1208 (fmask pL1208) (cmask pL1208) (hmask pL1208) 854 354 (true, L1208_cp1.1, L1208_cp1.2)) 1208 604 false) = true := by
  decide +kernel
theorem L1208_ok : RunOK pL1208 1208 (runFrom pL1208 (fmask pL1208) (cmask pL1208) (hmask pL1208) 854 354 (true, L1208_cp1.1, L1208_cp1.2)) ∧ ptTest pL1208 (runFrom pL1208 (fmask pL1208) (cmask pL1208) (hmask pL1208) 854 354 (true, L1208_cp1.1, L1208_cp1.2)) 1208 604 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1208_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1208_fin) true) L1208_seg1) (by decide) rfl L1208_fin ptTest_fst
noncomputable def H1208_cp1 : Nat × Nat := t7val% (fastRun pH1208 1 853 (init pH1208) (init pH1208))
theorem H1208_seg1 : segOK pH1208 1 853 (init pH1208) (init pH1208) H1208_cp1.1 H1208_cp1.2 = true := by
  decide +kernel
theorem H1208_fin : (prmOK pH1208 1208 && ptTest pH1208 (runFrom pH1208 (fmask pH1208) (cmask pH1208) (hmask pH1208) 854 354 (true, H1208_cp1.1, H1208_cp1.2)) 1208 604 true) = true := by
  decide +kernel
theorem H1208_ok : RunOK pH1208 1208 (runFrom pH1208 (fmask pH1208) (cmask pH1208) (hmask pH1208) 854 354 (true, H1208_cp1.1, H1208_cp1.2)) ∧ ptTest pH1208 (runFrom pH1208 (fmask pH1208) (cmask pH1208) (hmask pH1208) 854 354 (true, H1208_cp1.1, H1208_cp1.2)) 1208 604 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1208_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1208_fin) true) H1208_seg1) (by decide) rfl H1208_fin ptTest_fst
theorem I1208_fin : (prmOK pI1208 1208 && intTest pI1208 (runFrom pI1208 (fmask pI1208) (cmask pI1208) (hmask pI1208) 1 1207 (true, (init pI1208), (init pI1208))) 1208 19 true) = true := by
  decide +kernel
theorem I1208_ok : RunOK pI1208 1208 (runFrom pI1208 (fmask pI1208) (cmask pI1208) (hmask pI1208) 1 1207 (true, (init pI1208), (init pI1208))) ∧ intTest pI1208 (runFrom pI1208 (fmask pI1208) (cmask pI1208) (hmask pI1208) 1 1207 (true, (init pI1208), (init pI1208))) 1208 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1208_fin) true) (by decide) rfl I1208_fin intTest_fst
theorem link1208 : linkOK pL1208 pH1208 pI1208 = true := by decide +kernel
theorem cvx1208 : ConvexBetweenHumps 1208 :=
  cvx_of L1208_ok H1208_ok I1208_ok link1208 (by decide)
theorem cenlink1208 : cenLinkOK pI1208 1208 = true := by decide +kernel
theorem cen1208 : CenterUniqueMin 1208 ∧ DipHyp 1208 ∧ OnePointHyps 1208 :=
  cen_of L1208_ok H1208_ok I1208_ok link1208 cenlink1208

/-! ### `N = 1209` -/

def pL1209 : Prm := ⟨76, 35, 38, 1211, 11, 18446744073709551616, 148185915179608746, 148185915179608746⟩
def pH1209 : Prm := ⟨76, 35, 38, 1211, 11, 18446744073709551616, 148188114202864298, 148188114202864298⟩
def pI1209 : Prm := ⟨67, 32, 32, 1211, 11, 18446744073709551616, 148185915179608746, 148188114202864298⟩
noncomputable def L1209_cp1 : Nat × Nat := t7val% (fastRun pL1209 1 854 (init pL1209) (init pL1209))
theorem L1209_seg1 : segOK pL1209 1 854 (init pL1209) (init pL1209) L1209_cp1.1 L1209_cp1.2 = true := by
  decide +kernel
theorem L1209_fin : (prmOK pL1209 1209 && ptTest pL1209 (runFrom pL1209 (fmask pL1209) (cmask pL1209) (hmask pL1209) 855 354 (true, L1209_cp1.1, L1209_cp1.2)) 1209 605 false) = true := by
  decide +kernel
theorem L1209_ok : RunOK pL1209 1209 (runFrom pL1209 (fmask pL1209) (cmask pL1209) (hmask pL1209) 855 354 (true, L1209_cp1.1, L1209_cp1.2)) ∧ ptTest pL1209 (runFrom pL1209 (fmask pL1209) (cmask pL1209) (hmask pL1209) 855 354 (true, L1209_cp1.1, L1209_cp1.2)) 1209 605 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1209_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1209_fin) true) L1209_seg1) (by decide) rfl L1209_fin ptTest_fst
noncomputable def H1209_cp1 : Nat × Nat := t7val% (fastRun pH1209 1 854 (init pH1209) (init pH1209))
theorem H1209_seg1 : segOK pH1209 1 854 (init pH1209) (init pH1209) H1209_cp1.1 H1209_cp1.2 = true := by
  decide +kernel
theorem H1209_fin : (prmOK pH1209 1209 && ptTest pH1209 (runFrom pH1209 (fmask pH1209) (cmask pH1209) (hmask pH1209) 855 354 (true, H1209_cp1.1, H1209_cp1.2)) 1209 605 true) = true := by
  decide +kernel
theorem H1209_ok : RunOK pH1209 1209 (runFrom pH1209 (fmask pH1209) (cmask pH1209) (hmask pH1209) 855 354 (true, H1209_cp1.1, H1209_cp1.2)) ∧ ptTest pH1209 (runFrom pH1209 (fmask pH1209) (cmask pH1209) (hmask pH1209) 855 354 (true, H1209_cp1.1, H1209_cp1.2)) 1209 605 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1209_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1209_fin) true) H1209_seg1) (by decide) rfl H1209_fin ptTest_fst
theorem I1209_fin : (prmOK pI1209 1209 && intTest pI1209 (runFrom pI1209 (fmask pI1209) (cmask pI1209) (hmask pI1209) 1 1208 (true, (init pI1209), (init pI1209))) 1209 19 false) = true := by
  decide +kernel
theorem I1209_ok : RunOK pI1209 1209 (runFrom pI1209 (fmask pI1209) (cmask pI1209) (hmask pI1209) 1 1208 (true, (init pI1209), (init pI1209))) ∧ intTest pI1209 (runFrom pI1209 (fmask pI1209) (cmask pI1209) (hmask pI1209) 1 1208 (true, (init pI1209), (init pI1209))) 1209 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1209_fin) true) (by decide) rfl I1209_fin intTest_fst
theorem link1209 : linkOK pL1209 pH1209 pI1209 = true := by decide +kernel
theorem cvx1209 : ConvexBetweenHumps 1209 :=
  cvx_of L1209_ok H1209_ok I1209_ok link1209 (by decide)

/-! ### `N = 1210` -/

def pL1210 : Prm := ⟨76, 35, 38, 1212, 11, 18446744073709551616, 148087249756300503, 148087249756300503⟩
def pH1210 : Prm := ⟨76, 35, 38, 1212, 11, 18446744073709551616, 148089448779556055, 148089448779556055⟩
def pI1210 : Prm := ⟨67, 32, 32, 1212, 11, 18446744073709551616, 148087249756300503, 148089448779556055⟩
noncomputable def L1210_cp1 : Nat × Nat := t7val% (fastRun pL1210 1 855 (init pL1210) (init pL1210))
theorem L1210_seg1 : segOK pL1210 1 855 (init pL1210) (init pL1210) L1210_cp1.1 L1210_cp1.2 = true := by
  decide +kernel
theorem L1210_fin : (prmOK pL1210 1210 && ptTest pL1210 (runFrom pL1210 (fmask pL1210) (cmask pL1210) (hmask pL1210) 856 354 (true, L1210_cp1.1, L1210_cp1.2)) 1210 605 false) = true := by
  decide +kernel
theorem L1210_ok : RunOK pL1210 1210 (runFrom pL1210 (fmask pL1210) (cmask pL1210) (hmask pL1210) 856 354 (true, L1210_cp1.1, L1210_cp1.2)) ∧ ptTest pL1210 (runFrom pL1210 (fmask pL1210) (cmask pL1210) (hmask pL1210) 856 354 (true, L1210_cp1.1, L1210_cp1.2)) 1210 605 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1210_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1210_fin) true) L1210_seg1) (by decide) rfl L1210_fin ptTest_fst
noncomputable def H1210_cp1 : Nat × Nat := t7val% (fastRun pH1210 1 855 (init pH1210) (init pH1210))
theorem H1210_seg1 : segOK pH1210 1 855 (init pH1210) (init pH1210) H1210_cp1.1 H1210_cp1.2 = true := by
  decide +kernel
theorem H1210_fin : (prmOK pH1210 1210 && ptTest pH1210 (runFrom pH1210 (fmask pH1210) (cmask pH1210) (hmask pH1210) 856 354 (true, H1210_cp1.1, H1210_cp1.2)) 1210 605 true) = true := by
  decide +kernel
theorem H1210_ok : RunOK pH1210 1210 (runFrom pH1210 (fmask pH1210) (cmask pH1210) (hmask pH1210) 856 354 (true, H1210_cp1.1, H1210_cp1.2)) ∧ ptTest pH1210 (runFrom pH1210 (fmask pH1210) (cmask pH1210) (hmask pH1210) 856 354 (true, H1210_cp1.1, H1210_cp1.2)) 1210 605 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1210_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1210_fin) true) H1210_seg1) (by decide) rfl H1210_fin ptTest_fst
theorem I1210_fin : (prmOK pI1210 1210 && intTest pI1210 (runFrom pI1210 (fmask pI1210) (cmask pI1210) (hmask pI1210) 1 1209 (true, (init pI1210), (init pI1210))) 1210 19 true) = true := by
  decide +kernel
theorem I1210_ok : RunOK pI1210 1210 (runFrom pI1210 (fmask pI1210) (cmask pI1210) (hmask pI1210) 1 1209 (true, (init pI1210), (init pI1210))) ∧ intTest pI1210 (runFrom pI1210 (fmask pI1210) (cmask pI1210) (hmask pI1210) 1 1209 (true, (init pI1210), (init pI1210))) 1210 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1210_fin) true) (by decide) rfl I1210_fin intTest_fst
theorem link1210 : linkOK pL1210 pH1210 pI1210 = true := by decide +kernel
theorem cvx1210 : ConvexBetweenHumps 1210 :=
  cvx_of L1210_ok H1210_ok I1210_ok link1210 (by decide)
theorem cenlink1210 : cenLinkOK pI1210 1210 = true := by decide +kernel
theorem cen1210 : CenterUniqueMin 1210 ∧ DipHyp 1210 ∧ OnePointHyps 1210 :=
  cen_of L1210_ok H1210_ok I1210_ok link1210 cenlink1210

/-! ### `N = 1211` -/

def pL1211 : Prm := ⟨76, 35, 38, 1213, 11, 18446744073709551616, 147988663111140991, 147988663111140991⟩
def pH1211 : Prm := ⟨76, 35, 38, 1213, 11, 18446744073709551616, 147990862134396543, 147990862134396543⟩
def pI1211 : Prm := ⟨67, 32, 32, 1213, 11, 18446744073709551616, 147988663111140991, 147990862134396543⟩
noncomputable def L1211_cp1 : Nat × Nat := t7val% (fastRun pL1211 1 855 (init pL1211) (init pL1211))
theorem L1211_seg1 : segOK pL1211 1 855 (init pL1211) (init pL1211) L1211_cp1.1 L1211_cp1.2 = true := by
  decide +kernel
theorem L1211_fin : (prmOK pL1211 1211 && ptTest pL1211 (runFrom pL1211 (fmask pL1211) (cmask pL1211) (hmask pL1211) 856 355 (true, L1211_cp1.1, L1211_cp1.2)) 1211 606 false) = true := by
  decide +kernel
theorem L1211_ok : RunOK pL1211 1211 (runFrom pL1211 (fmask pL1211) (cmask pL1211) (hmask pL1211) 856 355 (true, L1211_cp1.1, L1211_cp1.2)) ∧ ptTest pL1211 (runFrom pL1211 (fmask pL1211) (cmask pL1211) (hmask pL1211) 856 355 (true, L1211_cp1.1, L1211_cp1.2)) 1211 606 false = true :=
  fin_run (runOK_seg (prmOK_of_and L1211_fin) (by decide) (by decide) (runOK_init (prmOK_of_and L1211_fin) true) L1211_seg1) (by decide) rfl L1211_fin ptTest_fst
noncomputable def H1211_cp1 : Nat × Nat := t7val% (fastRun pH1211 1 855 (init pH1211) (init pH1211))
theorem H1211_seg1 : segOK pH1211 1 855 (init pH1211) (init pH1211) H1211_cp1.1 H1211_cp1.2 = true := by
  decide +kernel
theorem H1211_fin : (prmOK pH1211 1211 && ptTest pH1211 (runFrom pH1211 (fmask pH1211) (cmask pH1211) (hmask pH1211) 856 355 (true, H1211_cp1.1, H1211_cp1.2)) 1211 606 true) = true := by
  decide +kernel
theorem H1211_ok : RunOK pH1211 1211 (runFrom pH1211 (fmask pH1211) (cmask pH1211) (hmask pH1211) 856 355 (true, H1211_cp1.1, H1211_cp1.2)) ∧ ptTest pH1211 (runFrom pH1211 (fmask pH1211) (cmask pH1211) (hmask pH1211) 856 355 (true, H1211_cp1.1, H1211_cp1.2)) 1211 606 true = true :=
  fin_run (runOK_seg (prmOK_of_and H1211_fin) (by decide) (by decide) (runOK_init (prmOK_of_and H1211_fin) true) H1211_seg1) (by decide) rfl H1211_fin ptTest_fst
theorem I1211_fin : (prmOK pI1211 1211 && intTest pI1211 (runFrom pI1211 (fmask pI1211) (cmask pI1211) (hmask pI1211) 1 1210 (true, (init pI1211), (init pI1211))) 1211 19 false) = true := by
  decide +kernel
theorem I1211_ok : RunOK pI1211 1211 (runFrom pI1211 (fmask pI1211) (cmask pI1211) (hmask pI1211) 1 1210 (true, (init pI1211), (init pI1211))) ∧ intTest pI1211 (runFrom pI1211 (fmask pI1211) (cmask pI1211) (hmask pI1211) 1 1210 (true, (init pI1211), (init pI1211))) 1211 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1211_fin) true) (by decide) rfl I1211_fin intTest_fst
theorem link1211 : linkOK pL1211 pH1211 pI1211 = true := by decide +kernel
theorem cvx1211 : ConvexBetweenHumps 1211 :=
  cvx_of L1211_ok H1211_ok I1211_ok link1211 (by decide)

/-! ### The range -/

theorem cvx_1183_1211 {N : ℕ} (h1 : 1183 ≤ N) (h2 : N ≤ 1211) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1196
  · by_cases h4 : N ≤ 1189
    · by_cases h6 : N ≤ 1185
      · by_cases h8 : N ≤ 1183
        · obtain rfl : N = 1183 := by omega
          exact cvx1183
        · by_cases h10 : N ≤ 1184
          · obtain rfl : N = 1184 := by omega
            exact cvx1184
          · obtain rfl : N = 1185 := by omega
            exact cvx1185
      · by_cases h8 : N ≤ 1187
        · by_cases h10 : N ≤ 1186
          · obtain rfl : N = 1186 := by omega
            exact cvx1186
          · obtain rfl : N = 1187 := by omega
            exact cvx1187
        · by_cases h10 : N ≤ 1188
          · obtain rfl : N = 1188 := by omega
            exact cvx1188
          · obtain rfl : N = 1189 := by omega
            exact cvx1189
    · by_cases h6 : N ≤ 1192
      · by_cases h8 : N ≤ 1190
        · obtain rfl : N = 1190 := by omega
          exact cvx1190
        · by_cases h10 : N ≤ 1191
          · obtain rfl : N = 1191 := by omega
            exact cvx1191
          · obtain rfl : N = 1192 := by omega
            exact cvx1192
      · by_cases h8 : N ≤ 1194
        · by_cases h10 : N ≤ 1193
          · obtain rfl : N = 1193 := by omega
            exact cvx1193
          · obtain rfl : N = 1194 := by omega
            exact cvx1194
        · by_cases h10 : N ≤ 1195
          · obtain rfl : N = 1195 := by omega
            exact cvx1195
          · obtain rfl : N = 1196 := by omega
            exact cvx1196
  · by_cases h4 : N ≤ 1203
    · by_cases h6 : N ≤ 1199
      · by_cases h8 : N ≤ 1197
        · obtain rfl : N = 1197 := by omega
          exact cvx1197
        · by_cases h10 : N ≤ 1198
          · obtain rfl : N = 1198 := by omega
            exact cvx1198
          · obtain rfl : N = 1199 := by omega
            exact cvx1199
      · by_cases h8 : N ≤ 1201
        · by_cases h10 : N ≤ 1200
          · obtain rfl : N = 1200 := by omega
            exact cvx1200
          · obtain rfl : N = 1201 := by omega
            exact cvx1201
        · by_cases h10 : N ≤ 1202
          · obtain rfl : N = 1202 := by omega
            exact cvx1202
          · obtain rfl : N = 1203 := by omega
            exact cvx1203
    · by_cases h6 : N ≤ 1207
      · by_cases h8 : N ≤ 1205
        · by_cases h10 : N ≤ 1204
          · obtain rfl : N = 1204 := by omega
            exact cvx1204
          · obtain rfl : N = 1205 := by omega
            exact cvx1205
        · by_cases h10 : N ≤ 1206
          · obtain rfl : N = 1206 := by omega
            exact cvx1206
          · obtain rfl : N = 1207 := by omega
            exact cvx1207
      · by_cases h8 : N ≤ 1209
        · by_cases h10 : N ≤ 1208
          · obtain rfl : N = 1208 := by omega
            exact cvx1208
          · obtain rfl : N = 1209 := by omega
            exact cvx1209
        · by_cases h10 : N ≤ 1210
          · obtain rfl : N = 1210 := by omega
            exact cvx1210
          · obtain rfl : N = 1211 := by omega
            exact cvx1211

theorem cen_1183_1211 {N : ℕ} (h1 : 1183 ≤ N) (h2 : N ≤ 1211) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1196
  · by_cases h4 : N ≤ 1188
    · by_cases h6 : N ≤ 1184
      · obtain rfl : N = 1184 := by omega
        exact cen1184
      · by_cases h8 : N ≤ 1186
        · obtain rfl : N = 1186 := by omega
          exact cen1186
        · obtain rfl : N = 1188 := by omega
          exact cen1188
    · by_cases h6 : N ≤ 1192
      · by_cases h8 : N ≤ 1190
        · obtain rfl : N = 1190 := by omega
          exact cen1190
        · obtain rfl : N = 1192 := by omega
          exact cen1192
      · by_cases h8 : N ≤ 1194
        · obtain rfl : N = 1194 := by omega
          exact cen1194
        · obtain rfl : N = 1196 := by omega
          exact cen1196
  · by_cases h4 : N ≤ 1202
    · by_cases h6 : N ≤ 1198
      · obtain rfl : N = 1198 := by omega
        exact cen1198
      · by_cases h8 : N ≤ 1200
        · obtain rfl : N = 1200 := by omega
          exact cen1200
        · obtain rfl : N = 1202 := by omega
          exact cen1202
    · by_cases h6 : N ≤ 1206
      · by_cases h8 : N ≤ 1204
        · obtain rfl : N = 1204 := by omega
          exact cen1204
        · obtain rfl : N = 1206 := by omega
          exact cen1206
      · by_cases h8 : N ≤ 1208
        · obtain rfl : N = 1208 := by omega
          exact cen1208
        · obtain rfl : N = 1210 := by omega
          exact cen1210

end Kagey131.PaperD.T7
