import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1120, …, 1151` (generated)

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

/-! ### `N = 1120` -/

def pL1120 : Prm := ⟨76, 35, 38, 1122, 11, 18446744073709551616, 157586398140618738, 157586398140618738⟩
def pH1120 : Prm := ⟨76, 35, 38, 1122, 11, 18446744073709551616, 157588597163874290, 157588597163874290⟩
def pI1120 : Prm := ⟨65, 32, 30, 1122, 11, 18446744073709551616, 157586398140618738, 157588597163874290⟩
theorem L1120_fin : (prmOK pL1120 1120 && ptTest pL1120 (runFrom pL1120 (fmask pL1120) (cmask pL1120) (hmask pL1120) 1 1119 (true, (init pL1120), (init pL1120))) 1120 560 false) = true := by
  decide +kernel
theorem L1120_ok : RunOK pL1120 1120 (runFrom pL1120 (fmask pL1120) (cmask pL1120) (hmask pL1120) 1 1119 (true, (init pL1120), (init pL1120))) ∧ ptTest pL1120 (runFrom pL1120 (fmask pL1120) (cmask pL1120) (hmask pL1120) 1 1119 (true, (init pL1120), (init pL1120))) 1120 560 false = true :=
  fin_run (runOK_init (prmOK_of_and L1120_fin) true) (by decide) rfl L1120_fin ptTest_fst
theorem H1120_fin : (prmOK pH1120 1120 && ptTest pH1120 (runFrom pH1120 (fmask pH1120) (cmask pH1120) (hmask pH1120) 1 1119 (true, (init pH1120), (init pH1120))) 1120 560 true) = true := by
  decide +kernel
theorem H1120_ok : RunOK pH1120 1120 (runFrom pH1120 (fmask pH1120) (cmask pH1120) (hmask pH1120) 1 1119 (true, (init pH1120), (init pH1120))) ∧ ptTest pH1120 (runFrom pH1120 (fmask pH1120) (cmask pH1120) (hmask pH1120) 1 1119 (true, (init pH1120), (init pH1120))) 1120 560 true = true :=
  fin_run (runOK_init (prmOK_of_and H1120_fin) true) (by decide) rfl H1120_fin ptTest_fst
theorem I1120_fin : (prmOK pI1120 1120 && intTest pI1120 (runFrom pI1120 (fmask pI1120) (cmask pI1120) (hmask pI1120) 1 1119 (true, (init pI1120), (init pI1120))) 1120 18 true) = true := by
  decide +kernel
theorem I1120_ok : RunOK pI1120 1120 (runFrom pI1120 (fmask pI1120) (cmask pI1120) (hmask pI1120) 1 1119 (true, (init pI1120), (init pI1120))) ∧ intTest pI1120 (runFrom pI1120 (fmask pI1120) (cmask pI1120) (hmask pI1120) 1 1119 (true, (init pI1120), (init pI1120))) 1120 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1120_fin) true) (by decide) rfl I1120_fin intTest_fst
theorem link1120 : linkOK pL1120 pH1120 pI1120 = true := by decide +kernel
theorem cvx1120 : ConvexBetweenHumps 1120 :=
  cvx_of L1120_ok H1120_ok I1120_ok link1120 (by decide)
theorem cenlink1120 : cenLinkOK pI1120 1120 = true := by decide +kernel
theorem cen1120 : CenterUniqueMin 1120 ∧ DipHyp 1120 ∧ OnePointHyps 1120 :=
  cen_of L1120_ok H1120_ok I1120_ok link1120 cenlink1120

/-! ### `N = 1121` -/

def pL1121 : Prm := ⟨76, 35, 38, 1123, 11, 18446744073709551616, 157473476621120826, 157473476621120826⟩
def pH1121 : Prm := ⟨76, 35, 38, 1123, 11, 18446744073709551616, 157475675644376378, 157475675644376378⟩
def pI1121 : Prm := ⟨65, 32, 30, 1123, 11, 18446744073709551616, 157473476621120826, 157475675644376378⟩
theorem L1121_fin : (prmOK pL1121 1121 && ptTest pL1121 (runFrom pL1121 (fmask pL1121) (cmask pL1121) (hmask pL1121) 1 1120 (true, (init pL1121), (init pL1121))) 1121 561 false) = true := by
  decide +kernel
theorem L1121_ok : RunOK pL1121 1121 (runFrom pL1121 (fmask pL1121) (cmask pL1121) (hmask pL1121) 1 1120 (true, (init pL1121), (init pL1121))) ∧ ptTest pL1121 (runFrom pL1121 (fmask pL1121) (cmask pL1121) (hmask pL1121) 1 1120 (true, (init pL1121), (init pL1121))) 1121 561 false = true :=
  fin_run (runOK_init (prmOK_of_and L1121_fin) true) (by decide) rfl L1121_fin ptTest_fst
theorem H1121_fin : (prmOK pH1121 1121 && ptTest pH1121 (runFrom pH1121 (fmask pH1121) (cmask pH1121) (hmask pH1121) 1 1120 (true, (init pH1121), (init pH1121))) 1121 561 true) = true := by
  decide +kernel
theorem H1121_ok : RunOK pH1121 1121 (runFrom pH1121 (fmask pH1121) (cmask pH1121) (hmask pH1121) 1 1120 (true, (init pH1121), (init pH1121))) ∧ ptTest pH1121 (runFrom pH1121 (fmask pH1121) (cmask pH1121) (hmask pH1121) 1 1120 (true, (init pH1121), (init pH1121))) 1121 561 true = true :=
  fin_run (runOK_init (prmOK_of_and H1121_fin) true) (by decide) rfl H1121_fin ptTest_fst
theorem I1121_fin : (prmOK pI1121 1121 && intTest pI1121 (runFrom pI1121 (fmask pI1121) (cmask pI1121) (hmask pI1121) 1 1120 (true, (init pI1121), (init pI1121))) 1121 18 false) = true := by
  decide +kernel
theorem I1121_ok : RunOK pI1121 1121 (runFrom pI1121 (fmask pI1121) (cmask pI1121) (hmask pI1121) 1 1120 (true, (init pI1121), (init pI1121))) ∧ intTest pI1121 (runFrom pI1121 (fmask pI1121) (cmask pI1121) (hmask pI1121) 1 1120 (true, (init pI1121), (init pI1121))) 1121 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1121_fin) true) (by decide) rfl I1121_fin intTest_fst
theorem link1121 : linkOK pL1121 pH1121 pI1121 = true := by decide +kernel
theorem cvx1121 : ConvexBetweenHumps 1121 :=
  cvx_of L1121_ok H1121_ok I1121_ok link1121 (by decide)

/-! ### `N = 1122` -/

def pL1122 : Prm := ⟨76, 35, 38, 1124, 11, 18446744073709551616, 157360813191882371, 157360813191882371⟩
def pH1122 : Prm := ⟨76, 35, 38, 1124, 11, 18446744073709551616, 157363012215137923, 157363012215137923⟩
def pI1122 : Prm := ⟨66, 32, 31, 1124, 11, 18446744073709551616, 157360813191882371, 157363012215137923⟩
theorem L1122_fin : (prmOK pL1122 1122 && ptTest pL1122 (runFrom pL1122 (fmask pL1122) (cmask pL1122) (hmask pL1122) 1 1121 (true, (init pL1122), (init pL1122))) 1122 561 false) = true := by
  decide +kernel
theorem L1122_ok : RunOK pL1122 1122 (runFrom pL1122 (fmask pL1122) (cmask pL1122) (hmask pL1122) 1 1121 (true, (init pL1122), (init pL1122))) ∧ ptTest pL1122 (runFrom pL1122 (fmask pL1122) (cmask pL1122) (hmask pL1122) 1 1121 (true, (init pL1122), (init pL1122))) 1122 561 false = true :=
  fin_run (runOK_init (prmOK_of_and L1122_fin) true) (by decide) rfl L1122_fin ptTest_fst
theorem H1122_fin : (prmOK pH1122 1122 && ptTest pH1122 (runFrom pH1122 (fmask pH1122) (cmask pH1122) (hmask pH1122) 1 1121 (true, (init pH1122), (init pH1122))) 1122 561 true) = true := by
  decide +kernel
theorem H1122_ok : RunOK pH1122 1122 (runFrom pH1122 (fmask pH1122) (cmask pH1122) (hmask pH1122) 1 1121 (true, (init pH1122), (init pH1122))) ∧ ptTest pH1122 (runFrom pH1122 (fmask pH1122) (cmask pH1122) (hmask pH1122) 1 1121 (true, (init pH1122), (init pH1122))) 1122 561 true = true :=
  fin_run (runOK_init (prmOK_of_and H1122_fin) true) (by decide) rfl H1122_fin ptTest_fst
theorem I1122_fin : (prmOK pI1122 1122 && intTest pI1122 (runFrom pI1122 (fmask pI1122) (cmask pI1122) (hmask pI1122) 1 1121 (true, (init pI1122), (init pI1122))) 1122 18 true) = true := by
  decide +kernel
theorem I1122_ok : RunOK pI1122 1122 (runFrom pI1122 (fmask pI1122) (cmask pI1122) (hmask pI1122) 1 1121 (true, (init pI1122), (init pI1122))) ∧ intTest pI1122 (runFrom pI1122 (fmask pI1122) (cmask pI1122) (hmask pI1122) 1 1121 (true, (init pI1122), (init pI1122))) 1122 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1122_fin) true) (by decide) rfl I1122_fin intTest_fst
theorem link1122 : linkOK pL1122 pH1122 pI1122 = true := by decide +kernel
theorem cvx1122 : ConvexBetweenHumps 1122 :=
  cvx_of L1122_ok H1122_ok I1122_ok link1122 (by decide)
theorem cenlink1122 : cenLinkOK pI1122 1122 = true := by decide +kernel
theorem cen1122 : CenterUniqueMin 1122 ∧ DipHyp 1122 ∧ OnePointHyps 1122 :=
  cen_of L1122_ok H1122_ok I1122_ok link1122 cenlink1122

/-! ### `N = 1123` -/

def pL1123 : Prm := ⟨76, 35, 38, 1125, 11, 18446744073709551616, 157248244534433355, 157248244534433355⟩
def pH1123 : Prm := ⟨76, 35, 38, 1125, 11, 18446744073709551616, 157250443557688907, 157250443557688907⟩
def pI1123 : Prm := ⟨65, 32, 30, 1125, 11, 18446744073709551616, 157248244534433355, 157250443557688907⟩
theorem L1123_fin : (prmOK pL1123 1123 && ptTest pL1123 (runFrom pL1123 (fmask pL1123) (cmask pL1123) (hmask pL1123) 1 1122 (true, (init pL1123), (init pL1123))) 1123 562 false) = true := by
  decide +kernel
theorem L1123_ok : RunOK pL1123 1123 (runFrom pL1123 (fmask pL1123) (cmask pL1123) (hmask pL1123) 1 1122 (true, (init pL1123), (init pL1123))) ∧ ptTest pL1123 (runFrom pL1123 (fmask pL1123) (cmask pL1123) (hmask pL1123) 1 1122 (true, (init pL1123), (init pL1123))) 1123 562 false = true :=
  fin_run (runOK_init (prmOK_of_and L1123_fin) true) (by decide) rfl L1123_fin ptTest_fst
theorem H1123_fin : (prmOK pH1123 1123 && ptTest pH1123 (runFrom pH1123 (fmask pH1123) (cmask pH1123) (hmask pH1123) 1 1122 (true, (init pH1123), (init pH1123))) 1123 562 true) = true := by
  decide +kernel
theorem H1123_ok : RunOK pH1123 1123 (runFrom pH1123 (fmask pH1123) (cmask pH1123) (hmask pH1123) 1 1122 (true, (init pH1123), (init pH1123))) ∧ ptTest pH1123 (runFrom pH1123 (fmask pH1123) (cmask pH1123) (hmask pH1123) 1 1122 (true, (init pH1123), (init pH1123))) 1123 562 true = true :=
  fin_run (runOK_init (prmOK_of_and H1123_fin) true) (by decide) rfl H1123_fin ptTest_fst
theorem I1123_fin : (prmOK pI1123 1123 && intTest pI1123 (runFrom pI1123 (fmask pI1123) (cmask pI1123) (hmask pI1123) 1 1122 (true, (init pI1123), (init pI1123))) 1123 18 false) = true := by
  decide +kernel
theorem I1123_ok : RunOK pI1123 1123 (runFrom pI1123 (fmask pI1123) (cmask pI1123) (hmask pI1123) 1 1122 (true, (init pI1123), (init pI1123))) ∧ intTest pI1123 (runFrom pI1123 (fmask pI1123) (cmask pI1123) (hmask pI1123) 1 1122 (true, (init pI1123), (init pI1123))) 1123 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1123_fin) true) (by decide) rfl I1123_fin intTest_fst
theorem link1123 : linkOK pL1123 pH1123 pI1123 = true := by decide +kernel
theorem cvx1123 : ConvexBetweenHumps 1123 :=
  cvx_of L1123_ok H1123_ok I1123_ok link1123 (by decide)

/-! ### `N = 1124` -/

def pL1124 : Prm := ⟨76, 35, 38, 1126, 11, 18446744073709551616, 157135932670493027, 157135932670493027⟩
def pH1124 : Prm := ⟨76, 35, 38, 1126, 11, 18446744073709551616, 157138131693748579, 157138131693748579⟩
def pI1124 : Prm := ⟨66, 32, 31, 1126, 11, 18446744073709551616, 157135932670493027, 157138131693748579⟩
theorem L1124_fin : (prmOK pL1124 1124 && ptTest pL1124 (runFrom pL1124 (fmask pL1124) (cmask pL1124) (hmask pL1124) 1 1123 (true, (init pL1124), (init pL1124))) 1124 562 false) = true := by
  decide +kernel
theorem L1124_ok : RunOK pL1124 1124 (runFrom pL1124 (fmask pL1124) (cmask pL1124) (hmask pL1124) 1 1123 (true, (init pL1124), (init pL1124))) ∧ ptTest pL1124 (runFrom pL1124 (fmask pL1124) (cmask pL1124) (hmask pL1124) 1 1123 (true, (init pL1124), (init pL1124))) 1124 562 false = true :=
  fin_run (runOK_init (prmOK_of_and L1124_fin) true) (by decide) rfl L1124_fin ptTest_fst
theorem H1124_fin : (prmOK pH1124 1124 && ptTest pH1124 (runFrom pH1124 (fmask pH1124) (cmask pH1124) (hmask pH1124) 1 1123 (true, (init pH1124), (init pH1124))) 1124 562 true) = true := by
  decide +kernel
theorem H1124_ok : RunOK pH1124 1124 (runFrom pH1124 (fmask pH1124) (cmask pH1124) (hmask pH1124) 1 1123 (true, (init pH1124), (init pH1124))) ∧ ptTest pH1124 (runFrom pH1124 (fmask pH1124) (cmask pH1124) (hmask pH1124) 1 1123 (true, (init pH1124), (init pH1124))) 1124 562 true = true :=
  fin_run (runOK_init (prmOK_of_and H1124_fin) true) (by decide) rfl H1124_fin ptTest_fst
theorem I1124_fin : (prmOK pI1124 1124 && intTest pI1124 (runFrom pI1124 (fmask pI1124) (cmask pI1124) (hmask pI1124) 1 1123 (true, (init pI1124), (init pI1124))) 1124 18 true) = true := by
  decide +kernel
theorem I1124_ok : RunOK pI1124 1124 (runFrom pI1124 (fmask pI1124) (cmask pI1124) (hmask pI1124) 1 1123 (true, (init pI1124), (init pI1124))) ∧ intTest pI1124 (runFrom pI1124 (fmask pI1124) (cmask pI1124) (hmask pI1124) 1 1123 (true, (init pI1124), (init pI1124))) 1124 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1124_fin) true) (by decide) rfl I1124_fin intTest_fst
theorem link1124 : linkOK pL1124 pH1124 pI1124 = true := by decide +kernel
theorem cvx1124 : ConvexBetweenHumps 1124 :=
  cvx_of L1124_ok H1124_ok I1124_ok link1124 (by decide)
theorem cenlink1124 : cenLinkOK pI1124 1124 = true := by decide +kernel
theorem cen1124 : CenterUniqueMin 1124 ∧ DipHyp 1124 ∧ OnePointHyps 1124 :=
  cen_of L1124_ok H1124_ok I1124_ok link1124 cenlink1124

/-! ### `N = 1125` -/

def pL1125 : Prm := ⟨76, 35, 38, 1127, 11, 18446744073709551616, 157023715168012762, 157023715168012762⟩
def pH1125 : Prm := ⟨76, 35, 38, 1127, 11, 18446744073709551616, 157025914191268314, 157025914191268314⟩
def pI1125 : Prm := ⟨66, 32, 31, 1127, 11, 18446744073709551616, 157023715168012762, 157025914191268314⟩
theorem L1125_fin : (prmOK pL1125 1125 && ptTest pL1125 (runFrom pL1125 (fmask pL1125) (cmask pL1125) (hmask pL1125) 1 1124 (true, (init pL1125), (init pL1125))) 1125 563 false) = true := by
  decide +kernel
theorem L1125_ok : RunOK pL1125 1125 (runFrom pL1125 (fmask pL1125) (cmask pL1125) (hmask pL1125) 1 1124 (true, (init pL1125), (init pL1125))) ∧ ptTest pL1125 (runFrom pL1125 (fmask pL1125) (cmask pL1125) (hmask pL1125) 1 1124 (true, (init pL1125), (init pL1125))) 1125 563 false = true :=
  fin_run (runOK_init (prmOK_of_and L1125_fin) true) (by decide) rfl L1125_fin ptTest_fst
theorem H1125_fin : (prmOK pH1125 1125 && ptTest pH1125 (runFrom pH1125 (fmask pH1125) (cmask pH1125) (hmask pH1125) 1 1124 (true, (init pH1125), (init pH1125))) 1125 563 true) = true := by
  decide +kernel
theorem H1125_ok : RunOK pH1125 1125 (runFrom pH1125 (fmask pH1125) (cmask pH1125) (hmask pH1125) 1 1124 (true, (init pH1125), (init pH1125))) ∧ ptTest pH1125 (runFrom pH1125 (fmask pH1125) (cmask pH1125) (hmask pH1125) 1 1124 (true, (init pH1125), (init pH1125))) 1125 563 true = true :=
  fin_run (runOK_init (prmOK_of_and H1125_fin) true) (by decide) rfl H1125_fin ptTest_fst
theorem I1125_fin : (prmOK pI1125 1125 && intTest pI1125 (runFrom pI1125 (fmask pI1125) (cmask pI1125) (hmask pI1125) 1 1124 (true, (init pI1125), (init pI1125))) 1125 18 false) = true := by
  decide +kernel
theorem I1125_ok : RunOK pI1125 1125 (runFrom pI1125 (fmask pI1125) (cmask pI1125) (hmask pI1125) 1 1124 (true, (init pI1125), (init pI1125))) ∧ intTest pI1125 (runFrom pI1125 (fmask pI1125) (cmask pI1125) (hmask pI1125) 1 1124 (true, (init pI1125), (init pI1125))) 1125 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1125_fin) true) (by decide) rfl I1125_fin intTest_fst
theorem link1125 : linkOK pL1125 pH1125 pI1125 = true := by decide +kernel
theorem cvx1125 : ConvexBetweenHumps 1125 :=
  cvx_of L1125_ok H1125_ok I1125_ok link1125 (by decide)

/-! ### `N = 1126` -/

def pL1126 : Prm := ⟨76, 35, 38, 1128, 11, 18446744073709551616, 156911753171107962, 156911753171107962⟩
def pH1126 : Prm := ⟨76, 35, 38, 1128, 11, 18446744073709551616, 156913952194363514, 156913952194363514⟩
def pI1126 : Prm := ⟨66, 32, 31, 1128, 11, 18446744073709551616, 156911753171107962, 156913952194363514⟩
theorem L1126_fin : (prmOK pL1126 1126 && ptTest pL1126 (runFrom pL1126 (fmask pL1126) (cmask pL1126) (hmask pL1126) 1 1125 (true, (init pL1126), (init pL1126))) 1126 563 false) = true := by
  decide +kernel
theorem L1126_ok : RunOK pL1126 1126 (runFrom pL1126 (fmask pL1126) (cmask pL1126) (hmask pL1126) 1 1125 (true, (init pL1126), (init pL1126))) ∧ ptTest pL1126 (runFrom pL1126 (fmask pL1126) (cmask pL1126) (hmask pL1126) 1 1125 (true, (init pL1126), (init pL1126))) 1126 563 false = true :=
  fin_run (runOK_init (prmOK_of_and L1126_fin) true) (by decide) rfl L1126_fin ptTest_fst
theorem H1126_fin : (prmOK pH1126 1126 && ptTest pH1126 (runFrom pH1126 (fmask pH1126) (cmask pH1126) (hmask pH1126) 1 1125 (true, (init pH1126), (init pH1126))) 1126 563 true) = true := by
  decide +kernel
theorem H1126_ok : RunOK pH1126 1126 (runFrom pH1126 (fmask pH1126) (cmask pH1126) (hmask pH1126) 1 1125 (true, (init pH1126), (init pH1126))) ∧ ptTest pH1126 (runFrom pH1126 (fmask pH1126) (cmask pH1126) (hmask pH1126) 1 1125 (true, (init pH1126), (init pH1126))) 1126 563 true = true :=
  fin_run (runOK_init (prmOK_of_and H1126_fin) true) (by decide) rfl H1126_fin ptTest_fst
theorem I1126_fin : (prmOK pI1126 1126 && intTest pI1126 (runFrom pI1126 (fmask pI1126) (cmask pI1126) (hmask pI1126) 1 1125 (true, (init pI1126), (init pI1126))) 1126 18 true) = true := by
  decide +kernel
theorem I1126_ok : RunOK pI1126 1126 (runFrom pI1126 (fmask pI1126) (cmask pI1126) (hmask pI1126) 1 1125 (true, (init pI1126), (init pI1126))) ∧ intTest pI1126 (runFrom pI1126 (fmask pI1126) (cmask pI1126) (hmask pI1126) 1 1125 (true, (init pI1126), (init pI1126))) 1126 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1126_fin) true) (by decide) rfl I1126_fin intTest_fst
theorem link1126 : linkOK pL1126 pH1126 pI1126 = true := by decide +kernel
theorem cvx1126 : ConvexBetweenHumps 1126 :=
  cvx_of L1126_ok H1126_ok I1126_ok link1126 (by decide)
theorem cenlink1126 : cenLinkOK pI1126 1126 = true := by decide +kernel
theorem cen1126 : CenterUniqueMin 1126 ∧ DipHyp 1126 ∧ OnePointHyps 1126 :=
  cen_of L1126_ok H1126_ok I1126_ok link1126 cenlink1126

/-! ### `N = 1127` -/

def pL1127 : Prm := ⟨76, 35, 38, 1129, 11, 18446744073709551616, 156799885127750373, 156799885127750373⟩
def pH1127 : Prm := ⟨76, 35, 38, 1129, 11, 18446744073709551616, 156802084151005925, 156802084151005925⟩
def pI1127 : Prm := ⟨66, 32, 31, 1129, 11, 18446744073709551616, 156799885127750373, 156802084151005925⟩
theorem L1127_fin : (prmOK pL1127 1127 && ptTest pL1127 (runFrom pL1127 (fmask pL1127) (cmask pL1127) (hmask pL1127) 1 1126 (true, (init pL1127), (init pL1127))) 1127 564 false) = true := by
  decide +kernel
theorem L1127_ok : RunOK pL1127 1127 (runFrom pL1127 (fmask pL1127) (cmask pL1127) (hmask pL1127) 1 1126 (true, (init pL1127), (init pL1127))) ∧ ptTest pL1127 (runFrom pL1127 (fmask pL1127) (cmask pL1127) (hmask pL1127) 1 1126 (true, (init pL1127), (init pL1127))) 1127 564 false = true :=
  fin_run (runOK_init (prmOK_of_and L1127_fin) true) (by decide) rfl L1127_fin ptTest_fst
theorem H1127_fin : (prmOK pH1127 1127 && ptTest pH1127 (runFrom pH1127 (fmask pH1127) (cmask pH1127) (hmask pH1127) 1 1126 (true, (init pH1127), (init pH1127))) 1127 564 true) = true := by
  decide +kernel
theorem H1127_ok : RunOK pH1127 1127 (runFrom pH1127 (fmask pH1127) (cmask pH1127) (hmask pH1127) 1 1126 (true, (init pH1127), (init pH1127))) ∧ ptTest pH1127 (runFrom pH1127 (fmask pH1127) (cmask pH1127) (hmask pH1127) 1 1126 (true, (init pH1127), (init pH1127))) 1127 564 true = true :=
  fin_run (runOK_init (prmOK_of_and H1127_fin) true) (by decide) rfl H1127_fin ptTest_fst
theorem I1127_fin : (prmOK pI1127 1127 && intTest pI1127 (runFrom pI1127 (fmask pI1127) (cmask pI1127) (hmask pI1127) 1 1126 (true, (init pI1127), (init pI1127))) 1127 19 false) = true := by
  decide +kernel
theorem I1127_ok : RunOK pI1127 1127 (runFrom pI1127 (fmask pI1127) (cmask pI1127) (hmask pI1127) 1 1126 (true, (init pI1127), (init pI1127))) ∧ intTest pI1127 (runFrom pI1127 (fmask pI1127) (cmask pI1127) (hmask pI1127) 1 1126 (true, (init pI1127), (init pI1127))) 1127 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1127_fin) true) (by decide) rfl I1127_fin intTest_fst
theorem link1127 : linkOK pL1127 pH1127 pI1127 = true := by decide +kernel
theorem cvx1127 : ConvexBetweenHumps 1127 :=
  cvx_of L1127_ok H1127_ok I1127_ok link1127 (by decide)

/-! ### `N = 1128` -/

def pL1128 : Prm := ⟨76, 35, 38, 1130, 11, 18446744073709551616, 156688271310741888, 156688271310741888⟩
def pH1128 : Prm := ⟨76, 35, 38, 1130, 11, 18446744073709551616, 156690470333997440, 156690470333997440⟩
def pI1128 : Prm := ⟨66, 32, 31, 1130, 11, 18446744073709551616, 156688271310741888, 156690470333997440⟩
theorem L1128_fin : (prmOK pL1128 1128 && ptTest pL1128 (runFrom pL1128 (fmask pL1128) (cmask pL1128) (hmask pL1128) 1 1127 (true, (init pL1128), (init pL1128))) 1128 564 false) = true := by
  decide +kernel
theorem L1128_ok : RunOK pL1128 1128 (runFrom pL1128 (fmask pL1128) (cmask pL1128) (hmask pL1128) 1 1127 (true, (init pL1128), (init pL1128))) ∧ ptTest pL1128 (runFrom pL1128 (fmask pL1128) (cmask pL1128) (hmask pL1128) 1 1127 (true, (init pL1128), (init pL1128))) 1128 564 false = true :=
  fin_run (runOK_init (prmOK_of_and L1128_fin) true) (by decide) rfl L1128_fin ptTest_fst
theorem H1128_fin : (prmOK pH1128 1128 && ptTest pH1128 (runFrom pH1128 (fmask pH1128) (cmask pH1128) (hmask pH1128) 1 1127 (true, (init pH1128), (init pH1128))) 1128 564 true) = true := by
  decide +kernel
theorem H1128_ok : RunOK pH1128 1128 (runFrom pH1128 (fmask pH1128) (cmask pH1128) (hmask pH1128) 1 1127 (true, (init pH1128), (init pH1128))) ∧ ptTest pH1128 (runFrom pH1128 (fmask pH1128) (cmask pH1128) (hmask pH1128) 1 1127 (true, (init pH1128), (init pH1128))) 1128 564 true = true :=
  fin_run (runOK_init (prmOK_of_and H1128_fin) true) (by decide) rfl H1128_fin ptTest_fst
theorem I1128_fin : (prmOK pI1128 1128 && intTest pI1128 (runFrom pI1128 (fmask pI1128) (cmask pI1128) (hmask pI1128) 1 1127 (true, (init pI1128), (init pI1128))) 1128 19 true) = true := by
  decide +kernel
theorem I1128_ok : RunOK pI1128 1128 (runFrom pI1128 (fmask pI1128) (cmask pI1128) (hmask pI1128) 1 1127 (true, (init pI1128), (init pI1128))) ∧ intTest pI1128 (runFrom pI1128 (fmask pI1128) (cmask pI1128) (hmask pI1128) 1 1127 (true, (init pI1128), (init pI1128))) 1128 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1128_fin) true) (by decide) rfl I1128_fin intTest_fst
theorem link1128 : linkOK pL1128 pH1128 pI1128 = true := by decide +kernel
theorem cvx1128 : ConvexBetweenHumps 1128 :=
  cvx_of L1128_ok H1128_ok I1128_ok link1128 (by decide)
theorem cenlink1128 : cenLinkOK pI1128 1128 = true := by decide +kernel
theorem cen1128 : CenterUniqueMin 1128 ∧ DipHyp 1128 ∧ OnePointHyps 1128 :=
  cen_of L1128_ok H1128_ok I1128_ok link1128 cenlink1128

/-! ### `N = 1129` -/

def pL1129 : Prm := ⟨76, 35, 38, 1131, 11, 18446744073709551616, 156576751041765839, 156576751041765839⟩
def pH1129 : Prm := ⟨76, 35, 38, 1131, 11, 18446744073709551616, 156578950065021391, 156578950065021391⟩
def pI1129 : Prm := ⟨66, 32, 31, 1131, 11, 18446744073709551616, 156576751041765839, 156578950065021391⟩
theorem L1129_fin : (prmOK pL1129 1129 && ptTest pL1129 (runFrom pL1129 (fmask pL1129) (cmask pL1129) (hmask pL1129) 1 1128 (true, (init pL1129), (init pL1129))) 1129 565 false) = true := by
  decide +kernel
theorem L1129_ok : RunOK pL1129 1129 (runFrom pL1129 (fmask pL1129) (cmask pL1129) (hmask pL1129) 1 1128 (true, (init pL1129), (init pL1129))) ∧ ptTest pL1129 (runFrom pL1129 (fmask pL1129) (cmask pL1129) (hmask pL1129) 1 1128 (true, (init pL1129), (init pL1129))) 1129 565 false = true :=
  fin_run (runOK_init (prmOK_of_and L1129_fin) true) (by decide) rfl L1129_fin ptTest_fst
theorem H1129_fin : (prmOK pH1129 1129 && ptTest pH1129 (runFrom pH1129 (fmask pH1129) (cmask pH1129) (hmask pH1129) 1 1128 (true, (init pH1129), (init pH1129))) 1129 565 true) = true := by
  decide +kernel
theorem H1129_ok : RunOK pH1129 1129 (runFrom pH1129 (fmask pH1129) (cmask pH1129) (hmask pH1129) 1 1128 (true, (init pH1129), (init pH1129))) ∧ ptTest pH1129 (runFrom pH1129 (fmask pH1129) (cmask pH1129) (hmask pH1129) 1 1128 (true, (init pH1129), (init pH1129))) 1129 565 true = true :=
  fin_run (runOK_init (prmOK_of_and H1129_fin) true) (by decide) rfl H1129_fin ptTest_fst
theorem I1129_fin : (prmOK pI1129 1129 && intTest pI1129 (runFrom pI1129 (fmask pI1129) (cmask pI1129) (hmask pI1129) 1 1128 (true, (init pI1129), (init pI1129))) 1129 19 false) = true := by
  decide +kernel
theorem I1129_ok : RunOK pI1129 1129 (runFrom pI1129 (fmask pI1129) (cmask pI1129) (hmask pI1129) 1 1128 (true, (init pI1129), (init pI1129))) ∧ intTest pI1129 (runFrom pI1129 (fmask pI1129) (cmask pI1129) (hmask pI1129) 1 1128 (true, (init pI1129), (init pI1129))) 1129 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1129_fin) true) (by decide) rfl I1129_fin intTest_fst
theorem link1129 : linkOK pL1129 pH1129 pI1129 = true := by decide +kernel
theorem cvx1129 : ConvexBetweenHumps 1129 :=
  cvx_of L1129_ok H1129_ok I1129_ok link1129 (by decide)

/-! ### `N = 1130` -/

def pL1130 : Prm := ⟨76, 35, 38, 1132, 11, 18446744073709551616, 156465483728527160, 156465483728527160⟩
def pH1130 : Prm := ⟨76, 35, 38, 1132, 11, 18446744073709551616, 156467682751782712, 156467682751782712⟩
def pI1130 : Prm := ⟨66, 32, 31, 1132, 11, 18446744073709551616, 156465483728527160, 156467682751782712⟩
theorem L1130_fin : (prmOK pL1130 1130 && ptTest pL1130 (runFrom pL1130 (fmask pL1130) (cmask pL1130) (hmask pL1130) 1 1129 (true, (init pL1130), (init pL1130))) 1130 565 false) = true := by
  decide +kernel
theorem L1130_ok : RunOK pL1130 1130 (runFrom pL1130 (fmask pL1130) (cmask pL1130) (hmask pL1130) 1 1129 (true, (init pL1130), (init pL1130))) ∧ ptTest pL1130 (runFrom pL1130 (fmask pL1130) (cmask pL1130) (hmask pL1130) 1 1129 (true, (init pL1130), (init pL1130))) 1130 565 false = true :=
  fin_run (runOK_init (prmOK_of_and L1130_fin) true) (by decide) rfl L1130_fin ptTest_fst
theorem H1130_fin : (prmOK pH1130 1130 && ptTest pH1130 (runFrom pH1130 (fmask pH1130) (cmask pH1130) (hmask pH1130) 1 1129 (true, (init pH1130), (init pH1130))) 1130 565 true) = true := by
  decide +kernel
theorem H1130_ok : RunOK pH1130 1130 (runFrom pH1130 (fmask pH1130) (cmask pH1130) (hmask pH1130) 1 1129 (true, (init pH1130), (init pH1130))) ∧ ptTest pH1130 (runFrom pH1130 (fmask pH1130) (cmask pH1130) (hmask pH1130) 1 1129 (true, (init pH1130), (init pH1130))) 1130 565 true = true :=
  fin_run (runOK_init (prmOK_of_and H1130_fin) true) (by decide) rfl H1130_fin ptTest_fst
theorem I1130_fin : (prmOK pI1130 1130 && intTest pI1130 (runFrom pI1130 (fmask pI1130) (cmask pI1130) (hmask pI1130) 1 1129 (true, (init pI1130), (init pI1130))) 1130 19 true) = true := by
  decide +kernel
theorem I1130_ok : RunOK pI1130 1130 (runFrom pI1130 (fmask pI1130) (cmask pI1130) (hmask pI1130) 1 1129 (true, (init pI1130), (init pI1130))) ∧ intTest pI1130 (runFrom pI1130 (fmask pI1130) (cmask pI1130) (hmask pI1130) 1 1129 (true, (init pI1130), (init pI1130))) 1130 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1130_fin) true) (by decide) rfl I1130_fin intTest_fst
theorem link1130 : linkOK pL1130 pH1130 pI1130 = true := by decide +kernel
theorem cvx1130 : ConvexBetweenHumps 1130 :=
  cvx_of L1130_ok H1130_ok I1130_ok link1130 (by decide)
theorem cenlink1130 : cenLinkOK pI1130 1130 = true := by decide +kernel
theorem cen1130 : CenterUniqueMin 1130 ∧ DipHyp 1130 ∧ OnePointHyps 1130 :=
  cen_of L1130_ok H1130_ok I1130_ok link1130 cenlink1130

/-! ### `N = 1131` -/

def pL1131 : Prm := ⟨76, 35, 38, 1133, 11, 18446744073709551616, 156354309560167328, 156354309560167328⟩
def pH1131 : Prm := ⟨76, 35, 38, 1133, 11, 18446744073709551616, 156356508583422880, 156356508583422880⟩
def pI1131 : Prm := ⟨66, 32, 31, 1133, 11, 18446744073709551616, 156354309560167328, 156356508583422880⟩
theorem L1131_fin : (prmOK pL1131 1131 && ptTest pL1131 (runFrom pL1131 (fmask pL1131) (cmask pL1131) (hmask pL1131) 1 1130 (true, (init pL1131), (init pL1131))) 1131 566 false) = true := by
  decide +kernel
theorem L1131_ok : RunOK pL1131 1131 (runFrom pL1131 (fmask pL1131) (cmask pL1131) (hmask pL1131) 1 1130 (true, (init pL1131), (init pL1131))) ∧ ptTest pL1131 (runFrom pL1131 (fmask pL1131) (cmask pL1131) (hmask pL1131) 1 1130 (true, (init pL1131), (init pL1131))) 1131 566 false = true :=
  fin_run (runOK_init (prmOK_of_and L1131_fin) true) (by decide) rfl L1131_fin ptTest_fst
theorem H1131_fin : (prmOK pH1131 1131 && ptTest pH1131 (runFrom pH1131 (fmask pH1131) (cmask pH1131) (hmask pH1131) 1 1130 (true, (init pH1131), (init pH1131))) 1131 566 true) = true := by
  decide +kernel
theorem H1131_ok : RunOK pH1131 1131 (runFrom pH1131 (fmask pH1131) (cmask pH1131) (hmask pH1131) 1 1130 (true, (init pH1131), (init pH1131))) ∧ ptTest pH1131 (runFrom pH1131 (fmask pH1131) (cmask pH1131) (hmask pH1131) 1 1130 (true, (init pH1131), (init pH1131))) 1131 566 true = true :=
  fin_run (runOK_init (prmOK_of_and H1131_fin) true) (by decide) rfl H1131_fin ptTest_fst
theorem I1131_fin : (prmOK pI1131 1131 && intTest pI1131 (runFrom pI1131 (fmask pI1131) (cmask pI1131) (hmask pI1131) 1 1130 (true, (init pI1131), (init pI1131))) 1131 19 false) = true := by
  decide +kernel
theorem I1131_ok : RunOK pI1131 1131 (runFrom pI1131 (fmask pI1131) (cmask pI1131) (hmask pI1131) 1 1130 (true, (init pI1131), (init pI1131))) ∧ intTest pI1131 (runFrom pI1131 (fmask pI1131) (cmask pI1131) (hmask pI1131) 1 1130 (true, (init pI1131), (init pI1131))) 1131 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1131_fin) true) (by decide) rfl I1131_fin intTest_fst
theorem link1131 : linkOK pL1131 pH1131 pI1131 = true := by decide +kernel
theorem cvx1131 : ConvexBetweenHumps 1131 :=
  cvx_of L1131_ok H1131_ok I1131_ok link1131 (by decide)

/-! ### `N = 1132` -/

def pL1132 : Prm := ⟨76, 35, 38, 1134, 11, 18446744073709551616, 156243387085529316, 156243387085529316⟩
def pH1132 : Prm := ⟨76, 35, 38, 1134, 11, 18446744073709551616, 156245586108784868, 156245586108784868⟩
def pI1132 : Prm := ⟨66, 32, 31, 1134, 11, 18446744073709551616, 156243387085529316, 156245586108784868⟩
theorem L1132_fin : (prmOK pL1132 1132 && ptTest pL1132 (runFrom pL1132 (fmask pL1132) (cmask pL1132) (hmask pL1132) 1 1131 (true, (init pL1132), (init pL1132))) 1132 566 false) = true := by
  decide +kernel
theorem L1132_ok : RunOK pL1132 1132 (runFrom pL1132 (fmask pL1132) (cmask pL1132) (hmask pL1132) 1 1131 (true, (init pL1132), (init pL1132))) ∧ ptTest pL1132 (runFrom pL1132 (fmask pL1132) (cmask pL1132) (hmask pL1132) 1 1131 (true, (init pL1132), (init pL1132))) 1132 566 false = true :=
  fin_run (runOK_init (prmOK_of_and L1132_fin) true) (by decide) rfl L1132_fin ptTest_fst
theorem H1132_fin : (prmOK pH1132 1132 && ptTest pH1132 (runFrom pH1132 (fmask pH1132) (cmask pH1132) (hmask pH1132) 1 1131 (true, (init pH1132), (init pH1132))) 1132 566 true) = true := by
  decide +kernel
theorem H1132_ok : RunOK pH1132 1132 (runFrom pH1132 (fmask pH1132) (cmask pH1132) (hmask pH1132) 1 1131 (true, (init pH1132), (init pH1132))) ∧ ptTest pH1132 (runFrom pH1132 (fmask pH1132) (cmask pH1132) (hmask pH1132) 1 1131 (true, (init pH1132), (init pH1132))) 1132 566 true = true :=
  fin_run (runOK_init (prmOK_of_and H1132_fin) true) (by decide) rfl H1132_fin ptTest_fst
theorem I1132_fin : (prmOK pI1132 1132 && intTest pI1132 (runFrom pI1132 (fmask pI1132) (cmask pI1132) (hmask pI1132) 1 1131 (true, (init pI1132), (init pI1132))) 1132 19 true) = true := by
  decide +kernel
theorem I1132_ok : RunOK pI1132 1132 (runFrom pI1132 (fmask pI1132) (cmask pI1132) (hmask pI1132) 1 1131 (true, (init pI1132), (init pI1132))) ∧ intTest pI1132 (runFrom pI1132 (fmask pI1132) (cmask pI1132) (hmask pI1132) 1 1131 (true, (init pI1132), (init pI1132))) 1132 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1132_fin) true) (by decide) rfl I1132_fin intTest_fst
theorem link1132 : linkOK pL1132 pH1132 pI1132 = true := by decide +kernel
theorem cvx1132 : ConvexBetweenHumps 1132 :=
  cvx_of L1132_ok H1132_ok I1132_ok link1132 (by decide)
theorem cenlink1132 : cenLinkOK pI1132 1132 = true := by decide +kernel
theorem cen1132 : CenterUniqueMin 1132 ∧ DipHyp 1132 ∧ OnePointHyps 1132 :=
  cen_of L1132_ok H1132_ok I1132_ok link1132 cenlink1132

/-! ### `N = 1133` -/

def pL1133 : Prm := ⟨76, 35, 38, 1135, 11, 18446744073709551616, 156132557354959296, 156132557354959296⟩
def pH1133 : Prm := ⟨76, 35, 38, 1135, 11, 18446744073709551616, 156134756378214848, 156134756378214848⟩
def pI1133 : Prm := ⟨66, 32, 31, 1135, 11, 18446744073709551616, 156132557354959296, 156134756378214848⟩
theorem L1133_fin : (prmOK pL1133 1133 && ptTest pL1133 (runFrom pL1133 (fmask pL1133) (cmask pL1133) (hmask pL1133) 1 1132 (true, (init pL1133), (init pL1133))) 1133 567 false) = true := by
  decide +kernel
theorem L1133_ok : RunOK pL1133 1133 (runFrom pL1133 (fmask pL1133) (cmask pL1133) (hmask pL1133) 1 1132 (true, (init pL1133), (init pL1133))) ∧ ptTest pL1133 (runFrom pL1133 (fmask pL1133) (cmask pL1133) (hmask pL1133) 1 1132 (true, (init pL1133), (init pL1133))) 1133 567 false = true :=
  fin_run (runOK_init (prmOK_of_and L1133_fin) true) (by decide) rfl L1133_fin ptTest_fst
theorem H1133_fin : (prmOK pH1133 1133 && ptTest pH1133 (runFrom pH1133 (fmask pH1133) (cmask pH1133) (hmask pH1133) 1 1132 (true, (init pH1133), (init pH1133))) 1133 567 true) = true := by
  decide +kernel
theorem H1133_ok : RunOK pH1133 1133 (runFrom pH1133 (fmask pH1133) (cmask pH1133) (hmask pH1133) 1 1132 (true, (init pH1133), (init pH1133))) ∧ ptTest pH1133 (runFrom pH1133 (fmask pH1133) (cmask pH1133) (hmask pH1133) 1 1132 (true, (init pH1133), (init pH1133))) 1133 567 true = true :=
  fin_run (runOK_init (prmOK_of_and H1133_fin) true) (by decide) rfl H1133_fin ptTest_fst
theorem I1133_fin : (prmOK pI1133 1133 && intTest pI1133 (runFrom pI1133 (fmask pI1133) (cmask pI1133) (hmask pI1133) 1 1132 (true, (init pI1133), (init pI1133))) 1133 19 false) = true := by
  decide +kernel
theorem I1133_ok : RunOK pI1133 1133 (runFrom pI1133 (fmask pI1133) (cmask pI1133) (hmask pI1133) 1 1132 (true, (init pI1133), (init pI1133))) ∧ intTest pI1133 (runFrom pI1133 (fmask pI1133) (cmask pI1133) (hmask pI1133) 1 1132 (true, (init pI1133), (init pI1133))) 1133 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1133_fin) true) (by decide) rfl I1133_fin intTest_fst
theorem link1133 : linkOK pL1133 pH1133 pI1133 = true := by decide +kernel
theorem cvx1133 : ConvexBetweenHumps 1133 :=
  cvx_of L1133_ok H1133_ok I1133_ok link1133 (by decide)

/-! ### `N = 1134` -/

def pL1134 : Prm := ⟨76, 35, 38, 1136, 11, 18446744073709551616, 156021978064581049, 156021978064581049⟩
def pH1134 : Prm := ⟨76, 35, 38, 1136, 11, 18446744073709551616, 156024177087836601, 156024177087836601⟩
def pI1134 : Prm := ⟨66, 32, 31, 1136, 11, 18446744073709551616, 156021978064581049, 156024177087836601⟩
theorem L1134_fin : (prmOK pL1134 1134 && ptTest pL1134 (runFrom pL1134 (fmask pL1134) (cmask pL1134) (hmask pL1134) 1 1133 (true, (init pL1134), (init pL1134))) 1134 567 false) = true := by
  decide +kernel
theorem L1134_ok : RunOK pL1134 1134 (runFrom pL1134 (fmask pL1134) (cmask pL1134) (hmask pL1134) 1 1133 (true, (init pL1134), (init pL1134))) ∧ ptTest pL1134 (runFrom pL1134 (fmask pL1134) (cmask pL1134) (hmask pL1134) 1 1133 (true, (init pL1134), (init pL1134))) 1134 567 false = true :=
  fin_run (runOK_init (prmOK_of_and L1134_fin) true) (by decide) rfl L1134_fin ptTest_fst
theorem H1134_fin : (prmOK pH1134 1134 && ptTest pH1134 (runFrom pH1134 (fmask pH1134) (cmask pH1134) (hmask pH1134) 1 1133 (true, (init pH1134), (init pH1134))) 1134 567 true) = true := by
  decide +kernel
theorem H1134_ok : RunOK pH1134 1134 (runFrom pH1134 (fmask pH1134) (cmask pH1134) (hmask pH1134) 1 1133 (true, (init pH1134), (init pH1134))) ∧ ptTest pH1134 (runFrom pH1134 (fmask pH1134) (cmask pH1134) (hmask pH1134) 1 1133 (true, (init pH1134), (init pH1134))) 1134 567 true = true :=
  fin_run (runOK_init (prmOK_of_and H1134_fin) true) (by decide) rfl H1134_fin ptTest_fst
theorem I1134_fin : (prmOK pI1134 1134 && intTest pI1134 (runFrom pI1134 (fmask pI1134) (cmask pI1134) (hmask pI1134) 1 1133 (true, (init pI1134), (init pI1134))) 1134 19 true) = true := by
  decide +kernel
theorem I1134_ok : RunOK pI1134 1134 (runFrom pI1134 (fmask pI1134) (cmask pI1134) (hmask pI1134) 1 1133 (true, (init pI1134), (init pI1134))) ∧ intTest pI1134 (runFrom pI1134 (fmask pI1134) (cmask pI1134) (hmask pI1134) 1 1133 (true, (init pI1134), (init pI1134))) 1134 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1134_fin) true) (by decide) rfl I1134_fin intTest_fst
theorem link1134 : linkOK pL1134 pH1134 pI1134 = true := by decide +kernel
theorem cvx1134 : ConvexBetweenHumps 1134 :=
  cvx_of L1134_ok H1134_ok I1134_ok link1134 (by decide)
theorem cenlink1134 : cenLinkOK pI1134 1134 = true := by decide +kernel
theorem cen1134 : CenterUniqueMin 1134 ∧ DipHyp 1134 ∧ OnePointHyps 1134 :=
  cen_of L1134_ok H1134_ok I1134_ok link1134 cenlink1134

/-! ### `N = 1135` -/

def pL1135 : Prm := ⟨76, 35, 38, 1137, 11, 18446744073709551616, 155911491119784227, 155911491119784227⟩
def pH1135 : Prm := ⟨76, 35, 38, 1137, 11, 18446744073709551616, 155913690143039779, 155913690143039779⟩
def pI1135 : Prm := ⟨66, 32, 31, 1137, 11, 18446744073709551616, 155911491119784227, 155913690143039779⟩
theorem L1135_fin : (prmOK pL1135 1135 && ptTest pL1135 (runFrom pL1135 (fmask pL1135) (cmask pL1135) (hmask pL1135) 1 1134 (true, (init pL1135), (init pL1135))) 1135 568 false) = true := by
  decide +kernel
theorem L1135_ok : RunOK pL1135 1135 (runFrom pL1135 (fmask pL1135) (cmask pL1135) (hmask pL1135) 1 1134 (true, (init pL1135), (init pL1135))) ∧ ptTest pL1135 (runFrom pL1135 (fmask pL1135) (cmask pL1135) (hmask pL1135) 1 1134 (true, (init pL1135), (init pL1135))) 1135 568 false = true :=
  fin_run (runOK_init (prmOK_of_and L1135_fin) true) (by decide) rfl L1135_fin ptTest_fst
theorem H1135_fin : (prmOK pH1135 1135 && ptTest pH1135 (runFrom pH1135 (fmask pH1135) (cmask pH1135) (hmask pH1135) 1 1134 (true, (init pH1135), (init pH1135))) 1135 568 true) = true := by
  decide +kernel
theorem H1135_ok : RunOK pH1135 1135 (runFrom pH1135 (fmask pH1135) (cmask pH1135) (hmask pH1135) 1 1134 (true, (init pH1135), (init pH1135))) ∧ ptTest pH1135 (runFrom pH1135 (fmask pH1135) (cmask pH1135) (hmask pH1135) 1 1134 (true, (init pH1135), (init pH1135))) 1135 568 true = true :=
  fin_run (runOK_init (prmOK_of_and H1135_fin) true) (by decide) rfl H1135_fin ptTest_fst
theorem I1135_fin : (prmOK pI1135 1135 && intTest pI1135 (runFrom pI1135 (fmask pI1135) (cmask pI1135) (hmask pI1135) 1 1134 (true, (init pI1135), (init pI1135))) 1135 19 false) = true := by
  decide +kernel
theorem I1135_ok : RunOK pI1135 1135 (runFrom pI1135 (fmask pI1135) (cmask pI1135) (hmask pI1135) 1 1134 (true, (init pI1135), (init pI1135))) ∧ intTest pI1135 (runFrom pI1135 (fmask pI1135) (cmask pI1135) (hmask pI1135) 1 1134 (true, (init pI1135), (init pI1135))) 1135 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1135_fin) true) (by decide) rfl I1135_fin intTest_fst
theorem link1135 : linkOK pL1135 pH1135 pI1135 = true := by decide +kernel
theorem cvx1135 : ConvexBetweenHumps 1135 :=
  cvx_of L1135_ok H1135_ok I1135_ok link1135 (by decide)

/-! ### `N = 1136` -/

def pL1136 : Prm := ⟨76, 35, 38, 1138, 11, 18446744073709551616, 155801253370060850, 155801253370060850⟩
def pH1136 : Prm := ⟨76, 35, 38, 1138, 11, 18446744073709551616, 155803452393316402, 155803452393316402⟩
def pI1136 : Prm := ⟨66, 32, 31, 1138, 11, 18446744073709551616, 155801253370060850, 155803452393316402⟩
theorem L1136_fin : (prmOK pL1136 1136 && ptTest pL1136 (runFrom pL1136 (fmask pL1136) (cmask pL1136) (hmask pL1136) 1 1135 (true, (init pL1136), (init pL1136))) 1136 568 false) = true := by
  decide +kernel
theorem L1136_ok : RunOK pL1136 1136 (runFrom pL1136 (fmask pL1136) (cmask pL1136) (hmask pL1136) 1 1135 (true, (init pL1136), (init pL1136))) ∧ ptTest pL1136 (runFrom pL1136 (fmask pL1136) (cmask pL1136) (hmask pL1136) 1 1135 (true, (init pL1136), (init pL1136))) 1136 568 false = true :=
  fin_run (runOK_init (prmOK_of_and L1136_fin) true) (by decide) rfl L1136_fin ptTest_fst
theorem H1136_fin : (prmOK pH1136 1136 && ptTest pH1136 (runFrom pH1136 (fmask pH1136) (cmask pH1136) (hmask pH1136) 1 1135 (true, (init pH1136), (init pH1136))) 1136 568 true) = true := by
  decide +kernel
theorem H1136_ok : RunOK pH1136 1136 (runFrom pH1136 (fmask pH1136) (cmask pH1136) (hmask pH1136) 1 1135 (true, (init pH1136), (init pH1136))) ∧ ptTest pH1136 (runFrom pH1136 (fmask pH1136) (cmask pH1136) (hmask pH1136) 1 1135 (true, (init pH1136), (init pH1136))) 1136 568 true = true :=
  fin_run (runOK_init (prmOK_of_and H1136_fin) true) (by decide) rfl H1136_fin ptTest_fst
theorem I1136_fin : (prmOK pI1136 1136 && intTest pI1136 (runFrom pI1136 (fmask pI1136) (cmask pI1136) (hmask pI1136) 1 1135 (true, (init pI1136), (init pI1136))) 1136 19 true) = true := by
  decide +kernel
theorem I1136_ok : RunOK pI1136 1136 (runFrom pI1136 (fmask pI1136) (cmask pI1136) (hmask pI1136) 1 1135 (true, (init pI1136), (init pI1136))) ∧ intTest pI1136 (runFrom pI1136 (fmask pI1136) (cmask pI1136) (hmask pI1136) 1 1135 (true, (init pI1136), (init pI1136))) 1136 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1136_fin) true) (by decide) rfl I1136_fin intTest_fst
theorem link1136 : linkOK pL1136 pH1136 pI1136 = true := by decide +kernel
theorem cvx1136 : ConvexBetweenHumps 1136 :=
  cvx_of L1136_ok H1136_ok I1136_ok link1136 (by decide)
theorem cenlink1136 : cenLinkOK pI1136 1136 = true := by decide +kernel
theorem cen1136 : CenterUniqueMin 1136 ∧ DipHyp 1136 ∧ OnePointHyps 1136 :=
  cen_of L1136_ok H1136_ok I1136_ok link1136 cenlink1136

/-! ### `N = 1137` -/

def pL1137 : Prm := ⟨76, 35, 38, 1139, 11, 18446744073709551616, 155691107569793513, 155691107569793513⟩
def pH1137 : Prm := ⟨76, 35, 38, 1139, 11, 18446744073709551616, 155693306593049065, 155693306593049065⟩
def pI1137 : Prm := ⟨66, 32, 31, 1139, 11, 18446744073709551616, 155691107569793513, 155693306593049065⟩
theorem L1137_fin : (prmOK pL1137 1137 && ptTest pL1137 (runFrom pL1137 (fmask pL1137) (cmask pL1137) (hmask pL1137) 1 1136 (true, (init pL1137), (init pL1137))) 1137 569 false) = true := by
  decide +kernel
theorem L1137_ok : RunOK pL1137 1137 (runFrom pL1137 (fmask pL1137) (cmask pL1137) (hmask pL1137) 1 1136 (true, (init pL1137), (init pL1137))) ∧ ptTest pL1137 (runFrom pL1137 (fmask pL1137) (cmask pL1137) (hmask pL1137) 1 1136 (true, (init pL1137), (init pL1137))) 1137 569 false = true :=
  fin_run (runOK_init (prmOK_of_and L1137_fin) true) (by decide) rfl L1137_fin ptTest_fst
theorem H1137_fin : (prmOK pH1137 1137 && ptTest pH1137 (runFrom pH1137 (fmask pH1137) (cmask pH1137) (hmask pH1137) 1 1136 (true, (init pH1137), (init pH1137))) 1137 569 true) = true := by
  decide +kernel
theorem H1137_ok : RunOK pH1137 1137 (runFrom pH1137 (fmask pH1137) (cmask pH1137) (hmask pH1137) 1 1136 (true, (init pH1137), (init pH1137))) ∧ ptTest pH1137 (runFrom pH1137 (fmask pH1137) (cmask pH1137) (hmask pH1137) 1 1136 (true, (init pH1137), (init pH1137))) 1137 569 true = true :=
  fin_run (runOK_init (prmOK_of_and H1137_fin) true) (by decide) rfl H1137_fin ptTest_fst
theorem I1137_fin : (prmOK pI1137 1137 && intTest pI1137 (runFrom pI1137 (fmask pI1137) (cmask pI1137) (hmask pI1137) 1 1136 (true, (init pI1137), (init pI1137))) 1137 19 false) = true := by
  decide +kernel
theorem I1137_ok : RunOK pI1137 1137 (runFrom pI1137 (fmask pI1137) (cmask pI1137) (hmask pI1137) 1 1136 (true, (init pI1137), (init pI1137))) ∧ intTest pI1137 (runFrom pI1137 (fmask pI1137) (cmask pI1137) (hmask pI1137) 1 1136 (true, (init pI1137), (init pI1137))) 1137 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1137_fin) true) (by decide) rfl I1137_fin intTest_fst
theorem link1137 : linkOK pL1137 pH1137 pI1137 = true := by decide +kernel
theorem cvx1137 : ConvexBetweenHumps 1137 :=
  cvx_of L1137_ok H1137_ok I1137_ok link1137 (by decide)

/-! ### `N = 1138` -/

def pL1138 : Prm := ⟨76, 35, 38, 1140, 11, 18446744073709551616, 155581209727800771, 155581209727800771⟩
def pH1138 : Prm := ⟨76, 35, 38, 1140, 11, 18446744073709551616, 155583408751056323, 155583408751056323⟩
def pI1138 : Prm := ⟨66, 32, 31, 1140, 11, 18446744073709551616, 155581209727800771, 155583408751056323⟩
theorem L1138_fin : (prmOK pL1138 1138 && ptTest pL1138 (runFrom pL1138 (fmask pL1138) (cmask pL1138) (hmask pL1138) 1 1137 (true, (init pL1138), (init pL1138))) 1138 569 false) = true := by
  decide +kernel
theorem L1138_ok : RunOK pL1138 1138 (runFrom pL1138 (fmask pL1138) (cmask pL1138) (hmask pL1138) 1 1137 (true, (init pL1138), (init pL1138))) ∧ ptTest pL1138 (runFrom pL1138 (fmask pL1138) (cmask pL1138) (hmask pL1138) 1 1137 (true, (init pL1138), (init pL1138))) 1138 569 false = true :=
  fin_run (runOK_init (prmOK_of_and L1138_fin) true) (by decide) rfl L1138_fin ptTest_fst
theorem H1138_fin : (prmOK pH1138 1138 && ptTest pH1138 (runFrom pH1138 (fmask pH1138) (cmask pH1138) (hmask pH1138) 1 1137 (true, (init pH1138), (init pH1138))) 1138 569 true) = true := by
  decide +kernel
theorem H1138_ok : RunOK pH1138 1138 (runFrom pH1138 (fmask pH1138) (cmask pH1138) (hmask pH1138) 1 1137 (true, (init pH1138), (init pH1138))) ∧ ptTest pH1138 (runFrom pH1138 (fmask pH1138) (cmask pH1138) (hmask pH1138) 1 1137 (true, (init pH1138), (init pH1138))) 1138 569 true = true :=
  fin_run (runOK_init (prmOK_of_and H1138_fin) true) (by decide) rfl H1138_fin ptTest_fst
theorem I1138_fin : (prmOK pI1138 1138 && intTest pI1138 (runFrom pI1138 (fmask pI1138) (cmask pI1138) (hmask pI1138) 1 1137 (true, (init pI1138), (init pI1138))) 1138 19 true) = true := by
  decide +kernel
theorem I1138_ok : RunOK pI1138 1138 (runFrom pI1138 (fmask pI1138) (cmask pI1138) (hmask pI1138) 1 1137 (true, (init pI1138), (init pI1138))) ∧ intTest pI1138 (runFrom pI1138 (fmask pI1138) (cmask pI1138) (hmask pI1138) 1 1137 (true, (init pI1138), (init pI1138))) 1138 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1138_fin) true) (by decide) rfl I1138_fin intTest_fst
theorem link1138 : linkOK pL1138 pH1138 pI1138 = true := by decide +kernel
theorem cvx1138 : ConvexBetweenHumps 1138 :=
  cvx_of L1138_ok H1138_ok I1138_ok link1138 (by decide)
theorem cenlink1138 : cenLinkOK pI1138 1138 = true := by decide +kernel
theorem cen1138 : CenterUniqueMin 1138 ∧ DipHyp 1138 ∧ OnePointHyps 1138 :=
  cen_of L1138_ok H1138_ok I1138_ok link1138 cenlink1138

/-! ### `N = 1139` -/

def pL1139 : Prm := ⟨76, 35, 38, 1141, 11, 18446744073709551616, 155471403441444532, 155471403441444532⟩
def pH1139 : Prm := ⟨76, 35, 38, 1141, 11, 18446744073709551616, 155473602464700084, 155473602464700084⟩
def pI1139 : Prm := ⟨66, 32, 31, 1141, 11, 18446744073709551616, 155471403441444532, 155473602464700084⟩
theorem L1139_fin : (prmOK pL1139 1139 && ptTest pL1139 (runFrom pL1139 (fmask pL1139) (cmask pL1139) (hmask pL1139) 1 1138 (true, (init pL1139), (init pL1139))) 1139 570 false) = true := by
  decide +kernel
theorem L1139_ok : RunOK pL1139 1139 (runFrom pL1139 (fmask pL1139) (cmask pL1139) (hmask pL1139) 1 1138 (true, (init pL1139), (init pL1139))) ∧ ptTest pL1139 (runFrom pL1139 (fmask pL1139) (cmask pL1139) (hmask pL1139) 1 1138 (true, (init pL1139), (init pL1139))) 1139 570 false = true :=
  fin_run (runOK_init (prmOK_of_and L1139_fin) true) (by decide) rfl L1139_fin ptTest_fst
theorem H1139_fin : (prmOK pH1139 1139 && ptTest pH1139 (runFrom pH1139 (fmask pH1139) (cmask pH1139) (hmask pH1139) 1 1138 (true, (init pH1139), (init pH1139))) 1139 570 true) = true := by
  decide +kernel
theorem H1139_ok : RunOK pH1139 1139 (runFrom pH1139 (fmask pH1139) (cmask pH1139) (hmask pH1139) 1 1138 (true, (init pH1139), (init pH1139))) ∧ ptTest pH1139 (runFrom pH1139 (fmask pH1139) (cmask pH1139) (hmask pH1139) 1 1138 (true, (init pH1139), (init pH1139))) 1139 570 true = true :=
  fin_run (runOK_init (prmOK_of_and H1139_fin) true) (by decide) rfl H1139_fin ptTest_fst
theorem I1139_fin : (prmOK pI1139 1139 && intTest pI1139 (runFrom pI1139 (fmask pI1139) (cmask pI1139) (hmask pI1139) 1 1138 (true, (init pI1139), (init pI1139))) 1139 19 false) = true := by
  decide +kernel
theorem I1139_ok : RunOK pI1139 1139 (runFrom pI1139 (fmask pI1139) (cmask pI1139) (hmask pI1139) 1 1138 (true, (init pI1139), (init pI1139))) ∧ intTest pI1139 (runFrom pI1139 (fmask pI1139) (cmask pI1139) (hmask pI1139) 1 1138 (true, (init pI1139), (init pI1139))) 1139 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1139_fin) true) (by decide) rfl I1139_fin intTest_fst
theorem link1139 : linkOK pL1139 pH1139 pI1139 = true := by decide +kernel
theorem cvx1139 : ConvexBetweenHumps 1139 :=
  cvx_of L1139_ok H1139_ok I1139_ok link1139 (by decide)

/-! ### `N = 1140` -/

def pL1140 : Prm := ⟨76, 35, 38, 1142, 11, 18446744073709551616, 155361843884865071, 155361843884865071⟩
def pH1140 : Prm := ⟨76, 35, 38, 1142, 11, 18446744073709551616, 155364042908120623, 155364042908120623⟩
def pI1140 : Prm := ⟨66, 32, 31, 1142, 11, 18446744073709551616, 155361843884865071, 155364042908120623⟩
theorem L1140_fin : (prmOK pL1140 1140 && ptTest pL1140 (runFrom pL1140 (fmask pL1140) (cmask pL1140) (hmask pL1140) 1 1139 (true, (init pL1140), (init pL1140))) 1140 570 false) = true := by
  decide +kernel
theorem L1140_ok : RunOK pL1140 1140 (runFrom pL1140 (fmask pL1140) (cmask pL1140) (hmask pL1140) 1 1139 (true, (init pL1140), (init pL1140))) ∧ ptTest pL1140 (runFrom pL1140 (fmask pL1140) (cmask pL1140) (hmask pL1140) 1 1139 (true, (init pL1140), (init pL1140))) 1140 570 false = true :=
  fin_run (runOK_init (prmOK_of_and L1140_fin) true) (by decide) rfl L1140_fin ptTest_fst
theorem H1140_fin : (prmOK pH1140 1140 && ptTest pH1140 (runFrom pH1140 (fmask pH1140) (cmask pH1140) (hmask pH1140) 1 1139 (true, (init pH1140), (init pH1140))) 1140 570 true) = true := by
  decide +kernel
theorem H1140_ok : RunOK pH1140 1140 (runFrom pH1140 (fmask pH1140) (cmask pH1140) (hmask pH1140) 1 1139 (true, (init pH1140), (init pH1140))) ∧ ptTest pH1140 (runFrom pH1140 (fmask pH1140) (cmask pH1140) (hmask pH1140) 1 1139 (true, (init pH1140), (init pH1140))) 1140 570 true = true :=
  fin_run (runOK_init (prmOK_of_and H1140_fin) true) (by decide) rfl H1140_fin ptTest_fst
theorem I1140_fin : (prmOK pI1140 1140 && intTest pI1140 (runFrom pI1140 (fmask pI1140) (cmask pI1140) (hmask pI1140) 1 1139 (true, (init pI1140), (init pI1140))) 1140 19 true) = true := by
  decide +kernel
theorem I1140_ok : RunOK pI1140 1140 (runFrom pI1140 (fmask pI1140) (cmask pI1140) (hmask pI1140) 1 1139 (true, (init pI1140), (init pI1140))) ∧ intTest pI1140 (runFrom pI1140 (fmask pI1140) (cmask pI1140) (hmask pI1140) 1 1139 (true, (init pI1140), (init pI1140))) 1140 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1140_fin) true) (by decide) rfl I1140_fin intTest_fst
theorem link1140 : linkOK pL1140 pH1140 pI1140 = true := by decide +kernel
theorem cvx1140 : ConvexBetweenHumps 1140 :=
  cvx_of L1140_ok H1140_ok I1140_ok link1140 (by decide)
theorem cenlink1140 : cenLinkOK pI1140 1140 = true := by decide +kernel
theorem cen1140 : CenterUniqueMin 1140 ∧ DipHyp 1140 ∧ OnePointHyps 1140 :=
  cen_of L1140_ok H1140_ok I1140_ok link1140 cenlink1140

/-! ### `N = 1141` -/

def pL1141 : Prm := ⟨76, 35, 38, 1143, 11, 18446744073709551616, 155252375492334630, 155252375492334630⟩
def pH1141 : Prm := ⟨76, 35, 38, 1143, 11, 18446744073709551616, 155254574515590182, 155254574515590182⟩
def pI1141 : Prm := ⟨66, 32, 31, 1143, 11, 18446744073709551616, 155252375492334630, 155254574515590182⟩
theorem L1141_fin : (prmOK pL1141 1141 && ptTest pL1141 (runFrom pL1141 (fmask pL1141) (cmask pL1141) (hmask pL1141) 1 1140 (true, (init pL1141), (init pL1141))) 1141 571 false) = true := by
  decide +kernel
theorem L1141_ok : RunOK pL1141 1141 (runFrom pL1141 (fmask pL1141) (cmask pL1141) (hmask pL1141) 1 1140 (true, (init pL1141), (init pL1141))) ∧ ptTest pL1141 (runFrom pL1141 (fmask pL1141) (cmask pL1141) (hmask pL1141) 1 1140 (true, (init pL1141), (init pL1141))) 1141 571 false = true :=
  fin_run (runOK_init (prmOK_of_and L1141_fin) true) (by decide) rfl L1141_fin ptTest_fst
theorem H1141_fin : (prmOK pH1141 1141 && ptTest pH1141 (runFrom pH1141 (fmask pH1141) (cmask pH1141) (hmask pH1141) 1 1140 (true, (init pH1141), (init pH1141))) 1141 571 true) = true := by
  decide +kernel
theorem H1141_ok : RunOK pH1141 1141 (runFrom pH1141 (fmask pH1141) (cmask pH1141) (hmask pH1141) 1 1140 (true, (init pH1141), (init pH1141))) ∧ ptTest pH1141 (runFrom pH1141 (fmask pH1141) (cmask pH1141) (hmask pH1141) 1 1140 (true, (init pH1141), (init pH1141))) 1141 571 true = true :=
  fin_run (runOK_init (prmOK_of_and H1141_fin) true) (by decide) rfl H1141_fin ptTest_fst
theorem I1141_fin : (prmOK pI1141 1141 && intTest pI1141 (runFrom pI1141 (fmask pI1141) (cmask pI1141) (hmask pI1141) 1 1140 (true, (init pI1141), (init pI1141))) 1141 19 false) = true := by
  decide +kernel
theorem I1141_ok : RunOK pI1141 1141 (runFrom pI1141 (fmask pI1141) (cmask pI1141) (hmask pI1141) 1 1140 (true, (init pI1141), (init pI1141))) ∧ intTest pI1141 (runFrom pI1141 (fmask pI1141) (cmask pI1141) (hmask pI1141) 1 1140 (true, (init pI1141), (init pI1141))) 1141 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1141_fin) true) (by decide) rfl I1141_fin intTest_fst
theorem link1141 : linkOK pL1141 pH1141 pI1141 = true := by decide +kernel
theorem cvx1141 : ConvexBetweenHumps 1141 :=
  cvx_of L1141_ok H1141_ok I1141_ok link1141 (by decide)

/-! ### `N = 1142` -/

def pL1142 : Prm := ⟨76, 35, 38, 1144, 11, 18446744073709551616, 155143152609310401, 155143152609310401⟩
def pH1142 : Prm := ⟨76, 35, 38, 1144, 11, 18446744073709551616, 155145351632565953, 155145351632565953⟩
def pI1142 : Prm := ⟨66, 32, 31, 1144, 11, 18446744073709551616, 155143152609310401, 155145351632565953⟩
theorem L1142_fin : (prmOK pL1142 1142 && ptTest pL1142 (runFrom pL1142 (fmask pL1142) (cmask pL1142) (hmask pL1142) 1 1141 (true, (init pL1142), (init pL1142))) 1142 571 false) = true := by
  decide +kernel
theorem L1142_ok : RunOK pL1142 1142 (runFrom pL1142 (fmask pL1142) (cmask pL1142) (hmask pL1142) 1 1141 (true, (init pL1142), (init pL1142))) ∧ ptTest pL1142 (runFrom pL1142 (fmask pL1142) (cmask pL1142) (hmask pL1142) 1 1141 (true, (init pL1142), (init pL1142))) 1142 571 false = true :=
  fin_run (runOK_init (prmOK_of_and L1142_fin) true) (by decide) rfl L1142_fin ptTest_fst
theorem H1142_fin : (prmOK pH1142 1142 && ptTest pH1142 (runFrom pH1142 (fmask pH1142) (cmask pH1142) (hmask pH1142) 1 1141 (true, (init pH1142), (init pH1142))) 1142 571 true) = true := by
  decide +kernel
theorem H1142_ok : RunOK pH1142 1142 (runFrom pH1142 (fmask pH1142) (cmask pH1142) (hmask pH1142) 1 1141 (true, (init pH1142), (init pH1142))) ∧ ptTest pH1142 (runFrom pH1142 (fmask pH1142) (cmask pH1142) (hmask pH1142) 1 1141 (true, (init pH1142), (init pH1142))) 1142 571 true = true :=
  fin_run (runOK_init (prmOK_of_and H1142_fin) true) (by decide) rfl H1142_fin ptTest_fst
theorem I1142_fin : (prmOK pI1142 1142 && intTest pI1142 (runFrom pI1142 (fmask pI1142) (cmask pI1142) (hmask pI1142) 1 1141 (true, (init pI1142), (init pI1142))) 1142 19 true) = true := by
  decide +kernel
theorem I1142_ok : RunOK pI1142 1142 (runFrom pI1142 (fmask pI1142) (cmask pI1142) (hmask pI1142) 1 1141 (true, (init pI1142), (init pI1142))) ∧ intTest pI1142 (runFrom pI1142 (fmask pI1142) (cmask pI1142) (hmask pI1142) 1 1141 (true, (init pI1142), (init pI1142))) 1142 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1142_fin) true) (by decide) rfl I1142_fin intTest_fst
theorem link1142 : linkOK pL1142 pH1142 pI1142 = true := by decide +kernel
theorem cvx1142 : ConvexBetweenHumps 1142 :=
  cvx_of L1142_ok H1142_ok I1142_ok link1142 (by decide)
theorem cenlink1142 : cenLinkOK pI1142 1142 = true := by decide +kernel
theorem cen1142 : CenterUniqueMin 1142 ∧ DipHyp 1142 ∧ OnePointHyps 1142 :=
  cen_of L1142_ok H1142_ok I1142_ok link1142 cenlink1142

/-! ### `N = 1143` -/

def pL1143 : Prm := ⟨76, 35, 38, 1145, 11, 18446744073709551616, 155034020501035104, 155034020501035104⟩
def pH1143 : Prm := ⟨76, 35, 38, 1145, 11, 18446744073709551616, 155036219524290656, 155036219524290656⟩
def pI1143 : Prm := ⟨66, 32, 31, 1145, 11, 18446744073709551616, 155034020501035104, 155036219524290656⟩
theorem L1143_fin : (prmOK pL1143 1143 && ptTest pL1143 (runFrom pL1143 (fmask pL1143) (cmask pL1143) (hmask pL1143) 1 1142 (true, (init pL1143), (init pL1143))) 1143 572 false) = true := by
  decide +kernel
theorem L1143_ok : RunOK pL1143 1143 (runFrom pL1143 (fmask pL1143) (cmask pL1143) (hmask pL1143) 1 1142 (true, (init pL1143), (init pL1143))) ∧ ptTest pL1143 (runFrom pL1143 (fmask pL1143) (cmask pL1143) (hmask pL1143) 1 1142 (true, (init pL1143), (init pL1143))) 1143 572 false = true :=
  fin_run (runOK_init (prmOK_of_and L1143_fin) true) (by decide) rfl L1143_fin ptTest_fst
theorem H1143_fin : (prmOK pH1143 1143 && ptTest pH1143 (runFrom pH1143 (fmask pH1143) (cmask pH1143) (hmask pH1143) 1 1142 (true, (init pH1143), (init pH1143))) 1143 572 true) = true := by
  decide +kernel
theorem H1143_ok : RunOK pH1143 1143 (runFrom pH1143 (fmask pH1143) (cmask pH1143) (hmask pH1143) 1 1142 (true, (init pH1143), (init pH1143))) ∧ ptTest pH1143 (runFrom pH1143 (fmask pH1143) (cmask pH1143) (hmask pH1143) 1 1142 (true, (init pH1143), (init pH1143))) 1143 572 true = true :=
  fin_run (runOK_init (prmOK_of_and H1143_fin) true) (by decide) rfl H1143_fin ptTest_fst
theorem I1143_fin : (prmOK pI1143 1143 && intTest pI1143 (runFrom pI1143 (fmask pI1143) (cmask pI1143) (hmask pI1143) 1 1142 (true, (init pI1143), (init pI1143))) 1143 19 false) = true := by
  decide +kernel
theorem I1143_ok : RunOK pI1143 1143 (runFrom pI1143 (fmask pI1143) (cmask pI1143) (hmask pI1143) 1 1142 (true, (init pI1143), (init pI1143))) ∧ intTest pI1143 (runFrom pI1143 (fmask pI1143) (cmask pI1143) (hmask pI1143) 1 1142 (true, (init pI1143), (init pI1143))) 1143 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1143_fin) true) (by decide) rfl I1143_fin intTest_fst
theorem link1143 : linkOK pL1143 pH1143 pI1143 = true := by decide +kernel
theorem cvx1143 : ConvexBetweenHumps 1143 :=
  cvx_of L1143_ok H1143_ok I1143_ok link1143 (by decide)

/-! ### `N = 1144` -/

def pL1144 : Prm := ⟨76, 35, 38, 1146, 11, 18446744073709551616, 154925132690130465, 154925132690130465⟩
def pH1144 : Prm := ⟨76, 35, 38, 1146, 11, 18446744073709551616, 154927331713386017, 154927331713386017⟩
def pI1144 : Prm := ⟨66, 32, 31, 1146, 11, 18446744073709551616, 154925132690130465, 154927331713386017⟩
theorem L1144_fin : (prmOK pL1144 1144 && ptTest pL1144 (runFrom pL1144 (fmask pL1144) (cmask pL1144) (hmask pL1144) 1 1143 (true, (init pL1144), (init pL1144))) 1144 572 false) = true := by
  decide +kernel
theorem L1144_ok : RunOK pL1144 1144 (runFrom pL1144 (fmask pL1144) (cmask pL1144) (hmask pL1144) 1 1143 (true, (init pL1144), (init pL1144))) ∧ ptTest pL1144 (runFrom pL1144 (fmask pL1144) (cmask pL1144) (hmask pL1144) 1 1143 (true, (init pL1144), (init pL1144))) 1144 572 false = true :=
  fin_run (runOK_init (prmOK_of_and L1144_fin) true) (by decide) rfl L1144_fin ptTest_fst
theorem H1144_fin : (prmOK pH1144 1144 && ptTest pH1144 (runFrom pH1144 (fmask pH1144) (cmask pH1144) (hmask pH1144) 1 1143 (true, (init pH1144), (init pH1144))) 1144 572 true) = true := by
  decide +kernel
theorem H1144_ok : RunOK pH1144 1144 (runFrom pH1144 (fmask pH1144) (cmask pH1144) (hmask pH1144) 1 1143 (true, (init pH1144), (init pH1144))) ∧ ptTest pH1144 (runFrom pH1144 (fmask pH1144) (cmask pH1144) (hmask pH1144) 1 1143 (true, (init pH1144), (init pH1144))) 1144 572 true = true :=
  fin_run (runOK_init (prmOK_of_and H1144_fin) true) (by decide) rfl H1144_fin ptTest_fst
theorem I1144_fin : (prmOK pI1144 1144 && intTest pI1144 (runFrom pI1144 (fmask pI1144) (cmask pI1144) (hmask pI1144) 1 1143 (true, (init pI1144), (init pI1144))) 1144 19 true) = true := by
  decide +kernel
theorem I1144_ok : RunOK pI1144 1144 (runFrom pI1144 (fmask pI1144) (cmask pI1144) (hmask pI1144) 1 1143 (true, (init pI1144), (init pI1144))) ∧ intTest pI1144 (runFrom pI1144 (fmask pI1144) (cmask pI1144) (hmask pI1144) 1 1143 (true, (init pI1144), (init pI1144))) 1144 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1144_fin) true) (by decide) rfl I1144_fin intTest_fst
theorem link1144 : linkOK pL1144 pH1144 pI1144 = true := by decide +kernel
theorem cvx1144 : ConvexBetweenHumps 1144 :=
  cvx_of L1144_ok H1144_ok I1144_ok link1144 (by decide)
theorem cenlink1144 : cenLinkOK pI1144 1144 = true := by decide +kernel
theorem cen1144 : CenterUniqueMin 1144 ∧ DipHyp 1144 ∧ OnePointHyps 1144 :=
  cen_of L1144_ok H1144_ok I1144_ok link1144 cenlink1144

/-! ### `N = 1145` -/

def pL1145 : Prm := ⟨76, 35, 38, 1147, 11, 18446744073709551616, 154816335266943622, 154816335266943622⟩
def pH1145 : Prm := ⟨76, 35, 38, 1147, 11, 18446744073709551616, 154818534290199174, 154818534290199174⟩
def pI1145 : Prm := ⟨66, 32, 31, 1147, 11, 18446744073709551616, 154816335266943622, 154818534290199174⟩
theorem L1145_fin : (prmOK pL1145 1145 && ptTest pL1145 (runFrom pL1145 (fmask pL1145) (cmask pL1145) (hmask pL1145) 1 1144 (true, (init pL1145), (init pL1145))) 1145 573 false) = true := by
  decide +kernel
theorem L1145_ok : RunOK pL1145 1145 (runFrom pL1145 (fmask pL1145) (cmask pL1145) (hmask pL1145) 1 1144 (true, (init pL1145), (init pL1145))) ∧ ptTest pL1145 (runFrom pL1145 (fmask pL1145) (cmask pL1145) (hmask pL1145) 1 1144 (true, (init pL1145), (init pL1145))) 1145 573 false = true :=
  fin_run (runOK_init (prmOK_of_and L1145_fin) true) (by decide) rfl L1145_fin ptTest_fst
theorem H1145_fin : (prmOK pH1145 1145 && ptTest pH1145 (runFrom pH1145 (fmask pH1145) (cmask pH1145) (hmask pH1145) 1 1144 (true, (init pH1145), (init pH1145))) 1145 573 true) = true := by
  decide +kernel
theorem H1145_ok : RunOK pH1145 1145 (runFrom pH1145 (fmask pH1145) (cmask pH1145) (hmask pH1145) 1 1144 (true, (init pH1145), (init pH1145))) ∧ ptTest pH1145 (runFrom pH1145 (fmask pH1145) (cmask pH1145) (hmask pH1145) 1 1144 (true, (init pH1145), (init pH1145))) 1145 573 true = true :=
  fin_run (runOK_init (prmOK_of_and H1145_fin) true) (by decide) rfl H1145_fin ptTest_fst
theorem I1145_fin : (prmOK pI1145 1145 && intTest pI1145 (runFrom pI1145 (fmask pI1145) (cmask pI1145) (hmask pI1145) 1 1144 (true, (init pI1145), (init pI1145))) 1145 19 false) = true := by
  decide +kernel
theorem I1145_ok : RunOK pI1145 1145 (runFrom pI1145 (fmask pI1145) (cmask pI1145) (hmask pI1145) 1 1144 (true, (init pI1145), (init pI1145))) ∧ intTest pI1145 (runFrom pI1145 (fmask pI1145) (cmask pI1145) (hmask pI1145) 1 1144 (true, (init pI1145), (init pI1145))) 1145 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1145_fin) true) (by decide) rfl I1145_fin intTest_fst
theorem link1145 : linkOK pL1145 pH1145 pI1145 = true := by decide +kernel
theorem cvx1145 : ConvexBetweenHumps 1145 :=
  cvx_of L1145_ok H1145_ok I1145_ok link1145 (by decide)

/-! ### `N = 1146` -/

def pL1146 : Prm := ⟨76, 35, 38, 1148, 11, 18446744073709551616, 154707780937034664, 154707780937034664⟩
def pH1146 : Prm := ⟨76, 35, 38, 1148, 11, 18446744073709551616, 154709979960290216, 154709979960290216⟩
def pI1146 : Prm := ⟨65, 32, 30, 1148, 11, 18446744073709551616, 154707780937034664, 154709979960290216⟩
theorem L1146_fin : (prmOK pL1146 1146 && ptTest pL1146 (runFrom pL1146 (fmask pL1146) (cmask pL1146) (hmask pL1146) 1 1145 (true, (init pL1146), (init pL1146))) 1146 573 false) = true := by
  decide +kernel
theorem L1146_ok : RunOK pL1146 1146 (runFrom pL1146 (fmask pL1146) (cmask pL1146) (hmask pL1146) 1 1145 (true, (init pL1146), (init pL1146))) ∧ ptTest pL1146 (runFrom pL1146 (fmask pL1146) (cmask pL1146) (hmask pL1146) 1 1145 (true, (init pL1146), (init pL1146))) 1146 573 false = true :=
  fin_run (runOK_init (prmOK_of_and L1146_fin) true) (by decide) rfl L1146_fin ptTest_fst
theorem H1146_fin : (prmOK pH1146 1146 && ptTest pH1146 (runFrom pH1146 (fmask pH1146) (cmask pH1146) (hmask pH1146) 1 1145 (true, (init pH1146), (init pH1146))) 1146 573 true) = true := by
  decide +kernel
theorem H1146_ok : RunOK pH1146 1146 (runFrom pH1146 (fmask pH1146) (cmask pH1146) (hmask pH1146) 1 1145 (true, (init pH1146), (init pH1146))) ∧ ptTest pH1146 (runFrom pH1146 (fmask pH1146) (cmask pH1146) (hmask pH1146) 1 1145 (true, (init pH1146), (init pH1146))) 1146 573 true = true :=
  fin_run (runOK_init (prmOK_of_and H1146_fin) true) (by decide) rfl H1146_fin ptTest_fst
theorem I1146_fin : (prmOK pI1146 1146 && intTest pI1146 (runFrom pI1146 (fmask pI1146) (cmask pI1146) (hmask pI1146) 1 1145 (true, (init pI1146), (init pI1146))) 1146 19 true) = true := by
  decide +kernel
theorem I1146_ok : RunOK pI1146 1146 (runFrom pI1146 (fmask pI1146) (cmask pI1146) (hmask pI1146) 1 1145 (true, (init pI1146), (init pI1146))) ∧ intTest pI1146 (runFrom pI1146 (fmask pI1146) (cmask pI1146) (hmask pI1146) 1 1145 (true, (init pI1146), (init pI1146))) 1146 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1146_fin) true) (by decide) rfl I1146_fin intTest_fst
theorem link1146 : linkOK pL1146 pH1146 pI1146 = true := by decide +kernel
theorem cvx1146 : ConvexBetweenHumps 1146 :=
  cvx_of L1146_ok H1146_ok I1146_ok link1146 (by decide)
theorem cenlink1146 : cenLinkOK pI1146 1146 = true := by decide +kernel
theorem cen1146 : CenterUniqueMin 1146 ∧ DipHyp 1146 ∧ OnePointHyps 1146 :=
  cen_of L1146_ok H1146_ok I1146_ok link1146 cenlink1146

/-! ### `N = 1147` -/

def pL1147 : Prm := ⟨76, 35, 38, 1149, 11, 18446744073709551616, 154599316610025974, 154599316610025974⟩
def pH1147 : Prm := ⟨76, 35, 38, 1149, 11, 18446744073709551616, 154601515633281526, 154601515633281526⟩
def pI1147 : Prm := ⟨65, 32, 30, 1149, 11, 18446744073709551616, 154599316610025974, 154601515633281526⟩
theorem L1147_fin : (prmOK pL1147 1147 && ptTest pL1147 (runFrom pL1147 (fmask pL1147) (cmask pL1147) (hmask pL1147) 1 1146 (true, (init pL1147), (init pL1147))) 1147 574 false) = true := by
  decide +kernel
theorem L1147_ok : RunOK pL1147 1147 (runFrom pL1147 (fmask pL1147) (cmask pL1147) (hmask pL1147) 1 1146 (true, (init pL1147), (init pL1147))) ∧ ptTest pL1147 (runFrom pL1147 (fmask pL1147) (cmask pL1147) (hmask pL1147) 1 1146 (true, (init pL1147), (init pL1147))) 1147 574 false = true :=
  fin_run (runOK_init (prmOK_of_and L1147_fin) true) (by decide) rfl L1147_fin ptTest_fst
theorem H1147_fin : (prmOK pH1147 1147 && ptTest pH1147 (runFrom pH1147 (fmask pH1147) (cmask pH1147) (hmask pH1147) 1 1146 (true, (init pH1147), (init pH1147))) 1147 574 true) = true := by
  decide +kernel
theorem H1147_ok : RunOK pH1147 1147 (runFrom pH1147 (fmask pH1147) (cmask pH1147) (hmask pH1147) 1 1146 (true, (init pH1147), (init pH1147))) ∧ ptTest pH1147 (runFrom pH1147 (fmask pH1147) (cmask pH1147) (hmask pH1147) 1 1146 (true, (init pH1147), (init pH1147))) 1147 574 true = true :=
  fin_run (runOK_init (prmOK_of_and H1147_fin) true) (by decide) rfl H1147_fin ptTest_fst
theorem I1147_fin : (prmOK pI1147 1147 && intTest pI1147 (runFrom pI1147 (fmask pI1147) (cmask pI1147) (hmask pI1147) 1 1146 (true, (init pI1147), (init pI1147))) 1147 19 false) = true := by
  decide +kernel
theorem I1147_ok : RunOK pI1147 1147 (runFrom pI1147 (fmask pI1147) (cmask pI1147) (hmask pI1147) 1 1146 (true, (init pI1147), (init pI1147))) ∧ intTest pI1147 (runFrom pI1147 (fmask pI1147) (cmask pI1147) (hmask pI1147) 1 1146 (true, (init pI1147), (init pI1147))) 1147 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1147_fin) true) (by decide) rfl I1147_fin intTest_fst
theorem link1147 : linkOK pL1147 pH1147 pI1147 = true := by decide +kernel
theorem cvx1147 : ConvexBetweenHumps 1147 :=
  cvx_of L1147_ok H1147_ok I1147_ok link1147 (by decide)

/-! ### `N = 1148` -/

def pL1148 : Prm := ⟨76, 35, 38, 1150, 11, 18446744073709551616, 154491094180245177, 154491094180245177⟩
def pH1148 : Prm := ⟨76, 35, 38, 1150, 11, 18446744073709551616, 154493293203500729, 154493293203500729⟩
def pI1148 : Prm := ⟨65, 32, 30, 1150, 11, 18446744073709551616, 154491094180245177, 154493293203500729⟩
theorem L1148_fin : (prmOK pL1148 1148 && ptTest pL1148 (runFrom pL1148 (fmask pL1148) (cmask pL1148) (hmask pL1148) 1 1147 (true, (init pL1148), (init pL1148))) 1148 574 false) = true := by
  decide +kernel
theorem L1148_ok : RunOK pL1148 1148 (runFrom pL1148 (fmask pL1148) (cmask pL1148) (hmask pL1148) 1 1147 (true, (init pL1148), (init pL1148))) ∧ ptTest pL1148 (runFrom pL1148 (fmask pL1148) (cmask pL1148) (hmask pL1148) 1 1147 (true, (init pL1148), (init pL1148))) 1148 574 false = true :=
  fin_run (runOK_init (prmOK_of_and L1148_fin) true) (by decide) rfl L1148_fin ptTest_fst
theorem H1148_fin : (prmOK pH1148 1148 && ptTest pH1148 (runFrom pH1148 (fmask pH1148) (cmask pH1148) (hmask pH1148) 1 1147 (true, (init pH1148), (init pH1148))) 1148 574 true) = true := by
  decide +kernel
theorem H1148_ok : RunOK pH1148 1148 (runFrom pH1148 (fmask pH1148) (cmask pH1148) (hmask pH1148) 1 1147 (true, (init pH1148), (init pH1148))) ∧ ptTest pH1148 (runFrom pH1148 (fmask pH1148) (cmask pH1148) (hmask pH1148) 1 1147 (true, (init pH1148), (init pH1148))) 1148 574 true = true :=
  fin_run (runOK_init (prmOK_of_and H1148_fin) true) (by decide) rfl H1148_fin ptTest_fst
theorem I1148_fin : (prmOK pI1148 1148 && intTest pI1148 (runFrom pI1148 (fmask pI1148) (cmask pI1148) (hmask pI1148) 1 1147 (true, (init pI1148), (init pI1148))) 1148 19 true) = true := by
  decide +kernel
theorem I1148_ok : RunOK pI1148 1148 (runFrom pI1148 (fmask pI1148) (cmask pI1148) (hmask pI1148) 1 1147 (true, (init pI1148), (init pI1148))) ∧ intTest pI1148 (runFrom pI1148 (fmask pI1148) (cmask pI1148) (hmask pI1148) 1 1147 (true, (init pI1148), (init pI1148))) 1148 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1148_fin) true) (by decide) rfl I1148_fin intTest_fst
theorem link1148 : linkOK pL1148 pH1148 pI1148 = true := by decide +kernel
theorem cvx1148 : ConvexBetweenHumps 1148 :=
  cvx_of L1148_ok H1148_ok I1148_ok link1148 (by decide)
theorem cenlink1148 : cenLinkOK pI1148 1148 = true := by decide +kernel
theorem cen1148 : CenterUniqueMin 1148 ∧ DipHyp 1148 ∧ OnePointHyps 1148 :=
  cen_of L1148_ok H1148_ok I1148_ok link1148 cenlink1148

/-! ### `N = 1149` -/

def pL1149 : Prm := ⟨76, 35, 38, 1151, 11, 18446744073709551616, 154382961370760729, 154382961370760729⟩
def pH1149 : Prm := ⟨76, 35, 38, 1151, 11, 18446744073709551616, 154385160394016281, 154385160394016281⟩
def pI1149 : Prm := ⟨65, 32, 30, 1151, 11, 18446744073709551616, 154382961370760729, 154385160394016281⟩
theorem L1149_fin : (prmOK pL1149 1149 && ptTest pL1149 (runFrom pL1149 (fmask pL1149) (cmask pL1149) (hmask pL1149) 1 1148 (true, (init pL1149), (init pL1149))) 1149 575 false) = true := by
  decide +kernel
theorem L1149_ok : RunOK pL1149 1149 (runFrom pL1149 (fmask pL1149) (cmask pL1149) (hmask pL1149) 1 1148 (true, (init pL1149), (init pL1149))) ∧ ptTest pL1149 (runFrom pL1149 (fmask pL1149) (cmask pL1149) (hmask pL1149) 1 1148 (true, (init pL1149), (init pL1149))) 1149 575 false = true :=
  fin_run (runOK_init (prmOK_of_and L1149_fin) true) (by decide) rfl L1149_fin ptTest_fst
theorem H1149_fin : (prmOK pH1149 1149 && ptTest pH1149 (runFrom pH1149 (fmask pH1149) (cmask pH1149) (hmask pH1149) 1 1148 (true, (init pH1149), (init pH1149))) 1149 575 true) = true := by
  decide +kernel
theorem H1149_ok : RunOK pH1149 1149 (runFrom pH1149 (fmask pH1149) (cmask pH1149) (hmask pH1149) 1 1148 (true, (init pH1149), (init pH1149))) ∧ ptTest pH1149 (runFrom pH1149 (fmask pH1149) (cmask pH1149) (hmask pH1149) 1 1148 (true, (init pH1149), (init pH1149))) 1149 575 true = true :=
  fin_run (runOK_init (prmOK_of_and H1149_fin) true) (by decide) rfl H1149_fin ptTest_fst
theorem I1149_fin : (prmOK pI1149 1149 && intTest pI1149 (runFrom pI1149 (fmask pI1149) (cmask pI1149) (hmask pI1149) 1 1148 (true, (init pI1149), (init pI1149))) 1149 19 false) = true := by
  decide +kernel
theorem I1149_ok : RunOK pI1149 1149 (runFrom pI1149 (fmask pI1149) (cmask pI1149) (hmask pI1149) 1 1148 (true, (init pI1149), (init pI1149))) ∧ intTest pI1149 (runFrom pI1149 (fmask pI1149) (cmask pI1149) (hmask pI1149) 1 1148 (true, (init pI1149), (init pI1149))) 1149 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1149_fin) true) (by decide) rfl I1149_fin intTest_fst
theorem link1149 : linkOK pL1149 pH1149 pI1149 = true := by decide +kernel
theorem cvx1149 : ConvexBetweenHumps 1149 :=
  cvx_of L1149_ok H1149_ok I1149_ok link1149 (by decide)

/-! ### `N = 1150` -/

def pL1150 : Prm := ⟨76, 35, 38, 1152, 11, 18446744073709551616, 154275069270367835, 154275069270367835⟩
def pH1150 : Prm := ⟨76, 35, 38, 1152, 11, 18446744073709551616, 154277268293623387, 154277268293623387⟩
def pI1150 : Prm := ⟨65, 32, 30, 1152, 11, 18446744073709551616, 154275069270367835, 154277268293623387⟩
theorem L1150_fin : (prmOK pL1150 1150 && ptTest pL1150 (runFrom pL1150 (fmask pL1150) (cmask pL1150) (hmask pL1150) 1 1149 (true, (init pL1150), (init pL1150))) 1150 575 false) = true := by
  decide +kernel
theorem L1150_ok : RunOK pL1150 1150 (runFrom pL1150 (fmask pL1150) (cmask pL1150) (hmask pL1150) 1 1149 (true, (init pL1150), (init pL1150))) ∧ ptTest pL1150 (runFrom pL1150 (fmask pL1150) (cmask pL1150) (hmask pL1150) 1 1149 (true, (init pL1150), (init pL1150))) 1150 575 false = true :=
  fin_run (runOK_init (prmOK_of_and L1150_fin) true) (by decide) rfl L1150_fin ptTest_fst
theorem H1150_fin : (prmOK pH1150 1150 && ptTest pH1150 (runFrom pH1150 (fmask pH1150) (cmask pH1150) (hmask pH1150) 1 1149 (true, (init pH1150), (init pH1150))) 1150 575 true) = true := by
  decide +kernel
theorem H1150_ok : RunOK pH1150 1150 (runFrom pH1150 (fmask pH1150) (cmask pH1150) (hmask pH1150) 1 1149 (true, (init pH1150), (init pH1150))) ∧ ptTest pH1150 (runFrom pH1150 (fmask pH1150) (cmask pH1150) (hmask pH1150) 1 1149 (true, (init pH1150), (init pH1150))) 1150 575 true = true :=
  fin_run (runOK_init (prmOK_of_and H1150_fin) true) (by decide) rfl H1150_fin ptTest_fst
theorem I1150_fin : (prmOK pI1150 1150 && intTest pI1150 (runFrom pI1150 (fmask pI1150) (cmask pI1150) (hmask pI1150) 1 1149 (true, (init pI1150), (init pI1150))) 1150 19 true) = true := by
  decide +kernel
theorem I1150_ok : RunOK pI1150 1150 (runFrom pI1150 (fmask pI1150) (cmask pI1150) (hmask pI1150) 1 1149 (true, (init pI1150), (init pI1150))) ∧ intTest pI1150 (runFrom pI1150 (fmask pI1150) (cmask pI1150) (hmask pI1150) 1 1149 (true, (init pI1150), (init pI1150))) 1150 19 true = true :=
  fin_run (runOK_init (prmOK_of_and I1150_fin) true) (by decide) rfl I1150_fin intTest_fst
theorem link1150 : linkOK pL1150 pH1150 pI1150 = true := by decide +kernel
theorem cvx1150 : ConvexBetweenHumps 1150 :=
  cvx_of L1150_ok H1150_ok I1150_ok link1150 (by decide)
theorem cenlink1150 : cenLinkOK pI1150 1150 = true := by decide +kernel
theorem cen1150 : CenterUniqueMin 1150 ∧ DipHyp 1150 ∧ OnePointHyps 1150 :=
  cen_of L1150_ok H1150_ok I1150_ok link1150 cenlink1150

/-! ### `N = 1151` -/

def pL1151 : Prm := ⟨76, 35, 38, 1153, 11, 18446744073709551616, 154167266409899427, 154167266409899427⟩
def pH1151 : Prm := ⟨76, 35, 38, 1153, 11, 18446744073709551616, 154169465433154979, 154169465433154979⟩
def pI1151 : Prm := ⟨65, 32, 30, 1153, 11, 18446744073709551616, 154167266409899427, 154169465433154979⟩
theorem L1151_fin : (prmOK pL1151 1151 && ptTest pL1151 (runFrom pL1151 (fmask pL1151) (cmask pL1151) (hmask pL1151) 1 1150 (true, (init pL1151), (init pL1151))) 1151 576 false) = true := by
  decide +kernel
theorem L1151_ok : RunOK pL1151 1151 (runFrom pL1151 (fmask pL1151) (cmask pL1151) (hmask pL1151) 1 1150 (true, (init pL1151), (init pL1151))) ∧ ptTest pL1151 (runFrom pL1151 (fmask pL1151) (cmask pL1151) (hmask pL1151) 1 1150 (true, (init pL1151), (init pL1151))) 1151 576 false = true :=
  fin_run (runOK_init (prmOK_of_and L1151_fin) true) (by decide) rfl L1151_fin ptTest_fst
theorem H1151_fin : (prmOK pH1151 1151 && ptTest pH1151 (runFrom pH1151 (fmask pH1151) (cmask pH1151) (hmask pH1151) 1 1150 (true, (init pH1151), (init pH1151))) 1151 576 true) = true := by
  decide +kernel
theorem H1151_ok : RunOK pH1151 1151 (runFrom pH1151 (fmask pH1151) (cmask pH1151) (hmask pH1151) 1 1150 (true, (init pH1151), (init pH1151))) ∧ ptTest pH1151 (runFrom pH1151 (fmask pH1151) (cmask pH1151) (hmask pH1151) 1 1150 (true, (init pH1151), (init pH1151))) 1151 576 true = true :=
  fin_run (runOK_init (prmOK_of_and H1151_fin) true) (by decide) rfl H1151_fin ptTest_fst
theorem I1151_fin : (prmOK pI1151 1151 && intTest pI1151 (runFrom pI1151 (fmask pI1151) (cmask pI1151) (hmask pI1151) 1 1150 (true, (init pI1151), (init pI1151))) 1151 19 false) = true := by
  decide +kernel
theorem I1151_ok : RunOK pI1151 1151 (runFrom pI1151 (fmask pI1151) (cmask pI1151) (hmask pI1151) 1 1150 (true, (init pI1151), (init pI1151))) ∧ intTest pI1151 (runFrom pI1151 (fmask pI1151) (cmask pI1151) (hmask pI1151) 1 1150 (true, (init pI1151), (init pI1151))) 1151 19 false = true :=
  fin_run (runOK_init (prmOK_of_and I1151_fin) true) (by decide) rfl I1151_fin intTest_fst
theorem link1151 : linkOK pL1151 pH1151 pI1151 = true := by decide +kernel
theorem cvx1151 : ConvexBetweenHumps 1151 :=
  cvx_of L1151_ok H1151_ok I1151_ok link1151 (by decide)

/-! ### The range -/

theorem cvx_1120_1151 {N : ℕ} (h1 : 1120 ≤ N) (h2 : N ≤ 1151) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1135
  · by_cases h4 : N ≤ 1127
    · by_cases h6 : N ≤ 1123
      · by_cases h8 : N ≤ 1121
        · by_cases h10 : N ≤ 1120
          · obtain rfl : N = 1120 := by omega
            exact cvx1120
          · obtain rfl : N = 1121 := by omega
            exact cvx1121
        · by_cases h10 : N ≤ 1122
          · obtain rfl : N = 1122 := by omega
            exact cvx1122
          · obtain rfl : N = 1123 := by omega
            exact cvx1123
      · by_cases h8 : N ≤ 1125
        · by_cases h10 : N ≤ 1124
          · obtain rfl : N = 1124 := by omega
            exact cvx1124
          · obtain rfl : N = 1125 := by omega
            exact cvx1125
        · by_cases h10 : N ≤ 1126
          · obtain rfl : N = 1126 := by omega
            exact cvx1126
          · obtain rfl : N = 1127 := by omega
            exact cvx1127
    · by_cases h6 : N ≤ 1131
      · by_cases h8 : N ≤ 1129
        · by_cases h10 : N ≤ 1128
          · obtain rfl : N = 1128 := by omega
            exact cvx1128
          · obtain rfl : N = 1129 := by omega
            exact cvx1129
        · by_cases h10 : N ≤ 1130
          · obtain rfl : N = 1130 := by omega
            exact cvx1130
          · obtain rfl : N = 1131 := by omega
            exact cvx1131
      · by_cases h8 : N ≤ 1133
        · by_cases h10 : N ≤ 1132
          · obtain rfl : N = 1132 := by omega
            exact cvx1132
          · obtain rfl : N = 1133 := by omega
            exact cvx1133
        · by_cases h10 : N ≤ 1134
          · obtain rfl : N = 1134 := by omega
            exact cvx1134
          · obtain rfl : N = 1135 := by omega
            exact cvx1135
  · by_cases h4 : N ≤ 1143
    · by_cases h6 : N ≤ 1139
      · by_cases h8 : N ≤ 1137
        · by_cases h10 : N ≤ 1136
          · obtain rfl : N = 1136 := by omega
            exact cvx1136
          · obtain rfl : N = 1137 := by omega
            exact cvx1137
        · by_cases h10 : N ≤ 1138
          · obtain rfl : N = 1138 := by omega
            exact cvx1138
          · obtain rfl : N = 1139 := by omega
            exact cvx1139
      · by_cases h8 : N ≤ 1141
        · by_cases h10 : N ≤ 1140
          · obtain rfl : N = 1140 := by omega
            exact cvx1140
          · obtain rfl : N = 1141 := by omega
            exact cvx1141
        · by_cases h10 : N ≤ 1142
          · obtain rfl : N = 1142 := by omega
            exact cvx1142
          · obtain rfl : N = 1143 := by omega
            exact cvx1143
    · by_cases h6 : N ≤ 1147
      · by_cases h8 : N ≤ 1145
        · by_cases h10 : N ≤ 1144
          · obtain rfl : N = 1144 := by omega
            exact cvx1144
          · obtain rfl : N = 1145 := by omega
            exact cvx1145
        · by_cases h10 : N ≤ 1146
          · obtain rfl : N = 1146 := by omega
            exact cvx1146
          · obtain rfl : N = 1147 := by omega
            exact cvx1147
      · by_cases h8 : N ≤ 1149
        · by_cases h10 : N ≤ 1148
          · obtain rfl : N = 1148 := by omega
            exact cvx1148
          · obtain rfl : N = 1149 := by omega
            exact cvx1149
        · by_cases h10 : N ≤ 1150
          · obtain rfl : N = 1150 := by omega
            exact cvx1150
          · obtain rfl : N = 1151 := by omega
            exact cvx1151

theorem cen_1120_1151 {N : ℕ} (h1 : 1120 ≤ N) (h2 : N ≤ 1151) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1134
  · by_cases h4 : N ≤ 1126
    · by_cases h6 : N ≤ 1122
      · by_cases h8 : N ≤ 1120
        · obtain rfl : N = 1120 := by omega
          exact cen1120
        · obtain rfl : N = 1122 := by omega
          exact cen1122
      · by_cases h8 : N ≤ 1124
        · obtain rfl : N = 1124 := by omega
          exact cen1124
        · obtain rfl : N = 1126 := by omega
          exact cen1126
    · by_cases h6 : N ≤ 1130
      · by_cases h8 : N ≤ 1128
        · obtain rfl : N = 1128 := by omega
          exact cen1128
        · obtain rfl : N = 1130 := by omega
          exact cen1130
      · by_cases h8 : N ≤ 1132
        · obtain rfl : N = 1132 := by omega
          exact cen1132
        · obtain rfl : N = 1134 := by omega
          exact cen1134
  · by_cases h4 : N ≤ 1142
    · by_cases h6 : N ≤ 1138
      · by_cases h8 : N ≤ 1136
        · obtain rfl : N = 1136 := by omega
          exact cen1136
        · obtain rfl : N = 1138 := by omega
          exact cen1138
      · by_cases h8 : N ≤ 1140
        · obtain rfl : N = 1140 := by omega
          exact cen1140
        · obtain rfl : N = 1142 := by omega
          exact cen1142
    · by_cases h6 : N ≤ 1146
      · by_cases h8 : N ≤ 1144
        · obtain rfl : N = 1144 := by omega
          exact cen1144
        · obtain rfl : N = 1146 := by omega
          exact cen1146
      · by_cases h8 : N ≤ 1148
        · obtain rfl : N = 1148 := by omega
          exact cen1148
        · obtain rfl : N = 1150 := by omega
          exact cen1150

end Kagey131.PaperD.T7
