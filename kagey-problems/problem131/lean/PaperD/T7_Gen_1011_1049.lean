import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1011, …, 1049` (generated)

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

/-! ### `N = 1011` -/

def pL1011 : Prm := ⟨76, 36, 37, 1013, 11, 18446744073709551616, 171053189045702640, 171053189045702640⟩
def pH1011 : Prm := ⟨76, 36, 37, 1013, 11, 18446744073709551616, 171055388068958192, 171055388068958192⟩
def pI1011 : Prm := ⟨64, 32, 29, 1013, 11, 18446744073709551616, 171053189045702640, 171055388068958192⟩
theorem L1011_fin : (prmOK pL1011 1011 && ptTest pL1011 (runFrom pL1011 (fmask pL1011) (cmask pL1011) (hmask pL1011) 1 1010 (true, (init pL1011), (init pL1011))) 1011 506 false) = true := by
  decide +kernel
theorem L1011_ok : RunOK pL1011 1011 (runFrom pL1011 (fmask pL1011) (cmask pL1011) (hmask pL1011) 1 1010 (true, (init pL1011), (init pL1011))) ∧ ptTest pL1011 (runFrom pL1011 (fmask pL1011) (cmask pL1011) (hmask pL1011) 1 1010 (true, (init pL1011), (init pL1011))) 1011 506 false = true :=
  fin_run (runOK_init (prmOK_of_and L1011_fin) true) (by decide) rfl L1011_fin ptTest_fst
theorem H1011_fin : (prmOK pH1011 1011 && ptTest pH1011 (runFrom pH1011 (fmask pH1011) (cmask pH1011) (hmask pH1011) 1 1010 (true, (init pH1011), (init pH1011))) 1011 506 true) = true := by
  decide +kernel
theorem H1011_ok : RunOK pH1011 1011 (runFrom pH1011 (fmask pH1011) (cmask pH1011) (hmask pH1011) 1 1010 (true, (init pH1011), (init pH1011))) ∧ ptTest pH1011 (runFrom pH1011 (fmask pH1011) (cmask pH1011) (hmask pH1011) 1 1010 (true, (init pH1011), (init pH1011))) 1011 506 true = true :=
  fin_run (runOK_init (prmOK_of_and H1011_fin) true) (by decide) rfl H1011_fin ptTest_fst
theorem I1011_fin : (prmOK pI1011 1011 && intTest pI1011 (runFrom pI1011 (fmask pI1011) (cmask pI1011) (hmask pI1011) 1 1010 (true, (init pI1011), (init pI1011))) 1011 18 false) = true := by
  decide +kernel
theorem I1011_ok : RunOK pI1011 1011 (runFrom pI1011 (fmask pI1011) (cmask pI1011) (hmask pI1011) 1 1010 (true, (init pI1011), (init pI1011))) ∧ intTest pI1011 (runFrom pI1011 (fmask pI1011) (cmask pI1011) (hmask pI1011) 1 1010 (true, (init pI1011), (init pI1011))) 1011 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1011_fin) true) (by decide) rfl I1011_fin intTest_fst
theorem link1011 : linkOK pL1011 pH1011 pI1011 = true := by decide +kernel
theorem cvx1011 : ConvexBetweenHumps 1011 :=
  cvx_of L1011_ok H1011_ok I1011_ok link1011 (by decide)

/-! ### `N = 1012` -/

def pL1012 : Prm := ⟨76, 36, 37, 1014, 11, 18446744073709551616, 170918204759308438, 170918204759308438⟩
def pH1012 : Prm := ⟨76, 36, 37, 1014, 11, 18446744073709551616, 170920403782563990, 170920403782563990⟩
def pI1012 : Prm := ⟨64, 32, 29, 1014, 11, 18446744073709551616, 170918204759308438, 170920403782563990⟩
theorem L1012_fin : (prmOK pL1012 1012 && ptTest pL1012 (runFrom pL1012 (fmask pL1012) (cmask pL1012) (hmask pL1012) 1 1011 (true, (init pL1012), (init pL1012))) 1012 506 false) = true := by
  decide +kernel
theorem L1012_ok : RunOK pL1012 1012 (runFrom pL1012 (fmask pL1012) (cmask pL1012) (hmask pL1012) 1 1011 (true, (init pL1012), (init pL1012))) ∧ ptTest pL1012 (runFrom pL1012 (fmask pL1012) (cmask pL1012) (hmask pL1012) 1 1011 (true, (init pL1012), (init pL1012))) 1012 506 false = true :=
  fin_run (runOK_init (prmOK_of_and L1012_fin) true) (by decide) rfl L1012_fin ptTest_fst
theorem H1012_fin : (prmOK pH1012 1012 && ptTest pH1012 (runFrom pH1012 (fmask pH1012) (cmask pH1012) (hmask pH1012) 1 1011 (true, (init pH1012), (init pH1012))) 1012 506 true) = true := by
  decide +kernel
theorem H1012_ok : RunOK pH1012 1012 (runFrom pH1012 (fmask pH1012) (cmask pH1012) (hmask pH1012) 1 1011 (true, (init pH1012), (init pH1012))) ∧ ptTest pH1012 (runFrom pH1012 (fmask pH1012) (cmask pH1012) (hmask pH1012) 1 1011 (true, (init pH1012), (init pH1012))) 1012 506 true = true :=
  fin_run (runOK_init (prmOK_of_and H1012_fin) true) (by decide) rfl H1012_fin ptTest_fst
theorem I1012_fin : (prmOK pI1012 1012 && intTest pI1012 (runFrom pI1012 (fmask pI1012) (cmask pI1012) (hmask pI1012) 1 1011 (true, (init pI1012), (init pI1012))) 1012 18 true) = true := by
  decide +kernel
theorem I1012_ok : RunOK pI1012 1012 (runFrom pI1012 (fmask pI1012) (cmask pI1012) (hmask pI1012) 1 1011 (true, (init pI1012), (init pI1012))) ∧ intTest pI1012 (runFrom pI1012 (fmask pI1012) (cmask pI1012) (hmask pI1012) 1 1011 (true, (init pI1012), (init pI1012))) 1012 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1012_fin) true) (by decide) rfl I1012_fin intTest_fst
theorem link1012 : linkOK pL1012 pH1012 pI1012 = true := by decide +kernel
theorem cvx1012 : ConvexBetweenHumps 1012 :=
  cvx_of L1012_ok H1012_ok I1012_ok link1012 (by decide)
theorem cenlink1012 : cenLinkOK pI1012 1012 = true := by decide +kernel
theorem cen1012 : CenterUniqueMin 1012 ∧ DipHyp 1012 ∧ OnePointHyps 1012 :=
  cen_of L1012_ok H1012_ok I1012_ok link1012 cenlink1012

/-! ### `N = 1013` -/

def pL1013 : Prm := ⟨76, 36, 37, 1015, 11, 18446744073709551616, 170783342110781551, 170783342110781551⟩
def pH1013 : Prm := ⟨76, 36, 37, 1015, 11, 18446744073709551616, 170785541134037103, 170785541134037103⟩
def pI1013 : Prm := ⟨64, 32, 29, 1015, 11, 18446744073709551616, 170783342110781551, 170785541134037103⟩
theorem L1013_fin : (prmOK pL1013 1013 && ptTest pL1013 (runFrom pL1013 (fmask pL1013) (cmask pL1013) (hmask pL1013) 1 1012 (true, (init pL1013), (init pL1013))) 1013 507 false) = true := by
  decide +kernel
theorem L1013_ok : RunOK pL1013 1013 (runFrom pL1013 (fmask pL1013) (cmask pL1013) (hmask pL1013) 1 1012 (true, (init pL1013), (init pL1013))) ∧ ptTest pL1013 (runFrom pL1013 (fmask pL1013) (cmask pL1013) (hmask pL1013) 1 1012 (true, (init pL1013), (init pL1013))) 1013 507 false = true :=
  fin_run (runOK_init (prmOK_of_and L1013_fin) true) (by decide) rfl L1013_fin ptTest_fst
theorem H1013_fin : (prmOK pH1013 1013 && ptTest pH1013 (runFrom pH1013 (fmask pH1013) (cmask pH1013) (hmask pH1013) 1 1012 (true, (init pH1013), (init pH1013))) 1013 507 true) = true := by
  decide +kernel
theorem H1013_ok : RunOK pH1013 1013 (runFrom pH1013 (fmask pH1013) (cmask pH1013) (hmask pH1013) 1 1012 (true, (init pH1013), (init pH1013))) ∧ ptTest pH1013 (runFrom pH1013 (fmask pH1013) (cmask pH1013) (hmask pH1013) 1 1012 (true, (init pH1013), (init pH1013))) 1013 507 true = true :=
  fin_run (runOK_init (prmOK_of_and H1013_fin) true) (by decide) rfl H1013_fin ptTest_fst
theorem I1013_fin : (prmOK pI1013 1013 && intTest pI1013 (runFrom pI1013 (fmask pI1013) (cmask pI1013) (hmask pI1013) 1 1012 (true, (init pI1013), (init pI1013))) 1013 18 false) = true := by
  decide +kernel
theorem I1013_ok : RunOK pI1013 1013 (runFrom pI1013 (fmask pI1013) (cmask pI1013) (hmask pI1013) 1 1012 (true, (init pI1013), (init pI1013))) ∧ intTest pI1013 (runFrom pI1013 (fmask pI1013) (cmask pI1013) (hmask pI1013) 1 1012 (true, (init pI1013), (init pI1013))) 1013 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1013_fin) true) (by decide) rfl I1013_fin intTest_fst
theorem link1013 : linkOK pL1013 pH1013 pI1013 = true := by decide +kernel
theorem cvx1013 : ConvexBetweenHumps 1013 :=
  cvx_of L1013_ok H1013_ok I1013_ok link1013 (by decide)

/-! ### `N = 1014` -/

def pL1014 : Prm := ⟨76, 36, 37, 1016, 11, 18446744073709551616, 170648823052269011, 170648823052269011⟩
def pH1014 : Prm := ⟨76, 36, 37, 1016, 11, 18446744073709551616, 170651022075524563, 170651022075524563⟩
def pI1014 : Prm := ⟨64, 32, 29, 1016, 11, 18446744073709551616, 170648823052269011, 170651022075524563⟩
theorem L1014_fin : (prmOK pL1014 1014 && ptTest pL1014 (runFrom pL1014 (fmask pL1014) (cmask pL1014) (hmask pL1014) 1 1013 (true, (init pL1014), (init pL1014))) 1014 507 false) = true := by
  decide +kernel
theorem L1014_ok : RunOK pL1014 1014 (runFrom pL1014 (fmask pL1014) (cmask pL1014) (hmask pL1014) 1 1013 (true, (init pL1014), (init pL1014))) ∧ ptTest pL1014 (runFrom pL1014 (fmask pL1014) (cmask pL1014) (hmask pL1014) 1 1013 (true, (init pL1014), (init pL1014))) 1014 507 false = true :=
  fin_run (runOK_init (prmOK_of_and L1014_fin) true) (by decide) rfl L1014_fin ptTest_fst
theorem H1014_fin : (prmOK pH1014 1014 && ptTest pH1014 (runFrom pH1014 (fmask pH1014) (cmask pH1014) (hmask pH1014) 1 1013 (true, (init pH1014), (init pH1014))) 1014 507 true) = true := by
  decide +kernel
theorem H1014_ok : RunOK pH1014 1014 (runFrom pH1014 (fmask pH1014) (cmask pH1014) (hmask pH1014) 1 1013 (true, (init pH1014), (init pH1014))) ∧ ptTest pH1014 (runFrom pH1014 (fmask pH1014) (cmask pH1014) (hmask pH1014) 1 1013 (true, (init pH1014), (init pH1014))) 1014 507 true = true :=
  fin_run (runOK_init (prmOK_of_and H1014_fin) true) (by decide) rfl H1014_fin ptTest_fst
theorem I1014_fin : (prmOK pI1014 1014 && intTest pI1014 (runFrom pI1014 (fmask pI1014) (cmask pI1014) (hmask pI1014) 1 1013 (true, (init pI1014), (init pI1014))) 1014 18 true) = true := by
  decide +kernel
theorem I1014_ok : RunOK pI1014 1014 (runFrom pI1014 (fmask pI1014) (cmask pI1014) (hmask pI1014) 1 1013 (true, (init pI1014), (init pI1014))) ∧ intTest pI1014 (runFrom pI1014 (fmask pI1014) (cmask pI1014) (hmask pI1014) 1 1013 (true, (init pI1014), (init pI1014))) 1014 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1014_fin) true) (by decide) rfl I1014_fin intTest_fst
theorem link1014 : linkOK pL1014 pH1014 pI1014 = true := by decide +kernel
theorem cvx1014 : ConvexBetweenHumps 1014 :=
  cvx_of L1014_ok H1014_ok I1014_ok link1014 (by decide)
theorem cenlink1014 : cenLinkOK pI1014 1014 = true := by decide +kernel
theorem cen1014 : CenterUniqueMin 1014 ∧ DipHyp 1014 ∧ OnePointHyps 1014 :=
  cen_of L1014_ok H1014_ok I1014_ok link1014 cenlink1014

/-! ### `N = 1015` -/

def pL1015 : Prm := ⟨76, 36, 37, 1017, 11, 18446744073709551616, 170514425056306733, 170514425056306733⟩
def pH1015 : Prm := ⟨76, 36, 37, 1017, 11, 18446744073709551616, 170516624079562285, 170516624079562285⟩
def pI1015 : Prm := ⟨64, 32, 29, 1017, 11, 18446744073709551616, 170514425056306733, 170516624079562285⟩
theorem L1015_fin : (prmOK pL1015 1015 && ptTest pL1015 (runFrom pL1015 (fmask pL1015) (cmask pL1015) (hmask pL1015) 1 1014 (true, (init pL1015), (init pL1015))) 1015 508 false) = true := by
  decide +kernel
theorem L1015_ok : RunOK pL1015 1015 (runFrom pL1015 (fmask pL1015) (cmask pL1015) (hmask pL1015) 1 1014 (true, (init pL1015), (init pL1015))) ∧ ptTest pL1015 (runFrom pL1015 (fmask pL1015) (cmask pL1015) (hmask pL1015) 1 1014 (true, (init pL1015), (init pL1015))) 1015 508 false = true :=
  fin_run (runOK_init (prmOK_of_and L1015_fin) true) (by decide) rfl L1015_fin ptTest_fst
theorem H1015_fin : (prmOK pH1015 1015 && ptTest pH1015 (runFrom pH1015 (fmask pH1015) (cmask pH1015) (hmask pH1015) 1 1014 (true, (init pH1015), (init pH1015))) 1015 508 true) = true := by
  decide +kernel
theorem H1015_ok : RunOK pH1015 1015 (runFrom pH1015 (fmask pH1015) (cmask pH1015) (hmask pH1015) 1 1014 (true, (init pH1015), (init pH1015))) ∧ ptTest pH1015 (runFrom pH1015 (fmask pH1015) (cmask pH1015) (hmask pH1015) 1 1014 (true, (init pH1015), (init pH1015))) 1015 508 true = true :=
  fin_run (runOK_init (prmOK_of_and H1015_fin) true) (by decide) rfl H1015_fin ptTest_fst
theorem I1015_fin : (prmOK pI1015 1015 && intTest pI1015 (runFrom pI1015 (fmask pI1015) (cmask pI1015) (hmask pI1015) 1 1014 (true, (init pI1015), (init pI1015))) 1015 18 false) = true := by
  decide +kernel
theorem I1015_ok : RunOK pI1015 1015 (runFrom pI1015 (fmask pI1015) (cmask pI1015) (hmask pI1015) 1 1014 (true, (init pI1015), (init pI1015))) ∧ intTest pI1015 (runFrom pI1015 (fmask pI1015) (cmask pI1015) (hmask pI1015) 1 1014 (true, (init pI1015), (init pI1015))) 1015 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1015_fin) true) (by decide) rfl I1015_fin intTest_fst
theorem link1015 : linkOK pL1015 pH1015 pI1015 = true := by decide +kernel
theorem cvx1015 : ConvexBetweenHumps 1015 :=
  cvx_of L1015_ok H1015_ok I1015_ok link1015 (by decide)

/-! ### `N = 1016` -/

def pL1016 : Prm := ⟨76, 36, 37, 1018, 11, 18446744073709551616, 170380368742319830, 170380368742319830⟩
def pH1016 : Prm := ⟨76, 36, 37, 1018, 11, 18446744073709551616, 170382567765575382, 170382567765575382⟩
def pI1016 : Prm := ⟨64, 32, 29, 1018, 11, 18446744073709551616, 170380368742319830, 170382567765575382⟩
theorem L1016_fin : (prmOK pL1016 1016 && ptTest pL1016 (runFrom pL1016 (fmask pL1016) (cmask pL1016) (hmask pL1016) 1 1015 (true, (init pL1016), (init pL1016))) 1016 508 false) = true := by
  decide +kernel
theorem L1016_ok : RunOK pL1016 1016 (runFrom pL1016 (fmask pL1016) (cmask pL1016) (hmask pL1016) 1 1015 (true, (init pL1016), (init pL1016))) ∧ ptTest pL1016 (runFrom pL1016 (fmask pL1016) (cmask pL1016) (hmask pL1016) 1 1015 (true, (init pL1016), (init pL1016))) 1016 508 false = true :=
  fin_run (runOK_init (prmOK_of_and L1016_fin) true) (by decide) rfl L1016_fin ptTest_fst
theorem H1016_fin : (prmOK pH1016 1016 && ptTest pH1016 (runFrom pH1016 (fmask pH1016) (cmask pH1016) (hmask pH1016) 1 1015 (true, (init pH1016), (init pH1016))) 1016 508 true) = true := by
  decide +kernel
theorem H1016_ok : RunOK pH1016 1016 (runFrom pH1016 (fmask pH1016) (cmask pH1016) (hmask pH1016) 1 1015 (true, (init pH1016), (init pH1016))) ∧ ptTest pH1016 (runFrom pH1016 (fmask pH1016) (cmask pH1016) (hmask pH1016) 1 1015 (true, (init pH1016), (init pH1016))) 1016 508 true = true :=
  fin_run (runOK_init (prmOK_of_and H1016_fin) true) (by decide) rfl H1016_fin ptTest_fst
theorem I1016_fin : (prmOK pI1016 1016 && intTest pI1016 (runFrom pI1016 (fmask pI1016) (cmask pI1016) (hmask pI1016) 1 1015 (true, (init pI1016), (init pI1016))) 1016 18 true) = true := by
  decide +kernel
theorem I1016_ok : RunOK pI1016 1016 (runFrom pI1016 (fmask pI1016) (cmask pI1016) (hmask pI1016) 1 1015 (true, (init pI1016), (init pI1016))) ∧ intTest pI1016 (runFrom pI1016 (fmask pI1016) (cmask pI1016) (hmask pI1016) 1 1015 (true, (init pI1016), (init pI1016))) 1016 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1016_fin) true) (by decide) rfl I1016_fin intTest_fst
theorem link1016 : linkOK pL1016 pH1016 pI1016 = true := by decide +kernel
theorem cvx1016 : ConvexBetweenHumps 1016 :=
  cvx_of L1016_ok H1016_ok I1016_ok link1016 (by decide)
theorem cenlink1016 : cenLinkOK pI1016 1016 = true := by decide +kernel
theorem cen1016 : CenterUniqueMin 1016 ∧ DipHyp 1016 ∧ OnePointHyps 1016 :=
  cen_of L1016_ok H1016_ok I1016_ok link1016 cenlink1016

/-! ### `N = 1017` -/

def pL1017 : Prm := ⟨76, 36, 37, 1019, 11, 18446744073709551616, 170246432919273928, 170246432919273928⟩
def pH1017 : Prm := ⟨76, 36, 37, 1019, 11, 18446744073709551616, 170248631942529480, 170248631942529480⟩
def pI1017 : Prm := ⟨64, 32, 29, 1019, 11, 18446744073709551616, 170246432919273928, 170248631942529480⟩
theorem L1017_fin : (prmOK pL1017 1017 && ptTest pL1017 (runFrom pL1017 (fmask pL1017) (cmask pL1017) (hmask pL1017) 1 1016 (true, (init pL1017), (init pL1017))) 1017 509 false) = true := by
  decide +kernel
theorem L1017_ok : RunOK pL1017 1017 (runFrom pL1017 (fmask pL1017) (cmask pL1017) (hmask pL1017) 1 1016 (true, (init pL1017), (init pL1017))) ∧ ptTest pL1017 (runFrom pL1017 (fmask pL1017) (cmask pL1017) (hmask pL1017) 1 1016 (true, (init pL1017), (init pL1017))) 1017 509 false = true :=
  fin_run (runOK_init (prmOK_of_and L1017_fin) true) (by decide) rfl L1017_fin ptTest_fst
theorem H1017_fin : (prmOK pH1017 1017 && ptTest pH1017 (runFrom pH1017 (fmask pH1017) (cmask pH1017) (hmask pH1017) 1 1016 (true, (init pH1017), (init pH1017))) 1017 509 true) = true := by
  decide +kernel
theorem H1017_ok : RunOK pH1017 1017 (runFrom pH1017 (fmask pH1017) (cmask pH1017) (hmask pH1017) 1 1016 (true, (init pH1017), (init pH1017))) ∧ ptTest pH1017 (runFrom pH1017 (fmask pH1017) (cmask pH1017) (hmask pH1017) 1 1016 (true, (init pH1017), (init pH1017))) 1017 509 true = true :=
  fin_run (runOK_init (prmOK_of_and H1017_fin) true) (by decide) rfl H1017_fin ptTest_fst
theorem I1017_fin : (prmOK pI1017 1017 && intTest pI1017 (runFrom pI1017 (fmask pI1017) (cmask pI1017) (hmask pI1017) 1 1016 (true, (init pI1017), (init pI1017))) 1017 18 false) = true := by
  decide +kernel
theorem I1017_ok : RunOK pI1017 1017 (runFrom pI1017 (fmask pI1017) (cmask pI1017) (hmask pI1017) 1 1016 (true, (init pI1017), (init pI1017))) ∧ intTest pI1017 (runFrom pI1017 (fmask pI1017) (cmask pI1017) (hmask pI1017) 1 1016 (true, (init pI1017), (init pI1017))) 1017 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1017_fin) true) (by decide) rfl I1017_fin intTest_fst
theorem link1017 : linkOK pL1017 pH1017 pI1017 = true := by decide +kernel
theorem cvx1017 : ConvexBetweenHumps 1017 :=
  cvx_of L1017_ok H1017_ok I1017_ok link1017 (by decide)

/-! ### `N = 1018` -/

def pL1018 : Prm := ⟨76, 36, 37, 1020, 11, 18446744073709551616, 170112836884423762, 170112836884423762⟩
def pH1018 : Prm := ⟨76, 36, 37, 1020, 11, 18446744073709551616, 170115035907679314, 170115035907679314⟩
def pI1018 : Prm := ⟨64, 32, 29, 1020, 11, 18446744073709551616, 170112836884423762, 170115035907679314⟩
theorem L1018_fin : (prmOK pL1018 1018 && ptTest pL1018 (runFrom pL1018 (fmask pL1018) (cmask pL1018) (hmask pL1018) 1 1017 (true, (init pL1018), (init pL1018))) 1018 509 false) = true := by
  decide +kernel
theorem L1018_ok : RunOK pL1018 1018 (runFrom pL1018 (fmask pL1018) (cmask pL1018) (hmask pL1018) 1 1017 (true, (init pL1018), (init pL1018))) ∧ ptTest pL1018 (runFrom pL1018 (fmask pL1018) (cmask pL1018) (hmask pL1018) 1 1017 (true, (init pL1018), (init pL1018))) 1018 509 false = true :=
  fin_run (runOK_init (prmOK_of_and L1018_fin) true) (by decide) rfl L1018_fin ptTest_fst
theorem H1018_fin : (prmOK pH1018 1018 && ptTest pH1018 (runFrom pH1018 (fmask pH1018) (cmask pH1018) (hmask pH1018) 1 1017 (true, (init pH1018), (init pH1018))) 1018 509 true) = true := by
  decide +kernel
theorem H1018_ok : RunOK pH1018 1018 (runFrom pH1018 (fmask pH1018) (cmask pH1018) (hmask pH1018) 1 1017 (true, (init pH1018), (init pH1018))) ∧ ptTest pH1018 (runFrom pH1018 (fmask pH1018) (cmask pH1018) (hmask pH1018) 1 1017 (true, (init pH1018), (init pH1018))) 1018 509 true = true :=
  fin_run (runOK_init (prmOK_of_and H1018_fin) true) (by decide) rfl H1018_fin ptTest_fst
theorem I1018_fin : (prmOK pI1018 1018 && intTest pI1018 (runFrom pI1018 (fmask pI1018) (cmask pI1018) (hmask pI1018) 1 1017 (true, (init pI1018), (init pI1018))) 1018 18 true) = true := by
  decide +kernel
theorem I1018_ok : RunOK pI1018 1018 (runFrom pI1018 (fmask pI1018) (cmask pI1018) (hmask pI1018) 1 1017 (true, (init pI1018), (init pI1018))) ∧ intTest pI1018 (runFrom pI1018 (fmask pI1018) (cmask pI1018) (hmask pI1018) 1 1017 (true, (init pI1018), (init pI1018))) 1018 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1018_fin) true) (by decide) rfl I1018_fin intTest_fst
theorem link1018 : linkOK pL1018 pH1018 pI1018 = true := by decide +kernel
theorem cvx1018 : ConvexBetweenHumps 1018 :=
  cvx_of L1018_ok H1018_ok I1018_ok link1018 (by decide)
theorem cenlink1018 : cenLinkOK pI1018 1018 = true := by decide +kernel
theorem cen1018 : CenterUniqueMin 1018 ∧ DipHyp 1018 ∧ OnePointHyps 1018 :=
  cen_of L1018_ok H1018_ok I1018_ok link1018 cenlink1018

/-! ### `N = 1019` -/

def pL1019 : Prm := ⟨76, 36, 37, 1021, 11, 18446744073709551616, 169979360772557794, 169979360772557794⟩
def pH1019 : Prm := ⟨76, 36, 37, 1021, 11, 18446744073709551616, 169981559795813346, 169981559795813346⟩
def pI1019 : Prm := ⟨64, 32, 29, 1021, 11, 18446744073709551616, 169979360772557794, 169981559795813346⟩
theorem L1019_fin : (prmOK pL1019 1019 && ptTest pL1019 (runFrom pL1019 (fmask pL1019) (cmask pL1019) (hmask pL1019) 1 1018 (true, (init pL1019), (init pL1019))) 1019 510 false) = true := by
  decide +kernel
theorem L1019_ok : RunOK pL1019 1019 (runFrom pL1019 (fmask pL1019) (cmask pL1019) (hmask pL1019) 1 1018 (true, (init pL1019), (init pL1019))) ∧ ptTest pL1019 (runFrom pL1019 (fmask pL1019) (cmask pL1019) (hmask pL1019) 1 1018 (true, (init pL1019), (init pL1019))) 1019 510 false = true :=
  fin_run (runOK_init (prmOK_of_and L1019_fin) true) (by decide) rfl L1019_fin ptTest_fst
theorem H1019_fin : (prmOK pH1019 1019 && ptTest pH1019 (runFrom pH1019 (fmask pH1019) (cmask pH1019) (hmask pH1019) 1 1018 (true, (init pH1019), (init pH1019))) 1019 510 true) = true := by
  decide +kernel
theorem H1019_ok : RunOK pH1019 1019 (runFrom pH1019 (fmask pH1019) (cmask pH1019) (hmask pH1019) 1 1018 (true, (init pH1019), (init pH1019))) ∧ ptTest pH1019 (runFrom pH1019 (fmask pH1019) (cmask pH1019) (hmask pH1019) 1 1018 (true, (init pH1019), (init pH1019))) 1019 510 true = true :=
  fin_run (runOK_init (prmOK_of_and H1019_fin) true) (by decide) rfl H1019_fin ptTest_fst
theorem I1019_fin : (prmOK pI1019 1019 && intTest pI1019 (runFrom pI1019 (fmask pI1019) (cmask pI1019) (hmask pI1019) 1 1018 (true, (init pI1019), (init pI1019))) 1019 18 false) = true := by
  decide +kernel
theorem I1019_ok : RunOK pI1019 1019 (runFrom pI1019 (fmask pI1019) (cmask pI1019) (hmask pI1019) 1 1018 (true, (init pI1019), (init pI1019))) ∧ intTest pI1019 (runFrom pI1019 (fmask pI1019) (cmask pI1019) (hmask pI1019) 1 1018 (true, (init pI1019), (init pI1019))) 1019 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1019_fin) true) (by decide) rfl I1019_fin intTest_fst
theorem link1019 : linkOK pL1019 pH1019 pI1019 = true := by decide +kernel
theorem cvx1019 : ConvexBetweenHumps 1019 :=
  cvx_of L1019_ok H1019_ok I1019_ok link1019 (by decide)

/-! ### `N = 1020` -/

def pL1020 : Prm := ⟨76, 36, 37, 1022, 11, 18446744073709551616, 169846222569293467, 169846222569293467⟩
def pH1020 : Prm := ⟨76, 36, 37, 1022, 11, 18446744073709551616, 169848421592549019, 169848421592549019⟩
def pI1020 : Prm := ⟨64, 32, 29, 1022, 11, 18446744073709551616, 169846222569293467, 169848421592549019⟩
theorem L1020_fin : (prmOK pL1020 1020 && ptTest pL1020 (runFrom pL1020 (fmask pL1020) (cmask pL1020) (hmask pL1020) 1 1019 (true, (init pL1020), (init pL1020))) 1020 510 false) = true := by
  decide +kernel
theorem L1020_ok : RunOK pL1020 1020 (runFrom pL1020 (fmask pL1020) (cmask pL1020) (hmask pL1020) 1 1019 (true, (init pL1020), (init pL1020))) ∧ ptTest pL1020 (runFrom pL1020 (fmask pL1020) (cmask pL1020) (hmask pL1020) 1 1019 (true, (init pL1020), (init pL1020))) 1020 510 false = true :=
  fin_run (runOK_init (prmOK_of_and L1020_fin) true) (by decide) rfl L1020_fin ptTest_fst
theorem H1020_fin : (prmOK pH1020 1020 && ptTest pH1020 (runFrom pH1020 (fmask pH1020) (cmask pH1020) (hmask pH1020) 1 1019 (true, (init pH1020), (init pH1020))) 1020 510 true) = true := by
  decide +kernel
theorem H1020_ok : RunOK pH1020 1020 (runFrom pH1020 (fmask pH1020) (cmask pH1020) (hmask pH1020) 1 1019 (true, (init pH1020), (init pH1020))) ∧ ptTest pH1020 (runFrom pH1020 (fmask pH1020) (cmask pH1020) (hmask pH1020) 1 1019 (true, (init pH1020), (init pH1020))) 1020 510 true = true :=
  fin_run (runOK_init (prmOK_of_and H1020_fin) true) (by decide) rfl H1020_fin ptTest_fst
theorem I1020_fin : (prmOK pI1020 1020 && intTest pI1020 (runFrom pI1020 (fmask pI1020) (cmask pI1020) (hmask pI1020) 1 1019 (true, (init pI1020), (init pI1020))) 1020 18 true) = true := by
  decide +kernel
theorem I1020_ok : RunOK pI1020 1020 (runFrom pI1020 (fmask pI1020) (cmask pI1020) (hmask pI1020) 1 1019 (true, (init pI1020), (init pI1020))) ∧ intTest pI1020 (runFrom pI1020 (fmask pI1020) (cmask pI1020) (hmask pI1020) 1 1019 (true, (init pI1020), (init pI1020))) 1020 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1020_fin) true) (by decide) rfl I1020_fin intTest_fst
theorem link1020 : linkOK pL1020 pH1020 pI1020 = true := by decide +kernel
theorem cvx1020 : ConvexBetweenHumps 1020 :=
  cvx_of L1020_ok H1020_ok I1020_ok link1020 (by decide)
theorem cenlink1020 : cenLinkOK pI1020 1020 = true := by decide +kernel
theorem cen1020 : CenterUniqueMin 1020 ∧ DipHyp 1020 ∧ OnePointHyps 1020 :=
  cen_of L1020_ok H1020_ok I1020_ok link1020 cenlink1020

/-! ### `N = 1021` -/

def pL1021 : Prm := ⟨76, 36, 37, 1023, 11, 18446744073709551616, 169713203724672098, 169713203724672098⟩
def pH1021 : Prm := ⟨77, 37, 37, 1023, 11, 18446744073709551616, 169715402747927650, 169715402747927650⟩
def pI1021 : Prm := ⟨64, 32, 29, 1023, 11, 18446744073709551616, 169713203724672098, 169715402747927650⟩
theorem L1021_fin : (prmOK pL1021 1021 && ptTest pL1021 (runFrom pL1021 (fmask pL1021) (cmask pL1021) (hmask pL1021) 1 1020 (true, (init pL1021), (init pL1021))) 1021 511 false) = true := by
  decide +kernel
theorem L1021_ok : RunOK pL1021 1021 (runFrom pL1021 (fmask pL1021) (cmask pL1021) (hmask pL1021) 1 1020 (true, (init pL1021), (init pL1021))) ∧ ptTest pL1021 (runFrom pL1021 (fmask pL1021) (cmask pL1021) (hmask pL1021) 1 1020 (true, (init pL1021), (init pL1021))) 1021 511 false = true :=
  fin_run (runOK_init (prmOK_of_and L1021_fin) true) (by decide) rfl L1021_fin ptTest_fst
theorem H1021_fin : (prmOK pH1021 1021 && ptTest pH1021 (runFrom pH1021 (fmask pH1021) (cmask pH1021) (hmask pH1021) 1 1020 (true, (init pH1021), (init pH1021))) 1021 511 true) = true := by
  decide +kernel
theorem H1021_ok : RunOK pH1021 1021 (runFrom pH1021 (fmask pH1021) (cmask pH1021) (hmask pH1021) 1 1020 (true, (init pH1021), (init pH1021))) ∧ ptTest pH1021 (runFrom pH1021 (fmask pH1021) (cmask pH1021) (hmask pH1021) 1 1020 (true, (init pH1021), (init pH1021))) 1021 511 true = true :=
  fin_run (runOK_init (prmOK_of_and H1021_fin) true) (by decide) rfl H1021_fin ptTest_fst
theorem I1021_fin : (prmOK pI1021 1021 && intTest pI1021 (runFrom pI1021 (fmask pI1021) (cmask pI1021) (hmask pI1021) 1 1020 (true, (init pI1021), (init pI1021))) 1021 18 false) = true := by
  decide +kernel
theorem I1021_ok : RunOK pI1021 1021 (runFrom pI1021 (fmask pI1021) (cmask pI1021) (hmask pI1021) 1 1020 (true, (init pI1021), (init pI1021))) ∧ intTest pI1021 (runFrom pI1021 (fmask pI1021) (cmask pI1021) (hmask pI1021) 1 1020 (true, (init pI1021), (init pI1021))) 1021 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1021_fin) true) (by decide) rfl I1021_fin intTest_fst
theorem link1021 : linkOK pL1021 pH1021 pI1021 = true := by decide +kernel
theorem cvx1021 : ConvexBetweenHumps 1021 :=
  cvx_of L1021_ok H1021_ok I1021_ok link1021 (by decide)

/-! ### `N = 1022` -/

def pL1022 : Prm := ⟨76, 36, 37, 1024, 11, 18446744073709551616, 169580520923040908, 169580520923040908⟩
def pH1022 : Prm := ⟨76, 36, 37, 1024, 11, 18446744073709551616, 169582719946296460, 169582719946296460⟩
def pI1022 : Prm := ⟨64, 32, 29, 1024, 11, 18446744073709551616, 169580520923040908, 169582719946296460⟩
theorem L1022_fin : (prmOK pL1022 1022 && ptTest pL1022 (runFrom pL1022 (fmask pL1022) (cmask pL1022) (hmask pL1022) 1 1021 (true, (init pL1022), (init pL1022))) 1022 511 false) = true := by
  decide +kernel
theorem L1022_ok : RunOK pL1022 1022 (runFrom pL1022 (fmask pL1022) (cmask pL1022) (hmask pL1022) 1 1021 (true, (init pL1022), (init pL1022))) ∧ ptTest pL1022 (runFrom pL1022 (fmask pL1022) (cmask pL1022) (hmask pL1022) 1 1021 (true, (init pL1022), (init pL1022))) 1022 511 false = true :=
  fin_run (runOK_init (prmOK_of_and L1022_fin) true) (by decide) rfl L1022_fin ptTest_fst
theorem H1022_fin : (prmOK pH1022 1022 && ptTest pH1022 (runFrom pH1022 (fmask pH1022) (cmask pH1022) (hmask pH1022) 1 1021 (true, (init pH1022), (init pH1022))) 1022 511 true) = true := by
  decide +kernel
theorem H1022_ok : RunOK pH1022 1022 (runFrom pH1022 (fmask pH1022) (cmask pH1022) (hmask pH1022) 1 1021 (true, (init pH1022), (init pH1022))) ∧ ptTest pH1022 (runFrom pH1022 (fmask pH1022) (cmask pH1022) (hmask pH1022) 1 1021 (true, (init pH1022), (init pH1022))) 1022 511 true = true :=
  fin_run (runOK_init (prmOK_of_and H1022_fin) true) (by decide) rfl H1022_fin ptTest_fst
theorem I1022_fin : (prmOK pI1022 1022 && intTest pI1022 (runFrom pI1022 (fmask pI1022) (cmask pI1022) (hmask pI1022) 1 1021 (true, (init pI1022), (init pI1022))) 1022 18 true) = true := by
  decide +kernel
theorem I1022_ok : RunOK pI1022 1022 (runFrom pI1022 (fmask pI1022) (cmask pI1022) (hmask pI1022) 1 1021 (true, (init pI1022), (init pI1022))) ∧ intTest pI1022 (runFrom pI1022 (fmask pI1022) (cmask pI1022) (hmask pI1022) 1 1021 (true, (init pI1022), (init pI1022))) 1022 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1022_fin) true) (by decide) rfl I1022_fin intTest_fst
theorem link1022 : linkOK pL1022 pH1022 pI1022 = true := by decide +kernel
theorem cvx1022 : ConvexBetweenHumps 1022 :=
  cvx_of L1022_ok H1022_ok I1022_ok link1022 (by decide)
theorem cenlink1022 : cenLinkOK pI1022 1022 = true := by decide +kernel
theorem cen1022 : CenterUniqueMin 1022 ∧ DipHyp 1022 ∧ OnePointHyps 1022 :=
  cen_of L1022_ok H1022_ok I1022_ok link1022 cenlink1022

/-! ### `N = 1023` -/

def pL1023 : Prm := ⟨76, 36, 37, 1025, 11, 18446744073709551616, 169447956919290102, 169447956919290102⟩
def pH1023 : Prm := ⟨76, 36, 37, 1025, 11, 18446744073709551616, 169450155942545654, 169450155942545654⟩
def pI1023 : Prm := ⟨64, 32, 29, 1025, 11, 18446744073709551616, 169447956919290102, 169450155942545654⟩
theorem L1023_fin : (prmOK pL1023 1023 && ptTest pL1023 (runFrom pL1023 (fmask pL1023) (cmask pL1023) (hmask pL1023) 1 1022 (true, (init pL1023), (init pL1023))) 1023 512 false) = true := by
  decide +kernel
theorem L1023_ok : RunOK pL1023 1023 (runFrom pL1023 (fmask pL1023) (cmask pL1023) (hmask pL1023) 1 1022 (true, (init pL1023), (init pL1023))) ∧ ptTest pL1023 (runFrom pL1023 (fmask pL1023) (cmask pL1023) (hmask pL1023) 1 1022 (true, (init pL1023), (init pL1023))) 1023 512 false = true :=
  fin_run (runOK_init (prmOK_of_and L1023_fin) true) (by decide) rfl L1023_fin ptTest_fst
theorem H1023_fin : (prmOK pH1023 1023 && ptTest pH1023 (runFrom pH1023 (fmask pH1023) (cmask pH1023) (hmask pH1023) 1 1022 (true, (init pH1023), (init pH1023))) 1023 512 true) = true := by
  decide +kernel
theorem H1023_ok : RunOK pH1023 1023 (runFrom pH1023 (fmask pH1023) (cmask pH1023) (hmask pH1023) 1 1022 (true, (init pH1023), (init pH1023))) ∧ ptTest pH1023 (runFrom pH1023 (fmask pH1023) (cmask pH1023) (hmask pH1023) 1 1022 (true, (init pH1023), (init pH1023))) 1023 512 true = true :=
  fin_run (runOK_init (prmOK_of_and H1023_fin) true) (by decide) rfl H1023_fin ptTest_fst
theorem I1023_fin : (prmOK pI1023 1023 && intTest pI1023 (runFrom pI1023 (fmask pI1023) (cmask pI1023) (hmask pI1023) 1 1022 (true, (init pI1023), (init pI1023))) 1023 18 false) = true := by
  decide +kernel
theorem I1023_ok : RunOK pI1023 1023 (runFrom pI1023 (fmask pI1023) (cmask pI1023) (hmask pI1023) 1 1022 (true, (init pI1023), (init pI1023))) ∧ intTest pI1023 (runFrom pI1023 (fmask pI1023) (cmask pI1023) (hmask pI1023) 1 1022 (true, (init pI1023), (init pI1023))) 1023 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1023_fin) true) (by decide) rfl I1023_fin intTest_fst
theorem link1023 : linkOK pL1023 pH1023 pI1023 = true := by decide +kernel
theorem cvx1023 : ConvexBetweenHumps 1023 :=
  cvx_of L1023_ok H1023_ok I1023_ok link1023 (by decide)

/-! ### `N = 1024` -/

def pL1024 : Prm := ⟨77, 37, 37, 1026, 11, 18446744073709551616, 169315727106863752, 169315727106863752⟩
def pH1024 : Prm := ⟨76, 36, 37, 1026, 11, 18446744073709551616, 169317926130119304, 169317926130119304⟩
def pI1024 : Prm := ⟨64, 32, 29, 1026, 11, 18446744073709551616, 169315727106863752, 169317926130119304⟩
theorem L1024_fin : (prmOK pL1024 1024 && ptTest pL1024 (runFrom pL1024 (fmask pL1024) (cmask pL1024) (hmask pL1024) 1 1023 (true, (init pL1024), (init pL1024))) 1024 512 false) = true := by
  decide +kernel
theorem L1024_ok : RunOK pL1024 1024 (runFrom pL1024 (fmask pL1024) (cmask pL1024) (hmask pL1024) 1 1023 (true, (init pL1024), (init pL1024))) ∧ ptTest pL1024 (runFrom pL1024 (fmask pL1024) (cmask pL1024) (hmask pL1024) 1 1023 (true, (init pL1024), (init pL1024))) 1024 512 false = true :=
  fin_run (runOK_init (prmOK_of_and L1024_fin) true) (by decide) rfl L1024_fin ptTest_fst
theorem H1024_fin : (prmOK pH1024 1024 && ptTest pH1024 (runFrom pH1024 (fmask pH1024) (cmask pH1024) (hmask pH1024) 1 1023 (true, (init pH1024), (init pH1024))) 1024 512 true) = true := by
  decide +kernel
theorem H1024_ok : RunOK pH1024 1024 (runFrom pH1024 (fmask pH1024) (cmask pH1024) (hmask pH1024) 1 1023 (true, (init pH1024), (init pH1024))) ∧ ptTest pH1024 (runFrom pH1024 (fmask pH1024) (cmask pH1024) (hmask pH1024) 1 1023 (true, (init pH1024), (init pH1024))) 1024 512 true = true :=
  fin_run (runOK_init (prmOK_of_and H1024_fin) true) (by decide) rfl H1024_fin ptTest_fst
theorem I1024_fin : (prmOK pI1024 1024 && intTest pI1024 (runFrom pI1024 (fmask pI1024) (cmask pI1024) (hmask pI1024) 1 1023 (true, (init pI1024), (init pI1024))) 1024 18 true) = true := by
  decide +kernel
theorem I1024_ok : RunOK pI1024 1024 (runFrom pI1024 (fmask pI1024) (cmask pI1024) (hmask pI1024) 1 1023 (true, (init pI1024), (init pI1024))) ∧ intTest pI1024 (runFrom pI1024 (fmask pI1024) (cmask pI1024) (hmask pI1024) 1 1023 (true, (init pI1024), (init pI1024))) 1024 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1024_fin) true) (by decide) rfl I1024_fin intTest_fst
theorem link1024 : linkOK pL1024 pH1024 pI1024 = true := by decide +kernel
theorem cvx1024 : ConvexBetweenHumps 1024 :=
  cvx_of L1024_ok H1024_ok I1024_ok link1024 (by decide)
theorem cenlink1024 : cenLinkOK pI1024 1024 = true := by decide +kernel
theorem cen1024 : CenterUniqueMin 1024 ∧ DipHyp 1024 ∧ OnePointHyps 1024 :=
  cen_of L1024_ok H1024_ok I1024_ok link1024 cenlink1024

/-! ### `N = 1025` -/

def pL1025 : Prm := ⟨76, 36, 37, 1027, 11, 18446744073709551616, 169183615535133881, 169183615535133881⟩
def pH1025 : Prm := ⟨77, 37, 37, 1027, 11, 18446744073709551616, 169185814558389433, 169185814558389433⟩
def pI1025 : Prm := ⟨64, 32, 29, 1027, 11, 18446744073709551616, 169183615535133881, 169185814558389433⟩
theorem L1025_fin : (prmOK pL1025 1025 && ptTest pL1025 (runFrom pL1025 (fmask pL1025) (cmask pL1025) (hmask pL1025) 1 1024 (true, (init pL1025), (init pL1025))) 1025 513 false) = true := by
  decide +kernel
theorem L1025_ok : RunOK pL1025 1025 (runFrom pL1025 (fmask pL1025) (cmask pL1025) (hmask pL1025) 1 1024 (true, (init pL1025), (init pL1025))) ∧ ptTest pL1025 (runFrom pL1025 (fmask pL1025) (cmask pL1025) (hmask pL1025) 1 1024 (true, (init pL1025), (init pL1025))) 1025 513 false = true :=
  fin_run (runOK_init (prmOK_of_and L1025_fin) true) (by decide) rfl L1025_fin ptTest_fst
theorem H1025_fin : (prmOK pH1025 1025 && ptTest pH1025 (runFrom pH1025 (fmask pH1025) (cmask pH1025) (hmask pH1025) 1 1024 (true, (init pH1025), (init pH1025))) 1025 513 true) = true := by
  decide +kernel
theorem H1025_ok : RunOK pH1025 1025 (runFrom pH1025 (fmask pH1025) (cmask pH1025) (hmask pH1025) 1 1024 (true, (init pH1025), (init pH1025))) ∧ ptTest pH1025 (runFrom pH1025 (fmask pH1025) (cmask pH1025) (hmask pH1025) 1 1024 (true, (init pH1025), (init pH1025))) 1025 513 true = true :=
  fin_run (runOK_init (prmOK_of_and H1025_fin) true) (by decide) rfl H1025_fin ptTest_fst
theorem I1025_fin : (prmOK pI1025 1025 && intTest pI1025 (runFrom pI1025 (fmask pI1025) (cmask pI1025) (hmask pI1025) 1 1024 (true, (init pI1025), (init pI1025))) 1025 18 false) = true := by
  decide +kernel
theorem I1025_ok : RunOK pI1025 1025 (runFrom pI1025 (fmask pI1025) (cmask pI1025) (hmask pI1025) 1 1024 (true, (init pI1025), (init pI1025))) ∧ intTest pI1025 (runFrom pI1025 (fmask pI1025) (cmask pI1025) (hmask pI1025) 1 1024 (true, (init pI1025), (init pI1025))) 1025 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1025_fin) true) (by decide) rfl I1025_fin intTest_fst
theorem link1025 : linkOK pL1025 pH1025 pI1025 = true := by decide +kernel
theorem cvx1025 : ConvexBetweenHumps 1025 :=
  cvx_of L1025_ok H1025_ok I1025_ok link1025 (by decide)

/-! ### `N = 1026` -/

def pL1026 : Prm := ⟨77, 37, 37, 1028, 11, 18446744073709551616, 169051836316750227, 169051836316750227⟩
def pH1026 : Prm := ⟨76, 36, 37, 1028, 11, 18446744073709551616, 169054035340005779, 169054035340005779⟩
def pI1026 : Prm := ⟨64, 32, 29, 1028, 11, 18446744073709551616, 169051836316750227, 169054035340005779⟩
theorem L1026_fin : (prmOK pL1026 1026 && ptTest pL1026 (runFrom pL1026 (fmask pL1026) (cmask pL1026) (hmask pL1026) 1 1025 (true, (init pL1026), (init pL1026))) 1026 513 false) = true := by
  decide +kernel
theorem L1026_ok : RunOK pL1026 1026 (runFrom pL1026 (fmask pL1026) (cmask pL1026) (hmask pL1026) 1 1025 (true, (init pL1026), (init pL1026))) ∧ ptTest pL1026 (runFrom pL1026 (fmask pL1026) (cmask pL1026) (hmask pL1026) 1 1025 (true, (init pL1026), (init pL1026))) 1026 513 false = true :=
  fin_run (runOK_init (prmOK_of_and L1026_fin) true) (by decide) rfl L1026_fin ptTest_fst
theorem H1026_fin : (prmOK pH1026 1026 && ptTest pH1026 (runFrom pH1026 (fmask pH1026) (cmask pH1026) (hmask pH1026) 1 1025 (true, (init pH1026), (init pH1026))) 1026 513 true) = true := by
  decide +kernel
theorem H1026_ok : RunOK pH1026 1026 (runFrom pH1026 (fmask pH1026) (cmask pH1026) (hmask pH1026) 1 1025 (true, (init pH1026), (init pH1026))) ∧ ptTest pH1026 (runFrom pH1026 (fmask pH1026) (cmask pH1026) (hmask pH1026) 1 1025 (true, (init pH1026), (init pH1026))) 1026 513 true = true :=
  fin_run (runOK_init (prmOK_of_and H1026_fin) true) (by decide) rfl H1026_fin ptTest_fst
theorem I1026_fin : (prmOK pI1026 1026 && intTest pI1026 (runFrom pI1026 (fmask pI1026) (cmask pI1026) (hmask pI1026) 1 1025 (true, (init pI1026), (init pI1026))) 1026 18 true) = true := by
  decide +kernel
theorem I1026_ok : RunOK pI1026 1026 (runFrom pI1026 (fmask pI1026) (cmask pI1026) (hmask pI1026) 1 1025 (true, (init pI1026), (init pI1026))) ∧ intTest pI1026 (runFrom pI1026 (fmask pI1026) (cmask pI1026) (hmask pI1026) 1 1025 (true, (init pI1026), (init pI1026))) 1026 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1026_fin) true) (by decide) rfl I1026_fin intTest_fst
theorem link1026 : linkOK pL1026 pH1026 pI1026 = true := by decide +kernel
theorem cvx1026 : ConvexBetweenHumps 1026 :=
  cvx_of L1026_ok H1026_ok I1026_ok link1026 (by decide)
theorem cenlink1026 : cenLinkOK pI1026 1026 = true := by decide +kernel
theorem cen1026 : CenterUniqueMin 1026 ∧ DipHyp 1026 ∧ OnePointHyps 1026 :=
  cen_of L1026_ok H1026_ok I1026_ok link1026 cenlink1026

/-! ### `N = 1027` -/

def pL1027 : Prm := ⟨76, 36, 37, 1029, 11, 18446744073709551616, 168920174785420922, 168920174785420922⟩
def pH1027 : Prm := ⟨76, 36, 37, 1029, 11, 18446744073709551616, 168922373808676474, 168922373808676474⟩
def pI1027 : Prm := ⟨64, 32, 29, 1029, 11, 18446744073709551616, 168920174785420922, 168922373808676474⟩
theorem L1027_fin : (prmOK pL1027 1027 && ptTest pL1027 (runFrom pL1027 (fmask pL1027) (cmask pL1027) (hmask pL1027) 1 1026 (true, (init pL1027), (init pL1027))) 1027 514 false) = true := by
  decide +kernel
theorem L1027_ok : RunOK pL1027 1027 (runFrom pL1027 (fmask pL1027) (cmask pL1027) (hmask pL1027) 1 1026 (true, (init pL1027), (init pL1027))) ∧ ptTest pL1027 (runFrom pL1027 (fmask pL1027) (cmask pL1027) (hmask pL1027) 1 1026 (true, (init pL1027), (init pL1027))) 1027 514 false = true :=
  fin_run (runOK_init (prmOK_of_and L1027_fin) true) (by decide) rfl L1027_fin ptTest_fst
theorem H1027_fin : (prmOK pH1027 1027 && ptTest pH1027 (runFrom pH1027 (fmask pH1027) (cmask pH1027) (hmask pH1027) 1 1026 (true, (init pH1027), (init pH1027))) 1027 514 true) = true := by
  decide +kernel
theorem H1027_ok : RunOK pH1027 1027 (runFrom pH1027 (fmask pH1027) (cmask pH1027) (hmask pH1027) 1 1026 (true, (init pH1027), (init pH1027))) ∧ ptTest pH1027 (runFrom pH1027 (fmask pH1027) (cmask pH1027) (hmask pH1027) 1 1026 (true, (init pH1027), (init pH1027))) 1027 514 true = true :=
  fin_run (runOK_init (prmOK_of_and H1027_fin) true) (by decide) rfl H1027_fin ptTest_fst
theorem I1027_fin : (prmOK pI1027 1027 && intTest pI1027 (runFrom pI1027 (fmask pI1027) (cmask pI1027) (hmask pI1027) 1 1026 (true, (init pI1027), (init pI1027))) 1027 18 false) = true := by
  decide +kernel
theorem I1027_ok : RunOK pI1027 1027 (runFrom pI1027 (fmask pI1027) (cmask pI1027) (hmask pI1027) 1 1026 (true, (init pI1027), (init pI1027))) ∧ intTest pI1027 (runFrom pI1027 (fmask pI1027) (cmask pI1027) (hmask pI1027) 1 1026 (true, (init pI1027), (init pI1027))) 1027 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1027_fin) true) (by decide) rfl I1027_fin intTest_fst
theorem link1027 : linkOK pL1027 pH1027 pI1027 = true := by decide +kernel
theorem cvx1027 : ConvexBetweenHumps 1027 :=
  cvx_of L1027_ok H1027_ok I1027_ok link1027 (by decide)

/-! ### `N = 1028` -/

def pL1028 : Prm := ⟨77, 37, 37, 1030, 11, 18446744073709551616, 168788843783165526, 168788843783165526⟩
def pH1028 : Prm := ⟨77, 37, 37, 1030, 11, 18446744073709551616, 168791042806421078, 168791042806421078⟩
def pI1028 : Prm := ⟨64, 32, 29, 1030, 11, 18446744073709551616, 168788843783165526, 168791042806421078⟩
theorem L1028_fin : (prmOK pL1028 1028 && ptTest pL1028 (runFrom pL1028 (fmask pL1028) (cmask pL1028) (hmask pL1028) 1 1027 (true, (init pL1028), (init pL1028))) 1028 514 false) = true := by
  decide +kernel
theorem L1028_ok : RunOK pL1028 1028 (runFrom pL1028 (fmask pL1028) (cmask pL1028) (hmask pL1028) 1 1027 (true, (init pL1028), (init pL1028))) ∧ ptTest pL1028 (runFrom pL1028 (fmask pL1028) (cmask pL1028) (hmask pL1028) 1 1027 (true, (init pL1028), (init pL1028))) 1028 514 false = true :=
  fin_run (runOK_init (prmOK_of_and L1028_fin) true) (by decide) rfl L1028_fin ptTest_fst
theorem H1028_fin : (prmOK pH1028 1028 && ptTest pH1028 (runFrom pH1028 (fmask pH1028) (cmask pH1028) (hmask pH1028) 1 1027 (true, (init pH1028), (init pH1028))) 1028 514 true) = true := by
  decide +kernel
theorem H1028_ok : RunOK pH1028 1028 (runFrom pH1028 (fmask pH1028) (cmask pH1028) (hmask pH1028) 1 1027 (true, (init pH1028), (init pH1028))) ∧ ptTest pH1028 (runFrom pH1028 (fmask pH1028) (cmask pH1028) (hmask pH1028) 1 1027 (true, (init pH1028), (init pH1028))) 1028 514 true = true :=
  fin_run (runOK_init (prmOK_of_and H1028_fin) true) (by decide) rfl H1028_fin ptTest_fst
theorem I1028_fin : (prmOK pI1028 1028 && intTest pI1028 (runFrom pI1028 (fmask pI1028) (cmask pI1028) (hmask pI1028) 1 1027 (true, (init pI1028), (init pI1028))) 1028 18 true) = true := by
  decide +kernel
theorem I1028_ok : RunOK pI1028 1028 (runFrom pI1028 (fmask pI1028) (cmask pI1028) (hmask pI1028) 1 1027 (true, (init pI1028), (init pI1028))) ∧ intTest pI1028 (runFrom pI1028 (fmask pI1028) (cmask pI1028) (hmask pI1028) 1 1027 (true, (init pI1028), (init pI1028))) 1028 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1028_fin) true) (by decide) rfl I1028_fin intTest_fst
theorem link1028 : linkOK pL1028 pH1028 pI1028 = true := by decide +kernel
theorem cvx1028 : ConvexBetweenHumps 1028 :=
  cvx_of L1028_ok H1028_ok I1028_ok link1028 (by decide)
theorem cenlink1028 : cenLinkOK pI1028 1028 = true := by decide +kernel
theorem cen1028 : CenterUniqueMin 1028 ∧ DipHyp 1028 ∧ OnePointHyps 1028 :=
  cen_of L1028_ok H1028_ok I1028_ok link1028 cenlink1028

/-! ### `N = 1029` -/

def pL1029 : Prm := ⟨77, 37, 37, 1031, 11, 18446744073709551616, 168657629917771890, 168657629917771890⟩
def pH1029 : Prm := ⟨77, 37, 37, 1031, 11, 18446744073709551616, 168659828941027442, 168659828941027442⟩
def pI1029 : Prm := ⟨64, 32, 29, 1031, 11, 18446744073709551616, 168657629917771890, 168659828941027442⟩
theorem L1029_fin : (prmOK pL1029 1029 && ptTest pL1029 (runFrom pL1029 (fmask pL1029) (cmask pL1029) (hmask pL1029) 1 1028 (true, (init pL1029), (init pL1029))) 1029 515 false) = true := by
  decide +kernel
theorem L1029_ok : RunOK pL1029 1029 (runFrom pL1029 (fmask pL1029) (cmask pL1029) (hmask pL1029) 1 1028 (true, (init pL1029), (init pL1029))) ∧ ptTest pL1029 (runFrom pL1029 (fmask pL1029) (cmask pL1029) (hmask pL1029) 1 1028 (true, (init pL1029), (init pL1029))) 1029 515 false = true :=
  fin_run (runOK_init (prmOK_of_and L1029_fin) true) (by decide) rfl L1029_fin ptTest_fst
theorem H1029_fin : (prmOK pH1029 1029 && ptTest pH1029 (runFrom pH1029 (fmask pH1029) (cmask pH1029) (hmask pH1029) 1 1028 (true, (init pH1029), (init pH1029))) 1029 515 true) = true := by
  decide +kernel
theorem H1029_ok : RunOK pH1029 1029 (runFrom pH1029 (fmask pH1029) (cmask pH1029) (hmask pH1029) 1 1028 (true, (init pH1029), (init pH1029))) ∧ ptTest pH1029 (runFrom pH1029 (fmask pH1029) (cmask pH1029) (hmask pH1029) 1 1028 (true, (init pH1029), (init pH1029))) 1029 515 true = true :=
  fin_run (runOK_init (prmOK_of_and H1029_fin) true) (by decide) rfl H1029_fin ptTest_fst
theorem I1029_fin : (prmOK pI1029 1029 && intTest pI1029 (runFrom pI1029 (fmask pI1029) (cmask pI1029) (hmask pI1029) 1 1028 (true, (init pI1029), (init pI1029))) 1029 18 false) = true := by
  decide +kernel
theorem I1029_ok : RunOK pI1029 1029 (runFrom pI1029 (fmask pI1029) (cmask pI1029) (hmask pI1029) 1 1028 (true, (init pI1029), (init pI1029))) ∧ intTest pI1029 (runFrom pI1029 (fmask pI1029) (cmask pI1029) (hmask pI1029) 1 1028 (true, (init pI1029), (init pI1029))) 1029 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1029_fin) true) (by decide) rfl I1029_fin intTest_fst
theorem link1029 : linkOK pL1029 pH1029 pI1029 = true := by decide +kernel
theorem cvx1029 : ConvexBetweenHumps 1029 :=
  cvx_of L1029_ok H1029_ok I1029_ok link1029 (by decide)

/-! ### `N = 1030` -/

def pL1030 : Prm := ⟨76, 36, 37, 1032, 11, 18446744073709551616, 168526744770645977, 168526744770645977⟩
def pH1030 : Prm := ⟨77, 37, 37, 1032, 11, 18446744073709551616, 168528943793901529, 168528943793901529⟩
def pI1030 : Prm := ⟨64, 32, 29, 1032, 11, 18446744073709551616, 168526744770645977, 168528943793901529⟩
theorem L1030_fin : (prmOK pL1030 1030 && ptTest pL1030 (runFrom pL1030 (fmask pL1030) (cmask pL1030) (hmask pL1030) 1 1029 (true, (init pL1030), (init pL1030))) 1030 515 false) = true := by
  decide +kernel
theorem L1030_ok : RunOK pL1030 1030 (runFrom pL1030 (fmask pL1030) (cmask pL1030) (hmask pL1030) 1 1029 (true, (init pL1030), (init pL1030))) ∧ ptTest pL1030 (runFrom pL1030 (fmask pL1030) (cmask pL1030) (hmask pL1030) 1 1029 (true, (init pL1030), (init pL1030))) 1030 515 false = true :=
  fin_run (runOK_init (prmOK_of_and L1030_fin) true) (by decide) rfl L1030_fin ptTest_fst
theorem H1030_fin : (prmOK pH1030 1030 && ptTest pH1030 (runFrom pH1030 (fmask pH1030) (cmask pH1030) (hmask pH1030) 1 1029 (true, (init pH1030), (init pH1030))) 1030 515 true) = true := by
  decide +kernel
theorem H1030_ok : RunOK pH1030 1030 (runFrom pH1030 (fmask pH1030) (cmask pH1030) (hmask pH1030) 1 1029 (true, (init pH1030), (init pH1030))) ∧ ptTest pH1030 (runFrom pH1030 (fmask pH1030) (cmask pH1030) (hmask pH1030) 1 1029 (true, (init pH1030), (init pH1030))) 1030 515 true = true :=
  fin_run (runOK_init (prmOK_of_and H1030_fin) true) (by decide) rfl H1030_fin ptTest_fst
theorem I1030_fin : (prmOK pI1030 1030 && intTest pI1030 (runFrom pI1030 (fmask pI1030) (cmask pI1030) (hmask pI1030) 1 1029 (true, (init pI1030), (init pI1030))) 1030 18 true) = true := by
  decide +kernel
theorem I1030_ok : RunOK pI1030 1030 (runFrom pI1030 (fmask pI1030) (cmask pI1030) (hmask pI1030) 1 1029 (true, (init pI1030), (init pI1030))) ∧ intTest pI1030 (runFrom pI1030 (fmask pI1030) (cmask pI1030) (hmask pI1030) 1 1029 (true, (init pI1030), (init pI1030))) 1030 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1030_fin) true) (by decide) rfl I1030_fin intTest_fst
theorem link1030 : linkOK pL1030 pH1030 pI1030 = true := by decide +kernel
theorem cvx1030 : ConvexBetweenHumps 1030 :=
  cvx_of L1030_ok H1030_ok I1030_ok link1030 (by decide)
theorem cenlink1030 : cenLinkOK pI1030 1030 = true := by decide +kernel
theorem cen1030 : CenterUniqueMin 1030 ∧ DipHyp 1030 ∧ OnePointHyps 1030 :=
  cen_of L1030_ok H1030_ok I1030_ok link1030 cenlink1030

/-! ### `N = 1031` -/

def pL1031 : Prm := ⟨77, 37, 37, 1033, 11, 18446744073709551616, 168395976213731011, 168395976213731011⟩
def pH1031 : Prm := ⟨77, 37, 37, 1033, 11, 18446744073709551616, 168398175236986563, 168398175236986563⟩
def pI1031 : Prm := ⟨64, 32, 29, 1033, 11, 18446744073709551616, 168395976213731011, 168398175236986563⟩
theorem L1031_fin : (prmOK pL1031 1031 && ptTest pL1031 (runFrom pL1031 (fmask pL1031) (cmask pL1031) (hmask pL1031) 1 1030 (true, (init pL1031), (init pL1031))) 1031 516 false) = true := by
  decide +kernel
theorem L1031_ok : RunOK pL1031 1031 (runFrom pL1031 (fmask pL1031) (cmask pL1031) (hmask pL1031) 1 1030 (true, (init pL1031), (init pL1031))) ∧ ptTest pL1031 (runFrom pL1031 (fmask pL1031) (cmask pL1031) (hmask pL1031) 1 1030 (true, (init pL1031), (init pL1031))) 1031 516 false = true :=
  fin_run (runOK_init (prmOK_of_and L1031_fin) true) (by decide) rfl L1031_fin ptTest_fst
theorem H1031_fin : (prmOK pH1031 1031 && ptTest pH1031 (runFrom pH1031 (fmask pH1031) (cmask pH1031) (hmask pH1031) 1 1030 (true, (init pH1031), (init pH1031))) 1031 516 true) = true := by
  decide +kernel
theorem H1031_ok : RunOK pH1031 1031 (runFrom pH1031 (fmask pH1031) (cmask pH1031) (hmask pH1031) 1 1030 (true, (init pH1031), (init pH1031))) ∧ ptTest pH1031 (runFrom pH1031 (fmask pH1031) (cmask pH1031) (hmask pH1031) 1 1030 (true, (init pH1031), (init pH1031))) 1031 516 true = true :=
  fin_run (runOK_init (prmOK_of_and H1031_fin) true) (by decide) rfl H1031_fin ptTest_fst
theorem I1031_fin : (prmOK pI1031 1031 && intTest pI1031 (runFrom pI1031 (fmask pI1031) (cmask pI1031) (hmask pI1031) 1 1030 (true, (init pI1031), (init pI1031))) 1031 18 false) = true := by
  decide +kernel
theorem I1031_ok : RunOK pI1031 1031 (runFrom pI1031 (fmask pI1031) (cmask pI1031) (hmask pI1031) 1 1030 (true, (init pI1031), (init pI1031))) ∧ intTest pI1031 (runFrom pI1031 (fmask pI1031) (cmask pI1031) (hmask pI1031) 1 1030 (true, (init pI1031), (init pI1031))) 1031 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1031_fin) true) (by decide) rfl I1031_fin intTest_fst
theorem link1031 : linkOK pL1031 pH1031 pI1031 = true := by decide +kernel
theorem cvx1031 : ConvexBetweenHumps 1031 :=
  cvx_of L1031_ok H1031_ok I1031_ok link1031 (by decide)

/-! ### `N = 1032` -/

def pL1032 : Prm := ⟨77, 37, 37, 1034, 11, 18446744073709551616, 168265534577651472, 168265534577651472⟩
def pH1032 : Prm := ⟨77, 37, 37, 1034, 11, 18446744073709551616, 168267733600907024, 168267733600907024⟩
def pI1032 : Prm := ⟨64, 32, 29, 1034, 11, 18446744073709551616, 168265534577651472, 168267733600907024⟩
theorem L1032_fin : (prmOK pL1032 1032 && ptTest pL1032 (runFrom pL1032 (fmask pL1032) (cmask pL1032) (hmask pL1032) 1 1031 (true, (init pL1032), (init pL1032))) 1032 516 false) = true := by
  decide +kernel
theorem L1032_ok : RunOK pL1032 1032 (runFrom pL1032 (fmask pL1032) (cmask pL1032) (hmask pL1032) 1 1031 (true, (init pL1032), (init pL1032))) ∧ ptTest pL1032 (runFrom pL1032 (fmask pL1032) (cmask pL1032) (hmask pL1032) 1 1031 (true, (init pL1032), (init pL1032))) 1032 516 false = true :=
  fin_run (runOK_init (prmOK_of_and L1032_fin) true) (by decide) rfl L1032_fin ptTest_fst
theorem H1032_fin : (prmOK pH1032 1032 && ptTest pH1032 (runFrom pH1032 (fmask pH1032) (cmask pH1032) (hmask pH1032) 1 1031 (true, (init pH1032), (init pH1032))) 1032 516 true) = true := by
  decide +kernel
theorem H1032_ok : RunOK pH1032 1032 (runFrom pH1032 (fmask pH1032) (cmask pH1032) (hmask pH1032) 1 1031 (true, (init pH1032), (init pH1032))) ∧ ptTest pH1032 (runFrom pH1032 (fmask pH1032) (cmask pH1032) (hmask pH1032) 1 1031 (true, (init pH1032), (init pH1032))) 1032 516 true = true :=
  fin_run (runOK_init (prmOK_of_and H1032_fin) true) (by decide) rfl H1032_fin ptTest_fst
theorem I1032_fin : (prmOK pI1032 1032 && intTest pI1032 (runFrom pI1032 (fmask pI1032) (cmask pI1032) (hmask pI1032) 1 1031 (true, (init pI1032), (init pI1032))) 1032 18 true) = true := by
  decide +kernel
theorem I1032_ok : RunOK pI1032 1032 (runFrom pI1032 (fmask pI1032) (cmask pI1032) (hmask pI1032) 1 1031 (true, (init pI1032), (init pI1032))) ∧ intTest pI1032 (runFrom pI1032 (fmask pI1032) (cmask pI1032) (hmask pI1032) 1 1031 (true, (init pI1032), (init pI1032))) 1032 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1032_fin) true) (by decide) rfl I1032_fin intTest_fst
theorem link1032 : linkOK pL1032 pH1032 pI1032 = true := by decide +kernel
theorem cvx1032 : ConvexBetweenHumps 1032 :=
  cvx_of L1032_ok H1032_ok I1032_ok link1032 (by decide)
theorem cenlink1032 : cenLinkOK pI1032 1032 = true := by decide +kernel
theorem cen1032 : CenterUniqueMin 1032 ∧ DipHyp 1032 ∧ OnePointHyps 1032 :=
  cen_of L1032_ok H1032_ok I1032_ok link1032 cenlink1032

/-! ### `N = 1033` -/

def pL1033 : Prm := ⟨77, 37, 37, 1035, 11, 18446744073709551616, 168135208988563161, 168135208988563161⟩
def pH1033 : Prm := ⟨77, 37, 37, 1035, 11, 18446744073709551616, 168137408011818713, 168137408011818713⟩
def pI1033 : Prm := ⟨64, 32, 29, 1035, 11, 18446744073709551616, 168135208988563161, 168137408011818713⟩
theorem L1033_fin : (prmOK pL1033 1033 && ptTest pL1033 (runFrom pL1033 (fmask pL1033) (cmask pL1033) (hmask pL1033) 1 1032 (true, (init pL1033), (init pL1033))) 1033 517 false) = true := by
  decide +kernel
theorem L1033_ok : RunOK pL1033 1033 (runFrom pL1033 (fmask pL1033) (cmask pL1033) (hmask pL1033) 1 1032 (true, (init pL1033), (init pL1033))) ∧ ptTest pL1033 (runFrom pL1033 (fmask pL1033) (cmask pL1033) (hmask pL1033) 1 1032 (true, (init pL1033), (init pL1033))) 1033 517 false = true :=
  fin_run (runOK_init (prmOK_of_and L1033_fin) true) (by decide) rfl L1033_fin ptTest_fst
theorem H1033_fin : (prmOK pH1033 1033 && ptTest pH1033 (runFrom pH1033 (fmask pH1033) (cmask pH1033) (hmask pH1033) 1 1032 (true, (init pH1033), (init pH1033))) 1033 517 true) = true := by
  decide +kernel
theorem H1033_ok : RunOK pH1033 1033 (runFrom pH1033 (fmask pH1033) (cmask pH1033) (hmask pH1033) 1 1032 (true, (init pH1033), (init pH1033))) ∧ ptTest pH1033 (runFrom pH1033 (fmask pH1033) (cmask pH1033) (hmask pH1033) 1 1032 (true, (init pH1033), (init pH1033))) 1033 517 true = true :=
  fin_run (runOK_init (prmOK_of_and H1033_fin) true) (by decide) rfl H1033_fin ptTest_fst
theorem I1033_fin : (prmOK pI1033 1033 && intTest pI1033 (runFrom pI1033 (fmask pI1033) (cmask pI1033) (hmask pI1033) 1 1032 (true, (init pI1033), (init pI1033))) 1033 18 false) = true := by
  decide +kernel
theorem I1033_ok : RunOK pI1033 1033 (runFrom pI1033 (fmask pI1033) (cmask pI1033) (hmask pI1033) 1 1032 (true, (init pI1033), (init pI1033))) ∧ intTest pI1033 (runFrom pI1033 (fmask pI1033) (cmask pI1033) (hmask pI1033) 1 1032 (true, (init pI1033), (init pI1033))) 1033 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1033_fin) true) (by decide) rfl I1033_fin intTest_fst
theorem link1033 : linkOK pL1033 pH1033 pI1033 = true := by decide +kernel
theorem cvx1033 : ConvexBetweenHumps 1033 :=
  cvx_of L1033_ok H1033_ok I1033_ok link1033 (by decide)

/-! ### `N = 1034` -/

def pL1034 : Prm := ⟨77, 37, 37, 1036, 11, 18446744073709551616, 168005208536122743, 168005208536122743⟩
def pH1034 : Prm := ⟨77, 37, 37, 1036, 11, 18446744073709551616, 168007407559378295, 168007407559378295⟩
def pI1034 : Prm := ⟨64, 32, 29, 1036, 11, 18446744073709551616, 168005208536122743, 168007407559378295⟩
theorem L1034_fin : (prmOK pL1034 1034 && ptTest pL1034 (runFrom pL1034 (fmask pL1034) (cmask pL1034) (hmask pL1034) 1 1033 (true, (init pL1034), (init pL1034))) 1034 517 false) = true := by
  decide +kernel
theorem L1034_ok : RunOK pL1034 1034 (runFrom pL1034 (fmask pL1034) (cmask pL1034) (hmask pL1034) 1 1033 (true, (init pL1034), (init pL1034))) ∧ ptTest pL1034 (runFrom pL1034 (fmask pL1034) (cmask pL1034) (hmask pL1034) 1 1033 (true, (init pL1034), (init pL1034))) 1034 517 false = true :=
  fin_run (runOK_init (prmOK_of_and L1034_fin) true) (by decide) rfl L1034_fin ptTest_fst
theorem H1034_fin : (prmOK pH1034 1034 && ptTest pH1034 (runFrom pH1034 (fmask pH1034) (cmask pH1034) (hmask pH1034) 1 1033 (true, (init pH1034), (init pH1034))) 1034 517 true) = true := by
  decide +kernel
theorem H1034_ok : RunOK pH1034 1034 (runFrom pH1034 (fmask pH1034) (cmask pH1034) (hmask pH1034) 1 1033 (true, (init pH1034), (init pH1034))) ∧ ptTest pH1034 (runFrom pH1034 (fmask pH1034) (cmask pH1034) (hmask pH1034) 1 1033 (true, (init pH1034), (init pH1034))) 1034 517 true = true :=
  fin_run (runOK_init (prmOK_of_and H1034_fin) true) (by decide) rfl H1034_fin ptTest_fst
theorem I1034_fin : (prmOK pI1034 1034 && intTest pI1034 (runFrom pI1034 (fmask pI1034) (cmask pI1034) (hmask pI1034) 1 1033 (true, (init pI1034), (init pI1034))) 1034 18 true) = true := by
  decide +kernel
theorem I1034_ok : RunOK pI1034 1034 (runFrom pI1034 (fmask pI1034) (cmask pI1034) (hmask pI1034) 1 1033 (true, (init pI1034), (init pI1034))) ∧ intTest pI1034 (runFrom pI1034 (fmask pI1034) (cmask pI1034) (hmask pI1034) 1 1033 (true, (init pI1034), (init pI1034))) 1034 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1034_fin) true) (by decide) rfl I1034_fin intTest_fst
theorem link1034 : linkOK pL1034 pH1034 pI1034 = true := by decide +kernel
theorem cvx1034 : ConvexBetweenHumps 1034 :=
  cvx_of L1034_ok H1034_ok I1034_ok link1034 (by decide)
theorem cenlink1034 : cenLinkOK pI1034 1034 = true := by decide +kernel
theorem cen1034 : CenterUniqueMin 1034 ∧ DipHyp 1034 ∧ OnePointHyps 1034 :=
  cen_of L1034_ok H1034_ok I1034_ok link1034 cenlink1034

/-! ### `N = 1035` -/

def pL1035 : Prm := ⟨77, 37, 37, 1037, 11, 18446744073709551616, 167875323590884928, 167875323590884928⟩
def pH1035 : Prm := ⟨77, 37, 37, 1037, 11, 18446744073709551616, 167877522614140480, 167877522614140480⟩
def pI1035 : Prm := ⟨64, 32, 29, 1037, 11, 18446744073709551616, 167875323590884928, 167877522614140480⟩
theorem L1035_fin : (prmOK pL1035 1035 && ptTest pL1035 (runFrom pL1035 (fmask pL1035) (cmask pL1035) (hmask pL1035) 1 1034 (true, (init pL1035), (init pL1035))) 1035 518 false) = true := by
  decide +kernel
theorem L1035_ok : RunOK pL1035 1035 (runFrom pL1035 (fmask pL1035) (cmask pL1035) (hmask pL1035) 1 1034 (true, (init pL1035), (init pL1035))) ∧ ptTest pL1035 (runFrom pL1035 (fmask pL1035) (cmask pL1035) (hmask pL1035) 1 1034 (true, (init pL1035), (init pL1035))) 1035 518 false = true :=
  fin_run (runOK_init (prmOK_of_and L1035_fin) true) (by decide) rfl L1035_fin ptTest_fst
theorem H1035_fin : (prmOK pH1035 1035 && ptTest pH1035 (runFrom pH1035 (fmask pH1035) (cmask pH1035) (hmask pH1035) 1 1034 (true, (init pH1035), (init pH1035))) 1035 518 true) = true := by
  decide +kernel
theorem H1035_ok : RunOK pH1035 1035 (runFrom pH1035 (fmask pH1035) (cmask pH1035) (hmask pH1035) 1 1034 (true, (init pH1035), (init pH1035))) ∧ ptTest pH1035 (runFrom pH1035 (fmask pH1035) (cmask pH1035) (hmask pH1035) 1 1034 (true, (init pH1035), (init pH1035))) 1035 518 true = true :=
  fin_run (runOK_init (prmOK_of_and H1035_fin) true) (by decide) rfl H1035_fin ptTest_fst
theorem I1035_fin : (prmOK pI1035 1035 && intTest pI1035 (runFrom pI1035 (fmask pI1035) (cmask pI1035) (hmask pI1035) 1 1034 (true, (init pI1035), (init pI1035))) 1035 18 false) = true := by
  decide +kernel
theorem I1035_ok : RunOK pI1035 1035 (runFrom pI1035 (fmask pI1035) (cmask pI1035) (hmask pI1035) 1 1034 (true, (init pI1035), (init pI1035))) ∧ intTest pI1035 (runFrom pI1035 (fmask pI1035) (cmask pI1035) (hmask pI1035) 1 1034 (true, (init pI1035), (init pI1035))) 1035 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1035_fin) true) (by decide) rfl I1035_fin intTest_fst
theorem link1035 : linkOK pL1035 pH1035 pI1035 = true := by decide +kernel
theorem cvx1035 : ConvexBetweenHumps 1035 :=
  cvx_of L1035_ok H1035_ok I1035_ok link1035 (by decide)

/-! ### `N = 1036` -/

def pL1036 : Prm := ⟨77, 37, 37, 1038, 11, 18446744073709551616, 167745762011260000, 167745762011260000⟩
def pH1036 : Prm := ⟨77, 37, 37, 1038, 11, 18446744073709551616, 167747961034515552, 167747961034515552⟩
def pI1036 : Prm := ⟨64, 32, 29, 1038, 11, 18446744073709551616, 167745762011260000, 167747961034515552⟩
theorem L1036_fin : (prmOK pL1036 1036 && ptTest pL1036 (runFrom pL1036 (fmask pL1036) (cmask pL1036) (hmask pL1036) 1 1035 (true, (init pL1036), (init pL1036))) 1036 518 false) = true := by
  decide +kernel
theorem L1036_ok : RunOK pL1036 1036 (runFrom pL1036 (fmask pL1036) (cmask pL1036) (hmask pL1036) 1 1035 (true, (init pL1036), (init pL1036))) ∧ ptTest pL1036 (runFrom pL1036 (fmask pL1036) (cmask pL1036) (hmask pL1036) 1 1035 (true, (init pL1036), (init pL1036))) 1036 518 false = true :=
  fin_run (runOK_init (prmOK_of_and L1036_fin) true) (by decide) rfl L1036_fin ptTest_fst
theorem H1036_fin : (prmOK pH1036 1036 && ptTest pH1036 (runFrom pH1036 (fmask pH1036) (cmask pH1036) (hmask pH1036) 1 1035 (true, (init pH1036), (init pH1036))) 1036 518 true) = true := by
  decide +kernel
theorem H1036_ok : RunOK pH1036 1036 (runFrom pH1036 (fmask pH1036) (cmask pH1036) (hmask pH1036) 1 1035 (true, (init pH1036), (init pH1036))) ∧ ptTest pH1036 (runFrom pH1036 (fmask pH1036) (cmask pH1036) (hmask pH1036) 1 1035 (true, (init pH1036), (init pH1036))) 1036 518 true = true :=
  fin_run (runOK_init (prmOK_of_and H1036_fin) true) (by decide) rfl H1036_fin ptTest_fst
theorem I1036_fin : (prmOK pI1036 1036 && intTest pI1036 (runFrom pI1036 (fmask pI1036) (cmask pI1036) (hmask pI1036) 1 1035 (true, (init pI1036), (init pI1036))) 1036 18 true) = true := by
  decide +kernel
theorem I1036_ok : RunOK pI1036 1036 (runFrom pI1036 (fmask pI1036) (cmask pI1036) (hmask pI1036) 1 1035 (true, (init pI1036), (init pI1036))) ∧ intTest pI1036 (runFrom pI1036 (fmask pI1036) (cmask pI1036) (hmask pI1036) 1 1035 (true, (init pI1036), (init pI1036))) 1036 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1036_fin) true) (by decide) rfl I1036_fin intTest_fst
theorem link1036 : linkOK pL1036 pH1036 pI1036 = true := by decide +kernel
theorem cvx1036 : ConvexBetweenHumps 1036 :=
  cvx_of L1036_ok H1036_ok I1036_ok link1036 (by decide)
theorem cenlink1036 : cenLinkOK pI1036 1036 = true := by decide +kernel
theorem cen1036 : CenterUniqueMin 1036 ∧ DipHyp 1036 ∧ OnePointHyps 1036 :=
  cen_of L1036_ok H1036_ok I1036_ok link1036 cenlink1036

/-! ### `N = 1037` -/

def pL1037 : Prm := ⟨77, 37, 37, 1039, 11, 18446744073709551616, 167616315402406358, 167616315402406358⟩
def pH1037 : Prm := ⟨77, 37, 37, 1039, 11, 18446744073709551616, 167618514425661910, 167618514425661910⟩
def pI1037 : Prm := ⟨64, 32, 29, 1039, 11, 18446744073709551616, 167616315402406358, 167618514425661910⟩
theorem L1037_fin : (prmOK pL1037 1037 && ptTest pL1037 (runFrom pL1037 (fmask pL1037) (cmask pL1037) (hmask pL1037) 1 1036 (true, (init pL1037), (init pL1037))) 1037 519 false) = true := by
  decide +kernel
theorem L1037_ok : RunOK pL1037 1037 (runFrom pL1037 (fmask pL1037) (cmask pL1037) (hmask pL1037) 1 1036 (true, (init pL1037), (init pL1037))) ∧ ptTest pL1037 (runFrom pL1037 (fmask pL1037) (cmask pL1037) (hmask pL1037) 1 1036 (true, (init pL1037), (init pL1037))) 1037 519 false = true :=
  fin_run (runOK_init (prmOK_of_and L1037_fin) true) (by decide) rfl L1037_fin ptTest_fst
theorem H1037_fin : (prmOK pH1037 1037 && ptTest pH1037 (runFrom pH1037 (fmask pH1037) (cmask pH1037) (hmask pH1037) 1 1036 (true, (init pH1037), (init pH1037))) 1037 519 true) = true := by
  decide +kernel
theorem H1037_ok : RunOK pH1037 1037 (runFrom pH1037 (fmask pH1037) (cmask pH1037) (hmask pH1037) 1 1036 (true, (init pH1037), (init pH1037))) ∧ ptTest pH1037 (runFrom pH1037 (fmask pH1037) (cmask pH1037) (hmask pH1037) 1 1036 (true, (init pH1037), (init pH1037))) 1037 519 true = true :=
  fin_run (runOK_init (prmOK_of_and H1037_fin) true) (by decide) rfl H1037_fin ptTest_fst
theorem I1037_fin : (prmOK pI1037 1037 && intTest pI1037 (runFrom pI1037 (fmask pI1037) (cmask pI1037) (hmask pI1037) 1 1036 (true, (init pI1037), (init pI1037))) 1037 18 false) = true := by
  decide +kernel
theorem I1037_ok : RunOK pI1037 1037 (runFrom pI1037 (fmask pI1037) (cmask pI1037) (hmask pI1037) 1 1036 (true, (init pI1037), (init pI1037))) ∧ intTest pI1037 (runFrom pI1037 (fmask pI1037) (cmask pI1037) (hmask pI1037) 1 1036 (true, (init pI1037), (init pI1037))) 1037 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1037_fin) true) (by decide) rfl I1037_fin intTest_fst
theorem link1037 : linkOK pL1037 pH1037 pI1037 = true := by decide +kernel
theorem cvx1037 : ConvexBetweenHumps 1037 :=
  cvx_of L1037_ok H1037_ok I1037_ok link1037 (by decide)

/-! ### `N = 1038` -/

def pL1038 : Prm := ⟨77, 37, 37, 1040, 11, 18446744073709551616, 167487190401172447, 167487190401172447⟩
def pH1038 : Prm := ⟨77, 37, 37, 1040, 11, 18446744073709551616, 167489389424427999, 167489389424427999⟩
def pI1038 : Prm := ⟨64, 32, 29, 1040, 11, 18446744073709551616, 167487190401172447, 167489389424427999⟩
theorem L1038_fin : (prmOK pL1038 1038 && ptTest pL1038 (runFrom pL1038 (fmask pL1038) (cmask pL1038) (hmask pL1038) 1 1037 (true, (init pL1038), (init pL1038))) 1038 519 false) = true := by
  decide +kernel
theorem L1038_ok : RunOK pL1038 1038 (runFrom pL1038 (fmask pL1038) (cmask pL1038) (hmask pL1038) 1 1037 (true, (init pL1038), (init pL1038))) ∧ ptTest pL1038 (runFrom pL1038 (fmask pL1038) (cmask pL1038) (hmask pL1038) 1 1037 (true, (init pL1038), (init pL1038))) 1038 519 false = true :=
  fin_run (runOK_init (prmOK_of_and L1038_fin) true) (by decide) rfl L1038_fin ptTest_fst
theorem H1038_fin : (prmOK pH1038 1038 && ptTest pH1038 (runFrom pH1038 (fmask pH1038) (cmask pH1038) (hmask pH1038) 1 1037 (true, (init pH1038), (init pH1038))) 1038 519 true) = true := by
  decide +kernel
theorem H1038_ok : RunOK pH1038 1038 (runFrom pH1038 (fmask pH1038) (cmask pH1038) (hmask pH1038) 1 1037 (true, (init pH1038), (init pH1038))) ∧ ptTest pH1038 (runFrom pH1038 (fmask pH1038) (cmask pH1038) (hmask pH1038) 1 1037 (true, (init pH1038), (init pH1038))) 1038 519 true = true :=
  fin_run (runOK_init (prmOK_of_and H1038_fin) true) (by decide) rfl H1038_fin ptTest_fst
theorem I1038_fin : (prmOK pI1038 1038 && intTest pI1038 (runFrom pI1038 (fmask pI1038) (cmask pI1038) (hmask pI1038) 1 1037 (true, (init pI1038), (init pI1038))) 1038 18 true) = true := by
  decide +kernel
theorem I1038_ok : RunOK pI1038 1038 (runFrom pI1038 (fmask pI1038) (cmask pI1038) (hmask pI1038) 1 1037 (true, (init pI1038), (init pI1038))) ∧ intTest pI1038 (runFrom pI1038 (fmask pI1038) (cmask pI1038) (hmask pI1038) 1 1037 (true, (init pI1038), (init pI1038))) 1038 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1038_fin) true) (by decide) rfl I1038_fin intTest_fst
theorem link1038 : linkOK pL1038 pH1038 pI1038 = true := by decide +kernel
theorem cvx1038 : ConvexBetweenHumps 1038 :=
  cvx_of L1038_ok H1038_ok I1038_ok link1038 (by decide)
theorem cenlink1038 : cenLinkOK pI1038 1038 = true := by decide +kernel
theorem cen1038 : CenterUniqueMin 1038 ∧ DipHyp 1038 ∧ OnePointHyps 1038 :=
  cen_of L1038_ok H1038_ok I1038_ok link1038 cenlink1038

/-! ### `N = 1039` -/

def pL1039 : Prm := ⟨77, 37, 37, 1041, 11, 18446744073709551616, 167358179837654258, 167358179837654258⟩
def pH1039 : Prm := ⟨77, 37, 37, 1041, 11, 18446744073709551616, 167360378860909810, 167360378860909810⟩
def pI1039 : Prm := ⟨64, 32, 29, 1041, 11, 18446744073709551616, 167358179837654258, 167360378860909810⟩
theorem L1039_fin : (prmOK pL1039 1039 && ptTest pL1039 (runFrom pL1039 (fmask pL1039) (cmask pL1039) (hmask pL1039) 1 1038 (true, (init pL1039), (init pL1039))) 1039 520 false) = true := by
  decide +kernel
theorem L1039_ok : RunOK pL1039 1039 (runFrom pL1039 (fmask pL1039) (cmask pL1039) (hmask pL1039) 1 1038 (true, (init pL1039), (init pL1039))) ∧ ptTest pL1039 (runFrom pL1039 (fmask pL1039) (cmask pL1039) (hmask pL1039) 1 1038 (true, (init pL1039), (init pL1039))) 1039 520 false = true :=
  fin_run (runOK_init (prmOK_of_and L1039_fin) true) (by decide) rfl L1039_fin ptTest_fst
theorem H1039_fin : (prmOK pH1039 1039 && ptTest pH1039 (runFrom pH1039 (fmask pH1039) (cmask pH1039) (hmask pH1039) 1 1038 (true, (init pH1039), (init pH1039))) 1039 520 true) = true := by
  decide +kernel
theorem H1039_ok : RunOK pH1039 1039 (runFrom pH1039 (fmask pH1039) (cmask pH1039) (hmask pH1039) 1 1038 (true, (init pH1039), (init pH1039))) ∧ ptTest pH1039 (runFrom pH1039 (fmask pH1039) (cmask pH1039) (hmask pH1039) 1 1038 (true, (init pH1039), (init pH1039))) 1039 520 true = true :=
  fin_run (runOK_init (prmOK_of_and H1039_fin) true) (by decide) rfl H1039_fin ptTest_fst
theorem I1039_fin : (prmOK pI1039 1039 && intTest pI1039 (runFrom pI1039 (fmask pI1039) (cmask pI1039) (hmask pI1039) 1 1038 (true, (init pI1039), (init pI1039))) 1039 18 false) = true := by
  decide +kernel
theorem I1039_ok : RunOK pI1039 1039 (runFrom pI1039 (fmask pI1039) (cmask pI1039) (hmask pI1039) 1 1038 (true, (init pI1039), (init pI1039))) ∧ intTest pI1039 (runFrom pI1039 (fmask pI1039) (cmask pI1039) (hmask pI1039) 1 1038 (true, (init pI1039), (init pI1039))) 1039 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1039_fin) true) (by decide) rfl I1039_fin intTest_fst
theorem link1039 : linkOK pL1039 pH1039 pI1039 = true := by decide +kernel
theorem cvx1039 : ConvexBetweenHumps 1039 :=
  cvx_of L1039_ok H1039_ok I1039_ok link1039 (by decide)

/-! ### `N = 1040` -/

def pL1040 : Prm := ⟨77, 37, 37, 1042, 11, 18446744073709551616, 167229489136601576, 167229489136601576⟩
def pH1040 : Prm := ⟨77, 37, 37, 1042, 11, 18446744073709551616, 167231688159857128, 167231688159857128⟩
def pI1040 : Prm := ⟨64, 32, 29, 1042, 11, 18446744073709551616, 167229489136601576, 167231688159857128⟩
theorem L1040_fin : (prmOK pL1040 1040 && ptTest pL1040 (runFrom pL1040 (fmask pL1040) (cmask pL1040) (hmask pL1040) 1 1039 (true, (init pL1040), (init pL1040))) 1040 520 false) = true := by
  decide +kernel
theorem L1040_ok : RunOK pL1040 1040 (runFrom pL1040 (fmask pL1040) (cmask pL1040) (hmask pL1040) 1 1039 (true, (init pL1040), (init pL1040))) ∧ ptTest pL1040 (runFrom pL1040 (fmask pL1040) (cmask pL1040) (hmask pL1040) 1 1039 (true, (init pL1040), (init pL1040))) 1040 520 false = true :=
  fin_run (runOK_init (prmOK_of_and L1040_fin) true) (by decide) rfl L1040_fin ptTest_fst
theorem H1040_fin : (prmOK pH1040 1040 && ptTest pH1040 (runFrom pH1040 (fmask pH1040) (cmask pH1040) (hmask pH1040) 1 1039 (true, (init pH1040), (init pH1040))) 1040 520 true) = true := by
  decide +kernel
theorem H1040_ok : RunOK pH1040 1040 (runFrom pH1040 (fmask pH1040) (cmask pH1040) (hmask pH1040) 1 1039 (true, (init pH1040), (init pH1040))) ∧ ptTest pH1040 (runFrom pH1040 (fmask pH1040) (cmask pH1040) (hmask pH1040) 1 1039 (true, (init pH1040), (init pH1040))) 1040 520 true = true :=
  fin_run (runOK_init (prmOK_of_and H1040_fin) true) (by decide) rfl H1040_fin ptTest_fst
theorem I1040_fin : (prmOK pI1040 1040 && intTest pI1040 (runFrom pI1040 (fmask pI1040) (cmask pI1040) (hmask pI1040) 1 1039 (true, (init pI1040), (init pI1040))) 1040 18 true) = true := by
  decide +kernel
theorem I1040_ok : RunOK pI1040 1040 (runFrom pI1040 (fmask pI1040) (cmask pI1040) (hmask pI1040) 1 1039 (true, (init pI1040), (init pI1040))) ∧ intTest pI1040 (runFrom pI1040 (fmask pI1040) (cmask pI1040) (hmask pI1040) 1 1039 (true, (init pI1040), (init pI1040))) 1040 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1040_fin) true) (by decide) rfl I1040_fin intTest_fst
theorem link1040 : linkOK pL1040 pH1040 pI1040 = true := by decide +kernel
theorem cvx1040 : ConvexBetweenHumps 1040 :=
  cvx_of L1040_ok H1040_ok I1040_ok link1040 (by decide)
theorem cenlink1040 : cenLinkOK pI1040 1040 = true := by decide +kernel
theorem cen1040 : CenterUniqueMin 1040 ∧ DipHyp 1040 ∧ OnePointHyps 1040 :=
  cen_of L1040_ok H1040_ok I1040_ok link1040 cenlink1040

/-! ### `N = 1041` -/

def pL1041 : Prm := ⟨77, 37, 37, 1043, 11, 18446744073709551616, 167100912343584807, 167100912343584807⟩
def pH1041 : Prm := ⟨77, 37, 37, 1043, 11, 18446744073709551616, 167103111366840359, 167103111366840359⟩
def pI1041 : Prm := ⟨64, 32, 29, 1043, 11, 18446744073709551616, 167100912343584807, 167103111366840359⟩
theorem L1041_fin : (prmOK pL1041 1041 && ptTest pL1041 (runFrom pL1041 (fmask pL1041) (cmask pL1041) (hmask pL1041) 1 1040 (true, (init pL1041), (init pL1041))) 1041 521 false) = true := by
  decide +kernel
theorem L1041_ok : RunOK pL1041 1041 (runFrom pL1041 (fmask pL1041) (cmask pL1041) (hmask pL1041) 1 1040 (true, (init pL1041), (init pL1041))) ∧ ptTest pL1041 (runFrom pL1041 (fmask pL1041) (cmask pL1041) (hmask pL1041) 1 1040 (true, (init pL1041), (init pL1041))) 1041 521 false = true :=
  fin_run (runOK_init (prmOK_of_and L1041_fin) true) (by decide) rfl L1041_fin ptTest_fst
theorem H1041_fin : (prmOK pH1041 1041 && ptTest pH1041 (runFrom pH1041 (fmask pH1041) (cmask pH1041) (hmask pH1041) 1 1040 (true, (init pH1041), (init pH1041))) 1041 521 true) = true := by
  decide +kernel
theorem H1041_ok : RunOK pH1041 1041 (runFrom pH1041 (fmask pH1041) (cmask pH1041) (hmask pH1041) 1 1040 (true, (init pH1041), (init pH1041))) ∧ ptTest pH1041 (runFrom pH1041 (fmask pH1041) (cmask pH1041) (hmask pH1041) 1 1040 (true, (init pH1041), (init pH1041))) 1041 521 true = true :=
  fin_run (runOK_init (prmOK_of_and H1041_fin) true) (by decide) rfl H1041_fin ptTest_fst
theorem I1041_fin : (prmOK pI1041 1041 && intTest pI1041 (runFrom pI1041 (fmask pI1041) (cmask pI1041) (hmask pI1041) 1 1040 (true, (init pI1041), (init pI1041))) 1041 18 false) = true := by
  decide +kernel
theorem I1041_ok : RunOK pI1041 1041 (runFrom pI1041 (fmask pI1041) (cmask pI1041) (hmask pI1041) 1 1040 (true, (init pI1041), (init pI1041))) ∧ intTest pI1041 (runFrom pI1041 (fmask pI1041) (cmask pI1041) (hmask pI1041) 1 1040 (true, (init pI1041), (init pI1041))) 1041 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1041_fin) true) (by decide) rfl I1041_fin intTest_fst
theorem link1041 : linkOK pL1041 pH1041 pI1041 = true := by decide +kernel
theorem cvx1041 : ConvexBetweenHumps 1041 :=
  cvx_of L1041_ok H1041_ok I1041_ok link1041 (by decide)

/-! ### `N = 1042` -/

def pL1042 : Prm := ⟨77, 37, 37, 1044, 11, 18446744073709551616, 166972653680644470, 166972653680644470⟩
def pH1042 : Prm := ⟨77, 37, 37, 1044, 11, 18446744073709551616, 166974852703900022, 166974852703900022⟩
def pI1042 : Prm := ⟨64, 32, 29, 1044, 11, 18446744073709551616, 166972653680644470, 166974852703900022⟩
theorem L1042_fin : (prmOK pL1042 1042 && ptTest pL1042 (runFrom pL1042 (fmask pL1042) (cmask pL1042) (hmask pL1042) 1 1041 (true, (init pL1042), (init pL1042))) 1042 521 false) = true := by
  decide +kernel
theorem L1042_ok : RunOK pL1042 1042 (runFrom pL1042 (fmask pL1042) (cmask pL1042) (hmask pL1042) 1 1041 (true, (init pL1042), (init pL1042))) ∧ ptTest pL1042 (runFrom pL1042 (fmask pL1042) (cmask pL1042) (hmask pL1042) 1 1041 (true, (init pL1042), (init pL1042))) 1042 521 false = true :=
  fin_run (runOK_init (prmOK_of_and L1042_fin) true) (by decide) rfl L1042_fin ptTest_fst
theorem H1042_fin : (prmOK pH1042 1042 && ptTest pH1042 (runFrom pH1042 (fmask pH1042) (cmask pH1042) (hmask pH1042) 1 1041 (true, (init pH1042), (init pH1042))) 1042 521 true) = true := by
  decide +kernel
theorem H1042_ok : RunOK pH1042 1042 (runFrom pH1042 (fmask pH1042) (cmask pH1042) (hmask pH1042) 1 1041 (true, (init pH1042), (init pH1042))) ∧ ptTest pH1042 (runFrom pH1042 (fmask pH1042) (cmask pH1042) (hmask pH1042) 1 1041 (true, (init pH1042), (init pH1042))) 1042 521 true = true :=
  fin_run (runOK_init (prmOK_of_and H1042_fin) true) (by decide) rfl H1042_fin ptTest_fst
theorem I1042_fin : (prmOK pI1042 1042 && intTest pI1042 (runFrom pI1042 (fmask pI1042) (cmask pI1042) (hmask pI1042) 1 1041 (true, (init pI1042), (init pI1042))) 1042 18 true) = true := by
  decide +kernel
theorem I1042_ok : RunOK pI1042 1042 (runFrom pI1042 (fmask pI1042) (cmask pI1042) (hmask pI1042) 1 1041 (true, (init pI1042), (init pI1042))) ∧ intTest pI1042 (runFrom pI1042 (fmask pI1042) (cmask pI1042) (hmask pI1042) 1 1041 (true, (init pI1042), (init pI1042))) 1042 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1042_fin) true) (by decide) rfl I1042_fin intTest_fst
theorem link1042 : linkOK pL1042 pH1042 pI1042 = true := by decide +kernel
theorem cvx1042 : ConvexBetweenHumps 1042 :=
  cvx_of L1042_ok H1042_ok I1042_ok link1042 (by decide)
theorem cenlink1042 : cenLinkOK pI1042 1042 = true := by decide +kernel
theorem cen1042 : CenterUniqueMin 1042 ∧ DipHyp 1042 ∧ OnePointHyps 1042 :=
  cen_of L1042_ok H1042_ok I1042_ok link1042 cenlink1042

/-! ### `N = 1043` -/

def pL1043 : Prm := ⟨77, 37, 37, 1045, 11, 18446744073709551616, 166844508399380649, 166844508399380649⟩
def pH1043 : Prm := ⟨77, 37, 37, 1045, 11, 18446744073709551616, 166846707422636201, 166846707422636201⟩
def pI1043 : Prm := ⟨64, 32, 29, 1045, 11, 18446744073709551616, 166844508399380649, 166846707422636201⟩
theorem L1043_fin : (prmOK pL1043 1043 && ptTest pL1043 (runFrom pL1043 (fmask pL1043) (cmask pL1043) (hmask pL1043) 1 1042 (true, (init pL1043), (init pL1043))) 1043 522 false) = true := by
  decide +kernel
theorem L1043_ok : RunOK pL1043 1043 (runFrom pL1043 (fmask pL1043) (cmask pL1043) (hmask pL1043) 1 1042 (true, (init pL1043), (init pL1043))) ∧ ptTest pL1043 (runFrom pL1043 (fmask pL1043) (cmask pL1043) (hmask pL1043) 1 1042 (true, (init pL1043), (init pL1043))) 1043 522 false = true :=
  fin_run (runOK_init (prmOK_of_and L1043_fin) true) (by decide) rfl L1043_fin ptTest_fst
theorem H1043_fin : (prmOK pH1043 1043 && ptTest pH1043 (runFrom pH1043 (fmask pH1043) (cmask pH1043) (hmask pH1043) 1 1042 (true, (init pH1043), (init pH1043))) 1043 522 true) = true := by
  decide +kernel
theorem H1043_ok : RunOK pH1043 1043 (runFrom pH1043 (fmask pH1043) (cmask pH1043) (hmask pH1043) 1 1042 (true, (init pH1043), (init pH1043))) ∧ ptTest pH1043 (runFrom pH1043 (fmask pH1043) (cmask pH1043) (hmask pH1043) 1 1042 (true, (init pH1043), (init pH1043))) 1043 522 true = true :=
  fin_run (runOK_init (prmOK_of_and H1043_fin) true) (by decide) rfl H1043_fin ptTest_fst
theorem I1043_fin : (prmOK pI1043 1043 && intTest pI1043 (runFrom pI1043 (fmask pI1043) (cmask pI1043) (hmask pI1043) 1 1042 (true, (init pI1043), (init pI1043))) 1043 18 false) = true := by
  decide +kernel
theorem I1043_ok : RunOK pI1043 1043 (runFrom pI1043 (fmask pI1043) (cmask pI1043) (hmask pI1043) 1 1042 (true, (init pI1043), (init pI1043))) ∧ intTest pI1043 (runFrom pI1043 (fmask pI1043) (cmask pI1043) (hmask pI1043) 1 1042 (true, (init pI1043), (init pI1043))) 1043 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1043_fin) true) (by decide) rfl I1043_fin intTest_fst
theorem link1043 : linkOK pL1043 pH1043 pI1043 = true := by decide +kernel
theorem cvx1043 : ConvexBetweenHumps 1043 :=
  cvx_of L1043_ok H1043_ok I1043_ok link1043 (by decide)

/-! ### `N = 1044` -/

def pL1044 : Prm := ⟨77, 37, 37, 1046, 11, 18446744073709551616, 166716679528477097, 166716679528477097⟩
def pH1044 : Prm := ⟨77, 37, 37, 1046, 11, 18446744073709551616, 166718878551732649, 166718878551732649⟩
def pI1044 : Prm := ⟨64, 32, 29, 1046, 11, 18446744073709551616, 166716679528477097, 166718878551732649⟩
theorem L1044_fin : (prmOK pL1044 1044 && ptTest pL1044 (runFrom pL1044 (fmask pL1044) (cmask pL1044) (hmask pL1044) 1 1043 (true, (init pL1044), (init pL1044))) 1044 522 false) = true := by
  decide +kernel
theorem L1044_ok : RunOK pL1044 1044 (runFrom pL1044 (fmask pL1044) (cmask pL1044) (hmask pL1044) 1 1043 (true, (init pL1044), (init pL1044))) ∧ ptTest pL1044 (runFrom pL1044 (fmask pL1044) (cmask pL1044) (hmask pL1044) 1 1043 (true, (init pL1044), (init pL1044))) 1044 522 false = true :=
  fin_run (runOK_init (prmOK_of_and L1044_fin) true) (by decide) rfl L1044_fin ptTest_fst
theorem H1044_fin : (prmOK pH1044 1044 && ptTest pH1044 (runFrom pH1044 (fmask pH1044) (cmask pH1044) (hmask pH1044) 1 1043 (true, (init pH1044), (init pH1044))) 1044 522 true) = true := by
  decide +kernel
theorem H1044_ok : RunOK pH1044 1044 (runFrom pH1044 (fmask pH1044) (cmask pH1044) (hmask pH1044) 1 1043 (true, (init pH1044), (init pH1044))) ∧ ptTest pH1044 (runFrom pH1044 (fmask pH1044) (cmask pH1044) (hmask pH1044) 1 1043 (true, (init pH1044), (init pH1044))) 1044 522 true = true :=
  fin_run (runOK_init (prmOK_of_and H1044_fin) true) (by decide) rfl H1044_fin ptTest_fst
theorem I1044_fin : (prmOK pI1044 1044 && intTest pI1044 (runFrom pI1044 (fmask pI1044) (cmask pI1044) (hmask pI1044) 1 1043 (true, (init pI1044), (init pI1044))) 1044 18 true) = true := by
  decide +kernel
theorem I1044_ok : RunOK pI1044 1044 (runFrom pI1044 (fmask pI1044) (cmask pI1044) (hmask pI1044) 1 1043 (true, (init pI1044), (init pI1044))) ∧ intTest pI1044 (runFrom pI1044 (fmask pI1044) (cmask pI1044) (hmask pI1044) 1 1043 (true, (init pI1044), (init pI1044))) 1044 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1044_fin) true) (by decide) rfl I1044_fin intTest_fst
theorem link1044 : linkOK pL1044 pH1044 pI1044 = true := by decide +kernel
theorem cvx1044 : ConvexBetweenHumps 1044 :=
  cvx_of L1044_ok H1044_ok I1044_ok link1044 (by decide)
theorem cenlink1044 : cenLinkOK pI1044 1044 = true := by decide +kernel
theorem cen1044 : CenterUniqueMin 1044 ∧ DipHyp 1044 ∧ OnePointHyps 1044 :=
  cen_of L1044_ok H1044_ok I1044_ok link1044 cenlink1044

/-! ### `N = 1045` -/

def pL1045 : Prm := ⟨77, 37, 37, 1047, 11, 18446744073709551616, 166588963516155741, 166588963516155741⟩
def pH1045 : Prm := ⟨77, 37, 37, 1047, 11, 18446744073709551616, 166591162539411293, 166591162539411293⟩
def pI1045 : Prm := ⟨64, 32, 29, 1047, 11, 18446744073709551616, 166588963516155741, 166591162539411293⟩
theorem L1045_fin : (prmOK pL1045 1045 && ptTest pL1045 (runFrom pL1045 (fmask pL1045) (cmask pL1045) (hmask pL1045) 1 1044 (true, (init pL1045), (init pL1045))) 1045 523 false) = true := by
  decide +kernel
theorem L1045_ok : RunOK pL1045 1045 (runFrom pL1045 (fmask pL1045) (cmask pL1045) (hmask pL1045) 1 1044 (true, (init pL1045), (init pL1045))) ∧ ptTest pL1045 (runFrom pL1045 (fmask pL1045) (cmask pL1045) (hmask pL1045) 1 1044 (true, (init pL1045), (init pL1045))) 1045 523 false = true :=
  fin_run (runOK_init (prmOK_of_and L1045_fin) true) (by decide) rfl L1045_fin ptTest_fst
theorem H1045_fin : (prmOK pH1045 1045 && ptTest pH1045 (runFrom pH1045 (fmask pH1045) (cmask pH1045) (hmask pH1045) 1 1044 (true, (init pH1045), (init pH1045))) 1045 523 true) = true := by
  decide +kernel
theorem H1045_ok : RunOK pH1045 1045 (runFrom pH1045 (fmask pH1045) (cmask pH1045) (hmask pH1045) 1 1044 (true, (init pH1045), (init pH1045))) ∧ ptTest pH1045 (runFrom pH1045 (fmask pH1045) (cmask pH1045) (hmask pH1045) 1 1044 (true, (init pH1045), (init pH1045))) 1045 523 true = true :=
  fin_run (runOK_init (prmOK_of_and H1045_fin) true) (by decide) rfl H1045_fin ptTest_fst
theorem I1045_fin : (prmOK pI1045 1045 && intTest pI1045 (runFrom pI1045 (fmask pI1045) (cmask pI1045) (hmask pI1045) 1 1044 (true, (init pI1045), (init pI1045))) 1045 18 false) = true := by
  decide +kernel
theorem I1045_ok : RunOK pI1045 1045 (runFrom pI1045 (fmask pI1045) (cmask pI1045) (hmask pI1045) 1 1044 (true, (init pI1045), (init pI1045))) ∧ intTest pI1045 (runFrom pI1045 (fmask pI1045) (cmask pI1045) (hmask pI1045) 1 1044 (true, (init pI1045), (init pI1045))) 1045 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1045_fin) true) (by decide) rfl I1045_fin intTest_fst
theorem link1045 : linkOK pL1045 pH1045 pI1045 = true := by decide +kernel
theorem cvx1045 : ConvexBetweenHumps 1045 :=
  cvx_of L1045_ok H1045_ok I1045_ok link1045 (by decide)

/-! ### `N = 1046` -/

def pL1046 : Prm := ⟨77, 37, 37, 1048, 11, 18446744073709551616, 166461562207022276, 166461562207022276⟩
def pH1046 : Prm := ⟨77, 37, 37, 1048, 11, 18446744073709551616, 166463761230277828, 166463761230277828⟩
def pI1046 : Prm := ⟨64, 32, 29, 1048, 11, 18446744073709551616, 166461562207022276, 166463761230277828⟩
theorem L1046_fin : (prmOK pL1046 1046 && ptTest pL1046 (runFrom pL1046 (fmask pL1046) (cmask pL1046) (hmask pL1046) 1 1045 (true, (init pL1046), (init pL1046))) 1046 523 false) = true := by
  decide +kernel
theorem L1046_ok : RunOK pL1046 1046 (runFrom pL1046 (fmask pL1046) (cmask pL1046) (hmask pL1046) 1 1045 (true, (init pL1046), (init pL1046))) ∧ ptTest pL1046 (runFrom pL1046 (fmask pL1046) (cmask pL1046) (hmask pL1046) 1 1045 (true, (init pL1046), (init pL1046))) 1046 523 false = true :=
  fin_run (runOK_init (prmOK_of_and L1046_fin) true) (by decide) rfl L1046_fin ptTest_fst
theorem H1046_fin : (prmOK pH1046 1046 && ptTest pH1046 (runFrom pH1046 (fmask pH1046) (cmask pH1046) (hmask pH1046) 1 1045 (true, (init pH1046), (init pH1046))) 1046 523 true) = true := by
  decide +kernel
theorem H1046_ok : RunOK pH1046 1046 (runFrom pH1046 (fmask pH1046) (cmask pH1046) (hmask pH1046) 1 1045 (true, (init pH1046), (init pH1046))) ∧ ptTest pH1046 (runFrom pH1046 (fmask pH1046) (cmask pH1046) (hmask pH1046) 1 1045 (true, (init pH1046), (init pH1046))) 1046 523 true = true :=
  fin_run (runOK_init (prmOK_of_and H1046_fin) true) (by decide) rfl H1046_fin ptTest_fst
theorem I1046_fin : (prmOK pI1046 1046 && intTest pI1046 (runFrom pI1046 (fmask pI1046) (cmask pI1046) (hmask pI1046) 1 1045 (true, (init pI1046), (init pI1046))) 1046 18 true) = true := by
  decide +kernel
theorem I1046_ok : RunOK pI1046 1046 (runFrom pI1046 (fmask pI1046) (cmask pI1046) (hmask pI1046) 1 1045 (true, (init pI1046), (init pI1046))) ∧ intTest pI1046 (runFrom pI1046 (fmask pI1046) (cmask pI1046) (hmask pI1046) 1 1045 (true, (init pI1046), (init pI1046))) 1046 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1046_fin) true) (by decide) rfl I1046_fin intTest_fst
theorem link1046 : linkOK pL1046 pH1046 pI1046 = true := by decide +kernel
theorem cvx1046 : ConvexBetweenHumps 1046 :=
  cvx_of L1046_ok H1046_ok I1046_ok link1046 (by decide)
theorem cenlink1046 : cenLinkOK pI1046 1046 = true := by decide +kernel
theorem cen1046 : CenterUniqueMin 1046 ∧ DipHyp 1046 ∧ OnePointHyps 1046 :=
  cen_of L1046_ok H1046_ok I1046_ok link1046 cenlink1046

/-! ### `N = 1047` -/

def pL1047 : Prm := ⟨77, 37, 37, 1049, 11, 18446744073709551616, 166334273236623312, 166334273236623312⟩
def pH1047 : Prm := ⟨77, 37, 37, 1049, 11, 18446744073709551616, 166336472259878864, 166336472259878864⟩
def pI1047 : Prm := ⟨64, 32, 29, 1049, 11, 18446744073709551616, 166334273236623312, 166336472259878864⟩
theorem L1047_fin : (prmOK pL1047 1047 && ptTest pL1047 (runFrom pL1047 (fmask pL1047) (cmask pL1047) (hmask pL1047) 1 1046 (true, (init pL1047), (init pL1047))) 1047 524 false) = true := by
  decide +kernel
theorem L1047_ok : RunOK pL1047 1047 (runFrom pL1047 (fmask pL1047) (cmask pL1047) (hmask pL1047) 1 1046 (true, (init pL1047), (init pL1047))) ∧ ptTest pL1047 (runFrom pL1047 (fmask pL1047) (cmask pL1047) (hmask pL1047) 1 1046 (true, (init pL1047), (init pL1047))) 1047 524 false = true :=
  fin_run (runOK_init (prmOK_of_and L1047_fin) true) (by decide) rfl L1047_fin ptTest_fst
theorem H1047_fin : (prmOK pH1047 1047 && ptTest pH1047 (runFrom pH1047 (fmask pH1047) (cmask pH1047) (hmask pH1047) 1 1046 (true, (init pH1047), (init pH1047))) 1047 524 true) = true := by
  decide +kernel
theorem H1047_ok : RunOK pH1047 1047 (runFrom pH1047 (fmask pH1047) (cmask pH1047) (hmask pH1047) 1 1046 (true, (init pH1047), (init pH1047))) ∧ ptTest pH1047 (runFrom pH1047 (fmask pH1047) (cmask pH1047) (hmask pH1047) 1 1046 (true, (init pH1047), (init pH1047))) 1047 524 true = true :=
  fin_run (runOK_init (prmOK_of_and H1047_fin) true) (by decide) rfl H1047_fin ptTest_fst
theorem I1047_fin : (prmOK pI1047 1047 && intTest pI1047 (runFrom pI1047 (fmask pI1047) (cmask pI1047) (hmask pI1047) 1 1046 (true, (init pI1047), (init pI1047))) 1047 18 false) = true := by
  decide +kernel
theorem I1047_ok : RunOK pI1047 1047 (runFrom pI1047 (fmask pI1047) (cmask pI1047) (hmask pI1047) 1 1046 (true, (init pI1047), (init pI1047))) ∧ intTest pI1047 (runFrom pI1047 (fmask pI1047) (cmask pI1047) (hmask pI1047) 1 1046 (true, (init pI1047), (init pI1047))) 1047 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1047_fin) true) (by decide) rfl I1047_fin intTest_fst
theorem link1047 : linkOK pL1047 pH1047 pI1047 = true := by decide +kernel
theorem cvx1047 : ConvexBetweenHumps 1047 :=
  cvx_of L1047_ok H1047_ok I1047_ok link1047 (by decide)

/-! ### `N = 1048` -/

def pL1048 : Prm := ⟨77, 37, 37, 1050, 11, 18446744073709551616, 166207297274654521, 166207297274654521⟩
def pH1048 : Prm := ⟨77, 37, 37, 1050, 11, 18446744073709551616, 166209496297910073, 166209496297910073⟩
def pI1048 : Prm := ⟨64, 32, 29, 1050, 11, 18446744073709551616, 166207297274654521, 166209496297910073⟩
theorem L1048_fin : (prmOK pL1048 1048 && ptTest pL1048 (runFrom pL1048 (fmask pL1048) (cmask pL1048) (hmask pL1048) 1 1047 (true, (init pL1048), (init pL1048))) 1048 524 false) = true := by
  decide +kernel
theorem L1048_ok : RunOK pL1048 1048 (runFrom pL1048 (fmask pL1048) (cmask pL1048) (hmask pL1048) 1 1047 (true, (init pL1048), (init pL1048))) ∧ ptTest pL1048 (runFrom pL1048 (fmask pL1048) (cmask pL1048) (hmask pL1048) 1 1047 (true, (init pL1048), (init pL1048))) 1048 524 false = true :=
  fin_run (runOK_init (prmOK_of_and L1048_fin) true) (by decide) rfl L1048_fin ptTest_fst
theorem H1048_fin : (prmOK pH1048 1048 && ptTest pH1048 (runFrom pH1048 (fmask pH1048) (cmask pH1048) (hmask pH1048) 1 1047 (true, (init pH1048), (init pH1048))) 1048 524 true) = true := by
  decide +kernel
theorem H1048_ok : RunOK pH1048 1048 (runFrom pH1048 (fmask pH1048) (cmask pH1048) (hmask pH1048) 1 1047 (true, (init pH1048), (init pH1048))) ∧ ptTest pH1048 (runFrom pH1048 (fmask pH1048) (cmask pH1048) (hmask pH1048) 1 1047 (true, (init pH1048), (init pH1048))) 1048 524 true = true :=
  fin_run (runOK_init (prmOK_of_and H1048_fin) true) (by decide) rfl H1048_fin ptTest_fst
theorem I1048_fin : (prmOK pI1048 1048 && intTest pI1048 (runFrom pI1048 (fmask pI1048) (cmask pI1048) (hmask pI1048) 1 1047 (true, (init pI1048), (init pI1048))) 1048 18 true) = true := by
  decide +kernel
theorem I1048_ok : RunOK pI1048 1048 (runFrom pI1048 (fmask pI1048) (cmask pI1048) (hmask pI1048) 1 1047 (true, (init pI1048), (init pI1048))) ∧ intTest pI1048 (runFrom pI1048 (fmask pI1048) (cmask pI1048) (hmask pI1048) 1 1047 (true, (init pI1048), (init pI1048))) 1048 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1048_fin) true) (by decide) rfl I1048_fin intTest_fst
theorem link1048 : linkOK pL1048 pH1048 pI1048 = true := by decide +kernel
theorem cvx1048 : ConvexBetweenHumps 1048 :=
  cvx_of L1048_ok H1048_ok I1048_ok link1048 (by decide)
theorem cenlink1048 : cenLinkOK pI1048 1048 = true := by decide +kernel
theorem cen1048 : CenterUniqueMin 1048 ∧ DipHyp 1048 ∧ OnePointHyps 1048 :=
  cen_of L1048_ok H1048_ok I1048_ok link1048 cenlink1048

/-! ### `N = 1049` -/

def pL1049 : Prm := ⟨77, 37, 37, 1051, 11, 18446744073709551616, 166080433134856056, 166080433134856056⟩
def pH1049 : Prm := ⟨77, 37, 37, 1051, 11, 18446744073709551616, 166082632158111608, 166082632158111608⟩
def pI1049 : Prm := ⟨64, 32, 29, 1051, 11, 18446744073709551616, 166080433134856056, 166082632158111608⟩
theorem L1049_fin : (prmOK pL1049 1049 && ptTest pL1049 (runFrom pL1049 (fmask pL1049) (cmask pL1049) (hmask pL1049) 1 1048 (true, (init pL1049), (init pL1049))) 1049 525 false) = true := by
  decide +kernel
theorem L1049_ok : RunOK pL1049 1049 (runFrom pL1049 (fmask pL1049) (cmask pL1049) (hmask pL1049) 1 1048 (true, (init pL1049), (init pL1049))) ∧ ptTest pL1049 (runFrom pL1049 (fmask pL1049) (cmask pL1049) (hmask pL1049) 1 1048 (true, (init pL1049), (init pL1049))) 1049 525 false = true :=
  fin_run (runOK_init (prmOK_of_and L1049_fin) true) (by decide) rfl L1049_fin ptTest_fst
theorem H1049_fin : (prmOK pH1049 1049 && ptTest pH1049 (runFrom pH1049 (fmask pH1049) (cmask pH1049) (hmask pH1049) 1 1048 (true, (init pH1049), (init pH1049))) 1049 525 true) = true := by
  decide +kernel
theorem H1049_ok : RunOK pH1049 1049 (runFrom pH1049 (fmask pH1049) (cmask pH1049) (hmask pH1049) 1 1048 (true, (init pH1049), (init pH1049))) ∧ ptTest pH1049 (runFrom pH1049 (fmask pH1049) (cmask pH1049) (hmask pH1049) 1 1048 (true, (init pH1049), (init pH1049))) 1049 525 true = true :=
  fin_run (runOK_init (prmOK_of_and H1049_fin) true) (by decide) rfl H1049_fin ptTest_fst
theorem I1049_fin : (prmOK pI1049 1049 && intTest pI1049 (runFrom pI1049 (fmask pI1049) (cmask pI1049) (hmask pI1049) 1 1048 (true, (init pI1049), (init pI1049))) 1049 18 false) = true := by
  decide +kernel
theorem I1049_ok : RunOK pI1049 1049 (runFrom pI1049 (fmask pI1049) (cmask pI1049) (hmask pI1049) 1 1048 (true, (init pI1049), (init pI1049))) ∧ intTest pI1049 (runFrom pI1049 (fmask pI1049) (cmask pI1049) (hmask pI1049) 1 1048 (true, (init pI1049), (init pI1049))) 1049 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1049_fin) true) (by decide) rfl I1049_fin intTest_fst
theorem link1049 : linkOK pL1049 pH1049 pI1049 = true := by decide +kernel
theorem cvx1049 : ConvexBetweenHumps 1049 :=
  cvx_of L1049_ok H1049_ok I1049_ok link1049 (by decide)

/-! ### The range -/

theorem cvx_1011_1049 {N : ℕ} (h1 : 1011 ≤ N) (h2 : N ≤ 1049) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1029
  · by_cases h4 : N ≤ 1019
    · by_cases h6 : N ≤ 1014
      · by_cases h8 : N ≤ 1012
        · by_cases h10 : N ≤ 1011
          · obtain rfl : N = 1011 := by omega
            exact cvx1011
          · obtain rfl : N = 1012 := by omega
            exact cvx1012
        · by_cases h10 : N ≤ 1013
          · obtain rfl : N = 1013 := by omega
            exact cvx1013
          · obtain rfl : N = 1014 := by omega
            exact cvx1014
      · by_cases h8 : N ≤ 1016
        · by_cases h10 : N ≤ 1015
          · obtain rfl : N = 1015 := by omega
            exact cvx1015
          · obtain rfl : N = 1016 := by omega
            exact cvx1016
        · by_cases h10 : N ≤ 1017
          · obtain rfl : N = 1017 := by omega
            exact cvx1017
          · by_cases h12 : N ≤ 1018
            · obtain rfl : N = 1018 := by omega
              exact cvx1018
            · obtain rfl : N = 1019 := by omega
              exact cvx1019
    · by_cases h6 : N ≤ 1024
      · by_cases h8 : N ≤ 1021
        · by_cases h10 : N ≤ 1020
          · obtain rfl : N = 1020 := by omega
            exact cvx1020
          · obtain rfl : N = 1021 := by omega
            exact cvx1021
        · by_cases h10 : N ≤ 1022
          · obtain rfl : N = 1022 := by omega
            exact cvx1022
          · by_cases h12 : N ≤ 1023
            · obtain rfl : N = 1023 := by omega
              exact cvx1023
            · obtain rfl : N = 1024 := by omega
              exact cvx1024
      · by_cases h8 : N ≤ 1026
        · by_cases h10 : N ≤ 1025
          · obtain rfl : N = 1025 := by omega
            exact cvx1025
          · obtain rfl : N = 1026 := by omega
            exact cvx1026
        · by_cases h10 : N ≤ 1027
          · obtain rfl : N = 1027 := by omega
            exact cvx1027
          · by_cases h12 : N ≤ 1028
            · obtain rfl : N = 1028 := by omega
              exact cvx1028
            · obtain rfl : N = 1029 := by omega
              exact cvx1029
  · by_cases h4 : N ≤ 1039
    · by_cases h6 : N ≤ 1034
      · by_cases h8 : N ≤ 1031
        · by_cases h10 : N ≤ 1030
          · obtain rfl : N = 1030 := by omega
            exact cvx1030
          · obtain rfl : N = 1031 := by omega
            exact cvx1031
        · by_cases h10 : N ≤ 1032
          · obtain rfl : N = 1032 := by omega
            exact cvx1032
          · by_cases h12 : N ≤ 1033
            · obtain rfl : N = 1033 := by omega
              exact cvx1033
            · obtain rfl : N = 1034 := by omega
              exact cvx1034
      · by_cases h8 : N ≤ 1036
        · by_cases h10 : N ≤ 1035
          · obtain rfl : N = 1035 := by omega
            exact cvx1035
          · obtain rfl : N = 1036 := by omega
            exact cvx1036
        · by_cases h10 : N ≤ 1037
          · obtain rfl : N = 1037 := by omega
            exact cvx1037
          · by_cases h12 : N ≤ 1038
            · obtain rfl : N = 1038 := by omega
              exact cvx1038
            · obtain rfl : N = 1039 := by omega
              exact cvx1039
    · by_cases h6 : N ≤ 1044
      · by_cases h8 : N ≤ 1041
        · by_cases h10 : N ≤ 1040
          · obtain rfl : N = 1040 := by omega
            exact cvx1040
          · obtain rfl : N = 1041 := by omega
            exact cvx1041
        · by_cases h10 : N ≤ 1042
          · obtain rfl : N = 1042 := by omega
            exact cvx1042
          · by_cases h12 : N ≤ 1043
            · obtain rfl : N = 1043 := by omega
              exact cvx1043
            · obtain rfl : N = 1044 := by omega
              exact cvx1044
      · by_cases h8 : N ≤ 1046
        · by_cases h10 : N ≤ 1045
          · obtain rfl : N = 1045 := by omega
            exact cvx1045
          · obtain rfl : N = 1046 := by omega
            exact cvx1046
        · by_cases h10 : N ≤ 1047
          · obtain rfl : N = 1047 := by omega
            exact cvx1047
          · by_cases h12 : N ≤ 1048
            · obtain rfl : N = 1048 := by omega
              exact cvx1048
            · obtain rfl : N = 1049 := by omega
              exact cvx1049

theorem cen_1011_1049 {N : ℕ} (h1 : 1011 ≤ N) (h2 : N ≤ 1049) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1028
  · by_cases h4 : N ≤ 1018
    · by_cases h6 : N ≤ 1014
      · by_cases h8 : N ≤ 1012
        · obtain rfl : N = 1012 := by omega
          exact cen1012
        · obtain rfl : N = 1014 := by omega
          exact cen1014
      · by_cases h8 : N ≤ 1016
        · obtain rfl : N = 1016 := by omega
          exact cen1016
        · obtain rfl : N = 1018 := by omega
          exact cen1018
    · by_cases h6 : N ≤ 1022
      · by_cases h8 : N ≤ 1020
        · obtain rfl : N = 1020 := by omega
          exact cen1020
        · obtain rfl : N = 1022 := by omega
          exact cen1022
      · by_cases h8 : N ≤ 1024
        · obtain rfl : N = 1024 := by omega
          exact cen1024
        · by_cases h10 : N ≤ 1026
          · obtain rfl : N = 1026 := by omega
            exact cen1026
          · obtain rfl : N = 1028 := by omega
            exact cen1028
  · by_cases h4 : N ≤ 1038
    · by_cases h6 : N ≤ 1032
      · by_cases h8 : N ≤ 1030
        · obtain rfl : N = 1030 := by omega
          exact cen1030
        · obtain rfl : N = 1032 := by omega
          exact cen1032
      · by_cases h8 : N ≤ 1034
        · obtain rfl : N = 1034 := by omega
          exact cen1034
        · by_cases h10 : N ≤ 1036
          · obtain rfl : N = 1036 := by omega
            exact cen1036
          · obtain rfl : N = 1038 := by omega
            exact cen1038
    · by_cases h6 : N ≤ 1042
      · by_cases h8 : N ≤ 1040
        · obtain rfl : N = 1040 := by omega
          exact cen1040
        · obtain rfl : N = 1042 := by omega
          exact cen1042
      · by_cases h8 : N ≤ 1044
        · obtain rfl : N = 1044 := by omega
          exact cen1044
        · by_cases h10 : N ≤ 1046
          · obtain rfl : N = 1046 := by omega
            exact cen1046
          · obtain rfl : N = 1048 := by omega
            exact cen1048

end Kagey131.PaperD.T7
