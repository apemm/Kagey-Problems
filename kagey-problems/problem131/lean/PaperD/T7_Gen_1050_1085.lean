import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 1050, …, 1085` (generated)

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

/-! ### `N = 1050` -/

def pL1050 : Prm := ⟨77, 37, 37, 1052, 11, 18446744073709551616, 165953880321015578, 165953880321015578⟩
def pH1050 : Prm := ⟨77, 37, 37, 1052, 11, 18446744073709551616, 165956079344271130, 165956079344271130⟩
def pI1050 : Prm := ⟨64, 32, 29, 1052, 11, 18446744073709551616, 165953880321015578, 165956079344271130⟩
theorem L1050_fin : (prmOK pL1050 1050 && ptTest pL1050 (runFrom pL1050 (fmask pL1050) (cmask pL1050) (hmask pL1050) 1 1049 (true, (init pL1050), (init pL1050))) 1050 525 false) = true := by
  decide +kernel
theorem L1050_ok : RunOK pL1050 1050 (runFrom pL1050 (fmask pL1050) (cmask pL1050) (hmask pL1050) 1 1049 (true, (init pL1050), (init pL1050))) ∧ ptTest pL1050 (runFrom pL1050 (fmask pL1050) (cmask pL1050) (hmask pL1050) 1 1049 (true, (init pL1050), (init pL1050))) 1050 525 false = true :=
  fin_run (runOK_init (prmOK_of_and L1050_fin) true) (by decide) rfl L1050_fin ptTest_fst
theorem H1050_fin : (prmOK pH1050 1050 && ptTest pH1050 (runFrom pH1050 (fmask pH1050) (cmask pH1050) (hmask pH1050) 1 1049 (true, (init pH1050), (init pH1050))) 1050 525 true) = true := by
  decide +kernel
theorem H1050_ok : RunOK pH1050 1050 (runFrom pH1050 (fmask pH1050) (cmask pH1050) (hmask pH1050) 1 1049 (true, (init pH1050), (init pH1050))) ∧ ptTest pH1050 (runFrom pH1050 (fmask pH1050) (cmask pH1050) (hmask pH1050) 1 1049 (true, (init pH1050), (init pH1050))) 1050 525 true = true :=
  fin_run (runOK_init (prmOK_of_and H1050_fin) true) (by decide) rfl H1050_fin ptTest_fst
theorem I1050_fin : (prmOK pI1050 1050 && intTest pI1050 (runFrom pI1050 (fmask pI1050) (cmask pI1050) (hmask pI1050) 1 1049 (true, (init pI1050), (init pI1050))) 1050 18 true) = true := by
  decide +kernel
theorem I1050_ok : RunOK pI1050 1050 (runFrom pI1050 (fmask pI1050) (cmask pI1050) (hmask pI1050) 1 1049 (true, (init pI1050), (init pI1050))) ∧ intTest pI1050 (runFrom pI1050 (fmask pI1050) (cmask pI1050) (hmask pI1050) 1 1049 (true, (init pI1050), (init pI1050))) 1050 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1050_fin) true) (by decide) rfl I1050_fin intTest_fst
theorem link1050 : linkOK pL1050 pH1050 pI1050 = true := by decide +kernel
theorem cvx1050 : ConvexBetweenHumps 1050 :=
  cvx_of L1050_ok H1050_ok I1050_ok link1050 (by decide)
theorem cenlink1050 : cenLinkOK pI1050 1050 = true := by decide +kernel
theorem cen1050 : CenterUniqueMin 1050 ∧ DipHyp 1050 ∧ OnePointHyps 1050 :=
  cen_of L1050_ok H1050_ok I1050_ok link1050 cenlink1050

/-! ### `N = 1051` -/

def pL1051 : Prm := ⟨77, 37, 37, 1053, 11, 18446744073709551616, 165827438815972539, 165827438815972539⟩
def pH1051 : Prm := ⟨77, 37, 37, 1053, 11, 18446744073709551616, 165829637839228091, 165829637839228091⟩
def pI1051 : Prm := ⟨64, 32, 29, 1053, 11, 18446744073709551616, 165827438815972539, 165829637839228091⟩
theorem L1051_fin : (prmOK pL1051 1051 && ptTest pL1051 (runFrom pL1051 (fmask pL1051) (cmask pL1051) (hmask pL1051) 1 1050 (true, (init pL1051), (init pL1051))) 1051 526 false) = true := by
  decide +kernel
theorem L1051_ok : RunOK pL1051 1051 (runFrom pL1051 (fmask pL1051) (cmask pL1051) (hmask pL1051) 1 1050 (true, (init pL1051), (init pL1051))) ∧ ptTest pL1051 (runFrom pL1051 (fmask pL1051) (cmask pL1051) (hmask pL1051) 1 1050 (true, (init pL1051), (init pL1051))) 1051 526 false = true :=
  fin_run (runOK_init (prmOK_of_and L1051_fin) true) (by decide) rfl L1051_fin ptTest_fst
theorem H1051_fin : (prmOK pH1051 1051 && ptTest pH1051 (runFrom pH1051 (fmask pH1051) (cmask pH1051) (hmask pH1051) 1 1050 (true, (init pH1051), (init pH1051))) 1051 526 true) = true := by
  decide +kernel
theorem H1051_ok : RunOK pH1051 1051 (runFrom pH1051 (fmask pH1051) (cmask pH1051) (hmask pH1051) 1 1050 (true, (init pH1051), (init pH1051))) ∧ ptTest pH1051 (runFrom pH1051 (fmask pH1051) (cmask pH1051) (hmask pH1051) 1 1050 (true, (init pH1051), (init pH1051))) 1051 526 true = true :=
  fin_run (runOK_init (prmOK_of_and H1051_fin) true) (by decide) rfl H1051_fin ptTest_fst
theorem I1051_fin : (prmOK pI1051 1051 && intTest pI1051 (runFrom pI1051 (fmask pI1051) (cmask pI1051) (hmask pI1051) 1 1050 (true, (init pI1051), (init pI1051))) 1051 18 false) = true := by
  decide +kernel
theorem I1051_ok : RunOK pI1051 1051 (runFrom pI1051 (fmask pI1051) (cmask pI1051) (hmask pI1051) 1 1050 (true, (init pI1051), (init pI1051))) ∧ intTest pI1051 (runFrom pI1051 (fmask pI1051) (cmask pI1051) (hmask pI1051) 1 1050 (true, (init pI1051), (init pI1051))) 1051 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1051_fin) true) (by decide) rfl I1051_fin intTest_fst
theorem link1051 : linkOK pL1051 pH1051 pI1051 = true := by decide +kernel
theorem cvx1051 : ConvexBetweenHumps 1051 :=
  cvx_of L1051_ok H1051_ok I1051_ok link1051 (by decide)

/-! ### `N = 1052` -/

def pL1052 : Prm := ⟨77, 37, 37, 1054, 11, 18446744073709551616, 165701306966645491, 165701306966645491⟩
def pH1052 : Prm := ⟨77, 37, 37, 1054, 11, 18446744073709551616, 165703505989901043, 165703505989901043⟩
def pI1052 : Prm := ⟨64, 32, 29, 1054, 11, 18446744073709551616, 165701306966645491, 165703505989901043⟩
theorem L1052_fin : (prmOK pL1052 1052 && ptTest pL1052 (runFrom pL1052 (fmask pL1052) (cmask pL1052) (hmask pL1052) 1 1051 (true, (init pL1052), (init pL1052))) 1052 526 false) = true := by
  decide +kernel
theorem L1052_ok : RunOK pL1052 1052 (runFrom pL1052 (fmask pL1052) (cmask pL1052) (hmask pL1052) 1 1051 (true, (init pL1052), (init pL1052))) ∧ ptTest pL1052 (runFrom pL1052 (fmask pL1052) (cmask pL1052) (hmask pL1052) 1 1051 (true, (init pL1052), (init pL1052))) 1052 526 false = true :=
  fin_run (runOK_init (prmOK_of_and L1052_fin) true) (by decide) rfl L1052_fin ptTest_fst
theorem H1052_fin : (prmOK pH1052 1052 && ptTest pH1052 (runFrom pH1052 (fmask pH1052) (cmask pH1052) (hmask pH1052) 1 1051 (true, (init pH1052), (init pH1052))) 1052 526 true) = true := by
  decide +kernel
theorem H1052_ok : RunOK pH1052 1052 (runFrom pH1052 (fmask pH1052) (cmask pH1052) (hmask pH1052) 1 1051 (true, (init pH1052), (init pH1052))) ∧ ptTest pH1052 (runFrom pH1052 (fmask pH1052) (cmask pH1052) (hmask pH1052) 1 1051 (true, (init pH1052), (init pH1052))) 1052 526 true = true :=
  fin_run (runOK_init (prmOK_of_and H1052_fin) true) (by decide) rfl H1052_fin ptTest_fst
theorem I1052_fin : (prmOK pI1052 1052 && intTest pI1052 (runFrom pI1052 (fmask pI1052) (cmask pI1052) (hmask pI1052) 1 1051 (true, (init pI1052), (init pI1052))) 1052 18 true) = true := by
  decide +kernel
theorem I1052_ok : RunOK pI1052 1052 (runFrom pI1052 (fmask pI1052) (cmask pI1052) (hmask pI1052) 1 1051 (true, (init pI1052), (init pI1052))) ∧ intTest pI1052 (runFrom pI1052 (fmask pI1052) (cmask pI1052) (hmask pI1052) 1 1051 (true, (init pI1052), (init pI1052))) 1052 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1052_fin) true) (by decide) rfl I1052_fin intTest_fst
theorem link1052 : linkOK pL1052 pH1052 pI1052 = true := by decide +kernel
theorem cvx1052 : ConvexBetweenHumps 1052 :=
  cvx_of L1052_ok H1052_ok I1052_ok link1052 (by decide)
theorem cenlink1052 : cenLinkOK pI1052 1052 = true := by decide +kernel
theorem cen1052 : CenterUniqueMin 1052 ∧ DipHyp 1052 ∧ OnePointHyps 1052 :=
  cen_of L1052_ok H1052_ok I1052_ok link1052 cenlink1052

/-! ### `N = 1053` -/

def pL1053 : Prm := ⟨77, 37, 37, 1055, 11, 18446744073709551616, 165575285915915834, 165575285915915834⟩
def pH1053 : Prm := ⟨77, 37, 37, 1055, 11, 18446744073709551616, 165577484939171386, 165577484939171386⟩
def pI1053 : Prm := ⟨64, 32, 29, 1055, 11, 18446744073709551616, 165575285915915834, 165577484939171386⟩
theorem L1053_fin : (prmOK pL1053 1053 && ptTest pL1053 (runFrom pL1053 (fmask pL1053) (cmask pL1053) (hmask pL1053) 1 1052 (true, (init pL1053), (init pL1053))) 1053 527 false) = true := by
  decide +kernel
theorem L1053_ok : RunOK pL1053 1053 (runFrom pL1053 (fmask pL1053) (cmask pL1053) (hmask pL1053) 1 1052 (true, (init pL1053), (init pL1053))) ∧ ptTest pL1053 (runFrom pL1053 (fmask pL1053) (cmask pL1053) (hmask pL1053) 1 1052 (true, (init pL1053), (init pL1053))) 1053 527 false = true :=
  fin_run (runOK_init (prmOK_of_and L1053_fin) true) (by decide) rfl L1053_fin ptTest_fst
theorem H1053_fin : (prmOK pH1053 1053 && ptTest pH1053 (runFrom pH1053 (fmask pH1053) (cmask pH1053) (hmask pH1053) 1 1052 (true, (init pH1053), (init pH1053))) 1053 527 true) = true := by
  decide +kernel
theorem H1053_ok : RunOK pH1053 1053 (runFrom pH1053 (fmask pH1053) (cmask pH1053) (hmask pH1053) 1 1052 (true, (init pH1053), (init pH1053))) ∧ ptTest pH1053 (runFrom pH1053 (fmask pH1053) (cmask pH1053) (hmask pH1053) 1 1052 (true, (init pH1053), (init pH1053))) 1053 527 true = true :=
  fin_run (runOK_init (prmOK_of_and H1053_fin) true) (by decide) rfl H1053_fin ptTest_fst
theorem I1053_fin : (prmOK pI1053 1053 && intTest pI1053 (runFrom pI1053 (fmask pI1053) (cmask pI1053) (hmask pI1053) 1 1052 (true, (init pI1053), (init pI1053))) 1053 18 false) = true := by
  decide +kernel
theorem I1053_ok : RunOK pI1053 1053 (runFrom pI1053 (fmask pI1053) (cmask pI1053) (hmask pI1053) 1 1052 (true, (init pI1053), (init pI1053))) ∧ intTest pI1053 (runFrom pI1053 (fmask pI1053) (cmask pI1053) (hmask pI1053) 1 1052 (true, (init pI1053), (init pI1053))) 1053 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1053_fin) true) (by decide) rfl I1053_fin intTest_fst
theorem link1053 : linkOK pL1053 pH1053 pI1053 = true := by decide +kernel
theorem cvx1053 : ConvexBetweenHumps 1053 :=
  cvx_of L1053_ok H1053_ok I1053_ok link1053 (by decide)

/-! ### `N = 1054` -/

def pL1054 : Prm := ⟨77, 37, 37, 1056, 11, 18446744073709551616, 165449572862742790, 165449572862742790⟩
def pH1054 : Prm := ⟨77, 37, 37, 1056, 11, 18446744073709551616, 165451771885998342, 165451771885998342⟩
def pI1054 : Prm := ⟨64, 32, 29, 1056, 11, 18446744073709551616, 165449572862742790, 165451771885998342⟩
theorem L1054_fin : (prmOK pL1054 1054 && ptTest pL1054 (runFrom pL1054 (fmask pL1054) (cmask pL1054) (hmask pL1054) 1 1053 (true, (init pL1054), (init pL1054))) 1054 527 false) = true := by
  decide +kernel
theorem L1054_ok : RunOK pL1054 1054 (runFrom pL1054 (fmask pL1054) (cmask pL1054) (hmask pL1054) 1 1053 (true, (init pL1054), (init pL1054))) ∧ ptTest pL1054 (runFrom pL1054 (fmask pL1054) (cmask pL1054) (hmask pL1054) 1 1053 (true, (init pL1054), (init pL1054))) 1054 527 false = true :=
  fin_run (runOK_init (prmOK_of_and L1054_fin) true) (by decide) rfl L1054_fin ptTest_fst
theorem H1054_fin : (prmOK pH1054 1054 && ptTest pH1054 (runFrom pH1054 (fmask pH1054) (cmask pH1054) (hmask pH1054) 1 1053 (true, (init pH1054), (init pH1054))) 1054 527 true) = true := by
  decide +kernel
theorem H1054_ok : RunOK pH1054 1054 (runFrom pH1054 (fmask pH1054) (cmask pH1054) (hmask pH1054) 1 1053 (true, (init pH1054), (init pH1054))) ∧ ptTest pH1054 (runFrom pH1054 (fmask pH1054) (cmask pH1054) (hmask pH1054) 1 1053 (true, (init pH1054), (init pH1054))) 1054 527 true = true :=
  fin_run (runOK_init (prmOK_of_and H1054_fin) true) (by decide) rfl H1054_fin ptTest_fst
theorem I1054_fin : (prmOK pI1054 1054 && intTest pI1054 (runFrom pI1054 (fmask pI1054) (cmask pI1054) (hmask pI1054) 1 1053 (true, (init pI1054), (init pI1054))) 1054 18 true) = true := by
  decide +kernel
theorem I1054_ok : RunOK pI1054 1054 (runFrom pI1054 (fmask pI1054) (cmask pI1054) (hmask pI1054) 1 1053 (true, (init pI1054), (init pI1054))) ∧ intTest pI1054 (runFrom pI1054 (fmask pI1054) (cmask pI1054) (hmask pI1054) 1 1053 (true, (init pI1054), (init pI1054))) 1054 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1054_fin) true) (by decide) rfl I1054_fin intTest_fst
theorem link1054 : linkOK pL1054 pH1054 pI1054 = true := by decide +kernel
theorem cvx1054 : ConvexBetweenHumps 1054 :=
  cvx_of L1054_ok H1054_ok I1054_ok link1054 (by decide)
theorem cenlink1054 : cenLinkOK pI1054 1054 = true := by decide +kernel
theorem cen1054 : CenterUniqueMin 1054 ∧ DipHyp 1054 ∧ OnePointHyps 1054 :=
  cen_of L1054_ok H1054_ok I1054_ok link1054 cenlink1054

/-! ### `N = 1055` -/

def pL1055 : Prm := ⟨77, 37, 37, 1057, 11, 18446744073709551616, 165323970101139930, 165323970101139930⟩
def pH1055 : Prm := ⟨77, 37, 37, 1057, 11, 18446744073709551616, 165326169124395482, 165326169124395482⟩
def pI1055 : Prm := ⟨64, 32, 29, 1057, 11, 18446744073709551616, 165323970101139930, 165326169124395482⟩
theorem L1055_fin : (prmOK pL1055 1055 && ptTest pL1055 (runFrom pL1055 (fmask pL1055) (cmask pL1055) (hmask pL1055) 1 1054 (true, (init pL1055), (init pL1055))) 1055 528 false) = true := by
  decide +kernel
theorem L1055_ok : RunOK pL1055 1055 (runFrom pL1055 (fmask pL1055) (cmask pL1055) (hmask pL1055) 1 1054 (true, (init pL1055), (init pL1055))) ∧ ptTest pL1055 (runFrom pL1055 (fmask pL1055) (cmask pL1055) (hmask pL1055) 1 1054 (true, (init pL1055), (init pL1055))) 1055 528 false = true :=
  fin_run (runOK_init (prmOK_of_and L1055_fin) true) (by decide) rfl L1055_fin ptTest_fst
theorem H1055_fin : (prmOK pH1055 1055 && ptTest pH1055 (runFrom pH1055 (fmask pH1055) (cmask pH1055) (hmask pH1055) 1 1054 (true, (init pH1055), (init pH1055))) 1055 528 true) = true := by
  decide +kernel
theorem H1055_ok : RunOK pH1055 1055 (runFrom pH1055 (fmask pH1055) (cmask pH1055) (hmask pH1055) 1 1054 (true, (init pH1055), (init pH1055))) ∧ ptTest pH1055 (runFrom pH1055 (fmask pH1055) (cmask pH1055) (hmask pH1055) 1 1054 (true, (init pH1055), (init pH1055))) 1055 528 true = true :=
  fin_run (runOK_init (prmOK_of_and H1055_fin) true) (by decide) rfl H1055_fin ptTest_fst
theorem I1055_fin : (prmOK pI1055 1055 && intTest pI1055 (runFrom pI1055 (fmask pI1055) (cmask pI1055) (hmask pI1055) 1 1054 (true, (init pI1055), (init pI1055))) 1055 18 false) = true := by
  decide +kernel
theorem I1055_ok : RunOK pI1055 1055 (runFrom pI1055 (fmask pI1055) (cmask pI1055) (hmask pI1055) 1 1054 (true, (init pI1055), (init pI1055))) ∧ intTest pI1055 (runFrom pI1055 (fmask pI1055) (cmask pI1055) (hmask pI1055) 1 1054 (true, (init pI1055), (init pI1055))) 1055 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1055_fin) true) (by decide) rfl I1055_fin intTest_fst
theorem link1055 : linkOK pL1055 pH1055 pI1055 = true := by decide +kernel
theorem cvx1055 : ConvexBetweenHumps 1055 :=
  cvx_of L1055_ok H1055_ok I1055_ok link1055 (by decide)

/-! ### `N = 1056` -/

def pL1056 : Prm := ⟨77, 37, 37, 1058, 11, 18446744073709551616, 165198673690906241, 165198673690906241⟩
def pH1056 : Prm := ⟨77, 37, 37, 1058, 11, 18446744073709551616, 165200872714161793, 165200872714161793⟩
def pI1056 : Prm := ⟨64, 32, 29, 1058, 11, 18446744073709551616, 165198673690906241, 165200872714161793⟩
theorem L1056_fin : (prmOK pL1056 1056 && ptTest pL1056 (runFrom pL1056 (fmask pL1056) (cmask pL1056) (hmask pL1056) 1 1055 (true, (init pL1056), (init pL1056))) 1056 528 false) = true := by
  decide +kernel
theorem L1056_ok : RunOK pL1056 1056 (runFrom pL1056 (fmask pL1056) (cmask pL1056) (hmask pL1056) 1 1055 (true, (init pL1056), (init pL1056))) ∧ ptTest pL1056 (runFrom pL1056 (fmask pL1056) (cmask pL1056) (hmask pL1056) 1 1055 (true, (init pL1056), (init pL1056))) 1056 528 false = true :=
  fin_run (runOK_init (prmOK_of_and L1056_fin) true) (by decide) rfl L1056_fin ptTest_fst
theorem H1056_fin : (prmOK pH1056 1056 && ptTest pH1056 (runFrom pH1056 (fmask pH1056) (cmask pH1056) (hmask pH1056) 1 1055 (true, (init pH1056), (init pH1056))) 1056 528 true) = true := by
  decide +kernel
theorem H1056_ok : RunOK pH1056 1056 (runFrom pH1056 (fmask pH1056) (cmask pH1056) (hmask pH1056) 1 1055 (true, (init pH1056), (init pH1056))) ∧ ptTest pH1056 (runFrom pH1056 (fmask pH1056) (cmask pH1056) (hmask pH1056) 1 1055 (true, (init pH1056), (init pH1056))) 1056 528 true = true :=
  fin_run (runOK_init (prmOK_of_and H1056_fin) true) (by decide) rfl H1056_fin ptTest_fst
theorem I1056_fin : (prmOK pI1056 1056 && intTest pI1056 (runFrom pI1056 (fmask pI1056) (cmask pI1056) (hmask pI1056) 1 1055 (true, (init pI1056), (init pI1056))) 1056 18 true) = true := by
  decide +kernel
theorem I1056_ok : RunOK pI1056 1056 (runFrom pI1056 (fmask pI1056) (cmask pI1056) (hmask pI1056) 1 1055 (true, (init pI1056), (init pI1056))) ∧ intTest pI1056 (runFrom pI1056 (fmask pI1056) (cmask pI1056) (hmask pI1056) 1 1055 (true, (init pI1056), (init pI1056))) 1056 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1056_fin) true) (by decide) rfl I1056_fin intTest_fst
theorem link1056 : linkOK pL1056 pH1056 pI1056 = true := by decide +kernel
theorem cvx1056 : ConvexBetweenHumps 1056 :=
  cvx_of L1056_ok H1056_ok I1056_ok link1056 (by decide)
theorem cenlink1056 : cenLinkOK pI1056 1056 = true := by decide +kernel
theorem cen1056 : CenterUniqueMin 1056 ∧ DipHyp 1056 ∧ OnePointHyps 1056 :=
  cen_of L1056_ok H1056_ok I1056_ok link1056 cenlink1056

/-! ### `N = 1057` -/

def pL1057 : Prm := ⟨77, 37, 37, 1059, 11, 18446744073709551616, 165073487068333028, 165073487068333028⟩
def pH1057 : Prm := ⟨77, 37, 37, 1059, 11, 18446744073709551616, 165075686091588580, 165075686091588580⟩
def pI1057 : Prm := ⟨64, 32, 29, 1059, 11, 18446744073709551616, 165073487068333028, 165075686091588580⟩
theorem L1057_fin : (prmOK pL1057 1057 && ptTest pL1057 (runFrom pL1057 (fmask pL1057) (cmask pL1057) (hmask pL1057) 1 1056 (true, (init pL1057), (init pL1057))) 1057 529 false) = true := by
  decide +kernel
theorem L1057_ok : RunOK pL1057 1057 (runFrom pL1057 (fmask pL1057) (cmask pL1057) (hmask pL1057) 1 1056 (true, (init pL1057), (init pL1057))) ∧ ptTest pL1057 (runFrom pL1057 (fmask pL1057) (cmask pL1057) (hmask pL1057) 1 1056 (true, (init pL1057), (init pL1057))) 1057 529 false = true :=
  fin_run (runOK_init (prmOK_of_and L1057_fin) true) (by decide) rfl L1057_fin ptTest_fst
theorem H1057_fin : (prmOK pH1057 1057 && ptTest pH1057 (runFrom pH1057 (fmask pH1057) (cmask pH1057) (hmask pH1057) 1 1056 (true, (init pH1057), (init pH1057))) 1057 529 true) = true := by
  decide +kernel
theorem H1057_ok : RunOK pH1057 1057 (runFrom pH1057 (fmask pH1057) (cmask pH1057) (hmask pH1057) 1 1056 (true, (init pH1057), (init pH1057))) ∧ ptTest pH1057 (runFrom pH1057 (fmask pH1057) (cmask pH1057) (hmask pH1057) 1 1056 (true, (init pH1057), (init pH1057))) 1057 529 true = true :=
  fin_run (runOK_init (prmOK_of_and H1057_fin) true) (by decide) rfl H1057_fin ptTest_fst
theorem I1057_fin : (prmOK pI1057 1057 && intTest pI1057 (runFrom pI1057 (fmask pI1057) (cmask pI1057) (hmask pI1057) 1 1056 (true, (init pI1057), (init pI1057))) 1057 18 false) = true := by
  decide +kernel
theorem I1057_ok : RunOK pI1057 1057 (runFrom pI1057 (fmask pI1057) (cmask pI1057) (hmask pI1057) 1 1056 (true, (init pI1057), (init pI1057))) ∧ intTest pI1057 (runFrom pI1057 (fmask pI1057) (cmask pI1057) (hmask pI1057) 1 1056 (true, (init pI1057), (init pI1057))) 1057 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1057_fin) true) (by decide) rfl I1057_fin intTest_fst
theorem link1057 : linkOK pL1057 pH1057 pI1057 = true := by decide +kernel
theorem cvx1057 : ConvexBetweenHumps 1057 :=
  cvx_of L1057_ok H1057_ok I1057_ok link1057 (by decide)

/-! ### `N = 1058` -/

def pL1058 : Prm := ⟨77, 37, 37, 1060, 11, 18446744073709551616, 164948605162802803, 164948605162802803⟩
def pH1058 : Prm := ⟨77, 37, 37, 1060, 11, 18446744073709551616, 164950804186058355, 164950804186058355⟩
def pI1058 : Prm := ⟨64, 32, 29, 1060, 11, 18446744073709551616, 164948605162802803, 164950804186058355⟩
theorem L1058_fin : (prmOK pL1058 1058 && ptTest pL1058 (runFrom pL1058 (fmask pL1058) (cmask pL1058) (hmask pL1058) 1 1057 (true, (init pL1058), (init pL1058))) 1058 529 false) = true := by
  decide +kernel
theorem L1058_ok : RunOK pL1058 1058 (runFrom pL1058 (fmask pL1058) (cmask pL1058) (hmask pL1058) 1 1057 (true, (init pL1058), (init pL1058))) ∧ ptTest pL1058 (runFrom pL1058 (fmask pL1058) (cmask pL1058) (hmask pL1058) 1 1057 (true, (init pL1058), (init pL1058))) 1058 529 false = true :=
  fin_run (runOK_init (prmOK_of_and L1058_fin) true) (by decide) rfl L1058_fin ptTest_fst
theorem H1058_fin : (prmOK pH1058 1058 && ptTest pH1058 (runFrom pH1058 (fmask pH1058) (cmask pH1058) (hmask pH1058) 1 1057 (true, (init pH1058), (init pH1058))) 1058 529 true) = true := by
  decide +kernel
theorem H1058_ok : RunOK pH1058 1058 (runFrom pH1058 (fmask pH1058) (cmask pH1058) (hmask pH1058) 1 1057 (true, (init pH1058), (init pH1058))) ∧ ptTest pH1058 (runFrom pH1058 (fmask pH1058) (cmask pH1058) (hmask pH1058) 1 1057 (true, (init pH1058), (init pH1058))) 1058 529 true = true :=
  fin_run (runOK_init (prmOK_of_and H1058_fin) true) (by decide) rfl H1058_fin ptTest_fst
theorem I1058_fin : (prmOK pI1058 1058 && intTest pI1058 (runFrom pI1058 (fmask pI1058) (cmask pI1058) (hmask pI1058) 1 1057 (true, (init pI1058), (init pI1058))) 1058 18 true) = true := by
  decide +kernel
theorem I1058_ok : RunOK pI1058 1058 (runFrom pI1058 (fmask pI1058) (cmask pI1058) (hmask pI1058) 1 1057 (true, (init pI1058), (init pI1058))) ∧ intTest pI1058 (runFrom pI1058 (fmask pI1058) (cmask pI1058) (hmask pI1058) 1 1057 (true, (init pI1058), (init pI1058))) 1058 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1058_fin) true) (by decide) rfl I1058_fin intTest_fst
theorem link1058 : linkOK pL1058 pH1058 pI1058 = true := by decide +kernel
theorem cvx1058 : ConvexBetweenHumps 1058 :=
  cvx_of L1058_ok H1058_ok I1058_ok link1058 (by decide)
theorem cenlink1058 : cenLinkOK pI1058 1058 = true := by decide +kernel
theorem cen1058 : CenterUniqueMin 1058 ∧ DipHyp 1058 ∧ OnePointHyps 1058 :=
  cen_of L1058_ok H1058_ok I1058_ok link1058 cenlink1058

/-! ### `N = 1059` -/

def pL1059 : Prm := ⟨77, 37, 37, 1061, 11, 18446744073709551616, 164823832544196186, 164823832544196186⟩
def pH1059 : Prm := ⟨77, 37, 37, 1061, 11, 18446744073709551616, 164826031567451738, 164826031567451738⟩
def pI1059 : Prm := ⟨64, 32, 29, 1061, 11, 18446744073709551616, 164823832544196186, 164826031567451738⟩
theorem L1059_fin : (prmOK pL1059 1059 && ptTest pL1059 (runFrom pL1059 (fmask pL1059) (cmask pL1059) (hmask pL1059) 1 1058 (true, (init pL1059), (init pL1059))) 1059 530 false) = true := by
  decide +kernel
theorem L1059_ok : RunOK pL1059 1059 (runFrom pL1059 (fmask pL1059) (cmask pL1059) (hmask pL1059) 1 1058 (true, (init pL1059), (init pL1059))) ∧ ptTest pL1059 (runFrom pL1059 (fmask pL1059) (cmask pL1059) (hmask pL1059) 1 1058 (true, (init pL1059), (init pL1059))) 1059 530 false = true :=
  fin_run (runOK_init (prmOK_of_and L1059_fin) true) (by decide) rfl L1059_fin ptTest_fst
theorem H1059_fin : (prmOK pH1059 1059 && ptTest pH1059 (runFrom pH1059 (fmask pH1059) (cmask pH1059) (hmask pH1059) 1 1058 (true, (init pH1059), (init pH1059))) 1059 530 true) = true := by
  decide +kernel
theorem H1059_ok : RunOK pH1059 1059 (runFrom pH1059 (fmask pH1059) (cmask pH1059) (hmask pH1059) 1 1058 (true, (init pH1059), (init pH1059))) ∧ ptTest pH1059 (runFrom pH1059 (fmask pH1059) (cmask pH1059) (hmask pH1059) 1 1058 (true, (init pH1059), (init pH1059))) 1059 530 true = true :=
  fin_run (runOK_init (prmOK_of_and H1059_fin) true) (by decide) rfl H1059_fin ptTest_fst
theorem I1059_fin : (prmOK pI1059 1059 && intTest pI1059 (runFrom pI1059 (fmask pI1059) (cmask pI1059) (hmask pI1059) 1 1058 (true, (init pI1059), (init pI1059))) 1059 18 false) = true := by
  decide +kernel
theorem I1059_ok : RunOK pI1059 1059 (runFrom pI1059 (fmask pI1059) (cmask pI1059) (hmask pI1059) 1 1058 (true, (init pI1059), (init pI1059))) ∧ intTest pI1059 (runFrom pI1059 (fmask pI1059) (cmask pI1059) (hmask pI1059) 1 1058 (true, (init pI1059), (init pI1059))) 1059 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1059_fin) true) (by decide) rfl I1059_fin intTest_fst
theorem link1059 : linkOK pL1059 pH1059 pI1059 = true := by decide +kernel
theorem cvx1059 : ConvexBetweenHumps 1059 :=
  cvx_of L1059_ok H1059_ok I1059_ok link1059 (by decide)

/-! ### `N = 1060` -/

def pL1060 : Prm := ⟨77, 37, 37, 1062, 11, 18446744073709551616, 164699363020038500, 164699363020038500⟩
def pH1060 : Prm := ⟨77, 37, 37, 1062, 11, 18446744073709551616, 164701562043294052, 164701562043294052⟩
def pI1060 : Prm := ⟨64, 32, 29, 1062, 11, 18446744073709551616, 164699363020038500, 164701562043294052⟩
theorem L1060_fin : (prmOK pL1060 1060 && ptTest pL1060 (runFrom pL1060 (fmask pL1060) (cmask pL1060) (hmask pL1060) 1 1059 (true, (init pL1060), (init pL1060))) 1060 530 false) = true := by
  decide +kernel
theorem L1060_ok : RunOK pL1060 1060 (runFrom pL1060 (fmask pL1060) (cmask pL1060) (hmask pL1060) 1 1059 (true, (init pL1060), (init pL1060))) ∧ ptTest pL1060 (runFrom pL1060 (fmask pL1060) (cmask pL1060) (hmask pL1060) 1 1059 (true, (init pL1060), (init pL1060))) 1060 530 false = true :=
  fin_run (runOK_init (prmOK_of_and L1060_fin) true) (by decide) rfl L1060_fin ptTest_fst
theorem H1060_fin : (prmOK pH1060 1060 && ptTest pH1060 (runFrom pH1060 (fmask pH1060) (cmask pH1060) (hmask pH1060) 1 1059 (true, (init pH1060), (init pH1060))) 1060 530 true) = true := by
  decide +kernel
theorem H1060_ok : RunOK pH1060 1060 (runFrom pH1060 (fmask pH1060) (cmask pH1060) (hmask pH1060) 1 1059 (true, (init pH1060), (init pH1060))) ∧ ptTest pH1060 (runFrom pH1060 (fmask pH1060) (cmask pH1060) (hmask pH1060) 1 1059 (true, (init pH1060), (init pH1060))) 1060 530 true = true :=
  fin_run (runOK_init (prmOK_of_and H1060_fin) true) (by decide) rfl H1060_fin ptTest_fst
theorem I1060_fin : (prmOK pI1060 1060 && intTest pI1060 (runFrom pI1060 (fmask pI1060) (cmask pI1060) (hmask pI1060) 1 1059 (true, (init pI1060), (init pI1060))) 1060 18 true) = true := by
  decide +kernel
theorem I1060_ok : RunOK pI1060 1060 (runFrom pI1060 (fmask pI1060) (cmask pI1060) (hmask pI1060) 1 1059 (true, (init pI1060), (init pI1060))) ∧ intTest pI1060 (runFrom pI1060 (fmask pI1060) (cmask pI1060) (hmask pI1060) 1 1059 (true, (init pI1060), (init pI1060))) 1060 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1060_fin) true) (by decide) rfl I1060_fin intTest_fst
theorem link1060 : linkOK pL1060 pH1060 pI1060 = true := by decide +kernel
theorem cvx1060 : ConvexBetweenHumps 1060 :=
  cvx_of L1060_ok H1060_ok I1060_ok link1060 (by decide)
theorem cenlink1060 : cenLinkOK pI1060 1060 = true := by decide +kernel
theorem cen1060 : CenterUniqueMin 1060 ∧ DipHyp 1060 ∧ OnePointHyps 1060 :=
  cen_of L1060_ok H1060_ok I1060_ok link1060 cenlink1060

/-! ### `N = 1061` -/

def pL1061 : Prm := ⟨77, 37, 37, 1063, 11, 18446744073709551616, 164575002285111266, 164575002285111266⟩
def pH1061 : Prm := ⟨77, 37, 37, 1063, 11, 18446744073709551616, 164577201308366818, 164577201308366818⟩
def pI1061 : Prm := ⟨64, 32, 29, 1063, 11, 18446744073709551616, 164575002285111266, 164577201308366818⟩
theorem L1061_fin : (prmOK pL1061 1061 && ptTest pL1061 (runFrom pL1061 (fmask pL1061) (cmask pL1061) (hmask pL1061) 1 1060 (true, (init pL1061), (init pL1061))) 1061 531 false) = true := by
  decide +kernel
theorem L1061_ok : RunOK pL1061 1061 (runFrom pL1061 (fmask pL1061) (cmask pL1061) (hmask pL1061) 1 1060 (true, (init pL1061), (init pL1061))) ∧ ptTest pL1061 (runFrom pL1061 (fmask pL1061) (cmask pL1061) (hmask pL1061) 1 1060 (true, (init pL1061), (init pL1061))) 1061 531 false = true :=
  fin_run (runOK_init (prmOK_of_and L1061_fin) true) (by decide) rfl L1061_fin ptTest_fst
theorem H1061_fin : (prmOK pH1061 1061 && ptTest pH1061 (runFrom pH1061 (fmask pH1061) (cmask pH1061) (hmask pH1061) 1 1060 (true, (init pH1061), (init pH1061))) 1061 531 true) = true := by
  decide +kernel
theorem H1061_ok : RunOK pH1061 1061 (runFrom pH1061 (fmask pH1061) (cmask pH1061) (hmask pH1061) 1 1060 (true, (init pH1061), (init pH1061))) ∧ ptTest pH1061 (runFrom pH1061 (fmask pH1061) (cmask pH1061) (hmask pH1061) 1 1060 (true, (init pH1061), (init pH1061))) 1061 531 true = true :=
  fin_run (runOK_init (prmOK_of_and H1061_fin) true) (by decide) rfl H1061_fin ptTest_fst
theorem I1061_fin : (prmOK pI1061 1061 && intTest pI1061 (runFrom pI1061 (fmask pI1061) (cmask pI1061) (hmask pI1061) 1 1060 (true, (init pI1061), (init pI1061))) 1061 18 false) = true := by
  decide +kernel
theorem I1061_ok : RunOK pI1061 1061 (runFrom pI1061 (fmask pI1061) (cmask pI1061) (hmask pI1061) 1 1060 (true, (init pI1061), (init pI1061))) ∧ intTest pI1061 (runFrom pI1061 (fmask pI1061) (cmask pI1061) (hmask pI1061) 1 1060 (true, (init pI1061), (init pI1061))) 1061 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1061_fin) true) (by decide) rfl I1061_fin intTest_fst
theorem link1061 : linkOK pL1061 pH1061 pI1061 = true := by decide +kernel
theorem cvx1061 : ConvexBetweenHumps 1061 :=
  cvx_of L1061_ok H1061_ok I1061_ok link1061 (by decide)

/-! ### `N = 1062` -/

def pL1062 : Prm := ⟨77, 37, 37, 1064, 11, 18446744073709551616, 164450943033715699, 164450943033715699⟩
def pH1062 : Prm := ⟨77, 37, 37, 1064, 11, 18446744073709551616, 164453142056971251, 164453142056971251⟩
def pI1062 : Prm := ⟨64, 32, 29, 1064, 11, 18446744073709551616, 164450943033715699, 164453142056971251⟩
theorem L1062_fin : (prmOK pL1062 1062 && ptTest pL1062 (runFrom pL1062 (fmask pL1062) (cmask pL1062) (hmask pL1062) 1 1061 (true, (init pL1062), (init pL1062))) 1062 531 false) = true := by
  decide +kernel
theorem L1062_ok : RunOK pL1062 1062 (runFrom pL1062 (fmask pL1062) (cmask pL1062) (hmask pL1062) 1 1061 (true, (init pL1062), (init pL1062))) ∧ ptTest pL1062 (runFrom pL1062 (fmask pL1062) (cmask pL1062) (hmask pL1062) 1 1061 (true, (init pL1062), (init pL1062))) 1062 531 false = true :=
  fin_run (runOK_init (prmOK_of_and L1062_fin) true) (by decide) rfl L1062_fin ptTest_fst
theorem H1062_fin : (prmOK pH1062 1062 && ptTest pH1062 (runFrom pH1062 (fmask pH1062) (cmask pH1062) (hmask pH1062) 1 1061 (true, (init pH1062), (init pH1062))) 1062 531 true) = true := by
  decide +kernel
theorem H1062_ok : RunOK pH1062 1062 (runFrom pH1062 (fmask pH1062) (cmask pH1062) (hmask pH1062) 1 1061 (true, (init pH1062), (init pH1062))) ∧ ptTest pH1062 (runFrom pH1062 (fmask pH1062) (cmask pH1062) (hmask pH1062) 1 1061 (true, (init pH1062), (init pH1062))) 1062 531 true = true :=
  fin_run (runOK_init (prmOK_of_and H1062_fin) true) (by decide) rfl H1062_fin ptTest_fst
theorem I1062_fin : (prmOK pI1062 1062 && intTest pI1062 (runFrom pI1062 (fmask pI1062) (cmask pI1062) (hmask pI1062) 1 1061 (true, (init pI1062), (init pI1062))) 1062 18 true) = true := by
  decide +kernel
theorem I1062_ok : RunOK pI1062 1062 (runFrom pI1062 (fmask pI1062) (cmask pI1062) (hmask pI1062) 1 1061 (true, (init pI1062), (init pI1062))) ∧ intTest pI1062 (runFrom pI1062 (fmask pI1062) (cmask pI1062) (hmask pI1062) 1 1061 (true, (init pI1062), (init pI1062))) 1062 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1062_fin) true) (by decide) rfl I1062_fin intTest_fst
theorem link1062 : linkOK pL1062 pH1062 pI1062 = true := by decide +kernel
theorem cvx1062 : ConvexBetweenHumps 1062 :=
  cvx_of L1062_ok H1062_ok I1062_ok link1062 (by decide)
theorem cenlink1062 : cenLinkOK pI1062 1062 = true := by decide +kernel
theorem cen1062 : CenterUniqueMin 1062 ∧ DipHyp 1062 ∧ OnePointHyps 1062 :=
  cen_of L1062_ok H1062_ok I1062_ok link1062 cenlink1062

/-! ### `N = 1063` -/

def pL1063 : Prm := ⟨77, 37, 37, 1065, 11, 18446744073709551616, 164326992076938035, 164326992076938035⟩
def pH1063 : Prm := ⟨77, 37, 37, 1065, 11, 18446744073709551616, 164329191100193587, 164329191100193587⟩
def pI1063 : Prm := ⟨64, 32, 29, 1065, 11, 18446744073709551616, 164326992076938035, 164329191100193587⟩
theorem L1063_fin : (prmOK pL1063 1063 && ptTest pL1063 (runFrom pL1063 (fmask pL1063) (cmask pL1063) (hmask pL1063) 1 1062 (true, (init pL1063), (init pL1063))) 1063 532 false) = true := by
  decide +kernel
theorem L1063_ok : RunOK pL1063 1063 (runFrom pL1063 (fmask pL1063) (cmask pL1063) (hmask pL1063) 1 1062 (true, (init pL1063), (init pL1063))) ∧ ptTest pL1063 (runFrom pL1063 (fmask pL1063) (cmask pL1063) (hmask pL1063) 1 1062 (true, (init pL1063), (init pL1063))) 1063 532 false = true :=
  fin_run (runOK_init (prmOK_of_and L1063_fin) true) (by decide) rfl L1063_fin ptTest_fst
theorem H1063_fin : (prmOK pH1063 1063 && ptTest pH1063 (runFrom pH1063 (fmask pH1063) (cmask pH1063) (hmask pH1063) 1 1062 (true, (init pH1063), (init pH1063))) 1063 532 true) = true := by
  decide +kernel
theorem H1063_ok : RunOK pH1063 1063 (runFrom pH1063 (fmask pH1063) (cmask pH1063) (hmask pH1063) 1 1062 (true, (init pH1063), (init pH1063))) ∧ ptTest pH1063 (runFrom pH1063 (fmask pH1063) (cmask pH1063) (hmask pH1063) 1 1062 (true, (init pH1063), (init pH1063))) 1063 532 true = true :=
  fin_run (runOK_init (prmOK_of_and H1063_fin) true) (by decide) rfl H1063_fin ptTest_fst
theorem I1063_fin : (prmOK pI1063 1063 && intTest pI1063 (runFrom pI1063 (fmask pI1063) (cmask pI1063) (hmask pI1063) 1 1062 (true, (init pI1063), (init pI1063))) 1063 18 false) = true := by
  decide +kernel
theorem I1063_ok : RunOK pI1063 1063 (runFrom pI1063 (fmask pI1063) (cmask pI1063) (hmask pI1063) 1 1062 (true, (init pI1063), (init pI1063))) ∧ intTest pI1063 (runFrom pI1063 (fmask pI1063) (cmask pI1063) (hmask pI1063) 1 1062 (true, (init pI1063), (init pI1063))) 1063 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1063_fin) true) (by decide) rfl I1063_fin intTest_fst
theorem link1063 : linkOK pL1063 pH1063 pI1063 = true := by decide +kernel
theorem cvx1063 : ConvexBetweenHumps 1063 :=
  cvx_of L1063_ok H1063_ok I1063_ok link1063 (by decide)

/-! ### `N = 1064` -/

def pL1064 : Prm := ⟨77, 37, 37, 1066, 11, 18446744073709551616, 164203341004322432, 164203341004322432⟩
def pH1064 : Prm := ⟨77, 37, 37, 1066, 11, 18446744073709551616, 164205540027577984, 164205540027577984⟩
def pI1064 : Prm := ⟨64, 32, 29, 1066, 11, 18446744073709551616, 164203341004322432, 164205540027577984⟩
theorem L1064_fin : (prmOK pL1064 1064 && ptTest pL1064 (runFrom pL1064 (fmask pL1064) (cmask pL1064) (hmask pL1064) 1 1063 (true, (init pL1064), (init pL1064))) 1064 532 false) = true := by
  decide +kernel
theorem L1064_ok : RunOK pL1064 1064 (runFrom pL1064 (fmask pL1064) (cmask pL1064) (hmask pL1064) 1 1063 (true, (init pL1064), (init pL1064))) ∧ ptTest pL1064 (runFrom pL1064 (fmask pL1064) (cmask pL1064) (hmask pL1064) 1 1063 (true, (init pL1064), (init pL1064))) 1064 532 false = true :=
  fin_run (runOK_init (prmOK_of_and L1064_fin) true) (by decide) rfl L1064_fin ptTest_fst
theorem H1064_fin : (prmOK pH1064 1064 && ptTest pH1064 (runFrom pH1064 (fmask pH1064) (cmask pH1064) (hmask pH1064) 1 1063 (true, (init pH1064), (init pH1064))) 1064 532 true) = true := by
  decide +kernel
theorem H1064_ok : RunOK pH1064 1064 (runFrom pH1064 (fmask pH1064) (cmask pH1064) (hmask pH1064) 1 1063 (true, (init pH1064), (init pH1064))) ∧ ptTest pH1064 (runFrom pH1064 (fmask pH1064) (cmask pH1064) (hmask pH1064) 1 1063 (true, (init pH1064), (init pH1064))) 1064 532 true = true :=
  fin_run (runOK_init (prmOK_of_and H1064_fin) true) (by decide) rfl H1064_fin ptTest_fst
theorem I1064_fin : (prmOK pI1064 1064 && intTest pI1064 (runFrom pI1064 (fmask pI1064) (cmask pI1064) (hmask pI1064) 1 1063 (true, (init pI1064), (init pI1064))) 1064 18 true) = true := by
  decide +kernel
theorem I1064_ok : RunOK pI1064 1064 (runFrom pI1064 (fmask pI1064) (cmask pI1064) (hmask pI1064) 1 1063 (true, (init pI1064), (init pI1064))) ∧ intTest pI1064 (runFrom pI1064 (fmask pI1064) (cmask pI1064) (hmask pI1064) 1 1063 (true, (init pI1064), (init pI1064))) 1064 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1064_fin) true) (by decide) rfl I1064_fin intTest_fst
theorem link1064 : linkOK pL1064 pH1064 pI1064 = true := by decide +kernel
theorem cvx1064 : ConvexBetweenHumps 1064 :=
  cvx_of L1064_ok H1064_ok I1064_ok link1064 (by decide)
theorem cenlink1064 : cenLinkOK pI1064 1064 = true := by decide +kernel
theorem cen1064 : CenterUniqueMin 1064 ∧ DipHyp 1064 ∧ OnePointHyps 1064 :=
  cen_of L1064_ok H1064_ok I1064_ok link1064 cenlink1064

/-! ### `N = 1065` -/

def pL1065 : Prm := ⟨77, 37, 37, 1067, 11, 18446744073709551616, 164079797734755896, 164079797734755896⟩
def pH1065 : Prm := ⟨77, 37, 37, 1067, 11, 18446744073709551616, 164081996758011448, 164081996758011448⟩
def pI1065 : Prm := ⟨64, 32, 29, 1067, 11, 18446744073709551616, 164079797734755896, 164081996758011448⟩
theorem L1065_fin : (prmOK pL1065 1065 && ptTest pL1065 (runFrom pL1065 (fmask pL1065) (cmask pL1065) (hmask pL1065) 1 1064 (true, (init pL1065), (init pL1065))) 1065 533 false) = true := by
  decide +kernel
theorem L1065_ok : RunOK pL1065 1065 (runFrom pL1065 (fmask pL1065) (cmask pL1065) (hmask pL1065) 1 1064 (true, (init pL1065), (init pL1065))) ∧ ptTest pL1065 (runFrom pL1065 (fmask pL1065) (cmask pL1065) (hmask pL1065) 1 1064 (true, (init pL1065), (init pL1065))) 1065 533 false = true :=
  fin_run (runOK_init (prmOK_of_and L1065_fin) true) (by decide) rfl L1065_fin ptTest_fst
theorem H1065_fin : (prmOK pH1065 1065 && ptTest pH1065 (runFrom pH1065 (fmask pH1065) (cmask pH1065) (hmask pH1065) 1 1064 (true, (init pH1065), (init pH1065))) 1065 533 true) = true := by
  decide +kernel
theorem H1065_ok : RunOK pH1065 1065 (runFrom pH1065 (fmask pH1065) (cmask pH1065) (hmask pH1065) 1 1064 (true, (init pH1065), (init pH1065))) ∧ ptTest pH1065 (runFrom pH1065 (fmask pH1065) (cmask pH1065) (hmask pH1065) 1 1064 (true, (init pH1065), (init pH1065))) 1065 533 true = true :=
  fin_run (runOK_init (prmOK_of_and H1065_fin) true) (by decide) rfl H1065_fin ptTest_fst
theorem I1065_fin : (prmOK pI1065 1065 && intTest pI1065 (runFrom pI1065 (fmask pI1065) (cmask pI1065) (hmask pI1065) 1 1064 (true, (init pI1065), (init pI1065))) 1065 18 false) = true := by
  decide +kernel
theorem I1065_ok : RunOK pI1065 1065 (runFrom pI1065 (fmask pI1065) (cmask pI1065) (hmask pI1065) 1 1064 (true, (init pI1065), (init pI1065))) ∧ intTest pI1065 (runFrom pI1065 (fmask pI1065) (cmask pI1065) (hmask pI1065) 1 1064 (true, (init pI1065), (init pI1065))) 1065 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1065_fin) true) (by decide) rfl I1065_fin intTest_fst
theorem link1065 : linkOK pL1065 pH1065 pI1065 = true := by decide +kernel
theorem cvx1065 : ConvexBetweenHumps 1065 :=
  cvx_of L1065_ok H1065_ok I1065_ok link1065 (by decide)

/-! ### `N = 1066` -/

def pL1066 : Prm := ⟨77, 37, 37, 1068, 11, 18446744073709551616, 163956552761418798, 163956552761418798⟩
def pH1066 : Prm := ⟨77, 37, 37, 1068, 11, 18446744073709551616, 163958751784674350, 163958751784674350⟩
def pI1066 : Prm := ⟨64, 32, 29, 1068, 11, 18446744073709551616, 163956552761418798, 163958751784674350⟩
theorem L1066_fin : (prmOK pL1066 1066 && ptTest pL1066 (runFrom pL1066 (fmask pL1066) (cmask pL1066) (hmask pL1066) 1 1065 (true, (init pL1066), (init pL1066))) 1066 533 false) = true := by
  decide +kernel
theorem L1066_ok : RunOK pL1066 1066 (runFrom pL1066 (fmask pL1066) (cmask pL1066) (hmask pL1066) 1 1065 (true, (init pL1066), (init pL1066))) ∧ ptTest pL1066 (runFrom pL1066 (fmask pL1066) (cmask pL1066) (hmask pL1066) 1 1065 (true, (init pL1066), (init pL1066))) 1066 533 false = true :=
  fin_run (runOK_init (prmOK_of_and L1066_fin) true) (by decide) rfl L1066_fin ptTest_fst
theorem H1066_fin : (prmOK pH1066 1066 && ptTest pH1066 (runFrom pH1066 (fmask pH1066) (cmask pH1066) (hmask pH1066) 1 1065 (true, (init pH1066), (init pH1066))) 1066 533 true) = true := by
  decide +kernel
theorem H1066_ok : RunOK pH1066 1066 (runFrom pH1066 (fmask pH1066) (cmask pH1066) (hmask pH1066) 1 1065 (true, (init pH1066), (init pH1066))) ∧ ptTest pH1066 (runFrom pH1066 (fmask pH1066) (cmask pH1066) (hmask pH1066) 1 1065 (true, (init pH1066), (init pH1066))) 1066 533 true = true :=
  fin_run (runOK_init (prmOK_of_and H1066_fin) true) (by decide) rfl H1066_fin ptTest_fst
theorem I1066_fin : (prmOK pI1066 1066 && intTest pI1066 (runFrom pI1066 (fmask pI1066) (cmask pI1066) (hmask pI1066) 1 1065 (true, (init pI1066), (init pI1066))) 1066 18 true) = true := by
  decide +kernel
theorem I1066_ok : RunOK pI1066 1066 (runFrom pI1066 (fmask pI1066) (cmask pI1066) (hmask pI1066) 1 1065 (true, (init pI1066), (init pI1066))) ∧ intTest pI1066 (runFrom pI1066 (fmask pI1066) (cmask pI1066) (hmask pI1066) 1 1065 (true, (init pI1066), (init pI1066))) 1066 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1066_fin) true) (by decide) rfl I1066_fin intTest_fst
theorem link1066 : linkOK pL1066 pH1066 pI1066 = true := by decide +kernel
theorem cvx1066 : ConvexBetweenHumps 1066 :=
  cvx_of L1066_ok H1066_ok I1066_ok link1066 (by decide)
theorem cenlink1066 : cenLinkOK pI1066 1066 = true := by decide +kernel
theorem cen1066 : CenterUniqueMin 1066 ∧ DipHyp 1066 ∧ OnePointHyps 1066 :=
  cen_of L1066_ok H1066_ok I1066_ok link1066 cenlink1066

/-! ### `N = 1067` -/

def pL1067 : Prm := ⟨77, 37, 37, 1069, 11, 18446744073709551616, 163833415102568751, 163833415102568751⟩
def pH1067 : Prm := ⟨77, 37, 37, 1069, 11, 18446744073709551616, 163835614125824303, 163835614125824303⟩
def pI1067 : Prm := ⟨64, 32, 29, 1069, 11, 18446744073709551616, 163833415102568751, 163835614125824303⟩
theorem L1067_fin : (prmOK pL1067 1067 && ptTest pL1067 (runFrom pL1067 (fmask pL1067) (cmask pL1067) (hmask pL1067) 1 1066 (true, (init pL1067), (init pL1067))) 1067 534 false) = true := by
  decide +kernel
theorem L1067_ok : RunOK pL1067 1067 (runFrom pL1067 (fmask pL1067) (cmask pL1067) (hmask pL1067) 1 1066 (true, (init pL1067), (init pL1067))) ∧ ptTest pL1067 (runFrom pL1067 (fmask pL1067) (cmask pL1067) (hmask pL1067) 1 1066 (true, (init pL1067), (init pL1067))) 1067 534 false = true :=
  fin_run (runOK_init (prmOK_of_and L1067_fin) true) (by decide) rfl L1067_fin ptTest_fst
theorem H1067_fin : (prmOK pH1067 1067 && ptTest pH1067 (runFrom pH1067 (fmask pH1067) (cmask pH1067) (hmask pH1067) 1 1066 (true, (init pH1067), (init pH1067))) 1067 534 true) = true := by
  decide +kernel
theorem H1067_ok : RunOK pH1067 1067 (runFrom pH1067 (fmask pH1067) (cmask pH1067) (hmask pH1067) 1 1066 (true, (init pH1067), (init pH1067))) ∧ ptTest pH1067 (runFrom pH1067 (fmask pH1067) (cmask pH1067) (hmask pH1067) 1 1066 (true, (init pH1067), (init pH1067))) 1067 534 true = true :=
  fin_run (runOK_init (prmOK_of_and H1067_fin) true) (by decide) rfl H1067_fin ptTest_fst
theorem I1067_fin : (prmOK pI1067 1067 && intTest pI1067 (runFrom pI1067 (fmask pI1067) (cmask pI1067) (hmask pI1067) 1 1066 (true, (init pI1067), (init pI1067))) 1067 18 false) = true := by
  decide +kernel
theorem I1067_ok : RunOK pI1067 1067 (runFrom pI1067 (fmask pI1067) (cmask pI1067) (hmask pI1067) 1 1066 (true, (init pI1067), (init pI1067))) ∧ intTest pI1067 (runFrom pI1067 (fmask pI1067) (cmask pI1067) (hmask pI1067) 1 1066 (true, (init pI1067), (init pI1067))) 1067 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1067_fin) true) (by decide) rfl I1067_fin intTest_fst
theorem link1067 : linkOK pL1067 pH1067 pI1067 = true := by decide +kernel
theorem cvx1067 : ConvexBetweenHumps 1067 :=
  cvx_of L1067_ok H1067_ok I1067_ok link1067 (by decide)

/-! ### `N = 1068` -/

def pL1068 : Prm := ⟨77, 37, 37, 1070, 11, 18446744073709551616, 163710574163360265, 163710574163360265⟩
def pH1068 : Prm := ⟨77, 37, 37, 1070, 11, 18446744073709551616, 163712773186615817, 163712773186615817⟩
def pI1068 : Prm := ⟨64, 32, 29, 1070, 11, 18446744073709551616, 163710574163360265, 163712773186615817⟩
theorem L1068_fin : (prmOK pL1068 1068 && ptTest pL1068 (runFrom pL1068 (fmask pL1068) (cmask pL1068) (hmask pL1068) 1 1067 (true, (init pL1068), (init pL1068))) 1068 534 false) = true := by
  decide +kernel
theorem L1068_ok : RunOK pL1068 1068 (runFrom pL1068 (fmask pL1068) (cmask pL1068) (hmask pL1068) 1 1067 (true, (init pL1068), (init pL1068))) ∧ ptTest pL1068 (runFrom pL1068 (fmask pL1068) (cmask pL1068) (hmask pL1068) 1 1067 (true, (init pL1068), (init pL1068))) 1068 534 false = true :=
  fin_run (runOK_init (prmOK_of_and L1068_fin) true) (by decide) rfl L1068_fin ptTest_fst
theorem H1068_fin : (prmOK pH1068 1068 && ptTest pH1068 (runFrom pH1068 (fmask pH1068) (cmask pH1068) (hmask pH1068) 1 1067 (true, (init pH1068), (init pH1068))) 1068 534 true) = true := by
  decide +kernel
theorem H1068_ok : RunOK pH1068 1068 (runFrom pH1068 (fmask pH1068) (cmask pH1068) (hmask pH1068) 1 1067 (true, (init pH1068), (init pH1068))) ∧ ptTest pH1068 (runFrom pH1068 (fmask pH1068) (cmask pH1068) (hmask pH1068) 1 1067 (true, (init pH1068), (init pH1068))) 1068 534 true = true :=
  fin_run (runOK_init (prmOK_of_and H1068_fin) true) (by decide) rfl H1068_fin ptTest_fst
theorem I1068_fin : (prmOK pI1068 1068 && intTest pI1068 (runFrom pI1068 (fmask pI1068) (cmask pI1068) (hmask pI1068) 1 1067 (true, (init pI1068), (init pI1068))) 1068 18 true) = true := by
  decide +kernel
theorem I1068_ok : RunOK pI1068 1068 (runFrom pI1068 (fmask pI1068) (cmask pI1068) (hmask pI1068) 1 1067 (true, (init pI1068), (init pI1068))) ∧ intTest pI1068 (runFrom pI1068 (fmask pI1068) (cmask pI1068) (hmask pI1068) 1 1067 (true, (init pI1068), (init pI1068))) 1068 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1068_fin) true) (by decide) rfl I1068_fin intTest_fst
theorem link1068 : linkOK pL1068 pH1068 pI1068 = true := by decide +kernel
theorem cvx1068 : ConvexBetweenHumps 1068 :=
  cvx_of L1068_ok H1068_ok I1068_ok link1068 (by decide)
theorem cenlink1068 : cenLinkOK pI1068 1068 = true := by decide +kernel
theorem cen1068 : CenterUniqueMin 1068 ∧ DipHyp 1068 ∧ OnePointHyps 1068 :=
  cen_of L1068_ok H1068_ok I1068_ok link1068 cenlink1068

/-! ### `N = 1069` -/

def pL1069 : Prm := ⟨77, 37, 37, 1071, 11, 18446744073709551616, 163587840053083633, 163587840053083633⟩
def pH1069 : Prm := ⟨77, 37, 37, 1071, 11, 18446744073709551616, 163590039076339185, 163590039076339185⟩
def pI1069 : Prm := ⟨64, 32, 29, 1071, 11, 18446744073709551616, 163587840053083633, 163590039076339185⟩
theorem L1069_fin : (prmOK pL1069 1069 && ptTest pL1069 (runFrom pL1069 (fmask pL1069) (cmask pL1069) (hmask pL1069) 1 1068 (true, (init pL1069), (init pL1069))) 1069 535 false) = true := by
  decide +kernel
theorem L1069_ok : RunOK pL1069 1069 (runFrom pL1069 (fmask pL1069) (cmask pL1069) (hmask pL1069) 1 1068 (true, (init pL1069), (init pL1069))) ∧ ptTest pL1069 (runFrom pL1069 (fmask pL1069) (cmask pL1069) (hmask pL1069) 1 1068 (true, (init pL1069), (init pL1069))) 1069 535 false = true :=
  fin_run (runOK_init (prmOK_of_and L1069_fin) true) (by decide) rfl L1069_fin ptTest_fst
theorem H1069_fin : (prmOK pH1069 1069 && ptTest pH1069 (runFrom pH1069 (fmask pH1069) (cmask pH1069) (hmask pH1069) 1 1068 (true, (init pH1069), (init pH1069))) 1069 535 true) = true := by
  decide +kernel
theorem H1069_ok : RunOK pH1069 1069 (runFrom pH1069 (fmask pH1069) (cmask pH1069) (hmask pH1069) 1 1068 (true, (init pH1069), (init pH1069))) ∧ ptTest pH1069 (runFrom pH1069 (fmask pH1069) (cmask pH1069) (hmask pH1069) 1 1068 (true, (init pH1069), (init pH1069))) 1069 535 true = true :=
  fin_run (runOK_init (prmOK_of_and H1069_fin) true) (by decide) rfl H1069_fin ptTest_fst
theorem I1069_fin : (prmOK pI1069 1069 && intTest pI1069 (runFrom pI1069 (fmask pI1069) (cmask pI1069) (hmask pI1069) 1 1068 (true, (init pI1069), (init pI1069))) 1069 18 false) = true := by
  decide +kernel
theorem I1069_ok : RunOK pI1069 1069 (runFrom pI1069 (fmask pI1069) (cmask pI1069) (hmask pI1069) 1 1068 (true, (init pI1069), (init pI1069))) ∧ intTest pI1069 (runFrom pI1069 (fmask pI1069) (cmask pI1069) (hmask pI1069) 1 1068 (true, (init pI1069), (init pI1069))) 1069 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1069_fin) true) (by decide) rfl I1069_fin intTest_fst
theorem link1069 : linkOK pL1069 pH1069 pI1069 = true := by decide +kernel
theorem cvx1069 : ConvexBetweenHumps 1069 :=
  cvx_of L1069_ok H1069_ok I1069_ok link1069 (by decide)

/-! ### `N = 1070` -/

def pL1070 : Prm := ⟨77, 37, 37, 1072, 11, 18446744073709551616, 163465401097094753, 163465401097094753⟩
def pH1070 : Prm := ⟨77, 37, 37, 1072, 11, 18446744073709551616, 163467600120350305, 163467600120350305⟩
def pI1070 : Prm := ⟨64, 32, 29, 1072, 11, 18446744073709551616, 163465401097094753, 163467600120350305⟩
theorem L1070_fin : (prmOK pL1070 1070 && ptTest pL1070 (runFrom pL1070 (fmask pL1070) (cmask pL1070) (hmask pL1070) 1 1069 (true, (init pL1070), (init pL1070))) 1070 535 false) = true := by
  decide +kernel
theorem L1070_ok : RunOK pL1070 1070 (runFrom pL1070 (fmask pL1070) (cmask pL1070) (hmask pL1070) 1 1069 (true, (init pL1070), (init pL1070))) ∧ ptTest pL1070 (runFrom pL1070 (fmask pL1070) (cmask pL1070) (hmask pL1070) 1 1069 (true, (init pL1070), (init pL1070))) 1070 535 false = true :=
  fin_run (runOK_init (prmOK_of_and L1070_fin) true) (by decide) rfl L1070_fin ptTest_fst
theorem H1070_fin : (prmOK pH1070 1070 && ptTest pH1070 (runFrom pH1070 (fmask pH1070) (cmask pH1070) (hmask pH1070) 1 1069 (true, (init pH1070), (init pH1070))) 1070 535 true) = true := by
  decide +kernel
theorem H1070_ok : RunOK pH1070 1070 (runFrom pH1070 (fmask pH1070) (cmask pH1070) (hmask pH1070) 1 1069 (true, (init pH1070), (init pH1070))) ∧ ptTest pH1070 (runFrom pH1070 (fmask pH1070) (cmask pH1070) (hmask pH1070) 1 1069 (true, (init pH1070), (init pH1070))) 1070 535 true = true :=
  fin_run (runOK_init (prmOK_of_and H1070_fin) true) (by decide) rfl H1070_fin ptTest_fst
theorem I1070_fin : (prmOK pI1070 1070 && intTest pI1070 (runFrom pI1070 (fmask pI1070) (cmask pI1070) (hmask pI1070) 1 1069 (true, (init pI1070), (init pI1070))) 1070 18 true) = true := by
  decide +kernel
theorem I1070_ok : RunOK pI1070 1070 (runFrom pI1070 (fmask pI1070) (cmask pI1070) (hmask pI1070) 1 1069 (true, (init pI1070), (init pI1070))) ∧ intTest pI1070 (runFrom pI1070 (fmask pI1070) (cmask pI1070) (hmask pI1070) 1 1069 (true, (init pI1070), (init pI1070))) 1070 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1070_fin) true) (by decide) rfl I1070_fin intTest_fst
theorem link1070 : linkOK pL1070 pH1070 pI1070 = true := by decide +kernel
theorem cvx1070 : ConvexBetweenHumps 1070 :=
  cvx_of L1070_ok H1070_ok I1070_ok link1070 (by decide)
theorem cenlink1070 : cenLinkOK pI1070 1070 = true := by decide +kernel
theorem cen1070 : CenterUniqueMin 1070 ∧ DipHyp 1070 ∧ OnePointHyps 1070 :=
  cen_of L1070_ok H1070_ok I1070_ok link1070 cenlink1070

/-! ### `N = 1071` -/

def pL1071 : Prm := ⟨77, 37, 37, 1073, 11, 18446744073709551616, 163343068487452456, 163343068487452456⟩
def pH1071 : Prm := ⟨77, 37, 37, 1073, 11, 18446744073709551616, 163345267510708008, 163345267510708008⟩
def pI1071 : Prm := ⟨65, 32, 30, 1073, 11, 18446744073709551616, 163343068487452456, 163345267510708008⟩
theorem L1071_fin : (prmOK pL1071 1071 && ptTest pL1071 (runFrom pL1071 (fmask pL1071) (cmask pL1071) (hmask pL1071) 1 1070 (true, (init pL1071), (init pL1071))) 1071 536 false) = true := by
  decide +kernel
theorem L1071_ok : RunOK pL1071 1071 (runFrom pL1071 (fmask pL1071) (cmask pL1071) (hmask pL1071) 1 1070 (true, (init pL1071), (init pL1071))) ∧ ptTest pL1071 (runFrom pL1071 (fmask pL1071) (cmask pL1071) (hmask pL1071) 1 1070 (true, (init pL1071), (init pL1071))) 1071 536 false = true :=
  fin_run (runOK_init (prmOK_of_and L1071_fin) true) (by decide) rfl L1071_fin ptTest_fst
theorem H1071_fin : (prmOK pH1071 1071 && ptTest pH1071 (runFrom pH1071 (fmask pH1071) (cmask pH1071) (hmask pH1071) 1 1070 (true, (init pH1071), (init pH1071))) 1071 536 true) = true := by
  decide +kernel
theorem H1071_ok : RunOK pH1071 1071 (runFrom pH1071 (fmask pH1071) (cmask pH1071) (hmask pH1071) 1 1070 (true, (init pH1071), (init pH1071))) ∧ ptTest pH1071 (runFrom pH1071 (fmask pH1071) (cmask pH1071) (hmask pH1071) 1 1070 (true, (init pH1071), (init pH1071))) 1071 536 true = true :=
  fin_run (runOK_init (prmOK_of_and H1071_fin) true) (by decide) rfl H1071_fin ptTest_fst
theorem I1071_fin : (prmOK pI1071 1071 && intTest pI1071 (runFrom pI1071 (fmask pI1071) (cmask pI1071) (hmask pI1071) 1 1070 (true, (init pI1071), (init pI1071))) 1071 18 false) = true := by
  decide +kernel
theorem I1071_ok : RunOK pI1071 1071 (runFrom pI1071 (fmask pI1071) (cmask pI1071) (hmask pI1071) 1 1070 (true, (init pI1071), (init pI1071))) ∧ intTest pI1071 (runFrom pI1071 (fmask pI1071) (cmask pI1071) (hmask pI1071) 1 1070 (true, (init pI1071), (init pI1071))) 1071 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1071_fin) true) (by decide) rfl I1071_fin intTest_fst
theorem link1071 : linkOK pL1071 pH1071 pI1071 = true := by decide +kernel
theorem cvx1071 : ConvexBetweenHumps 1071 :=
  cvx_of L1071_ok H1071_ok I1071_ok link1071 (by decide)

/-! ### `N = 1072` -/

def pL1072 : Prm := ⟨77, 37, 37, 1074, 11, 18446744073709551616, 163221029477849043, 163221029477849043⟩
def pH1072 : Prm := ⟨77, 37, 37, 1074, 11, 18446744073709551616, 163223228501104595, 163223228501104595⟩
def pI1072 : Prm := ⟨65, 32, 30, 1074, 11, 18446744073709551616, 163221029477849043, 163223228501104595⟩
theorem L1072_fin : (prmOK pL1072 1072 && ptTest pL1072 (runFrom pL1072 (fmask pL1072) (cmask pL1072) (hmask pL1072) 1 1071 (true, (init pL1072), (init pL1072))) 1072 536 false) = true := by
  decide +kernel
theorem L1072_ok : RunOK pL1072 1072 (runFrom pL1072 (fmask pL1072) (cmask pL1072) (hmask pL1072) 1 1071 (true, (init pL1072), (init pL1072))) ∧ ptTest pL1072 (runFrom pL1072 (fmask pL1072) (cmask pL1072) (hmask pL1072) 1 1071 (true, (init pL1072), (init pL1072))) 1072 536 false = true :=
  fin_run (runOK_init (prmOK_of_and L1072_fin) true) (by decide) rfl L1072_fin ptTest_fst
theorem H1072_fin : (prmOK pH1072 1072 && ptTest pH1072 (runFrom pH1072 (fmask pH1072) (cmask pH1072) (hmask pH1072) 1 1071 (true, (init pH1072), (init pH1072))) 1072 536 true) = true := by
  decide +kernel
theorem H1072_ok : RunOK pH1072 1072 (runFrom pH1072 (fmask pH1072) (cmask pH1072) (hmask pH1072) 1 1071 (true, (init pH1072), (init pH1072))) ∧ ptTest pH1072 (runFrom pH1072 (fmask pH1072) (cmask pH1072) (hmask pH1072) 1 1071 (true, (init pH1072), (init pH1072))) 1072 536 true = true :=
  fin_run (runOK_init (prmOK_of_and H1072_fin) true) (by decide) rfl H1072_fin ptTest_fst
theorem I1072_fin : (prmOK pI1072 1072 && intTest pI1072 (runFrom pI1072 (fmask pI1072) (cmask pI1072) (hmask pI1072) 1 1071 (true, (init pI1072), (init pI1072))) 1072 18 true) = true := by
  decide +kernel
theorem I1072_ok : RunOK pI1072 1072 (runFrom pI1072 (fmask pI1072) (cmask pI1072) (hmask pI1072) 1 1071 (true, (init pI1072), (init pI1072))) ∧ intTest pI1072 (runFrom pI1072 (fmask pI1072) (cmask pI1072) (hmask pI1072) 1 1071 (true, (init pI1072), (init pI1072))) 1072 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1072_fin) true) (by decide) rfl I1072_fin intTest_fst
theorem link1072 : linkOK pL1072 pH1072 pI1072 = true := by decide +kernel
theorem cvx1072 : ConvexBetweenHumps 1072 :=
  cvx_of L1072_ok H1072_ok I1072_ok link1072 (by decide)
theorem cenlink1072 : cenLinkOK pI1072 1072 = true := by decide +kernel
theorem cen1072 : CenterUniqueMin 1072 ∧ DipHyp 1072 ∧ OnePointHyps 1072 :=
  cen_of L1072_ok H1072_ok I1072_ok link1072 cenlink1072

/-! ### `N = 1073` -/

def pL1073 : Prm := ⟨77, 37, 37, 1075, 11, 18446744073709551616, 163099096334995312, 163099096334995312⟩
def pH1073 : Prm := ⟨77, 37, 37, 1075, 11, 18446744073709551616, 163101295358250864, 163101295358250864⟩
def pI1073 : Prm := ⟨65, 32, 30, 1075, 11, 18446744073709551616, 163099096334995312, 163101295358250864⟩
theorem L1073_fin : (prmOK pL1073 1073 && ptTest pL1073 (runFrom pL1073 (fmask pL1073) (cmask pL1073) (hmask pL1073) 1 1072 (true, (init pL1073), (init pL1073))) 1073 537 false) = true := by
  decide +kernel
theorem L1073_ok : RunOK pL1073 1073 (runFrom pL1073 (fmask pL1073) (cmask pL1073) (hmask pL1073) 1 1072 (true, (init pL1073), (init pL1073))) ∧ ptTest pL1073 (runFrom pL1073 (fmask pL1073) (cmask pL1073) (hmask pL1073) 1 1072 (true, (init pL1073), (init pL1073))) 1073 537 false = true :=
  fin_run (runOK_init (prmOK_of_and L1073_fin) true) (by decide) rfl L1073_fin ptTest_fst
theorem H1073_fin : (prmOK pH1073 1073 && ptTest pH1073 (runFrom pH1073 (fmask pH1073) (cmask pH1073) (hmask pH1073) 1 1072 (true, (init pH1073), (init pH1073))) 1073 537 true) = true := by
  decide +kernel
theorem H1073_ok : RunOK pH1073 1073 (runFrom pH1073 (fmask pH1073) (cmask pH1073) (hmask pH1073) 1 1072 (true, (init pH1073), (init pH1073))) ∧ ptTest pH1073 (runFrom pH1073 (fmask pH1073) (cmask pH1073) (hmask pH1073) 1 1072 (true, (init pH1073), (init pH1073))) 1073 537 true = true :=
  fin_run (runOK_init (prmOK_of_and H1073_fin) true) (by decide) rfl H1073_fin ptTest_fst
theorem I1073_fin : (prmOK pI1073 1073 && intTest pI1073 (runFrom pI1073 (fmask pI1073) (cmask pI1073) (hmask pI1073) 1 1072 (true, (init pI1073), (init pI1073))) 1073 18 false) = true := by
  decide +kernel
theorem I1073_ok : RunOK pI1073 1073 (runFrom pI1073 (fmask pI1073) (cmask pI1073) (hmask pI1073) 1 1072 (true, (init pI1073), (init pI1073))) ∧ intTest pI1073 (runFrom pI1073 (fmask pI1073) (cmask pI1073) (hmask pI1073) 1 1072 (true, (init pI1073), (init pI1073))) 1073 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1073_fin) true) (by decide) rfl I1073_fin intTest_fst
theorem link1073 : linkOK pL1073 pH1073 pI1073 = true := by decide +kernel
theorem cvx1073 : ConvexBetweenHumps 1073 :=
  cvx_of L1073_ok H1073_ok I1073_ok link1073 (by decide)

/-! ### `N = 1074` -/

def pL1074 : Prm := ⟨77, 37, 37, 1076, 11, 18446744073709551616, 162977455248999644, 162977455248999644⟩
def pH1074 : Prm := ⟨77, 37, 37, 1076, 11, 18446744073709551616, 162979654272255196, 162979654272255196⟩
def pI1074 : Prm := ⟨65, 32, 30, 1076, 11, 18446744073709551616, 162977455248999644, 162979654272255196⟩
theorem L1074_fin : (prmOK pL1074 1074 && ptTest pL1074 (runFrom pL1074 (fmask pL1074) (cmask pL1074) (hmask pL1074) 1 1073 (true, (init pL1074), (init pL1074))) 1074 537 false) = true := by
  decide +kernel
theorem L1074_ok : RunOK pL1074 1074 (runFrom pL1074 (fmask pL1074) (cmask pL1074) (hmask pL1074) 1 1073 (true, (init pL1074), (init pL1074))) ∧ ptTest pL1074 (runFrom pL1074 (fmask pL1074) (cmask pL1074) (hmask pL1074) 1 1073 (true, (init pL1074), (init pL1074))) 1074 537 false = true :=
  fin_run (runOK_init (prmOK_of_and L1074_fin) true) (by decide) rfl L1074_fin ptTest_fst
theorem H1074_fin : (prmOK pH1074 1074 && ptTest pH1074 (runFrom pH1074 (fmask pH1074) (cmask pH1074) (hmask pH1074) 1 1073 (true, (init pH1074), (init pH1074))) 1074 537 true) = true := by
  decide +kernel
theorem H1074_ok : RunOK pH1074 1074 (runFrom pH1074 (fmask pH1074) (cmask pH1074) (hmask pH1074) 1 1073 (true, (init pH1074), (init pH1074))) ∧ ptTest pH1074 (runFrom pH1074 (fmask pH1074) (cmask pH1074) (hmask pH1074) 1 1073 (true, (init pH1074), (init pH1074))) 1074 537 true = true :=
  fin_run (runOK_init (prmOK_of_and H1074_fin) true) (by decide) rfl H1074_fin ptTest_fst
theorem I1074_fin : (prmOK pI1074 1074 && intTest pI1074 (runFrom pI1074 (fmask pI1074) (cmask pI1074) (hmask pI1074) 1 1073 (true, (init pI1074), (init pI1074))) 1074 18 true) = true := by
  decide +kernel
theorem I1074_ok : RunOK pI1074 1074 (runFrom pI1074 (fmask pI1074) (cmask pI1074) (hmask pI1074) 1 1073 (true, (init pI1074), (init pI1074))) ∧ intTest pI1074 (runFrom pI1074 (fmask pI1074) (cmask pI1074) (hmask pI1074) 1 1073 (true, (init pI1074), (init pI1074))) 1074 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1074_fin) true) (by decide) rfl I1074_fin intTest_fst
theorem link1074 : linkOK pL1074 pH1074 pI1074 = true := by decide +kernel
theorem cvx1074 : ConvexBetweenHumps 1074 :=
  cvx_of L1074_ok H1074_ok I1074_ok link1074 (by decide)
theorem cenlink1074 : cenLinkOK pI1074 1074 = true := by decide +kernel
theorem cen1074 : CenterUniqueMin 1074 ∧ DipHyp 1074 ∧ OnePointHyps 1074 :=
  cen_of L1074_ok H1074_ok I1074_ok link1074 cenlink1074

/-! ### `N = 1075` -/

def pL1075 : Prm := ⟨77, 37, 37, 1077, 11, 18446744073709551616, 162855919553016004, 162855919553016004⟩
def pH1075 : Prm := ⟨77, 37, 37, 1077, 11, 18446744073709551616, 162858118576271556, 162858118576271556⟩
def pI1075 : Prm := ⟨65, 32, 30, 1077, 11, 18446744073709551616, 162855919553016004, 162858118576271556⟩
theorem L1075_fin : (prmOK pL1075 1075 && ptTest pL1075 (runFrom pL1075 (fmask pL1075) (cmask pL1075) (hmask pL1075) 1 1074 (true, (init pL1075), (init pL1075))) 1075 538 false) = true := by
  decide +kernel
theorem L1075_ok : RunOK pL1075 1075 (runFrom pL1075 (fmask pL1075) (cmask pL1075) (hmask pL1075) 1 1074 (true, (init pL1075), (init pL1075))) ∧ ptTest pL1075 (runFrom pL1075 (fmask pL1075) (cmask pL1075) (hmask pL1075) 1 1074 (true, (init pL1075), (init pL1075))) 1075 538 false = true :=
  fin_run (runOK_init (prmOK_of_and L1075_fin) true) (by decide) rfl L1075_fin ptTest_fst
theorem H1075_fin : (prmOK pH1075 1075 && ptTest pH1075 (runFrom pH1075 (fmask pH1075) (cmask pH1075) (hmask pH1075) 1 1074 (true, (init pH1075), (init pH1075))) 1075 538 true) = true := by
  decide +kernel
theorem H1075_ok : RunOK pH1075 1075 (runFrom pH1075 (fmask pH1075) (cmask pH1075) (hmask pH1075) 1 1074 (true, (init pH1075), (init pH1075))) ∧ ptTest pH1075 (runFrom pH1075 (fmask pH1075) (cmask pH1075) (hmask pH1075) 1 1074 (true, (init pH1075), (init pH1075))) 1075 538 true = true :=
  fin_run (runOK_init (prmOK_of_and H1075_fin) true) (by decide) rfl H1075_fin ptTest_fst
theorem I1075_fin : (prmOK pI1075 1075 && intTest pI1075 (runFrom pI1075 (fmask pI1075) (cmask pI1075) (hmask pI1075) 1 1074 (true, (init pI1075), (init pI1075))) 1075 18 false) = true := by
  decide +kernel
theorem I1075_ok : RunOK pI1075 1075 (runFrom pI1075 (fmask pI1075) (cmask pI1075) (hmask pI1075) 1 1074 (true, (init pI1075), (init pI1075))) ∧ intTest pI1075 (runFrom pI1075 (fmask pI1075) (cmask pI1075) (hmask pI1075) 1 1074 (true, (init pI1075), (init pI1075))) 1075 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1075_fin) true) (by decide) rfl I1075_fin intTest_fst
theorem link1075 : linkOK pL1075 pH1075 pI1075 = true := by decide +kernel
theorem cvx1075 : ConvexBetweenHumps 1075 :=
  cvx_of L1075_ok H1075_ok I1075_ok link1075 (by decide)

/-! ### `N = 1076` -/

def pL1076 : Prm := ⟨77, 37, 37, 1078, 11, 18446744073709551616, 162734674381648523, 162734674381648523⟩
def pH1076 : Prm := ⟨78, 38, 37, 1078, 11, 18446744073709551616, 162736873404904075, 162736873404904075⟩
def pI1076 : Prm := ⟨65, 32, 30, 1078, 11, 18446744073709551616, 162734674381648523, 162736873404904075⟩
theorem L1076_fin : (prmOK pL1076 1076 && ptTest pL1076 (runFrom pL1076 (fmask pL1076) (cmask pL1076) (hmask pL1076) 1 1075 (true, (init pL1076), (init pL1076))) 1076 538 false) = true := by
  decide +kernel
theorem L1076_ok : RunOK pL1076 1076 (runFrom pL1076 (fmask pL1076) (cmask pL1076) (hmask pL1076) 1 1075 (true, (init pL1076), (init pL1076))) ∧ ptTest pL1076 (runFrom pL1076 (fmask pL1076) (cmask pL1076) (hmask pL1076) 1 1075 (true, (init pL1076), (init pL1076))) 1076 538 false = true :=
  fin_run (runOK_init (prmOK_of_and L1076_fin) true) (by decide) rfl L1076_fin ptTest_fst
theorem H1076_fin : (prmOK pH1076 1076 && ptTest pH1076 (runFrom pH1076 (fmask pH1076) (cmask pH1076) (hmask pH1076) 1 1075 (true, (init pH1076), (init pH1076))) 1076 538 true) = true := by
  decide +kernel
theorem H1076_ok : RunOK pH1076 1076 (runFrom pH1076 (fmask pH1076) (cmask pH1076) (hmask pH1076) 1 1075 (true, (init pH1076), (init pH1076))) ∧ ptTest pH1076 (runFrom pH1076 (fmask pH1076) (cmask pH1076) (hmask pH1076) 1 1075 (true, (init pH1076), (init pH1076))) 1076 538 true = true :=
  fin_run (runOK_init (prmOK_of_and H1076_fin) true) (by decide) rfl H1076_fin ptTest_fst
theorem I1076_fin : (prmOK pI1076 1076 && intTest pI1076 (runFrom pI1076 (fmask pI1076) (cmask pI1076) (hmask pI1076) 1 1075 (true, (init pI1076), (init pI1076))) 1076 18 true) = true := by
  decide +kernel
theorem I1076_ok : RunOK pI1076 1076 (runFrom pI1076 (fmask pI1076) (cmask pI1076) (hmask pI1076) 1 1075 (true, (init pI1076), (init pI1076))) ∧ intTest pI1076 (runFrom pI1076 (fmask pI1076) (cmask pI1076) (hmask pI1076) 1 1075 (true, (init pI1076), (init pI1076))) 1076 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1076_fin) true) (by decide) rfl I1076_fin intTest_fst
theorem link1076 : linkOK pL1076 pH1076 pI1076 = true := by decide +kernel
theorem cvx1076 : ConvexBetweenHumps 1076 :=
  cvx_of L1076_ok H1076_ok I1076_ok link1076 (by decide)
theorem cenlink1076 : cenLinkOK pI1076 1076 = true := by decide +kernel
theorem cen1076 : CenterUniqueMin 1076 ∧ DipHyp 1076 ∧ OnePointHyps 1076 :=
  cen_of L1076_ok H1076_ok I1076_ok link1076 cenlink1076

/-! ### `N = 1077` -/

def pL1077 : Prm := ⟨77, 37, 37, 1079, 11, 18446744073709551616, 162613534126506897, 162613534126506897⟩
def pH1077 : Prm := ⟨77, 37, 37, 1079, 11, 18446744073709551616, 162615733149762449, 162615733149762449⟩
def pI1077 : Prm := ⟨65, 32, 30, 1079, 11, 18446744073709551616, 162613534126506897, 162615733149762449⟩
theorem L1077_fin : (prmOK pL1077 1077 && ptTest pL1077 (runFrom pL1077 (fmask pL1077) (cmask pL1077) (hmask pL1077) 1 1076 (true, (init pL1077), (init pL1077))) 1077 539 false) = true := by
  decide +kernel
theorem L1077_ok : RunOK pL1077 1077 (runFrom pL1077 (fmask pL1077) (cmask pL1077) (hmask pL1077) 1 1076 (true, (init pL1077), (init pL1077))) ∧ ptTest pL1077 (runFrom pL1077 (fmask pL1077) (cmask pL1077) (hmask pL1077) 1 1076 (true, (init pL1077), (init pL1077))) 1077 539 false = true :=
  fin_run (runOK_init (prmOK_of_and L1077_fin) true) (by decide) rfl L1077_fin ptTest_fst
theorem H1077_fin : (prmOK pH1077 1077 && ptTest pH1077 (runFrom pH1077 (fmask pH1077) (cmask pH1077) (hmask pH1077) 1 1076 (true, (init pH1077), (init pH1077))) 1077 539 true) = true := by
  decide +kernel
theorem H1077_ok : RunOK pH1077 1077 (runFrom pH1077 (fmask pH1077) (cmask pH1077) (hmask pH1077) 1 1076 (true, (init pH1077), (init pH1077))) ∧ ptTest pH1077 (runFrom pH1077 (fmask pH1077) (cmask pH1077) (hmask pH1077) 1 1076 (true, (init pH1077), (init pH1077))) 1077 539 true = true :=
  fin_run (runOK_init (prmOK_of_and H1077_fin) true) (by decide) rfl H1077_fin ptTest_fst
theorem I1077_fin : (prmOK pI1077 1077 && intTest pI1077 (runFrom pI1077 (fmask pI1077) (cmask pI1077) (hmask pI1077) 1 1076 (true, (init pI1077), (init pI1077))) 1077 18 false) = true := by
  decide +kernel
theorem I1077_ok : RunOK pI1077 1077 (runFrom pI1077 (fmask pI1077) (cmask pI1077) (hmask pI1077) 1 1076 (true, (init pI1077), (init pI1077))) ∧ intTest pI1077 (runFrom pI1077 (fmask pI1077) (cmask pI1077) (hmask pI1077) 1 1076 (true, (init pI1077), (init pI1077))) 1077 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1077_fin) true) (by decide) rfl I1077_fin intTest_fst
theorem link1077 : linkOK pL1077 pH1077 pI1077 = true := by decide +kernel
theorem cvx1077 : ConvexBetweenHumps 1077 :=
  cvx_of L1077_ok H1077_ok I1077_ok link1077 (by decide)

/-! ### `N = 1078` -/

def pL1078 : Prm := ⟨78, 38, 37, 1080, 11, 18446744073709551616, 162492682874586211, 162492682874586211⟩
def pH1078 : Prm := ⟨77, 37, 37, 1080, 11, 18446744073709551616, 162494881897841763, 162494881897841763⟩
def pI1078 : Prm := ⟨65, 32, 30, 1080, 11, 18446744073709551616, 162492682874586211, 162494881897841763⟩
theorem L1078_fin : (prmOK pL1078 1078 && ptTest pL1078 (runFrom pL1078 (fmask pL1078) (cmask pL1078) (hmask pL1078) 1 1077 (true, (init pL1078), (init pL1078))) 1078 539 false) = true := by
  decide +kernel
theorem L1078_ok : RunOK pL1078 1078 (runFrom pL1078 (fmask pL1078) (cmask pL1078) (hmask pL1078) 1 1077 (true, (init pL1078), (init pL1078))) ∧ ptTest pL1078 (runFrom pL1078 (fmask pL1078) (cmask pL1078) (hmask pL1078) 1 1077 (true, (init pL1078), (init pL1078))) 1078 539 false = true :=
  fin_run (runOK_init (prmOK_of_and L1078_fin) true) (by decide) rfl L1078_fin ptTest_fst
theorem H1078_fin : (prmOK pH1078 1078 && ptTest pH1078 (runFrom pH1078 (fmask pH1078) (cmask pH1078) (hmask pH1078) 1 1077 (true, (init pH1078), (init pH1078))) 1078 539 true) = true := by
  decide +kernel
theorem H1078_ok : RunOK pH1078 1078 (runFrom pH1078 (fmask pH1078) (cmask pH1078) (hmask pH1078) 1 1077 (true, (init pH1078), (init pH1078))) ∧ ptTest pH1078 (runFrom pH1078 (fmask pH1078) (cmask pH1078) (hmask pH1078) 1 1077 (true, (init pH1078), (init pH1078))) 1078 539 true = true :=
  fin_run (runOK_init (prmOK_of_and H1078_fin) true) (by decide) rfl H1078_fin ptTest_fst
theorem I1078_fin : (prmOK pI1078 1078 && intTest pI1078 (runFrom pI1078 (fmask pI1078) (cmask pI1078) (hmask pI1078) 1 1077 (true, (init pI1078), (init pI1078))) 1078 18 true) = true := by
  decide +kernel
theorem I1078_ok : RunOK pI1078 1078 (runFrom pI1078 (fmask pI1078) (cmask pI1078) (hmask pI1078) 1 1077 (true, (init pI1078), (init pI1078))) ∧ intTest pI1078 (runFrom pI1078 (fmask pI1078) (cmask pI1078) (hmask pI1078) 1 1077 (true, (init pI1078), (init pI1078))) 1078 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1078_fin) true) (by decide) rfl I1078_fin intTest_fst
theorem link1078 : linkOK pL1078 pH1078 pI1078 = true := by decide +kernel
theorem cvx1078 : ConvexBetweenHumps 1078 :=
  cvx_of L1078_ok H1078_ok I1078_ok link1078 (by decide)
theorem cenlink1078 : cenLinkOK pI1078 1078 = true := by decide +kernel
theorem cen1078 : CenterUniqueMin 1078 ∧ DipHyp 1078 ∧ OnePointHyps 1078 :=
  cen_of L1078_ok H1078_ok I1078_ok link1078 cenlink1078

/-! ### `N = 1079` -/

def pL1079 : Prm := ⟨77, 37, 37, 1081, 11, 18446744073709551616, 162371936067946004, 162371936067946004⟩
def pH1079 : Prm := ⟨78, 38, 37, 1081, 11, 18446744073709551616, 162374135091201556, 162374135091201556⟩
def pI1079 : Prm := ⟨65, 32, 30, 1081, 11, 18446744073709551616, 162371936067946004, 162374135091201556⟩
theorem L1079_fin : (prmOK pL1079 1079 && ptTest pL1079 (runFrom pL1079 (fmask pL1079) (cmask pL1079) (hmask pL1079) 1 1078 (true, (init pL1079), (init pL1079))) 1079 540 false) = true := by
  decide +kernel
theorem L1079_ok : RunOK pL1079 1079 (runFrom pL1079 (fmask pL1079) (cmask pL1079) (hmask pL1079) 1 1078 (true, (init pL1079), (init pL1079))) ∧ ptTest pL1079 (runFrom pL1079 (fmask pL1079) (cmask pL1079) (hmask pL1079) 1 1078 (true, (init pL1079), (init pL1079))) 1079 540 false = true :=
  fin_run (runOK_init (prmOK_of_and L1079_fin) true) (by decide) rfl L1079_fin ptTest_fst
theorem H1079_fin : (prmOK pH1079 1079 && ptTest pH1079 (runFrom pH1079 (fmask pH1079) (cmask pH1079) (hmask pH1079) 1 1078 (true, (init pH1079), (init pH1079))) 1079 540 true) = true := by
  decide +kernel
theorem H1079_ok : RunOK pH1079 1079 (runFrom pH1079 (fmask pH1079) (cmask pH1079) (hmask pH1079) 1 1078 (true, (init pH1079), (init pH1079))) ∧ ptTest pH1079 (runFrom pH1079 (fmask pH1079) (cmask pH1079) (hmask pH1079) 1 1078 (true, (init pH1079), (init pH1079))) 1079 540 true = true :=
  fin_run (runOK_init (prmOK_of_and H1079_fin) true) (by decide) rfl H1079_fin ptTest_fst
theorem I1079_fin : (prmOK pI1079 1079 && intTest pI1079 (runFrom pI1079 (fmask pI1079) (cmask pI1079) (hmask pI1079) 1 1078 (true, (init pI1079), (init pI1079))) 1079 18 false) = true := by
  decide +kernel
theorem I1079_ok : RunOK pI1079 1079 (runFrom pI1079 (fmask pI1079) (cmask pI1079) (hmask pI1079) 1 1078 (true, (init pI1079), (init pI1079))) ∧ intTest pI1079 (runFrom pI1079 (fmask pI1079) (cmask pI1079) (hmask pI1079) 1 1078 (true, (init pI1079), (init pI1079))) 1079 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1079_fin) true) (by decide) rfl I1079_fin intTest_fst
theorem link1079 : linkOK pL1079 pH1079 pI1079 = true := by decide +kernel
theorem cvx1079 : ConvexBetweenHumps 1079 :=
  cvx_of L1079_ok H1079_ok I1079_ok link1079 (by decide)

/-! ### `N = 1080` -/

def pL1080 : Prm := ⟨78, 38, 37, 1082, 11, 18446744073709551616, 162251476753885972, 162251476753885972⟩
def pH1080 : Prm := ⟨78, 38, 37, 1082, 11, 18446744073709551616, 162253675777141524, 162253675777141524⟩
def pI1080 : Prm := ⟨65, 32, 30, 1082, 11, 18446744073709551616, 162251476753885972, 162253675777141524⟩
theorem L1080_fin : (prmOK pL1080 1080 && ptTest pL1080 (runFrom pL1080 (fmask pL1080) (cmask pL1080) (hmask pL1080) 1 1079 (true, (init pL1080), (init pL1080))) 1080 540 false) = true := by
  decide +kernel
theorem L1080_ok : RunOK pL1080 1080 (runFrom pL1080 (fmask pL1080) (cmask pL1080) (hmask pL1080) 1 1079 (true, (init pL1080), (init pL1080))) ∧ ptTest pL1080 (runFrom pL1080 (fmask pL1080) (cmask pL1080) (hmask pL1080) 1 1079 (true, (init pL1080), (init pL1080))) 1080 540 false = true :=
  fin_run (runOK_init (prmOK_of_and L1080_fin) true) (by decide) rfl L1080_fin ptTest_fst
theorem H1080_fin : (prmOK pH1080 1080 && ptTest pH1080 (runFrom pH1080 (fmask pH1080) (cmask pH1080) (hmask pH1080) 1 1079 (true, (init pH1080), (init pH1080))) 1080 540 true) = true := by
  decide +kernel
theorem H1080_ok : RunOK pH1080 1080 (runFrom pH1080 (fmask pH1080) (cmask pH1080) (hmask pH1080) 1 1079 (true, (init pH1080), (init pH1080))) ∧ ptTest pH1080 (runFrom pH1080 (fmask pH1080) (cmask pH1080) (hmask pH1080) 1 1079 (true, (init pH1080), (init pH1080))) 1080 540 true = true :=
  fin_run (runOK_init (prmOK_of_and H1080_fin) true) (by decide) rfl H1080_fin ptTest_fst
theorem I1080_fin : (prmOK pI1080 1080 && intTest pI1080 (runFrom pI1080 (fmask pI1080) (cmask pI1080) (hmask pI1080) 1 1079 (true, (init pI1080), (init pI1080))) 1080 18 true) = true := by
  decide +kernel
theorem I1080_ok : RunOK pI1080 1080 (runFrom pI1080 (fmask pI1080) (cmask pI1080) (hmask pI1080) 1 1079 (true, (init pI1080), (init pI1080))) ∧ intTest pI1080 (runFrom pI1080 (fmask pI1080) (cmask pI1080) (hmask pI1080) 1 1079 (true, (init pI1080), (init pI1080))) 1080 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1080_fin) true) (by decide) rfl I1080_fin intTest_fst
theorem link1080 : linkOK pL1080 pH1080 pI1080 = true := by decide +kernel
theorem cvx1080 : ConvexBetweenHumps 1080 :=
  cvx_of L1080_ok H1080_ok I1080_ok link1080 (by decide)
theorem cenlink1080 : cenLinkOK pI1080 1080 = true := by decide +kernel
theorem cen1080 : CenterUniqueMin 1080 ∧ DipHyp 1080 ∧ OnePointHyps 1080 :=
  cen_of L1080_ok H1080_ok I1080_ok link1080 cenlink1080

/-! ### `N = 1081` -/

def pL1081 : Prm := ⟨77, 37, 37, 1083, 11, 18446744073709551616, 162131121417038734, 162131121417038734⟩
def pH1081 : Prm := ⟨78, 38, 37, 1083, 11, 18446744073709551616, 162133320440294286, 162133320440294286⟩
def pI1081 : Prm := ⟨65, 32, 30, 1083, 11, 18446744073709551616, 162131121417038734, 162133320440294286⟩
theorem L1081_fin : (prmOK pL1081 1081 && ptTest pL1081 (runFrom pL1081 (fmask pL1081) (cmask pL1081) (hmask pL1081) 1 1080 (true, (init pL1081), (init pL1081))) 1081 541 false) = true := by
  decide +kernel
theorem L1081_ok : RunOK pL1081 1081 (runFrom pL1081 (fmask pL1081) (cmask pL1081) (hmask pL1081) 1 1080 (true, (init pL1081), (init pL1081))) ∧ ptTest pL1081 (runFrom pL1081 (fmask pL1081) (cmask pL1081) (hmask pL1081) 1 1080 (true, (init pL1081), (init pL1081))) 1081 541 false = true :=
  fin_run (runOK_init (prmOK_of_and L1081_fin) true) (by decide) rfl L1081_fin ptTest_fst
theorem H1081_fin : (prmOK pH1081 1081 && ptTest pH1081 (runFrom pH1081 (fmask pH1081) (cmask pH1081) (hmask pH1081) 1 1080 (true, (init pH1081), (init pH1081))) 1081 541 true) = true := by
  decide +kernel
theorem H1081_ok : RunOK pH1081 1081 (runFrom pH1081 (fmask pH1081) (cmask pH1081) (hmask pH1081) 1 1080 (true, (init pH1081), (init pH1081))) ∧ ptTest pH1081 (runFrom pH1081 (fmask pH1081) (cmask pH1081) (hmask pH1081) 1 1080 (true, (init pH1081), (init pH1081))) 1081 541 true = true :=
  fin_run (runOK_init (prmOK_of_and H1081_fin) true) (by decide) rfl H1081_fin ptTest_fst
theorem I1081_fin : (prmOK pI1081 1081 && intTest pI1081 (runFrom pI1081 (fmask pI1081) (cmask pI1081) (hmask pI1081) 1 1080 (true, (init pI1081), (init pI1081))) 1081 18 false) = true := by
  decide +kernel
theorem I1081_ok : RunOK pI1081 1081 (runFrom pI1081 (fmask pI1081) (cmask pI1081) (hmask pI1081) 1 1080 (true, (init pI1081), (init pI1081))) ∧ intTest pI1081 (runFrom pI1081 (fmask pI1081) (cmask pI1081) (hmask pI1081) 1 1080 (true, (init pI1081), (init pI1081))) 1081 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1081_fin) true) (by decide) rfl I1081_fin intTest_fst
theorem link1081 : linkOK pL1081 pH1081 pI1081 = true := by decide +kernel
theorem cvx1081 : ConvexBetweenHumps 1081 :=
  cvx_of L1081_ok H1081_ok I1081_ok link1081 (by decide)

/-! ### `N = 1082` -/

def pL1082 : Prm := ⟨77, 37, 37, 1084, 11, 18446744073709551616, 162011052072756231, 162011052072756231⟩
def pH1082 : Prm := ⟨78, 38, 37, 1084, 11, 18446744073709551616, 162013251096011783, 162013251096011783⟩
def pI1082 : Prm := ⟨65, 32, 30, 1084, 11, 18446744073709551616, 162011052072756231, 162013251096011783⟩
theorem L1082_fin : (prmOK pL1082 1082 && ptTest pL1082 (runFrom pL1082 (fmask pL1082) (cmask pL1082) (hmask pL1082) 1 1081 (true, (init pL1082), (init pL1082))) 1082 541 false) = true := by
  decide +kernel
theorem L1082_ok : RunOK pL1082 1082 (runFrom pL1082 (fmask pL1082) (cmask pL1082) (hmask pL1082) 1 1081 (true, (init pL1082), (init pL1082))) ∧ ptTest pL1082 (runFrom pL1082 (fmask pL1082) (cmask pL1082) (hmask pL1082) 1 1081 (true, (init pL1082), (init pL1082))) 1082 541 false = true :=
  fin_run (runOK_init (prmOK_of_and L1082_fin) true) (by decide) rfl L1082_fin ptTest_fst
theorem H1082_fin : (prmOK pH1082 1082 && ptTest pH1082 (runFrom pH1082 (fmask pH1082) (cmask pH1082) (hmask pH1082) 1 1081 (true, (init pH1082), (init pH1082))) 1082 541 true) = true := by
  decide +kernel
theorem H1082_ok : RunOK pH1082 1082 (runFrom pH1082 (fmask pH1082) (cmask pH1082) (hmask pH1082) 1 1081 (true, (init pH1082), (init pH1082))) ∧ ptTest pH1082 (runFrom pH1082 (fmask pH1082) (cmask pH1082) (hmask pH1082) 1 1081 (true, (init pH1082), (init pH1082))) 1082 541 true = true :=
  fin_run (runOK_init (prmOK_of_and H1082_fin) true) (by decide) rfl H1082_fin ptTest_fst
theorem I1082_fin : (prmOK pI1082 1082 && intTest pI1082 (runFrom pI1082 (fmask pI1082) (cmask pI1082) (hmask pI1082) 1 1081 (true, (init pI1082), (init pI1082))) 1082 18 true) = true := by
  decide +kernel
theorem I1082_ok : RunOK pI1082 1082 (runFrom pI1082 (fmask pI1082) (cmask pI1082) (hmask pI1082) 1 1081 (true, (init pI1082), (init pI1082))) ∧ intTest pI1082 (runFrom pI1082 (fmask pI1082) (cmask pI1082) (hmask pI1082) 1 1081 (true, (init pI1082), (init pI1082))) 1082 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1082_fin) true) (by decide) rfl I1082_fin intTest_fst
theorem link1082 : linkOK pL1082 pH1082 pI1082 = true := by decide +kernel
theorem cvx1082 : ConvexBetweenHumps 1082 :=
  cvx_of L1082_ok H1082_ok I1082_ok link1082 (by decide)
theorem cenlink1082 : cenLinkOK pI1082 1082 = true := by decide +kernel
theorem cen1082 : CenterUniqueMin 1082 ∧ DipHyp 1082 ∧ OnePointHyps 1082 :=
  cen_of L1082_ok H1082_ok I1082_ok link1082 cenlink1082

/-! ### `N = 1083` -/

def pL1083 : Prm := ⟨78, 38, 37, 1085, 11, 18446744073709551616, 161891086240478083, 161891086240478083⟩
def pH1083 : Prm := ⟨78, 38, 37, 1085, 11, 18446744073709551616, 161893285263733635, 161893285263733635⟩
def pI1083 : Prm := ⟨65, 32, 30, 1085, 11, 18446744073709551616, 161891086240478083, 161893285263733635⟩
theorem L1083_fin : (prmOK pL1083 1083 && ptTest pL1083 (runFrom pL1083 (fmask pL1083) (cmask pL1083) (hmask pL1083) 1 1082 (true, (init pL1083), (init pL1083))) 1083 542 false) = true := by
  decide +kernel
theorem L1083_ok : RunOK pL1083 1083 (runFrom pL1083 (fmask pL1083) (cmask pL1083) (hmask pL1083) 1 1082 (true, (init pL1083), (init pL1083))) ∧ ptTest pL1083 (runFrom pL1083 (fmask pL1083) (cmask pL1083) (hmask pL1083) 1 1082 (true, (init pL1083), (init pL1083))) 1083 542 false = true :=
  fin_run (runOK_init (prmOK_of_and L1083_fin) true) (by decide) rfl L1083_fin ptTest_fst
theorem H1083_fin : (prmOK pH1083 1083 && ptTest pH1083 (runFrom pH1083 (fmask pH1083) (cmask pH1083) (hmask pH1083) 1 1082 (true, (init pH1083), (init pH1083))) 1083 542 true) = true := by
  decide +kernel
theorem H1083_ok : RunOK pH1083 1083 (runFrom pH1083 (fmask pH1083) (cmask pH1083) (hmask pH1083) 1 1082 (true, (init pH1083), (init pH1083))) ∧ ptTest pH1083 (runFrom pH1083 (fmask pH1083) (cmask pH1083) (hmask pH1083) 1 1082 (true, (init pH1083), (init pH1083))) 1083 542 true = true :=
  fin_run (runOK_init (prmOK_of_and H1083_fin) true) (by decide) rfl H1083_fin ptTest_fst
theorem I1083_fin : (prmOK pI1083 1083 && intTest pI1083 (runFrom pI1083 (fmask pI1083) (cmask pI1083) (hmask pI1083) 1 1082 (true, (init pI1083), (init pI1083))) 1083 18 false) = true := by
  decide +kernel
theorem I1083_ok : RunOK pI1083 1083 (runFrom pI1083 (fmask pI1083) (cmask pI1083) (hmask pI1083) 1 1082 (true, (init pI1083), (init pI1083))) ∧ intTest pI1083 (runFrom pI1083 (fmask pI1083) (cmask pI1083) (hmask pI1083) 1 1082 (true, (init pI1083), (init pI1083))) 1083 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1083_fin) true) (by decide) rfl I1083_fin intTest_fst
theorem link1083 : linkOK pL1083 pH1083 pI1083 = true := by decide +kernel
theorem cvx1083 : ConvexBetweenHumps 1083 :=
  cvx_of L1083_ok H1083_ok I1083_ok link1083 (by decide)

/-! ### `N = 1084` -/

def pL1084 : Prm := ⟨77, 37, 37, 1086, 11, 18446744073709551616, 161771404911300766, 161771404911300766⟩
def pH1084 : Prm := ⟨78, 38, 37, 1086, 11, 18446744073709551616, 161773603934556318, 161773603934556318⟩
def pI1084 : Prm := ⟨65, 32, 30, 1086, 11, 18446744073709551616, 161771404911300766, 161773603934556318⟩
theorem L1084_fin : (prmOK pL1084 1084 && ptTest pL1084 (runFrom pL1084 (fmask pL1084) (cmask pL1084) (hmask pL1084) 1 1083 (true, (init pL1084), (init pL1084))) 1084 542 false) = true := by
  decide +kernel
theorem L1084_ok : RunOK pL1084 1084 (runFrom pL1084 (fmask pL1084) (cmask pL1084) (hmask pL1084) 1 1083 (true, (init pL1084), (init pL1084))) ∧ ptTest pL1084 (runFrom pL1084 (fmask pL1084) (cmask pL1084) (hmask pL1084) 1 1083 (true, (init pL1084), (init pL1084))) 1084 542 false = true :=
  fin_run (runOK_init (prmOK_of_and L1084_fin) true) (by decide) rfl L1084_fin ptTest_fst
theorem H1084_fin : (prmOK pH1084 1084 && ptTest pH1084 (runFrom pH1084 (fmask pH1084) (cmask pH1084) (hmask pH1084) 1 1083 (true, (init pH1084), (init pH1084))) 1084 542 true) = true := by
  decide +kernel
theorem H1084_ok : RunOK pH1084 1084 (runFrom pH1084 (fmask pH1084) (cmask pH1084) (hmask pH1084) 1 1083 (true, (init pH1084), (init pH1084))) ∧ ptTest pH1084 (runFrom pH1084 (fmask pH1084) (cmask pH1084) (hmask pH1084) 1 1083 (true, (init pH1084), (init pH1084))) 1084 542 true = true :=
  fin_run (runOK_init (prmOK_of_and H1084_fin) true) (by decide) rfl H1084_fin ptTest_fst
theorem I1084_fin : (prmOK pI1084 1084 && intTest pI1084 (runFrom pI1084 (fmask pI1084) (cmask pI1084) (hmask pI1084) 1 1083 (true, (init pI1084), (init pI1084))) 1084 18 true) = true := by
  decide +kernel
theorem I1084_ok : RunOK pI1084 1084 (runFrom pI1084 (fmask pI1084) (cmask pI1084) (hmask pI1084) 1 1083 (true, (init pI1084), (init pI1084))) ∧ intTest pI1084 (runFrom pI1084 (fmask pI1084) (cmask pI1084) (hmask pI1084) 1 1083 (true, (init pI1084), (init pI1084))) 1084 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1084_fin) true) (by decide) rfl I1084_fin intTest_fst
theorem link1084 : linkOK pL1084 pH1084 pI1084 = true := by decide +kernel
theorem cvx1084 : ConvexBetweenHumps 1084 :=
  cvx_of L1084_ok H1084_ok I1084_ok link1084 (by decide)
theorem cenlink1084 : cenLinkOK pI1084 1084 = true := by decide +kernel
theorem cen1084 : CenterUniqueMin 1084 ∧ DipHyp 1084 ∧ OnePointHyps 1084 :=
  cen_of L1084_ok H1084_ok I1084_ok link1084 cenlink1084

/-! ### `N = 1085` -/

def pL1085 : Prm := ⟨78, 38, 37, 1087, 11, 18446744073709551616, 161651826631723270, 161651826631723270⟩
def pH1085 : Prm := ⟨78, 38, 37, 1087, 11, 18446744073709551616, 161654025654978822, 161654025654978822⟩
def pI1085 : Prm := ⟨65, 32, 30, 1087, 11, 18446744073709551616, 161651826631723270, 161654025654978822⟩
theorem L1085_fin : (prmOK pL1085 1085 && ptTest pL1085 (runFrom pL1085 (fmask pL1085) (cmask pL1085) (hmask pL1085) 1 1084 (true, (init pL1085), (init pL1085))) 1085 543 false) = true := by
  decide +kernel
theorem L1085_ok : RunOK pL1085 1085 (runFrom pL1085 (fmask pL1085) (cmask pL1085) (hmask pL1085) 1 1084 (true, (init pL1085), (init pL1085))) ∧ ptTest pL1085 (runFrom pL1085 (fmask pL1085) (cmask pL1085) (hmask pL1085) 1 1084 (true, (init pL1085), (init pL1085))) 1085 543 false = true :=
  fin_run (runOK_init (prmOK_of_and L1085_fin) true) (by decide) rfl L1085_fin ptTest_fst
theorem H1085_fin : (prmOK pH1085 1085 && ptTest pH1085 (runFrom pH1085 (fmask pH1085) (cmask pH1085) (hmask pH1085) 1 1084 (true, (init pH1085), (init pH1085))) 1085 543 true) = true := by
  decide +kernel
theorem H1085_ok : RunOK pH1085 1085 (runFrom pH1085 (fmask pH1085) (cmask pH1085) (hmask pH1085) 1 1084 (true, (init pH1085), (init pH1085))) ∧ ptTest pH1085 (runFrom pH1085 (fmask pH1085) (cmask pH1085) (hmask pH1085) 1 1084 (true, (init pH1085), (init pH1085))) 1085 543 true = true :=
  fin_run (runOK_init (prmOK_of_and H1085_fin) true) (by decide) rfl H1085_fin ptTest_fst
theorem I1085_fin : (prmOK pI1085 1085 && intTest pI1085 (runFrom pI1085 (fmask pI1085) (cmask pI1085) (hmask pI1085) 1 1084 (true, (init pI1085), (init pI1085))) 1085 18 false) = true := by
  decide +kernel
theorem I1085_ok : RunOK pI1085 1085 (runFrom pI1085 (fmask pI1085) (cmask pI1085) (hmask pI1085) 1 1084 (true, (init pI1085), (init pI1085))) ∧ intTest pI1085 (runFrom pI1085 (fmask pI1085) (cmask pI1085) (hmask pI1085) 1 1084 (true, (init pI1085), (init pI1085))) 1085 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1085_fin) true) (by decide) rfl I1085_fin intTest_fst
theorem link1085 : linkOK pL1085 pH1085 pI1085 = true := by decide +kernel
theorem cvx1085 : ConvexBetweenHumps 1085 :=
  cvx_of L1085_ok H1085_ok I1085_ok link1085 (by decide)

/-! ### The range -/

theorem cvx_1050_1085 {N : ℕ} (h1 : 1050 ≤ N) (h2 : N ≤ 1085) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 1067
  · by_cases h4 : N ≤ 1058
    · by_cases h6 : N ≤ 1053
      · by_cases h8 : N ≤ 1051
        · by_cases h10 : N ≤ 1050
          · obtain rfl : N = 1050 := by omega
            exact cvx1050
          · obtain rfl : N = 1051 := by omega
            exact cvx1051
        · by_cases h10 : N ≤ 1052
          · obtain rfl : N = 1052 := by omega
            exact cvx1052
          · obtain rfl : N = 1053 := by omega
            exact cvx1053
      · by_cases h8 : N ≤ 1055
        · by_cases h10 : N ≤ 1054
          · obtain rfl : N = 1054 := by omega
            exact cvx1054
          · obtain rfl : N = 1055 := by omega
            exact cvx1055
        · by_cases h10 : N ≤ 1056
          · obtain rfl : N = 1056 := by omega
            exact cvx1056
          · by_cases h12 : N ≤ 1057
            · obtain rfl : N = 1057 := by omega
              exact cvx1057
            · obtain rfl : N = 1058 := by omega
              exact cvx1058
    · by_cases h6 : N ≤ 1062
      · by_cases h8 : N ≤ 1060
        · by_cases h10 : N ≤ 1059
          · obtain rfl : N = 1059 := by omega
            exact cvx1059
          · obtain rfl : N = 1060 := by omega
            exact cvx1060
        · by_cases h10 : N ≤ 1061
          · obtain rfl : N = 1061 := by omega
            exact cvx1061
          · obtain rfl : N = 1062 := by omega
            exact cvx1062
      · by_cases h8 : N ≤ 1064
        · by_cases h10 : N ≤ 1063
          · obtain rfl : N = 1063 := by omega
            exact cvx1063
          · obtain rfl : N = 1064 := by omega
            exact cvx1064
        · by_cases h10 : N ≤ 1065
          · obtain rfl : N = 1065 := by omega
            exact cvx1065
          · by_cases h12 : N ≤ 1066
            · obtain rfl : N = 1066 := by omega
              exact cvx1066
            · obtain rfl : N = 1067 := by omega
              exact cvx1067
  · by_cases h4 : N ≤ 1076
    · by_cases h6 : N ≤ 1071
      · by_cases h8 : N ≤ 1069
        · by_cases h10 : N ≤ 1068
          · obtain rfl : N = 1068 := by omega
            exact cvx1068
          · obtain rfl : N = 1069 := by omega
            exact cvx1069
        · by_cases h10 : N ≤ 1070
          · obtain rfl : N = 1070 := by omega
            exact cvx1070
          · obtain rfl : N = 1071 := by omega
            exact cvx1071
      · by_cases h8 : N ≤ 1073
        · by_cases h10 : N ≤ 1072
          · obtain rfl : N = 1072 := by omega
            exact cvx1072
          · obtain rfl : N = 1073 := by omega
            exact cvx1073
        · by_cases h10 : N ≤ 1074
          · obtain rfl : N = 1074 := by omega
            exact cvx1074
          · by_cases h12 : N ≤ 1075
            · obtain rfl : N = 1075 := by omega
              exact cvx1075
            · obtain rfl : N = 1076 := by omega
              exact cvx1076
    · by_cases h6 : N ≤ 1080
      · by_cases h8 : N ≤ 1078
        · by_cases h10 : N ≤ 1077
          · obtain rfl : N = 1077 := by omega
            exact cvx1077
          · obtain rfl : N = 1078 := by omega
            exact cvx1078
        · by_cases h10 : N ≤ 1079
          · obtain rfl : N = 1079 := by omega
            exact cvx1079
          · obtain rfl : N = 1080 := by omega
            exact cvx1080
      · by_cases h8 : N ≤ 1082
        · by_cases h10 : N ≤ 1081
          · obtain rfl : N = 1081 := by omega
            exact cvx1081
          · obtain rfl : N = 1082 := by omega
            exact cvx1082
        · by_cases h10 : N ≤ 1083
          · obtain rfl : N = 1083 := by omega
            exact cvx1083
          · by_cases h12 : N ≤ 1084
            · obtain rfl : N = 1084 := by omega
              exact cvx1084
            · obtain rfl : N = 1085 := by omega
              exact cvx1085

theorem cen_1050_1085 {N : ℕ} (h1 : 1050 ≤ N) (h2 : N ≤ 1085) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 1066
  · by_cases h4 : N ≤ 1056
    · by_cases h6 : N ≤ 1052
      · by_cases h8 : N ≤ 1050
        · obtain rfl : N = 1050 := by omega
          exact cen1050
        · obtain rfl : N = 1052 := by omega
          exact cen1052
      · by_cases h8 : N ≤ 1054
        · obtain rfl : N = 1054 := by omega
          exact cen1054
        · obtain rfl : N = 1056 := by omega
          exact cen1056
    · by_cases h6 : N ≤ 1060
      · by_cases h8 : N ≤ 1058
        · obtain rfl : N = 1058 := by omega
          exact cen1058
        · obtain rfl : N = 1060 := by omega
          exact cen1060
      · by_cases h8 : N ≤ 1062
        · obtain rfl : N = 1062 := by omega
          exact cen1062
        · by_cases h10 : N ≤ 1064
          · obtain rfl : N = 1064 := by omega
            exact cen1064
          · obtain rfl : N = 1066 := by omega
            exact cen1066
  · by_cases h4 : N ≤ 1074
    · by_cases h6 : N ≤ 1070
      · by_cases h8 : N ≤ 1068
        · obtain rfl : N = 1068 := by omega
          exact cen1068
        · obtain rfl : N = 1070 := by omega
          exact cen1070
      · by_cases h8 : N ≤ 1072
        · obtain rfl : N = 1072 := by omega
          exact cen1072
        · obtain rfl : N = 1074 := by omega
          exact cen1074
    · by_cases h6 : N ≤ 1078
      · by_cases h8 : N ≤ 1076
        · obtain rfl : N = 1076 := by omega
          exact cen1076
        · obtain rfl : N = 1078 := by omega
          exact cen1078
      · by_cases h8 : N ≤ 1080
        · obtain rfl : N = 1080 := by omega
          exact cen1080
        · by_cases h10 : N ≤ 1082
          · obtain rfl : N = 1082 := by omega
            exact cen1082
          · obtain rfl : N = 1084 := by omega
            exact cen1084

end Kagey131.PaperD.T7
