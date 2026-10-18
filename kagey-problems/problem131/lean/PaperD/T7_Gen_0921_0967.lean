import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 921, …, 967` (generated)

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

/-! ### `N = 921` -/

def pL921 : Prm := ⟨75, 35, 37, 923, 11, 18446744073709551616, 184246877666918948, 184246877666918948⟩
def pH921 : Prm := ⟨75, 35, 37, 923, 11, 18446744073709551616, 184249076690174500, 184249076690174500⟩
def pI921 : Prm := ⟨64, 31, 30, 923, 11, 18446744073709551616, 184246877666918948, 184249076690174500⟩
theorem L921_fin : (prmOK pL921 921 && ptTest pL921 (runFrom pL921 (fmask pL921) (cmask pL921) (hmask pL921) 1 920 (true, (init pL921), (init pL921))) 921 461 false) = true := by
  decide +kernel
theorem L921_ok : RunOK pL921 921 (runFrom pL921 (fmask pL921) (cmask pL921) (hmask pL921) 1 920 (true, (init pL921), (init pL921))) ∧ ptTest pL921 (runFrom pL921 (fmask pL921) (cmask pL921) (hmask pL921) 1 920 (true, (init pL921), (init pL921))) 921 461 false = true :=
  fin_run (runOK_init (prmOK_of_and L921_fin) true) (by decide) rfl L921_fin ptTest_fst
theorem H921_fin : (prmOK pH921 921 && ptTest pH921 (runFrom pH921 (fmask pH921) (cmask pH921) (hmask pH921) 1 920 (true, (init pH921), (init pH921))) 921 461 true) = true := by
  decide +kernel
theorem H921_ok : RunOK pH921 921 (runFrom pH921 (fmask pH921) (cmask pH921) (hmask pH921) 1 920 (true, (init pH921), (init pH921))) ∧ ptTest pH921 (runFrom pH921 (fmask pH921) (cmask pH921) (hmask pH921) 1 920 (true, (init pH921), (init pH921))) 921 461 true = true :=
  fin_run (runOK_init (prmOK_of_and H921_fin) true) (by decide) rfl H921_fin ptTest_fst
theorem I921_fin : (prmOK pI921 921 && intTest pI921 (runFrom pI921 (fmask pI921) (cmask pI921) (hmask pI921) 1 920 (true, (init pI921), (init pI921))) 921 17 false) = true := by
  decide +kernel
theorem I921_ok : RunOK pI921 921 (runFrom pI921 (fmask pI921) (cmask pI921) (hmask pI921) 1 920 (true, (init pI921), (init pI921))) ∧ intTest pI921 (runFrom pI921 (fmask pI921) (cmask pI921) (hmask pI921) 1 920 (true, (init pI921), (init pI921))) 921 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I921_fin) true) (by decide) rfl I921_fin intTest_fst
theorem link921 : linkOK pL921 pH921 pI921 = true := by decide +kernel
theorem cvx921 : ConvexBetweenHumps 921 :=
  cvx_of L921_ok H921_ok I921_ok link921 (by decide)

/-! ### `N = 922` -/

def pL922 : Prm := ⟨75, 35, 37, 924, 11, 18446744073709551616, 184088060730511913, 184088060730511913⟩
def pH922 : Prm := ⟨75, 35, 37, 924, 11, 18446744073709551616, 184090259753767465, 184090259753767465⟩
def pI922 : Prm := ⟨64, 31, 30, 924, 11, 18446744073709551616, 184088060730511913, 184090259753767465⟩
theorem L922_fin : (prmOK pL922 922 && ptTest pL922 (runFrom pL922 (fmask pL922) (cmask pL922) (hmask pL922) 1 921 (true, (init pL922), (init pL922))) 922 461 false) = true := by
  decide +kernel
theorem L922_ok : RunOK pL922 922 (runFrom pL922 (fmask pL922) (cmask pL922) (hmask pL922) 1 921 (true, (init pL922), (init pL922))) ∧ ptTest pL922 (runFrom pL922 (fmask pL922) (cmask pL922) (hmask pL922) 1 921 (true, (init pL922), (init pL922))) 922 461 false = true :=
  fin_run (runOK_init (prmOK_of_and L922_fin) true) (by decide) rfl L922_fin ptTest_fst
theorem H922_fin : (prmOK pH922 922 && ptTest pH922 (runFrom pH922 (fmask pH922) (cmask pH922) (hmask pH922) 1 921 (true, (init pH922), (init pH922))) 922 461 true) = true := by
  decide +kernel
theorem H922_ok : RunOK pH922 922 (runFrom pH922 (fmask pH922) (cmask pH922) (hmask pH922) 1 921 (true, (init pH922), (init pH922))) ∧ ptTest pH922 (runFrom pH922 (fmask pH922) (cmask pH922) (hmask pH922) 1 921 (true, (init pH922), (init pH922))) 922 461 true = true :=
  fin_run (runOK_init (prmOK_of_and H922_fin) true) (by decide) rfl H922_fin ptTest_fst
theorem I922_fin : (prmOK pI922 922 && intTest pI922 (runFrom pI922 (fmask pI922) (cmask pI922) (hmask pI922) 1 921 (true, (init pI922), (init pI922))) 922 17 true) = true := by
  decide +kernel
theorem I922_ok : RunOK pI922 922 (runFrom pI922 (fmask pI922) (cmask pI922) (hmask pI922) 1 921 (true, (init pI922), (init pI922))) ∧ intTest pI922 (runFrom pI922 (fmask pI922) (cmask pI922) (hmask pI922) 1 921 (true, (init pI922), (init pI922))) 922 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I922_fin) true) (by decide) rfl I922_fin intTest_fst
theorem link922 : linkOK pL922 pH922 pI922 = true := by decide +kernel
theorem cvx922 : ConvexBetweenHumps 922 :=
  cvx_of L922_ok H922_ok I922_ok link922 (by decide)
theorem cenlink922 : cenLinkOK pI922 922 = true := by decide +kernel
theorem cen922 : CenterUniqueMin 922 ∧ DipHyp 922 ∧ OnePointHyps 922 :=
  cen_of L922_ok H922_ok I922_ok link922 cenlink922

/-! ### `N = 923` -/

def pL923 : Prm := ⟨75, 35, 37, 925, 11, 18446744073709551616, 183929395667347874, 183929395667347874⟩
def pH923 : Prm := ⟨75, 35, 37, 925, 11, 18446744073709551616, 183931594690603426, 183931594690603426⟩
def pI923 : Prm := ⟨64, 31, 30, 925, 11, 18446744073709551616, 183929395667347874, 183931594690603426⟩
theorem L923_fin : (prmOK pL923 923 && ptTest pL923 (runFrom pL923 (fmask pL923) (cmask pL923) (hmask pL923) 1 922 (true, (init pL923), (init pL923))) 923 462 false) = true := by
  decide +kernel
theorem L923_ok : RunOK pL923 923 (runFrom pL923 (fmask pL923) (cmask pL923) (hmask pL923) 1 922 (true, (init pL923), (init pL923))) ∧ ptTest pL923 (runFrom pL923 (fmask pL923) (cmask pL923) (hmask pL923) 1 922 (true, (init pL923), (init pL923))) 923 462 false = true :=
  fin_run (runOK_init (prmOK_of_and L923_fin) true) (by decide) rfl L923_fin ptTest_fst
theorem H923_fin : (prmOK pH923 923 && ptTest pH923 (runFrom pH923 (fmask pH923) (cmask pH923) (hmask pH923) 1 922 (true, (init pH923), (init pH923))) 923 462 true) = true := by
  decide +kernel
theorem H923_ok : RunOK pH923 923 (runFrom pH923 (fmask pH923) (cmask pH923) (hmask pH923) 1 922 (true, (init pH923), (init pH923))) ∧ ptTest pH923 (runFrom pH923 (fmask pH923) (cmask pH923) (hmask pH923) 1 922 (true, (init pH923), (init pH923))) 923 462 true = true :=
  fin_run (runOK_init (prmOK_of_and H923_fin) true) (by decide) rfl H923_fin ptTest_fst
theorem I923_fin : (prmOK pI923 923 && intTest pI923 (runFrom pI923 (fmask pI923) (cmask pI923) (hmask pI923) 1 922 (true, (init pI923), (init pI923))) 923 17 false) = true := by
  decide +kernel
theorem I923_ok : RunOK pI923 923 (runFrom pI923 (fmask pI923) (cmask pI923) (hmask pI923) 1 922 (true, (init pI923), (init pI923))) ∧ intTest pI923 (runFrom pI923 (fmask pI923) (cmask pI923) (hmask pI923) 1 922 (true, (init pI923), (init pI923))) 923 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I923_fin) true) (by decide) rfl I923_fin intTest_fst
theorem link923 : linkOK pL923 pH923 pI923 = true := by decide +kernel
theorem cvx923 : ConvexBetweenHumps 923 :=
  cvx_of L923_ok H923_ok I923_ok link923 (by decide)

/-! ### `N = 924` -/

def pL924 : Prm := ⟨75, 35, 37, 926, 11, 18446744073709551616, 183771177369143631, 183771177369143631⟩
def pH924 : Prm := ⟨75, 35, 37, 926, 11, 18446744073709551616, 183773376392399183, 183773376392399183⟩
def pI924 : Prm := ⟨64, 31, 30, 926, 11, 18446744073709551616, 183771177369143631, 183773376392399183⟩
theorem L924_fin : (prmOK pL924 924 && ptTest pL924 (runFrom pL924 (fmask pL924) (cmask pL924) (hmask pL924) 1 923 (true, (init pL924), (init pL924))) 924 462 false) = true := by
  decide +kernel
theorem L924_ok : RunOK pL924 924 (runFrom pL924 (fmask pL924) (cmask pL924) (hmask pL924) 1 923 (true, (init pL924), (init pL924))) ∧ ptTest pL924 (runFrom pL924 (fmask pL924) (cmask pL924) (hmask pL924) 1 923 (true, (init pL924), (init pL924))) 924 462 false = true :=
  fin_run (runOK_init (prmOK_of_and L924_fin) true) (by decide) rfl L924_fin ptTest_fst
theorem H924_fin : (prmOK pH924 924 && ptTest pH924 (runFrom pH924 (fmask pH924) (cmask pH924) (hmask pH924) 1 923 (true, (init pH924), (init pH924))) 924 462 true) = true := by
  decide +kernel
theorem H924_ok : RunOK pH924 924 (runFrom pH924 (fmask pH924) (cmask pH924) (hmask pH924) 1 923 (true, (init pH924), (init pH924))) ∧ ptTest pH924 (runFrom pH924 (fmask pH924) (cmask pH924) (hmask pH924) 1 923 (true, (init pH924), (init pH924))) 924 462 true = true :=
  fin_run (runOK_init (prmOK_of_and H924_fin) true) (by decide) rfl H924_fin ptTest_fst
theorem I924_fin : (prmOK pI924 924 && intTest pI924 (runFrom pI924 (fmask pI924) (cmask pI924) (hmask pI924) 1 923 (true, (init pI924), (init pI924))) 924 17 true) = true := by
  decide +kernel
theorem I924_ok : RunOK pI924 924 (runFrom pI924 (fmask pI924) (cmask pI924) (hmask pI924) 1 923 (true, (init pI924), (init pI924))) ∧ intTest pI924 (runFrom pI924 (fmask pI924) (cmask pI924) (hmask pI924) 1 923 (true, (init pI924), (init pI924))) 924 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I924_fin) true) (by decide) rfl I924_fin intTest_fst
theorem link924 : linkOK pL924 pH924 pI924 = true := by decide +kernel
theorem cvx924 : ConvexBetweenHumps 924 :=
  cvx_of L924_ok H924_ok I924_ok link924 (by decide)
theorem cenlink924 : cenLinkOK pI924 924 = true := by decide +kernel
theorem cen924 : CenterUniqueMin 924 ∧ DipHyp 924 ∧ OnePointHyps 924 :=
  cen_of L924_ok H924_ok I924_ok link924 cenlink924

/-! ### `N = 925` -/

def pL925 : Prm := ⟨76, 36, 37, 927, 11, 18446744073709551616, 183613110167556012, 183613110167556012⟩
def pH925 : Prm := ⟨75, 35, 37, 927, 11, 18446744073709551616, 183615309190811564, 183615309190811564⟩
def pI925 : Prm := ⟨64, 31, 30, 927, 11, 18446744073709551616, 183613110167556012, 183615309190811564⟩
theorem L925_fin : (prmOK pL925 925 && ptTest pL925 (runFrom pL925 (fmask pL925) (cmask pL925) (hmask pL925) 1 924 (true, (init pL925), (init pL925))) 925 463 false) = true := by
  decide +kernel
theorem L925_ok : RunOK pL925 925 (runFrom pL925 (fmask pL925) (cmask pL925) (hmask pL925) 1 924 (true, (init pL925), (init pL925))) ∧ ptTest pL925 (runFrom pL925 (fmask pL925) (cmask pL925) (hmask pL925) 1 924 (true, (init pL925), (init pL925))) 925 463 false = true :=
  fin_run (runOK_init (prmOK_of_and L925_fin) true) (by decide) rfl L925_fin ptTest_fst
theorem H925_fin : (prmOK pH925 925 && ptTest pH925 (runFrom pH925 (fmask pH925) (cmask pH925) (hmask pH925) 1 924 (true, (init pH925), (init pH925))) 925 463 true) = true := by
  decide +kernel
theorem H925_ok : RunOK pH925 925 (runFrom pH925 (fmask pH925) (cmask pH925) (hmask pH925) 1 924 (true, (init pH925), (init pH925))) ∧ ptTest pH925 (runFrom pH925 (fmask pH925) (cmask pH925) (hmask pH925) 1 924 (true, (init pH925), (init pH925))) 925 463 true = true :=
  fin_run (runOK_init (prmOK_of_and H925_fin) true) (by decide) rfl H925_fin ptTest_fst
theorem I925_fin : (prmOK pI925 925 && intTest pI925 (runFrom pI925 (fmask pI925) (cmask pI925) (hmask pI925) 1 924 (true, (init pI925), (init pI925))) 925 17 false) = true := by
  decide +kernel
theorem I925_ok : RunOK pI925 925 (runFrom pI925 (fmask pI925) (cmask pI925) (hmask pI925) 1 924 (true, (init pI925), (init pI925))) ∧ intTest pI925 (runFrom pI925 (fmask pI925) (cmask pI925) (hmask pI925) 1 924 (true, (init pI925), (init pI925))) 925 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I925_fin) true) (by decide) rfl I925_fin intTest_fst
theorem link925 : linkOK pL925 pH925 pI925 = true := by decide +kernel
theorem cvx925 : ConvexBetweenHumps 925 :=
  cvx_of L925_ok H925_ok I925_ok link925 (by decide)

/-! ### `N = 926` -/

def pL926 : Prm := ⟨75, 35, 37, 928, 11, 18446744073709551616, 183455487011177136, 183455487011177136⟩
def pH926 : Prm := ⟨75, 35, 37, 928, 11, 18446744073709551616, 183457686034432688, 183457686034432688⟩
def pI926 : Prm := ⟨64, 31, 30, 928, 11, 18446744073709551616, 183455487011177136, 183457686034432688⟩
theorem L926_fin : (prmOK pL926 926 && ptTest pL926 (runFrom pL926 (fmask pL926) (cmask pL926) (hmask pL926) 1 925 (true, (init pL926), (init pL926))) 926 463 false) = true := by
  decide +kernel
theorem L926_ok : RunOK pL926 926 (runFrom pL926 (fmask pL926) (cmask pL926) (hmask pL926) 1 925 (true, (init pL926), (init pL926))) ∧ ptTest pL926 (runFrom pL926 (fmask pL926) (cmask pL926) (hmask pL926) 1 925 (true, (init pL926), (init pL926))) 926 463 false = true :=
  fin_run (runOK_init (prmOK_of_and L926_fin) true) (by decide) rfl L926_fin ptTest_fst
theorem H926_fin : (prmOK pH926 926 && ptTest pH926 (runFrom pH926 (fmask pH926) (cmask pH926) (hmask pH926) 1 925 (true, (init pH926), (init pH926))) 926 463 true) = true := by
  decide +kernel
theorem H926_ok : RunOK pH926 926 (runFrom pH926 (fmask pH926) (cmask pH926) (hmask pH926) 1 925 (true, (init pH926), (init pH926))) ∧ ptTest pH926 (runFrom pH926 (fmask pH926) (cmask pH926) (hmask pH926) 1 925 (true, (init pH926), (init pH926))) 926 463 true = true :=
  fin_run (runOK_init (prmOK_of_and H926_fin) true) (by decide) rfl H926_fin ptTest_fst
theorem I926_fin : (prmOK pI926 926 && intTest pI926 (runFrom pI926 (fmask pI926) (cmask pI926) (hmask pI926) 1 925 (true, (init pI926), (init pI926))) 926 17 true) = true := by
  decide +kernel
theorem I926_ok : RunOK pI926 926 (runFrom pI926 (fmask pI926) (cmask pI926) (hmask pI926) 1 925 (true, (init pI926), (init pI926))) ∧ intTest pI926 (runFrom pI926 (fmask pI926) (cmask pI926) (hmask pI926) 1 925 (true, (init pI926), (init pI926))) 926 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I926_fin) true) (by decide) rfl I926_fin intTest_fst
theorem link926 : linkOK pL926 pH926 pI926 = true := by decide +kernel
theorem cvx926 : ConvexBetweenHumps 926 :=
  cvx_of L926_ok H926_ok I926_ok link926 (by decide)
theorem cenlink926 : cenLinkOK pI926 926 = true := by decide +kernel
theorem cen926 : CenterUniqueMin 926 ∧ DipHyp 926 ∧ OnePointHyps 926 :=
  cen_of L926_ok H926_ok I926_ok link926 cenlink926

/-! ### `N = 927` -/

def pL927 : Prm := ⟨75, 35, 37, 929, 11, 18446744073709551616, 183298014180138069, 183298014180138069⟩
def pH927 : Prm := ⟨75, 35, 37, 929, 11, 18446744073709551616, 183300213203393621, 183300213203393621⟩
def pI927 : Prm := ⟨64, 31, 30, 929, 11, 18446744073709551616, 183298014180138069, 183300213203393621⟩
theorem L927_fin : (prmOK pL927 927 && ptTest pL927 (runFrom pL927 (fmask pL927) (cmask pL927) (hmask pL927) 1 926 (true, (init pL927), (init pL927))) 927 464 false) = true := by
  decide +kernel
theorem L927_ok : RunOK pL927 927 (runFrom pL927 (fmask pL927) (cmask pL927) (hmask pL927) 1 926 (true, (init pL927), (init pL927))) ∧ ptTest pL927 (runFrom pL927 (fmask pL927) (cmask pL927) (hmask pL927) 1 926 (true, (init pL927), (init pL927))) 927 464 false = true :=
  fin_run (runOK_init (prmOK_of_and L927_fin) true) (by decide) rfl L927_fin ptTest_fst
theorem H927_fin : (prmOK pH927 927 && ptTest pH927 (runFrom pH927 (fmask pH927) (cmask pH927) (hmask pH927) 1 926 (true, (init pH927), (init pH927))) 927 464 true) = true := by
  decide +kernel
theorem H927_ok : RunOK pH927 927 (runFrom pH927 (fmask pH927) (cmask pH927) (hmask pH927) 1 926 (true, (init pH927), (init pH927))) ∧ ptTest pH927 (runFrom pH927 (fmask pH927) (cmask pH927) (hmask pH927) 1 926 (true, (init pH927), (init pH927))) 927 464 true = true :=
  fin_run (runOK_init (prmOK_of_and H927_fin) true) (by decide) rfl H927_fin ptTest_fst
theorem I927_fin : (prmOK pI927 927 && intTest pI927 (runFrom pI927 (fmask pI927) (cmask pI927) (hmask pI927) 1 926 (true, (init pI927), (init pI927))) 927 17 false) = true := by
  decide +kernel
theorem I927_ok : RunOK pI927 927 (runFrom pI927 (fmask pI927) (cmask pI927) (hmask pI927) 1 926 (true, (init pI927), (init pI927))) ∧ intTest pI927 (runFrom pI927 (fmask pI927) (cmask pI927) (hmask pI927) 1 926 (true, (init pI927), (init pI927))) 927 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I927_fin) true) (by decide) rfl I927_fin intTest_fst
theorem link927 : linkOK pL927 pH927 pI927 = true := by decide +kernel
theorem cvx927 : ConvexBetweenHumps 927 :=
  cvx_of L927_ok H927_ok I927_ok link927 (by decide)

/-! ### `N = 928` -/

def pL928 : Prm := ⟨75, 35, 37, 930, 11, 18446744073709551616, 183140982696895697, 183140982696895697⟩
def pH928 : Prm := ⟨75, 35, 37, 930, 11, 18446744073709551616, 183143181720151249, 183143181720151249⟩
def pI928 : Prm := ⟨64, 31, 30, 930, 11, 18446744073709551616, 183140982696895697, 183143181720151249⟩
theorem L928_fin : (prmOK pL928 928 && ptTest pL928 (runFrom pL928 (fmask pL928) (cmask pL928) (hmask pL928) 1 927 (true, (init pL928), (init pL928))) 928 464 false) = true := by
  decide +kernel
theorem L928_ok : RunOK pL928 928 (runFrom pL928 (fmask pL928) (cmask pL928) (hmask pL928) 1 927 (true, (init pL928), (init pL928))) ∧ ptTest pL928 (runFrom pL928 (fmask pL928) (cmask pL928) (hmask pL928) 1 927 (true, (init pL928), (init pL928))) 928 464 false = true :=
  fin_run (runOK_init (prmOK_of_and L928_fin) true) (by decide) rfl L928_fin ptTest_fst
theorem H928_fin : (prmOK pH928 928 && ptTest pH928 (runFrom pH928 (fmask pH928) (cmask pH928) (hmask pH928) 1 927 (true, (init pH928), (init pH928))) 928 464 true) = true := by
  decide +kernel
theorem H928_ok : RunOK pH928 928 (runFrom pH928 (fmask pH928) (cmask pH928) (hmask pH928) 1 927 (true, (init pH928), (init pH928))) ∧ ptTest pH928 (runFrom pH928 (fmask pH928) (cmask pH928) (hmask pH928) 1 927 (true, (init pH928), (init pH928))) 928 464 true = true :=
  fin_run (runOK_init (prmOK_of_and H928_fin) true) (by decide) rfl H928_fin ptTest_fst
theorem I928_fin : (prmOK pI928 928 && intTest pI928 (runFrom pI928 (fmask pI928) (cmask pI928) (hmask pI928) 1 927 (true, (init pI928), (init pI928))) 928 17 true) = true := by
  decide +kernel
theorem I928_ok : RunOK pI928 928 (runFrom pI928 (fmask pI928) (cmask pI928) (hmask pI928) 1 927 (true, (init pI928), (init pI928))) ∧ intTest pI928 (runFrom pI928 (fmask pI928) (cmask pI928) (hmask pI928) 1 927 (true, (init pI928), (init pI928))) 928 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I928_fin) true) (by decide) rfl I928_fin intTest_fst
theorem link928 : linkOK pL928 pH928 pI928 = true := by decide +kernel
theorem cvx928 : ConvexBetweenHumps 928 :=
  cvx_of L928_ok H928_ok I928_ok link928 (by decide)
theorem cenlink928 : cenLinkOK pI928 928 = true := by decide +kernel
theorem cen928 : CenterUniqueMin 928 ∧ DipHyp 928 ∧ OnePointHyps 928 :=
  cen_of L928_ok H928_ok I928_ok link928 cenlink928

/-! ### `N = 929` -/

def pL929 : Prm := ⟨75, 35, 37, 931, 11, 18446744073709551616, 182984100773028980, 182984100773028980⟩
def pH929 : Prm := ⟨76, 36, 37, 931, 11, 18446744073709551616, 182986299796284532, 182986299796284532⟩
def pI929 : Prm := ⟨64, 31, 30, 931, 11, 18446744073709551616, 182984100773028980, 182986299796284532⟩
theorem L929_fin : (prmOK pL929 929 && ptTest pL929 (runFrom pL929 (fmask pL929) (cmask pL929) (hmask pL929) 1 928 (true, (init pL929), (init pL929))) 929 465 false) = true := by
  decide +kernel
theorem L929_ok : RunOK pL929 929 (runFrom pL929 (fmask pL929) (cmask pL929) (hmask pL929) 1 928 (true, (init pL929), (init pL929))) ∧ ptTest pL929 (runFrom pL929 (fmask pL929) (cmask pL929) (hmask pL929) 1 928 (true, (init pL929), (init pL929))) 929 465 false = true :=
  fin_run (runOK_init (prmOK_of_and L929_fin) true) (by decide) rfl L929_fin ptTest_fst
theorem H929_fin : (prmOK pH929 929 && ptTest pH929 (runFrom pH929 (fmask pH929) (cmask pH929) (hmask pH929) 1 928 (true, (init pH929), (init pH929))) 929 465 true) = true := by
  decide +kernel
theorem H929_ok : RunOK pH929 929 (runFrom pH929 (fmask pH929) (cmask pH929) (hmask pH929) 1 928 (true, (init pH929), (init pH929))) ∧ ptTest pH929 (runFrom pH929 (fmask pH929) (cmask pH929) (hmask pH929) 1 928 (true, (init pH929), (init pH929))) 929 465 true = true :=
  fin_run (runOK_init (prmOK_of_and H929_fin) true) (by decide) rfl H929_fin ptTest_fst
theorem I929_fin : (prmOK pI929 929 && intTest pI929 (runFrom pI929 (fmask pI929) (cmask pI929) (hmask pI929) 1 928 (true, (init pI929), (init pI929))) 929 17 false) = true := by
  decide +kernel
theorem I929_ok : RunOK pI929 929 (runFrom pI929 (fmask pI929) (cmask pI929) (hmask pI929) 1 928 (true, (init pI929), (init pI929))) ∧ intTest pI929 (runFrom pI929 (fmask pI929) (cmask pI929) (hmask pI929) 1 928 (true, (init pI929), (init pI929))) 929 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I929_fin) true) (by decide) rfl I929_fin intTest_fst
theorem link929 : linkOK pL929 pH929 pI929 = true := by decide +kernel
theorem cvx929 : ConvexBetweenHumps 929 :=
  cvx_of L929_ok H929_ok I929_ok link929 (by decide)

/-! ### `N = 930` -/

def pL930 : Prm := ⟨75, 35, 37, 932, 11, 18446744073709551616, 182827657521664561, 182827657521664561⟩
def pH930 : Prm := ⟨76, 36, 37, 932, 11, 18446744073709551616, 182829856544920113, 182829856544920113⟩
def pI930 : Prm := ⟨64, 31, 30, 932, 11, 18446744073709551616, 182827657521664561, 182829856544920113⟩
theorem L930_fin : (prmOK pL930 930 && ptTest pL930 (runFrom pL930 (fmask pL930) (cmask pL930) (hmask pL930) 1 929 (true, (init pL930), (init pL930))) 930 465 false) = true := by
  decide +kernel
theorem L930_ok : RunOK pL930 930 (runFrom pL930 (fmask pL930) (cmask pL930) (hmask pL930) 1 929 (true, (init pL930), (init pL930))) ∧ ptTest pL930 (runFrom pL930 (fmask pL930) (cmask pL930) (hmask pL930) 1 929 (true, (init pL930), (init pL930))) 930 465 false = true :=
  fin_run (runOK_init (prmOK_of_and L930_fin) true) (by decide) rfl L930_fin ptTest_fst
theorem H930_fin : (prmOK pH930 930 && ptTest pH930 (runFrom pH930 (fmask pH930) (cmask pH930) (hmask pH930) 1 929 (true, (init pH930), (init pH930))) 930 465 true) = true := by
  decide +kernel
theorem H930_ok : RunOK pH930 930 (runFrom pH930 (fmask pH930) (cmask pH930) (hmask pH930) 1 929 (true, (init pH930), (init pH930))) ∧ ptTest pH930 (runFrom pH930 (fmask pH930) (cmask pH930) (hmask pH930) 1 929 (true, (init pH930), (init pH930))) 930 465 true = true :=
  fin_run (runOK_init (prmOK_of_and H930_fin) true) (by decide) rfl H930_fin ptTest_fst
theorem I930_fin : (prmOK pI930 930 && intTest pI930 (runFrom pI930 (fmask pI930) (cmask pI930) (hmask pI930) 1 929 (true, (init pI930), (init pI930))) 930 17 true) = true := by
  decide +kernel
theorem I930_ok : RunOK pI930 930 (runFrom pI930 (fmask pI930) (cmask pI930) (hmask pI930) 1 929 (true, (init pI930), (init pI930))) ∧ intTest pI930 (runFrom pI930 (fmask pI930) (cmask pI930) (hmask pI930) 1 929 (true, (init pI930), (init pI930))) 930 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I930_fin) true) (by decide) rfl I930_fin intTest_fst
theorem link930 : linkOK pL930 pH930 pI930 = true := by decide +kernel
theorem cvx930 : ConvexBetweenHumps 930 :=
  cvx_of L930_ok H930_ok I930_ok link930 (by decide)
theorem cenlink930 : cenLinkOK pI930 930 = true := by decide +kernel
theorem cen930 : CenterUniqueMin 930 ∧ DipHyp 930 ∧ OnePointHyps 930 :=
  cen_of L930_ok H930_ok I930_ok link930 cenlink930

/-! ### `N = 931` -/

def pL931 : Prm := ⟨75, 35, 37, 933, 11, 18446744073709551616, 182671363068968963, 182671363068968963⟩
def pH931 : Prm := ⟨75, 35, 37, 933, 11, 18446744073709551616, 182673562092224515, 182673562092224515⟩
def pI931 : Prm := ⟨65, 31, 31, 933, 11, 18446744073709551616, 182671363068968963, 182673562092224515⟩
theorem L931_fin : (prmOK pL931 931 && ptTest pL931 (runFrom pL931 (fmask pL931) (cmask pL931) (hmask pL931) 1 930 (true, (init pL931), (init pL931))) 931 466 false) = true := by
  decide +kernel
theorem L931_ok : RunOK pL931 931 (runFrom pL931 (fmask pL931) (cmask pL931) (hmask pL931) 1 930 (true, (init pL931), (init pL931))) ∧ ptTest pL931 (runFrom pL931 (fmask pL931) (cmask pL931) (hmask pL931) 1 930 (true, (init pL931), (init pL931))) 931 466 false = true :=
  fin_run (runOK_init (prmOK_of_and L931_fin) true) (by decide) rfl L931_fin ptTest_fst
theorem H931_fin : (prmOK pH931 931 && ptTest pH931 (runFrom pH931 (fmask pH931) (cmask pH931) (hmask pH931) 1 930 (true, (init pH931), (init pH931))) 931 466 true) = true := by
  decide +kernel
theorem H931_ok : RunOK pH931 931 (runFrom pH931 (fmask pH931) (cmask pH931) (hmask pH931) 1 930 (true, (init pH931), (init pH931))) ∧ ptTest pH931 (runFrom pH931 (fmask pH931) (cmask pH931) (hmask pH931) 1 930 (true, (init pH931), (init pH931))) 931 466 true = true :=
  fin_run (runOK_init (prmOK_of_and H931_fin) true) (by decide) rfl H931_fin ptTest_fst
theorem I931_fin : (prmOK pI931 931 && intTest pI931 (runFrom pI931 (fmask pI931) (cmask pI931) (hmask pI931) 1 930 (true, (init pI931), (init pI931))) 931 17 false) = true := by
  decide +kernel
theorem I931_ok : RunOK pI931 931 (runFrom pI931 (fmask pI931) (cmask pI931) (hmask pI931) 1 930 (true, (init pI931), (init pI931))) ∧ intTest pI931 (runFrom pI931 (fmask pI931) (cmask pI931) (hmask pI931) 1 930 (true, (init pI931), (init pI931))) 931 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I931_fin) true) (by decide) rfl I931_fin intTest_fst
theorem link931 : linkOK pL931 pH931 pI931 = true := by decide +kernel
theorem cvx931 : ConvexBetweenHumps 931 :=
  cvx_of L931_ok H931_ok I931_ok link931 (by decide)

/-! ### `N = 932` -/

def pL932 : Prm := ⟨75, 35, 37, 934, 11, 18446744073709551616, 182515504635322207, 182515504635322207⟩
def pH932 : Prm := ⟨75, 35, 37, 934, 11, 18446744073709551616, 182517703658577759, 182517703658577759⟩
def pI932 : Prm := ⟨64, 31, 30, 934, 11, 18446744073709551616, 182515504635322207, 182517703658577759⟩
theorem L932_fin : (prmOK pL932 932 && ptTest pL932 (runFrom pL932 (fmask pL932) (cmask pL932) (hmask pL932) 1 931 (true, (init pL932), (init pL932))) 932 466 false) = true := by
  decide +kernel
theorem L932_ok : RunOK pL932 932 (runFrom pL932 (fmask pL932) (cmask pL932) (hmask pL932) 1 931 (true, (init pL932), (init pL932))) ∧ ptTest pL932 (runFrom pL932 (fmask pL932) (cmask pL932) (hmask pL932) 1 931 (true, (init pL932), (init pL932))) 932 466 false = true :=
  fin_run (runOK_init (prmOK_of_and L932_fin) true) (by decide) rfl L932_fin ptTest_fst
theorem H932_fin : (prmOK pH932 932 && ptTest pH932 (runFrom pH932 (fmask pH932) (cmask pH932) (hmask pH932) 1 931 (true, (init pH932), (init pH932))) 932 466 true) = true := by
  decide +kernel
theorem H932_ok : RunOK pH932 932 (runFrom pH932 (fmask pH932) (cmask pH932) (hmask pH932) 1 931 (true, (init pH932), (init pH932))) ∧ ptTest pH932 (runFrom pH932 (fmask pH932) (cmask pH932) (hmask pH932) 1 931 (true, (init pH932), (init pH932))) 932 466 true = true :=
  fin_run (runOK_init (prmOK_of_and H932_fin) true) (by decide) rfl H932_fin ptTest_fst
theorem I932_fin : (prmOK pI932 932 && intTest pI932 (runFrom pI932 (fmask pI932) (cmask pI932) (hmask pI932) 1 931 (true, (init pI932), (init pI932))) 932 17 true) = true := by
  decide +kernel
theorem I932_ok : RunOK pI932 932 (runFrom pI932 (fmask pI932) (cmask pI932) (hmask pI932) 1 931 (true, (init pI932), (init pI932))) ∧ intTest pI932 (runFrom pI932 (fmask pI932) (cmask pI932) (hmask pI932) 1 931 (true, (init pI932), (init pI932))) 932 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I932_fin) true) (by decide) rfl I932_fin intTest_fst
theorem link932 : linkOK pL932 pH932 pI932 = true := by decide +kernel
theorem cvx932 : ConvexBetweenHumps 932 :=
  cvx_of L932_ok H932_ok I932_ok link932 (by decide)
theorem cenlink932 : cenLinkOK pI932 932 = true := by decide +kernel
theorem cen932 : CenterUniqueMin 932 ∧ DipHyp 932 ∧ OnePointHyps 932 :=
  cen_of L932_ok H932_ok I932_ok link932 cenlink932

/-! ### `N = 933` -/

def pL933 : Prm := ⟨75, 35, 37, 935, 11, 18446744073709551616, 182359794244876317, 182359794244876317⟩
def pH933 : Prm := ⟨75, 35, 37, 935, 11, 18446744073709551616, 182361993268131869, 182361993268131869⟩
def pI933 : Prm := ⟨64, 31, 30, 935, 11, 18446744073709551616, 182359794244876317, 182361993268131869⟩
theorem L933_fin : (prmOK pL933 933 && ptTest pL933 (runFrom pL933 (fmask pL933) (cmask pL933) (hmask pL933) 1 932 (true, (init pL933), (init pL933))) 933 467 false) = true := by
  decide +kernel
theorem L933_ok : RunOK pL933 933 (runFrom pL933 (fmask pL933) (cmask pL933) (hmask pL933) 1 932 (true, (init pL933), (init pL933))) ∧ ptTest pL933 (runFrom pL933 (fmask pL933) (cmask pL933) (hmask pL933) 1 932 (true, (init pL933), (init pL933))) 933 467 false = true :=
  fin_run (runOK_init (prmOK_of_and L933_fin) true) (by decide) rfl L933_fin ptTest_fst
theorem H933_fin : (prmOK pH933 933 && ptTest pH933 (runFrom pH933 (fmask pH933) (cmask pH933) (hmask pH933) 1 932 (true, (init pH933), (init pH933))) 933 467 true) = true := by
  decide +kernel
theorem H933_ok : RunOK pH933 933 (runFrom pH933 (fmask pH933) (cmask pH933) (hmask pH933) 1 932 (true, (init pH933), (init pH933))) ∧ ptTest pH933 (runFrom pH933 (fmask pH933) (cmask pH933) (hmask pH933) 1 932 (true, (init pH933), (init pH933))) 933 467 true = true :=
  fin_run (runOK_init (prmOK_of_and H933_fin) true) (by decide) rfl H933_fin ptTest_fst
theorem I933_fin : (prmOK pI933 933 && intTest pI933 (runFrom pI933 (fmask pI933) (cmask pI933) (hmask pI933) 1 932 (true, (init pI933), (init pI933))) 933 17 false) = true := by
  decide +kernel
theorem I933_ok : RunOK pI933 933 (runFrom pI933 (fmask pI933) (cmask pI933) (hmask pI933) 1 932 (true, (init pI933), (init pI933))) ∧ intTest pI933 (runFrom pI933 (fmask pI933) (cmask pI933) (hmask pI933) 1 932 (true, (init pI933), (init pI933))) 933 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I933_fin) true) (by decide) rfl I933_fin intTest_fst
theorem link933 : linkOK pL933 pH933 pI933 = true := by decide +kernel
theorem cvx933 : ConvexBetweenHumps 933 :=
  cvx_of L933_ok H933_ok I933_ok link933 (by decide)

/-! ### `N = 934` -/

def pL934 : Prm := ⟨76, 36, 37, 936, 11, 18446744073709551616, 182204517241682293, 182204517241682293⟩
def pH934 : Prm := ⟨75, 35, 37, 936, 11, 18446744073709551616, 182206716264937845, 182206716264937845⟩
def pI934 : Prm := ⟨65, 31, 31, 936, 11, 18446744073709551616, 182204517241682293, 182206716264937845⟩
theorem L934_fin : (prmOK pL934 934 && ptTest pL934 (runFrom pL934 (fmask pL934) (cmask pL934) (hmask pL934) 1 933 (true, (init pL934), (init pL934))) 934 467 false) = true := by
  decide +kernel
theorem L934_ok : RunOK pL934 934 (runFrom pL934 (fmask pL934) (cmask pL934) (hmask pL934) 1 933 (true, (init pL934), (init pL934))) ∧ ptTest pL934 (runFrom pL934 (fmask pL934) (cmask pL934) (hmask pL934) 1 933 (true, (init pL934), (init pL934))) 934 467 false = true :=
  fin_run (runOK_init (prmOK_of_and L934_fin) true) (by decide) rfl L934_fin ptTest_fst
theorem H934_fin : (prmOK pH934 934 && ptTest pH934 (runFrom pH934 (fmask pH934) (cmask pH934) (hmask pH934) 1 933 (true, (init pH934), (init pH934))) 934 467 true) = true := by
  decide +kernel
theorem H934_ok : RunOK pH934 934 (runFrom pH934 (fmask pH934) (cmask pH934) (hmask pH934) 1 933 (true, (init pH934), (init pH934))) ∧ ptTest pH934 (runFrom pH934 (fmask pH934) (cmask pH934) (hmask pH934) 1 933 (true, (init pH934), (init pH934))) 934 467 true = true :=
  fin_run (runOK_init (prmOK_of_and H934_fin) true) (by decide) rfl H934_fin ptTest_fst
theorem I934_fin : (prmOK pI934 934 && intTest pI934 (runFrom pI934 (fmask pI934) (cmask pI934) (hmask pI934) 1 933 (true, (init pI934), (init pI934))) 934 17 true) = true := by
  decide +kernel
theorem I934_ok : RunOK pI934 934 (runFrom pI934 (fmask pI934) (cmask pI934) (hmask pI934) 1 933 (true, (init pI934), (init pI934))) ∧ intTest pI934 (runFrom pI934 (fmask pI934) (cmask pI934) (hmask pI934) 1 933 (true, (init pI934), (init pI934))) 934 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I934_fin) true) (by decide) rfl I934_fin intTest_fst
theorem link934 : linkOK pL934 pH934 pI934 = true := by decide +kernel
theorem cvx934 : ConvexBetweenHumps 934 :=
  cvx_of L934_ok H934_ok I934_ok link934 (by decide)
theorem cenlink934 : cenLinkOK pI934 934 = true := by decide +kernel
theorem cen934 : CenterUniqueMin 934 ∧ DipHyp 934 ∧ OnePointHyps 934 :=
  cen_of L934_ok H934_ok I934_ok link934 cenlink934

/-! ### `N = 935` -/

def pL935 : Prm := ⟨76, 36, 37, 937, 11, 18446744073709551616, 182049387531367818, 182049387531367818⟩
def pH935 : Prm := ⟨76, 36, 37, 937, 11, 18446744073709551616, 182051586554623370, 182051586554623370⟩
def pI935 : Prm := ⟨65, 31, 31, 937, 11, 18446744073709551616, 182049387531367818, 182051586554623370⟩
theorem L935_fin : (prmOK pL935 935 && ptTest pL935 (runFrom pL935 (fmask pL935) (cmask pL935) (hmask pL935) 1 934 (true, (init pL935), (init pL935))) 935 468 false) = true := by
  decide +kernel
theorem L935_ok : RunOK pL935 935 (runFrom pL935 (fmask pL935) (cmask pL935) (hmask pL935) 1 934 (true, (init pL935), (init pL935))) ∧ ptTest pL935 (runFrom pL935 (fmask pL935) (cmask pL935) (hmask pL935) 1 934 (true, (init pL935), (init pL935))) 935 468 false = true :=
  fin_run (runOK_init (prmOK_of_and L935_fin) true) (by decide) rfl L935_fin ptTest_fst
theorem H935_fin : (prmOK pH935 935 && ptTest pH935 (runFrom pH935 (fmask pH935) (cmask pH935) (hmask pH935) 1 934 (true, (init pH935), (init pH935))) 935 468 true) = true := by
  decide +kernel
theorem H935_ok : RunOK pH935 935 (runFrom pH935 (fmask pH935) (cmask pH935) (hmask pH935) 1 934 (true, (init pH935), (init pH935))) ∧ ptTest pH935 (runFrom pH935 (fmask pH935) (cmask pH935) (hmask pH935) 1 934 (true, (init pH935), (init pH935))) 935 468 true = true :=
  fin_run (runOK_init (prmOK_of_and H935_fin) true) (by decide) rfl H935_fin ptTest_fst
theorem I935_fin : (prmOK pI935 935 && intTest pI935 (runFrom pI935 (fmask pI935) (cmask pI935) (hmask pI935) 1 934 (true, (init pI935), (init pI935))) 935 17 false) = true := by
  decide +kernel
theorem I935_ok : RunOK pI935 935 (runFrom pI935 (fmask pI935) (cmask pI935) (hmask pI935) 1 934 (true, (init pI935), (init pI935))) ∧ intTest pI935 (runFrom pI935 (fmask pI935) (cmask pI935) (hmask pI935) 1 934 (true, (init pI935), (init pI935))) 935 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I935_fin) true) (by decide) rfl I935_fin intTest_fst
theorem link935 : linkOK pL935 pH935 pI935 = true := by decide +kernel
theorem cvx935 : ConvexBetweenHumps 935 :=
  cvx_of L935_ok H935_ok I935_ok link935 (by decide)

/-! ### `N = 936` -/

def pL936 : Prm := ⟨76, 36, 37, 938, 11, 18446744073709551616, 181894688597943349, 181894688597943349⟩
def pH936 : Prm := ⟨76, 36, 37, 938, 11, 18446744073709551616, 181896887621198901, 181896887621198901⟩
def pI936 : Prm := ⟨65, 31, 31, 938, 11, 18446744073709551616, 181894688597943349, 181896887621198901⟩
theorem L936_fin : (prmOK pL936 936 && ptTest pL936 (runFrom pL936 (fmask pL936) (cmask pL936) (hmask pL936) 1 935 (true, (init pL936), (init pL936))) 936 468 false) = true := by
  decide +kernel
theorem L936_ok : RunOK pL936 936 (runFrom pL936 (fmask pL936) (cmask pL936) (hmask pL936) 1 935 (true, (init pL936), (init pL936))) ∧ ptTest pL936 (runFrom pL936 (fmask pL936) (cmask pL936) (hmask pL936) 1 935 (true, (init pL936), (init pL936))) 936 468 false = true :=
  fin_run (runOK_init (prmOK_of_and L936_fin) true) (by decide) rfl L936_fin ptTest_fst
theorem H936_fin : (prmOK pH936 936 && ptTest pH936 (runFrom pH936 (fmask pH936) (cmask pH936) (hmask pH936) 1 935 (true, (init pH936), (init pH936))) 936 468 true) = true := by
  decide +kernel
theorem H936_ok : RunOK pH936 936 (runFrom pH936 (fmask pH936) (cmask pH936) (hmask pH936) 1 935 (true, (init pH936), (init pH936))) ∧ ptTest pH936 (runFrom pH936 (fmask pH936) (cmask pH936) (hmask pH936) 1 935 (true, (init pH936), (init pH936))) 936 468 true = true :=
  fin_run (runOK_init (prmOK_of_and H936_fin) true) (by decide) rfl H936_fin ptTest_fst
theorem I936_fin : (prmOK pI936 936 && intTest pI936 (runFrom pI936 (fmask pI936) (cmask pI936) (hmask pI936) 1 935 (true, (init pI936), (init pI936))) 936 17 true) = true := by
  decide +kernel
theorem I936_ok : RunOK pI936 936 (runFrom pI936 (fmask pI936) (cmask pI936) (hmask pI936) 1 935 (true, (init pI936), (init pI936))) ∧ intTest pI936 (runFrom pI936 (fmask pI936) (cmask pI936) (hmask pI936) 1 935 (true, (init pI936), (init pI936))) 936 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I936_fin) true) (by decide) rfl I936_fin intTest_fst
theorem link936 : linkOK pL936 pH936 pI936 = true := by decide +kernel
theorem cvx936 : ConvexBetweenHumps 936 :=
  cvx_of L936_ok H936_ok I936_ok link936 (by decide)
theorem cenlink936 : cenLinkOK pI936 936 = true := by decide +kernel
theorem cen936 : CenterUniqueMin 936 ∧ DipHyp 936 ∧ OnePointHyps 936 :=
  cen_of L936_ok H936_ok I936_ok link936 cenlink936

/-! ### `N = 937` -/

def pL937 : Prm := ⟨76, 36, 37, 939, 11, 18446744073709551616, 181740136212223757, 181740136212223757⟩
def pH937 : Prm := ⟨76, 36, 37, 939, 11, 18446744073709551616, 181742335235479309, 181742335235479309⟩
def pI937 : Prm := ⟨64, 31, 30, 939, 11, 18446744073709551616, 181740136212223757, 181742335235479309⟩
theorem L937_fin : (prmOK pL937 937 && ptTest pL937 (runFrom pL937 (fmask pL937) (cmask pL937) (hmask pL937) 1 936 (true, (init pL937), (init pL937))) 937 469 false) = true := by
  decide +kernel
theorem L937_ok : RunOK pL937 937 (runFrom pL937 (fmask pL937) (cmask pL937) (hmask pL937) 1 936 (true, (init pL937), (init pL937))) ∧ ptTest pL937 (runFrom pL937 (fmask pL937) (cmask pL937) (hmask pL937) 1 936 (true, (init pL937), (init pL937))) 937 469 false = true :=
  fin_run (runOK_init (prmOK_of_and L937_fin) true) (by decide) rfl L937_fin ptTest_fst
theorem H937_fin : (prmOK pH937 937 && ptTest pH937 (runFrom pH937 (fmask pH937) (cmask pH937) (hmask pH937) 1 936 (true, (init pH937), (init pH937))) 937 469 true) = true := by
  decide +kernel
theorem H937_ok : RunOK pH937 937 (runFrom pH937 (fmask pH937) (cmask pH937) (hmask pH937) 1 936 (true, (init pH937), (init pH937))) ∧ ptTest pH937 (runFrom pH937 (fmask pH937) (cmask pH937) (hmask pH937) 1 936 (true, (init pH937), (init pH937))) 937 469 true = true :=
  fin_run (runOK_init (prmOK_of_and H937_fin) true) (by decide) rfl H937_fin ptTest_fst
theorem I937_fin : (prmOK pI937 937 && intTest pI937 (runFrom pI937 (fmask pI937) (cmask pI937) (hmask pI937) 1 936 (true, (init pI937), (init pI937))) 937 17 false) = true := by
  decide +kernel
theorem I937_ok : RunOK pI937 937 (runFrom pI937 (fmask pI937) (cmask pI937) (hmask pI937) 1 936 (true, (init pI937), (init pI937))) ∧ intTest pI937 (runFrom pI937 (fmask pI937) (cmask pI937) (hmask pI937) 1 936 (true, (init pI937), (init pI937))) 937 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I937_fin) true) (by decide) rfl I937_fin intTest_fst
theorem link937 : linkOK pL937 pH937 pI937 = true := by decide +kernel
theorem cvx937 : ConvexBetweenHumps 937 :=
  cvx_of L937_ok H937_ok I937_ok link937 (by decide)

/-! ### `N = 938` -/

def pL938 : Prm := ⟨76, 36, 37, 940, 11, 18446744073709551616, 181586012014209171, 181586012014209171⟩
def pH938 : Prm := ⟨76, 36, 37, 940, 11, 18446744073709551616, 181588211037464723, 181588211037464723⟩
def pI938 : Prm := ⟨65, 31, 31, 940, 11, 18446744073709551616, 181586012014209171, 181588211037464723⟩
theorem L938_fin : (prmOK pL938 938 && ptTest pL938 (runFrom pL938 (fmask pL938) (cmask pL938) (hmask pL938) 1 937 (true, (init pL938), (init pL938))) 938 469 false) = true := by
  decide +kernel
theorem L938_ok : RunOK pL938 938 (runFrom pL938 (fmask pL938) (cmask pL938) (hmask pL938) 1 937 (true, (init pL938), (init pL938))) ∧ ptTest pL938 (runFrom pL938 (fmask pL938) (cmask pL938) (hmask pL938) 1 937 (true, (init pL938), (init pL938))) 938 469 false = true :=
  fin_run (runOK_init (prmOK_of_and L938_fin) true) (by decide) rfl L938_fin ptTest_fst
theorem H938_fin : (prmOK pH938 938 && ptTest pH938 (runFrom pH938 (fmask pH938) (cmask pH938) (hmask pH938) 1 937 (true, (init pH938), (init pH938))) 938 469 true) = true := by
  decide +kernel
theorem H938_ok : RunOK pH938 938 (runFrom pH938 (fmask pH938) (cmask pH938) (hmask pH938) 1 937 (true, (init pH938), (init pH938))) ∧ ptTest pH938 (runFrom pH938 (fmask pH938) (cmask pH938) (hmask pH938) 1 937 (true, (init pH938), (init pH938))) 938 469 true = true :=
  fin_run (runOK_init (prmOK_of_and H938_fin) true) (by decide) rfl H938_fin ptTest_fst
theorem I938_fin : (prmOK pI938 938 && intTest pI938 (runFrom pI938 (fmask pI938) (cmask pI938) (hmask pI938) 1 937 (true, (init pI938), (init pI938))) 938 17 true) = true := by
  decide +kernel
theorem I938_ok : RunOK pI938 938 (runFrom pI938 (fmask pI938) (cmask pI938) (hmask pI938) 1 937 (true, (init pI938), (init pI938))) ∧ intTest pI938 (runFrom pI938 (fmask pI938) (cmask pI938) (hmask pI938) 1 937 (true, (init pI938), (init pI938))) 938 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I938_fin) true) (by decide) rfl I938_fin intTest_fst
theorem link938 : linkOK pL938 pH938 pI938 = true := by decide +kernel
theorem cvx938 : ConvexBetweenHumps 938 :=
  cvx_of L938_ok H938_ok I938_ok link938 (by decide)
theorem cenlink938 : cenLinkOK pI938 938 = true := by decide +kernel
theorem cen938 : CenterUniqueMin 938 ∧ DipHyp 938 ∧ OnePointHyps 938 :=
  cen_of L938_ok H938_ok I938_ok link938 cenlink938

/-! ### `N = 939` -/

def pL939 : Prm := ⟨76, 36, 37, 941, 11, 18446744073709551616, 181432033623816090, 181432033623816090⟩
def pH939 : Prm := ⟨76, 36, 37, 941, 11, 18446744073709551616, 181434232647071642, 181434232647071642⟩
def pI939 : Prm := ⟨65, 31, 31, 941, 11, 18446744073709551616, 181432033623816090, 181434232647071642⟩
theorem L939_fin : (prmOK pL939 939 && ptTest pL939 (runFrom pL939 (fmask pL939) (cmask pL939) (hmask pL939) 1 938 (true, (init pL939), (init pL939))) 939 470 false) = true := by
  decide +kernel
theorem L939_ok : RunOK pL939 939 (runFrom pL939 (fmask pL939) (cmask pL939) (hmask pL939) 1 938 (true, (init pL939), (init pL939))) ∧ ptTest pL939 (runFrom pL939 (fmask pL939) (cmask pL939) (hmask pL939) 1 938 (true, (init pL939), (init pL939))) 939 470 false = true :=
  fin_run (runOK_init (prmOK_of_and L939_fin) true) (by decide) rfl L939_fin ptTest_fst
theorem H939_fin : (prmOK pH939 939 && ptTest pH939 (runFrom pH939 (fmask pH939) (cmask pH939) (hmask pH939) 1 938 (true, (init pH939), (init pH939))) 939 470 true) = true := by
  decide +kernel
theorem H939_ok : RunOK pH939 939 (runFrom pH939 (fmask pH939) (cmask pH939) (hmask pH939) 1 938 (true, (init pH939), (init pH939))) ∧ ptTest pH939 (runFrom pH939 (fmask pH939) (cmask pH939) (hmask pH939) 1 938 (true, (init pH939), (init pH939))) 939 470 true = true :=
  fin_run (runOK_init (prmOK_of_and H939_fin) true) (by decide) rfl H939_fin ptTest_fst
theorem I939_fin : (prmOK pI939 939 && intTest pI939 (runFrom pI939 (fmask pI939) (cmask pI939) (hmask pI939) 1 938 (true, (init pI939), (init pI939))) 939 17 false) = true := by
  decide +kernel
theorem I939_ok : RunOK pI939 939 (runFrom pI939 (fmask pI939) (cmask pI939) (hmask pI939) 1 938 (true, (init pI939), (init pI939))) ∧ intTest pI939 (runFrom pI939 (fmask pI939) (cmask pI939) (hmask pI939) 1 938 (true, (init pI939), (init pI939))) 939 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I939_fin) true) (by decide) rfl I939_fin intTest_fst
theorem link939 : linkOK pL939 pH939 pI939 = true := by decide +kernel
theorem cvx939 : ConvexBetweenHumps 939 :=
  cvx_of L939_ok H939_ok I939_ok link939 (by decide)

/-! ### `N = 940` -/

def pL940 : Prm := ⟨76, 36, 37, 942, 11, 18446744073709551616, 181278480852935411, 181278480852935411⟩
def pH940 : Prm := ⟨76, 36, 37, 942, 11, 18446744073709551616, 181280679876190963, 181280679876190963⟩
def pI940 : Prm := ⟨65, 31, 31, 942, 11, 18446744073709551616, 181278480852935411, 181280679876190963⟩
theorem L940_fin : (prmOK pL940 940 && ptTest pL940 (runFrom pL940 (fmask pL940) (cmask pL940) (hmask pL940) 1 939 (true, (init pL940), (init pL940))) 940 470 false) = true := by
  decide +kernel
theorem L940_ok : RunOK pL940 940 (runFrom pL940 (fmask pL940) (cmask pL940) (hmask pL940) 1 939 (true, (init pL940), (init pL940))) ∧ ptTest pL940 (runFrom pL940 (fmask pL940) (cmask pL940) (hmask pL940) 1 939 (true, (init pL940), (init pL940))) 940 470 false = true :=
  fin_run (runOK_init (prmOK_of_and L940_fin) true) (by decide) rfl L940_fin ptTest_fst
theorem H940_fin : (prmOK pH940 940 && ptTest pH940 (runFrom pH940 (fmask pH940) (cmask pH940) (hmask pH940) 1 939 (true, (init pH940), (init pH940))) 940 470 true) = true := by
  decide +kernel
theorem H940_ok : RunOK pH940 940 (runFrom pH940 (fmask pH940) (cmask pH940) (hmask pH940) 1 939 (true, (init pH940), (init pH940))) ∧ ptTest pH940 (runFrom pH940 (fmask pH940) (cmask pH940) (hmask pH940) 1 939 (true, (init pH940), (init pH940))) 940 470 true = true :=
  fin_run (runOK_init (prmOK_of_and H940_fin) true) (by decide) rfl H940_fin ptTest_fst
theorem I940_fin : (prmOK pI940 940 && intTest pI940 (runFrom pI940 (fmask pI940) (cmask pI940) (hmask pI940) 1 939 (true, (init pI940), (init pI940))) 940 17 true) = true := by
  decide +kernel
theorem I940_ok : RunOK pI940 940 (runFrom pI940 (fmask pI940) (cmask pI940) (hmask pI940) 1 939 (true, (init pI940), (init pI940))) ∧ intTest pI940 (runFrom pI940 (fmask pI940) (cmask pI940) (hmask pI940) 1 939 (true, (init pI940), (init pI940))) 940 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I940_fin) true) (by decide) rfl I940_fin intTest_fst
theorem link940 : linkOK pL940 pH940 pI940 = true := by decide +kernel
theorem cvx940 : ConvexBetweenHumps 940 :=
  cvx_of L940_ok H940_ok I940_ok link940 (by decide)
theorem cenlink940 : cenLinkOK pI940 940 = true := by decide +kernel
theorem cen940 : CenterUniqueMin 940 ∧ DipHyp 940 ∧ OnePointHyps 940 :=
  cen_of L940_ok H940_ok I940_ok link940 cenlink940

/-! ### `N = 941` -/

def pL941 : Prm := ⟨76, 36, 37, 943, 11, 18446744073709551616, 181125073154647273, 181125073154647273⟩
def pH941 : Prm := ⟨76, 36, 37, 943, 11, 18446744073709551616, 181127272177902825, 181127272177902825⟩
def pI941 : Prm := ⟨65, 31, 31, 943, 11, 18446744073709551616, 181125073154647273, 181127272177902825⟩
theorem L941_fin : (prmOK pL941 941 && ptTest pL941 (runFrom pL941 (fmask pL941) (cmask pL941) (hmask pL941) 1 940 (true, (init pL941), (init pL941))) 941 471 false) = true := by
  decide +kernel
theorem L941_ok : RunOK pL941 941 (runFrom pL941 (fmask pL941) (cmask pL941) (hmask pL941) 1 940 (true, (init pL941), (init pL941))) ∧ ptTest pL941 (runFrom pL941 (fmask pL941) (cmask pL941) (hmask pL941) 1 940 (true, (init pL941), (init pL941))) 941 471 false = true :=
  fin_run (runOK_init (prmOK_of_and L941_fin) true) (by decide) rfl L941_fin ptTest_fst
theorem H941_fin : (prmOK pH941 941 && ptTest pH941 (runFrom pH941 (fmask pH941) (cmask pH941) (hmask pH941) 1 940 (true, (init pH941), (init pH941))) 941 471 true) = true := by
  decide +kernel
theorem H941_ok : RunOK pH941 941 (runFrom pH941 (fmask pH941) (cmask pH941) (hmask pH941) 1 940 (true, (init pH941), (init pH941))) ∧ ptTest pH941 (runFrom pH941 (fmask pH941) (cmask pH941) (hmask pH941) 1 940 (true, (init pH941), (init pH941))) 941 471 true = true :=
  fin_run (runOK_init (prmOK_of_and H941_fin) true) (by decide) rfl H941_fin ptTest_fst
theorem I941_fin : (prmOK pI941 941 && intTest pI941 (runFrom pI941 (fmask pI941) (cmask pI941) (hmask pI941) 1 940 (true, (init pI941), (init pI941))) 941 17 false) = true := by
  decide +kernel
theorem I941_ok : RunOK pI941 941 (runFrom pI941 (fmask pI941) (cmask pI941) (hmask pI941) 1 940 (true, (init pI941), (init pI941))) ∧ intTest pI941 (runFrom pI941 (fmask pI941) (cmask pI941) (hmask pI941) 1 940 (true, (init pI941), (init pI941))) 941 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I941_fin) true) (by decide) rfl I941_fin intTest_fst
theorem link941 : linkOK pL941 pH941 pI941 = true := by decide +kernel
theorem cvx941 : ConvexBetweenHumps 941 :=
  cvx_of L941_ok H941_ok I941_ok link941 (by decide)

/-! ### `N = 942` -/

def pL942 : Prm := ⟨76, 36, 37, 944, 11, 18446744073709551616, 180972088528449969, 180972088528449969⟩
def pH942 : Prm := ⟨76, 36, 37, 944, 11, 18446744073709551616, 180974287551705521, 180974287551705521⟩
def pI942 : Prm := ⟨65, 31, 31, 944, 11, 18446744073709551616, 180972088528449969, 180974287551705521⟩
theorem L942_fin : (prmOK pL942 942 && ptTest pL942 (runFrom pL942 (fmask pL942) (cmask pL942) (hmask pL942) 1 941 (true, (init pL942), (init pL942))) 942 471 false) = true := by
  decide +kernel
theorem L942_ok : RunOK pL942 942 (runFrom pL942 (fmask pL942) (cmask pL942) (hmask pL942) 1 941 (true, (init pL942), (init pL942))) ∧ ptTest pL942 (runFrom pL942 (fmask pL942) (cmask pL942) (hmask pL942) 1 941 (true, (init pL942), (init pL942))) 942 471 false = true :=
  fin_run (runOK_init (prmOK_of_and L942_fin) true) (by decide) rfl L942_fin ptTest_fst
theorem H942_fin : (prmOK pH942 942 && ptTest pH942 (runFrom pH942 (fmask pH942) (cmask pH942) (hmask pH942) 1 941 (true, (init pH942), (init pH942))) 942 471 true) = true := by
  decide +kernel
theorem H942_ok : RunOK pH942 942 (runFrom pH942 (fmask pH942) (cmask pH942) (hmask pH942) 1 941 (true, (init pH942), (init pH942))) ∧ ptTest pH942 (runFrom pH942 (fmask pH942) (cmask pH942) (hmask pH942) 1 941 (true, (init pH942), (init pH942))) 942 471 true = true :=
  fin_run (runOK_init (prmOK_of_and H942_fin) true) (by decide) rfl H942_fin ptTest_fst
theorem I942_fin : (prmOK pI942 942 && intTest pI942 (runFrom pI942 (fmask pI942) (cmask pI942) (hmask pI942) 1 941 (true, (init pI942), (init pI942))) 942 18 true) = true := by
  decide +kernel
theorem I942_ok : RunOK pI942 942 (runFrom pI942 (fmask pI942) (cmask pI942) (hmask pI942) 1 941 (true, (init pI942), (init pI942))) ∧ intTest pI942 (runFrom pI942 (fmask pI942) (cmask pI942) (hmask pI942) 1 941 (true, (init pI942), (init pI942))) 942 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I942_fin) true) (by decide) rfl I942_fin intTest_fst
theorem link942 : linkOK pL942 pH942 pI942 = true := by decide +kernel
theorem cvx942 : ConvexBetweenHumps 942 :=
  cvx_of L942_ok H942_ok I942_ok link942 (by decide)
theorem cenlink942 : cenLinkOK pI942 942 = true := by decide +kernel
theorem cen942 : CenterUniqueMin 942 ∧ DipHyp 942 ∧ OnePointHyps 942 :=
  cen_of L942_ok H942_ok I942_ok link942 cenlink942

/-! ### `N = 943` -/

def pL943 : Prm := ⟨76, 36, 37, 945, 11, 18446744073709551616, 180819248244796862, 180819248244796862⟩
def pH943 : Prm := ⟨76, 36, 37, 945, 11, 18446744073709551616, 180821447268052414, 180821447268052414⟩
def pI943 : Prm := ⟨65, 31, 31, 945, 11, 18446744073709551616, 180819248244796862, 180821447268052414⟩
theorem L943_fin : (prmOK pL943 943 && ptTest pL943 (runFrom pL943 (fmask pL943) (cmask pL943) (hmask pL943) 1 942 (true, (init pL943), (init pL943))) 943 472 false) = true := by
  decide +kernel
theorem L943_ok : RunOK pL943 943 (runFrom pL943 (fmask pL943) (cmask pL943) (hmask pL943) 1 942 (true, (init pL943), (init pL943))) ∧ ptTest pL943 (runFrom pL943 (fmask pL943) (cmask pL943) (hmask pL943) 1 942 (true, (init pL943), (init pL943))) 943 472 false = true :=
  fin_run (runOK_init (prmOK_of_and L943_fin) true) (by decide) rfl L943_fin ptTest_fst
theorem H943_fin : (prmOK pH943 943 && ptTest pH943 (runFrom pH943 (fmask pH943) (cmask pH943) (hmask pH943) 1 942 (true, (init pH943), (init pH943))) 943 472 true) = true := by
  decide +kernel
theorem H943_ok : RunOK pH943 943 (runFrom pH943 (fmask pH943) (cmask pH943) (hmask pH943) 1 942 (true, (init pH943), (init pH943))) ∧ ptTest pH943 (runFrom pH943 (fmask pH943) (cmask pH943) (hmask pH943) 1 942 (true, (init pH943), (init pH943))) 943 472 true = true :=
  fin_run (runOK_init (prmOK_of_and H943_fin) true) (by decide) rfl H943_fin ptTest_fst
theorem I943_fin : (prmOK pI943 943 && intTest pI943 (runFrom pI943 (fmask pI943) (cmask pI943) (hmask pI943) 1 942 (true, (init pI943), (init pI943))) 943 18 false) = true := by
  decide +kernel
theorem I943_ok : RunOK pI943 943 (runFrom pI943 (fmask pI943) (cmask pI943) (hmask pI943) 1 942 (true, (init pI943), (init pI943))) ∧ intTest pI943 (runFrom pI943 (fmask pI943) (cmask pI943) (hmask pI943) 1 942 (true, (init pI943), (init pI943))) 943 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I943_fin) true) (by decide) rfl I943_fin intTest_fst
theorem link943 : linkOK pL943 pH943 pI943 = true := by decide +kernel
theorem cvx943 : ConvexBetweenHumps 943 :=
  cvx_of L943_ok H943_ok I943_ok link943 (by decide)

/-! ### `N = 944` -/

def pL944 : Prm := ⟨76, 36, 37, 946, 11, 18446744073709551616, 180666828506381138, 180666828506381138⟩
def pH944 : Prm := ⟨76, 36, 37, 946, 11, 18446744073709551616, 180669027529636690, 180669027529636690⟩
def pI944 : Prm := ⟨65, 31, 31, 946, 11, 18446744073709551616, 180666828506381138, 180669027529636690⟩
theorem L944_fin : (prmOK pL944 944 && ptTest pL944 (runFrom pL944 (fmask pL944) (cmask pL944) (hmask pL944) 1 943 (true, (init pL944), (init pL944))) 944 472 false) = true := by
  decide +kernel
theorem L944_ok : RunOK pL944 944 (runFrom pL944 (fmask pL944) (cmask pL944) (hmask pL944) 1 943 (true, (init pL944), (init pL944))) ∧ ptTest pL944 (runFrom pL944 (fmask pL944) (cmask pL944) (hmask pL944) 1 943 (true, (init pL944), (init pL944))) 944 472 false = true :=
  fin_run (runOK_init (prmOK_of_and L944_fin) true) (by decide) rfl L944_fin ptTest_fst
theorem H944_fin : (prmOK pH944 944 && ptTest pH944 (runFrom pH944 (fmask pH944) (cmask pH944) (hmask pH944) 1 943 (true, (init pH944), (init pH944))) 944 472 true) = true := by
  decide +kernel
theorem H944_ok : RunOK pH944 944 (runFrom pH944 (fmask pH944) (cmask pH944) (hmask pH944) 1 943 (true, (init pH944), (init pH944))) ∧ ptTest pH944 (runFrom pH944 (fmask pH944) (cmask pH944) (hmask pH944) 1 943 (true, (init pH944), (init pH944))) 944 472 true = true :=
  fin_run (runOK_init (prmOK_of_and H944_fin) true) (by decide) rfl H944_fin ptTest_fst
theorem I944_fin : (prmOK pI944 944 && intTest pI944 (runFrom pI944 (fmask pI944) (cmask pI944) (hmask pI944) 1 943 (true, (init pI944), (init pI944))) 944 18 true) = true := by
  decide +kernel
theorem I944_ok : RunOK pI944 944 (runFrom pI944 (fmask pI944) (cmask pI944) (hmask pI944) 1 943 (true, (init pI944), (init pI944))) ∧ intTest pI944 (runFrom pI944 (fmask pI944) (cmask pI944) (hmask pI944) 1 943 (true, (init pI944), (init pI944))) 944 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I944_fin) true) (by decide) rfl I944_fin intTest_fst
theorem link944 : linkOK pL944 pH944 pI944 = true := by decide +kernel
theorem cvx944 : ConvexBetweenHumps 944 :=
  cvx_of L944_ok H944_ok I944_ok link944 (by decide)
theorem cenlink944 : cenLinkOK pI944 944 = true := by decide +kernel
theorem cen944 : CenterUniqueMin 944 ∧ DipHyp 944 ∧ OnePointHyps 944 :=
  cen_of L944_ok H944_ok I944_ok link944 cenlink944

/-! ### `N = 945` -/

def pL945 : Prm := ⟨76, 36, 37, 947, 11, 18446744073709551616, 180514552385423442, 180514552385423442⟩
def pH945 : Prm := ⟨76, 36, 37, 947, 11, 18446744073709551616, 180516751408678994, 180516751408678994⟩
def pI945 : Prm := ⟨65, 31, 31, 947, 11, 18446744073709551616, 180514552385423442, 180516751408678994⟩
theorem L945_fin : (prmOK pL945 945 && ptTest pL945 (runFrom pL945 (fmask pL945) (cmask pL945) (hmask pL945) 1 944 (true, (init pL945), (init pL945))) 945 473 false) = true := by
  decide +kernel
theorem L945_ok : RunOK pL945 945 (runFrom pL945 (fmask pL945) (cmask pL945) (hmask pL945) 1 944 (true, (init pL945), (init pL945))) ∧ ptTest pL945 (runFrom pL945 (fmask pL945) (cmask pL945) (hmask pL945) 1 944 (true, (init pL945), (init pL945))) 945 473 false = true :=
  fin_run (runOK_init (prmOK_of_and L945_fin) true) (by decide) rfl L945_fin ptTest_fst
theorem H945_fin : (prmOK pH945 945 && ptTest pH945 (runFrom pH945 (fmask pH945) (cmask pH945) (hmask pH945) 1 944 (true, (init pH945), (init pH945))) 945 473 true) = true := by
  decide +kernel
theorem H945_ok : RunOK pH945 945 (runFrom pH945 (fmask pH945) (cmask pH945) (hmask pH945) 1 944 (true, (init pH945), (init pH945))) ∧ ptTest pH945 (runFrom pH945 (fmask pH945) (cmask pH945) (hmask pH945) 1 944 (true, (init pH945), (init pH945))) 945 473 true = true :=
  fin_run (runOK_init (prmOK_of_and H945_fin) true) (by decide) rfl H945_fin ptTest_fst
theorem I945_fin : (prmOK pI945 945 && intTest pI945 (runFrom pI945 (fmask pI945) (cmask pI945) (hmask pI945) 1 944 (true, (init pI945), (init pI945))) 945 18 false) = true := by
  decide +kernel
theorem I945_ok : RunOK pI945 945 (runFrom pI945 (fmask pI945) (cmask pI945) (hmask pI945) 1 944 (true, (init pI945), (init pI945))) ∧ intTest pI945 (runFrom pI945 (fmask pI945) (cmask pI945) (hmask pI945) 1 944 (true, (init pI945), (init pI945))) 945 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I945_fin) true) (by decide) rfl I945_fin intTest_fst
theorem link945 : linkOK pL945 pH945 pI945 = true := by decide +kernel
theorem cvx945 : ConvexBetweenHumps 945 :=
  cvx_of L945_ok H945_ok I945_ok link945 (by decide)

/-! ### `N = 946` -/

def pL946 : Prm := ⟨76, 36, 37, 948, 11, 18446744073709551616, 180362694303196437, 180362694303196437⟩
def pH946 : Prm := ⟨76, 36, 37, 948, 11, 18446744073709551616, 180364893326451989, 180364893326451989⟩
def pI946 : Prm := ⟨65, 31, 31, 948, 11, 18446744073709551616, 180362694303196437, 180364893326451989⟩
theorem L946_fin : (prmOK pL946 946 && ptTest pL946 (runFrom pL946 (fmask pL946) (cmask pL946) (hmask pL946) 1 945 (true, (init pL946), (init pL946))) 946 473 false) = true := by
  decide +kernel
theorem L946_ok : RunOK pL946 946 (runFrom pL946 (fmask pL946) (cmask pL946) (hmask pL946) 1 945 (true, (init pL946), (init pL946))) ∧ ptTest pL946 (runFrom pL946 (fmask pL946) (cmask pL946) (hmask pL946) 1 945 (true, (init pL946), (init pL946))) 946 473 false = true :=
  fin_run (runOK_init (prmOK_of_and L946_fin) true) (by decide) rfl L946_fin ptTest_fst
theorem H946_fin : (prmOK pH946 946 && ptTest pH946 (runFrom pH946 (fmask pH946) (cmask pH946) (hmask pH946) 1 945 (true, (init pH946), (init pH946))) 946 473 true) = true := by
  decide +kernel
theorem H946_ok : RunOK pH946 946 (runFrom pH946 (fmask pH946) (cmask pH946) (hmask pH946) 1 945 (true, (init pH946), (init pH946))) ∧ ptTest pH946 (runFrom pH946 (fmask pH946) (cmask pH946) (hmask pH946) 1 945 (true, (init pH946), (init pH946))) 946 473 true = true :=
  fin_run (runOK_init (prmOK_of_and H946_fin) true) (by decide) rfl H946_fin ptTest_fst
theorem I946_fin : (prmOK pI946 946 && intTest pI946 (runFrom pI946 (fmask pI946) (cmask pI946) (hmask pI946) 1 945 (true, (init pI946), (init pI946))) 946 18 true) = true := by
  decide +kernel
theorem I946_ok : RunOK pI946 946 (runFrom pI946 (fmask pI946) (cmask pI946) (hmask pI946) 1 945 (true, (init pI946), (init pI946))) ∧ intTest pI946 (runFrom pI946 (fmask pI946) (cmask pI946) (hmask pI946) 1 945 (true, (init pI946), (init pI946))) 946 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I946_fin) true) (by decide) rfl I946_fin intTest_fst
theorem link946 : linkOK pL946 pH946 pI946 = true := by decide +kernel
theorem cvx946 : ConvexBetweenHumps 946 :=
  cvx_of L946_ok H946_ok I946_ok link946 (by decide)
theorem cenlink946 : cenLinkOK pI946 946 = true := by decide +kernel
theorem cen946 : CenterUniqueMin 946 ∧ DipHyp 946 ∧ OnePointHyps 946 :=
  cen_of L946_ok H946_ok I946_ok link946 cenlink946

/-! ### `N = 947` -/

def pL947 : Prm := ⟨76, 36, 37, 949, 11, 18446744073709551616, 180210979118285019, 180210979118285019⟩
def pH947 : Prm := ⟨76, 36, 37, 949, 11, 18446744073709551616, 180213178141540571, 180213178141540571⟩
def pI947 : Prm := ⟨65, 31, 31, 949, 11, 18446744073709551616, 180210979118285019, 180213178141540571⟩
theorem L947_fin : (prmOK pL947 947 && ptTest pL947 (runFrom pL947 (fmask pL947) (cmask pL947) (hmask pL947) 1 946 (true, (init pL947), (init pL947))) 947 474 false) = true := by
  decide +kernel
theorem L947_ok : RunOK pL947 947 (runFrom pL947 (fmask pL947) (cmask pL947) (hmask pL947) 1 946 (true, (init pL947), (init pL947))) ∧ ptTest pL947 (runFrom pL947 (fmask pL947) (cmask pL947) (hmask pL947) 1 946 (true, (init pL947), (init pL947))) 947 474 false = true :=
  fin_run (runOK_init (prmOK_of_and L947_fin) true) (by decide) rfl L947_fin ptTest_fst
theorem H947_fin : (prmOK pH947 947 && ptTest pH947 (runFrom pH947 (fmask pH947) (cmask pH947) (hmask pH947) 1 946 (true, (init pH947), (init pH947))) 947 474 true) = true := by
  decide +kernel
theorem H947_ok : RunOK pH947 947 (runFrom pH947 (fmask pH947) (cmask pH947) (hmask pH947) 1 946 (true, (init pH947), (init pH947))) ∧ ptTest pH947 (runFrom pH947 (fmask pH947) (cmask pH947) (hmask pH947) 1 946 (true, (init pH947), (init pH947))) 947 474 true = true :=
  fin_run (runOK_init (prmOK_of_and H947_fin) true) (by decide) rfl H947_fin ptTest_fst
theorem I947_fin : (prmOK pI947 947 && intTest pI947 (runFrom pI947 (fmask pI947) (cmask pI947) (hmask pI947) 1 946 (true, (init pI947), (init pI947))) 947 18 false) = true := by
  decide +kernel
theorem I947_ok : RunOK pI947 947 (runFrom pI947 (fmask pI947) (cmask pI947) (hmask pI947) 1 946 (true, (init pI947), (init pI947))) ∧ intTest pI947 (runFrom pI947 (fmask pI947) (cmask pI947) (hmask pI947) 1 946 (true, (init pI947), (init pI947))) 947 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I947_fin) true) (by decide) rfl I947_fin intTest_fst
theorem link947 : linkOK pL947 pH947 pI947 = true := by decide +kernel
theorem cvx947 : ConvexBetweenHumps 947 :=
  cvx_of L947_ok H947_ok I947_ok link947 (by decide)

/-! ### `N = 948` -/

def pL948 : Prm := ⟨76, 36, 37, 950, 11, 18446744073709551616, 180059679485704553, 180059679485704553⟩
def pH948 : Prm := ⟨76, 36, 37, 950, 11, 18446744073709551616, 180061878508960105, 180061878508960105⟩
def pI948 : Prm := ⟨64, 32, 29, 950, 11, 18446744073709551616, 180059679485704553, 180061878508960105⟩
theorem L948_fin : (prmOK pL948 948 && ptTest pL948 (runFrom pL948 (fmask pL948) (cmask pL948) (hmask pL948) 1 947 (true, (init pL948), (init pL948))) 948 474 false) = true := by
  decide +kernel
theorem L948_ok : RunOK pL948 948 (runFrom pL948 (fmask pL948) (cmask pL948) (hmask pL948) 1 947 (true, (init pL948), (init pL948))) ∧ ptTest pL948 (runFrom pL948 (fmask pL948) (cmask pL948) (hmask pL948) 1 947 (true, (init pL948), (init pL948))) 948 474 false = true :=
  fin_run (runOK_init (prmOK_of_and L948_fin) true) (by decide) rfl L948_fin ptTest_fst
theorem H948_fin : (prmOK pH948 948 && ptTest pH948 (runFrom pH948 (fmask pH948) (cmask pH948) (hmask pH948) 1 947 (true, (init pH948), (init pH948))) 948 474 true) = true := by
  decide +kernel
theorem H948_ok : RunOK pH948 948 (runFrom pH948 (fmask pH948) (cmask pH948) (hmask pH948) 1 947 (true, (init pH948), (init pH948))) ∧ ptTest pH948 (runFrom pH948 (fmask pH948) (cmask pH948) (hmask pH948) 1 947 (true, (init pH948), (init pH948))) 948 474 true = true :=
  fin_run (runOK_init (prmOK_of_and H948_fin) true) (by decide) rfl H948_fin ptTest_fst
theorem I948_fin : (prmOK pI948 948 && intTest pI948 (runFrom pI948 (fmask pI948) (cmask pI948) (hmask pI948) 1 947 (true, (init pI948), (init pI948))) 948 18 true) = true := by
  decide +kernel
theorem I948_ok : RunOK pI948 948 (runFrom pI948 (fmask pI948) (cmask pI948) (hmask pI948) 1 947 (true, (init pI948), (init pI948))) ∧ intTest pI948 (runFrom pI948 (fmask pI948) (cmask pI948) (hmask pI948) 1 947 (true, (init pI948), (init pI948))) 948 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I948_fin) true) (by decide) rfl I948_fin intTest_fst
theorem link948 : linkOK pL948 pH948 pI948 = true := by decide +kernel
theorem cvx948 : ConvexBetweenHumps 948 :=
  cvx_of L948_ok H948_ok I948_ok link948 (by decide)
theorem cenlink948 : cenLinkOK pI948 948 = true := by decide +kernel
theorem cen948 : CenterUniqueMin 948 ∧ DipHyp 948 ∧ OnePointHyps 948 :=
  cen_of L948_ok H948_ok I948_ok link948 cenlink948

/-! ### `N = 949` -/

def pL949 : Prm := ⟨76, 36, 37, 951, 11, 18446744073709551616, 179908522035167171, 179908522035167171⟩
def pH949 : Prm := ⟨76, 36, 37, 951, 11, 18446744073709551616, 179910721058422723, 179910721058422723⟩
def pI949 : Prm := ⟨64, 32, 29, 951, 11, 18446744073709551616, 179908522035167171, 179910721058422723⟩
theorem L949_fin : (prmOK pL949 949 && ptTest pL949 (runFrom pL949 (fmask pL949) (cmask pL949) (hmask pL949) 1 948 (true, (init pL949), (init pL949))) 949 475 false) = true := by
  decide +kernel
theorem L949_ok : RunOK pL949 949 (runFrom pL949 (fmask pL949) (cmask pL949) (hmask pL949) 1 948 (true, (init pL949), (init pL949))) ∧ ptTest pL949 (runFrom pL949 (fmask pL949) (cmask pL949) (hmask pL949) 1 948 (true, (init pL949), (init pL949))) 949 475 false = true :=
  fin_run (runOK_init (prmOK_of_and L949_fin) true) (by decide) rfl L949_fin ptTest_fst
theorem H949_fin : (prmOK pH949 949 && ptTest pH949 (runFrom pH949 (fmask pH949) (cmask pH949) (hmask pH949) 1 948 (true, (init pH949), (init pH949))) 949 475 true) = true := by
  decide +kernel
theorem H949_ok : RunOK pH949 949 (runFrom pH949 (fmask pH949) (cmask pH949) (hmask pH949) 1 948 (true, (init pH949), (init pH949))) ∧ ptTest pH949 (runFrom pH949 (fmask pH949) (cmask pH949) (hmask pH949) 1 948 (true, (init pH949), (init pH949))) 949 475 true = true :=
  fin_run (runOK_init (prmOK_of_and H949_fin) true) (by decide) rfl H949_fin ptTest_fst
theorem I949_fin : (prmOK pI949 949 && intTest pI949 (runFrom pI949 (fmask pI949) (cmask pI949) (hmask pI949) 1 948 (true, (init pI949), (init pI949))) 949 18 false) = true := by
  decide +kernel
theorem I949_ok : RunOK pI949 949 (runFrom pI949 (fmask pI949) (cmask pI949) (hmask pI949) 1 948 (true, (init pI949), (init pI949))) ∧ intTest pI949 (runFrom pI949 (fmask pI949) (cmask pI949) (hmask pI949) 1 948 (true, (init pI949), (init pI949))) 949 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I949_fin) true) (by decide) rfl I949_fin intTest_fst
theorem link949 : linkOK pL949 pH949 pI949 = true := by decide +kernel
theorem cvx949 : ConvexBetweenHumps 949 :=
  cvx_of L949_ok H949_ok I949_ok link949 (by decide)

/-! ### `N = 950` -/

def pL950 : Prm := ⟨76, 36, 37, 952, 11, 18446744073709551616, 179757777670538824, 179757777670538824⟩
def pH950 : Prm := ⟨76, 36, 37, 952, 11, 18446744073709551616, 179759976693794376, 179759976693794376⟩
def pI950 : Prm := ⟨64, 32, 29, 952, 11, 18446744073709551616, 179757777670538824, 179759976693794376⟩
theorem L950_fin : (prmOK pL950 950 && ptTest pL950 (runFrom pL950 (fmask pL950) (cmask pL950) (hmask pL950) 1 949 (true, (init pL950), (init pL950))) 950 475 false) = true := by
  decide +kernel
theorem L950_ok : RunOK pL950 950 (runFrom pL950 (fmask pL950) (cmask pL950) (hmask pL950) 1 949 (true, (init pL950), (init pL950))) ∧ ptTest pL950 (runFrom pL950 (fmask pL950) (cmask pL950) (hmask pL950) 1 949 (true, (init pL950), (init pL950))) 950 475 false = true :=
  fin_run (runOK_init (prmOK_of_and L950_fin) true) (by decide) rfl L950_fin ptTest_fst
theorem H950_fin : (prmOK pH950 950 && ptTest pH950 (runFrom pH950 (fmask pH950) (cmask pH950) (hmask pH950) 1 949 (true, (init pH950), (init pH950))) 950 475 true) = true := by
  decide +kernel
theorem H950_ok : RunOK pH950 950 (runFrom pH950 (fmask pH950) (cmask pH950) (hmask pH950) 1 949 (true, (init pH950), (init pH950))) ∧ ptTest pH950 (runFrom pH950 (fmask pH950) (cmask pH950) (hmask pH950) 1 949 (true, (init pH950), (init pH950))) 950 475 true = true :=
  fin_run (runOK_init (prmOK_of_and H950_fin) true) (by decide) rfl H950_fin ptTest_fst
theorem I950_fin : (prmOK pI950 950 && intTest pI950 (runFrom pI950 (fmask pI950) (cmask pI950) (hmask pI950) 1 949 (true, (init pI950), (init pI950))) 950 18 true) = true := by
  decide +kernel
theorem I950_ok : RunOK pI950 950 (runFrom pI950 (fmask pI950) (cmask pI950) (hmask pI950) 1 949 (true, (init pI950), (init pI950))) ∧ intTest pI950 (runFrom pI950 (fmask pI950) (cmask pI950) (hmask pI950) 1 949 (true, (init pI950), (init pI950))) 950 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I950_fin) true) (by decide) rfl I950_fin intTest_fst
theorem link950 : linkOK pL950 pH950 pI950 = true := by decide +kernel
theorem cvx950 : ConvexBetweenHumps 950 :=
  cvx_of L950_ok H950_ok I950_ok link950 (by decide)
theorem cenlink950 : cenLinkOK pI950 950 = true := by decide +kernel
theorem cen950 : CenterUniqueMin 950 ∧ DipHyp 950 ∧ OnePointHyps 950 :=
  cen_of L950_ok H950_ok I950_ok link950 cenlink950

/-! ### `N = 951` -/

def pL951 : Prm := ⟨76, 36, 37, 953, 11, 18446744073709551616, 179607174777514108, 179607174777514108⟩
def pH951 : Prm := ⟨76, 36, 37, 953, 11, 18446744073709551616, 179609373800769660, 179609373800769660⟩
def pI951 : Prm := ⟨64, 32, 29, 953, 11, 18446744073709551616, 179607174777514108, 179609373800769660⟩
theorem L951_fin : (prmOK pL951 951 && ptTest pL951 (runFrom pL951 (fmask pL951) (cmask pL951) (hmask pL951) 1 950 (true, (init pL951), (init pL951))) 951 476 false) = true := by
  decide +kernel
theorem L951_ok : RunOK pL951 951 (runFrom pL951 (fmask pL951) (cmask pL951) (hmask pL951) 1 950 (true, (init pL951), (init pL951))) ∧ ptTest pL951 (runFrom pL951 (fmask pL951) (cmask pL951) (hmask pL951) 1 950 (true, (init pL951), (init pL951))) 951 476 false = true :=
  fin_run (runOK_init (prmOK_of_and L951_fin) true) (by decide) rfl L951_fin ptTest_fst
theorem H951_fin : (prmOK pH951 951 && ptTest pH951 (runFrom pH951 (fmask pH951) (cmask pH951) (hmask pH951) 1 950 (true, (init pH951), (init pH951))) 951 476 true) = true := by
  decide +kernel
theorem H951_ok : RunOK pH951 951 (runFrom pH951 (fmask pH951) (cmask pH951) (hmask pH951) 1 950 (true, (init pH951), (init pH951))) ∧ ptTest pH951 (runFrom pH951 (fmask pH951) (cmask pH951) (hmask pH951) 1 950 (true, (init pH951), (init pH951))) 951 476 true = true :=
  fin_run (runOK_init (prmOK_of_and H951_fin) true) (by decide) rfl H951_fin ptTest_fst
theorem I951_fin : (prmOK pI951 951 && intTest pI951 (runFrom pI951 (fmask pI951) (cmask pI951) (hmask pI951) 1 950 (true, (init pI951), (init pI951))) 951 18 false) = true := by
  decide +kernel
theorem I951_ok : RunOK pI951 951 (runFrom pI951 (fmask pI951) (cmask pI951) (hmask pI951) 1 950 (true, (init pI951), (init pI951))) ∧ intTest pI951 (runFrom pI951 (fmask pI951) (cmask pI951) (hmask pI951) 1 950 (true, (init pI951), (init pI951))) 951 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I951_fin) true) (by decide) rfl I951_fin intTest_fst
theorem link951 : linkOK pL951 pH951 pI951 = true := by decide +kernel
theorem cvx951 : ConvexBetweenHumps 951 :=
  cvx_of L951_ok H951_ok I951_ok link951 (by decide)

/-! ### `N = 952` -/

def pL952 : Prm := ⟨76, 36, 37, 954, 11, 18446744073709551616, 179456982523714526, 179456982523714526⟩
def pH952 : Prm := ⟨76, 36, 37, 954, 11, 18446744073709551616, 179459181546970078, 179459181546970078⟩
def pI952 : Prm := ⟨64, 32, 29, 954, 11, 18446744073709551616, 179456982523714526, 179459181546970078⟩
theorem L952_fin : (prmOK pL952 952 && ptTest pL952 (runFrom pL952 (fmask pL952) (cmask pL952) (hmask pL952) 1 951 (true, (init pL952), (init pL952))) 952 476 false) = true := by
  decide +kernel
theorem L952_ok : RunOK pL952 952 (runFrom pL952 (fmask pL952) (cmask pL952) (hmask pL952) 1 951 (true, (init pL952), (init pL952))) ∧ ptTest pL952 (runFrom pL952 (fmask pL952) (cmask pL952) (hmask pL952) 1 951 (true, (init pL952), (init pL952))) 952 476 false = true :=
  fin_run (runOK_init (prmOK_of_and L952_fin) true) (by decide) rfl L952_fin ptTest_fst
theorem H952_fin : (prmOK pH952 952 && ptTest pH952 (runFrom pH952 (fmask pH952) (cmask pH952) (hmask pH952) 1 951 (true, (init pH952), (init pH952))) 952 476 true) = true := by
  decide +kernel
theorem H952_ok : RunOK pH952 952 (runFrom pH952 (fmask pH952) (cmask pH952) (hmask pH952) 1 951 (true, (init pH952), (init pH952))) ∧ ptTest pH952 (runFrom pH952 (fmask pH952) (cmask pH952) (hmask pH952) 1 951 (true, (init pH952), (init pH952))) 952 476 true = true :=
  fin_run (runOK_init (prmOK_of_and H952_fin) true) (by decide) rfl H952_fin ptTest_fst
theorem I952_fin : (prmOK pI952 952 && intTest pI952 (runFrom pI952 (fmask pI952) (cmask pI952) (hmask pI952) 1 951 (true, (init pI952), (init pI952))) 952 18 true) = true := by
  decide +kernel
theorem I952_ok : RunOK pI952 952 (runFrom pI952 (fmask pI952) (cmask pI952) (hmask pI952) 1 951 (true, (init pI952), (init pI952))) ∧ intTest pI952 (runFrom pI952 (fmask pI952) (cmask pI952) (hmask pI952) 1 951 (true, (init pI952), (init pI952))) 952 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I952_fin) true) (by decide) rfl I952_fin intTest_fst
theorem link952 : linkOK pL952 pH952 pI952 = true := by decide +kernel
theorem cvx952 : ConvexBetweenHumps 952 :=
  cvx_of L952_ok H952_ok I952_ok link952 (by decide)
theorem cenlink952 : cenLinkOK pI952 952 = true := by decide +kernel
theorem cen952 : CenterUniqueMin 952 ∧ DipHyp 952 ∧ OnePointHyps 952 :=
  cen_of L952_ok H952_ok I952_ok link952 cenlink952

/-! ### `N = 953` -/

def pL953 : Prm := ⟨76, 36, 37, 955, 11, 18446744073709551616, 179306931035819934, 179306931035819934⟩
def pH953 : Prm := ⟨76, 36, 37, 955, 11, 18446744073709551616, 179309130059075486, 179309130059075486⟩
def pI953 : Prm := ⟨64, 32, 29, 955, 11, 18446744073709551616, 179306931035819934, 179309130059075486⟩
theorem L953_fin : (prmOK pL953 953 && ptTest pL953 (runFrom pL953 (fmask pL953) (cmask pL953) (hmask pL953) 1 952 (true, (init pL953), (init pL953))) 953 477 false) = true := by
  decide +kernel
theorem L953_ok : RunOK pL953 953 (runFrom pL953 (fmask pL953) (cmask pL953) (hmask pL953) 1 952 (true, (init pL953), (init pL953))) ∧ ptTest pL953 (runFrom pL953 (fmask pL953) (cmask pL953) (hmask pL953) 1 952 (true, (init pL953), (init pL953))) 953 477 false = true :=
  fin_run (runOK_init (prmOK_of_and L953_fin) true) (by decide) rfl L953_fin ptTest_fst
theorem H953_fin : (prmOK pH953 953 && ptTest pH953 (runFrom pH953 (fmask pH953) (cmask pH953) (hmask pH953) 1 952 (true, (init pH953), (init pH953))) 953 477 true) = true := by
  decide +kernel
theorem H953_ok : RunOK pH953 953 (runFrom pH953 (fmask pH953) (cmask pH953) (hmask pH953) 1 952 (true, (init pH953), (init pH953))) ∧ ptTest pH953 (runFrom pH953 (fmask pH953) (cmask pH953) (hmask pH953) 1 952 (true, (init pH953), (init pH953))) 953 477 true = true :=
  fin_run (runOK_init (prmOK_of_and H953_fin) true) (by decide) rfl H953_fin ptTest_fst
theorem I953_fin : (prmOK pI953 953 && intTest pI953 (runFrom pI953 (fmask pI953) (cmask pI953) (hmask pI953) 1 952 (true, (init pI953), (init pI953))) 953 18 false) = true := by
  decide +kernel
theorem I953_ok : RunOK pI953 953 (runFrom pI953 (fmask pI953) (cmask pI953) (hmask pI953) 1 952 (true, (init pI953), (init pI953))) ∧ intTest pI953 (runFrom pI953 (fmask pI953) (cmask pI953) (hmask pI953) 1 952 (true, (init pI953), (init pI953))) 953 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I953_fin) true) (by decide) rfl I953_fin intTest_fst
theorem link953 : linkOK pL953 pH953 pI953 = true := by decide +kernel
theorem cvx953 : ConvexBetweenHumps 953 :=
  cvx_of L953_ok H953_ok I953_ok link953 (by decide)

/-! ### `N = 954` -/

def pL954 : Prm := ⟨76, 36, 37, 956, 11, 18446744073709551616, 179157287760038572, 179157287760038572⟩
def pH954 : Prm := ⟨76, 36, 37, 956, 11, 18446744073709551616, 179159486783294124, 179159486783294124⟩
def pI954 : Prm := ⟨64, 32, 29, 956, 11, 18446744073709551616, 179157287760038572, 179159486783294124⟩
theorem L954_fin : (prmOK pL954 954 && ptTest pL954 (runFrom pL954 (fmask pL954) (cmask pL954) (hmask pL954) 1 953 (true, (init pL954), (init pL954))) 954 477 false) = true := by
  decide +kernel
theorem L954_ok : RunOK pL954 954 (runFrom pL954 (fmask pL954) (cmask pL954) (hmask pL954) 1 953 (true, (init pL954), (init pL954))) ∧ ptTest pL954 (runFrom pL954 (fmask pL954) (cmask pL954) (hmask pL954) 1 953 (true, (init pL954), (init pL954))) 954 477 false = true :=
  fin_run (runOK_init (prmOK_of_and L954_fin) true) (by decide) rfl L954_fin ptTest_fst
theorem H954_fin : (prmOK pH954 954 && ptTest pH954 (runFrom pH954 (fmask pH954) (cmask pH954) (hmask pH954) 1 953 (true, (init pH954), (init pH954))) 954 477 true) = true := by
  decide +kernel
theorem H954_ok : RunOK pH954 954 (runFrom pH954 (fmask pH954) (cmask pH954) (hmask pH954) 1 953 (true, (init pH954), (init pH954))) ∧ ptTest pH954 (runFrom pH954 (fmask pH954) (cmask pH954) (hmask pH954) 1 953 (true, (init pH954), (init pH954))) 954 477 true = true :=
  fin_run (runOK_init (prmOK_of_and H954_fin) true) (by decide) rfl H954_fin ptTest_fst
theorem I954_fin : (prmOK pI954 954 && intTest pI954 (runFrom pI954 (fmask pI954) (cmask pI954) (hmask pI954) 1 953 (true, (init pI954), (init pI954))) 954 18 true) = true := by
  decide +kernel
theorem I954_ok : RunOK pI954 954 (runFrom pI954 (fmask pI954) (cmask pI954) (hmask pI954) 1 953 (true, (init pI954), (init pI954))) ∧ intTest pI954 (runFrom pI954 (fmask pI954) (cmask pI954) (hmask pI954) 1 953 (true, (init pI954), (init pI954))) 954 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I954_fin) true) (by decide) rfl I954_fin intTest_fst
theorem link954 : linkOK pL954 pH954 pI954 = true := by decide +kernel
theorem cvx954 : ConvexBetweenHumps 954 :=
  cvx_of L954_ok H954_ok I954_ok link954 (by decide)
theorem cenlink954 : cenLinkOK pI954 954 = true := by decide +kernel
theorem cen954 : CenterUniqueMin 954 ∧ DipHyp 954 ∧ OnePointHyps 954 :=
  cen_of L954_ok H954_ok I954_ok link954 cenlink954

/-! ### `N = 955` -/

def pL955 : Prm := ⟨76, 36, 37, 957, 11, 18446744073709551616, 179007784549259710, 179007784549259710⟩
def pH955 : Prm := ⟨76, 36, 37, 957, 11, 18446744073709551616, 179009983572515262, 179009983572515262⟩
def pI955 : Prm := ⟨64, 32, 29, 957, 11, 18446744073709551616, 179007784549259710, 179009983572515262⟩
theorem L955_fin : (prmOK pL955 955 && ptTest pL955 (runFrom pL955 (fmask pL955) (cmask pL955) (hmask pL955) 1 954 (true, (init pL955), (init pL955))) 955 478 false) = true := by
  decide +kernel
theorem L955_ok : RunOK pL955 955 (runFrom pL955 (fmask pL955) (cmask pL955) (hmask pL955) 1 954 (true, (init pL955), (init pL955))) ∧ ptTest pL955 (runFrom pL955 (fmask pL955) (cmask pL955) (hmask pL955) 1 954 (true, (init pL955), (init pL955))) 955 478 false = true :=
  fin_run (runOK_init (prmOK_of_and L955_fin) true) (by decide) rfl L955_fin ptTest_fst
theorem H955_fin : (prmOK pH955 955 && ptTest pH955 (runFrom pH955 (fmask pH955) (cmask pH955) (hmask pH955) 1 954 (true, (init pH955), (init pH955))) 955 478 true) = true := by
  decide +kernel
theorem H955_ok : RunOK pH955 955 (runFrom pH955 (fmask pH955) (cmask pH955) (hmask pH955) 1 954 (true, (init pH955), (init pH955))) ∧ ptTest pH955 (runFrom pH955 (fmask pH955) (cmask pH955) (hmask pH955) 1 954 (true, (init pH955), (init pH955))) 955 478 true = true :=
  fin_run (runOK_init (prmOK_of_and H955_fin) true) (by decide) rfl H955_fin ptTest_fst
theorem I955_fin : (prmOK pI955 955 && intTest pI955 (runFrom pI955 (fmask pI955) (cmask pI955) (hmask pI955) 1 954 (true, (init pI955), (init pI955))) 955 18 false) = true := by
  decide +kernel
theorem I955_ok : RunOK pI955 955 (runFrom pI955 (fmask pI955) (cmask pI955) (hmask pI955) 1 954 (true, (init pI955), (init pI955))) ∧ intTest pI955 (runFrom pI955 (fmask pI955) (cmask pI955) (hmask pI955) 1 954 (true, (init pI955), (init pI955))) 955 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I955_fin) true) (by decide) rfl I955_fin intTest_fst
theorem link955 : linkOK pL955 pH955 pI955 = true := by decide +kernel
theorem cvx955 : ConvexBetweenHumps 955 :=
  cvx_of L955_ok H955_ok I955_ok link955 (by decide)

/-! ### `N = 956` -/

def pL956 : Prm := ⟨76, 36, 37, 958, 11, 18446744073709551616, 178858687142777469, 178858687142777469⟩
def pH956 : Prm := ⟨76, 36, 37, 958, 11, 18446744073709551616, 178860886166033021, 178860886166033021⟩
def pI956 : Prm := ⟨63, 32, 28, 958, 11, 18446744073709551616, 178858687142777469, 178860886166033021⟩
theorem L956_fin : (prmOK pL956 956 && ptTest pL956 (runFrom pL956 (fmask pL956) (cmask pL956) (hmask pL956) 1 955 (true, (init pL956), (init pL956))) 956 478 false) = true := by
  decide +kernel
theorem L956_ok : RunOK pL956 956 (runFrom pL956 (fmask pL956) (cmask pL956) (hmask pL956) 1 955 (true, (init pL956), (init pL956))) ∧ ptTest pL956 (runFrom pL956 (fmask pL956) (cmask pL956) (hmask pL956) 1 955 (true, (init pL956), (init pL956))) 956 478 false = true :=
  fin_run (runOK_init (prmOK_of_and L956_fin) true) (by decide) rfl L956_fin ptTest_fst
theorem H956_fin : (prmOK pH956 956 && ptTest pH956 (runFrom pH956 (fmask pH956) (cmask pH956) (hmask pH956) 1 955 (true, (init pH956), (init pH956))) 956 478 true) = true := by
  decide +kernel
theorem H956_ok : RunOK pH956 956 (runFrom pH956 (fmask pH956) (cmask pH956) (hmask pH956) 1 955 (true, (init pH956), (init pH956))) ∧ ptTest pH956 (runFrom pH956 (fmask pH956) (cmask pH956) (hmask pH956) 1 955 (true, (init pH956), (init pH956))) 956 478 true = true :=
  fin_run (runOK_init (prmOK_of_and H956_fin) true) (by decide) rfl H956_fin ptTest_fst
theorem I956_fin : (prmOK pI956 956 && intTest pI956 (runFrom pI956 (fmask pI956) (cmask pI956) (hmask pI956) 1 955 (true, (init pI956), (init pI956))) 956 18 true) = true := by
  decide +kernel
theorem I956_ok : RunOK pI956 956 (runFrom pI956 (fmask pI956) (cmask pI956) (hmask pI956) 1 955 (true, (init pI956), (init pI956))) ∧ intTest pI956 (runFrom pI956 (fmask pI956) (cmask pI956) (hmask pI956) 1 955 (true, (init pI956), (init pI956))) 956 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I956_fin) true) (by decide) rfl I956_fin intTest_fst
theorem link956 : linkOK pL956 pH956 pI956 = true := by decide +kernel
theorem cvx956 : ConvexBetweenHumps 956 :=
  cvx_of L956_ok H956_ok I956_ok link956 (by decide)
theorem cenlink956 : cenLinkOK pI956 956 = true := by decide +kernel
theorem cen956 : CenterUniqueMin 956 ∧ DipHyp 956 ∧ OnePointHyps 956 :=
  cen_of L956_ok H956_ok I956_ok link956 cenlink956

/-! ### `N = 957` -/

def pL957 : Prm := ⟨76, 36, 37, 959, 11, 18446744073709551616, 178709729105117607, 178709729105117607⟩
def pH957 : Prm := ⟨76, 36, 37, 959, 11, 18446744073709551616, 178711928128373159, 178711928128373159⟩
def pI957 : Prm := ⟨63, 32, 28, 959, 11, 18446744073709551616, 178709729105117607, 178711928128373159⟩
theorem L957_fin : (prmOK pL957 957 && ptTest pL957 (runFrom pL957 (fmask pL957) (cmask pL957) (hmask pL957) 1 956 (true, (init pL957), (init pL957))) 957 479 false) = true := by
  decide +kernel
theorem L957_ok : RunOK pL957 957 (runFrom pL957 (fmask pL957) (cmask pL957) (hmask pL957) 1 956 (true, (init pL957), (init pL957))) ∧ ptTest pL957 (runFrom pL957 (fmask pL957) (cmask pL957) (hmask pL957) 1 956 (true, (init pL957), (init pL957))) 957 479 false = true :=
  fin_run (runOK_init (prmOK_of_and L957_fin) true) (by decide) rfl L957_fin ptTest_fst
theorem H957_fin : (prmOK pH957 957 && ptTest pH957 (runFrom pH957 (fmask pH957) (cmask pH957) (hmask pH957) 1 956 (true, (init pH957), (init pH957))) 957 479 true) = true := by
  decide +kernel
theorem H957_ok : RunOK pH957 957 (runFrom pH957 (fmask pH957) (cmask pH957) (hmask pH957) 1 956 (true, (init pH957), (init pH957))) ∧ ptTest pH957 (runFrom pH957 (fmask pH957) (cmask pH957) (hmask pH957) 1 956 (true, (init pH957), (init pH957))) 957 479 true = true :=
  fin_run (runOK_init (prmOK_of_and H957_fin) true) (by decide) rfl H957_fin ptTest_fst
theorem I957_fin : (prmOK pI957 957 && intTest pI957 (runFrom pI957 (fmask pI957) (cmask pI957) (hmask pI957) 1 956 (true, (init pI957), (init pI957))) 957 18 false) = true := by
  decide +kernel
theorem I957_ok : RunOK pI957 957 (runFrom pI957 (fmask pI957) (cmask pI957) (hmask pI957) 1 956 (true, (init pI957), (init pI957))) ∧ intTest pI957 (runFrom pI957 (fmask pI957) (cmask pI957) (hmask pI957) 1 956 (true, (init pI957), (init pI957))) 957 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I957_fin) true) (by decide) rfl I957_fin intTest_fst
theorem link957 : linkOK pL957 pH957 pI957 = true := by decide +kernel
theorem cvx957 : ConvexBetweenHumps 957 :=
  cvx_of L957_ok H957_ok I957_ok link957 (by decide)

/-! ### `N = 958` -/

def pL958 : Prm := ⟨76, 36, 37, 960, 11, 18446744073709551616, 178561174483103922, 178561174483103922⟩
def pH958 : Prm := ⟨76, 36, 37, 960, 11, 18446744073709551616, 178563373506359474, 178563373506359474⟩
def pI958 : Prm := ⟨65, 31, 31, 960, 11, 18446744073709551616, 178561174483103922, 178563373506359474⟩
theorem L958_fin : (prmOK pL958 958 && ptTest pL958 (runFrom pL958 (fmask pL958) (cmask pL958) (hmask pL958) 1 957 (true, (init pL958), (init pL958))) 958 479 false) = true := by
  decide +kernel
theorem L958_ok : RunOK pL958 958 (runFrom pL958 (fmask pL958) (cmask pL958) (hmask pL958) 1 957 (true, (init pL958), (init pL958))) ∧ ptTest pL958 (runFrom pL958 (fmask pL958) (cmask pL958) (hmask pL958) 1 957 (true, (init pL958), (init pL958))) 958 479 false = true :=
  fin_run (runOK_init (prmOK_of_and L958_fin) true) (by decide) rfl L958_fin ptTest_fst
theorem H958_fin : (prmOK pH958 958 && ptTest pH958 (runFrom pH958 (fmask pH958) (cmask pH958) (hmask pH958) 1 957 (true, (init pH958), (init pH958))) 958 479 true) = true := by
  decide +kernel
theorem H958_ok : RunOK pH958 958 (runFrom pH958 (fmask pH958) (cmask pH958) (hmask pH958) 1 957 (true, (init pH958), (init pH958))) ∧ ptTest pH958 (runFrom pH958 (fmask pH958) (cmask pH958) (hmask pH958) 1 957 (true, (init pH958), (init pH958))) 958 479 true = true :=
  fin_run (runOK_init (prmOK_of_and H958_fin) true) (by decide) rfl H958_fin ptTest_fst
theorem I958_fin : (prmOK pI958 958 && intTest pI958 (runFrom pI958 (fmask pI958) (cmask pI958) (hmask pI958) 1 957 (true, (init pI958), (init pI958))) 958 18 true) = true := by
  decide +kernel
theorem I958_ok : RunOK pI958 958 (runFrom pI958 (fmask pI958) (cmask pI958) (hmask pI958) 1 957 (true, (init pI958), (init pI958))) ∧ intTest pI958 (runFrom pI958 (fmask pI958) (cmask pI958) (hmask pI958) 1 957 (true, (init pI958), (init pI958))) 958 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I958_fin) true) (by decide) rfl I958_fin intTest_fst
theorem link958 : linkOK pL958 pH958 pI958 = true := by decide +kernel
theorem cvx958 : ConvexBetweenHumps 958 :=
  cvx_of L958_ok H958_ok I958_ok link958 (by decide)
theorem cenlink958 : cenLinkOK pI958 958 = true := by decide +kernel
theorem cen958 : CenterUniqueMin 958 ∧ DipHyp 958 ∧ OnePointHyps 958 :=
  cen_of L958_ok H958_ok I958_ok link958 cenlink958

/-! ### `N = 959` -/

def pL959 : Prm := ⟨76, 36, 37, 961, 11, 18446744073709551616, 178412758538399522, 178412758538399522⟩
def pH959 : Prm := ⟨76, 36, 37, 961, 11, 18446744073709551616, 178414957561655074, 178414957561655074⟩
def pI959 : Prm := ⟨64, 31, 30, 961, 11, 18446744073709551616, 178412758538399522, 178414957561655074⟩
theorem L959_fin : (prmOK pL959 959 && ptTest pL959 (runFrom pL959 (fmask pL959) (cmask pL959) (hmask pL959) 1 958 (true, (init pL959), (init pL959))) 959 480 false) = true := by
  decide +kernel
theorem L959_ok : RunOK pL959 959 (runFrom pL959 (fmask pL959) (cmask pL959) (hmask pL959) 1 958 (true, (init pL959), (init pL959))) ∧ ptTest pL959 (runFrom pL959 (fmask pL959) (cmask pL959) (hmask pL959) 1 958 (true, (init pL959), (init pL959))) 959 480 false = true :=
  fin_run (runOK_init (prmOK_of_and L959_fin) true) (by decide) rfl L959_fin ptTest_fst
theorem H959_fin : (prmOK pH959 959 && ptTest pH959 (runFrom pH959 (fmask pH959) (cmask pH959) (hmask pH959) 1 958 (true, (init pH959), (init pH959))) 959 480 true) = true := by
  decide +kernel
theorem H959_ok : RunOK pH959 959 (runFrom pH959 (fmask pH959) (cmask pH959) (hmask pH959) 1 958 (true, (init pH959), (init pH959))) ∧ ptTest pH959 (runFrom pH959 (fmask pH959) (cmask pH959) (hmask pH959) 1 958 (true, (init pH959), (init pH959))) 959 480 true = true :=
  fin_run (runOK_init (prmOK_of_and H959_fin) true) (by decide) rfl H959_fin ptTest_fst
theorem I959_fin : (prmOK pI959 959 && intTest pI959 (runFrom pI959 (fmask pI959) (cmask pI959) (hmask pI959) 1 958 (true, (init pI959), (init pI959))) 959 18 false) = true := by
  decide +kernel
theorem I959_ok : RunOK pI959 959 (runFrom pI959 (fmask pI959) (cmask pI959) (hmask pI959) 1 958 (true, (init pI959), (init pI959))) ∧ intTest pI959 (runFrom pI959 (fmask pI959) (cmask pI959) (hmask pI959) 1 958 (true, (init pI959), (init pI959))) 959 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I959_fin) true) (by decide) rfl I959_fin intTest_fst
theorem link959 : linkOK pL959 pH959 pI959 = true := by decide +kernel
theorem cvx959 : ConvexBetweenHumps 959 :=
  cvx_of L959_ok H959_ok I959_ok link959 (by decide)

/-! ### `N = 960` -/

def pL960 : Prm := ⟨76, 36, 37, 962, 11, 18446744073709551616, 178264743639635661, 178264743639635661⟩
def pH960 : Prm := ⟨76, 36, 37, 962, 11, 18446744073709551616, 178266942662891213, 178266942662891213⟩
def pI960 : Prm := ⟨64, 31, 30, 962, 11, 18446744073709551616, 178264743639635661, 178266942662891213⟩
theorem L960_fin : (prmOK pL960 960 && ptTest pL960 (runFrom pL960 (fmask pL960) (cmask pL960) (hmask pL960) 1 959 (true, (init pL960), (init pL960))) 960 480 false) = true := by
  decide +kernel
theorem L960_ok : RunOK pL960 960 (runFrom pL960 (fmask pL960) (cmask pL960) (hmask pL960) 1 959 (true, (init pL960), (init pL960))) ∧ ptTest pL960 (runFrom pL960 (fmask pL960) (cmask pL960) (hmask pL960) 1 959 (true, (init pL960), (init pL960))) 960 480 false = true :=
  fin_run (runOK_init (prmOK_of_and L960_fin) true) (by decide) rfl L960_fin ptTest_fst
theorem H960_fin : (prmOK pH960 960 && ptTest pH960 (runFrom pH960 (fmask pH960) (cmask pH960) (hmask pH960) 1 959 (true, (init pH960), (init pH960))) 960 480 true) = true := by
  decide +kernel
theorem H960_ok : RunOK pH960 960 (runFrom pH960 (fmask pH960) (cmask pH960) (hmask pH960) 1 959 (true, (init pH960), (init pH960))) ∧ ptTest pH960 (runFrom pH960 (fmask pH960) (cmask pH960) (hmask pH960) 1 959 (true, (init pH960), (init pH960))) 960 480 true = true :=
  fin_run (runOK_init (prmOK_of_and H960_fin) true) (by decide) rfl H960_fin ptTest_fst
theorem I960_fin : (prmOK pI960 960 && intTest pI960 (runFrom pI960 (fmask pI960) (cmask pI960) (hmask pI960) 1 959 (true, (init pI960), (init pI960))) 960 18 true) = true := by
  decide +kernel
theorem I960_ok : RunOK pI960 960 (runFrom pI960 (fmask pI960) (cmask pI960) (hmask pI960) 1 959 (true, (init pI960), (init pI960))) ∧ intTest pI960 (runFrom pI960 (fmask pI960) (cmask pI960) (hmask pI960) 1 959 (true, (init pI960), (init pI960))) 960 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I960_fin) true) (by decide) rfl I960_fin intTest_fst
theorem link960 : linkOK pL960 pH960 pI960 = true := by decide +kernel
theorem cvx960 : ConvexBetweenHumps 960 :=
  cvx_of L960_ok H960_ok I960_ok link960 (by decide)
theorem cenlink960 : cenLinkOK pI960 960 = true := by decide +kernel
theorem cen960 : CenterUniqueMin 960 ∧ DipHyp 960 ∧ OnePointHyps 960 :=
  cen_of L960_ok H960_ok I960_ok link960 cenlink960

/-! ### `N = 961` -/

def pL961 : Prm := ⟨76, 36, 37, 963, 11, 18446744073709551616, 178116866731298121, 178116866731298121⟩
def pH961 : Prm := ⟨76, 36, 37, 963, 11, 18446744073709551616, 178119065754553673, 178119065754553673⟩
def pI961 : Prm := ⟨64, 31, 30, 963, 11, 18446744073709551616, 178116866731298121, 178119065754553673⟩
theorem L961_fin : (prmOK pL961 961 && ptTest pL961 (runFrom pL961 (fmask pL961) (cmask pL961) (hmask pL961) 1 960 (true, (init pL961), (init pL961))) 961 481 false) = true := by
  decide +kernel
theorem L961_ok : RunOK pL961 961 (runFrom pL961 (fmask pL961) (cmask pL961) (hmask pL961) 1 960 (true, (init pL961), (init pL961))) ∧ ptTest pL961 (runFrom pL961 (fmask pL961) (cmask pL961) (hmask pL961) 1 960 (true, (init pL961), (init pL961))) 961 481 false = true :=
  fin_run (runOK_init (prmOK_of_and L961_fin) true) (by decide) rfl L961_fin ptTest_fst
theorem H961_fin : (prmOK pH961 961 && ptTest pH961 (runFrom pH961 (fmask pH961) (cmask pH961) (hmask pH961) 1 960 (true, (init pH961), (init pH961))) 961 481 true) = true := by
  decide +kernel
theorem H961_ok : RunOK pH961 961 (runFrom pH961 (fmask pH961) (cmask pH961) (hmask pH961) 1 960 (true, (init pH961), (init pH961))) ∧ ptTest pH961 (runFrom pH961 (fmask pH961) (cmask pH961) (hmask pH961) 1 960 (true, (init pH961), (init pH961))) 961 481 true = true :=
  fin_run (runOK_init (prmOK_of_and H961_fin) true) (by decide) rfl H961_fin ptTest_fst
theorem I961_fin : (prmOK pI961 961 && intTest pI961 (runFrom pI961 (fmask pI961) (cmask pI961) (hmask pI961) 1 960 (true, (init pI961), (init pI961))) 961 18 false) = true := by
  decide +kernel
theorem I961_ok : RunOK pI961 961 (runFrom pI961 (fmask pI961) (cmask pI961) (hmask pI961) 1 960 (true, (init pI961), (init pI961))) ∧ intTest pI961 (runFrom pI961 (fmask pI961) (cmask pI961) (hmask pI961) 1 960 (true, (init pI961), (init pI961))) 961 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I961_fin) true) (by decide) rfl I961_fin intTest_fst
theorem link961 : linkOK pL961 pH961 pI961 = true := by decide +kernel
theorem cvx961 : ConvexBetweenHumps 961 :=
  cvx_of L961_ok H961_ok I961_ok link961 (by decide)

/-! ### `N = 962` -/

def pL962 : Prm := ⟨76, 36, 37, 964, 11, 18446744073709551616, 177969388517992717, 177969388517992717⟩
def pH962 : Prm := ⟨76, 36, 37, 964, 11, 18446744073709551616, 177971587541248269, 177971587541248269⟩
def pI962 : Prm := ⟨64, 31, 30, 964, 11, 18446744073709551616, 177969388517992717, 177971587541248269⟩
theorem L962_fin : (prmOK pL962 962 && ptTest pL962 (runFrom pL962 (fmask pL962) (cmask pL962) (hmask pL962) 1 961 (true, (init pL962), (init pL962))) 962 481 false) = true := by
  decide +kernel
theorem L962_ok : RunOK pL962 962 (runFrom pL962 (fmask pL962) (cmask pL962) (hmask pL962) 1 961 (true, (init pL962), (init pL962))) ∧ ptTest pL962 (runFrom pL962 (fmask pL962) (cmask pL962) (hmask pL962) 1 961 (true, (init pL962), (init pL962))) 962 481 false = true :=
  fin_run (runOK_init (prmOK_of_and L962_fin) true) (by decide) rfl L962_fin ptTest_fst
theorem H962_fin : (prmOK pH962 962 && ptTest pH962 (runFrom pH962 (fmask pH962) (cmask pH962) (hmask pH962) 1 961 (true, (init pH962), (init pH962))) 962 481 true) = true := by
  decide +kernel
theorem H962_ok : RunOK pH962 962 (runFrom pH962 (fmask pH962) (cmask pH962) (hmask pH962) 1 961 (true, (init pH962), (init pH962))) ∧ ptTest pH962 (runFrom pH962 (fmask pH962) (cmask pH962) (hmask pH962) 1 961 (true, (init pH962), (init pH962))) 962 481 true = true :=
  fin_run (runOK_init (prmOK_of_and H962_fin) true) (by decide) rfl H962_fin ptTest_fst
theorem I962_fin : (prmOK pI962 962 && intTest pI962 (runFrom pI962 (fmask pI962) (cmask pI962) (hmask pI962) 1 961 (true, (init pI962), (init pI962))) 962 18 true) = true := by
  decide +kernel
theorem I962_ok : RunOK pI962 962 (runFrom pI962 (fmask pI962) (cmask pI962) (hmask pI962) 1 961 (true, (init pI962), (init pI962))) ∧ intTest pI962 (runFrom pI962 (fmask pI962) (cmask pI962) (hmask pI962) 1 961 (true, (init pI962), (init pI962))) 962 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I962_fin) true) (by decide) rfl I962_fin intTest_fst
theorem link962 : linkOK pL962 pH962 pI962 = true := by decide +kernel
theorem cvx962 : ConvexBetweenHumps 962 :=
  cvx_of L962_ok H962_ok I962_ok link962 (by decide)
theorem cenlink962 : cenLinkOK pI962 962 = true := by decide +kernel
theorem cen962 : CenterUniqueMin 962 ∧ DipHyp 962 ∧ OnePointHyps 962 :=
  cen_of L962_ok H962_ok I962_ok link962 cenlink962

/-! ### `N = 963` -/

def pL963 : Prm := ⟨76, 36, 37, 965, 11, 18446744073709551616, 177822047612823911, 177822047612823911⟩
def pH963 : Prm := ⟨76, 36, 37, 965, 11, 18446744073709551616, 177824246636079463, 177824246636079463⟩
def pI963 : Prm := ⟨64, 31, 30, 965, 11, 18446744073709551616, 177822047612823911, 177824246636079463⟩
theorem L963_fin : (prmOK pL963 963 && ptTest pL963 (runFrom pL963 (fmask pL963) (cmask pL963) (hmask pL963) 1 962 (true, (init pL963), (init pL963))) 963 482 false) = true := by
  decide +kernel
theorem L963_ok : RunOK pL963 963 (runFrom pL963 (fmask pL963) (cmask pL963) (hmask pL963) 1 962 (true, (init pL963), (init pL963))) ∧ ptTest pL963 (runFrom pL963 (fmask pL963) (cmask pL963) (hmask pL963) 1 962 (true, (init pL963), (init pL963))) 963 482 false = true :=
  fin_run (runOK_init (prmOK_of_and L963_fin) true) (by decide) rfl L963_fin ptTest_fst
theorem H963_fin : (prmOK pH963 963 && ptTest pH963 (runFrom pH963 (fmask pH963) (cmask pH963) (hmask pH963) 1 962 (true, (init pH963), (init pH963))) 963 482 true) = true := by
  decide +kernel
theorem H963_ok : RunOK pH963 963 (runFrom pH963 (fmask pH963) (cmask pH963) (hmask pH963) 1 962 (true, (init pH963), (init pH963))) ∧ ptTest pH963 (runFrom pH963 (fmask pH963) (cmask pH963) (hmask pH963) 1 962 (true, (init pH963), (init pH963))) 963 482 true = true :=
  fin_run (runOK_init (prmOK_of_and H963_fin) true) (by decide) rfl H963_fin ptTest_fst
theorem I963_fin : (prmOK pI963 963 && intTest pI963 (runFrom pI963 (fmask pI963) (cmask pI963) (hmask pI963) 1 962 (true, (init pI963), (init pI963))) 963 18 false) = true := by
  decide +kernel
theorem I963_ok : RunOK pI963 963 (runFrom pI963 (fmask pI963) (cmask pI963) (hmask pI963) 1 962 (true, (init pI963), (init pI963))) ∧ intTest pI963 (runFrom pI963 (fmask pI963) (cmask pI963) (hmask pI963) 1 962 (true, (init pI963), (init pI963))) 963 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I963_fin) true) (by decide) rfl I963_fin intTest_fst
theorem link963 : linkOK pL963 pH963 pI963 = true := by decide +kernel
theorem cvx963 : ConvexBetweenHumps 963 :=
  cvx_of L963_ok H963_ok I963_ok link963 (by decide)

/-! ### `N = 964` -/

def pL964 : Prm := ⟨76, 36, 37, 966, 11, 18446744073709551616, 177675103070336259, 177675103070336259⟩
def pH964 : Prm := ⟨76, 36, 37, 966, 11, 18446744073709551616, 177677302093591811, 177677302093591811⟩
def pI964 : Prm := ⟨64, 31, 30, 966, 11, 18446744073709551616, 177675103070336259, 177677302093591811⟩
theorem L964_fin : (prmOK pL964 964 && ptTest pL964 (runFrom pL964 (fmask pL964) (cmask pL964) (hmask pL964) 1 963 (true, (init pL964), (init pL964))) 964 482 false) = true := by
  decide +kernel
theorem L964_ok : RunOK pL964 964 (runFrom pL964 (fmask pL964) (cmask pL964) (hmask pL964) 1 963 (true, (init pL964), (init pL964))) ∧ ptTest pL964 (runFrom pL964 (fmask pL964) (cmask pL964) (hmask pL964) 1 963 (true, (init pL964), (init pL964))) 964 482 false = true :=
  fin_run (runOK_init (prmOK_of_and L964_fin) true) (by decide) rfl L964_fin ptTest_fst
theorem H964_fin : (prmOK pH964 964 && ptTest pH964 (runFrom pH964 (fmask pH964) (cmask pH964) (hmask pH964) 1 963 (true, (init pH964), (init pH964))) 964 482 true) = true := by
  decide +kernel
theorem H964_ok : RunOK pH964 964 (runFrom pH964 (fmask pH964) (cmask pH964) (hmask pH964) 1 963 (true, (init pH964), (init pH964))) ∧ ptTest pH964 (runFrom pH964 (fmask pH964) (cmask pH964) (hmask pH964) 1 963 (true, (init pH964), (init pH964))) 964 482 true = true :=
  fin_run (runOK_init (prmOK_of_and H964_fin) true) (by decide) rfl H964_fin ptTest_fst
theorem I964_fin : (prmOK pI964 964 && intTest pI964 (runFrom pI964 (fmask pI964) (cmask pI964) (hmask pI964) 1 963 (true, (init pI964), (init pI964))) 964 18 true) = true := by
  decide +kernel
theorem I964_ok : RunOK pI964 964 (runFrom pI964 (fmask pI964) (cmask pI964) (hmask pI964) 1 963 (true, (init pI964), (init pI964))) ∧ intTest pI964 (runFrom pI964 (fmask pI964) (cmask pI964) (hmask pI964) 1 963 (true, (init pI964), (init pI964))) 964 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I964_fin) true) (by decide) rfl I964_fin intTest_fst
theorem link964 : linkOK pL964 pH964 pI964 = true := by decide +kernel
theorem cvx964 : ConvexBetweenHumps 964 :=
  cvx_of L964_ok H964_ok I964_ok link964 (by decide)
theorem cenlink964 : cenLinkOK pI964 964 = true := by decide +kernel
theorem cen964 : CenterUniqueMin 964 ∧ DipHyp 964 ∧ OnePointHyps 964 :=
  cen_of L964_ok H964_ok I964_ok link964 cenlink964

/-! ### `N = 965` -/

def pL965 : Prm := ⟨76, 36, 37, 967, 11, 18446744073709551616, 177528295158251829, 177528295158251829⟩
def pH965 : Prm := ⟨76, 36, 37, 967, 11, 18446744073709551616, 177530494181507381, 177530494181507381⟩
def pI965 : Prm := ⟨64, 31, 30, 967, 11, 18446744073709551616, 177528295158251829, 177530494181507381⟩
theorem L965_fin : (prmOK pL965 965 && ptTest pL965 (runFrom pL965 (fmask pL965) (cmask pL965) (hmask pL965) 1 964 (true, (init pL965), (init pL965))) 965 483 false) = true := by
  decide +kernel
theorem L965_ok : RunOK pL965 965 (runFrom pL965 (fmask pL965) (cmask pL965) (hmask pL965) 1 964 (true, (init pL965), (init pL965))) ∧ ptTest pL965 (runFrom pL965 (fmask pL965) (cmask pL965) (hmask pL965) 1 964 (true, (init pL965), (init pL965))) 965 483 false = true :=
  fin_run (runOK_init (prmOK_of_and L965_fin) true) (by decide) rfl L965_fin ptTest_fst
theorem H965_fin : (prmOK pH965 965 && ptTest pH965 (runFrom pH965 (fmask pH965) (cmask pH965) (hmask pH965) 1 964 (true, (init pH965), (init pH965))) 965 483 true) = true := by
  decide +kernel
theorem H965_ok : RunOK pH965 965 (runFrom pH965 (fmask pH965) (cmask pH965) (hmask pH965) 1 964 (true, (init pH965), (init pH965))) ∧ ptTest pH965 (runFrom pH965 (fmask pH965) (cmask pH965) (hmask pH965) 1 964 (true, (init pH965), (init pH965))) 965 483 true = true :=
  fin_run (runOK_init (prmOK_of_and H965_fin) true) (by decide) rfl H965_fin ptTest_fst
theorem I965_fin : (prmOK pI965 965 && intTest pI965 (runFrom pI965 (fmask pI965) (cmask pI965) (hmask pI965) 1 964 (true, (init pI965), (init pI965))) 965 18 false) = true := by
  decide +kernel
theorem I965_ok : RunOK pI965 965 (runFrom pI965 (fmask pI965) (cmask pI965) (hmask pI965) 1 964 (true, (init pI965), (init pI965))) ∧ intTest pI965 (runFrom pI965 (fmask pI965) (cmask pI965) (hmask pI965) 1 964 (true, (init pI965), (init pI965))) 965 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I965_fin) true) (by decide) rfl I965_fin intTest_fst
theorem link965 : linkOK pL965 pH965 pI965 = true := by decide +kernel
theorem cvx965 : ConvexBetweenHumps 965 :=
  cvx_of L965_ok H965_ok I965_ok link965 (by decide)

/-! ### `N = 966` -/

def pL966 : Prm := ⟨76, 36, 37, 968, 11, 18446744073709551616, 177381881294925871, 177381881294925871⟩
def pH966 : Prm := ⟨76, 36, 37, 968, 11, 18446744073709551616, 177384080318181423, 177384080318181423⟩
def pI966 : Prm := ⟨64, 31, 30, 968, 11, 18446744073709551616, 177381881294925871, 177384080318181423⟩
theorem L966_fin : (prmOK pL966 966 && ptTest pL966 (runFrom pL966 (fmask pL966) (cmask pL966) (hmask pL966) 1 965 (true, (init pL966), (init pL966))) 966 483 false) = true := by
  decide +kernel
theorem L966_ok : RunOK pL966 966 (runFrom pL966 (fmask pL966) (cmask pL966) (hmask pL966) 1 965 (true, (init pL966), (init pL966))) ∧ ptTest pL966 (runFrom pL966 (fmask pL966) (cmask pL966) (hmask pL966) 1 965 (true, (init pL966), (init pL966))) 966 483 false = true :=
  fin_run (runOK_init (prmOK_of_and L966_fin) true) (by decide) rfl L966_fin ptTest_fst
theorem H966_fin : (prmOK pH966 966 && ptTest pH966 (runFrom pH966 (fmask pH966) (cmask pH966) (hmask pH966) 1 965 (true, (init pH966), (init pH966))) 966 483 true) = true := by
  decide +kernel
theorem H966_ok : RunOK pH966 966 (runFrom pH966 (fmask pH966) (cmask pH966) (hmask pH966) 1 965 (true, (init pH966), (init pH966))) ∧ ptTest pH966 (runFrom pH966 (fmask pH966) (cmask pH966) (hmask pH966) 1 965 (true, (init pH966), (init pH966))) 966 483 true = true :=
  fin_run (runOK_init (prmOK_of_and H966_fin) true) (by decide) rfl H966_fin ptTest_fst
theorem I966_fin : (prmOK pI966 966 && intTest pI966 (runFrom pI966 (fmask pI966) (cmask pI966) (hmask pI966) 1 965 (true, (init pI966), (init pI966))) 966 18 true) = true := by
  decide +kernel
theorem I966_ok : RunOK pI966 966 (runFrom pI966 (fmask pI966) (cmask pI966) (hmask pI966) 1 965 (true, (init pI966), (init pI966))) ∧ intTest pI966 (runFrom pI966 (fmask pI966) (cmask pI966) (hmask pI966) 1 965 (true, (init pI966), (init pI966))) 966 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I966_fin) true) (by decide) rfl I966_fin intTest_fst
theorem link966 : linkOK pL966 pH966 pI966 = true := by decide +kernel
theorem cvx966 : ConvexBetweenHumps 966 :=
  cvx_of L966_ok H966_ok I966_ok link966 (by decide)
theorem cenlink966 : cenLinkOK pI966 966 = true := by decide +kernel
theorem cen966 : CenterUniqueMin 966 ∧ DipHyp 966 ∧ OnePointHyps 966 :=
  cen_of L966_ok H966_ok I966_ok link966 cenlink966

/-! ### `N = 967` -/

def pL967 : Prm := ⟨76, 36, 37, 969, 11, 18446744073709551616, 177235603388789209, 177235603388789209⟩
def pH967 : Prm := ⟨76, 36, 37, 969, 11, 18446744073709551616, 177237802412044761, 177237802412044761⟩
def pI967 : Prm := ⟨64, 31, 30, 969, 11, 18446744073709551616, 177235603388789209, 177237802412044761⟩
theorem L967_fin : (prmOK pL967 967 && ptTest pL967 (runFrom pL967 (fmask pL967) (cmask pL967) (hmask pL967) 1 966 (true, (init pL967), (init pL967))) 967 484 false) = true := by
  decide +kernel
theorem L967_ok : RunOK pL967 967 (runFrom pL967 (fmask pL967) (cmask pL967) (hmask pL967) 1 966 (true, (init pL967), (init pL967))) ∧ ptTest pL967 (runFrom pL967 (fmask pL967) (cmask pL967) (hmask pL967) 1 966 (true, (init pL967), (init pL967))) 967 484 false = true :=
  fin_run (runOK_init (prmOK_of_and L967_fin) true) (by decide) rfl L967_fin ptTest_fst
theorem H967_fin : (prmOK pH967 967 && ptTest pH967 (runFrom pH967 (fmask pH967) (cmask pH967) (hmask pH967) 1 966 (true, (init pH967), (init pH967))) 967 484 true) = true := by
  decide +kernel
theorem H967_ok : RunOK pH967 967 (runFrom pH967 (fmask pH967) (cmask pH967) (hmask pH967) 1 966 (true, (init pH967), (init pH967))) ∧ ptTest pH967 (runFrom pH967 (fmask pH967) (cmask pH967) (hmask pH967) 1 966 (true, (init pH967), (init pH967))) 967 484 true = true :=
  fin_run (runOK_init (prmOK_of_and H967_fin) true) (by decide) rfl H967_fin ptTest_fst
theorem I967_fin : (prmOK pI967 967 && intTest pI967 (runFrom pI967 (fmask pI967) (cmask pI967) (hmask pI967) 1 966 (true, (init pI967), (init pI967))) 967 18 false) = true := by
  decide +kernel
theorem I967_ok : RunOK pI967 967 (runFrom pI967 (fmask pI967) (cmask pI967) (hmask pI967) 1 966 (true, (init pI967), (init pI967))) ∧ intTest pI967 (runFrom pI967 (fmask pI967) (cmask pI967) (hmask pI967) 1 966 (true, (init pI967), (init pI967))) 967 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I967_fin) true) (by decide) rfl I967_fin intTest_fst
theorem link967 : linkOK pL967 pH967 pI967 = true := by decide +kernel
theorem cvx967 : ConvexBetweenHumps 967 :=
  cvx_of L967_ok H967_ok I967_ok link967 (by decide)

/-! ### The range -/

theorem cvx_921_967 {N : ℕ} (h1 : 921 ≤ N) (h2 : N ≤ 967) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 943
  · by_cases h4 : N ≤ 931
    · by_cases h6 : N ≤ 925
      · by_cases h8 : N ≤ 922
        · by_cases h10 : N ≤ 921
          · obtain rfl : N = 921 := by omega
            exact cvx921
          · obtain rfl : N = 922 := by omega
            exact cvx922
        · by_cases h10 : N ≤ 923
          · obtain rfl : N = 923 := by omega
            exact cvx923
          · by_cases h12 : N ≤ 924
            · obtain rfl : N = 924 := by omega
              exact cvx924
            · obtain rfl : N = 925 := by omega
              exact cvx925
      · by_cases h8 : N ≤ 928
        · by_cases h10 : N ≤ 926
          · obtain rfl : N = 926 := by omega
            exact cvx926
          · by_cases h12 : N ≤ 927
            · obtain rfl : N = 927 := by omega
              exact cvx927
            · obtain rfl : N = 928 := by omega
              exact cvx928
        · by_cases h10 : N ≤ 929
          · obtain rfl : N = 929 := by omega
            exact cvx929
          · by_cases h12 : N ≤ 930
            · obtain rfl : N = 930 := by omega
              exact cvx930
            · obtain rfl : N = 931 := by omega
              exact cvx931
    · by_cases h6 : N ≤ 937
      · by_cases h8 : N ≤ 934
        · by_cases h10 : N ≤ 932
          · obtain rfl : N = 932 := by omega
            exact cvx932
          · by_cases h12 : N ≤ 933
            · obtain rfl : N = 933 := by omega
              exact cvx933
            · obtain rfl : N = 934 := by omega
              exact cvx934
        · by_cases h10 : N ≤ 935
          · obtain rfl : N = 935 := by omega
            exact cvx935
          · by_cases h12 : N ≤ 936
            · obtain rfl : N = 936 := by omega
              exact cvx936
            · obtain rfl : N = 937 := by omega
              exact cvx937
      · by_cases h8 : N ≤ 940
        · by_cases h10 : N ≤ 938
          · obtain rfl : N = 938 := by omega
            exact cvx938
          · by_cases h12 : N ≤ 939
            · obtain rfl : N = 939 := by omega
              exact cvx939
            · obtain rfl : N = 940 := by omega
              exact cvx940
        · by_cases h10 : N ≤ 941
          · obtain rfl : N = 941 := by omega
            exact cvx941
          · by_cases h12 : N ≤ 942
            · obtain rfl : N = 942 := by omega
              exact cvx942
            · obtain rfl : N = 943 := by omega
              exact cvx943
  · by_cases h4 : N ≤ 955
    · by_cases h6 : N ≤ 949
      · by_cases h8 : N ≤ 946
        · by_cases h10 : N ≤ 944
          · obtain rfl : N = 944 := by omega
            exact cvx944
          · by_cases h12 : N ≤ 945
            · obtain rfl : N = 945 := by omega
              exact cvx945
            · obtain rfl : N = 946 := by omega
              exact cvx946
        · by_cases h10 : N ≤ 947
          · obtain rfl : N = 947 := by omega
            exact cvx947
          · by_cases h12 : N ≤ 948
            · obtain rfl : N = 948 := by omega
              exact cvx948
            · obtain rfl : N = 949 := by omega
              exact cvx949
      · by_cases h8 : N ≤ 952
        · by_cases h10 : N ≤ 950
          · obtain rfl : N = 950 := by omega
            exact cvx950
          · by_cases h12 : N ≤ 951
            · obtain rfl : N = 951 := by omega
              exact cvx951
            · obtain rfl : N = 952 := by omega
              exact cvx952
        · by_cases h10 : N ≤ 953
          · obtain rfl : N = 953 := by omega
            exact cvx953
          · by_cases h12 : N ≤ 954
            · obtain rfl : N = 954 := by omega
              exact cvx954
            · obtain rfl : N = 955 := by omega
              exact cvx955
    · by_cases h6 : N ≤ 961
      · by_cases h8 : N ≤ 958
        · by_cases h10 : N ≤ 956
          · obtain rfl : N = 956 := by omega
            exact cvx956
          · by_cases h12 : N ≤ 957
            · obtain rfl : N = 957 := by omega
              exact cvx957
            · obtain rfl : N = 958 := by omega
              exact cvx958
        · by_cases h10 : N ≤ 959
          · obtain rfl : N = 959 := by omega
            exact cvx959
          · by_cases h12 : N ≤ 960
            · obtain rfl : N = 960 := by omega
              exact cvx960
            · obtain rfl : N = 961 := by omega
              exact cvx961
      · by_cases h8 : N ≤ 964
        · by_cases h10 : N ≤ 962
          · obtain rfl : N = 962 := by omega
            exact cvx962
          · by_cases h12 : N ≤ 963
            · obtain rfl : N = 963 := by omega
              exact cvx963
            · obtain rfl : N = 964 := by omega
              exact cvx964
        · by_cases h10 : N ≤ 965
          · obtain rfl : N = 965 := by omega
            exact cvx965
          · by_cases h12 : N ≤ 966
            · obtain rfl : N = 966 := by omega
              exact cvx966
            · obtain rfl : N = 967 := by omega
              exact cvx967

theorem cen_921_967 {N : ℕ} (h1 : 921 ≤ N) (h2 : N ≤ 967) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 942
  · by_cases h4 : N ≤ 930
    · by_cases h6 : N ≤ 924
      · by_cases h8 : N ≤ 922
        · obtain rfl : N = 922 := by omega
          exact cen922
        · obtain rfl : N = 924 := by omega
          exact cen924
      · by_cases h8 : N ≤ 926
        · obtain rfl : N = 926 := by omega
          exact cen926
        · by_cases h10 : N ≤ 928
          · obtain rfl : N = 928 := by omega
            exact cen928
          · obtain rfl : N = 930 := by omega
            exact cen930
    · by_cases h6 : N ≤ 936
      · by_cases h8 : N ≤ 932
        · obtain rfl : N = 932 := by omega
          exact cen932
        · by_cases h10 : N ≤ 934
          · obtain rfl : N = 934 := by omega
            exact cen934
          · obtain rfl : N = 936 := by omega
            exact cen936
      · by_cases h8 : N ≤ 938
        · obtain rfl : N = 938 := by omega
          exact cen938
        · by_cases h10 : N ≤ 940
          · obtain rfl : N = 940 := by omega
            exact cen940
          · obtain rfl : N = 942 := by omega
            exact cen942
  · by_cases h4 : N ≤ 954
    · by_cases h6 : N ≤ 948
      · by_cases h8 : N ≤ 944
        · obtain rfl : N = 944 := by omega
          exact cen944
        · by_cases h10 : N ≤ 946
          · obtain rfl : N = 946 := by omega
            exact cen946
          · obtain rfl : N = 948 := by omega
            exact cen948
      · by_cases h8 : N ≤ 950
        · obtain rfl : N = 950 := by omega
          exact cen950
        · by_cases h10 : N ≤ 952
          · obtain rfl : N = 952 := by omega
            exact cen952
          · obtain rfl : N = 954 := by omega
            exact cen954
    · by_cases h6 : N ≤ 960
      · by_cases h8 : N ≤ 956
        · obtain rfl : N = 956 := by omega
          exact cen956
        · by_cases h10 : N ≤ 958
          · obtain rfl : N = 958 := by omega
            exact cen958
          · obtain rfl : N = 960 := by omega
            exact cen960
      · by_cases h8 : N ≤ 962
        · obtain rfl : N = 962 := by omega
          exact cen962
        · by_cases h10 : N ≤ 964
          · obtain rfl : N = 964 := by omega
            exact cen964
          · obtain rfl : N = 966 := by omega
            exact cen966

end Kagey131.PaperD.T7
