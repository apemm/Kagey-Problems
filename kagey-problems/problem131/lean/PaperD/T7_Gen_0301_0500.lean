import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 301, …, 500` (generated)

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

/-! ### `N = 301` -/

def pL301 : Prm := ⟨67, 32, 32, 303, 11, 18446744073709551616, 434962097508269833, 434962097508269833⟩
def pH301 : Prm := ⟨67, 32, 32, 303, 11, 18446744073709551616, 434970893601292041, 434970893601292041⟩
def pI301 : Prm := ⟨57, 28, 26, 303, 11, 18446744073709551616, 434962097508269833, 434970893601292041⟩
theorem L301_fin : (prmOK pL301 301 && ptTest pL301 (runFrom pL301 (fmask pL301) (cmask pL301) (hmask pL301) 1 300 (true, (init pL301), (init pL301))) 301 151 false) = true := by
  decide +kernel
theorem L301_ok : RunOK pL301 301 (runFrom pL301 (fmask pL301) (cmask pL301) (hmask pL301) 1 300 (true, (init pL301), (init pL301))) ∧ ptTest pL301 (runFrom pL301 (fmask pL301) (cmask pL301) (hmask pL301) 1 300 (true, (init pL301), (init pL301))) 301 151 false = true :=
  fin_run (runOK_init (prmOK_of_and L301_fin) true) (by decide) rfl L301_fin ptTest_fst
theorem H301_fin : (prmOK pH301 301 && ptTest pH301 (runFrom pH301 (fmask pH301) (cmask pH301) (hmask pH301) 1 300 (true, (init pH301), (init pH301))) 301 151 true) = true := by
  decide +kernel
theorem H301_ok : RunOK pH301 301 (runFrom pH301 (fmask pH301) (cmask pH301) (hmask pH301) 1 300 (true, (init pH301), (init pH301))) ∧ ptTest pH301 (runFrom pH301 (fmask pH301) (cmask pH301) (hmask pH301) 1 300 (true, (init pH301), (init pH301))) 301 151 true = true :=
  fin_run (runOK_init (prmOK_of_and H301_fin) true) (by decide) rfl H301_fin ptTest_fst
theorem I301_fin : (prmOK pI301 301 && intTest pI301 (runFrom pI301 (fmask pI301) (cmask pI301) (hmask pI301) 1 300 (true, (init pI301), (init pI301))) 301 12 false) = true := by
  decide +kernel
theorem I301_ok : RunOK pI301 301 (runFrom pI301 (fmask pI301) (cmask pI301) (hmask pI301) 1 300 (true, (init pI301), (init pI301))) ∧ intTest pI301 (runFrom pI301 (fmask pI301) (cmask pI301) (hmask pI301) 1 300 (true, (init pI301), (init pI301))) 301 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I301_fin) true) (by decide) rfl I301_fin intTest_fst
theorem link301 : linkOK pL301 pH301 pI301 = true := by decide +kernel
theorem cvx301 : ConvexBetweenHumps 301 :=
  cvx_of L301_ok H301_ok I301_ok link301 (by decide)

/-! ### `N = 302` -/

def pL302 : Prm := ⟨67, 32, 32, 304, 11, 18446744073709551616, 433901687076418046, 433901687076418046⟩
def pH302 : Prm := ⟨67, 32, 32, 304, 11, 18446744073709551616, 433910483169440254, 433910483169440254⟩
def pI302 : Prm := ⟨57, 28, 26, 304, 11, 18446744073709551616, 433901687076418046, 433910483169440254⟩
theorem L302_fin : (prmOK pL302 302 && ptTest pL302 (runFrom pL302 (fmask pL302) (cmask pL302) (hmask pL302) 1 301 (true, (init pL302), (init pL302))) 302 151 false) = true := by
  decide +kernel
theorem L302_ok : RunOK pL302 302 (runFrom pL302 (fmask pL302) (cmask pL302) (hmask pL302) 1 301 (true, (init pL302), (init pL302))) ∧ ptTest pL302 (runFrom pL302 (fmask pL302) (cmask pL302) (hmask pL302) 1 301 (true, (init pL302), (init pL302))) 302 151 false = true :=
  fin_run (runOK_init (prmOK_of_and L302_fin) true) (by decide) rfl L302_fin ptTest_fst
theorem H302_fin : (prmOK pH302 302 && ptTest pH302 (runFrom pH302 (fmask pH302) (cmask pH302) (hmask pH302) 1 301 (true, (init pH302), (init pH302))) 302 151 true) = true := by
  decide +kernel
theorem H302_ok : RunOK pH302 302 (runFrom pH302 (fmask pH302) (cmask pH302) (hmask pH302) 1 301 (true, (init pH302), (init pH302))) ∧ ptTest pH302 (runFrom pH302 (fmask pH302) (cmask pH302) (hmask pH302) 1 301 (true, (init pH302), (init pH302))) 302 151 true = true :=
  fin_run (runOK_init (prmOK_of_and H302_fin) true) (by decide) rfl H302_fin ptTest_fst
theorem I302_fin : (prmOK pI302 302 && intTest pI302 (runFrom pI302 (fmask pI302) (cmask pI302) (hmask pI302) 1 301 (true, (init pI302), (init pI302))) 302 12 true) = true := by
  decide +kernel
theorem I302_ok : RunOK pI302 302 (runFrom pI302 (fmask pI302) (cmask pI302) (hmask pI302) 1 301 (true, (init pI302), (init pI302))) ∧ intTest pI302 (runFrom pI302 (fmask pI302) (cmask pI302) (hmask pI302) 1 301 (true, (init pI302), (init pI302))) 302 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I302_fin) true) (by decide) rfl I302_fin intTest_fst
theorem link302 : linkOK pL302 pH302 pI302 = true := by decide +kernel
theorem cvx302 : ConvexBetweenHumps 302 :=
  cvx_of L302_ok H302_ok I302_ok link302 (by decide)
theorem cenlink302 : cenLinkOK pI302 302 = true := by decide +kernel
theorem cen302 : CenterUniqueMin 302 ∧ DipHyp 302 ∧ OnePointHyps 302 :=
  cen_of L302_ok H302_ok I302_ok link302 cenlink302

/-! ### `N = 303` -/

def pL303 : Prm := ⟨67, 32, 32, 305, 11, 18446744073709551616, 432842647389910361, 432842647389910361⟩
def pH303 : Prm := ⟨67, 32, 32, 305, 11, 18446744073709551616, 432851443482932569, 432851443482932569⟩
def pI303 : Prm := ⟨57, 28, 26, 305, 11, 18446744073709551616, 432842647389910361, 432851443482932569⟩
theorem L303_fin : (prmOK pL303 303 && ptTest pL303 (runFrom pL303 (fmask pL303) (cmask pL303) (hmask pL303) 1 302 (true, (init pL303), (init pL303))) 303 152 false) = true := by
  decide +kernel
theorem L303_ok : RunOK pL303 303 (runFrom pL303 (fmask pL303) (cmask pL303) (hmask pL303) 1 302 (true, (init pL303), (init pL303))) ∧ ptTest pL303 (runFrom pL303 (fmask pL303) (cmask pL303) (hmask pL303) 1 302 (true, (init pL303), (init pL303))) 303 152 false = true :=
  fin_run (runOK_init (prmOK_of_and L303_fin) true) (by decide) rfl L303_fin ptTest_fst
theorem H303_fin : (prmOK pH303 303 && ptTest pH303 (runFrom pH303 (fmask pH303) (cmask pH303) (hmask pH303) 1 302 (true, (init pH303), (init pH303))) 303 152 true) = true := by
  decide +kernel
theorem H303_ok : RunOK pH303 303 (runFrom pH303 (fmask pH303) (cmask pH303) (hmask pH303) 1 302 (true, (init pH303), (init pH303))) ∧ ptTest pH303 (runFrom pH303 (fmask pH303) (cmask pH303) (hmask pH303) 1 302 (true, (init pH303), (init pH303))) 303 152 true = true :=
  fin_run (runOK_init (prmOK_of_and H303_fin) true) (by decide) rfl H303_fin ptTest_fst
theorem I303_fin : (prmOK pI303 303 && intTest pI303 (runFrom pI303 (fmask pI303) (cmask pI303) (hmask pI303) 1 302 (true, (init pI303), (init pI303))) 303 12 false) = true := by
  decide +kernel
theorem I303_ok : RunOK pI303 303 (runFrom pI303 (fmask pI303) (cmask pI303) (hmask pI303) 1 302 (true, (init pI303), (init pI303))) ∧ intTest pI303 (runFrom pI303 (fmask pI303) (cmask pI303) (hmask pI303) 1 302 (true, (init pI303), (init pI303))) 303 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I303_fin) true) (by decide) rfl I303_fin intTest_fst
theorem link303 : linkOK pL303 pH303 pI303 = true := by decide +kernel
theorem cvx303 : ConvexBetweenHumps 303 :=
  cvx_of L303_ok H303_ok I303_ok link303 (by decide)

/-! ### `N = 304` -/

def pL304 : Prm := ⟨65, 31, 31, 306, 11, 18446744073709551616, 431789349674186314, 431789349674186314⟩
def pH304 : Prm := ⟨65, 31, 31, 306, 11, 18446744073709551616, 431806941860230730, 431806941860230730⟩
def pI304 : Prm := ⟨57, 28, 26, 306, 11, 18446744073709551616, 431789349674186314, 431806941860230730⟩
theorem L304_fin : (prmOK pL304 304 && ptTest pL304 (runFrom pL304 (fmask pL304) (cmask pL304) (hmask pL304) 1 303 (true, (init pL304), (init pL304))) 304 152 false) = true := by
  decide +kernel
theorem L304_ok : RunOK pL304 304 (runFrom pL304 (fmask pL304) (cmask pL304) (hmask pL304) 1 303 (true, (init pL304), (init pL304))) ∧ ptTest pL304 (runFrom pL304 (fmask pL304) (cmask pL304) (hmask pL304) 1 303 (true, (init pL304), (init pL304))) 304 152 false = true :=
  fin_run (runOK_init (prmOK_of_and L304_fin) true) (by decide) rfl L304_fin ptTest_fst
theorem H304_fin : (prmOK pH304 304 && ptTest pH304 (runFrom pH304 (fmask pH304) (cmask pH304) (hmask pH304) 1 303 (true, (init pH304), (init pH304))) 304 152 true) = true := by
  decide +kernel
theorem H304_ok : RunOK pH304 304 (runFrom pH304 (fmask pH304) (cmask pH304) (hmask pH304) 1 303 (true, (init pH304), (init pH304))) ∧ ptTest pH304 (runFrom pH304 (fmask pH304) (cmask pH304) (hmask pH304) 1 303 (true, (init pH304), (init pH304))) 304 152 true = true :=
  fin_run (runOK_init (prmOK_of_and H304_fin) true) (by decide) rfl H304_fin ptTest_fst
theorem I304_fin : (prmOK pI304 304 && intTest pI304 (runFrom pI304 (fmask pI304) (cmask pI304) (hmask pI304) 1 303 (true, (init pI304), (init pI304))) 304 12 true) = true := by
  decide +kernel
theorem I304_ok : RunOK pI304 304 (runFrom pI304 (fmask pI304) (cmask pI304) (hmask pI304) 1 303 (true, (init pI304), (init pI304))) ∧ intTest pI304 (runFrom pI304 (fmask pI304) (cmask pI304) (hmask pI304) 1 303 (true, (init pI304), (init pI304))) 304 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I304_fin) true) (by decide) rfl I304_fin intTest_fst
theorem link304 : linkOK pL304 pH304 pI304 = true := by decide +kernel
theorem cvx304 : ConvexBetweenHumps 304 :=
  cvx_of L304_ok H304_ok I304_ok link304 (by decide)
theorem cenlink304 : cenLinkOK pI304 304 = true := by decide +kernel
theorem cen304 : CenterUniqueMin 304 ∧ DipHyp 304 ∧ OnePointHyps 304 :=
  cen_of L304_ok H304_ok I304_ok link304 cenlink304

/-! ### `N = 305` -/

def pL305 : Prm := ⟨65, 31, 31, 307, 11, 18446744073709551616, 430741809563418656, 430741809563418656⟩
def pH305 : Prm := ⟨65, 31, 31, 307, 11, 18446744073709551616, 430759401749463072, 430759401749463072⟩
def pI305 : Prm := ⟨57, 28, 26, 307, 11, 18446744073709551616, 430741809563418656, 430759401749463072⟩
theorem L305_fin : (prmOK pL305 305 && ptTest pL305 (runFrom pL305 (fmask pL305) (cmask pL305) (hmask pL305) 1 304 (true, (init pL305), (init pL305))) 305 153 false) = true := by
  decide +kernel
theorem L305_ok : RunOK pL305 305 (runFrom pL305 (fmask pL305) (cmask pL305) (hmask pL305) 1 304 (true, (init pL305), (init pL305))) ∧ ptTest pL305 (runFrom pL305 (fmask pL305) (cmask pL305) (hmask pL305) 1 304 (true, (init pL305), (init pL305))) 305 153 false = true :=
  fin_run (runOK_init (prmOK_of_and L305_fin) true) (by decide) rfl L305_fin ptTest_fst
theorem H305_fin : (prmOK pH305 305 && ptTest pH305 (runFrom pH305 (fmask pH305) (cmask pH305) (hmask pH305) 1 304 (true, (init pH305), (init pH305))) 305 153 true) = true := by
  decide +kernel
theorem H305_ok : RunOK pH305 305 (runFrom pH305 (fmask pH305) (cmask pH305) (hmask pH305) 1 304 (true, (init pH305), (init pH305))) ∧ ptTest pH305 (runFrom pH305 (fmask pH305) (cmask pH305) (hmask pH305) 1 304 (true, (init pH305), (init pH305))) 305 153 true = true :=
  fin_run (runOK_init (prmOK_of_and H305_fin) true) (by decide) rfl H305_fin ptTest_fst
theorem I305_fin : (prmOK pI305 305 && intTest pI305 (runFrom pI305 (fmask pI305) (cmask pI305) (hmask pI305) 1 304 (true, (init pI305), (init pI305))) 305 12 false) = true := by
  decide +kernel
theorem I305_ok : RunOK pI305 305 (runFrom pI305 (fmask pI305) (cmask pI305) (hmask pI305) 1 304 (true, (init pI305), (init pI305))) ∧ intTest pI305 (runFrom pI305 (fmask pI305) (cmask pI305) (hmask pI305) 1 304 (true, (init pI305), (init pI305))) 305 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I305_fin) true) (by decide) rfl I305_fin intTest_fst
theorem link305 : linkOK pL305 pH305 pI305 = true := by decide +kernel
theorem cvx305 : ConvexBetweenHumps 305 :=
  cvx_of L305_ok H305_ok I305_ok link305 (by decide)

/-! ### `N = 306` -/

def pL306 : Prm := ⟨65, 31, 31, 308, 11, 18446744073709551616, 429704225802116019, 429704225802116019⟩
def pH306 : Prm := ⟨65, 31, 31, 308, 11, 18446744073709551616, 429721817988160435, 429721817988160435⟩
def pI306 : Prm := ⟨57, 28, 26, 308, 11, 18446744073709551616, 429704225802116019, 429721817988160435⟩
theorem L306_fin : (prmOK pL306 306 && ptTest pL306 (runFrom pL306 (fmask pL306) (cmask pL306) (hmask pL306) 1 305 (true, (init pL306), (init pL306))) 306 153 false) = true := by
  decide +kernel
theorem L306_ok : RunOK pL306 306 (runFrom pL306 (fmask pL306) (cmask pL306) (hmask pL306) 1 305 (true, (init pL306), (init pL306))) ∧ ptTest pL306 (runFrom pL306 (fmask pL306) (cmask pL306) (hmask pL306) 1 305 (true, (init pL306), (init pL306))) 306 153 false = true :=
  fin_run (runOK_init (prmOK_of_and L306_fin) true) (by decide) rfl L306_fin ptTest_fst
theorem H306_fin : (prmOK pH306 306 && ptTest pH306 (runFrom pH306 (fmask pH306) (cmask pH306) (hmask pH306) 1 305 (true, (init pH306), (init pH306))) 306 153 true) = true := by
  decide +kernel
theorem H306_ok : RunOK pH306 306 (runFrom pH306 (fmask pH306) (cmask pH306) (hmask pH306) 1 305 (true, (init pH306), (init pH306))) ∧ ptTest pH306 (runFrom pH306 (fmask pH306) (cmask pH306) (hmask pH306) 1 305 (true, (init pH306), (init pH306))) 306 153 true = true :=
  fin_run (runOK_init (prmOK_of_and H306_fin) true) (by decide) rfl H306_fin ptTest_fst
theorem I306_fin : (prmOK pI306 306 && intTest pI306 (runFrom pI306 (fmask pI306) (cmask pI306) (hmask pI306) 1 305 (true, (init pI306), (init pI306))) 306 12 true) = true := by
  decide +kernel
theorem I306_ok : RunOK pI306 306 (runFrom pI306 (fmask pI306) (cmask pI306) (hmask pI306) 1 305 (true, (init pI306), (init pI306))) ∧ intTest pI306 (runFrom pI306 (fmask pI306) (cmask pI306) (hmask pI306) 1 305 (true, (init pI306), (init pI306))) 306 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I306_fin) true) (by decide) rfl I306_fin intTest_fst
theorem link306 : linkOK pL306 pH306 pI306 = true := by decide +kernel
theorem cvx306 : ConvexBetweenHumps 306 :=
  cvx_of L306_ok H306_ok I306_ok link306 (by decide)
theorem cenlink306 : cenLinkOK pI306 306 = true := by decide +kernel
theorem cen306 : CenterUniqueMin 306 ∧ DipHyp 306 ∧ OnePointHyps 306 :=
  cen_of L306_ok H306_ok I306_ok link306 cenlink306

/-! ### `N = 307` -/

def pL307 : Prm := ⟨65, 31, 31, 309, 11, 18446744073709551616, 428667990426692972, 428667990426692972⟩
def pH307 : Prm := ⟨65, 31, 31, 309, 11, 18446744073709551616, 428685582612737388, 428685582612737388⟩
def pI307 : Prm := ⟨57, 28, 26, 309, 11, 18446744073709551616, 428667990426692972, 428685582612737388⟩
theorem L307_fin : (prmOK pL307 307 && ptTest pL307 (runFrom pL307 (fmask pL307) (cmask pL307) (hmask pL307) 1 306 (true, (init pL307), (init pL307))) 307 154 false) = true := by
  decide +kernel
theorem L307_ok : RunOK pL307 307 (runFrom pL307 (fmask pL307) (cmask pL307) (hmask pL307) 1 306 (true, (init pL307), (init pL307))) ∧ ptTest pL307 (runFrom pL307 (fmask pL307) (cmask pL307) (hmask pL307) 1 306 (true, (init pL307), (init pL307))) 307 154 false = true :=
  fin_run (runOK_init (prmOK_of_and L307_fin) true) (by decide) rfl L307_fin ptTest_fst
theorem H307_fin : (prmOK pH307 307 && ptTest pH307 (runFrom pH307 (fmask pH307) (cmask pH307) (hmask pH307) 1 306 (true, (init pH307), (init pH307))) 307 154 true) = true := by
  decide +kernel
theorem H307_ok : RunOK pH307 307 (runFrom pH307 (fmask pH307) (cmask pH307) (hmask pH307) 1 306 (true, (init pH307), (init pH307))) ∧ ptTest pH307 (runFrom pH307 (fmask pH307) (cmask pH307) (hmask pH307) 1 306 (true, (init pH307), (init pH307))) 307 154 true = true :=
  fin_run (runOK_init (prmOK_of_and H307_fin) true) (by decide) rfl H307_fin ptTest_fst
theorem I307_fin : (prmOK pI307 307 && intTest pI307 (runFrom pI307 (fmask pI307) (cmask pI307) (hmask pI307) 1 306 (true, (init pI307), (init pI307))) 307 12 false) = true := by
  decide +kernel
theorem I307_ok : RunOK pI307 307 (runFrom pI307 (fmask pI307) (cmask pI307) (hmask pI307) 1 306 (true, (init pI307), (init pI307))) ∧ intTest pI307 (runFrom pI307 (fmask pI307) (cmask pI307) (hmask pI307) 1 306 (true, (init pI307), (init pI307))) 307 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I307_fin) true) (by decide) rfl I307_fin intTest_fst
theorem link307 : linkOK pL307 pH307 pI307 = true := by decide +kernel
theorem cvx307 : ConvexBetweenHumps 307 :=
  cvx_of L307_ok H307_ok I307_ok link307 (by decide)

/-! ### `N = 308` -/

def pL308 : Prm := ⟨65, 31, 31, 310, 11, 18446744073709551616, 427641532201702763, 427641532201702763⟩
def pH308 : Prm := ⟨65, 31, 31, 310, 11, 18446744073709551616, 427659124387747179, 427659124387747179⟩
def pI308 : Prm := ⟨57, 28, 26, 310, 11, 18446744073709551616, 427641532201702763, 427659124387747179⟩
theorem L308_fin : (prmOK pL308 308 && ptTest pL308 (runFrom pL308 (fmask pL308) (cmask pL308) (hmask pL308) 1 307 (true, (init pL308), (init pL308))) 308 154 false) = true := by
  decide +kernel
theorem L308_ok : RunOK pL308 308 (runFrom pL308 (fmask pL308) (cmask pL308) (hmask pL308) 1 307 (true, (init pL308), (init pL308))) ∧ ptTest pL308 (runFrom pL308 (fmask pL308) (cmask pL308) (hmask pL308) 1 307 (true, (init pL308), (init pL308))) 308 154 false = true :=
  fin_run (runOK_init (prmOK_of_and L308_fin) true) (by decide) rfl L308_fin ptTest_fst
theorem H308_fin : (prmOK pH308 308 && ptTest pH308 (runFrom pH308 (fmask pH308) (cmask pH308) (hmask pH308) 1 307 (true, (init pH308), (init pH308))) 308 154 true) = true := by
  decide +kernel
theorem H308_ok : RunOK pH308 308 (runFrom pH308 (fmask pH308) (cmask pH308) (hmask pH308) 1 307 (true, (init pH308), (init pH308))) ∧ ptTest pH308 (runFrom pH308 (fmask pH308) (cmask pH308) (hmask pH308) 1 307 (true, (init pH308), (init pH308))) 308 154 true = true :=
  fin_run (runOK_init (prmOK_of_and H308_fin) true) (by decide) rfl H308_fin ptTest_fst
theorem I308_fin : (prmOK pI308 308 && intTest pI308 (runFrom pI308 (fmask pI308) (cmask pI308) (hmask pI308) 1 307 (true, (init pI308), (init pI308))) 308 12 true) = true := by
  decide +kernel
theorem I308_ok : RunOK pI308 308 (runFrom pI308 (fmask pI308) (cmask pI308) (hmask pI308) 1 307 (true, (init pI308), (init pI308))) ∧ intTest pI308 (runFrom pI308 (fmask pI308) (cmask pI308) (hmask pI308) 1 307 (true, (init pI308), (init pI308))) 308 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I308_fin) true) (by decide) rfl I308_fin intTest_fst
theorem link308 : linkOK pL308 pH308 pI308 = true := by decide +kernel
theorem cvx308 : ConvexBetweenHumps 308 :=
  cvx_of L308_ok H308_ok I308_ok link308 (by decide)
theorem cenlink308 : cenLinkOK pI308 308 = true := by decide +kernel
theorem cen308 : CenterUniqueMin 308 ∧ DipHyp 308 ∧ OnePointHyps 308 :=
  cen_of L308_ok H308_ok I308_ok link308 cenlink308

/-! ### `N = 309` -/

def pL309 : Prm := ⟨65, 31, 31, 311, 11, 18446744073709551616, 426616411210244078, 426616411210244078⟩
def pH309 : Prm := ⟨65, 31, 31, 311, 11, 18446744073709551616, 426634003396288494, 426634003396288494⟩
def pI309 : Prm := ⟨57, 28, 26, 311, 11, 18446744073709551616, 426616411210244078, 426634003396288494⟩
theorem L309_fin : (prmOK pL309 309 && ptTest pL309 (runFrom pL309 (fmask pL309) (cmask pL309) (hmask pL309) 1 308 (true, (init pL309), (init pL309))) 309 155 false) = true := by
  decide +kernel
theorem L309_ok : RunOK pL309 309 (runFrom pL309 (fmask pL309) (cmask pL309) (hmask pL309) 1 308 (true, (init pL309), (init pL309))) ∧ ptTest pL309 (runFrom pL309 (fmask pL309) (cmask pL309) (hmask pL309) 1 308 (true, (init pL309), (init pL309))) 309 155 false = true :=
  fin_run (runOK_init (prmOK_of_and L309_fin) true) (by decide) rfl L309_fin ptTest_fst
theorem H309_fin : (prmOK pH309 309 && ptTest pH309 (runFrom pH309 (fmask pH309) (cmask pH309) (hmask pH309) 1 308 (true, (init pH309), (init pH309))) 309 155 true) = true := by
  decide +kernel
theorem H309_ok : RunOK pH309 309 (runFrom pH309 (fmask pH309) (cmask pH309) (hmask pH309) 1 308 (true, (init pH309), (init pH309))) ∧ ptTest pH309 (runFrom pH309 (fmask pH309) (cmask pH309) (hmask pH309) 1 308 (true, (init pH309), (init pH309))) 309 155 true = true :=
  fin_run (runOK_init (prmOK_of_and H309_fin) true) (by decide) rfl H309_fin ptTest_fst
theorem I309_fin : (prmOK pI309 309 && intTest pI309 (runFrom pI309 (fmask pI309) (cmask pI309) (hmask pI309) 1 308 (true, (init pI309), (init pI309))) 309 12 false) = true := by
  decide +kernel
theorem I309_ok : RunOK pI309 309 (runFrom pI309 (fmask pI309) (cmask pI309) (hmask pI309) 1 308 (true, (init pI309), (init pI309))) ∧ intTest pI309 (runFrom pI309 (fmask pI309) (cmask pI309) (hmask pI309) 1 308 (true, (init pI309), (init pI309))) 309 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I309_fin) true) (by decide) rfl I309_fin intTest_fst
theorem link309 : linkOK pL309 pH309 pI309 = true := by decide +kernel
theorem cvx309 : ConvexBetweenHumps 309 :=
  cvx_of L309_ok H309_ok I309_ok link309 (by decide)

/-! ### `N = 310` -/

def pL310 : Prm := ⟨65, 31, 31, 312, 11, 18446744073709551616, 425600892502846615, 425600892502846615⟩
def pH310 : Prm := ⟨65, 31, 31, 312, 11, 18446744073709551616, 425618484688891031, 425618484688891031⟩
def pI310 : Prm := ⟨57, 28, 26, 312, 11, 18446744073709551616, 425600892502846615, 425618484688891031⟩
theorem L310_fin : (prmOK pL310 310 && ptTest pL310 (runFrom pL310 (fmask pL310) (cmask pL310) (hmask pL310) 1 309 (true, (init pL310), (init pL310))) 310 155 false) = true := by
  decide +kernel
theorem L310_ok : RunOK pL310 310 (runFrom pL310 (fmask pL310) (cmask pL310) (hmask pL310) 1 309 (true, (init pL310), (init pL310))) ∧ ptTest pL310 (runFrom pL310 (fmask pL310) (cmask pL310) (hmask pL310) 1 309 (true, (init pL310), (init pL310))) 310 155 false = true :=
  fin_run (runOK_init (prmOK_of_and L310_fin) true) (by decide) rfl L310_fin ptTest_fst
theorem H310_fin : (prmOK pH310 310 && ptTest pH310 (runFrom pH310 (fmask pH310) (cmask pH310) (hmask pH310) 1 309 (true, (init pH310), (init pH310))) 310 155 true) = true := by
  decide +kernel
theorem H310_ok : RunOK pH310 310 (runFrom pH310 (fmask pH310) (cmask pH310) (hmask pH310) 1 309 (true, (init pH310), (init pH310))) ∧ ptTest pH310 (runFrom pH310 (fmask pH310) (cmask pH310) (hmask pH310) 1 309 (true, (init pH310), (init pH310))) 310 155 true = true :=
  fin_run (runOK_init (prmOK_of_and H310_fin) true) (by decide) rfl H310_fin ptTest_fst
theorem I310_fin : (prmOK pI310 310 && intTest pI310 (runFrom pI310 (fmask pI310) (cmask pI310) (hmask pI310) 1 309 (true, (init pI310), (init pI310))) 310 12 true) = true := by
  decide +kernel
theorem I310_ok : RunOK pI310 310 (runFrom pI310 (fmask pI310) (cmask pI310) (hmask pI310) 1 309 (true, (init pI310), (init pI310))) ∧ intTest pI310 (runFrom pI310 (fmask pI310) (cmask pI310) (hmask pI310) 1 309 (true, (init pI310), (init pI310))) 310 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I310_fin) true) (by decide) rfl I310_fin intTest_fst
theorem link310 : linkOK pL310 pH310 pI310 = true := by decide +kernel
theorem cvx310 : ConvexBetweenHumps 310 :=
  cvx_of L310_ok H310_ok I310_ok link310 (by decide)
theorem cenlink310 : cenLinkOK pI310 310 = true := by decide +kernel
theorem cen310 : CenterUniqueMin 310 ∧ DipHyp 310 ∧ OnePointHyps 310 :=
  cen_of L310_ok H310_ok I310_ok link310 cenlink310

/-! ### `N = 311` -/

def pL311 : Prm := ⟨65, 31, 31, 313, 11, 18446744073709551616, 424586699902236694, 424586699902236694⟩
def pH311 : Prm := ⟨65, 31, 31, 313, 11, 18446744073709551616, 424604292088281110, 424604292088281110⟩
def pI311 : Prm := ⟨57, 28, 26, 313, 11, 18446744073709551616, 424586699902236694, 424604292088281110⟩
theorem L311_fin : (prmOK pL311 311 && ptTest pL311 (runFrom pL311 (fmask pL311) (cmask pL311) (hmask pL311) 1 310 (true, (init pL311), (init pL311))) 311 156 false) = true := by
  decide +kernel
theorem L311_ok : RunOK pL311 311 (runFrom pL311 (fmask pL311) (cmask pL311) (hmask pL311) 1 310 (true, (init pL311), (init pL311))) ∧ ptTest pL311 (runFrom pL311 (fmask pL311) (cmask pL311) (hmask pL311) 1 310 (true, (init pL311), (init pL311))) 311 156 false = true :=
  fin_run (runOK_init (prmOK_of_and L311_fin) true) (by decide) rfl L311_fin ptTest_fst
theorem H311_fin : (prmOK pH311 311 && ptTest pH311 (runFrom pH311 (fmask pH311) (cmask pH311) (hmask pH311) 1 310 (true, (init pH311), (init pH311))) 311 156 true) = true := by
  decide +kernel
theorem H311_ok : RunOK pH311 311 (runFrom pH311 (fmask pH311) (cmask pH311) (hmask pH311) 1 310 (true, (init pH311), (init pH311))) ∧ ptTest pH311 (runFrom pH311 (fmask pH311) (cmask pH311) (hmask pH311) 1 310 (true, (init pH311), (init pH311))) 311 156 true = true :=
  fin_run (runOK_init (prmOK_of_and H311_fin) true) (by decide) rfl H311_fin ptTest_fst
theorem I311_fin : (prmOK pI311 311 && intTest pI311 (runFrom pI311 (fmask pI311) (cmask pI311) (hmask pI311) 1 310 (true, (init pI311), (init pI311))) 311 12 false) = true := by
  decide +kernel
theorem I311_ok : RunOK pI311 311 (runFrom pI311 (fmask pI311) (cmask pI311) (hmask pI311) 1 310 (true, (init pI311), (init pI311))) ∧ intTest pI311 (runFrom pI311 (fmask pI311) (cmask pI311) (hmask pI311) 1 310 (true, (init pI311), (init pI311))) 311 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I311_fin) true) (by decide) rfl I311_fin intTest_fst
theorem link311 : linkOK pL311 pH311 pI311 = true := by decide +kernel
theorem cvx311 : ConvexBetweenHumps 311 :=
  cvx_of L311_ok H311_ok I311_ok link311 (by decide)

/-! ### `N = 312` -/

def pL312 : Prm := ⟨65, 31, 31, 314, 11, 18446744073709551616, 423581938920783704, 423581938920783704⟩
def pH312 : Prm := ⟨65, 31, 31, 314, 11, 18446744073709551616, 423599531106828120, 423599531106828120⟩
def pI312 : Prm := ⟨57, 28, 26, 314, 11, 18446744073709551616, 423581938920783704, 423599531106828120⟩
theorem L312_fin : (prmOK pL312 312 && ptTest pL312 (runFrom pL312 (fmask pL312) (cmask pL312) (hmask pL312) 1 311 (true, (init pL312), (init pL312))) 312 156 false) = true := by
  decide +kernel
theorem L312_ok : RunOK pL312 312 (runFrom pL312 (fmask pL312) (cmask pL312) (hmask pL312) 1 311 (true, (init pL312), (init pL312))) ∧ ptTest pL312 (runFrom pL312 (fmask pL312) (cmask pL312) (hmask pL312) 1 311 (true, (init pL312), (init pL312))) 312 156 false = true :=
  fin_run (runOK_init (prmOK_of_and L312_fin) true) (by decide) rfl L312_fin ptTest_fst
theorem H312_fin : (prmOK pH312 312 && ptTest pH312 (runFrom pH312 (fmask pH312) (cmask pH312) (hmask pH312) 1 311 (true, (init pH312), (init pH312))) 312 156 true) = true := by
  decide +kernel
theorem H312_ok : RunOK pH312 312 (runFrom pH312 (fmask pH312) (cmask pH312) (hmask pH312) 1 311 (true, (init pH312), (init pH312))) ∧ ptTest pH312 (runFrom pH312 (fmask pH312) (cmask pH312) (hmask pH312) 1 311 (true, (init pH312), (init pH312))) 312 156 true = true :=
  fin_run (runOK_init (prmOK_of_and H312_fin) true) (by decide) rfl H312_fin ptTest_fst
theorem I312_fin : (prmOK pI312 312 && intTest pI312 (runFrom pI312 (fmask pI312) (cmask pI312) (hmask pI312) 1 311 (true, (init pI312), (init pI312))) 312 12 true) = true := by
  decide +kernel
theorem I312_ok : RunOK pI312 312 (runFrom pI312 (fmask pI312) (cmask pI312) (hmask pI312) 1 311 (true, (init pI312), (init pI312))) ∧ intTest pI312 (runFrom pI312 (fmask pI312) (cmask pI312) (hmask pI312) 1 311 (true, (init pI312), (init pI312))) 312 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I312_fin) true) (by decide) rfl I312_fin intTest_fst
theorem link312 : linkOK pL312 pH312 pI312 = true := by decide +kernel
theorem cvx312 : ConvexBetweenHumps 312 :=
  cvx_of L312_ok H312_ok I312_ok link312 (by decide)
theorem cenlink312 : cenLinkOK pI312 312 = true := by decide +kernel
theorem cen312 : CenterUniqueMin 312 ∧ DipHyp 312 ∧ OnePointHyps 312 :=
  cen_of L312_ok H312_ok I312_ok link312 cenlink312

/-! ### `N = 313` -/

def pL313 : Prm := ⟨65, 31, 31, 315, 11, 18446744073709551616, 422578492950106546, 422578492950106546⟩
def pH313 : Prm := ⟨65, 31, 31, 315, 11, 18446744073709551616, 422596085136150962, 422596085136150962⟩
def pI313 : Prm := ⟨57, 28, 26, 315, 11, 18446744073709551616, 422578492950106546, 422596085136150962⟩
theorem L313_fin : (prmOK pL313 313 && ptTest pL313 (runFrom pL313 (fmask pL313) (cmask pL313) (hmask pL313) 1 312 (true, (init pL313), (init pL313))) 313 157 false) = true := by
  decide +kernel
theorem L313_ok : RunOK pL313 313 (runFrom pL313 (fmask pL313) (cmask pL313) (hmask pL313) 1 312 (true, (init pL313), (init pL313))) ∧ ptTest pL313 (runFrom pL313 (fmask pL313) (cmask pL313) (hmask pL313) 1 312 (true, (init pL313), (init pL313))) 313 157 false = true :=
  fin_run (runOK_init (prmOK_of_and L313_fin) true) (by decide) rfl L313_fin ptTest_fst
theorem H313_fin : (prmOK pH313 313 && ptTest pH313 (runFrom pH313 (fmask pH313) (cmask pH313) (hmask pH313) 1 312 (true, (init pH313), (init pH313))) 313 157 true) = true := by
  decide +kernel
theorem H313_ok : RunOK pH313 313 (runFrom pH313 (fmask pH313) (cmask pH313) (hmask pH313) 1 312 (true, (init pH313), (init pH313))) ∧ ptTest pH313 (runFrom pH313 (fmask pH313) (cmask pH313) (hmask pH313) 1 312 (true, (init pH313), (init pH313))) 313 157 true = true :=
  fin_run (runOK_init (prmOK_of_and H313_fin) true) (by decide) rfl H313_fin ptTest_fst
theorem I313_fin : (prmOK pI313 313 && intTest pI313 (runFrom pI313 (fmask pI313) (cmask pI313) (hmask pI313) 1 312 (true, (init pI313), (init pI313))) 313 12 false) = true := by
  decide +kernel
theorem I313_ok : RunOK pI313 313 (runFrom pI313 (fmask pI313) (cmask pI313) (hmask pI313) 1 312 (true, (init pI313), (init pI313))) ∧ intTest pI313 (runFrom pI313 (fmask pI313) (cmask pI313) (hmask pI313) 1 312 (true, (init pI313), (init pI313))) 313 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I313_fin) true) (by decide) rfl I313_fin intTest_fst
theorem link313 : linkOK pL313 pH313 pI313 = true := by decide +kernel
theorem cvx313 : ConvexBetweenHumps 313 :=
  cvx_of L313_ok H313_ok I313_ok link313 (by decide)

/-! ### `N = 314` -/

def pL314 : Prm := ⟨65, 31, 31, 316, 11, 18446744073709551616, 421584312008789154, 421584312008789154⟩
def pH314 : Prm := ⟨65, 31, 31, 316, 11, 18446744073709551616, 421601904194833570, 421601904194833570⟩
def pI314 : Prm := ⟨57, 28, 26, 316, 11, 18446744073709551616, 421584312008789154, 421601904194833570⟩
theorem L314_fin : (prmOK pL314 314 && ptTest pL314 (runFrom pL314 (fmask pL314) (cmask pL314) (hmask pL314) 1 313 (true, (init pL314), (init pL314))) 314 157 false) = true := by
  decide +kernel
theorem L314_ok : RunOK pL314 314 (runFrom pL314 (fmask pL314) (cmask pL314) (hmask pL314) 1 313 (true, (init pL314), (init pL314))) ∧ ptTest pL314 (runFrom pL314 (fmask pL314) (cmask pL314) (hmask pL314) 1 313 (true, (init pL314), (init pL314))) 314 157 false = true :=
  fin_run (runOK_init (prmOK_of_and L314_fin) true) (by decide) rfl L314_fin ptTest_fst
theorem H314_fin : (prmOK pH314 314 && ptTest pH314 (runFrom pH314 (fmask pH314) (cmask pH314) (hmask pH314) 1 313 (true, (init pH314), (init pH314))) 314 157 true) = true := by
  decide +kernel
theorem H314_ok : RunOK pH314 314 (runFrom pH314 (fmask pH314) (cmask pH314) (hmask pH314) 1 313 (true, (init pH314), (init pH314))) ∧ ptTest pH314 (runFrom pH314 (fmask pH314) (cmask pH314) (hmask pH314) 1 313 (true, (init pH314), (init pH314))) 314 157 true = true :=
  fin_run (runOK_init (prmOK_of_and H314_fin) true) (by decide) rfl H314_fin ptTest_fst
theorem I314_fin : (prmOK pI314 314 && intTest pI314 (runFrom pI314 (fmask pI314) (cmask pI314) (hmask pI314) 1 313 (true, (init pI314), (init pI314))) 314 12 true) = true := by
  decide +kernel
theorem I314_ok : RunOK pI314 314 (runFrom pI314 (fmask pI314) (cmask pI314) (hmask pI314) 1 313 (true, (init pI314), (init pI314))) ∧ intTest pI314 (runFrom pI314 (fmask pI314) (cmask pI314) (hmask pI314) 1 313 (true, (init pI314), (init pI314))) 314 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I314_fin) true) (by decide) rfl I314_fin intTest_fst
theorem link314 : linkOK pL314 pH314 pI314 = true := by decide +kernel
theorem cvx314 : ConvexBetweenHumps 314 :=
  cvx_of L314_ok H314_ok I314_ok link314 (by decide)
theorem cenlink314 : cenLinkOK pI314 314 = true := by decide +kernel
theorem cen314 : CenterUniqueMin 314 ∧ DipHyp 314 ∧ OnePointHyps 314 :=
  cen_of L314_ok H314_ok I314_ok link314 cenlink314

/-! ### `N = 315` -/

def pL315 : Prm := ⟨65, 31, 31, 317, 11, 18446744073709551616, 420591435017598296, 420591435017598296⟩
def pH315 : Prm := ⟨65, 31, 31, 317, 11, 18446744073709551616, 420609027203642712, 420609027203642712⟩
def pI315 : Prm := ⟨57, 28, 26, 317, 11, 18446744073709551616, 420591435017598296, 420609027203642712⟩
theorem L315_fin : (prmOK pL315 315 && ptTest pL315 (runFrom pL315 (fmask pL315) (cmask pL315) (hmask pL315) 1 314 (true, (init pL315), (init pL315))) 315 158 false) = true := by
  decide +kernel
theorem L315_ok : RunOK pL315 315 (runFrom pL315 (fmask pL315) (cmask pL315) (hmask pL315) 1 314 (true, (init pL315), (init pL315))) ∧ ptTest pL315 (runFrom pL315 (fmask pL315) (cmask pL315) (hmask pL315) 1 314 (true, (init pL315), (init pL315))) 315 158 false = true :=
  fin_run (runOK_init (prmOK_of_and L315_fin) true) (by decide) rfl L315_fin ptTest_fst
theorem H315_fin : (prmOK pH315 315 && ptTest pH315 (runFrom pH315 (fmask pH315) (cmask pH315) (hmask pH315) 1 314 (true, (init pH315), (init pH315))) 315 158 true) = true := by
  decide +kernel
theorem H315_ok : RunOK pH315 315 (runFrom pH315 (fmask pH315) (cmask pH315) (hmask pH315) 1 314 (true, (init pH315), (init pH315))) ∧ ptTest pH315 (runFrom pH315 (fmask pH315) (cmask pH315) (hmask pH315) 1 314 (true, (init pH315), (init pH315))) 315 158 true = true :=
  fin_run (runOK_init (prmOK_of_and H315_fin) true) (by decide) rfl H315_fin ptTest_fst
theorem I315_fin : (prmOK pI315 315 && intTest pI315 (runFrom pI315 (fmask pI315) (cmask pI315) (hmask pI315) 1 314 (true, (init pI315), (init pI315))) 315 12 false) = true := by
  decide +kernel
theorem I315_ok : RunOK pI315 315 (runFrom pI315 (fmask pI315) (cmask pI315) (hmask pI315) 1 314 (true, (init pI315), (init pI315))) ∧ intTest pI315 (runFrom pI315 (fmask pI315) (cmask pI315) (hmask pI315) 1 314 (true, (init pI315), (init pI315))) 315 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I315_fin) true) (by decide) rfl I315_fin intTest_fst
theorem link315 : linkOK pL315 pH315 pI315 = true := by decide +kernel
theorem cvx315 : ConvexBetweenHumps 315 :=
  cvx_of L315_ok H315_ok I315_ok link315 (by decide)

/-! ### `N = 316` -/

def pL316 : Prm := ⟨65, 31, 31, 318, 11, 18446744073709551616, 419607660419181080, 419607660419181080⟩
def pH316 : Prm := ⟨65, 31, 31, 318, 11, 18446744073709551616, 419625252605225496, 419625252605225496⟩
def pI316 : Prm := ⟨57, 28, 26, 318, 11, 18446744073709551616, 419607660419181080, 419625252605225496⟩
theorem L316_fin : (prmOK pL316 316 && ptTest pL316 (runFrom pL316 (fmask pL316) (cmask pL316) (hmask pL316) 1 315 (true, (init pL316), (init pL316))) 316 158 false) = true := by
  decide +kernel
theorem L316_ok : RunOK pL316 316 (runFrom pL316 (fmask pL316) (cmask pL316) (hmask pL316) 1 315 (true, (init pL316), (init pL316))) ∧ ptTest pL316 (runFrom pL316 (fmask pL316) (cmask pL316) (hmask pL316) 1 315 (true, (init pL316), (init pL316))) 316 158 false = true :=
  fin_run (runOK_init (prmOK_of_and L316_fin) true) (by decide) rfl L316_fin ptTest_fst
theorem H316_fin : (prmOK pH316 316 && ptTest pH316 (runFrom pH316 (fmask pH316) (cmask pH316) (hmask pH316) 1 315 (true, (init pH316), (init pH316))) 316 158 true) = true := by
  decide +kernel
theorem H316_ok : RunOK pH316 316 (runFrom pH316 (fmask pH316) (cmask pH316) (hmask pH316) 1 315 (true, (init pH316), (init pH316))) ∧ ptTest pH316 (runFrom pH316 (fmask pH316) (cmask pH316) (hmask pH316) 1 315 (true, (init pH316), (init pH316))) 316 158 true = true :=
  fin_run (runOK_init (prmOK_of_and H316_fin) true) (by decide) rfl H316_fin ptTest_fst
theorem I316_fin : (prmOK pI316 316 && intTest pI316 (runFrom pI316 (fmask pI316) (cmask pI316) (hmask pI316) 1 315 (true, (init pI316), (init pI316))) 316 12 true) = true := by
  decide +kernel
theorem I316_ok : RunOK pI316 316 (runFrom pI316 (fmask pI316) (cmask pI316) (hmask pI316) 1 315 (true, (init pI316), (init pI316))) ∧ intTest pI316 (runFrom pI316 (fmask pI316) (cmask pI316) (hmask pI316) 1 315 (true, (init pI316), (init pI316))) 316 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I316_fin) true) (by decide) rfl I316_fin intTest_fst
theorem link316 : linkOK pL316 pH316 pI316 = true := by decide +kernel
theorem cvx316 : ConvexBetweenHumps 316 :=
  cvx_of L316_ok H316_ok I316_ok link316 (by decide)
theorem cenlink316 : cenLinkOK pI316 316 = true := by decide +kernel
theorem cen316 : CenterUniqueMin 316 ∧ DipHyp 316 ∧ OnePointHyps 316 :=
  cen_of L316_ok H316_ok I316_ok link316 cenlink316

/-! ### `N = 317` -/

def pL317 : Prm := ⟨65, 31, 31, 319, 11, 18446744073709551616, 418625178750067618, 418625178750067618⟩
def pH317 : Prm := ⟨65, 31, 31, 319, 11, 18446744073709551616, 418642770936112034, 418642770936112034⟩
def pI317 : Prm := ⟨57, 28, 26, 319, 11, 18446744073709551616, 418625178750067618, 418642770936112034⟩
theorem L317_fin : (prmOK pL317 317 && ptTest pL317 (runFrom pL317 (fmask pL317) (cmask pL317) (hmask pL317) 1 316 (true, (init pL317), (init pL317))) 317 159 false) = true := by
  decide +kernel
theorem L317_ok : RunOK pL317 317 (runFrom pL317 (fmask pL317) (cmask pL317) (hmask pL317) 1 316 (true, (init pL317), (init pL317))) ∧ ptTest pL317 (runFrom pL317 (fmask pL317) (cmask pL317) (hmask pL317) 1 316 (true, (init pL317), (init pL317))) 317 159 false = true :=
  fin_run (runOK_init (prmOK_of_and L317_fin) true) (by decide) rfl L317_fin ptTest_fst
theorem H317_fin : (prmOK pH317 317 && ptTest pH317 (runFrom pH317 (fmask pH317) (cmask pH317) (hmask pH317) 1 316 (true, (init pH317), (init pH317))) 317 159 true) = true := by
  decide +kernel
theorem H317_ok : RunOK pH317 317 (runFrom pH317 (fmask pH317) (cmask pH317) (hmask pH317) 1 316 (true, (init pH317), (init pH317))) ∧ ptTest pH317 (runFrom pH317 (fmask pH317) (cmask pH317) (hmask pH317) 1 316 (true, (init pH317), (init pH317))) 317 159 true = true :=
  fin_run (runOK_init (prmOK_of_and H317_fin) true) (by decide) rfl H317_fin ptTest_fst
theorem I317_fin : (prmOK pI317 317 && intTest pI317 (runFrom pI317 (fmask pI317) (cmask pI317) (hmask pI317) 1 316 (true, (init pI317), (init pI317))) 317 12 false) = true := by
  decide +kernel
theorem I317_ok : RunOK pI317 317 (runFrom pI317 (fmask pI317) (cmask pI317) (hmask pI317) 1 316 (true, (init pI317), (init pI317))) ∧ intTest pI317 (runFrom pI317 (fmask pI317) (cmask pI317) (hmask pI317) 1 316 (true, (init pI317), (init pI317))) 317 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I317_fin) true) (by decide) rfl I317_fin intTest_fst
theorem link317 : linkOK pL317 pH317 pI317 = true := by decide +kernel
theorem cvx317 : ConvexBetweenHumps 317 :=
  cvx_of L317_ok H317_ok I317_ok link317 (by decide)

/-! ### `N = 318` -/

def pL318 : Prm := ⟨65, 31, 31, 320, 11, 18446744073709551616, 417651640672846959, 417651640672846959⟩
def pH318 : Prm := ⟨65, 31, 31, 320, 11, 18446744073709551616, 417669232858891375, 417669232858891375⟩
def pI318 : Prm := ⟨58, 28, 27, 320, 11, 18446744073709551616, 417651640672846959, 417669232858891375⟩
theorem L318_fin : (prmOK pL318 318 && ptTest pL318 (runFrom pL318 (fmask pL318) (cmask pL318) (hmask pL318) 1 317 (true, (init pL318), (init pL318))) 318 159 false) = true := by
  decide +kernel
theorem L318_ok : RunOK pL318 318 (runFrom pL318 (fmask pL318) (cmask pL318) (hmask pL318) 1 317 (true, (init pL318), (init pL318))) ∧ ptTest pL318 (runFrom pL318 (fmask pL318) (cmask pL318) (hmask pL318) 1 317 (true, (init pL318), (init pL318))) 318 159 false = true :=
  fin_run (runOK_init (prmOK_of_and L318_fin) true) (by decide) rfl L318_fin ptTest_fst
theorem H318_fin : (prmOK pH318 318 && ptTest pH318 (runFrom pH318 (fmask pH318) (cmask pH318) (hmask pH318) 1 317 (true, (init pH318), (init pH318))) 318 159 true) = true := by
  decide +kernel
theorem H318_ok : RunOK pH318 318 (runFrom pH318 (fmask pH318) (cmask pH318) (hmask pH318) 1 317 (true, (init pH318), (init pH318))) ∧ ptTest pH318 (runFrom pH318 (fmask pH318) (cmask pH318) (hmask pH318) 1 317 (true, (init pH318), (init pH318))) 318 159 true = true :=
  fin_run (runOK_init (prmOK_of_and H318_fin) true) (by decide) rfl H318_fin ptTest_fst
theorem I318_fin : (prmOK pI318 318 && intTest pI318 (runFrom pI318 (fmask pI318) (cmask pI318) (hmask pI318) 1 317 (true, (init pI318), (init pI318))) 318 12 true) = true := by
  decide +kernel
theorem I318_ok : RunOK pI318 318 (runFrom pI318 (fmask pI318) (cmask pI318) (hmask pI318) 1 317 (true, (init pI318), (init pI318))) ∧ intTest pI318 (runFrom pI318 (fmask pI318) (cmask pI318) (hmask pI318) 1 317 (true, (init pI318), (init pI318))) 318 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I318_fin) true) (by decide) rfl I318_fin intTest_fst
theorem link318 : linkOK pL318 pH318 pI318 = true := by decide +kernel
theorem cvx318 : ConvexBetweenHumps 318 :=
  cvx_of L318_ok H318_ok I318_ok link318 (by decide)
theorem cenlink318 : cenLinkOK pI318 318 = true := by decide +kernel
theorem cen318 : CenterUniqueMin 318 ∧ DipHyp 318 ∧ OnePointHyps 318 :=
  cen_of L318_ok H318_ok I318_ok link318 cenlink318

/-! ### `N = 319` -/

def pL319 : Prm := ⟨65, 31, 31, 321, 11, 18446744073709551616, 416679384547936737, 416679384547936737⟩
def pH319 : Prm := ⟨65, 31, 31, 321, 11, 18446744073709551616, 416696976733981153, 416696976733981153⟩
def pI319 : Prm := ⟨58, 28, 27, 321, 11, 18446744073709551616, 416679384547936737, 416696976733981153⟩
theorem L319_fin : (prmOK pL319 319 && ptTest pL319 (runFrom pL319 (fmask pL319) (cmask pL319) (hmask pL319) 1 318 (true, (init pL319), (init pL319))) 319 160 false) = true := by
  decide +kernel
theorem L319_ok : RunOK pL319 319 (runFrom pL319 (fmask pL319) (cmask pL319) (hmask pL319) 1 318 (true, (init pL319), (init pL319))) ∧ ptTest pL319 (runFrom pL319 (fmask pL319) (cmask pL319) (hmask pL319) 1 318 (true, (init pL319), (init pL319))) 319 160 false = true :=
  fin_run (runOK_init (prmOK_of_and L319_fin) true) (by decide) rfl L319_fin ptTest_fst
theorem H319_fin : (prmOK pH319 319 && ptTest pH319 (runFrom pH319 (fmask pH319) (cmask pH319) (hmask pH319) 1 318 (true, (init pH319), (init pH319))) 319 160 true) = true := by
  decide +kernel
theorem H319_ok : RunOK pH319 319 (runFrom pH319 (fmask pH319) (cmask pH319) (hmask pH319) 1 318 (true, (init pH319), (init pH319))) ∧ ptTest pH319 (runFrom pH319 (fmask pH319) (cmask pH319) (hmask pH319) 1 318 (true, (init pH319), (init pH319))) 319 160 true = true :=
  fin_run (runOK_init (prmOK_of_and H319_fin) true) (by decide) rfl H319_fin ptTest_fst
theorem I319_fin : (prmOK pI319 319 && intTest pI319 (runFrom pI319 (fmask pI319) (cmask pI319) (hmask pI319) 1 318 (true, (init pI319), (init pI319))) 319 12 false) = true := by
  decide +kernel
theorem I319_ok : RunOK pI319 319 (runFrom pI319 (fmask pI319) (cmask pI319) (hmask pI319) 1 318 (true, (init pI319), (init pI319))) ∧ intTest pI319 (runFrom pI319 (fmask pI319) (cmask pI319) (hmask pI319) 1 318 (true, (init pI319), (init pI319))) 319 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I319_fin) true) (by decide) rfl I319_fin intTest_fst
theorem link319 : linkOK pL319 pH319 pI319 = true := by decide +kernel
theorem cvx319 : ConvexBetweenHumps 319 :=
  cvx_of L319_ok H319_ok I319_ok link319 (by decide)

/-! ### `N = 320` -/

def pL320 : Prm := ⟨67, 32, 32, 322, 11, 18446744073709551616, 415720314983065642, 415720314983065642⟩
def pH320 : Prm := ⟨68, 33, 32, 322, 11, 18446744073709551616, 415729111076087850, 415729111076087850⟩
def pI320 : Prm := ⟨57, 27, 27, 322, 11, 18446744073709551616, 415720314983065642, 415729111076087850⟩
theorem L320_fin : (prmOK pL320 320 && ptTest pL320 (runFrom pL320 (fmask pL320) (cmask pL320) (hmask pL320) 1 319 (true, (init pL320), (init pL320))) 320 160 false) = true := by
  decide +kernel
theorem L320_ok : RunOK pL320 320 (runFrom pL320 (fmask pL320) (cmask pL320) (hmask pL320) 1 319 (true, (init pL320), (init pL320))) ∧ ptTest pL320 (runFrom pL320 (fmask pL320) (cmask pL320) (hmask pL320) 1 319 (true, (init pL320), (init pL320))) 320 160 false = true :=
  fin_run (runOK_init (prmOK_of_and L320_fin) true) (by decide) rfl L320_fin ptTest_fst
theorem H320_fin : (prmOK pH320 320 && ptTest pH320 (runFrom pH320 (fmask pH320) (cmask pH320) (hmask pH320) 1 319 (true, (init pH320), (init pH320))) 320 160 true) = true := by
  decide +kernel
theorem H320_ok : RunOK pH320 320 (runFrom pH320 (fmask pH320) (cmask pH320) (hmask pH320) 1 319 (true, (init pH320), (init pH320))) ∧ ptTest pH320 (runFrom pH320 (fmask pH320) (cmask pH320) (hmask pH320) 1 319 (true, (init pH320), (init pH320))) 320 160 true = true :=
  fin_run (runOK_init (prmOK_of_and H320_fin) true) (by decide) rfl H320_fin ptTest_fst
theorem I320_fin : (prmOK pI320 320 && intTest pI320 (runFrom pI320 (fmask pI320) (cmask pI320) (hmask pI320) 1 319 (true, (init pI320), (init pI320))) 320 12 true) = true := by
  decide +kernel
theorem I320_ok : RunOK pI320 320 (runFrom pI320 (fmask pI320) (cmask pI320) (hmask pI320) 1 319 (true, (init pI320), (init pI320))) ∧ intTest pI320 (runFrom pI320 (fmask pI320) (cmask pI320) (hmask pI320) 1 319 (true, (init pI320), (init pI320))) 320 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I320_fin) true) (by decide) rfl I320_fin intTest_fst
theorem link320 : linkOK pL320 pH320 pI320 = true := by decide +kernel
theorem cvx320 : ConvexBetweenHumps 320 :=
  cvx_of L320_ok H320_ok I320_ok link320 (by decide)
theorem cenlink320 : cenLinkOK pI320 320 = true := by decide +kernel
theorem cen320 : CenterUniqueMin 320 ∧ DipHyp 320 ∧ OnePointHyps 320 :=
  cen_of L320_ok H320_ok I320_ok link320 cenlink320

/-! ### `N = 321` -/

def pL321 : Prm := ⟨67, 32, 32, 323, 11, 18446744073709551616, 414758118394593165, 414758118394593165⟩
def pH321 : Prm := ⟨67, 32, 32, 323, 11, 18446744073709551616, 414766914487615373, 414766914487615373⟩
def pI321 : Prm := ⟨56, 28, 25, 323, 11, 18446744073709551616, 414758118394593165, 414766914487615373⟩
theorem L321_fin : (prmOK pL321 321 && ptTest pL321 (runFrom pL321 (fmask pL321) (cmask pL321) (hmask pL321) 1 320 (true, (init pL321), (init pL321))) 321 161 false) = true := by
  decide +kernel
theorem L321_ok : RunOK pL321 321 (runFrom pL321 (fmask pL321) (cmask pL321) (hmask pL321) 1 320 (true, (init pL321), (init pL321))) ∧ ptTest pL321 (runFrom pL321 (fmask pL321) (cmask pL321) (hmask pL321) 1 320 (true, (init pL321), (init pL321))) 321 161 false = true :=
  fin_run (runOK_init (prmOK_of_and L321_fin) true) (by decide) rfl L321_fin ptTest_fst
theorem H321_fin : (prmOK pH321 321 && ptTest pH321 (runFrom pH321 (fmask pH321) (cmask pH321) (hmask pH321) 1 320 (true, (init pH321), (init pH321))) 321 161 true) = true := by
  decide +kernel
theorem H321_ok : RunOK pH321 321 (runFrom pH321 (fmask pH321) (cmask pH321) (hmask pH321) 1 320 (true, (init pH321), (init pH321))) ∧ ptTest pH321 (runFrom pH321 (fmask pH321) (cmask pH321) (hmask pH321) 1 320 (true, (init pH321), (init pH321))) 321 161 true = true :=
  fin_run (runOK_init (prmOK_of_and H321_fin) true) (by decide) rfl H321_fin ptTest_fst
theorem I321_fin : (prmOK pI321 321 && intTest pI321 (runFrom pI321 (fmask pI321) (cmask pI321) (hmask pI321) 1 320 (true, (init pI321), (init pI321))) 321 12 false) = true := by
  decide +kernel
theorem I321_ok : RunOK pI321 321 (runFrom pI321 (fmask pI321) (cmask pI321) (hmask pI321) 1 320 (true, (init pI321), (init pI321))) ∧ intTest pI321 (runFrom pI321 (fmask pI321) (cmask pI321) (hmask pI321) 1 320 (true, (init pI321), (init pI321))) 321 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I321_fin) true) (by decide) rfl I321_fin intTest_fst
theorem link321 : linkOK pL321 pH321 pI321 = true := by decide +kernel
theorem cvx321 : ConvexBetweenHumps 321 :=
  cvx_of L321_ok H321_ok I321_ok link321 (by decide)

/-! ### `N = 322` -/

def pL322 : Prm := ⟨67, 32, 32, 324, 11, 18446744073709551616, 413804558854429246, 413804558854429246⟩
def pH322 : Prm := ⟨68, 33, 32, 324, 11, 18446744073709551616, 413813354947451454, 413813354947451454⟩
def pI322 : Prm := ⟨57, 27, 27, 324, 11, 18446744073709551616, 413804558854429246, 413813354947451454⟩
theorem L322_fin : (prmOK pL322 322 && ptTest pL322 (runFrom pL322 (fmask pL322) (cmask pL322) (hmask pL322) 1 321 (true, (init pL322), (init pL322))) 322 161 false) = true := by
  decide +kernel
theorem L322_ok : RunOK pL322 322 (runFrom pL322 (fmask pL322) (cmask pL322) (hmask pL322) 1 321 (true, (init pL322), (init pL322))) ∧ ptTest pL322 (runFrom pL322 (fmask pL322) (cmask pL322) (hmask pL322) 1 321 (true, (init pL322), (init pL322))) 322 161 false = true :=
  fin_run (runOK_init (prmOK_of_and L322_fin) true) (by decide) rfl L322_fin ptTest_fst
theorem H322_fin : (prmOK pH322 322 && ptTest pH322 (runFrom pH322 (fmask pH322) (cmask pH322) (hmask pH322) 1 321 (true, (init pH322), (init pH322))) 322 161 true) = true := by
  decide +kernel
theorem H322_ok : RunOK pH322 322 (runFrom pH322 (fmask pH322) (cmask pH322) (hmask pH322) 1 321 (true, (init pH322), (init pH322))) ∧ ptTest pH322 (runFrom pH322 (fmask pH322) (cmask pH322) (hmask pH322) 1 321 (true, (init pH322), (init pH322))) 322 161 true = true :=
  fin_run (runOK_init (prmOK_of_and H322_fin) true) (by decide) rfl H322_fin ptTest_fst
theorem I322_fin : (prmOK pI322 322 && intTest pI322 (runFrom pI322 (fmask pI322) (cmask pI322) (hmask pI322) 1 321 (true, (init pI322), (init pI322))) 322 12 true) = true := by
  decide +kernel
theorem I322_ok : RunOK pI322 322 (runFrom pI322 (fmask pI322) (cmask pI322) (hmask pI322) 1 321 (true, (init pI322), (init pI322))) ∧ intTest pI322 (runFrom pI322 (fmask pI322) (cmask pI322) (hmask pI322) 1 321 (true, (init pI322), (init pI322))) 322 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I322_fin) true) (by decide) rfl I322_fin intTest_fst
theorem link322 : linkOK pL322 pH322 pI322 = true := by decide +kernel
theorem cvx322 : ConvexBetweenHumps 322 :=
  cvx_of L322_ok H322_ok I322_ok link322 (by decide)
theorem cenlink322 : cenLinkOK pI322 322 = true := by decide +kernel
theorem cen322 : CenterUniqueMin 322 ∧ DipHyp 322 ∧ OnePointHyps 322 :=
  cen_of L322_ok H322_ok I322_ok link322 cenlink322

/-! ### `N = 323` -/

def pL323 : Prm := ⟨67, 32, 32, 325, 11, 18446744073709551616, 412852259458853368, 412852259458853368⟩
def pH323 : Prm := ⟨67, 32, 32, 325, 11, 18446744073709551616, 412861055551875576, 412861055551875576⟩
def pI323 : Prm := ⟨57, 28, 26, 325, 11, 18446744073709551616, 412852259458853368, 412861055551875576⟩
theorem L323_fin : (prmOK pL323 323 && ptTest pL323 (runFrom pL323 (fmask pL323) (cmask pL323) (hmask pL323) 1 322 (true, (init pL323), (init pL323))) 323 162 false) = true := by
  decide +kernel
theorem L323_ok : RunOK pL323 323 (runFrom pL323 (fmask pL323) (cmask pL323) (hmask pL323) 1 322 (true, (init pL323), (init pL323))) ∧ ptTest pL323 (runFrom pL323 (fmask pL323) (cmask pL323) (hmask pL323) 1 322 (true, (init pL323), (init pL323))) 323 162 false = true :=
  fin_run (runOK_init (prmOK_of_and L323_fin) true) (by decide) rfl L323_fin ptTest_fst
theorem H323_fin : (prmOK pH323 323 && ptTest pH323 (runFrom pH323 (fmask pH323) (cmask pH323) (hmask pH323) 1 322 (true, (init pH323), (init pH323))) 323 162 true) = true := by
  decide +kernel
theorem H323_ok : RunOK pH323 323 (runFrom pH323 (fmask pH323) (cmask pH323) (hmask pH323) 1 322 (true, (init pH323), (init pH323))) ∧ ptTest pH323 (runFrom pH323 (fmask pH323) (cmask pH323) (hmask pH323) 1 322 (true, (init pH323), (init pH323))) 323 162 true = true :=
  fin_run (runOK_init (prmOK_of_and H323_fin) true) (by decide) rfl H323_fin ptTest_fst
theorem I323_fin : (prmOK pI323 323 && intTest pI323 (runFrom pI323 (fmask pI323) (cmask pI323) (hmask pI323) 1 322 (true, (init pI323), (init pI323))) 323 12 false) = true := by
  decide +kernel
theorem I323_ok : RunOK pI323 323 (runFrom pI323 (fmask pI323) (cmask pI323) (hmask pI323) 1 322 (true, (init pI323), (init pI323))) ∧ intTest pI323 (runFrom pI323 (fmask pI323) (cmask pI323) (hmask pI323) 1 322 (true, (init pI323), (init pI323))) 323 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I323_fin) true) (by decide) rfl I323_fin intTest_fst
theorem link323 : linkOK pL323 pH323 pI323 = true := by decide +kernel
theorem cvx323 : ConvexBetweenHumps 323 :=
  cvx_of L323_ok H323_ok I323_ok link323 (by decide)

/-! ### `N = 324` -/

def pL324 : Prm := ⟨67, 32, 32, 326, 11, 18446744073709551616, 411908449154107201, 411908449154107201⟩
def pH324 : Prm := ⟨67, 32, 32, 326, 11, 18446744073709551616, 411917245247129409, 411917245247129409⟩
def pI324 : Prm := ⟨57, 27, 27, 326, 11, 18446744073709551616, 411908449154107201, 411917245247129409⟩
theorem L324_fin : (prmOK pL324 324 && ptTest pL324 (runFrom pL324 (fmask pL324) (cmask pL324) (hmask pL324) 1 323 (true, (init pL324), (init pL324))) 324 162 false) = true := by
  decide +kernel
theorem L324_ok : RunOK pL324 324 (runFrom pL324 (fmask pL324) (cmask pL324) (hmask pL324) 1 323 (true, (init pL324), (init pL324))) ∧ ptTest pL324 (runFrom pL324 (fmask pL324) (cmask pL324) (hmask pL324) 1 323 (true, (init pL324), (init pL324))) 324 162 false = true :=
  fin_run (runOK_init (prmOK_of_and L324_fin) true) (by decide) rfl L324_fin ptTest_fst
theorem H324_fin : (prmOK pH324 324 && ptTest pH324 (runFrom pH324 (fmask pH324) (cmask pH324) (hmask pH324) 1 323 (true, (init pH324), (init pH324))) 324 162 true) = true := by
  decide +kernel
theorem H324_ok : RunOK pH324 324 (runFrom pH324 (fmask pH324) (cmask pH324) (hmask pH324) 1 323 (true, (init pH324), (init pH324))) ∧ ptTest pH324 (runFrom pH324 (fmask pH324) (cmask pH324) (hmask pH324) 1 323 (true, (init pH324), (init pH324))) 324 162 true = true :=
  fin_run (runOK_init (prmOK_of_and H324_fin) true) (by decide) rfl H324_fin ptTest_fst
theorem I324_fin : (prmOK pI324 324 && intTest pI324 (runFrom pI324 (fmask pI324) (cmask pI324) (hmask pI324) 1 323 (true, (init pI324), (init pI324))) 324 12 true) = true := by
  decide +kernel
theorem I324_ok : RunOK pI324 324 (runFrom pI324 (fmask pI324) (cmask pI324) (hmask pI324) 1 323 (true, (init pI324), (init pI324))) ∧ intTest pI324 (runFrom pI324 (fmask pI324) (cmask pI324) (hmask pI324) 1 323 (true, (init pI324), (init pI324))) 324 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I324_fin) true) (by decide) rfl I324_fin intTest_fst
theorem link324 : linkOK pL324 pH324 pI324 = true := by decide +kernel
theorem cvx324 : ConvexBetweenHumps 324 :=
  cvx_of L324_ok H324_ok I324_ok link324 (by decide)
theorem cenlink324 : cenLinkOK pI324 324 = true := by decide +kernel
theorem cen324 : CenterUniqueMin 324 ∧ DipHyp 324 ∧ OnePointHyps 324 :=
  cen_of L324_ok H324_ok I324_ok link324 cenlink324

/-! ### `N = 325` -/

def pL325 : Prm := ⟨68, 33, 32, 327, 11, 18446744073709551616, 410965888169971502, 410965888169971502⟩
def pH325 : Prm := ⟨68, 33, 32, 327, 11, 18446744073709551616, 410974684262993710, 410974684262993710⟩
def pI325 : Prm := ⟨57, 28, 26, 327, 11, 18446744073709551616, 410965888169971502, 410974684262993710⟩
theorem L325_fin : (prmOK pL325 325 && ptTest pL325 (runFrom pL325 (fmask pL325) (cmask pL325) (hmask pL325) 1 324 (true, (init pL325), (init pL325))) 325 163 false) = true := by
  decide +kernel
theorem L325_ok : RunOK pL325 325 (runFrom pL325 (fmask pL325) (cmask pL325) (hmask pL325) 1 324 (true, (init pL325), (init pL325))) ∧ ptTest pL325 (runFrom pL325 (fmask pL325) (cmask pL325) (hmask pL325) 1 324 (true, (init pL325), (init pL325))) 325 163 false = true :=
  fin_run (runOK_init (prmOK_of_and L325_fin) true) (by decide) rfl L325_fin ptTest_fst
theorem H325_fin : (prmOK pH325 325 && ptTest pH325 (runFrom pH325 (fmask pH325) (cmask pH325) (hmask pH325) 1 324 (true, (init pH325), (init pH325))) 325 163 true) = true := by
  decide +kernel
theorem H325_ok : RunOK pH325 325 (runFrom pH325 (fmask pH325) (cmask pH325) (hmask pH325) 1 324 (true, (init pH325), (init pH325))) ∧ ptTest pH325 (runFrom pH325 (fmask pH325) (cmask pH325) (hmask pH325) 1 324 (true, (init pH325), (init pH325))) 325 163 true = true :=
  fin_run (runOK_init (prmOK_of_and H325_fin) true) (by decide) rfl H325_fin ptTest_fst
theorem I325_fin : (prmOK pI325 325 && intTest pI325 (runFrom pI325 (fmask pI325) (cmask pI325) (hmask pI325) 1 324 (true, (init pI325), (init pI325))) 325 12 false) = true := by
  decide +kernel
theorem I325_ok : RunOK pI325 325 (runFrom pI325 (fmask pI325) (cmask pI325) (hmask pI325) 1 324 (true, (init pI325), (init pI325))) ∧ intTest pI325 (runFrom pI325 (fmask pI325) (cmask pI325) (hmask pI325) 1 324 (true, (init pI325), (init pI325))) 325 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I325_fin) true) (by decide) rfl I325_fin intTest_fst
theorem link325 : linkOK pL325 pH325 pI325 = true := by decide +kernel
theorem cvx325 : ConvexBetweenHumps 325 :=
  cvx_of L325_ok H325_ok I325_ok link325 (by decide)

/-! ### `N = 326` -/

def pL326 : Prm := ⟨67, 32, 32, 328, 11, 18446744073709551616, 410031671725156601, 410031671725156601⟩
def pH326 : Prm := ⟨68, 33, 32, 328, 11, 18446744073709551616, 410040467818178809, 410040467818178809⟩
def pI326 : Prm := ⟨57, 28, 26, 328, 11, 18446744073709551616, 410031671725156601, 410040467818178809⟩
theorem L326_fin : (prmOK pL326 326 && ptTest pL326 (runFrom pL326 (fmask pL326) (cmask pL326) (hmask pL326) 1 325 (true, (init pL326), (init pL326))) 326 163 false) = true := by
  decide +kernel
theorem L326_ok : RunOK pL326 326 (runFrom pL326 (fmask pL326) (cmask pL326) (hmask pL326) 1 325 (true, (init pL326), (init pL326))) ∧ ptTest pL326 (runFrom pL326 (fmask pL326) (cmask pL326) (hmask pL326) 1 325 (true, (init pL326), (init pL326))) 326 163 false = true :=
  fin_run (runOK_init (prmOK_of_and L326_fin) true) (by decide) rfl L326_fin ptTest_fst
theorem H326_fin : (prmOK pH326 326 && ptTest pH326 (runFrom pH326 (fmask pH326) (cmask pH326) (hmask pH326) 1 325 (true, (init pH326), (init pH326))) 326 163 true) = true := by
  decide +kernel
theorem H326_ok : RunOK pH326 326 (runFrom pH326 (fmask pH326) (cmask pH326) (hmask pH326) 1 325 (true, (init pH326), (init pH326))) ∧ ptTest pH326 (runFrom pH326 (fmask pH326) (cmask pH326) (hmask pH326) 1 325 (true, (init pH326), (init pH326))) 326 163 true = true :=
  fin_run (runOK_init (prmOK_of_and H326_fin) true) (by decide) rfl H326_fin ptTest_fst
theorem I326_fin : (prmOK pI326 326 && intTest pI326 (runFrom pI326 (fmask pI326) (cmask pI326) (hmask pI326) 1 325 (true, (init pI326), (init pI326))) 326 12 true) = true := by
  decide +kernel
theorem I326_ok : RunOK pI326 326 (runFrom pI326 (fmask pI326) (cmask pI326) (hmask pI326) 1 325 (true, (init pI326), (init pI326))) ∧ intTest pI326 (runFrom pI326 (fmask pI326) (cmask pI326) (hmask pI326) 1 325 (true, (init pI326), (init pI326))) 326 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I326_fin) true) (by decide) rfl I326_fin intTest_fst
theorem link326 : linkOK pL326 pH326 pI326 = true := by decide +kernel
theorem cvx326 : ConvexBetweenHumps 326 :=
  cvx_of L326_ok H326_ok I326_ok link326 (by decide)
theorem cenlink326 : cenLinkOK pI326 326 = true := by decide +kernel
theorem cen326 : CenterUniqueMin 326 ∧ DipHyp 326 ∧ OnePointHyps 326 :=
  cen_of L326_ok H326_ok I326_ok link326 cenlink326

/-! ### `N = 327` -/

def pL327 : Prm := ⟨68, 33, 32, 329, 11, 18446744073709551616, 409098693834270181, 409098693834270181⟩
def pH327 : Prm := ⟨67, 32, 32, 329, 11, 18446744073709551616, 409107489927292389, 409107489927292389⟩
def pI327 : Prm := ⟨57, 28, 26, 329, 11, 18446744073709551616, 409098693834270181, 409107489927292389⟩
theorem L327_fin : (prmOK pL327 327 && ptTest pL327 (runFrom pL327 (fmask pL327) (cmask pL327) (hmask pL327) 1 326 (true, (init pL327), (init pL327))) 327 164 false) = true := by
  decide +kernel
theorem L327_ok : RunOK pL327 327 (runFrom pL327 (fmask pL327) (cmask pL327) (hmask pL327) 1 326 (true, (init pL327), (init pL327))) ∧ ptTest pL327 (runFrom pL327 (fmask pL327) (cmask pL327) (hmask pL327) 1 326 (true, (init pL327), (init pL327))) 327 164 false = true :=
  fin_run (runOK_init (prmOK_of_and L327_fin) true) (by decide) rfl L327_fin ptTest_fst
theorem H327_fin : (prmOK pH327 327 && ptTest pH327 (runFrom pH327 (fmask pH327) (cmask pH327) (hmask pH327) 1 326 (true, (init pH327), (init pH327))) 327 164 true) = true := by
  decide +kernel
theorem H327_ok : RunOK pH327 327 (runFrom pH327 (fmask pH327) (cmask pH327) (hmask pH327) 1 326 (true, (init pH327), (init pH327))) ∧ ptTest pH327 (runFrom pH327 (fmask pH327) (cmask pH327) (hmask pH327) 1 326 (true, (init pH327), (init pH327))) 327 164 true = true :=
  fin_run (runOK_init (prmOK_of_and H327_fin) true) (by decide) rfl H327_fin ptTest_fst
theorem I327_fin : (prmOK pI327 327 && intTest pI327 (runFrom pI327 (fmask pI327) (cmask pI327) (hmask pI327) 1 326 (true, (init pI327), (init pI327))) 327 12 false) = true := by
  decide +kernel
theorem I327_ok : RunOK pI327 327 (runFrom pI327 (fmask pI327) (cmask pI327) (hmask pI327) 1 326 (true, (init pI327), (init pI327))) ∧ intTest pI327 (runFrom pI327 (fmask pI327) (cmask pI327) (hmask pI327) 1 326 (true, (init pI327), (init pI327))) 327 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I327_fin) true) (by decide) rfl I327_fin intTest_fst
theorem link327 : linkOK pL327 pH327 pI327 = true := by decide +kernel
theorem cvx327 : ConvexBetweenHumps 327 :=
  cvx_of L327_ok H327_ok I327_ok link327 (by decide)

/-! ### `N = 328` -/

def pL328 : Prm := ⟨68, 33, 32, 330, 11, 18446744073709551616, 408173919238992007, 408173919238992007⟩
def pH328 : Prm := ⟨68, 33, 32, 330, 11, 18446744073709551616, 408182715332014215, 408182715332014215⟩
def pI328 : Prm := ⟨57, 28, 26, 330, 11, 18446744073709551616, 408173919238992007, 408182715332014215⟩
theorem L328_fin : (prmOK pL328 328 && ptTest pL328 (runFrom pL328 (fmask pL328) (cmask pL328) (hmask pL328) 1 327 (true, (init pL328), (init pL328))) 328 164 false) = true := by
  decide +kernel
theorem L328_ok : RunOK pL328 328 (runFrom pL328 (fmask pL328) (cmask pL328) (hmask pL328) 1 327 (true, (init pL328), (init pL328))) ∧ ptTest pL328 (runFrom pL328 (fmask pL328) (cmask pL328) (hmask pL328) 1 327 (true, (init pL328), (init pL328))) 328 164 false = true :=
  fin_run (runOK_init (prmOK_of_and L328_fin) true) (by decide) rfl L328_fin ptTest_fst
theorem H328_fin : (prmOK pH328 328 && ptTest pH328 (runFrom pH328 (fmask pH328) (cmask pH328) (hmask pH328) 1 327 (true, (init pH328), (init pH328))) 328 164 true) = true := by
  decide +kernel
theorem H328_ok : RunOK pH328 328 (runFrom pH328 (fmask pH328) (cmask pH328) (hmask pH328) 1 327 (true, (init pH328), (init pH328))) ∧ ptTest pH328 (runFrom pH328 (fmask pH328) (cmask pH328) (hmask pH328) 1 327 (true, (init pH328), (init pH328))) 328 164 true = true :=
  fin_run (runOK_init (prmOK_of_and H328_fin) true) (by decide) rfl H328_fin ptTest_fst
theorem I328_fin : (prmOK pI328 328 && intTest pI328 (runFrom pI328 (fmask pI328) (cmask pI328) (hmask pI328) 1 327 (true, (init pI328), (init pI328))) 328 12 true) = true := by
  decide +kernel
theorem I328_ok : RunOK pI328 328 (runFrom pI328 (fmask pI328) (cmask pI328) (hmask pI328) 1 327 (true, (init pI328), (init pI328))) ∧ intTest pI328 (runFrom pI328 (fmask pI328) (cmask pI328) (hmask pI328) 1 327 (true, (init pI328), (init pI328))) 328 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I328_fin) true) (by decide) rfl I328_fin intTest_fst
theorem link328 : linkOK pL328 pH328 pI328 = true := by decide +kernel
theorem cvx328 : ConvexBetweenHumps 328 :=
  cvx_of L328_ok H328_ok I328_ok link328 (by decide)
theorem cenlink328 : cenLinkOK pI328 328 = true := by decide +kernel
theorem cen328 : CenterUniqueMin 328 ∧ DipHyp 328 ∧ OnePointHyps 328 :=
  cen_of L328_ok H328_ok I328_ok link328 cenlink328

/-! ### `N = 329` -/

def pL329 : Prm := ⟨68, 33, 32, 331, 11, 18446744073709551616, 407250372491004479, 407250372491004479⟩
def pH329 : Prm := ⟨68, 33, 32, 331, 11, 18446744073709551616, 407259168584026687, 407259168584026687⟩
def pI329 : Prm := ⟨57, 28, 26, 331, 11, 18446744073709551616, 407250372491004479, 407259168584026687⟩
theorem L329_fin : (prmOK pL329 329 && ptTest pL329 (runFrom pL329 (fmask pL329) (cmask pL329) (hmask pL329) 1 328 (true, (init pL329), (init pL329))) 329 165 false) = true := by
  decide +kernel
theorem L329_ok : RunOK pL329 329 (runFrom pL329 (fmask pL329) (cmask pL329) (hmask pL329) 1 328 (true, (init pL329), (init pL329))) ∧ ptTest pL329 (runFrom pL329 (fmask pL329) (cmask pL329) (hmask pL329) 1 328 (true, (init pL329), (init pL329))) 329 165 false = true :=
  fin_run (runOK_init (prmOK_of_and L329_fin) true) (by decide) rfl L329_fin ptTest_fst
theorem H329_fin : (prmOK pH329 329 && ptTest pH329 (runFrom pH329 (fmask pH329) (cmask pH329) (hmask pH329) 1 328 (true, (init pH329), (init pH329))) 329 165 true) = true := by
  decide +kernel
theorem H329_ok : RunOK pH329 329 (runFrom pH329 (fmask pH329) (cmask pH329) (hmask pH329) 1 328 (true, (init pH329), (init pH329))) ∧ ptTest pH329 (runFrom pH329 (fmask pH329) (cmask pH329) (hmask pH329) 1 328 (true, (init pH329), (init pH329))) 329 165 true = true :=
  fin_run (runOK_init (prmOK_of_and H329_fin) true) (by decide) rfl H329_fin ptTest_fst
theorem I329_fin : (prmOK pI329 329 && intTest pI329 (runFrom pI329 (fmask pI329) (cmask pI329) (hmask pI329) 1 328 (true, (init pI329), (init pI329))) 329 12 false) = true := by
  decide +kernel
theorem I329_ok : RunOK pI329 329 (runFrom pI329 (fmask pI329) (cmask pI329) (hmask pI329) 1 328 (true, (init pI329), (init pI329))) ∧ intTest pI329 (runFrom pI329 (fmask pI329) (cmask pI329) (hmask pI329) 1 328 (true, (init pI329), (init pI329))) 329 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I329_fin) true) (by decide) rfl I329_fin intTest_fst
theorem link329 : linkOK pL329 pH329 pI329 = true := by decide +kernel
theorem cvx329 : ConvexBetweenHumps 329 :=
  cvx_of L329_ok H329_ok I329_ok link329 (by decide)

/-! ### `N = 330` -/

def pL330 : Prm := ⟨68, 33, 32, 332, 11, 18446744073709551616, 406334891007855846, 406334891007855846⟩
def pH330 : Prm := ⟨68, 33, 32, 332, 11, 18446744073709551616, 406343687100878054, 406343687100878054⟩
def pI330 : Prm := ⟨57, 28, 26, 332, 11, 18446744073709551616, 406334891007855846, 406343687100878054⟩
theorem L330_fin : (prmOK pL330 330 && ptTest pL330 (runFrom pL330 (fmask pL330) (cmask pL330) (hmask pL330) 1 329 (true, (init pL330), (init pL330))) 330 165 false) = true := by
  decide +kernel
theorem L330_ok : RunOK pL330 330 (runFrom pL330 (fmask pL330) (cmask pL330) (hmask pL330) 1 329 (true, (init pL330), (init pL330))) ∧ ptTest pL330 (runFrom pL330 (fmask pL330) (cmask pL330) (hmask pL330) 1 329 (true, (init pL330), (init pL330))) 330 165 false = true :=
  fin_run (runOK_init (prmOK_of_and L330_fin) true) (by decide) rfl L330_fin ptTest_fst
theorem H330_fin : (prmOK pH330 330 && ptTest pH330 (runFrom pH330 (fmask pH330) (cmask pH330) (hmask pH330) 1 329 (true, (init pH330), (init pH330))) 330 165 true) = true := by
  decide +kernel
theorem H330_ok : RunOK pH330 330 (runFrom pH330 (fmask pH330) (cmask pH330) (hmask pH330) 1 329 (true, (init pH330), (init pH330))) ∧ ptTest pH330 (runFrom pH330 (fmask pH330) (cmask pH330) (hmask pH330) 1 329 (true, (init pH330), (init pH330))) 330 165 true = true :=
  fin_run (runOK_init (prmOK_of_and H330_fin) true) (by decide) rfl H330_fin ptTest_fst
theorem I330_fin : (prmOK pI330 330 && intTest pI330 (runFrom pI330 (fmask pI330) (cmask pI330) (hmask pI330) 1 329 (true, (init pI330), (init pI330))) 330 12 true) = true := by
  decide +kernel
theorem I330_ok : RunOK pI330 330 (runFrom pI330 (fmask pI330) (cmask pI330) (hmask pI330) 1 329 (true, (init pI330), (init pI330))) ∧ intTest pI330 (runFrom pI330 (fmask pI330) (cmask pI330) (hmask pI330) 1 329 (true, (init pI330), (init pI330))) 330 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I330_fin) true) (by decide) rfl I330_fin intTest_fst
theorem link330 : linkOK pL330 pH330 pI330 = true := by decide +kernel
theorem cvx330 : ConvexBetweenHumps 330 :=
  cvx_of L330_ok H330_ok I330_ok link330 (by decide)
theorem cenlink330 : cenLinkOK pI330 330 = true := by decide +kernel
theorem cen330 : CenterUniqueMin 330 ∧ DipHyp 330 ∧ OnePointHyps 330 :=
  cen_of L330_ok H330_ok I330_ok link330 cenlink330

/-! ### `N = 331` -/

def pL331 : Prm := ⟨68, 33, 32, 333, 11, 18446744073709551616, 405420626727912934, 405420626727912934⟩
def pH331 : Prm := ⟨68, 33, 32, 333, 11, 18446744073709551616, 405429422820935142, 405429422820935142⟩
def pI331 : Prm := ⟨57, 28, 26, 333, 11, 18446744073709551616, 405420626727912934, 405429422820935142⟩
theorem L331_fin : (prmOK pL331 331 && ptTest pL331 (runFrom pL331 (fmask pL331) (cmask pL331) (hmask pL331) 1 330 (true, (init pL331), (init pL331))) 331 166 false) = true := by
  decide +kernel
theorem L331_ok : RunOK pL331 331 (runFrom pL331 (fmask pL331) (cmask pL331) (hmask pL331) 1 330 (true, (init pL331), (init pL331))) ∧ ptTest pL331 (runFrom pL331 (fmask pL331) (cmask pL331) (hmask pL331) 1 330 (true, (init pL331), (init pL331))) 331 166 false = true :=
  fin_run (runOK_init (prmOK_of_and L331_fin) true) (by decide) rfl L331_fin ptTest_fst
theorem H331_fin : (prmOK pH331 331 && ptTest pH331 (runFrom pH331 (fmask pH331) (cmask pH331) (hmask pH331) 1 330 (true, (init pH331), (init pH331))) 331 166 true) = true := by
  decide +kernel
theorem H331_ok : RunOK pH331 331 (runFrom pH331 (fmask pH331) (cmask pH331) (hmask pH331) 1 330 (true, (init pH331), (init pH331))) ∧ ptTest pH331 (runFrom pH331 (fmask pH331) (cmask pH331) (hmask pH331) 1 330 (true, (init pH331), (init pH331))) 331 166 true = true :=
  fin_run (runOK_init (prmOK_of_and H331_fin) true) (by decide) rfl H331_fin ptTest_fst
theorem I331_fin : (prmOK pI331 331 && intTest pI331 (runFrom pI331 (fmask pI331) (cmask pI331) (hmask pI331) 1 330 (true, (init pI331), (init pI331))) 331 12 false) = true := by
  decide +kernel
theorem I331_ok : RunOK pI331 331 (runFrom pI331 (fmask pI331) (cmask pI331) (hmask pI331) 1 330 (true, (init pI331), (init pI331))) ∧ intTest pI331 (runFrom pI331 (fmask pI331) (cmask pI331) (hmask pI331) 1 330 (true, (init pI331), (init pI331))) 331 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I331_fin) true) (by decide) rfl I331_fin intTest_fst
theorem link331 : linkOK pL331 pH331 pI331 = true := by decide +kernel
theorem cvx331 : ConvexBetweenHumps 331 :=
  cvx_of L331_ok H331_ok I331_ok link331 (by decide)

/-! ### `N = 332` -/

def pL332 : Prm := ⟨68, 33, 32, 334, 11, 18446744073709551616, 404514292803486918, 404514292803486918⟩
def pH332 : Prm := ⟨68, 33, 32, 334, 11, 18446744073709551616, 404523088896509126, 404523088896509126⟩
def pI332 : Prm := ⟨57, 28, 26, 334, 11, 18446744073709551616, 404514292803486918, 404523088896509126⟩
theorem L332_fin : (prmOK pL332 332 && ptTest pL332 (runFrom pL332 (fmask pL332) (cmask pL332) (hmask pL332) 1 331 (true, (init pL332), (init pL332))) 332 166 false) = true := by
  decide +kernel
theorem L332_ok : RunOK pL332 332 (runFrom pL332 (fmask pL332) (cmask pL332) (hmask pL332) 1 331 (true, (init pL332), (init pL332))) ∧ ptTest pL332 (runFrom pL332 (fmask pL332) (cmask pL332) (hmask pL332) 1 331 (true, (init pL332), (init pL332))) 332 166 false = true :=
  fin_run (runOK_init (prmOK_of_and L332_fin) true) (by decide) rfl L332_fin ptTest_fst
theorem H332_fin : (prmOK pH332 332 && ptTest pH332 (runFrom pH332 (fmask pH332) (cmask pH332) (hmask pH332) 1 331 (true, (init pH332), (init pH332))) 332 166 true) = true := by
  decide +kernel
theorem H332_ok : RunOK pH332 332 (runFrom pH332 (fmask pH332) (cmask pH332) (hmask pH332) 1 331 (true, (init pH332), (init pH332))) ∧ ptTest pH332 (runFrom pH332 (fmask pH332) (cmask pH332) (hmask pH332) 1 331 (true, (init pH332), (init pH332))) 332 166 true = true :=
  fin_run (runOK_init (prmOK_of_and H332_fin) true) (by decide) rfl H332_fin ptTest_fst
theorem I332_fin : (prmOK pI332 332 && intTest pI332 (runFrom pI332 (fmask pI332) (cmask pI332) (hmask pI332) 1 331 (true, (init pI332), (init pI332))) 332 12 true) = true := by
  decide +kernel
theorem I332_ok : RunOK pI332 332 (runFrom pI332 (fmask pI332) (cmask pI332) (hmask pI332) 1 331 (true, (init pI332), (init pI332))) ∧ intTest pI332 (runFrom pI332 (fmask pI332) (cmask pI332) (hmask pI332) 1 331 (true, (init pI332), (init pI332))) 332 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I332_fin) true) (by decide) rfl I332_fin intTest_fst
theorem link332 : linkOK pL332 pH332 pI332 = true := by decide +kernel
theorem cvx332 : ConvexBetweenHumps 332 :=
  cvx_of L332_ok H332_ok I332_ok link332 (by decide)
theorem cenlink332 : cenLinkOK pI332 332 = true := by decide +kernel
theorem cen332 : CenterUniqueMin 332 ∧ DipHyp 332 ∧ OnePointHyps 332 :=
  cen_of L332_ok H332_ok I332_ok link332 cenlink332

/-! ### `N = 333` -/

def pL333 : Prm := ⟨68, 33, 32, 335, 11, 18446744073709551616, 403609165503077344, 403609165503077344⟩
def pH333 : Prm := ⟨68, 33, 32, 335, 11, 18446744073709551616, 403617961596099552, 403617961596099552⟩
def pI333 : Prm := ⟨57, 28, 26, 335, 11, 18446744073709551616, 403609165503077344, 403617961596099552⟩
theorem L333_fin : (prmOK pL333 333 && ptTest pL333 (runFrom pL333 (fmask pL333) (cmask pL333) (hmask pL333) 1 332 (true, (init pL333), (init pL333))) 333 167 false) = true := by
  decide +kernel
theorem L333_ok : RunOK pL333 333 (runFrom pL333 (fmask pL333) (cmask pL333) (hmask pL333) 1 332 (true, (init pL333), (init pL333))) ∧ ptTest pL333 (runFrom pL333 (fmask pL333) (cmask pL333) (hmask pL333) 1 332 (true, (init pL333), (init pL333))) 333 167 false = true :=
  fin_run (runOK_init (prmOK_of_and L333_fin) true) (by decide) rfl L333_fin ptTest_fst
theorem H333_fin : (prmOK pH333 333 && ptTest pH333 (runFrom pH333 (fmask pH333) (cmask pH333) (hmask pH333) 1 332 (true, (init pH333), (init pH333))) 333 167 true) = true := by
  decide +kernel
theorem H333_ok : RunOK pH333 333 (runFrom pH333 (fmask pH333) (cmask pH333) (hmask pH333) 1 332 (true, (init pH333), (init pH333))) ∧ ptTest pH333 (runFrom pH333 (fmask pH333) (cmask pH333) (hmask pH333) 1 332 (true, (init pH333), (init pH333))) 333 167 true = true :=
  fin_run (runOK_init (prmOK_of_and H333_fin) true) (by decide) rfl H333_fin ptTest_fst
theorem I333_fin : (prmOK pI333 333 && intTest pI333 (runFrom pI333 (fmask pI333) (cmask pI333) (hmask pI333) 1 332 (true, (init pI333), (init pI333))) 333 12 false) = true := by
  decide +kernel
theorem I333_ok : RunOK pI333 333 (runFrom pI333 (fmask pI333) (cmask pI333) (hmask pI333) 1 332 (true, (init pI333), (init pI333))) ∧ intTest pI333 (runFrom pI333 (fmask pI333) (cmask pI333) (hmask pI333) 1 332 (true, (init pI333), (init pI333))) 333 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I333_fin) true) (by decide) rfl I333_fin intTest_fst
theorem link333 : linkOK pL333 pH333 pI333 = true := by decide +kernel
theorem cvx333 : ConvexBetweenHumps 333 :=
  cvx_of L333_ok H333_ok I333_ok link333 (by decide)

/-! ### `N = 334` -/

def pL334 : Prm := ⟨68, 33, 32, 336, 11, 18446744073709551616, 402711836681839433, 402711836681839433⟩
def pH334 : Prm := ⟨68, 33, 32, 336, 11, 18446744073709551616, 402720632774861641, 402720632774861641⟩
def pI334 : Prm := ⟨57, 28, 26, 336, 11, 18446744073709551616, 402711836681839433, 402720632774861641⟩
theorem L334_fin : (prmOK pL334 334 && ptTest pL334 (runFrom pL334 (fmask pL334) (cmask pL334) (hmask pL334) 1 333 (true, (init pL334), (init pL334))) 334 167 false) = true := by
  decide +kernel
theorem L334_ok : RunOK pL334 334 (runFrom pL334 (fmask pL334) (cmask pL334) (hmask pL334) 1 333 (true, (init pL334), (init pL334))) ∧ ptTest pL334 (runFrom pL334 (fmask pL334) (cmask pL334) (hmask pL334) 1 333 (true, (init pL334), (init pL334))) 334 167 false = true :=
  fin_run (runOK_init (prmOK_of_and L334_fin) true) (by decide) rfl L334_fin ptTest_fst
theorem H334_fin : (prmOK pH334 334 && ptTest pH334 (runFrom pH334 (fmask pH334) (cmask pH334) (hmask pH334) 1 333 (true, (init pH334), (init pH334))) 334 167 true) = true := by
  decide +kernel
theorem H334_ok : RunOK pH334 334 (runFrom pH334 (fmask pH334) (cmask pH334) (hmask pH334) 1 333 (true, (init pH334), (init pH334))) ∧ ptTest pH334 (runFrom pH334 (fmask pH334) (cmask pH334) (hmask pH334) 1 333 (true, (init pH334), (init pH334))) 334 167 true = true :=
  fin_run (runOK_init (prmOK_of_and H334_fin) true) (by decide) rfl H334_fin ptTest_fst
theorem I334_fin : (prmOK pI334 334 && intTest pI334 (runFrom pI334 (fmask pI334) (cmask pI334) (hmask pI334) 1 333 (true, (init pI334), (init pI334))) 334 12 true) = true := by
  decide +kernel
theorem I334_ok : RunOK pI334 334 (runFrom pI334 (fmask pI334) (cmask pI334) (hmask pI334) 1 333 (true, (init pI334), (init pI334))) ∧ intTest pI334 (runFrom pI334 (fmask pI334) (cmask pI334) (hmask pI334) 1 333 (true, (init pI334), (init pI334))) 334 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I334_fin) true) (by decide) rfl I334_fin intTest_fst
theorem link334 : linkOK pL334 pH334 pI334 = true := by decide +kernel
theorem cvx334 : ConvexBetweenHumps 334 :=
  cvx_of L334_ok H334_ok I334_ok link334 (by decide)
theorem cenlink334 : cenLinkOK pI334 334 = true := by decide +kernel
theorem cen334 : CenterUniqueMin 334 ∧ DipHyp 334 ∧ OnePointHyps 334 :=
  cen_of L334_ok H334_ok I334_ok link334 cenlink334

/-! ### `N = 335` -/

def pL335 : Prm := ⟨68, 33, 32, 337, 11, 18446744073709551616, 401815703972501046, 401815703972501046⟩
def pH335 : Prm := ⟨68, 33, 32, 337, 11, 18446744073709551616, 401824500065523254, 401824500065523254⟩
def pI335 : Prm := ⟨57, 28, 26, 337, 11, 18446744073709551616, 401815703972501046, 401824500065523254⟩
theorem L335_fin : (prmOK pL335 335 && ptTest pL335 (runFrom pL335 (fmask pL335) (cmask pL335) (hmask pL335) 1 334 (true, (init pL335), (init pL335))) 335 168 false) = true := by
  decide +kernel
theorem L335_ok : RunOK pL335 335 (runFrom pL335 (fmask pL335) (cmask pL335) (hmask pL335) 1 334 (true, (init pL335), (init pL335))) ∧ ptTest pL335 (runFrom pL335 (fmask pL335) (cmask pL335) (hmask pL335) 1 334 (true, (init pL335), (init pL335))) 335 168 false = true :=
  fin_run (runOK_init (prmOK_of_and L335_fin) true) (by decide) rfl L335_fin ptTest_fst
theorem H335_fin : (prmOK pH335 335 && ptTest pH335 (runFrom pH335 (fmask pH335) (cmask pH335) (hmask pH335) 1 334 (true, (init pH335), (init pH335))) 335 168 true) = true := by
  decide +kernel
theorem H335_ok : RunOK pH335 335 (runFrom pH335 (fmask pH335) (cmask pH335) (hmask pH335) 1 334 (true, (init pH335), (init pH335))) ∧ ptTest pH335 (runFrom pH335 (fmask pH335) (cmask pH335) (hmask pH335) 1 334 (true, (init pH335), (init pH335))) 335 168 true = true :=
  fin_run (runOK_init (prmOK_of_and H335_fin) true) (by decide) rfl H335_fin ptTest_fst
theorem I335_fin : (prmOK pI335 335 && intTest pI335 (runFrom pI335 (fmask pI335) (cmask pI335) (hmask pI335) 1 334 (true, (init pI335), (init pI335))) 335 12 false) = true := by
  decide +kernel
theorem I335_ok : RunOK pI335 335 (runFrom pI335 (fmask pI335) (cmask pI335) (hmask pI335) 1 334 (true, (init pI335), (init pI335))) ∧ intTest pI335 (runFrom pI335 (fmask pI335) (cmask pI335) (hmask pI335) 1 334 (true, (init pI335), (init pI335))) 335 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I335_fin) true) (by decide) rfl I335_fin intTest_fst
theorem link335 : linkOK pL335 pH335 pI335 = true := by decide +kernel
theorem cvx335 : ConvexBetweenHumps 335 :=
  cvx_of L335_ok H335_ok I335_ok link335 (by decide)

/-! ### `N = 336` -/

def pL336 : Prm := ⟨68, 33, 32, 338, 11, 18446744073709551616, 400927240813520539, 400927240813520539⟩
def pH336 : Prm := ⟨68, 33, 32, 338, 11, 18446744073709551616, 400936036906542747, 400936036906542747⟩
def pI336 : Prm := ⟨57, 28, 26, 338, 11, 18446744073709551616, 400927240813520539, 400936036906542747⟩
theorem L336_fin : (prmOK pL336 336 && ptTest pL336 (runFrom pL336 (fmask pL336) (cmask pL336) (hmask pL336) 1 335 (true, (init pL336), (init pL336))) 336 168 false) = true := by
  decide +kernel
theorem L336_ok : RunOK pL336 336 (runFrom pL336 (fmask pL336) (cmask pL336) (hmask pL336) 1 335 (true, (init pL336), (init pL336))) ∧ ptTest pL336 (runFrom pL336 (fmask pL336) (cmask pL336) (hmask pL336) 1 335 (true, (init pL336), (init pL336))) 336 168 false = true :=
  fin_run (runOK_init (prmOK_of_and L336_fin) true) (by decide) rfl L336_fin ptTest_fst
theorem H336_fin : (prmOK pH336 336 && ptTest pH336 (runFrom pH336 (fmask pH336) (cmask pH336) (hmask pH336) 1 335 (true, (init pH336), (init pH336))) 336 168 true) = true := by
  decide +kernel
theorem H336_ok : RunOK pH336 336 (runFrom pH336 (fmask pH336) (cmask pH336) (hmask pH336) 1 335 (true, (init pH336), (init pH336))) ∧ ptTest pH336 (runFrom pH336 (fmask pH336) (cmask pH336) (hmask pH336) 1 335 (true, (init pH336), (init pH336))) 336 168 true = true :=
  fin_run (runOK_init (prmOK_of_and H336_fin) true) (by decide) rfl H336_fin ptTest_fst
theorem I336_fin : (prmOK pI336 336 && intTest pI336 (runFrom pI336 (fmask pI336) (cmask pI336) (hmask pI336) 1 335 (true, (init pI336), (init pI336))) 336 12 true) = true := by
  decide +kernel
theorem I336_ok : RunOK pI336 336 (runFrom pI336 (fmask pI336) (cmask pI336) (hmask pI336) 1 335 (true, (init pI336), (init pI336))) ∧ intTest pI336 (runFrom pI336 (fmask pI336) (cmask pI336) (hmask pI336) 1 335 (true, (init pI336), (init pI336))) 336 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I336_fin) true) (by decide) rfl I336_fin intTest_fst
theorem link336 : linkOK pL336 pH336 pI336 = true := by decide +kernel
theorem cvx336 : ConvexBetweenHumps 336 :=
  cvx_of L336_ok H336_ok I336_ok link336 (by decide)
theorem cenlink336 : cenLinkOK pI336 336 = true := by decide +kernel
theorem cen336 : CenterUniqueMin 336 ∧ DipHyp 336 ∧ OnePointHyps 336 :=
  cen_of L336_ok H336_ok I336_ok link336 cenlink336

/-! ### `N = 337` -/

def pL337 : Prm := ⟨68, 33, 32, 339, 11, 18446744073709551616, 400039963323295014, 400039963323295014⟩
def pH337 : Prm := ⟨68, 33, 32, 339, 11, 18446744073709551616, 400048759416317222, 400048759416317222⟩
def pI337 : Prm := ⟨57, 28, 26, 339, 11, 18446744073709551616, 400039963323295014, 400048759416317222⟩
theorem L337_fin : (prmOK pL337 337 && ptTest pL337 (runFrom pL337 (fmask pL337) (cmask pL337) (hmask pL337) 1 336 (true, (init pL337), (init pL337))) 337 169 false) = true := by
  decide +kernel
theorem L337_ok : RunOK pL337 337 (runFrom pL337 (fmask pL337) (cmask pL337) (hmask pL337) 1 336 (true, (init pL337), (init pL337))) ∧ ptTest pL337 (runFrom pL337 (fmask pL337) (cmask pL337) (hmask pL337) 1 336 (true, (init pL337), (init pL337))) 337 169 false = true :=
  fin_run (runOK_init (prmOK_of_and L337_fin) true) (by decide) rfl L337_fin ptTest_fst
theorem H337_fin : (prmOK pH337 337 && ptTest pH337 (runFrom pH337 (fmask pH337) (cmask pH337) (hmask pH337) 1 336 (true, (init pH337), (init pH337))) 337 169 true) = true := by
  decide +kernel
theorem H337_ok : RunOK pH337 337 (runFrom pH337 (fmask pH337) (cmask pH337) (hmask pH337) 1 336 (true, (init pH337), (init pH337))) ∧ ptTest pH337 (runFrom pH337 (fmask pH337) (cmask pH337) (hmask pH337) 1 336 (true, (init pH337), (init pH337))) 337 169 true = true :=
  fin_run (runOK_init (prmOK_of_and H337_fin) true) (by decide) rfl H337_fin ptTest_fst
theorem I337_fin : (prmOK pI337 337 && intTest pI337 (runFrom pI337 (fmask pI337) (cmask pI337) (hmask pI337) 1 336 (true, (init pI337), (init pI337))) 337 12 false) = true := by
  decide +kernel
theorem I337_ok : RunOK pI337 337 (runFrom pI337 (fmask pI337) (cmask pI337) (hmask pI337) 1 336 (true, (init pI337), (init pI337))) ∧ intTest pI337 (runFrom pI337 (fmask pI337) (cmask pI337) (hmask pI337) 1 336 (true, (init pI337), (init pI337))) 337 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I337_fin) true) (by decide) rfl I337_fin intTest_fst
theorem link337 : linkOK pL337 pH337 pI337 = true := by decide +kernel
theorem cvx337 : ConvexBetweenHumps 337 :=
  cvx_of L337_ok H337_ok I337_ok link337 (by decide)

/-! ### `N = 338` -/

def pL338 : Prm := ⟨68, 33, 32, 340, 11, 18446744073709551616, 399160229319632748, 399160229319632748⟩
def pH338 : Prm := ⟨68, 33, 32, 340, 11, 18446744073709551616, 399169025412654956, 399169025412654956⟩
def pI338 : Prm := ⟨57, 28, 26, 340, 11, 18446744073709551616, 399160229319632748, 399169025412654956⟩
theorem L338_fin : (prmOK pL338 338 && ptTest pL338 (runFrom pL338 (fmask pL338) (cmask pL338) (hmask pL338) 1 337 (true, (init pL338), (init pL338))) 338 169 false) = true := by
  decide +kernel
theorem L338_ok : RunOK pL338 338 (runFrom pL338 (fmask pL338) (cmask pL338) (hmask pL338) 1 337 (true, (init pL338), (init pL338))) ∧ ptTest pL338 (runFrom pL338 (fmask pL338) (cmask pL338) (hmask pL338) 1 337 (true, (init pL338), (init pL338))) 338 169 false = true :=
  fin_run (runOK_init (prmOK_of_and L338_fin) true) (by decide) rfl L338_fin ptTest_fst
theorem H338_fin : (prmOK pH338 338 && ptTest pH338 (runFrom pH338 (fmask pH338) (cmask pH338) (hmask pH338) 1 337 (true, (init pH338), (init pH338))) 338 169 true) = true := by
  decide +kernel
theorem H338_ok : RunOK pH338 338 (runFrom pH338 (fmask pH338) (cmask pH338) (hmask pH338) 1 337 (true, (init pH338), (init pH338))) ∧ ptTest pH338 (runFrom pH338 (fmask pH338) (cmask pH338) (hmask pH338) 1 337 (true, (init pH338), (init pH338))) 338 169 true = true :=
  fin_run (runOK_init (prmOK_of_and H338_fin) true) (by decide) rfl H338_fin ptTest_fst
theorem I338_fin : (prmOK pI338 338 && intTest pI338 (runFrom pI338 (fmask pI338) (cmask pI338) (hmask pI338) 1 337 (true, (init pI338), (init pI338))) 338 12 true) = true := by
  decide +kernel
theorem I338_ok : RunOK pI338 338 (runFrom pI338 (fmask pI338) (cmask pI338) (hmask pI338) 1 337 (true, (init pI338), (init pI338))) ∧ intTest pI338 (runFrom pI338 (fmask pI338) (cmask pI338) (hmask pI338) 1 337 (true, (init pI338), (init pI338))) 338 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I338_fin) true) (by decide) rfl I338_fin intTest_fst
theorem link338 : linkOK pL338 pH338 pI338 = true := by decide +kernel
theorem cvx338 : ConvexBetweenHumps 338 :=
  cvx_of L338_ok H338_ok I338_ok link338 (by decide)
theorem cenlink338 : cenLinkOK pI338 338 = true := by decide +kernel
theorem cen338 : CenterUniqueMin 338 ∧ DipHyp 338 ∧ OnePointHyps 338 :=
  cen_of L338_ok H338_ok I338_ok link338 cenlink338

/-! ### `N = 339` -/

def pL339 : Prm := ⟨68, 33, 32, 341, 11, 18446744073709551616, 398281670612324185, 398281670612324185⟩
def pH339 : Prm := ⟨68, 33, 32, 341, 11, 18446744073709551616, 398290466705346393, 398290466705346393⟩
def pI339 : Prm := ⟨57, 28, 26, 341, 11, 18446744073709551616, 398281670612324185, 398290466705346393⟩
theorem L339_fin : (prmOK pL339 339 && ptTest pL339 (runFrom pL339 (fmask pL339) (cmask pL339) (hmask pL339) 1 338 (true, (init pL339), (init pL339))) 339 170 false) = true := by
  decide +kernel
theorem L339_ok : RunOK pL339 339 (runFrom pL339 (fmask pL339) (cmask pL339) (hmask pL339) 1 338 (true, (init pL339), (init pL339))) ∧ ptTest pL339 (runFrom pL339 (fmask pL339) (cmask pL339) (hmask pL339) 1 338 (true, (init pL339), (init pL339))) 339 170 false = true :=
  fin_run (runOK_init (prmOK_of_and L339_fin) true) (by decide) rfl L339_fin ptTest_fst
theorem H339_fin : (prmOK pH339 339 && ptTest pH339 (runFrom pH339 (fmask pH339) (cmask pH339) (hmask pH339) 1 338 (true, (init pH339), (init pH339))) 339 170 true) = true := by
  decide +kernel
theorem H339_ok : RunOK pH339 339 (runFrom pH339 (fmask pH339) (cmask pH339) (hmask pH339) 1 338 (true, (init pH339), (init pH339))) ∧ ptTest pH339 (runFrom pH339 (fmask pH339) (cmask pH339) (hmask pH339) 1 338 (true, (init pH339), (init pH339))) 339 170 true = true :=
  fin_run (runOK_init (prmOK_of_and H339_fin) true) (by decide) rfl H339_fin ptTest_fst
theorem I339_fin : (prmOK pI339 339 && intTest pI339 (runFrom pI339 (fmask pI339) (cmask pI339) (hmask pI339) 1 338 (true, (init pI339), (init pI339))) 339 12 false) = true := by
  decide +kernel
theorem I339_ok : RunOK pI339 339 (runFrom pI339 (fmask pI339) (cmask pI339) (hmask pI339) 1 338 (true, (init pI339), (init pI339))) ∧ intTest pI339 (runFrom pI339 (fmask pI339) (cmask pI339) (hmask pI339) 1 338 (true, (init pI339), (init pI339))) 339 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I339_fin) true) (by decide) rfl I339_fin intTest_fst
theorem link339 : linkOK pL339 pH339 pI339 = true := by decide +kernel
theorem cvx339 : ConvexBetweenHumps 339 :=
  cvx_of L339_ok H339_ok I339_ok link339 (by decide)

/-! ### `N = 340` -/

def pL340 : Prm := ⟨68, 33, 32, 342, 11, 18446744073709551616, 397410532113095041, 397410532113095041⟩
def pH340 : Prm := ⟨68, 33, 32, 342, 11, 18446744073709551616, 397419328206117249, 397419328206117249⟩
def pI340 : Prm := ⟨57, 28, 26, 342, 11, 18446744073709551616, 397410532113095041, 397419328206117249⟩
theorem L340_fin : (prmOK pL340 340 && ptTest pL340 (runFrom pL340 (fmask pL340) (cmask pL340) (hmask pL340) 1 339 (true, (init pL340), (init pL340))) 340 170 false) = true := by
  decide +kernel
theorem L340_ok : RunOK pL340 340 (runFrom pL340 (fmask pL340) (cmask pL340) (hmask pL340) 1 339 (true, (init pL340), (init pL340))) ∧ ptTest pL340 (runFrom pL340 (fmask pL340) (cmask pL340) (hmask pL340) 1 339 (true, (init pL340), (init pL340))) 340 170 false = true :=
  fin_run (runOK_init (prmOK_of_and L340_fin) true) (by decide) rfl L340_fin ptTest_fst
theorem H340_fin : (prmOK pH340 340 && ptTest pH340 (runFrom pH340 (fmask pH340) (cmask pH340) (hmask pH340) 1 339 (true, (init pH340), (init pH340))) 340 170 true) = true := by
  decide +kernel
theorem H340_ok : RunOK pH340 340 (runFrom pH340 (fmask pH340) (cmask pH340) (hmask pH340) 1 339 (true, (init pH340), (init pH340))) ∧ ptTest pH340 (runFrom pH340 (fmask pH340) (cmask pH340) (hmask pH340) 1 339 (true, (init pH340), (init pH340))) 340 170 true = true :=
  fin_run (runOK_init (prmOK_of_and H340_fin) true) (by decide) rfl H340_fin ptTest_fst
theorem I340_fin : (prmOK pI340 340 && intTest pI340 (runFrom pI340 (fmask pI340) (cmask pI340) (hmask pI340) 1 339 (true, (init pI340), (init pI340))) 340 12 true) = true := by
  decide +kernel
theorem I340_ok : RunOK pI340 340 (runFrom pI340 (fmask pI340) (cmask pI340) (hmask pI340) 1 339 (true, (init pI340), (init pI340))) ∧ intTest pI340 (runFrom pI340 (fmask pI340) (cmask pI340) (hmask pI340) 1 339 (true, (init pI340), (init pI340))) 340 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I340_fin) true) (by decide) rfl I340_fin intTest_fst
theorem link340 : linkOK pL340 pH340 pI340 = true := by decide +kernel
theorem cvx340 : ConvexBetweenHumps 340 :=
  cvx_of L340_ok H340_ok I340_ok link340 (by decide)
theorem cenlink340 : cenLinkOK pI340 340 = true := by decide +kernel
theorem cen340 : CenterUniqueMin 340 ∧ DipHyp 340 ∧ OnePointHyps 340 :=
  cen_of L340_ok H340_ok I340_ok link340 cenlink340

/-! ### `N = 341` -/

def pL341 : Prm := ⟨68, 33, 32, 343, 11, 18446744073709551616, 396540558610203346, 396540558610203346⟩
def pH341 : Prm := ⟨68, 33, 32, 343, 11, 18446744073709551616, 396549354703225554, 396549354703225554⟩
def pI341 : Prm := ⟨57, 28, 26, 343, 11, 18446744073709551616, 396540558610203346, 396549354703225554⟩
theorem L341_fin : (prmOK pL341 341 && ptTest pL341 (runFrom pL341 (fmask pL341) (cmask pL341) (hmask pL341) 1 340 (true, (init pL341), (init pL341))) 341 171 false) = true := by
  decide +kernel
theorem L341_ok : RunOK pL341 341 (runFrom pL341 (fmask pL341) (cmask pL341) (hmask pL341) 1 340 (true, (init pL341), (init pL341))) ∧ ptTest pL341 (runFrom pL341 (fmask pL341) (cmask pL341) (hmask pL341) 1 340 (true, (init pL341), (init pL341))) 341 171 false = true :=
  fin_run (runOK_init (prmOK_of_and L341_fin) true) (by decide) rfl L341_fin ptTest_fst
theorem H341_fin : (prmOK pH341 341 && ptTest pH341 (runFrom pH341 (fmask pH341) (cmask pH341) (hmask pH341) 1 340 (true, (init pH341), (init pH341))) 341 171 true) = true := by
  decide +kernel
theorem H341_ok : RunOK pH341 341 (runFrom pH341 (fmask pH341) (cmask pH341) (hmask pH341) 1 340 (true, (init pH341), (init pH341))) ∧ ptTest pH341 (runFrom pH341 (fmask pH341) (cmask pH341) (hmask pH341) 1 340 (true, (init pH341), (init pH341))) 341 171 true = true :=
  fin_run (runOK_init (prmOK_of_and H341_fin) true) (by decide) rfl H341_fin ptTest_fst
theorem I341_fin : (prmOK pI341 341 && intTest pI341 (runFrom pI341 (fmask pI341) (cmask pI341) (hmask pI341) 1 340 (true, (init pI341), (init pI341))) 341 12 false) = true := by
  decide +kernel
theorem I341_ok : RunOK pI341 341 (runFrom pI341 (fmask pI341) (cmask pI341) (hmask pI341) 1 340 (true, (init pI341), (init pI341))) ∧ intTest pI341 (runFrom pI341 (fmask pI341) (cmask pI341) (hmask pI341) 1 340 (true, (init pI341), (init pI341))) 341 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I341_fin) true) (by decide) rfl I341_fin intTest_fst
theorem link341 : linkOK pL341 pH341 pI341 = true := by decide +kernel
theorem cvx341 : ConvexBetweenHumps 341 :=
  cvx_of L341_ok H341_ok I341_ok link341 (by decide)

/-! ### `N = 342` -/

def pL342 : Prm := ⟨68, 33, 32, 344, 11, 18446744073709551616, 395677884745018387, 395677884745018387⟩
def pH342 : Prm := ⟨68, 33, 32, 344, 11, 18446744073709551616, 395686680838040595, 395686680838040595⟩
def pI342 : Prm := ⟨57, 28, 26, 344, 11, 18446744073709551616, 395677884745018387, 395686680838040595⟩
theorem L342_fin : (prmOK pL342 342 && ptTest pL342 (runFrom pL342 (fmask pL342) (cmask pL342) (hmask pL342) 1 341 (true, (init pL342), (init pL342))) 342 171 false) = true := by
  decide +kernel
theorem L342_ok : RunOK pL342 342 (runFrom pL342 (fmask pL342) (cmask pL342) (hmask pL342) 1 341 (true, (init pL342), (init pL342))) ∧ ptTest pL342 (runFrom pL342 (fmask pL342) (cmask pL342) (hmask pL342) 1 341 (true, (init pL342), (init pL342))) 342 171 false = true :=
  fin_run (runOK_init (prmOK_of_and L342_fin) true) (by decide) rfl L342_fin ptTest_fst
theorem H342_fin : (prmOK pH342 342 && ptTest pH342 (runFrom pH342 (fmask pH342) (cmask pH342) (hmask pH342) 1 341 (true, (init pH342), (init pH342))) 342 171 true) = true := by
  decide +kernel
theorem H342_ok : RunOK pH342 342 (runFrom pH342 (fmask pH342) (cmask pH342) (hmask pH342) 1 341 (true, (init pH342), (init pH342))) ∧ ptTest pH342 (runFrom pH342 (fmask pH342) (cmask pH342) (hmask pH342) 1 341 (true, (init pH342), (init pH342))) 342 171 true = true :=
  fin_run (runOK_init (prmOK_of_and H342_fin) true) (by decide) rfl H342_fin ptTest_fst
theorem I342_fin : (prmOK pI342 342 && intTest pI342 (runFrom pI342 (fmask pI342) (cmask pI342) (hmask pI342) 1 341 (true, (init pI342), (init pI342))) 342 12 true) = true := by
  decide +kernel
theorem I342_ok : RunOK pI342 342 (runFrom pI342 (fmask pI342) (cmask pI342) (hmask pI342) 1 341 (true, (init pI342), (init pI342))) ∧ intTest pI342 (runFrom pI342 (fmask pI342) (cmask pI342) (hmask pI342) 1 341 (true, (init pI342), (init pI342))) 342 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I342_fin) true) (by decide) rfl I342_fin intTest_fst
theorem link342 : linkOK pL342 pH342 pI342 = true := by decide +kernel
theorem cvx342 : ConvexBetweenHumps 342 :=
  cvx_of L342_ok H342_ok I342_ok link342 (by decide)
theorem cenlink342 : cenLinkOK pI342 342 = true := by decide +kernel
theorem cen342 : CenterUniqueMin 342 ∧ DipHyp 342 ∧ OnePointHyps 342 :=
  cen_of L342_ok H342_ok I342_ok link342 cenlink342

/-! ### `N = 343` -/

def pL343 : Prm := ⟨68, 33, 32, 345, 11, 18446744073709551616, 394816365650015385, 394816365650015385⟩
def pH343 : Prm := ⟨68, 33, 32, 345, 11, 18446744073709551616, 394825161743037593, 394825161743037593⟩
def pI343 : Prm := ⟨57, 28, 26, 345, 11, 18446744073709551616, 394816365650015385, 394825161743037593⟩
theorem L343_fin : (prmOK pL343 343 && ptTest pL343 (runFrom pL343 (fmask pL343) (cmask pL343) (hmask pL343) 1 342 (true, (init pL343), (init pL343))) 343 172 false) = true := by
  decide +kernel
theorem L343_ok : RunOK pL343 343 (runFrom pL343 (fmask pL343) (cmask pL343) (hmask pL343) 1 342 (true, (init pL343), (init pL343))) ∧ ptTest pL343 (runFrom pL343 (fmask pL343) (cmask pL343) (hmask pL343) 1 342 (true, (init pL343), (init pL343))) 343 172 false = true :=
  fin_run (runOK_init (prmOK_of_and L343_fin) true) (by decide) rfl L343_fin ptTest_fst
theorem H343_fin : (prmOK pH343 343 && ptTest pH343 (runFrom pH343 (fmask pH343) (cmask pH343) (hmask pH343) 1 342 (true, (init pH343), (init pH343))) 343 172 true) = true := by
  decide +kernel
theorem H343_ok : RunOK pH343 343 (runFrom pH343 (fmask pH343) (cmask pH343) (hmask pH343) 1 342 (true, (init pH343), (init pH343))) ∧ ptTest pH343 (runFrom pH343 (fmask pH343) (cmask pH343) (hmask pH343) 1 342 (true, (init pH343), (init pH343))) 343 172 true = true :=
  fin_run (runOK_init (prmOK_of_and H343_fin) true) (by decide) rfl H343_fin ptTest_fst
theorem I343_fin : (prmOK pI343 343 && intTest pI343 (runFrom pI343 (fmask pI343) (cmask pI343) (hmask pI343) 1 342 (true, (init pI343), (init pI343))) 343 12 false) = true := by
  decide +kernel
theorem I343_ok : RunOK pI343 343 (runFrom pI343 (fmask pI343) (cmask pI343) (hmask pI343) 1 342 (true, (init pI343), (init pI343))) ∧ intTest pI343 (runFrom pI343 (fmask pI343) (cmask pI343) (hmask pI343) 1 342 (true, (init pI343), (init pI343))) 343 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I343_fin) true) (by decide) rfl I343_fin intTest_fst
theorem link343 : linkOK pL343 pH343 pI343 = true := by decide +kernel
theorem cvx343 : ConvexBetweenHumps 343 :=
  cvx_of L343_ok H343_ok I343_ok link343 (by decide)

/-! ### `N = 344` -/

def pL344 : Prm := ⟨68, 33, 32, 346, 11, 18446744073709551616, 393962028255951194, 393962028255951194⟩
def pH344 : Prm := ⟨67, 31, 33, 346, 11, 18446744073709551616, 393970824348973402, 393970824348973402⟩
def pI344 : Prm := ⟨57, 28, 26, 346, 11, 18446744073709551616, 393962028255951194, 393970824348973402⟩
theorem L344_fin : (prmOK pL344 344 && ptTest pL344 (runFrom pL344 (fmask pL344) (cmask pL344) (hmask pL344) 1 343 (true, (init pL344), (init pL344))) 344 172 false) = true := by
  decide +kernel
theorem L344_ok : RunOK pL344 344 (runFrom pL344 (fmask pL344) (cmask pL344) (hmask pL344) 1 343 (true, (init pL344), (init pL344))) ∧ ptTest pL344 (runFrom pL344 (fmask pL344) (cmask pL344) (hmask pL344) 1 343 (true, (init pL344), (init pL344))) 344 172 false = true :=
  fin_run (runOK_init (prmOK_of_and L344_fin) true) (by decide) rfl L344_fin ptTest_fst
theorem H344_fin : (prmOK pH344 344 && ptTest pH344 (runFrom pH344 (fmask pH344) (cmask pH344) (hmask pH344) 1 343 (true, (init pH344), (init pH344))) 344 172 true) = true := by
  decide +kernel
theorem H344_ok : RunOK pH344 344 (runFrom pH344 (fmask pH344) (cmask pH344) (hmask pH344) 1 343 (true, (init pH344), (init pH344))) ∧ ptTest pH344 (runFrom pH344 (fmask pH344) (cmask pH344) (hmask pH344) 1 343 (true, (init pH344), (init pH344))) 344 172 true = true :=
  fin_run (runOK_init (prmOK_of_and H344_fin) true) (by decide) rfl H344_fin ptTest_fst
theorem I344_fin : (prmOK pI344 344 && intTest pI344 (runFrom pI344 (fmask pI344) (cmask pI344) (hmask pI344) 1 343 (true, (init pI344), (init pI344))) 344 12 true) = true := by
  decide +kernel
theorem I344_ok : RunOK pI344 344 (runFrom pI344 (fmask pI344) (cmask pI344) (hmask pI344) 1 343 (true, (init pI344), (init pI344))) ∧ intTest pI344 (runFrom pI344 (fmask pI344) (cmask pI344) (hmask pI344) 1 343 (true, (init pI344), (init pI344))) 344 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I344_fin) true) (by decide) rfl I344_fin intTest_fst
theorem link344 : linkOK pL344 pH344 pI344 = true := by decide +kernel
theorem cvx344 : ConvexBetweenHumps 344 :=
  cvx_of L344_ok H344_ok I344_ok link344 (by decide)
theorem cenlink344 : cenLinkOK pI344 344 = true := by decide +kernel
theorem cen344 : CenterUniqueMin 344 ∧ DipHyp 344 ∧ OnePointHyps 344 :=
  cen_of L344_ok H344_ok I344_ok link344 cenlink344

/-! ### `N = 345` -/

def pL345 : Prm := ⟨67, 31, 33, 347, 11, 18446744073709551616, 393108835481102399, 393108835481102399⟩
def pH345 : Prm := ⟨68, 33, 32, 347, 11, 18446744073709551616, 393117631574124607, 393117631574124607⟩
def pI345 : Prm := ⟨57, 28, 26, 347, 11, 18446744073709551616, 393108835481102399, 393117631574124607⟩
theorem L345_fin : (prmOK pL345 345 && ptTest pL345 (runFrom pL345 (fmask pL345) (cmask pL345) (hmask pL345) 1 344 (true, (init pL345), (init pL345))) 345 173 false) = true := by
  decide +kernel
theorem L345_ok : RunOK pL345 345 (runFrom pL345 (fmask pL345) (cmask pL345) (hmask pL345) 1 344 (true, (init pL345), (init pL345))) ∧ ptTest pL345 (runFrom pL345 (fmask pL345) (cmask pL345) (hmask pL345) 1 344 (true, (init pL345), (init pL345))) 345 173 false = true :=
  fin_run (runOK_init (prmOK_of_and L345_fin) true) (by decide) rfl L345_fin ptTest_fst
theorem H345_fin : (prmOK pH345 345 && ptTest pH345 (runFrom pH345 (fmask pH345) (cmask pH345) (hmask pH345) 1 344 (true, (init pH345), (init pH345))) 345 173 true) = true := by
  decide +kernel
theorem H345_ok : RunOK pH345 345 (runFrom pH345 (fmask pH345) (cmask pH345) (hmask pH345) 1 344 (true, (init pH345), (init pH345))) ∧ ptTest pH345 (runFrom pH345 (fmask pH345) (cmask pH345) (hmask pH345) 1 344 (true, (init pH345), (init pH345))) 345 173 true = true :=
  fin_run (runOK_init (prmOK_of_and H345_fin) true) (by decide) rfl H345_fin ptTest_fst
theorem I345_fin : (prmOK pI345 345 && intTest pI345 (runFrom pI345 (fmask pI345) (cmask pI345) (hmask pI345) 1 344 (true, (init pI345), (init pI345))) 345 12 false) = true := by
  decide +kernel
theorem I345_ok : RunOK pI345 345 (runFrom pI345 (fmask pI345) (cmask pI345) (hmask pI345) 1 344 (true, (init pI345), (init pI345))) ∧ intTest pI345 (runFrom pI345 (fmask pI345) (cmask pI345) (hmask pI345) 1 344 (true, (init pI345), (init pI345))) 345 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I345_fin) true) (by decide) rfl I345_fin intTest_fst
theorem link345 : linkOK pL345 pH345 pI345 = true := by decide +kernel
theorem cvx345 : ConvexBetweenHumps 345 :=
  cvx_of L345_ok H345_ok I345_ok link345 (by decide)

/-! ### `N = 346` -/

def pL346 : Prm := ⟨68, 33, 32, 348, 11, 18446744073709551616, 392262709031976265, 392262709031976265⟩
def pH346 : Prm := ⟨68, 33, 32, 348, 11, 18446744073709551616, 392271505124998473, 392271505124998473⟩
def pI346 : Prm := ⟨57, 28, 26, 348, 11, 18446744073709551616, 392262709031976265, 392271505124998473⟩
theorem L346_fin : (prmOK pL346 346 && ptTest pL346 (runFrom pL346 (fmask pL346) (cmask pL346) (hmask pL346) 1 345 (true, (init pL346), (init pL346))) 346 173 false) = true := by
  decide +kernel
theorem L346_ok : RunOK pL346 346 (runFrom pL346 (fmask pL346) (cmask pL346) (hmask pL346) 1 345 (true, (init pL346), (init pL346))) ∧ ptTest pL346 (runFrom pL346 (fmask pL346) (cmask pL346) (hmask pL346) 1 345 (true, (init pL346), (init pL346))) 346 173 false = true :=
  fin_run (runOK_init (prmOK_of_and L346_fin) true) (by decide) rfl L346_fin ptTest_fst
theorem H346_fin : (prmOK pH346 346 && ptTest pH346 (runFrom pH346 (fmask pH346) (cmask pH346) (hmask pH346) 1 345 (true, (init pH346), (init pH346))) 346 173 true) = true := by
  decide +kernel
theorem H346_ok : RunOK pH346 346 (runFrom pH346 (fmask pH346) (cmask pH346) (hmask pH346) 1 345 (true, (init pH346), (init pH346))) ∧ ptTest pH346 (runFrom pH346 (fmask pH346) (cmask pH346) (hmask pH346) 1 345 (true, (init pH346), (init pH346))) 346 173 true = true :=
  fin_run (runOK_init (prmOK_of_and H346_fin) true) (by decide) rfl H346_fin ptTest_fst
theorem I346_fin : (prmOK pI346 346 && intTest pI346 (runFrom pI346 (fmask pI346) (cmask pI346) (hmask pI346) 1 345 (true, (init pI346), (init pI346))) 346 12 true) = true := by
  decide +kernel
theorem I346_ok : RunOK pI346 346 (runFrom pI346 (fmask pI346) (cmask pI346) (hmask pI346) 1 345 (true, (init pI346), (init pI346))) ∧ intTest pI346 (runFrom pI346 (fmask pI346) (cmask pI346) (hmask pI346) 1 345 (true, (init pI346), (init pI346))) 346 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I346_fin) true) (by decide) rfl I346_fin intTest_fst
theorem link346 : linkOK pL346 pH346 pI346 = true := by decide +kernel
theorem cvx346 : ConvexBetweenHumps 346 :=
  cvx_of L346_ok H346_ok I346_ok link346 (by decide)
theorem cenlink346 : cenLinkOK pI346 346 = true := by decide +kernel
theorem cen346 : CenterUniqueMin 346 ∧ DipHyp 346 ∧ OnePointHyps 346 :=
  cen_of L346_ok H346_ok I346_ok link346 cenlink346

/-! ### `N = 347` -/

def pL347 : Prm := ⟨68, 33, 32, 349, 11, 18446744073709551616, 391417717127431590, 391417717127431590⟩
def pH347 : Prm := ⟨67, 31, 33, 349, 11, 18446744073709551616, 391426513220453798, 391426513220453798⟩
def pI347 : Prm := ⟨57, 28, 26, 349, 11, 18446744073709551616, 391417717127431590, 391426513220453798⟩
theorem L347_fin : (prmOK pL347 347 && ptTest pL347 (runFrom pL347 (fmask pL347) (cmask pL347) (hmask pL347) 1 346 (true, (init pL347), (init pL347))) 347 174 false) = true := by
  decide +kernel
theorem L347_ok : RunOK pL347 347 (runFrom pL347 (fmask pL347) (cmask pL347) (hmask pL347) 1 346 (true, (init pL347), (init pL347))) ∧ ptTest pL347 (runFrom pL347 (fmask pL347) (cmask pL347) (hmask pL347) 1 346 (true, (init pL347), (init pL347))) 347 174 false = true :=
  fin_run (runOK_init (prmOK_of_and L347_fin) true) (by decide) rfl L347_fin ptTest_fst
theorem H347_fin : (prmOK pH347 347 && ptTest pH347 (runFrom pH347 (fmask pH347) (cmask pH347) (hmask pH347) 1 346 (true, (init pH347), (init pH347))) 347 174 true) = true := by
  decide +kernel
theorem H347_ok : RunOK pH347 347 (runFrom pH347 (fmask pH347) (cmask pH347) (hmask pH347) 1 346 (true, (init pH347), (init pH347))) ∧ ptTest pH347 (runFrom pH347 (fmask pH347) (cmask pH347) (hmask pH347) 1 346 (true, (init pH347), (init pH347))) 347 174 true = true :=
  fin_run (runOK_init (prmOK_of_and H347_fin) true) (by decide) rfl H347_fin ptTest_fst
theorem I347_fin : (prmOK pI347 347 && intTest pI347 (runFrom pI347 (fmask pI347) (cmask pI347) (hmask pI347) 1 346 (true, (init pI347), (init pI347))) 347 12 false) = true := by
  decide +kernel
theorem I347_ok : RunOK pI347 347 (runFrom pI347 (fmask pI347) (cmask pI347) (hmask pI347) 1 346 (true, (init pI347), (init pI347))) ∧ intTest pI347 (runFrom pI347 (fmask pI347) (cmask pI347) (hmask pI347) 1 346 (true, (init pI347), (init pI347))) 347 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I347_fin) true) (by decide) rfl I347_fin intTest_fst
theorem link347 : linkOK pL347 pH347 pI347 = true := by decide +kernel
theorem cvx347 : ConvexBetweenHumps 347 :=
  cvx_of L347_ok H347_ok I347_ok link347 (by decide)

/-! ### `N = 348` -/

def pL348 : Prm := ⟨67, 31, 33, 350, 11, 18446744073709551616, 390579678665216512, 390579678665216512⟩
def pH348 : Prm := ⟨67, 31, 33, 350, 11, 18446744073709551616, 390588474758238720, 390588474758238720⟩
def pI348 : Prm := ⟨58, 28, 27, 350, 11, 18446744073709551616, 390579678665216512, 390588474758238720⟩
theorem L348_fin : (prmOK pL348 348 && ptTest pL348 (runFrom pL348 (fmask pL348) (cmask pL348) (hmask pL348) 1 347 (true, (init pL348), (init pL348))) 348 174 false) = true := by
  decide +kernel
theorem L348_ok : RunOK pL348 348 (runFrom pL348 (fmask pL348) (cmask pL348) (hmask pL348) 1 347 (true, (init pL348), (init pL348))) ∧ ptTest pL348 (runFrom pL348 (fmask pL348) (cmask pL348) (hmask pL348) 1 347 (true, (init pL348), (init pL348))) 348 174 false = true :=
  fin_run (runOK_init (prmOK_of_and L348_fin) true) (by decide) rfl L348_fin ptTest_fst
theorem H348_fin : (prmOK pH348 348 && ptTest pH348 (runFrom pH348 (fmask pH348) (cmask pH348) (hmask pH348) 1 347 (true, (init pH348), (init pH348))) 348 174 true) = true := by
  decide +kernel
theorem H348_ok : RunOK pH348 348 (runFrom pH348 (fmask pH348) (cmask pH348) (hmask pH348) 1 347 (true, (init pH348), (init pH348))) ∧ ptTest pH348 (runFrom pH348 (fmask pH348) (cmask pH348) (hmask pH348) 1 347 (true, (init pH348), (init pH348))) 348 174 true = true :=
  fin_run (runOK_init (prmOK_of_and H348_fin) true) (by decide) rfl H348_fin ptTest_fst
theorem I348_fin : (prmOK pI348 348 && intTest pI348 (runFrom pI348 (fmask pI348) (cmask pI348) (hmask pI348) 1 347 (true, (init pI348), (init pI348))) 348 12 true) = true := by
  decide +kernel
theorem I348_ok : RunOK pI348 348 (runFrom pI348 (fmask pI348) (cmask pI348) (hmask pI348) 1 347 (true, (init pI348), (init pI348))) ∧ intTest pI348 (runFrom pI348 (fmask pI348) (cmask pI348) (hmask pI348) 1 347 (true, (init pI348), (init pI348))) 348 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I348_fin) true) (by decide) rfl I348_fin intTest_fst
theorem link348 : linkOK pL348 pH348 pI348 = true := by decide +kernel
theorem cvx348 : ConvexBetweenHumps 348 :=
  cvx_of L348_ok H348_ok I348_ok link348 (by decide)
theorem cenlink348 : cenLinkOK pI348 348 = true := by decide +kernel
theorem cen348 : CenterUniqueMin 348 ∧ DipHyp 348 ∧ OnePointHyps 348 :=
  cen_of L348_ok H348_ok I348_ok link348 cenlink348

/-! ### `N = 349` -/

def pL349 : Prm := ⟨67, 31, 33, 351, 11, 18446744073709551616, 389742764750369941, 389742764750369941⟩
def pH349 : Prm := ⟨67, 31, 33, 351, 11, 18446744073709551616, 389751560843392149, 389751560843392149⟩
def pI349 : Prm := ⟨57, 28, 26, 351, 11, 18446744073709551616, 389742764750369941, 389751560843392149⟩
theorem L349_fin : (prmOK pL349 349 && ptTest pL349 (runFrom pL349 (fmask pL349) (cmask pL349) (hmask pL349) 1 348 (true, (init pL349), (init pL349))) 349 175 false) = true := by
  decide +kernel
theorem L349_ok : RunOK pL349 349 (runFrom pL349 (fmask pL349) (cmask pL349) (hmask pL349) 1 348 (true, (init pL349), (init pL349))) ∧ ptTest pL349 (runFrom pL349 (fmask pL349) (cmask pL349) (hmask pL349) 1 348 (true, (init pL349), (init pL349))) 349 175 false = true :=
  fin_run (runOK_init (prmOK_of_and L349_fin) true) (by decide) rfl L349_fin ptTest_fst
theorem H349_fin : (prmOK pH349 349 && ptTest pH349 (runFrom pH349 (fmask pH349) (cmask pH349) (hmask pH349) 1 348 (true, (init pH349), (init pH349))) 349 175 true) = true := by
  decide +kernel
theorem H349_ok : RunOK pH349 349 (runFrom pH349 (fmask pH349) (cmask pH349) (hmask pH349) 1 348 (true, (init pH349), (init pH349))) ∧ ptTest pH349 (runFrom pH349 (fmask pH349) (cmask pH349) (hmask pH349) 1 348 (true, (init pH349), (init pH349))) 349 175 true = true :=
  fin_run (runOK_init (prmOK_of_and H349_fin) true) (by decide) rfl H349_fin ptTest_fst
theorem I349_fin : (prmOK pI349 349 && intTest pI349 (runFrom pI349 (fmask pI349) (cmask pI349) (hmask pI349) 1 348 (true, (init pI349), (init pI349))) 349 12 false) = true := by
  decide +kernel
theorem I349_ok : RunOK pI349 349 (runFrom pI349 (fmask pI349) (cmask pI349) (hmask pI349) 1 348 (true, (init pI349), (init pI349))) ∧ intTest pI349 (runFrom pI349 (fmask pI349) (cmask pI349) (hmask pI349) 1 348 (true, (init pI349), (init pI349))) 349 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I349_fin) true) (by decide) rfl I349_fin intTest_fst
theorem link349 : linkOK pL349 pH349 pI349 = true := by decide +kernel
theorem cvx349 : ConvexBetweenHumps 349 :=
  cvx_of L349_ok H349_ok I349_ok link349 (by decide)

/-! ### `N = 350` -/

def pL350 : Prm := ⟨67, 31, 33, 352, 11, 18446744073709551616, 388912693818841686, 388912693818841686⟩
def pH350 : Prm := ⟨67, 31, 33, 352, 11, 18446744073709551616, 388921489911863894, 388921489911863894⟩
def pI350 : Prm := ⟨58, 28, 27, 352, 11, 18446744073709551616, 388912693818841686, 388921489911863894⟩
theorem L350_fin : (prmOK pL350 350 && ptTest pL350 (runFrom pL350 (fmask pL350) (cmask pL350) (hmask pL350) 1 349 (true, (init pL350), (init pL350))) 350 175 false) = true := by
  decide +kernel
theorem L350_ok : RunOK pL350 350 (runFrom pL350 (fmask pL350) (cmask pL350) (hmask pL350) 1 349 (true, (init pL350), (init pL350))) ∧ ptTest pL350 (runFrom pL350 (fmask pL350) (cmask pL350) (hmask pL350) 1 349 (true, (init pL350), (init pL350))) 350 175 false = true :=
  fin_run (runOK_init (prmOK_of_and L350_fin) true) (by decide) rfl L350_fin ptTest_fst
theorem H350_fin : (prmOK pH350 350 && ptTest pH350 (runFrom pH350 (fmask pH350) (cmask pH350) (hmask pH350) 1 349 (true, (init pH350), (init pH350))) 350 175 true) = true := by
  decide +kernel
theorem H350_ok : RunOK pH350 350 (runFrom pH350 (fmask pH350) (cmask pH350) (hmask pH350) 1 349 (true, (init pH350), (init pH350))) ∧ ptTest pH350 (runFrom pH350 (fmask pH350) (cmask pH350) (hmask pH350) 1 349 (true, (init pH350), (init pH350))) 350 175 true = true :=
  fin_run (runOK_init (prmOK_of_and H350_fin) true) (by decide) rfl H350_fin ptTest_fst
theorem I350_fin : (prmOK pI350 350 && intTest pI350 (runFrom pI350 (fmask pI350) (cmask pI350) (hmask pI350) 1 349 (true, (init pI350), (init pI350))) 350 12 true) = true := by
  decide +kernel
theorem I350_ok : RunOK pI350 350 (runFrom pI350 (fmask pI350) (cmask pI350) (hmask pI350) 1 349 (true, (init pI350), (init pI350))) ∧ intTest pI350 (runFrom pI350 (fmask pI350) (cmask pI350) (hmask pI350) 1 349 (true, (init pI350), (init pI350))) 350 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I350_fin) true) (by decide) rfl I350_fin intTest_fst
theorem link350 : linkOK pL350 pH350 pI350 = true := by decide +kernel
theorem cvx350 : ConvexBetweenHumps 350 :=
  cvx_of L350_ok H350_ok I350_ok link350 (by decide)
theorem cenlink350 : cenLinkOK pI350 350 = true := by decide +kernel
theorem cen350 : CenterUniqueMin 350 ∧ DipHyp 350 ∧ OnePointHyps 350 :=
  cen_of L350_ok H350_ok I350_ok link350 cenlink350

/-! ### `N = 351` -/

def pL351 : Prm := ⟨67, 31, 33, 353, 11, 18446744073709551616, 388083737515867652, 388083737515867652⟩
def pH351 : Prm := ⟨67, 31, 33, 353, 11, 18446744073709551616, 388092533608889860, 388092533608889860⟩
def pI351 : Prm := ⟨58, 28, 27, 353, 11, 18446744073709551616, 388083737515867652, 388092533608889860⟩
theorem L351_fin : (prmOK pL351 351 && ptTest pL351 (runFrom pL351 (fmask pL351) (cmask pL351) (hmask pL351) 1 350 (true, (init pL351), (init pL351))) 351 176 false) = true := by
  decide +kernel
theorem L351_ok : RunOK pL351 351 (runFrom pL351 (fmask pL351) (cmask pL351) (hmask pL351) 1 350 (true, (init pL351), (init pL351))) ∧ ptTest pL351 (runFrom pL351 (fmask pL351) (cmask pL351) (hmask pL351) 1 350 (true, (init pL351), (init pL351))) 351 176 false = true :=
  fin_run (runOK_init (prmOK_of_and L351_fin) true) (by decide) rfl L351_fin ptTest_fst
theorem H351_fin : (prmOK pH351 351 && ptTest pH351 (runFrom pH351 (fmask pH351) (cmask pH351) (hmask pH351) 1 350 (true, (init pH351), (init pH351))) 351 176 true) = true := by
  decide +kernel
theorem H351_ok : RunOK pH351 351 (runFrom pH351 (fmask pH351) (cmask pH351) (hmask pH351) 1 350 (true, (init pH351), (init pH351))) ∧ ptTest pH351 (runFrom pH351 (fmask pH351) (cmask pH351) (hmask pH351) 1 350 (true, (init pH351), (init pH351))) 351 176 true = true :=
  fin_run (runOK_init (prmOK_of_and H351_fin) true) (by decide) rfl H351_fin ptTest_fst
theorem I351_fin : (prmOK pI351 351 && intTest pI351 (runFrom pI351 (fmask pI351) (cmask pI351) (hmask pI351) 1 350 (true, (init pI351), (init pI351))) 351 12 false) = true := by
  decide +kernel
theorem I351_ok : RunOK pI351 351 (runFrom pI351 (fmask pI351) (cmask pI351) (hmask pI351) 1 350 (true, (init pI351), (init pI351))) ∧ intTest pI351 (runFrom pI351 (fmask pI351) (cmask pI351) (hmask pI351) 1 350 (true, (init pI351), (init pI351))) 351 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I351_fin) true) (by decide) rfl I351_fin intTest_fst
theorem link351 : linkOK pL351 pH351 pI351 = true := by decide +kernel
theorem cvx351 : ConvexBetweenHumps 351 :=
  cvx_of L351_ok H351_ok I351_ok link351 (by decide)

/-! ### `N = 352` -/

def pL352 : Prm := ⟨67, 31, 33, 354, 11, 18446744073709551616, 387261516096299413, 387261516096299413⟩
def pH352 : Prm := ⟨67, 31, 33, 354, 11, 18446744073709551616, 387270312189321621, 387270312189321621⟩
def pI352 : Prm := ⟨58, 28, 27, 354, 11, 18446744073709551616, 387261516096299413, 387270312189321621⟩
theorem L352_fin : (prmOK pL352 352 && ptTest pL352 (runFrom pL352 (fmask pL352) (cmask pL352) (hmask pL352) 1 351 (true, (init pL352), (init pL352))) 352 176 false) = true := by
  decide +kernel
theorem L352_ok : RunOK pL352 352 (runFrom pL352 (fmask pL352) (cmask pL352) (hmask pL352) 1 351 (true, (init pL352), (init pL352))) ∧ ptTest pL352 (runFrom pL352 (fmask pL352) (cmask pL352) (hmask pL352) 1 351 (true, (init pL352), (init pL352))) 352 176 false = true :=
  fin_run (runOK_init (prmOK_of_and L352_fin) true) (by decide) rfl L352_fin ptTest_fst
theorem H352_fin : (prmOK pH352 352 && ptTest pH352 (runFrom pH352 (fmask pH352) (cmask pH352) (hmask pH352) 1 351 (true, (init pH352), (init pH352))) 352 176 true) = true := by
  decide +kernel
theorem H352_ok : RunOK pH352 352 (runFrom pH352 (fmask pH352) (cmask pH352) (hmask pH352) 1 351 (true, (init pH352), (init pH352))) ∧ ptTest pH352 (runFrom pH352 (fmask pH352) (cmask pH352) (hmask pH352) 1 351 (true, (init pH352), (init pH352))) 352 176 true = true :=
  fin_run (runOK_init (prmOK_of_and H352_fin) true) (by decide) rfl H352_fin ptTest_fst
theorem I352_fin : (prmOK pI352 352 && intTest pI352 (runFrom pI352 (fmask pI352) (cmask pI352) (hmask pI352) 1 351 (true, (init pI352), (init pI352))) 352 12 true) = true := by
  decide +kernel
theorem I352_ok : RunOK pI352 352 (runFrom pI352 (fmask pI352) (cmask pI352) (hmask pI352) 1 351 (true, (init pI352), (init pI352))) ∧ intTest pI352 (runFrom pI352 (fmask pI352) (cmask pI352) (hmask pI352) 1 351 (true, (init pI352), (init pI352))) 352 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I352_fin) true) (by decide) rfl I352_fin intTest_fst
theorem link352 : linkOK pL352 pH352 pI352 = true := by decide +kernel
theorem cvx352 : ConvexBetweenHumps 352 :=
  cvx_of L352_ok H352_ok I352_ok link352 (by decide)
theorem cenlink352 : cenLinkOK pI352 352 = true := by decide +kernel
theorem cen352 : CenterUniqueMin 352 ∧ DipHyp 352 ∧ OnePointHyps 352 :=
  cen_of L352_ok H352_ok I352_ok link352 cenlink352

/-! ### `N = 353` -/

def pL353 : Prm := ⟨67, 31, 33, 355, 11, 18446744073709551616, 386440399465699872, 386440399465699872⟩
def pH353 : Prm := ⟨67, 31, 33, 355, 11, 18446744073709551616, 386449195558722080, 386449195558722080⟩
def pI353 : Prm := ⟨58, 28, 27, 355, 11, 18446744073709551616, 386440399465699872, 386449195558722080⟩
theorem L353_fin : (prmOK pL353 353 && ptTest pL353 (runFrom pL353 (fmask pL353) (cmask pL353) (hmask pL353) 1 352 (true, (init pL353), (init pL353))) 353 177 false) = true := by
  decide +kernel
theorem L353_ok : RunOK pL353 353 (runFrom pL353 (fmask pL353) (cmask pL353) (hmask pL353) 1 352 (true, (init pL353), (init pL353))) ∧ ptTest pL353 (runFrom pL353 (fmask pL353) (cmask pL353) (hmask pL353) 1 352 (true, (init pL353), (init pL353))) 353 177 false = true :=
  fin_run (runOK_init (prmOK_of_and L353_fin) true) (by decide) rfl L353_fin ptTest_fst
theorem H353_fin : (prmOK pH353 353 && ptTest pH353 (runFrom pH353 (fmask pH353) (cmask pH353) (hmask pH353) 1 352 (true, (init pH353), (init pH353))) 353 177 true) = true := by
  decide +kernel
theorem H353_ok : RunOK pH353 353 (runFrom pH353 (fmask pH353) (cmask pH353) (hmask pH353) 1 352 (true, (init pH353), (init pH353))) ∧ ptTest pH353 (runFrom pH353 (fmask pH353) (cmask pH353) (hmask pH353) 1 352 (true, (init pH353), (init pH353))) 353 177 true = true :=
  fin_run (runOK_init (prmOK_of_and H353_fin) true) (by decide) rfl H353_fin ptTest_fst
theorem I353_fin : (prmOK pI353 353 && intTest pI353 (runFrom pI353 (fmask pI353) (cmask pI353) (hmask pI353) 1 352 (true, (init pI353), (init pI353))) 353 12 false) = true := by
  decide +kernel
theorem I353_ok : RunOK pI353 353 (runFrom pI353 (fmask pI353) (cmask pI353) (hmask pI353) 1 352 (true, (init pI353), (init pI353))) ∧ intTest pI353 (runFrom pI353 (fmask pI353) (cmask pI353) (hmask pI353) 1 352 (true, (init pI353), (init pI353))) 353 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I353_fin) true) (by decide) rfl I353_fin intTest_fst
theorem link353 : linkOK pL353 pH353 pI353 = true := by decide +kernel
theorem cvx353 : ConvexBetweenHumps 353 :=
  cvx_of L353_ok H353_ok I353_ok link353 (by decide)

/-! ### `N = 354` -/

def pL354 : Prm := ⟨67, 31, 33, 356, 11, 18446744073709551616, 385625911914586054, 385625911914586054⟩
def pH354 : Prm := ⟨67, 31, 33, 356, 11, 18446744073709551616, 385634708007608262, 385634708007608262⟩
def pI354 : Prm := ⟨58, 28, 27, 356, 11, 18446744073709551616, 385625911914586054, 385634708007608262⟩
theorem L354_fin : (prmOK pL354 354 && ptTest pL354 (runFrom pL354 (fmask pL354) (cmask pL354) (hmask pL354) 1 353 (true, (init pL354), (init pL354))) 354 177 false) = true := by
  decide +kernel
theorem L354_ok : RunOK pL354 354 (runFrom pL354 (fmask pL354) (cmask pL354) (hmask pL354) 1 353 (true, (init pL354), (init pL354))) ∧ ptTest pL354 (runFrom pL354 (fmask pL354) (cmask pL354) (hmask pL354) 1 353 (true, (init pL354), (init pL354))) 354 177 false = true :=
  fin_run (runOK_init (prmOK_of_and L354_fin) true) (by decide) rfl L354_fin ptTest_fst
theorem H354_fin : (prmOK pH354 354 && ptTest pH354 (runFrom pH354 (fmask pH354) (cmask pH354) (hmask pH354) 1 353 (true, (init pH354), (init pH354))) 354 177 true) = true := by
  decide +kernel
theorem H354_ok : RunOK pH354 354 (runFrom pH354 (fmask pH354) (cmask pH354) (hmask pH354) 1 353 (true, (init pH354), (init pH354))) ∧ ptTest pH354 (runFrom pH354 (fmask pH354) (cmask pH354) (hmask pH354) 1 353 (true, (init pH354), (init pH354))) 354 177 true = true :=
  fin_run (runOK_init (prmOK_of_and H354_fin) true) (by decide) rfl H354_fin ptTest_fst
theorem I354_fin : (prmOK pI354 354 && intTest pI354 (runFrom pI354 (fmask pI354) (cmask pI354) (hmask pI354) 1 353 (true, (init pI354), (init pI354))) 354 12 true) = true := by
  decide +kernel
theorem I354_ok : RunOK pI354 354 (runFrom pI354 (fmask pI354) (cmask pI354) (hmask pI354) 1 353 (true, (init pI354), (init pI354))) ∧ intTest pI354 (runFrom pI354 (fmask pI354) (cmask pI354) (hmask pI354) 1 353 (true, (init pI354), (init pI354))) 354 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I354_fin) true) (by decide) rfl I354_fin intTest_fst
theorem link354 : linkOK pL354 pH354 pI354 = true := by decide +kernel
theorem cvx354 : ConvexBetweenHumps 354 :=
  cvx_of L354_ok H354_ok I354_ok link354 (by decide)
theorem cenlink354 : cenLinkOK pI354 354 = true := by decide +kernel
theorem cen354 : CenterUniqueMin 354 ∧ DipHyp 354 ∧ OnePointHyps 354 :=
  cen_of L354_ok H354_ok I354_ok link354 cenlink354

/-! ### `N = 355` -/

def pL355 : Prm := ⟨67, 31, 33, 357, 11, 18446744073709551616, 384812519392748259, 384812519392748259⟩
def pH355 : Prm := ⟨67, 31, 33, 357, 11, 18446744073709551616, 384821315485770467, 384821315485770467⟩
def pI355 : Prm := ⟨58, 28, 27, 357, 11, 18446744073709551616, 384812519392748259, 384821315485770467⟩
theorem L355_fin : (prmOK pL355 355 && ptTest pL355 (runFrom pL355 (fmask pL355) (cmask pL355) (hmask pL355) 1 354 (true, (init pL355), (init pL355))) 355 178 false) = true := by
  decide +kernel
theorem L355_ok : RunOK pL355 355 (runFrom pL355 (fmask pL355) (cmask pL355) (hmask pL355) 1 354 (true, (init pL355), (init pL355))) ∧ ptTest pL355 (runFrom pL355 (fmask pL355) (cmask pL355) (hmask pL355) 1 354 (true, (init pL355), (init pL355))) 355 178 false = true :=
  fin_run (runOK_init (prmOK_of_and L355_fin) true) (by decide) rfl L355_fin ptTest_fst
theorem H355_fin : (prmOK pH355 355 && ptTest pH355 (runFrom pH355 (fmask pH355) (cmask pH355) (hmask pH355) 1 354 (true, (init pH355), (init pH355))) 355 178 true) = true := by
  decide +kernel
theorem H355_ok : RunOK pH355 355 (runFrom pH355 (fmask pH355) (cmask pH355) (hmask pH355) 1 354 (true, (init pH355), (init pH355))) ∧ ptTest pH355 (runFrom pH355 (fmask pH355) (cmask pH355) (hmask pH355) 1 354 (true, (init pH355), (init pH355))) 355 178 true = true :=
  fin_run (runOK_init (prmOK_of_and H355_fin) true) (by decide) rfl H355_fin ptTest_fst
theorem I355_fin : (prmOK pI355 355 && intTest pI355 (runFrom pI355 (fmask pI355) (cmask pI355) (hmask pI355) 1 354 (true, (init pI355), (init pI355))) 355 12 false) = true := by
  decide +kernel
theorem I355_ok : RunOK pI355 355 (runFrom pI355 (fmask pI355) (cmask pI355) (hmask pI355) 1 354 (true, (init pI355), (init pI355))) ∧ intTest pI355 (runFrom pI355 (fmask pI355) (cmask pI355) (hmask pI355) 1 354 (true, (init pI355), (init pI355))) 355 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I355_fin) true) (by decide) rfl I355_fin intTest_fst
theorem link355 : linkOK pL355 pH355 pI355 = true := by decide +kernel
theorem cvx355 : ConvexBetweenHumps 355 :=
  cvx_of L355_ok H355_ok I355_ok link355 (by decide)

/-! ### `N = 356` -/

def pL356 : Prm := ⟨67, 31, 33, 358, 11, 18446744073709551616, 384005652381372947, 384005652381372947⟩
def pH356 : Prm := ⟨67, 31, 33, 358, 11, 18446744073709551616, 384014448474395155, 384014448474395155⟩
def pI356 : Prm := ⟨58, 28, 27, 358, 11, 18446744073709551616, 384005652381372947, 384014448474395155⟩
theorem L356_fin : (prmOK pL356 356 && ptTest pL356 (runFrom pL356 (fmask pL356) (cmask pL356) (hmask pL356) 1 355 (true, (init pL356), (init pL356))) 356 178 false) = true := by
  decide +kernel
theorem L356_ok : RunOK pL356 356 (runFrom pL356 (fmask pL356) (cmask pL356) (hmask pL356) 1 355 (true, (init pL356), (init pL356))) ∧ ptTest pL356 (runFrom pL356 (fmask pL356) (cmask pL356) (hmask pL356) 1 355 (true, (init pL356), (init pL356))) 356 178 false = true :=
  fin_run (runOK_init (prmOK_of_and L356_fin) true) (by decide) rfl L356_fin ptTest_fst
theorem H356_fin : (prmOK pH356 356 && ptTest pH356 (runFrom pH356 (fmask pH356) (cmask pH356) (hmask pH356) 1 355 (true, (init pH356), (init pH356))) 356 178 true) = true := by
  decide +kernel
theorem H356_ok : RunOK pH356 356 (runFrom pH356 (fmask pH356) (cmask pH356) (hmask pH356) 1 355 (true, (init pH356), (init pH356))) ∧ ptTest pH356 (runFrom pH356 (fmask pH356) (cmask pH356) (hmask pH356) 1 355 (true, (init pH356), (init pH356))) 356 178 true = true :=
  fin_run (runOK_init (prmOK_of_and H356_fin) true) (by decide) rfl H356_fin ptTest_fst
theorem I356_fin : (prmOK pI356 356 && intTest pI356 (runFrom pI356 (fmask pI356) (cmask pI356) (hmask pI356) 1 355 (true, (init pI356), (init pI356))) 356 12 true) = true := by
  decide +kernel
theorem I356_ok : RunOK pI356 356 (runFrom pI356 (fmask pI356) (cmask pI356) (hmask pI356) 1 355 (true, (init pI356), (init pI356))) ∧ intTest pI356 (runFrom pI356 (fmask pI356) (cmask pI356) (hmask pI356) 1 355 (true, (init pI356), (init pI356))) 356 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I356_fin) true) (by decide) rfl I356_fin intTest_fst
theorem link356 : linkOK pL356 pH356 pI356 = true := by decide +kernel
theorem cvx356 : ConvexBetweenHumps 356 :=
  cvx_of L356_ok H356_ok I356_ok link356 (by decide)
theorem cenlink356 : cenLinkOK pI356 356 = true := by decide +kernel
theorem cen356 : CenterUniqueMin 356 ∧ DipHyp 356 ∧ OnePointHyps 356 :=
  cen_of L356_ok H356_ok I356_ok link356 cenlink356

/-! ### `N = 357` -/

def pL357 : Prm := ⟨67, 31, 33, 359, 11, 18446744073709551616, 383199870720174809, 383199870720174809⟩
def pH357 : Prm := ⟨67, 31, 33, 359, 11, 18446744073709551616, 383208666813197017, 383208666813197017⟩
def pI357 : Prm := ⟨58, 28, 27, 359, 11, 18446744073709551616, 383199870720174809, 383208666813197017⟩
theorem L357_fin : (prmOK pL357 357 && ptTest pL357 (runFrom pL357 (fmask pL357) (cmask pL357) (hmask pL357) 1 356 (true, (init pL357), (init pL357))) 357 179 false) = true := by
  decide +kernel
theorem L357_ok : RunOK pL357 357 (runFrom pL357 (fmask pL357) (cmask pL357) (hmask pL357) 1 356 (true, (init pL357), (init pL357))) ∧ ptTest pL357 (runFrom pL357 (fmask pL357) (cmask pL357) (hmask pL357) 1 356 (true, (init pL357), (init pL357))) 357 179 false = true :=
  fin_run (runOK_init (prmOK_of_and L357_fin) true) (by decide) rfl L357_fin ptTest_fst
theorem H357_fin : (prmOK pH357 357 && ptTest pH357 (runFrom pH357 (fmask pH357) (cmask pH357) (hmask pH357) 1 356 (true, (init pH357), (init pH357))) 357 179 true) = true := by
  decide +kernel
theorem H357_ok : RunOK pH357 357 (runFrom pH357 (fmask pH357) (cmask pH357) (hmask pH357) 1 356 (true, (init pH357), (init pH357))) ∧ ptTest pH357 (runFrom pH357 (fmask pH357) (cmask pH357) (hmask pH357) 1 356 (true, (init pH357), (init pH357))) 357 179 true = true :=
  fin_run (runOK_init (prmOK_of_and H357_fin) true) (by decide) rfl H357_fin ptTest_fst
theorem I357_fin : (prmOK pI357 357 && intTest pI357 (runFrom pI357 (fmask pI357) (cmask pI357) (hmask pI357) 1 356 (true, (init pI357), (init pI357))) 357 12 false) = true := by
  decide +kernel
theorem I357_ok : RunOK pI357 357 (runFrom pI357 (fmask pI357) (cmask pI357) (hmask pI357) 1 356 (true, (init pI357), (init pI357))) ∧ intTest pI357 (runFrom pI357 (fmask pI357) (cmask pI357) (hmask pI357) 1 356 (true, (init pI357), (init pI357))) 357 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I357_fin) true) (by decide) rfl I357_fin intTest_fst
theorem link357 : linkOK pL357 pH357 pI357 = true := by decide +kernel
theorem cvx357 : ConvexBetweenHumps 357 :=
  cvx_of L357_ok H357_ok I357_ok link357 (by decide)

/-! ### `N = 358` -/

def pL358 : Prm := ⟨67, 31, 33, 360, 11, 18446744073709551616, 382400513176098695, 382400513176098695⟩
def pH358 : Prm := ⟨67, 31, 33, 360, 11, 18446744073709551616, 382409309269120903, 382409309269120903⟩
def pI358 : Prm := ⟨58, 28, 27, 360, 11, 18446744073709551616, 382400513176098695, 382409309269120903⟩
theorem L358_fin : (prmOK pL358 358 && ptTest pL358 (runFrom pL358 (fmask pL358) (cmask pL358) (hmask pL358) 1 357 (true, (init pL358), (init pL358))) 358 179 false) = true := by
  decide +kernel
theorem L358_ok : RunOK pL358 358 (runFrom pL358 (fmask pL358) (cmask pL358) (hmask pL358) 1 357 (true, (init pL358), (init pL358))) ∧ ptTest pL358 (runFrom pL358 (fmask pL358) (cmask pL358) (hmask pL358) 1 357 (true, (init pL358), (init pL358))) 358 179 false = true :=
  fin_run (runOK_init (prmOK_of_and L358_fin) true) (by decide) rfl L358_fin ptTest_fst
theorem H358_fin : (prmOK pH358 358 && ptTest pH358 (runFrom pH358 (fmask pH358) (cmask pH358) (hmask pH358) 1 357 (true, (init pH358), (init pH358))) 358 179 true) = true := by
  decide +kernel
theorem H358_ok : RunOK pH358 358 (runFrom pH358 (fmask pH358) (cmask pH358) (hmask pH358) 1 357 (true, (init pH358), (init pH358))) ∧ ptTest pH358 (runFrom pH358 (fmask pH358) (cmask pH358) (hmask pH358) 1 357 (true, (init pH358), (init pH358))) 358 179 true = true :=
  fin_run (runOK_init (prmOK_of_and H358_fin) true) (by decide) rfl H358_fin ptTest_fst
theorem I358_fin : (prmOK pI358 358 && intTest pI358 (runFrom pI358 (fmask pI358) (cmask pI358) (hmask pI358) 1 357 (true, (init pI358), (init pI358))) 358 12 true) = true := by
  decide +kernel
theorem I358_ok : RunOK pI358 358 (runFrom pI358 (fmask pI358) (cmask pI358) (hmask pI358) 1 357 (true, (init pI358), (init pI358))) ∧ intTest pI358 (runFrom pI358 (fmask pI358) (cmask pI358) (hmask pI358) 1 357 (true, (init pI358), (init pI358))) 358 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I358_fin) true) (by decide) rfl I358_fin intTest_fst
theorem link358 : linkOK pL358 pH358 pI358 = true := by decide +kernel
theorem cvx358 : ConvexBetweenHumps 358 :=
  cvx_of L358_ok H358_ok I358_ok link358 (by decide)
theorem cenlink358 : cenLinkOK pI358 358 = true := by decide +kernel
theorem cen358 : CenterUniqueMin 358 ∧ DipHyp 358 ∧ OnePointHyps 358 :=
  cen_of L358_ok H358_ok I358_ok link358 cenlink358

/-! ### `N = 359` -/

def pL359 : Prm := ⟨67, 31, 33, 361, 11, 18446744073709551616, 381602231384229687, 381602231384229687⟩
def pH359 : Prm := ⟨67, 31, 33, 361, 11, 18446744073709551616, 381611027477251895, 381611027477251895⟩
def pI359 : Prm := ⟨58, 28, 27, 361, 11, 18446744073709551616, 381602231384229687, 381611027477251895⟩
theorem L359_fin : (prmOK pL359 359 && ptTest pL359 (runFrom pL359 (fmask pL359) (cmask pL359) (hmask pL359) 1 358 (true, (init pL359), (init pL359))) 359 180 false) = true := by
  decide +kernel
theorem L359_ok : RunOK pL359 359 (runFrom pL359 (fmask pL359) (cmask pL359) (hmask pL359) 1 358 (true, (init pL359), (init pL359))) ∧ ptTest pL359 (runFrom pL359 (fmask pL359) (cmask pL359) (hmask pL359) 1 358 (true, (init pL359), (init pL359))) 359 180 false = true :=
  fin_run (runOK_init (prmOK_of_and L359_fin) true) (by decide) rfl L359_fin ptTest_fst
theorem H359_fin : (prmOK pH359 359 && ptTest pH359 (runFrom pH359 (fmask pH359) (cmask pH359) (hmask pH359) 1 358 (true, (init pH359), (init pH359))) 359 180 true) = true := by
  decide +kernel
theorem H359_ok : RunOK pH359 359 (runFrom pH359 (fmask pH359) (cmask pH359) (hmask pH359) 1 358 (true, (init pH359), (init pH359))) ∧ ptTest pH359 (runFrom pH359 (fmask pH359) (cmask pH359) (hmask pH359) 1 358 (true, (init pH359), (init pH359))) 359 180 true = true :=
  fin_run (runOK_init (prmOK_of_and H359_fin) true) (by decide) rfl H359_fin ptTest_fst
theorem I359_fin : (prmOK pI359 359 && intTest pI359 (runFrom pI359 (fmask pI359) (cmask pI359) (hmask pI359) 1 358 (true, (init pI359), (init pI359))) 359 12 false) = true := by
  decide +kernel
theorem I359_ok : RunOK pI359 359 (runFrom pI359 (fmask pI359) (cmask pI359) (hmask pI359) 1 358 (true, (init pI359), (init pI359))) ∧ intTest pI359 (runFrom pI359 (fmask pI359) (cmask pI359) (hmask pI359) 1 358 (true, (init pI359), (init pI359))) 359 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I359_fin) true) (by decide) rfl I359_fin intTest_fst
theorem link359 : linkOK pL359 pH359 pI359 = true := by decide +kernel
theorem cvx359 : ConvexBetweenHumps 359 :=
  cvx_of L359_ok H359_ok I359_ok link359 (by decide)

/-! ### `N = 360` -/

def pL360 : Prm := ⟨67, 31, 33, 362, 11, 18446744073709551616, 380810274434547888, 380810274434547888⟩
def pH360 : Prm := ⟨67, 31, 33, 362, 11, 18446744073709551616, 380819070527570096, 380819070527570096⟩
def pI360 : Prm := ⟨58, 28, 27, 362, 11, 18446744073709551616, 380810274434547888, 380819070527570096⟩
theorem L360_fin : (prmOK pL360 360 && ptTest pL360 (runFrom pL360 (fmask pL360) (cmask pL360) (hmask pL360) 1 359 (true, (init pL360), (init pL360))) 360 180 false) = true := by
  decide +kernel
theorem L360_ok : RunOK pL360 360 (runFrom pL360 (fmask pL360) (cmask pL360) (hmask pL360) 1 359 (true, (init pL360), (init pL360))) ∧ ptTest pL360 (runFrom pL360 (fmask pL360) (cmask pL360) (hmask pL360) 1 359 (true, (init pL360), (init pL360))) 360 180 false = true :=
  fin_run (runOK_init (prmOK_of_and L360_fin) true) (by decide) rfl L360_fin ptTest_fst
theorem H360_fin : (prmOK pH360 360 && ptTest pH360 (runFrom pH360 (fmask pH360) (cmask pH360) (hmask pH360) 1 359 (true, (init pH360), (init pH360))) 360 180 true) = true := by
  decide +kernel
theorem H360_ok : RunOK pH360 360 (runFrom pH360 (fmask pH360) (cmask pH360) (hmask pH360) 1 359 (true, (init pH360), (init pH360))) ∧ ptTest pH360 (runFrom pH360 (fmask pH360) (cmask pH360) (hmask pH360) 1 359 (true, (init pH360), (init pH360))) 360 180 true = true :=
  fin_run (runOK_init (prmOK_of_and H360_fin) true) (by decide) rfl H360_fin ptTest_fst
theorem I360_fin : (prmOK pI360 360 && intTest pI360 (runFrom pI360 (fmask pI360) (cmask pI360) (hmask pI360) 1 359 (true, (init pI360), (init pI360))) 360 12 true) = true := by
  decide +kernel
theorem I360_ok : RunOK pI360 360 (runFrom pI360 (fmask pI360) (cmask pI360) (hmask pI360) 1 359 (true, (init pI360), (init pI360))) ∧ intTest pI360 (runFrom pI360 (fmask pI360) (cmask pI360) (hmask pI360) 1 359 (true, (init pI360), (init pI360))) 360 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I360_fin) true) (by decide) rfl I360_fin intTest_fst
theorem link360 : linkOK pL360 pH360 pI360 = true := by decide +kernel
theorem cvx360 : ConvexBetweenHumps 360 :=
  cvx_of L360_ok H360_ok I360_ok link360 (by decide)
theorem cenlink360 : cenLinkOK pI360 360 = true := by decide +kernel
theorem cen360 : CenterUniqueMin 360 ∧ DipHyp 360 ∧ OnePointHyps 360 :=
  cen_of L360_ok H360_ok I360_ok link360 cenlink360

/-! ### `N = 361` -/

def pL361 : Prm := ⟨67, 31, 33, 363, 11, 18446744073709551616, 380019383720674628, 380019383720674628⟩
def pH361 : Prm := ⟨67, 31, 33, 363, 11, 18446744073709551616, 380028179813696836, 380028179813696836⟩
def pI361 : Prm := ⟨58, 28, 27, 363, 11, 18446744073709551616, 380019383720674628, 380028179813696836⟩
theorem L361_fin : (prmOK pL361 361 && ptTest pL361 (runFrom pL361 (fmask pL361) (cmask pL361) (hmask pL361) 1 360 (true, (init pL361), (init pL361))) 361 181 false) = true := by
  decide +kernel
theorem L361_ok : RunOK pL361 361 (runFrom pL361 (fmask pL361) (cmask pL361) (hmask pL361) 1 360 (true, (init pL361), (init pL361))) ∧ ptTest pL361 (runFrom pL361 (fmask pL361) (cmask pL361) (hmask pL361) 1 360 (true, (init pL361), (init pL361))) 361 181 false = true :=
  fin_run (runOK_init (prmOK_of_and L361_fin) true) (by decide) rfl L361_fin ptTest_fst
theorem H361_fin : (prmOK pH361 361 && ptTest pH361 (runFrom pH361 (fmask pH361) (cmask pH361) (hmask pH361) 1 360 (true, (init pH361), (init pH361))) 361 181 true) = true := by
  decide +kernel
theorem H361_ok : RunOK pH361 361 (runFrom pH361 (fmask pH361) (cmask pH361) (hmask pH361) 1 360 (true, (init pH361), (init pH361))) ∧ ptTest pH361 (runFrom pH361 (fmask pH361) (cmask pH361) (hmask pH361) 1 360 (true, (init pH361), (init pH361))) 361 181 true = true :=
  fin_run (runOK_init (prmOK_of_and H361_fin) true) (by decide) rfl H361_fin ptTest_fst
theorem I361_fin : (prmOK pI361 361 && intTest pI361 (runFrom pI361 (fmask pI361) (cmask pI361) (hmask pI361) 1 360 (true, (init pI361), (init pI361))) 361 12 false) = true := by
  decide +kernel
theorem I361_ok : RunOK pI361 361 (runFrom pI361 (fmask pI361) (cmask pI361) (hmask pI361) 1 360 (true, (init pI361), (init pI361))) ∧ intTest pI361 (runFrom pI361 (fmask pI361) (cmask pI361) (hmask pI361) 1 360 (true, (init pI361), (init pI361))) 361 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I361_fin) true) (by decide) rfl I361_fin intTest_fst
theorem link361 : linkOK pL361 pH361 pI361 = true := by decide +kernel
theorem cvx361 : ConvexBetweenHumps 361 :=
  cvx_of L361_ok H361_ok I361_ok link361 (by decide)

/-! ### `N = 362` -/

def pL362 : Prm := ⟨67, 31, 33, 364, 11, 18446744073709551616, 379234720637008491, 379234720637008491⟩
def pH362 : Prm := ⟨67, 31, 33, 364, 11, 18446744073709551616, 379243516730030699, 379243516730030699⟩
def pI362 : Prm := ⟨58, 28, 27, 364, 11, 18446744073709551616, 379234720637008491, 379243516730030699⟩
theorem L362_fin : (prmOK pL362 362 && ptTest pL362 (runFrom pL362 (fmask pL362) (cmask pL362) (hmask pL362) 1 361 (true, (init pL362), (init pL362))) 362 181 false) = true := by
  decide +kernel
theorem L362_ok : RunOK pL362 362 (runFrom pL362 (fmask pL362) (cmask pL362) (hmask pL362) 1 361 (true, (init pL362), (init pL362))) ∧ ptTest pL362 (runFrom pL362 (fmask pL362) (cmask pL362) (hmask pL362) 1 361 (true, (init pL362), (init pL362))) 362 181 false = true :=
  fin_run (runOK_init (prmOK_of_and L362_fin) true) (by decide) rfl L362_fin ptTest_fst
theorem H362_fin : (prmOK pH362 362 && ptTest pH362 (runFrom pH362 (fmask pH362) (cmask pH362) (hmask pH362) 1 361 (true, (init pH362), (init pH362))) 362 181 true) = true := by
  decide +kernel
theorem H362_ok : RunOK pH362 362 (runFrom pH362 (fmask pH362) (cmask pH362) (hmask pH362) 1 361 (true, (init pH362), (init pH362))) ∧ ptTest pH362 (runFrom pH362 (fmask pH362) (cmask pH362) (hmask pH362) 1 361 (true, (init pH362), (init pH362))) 362 181 true = true :=
  fin_run (runOK_init (prmOK_of_and H362_fin) true) (by decide) rfl H362_fin ptTest_fst
theorem I362_fin : (prmOK pI362 362 && intTest pI362 (runFrom pI362 (fmask pI362) (cmask pI362) (hmask pI362) 1 361 (true, (init pI362), (init pI362))) 362 12 true) = true := by
  decide +kernel
theorem I362_ok : RunOK pI362 362 (runFrom pI362 (fmask pI362) (cmask pI362) (hmask pI362) 1 361 (true, (init pI362), (init pI362))) ∧ intTest pI362 (runFrom pI362 (fmask pI362) (cmask pI362) (hmask pI362) 1 361 (true, (init pI362), (init pI362))) 362 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I362_fin) true) (by decide) rfl I362_fin intTest_fst
theorem link362 : linkOK pL362 pH362 pI362 = true := by decide +kernel
theorem cvx362 : ConvexBetweenHumps 362 :=
  cvx_of L362_ok H362_ok I362_ok link362 (by decide)
theorem cenlink362 : cenLinkOK pI362 362 = true := by decide +kernel
theorem cen362 : CenterUniqueMin 362 ∧ DipHyp 362 ∧ OnePointHyps 362 :=
  cen_of L362_ok H362_ok I362_ok link362 cenlink362

/-! ### `N = 363` -/

def pL363 : Prm := ⟨67, 31, 33, 365, 11, 18446744073709551616, 378451114354692765, 378451114354692765⟩
def pH363 : Prm := ⟨67, 31, 33, 365, 11, 18446744073709551616, 378459910447714973, 378459910447714973⟩
def pI363 : Prm := ⟨58, 28, 27, 365, 11, 18446744073709551616, 378451114354692765, 378459910447714973⟩
theorem L363_fin : (prmOK pL363 363 && ptTest pL363 (runFrom pL363 (fmask pL363) (cmask pL363) (hmask pL363) 1 362 (true, (init pL363), (init pL363))) 363 182 false) = true := by
  decide +kernel
theorem L363_ok : RunOK pL363 363 (runFrom pL363 (fmask pL363) (cmask pL363) (hmask pL363) 1 362 (true, (init pL363), (init pL363))) ∧ ptTest pL363 (runFrom pL363 (fmask pL363) (cmask pL363) (hmask pL363) 1 362 (true, (init pL363), (init pL363))) 363 182 false = true :=
  fin_run (runOK_init (prmOK_of_and L363_fin) true) (by decide) rfl L363_fin ptTest_fst
theorem H363_fin : (prmOK pH363 363 && ptTest pH363 (runFrom pH363 (fmask pH363) (cmask pH363) (hmask pH363) 1 362 (true, (init pH363), (init pH363))) 363 182 true) = true := by
  decide +kernel
theorem H363_ok : RunOK pH363 363 (runFrom pH363 (fmask pH363) (cmask pH363) (hmask pH363) 1 362 (true, (init pH363), (init pH363))) ∧ ptTest pH363 (runFrom pH363 (fmask pH363) (cmask pH363) (hmask pH363) 1 362 (true, (init pH363), (init pH363))) 363 182 true = true :=
  fin_run (runOK_init (prmOK_of_and H363_fin) true) (by decide) rfl H363_fin ptTest_fst
theorem I363_fin : (prmOK pI363 363 && intTest pI363 (runFrom pI363 (fmask pI363) (cmask pI363) (hmask pI363) 1 362 (true, (init pI363), (init pI363))) 363 12 false) = true := by
  decide +kernel
theorem I363_ok : RunOK pI363 363 (runFrom pI363 (fmask pI363) (cmask pI363) (hmask pI363) 1 362 (true, (init pI363), (init pI363))) ∧ intTest pI363 (runFrom pI363 (fmask pI363) (cmask pI363) (hmask pI363) 1 362 (true, (init pI363), (init pI363))) 363 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I363_fin) true) (by decide) rfl I363_fin intTest_fst
theorem link363 : linkOK pL363 pH363 pI363 = true := by decide +kernel
theorem cvx363 : ConvexBetweenHumps 363 :=
  cvx_of L363_ok H363_ok I363_ok link363 (by decide)

/-! ### `N = 364` -/

def pL364 : Prm := ⟨67, 31, 33, 366, 11, 18446744073709551616, 377673640499804995, 377673640499804995⟩
def pH364 : Prm := ⟨67, 31, 33, 366, 11, 18446744073709551616, 377682436592827203, 377682436592827203⟩
def pI364 : Prm := ⟨59, 28, 28, 366, 11, 18446744073709551616, 377673640499804995, 377682436592827203⟩
theorem L364_fin : (prmOK pL364 364 && ptTest pL364 (runFrom pL364 (fmask pL364) (cmask pL364) (hmask pL364) 1 363 (true, (init pL364), (init pL364))) 364 182 false) = true := by
  decide +kernel
theorem L364_ok : RunOK pL364 364 (runFrom pL364 (fmask pL364) (cmask pL364) (hmask pL364) 1 363 (true, (init pL364), (init pL364))) ∧ ptTest pL364 (runFrom pL364 (fmask pL364) (cmask pL364) (hmask pL364) 1 363 (true, (init pL364), (init pL364))) 364 182 false = true :=
  fin_run (runOK_init (prmOK_of_and L364_fin) true) (by decide) rfl L364_fin ptTest_fst
theorem H364_fin : (prmOK pH364 364 && ptTest pH364 (runFrom pH364 (fmask pH364) (cmask pH364) (hmask pH364) 1 363 (true, (init pH364), (init pH364))) 364 182 true) = true := by
  decide +kernel
theorem H364_ok : RunOK pH364 364 (runFrom pH364 (fmask pH364) (cmask pH364) (hmask pH364) 1 363 (true, (init pH364), (init pH364))) ∧ ptTest pH364 (runFrom pH364 (fmask pH364) (cmask pH364) (hmask pH364) 1 363 (true, (init pH364), (init pH364))) 364 182 true = true :=
  fin_run (runOK_init (prmOK_of_and H364_fin) true) (by decide) rfl H364_fin ptTest_fst
theorem I364_fin : (prmOK pI364 364 && intTest pI364 (runFrom pI364 (fmask pI364) (cmask pI364) (hmask pI364) 1 363 (true, (init pI364), (init pI364))) 364 12 true) = true := by
  decide +kernel
theorem I364_ok : RunOK pI364 364 (runFrom pI364 (fmask pI364) (cmask pI364) (hmask pI364) 1 363 (true, (init pI364), (init pI364))) ∧ intTest pI364 (runFrom pI364 (fmask pI364) (cmask pI364) (hmask pI364) 1 363 (true, (init pI364), (init pI364))) 364 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I364_fin) true) (by decide) rfl I364_fin intTest_fst
theorem link364 : linkOK pL364 pH364 pI364 = true := by decide +kernel
theorem cvx364 : ConvexBetweenHumps 364 :=
  cvx_of L364_ok H364_ok I364_ok link364 (by decide)
theorem cenlink364 : cenLinkOK pI364 364 = true := by decide +kernel
theorem cen364 : CenterUniqueMin 364 ∧ DipHyp 364 ∧ OnePointHyps 364 :=
  cen_of L364_ok H364_ok I364_ok link364 cenlink364

/-! ### `N = 365` -/

def pL365 : Prm := ⟨67, 31, 33, 367, 11, 18446744073709551616, 376897214094026644, 376897214094026644⟩
def pH365 : Prm := ⟨67, 31, 33, 367, 11, 18446744073709551616, 376906010187048852, 376906010187048852⟩
def pI365 : Prm := ⟨59, 28, 28, 367, 11, 18446744073709551616, 376897214094026644, 376906010187048852⟩
theorem L365_fin : (prmOK pL365 365 && ptTest pL365 (runFrom pL365 (fmask pL365) (cmask pL365) (hmask pL365) 1 364 (true, (init pL365), (init pL365))) 365 183 false) = true := by
  decide +kernel
theorem L365_ok : RunOK pL365 365 (runFrom pL365 (fmask pL365) (cmask pL365) (hmask pL365) 1 364 (true, (init pL365), (init pL365))) ∧ ptTest pL365 (runFrom pL365 (fmask pL365) (cmask pL365) (hmask pL365) 1 364 (true, (init pL365), (init pL365))) 365 183 false = true :=
  fin_run (runOK_init (prmOK_of_and L365_fin) true) (by decide) rfl L365_fin ptTest_fst
theorem H365_fin : (prmOK pH365 365 && ptTest pH365 (runFrom pH365 (fmask pH365) (cmask pH365) (hmask pH365) 1 364 (true, (init pH365), (init pH365))) 365 183 true) = true := by
  decide +kernel
theorem H365_ok : RunOK pH365 365 (runFrom pH365 (fmask pH365) (cmask pH365) (hmask pH365) 1 364 (true, (init pH365), (init pH365))) ∧ ptTest pH365 (runFrom pH365 (fmask pH365) (cmask pH365) (hmask pH365) 1 364 (true, (init pH365), (init pH365))) 365 183 true = true :=
  fin_run (runOK_init (prmOK_of_and H365_fin) true) (by decide) rfl H365_fin ptTest_fst
theorem I365_fin : (prmOK pI365 365 && intTest pI365 (runFrom pI365 (fmask pI365) (cmask pI365) (hmask pI365) 1 364 (true, (init pI365), (init pI365))) 365 12 false) = true := by
  decide +kernel
theorem I365_ok : RunOK pI365 365 (runFrom pI365 (fmask pI365) (cmask pI365) (hmask pI365) 1 364 (true, (init pI365), (init pI365))) ∧ intTest pI365 (runFrom pI365 (fmask pI365) (cmask pI365) (hmask pI365) 1 364 (true, (init pI365), (init pI365))) 365 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I365_fin) true) (by decide) rfl I365_fin intTest_fst
theorem link365 : linkOK pL365 pH365 pI365 = true := by decide +kernel
theorem cvx365 : ConvexBetweenHumps 365 :=
  cvx_of L365_ok H365_ok I365_ok link365 (by decide)

/-! ### `N = 366` -/

def pL366 : Prm := ⟨67, 31, 33, 368, 11, 18446744073709551616, 376126826870078182, 376126826870078182⟩
def pH366 : Prm := ⟨67, 31, 33, 368, 11, 18446744073709551616, 376135622963100390, 376135622963100390⟩
def pI366 : Prm := ⟨59, 28, 28, 368, 11, 18446744073709551616, 376126826870078182, 376135622963100390⟩
theorem L366_fin : (prmOK pL366 366 && ptTest pL366 (runFrom pL366 (fmask pL366) (cmask pL366) (hmask pL366) 1 365 (true, (init pL366), (init pL366))) 366 183 false) = true := by
  decide +kernel
theorem L366_ok : RunOK pL366 366 (runFrom pL366 (fmask pL366) (cmask pL366) (hmask pL366) 1 365 (true, (init pL366), (init pL366))) ∧ ptTest pL366 (runFrom pL366 (fmask pL366) (cmask pL366) (hmask pL366) 1 365 (true, (init pL366), (init pL366))) 366 183 false = true :=
  fin_run (runOK_init (prmOK_of_and L366_fin) true) (by decide) rfl L366_fin ptTest_fst
theorem H366_fin : (prmOK pH366 366 && ptTest pH366 (runFrom pH366 (fmask pH366) (cmask pH366) (hmask pH366) 1 365 (true, (init pH366), (init pH366))) 366 183 true) = true := by
  decide +kernel
theorem H366_ok : RunOK pH366 366 (runFrom pH366 (fmask pH366) (cmask pH366) (hmask pH366) 1 365 (true, (init pH366), (init pH366))) ∧ ptTest pH366 (runFrom pH366 (fmask pH366) (cmask pH366) (hmask pH366) 1 365 (true, (init pH366), (init pH366))) 366 183 true = true :=
  fin_run (runOK_init (prmOK_of_and H366_fin) true) (by decide) rfl H366_fin ptTest_fst
theorem I366_fin : (prmOK pI366 366 && intTest pI366 (runFrom pI366 (fmask pI366) (cmask pI366) (hmask pI366) 1 365 (true, (init pI366), (init pI366))) 366 12 true) = true := by
  decide +kernel
theorem I366_ok : RunOK pI366 366 (runFrom pI366 (fmask pI366) (cmask pI366) (hmask pI366) 1 365 (true, (init pI366), (init pI366))) ∧ intTest pI366 (runFrom pI366 (fmask pI366) (cmask pI366) (hmask pI366) 1 365 (true, (init pI366), (init pI366))) 366 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I366_fin) true) (by decide) rfl I366_fin intTest_fst
theorem link366 : linkOK pL366 pH366 pI366 = true := by decide +kernel
theorem cvx366 : ConvexBetweenHumps 366 :=
  cvx_of L366_ok H366_ok I366_ok link366 (by decide)
theorem cenlink366 : cenLinkOK pI366 366 = true := by decide +kernel
theorem cen366 : CenterUniqueMin 366 ∧ DipHyp 366 ∧ OnePointHyps 366 :=
  cen_of L366_ok H366_ok I366_ok link366 cenlink366

/-! ### `N = 367` -/

def pL367 : Prm := ⟨67, 31, 33, 369, 11, 18446744073709551616, 375357477825473540, 375357477825473540⟩
def pH367 : Prm := ⟨67, 31, 33, 369, 11, 18446744073709551616, 375366273918495748, 375366273918495748⟩
def pI367 : Prm := ⟨59, 28, 28, 369, 11, 18446744073709551616, 375357477825473540, 375366273918495748⟩
theorem L367_fin : (prmOK pL367 367 && ptTest pL367 (runFrom pL367 (fmask pL367) (cmask pL367) (hmask pL367) 1 366 (true, (init pL367), (init pL367))) 367 184 false) = true := by
  decide +kernel
theorem L367_ok : RunOK pL367 367 (runFrom pL367 (fmask pL367) (cmask pL367) (hmask pL367) 1 366 (true, (init pL367), (init pL367))) ∧ ptTest pL367 (runFrom pL367 (fmask pL367) (cmask pL367) (hmask pL367) 1 366 (true, (init pL367), (init pL367))) 367 184 false = true :=
  fin_run (runOK_init (prmOK_of_and L367_fin) true) (by decide) rfl L367_fin ptTest_fst
theorem H367_fin : (prmOK pH367 367 && ptTest pH367 (runFrom pH367 (fmask pH367) (cmask pH367) (hmask pH367) 1 366 (true, (init pH367), (init pH367))) 367 184 true) = true := by
  decide +kernel
theorem H367_ok : RunOK pH367 367 (runFrom pH367 (fmask pH367) (cmask pH367) (hmask pH367) 1 366 (true, (init pH367), (init pH367))) ∧ ptTest pH367 (runFrom pH367 (fmask pH367) (cmask pH367) (hmask pH367) 1 366 (true, (init pH367), (init pH367))) 367 184 true = true :=
  fin_run (runOK_init (prmOK_of_and H367_fin) true) (by decide) rfl H367_fin ptTest_fst
theorem I367_fin : (prmOK pI367 367 && intTest pI367 (runFrom pI367 (fmask pI367) (cmask pI367) (hmask pI367) 1 366 (true, (init pI367), (init pI367))) 367 13 false) = true := by
  decide +kernel
theorem I367_ok : RunOK pI367 367 (runFrom pI367 (fmask pI367) (cmask pI367) (hmask pI367) 1 366 (true, (init pI367), (init pI367))) ∧ intTest pI367 (runFrom pI367 (fmask pI367) (cmask pI367) (hmask pI367) 1 366 (true, (init pI367), (init pI367))) 367 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I367_fin) true) (by decide) rfl I367_fin intTest_fst
theorem link367 : linkOK pL367 pH367 pI367 = true := by decide +kernel
theorem cvx367 : ConvexBetweenHumps 367 :=
  cvx_of L367_ok H367_ok I367_ok link367 (by decide)

/-! ### `N = 368` -/

def pL368 : Prm := ⟨67, 31, 33, 370, 11, 18446744073709551616, 374594076623811526, 374594076623811526⟩
def pH368 : Prm := ⟨67, 31, 33, 370, 11, 18446744073709551616, 374602872716833734, 374602872716833734⟩
def pI368 : Prm := ⟨59, 28, 28, 370, 11, 18446744073709551616, 374594076623811526, 374602872716833734⟩
theorem L368_fin : (prmOK pL368 368 && ptTest pL368 (runFrom pL368 (fmask pL368) (cmask pL368) (hmask pL368) 1 367 (true, (init pL368), (init pL368))) 368 184 false) = true := by
  decide +kernel
theorem L368_ok : RunOK pL368 368 (runFrom pL368 (fmask pL368) (cmask pL368) (hmask pL368) 1 367 (true, (init pL368), (init pL368))) ∧ ptTest pL368 (runFrom pL368 (fmask pL368) (cmask pL368) (hmask pL368) 1 367 (true, (init pL368), (init pL368))) 368 184 false = true :=
  fin_run (runOK_init (prmOK_of_and L368_fin) true) (by decide) rfl L368_fin ptTest_fst
theorem H368_fin : (prmOK pH368 368 && ptTest pH368 (runFrom pH368 (fmask pH368) (cmask pH368) (hmask pH368) 1 367 (true, (init pH368), (init pH368))) 368 184 true) = true := by
  decide +kernel
theorem H368_ok : RunOK pH368 368 (runFrom pH368 (fmask pH368) (cmask pH368) (hmask pH368) 1 367 (true, (init pH368), (init pH368))) ∧ ptTest pH368 (runFrom pH368 (fmask pH368) (cmask pH368) (hmask pH368) 1 367 (true, (init pH368), (init pH368))) 368 184 true = true :=
  fin_run (runOK_init (prmOK_of_and H368_fin) true) (by decide) rfl H368_fin ptTest_fst
theorem I368_fin : (prmOK pI368 368 && intTest pI368 (runFrom pI368 (fmask pI368) (cmask pI368) (hmask pI368) 1 367 (true, (init pI368), (init pI368))) 368 13 true) = true := by
  decide +kernel
theorem I368_ok : RunOK pI368 368 (runFrom pI368 (fmask pI368) (cmask pI368) (hmask pI368) 1 367 (true, (init pI368), (init pI368))) ∧ intTest pI368 (runFrom pI368 (fmask pI368) (cmask pI368) (hmask pI368) 1 367 (true, (init pI368), (init pI368))) 368 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I368_fin) true) (by decide) rfl I368_fin intTest_fst
theorem link368 : linkOK pL368 pH368 pI368 = true := by decide +kernel
theorem cvx368 : ConvexBetweenHumps 368 :=
  cvx_of L368_ok H368_ok I368_ok link368 (by decide)
theorem cenlink368 : cenLinkOK pI368 368 = true := by decide +kernel
theorem cen368 : CenterUniqueMin 368 ∧ DipHyp 368 ∧ OnePointHyps 368 :=
  cen_of L368_ok H368_ok I368_ok link368 cenlink368

/-! ### `N = 369` -/

def pL369 : Prm := ⟨67, 31, 33, 371, 11, 18446744073709551616, 373831704414350701, 373831704414350701⟩
def pH369 : Prm := ⟨67, 31, 33, 371, 11, 18446744073709551616, 373840500507372909, 373840500507372909⟩
def pI369 : Prm := ⟨59, 28, 28, 371, 11, 18446744073709551616, 373831704414350701, 373840500507372909⟩
theorem L369_fin : (prmOK pL369 369 && ptTest pL369 (runFrom pL369 (fmask pL369) (cmask pL369) (hmask pL369) 1 368 (true, (init pL369), (init pL369))) 369 185 false) = true := by
  decide +kernel
theorem L369_ok : RunOK pL369 369 (runFrom pL369 (fmask pL369) (cmask pL369) (hmask pL369) 1 368 (true, (init pL369), (init pL369))) ∧ ptTest pL369 (runFrom pL369 (fmask pL369) (cmask pL369) (hmask pL369) 1 368 (true, (init pL369), (init pL369))) 369 185 false = true :=
  fin_run (runOK_init (prmOK_of_and L369_fin) true) (by decide) rfl L369_fin ptTest_fst
theorem H369_fin : (prmOK pH369 369 && ptTest pH369 (runFrom pH369 (fmask pH369) (cmask pH369) (hmask pH369) 1 368 (true, (init pH369), (init pH369))) 369 185 true) = true := by
  decide +kernel
theorem H369_ok : RunOK pH369 369 (runFrom pH369 (fmask pH369) (cmask pH369) (hmask pH369) 1 368 (true, (init pH369), (init pH369))) ∧ ptTest pH369 (runFrom pH369 (fmask pH369) (cmask pH369) (hmask pH369) 1 368 (true, (init pH369), (init pH369))) 369 185 true = true :=
  fin_run (runOK_init (prmOK_of_and H369_fin) true) (by decide) rfl H369_fin ptTest_fst
theorem I369_fin : (prmOK pI369 369 && intTest pI369 (runFrom pI369 (fmask pI369) (cmask pI369) (hmask pI369) 1 368 (true, (init pI369), (init pI369))) 369 13 false) = true := by
  decide +kernel
theorem I369_ok : RunOK pI369 369 (runFrom pI369 (fmask pI369) (cmask pI369) (hmask pI369) 1 368 (true, (init pI369), (init pI369))) ∧ intTest pI369 (runFrom pI369 (fmask pI369) (cmask pI369) (hmask pI369) 1 368 (true, (init pI369), (init pI369))) 369 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I369_fin) true) (by decide) rfl I369_fin intTest_fst
theorem link369 : linkOK pL369 pH369 pI369 = true := by decide +kernel
theorem cvx369 : ConvexBetweenHumps 369 :=
  cvx_of L369_ok H369_ok I369_ok link369 (by decide)

/-! ### `N = 370` -/

def pL370 : Prm := ⟨67, 31, 33, 372, 11, 18446744073709551616, 373075190566753734, 373075190566753734⟩
def pH370 : Prm := ⟨67, 31, 33, 372, 11, 18446744073709551616, 373083986659775942, 373083986659775942⟩
def pI370 : Prm := ⟨59, 28, 28, 372, 11, 18446744073709551616, 373075190566753734, 373083986659775942⟩
theorem L370_fin : (prmOK pL370 370 && ptTest pL370 (runFrom pL370 (fmask pL370) (cmask pL370) (hmask pL370) 1 369 (true, (init pL370), (init pL370))) 370 185 false) = true := by
  decide +kernel
theorem L370_ok : RunOK pL370 370 (runFrom pL370 (fmask pL370) (cmask pL370) (hmask pL370) 1 369 (true, (init pL370), (init pL370))) ∧ ptTest pL370 (runFrom pL370 (fmask pL370) (cmask pL370) (hmask pL370) 1 369 (true, (init pL370), (init pL370))) 370 185 false = true :=
  fin_run (runOK_init (prmOK_of_and L370_fin) true) (by decide) rfl L370_fin ptTest_fst
theorem H370_fin : (prmOK pH370 370 && ptTest pH370 (runFrom pH370 (fmask pH370) (cmask pH370) (hmask pH370) 1 369 (true, (init pH370), (init pH370))) 370 185 true) = true := by
  decide +kernel
theorem H370_ok : RunOK pH370 370 (runFrom pH370 (fmask pH370) (cmask pH370) (hmask pH370) 1 369 (true, (init pH370), (init pH370))) ∧ ptTest pH370 (runFrom pH370 (fmask pH370) (cmask pH370) (hmask pH370) 1 369 (true, (init pH370), (init pH370))) 370 185 true = true :=
  fin_run (runOK_init (prmOK_of_and H370_fin) true) (by decide) rfl H370_fin ptTest_fst
theorem I370_fin : (prmOK pI370 370 && intTest pI370 (runFrom pI370 (fmask pI370) (cmask pI370) (hmask pI370) 1 369 (true, (init pI370), (init pI370))) 370 13 true) = true := by
  decide +kernel
theorem I370_ok : RunOK pI370 370 (runFrom pI370 (fmask pI370) (cmask pI370) (hmask pI370) 1 369 (true, (init pI370), (init pI370))) ∧ intTest pI370 (runFrom pI370 (fmask pI370) (cmask pI370) (hmask pI370) 1 369 (true, (init pI370), (init pI370))) 370 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I370_fin) true) (by decide) rfl I370_fin intTest_fst
theorem link370 : linkOK pL370 pH370 pI370 = true := by decide +kernel
theorem cvx370 : ConvexBetweenHumps 370 :=
  cvx_of L370_ok H370_ok I370_ok link370 (by decide)
theorem cenlink370 : cenLinkOK pI370 370 = true := by decide +kernel
theorem cen370 : CenterUniqueMin 370 ∧ DipHyp 370 ∧ OnePointHyps 370 :=
  cen_of L370_ok H370_ok I370_ok link370 cenlink370

/-! ### `N = 371` -/

def pL371 : Prm := ⟨67, 31, 33, 373, 11, 18446744073709551616, 372319696606967418, 372319696606967418⟩
def pH371 : Prm := ⟨67, 31, 33, 373, 11, 18446744073709551616, 372328492699989626, 372328492699989626⟩
def pI371 : Prm := ⟨58, 29, 26, 373, 11, 18446744073709551616, 372319696606967418, 372328492699989626⟩
theorem L371_fin : (prmOK pL371 371 && ptTest pL371 (runFrom pL371 (fmask pL371) (cmask pL371) (hmask pL371) 1 370 (true, (init pL371), (init pL371))) 371 186 false) = true := by
  decide +kernel
theorem L371_ok : RunOK pL371 371 (runFrom pL371 (fmask pL371) (cmask pL371) (hmask pL371) 1 370 (true, (init pL371), (init pL371))) ∧ ptTest pL371 (runFrom pL371 (fmask pL371) (cmask pL371) (hmask pL371) 1 370 (true, (init pL371), (init pL371))) 371 186 false = true :=
  fin_run (runOK_init (prmOK_of_and L371_fin) true) (by decide) rfl L371_fin ptTest_fst
theorem H371_fin : (prmOK pH371 371 && ptTest pH371 (runFrom pH371 (fmask pH371) (cmask pH371) (hmask pH371) 1 370 (true, (init pH371), (init pH371))) 371 186 true) = true := by
  decide +kernel
theorem H371_ok : RunOK pH371 371 (runFrom pH371 (fmask pH371) (cmask pH371) (hmask pH371) 1 370 (true, (init pH371), (init pH371))) ∧ ptTest pH371 (runFrom pH371 (fmask pH371) (cmask pH371) (hmask pH371) 1 370 (true, (init pH371), (init pH371))) 371 186 true = true :=
  fin_run (runOK_init (prmOK_of_and H371_fin) true) (by decide) rfl H371_fin ptTest_fst
theorem I371_fin : (prmOK pI371 371 && intTest pI371 (runFrom pI371 (fmask pI371) (cmask pI371) (hmask pI371) 1 370 (true, (init pI371), (init pI371))) 371 13 false) = true := by
  decide +kernel
theorem I371_ok : RunOK pI371 371 (runFrom pI371 (fmask pI371) (cmask pI371) (hmask pI371) 1 370 (true, (init pI371), (init pI371))) ∧ intTest pI371 (runFrom pI371 (fmask pI371) (cmask pI371) (hmask pI371) 1 370 (true, (init pI371), (init pI371))) 371 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I371_fin) true) (by decide) rfl I371_fin intTest_fst
theorem link371 : linkOK pL371 pH371 pI371 = true := by decide +kernel
theorem cvx371 : ConvexBetweenHumps 371 :=
  cvx_of L371_ok H371_ok I371_ok link371 (by decide)

/-! ### `N = 372` -/

def pL372 : Prm := ⟨67, 31, 33, 374, 11, 18446744073709551616, 371569973338477225, 371569973338477225⟩
def pH372 : Prm := ⟨67, 31, 33, 374, 11, 18446744073709551616, 371578769431499433, 371578769431499433⟩
def pI372 : Prm := ⟨58, 28, 27, 374, 11, 18446744073709551616, 371569973338477225, 371578769431499433⟩
theorem L372_fin : (prmOK pL372 372 && ptTest pL372 (runFrom pL372 (fmask pL372) (cmask pL372) (hmask pL372) 1 371 (true, (init pL372), (init pL372))) 372 186 false) = true := by
  decide +kernel
theorem L372_ok : RunOK pL372 372 (runFrom pL372 (fmask pL372) (cmask pL372) (hmask pL372) 1 371 (true, (init pL372), (init pL372))) ∧ ptTest pL372 (runFrom pL372 (fmask pL372) (cmask pL372) (hmask pL372) 1 371 (true, (init pL372), (init pL372))) 372 186 false = true :=
  fin_run (runOK_init (prmOK_of_and L372_fin) true) (by decide) rfl L372_fin ptTest_fst
theorem H372_fin : (prmOK pH372 372 && ptTest pH372 (runFrom pH372 (fmask pH372) (cmask pH372) (hmask pH372) 1 371 (true, (init pH372), (init pH372))) 372 186 true) = true := by
  decide +kernel
theorem H372_ok : RunOK pH372 372 (runFrom pH372 (fmask pH372) (cmask pH372) (hmask pH372) 1 371 (true, (init pH372), (init pH372))) ∧ ptTest pH372 (runFrom pH372 (fmask pH372) (cmask pH372) (hmask pH372) 1 371 (true, (init pH372), (init pH372))) 372 186 true = true :=
  fin_run (runOK_init (prmOK_of_and H372_fin) true) (by decide) rfl H372_fin ptTest_fst
theorem I372_fin : (prmOK pI372 372 && intTest pI372 (runFrom pI372 (fmask pI372) (cmask pI372) (hmask pI372) 1 371 (true, (init pI372), (init pI372))) 372 13 true) = true := by
  decide +kernel
theorem I372_ok : RunOK pI372 372 (runFrom pI372 (fmask pI372) (cmask pI372) (hmask pI372) 1 371 (true, (init pI372), (init pI372))) ∧ intTest pI372 (runFrom pI372 (fmask pI372) (cmask pI372) (hmask pI372) 1 371 (true, (init pI372), (init pI372))) 372 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I372_fin) true) (by decide) rfl I372_fin intTest_fst
theorem link372 : linkOK pL372 pH372 pI372 = true := by decide +kernel
theorem cvx372 : ConvexBetweenHumps 372 :=
  cvx_of L372_ok H372_ok I372_ok link372 (by decide)
theorem cenlink372 : cenLinkOK pI372 372 = true := by decide +kernel
theorem cen372 : CenterUniqueMin 372 ∧ DipHyp 372 ∧ OnePointHyps 372 :=
  cen_of L372_ok H372_ok I372_ok link372 cenlink372

/-! ### `N = 373` -/

def pL373 : Prm := ⟨67, 31, 33, 375, 11, 18446744073709551616, 370821260936103901, 370821260936103901⟩
def pH373 : Prm := ⟨67, 31, 33, 375, 11, 18446744073709551616, 370830057029126109, 370830057029126109⟩
def pI373 : Prm := ⟨58, 28, 27, 375, 11, 18446744073709551616, 370821260936103901, 370830057029126109⟩
theorem L373_fin : (prmOK pL373 373 && ptTest pL373 (runFrom pL373 (fmask pL373) (cmask pL373) (hmask pL373) 1 372 (true, (init pL373), (init pL373))) 373 187 false) = true := by
  decide +kernel
theorem L373_ok : RunOK pL373 373 (runFrom pL373 (fmask pL373) (cmask pL373) (hmask pL373) 1 372 (true, (init pL373), (init pL373))) ∧ ptTest pL373 (runFrom pL373 (fmask pL373) (cmask pL373) (hmask pL373) 1 372 (true, (init pL373), (init pL373))) 373 187 false = true :=
  fin_run (runOK_init (prmOK_of_and L373_fin) true) (by decide) rfl L373_fin ptTest_fst
theorem H373_fin : (prmOK pH373 373 && ptTest pH373 (runFrom pH373 (fmask pH373) (cmask pH373) (hmask pH373) 1 372 (true, (init pH373), (init pH373))) 373 187 true) = true := by
  decide +kernel
theorem H373_ok : RunOK pH373 373 (runFrom pH373 (fmask pH373) (cmask pH373) (hmask pH373) 1 372 (true, (init pH373), (init pH373))) ∧ ptTest pH373 (runFrom pH373 (fmask pH373) (cmask pH373) (hmask pH373) 1 372 (true, (init pH373), (init pH373))) 373 187 true = true :=
  fin_run (runOK_init (prmOK_of_and H373_fin) true) (by decide) rfl H373_fin ptTest_fst
theorem I373_fin : (prmOK pI373 373 && intTest pI373 (runFrom pI373 (fmask pI373) (cmask pI373) (hmask pI373) 1 372 (true, (init pI373), (init pI373))) 373 13 false) = true := by
  decide +kernel
theorem I373_ok : RunOK pI373 373 (runFrom pI373 (fmask pI373) (cmask pI373) (hmask pI373) 1 372 (true, (init pI373), (init pI373))) ∧ intTest pI373 (runFrom pI373 (fmask pI373) (cmask pI373) (hmask pI373) 1 372 (true, (init pI373), (init pI373))) 373 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I373_fin) true) (by decide) rfl I373_fin intTest_fst
theorem link373 : linkOK pL373 pH373 pI373 = true := by decide +kernel
theorem cvx373 : ConvexBetweenHumps 373 :=
  cvx_of L373_ok H373_ok I373_ok link373 (by decide)

/-! ### `N = 374` -/

def pL374 : Prm := ⟨67, 31, 33, 376, 11, 18446744073709551616, 370078233319000716, 370078233319000716⟩
def pH374 : Prm := ⟨67, 31, 33, 376, 11, 18446744073709551616, 370087029412022924, 370087029412022924⟩
def pI374 : Prm := ⟨58, 28, 27, 376, 11, 18446744073709551616, 370078233319000716, 370087029412022924⟩
theorem L374_fin : (prmOK pL374 374 && ptTest pL374 (runFrom pL374 (fmask pL374) (cmask pL374) (hmask pL374) 1 373 (true, (init pL374), (init pL374))) 374 187 false) = true := by
  decide +kernel
theorem L374_ok : RunOK pL374 374 (runFrom pL374 (fmask pL374) (cmask pL374) (hmask pL374) 1 373 (true, (init pL374), (init pL374))) ∧ ptTest pL374 (runFrom pL374 (fmask pL374) (cmask pL374) (hmask pL374) 1 373 (true, (init pL374), (init pL374))) 374 187 false = true :=
  fin_run (runOK_init (prmOK_of_and L374_fin) true) (by decide) rfl L374_fin ptTest_fst
theorem H374_fin : (prmOK pH374 374 && ptTest pH374 (runFrom pH374 (fmask pH374) (cmask pH374) (hmask pH374) 1 373 (true, (init pH374), (init pH374))) 374 187 true) = true := by
  decide +kernel
theorem H374_ok : RunOK pH374 374 (runFrom pH374 (fmask pH374) (cmask pH374) (hmask pH374) 1 373 (true, (init pH374), (init pH374))) ∧ ptTest pH374 (runFrom pH374 (fmask pH374) (cmask pH374) (hmask pH374) 1 373 (true, (init pH374), (init pH374))) 374 187 true = true :=
  fin_run (runOK_init (prmOK_of_and H374_fin) true) (by decide) rfl H374_fin ptTest_fst
theorem I374_fin : (prmOK pI374 374 && intTest pI374 (runFrom pI374 (fmask pI374) (cmask pI374) (hmask pI374) 1 373 (true, (init pI374), (init pI374))) 374 13 true) = true := by
  decide +kernel
theorem I374_ok : RunOK pI374 374 (runFrom pI374 (fmask pI374) (cmask pI374) (hmask pI374) 1 373 (true, (init pI374), (init pI374))) ∧ intTest pI374 (runFrom pI374 (fmask pI374) (cmask pI374) (hmask pI374) 1 373 (true, (init pI374), (init pI374))) 374 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I374_fin) true) (by decide) rfl I374_fin intTest_fst
theorem link374 : linkOK pL374 pH374 pI374 = true := by decide +kernel
theorem cvx374 : ConvexBetweenHumps 374 :=
  cvx_of L374_ok H374_ok I374_ok link374 (by decide)
theorem cenlink374 : cenLinkOK pI374 374 = true := by decide +kernel
theorem cen374 : CenterUniqueMin 374 ∧ DipHyp 374 ∧ OnePointHyps 374 :=
  cen_of L374_ok H374_ok I374_ok link374 cenlink374

/-! ### `N = 375` -/

def pL375 : Prm := ⟨67, 31, 33, 377, 11, 18446744073709551616, 369336207629072709, 369336207629072709⟩
def pH375 : Prm := ⟨67, 31, 33, 377, 11, 18446744073709551616, 369345003722094917, 369345003722094917⟩
def pI375 : Prm := ⟨58, 28, 27, 377, 11, 18446744073709551616, 369336207629072709, 369345003722094917⟩
theorem L375_fin : (prmOK pL375 375 && ptTest pL375 (runFrom pL375 (fmask pL375) (cmask pL375) (hmask pL375) 1 374 (true, (init pL375), (init pL375))) 375 188 false) = true := by
  decide +kernel
theorem L375_ok : RunOK pL375 375 (runFrom pL375 (fmask pL375) (cmask pL375) (hmask pL375) 1 374 (true, (init pL375), (init pL375))) ∧ ptTest pL375 (runFrom pL375 (fmask pL375) (cmask pL375) (hmask pL375) 1 374 (true, (init pL375), (init pL375))) 375 188 false = true :=
  fin_run (runOK_init (prmOK_of_and L375_fin) true) (by decide) rfl L375_fin ptTest_fst
theorem H375_fin : (prmOK pH375 375 && ptTest pH375 (runFrom pH375 (fmask pH375) (cmask pH375) (hmask pH375) 1 374 (true, (init pH375), (init pH375))) 375 188 true) = true := by
  decide +kernel
theorem H375_ok : RunOK pH375 375 (runFrom pH375 (fmask pH375) (cmask pH375) (hmask pH375) 1 374 (true, (init pH375), (init pH375))) ∧ ptTest pH375 (runFrom pH375 (fmask pH375) (cmask pH375) (hmask pH375) 1 374 (true, (init pH375), (init pH375))) 375 188 true = true :=
  fin_run (runOK_init (prmOK_of_and H375_fin) true) (by decide) rfl H375_fin ptTest_fst
theorem I375_fin : (prmOK pI375 375 && intTest pI375 (runFrom pI375 (fmask pI375) (cmask pI375) (hmask pI375) 1 374 (true, (init pI375), (init pI375))) 375 13 false) = true := by
  decide +kernel
theorem I375_ok : RunOK pI375 375 (runFrom pI375 (fmask pI375) (cmask pI375) (hmask pI375) 1 374 (true, (init pI375), (init pI375))) ∧ intTest pI375 (runFrom pI375 (fmask pI375) (cmask pI375) (hmask pI375) 1 374 (true, (init pI375), (init pI375))) 375 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I375_fin) true) (by decide) rfl I375_fin intTest_fst
theorem link375 : linkOK pL375 pH375 pI375 = true := by decide +kernel
theorem cvx375 : ConvexBetweenHumps 375 :=
  cvx_of L375_ok H375_ok I375_ok link375 (by decide)

/-! ### `N = 376` -/

def pL376 : Prm := ⟨68, 32, 33, 378, 11, 18446744073709551616, 368599782538455512, 368599782538455512⟩
def pH376 : Prm := ⟨67, 31, 33, 378, 11, 18446744073709551616, 368608578631477720, 368608578631477720⟩
def pI376 : Prm := ⟨58, 28, 27, 378, 11, 18446744073709551616, 368599782538455512, 368608578631477720⟩
theorem L376_fin : (prmOK pL376 376 && ptTest pL376 (runFrom pL376 (fmask pL376) (cmask pL376) (hmask pL376) 1 375 (true, (init pL376), (init pL376))) 376 188 false) = true := by
  decide +kernel
theorem L376_ok : RunOK pL376 376 (runFrom pL376 (fmask pL376) (cmask pL376) (hmask pL376) 1 375 (true, (init pL376), (init pL376))) ∧ ptTest pL376 (runFrom pL376 (fmask pL376) (cmask pL376) (hmask pL376) 1 375 (true, (init pL376), (init pL376))) 376 188 false = true :=
  fin_run (runOK_init (prmOK_of_and L376_fin) true) (by decide) rfl L376_fin ptTest_fst
theorem H376_fin : (prmOK pH376 376 && ptTest pH376 (runFrom pH376 (fmask pH376) (cmask pH376) (hmask pH376) 1 375 (true, (init pH376), (init pH376))) 376 188 true) = true := by
  decide +kernel
theorem H376_ok : RunOK pH376 376 (runFrom pH376 (fmask pH376) (cmask pH376) (hmask pH376) 1 375 (true, (init pH376), (init pH376))) ∧ ptTest pH376 (runFrom pH376 (fmask pH376) (cmask pH376) (hmask pH376) 1 375 (true, (init pH376), (init pH376))) 376 188 true = true :=
  fin_run (runOK_init (prmOK_of_and H376_fin) true) (by decide) rfl H376_fin ptTest_fst
theorem I376_fin : (prmOK pI376 376 && intTest pI376 (runFrom pI376 (fmask pI376) (cmask pI376) (hmask pI376) 1 375 (true, (init pI376), (init pI376))) 376 13 true) = true := by
  decide +kernel
theorem I376_ok : RunOK pI376 376 (runFrom pI376 (fmask pI376) (cmask pI376) (hmask pI376) 1 375 (true, (init pI376), (init pI376))) ∧ intTest pI376 (runFrom pI376 (fmask pI376) (cmask pI376) (hmask pI376) 1 375 (true, (init pI376), (init pI376))) 376 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I376_fin) true) (by decide) rfl I376_fin intTest_fst
theorem link376 : linkOK pL376 pH376 pI376 = true := by decide +kernel
theorem cvx376 : ConvexBetweenHumps 376 :=
  cvx_of L376_ok H376_ok I376_ok link376 (by decide)
theorem cenlink376 : cenLinkOK pI376 376 = true := by decide +kernel
theorem cen376 : CenterUniqueMin 376 ∧ DipHyp 376 ∧ OnePointHyps 376 :=
  cen_of L376_ok H376_ok I376_ok link376 cenlink376

/-! ### `N = 377` -/

def pL377 : Prm := ⟨68, 32, 33, 379, 11, 18446744073709551616, 367864350518713216, 367864350518713216⟩
def pH377 : Prm := ⟨67, 31, 33, 379, 11, 18446744073709551616, 367873146611735424, 367873146611735424⟩
def pI377 : Prm := ⟨58, 28, 27, 379, 11, 18446744073709551616, 367864350518713216, 367873146611735424⟩
theorem L377_fin : (prmOK pL377 377 && ptTest pL377 (runFrom pL377 (fmask pL377) (cmask pL377) (hmask pL377) 1 376 (true, (init pL377), (init pL377))) 377 189 false) = true := by
  decide +kernel
theorem L377_ok : RunOK pL377 377 (runFrom pL377 (fmask pL377) (cmask pL377) (hmask pL377) 1 376 (true, (init pL377), (init pL377))) ∧ ptTest pL377 (runFrom pL377 (fmask pL377) (cmask pL377) (hmask pL377) 1 376 (true, (init pL377), (init pL377))) 377 189 false = true :=
  fin_run (runOK_init (prmOK_of_and L377_fin) true) (by decide) rfl L377_fin ptTest_fst
theorem H377_fin : (prmOK pH377 377 && ptTest pH377 (runFrom pH377 (fmask pH377) (cmask pH377) (hmask pH377) 1 376 (true, (init pH377), (init pH377))) 377 189 true) = true := by
  decide +kernel
theorem H377_ok : RunOK pH377 377 (runFrom pH377 (fmask pH377) (cmask pH377) (hmask pH377) 1 376 (true, (init pH377), (init pH377))) ∧ ptTest pH377 (runFrom pH377 (fmask pH377) (cmask pH377) (hmask pH377) 1 376 (true, (init pH377), (init pH377))) 377 189 true = true :=
  fin_run (runOK_init (prmOK_of_and H377_fin) true) (by decide) rfl H377_fin ptTest_fst
theorem I377_fin : (prmOK pI377 377 && intTest pI377 (runFrom pI377 (fmask pI377) (cmask pI377) (hmask pI377) 1 376 (true, (init pI377), (init pI377))) 377 13 false) = true := by
  decide +kernel
theorem I377_ok : RunOK pI377 377 (runFrom pI377 (fmask pI377) (cmask pI377) (hmask pI377) 1 376 (true, (init pI377), (init pI377))) ∧ intTest pI377 (runFrom pI377 (fmask pI377) (cmask pI377) (hmask pI377) 1 376 (true, (init pI377), (init pI377))) 377 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I377_fin) true) (by decide) rfl I377_fin intTest_fst
theorem link377 : linkOK pL377 pH377 pI377 = true := by decide +kernel
theorem cvx377 : ConvexBetweenHumps 377 :=
  cvx_of L377_ok H377_ok I377_ok link377 (by decide)

/-! ### `N = 378` -/

def pL378 : Prm := ⟨68, 32, 33, 380, 11, 18446744073709551616, 367134436589112987, 367134436589112987⟩
def pH378 : Prm := ⟨67, 31, 33, 380, 11, 18446744073709551616, 367143232682135195, 367143232682135195⟩
def pI378 : Prm := ⟨58, 28, 27, 380, 11, 18446744073709551616, 367134436589112987, 367143232682135195⟩
theorem L378_fin : (prmOK pL378 378 && ptTest pL378 (runFrom pL378 (fmask pL378) (cmask pL378) (hmask pL378) 1 377 (true, (init pL378), (init pL378))) 378 189 false) = true := by
  decide +kernel
theorem L378_ok : RunOK pL378 378 (runFrom pL378 (fmask pL378) (cmask pL378) (hmask pL378) 1 377 (true, (init pL378), (init pL378))) ∧ ptTest pL378 (runFrom pL378 (fmask pL378) (cmask pL378) (hmask pL378) 1 377 (true, (init pL378), (init pL378))) 378 189 false = true :=
  fin_run (runOK_init (prmOK_of_and L378_fin) true) (by decide) rfl L378_fin ptTest_fst
theorem H378_fin : (prmOK pH378 378 && ptTest pH378 (runFrom pH378 (fmask pH378) (cmask pH378) (hmask pH378) 1 377 (true, (init pH378), (init pH378))) 378 189 true) = true := by
  decide +kernel
theorem H378_ok : RunOK pH378 378 (runFrom pH378 (fmask pH378) (cmask pH378) (hmask pH378) 1 377 (true, (init pH378), (init pH378))) ∧ ptTest pH378 (runFrom pH378 (fmask pH378) (cmask pH378) (hmask pH378) 1 377 (true, (init pH378), (init pH378))) 378 189 true = true :=
  fin_run (runOK_init (prmOK_of_and H378_fin) true) (by decide) rfl H378_fin ptTest_fst
theorem I378_fin : (prmOK pI378 378 && intTest pI378 (runFrom pI378 (fmask pI378) (cmask pI378) (hmask pI378) 1 377 (true, (init pI378), (init pI378))) 378 13 true) = true := by
  decide +kernel
theorem I378_ok : RunOK pI378 378 (runFrom pI378 (fmask pI378) (cmask pI378) (hmask pI378) 1 377 (true, (init pI378), (init pI378))) ∧ intTest pI378 (runFrom pI378 (fmask pI378) (cmask pI378) (hmask pI378) 1 377 (true, (init pI378), (init pI378))) 378 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I378_fin) true) (by decide) rfl I378_fin intTest_fst
theorem link378 : linkOK pL378 pH378 pI378 = true := by decide +kernel
theorem cvx378 : ConvexBetweenHumps 378 :=
  cvx_of L378_ok H378_ok I378_ok link378 (by decide)
theorem cenlink378 : cenLinkOK pI378 378 = true := by decide +kernel
theorem cen378 : CenterUniqueMin 378 ∧ DipHyp 378 ∧ OnePointHyps 378 :=
  cen_of L378_ok H378_ok I378_ok link378 cenlink378

/-! ### `N = 379` -/

def pL379 : Prm := ⟨67, 31, 33, 381, 11, 18446744073709551616, 366405506956673455, 366405506956673455⟩
def pH379 : Prm := ⟨68, 32, 33, 381, 11, 18446744073709551616, 366414303049695663, 366414303049695663⟩
def pI379 : Prm := ⟨58, 28, 27, 381, 11, 18446744073709551616, 366405506956673455, 366414303049695663⟩
theorem L379_fin : (prmOK pL379 379 && ptTest pL379 (runFrom pL379 (fmask pL379) (cmask pL379) (hmask pL379) 1 378 (true, (init pL379), (init pL379))) 379 190 false) = true := by
  decide +kernel
theorem L379_ok : RunOK pL379 379 (runFrom pL379 (fmask pL379) (cmask pL379) (hmask pL379) 1 378 (true, (init pL379), (init pL379))) ∧ ptTest pL379 (runFrom pL379 (fmask pL379) (cmask pL379) (hmask pL379) 1 378 (true, (init pL379), (init pL379))) 379 190 false = true :=
  fin_run (runOK_init (prmOK_of_and L379_fin) true) (by decide) rfl L379_fin ptTest_fst
theorem H379_fin : (prmOK pH379 379 && ptTest pH379 (runFrom pH379 (fmask pH379) (cmask pH379) (hmask pH379) 1 378 (true, (init pH379), (init pH379))) 379 190 true) = true := by
  decide +kernel
theorem H379_ok : RunOK pH379 379 (runFrom pH379 (fmask pH379) (cmask pH379) (hmask pH379) 1 378 (true, (init pH379), (init pH379))) ∧ ptTest pH379 (runFrom pH379 (fmask pH379) (cmask pH379) (hmask pH379) 1 378 (true, (init pH379), (init pH379))) 379 190 true = true :=
  fin_run (runOK_init (prmOK_of_and H379_fin) true) (by decide) rfl H379_fin ptTest_fst
theorem I379_fin : (prmOK pI379 379 && intTest pI379 (runFrom pI379 (fmask pI379) (cmask pI379) (hmask pI379) 1 378 (true, (init pI379), (init pI379))) 379 13 false) = true := by
  decide +kernel
theorem I379_ok : RunOK pI379 379 (runFrom pI379 (fmask pI379) (cmask pI379) (hmask pI379) 1 378 (true, (init pI379), (init pI379))) ∧ intTest pI379 (runFrom pI379 (fmask pI379) (cmask pI379) (hmask pI379) 1 378 (true, (init pI379), (init pI379))) 379 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I379_fin) true) (by decide) rfl I379_fin intTest_fst
theorem link379 : linkOK pL379 pH379 pI379 = true := by decide +kernel
theorem cvx379 : ConvexBetweenHumps 379 :=
  cvx_of L379_ok H379_ok I379_ok link379 (by decide)

/-! ### `N = 380` -/

def pL380 : Prm := ⟨68, 32, 33, 382, 11, 18446744073709551616, 365682014540234410, 365682014540234410⟩
def pH380 : Prm := ⟨68, 32, 33, 382, 11, 18446744073709551616, 365690810633256618, 365690810633256618⟩
def pI380 : Prm := ⟨58, 28, 27, 382, 11, 18446744073709551616, 365682014540234410, 365690810633256618⟩
theorem L380_fin : (prmOK pL380 380 && ptTest pL380 (runFrom pL380 (fmask pL380) (cmask pL380) (hmask pL380) 1 379 (true, (init pL380), (init pL380))) 380 190 false) = true := by
  decide +kernel
theorem L380_ok : RunOK pL380 380 (runFrom pL380 (fmask pL380) (cmask pL380) (hmask pL380) 1 379 (true, (init pL380), (init pL380))) ∧ ptTest pL380 (runFrom pL380 (fmask pL380) (cmask pL380) (hmask pL380) 1 379 (true, (init pL380), (init pL380))) 380 190 false = true :=
  fin_run (runOK_init (prmOK_of_and L380_fin) true) (by decide) rfl L380_fin ptTest_fst
theorem H380_fin : (prmOK pH380 380 && ptTest pH380 (runFrom pH380 (fmask pH380) (cmask pH380) (hmask pH380) 1 379 (true, (init pH380), (init pH380))) 380 190 true) = true := by
  decide +kernel
theorem H380_ok : RunOK pH380 380 (runFrom pH380 (fmask pH380) (cmask pH380) (hmask pH380) 1 379 (true, (init pH380), (init pH380))) ∧ ptTest pH380 (runFrom pH380 (fmask pH380) (cmask pH380) (hmask pH380) 1 379 (true, (init pH380), (init pH380))) 380 190 true = true :=
  fin_run (runOK_init (prmOK_of_and H380_fin) true) (by decide) rfl H380_fin ptTest_fst
theorem I380_fin : (prmOK pI380 380 && intTest pI380 (runFrom pI380 (fmask pI380) (cmask pI380) (hmask pI380) 1 379 (true, (init pI380), (init pI380))) 380 13 true) = true := by
  decide +kernel
theorem I380_ok : RunOK pI380 380 (runFrom pI380 (fmask pI380) (cmask pI380) (hmask pI380) 1 379 (true, (init pI380), (init pI380))) ∧ intTest pI380 (runFrom pI380 (fmask pI380) (cmask pI380) (hmask pI380) 1 379 (true, (init pI380), (init pI380))) 380 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I380_fin) true) (by decide) rfl I380_fin intTest_fst
theorem link380 : linkOK pL380 pH380 pI380 = true := by decide +kernel
theorem cvx380 : ConvexBetweenHumps 380 :=
  cvx_of L380_ok H380_ok I380_ok link380 (by decide)
theorem cenlink380 : cenLinkOK pI380 380 = true := by decide +kernel
theorem cen380 : CenterUniqueMin 380 ∧ DipHyp 380 ∧ OnePointHyps 380 :=
  cen_of L380_ok H380_ok I380_ok link380 cenlink380

/-! ### `N = 381` -/

def pL381 : Prm := ⟨68, 32, 33, 383, 11, 18446744073709551616, 364959497729569678, 364959497729569678⟩
def pH381 : Prm := ⟨67, 31, 33, 383, 11, 18446744073709551616, 364968293822591886, 364968293822591886⟩
def pI381 : Prm := ⟨58, 28, 27, 383, 11, 18446744073709551616, 364959497729569678, 364968293822591886⟩
theorem L381_fin : (prmOK pL381 381 && ptTest pL381 (runFrom pL381 (fmask pL381) (cmask pL381) (hmask pL381) 1 380 (true, (init pL381), (init pL381))) 381 191 false) = true := by
  decide +kernel
theorem L381_ok : RunOK pL381 381 (runFrom pL381 (fmask pL381) (cmask pL381) (hmask pL381) 1 380 (true, (init pL381), (init pL381))) ∧ ptTest pL381 (runFrom pL381 (fmask pL381) (cmask pL381) (hmask pL381) 1 380 (true, (init pL381), (init pL381))) 381 191 false = true :=
  fin_run (runOK_init (prmOK_of_and L381_fin) true) (by decide) rfl L381_fin ptTest_fst
theorem H381_fin : (prmOK pH381 381 && ptTest pH381 (runFrom pH381 (fmask pH381) (cmask pH381) (hmask pH381) 1 380 (true, (init pH381), (init pH381))) 381 191 true) = true := by
  decide +kernel
theorem H381_ok : RunOK pH381 381 (runFrom pH381 (fmask pH381) (cmask pH381) (hmask pH381) 1 380 (true, (init pH381), (init pH381))) ∧ ptTest pH381 (runFrom pH381 (fmask pH381) (cmask pH381) (hmask pH381) 1 380 (true, (init pH381), (init pH381))) 381 191 true = true :=
  fin_run (runOK_init (prmOK_of_and H381_fin) true) (by decide) rfl H381_fin ptTest_fst
theorem I381_fin : (prmOK pI381 381 && intTest pI381 (runFrom pI381 (fmask pI381) (cmask pI381) (hmask pI381) 1 380 (true, (init pI381), (init pI381))) 381 13 false) = true := by
  decide +kernel
theorem I381_ok : RunOK pI381 381 (runFrom pI381 (fmask pI381) (cmask pI381) (hmask pI381) 1 380 (true, (init pI381), (init pI381))) ∧ intTest pI381 (runFrom pI381 (fmask pI381) (cmask pI381) (hmask pI381) 1 380 (true, (init pI381), (init pI381))) 381 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I381_fin) true) (by decide) rfl I381_fin intTest_fst
theorem link381 : linkOK pL381 pH381 pI381 = true := by decide +kernel
theorem cvx381 : ConvexBetweenHumps 381 :=
  cvx_of L381_ok H381_ok I381_ok link381 (by decide)

/-! ### `N = 382` -/

def pL382 : Prm := ⟨68, 32, 33, 384, 11, 18446744073709551616, 364242338855079049, 364242338855079049⟩
def pH382 : Prm := ⟨68, 32, 33, 384, 11, 18446744073709551616, 364251134948101257, 364251134948101257⟩
def pI382 : Prm := ⟨58, 28, 27, 384, 11, 18446744073709551616, 364242338855079049, 364251134948101257⟩
theorem L382_fin : (prmOK pL382 382 && ptTest pL382 (runFrom pL382 (fmask pL382) (cmask pL382) (hmask pL382) 1 381 (true, (init pL382), (init pL382))) 382 191 false) = true := by
  decide +kernel
theorem L382_ok : RunOK pL382 382 (runFrom pL382 (fmask pL382) (cmask pL382) (hmask pL382) 1 381 (true, (init pL382), (init pL382))) ∧ ptTest pL382 (runFrom pL382 (fmask pL382) (cmask pL382) (hmask pL382) 1 381 (true, (init pL382), (init pL382))) 382 191 false = true :=
  fin_run (runOK_init (prmOK_of_and L382_fin) true) (by decide) rfl L382_fin ptTest_fst
theorem H382_fin : (prmOK pH382 382 && ptTest pH382 (runFrom pH382 (fmask pH382) (cmask pH382) (hmask pH382) 1 381 (true, (init pH382), (init pH382))) 382 191 true) = true := by
  decide +kernel
theorem H382_ok : RunOK pH382 382 (runFrom pH382 (fmask pH382) (cmask pH382) (hmask pH382) 1 381 (true, (init pH382), (init pH382))) ∧ ptTest pH382 (runFrom pH382 (fmask pH382) (cmask pH382) (hmask pH382) 1 381 (true, (init pH382), (init pH382))) 382 191 true = true :=
  fin_run (runOK_init (prmOK_of_and H382_fin) true) (by decide) rfl H382_fin ptTest_fst
theorem I382_fin : (prmOK pI382 382 && intTest pI382 (runFrom pI382 (fmask pI382) (cmask pI382) (hmask pI382) 1 381 (true, (init pI382), (init pI382))) 382 13 true) = true := by
  decide +kernel
theorem I382_ok : RunOK pI382 382 (runFrom pI382 (fmask pI382) (cmask pI382) (hmask pI382) 1 381 (true, (init pI382), (init pI382))) ∧ intTest pI382 (runFrom pI382 (fmask pI382) (cmask pI382) (hmask pI382) 1 381 (true, (init pI382), (init pI382))) 382 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I382_fin) true) (by decide) rfl I382_fin intTest_fst
theorem link382 : linkOK pL382 pH382 pI382 = true := by decide +kernel
theorem cvx382 : ConvexBetweenHumps 382 :=
  cvx_of L382_ok H382_ok I382_ok link382 (by decide)
theorem cenlink382 : cenLinkOK pI382 382 = true := by decide +kernel
theorem cen382 : CenterUniqueMin 382 ∧ DipHyp 382 ∧ OnePointHyps 382 :=
  cen_of L382_ok H382_ok I382_ok link382 cenlink382

/-! ### `N = 383` -/

def pL383 : Prm := ⟨68, 32, 33, 385, 11, 18446744073709551616, 363526146977193486, 363526146977193486⟩
def pH383 : Prm := ⟨68, 32, 33, 385, 11, 18446744073709551616, 363534943070215694, 363534943070215694⟩
def pI383 : Prm := ⟨58, 28, 27, 385, 11, 18446744073709551616, 363526146977193486, 363534943070215694⟩
theorem L383_fin : (prmOK pL383 383 && ptTest pL383 (runFrom pL383 (fmask pL383) (cmask pL383) (hmask pL383) 1 382 (true, (init pL383), (init pL383))) 383 192 false) = true := by
  decide +kernel
theorem L383_ok : RunOK pL383 383 (runFrom pL383 (fmask pL383) (cmask pL383) (hmask pL383) 1 382 (true, (init pL383), (init pL383))) ∧ ptTest pL383 (runFrom pL383 (fmask pL383) (cmask pL383) (hmask pL383) 1 382 (true, (init pL383), (init pL383))) 383 192 false = true :=
  fin_run (runOK_init (prmOK_of_and L383_fin) true) (by decide) rfl L383_fin ptTest_fst
theorem H383_fin : (prmOK pH383 383 && ptTest pH383 (runFrom pH383 (fmask pH383) (cmask pH383) (hmask pH383) 1 382 (true, (init pH383), (init pH383))) 383 192 true) = true := by
  decide +kernel
theorem H383_ok : RunOK pH383 383 (runFrom pH383 (fmask pH383) (cmask pH383) (hmask pH383) 1 382 (true, (init pH383), (init pH383))) ∧ ptTest pH383 (runFrom pH383 (fmask pH383) (cmask pH383) (hmask pH383) 1 382 (true, (init pH383), (init pH383))) 383 192 true = true :=
  fin_run (runOK_init (prmOK_of_and H383_fin) true) (by decide) rfl H383_fin ptTest_fst
theorem I383_fin : (prmOK pI383 383 && intTest pI383 (runFrom pI383 (fmask pI383) (cmask pI383) (hmask pI383) 1 382 (true, (init pI383), (init pI383))) 383 13 false) = true := by
  decide +kernel
theorem I383_ok : RunOK pI383 383 (runFrom pI383 (fmask pI383) (cmask pI383) (hmask pI383) 1 382 (true, (init pI383), (init pI383))) ∧ intTest pI383 (runFrom pI383 (fmask pI383) (cmask pI383) (hmask pI383) 1 382 (true, (init pI383), (init pI383))) 383 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I383_fin) true) (by decide) rfl I383_fin intTest_fst
theorem link383 : linkOK pL383 pH383 pI383 = true := by decide +kernel
theorem cvx383 : ConvexBetweenHumps 383 :=
  cvx_of L383_ok H383_ok I383_ok link383 (by decide)

/-! ### `N = 384` -/

def pL384 : Prm := ⟨68, 32, 33, 386, 11, 18446744073709551616, 362815235310623933, 362815235310623933⟩
def pH384 : Prm := ⟨68, 32, 33, 386, 11, 18446744073709551616, 362824031403646141, 362824031403646141⟩
def pI384 : Prm := ⟨58, 28, 27, 386, 11, 18446744073709551616, 362815235310623933, 362824031403646141⟩
theorem L384_fin : (prmOK pL384 384 && ptTest pL384 (runFrom pL384 (fmask pL384) (cmask pL384) (hmask pL384) 1 383 (true, (init pL384), (init pL384))) 384 192 false) = true := by
  decide +kernel
theorem L384_ok : RunOK pL384 384 (runFrom pL384 (fmask pL384) (cmask pL384) (hmask pL384) 1 383 (true, (init pL384), (init pL384))) ∧ ptTest pL384 (runFrom pL384 (fmask pL384) (cmask pL384) (hmask pL384) 1 383 (true, (init pL384), (init pL384))) 384 192 false = true :=
  fin_run (runOK_init (prmOK_of_and L384_fin) true) (by decide) rfl L384_fin ptTest_fst
theorem H384_fin : (prmOK pH384 384 && ptTest pH384 (runFrom pH384 (fmask pH384) (cmask pH384) (hmask pH384) 1 383 (true, (init pH384), (init pH384))) 384 192 true) = true := by
  decide +kernel
theorem H384_ok : RunOK pH384 384 (runFrom pH384 (fmask pH384) (cmask pH384) (hmask pH384) 1 383 (true, (init pH384), (init pH384))) ∧ ptTest pH384 (runFrom pH384 (fmask pH384) (cmask pH384) (hmask pH384) 1 383 (true, (init pH384), (init pH384))) 384 192 true = true :=
  fin_run (runOK_init (prmOK_of_and H384_fin) true) (by decide) rfl H384_fin ptTest_fst
theorem I384_fin : (prmOK pI384 384 && intTest pI384 (runFrom pI384 (fmask pI384) (cmask pI384) (hmask pI384) 1 383 (true, (init pI384), (init pI384))) 384 13 true) = true := by
  decide +kernel
theorem I384_ok : RunOK pI384 384 (runFrom pI384 (fmask pI384) (cmask pI384) (hmask pI384) 1 383 (true, (init pI384), (init pI384))) ∧ intTest pI384 (runFrom pI384 (fmask pI384) (cmask pI384) (hmask pI384) 1 383 (true, (init pI384), (init pI384))) 384 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I384_fin) true) (by decide) rfl I384_fin intTest_fst
theorem link384 : linkOK pL384 pH384 pI384 = true := by decide +kernel
theorem cvx384 : ConvexBetweenHumps 384 :=
  cvx_of L384_ok H384_ok I384_ok link384 (by decide)
theorem cenlink384 : cenLinkOK pI384 384 = true := by decide +kernel
theorem cen384 : CenterUniqueMin 384 ∧ DipHyp 384 ∧ OnePointHyps 384 :=
  cen_of L384_ok H384_ok I384_ok link384 cenlink384

/-! ### `N = 385` -/

def pL385 : Prm := ⟨68, 32, 33, 387, 11, 18446744073709551616, 362105282113412192, 362105282113412192⟩
def pH385 : Prm := ⟨68, 32, 33, 387, 11, 18446744073709551616, 362114078206434400, 362114078206434400⟩
def pI385 : Prm := ⟨58, 28, 27, 387, 11, 18446744073709551616, 362105282113412192, 362114078206434400⟩
theorem L385_fin : (prmOK pL385 385 && ptTest pL385 (runFrom pL385 (fmask pL385) (cmask pL385) (hmask pL385) 1 384 (true, (init pL385), (init pL385))) 385 193 false) = true := by
  decide +kernel
theorem L385_ok : RunOK pL385 385 (runFrom pL385 (fmask pL385) (cmask pL385) (hmask pL385) 1 384 (true, (init pL385), (init pL385))) ∧ ptTest pL385 (runFrom pL385 (fmask pL385) (cmask pL385) (hmask pL385) 1 384 (true, (init pL385), (init pL385))) 385 193 false = true :=
  fin_run (runOK_init (prmOK_of_and L385_fin) true) (by decide) rfl L385_fin ptTest_fst
theorem H385_fin : (prmOK pH385 385 && ptTest pH385 (runFrom pH385 (fmask pH385) (cmask pH385) (hmask pH385) 1 384 (true, (init pH385), (init pH385))) 385 193 true) = true := by
  decide +kernel
theorem H385_ok : RunOK pH385 385 (runFrom pH385 (fmask pH385) (cmask pH385) (hmask pH385) 1 384 (true, (init pH385), (init pH385))) ∧ ptTest pH385 (runFrom pH385 (fmask pH385) (cmask pH385) (hmask pH385) 1 384 (true, (init pH385), (init pH385))) 385 193 true = true :=
  fin_run (runOK_init (prmOK_of_and H385_fin) true) (by decide) rfl H385_fin ptTest_fst
theorem I385_fin : (prmOK pI385 385 && intTest pI385 (runFrom pI385 (fmask pI385) (cmask pI385) (hmask pI385) 1 384 (true, (init pI385), (init pI385))) 385 13 false) = true := by
  decide +kernel
theorem I385_ok : RunOK pI385 385 (runFrom pI385 (fmask pI385) (cmask pI385) (hmask pI385) 1 384 (true, (init pI385), (init pI385))) ∧ intTest pI385 (runFrom pI385 (fmask pI385) (cmask pI385) (hmask pI385) 1 384 (true, (init pI385), (init pI385))) 385 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I385_fin) true) (by decide) rfl I385_fin intTest_fst
theorem link385 : linkOK pL385 pH385 pI385 = true := by decide +kernel
theorem cvx385 : ConvexBetweenHumps 385 :=
  cvx_of L385_ok H385_ok I385_ok link385 (by decide)

/-! ### `N = 386` -/

def pL386 : Prm := ⟨68, 32, 33, 388, 11, 18446744073709551616, 361400532919331218, 361400532919331218⟩
def pH386 : Prm := ⟨68, 32, 33, 388, 11, 18446744073709551616, 361409329012353426, 361409329012353426⟩
def pI386 : Prm := ⟨58, 28, 27, 388, 11, 18446744073709551616, 361400532919331218, 361409329012353426⟩
theorem L386_fin : (prmOK pL386 386 && ptTest pL386 (runFrom pL386 (fmask pL386) (cmask pL386) (hmask pL386) 1 385 (true, (init pL386), (init pL386))) 386 193 false) = true := by
  decide +kernel
theorem L386_ok : RunOK pL386 386 (runFrom pL386 (fmask pL386) (cmask pL386) (hmask pL386) 1 385 (true, (init pL386), (init pL386))) ∧ ptTest pL386 (runFrom pL386 (fmask pL386) (cmask pL386) (hmask pL386) 1 385 (true, (init pL386), (init pL386))) 386 193 false = true :=
  fin_run (runOK_init (prmOK_of_and L386_fin) true) (by decide) rfl L386_fin ptTest_fst
theorem H386_fin : (prmOK pH386 386 && ptTest pH386 (runFrom pH386 (fmask pH386) (cmask pH386) (hmask pH386) 1 385 (true, (init pH386), (init pH386))) 386 193 true) = true := by
  decide +kernel
theorem H386_ok : RunOK pH386 386 (runFrom pH386 (fmask pH386) (cmask pH386) (hmask pH386) 1 385 (true, (init pH386), (init pH386))) ∧ ptTest pH386 (runFrom pH386 (fmask pH386) (cmask pH386) (hmask pH386) 1 385 (true, (init pH386), (init pH386))) 386 193 true = true :=
  fin_run (runOK_init (prmOK_of_and H386_fin) true) (by decide) rfl H386_fin ptTest_fst
theorem I386_fin : (prmOK pI386 386 && intTest pI386 (runFrom pI386 (fmask pI386) (cmask pI386) (hmask pI386) 1 385 (true, (init pI386), (init pI386))) 386 13 true) = true := by
  decide +kernel
theorem I386_ok : RunOK pI386 386 (runFrom pI386 (fmask pI386) (cmask pI386) (hmask pI386) 1 385 (true, (init pI386), (init pI386))) ∧ intTest pI386 (runFrom pI386 (fmask pI386) (cmask pI386) (hmask pI386) 1 385 (true, (init pI386), (init pI386))) 386 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I386_fin) true) (by decide) rfl I386_fin intTest_fst
theorem link386 : linkOK pL386 pH386 pI386 = true := by decide +kernel
theorem cvx386 : ConvexBetweenHumps 386 :=
  cvx_of L386_ok H386_ok I386_ok link386 (by decide)
theorem cenlink386 : cenLinkOK pI386 386 = true := by decide +kernel
theorem cen386 : CenterUniqueMin 386 ∧ DipHyp 386 ∧ OnePointHyps 386 :=
  cen_of L386_ok H386_ok I386_ok link386 cenlink386

/-! ### `N = 387` -/

def pL387 : Prm := ⟨68, 32, 33, 389, 11, 18446744073709551616, 360696733749024536, 360696733749024536⟩
def pH387 : Prm := ⟨68, 32, 33, 389, 11, 18446744073709551616, 360705529842046744, 360705529842046744⟩
def pI387 : Prm := ⟨58, 28, 27, 389, 11, 18446744073709551616, 360696733749024536, 360705529842046744⟩
theorem L387_fin : (prmOK pL387 387 && ptTest pL387 (runFrom pL387 (fmask pL387) (cmask pL387) (hmask pL387) 1 386 (true, (init pL387), (init pL387))) 387 194 false) = true := by
  decide +kernel
theorem L387_ok : RunOK pL387 387 (runFrom pL387 (fmask pL387) (cmask pL387) (hmask pL387) 1 386 (true, (init pL387), (init pL387))) ∧ ptTest pL387 (runFrom pL387 (fmask pL387) (cmask pL387) (hmask pL387) 1 386 (true, (init pL387), (init pL387))) 387 194 false = true :=
  fin_run (runOK_init (prmOK_of_and L387_fin) true) (by decide) rfl L387_fin ptTest_fst
theorem H387_fin : (prmOK pH387 387 && ptTest pH387 (runFrom pH387 (fmask pH387) (cmask pH387) (hmask pH387) 1 386 (true, (init pH387), (init pH387))) 387 194 true) = true := by
  decide +kernel
theorem H387_ok : RunOK pH387 387 (runFrom pH387 (fmask pH387) (cmask pH387) (hmask pH387) 1 386 (true, (init pH387), (init pH387))) ∧ ptTest pH387 (runFrom pH387 (fmask pH387) (cmask pH387) (hmask pH387) 1 386 (true, (init pH387), (init pH387))) 387 194 true = true :=
  fin_run (runOK_init (prmOK_of_and H387_fin) true) (by decide) rfl H387_fin ptTest_fst
theorem I387_fin : (prmOK pI387 387 && intTest pI387 (runFrom pI387 (fmask pI387) (cmask pI387) (hmask pI387) 1 386 (true, (init pI387), (init pI387))) 387 13 false) = true := by
  decide +kernel
theorem I387_ok : RunOK pI387 387 (runFrom pI387 (fmask pI387) (cmask pI387) (hmask pI387) 1 386 (true, (init pI387), (init pI387))) ∧ intTest pI387 (runFrom pI387 (fmask pI387) (cmask pI387) (hmask pI387) 1 386 (true, (init pI387), (init pI387))) 387 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I387_fin) true) (by decide) rfl I387_fin intTest_fst
theorem link387 : linkOK pL387 pH387 pI387 = true := by decide +kernel
theorem cvx387 : ConvexBetweenHumps 387 :=
  cvx_of L387_ok H387_ok I387_ok link387 (by decide)

/-! ### `N = 388` -/

def pL388 : Prm := ⟨68, 32, 33, 390, 11, 18446744073709551616, 359998063853276723, 359998063853276723⟩
def pH388 : Prm := ⟨68, 32, 33, 390, 11, 18446744073709551616, 360006859946298931, 360006859946298931⟩
def pI388 : Prm := ⟨58, 28, 27, 390, 11, 18446744073709551616, 359998063853276723, 360006859946298931⟩
theorem L388_fin : (prmOK pL388 388 && ptTest pL388 (runFrom pL388 (fmask pL388) (cmask pL388) (hmask pL388) 1 387 (true, (init pL388), (init pL388))) 388 194 false) = true := by
  decide +kernel
theorem L388_ok : RunOK pL388 388 (runFrom pL388 (fmask pL388) (cmask pL388) (hmask pL388) 1 387 (true, (init pL388), (init pL388))) ∧ ptTest pL388 (runFrom pL388 (fmask pL388) (cmask pL388) (hmask pL388) 1 387 (true, (init pL388), (init pL388))) 388 194 false = true :=
  fin_run (runOK_init (prmOK_of_and L388_fin) true) (by decide) rfl L388_fin ptTest_fst
theorem H388_fin : (prmOK pH388 388 && ptTest pH388 (runFrom pH388 (fmask pH388) (cmask pH388) (hmask pH388) 1 387 (true, (init pH388), (init pH388))) 388 194 true) = true := by
  decide +kernel
theorem H388_ok : RunOK pH388 388 (runFrom pH388 (fmask pH388) (cmask pH388) (hmask pH388) 1 387 (true, (init pH388), (init pH388))) ∧ ptTest pH388 (runFrom pH388 (fmask pH388) (cmask pH388) (hmask pH388) 1 387 (true, (init pH388), (init pH388))) 388 194 true = true :=
  fin_run (runOK_init (prmOK_of_and H388_fin) true) (by decide) rfl H388_fin ptTest_fst
theorem I388_fin : (prmOK pI388 388 && intTest pI388 (runFrom pI388 (fmask pI388) (cmask pI388) (hmask pI388) 1 387 (true, (init pI388), (init pI388))) 388 13 true) = true := by
  decide +kernel
theorem I388_ok : RunOK pI388 388 (runFrom pI388 (fmask pI388) (cmask pI388) (hmask pI388) 1 387 (true, (init pI388), (init pI388))) ∧ intTest pI388 (runFrom pI388 (fmask pI388) (cmask pI388) (hmask pI388) 1 387 (true, (init pI388), (init pI388))) 388 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I388_fin) true) (by decide) rfl I388_fin intTest_fst
theorem link388 : linkOK pL388 pH388 pI388 = true := by decide +kernel
theorem cvx388 : ConvexBetweenHumps 388 :=
  cvx_of L388_ok H388_ok I388_ok link388 (by decide)
theorem cenlink388 : cenLinkOK pI388 388 = true := by decide +kernel
theorem cen388 : CenterUniqueMin 388 ∧ DipHyp 388 ∧ OnePointHyps 388 :=
  cen_of L388_ok H388_ok I388_ok link388 cenlink388

/-! ### `N = 389` -/

def pL389 : Prm := ⟨68, 32, 33, 391, 11, 18446744073709551616, 359300335617014483, 359300335617014483⟩
def pH389 : Prm := ⟨68, 32, 33, 391, 11, 18446744073709551616, 359309131710036691, 359309131710036691⟩
def pI389 : Prm := ⟨58, 28, 27, 391, 11, 18446744073709551616, 359300335617014483, 359309131710036691⟩
theorem L389_fin : (prmOK pL389 389 && ptTest pL389 (runFrom pL389 (fmask pL389) (cmask pL389) (hmask pL389) 1 388 (true, (init pL389), (init pL389))) 389 195 false) = true := by
  decide +kernel
theorem L389_ok : RunOK pL389 389 (runFrom pL389 (fmask pL389) (cmask pL389) (hmask pL389) 1 388 (true, (init pL389), (init pL389))) ∧ ptTest pL389 (runFrom pL389 (fmask pL389) (cmask pL389) (hmask pL389) 1 388 (true, (init pL389), (init pL389))) 389 195 false = true :=
  fin_run (runOK_init (prmOK_of_and L389_fin) true) (by decide) rfl L389_fin ptTest_fst
theorem H389_fin : (prmOK pH389 389 && ptTest pH389 (runFrom pH389 (fmask pH389) (cmask pH389) (hmask pH389) 1 388 (true, (init pH389), (init pH389))) 389 195 true) = true := by
  decide +kernel
theorem H389_ok : RunOK pH389 389 (runFrom pH389 (fmask pH389) (cmask pH389) (hmask pH389) 1 388 (true, (init pH389), (init pH389))) ∧ ptTest pH389 (runFrom pH389 (fmask pH389) (cmask pH389) (hmask pH389) 1 388 (true, (init pH389), (init pH389))) 389 195 true = true :=
  fin_run (runOK_init (prmOK_of_and H389_fin) true) (by decide) rfl H389_fin ptTest_fst
theorem I389_fin : (prmOK pI389 389 && intTest pI389 (runFrom pI389 (fmask pI389) (cmask pI389) (hmask pI389) 1 388 (true, (init pI389), (init pI389))) 389 13 false) = true := by
  decide +kernel
theorem I389_ok : RunOK pI389 389 (runFrom pI389 (fmask pI389) (cmask pI389) (hmask pI389) 1 388 (true, (init pI389), (init pI389))) ∧ intTest pI389 (runFrom pI389 (fmask pI389) (cmask pI389) (hmask pI389) 1 388 (true, (init pI389), (init pI389))) 389 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I389_fin) true) (by decide) rfl I389_fin intTest_fst
theorem link389 : linkOK pL389 pH389 pI389 = true := by decide +kernel
theorem cvx389 : ConvexBetweenHumps 389 :=
  cvx_of L389_ok H389_ok I389_ok link389 (by decide)

/-! ### `N = 390` -/

def pL390 : Prm := ⟨68, 32, 33, 392, 11, 18446744073709551616, 358607663370307616, 358607663370307616⟩
def pH390 : Prm := ⟨68, 32, 33, 392, 11, 18446744073709551616, 358616459463329824, 358616459463329824⟩
def pI390 : Prm := ⟨58, 28, 27, 392, 11, 18446744073709551616, 358607663370307616, 358616459463329824⟩
theorem L390_fin : (prmOK pL390 390 && ptTest pL390 (runFrom pL390 (fmask pL390) (cmask pL390) (hmask pL390) 1 389 (true, (init pL390), (init pL390))) 390 195 false) = true := by
  decide +kernel
theorem L390_ok : RunOK pL390 390 (runFrom pL390 (fmask pL390) (cmask pL390) (hmask pL390) 1 389 (true, (init pL390), (init pL390))) ∧ ptTest pL390 (runFrom pL390 (fmask pL390) (cmask pL390) (hmask pL390) 1 389 (true, (init pL390), (init pL390))) 390 195 false = true :=
  fin_run (runOK_init (prmOK_of_and L390_fin) true) (by decide) rfl L390_fin ptTest_fst
theorem H390_fin : (prmOK pH390 390 && ptTest pH390 (runFrom pH390 (fmask pH390) (cmask pH390) (hmask pH390) 1 389 (true, (init pH390), (init pH390))) 390 195 true) = true := by
  decide +kernel
theorem H390_ok : RunOK pH390 390 (runFrom pH390 (fmask pH390) (cmask pH390) (hmask pH390) 1 389 (true, (init pH390), (init pH390))) ∧ ptTest pH390 (runFrom pH390 (fmask pH390) (cmask pH390) (hmask pH390) 1 389 (true, (init pH390), (init pH390))) 390 195 true = true :=
  fin_run (runOK_init (prmOK_of_and H390_fin) true) (by decide) rfl H390_fin ptTest_fst
theorem I390_fin : (prmOK pI390 390 && intTest pI390 (runFrom pI390 (fmask pI390) (cmask pI390) (hmask pI390) 1 389 (true, (init pI390), (init pI390))) 390 13 true) = true := by
  decide +kernel
theorem I390_ok : RunOK pI390 390 (runFrom pI390 (fmask pI390) (cmask pI390) (hmask pI390) 1 389 (true, (init pI390), (init pI390))) ∧ intTest pI390 (runFrom pI390 (fmask pI390) (cmask pI390) (hmask pI390) 1 389 (true, (init pI390), (init pI390))) 390 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I390_fin) true) (by decide) rfl I390_fin intTest_fst
theorem link390 : linkOK pL390 pH390 pI390 = true := by decide +kernel
theorem cvx390 : ConvexBetweenHumps 390 :=
  cvx_of L390_ok H390_ok I390_ok link390 (by decide)
theorem cenlink390 : cenLinkOK pI390 390 = true := by decide +kernel
theorem cen390 : CenterUniqueMin 390 ∧ DipHyp 390 ∧ OnePointHyps 390 :=
  cen_of L390_ok H390_ok I390_ok link390 cenlink390

/-! ### `N = 391` -/

def pL391 : Prm := ⟨68, 32, 33, 393, 11, 18446744073709551616, 357915924499834151, 357915924499834151⟩
def pH391 : Prm := ⟨68, 32, 33, 393, 11, 18446744073709551616, 357924720592856359, 357924720592856359⟩
def pI391 : Prm := ⟨59, 28, 28, 393, 11, 18446744073709551616, 357915924499834151, 357924720592856359⟩
theorem L391_fin : (prmOK pL391 391 && ptTest pL391 (runFrom pL391 (fmask pL391) (cmask pL391) (hmask pL391) 1 390 (true, (init pL391), (init pL391))) 391 196 false) = true := by
  decide +kernel
theorem L391_ok : RunOK pL391 391 (runFrom pL391 (fmask pL391) (cmask pL391) (hmask pL391) 1 390 (true, (init pL391), (init pL391))) ∧ ptTest pL391 (runFrom pL391 (fmask pL391) (cmask pL391) (hmask pL391) 1 390 (true, (init pL391), (init pL391))) 391 196 false = true :=
  fin_run (runOK_init (prmOK_of_and L391_fin) true) (by decide) rfl L391_fin ptTest_fst
theorem H391_fin : (prmOK pH391 391 && ptTest pH391 (runFrom pH391 (fmask pH391) (cmask pH391) (hmask pH391) 1 390 (true, (init pH391), (init pH391))) 391 196 true) = true := by
  decide +kernel
theorem H391_ok : RunOK pH391 391 (runFrom pH391 (fmask pH391) (cmask pH391) (hmask pH391) 1 390 (true, (init pH391), (init pH391))) ∧ ptTest pH391 (runFrom pH391 (fmask pH391) (cmask pH391) (hmask pH391) 1 390 (true, (init pH391), (init pH391))) 391 196 true = true :=
  fin_run (runOK_init (prmOK_of_and H391_fin) true) (by decide) rfl H391_fin ptTest_fst
theorem I391_fin : (prmOK pI391 391 && intTest pI391 (runFrom pI391 (fmask pI391) (cmask pI391) (hmask pI391) 1 390 (true, (init pI391), (init pI391))) 391 13 false) = true := by
  decide +kernel
theorem I391_ok : RunOK pI391 391 (runFrom pI391 (fmask pI391) (cmask pI391) (hmask pI391) 1 390 (true, (init pI391), (init pI391))) ∧ intTest pI391 (runFrom pI391 (fmask pI391) (cmask pI391) (hmask pI391) 1 390 (true, (init pI391), (init pI391))) 391 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I391_fin) true) (by decide) rfl I391_fin intTest_fst
theorem link391 : linkOK pL391 pH391 pI391 = true := by decide +kernel
theorem cvx391 : ConvexBetweenHumps 391 :=
  cvx_of L391_ok H391_ok I391_ok link391 (by decide)

/-! ### `N = 392` -/

def pL392 : Prm := ⟨68, 32, 33, 394, 11, 18446744073709551616, 357229169742524388, 357229169742524388⟩
def pH392 : Prm := ⟨68, 32, 33, 394, 11, 18446744073709551616, 357237965835546596, 357237965835546596⟩
def pI392 : Prm := ⟨59, 28, 28, 394, 11, 18446744073709551616, 357229169742524388, 357237965835546596⟩
theorem L392_fin : (prmOK pL392 392 && ptTest pL392 (runFrom pL392 (fmask pL392) (cmask pL392) (hmask pL392) 1 391 (true, (init pL392), (init pL392))) 392 196 false) = true := by
  decide +kernel
theorem L392_ok : RunOK pL392 392 (runFrom pL392 (fmask pL392) (cmask pL392) (hmask pL392) 1 391 (true, (init pL392), (init pL392))) ∧ ptTest pL392 (runFrom pL392 (fmask pL392) (cmask pL392) (hmask pL392) 1 391 (true, (init pL392), (init pL392))) 392 196 false = true :=
  fin_run (runOK_init (prmOK_of_and L392_fin) true) (by decide) rfl L392_fin ptTest_fst
theorem H392_fin : (prmOK pH392 392 && ptTest pH392 (runFrom pH392 (fmask pH392) (cmask pH392) (hmask pH392) 1 391 (true, (init pH392), (init pH392))) 392 196 true) = true := by
  decide +kernel
theorem H392_ok : RunOK pH392 392 (runFrom pH392 (fmask pH392) (cmask pH392) (hmask pH392) 1 391 (true, (init pH392), (init pH392))) ∧ ptTest pH392 (runFrom pH392 (fmask pH392) (cmask pH392) (hmask pH392) 1 391 (true, (init pH392), (init pH392))) 392 196 true = true :=
  fin_run (runOK_init (prmOK_of_and H392_fin) true) (by decide) rfl H392_fin ptTest_fst
theorem I392_fin : (prmOK pI392 392 && intTest pI392 (runFrom pI392 (fmask pI392) (cmask pI392) (hmask pI392) 1 391 (true, (init pI392), (init pI392))) 392 13 true) = true := by
  decide +kernel
theorem I392_ok : RunOK pI392 392 (runFrom pI392 (fmask pI392) (cmask pI392) (hmask pI392) 1 391 (true, (init pI392), (init pI392))) ∧ intTest pI392 (runFrom pI392 (fmask pI392) (cmask pI392) (hmask pI392) 1 391 (true, (init pI392), (init pI392))) 392 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I392_fin) true) (by decide) rfl I392_fin intTest_fst
theorem link392 : linkOK pL392 pH392 pI392 = true := by decide +kernel
theorem cvx392 : ConvexBetweenHumps 392 :=
  cvx_of L392_ok H392_ok I392_ok link392 (by decide)
theorem cenlink392 : cenLinkOK pI392 392 = true := by decide +kernel
theorem cen392 : CenterUniqueMin 392 ∧ DipHyp 392 ∧ OnePointHyps 392 :=
  cen_of L392_ok H392_ok I392_ok link392 cenlink392

/-! ### `N = 393` -/

def pL393 : Prm := ⟨68, 32, 33, 395, 11, 18446744073709551616, 356543340158771233, 356543340158771233⟩
def pH393 : Prm := ⟨68, 32, 33, 395, 11, 18446744073709551616, 356552136251793441, 356552136251793441⟩
def pI393 : Prm := ⟨59, 28, 28, 395, 11, 18446744073709551616, 356543340158771233, 356552136251793441⟩
theorem L393_fin : (prmOK pL393 393 && ptTest pL393 (runFrom pL393 (fmask pL393) (cmask pL393) (hmask pL393) 1 392 (true, (init pL393), (init pL393))) 393 197 false) = true := by
  decide +kernel
theorem L393_ok : RunOK pL393 393 (runFrom pL393 (fmask pL393) (cmask pL393) (hmask pL393) 1 392 (true, (init pL393), (init pL393))) ∧ ptTest pL393 (runFrom pL393 (fmask pL393) (cmask pL393) (hmask pL393) 1 392 (true, (init pL393), (init pL393))) 393 197 false = true :=
  fin_run (runOK_init (prmOK_of_and L393_fin) true) (by decide) rfl L393_fin ptTest_fst
theorem H393_fin : (prmOK pH393 393 && ptTest pH393 (runFrom pH393 (fmask pH393) (cmask pH393) (hmask pH393) 1 392 (true, (init pH393), (init pH393))) 393 197 true) = true := by
  decide +kernel
theorem H393_ok : RunOK pH393 393 (runFrom pH393 (fmask pH393) (cmask pH393) (hmask pH393) 1 392 (true, (init pH393), (init pH393))) ∧ ptTest pH393 (runFrom pH393 (fmask pH393) (cmask pH393) (hmask pH393) 1 392 (true, (init pH393), (init pH393))) 393 197 true = true :=
  fin_run (runOK_init (prmOK_of_and H393_fin) true) (by decide) rfl H393_fin ptTest_fst
theorem I393_fin : (prmOK pI393 393 && intTest pI393 (runFrom pI393 (fmask pI393) (cmask pI393) (hmask pI393) 1 392 (true, (init pI393), (init pI393))) 393 13 false) = true := by
  decide +kernel
theorem I393_ok : RunOK pI393 393 (runFrom pI393 (fmask pI393) (cmask pI393) (hmask pI393) 1 392 (true, (init pI393), (init pI393))) ∧ intTest pI393 (runFrom pI393 (fmask pI393) (cmask pI393) (hmask pI393) 1 392 (true, (init pI393), (init pI393))) 393 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I393_fin) true) (by decide) rfl I393_fin intTest_fst
theorem link393 : linkOK pL393 pH393 pI393 = true := by decide +kernel
theorem cvx393 : ConvexBetweenHumps 393 :=
  cvx_of L393_ok H393_ok I393_ok link393 (by decide)

/-! ### `N = 394` -/

def pL394 : Prm := ⟨68, 32, 33, 396, 11, 18446744073709551616, 355862424186386138, 355862424186386138⟩
def pH394 : Prm := ⟨68, 32, 33, 396, 11, 18446744073709551616, 355871220279408346, 355871220279408346⟩
def pI394 : Prm := ⟨59, 28, 28, 396, 11, 18446744073709551616, 355862424186386138, 355871220279408346⟩
theorem L394_fin : (prmOK pL394 394 && ptTest pL394 (runFrom pL394 (fmask pL394) (cmask pL394) (hmask pL394) 1 393 (true, (init pL394), (init pL394))) 394 197 false) = true := by
  decide +kernel
theorem L394_ok : RunOK pL394 394 (runFrom pL394 (fmask pL394) (cmask pL394) (hmask pL394) 1 393 (true, (init pL394), (init pL394))) ∧ ptTest pL394 (runFrom pL394 (fmask pL394) (cmask pL394) (hmask pL394) 1 393 (true, (init pL394), (init pL394))) 394 197 false = true :=
  fin_run (runOK_init (prmOK_of_and L394_fin) true) (by decide) rfl L394_fin ptTest_fst
theorem H394_fin : (prmOK pH394 394 && ptTest pH394 (runFrom pH394 (fmask pH394) (cmask pH394) (hmask pH394) 1 393 (true, (init pH394), (init pH394))) 394 197 true) = true := by
  decide +kernel
theorem H394_ok : RunOK pH394 394 (runFrom pH394 (fmask pH394) (cmask pH394) (hmask pH394) 1 393 (true, (init pH394), (init pH394))) ∧ ptTest pH394 (runFrom pH394 (fmask pH394) (cmask pH394) (hmask pH394) 1 393 (true, (init pH394), (init pH394))) 394 197 true = true :=
  fin_run (runOK_init (prmOK_of_and H394_fin) true) (by decide) rfl H394_fin ptTest_fst
theorem I394_fin : (prmOK pI394 394 && intTest pI394 (runFrom pI394 (fmask pI394) (cmask pI394) (hmask pI394) 1 393 (true, (init pI394), (init pI394))) 394 13 true) = true := by
  decide +kernel
theorem I394_ok : RunOK pI394 394 (runFrom pI394 (fmask pI394) (cmask pI394) (hmask pI394) 1 393 (true, (init pI394), (init pI394))) ∧ intTest pI394 (runFrom pI394 (fmask pI394) (cmask pI394) (hmask pI394) 1 393 (true, (init pI394), (init pI394))) 394 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I394_fin) true) (by decide) rfl I394_fin intTest_fst
theorem link394 : linkOK pL394 pH394 pI394 = true := by decide +kernel
theorem cvx394 : ConvexBetweenHumps 394 :=
  cvx_of L394_ok H394_ok I394_ok link394 (by decide)
theorem cenlink394 : cenLinkOK pI394 394 = true := by decide +kernel
theorem cen394 : CenterUniqueMin 394 ∧ DipHyp 394 ∧ OnePointHyps 394 :=
  cen_of L394_ok H394_ok I394_ok link394 cenlink394

/-! ### `N = 395` -/

def pL395 : Prm := ⟨68, 32, 33, 397, 11, 18446744073709551616, 355182425265142640, 355182425265142640⟩
def pH395 : Prm := ⟨68, 32, 33, 397, 11, 18446744073709551616, 355191221358164848, 355191221358164848⟩
def pI395 : Prm := ⟨59, 28, 28, 397, 11, 18446744073709551616, 355182425265142640, 355191221358164848⟩
theorem L395_fin : (prmOK pL395 395 && ptTest pL395 (runFrom pL395 (fmask pL395) (cmask pL395) (hmask pL395) 1 394 (true, (init pL395), (init pL395))) 395 198 false) = true := by
  decide +kernel
theorem L395_ok : RunOK pL395 395 (runFrom pL395 (fmask pL395) (cmask pL395) (hmask pL395) 1 394 (true, (init pL395), (init pL395))) ∧ ptTest pL395 (runFrom pL395 (fmask pL395) (cmask pL395) (hmask pL395) 1 394 (true, (init pL395), (init pL395))) 395 198 false = true :=
  fin_run (runOK_init (prmOK_of_and L395_fin) true) (by decide) rfl L395_fin ptTest_fst
theorem H395_fin : (prmOK pH395 395 && ptTest pH395 (runFrom pH395 (fmask pH395) (cmask pH395) (hmask pH395) 1 394 (true, (init pH395), (init pH395))) 395 198 true) = true := by
  decide +kernel
theorem H395_ok : RunOK pH395 395 (runFrom pH395 (fmask pH395) (cmask pH395) (hmask pH395) 1 394 (true, (init pH395), (init pH395))) ∧ ptTest pH395 (runFrom pH395 (fmask pH395) (cmask pH395) (hmask pH395) 1 394 (true, (init pH395), (init pH395))) 395 198 true = true :=
  fin_run (runOK_init (prmOK_of_and H395_fin) true) (by decide) rfl H395_fin ptTest_fst
theorem I395_fin : (prmOK pI395 395 && intTest pI395 (runFrom pI395 (fmask pI395) (cmask pI395) (hmask pI395) 1 394 (true, (init pI395), (init pI395))) 395 13 false) = true := by
  decide +kernel
theorem I395_ok : RunOK pI395 395 (runFrom pI395 (fmask pI395) (cmask pI395) (hmask pI395) 1 394 (true, (init pI395), (init pI395))) ∧ intTest pI395 (runFrom pI395 (fmask pI395) (cmask pI395) (hmask pI395) 1 394 (true, (init pI395), (init pI395))) 395 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I395_fin) true) (by decide) rfl I395_fin intTest_fst
theorem link395 : linkOK pL395 pH395 pI395 = true := by decide +kernel
theorem cvx395 : ConvexBetweenHumps 395 :=
  cvx_of L395_ok H395_ok I395_ok link395 (by decide)

/-! ### `N = 396` -/

def pL396 : Prm := ⟨68, 32, 33, 398, 11, 18446744073709551616, 354507270795213936, 354507270795213936⟩
def pH396 : Prm := ⟨68, 32, 33, 398, 11, 18446744073709551616, 354516066888236144, 354516066888236144⟩
def pI396 : Prm := ⟨59, 28, 28, 398, 11, 18446744073709551616, 354507270795213936, 354516066888236144⟩
theorem L396_fin : (prmOK pL396 396 && ptTest pL396 (runFrom pL396 (fmask pL396) (cmask pL396) (hmask pL396) 1 395 (true, (init pL396), (init pL396))) 396 198 false) = true := by
  decide +kernel
theorem L396_ok : RunOK pL396 396 (runFrom pL396 (fmask pL396) (cmask pL396) (hmask pL396) 1 395 (true, (init pL396), (init pL396))) ∧ ptTest pL396 (runFrom pL396 (fmask pL396) (cmask pL396) (hmask pL396) 1 395 (true, (init pL396), (init pL396))) 396 198 false = true :=
  fin_run (runOK_init (prmOK_of_and L396_fin) true) (by decide) rfl L396_fin ptTest_fst
theorem H396_fin : (prmOK pH396 396 && ptTest pH396 (runFrom pH396 (fmask pH396) (cmask pH396) (hmask pH396) 1 395 (true, (init pH396), (init pH396))) 396 198 true) = true := by
  decide +kernel
theorem H396_ok : RunOK pH396 396 (runFrom pH396 (fmask pH396) (cmask pH396) (hmask pH396) 1 395 (true, (init pH396), (init pH396))) ∧ ptTest pH396 (runFrom pH396 (fmask pH396) (cmask pH396) (hmask pH396) 1 395 (true, (init pH396), (init pH396))) 396 198 true = true :=
  fin_run (runOK_init (prmOK_of_and H396_fin) true) (by decide) rfl H396_fin ptTest_fst
theorem I396_fin : (prmOK pI396 396 && intTest pI396 (runFrom pI396 (fmask pI396) (cmask pI396) (hmask pI396) 1 395 (true, (init pI396), (init pI396))) 396 13 true) = true := by
  decide +kernel
theorem I396_ok : RunOK pI396 396 (runFrom pI396 (fmask pI396) (cmask pI396) (hmask pI396) 1 395 (true, (init pI396), (init pI396))) ∧ intTest pI396 (runFrom pI396 (fmask pI396) (cmask pI396) (hmask pI396) 1 395 (true, (init pI396), (init pI396))) 396 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I396_fin) true) (by decide) rfl I396_fin intTest_fst
theorem link396 : linkOK pL396 pH396 pI396 = true := by decide +kernel
theorem cvx396 : ConvexBetweenHumps 396 :=
  cvx_of L396_ok H396_ok I396_ok link396 (by decide)
theorem cenlink396 : cenLinkOK pI396 396 = true := by decide +kernel
theorem cen396 : CenterUniqueMin 396 ∧ DipHyp 396 ∧ OnePointHyps 396 :=
  cen_of L396_ok H396_ok I396_ok link396 cenlink396

/-! ### `N = 397` -/

def pL397 : Prm := ⟨68, 32, 33, 399, 11, 18446744073709551616, 353833025333738647, 353833025333738647⟩
def pH397 : Prm := ⟨68, 32, 33, 399, 11, 18446744073709551616, 353841821426760855, 353841821426760855⟩
def pI397 : Prm := ⟨59, 28, 28, 399, 11, 18446744073709551616, 353833025333738647, 353841821426760855⟩
theorem L397_fin : (prmOK pL397 397 && ptTest pL397 (runFrom pL397 (fmask pL397) (cmask pL397) (hmask pL397) 1 396 (true, (init pL397), (init pL397))) 397 199 false) = true := by
  decide +kernel
theorem L397_ok : RunOK pL397 397 (runFrom pL397 (fmask pL397) (cmask pL397) (hmask pL397) 1 396 (true, (init pL397), (init pL397))) ∧ ptTest pL397 (runFrom pL397 (fmask pL397) (cmask pL397) (hmask pL397) 1 396 (true, (init pL397), (init pL397))) 397 199 false = true :=
  fin_run (runOK_init (prmOK_of_and L397_fin) true) (by decide) rfl L397_fin ptTest_fst
theorem H397_fin : (prmOK pH397 397 && ptTest pH397 (runFrom pH397 (fmask pH397) (cmask pH397) (hmask pH397) 1 396 (true, (init pH397), (init pH397))) 397 199 true) = true := by
  decide +kernel
theorem H397_ok : RunOK pH397 397 (runFrom pH397 (fmask pH397) (cmask pH397) (hmask pH397) 1 396 (true, (init pH397), (init pH397))) ∧ ptTest pH397 (runFrom pH397 (fmask pH397) (cmask pH397) (hmask pH397) 1 396 (true, (init pH397), (init pH397))) 397 199 true = true :=
  fin_run (runOK_init (prmOK_of_and H397_fin) true) (by decide) rfl H397_fin ptTest_fst
theorem I397_fin : (prmOK pI397 397 && intTest pI397 (runFrom pI397 (fmask pI397) (cmask pI397) (hmask pI397) 1 396 (true, (init pI397), (init pI397))) 397 13 false) = true := by
  decide +kernel
theorem I397_ok : RunOK pI397 397 (runFrom pI397 (fmask pI397) (cmask pI397) (hmask pI397) 1 396 (true, (init pI397), (init pI397))) ∧ intTest pI397 (runFrom pI397 (fmask pI397) (cmask pI397) (hmask pI397) 1 396 (true, (init pI397), (init pI397))) 397 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I397_fin) true) (by decide) rfl I397_fin intTest_fst
theorem link397 : linkOK pL397 pH397 pI397 = true := by decide +kernel
theorem cvx397 : ConvexBetweenHumps 397 :=
  cvx_of L397_ok H397_ok I397_ok link397 (by decide)

/-! ### `N = 398` -/

def pL398 : Prm := ⟨68, 32, 33, 400, 11, 18446744073709551616, 353163556473151482, 353163556473151482⟩
def pH398 : Prm := ⟨68, 32, 33, 400, 11, 18446744073709551616, 353172352566173690, 353172352566173690⟩
def pI398 : Prm := ⟨59, 28, 28, 400, 11, 18446744073709551616, 353163556473151482, 353172352566173690⟩
theorem L398_fin : (prmOK pL398 398 && ptTest pL398 (runFrom pL398 (fmask pL398) (cmask pL398) (hmask pL398) 1 397 (true, (init pL398), (init pL398))) 398 199 false) = true := by
  decide +kernel
theorem L398_ok : RunOK pL398 398 (runFrom pL398 (fmask pL398) (cmask pL398) (hmask pL398) 1 397 (true, (init pL398), (init pL398))) ∧ ptTest pL398 (runFrom pL398 (fmask pL398) (cmask pL398) (hmask pL398) 1 397 (true, (init pL398), (init pL398))) 398 199 false = true :=
  fin_run (runOK_init (prmOK_of_and L398_fin) true) (by decide) rfl L398_fin ptTest_fst
theorem H398_fin : (prmOK pH398 398 && ptTest pH398 (runFrom pH398 (fmask pH398) (cmask pH398) (hmask pH398) 1 397 (true, (init pH398), (init pH398))) 398 199 true) = true := by
  decide +kernel
theorem H398_ok : RunOK pH398 398 (runFrom pH398 (fmask pH398) (cmask pH398) (hmask pH398) 1 397 (true, (init pH398), (init pH398))) ∧ ptTest pH398 (runFrom pH398 (fmask pH398) (cmask pH398) (hmask pH398) 1 397 (true, (init pH398), (init pH398))) 398 199 true = true :=
  fin_run (runOK_init (prmOK_of_and H398_fin) true) (by decide) rfl H398_fin ptTest_fst
theorem I398_fin : (prmOK pI398 398 && intTest pI398 (runFrom pI398 (fmask pI398) (cmask pI398) (hmask pI398) 1 397 (true, (init pI398), (init pI398))) 398 13 true) = true := by
  decide +kernel
theorem I398_ok : RunOK pI398 398 (runFrom pI398 (fmask pI398) (cmask pI398) (hmask pI398) 1 397 (true, (init pI398), (init pI398))) ∧ intTest pI398 (runFrom pI398 (fmask pI398) (cmask pI398) (hmask pI398) 1 397 (true, (init pI398), (init pI398))) 398 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I398_fin) true) (by decide) rfl I398_fin intTest_fst
theorem link398 : linkOK pL398 pH398 pI398 = true := by decide +kernel
theorem cvx398 : ConvexBetweenHumps 398 :=
  cvx_of L398_ok H398_ok I398_ok link398 (by decide)
theorem cenlink398 : cenLinkOK pI398 398 = true := by decide +kernel
theorem cen398 : CenterUniqueMin 398 ∧ DipHyp 398 ∧ OnePointHyps 398 :=
  cen_of L398_ok H398_ok I398_ok link398 cenlink398

/-! ### `N = 399` -/

def pL399 : Prm := ⟨68, 32, 33, 401, 11, 18446744073709551616, 352494988657687441, 352494988657687441⟩
def pH399 : Prm := ⟨68, 32, 33, 401, 11, 18446744073709551616, 352503784750709649, 352503784750709649⟩
def pI399 : Prm := ⟨59, 28, 28, 401, 11, 18446744073709551616, 352494988657687441, 352503784750709649⟩
theorem L399_fin : (prmOK pL399 399 && ptTest pL399 (runFrom pL399 (fmask pL399) (cmask pL399) (hmask pL399) 1 398 (true, (init pL399), (init pL399))) 399 200 false) = true := by
  decide +kernel
theorem L399_ok : RunOK pL399 399 (runFrom pL399 (fmask pL399) (cmask pL399) (hmask pL399) 1 398 (true, (init pL399), (init pL399))) ∧ ptTest pL399 (runFrom pL399 (fmask pL399) (cmask pL399) (hmask pL399) 1 398 (true, (init pL399), (init pL399))) 399 200 false = true :=
  fin_run (runOK_init (prmOK_of_and L399_fin) true) (by decide) rfl L399_fin ptTest_fst
theorem H399_fin : (prmOK pH399 399 && ptTest pH399 (runFrom pH399 (fmask pH399) (cmask pH399) (hmask pH399) 1 398 (true, (init pH399), (init pH399))) 399 200 true) = true := by
  decide +kernel
theorem H399_ok : RunOK pH399 399 (runFrom pH399 (fmask pH399) (cmask pH399) (hmask pH399) 1 398 (true, (init pH399), (init pH399))) ∧ ptTest pH399 (runFrom pH399 (fmask pH399) (cmask pH399) (hmask pH399) 1 398 (true, (init pH399), (init pH399))) 399 200 true = true :=
  fin_run (runOK_init (prmOK_of_and H399_fin) true) (by decide) rfl H399_fin ptTest_fst
theorem I399_fin : (prmOK pI399 399 && intTest pI399 (runFrom pI399 (fmask pI399) (cmask pI399) (hmask pI399) 1 398 (true, (init pI399), (init pI399))) 399 13 false) = true := by
  decide +kernel
theorem I399_ok : RunOK pI399 399 (runFrom pI399 (fmask pI399) (cmask pI399) (hmask pI399) 1 398 (true, (init pI399), (init pI399))) ∧ intTest pI399 (runFrom pI399 (fmask pI399) (cmask pI399) (hmask pI399) 1 398 (true, (init pI399), (init pI399))) 399 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I399_fin) true) (by decide) rfl I399_fin intTest_fst
theorem link399 : linkOK pL399 pH399 pI399 = true := by decide +kernel
theorem cvx399 : ConvexBetweenHumps 399 :=
  cvx_of L399_ok H399_ok I399_ok link399 (by decide)

/-! ### `N = 400` -/

def pL400 : Prm := ⟨68, 32, 33, 402, 11, 18446744073709551616, 351831130871265580, 351831130871265580⟩
def pH400 : Prm := ⟨68, 32, 33, 402, 11, 18446744073709551616, 351839926964287788, 351839926964287788⟩
def pI400 : Prm := ⟨59, 28, 28, 402, 11, 18446744073709551616, 351831130871265580, 351839926964287788⟩
theorem L400_fin : (prmOK pL400 400 && ptTest pL400 (runFrom pL400 (fmask pL400) (cmask pL400) (hmask pL400) 1 399 (true, (init pL400), (init pL400))) 400 200 false) = true := by
  decide +kernel
theorem L400_ok : RunOK pL400 400 (runFrom pL400 (fmask pL400) (cmask pL400) (hmask pL400) 1 399 (true, (init pL400), (init pL400))) ∧ ptTest pL400 (runFrom pL400 (fmask pL400) (cmask pL400) (hmask pL400) 1 399 (true, (init pL400), (init pL400))) 400 200 false = true :=
  fin_run (runOK_init (prmOK_of_and L400_fin) true) (by decide) rfl L400_fin ptTest_fst
theorem H400_fin : (prmOK pH400 400 && ptTest pH400 (runFrom pH400 (fmask pH400) (cmask pH400) (hmask pH400) 1 399 (true, (init pH400), (init pH400))) 400 200 true) = true := by
  decide +kernel
theorem H400_ok : RunOK pH400 400 (runFrom pH400 (fmask pH400) (cmask pH400) (hmask pH400) 1 399 (true, (init pH400), (init pH400))) ∧ ptTest pH400 (runFrom pH400 (fmask pH400) (cmask pH400) (hmask pH400) 1 399 (true, (init pH400), (init pH400))) 400 200 true = true :=
  fin_run (runOK_init (prmOK_of_and H400_fin) true) (by decide) rfl H400_fin ptTest_fst
theorem I400_fin : (prmOK pI400 400 && intTest pI400 (runFrom pI400 (fmask pI400) (cmask pI400) (hmask pI400) 1 399 (true, (init pI400), (init pI400))) 400 13 true) = true := by
  decide +kernel
theorem I400_ok : RunOK pI400 400 (runFrom pI400 (fmask pI400) (cmask pI400) (hmask pI400) 1 399 (true, (init pI400), (init pI400))) ∧ intTest pI400 (runFrom pI400 (fmask pI400) (cmask pI400) (hmask pI400) 1 399 (true, (init pI400), (init pI400))) 400 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I400_fin) true) (by decide) rfl I400_fin intTest_fst
theorem link400 : linkOK pL400 pH400 pI400 = true := by decide +kernel
theorem cvx400 : ConvexBetweenHumps 400 :=
  cvx_of L400_ok H400_ok I400_ok link400 (by decide)
theorem cenlink400 : cenLinkOK pI400 400 = true := by decide +kernel
theorem cen400 : CenterUniqueMin 400 ∧ DipHyp 400 ∧ OnePointHyps 400 :=
  cen_of L400_ok H400_ok I400_ok link400 cenlink400

/-! ### `N = 401` -/

def pL401 : Prm := ⟨68, 32, 33, 403, 11, 18446744073709551616, 351168166245477939, 351168166245477939⟩
def pH401 : Prm := ⟨68, 32, 33, 403, 11, 18446744073709551616, 351176962338500147, 351176962338500147⟩
def pI401 : Prm := ⟨58, 29, 26, 403, 11, 18446744073709551616, 351168166245477939, 351176962338500147⟩
theorem L401_fin : (prmOK pL401 401 && ptTest pL401 (runFrom pL401 (fmask pL401) (cmask pL401) (hmask pL401) 1 400 (true, (init pL401), (init pL401))) 401 201 false) = true := by
  decide +kernel
theorem L401_ok : RunOK pL401 401 (runFrom pL401 (fmask pL401) (cmask pL401) (hmask pL401) 1 400 (true, (init pL401), (init pL401))) ∧ ptTest pL401 (runFrom pL401 (fmask pL401) (cmask pL401) (hmask pL401) 1 400 (true, (init pL401), (init pL401))) 401 201 false = true :=
  fin_run (runOK_init (prmOK_of_and L401_fin) true) (by decide) rfl L401_fin ptTest_fst
theorem H401_fin : (prmOK pH401 401 && ptTest pH401 (runFrom pH401 (fmask pH401) (cmask pH401) (hmask pH401) 1 400 (true, (init pH401), (init pH401))) 401 201 true) = true := by
  decide +kernel
theorem H401_ok : RunOK pH401 401 (runFrom pH401 (fmask pH401) (cmask pH401) (hmask pH401) 1 400 (true, (init pH401), (init pH401))) ∧ ptTest pH401 (runFrom pH401 (fmask pH401) (cmask pH401) (hmask pH401) 1 400 (true, (init pH401), (init pH401))) 401 201 true = true :=
  fin_run (runOK_init (prmOK_of_and H401_fin) true) (by decide) rfl H401_fin ptTest_fst
theorem I401_fin : (prmOK pI401 401 && intTest pI401 (runFrom pI401 (fmask pI401) (cmask pI401) (hmask pI401) 1 400 (true, (init pI401), (init pI401))) 401 13 false) = true := by
  decide +kernel
theorem I401_ok : RunOK pI401 401 (runFrom pI401 (fmask pI401) (cmask pI401) (hmask pI401) 1 400 (true, (init pI401), (init pI401))) ∧ intTest pI401 (runFrom pI401 (fmask pI401) (cmask pI401) (hmask pI401) 1 400 (true, (init pI401), (init pI401))) 401 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I401_fin) true) (by decide) rfl I401_fin intTest_fst
theorem link401 : linkOK pL401 pH401 pI401 = true := by decide +kernel
theorem cvx401 : ConvexBetweenHumps 401 :=
  cvx_of L401_ok H401_ok I401_ok link401 (by decide)

/-! ### `N = 402` -/

def pL402 : Prm := ⟨68, 32, 33, 404, 11, 18446744073709551616, 350509846325177703, 350509846325177703⟩
def pH402 : Prm := ⟨68, 32, 33, 404, 11, 18446744073709551616, 350518642418199911, 350518642418199911⟩
def pI402 : Prm := ⟨59, 28, 28, 404, 11, 18446744073709551616, 350509846325177703, 350518642418199911⟩
theorem L402_fin : (prmOK pL402 402 && ptTest pL402 (runFrom pL402 (fmask pL402) (cmask pL402) (hmask pL402) 1 401 (true, (init pL402), (init pL402))) 402 201 false) = true := by
  decide +kernel
theorem L402_ok : RunOK pL402 402 (runFrom pL402 (fmask pL402) (cmask pL402) (hmask pL402) 1 401 (true, (init pL402), (init pL402))) ∧ ptTest pL402 (runFrom pL402 (fmask pL402) (cmask pL402) (hmask pL402) 1 401 (true, (init pL402), (init pL402))) 402 201 false = true :=
  fin_run (runOK_init (prmOK_of_and L402_fin) true) (by decide) rfl L402_fin ptTest_fst
theorem H402_fin : (prmOK pH402 402 && ptTest pH402 (runFrom pH402 (fmask pH402) (cmask pH402) (hmask pH402) 1 401 (true, (init pH402), (init pH402))) 402 201 true) = true := by
  decide +kernel
theorem H402_ok : RunOK pH402 402 (runFrom pH402 (fmask pH402) (cmask pH402) (hmask pH402) 1 401 (true, (init pH402), (init pH402))) ∧ ptTest pH402 (runFrom pH402 (fmask pH402) (cmask pH402) (hmask pH402) 1 401 (true, (init pH402), (init pH402))) 402 201 true = true :=
  fin_run (runOK_init (prmOK_of_and H402_fin) true) (by decide) rfl H402_fin ptTest_fst
theorem I402_fin : (prmOK pI402 402 && intTest pI402 (runFrom pI402 (fmask pI402) (cmask pI402) (hmask pI402) 1 401 (true, (init pI402), (init pI402))) 402 13 true) = true := by
  decide +kernel
theorem I402_ok : RunOK pI402 402 (runFrom pI402 (fmask pI402) (cmask pI402) (hmask pI402) 1 401 (true, (init pI402), (init pI402))) ∧ intTest pI402 (runFrom pI402 (fmask pI402) (cmask pI402) (hmask pI402) 1 401 (true, (init pI402), (init pI402))) 402 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I402_fin) true) (by decide) rfl I402_fin intTest_fst
theorem link402 : linkOK pL402 pH402 pI402 = true := by decide +kernel
theorem cvx402 : ConvexBetweenHumps 402 :=
  cvx_of L402_ok H402_ok I402_ok link402 (by decide)
theorem cenlink402 : cenLinkOK pI402 402 = true := by decide +kernel
theorem cen402 : CenterUniqueMin 402 ∧ DipHyp 402 ∧ OnePointHyps 402 :=
  cen_of L402_ok H402_ok I402_ok link402 cenlink402

/-! ### `N = 403` -/

def pL403 : Prm := ⟨68, 32, 33, 405, 11, 18446744073709551616, 349852411759439891, 349852411759439891⟩
def pH403 : Prm := ⟨68, 32, 33, 405, 11, 18446744073709551616, 349861207852462099, 349861207852462099⟩
def pI403 : Prm := ⟨58, 29, 26, 405, 11, 18446744073709551616, 349852411759439891, 349861207852462099⟩
theorem L403_fin : (prmOK pL403 403 && ptTest pL403 (runFrom pL403 (fmask pL403) (cmask pL403) (hmask pL403) 1 402 (true, (init pL403), (init pL403))) 403 202 false) = true := by
  decide +kernel
theorem L403_ok : RunOK pL403 403 (runFrom pL403 (fmask pL403) (cmask pL403) (hmask pL403) 1 402 (true, (init pL403), (init pL403))) ∧ ptTest pL403 (runFrom pL403 (fmask pL403) (cmask pL403) (hmask pL403) 1 402 (true, (init pL403), (init pL403))) 403 202 false = true :=
  fin_run (runOK_init (prmOK_of_and L403_fin) true) (by decide) rfl L403_fin ptTest_fst
theorem H403_fin : (prmOK pH403 403 && ptTest pH403 (runFrom pH403 (fmask pH403) (cmask pH403) (hmask pH403) 1 402 (true, (init pH403), (init pH403))) 403 202 true) = true := by
  decide +kernel
theorem H403_ok : RunOK pH403 403 (runFrom pH403 (fmask pH403) (cmask pH403) (hmask pH403) 1 402 (true, (init pH403), (init pH403))) ∧ ptTest pH403 (runFrom pH403 (fmask pH403) (cmask pH403) (hmask pH403) 1 402 (true, (init pH403), (init pH403))) 403 202 true = true :=
  fin_run (runOK_init (prmOK_of_and H403_fin) true) (by decide) rfl H403_fin ptTest_fst
theorem I403_fin : (prmOK pI403 403 && intTest pI403 (runFrom pI403 (fmask pI403) (cmask pI403) (hmask pI403) 1 402 (true, (init pI403), (init pI403))) 403 13 false) = true := by
  decide +kernel
theorem I403_ok : RunOK pI403 403 (runFrom pI403 (fmask pI403) (cmask pI403) (hmask pI403) 1 402 (true, (init pI403), (init pI403))) ∧ intTest pI403 (runFrom pI403 (fmask pI403) (cmask pI403) (hmask pI403) 1 402 (true, (init pI403), (init pI403))) 403 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I403_fin) true) (by decide) rfl I403_fin intTest_fst
theorem link403 : linkOK pL403 pH403 pI403 = true := by decide +kernel
theorem cvx403 : ConvexBetweenHumps 403 :=
  cvx_of L403_ok H403_ok I403_ok link403 (by decide)

/-! ### `N = 404` -/

def pL404 : Prm := ⟨68, 32, 33, 406, 11, 18446744073709551616, 349199557794632453, 349199557794632453⟩
def pH404 : Prm := ⟨68, 32, 33, 406, 11, 18446744073709551616, 349208353887654661, 349208353887654661⟩
def pI404 : Prm := ⟨58, 29, 26, 406, 11, 18446744073709551616, 349199557794632453, 349208353887654661⟩
theorem L404_fin : (prmOK pL404 404 && ptTest pL404 (runFrom pL404 (fmask pL404) (cmask pL404) (hmask pL404) 1 403 (true, (init pL404), (init pL404))) 404 202 false) = true := by
  decide +kernel
theorem L404_ok : RunOK pL404 404 (runFrom pL404 (fmask pL404) (cmask pL404) (hmask pL404) 1 403 (true, (init pL404), (init pL404))) ∧ ptTest pL404 (runFrom pL404 (fmask pL404) (cmask pL404) (hmask pL404) 1 403 (true, (init pL404), (init pL404))) 404 202 false = true :=
  fin_run (runOK_init (prmOK_of_and L404_fin) true) (by decide) rfl L404_fin ptTest_fst
theorem H404_fin : (prmOK pH404 404 && ptTest pH404 (runFrom pH404 (fmask pH404) (cmask pH404) (hmask pH404) 1 403 (true, (init pH404), (init pH404))) 404 202 true) = true := by
  decide +kernel
theorem H404_ok : RunOK pH404 404 (runFrom pH404 (fmask pH404) (cmask pH404) (hmask pH404) 1 403 (true, (init pH404), (init pH404))) ∧ ptTest pH404 (runFrom pH404 (fmask pH404) (cmask pH404) (hmask pH404) 1 403 (true, (init pH404), (init pH404))) 404 202 true = true :=
  fin_run (runOK_init (prmOK_of_and H404_fin) true) (by decide) rfl H404_fin ptTest_fst
theorem I404_fin : (prmOK pI404 404 && intTest pI404 (runFrom pI404 (fmask pI404) (cmask pI404) (hmask pI404) 1 403 (true, (init pI404), (init pI404))) 404 13 true) = true := by
  decide +kernel
theorem I404_ok : RunOK pI404 404 (runFrom pI404 (fmask pI404) (cmask pI404) (hmask pI404) 1 403 (true, (init pI404), (init pI404))) ∧ intTest pI404 (runFrom pI404 (fmask pI404) (cmask pI404) (hmask pI404) 1 403 (true, (init pI404), (init pI404))) 404 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I404_fin) true) (by decide) rfl I404_fin intTest_fst
theorem link404 : linkOK pL404 pH404 pI404 = true := by decide +kernel
theorem cvx404 : ConvexBetweenHumps 404 :=
  cvx_of L404_ok H404_ok I404_ok link404 (by decide)
theorem cenlink404 : cenLinkOK pI404 404 = true := by decide +kernel
theorem cen404 : CenterUniqueMin 404 ∧ DipHyp 404 ∧ OnePointHyps 404 :=
  cen_of L404_ok H404_ok I404_ok link404 cenlink404

/-! ### `N = 405` -/

def pL405 : Prm := ⟨68, 32, 33, 407, 11, 18446744073709551616, 348547581456124008, 348547581456124008⟩
def pH405 : Prm := ⟨68, 32, 33, 407, 11, 18446744073709551616, 348556377549146216, 348556377549146216⟩
def pI405 : Prm := ⟨58, 29, 26, 407, 11, 18446744073709551616, 348547581456124008, 348556377549146216⟩
theorem L405_fin : (prmOK pL405 405 && ptTest pL405 (runFrom pL405 (fmask pL405) (cmask pL405) (hmask pL405) 1 404 (true, (init pL405), (init pL405))) 405 203 false) = true := by
  decide +kernel
theorem L405_ok : RunOK pL405 405 (runFrom pL405 (fmask pL405) (cmask pL405) (hmask pL405) 1 404 (true, (init pL405), (init pL405))) ∧ ptTest pL405 (runFrom pL405 (fmask pL405) (cmask pL405) (hmask pL405) 1 404 (true, (init pL405), (init pL405))) 405 203 false = true :=
  fin_run (runOK_init (prmOK_of_and L405_fin) true) (by decide) rfl L405_fin ptTest_fst
theorem H405_fin : (prmOK pH405 405 && ptTest pH405 (runFrom pH405 (fmask pH405) (cmask pH405) (hmask pH405) 1 404 (true, (init pH405), (init pH405))) 405 203 true) = true := by
  decide +kernel
theorem H405_ok : RunOK pH405 405 (runFrom pH405 (fmask pH405) (cmask pH405) (hmask pH405) 1 404 (true, (init pH405), (init pH405))) ∧ ptTest pH405 (runFrom pH405 (fmask pH405) (cmask pH405) (hmask pH405) 1 404 (true, (init pH405), (init pH405))) 405 203 true = true :=
  fin_run (runOK_init (prmOK_of_and H405_fin) true) (by decide) rfl H405_fin ptTest_fst
theorem I405_fin : (prmOK pI405 405 && intTest pI405 (runFrom pI405 (fmask pI405) (cmask pI405) (hmask pI405) 1 404 (true, (init pI405), (init pI405))) 405 13 false) = true := by
  decide +kernel
theorem I405_ok : RunOK pI405 405 (runFrom pI405 (fmask pI405) (cmask pI405) (hmask pI405) 1 404 (true, (init pI405), (init pI405))) ∧ intTest pI405 (runFrom pI405 (fmask pI405) (cmask pI405) (hmask pI405) 1 404 (true, (init pI405), (init pI405))) 405 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I405_fin) true) (by decide) rfl I405_fin intTest_fst
theorem link405 : linkOK pL405 pH405 pI405 = true := by decide +kernel
theorem cvx405 : ConvexBetweenHumps 405 :=
  cvx_of L405_ok H405_ok I405_ok link405 (by decide)

/-! ### `N = 406` -/

def pL406 : Prm := ⟨68, 32, 33, 408, 11, 18446744073709551616, 347900122804486428, 347900122804486428⟩
def pH406 : Prm := ⟨68, 32, 33, 408, 11, 18446744073709551616, 347908918897508636, 347908918897508636⟩
def pI406 : Prm := ⟨59, 29, 27, 408, 11, 18446744073709551616, 347900122804486428, 347908918897508636⟩
theorem L406_fin : (prmOK pL406 406 && ptTest pL406 (runFrom pL406 (fmask pL406) (cmask pL406) (hmask pL406) 1 405 (true, (init pL406), (init pL406))) 406 203 false) = true := by
  decide +kernel
theorem L406_ok : RunOK pL406 406 (runFrom pL406 (fmask pL406) (cmask pL406) (hmask pL406) 1 405 (true, (init pL406), (init pL406))) ∧ ptTest pL406 (runFrom pL406 (fmask pL406) (cmask pL406) (hmask pL406) 1 405 (true, (init pL406), (init pL406))) 406 203 false = true :=
  fin_run (runOK_init (prmOK_of_and L406_fin) true) (by decide) rfl L406_fin ptTest_fst
theorem H406_fin : (prmOK pH406 406 && ptTest pH406 (runFrom pH406 (fmask pH406) (cmask pH406) (hmask pH406) 1 405 (true, (init pH406), (init pH406))) 406 203 true) = true := by
  decide +kernel
theorem H406_ok : RunOK pH406 406 (runFrom pH406 (fmask pH406) (cmask pH406) (hmask pH406) 1 405 (true, (init pH406), (init pH406))) ∧ ptTest pH406 (runFrom pH406 (fmask pH406) (cmask pH406) (hmask pH406) 1 405 (true, (init pH406), (init pH406))) 406 203 true = true :=
  fin_run (runOK_init (prmOK_of_and H406_fin) true) (by decide) rfl H406_fin ptTest_fst
theorem I406_fin : (prmOK pI406 406 && intTest pI406 (runFrom pI406 (fmask pI406) (cmask pI406) (hmask pI406) 1 405 (true, (init pI406), (init pI406))) 406 13 true) = true := by
  decide +kernel
theorem I406_ok : RunOK pI406 406 (runFrom pI406 (fmask pI406) (cmask pI406) (hmask pI406) 1 405 (true, (init pI406), (init pI406))) ∧ intTest pI406 (runFrom pI406 (fmask pI406) (cmask pI406) (hmask pI406) 1 405 (true, (init pI406), (init pI406))) 406 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I406_fin) true) (by decide) rfl I406_fin intTest_fst
theorem link406 : linkOK pL406 pH406 pI406 = true := by decide +kernel
theorem cvx406 : ConvexBetweenHumps 406 :=
  cvx_of L406_ok H406_ok I406_ok link406 (by decide)
theorem cenlink406 : cenLinkOK pI406 406 = true := by decide +kernel
theorem cen406 : CenterUniqueMin 406 ∧ DipHyp 406 ∧ OnePointHyps 406 :=
  cen_of L406_ok H406_ok I406_ok link406 cenlink406

/-! ### `N = 407` -/

def pL407 : Prm := ⟨68, 32, 33, 409, 11, 18446744073709551616, 347253534128194716, 347253534128194716⟩
def pH407 : Prm := ⟨68, 32, 33, 409, 11, 18446744073709551616, 347262330221216924, 347262330221216924⟩
def pI407 : Prm := ⟨59, 29, 27, 409, 11, 18446744073709551616, 347253534128194716, 347262330221216924⟩
theorem L407_fin : (prmOK pL407 407 && ptTest pL407 (runFrom pL407 (fmask pL407) (cmask pL407) (hmask pL407) 1 406 (true, (init pL407), (init pL407))) 407 204 false) = true := by
  decide +kernel
theorem L407_ok : RunOK pL407 407 (runFrom pL407 (fmask pL407) (cmask pL407) (hmask pL407) 1 406 (true, (init pL407), (init pL407))) ∧ ptTest pL407 (runFrom pL407 (fmask pL407) (cmask pL407) (hmask pL407) 1 406 (true, (init pL407), (init pL407))) 407 204 false = true :=
  fin_run (runOK_init (prmOK_of_and L407_fin) true) (by decide) rfl L407_fin ptTest_fst
theorem H407_fin : (prmOK pH407 407 && ptTest pH407 (runFrom pH407 (fmask pH407) (cmask pH407) (hmask pH407) 1 406 (true, (init pH407), (init pH407))) 407 204 true) = true := by
  decide +kernel
theorem H407_ok : RunOK pH407 407 (runFrom pH407 (fmask pH407) (cmask pH407) (hmask pH407) 1 406 (true, (init pH407), (init pH407))) ∧ ptTest pH407 (runFrom pH407 (fmask pH407) (cmask pH407) (hmask pH407) 1 406 (true, (init pH407), (init pH407))) 407 204 true = true :=
  fin_run (runOK_init (prmOK_of_and H407_fin) true) (by decide) rfl H407_fin ptTest_fst
theorem I407_fin : (prmOK pI407 407 && intTest pI407 (runFrom pI407 (fmask pI407) (cmask pI407) (hmask pI407) 1 406 (true, (init pI407), (init pI407))) 407 13 false) = true := by
  decide +kernel
theorem I407_ok : RunOK pI407 407 (runFrom pI407 (fmask pI407) (cmask pI407) (hmask pI407) 1 406 (true, (init pI407), (init pI407))) ∧ intTest pI407 (runFrom pI407 (fmask pI407) (cmask pI407) (hmask pI407) 1 406 (true, (init pI407), (init pI407))) 407 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I407_fin) true) (by decide) rfl I407_fin intTest_fst
theorem link407 : linkOK pL407 pH407 pI407 = true := by decide +kernel
theorem cvx407 : ConvexBetweenHumps 407 :=
  cvx_of L407_ok H407_ok I407_ok link407 (by decide)

/-! ### `N = 408` -/

def pL408 : Prm := ⟨68, 32, 33, 410, 11, 18446744073709551616, 346611401387375745, 346611401387375745⟩
def pH408 : Prm := ⟨68, 32, 33, 410, 11, 18446744073709551616, 346620197480397953, 346620197480397953⟩
def pI408 : Prm := ⟨59, 29, 27, 410, 11, 18446744073709551616, 346611401387375745, 346620197480397953⟩
theorem L408_fin : (prmOK pL408 408 && ptTest pL408 (runFrom pL408 (fmask pL408) (cmask pL408) (hmask pL408) 1 407 (true, (init pL408), (init pL408))) 408 204 false) = true := by
  decide +kernel
theorem L408_ok : RunOK pL408 408 (runFrom pL408 (fmask pL408) (cmask pL408) (hmask pL408) 1 407 (true, (init pL408), (init pL408))) ∧ ptTest pL408 (runFrom pL408 (fmask pL408) (cmask pL408) (hmask pL408) 1 407 (true, (init pL408), (init pL408))) 408 204 false = true :=
  fin_run (runOK_init (prmOK_of_and L408_fin) true) (by decide) rfl L408_fin ptTest_fst
theorem H408_fin : (prmOK pH408 408 && ptTest pH408 (runFrom pH408 (fmask pH408) (cmask pH408) (hmask pH408) 1 407 (true, (init pH408), (init pH408))) 408 204 true) = true := by
  decide +kernel
theorem H408_ok : RunOK pH408 408 (runFrom pH408 (fmask pH408) (cmask pH408) (hmask pH408) 1 407 (true, (init pH408), (init pH408))) ∧ ptTest pH408 (runFrom pH408 (fmask pH408) (cmask pH408) (hmask pH408) 1 407 (true, (init pH408), (init pH408))) 408 204 true = true :=
  fin_run (runOK_init (prmOK_of_and H408_fin) true) (by decide) rfl H408_fin ptTest_fst
theorem I408_fin : (prmOK pI408 408 && intTest pI408 (runFrom pI408 (fmask pI408) (cmask pI408) (hmask pI408) 1 407 (true, (init pI408), (init pI408))) 408 13 true) = true := by
  decide +kernel
theorem I408_ok : RunOK pI408 408 (runFrom pI408 (fmask pI408) (cmask pI408) (hmask pI408) 1 407 (true, (init pI408), (init pI408))) ∧ intTest pI408 (runFrom pI408 (fmask pI408) (cmask pI408) (hmask pI408) 1 407 (true, (init pI408), (init pI408))) 408 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I408_fin) true) (by decide) rfl I408_fin intTest_fst
theorem link408 : linkOK pL408 pH408 pI408 = true := by decide +kernel
theorem cvx408 : ConvexBetweenHumps 408 :=
  cvx_of L408_ok H408_ok I408_ok link408 (by decide)
theorem cenlink408 : cenLinkOK pI408 408 = true := by decide +kernel
theorem cen408 : CenterUniqueMin 408 ∧ DipHyp 408 ∧ OnePointHyps 408 :=
  cen_of L408_ok H408_ok I408_ok link408 cenlink408

/-! ### `N = 409` -/

def pL409 : Prm := ⟨68, 32, 33, 411, 11, 18446744073709551616, 345970131047780207, 345970131047780207⟩
def pH409 : Prm := ⟨68, 32, 33, 411, 11, 18446744073709551616, 345978927140802415, 345978927140802415⟩
def pI409 : Prm := ⟨59, 29, 27, 411, 11, 18446744073709551616, 345970131047780207, 345978927140802415⟩
theorem L409_fin : (prmOK pL409 409 && ptTest pL409 (runFrom pL409 (fmask pL409) (cmask pL409) (hmask pL409) 1 408 (true, (init pL409), (init pL409))) 409 205 false) = true := by
  decide +kernel
theorem L409_ok : RunOK pL409 409 (runFrom pL409 (fmask pL409) (cmask pL409) (hmask pL409) 1 408 (true, (init pL409), (init pL409))) ∧ ptTest pL409 (runFrom pL409 (fmask pL409) (cmask pL409) (hmask pL409) 1 408 (true, (init pL409), (init pL409))) 409 205 false = true :=
  fin_run (runOK_init (prmOK_of_and L409_fin) true) (by decide) rfl L409_fin ptTest_fst
theorem H409_fin : (prmOK pH409 409 && ptTest pH409 (runFrom pH409 (fmask pH409) (cmask pH409) (hmask pH409) 1 408 (true, (init pH409), (init pH409))) 409 205 true) = true := by
  decide +kernel
theorem H409_ok : RunOK pH409 409 (runFrom pH409 (fmask pH409) (cmask pH409) (hmask pH409) 1 408 (true, (init pH409), (init pH409))) ∧ ptTest pH409 (runFrom pH409 (fmask pH409) (cmask pH409) (hmask pH409) 1 408 (true, (init pH409), (init pH409))) 409 205 true = true :=
  fin_run (runOK_init (prmOK_of_and H409_fin) true) (by decide) rfl H409_fin ptTest_fst
theorem I409_fin : (prmOK pI409 409 && intTest pI409 (runFrom pI409 (fmask pI409) (cmask pI409) (hmask pI409) 1 408 (true, (init pI409), (init pI409))) 409 13 false) = true := by
  decide +kernel
theorem I409_ok : RunOK pI409 409 (runFrom pI409 (fmask pI409) (cmask pI409) (hmask pI409) 1 408 (true, (init pI409), (init pI409))) ∧ intTest pI409 (runFrom pI409 (fmask pI409) (cmask pI409) (hmask pI409) 1 408 (true, (init pI409), (init pI409))) 409 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I409_fin) true) (by decide) rfl I409_fin intTest_fst
theorem link409 : linkOK pL409 pH409 pI409 = true := by decide +kernel
theorem cvx409 : ConvexBetweenHumps 409 :=
  cvx_of L409_ok H409_ok I409_ok link409 (by decide)

/-! ### `N = 410` -/

def pL410 : Prm := ⟨68, 32, 33, 412, 11, 18446744073709551616, 345333256028062211, 345333256028062211⟩
def pH410 : Prm := ⟨68, 32, 33, 412, 11, 18446744073709551616, 345342052121084419, 345342052121084419⟩
def pI410 : Prm := ⟨59, 29, 27, 412, 11, 18446744073709551616, 345333256028062211, 345342052121084419⟩
theorem L410_fin : (prmOK pL410 410 && ptTest pL410 (runFrom pL410 (fmask pL410) (cmask pL410) (hmask pL410) 1 409 (true, (init pL410), (init pL410))) 410 205 false) = true := by
  decide +kernel
theorem L410_ok : RunOK pL410 410 (runFrom pL410 (fmask pL410) (cmask pL410) (hmask pL410) 1 409 (true, (init pL410), (init pL410))) ∧ ptTest pL410 (runFrom pL410 (fmask pL410) (cmask pL410) (hmask pL410) 1 409 (true, (init pL410), (init pL410))) 410 205 false = true :=
  fin_run (runOK_init (prmOK_of_and L410_fin) true) (by decide) rfl L410_fin ptTest_fst
theorem H410_fin : (prmOK pH410 410 && ptTest pH410 (runFrom pH410 (fmask pH410) (cmask pH410) (hmask pH410) 1 409 (true, (init pH410), (init pH410))) 410 205 true) = true := by
  decide +kernel
theorem H410_ok : RunOK pH410 410 (runFrom pH410 (fmask pH410) (cmask pH410) (hmask pH410) 1 409 (true, (init pH410), (init pH410))) ∧ ptTest pH410 (runFrom pH410 (fmask pH410) (cmask pH410) (hmask pH410) 1 409 (true, (init pH410), (init pH410))) 410 205 true = true :=
  fin_run (runOK_init (prmOK_of_and H410_fin) true) (by decide) rfl H410_fin ptTest_fst
theorem I410_fin : (prmOK pI410 410 && intTest pI410 (runFrom pI410 (fmask pI410) (cmask pI410) (hmask pI410) 1 409 (true, (init pI410), (init pI410))) 410 13 true) = true := by
  decide +kernel
theorem I410_ok : RunOK pI410 410 (runFrom pI410 (fmask pI410) (cmask pI410) (hmask pI410) 1 409 (true, (init pI410), (init pI410))) ∧ intTest pI410 (runFrom pI410 (fmask pI410) (cmask pI410) (hmask pI410) 1 409 (true, (init pI410), (init pI410))) 410 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I410_fin) true) (by decide) rfl I410_fin intTest_fst
theorem link410 : linkOK pL410 pH410 pI410 = true := by decide +kernel
theorem cvx410 : ConvexBetweenHumps 410 :=
  cvx_of L410_ok H410_ok I410_ok link410 (by decide)
theorem cenlink410 : cenLinkOK pI410 410 = true := by decide +kernel
theorem cen410 : CenterUniqueMin 410 ∧ DipHyp 410 ∧ OnePointHyps 410 :=
  cen_of L410_ok H410_ok I410_ok link410 cenlink410

/-! ### `N = 411` -/

def pL411 : Prm := ⟨68, 32, 33, 413, 11, 18446744073709551616, 344697235911630264, 344697235911630264⟩
def pH411 : Prm := ⟨68, 32, 33, 413, 11, 18446744073709551616, 344706032004652472, 344706032004652472⟩
def pI411 : Prm := ⟨59, 29, 27, 413, 11, 18446744073709551616, 344697235911630264, 344706032004652472⟩
theorem L411_fin : (prmOK pL411 411 && ptTest pL411 (runFrom pL411 (fmask pL411) (cmask pL411) (hmask pL411) 1 410 (true, (init pL411), (init pL411))) 411 206 false) = true := by
  decide +kernel
theorem L411_ok : RunOK pL411 411 (runFrom pL411 (fmask pL411) (cmask pL411) (hmask pL411) 1 410 (true, (init pL411), (init pL411))) ∧ ptTest pL411 (runFrom pL411 (fmask pL411) (cmask pL411) (hmask pL411) 1 410 (true, (init pL411), (init pL411))) 411 206 false = true :=
  fin_run (runOK_init (prmOK_of_and L411_fin) true) (by decide) rfl L411_fin ptTest_fst
theorem H411_fin : (prmOK pH411 411 && ptTest pH411 (runFrom pH411 (fmask pH411) (cmask pH411) (hmask pH411) 1 410 (true, (init pH411), (init pH411))) 411 206 true) = true := by
  decide +kernel
theorem H411_ok : RunOK pH411 411 (runFrom pH411 (fmask pH411) (cmask pH411) (hmask pH411) 1 410 (true, (init pH411), (init pH411))) ∧ ptTest pH411 (runFrom pH411 (fmask pH411) (cmask pH411) (hmask pH411) 1 410 (true, (init pH411), (init pH411))) 411 206 true = true :=
  fin_run (runOK_init (prmOK_of_and H411_fin) true) (by decide) rfl H411_fin ptTest_fst
theorem I411_fin : (prmOK pI411 411 && intTest pI411 (runFrom pI411 (fmask pI411) (cmask pI411) (hmask pI411) 1 410 (true, (init pI411), (init pI411))) 411 13 false) = true := by
  decide +kernel
theorem I411_ok : RunOK pI411 411 (runFrom pI411 (fmask pI411) (cmask pI411) (hmask pI411) 1 410 (true, (init pI411), (init pI411))) ∧ intTest pI411 (runFrom pI411 (fmask pI411) (cmask pI411) (hmask pI411) 1 410 (true, (init pI411), (init pI411))) 411 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I411_fin) true) (by decide) rfl I411_fin intTest_fst
theorem link411 : linkOK pL411 pH411 pI411 = true := by decide +kernel
theorem cvx411 : ConvexBetweenHumps 411 :=
  cvx_of L411_ok H411_ok I411_ok link411 (by decide)

/-! ### `N = 412` -/

def pL412 : Prm := ⟨68, 32, 33, 414, 11, 18446744073709551616, 344065551609033871, 344065551609033871⟩
def pH412 : Prm := ⟨68, 32, 33, 414, 11, 18446744073709551616, 344074347702056079, 344074347702056079⟩
def pI412 : Prm := ⟨59, 29, 27, 414, 11, 18446744073709551616, 344065551609033871, 344074347702056079⟩
theorem L412_fin : (prmOK pL412 412 && ptTest pL412 (runFrom pL412 (fmask pL412) (cmask pL412) (hmask pL412) 1 411 (true, (init pL412), (init pL412))) 412 206 false) = true := by
  decide +kernel
theorem L412_ok : RunOK pL412 412 (runFrom pL412 (fmask pL412) (cmask pL412) (hmask pL412) 1 411 (true, (init pL412), (init pL412))) ∧ ptTest pL412 (runFrom pL412 (fmask pL412) (cmask pL412) (hmask pL412) 1 411 (true, (init pL412), (init pL412))) 412 206 false = true :=
  fin_run (runOK_init (prmOK_of_and L412_fin) true) (by decide) rfl L412_fin ptTest_fst
theorem H412_fin : (prmOK pH412 412 && ptTest pH412 (runFrom pH412 (fmask pH412) (cmask pH412) (hmask pH412) 1 411 (true, (init pH412), (init pH412))) 412 206 true) = true := by
  decide +kernel
theorem H412_ok : RunOK pH412 412 (runFrom pH412 (fmask pH412) (cmask pH412) (hmask pH412) 1 411 (true, (init pH412), (init pH412))) ∧ ptTest pH412 (runFrom pH412 (fmask pH412) (cmask pH412) (hmask pH412) 1 411 (true, (init pH412), (init pH412))) 412 206 true = true :=
  fin_run (runOK_init (prmOK_of_and H412_fin) true) (by decide) rfl H412_fin ptTest_fst
theorem I412_fin : (prmOK pI412 412 && intTest pI412 (runFrom pI412 (fmask pI412) (cmask pI412) (hmask pI412) 1 411 (true, (init pI412), (init pI412))) 412 13 true) = true := by
  decide +kernel
theorem I412_ok : RunOK pI412 412 (runFrom pI412 (fmask pI412) (cmask pI412) (hmask pI412) 1 411 (true, (init pI412), (init pI412))) ∧ intTest pI412 (runFrom pI412 (fmask pI412) (cmask pI412) (hmask pI412) 1 411 (true, (init pI412), (init pI412))) 412 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I412_fin) true) (by decide) rfl I412_fin intTest_fst
theorem link412 : linkOK pL412 pH412 pI412 = true := by decide +kernel
theorem cvx412 : ConvexBetweenHumps 412 :=
  cvx_of L412_ok H412_ok I412_ok link412 (by decide)
theorem cenlink412 : cenLinkOK pI412 412 = true := by decide +kernel
theorem cen412 : CenterUniqueMin 412 ∧ DipHyp 412 ∧ OnePointHyps 412 :=
  cen_of L412_ok H412_ok I412_ok link412 cenlink412

/-! ### `N = 413` -/

def pL413 : Prm := ⟨68, 32, 33, 415, 11, 18446744073709551616, 343434714787491582, 343434714787491582⟩
def pH413 : Prm := ⟨68, 32, 33, 415, 11, 18446744073709551616, 343443510880513790, 343443510880513790⟩
def pI413 : Prm := ⟨59, 29, 27, 415, 11, 18446744073709551616, 343434714787491582, 343443510880513790⟩
theorem L413_fin : (prmOK pL413 413 && ptTest pL413 (runFrom pL413 (fmask pL413) (cmask pL413) (hmask pL413) 1 412 (true, (init pL413), (init pL413))) 413 207 false) = true := by
  decide +kernel
theorem L413_ok : RunOK pL413 413 (runFrom pL413 (fmask pL413) (cmask pL413) (hmask pL413) 1 412 (true, (init pL413), (init pL413))) ∧ ptTest pL413 (runFrom pL413 (fmask pL413) (cmask pL413) (hmask pL413) 1 412 (true, (init pL413), (init pL413))) 413 207 false = true :=
  fin_run (runOK_init (prmOK_of_and L413_fin) true) (by decide) rfl L413_fin ptTest_fst
theorem H413_fin : (prmOK pH413 413 && ptTest pH413 (runFrom pH413 (fmask pH413) (cmask pH413) (hmask pH413) 1 412 (true, (init pH413), (init pH413))) 413 207 true) = true := by
  decide +kernel
theorem H413_ok : RunOK pH413 413 (runFrom pH413 (fmask pH413) (cmask pH413) (hmask pH413) 1 412 (true, (init pH413), (init pH413))) ∧ ptTest pH413 (runFrom pH413 (fmask pH413) (cmask pH413) (hmask pH413) 1 412 (true, (init pH413), (init pH413))) 413 207 true = true :=
  fin_run (runOK_init (prmOK_of_and H413_fin) true) (by decide) rfl H413_fin ptTest_fst
theorem I413_fin : (prmOK pI413 413 && intTest pI413 (runFrom pI413 (fmask pI413) (cmask pI413) (hmask pI413) 1 412 (true, (init pI413), (init pI413))) 413 13 false) = true := by
  decide +kernel
theorem I413_ok : RunOK pI413 413 (runFrom pI413 (fmask pI413) (cmask pI413) (hmask pI413) 1 412 (true, (init pI413), (init pI413))) ∧ intTest pI413 (runFrom pI413 (fmask pI413) (cmask pI413) (hmask pI413) 1 412 (true, (init pI413), (init pI413))) 413 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I413_fin) true) (by decide) rfl I413_fin intTest_fst
theorem link413 : linkOK pL413 pH413 pI413 = true := by decide +kernel
theorem cvx413 : ConvexBetweenHumps 413 :=
  cvx_of L413_ok H413_ok I413_ok link413 (by decide)

/-! ### `N = 414` -/

def pL414 : Prm := ⟨68, 32, 33, 416, 11, 18446744073709551616, 342808155357821114, 342808155357821114⟩
def pH414 : Prm := ⟨68, 32, 33, 416, 11, 18446744073709551616, 342816951450843322, 342816951450843322⟩
def pI414 : Prm := ⟨59, 29, 27, 416, 11, 18446744073709551616, 342808155357821114, 342816951450843322⟩
theorem L414_fin : (prmOK pL414 414 && ptTest pL414 (runFrom pL414 (fmask pL414) (cmask pL414) (hmask pL414) 1 413 (true, (init pL414), (init pL414))) 414 207 false) = true := by
  decide +kernel
theorem L414_ok : RunOK pL414 414 (runFrom pL414 (fmask pL414) (cmask pL414) (hmask pL414) 1 413 (true, (init pL414), (init pL414))) ∧ ptTest pL414 (runFrom pL414 (fmask pL414) (cmask pL414) (hmask pL414) 1 413 (true, (init pL414), (init pL414))) 414 207 false = true :=
  fin_run (runOK_init (prmOK_of_and L414_fin) true) (by decide) rfl L414_fin ptTest_fst
theorem H414_fin : (prmOK pH414 414 && ptTest pH414 (runFrom pH414 (fmask pH414) (cmask pH414) (hmask pH414) 1 413 (true, (init pH414), (init pH414))) 414 207 true) = true := by
  decide +kernel
theorem H414_ok : RunOK pH414 414 (runFrom pH414 (fmask pH414) (cmask pH414) (hmask pH414) 1 413 (true, (init pH414), (init pH414))) ∧ ptTest pH414 (runFrom pH414 (fmask pH414) (cmask pH414) (hmask pH414) 1 413 (true, (init pH414), (init pH414))) 414 207 true = true :=
  fin_run (runOK_init (prmOK_of_and H414_fin) true) (by decide) rfl H414_fin ptTest_fst
theorem I414_fin : (prmOK pI414 414 && intTest pI414 (runFrom pI414 (fmask pI414) (cmask pI414) (hmask pI414) 1 413 (true, (init pI414), (init pI414))) 414 13 true) = true := by
  decide +kernel
theorem I414_ok : RunOK pI414 414 (runFrom pI414 (fmask pI414) (cmask pI414) (hmask pI414) 1 413 (true, (init pI414), (init pI414))) ∧ intTest pI414 (runFrom pI414 (fmask pI414) (cmask pI414) (hmask pI414) 1 413 (true, (init pI414), (init pI414))) 414 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I414_fin) true) (by decide) rfl I414_fin intTest_fst
theorem link414 : linkOK pL414 pH414 pI414 = true := by decide +kernel
theorem cvx414 : ConvexBetweenHumps 414 :=
  cvx_of L414_ok H414_ok I414_ok link414 (by decide)
theorem cenlink414 : cenLinkOK pI414 414 = true := by decide +kernel
theorem cen414 : CenterUniqueMin 414 ∧ DipHyp 414 ∧ OnePointHyps 414 :=
  cen_of L414_ok H414_ok I414_ok link414 cenlink414

/-! ### `N = 415` -/

def pL415 : Prm := ⟨68, 32, 33, 417, 11, 18446744073709551616, 342182436062014160, 342182436062014160⟩
def pH415 : Prm := ⟨68, 32, 33, 417, 11, 18446744073709551616, 342191232155036368, 342191232155036368⟩
def pI415 : Prm := ⟨59, 29, 27, 417, 11, 18446744073709551616, 342182436062014160, 342191232155036368⟩
theorem L415_fin : (prmOK pL415 415 && ptTest pL415 (runFrom pL415 (fmask pL415) (cmask pL415) (hmask pL415) 1 414 (true, (init pL415), (init pL415))) 415 208 false) = true := by
  decide +kernel
theorem L415_ok : RunOK pL415 415 (runFrom pL415 (fmask pL415) (cmask pL415) (hmask pL415) 1 414 (true, (init pL415), (init pL415))) ∧ ptTest pL415 (runFrom pL415 (fmask pL415) (cmask pL415) (hmask pL415) 1 414 (true, (init pL415), (init pL415))) 415 208 false = true :=
  fin_run (runOK_init (prmOK_of_and L415_fin) true) (by decide) rfl L415_fin ptTest_fst
theorem H415_fin : (prmOK pH415 415 && ptTest pH415 (runFrom pH415 (fmask pH415) (cmask pH415) (hmask pH415) 1 414 (true, (init pH415), (init pH415))) 415 208 true) = true := by
  decide +kernel
theorem H415_ok : RunOK pH415 415 (runFrom pH415 (fmask pH415) (cmask pH415) (hmask pH415) 1 414 (true, (init pH415), (init pH415))) ∧ ptTest pH415 (runFrom pH415 (fmask pH415) (cmask pH415) (hmask pH415) 1 414 (true, (init pH415), (init pH415))) 415 208 true = true :=
  fin_run (runOK_init (prmOK_of_and H415_fin) true) (by decide) rfl H415_fin ptTest_fst
theorem I415_fin : (prmOK pI415 415 && intTest pI415 (runFrom pI415 (fmask pI415) (cmask pI415) (hmask pI415) 1 414 (true, (init pI415), (init pI415))) 415 13 false) = true := by
  decide +kernel
theorem I415_ok : RunOK pI415 415 (runFrom pI415 (fmask pI415) (cmask pI415) (hmask pI415) 1 414 (true, (init pI415), (init pI415))) ∧ intTest pI415 (runFrom pI415 (fmask pI415) (cmask pI415) (hmask pI415) 1 414 (true, (init pI415), (init pI415))) 415 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I415_fin) true) (by decide) rfl I415_fin intTest_fst
theorem link415 : linkOK pL415 pH415 pI415 = true := by decide +kernel
theorem cvx415 : ConvexBetweenHumps 415 :=
  cvx_of L415_ok H415_ok I415_ok link415 (by decide)

/-! ### `N = 416` -/

def pL416 : Prm := ⟨68, 32, 33, 418, 11, 18446744073709551616, 341560936795438018, 341560936795438018⟩
def pH416 : Prm := ⟨68, 32, 33, 418, 11, 18446744073709551616, 341569732888460226, 341569732888460226⟩
def pI416 : Prm := ⟨59, 29, 27, 418, 11, 18446744073709551616, 341560936795438018, 341569732888460226⟩
theorem L416_fin : (prmOK pL416 416 && ptTest pL416 (runFrom pL416 (fmask pL416) (cmask pL416) (hmask pL416) 1 415 (true, (init pL416), (init pL416))) 416 208 false) = true := by
  decide +kernel
theorem L416_ok : RunOK pL416 416 (runFrom pL416 (fmask pL416) (cmask pL416) (hmask pL416) 1 415 (true, (init pL416), (init pL416))) ∧ ptTest pL416 (runFrom pL416 (fmask pL416) (cmask pL416) (hmask pL416) 1 415 (true, (init pL416), (init pL416))) 416 208 false = true :=
  fin_run (runOK_init (prmOK_of_and L416_fin) true) (by decide) rfl L416_fin ptTest_fst
theorem H416_fin : (prmOK pH416 416 && ptTest pH416 (runFrom pH416 (fmask pH416) (cmask pH416) (hmask pH416) 1 415 (true, (init pH416), (init pH416))) 416 208 true) = true := by
  decide +kernel
theorem H416_ok : RunOK pH416 416 (runFrom pH416 (fmask pH416) (cmask pH416) (hmask pH416) 1 415 (true, (init pH416), (init pH416))) ∧ ptTest pH416 (runFrom pH416 (fmask pH416) (cmask pH416) (hmask pH416) 1 415 (true, (init pH416), (init pH416))) 416 208 true = true :=
  fin_run (runOK_init (prmOK_of_and H416_fin) true) (by decide) rfl H416_fin ptTest_fst
theorem I416_fin : (prmOK pI416 416 && intTest pI416 (runFrom pI416 (fmask pI416) (cmask pI416) (hmask pI416) 1 415 (true, (init pI416), (init pI416))) 416 13 true) = true := by
  decide +kernel
theorem I416_ok : RunOK pI416 416 (runFrom pI416 (fmask pI416) (cmask pI416) (hmask pI416) 1 415 (true, (init pI416), (init pI416))) ∧ intTest pI416 (runFrom pI416 (fmask pI416) (cmask pI416) (hmask pI416) 1 415 (true, (init pI416), (init pI416))) 416 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I416_fin) true) (by decide) rfl I416_fin intTest_fst
theorem link416 : linkOK pL416 pH416 pI416 = true := by decide +kernel
theorem cvx416 : ConvexBetweenHumps 416 :=
  cvx_of L416_ok H416_ok I416_ok link416 (by decide)
theorem cenlink416 : cenLinkOK pI416 416 = true := by decide +kernel
theorem cen416 : CenterUniqueMin 416 ∧ DipHyp 416 ∧ OnePointHyps 416 :=
  cen_of L416_ok H416_ok I416_ok link416 cenlink416

/-! ### `N = 417` -/

def pL417 : Prm := ⟨68, 32, 33, 419, 11, 18446744073709551616, 340940270390022753, 340940270390022753⟩
def pH417 : Prm := ⟨68, 32, 33, 419, 11, 18446744073709551616, 340949066483044961, 340949066483044961⟩
def pI417 : Prm := ⟨59, 29, 27, 419, 11, 18446744073709551616, 340940270390022753, 340949066483044961⟩
theorem L417_fin : (prmOK pL417 417 && ptTest pL417 (runFrom pL417 (fmask pL417) (cmask pL417) (hmask pL417) 1 416 (true, (init pL417), (init pL417))) 417 209 false) = true := by
  decide +kernel
theorem L417_ok : RunOK pL417 417 (runFrom pL417 (fmask pL417) (cmask pL417) (hmask pL417) 1 416 (true, (init pL417), (init pL417))) ∧ ptTest pL417 (runFrom pL417 (fmask pL417) (cmask pL417) (hmask pL417) 1 416 (true, (init pL417), (init pL417))) 417 209 false = true :=
  fin_run (runOK_init (prmOK_of_and L417_fin) true) (by decide) rfl L417_fin ptTest_fst
theorem H417_fin : (prmOK pH417 417 && ptTest pH417 (runFrom pH417 (fmask pH417) (cmask pH417) (hmask pH417) 1 416 (true, (init pH417), (init pH417))) 417 209 true) = true := by
  decide +kernel
theorem H417_ok : RunOK pH417 417 (runFrom pH417 (fmask pH417) (cmask pH417) (hmask pH417) 1 416 (true, (init pH417), (init pH417))) ∧ ptTest pH417 (runFrom pH417 (fmask pH417) (cmask pH417) (hmask pH417) 1 416 (true, (init pH417), (init pH417))) 417 209 true = true :=
  fin_run (runOK_init (prmOK_of_and H417_fin) true) (by decide) rfl H417_fin ptTest_fst
theorem I417_fin : (prmOK pI417 417 && intTest pI417 (runFrom pI417 (fmask pI417) (cmask pI417) (hmask pI417) 1 416 (true, (init pI417), (init pI417))) 417 13 false) = true := by
  decide +kernel
theorem I417_ok : RunOK pI417 417 (runFrom pI417 (fmask pI417) (cmask pI417) (hmask pI417) 1 416 (true, (init pI417), (init pI417))) ∧ intTest pI417 (runFrom pI417 (fmask pI417) (cmask pI417) (hmask pI417) 1 416 (true, (init pI417), (init pI417))) 417 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I417_fin) true) (by decide) rfl I417_fin intTest_fst
theorem link417 : linkOK pL417 pH417 pI417 = true := by decide +kernel
theorem cvx417 : ConvexBetweenHumps 417 :=
  cvx_of L417_ok H417_ok I417_ok link417 (by decide)

/-! ### `N = 418` -/

def pL418 : Prm := ⟨68, 32, 33, 420, 11, 18446744073709551616, 340323767686447017, 340323767686447017⟩
def pH418 : Prm := ⟨68, 32, 33, 420, 11, 18446744073709551616, 340332563779469225, 340332563779469225⟩
def pI418 : Prm := ⟨59, 29, 27, 420, 11, 18446744073709551616, 340323767686447017, 340332563779469225⟩
theorem L418_fin : (prmOK pL418 418 && ptTest pL418 (runFrom pL418 (fmask pL418) (cmask pL418) (hmask pL418) 1 417 (true, (init pL418), (init pL418))) 418 209 false) = true := by
  decide +kernel
theorem L418_ok : RunOK pL418 418 (runFrom pL418 (fmask pL418) (cmask pL418) (hmask pL418) 1 417 (true, (init pL418), (init pL418))) ∧ ptTest pL418 (runFrom pL418 (fmask pL418) (cmask pL418) (hmask pL418) 1 417 (true, (init pL418), (init pL418))) 418 209 false = true :=
  fin_run (runOK_init (prmOK_of_and L418_fin) true) (by decide) rfl L418_fin ptTest_fst
theorem H418_fin : (prmOK pH418 418 && ptTest pH418 (runFrom pH418 (fmask pH418) (cmask pH418) (hmask pH418) 1 417 (true, (init pH418), (init pH418))) 418 209 true) = true := by
  decide +kernel
theorem H418_ok : RunOK pH418 418 (runFrom pH418 (fmask pH418) (cmask pH418) (hmask pH418) 1 417 (true, (init pH418), (init pH418))) ∧ ptTest pH418 (runFrom pH418 (fmask pH418) (cmask pH418) (hmask pH418) 1 417 (true, (init pH418), (init pH418))) 418 209 true = true :=
  fin_run (runOK_init (prmOK_of_and H418_fin) true) (by decide) rfl H418_fin ptTest_fst
theorem I418_fin : (prmOK pI418 418 && intTest pI418 (runFrom pI418 (fmask pI418) (cmask pI418) (hmask pI418) 1 417 (true, (init pI418), (init pI418))) 418 13 true) = true := by
  decide +kernel
theorem I418_ok : RunOK pI418 418 (runFrom pI418 (fmask pI418) (cmask pI418) (hmask pI418) 1 417 (true, (init pI418), (init pI418))) ∧ intTest pI418 (runFrom pI418 (fmask pI418) (cmask pI418) (hmask pI418) 1 417 (true, (init pI418), (init pI418))) 418 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I418_fin) true) (by decide) rfl I418_fin intTest_fst
theorem link418 : linkOK pL418 pH418 pI418 = true := by decide +kernel
theorem cvx418 : ConvexBetweenHumps 418 :=
  cvx_of L418_ok H418_ok I418_ok link418 (by decide)
theorem cenlink418 : cenLinkOK pI418 418 = true := by decide +kernel
theorem cen418 : CenterUniqueMin 418 ∧ DipHyp 418 ∧ OnePointHyps 418 :=
  cen_of L418_ok H418_ok I418_ok link418 cenlink418

/-! ### `N = 419` -/

def pL419 : Prm := ⟨68, 32, 33, 421, 11, 18446744073709551616, 339708090645190281, 339708090645190281⟩
def pH419 : Prm := ⟨68, 32, 33, 421, 11, 18446744073709551616, 339716886738212489, 339716886738212489⟩
def pI419 : Prm := ⟨59, 29, 27, 421, 11, 18446744073709551616, 339708090645190281, 339716886738212489⟩
theorem L419_fin : (prmOK pL419 419 && ptTest pL419 (runFrom pL419 (fmask pL419) (cmask pL419) (hmask pL419) 1 418 (true, (init pL419), (init pL419))) 419 210 false) = true := by
  decide +kernel
theorem L419_ok : RunOK pL419 419 (runFrom pL419 (fmask pL419) (cmask pL419) (hmask pL419) 1 418 (true, (init pL419), (init pL419))) ∧ ptTest pL419 (runFrom pL419 (fmask pL419) (cmask pL419) (hmask pL419) 1 418 (true, (init pL419), (init pL419))) 419 210 false = true :=
  fin_run (runOK_init (prmOK_of_and L419_fin) true) (by decide) rfl L419_fin ptTest_fst
theorem H419_fin : (prmOK pH419 419 && ptTest pH419 (runFrom pH419 (fmask pH419) (cmask pH419) (hmask pH419) 1 418 (true, (init pH419), (init pH419))) 419 210 true) = true := by
  decide +kernel
theorem H419_ok : RunOK pH419 419 (runFrom pH419 (fmask pH419) (cmask pH419) (hmask pH419) 1 418 (true, (init pH419), (init pH419))) ∧ ptTest pH419 (runFrom pH419 (fmask pH419) (cmask pH419) (hmask pH419) 1 418 (true, (init pH419), (init pH419))) 419 210 true = true :=
  fin_run (runOK_init (prmOK_of_and H419_fin) true) (by decide) rfl H419_fin ptTest_fst
theorem I419_fin : (prmOK pI419 419 && intTest pI419 (runFrom pI419 (fmask pI419) (cmask pI419) (hmask pI419) 1 418 (true, (init pI419), (init pI419))) 419 13 false) = true := by
  decide +kernel
theorem I419_ok : RunOK pI419 419 (runFrom pI419 (fmask pI419) (cmask pI419) (hmask pI419) 1 418 (true, (init pI419), (init pI419))) ∧ intTest pI419 (runFrom pI419 (fmask pI419) (cmask pI419) (hmask pI419) 1 418 (true, (init pI419), (init pI419))) 419 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I419_fin) true) (by decide) rfl I419_fin intTest_fst
theorem link419 : linkOK pL419 pH419 pI419 = true := by decide +kernel
theorem cvx419 : ConvexBetweenHumps 419 :=
  cvx_of L419_ok H419_ok I419_ok link419 (by decide)

/-! ### `N = 420` -/

def pL420 : Prm := ⟨68, 32, 33, 422, 11, 18446744073709551616, 339096521990130364, 339096521990130364⟩
def pH420 : Prm := ⟨68, 32, 33, 422, 11, 18446744073709551616, 339105318083152572, 339105318083152572⟩
def pI420 : Prm := ⟨59, 29, 27, 422, 11, 18446744073709551616, 339096521990130364, 339105318083152572⟩
theorem L420_fin : (prmOK pL420 420 && ptTest pL420 (runFrom pL420 (fmask pL420) (cmask pL420) (hmask pL420) 1 419 (true, (init pL420), (init pL420))) 420 210 false) = true := by
  decide +kernel
theorem L420_ok : RunOK pL420 420 (runFrom pL420 (fmask pL420) (cmask pL420) (hmask pL420) 1 419 (true, (init pL420), (init pL420))) ∧ ptTest pL420 (runFrom pL420 (fmask pL420) (cmask pL420) (hmask pL420) 1 419 (true, (init pL420), (init pL420))) 420 210 false = true :=
  fin_run (runOK_init (prmOK_of_and L420_fin) true) (by decide) rfl L420_fin ptTest_fst
theorem H420_fin : (prmOK pH420 420 && ptTest pH420 (runFrom pH420 (fmask pH420) (cmask pH420) (hmask pH420) 1 419 (true, (init pH420), (init pH420))) 420 210 true) = true := by
  decide +kernel
theorem H420_ok : RunOK pH420 420 (runFrom pH420 (fmask pH420) (cmask pH420) (hmask pH420) 1 419 (true, (init pH420), (init pH420))) ∧ ptTest pH420 (runFrom pH420 (fmask pH420) (cmask pH420) (hmask pH420) 1 419 (true, (init pH420), (init pH420))) 420 210 true = true :=
  fin_run (runOK_init (prmOK_of_and H420_fin) true) (by decide) rfl H420_fin ptTest_fst
theorem I420_fin : (prmOK pI420 420 && intTest pI420 (runFrom pI420 (fmask pI420) (cmask pI420) (hmask pI420) 1 419 (true, (init pI420), (init pI420))) 420 13 true) = true := by
  decide +kernel
theorem I420_ok : RunOK pI420 420 (runFrom pI420 (fmask pI420) (cmask pI420) (hmask pI420) 1 419 (true, (init pI420), (init pI420))) ∧ intTest pI420 (runFrom pI420 (fmask pI420) (cmask pI420) (hmask pI420) 1 419 (true, (init pI420), (init pI420))) 420 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I420_fin) true) (by decide) rfl I420_fin intTest_fst
theorem link420 : linkOK pL420 pH420 pI420 = true := by decide +kernel
theorem cvx420 : ConvexBetweenHumps 420 :=
  cvx_of L420_ok H420_ok I420_ok link420 (by decide)
theorem cenlink420 : cenLinkOK pI420 420 = true := by decide +kernel
theorem cen420 : CenterUniqueMin 420 ∧ DipHyp 420 ∧ OnePointHyps 420 :=
  cen_of L420_ok H420_ok I420_ok link420 cenlink420

/-! ### `N = 421` -/

def pL421 : Prm := ⟨68, 32, 33, 423, 11, 18446744073709551616, 338485771871854934, 338485771871854934⟩
def pH421 : Prm := ⟨68, 32, 33, 423, 11, 18446744073709551616, 338494567964877142, 338494567964877142⟩
def pI421 : Prm := ⟨59, 29, 27, 423, 11, 18446744073709551616, 338485771871854934, 338494567964877142⟩
theorem L421_fin : (prmOK pL421 421 && ptTest pL421 (runFrom pL421 (fmask pL421) (cmask pL421) (hmask pL421) 1 420 (true, (init pL421), (init pL421))) 421 211 false) = true := by
  decide +kernel
theorem L421_ok : RunOK pL421 421 (runFrom pL421 (fmask pL421) (cmask pL421) (hmask pL421) 1 420 (true, (init pL421), (init pL421))) ∧ ptTest pL421 (runFrom pL421 (fmask pL421) (cmask pL421) (hmask pL421) 1 420 (true, (init pL421), (init pL421))) 421 211 false = true :=
  fin_run (runOK_init (prmOK_of_and L421_fin) true) (by decide) rfl L421_fin ptTest_fst
theorem H421_fin : (prmOK pH421 421 && ptTest pH421 (runFrom pH421 (fmask pH421) (cmask pH421) (hmask pH421) 1 420 (true, (init pH421), (init pH421))) 421 211 true) = true := by
  decide +kernel
theorem H421_ok : RunOK pH421 421 (runFrom pH421 (fmask pH421) (cmask pH421) (hmask pH421) 1 420 (true, (init pH421), (init pH421))) ∧ ptTest pH421 (runFrom pH421 (fmask pH421) (cmask pH421) (hmask pH421) 1 420 (true, (init pH421), (init pH421))) 421 211 true = true :=
  fin_run (runOK_init (prmOK_of_and H421_fin) true) (by decide) rfl H421_fin ptTest_fst
theorem I421_fin : (prmOK pI421 421 && intTest pI421 (runFrom pI421 (fmask pI421) (cmask pI421) (hmask pI421) 1 420 (true, (init pI421), (init pI421))) 421 13 false) = true := by
  decide +kernel
theorem I421_ok : RunOK pI421 421 (runFrom pI421 (fmask pI421) (cmask pI421) (hmask pI421) 1 420 (true, (init pI421), (init pI421))) ∧ intTest pI421 (runFrom pI421 (fmask pI421) (cmask pI421) (hmask pI421) 1 420 (true, (init pI421), (init pI421))) 421 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I421_fin) true) (by decide) rfl I421_fin intTest_fst
theorem link421 : linkOK pL421 pH421 pI421 = true := by decide +kernel
theorem cvx421 : ConvexBetweenHumps 421 :=
  cvx_of L421_ok H421_ok I421_ok link421 (by decide)

/-! ### `N = 422` -/

def pL422 : Prm := ⟨68, 32, 33, 424, 11, 18446744073709551616, 337879075813137348, 337879075813137348⟩
def pH422 : Prm := ⟨68, 32, 33, 424, 11, 18446744073709551616, 337887871906159556, 337887871906159556⟩
def pI422 : Prm := ⟨59, 29, 27, 424, 11, 18446744073709551616, 337879075813137348, 337887871906159556⟩
theorem L422_fin : (prmOK pL422 422 && ptTest pL422 (runFrom pL422 (fmask pL422) (cmask pL422) (hmask pL422) 1 421 (true, (init pL422), (init pL422))) 422 211 false) = true := by
  decide +kernel
theorem L422_ok : RunOK pL422 422 (runFrom pL422 (fmask pL422) (cmask pL422) (hmask pL422) 1 421 (true, (init pL422), (init pL422))) ∧ ptTest pL422 (runFrom pL422 (fmask pL422) (cmask pL422) (hmask pL422) 1 421 (true, (init pL422), (init pL422))) 422 211 false = true :=
  fin_run (runOK_init (prmOK_of_and L422_fin) true) (by decide) rfl L422_fin ptTest_fst
theorem H422_fin : (prmOK pH422 422 && ptTest pH422 (runFrom pH422 (fmask pH422) (cmask pH422) (hmask pH422) 1 421 (true, (init pH422), (init pH422))) 422 211 true) = true := by
  decide +kernel
theorem H422_ok : RunOK pH422 422 (runFrom pH422 (fmask pH422) (cmask pH422) (hmask pH422) 1 421 (true, (init pH422), (init pH422))) ∧ ptTest pH422 (runFrom pH422 (fmask pH422) (cmask pH422) (hmask pH422) 1 421 (true, (init pH422), (init pH422))) 422 211 true = true :=
  fin_run (runOK_init (prmOK_of_and H422_fin) true) (by decide) rfl H422_fin ptTest_fst
theorem I422_fin : (prmOK pI422 422 && intTest pI422 (runFrom pI422 (fmask pI422) (cmask pI422) (hmask pI422) 1 421 (true, (init pI422), (init pI422))) 422 13 true) = true := by
  decide +kernel
theorem I422_ok : RunOK pI422 422 (runFrom pI422 (fmask pI422) (cmask pI422) (hmask pI422) 1 421 (true, (init pI422), (init pI422))) ∧ intTest pI422 (runFrom pI422 (fmask pI422) (cmask pI422) (hmask pI422) 1 421 (true, (init pI422), (init pI422))) 422 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I422_fin) true) (by decide) rfl I422_fin intTest_fst
theorem link422 : linkOK pL422 pH422 pI422 = true := by decide +kernel
theorem cvx422 : ConvexBetweenHumps 422 :=
  cvx_of L422_ok H422_ok I422_ok link422 (by decide)
theorem cenlink422 : cenLinkOK pI422 422 = true := by decide +kernel
theorem cen422 : CenterUniqueMin 422 ∧ DipHyp 422 ∧ OnePointHyps 422 :=
  cen_of L422_ok H422_ok I422_ok link422 cenlink422

/-! ### `N = 423` -/

def pL423 : Prm := ⟨68, 32, 33, 425, 11, 18446744073709551616, 337273191238313013, 337273191238313013⟩
def pH423 : Prm := ⟨68, 32, 33, 425, 11, 18446744073709551616, 337281987331335221, 337281987331335221⟩
def pI423 : Prm := ⟨59, 29, 27, 425, 11, 18446744073709551616, 337273191238313013, 337281987331335221⟩
theorem L423_fin : (prmOK pL423 423 && ptTest pL423 (runFrom pL423 (fmask pL423) (cmask pL423) (hmask pL423) 1 422 (true, (init pL423), (init pL423))) 423 212 false) = true := by
  decide +kernel
theorem L423_ok : RunOK pL423 423 (runFrom pL423 (fmask pL423) (cmask pL423) (hmask pL423) 1 422 (true, (init pL423), (init pL423))) ∧ ptTest pL423 (runFrom pL423 (fmask pL423) (cmask pL423) (hmask pL423) 1 422 (true, (init pL423), (init pL423))) 423 212 false = true :=
  fin_run (runOK_init (prmOK_of_and L423_fin) true) (by decide) rfl L423_fin ptTest_fst
theorem H423_fin : (prmOK pH423 423 && ptTest pH423 (runFrom pH423 (fmask pH423) (cmask pH423) (hmask pH423) 1 422 (true, (init pH423), (init pH423))) 423 212 true) = true := by
  decide +kernel
theorem H423_ok : RunOK pH423 423 (runFrom pH423 (fmask pH423) (cmask pH423) (hmask pH423) 1 422 (true, (init pH423), (init pH423))) ∧ ptTest pH423 (runFrom pH423 (fmask pH423) (cmask pH423) (hmask pH423) 1 422 (true, (init pH423), (init pH423))) 423 212 true = true :=
  fin_run (runOK_init (prmOK_of_and H423_fin) true) (by decide) rfl H423_fin ptTest_fst
theorem I423_fin : (prmOK pI423 423 && intTest pI423 (runFrom pI423 (fmask pI423) (cmask pI423) (hmask pI423) 1 422 (true, (init pI423), (init pI423))) 423 13 false) = true := by
  decide +kernel
theorem I423_ok : RunOK pI423 423 (runFrom pI423 (fmask pI423) (cmask pI423) (hmask pI423) 1 422 (true, (init pI423), (init pI423))) ∧ intTest pI423 (runFrom pI423 (fmask pI423) (cmask pI423) (hmask pI423) 1 422 (true, (init pI423), (init pI423))) 423 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I423_fin) true) (by decide) rfl I423_fin intTest_fst
theorem link423 : linkOK pL423 pH423 pI423 = true := by decide +kernel
theorem cvx423 : ConvexBetweenHumps 423 :=
  cvx_of L423_ok H423_ok I423_ok link423 (by decide)

/-! ### `N = 424` -/

def pL424 : Prm := ⟨68, 32, 33, 426, 11, 18446744073709551616, 336671307363164511, 336671307363164511⟩
def pH424 : Prm := ⟨68, 32, 33, 426, 11, 18446744073709551616, 336680103456186719, 336680103456186719⟩
def pI424 : Prm := ⟨59, 29, 27, 426, 11, 18446744073709551616, 336671307363164511, 336680103456186719⟩
theorem L424_fin : (prmOK pL424 424 && ptTest pL424 (runFrom pL424 (fmask pL424) (cmask pL424) (hmask pL424) 1 423 (true, (init pL424), (init pL424))) 424 212 false) = true := by
  decide +kernel
theorem L424_ok : RunOK pL424 424 (runFrom pL424 (fmask pL424) (cmask pL424) (hmask pL424) 1 423 (true, (init pL424), (init pL424))) ∧ ptTest pL424 (runFrom pL424 (fmask pL424) (cmask pL424) (hmask pL424) 1 423 (true, (init pL424), (init pL424))) 424 212 false = true :=
  fin_run (runOK_init (prmOK_of_and L424_fin) true) (by decide) rfl L424_fin ptTest_fst
theorem H424_fin : (prmOK pH424 424 && ptTest pH424 (runFrom pH424 (fmask pH424) (cmask pH424) (hmask pH424) 1 423 (true, (init pH424), (init pH424))) 424 212 true) = true := by
  decide +kernel
theorem H424_ok : RunOK pH424 424 (runFrom pH424 (fmask pH424) (cmask pH424) (hmask pH424) 1 423 (true, (init pH424), (init pH424))) ∧ ptTest pH424 (runFrom pH424 (fmask pH424) (cmask pH424) (hmask pH424) 1 423 (true, (init pH424), (init pH424))) 424 212 true = true :=
  fin_run (runOK_init (prmOK_of_and H424_fin) true) (by decide) rfl H424_fin ptTest_fst
theorem I424_fin : (prmOK pI424 424 && intTest pI424 (runFrom pI424 (fmask pI424) (cmask pI424) (hmask pI424) 1 423 (true, (init pI424), (init pI424))) 424 13 true) = true := by
  decide +kernel
theorem I424_ok : RunOK pI424 424 (runFrom pI424 (fmask pI424) (cmask pI424) (hmask pI424) 1 423 (true, (init pI424), (init pI424))) ∧ intTest pI424 (runFrom pI424 (fmask pI424) (cmask pI424) (hmask pI424) 1 423 (true, (init pI424), (init pI424))) 424 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I424_fin) true) (by decide) rfl I424_fin intTest_fst
theorem link424 : linkOK pL424 pH424 pI424 = true := by decide +kernel
theorem cvx424 : ConvexBetweenHumps 424 :=
  cvx_of L424_ok H424_ok I424_ok link424 (by decide)
theorem cenlink424 : cenLinkOK pI424 424 = true := by decide +kernel
theorem cen424 : CenterUniqueMin 424 ∧ DipHyp 424 ∧ OnePointHyps 424 :=
  cen_of L424_ok H424_ok I424_ok link424 cenlink424

/-! ### `N = 425` -/

def pL425 : Prm := ⟨68, 32, 33, 427, 11, 18446744073709551616, 336070227991071007, 336070227991071007⟩
def pH425 : Prm := ⟨68, 32, 33, 427, 11, 18446744073709551616, 336079024084093215, 336079024084093215⟩
def pI425 : Prm := ⟨59, 29, 27, 427, 11, 18446744073709551616, 336070227991071007, 336079024084093215⟩
theorem L425_fin : (prmOK pL425 425 && ptTest pL425 (runFrom pL425 (fmask pL425) (cmask pL425) (hmask pL425) 1 424 (true, (init pL425), (init pL425))) 425 213 false) = true := by
  decide +kernel
theorem L425_ok : RunOK pL425 425 (runFrom pL425 (fmask pL425) (cmask pL425) (hmask pL425) 1 424 (true, (init pL425), (init pL425))) ∧ ptTest pL425 (runFrom pL425 (fmask pL425) (cmask pL425) (hmask pL425) 1 424 (true, (init pL425), (init pL425))) 425 213 false = true :=
  fin_run (runOK_init (prmOK_of_and L425_fin) true) (by decide) rfl L425_fin ptTest_fst
theorem H425_fin : (prmOK pH425 425 && ptTest pH425 (runFrom pH425 (fmask pH425) (cmask pH425) (hmask pH425) 1 424 (true, (init pH425), (init pH425))) 425 213 true) = true := by
  decide +kernel
theorem H425_ok : RunOK pH425 425 (runFrom pH425 (fmask pH425) (cmask pH425) (hmask pH425) 1 424 (true, (init pH425), (init pH425))) ∧ ptTest pH425 (runFrom pH425 (fmask pH425) (cmask pH425) (hmask pH425) 1 424 (true, (init pH425), (init pH425))) 425 213 true = true :=
  fin_run (runOK_init (prmOK_of_and H425_fin) true) (by decide) rfl H425_fin ptTest_fst
theorem I425_fin : (prmOK pI425 425 && intTest pI425 (runFrom pI425 (fmask pI425) (cmask pI425) (hmask pI425) 1 424 (true, (init pI425), (init pI425))) 425 13 false) = true := by
  decide +kernel
theorem I425_ok : RunOK pI425 425 (runFrom pI425 (fmask pI425) (cmask pI425) (hmask pI425) 1 424 (true, (init pI425), (init pI425))) ∧ intTest pI425 (runFrom pI425 (fmask pI425) (cmask pI425) (hmask pI425) 1 424 (true, (init pI425), (init pI425))) 425 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I425_fin) true) (by decide) rfl I425_fin intTest_fst
theorem link425 : linkOK pL425 pH425 pI425 = true := by decide +kernel
theorem cvx425 : ConvexBetweenHumps 425 :=
  cvx_of L425_ok H425_ok I425_ok link425 (by decide)

/-! ### `N = 426` -/

def pL426 : Prm := ⟨68, 32, 33, 428, 11, 18446744073709551616, 335473096904019385, 335473096904019385⟩
def pH426 : Prm := ⟨68, 32, 33, 428, 11, 18446744073709551616, 335481892997041593, 335481892997041593⟩
def pI426 : Prm := ⟨59, 29, 27, 428, 11, 18446744073709551616, 335473096904019385, 335481892997041593⟩
theorem L426_fin : (prmOK pL426 426 && ptTest pL426 (runFrom pL426 (fmask pL426) (cmask pL426) (hmask pL426) 1 425 (true, (init pL426), (init pL426))) 426 213 false) = true := by
  decide +kernel
theorem L426_ok : RunOK pL426 426 (runFrom pL426 (fmask pL426) (cmask pL426) (hmask pL426) 1 425 (true, (init pL426), (init pL426))) ∧ ptTest pL426 (runFrom pL426 (fmask pL426) (cmask pL426) (hmask pL426) 1 425 (true, (init pL426), (init pL426))) 426 213 false = true :=
  fin_run (runOK_init (prmOK_of_and L426_fin) true) (by decide) rfl L426_fin ptTest_fst
theorem H426_fin : (prmOK pH426 426 && ptTest pH426 (runFrom pH426 (fmask pH426) (cmask pH426) (hmask pH426) 1 425 (true, (init pH426), (init pH426))) 426 213 true) = true := by
  decide +kernel
theorem H426_ok : RunOK pH426 426 (runFrom pH426 (fmask pH426) (cmask pH426) (hmask pH426) 1 425 (true, (init pH426), (init pH426))) ∧ ptTest pH426 (runFrom pH426 (fmask pH426) (cmask pH426) (hmask pH426) 1 425 (true, (init pH426), (init pH426))) 426 213 true = true :=
  fin_run (runOK_init (prmOK_of_and H426_fin) true) (by decide) rfl H426_fin ptTest_fst
theorem I426_fin : (prmOK pI426 426 && intTest pI426 (runFrom pI426 (fmask pI426) (cmask pI426) (hmask pI426) 1 425 (true, (init pI426), (init pI426))) 426 13 true) = true := by
  decide +kernel
theorem I426_ok : RunOK pI426 426 (runFrom pI426 (fmask pI426) (cmask pI426) (hmask pI426) 1 425 (true, (init pI426), (init pI426))) ∧ intTest pI426 (runFrom pI426 (fmask pI426) (cmask pI426) (hmask pI426) 1 425 (true, (init pI426), (init pI426))) 426 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I426_fin) true) (by decide) rfl I426_fin intTest_fst
theorem link426 : linkOK pL426 pH426 pI426 = true := by decide +kernel
theorem cvx426 : ConvexBetweenHumps 426 :=
  cvx_of L426_ok H426_ok I426_ok link426 (by decide)
theorem cenlink426 : cenLinkOK pI426 426 = true := by decide +kernel
theorem cen426 : CenterUniqueMin 426 ∧ DipHyp 426 ∧ OnePointHyps 426 :=
  cen_of L426_ok H426_ok I426_ok link426 cenlink426

/-! ### `N = 427` -/

def pL427 : Prm := ⟨68, 32, 33, 429, 11, 18446744073709551616, 334876763410573407, 334876763410573407⟩
def pH427 : Prm := ⟨68, 32, 33, 429, 11, 18446744073709551616, 334885559503595615, 334885559503595615⟩
def pI427 : Prm := ⟨59, 29, 27, 429, 11, 18446744073709551616, 334876763410573407, 334885559503595615⟩
theorem L427_fin : (prmOK pL427 427 && ptTest pL427 (runFrom pL427 (fmask pL427) (cmask pL427) (hmask pL427) 1 426 (true, (init pL427), (init pL427))) 427 214 false) = true := by
  decide +kernel
theorem L427_ok : RunOK pL427 427 (runFrom pL427 (fmask pL427) (cmask pL427) (hmask pL427) 1 426 (true, (init pL427), (init pL427))) ∧ ptTest pL427 (runFrom pL427 (fmask pL427) (cmask pL427) (hmask pL427) 1 426 (true, (init pL427), (init pL427))) 427 214 false = true :=
  fin_run (runOK_init (prmOK_of_and L427_fin) true) (by decide) rfl L427_fin ptTest_fst
theorem H427_fin : (prmOK pH427 427 && ptTest pH427 (runFrom pH427 (fmask pH427) (cmask pH427) (hmask pH427) 1 426 (true, (init pH427), (init pH427))) 427 214 true) = true := by
  decide +kernel
theorem H427_ok : RunOK pH427 427 (runFrom pH427 (fmask pH427) (cmask pH427) (hmask pH427) 1 426 (true, (init pH427), (init pH427))) ∧ ptTest pH427 (runFrom pH427 (fmask pH427) (cmask pH427) (hmask pH427) 1 426 (true, (init pH427), (init pH427))) 427 214 true = true :=
  fin_run (runOK_init (prmOK_of_and H427_fin) true) (by decide) rfl H427_fin ptTest_fst
theorem I427_fin : (prmOK pI427 427 && intTest pI427 (runFrom pI427 (fmask pI427) (cmask pI427) (hmask pI427) 1 426 (true, (init pI427), (init pI427))) 427 13 false) = true := by
  decide +kernel
theorem I427_ok : RunOK pI427 427 (runFrom pI427 (fmask pI427) (cmask pI427) (hmask pI427) 1 426 (true, (init pI427), (init pI427))) ∧ intTest pI427 (runFrom pI427 (fmask pI427) (cmask pI427) (hmask pI427) 1 426 (true, (init pI427), (init pI427))) 427 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I427_fin) true) (by decide) rfl I427_fin intTest_fst
theorem link427 : linkOK pL427 pH427 pI427 = true := by decide +kernel
theorem cvx427 : ConvexBetweenHumps 427 :=
  cvx_of L427_ok H427_ok I427_ok link427 (by decide)

/-! ### `N = 428` -/

def pL428 : Prm := ⟨68, 32, 33, 430, 11, 18446744073709551616, 334284326711754130, 334284326711754130⟩
def pH428 : Prm := ⟨68, 32, 33, 430, 11, 18446744073709551616, 334293122804776338, 334293122804776338⟩
def pI428 : Prm := ⟨59, 29, 27, 430, 11, 18446744073709551616, 334284326711754130, 334293122804776338⟩
theorem L428_fin : (prmOK pL428 428 && ptTest pL428 (runFrom pL428 (fmask pL428) (cmask pL428) (hmask pL428) 1 427 (true, (init pL428), (init pL428))) 428 214 false) = true := by
  decide +kernel
theorem L428_ok : RunOK pL428 428 (runFrom pL428 (fmask pL428) (cmask pL428) (hmask pL428) 1 427 (true, (init pL428), (init pL428))) ∧ ptTest pL428 (runFrom pL428 (fmask pL428) (cmask pL428) (hmask pL428) 1 427 (true, (init pL428), (init pL428))) 428 214 false = true :=
  fin_run (runOK_init (prmOK_of_and L428_fin) true) (by decide) rfl L428_fin ptTest_fst
theorem H428_fin : (prmOK pH428 428 && ptTest pH428 (runFrom pH428 (fmask pH428) (cmask pH428) (hmask pH428) 1 427 (true, (init pH428), (init pH428))) 428 214 true) = true := by
  decide +kernel
theorem H428_ok : RunOK pH428 428 (runFrom pH428 (fmask pH428) (cmask pH428) (hmask pH428) 1 427 (true, (init pH428), (init pH428))) ∧ ptTest pH428 (runFrom pH428 (fmask pH428) (cmask pH428) (hmask pH428) 1 427 (true, (init pH428), (init pH428))) 428 214 true = true :=
  fin_run (runOK_init (prmOK_of_and H428_fin) true) (by decide) rfl H428_fin ptTest_fst
theorem I428_fin : (prmOK pI428 428 && intTest pI428 (runFrom pI428 (fmask pI428) (cmask pI428) (hmask pI428) 1 427 (true, (init pI428), (init pI428))) 428 13 true) = true := by
  decide +kernel
theorem I428_ok : RunOK pI428 428 (runFrom pI428 (fmask pI428) (cmask pI428) (hmask pI428) 1 427 (true, (init pI428), (init pI428))) ∧ intTest pI428 (runFrom pI428 (fmask pI428) (cmask pI428) (hmask pI428) 1 427 (true, (init pI428), (init pI428))) 428 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I428_fin) true) (by decide) rfl I428_fin intTest_fst
theorem link428 : linkOK pL428 pH428 pI428 = true := by decide +kernel
theorem cvx428 : ConvexBetweenHumps 428 :=
  cvx_of L428_ok H428_ok I428_ok link428 (by decide)
theorem cenlink428 : cenLinkOK pI428 428 = true := by decide +kernel
theorem cen428 : CenterUniqueMin 428 ∧ DipHyp 428 ∧ OnePointHyps 428 :=
  cen_of L428_ok H428_ok I428_ok link428 cenlink428

/-! ### `N = 429` -/

def pL429 : Prm := ⟨68, 32, 33, 431, 11, 18446744073709551616, 333692680767834407, 333692680767834407⟩
def pH429 : Prm := ⟨68, 32, 33, 431, 11, 18446744073709551616, 333701476860856615, 333701476860856615⟩
def pI429 : Prm := ⟨59, 29, 27, 431, 11, 18446744073709551616, 333692680767834407, 333701476860856615⟩
theorem L429_fin : (prmOK pL429 429 && ptTest pL429 (runFrom pL429 (fmask pL429) (cmask pL429) (hmask pL429) 1 428 (true, (init pL429), (init pL429))) 429 215 false) = true := by
  decide +kernel
theorem L429_ok : RunOK pL429 429 (runFrom pL429 (fmask pL429) (cmask pL429) (hmask pL429) 1 428 (true, (init pL429), (init pL429))) ∧ ptTest pL429 (runFrom pL429 (fmask pL429) (cmask pL429) (hmask pL429) 1 428 (true, (init pL429), (init pL429))) 429 215 false = true :=
  fin_run (runOK_init (prmOK_of_and L429_fin) true) (by decide) rfl L429_fin ptTest_fst
theorem H429_fin : (prmOK pH429 429 && ptTest pH429 (runFrom pH429 (fmask pH429) (cmask pH429) (hmask pH429) 1 428 (true, (init pH429), (init pH429))) 429 215 true) = true := by
  decide +kernel
theorem H429_ok : RunOK pH429 429 (runFrom pH429 (fmask pH429) (cmask pH429) (hmask pH429) 1 428 (true, (init pH429), (init pH429))) ∧ ptTest pH429 (runFrom pH429 (fmask pH429) (cmask pH429) (hmask pH429) 1 428 (true, (init pH429), (init pH429))) 429 215 true = true :=
  fin_run (runOK_init (prmOK_of_and H429_fin) true) (by decide) rfl H429_fin ptTest_fst
theorem I429_fin : (prmOK pI429 429 && intTest pI429 (runFrom pI429 (fmask pI429) (cmask pI429) (hmask pI429) 1 428 (true, (init pI429), (init pI429))) 429 13 false) = true := by
  decide +kernel
theorem I429_ok : RunOK pI429 429 (runFrom pI429 (fmask pI429) (cmask pI429) (hmask pI429) 1 428 (true, (init pI429), (init pI429))) ∧ intTest pI429 (runFrom pI429 (fmask pI429) (cmask pI429) (hmask pI429) 1 428 (true, (init pI429), (init pI429))) 429 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I429_fin) true) (by decide) rfl I429_fin intTest_fst
theorem link429 : linkOK pL429 pH429 pI429 = true := by decide +kernel
theorem cvx429 : ConvexBetweenHumps 429 :=
  cvx_of L429_ok H429_ok I429_ok link429 (by decide)

/-! ### `N = 430` -/

def pL430 : Prm := ⟨68, 32, 33, 432, 11, 18446744073709551616, 333104881031869093, 333104881031869093⟩
def pH430 : Prm := ⟨68, 32, 33, 432, 11, 18446744073709551616, 333113677124891301, 333113677124891301⟩
def pI430 : Prm := ⟨59, 29, 27, 432, 11, 18446744073709551616, 333104881031869093, 333113677124891301⟩
theorem L430_fin : (prmOK pL430 430 && ptTest pL430 (runFrom pL430 (fmask pL430) (cmask pL430) (hmask pL430) 1 429 (true, (init pL430), (init pL430))) 430 215 false) = true := by
  decide +kernel
theorem L430_ok : RunOK pL430 430 (runFrom pL430 (fmask pL430) (cmask pL430) (hmask pL430) 1 429 (true, (init pL430), (init pL430))) ∧ ptTest pL430 (runFrom pL430 (fmask pL430) (cmask pL430) (hmask pL430) 1 429 (true, (init pL430), (init pL430))) 430 215 false = true :=
  fin_run (runOK_init (prmOK_of_and L430_fin) true) (by decide) rfl L430_fin ptTest_fst
theorem H430_fin : (prmOK pH430 430 && ptTest pH430 (runFrom pH430 (fmask pH430) (cmask pH430) (hmask pH430) 1 429 (true, (init pH430), (init pH430))) 430 215 true) = true := by
  decide +kernel
theorem H430_ok : RunOK pH430 430 (runFrom pH430 (fmask pH430) (cmask pH430) (hmask pH430) 1 429 (true, (init pH430), (init pH430))) ∧ ptTest pH430 (runFrom pH430 (fmask pH430) (cmask pH430) (hmask pH430) 1 429 (true, (init pH430), (init pH430))) 430 215 true = true :=
  fin_run (runOK_init (prmOK_of_and H430_fin) true) (by decide) rfl H430_fin ptTest_fst
theorem I430_fin : (prmOK pI430 430 && intTest pI430 (runFrom pI430 (fmask pI430) (cmask pI430) (hmask pI430) 1 429 (true, (init pI430), (init pI430))) 430 13 true) = true := by
  decide +kernel
theorem I430_ok : RunOK pI430 430 (runFrom pI430 (fmask pI430) (cmask pI430) (hmask pI430) 1 429 (true, (init pI430), (init pI430))) ∧ intTest pI430 (runFrom pI430 (fmask pI430) (cmask pI430) (hmask pI430) 1 429 (true, (init pI430), (init pI430))) 430 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I430_fin) true) (by decide) rfl I430_fin intTest_fst
theorem link430 : linkOK pL430 pH430 pI430 = true := by decide +kernel
theorem cvx430 : ConvexBetweenHumps 430 :=
  cvx_of L430_ok H430_ok I430_ok link430 (by decide)
theorem cenlink430 : cenLinkOK pI430 430 = true := by decide +kernel
theorem cen430 : CenterUniqueMin 430 ∧ DipHyp 430 ∧ OnePointHyps 430 :=
  cen_of L430_ok H430_ok I430_ok link430 cenlink430

/-! ### `N = 431` -/

def pL431 : Prm := ⟨68, 32, 33, 433, 11, 18446744073709551616, 332517865282268657, 332517865282268657⟩
def pH431 : Prm := ⟨68, 32, 33, 433, 11, 18446744073709551616, 332526661375290865, 332526661375290865⟩
def pI431 : Prm := ⟨59, 29, 27, 433, 11, 18446744073709551616, 332517865282268657, 332526661375290865⟩
theorem L431_fin : (prmOK pL431 431 && ptTest pL431 (runFrom pL431 (fmask pL431) (cmask pL431) (hmask pL431) 1 430 (true, (init pL431), (init pL431))) 431 216 false) = true := by
  decide +kernel
theorem L431_ok : RunOK pL431 431 (runFrom pL431 (fmask pL431) (cmask pL431) (hmask pL431) 1 430 (true, (init pL431), (init pL431))) ∧ ptTest pL431 (runFrom pL431 (fmask pL431) (cmask pL431) (hmask pL431) 1 430 (true, (init pL431), (init pL431))) 431 216 false = true :=
  fin_run (runOK_init (prmOK_of_and L431_fin) true) (by decide) rfl L431_fin ptTest_fst
theorem H431_fin : (prmOK pH431 431 && ptTest pH431 (runFrom pH431 (fmask pH431) (cmask pH431) (hmask pH431) 1 430 (true, (init pH431), (init pH431))) 431 216 true) = true := by
  decide +kernel
theorem H431_ok : RunOK pH431 431 (runFrom pH431 (fmask pH431) (cmask pH431) (hmask pH431) 1 430 (true, (init pH431), (init pH431))) ∧ ptTest pH431 (runFrom pH431 (fmask pH431) (cmask pH431) (hmask pH431) 1 430 (true, (init pH431), (init pH431))) 431 216 true = true :=
  fin_run (runOK_init (prmOK_of_and H431_fin) true) (by decide) rfl H431_fin ptTest_fst
theorem I431_fin : (prmOK pI431 431 && intTest pI431 (runFrom pI431 (fmask pI431) (cmask pI431) (hmask pI431) 1 430 (true, (init pI431), (init pI431))) 431 13 false) = true := by
  decide +kernel
theorem I431_ok : RunOK pI431 431 (runFrom pI431 (fmask pI431) (cmask pI431) (hmask pI431) 1 430 (true, (init pI431), (init pI431))) ∧ intTest pI431 (runFrom pI431 (fmask pI431) (cmask pI431) (hmask pI431) 1 430 (true, (init pI431), (init pI431))) 431 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I431_fin) true) (by decide) rfl I431_fin intTest_fst
theorem link431 : linkOK pL431 pH431 pI431 = true := by decide +kernel
theorem cvx431 : ConvexBetweenHumps 431 :=
  cvx_of L431_ok H431_ok I431_ok link431 (by decide)

/-! ### `N = 432` -/

def pL432 : Prm := ⟨68, 32, 33, 434, 11, 18446744073709551616, 331934646037807630, 331934646037807630⟩
def pH432 : Prm := ⟨68, 32, 33, 434, 11, 18446744073709551616, 331943442130829838, 331943442130829838⟩
def pI432 : Prm := ⟨59, 29, 27, 434, 11, 18446744073709551616, 331934646037807630, 331943442130829838⟩
theorem L432_fin : (prmOK pL432 432 && ptTest pL432 (runFrom pL432 (fmask pL432) (cmask pL432) (hmask pL432) 1 431 (true, (init pL432), (init pL432))) 432 216 false) = true := by
  decide +kernel
theorem L432_ok : RunOK pL432 432 (runFrom pL432 (fmask pL432) (cmask pL432) (hmask pL432) 1 431 (true, (init pL432), (init pL432))) ∧ ptTest pL432 (runFrom pL432 (fmask pL432) (cmask pL432) (hmask pL432) 1 431 (true, (init pL432), (init pL432))) 432 216 false = true :=
  fin_run (runOK_init (prmOK_of_and L432_fin) true) (by decide) rfl L432_fin ptTest_fst
theorem H432_fin : (prmOK pH432 432 && ptTest pH432 (runFrom pH432 (fmask pH432) (cmask pH432) (hmask pH432) 1 431 (true, (init pH432), (init pH432))) 432 216 true) = true := by
  decide +kernel
theorem H432_ok : RunOK pH432 432 (runFrom pH432 (fmask pH432) (cmask pH432) (hmask pH432) 1 431 (true, (init pH432), (init pH432))) ∧ ptTest pH432 (runFrom pH432 (fmask pH432) (cmask pH432) (hmask pH432) 1 431 (true, (init pH432), (init pH432))) 432 216 true = true :=
  fin_run (runOK_init (prmOK_of_and H432_fin) true) (by decide) rfl H432_fin ptTest_fst
theorem I432_fin : (prmOK pI432 432 && intTest pI432 (runFrom pI432 (fmask pI432) (cmask pI432) (hmask pI432) 1 431 (true, (init pI432), (init pI432))) 432 13 true) = true := by
  decide +kernel
theorem I432_ok : RunOK pI432 432 (runFrom pI432 (fmask pI432) (cmask pI432) (hmask pI432) 1 431 (true, (init pI432), (init pI432))) ∧ intTest pI432 (runFrom pI432 (fmask pI432) (cmask pI432) (hmask pI432) 1 431 (true, (init pI432), (init pI432))) 432 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I432_fin) true) (by decide) rfl I432_fin intTest_fst
theorem link432 : linkOK pL432 pH432 pI432 = true := by decide +kernel
theorem cvx432 : ConvexBetweenHumps 432 :=
  cvx_of L432_ok H432_ok I432_ok link432 (by decide)
theorem cenlink432 : cenLinkOK pI432 432 = true := by decide +kernel
theorem cen432 : CenterUniqueMin 432 ∧ DipHyp 432 ∧ OnePointHyps 432 :=
  cen_of L432_ok H432_ok I432_ok link432 cenlink432

/-! ### `N = 433` -/

def pL433 : Prm := ⟨68, 32, 33, 435, 11, 18446744073709551616, 331352204080647243, 331352204080647243⟩
def pH433 : Prm := ⟨68, 32, 33, 435, 11, 18446744073709551616, 331361000173669451, 331361000173669451⟩
def pI433 : Prm := ⟨60, 29, 28, 435, 11, 18446744073709551616, 331352204080647243, 331361000173669451⟩
theorem L433_fin : (prmOK pL433 433 && ptTest pL433 (runFrom pL433 (fmask pL433) (cmask pL433) (hmask pL433) 1 432 (true, (init pL433), (init pL433))) 433 217 false) = true := by
  decide +kernel
theorem L433_ok : RunOK pL433 433 (runFrom pL433 (fmask pL433) (cmask pL433) (hmask pL433) 1 432 (true, (init pL433), (init pL433))) ∧ ptTest pL433 (runFrom pL433 (fmask pL433) (cmask pL433) (hmask pL433) 1 432 (true, (init pL433), (init pL433))) 433 217 false = true :=
  fin_run (runOK_init (prmOK_of_and L433_fin) true) (by decide) rfl L433_fin ptTest_fst
theorem H433_fin : (prmOK pH433 433 && ptTest pH433 (runFrom pH433 (fmask pH433) (cmask pH433) (hmask pH433) 1 432 (true, (init pH433), (init pH433))) 433 217 true) = true := by
  decide +kernel
theorem H433_ok : RunOK pH433 433 (runFrom pH433 (fmask pH433) (cmask pH433) (hmask pH433) 1 432 (true, (init pH433), (init pH433))) ∧ ptTest pH433 (runFrom pH433 (fmask pH433) (cmask pH433) (hmask pH433) 1 432 (true, (init pH433), (init pH433))) 433 217 true = true :=
  fin_run (runOK_init (prmOK_of_and H433_fin) true) (by decide) rfl H433_fin ptTest_fst
theorem I433_fin : (prmOK pI433 433 && intTest pI433 (runFrom pI433 (fmask pI433) (cmask pI433) (hmask pI433) 1 432 (true, (init pI433), (init pI433))) 433 13 false) = true := by
  decide +kernel
theorem I433_ok : RunOK pI433 433 (runFrom pI433 (fmask pI433) (cmask pI433) (hmask pI433) 1 432 (true, (init pI433), (init pI433))) ∧ intTest pI433 (runFrom pI433 (fmask pI433) (cmask pI433) (hmask pI433) 1 432 (true, (init pI433), (init pI433))) 433 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I433_fin) true) (by decide) rfl I433_fin intTest_fst
theorem link433 : linkOK pL433 pH433 pI433 = true := by decide +kernel
theorem cvx433 : ConvexBetweenHumps 433 :=
  cvx_of L433_ok H433_ok I433_ok link433 (by decide)

/-! ### `N = 434` -/

def pL434 : Prm := ⟨68, 32, 33, 436, 11, 18446744073709551616, 330773509790299482, 330773509790299482⟩
def pH434 : Prm := ⟨68, 32, 33, 436, 11, 18446744073709551616, 330782305883321690, 330782305883321690⟩
def pI434 : Prm := ⟨60, 29, 28, 436, 11, 18446744073709551616, 330773509790299482, 330782305883321690⟩
theorem L434_fin : (prmOK pL434 434 && ptTest pL434 (runFrom pL434 (fmask pL434) (cmask pL434) (hmask pL434) 1 433 (true, (init pL434), (init pL434))) 434 217 false) = true := by
  decide +kernel
theorem L434_ok : RunOK pL434 434 (runFrom pL434 (fmask pL434) (cmask pL434) (hmask pL434) 1 433 (true, (init pL434), (init pL434))) ∧ ptTest pL434 (runFrom pL434 (fmask pL434) (cmask pL434) (hmask pL434) 1 433 (true, (init pL434), (init pL434))) 434 217 false = true :=
  fin_run (runOK_init (prmOK_of_and L434_fin) true) (by decide) rfl L434_fin ptTest_fst
theorem H434_fin : (prmOK pH434 434 && ptTest pH434 (runFrom pH434 (fmask pH434) (cmask pH434) (hmask pH434) 1 433 (true, (init pH434), (init pH434))) 434 217 true) = true := by
  decide +kernel
theorem H434_ok : RunOK pH434 434 (runFrom pH434 (fmask pH434) (cmask pH434) (hmask pH434) 1 433 (true, (init pH434), (init pH434))) ∧ ptTest pH434 (runFrom pH434 (fmask pH434) (cmask pH434) (hmask pH434) 1 433 (true, (init pH434), (init pH434))) 434 217 true = true :=
  fin_run (runOK_init (prmOK_of_and H434_fin) true) (by decide) rfl H434_fin ptTest_fst
theorem I434_fin : (prmOK pI434 434 && intTest pI434 (runFrom pI434 (fmask pI434) (cmask pI434) (hmask pI434) 1 433 (true, (init pI434), (init pI434))) 434 13 true) = true := by
  decide +kernel
theorem I434_ok : RunOK pI434 434 (runFrom pI434 (fmask pI434) (cmask pI434) (hmask pI434) 1 433 (true, (init pI434), (init pI434))) ∧ intTest pI434 (runFrom pI434 (fmask pI434) (cmask pI434) (hmask pI434) 1 433 (true, (init pI434), (init pI434))) 434 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I434_fin) true) (by decide) rfl I434_fin intTest_fst
theorem link434 : linkOK pL434 pH434 pI434 = true := by decide +kernel
theorem cvx434 : ConvexBetweenHumps 434 :=
  cvx_of L434_ok H434_ok I434_ok link434 (by decide)
theorem cenlink434 : cenLinkOK pI434 434 = true := by decide +kernel
theorem cen434 : CenterUniqueMin 434 ∧ DipHyp 434 ∧ OnePointHyps 434 :=
  cen_of L434_ok H434_ok I434_ok link434 cenlink434

/-! ### `N = 435` -/

def pL435 : Prm := ⟨68, 32, 33, 437, 11, 18446744073709551616, 330195586157031373, 330195586157031373⟩
def pH435 : Prm := ⟨68, 32, 33, 437, 11, 18446744073709551616, 330204382250053581, 330204382250053581⟩
def pI435 : Prm := ⟨60, 29, 28, 437, 11, 18446744073709551616, 330195586157031373, 330204382250053581⟩
theorem L435_fin : (prmOK pL435 435 && ptTest pL435 (runFrom pL435 (fmask pL435) (cmask pL435) (hmask pL435) 1 434 (true, (init pL435), (init pL435))) 435 218 false) = true := by
  decide +kernel
theorem L435_ok : RunOK pL435 435 (runFrom pL435 (fmask pL435) (cmask pL435) (hmask pL435) 1 434 (true, (init pL435), (init pL435))) ∧ ptTest pL435 (runFrom pL435 (fmask pL435) (cmask pL435) (hmask pL435) 1 434 (true, (init pL435), (init pL435))) 435 218 false = true :=
  fin_run (runOK_init (prmOK_of_and L435_fin) true) (by decide) rfl L435_fin ptTest_fst
theorem H435_fin : (prmOK pH435 435 && ptTest pH435 (runFrom pH435 (fmask pH435) (cmask pH435) (hmask pH435) 1 434 (true, (init pH435), (init pH435))) 435 218 true) = true := by
  decide +kernel
theorem H435_ok : RunOK pH435 435 (runFrom pH435 (fmask pH435) (cmask pH435) (hmask pH435) 1 434 (true, (init pH435), (init pH435))) ∧ ptTest pH435 (runFrom pH435 (fmask pH435) (cmask pH435) (hmask pH435) 1 434 (true, (init pH435), (init pH435))) 435 218 true = true :=
  fin_run (runOK_init (prmOK_of_and H435_fin) true) (by decide) rfl H435_fin ptTest_fst
theorem I435_fin : (prmOK pI435 435 && intTest pI435 (runFrom pI435 (fmask pI435) (cmask pI435) (hmask pI435) 1 434 (true, (init pI435), (init pI435))) 435 13 false) = true := by
  decide +kernel
theorem I435_ok : RunOK pI435 435 (runFrom pI435 (fmask pI435) (cmask pI435) (hmask pI435) 1 434 (true, (init pI435), (init pI435))) ∧ intTest pI435 (runFrom pI435 (fmask pI435) (cmask pI435) (hmask pI435) 1 434 (true, (init pI435), (init pI435))) 435 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I435_fin) true) (by decide) rfl I435_fin intTest_fst
theorem link435 : linkOK pL435 pH435 pI435 = true := by decide +kernel
theorem cvx435 : ConvexBetweenHumps 435 :=
  cvx_of L435_ok H435_ok I435_ok link435 (by decide)

/-! ### `N = 436` -/

def pL436 : Prm := ⟨68, 32, 33, 438, 11, 18446744073709551616, 329621362197884746, 329621362197884746⟩
def pH436 : Prm := ⟨68, 32, 33, 438, 11, 18446744073709551616, 329630158290906954, 329630158290906954⟩
def pI436 : Prm := ⟨60, 29, 28, 438, 11, 18446744073709551616, 329621362197884746, 329630158290906954⟩
theorem L436_fin : (prmOK pL436 436 && ptTest pL436 (runFrom pL436 (fmask pL436) (cmask pL436) (hmask pL436) 1 435 (true, (init pL436), (init pL436))) 436 218 false) = true := by
  decide +kernel
theorem L436_ok : RunOK pL436 436 (runFrom pL436 (fmask pL436) (cmask pL436) (hmask pL436) 1 435 (true, (init pL436), (init pL436))) ∧ ptTest pL436 (runFrom pL436 (fmask pL436) (cmask pL436) (hmask pL436) 1 435 (true, (init pL436), (init pL436))) 436 218 false = true :=
  fin_run (runOK_init (prmOK_of_and L436_fin) true) (by decide) rfl L436_fin ptTest_fst
theorem H436_fin : (prmOK pH436 436 && ptTest pH436 (runFrom pH436 (fmask pH436) (cmask pH436) (hmask pH436) 1 435 (true, (init pH436), (init pH436))) 436 218 true) = true := by
  decide +kernel
theorem H436_ok : RunOK pH436 436 (runFrom pH436 (fmask pH436) (cmask pH436) (hmask pH436) 1 435 (true, (init pH436), (init pH436))) ∧ ptTest pH436 (runFrom pH436 (fmask pH436) (cmask pH436) (hmask pH436) 1 435 (true, (init pH436), (init pH436))) 436 218 true = true :=
  fin_run (runOK_init (prmOK_of_and H436_fin) true) (by decide) rfl H436_fin ptTest_fst
theorem I436_fin : (prmOK pI436 436 && intTest pI436 (runFrom pI436 (fmask pI436) (cmask pI436) (hmask pI436) 1 435 (true, (init pI436), (init pI436))) 436 13 true) = true := by
  decide +kernel
theorem I436_ok : RunOK pI436 436 (runFrom pI436 (fmask pI436) (cmask pI436) (hmask pI436) 1 435 (true, (init pI436), (init pI436))) ∧ intTest pI436 (runFrom pI436 (fmask pI436) (cmask pI436) (hmask pI436) 1 435 (true, (init pI436), (init pI436))) 436 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I436_fin) true) (by decide) rfl I436_fin intTest_fst
theorem link436 : linkOK pL436 pH436 pI436 = true := by decide +kernel
theorem cvx436 : ConvexBetweenHumps 436 :=
  cvx_of L436_ok H436_ok I436_ok link436 (by decide)
theorem cenlink436 : cenLinkOK pI436 436 = true := by decide +kernel
theorem cen436 : CenterUniqueMin 436 ∧ DipHyp 436 ∧ OnePointHyps 436 :=
  cen_of L436_ok H436_ok I436_ok link436 cenlink436

/-! ### `N = 437` -/

def pL437 : Prm := ⟨68, 32, 33, 439, 11, 18446744073709551616, 329047902333775949, 329047902333775949⟩
def pH437 : Prm := ⟨68, 32, 33, 439, 11, 18446744073709551616, 329056698426798157, 329056698426798157⟩
def pI437 : Prm := ⟨60, 29, 28, 439, 11, 18446744073709551616, 329047902333775949, 329056698426798157⟩
theorem L437_fin : (prmOK pL437 437 && ptTest pL437 (runFrom pL437 (fmask pL437) (cmask pL437) (hmask pL437) 1 436 (true, (init pL437), (init pL437))) 437 219 false) = true := by
  decide +kernel
theorem L437_ok : RunOK pL437 437 (runFrom pL437 (fmask pL437) (cmask pL437) (hmask pL437) 1 436 (true, (init pL437), (init pL437))) ∧ ptTest pL437 (runFrom pL437 (fmask pL437) (cmask pL437) (hmask pL437) 1 436 (true, (init pL437), (init pL437))) 437 219 false = true :=
  fin_run (runOK_init (prmOK_of_and L437_fin) true) (by decide) rfl L437_fin ptTest_fst
theorem H437_fin : (prmOK pH437 437 && ptTest pH437 (runFrom pH437 (fmask pH437) (cmask pH437) (hmask pH437) 1 436 (true, (init pH437), (init pH437))) 437 219 true) = true := by
  decide +kernel
theorem H437_ok : RunOK pH437 437 (runFrom pH437 (fmask pH437) (cmask pH437) (hmask pH437) 1 436 (true, (init pH437), (init pH437))) ∧ ptTest pH437 (runFrom pH437 (fmask pH437) (cmask pH437) (hmask pH437) 1 436 (true, (init pH437), (init pH437))) 437 219 true = true :=
  fin_run (runOK_init (prmOK_of_and H437_fin) true) (by decide) rfl H437_fin ptTest_fst
theorem I437_fin : (prmOK pI437 437 && intTest pI437 (runFrom pI437 (fmask pI437) (cmask pI437) (hmask pI437) 1 436 (true, (init pI437), (init pI437))) 437 13 false) = true := by
  decide +kernel
theorem I437_ok : RunOK pI437 437 (runFrom pI437 (fmask pI437) (cmask pI437) (hmask pI437) 1 436 (true, (init pI437), (init pI437))) ∧ intTest pI437 (runFrom pI437 (fmask pI437) (cmask pI437) (hmask pI437) 1 436 (true, (init pI437), (init pI437))) 437 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I437_fin) true) (by decide) rfl I437_fin intTest_fst
theorem link437 : linkOK pL437 pH437 pI437 = true := by decide +kernel
theorem cvx437 : ConvexBetweenHumps 437 :=
  cvx_of L437_ok H437_ok I437_ok link437 (by decide)

/-! ### `N = 438` -/

def pL438 : Prm := ⟨68, 32, 33, 440, 11, 18446744073709551616, 328478094978360177, 328478094978360177⟩
def pH438 : Prm := ⟨68, 32, 33, 440, 11, 18446744073709551616, 328486891071382385, 328486891071382385⟩
def pI438 : Prm := ⟨60, 29, 28, 440, 11, 18446744073709551616, 328478094978360177, 328486891071382385⟩
theorem L438_fin : (prmOK pL438 438 && ptTest pL438 (runFrom pL438 (fmask pL438) (cmask pL438) (hmask pL438) 1 437 (true, (init pL438), (init pL438))) 438 219 false) = true := by
  decide +kernel
theorem L438_ok : RunOK pL438 438 (runFrom pL438 (fmask pL438) (cmask pL438) (hmask pL438) 1 437 (true, (init pL438), (init pL438))) ∧ ptTest pL438 (runFrom pL438 (fmask pL438) (cmask pL438) (hmask pL438) 1 437 (true, (init pL438), (init pL438))) 438 219 false = true :=
  fin_run (runOK_init (prmOK_of_and L438_fin) true) (by decide) rfl L438_fin ptTest_fst
theorem H438_fin : (prmOK pH438 438 && ptTest pH438 (runFrom pH438 (fmask pH438) (cmask pH438) (hmask pH438) 1 437 (true, (init pH438), (init pH438))) 438 219 true) = true := by
  decide +kernel
theorem H438_ok : RunOK pH438 438 (runFrom pH438 (fmask pH438) (cmask pH438) (hmask pH438) 1 437 (true, (init pH438), (init pH438))) ∧ ptTest pH438 (runFrom pH438 (fmask pH438) (cmask pH438) (hmask pH438) 1 437 (true, (init pH438), (init pH438))) 438 219 true = true :=
  fin_run (runOK_init (prmOK_of_and H438_fin) true) (by decide) rfl H438_fin ptTest_fst
theorem I438_fin : (prmOK pI438 438 && intTest pI438 (runFrom pI438 (fmask pI438) (cmask pI438) (hmask pI438) 1 437 (true, (init pI438), (init pI438))) 438 13 true) = true := by
  decide +kernel
theorem I438_ok : RunOK pI438 438 (runFrom pI438 (fmask pI438) (cmask pI438) (hmask pI438) 1 437 (true, (init pI438), (init pI438))) ∧ intTest pI438 (runFrom pI438 (fmask pI438) (cmask pI438) (hmask pI438) 1 437 (true, (init pI438), (init pI438))) 438 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I438_fin) true) (by decide) rfl I438_fin intTest_fst
theorem link438 : linkOK pL438 pH438 pI438 = true := by decide +kernel
theorem cvx438 : ConvexBetweenHumps 438 :=
  cvx_of L438_ok H438_ok I438_ok link438 (by decide)
theorem cenlink438 : cenLinkOK pI438 438 = true := by decide +kernel
theorem cen438 : CenterUniqueMin 438 ∧ DipHyp 438 ∧ OnePointHyps 438 :=
  cen_of L438_ok H438_ok I438_ok link438 cenlink438

/-! ### `N = 439` -/

def pL439 : Prm := ⟨68, 32, 33, 441, 11, 18446744073709551616, 327909045223455495, 327909045223455495⟩
def pH439 : Prm := ⟨68, 32, 33, 441, 11, 18446744073709551616, 327917841316477703, 327917841316477703⟩
def pI439 : Prm := ⟨60, 29, 28, 441, 11, 18446744073709551616, 327909045223455495, 327917841316477703⟩
theorem L439_fin : (prmOK pL439 439 && ptTest pL439 (runFrom pL439 (fmask pL439) (cmask pL439) (hmask pL439) 1 438 (true, (init pL439), (init pL439))) 439 220 false) = true := by
  decide +kernel
theorem L439_ok : RunOK pL439 439 (runFrom pL439 (fmask pL439) (cmask pL439) (hmask pL439) 1 438 (true, (init pL439), (init pL439))) ∧ ptTest pL439 (runFrom pL439 (fmask pL439) (cmask pL439) (hmask pL439) 1 438 (true, (init pL439), (init pL439))) 439 220 false = true :=
  fin_run (runOK_init (prmOK_of_and L439_fin) true) (by decide) rfl L439_fin ptTest_fst
theorem H439_fin : (prmOK pH439 439 && ptTest pH439 (runFrom pH439 (fmask pH439) (cmask pH439) (hmask pH439) 1 438 (true, (init pH439), (init pH439))) 439 220 true) = true := by
  decide +kernel
theorem H439_ok : RunOK pH439 439 (runFrom pH439 (fmask pH439) (cmask pH439) (hmask pH439) 1 438 (true, (init pH439), (init pH439))) ∧ ptTest pH439 (runFrom pH439 (fmask pH439) (cmask pH439) (hmask pH439) 1 438 (true, (init pH439), (init pH439))) 439 220 true = true :=
  fin_run (runOK_init (prmOK_of_and H439_fin) true) (by decide) rfl H439_fin ptTest_fst
theorem I439_fin : (prmOK pI439 439 && intTest pI439 (runFrom pI439 (fmask pI439) (cmask pI439) (hmask pI439) 1 438 (true, (init pI439), (init pI439))) 439 13 false) = true := by
  decide +kernel
theorem I439_ok : RunOK pI439 439 (runFrom pI439 (fmask pI439) (cmask pI439) (hmask pI439) 1 438 (true, (init pI439), (init pI439))) ∧ intTest pI439 (runFrom pI439 (fmask pI439) (cmask pI439) (hmask pI439) 1 438 (true, (init pI439), (init pI439))) 439 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I439_fin) true) (by decide) rfl I439_fin intTest_fst
theorem link439 : linkOK pL439 pH439 pI439 = true := by decide +kernel
theorem cvx439 : ConvexBetweenHumps 439 :=
  cvx_of L439_ok H439_ok I439_ok link439 (by decide)

/-! ### `N = 440` -/

def pL440 : Prm := ⟨68, 32, 33, 442, 11, 18446744073709551616, 327343601621166277, 327343601621166277⟩
def pH440 : Prm := ⟨68, 32, 33, 442, 11, 18446744073709551616, 327352397714188485, 327352397714188485⟩
def pI440 : Prm := ⟨60, 29, 28, 442, 11, 18446744073709551616, 327343601621166277, 327352397714188485⟩
theorem L440_fin : (prmOK pL440 440 && ptTest pL440 (runFrom pL440 (fmask pL440) (cmask pL440) (hmask pL440) 1 439 (true, (init pL440), (init pL440))) 440 220 false) = true := by
  decide +kernel
theorem L440_ok : RunOK pL440 440 (runFrom pL440 (fmask pL440) (cmask pL440) (hmask pL440) 1 439 (true, (init pL440), (init pL440))) ∧ ptTest pL440 (runFrom pL440 (fmask pL440) (cmask pL440) (hmask pL440) 1 439 (true, (init pL440), (init pL440))) 440 220 false = true :=
  fin_run (runOK_init (prmOK_of_and L440_fin) true) (by decide) rfl L440_fin ptTest_fst
theorem H440_fin : (prmOK pH440 440 && ptTest pH440 (runFrom pH440 (fmask pH440) (cmask pH440) (hmask pH440) 1 439 (true, (init pH440), (init pH440))) 440 220 true) = true := by
  decide +kernel
theorem H440_ok : RunOK pH440 440 (runFrom pH440 (fmask pH440) (cmask pH440) (hmask pH440) 1 439 (true, (init pH440), (init pH440))) ∧ ptTest pH440 (runFrom pH440 (fmask pH440) (cmask pH440) (hmask pH440) 1 439 (true, (init pH440), (init pH440))) 440 220 true = true :=
  fin_run (runOK_init (prmOK_of_and H440_fin) true) (by decide) rfl H440_fin ptTest_fst
theorem I440_fin : (prmOK pI440 440 && intTest pI440 (runFrom pI440 (fmask pI440) (cmask pI440) (hmask pI440) 1 439 (true, (init pI440), (init pI440))) 440 13 true) = true := by
  decide +kernel
theorem I440_ok : RunOK pI440 440 (runFrom pI440 (fmask pI440) (cmask pI440) (hmask pI440) 1 439 (true, (init pI440), (init pI440))) ∧ intTest pI440 (runFrom pI440 (fmask pI440) (cmask pI440) (hmask pI440) 1 439 (true, (init pI440), (init pI440))) 440 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I440_fin) true) (by decide) rfl I440_fin intTest_fst
theorem link440 : linkOK pL440 pH440 pI440 = true := by decide +kernel
theorem cvx440 : ConvexBetweenHumps 440 :=
  cvx_of L440_ok H440_ok I440_ok link440 (by decide)
theorem cenlink440 : cenLinkOK pI440 440 = true := by decide +kernel
theorem cen440 : CenterUniqueMin 440 ∧ DipHyp 440 ∧ OnePointHyps 440 :=
  cen_of L440_ok H440_ok I440_ok link440 cenlink440

/-! ### `N = 441` -/

def pL441 : Prm := ⟨68, 32, 33, 443, 11, 18446744073709551616, 326778909191786197, 326778909191786197⟩
def pH441 : Prm := ⟨68, 32, 33, 443, 11, 18446744073709551616, 326787705284808405, 326787705284808405⟩
def pI441 : Prm := ⟨60, 29, 28, 443, 11, 18446744073709551616, 326778909191786197, 326787705284808405⟩
theorem L441_fin : (prmOK pL441 441 && ptTest pL441 (runFrom pL441 (fmask pL441) (cmask pL441) (hmask pL441) 1 440 (true, (init pL441), (init pL441))) 441 221 false) = true := by
  decide +kernel
theorem L441_ok : RunOK pL441 441 (runFrom pL441 (fmask pL441) (cmask pL441) (hmask pL441) 1 440 (true, (init pL441), (init pL441))) ∧ ptTest pL441 (runFrom pL441 (fmask pL441) (cmask pL441) (hmask pL441) 1 440 (true, (init pL441), (init pL441))) 441 221 false = true :=
  fin_run (runOK_init (prmOK_of_and L441_fin) true) (by decide) rfl L441_fin ptTest_fst
theorem H441_fin : (prmOK pH441 441 && ptTest pH441 (runFrom pH441 (fmask pH441) (cmask pH441) (hmask pH441) 1 440 (true, (init pH441), (init pH441))) 441 221 true) = true := by
  decide +kernel
theorem H441_ok : RunOK pH441 441 (runFrom pH441 (fmask pH441) (cmask pH441) (hmask pH441) 1 440 (true, (init pH441), (init pH441))) ∧ ptTest pH441 (runFrom pH441 (fmask pH441) (cmask pH441) (hmask pH441) 1 440 (true, (init pH441), (init pH441))) 441 221 true = true :=
  fin_run (runOK_init (prmOK_of_and H441_fin) true) (by decide) rfl H441_fin ptTest_fst
theorem I441_fin : (prmOK pI441 441 && intTest pI441 (runFrom pI441 (fmask pI441) (cmask pI441) (hmask pI441) 1 440 (true, (init pI441), (init pI441))) 441 13 false) = true := by
  decide +kernel
theorem I441_ok : RunOK pI441 441 (runFrom pI441 (fmask pI441) (cmask pI441) (hmask pI441) 1 440 (true, (init pI441), (init pI441))) ∧ intTest pI441 (runFrom pI441 (fmask pI441) (cmask pI441) (hmask pI441) 1 440 (true, (init pI441), (init pI441))) 441 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I441_fin) true) (by decide) rfl I441_fin intTest_fst
theorem link441 : linkOK pL441 pH441 pI441 = true := by decide +kernel
theorem cvx441 : ConvexBetweenHumps 441 :=
  cvx_of L441_ok H441_ok I441_ok link441 (by decide)

/-! ### `N = 442` -/

def pL442 : Prm := ⟨68, 32, 33, 444, 11, 18446744073709551616, 326217777350862742, 326217777350862742⟩
def pH442 : Prm := ⟨68, 32, 33, 444, 11, 18446744073709551616, 326226573443884950, 326226573443884950⟩
def pI442 : Prm := ⟨60, 29, 28, 444, 11, 18446744073709551616, 326217777350862742, 326226573443884950⟩
theorem L442_fin : (prmOK pL442 442 && ptTest pL442 (runFrom pL442 (fmask pL442) (cmask pL442) (hmask pL442) 1 441 (true, (init pL442), (init pL442))) 442 221 false) = true := by
  decide +kernel
theorem L442_ok : RunOK pL442 442 (runFrom pL442 (fmask pL442) (cmask pL442) (hmask pL442) 1 441 (true, (init pL442), (init pL442))) ∧ ptTest pL442 (runFrom pL442 (fmask pL442) (cmask pL442) (hmask pL442) 1 441 (true, (init pL442), (init pL442))) 442 221 false = true :=
  fin_run (runOK_init (prmOK_of_and L442_fin) true) (by decide) rfl L442_fin ptTest_fst
theorem H442_fin : (prmOK pH442 442 && ptTest pH442 (runFrom pH442 (fmask pH442) (cmask pH442) (hmask pH442) 1 441 (true, (init pH442), (init pH442))) 442 221 true) = true := by
  decide +kernel
theorem H442_ok : RunOK pH442 442 (runFrom pH442 (fmask pH442) (cmask pH442) (hmask pH442) 1 441 (true, (init pH442), (init pH442))) ∧ ptTest pH442 (runFrom pH442 (fmask pH442) (cmask pH442) (hmask pH442) 1 441 (true, (init pH442), (init pH442))) 442 221 true = true :=
  fin_run (runOK_init (prmOK_of_and H442_fin) true) (by decide) rfl H442_fin ptTest_fst
theorem I442_fin : (prmOK pI442 442 && intTest pI442 (runFrom pI442 (fmask pI442) (cmask pI442) (hmask pI442) 1 441 (true, (init pI442), (init pI442))) 442 13 true) = true := by
  decide +kernel
theorem I442_ok : RunOK pI442 442 (runFrom pI442 (fmask pI442) (cmask pI442) (hmask pI442) 1 441 (true, (init pI442), (init pI442))) ∧ intTest pI442 (runFrom pI442 (fmask pI442) (cmask pI442) (hmask pI442) 1 441 (true, (init pI442), (init pI442))) 442 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I442_fin) true) (by decide) rfl I442_fin intTest_fst
theorem link442 : linkOK pL442 pH442 pI442 = true := by decide +kernel
theorem cvx442 : ConvexBetweenHumps 442 :=
  cvx_of L442_ok H442_ok I442_ok link442 (by decide)
theorem cenlink442 : cenLinkOK pI442 442 = true := by decide +kernel
theorem cen442 : CenterUniqueMin 442 ∧ DipHyp 442 ∧ OnePointHyps 442 :=
  cen_of L442_ok H442_ok I442_ok link442 cenlink442

/-! ### `N = 443` -/

def pL443 : Prm := ⟨68, 32, 33, 445, 11, 18446744073709551616, 325657390321507179, 325657390321507179⟩
def pH443 : Prm := ⟨68, 32, 33, 445, 11, 18446744073709551616, 325666186414529387, 325666186414529387⟩
def pI443 : Prm := ⟨60, 29, 28, 445, 11, 18446744073709551616, 325657390321507179, 325666186414529387⟩
theorem L443_fin : (prmOK pL443 443 && ptTest pL443 (runFrom pL443 (fmask pL443) (cmask pL443) (hmask pL443) 1 442 (true, (init pL443), (init pL443))) 443 222 false) = true := by
  decide +kernel
theorem L443_ok : RunOK pL443 443 (runFrom pL443 (fmask pL443) (cmask pL443) (hmask pL443) 1 442 (true, (init pL443), (init pL443))) ∧ ptTest pL443 (runFrom pL443 (fmask pL443) (cmask pL443) (hmask pL443) 1 442 (true, (init pL443), (init pL443))) 443 222 false = true :=
  fin_run (runOK_init (prmOK_of_and L443_fin) true) (by decide) rfl L443_fin ptTest_fst
theorem H443_fin : (prmOK pH443 443 && ptTest pH443 (runFrom pH443 (fmask pH443) (cmask pH443) (hmask pH443) 1 442 (true, (init pH443), (init pH443))) 443 222 true) = true := by
  decide +kernel
theorem H443_ok : RunOK pH443 443 (runFrom pH443 (fmask pH443) (cmask pH443) (hmask pH443) 1 442 (true, (init pH443), (init pH443))) ∧ ptTest pH443 (runFrom pH443 (fmask pH443) (cmask pH443) (hmask pH443) 1 442 (true, (init pH443), (init pH443))) 443 222 true = true :=
  fin_run (runOK_init (prmOK_of_and H443_fin) true) (by decide) rfl H443_fin ptTest_fst
theorem I443_fin : (prmOK pI443 443 && intTest pI443 (runFrom pI443 (fmask pI443) (cmask pI443) (hmask pI443) 1 442 (true, (init pI443), (init pI443))) 443 13 false) = true := by
  decide +kernel
theorem I443_ok : RunOK pI443 443 (runFrom pI443 (fmask pI443) (cmask pI443) (hmask pI443) 1 442 (true, (init pI443), (init pI443))) ∧ intTest pI443 (runFrom pI443 (fmask pI443) (cmask pI443) (hmask pI443) 1 442 (true, (init pI443), (init pI443))) 443 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I443_fin) true) (by decide) rfl I443_fin intTest_fst
theorem link443 : linkOK pL443 pH443 pI443 = true := by decide +kernel
theorem cvx443 : ConvexBetweenHumps 443 :=
  cvx_of L443_ok H443_ok I443_ok link443 (by decide)

/-! ### `N = 444` -/

def pL444 : Prm := ⟨68, 32, 33, 446, 11, 18446744073709551616, 325100519091378674, 325100519091378674⟩
def pH444 : Prm := ⟨68, 32, 33, 446, 11, 18446744073709551616, 325109315184400882, 325109315184400882⟩
def pI444 : Prm := ⟨60, 29, 28, 446, 11, 18446744073709551616, 325100519091378674, 325109315184400882⟩
theorem L444_fin : (prmOK pL444 444 && ptTest pL444 (runFrom pL444 (fmask pL444) (cmask pL444) (hmask pL444) 1 443 (true, (init pL444), (init pL444))) 444 222 false) = true := by
  decide +kernel
theorem L444_ok : RunOK pL444 444 (runFrom pL444 (fmask pL444) (cmask pL444) (hmask pL444) 1 443 (true, (init pL444), (init pL444))) ∧ ptTest pL444 (runFrom pL444 (fmask pL444) (cmask pL444) (hmask pL444) 1 443 (true, (init pL444), (init pL444))) 444 222 false = true :=
  fin_run (runOK_init (prmOK_of_and L444_fin) true) (by decide) rfl L444_fin ptTest_fst
theorem H444_fin : (prmOK pH444 444 && ptTest pH444 (runFrom pH444 (fmask pH444) (cmask pH444) (hmask pH444) 1 443 (true, (init pH444), (init pH444))) 444 222 true) = true := by
  decide +kernel
theorem H444_ok : RunOK pH444 444 (runFrom pH444 (fmask pH444) (cmask pH444) (hmask pH444) 1 443 (true, (init pH444), (init pH444))) ∧ ptTest pH444 (runFrom pH444 (fmask pH444) (cmask pH444) (hmask pH444) 1 443 (true, (init pH444), (init pH444))) 444 222 true = true :=
  fin_run (runOK_init (prmOK_of_and H444_fin) true) (by decide) rfl H444_fin ptTest_fst
theorem I444_fin : (prmOK pI444 444 && intTest pI444 (runFrom pI444 (fmask pI444) (cmask pI444) (hmask pI444) 1 443 (true, (init pI444), (init pI444))) 444 13 true) = true := by
  decide +kernel
theorem I444_ok : RunOK pI444 444 (runFrom pI444 (fmask pI444) (cmask pI444) (hmask pI444) 1 443 (true, (init pI444), (init pI444))) ∧ intTest pI444 (runFrom pI444 (fmask pI444) (cmask pI444) (hmask pI444) 1 443 (true, (init pI444), (init pI444))) 444 13 true = true :=
  fin_run (runOK_init (prmOK_of_and I444_fin) true) (by decide) rfl I444_fin intTest_fst
theorem link444 : linkOK pL444 pH444 pI444 = true := by decide +kernel
theorem cvx444 : ConvexBetweenHumps 444 :=
  cvx_of L444_ok H444_ok I444_ok link444 (by decide)
theorem cenlink444 : cenLinkOK pI444 444 = true := by decide +kernel
theorem cen444 : CenterUniqueMin 444 ∧ DipHyp 444 ∧ OnePointHyps 444 :=
  cen_of L444_ok H444_ok I444_ok link444 cenlink444

/-! ### `N = 445` -/

def pL445 : Prm := ⟨69, 33, 33, 447, 11, 18446744073709551616, 324544386377054989, 324544386377054989⟩
def pH445 : Prm := ⟨69, 33, 33, 447, 11, 18446744073709551616, 324553182470077197, 324553182470077197⟩
def pI445 : Prm := ⟨60, 29, 28, 447, 11, 18446744073709551616, 324544386377054989, 324553182470077197⟩
theorem L445_fin : (prmOK pL445 445 && ptTest pL445 (runFrom pL445 (fmask pL445) (cmask pL445) (hmask pL445) 1 444 (true, (init pL445), (init pL445))) 445 223 false) = true := by
  decide +kernel
theorem L445_ok : RunOK pL445 445 (runFrom pL445 (fmask pL445) (cmask pL445) (hmask pL445) 1 444 (true, (init pL445), (init pL445))) ∧ ptTest pL445 (runFrom pL445 (fmask pL445) (cmask pL445) (hmask pL445) 1 444 (true, (init pL445), (init pL445))) 445 223 false = true :=
  fin_run (runOK_init (prmOK_of_and L445_fin) true) (by decide) rfl L445_fin ptTest_fst
theorem H445_fin : (prmOK pH445 445 && ptTest pH445 (runFrom pH445 (fmask pH445) (cmask pH445) (hmask pH445) 1 444 (true, (init pH445), (init pH445))) 445 223 true) = true := by
  decide +kernel
theorem H445_ok : RunOK pH445 445 (runFrom pH445 (fmask pH445) (cmask pH445) (hmask pH445) 1 444 (true, (init pH445), (init pH445))) ∧ ptTest pH445 (runFrom pH445 (fmask pH445) (cmask pH445) (hmask pH445) 1 444 (true, (init pH445), (init pH445))) 445 223 true = true :=
  fin_run (runOK_init (prmOK_of_and H445_fin) true) (by decide) rfl H445_fin ptTest_fst
theorem I445_fin : (prmOK pI445 445 && intTest pI445 (runFrom pI445 (fmask pI445) (cmask pI445) (hmask pI445) 1 444 (true, (init pI445), (init pI445))) 445 13 false) = true := by
  decide +kernel
theorem I445_ok : RunOK pI445 445 (runFrom pI445 (fmask pI445) (cmask pI445) (hmask pI445) 1 444 (true, (init pI445), (init pI445))) ∧ intTest pI445 (runFrom pI445 (fmask pI445) (cmask pI445) (hmask pI445) 1 444 (true, (init pI445), (init pI445))) 445 13 false = true :=
  fin_run (runOK_init (prmOK_of_and I445_fin) true) (by decide) rfl I445_fin intTest_fst
theorem link445 : linkOK pL445 pH445 pI445 = true := by decide +kernel
theorem cvx445 : ConvexBetweenHumps 445 :=
  cvx_of L445_ok H445_ok I445_ok link445 (by decide)

/-! ### `N = 446` -/

def pL446 : Prm := ⟨68, 32, 33, 448, 11, 18446744073709551616, 323991725431166678, 323991725431166678⟩
def pH446 : Prm := ⟨68, 32, 33, 448, 11, 18446744073709551616, 324000521524188886, 324000521524188886⟩
def pI446 : Prm := ⟨60, 29, 28, 448, 11, 18446744073709551616, 323991725431166678, 324000521524188886⟩
theorem L446_fin : (prmOK pL446 446 && ptTest pL446 (runFrom pL446 (fmask pL446) (cmask pL446) (hmask pL446) 1 445 (true, (init pL446), (init pL446))) 446 223 false) = true := by
  decide +kernel
theorem L446_ok : RunOK pL446 446 (runFrom pL446 (fmask pL446) (cmask pL446) (hmask pL446) 1 445 (true, (init pL446), (init pL446))) ∧ ptTest pL446 (runFrom pL446 (fmask pL446) (cmask pL446) (hmask pL446) 1 445 (true, (init pL446), (init pL446))) 446 223 false = true :=
  fin_run (runOK_init (prmOK_of_and L446_fin) true) (by decide) rfl L446_fin ptTest_fst
theorem H446_fin : (prmOK pH446 446 && ptTest pH446 (runFrom pH446 (fmask pH446) (cmask pH446) (hmask pH446) 1 445 (true, (init pH446), (init pH446))) 446 223 true) = true := by
  decide +kernel
theorem H446_ok : RunOK pH446 446 (runFrom pH446 (fmask pH446) (cmask pH446) (hmask pH446) 1 445 (true, (init pH446), (init pH446))) ∧ ptTest pH446 (runFrom pH446 (fmask pH446) (cmask pH446) (hmask pH446) 1 445 (true, (init pH446), (init pH446))) 446 223 true = true :=
  fin_run (runOK_init (prmOK_of_and H446_fin) true) (by decide) rfl H446_fin ptTest_fst
theorem I446_fin : (prmOK pI446 446 && intTest pI446 (runFrom pI446 (fmask pI446) (cmask pI446) (hmask pI446) 1 445 (true, (init pI446), (init pI446))) 446 14 true) = true := by
  decide +kernel
theorem I446_ok : RunOK pI446 446 (runFrom pI446 (fmask pI446) (cmask pI446) (hmask pI446) 1 445 (true, (init pI446), (init pI446))) ∧ intTest pI446 (runFrom pI446 (fmask pI446) (cmask pI446) (hmask pI446) 1 445 (true, (init pI446), (init pI446))) 446 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I446_fin) true) (by decide) rfl I446_fin intTest_fst
theorem link446 : linkOK pL446 pH446 pI446 = true := by decide +kernel
theorem cvx446 : ConvexBetweenHumps 446 :=
  cvx_of L446_ok H446_ok I446_ok link446 (by decide)
theorem cenlink446 : cenLinkOK pI446 446 = true := by decide +kernel
theorem cen446 : CenterUniqueMin 446 ∧ DipHyp 446 ∧ OnePointHyps 446 :=
  cen_of L446_ok H446_ok I446_ok link446 cenlink446

/-! ### `N = 447` -/

def pL447 : Prm := ⟨68, 32, 33, 449, 11, 18446744073709551616, 323439796770252654, 323439796770252654⟩
def pH447 : Prm := ⟨68, 32, 33, 449, 11, 18446744073709551616, 323448592863274862, 323448592863274862⟩
def pI447 : Prm := ⟨60, 29, 28, 449, 11, 18446744073709551616, 323439796770252654, 323448592863274862⟩
theorem L447_fin : (prmOK pL447 447 && ptTest pL447 (runFrom pL447 (fmask pL447) (cmask pL447) (hmask pL447) 1 446 (true, (init pL447), (init pL447))) 447 224 false) = true := by
  decide +kernel
theorem L447_ok : RunOK pL447 447 (runFrom pL447 (fmask pL447) (cmask pL447) (hmask pL447) 1 446 (true, (init pL447), (init pL447))) ∧ ptTest pL447 (runFrom pL447 (fmask pL447) (cmask pL447) (hmask pL447) 1 446 (true, (init pL447), (init pL447))) 447 224 false = true :=
  fin_run (runOK_init (prmOK_of_and L447_fin) true) (by decide) rfl L447_fin ptTest_fst
theorem H447_fin : (prmOK pH447 447 && ptTest pH447 (runFrom pH447 (fmask pH447) (cmask pH447) (hmask pH447) 1 446 (true, (init pH447), (init pH447))) 447 224 true) = true := by
  decide +kernel
theorem H447_ok : RunOK pH447 447 (runFrom pH447 (fmask pH447) (cmask pH447) (hmask pH447) 1 446 (true, (init pH447), (init pH447))) ∧ ptTest pH447 (runFrom pH447 (fmask pH447) (cmask pH447) (hmask pH447) 1 446 (true, (init pH447), (init pH447))) 447 224 true = true :=
  fin_run (runOK_init (prmOK_of_and H447_fin) true) (by decide) rfl H447_fin ptTest_fst
theorem I447_fin : (prmOK pI447 447 && intTest pI447 (runFrom pI447 (fmask pI447) (cmask pI447) (hmask pI447) 1 446 (true, (init pI447), (init pI447))) 447 14 false) = true := by
  decide +kernel
theorem I447_ok : RunOK pI447 447 (runFrom pI447 (fmask pI447) (cmask pI447) (hmask pI447) 1 446 (true, (init pI447), (init pI447))) ∧ intTest pI447 (runFrom pI447 (fmask pI447) (cmask pI447) (hmask pI447) 1 446 (true, (init pI447), (init pI447))) 447 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I447_fin) true) (by decide) rfl I447_fin intTest_fst
theorem link447 : linkOK pL447 pH447 pI447 = true := by decide +kernel
theorem cvx447 : ConvexBetweenHumps 447 :=
  cvx_of L447_ok H447_ok I447_ok link447 (by decide)

/-! ### `N = 448` -/

def pL448 : Prm := ⟨69, 33, 33, 450, 11, 18446744073709551616, 322891296589297750, 322891296589297750⟩
def pH448 : Prm := ⟨69, 33, 33, 450, 11, 18446744073709551616, 322900092682319958, 322900092682319958⟩
def pI448 : Prm := ⟨61, 29, 29, 450, 11, 18446744073709551616, 322891296589297750, 322900092682319958⟩
theorem L448_fin : (prmOK pL448 448 && ptTest pL448 (runFrom pL448 (fmask pL448) (cmask pL448) (hmask pL448) 1 447 (true, (init pL448), (init pL448))) 448 224 false) = true := by
  decide +kernel
theorem L448_ok : RunOK pL448 448 (runFrom pL448 (fmask pL448) (cmask pL448) (hmask pL448) 1 447 (true, (init pL448), (init pL448))) ∧ ptTest pL448 (runFrom pL448 (fmask pL448) (cmask pL448) (hmask pL448) 1 447 (true, (init pL448), (init pL448))) 448 224 false = true :=
  fin_run (runOK_init (prmOK_of_and L448_fin) true) (by decide) rfl L448_fin ptTest_fst
theorem H448_fin : (prmOK pH448 448 && ptTest pH448 (runFrom pH448 (fmask pH448) (cmask pH448) (hmask pH448) 1 447 (true, (init pH448), (init pH448))) 448 224 true) = true := by
  decide +kernel
theorem H448_ok : RunOK pH448 448 (runFrom pH448 (fmask pH448) (cmask pH448) (hmask pH448) 1 447 (true, (init pH448), (init pH448))) ∧ ptTest pH448 (runFrom pH448 (fmask pH448) (cmask pH448) (hmask pH448) 1 447 (true, (init pH448), (init pH448))) 448 224 true = true :=
  fin_run (runOK_init (prmOK_of_and H448_fin) true) (by decide) rfl H448_fin ptTest_fst
theorem I448_fin : (prmOK pI448 448 && intTest pI448 (runFrom pI448 (fmask pI448) (cmask pI448) (hmask pI448) 1 447 (true, (init pI448), (init pI448))) 448 14 true) = true := by
  decide +kernel
theorem I448_ok : RunOK pI448 448 (runFrom pI448 (fmask pI448) (cmask pI448) (hmask pI448) 1 447 (true, (init pI448), (init pI448))) ∧ intTest pI448 (runFrom pI448 (fmask pI448) (cmask pI448) (hmask pI448) 1 447 (true, (init pI448), (init pI448))) 448 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I448_fin) true) (by decide) rfl I448_fin intTest_fst
theorem link448 : linkOK pL448 pH448 pI448 = true := by decide +kernel
theorem cvx448 : ConvexBetweenHumps 448 :=
  cvx_of L448_ok H448_ok I448_ok link448 (by decide)
theorem cenlink448 : cenLinkOK pI448 448 = true := by decide +kernel
theorem cen448 : CenterUniqueMin 448 ∧ DipHyp 448 ∧ OnePointHyps 448 :=
  cen_of L448_ok H448_ok I448_ok link448 cenlink448

/-! ### `N = 449` -/

def pL449 : Prm := ⟨68, 32, 33, 451, 11, 18446744073709551616, 322343522526755055, 322343522526755055⟩
def pH449 : Prm := ⟨68, 32, 33, 451, 11, 18446744073709551616, 322352318619777263, 322352318619777263⟩
def pI449 : Prm := ⟨61, 29, 29, 451, 11, 18446744073709551616, 322343522526755055, 322352318619777263⟩
theorem L449_fin : (prmOK pL449 449 && ptTest pL449 (runFrom pL449 (fmask pL449) (cmask pL449) (hmask pL449) 1 448 (true, (init pL449), (init pL449))) 449 225 false) = true := by
  decide +kernel
theorem L449_ok : RunOK pL449 449 (runFrom pL449 (fmask pL449) (cmask pL449) (hmask pL449) 1 448 (true, (init pL449), (init pL449))) ∧ ptTest pL449 (runFrom pL449 (fmask pL449) (cmask pL449) (hmask pL449) 1 448 (true, (init pL449), (init pL449))) 449 225 false = true :=
  fin_run (runOK_init (prmOK_of_and L449_fin) true) (by decide) rfl L449_fin ptTest_fst
theorem H449_fin : (prmOK pH449 449 && ptTest pH449 (runFrom pH449 (fmask pH449) (cmask pH449) (hmask pH449) 1 448 (true, (init pH449), (init pH449))) 449 225 true) = true := by
  decide +kernel
theorem H449_ok : RunOK pH449 449 (runFrom pH449 (fmask pH449) (cmask pH449) (hmask pH449) 1 448 (true, (init pH449), (init pH449))) ∧ ptTest pH449 (runFrom pH449 (fmask pH449) (cmask pH449) (hmask pH449) 1 448 (true, (init pH449), (init pH449))) 449 225 true = true :=
  fin_run (runOK_init (prmOK_of_and H449_fin) true) (by decide) rfl H449_fin ptTest_fst
theorem I449_fin : (prmOK pI449 449 && intTest pI449 (runFrom pI449 (fmask pI449) (cmask pI449) (hmask pI449) 1 448 (true, (init pI449), (init pI449))) 449 14 false) = true := by
  decide +kernel
theorem I449_ok : RunOK pI449 449 (runFrom pI449 (fmask pI449) (cmask pI449) (hmask pI449) 1 448 (true, (init pI449), (init pI449))) ∧ intTest pI449 (runFrom pI449 (fmask pI449) (cmask pI449) (hmask pI449) 1 448 (true, (init pI449), (init pI449))) 449 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I449_fin) true) (by decide) rfl I449_fin intTest_fst
theorem link449 : linkOK pL449 pH449 pI449 = true := by decide +kernel
theorem cvx449 : ConvexBetweenHumps 449 :=
  cvx_of L449_ok H449_ok I449_ok link449 (by decide)

/-! ### `N = 450` -/

def pL450 : Prm := ⟨69, 33, 33, 452, 11, 18446744073709551616, 321799134382257133, 321799134382257133⟩
def pH450 : Prm := ⟨69, 33, 33, 452, 11, 18446744073709551616, 321807930475279341, 321807930475279341⟩
def pI450 : Prm := ⟨61, 29, 29, 452, 11, 18446744073709551616, 321799134382257133, 321807930475279341⟩
theorem L450_fin : (prmOK pL450 450 && ptTest pL450 (runFrom pL450 (fmask pL450) (cmask pL450) (hmask pL450) 1 449 (true, (init pL450), (init pL450))) 450 225 false) = true := by
  decide +kernel
theorem L450_ok : RunOK pL450 450 (runFrom pL450 (fmask pL450) (cmask pL450) (hmask pL450) 1 449 (true, (init pL450), (init pL450))) ∧ ptTest pL450 (runFrom pL450 (fmask pL450) (cmask pL450) (hmask pL450) 1 449 (true, (init pL450), (init pL450))) 450 225 false = true :=
  fin_run (runOK_init (prmOK_of_and L450_fin) true) (by decide) rfl L450_fin ptTest_fst
theorem H450_fin : (prmOK pH450 450 && ptTest pH450 (runFrom pH450 (fmask pH450) (cmask pH450) (hmask pH450) 1 449 (true, (init pH450), (init pH450))) 450 225 true) = true := by
  decide +kernel
theorem H450_ok : RunOK pH450 450 (runFrom pH450 (fmask pH450) (cmask pH450) (hmask pH450) 1 449 (true, (init pH450), (init pH450))) ∧ ptTest pH450 (runFrom pH450 (fmask pH450) (cmask pH450) (hmask pH450) 1 449 (true, (init pH450), (init pH450))) 450 225 true = true :=
  fin_run (runOK_init (prmOK_of_and H450_fin) true) (by decide) rfl H450_fin ptTest_fst
theorem I450_fin : (prmOK pI450 450 && intTest pI450 (runFrom pI450 (fmask pI450) (cmask pI450) (hmask pI450) 1 449 (true, (init pI450), (init pI450))) 450 14 true) = true := by
  decide +kernel
theorem I450_ok : RunOK pI450 450 (runFrom pI450 (fmask pI450) (cmask pI450) (hmask pI450) 1 449 (true, (init pI450), (init pI450))) ∧ intTest pI450 (runFrom pI450 (fmask pI450) (cmask pI450) (hmask pI450) 1 449 (true, (init pI450), (init pI450))) 450 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I450_fin) true) (by decide) rfl I450_fin intTest_fst
theorem link450 : linkOK pL450 pH450 pI450 = true := by decide +kernel
theorem cvx450 : ConvexBetweenHumps 450 :=
  cvx_of L450_ok H450_ok I450_ok link450 (by decide)
theorem cenlink450 : cenLinkOK pI450 450 = true := by decide +kernel
theorem cen450 : CenterUniqueMin 450 ∧ DipHyp 450 ∧ OnePointHyps 450 :=
  cen_of L450_ok H450_ok I450_ok link450 cenlink450

/-! ### `N = 451` -/

def pL451 : Prm := ⟨69, 33, 33, 453, 11, 18446744073709551616, 321255466253305952, 321255466253305952⟩
def pH451 : Prm := ⟨69, 33, 33, 453, 11, 18446744073709551616, 321264262346328160, 321264262346328160⟩
def pI451 : Prm := ⟨61, 29, 29, 453, 11, 18446744073709551616, 321255466253305952, 321264262346328160⟩
theorem L451_fin : (prmOK pL451 451 && ptTest pL451 (runFrom pL451 (fmask pL451) (cmask pL451) (hmask pL451) 1 450 (true, (init pL451), (init pL451))) 451 226 false) = true := by
  decide +kernel
theorem L451_ok : RunOK pL451 451 (runFrom pL451 (fmask pL451) (cmask pL451) (hmask pL451) 1 450 (true, (init pL451), (init pL451))) ∧ ptTest pL451 (runFrom pL451 (fmask pL451) (cmask pL451) (hmask pL451) 1 450 (true, (init pL451), (init pL451))) 451 226 false = true :=
  fin_run (runOK_init (prmOK_of_and L451_fin) true) (by decide) rfl L451_fin ptTest_fst
theorem H451_fin : (prmOK pH451 451 && ptTest pH451 (runFrom pH451 (fmask pH451) (cmask pH451) (hmask pH451) 1 450 (true, (init pH451), (init pH451))) 451 226 true) = true := by
  decide +kernel
theorem H451_ok : RunOK pH451 451 (runFrom pH451 (fmask pH451) (cmask pH451) (hmask pH451) 1 450 (true, (init pH451), (init pH451))) ∧ ptTest pH451 (runFrom pH451 (fmask pH451) (cmask pH451) (hmask pH451) 1 450 (true, (init pH451), (init pH451))) 451 226 true = true :=
  fin_run (runOK_init (prmOK_of_and H451_fin) true) (by decide) rfl H451_fin ptTest_fst
theorem I451_fin : (prmOK pI451 451 && intTest pI451 (runFrom pI451 (fmask pI451) (cmask pI451) (hmask pI451) 1 450 (true, (init pI451), (init pI451))) 451 14 false) = true := by
  decide +kernel
theorem I451_ok : RunOK pI451 451 (runFrom pI451 (fmask pI451) (cmask pI451) (hmask pI451) 1 450 (true, (init pI451), (init pI451))) ∧ intTest pI451 (runFrom pI451 (fmask pI451) (cmask pI451) (hmask pI451) 1 450 (true, (init pI451), (init pI451))) 451 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I451_fin) true) (by decide) rfl I451_fin intTest_fst
theorem link451 : linkOK pL451 pH451 pI451 = true := by decide +kernel
theorem cvx451 : ConvexBetweenHumps 451 :=
  cvx_of L451_ok H451_ok I451_ok link451 (by decide)

/-! ### `N = 452` -/

def pL452 : Prm := ⟨69, 33, 33, 454, 11, 18446744073709551616, 320715142191754754, 320715142191754754⟩
def pH452 : Prm := ⟨69, 33, 33, 454, 11, 18446744073709551616, 320723938284776962, 320723938284776962⟩
def pI452 : Prm := ⟨61, 29, 29, 454, 11, 18446744073709551616, 320715142191754754, 320723938284776962⟩
theorem L452_fin : (prmOK pL452 452 && ptTest pL452 (runFrom pL452 (fmask pL452) (cmask pL452) (hmask pL452) 1 451 (true, (init pL452), (init pL452))) 452 226 false) = true := by
  decide +kernel
theorem L452_ok : RunOK pL452 452 (runFrom pL452 (fmask pL452) (cmask pL452) (hmask pL452) 1 451 (true, (init pL452), (init pL452))) ∧ ptTest pL452 (runFrom pL452 (fmask pL452) (cmask pL452) (hmask pL452) 1 451 (true, (init pL452), (init pL452))) 452 226 false = true :=
  fin_run (runOK_init (prmOK_of_and L452_fin) true) (by decide) rfl L452_fin ptTest_fst
theorem H452_fin : (prmOK pH452 452 && ptTest pH452 (runFrom pH452 (fmask pH452) (cmask pH452) (hmask pH452) 1 451 (true, (init pH452), (init pH452))) 452 226 true) = true := by
  decide +kernel
theorem H452_ok : RunOK pH452 452 (runFrom pH452 (fmask pH452) (cmask pH452) (hmask pH452) 1 451 (true, (init pH452), (init pH452))) ∧ ptTest pH452 (runFrom pH452 (fmask pH452) (cmask pH452) (hmask pH452) 1 451 (true, (init pH452), (init pH452))) 452 226 true = true :=
  fin_run (runOK_init (prmOK_of_and H452_fin) true) (by decide) rfl H452_fin ptTest_fst
theorem I452_fin : (prmOK pI452 452 && intTest pI452 (runFrom pI452 (fmask pI452) (cmask pI452) (hmask pI452) 1 451 (true, (init pI452), (init pI452))) 452 14 true) = true := by
  decide +kernel
theorem I452_ok : RunOK pI452 452 (runFrom pI452 (fmask pI452) (cmask pI452) (hmask pI452) 1 451 (true, (init pI452), (init pI452))) ∧ intTest pI452 (runFrom pI452 (fmask pI452) (cmask pI452) (hmask pI452) 1 451 (true, (init pI452), (init pI452))) 452 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I452_fin) true) (by decide) rfl I452_fin intTest_fst
theorem link452 : linkOK pL452 pH452 pI452 = true := by decide +kernel
theorem cvx452 : ConvexBetweenHumps 452 :=
  cvx_of L452_ok H452_ok I452_ok link452 (by decide)
theorem cenlink452 : cenLinkOK pI452 452 = true := by decide +kernel
theorem cen452 : CenterUniqueMin 452 ∧ DipHyp 452 ∧ OnePointHyps 452 :=
  cen_of L452_ok H452_ok I452_ok link452 cenlink452

/-! ### `N = 453` -/

def pL453 : Prm := ⟨69, 33, 33, 455, 11, 18446744073709551616, 320175532105843566, 320175532105843566⟩
def pH453 : Prm := ⟨69, 33, 33, 455, 11, 18446744073709551616, 320184328198865774, 320184328198865774⟩
def pI453 : Prm := ⟨60, 29, 28, 455, 11, 18446744073709551616, 320175532105843566, 320184328198865774⟩
theorem L453_fin : (prmOK pL453 453 && ptTest pL453 (runFrom pL453 (fmask pL453) (cmask pL453) (hmask pL453) 1 452 (true, (init pL453), (init pL453))) 453 227 false) = true := by
  decide +kernel
theorem L453_ok : RunOK pL453 453 (runFrom pL453 (fmask pL453) (cmask pL453) (hmask pL453) 1 452 (true, (init pL453), (init pL453))) ∧ ptTest pL453 (runFrom pL453 (fmask pL453) (cmask pL453) (hmask pL453) 1 452 (true, (init pL453), (init pL453))) 453 227 false = true :=
  fin_run (runOK_init (prmOK_of_and L453_fin) true) (by decide) rfl L453_fin ptTest_fst
theorem H453_fin : (prmOK pH453 453 && ptTest pH453 (runFrom pH453 (fmask pH453) (cmask pH453) (hmask pH453) 1 452 (true, (init pH453), (init pH453))) 453 227 true) = true := by
  decide +kernel
theorem H453_ok : RunOK pH453 453 (runFrom pH453 (fmask pH453) (cmask pH453) (hmask pH453) 1 452 (true, (init pH453), (init pH453))) ∧ ptTest pH453 (runFrom pH453 (fmask pH453) (cmask pH453) (hmask pH453) 1 452 (true, (init pH453), (init pH453))) 453 227 true = true :=
  fin_run (runOK_init (prmOK_of_and H453_fin) true) (by decide) rfl H453_fin ptTest_fst
theorem I453_fin : (prmOK pI453 453 && intTest pI453 (runFrom pI453 (fmask pI453) (cmask pI453) (hmask pI453) 1 452 (true, (init pI453), (init pI453))) 453 14 false) = true := by
  decide +kernel
theorem I453_ok : RunOK pI453 453 (runFrom pI453 (fmask pI453) (cmask pI453) (hmask pI453) 1 452 (true, (init pI453), (init pI453))) ∧ intTest pI453 (runFrom pI453 (fmask pI453) (cmask pI453) (hmask pI453) 1 452 (true, (init pI453), (init pI453))) 453 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I453_fin) true) (by decide) rfl I453_fin intTest_fst
theorem link453 : linkOK pL453 pH453 pI453 = true := by decide +kernel
theorem cvx453 : ConvexBetweenHumps 453 :=
  cvx_of L453_ok H453_ok I453_ok link453 (by decide)

/-! ### `N = 454` -/

def pL454 : Prm := ⟨68, 32, 33, 456, 11, 18446744073709551616, 319639224933125948, 319639224933125948⟩
def pH454 : Prm := ⟨69, 33, 33, 456, 11, 18446744073709551616, 319648021026148156, 319648021026148156⟩
def pI454 : Prm := ⟨59, 29, 27, 456, 11, 18446744073709551616, 319639224933125948, 319648021026148156⟩
theorem L454_fin : (prmOK pL454 454 && ptTest pL454 (runFrom pL454 (fmask pL454) (cmask pL454) (hmask pL454) 1 453 (true, (init pL454), (init pL454))) 454 227 false) = true := by
  decide +kernel
theorem L454_ok : RunOK pL454 454 (runFrom pL454 (fmask pL454) (cmask pL454) (hmask pL454) 1 453 (true, (init pL454), (init pL454))) ∧ ptTest pL454 (runFrom pL454 (fmask pL454) (cmask pL454) (hmask pL454) 1 453 (true, (init pL454), (init pL454))) 454 227 false = true :=
  fin_run (runOK_init (prmOK_of_and L454_fin) true) (by decide) rfl L454_fin ptTest_fst
theorem H454_fin : (prmOK pH454 454 && ptTest pH454 (runFrom pH454 (fmask pH454) (cmask pH454) (hmask pH454) 1 453 (true, (init pH454), (init pH454))) 454 227 true) = true := by
  decide +kernel
theorem H454_ok : RunOK pH454 454 (runFrom pH454 (fmask pH454) (cmask pH454) (hmask pH454) 1 453 (true, (init pH454), (init pH454))) ∧ ptTest pH454 (runFrom pH454 (fmask pH454) (cmask pH454) (hmask pH454) 1 453 (true, (init pH454), (init pH454))) 454 227 true = true :=
  fin_run (runOK_init (prmOK_of_and H454_fin) true) (by decide) rfl H454_fin ptTest_fst
theorem I454_fin : (prmOK pI454 454 && intTest pI454 (runFrom pI454 (fmask pI454) (cmask pI454) (hmask pI454) 1 453 (true, (init pI454), (init pI454))) 454 14 true) = true := by
  decide +kernel
theorem I454_ok : RunOK pI454 454 (runFrom pI454 (fmask pI454) (cmask pI454) (hmask pI454) 1 453 (true, (init pI454), (init pI454))) ∧ intTest pI454 (runFrom pI454 (fmask pI454) (cmask pI454) (hmask pI454) 1 453 (true, (init pI454), (init pI454))) 454 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I454_fin) true) (by decide) rfl I454_fin intTest_fst
theorem link454 : linkOK pL454 pH454 pI454 = true := by decide +kernel
theorem cvx454 : ConvexBetweenHumps 454 :=
  cvx_of L454_ok H454_ok I454_ok link454 (by decide)
theorem cenlink454 : cenLinkOK pI454 454 = true := by decide +kernel
theorem cen454 : CenterUniqueMin 454 ∧ DipHyp 454 ∧ OnePointHyps 454 :=
  cen_of L454_ok H454_ok I454_ok link454 cenlink454

/-! ### `N = 455` -/

def pL455 : Prm := ⟨69, 33, 33, 457, 11, 18446744073709551616, 319103625758436263, 319103625758436263⟩
def pH455 : Prm := ⟨69, 33, 33, 457, 11, 18446744073709551616, 319112421851458471, 319112421851458471⟩
def pI455 : Prm := ⟨59, 29, 27, 457, 11, 18446744073709551616, 319103625758436263, 319112421851458471⟩
theorem L455_fin : (prmOK pL455 455 && ptTest pL455 (runFrom pL455 (fmask pL455) (cmask pL455) (hmask pL455) 1 454 (true, (init pL455), (init pL455))) 455 228 false) = true := by
  decide +kernel
theorem L455_ok : RunOK pL455 455 (runFrom pL455 (fmask pL455) (cmask pL455) (hmask pL455) 1 454 (true, (init pL455), (init pL455))) ∧ ptTest pL455 (runFrom pL455 (fmask pL455) (cmask pL455) (hmask pL455) 1 454 (true, (init pL455), (init pL455))) 455 228 false = true :=
  fin_run (runOK_init (prmOK_of_and L455_fin) true) (by decide) rfl L455_fin ptTest_fst
theorem H455_fin : (prmOK pH455 455 && ptTest pH455 (runFrom pH455 (fmask pH455) (cmask pH455) (hmask pH455) 1 454 (true, (init pH455), (init pH455))) 455 228 true) = true := by
  decide +kernel
theorem H455_ok : RunOK pH455 455 (runFrom pH455 (fmask pH455) (cmask pH455) (hmask pH455) 1 454 (true, (init pH455), (init pH455))) ∧ ptTest pH455 (runFrom pH455 (fmask pH455) (cmask pH455) (hmask pH455) 1 454 (true, (init pH455), (init pH455))) 455 228 true = true :=
  fin_run (runOK_init (prmOK_of_and H455_fin) true) (by decide) rfl H455_fin ptTest_fst
theorem I455_fin : (prmOK pI455 455 && intTest pI455 (runFrom pI455 (fmask pI455) (cmask pI455) (hmask pI455) 1 454 (true, (init pI455), (init pI455))) 455 14 false) = true := by
  decide +kernel
theorem I455_ok : RunOK pI455 455 (runFrom pI455 (fmask pI455) (cmask pI455) (hmask pI455) 1 454 (true, (init pI455), (init pI455))) ∧ intTest pI455 (runFrom pI455 (fmask pI455) (cmask pI455) (hmask pI455) 1 454 (true, (init pI455), (init pI455))) 455 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I455_fin) true) (by decide) rfl I455_fin intTest_fst
theorem link455 : linkOK pL455 pH455 pI455 = true := by decide +kernel
theorem cvx455 : ConvexBetweenHumps 455 :=
  cvx_of L455_ok H455_ok I455_ok link455 (by decide)

/-! ### `N = 456` -/

def pL456 : Prm := ⟨69, 33, 33, 458, 11, 18446744073709551616, 318571289024543842, 318571289024543842⟩
def pH456 : Prm := ⟨69, 33, 33, 458, 11, 18446744073709551616, 318580085117566050, 318580085117566050⟩
def pI456 : Prm := ⟨59, 29, 27, 458, 11, 18446744073709551616, 318571289024543842, 318580085117566050⟩
theorem L456_fin : (prmOK pL456 456 && ptTest pL456 (runFrom pL456 (fmask pL456) (cmask pL456) (hmask pL456) 1 455 (true, (init pL456), (init pL456))) 456 228 false) = true := by
  decide +kernel
theorem L456_ok : RunOK pL456 456 (runFrom pL456 (fmask pL456) (cmask pL456) (hmask pL456) 1 455 (true, (init pL456), (init pL456))) ∧ ptTest pL456 (runFrom pL456 (fmask pL456) (cmask pL456) (hmask pL456) 1 455 (true, (init pL456), (init pL456))) 456 228 false = true :=
  fin_run (runOK_init (prmOK_of_and L456_fin) true) (by decide) rfl L456_fin ptTest_fst
theorem H456_fin : (prmOK pH456 456 && ptTest pH456 (runFrom pH456 (fmask pH456) (cmask pH456) (hmask pH456) 1 455 (true, (init pH456), (init pH456))) 456 228 true) = true := by
  decide +kernel
theorem H456_ok : RunOK pH456 456 (runFrom pH456 (fmask pH456) (cmask pH456) (hmask pH456) 1 455 (true, (init pH456), (init pH456))) ∧ ptTest pH456 (runFrom pH456 (fmask pH456) (cmask pH456) (hmask pH456) 1 455 (true, (init pH456), (init pH456))) 456 228 true = true :=
  fin_run (runOK_init (prmOK_of_and H456_fin) true) (by decide) rfl H456_fin ptTest_fst
theorem I456_fin : (prmOK pI456 456 && intTest pI456 (runFrom pI456 (fmask pI456) (cmask pI456) (hmask pI456) 1 455 (true, (init pI456), (init pI456))) 456 14 true) = true := by
  decide +kernel
theorem I456_ok : RunOK pI456 456 (runFrom pI456 (fmask pI456) (cmask pI456) (hmask pI456) 1 455 (true, (init pI456), (init pI456))) ∧ intTest pI456 (runFrom pI456 (fmask pI456) (cmask pI456) (hmask pI456) 1 455 (true, (init pI456), (init pI456))) 456 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I456_fin) true) (by decide) rfl I456_fin intTest_fst
theorem link456 : linkOK pL456 pH456 pI456 = true := by decide +kernel
theorem cvx456 : ConvexBetweenHumps 456 :=
  cvx_of L456_ok H456_ok I456_ok link456 (by decide)
theorem cenlink456 : cenLinkOK pI456 456 = true := by decide +kernel
theorem cen456 : CenterUniqueMin 456 ∧ DipHyp 456 ∧ OnePointHyps 456 :=
  cen_of L456_ok H456_ok I456_ok link456 cenlink456

/-! ### `N = 457` -/

def pL457 : Prm := ⟨69, 33, 33, 459, 11, 18446744073709551616, 318039654372826977, 318039654372826977⟩
def pH457 : Prm := ⟨69, 33, 33, 459, 11, 18446744073709551616, 318048450465849185, 318048450465849185⟩
def pI457 : Prm := ⟨59, 29, 27, 459, 11, 18446744073709551616, 318039654372826977, 318048450465849185⟩
theorem L457_fin : (prmOK pL457 457 && ptTest pL457 (runFrom pL457 (fmask pL457) (cmask pL457) (hmask pL457) 1 456 (true, (init pL457), (init pL457))) 457 229 false) = true := by
  decide +kernel
theorem L457_ok : RunOK pL457 457 (runFrom pL457 (fmask pL457) (cmask pL457) (hmask pL457) 1 456 (true, (init pL457), (init pL457))) ∧ ptTest pL457 (runFrom pL457 (fmask pL457) (cmask pL457) (hmask pL457) 1 456 (true, (init pL457), (init pL457))) 457 229 false = true :=
  fin_run (runOK_init (prmOK_of_and L457_fin) true) (by decide) rfl L457_fin ptTest_fst
theorem H457_fin : (prmOK pH457 457 && ptTest pH457 (runFrom pH457 (fmask pH457) (cmask pH457) (hmask pH457) 1 456 (true, (init pH457), (init pH457))) 457 229 true) = true := by
  decide +kernel
theorem H457_ok : RunOK pH457 457 (runFrom pH457 (fmask pH457) (cmask pH457) (hmask pH457) 1 456 (true, (init pH457), (init pH457))) ∧ ptTest pH457 (runFrom pH457 (fmask pH457) (cmask pH457) (hmask pH457) 1 456 (true, (init pH457), (init pH457))) 457 229 true = true :=
  fin_run (runOK_init (prmOK_of_and H457_fin) true) (by decide) rfl H457_fin ptTest_fst
theorem I457_fin : (prmOK pI457 457 && intTest pI457 (runFrom pI457 (fmask pI457) (cmask pI457) (hmask pI457) 1 456 (true, (init pI457), (init pI457))) 457 14 false) = true := by
  decide +kernel
theorem I457_ok : RunOK pI457 457 (runFrom pI457 (fmask pI457) (cmask pI457) (hmask pI457) 1 456 (true, (init pI457), (init pI457))) ∧ intTest pI457 (runFrom pI457 (fmask pI457) (cmask pI457) (hmask pI457) 1 456 (true, (init pI457), (init pI457))) 457 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I457_fin) true) (by decide) rfl I457_fin intTest_fst
theorem link457 : linkOK pL457 pH457 pI457 = true := by decide +kernel
theorem cvx457 : ConvexBetweenHumps 457 :=
  cvx_of L457_ok H457_ok I457_ok link457 (by decide)

/-! ### `N = 458` -/

def pL458 : Prm := ⟨69, 33, 33, 460, 11, 18446744073709551616, 317511242357135633, 317511242357135633⟩
def pH458 : Prm := ⟨69, 33, 33, 460, 11, 18446744073709551616, 317520038450157841, 317520038450157841⟩
def pI458 : Prm := ⟨59, 29, 27, 460, 11, 18446744073709551616, 317511242357135633, 317520038450157841⟩
theorem L458_fin : (prmOK pL458 458 && ptTest pL458 (runFrom pL458 (fmask pL458) (cmask pL458) (hmask pL458) 1 457 (true, (init pL458), (init pL458))) 458 229 false) = true := by
  decide +kernel
theorem L458_ok : RunOK pL458 458 (runFrom pL458 (fmask pL458) (cmask pL458) (hmask pL458) 1 457 (true, (init pL458), (init pL458))) ∧ ptTest pL458 (runFrom pL458 (fmask pL458) (cmask pL458) (hmask pL458) 1 457 (true, (init pL458), (init pL458))) 458 229 false = true :=
  fin_run (runOK_init (prmOK_of_and L458_fin) true) (by decide) rfl L458_fin ptTest_fst
theorem H458_fin : (prmOK pH458 458 && ptTest pH458 (runFrom pH458 (fmask pH458) (cmask pH458) (hmask pH458) 1 457 (true, (init pH458), (init pH458))) 458 229 true) = true := by
  decide +kernel
theorem H458_ok : RunOK pH458 458 (runFrom pH458 (fmask pH458) (cmask pH458) (hmask pH458) 1 457 (true, (init pH458), (init pH458))) ∧ ptTest pH458 (runFrom pH458 (fmask pH458) (cmask pH458) (hmask pH458) 1 457 (true, (init pH458), (init pH458))) 458 229 true = true :=
  fin_run (runOK_init (prmOK_of_and H458_fin) true) (by decide) rfl H458_fin ptTest_fst
theorem I458_fin : (prmOK pI458 458 && intTest pI458 (runFrom pI458 (fmask pI458) (cmask pI458) (hmask pI458) 1 457 (true, (init pI458), (init pI458))) 458 14 true) = true := by
  decide +kernel
theorem I458_ok : RunOK pI458 458 (runFrom pI458 (fmask pI458) (cmask pI458) (hmask pI458) 1 457 (true, (init pI458), (init pI458))) ∧ intTest pI458 (runFrom pI458 (fmask pI458) (cmask pI458) (hmask pI458) 1 457 (true, (init pI458), (init pI458))) 458 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I458_fin) true) (by decide) rfl I458_fin intTest_fst
theorem link458 : linkOK pL458 pH458 pI458 = true := by decide +kernel
theorem cvx458 : ConvexBetweenHumps 458 :=
  cvx_of L458_ok H458_ok I458_ok link458 (by decide)
theorem cenlink458 : cenLinkOK pI458 458 = true := by decide +kernel
theorem cen458 : CenterUniqueMin 458 ∧ DipHyp 458 ∧ OnePointHyps 458 :=
  cen_of L458_ok H458_ok I458_ok link458 cenlink458

/-! ### `N = 459` -/

def pL459 : Prm := ⟨69, 33, 33, 461, 11, 18446744073709551616, 316983526568807742, 316983526568807742⟩
def pH459 : Prm := ⟨69, 33, 33, 461, 11, 18446744073709551616, 316992322661829950, 316992322661829950⟩
def pI459 : Prm := ⟨59, 29, 27, 461, 11, 18446744073709551616, 316983526568807742, 316992322661829950⟩
theorem L459_fin : (prmOK pL459 459 && ptTest pL459 (runFrom pL459 (fmask pL459) (cmask pL459) (hmask pL459) 1 458 (true, (init pL459), (init pL459))) 459 230 false) = true := by
  decide +kernel
theorem L459_ok : RunOK pL459 459 (runFrom pL459 (fmask pL459) (cmask pL459) (hmask pL459) 1 458 (true, (init pL459), (init pL459))) ∧ ptTest pL459 (runFrom pL459 (fmask pL459) (cmask pL459) (hmask pL459) 1 458 (true, (init pL459), (init pL459))) 459 230 false = true :=
  fin_run (runOK_init (prmOK_of_and L459_fin) true) (by decide) rfl L459_fin ptTest_fst
theorem H459_fin : (prmOK pH459 459 && ptTest pH459 (runFrom pH459 (fmask pH459) (cmask pH459) (hmask pH459) 1 458 (true, (init pH459), (init pH459))) 459 230 true) = true := by
  decide +kernel
theorem H459_ok : RunOK pH459 459 (runFrom pH459 (fmask pH459) (cmask pH459) (hmask pH459) 1 458 (true, (init pH459), (init pH459))) ∧ ptTest pH459 (runFrom pH459 (fmask pH459) (cmask pH459) (hmask pH459) 1 458 (true, (init pH459), (init pH459))) 459 230 true = true :=
  fin_run (runOK_init (prmOK_of_and H459_fin) true) (by decide) rfl H459_fin ptTest_fst
theorem I459_fin : (prmOK pI459 459 && intTest pI459 (runFrom pI459 (fmask pI459) (cmask pI459) (hmask pI459) 1 458 (true, (init pI459), (init pI459))) 459 14 false) = true := by
  decide +kernel
theorem I459_ok : RunOK pI459 459 (runFrom pI459 (fmask pI459) (cmask pI459) (hmask pI459) 1 458 (true, (init pI459), (init pI459))) ∧ intTest pI459 (runFrom pI459 (fmask pI459) (cmask pI459) (hmask pI459) 1 458 (true, (init pI459), (init pI459))) 459 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I459_fin) true) (by decide) rfl I459_fin intTest_fst
theorem link459 : linkOK pL459 pH459 pI459 = true := by decide +kernel
theorem cvx459 : ConvexBetweenHumps 459 :=
  cvx_of L459_ok H459_ok I459_ok link459 (by decide)

/-! ### `N = 460` -/

def pL460 : Prm := ⟨69, 33, 33, 462, 11, 18446744073709551616, 316458994265578471, 316458994265578471⟩
def pH460 : Prm := ⟨69, 33, 33, 462, 11, 18446744073709551616, 316467790358600679, 316467790358600679⟩
def pI460 : Prm := ⟨59, 29, 27, 462, 11, 18446744073709551616, 316458994265578471, 316467790358600679⟩
theorem L460_fin : (prmOK pL460 460 && ptTest pL460 (runFrom pL460 (fmask pL460) (cmask pL460) (hmask pL460) 1 459 (true, (init pL460), (init pL460))) 460 230 false) = true := by
  decide +kernel
theorem L460_ok : RunOK pL460 460 (runFrom pL460 (fmask pL460) (cmask pL460) (hmask pL460) 1 459 (true, (init pL460), (init pL460))) ∧ ptTest pL460 (runFrom pL460 (fmask pL460) (cmask pL460) (hmask pL460) 1 459 (true, (init pL460), (init pL460))) 460 230 false = true :=
  fin_run (runOK_init (prmOK_of_and L460_fin) true) (by decide) rfl L460_fin ptTest_fst
theorem H460_fin : (prmOK pH460 460 && ptTest pH460 (runFrom pH460 (fmask pH460) (cmask pH460) (hmask pH460) 1 459 (true, (init pH460), (init pH460))) 460 230 true) = true := by
  decide +kernel
theorem H460_ok : RunOK pH460 460 (runFrom pH460 (fmask pH460) (cmask pH460) (hmask pH460) 1 459 (true, (init pH460), (init pH460))) ∧ ptTest pH460 (runFrom pH460 (fmask pH460) (cmask pH460) (hmask pH460) 1 459 (true, (init pH460), (init pH460))) 460 230 true = true :=
  fin_run (runOK_init (prmOK_of_and H460_fin) true) (by decide) rfl H460_fin ptTest_fst
theorem I460_fin : (prmOK pI460 460 && intTest pI460 (runFrom pI460 (fmask pI460) (cmask pI460) (hmask pI460) 1 459 (true, (init pI460), (init pI460))) 460 14 true) = true := by
  decide +kernel
theorem I460_ok : RunOK pI460 460 (runFrom pI460 (fmask pI460) (cmask pI460) (hmask pI460) 1 459 (true, (init pI460), (init pI460))) ∧ intTest pI460 (runFrom pI460 (fmask pI460) (cmask pI460) (hmask pI460) 1 459 (true, (init pI460), (init pI460))) 460 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I460_fin) true) (by decide) rfl I460_fin intTest_fst
theorem link460 : linkOK pL460 pH460 pI460 = true := by decide +kernel
theorem cvx460 : ConvexBetweenHumps 460 :=
  cvx_of L460_ok H460_ok I460_ok link460 (by decide)
theorem cenlink460 : cenLinkOK pI460 460 = true := by decide +kernel
theorem cen460 : CenterUniqueMin 460 ∧ DipHyp 460 ∧ OnePointHyps 460 :=
  cen_of L460_ok H460_ok I460_ok link460 cenlink460

/-! ### `N = 461` -/

def pL461 : Prm := ⟨69, 33, 33, 463, 11, 18446744073709551616, 315935152395313640, 315935152395313640⟩
def pH461 : Prm := ⟨69, 33, 33, 463, 11, 18446744073709551616, 315943948488335848, 315943948488335848⟩
def pI461 : Prm := ⟨60, 29, 28, 463, 11, 18446744073709551616, 315935152395313640, 315943948488335848⟩
theorem L461_fin : (prmOK pL461 461 && ptTest pL461 (runFrom pL461 (fmask pL461) (cmask pL461) (hmask pL461) 1 460 (true, (init pL461), (init pL461))) 461 231 false) = true := by
  decide +kernel
theorem L461_ok : RunOK pL461 461 (runFrom pL461 (fmask pL461) (cmask pL461) (hmask pL461) 1 460 (true, (init pL461), (init pL461))) ∧ ptTest pL461 (runFrom pL461 (fmask pL461) (cmask pL461) (hmask pL461) 1 460 (true, (init pL461), (init pL461))) 461 231 false = true :=
  fin_run (runOK_init (prmOK_of_and L461_fin) true) (by decide) rfl L461_fin ptTest_fst
theorem H461_fin : (prmOK pH461 461 && ptTest pH461 (runFrom pH461 (fmask pH461) (cmask pH461) (hmask pH461) 1 460 (true, (init pH461), (init pH461))) 461 231 true) = true := by
  decide +kernel
theorem H461_ok : RunOK pH461 461 (runFrom pH461 (fmask pH461) (cmask pH461) (hmask pH461) 1 460 (true, (init pH461), (init pH461))) ∧ ptTest pH461 (runFrom pH461 (fmask pH461) (cmask pH461) (hmask pH461) 1 460 (true, (init pH461), (init pH461))) 461 231 true = true :=
  fin_run (runOK_init (prmOK_of_and H461_fin) true) (by decide) rfl H461_fin ptTest_fst
theorem I461_fin : (prmOK pI461 461 && intTest pI461 (runFrom pI461 (fmask pI461) (cmask pI461) (hmask pI461) 1 460 (true, (init pI461), (init pI461))) 461 14 false) = true := by
  decide +kernel
theorem I461_ok : RunOK pI461 461 (runFrom pI461 (fmask pI461) (cmask pI461) (hmask pI461) 1 460 (true, (init pI461), (init pI461))) ∧ intTest pI461 (runFrom pI461 (fmask pI461) (cmask pI461) (hmask pI461) 1 460 (true, (init pI461), (init pI461))) 461 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I461_fin) true) (by decide) rfl I461_fin intTest_fst
theorem link461 : linkOK pL461 pH461 pI461 = true := by decide +kernel
theorem cvx461 : ConvexBetweenHumps 461 :=
  cvx_of L461_ok H461_ok I461_ok link461 (by decide)

/-! ### `N = 462` -/

def pL462 : Prm := ⟨69, 33, 33, 464, 11, 18446744073709551616, 315414455499580803, 315414455499580803⟩
def pH462 : Prm := ⟨69, 33, 33, 464, 11, 18446744073709551616, 315423251592603011, 315423251592603011⟩
def pI462 : Prm := ⟨60, 29, 28, 464, 11, 18446744073709551616, 315414455499580803, 315423251592603011⟩
theorem L462_fin : (prmOK pL462 462 && ptTest pL462 (runFrom pL462 (fmask pL462) (cmask pL462) (hmask pL462) 1 461 (true, (init pL462), (init pL462))) 462 231 false) = true := by
  decide +kernel
theorem L462_ok : RunOK pL462 462 (runFrom pL462 (fmask pL462) (cmask pL462) (hmask pL462) 1 461 (true, (init pL462), (init pL462))) ∧ ptTest pL462 (runFrom pL462 (fmask pL462) (cmask pL462) (hmask pL462) 1 461 (true, (init pL462), (init pL462))) 462 231 false = true :=
  fin_run (runOK_init (prmOK_of_and L462_fin) true) (by decide) rfl L462_fin ptTest_fst
theorem H462_fin : (prmOK pH462 462 && ptTest pH462 (runFrom pH462 (fmask pH462) (cmask pH462) (hmask pH462) 1 461 (true, (init pH462), (init pH462))) 462 231 true) = true := by
  decide +kernel
theorem H462_ok : RunOK pH462 462 (runFrom pH462 (fmask pH462) (cmask pH462) (hmask pH462) 1 461 (true, (init pH462), (init pH462))) ∧ ptTest pH462 (runFrom pH462 (fmask pH462) (cmask pH462) (hmask pH462) 1 461 (true, (init pH462), (init pH462))) 462 231 true = true :=
  fin_run (runOK_init (prmOK_of_and H462_fin) true) (by decide) rfl H462_fin ptTest_fst
theorem I462_fin : (prmOK pI462 462 && intTest pI462 (runFrom pI462 (fmask pI462) (cmask pI462) (hmask pI462) 1 461 (true, (init pI462), (init pI462))) 462 14 true) = true := by
  decide +kernel
theorem I462_ok : RunOK pI462 462 (runFrom pI462 (fmask pI462) (cmask pI462) (hmask pI462) 1 461 (true, (init pI462), (init pI462))) ∧ intTest pI462 (runFrom pI462 (fmask pI462) (cmask pI462) (hmask pI462) 1 461 (true, (init pI462), (init pI462))) 462 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I462_fin) true) (by decide) rfl I462_fin intTest_fst
theorem link462 : linkOK pL462 pH462 pI462 = true := by decide +kernel
theorem cvx462 : ConvexBetweenHumps 462 :=
  cvx_of L462_ok H462_ok I462_ok link462 (by decide)
theorem cenlink462 : cenLinkOK pI462 462 = true := by decide +kernel
theorem cen462 : CenterUniqueMin 462 ∧ DipHyp 462 ∧ OnePointHyps 462 :=
  cen_of L462_ok H462_ok I462_ok link462 cenlink462

/-! ### `N = 463` -/

def pL463 : Prm := ⟨69, 33, 33, 465, 11, 18446744073709551616, 314894443302199288, 314894443302199288⟩
def pH463 : Prm := ⟨69, 33, 33, 465, 11, 18446744073709551616, 314903239395221496, 314903239395221496⟩
def pI463 : Prm := ⟨60, 29, 28, 465, 11, 18446744073709551616, 314894443302199288, 314903239395221496⟩
theorem L463_fin : (prmOK pL463 463 && ptTest pL463 (runFrom pL463 (fmask pL463) (cmask pL463) (hmask pL463) 1 462 (true, (init pL463), (init pL463))) 463 232 false) = true := by
  decide +kernel
theorem L463_ok : RunOK pL463 463 (runFrom pL463 (fmask pL463) (cmask pL463) (hmask pL463) 1 462 (true, (init pL463), (init pL463))) ∧ ptTest pL463 (runFrom pL463 (fmask pL463) (cmask pL463) (hmask pL463) 1 462 (true, (init pL463), (init pL463))) 463 232 false = true :=
  fin_run (runOK_init (prmOK_of_and L463_fin) true) (by decide) rfl L463_fin ptTest_fst
theorem H463_fin : (prmOK pH463 463 && ptTest pH463 (runFrom pH463 (fmask pH463) (cmask pH463) (hmask pH463) 1 462 (true, (init pH463), (init pH463))) 463 232 true) = true := by
  decide +kernel
theorem H463_ok : RunOK pH463 463 (runFrom pH463 (fmask pH463) (cmask pH463) (hmask pH463) 1 462 (true, (init pH463), (init pH463))) ∧ ptTest pH463 (runFrom pH463 (fmask pH463) (cmask pH463) (hmask pH463) 1 462 (true, (init pH463), (init pH463))) 463 232 true = true :=
  fin_run (runOK_init (prmOK_of_and H463_fin) true) (by decide) rfl H463_fin ptTest_fst
theorem I463_fin : (prmOK pI463 463 && intTest pI463 (runFrom pI463 (fmask pI463) (cmask pI463) (hmask pI463) 1 462 (true, (init pI463), (init pI463))) 463 14 false) = true := by
  decide +kernel
theorem I463_ok : RunOK pI463 463 (runFrom pI463 (fmask pI463) (cmask pI463) (hmask pI463) 1 462 (true, (init pI463), (init pI463))) ∧ intTest pI463 (runFrom pI463 (fmask pI463) (cmask pI463) (hmask pI463) 1 462 (true, (init pI463), (init pI463))) 463 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I463_fin) true) (by decide) rfl I463_fin intTest_fst
theorem link463 : linkOK pL463 pH463 pI463 = true := by decide +kernel
theorem cvx463 : ConvexBetweenHumps 463 :=
  cvx_of L463_ok H463_ok I463_ok link463 (by decide)

/-! ### `N = 464` -/

def pL464 : Prm := ⟨69, 33, 33, 466, 11, 18446744073709551616, 314377538195972439, 314377538195972439⟩
def pH464 : Prm := ⟨69, 33, 33, 466, 11, 18446744073709551616, 314386334288994647, 314386334288994647⟩
def pI464 : Prm := ⟨60, 29, 28, 466, 11, 18446744073709551616, 314377538195972439, 314386334288994647⟩
theorem L464_fin : (prmOK pL464 464 && ptTest pL464 (runFrom pL464 (fmask pL464) (cmask pL464) (hmask pL464) 1 463 (true, (init pL464), (init pL464))) 464 232 false) = true := by
  decide +kernel
theorem L464_ok : RunOK pL464 464 (runFrom pL464 (fmask pL464) (cmask pL464) (hmask pL464) 1 463 (true, (init pL464), (init pL464))) ∧ ptTest pL464 (runFrom pL464 (fmask pL464) (cmask pL464) (hmask pL464) 1 463 (true, (init pL464), (init pL464))) 464 232 false = true :=
  fin_run (runOK_init (prmOK_of_and L464_fin) true) (by decide) rfl L464_fin ptTest_fst
theorem H464_fin : (prmOK pH464 464 && ptTest pH464 (runFrom pH464 (fmask pH464) (cmask pH464) (hmask pH464) 1 463 (true, (init pH464), (init pH464))) 464 232 true) = true := by
  decide +kernel
theorem H464_ok : RunOK pH464 464 (runFrom pH464 (fmask pH464) (cmask pH464) (hmask pH464) 1 463 (true, (init pH464), (init pH464))) ∧ ptTest pH464 (runFrom pH464 (fmask pH464) (cmask pH464) (hmask pH464) 1 463 (true, (init pH464), (init pH464))) 464 232 true = true :=
  fin_run (runOK_init (prmOK_of_and H464_fin) true) (by decide) rfl H464_fin ptTest_fst
theorem I464_fin : (prmOK pI464 464 && intTest pI464 (runFrom pI464 (fmask pI464) (cmask pI464) (hmask pI464) 1 463 (true, (init pI464), (init pI464))) 464 14 true) = true := by
  decide +kernel
theorem I464_ok : RunOK pI464 464 (runFrom pI464 (fmask pI464) (cmask pI464) (hmask pI464) 1 463 (true, (init pI464), (init pI464))) ∧ intTest pI464 (runFrom pI464 (fmask pI464) (cmask pI464) (hmask pI464) 1 463 (true, (init pI464), (init pI464))) 464 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I464_fin) true) (by decide) rfl I464_fin intTest_fst
theorem link464 : linkOK pL464 pH464 pI464 = true := by decide +kernel
theorem cvx464 : ConvexBetweenHumps 464 :=
  cvx_of L464_ok H464_ok I464_ok link464 (by decide)
theorem cenlink464 : cenLinkOK pI464 464 = true := by decide +kernel
theorem cen464 : CenterUniqueMin 464 ∧ DipHyp 464 ∧ OnePointHyps 464 :=
  cen_of L464_ok H464_ok I464_ok link464 cenlink464

/-! ### `N = 465` -/

def pL465 : Prm := ⟨69, 33, 33, 467, 11, 18446744073709551616, 313861312112642502, 313861312112642502⟩
def pH465 : Prm := ⟨69, 33, 33, 467, 11, 18446744073709551616, 313870108205664710, 313870108205664710⟩
def pI465 : Prm := ⟨60, 29, 28, 467, 11, 18446744073709551616, 313861312112642502, 313870108205664710⟩
theorem L465_fin : (prmOK pL465 465 && ptTest pL465 (runFrom pL465 (fmask pL465) (cmask pL465) (hmask pL465) 1 464 (true, (init pL465), (init pL465))) 465 233 false) = true := by
  decide +kernel
theorem L465_ok : RunOK pL465 465 (runFrom pL465 (fmask pL465) (cmask pL465) (hmask pL465) 1 464 (true, (init pL465), (init pL465))) ∧ ptTest pL465 (runFrom pL465 (fmask pL465) (cmask pL465) (hmask pL465) 1 464 (true, (init pL465), (init pL465))) 465 233 false = true :=
  fin_run (runOK_init (prmOK_of_and L465_fin) true) (by decide) rfl L465_fin ptTest_fst
theorem H465_fin : (prmOK pH465 465 && ptTest pH465 (runFrom pH465 (fmask pH465) (cmask pH465) (hmask pH465) 1 464 (true, (init pH465), (init pH465))) 465 233 true) = true := by
  decide +kernel
theorem H465_ok : RunOK pH465 465 (runFrom pH465 (fmask pH465) (cmask pH465) (hmask pH465) 1 464 (true, (init pH465), (init pH465))) ∧ ptTest pH465 (runFrom pH465 (fmask pH465) (cmask pH465) (hmask pH465) 1 464 (true, (init pH465), (init pH465))) 465 233 true = true :=
  fin_run (runOK_init (prmOK_of_and H465_fin) true) (by decide) rfl H465_fin ptTest_fst
theorem I465_fin : (prmOK pI465 465 && intTest pI465 (runFrom pI465 (fmask pI465) (cmask pI465) (hmask pI465) 1 464 (true, (init pI465), (init pI465))) 465 14 false) = true := by
  decide +kernel
theorem I465_ok : RunOK pI465 465 (runFrom pI465 (fmask pI465) (cmask pI465) (hmask pI465) 1 464 (true, (init pI465), (init pI465))) ∧ intTest pI465 (runFrom pI465 (fmask pI465) (cmask pI465) (hmask pI465) 1 464 (true, (init pI465), (init pI465))) 465 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I465_fin) true) (by decide) rfl I465_fin intTest_fst
theorem link465 : linkOK pL465 pH465 pI465 = true := by decide +kernel
theorem cvx465 : ConvexBetweenHumps 465 :=
  cvx_of L465_ok H465_ok I465_ok link465 (by decide)

/-! ### `N = 466` -/

def pL466 : Prm := ⟨69, 33, 33, 468, 11, 18446744073709551616, 313348155851458716, 313348155851458716⟩
def pH466 : Prm := ⟨69, 33, 33, 468, 11, 18446744073709551616, 313356951944480924, 313356951944480924⟩
def pI466 : Prm := ⟨60, 29, 28, 468, 11, 18446744073709551616, 313348155851458716, 313356951944480924⟩
theorem L466_fin : (prmOK pL466 466 && ptTest pL466 (runFrom pL466 (fmask pL466) (cmask pL466) (hmask pL466) 1 465 (true, (init pL466), (init pL466))) 466 233 false) = true := by
  decide +kernel
theorem L466_ok : RunOK pL466 466 (runFrom pL466 (fmask pL466) (cmask pL466) (hmask pL466) 1 465 (true, (init pL466), (init pL466))) ∧ ptTest pL466 (runFrom pL466 (fmask pL466) (cmask pL466) (hmask pL466) 1 465 (true, (init pL466), (init pL466))) 466 233 false = true :=
  fin_run (runOK_init (prmOK_of_and L466_fin) true) (by decide) rfl L466_fin ptTest_fst
theorem H466_fin : (prmOK pH466 466 && ptTest pH466 (runFrom pH466 (fmask pH466) (cmask pH466) (hmask pH466) 1 465 (true, (init pH466), (init pH466))) 466 233 true) = true := by
  decide +kernel
theorem H466_ok : RunOK pH466 466 (runFrom pH466 (fmask pH466) (cmask pH466) (hmask pH466) 1 465 (true, (init pH466), (init pH466))) ∧ ptTest pH466 (runFrom pH466 (fmask pH466) (cmask pH466) (hmask pH466) 1 465 (true, (init pH466), (init pH466))) 466 233 true = true :=
  fin_run (runOK_init (prmOK_of_and H466_fin) true) (by decide) rfl H466_fin ptTest_fst
theorem I466_fin : (prmOK pI466 466 && intTest pI466 (runFrom pI466 (fmask pI466) (cmask pI466) (hmask pI466) 1 465 (true, (init pI466), (init pI466))) 466 14 true) = true := by
  decide +kernel
theorem I466_ok : RunOK pI466 466 (runFrom pI466 (fmask pI466) (cmask pI466) (hmask pI466) 1 465 (true, (init pI466), (init pI466))) ∧ intTest pI466 (runFrom pI466 (fmask pI466) (cmask pI466) (hmask pI466) 1 465 (true, (init pI466), (init pI466))) 466 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I466_fin) true) (by decide) rfl I466_fin intTest_fst
theorem link466 : linkOK pL466 pH466 pI466 = true := by decide +kernel
theorem cvx466 : ConvexBetweenHumps 466 :=
  cvx_of L466_ok H466_ok I466_ok link466 (by decide)
theorem cenlink466 : cenLinkOK pI466 466 = true := by decide +kernel
theorem cen466 : CenterUniqueMin 466 ∧ DipHyp 466 ∧ OnePointHyps 466 :=
  cen_of L466_ok H466_ok I466_ok link466 cenlink466

/-! ### `N = 467` -/

def pL467 : Prm := ⟨69, 33, 33, 469, 11, 18446744073709551616, 312835672996230506, 312835672996230506⟩
def pH467 : Prm := ⟨69, 33, 33, 469, 11, 18446744073709551616, 312844469089252714, 312844469089252714⟩
def pI467 : Prm := ⟨60, 29, 28, 469, 11, 18446744073709551616, 312835672996230506, 312844469089252714⟩
theorem L467_fin : (prmOK pL467 467 && ptTest pL467 (runFrom pL467 (fmask pL467) (cmask pL467) (hmask pL467) 1 466 (true, (init pL467), (init pL467))) 467 234 false) = true := by
  decide +kernel
theorem L467_ok : RunOK pL467 467 (runFrom pL467 (fmask pL467) (cmask pL467) (hmask pL467) 1 466 (true, (init pL467), (init pL467))) ∧ ptTest pL467 (runFrom pL467 (fmask pL467) (cmask pL467) (hmask pL467) 1 466 (true, (init pL467), (init pL467))) 467 234 false = true :=
  fin_run (runOK_init (prmOK_of_and L467_fin) true) (by decide) rfl L467_fin ptTest_fst
theorem H467_fin : (prmOK pH467 467 && ptTest pH467 (runFrom pH467 (fmask pH467) (cmask pH467) (hmask pH467) 1 466 (true, (init pH467), (init pH467))) 467 234 true) = true := by
  decide +kernel
theorem H467_ok : RunOK pH467 467 (runFrom pH467 (fmask pH467) (cmask pH467) (hmask pH467) 1 466 (true, (init pH467), (init pH467))) ∧ ptTest pH467 (runFrom pH467 (fmask pH467) (cmask pH467) (hmask pH467) 1 466 (true, (init pH467), (init pH467))) 467 234 true = true :=
  fin_run (runOK_init (prmOK_of_and H467_fin) true) (by decide) rfl H467_fin ptTest_fst
theorem I467_fin : (prmOK pI467 467 && intTest pI467 (runFrom pI467 (fmask pI467) (cmask pI467) (hmask pI467) 1 466 (true, (init pI467), (init pI467))) 467 14 false) = true := by
  decide +kernel
theorem I467_ok : RunOK pI467 467 (runFrom pI467 (fmask pI467) (cmask pI467) (hmask pI467) 1 466 (true, (init pI467), (init pI467))) ∧ intTest pI467 (runFrom pI467 (fmask pI467) (cmask pI467) (hmask pI467) 1 466 (true, (init pI467), (init pI467))) 467 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I467_fin) true) (by decide) rfl I467_fin intTest_fst
theorem link467 : linkOK pL467 pH467 pI467 = true := by decide +kernel
theorem cvx467 : ConvexBetweenHumps 467 :=
  cvx_of L467_ok H467_ok I467_ok link467 (by decide)

/-! ### `N = 468` -/

def pL468 : Prm := ⟨69, 33, 33, 470, 11, 18446744073709551616, 312326223296038741, 312326223296038741⟩
def pH468 : Prm := ⟨69, 33, 33, 470, 11, 18446744073709551616, 312335019389060949, 312335019389060949⟩
def pI468 : Prm := ⟨60, 29, 28, 470, 11, 18446744073709551616, 312326223296038741, 312335019389060949⟩
theorem L468_fin : (prmOK pL468 468 && ptTest pL468 (runFrom pL468 (fmask pL468) (cmask pL468) (hmask pL468) 1 467 (true, (init pL468), (init pL468))) 468 234 false) = true := by
  decide +kernel
theorem L468_ok : RunOK pL468 468 (runFrom pL468 (fmask pL468) (cmask pL468) (hmask pL468) 1 467 (true, (init pL468), (init pL468))) ∧ ptTest pL468 (runFrom pL468 (fmask pL468) (cmask pL468) (hmask pL468) 1 467 (true, (init pL468), (init pL468))) 468 234 false = true :=
  fin_run (runOK_init (prmOK_of_and L468_fin) true) (by decide) rfl L468_fin ptTest_fst
theorem H468_fin : (prmOK pH468 468 && ptTest pH468 (runFrom pH468 (fmask pH468) (cmask pH468) (hmask pH468) 1 467 (true, (init pH468), (init pH468))) 468 234 true) = true := by
  decide +kernel
theorem H468_ok : RunOK pH468 468 (runFrom pH468 (fmask pH468) (cmask pH468) (hmask pH468) 1 467 (true, (init pH468), (init pH468))) ∧ ptTest pH468 (runFrom pH468 (fmask pH468) (cmask pH468) (hmask pH468) 1 467 (true, (init pH468), (init pH468))) 468 234 true = true :=
  fin_run (runOK_init (prmOK_of_and H468_fin) true) (by decide) rfl H468_fin ptTest_fst
theorem I468_fin : (prmOK pI468 468 && intTest pI468 (runFrom pI468 (fmask pI468) (cmask pI468) (hmask pI468) 1 467 (true, (init pI468), (init pI468))) 468 14 true) = true := by
  decide +kernel
theorem I468_ok : RunOK pI468 468 (runFrom pI468 (fmask pI468) (cmask pI468) (hmask pI468) 1 467 (true, (init pI468), (init pI468))) ∧ intTest pI468 (runFrom pI468 (fmask pI468) (cmask pI468) (hmask pI468) 1 467 (true, (init pI468), (init pI468))) 468 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I468_fin) true) (by decide) rfl I468_fin intTest_fst
theorem link468 : linkOK pL468 pH468 pI468 = true := by decide +kernel
theorem cvx468 : ConvexBetweenHumps 468 :=
  cvx_of L468_ok H468_ok I468_ok link468 (by decide)
theorem cenlink468 : cenLinkOK pI468 468 = true := by decide +kernel
theorem cen468 : CenterUniqueMin 468 ∧ DipHyp 468 ∧ OnePointHyps 468 :=
  cen_of L468_ok H468_ok I468_ok link468 cenlink468

/-! ### `N = 469` -/

def pL469 : Prm := ⟨69, 33, 33, 471, 11, 18446744073709551616, 311817441442747099, 311817441442747099⟩
def pH469 : Prm := ⟨69, 33, 33, 471, 11, 18446744073709551616, 311826237535769307, 311826237535769307⟩
def pI469 : Prm := ⟨60, 29, 28, 471, 11, 18446744073709551616, 311817441442747099, 311826237535769307⟩
theorem L469_fin : (prmOK pL469 469 && ptTest pL469 (runFrom pL469 (fmask pL469) (cmask pL469) (hmask pL469) 1 468 (true, (init pL469), (init pL469))) 469 235 false) = true := by
  decide +kernel
theorem L469_ok : RunOK pL469 469 (runFrom pL469 (fmask pL469) (cmask pL469) (hmask pL469) 1 468 (true, (init pL469), (init pL469))) ∧ ptTest pL469 (runFrom pL469 (fmask pL469) (cmask pL469) (hmask pL469) 1 468 (true, (init pL469), (init pL469))) 469 235 false = true :=
  fin_run (runOK_init (prmOK_of_and L469_fin) true) (by decide) rfl L469_fin ptTest_fst
theorem H469_fin : (prmOK pH469 469 && ptTest pH469 (runFrom pH469 (fmask pH469) (cmask pH469) (hmask pH469) 1 468 (true, (init pH469), (init pH469))) 469 235 true) = true := by
  decide +kernel
theorem H469_ok : RunOK pH469 469 (runFrom pH469 (fmask pH469) (cmask pH469) (hmask pH469) 1 468 (true, (init pH469), (init pH469))) ∧ ptTest pH469 (runFrom pH469 (fmask pH469) (cmask pH469) (hmask pH469) 1 468 (true, (init pH469), (init pH469))) 469 235 true = true :=
  fin_run (runOK_init (prmOK_of_and H469_fin) true) (by decide) rfl H469_fin ptTest_fst
theorem I469_fin : (prmOK pI469 469 && intTest pI469 (runFrom pI469 (fmask pI469) (cmask pI469) (hmask pI469) 1 468 (true, (init pI469), (init pI469))) 469 14 false) = true := by
  decide +kernel
theorem I469_ok : RunOK pI469 469 (runFrom pI469 (fmask pI469) (cmask pI469) (hmask pI469) 1 468 (true, (init pI469), (init pI469))) ∧ intTest pI469 (runFrom pI469 (fmask pI469) (cmask pI469) (hmask pI469) 1 468 (true, (init pI469), (init pI469))) 469 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I469_fin) true) (by decide) rfl I469_fin intTest_fst
theorem link469 : linkOK pL469 pH469 pI469 = true := by decide +kernel
theorem cvx469 : ConvexBetweenHumps 469 :=
  cvx_of L469_ok H469_ok I469_ok link469 (by decide)

/-! ### `N = 470` -/

def pL470 : Prm := ⟨69, 33, 33, 472, 11, 18446744073709551616, 311311656667069266, 311311656667069266⟩
def pH470 : Prm := ⟨69, 33, 33, 472, 11, 18446744073709551616, 311320452760091474, 311320452760091474⟩
def pI470 : Prm := ⟨60, 29, 28, 472, 11, 18446744073709551616, 311311656667069266, 311320452760091474⟩
theorem L470_fin : (prmOK pL470 470 && ptTest pL470 (runFrom pL470 (fmask pL470) (cmask pL470) (hmask pL470) 1 469 (true, (init pL470), (init pL470))) 470 235 false) = true := by
  decide +kernel
theorem L470_ok : RunOK pL470 470 (runFrom pL470 (fmask pL470) (cmask pL470) (hmask pL470) 1 469 (true, (init pL470), (init pL470))) ∧ ptTest pL470 (runFrom pL470 (fmask pL470) (cmask pL470) (hmask pL470) 1 469 (true, (init pL470), (init pL470))) 470 235 false = true :=
  fin_run (runOK_init (prmOK_of_and L470_fin) true) (by decide) rfl L470_fin ptTest_fst
theorem H470_fin : (prmOK pH470 470 && ptTest pH470 (runFrom pH470 (fmask pH470) (cmask pH470) (hmask pH470) 1 469 (true, (init pH470), (init pH470))) 470 235 true) = true := by
  decide +kernel
theorem H470_ok : RunOK pH470 470 (runFrom pH470 (fmask pH470) (cmask pH470) (hmask pH470) 1 469 (true, (init pH470), (init pH470))) ∧ ptTest pH470 (runFrom pH470 (fmask pH470) (cmask pH470) (hmask pH470) 1 469 (true, (init pH470), (init pH470))) 470 235 true = true :=
  fin_run (runOK_init (prmOK_of_and H470_fin) true) (by decide) rfl H470_fin ptTest_fst
theorem I470_fin : (prmOK pI470 470 && intTest pI470 (runFrom pI470 (fmask pI470) (cmask pI470) (hmask pI470) 1 469 (true, (init pI470), (init pI470))) 470 14 true) = true := by
  decide +kernel
theorem I470_ok : RunOK pI470 470 (runFrom pI470 (fmask pI470) (cmask pI470) (hmask pI470) 1 469 (true, (init pI470), (init pI470))) ∧ intTest pI470 (runFrom pI470 (fmask pI470) (cmask pI470) (hmask pI470) 1 469 (true, (init pI470), (init pI470))) 470 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I470_fin) true) (by decide) rfl I470_fin intTest_fst
theorem link470 : linkOK pL470 pH470 pI470 = true := by decide +kernel
theorem cvx470 : ConvexBetweenHumps 470 :=
  cvx_of L470_ok H470_ok I470_ok link470 (by decide)
theorem cenlink470 : cenLinkOK pI470 470 = true := by decide +kernel
theorem cen470 : CenterUniqueMin 470 ∧ DipHyp 470 ∧ OnePointHyps 470 :=
  cen_of L470_ok H470_ok I470_ok link470 cenlink470

/-! ### `N = 471` -/

def pL471 : Prm := ⟨69, 33, 33, 473, 11, 18446744073709551616, 310806534236513241, 310806534236513241⟩
def pH471 : Prm := ⟨69, 33, 33, 473, 11, 18446744073709551616, 310815330329535449, 310815330329535449⟩
def pI471 : Prm := ⟨60, 29, 28, 473, 11, 18446744073709551616, 310806534236513241, 310815330329535449⟩
theorem L471_fin : (prmOK pL471 471 && ptTest pL471 (runFrom pL471 (fmask pL471) (cmask pL471) (hmask pL471) 1 470 (true, (init pL471), (init pL471))) 471 236 false) = true := by
  decide +kernel
theorem L471_ok : RunOK pL471 471 (runFrom pL471 (fmask pL471) (cmask pL471) (hmask pL471) 1 470 (true, (init pL471), (init pL471))) ∧ ptTest pL471 (runFrom pL471 (fmask pL471) (cmask pL471) (hmask pL471) 1 470 (true, (init pL471), (init pL471))) 471 236 false = true :=
  fin_run (runOK_init (prmOK_of_and L471_fin) true) (by decide) rfl L471_fin ptTest_fst
theorem H471_fin : (prmOK pH471 471 && ptTest pH471 (runFrom pH471 (fmask pH471) (cmask pH471) (hmask pH471) 1 470 (true, (init pH471), (init pH471))) 471 236 true) = true := by
  decide +kernel
theorem H471_ok : RunOK pH471 471 (runFrom pH471 (fmask pH471) (cmask pH471) (hmask pH471) 1 470 (true, (init pH471), (init pH471))) ∧ ptTest pH471 (runFrom pH471 (fmask pH471) (cmask pH471) (hmask pH471) 1 470 (true, (init pH471), (init pH471))) 471 236 true = true :=
  fin_run (runOK_init (prmOK_of_and H471_fin) true) (by decide) rfl H471_fin ptTest_fst
theorem I471_fin : (prmOK pI471 471 && intTest pI471 (runFrom pI471 (fmask pI471) (cmask pI471) (hmask pI471) 1 470 (true, (init pI471), (init pI471))) 471 14 false) = true := by
  decide +kernel
theorem I471_ok : RunOK pI471 471 (runFrom pI471 (fmask pI471) (cmask pI471) (hmask pI471) 1 470 (true, (init pI471), (init pI471))) ∧ intTest pI471 (runFrom pI471 (fmask pI471) (cmask pI471) (hmask pI471) 1 470 (true, (init pI471), (init pI471))) 471 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I471_fin) true) (by decide) rfl I471_fin intTest_fst
theorem link471 : linkOK pL471 pH471 pI471 = true := by decide +kernel
theorem cvx471 : ConvexBetweenHumps 471 :=
  cvx_of L471_ok H471_ok I471_ok link471 (by decide)

/-! ### `N = 472` -/

def pL472 : Prm := ⟨69, 33, 33, 474, 11, 18446744073709551616, 310304373383881968, 310304373383881968⟩
def pH472 : Prm := ⟨69, 33, 33, 474, 11, 18446744073709551616, 310313169476904176, 310313169476904176⟩
def pI472 : Prm := ⟨60, 29, 28, 474, 11, 18446744073709551616, 310304373383881968, 310313169476904176⟩
theorem L472_fin : (prmOK pL472 472 && ptTest pL472 (runFrom pL472 (fmask pL472) (cmask pL472) (hmask pL472) 1 471 (true, (init pL472), (init pL472))) 472 236 false) = true := by
  decide +kernel
theorem L472_ok : RunOK pL472 472 (runFrom pL472 (fmask pL472) (cmask pL472) (hmask pL472) 1 471 (true, (init pL472), (init pL472))) ∧ ptTest pL472 (runFrom pL472 (fmask pL472) (cmask pL472) (hmask pL472) 1 471 (true, (init pL472), (init pL472))) 472 236 false = true :=
  fin_run (runOK_init (prmOK_of_and L472_fin) true) (by decide) rfl L472_fin ptTest_fst
theorem H472_fin : (prmOK pH472 472 && ptTest pH472 (runFrom pH472 (fmask pH472) (cmask pH472) (hmask pH472) 1 471 (true, (init pH472), (init pH472))) 472 236 true) = true := by
  decide +kernel
theorem H472_ok : RunOK pH472 472 (runFrom pH472 (fmask pH472) (cmask pH472) (hmask pH472) 1 471 (true, (init pH472), (init pH472))) ∧ ptTest pH472 (runFrom pH472 (fmask pH472) (cmask pH472) (hmask pH472) 1 471 (true, (init pH472), (init pH472))) 472 236 true = true :=
  fin_run (runOK_init (prmOK_of_and H472_fin) true) (by decide) rfl H472_fin ptTest_fst
theorem I472_fin : (prmOK pI472 472 && intTest pI472 (runFrom pI472 (fmask pI472) (cmask pI472) (hmask pI472) 1 471 (true, (init pI472), (init pI472))) 472 14 true) = true := by
  decide +kernel
theorem I472_ok : RunOK pI472 472 (runFrom pI472 (fmask pI472) (cmask pI472) (hmask pI472) 1 471 (true, (init pI472), (init pI472))) ∧ intTest pI472 (runFrom pI472 (fmask pI472) (cmask pI472) (hmask pI472) 1 471 (true, (init pI472), (init pI472))) 472 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I472_fin) true) (by decide) rfl I472_fin intTest_fst
theorem link472 : linkOK pL472 pH472 pI472 = true := by decide +kernel
theorem cvx472 : ConvexBetweenHumps 472 :=
  cvx_of L472_ok H472_ok I472_ok link472 (by decide)
theorem cenlink472 : cenLinkOK pI472 472 = true := by decide +kernel
theorem cen472 : CenterUniqueMin 472 ∧ DipHyp 472 ∧ OnePointHyps 472 :=
  cen_of L472_ok H472_ok I472_ok link472 cenlink472

/-! ### `N = 473` -/

def pL473 : Prm := ⟨69, 33, 33, 475, 11, 18446744073709551616, 309802869431225694, 309802869431225694⟩
def pH473 : Prm := ⟨69, 33, 33, 475, 11, 18446744073709551616, 309811665524247902, 309811665524247902⟩
def pI473 : Prm := ⟨60, 29, 28, 475, 11, 18446744073709551616, 309802869431225694, 309811665524247902⟩
theorem L473_fin : (prmOK pL473 473 && ptTest pL473 (runFrom pL473 (fmask pL473) (cmask pL473) (hmask pL473) 1 472 (true, (init pL473), (init pL473))) 473 237 false) = true := by
  decide +kernel
theorem L473_ok : RunOK pL473 473 (runFrom pL473 (fmask pL473) (cmask pL473) (hmask pL473) 1 472 (true, (init pL473), (init pL473))) ∧ ptTest pL473 (runFrom pL473 (fmask pL473) (cmask pL473) (hmask pL473) 1 472 (true, (init pL473), (init pL473))) 473 237 false = true :=
  fin_run (runOK_init (prmOK_of_and L473_fin) true) (by decide) rfl L473_fin ptTest_fst
theorem H473_fin : (prmOK pH473 473 && ptTest pH473 (runFrom pH473 (fmask pH473) (cmask pH473) (hmask pH473) 1 472 (true, (init pH473), (init pH473))) 473 237 true) = true := by
  decide +kernel
theorem H473_ok : RunOK pH473 473 (runFrom pH473 (fmask pH473) (cmask pH473) (hmask pH473) 1 472 (true, (init pH473), (init pH473))) ∧ ptTest pH473 (runFrom pH473 (fmask pH473) (cmask pH473) (hmask pH473) 1 472 (true, (init pH473), (init pH473))) 473 237 true = true :=
  fin_run (runOK_init (prmOK_of_and H473_fin) true) (by decide) rfl H473_fin ptTest_fst
theorem I473_fin : (prmOK pI473 473 && intTest pI473 (runFrom pI473 (fmask pI473) (cmask pI473) (hmask pI473) 1 472 (true, (init pI473), (init pI473))) 473 14 false) = true := by
  decide +kernel
theorem I473_ok : RunOK pI473 473 (runFrom pI473 (fmask pI473) (cmask pI473) (hmask pI473) 1 472 (true, (init pI473), (init pI473))) ∧ intTest pI473 (runFrom pI473 (fmask pI473) (cmask pI473) (hmask pI473) 1 472 (true, (init pI473), (init pI473))) 473 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I473_fin) true) (by decide) rfl I473_fin intTest_fst
theorem link473 : linkOK pL473 pH473 pI473 = true := by decide +kernel
theorem cvx473 : ConvexBetweenHumps 473 :=
  cvx_of L473_ok H473_ok I473_ok link473 (by decide)

/-! ### `N = 474` -/

def pL474 : Prm := ⟨69, 33, 33, 476, 11, 18446744073709551616, 309304292123027921, 309304292123027921⟩
def pH474 : Prm := ⟨69, 33, 33, 476, 11, 18446744073709551616, 309313088216050129, 309313088216050129⟩
def pI474 : Prm := ⟨60, 29, 28, 476, 11, 18446744073709551616, 309304292123027921, 309313088216050129⟩
theorem L474_fin : (prmOK pL474 474 && ptTest pL474 (runFrom pL474 (fmask pL474) (cmask pL474) (hmask pL474) 1 473 (true, (init pL474), (init pL474))) 474 237 false) = true := by
  decide +kernel
theorem L474_ok : RunOK pL474 474 (runFrom pL474 (fmask pL474) (cmask pL474) (hmask pL474) 1 473 (true, (init pL474), (init pL474))) ∧ ptTest pL474 (runFrom pL474 (fmask pL474) (cmask pL474) (hmask pL474) 1 473 (true, (init pL474), (init pL474))) 474 237 false = true :=
  fin_run (runOK_init (prmOK_of_and L474_fin) true) (by decide) rfl L474_fin ptTest_fst
theorem H474_fin : (prmOK pH474 474 && ptTest pH474 (runFrom pH474 (fmask pH474) (cmask pH474) (hmask pH474) 1 473 (true, (init pH474), (init pH474))) 474 237 true) = true := by
  decide +kernel
theorem H474_ok : RunOK pH474 474 (runFrom pH474 (fmask pH474) (cmask pH474) (hmask pH474) 1 473 (true, (init pH474), (init pH474))) ∧ ptTest pH474 (runFrom pH474 (fmask pH474) (cmask pH474) (hmask pH474) 1 473 (true, (init pH474), (init pH474))) 474 237 true = true :=
  fin_run (runOK_init (prmOK_of_and H474_fin) true) (by decide) rfl H474_fin ptTest_fst
theorem I474_fin : (prmOK pI474 474 && intTest pI474 (runFrom pI474 (fmask pI474) (cmask pI474) (hmask pI474) 1 473 (true, (init pI474), (init pI474))) 474 14 true) = true := by
  decide +kernel
theorem I474_ok : RunOK pI474 474 (runFrom pI474 (fmask pI474) (cmask pI474) (hmask pI474) 1 473 (true, (init pI474), (init pI474))) ∧ intTest pI474 (runFrom pI474 (fmask pI474) (cmask pI474) (hmask pI474) 1 473 (true, (init pI474), (init pI474))) 474 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I474_fin) true) (by decide) rfl I474_fin intTest_fst
theorem link474 : linkOK pL474 pH474 pI474 = true := by decide +kernel
theorem cvx474 : ConvexBetweenHumps 474 :=
  cvx_of L474_ok H474_ok I474_ok link474 (by decide)
theorem cenlink474 : cenLinkOK pI474 474 = true := by decide +kernel
theorem cen474 : CenterUniqueMin 474 ∧ DipHyp 474 ∧ OnePointHyps 474 :=
  cen_of L474_ok H474_ok I474_ok link474 cenlink474

/-! ### `N = 475` -/

def pL475 : Prm := ⟨69, 33, 33, 477, 11, 18446744073709551616, 308806366325681100, 308806366325681100⟩
def pH475 : Prm := ⟨69, 33, 33, 477, 11, 18446744073709551616, 308815162418703308, 308815162418703308⟩
def pI475 : Prm := ⟨60, 29, 28, 477, 11, 18446744073709551616, 308806366325681100, 308815162418703308⟩
theorem L475_fin : (prmOK pL475 475 && ptTest pL475 (runFrom pL475 (fmask pL475) (cmask pL475) (hmask pL475) 1 474 (true, (init pL475), (init pL475))) 475 238 false) = true := by
  decide +kernel
theorem L475_ok : RunOK pL475 475 (runFrom pL475 (fmask pL475) (cmask pL475) (hmask pL475) 1 474 (true, (init pL475), (init pL475))) ∧ ptTest pL475 (runFrom pL475 (fmask pL475) (cmask pL475) (hmask pL475) 1 474 (true, (init pL475), (init pL475))) 475 238 false = true :=
  fin_run (runOK_init (prmOK_of_and L475_fin) true) (by decide) rfl L475_fin ptTest_fst
theorem H475_fin : (prmOK pH475 475 && ptTest pH475 (runFrom pH475 (fmask pH475) (cmask pH475) (hmask pH475) 1 474 (true, (init pH475), (init pH475))) 475 238 true) = true := by
  decide +kernel
theorem H475_ok : RunOK pH475 475 (runFrom pH475 (fmask pH475) (cmask pH475) (hmask pH475) 1 474 (true, (init pH475), (init pH475))) ∧ ptTest pH475 (runFrom pH475 (fmask pH475) (cmask pH475) (hmask pH475) 1 474 (true, (init pH475), (init pH475))) 475 238 true = true :=
  fin_run (runOK_init (prmOK_of_and H475_fin) true) (by decide) rfl H475_fin ptTest_fst
theorem I475_fin : (prmOK pI475 475 && intTest pI475 (runFrom pI475 (fmask pI475) (cmask pI475) (hmask pI475) 1 474 (true, (init pI475), (init pI475))) 475 14 false) = true := by
  decide +kernel
theorem I475_ok : RunOK pI475 475 (runFrom pI475 (fmask pI475) (cmask pI475) (hmask pI475) 1 474 (true, (init pI475), (init pI475))) ∧ intTest pI475 (runFrom pI475 (fmask pI475) (cmask pI475) (hmask pI475) 1 474 (true, (init pI475), (init pI475))) 475 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I475_fin) true) (by decide) rfl I475_fin intTest_fst
theorem link475 : linkOK pL475 pH475 pI475 = true := by decide +kernel
theorem cvx475 : ConvexBetweenHumps 475 :=
  cvx_of L475_ok H475_ok I475_ok link475 (by decide)

/-! ### `N = 476` -/

def pL476 : Prm := ⟨69, 33, 33, 478, 11, 18446744073709551616, 308311332794130807, 308311332794130807⟩
def pH476 : Prm := ⟨69, 33, 33, 478, 11, 18446744073709551616, 308320128887153015, 308320128887153015⟩
def pI476 : Prm := ⟨60, 29, 28, 478, 11, 18446744073709551616, 308311332794130807, 308320128887153015⟩
theorem L476_fin : (prmOK pL476 476 && ptTest pL476 (runFrom pL476 (fmask pL476) (cmask pL476) (hmask pL476) 1 475 (true, (init pL476), (init pL476))) 476 238 false) = true := by
  decide +kernel
theorem L476_ok : RunOK pL476 476 (runFrom pL476 (fmask pL476) (cmask pL476) (hmask pL476) 1 475 (true, (init pL476), (init pL476))) ∧ ptTest pL476 (runFrom pL476 (fmask pL476) (cmask pL476) (hmask pL476) 1 475 (true, (init pL476), (init pL476))) 476 238 false = true :=
  fin_run (runOK_init (prmOK_of_and L476_fin) true) (by decide) rfl L476_fin ptTest_fst
theorem H476_fin : (prmOK pH476 476 && ptTest pH476 (runFrom pH476 (fmask pH476) (cmask pH476) (hmask pH476) 1 475 (true, (init pH476), (init pH476))) 476 238 true) = true := by
  decide +kernel
theorem H476_ok : RunOK pH476 476 (runFrom pH476 (fmask pH476) (cmask pH476) (hmask pH476) 1 475 (true, (init pH476), (init pH476))) ∧ ptTest pH476 (runFrom pH476 (fmask pH476) (cmask pH476) (hmask pH476) 1 475 (true, (init pH476), (init pH476))) 476 238 true = true :=
  fin_run (runOK_init (prmOK_of_and H476_fin) true) (by decide) rfl H476_fin ptTest_fst
theorem I476_fin : (prmOK pI476 476 && intTest pI476 (runFrom pI476 (fmask pI476) (cmask pI476) (hmask pI476) 1 475 (true, (init pI476), (init pI476))) 476 14 true) = true := by
  decide +kernel
theorem I476_ok : RunOK pI476 476 (runFrom pI476 (fmask pI476) (cmask pI476) (hmask pI476) 1 475 (true, (init pI476), (init pI476))) ∧ intTest pI476 (runFrom pI476 (fmask pI476) (cmask pI476) (hmask pI476) 1 475 (true, (init pI476), (init pI476))) 476 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I476_fin) true) (by decide) rfl I476_fin intTest_fst
theorem link476 : linkOK pL476 pH476 pI476 = true := by decide +kernel
theorem cvx476 : ConvexBetweenHumps 476 :=
  cvx_of L476_ok H476_ok I476_ok link476 (by decide)
theorem cenlink476 : cenLinkOK pI476 476 = true := by decide +kernel
theorem cen476 : CenterUniqueMin 476 ∧ DipHyp 476 ∧ OnePointHyps 476 :=
  cen_of L476_ok H476_ok I476_ok link476 cenlink476

/-! ### `N = 477` -/

def pL477 : Prm := ⟨69, 33, 33, 479, 11, 18446744073709551616, 307816945439721437, 307816945439721437⟩
def pH477 : Prm := ⟨69, 33, 33, 479, 11, 18446744073709551616, 307825741532743645, 307825741532743645⟩
def pI477 : Prm := ⟨60, 29, 28, 479, 11, 18446744073709551616, 307816945439721437, 307825741532743645⟩
theorem L477_fin : (prmOK pL477 477 && ptTest pL477 (runFrom pL477 (fmask pL477) (cmask pL477) (hmask pL477) 1 476 (true, (init pL477), (init pL477))) 477 239 false) = true := by
  decide +kernel
theorem L477_ok : RunOK pL477 477 (runFrom pL477 (fmask pL477) (cmask pL477) (hmask pL477) 1 476 (true, (init pL477), (init pL477))) ∧ ptTest pL477 (runFrom pL477 (fmask pL477) (cmask pL477) (hmask pL477) 1 476 (true, (init pL477), (init pL477))) 477 239 false = true :=
  fin_run (runOK_init (prmOK_of_and L477_fin) true) (by decide) rfl L477_fin ptTest_fst
theorem H477_fin : (prmOK pH477 477 && ptTest pH477 (runFrom pH477 (fmask pH477) (cmask pH477) (hmask pH477) 1 476 (true, (init pH477), (init pH477))) 477 239 true) = true := by
  decide +kernel
theorem H477_ok : RunOK pH477 477 (runFrom pH477 (fmask pH477) (cmask pH477) (hmask pH477) 1 476 (true, (init pH477), (init pH477))) ∧ ptTest pH477 (runFrom pH477 (fmask pH477) (cmask pH477) (hmask pH477) 1 476 (true, (init pH477), (init pH477))) 477 239 true = true :=
  fin_run (runOK_init (prmOK_of_and H477_fin) true) (by decide) rfl H477_fin ptTest_fst
theorem I477_fin : (prmOK pI477 477 && intTest pI477 (runFrom pI477 (fmask pI477) (cmask pI477) (hmask pI477) 1 476 (true, (init pI477), (init pI477))) 477 14 false) = true := by
  decide +kernel
theorem I477_ok : RunOK pI477 477 (runFrom pI477 (fmask pI477) (cmask pI477) (hmask pI477) 1 476 (true, (init pI477), (init pI477))) ∧ intTest pI477 (runFrom pI477 (fmask pI477) (cmask pI477) (hmask pI477) 1 476 (true, (init pI477), (init pI477))) 477 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I477_fin) true) (by decide) rfl I477_fin intTest_fst
theorem link477 : linkOK pL477 pH477 pI477 = true := by decide +kernel
theorem cvx477 : ConvexBetweenHumps 477 :=
  cvx_of L477_ok H477_ok I477_ok link477 (by decide)

/-! ### `N = 478` -/

def pL478 : Prm := ⟨69, 33, 33, 480, 11, 18446744073709551616, 307325416516219741, 307325416516219741⟩
def pH478 : Prm := ⟨69, 33, 33, 480, 11, 18446744073709551616, 307334212609241949, 307334212609241949⟩
def pI478 : Prm := ⟨60, 29, 28, 480, 11, 18446744073709551616, 307325416516219741, 307334212609241949⟩
theorem L478_fin : (prmOK pL478 478 && ptTest pL478 (runFrom pL478 (fmask pL478) (cmask pL478) (hmask pL478) 1 477 (true, (init pL478), (init pL478))) 478 239 false) = true := by
  decide +kernel
theorem L478_ok : RunOK pL478 478 (runFrom pL478 (fmask pL478) (cmask pL478) (hmask pL478) 1 477 (true, (init pL478), (init pL478))) ∧ ptTest pL478 (runFrom pL478 (fmask pL478) (cmask pL478) (hmask pL478) 1 477 (true, (init pL478), (init pL478))) 478 239 false = true :=
  fin_run (runOK_init (prmOK_of_and L478_fin) true) (by decide) rfl L478_fin ptTest_fst
theorem H478_fin : (prmOK pH478 478 && ptTest pH478 (runFrom pH478 (fmask pH478) (cmask pH478) (hmask pH478) 1 477 (true, (init pH478), (init pH478))) 478 239 true) = true := by
  decide +kernel
theorem H478_ok : RunOK pH478 478 (runFrom pH478 (fmask pH478) (cmask pH478) (hmask pH478) 1 477 (true, (init pH478), (init pH478))) ∧ ptTest pH478 (runFrom pH478 (fmask pH478) (cmask pH478) (hmask pH478) 1 477 (true, (init pH478), (init pH478))) 478 239 true = true :=
  fin_run (runOK_init (prmOK_of_and H478_fin) true) (by decide) rfl H478_fin ptTest_fst
theorem I478_fin : (prmOK pI478 478 && intTest pI478 (runFrom pI478 (fmask pI478) (cmask pI478) (hmask pI478) 1 477 (true, (init pI478), (init pI478))) 478 14 true) = true := by
  decide +kernel
theorem I478_ok : RunOK pI478 478 (runFrom pI478 (fmask pI478) (cmask pI478) (hmask pI478) 1 477 (true, (init pI478), (init pI478))) ∧ intTest pI478 (runFrom pI478 (fmask pI478) (cmask pI478) (hmask pI478) 1 477 (true, (init pI478), (init pI478))) 478 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I478_fin) true) (by decide) rfl I478_fin intTest_fst
theorem link478 : linkOK pL478 pH478 pI478 = true := by decide +kernel
theorem cvx478 : ConvexBetweenHumps 478 :=
  cvx_of L478_ok H478_ok I478_ok link478 (by decide)
theorem cenlink478 : cenLinkOK pI478 478 = true := by decide +kernel
theorem cen478 : CenterUniqueMin 478 ∧ DipHyp 478 ∧ OnePointHyps 478 :=
  cen_of L478_ok H478_ok I478_ok link478 cenlink478

/-! ### `N = 479` -/

def pL479 : Prm := ⟨69, 33, 33, 481, 11, 18446744073709551616, 306834528490991110, 306834528490991110⟩
def pH479 : Prm := ⟨69, 33, 33, 481, 11, 18446744073709551616, 306843324584013318, 306843324584013318⟩
def pI479 : Prm := ⟨61, 29, 29, 481, 11, 18446744073709551616, 306834528490991110, 306843324584013318⟩
theorem L479_fin : (prmOK pL479 479 && ptTest pL479 (runFrom pL479 (fmask pL479) (cmask pL479) (hmask pL479) 1 478 (true, (init pL479), (init pL479))) 479 240 false) = true := by
  decide +kernel
theorem L479_ok : RunOK pL479 479 (runFrom pL479 (fmask pL479) (cmask pL479) (hmask pL479) 1 478 (true, (init pL479), (init pL479))) ∧ ptTest pL479 (runFrom pL479 (fmask pL479) (cmask pL479) (hmask pL479) 1 478 (true, (init pL479), (init pL479))) 479 240 false = true :=
  fin_run (runOK_init (prmOK_of_and L479_fin) true) (by decide) rfl L479_fin ptTest_fst
theorem H479_fin : (prmOK pH479 479 && ptTest pH479 (runFrom pH479 (fmask pH479) (cmask pH479) (hmask pH479) 1 478 (true, (init pH479), (init pH479))) 479 240 true) = true := by
  decide +kernel
theorem H479_ok : RunOK pH479 479 (runFrom pH479 (fmask pH479) (cmask pH479) (hmask pH479) 1 478 (true, (init pH479), (init pH479))) ∧ ptTest pH479 (runFrom pH479 (fmask pH479) (cmask pH479) (hmask pH479) 1 478 (true, (init pH479), (init pH479))) 479 240 true = true :=
  fin_run (runOK_init (prmOK_of_and H479_fin) true) (by decide) rfl H479_fin ptTest_fst
theorem I479_fin : (prmOK pI479 479 && intTest pI479 (runFrom pI479 (fmask pI479) (cmask pI479) (hmask pI479) 1 478 (true, (init pI479), (init pI479))) 479 14 false) = true := by
  decide +kernel
theorem I479_ok : RunOK pI479 479 (runFrom pI479 (fmask pI479) (cmask pI479) (hmask pI479) 1 478 (true, (init pI479), (init pI479))) ∧ intTest pI479 (runFrom pI479 (fmask pI479) (cmask pI479) (hmask pI479) 1 478 (true, (init pI479), (init pI479))) 479 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I479_fin) true) (by decide) rfl I479_fin intTest_fst
theorem link479 : linkOK pL479 pH479 pI479 = true := by decide +kernel
theorem cvx479 : ConvexBetweenHumps 479 :=
  cvx_of L479_ok H479_ok I479_ok link479 (by decide)

/-! ### `N = 480` -/

def pL480 : Prm := ⟨69, 33, 33, 482, 11, 18446744073709551616, 306346465594726185, 306346465594726185⟩
def pH480 : Prm := ⟨69, 33, 33, 482, 11, 18446744073709551616, 306355261687748393, 306355261687748393⟩
def pI480 : Prm := ⟨61, 29, 29, 482, 11, 18446744073709551616, 306346465594726185, 306355261687748393⟩
theorem L480_fin : (prmOK pL480 480 && ptTest pL480 (runFrom pL480 (fmask pL480) (cmask pL480) (hmask pL480) 1 479 (true, (init pL480), (init pL480))) 480 240 false) = true := by
  decide +kernel
theorem L480_ok : RunOK pL480 480 (runFrom pL480 (fmask pL480) (cmask pL480) (hmask pL480) 1 479 (true, (init pL480), (init pL480))) ∧ ptTest pL480 (runFrom pL480 (fmask pL480) (cmask pL480) (hmask pL480) 1 479 (true, (init pL480), (init pL480))) 480 240 false = true :=
  fin_run (runOK_init (prmOK_of_and L480_fin) true) (by decide) rfl L480_fin ptTest_fst
theorem H480_fin : (prmOK pH480 480 && ptTest pH480 (runFrom pH480 (fmask pH480) (cmask pH480) (hmask pH480) 1 479 (true, (init pH480), (init pH480))) 480 240 true) = true := by
  decide +kernel
theorem H480_ok : RunOK pH480 480 (runFrom pH480 (fmask pH480) (cmask pH480) (hmask pH480) 1 479 (true, (init pH480), (init pH480))) ∧ ptTest pH480 (runFrom pH480 (fmask pH480) (cmask pH480) (hmask pH480) 1 479 (true, (init pH480), (init pH480))) 480 240 true = true :=
  fin_run (runOK_init (prmOK_of_and H480_fin) true) (by decide) rfl H480_fin ptTest_fst
theorem I480_fin : (prmOK pI480 480 && intTest pI480 (runFrom pI480 (fmask pI480) (cmask pI480) (hmask pI480) 1 479 (true, (init pI480), (init pI480))) 480 14 true) = true := by
  decide +kernel
theorem I480_ok : RunOK pI480 480 (runFrom pI480 (fmask pI480) (cmask pI480) (hmask pI480) 1 479 (true, (init pI480), (init pI480))) ∧ intTest pI480 (runFrom pI480 (fmask pI480) (cmask pI480) (hmask pI480) 1 479 (true, (init pI480), (init pI480))) 480 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I480_fin) true) (by decide) rfl I480_fin intTest_fst
theorem link480 : linkOK pL480 pH480 pI480 = true := by decide +kernel
theorem cvx480 : ConvexBetweenHumps 480 :=
  cvx_of L480_ok H480_ok I480_ok link480 (by decide)
theorem cenlink480 : cenLinkOK pI480 480 = true := by decide +kernel
theorem cen480 : CenterUniqueMin 480 ∧ DipHyp 480 ∧ OnePointHyps 480 :=
  cen_of L480_ok H480_ok I480_ok link480 cenlink480

/-! ### `N = 481` -/

def pL481 : Prm := ⟨69, 33, 33, 483, 11, 18446744073709551616, 305859038372081447, 305859038372081447⟩
def pH481 : Prm := ⟨69, 33, 33, 483, 11, 18446744073709551616, 305867834465103655, 305867834465103655⟩
def pI481 : Prm := ⟨61, 29, 29, 483, 11, 18446744073709551616, 305859038372081447, 305867834465103655⟩
theorem L481_fin : (prmOK pL481 481 && ptTest pL481 (runFrom pL481 (fmask pL481) (cmask pL481) (hmask pL481) 1 480 (true, (init pL481), (init pL481))) 481 241 false) = true := by
  decide +kernel
theorem L481_ok : RunOK pL481 481 (runFrom pL481 (fmask pL481) (cmask pL481) (hmask pL481) 1 480 (true, (init pL481), (init pL481))) ∧ ptTest pL481 (runFrom pL481 (fmask pL481) (cmask pL481) (hmask pL481) 1 480 (true, (init pL481), (init pL481))) 481 241 false = true :=
  fin_run (runOK_init (prmOK_of_and L481_fin) true) (by decide) rfl L481_fin ptTest_fst
theorem H481_fin : (prmOK pH481 481 && ptTest pH481 (runFrom pH481 (fmask pH481) (cmask pH481) (hmask pH481) 1 480 (true, (init pH481), (init pH481))) 481 241 true) = true := by
  decide +kernel
theorem H481_ok : RunOK pH481 481 (runFrom pH481 (fmask pH481) (cmask pH481) (hmask pH481) 1 480 (true, (init pH481), (init pH481))) ∧ ptTest pH481 (runFrom pH481 (fmask pH481) (cmask pH481) (hmask pH481) 1 480 (true, (init pH481), (init pH481))) 481 241 true = true :=
  fin_run (runOK_init (prmOK_of_and H481_fin) true) (by decide) rfl H481_fin ptTest_fst
theorem I481_fin : (prmOK pI481 481 && intTest pI481 (runFrom pI481 (fmask pI481) (cmask pI481) (hmask pI481) 1 480 (true, (init pI481), (init pI481))) 481 14 false) = true := by
  decide +kernel
theorem I481_ok : RunOK pI481 481 (runFrom pI481 (fmask pI481) (cmask pI481) (hmask pI481) 1 480 (true, (init pI481), (init pI481))) ∧ intTest pI481 (runFrom pI481 (fmask pI481) (cmask pI481) (hmask pI481) 1 480 (true, (init pI481), (init pI481))) 481 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I481_fin) true) (by decide) rfl I481_fin intTest_fst
theorem link481 : linkOK pL481 pH481 pI481 = true := by decide +kernel
theorem cvx481 : ConvexBetweenHumps 481 :=
  cvx_of L481_ok H481_ok I481_ok link481 (by decide)

/-! ### `N = 482` -/

def pL482 : Prm := ⟨69, 33, 33, 484, 11, 18446744073709551616, 305374403498886683, 305374403498886683⟩
def pH482 : Prm := ⟨69, 33, 33, 484, 11, 18446744073709551616, 305383199591908891, 305383199591908891⟩
def pI482 : Prm := ⟨61, 29, 29, 484, 11, 18446744073709551616, 305374403498886683, 305383199591908891⟩
theorem L482_fin : (prmOK pL482 482 && ptTest pL482 (runFrom pL482 (fmask pL482) (cmask pL482) (hmask pL482) 1 481 (true, (init pL482), (init pL482))) 482 241 false) = true := by
  decide +kernel
theorem L482_ok : RunOK pL482 482 (runFrom pL482 (fmask pL482) (cmask pL482) (hmask pL482) 1 481 (true, (init pL482), (init pL482))) ∧ ptTest pL482 (runFrom pL482 (fmask pL482) (cmask pL482) (hmask pL482) 1 481 (true, (init pL482), (init pL482))) 482 241 false = true :=
  fin_run (runOK_init (prmOK_of_and L482_fin) true) (by decide) rfl L482_fin ptTest_fst
theorem H482_fin : (prmOK pH482 482 && ptTest pH482 (runFrom pH482 (fmask pH482) (cmask pH482) (hmask pH482) 1 481 (true, (init pH482), (init pH482))) 482 241 true) = true := by
  decide +kernel
theorem H482_ok : RunOK pH482 482 (runFrom pH482 (fmask pH482) (cmask pH482) (hmask pH482) 1 481 (true, (init pH482), (init pH482))) ∧ ptTest pH482 (runFrom pH482 (fmask pH482) (cmask pH482) (hmask pH482) 1 481 (true, (init pH482), (init pH482))) 482 241 true = true :=
  fin_run (runOK_init (prmOK_of_and H482_fin) true) (by decide) rfl H482_fin ptTest_fst
theorem I482_fin : (prmOK pI482 482 && intTest pI482 (runFrom pI482 (fmask pI482) (cmask pI482) (hmask pI482) 1 481 (true, (init pI482), (init pI482))) 482 14 true) = true := by
  decide +kernel
theorem I482_ok : RunOK pI482 482 (runFrom pI482 (fmask pI482) (cmask pI482) (hmask pI482) 1 481 (true, (init pI482), (init pI482))) ∧ intTest pI482 (runFrom pI482 (fmask pI482) (cmask pI482) (hmask pI482) 1 481 (true, (init pI482), (init pI482))) 482 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I482_fin) true) (by decide) rfl I482_fin intTest_fst
theorem link482 : linkOK pL482 pH482 pI482 = true := by decide +kernel
theorem cvx482 : ConvexBetweenHumps 482 :=
  cvx_of L482_ok H482_ok I482_ok link482 (by decide)
theorem cenlink482 : cenLinkOK pI482 482 = true := by decide +kernel
theorem cen482 : CenterUniqueMin 482 ∧ DipHyp 482 ∧ OnePointHyps 482 :=
  cen_of L482_ok H482_ok I482_ok link482 cenlink482

/-! ### `N = 483` -/

def pL483 : Prm := ⟨69, 33, 33, 485, 11, 18446744073709551616, 304890399128265469, 304890399128265469⟩
def pH483 : Prm := ⟨69, 33, 33, 485, 11, 18446744073709551616, 304899195221287677, 304899195221287677⟩
def pI483 : Prm := ⟨61, 29, 29, 485, 11, 18446744073709551616, 304890399128265469, 304899195221287677⟩
theorem L483_fin : (prmOK pL483 483 && ptTest pL483 (runFrom pL483 (fmask pL483) (cmask pL483) (hmask pL483) 1 482 (true, (init pL483), (init pL483))) 483 242 false) = true := by
  decide +kernel
theorem L483_ok : RunOK pL483 483 (runFrom pL483 (fmask pL483) (cmask pL483) (hmask pL483) 1 482 (true, (init pL483), (init pL483))) ∧ ptTest pL483 (runFrom pL483 (fmask pL483) (cmask pL483) (hmask pL483) 1 482 (true, (init pL483), (init pL483))) 483 242 false = true :=
  fin_run (runOK_init (prmOK_of_and L483_fin) true) (by decide) rfl L483_fin ptTest_fst
theorem H483_fin : (prmOK pH483 483 && ptTest pH483 (runFrom pH483 (fmask pH483) (cmask pH483) (hmask pH483) 1 482 (true, (init pH483), (init pH483))) 483 242 true) = true := by
  decide +kernel
theorem H483_ok : RunOK pH483 483 (runFrom pH483 (fmask pH483) (cmask pH483) (hmask pH483) 1 482 (true, (init pH483), (init pH483))) ∧ ptTest pH483 (runFrom pH483 (fmask pH483) (cmask pH483) (hmask pH483) 1 482 (true, (init pH483), (init pH483))) 483 242 true = true :=
  fin_run (runOK_init (prmOK_of_and H483_fin) true) (by decide) rfl H483_fin ptTest_fst
theorem I483_fin : (prmOK pI483 483 && intTest pI483 (runFrom pI483 (fmask pI483) (cmask pI483) (hmask pI483) 1 482 (true, (init pI483), (init pI483))) 483 14 false) = true := by
  decide +kernel
theorem I483_ok : RunOK pI483 483 (runFrom pI483 (fmask pI483) (cmask pI483) (hmask pI483) 1 482 (true, (init pI483), (init pI483))) ∧ intTest pI483 (runFrom pI483 (fmask pI483) (cmask pI483) (hmask pI483) 1 482 (true, (init pI483), (init pI483))) 483 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I483_fin) true) (by decide) rfl I483_fin intTest_fst
theorem link483 : linkOK pL483 pH483 pI483 = true := by decide +kernel
theorem cvx483 : ConvexBetweenHumps 483 :=
  cvx_of L483_ok H483_ok I483_ok link483 (by decide)

/-! ### `N = 484` -/

def pL484 : Prm := ⟨69, 33, 33, 486, 11, 18446744073709551616, 304409154839735900, 304409154839735900⟩
def pH484 : Prm := ⟨69, 33, 33, 486, 11, 18446744073709551616, 304417950932758108, 304417950932758108⟩
def pI484 : Prm := ⟨61, 29, 29, 486, 11, 18446744073709551616, 304409154839735900, 304417950932758108⟩
theorem L484_fin : (prmOK pL484 484 && ptTest pL484 (runFrom pL484 (fmask pL484) (cmask pL484) (hmask pL484) 1 483 (true, (init pL484), (init pL484))) 484 242 false) = true := by
  decide +kernel
theorem L484_ok : RunOK pL484 484 (runFrom pL484 (fmask pL484) (cmask pL484) (hmask pL484) 1 483 (true, (init pL484), (init pL484))) ∧ ptTest pL484 (runFrom pL484 (fmask pL484) (cmask pL484) (hmask pL484) 1 483 (true, (init pL484), (init pL484))) 484 242 false = true :=
  fin_run (runOK_init (prmOK_of_and L484_fin) true) (by decide) rfl L484_fin ptTest_fst
theorem H484_fin : (prmOK pH484 484 && ptTest pH484 (runFrom pH484 (fmask pH484) (cmask pH484) (hmask pH484) 1 483 (true, (init pH484), (init pH484))) 484 242 true) = true := by
  decide +kernel
theorem H484_ok : RunOK pH484 484 (runFrom pH484 (fmask pH484) (cmask pH484) (hmask pH484) 1 483 (true, (init pH484), (init pH484))) ∧ ptTest pH484 (runFrom pH484 (fmask pH484) (cmask pH484) (hmask pH484) 1 483 (true, (init pH484), (init pH484))) 484 242 true = true :=
  fin_run (runOK_init (prmOK_of_and H484_fin) true) (by decide) rfl H484_fin ptTest_fst
theorem I484_fin : (prmOK pI484 484 && intTest pI484 (runFrom pI484 (fmask pI484) (cmask pI484) (hmask pI484) 1 483 (true, (init pI484), (init pI484))) 484 14 true) = true := by
  decide +kernel
theorem I484_ok : RunOK pI484 484 (runFrom pI484 (fmask pI484) (cmask pI484) (hmask pI484) 1 483 (true, (init pI484), (init pI484))) ∧ intTest pI484 (runFrom pI484 (fmask pI484) (cmask pI484) (hmask pI484) 1 483 (true, (init pI484), (init pI484))) 484 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I484_fin) true) (by decide) rfl I484_fin intTest_fst
theorem link484 : linkOK pL484 pH484 pI484 = true := by decide +kernel
theorem cvx484 : ConvexBetweenHumps 484 :=
  cvx_of L484_ok H484_ok I484_ok link484 (by decide)
theorem cenlink484 : cenLinkOK pI484 484 = true := by decide +kernel
theorem cen484 : CenterUniqueMin 484 ∧ DipHyp 484 ∧ OnePointHyps 484 :=
  cen_of L484_ok H484_ok I484_ok link484 cenlink484

/-! ### `N = 485` -/

def pL485 : Prm := ⟨69, 33, 33, 487, 11, 18446744073709551616, 303928535935767630, 303928535935767630⟩
def pH485 : Prm := ⟨69, 33, 33, 487, 11, 18446744073709551616, 303937332028789838, 303937332028789838⟩
def pI485 : Prm := ⟨61, 29, 29, 487, 11, 18446744073709551616, 303928535935767630, 303937332028789838⟩
theorem L485_fin : (prmOK pL485 485 && ptTest pL485 (runFrom pL485 (fmask pL485) (cmask pL485) (hmask pL485) 1 484 (true, (init pL485), (init pL485))) 485 243 false) = true := by
  decide +kernel
theorem L485_ok : RunOK pL485 485 (runFrom pL485 (fmask pL485) (cmask pL485) (hmask pL485) 1 484 (true, (init pL485), (init pL485))) ∧ ptTest pL485 (runFrom pL485 (fmask pL485) (cmask pL485) (hmask pL485) 1 484 (true, (init pL485), (init pL485))) 485 243 false = true :=
  fin_run (runOK_init (prmOK_of_and L485_fin) true) (by decide) rfl L485_fin ptTest_fst
theorem H485_fin : (prmOK pH485 485 && ptTest pH485 (runFrom pH485 (fmask pH485) (cmask pH485) (hmask pH485) 1 484 (true, (init pH485), (init pH485))) 485 243 true) = true := by
  decide +kernel
theorem H485_ok : RunOK pH485 485 (runFrom pH485 (fmask pH485) (cmask pH485) (hmask pH485) 1 484 (true, (init pH485), (init pH485))) ∧ ptTest pH485 (runFrom pH485 (fmask pH485) (cmask pH485) (hmask pH485) 1 484 (true, (init pH485), (init pH485))) 485 243 true = true :=
  fin_run (runOK_init (prmOK_of_and H485_fin) true) (by decide) rfl H485_fin ptTest_fst
theorem I485_fin : (prmOK pI485 485 && intTest pI485 (runFrom pI485 (fmask pI485) (cmask pI485) (hmask pI485) 1 484 (true, (init pI485), (init pI485))) 485 14 false) = true := by
  decide +kernel
theorem I485_ok : RunOK pI485 485 (runFrom pI485 (fmask pI485) (cmask pI485) (hmask pI485) 1 484 (true, (init pI485), (init pI485))) ∧ intTest pI485 (runFrom pI485 (fmask pI485) (cmask pI485) (hmask pI485) 1 484 (true, (init pI485), (init pI485))) 485 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I485_fin) true) (by decide) rfl I485_fin intTest_fst
theorem link485 : linkOK pL485 pH485 pI485 = true := by decide +kernel
theorem cvx485 : ConvexBetweenHumps 485 :=
  cvx_of L485_ok H485_ok I485_ok link485 (by decide)

/-! ### `N = 486` -/

def pL486 : Prm := ⟨69, 33, 33, 488, 11, 18446744073709551616, 303450645348616157, 303450645348616157⟩
def pH486 : Prm := ⟨69, 33, 33, 488, 11, 18446744073709551616, 303459441441638365, 303459441441638365⟩
def pI486 : Prm := ⟨61, 29, 29, 488, 11, 18446744073709551616, 303450645348616157, 303459441441638365⟩
theorem L486_fin : (prmOK pL486 486 && ptTest pL486 (runFrom pL486 (fmask pL486) (cmask pL486) (hmask pL486) 1 485 (true, (init pL486), (init pL486))) 486 243 false) = true := by
  decide +kernel
theorem L486_ok : RunOK pL486 486 (runFrom pL486 (fmask pL486) (cmask pL486) (hmask pL486) 1 485 (true, (init pL486), (init pL486))) ∧ ptTest pL486 (runFrom pL486 (fmask pL486) (cmask pL486) (hmask pL486) 1 485 (true, (init pL486), (init pL486))) 486 243 false = true :=
  fin_run (runOK_init (prmOK_of_and L486_fin) true) (by decide) rfl L486_fin ptTest_fst
theorem H486_fin : (prmOK pH486 486 && ptTest pH486 (runFrom pH486 (fmask pH486) (cmask pH486) (hmask pH486) 1 485 (true, (init pH486), (init pH486))) 486 243 true) = true := by
  decide +kernel
theorem H486_ok : RunOK pH486 486 (runFrom pH486 (fmask pH486) (cmask pH486) (hmask pH486) 1 485 (true, (init pH486), (init pH486))) ∧ ptTest pH486 (runFrom pH486 (fmask pH486) (cmask pH486) (hmask pH486) 1 485 (true, (init pH486), (init pH486))) 486 243 true = true :=
  fin_run (runOK_init (prmOK_of_and H486_fin) true) (by decide) rfl H486_fin ptTest_fst
theorem I486_fin : (prmOK pI486 486 && intTest pI486 (runFrom pI486 (fmask pI486) (cmask pI486) (hmask pI486) 1 485 (true, (init pI486), (init pI486))) 486 14 true) = true := by
  decide +kernel
theorem I486_ok : RunOK pI486 486 (runFrom pI486 (fmask pI486) (cmask pI486) (hmask pI486) 1 485 (true, (init pI486), (init pI486))) ∧ intTest pI486 (runFrom pI486 (fmask pI486) (cmask pI486) (hmask pI486) 1 485 (true, (init pI486), (init pI486))) 486 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I486_fin) true) (by decide) rfl I486_fin intTest_fst
theorem link486 : linkOK pL486 pH486 pI486 = true := by decide +kernel
theorem cvx486 : ConvexBetweenHumps 486 :=
  cvx_of L486_ok H486_ok I486_ok link486 (by decide)
theorem cenlink486 : cenLinkOK pI486 486 = true := by decide +kernel
theorem cen486 : CenterUniqueMin 486 ∧ DipHyp 486 ∧ OnePointHyps 486 :=
  cen_of L486_ok H486_ok I486_ok link486 cenlink486

/-! ### `N = 487` -/

def pL487 : Prm := ⟨69, 33, 33, 489, 11, 18446744073709551616, 302973375080420934, 302973375080420934⟩
def pH487 : Prm := ⟨69, 33, 33, 489, 11, 18446744073709551616, 302982171173443142, 302982171173443142⟩
def pI487 : Prm := ⟨61, 29, 29, 489, 11, 18446744073709551616, 302973375080420934, 302982171173443142⟩
theorem L487_fin : (prmOK pL487 487 && ptTest pL487 (runFrom pL487 (fmask pL487) (cmask pL487) (hmask pL487) 1 486 (true, (init pL487), (init pL487))) 487 244 false) = true := by
  decide +kernel
theorem L487_ok : RunOK pL487 487 (runFrom pL487 (fmask pL487) (cmask pL487) (hmask pL487) 1 486 (true, (init pL487), (init pL487))) ∧ ptTest pL487 (runFrom pL487 (fmask pL487) (cmask pL487) (hmask pL487) 1 486 (true, (init pL487), (init pL487))) 487 244 false = true :=
  fin_run (runOK_init (prmOK_of_and L487_fin) true) (by decide) rfl L487_fin ptTest_fst
theorem H487_fin : (prmOK pH487 487 && ptTest pH487 (runFrom pH487 (fmask pH487) (cmask pH487) (hmask pH487) 1 486 (true, (init pH487), (init pH487))) 487 244 true) = true := by
  decide +kernel
theorem H487_ok : RunOK pH487 487 (runFrom pH487 (fmask pH487) (cmask pH487) (hmask pH487) 1 486 (true, (init pH487), (init pH487))) ∧ ptTest pH487 (runFrom pH487 (fmask pH487) (cmask pH487) (hmask pH487) 1 486 (true, (init pH487), (init pH487))) 487 244 true = true :=
  fin_run (runOK_init (prmOK_of_and H487_fin) true) (by decide) rfl H487_fin ptTest_fst
theorem I487_fin : (prmOK pI487 487 && intTest pI487 (runFrom pI487 (fmask pI487) (cmask pI487) (hmask pI487) 1 486 (true, (init pI487), (init pI487))) 487 14 false) = true := by
  decide +kernel
theorem I487_ok : RunOK pI487 487 (runFrom pI487 (fmask pI487) (cmask pI487) (hmask pI487) 1 486 (true, (init pI487), (init pI487))) ∧ intTest pI487 (runFrom pI487 (fmask pI487) (cmask pI487) (hmask pI487) 1 486 (true, (init pI487), (init pI487))) 487 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I487_fin) true) (by decide) rfl I487_fin intTest_fst
theorem link487 : linkOK pL487 pH487 pI487 = true := by decide +kernel
theorem cvx487 : ConvexBetweenHumps 487 :=
  cvx_of L487_ok H487_ok I487_ok link487 (by decide)

/-! ### `N = 488` -/

def pL488 : Prm := ⟨69, 33, 33, 490, 11, 18446744073709551616, 302498801856092812, 302498801856092812⟩
def pH488 : Prm := ⟨69, 33, 33, 490, 11, 18446744073709551616, 302507597949115020, 302507597949115020⟩
def pI488 : Prm := ⟨61, 29, 29, 490, 11, 18446744073709551616, 302498801856092812, 302507597949115020⟩
theorem L488_fin : (prmOK pL488 488 && ptTest pL488 (runFrom pL488 (fmask pL488) (cmask pL488) (hmask pL488) 1 487 (true, (init pL488), (init pL488))) 488 244 false) = true := by
  decide +kernel
theorem L488_ok : RunOK pL488 488 (runFrom pL488 (fmask pL488) (cmask pL488) (hmask pL488) 1 487 (true, (init pL488), (init pL488))) ∧ ptTest pL488 (runFrom pL488 (fmask pL488) (cmask pL488) (hmask pL488) 1 487 (true, (init pL488), (init pL488))) 488 244 false = true :=
  fin_run (runOK_init (prmOK_of_and L488_fin) true) (by decide) rfl L488_fin ptTest_fst
theorem H488_fin : (prmOK pH488 488 && ptTest pH488 (runFrom pH488 (fmask pH488) (cmask pH488) (hmask pH488) 1 487 (true, (init pH488), (init pH488))) 488 244 true) = true := by
  decide +kernel
theorem H488_ok : RunOK pH488 488 (runFrom pH488 (fmask pH488) (cmask pH488) (hmask pH488) 1 487 (true, (init pH488), (init pH488))) ∧ ptTest pH488 (runFrom pH488 (fmask pH488) (cmask pH488) (hmask pH488) 1 487 (true, (init pH488), (init pH488))) 488 244 true = true :=
  fin_run (runOK_init (prmOK_of_and H488_fin) true) (by decide) rfl H488_fin ptTest_fst
theorem I488_fin : (prmOK pI488 488 && intTest pI488 (runFrom pI488 (fmask pI488) (cmask pI488) (hmask pI488) 1 487 (true, (init pI488), (init pI488))) 488 14 true) = true := by
  decide +kernel
theorem I488_ok : RunOK pI488 488 (runFrom pI488 (fmask pI488) (cmask pI488) (hmask pI488) 1 487 (true, (init pI488), (init pI488))) ∧ intTest pI488 (runFrom pI488 (fmask pI488) (cmask pI488) (hmask pI488) 1 487 (true, (init pI488), (init pI488))) 488 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I488_fin) true) (by decide) rfl I488_fin intTest_fst
theorem link488 : linkOK pL488 pH488 pI488 = true := by decide +kernel
theorem cvx488 : ConvexBetweenHumps 488 :=
  cvx_of L488_ok H488_ok I488_ok link488 (by decide)
theorem cenlink488 : cenLinkOK pI488 488 = true := by decide +kernel
theorem cen488 : CenterUniqueMin 488 ∧ DipHyp 488 ∧ OnePointHyps 488 :=
  cen_of L488_ok H488_ok I488_ok link488 cenlink488

/-! ### `N = 489` -/

def pL489 : Prm := ⟨69, 33, 33, 491, 11, 18446744073709551616, 302024843936969689, 302024843936969689⟩
def pH489 : Prm := ⟨70, 34, 33, 491, 11, 18446744073709551616, 302033640029991897, 302033640029991897⟩
def pI489 : Prm := ⟨60, 30, 27, 491, 11, 18446744073709551616, 302024843936969689, 302033640029991897⟩
theorem L489_fin : (prmOK pL489 489 && ptTest pL489 (runFrom pL489 (fmask pL489) (cmask pL489) (hmask pL489) 1 488 (true, (init pL489), (init pL489))) 489 245 false) = true := by
  decide +kernel
theorem L489_ok : RunOK pL489 489 (runFrom pL489 (fmask pL489) (cmask pL489) (hmask pL489) 1 488 (true, (init pL489), (init pL489))) ∧ ptTest pL489 (runFrom pL489 (fmask pL489) (cmask pL489) (hmask pL489) 1 488 (true, (init pL489), (init pL489))) 489 245 false = true :=
  fin_run (runOK_init (prmOK_of_and L489_fin) true) (by decide) rfl L489_fin ptTest_fst
theorem H489_fin : (prmOK pH489 489 && ptTest pH489 (runFrom pH489 (fmask pH489) (cmask pH489) (hmask pH489) 1 488 (true, (init pH489), (init pH489))) 489 245 true) = true := by
  decide +kernel
theorem H489_ok : RunOK pH489 489 (runFrom pH489 (fmask pH489) (cmask pH489) (hmask pH489) 1 488 (true, (init pH489), (init pH489))) ∧ ptTest pH489 (runFrom pH489 (fmask pH489) (cmask pH489) (hmask pH489) 1 488 (true, (init pH489), (init pH489))) 489 245 true = true :=
  fin_run (runOK_init (prmOK_of_and H489_fin) true) (by decide) rfl H489_fin ptTest_fst
theorem I489_fin : (prmOK pI489 489 && intTest pI489 (runFrom pI489 (fmask pI489) (cmask pI489) (hmask pI489) 1 488 (true, (init pI489), (init pI489))) 489 14 false) = true := by
  decide +kernel
theorem I489_ok : RunOK pI489 489 (runFrom pI489 (fmask pI489) (cmask pI489) (hmask pI489) 1 488 (true, (init pI489), (init pI489))) ∧ intTest pI489 (runFrom pI489 (fmask pI489) (cmask pI489) (hmask pI489) 1 488 (true, (init pI489), (init pI489))) 489 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I489_fin) true) (by decide) rfl I489_fin intTest_fst
theorem link489 : linkOK pL489 pH489 pI489 = true := by decide +kernel
theorem cvx489 : ConvexBetweenHumps 489 :=
  cvx_of L489_ok H489_ok I489_ok link489 (by decide)

/-! ### `N = 490` -/

def pL490 : Prm := ⟨69, 33, 33, 492, 11, 18446744073709551616, 301553552271459923, 301553552271459923⟩
def pH490 : Prm := ⟨70, 34, 33, 492, 11, 18446744073709551616, 301562348364482131, 301562348364482131⟩
def pI490 : Prm := ⟨60, 30, 27, 492, 11, 18446744073709551616, 301553552271459923, 301562348364482131⟩
theorem L490_fin : (prmOK pL490 490 && ptTest pL490 (runFrom pL490 (fmask pL490) (cmask pL490) (hmask pL490) 1 489 (true, (init pL490), (init pL490))) 490 245 false) = true := by
  decide +kernel
theorem L490_ok : RunOK pL490 490 (runFrom pL490 (fmask pL490) (cmask pL490) (hmask pL490) 1 489 (true, (init pL490), (init pL490))) ∧ ptTest pL490 (runFrom pL490 (fmask pL490) (cmask pL490) (hmask pL490) 1 489 (true, (init pL490), (init pL490))) 490 245 false = true :=
  fin_run (runOK_init (prmOK_of_and L490_fin) true) (by decide) rfl L490_fin ptTest_fst
theorem H490_fin : (prmOK pH490 490 && ptTest pH490 (runFrom pH490 (fmask pH490) (cmask pH490) (hmask pH490) 1 489 (true, (init pH490), (init pH490))) 490 245 true) = true := by
  decide +kernel
theorem H490_ok : RunOK pH490 490 (runFrom pH490 (fmask pH490) (cmask pH490) (hmask pH490) 1 489 (true, (init pH490), (init pH490))) ∧ ptTest pH490 (runFrom pH490 (fmask pH490) (cmask pH490) (hmask pH490) 1 489 (true, (init pH490), (init pH490))) 490 245 true = true :=
  fin_run (runOK_init (prmOK_of_and H490_fin) true) (by decide) rfl H490_fin ptTest_fst
theorem I490_fin : (prmOK pI490 490 && intTest pI490 (runFrom pI490 (fmask pI490) (cmask pI490) (hmask pI490) 1 489 (true, (init pI490), (init pI490))) 490 14 true) = true := by
  decide +kernel
theorem I490_ok : RunOK pI490 490 (runFrom pI490 (fmask pI490) (cmask pI490) (hmask pI490) 1 489 (true, (init pI490), (init pI490))) ∧ intTest pI490 (runFrom pI490 (fmask pI490) (cmask pI490) (hmask pI490) 1 489 (true, (init pI490), (init pI490))) 490 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I490_fin) true) (by decide) rfl I490_fin intTest_fst
theorem link490 : linkOK pL490 pH490 pI490 = true := by decide +kernel
theorem cvx490 : ConvexBetweenHumps 490 :=
  cvx_of L490_ok H490_ok I490_ok link490 (by decide)
theorem cenlink490 : cenLinkOK pI490 490 = true := by decide +kernel
theorem cen490 : CenterUniqueMin 490 ∧ DipHyp 490 ∧ OnePointHyps 490 :=
  cen_of L490_ok H490_ok I490_ok link490 cenlink490

/-! ### `N = 491` -/

def pL491 : Prm := ⟨70, 34, 33, 493, 11, 18446744073709551616, 301082870948685851, 301082870948685851⟩
def pH491 : Prm := ⟨69, 33, 33, 493, 11, 18446744073709551616, 301091667041708059, 301091667041708059⟩
def pI491 : Prm := ⟨60, 30, 27, 493, 11, 18446744073709551616, 301082870948685851, 301091667041708059⟩
theorem L491_fin : (prmOK pL491 491 && ptTest pL491 (runFrom pL491 (fmask pL491) (cmask pL491) (hmask pL491) 1 490 (true, (init pL491), (init pL491))) 491 246 false) = true := by
  decide +kernel
theorem L491_ok : RunOK pL491 491 (runFrom pL491 (fmask pL491) (cmask pL491) (hmask pL491) 1 490 (true, (init pL491), (init pL491))) ∧ ptTest pL491 (runFrom pL491 (fmask pL491) (cmask pL491) (hmask pL491) 1 490 (true, (init pL491), (init pL491))) 491 246 false = true :=
  fin_run (runOK_init (prmOK_of_and L491_fin) true) (by decide) rfl L491_fin ptTest_fst
theorem H491_fin : (prmOK pH491 491 && ptTest pH491 (runFrom pH491 (fmask pH491) (cmask pH491) (hmask pH491) 1 490 (true, (init pH491), (init pH491))) 491 246 true) = true := by
  decide +kernel
theorem H491_ok : RunOK pH491 491 (runFrom pH491 (fmask pH491) (cmask pH491) (hmask pH491) 1 490 (true, (init pH491), (init pH491))) ∧ ptTest pH491 (runFrom pH491 (fmask pH491) (cmask pH491) (hmask pH491) 1 490 (true, (init pH491), (init pH491))) 491 246 true = true :=
  fin_run (runOK_init (prmOK_of_and H491_fin) true) (by decide) rfl H491_fin ptTest_fst
theorem I491_fin : (prmOK pI491 491 && intTest pI491 (runFrom pI491 (fmask pI491) (cmask pI491) (hmask pI491) 1 490 (true, (init pI491), (init pI491))) 491 14 false) = true := by
  decide +kernel
theorem I491_ok : RunOK pI491 491 (runFrom pI491 (fmask pI491) (cmask pI491) (hmask pI491) 1 490 (true, (init pI491), (init pI491))) ∧ intTest pI491 (runFrom pI491 (fmask pI491) (cmask pI491) (hmask pI491) 1 490 (true, (init pI491), (init pI491))) 491 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I491_fin) true) (by decide) rfl I491_fin intTest_fst
theorem link491 : linkOK pL491 pH491 pI491 = true := by decide +kernel
theorem cvx491 : ConvexBetweenHumps 491 :=
  cvx_of L491_ok H491_ok I491_ok link491 (by decide)

/-! ### `N = 492` -/

def pL492 : Prm := ⟨69, 33, 33, 494, 11, 18446744073709551616, 300614825562614846, 300614825562614846⟩
def pH492 : Prm := ⟨70, 34, 33, 494, 11, 18446744073709551616, 300623621655637054, 300623621655637054⟩
def pI492 : Prm := ⟨60, 30, 27, 494, 11, 18446744073709551616, 300614825562614846, 300623621655637054⟩
theorem L492_fin : (prmOK pL492 492 && ptTest pL492 (runFrom pL492 (fmask pL492) (cmask pL492) (hmask pL492) 1 491 (true, (init pL492), (init pL492))) 492 246 false) = true := by
  decide +kernel
theorem L492_ok : RunOK pL492 492 (runFrom pL492 (fmask pL492) (cmask pL492) (hmask pL492) 1 491 (true, (init pL492), (init pL492))) ∧ ptTest pL492 (runFrom pL492 (fmask pL492) (cmask pL492) (hmask pL492) 1 491 (true, (init pL492), (init pL492))) 492 246 false = true :=
  fin_run (runOK_init (prmOK_of_and L492_fin) true) (by decide) rfl L492_fin ptTest_fst
theorem H492_fin : (prmOK pH492 492 && ptTest pH492 (runFrom pH492 (fmask pH492) (cmask pH492) (hmask pH492) 1 491 (true, (init pH492), (init pH492))) 492 246 true) = true := by
  decide +kernel
theorem H492_ok : RunOK pH492 492 (runFrom pH492 (fmask pH492) (cmask pH492) (hmask pH492) 1 491 (true, (init pH492), (init pH492))) ∧ ptTest pH492 (runFrom pH492 (fmask pH492) (cmask pH492) (hmask pH492) 1 491 (true, (init pH492), (init pH492))) 492 246 true = true :=
  fin_run (runOK_init (prmOK_of_and H492_fin) true) (by decide) rfl H492_fin ptTest_fst
theorem I492_fin : (prmOK pI492 492 && intTest pI492 (runFrom pI492 (fmask pI492) (cmask pI492) (hmask pI492) 1 491 (true, (init pI492), (init pI492))) 492 14 true) = true := by
  decide +kernel
theorem I492_ok : RunOK pI492 492 (runFrom pI492 (fmask pI492) (cmask pI492) (hmask pI492) 1 491 (true, (init pI492), (init pI492))) ∧ intTest pI492 (runFrom pI492 (fmask pI492) (cmask pI492) (hmask pI492) 1 491 (true, (init pI492), (init pI492))) 492 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I492_fin) true) (by decide) rfl I492_fin intTest_fst
theorem link492 : linkOK pL492 pH492 pI492 = true := by decide +kernel
theorem cvx492 : ConvexBetweenHumps 492 :=
  cvx_of L492_ok H492_ok I492_ok link492 (by decide)
theorem cenlink492 : cenLinkOK pI492 492 = true := by decide +kernel
theorem cen492 : CenterUniqueMin 492 ∧ DipHyp 492 ∧ OnePointHyps 492 :=
  cen_of L492_ok H492_ok I492_ok link492 cenlink492

/-! ### `N = 493` -/

def pL493 : Prm := ⟨70, 34, 33, 495, 11, 18446744073709551616, 300147385607520330, 300147385607520330⟩
def pH493 : Prm := ⟨70, 34, 33, 495, 11, 18446744073709551616, 300156181700542538, 300156181700542538⟩
def pI493 : Prm := ⟨60, 30, 27, 495, 11, 18446744073709551616, 300147385607520330, 300156181700542538⟩
theorem L493_fin : (prmOK pL493 493 && ptTest pL493 (runFrom pL493 (fmask pL493) (cmask pL493) (hmask pL493) 1 492 (true, (init pL493), (init pL493))) 493 247 false) = true := by
  decide +kernel
theorem L493_ok : RunOK pL493 493 (runFrom pL493 (fmask pL493) (cmask pL493) (hmask pL493) 1 492 (true, (init pL493), (init pL493))) ∧ ptTest pL493 (runFrom pL493 (fmask pL493) (cmask pL493) (hmask pL493) 1 492 (true, (init pL493), (init pL493))) 493 247 false = true :=
  fin_run (runOK_init (prmOK_of_and L493_fin) true) (by decide) rfl L493_fin ptTest_fst
theorem H493_fin : (prmOK pH493 493 && ptTest pH493 (runFrom pH493 (fmask pH493) (cmask pH493) (hmask pH493) 1 492 (true, (init pH493), (init pH493))) 493 247 true) = true := by
  decide +kernel
theorem H493_ok : RunOK pH493 493 (runFrom pH493 (fmask pH493) (cmask pH493) (hmask pH493) 1 492 (true, (init pH493), (init pH493))) ∧ ptTest pH493 (runFrom pH493 (fmask pH493) (cmask pH493) (hmask pH493) 1 492 (true, (init pH493), (init pH493))) 493 247 true = true :=
  fin_run (runOK_init (prmOK_of_and H493_fin) true) (by decide) rfl H493_fin ptTest_fst
theorem I493_fin : (prmOK pI493 493 && intTest pI493 (runFrom pI493 (fmask pI493) (cmask pI493) (hmask pI493) 1 492 (true, (init pI493), (init pI493))) 493 14 false) = true := by
  decide +kernel
theorem I493_ok : RunOK pI493 493 (runFrom pI493 (fmask pI493) (cmask pI493) (hmask pI493) 1 492 (true, (init pI493), (init pI493))) ∧ intTest pI493 (runFrom pI493 (fmask pI493) (cmask pI493) (hmask pI493) 1 492 (true, (init pI493), (init pI493))) 493 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I493_fin) true) (by decide) rfl I493_fin intTest_fst
theorem link493 : linkOK pL493 pH493 pI493 = true := by decide +kernel
theorem cvx493 : ConvexBetweenHumps 493 :=
  cvx_of L493_ok H493_ok I493_ok link493 (by decide)

/-! ### `N = 494` -/

def pL494 : Prm := ⟨70, 34, 33, 496, 11, 18446744073709551616, 299682551736430907, 299682551736430907⟩
def pH494 : Prm := ⟨70, 34, 33, 496, 11, 18446744073709551616, 299691347829453115, 299691347829453115⟩
def pI494 : Prm := ⟨60, 30, 27, 496, 11, 18446744073709551616, 299682551736430907, 299691347829453115⟩
theorem L494_fin : (prmOK pL494 494 && ptTest pL494 (runFrom pL494 (fmask pL494) (cmask pL494) (hmask pL494) 1 493 (true, (init pL494), (init pL494))) 494 247 false) = true := by
  decide +kernel
theorem L494_ok : RunOK pL494 494 (runFrom pL494 (fmask pL494) (cmask pL494) (hmask pL494) 1 493 (true, (init pL494), (init pL494))) ∧ ptTest pL494 (runFrom pL494 (fmask pL494) (cmask pL494) (hmask pL494) 1 493 (true, (init pL494), (init pL494))) 494 247 false = true :=
  fin_run (runOK_init (prmOK_of_and L494_fin) true) (by decide) rfl L494_fin ptTest_fst
theorem H494_fin : (prmOK pH494 494 && ptTest pH494 (runFrom pH494 (fmask pH494) (cmask pH494) (hmask pH494) 1 493 (true, (init pH494), (init pH494))) 494 247 true) = true := by
  decide +kernel
theorem H494_ok : RunOK pH494 494 (runFrom pH494 (fmask pH494) (cmask pH494) (hmask pH494) 1 493 (true, (init pH494), (init pH494))) ∧ ptTest pH494 (runFrom pH494 (fmask pH494) (cmask pH494) (hmask pH494) 1 493 (true, (init pH494), (init pH494))) 494 247 true = true :=
  fin_run (runOK_init (prmOK_of_and H494_fin) true) (by decide) rfl H494_fin ptTest_fst
theorem I494_fin : (prmOK pI494 494 && intTest pI494 (runFrom pI494 (fmask pI494) (cmask pI494) (hmask pI494) 1 493 (true, (init pI494), (init pI494))) 494 14 true) = true := by
  decide +kernel
theorem I494_ok : RunOK pI494 494 (runFrom pI494 (fmask pI494) (cmask pI494) (hmask pI494) 1 493 (true, (init pI494), (init pI494))) ∧ intTest pI494 (runFrom pI494 (fmask pI494) (cmask pI494) (hmask pI494) 1 493 (true, (init pI494), (init pI494))) 494 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I494_fin) true) (by decide) rfl I494_fin intTest_fst
theorem link494 : linkOK pL494 pH494 pI494 = true := by decide +kernel
theorem cvx494 : ConvexBetweenHumps 494 :=
  cvx_of L494_ok H494_ok I494_ok link494 (by decide)
theorem cenlink494 : cenLinkOK pI494 494 = true := by decide +kernel
theorem cen494 : CenterUniqueMin 494 ∧ DipHyp 494 ∧ OnePointHyps 494 :=
  cen_of L494_ok H494_ok I494_ok link494 cenlink494

/-! ### `N = 495` -/

def pL495 : Prm := ⟨70, 34, 33, 497, 11, 18446744073709551616, 299218318434678572, 299218318434678572⟩
def pH495 : Prm := ⟨70, 34, 33, 497, 11, 18446744073709551616, 299227114527700780, 299227114527700780⟩
def pI495 : Prm := ⟨60, 30, 27, 497, 11, 18446744073709551616, 299218318434678572, 299227114527700780⟩
theorem L495_fin : (prmOK pL495 495 && ptTest pL495 (runFrom pL495 (fmask pL495) (cmask pL495) (hmask pL495) 1 494 (true, (init pL495), (init pL495))) 495 248 false) = true := by
  decide +kernel
theorem L495_ok : RunOK pL495 495 (runFrom pL495 (fmask pL495) (cmask pL495) (hmask pL495) 1 494 (true, (init pL495), (init pL495))) ∧ ptTest pL495 (runFrom pL495 (fmask pL495) (cmask pL495) (hmask pL495) 1 494 (true, (init pL495), (init pL495))) 495 248 false = true :=
  fin_run (runOK_init (prmOK_of_and L495_fin) true) (by decide) rfl L495_fin ptTest_fst
theorem H495_fin : (prmOK pH495 495 && ptTest pH495 (runFrom pH495 (fmask pH495) (cmask pH495) (hmask pH495) 1 494 (true, (init pH495), (init pH495))) 495 248 true) = true := by
  decide +kernel
theorem H495_ok : RunOK pH495 495 (runFrom pH495 (fmask pH495) (cmask pH495) (hmask pH495) 1 494 (true, (init pH495), (init pH495))) ∧ ptTest pH495 (runFrom pH495 (fmask pH495) (cmask pH495) (hmask pH495) 1 494 (true, (init pH495), (init pH495))) 495 248 true = true :=
  fin_run (runOK_init (prmOK_of_and H495_fin) true) (by decide) rfl H495_fin ptTest_fst
theorem I495_fin : (prmOK pI495 495 && intTest pI495 (runFrom pI495 (fmask pI495) (cmask pI495) (hmask pI495) 1 494 (true, (init pI495), (init pI495))) 495 14 false) = true := by
  decide +kernel
theorem I495_ok : RunOK pI495 495 (runFrom pI495 (fmask pI495) (cmask pI495) (hmask pI495) 1 494 (true, (init pI495), (init pI495))) ∧ intTest pI495 (runFrom pI495 (fmask pI495) (cmask pI495) (hmask pI495) 1 494 (true, (init pI495), (init pI495))) 495 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I495_fin) true) (by decide) rfl I495_fin intTest_fst
theorem link495 : linkOK pL495 pH495 pI495 = true := by decide +kernel
theorem cvx495 : ConvexBetweenHumps 495 :=
  cvx_of L495_ok H495_ok I495_ok link495 (by decide)

/-! ### `N = 496` -/

def pL496 : Prm := ⟨72, 35, 34, 498, 11, 18446744073709551616, 298758860842846783, 298758860842846783⟩
def pH496 : Prm := ⟨72, 35, 34, 498, 11, 18446744073709551616, 298763258889357887, 298763258889357887⟩
def pI496 : Prm := ⟨59, 29, 27, 498, 11, 18446744073709551616, 298758860842846783, 298763258889357887⟩
theorem L496_fin : (prmOK pL496 496 && ptTest pL496 (runFrom pL496 (fmask pL496) (cmask pL496) (hmask pL496) 1 495 (true, (init pL496), (init pL496))) 496 248 false) = true := by
  decide +kernel
theorem L496_ok : RunOK pL496 496 (runFrom pL496 (fmask pL496) (cmask pL496) (hmask pL496) 1 495 (true, (init pL496), (init pL496))) ∧ ptTest pL496 (runFrom pL496 (fmask pL496) (cmask pL496) (hmask pL496) 1 495 (true, (init pL496), (init pL496))) 496 248 false = true :=
  fin_run (runOK_init (prmOK_of_and L496_fin) true) (by decide) rfl L496_fin ptTest_fst
theorem H496_fin : (prmOK pH496 496 && ptTest pH496 (runFrom pH496 (fmask pH496) (cmask pH496) (hmask pH496) 1 495 (true, (init pH496), (init pH496))) 496 248 true) = true := by
  decide +kernel
theorem H496_ok : RunOK pH496 496 (runFrom pH496 (fmask pH496) (cmask pH496) (hmask pH496) 1 495 (true, (init pH496), (init pH496))) ∧ ptTest pH496 (runFrom pH496 (fmask pH496) (cmask pH496) (hmask pH496) 1 495 (true, (init pH496), (init pH496))) 496 248 true = true :=
  fin_run (runOK_init (prmOK_of_and H496_fin) true) (by decide) rfl H496_fin ptTest_fst
theorem I496_fin : (prmOK pI496 496 && intTest pI496 (runFrom pI496 (fmask pI496) (cmask pI496) (hmask pI496) 1 495 (true, (init pI496), (init pI496))) 496 14 true) = true := by
  decide +kernel
theorem I496_ok : RunOK pI496 496 (runFrom pI496 (fmask pI496) (cmask pI496) (hmask pI496) 1 495 (true, (init pI496), (init pI496))) ∧ intTest pI496 (runFrom pI496 (fmask pI496) (cmask pI496) (hmask pI496) 1 495 (true, (init pI496), (init pI496))) 496 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I496_fin) true) (by decide) rfl I496_fin intTest_fst
theorem link496 : linkOK pL496 pH496 pI496 = true := by decide +kernel
theorem cvx496 : ConvexBetweenHumps 496 :=
  cvx_of L496_ok H496_ok I496_ok link496 (by decide)
theorem cenlink496 : cenLinkOK pI496 496 = true := by decide +kernel
theorem cen496 : CenterUniqueMin 496 ∧ DipHyp 496 ∧ OnePointHyps 496 :=
  cen_of L496_ok H496_ok I496_ok link496 cenlink496

/-! ### `N = 497` -/

def pL497 : Prm := ⟨72, 35, 34, 499, 11, 18446744073709551616, 298297799984986637, 298297799984986637⟩
def pH497 : Prm := ⟨72, 35, 34, 499, 11, 18446744073709551616, 298302198031497741, 298302198031497741⟩
def pI497 : Prm := ⟨59, 29, 27, 499, 11, 18446744073709551616, 298297799984986637, 298302198031497741⟩
theorem L497_fin : (prmOK pL497 497 && ptTest pL497 (runFrom pL497 (fmask pL497) (cmask pL497) (hmask pL497) 1 496 (true, (init pL497), (init pL497))) 497 249 false) = true := by
  decide +kernel
theorem L497_ok : RunOK pL497 497 (runFrom pL497 (fmask pL497) (cmask pL497) (hmask pL497) 1 496 (true, (init pL497), (init pL497))) ∧ ptTest pL497 (runFrom pL497 (fmask pL497) (cmask pL497) (hmask pL497) 1 496 (true, (init pL497), (init pL497))) 497 249 false = true :=
  fin_run (runOK_init (prmOK_of_and L497_fin) true) (by decide) rfl L497_fin ptTest_fst
theorem H497_fin : (prmOK pH497 497 && ptTest pH497 (runFrom pH497 (fmask pH497) (cmask pH497) (hmask pH497) 1 496 (true, (init pH497), (init pH497))) 497 249 true) = true := by
  decide +kernel
theorem H497_ok : RunOK pH497 497 (runFrom pH497 (fmask pH497) (cmask pH497) (hmask pH497) 1 496 (true, (init pH497), (init pH497))) ∧ ptTest pH497 (runFrom pH497 (fmask pH497) (cmask pH497) (hmask pH497) 1 496 (true, (init pH497), (init pH497))) 497 249 true = true :=
  fin_run (runOK_init (prmOK_of_and H497_fin) true) (by decide) rfl H497_fin ptTest_fst
theorem I497_fin : (prmOK pI497 497 && intTest pI497 (runFrom pI497 (fmask pI497) (cmask pI497) (hmask pI497) 1 496 (true, (init pI497), (init pI497))) 497 14 false) = true := by
  decide +kernel
theorem I497_ok : RunOK pI497 497 (runFrom pI497 (fmask pI497) (cmask pI497) (hmask pI497) 1 496 (true, (init pI497), (init pI497))) ∧ intTest pI497 (runFrom pI497 (fmask pI497) (cmask pI497) (hmask pI497) 1 496 (true, (init pI497), (init pI497))) 497 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I497_fin) true) (by decide) rfl I497_fin intTest_fst
theorem link497 : linkOK pL497 pH497 pI497 = true := by decide +kernel
theorem cvx497 : ConvexBetweenHumps 497 :=
  cvx_of L497_ok H497_ok I497_ok link497 (by decide)

/-! ### `N = 498` -/

def pL498 : Prm := ⟨72, 35, 34, 500, 11, 18446744073709551616, 297839286862991720, 297839286862991720⟩
def pH498 : Prm := ⟨72, 35, 34, 500, 11, 18446744073709551616, 297843684909502824, 297843684909502824⟩
def pI498 : Prm := ⟨59, 29, 27, 500, 11, 18446744073709551616, 297839286862991720, 297843684909502824⟩
theorem L498_fin : (prmOK pL498 498 && ptTest pL498 (runFrom pL498 (fmask pL498) (cmask pL498) (hmask pL498) 1 497 (true, (init pL498), (init pL498))) 498 249 false) = true := by
  decide +kernel
theorem L498_ok : RunOK pL498 498 (runFrom pL498 (fmask pL498) (cmask pL498) (hmask pL498) 1 497 (true, (init pL498), (init pL498))) ∧ ptTest pL498 (runFrom pL498 (fmask pL498) (cmask pL498) (hmask pL498) 1 497 (true, (init pL498), (init pL498))) 498 249 false = true :=
  fin_run (runOK_init (prmOK_of_and L498_fin) true) (by decide) rfl L498_fin ptTest_fst
theorem H498_fin : (prmOK pH498 498 && ptTest pH498 (runFrom pH498 (fmask pH498) (cmask pH498) (hmask pH498) 1 497 (true, (init pH498), (init pH498))) 498 249 true) = true := by
  decide +kernel
theorem H498_ok : RunOK pH498 498 (runFrom pH498 (fmask pH498) (cmask pH498) (hmask pH498) 1 497 (true, (init pH498), (init pH498))) ∧ ptTest pH498 (runFrom pH498 (fmask pH498) (cmask pH498) (hmask pH498) 1 497 (true, (init pH498), (init pH498))) 498 249 true = true :=
  fin_run (runOK_init (prmOK_of_and H498_fin) true) (by decide) rfl H498_fin ptTest_fst
theorem I498_fin : (prmOK pI498 498 && intTest pI498 (runFrom pI498 (fmask pI498) (cmask pI498) (hmask pI498) 1 497 (true, (init pI498), (init pI498))) 498 14 true) = true := by
  decide +kernel
theorem I498_ok : RunOK pI498 498 (runFrom pI498 (fmask pI498) (cmask pI498) (hmask pI498) 1 497 (true, (init pI498), (init pI498))) ∧ intTest pI498 (runFrom pI498 (fmask pI498) (cmask pI498) (hmask pI498) 1 497 (true, (init pI498), (init pI498))) 498 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I498_fin) true) (by decide) rfl I498_fin intTest_fst
theorem link498 : linkOK pL498 pH498 pI498 = true := by decide +kernel
theorem cvx498 : ConvexBetweenHumps 498 :=
  cvx_of L498_ok H498_ok I498_ok link498 (by decide)
theorem cenlink498 : cenLinkOK pI498 498 = true := by decide +kernel
theorem cen498 : CenterUniqueMin 498 ∧ DipHyp 498 ∧ OnePointHyps 498 :=
  cen_of L498_ok H498_ok I498_ok link498 cenlink498

/-! ### `N = 499` -/

def pL499 : Prm := ⟨72, 35, 34, 501, 11, 18446744073709551616, 297381364735164000, 297381364735164000⟩
def pH499 : Prm := ⟨72, 35, 34, 501, 11, 18446744073709551616, 297385762781675104, 297385762781675104⟩
def pI499 : Prm := ⟨59, 29, 27, 501, 11, 18446744073709551616, 297381364735164000, 297385762781675104⟩
theorem L499_fin : (prmOK pL499 499 && ptTest pL499 (runFrom pL499 (fmask pL499) (cmask pL499) (hmask pL499) 1 498 (true, (init pL499), (init pL499))) 499 250 false) = true := by
  decide +kernel
theorem L499_ok : RunOK pL499 499 (runFrom pL499 (fmask pL499) (cmask pL499) (hmask pL499) 1 498 (true, (init pL499), (init pL499))) ∧ ptTest pL499 (runFrom pL499 (fmask pL499) (cmask pL499) (hmask pL499) 1 498 (true, (init pL499), (init pL499))) 499 250 false = true :=
  fin_run (runOK_init (prmOK_of_and L499_fin) true) (by decide) rfl L499_fin ptTest_fst
theorem H499_fin : (prmOK pH499 499 && ptTest pH499 (runFrom pH499 (fmask pH499) (cmask pH499) (hmask pH499) 1 498 (true, (init pH499), (init pH499))) 499 250 true) = true := by
  decide +kernel
theorem H499_ok : RunOK pH499 499 (runFrom pH499 (fmask pH499) (cmask pH499) (hmask pH499) 1 498 (true, (init pH499), (init pH499))) ∧ ptTest pH499 (runFrom pH499 (fmask pH499) (cmask pH499) (hmask pH499) 1 498 (true, (init pH499), (init pH499))) 499 250 true = true :=
  fin_run (runOK_init (prmOK_of_and H499_fin) true) (by decide) rfl H499_fin ptTest_fst
theorem I499_fin : (prmOK pI499 499 && intTest pI499 (runFrom pI499 (fmask pI499) (cmask pI499) (hmask pI499) 1 498 (true, (init pI499), (init pI499))) 499 14 false) = true := by
  decide +kernel
theorem I499_ok : RunOK pI499 499 (runFrom pI499 (fmask pI499) (cmask pI499) (hmask pI499) 1 498 (true, (init pI499), (init pI499))) ∧ intTest pI499 (runFrom pI499 (fmask pI499) (cmask pI499) (hmask pI499) 1 498 (true, (init pI499), (init pI499))) 499 14 false = true :=
  fin_run (runOK_init (prmOK_of_and I499_fin) true) (by decide) rfl I499_fin intTest_fst
theorem link499 : linkOK pL499 pH499 pI499 = true := by decide +kernel
theorem cvx499 : ConvexBetweenHumps 499 :=
  cvx_of L499_ok H499_ok I499_ok link499 (by decide)

/-! ### `N = 500` -/

def pL500 : Prm := ⟨72, 35, 34, 502, 11, 18446744073709551616, 296925961830456574, 296925961830456574⟩
def pH500 : Prm := ⟨72, 35, 34, 502, 11, 18446744073709551616, 296930359876967678, 296930359876967678⟩
def pI500 : Prm := ⟨59, 29, 27, 502, 11, 18446744073709551616, 296925961830456574, 296930359876967678⟩
theorem L500_fin : (prmOK pL500 500 && ptTest pL500 (runFrom pL500 (fmask pL500) (cmask pL500) (hmask pL500) 1 499 (true, (init pL500), (init pL500))) 500 250 false) = true := by
  decide +kernel
theorem L500_ok : RunOK pL500 500 (runFrom pL500 (fmask pL500) (cmask pL500) (hmask pL500) 1 499 (true, (init pL500), (init pL500))) ∧ ptTest pL500 (runFrom pL500 (fmask pL500) (cmask pL500) (hmask pL500) 1 499 (true, (init pL500), (init pL500))) 500 250 false = true :=
  fin_run (runOK_init (prmOK_of_and L500_fin) true) (by decide) rfl L500_fin ptTest_fst
theorem H500_fin : (prmOK pH500 500 && ptTest pH500 (runFrom pH500 (fmask pH500) (cmask pH500) (hmask pH500) 1 499 (true, (init pH500), (init pH500))) 500 250 true) = true := by
  decide +kernel
theorem H500_ok : RunOK pH500 500 (runFrom pH500 (fmask pH500) (cmask pH500) (hmask pH500) 1 499 (true, (init pH500), (init pH500))) ∧ ptTest pH500 (runFrom pH500 (fmask pH500) (cmask pH500) (hmask pH500) 1 499 (true, (init pH500), (init pH500))) 500 250 true = true :=
  fin_run (runOK_init (prmOK_of_and H500_fin) true) (by decide) rfl H500_fin ptTest_fst
theorem I500_fin : (prmOK pI500 500 && intTest pI500 (runFrom pI500 (fmask pI500) (cmask pI500) (hmask pI500) 1 499 (true, (init pI500), (init pI500))) 500 14 true) = true := by
  decide +kernel
theorem I500_ok : RunOK pI500 500 (runFrom pI500 (fmask pI500) (cmask pI500) (hmask pI500) 1 499 (true, (init pI500), (init pI500))) ∧ intTest pI500 (runFrom pI500 (fmask pI500) (cmask pI500) (hmask pI500) 1 499 (true, (init pI500), (init pI500))) 500 14 true = true :=
  fin_run (runOK_init (prmOK_of_and I500_fin) true) (by decide) rfl I500_fin intTest_fst
theorem link500 : linkOK pL500 pH500 pI500 = true := by decide +kernel
theorem cvx500 : ConvexBetweenHumps 500 :=
  cvx_of L500_ok H500_ok I500_ok link500 (by decide)
theorem cenlink500 : cenLinkOK pI500 500 = true := by decide +kernel
theorem cen500 : CenterUniqueMin 500 ∧ DipHyp 500 ∧ OnePointHyps 500 :=
  cen_of L500_ok H500_ok I500_ok link500 cenlink500

/-! ### The range -/

theorem cvx_301_500 {N : ℕ} (h1 : 301 ≤ N) (h2 : N ≤ 500) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 400
  · by_cases h4 : N ≤ 350
    · by_cases h6 : N ≤ 325
      · by_cases h8 : N ≤ 312
        · by_cases h10 : N ≤ 306
          · by_cases h12 : N ≤ 303
            · by_cases h14 : N ≤ 301
              · obtain rfl : N = 301 := by omega
                exact cvx301
              · by_cases h16 : N ≤ 302
                · obtain rfl : N = 302 := by omega
                  exact cvx302
                · obtain rfl : N = 303 := by omega
                  exact cvx303
            · by_cases h14 : N ≤ 304
              · obtain rfl : N = 304 := by omega
                exact cvx304
              · by_cases h16 : N ≤ 305
                · obtain rfl : N = 305 := by omega
                  exact cvx305
                · obtain rfl : N = 306 := by omega
                  exact cvx306
          · by_cases h12 : N ≤ 309
            · by_cases h14 : N ≤ 307
              · obtain rfl : N = 307 := by omega
                exact cvx307
              · by_cases h16 : N ≤ 308
                · obtain rfl : N = 308 := by omega
                  exact cvx308
                · obtain rfl : N = 309 := by omega
                  exact cvx309
            · by_cases h14 : N ≤ 310
              · obtain rfl : N = 310 := by omega
                exact cvx310
              · by_cases h16 : N ≤ 311
                · obtain rfl : N = 311 := by omega
                  exact cvx311
                · obtain rfl : N = 312 := by omega
                  exact cvx312
        · by_cases h10 : N ≤ 318
          · by_cases h12 : N ≤ 315
            · by_cases h14 : N ≤ 313
              · obtain rfl : N = 313 := by omega
                exact cvx313
              · by_cases h16 : N ≤ 314
                · obtain rfl : N = 314 := by omega
                  exact cvx314
                · obtain rfl : N = 315 := by omega
                  exact cvx315
            · by_cases h14 : N ≤ 316
              · obtain rfl : N = 316 := by omega
                exact cvx316
              · by_cases h16 : N ≤ 317
                · obtain rfl : N = 317 := by omega
                  exact cvx317
                · obtain rfl : N = 318 := by omega
                  exact cvx318
          · by_cases h12 : N ≤ 321
            · by_cases h14 : N ≤ 319
              · obtain rfl : N = 319 := by omega
                exact cvx319
              · by_cases h16 : N ≤ 320
                · obtain rfl : N = 320 := by omega
                  exact cvx320
                · obtain rfl : N = 321 := by omega
                  exact cvx321
            · by_cases h14 : N ≤ 323
              · by_cases h16 : N ≤ 322
                · obtain rfl : N = 322 := by omega
                  exact cvx322
                · obtain rfl : N = 323 := by omega
                  exact cvx323
              · by_cases h16 : N ≤ 324
                · obtain rfl : N = 324 := by omega
                  exact cvx324
                · obtain rfl : N = 325 := by omega
                  exact cvx325
      · by_cases h8 : N ≤ 337
        · by_cases h10 : N ≤ 331
          · by_cases h12 : N ≤ 328
            · by_cases h14 : N ≤ 326
              · obtain rfl : N = 326 := by omega
                exact cvx326
              · by_cases h16 : N ≤ 327
                · obtain rfl : N = 327 := by omega
                  exact cvx327
                · obtain rfl : N = 328 := by omega
                  exact cvx328
            · by_cases h14 : N ≤ 329
              · obtain rfl : N = 329 := by omega
                exact cvx329
              · by_cases h16 : N ≤ 330
                · obtain rfl : N = 330 := by omega
                  exact cvx330
                · obtain rfl : N = 331 := by omega
                  exact cvx331
          · by_cases h12 : N ≤ 334
            · by_cases h14 : N ≤ 332
              · obtain rfl : N = 332 := by omega
                exact cvx332
              · by_cases h16 : N ≤ 333
                · obtain rfl : N = 333 := by omega
                  exact cvx333
                · obtain rfl : N = 334 := by omega
                  exact cvx334
            · by_cases h14 : N ≤ 335
              · obtain rfl : N = 335 := by omega
                exact cvx335
              · by_cases h16 : N ≤ 336
                · obtain rfl : N = 336 := by omega
                  exact cvx336
                · obtain rfl : N = 337 := by omega
                  exact cvx337
        · by_cases h10 : N ≤ 343
          · by_cases h12 : N ≤ 340
            · by_cases h14 : N ≤ 338
              · obtain rfl : N = 338 := by omega
                exact cvx338
              · by_cases h16 : N ≤ 339
                · obtain rfl : N = 339 := by omega
                  exact cvx339
                · obtain rfl : N = 340 := by omega
                  exact cvx340
            · by_cases h14 : N ≤ 341
              · obtain rfl : N = 341 := by omega
                exact cvx341
              · by_cases h16 : N ≤ 342
                · obtain rfl : N = 342 := by omega
                  exact cvx342
                · obtain rfl : N = 343 := by omega
                  exact cvx343
          · by_cases h12 : N ≤ 346
            · by_cases h14 : N ≤ 344
              · obtain rfl : N = 344 := by omega
                exact cvx344
              · by_cases h16 : N ≤ 345
                · obtain rfl : N = 345 := by omega
                  exact cvx345
                · obtain rfl : N = 346 := by omega
                  exact cvx346
            · by_cases h14 : N ≤ 348
              · by_cases h16 : N ≤ 347
                · obtain rfl : N = 347 := by omega
                  exact cvx347
                · obtain rfl : N = 348 := by omega
                  exact cvx348
              · by_cases h16 : N ≤ 349
                · obtain rfl : N = 349 := by omega
                  exact cvx349
                · obtain rfl : N = 350 := by omega
                  exact cvx350
    · by_cases h6 : N ≤ 375
      · by_cases h8 : N ≤ 362
        · by_cases h10 : N ≤ 356
          · by_cases h12 : N ≤ 353
            · by_cases h14 : N ≤ 351
              · obtain rfl : N = 351 := by omega
                exact cvx351
              · by_cases h16 : N ≤ 352
                · obtain rfl : N = 352 := by omega
                  exact cvx352
                · obtain rfl : N = 353 := by omega
                  exact cvx353
            · by_cases h14 : N ≤ 354
              · obtain rfl : N = 354 := by omega
                exact cvx354
              · by_cases h16 : N ≤ 355
                · obtain rfl : N = 355 := by omega
                  exact cvx355
                · obtain rfl : N = 356 := by omega
                  exact cvx356
          · by_cases h12 : N ≤ 359
            · by_cases h14 : N ≤ 357
              · obtain rfl : N = 357 := by omega
                exact cvx357
              · by_cases h16 : N ≤ 358
                · obtain rfl : N = 358 := by omega
                  exact cvx358
                · obtain rfl : N = 359 := by omega
                  exact cvx359
            · by_cases h14 : N ≤ 360
              · obtain rfl : N = 360 := by omega
                exact cvx360
              · by_cases h16 : N ≤ 361
                · obtain rfl : N = 361 := by omega
                  exact cvx361
                · obtain rfl : N = 362 := by omega
                  exact cvx362
        · by_cases h10 : N ≤ 368
          · by_cases h12 : N ≤ 365
            · by_cases h14 : N ≤ 363
              · obtain rfl : N = 363 := by omega
                exact cvx363
              · by_cases h16 : N ≤ 364
                · obtain rfl : N = 364 := by omega
                  exact cvx364
                · obtain rfl : N = 365 := by omega
                  exact cvx365
            · by_cases h14 : N ≤ 366
              · obtain rfl : N = 366 := by omega
                exact cvx366
              · by_cases h16 : N ≤ 367
                · obtain rfl : N = 367 := by omega
                  exact cvx367
                · obtain rfl : N = 368 := by omega
                  exact cvx368
          · by_cases h12 : N ≤ 371
            · by_cases h14 : N ≤ 369
              · obtain rfl : N = 369 := by omega
                exact cvx369
              · by_cases h16 : N ≤ 370
                · obtain rfl : N = 370 := by omega
                  exact cvx370
                · obtain rfl : N = 371 := by omega
                  exact cvx371
            · by_cases h14 : N ≤ 373
              · by_cases h16 : N ≤ 372
                · obtain rfl : N = 372 := by omega
                  exact cvx372
                · obtain rfl : N = 373 := by omega
                  exact cvx373
              · by_cases h16 : N ≤ 374
                · obtain rfl : N = 374 := by omega
                  exact cvx374
                · obtain rfl : N = 375 := by omega
                  exact cvx375
      · by_cases h8 : N ≤ 387
        · by_cases h10 : N ≤ 381
          · by_cases h12 : N ≤ 378
            · by_cases h14 : N ≤ 376
              · obtain rfl : N = 376 := by omega
                exact cvx376
              · by_cases h16 : N ≤ 377
                · obtain rfl : N = 377 := by omega
                  exact cvx377
                · obtain rfl : N = 378 := by omega
                  exact cvx378
            · by_cases h14 : N ≤ 379
              · obtain rfl : N = 379 := by omega
                exact cvx379
              · by_cases h16 : N ≤ 380
                · obtain rfl : N = 380 := by omega
                  exact cvx380
                · obtain rfl : N = 381 := by omega
                  exact cvx381
          · by_cases h12 : N ≤ 384
            · by_cases h14 : N ≤ 382
              · obtain rfl : N = 382 := by omega
                exact cvx382
              · by_cases h16 : N ≤ 383
                · obtain rfl : N = 383 := by omega
                  exact cvx383
                · obtain rfl : N = 384 := by omega
                  exact cvx384
            · by_cases h14 : N ≤ 385
              · obtain rfl : N = 385 := by omega
                exact cvx385
              · by_cases h16 : N ≤ 386
                · obtain rfl : N = 386 := by omega
                  exact cvx386
                · obtain rfl : N = 387 := by omega
                  exact cvx387
        · by_cases h10 : N ≤ 393
          · by_cases h12 : N ≤ 390
            · by_cases h14 : N ≤ 388
              · obtain rfl : N = 388 := by omega
                exact cvx388
              · by_cases h16 : N ≤ 389
                · obtain rfl : N = 389 := by omega
                  exact cvx389
                · obtain rfl : N = 390 := by omega
                  exact cvx390
            · by_cases h14 : N ≤ 391
              · obtain rfl : N = 391 := by omega
                exact cvx391
              · by_cases h16 : N ≤ 392
                · obtain rfl : N = 392 := by omega
                  exact cvx392
                · obtain rfl : N = 393 := by omega
                  exact cvx393
          · by_cases h12 : N ≤ 396
            · by_cases h14 : N ≤ 394
              · obtain rfl : N = 394 := by omega
                exact cvx394
              · by_cases h16 : N ≤ 395
                · obtain rfl : N = 395 := by omega
                  exact cvx395
                · obtain rfl : N = 396 := by omega
                  exact cvx396
            · by_cases h14 : N ≤ 398
              · by_cases h16 : N ≤ 397
                · obtain rfl : N = 397 := by omega
                  exact cvx397
                · obtain rfl : N = 398 := by omega
                  exact cvx398
              · by_cases h16 : N ≤ 399
                · obtain rfl : N = 399 := by omega
                  exact cvx399
                · obtain rfl : N = 400 := by omega
                  exact cvx400
  · by_cases h4 : N ≤ 450
    · by_cases h6 : N ≤ 425
      · by_cases h8 : N ≤ 412
        · by_cases h10 : N ≤ 406
          · by_cases h12 : N ≤ 403
            · by_cases h14 : N ≤ 401
              · obtain rfl : N = 401 := by omega
                exact cvx401
              · by_cases h16 : N ≤ 402
                · obtain rfl : N = 402 := by omega
                  exact cvx402
                · obtain rfl : N = 403 := by omega
                  exact cvx403
            · by_cases h14 : N ≤ 404
              · obtain rfl : N = 404 := by omega
                exact cvx404
              · by_cases h16 : N ≤ 405
                · obtain rfl : N = 405 := by omega
                  exact cvx405
                · obtain rfl : N = 406 := by omega
                  exact cvx406
          · by_cases h12 : N ≤ 409
            · by_cases h14 : N ≤ 407
              · obtain rfl : N = 407 := by omega
                exact cvx407
              · by_cases h16 : N ≤ 408
                · obtain rfl : N = 408 := by omega
                  exact cvx408
                · obtain rfl : N = 409 := by omega
                  exact cvx409
            · by_cases h14 : N ≤ 410
              · obtain rfl : N = 410 := by omega
                exact cvx410
              · by_cases h16 : N ≤ 411
                · obtain rfl : N = 411 := by omega
                  exact cvx411
                · obtain rfl : N = 412 := by omega
                  exact cvx412
        · by_cases h10 : N ≤ 418
          · by_cases h12 : N ≤ 415
            · by_cases h14 : N ≤ 413
              · obtain rfl : N = 413 := by omega
                exact cvx413
              · by_cases h16 : N ≤ 414
                · obtain rfl : N = 414 := by omega
                  exact cvx414
                · obtain rfl : N = 415 := by omega
                  exact cvx415
            · by_cases h14 : N ≤ 416
              · obtain rfl : N = 416 := by omega
                exact cvx416
              · by_cases h16 : N ≤ 417
                · obtain rfl : N = 417 := by omega
                  exact cvx417
                · obtain rfl : N = 418 := by omega
                  exact cvx418
          · by_cases h12 : N ≤ 421
            · by_cases h14 : N ≤ 419
              · obtain rfl : N = 419 := by omega
                exact cvx419
              · by_cases h16 : N ≤ 420
                · obtain rfl : N = 420 := by omega
                  exact cvx420
                · obtain rfl : N = 421 := by omega
                  exact cvx421
            · by_cases h14 : N ≤ 423
              · by_cases h16 : N ≤ 422
                · obtain rfl : N = 422 := by omega
                  exact cvx422
                · obtain rfl : N = 423 := by omega
                  exact cvx423
              · by_cases h16 : N ≤ 424
                · obtain rfl : N = 424 := by omega
                  exact cvx424
                · obtain rfl : N = 425 := by omega
                  exact cvx425
      · by_cases h8 : N ≤ 437
        · by_cases h10 : N ≤ 431
          · by_cases h12 : N ≤ 428
            · by_cases h14 : N ≤ 426
              · obtain rfl : N = 426 := by omega
                exact cvx426
              · by_cases h16 : N ≤ 427
                · obtain rfl : N = 427 := by omega
                  exact cvx427
                · obtain rfl : N = 428 := by omega
                  exact cvx428
            · by_cases h14 : N ≤ 429
              · obtain rfl : N = 429 := by omega
                exact cvx429
              · by_cases h16 : N ≤ 430
                · obtain rfl : N = 430 := by omega
                  exact cvx430
                · obtain rfl : N = 431 := by omega
                  exact cvx431
          · by_cases h12 : N ≤ 434
            · by_cases h14 : N ≤ 432
              · obtain rfl : N = 432 := by omega
                exact cvx432
              · by_cases h16 : N ≤ 433
                · obtain rfl : N = 433 := by omega
                  exact cvx433
                · obtain rfl : N = 434 := by omega
                  exact cvx434
            · by_cases h14 : N ≤ 435
              · obtain rfl : N = 435 := by omega
                exact cvx435
              · by_cases h16 : N ≤ 436
                · obtain rfl : N = 436 := by omega
                  exact cvx436
                · obtain rfl : N = 437 := by omega
                  exact cvx437
        · by_cases h10 : N ≤ 443
          · by_cases h12 : N ≤ 440
            · by_cases h14 : N ≤ 438
              · obtain rfl : N = 438 := by omega
                exact cvx438
              · by_cases h16 : N ≤ 439
                · obtain rfl : N = 439 := by omega
                  exact cvx439
                · obtain rfl : N = 440 := by omega
                  exact cvx440
            · by_cases h14 : N ≤ 441
              · obtain rfl : N = 441 := by omega
                exact cvx441
              · by_cases h16 : N ≤ 442
                · obtain rfl : N = 442 := by omega
                  exact cvx442
                · obtain rfl : N = 443 := by omega
                  exact cvx443
          · by_cases h12 : N ≤ 446
            · by_cases h14 : N ≤ 444
              · obtain rfl : N = 444 := by omega
                exact cvx444
              · by_cases h16 : N ≤ 445
                · obtain rfl : N = 445 := by omega
                  exact cvx445
                · obtain rfl : N = 446 := by omega
                  exact cvx446
            · by_cases h14 : N ≤ 448
              · by_cases h16 : N ≤ 447
                · obtain rfl : N = 447 := by omega
                  exact cvx447
                · obtain rfl : N = 448 := by omega
                  exact cvx448
              · by_cases h16 : N ≤ 449
                · obtain rfl : N = 449 := by omega
                  exact cvx449
                · obtain rfl : N = 450 := by omega
                  exact cvx450
    · by_cases h6 : N ≤ 475
      · by_cases h8 : N ≤ 462
        · by_cases h10 : N ≤ 456
          · by_cases h12 : N ≤ 453
            · by_cases h14 : N ≤ 451
              · obtain rfl : N = 451 := by omega
                exact cvx451
              · by_cases h16 : N ≤ 452
                · obtain rfl : N = 452 := by omega
                  exact cvx452
                · obtain rfl : N = 453 := by omega
                  exact cvx453
            · by_cases h14 : N ≤ 454
              · obtain rfl : N = 454 := by omega
                exact cvx454
              · by_cases h16 : N ≤ 455
                · obtain rfl : N = 455 := by omega
                  exact cvx455
                · obtain rfl : N = 456 := by omega
                  exact cvx456
          · by_cases h12 : N ≤ 459
            · by_cases h14 : N ≤ 457
              · obtain rfl : N = 457 := by omega
                exact cvx457
              · by_cases h16 : N ≤ 458
                · obtain rfl : N = 458 := by omega
                  exact cvx458
                · obtain rfl : N = 459 := by omega
                  exact cvx459
            · by_cases h14 : N ≤ 460
              · obtain rfl : N = 460 := by omega
                exact cvx460
              · by_cases h16 : N ≤ 461
                · obtain rfl : N = 461 := by omega
                  exact cvx461
                · obtain rfl : N = 462 := by omega
                  exact cvx462
        · by_cases h10 : N ≤ 468
          · by_cases h12 : N ≤ 465
            · by_cases h14 : N ≤ 463
              · obtain rfl : N = 463 := by omega
                exact cvx463
              · by_cases h16 : N ≤ 464
                · obtain rfl : N = 464 := by omega
                  exact cvx464
                · obtain rfl : N = 465 := by omega
                  exact cvx465
            · by_cases h14 : N ≤ 466
              · obtain rfl : N = 466 := by omega
                exact cvx466
              · by_cases h16 : N ≤ 467
                · obtain rfl : N = 467 := by omega
                  exact cvx467
                · obtain rfl : N = 468 := by omega
                  exact cvx468
          · by_cases h12 : N ≤ 471
            · by_cases h14 : N ≤ 469
              · obtain rfl : N = 469 := by omega
                exact cvx469
              · by_cases h16 : N ≤ 470
                · obtain rfl : N = 470 := by omega
                  exact cvx470
                · obtain rfl : N = 471 := by omega
                  exact cvx471
            · by_cases h14 : N ≤ 473
              · by_cases h16 : N ≤ 472
                · obtain rfl : N = 472 := by omega
                  exact cvx472
                · obtain rfl : N = 473 := by omega
                  exact cvx473
              · by_cases h16 : N ≤ 474
                · obtain rfl : N = 474 := by omega
                  exact cvx474
                · obtain rfl : N = 475 := by omega
                  exact cvx475
      · by_cases h8 : N ≤ 487
        · by_cases h10 : N ≤ 481
          · by_cases h12 : N ≤ 478
            · by_cases h14 : N ≤ 476
              · obtain rfl : N = 476 := by omega
                exact cvx476
              · by_cases h16 : N ≤ 477
                · obtain rfl : N = 477 := by omega
                  exact cvx477
                · obtain rfl : N = 478 := by omega
                  exact cvx478
            · by_cases h14 : N ≤ 479
              · obtain rfl : N = 479 := by omega
                exact cvx479
              · by_cases h16 : N ≤ 480
                · obtain rfl : N = 480 := by omega
                  exact cvx480
                · obtain rfl : N = 481 := by omega
                  exact cvx481
          · by_cases h12 : N ≤ 484
            · by_cases h14 : N ≤ 482
              · obtain rfl : N = 482 := by omega
                exact cvx482
              · by_cases h16 : N ≤ 483
                · obtain rfl : N = 483 := by omega
                  exact cvx483
                · obtain rfl : N = 484 := by omega
                  exact cvx484
            · by_cases h14 : N ≤ 485
              · obtain rfl : N = 485 := by omega
                exact cvx485
              · by_cases h16 : N ≤ 486
                · obtain rfl : N = 486 := by omega
                  exact cvx486
                · obtain rfl : N = 487 := by omega
                  exact cvx487
        · by_cases h10 : N ≤ 493
          · by_cases h12 : N ≤ 490
            · by_cases h14 : N ≤ 488
              · obtain rfl : N = 488 := by omega
                exact cvx488
              · by_cases h16 : N ≤ 489
                · obtain rfl : N = 489 := by omega
                  exact cvx489
                · obtain rfl : N = 490 := by omega
                  exact cvx490
            · by_cases h14 : N ≤ 491
              · obtain rfl : N = 491 := by omega
                exact cvx491
              · by_cases h16 : N ≤ 492
                · obtain rfl : N = 492 := by omega
                  exact cvx492
                · obtain rfl : N = 493 := by omega
                  exact cvx493
          · by_cases h12 : N ≤ 496
            · by_cases h14 : N ≤ 494
              · obtain rfl : N = 494 := by omega
                exact cvx494
              · by_cases h16 : N ≤ 495
                · obtain rfl : N = 495 := by omega
                  exact cvx495
                · obtain rfl : N = 496 := by omega
                  exact cvx496
            · by_cases h14 : N ≤ 498
              · by_cases h16 : N ≤ 497
                · obtain rfl : N = 497 := by omega
                  exact cvx497
                · obtain rfl : N = 498 := by omega
                  exact cvx498
              · by_cases h16 : N ≤ 499
                · obtain rfl : N = 499 := by omega
                  exact cvx499
                · obtain rfl : N = 500 := by omega
                  exact cvx500

theorem cen_301_500 {N : ℕ} (h1 : 301 ≤ N) (h2 : N ≤ 500) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 400
  · by_cases h4 : N ≤ 350
    · by_cases h6 : N ≤ 324
      · by_cases h8 : N ≤ 312
        · by_cases h10 : N ≤ 306
          · by_cases h12 : N ≤ 302
            · obtain rfl : N = 302 := by omega
              exact cen302
            · by_cases h14 : N ≤ 304
              · obtain rfl : N = 304 := by omega
                exact cen304
              · obtain rfl : N = 306 := by omega
                exact cen306
          · by_cases h12 : N ≤ 308
            · obtain rfl : N = 308 := by omega
              exact cen308
            · by_cases h14 : N ≤ 310
              · obtain rfl : N = 310 := by omega
                exact cen310
              · obtain rfl : N = 312 := by omega
                exact cen312
        · by_cases h10 : N ≤ 318
          · by_cases h12 : N ≤ 314
            · obtain rfl : N = 314 := by omega
              exact cen314
            · by_cases h14 : N ≤ 316
              · obtain rfl : N = 316 := by omega
                exact cen316
              · obtain rfl : N = 318 := by omega
                exact cen318
          · by_cases h12 : N ≤ 320
            · obtain rfl : N = 320 := by omega
              exact cen320
            · by_cases h14 : N ≤ 322
              · obtain rfl : N = 322 := by omega
                exact cen322
              · obtain rfl : N = 324 := by omega
                exact cen324
      · by_cases h8 : N ≤ 336
        · by_cases h10 : N ≤ 330
          · by_cases h12 : N ≤ 326
            · obtain rfl : N = 326 := by omega
              exact cen326
            · by_cases h14 : N ≤ 328
              · obtain rfl : N = 328 := by omega
                exact cen328
              · obtain rfl : N = 330 := by omega
                exact cen330
          · by_cases h12 : N ≤ 332
            · obtain rfl : N = 332 := by omega
              exact cen332
            · by_cases h14 : N ≤ 334
              · obtain rfl : N = 334 := by omega
                exact cen334
              · obtain rfl : N = 336 := by omega
                exact cen336
        · by_cases h10 : N ≤ 342
          · by_cases h12 : N ≤ 338
            · obtain rfl : N = 338 := by omega
              exact cen338
            · by_cases h14 : N ≤ 340
              · obtain rfl : N = 340 := by omega
                exact cen340
              · obtain rfl : N = 342 := by omega
                exact cen342
          · by_cases h12 : N ≤ 346
            · by_cases h14 : N ≤ 344
              · obtain rfl : N = 344 := by omega
                exact cen344
              · obtain rfl : N = 346 := by omega
                exact cen346
            · by_cases h14 : N ≤ 348
              · obtain rfl : N = 348 := by omega
                exact cen348
              · obtain rfl : N = 350 := by omega
                exact cen350
    · by_cases h6 : N ≤ 374
      · by_cases h8 : N ≤ 362
        · by_cases h10 : N ≤ 356
          · by_cases h12 : N ≤ 352
            · obtain rfl : N = 352 := by omega
              exact cen352
            · by_cases h14 : N ≤ 354
              · obtain rfl : N = 354 := by omega
                exact cen354
              · obtain rfl : N = 356 := by omega
                exact cen356
          · by_cases h12 : N ≤ 358
            · obtain rfl : N = 358 := by omega
              exact cen358
            · by_cases h14 : N ≤ 360
              · obtain rfl : N = 360 := by omega
                exact cen360
              · obtain rfl : N = 362 := by omega
                exact cen362
        · by_cases h10 : N ≤ 368
          · by_cases h12 : N ≤ 364
            · obtain rfl : N = 364 := by omega
              exact cen364
            · by_cases h14 : N ≤ 366
              · obtain rfl : N = 366 := by omega
                exact cen366
              · obtain rfl : N = 368 := by omega
                exact cen368
          · by_cases h12 : N ≤ 370
            · obtain rfl : N = 370 := by omega
              exact cen370
            · by_cases h14 : N ≤ 372
              · obtain rfl : N = 372 := by omega
                exact cen372
              · obtain rfl : N = 374 := by omega
                exact cen374
      · by_cases h8 : N ≤ 386
        · by_cases h10 : N ≤ 380
          · by_cases h12 : N ≤ 376
            · obtain rfl : N = 376 := by omega
              exact cen376
            · by_cases h14 : N ≤ 378
              · obtain rfl : N = 378 := by omega
                exact cen378
              · obtain rfl : N = 380 := by omega
                exact cen380
          · by_cases h12 : N ≤ 382
            · obtain rfl : N = 382 := by omega
              exact cen382
            · by_cases h14 : N ≤ 384
              · obtain rfl : N = 384 := by omega
                exact cen384
              · obtain rfl : N = 386 := by omega
                exact cen386
        · by_cases h10 : N ≤ 392
          · by_cases h12 : N ≤ 388
            · obtain rfl : N = 388 := by omega
              exact cen388
            · by_cases h14 : N ≤ 390
              · obtain rfl : N = 390 := by omega
                exact cen390
              · obtain rfl : N = 392 := by omega
                exact cen392
          · by_cases h12 : N ≤ 396
            · by_cases h14 : N ≤ 394
              · obtain rfl : N = 394 := by omega
                exact cen394
              · obtain rfl : N = 396 := by omega
                exact cen396
            · by_cases h14 : N ≤ 398
              · obtain rfl : N = 398 := by omega
                exact cen398
              · obtain rfl : N = 400 := by omega
                exact cen400
  · by_cases h4 : N ≤ 450
    · by_cases h6 : N ≤ 424
      · by_cases h8 : N ≤ 412
        · by_cases h10 : N ≤ 406
          · by_cases h12 : N ≤ 402
            · obtain rfl : N = 402 := by omega
              exact cen402
            · by_cases h14 : N ≤ 404
              · obtain rfl : N = 404 := by omega
                exact cen404
              · obtain rfl : N = 406 := by omega
                exact cen406
          · by_cases h12 : N ≤ 408
            · obtain rfl : N = 408 := by omega
              exact cen408
            · by_cases h14 : N ≤ 410
              · obtain rfl : N = 410 := by omega
                exact cen410
              · obtain rfl : N = 412 := by omega
                exact cen412
        · by_cases h10 : N ≤ 418
          · by_cases h12 : N ≤ 414
            · obtain rfl : N = 414 := by omega
              exact cen414
            · by_cases h14 : N ≤ 416
              · obtain rfl : N = 416 := by omega
                exact cen416
              · obtain rfl : N = 418 := by omega
                exact cen418
          · by_cases h12 : N ≤ 420
            · obtain rfl : N = 420 := by omega
              exact cen420
            · by_cases h14 : N ≤ 422
              · obtain rfl : N = 422 := by omega
                exact cen422
              · obtain rfl : N = 424 := by omega
                exact cen424
      · by_cases h8 : N ≤ 436
        · by_cases h10 : N ≤ 430
          · by_cases h12 : N ≤ 426
            · obtain rfl : N = 426 := by omega
              exact cen426
            · by_cases h14 : N ≤ 428
              · obtain rfl : N = 428 := by omega
                exact cen428
              · obtain rfl : N = 430 := by omega
                exact cen430
          · by_cases h12 : N ≤ 432
            · obtain rfl : N = 432 := by omega
              exact cen432
            · by_cases h14 : N ≤ 434
              · obtain rfl : N = 434 := by omega
                exact cen434
              · obtain rfl : N = 436 := by omega
                exact cen436
        · by_cases h10 : N ≤ 442
          · by_cases h12 : N ≤ 438
            · obtain rfl : N = 438 := by omega
              exact cen438
            · by_cases h14 : N ≤ 440
              · obtain rfl : N = 440 := by omega
                exact cen440
              · obtain rfl : N = 442 := by omega
                exact cen442
          · by_cases h12 : N ≤ 446
            · by_cases h14 : N ≤ 444
              · obtain rfl : N = 444 := by omega
                exact cen444
              · obtain rfl : N = 446 := by omega
                exact cen446
            · by_cases h14 : N ≤ 448
              · obtain rfl : N = 448 := by omega
                exact cen448
              · obtain rfl : N = 450 := by omega
                exact cen450
    · by_cases h6 : N ≤ 474
      · by_cases h8 : N ≤ 462
        · by_cases h10 : N ≤ 456
          · by_cases h12 : N ≤ 452
            · obtain rfl : N = 452 := by omega
              exact cen452
            · by_cases h14 : N ≤ 454
              · obtain rfl : N = 454 := by omega
                exact cen454
              · obtain rfl : N = 456 := by omega
                exact cen456
          · by_cases h12 : N ≤ 458
            · obtain rfl : N = 458 := by omega
              exact cen458
            · by_cases h14 : N ≤ 460
              · obtain rfl : N = 460 := by omega
                exact cen460
              · obtain rfl : N = 462 := by omega
                exact cen462
        · by_cases h10 : N ≤ 468
          · by_cases h12 : N ≤ 464
            · obtain rfl : N = 464 := by omega
              exact cen464
            · by_cases h14 : N ≤ 466
              · obtain rfl : N = 466 := by omega
                exact cen466
              · obtain rfl : N = 468 := by omega
                exact cen468
          · by_cases h12 : N ≤ 470
            · obtain rfl : N = 470 := by omega
              exact cen470
            · by_cases h14 : N ≤ 472
              · obtain rfl : N = 472 := by omega
                exact cen472
              · obtain rfl : N = 474 := by omega
                exact cen474
      · by_cases h8 : N ≤ 486
        · by_cases h10 : N ≤ 480
          · by_cases h12 : N ≤ 476
            · obtain rfl : N = 476 := by omega
              exact cen476
            · by_cases h14 : N ≤ 478
              · obtain rfl : N = 478 := by omega
                exact cen478
              · obtain rfl : N = 480 := by omega
                exact cen480
          · by_cases h12 : N ≤ 482
            · obtain rfl : N = 482 := by omega
              exact cen482
            · by_cases h14 : N ≤ 484
              · obtain rfl : N = 484 := by omega
                exact cen484
              · obtain rfl : N = 486 := by omega
                exact cen486
        · by_cases h10 : N ≤ 492
          · by_cases h12 : N ≤ 488
            · obtain rfl : N = 488 := by omega
              exact cen488
            · by_cases h14 : N ≤ 490
              · obtain rfl : N = 490 := by omega
                exact cen490
              · obtain rfl : N = 492 := by omega
                exact cen492
          · by_cases h12 : N ≤ 496
            · by_cases h14 : N ≤ 494
              · obtain rfl : N = 494 := by omega
                exact cen494
              · obtain rfl : N = 496 := by omega
                exact cen496
            · by_cases h14 : N ≤ 498
              · obtain rfl : N = 498 := by omega
                exact cen498
              · obtain rfl : N = 500 := by omega
                exact cen500

end Kagey131.PaperD.T7
