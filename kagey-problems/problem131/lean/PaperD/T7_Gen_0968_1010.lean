import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 968, …, 1010` (generated)

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

/-! ### `N = 968` -/

def pL968 : Prm := ⟨76, 36, 37, 970, 11, 18446744073709551616, 177089717235676824, 177089717235676824⟩
def pH968 : Prm := ⟨76, 36, 37, 970, 11, 18446744073709551616, 177091916258932376, 177091916258932376⟩
def pI968 : Prm := ⟨64, 31, 30, 970, 11, 18446744073709551616, 177089717235676824, 177091916258932376⟩
theorem L968_fin : (prmOK pL968 968 && ptTest pL968 (runFrom pL968 (fmask pL968) (cmask pL968) (hmask pL968) 1 967 (true, (init pL968), (init pL968))) 968 484 false) = true := by
  decide +kernel
theorem L968_ok : RunOK pL968 968 (runFrom pL968 (fmask pL968) (cmask pL968) (hmask pL968) 1 967 (true, (init pL968), (init pL968))) ∧ ptTest pL968 (runFrom pL968 (fmask pL968) (cmask pL968) (hmask pL968) 1 967 (true, (init pL968), (init pL968))) 968 484 false = true :=
  fin_run (runOK_init (prmOK_of_and L968_fin) true) (by decide) rfl L968_fin ptTest_fst
theorem H968_fin : (prmOK pH968 968 && ptTest pH968 (runFrom pH968 (fmask pH968) (cmask pH968) (hmask pH968) 1 967 (true, (init pH968), (init pH968))) 968 484 true) = true := by
  decide +kernel
theorem H968_ok : RunOK pH968 968 (runFrom pH968 (fmask pH968) (cmask pH968) (hmask pH968) 1 967 (true, (init pH968), (init pH968))) ∧ ptTest pH968 (runFrom pH968 (fmask pH968) (cmask pH968) (hmask pH968) 1 967 (true, (init pH968), (init pH968))) 968 484 true = true :=
  fin_run (runOK_init (prmOK_of_and H968_fin) true) (by decide) rfl H968_fin ptTest_fst
theorem I968_fin : (prmOK pI968 968 && intTest pI968 (runFrom pI968 (fmask pI968) (cmask pI968) (hmask pI968) 1 967 (true, (init pI968), (init pI968))) 968 18 true) = true := by
  decide +kernel
theorem I968_ok : RunOK pI968 968 (runFrom pI968 (fmask pI968) (cmask pI968) (hmask pI968) 1 967 (true, (init pI968), (init pI968))) ∧ intTest pI968 (runFrom pI968 (fmask pI968) (cmask pI968) (hmask pI968) 1 967 (true, (init pI968), (init pI968))) 968 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I968_fin) true) (by decide) rfl I968_fin intTest_fst
theorem link968 : linkOK pL968 pH968 pI968 = true := by decide +kernel
theorem cvx968 : ConvexBetweenHumps 968 :=
  cvx_of L968_ok H968_ok I968_ok link968 (by decide)
theorem cenlink968 : cenLinkOK pI968 968 = true := by decide +kernel
theorem cen968 : CenterUniqueMin 968 ∧ DipHyp 968 ∧ OnePointHyps 968 :=
  cen_of L968_ok H968_ok I968_ok link968 cenlink968

/-! ### `N = 969` -/

def pL969 : Prm := ⟨76, 36, 37, 971, 11, 18446744073709551616, 176943966371003924, 176943966371003924⟩
def pH969 : Prm := ⟨76, 36, 37, 971, 11, 18446744073709551616, 176946165394259476, 176946165394259476⟩
def pI969 : Prm := ⟨64, 31, 30, 971, 11, 18446744073709551616, 176943966371003924, 176946165394259476⟩
theorem L969_fin : (prmOK pL969 969 && ptTest pL969 (runFrom pL969 (fmask pL969) (cmask pL969) (hmask pL969) 1 968 (true, (init pL969), (init pL969))) 969 485 false) = true := by
  decide +kernel
theorem L969_ok : RunOK pL969 969 (runFrom pL969 (fmask pL969) (cmask pL969) (hmask pL969) 1 968 (true, (init pL969), (init pL969))) ∧ ptTest pL969 (runFrom pL969 (fmask pL969) (cmask pL969) (hmask pL969) 1 968 (true, (init pL969), (init pL969))) 969 485 false = true :=
  fin_run (runOK_init (prmOK_of_and L969_fin) true) (by decide) rfl L969_fin ptTest_fst
theorem H969_fin : (prmOK pH969 969 && ptTest pH969 (runFrom pH969 (fmask pH969) (cmask pH969) (hmask pH969) 1 968 (true, (init pH969), (init pH969))) 969 485 true) = true := by
  decide +kernel
theorem H969_ok : RunOK pH969 969 (runFrom pH969 (fmask pH969) (cmask pH969) (hmask pH969) 1 968 (true, (init pH969), (init pH969))) ∧ ptTest pH969 (runFrom pH969 (fmask pH969) (cmask pH969) (hmask pH969) 1 968 (true, (init pH969), (init pH969))) 969 485 true = true :=
  fin_run (runOK_init (prmOK_of_and H969_fin) true) (by decide) rfl H969_fin ptTest_fst
theorem I969_fin : (prmOK pI969 969 && intTest pI969 (runFrom pI969 (fmask pI969) (cmask pI969) (hmask pI969) 1 968 (true, (init pI969), (init pI969))) 969 18 false) = true := by
  decide +kernel
theorem I969_ok : RunOK pI969 969 (runFrom pI969 (fmask pI969) (cmask pI969) (hmask pI969) 1 968 (true, (init pI969), (init pI969))) ∧ intTest pI969 (runFrom pI969 (fmask pI969) (cmask pI969) (hmask pI969) 1 968 (true, (init pI969), (init pI969))) 969 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I969_fin) true) (by decide) rfl I969_fin intTest_fst
theorem link969 : linkOK pL969 pH969 pI969 = true := by decide +kernel
theorem cvx969 : ConvexBetweenHumps 969 :=
  cvx_of L969_ok H969_ok I969_ok link969 (by decide)

/-! ### `N = 970` -/

def pL970 : Prm := ⟨76, 36, 37, 972, 11, 18446744073709551616, 176798604981698916, 176798604981698916⟩
def pH970 : Prm := ⟨76, 36, 37, 972, 11, 18446744073709551616, 176800804004954468, 176800804004954468⟩
def pI970 : Prm := ⟨64, 31, 30, 972, 11, 18446744073709551616, 176798604981698916, 176800804004954468⟩
theorem L970_fin : (prmOK pL970 970 && ptTest pL970 (runFrom pL970 (fmask pL970) (cmask pL970) (hmask pL970) 1 969 (true, (init pL970), (init pL970))) 970 485 false) = true := by
  decide +kernel
theorem L970_ok : RunOK pL970 970 (runFrom pL970 (fmask pL970) (cmask pL970) (hmask pL970) 1 969 (true, (init pL970), (init pL970))) ∧ ptTest pL970 (runFrom pL970 (fmask pL970) (cmask pL970) (hmask pL970) 1 969 (true, (init pL970), (init pL970))) 970 485 false = true :=
  fin_run (runOK_init (prmOK_of_and L970_fin) true) (by decide) rfl L970_fin ptTest_fst
theorem H970_fin : (prmOK pH970 970 && ptTest pH970 (runFrom pH970 (fmask pH970) (cmask pH970) (hmask pH970) 1 969 (true, (init pH970), (init pH970))) 970 485 true) = true := by
  decide +kernel
theorem H970_ok : RunOK pH970 970 (runFrom pH970 (fmask pH970) (cmask pH970) (hmask pH970) 1 969 (true, (init pH970), (init pH970))) ∧ ptTest pH970 (runFrom pH970 (fmask pH970) (cmask pH970) (hmask pH970) 1 969 (true, (init pH970), (init pH970))) 970 485 true = true :=
  fin_run (runOK_init (prmOK_of_and H970_fin) true) (by decide) rfl H970_fin ptTest_fst
theorem I970_fin : (prmOK pI970 970 && intTest pI970 (runFrom pI970 (fmask pI970) (cmask pI970) (hmask pI970) 1 969 (true, (init pI970), (init pI970))) 970 18 true) = true := by
  decide +kernel
theorem I970_ok : RunOK pI970 970 (runFrom pI970 (fmask pI970) (cmask pI970) (hmask pI970) 1 969 (true, (init pI970), (init pI970))) ∧ intTest pI970 (runFrom pI970 (fmask pI970) (cmask pI970) (hmask pI970) 1 969 (true, (init pI970), (init pI970))) 970 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I970_fin) true) (by decide) rfl I970_fin intTest_fst
theorem link970 : linkOK pL970 pH970 pI970 = true := by decide +kernel
theorem cvx970 : ConvexBetweenHumps 970 :=
  cvx_of L970_ok H970_ok I970_ok link970 (by decide)
theorem cenlink970 : cenLinkOK pI970 970 = true := by decide +kernel
theorem cen970 : CenterUniqueMin 970 ∧ DipHyp 970 ∧ OnePointHyps 970 :=
  cen_of L970_ok H970_ok I970_ok link970 cenlink970

/-! ### `N = 971` -/

def pL971 : Prm := ⟨76, 36, 37, 973, 11, 18446744073709551616, 176653378216510798, 176653378216510798⟩
def pH971 : Prm := ⟨76, 36, 37, 973, 11, 18446744073709551616, 176655577239766350, 176655577239766350⟩
def pI971 : Prm := ⟨64, 31, 30, 973, 11, 18446744073709551616, 176653378216510798, 176655577239766350⟩
theorem L971_fin : (prmOK pL971 971 && ptTest pL971 (runFrom pL971 (fmask pL971) (cmask pL971) (hmask pL971) 1 970 (true, (init pL971), (init pL971))) 971 486 false) = true := by
  decide +kernel
theorem L971_ok : RunOK pL971 971 (runFrom pL971 (fmask pL971) (cmask pL971) (hmask pL971) 1 970 (true, (init pL971), (init pL971))) ∧ ptTest pL971 (runFrom pL971 (fmask pL971) (cmask pL971) (hmask pL971) 1 970 (true, (init pL971), (init pL971))) 971 486 false = true :=
  fin_run (runOK_init (prmOK_of_and L971_fin) true) (by decide) rfl L971_fin ptTest_fst
theorem H971_fin : (prmOK pH971 971 && ptTest pH971 (runFrom pH971 (fmask pH971) (cmask pH971) (hmask pH971) 1 970 (true, (init pH971), (init pH971))) 971 486 true) = true := by
  decide +kernel
theorem H971_ok : RunOK pH971 971 (runFrom pH971 (fmask pH971) (cmask pH971) (hmask pH971) 1 970 (true, (init pH971), (init pH971))) ∧ ptTest pH971 (runFrom pH971 (fmask pH971) (cmask pH971) (hmask pH971) 1 970 (true, (init pH971), (init pH971))) 971 486 true = true :=
  fin_run (runOK_init (prmOK_of_and H971_fin) true) (by decide) rfl H971_fin ptTest_fst
theorem I971_fin : (prmOK pI971 971 && intTest pI971 (runFrom pI971 (fmask pI971) (cmask pI971) (hmask pI971) 1 970 (true, (init pI971), (init pI971))) 971 18 false) = true := by
  decide +kernel
theorem I971_ok : RunOK pI971 971 (runFrom pI971 (fmask pI971) (cmask pI971) (hmask pI971) 1 970 (true, (init pI971), (init pI971))) ∧ intTest pI971 (runFrom pI971 (fmask pI971) (cmask pI971) (hmask pI971) 1 970 (true, (init pI971), (init pI971))) 971 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I971_fin) true) (by decide) rfl I971_fin intTest_fst
theorem link971 : linkOK pL971 pH971 pI971 = true := by decide +kernel
theorem cvx971 : ConvexBetweenHumps 971 :=
  cvx_of L971_ok H971_ok I971_ok link971 (by decide)

/-! ### `N = 972` -/

def pL972 : Prm := ⟨76, 36, 37, 974, 11, 18446744073709551616, 176508538666872191, 176508538666872191⟩
def pH972 : Prm := ⟨76, 36, 37, 974, 11, 18446744073709551616, 176510737690127743, 176510737690127743⟩
def pI972 : Prm := ⟨64, 31, 30, 974, 11, 18446744073709551616, 176508538666872191, 176510737690127743⟩
theorem L972_fin : (prmOK pL972 972 && ptTest pL972 (runFrom pL972 (fmask pL972) (cmask pL972) (hmask pL972) 1 971 (true, (init pL972), (init pL972))) 972 486 false) = true := by
  decide +kernel
theorem L972_ok : RunOK pL972 972 (runFrom pL972 (fmask pL972) (cmask pL972) (hmask pL972) 1 971 (true, (init pL972), (init pL972))) ∧ ptTest pL972 (runFrom pL972 (fmask pL972) (cmask pL972) (hmask pL972) 1 971 (true, (init pL972), (init pL972))) 972 486 false = true :=
  fin_run (runOK_init (prmOK_of_and L972_fin) true) (by decide) rfl L972_fin ptTest_fst
theorem H972_fin : (prmOK pH972 972 && ptTest pH972 (runFrom pH972 (fmask pH972) (cmask pH972) (hmask pH972) 1 971 (true, (init pH972), (init pH972))) 972 486 true) = true := by
  decide +kernel
theorem H972_ok : RunOK pH972 972 (runFrom pH972 (fmask pH972) (cmask pH972) (hmask pH972) 1 971 (true, (init pH972), (init pH972))) ∧ ptTest pH972 (runFrom pH972 (fmask pH972) (cmask pH972) (hmask pH972) 1 971 (true, (init pH972), (init pH972))) 972 486 true = true :=
  fin_run (runOK_init (prmOK_of_and H972_fin) true) (by decide) rfl H972_fin ptTest_fst
theorem I972_fin : (prmOK pI972 972 && intTest pI972 (runFrom pI972 (fmask pI972) (cmask pI972) (hmask pI972) 1 971 (true, (init pI972), (init pI972))) 972 18 true) = true := by
  decide +kernel
theorem I972_ok : RunOK pI972 972 (runFrom pI972 (fmask pI972) (cmask pI972) (hmask pI972) 1 971 (true, (init pI972), (init pI972))) ∧ intTest pI972 (runFrom pI972 (fmask pI972) (cmask pI972) (hmask pI972) 1 971 (true, (init pI972), (init pI972))) 972 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I972_fin) true) (by decide) rfl I972_fin intTest_fst
theorem link972 : linkOK pL972 pH972 pI972 = true := by decide +kernel
theorem cvx972 : ConvexBetweenHumps 972 :=
  cvx_of L972_ok H972_ok I972_ok link972 (by decide)
theorem cenlink972 : cenLinkOK pI972 972 = true := by decide +kernel
theorem cen972 : CenterUniqueMin 972 ∧ DipHyp 972 ∧ OnePointHyps 972 :=
  cen_of L972_ok H972_ok I972_ok link972 cenlink972

/-! ### `N = 973` -/

def pL973 : Prm := ⟨76, 36, 37, 975, 11, 18446744073709551616, 176363833081473544, 176363833081473544⟩
def pH973 : Prm := ⟨76, 36, 37, 975, 11, 18446744073709551616, 176366032104729096, 176366032104729096⟩
def pI973 : Prm := ⟨65, 31, 31, 975, 11, 18446744073709551616, 176363833081473544, 176366032104729096⟩
theorem L973_fin : (prmOK pL973 973 && ptTest pL973 (runFrom pL973 (fmask pL973) (cmask pL973) (hmask pL973) 1 972 (true, (init pL973), (init pL973))) 973 487 false) = true := by
  decide +kernel
theorem L973_ok : RunOK pL973 973 (runFrom pL973 (fmask pL973) (cmask pL973) (hmask pL973) 1 972 (true, (init pL973), (init pL973))) ∧ ptTest pL973 (runFrom pL973 (fmask pL973) (cmask pL973) (hmask pL973) 1 972 (true, (init pL973), (init pL973))) 973 487 false = true :=
  fin_run (runOK_init (prmOK_of_and L973_fin) true) (by decide) rfl L973_fin ptTest_fst
theorem H973_fin : (prmOK pH973 973 && ptTest pH973 (runFrom pH973 (fmask pH973) (cmask pH973) (hmask pH973) 1 972 (true, (init pH973), (init pH973))) 973 487 true) = true := by
  decide +kernel
theorem H973_ok : RunOK pH973 973 (runFrom pH973 (fmask pH973) (cmask pH973) (hmask pH973) 1 972 (true, (init pH973), (init pH973))) ∧ ptTest pH973 (runFrom pH973 (fmask pH973) (cmask pH973) (hmask pH973) 1 972 (true, (init pH973), (init pH973))) 973 487 true = true :=
  fin_run (runOK_init (prmOK_of_and H973_fin) true) (by decide) rfl H973_fin ptTest_fst
theorem I973_fin : (prmOK pI973 973 && intTest pI973 (runFrom pI973 (fmask pI973) (cmask pI973) (hmask pI973) 1 972 (true, (init pI973), (init pI973))) 973 18 false) = true := by
  decide +kernel
theorem I973_ok : RunOK pI973 973 (runFrom pI973 (fmask pI973) (cmask pI973) (hmask pI973) 1 972 (true, (init pI973), (init pI973))) ∧ intTest pI973 (runFrom pI973 (fmask pI973) (cmask pI973) (hmask pI973) 1 972 (true, (init pI973), (init pI973))) 973 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I973_fin) true) (by decide) rfl I973_fin intTest_fst
theorem link973 : linkOK pL973 pH973 pI973 = true := by decide +kernel
theorem cvx973 : ConvexBetweenHumps 973 :=
  cvx_of L973_ok H973_ok I973_ok link973 (by decide)

/-! ### `N = 974` -/

def pL974 : Prm := ⟨76, 36, 37, 976, 11, 18446744073709551616, 176219512469478005, 176219512469478005⟩
def pH974 : Prm := ⟨76, 36, 37, 976, 11, 18446744073709551616, 176221711492733557, 176221711492733557⟩
def pI974 : Prm := ⟨64, 31, 30, 976, 11, 18446744073709551616, 176219512469478005, 176221711492733557⟩
theorem L974_fin : (prmOK pL974 974 && ptTest pL974 (runFrom pL974 (fmask pL974) (cmask pL974) (hmask pL974) 1 973 (true, (init pL974), (init pL974))) 974 487 false) = true := by
  decide +kernel
theorem L974_ok : RunOK pL974 974 (runFrom pL974 (fmask pL974) (cmask pL974) (hmask pL974) 1 973 (true, (init pL974), (init pL974))) ∧ ptTest pL974 (runFrom pL974 (fmask pL974) (cmask pL974) (hmask pL974) 1 973 (true, (init pL974), (init pL974))) 974 487 false = true :=
  fin_run (runOK_init (prmOK_of_and L974_fin) true) (by decide) rfl L974_fin ptTest_fst
theorem H974_fin : (prmOK pH974 974 && ptTest pH974 (runFrom pH974 (fmask pH974) (cmask pH974) (hmask pH974) 1 973 (true, (init pH974), (init pH974))) 974 487 true) = true := by
  decide +kernel
theorem H974_ok : RunOK pH974 974 (runFrom pH974 (fmask pH974) (cmask pH974) (hmask pH974) 1 973 (true, (init pH974), (init pH974))) ∧ ptTest pH974 (runFrom pH974 (fmask pH974) (cmask pH974) (hmask pH974) 1 973 (true, (init pH974), (init pH974))) 974 487 true = true :=
  fin_run (runOK_init (prmOK_of_and H974_fin) true) (by decide) rfl H974_fin ptTest_fst
theorem I974_fin : (prmOK pI974 974 && intTest pI974 (runFrom pI974 (fmask pI974) (cmask pI974) (hmask pI974) 1 973 (true, (init pI974), (init pI974))) 974 18 true) = true := by
  decide +kernel
theorem I974_ok : RunOK pI974 974 (runFrom pI974 (fmask pI974) (cmask pI974) (hmask pI974) 1 973 (true, (init pI974), (init pI974))) ∧ intTest pI974 (runFrom pI974 (fmask pI974) (cmask pI974) (hmask pI974) 1 973 (true, (init pI974), (init pI974))) 974 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I974_fin) true) (by decide) rfl I974_fin intTest_fst
theorem link974 : linkOK pL974 pH974 pI974 = true := by decide +kernel
theorem cvx974 : ConvexBetweenHumps 974 :=
  cvx_of L974_ok H974_ok I974_ok link974 (by decide)
theorem cenlink974 : cenLinkOK pI974 974 = true := by decide +kernel
theorem cen974 : CenterUniqueMin 974 ∧ DipHyp 974 ∧ OnePointHyps 974 :=
  cen_of L974_ok H974_ok I974_ok link974 cenlink974

/-! ### `N = 975` -/

def pL975 : Prm := ⟨76, 36, 37, 977, 11, 18446744073709551616, 176075325166198930, 176075325166198930⟩
def pH975 : Prm := ⟨76, 36, 37, 977, 11, 18446744073709551616, 176077524189454482, 176077524189454482⟩
def pI975 : Prm := ⟨65, 31, 31, 977, 11, 18446744073709551616, 176075325166198930, 176077524189454482⟩
theorem L975_fin : (prmOK pL975 975 && ptTest pL975 (runFrom pL975 (fmask pL975) (cmask pL975) (hmask pL975) 1 974 (true, (init pL975), (init pL975))) 975 488 false) = true := by
  decide +kernel
theorem L975_ok : RunOK pL975 975 (runFrom pL975 (fmask pL975) (cmask pL975) (hmask pL975) 1 974 (true, (init pL975), (init pL975))) ∧ ptTest pL975 (runFrom pL975 (fmask pL975) (cmask pL975) (hmask pL975) 1 974 (true, (init pL975), (init pL975))) 975 488 false = true :=
  fin_run (runOK_init (prmOK_of_and L975_fin) true) (by decide) rfl L975_fin ptTest_fst
theorem H975_fin : (prmOK pH975 975 && ptTest pH975 (runFrom pH975 (fmask pH975) (cmask pH975) (hmask pH975) 1 974 (true, (init pH975), (init pH975))) 975 488 true) = true := by
  decide +kernel
theorem H975_ok : RunOK pH975 975 (runFrom pH975 (fmask pH975) (cmask pH975) (hmask pH975) 1 974 (true, (init pH975), (init pH975))) ∧ ptTest pH975 (runFrom pH975 (fmask pH975) (cmask pH975) (hmask pH975) 1 974 (true, (init pH975), (init pH975))) 975 488 true = true :=
  fin_run (runOK_init (prmOK_of_and H975_fin) true) (by decide) rfl H975_fin ptTest_fst
theorem I975_fin : (prmOK pI975 975 && intTest pI975 (runFrom pI975 (fmask pI975) (cmask pI975) (hmask pI975) 1 974 (true, (init pI975), (init pI975))) 975 18 false) = true := by
  decide +kernel
theorem I975_ok : RunOK pI975 975 (runFrom pI975 (fmask pI975) (cmask pI975) (hmask pI975) 1 974 (true, (init pI975), (init pI975))) ∧ intTest pI975 (runFrom pI975 (fmask pI975) (cmask pI975) (hmask pI975) 1 974 (true, (init pI975), (init pI975))) 975 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I975_fin) true) (by decide) rfl I975_fin intTest_fst
theorem link975 : linkOK pL975 pH975 pI975 = true := by decide +kernel
theorem cvx975 : ConvexBetweenHumps 975 :=
  cvx_of L975_ok H975_ok I975_ok link975 (by decide)

/-! ### `N = 976` -/

def pL976 : Prm := ⟨76, 36, 37, 978, 11, 18446744073709551616, 175931520611682522, 175931520611682522⟩
def pH976 : Prm := ⟨76, 36, 37, 978, 11, 18446744073709551616, 175933719634938074, 175933719634938074⟩
def pI976 : Prm := ⟨65, 31, 31, 978, 11, 18446744073709551616, 175931520611682522, 175933719634938074⟩
theorem L976_fin : (prmOK pL976 976 && ptTest pL976 (runFrom pL976 (fmask pL976) (cmask pL976) (hmask pL976) 1 975 (true, (init pL976), (init pL976))) 976 488 false) = true := by
  decide +kernel
theorem L976_ok : RunOK pL976 976 (runFrom pL976 (fmask pL976) (cmask pL976) (hmask pL976) 1 975 (true, (init pL976), (init pL976))) ∧ ptTest pL976 (runFrom pL976 (fmask pL976) (cmask pL976) (hmask pL976) 1 975 (true, (init pL976), (init pL976))) 976 488 false = true :=
  fin_run (runOK_init (prmOK_of_and L976_fin) true) (by decide) rfl L976_fin ptTest_fst
theorem H976_fin : (prmOK pH976 976 && ptTest pH976 (runFrom pH976 (fmask pH976) (cmask pH976) (hmask pH976) 1 975 (true, (init pH976), (init pH976))) 976 488 true) = true := by
  decide +kernel
theorem H976_ok : RunOK pH976 976 (runFrom pH976 (fmask pH976) (cmask pH976) (hmask pH976) 1 975 (true, (init pH976), (init pH976))) ∧ ptTest pH976 (runFrom pH976 (fmask pH976) (cmask pH976) (hmask pH976) 1 975 (true, (init pH976), (init pH976))) 976 488 true = true :=
  fin_run (runOK_init (prmOK_of_and H976_fin) true) (by decide) rfl H976_fin ptTest_fst
theorem I976_fin : (prmOK pI976 976 && intTest pI976 (runFrom pI976 (fmask pI976) (cmask pI976) (hmask pI976) 1 975 (true, (init pI976), (init pI976))) 976 18 true) = true := by
  decide +kernel
theorem I976_ok : RunOK pI976 976 (runFrom pI976 (fmask pI976) (cmask pI976) (hmask pI976) 1 975 (true, (init pI976), (init pI976))) ∧ intTest pI976 (runFrom pI976 (fmask pI976) (cmask pI976) (hmask pI976) 1 975 (true, (init pI976), (init pI976))) 976 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I976_fin) true) (by decide) rfl I976_fin intTest_fst
theorem link976 : linkOK pL976 pH976 pI976 = true := by decide +kernel
theorem cvx976 : ConvexBetweenHumps 976 :=
  cvx_of L976_ok H976_ok I976_ok link976 (by decide)
theorem cenlink976 : cenLinkOK pI976 976 = true := by decide +kernel
theorem cen976 : CenterUniqueMin 976 ∧ DipHyp 976 ∧ OnePointHyps 976 :=
  cen_of L976_ok H976_ok I976_ok link976 cenlink976

/-! ### `N = 977` -/

def pL977 : Prm := ⟨76, 36, 37, 979, 11, 18446744073709551616, 175787848714694064, 175787848714694064⟩
def pH977 : Prm := ⟨76, 36, 37, 979, 11, 18446744073709551616, 175790047737949616, 175790047737949616⟩
def pI977 : Prm := ⟨65, 31, 31, 979, 11, 18446744073709551616, 175787848714694064, 175790047737949616⟩
theorem L977_fin : (prmOK pL977 977 && ptTest pL977 (runFrom pL977 (fmask pL977) (cmask pL977) (hmask pL977) 1 976 (true, (init pL977), (init pL977))) 977 489 false) = true := by
  decide +kernel
theorem L977_ok : RunOK pL977 977 (runFrom pL977 (fmask pL977) (cmask pL977) (hmask pL977) 1 976 (true, (init pL977), (init pL977))) ∧ ptTest pL977 (runFrom pL977 (fmask pL977) (cmask pL977) (hmask pL977) 1 976 (true, (init pL977), (init pL977))) 977 489 false = true :=
  fin_run (runOK_init (prmOK_of_and L977_fin) true) (by decide) rfl L977_fin ptTest_fst
theorem H977_fin : (prmOK pH977 977 && ptTest pH977 (runFrom pH977 (fmask pH977) (cmask pH977) (hmask pH977) 1 976 (true, (init pH977), (init pH977))) 977 489 true) = true := by
  decide +kernel
theorem H977_ok : RunOK pH977 977 (runFrom pH977 (fmask pH977) (cmask pH977) (hmask pH977) 1 976 (true, (init pH977), (init pH977))) ∧ ptTest pH977 (runFrom pH977 (fmask pH977) (cmask pH977) (hmask pH977) 1 976 (true, (init pH977), (init pH977))) 977 489 true = true :=
  fin_run (runOK_init (prmOK_of_and H977_fin) true) (by decide) rfl H977_fin ptTest_fst
theorem I977_fin : (prmOK pI977 977 && intTest pI977 (runFrom pI977 (fmask pI977) (cmask pI977) (hmask pI977) 1 976 (true, (init pI977), (init pI977))) 977 18 false) = true := by
  decide +kernel
theorem I977_ok : RunOK pI977 977 (runFrom pI977 (fmask pI977) (cmask pI977) (hmask pI977) 1 976 (true, (init pI977), (init pI977))) ∧ intTest pI977 (runFrom pI977 (fmask pI977) (cmask pI977) (hmask pI977) 1 976 (true, (init pI977), (init pI977))) 977 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I977_fin) true) (by decide) rfl I977_fin intTest_fst
theorem link977 : linkOK pL977 pH977 pI977 = true := by decide +kernel
theorem cvx977 : ConvexBetweenHumps 977 :=
  cvx_of L977_ok H977_ok I977_ok link977 (by decide)

/-! ### `N = 978` -/

def pL978 : Prm := ⟨76, 36, 37, 980, 11, 18446744073709551616, 175644557359167770, 175644557359167770⟩
def pH978 : Prm := ⟨76, 36, 37, 980, 11, 18446744073709551616, 175646756382423322, 175646756382423322⟩
def pI978 : Prm := ⟨65, 31, 31, 980, 11, 18446744073709551616, 175644557359167770, 175646756382423322⟩
theorem L978_fin : (prmOK pL978 978 && ptTest pL978 (runFrom pL978 (fmask pL978) (cmask pL978) (hmask pL978) 1 977 (true, (init pL978), (init pL978))) 978 489 false) = true := by
  decide +kernel
theorem L978_ok : RunOK pL978 978 (runFrom pL978 (fmask pL978) (cmask pL978) (hmask pL978) 1 977 (true, (init pL978), (init pL978))) ∧ ptTest pL978 (runFrom pL978 (fmask pL978) (cmask pL978) (hmask pL978) 1 977 (true, (init pL978), (init pL978))) 978 489 false = true :=
  fin_run (runOK_init (prmOK_of_and L978_fin) true) (by decide) rfl L978_fin ptTest_fst
theorem H978_fin : (prmOK pH978 978 && ptTest pH978 (runFrom pH978 (fmask pH978) (cmask pH978) (hmask pH978) 1 977 (true, (init pH978), (init pH978))) 978 489 true) = true := by
  decide +kernel
theorem H978_ok : RunOK pH978 978 (runFrom pH978 (fmask pH978) (cmask pH978) (hmask pH978) 1 977 (true, (init pH978), (init pH978))) ∧ ptTest pH978 (runFrom pH978 (fmask pH978) (cmask pH978) (hmask pH978) 1 977 (true, (init pH978), (init pH978))) 978 489 true = true :=
  fin_run (runOK_init (prmOK_of_and H978_fin) true) (by decide) rfl H978_fin ptTest_fst
theorem I978_fin : (prmOK pI978 978 && intTest pI978 (runFrom pI978 (fmask pI978) (cmask pI978) (hmask pI978) 1 977 (true, (init pI978), (init pI978))) 978 18 true) = true := by
  decide +kernel
theorem I978_ok : RunOK pI978 978 (runFrom pI978 (fmask pI978) (cmask pI978) (hmask pI978) 1 977 (true, (init pI978), (init pI978))) ∧ intTest pI978 (runFrom pI978 (fmask pI978) (cmask pI978) (hmask pI978) 1 977 (true, (init pI978), (init pI978))) 978 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I978_fin) true) (by decide) rfl I978_fin intTest_fst
theorem link978 : linkOK pL978 pH978 pI978 = true := by decide +kernel
theorem cvx978 : ConvexBetweenHumps 978 :=
  cvx_of L978_ok H978_ok I978_ok link978 (by decide)
theorem cenlink978 : cenLinkOK pI978 978 = true := by decide +kernel
theorem cen978 : CenterUniqueMin 978 ∧ DipHyp 978 ∧ OnePointHyps 978 :=
  cen_of L978_ok H978_ok I978_ok link978 cenlink978

/-! ### `N = 979` -/

def pL979 : Prm := ⟨76, 36, 37, 981, 11, 18446744073709551616, 175501398014279005, 175501398014279005⟩
def pH979 : Prm := ⟨76, 36, 37, 981, 11, 18446744073709551616, 175503597037534557, 175503597037534557⟩
def pI979 : Prm := ⟨65, 31, 31, 981, 11, 18446744073709551616, 175501398014279005, 175503597037534557⟩
theorem L979_fin : (prmOK pL979 979 && ptTest pL979 (runFrom pL979 (fmask pL979) (cmask pL979) (hmask pL979) 1 978 (true, (init pL979), (init pL979))) 979 490 false) = true := by
  decide +kernel
theorem L979_ok : RunOK pL979 979 (runFrom pL979 (fmask pL979) (cmask pL979) (hmask pL979) 1 978 (true, (init pL979), (init pL979))) ∧ ptTest pL979 (runFrom pL979 (fmask pL979) (cmask pL979) (hmask pL979) 1 978 (true, (init pL979), (init pL979))) 979 490 false = true :=
  fin_run (runOK_init (prmOK_of_and L979_fin) true) (by decide) rfl L979_fin ptTest_fst
theorem H979_fin : (prmOK pH979 979 && ptTest pH979 (runFrom pH979 (fmask pH979) (cmask pH979) (hmask pH979) 1 978 (true, (init pH979), (init pH979))) 979 490 true) = true := by
  decide +kernel
theorem H979_ok : RunOK pH979 979 (runFrom pH979 (fmask pH979) (cmask pH979) (hmask pH979) 1 978 (true, (init pH979), (init pH979))) ∧ ptTest pH979 (runFrom pH979 (fmask pH979) (cmask pH979) (hmask pH979) 1 978 (true, (init pH979), (init pH979))) 979 490 true = true :=
  fin_run (runOK_init (prmOK_of_and H979_fin) true) (by decide) rfl H979_fin ptTest_fst
theorem I979_fin : (prmOK pI979 979 && intTest pI979 (runFrom pI979 (fmask pI979) (cmask pI979) (hmask pI979) 1 978 (true, (init pI979), (init pI979))) 979 18 false) = true := by
  decide +kernel
theorem I979_ok : RunOK pI979 979 (runFrom pI979 (fmask pI979) (cmask pI979) (hmask pI979) 1 978 (true, (init pI979), (init pI979))) ∧ intTest pI979 (runFrom pI979 (fmask pI979) (cmask pI979) (hmask pI979) 1 978 (true, (init pI979), (init pI979))) 979 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I979_fin) true) (by decide) rfl I979_fin intTest_fst
theorem link979 : linkOK pL979 pH979 pI979 = true := by decide +kernel
theorem cvx979 : ConvexBetweenHumps 979 :=
  cvx_of L979_ok H979_ok I979_ok link979 (by decide)

/-! ### `N = 980` -/

def pL980 : Prm := ⟨76, 36, 37, 982, 11, 18446744073709551616, 175358617020707376, 175358617020707376⟩
def pH980 : Prm := ⟨76, 36, 37, 982, 11, 18446744073709551616, 175360816043962928, 175360816043962928⟩
def pI980 : Prm := ⟨65, 31, 31, 982, 11, 18446744073709551616, 175358617020707376, 175360816043962928⟩
theorem L980_fin : (prmOK pL980 980 && ptTest pL980 (runFrom pL980 (fmask pL980) (cmask pL980) (hmask pL980) 1 979 (true, (init pL980), (init pL980))) 980 490 false) = true := by
  decide +kernel
theorem L980_ok : RunOK pL980 980 (runFrom pL980 (fmask pL980) (cmask pL980) (hmask pL980) 1 979 (true, (init pL980), (init pL980))) ∧ ptTest pL980 (runFrom pL980 (fmask pL980) (cmask pL980) (hmask pL980) 1 979 (true, (init pL980), (init pL980))) 980 490 false = true :=
  fin_run (runOK_init (prmOK_of_and L980_fin) true) (by decide) rfl L980_fin ptTest_fst
theorem H980_fin : (prmOK pH980 980 && ptTest pH980 (runFrom pH980 (fmask pH980) (cmask pH980) (hmask pH980) 1 979 (true, (init pH980), (init pH980))) 980 490 true) = true := by
  decide +kernel
theorem H980_ok : RunOK pH980 980 (runFrom pH980 (fmask pH980) (cmask pH980) (hmask pH980) 1 979 (true, (init pH980), (init pH980))) ∧ ptTest pH980 (runFrom pH980 (fmask pH980) (cmask pH980) (hmask pH980) 1 979 (true, (init pH980), (init pH980))) 980 490 true = true :=
  fin_run (runOK_init (prmOK_of_and H980_fin) true) (by decide) rfl H980_fin ptTest_fst
theorem I980_fin : (prmOK pI980 980 && intTest pI980 (runFrom pI980 (fmask pI980) (cmask pI980) (hmask pI980) 1 979 (true, (init pI980), (init pI980))) 980 18 true) = true := by
  decide +kernel
theorem I980_ok : RunOK pI980 980 (runFrom pI980 (fmask pI980) (cmask pI980) (hmask pI980) 1 979 (true, (init pI980), (init pI980))) ∧ intTest pI980 (runFrom pI980 (fmask pI980) (cmask pI980) (hmask pI980) 1 979 (true, (init pI980), (init pI980))) 980 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I980_fin) true) (by decide) rfl I980_fin intTest_fst
theorem link980 : linkOK pL980 pH980 pI980 = true := by decide +kernel
theorem cvx980 : ConvexBetweenHumps 980 :=
  cvx_of L980_ok H980_ok I980_ok link980 (by decide)
theorem cenlink980 : cenLinkOK pI980 980 = true := by decide +kernel
theorem cen980 : CenterUniqueMin 980 ∧ DipHyp 980 ∧ OnePointHyps 980 :=
  cen_of L980_ok H980_ok I980_ok link980 cenlink980

/-! ### `N = 981` -/

def pL981 : Prm := ⟨76, 36, 37, 983, 11, 18446744073709551616, 175215967395162498, 175215967395162498⟩
def pH981 : Prm := ⟨76, 36, 37, 983, 11, 18446744073709551616, 175218166418418050, 175218166418418050⟩
def pI981 : Prm := ⟨65, 31, 31, 983, 11, 18446744073709551616, 175215967395162498, 175218166418418050⟩
theorem L981_fin : (prmOK pL981 981 && ptTest pL981 (runFrom pL981 (fmask pL981) (cmask pL981) (hmask pL981) 1 980 (true, (init pL981), (init pL981))) 981 491 false) = true := by
  decide +kernel
theorem L981_ok : RunOK pL981 981 (runFrom pL981 (fmask pL981) (cmask pL981) (hmask pL981) 1 980 (true, (init pL981), (init pL981))) ∧ ptTest pL981 (runFrom pL981 (fmask pL981) (cmask pL981) (hmask pL981) 1 980 (true, (init pL981), (init pL981))) 981 491 false = true :=
  fin_run (runOK_init (prmOK_of_and L981_fin) true) (by decide) rfl L981_fin ptTest_fst
theorem H981_fin : (prmOK pH981 981 && ptTest pH981 (runFrom pH981 (fmask pH981) (cmask pH981) (hmask pH981) 1 980 (true, (init pH981), (init pH981))) 981 491 true) = true := by
  decide +kernel
theorem H981_ok : RunOK pH981 981 (runFrom pH981 (fmask pH981) (cmask pH981) (hmask pH981) 1 980 (true, (init pH981), (init pH981))) ∧ ptTest pH981 (runFrom pH981 (fmask pH981) (cmask pH981) (hmask pH981) 1 980 (true, (init pH981), (init pH981))) 981 491 true = true :=
  fin_run (runOK_init (prmOK_of_and H981_fin) true) (by decide) rfl H981_fin ptTest_fst
theorem I981_fin : (prmOK pI981 981 && intTest pI981 (runFrom pI981 (fmask pI981) (cmask pI981) (hmask pI981) 1 980 (true, (init pI981), (init pI981))) 981 18 false) = true := by
  decide +kernel
theorem I981_ok : RunOK pI981 981 (runFrom pI981 (fmask pI981) (cmask pI981) (hmask pI981) 1 980 (true, (init pI981), (init pI981))) ∧ intTest pI981 (runFrom pI981 (fmask pI981) (cmask pI981) (hmask pI981) 1 980 (true, (init pI981), (init pI981))) 981 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I981_fin) true) (by decide) rfl I981_fin intTest_fst
theorem link981 : linkOK pL981 pH981 pI981 = true := by decide +kernel
theorem cvx981 : ConvexBetweenHumps 981 :=
  cvx_of L981_ok H981_ok I981_ok link981 (by decide)

/-! ### `N = 982` -/

def pL982 : Prm := ⟨76, 36, 37, 984, 11, 18446744073709551616, 175073693947779176, 175073693947779176⟩
def pH982 : Prm := ⟨76, 36, 37, 984, 11, 18446744073709551616, 175075892971034728, 175075892971034728⟩
def pI982 : Prm := ⟨65, 31, 31, 984, 11, 18446744073709551616, 175073693947779176, 175075892971034728⟩
theorem L982_fin : (prmOK pL982 982 && ptTest pL982 (runFrom pL982 (fmask pL982) (cmask pL982) (hmask pL982) 1 981 (true, (init pL982), (init pL982))) 982 491 false) = true := by
  decide +kernel
theorem L982_ok : RunOK pL982 982 (runFrom pL982 (fmask pL982) (cmask pL982) (hmask pL982) 1 981 (true, (init pL982), (init pL982))) ∧ ptTest pL982 (runFrom pL982 (fmask pL982) (cmask pL982) (hmask pL982) 1 981 (true, (init pL982), (init pL982))) 982 491 false = true :=
  fin_run (runOK_init (prmOK_of_and L982_fin) true) (by decide) rfl L982_fin ptTest_fst
theorem H982_fin : (prmOK pH982 982 && ptTest pH982 (runFrom pH982 (fmask pH982) (cmask pH982) (hmask pH982) 1 981 (true, (init pH982), (init pH982))) 982 491 true) = true := by
  decide +kernel
theorem H982_ok : RunOK pH982 982 (runFrom pH982 (fmask pH982) (cmask pH982) (hmask pH982) 1 981 (true, (init pH982), (init pH982))) ∧ ptTest pH982 (runFrom pH982 (fmask pH982) (cmask pH982) (hmask pH982) 1 981 (true, (init pH982), (init pH982))) 982 491 true = true :=
  fin_run (runOK_init (prmOK_of_and H982_fin) true) (by decide) rfl H982_fin ptTest_fst
theorem I982_fin : (prmOK pI982 982 && intTest pI982 (runFrom pI982 (fmask pI982) (cmask pI982) (hmask pI982) 1 981 (true, (init pI982), (init pI982))) 982 18 true) = true := by
  decide +kernel
theorem I982_ok : RunOK pI982 982 (runFrom pI982 (fmask pI982) (cmask pI982) (hmask pI982) 1 981 (true, (init pI982), (init pI982))) ∧ intTest pI982 (runFrom pI982 (fmask pI982) (cmask pI982) (hmask pI982) 1 981 (true, (init pI982), (init pI982))) 982 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I982_fin) true) (by decide) rfl I982_fin intTest_fst
theorem link982 : linkOK pL982 pH982 pI982 = true := by decide +kernel
theorem cvx982 : ConvexBetweenHumps 982 :=
  cvx_of L982_ok H982_ok I982_ok link982 (by decide)
theorem cenlink982 : cenLinkOK pI982 982 = true := by decide +kernel
theorem cen982 : CenterUniqueMin 982 ∧ DipHyp 982 ∧ OnePointHyps 982 :=
  cen_of L982_ok H982_ok I982_ok link982 cenlink982

/-! ### `N = 983` -/

def pL983 : Prm := ⟨76, 36, 37, 985, 11, 18446744073709551616, 174931551230036134, 174931551230036134⟩
def pH983 : Prm := ⟨76, 36, 37, 985, 11, 18446744073709551616, 174933750253291686, 174933750253291686⟩
def pI983 : Prm := ⟨65, 31, 31, 985, 11, 18446744073709551616, 174931551230036134, 174933750253291686⟩
theorem L983_fin : (prmOK pL983 983 && ptTest pL983 (runFrom pL983 (fmask pL983) (cmask pL983) (hmask pL983) 1 982 (true, (init pL983), (init pL983))) 983 492 false) = true := by
  decide +kernel
theorem L983_ok : RunOK pL983 983 (runFrom pL983 (fmask pL983) (cmask pL983) (hmask pL983) 1 982 (true, (init pL983), (init pL983))) ∧ ptTest pL983 (runFrom pL983 (fmask pL983) (cmask pL983) (hmask pL983) 1 982 (true, (init pL983), (init pL983))) 983 492 false = true :=
  fin_run (runOK_init (prmOK_of_and L983_fin) true) (by decide) rfl L983_fin ptTest_fst
theorem H983_fin : (prmOK pH983 983 && ptTest pH983 (runFrom pH983 (fmask pH983) (cmask pH983) (hmask pH983) 1 982 (true, (init pH983), (init pH983))) 983 492 true) = true := by
  decide +kernel
theorem H983_ok : RunOK pH983 983 (runFrom pH983 (fmask pH983) (cmask pH983) (hmask pH983) 1 982 (true, (init pH983), (init pH983))) ∧ ptTest pH983 (runFrom pH983 (fmask pH983) (cmask pH983) (hmask pH983) 1 982 (true, (init pH983), (init pH983))) 983 492 true = true :=
  fin_run (runOK_init (prmOK_of_and H983_fin) true) (by decide) rfl H983_fin ptTest_fst
theorem I983_fin : (prmOK pI983 983 && intTest pI983 (runFrom pI983 (fmask pI983) (cmask pI983) (hmask pI983) 1 982 (true, (init pI983), (init pI983))) 983 18 false) = true := by
  decide +kernel
theorem I983_ok : RunOK pI983 983 (runFrom pI983 (fmask pI983) (cmask pI983) (hmask pI983) 1 982 (true, (init pI983), (init pI983))) ∧ intTest pI983 (runFrom pI983 (fmask pI983) (cmask pI983) (hmask pI983) 1 982 (true, (init pI983), (init pI983))) 983 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I983_fin) true) (by decide) rfl I983_fin intTest_fst
theorem link983 : linkOK pL983 pH983 pI983 = true := by decide +kernel
theorem cvx983 : ConvexBetweenHumps 983 :=
  cvx_of L983_ok H983_ok I983_ok link983 (by decide)

/-! ### `N = 984` -/

def pL984 : Prm := ⟨76, 36, 37, 986, 11, 18446744073709551616, 174789782534140946, 174789782534140946⟩
def pH984 : Prm := ⟨76, 36, 37, 986, 11, 18446744073709551616, 174791981557396498, 174791981557396498⟩
def pI984 : Prm := ⟨65, 31, 31, 986, 11, 18446744073709551616, 174789782534140946, 174791981557396498⟩
theorem L984_fin : (prmOK pL984 984 && ptTest pL984 (runFrom pL984 (fmask pL984) (cmask pL984) (hmask pL984) 1 983 (true, (init pL984), (init pL984))) 984 492 false) = true := by
  decide +kernel
theorem L984_ok : RunOK pL984 984 (runFrom pL984 (fmask pL984) (cmask pL984) (hmask pL984) 1 983 (true, (init pL984), (init pL984))) ∧ ptTest pL984 (runFrom pL984 (fmask pL984) (cmask pL984) (hmask pL984) 1 983 (true, (init pL984), (init pL984))) 984 492 false = true :=
  fin_run (runOK_init (prmOK_of_and L984_fin) true) (by decide) rfl L984_fin ptTest_fst
theorem H984_fin : (prmOK pH984 984 && ptTest pH984 (runFrom pH984 (fmask pH984) (cmask pH984) (hmask pH984) 1 983 (true, (init pH984), (init pH984))) 984 492 true) = true := by
  decide +kernel
theorem H984_ok : RunOK pH984 984 (runFrom pH984 (fmask pH984) (cmask pH984) (hmask pH984) 1 983 (true, (init pH984), (init pH984))) ∧ ptTest pH984 (runFrom pH984 (fmask pH984) (cmask pH984) (hmask pH984) 1 983 (true, (init pH984), (init pH984))) 984 492 true = true :=
  fin_run (runOK_init (prmOK_of_and H984_fin) true) (by decide) rfl H984_fin ptTest_fst
theorem I984_fin : (prmOK pI984 984 && intTest pI984 (runFrom pI984 (fmask pI984) (cmask pI984) (hmask pI984) 1 983 (true, (init pI984), (init pI984))) 984 18 true) = true := by
  decide +kernel
theorem I984_ok : RunOK pI984 984 (runFrom pI984 (fmask pI984) (cmask pI984) (hmask pI984) 1 983 (true, (init pI984), (init pI984))) ∧ intTest pI984 (runFrom pI984 (fmask pI984) (cmask pI984) (hmask pI984) 1 983 (true, (init pI984), (init pI984))) 984 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I984_fin) true) (by decide) rfl I984_fin intTest_fst
theorem link984 : linkOK pL984 pH984 pI984 = true := by decide +kernel
theorem cvx984 : ConvexBetweenHumps 984 :=
  cvx_of L984_ok H984_ok I984_ok link984 (by decide)
theorem cenlink984 : cenLinkOK pI984 984 = true := by decide +kernel
theorem cen984 : CenterUniqueMin 984 ∧ DipHyp 984 ∧ OnePointHyps 984 :=
  cen_of L984_ok H984_ok I984_ok link984 cenlink984

/-! ### `N = 985` -/

def pL985 : Prm := ⟨76, 36, 37, 987, 11, 18446744073709551616, 174648143933668530, 174648143933668530⟩
def pH985 : Prm := ⟨76, 36, 37, 987, 11, 18446744073709551616, 174650342956924082, 174650342956924082⟩
def pI985 : Prm := ⟨65, 31, 31, 987, 11, 18446744073709551616, 174648143933668530, 174650342956924082⟩
theorem L985_fin : (prmOK pL985 985 && ptTest pL985 (runFrom pL985 (fmask pL985) (cmask pL985) (hmask pL985) 1 984 (true, (init pL985), (init pL985))) 985 493 false) = true := by
  decide +kernel
theorem L985_ok : RunOK pL985 985 (runFrom pL985 (fmask pL985) (cmask pL985) (hmask pL985) 1 984 (true, (init pL985), (init pL985))) ∧ ptTest pL985 (runFrom pL985 (fmask pL985) (cmask pL985) (hmask pL985) 1 984 (true, (init pL985), (init pL985))) 985 493 false = true :=
  fin_run (runOK_init (prmOK_of_and L985_fin) true) (by decide) rfl L985_fin ptTest_fst
theorem H985_fin : (prmOK pH985 985 && ptTest pH985 (runFrom pH985 (fmask pH985) (cmask pH985) (hmask pH985) 1 984 (true, (init pH985), (init pH985))) 985 493 true) = true := by
  decide +kernel
theorem H985_ok : RunOK pH985 985 (runFrom pH985 (fmask pH985) (cmask pH985) (hmask pH985) 1 984 (true, (init pH985), (init pH985))) ∧ ptTest pH985 (runFrom pH985 (fmask pH985) (cmask pH985) (hmask pH985) 1 984 (true, (init pH985), (init pH985))) 985 493 true = true :=
  fin_run (runOK_init (prmOK_of_and H985_fin) true) (by decide) rfl H985_fin ptTest_fst
theorem I985_fin : (prmOK pI985 985 && intTest pI985 (runFrom pI985 (fmask pI985) (cmask pI985) (hmask pI985) 1 984 (true, (init pI985), (init pI985))) 985 18 false) = true := by
  decide +kernel
theorem I985_ok : RunOK pI985 985 (runFrom pI985 (fmask pI985) (cmask pI985) (hmask pI985) 1 984 (true, (init pI985), (init pI985))) ∧ intTest pI985 (runFrom pI985 (fmask pI985) (cmask pI985) (hmask pI985) 1 984 (true, (init pI985), (init pI985))) 985 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I985_fin) true) (by decide) rfl I985_fin intTest_fst
theorem link985 : linkOK pL985 pH985 pI985 = true := by decide +kernel
theorem cvx985 : ConvexBetweenHumps 985 :=
  cvx_of L985_ok H985_ok I985_ok link985 (by decide)

/-! ### `N = 986` -/

def pL986 : Prm := ⟨76, 36, 37, 988, 11, 18446744073709551616, 174506877215424569, 174506877215424569⟩
def pH986 : Prm := ⟨76, 36, 37, 988, 11, 18446744073709551616, 174509076238680121, 174509076238680121⟩
def pI986 : Prm := ⟨65, 31, 31, 988, 11, 18446744073709551616, 174506877215424569, 174509076238680121⟩
theorem L986_fin : (prmOK pL986 986 && ptTest pL986 (runFrom pL986 (fmask pL986) (cmask pL986) (hmask pL986) 1 985 (true, (init pL986), (init pL986))) 986 493 false) = true := by
  decide +kernel
theorem L986_ok : RunOK pL986 986 (runFrom pL986 (fmask pL986) (cmask pL986) (hmask pL986) 1 985 (true, (init pL986), (init pL986))) ∧ ptTest pL986 (runFrom pL986 (fmask pL986) (cmask pL986) (hmask pL986) 1 985 (true, (init pL986), (init pL986))) 986 493 false = true :=
  fin_run (runOK_init (prmOK_of_and L986_fin) true) (by decide) rfl L986_fin ptTest_fst
theorem H986_fin : (prmOK pH986 986 && ptTest pH986 (runFrom pH986 (fmask pH986) (cmask pH986) (hmask pH986) 1 985 (true, (init pH986), (init pH986))) 986 493 true) = true := by
  decide +kernel
theorem H986_ok : RunOK pH986 986 (runFrom pH986 (fmask pH986) (cmask pH986) (hmask pH986) 1 985 (true, (init pH986), (init pH986))) ∧ ptTest pH986 (runFrom pH986 (fmask pH986) (cmask pH986) (hmask pH986) 1 985 (true, (init pH986), (init pH986))) 986 493 true = true :=
  fin_run (runOK_init (prmOK_of_and H986_fin) true) (by decide) rfl H986_fin ptTest_fst
theorem I986_fin : (prmOK pI986 986 && intTest pI986 (runFrom pI986 (fmask pI986) (cmask pI986) (hmask pI986) 1 985 (true, (init pI986), (init pI986))) 986 18 true) = true := by
  decide +kernel
theorem I986_ok : RunOK pI986 986 (runFrom pI986 (fmask pI986) (cmask pI986) (hmask pI986) 1 985 (true, (init pI986), (init pI986))) ∧ intTest pI986 (runFrom pI986 (fmask pI986) (cmask pI986) (hmask pI986) 1 985 (true, (init pI986), (init pI986))) 986 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I986_fin) true) (by decide) rfl I986_fin intTest_fst
theorem link986 : linkOK pL986 pH986 pI986 = true := by decide +kernel
theorem cvx986 : ConvexBetweenHumps 986 :=
  cvx_of L986_ok H986_ok I986_ok link986 (by decide)
theorem cenlink986 : cenLinkOK pI986 986 = true := by decide +kernel
theorem cen986 : CenterUniqueMin 986 ∧ DipHyp 986 ∧ OnePointHyps 986 :=
  cen_of L986_ok H986_ok I986_ok link986 cenlink986

/-! ### `N = 987` -/

def pL987 : Prm := ⟨76, 36, 37, 989, 11, 18446744073709551616, 174365739962517943, 174365739962517943⟩
def pH987 : Prm := ⟨76, 36, 37, 989, 11, 18446744073709551616, 174367938985773495, 174367938985773495⟩
def pI987 : Prm := ⟨65, 31, 31, 989, 11, 18446744073709551616, 174365739962517943, 174367938985773495⟩
theorem L987_fin : (prmOK pL987 987 && ptTest pL987 (runFrom pL987 (fmask pL987) (cmask pL987) (hmask pL987) 1 986 (true, (init pL987), (init pL987))) 987 494 false) = true := by
  decide +kernel
theorem L987_ok : RunOK pL987 987 (runFrom pL987 (fmask pL987) (cmask pL987) (hmask pL987) 1 986 (true, (init pL987), (init pL987))) ∧ ptTest pL987 (runFrom pL987 (fmask pL987) (cmask pL987) (hmask pL987) 1 986 (true, (init pL987), (init pL987))) 987 494 false = true :=
  fin_run (runOK_init (prmOK_of_and L987_fin) true) (by decide) rfl L987_fin ptTest_fst
theorem H987_fin : (prmOK pH987 987 && ptTest pH987 (runFrom pH987 (fmask pH987) (cmask pH987) (hmask pH987) 1 986 (true, (init pH987), (init pH987))) 987 494 true) = true := by
  decide +kernel
theorem H987_ok : RunOK pH987 987 (runFrom pH987 (fmask pH987) (cmask pH987) (hmask pH987) 1 986 (true, (init pH987), (init pH987))) ∧ ptTest pH987 (runFrom pH987 (fmask pH987) (cmask pH987) (hmask pH987) 1 986 (true, (init pH987), (init pH987))) 987 494 true = true :=
  fin_run (runOK_init (prmOK_of_and H987_fin) true) (by decide) rfl H987_fin ptTest_fst
theorem I987_fin : (prmOK pI987 987 && intTest pI987 (runFrom pI987 (fmask pI987) (cmask pI987) (hmask pI987) 1 986 (true, (init pI987), (init pI987))) 987 18 false) = true := by
  decide +kernel
theorem I987_ok : RunOK pI987 987 (runFrom pI987 (fmask pI987) (cmask pI987) (hmask pI987) 1 986 (true, (init pI987), (init pI987))) ∧ intTest pI987 (runFrom pI987 (fmask pI987) (cmask pI987) (hmask pI987) 1 986 (true, (init pI987), (init pI987))) 987 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I987_fin) true) (by decide) rfl I987_fin intTest_fst
theorem link987 : linkOK pL987 pH987 pI987 = true := by decide +kernel
theorem cvx987 : ConvexBetweenHumps 987 :=
  cvx_of L987_ok H987_ok I987_ok link987 (by decide)

/-! ### `N = 988` -/

def pL988 : Prm := ⟨76, 36, 37, 990, 11, 18446744073709551616, 174224972468730210, 174224972468730210⟩
def pH988 : Prm := ⟨76, 36, 37, 990, 11, 18446744073709551616, 174227171491985762, 174227171491985762⟩
def pI988 : Prm := ⟨65, 31, 31, 990, 11, 18446744073709551616, 174224972468730210, 174227171491985762⟩
theorem L988_fin : (prmOK pL988 988 && ptTest pL988 (runFrom pL988 (fmask pL988) (cmask pL988) (hmask pL988) 1 987 (true, (init pL988), (init pL988))) 988 494 false) = true := by
  decide +kernel
theorem L988_ok : RunOK pL988 988 (runFrom pL988 (fmask pL988) (cmask pL988) (hmask pL988) 1 987 (true, (init pL988), (init pL988))) ∧ ptTest pL988 (runFrom pL988 (fmask pL988) (cmask pL988) (hmask pL988) 1 987 (true, (init pL988), (init pL988))) 988 494 false = true :=
  fin_run (runOK_init (prmOK_of_and L988_fin) true) (by decide) rfl L988_fin ptTest_fst
theorem H988_fin : (prmOK pH988 988 && ptTest pH988 (runFrom pH988 (fmask pH988) (cmask pH988) (hmask pH988) 1 987 (true, (init pH988), (init pH988))) 988 494 true) = true := by
  decide +kernel
theorem H988_ok : RunOK pH988 988 (runFrom pH988 (fmask pH988) (cmask pH988) (hmask pH988) 1 987 (true, (init pH988), (init pH988))) ∧ ptTest pH988 (runFrom pH988 (fmask pH988) (cmask pH988) (hmask pH988) 1 987 (true, (init pH988), (init pH988))) 988 494 true = true :=
  fin_run (runOK_init (prmOK_of_and H988_fin) true) (by decide) rfl H988_fin ptTest_fst
theorem I988_fin : (prmOK pI988 988 && intTest pI988 (runFrom pI988 (fmask pI988) (cmask pI988) (hmask pI988) 1 987 (true, (init pI988), (init pI988))) 988 18 true) = true := by
  decide +kernel
theorem I988_ok : RunOK pI988 988 (runFrom pI988 (fmask pI988) (cmask pI988) (hmask pI988) 1 987 (true, (init pI988), (init pI988))) ∧ intTest pI988 (runFrom pI988 (fmask pI988) (cmask pI988) (hmask pI988) 1 987 (true, (init pI988), (init pI988))) 988 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I988_fin) true) (by decide) rfl I988_fin intTest_fst
theorem link988 : linkOK pL988 pH988 pI988 = true := by decide +kernel
theorem cvx988 : ConvexBetweenHumps 988 :=
  cvx_of L988_ok H988_ok I988_ok link988 (by decide)
theorem cenlink988 : cenLinkOK pI988 988 = true := by decide +kernel
theorem cen988 : CenterUniqueMin 988 ∧ DipHyp 988 ∧ OnePointHyps 988 :=
  cen_of L988_ok H988_ok I988_ok link988 cenlink988

/-! ### `N = 989` -/

def pL989 : Prm := ⟨76, 36, 37, 991, 11, 18446744073709551616, 174084333814363338, 174084333814363338⟩
def pH989 : Prm := ⟨76, 36, 37, 991, 11, 18446744073709551616, 174086532837618890, 174086532837618890⟩
def pI989 : Prm := ⟨65, 31, 31, 991, 11, 18446744073709551616, 174084333814363338, 174086532837618890⟩
theorem L989_fin : (prmOK pL989 989 && ptTest pL989 (runFrom pL989 (fmask pL989) (cmask pL989) (hmask pL989) 1 988 (true, (init pL989), (init pL989))) 989 495 false) = true := by
  decide +kernel
theorem L989_ok : RunOK pL989 989 (runFrom pL989 (fmask pL989) (cmask pL989) (hmask pL989) 1 988 (true, (init pL989), (init pL989))) ∧ ptTest pL989 (runFrom pL989 (fmask pL989) (cmask pL989) (hmask pL989) 1 988 (true, (init pL989), (init pL989))) 989 495 false = true :=
  fin_run (runOK_init (prmOK_of_and L989_fin) true) (by decide) rfl L989_fin ptTest_fst
theorem H989_fin : (prmOK pH989 989 && ptTest pH989 (runFrom pH989 (fmask pH989) (cmask pH989) (hmask pH989) 1 988 (true, (init pH989), (init pH989))) 989 495 true) = true := by
  decide +kernel
theorem H989_ok : RunOK pH989 989 (runFrom pH989 (fmask pH989) (cmask pH989) (hmask pH989) 1 988 (true, (init pH989), (init pH989))) ∧ ptTest pH989 (runFrom pH989 (fmask pH989) (cmask pH989) (hmask pH989) 1 988 (true, (init pH989), (init pH989))) 989 495 true = true :=
  fin_run (runOK_init (prmOK_of_and H989_fin) true) (by decide) rfl H989_fin ptTest_fst
theorem I989_fin : (prmOK pI989 989 && intTest pI989 (runFrom pI989 (fmask pI989) (cmask pI989) (hmask pI989) 1 988 (true, (init pI989), (init pI989))) 989 18 false) = true := by
  decide +kernel
theorem I989_ok : RunOK pI989 989 (runFrom pI989 (fmask pI989) (cmask pI989) (hmask pI989) 1 988 (true, (init pI989), (init pI989))) ∧ intTest pI989 (runFrom pI989 (fmask pI989) (cmask pI989) (hmask pI989) 1 988 (true, (init pI989), (init pI989))) 989 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I989_fin) true) (by decide) rfl I989_fin intTest_fst
theorem link989 : linkOK pL989 pH989 pI989 = true := by decide +kernel
theorem cvx989 : ConvexBetweenHumps 989 :=
  cvx_of L989_ok H989_ok I989_ok link989 (by decide)

/-! ### `N = 990` -/

def pL990 : Prm := ⟨76, 36, 37, 992, 11, 18446744073709551616, 173944062812294272, 173944062812294272⟩
def pH990 : Prm := ⟨76, 36, 37, 992, 11, 18446744073709551616, 173946261835549824, 173946261835549824⟩
def pI990 : Prm := ⟨64, 32, 29, 992, 11, 18446744073709551616, 173944062812294272, 173946261835549824⟩
theorem L990_fin : (prmOK pL990 990 && ptTest pL990 (runFrom pL990 (fmask pL990) (cmask pL990) (hmask pL990) 1 989 (true, (init pL990), (init pL990))) 990 495 false) = true := by
  decide +kernel
theorem L990_ok : RunOK pL990 990 (runFrom pL990 (fmask pL990) (cmask pL990) (hmask pL990) 1 989 (true, (init pL990), (init pL990))) ∧ ptTest pL990 (runFrom pL990 (fmask pL990) (cmask pL990) (hmask pL990) 1 989 (true, (init pL990), (init pL990))) 990 495 false = true :=
  fin_run (runOK_init (prmOK_of_and L990_fin) true) (by decide) rfl L990_fin ptTest_fst
theorem H990_fin : (prmOK pH990 990 && ptTest pH990 (runFrom pH990 (fmask pH990) (cmask pH990) (hmask pH990) 1 989 (true, (init pH990), (init pH990))) 990 495 true) = true := by
  decide +kernel
theorem H990_ok : RunOK pH990 990 (runFrom pH990 (fmask pH990) (cmask pH990) (hmask pH990) 1 989 (true, (init pH990), (init pH990))) ∧ ptTest pH990 (runFrom pH990 (fmask pH990) (cmask pH990) (hmask pH990) 1 989 (true, (init pH990), (init pH990))) 990 495 true = true :=
  fin_run (runOK_init (prmOK_of_and H990_fin) true) (by decide) rfl H990_fin ptTest_fst
theorem I990_fin : (prmOK pI990 990 && intTest pI990 (runFrom pI990 (fmask pI990) (cmask pI990) (hmask pI990) 1 989 (true, (init pI990), (init pI990))) 990 18 true) = true := by
  decide +kernel
theorem I990_ok : RunOK pI990 990 (runFrom pI990 (fmask pI990) (cmask pI990) (hmask pI990) 1 989 (true, (init pI990), (init pI990))) ∧ intTest pI990 (runFrom pI990 (fmask pI990) (cmask pI990) (hmask pI990) 1 989 (true, (init pI990), (init pI990))) 990 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I990_fin) true) (by decide) rfl I990_fin intTest_fst
theorem link990 : linkOK pL990 pH990 pI990 = true := by decide +kernel
theorem cvx990 : ConvexBetweenHumps 990 :=
  cvx_of L990_ok H990_ok I990_ok link990 (by decide)
theorem cenlink990 : cenLinkOK pI990 990 = true := by decide +kernel
theorem cen990 : CenterUniqueMin 990 ∧ DipHyp 990 ∧ OnePointHyps 990 :=
  cen_of L990_ok H990_ok I990_ok link990 cenlink990

/-! ### `N = 991` -/

def pL991 : Prm := ⟨76, 36, 37, 993, 11, 18446744073709551616, 173803920027806325, 173803920027806325⟩
def pH991 : Prm := ⟨76, 36, 37, 993, 11, 18446744073709551616, 173806119051061877, 173806119051061877⟩
def pI991 : Prm := ⟨65, 31, 31, 993, 11, 18446744073709551616, 173803920027806325, 173806119051061877⟩
theorem L991_fin : (prmOK pL991 991 && ptTest pL991 (runFrom pL991 (fmask pL991) (cmask pL991) (hmask pL991) 1 990 (true, (init pL991), (init pL991))) 991 496 false) = true := by
  decide +kernel
theorem L991_ok : RunOK pL991 991 (runFrom pL991 (fmask pL991) (cmask pL991) (hmask pL991) 1 990 (true, (init pL991), (init pL991))) ∧ ptTest pL991 (runFrom pL991 (fmask pL991) (cmask pL991) (hmask pL991) 1 990 (true, (init pL991), (init pL991))) 991 496 false = true :=
  fin_run (runOK_init (prmOK_of_and L991_fin) true) (by decide) rfl L991_fin ptTest_fst
theorem H991_fin : (prmOK pH991 991 && ptTest pH991 (runFrom pH991 (fmask pH991) (cmask pH991) (hmask pH991) 1 990 (true, (init pH991), (init pH991))) 991 496 true) = true := by
  decide +kernel
theorem H991_ok : RunOK pH991 991 (runFrom pH991 (fmask pH991) (cmask pH991) (hmask pH991) 1 990 (true, (init pH991), (init pH991))) ∧ ptTest pH991 (runFrom pH991 (fmask pH991) (cmask pH991) (hmask pH991) 1 990 (true, (init pH991), (init pH991))) 991 496 true = true :=
  fin_run (runOK_init (prmOK_of_and H991_fin) true) (by decide) rfl H991_fin ptTest_fst
theorem I991_fin : (prmOK pI991 991 && intTest pI991 (runFrom pI991 (fmask pI991) (cmask pI991) (hmask pI991) 1 990 (true, (init pI991), (init pI991))) 991 18 false) = true := by
  decide +kernel
theorem I991_ok : RunOK pI991 991 (runFrom pI991 (fmask pI991) (cmask pI991) (hmask pI991) 1 990 (true, (init pI991), (init pI991))) ∧ intTest pI991 (runFrom pI991 (fmask pI991) (cmask pI991) (hmask pI991) 1 990 (true, (init pI991), (init pI991))) 991 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I991_fin) true) (by decide) rfl I991_fin intTest_fst
theorem link991 : linkOK pL991 pH991 pI991 = true := by decide +kernel
theorem cvx991 : ConvexBetweenHumps 991 :=
  cvx_of L991_ok H991_ok I991_ok link991 (by decide)

/-! ### `N = 992` -/

def pL992 : Prm := ⟨76, 36, 37, 994, 11, 18446744073709551616, 173664142805046678, 173664142805046678⟩
def pH992 : Prm := ⟨76, 36, 37, 994, 11, 18446744073709551616, 173666341828302230, 173666341828302230⟩
def pI992 : Prm := ⟨64, 32, 29, 994, 11, 18446744073709551616, 173664142805046678, 173666341828302230⟩
theorem L992_fin : (prmOK pL992 992 && ptTest pL992 (runFrom pL992 (fmask pL992) (cmask pL992) (hmask pL992) 1 991 (true, (init pL992), (init pL992))) 992 496 false) = true := by
  decide +kernel
theorem L992_ok : RunOK pL992 992 (runFrom pL992 (fmask pL992) (cmask pL992) (hmask pL992) 1 991 (true, (init pL992), (init pL992))) ∧ ptTest pL992 (runFrom pL992 (fmask pL992) (cmask pL992) (hmask pL992) 1 991 (true, (init pL992), (init pL992))) 992 496 false = true :=
  fin_run (runOK_init (prmOK_of_and L992_fin) true) (by decide) rfl L992_fin ptTest_fst
theorem H992_fin : (prmOK pH992 992 && ptTest pH992 (runFrom pH992 (fmask pH992) (cmask pH992) (hmask pH992) 1 991 (true, (init pH992), (init pH992))) 992 496 true) = true := by
  decide +kernel
theorem H992_ok : RunOK pH992 992 (runFrom pH992 (fmask pH992) (cmask pH992) (hmask pH992) 1 991 (true, (init pH992), (init pH992))) ∧ ptTest pH992 (runFrom pH992 (fmask pH992) (cmask pH992) (hmask pH992) 1 991 (true, (init pH992), (init pH992))) 992 496 true = true :=
  fin_run (runOK_init (prmOK_of_and H992_fin) true) (by decide) rfl H992_fin ptTest_fst
theorem I992_fin : (prmOK pI992 992 && intTest pI992 (runFrom pI992 (fmask pI992) (cmask pI992) (hmask pI992) 1 991 (true, (init pI992), (init pI992))) 992 18 true) = true := by
  decide +kernel
theorem I992_ok : RunOK pI992 992 (runFrom pI992 (fmask pI992) (cmask pI992) (hmask pI992) 1 991 (true, (init pI992), (init pI992))) ∧ intTest pI992 (runFrom pI992 (fmask pI992) (cmask pI992) (hmask pI992) 1 991 (true, (init pI992), (init pI992))) 992 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I992_fin) true) (by decide) rfl I992_fin intTest_fst
theorem link992 : linkOK pL992 pH992 pI992 = true := by decide +kernel
theorem cvx992 : ConvexBetweenHumps 992 :=
  cvx_of L992_ok H992_ok I992_ok link992 (by decide)
theorem cenlink992 : cenLinkOK pI992 992 = true := by decide +kernel
theorem cen992 : CenterUniqueMin 992 ∧ DipHyp 992 ∧ OnePointHyps 992 :=
  cen_of L992_ok H992_ok I992_ok link992 cenlink992

/-! ### `N = 993` -/

def pL993 : Prm := ⟨76, 36, 37, 995, 11, 18446744073709551616, 173524493182068243, 173524493182068243⟩
def pH993 : Prm := ⟨76, 36, 37, 995, 11, 18446744073709551616, 173526692205323795, 173526692205323795⟩
def pI993 : Prm := ⟨65, 31, 31, 995, 11, 18446744073709551616, 173524493182068243, 173526692205323795⟩
theorem L993_fin : (prmOK pL993 993 && ptTest pL993 (runFrom pL993 (fmask pL993) (cmask pL993) (hmask pL993) 1 992 (true, (init pL993), (init pL993))) 993 497 false) = true := by
  decide +kernel
theorem L993_ok : RunOK pL993 993 (runFrom pL993 (fmask pL993) (cmask pL993) (hmask pL993) 1 992 (true, (init pL993), (init pL993))) ∧ ptTest pL993 (runFrom pL993 (fmask pL993) (cmask pL993) (hmask pL993) 1 992 (true, (init pL993), (init pL993))) 993 497 false = true :=
  fin_run (runOK_init (prmOK_of_and L993_fin) true) (by decide) rfl L993_fin ptTest_fst
theorem H993_fin : (prmOK pH993 993 && ptTest pH993 (runFrom pH993 (fmask pH993) (cmask pH993) (hmask pH993) 1 992 (true, (init pH993), (init pH993))) 993 497 true) = true := by
  decide +kernel
theorem H993_ok : RunOK pH993 993 (runFrom pH993 (fmask pH993) (cmask pH993) (hmask pH993) 1 992 (true, (init pH993), (init pH993))) ∧ ptTest pH993 (runFrom pH993 (fmask pH993) (cmask pH993) (hmask pH993) 1 992 (true, (init pH993), (init pH993))) 993 497 true = true :=
  fin_run (runOK_init (prmOK_of_and H993_fin) true) (by decide) rfl H993_fin ptTest_fst
theorem I993_fin : (prmOK pI993 993 && intTest pI993 (runFrom pI993 (fmask pI993) (cmask pI993) (hmask pI993) 1 992 (true, (init pI993), (init pI993))) 993 18 false) = true := by
  decide +kernel
theorem I993_ok : RunOK pI993 993 (runFrom pI993 (fmask pI993) (cmask pI993) (hmask pI993) 1 992 (true, (init pI993), (init pI993))) ∧ intTest pI993 (runFrom pI993 (fmask pI993) (cmask pI993) (hmask pI993) 1 992 (true, (init pI993), (init pI993))) 993 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I993_fin) true) (by decide) rfl I993_fin intTest_fst
theorem link993 : linkOK pL993 pH993 pI993 = true := by decide +kernel
theorem cvx993 : ConvexBetweenHumps 993 :=
  cvx_of L993_ok H993_ok I993_ok link993 (by decide)

/-! ### `N = 994` -/

def pL994 : Prm := ⟨76, 36, 37, 996, 11, 18446744073709551616, 173385207046241930, 173385207046241930⟩
def pH994 : Prm := ⟨76, 36, 37, 996, 11, 18446744073709551616, 173387406069497482, 173387406069497482⟩
def pI994 : Prm := ⟨64, 32, 29, 996, 11, 18446744073709551616, 173385207046241930, 173387406069497482⟩
theorem L994_fin : (prmOK pL994 994 && ptTest pL994 (runFrom pL994 (fmask pL994) (cmask pL994) (hmask pL994) 1 993 (true, (init pL994), (init pL994))) 994 497 false) = true := by
  decide +kernel
theorem L994_ok : RunOK pL994 994 (runFrom pL994 (fmask pL994) (cmask pL994) (hmask pL994) 1 993 (true, (init pL994), (init pL994))) ∧ ptTest pL994 (runFrom pL994 (fmask pL994) (cmask pL994) (hmask pL994) 1 993 (true, (init pL994), (init pL994))) 994 497 false = true :=
  fin_run (runOK_init (prmOK_of_and L994_fin) true) (by decide) rfl L994_fin ptTest_fst
theorem H994_fin : (prmOK pH994 994 && ptTest pH994 (runFrom pH994 (fmask pH994) (cmask pH994) (hmask pH994) 1 993 (true, (init pH994), (init pH994))) 994 497 true) = true := by
  decide +kernel
theorem H994_ok : RunOK pH994 994 (runFrom pH994 (fmask pH994) (cmask pH994) (hmask pH994) 1 993 (true, (init pH994), (init pH994))) ∧ ptTest pH994 (runFrom pH994 (fmask pH994) (cmask pH994) (hmask pH994) 1 993 (true, (init pH994), (init pH994))) 994 497 true = true :=
  fin_run (runOK_init (prmOK_of_and H994_fin) true) (by decide) rfl H994_fin ptTest_fst
theorem I994_fin : (prmOK pI994 994 && intTest pI994 (runFrom pI994 (fmask pI994) (cmask pI994) (hmask pI994) 1 993 (true, (init pI994), (init pI994))) 994 18 true) = true := by
  decide +kernel
theorem I994_ok : RunOK pI994 994 (runFrom pI994 (fmask pI994) (cmask pI994) (hmask pI994) 1 993 (true, (init pI994), (init pI994))) ∧ intTest pI994 (runFrom pI994 (fmask pI994) (cmask pI994) (hmask pI994) 1 993 (true, (init pI994), (init pI994))) 994 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I994_fin) true) (by decide) rfl I994_fin intTest_fst
theorem link994 : linkOK pL994 pH994 pI994 = true := by decide +kernel
theorem cvx994 : ConvexBetweenHumps 994 :=
  cvx_of L994_ok H994_ok I994_ok link994 (by decide)
theorem cenlink994 : cenLinkOK pI994 994 = true := by decide +kernel
theorem cen994 : CenterUniqueMin 994 ∧ DipHyp 994 ∧ OnePointHyps 994 :=
  cen_of L994_ok H994_ok I994_ok link994 cenlink994

/-! ### `N = 995` -/

def pL995 : Prm := ⟨76, 36, 37, 997, 11, 18446744073709551616, 173246047896436761, 173246047896436761⟩
def pH995 : Prm := ⟨76, 36, 37, 997, 11, 18446744073709551616, 173248246919692313, 173248246919692313⟩
def pI995 : Prm := ⟨65, 31, 31, 997, 11, 18446744073709551616, 173246047896436761, 173248246919692313⟩
theorem L995_fin : (prmOK pL995 995 && ptTest pL995 (runFrom pL995 (fmask pL995) (cmask pL995) (hmask pL995) 1 994 (true, (init pL995), (init pL995))) 995 498 false) = true := by
  decide +kernel
theorem L995_ok : RunOK pL995 995 (runFrom pL995 (fmask pL995) (cmask pL995) (hmask pL995) 1 994 (true, (init pL995), (init pL995))) ∧ ptTest pL995 (runFrom pL995 (fmask pL995) (cmask pL995) (hmask pL995) 1 994 (true, (init pL995), (init pL995))) 995 498 false = true :=
  fin_run (runOK_init (prmOK_of_and L995_fin) true) (by decide) rfl L995_fin ptTest_fst
theorem H995_fin : (prmOK pH995 995 && ptTest pH995 (runFrom pH995 (fmask pH995) (cmask pH995) (hmask pH995) 1 994 (true, (init pH995), (init pH995))) 995 498 true) = true := by
  decide +kernel
theorem H995_ok : RunOK pH995 995 (runFrom pH995 (fmask pH995) (cmask pH995) (hmask pH995) 1 994 (true, (init pH995), (init pH995))) ∧ ptTest pH995 (runFrom pH995 (fmask pH995) (cmask pH995) (hmask pH995) 1 994 (true, (init pH995), (init pH995))) 995 498 true = true :=
  fin_run (runOK_init (prmOK_of_and H995_fin) true) (by decide) rfl H995_fin ptTest_fst
theorem I995_fin : (prmOK pI995 995 && intTest pI995 (runFrom pI995 (fmask pI995) (cmask pI995) (hmask pI995) 1 994 (true, (init pI995), (init pI995))) 995 18 false) = true := by
  decide +kernel
theorem I995_ok : RunOK pI995 995 (runFrom pI995 (fmask pI995) (cmask pI995) (hmask pI995) 1 994 (true, (init pI995), (init pI995))) ∧ intTest pI995 (runFrom pI995 (fmask pI995) (cmask pI995) (hmask pI995) 1 994 (true, (init pI995), (init pI995))) 995 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I995_fin) true) (by decide) rfl I995_fin intTest_fst
theorem link995 : linkOK pL995 pH995 pI995 = true := by decide +kernel
theorem cvx995 : ConvexBetweenHumps 995 :=
  cvx_of L995_ok H995_ok I995_ok link995 (by decide)

/-! ### `N = 996` -/

def pL996 : Prm := ⟨76, 36, 37, 998, 11, 18446744073709551616, 173107250175071734, 173107250175071734⟩
def pH996 : Prm := ⟨76, 36, 37, 998, 11, 18446744073709551616, 173109449198327286, 173109449198327286⟩
def pI996 : Prm := ⟨64, 32, 29, 998, 11, 18446744073709551616, 173107250175071734, 173109449198327286⟩
theorem L996_fin : (prmOK pL996 996 && ptTest pL996 (runFrom pL996 (fmask pL996) (cmask pL996) (hmask pL996) 1 995 (true, (init pL996), (init pL996))) 996 498 false) = true := by
  decide +kernel
theorem L996_ok : RunOK pL996 996 (runFrom pL996 (fmask pL996) (cmask pL996) (hmask pL996) 1 995 (true, (init pL996), (init pL996))) ∧ ptTest pL996 (runFrom pL996 (fmask pL996) (cmask pL996) (hmask pL996) 1 995 (true, (init pL996), (init pL996))) 996 498 false = true :=
  fin_run (runOK_init (prmOK_of_and L996_fin) true) (by decide) rfl L996_fin ptTest_fst
theorem H996_fin : (prmOK pH996 996 && ptTest pH996 (runFrom pH996 (fmask pH996) (cmask pH996) (hmask pH996) 1 995 (true, (init pH996), (init pH996))) 996 498 true) = true := by
  decide +kernel
theorem H996_ok : RunOK pH996 996 (runFrom pH996 (fmask pH996) (cmask pH996) (hmask pH996) 1 995 (true, (init pH996), (init pH996))) ∧ ptTest pH996 (runFrom pH996 (fmask pH996) (cmask pH996) (hmask pH996) 1 995 (true, (init pH996), (init pH996))) 996 498 true = true :=
  fin_run (runOK_init (prmOK_of_and H996_fin) true) (by decide) rfl H996_fin ptTest_fst
theorem I996_fin : (prmOK pI996 996 && intTest pI996 (runFrom pI996 (fmask pI996) (cmask pI996) (hmask pI996) 1 995 (true, (init pI996), (init pI996))) 996 18 true) = true := by
  decide +kernel
theorem I996_ok : RunOK pI996 996 (runFrom pI996 (fmask pI996) (cmask pI996) (hmask pI996) 1 995 (true, (init pI996), (init pI996))) ∧ intTest pI996 (runFrom pI996 (fmask pI996) (cmask pI996) (hmask pI996) 1 995 (true, (init pI996), (init pI996))) 996 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I996_fin) true) (by decide) rfl I996_fin intTest_fst
theorem link996 : linkOK pL996 pH996 pI996 = true := by decide +kernel
theorem cvx996 : ConvexBetweenHumps 996 :=
  cvx_of L996_ok H996_ok I996_ok link996 (by decide)
theorem cenlink996 : cenLinkOK pI996 996 = true := by decide +kernel
theorem cen996 : CenterUniqueMin 996 ∧ DipHyp 996 ∧ OnePointHyps 996 :=
  cen_of L996_ok H996_ok I996_ok link996 cenlink996

/-! ### `N = 997` -/

def pL997 : Prm := ⟨76, 36, 37, 999, 11, 18446744073709551616, 172968578829989173, 172968578829989173⟩
def pH997 : Prm := ⟨76, 36, 37, 999, 11, 18446744073709551616, 172970777853244725, 172970777853244725⟩
def pI997 : Prm := ⟨65, 31, 31, 999, 11, 18446744073709551616, 172968578829989173, 172970777853244725⟩
theorem L997_fin : (prmOK pL997 997 && ptTest pL997 (runFrom pL997 (fmask pL997) (cmask pL997) (hmask pL997) 1 996 (true, (init pL997), (init pL997))) 997 499 false) = true := by
  decide +kernel
theorem L997_ok : RunOK pL997 997 (runFrom pL997 (fmask pL997) (cmask pL997) (hmask pL997) 1 996 (true, (init pL997), (init pL997))) ∧ ptTest pL997 (runFrom pL997 (fmask pL997) (cmask pL997) (hmask pL997) 1 996 (true, (init pL997), (init pL997))) 997 499 false = true :=
  fin_run (runOK_init (prmOK_of_and L997_fin) true) (by decide) rfl L997_fin ptTest_fst
theorem H997_fin : (prmOK pH997 997 && ptTest pH997 (runFrom pH997 (fmask pH997) (cmask pH997) (hmask pH997) 1 996 (true, (init pH997), (init pH997))) 997 499 true) = true := by
  decide +kernel
theorem H997_ok : RunOK pH997 997 (runFrom pH997 (fmask pH997) (cmask pH997) (hmask pH997) 1 996 (true, (init pH997), (init pH997))) ∧ ptTest pH997 (runFrom pH997 (fmask pH997) (cmask pH997) (hmask pH997) 1 996 (true, (init pH997), (init pH997))) 997 499 true = true :=
  fin_run (runOK_init (prmOK_of_and H997_fin) true) (by decide) rfl H997_fin ptTest_fst
theorem I997_fin : (prmOK pI997 997 && intTest pI997 (runFrom pI997 (fmask pI997) (cmask pI997) (hmask pI997) 1 996 (true, (init pI997), (init pI997))) 997 18 false) = true := by
  decide +kernel
theorem I997_ok : RunOK pI997 997 (runFrom pI997 (fmask pI997) (cmask pI997) (hmask pI997) 1 996 (true, (init pI997), (init pI997))) ∧ intTest pI997 (runFrom pI997 (fmask pI997) (cmask pI997) (hmask pI997) 1 996 (true, (init pI997), (init pI997))) 997 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I997_fin) true) (by decide) rfl I997_fin intTest_fst
theorem link997 : linkOK pL997 pH997 pI997 = true := by decide +kernel
theorem cvx997 : ConvexBetweenHumps 997 :=
  cvx_of L997_ok H997_ok I997_ok link997 (by decide)

/-! ### `N = 998` -/

def pL998 : Prm := ⟨76, 36, 37, 1000, 11, 18446744073709551616, 172830266870369848, 172830266870369848⟩
def pH998 : Prm := ⟨76, 36, 37, 1000, 11, 18446744073709551616, 172832465893625400, 172832465893625400⟩
def pI998 : Prm := ⟨64, 32, 29, 1000, 11, 18446744073709551616, 172830266870369848, 172832465893625400⟩
theorem L998_fin : (prmOK pL998 998 && ptTest pL998 (runFrom pL998 (fmask pL998) (cmask pL998) (hmask pL998) 1 997 (true, (init pL998), (init pL998))) 998 499 false) = true := by
  decide +kernel
theorem L998_ok : RunOK pL998 998 (runFrom pL998 (fmask pL998) (cmask pL998) (hmask pL998) 1 997 (true, (init pL998), (init pL998))) ∧ ptTest pL998 (runFrom pL998 (fmask pL998) (cmask pL998) (hmask pL998) 1 997 (true, (init pL998), (init pL998))) 998 499 false = true :=
  fin_run (runOK_init (prmOK_of_and L998_fin) true) (by decide) rfl L998_fin ptTest_fst
theorem H998_fin : (prmOK pH998 998 && ptTest pH998 (runFrom pH998 (fmask pH998) (cmask pH998) (hmask pH998) 1 997 (true, (init pH998), (init pH998))) 998 499 true) = true := by
  decide +kernel
theorem H998_ok : RunOK pH998 998 (runFrom pH998 (fmask pH998) (cmask pH998) (hmask pH998) 1 997 (true, (init pH998), (init pH998))) ∧ ptTest pH998 (runFrom pH998 (fmask pH998) (cmask pH998) (hmask pH998) 1 997 (true, (init pH998), (init pH998))) 998 499 true = true :=
  fin_run (runOK_init (prmOK_of_and H998_fin) true) (by decide) rfl H998_fin ptTest_fst
theorem I998_fin : (prmOK pI998 998 && intTest pI998 (runFrom pI998 (fmask pI998) (cmask pI998) (hmask pI998) 1 997 (true, (init pI998), (init pI998))) 998 18 true) = true := by
  decide +kernel
theorem I998_ok : RunOK pI998 998 (runFrom pI998 (fmask pI998) (cmask pI998) (hmask pI998) 1 997 (true, (init pI998), (init pI998))) ∧ intTest pI998 (runFrom pI998 (fmask pI998) (cmask pI998) (hmask pI998) 1 997 (true, (init pI998), (init pI998))) 998 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I998_fin) true) (by decide) rfl I998_fin intTest_fst
theorem link998 : linkOK pL998 pH998 pI998 = true := by decide +kernel
theorem cvx998 : ConvexBetweenHumps 998 :=
  cvx_of L998_ok H998_ok I998_ok link998 (by decide)
theorem cenlink998 : cenLinkOK pI998 998 = true := by decide +kernel
theorem cen998 : CenterUniqueMin 998 ∧ DipHyp 998 ∧ OnePointHyps 998 :=
  cen_of L998_ok H998_ok I998_ok link998 cenlink998

/-! ### `N = 999` -/

def pL999 : Prm := ⟨76, 36, 37, 1001, 11, 18446744073709551616, 172692080681186572, 172692080681186572⟩
def pH999 : Prm := ⟨76, 36, 37, 1001, 11, 18446744073709551616, 172694279704442124, 172694279704442124⟩
def pI999 : Prm := ⟨64, 32, 29, 1001, 11, 18446744073709551616, 172692080681186572, 172694279704442124⟩
theorem L999_fin : (prmOK pL999 999 && ptTest pL999 (runFrom pL999 (fmask pL999) (cmask pL999) (hmask pL999) 1 998 (true, (init pL999), (init pL999))) 999 500 false) = true := by
  decide +kernel
theorem L999_ok : RunOK pL999 999 (runFrom pL999 (fmask pL999) (cmask pL999) (hmask pL999) 1 998 (true, (init pL999), (init pL999))) ∧ ptTest pL999 (runFrom pL999 (fmask pL999) (cmask pL999) (hmask pL999) 1 998 (true, (init pL999), (init pL999))) 999 500 false = true :=
  fin_run (runOK_init (prmOK_of_and L999_fin) true) (by decide) rfl L999_fin ptTest_fst
theorem H999_fin : (prmOK pH999 999 && ptTest pH999 (runFrom pH999 (fmask pH999) (cmask pH999) (hmask pH999) 1 998 (true, (init pH999), (init pH999))) 999 500 true) = true := by
  decide +kernel
theorem H999_ok : RunOK pH999 999 (runFrom pH999 (fmask pH999) (cmask pH999) (hmask pH999) 1 998 (true, (init pH999), (init pH999))) ∧ ptTest pH999 (runFrom pH999 (fmask pH999) (cmask pH999) (hmask pH999) 1 998 (true, (init pH999), (init pH999))) 999 500 true = true :=
  fin_run (runOK_init (prmOK_of_and H999_fin) true) (by decide) rfl H999_fin ptTest_fst
theorem I999_fin : (prmOK pI999 999 && intTest pI999 (runFrom pI999 (fmask pI999) (cmask pI999) (hmask pI999) 1 998 (true, (init pI999), (init pI999))) 999 18 false) = true := by
  decide +kernel
theorem I999_ok : RunOK pI999 999 (runFrom pI999 (fmask pI999) (cmask pI999) (hmask pI999) 1 998 (true, (init pI999), (init pI999))) ∧ intTest pI999 (runFrom pI999 (fmask pI999) (cmask pI999) (hmask pI999) 1 998 (true, (init pI999), (init pI999))) 999 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I999_fin) true) (by decide) rfl I999_fin intTest_fst
theorem link999 : linkOK pL999 pH999 pI999 = true := by decide +kernel
theorem cvx999 : ConvexBetweenHumps 999 :=
  cvx_of L999_ok H999_ok I999_ok link999 (by decide)

/-! ### `N = 1000` -/

def pL1000 : Prm := ⟨76, 36, 37, 1002, 11, 18446744073709551616, 172554251850095572, 172554251850095572⟩
def pH1000 : Prm := ⟨76, 36, 37, 1002, 11, 18446744073709551616, 172556450873351124, 172556450873351124⟩
def pI1000 : Prm := ⟨64, 32, 29, 1002, 11, 18446744073709551616, 172554251850095572, 172556450873351124⟩
theorem L1000_fin : (prmOK pL1000 1000 && ptTest pL1000 (runFrom pL1000 (fmask pL1000) (cmask pL1000) (hmask pL1000) 1 999 (true, (init pL1000), (init pL1000))) 1000 500 false) = true := by
  decide +kernel
theorem L1000_ok : RunOK pL1000 1000 (runFrom pL1000 (fmask pL1000) (cmask pL1000) (hmask pL1000) 1 999 (true, (init pL1000), (init pL1000))) ∧ ptTest pL1000 (runFrom pL1000 (fmask pL1000) (cmask pL1000) (hmask pL1000) 1 999 (true, (init pL1000), (init pL1000))) 1000 500 false = true :=
  fin_run (runOK_init (prmOK_of_and L1000_fin) true) (by decide) rfl L1000_fin ptTest_fst
theorem H1000_fin : (prmOK pH1000 1000 && ptTest pH1000 (runFrom pH1000 (fmask pH1000) (cmask pH1000) (hmask pH1000) 1 999 (true, (init pH1000), (init pH1000))) 1000 500 true) = true := by
  decide +kernel
theorem H1000_ok : RunOK pH1000 1000 (runFrom pH1000 (fmask pH1000) (cmask pH1000) (hmask pH1000) 1 999 (true, (init pH1000), (init pH1000))) ∧ ptTest pH1000 (runFrom pH1000 (fmask pH1000) (cmask pH1000) (hmask pH1000) 1 999 (true, (init pH1000), (init pH1000))) 1000 500 true = true :=
  fin_run (runOK_init (prmOK_of_and H1000_fin) true) (by decide) rfl H1000_fin ptTest_fst
theorem I1000_fin : (prmOK pI1000 1000 && intTest pI1000 (runFrom pI1000 (fmask pI1000) (cmask pI1000) (hmask pI1000) 1 999 (true, (init pI1000), (init pI1000))) 1000 18 true) = true := by
  decide +kernel
theorem I1000_ok : RunOK pI1000 1000 (runFrom pI1000 (fmask pI1000) (cmask pI1000) (hmask pI1000) 1 999 (true, (init pI1000), (init pI1000))) ∧ intTest pI1000 (runFrom pI1000 (fmask pI1000) (cmask pI1000) (hmask pI1000) 1 999 (true, (init pI1000), (init pI1000))) 1000 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1000_fin) true) (by decide) rfl I1000_fin intTest_fst
theorem link1000 : linkOK pL1000 pH1000 pI1000 = true := by decide +kernel
theorem cvx1000 : ConvexBetweenHumps 1000 :=
  cvx_of L1000_ok H1000_ok I1000_ok link1000 (by decide)
theorem cenlink1000 : cenLinkOK pI1000 1000 = true := by decide +kernel
theorem cen1000 : CenterUniqueMin 1000 ∧ DipHyp 1000 ∧ OnePointHyps 1000 :=
  cen_of L1000_ok H1000_ok I1000_ok link1000 cenlink1000

/-! ### `N = 1001` -/

def pL1001 : Prm := ⟨76, 36, 37, 1003, 11, 18446744073709551616, 172416548187560257, 172416548187560257⟩
def pH1001 : Prm := ⟨76, 36, 37, 1003, 11, 18446744073709551616, 172418747210815809, 172418747210815809⟩
def pI1001 : Prm := ⟨64, 32, 29, 1003, 11, 18446744073709551616, 172416548187560257, 172418747210815809⟩
theorem L1001_fin : (prmOK pL1001 1001 && ptTest pL1001 (runFrom pL1001 (fmask pL1001) (cmask pL1001) (hmask pL1001) 1 1000 (true, (init pL1001), (init pL1001))) 1001 501 false) = true := by
  decide +kernel
theorem L1001_ok : RunOK pL1001 1001 (runFrom pL1001 (fmask pL1001) (cmask pL1001) (hmask pL1001) 1 1000 (true, (init pL1001), (init pL1001))) ∧ ptTest pL1001 (runFrom pL1001 (fmask pL1001) (cmask pL1001) (hmask pL1001) 1 1000 (true, (init pL1001), (init pL1001))) 1001 501 false = true :=
  fin_run (runOK_init (prmOK_of_and L1001_fin) true) (by decide) rfl L1001_fin ptTest_fst
theorem H1001_fin : (prmOK pH1001 1001 && ptTest pH1001 (runFrom pH1001 (fmask pH1001) (cmask pH1001) (hmask pH1001) 1 1000 (true, (init pH1001), (init pH1001))) 1001 501 true) = true := by
  decide +kernel
theorem H1001_ok : RunOK pH1001 1001 (runFrom pH1001 (fmask pH1001) (cmask pH1001) (hmask pH1001) 1 1000 (true, (init pH1001), (init pH1001))) ∧ ptTest pH1001 (runFrom pH1001 (fmask pH1001) (cmask pH1001) (hmask pH1001) 1 1000 (true, (init pH1001), (init pH1001))) 1001 501 true = true :=
  fin_run (runOK_init (prmOK_of_and H1001_fin) true) (by decide) rfl H1001_fin ptTest_fst
theorem I1001_fin : (prmOK pI1001 1001 && intTest pI1001 (runFrom pI1001 (fmask pI1001) (cmask pI1001) (hmask pI1001) 1 1000 (true, (init pI1001), (init pI1001))) 1001 18 false) = true := by
  decide +kernel
theorem I1001_ok : RunOK pI1001 1001 (runFrom pI1001 (fmask pI1001) (cmask pI1001) (hmask pI1001) 1 1000 (true, (init pI1001), (init pI1001))) ∧ intTest pI1001 (runFrom pI1001 (fmask pI1001) (cmask pI1001) (hmask pI1001) 1 1000 (true, (init pI1001), (init pI1001))) 1001 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1001_fin) true) (by decide) rfl I1001_fin intTest_fst
theorem link1001 : linkOK pL1001 pH1001 pI1001 = true := by decide +kernel
theorem cvx1001 : ConvexBetweenHumps 1001 :=
  cvx_of L1001_ok H1001_ok I1001_ok link1001 (by decide)

/-! ### `N = 1002` -/

def pL1002 : Prm := ⟨76, 36, 37, 1004, 11, 18446744073709551616, 172279199871130839, 172279199871130839⟩
def pH1002 : Prm := ⟨76, 36, 37, 1004, 11, 18446744073709551616, 172281398894386391, 172281398894386391⟩
def pI1002 : Prm := ⟨64, 32, 29, 1004, 11, 18446744073709551616, 172279199871130839, 172281398894386391⟩
theorem L1002_fin : (prmOK pL1002 1002 && ptTest pL1002 (runFrom pL1002 (fmask pL1002) (cmask pL1002) (hmask pL1002) 1 1001 (true, (init pL1002), (init pL1002))) 1002 501 false) = true := by
  decide +kernel
theorem L1002_ok : RunOK pL1002 1002 (runFrom pL1002 (fmask pL1002) (cmask pL1002) (hmask pL1002) 1 1001 (true, (init pL1002), (init pL1002))) ∧ ptTest pL1002 (runFrom pL1002 (fmask pL1002) (cmask pL1002) (hmask pL1002) 1 1001 (true, (init pL1002), (init pL1002))) 1002 501 false = true :=
  fin_run (runOK_init (prmOK_of_and L1002_fin) true) (by decide) rfl L1002_fin ptTest_fst
theorem H1002_fin : (prmOK pH1002 1002 && ptTest pH1002 (runFrom pH1002 (fmask pH1002) (cmask pH1002) (hmask pH1002) 1 1001 (true, (init pH1002), (init pH1002))) 1002 501 true) = true := by
  decide +kernel
theorem H1002_ok : RunOK pH1002 1002 (runFrom pH1002 (fmask pH1002) (cmask pH1002) (hmask pH1002) 1 1001 (true, (init pH1002), (init pH1002))) ∧ ptTest pH1002 (runFrom pH1002 (fmask pH1002) (cmask pH1002) (hmask pH1002) 1 1001 (true, (init pH1002), (init pH1002))) 1002 501 true = true :=
  fin_run (runOK_init (prmOK_of_and H1002_fin) true) (by decide) rfl H1002_fin ptTest_fst
theorem I1002_fin : (prmOK pI1002 1002 && intTest pI1002 (runFrom pI1002 (fmask pI1002) (cmask pI1002) (hmask pI1002) 1 1001 (true, (init pI1002), (init pI1002))) 1002 18 true) = true := by
  decide +kernel
theorem I1002_ok : RunOK pI1002 1002 (runFrom pI1002 (fmask pI1002) (cmask pI1002) (hmask pI1002) 1 1001 (true, (init pI1002), (init pI1002))) ∧ intTest pI1002 (runFrom pI1002 (fmask pI1002) (cmask pI1002) (hmask pI1002) 1 1001 (true, (init pI1002), (init pI1002))) 1002 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1002_fin) true) (by decide) rfl I1002_fin intTest_fst
theorem link1002 : linkOK pL1002 pH1002 pI1002 = true := by decide +kernel
theorem cvx1002 : ConvexBetweenHumps 1002 :=
  cvx_of L1002_ok H1002_ok I1002_ok link1002 (by decide)
theorem cenlink1002 : cenLinkOK pI1002 1002 = true := by decide +kernel
theorem cen1002 : CenterUniqueMin 1002 ∧ DipHyp 1002 ∧ OnePointHyps 1002 :=
  cen_of L1002_ok H1002_ok I1002_ok link1002 cenlink1002

/-! ### `N = 1003` -/

def pL1003 : Prm := ⟨76, 36, 37, 1005, 11, 18446744073709551616, 172141976125232111, 172141976125232111⟩
def pH1003 : Prm := ⟨76, 36, 37, 1005, 11, 18446744073709551616, 172144175148487663, 172144175148487663⟩
def pI1003 : Prm := ⟨64, 32, 29, 1005, 11, 18446744073709551616, 172141976125232111, 172144175148487663⟩
theorem L1003_fin : (prmOK pL1003 1003 && ptTest pL1003 (runFrom pL1003 (fmask pL1003) (cmask pL1003) (hmask pL1003) 1 1002 (true, (init pL1003), (init pL1003))) 1003 502 false) = true := by
  decide +kernel
theorem L1003_ok : RunOK pL1003 1003 (runFrom pL1003 (fmask pL1003) (cmask pL1003) (hmask pL1003) 1 1002 (true, (init pL1003), (init pL1003))) ∧ ptTest pL1003 (runFrom pL1003 (fmask pL1003) (cmask pL1003) (hmask pL1003) 1 1002 (true, (init pL1003), (init pL1003))) 1003 502 false = true :=
  fin_run (runOK_init (prmOK_of_and L1003_fin) true) (by decide) rfl L1003_fin ptTest_fst
theorem H1003_fin : (prmOK pH1003 1003 && ptTest pH1003 (runFrom pH1003 (fmask pH1003) (cmask pH1003) (hmask pH1003) 1 1002 (true, (init pH1003), (init pH1003))) 1003 502 true) = true := by
  decide +kernel
theorem H1003_ok : RunOK pH1003 1003 (runFrom pH1003 (fmask pH1003) (cmask pH1003) (hmask pH1003) 1 1002 (true, (init pH1003), (init pH1003))) ∧ ptTest pH1003 (runFrom pH1003 (fmask pH1003) (cmask pH1003) (hmask pH1003) 1 1002 (true, (init pH1003), (init pH1003))) 1003 502 true = true :=
  fin_run (runOK_init (prmOK_of_and H1003_fin) true) (by decide) rfl H1003_fin ptTest_fst
theorem I1003_fin : (prmOK pI1003 1003 && intTest pI1003 (runFrom pI1003 (fmask pI1003) (cmask pI1003) (hmask pI1003) 1 1002 (true, (init pI1003), (init pI1003))) 1003 18 false) = true := by
  decide +kernel
theorem I1003_ok : RunOK pI1003 1003 (runFrom pI1003 (fmask pI1003) (cmask pI1003) (hmask pI1003) 1 1002 (true, (init pI1003), (init pI1003))) ∧ intTest pI1003 (runFrom pI1003 (fmask pI1003) (cmask pI1003) (hmask pI1003) 1 1002 (true, (init pI1003), (init pI1003))) 1003 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1003_fin) true) (by decide) rfl I1003_fin intTest_fst
theorem link1003 : linkOK pL1003 pH1003 pI1003 = true := by decide +kernel
theorem cvx1003 : ConvexBetweenHumps 1003 :=
  cvx_of L1003_ok H1003_ok I1003_ok link1003 (by decide)

/-! ### `N = 1004` -/

def pL1004 : Prm := ⟨76, 36, 37, 1006, 11, 18446744073709551616, 172005105728763703, 172005105728763703⟩
def pH1004 : Prm := ⟨76, 36, 37, 1006, 11, 18446744073709551616, 172007304752019255, 172007304752019255⟩
def pI1004 : Prm := ⟨64, 32, 29, 1006, 11, 18446744073709551616, 172005105728763703, 172007304752019255⟩
theorem L1004_fin : (prmOK pL1004 1004 && ptTest pL1004 (runFrom pL1004 (fmask pL1004) (cmask pL1004) (hmask pL1004) 1 1003 (true, (init pL1004), (init pL1004))) 1004 502 false) = true := by
  decide +kernel
theorem L1004_ok : RunOK pL1004 1004 (runFrom pL1004 (fmask pL1004) (cmask pL1004) (hmask pL1004) 1 1003 (true, (init pL1004), (init pL1004))) ∧ ptTest pL1004 (runFrom pL1004 (fmask pL1004) (cmask pL1004) (hmask pL1004) 1 1003 (true, (init pL1004), (init pL1004))) 1004 502 false = true :=
  fin_run (runOK_init (prmOK_of_and L1004_fin) true) (by decide) rfl L1004_fin ptTest_fst
theorem H1004_fin : (prmOK pH1004 1004 && ptTest pH1004 (runFrom pH1004 (fmask pH1004) (cmask pH1004) (hmask pH1004) 1 1003 (true, (init pH1004), (init pH1004))) 1004 502 true) = true := by
  decide +kernel
theorem H1004_ok : RunOK pH1004 1004 (runFrom pH1004 (fmask pH1004) (cmask pH1004) (hmask pH1004) 1 1003 (true, (init pH1004), (init pH1004))) ∧ ptTest pH1004 (runFrom pH1004 (fmask pH1004) (cmask pH1004) (hmask pH1004) 1 1003 (true, (init pH1004), (init pH1004))) 1004 502 true = true :=
  fin_run (runOK_init (prmOK_of_and H1004_fin) true) (by decide) rfl H1004_fin ptTest_fst
theorem I1004_fin : (prmOK pI1004 1004 && intTest pI1004 (runFrom pI1004 (fmask pI1004) (cmask pI1004) (hmask pI1004) 1 1003 (true, (init pI1004), (init pI1004))) 1004 18 true) = true := by
  decide +kernel
theorem I1004_ok : RunOK pI1004 1004 (runFrom pI1004 (fmask pI1004) (cmask pI1004) (hmask pI1004) 1 1003 (true, (init pI1004), (init pI1004))) ∧ intTest pI1004 (runFrom pI1004 (fmask pI1004) (cmask pI1004) (hmask pI1004) 1 1003 (true, (init pI1004), (init pI1004))) 1004 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1004_fin) true) (by decide) rfl I1004_fin intTest_fst
theorem link1004 : linkOK pL1004 pH1004 pI1004 = true := by decide +kernel
theorem cvx1004 : ConvexBetweenHumps 1004 :=
  cvx_of L1004_ok H1004_ok I1004_ok link1004 (by decide)
theorem cenlink1004 : cenLinkOK pI1004 1004 = true := by decide +kernel
theorem cen1004 : CenterUniqueMin 1004 ∧ DipHyp 1004 ∧ OnePointHyps 1004 :=
  cen_of L1004_ok H1004_ok I1004_ok link1004 cenlink1004

/-! ### `N = 1005` -/

def pL1005 : Prm := ⟨76, 36, 37, 1007, 11, 18446744073709551616, 171868359308711698, 171868359308711698⟩
def pH1005 : Prm := ⟨76, 36, 37, 1007, 11, 18446744073709551616, 171870558331967250, 171870558331967250⟩
def pI1005 : Prm := ⟨64, 32, 29, 1007, 11, 18446744073709551616, 171868359308711698, 171870558331967250⟩
theorem L1005_fin : (prmOK pL1005 1005 && ptTest pL1005 (runFrom pL1005 (fmask pL1005) (cmask pL1005) (hmask pL1005) 1 1004 (true, (init pL1005), (init pL1005))) 1005 503 false) = true := by
  decide +kernel
theorem L1005_ok : RunOK pL1005 1005 (runFrom pL1005 (fmask pL1005) (cmask pL1005) (hmask pL1005) 1 1004 (true, (init pL1005), (init pL1005))) ∧ ptTest pL1005 (runFrom pL1005 (fmask pL1005) (cmask pL1005) (hmask pL1005) 1 1004 (true, (init pL1005), (init pL1005))) 1005 503 false = true :=
  fin_run (runOK_init (prmOK_of_and L1005_fin) true) (by decide) rfl L1005_fin ptTest_fst
theorem H1005_fin : (prmOK pH1005 1005 && ptTest pH1005 (runFrom pH1005 (fmask pH1005) (cmask pH1005) (hmask pH1005) 1 1004 (true, (init pH1005), (init pH1005))) 1005 503 true) = true := by
  decide +kernel
theorem H1005_ok : RunOK pH1005 1005 (runFrom pH1005 (fmask pH1005) (cmask pH1005) (hmask pH1005) 1 1004 (true, (init pH1005), (init pH1005))) ∧ ptTest pH1005 (runFrom pH1005 (fmask pH1005) (cmask pH1005) (hmask pH1005) 1 1004 (true, (init pH1005), (init pH1005))) 1005 503 true = true :=
  fin_run (runOK_init (prmOK_of_and H1005_fin) true) (by decide) rfl H1005_fin ptTest_fst
theorem I1005_fin : (prmOK pI1005 1005 && intTest pI1005 (runFrom pI1005 (fmask pI1005) (cmask pI1005) (hmask pI1005) 1 1004 (true, (init pI1005), (init pI1005))) 1005 18 false) = true := by
  decide +kernel
theorem I1005_ok : RunOK pI1005 1005 (runFrom pI1005 (fmask pI1005) (cmask pI1005) (hmask pI1005) 1 1004 (true, (init pI1005), (init pI1005))) ∧ intTest pI1005 (runFrom pI1005 (fmask pI1005) (cmask pI1005) (hmask pI1005) 1 1004 (true, (init pI1005), (init pI1005))) 1005 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1005_fin) true) (by decide) rfl I1005_fin intTest_fst
theorem link1005 : linkOK pL1005 pH1005 pI1005 = true := by decide +kernel
theorem cvx1005 : ConvexBetweenHumps 1005 :=
  cvx_of L1005_ok H1005_ok I1005_ok link1005 (by decide)

/-! ### `N = 1006` -/

def pL1006 : Prm := ⟨76, 36, 37, 1008, 11, 18446744073709551616, 171731964256503871, 171731964256503871⟩
def pH1006 : Prm := ⟨76, 36, 37, 1008, 11, 18446744073709551616, 171734163279759423, 171734163279759423⟩
def pI1006 : Prm := ⟨64, 32, 29, 1008, 11, 18446744073709551616, 171731964256503871, 171734163279759423⟩
theorem L1006_fin : (prmOK pL1006 1006 && ptTest pL1006 (runFrom pL1006 (fmask pL1006) (cmask pL1006) (hmask pL1006) 1 1005 (true, (init pL1006), (init pL1006))) 1006 503 false) = true := by
  decide +kernel
theorem L1006_ok : RunOK pL1006 1006 (runFrom pL1006 (fmask pL1006) (cmask pL1006) (hmask pL1006) 1 1005 (true, (init pL1006), (init pL1006))) ∧ ptTest pL1006 (runFrom pL1006 (fmask pL1006) (cmask pL1006) (hmask pL1006) 1 1005 (true, (init pL1006), (init pL1006))) 1006 503 false = true :=
  fin_run (runOK_init (prmOK_of_and L1006_fin) true) (by decide) rfl L1006_fin ptTest_fst
theorem H1006_fin : (prmOK pH1006 1006 && ptTest pH1006 (runFrom pH1006 (fmask pH1006) (cmask pH1006) (hmask pH1006) 1 1005 (true, (init pH1006), (init pH1006))) 1006 503 true) = true := by
  decide +kernel
theorem H1006_ok : RunOK pH1006 1006 (runFrom pH1006 (fmask pH1006) (cmask pH1006) (hmask pH1006) 1 1005 (true, (init pH1006), (init pH1006))) ∧ ptTest pH1006 (runFrom pH1006 (fmask pH1006) (cmask pH1006) (hmask pH1006) 1 1005 (true, (init pH1006), (init pH1006))) 1006 503 true = true :=
  fin_run (runOK_init (prmOK_of_and H1006_fin) true) (by decide) rfl H1006_fin ptTest_fst
theorem I1006_fin : (prmOK pI1006 1006 && intTest pI1006 (runFrom pI1006 (fmask pI1006) (cmask pI1006) (hmask pI1006) 1 1005 (true, (init pI1006), (init pI1006))) 1006 18 true) = true := by
  decide +kernel
theorem I1006_ok : RunOK pI1006 1006 (runFrom pI1006 (fmask pI1006) (cmask pI1006) (hmask pI1006) 1 1005 (true, (init pI1006), (init pI1006))) ∧ intTest pI1006 (runFrom pI1006 (fmask pI1006) (cmask pI1006) (hmask pI1006) 1 1005 (true, (init pI1006), (init pI1006))) 1006 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1006_fin) true) (by decide) rfl I1006_fin intTest_fst
theorem link1006 : linkOK pL1006 pH1006 pI1006 = true := by decide +kernel
theorem cvx1006 : ConvexBetweenHumps 1006 :=
  cvx_of L1006_ok H1006_ok I1006_ok link1006 (by decide)
theorem cenlink1006 : cenLinkOK pI1006 1006 = true := by decide +kernel
theorem cen1006 : CenterUniqueMin 1006 ∧ DipHyp 1006 ∧ OnePointHyps 1006 :=
  cen_of L1006_ok H1006_ok I1006_ok link1006 cenlink1006

/-! ### `N = 1007` -/

def pL1007 : Prm := ⟨76, 36, 37, 1009, 11, 18446744073709551616, 171595692590398188, 171595692590398188⟩
def pH1007 : Prm := ⟨76, 36, 37, 1009, 11, 18446744073709551616, 171597891613653740, 171597891613653740⟩
def pI1007 : Prm := ⟨64, 32, 29, 1009, 11, 18446744073709551616, 171595692590398188, 171597891613653740⟩
theorem L1007_fin : (prmOK pL1007 1007 && ptTest pL1007 (runFrom pL1007 (fmask pL1007) (cmask pL1007) (hmask pL1007) 1 1006 (true, (init pL1007), (init pL1007))) 1007 504 false) = true := by
  decide +kernel
theorem L1007_ok : RunOK pL1007 1007 (runFrom pL1007 (fmask pL1007) (cmask pL1007) (hmask pL1007) 1 1006 (true, (init pL1007), (init pL1007))) ∧ ptTest pL1007 (runFrom pL1007 (fmask pL1007) (cmask pL1007) (hmask pL1007) 1 1006 (true, (init pL1007), (init pL1007))) 1007 504 false = true :=
  fin_run (runOK_init (prmOK_of_and L1007_fin) true) (by decide) rfl L1007_fin ptTest_fst
theorem H1007_fin : (prmOK pH1007 1007 && ptTest pH1007 (runFrom pH1007 (fmask pH1007) (cmask pH1007) (hmask pH1007) 1 1006 (true, (init pH1007), (init pH1007))) 1007 504 true) = true := by
  decide +kernel
theorem H1007_ok : RunOK pH1007 1007 (runFrom pH1007 (fmask pH1007) (cmask pH1007) (hmask pH1007) 1 1006 (true, (init pH1007), (init pH1007))) ∧ ptTest pH1007 (runFrom pH1007 (fmask pH1007) (cmask pH1007) (hmask pH1007) 1 1006 (true, (init pH1007), (init pH1007))) 1007 504 true = true :=
  fin_run (runOK_init (prmOK_of_and H1007_fin) true) (by decide) rfl H1007_fin ptTest_fst
theorem I1007_fin : (prmOK pI1007 1007 && intTest pI1007 (runFrom pI1007 (fmask pI1007) (cmask pI1007) (hmask pI1007) 1 1006 (true, (init pI1007), (init pI1007))) 1007 18 false) = true := by
  decide +kernel
theorem I1007_ok : RunOK pI1007 1007 (runFrom pI1007 (fmask pI1007) (cmask pI1007) (hmask pI1007) 1 1006 (true, (init pI1007), (init pI1007))) ∧ intTest pI1007 (runFrom pI1007 (fmask pI1007) (cmask pI1007) (hmask pI1007) 1 1006 (true, (init pI1007), (init pI1007))) 1007 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1007_fin) true) (by decide) rfl I1007_fin intTest_fst
theorem link1007 : linkOK pL1007 pH1007 pI1007 = true := by decide +kernel
theorem cvx1007 : ConvexBetweenHumps 1007 :=
  cvx_of L1007_ok H1007_ok I1007_ok link1007 (by decide)

/-! ### `N = 1008` -/

def pL1008 : Prm := ⟨76, 36, 37, 1010, 11, 18446744073709551616, 171459770325547746, 171459770325547746⟩
def pH1008 : Prm := ⟨76, 36, 37, 1010, 11, 18446744073709551616, 171461969348803298, 171461969348803298⟩
def pI1008 : Prm := ⟨64, 32, 29, 1010, 11, 18446744073709551616, 171459770325547746, 171461969348803298⟩
theorem L1008_fin : (prmOK pL1008 1008 && ptTest pL1008 (runFrom pL1008 (fmask pL1008) (cmask pL1008) (hmask pL1008) 1 1007 (true, (init pL1008), (init pL1008))) 1008 504 false) = true := by
  decide +kernel
theorem L1008_ok : RunOK pL1008 1008 (runFrom pL1008 (fmask pL1008) (cmask pL1008) (hmask pL1008) 1 1007 (true, (init pL1008), (init pL1008))) ∧ ptTest pL1008 (runFrom pL1008 (fmask pL1008) (cmask pL1008) (hmask pL1008) 1 1007 (true, (init pL1008), (init pL1008))) 1008 504 false = true :=
  fin_run (runOK_init (prmOK_of_and L1008_fin) true) (by decide) rfl L1008_fin ptTest_fst
theorem H1008_fin : (prmOK pH1008 1008 && ptTest pH1008 (runFrom pH1008 (fmask pH1008) (cmask pH1008) (hmask pH1008) 1 1007 (true, (init pH1008), (init pH1008))) 1008 504 true) = true := by
  decide +kernel
theorem H1008_ok : RunOK pH1008 1008 (runFrom pH1008 (fmask pH1008) (cmask pH1008) (hmask pH1008) 1 1007 (true, (init pH1008), (init pH1008))) ∧ ptTest pH1008 (runFrom pH1008 (fmask pH1008) (cmask pH1008) (hmask pH1008) 1 1007 (true, (init pH1008), (init pH1008))) 1008 504 true = true :=
  fin_run (runOK_init (prmOK_of_and H1008_fin) true) (by decide) rfl H1008_fin ptTest_fst
theorem I1008_fin : (prmOK pI1008 1008 && intTest pI1008 (runFrom pI1008 (fmask pI1008) (cmask pI1008) (hmask pI1008) 1 1007 (true, (init pI1008), (init pI1008))) 1008 18 true) = true := by
  decide +kernel
theorem I1008_ok : RunOK pI1008 1008 (runFrom pI1008 (fmask pI1008) (cmask pI1008) (hmask pI1008) 1 1007 (true, (init pI1008), (init pI1008))) ∧ intTest pI1008 (runFrom pI1008 (fmask pI1008) (cmask pI1008) (hmask pI1008) 1 1007 (true, (init pI1008), (init pI1008))) 1008 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1008_fin) true) (by decide) rfl I1008_fin intTest_fst
theorem link1008 : linkOK pL1008 pH1008 pI1008 = true := by decide +kernel
theorem cvx1008 : ConvexBetweenHumps 1008 :=
  cvx_of L1008_ok H1008_ok I1008_ok link1008 (by decide)
theorem cenlink1008 : cenLinkOK pI1008 1008 = true := by decide +kernel
theorem cen1008 : CenterUniqueMin 1008 ∧ DipHyp 1008 ∧ OnePointHyps 1008 :=
  cen_of L1008_ok H1008_ok I1008_ok link1008 cenlink1008

/-! ### `N = 1009` -/

def pL1009 : Prm := ⟨76, 36, 37, 1011, 11, 18446744073709551616, 171323970860285220, 171323970860285220⟩
def pH1009 : Prm := ⟨76, 36, 37, 1011, 11, 18446744073709551616, 171326169883540772, 171326169883540772⟩
def pI1009 : Prm := ⟨64, 32, 29, 1011, 11, 18446744073709551616, 171323970860285220, 171326169883540772⟩
theorem L1009_fin : (prmOK pL1009 1009 && ptTest pL1009 (runFrom pL1009 (fmask pL1009) (cmask pL1009) (hmask pL1009) 1 1008 (true, (init pL1009), (init pL1009))) 1009 505 false) = true := by
  decide +kernel
theorem L1009_ok : RunOK pL1009 1009 (runFrom pL1009 (fmask pL1009) (cmask pL1009) (hmask pL1009) 1 1008 (true, (init pL1009), (init pL1009))) ∧ ptTest pL1009 (runFrom pL1009 (fmask pL1009) (cmask pL1009) (hmask pL1009) 1 1008 (true, (init pL1009), (init pL1009))) 1009 505 false = true :=
  fin_run (runOK_init (prmOK_of_and L1009_fin) true) (by decide) rfl L1009_fin ptTest_fst
theorem H1009_fin : (prmOK pH1009 1009 && ptTest pH1009 (runFrom pH1009 (fmask pH1009) (cmask pH1009) (hmask pH1009) 1 1008 (true, (init pH1009), (init pH1009))) 1009 505 true) = true := by
  decide +kernel
theorem H1009_ok : RunOK pH1009 1009 (runFrom pH1009 (fmask pH1009) (cmask pH1009) (hmask pH1009) 1 1008 (true, (init pH1009), (init pH1009))) ∧ ptTest pH1009 (runFrom pH1009 (fmask pH1009) (cmask pH1009) (hmask pH1009) 1 1008 (true, (init pH1009), (init pH1009))) 1009 505 true = true :=
  fin_run (runOK_init (prmOK_of_and H1009_fin) true) (by decide) rfl H1009_fin ptTest_fst
theorem I1009_fin : (prmOK pI1009 1009 && intTest pI1009 (runFrom pI1009 (fmask pI1009) (cmask pI1009) (hmask pI1009) 1 1008 (true, (init pI1009), (init pI1009))) 1009 18 false) = true := by
  decide +kernel
theorem I1009_ok : RunOK pI1009 1009 (runFrom pI1009 (fmask pI1009) (cmask pI1009) (hmask pI1009) 1 1008 (true, (init pI1009), (init pI1009))) ∧ intTest pI1009 (runFrom pI1009 (fmask pI1009) (cmask pI1009) (hmask pI1009) 1 1008 (true, (init pI1009), (init pI1009))) 1009 18 false = true :=
  fin_run (runOK_init (prmOK_of_and I1009_fin) true) (by decide) rfl I1009_fin intTest_fst
theorem link1009 : linkOK pL1009 pH1009 pI1009 = true := by decide +kernel
theorem cvx1009 : ConvexBetweenHumps 1009 :=
  cvx_of L1009_ok H1009_ok I1009_ok link1009 (by decide)

/-! ### `N = 1010` -/

def pL1010 : Prm := ⟨76, 36, 37, 1012, 11, 18446744073709551616, 171188518844557071, 171188518844557071⟩
def pH1010 : Prm := ⟨76, 36, 37, 1012, 11, 18446744073709551616, 171190717867812623, 171190717867812623⟩
def pI1010 : Prm := ⟨64, 32, 29, 1012, 11, 18446744073709551616, 171188518844557071, 171190717867812623⟩
theorem L1010_fin : (prmOK pL1010 1010 && ptTest pL1010 (runFrom pL1010 (fmask pL1010) (cmask pL1010) (hmask pL1010) 1 1009 (true, (init pL1010), (init pL1010))) 1010 505 false) = true := by
  decide +kernel
theorem L1010_ok : RunOK pL1010 1010 (runFrom pL1010 (fmask pL1010) (cmask pL1010) (hmask pL1010) 1 1009 (true, (init pL1010), (init pL1010))) ∧ ptTest pL1010 (runFrom pL1010 (fmask pL1010) (cmask pL1010) (hmask pL1010) 1 1009 (true, (init pL1010), (init pL1010))) 1010 505 false = true :=
  fin_run (runOK_init (prmOK_of_and L1010_fin) true) (by decide) rfl L1010_fin ptTest_fst
theorem H1010_fin : (prmOK pH1010 1010 && ptTest pH1010 (runFrom pH1010 (fmask pH1010) (cmask pH1010) (hmask pH1010) 1 1009 (true, (init pH1010), (init pH1010))) 1010 505 true) = true := by
  decide +kernel
theorem H1010_ok : RunOK pH1010 1010 (runFrom pH1010 (fmask pH1010) (cmask pH1010) (hmask pH1010) 1 1009 (true, (init pH1010), (init pH1010))) ∧ ptTest pH1010 (runFrom pH1010 (fmask pH1010) (cmask pH1010) (hmask pH1010) 1 1009 (true, (init pH1010), (init pH1010))) 1010 505 true = true :=
  fin_run (runOK_init (prmOK_of_and H1010_fin) true) (by decide) rfl H1010_fin ptTest_fst
theorem I1010_fin : (prmOK pI1010 1010 && intTest pI1010 (runFrom pI1010 (fmask pI1010) (cmask pI1010) (hmask pI1010) 1 1009 (true, (init pI1010), (init pI1010))) 1010 18 true) = true := by
  decide +kernel
theorem I1010_ok : RunOK pI1010 1010 (runFrom pI1010 (fmask pI1010) (cmask pI1010) (hmask pI1010) 1 1009 (true, (init pI1010), (init pI1010))) ∧ intTest pI1010 (runFrom pI1010 (fmask pI1010) (cmask pI1010) (hmask pI1010) 1 1009 (true, (init pI1010), (init pI1010))) 1010 18 true = true :=
  fin_run (runOK_init (prmOK_of_and I1010_fin) true) (by decide) rfl I1010_fin intTest_fst
theorem link1010 : linkOK pL1010 pH1010 pI1010 = true := by decide +kernel
theorem cvx1010 : ConvexBetweenHumps 1010 :=
  cvx_of L1010_ok H1010_ok I1010_ok link1010 (by decide)
theorem cenlink1010 : cenLinkOK pI1010 1010 = true := by decide +kernel
theorem cen1010 : CenterUniqueMin 1010 ∧ DipHyp 1010 ∧ OnePointHyps 1010 :=
  cen_of L1010_ok H1010_ok I1010_ok link1010 cenlink1010

/-! ### The range -/

theorem cvx_968_1010 {N : ℕ} (h1 : 968 ≤ N) (h2 : N ≤ 1010) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 988
  · by_cases h4 : N ≤ 977
    · by_cases h6 : N ≤ 972
      · by_cases h8 : N ≤ 969
        · by_cases h10 : N ≤ 968
          · obtain rfl : N = 968 := by omega
            exact cvx968
          · obtain rfl : N = 969 := by omega
            exact cvx969
        · by_cases h10 : N ≤ 970
          · obtain rfl : N = 970 := by omega
            exact cvx970
          · by_cases h12 : N ≤ 971
            · obtain rfl : N = 971 := by omega
              exact cvx971
            · obtain rfl : N = 972 := by omega
              exact cvx972
      · by_cases h8 : N ≤ 974
        · by_cases h10 : N ≤ 973
          · obtain rfl : N = 973 := by omega
            exact cvx973
          · obtain rfl : N = 974 := by omega
            exact cvx974
        · by_cases h10 : N ≤ 975
          · obtain rfl : N = 975 := by omega
            exact cvx975
          · by_cases h12 : N ≤ 976
            · obtain rfl : N = 976 := by omega
              exact cvx976
            · obtain rfl : N = 977 := by omega
              exact cvx977
    · by_cases h6 : N ≤ 982
      · by_cases h8 : N ≤ 979
        · by_cases h10 : N ≤ 978
          · obtain rfl : N = 978 := by omega
            exact cvx978
          · obtain rfl : N = 979 := by omega
            exact cvx979
        · by_cases h10 : N ≤ 980
          · obtain rfl : N = 980 := by omega
            exact cvx980
          · by_cases h12 : N ≤ 981
            · obtain rfl : N = 981 := by omega
              exact cvx981
            · obtain rfl : N = 982 := by omega
              exact cvx982
      · by_cases h8 : N ≤ 985
        · by_cases h10 : N ≤ 983
          · obtain rfl : N = 983 := by omega
            exact cvx983
          · by_cases h12 : N ≤ 984
            · obtain rfl : N = 984 := by omega
              exact cvx984
            · obtain rfl : N = 985 := by omega
              exact cvx985
        · by_cases h10 : N ≤ 986
          · obtain rfl : N = 986 := by omega
            exact cvx986
          · by_cases h12 : N ≤ 987
            · obtain rfl : N = 987 := by omega
              exact cvx987
            · obtain rfl : N = 988 := by omega
              exact cvx988
  · by_cases h4 : N ≤ 999
    · by_cases h6 : N ≤ 993
      · by_cases h8 : N ≤ 990
        · by_cases h10 : N ≤ 989
          · obtain rfl : N = 989 := by omega
            exact cvx989
          · obtain rfl : N = 990 := by omega
            exact cvx990
        · by_cases h10 : N ≤ 991
          · obtain rfl : N = 991 := by omega
            exact cvx991
          · by_cases h12 : N ≤ 992
            · obtain rfl : N = 992 := by omega
              exact cvx992
            · obtain rfl : N = 993 := by omega
              exact cvx993
      · by_cases h8 : N ≤ 996
        · by_cases h10 : N ≤ 994
          · obtain rfl : N = 994 := by omega
            exact cvx994
          · by_cases h12 : N ≤ 995
            · obtain rfl : N = 995 := by omega
              exact cvx995
            · obtain rfl : N = 996 := by omega
              exact cvx996
        · by_cases h10 : N ≤ 997
          · obtain rfl : N = 997 := by omega
            exact cvx997
          · by_cases h12 : N ≤ 998
            · obtain rfl : N = 998 := by omega
              exact cvx998
            · obtain rfl : N = 999 := by omega
              exact cvx999
    · by_cases h6 : N ≤ 1004
      · by_cases h8 : N ≤ 1001
        · by_cases h10 : N ≤ 1000
          · obtain rfl : N = 1000 := by omega
            exact cvx1000
          · obtain rfl : N = 1001 := by omega
            exact cvx1001
        · by_cases h10 : N ≤ 1002
          · obtain rfl : N = 1002 := by omega
            exact cvx1002
          · by_cases h12 : N ≤ 1003
            · obtain rfl : N = 1003 := by omega
              exact cvx1003
            · obtain rfl : N = 1004 := by omega
              exact cvx1004
      · by_cases h8 : N ≤ 1007
        · by_cases h10 : N ≤ 1005
          · obtain rfl : N = 1005 := by omega
            exact cvx1005
          · by_cases h12 : N ≤ 1006
            · obtain rfl : N = 1006 := by omega
              exact cvx1006
            · obtain rfl : N = 1007 := by omega
              exact cvx1007
        · by_cases h10 : N ≤ 1008
          · obtain rfl : N = 1008 := by omega
            exact cvx1008
          · by_cases h12 : N ≤ 1009
            · obtain rfl : N = 1009 := by omega
              exact cvx1009
            · obtain rfl : N = 1010 := by omega
              exact cvx1010

theorem cen_968_1010 {N : ℕ} (h1 : 968 ≤ N) (h2 : N ≤ 1010) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 988
  · by_cases h4 : N ≤ 976
    · by_cases h6 : N ≤ 970
      · by_cases h8 : N ≤ 968
        · obtain rfl : N = 968 := by omega
          exact cen968
        · obtain rfl : N = 970 := by omega
          exact cen970
      · by_cases h8 : N ≤ 972
        · obtain rfl : N = 972 := by omega
          exact cen972
        · by_cases h10 : N ≤ 974
          · obtain rfl : N = 974 := by omega
            exact cen974
          · obtain rfl : N = 976 := by omega
            exact cen976
    · by_cases h6 : N ≤ 982
      · by_cases h8 : N ≤ 978
        · obtain rfl : N = 978 := by omega
          exact cen978
        · by_cases h10 : N ≤ 980
          · obtain rfl : N = 980 := by omega
            exact cen980
          · obtain rfl : N = 982 := by omega
            exact cen982
      · by_cases h8 : N ≤ 984
        · obtain rfl : N = 984 := by omega
          exact cen984
        · by_cases h10 : N ≤ 986
          · obtain rfl : N = 986 := by omega
            exact cen986
          · obtain rfl : N = 988 := by omega
            exact cen988
  · by_cases h4 : N ≤ 998
    · by_cases h6 : N ≤ 992
      · by_cases h8 : N ≤ 990
        · obtain rfl : N = 990 := by omega
          exact cen990
        · obtain rfl : N = 992 := by omega
          exact cen992
      · by_cases h8 : N ≤ 994
        · obtain rfl : N = 994 := by omega
          exact cen994
        · by_cases h10 : N ≤ 996
          · obtain rfl : N = 996 := by omega
            exact cen996
          · obtain rfl : N = 998 := by omega
            exact cen998
    · by_cases h6 : N ≤ 1004
      · by_cases h8 : N ≤ 1000
        · obtain rfl : N = 1000 := by omega
          exact cen1000
        · by_cases h10 : N ≤ 1002
          · obtain rfl : N = 1002 := by omega
            exact cen1002
          · obtain rfl : N = 1004 := by omega
            exact cen1004
      · by_cases h8 : N ≤ 1006
        · obtain rfl : N = 1006 := by omega
          exact cen1006
        · by_cases h10 : N ≤ 1008
          · obtain rfl : N = 1008 := by omega
            exact cen1008
          · obtain rfl : N = 1010 := by omega
            exact cen1010

end Kagey131.PaperD.T7
