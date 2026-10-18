import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 101, …, 300` (generated)

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

/-! ### `N = 101` -/

def pL101 : Prm := ⟨56, 26, 27, 103, 11, 18446744073709551616, 933800553287749216, 933800553287749216⟩
def pH101 : Prm := ⟨56, 26, 27, 103, 11, 18446744073709551616, 933870922031926880, 933870922031926880⟩
def pI101 : Prm := ⟨49, 23, 23, 103, 11, 18446744073709551616, 933800553287749216, 933870922031926880⟩
theorem L101_fin : (prmOK pL101 101 && ptTest pL101 (runFrom pL101 (fmask pL101) (cmask pL101) (hmask pL101) 1 100 (true, (init pL101), (init pL101))) 101 51 false) = true := by
  decide +kernel
theorem L101_ok : RunOK pL101 101 (runFrom pL101 (fmask pL101) (cmask pL101) (hmask pL101) 1 100 (true, (init pL101), (init pL101))) ∧ ptTest pL101 (runFrom pL101 (fmask pL101) (cmask pL101) (hmask pL101) 1 100 (true, (init pL101), (init pL101))) 101 51 false = true :=
  fin_run (runOK_init (prmOK_of_and L101_fin) true) (by decide) rfl L101_fin ptTest_fst
theorem H101_fin : (prmOK pH101 101 && ptTest pH101 (runFrom pH101 (fmask pH101) (cmask pH101) (hmask pH101) 1 100 (true, (init pH101), (init pH101))) 101 51 true) = true := by
  decide +kernel
theorem H101_ok : RunOK pH101 101 (runFrom pH101 (fmask pH101) (cmask pH101) (hmask pH101) 1 100 (true, (init pH101), (init pH101))) ∧ ptTest pH101 (runFrom pH101 (fmask pH101) (cmask pH101) (hmask pH101) 1 100 (true, (init pH101), (init pH101))) 101 51 true = true :=
  fin_run (runOK_init (prmOK_of_and H101_fin) true) (by decide) rfl H101_fin ptTest_fst
theorem I101_fin : (prmOK pI101 101 && intTest pI101 (runFrom pI101 (fmask pI101) (cmask pI101) (hmask pI101) 1 100 (true, (init pI101), (init pI101))) 101 7 false) = true := by
  decide +kernel
theorem I101_ok : RunOK pI101 101 (runFrom pI101 (fmask pI101) (cmask pI101) (hmask pI101) 1 100 (true, (init pI101), (init pI101))) ∧ intTest pI101 (runFrom pI101 (fmask pI101) (cmask pI101) (hmask pI101) 1 100 (true, (init pI101), (init pI101))) 101 7 false = true :=
  fin_run (runOK_init (prmOK_of_and I101_fin) true) (by decide) rfl I101_fin intTest_fst
theorem link101 : linkOK pL101 pH101 pI101 = true := by decide +kernel
theorem cvx101 : ConvexBetweenHumps 101 :=
  cvx_of L101_ok H101_ok I101_ok link101 (by decide)

/-! ### `N = 102` -/

def pL102 : Prm := ⟨56, 26, 27, 104, 11, 18446744073709551616, 927811362780010387, 927811362780010387⟩
def pH102 : Prm := ⟨56, 26, 27, 104, 11, 18446744073709551616, 927881731524188051, 927881731524188051⟩
def pI102 : Prm := ⟨49, 24, 22, 104, 11, 18446744073709551616, 927811362780010387, 927881731524188051⟩
theorem L102_fin : (prmOK pL102 102 && ptTest pL102 (runFrom pL102 (fmask pL102) (cmask pL102) (hmask pL102) 1 101 (true, (init pL102), (init pL102))) 102 51 false) = true := by
  decide +kernel
theorem L102_ok : RunOK pL102 102 (runFrom pL102 (fmask pL102) (cmask pL102) (hmask pL102) 1 101 (true, (init pL102), (init pL102))) ∧ ptTest pL102 (runFrom pL102 (fmask pL102) (cmask pL102) (hmask pL102) 1 101 (true, (init pL102), (init pL102))) 102 51 false = true :=
  fin_run (runOK_init (prmOK_of_and L102_fin) true) (by decide) rfl L102_fin ptTest_fst
theorem H102_fin : (prmOK pH102 102 && ptTest pH102 (runFrom pH102 (fmask pH102) (cmask pH102) (hmask pH102) 1 101 (true, (init pH102), (init pH102))) 102 51 true) = true := by
  decide +kernel
theorem H102_ok : RunOK pH102 102 (runFrom pH102 (fmask pH102) (cmask pH102) (hmask pH102) 1 101 (true, (init pH102), (init pH102))) ∧ ptTest pH102 (runFrom pH102 (fmask pH102) (cmask pH102) (hmask pH102) 1 101 (true, (init pH102), (init pH102))) 102 51 true = true :=
  fin_run (runOK_init (prmOK_of_and H102_fin) true) (by decide) rfl H102_fin ptTest_fst
theorem I102_fin : (prmOK pI102 102 && intTest pI102 (runFrom pI102 (fmask pI102) (cmask pI102) (hmask pI102) 1 101 (true, (init pI102), (init pI102))) 102 7 true) = true := by
  decide +kernel
theorem I102_ok : RunOK pI102 102 (runFrom pI102 (fmask pI102) (cmask pI102) (hmask pI102) 1 101 (true, (init pI102), (init pI102))) ∧ intTest pI102 (runFrom pI102 (fmask pI102) (cmask pI102) (hmask pI102) 1 101 (true, (init pI102), (init pI102))) 102 7 true = true :=
  fin_run (runOK_init (prmOK_of_and I102_fin) true) (by decide) rfl I102_fin intTest_fst
theorem link102 : linkOK pL102 pH102 pI102 = true := by decide +kernel
theorem cvx102 : ConvexBetweenHumps 102 :=
  cvx_of L102_ok H102_ok I102_ok link102 (by decide)
theorem cenlink102 : cenLinkOK pI102 102 = true := by decide +kernel
theorem cen102 : CenterUniqueMin 102 ∧ DipHyp 102 ∧ OnePointHyps 102 :=
  cen_of L102_ok H102_ok I102_ok link102 cenlink102

/-! ### `N = 103` -/

def pL103 : Prm := ⟨56, 26, 27, 105, 11, 18446744073709551616, 921806033787693641, 921806033787693641⟩
def pH103 : Prm := ⟨56, 26, 27, 105, 11, 18446744073709551616, 921876402531871305, 921876402531871305⟩
def pI103 : Prm := ⟨49, 24, 22, 105, 11, 18446744073709551616, 921806033787693641, 921876402531871305⟩
theorem L103_fin : (prmOK pL103 103 && ptTest pL103 (runFrom pL103 (fmask pL103) (cmask pL103) (hmask pL103) 1 102 (true, (init pL103), (init pL103))) 103 52 false) = true := by
  decide +kernel
theorem L103_ok : RunOK pL103 103 (runFrom pL103 (fmask pL103) (cmask pL103) (hmask pL103) 1 102 (true, (init pL103), (init pL103))) ∧ ptTest pL103 (runFrom pL103 (fmask pL103) (cmask pL103) (hmask pL103) 1 102 (true, (init pL103), (init pL103))) 103 52 false = true :=
  fin_run (runOK_init (prmOK_of_and L103_fin) true) (by decide) rfl L103_fin ptTest_fst
theorem H103_fin : (prmOK pH103 103 && ptTest pH103 (runFrom pH103 (fmask pH103) (cmask pH103) (hmask pH103) 1 102 (true, (init pH103), (init pH103))) 103 52 true) = true := by
  decide +kernel
theorem H103_ok : RunOK pH103 103 (runFrom pH103 (fmask pH103) (cmask pH103) (hmask pH103) 1 102 (true, (init pH103), (init pH103))) ∧ ptTest pH103 (runFrom pH103 (fmask pH103) (cmask pH103) (hmask pH103) 1 102 (true, (init pH103), (init pH103))) 103 52 true = true :=
  fin_run (runOK_init (prmOK_of_and H103_fin) true) (by decide) rfl H103_fin ptTest_fst
theorem I103_fin : (prmOK pI103 103 && intTest pI103 (runFrom pI103 (fmask pI103) (cmask pI103) (hmask pI103) 1 102 (true, (init pI103), (init pI103))) 103 7 false) = true := by
  decide +kernel
theorem I103_ok : RunOK pI103 103 (runFrom pI103 (fmask pI103) (cmask pI103) (hmask pI103) 1 102 (true, (init pI103), (init pI103))) ∧ intTest pI103 (runFrom pI103 (fmask pI103) (cmask pI103) (hmask pI103) 1 102 (true, (init pI103), (init pI103))) 103 7 false = true :=
  fin_run (runOK_init (prmOK_of_and I103_fin) true) (by decide) rfl I103_fin intTest_fst
theorem link103 : linkOK pL103 pH103 pI103 = true := by decide +kernel
theorem cvx103 : ConvexBetweenHumps 103 :=
  cvx_of L103_ok H103_ok I103_ok link103 (by decide)

/-! ### `N = 104` -/

def pL104 : Prm := ⟨56, 26, 27, 106, 11, 18446744073709551616, 915992580275042366, 915992580275042366⟩
def pH104 : Prm := ⟨56, 26, 27, 106, 11, 18446744073709551616, 916062949019220030, 916062949019220030⟩
def pI104 : Prm := ⟨49, 24, 22, 106, 11, 18446744073709551616, 915992580275042366, 916062949019220030⟩
theorem L104_fin : (prmOK pL104 104 && ptTest pL104 (runFrom pL104 (fmask pL104) (cmask pL104) (hmask pL104) 1 103 (true, (init pL104), (init pL104))) 104 52 false) = true := by
  decide +kernel
theorem L104_ok : RunOK pL104 104 (runFrom pL104 (fmask pL104) (cmask pL104) (hmask pL104) 1 103 (true, (init pL104), (init pL104))) ∧ ptTest pL104 (runFrom pL104 (fmask pL104) (cmask pL104) (hmask pL104) 1 103 (true, (init pL104), (init pL104))) 104 52 false = true :=
  fin_run (runOK_init (prmOK_of_and L104_fin) true) (by decide) rfl L104_fin ptTest_fst
theorem H104_fin : (prmOK pH104 104 && ptTest pH104 (runFrom pH104 (fmask pH104) (cmask pH104) (hmask pH104) 1 103 (true, (init pH104), (init pH104))) 104 52 true) = true := by
  decide +kernel
theorem H104_ok : RunOK pH104 104 (runFrom pH104 (fmask pH104) (cmask pH104) (hmask pH104) 1 103 (true, (init pH104), (init pH104))) ∧ ptTest pH104 (runFrom pH104 (fmask pH104) (cmask pH104) (hmask pH104) 1 103 (true, (init pH104), (init pH104))) 104 52 true = true :=
  fin_run (runOK_init (prmOK_of_and H104_fin) true) (by decide) rfl H104_fin ptTest_fst
theorem I104_fin : (prmOK pI104 104 && intTest pI104 (runFrom pI104 (fmask pI104) (cmask pI104) (hmask pI104) 1 103 (true, (init pI104), (init pI104))) 104 7 true) = true := by
  decide +kernel
theorem I104_ok : RunOK pI104 104 (runFrom pI104 (fmask pI104) (cmask pI104) (hmask pI104) 1 103 (true, (init pI104), (init pI104))) ∧ intTest pI104 (runFrom pI104 (fmask pI104) (cmask pI104) (hmask pI104) 1 103 (true, (init pI104), (init pI104))) 104 7 true = true :=
  fin_run (runOK_init (prmOK_of_and I104_fin) true) (by decide) rfl I104_fin intTest_fst
theorem link104 : linkOK pL104 pH104 pI104 = true := by decide +kernel
theorem cvx104 : ConvexBetweenHumps 104 :=
  cvx_of L104_ok H104_ok I104_ok link104 (by decide)
theorem cenlink104 : cenLinkOK pI104 104 = true := by decide +kernel
theorem cen104 : CenterUniqueMin 104 ∧ DipHyp 104 ∧ OnePointHyps 104 :=
  cen_of L104_ok H104_ok I104_ok link104 cenlink104

/-! ### `N = 105` -/

def pL105 : Prm := ⟨56, 26, 27, 107, 11, 18446744073709551616, 910164408247002565, 910164408247002565⟩
def pH105 : Prm := ⟨56, 26, 27, 107, 11, 18446744073709551616, 910234776991180229, 910234776991180229⟩
def pI105 : Prm := ⟨50, 24, 23, 107, 11, 18446744073709551616, 910164408247002565, 910234776991180229⟩
theorem L105_fin : (prmOK pL105 105 && ptTest pL105 (runFrom pL105 (fmask pL105) (cmask pL105) (hmask pL105) 1 104 (true, (init pL105), (init pL105))) 105 53 false) = true := by
  decide +kernel
theorem L105_ok : RunOK pL105 105 (runFrom pL105 (fmask pL105) (cmask pL105) (hmask pL105) 1 104 (true, (init pL105), (init pL105))) ∧ ptTest pL105 (runFrom pL105 (fmask pL105) (cmask pL105) (hmask pL105) 1 104 (true, (init pL105), (init pL105))) 105 53 false = true :=
  fin_run (runOK_init (prmOK_of_and L105_fin) true) (by decide) rfl L105_fin ptTest_fst
theorem H105_fin : (prmOK pH105 105 && ptTest pH105 (runFrom pH105 (fmask pH105) (cmask pH105) (hmask pH105) 1 104 (true, (init pH105), (init pH105))) 105 53 true) = true := by
  decide +kernel
theorem H105_ok : RunOK pH105 105 (runFrom pH105 (fmask pH105) (cmask pH105) (hmask pH105) 1 104 (true, (init pH105), (init pH105))) ∧ ptTest pH105 (runFrom pH105 (fmask pH105) (cmask pH105) (hmask pH105) 1 104 (true, (init pH105), (init pH105))) 105 53 true = true :=
  fin_run (runOK_init (prmOK_of_and H105_fin) true) (by decide) rfl H105_fin ptTest_fst
theorem I105_fin : (prmOK pI105 105 && intTest pI105 (runFrom pI105 (fmask pI105) (cmask pI105) (hmask pI105) 1 104 (true, (init pI105), (init pI105))) 105 7 false) = true := by
  decide +kernel
theorem I105_ok : RunOK pI105 105 (runFrom pI105 (fmask pI105) (cmask pI105) (hmask pI105) 1 104 (true, (init pI105), (init pI105))) ∧ intTest pI105 (runFrom pI105 (fmask pI105) (cmask pI105) (hmask pI105) 1 104 (true, (init pI105), (init pI105))) 105 7 false = true :=
  fin_run (runOK_init (prmOK_of_and I105_fin) true) (by decide) rfl I105_fin intTest_fst
theorem link105 : linkOK pL105 pH105 pI105 = true := by decide +kernel
theorem cvx105 : ConvexBetweenHumps 105 :=
  cvx_of L105_ok H105_ok I105_ok link105 (by decide)

/-! ### `N = 106` -/

def pL106 : Prm := ⟨56, 26, 27, 108, 11, 18446744073709551616, 904518582071034596, 904518582071034596⟩
def pH106 : Prm := ⟨56, 26, 27, 108, 11, 18446744073709551616, 904588950815212260, 904588950815212260⟩
def pI106 : Prm := ⟨50, 24, 23, 108, 11, 18446744073709551616, 904518582071034596, 904588950815212260⟩
theorem L106_fin : (prmOK pL106 106 && ptTest pL106 (runFrom pL106 (fmask pL106) (cmask pL106) (hmask pL106) 1 105 (true, (init pL106), (init pL106))) 106 53 false) = true := by
  decide +kernel
theorem L106_ok : RunOK pL106 106 (runFrom pL106 (fmask pL106) (cmask pL106) (hmask pL106) 1 105 (true, (init pL106), (init pL106))) ∧ ptTest pL106 (runFrom pL106 (fmask pL106) (cmask pL106) (hmask pL106) 1 105 (true, (init pL106), (init pL106))) 106 53 false = true :=
  fin_run (runOK_init (prmOK_of_and L106_fin) true) (by decide) rfl L106_fin ptTest_fst
theorem H106_fin : (prmOK pH106 106 && ptTest pH106 (runFrom pH106 (fmask pH106) (cmask pH106) (hmask pH106) 1 105 (true, (init pH106), (init pH106))) 106 53 true) = true := by
  decide +kernel
theorem H106_ok : RunOK pH106 106 (runFrom pH106 (fmask pH106) (cmask pH106) (hmask pH106) 1 105 (true, (init pH106), (init pH106))) ∧ ptTest pH106 (runFrom pH106 (fmask pH106) (cmask pH106) (hmask pH106) 1 105 (true, (init pH106), (init pH106))) 106 53 true = true :=
  fin_run (runOK_init (prmOK_of_and H106_fin) true) (by decide) rfl H106_fin ptTest_fst
theorem I106_fin : (prmOK pI106 106 && intTest pI106 (runFrom pI106 (fmask pI106) (cmask pI106) (hmask pI106) 1 105 (true, (init pI106), (init pI106))) 106 7 true) = true := by
  decide +kernel
theorem I106_ok : RunOK pI106 106 (runFrom pI106 (fmask pI106) (cmask pI106) (hmask pI106) 1 105 (true, (init pI106), (init pI106))) ∧ intTest pI106 (runFrom pI106 (fmask pI106) (cmask pI106) (hmask pI106) 1 105 (true, (init pI106), (init pI106))) 106 7 true = true :=
  fin_run (runOK_init (prmOK_of_and I106_fin) true) (by decide) rfl I106_fin intTest_fst
theorem link106 : linkOK pL106 pH106 pI106 = true := by decide +kernel
theorem cvx106 : ConvexBetweenHumps 106 :=
  cvx_of L106_ok H106_ok I106_ok link106 (by decide)
theorem cenlink106 : cenLinkOK pI106 106 = true := by decide +kernel
theorem cen106 : CenterUniqueMin 106 ∧ DipHyp 106 ∧ OnePointHyps 106 :=
  cen_of L106_ok H106_ok I106_ok link106 cenlink106

/-! ### `N = 107` -/

def pL107 : Prm := ⟨56, 26, 27, 109, 11, 18446744073709551616, 898859338975981645, 898859338975981645⟩
def pH107 : Prm := ⟨56, 26, 27, 109, 11, 18446744073709551616, 898929707720159309, 898929707720159309⟩
def pI107 : Prm := ⟨50, 24, 23, 109, 11, 18446744073709551616, 898859338975981645, 898929707720159309⟩
theorem L107_fin : (prmOK pL107 107 && ptTest pL107 (runFrom pL107 (fmask pL107) (cmask pL107) (hmask pL107) 1 106 (true, (init pL107), (init pL107))) 107 54 false) = true := by
  decide +kernel
theorem L107_ok : RunOK pL107 107 (runFrom pL107 (fmask pL107) (cmask pL107) (hmask pL107) 1 106 (true, (init pL107), (init pL107))) ∧ ptTest pL107 (runFrom pL107 (fmask pL107) (cmask pL107) (hmask pL107) 1 106 (true, (init pL107), (init pL107))) 107 54 false = true :=
  fin_run (runOK_init (prmOK_of_and L107_fin) true) (by decide) rfl L107_fin ptTest_fst
theorem H107_fin : (prmOK pH107 107 && ptTest pH107 (runFrom pH107 (fmask pH107) (cmask pH107) (hmask pH107) 1 106 (true, (init pH107), (init pH107))) 107 54 true) = true := by
  decide +kernel
theorem H107_ok : RunOK pH107 107 (runFrom pH107 (fmask pH107) (cmask pH107) (hmask pH107) 1 106 (true, (init pH107), (init pH107))) ∧ ptTest pH107 (runFrom pH107 (fmask pH107) (cmask pH107) (hmask pH107) 1 106 (true, (init pH107), (init pH107))) 107 54 true = true :=
  fin_run (runOK_init (prmOK_of_and H107_fin) true) (by decide) rfl H107_fin ptTest_fst
theorem I107_fin : (prmOK pI107 107 && intTest pI107 (runFrom pI107 (fmask pI107) (cmask pI107) (hmask pI107) 1 106 (true, (init pI107), (init pI107))) 107 7 false) = true := by
  decide +kernel
theorem I107_ok : RunOK pI107 107 (runFrom pI107 (fmask pI107) (cmask pI107) (hmask pI107) 1 106 (true, (init pI107), (init pI107))) ∧ intTest pI107 (runFrom pI107 (fmask pI107) (cmask pI107) (hmask pI107) 1 106 (true, (init pI107), (init pI107))) 107 7 false = true :=
  fin_run (runOK_init (prmOK_of_and I107_fin) true) (by decide) rfl I107_fin intTest_fst
theorem link107 : linkOK pL107 pH107 pI107 = true := by decide +kernel
theorem cvx107 : ConvexBetweenHumps 107 :=
  cvx_of L107_ok H107_ok I107_ok link107 (by decide)

/-! ### `N = 108` -/

def pL108 : Prm := ⟨56, 26, 27, 110, 11, 18446744073709551616, 893373539771313920, 893373539771313920⟩
def pH108 : Prm := ⟨56, 26, 27, 110, 11, 18446744073709551616, 893443908515491584, 893443908515491584⟩
def pI108 : Prm := ⟨50, 24, 23, 110, 11, 18446744073709551616, 893373539771313920, 893443908515491584⟩
theorem L108_fin : (prmOK pL108 108 && ptTest pL108 (runFrom pL108 (fmask pL108) (cmask pL108) (hmask pL108) 1 107 (true, (init pL108), (init pL108))) 108 54 false) = true := by
  decide +kernel
theorem L108_ok : RunOK pL108 108 (runFrom pL108 (fmask pL108) (cmask pL108) (hmask pL108) 1 107 (true, (init pL108), (init pL108))) ∧ ptTest pL108 (runFrom pL108 (fmask pL108) (cmask pL108) (hmask pL108) 1 107 (true, (init pL108), (init pL108))) 108 54 false = true :=
  fin_run (runOK_init (prmOK_of_and L108_fin) true) (by decide) rfl L108_fin ptTest_fst
theorem H108_fin : (prmOK pH108 108 && ptTest pH108 (runFrom pH108 (fmask pH108) (cmask pH108) (hmask pH108) 1 107 (true, (init pH108), (init pH108))) 108 54 true) = true := by
  decide +kernel
theorem H108_ok : RunOK pH108 108 (runFrom pH108 (fmask pH108) (cmask pH108) (hmask pH108) 1 107 (true, (init pH108), (init pH108))) ∧ ptTest pH108 (runFrom pH108 (fmask pH108) (cmask pH108) (hmask pH108) 1 107 (true, (init pH108), (init pH108))) 108 54 true = true :=
  fin_run (runOK_init (prmOK_of_and H108_fin) true) (by decide) rfl H108_fin ptTest_fst
theorem I108_fin : (prmOK pI108 108 && intTest pI108 (runFrom pI108 (fmask pI108) (cmask pI108) (hmask pI108) 1 107 (true, (init pI108), (init pI108))) 108 7 true) = true := by
  decide +kernel
theorem I108_ok : RunOK pI108 108 (runFrom pI108 (fmask pI108) (cmask pI108) (hmask pI108) 1 107 (true, (init pI108), (init pI108))) ∧ intTest pI108 (runFrom pI108 (fmask pI108) (cmask pI108) (hmask pI108) 1 107 (true, (init pI108), (init pI108))) 108 7 true = true :=
  fin_run (runOK_init (prmOK_of_and I108_fin) true) (by decide) rfl I108_fin intTest_fst
theorem link108 : linkOK pL108 pH108 pI108 = true := by decide +kernel
theorem cvx108 : ConvexBetweenHumps 108 :=
  cvx_of L108_ok H108_ok I108_ok link108 (by decide)
theorem cenlink108 : cenLinkOK pI108 108 = true := by decide +kernel
theorem cen108 : CenterUniqueMin 108 ∧ DipHyp 108 ∧ OnePointHyps 108 :=
  cen_of L108_ok H108_ok I108_ok link108 cenlink108

/-! ### `N = 109` -/

def pL109 : Prm := ⟨56, 26, 27, 111, 11, 18446744073709551616, 887875517730964524, 887875517730964524⟩
def pH109 : Prm := ⟨56, 26, 27, 111, 11, 18446744073709551616, 887945886475142188, 887945886475142188⟩
def pI109 : Prm := ⟨50, 24, 23, 111, 11, 18446744073709551616, 887875517730964524, 887945886475142188⟩
theorem L109_fin : (prmOK pL109 109 && ptTest pL109 (runFrom pL109 (fmask pL109) (cmask pL109) (hmask pL109) 1 108 (true, (init pL109), (init pL109))) 109 55 false) = true := by
  decide +kernel
theorem L109_ok : RunOK pL109 109 (runFrom pL109 (fmask pL109) (cmask pL109) (hmask pL109) 1 108 (true, (init pL109), (init pL109))) ∧ ptTest pL109 (runFrom pL109 (fmask pL109) (cmask pL109) (hmask pL109) 1 108 (true, (init pL109), (init pL109))) 109 55 false = true :=
  fin_run (runOK_init (prmOK_of_and L109_fin) true) (by decide) rfl L109_fin ptTest_fst
theorem H109_fin : (prmOK pH109 109 && ptTest pH109 (runFrom pH109 (fmask pH109) (cmask pH109) (hmask pH109) 1 108 (true, (init pH109), (init pH109))) 109 55 true) = true := by
  decide +kernel
theorem H109_ok : RunOK pH109 109 (runFrom pH109 (fmask pH109) (cmask pH109) (hmask pH109) 1 108 (true, (init pH109), (init pH109))) ∧ ptTest pH109 (runFrom pH109 (fmask pH109) (cmask pH109) (hmask pH109) 1 108 (true, (init pH109), (init pH109))) 109 55 true = true :=
  fin_run (runOK_init (prmOK_of_and H109_fin) true) (by decide) rfl H109_fin ptTest_fst
theorem I109_fin : (prmOK pI109 109 && intTest pI109 (runFrom pI109 (fmask pI109) (cmask pI109) (hmask pI109) 1 108 (true, (init pI109), (init pI109))) 109 7 false) = true := by
  decide +kernel
theorem I109_ok : RunOK pI109 109 (runFrom pI109 (fmask pI109) (cmask pI109) (hmask pI109) 1 108 (true, (init pI109), (init pI109))) ∧ intTest pI109 (runFrom pI109 (fmask pI109) (cmask pI109) (hmask pI109) 1 108 (true, (init pI109), (init pI109))) 109 7 false = true :=
  fin_run (runOK_init (prmOK_of_and I109_fin) true) (by decide) rfl I109_fin intTest_fst
theorem link109 : linkOK pL109 pH109 pI109 = true := by decide +kernel
theorem cvx109 : ConvexBetweenHumps 109 :=
  cvx_of L109_ok H109_ok I109_ok link109 (by decide)

/-! ### `N = 110` -/

def pL110 : Prm := ⟨56, 26, 27, 112, 11, 18446744073709551616, 882542614124246006, 882542614124246006⟩
def pH110 : Prm := ⟨56, 26, 27, 112, 11, 18446744073709551616, 882612982868423670, 882612982868423670⟩
def pI110 : Prm := ⟨51, 24, 24, 112, 11, 18446744073709551616, 882542614124246006, 882612982868423670⟩
theorem L110_fin : (prmOK pL110 110 && ptTest pL110 (runFrom pL110 (fmask pL110) (cmask pL110) (hmask pL110) 1 109 (true, (init pL110), (init pL110))) 110 55 false) = true := by
  decide +kernel
theorem L110_ok : RunOK pL110 110 (runFrom pL110 (fmask pL110) (cmask pL110) (hmask pL110) 1 109 (true, (init pL110), (init pL110))) ∧ ptTest pL110 (runFrom pL110 (fmask pL110) (cmask pL110) (hmask pL110) 1 109 (true, (init pL110), (init pL110))) 110 55 false = true :=
  fin_run (runOK_init (prmOK_of_and L110_fin) true) (by decide) rfl L110_fin ptTest_fst
theorem H110_fin : (prmOK pH110 110 && ptTest pH110 (runFrom pH110 (fmask pH110) (cmask pH110) (hmask pH110) 1 109 (true, (init pH110), (init pH110))) 110 55 true) = true := by
  decide +kernel
theorem H110_ok : RunOK pH110 110 (runFrom pH110 (fmask pH110) (cmask pH110) (hmask pH110) 1 109 (true, (init pH110), (init pH110))) ∧ ptTest pH110 (runFrom pH110 (fmask pH110) (cmask pH110) (hmask pH110) 1 109 (true, (init pH110), (init pH110))) 110 55 true = true :=
  fin_run (runOK_init (prmOK_of_and H110_fin) true) (by decide) rfl H110_fin ptTest_fst
theorem I110_fin : (prmOK pI110 110 && intTest pI110 (runFrom pI110 (fmask pI110) (cmask pI110) (hmask pI110) 1 109 (true, (init pI110), (init pI110))) 110 7 true) = true := by
  decide +kernel
theorem I110_ok : RunOK pI110 110 (runFrom pI110 (fmask pI110) (cmask pI110) (hmask pI110) 1 109 (true, (init pI110), (init pI110))) ∧ intTest pI110 (runFrom pI110 (fmask pI110) (cmask pI110) (hmask pI110) 1 109 (true, (init pI110), (init pI110))) 110 7 true = true :=
  fin_run (runOK_init (prmOK_of_and I110_fin) true) (by decide) rfl I110_fin intTest_fst
theorem link110 : linkOK pL110 pH110 pI110 = true := by decide +kernel
theorem cvx110 : ConvexBetweenHumps 110 :=
  cvx_of L110_ok H110_ok I110_ok link110 (by decide)
theorem cenlink110 : cenLinkOK pI110 110 = true := by decide +kernel
theorem cen110 : CenterUniqueMin 110 ∧ DipHyp 110 ∧ OnePointHyps 110 :=
  cen_of L110_ok H110_ok I110_ok link110 cenlink110

/-! ### `N = 111` -/

def pL111 : Prm := ⟨56, 26, 27, 113, 11, 18446744073709551616, 877198583997874474, 877198583997874474⟩
def pH111 : Prm := ⟨57, 27, 27, 113, 11, 18446744073709551616, 877268952742052138, 877268952742052138⟩
def pI111 : Prm := ⟨51, 24, 24, 113, 11, 18446744073709551616, 877198583997874474, 877268952742052138⟩
theorem L111_fin : (prmOK pL111 111 && ptTest pL111 (runFrom pL111 (fmask pL111) (cmask pL111) (hmask pL111) 1 110 (true, (init pL111), (init pL111))) 111 56 false) = true := by
  decide +kernel
theorem L111_ok : RunOK pL111 111 (runFrom pL111 (fmask pL111) (cmask pL111) (hmask pL111) 1 110 (true, (init pL111), (init pL111))) ∧ ptTest pL111 (runFrom pL111 (fmask pL111) (cmask pL111) (hmask pL111) 1 110 (true, (init pL111), (init pL111))) 111 56 false = true :=
  fin_run (runOK_init (prmOK_of_and L111_fin) true) (by decide) rfl L111_fin ptTest_fst
theorem H111_fin : (prmOK pH111 111 && ptTest pH111 (runFrom pH111 (fmask pH111) (cmask pH111) (hmask pH111) 1 110 (true, (init pH111), (init pH111))) 111 56 true) = true := by
  decide +kernel
theorem H111_ok : RunOK pH111 111 (runFrom pH111 (fmask pH111) (cmask pH111) (hmask pH111) 1 110 (true, (init pH111), (init pH111))) ∧ ptTest pH111 (runFrom pH111 (fmask pH111) (cmask pH111) (hmask pH111) 1 110 (true, (init pH111), (init pH111))) 111 56 true = true :=
  fin_run (runOK_init (prmOK_of_and H111_fin) true) (by decide) rfl H111_fin ptTest_fst
theorem I111_fin : (prmOK pI111 111 && intTest pI111 (runFrom pI111 (fmask pI111) (cmask pI111) (hmask pI111) 1 110 (true, (init pI111), (init pI111))) 111 7 false) = true := by
  decide +kernel
theorem I111_ok : RunOK pI111 111 (runFrom pI111 (fmask pI111) (cmask pI111) (hmask pI111) 1 110 (true, (init pI111), (init pI111))) ∧ intTest pI111 (runFrom pI111 (fmask pI111) (cmask pI111) (hmask pI111) 1 110 (true, (init pI111), (init pI111))) 111 7 false = true :=
  fin_run (runOK_init (prmOK_of_and I111_fin) true) (by decide) rfl I111_fin intTest_fst
theorem link111 : linkOK pL111 pH111 pI111 = true := by decide +kernel
theorem cvx111 : ConvexBetweenHumps 111 :=
  cvx_of L111_ok H111_ok I111_ok link111 (by decide)

/-! ### `N = 112` -/

def pL112 : Prm := ⟨57, 27, 27, 114, 11, 18446744073709551616, 872011877137595438, 872011877137595438⟩
def pH112 : Prm := ⟨57, 27, 27, 114, 11, 18446744073709551616, 872082245881773102, 872082245881773102⟩
def pI112 : Prm := ⟨51, 24, 24, 114, 11, 18446744073709551616, 872011877137595438, 872082245881773102⟩
theorem L112_fin : (prmOK pL112 112 && ptTest pL112 (runFrom pL112 (fmask pL112) (cmask pL112) (hmask pL112) 1 111 (true, (init pL112), (init pL112))) 112 56 false) = true := by
  decide +kernel
theorem L112_ok : RunOK pL112 112 (runFrom pL112 (fmask pL112) (cmask pL112) (hmask pL112) 1 111 (true, (init pL112), (init pL112))) ∧ ptTest pL112 (runFrom pL112 (fmask pL112) (cmask pL112) (hmask pL112) 1 111 (true, (init pL112), (init pL112))) 112 56 false = true :=
  fin_run (runOK_init (prmOK_of_and L112_fin) true) (by decide) rfl L112_fin ptTest_fst
theorem H112_fin : (prmOK pH112 112 && ptTest pH112 (runFrom pH112 (fmask pH112) (cmask pH112) (hmask pH112) 1 111 (true, (init pH112), (init pH112))) 112 56 true) = true := by
  decide +kernel
theorem H112_ok : RunOK pH112 112 (runFrom pH112 (fmask pH112) (cmask pH112) (hmask pH112) 1 111 (true, (init pH112), (init pH112))) ∧ ptTest pH112 (runFrom pH112 (fmask pH112) (cmask pH112) (hmask pH112) 1 111 (true, (init pH112), (init pH112))) 112 56 true = true :=
  fin_run (runOK_init (prmOK_of_and H112_fin) true) (by decide) rfl H112_fin ptTest_fst
theorem I112_fin : (prmOK pI112 112 && intTest pI112 (runFrom pI112 (fmask pI112) (cmask pI112) (hmask pI112) 1 111 (true, (init pI112), (init pI112))) 112 7 true) = true := by
  decide +kernel
theorem I112_ok : RunOK pI112 112 (runFrom pI112 (fmask pI112) (cmask pI112) (hmask pI112) 1 111 (true, (init pI112), (init pI112))) ∧ intTest pI112 (runFrom pI112 (fmask pI112) (cmask pI112) (hmask pI112) 1 111 (true, (init pI112), (init pI112))) 112 7 true = true :=
  fin_run (runOK_init (prmOK_of_and I112_fin) true) (by decide) rfl I112_fin intTest_fst
theorem link112 : linkOK pL112 pH112 pI112 = true := by decide +kernel
theorem cvx112 : ConvexBetweenHumps 112 :=
  cvx_of L112_ok H112_ok I112_ok link112 (by decide)
theorem cenlink112 : cenLinkOK pI112 112 = true := by decide +kernel
theorem cen112 : CenterUniqueMin 112 ∧ DipHyp 112 ∧ OnePointHyps 112 :=
  cen_of L112_ok H112_ok I112_ok link112 cenlink112

/-! ### `N = 113` -/

def pL113 : Prm := ⟨56, 26, 27, 115, 11, 18446744073709551616, 866815051064573222, 866815051064573222⟩
def pH113 : Prm := ⟨56, 26, 27, 115, 11, 18446744073709551616, 866885419808750886, 866885419808750886⟩
def pI113 : Prm := ⟨51, 24, 24, 115, 11, 18446744073709551616, 866815051064573222, 866885419808750886⟩
theorem L113_fin : (prmOK pL113 113 && ptTest pL113 (runFrom pL113 (fmask pL113) (cmask pL113) (hmask pL113) 1 112 (true, (init pL113), (init pL113))) 113 57 false) = true := by
  decide +kernel
theorem L113_ok : RunOK pL113 113 (runFrom pL113 (fmask pL113) (cmask pL113) (hmask pL113) 1 112 (true, (init pL113), (init pL113))) ∧ ptTest pL113 (runFrom pL113 (fmask pL113) (cmask pL113) (hmask pL113) 1 112 (true, (init pL113), (init pL113))) 113 57 false = true :=
  fin_run (runOK_init (prmOK_of_and L113_fin) true) (by decide) rfl L113_fin ptTest_fst
theorem H113_fin : (prmOK pH113 113 && ptTest pH113 (runFrom pH113 (fmask pH113) (cmask pH113) (hmask pH113) 1 112 (true, (init pH113), (init pH113))) 113 57 true) = true := by
  decide +kernel
theorem H113_ok : RunOK pH113 113 (runFrom pH113 (fmask pH113) (cmask pH113) (hmask pH113) 1 112 (true, (init pH113), (init pH113))) ∧ ptTest pH113 (runFrom pH113 (fmask pH113) (cmask pH113) (hmask pH113) 1 112 (true, (init pH113), (init pH113))) 113 57 true = true :=
  fin_run (runOK_init (prmOK_of_and H113_fin) true) (by decide) rfl H113_fin ptTest_fst
theorem I113_fin : (prmOK pI113 113 && intTest pI113 (runFrom pI113 (fmask pI113) (cmask pI113) (hmask pI113) 1 112 (true, (init pI113), (init pI113))) 113 7 false) = true := by
  decide +kernel
theorem I113_ok : RunOK pI113 113 (runFrom pI113 (fmask pI113) (cmask pI113) (hmask pI113) 1 112 (true, (init pI113), (init pI113))) ∧ intTest pI113 (runFrom pI113 (fmask pI113) (cmask pI113) (hmask pI113) 1 112 (true, (init pI113), (init pI113))) 113 7 false = true :=
  fin_run (runOK_init (prmOK_of_and I113_fin) true) (by decide) rfl I113_fin intTest_fst
theorem link113 : linkOK pL113 pH113 pI113 = true := by decide +kernel
theorem cvx113 : ConvexBetweenHumps 113 :=
  cvx_of L113_ok H113_ok I113_ok link113 (by decide)

/-! ### `N = 114` -/

def pL114 : Prm := ⟨57, 27, 27, 116, 11, 18446744073709551616, 861768241558191093, 861768241558191093⟩
def pH114 : Prm := ⟨57, 27, 27, 116, 11, 18446744073709551616, 861838610302368757, 861838610302368757⟩
def pI114 : Prm := ⟨51, 25, 23, 116, 11, 18446744073709551616, 861768241558191093, 861838610302368757⟩
theorem L114_fin : (prmOK pL114 114 && ptTest pL114 (runFrom pL114 (fmask pL114) (cmask pL114) (hmask pL114) 1 113 (true, (init pL114), (init pL114))) 114 57 false) = true := by
  decide +kernel
theorem L114_ok : RunOK pL114 114 (runFrom pL114 (fmask pL114) (cmask pL114) (hmask pL114) 1 113 (true, (init pL114), (init pL114))) ∧ ptTest pL114 (runFrom pL114 (fmask pL114) (cmask pL114) (hmask pL114) 1 113 (true, (init pL114), (init pL114))) 114 57 false = true :=
  fin_run (runOK_init (prmOK_of_and L114_fin) true) (by decide) rfl L114_fin ptTest_fst
theorem H114_fin : (prmOK pH114 114 && ptTest pH114 (runFrom pH114 (fmask pH114) (cmask pH114) (hmask pH114) 1 113 (true, (init pH114), (init pH114))) 114 57 true) = true := by
  decide +kernel
theorem H114_ok : RunOK pH114 114 (runFrom pH114 (fmask pH114) (cmask pH114) (hmask pH114) 1 113 (true, (init pH114), (init pH114))) ∧ ptTest pH114 (runFrom pH114 (fmask pH114) (cmask pH114) (hmask pH114) 1 113 (true, (init pH114), (init pH114))) 114 57 true = true :=
  fin_run (runOK_init (prmOK_of_and H114_fin) true) (by decide) rfl H114_fin ptTest_fst
theorem I114_fin : (prmOK pI114 114 && intTest pI114 (runFrom pI114 (fmask pI114) (cmask pI114) (hmask pI114) 1 113 (true, (init pI114), (init pI114))) 114 7 true) = true := by
  decide +kernel
theorem I114_ok : RunOK pI114 114 (runFrom pI114 (fmask pI114) (cmask pI114) (hmask pI114) 1 113 (true, (init pI114), (init pI114))) ∧ intTest pI114 (runFrom pI114 (fmask pI114) (cmask pI114) (hmask pI114) 1 113 (true, (init pI114), (init pI114))) 114 7 true = true :=
  fin_run (runOK_init (prmOK_of_and I114_fin) true) (by decide) rfl I114_fin intTest_fst
theorem link114 : linkOK pL114 pH114 pI114 = true := by decide +kernel
theorem cvx114 : ConvexBetweenHumps 114 :=
  cvx_of L114_ok H114_ok I114_ok link114 (by decide)
theorem cenlink114 : cenLinkOK pI114 114 = true := by decide +kernel
theorem cen114 : CenterUniqueMin 114 ∧ DipHyp 114 ∧ OnePointHyps 114 :=
  cen_of L114_ok H114_ok I114_ok link114 cenlink114

/-! ### `N = 115` -/

def pL115 : Prm := ⟨57, 27, 27, 117, 11, 18446744073709551616, 856712239019205875, 856712239019205875⟩
def pH115 : Prm := ⟨57, 27, 27, 117, 11, 18446744073709551616, 856782607763383539, 856782607763383539⟩
def pI115 : Prm := ⟨51, 25, 23, 117, 11, 18446744073709551616, 856712239019205875, 856782607763383539⟩
theorem L115_fin : (prmOK pL115 115 && ptTest pL115 (runFrom pL115 (fmask pL115) (cmask pL115) (hmask pL115) 1 114 (true, (init pL115), (init pL115))) 115 58 false) = true := by
  decide +kernel
theorem L115_ok : RunOK pL115 115 (runFrom pL115 (fmask pL115) (cmask pL115) (hmask pL115) 1 114 (true, (init pL115), (init pL115))) ∧ ptTest pL115 (runFrom pL115 (fmask pL115) (cmask pL115) (hmask pL115) 1 114 (true, (init pL115), (init pL115))) 115 58 false = true :=
  fin_run (runOK_init (prmOK_of_and L115_fin) true) (by decide) rfl L115_fin ptTest_fst
theorem H115_fin : (prmOK pH115 115 && ptTest pH115 (runFrom pH115 (fmask pH115) (cmask pH115) (hmask pH115) 1 114 (true, (init pH115), (init pH115))) 115 58 true) = true := by
  decide +kernel
theorem H115_ok : RunOK pH115 115 (runFrom pH115 (fmask pH115) (cmask pH115) (hmask pH115) 1 114 (true, (init pH115), (init pH115))) ∧ ptTest pH115 (runFrom pH115 (fmask pH115) (cmask pH115) (hmask pH115) 1 114 (true, (init pH115), (init pH115))) 115 58 true = true :=
  fin_run (runOK_init (prmOK_of_and H115_fin) true) (by decide) rfl H115_fin ptTest_fst
theorem I115_fin : (prmOK pI115 115 && intTest pI115 (runFrom pI115 (fmask pI115) (cmask pI115) (hmask pI115) 1 114 (true, (init pI115), (init pI115))) 115 7 false) = true := by
  decide +kernel
theorem I115_ok : RunOK pI115 115 (runFrom pI115 (fmask pI115) (cmask pI115) (hmask pI115) 1 114 (true, (init pI115), (init pI115))) ∧ intTest pI115 (runFrom pI115 (fmask pI115) (cmask pI115) (hmask pI115) 1 114 (true, (init pI115), (init pI115))) 115 7 false = true :=
  fin_run (runOK_init (prmOK_of_and I115_fin) true) (by decide) rfl I115_fin intTest_fst
theorem link115 : linkOK pL115 pH115 pI115 = true := by decide +kernel
theorem cvx115 : ConvexBetweenHumps 115 :=
  cvx_of L115_ok H115_ok I115_ok link115 (by decide)

/-! ### `N = 116` -/

def pL116 : Prm := ⟨59, 28, 28, 118, 11, 18446744073709551616, 851816989093498099, 851816989093498099⟩
def pH116 : Prm := ⟨59, 28, 28, 118, 11, 18446744073709551616, 851852173465586931, 851852173465586931⟩
def pI116 : Prm := ⟨51, 24, 24, 118, 11, 18446744073709551616, 851816989093498099, 851852173465586931⟩
theorem L116_fin : (prmOK pL116 116 && ptTest pL116 (runFrom pL116 (fmask pL116) (cmask pL116) (hmask pL116) 1 115 (true, (init pL116), (init pL116))) 116 58 false) = true := by
  decide +kernel
theorem L116_ok : RunOK pL116 116 (runFrom pL116 (fmask pL116) (cmask pL116) (hmask pL116) 1 115 (true, (init pL116), (init pL116))) ∧ ptTest pL116 (runFrom pL116 (fmask pL116) (cmask pL116) (hmask pL116) 1 115 (true, (init pL116), (init pL116))) 116 58 false = true :=
  fin_run (runOK_init (prmOK_of_and L116_fin) true) (by decide) rfl L116_fin ptTest_fst
theorem H116_fin : (prmOK pH116 116 && ptTest pH116 (runFrom pH116 (fmask pH116) (cmask pH116) (hmask pH116) 1 115 (true, (init pH116), (init pH116))) 116 58 true) = true := by
  decide +kernel
theorem H116_ok : RunOK pH116 116 (runFrom pH116 (fmask pH116) (cmask pH116) (hmask pH116) 1 115 (true, (init pH116), (init pH116))) ∧ ptTest pH116 (runFrom pH116 (fmask pH116) (cmask pH116) (hmask pH116) 1 115 (true, (init pH116), (init pH116))) 116 58 true = true :=
  fin_run (runOK_init (prmOK_of_and H116_fin) true) (by decide) rfl H116_fin ptTest_fst
theorem I116_fin : (prmOK pI116 116 && intTest pI116 (runFrom pI116 (fmask pI116) (cmask pI116) (hmask pI116) 1 115 (true, (init pI116), (init pI116))) 116 7 true) = true := by
  decide +kernel
theorem I116_ok : RunOK pI116 116 (runFrom pI116 (fmask pI116) (cmask pI116) (hmask pI116) 1 115 (true, (init pI116), (init pI116))) ∧ intTest pI116 (runFrom pI116 (fmask pI116) (cmask pI116) (hmask pI116) 1 115 (true, (init pI116), (init pI116))) 116 7 true = true :=
  fin_run (runOK_init (prmOK_of_and I116_fin) true) (by decide) rfl I116_fin intTest_fst
theorem link116 : linkOK pL116 pH116 pI116 = true := by decide +kernel
theorem cvx116 : ConvexBetweenHumps 116 :=
  cvx_of L116_ok H116_ok I116_ok link116 (by decide)
theorem cenlink116 : cenLinkOK pI116 116 = true := by decide +kernel
theorem cen116 : CenterUniqueMin 116 ∧ DipHyp 116 ∧ OnePointHyps 116 :=
  cen_of L116_ok H116_ok I116_ok link116 cenlink116

/-! ### `N = 117` -/

def pL117 : Prm := ⟨59, 28, 28, 119, 11, 18446744073709551616, 846895806106372756, 846895806106372756⟩
def pH117 : Prm := ⟨59, 28, 28, 119, 11, 18446744073709551616, 846930990478461588, 846930990478461588⟩
def pI117 : Prm := ⟨50, 24, 23, 119, 11, 18446744073709551616, 846895806106372756, 846930990478461588⟩
theorem L117_fin : (prmOK pL117 117 && ptTest pL117 (runFrom pL117 (fmask pL117) (cmask pL117) (hmask pL117) 1 116 (true, (init pL117), (init pL117))) 117 59 false) = true := by
  decide +kernel
theorem L117_ok : RunOK pL117 117 (runFrom pL117 (fmask pL117) (cmask pL117) (hmask pL117) 1 116 (true, (init pL117), (init pL117))) ∧ ptTest pL117 (runFrom pL117 (fmask pL117) (cmask pL117) (hmask pL117) 1 116 (true, (init pL117), (init pL117))) 117 59 false = true :=
  fin_run (runOK_init (prmOK_of_and L117_fin) true) (by decide) rfl L117_fin ptTest_fst
theorem H117_fin : (prmOK pH117 117 && ptTest pH117 (runFrom pH117 (fmask pH117) (cmask pH117) (hmask pH117) 1 116 (true, (init pH117), (init pH117))) 117 59 true) = true := by
  decide +kernel
theorem H117_ok : RunOK pH117 117 (runFrom pH117 (fmask pH117) (cmask pH117) (hmask pH117) 1 116 (true, (init pH117), (init pH117))) ∧ ptTest pH117 (runFrom pH117 (fmask pH117) (cmask pH117) (hmask pH117) 1 116 (true, (init pH117), (init pH117))) 117 59 true = true :=
  fin_run (runOK_init (prmOK_of_and H117_fin) true) (by decide) rfl H117_fin ptTest_fst
theorem I117_fin : (prmOK pI117 117 && intTest pI117 (runFrom pI117 (fmask pI117) (cmask pI117) (hmask pI117) 1 116 (true, (init pI117), (init pI117))) 117 7 false) = true := by
  decide +kernel
theorem I117_ok : RunOK pI117 117 (runFrom pI117 (fmask pI117) (cmask pI117) (hmask pI117) 1 116 (true, (init pI117), (init pI117))) ∧ intTest pI117 (runFrom pI117 (fmask pI117) (cmask pI117) (hmask pI117) 1 116 (true, (init pI117), (init pI117))) 117 7 false = true :=
  fin_run (runOK_init (prmOK_of_and I117_fin) true) (by decide) rfl I117_fin intTest_fst
theorem link117 : linkOK pL117 pH117 pI117 = true := by decide +kernel
theorem cvx117 : ConvexBetweenHumps 117 :=
  cvx_of L117_ok H117_ok I117_ok link117 (by decide)

/-! ### `N = 118` -/

def pL118 : Prm := ⟨59, 28, 28, 120, 11, 18446744073709551616, 842111343549921503, 842111343549921503⟩
def pH118 : Prm := ⟨59, 28, 28, 120, 11, 18446744073709551616, 842146527922010335, 842146527922010335⟩
def pI118 : Prm := ⟨51, 24, 24, 120, 11, 18446744073709551616, 842111343549921503, 842146527922010335⟩
theorem L118_fin : (prmOK pL118 118 && ptTest pL118 (runFrom pL118 (fmask pL118) (cmask pL118) (hmask pL118) 1 117 (true, (init pL118), (init pL118))) 118 59 false) = true := by
  decide +kernel
theorem L118_ok : RunOK pL118 118 (runFrom pL118 (fmask pL118) (cmask pL118) (hmask pL118) 1 117 (true, (init pL118), (init pL118))) ∧ ptTest pL118 (runFrom pL118 (fmask pL118) (cmask pL118) (hmask pL118) 1 117 (true, (init pL118), (init pL118))) 118 59 false = true :=
  fin_run (runOK_init (prmOK_of_and L118_fin) true) (by decide) rfl L118_fin ptTest_fst
theorem H118_fin : (prmOK pH118 118 && ptTest pH118 (runFrom pH118 (fmask pH118) (cmask pH118) (hmask pH118) 1 117 (true, (init pH118), (init pH118))) 118 59 true) = true := by
  decide +kernel
theorem H118_ok : RunOK pH118 118 (runFrom pH118 (fmask pH118) (cmask pH118) (hmask pH118) 1 117 (true, (init pH118), (init pH118))) ∧ ptTest pH118 (runFrom pH118 (fmask pH118) (cmask pH118) (hmask pH118) 1 117 (true, (init pH118), (init pH118))) 118 59 true = true :=
  fin_run (runOK_init (prmOK_of_and H118_fin) true) (by decide) rfl H118_fin ptTest_fst
theorem I118_fin : (prmOK pI118 118 && intTest pI118 (runFrom pI118 (fmask pI118) (cmask pI118) (hmask pI118) 1 117 (true, (init pI118), (init pI118))) 118 7 true) = true := by
  decide +kernel
theorem I118_ok : RunOK pI118 118 (runFrom pI118 (fmask pI118) (cmask pI118) (hmask pI118) 1 117 (true, (init pI118), (init pI118))) ∧ intTest pI118 (runFrom pI118 (fmask pI118) (cmask pI118) (hmask pI118) 1 117 (true, (init pI118), (init pI118))) 118 7 true = true :=
  fin_run (runOK_init (prmOK_of_and I118_fin) true) (by decide) rfl I118_fin intTest_fst
theorem link118 : linkOK pL118 pH118 pI118 = true := by decide +kernel
theorem cvx118 : ConvexBetweenHumps 118 :=
  cvx_of L118_ok H118_ok I118_ok link118 (by decide)
theorem cenlink118 : cenLinkOK pI118 118 = true := by decide +kernel
theorem cen118 : CenterUniqueMin 118 ∧ DipHyp 118 ∧ OnePointHyps 118 :=
  cen_of L118_ok H118_ok I118_ok link118 cenlink118

/-! ### `N = 119` -/

def pL119 : Prm := ⟨59, 28, 28, 121, 11, 18446744073709551616, 837319324663306088, 837319324663306088⟩
def pH119 : Prm := ⟨59, 28, 28, 121, 11, 18446744073709551616, 837354509035394920, 837354509035394920⟩
def pI119 : Prm := ⟨51, 24, 24, 121, 11, 18446744073709551616, 837319324663306088, 837354509035394920⟩
theorem L119_fin : (prmOK pL119 119 && ptTest pL119 (runFrom pL119 (fmask pL119) (cmask pL119) (hmask pL119) 1 118 (true, (init pL119), (init pL119))) 119 60 false) = true := by
  decide +kernel
theorem L119_ok : RunOK pL119 119 (runFrom pL119 (fmask pL119) (cmask pL119) (hmask pL119) 1 118 (true, (init pL119), (init pL119))) ∧ ptTest pL119 (runFrom pL119 (fmask pL119) (cmask pL119) (hmask pL119) 1 118 (true, (init pL119), (init pL119))) 119 60 false = true :=
  fin_run (runOK_init (prmOK_of_and L119_fin) true) (by decide) rfl L119_fin ptTest_fst
theorem H119_fin : (prmOK pH119 119 && ptTest pH119 (runFrom pH119 (fmask pH119) (cmask pH119) (hmask pH119) 1 118 (true, (init pH119), (init pH119))) 119 60 true) = true := by
  decide +kernel
theorem H119_ok : RunOK pH119 119 (runFrom pH119 (fmask pH119) (cmask pH119) (hmask pH119) 1 118 (true, (init pH119), (init pH119))) ∧ ptTest pH119 (runFrom pH119 (fmask pH119) (cmask pH119) (hmask pH119) 1 118 (true, (init pH119), (init pH119))) 119 60 true = true :=
  fin_run (runOK_init (prmOK_of_and H119_fin) true) (by decide) rfl H119_fin ptTest_fst
theorem I119_fin : (prmOK pI119 119 && intTest pI119 (runFrom pI119 (fmask pI119) (cmask pI119) (hmask pI119) 1 118 (true, (init pI119), (init pI119))) 119 7 false) = true := by
  decide +kernel
theorem I119_ok : RunOK pI119 119 (runFrom pI119 (fmask pI119) (cmask pI119) (hmask pI119) 1 118 (true, (init pI119), (init pI119))) ∧ intTest pI119 (runFrom pI119 (fmask pI119) (cmask pI119) (hmask pI119) 1 118 (true, (init pI119), (init pI119))) 119 7 false = true :=
  fin_run (runOK_init (prmOK_of_and I119_fin) true) (by decide) rfl I119_fin intTest_fst
theorem link119 : linkOK pL119 pH119 pI119 = true := by decide +kernel
theorem cvx119 : ConvexBetweenHumps 119 :=
  cvx_of L119_ok H119_ok I119_ok link119 (by decide)

/-! ### `N = 120` -/

def pL120 : Prm := ⟨59, 28, 28, 122, 11, 18446744073709551616, 832657971057110867, 832657971057110867⟩
def pH120 : Prm := ⟨59, 28, 28, 122, 11, 18446744073709551616, 832693155429199699, 832693155429199699⟩
def pI120 : Prm := ⟨51, 25, 23, 122, 11, 18446744073709551616, 832657971057110867, 832693155429199699⟩
theorem L120_fin : (prmOK pL120 120 && ptTest pL120 (runFrom pL120 (fmask pL120) (cmask pL120) (hmask pL120) 1 119 (true, (init pL120), (init pL120))) 120 60 false) = true := by
  decide +kernel
theorem L120_ok : RunOK pL120 120 (runFrom pL120 (fmask pL120) (cmask pL120) (hmask pL120) 1 119 (true, (init pL120), (init pL120))) ∧ ptTest pL120 (runFrom pL120 (fmask pL120) (cmask pL120) (hmask pL120) 1 119 (true, (init pL120), (init pL120))) 120 60 false = true :=
  fin_run (runOK_init (prmOK_of_and L120_fin) true) (by decide) rfl L120_fin ptTest_fst
theorem H120_fin : (prmOK pH120 120 && ptTest pH120 (runFrom pH120 (fmask pH120) (cmask pH120) (hmask pH120) 1 119 (true, (init pH120), (init pH120))) 120 60 true) = true := by
  decide +kernel
theorem H120_ok : RunOK pH120 120 (runFrom pH120 (fmask pH120) (cmask pH120) (hmask pH120) 1 119 (true, (init pH120), (init pH120))) ∧ ptTest pH120 (runFrom pH120 (fmask pH120) (cmask pH120) (hmask pH120) 1 119 (true, (init pH120), (init pH120))) 120 60 true = true :=
  fin_run (runOK_init (prmOK_of_and H120_fin) true) (by decide) rfl H120_fin ptTest_fst
theorem I120_fin : (prmOK pI120 120 && intTest pI120 (runFrom pI120 (fmask pI120) (cmask pI120) (hmask pI120) 1 119 (true, (init pI120), (init pI120))) 120 7 true) = true := by
  decide +kernel
theorem I120_ok : RunOK pI120 120 (runFrom pI120 (fmask pI120) (cmask pI120) (hmask pI120) 1 119 (true, (init pI120), (init pI120))) ∧ intTest pI120 (runFrom pI120 (fmask pI120) (cmask pI120) (hmask pI120) 1 119 (true, (init pI120), (init pI120))) 120 7 true = true :=
  fin_run (runOK_init (prmOK_of_and I120_fin) true) (by decide) rfl I120_fin intTest_fst
theorem link120 : linkOK pL120 pH120 pI120 = true := by decide +kernel
theorem cvx120 : ConvexBetweenHumps 120 :=
  cvx_of L120_ok H120_ok I120_ok link120 (by decide)
theorem cenlink120 : cenLinkOK pI120 120 = true := by decide +kernel
theorem cen120 : CenterUniqueMin 120 ∧ DipHyp 120 ∧ OnePointHyps 120 :=
  cen_of L120_ok H120_ok I120_ok link120 cenlink120

/-! ### `N = 121` -/

def pL121 : Prm := ⟨59, 28, 28, 123, 11, 18446744073709551616, 827989783846844353, 827989783846844353⟩
def pH121 : Prm := ⟨59, 28, 28, 123, 11, 18446744073709551616, 828024968218933185, 828024968218933185⟩
def pI121 : Prm := ⟨51, 25, 23, 123, 11, 18446744073709551616, 827989783846844353, 828024968218933185⟩
theorem L121_fin : (prmOK pL121 121 && ptTest pL121 (runFrom pL121 (fmask pL121) (cmask pL121) (hmask pL121) 1 120 (true, (init pL121), (init pL121))) 121 61 false) = true := by
  decide +kernel
theorem L121_ok : RunOK pL121 121 (runFrom pL121 (fmask pL121) (cmask pL121) (hmask pL121) 1 120 (true, (init pL121), (init pL121))) ∧ ptTest pL121 (runFrom pL121 (fmask pL121) (cmask pL121) (hmask pL121) 1 120 (true, (init pL121), (init pL121))) 121 61 false = true :=
  fin_run (runOK_init (prmOK_of_and L121_fin) true) (by decide) rfl L121_fin ptTest_fst
theorem H121_fin : (prmOK pH121 121 && ptTest pH121 (runFrom pH121 (fmask pH121) (cmask pH121) (hmask pH121) 1 120 (true, (init pH121), (init pH121))) 121 61 true) = true := by
  decide +kernel
theorem H121_ok : RunOK pH121 121 (runFrom pH121 (fmask pH121) (cmask pH121) (hmask pH121) 1 120 (true, (init pH121), (init pH121))) ∧ ptTest pH121 (runFrom pH121 (fmask pH121) (cmask pH121) (hmask pH121) 1 120 (true, (init pH121), (init pH121))) 121 61 true = true :=
  fin_run (runOK_init (prmOK_of_and H121_fin) true) (by decide) rfl H121_fin ptTest_fst
theorem I121_fin : (prmOK pI121 121 && intTest pI121 (runFrom pI121 (fmask pI121) (cmask pI121) (hmask pI121) 1 120 (true, (init pI121), (init pI121))) 121 7 false) = true := by
  decide +kernel
theorem I121_ok : RunOK pI121 121 (runFrom pI121 (fmask pI121) (cmask pI121) (hmask pI121) 1 120 (true, (init pI121), (init pI121))) ∧ intTest pI121 (runFrom pI121 (fmask pI121) (cmask pI121) (hmask pI121) 1 120 (true, (init pI121), (init pI121))) 121 7 false = true :=
  fin_run (runOK_init (prmOK_of_and I121_fin) true) (by decide) rfl I121_fin intTest_fst
theorem link121 : linkOK pL121 pH121 pI121 = true := by decide +kernel
theorem cvx121 : ConvexBetweenHumps 121 :=
  cvx_of L121_ok H121_ok I121_ok link121 (by decide)

/-! ### `N = 122` -/

def pL122 : Prm := ⟨59, 28, 28, 124, 11, 18446744073709551616, 823446563110652869, 823446563110652869⟩
def pH122 : Prm := ⟨59, 28, 28, 124, 11, 18446744073709551616, 823481747482741701, 823481747482741701⟩
def pI122 : Prm := ⟨51, 25, 23, 124, 11, 18446744073709551616, 823446563110652869, 823481747482741701⟩
theorem L122_fin : (prmOK pL122 122 && ptTest pL122 (runFrom pL122 (fmask pL122) (cmask pL122) (hmask pL122) 1 121 (true, (init pL122), (init pL122))) 122 61 false) = true := by
  decide +kernel
theorem L122_ok : RunOK pL122 122 (runFrom pL122 (fmask pL122) (cmask pL122) (hmask pL122) 1 121 (true, (init pL122), (init pL122))) ∧ ptTest pL122 (runFrom pL122 (fmask pL122) (cmask pL122) (hmask pL122) 1 121 (true, (init pL122), (init pL122))) 122 61 false = true :=
  fin_run (runOK_init (prmOK_of_and L122_fin) true) (by decide) rfl L122_fin ptTest_fst
theorem H122_fin : (prmOK pH122 122 && ptTest pH122 (runFrom pH122 (fmask pH122) (cmask pH122) (hmask pH122) 1 121 (true, (init pH122), (init pH122))) 122 61 true) = true := by
  decide +kernel
theorem H122_ok : RunOK pH122 122 (runFrom pH122 (fmask pH122) (cmask pH122) (hmask pH122) 1 121 (true, (init pH122), (init pH122))) ∧ ptTest pH122 (runFrom pH122 (fmask pH122) (cmask pH122) (hmask pH122) 1 121 (true, (init pH122), (init pH122))) 122 61 true = true :=
  fin_run (runOK_init (prmOK_of_and H122_fin) true) (by decide) rfl H122_fin ptTest_fst
theorem I122_fin : (prmOK pI122 122 && intTest pI122 (runFrom pI122 (fmask pI122) (cmask pI122) (hmask pI122) 1 121 (true, (init pI122), (init pI122))) 122 8 true) = true := by
  decide +kernel
theorem I122_ok : RunOK pI122 122 (runFrom pI122 (fmask pI122) (cmask pI122) (hmask pI122) 1 121 (true, (init pI122), (init pI122))) ∧ intTest pI122 (runFrom pI122 (fmask pI122) (cmask pI122) (hmask pI122) 1 121 (true, (init pI122), (init pI122))) 122 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I122_fin) true) (by decide) rfl I122_fin intTest_fst
theorem link122 : linkOK pL122 pH122 pI122 = true := by decide +kernel
theorem cvx122 : ConvexBetweenHumps 122 :=
  cvx_of L122_ok H122_ok I122_ok link122 (by decide)
theorem cenlink122 : cenLinkOK pI122 122 = true := by decide +kernel
theorem cen122 : CenterUniqueMin 122 ∧ DipHyp 122 ∧ OnePointHyps 122 :=
  cen_of L122_ok H122_ok I122_ok link122 cenlink122

/-! ### `N = 123` -/

def pL123 : Prm := ⟨59, 28, 28, 125, 11, 18446744073709551616, 818897174918566447, 818897174918566447⟩
def pH123 : Prm := ⟨59, 28, 28, 125, 11, 18446744073709551616, 818932359290655279, 818932359290655279⟩
def pI123 : Prm := ⟨51, 25, 23, 125, 11, 18446744073709551616, 818897174918566447, 818932359290655279⟩
theorem L123_fin : (prmOK pL123 123 && ptTest pL123 (runFrom pL123 (fmask pL123) (cmask pL123) (hmask pL123) 1 122 (true, (init pL123), (init pL123))) 123 62 false) = true := by
  decide +kernel
theorem L123_ok : RunOK pL123 123 (runFrom pL123 (fmask pL123) (cmask pL123) (hmask pL123) 1 122 (true, (init pL123), (init pL123))) ∧ ptTest pL123 (runFrom pL123 (fmask pL123) (cmask pL123) (hmask pL123) 1 122 (true, (init pL123), (init pL123))) 123 62 false = true :=
  fin_run (runOK_init (prmOK_of_and L123_fin) true) (by decide) rfl L123_fin ptTest_fst
theorem H123_fin : (prmOK pH123 123 && ptTest pH123 (runFrom pH123 (fmask pH123) (cmask pH123) (hmask pH123) 1 122 (true, (init pH123), (init pH123))) 123 62 true) = true := by
  decide +kernel
theorem H123_ok : RunOK pH123 123 (runFrom pH123 (fmask pH123) (cmask pH123) (hmask pH123) 1 122 (true, (init pH123), (init pH123))) ∧ ptTest pH123 (runFrom pH123 (fmask pH123) (cmask pH123) (hmask pH123) 1 122 (true, (init pH123), (init pH123))) 123 62 true = true :=
  fin_run (runOK_init (prmOK_of_and H123_fin) true) (by decide) rfl H123_fin ptTest_fst
theorem I123_fin : (prmOK pI123 123 && intTest pI123 (runFrom pI123 (fmask pI123) (cmask pI123) (hmask pI123) 1 122 (true, (init pI123), (init pI123))) 123 8 false) = true := by
  decide +kernel
theorem I123_ok : RunOK pI123 123 (runFrom pI123 (fmask pI123) (cmask pI123) (hmask pI123) 1 122 (true, (init pI123), (init pI123))) ∧ intTest pI123 (runFrom pI123 (fmask pI123) (cmask pI123) (hmask pI123) 1 122 (true, (init pI123), (init pI123))) 123 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I123_fin) true) (by decide) rfl I123_fin intTest_fst
theorem link123 : linkOK pL123 pH123 pI123 = true := by decide +kernel
theorem cvx123 : ConvexBetweenHumps 123 :=
  cvx_of L123_ok H123_ok I123_ok link123 (by decide)

/-! ### `N = 124` -/

def pL124 : Prm := ⟨57, 27, 27, 126, 11, 18446744073709551616, 814449792556239930, 814449792556239930⟩
def pH124 : Prm := ⟨57, 27, 27, 126, 11, 18446744073709551616, 814520161300417594, 814520161300417594⟩
def pI124 : Prm := ⟨51, 25, 23, 126, 11, 18446744073709551616, 814449792556239930, 814520161300417594⟩
theorem L124_fin : (prmOK pL124 124 && ptTest pL124 (runFrom pL124 (fmask pL124) (cmask pL124) (hmask pL124) 1 123 (true, (init pL124), (init pL124))) 124 62 false) = true := by
  decide +kernel
theorem L124_ok : RunOK pL124 124 (runFrom pL124 (fmask pL124) (cmask pL124) (hmask pL124) 1 123 (true, (init pL124), (init pL124))) ∧ ptTest pL124 (runFrom pL124 (fmask pL124) (cmask pL124) (hmask pL124) 1 123 (true, (init pL124), (init pL124))) 124 62 false = true :=
  fin_run (runOK_init (prmOK_of_and L124_fin) true) (by decide) rfl L124_fin ptTest_fst
theorem H124_fin : (prmOK pH124 124 && ptTest pH124 (runFrom pH124 (fmask pH124) (cmask pH124) (hmask pH124) 1 123 (true, (init pH124), (init pH124))) 124 62 true) = true := by
  decide +kernel
theorem H124_ok : RunOK pH124 124 (runFrom pH124 (fmask pH124) (cmask pH124) (hmask pH124) 1 123 (true, (init pH124), (init pH124))) ∧ ptTest pH124 (runFrom pH124 (fmask pH124) (cmask pH124) (hmask pH124) 1 123 (true, (init pH124), (init pH124))) 124 62 true = true :=
  fin_run (runOK_init (prmOK_of_and H124_fin) true) (by decide) rfl H124_fin ptTest_fst
theorem I124_fin : (prmOK pI124 124 && intTest pI124 (runFrom pI124 (fmask pI124) (cmask pI124) (hmask pI124) 1 123 (true, (init pI124), (init pI124))) 124 8 true) = true := by
  decide +kernel
theorem I124_ok : RunOK pI124 124 (runFrom pI124 (fmask pI124) (cmask pI124) (hmask pI124) 1 123 (true, (init pI124), (init pI124))) ∧ intTest pI124 (runFrom pI124 (fmask pI124) (cmask pI124) (hmask pI124) 1 123 (true, (init pI124), (init pI124))) 124 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I124_fin) true) (by decide) rfl I124_fin intTest_fst
theorem link124 : linkOK pL124 pH124 pI124 = true := by decide +kernel
theorem cvx124 : ConvexBetweenHumps 124 :=
  cvx_of L124_ok H124_ok I124_ok link124 (by decide)
theorem cenlink124 : cenLinkOK pI124 124 = true := by decide +kernel
theorem cen124 : CenterUniqueMin 124 ∧ DipHyp 124 ∧ OnePointHyps 124 :=
  cen_of L124_ok H124_ok I124_ok link124 cenlink124

/-! ### `N = 125` -/

def pL125 : Prm := ⟨57, 27, 27, 127, 11, 18446744073709551616, 810014449242127273, 810014449242127273⟩
def pH125 : Prm := ⟨57, 27, 27, 127, 11, 18446744073709551616, 810084817986304937, 810084817986304937⟩
def pI125 : Prm := ⟨51, 24, 24, 127, 11, 18446744073709551616, 810014449242127273, 810084817986304937⟩
theorem L125_fin : (prmOK pL125 125 && ptTest pL125 (runFrom pL125 (fmask pL125) (cmask pL125) (hmask pL125) 1 124 (true, (init pL125), (init pL125))) 125 63 false) = true := by
  decide +kernel
theorem L125_ok : RunOK pL125 125 (runFrom pL125 (fmask pL125) (cmask pL125) (hmask pL125) 1 124 (true, (init pL125), (init pL125))) ∧ ptTest pL125 (runFrom pL125 (fmask pL125) (cmask pL125) (hmask pL125) 1 124 (true, (init pL125), (init pL125))) 125 63 false = true :=
  fin_run (runOK_init (prmOK_of_and L125_fin) true) (by decide) rfl L125_fin ptTest_fst
theorem H125_fin : (prmOK pH125 125 && ptTest pH125 (runFrom pH125 (fmask pH125) (cmask pH125) (hmask pH125) 1 124 (true, (init pH125), (init pH125))) 125 63 true) = true := by
  decide +kernel
theorem H125_ok : RunOK pH125 125 (runFrom pH125 (fmask pH125) (cmask pH125) (hmask pH125) 1 124 (true, (init pH125), (init pH125))) ∧ ptTest pH125 (runFrom pH125 (fmask pH125) (cmask pH125) (hmask pH125) 1 124 (true, (init pH125), (init pH125))) 125 63 true = true :=
  fin_run (runOK_init (prmOK_of_and H125_fin) true) (by decide) rfl H125_fin ptTest_fst
theorem I125_fin : (prmOK pI125 125 && intTest pI125 (runFrom pI125 (fmask pI125) (cmask pI125) (hmask pI125) 1 124 (true, (init pI125), (init pI125))) 125 8 false) = true := by
  decide +kernel
theorem I125_ok : RunOK pI125 125 (runFrom pI125 (fmask pI125) (cmask pI125) (hmask pI125) 1 124 (true, (init pI125), (init pI125))) ∧ intTest pI125 (runFrom pI125 (fmask pI125) (cmask pI125) (hmask pI125) 1 124 (true, (init pI125), (init pI125))) 125 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I125_fin) true) (by decide) rfl I125_fin intTest_fst
theorem link125 : linkOK pL125 pH125 pI125 = true := by decide +kernel
theorem cvx125 : ConvexBetweenHumps 125 :=
  cvx_of L125_ok H125_ok I125_ok link125 (by decide)

/-! ### `N = 126` -/

def pL126 : Prm := ⟨57, 27, 27, 128, 11, 18446744073709551616, 805693642090098962, 805693642090098962⟩
def pH126 : Prm := ⟨57, 27, 27, 128, 11, 18446744073709551616, 805764010834276626, 805764010834276626⟩
def pI126 : Prm := ⟨51, 24, 24, 128, 11, 18446744073709551616, 805693642090098962, 805764010834276626⟩
theorem L126_fin : (prmOK pL126 126 && ptTest pL126 (runFrom pL126 (fmask pL126) (cmask pL126) (hmask pL126) 1 125 (true, (init pL126), (init pL126))) 126 63 false) = true := by
  decide +kernel
theorem L126_ok : RunOK pL126 126 (runFrom pL126 (fmask pL126) (cmask pL126) (hmask pL126) 1 125 (true, (init pL126), (init pL126))) ∧ ptTest pL126 (runFrom pL126 (fmask pL126) (cmask pL126) (hmask pL126) 1 125 (true, (init pL126), (init pL126))) 126 63 false = true :=
  fin_run (runOK_init (prmOK_of_and L126_fin) true) (by decide) rfl L126_fin ptTest_fst
theorem H126_fin : (prmOK pH126 126 && ptTest pH126 (runFrom pH126 (fmask pH126) (cmask pH126) (hmask pH126) 1 125 (true, (init pH126), (init pH126))) 126 63 true) = true := by
  decide +kernel
theorem H126_ok : RunOK pH126 126 (runFrom pH126 (fmask pH126) (cmask pH126) (hmask pH126) 1 125 (true, (init pH126), (init pH126))) ∧ ptTest pH126 (runFrom pH126 (fmask pH126) (cmask pH126) (hmask pH126) 1 125 (true, (init pH126), (init pH126))) 126 63 true = true :=
  fin_run (runOK_init (prmOK_of_and H126_fin) true) (by decide) rfl H126_fin ptTest_fst
theorem I126_fin : (prmOK pI126 126 && intTest pI126 (runFrom pI126 (fmask pI126) (cmask pI126) (hmask pI126) 1 125 (true, (init pI126), (init pI126))) 126 8 true) = true := by
  decide +kernel
theorem I126_ok : RunOK pI126 126 (runFrom pI126 (fmask pI126) (cmask pI126) (hmask pI126) 1 125 (true, (init pI126), (init pI126))) ∧ intTest pI126 (runFrom pI126 (fmask pI126) (cmask pI126) (hmask pI126) 1 125 (true, (init pI126), (init pI126))) 126 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I126_fin) true) (by decide) rfl I126_fin intTest_fst
theorem link126 : linkOK pL126 pH126 pI126 = true := by decide +kernel
theorem cvx126 : ConvexBetweenHumps 126 :=
  cvx_of L126_ok H126_ok I126_ok link126 (by decide)
theorem cenlink126 : cenLinkOK pI126 126 = true := by decide +kernel
theorem cen126 : CenterUniqueMin 126 ∧ DipHyp 126 ∧ OnePointHyps 126 :=
  cen_of L126_ok H126_ok I126_ok link126 cenlink126

/-! ### `N = 127` -/

def pL127 : Prm := ⟨57, 27, 27, 129, 11, 18446744073709551616, 801367848594197528, 801367848594197528⟩
def pH127 : Prm := ⟨57, 27, 27, 129, 11, 18446744073709551616, 801438217338375192, 801438217338375192⟩
def pI127 : Prm := ⟨51, 24, 24, 129, 11, 18446744073709551616, 801367848594197528, 801438217338375192⟩
theorem L127_fin : (prmOK pL127 127 && ptTest pL127 (runFrom pL127 (fmask pL127) (cmask pL127) (hmask pL127) 1 126 (true, (init pL127), (init pL127))) 127 64 false) = true := by
  decide +kernel
theorem L127_ok : RunOK pL127 127 (runFrom pL127 (fmask pL127) (cmask pL127) (hmask pL127) 1 126 (true, (init pL127), (init pL127))) ∧ ptTest pL127 (runFrom pL127 (fmask pL127) (cmask pL127) (hmask pL127) 1 126 (true, (init pL127), (init pL127))) 127 64 false = true :=
  fin_run (runOK_init (prmOK_of_and L127_fin) true) (by decide) rfl L127_fin ptTest_fst
theorem H127_fin : (prmOK pH127 127 && ptTest pH127 (runFrom pH127 (fmask pH127) (cmask pH127) (hmask pH127) 1 126 (true, (init pH127), (init pH127))) 127 64 true) = true := by
  decide +kernel
theorem H127_ok : RunOK pH127 127 (runFrom pH127 (fmask pH127) (cmask pH127) (hmask pH127) 1 126 (true, (init pH127), (init pH127))) ∧ ptTest pH127 (runFrom pH127 (fmask pH127) (cmask pH127) (hmask pH127) 1 126 (true, (init pH127), (init pH127))) 127 64 true = true :=
  fin_run (runOK_init (prmOK_of_and H127_fin) true) (by decide) rfl H127_fin ptTest_fst
theorem I127_fin : (prmOK pI127 127 && intTest pI127 (runFrom pI127 (fmask pI127) (cmask pI127) (hmask pI127) 1 126 (true, (init pI127), (init pI127))) 127 8 false) = true := by
  decide +kernel
theorem I127_ok : RunOK pI127 127 (runFrom pI127 (fmask pI127) (cmask pI127) (hmask pI127) 1 126 (true, (init pI127), (init pI127))) ∧ intTest pI127 (runFrom pI127 (fmask pI127) (cmask pI127) (hmask pI127) 1 126 (true, (init pI127), (init pI127))) 127 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I127_fin) true) (by decide) rfl I127_fin intTest_fst
theorem link127 : linkOK pL127 pH127 pI127 = true := by decide +kernel
theorem cvx127 : ConvexBetweenHumps 127 :=
  cvx_of L127_ok H127_ok I127_ok link127 (by decide)

/-! ### `N = 128` -/

def pL128 : Prm := ⟨57, 27, 27, 130, 11, 18446744073709551616, 797151814294726398, 797151814294726398⟩
def pH128 : Prm := ⟨57, 27, 27, 130, 11, 18446744073709551616, 797222183038904062, 797222183038904062⟩
def pI128 : Prm := ⟨51, 25, 23, 130, 11, 18446744073709551616, 797151814294726398, 797222183038904062⟩
theorem L128_fin : (prmOK pL128 128 && ptTest pL128 (runFrom pL128 (fmask pL128) (cmask pL128) (hmask pL128) 1 127 (true, (init pL128), (init pL128))) 128 64 false) = true := by
  decide +kernel
theorem L128_ok : RunOK pL128 128 (runFrom pL128 (fmask pL128) (cmask pL128) (hmask pL128) 1 127 (true, (init pL128), (init pL128))) ∧ ptTest pL128 (runFrom pL128 (fmask pL128) (cmask pL128) (hmask pL128) 1 127 (true, (init pL128), (init pL128))) 128 64 false = true :=
  fin_run (runOK_init (prmOK_of_and L128_fin) true) (by decide) rfl L128_fin ptTest_fst
theorem H128_fin : (prmOK pH128 128 && ptTest pH128 (runFrom pH128 (fmask pH128) (cmask pH128) (hmask pH128) 1 127 (true, (init pH128), (init pH128))) 128 64 true) = true := by
  decide +kernel
theorem H128_ok : RunOK pH128 128 (runFrom pH128 (fmask pH128) (cmask pH128) (hmask pH128) 1 127 (true, (init pH128), (init pH128))) ∧ ptTest pH128 (runFrom pH128 (fmask pH128) (cmask pH128) (hmask pH128) 1 127 (true, (init pH128), (init pH128))) 128 64 true = true :=
  fin_run (runOK_init (prmOK_of_and H128_fin) true) (by decide) rfl H128_fin ptTest_fst
theorem I128_fin : (prmOK pI128 128 && intTest pI128 (runFrom pI128 (fmask pI128) (cmask pI128) (hmask pI128) 1 127 (true, (init pI128), (init pI128))) 128 8 true) = true := by
  decide +kernel
theorem I128_ok : RunOK pI128 128 (runFrom pI128 (fmask pI128) (cmask pI128) (hmask pI128) 1 127 (true, (init pI128), (init pI128))) ∧ intTest pI128 (runFrom pI128 (fmask pI128) (cmask pI128) (hmask pI128) 1 127 (true, (init pI128), (init pI128))) 128 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I128_fin) true) (by decide) rfl I128_fin intTest_fst
theorem link128 : linkOK pL128 pH128 pI128 = true := by decide +kernel
theorem cvx128 : ConvexBetweenHumps 128 :=
  cvx_of L128_ok H128_ok I128_ok link128 (by decide)
theorem cenlink128 : cenLinkOK pI128 128 = true := by decide +kernel
theorem cen128 : CenterUniqueMin 128 ∧ DipHyp 128 ∧ OnePointHyps 128 :=
  cen_of L128_ok H128_ok I128_ok link128 cenlink128

/-! ### `N = 129` -/

def pL129 : Prm := ⟨57, 27, 27, 131, 11, 18446744073709551616, 792931316830983142, 792931316830983142⟩
def pH129 : Prm := ⟨57, 27, 27, 131, 11, 18446744073709551616, 793001685575160806, 793001685575160806⟩
def pI129 : Prm := ⟨51, 25, 23, 131, 11, 18446744073709551616, 792931316830983142, 793001685575160806⟩
theorem L129_fin : (prmOK pL129 129 && ptTest pL129 (runFrom pL129 (fmask pL129) (cmask pL129) (hmask pL129) 1 128 (true, (init pL129), (init pL129))) 129 65 false) = true := by
  decide +kernel
theorem L129_ok : RunOK pL129 129 (runFrom pL129 (fmask pL129) (cmask pL129) (hmask pL129) 1 128 (true, (init pL129), (init pL129))) ∧ ptTest pL129 (runFrom pL129 (fmask pL129) (cmask pL129) (hmask pL129) 1 128 (true, (init pL129), (init pL129))) 129 65 false = true :=
  fin_run (runOK_init (prmOK_of_and L129_fin) true) (by decide) rfl L129_fin ptTest_fst
theorem H129_fin : (prmOK pH129 129 && ptTest pH129 (runFrom pH129 (fmask pH129) (cmask pH129) (hmask pH129) 1 128 (true, (init pH129), (init pH129))) 129 65 true) = true := by
  decide +kernel
theorem H129_ok : RunOK pH129 129 (runFrom pH129 (fmask pH129) (cmask pH129) (hmask pH129) 1 128 (true, (init pH129), (init pH129))) ∧ ptTest pH129 (runFrom pH129 (fmask pH129) (cmask pH129) (hmask pH129) 1 128 (true, (init pH129), (init pH129))) 129 65 true = true :=
  fin_run (runOK_init (prmOK_of_and H129_fin) true) (by decide) rfl H129_fin ptTest_fst
theorem I129_fin : (prmOK pI129 129 && intTest pI129 (runFrom pI129 (fmask pI129) (cmask pI129) (hmask pI129) 1 128 (true, (init pI129), (init pI129))) 129 8 false) = true := by
  decide +kernel
theorem I129_ok : RunOK pI129 129 (runFrom pI129 (fmask pI129) (cmask pI129) (hmask pI129) 1 128 (true, (init pI129), (init pI129))) ∧ intTest pI129 (runFrom pI129 (fmask pI129) (cmask pI129) (hmask pI129) 1 128 (true, (init pI129), (init pI129))) 129 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I129_fin) true) (by decide) rfl I129_fin intTest_fst
theorem link129 : linkOK pL129 pH129 pI129 = true := by decide +kernel
theorem cvx129 : ConvexBetweenHumps 129 :=
  cvx_of L129_ok H129_ok I129_ok link129 (by decide)

/-! ### `N = 130` -/

def pL130 : Prm := ⟨57, 27, 27, 132, 11, 18446744073709551616, 788816066597300685, 788816066597300685⟩
def pH130 : Prm := ⟨57, 27, 27, 132, 11, 18446744073709551616, 788886435341478349, 788886435341478349⟩
def pI130 : Prm := ⟨51, 25, 23, 132, 11, 18446744073709551616, 788816066597300685, 788886435341478349⟩
theorem L130_fin : (prmOK pL130 130 && ptTest pL130 (runFrom pL130 (fmask pL130) (cmask pL130) (hmask pL130) 1 129 (true, (init pL130), (init pL130))) 130 65 false) = true := by
  decide +kernel
theorem L130_ok : RunOK pL130 130 (runFrom pL130 (fmask pL130) (cmask pL130) (hmask pL130) 1 129 (true, (init pL130), (init pL130))) ∧ ptTest pL130 (runFrom pL130 (fmask pL130) (cmask pL130) (hmask pL130) 1 129 (true, (init pL130), (init pL130))) 130 65 false = true :=
  fin_run (runOK_init (prmOK_of_and L130_fin) true) (by decide) rfl L130_fin ptTest_fst
theorem H130_fin : (prmOK pH130 130 && ptTest pH130 (runFrom pH130 (fmask pH130) (cmask pH130) (hmask pH130) 1 129 (true, (init pH130), (init pH130))) 130 65 true) = true := by
  decide +kernel
theorem H130_ok : RunOK pH130 130 (runFrom pH130 (fmask pH130) (cmask pH130) (hmask pH130) 1 129 (true, (init pH130), (init pH130))) ∧ ptTest pH130 (runFrom pH130 (fmask pH130) (cmask pH130) (hmask pH130) 1 129 (true, (init pH130), (init pH130))) 130 65 true = true :=
  fin_run (runOK_init (prmOK_of_and H130_fin) true) (by decide) rfl H130_fin ptTest_fst
theorem I130_fin : (prmOK pI130 130 && intTest pI130 (runFrom pI130 (fmask pI130) (cmask pI130) (hmask pI130) 1 129 (true, (init pI130), (init pI130))) 130 8 true) = true := by
  decide +kernel
theorem I130_ok : RunOK pI130 130 (runFrom pI130 (fmask pI130) (cmask pI130) (hmask pI130) 1 129 (true, (init pI130), (init pI130))) ∧ intTest pI130 (runFrom pI130 (fmask pI130) (cmask pI130) (hmask pI130) 1 129 (true, (init pI130), (init pI130))) 130 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I130_fin) true) (by decide) rfl I130_fin intTest_fst
theorem link130 : linkOK pL130 pH130 pI130 = true := by decide +kernel
theorem cvx130 : ConvexBetweenHumps 130 :=
  cvx_of L130_ok H130_ok I130_ok link130 (by decide)
theorem cenlink130 : cenLinkOK pI130 130 = true := by decide +kernel
theorem cen130 : CenterUniqueMin 130 ∧ DipHyp 130 ∧ OnePointHyps 130 :=
  cen_of L130_ok H130_ok I130_ok link130 cenlink130

/-! ### `N = 131` -/

def pL131 : Prm := ⟨57, 27, 27, 133, 11, 18446744073709551616, 784696836318466586, 784696836318466586⟩
def pH131 : Prm := ⟨57, 27, 27, 133, 11, 18446744073709551616, 784767205062644250, 784767205062644250⟩
def pI131 : Prm := ⟨52, 25, 24, 133, 11, 18446744073709551616, 784696836318466586, 784767205062644250⟩
theorem L131_fin : (prmOK pL131 131 && ptTest pL131 (runFrom pL131 (fmask pL131) (cmask pL131) (hmask pL131) 1 130 (true, (init pL131), (init pL131))) 131 66 false) = true := by
  decide +kernel
theorem L131_ok : RunOK pL131 131 (runFrom pL131 (fmask pL131) (cmask pL131) (hmask pL131) 1 130 (true, (init pL131), (init pL131))) ∧ ptTest pL131 (runFrom pL131 (fmask pL131) (cmask pL131) (hmask pL131) 1 130 (true, (init pL131), (init pL131))) 131 66 false = true :=
  fin_run (runOK_init (prmOK_of_and L131_fin) true) (by decide) rfl L131_fin ptTest_fst
theorem H131_fin : (prmOK pH131 131 && ptTest pH131 (runFrom pH131 (fmask pH131) (cmask pH131) (hmask pH131) 1 130 (true, (init pH131), (init pH131))) 131 66 true) = true := by
  decide +kernel
theorem H131_ok : RunOK pH131 131 (runFrom pH131 (fmask pH131) (cmask pH131) (hmask pH131) 1 130 (true, (init pH131), (init pH131))) ∧ ptTest pH131 (runFrom pH131 (fmask pH131) (cmask pH131) (hmask pH131) 1 130 (true, (init pH131), (init pH131))) 131 66 true = true :=
  fin_run (runOK_init (prmOK_of_and H131_fin) true) (by decide) rfl H131_fin ptTest_fst
theorem I131_fin : (prmOK pI131 131 && intTest pI131 (runFrom pI131 (fmask pI131) (cmask pI131) (hmask pI131) 1 130 (true, (init pI131), (init pI131))) 131 8 false) = true := by
  decide +kernel
theorem I131_ok : RunOK pI131 131 (runFrom pI131 (fmask pI131) (cmask pI131) (hmask pI131) 1 130 (true, (init pI131), (init pI131))) ∧ intTest pI131 (runFrom pI131 (fmask pI131) (cmask pI131) (hmask pI131) 1 130 (true, (init pI131), (init pI131))) 131 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I131_fin) true) (by decide) rfl I131_fin intTest_fst
theorem link131 : linkOK pL131 pH131 pI131 = true := by decide +kernel
theorem cvx131 : ConvexBetweenHumps 131 :=
  cvx_of L131_ok H131_ok I131_ok link131 (by decide)

/-! ### `N = 132` -/

def pL132 : Prm := ⟨57, 27, 27, 134, 11, 18446744073709551616, 780678588063611473, 780678588063611473⟩
def pH132 : Prm := ⟨57, 27, 27, 134, 11, 18446744073709551616, 780748956807789137, 780748956807789137⟩
def pI132 : Prm := ⟨52, 25, 24, 134, 11, 18446744073709551616, 780678588063611473, 780748956807789137⟩
theorem L132_fin : (prmOK pL132 132 && ptTest pL132 (runFrom pL132 (fmask pL132) (cmask pL132) (hmask pL132) 1 131 (true, (init pL132), (init pL132))) 132 66 false) = true := by
  decide +kernel
theorem L132_ok : RunOK pL132 132 (runFrom pL132 (fmask pL132) (cmask pL132) (hmask pL132) 1 131 (true, (init pL132), (init pL132))) ∧ ptTest pL132 (runFrom pL132 (fmask pL132) (cmask pL132) (hmask pL132) 1 131 (true, (init pL132), (init pL132))) 132 66 false = true :=
  fin_run (runOK_init (prmOK_of_and L132_fin) true) (by decide) rfl L132_fin ptTest_fst
theorem H132_fin : (prmOK pH132 132 && ptTest pH132 (runFrom pH132 (fmask pH132) (cmask pH132) (hmask pH132) 1 131 (true, (init pH132), (init pH132))) 132 66 true) = true := by
  decide +kernel
theorem H132_ok : RunOK pH132 132 (runFrom pH132 (fmask pH132) (cmask pH132) (hmask pH132) 1 131 (true, (init pH132), (init pH132))) ∧ ptTest pH132 (runFrom pH132 (fmask pH132) (cmask pH132) (hmask pH132) 1 131 (true, (init pH132), (init pH132))) 132 66 true = true :=
  fin_run (runOK_init (prmOK_of_and H132_fin) true) (by decide) rfl H132_fin ptTest_fst
theorem I132_fin : (prmOK pI132 132 && intTest pI132 (runFrom pI132 (fmask pI132) (cmask pI132) (hmask pI132) 1 131 (true, (init pI132), (init pI132))) 132 8 true) = true := by
  decide +kernel
theorem I132_ok : RunOK pI132 132 (runFrom pI132 (fmask pI132) (cmask pI132) (hmask pI132) 1 131 (true, (init pI132), (init pI132))) ∧ intTest pI132 (runFrom pI132 (fmask pI132) (cmask pI132) (hmask pI132) 1 131 (true, (init pI132), (init pI132))) 132 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I132_fin) true) (by decide) rfl I132_fin intTest_fst
theorem link132 : linkOK pL132 pH132 pI132 = true := by decide +kernel
theorem cvx132 : ConvexBetweenHumps 132 :=
  cvx_of L132_ok H132_ok I132_ok link132 (by decide)
theorem cenlink132 : cenLinkOK pI132 132 = true := by decide +kernel
theorem cen132 : CenterUniqueMin 132 ∧ DipHyp 132 ∧ OnePointHyps 132 :=
  cen_of L132_ok H132_ok I132_ok link132 cenlink132

/-! ### `N = 133` -/

def pL133 : Prm := ⟨59, 28, 28, 135, 11, 18446744073709551616, 776674398242446069, 776674398242446069⟩
def pH133 : Prm := ⟨59, 28, 28, 135, 11, 18446744073709551616, 776709582614534901, 776709582614534901⟩
def pI133 : Prm := ⟨51, 24, 24, 135, 11, 18446744073709551616, 776674398242446069, 776709582614534901⟩
theorem L133_fin : (prmOK pL133 133 && ptTest pL133 (runFrom pL133 (fmask pL133) (cmask pL133) (hmask pL133) 1 132 (true, (init pL133), (init pL133))) 133 67 false) = true := by
  decide +kernel
theorem L133_ok : RunOK pL133 133 (runFrom pL133 (fmask pL133) (cmask pL133) (hmask pL133) 1 132 (true, (init pL133), (init pL133))) ∧ ptTest pL133 (runFrom pL133 (fmask pL133) (cmask pL133) (hmask pL133) 1 132 (true, (init pL133), (init pL133))) 133 67 false = true :=
  fin_run (runOK_init (prmOK_of_and L133_fin) true) (by decide) rfl L133_fin ptTest_fst
theorem H133_fin : (prmOK pH133 133 && ptTest pH133 (runFrom pH133 (fmask pH133) (cmask pH133) (hmask pH133) 1 132 (true, (init pH133), (init pH133))) 133 67 true) = true := by
  decide +kernel
theorem H133_ok : RunOK pH133 133 (runFrom pH133 (fmask pH133) (cmask pH133) (hmask pH133) 1 132 (true, (init pH133), (init pH133))) ∧ ptTest pH133 (runFrom pH133 (fmask pH133) (cmask pH133) (hmask pH133) 1 132 (true, (init pH133), (init pH133))) 133 67 true = true :=
  fin_run (runOK_init (prmOK_of_and H133_fin) true) (by decide) rfl H133_fin ptTest_fst
theorem I133_fin : (prmOK pI133 133 && intTest pI133 (runFrom pI133 (fmask pI133) (cmask pI133) (hmask pI133) 1 132 (true, (init pI133), (init pI133))) 133 8 false) = true := by
  decide +kernel
theorem I133_ok : RunOK pI133 133 (runFrom pI133 (fmask pI133) (cmask pI133) (hmask pI133) 1 132 (true, (init pI133), (init pI133))) ∧ intTest pI133 (runFrom pI133 (fmask pI133) (cmask pI133) (hmask pI133) 1 132 (true, (init pI133), (init pI133))) 133 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I133_fin) true) (by decide) rfl I133_fin intTest_fst
theorem link133 : linkOK pL133 pH133 pI133 = true := by decide +kernel
theorem cvx133 : ConvexBetweenHumps 133 :=
  cvx_of L133_ok H133_ok I133_ok link133 (by decide)

/-! ### `N = 134` -/

def pL134 : Prm := ⟨59, 28, 28, 136, 11, 18446744073709551616, 772749563066470721, 772749563066470721⟩
def pH134 : Prm := ⟨59, 28, 28, 136, 11, 18446744073709551616, 772784747438559553, 772784747438559553⟩
def pI134 : Prm := ⟨51, 24, 24, 136, 11, 18446744073709551616, 772749563066470721, 772784747438559553⟩
theorem L134_fin : (prmOK pL134 134 && ptTest pL134 (runFrom pL134 (fmask pL134) (cmask pL134) (hmask pL134) 1 133 (true, (init pL134), (init pL134))) 134 67 false) = true := by
  decide +kernel
theorem L134_ok : RunOK pL134 134 (runFrom pL134 (fmask pL134) (cmask pL134) (hmask pL134) 1 133 (true, (init pL134), (init pL134))) ∧ ptTest pL134 (runFrom pL134 (fmask pL134) (cmask pL134) (hmask pL134) 1 133 (true, (init pL134), (init pL134))) 134 67 false = true :=
  fin_run (runOK_init (prmOK_of_and L134_fin) true) (by decide) rfl L134_fin ptTest_fst
theorem H134_fin : (prmOK pH134 134 && ptTest pH134 (runFrom pH134 (fmask pH134) (cmask pH134) (hmask pH134) 1 133 (true, (init pH134), (init pH134))) 134 67 true) = true := by
  decide +kernel
theorem H134_ok : RunOK pH134 134 (runFrom pH134 (fmask pH134) (cmask pH134) (hmask pH134) 1 133 (true, (init pH134), (init pH134))) ∧ ptTest pH134 (runFrom pH134 (fmask pH134) (cmask pH134) (hmask pH134) 1 133 (true, (init pH134), (init pH134))) 134 67 true = true :=
  fin_run (runOK_init (prmOK_of_and H134_fin) true) (by decide) rfl H134_fin ptTest_fst
theorem I134_fin : (prmOK pI134 134 && intTest pI134 (runFrom pI134 (fmask pI134) (cmask pI134) (hmask pI134) 1 133 (true, (init pI134), (init pI134))) 134 8 true) = true := by
  decide +kernel
theorem I134_ok : RunOK pI134 134 (runFrom pI134 (fmask pI134) (cmask pI134) (hmask pI134) 1 133 (true, (init pI134), (init pI134))) ∧ intTest pI134 (runFrom pI134 (fmask pI134) (cmask pI134) (hmask pI134) 1 133 (true, (init pI134), (init pI134))) 134 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I134_fin) true) (by decide) rfl I134_fin intTest_fst
theorem link134 : linkOK pL134 pH134 pI134 = true := by decide +kernel
theorem cvx134 : ConvexBetweenHumps 134 :=
  cvx_of L134_ok H134_ok I134_ok link134 (by decide)
theorem cenlink134 : cenLinkOK pI134 134 = true := by decide +kernel
theorem cen134 : CenterUniqueMin 134 ∧ DipHyp 134 ∧ OnePointHyps 134 :=
  cen_of L134_ok H134_ok I134_ok link134 cenlink134

/-! ### `N = 135` -/

def pL135 : Prm := ⟨59, 28, 28, 137, 11, 18446744073709551616, 768821606550503733, 768821606550503733⟩
def pH135 : Prm := ⟨59, 28, 28, 137, 11, 18446744073709551616, 768856790922592565, 768856790922592565⟩
def pI135 : Prm := ⟨51, 25, 23, 137, 11, 18446744073709551616, 768821606550503733, 768856790922592565⟩
theorem L135_fin : (prmOK pL135 135 && ptTest pL135 (runFrom pL135 (fmask pL135) (cmask pL135) (hmask pL135) 1 134 (true, (init pL135), (init pL135))) 135 68 false) = true := by
  decide +kernel
theorem L135_ok : RunOK pL135 135 (runFrom pL135 (fmask pL135) (cmask pL135) (hmask pL135) 1 134 (true, (init pL135), (init pL135))) ∧ ptTest pL135 (runFrom pL135 (fmask pL135) (cmask pL135) (hmask pL135) 1 134 (true, (init pL135), (init pL135))) 135 68 false = true :=
  fin_run (runOK_init (prmOK_of_and L135_fin) true) (by decide) rfl L135_fin ptTest_fst
theorem H135_fin : (prmOK pH135 135 && ptTest pH135 (runFrom pH135 (fmask pH135) (cmask pH135) (hmask pH135) 1 134 (true, (init pH135), (init pH135))) 135 68 true) = true := by
  decide +kernel
theorem H135_ok : RunOK pH135 135 (runFrom pH135 (fmask pH135) (cmask pH135) (hmask pH135) 1 134 (true, (init pH135), (init pH135))) ∧ ptTest pH135 (runFrom pH135 (fmask pH135) (cmask pH135) (hmask pH135) 1 134 (true, (init pH135), (init pH135))) 135 68 true = true :=
  fin_run (runOK_init (prmOK_of_and H135_fin) true) (by decide) rfl H135_fin ptTest_fst
theorem I135_fin : (prmOK pI135 135 && intTest pI135 (runFrom pI135 (fmask pI135) (cmask pI135) (hmask pI135) 1 134 (true, (init pI135), (init pI135))) 135 8 false) = true := by
  decide +kernel
theorem I135_ok : RunOK pI135 135 (runFrom pI135 (fmask pI135) (cmask pI135) (hmask pI135) 1 134 (true, (init pI135), (init pI135))) ∧ intTest pI135 (runFrom pI135 (fmask pI135) (cmask pI135) (hmask pI135) 1 134 (true, (init pI135), (init pI135))) 135 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I135_fin) true) (by decide) rfl I135_fin intTest_fst
theorem link135 : linkOK pL135 pH135 pI135 = true := by decide +kernel
theorem cvx135 : ConvexBetweenHumps 135 :=
  cvx_of L135_ok H135_ok I135_ok link135 (by decide)

/-! ### `N = 136` -/

def pL136 : Prm := ⟨59, 28, 28, 138, 11, 18446744073709551616, 764986776290619166, 764986776290619166⟩
def pH136 : Prm := ⟨60, 29, 28, 138, 11, 18446744073709551616, 765021960662707998, 765021960662707998⟩
def pI136 : Prm := ⟨51, 24, 24, 138, 11, 18446744073709551616, 764986776290619166, 765021960662707998⟩
theorem L136_fin : (prmOK pL136 136 && ptTest pL136 (runFrom pL136 (fmask pL136) (cmask pL136) (hmask pL136) 1 135 (true, (init pL136), (init pL136))) 136 68 false) = true := by
  decide +kernel
theorem L136_ok : RunOK pL136 136 (runFrom pL136 (fmask pL136) (cmask pL136) (hmask pL136) 1 135 (true, (init pL136), (init pL136))) ∧ ptTest pL136 (runFrom pL136 (fmask pL136) (cmask pL136) (hmask pL136) 1 135 (true, (init pL136), (init pL136))) 136 68 false = true :=
  fin_run (runOK_init (prmOK_of_and L136_fin) true) (by decide) rfl L136_fin ptTest_fst
theorem H136_fin : (prmOK pH136 136 && ptTest pH136 (runFrom pH136 (fmask pH136) (cmask pH136) (hmask pH136) 1 135 (true, (init pH136), (init pH136))) 136 68 true) = true := by
  decide +kernel
theorem H136_ok : RunOK pH136 136 (runFrom pH136 (fmask pH136) (cmask pH136) (hmask pH136) 1 135 (true, (init pH136), (init pH136))) ∧ ptTest pH136 (runFrom pH136 (fmask pH136) (cmask pH136) (hmask pH136) 1 135 (true, (init pH136), (init pH136))) 136 68 true = true :=
  fin_run (runOK_init (prmOK_of_and H136_fin) true) (by decide) rfl H136_fin ptTest_fst
theorem I136_fin : (prmOK pI136 136 && intTest pI136 (runFrom pI136 (fmask pI136) (cmask pI136) (hmask pI136) 1 135 (true, (init pI136), (init pI136))) 136 8 true) = true := by
  decide +kernel
theorem I136_ok : RunOK pI136 136 (runFrom pI136 (fmask pI136) (cmask pI136) (hmask pI136) 1 135 (true, (init pI136), (init pI136))) ∧ intTest pI136 (runFrom pI136 (fmask pI136) (cmask pI136) (hmask pI136) 1 135 (true, (init pI136), (init pI136))) 136 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I136_fin) true) (by decide) rfl I136_fin intTest_fst
theorem link136 : linkOK pL136 pH136 pI136 = true := by decide +kernel
theorem cvx136 : ConvexBetweenHumps 136 :=
  cvx_of L136_ok H136_ok I136_ok link136 (by decide)
theorem cenlink136 : cenLinkOK pI136 136 = true := by decide +kernel
theorem cen136 : CenterUniqueMin 136 ∧ DipHyp 136 ∧ OnePointHyps 136 :=
  cen_of L136_ok H136_ok I136_ok link136 cenlink136

/-! ### `N = 137` -/

def pL137 : Prm := ⟨59, 28, 28, 139, 11, 18446744073709551616, 761149205909108398, 761149205909108398⟩
def pH137 : Prm := ⟨59, 28, 28, 139, 11, 18446744073709551616, 761184390281197230, 761184390281197230⟩
def pI137 : Prm := ⟨51, 25, 23, 139, 11, 18446744073709551616, 761149205909108398, 761184390281197230⟩
theorem L137_fin : (prmOK pL137 137 && ptTest pL137 (runFrom pL137 (fmask pL137) (cmask pL137) (hmask pL137) 1 136 (true, (init pL137), (init pL137))) 137 69 false) = true := by
  decide +kernel
theorem L137_ok : RunOK pL137 137 (runFrom pL137 (fmask pL137) (cmask pL137) (hmask pL137) 1 136 (true, (init pL137), (init pL137))) ∧ ptTest pL137 (runFrom pL137 (fmask pL137) (cmask pL137) (hmask pL137) 1 136 (true, (init pL137), (init pL137))) 137 69 false = true :=
  fin_run (runOK_init (prmOK_of_and L137_fin) true) (by decide) rfl L137_fin ptTest_fst
theorem H137_fin : (prmOK pH137 137 && ptTest pH137 (runFrom pH137 (fmask pH137) (cmask pH137) (hmask pH137) 1 136 (true, (init pH137), (init pH137))) 137 69 true) = true := by
  decide +kernel
theorem H137_ok : RunOK pH137 137 (runFrom pH137 (fmask pH137) (cmask pH137) (hmask pH137) 1 136 (true, (init pH137), (init pH137))) ∧ ptTest pH137 (runFrom pH137 (fmask pH137) (cmask pH137) (hmask pH137) 1 136 (true, (init pH137), (init pH137))) 137 69 true = true :=
  fin_run (runOK_init (prmOK_of_and H137_fin) true) (by decide) rfl H137_fin ptTest_fst
theorem I137_fin : (prmOK pI137 137 && intTest pI137 (runFrom pI137 (fmask pI137) (cmask pI137) (hmask pI137) 1 136 (true, (init pI137), (init pI137))) 137 8 false) = true := by
  decide +kernel
theorem I137_ok : RunOK pI137 137 (runFrom pI137 (fmask pI137) (cmask pI137) (hmask pI137) 1 136 (true, (init pI137), (init pI137))) ∧ intTest pI137 (runFrom pI137 (fmask pI137) (cmask pI137) (hmask pI137) 1 136 (true, (init pI137), (init pI137))) 137 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I137_fin) true) (by decide) rfl I137_fin intTest_fst
theorem link137 : linkOK pL137 pH137 pI137 = true := by decide +kernel
theorem cvx137 : ConvexBetweenHumps 137 :=
  cvx_of L137_ok H137_ok I137_ok link137 (by decide)

/-! ### `N = 138` -/

def pL138 : Prm := ⟨60, 29, 28, 140, 11, 18446744073709551616, 757401141655516128, 757401141655516128⟩
def pH138 : Prm := ⟨59, 28, 28, 140, 11, 18446744073709551616, 757436326027604960, 757436326027604960⟩
def pI138 : Prm := ⟨51, 25, 23, 140, 11, 18446744073709551616, 757401141655516128, 757436326027604960⟩
theorem L138_fin : (prmOK pL138 138 && ptTest pL138 (runFrom pL138 (fmask pL138) (cmask pL138) (hmask pL138) 1 137 (true, (init pL138), (init pL138))) 138 69 false) = true := by
  decide +kernel
theorem L138_ok : RunOK pL138 138 (runFrom pL138 (fmask pL138) (cmask pL138) (hmask pL138) 1 137 (true, (init pL138), (init pL138))) ∧ ptTest pL138 (runFrom pL138 (fmask pL138) (cmask pL138) (hmask pL138) 1 137 (true, (init pL138), (init pL138))) 138 69 false = true :=
  fin_run (runOK_init (prmOK_of_and L138_fin) true) (by decide) rfl L138_fin ptTest_fst
theorem H138_fin : (prmOK pH138 138 && ptTest pH138 (runFrom pH138 (fmask pH138) (cmask pH138) (hmask pH138) 1 137 (true, (init pH138), (init pH138))) 138 69 true) = true := by
  decide +kernel
theorem H138_ok : RunOK pH138 138 (runFrom pH138 (fmask pH138) (cmask pH138) (hmask pH138) 1 137 (true, (init pH138), (init pH138))) ∧ ptTest pH138 (runFrom pH138 (fmask pH138) (cmask pH138) (hmask pH138) 1 137 (true, (init pH138), (init pH138))) 138 69 true = true :=
  fin_run (runOK_init (prmOK_of_and H138_fin) true) (by decide) rfl H138_fin ptTest_fst
theorem I138_fin : (prmOK pI138 138 && intTest pI138 (runFrom pI138 (fmask pI138) (cmask pI138) (hmask pI138) 1 137 (true, (init pI138), (init pI138))) 138 8 true) = true := by
  decide +kernel
theorem I138_ok : RunOK pI138 138 (runFrom pI138 (fmask pI138) (cmask pI138) (hmask pI138) 1 137 (true, (init pI138), (init pI138))) ∧ intTest pI138 (runFrom pI138 (fmask pI138) (cmask pI138) (hmask pI138) 1 137 (true, (init pI138), (init pI138))) 138 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I138_fin) true) (by decide) rfl I138_fin intTest_fst
theorem link138 : linkOK pL138 pH138 pI138 = true := by decide +kernel
theorem cvx138 : ConvexBetweenHumps 138 :=
  cvx_of L138_ok H138_ok I138_ok link138 (by decide)
theorem cenlink138 : cenLinkOK pI138 138 = true := by decide +kernel
theorem cen138 : CenterUniqueMin 138 ∧ DipHyp 138 ∧ OnePointHyps 138 :=
  cen_of L138_ok H138_ok I138_ok link138 cenlink138

/-! ### `N = 139` -/

def pL139 : Prm := ⟨60, 29, 28, 141, 11, 18446744073709551616, 753650689756717369, 753650689756717369⟩
def pH139 : Prm := ⟨59, 28, 28, 141, 11, 18446744073709551616, 753685874128806201, 753685874128806201⟩
def pI139 : Prm := ⟨51, 25, 23, 141, 11, 18446744073709551616, 753650689756717369, 753685874128806201⟩
theorem L139_fin : (prmOK pL139 139 && ptTest pL139 (runFrom pL139 (fmask pL139) (cmask pL139) (hmask pL139) 1 138 (true, (init pL139), (init pL139))) 139 70 false) = true := by
  decide +kernel
theorem L139_ok : RunOK pL139 139 (runFrom pL139 (fmask pL139) (cmask pL139) (hmask pL139) 1 138 (true, (init pL139), (init pL139))) ∧ ptTest pL139 (runFrom pL139 (fmask pL139) (cmask pL139) (hmask pL139) 1 138 (true, (init pL139), (init pL139))) 139 70 false = true :=
  fin_run (runOK_init (prmOK_of_and L139_fin) true) (by decide) rfl L139_fin ptTest_fst
theorem H139_fin : (prmOK pH139 139 && ptTest pH139 (runFrom pH139 (fmask pH139) (cmask pH139) (hmask pH139) 1 138 (true, (init pH139), (init pH139))) 139 70 true) = true := by
  decide +kernel
theorem H139_ok : RunOK pH139 139 (runFrom pH139 (fmask pH139) (cmask pH139) (hmask pH139) 1 138 (true, (init pH139), (init pH139))) ∧ ptTest pH139 (runFrom pH139 (fmask pH139) (cmask pH139) (hmask pH139) 1 138 (true, (init pH139), (init pH139))) 139 70 true = true :=
  fin_run (runOK_init (prmOK_of_and H139_fin) true) (by decide) rfl H139_fin ptTest_fst
theorem I139_fin : (prmOK pI139 139 && intTest pI139 (runFrom pI139 (fmask pI139) (cmask pI139) (hmask pI139) 1 138 (true, (init pI139), (init pI139))) 139 8 false) = true := by
  decide +kernel
theorem I139_ok : RunOK pI139 139 (runFrom pI139 (fmask pI139) (cmask pI139) (hmask pI139) 1 138 (true, (init pI139), (init pI139))) ∧ intTest pI139 (runFrom pI139 (fmask pI139) (cmask pI139) (hmask pI139) 1 138 (true, (init pI139), (init pI139))) 139 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I139_fin) true) (by decide) rfl I139_fin intTest_fst
theorem link139 : linkOK pL139 pH139 pI139 = true := by decide +kernel
theorem cvx139 : ConvexBetweenHumps 139 :=
  cvx_of L139_ok H139_ok I139_ok link139 (by decide)

/-! ### `N = 140` -/

def pL140 : Prm := ⟨60, 29, 28, 142, 11, 18446744073709551616, 749986311246727695, 749986311246727695⟩
def pH140 : Prm := ⟨60, 29, 28, 142, 11, 18446744073709551616, 750021495618816527, 750021495618816527⟩
def pI140 : Prm := ⟨51, 25, 23, 142, 11, 18446744073709551616, 749986311246727695, 750021495618816527⟩
theorem L140_fin : (prmOK pL140 140 && ptTest pL140 (runFrom pL140 (fmask pL140) (cmask pL140) (hmask pL140) 1 139 (true, (init pL140), (init pL140))) 140 70 false) = true := by
  decide +kernel
theorem L140_ok : RunOK pL140 140 (runFrom pL140 (fmask pL140) (cmask pL140) (hmask pL140) 1 139 (true, (init pL140), (init pL140))) ∧ ptTest pL140 (runFrom pL140 (fmask pL140) (cmask pL140) (hmask pL140) 1 139 (true, (init pL140), (init pL140))) 140 70 false = true :=
  fin_run (runOK_init (prmOK_of_and L140_fin) true) (by decide) rfl L140_fin ptTest_fst
theorem H140_fin : (prmOK pH140 140 && ptTest pH140 (runFrom pH140 (fmask pH140) (cmask pH140) (hmask pH140) 1 139 (true, (init pH140), (init pH140))) 140 70 true) = true := by
  decide +kernel
theorem H140_ok : RunOK pH140 140 (runFrom pH140 (fmask pH140) (cmask pH140) (hmask pH140) 1 139 (true, (init pH140), (init pH140))) ∧ ptTest pH140 (runFrom pH140 (fmask pH140) (cmask pH140) (hmask pH140) 1 139 (true, (init pH140), (init pH140))) 140 70 true = true :=
  fin_run (runOK_init (prmOK_of_and H140_fin) true) (by decide) rfl H140_fin ptTest_fst
theorem I140_fin : (prmOK pI140 140 && intTest pI140 (runFrom pI140 (fmask pI140) (cmask pI140) (hmask pI140) 1 139 (true, (init pI140), (init pI140))) 140 8 true) = true := by
  decide +kernel
theorem I140_ok : RunOK pI140 140 (runFrom pI140 (fmask pI140) (cmask pI140) (hmask pI140) 1 139 (true, (init pI140), (init pI140))) ∧ intTest pI140 (runFrom pI140 (fmask pI140) (cmask pI140) (hmask pI140) 1 139 (true, (init pI140), (init pI140))) 140 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I140_fin) true) (by decide) rfl I140_fin intTest_fst
theorem link140 : linkOK pL140 pH140 pI140 = true := by decide +kernel
theorem cvx140 : ConvexBetweenHumps 140 :=
  cvx_of L140_ok H140_ok I140_ok link140 (by decide)
theorem cenlink140 : cenLinkOK pI140 140 = true := by decide +kernel
theorem cen140 : CenterUniqueMin 140 ∧ DipHyp 140 ∧ OnePointHyps 140 :=
  cen_of L140_ok H140_ok I140_ok link140 cenlink140

/-! ### `N = 141` -/

def pL141 : Prm := ⟨60, 29, 28, 143, 11, 18446744073709551616, 746319871066344136, 746319871066344136⟩
def pH141 : Prm := ⟨60, 29, 28, 143, 11, 18446744073709551616, 746355055438432968, 746355055438432968⟩
def pI141 : Prm := ⟨52, 25, 24, 143, 11, 18446744073709551616, 746319871066344136, 746355055438432968⟩
theorem L141_fin : (prmOK pL141 141 && ptTest pL141 (runFrom pL141 (fmask pL141) (cmask pL141) (hmask pL141) 1 140 (true, (init pL141), (init pL141))) 141 71 false) = true := by
  decide +kernel
theorem L141_ok : RunOK pL141 141 (runFrom pL141 (fmask pL141) (cmask pL141) (hmask pL141) 1 140 (true, (init pL141), (init pL141))) ∧ ptTest pL141 (runFrom pL141 (fmask pL141) (cmask pL141) (hmask pL141) 1 140 (true, (init pL141), (init pL141))) 141 71 false = true :=
  fin_run (runOK_init (prmOK_of_and L141_fin) true) (by decide) rfl L141_fin ptTest_fst
theorem H141_fin : (prmOK pH141 141 && ptTest pH141 (runFrom pH141 (fmask pH141) (cmask pH141) (hmask pH141) 1 140 (true, (init pH141), (init pH141))) 141 71 true) = true := by
  decide +kernel
theorem H141_ok : RunOK pH141 141 (runFrom pH141 (fmask pH141) (cmask pH141) (hmask pH141) 1 140 (true, (init pH141), (init pH141))) ∧ ptTest pH141 (runFrom pH141 (fmask pH141) (cmask pH141) (hmask pH141) 1 140 (true, (init pH141), (init pH141))) 141 71 true = true :=
  fin_run (runOK_init (prmOK_of_and H141_fin) true) (by decide) rfl H141_fin ptTest_fst
theorem I141_fin : (prmOK pI141 141 && intTest pI141 (runFrom pI141 (fmask pI141) (cmask pI141) (hmask pI141) 1 140 (true, (init pI141), (init pI141))) 141 8 false) = true := by
  decide +kernel
theorem I141_ok : RunOK pI141 141 (runFrom pI141 (fmask pI141) (cmask pI141) (hmask pI141) 1 140 (true, (init pI141), (init pI141))) ∧ intTest pI141 (runFrom pI141 (fmask pI141) (cmask pI141) (hmask pI141) 1 140 (true, (init pI141), (init pI141))) 141 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I141_fin) true) (by decide) rfl I141_fin intTest_fst
theorem link141 : linkOK pL141 pH141 pI141 = true := by decide +kernel
theorem cvx141 : ConvexBetweenHumps 141 :=
  cvx_of L141_ok H141_ok I141_ok link141 (by decide)

/-! ### `N = 142` -/

def pL142 : Prm := ⟨60, 29, 28, 144, 11, 18446744073709551616, 742736246878492818, 742736246878492818⟩
def pH142 : Prm := ⟨60, 29, 28, 144, 11, 18446744073709551616, 742771431250581650, 742771431250581650⟩
def pI142 : Prm := ⟨52, 25, 24, 144, 11, 18446744073709551616, 742736246878492818, 742771431250581650⟩
theorem L142_fin : (prmOK pL142 142 && ptTest pL142 (runFrom pL142 (fmask pL142) (cmask pL142) (hmask pL142) 1 141 (true, (init pL142), (init pL142))) 142 71 false) = true := by
  decide +kernel
theorem L142_ok : RunOK pL142 142 (runFrom pL142 (fmask pL142) (cmask pL142) (hmask pL142) 1 141 (true, (init pL142), (init pL142))) ∧ ptTest pL142 (runFrom pL142 (fmask pL142) (cmask pL142) (hmask pL142) 1 141 (true, (init pL142), (init pL142))) 142 71 false = true :=
  fin_run (runOK_init (prmOK_of_and L142_fin) true) (by decide) rfl L142_fin ptTest_fst
theorem H142_fin : (prmOK pH142 142 && ptTest pH142 (runFrom pH142 (fmask pH142) (cmask pH142) (hmask pH142) 1 141 (true, (init pH142), (init pH142))) 142 71 true) = true := by
  decide +kernel
theorem H142_ok : RunOK pH142 142 (runFrom pH142 (fmask pH142) (cmask pH142) (hmask pH142) 1 141 (true, (init pH142), (init pH142))) ∧ ptTest pH142 (runFrom pH142 (fmask pH142) (cmask pH142) (hmask pH142) 1 141 (true, (init pH142), (init pH142))) 142 71 true = true :=
  fin_run (runOK_init (prmOK_of_and H142_fin) true) (by decide) rfl H142_fin ptTest_fst
theorem I142_fin : (prmOK pI142 142 && intTest pI142 (runFrom pI142 (fmask pI142) (cmask pI142) (hmask pI142) 1 141 (true, (init pI142), (init pI142))) 142 8 true) = true := by
  decide +kernel
theorem I142_ok : RunOK pI142 142 (runFrom pI142 (fmask pI142) (cmask pI142) (hmask pI142) 1 141 (true, (init pI142), (init pI142))) ∧ intTest pI142 (runFrom pI142 (fmask pI142) (cmask pI142) (hmask pI142) 1 141 (true, (init pI142), (init pI142))) 142 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I142_fin) true) (by decide) rfl I142_fin intTest_fst
theorem link142 : linkOK pL142 pH142 pI142 = true := by decide +kernel
theorem cvx142 : ConvexBetweenHumps 142 :=
  cvx_of L142_ok H142_ok I142_ok link142 (by decide)
theorem cenlink142 : cenLinkOK pI142 142 = true := by decide +kernel
theorem cen142 : CenterUniqueMin 142 ∧ DipHyp 142 ∧ OnePointHyps 142 :=
  cen_of L142_ok H142_ok I142_ok link142 cenlink142

/-! ### `N = 143` -/

def pL143 : Prm := ⟨60, 29, 28, 145, 11, 18446744073709551616, 739150862542351422, 739150862542351422⟩
def pH143 : Prm := ⟨60, 29, 28, 145, 11, 18446744073709551616, 739186046914440254, 739186046914440254⟩
def pI143 : Prm := ⟨52, 25, 24, 145, 11, 18446744073709551616, 739150862542351422, 739186046914440254⟩
theorem L143_fin : (prmOK pL143 143 && ptTest pL143 (runFrom pL143 (fmask pL143) (cmask pL143) (hmask pL143) 1 142 (true, (init pL143), (init pL143))) 143 72 false) = true := by
  decide +kernel
theorem L143_ok : RunOK pL143 143 (runFrom pL143 (fmask pL143) (cmask pL143) (hmask pL143) 1 142 (true, (init pL143), (init pL143))) ∧ ptTest pL143 (runFrom pL143 (fmask pL143) (cmask pL143) (hmask pL143) 1 142 (true, (init pL143), (init pL143))) 143 72 false = true :=
  fin_run (runOK_init (prmOK_of_and L143_fin) true) (by decide) rfl L143_fin ptTest_fst
theorem H143_fin : (prmOK pH143 143 && ptTest pH143 (runFrom pH143 (fmask pH143) (cmask pH143) (hmask pH143) 1 142 (true, (init pH143), (init pH143))) 143 72 true) = true := by
  decide +kernel
theorem H143_ok : RunOK pH143 143 (runFrom pH143 (fmask pH143) (cmask pH143) (hmask pH143) 1 142 (true, (init pH143), (init pH143))) ∧ ptTest pH143 (runFrom pH143 (fmask pH143) (cmask pH143) (hmask pH143) 1 142 (true, (init pH143), (init pH143))) 143 72 true = true :=
  fin_run (runOK_init (prmOK_of_and H143_fin) true) (by decide) rfl H143_fin ptTest_fst
theorem I143_fin : (prmOK pI143 143 && intTest pI143 (runFrom pI143 (fmask pI143) (cmask pI143) (hmask pI143) 1 142 (true, (init pI143), (init pI143))) 143 8 false) = true := by
  decide +kernel
theorem I143_ok : RunOK pI143 143 (runFrom pI143 (fmask pI143) (cmask pI143) (hmask pI143) 1 142 (true, (init pI143), (init pI143))) ∧ intTest pI143 (runFrom pI143 (fmask pI143) (cmask pI143) (hmask pI143) 1 142 (true, (init pI143), (init pI143))) 143 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I143_fin) true) (by decide) rfl I143_fin intTest_fst
theorem link143 : linkOK pL143 pH143 pI143 = true := by decide +kernel
theorem cvx143 : ConvexBetweenHumps 143 :=
  cvx_of L143_ok H143_ok I143_ok link143 (by decide)

/-! ### `N = 144` -/

def pL144 : Prm := ⟨60, 29, 28, 146, 11, 18446744073709551616, 735645201020324895, 735645201020324895⟩
def pH144 : Prm := ⟨60, 29, 28, 146, 11, 18446744073709551616, 735680385392413727, 735680385392413727⟩
def pI144 : Prm := ⟨52, 25, 24, 146, 11, 18446744073709551616, 735645201020324895, 735680385392413727⟩
theorem L144_fin : (prmOK pL144 144 && ptTest pL144 (runFrom pL144 (fmask pL144) (cmask pL144) (hmask pL144) 1 143 (true, (init pL144), (init pL144))) 144 72 false) = true := by
  decide +kernel
theorem L144_ok : RunOK pL144 144 (runFrom pL144 (fmask pL144) (cmask pL144) (hmask pL144) 1 143 (true, (init pL144), (init pL144))) ∧ ptTest pL144 (runFrom pL144 (fmask pL144) (cmask pL144) (hmask pL144) 1 143 (true, (init pL144), (init pL144))) 144 72 false = true :=
  fin_run (runOK_init (prmOK_of_and L144_fin) true) (by decide) rfl L144_fin ptTest_fst
theorem H144_fin : (prmOK pH144 144 && ptTest pH144 (runFrom pH144 (fmask pH144) (cmask pH144) (hmask pH144) 1 143 (true, (init pH144), (init pH144))) 144 72 true) = true := by
  decide +kernel
theorem H144_ok : RunOK pH144 144 (runFrom pH144 (fmask pH144) (cmask pH144) (hmask pH144) 1 143 (true, (init pH144), (init pH144))) ∧ ptTest pH144 (runFrom pH144 (fmask pH144) (cmask pH144) (hmask pH144) 1 143 (true, (init pH144), (init pH144))) 144 72 true = true :=
  fin_run (runOK_init (prmOK_of_and H144_fin) true) (by decide) rfl H144_fin ptTest_fst
theorem I144_fin : (prmOK pI144 144 && intTest pI144 (runFrom pI144 (fmask pI144) (cmask pI144) (hmask pI144) 1 143 (true, (init pI144), (init pI144))) 144 8 true) = true := by
  decide +kernel
theorem I144_ok : RunOK pI144 144 (runFrom pI144 (fmask pI144) (cmask pI144) (hmask pI144) 1 143 (true, (init pI144), (init pI144))) ∧ intTest pI144 (runFrom pI144 (fmask pI144) (cmask pI144) (hmask pI144) 1 143 (true, (init pI144), (init pI144))) 144 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I144_fin) true) (by decide) rfl I144_fin intTest_fst
theorem link144 : linkOK pL144 pH144 pI144 = true := by decide +kernel
theorem cvx144 : ConvexBetweenHumps 144 :=
  cvx_of L144_ok H144_ok I144_ok link144 (by decide)
theorem cenlink144 : cenLinkOK pI144 144 = true := by decide +kernel
theorem cen144 : CenterUniqueMin 144 ∧ DipHyp 144 ∧ OnePointHyps 144 :=
  cen_of L144_ok H144_ok I144_ok link144 cenlink144

/-! ### `N = 145` -/

def pL145 : Prm := ⟨60, 29, 28, 147, 11, 18446744073709551616, 732138058294773091, 732138058294773091⟩
def pH145 : Prm := ⟨60, 29, 28, 147, 11, 18446744073709551616, 732173242666861923, 732173242666861923⟩
def pI145 : Prm := ⟨52, 25, 24, 147, 11, 18446744073709551616, 732138058294773091, 732173242666861923⟩
theorem L145_fin : (prmOK pL145 145 && ptTest pL145 (runFrom pL145 (fmask pL145) (cmask pL145) (hmask pL145) 1 144 (true, (init pL145), (init pL145))) 145 73 false) = true := by
  decide +kernel
theorem L145_ok : RunOK pL145 145 (runFrom pL145 (fmask pL145) (cmask pL145) (hmask pL145) 1 144 (true, (init pL145), (init pL145))) ∧ ptTest pL145 (runFrom pL145 (fmask pL145) (cmask pL145) (hmask pL145) 1 144 (true, (init pL145), (init pL145))) 145 73 false = true :=
  fin_run (runOK_init (prmOK_of_and L145_fin) true) (by decide) rfl L145_fin ptTest_fst
theorem H145_fin : (prmOK pH145 145 && ptTest pH145 (runFrom pH145 (fmask pH145) (cmask pH145) (hmask pH145) 1 144 (true, (init pH145), (init pH145))) 145 73 true) = true := by
  decide +kernel
theorem H145_ok : RunOK pH145 145 (runFrom pH145 (fmask pH145) (cmask pH145) (hmask pH145) 1 144 (true, (init pH145), (init pH145))) ∧ ptTest pH145 (runFrom pH145 (fmask pH145) (cmask pH145) (hmask pH145) 1 144 (true, (init pH145), (init pH145))) 145 73 true = true :=
  fin_run (runOK_init (prmOK_of_and H145_fin) true) (by decide) rfl H145_fin ptTest_fst
theorem I145_fin : (prmOK pI145 145 && intTest pI145 (runFrom pI145 (fmask pI145) (cmask pI145) (hmask pI145) 1 144 (true, (init pI145), (init pI145))) 145 8 false) = true := by
  decide +kernel
theorem I145_ok : RunOK pI145 145 (runFrom pI145 (fmask pI145) (cmask pI145) (hmask pI145) 1 144 (true, (init pI145), (init pI145))) ∧ intTest pI145 (runFrom pI145 (fmask pI145) (cmask pI145) (hmask pI145) 1 144 (true, (init pI145), (init pI145))) 145 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I145_fin) true) (by decide) rfl I145_fin intTest_fst
theorem link145 : linkOK pL145 pH145 pI145 = true := by decide +kernel
theorem cvx145 : ConvexBetweenHumps 145 :=
  cvx_of L145_ok H145_ok I145_ok link145 (by decide)

/-! ### `N = 146` -/

def pL146 : Prm := ⟨60, 29, 28, 148, 11, 18446744073709551616, 728707699137500949, 728707699137500949⟩
def pH146 : Prm := ⟨60, 29, 28, 148, 11, 18446744073709551616, 728742883509589781, 728742883509589781⟩
def pI146 : Prm := ⟨52, 25, 24, 148, 11, 18446744073709551616, 728707699137500949, 728742883509589781⟩
theorem L146_fin : (prmOK pL146 146 && ptTest pL146 (runFrom pL146 (fmask pL146) (cmask pL146) (hmask pL146) 1 145 (true, (init pL146), (init pL146))) 146 73 false) = true := by
  decide +kernel
theorem L146_ok : RunOK pL146 146 (runFrom pL146 (fmask pL146) (cmask pL146) (hmask pL146) 1 145 (true, (init pL146), (init pL146))) ∧ ptTest pL146 (runFrom pL146 (fmask pL146) (cmask pL146) (hmask pL146) 1 145 (true, (init pL146), (init pL146))) 146 73 false = true :=
  fin_run (runOK_init (prmOK_of_and L146_fin) true) (by decide) rfl L146_fin ptTest_fst
theorem H146_fin : (prmOK pH146 146 && ptTest pH146 (runFrom pH146 (fmask pH146) (cmask pH146) (hmask pH146) 1 145 (true, (init pH146), (init pH146))) 146 73 true) = true := by
  decide +kernel
theorem H146_ok : RunOK pH146 146 (runFrom pH146 (fmask pH146) (cmask pH146) (hmask pH146) 1 145 (true, (init pH146), (init pH146))) ∧ ptTest pH146 (runFrom pH146 (fmask pH146) (cmask pH146) (hmask pH146) 1 145 (true, (init pH146), (init pH146))) 146 73 true = true :=
  fin_run (runOK_init (prmOK_of_and H146_fin) true) (by decide) rfl H146_fin ptTest_fst
theorem I146_fin : (prmOK pI146 146 && intTest pI146 (runFrom pI146 (fmask pI146) (cmask pI146) (hmask pI146) 1 145 (true, (init pI146), (init pI146))) 146 8 true) = true := by
  decide +kernel
theorem I146_ok : RunOK pI146 146 (runFrom pI146 (fmask pI146) (cmask pI146) (hmask pI146) 1 145 (true, (init pI146), (init pI146))) ∧ intTest pI146 (runFrom pI146 (fmask pI146) (cmask pI146) (hmask pI146) 1 145 (true, (init pI146), (init pI146))) 146 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I146_fin) true) (by decide) rfl I146_fin intTest_fst
theorem link146 : linkOK pL146 pH146 pI146 = true := by decide +kernel
theorem cvx146 : ConvexBetweenHumps 146 :=
  cvx_of L146_ok H146_ok I146_ok link146 (by decide)
theorem cenlink146 : cenLinkOK pI146 146 = true := by decide +kernel
theorem cen146 : CenterUniqueMin 146 ∧ DipHyp 146 ∧ OnePointHyps 146 :=
  cen_of L146_ok H146_ok I146_ok link146 cenlink146

/-! ### `N = 147` -/

def pL147 : Prm := ⟨60, 29, 28, 149, 11, 18446744073709551616, 725276116862351299, 725276116862351299⟩
def pH147 : Prm := ⟨60, 29, 28, 149, 11, 18446744073709551616, 725311301234440131, 725311301234440131⟩
def pI147 : Prm := ⟨52, 25, 24, 149, 11, 18446744073709551616, 725276116862351299, 725311301234440131⟩
theorem L147_fin : (prmOK pL147 147 && ptTest pL147 (runFrom pL147 (fmask pL147) (cmask pL147) (hmask pL147) 1 146 (true, (init pL147), (init pL147))) 147 74 false) = true := by
  decide +kernel
theorem L147_ok : RunOK pL147 147 (runFrom pL147 (fmask pL147) (cmask pL147) (hmask pL147) 1 146 (true, (init pL147), (init pL147))) ∧ ptTest pL147 (runFrom pL147 (fmask pL147) (cmask pL147) (hmask pL147) 1 146 (true, (init pL147), (init pL147))) 147 74 false = true :=
  fin_run (runOK_init (prmOK_of_and L147_fin) true) (by decide) rfl L147_fin ptTest_fst
theorem H147_fin : (prmOK pH147 147 && ptTest pH147 (runFrom pH147 (fmask pH147) (cmask pH147) (hmask pH147) 1 146 (true, (init pH147), (init pH147))) 147 74 true) = true := by
  decide +kernel
theorem H147_ok : RunOK pH147 147 (runFrom pH147 (fmask pH147) (cmask pH147) (hmask pH147) 1 146 (true, (init pH147), (init pH147))) ∧ ptTest pH147 (runFrom pH147 (fmask pH147) (cmask pH147) (hmask pH147) 1 146 (true, (init pH147), (init pH147))) 147 74 true = true :=
  fin_run (runOK_init (prmOK_of_and H147_fin) true) (by decide) rfl H147_fin ptTest_fst
theorem I147_fin : (prmOK pI147 147 && intTest pI147 (runFrom pI147 (fmask pI147) (cmask pI147) (hmask pI147) 1 146 (true, (init pI147), (init pI147))) 147 8 false) = true := by
  decide +kernel
theorem I147_ok : RunOK pI147 147 (runFrom pI147 (fmask pI147) (cmask pI147) (hmask pI147) 1 146 (true, (init pI147), (init pI147))) ∧ intTest pI147 (runFrom pI147 (fmask pI147) (cmask pI147) (hmask pI147) 1 146 (true, (init pI147), (init pI147))) 147 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I147_fin) true) (by decide) rfl I147_fin intTest_fst
theorem link147 : linkOK pL147 pH147 pI147 = true := by decide +kernel
theorem cvx147 : ConvexBetweenHumps 147 :=
  cvx_of L147_ok H147_ok I147_ok link147 (by decide)

/-! ### `N = 148` -/

def pL148 : Prm := ⟨60, 29, 28, 150, 11, 18446744073709551616, 721918523323616096, 721918523323616096⟩
def pH148 : Prm := ⟨60, 29, 28, 150, 11, 18446744073709551616, 721953707695704928, 721953707695704928⟩
def pI148 : Prm := ⟨53, 25, 25, 150, 11, 18446744073709551616, 721918523323616096, 721953707695704928⟩
theorem L148_fin : (prmOK pL148 148 && ptTest pL148 (runFrom pL148 (fmask pL148) (cmask pL148) (hmask pL148) 1 147 (true, (init pL148), (init pL148))) 148 74 false) = true := by
  decide +kernel
theorem L148_ok : RunOK pL148 148 (runFrom pL148 (fmask pL148) (cmask pL148) (hmask pL148) 1 147 (true, (init pL148), (init pL148))) ∧ ptTest pL148 (runFrom pL148 (fmask pL148) (cmask pL148) (hmask pL148) 1 147 (true, (init pL148), (init pL148))) 148 74 false = true :=
  fin_run (runOK_init (prmOK_of_and L148_fin) true) (by decide) rfl L148_fin ptTest_fst
theorem H148_fin : (prmOK pH148 148 && ptTest pH148 (runFrom pH148 (fmask pH148) (cmask pH148) (hmask pH148) 1 147 (true, (init pH148), (init pH148))) 148 74 true) = true := by
  decide +kernel
theorem H148_ok : RunOK pH148 148 (runFrom pH148 (fmask pH148) (cmask pH148) (hmask pH148) 1 147 (true, (init pH148), (init pH148))) ∧ ptTest pH148 (runFrom pH148 (fmask pH148) (cmask pH148) (hmask pH148) 1 147 (true, (init pH148), (init pH148))) 148 74 true = true :=
  fin_run (runOK_init (prmOK_of_and H148_fin) true) (by decide) rfl H148_fin ptTest_fst
theorem I148_fin : (prmOK pI148 148 && intTest pI148 (runFrom pI148 (fmask pI148) (cmask pI148) (hmask pI148) 1 147 (true, (init pI148), (init pI148))) 148 8 true) = true := by
  decide +kernel
theorem I148_ok : RunOK pI148 148 (runFrom pI148 (fmask pI148) (cmask pI148) (hmask pI148) 1 147 (true, (init pI148), (init pI148))) ∧ intTest pI148 (runFrom pI148 (fmask pI148) (cmask pI148) (hmask pI148) 1 147 (true, (init pI148), (init pI148))) 148 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I148_fin) true) (by decide) rfl I148_fin intTest_fst
theorem link148 : linkOK pL148 pH148 pI148 = true := by decide +kernel
theorem cvx148 : ConvexBetweenHumps 148 :=
  cvx_of L148_ok H148_ok I148_ok link148 (by decide)
theorem cenlink148 : cenLinkOK pI148 148 = true := by decide +kernel
theorem cen148 : CenterUniqueMin 148 ∧ DipHyp 148 ∧ OnePointHyps 148 :=
  cen_of L148_ok H148_ok I148_ok link148 cenlink148

/-! ### `N = 149` -/

def pL149 : Prm := ⟨60, 29, 28, 151, 11, 18446744073709551616, 718559945469033644, 718559945469033644⟩
def pH149 : Prm := ⟨60, 29, 28, 151, 11, 18446744073709551616, 718595129841122476, 718595129841122476⟩
def pI149 : Prm := ⟨52, 25, 24, 151, 11, 18446744073709551616, 718559945469033644, 718595129841122476⟩
theorem L149_fin : (prmOK pL149 149 && ptTest pL149 (runFrom pL149 (fmask pL149) (cmask pL149) (hmask pL149) 1 148 (true, (init pL149), (init pL149))) 149 75 false) = true := by
  decide +kernel
theorem L149_ok : RunOK pL149 149 (runFrom pL149 (fmask pL149) (cmask pL149) (hmask pL149) 1 148 (true, (init pL149), (init pL149))) ∧ ptTest pL149 (runFrom pL149 (fmask pL149) (cmask pL149) (hmask pL149) 1 148 (true, (init pL149), (init pL149))) 149 75 false = true :=
  fin_run (runOK_init (prmOK_of_and L149_fin) true) (by decide) rfl L149_fin ptTest_fst
theorem H149_fin : (prmOK pH149 149 && ptTest pH149 (runFrom pH149 (fmask pH149) (cmask pH149) (hmask pH149) 1 148 (true, (init pH149), (init pH149))) 149 75 true) = true := by
  decide +kernel
theorem H149_ok : RunOK pH149 149 (runFrom pH149 (fmask pH149) (cmask pH149) (hmask pH149) 1 148 (true, (init pH149), (init pH149))) ∧ ptTest pH149 (runFrom pH149 (fmask pH149) (cmask pH149) (hmask pH149) 1 148 (true, (init pH149), (init pH149))) 149 75 true = true :=
  fin_run (runOK_init (prmOK_of_and H149_fin) true) (by decide) rfl H149_fin ptTest_fst
theorem I149_fin : (prmOK pI149 149 && intTest pI149 (runFrom pI149 (fmask pI149) (cmask pI149) (hmask pI149) 1 148 (true, (init pI149), (init pI149))) 149 8 false) = true := by
  decide +kernel
theorem I149_ok : RunOK pI149 149 (runFrom pI149 (fmask pI149) (cmask pI149) (hmask pI149) 1 148 (true, (init pI149), (init pI149))) ∧ intTest pI149 (runFrom pI149 (fmask pI149) (cmask pI149) (hmask pI149) 1 148 (true, (init pI149), (init pI149))) 149 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I149_fin) true) (by decide) rfl I149_fin intTest_fst
theorem link149 : linkOK pL149 pH149 pI149 = true := by decide +kernel
theorem cvx149 : ConvexBetweenHumps 149 :=
  cvx_of L149_ok H149_ok I149_ok link149 (by decide)

/-! ### `N = 150` -/

def pL150 : Prm := ⟨60, 29, 28, 152, 11, 18446744073709551616, 715272697114744213, 715272697114744213⟩
def pH150 : Prm := ⟨60, 29, 28, 152, 11, 18446744073709551616, 715307881486833045, 715307881486833045⟩
def pI150 : Prm := ⟨53, 25, 25, 152, 11, 18446744073709551616, 715272697114744213, 715307881486833045⟩
theorem L150_fin : (prmOK pL150 150 && ptTest pL150 (runFrom pL150 (fmask pL150) (cmask pL150) (hmask pL150) 1 149 (true, (init pL150), (init pL150))) 150 75 false) = true := by
  decide +kernel
theorem L150_ok : RunOK pL150 150 (runFrom pL150 (fmask pL150) (cmask pL150) (hmask pL150) 1 149 (true, (init pL150), (init pL150))) ∧ ptTest pL150 (runFrom pL150 (fmask pL150) (cmask pL150) (hmask pL150) 1 149 (true, (init pL150), (init pL150))) 150 75 false = true :=
  fin_run (runOK_init (prmOK_of_and L150_fin) true) (by decide) rfl L150_fin ptTest_fst
theorem H150_fin : (prmOK pH150 150 && ptTest pH150 (runFrom pH150 (fmask pH150) (cmask pH150) (hmask pH150) 1 149 (true, (init pH150), (init pH150))) 150 75 true) = true := by
  decide +kernel
theorem H150_ok : RunOK pH150 150 (runFrom pH150 (fmask pH150) (cmask pH150) (hmask pH150) 1 149 (true, (init pH150), (init pH150))) ∧ ptTest pH150 (runFrom pH150 (fmask pH150) (cmask pH150) (hmask pH150) 1 149 (true, (init pH150), (init pH150))) 150 75 true = true :=
  fin_run (runOK_init (prmOK_of_and H150_fin) true) (by decide) rfl H150_fin ptTest_fst
theorem I150_fin : (prmOK pI150 150 && intTest pI150 (runFrom pI150 (fmask pI150) (cmask pI150) (hmask pI150) 1 149 (true, (init pI150), (init pI150))) 150 8 true) = true := by
  decide +kernel
theorem I150_ok : RunOK pI150 150 (runFrom pI150 (fmask pI150) (cmask pI150) (hmask pI150) 1 149 (true, (init pI150), (init pI150))) ∧ intTest pI150 (runFrom pI150 (fmask pI150) (cmask pI150) (hmask pI150) 1 149 (true, (init pI150), (init pI150))) 150 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I150_fin) true) (by decide) rfl I150_fin intTest_fst
theorem link150 : linkOK pL150 pH150 pI150 = true := by decide +kernel
theorem cvx150 : ConvexBetweenHumps 150 :=
  cvx_of L150_ok H150_ok I150_ok link150 (by decide)
theorem cenlink150 : cenLinkOK pI150 150 = true := by decide +kernel
theorem cen150 : CenterUniqueMin 150 ∧ DipHyp 150 ∧ OnePointHyps 150 :=
  cen_of L150_ok H150_ok I150_ok link150 cenlink150

/-! ### `N = 151` -/

def pL151 : Prm := ⟨60, 28, 29, 153, 11, 18446744073709551616, 711984685408876079, 711984685408876079⟩
def pH151 : Prm := ⟨60, 29, 28, 153, 11, 18446744073709551616, 712019869780964911, 712019869780964911⟩
def pI151 : Prm := ⟨53, 25, 25, 153, 11, 18446744073709551616, 711984685408876079, 712019869780964911⟩
theorem L151_fin : (prmOK pL151 151 && ptTest pL151 (runFrom pL151 (fmask pL151) (cmask pL151) (hmask pL151) 1 150 (true, (init pL151), (init pL151))) 151 76 false) = true := by
  decide +kernel
theorem L151_ok : RunOK pL151 151 (runFrom pL151 (fmask pL151) (cmask pL151) (hmask pL151) 1 150 (true, (init pL151), (init pL151))) ∧ ptTest pL151 (runFrom pL151 (fmask pL151) (cmask pL151) (hmask pL151) 1 150 (true, (init pL151), (init pL151))) 151 76 false = true :=
  fin_run (runOK_init (prmOK_of_and L151_fin) true) (by decide) rfl L151_fin ptTest_fst
theorem H151_fin : (prmOK pH151 151 && ptTest pH151 (runFrom pH151 (fmask pH151) (cmask pH151) (hmask pH151) 1 150 (true, (init pH151), (init pH151))) 151 76 true) = true := by
  decide +kernel
theorem H151_ok : RunOK pH151 151 (runFrom pH151 (fmask pH151) (cmask pH151) (hmask pH151) 1 150 (true, (init pH151), (init pH151))) ∧ ptTest pH151 (runFrom pH151 (fmask pH151) (cmask pH151) (hmask pH151) 1 150 (true, (init pH151), (init pH151))) 151 76 true = true :=
  fin_run (runOK_init (prmOK_of_and H151_fin) true) (by decide) rfl H151_fin ptTest_fst
theorem I151_fin : (prmOK pI151 151 && intTest pI151 (runFrom pI151 (fmask pI151) (cmask pI151) (hmask pI151) 1 150 (true, (init pI151), (init pI151))) 151 8 false) = true := by
  decide +kernel
theorem I151_ok : RunOK pI151 151 (runFrom pI151 (fmask pI151) (cmask pI151) (hmask pI151) 1 150 (true, (init pI151), (init pI151))) ∧ intTest pI151 (runFrom pI151 (fmask pI151) (cmask pI151) (hmask pI151) 1 150 (true, (init pI151), (init pI151))) 151 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I151_fin) true) (by decide) rfl I151_fin intTest_fst
theorem link151 : linkOK pL151 pH151 pI151 = true := by decide +kernel
theorem cvx151 : ConvexBetweenHumps 151 :=
  cvx_of L151_ok H151_ok I151_ok link151 (by decide)

/-! ### `N = 152` -/

def pL152 : Prm := ⟨60, 29, 28, 154, 11, 18446744073709551616, 708765471385795283, 708765471385795283⟩
def pH152 : Prm := ⟨60, 28, 29, 154, 11, 18446744073709551616, 708800655757884115, 708800655757884115⟩
def pI152 : Prm := ⟨53, 25, 25, 154, 11, 18446744073709551616, 708765471385795283, 708800655757884115⟩
theorem L152_fin : (prmOK pL152 152 && ptTest pL152 (runFrom pL152 (fmask pL152) (cmask pL152) (hmask pL152) 1 151 (true, (init pL152), (init pL152))) 152 76 false) = true := by
  decide +kernel
theorem L152_ok : RunOK pL152 152 (runFrom pL152 (fmask pL152) (cmask pL152) (hmask pL152) 1 151 (true, (init pL152), (init pL152))) ∧ ptTest pL152 (runFrom pL152 (fmask pL152) (cmask pL152) (hmask pL152) 1 151 (true, (init pL152), (init pL152))) 152 76 false = true :=
  fin_run (runOK_init (prmOK_of_and L152_fin) true) (by decide) rfl L152_fin ptTest_fst
theorem H152_fin : (prmOK pH152 152 && ptTest pH152 (runFrom pH152 (fmask pH152) (cmask pH152) (hmask pH152) 1 151 (true, (init pH152), (init pH152))) 152 76 true) = true := by
  decide +kernel
theorem H152_ok : RunOK pH152 152 (runFrom pH152 (fmask pH152) (cmask pH152) (hmask pH152) 1 151 (true, (init pH152), (init pH152))) ∧ ptTest pH152 (runFrom pH152 (fmask pH152) (cmask pH152) (hmask pH152) 1 151 (true, (init pH152), (init pH152))) 152 76 true = true :=
  fin_run (runOK_init (prmOK_of_and H152_fin) true) (by decide) rfl H152_fin ptTest_fst
theorem I152_fin : (prmOK pI152 152 && intTest pI152 (runFrom pI152 (fmask pI152) (cmask pI152) (hmask pI152) 1 151 (true, (init pI152), (init pI152))) 152 8 true) = true := by
  decide +kernel
theorem I152_ok : RunOK pI152 152 (runFrom pI152 (fmask pI152) (cmask pI152) (hmask pI152) 1 151 (true, (init pI152), (init pI152))) ∧ intTest pI152 (runFrom pI152 (fmask pI152) (cmask pI152) (hmask pI152) 1 151 (true, (init pI152), (init pI152))) 152 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I152_fin) true) (by decide) rfl I152_fin intTest_fst
theorem link152 : linkOK pL152 pH152 pI152 = true := by decide +kernel
theorem cvx152 : ConvexBetweenHumps 152 :=
  cvx_of L152_ok H152_ok I152_ok link152 (by decide)
theorem cenlink152 : cenLinkOK pI152 152 = true := by decide +kernel
theorem cen152 : CenterUniqueMin 152 ∧ DipHyp 152 ∧ OnePointHyps 152 :=
  cen_of L152_ok H152_ok I152_ok link152 cenlink152

/-! ### `N = 153` -/

def pL153 : Prm := ⟨60, 29, 28, 155, 11, 18446744073709551616, 705545698465642171, 705545698465642171⟩
def pH153 : Prm := ⟨60, 29, 28, 155, 11, 18446744073709551616, 705580882837731003, 705580882837731003⟩
def pI153 : Prm := ⟨53, 26, 24, 155, 11, 18446744073709551616, 705545698465642171, 705580882837731003⟩
theorem L153_fin : (prmOK pL153 153 && ptTest pL153 (runFrom pL153 (fmask pL153) (cmask pL153) (hmask pL153) 1 152 (true, (init pL153), (init pL153))) 153 77 false) = true := by
  decide +kernel
theorem L153_ok : RunOK pL153 153 (runFrom pL153 (fmask pL153) (cmask pL153) (hmask pL153) 1 152 (true, (init pL153), (init pL153))) ∧ ptTest pL153 (runFrom pL153 (fmask pL153) (cmask pL153) (hmask pL153) 1 152 (true, (init pL153), (init pL153))) 153 77 false = true :=
  fin_run (runOK_init (prmOK_of_and L153_fin) true) (by decide) rfl L153_fin ptTest_fst
theorem H153_fin : (prmOK pH153 153 && ptTest pH153 (runFrom pH153 (fmask pH153) (cmask pH153) (hmask pH153) 1 152 (true, (init pH153), (init pH153))) 153 77 true) = true := by
  decide +kernel
theorem H153_ok : RunOK pH153 153 (runFrom pH153 (fmask pH153) (cmask pH153) (hmask pH153) 1 152 (true, (init pH153), (init pH153))) ∧ ptTest pH153 (runFrom pH153 (fmask pH153) (cmask pH153) (hmask pH153) 1 152 (true, (init pH153), (init pH153))) 153 77 true = true :=
  fin_run (runOK_init (prmOK_of_and H153_fin) true) (by decide) rfl H153_fin ptTest_fst
theorem I153_fin : (prmOK pI153 153 && intTest pI153 (runFrom pI153 (fmask pI153) (cmask pI153) (hmask pI153) 1 152 (true, (init pI153), (init pI153))) 153 8 false) = true := by
  decide +kernel
theorem I153_ok : RunOK pI153 153 (runFrom pI153 (fmask pI153) (cmask pI153) (hmask pI153) 1 152 (true, (init pI153), (init pI153))) ∧ intTest pI153 (runFrom pI153 (fmask pI153) (cmask pI153) (hmask pI153) 1 152 (true, (init pI153), (init pI153))) 153 8 false = true :=
  fin_run (runOK_init (prmOK_of_and I153_fin) true) (by decide) rfl I153_fin intTest_fst
theorem link153 : linkOK pL153 pH153 pI153 = true := by decide +kernel
theorem cvx153 : ConvexBetweenHumps 153 :=
  cvx_of L153_ok H153_ok I153_ok link153 (by decide)

/-! ### `N = 154` -/

def pL154 : Prm := ⟨60, 28, 29, 156, 11, 18446744073709551616, 702392311239196902, 702392311239196902⟩
def pH154 : Prm := ⟨60, 29, 28, 156, 11, 18446744073709551616, 702427495611285734, 702427495611285734⟩
def pI154 : Prm := ⟨53, 26, 24, 156, 11, 18446744073709551616, 702392311239196902, 702427495611285734⟩
theorem L154_fin : (prmOK pL154 154 && ptTest pL154 (runFrom pL154 (fmask pL154) (cmask pL154) (hmask pL154) 1 153 (true, (init pL154), (init pL154))) 154 77 false) = true := by
  decide +kernel
theorem L154_ok : RunOK pL154 154 (runFrom pL154 (fmask pL154) (cmask pL154) (hmask pL154) 1 153 (true, (init pL154), (init pL154))) ∧ ptTest pL154 (runFrom pL154 (fmask pL154) (cmask pL154) (hmask pL154) 1 153 (true, (init pL154), (init pL154))) 154 77 false = true :=
  fin_run (runOK_init (prmOK_of_and L154_fin) true) (by decide) rfl L154_fin ptTest_fst
theorem H154_fin : (prmOK pH154 154 && ptTest pH154 (runFrom pH154 (fmask pH154) (cmask pH154) (hmask pH154) 1 153 (true, (init pH154), (init pH154))) 154 77 true) = true := by
  decide +kernel
theorem H154_ok : RunOK pH154 154 (runFrom pH154 (fmask pH154) (cmask pH154) (hmask pH154) 1 153 (true, (init pH154), (init pH154))) ∧ ptTest pH154 (runFrom pH154 (fmask pH154) (cmask pH154) (hmask pH154) 1 153 (true, (init pH154), (init pH154))) 154 77 true = true :=
  fin_run (runOK_init (prmOK_of_and H154_fin) true) (by decide) rfl H154_fin ptTest_fst
theorem I154_fin : (prmOK pI154 154 && intTest pI154 (runFrom pI154 (fmask pI154) (cmask pI154) (hmask pI154) 1 153 (true, (init pI154), (init pI154))) 154 8 true) = true := by
  decide +kernel
theorem I154_ok : RunOK pI154 154 (runFrom pI154 (fmask pI154) (cmask pI154) (hmask pI154) 1 153 (true, (init pI154), (init pI154))) ∧ intTest pI154 (runFrom pI154 (fmask pI154) (cmask pI154) (hmask pI154) 1 153 (true, (init pI154), (init pI154))) 154 8 true = true :=
  fin_run (runOK_init (prmOK_of_and I154_fin) true) (by decide) rfl I154_fin intTest_fst
theorem link154 : linkOK pL154 pH154 pI154 = true := by decide +kernel
theorem cvx154 : ConvexBetweenHumps 154 :=
  cvx_of L154_ok H154_ok I154_ok link154 (by decide)
theorem cenlink154 : cenLinkOK pI154 154 = true := by decide +kernel
theorem cen154 : CenterUniqueMin 154 ∧ DipHyp 154 ∧ OnePointHyps 154 :=
  cen_of L154_ok H154_ok I154_ok link154 cenlink154

/-! ### `N = 155` -/

def pL155 : Prm := ⟨60, 28, 29, 157, 11, 18446744073709551616, 699238554281136836, 699238554281136836⟩
def pH155 : Prm := ⟨60, 28, 29, 157, 11, 18446744073709551616, 699273738653225668, 699273738653225668⟩
def pI155 : Prm := ⟨53, 26, 24, 157, 11, 18446744073709551616, 699238554281136836, 699273738653225668⟩
theorem L155_fin : (prmOK pL155 155 && ptTest pL155 (runFrom pL155 (fmask pL155) (cmask pL155) (hmask pL155) 1 154 (true, (init pL155), (init pL155))) 155 78 false) = true := by
  decide +kernel
theorem L155_ok : RunOK pL155 155 (runFrom pL155 (fmask pL155) (cmask pL155) (hmask pL155) 1 154 (true, (init pL155), (init pL155))) ∧ ptTest pL155 (runFrom pL155 (fmask pL155) (cmask pL155) (hmask pL155) 1 154 (true, (init pL155), (init pL155))) 155 78 false = true :=
  fin_run (runOK_init (prmOK_of_and L155_fin) true) (by decide) rfl L155_fin ptTest_fst
theorem H155_fin : (prmOK pH155 155 && ptTest pH155 (runFrom pH155 (fmask pH155) (cmask pH155) (hmask pH155) 1 154 (true, (init pH155), (init pH155))) 155 78 true) = true := by
  decide +kernel
theorem H155_ok : RunOK pH155 155 (runFrom pH155 (fmask pH155) (cmask pH155) (hmask pH155) 1 154 (true, (init pH155), (init pH155))) ∧ ptTest pH155 (runFrom pH155 (fmask pH155) (cmask pH155) (hmask pH155) 1 154 (true, (init pH155), (init pH155))) 155 78 true = true :=
  fin_run (runOK_init (prmOK_of_and H155_fin) true) (by decide) rfl H155_fin ptTest_fst
theorem I155_fin : (prmOK pI155 155 && intTest pI155 (runFrom pI155 (fmask pI155) (cmask pI155) (hmask pI155) 1 154 (true, (init pI155), (init pI155))) 155 9 false) = true := by
  decide +kernel
theorem I155_ok : RunOK pI155 155 (runFrom pI155 (fmask pI155) (cmask pI155) (hmask pI155) 1 154 (true, (init pI155), (init pI155))) ∧ intTest pI155 (runFrom pI155 (fmask pI155) (cmask pI155) (hmask pI155) 1 154 (true, (init pI155), (init pI155))) 155 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I155_fin) true) (by decide) rfl I155_fin intTest_fst
theorem link155 : linkOK pL155 pH155 pI155 = true := by decide +kernel
theorem cvx155 : ConvexBetweenHumps 155 :=
  cvx_of L155_ok H155_ok I155_ok link155 (by decide)

/-! ### `N = 156` -/

def pL156 : Prm := ⟨60, 28, 29, 158, 11, 18446744073709551616, 696148883804309981, 696148883804309981⟩
def pH156 : Prm := ⟨60, 28, 29, 158, 11, 18446744073709551616, 696184068176398813, 696184068176398813⟩
def pI156 : Prm := ⟨53, 26, 24, 158, 11, 18446744073709551616, 696148883804309981, 696184068176398813⟩
theorem L156_fin : (prmOK pL156 156 && ptTest pL156 (runFrom pL156 (fmask pL156) (cmask pL156) (hmask pL156) 1 155 (true, (init pL156), (init pL156))) 156 78 false) = true := by
  decide +kernel
theorem L156_ok : RunOK pL156 156 (runFrom pL156 (fmask pL156) (cmask pL156) (hmask pL156) 1 155 (true, (init pL156), (init pL156))) ∧ ptTest pL156 (runFrom pL156 (fmask pL156) (cmask pL156) (hmask pL156) 1 155 (true, (init pL156), (init pL156))) 156 78 false = true :=
  fin_run (runOK_init (prmOK_of_and L156_fin) true) (by decide) rfl L156_fin ptTest_fst
theorem H156_fin : (prmOK pH156 156 && ptTest pH156 (runFrom pH156 (fmask pH156) (cmask pH156) (hmask pH156) 1 155 (true, (init pH156), (init pH156))) 156 78 true) = true := by
  decide +kernel
theorem H156_ok : RunOK pH156 156 (runFrom pH156 (fmask pH156) (cmask pH156) (hmask pH156) 1 155 (true, (init pH156), (init pH156))) ∧ ptTest pH156 (runFrom pH156 (fmask pH156) (cmask pH156) (hmask pH156) 1 155 (true, (init pH156), (init pH156))) 156 78 true = true :=
  fin_run (runOK_init (prmOK_of_and H156_fin) true) (by decide) rfl H156_fin ptTest_fst
theorem I156_fin : (prmOK pI156 156 && intTest pI156 (runFrom pI156 (fmask pI156) (cmask pI156) (hmask pI156) 1 155 (true, (init pI156), (init pI156))) 156 9 true) = true := by
  decide +kernel
theorem I156_ok : RunOK pI156 156 (runFrom pI156 (fmask pI156) (cmask pI156) (hmask pI156) 1 155 (true, (init pI156), (init pI156))) ∧ intTest pI156 (runFrom pI156 (fmask pI156) (cmask pI156) (hmask pI156) 1 155 (true, (init pI156), (init pI156))) 156 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I156_fin) true) (by decide) rfl I156_fin intTest_fst
theorem link156 : linkOK pL156 pH156 pI156 = true := by decide +kernel
theorem cvx156 : ConvexBetweenHumps 156 :=
  cvx_of L156_ok H156_ok I156_ok link156 (by decide)
theorem cenlink156 : cenLinkOK pI156 156 = true := by decide +kernel
theorem cen156 : CenterUniqueMin 156 ∧ DipHyp 156 ∧ OnePointHyps 156 :=
  cen_of L156_ok H156_ok I156_ok link156 cenlink156

/-! ### `N = 157` -/

def pL157 : Prm := ⟨60, 28, 29, 159, 11, 18446744073709551616, 693059018595167183, 693059018595167183⟩
def pH157 : Prm := ⟨60, 28, 29, 159, 11, 18446744073709551616, 693094202967256015, 693094202967256015⟩
def pI157 : Prm := ⟨53, 26, 24, 159, 11, 18446744073709551616, 693059018595167183, 693094202967256015⟩
theorem L157_fin : (prmOK pL157 157 && ptTest pL157 (runFrom pL157 (fmask pL157) (cmask pL157) (hmask pL157) 1 156 (true, (init pL157), (init pL157))) 157 79 false) = true := by
  decide +kernel
theorem L157_ok : RunOK pL157 157 (runFrom pL157 (fmask pL157) (cmask pL157) (hmask pL157) 1 156 (true, (init pL157), (init pL157))) ∧ ptTest pL157 (runFrom pL157 (fmask pL157) (cmask pL157) (hmask pL157) 1 156 (true, (init pL157), (init pL157))) 157 79 false = true :=
  fin_run (runOK_init (prmOK_of_and L157_fin) true) (by decide) rfl L157_fin ptTest_fst
theorem H157_fin : (prmOK pH157 157 && ptTest pH157 (runFrom pH157 (fmask pH157) (cmask pH157) (hmask pH157) 1 156 (true, (init pH157), (init pH157))) 157 79 true) = true := by
  decide +kernel
theorem H157_ok : RunOK pH157 157 (runFrom pH157 (fmask pH157) (cmask pH157) (hmask pH157) 1 156 (true, (init pH157), (init pH157))) ∧ ptTest pH157 (runFrom pH157 (fmask pH157) (cmask pH157) (hmask pH157) 1 156 (true, (init pH157), (init pH157))) 157 79 true = true :=
  fin_run (runOK_init (prmOK_of_and H157_fin) true) (by decide) rfl H157_fin ptTest_fst
theorem I157_fin : (prmOK pI157 157 && intTest pI157 (runFrom pI157 (fmask pI157) (cmask pI157) (hmask pI157) 1 156 (true, (init pI157), (init pI157))) 157 9 false) = true := by
  decide +kernel
theorem I157_ok : RunOK pI157 157 (runFrom pI157 (fmask pI157) (cmask pI157) (hmask pI157) 1 156 (true, (init pI157), (init pI157))) ∧ intTest pI157 (runFrom pI157 (fmask pI157) (cmask pI157) (hmask pI157) 1 156 (true, (init pI157), (init pI157))) 157 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I157_fin) true) (by decide) rfl I157_fin intTest_fst
theorem link157 : linkOK pL157 pH157 pI157 = true := by decide +kernel
theorem cvx157 : ConvexBetweenHumps 157 :=
  cvx_of L157_ok H157_ok I157_ok link157 (by decide)

/-! ### `N = 158` -/

def pL158 : Prm := ⟨60, 28, 29, 160, 11, 18446744073709551616, 690031046873865460, 690031046873865460⟩
def pH158 : Prm := ⟨60, 28, 29, 160, 11, 18446744073709551616, 690066231245954292, 690066231245954292⟩
def pI158 : Prm := ⟨52, 25, 24, 160, 11, 18446744073709551616, 690031046873865460, 690066231245954292⟩
theorem L158_fin : (prmOK pL158 158 && ptTest pL158 (runFrom pL158 (fmask pL158) (cmask pL158) (hmask pL158) 1 157 (true, (init pL158), (init pL158))) 158 79 false) = true := by
  decide +kernel
theorem L158_ok : RunOK pL158 158 (runFrom pL158 (fmask pL158) (cmask pL158) (hmask pL158) 1 157 (true, (init pL158), (init pL158))) ∧ ptTest pL158 (runFrom pL158 (fmask pL158) (cmask pL158) (hmask pL158) 1 157 (true, (init pL158), (init pL158))) 158 79 false = true :=
  fin_run (runOK_init (prmOK_of_and L158_fin) true) (by decide) rfl L158_fin ptTest_fst
theorem H158_fin : (prmOK pH158 158 && ptTest pH158 (runFrom pH158 (fmask pH158) (cmask pH158) (hmask pH158) 1 157 (true, (init pH158), (init pH158))) 158 79 true) = true := by
  decide +kernel
theorem H158_ok : RunOK pH158 158 (runFrom pH158 (fmask pH158) (cmask pH158) (hmask pH158) 1 157 (true, (init pH158), (init pH158))) ∧ ptTest pH158 (runFrom pH158 (fmask pH158) (cmask pH158) (hmask pH158) 1 157 (true, (init pH158), (init pH158))) 158 79 true = true :=
  fin_run (runOK_init (prmOK_of_and H158_fin) true) (by decide) rfl H158_fin ptTest_fst
theorem I158_fin : (prmOK pI158 158 && intTest pI158 (runFrom pI158 (fmask pI158) (cmask pI158) (hmask pI158) 1 157 (true, (init pI158), (init pI158))) 158 9 true) = true := by
  decide +kernel
theorem I158_ok : RunOK pI158 158 (runFrom pI158 (fmask pI158) (cmask pI158) (hmask pI158) 1 157 (true, (init pI158), (init pI158))) ∧ intTest pI158 (runFrom pI158 (fmask pI158) (cmask pI158) (hmask pI158) 1 157 (true, (init pI158), (init pI158))) 158 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I158_fin) true) (by decide) rfl I158_fin intTest_fst
theorem link158 : linkOK pL158 pH158 pI158 = true := by decide +kernel
theorem cvx158 : ConvexBetweenHumps 158 :=
  cvx_of L158_ok H158_ok I158_ok link158 (by decide)
theorem cenlink158 : cenLinkOK pI158 158 = true := by decide +kernel
theorem cen158 : CenterUniqueMin 158 ∧ DipHyp 158 ∧ OnePointHyps 158 :=
  cen_of L158_ok H158_ok I158_ok link158 cenlink158

/-! ### `N = 159` -/

def pL159 : Prm := ⟨60, 28, 29, 161, 11, 18446744073709551616, 687003042287217307, 687003042287217307⟩
def pH159 : Prm := ⟨60, 28, 29, 161, 11, 18446744073709551616, 687038226659306139, 687038226659306139⟩
def pI159 : Prm := ⟨52, 25, 24, 161, 11, 18446744073709551616, 687003042287217307, 687038226659306139⟩
theorem L159_fin : (prmOK pL159 159 && ptTest pL159 (runFrom pL159 (fmask pL159) (cmask pL159) (hmask pL159) 1 158 (true, (init pL159), (init pL159))) 159 80 false) = true := by
  decide +kernel
theorem L159_ok : RunOK pL159 159 (runFrom pL159 (fmask pL159) (cmask pL159) (hmask pL159) 1 158 (true, (init pL159), (init pL159))) ∧ ptTest pL159 (runFrom pL159 (fmask pL159) (cmask pL159) (hmask pL159) 1 158 (true, (init pL159), (init pL159))) 159 80 false = true :=
  fin_run (runOK_init (prmOK_of_and L159_fin) true) (by decide) rfl L159_fin ptTest_fst
theorem H159_fin : (prmOK pH159 159 && ptTest pH159 (runFrom pH159 (fmask pH159) (cmask pH159) (hmask pH159) 1 158 (true, (init pH159), (init pH159))) 159 80 true) = true := by
  decide +kernel
theorem H159_ok : RunOK pH159 159 (runFrom pH159 (fmask pH159) (cmask pH159) (hmask pH159) 1 158 (true, (init pH159), (init pH159))) ∧ ptTest pH159 (runFrom pH159 (fmask pH159) (cmask pH159) (hmask pH159) 1 158 (true, (init pH159), (init pH159))) 159 80 true = true :=
  fin_run (runOK_init (prmOK_of_and H159_fin) true) (by decide) rfl H159_fin ptTest_fst
theorem I159_fin : (prmOK pI159 159 && intTest pI159 (runFrom pI159 (fmask pI159) (cmask pI159) (hmask pI159) 1 158 (true, (init pI159), (init pI159))) 159 9 false) = true := by
  decide +kernel
theorem I159_ok : RunOK pI159 159 (runFrom pI159 (fmask pI159) (cmask pI159) (hmask pI159) 1 158 (true, (init pI159), (init pI159))) ∧ intTest pI159 (runFrom pI159 (fmask pI159) (cmask pI159) (hmask pI159) 1 158 (true, (init pI159), (init pI159))) 159 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I159_fin) true) (by decide) rfl I159_fin intTest_fst
theorem link159 : linkOK pL159 pH159 pI159 = true := by decide +kernel
theorem cvx159 : ConvexBetweenHumps 159 :=
  cvx_of L159_ok H159_ok I159_ok link159 (by decide)

/-! ### `N = 160` -/

def pL160 : Prm := ⟨60, 28, 29, 162, 11, 18446744073709551616, 684034838310589483, 684034838310589483⟩
def pH160 : Prm := ⟨60, 28, 29, 162, 11, 18446744073709551616, 684070022682678315, 684070022682678315⟩
def pI160 : Prm := ⟨52, 25, 24, 162, 11, 18446744073709551616, 684034838310589483, 684070022682678315⟩
theorem L160_fin : (prmOK pL160 160 && ptTest pL160 (runFrom pL160 (fmask pL160) (cmask pL160) (hmask pL160) 1 159 (true, (init pL160), (init pL160))) 160 80 false) = true := by
  decide +kernel
theorem L160_ok : RunOK pL160 160 (runFrom pL160 (fmask pL160) (cmask pL160) (hmask pL160) 1 159 (true, (init pL160), (init pL160))) ∧ ptTest pL160 (runFrom pL160 (fmask pL160) (cmask pL160) (hmask pL160) 1 159 (true, (init pL160), (init pL160))) 160 80 false = true :=
  fin_run (runOK_init (prmOK_of_and L160_fin) true) (by decide) rfl L160_fin ptTest_fst
theorem H160_fin : (prmOK pH160 160 && ptTest pH160 (runFrom pH160 (fmask pH160) (cmask pH160) (hmask pH160) 1 159 (true, (init pH160), (init pH160))) 160 80 true) = true := by
  decide +kernel
theorem H160_ok : RunOK pH160 160 (runFrom pH160 (fmask pH160) (cmask pH160) (hmask pH160) 1 159 (true, (init pH160), (init pH160))) ∧ ptTest pH160 (runFrom pH160 (fmask pH160) (cmask pH160) (hmask pH160) 1 159 (true, (init pH160), (init pH160))) 160 80 true = true :=
  fin_run (runOK_init (prmOK_of_and H160_fin) true) (by decide) rfl H160_fin ptTest_fst
theorem I160_fin : (prmOK pI160 160 && intTest pI160 (runFrom pI160 (fmask pI160) (cmask pI160) (hmask pI160) 1 159 (true, (init pI160), (init pI160))) 160 9 true) = true := by
  decide +kernel
theorem I160_ok : RunOK pI160 160 (runFrom pI160 (fmask pI160) (cmask pI160) (hmask pI160) 1 159 (true, (init pI160), (init pI160))) ∧ intTest pI160 (runFrom pI160 (fmask pI160) (cmask pI160) (hmask pI160) 1 159 (true, (init pI160), (init pI160))) 160 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I160_fin) true) (by decide) rfl I160_fin intTest_fst
theorem link160 : linkOK pL160 pH160 pI160 = true := by decide +kernel
theorem cvx160 : ConvexBetweenHumps 160 :=
  cvx_of L160_ok H160_ok I160_ok link160 (by decide)
theorem cenlink160 : cenLinkOK pI160 160 = true := by decide +kernel
theorem cen160 : CenterUniqueMin 160 ∧ DipHyp 160 ∧ OnePointHyps 160 :=
  cen_of L160_ok H160_ok I160_ok link160 cenlink160

/-! ### `N = 161` -/

def pL161 : Prm := ⟨60, 28, 29, 163, 11, 18446744073709551616, 681066751155568564, 681066751155568564⟩
def pH161 : Prm := ⟨60, 28, 29, 163, 11, 18446744073709551616, 681101935527657396, 681101935527657396⟩
def pI161 : Prm := ⟨52, 25, 24, 163, 11, 18446744073709551616, 681066751155568564, 681101935527657396⟩
theorem L161_fin : (prmOK pL161 161 && ptTest pL161 (runFrom pL161 (fmask pL161) (cmask pL161) (hmask pL161) 1 160 (true, (init pL161), (init pL161))) 161 81 false) = true := by
  decide +kernel
theorem L161_ok : RunOK pL161 161 (runFrom pL161 (fmask pL161) (cmask pL161) (hmask pL161) 1 160 (true, (init pL161), (init pL161))) ∧ ptTest pL161 (runFrom pL161 (fmask pL161) (cmask pL161) (hmask pL161) 1 160 (true, (init pL161), (init pL161))) 161 81 false = true :=
  fin_run (runOK_init (prmOK_of_and L161_fin) true) (by decide) rfl L161_fin ptTest_fst
theorem H161_fin : (prmOK pH161 161 && ptTest pH161 (runFrom pH161 (fmask pH161) (cmask pH161) (hmask pH161) 1 160 (true, (init pH161), (init pH161))) 161 81 true) = true := by
  decide +kernel
theorem H161_ok : RunOK pH161 161 (runFrom pH161 (fmask pH161) (cmask pH161) (hmask pH161) 1 160 (true, (init pH161), (init pH161))) ∧ ptTest pH161 (runFrom pH161 (fmask pH161) (cmask pH161) (hmask pH161) 1 160 (true, (init pH161), (init pH161))) 161 81 true = true :=
  fin_run (runOK_init (prmOK_of_and H161_fin) true) (by decide) rfl H161_fin ptTest_fst
theorem I161_fin : (prmOK pI161 161 && intTest pI161 (runFrom pI161 (fmask pI161) (cmask pI161) (hmask pI161) 1 160 (true, (init pI161), (init pI161))) 161 9 false) = true := by
  decide +kernel
theorem I161_ok : RunOK pI161 161 (runFrom pI161 (fmask pI161) (cmask pI161) (hmask pI161) 1 160 (true, (init pI161), (init pI161))) ∧ intTest pI161 (runFrom pI161 (fmask pI161) (cmask pI161) (hmask pI161) 1 160 (true, (init pI161), (init pI161))) 161 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I161_fin) true) (by decide) rfl I161_fin intTest_fst
theorem link161 : linkOK pL161 pH161 pI161 = true := by decide +kernel
theorem cvx161 : ConvexBetweenHumps 161 :=
  cvx_of L161_ok H161_ok I161_ok link161 (by decide)

/-! ### `N = 162` -/

def pL162 : Prm := ⟨60, 28, 29, 164, 11, 18446744073709551616, 678156466162644713, 678156466162644713⟩
def pH162 : Prm := ⟨60, 28, 29, 164, 11, 18446744073709551616, 678191650534733545, 678191650534733545⟩
def pI162 : Prm := ⟨52, 25, 24, 164, 11, 18446744073709551616, 678156466162644713, 678191650534733545⟩
theorem L162_fin : (prmOK pL162 162 && ptTest pL162 (runFrom pL162 (fmask pL162) (cmask pL162) (hmask pL162) 1 161 (true, (init pL162), (init pL162))) 162 81 false) = true := by
  decide +kernel
theorem L162_ok : RunOK pL162 162 (runFrom pL162 (fmask pL162) (cmask pL162) (hmask pL162) 1 161 (true, (init pL162), (init pL162))) ∧ ptTest pL162 (runFrom pL162 (fmask pL162) (cmask pL162) (hmask pL162) 1 161 (true, (init pL162), (init pL162))) 162 81 false = true :=
  fin_run (runOK_init (prmOK_of_and L162_fin) true) (by decide) rfl L162_fin ptTest_fst
theorem H162_fin : (prmOK pH162 162 && ptTest pH162 (runFrom pH162 (fmask pH162) (cmask pH162) (hmask pH162) 1 161 (true, (init pH162), (init pH162))) 162 81 true) = true := by
  decide +kernel
theorem H162_ok : RunOK pH162 162 (runFrom pH162 (fmask pH162) (cmask pH162) (hmask pH162) 1 161 (true, (init pH162), (init pH162))) ∧ ptTest pH162 (runFrom pH162 (fmask pH162) (cmask pH162) (hmask pH162) 1 161 (true, (init pH162), (init pH162))) 162 81 true = true :=
  fin_run (runOK_init (prmOK_of_and H162_fin) true) (by decide) rfl H162_fin ptTest_fst
theorem I162_fin : (prmOK pI162 162 && intTest pI162 (runFrom pI162 (fmask pI162) (cmask pI162) (hmask pI162) 1 161 (true, (init pI162), (init pI162))) 162 9 true) = true := by
  decide +kernel
theorem I162_ok : RunOK pI162 162 (runFrom pI162 (fmask pI162) (cmask pI162) (hmask pI162) 1 161 (true, (init pI162), (init pI162))) ∧ intTest pI162 (runFrom pI162 (fmask pI162) (cmask pI162) (hmask pI162) 1 161 (true, (init pI162), (init pI162))) 162 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I162_fin) true) (by decide) rfl I162_fin intTest_fst
theorem link162 : linkOK pL162 pH162 pI162 = true := by decide +kernel
theorem cvx162 : ConvexBetweenHumps 162 :=
  cvx_of L162_ok H162_ok I162_ok link162 (by decide)
theorem cenlink162 : cenLinkOK pI162 162 = true := by decide +kernel
theorem cen162 : CenterUniqueMin 162 ∧ DipHyp 162 ∧ OnePointHyps 162 :=
  cen_of L162_ok H162_ok I162_ok link162 cenlink162

/-! ### `N = 163` -/

def pL163 : Prm := ⟨60, 28, 29, 165, 11, 18446744073709551616, 675246436376366839, 675246436376366839⟩
def pH163 : Prm := ⟨60, 28, 29, 165, 11, 18446744073709551616, 675281620748455671, 675281620748455671⟩
def pI163 : Prm := ⟨52, 25, 24, 165, 11, 18446744073709551616, 675246436376366839, 675281620748455671⟩
theorem L163_fin : (prmOK pL163 163 && ptTest pL163 (runFrom pL163 (fmask pL163) (cmask pL163) (hmask pL163) 1 162 (true, (init pL163), (init pL163))) 163 82 false) = true := by
  decide +kernel
theorem L163_ok : RunOK pL163 163 (runFrom pL163 (fmask pL163) (cmask pL163) (hmask pL163) 1 162 (true, (init pL163), (init pL163))) ∧ ptTest pL163 (runFrom pL163 (fmask pL163) (cmask pL163) (hmask pL163) 1 162 (true, (init pL163), (init pL163))) 163 82 false = true :=
  fin_run (runOK_init (prmOK_of_and L163_fin) true) (by decide) rfl L163_fin ptTest_fst
theorem H163_fin : (prmOK pH163 163 && ptTest pH163 (runFrom pH163 (fmask pH163) (cmask pH163) (hmask pH163) 1 162 (true, (init pH163), (init pH163))) 163 82 true) = true := by
  decide +kernel
theorem H163_ok : RunOK pH163 163 (runFrom pH163 (fmask pH163) (cmask pH163) (hmask pH163) 1 162 (true, (init pH163), (init pH163))) ∧ ptTest pH163 (runFrom pH163 (fmask pH163) (cmask pH163) (hmask pH163) 1 162 (true, (init pH163), (init pH163))) 163 82 true = true :=
  fin_run (runOK_init (prmOK_of_and H163_fin) true) (by decide) rfl H163_fin ptTest_fst
theorem I163_fin : (prmOK pI163 163 && intTest pI163 (runFrom pI163 (fmask pI163) (cmask pI163) (hmask pI163) 1 162 (true, (init pI163), (init pI163))) 163 9 false) = true := by
  decide +kernel
theorem I163_ok : RunOK pI163 163 (runFrom pI163 (fmask pI163) (cmask pI163) (hmask pI163) 1 162 (true, (init pI163), (init pI163))) ∧ intTest pI163 (runFrom pI163 (fmask pI163) (cmask pI163) (hmask pI163) 1 162 (true, (init pI163), (init pI163))) 163 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I163_fin) true) (by decide) rfl I163_fin intTest_fst
theorem link163 : linkOK pL163 pH163 pI163 = true := by decide +kernel
theorem cvx163 : ConvexBetweenHumps 163 :=
  cvx_of L163_ok H163_ok I163_ok link163 (by decide)

/-! ### `N = 164` -/

def pL164 : Prm := ⟨60, 28, 29, 166, 11, 18446744073709551616, 672392299433174749, 672392299433174749⟩
def pH164 : Prm := ⟨60, 28, 29, 166, 11, 18446744073709551616, 672427483805263581, 672427483805263581⟩
def pI164 : Prm := ⟨53, 25, 25, 166, 11, 18446744073709551616, 672392299433174749, 672427483805263581⟩
theorem L164_fin : (prmOK pL164 164 && ptTest pL164 (runFrom pL164 (fmask pL164) (cmask pL164) (hmask pL164) 1 163 (true, (init pL164), (init pL164))) 164 82 false) = true := by
  decide +kernel
theorem L164_ok : RunOK pL164 164 (runFrom pL164 (fmask pL164) (cmask pL164) (hmask pL164) 1 163 (true, (init pL164), (init pL164))) ∧ ptTest pL164 (runFrom pL164 (fmask pL164) (cmask pL164) (hmask pL164) 1 163 (true, (init pL164), (init pL164))) 164 82 false = true :=
  fin_run (runOK_init (prmOK_of_and L164_fin) true) (by decide) rfl L164_fin ptTest_fst
theorem H164_fin : (prmOK pH164 164 && ptTest pH164 (runFrom pH164 (fmask pH164) (cmask pH164) (hmask pH164) 1 163 (true, (init pH164), (init pH164))) 164 82 true) = true := by
  decide +kernel
theorem H164_ok : RunOK pH164 164 (runFrom pH164 (fmask pH164) (cmask pH164) (hmask pH164) 1 163 (true, (init pH164), (init pH164))) ∧ ptTest pH164 (runFrom pH164 (fmask pH164) (cmask pH164) (hmask pH164) 1 163 (true, (init pH164), (init pH164))) 164 82 true = true :=
  fin_run (runOK_init (prmOK_of_and H164_fin) true) (by decide) rfl H164_fin ptTest_fst
theorem I164_fin : (prmOK pI164 164 && intTest pI164 (runFrom pI164 (fmask pI164) (cmask pI164) (hmask pI164) 1 163 (true, (init pI164), (init pI164))) 164 9 true) = true := by
  decide +kernel
theorem I164_ok : RunOK pI164 164 (runFrom pI164 (fmask pI164) (cmask pI164) (hmask pI164) 1 163 (true, (init pI164), (init pI164))) ∧ intTest pI164 (runFrom pI164 (fmask pI164) (cmask pI164) (hmask pI164) 1 163 (true, (init pI164), (init pI164))) 164 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I164_fin) true) (by decide) rfl I164_fin intTest_fst
theorem link164 : linkOK pL164 pH164 pI164 = true := by decide +kernel
theorem cvx164 : ConvexBetweenHumps 164 :=
  cvx_of L164_ok H164_ok I164_ok link164 (by decide)
theorem cenlink164 : cenLinkOK pI164 164 = true := by decide +kernel
theorem cen164 : CenterUniqueMin 164 ∧ DipHyp 164 ∧ OnePointHyps 164 :=
  cen_of L164_ok H164_ok I164_ok link164 cenlink164

/-! ### `N = 165` -/

def pL165 : Prm := ⟨60, 28, 29, 167, 11, 18446744073709551616, 669538545589731527, 669538545589731527⟩
def pH165 : Prm := ⟨60, 28, 29, 167, 11, 18446744073709551616, 669573729961820359, 669573729961820359⟩
def pI165 : Prm := ⟨53, 25, 25, 167, 11, 18446744073709551616, 669538545589731527, 669573729961820359⟩
theorem L165_fin : (prmOK pL165 165 && ptTest pL165 (runFrom pL165 (fmask pL165) (cmask pL165) (hmask pL165) 1 164 (true, (init pL165), (init pL165))) 165 83 false) = true := by
  decide +kernel
theorem L165_ok : RunOK pL165 165 (runFrom pL165 (fmask pL165) (cmask pL165) (hmask pL165) 1 164 (true, (init pL165), (init pL165))) ∧ ptTest pL165 (runFrom pL165 (fmask pL165) (cmask pL165) (hmask pL165) 1 164 (true, (init pL165), (init pL165))) 165 83 false = true :=
  fin_run (runOK_init (prmOK_of_and L165_fin) true) (by decide) rfl L165_fin ptTest_fst
theorem H165_fin : (prmOK pH165 165 && ptTest pH165 (runFrom pH165 (fmask pH165) (cmask pH165) (hmask pH165) 1 164 (true, (init pH165), (init pH165))) 165 83 true) = true := by
  decide +kernel
theorem H165_ok : RunOK pH165 165 (runFrom pH165 (fmask pH165) (cmask pH165) (hmask pH165) 1 164 (true, (init pH165), (init pH165))) ∧ ptTest pH165 (runFrom pH165 (fmask pH165) (cmask pH165) (hmask pH165) 1 164 (true, (init pH165), (init pH165))) 165 83 true = true :=
  fin_run (runOK_init (prmOK_of_and H165_fin) true) (by decide) rfl H165_fin ptTest_fst
theorem I165_fin : (prmOK pI165 165 && intTest pI165 (runFrom pI165 (fmask pI165) (cmask pI165) (hmask pI165) 1 164 (true, (init pI165), (init pI165))) 165 9 false) = true := by
  decide +kernel
theorem I165_ok : RunOK pI165 165 (runFrom pI165 (fmask pI165) (cmask pI165) (hmask pI165) 1 164 (true, (init pI165), (init pI165))) ∧ intTest pI165 (runFrom pI165 (fmask pI165) (cmask pI165) (hmask pI165) 1 164 (true, (init pI165), (init pI165))) 165 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I165_fin) true) (by decide) rfl I165_fin intTest_fst
theorem link165 : linkOK pL165 pH165 pI165 = true := by decide +kernel
theorem cvx165 : ConvexBetweenHumps 165 :=
  cvx_of L165_ok H165_ok I165_ok link165 (by decide)

/-! ### `N = 166` -/

def pL166 : Prm := ⟨60, 28, 29, 168, 11, 18446744073709551616, 666738859452854151, 666738859452854151⟩
def pH166 : Prm := ⟨60, 28, 29, 168, 11, 18446744073709551616, 666774043824942983, 666774043824942983⟩
def pI166 : Prm := ⟨53, 25, 25, 168, 11, 18446744073709551616, 666738859452854151, 666774043824942983⟩
theorem L166_fin : (prmOK pL166 166 && ptTest pL166 (runFrom pL166 (fmask pL166) (cmask pL166) (hmask pL166) 1 165 (true, (init pL166), (init pL166))) 166 83 false) = true := by
  decide +kernel
theorem L166_ok : RunOK pL166 166 (runFrom pL166 (fmask pL166) (cmask pL166) (hmask pL166) 1 165 (true, (init pL166), (init pL166))) ∧ ptTest pL166 (runFrom pL166 (fmask pL166) (cmask pL166) (hmask pL166) 1 165 (true, (init pL166), (init pL166))) 166 83 false = true :=
  fin_run (runOK_init (prmOK_of_and L166_fin) true) (by decide) rfl L166_fin ptTest_fst
theorem H166_fin : (prmOK pH166 166 && ptTest pH166 (runFrom pH166 (fmask pH166) (cmask pH166) (hmask pH166) 1 165 (true, (init pH166), (init pH166))) 166 83 true) = true := by
  decide +kernel
theorem H166_ok : RunOK pH166 166 (runFrom pH166 (fmask pH166) (cmask pH166) (hmask pH166) 1 165 (true, (init pH166), (init pH166))) ∧ ptTest pH166 (runFrom pH166 (fmask pH166) (cmask pH166) (hmask pH166) 1 165 (true, (init pH166), (init pH166))) 166 83 true = true :=
  fin_run (runOK_init (prmOK_of_and H166_fin) true) (by decide) rfl H166_fin ptTest_fst
theorem I166_fin : (prmOK pI166 166 && intTest pI166 (runFrom pI166 (fmask pI166) (cmask pI166) (hmask pI166) 1 165 (true, (init pI166), (init pI166))) 166 9 true) = true := by
  decide +kernel
theorem I166_ok : RunOK pI166 166 (runFrom pI166 (fmask pI166) (cmask pI166) (hmask pI166) 1 165 (true, (init pI166), (init pI166))) ∧ intTest pI166 (runFrom pI166 (fmask pI166) (cmask pI166) (hmask pI166) 1 165 (true, (init pI166), (init pI166))) 166 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I166_fin) true) (by decide) rfl I166_fin intTest_fst
theorem link166 : linkOK pL166 pH166 pI166 = true := by decide +kernel
theorem cvx166 : ConvexBetweenHumps 166 :=
  cvx_of L166_ok H166_ok I166_ok link166 (by decide)
theorem cenlink166 : cenLinkOK pI166 166 = true := by decide +kernel
theorem cen166 : CenterUniqueMin 166 ∧ DipHyp 166 ∧ OnePointHyps 166 :=
  cen_of L166_ok H166_ok I166_ok link166 cenlink166

/-! ### `N = 167` -/

def pL167 : Prm := ⟨60, 28, 29, 169, 11, 18446744073709551616, 663939674564760251, 663939674564760251⟩
def pH167 : Prm := ⟨60, 28, 29, 169, 11, 18446744073709551616, 663974858936849083, 663974858936849083⟩
def pI167 : Prm := ⟨53, 25, 25, 169, 11, 18446744073709551616, 663939674564760251, 663974858936849083⟩
theorem L167_fin : (prmOK pL167 167 && ptTest pL167 (runFrom pL167 (fmask pL167) (cmask pL167) (hmask pL167) 1 166 (true, (init pL167), (init pL167))) 167 84 false) = true := by
  decide +kernel
theorem L167_ok : RunOK pL167 167 (runFrom pL167 (fmask pL167) (cmask pL167) (hmask pL167) 1 166 (true, (init pL167), (init pL167))) ∧ ptTest pL167 (runFrom pL167 (fmask pL167) (cmask pL167) (hmask pL167) 1 166 (true, (init pL167), (init pL167))) 167 84 false = true :=
  fin_run (runOK_init (prmOK_of_and L167_fin) true) (by decide) rfl L167_fin ptTest_fst
theorem H167_fin : (prmOK pH167 167 && ptTest pH167 (runFrom pH167 (fmask pH167) (cmask pH167) (hmask pH167) 1 166 (true, (init pH167), (init pH167))) 167 84 true) = true := by
  decide +kernel
theorem H167_ok : RunOK pH167 167 (runFrom pH167 (fmask pH167) (cmask pH167) (hmask pH167) 1 166 (true, (init pH167), (init pH167))) ∧ ptTest pH167 (runFrom pH167 (fmask pH167) (cmask pH167) (hmask pH167) 1 166 (true, (init pH167), (init pH167))) 167 84 true = true :=
  fin_run (runOK_init (prmOK_of_and H167_fin) true) (by decide) rfl H167_fin ptTest_fst
theorem I167_fin : (prmOK pI167 167 && intTest pI167 (runFrom pI167 (fmask pI167) (cmask pI167) (hmask pI167) 1 166 (true, (init pI167), (init pI167))) 167 9 false) = true := by
  decide +kernel
theorem I167_ok : RunOK pI167 167 (runFrom pI167 (fmask pI167) (cmask pI167) (hmask pI167) 1 166 (true, (init pI167), (init pI167))) ∧ intTest pI167 (runFrom pI167 (fmask pI167) (cmask pI167) (hmask pI167) 1 166 (true, (init pI167), (init pI167))) 167 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I167_fin) true) (by decide) rfl I167_fin intTest_fst
theorem link167 : linkOK pL167 pH167 pI167 = true := by decide +kernel
theorem cvx167 : ConvexBetweenHumps 167 :=
  cvx_of L167_ok H167_ok I167_ok link167 (by decide)

/-! ### `N = 168` -/

def pL168 : Prm := ⟨60, 28, 29, 170, 11, 18446744073709551616, 661192811809880632, 661192811809880632⟩
def pH168 : Prm := ⟨60, 28, 29, 170, 11, 18446744073709551616, 661227996181969464, 661227996181969464⟩
def pI168 : Prm := ⟨53, 25, 25, 170, 11, 18446744073709551616, 661192811809880632, 661227996181969464⟩
theorem L168_fin : (prmOK pL168 168 && ptTest pL168 (runFrom pL168 (fmask pL168) (cmask pL168) (hmask pL168) 1 167 (true, (init pL168), (init pL168))) 168 84 false) = true := by
  decide +kernel
theorem L168_ok : RunOK pL168 168 (runFrom pL168 (fmask pL168) (cmask pL168) (hmask pL168) 1 167 (true, (init pL168), (init pL168))) ∧ ptTest pL168 (runFrom pL168 (fmask pL168) (cmask pL168) (hmask pL168) 1 167 (true, (init pL168), (init pL168))) 168 84 false = true :=
  fin_run (runOK_init (prmOK_of_and L168_fin) true) (by decide) rfl L168_fin ptTest_fst
theorem H168_fin : (prmOK pH168 168 && ptTest pH168 (runFrom pH168 (fmask pH168) (cmask pH168) (hmask pH168) 1 167 (true, (init pH168), (init pH168))) 168 84 true) = true := by
  decide +kernel
theorem H168_ok : RunOK pH168 168 (runFrom pH168 (fmask pH168) (cmask pH168) (hmask pH168) 1 167 (true, (init pH168), (init pH168))) ∧ ptTest pH168 (runFrom pH168 (fmask pH168) (cmask pH168) (hmask pH168) 1 167 (true, (init pH168), (init pH168))) 168 84 true = true :=
  fin_run (runOK_init (prmOK_of_and H168_fin) true) (by decide) rfl H168_fin ptTest_fst
theorem I168_fin : (prmOK pI168 168 && intTest pI168 (runFrom pI168 (fmask pI168) (cmask pI168) (hmask pI168) 1 167 (true, (init pI168), (init pI168))) 168 9 true) = true := by
  decide +kernel
theorem I168_ok : RunOK pI168 168 (runFrom pI168 (fmask pI168) (cmask pI168) (hmask pI168) 1 167 (true, (init pI168), (init pI168))) ∧ intTest pI168 (runFrom pI168 (fmask pI168) (cmask pI168) (hmask pI168) 1 167 (true, (init pI168), (init pI168))) 168 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I168_fin) true) (by decide) rfl I168_fin intTest_fst
theorem link168 : linkOK pL168 pH168 pI168 = true := by decide +kernel
theorem cvx168 : ConvexBetweenHumps 168 :=
  cvx_of L168_ok H168_ok I168_ok link168 (by decide)
theorem cenlink168 : cenLinkOK pI168 168 = true := by decide +kernel
theorem cen168 : CenterUniqueMin 168 ∧ DipHyp 168 ∧ OnePointHyps 168 :=
  cen_of L168_ok H168_ok I168_ok link168 cenlink168

/-! ### `N = 169` -/

def pL169 : Prm := ⟨60, 28, 29, 171, 11, 18446744073709551616, 658446559399544489, 658446559399544489⟩
def pH169 : Prm := ⟨60, 28, 29, 171, 11, 18446744073709551616, 658481743771633321, 658481743771633321⟩
def pI169 : Prm := ⟨53, 26, 24, 171, 11, 18446744073709551616, 658446559399544489, 658481743771633321⟩
theorem L169_fin : (prmOK pL169 169 && ptTest pL169 (runFrom pL169 (fmask pL169) (cmask pL169) (hmask pL169) 1 168 (true, (init pL169), (init pL169))) 169 85 false) = true := by
  decide +kernel
theorem L169_ok : RunOK pL169 169 (runFrom pL169 (fmask pL169) (cmask pL169) (hmask pL169) 1 168 (true, (init pL169), (init pL169))) ∧ ptTest pL169 (runFrom pL169 (fmask pL169) (cmask pL169) (hmask pL169) 1 168 (true, (init pL169), (init pL169))) 169 85 false = true :=
  fin_run (runOK_init (prmOK_of_and L169_fin) true) (by decide) rfl L169_fin ptTest_fst
theorem H169_fin : (prmOK pH169 169 && ptTest pH169 (runFrom pH169 (fmask pH169) (cmask pH169) (hmask pH169) 1 168 (true, (init pH169), (init pH169))) 169 85 true) = true := by
  decide +kernel
theorem H169_ok : RunOK pH169 169 (runFrom pH169 (fmask pH169) (cmask pH169) (hmask pH169) 1 168 (true, (init pH169), (init pH169))) ∧ ptTest pH169 (runFrom pH169 (fmask pH169) (cmask pH169) (hmask pH169) 1 168 (true, (init pH169), (init pH169))) 169 85 true = true :=
  fin_run (runOK_init (prmOK_of_and H169_fin) true) (by decide) rfl H169_fin ptTest_fst
theorem I169_fin : (prmOK pI169 169 && intTest pI169 (runFrom pI169 (fmask pI169) (cmask pI169) (hmask pI169) 1 168 (true, (init pI169), (init pI169))) 169 9 false) = true := by
  decide +kernel
theorem I169_ok : RunOK pI169 169 (runFrom pI169 (fmask pI169) (cmask pI169) (hmask pI169) 1 168 (true, (init pI169), (init pI169))) ∧ intTest pI169 (runFrom pI169 (fmask pI169) (cmask pI169) (hmask pI169) 1 168 (true, (init pI169), (init pI169))) 169 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I169_fin) true) (by decide) rfl I169_fin intTest_fst
theorem link169 : linkOK pL169 pH169 pI169 = true := by decide +kernel
theorem cvx169 : ConvexBetweenHumps 169 :=
  cvx_of L169_ok H169_ok I169_ok link169 (by decide)

/-! ### `N = 170` -/

def pL170 : Prm := ⟨60, 28, 29, 172, 11, 18446744073709551616, 655750958795074132, 655750958795074132⟩
def pH170 : Prm := ⟨60, 28, 29, 172, 11, 18446744073709551616, 655786143167162964, 655786143167162964⟩
def pI170 : Prm := ⟨53, 25, 25, 172, 11, 18446744073709551616, 655750958795074132, 655786143167162964⟩
theorem L170_fin : (prmOK pL170 170 && ptTest pL170 (runFrom pL170 (fmask pL170) (cmask pL170) (hmask pL170) 1 169 (true, (init pL170), (init pL170))) 170 85 false) = true := by
  decide +kernel
theorem L170_ok : RunOK pL170 170 (runFrom pL170 (fmask pL170) (cmask pL170) (hmask pL170) 1 169 (true, (init pL170), (init pL170))) ∧ ptTest pL170 (runFrom pL170 (fmask pL170) (cmask pL170) (hmask pL170) 1 169 (true, (init pL170), (init pL170))) 170 85 false = true :=
  fin_run (runOK_init (prmOK_of_and L170_fin) true) (by decide) rfl L170_fin ptTest_fst
theorem H170_fin : (prmOK pH170 170 && ptTest pH170 (runFrom pH170 (fmask pH170) (cmask pH170) (hmask pH170) 1 169 (true, (init pH170), (init pH170))) 170 85 true) = true := by
  decide +kernel
theorem H170_ok : RunOK pH170 170 (runFrom pH170 (fmask pH170) (cmask pH170) (hmask pH170) 1 169 (true, (init pH170), (init pH170))) ∧ ptTest pH170 (runFrom pH170 (fmask pH170) (cmask pH170) (hmask pH170) 1 169 (true, (init pH170), (init pH170))) 170 85 true = true :=
  fin_run (runOK_init (prmOK_of_and H170_fin) true) (by decide) rfl H170_fin ptTest_fst
theorem I170_fin : (prmOK pI170 170 && intTest pI170 (runFrom pI170 (fmask pI170) (cmask pI170) (hmask pI170) 1 169 (true, (init pI170), (init pI170))) 170 9 true) = true := by
  decide +kernel
theorem I170_ok : RunOK pI170 170 (runFrom pI170 (fmask pI170) (cmask pI170) (hmask pI170) 1 169 (true, (init pI170), (init pI170))) ∧ intTest pI170 (runFrom pI170 (fmask pI170) (cmask pI170) (hmask pI170) 1 169 (true, (init pI170), (init pI170))) 170 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I170_fin) true) (by decide) rfl I170_fin intTest_fst
theorem link170 : linkOK pL170 pH170 pI170 = true := by decide +kernel
theorem cvx170 : ConvexBetweenHumps 170 :=
  cvx_of L170_ok H170_ok I170_ok link170 (by decide)
theorem cenlink170 : cenLinkOK pI170 170 = true := by decide +kernel
theorem cen170 : CenterUniqueMin 170 ∧ DipHyp 170 ∧ OnePointHyps 170 :=
  cen_of L170_ok H170_ok I170_ok link170 cenlink170

/-! ### `N = 171` -/

def pL171 : Prm := ⟨60, 28, 29, 173, 11, 18446744073709551616, 653056069216277366, 653056069216277366⟩
def pH171 : Prm := ⟨60, 28, 29, 173, 11, 18446744073709551616, 653091253588366198, 653091253588366198⟩
def pI171 : Prm := ⟨53, 26, 24, 173, 11, 18446744073709551616, 653056069216277366, 653091253588366198⟩
theorem L171_fin : (prmOK pL171 171 && ptTest pL171 (runFrom pL171 (fmask pL171) (cmask pL171) (hmask pL171) 1 170 (true, (init pL171), (init pL171))) 171 86 false) = true := by
  decide +kernel
theorem L171_ok : RunOK pL171 171 (runFrom pL171 (fmask pL171) (cmask pL171) (hmask pL171) 1 170 (true, (init pL171), (init pL171))) ∧ ptTest pL171 (runFrom pL171 (fmask pL171) (cmask pL171) (hmask pL171) 1 170 (true, (init pL171), (init pL171))) 171 86 false = true :=
  fin_run (runOK_init (prmOK_of_and L171_fin) true) (by decide) rfl L171_fin ptTest_fst
theorem H171_fin : (prmOK pH171 171 && ptTest pH171 (runFrom pH171 (fmask pH171) (cmask pH171) (hmask pH171) 1 170 (true, (init pH171), (init pH171))) 171 86 true) = true := by
  decide +kernel
theorem H171_ok : RunOK pH171 171 (runFrom pH171 (fmask pH171) (cmask pH171) (hmask pH171) 1 170 (true, (init pH171), (init pH171))) ∧ ptTest pH171 (runFrom pH171 (fmask pH171) (cmask pH171) (hmask pH171) 1 170 (true, (init pH171), (init pH171))) 171 86 true = true :=
  fin_run (runOK_init (prmOK_of_and H171_fin) true) (by decide) rfl H171_fin ptTest_fst
theorem I171_fin : (prmOK pI171 171 && intTest pI171 (runFrom pI171 (fmask pI171) (cmask pI171) (hmask pI171) 1 170 (true, (init pI171), (init pI171))) 171 9 false) = true := by
  decide +kernel
theorem I171_ok : RunOK pI171 171 (runFrom pI171 (fmask pI171) (cmask pI171) (hmask pI171) 1 170 (true, (init pI171), (init pI171))) ∧ intTest pI171 (runFrom pI171 (fmask pI171) (cmask pI171) (hmask pI171) 1 170 (true, (init pI171), (init pI171))) 171 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I171_fin) true) (by decide) rfl I171_fin intTest_fst
theorem link171 : linkOK pL171 pH171 pI171 = true := by decide +kernel
theorem cvx171 : ConvexBetweenHumps 171 :=
  cvx_of L171_ok H171_ok I171_ok link171 (by decide)

/-! ### `N = 172` -/

def pL172 : Prm := ⟨60, 28, 29, 174, 11, 18446744073709551616, 650410232324027131, 650410232324027131⟩
def pH172 : Prm := ⟨60, 28, 29, 174, 11, 18446744073709551616, 650445416696115963, 650445416696115963⟩
def pI172 : Prm := ⟨53, 26, 24, 174, 11, 18446744073709551616, 650410232324027131, 650445416696115963⟩
theorem L172_fin : (prmOK pL172 172 && ptTest pL172 (runFrom pL172 (fmask pL172) (cmask pL172) (hmask pL172) 1 171 (true, (init pL172), (init pL172))) 172 86 false) = true := by
  decide +kernel
theorem L172_ok : RunOK pL172 172 (runFrom pL172 (fmask pL172) (cmask pL172) (hmask pL172) 1 171 (true, (init pL172), (init pL172))) ∧ ptTest pL172 (runFrom pL172 (fmask pL172) (cmask pL172) (hmask pL172) 1 171 (true, (init pL172), (init pL172))) 172 86 false = true :=
  fin_run (runOK_init (prmOK_of_and L172_fin) true) (by decide) rfl L172_fin ptTest_fst
theorem H172_fin : (prmOK pH172 172 && ptTest pH172 (runFrom pH172 (fmask pH172) (cmask pH172) (hmask pH172) 1 171 (true, (init pH172), (init pH172))) 172 86 true) = true := by
  decide +kernel
theorem H172_ok : RunOK pH172 172 (runFrom pH172 (fmask pH172) (cmask pH172) (hmask pH172) 1 171 (true, (init pH172), (init pH172))) ∧ ptTest pH172 (runFrom pH172 (fmask pH172) (cmask pH172) (hmask pH172) 1 171 (true, (init pH172), (init pH172))) 172 86 true = true :=
  fin_run (runOK_init (prmOK_of_and H172_fin) true) (by decide) rfl H172_fin ptTest_fst
theorem I172_fin : (prmOK pI172 172 && intTest pI172 (runFrom pI172 (fmask pI172) (cmask pI172) (hmask pI172) 1 171 (true, (init pI172), (init pI172))) 172 9 true) = true := by
  decide +kernel
theorem I172_ok : RunOK pI172 172 (runFrom pI172 (fmask pI172) (cmask pI172) (hmask pI172) 1 171 (true, (init pI172), (init pI172))) ∧ intTest pI172 (runFrom pI172 (fmask pI172) (cmask pI172) (hmask pI172) 1 171 (true, (init pI172), (init pI172))) 172 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I172_fin) true) (by decide) rfl I172_fin intTest_fst
theorem link172 : linkOK pL172 pH172 pI172 = true := by decide +kernel
theorem cvx172 : ConvexBetweenHumps 172 :=
  cvx_of L172_ok H172_ok I172_ok link172 (by decide)
theorem cenlink172 : cenLinkOK pI172 172 = true := by decide +kernel
theorem cen172 : CenterUniqueMin 172 ∧ DipHyp 172 ∧ OnePointHyps 172 :=
  cen_of L172_ok H172_ok I172_ok link172 cenlink172

/-! ### `N = 173` -/

def pL173 : Prm := ⟨60, 28, 29, 175, 11, 18446744073709551616, 647765199314541678, 647765199314541678⟩
def pH173 : Prm := ⟨60, 28, 29, 175, 11, 18446744073709551616, 647800383686630510, 647800383686630510⟩
def pI173 : Prm := ⟨53, 26, 24, 175, 11, 18446744073709551616, 647765199314541678, 647800383686630510⟩
theorem L173_fin : (prmOK pL173 173 && ptTest pL173 (runFrom pL173 (fmask pL173) (cmask pL173) (hmask pL173) 1 172 (true, (init pL173), (init pL173))) 173 87 false) = true := by
  decide +kernel
theorem L173_ok : RunOK pL173 173 (runFrom pL173 (fmask pL173) (cmask pL173) (hmask pL173) 1 172 (true, (init pL173), (init pL173))) ∧ ptTest pL173 (runFrom pL173 (fmask pL173) (cmask pL173) (hmask pL173) 1 172 (true, (init pL173), (init pL173))) 173 87 false = true :=
  fin_run (runOK_init (prmOK_of_and L173_fin) true) (by decide) rfl L173_fin ptTest_fst
theorem H173_fin : (prmOK pH173 173 && ptTest pH173 (runFrom pH173 (fmask pH173) (cmask pH173) (hmask pH173) 1 172 (true, (init pH173), (init pH173))) 173 87 true) = true := by
  decide +kernel
theorem H173_ok : RunOK pH173 173 (runFrom pH173 (fmask pH173) (cmask pH173) (hmask pH173) 1 172 (true, (init pH173), (init pH173))) ∧ ptTest pH173 (runFrom pH173 (fmask pH173) (cmask pH173) (hmask pH173) 1 172 (true, (init pH173), (init pH173))) 173 87 true = true :=
  fin_run (runOK_init (prmOK_of_and H173_fin) true) (by decide) rfl H173_fin ptTest_fst
theorem I173_fin : (prmOK pI173 173 && intTest pI173 (runFrom pI173 (fmask pI173) (cmask pI173) (hmask pI173) 1 172 (true, (init pI173), (init pI173))) 173 9 false) = true := by
  decide +kernel
theorem I173_ok : RunOK pI173 173 (runFrom pI173 (fmask pI173) (cmask pI173) (hmask pI173) 1 172 (true, (init pI173), (init pI173))) ∧ intTest pI173 (runFrom pI173 (fmask pI173) (cmask pI173) (hmask pI173) 1 172 (true, (init pI173), (init pI173))) 173 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I173_fin) true) (by decide) rfl I173_fin intTest_fst
theorem link173 : linkOK pL173 pH173 pI173 = true := by decide +kernel
theorem cvx173 : ConvexBetweenHumps 173 :=
  cvx_of L173_ok H173_ok I173_ok link173 (by decide)

/-! ### `N = 174` -/

def pL174 : Prm := ⟨60, 28, 29, 176, 11, 18446744073709551616, 645167687300667114, 645167687300667114⟩
def pH174 : Prm := ⟨60, 28, 29, 176, 11, 18446744073709551616, 645202871672755946, 645202871672755946⟩
def pI174 : Prm := ⟨53, 26, 24, 176, 11, 18446744073709551616, 645167687300667114, 645202871672755946⟩
theorem L174_fin : (prmOK pL174 174 && ptTest pL174 (runFrom pL174 (fmask pL174) (cmask pL174) (hmask pL174) 1 173 (true, (init pL174), (init pL174))) 174 87 false) = true := by
  decide +kernel
theorem L174_ok : RunOK pL174 174 (runFrom pL174 (fmask pL174) (cmask pL174) (hmask pL174) 1 173 (true, (init pL174), (init pL174))) ∧ ptTest pL174 (runFrom pL174 (fmask pL174) (cmask pL174) (hmask pL174) 1 173 (true, (init pL174), (init pL174))) 174 87 false = true :=
  fin_run (runOK_init (prmOK_of_and L174_fin) true) (by decide) rfl L174_fin ptTest_fst
theorem H174_fin : (prmOK pH174 174 && ptTest pH174 (runFrom pH174 (fmask pH174) (cmask pH174) (hmask pH174) 1 173 (true, (init pH174), (init pH174))) 174 87 true) = true := by
  decide +kernel
theorem H174_ok : RunOK pH174 174 (runFrom pH174 (fmask pH174) (cmask pH174) (hmask pH174) 1 173 (true, (init pH174), (init pH174))) ∧ ptTest pH174 (runFrom pH174 (fmask pH174) (cmask pH174) (hmask pH174) 1 173 (true, (init pH174), (init pH174))) 174 87 true = true :=
  fin_run (runOK_init (prmOK_of_and H174_fin) true) (by decide) rfl H174_fin ptTest_fst
theorem I174_fin : (prmOK pI174 174 && intTest pI174 (runFrom pI174 (fmask pI174) (cmask pI174) (hmask pI174) 1 173 (true, (init pI174), (init pI174))) 174 9 true) = true := by
  decide +kernel
theorem I174_ok : RunOK pI174 174 (runFrom pI174 (fmask pI174) (cmask pI174) (hmask pI174) 1 173 (true, (init pI174), (init pI174))) ∧ intTest pI174 (runFrom pI174 (fmask pI174) (cmask pI174) (hmask pI174) 1 173 (true, (init pI174), (init pI174))) 174 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I174_fin) true) (by decide) rfl I174_fin intTest_fst
theorem link174 : linkOK pL174 pH174 pI174 = true := by decide +kernel
theorem cvx174 : ConvexBetweenHumps 174 :=
  cvx_of L174_ok H174_ok I174_ok link174 (by decide)
theorem cenlink174 : cenLinkOK pI174 174 = true := by decide +kernel
theorem cen174 : CenterUniqueMin 174 ∧ DipHyp 174 ∧ OnePointHyps 174 :=
  cen_of L174_ok H174_ok I174_ok link174 cenlink174

/-! ### `N = 175` -/

def pL175 : Prm := ⟨60, 28, 29, 177, 11, 18446744073709551616, 642571064749352645, 642571064749352645⟩
def pH175 : Prm := ⟨60, 28, 29, 177, 11, 18446744073709551616, 642606249121441477, 642606249121441477⟩
def pI175 : Prm := ⟨53, 26, 24, 177, 11, 18446744073709551616, 642571064749352645, 642606249121441477⟩
theorem L175_fin : (prmOK pL175 175 && ptTest pL175 (runFrom pL175 (fmask pL175) (cmask pL175) (hmask pL175) 1 174 (true, (init pL175), (init pL175))) 175 88 false) = true := by
  decide +kernel
theorem L175_ok : RunOK pL175 175 (runFrom pL175 (fmask pL175) (cmask pL175) (hmask pL175) 1 174 (true, (init pL175), (init pL175))) ∧ ptTest pL175 (runFrom pL175 (fmask pL175) (cmask pL175) (hmask pL175) 1 174 (true, (init pL175), (init pL175))) 175 88 false = true :=
  fin_run (runOK_init (prmOK_of_and L175_fin) true) (by decide) rfl L175_fin ptTest_fst
theorem H175_fin : (prmOK pH175 175 && ptTest pH175 (runFrom pH175 (fmask pH175) (cmask pH175) (hmask pH175) 1 174 (true, (init pH175), (init pH175))) 175 88 true) = true := by
  decide +kernel
theorem H175_ok : RunOK pH175 175 (runFrom pH175 (fmask pH175) (cmask pH175) (hmask pH175) 1 174 (true, (init pH175), (init pH175))) ∧ ptTest pH175 (runFrom pH175 (fmask pH175) (cmask pH175) (hmask pH175) 1 174 (true, (init pH175), (init pH175))) 175 88 true = true :=
  fin_run (runOK_init (prmOK_of_and H175_fin) true) (by decide) rfl H175_fin ptTest_fst
theorem I175_fin : (prmOK pI175 175 && intTest pI175 (runFrom pI175 (fmask pI175) (cmask pI175) (hmask pI175) 1 174 (true, (init pI175), (init pI175))) 175 9 false) = true := by
  decide +kernel
theorem I175_ok : RunOK pI175 175 (runFrom pI175 (fmask pI175) (cmask pI175) (hmask pI175) 1 174 (true, (init pI175), (init pI175))) ∧ intTest pI175 (runFrom pI175 (fmask pI175) (cmask pI175) (hmask pI175) 1 174 (true, (init pI175), (init pI175))) 175 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I175_fin) true) (by decide) rfl I175_fin intTest_fst
theorem link175 : linkOK pL175 pH175 pI175 = true := by decide +kernel
theorem cvx175 : ConvexBetweenHumps 175 :=
  cvx_of L175_ok H175_ok I175_ok link175 (by decide)

/-! ### `N = 176` -/

def pL176 : Prm := ⟨60, 28, 29, 178, 11, 18446744073709551616, 640020495390687233, 640020495390687233⟩
def pH176 : Prm := ⟨60, 28, 29, 178, 11, 18446744073709551616, 640055679762776065, 640055679762776065⟩
def pI176 : Prm := ⟨53, 26, 24, 178, 11, 18446744073709551616, 640020495390687233, 640055679762776065⟩
theorem L176_fin : (prmOK pL176 176 && ptTest pL176 (runFrom pL176 (fmask pL176) (cmask pL176) (hmask pL176) 1 175 (true, (init pL176), (init pL176))) 176 88 false) = true := by
  decide +kernel
theorem L176_ok : RunOK pL176 176 (runFrom pL176 (fmask pL176) (cmask pL176) (hmask pL176) 1 175 (true, (init pL176), (init pL176))) ∧ ptTest pL176 (runFrom pL176 (fmask pL176) (cmask pL176) (hmask pL176) 1 175 (true, (init pL176), (init pL176))) 176 88 false = true :=
  fin_run (runOK_init (prmOK_of_and L176_fin) true) (by decide) rfl L176_fin ptTest_fst
theorem H176_fin : (prmOK pH176 176 && ptTest pH176 (runFrom pH176 (fmask pH176) (cmask pH176) (hmask pH176) 1 175 (true, (init pH176), (init pH176))) 176 88 true) = true := by
  decide +kernel
theorem H176_ok : RunOK pH176 176 (runFrom pH176 (fmask pH176) (cmask pH176) (hmask pH176) 1 175 (true, (init pH176), (init pH176))) ∧ ptTest pH176 (runFrom pH176 (fmask pH176) (cmask pH176) (hmask pH176) 1 175 (true, (init pH176), (init pH176))) 176 88 true = true :=
  fin_run (runOK_init (prmOK_of_and H176_fin) true) (by decide) rfl H176_fin ptTest_fst
theorem I176_fin : (prmOK pI176 176 && intTest pI176 (runFrom pI176 (fmask pI176) (cmask pI176) (hmask pI176) 1 175 (true, (init pI176), (init pI176))) 176 9 true) = true := by
  decide +kernel
theorem I176_ok : RunOK pI176 176 (runFrom pI176 (fmask pI176) (cmask pI176) (hmask pI176) 1 175 (true, (init pI176), (init pI176))) ∧ intTest pI176 (runFrom pI176 (fmask pI176) (cmask pI176) (hmask pI176) 1 175 (true, (init pI176), (init pI176))) 176 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I176_fin) true) (by decide) rfl I176_fin intTest_fst
theorem link176 : linkOK pL176 pH176 pI176 = true := by decide +kernel
theorem cvx176 : ConvexBetweenHumps 176 :=
  cvx_of L176_ok H176_ok I176_ok link176 (by decide)
theorem cenlink176 : cenLinkOK pI176 176 = true := by decide +kernel
theorem cen176 : CenterUniqueMin 176 ∧ DipHyp 176 ∧ OnePointHyps 176 :=
  cen_of L176_ok H176_ok I176_ok link176 cenlink176

/-! ### `N = 177` -/

def pL177 : Prm := ⟨60, 28, 29, 179, 11, 18446744073709551616, 637470894303241563, 637470894303241563⟩
def pH177 : Prm := ⟨60, 28, 29, 179, 11, 18446744073709551616, 637506078675330395, 637506078675330395⟩
def pI177 : Prm := ⟨53, 26, 24, 179, 11, 18446744073709551616, 637470894303241563, 637506078675330395⟩
theorem L177_fin : (prmOK pL177 177 && ptTest pL177 (runFrom pL177 (fmask pL177) (cmask pL177) (hmask pL177) 1 176 (true, (init pL177), (init pL177))) 177 89 false) = true := by
  decide +kernel
theorem L177_ok : RunOK pL177 177 (runFrom pL177 (fmask pL177) (cmask pL177) (hmask pL177) 1 176 (true, (init pL177), (init pL177))) ∧ ptTest pL177 (runFrom pL177 (fmask pL177) (cmask pL177) (hmask pL177) 1 176 (true, (init pL177), (init pL177))) 177 89 false = true :=
  fin_run (runOK_init (prmOK_of_and L177_fin) true) (by decide) rfl L177_fin ptTest_fst
theorem H177_fin : (prmOK pH177 177 && ptTest pH177 (runFrom pH177 (fmask pH177) (cmask pH177) (hmask pH177) 1 176 (true, (init pH177), (init pH177))) 177 89 true) = true := by
  decide +kernel
theorem H177_ok : RunOK pH177 177 (runFrom pH177 (fmask pH177) (cmask pH177) (hmask pH177) 1 176 (true, (init pH177), (init pH177))) ∧ ptTest pH177 (runFrom pH177 (fmask pH177) (cmask pH177) (hmask pH177) 1 176 (true, (init pH177), (init pH177))) 177 89 true = true :=
  fin_run (runOK_init (prmOK_of_and H177_fin) true) (by decide) rfl H177_fin ptTest_fst
theorem I177_fin : (prmOK pI177 177 && intTest pI177 (runFrom pI177 (fmask pI177) (cmask pI177) (hmask pI177) 1 176 (true, (init pI177), (init pI177))) 177 9 false) = true := by
  decide +kernel
theorem I177_ok : RunOK pI177 177 (runFrom pI177 (fmask pI177) (cmask pI177) (hmask pI177) 1 176 (true, (init pI177), (init pI177))) ∧ intTest pI177 (runFrom pI177 (fmask pI177) (cmask pI177) (hmask pI177) 1 176 (true, (init pI177), (init pI177))) 177 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I177_fin) true) (by decide) rfl I177_fin intTest_fst
theorem link177 : linkOK pL177 pH177 pI177 = true := by decide +kernel
theorem cvx177 : ConvexBetweenHumps 177 :=
  cvx_of L177_ok H177_ok I177_ok link177 (by decide)

/-! ### `N = 178` -/

def pL178 : Prm := ⟨60, 28, 29, 180, 11, 18446744073709551616, 634965939174684752, 634965939174684752⟩
def pH178 : Prm := ⟨60, 28, 29, 180, 11, 18446744073709551616, 635001123546773584, 635001123546773584⟩
def pI178 : Prm := ⟨54, 26, 25, 180, 11, 18446744073709551616, 634965939174684752, 635001123546773584⟩
theorem L178_fin : (prmOK pL178 178 && ptTest pL178 (runFrom pL178 (fmask pL178) (cmask pL178) (hmask pL178) 1 177 (true, (init pL178), (init pL178))) 178 89 false) = true := by
  decide +kernel
theorem L178_ok : RunOK pL178 178 (runFrom pL178 (fmask pL178) (cmask pL178) (hmask pL178) 1 177 (true, (init pL178), (init pL178))) ∧ ptTest pL178 (runFrom pL178 (fmask pL178) (cmask pL178) (hmask pL178) 1 177 (true, (init pL178), (init pL178))) 178 89 false = true :=
  fin_run (runOK_init (prmOK_of_and L178_fin) true) (by decide) rfl L178_fin ptTest_fst
theorem H178_fin : (prmOK pH178 178 && ptTest pH178 (runFrom pH178 (fmask pH178) (cmask pH178) (hmask pH178) 1 177 (true, (init pH178), (init pH178))) 178 89 true) = true := by
  decide +kernel
theorem H178_ok : RunOK pH178 178 (runFrom pH178 (fmask pH178) (cmask pH178) (hmask pH178) 1 177 (true, (init pH178), (init pH178))) ∧ ptTest pH178 (runFrom pH178 (fmask pH178) (cmask pH178) (hmask pH178) 1 177 (true, (init pH178), (init pH178))) 178 89 true = true :=
  fin_run (runOK_init (prmOK_of_and H178_fin) true) (by decide) rfl H178_fin ptTest_fst
theorem I178_fin : (prmOK pI178 178 && intTest pI178 (runFrom pI178 (fmask pI178) (cmask pI178) (hmask pI178) 1 177 (true, (init pI178), (init pI178))) 178 9 true) = true := by
  decide +kernel
theorem I178_ok : RunOK pI178 178 (runFrom pI178 (fmask pI178) (cmask pI178) (hmask pI178) 1 177 (true, (init pI178), (init pI178))) ∧ intTest pI178 (runFrom pI178 (fmask pI178) (cmask pI178) (hmask pI178) 1 177 (true, (init pI178), (init pI178))) 178 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I178_fin) true) (by decide) rfl I178_fin intTest_fst
theorem link178 : linkOK pL178 pH178 pI178 = true := by decide +kernel
theorem cvx178 : ConvexBetweenHumps 178 :=
  cvx_of L178_ok H178_ok I178_ok link178 (by decide)
theorem cenlink178 : cenLinkOK pI178 178 = true := by decide +kernel
theorem cen178 : CenterUniqueMin 178 ∧ DipHyp 178 ∧ OnePointHyps 178 :=
  cen_of L178_ok H178_ok I178_ok link178 cenlink178

/-! ### `N = 179` -/

def pL179 : Prm := ⟨60, 28, 29, 181, 11, 18446744073709551616, 632462024824027707, 632462024824027707⟩
def pH179 : Prm := ⟨60, 28, 29, 181, 11, 18446744073709551616, 632497209196116539, 632497209196116539⟩
def pI179 : Prm := ⟨54, 26, 25, 181, 11, 18446744073709551616, 632462024824027707, 632497209196116539⟩
theorem L179_fin : (prmOK pL179 179 && ptTest pL179 (runFrom pL179 (fmask pL179) (cmask pL179) (hmask pL179) 1 178 (true, (init pL179), (init pL179))) 179 90 false) = true := by
  decide +kernel
theorem L179_ok : RunOK pL179 179 (runFrom pL179 (fmask pL179) (cmask pL179) (hmask pL179) 1 178 (true, (init pL179), (init pL179))) ∧ ptTest pL179 (runFrom pL179 (fmask pL179) (cmask pL179) (hmask pL179) 1 178 (true, (init pL179), (init pL179))) 179 90 false = true :=
  fin_run (runOK_init (prmOK_of_and L179_fin) true) (by decide) rfl L179_fin ptTest_fst
theorem H179_fin : (prmOK pH179 179 && ptTest pH179 (runFrom pH179 (fmask pH179) (cmask pH179) (hmask pH179) 1 178 (true, (init pH179), (init pH179))) 179 90 true) = true := by
  decide +kernel
theorem H179_ok : RunOK pH179 179 (runFrom pH179 (fmask pH179) (cmask pH179) (hmask pH179) 1 178 (true, (init pH179), (init pH179))) ∧ ptTest pH179 (runFrom pH179 (fmask pH179) (cmask pH179) (hmask pH179) 1 178 (true, (init pH179), (init pH179))) 179 90 true = true :=
  fin_run (runOK_init (prmOK_of_and H179_fin) true) (by decide) rfl H179_fin ptTest_fst
theorem I179_fin : (prmOK pI179 179 && intTest pI179 (runFrom pI179 (fmask pI179) (cmask pI179) (hmask pI179) 1 178 (true, (init pI179), (init pI179))) 179 9 false) = true := by
  decide +kernel
theorem I179_ok : RunOK pI179 179 (runFrom pI179 (fmask pI179) (cmask pI179) (hmask pI179) 1 178 (true, (init pI179), (init pI179))) ∧ intTest pI179 (runFrom pI179 (fmask pI179) (cmask pI179) (hmask pI179) 1 178 (true, (init pI179), (init pI179))) 179 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I179_fin) true) (by decide) rfl I179_fin intTest_fst
theorem link179 : linkOK pL179 pH179 pI179 = true := by decide +kernel
theorem cvx179 : ConvexBetweenHumps 179 :=
  cvx_of L179_ok H179_ok I179_ok link179 (by decide)

/-! ### `N = 180` -/

def pL180 : Prm := ⟨60, 28, 29, 182, 11, 18446744073709551616, 630001406654499303, 630001406654499303⟩
def pH180 : Prm := ⟨60, 28, 29, 182, 11, 18446744073709551616, 630036591026588135, 630036591026588135⟩
def pI180 : Prm := ⟨54, 26, 25, 182, 11, 18446744073709551616, 630001406654499303, 630036591026588135⟩
theorem L180_fin : (prmOK pL180 180 && ptTest pL180 (runFrom pL180 (fmask pL180) (cmask pL180) (hmask pL180) 1 179 (true, (init pL180), (init pL180))) 180 90 false) = true := by
  decide +kernel
theorem L180_ok : RunOK pL180 180 (runFrom pL180 (fmask pL180) (cmask pL180) (hmask pL180) 1 179 (true, (init pL180), (init pL180))) ∧ ptTest pL180 (runFrom pL180 (fmask pL180) (cmask pL180) (hmask pL180) 1 179 (true, (init pL180), (init pL180))) 180 90 false = true :=
  fin_run (runOK_init (prmOK_of_and L180_fin) true) (by decide) rfl L180_fin ptTest_fst
theorem H180_fin : (prmOK pH180 180 && ptTest pH180 (runFrom pH180 (fmask pH180) (cmask pH180) (hmask pH180) 1 179 (true, (init pH180), (init pH180))) 180 90 true) = true := by
  decide +kernel
theorem H180_ok : RunOK pH180 180 (runFrom pH180 (fmask pH180) (cmask pH180) (hmask pH180) 1 179 (true, (init pH180), (init pH180))) ∧ ptTest pH180 (runFrom pH180 (fmask pH180) (cmask pH180) (hmask pH180) 1 179 (true, (init pH180), (init pH180))) 180 90 true = true :=
  fin_run (runOK_init (prmOK_of_and H180_fin) true) (by decide) rfl H180_fin ptTest_fst
theorem I180_fin : (prmOK pI180 180 && intTest pI180 (runFrom pI180 (fmask pI180) (cmask pI180) (hmask pI180) 1 179 (true, (init pI180), (init pI180))) 180 9 true) = true := by
  decide +kernel
theorem I180_ok : RunOK pI180 180 (runFrom pI180 (fmask pI180) (cmask pI180) (hmask pI180) 1 179 (true, (init pI180), (init pI180))) ∧ intTest pI180 (runFrom pI180 (fmask pI180) (cmask pI180) (hmask pI180) 1 179 (true, (init pI180), (init pI180))) 180 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I180_fin) true) (by decide) rfl I180_fin intTest_fst
theorem link180 : linkOK pL180 pH180 pI180 = true := by decide +kernel
theorem cvx180 : ConvexBetweenHumps 180 :=
  cvx_of L180_ok H180_ok I180_ok link180 (by decide)
theorem cenlink180 : cenLinkOK pI180 180 = true := by decide +kernel
theorem cen180 : CenterUniqueMin 180 ∧ DipHyp 180 ∧ OnePointHyps 180 :=
  cen_of L180_ok H180_ok I180_ok link180 cenlink180

/-! ### `N = 181` -/

def pL181 : Prm := ⟨61, 29, 29, 183, 11, 18446744073709551616, 627541895902379267, 627541895902379267⟩
def pH181 : Prm := ⟨60, 28, 29, 183, 11, 18446744073709551616, 627577080274468099, 627577080274468099⟩
def pI181 : Prm := ⟨54, 26, 25, 183, 11, 18446744073709551616, 627541895902379267, 627577080274468099⟩
theorem L181_fin : (prmOK pL181 181 && ptTest pL181 (runFrom pL181 (fmask pL181) (cmask pL181) (hmask pL181) 1 180 (true, (init pL181), (init pL181))) 181 91 false) = true := by
  decide +kernel
theorem L181_ok : RunOK pL181 181 (runFrom pL181 (fmask pL181) (cmask pL181) (hmask pL181) 1 180 (true, (init pL181), (init pL181))) ∧ ptTest pL181 (runFrom pL181 (fmask pL181) (cmask pL181) (hmask pL181) 1 180 (true, (init pL181), (init pL181))) 181 91 false = true :=
  fin_run (runOK_init (prmOK_of_and L181_fin) true) (by decide) rfl L181_fin ptTest_fst
theorem H181_fin : (prmOK pH181 181 && ptTest pH181 (runFrom pH181 (fmask pH181) (cmask pH181) (hmask pH181) 1 180 (true, (init pH181), (init pH181))) 181 91 true) = true := by
  decide +kernel
theorem H181_ok : RunOK pH181 181 (runFrom pH181 (fmask pH181) (cmask pH181) (hmask pH181) 1 180 (true, (init pH181), (init pH181))) ∧ ptTest pH181 (runFrom pH181 (fmask pH181) (cmask pH181) (hmask pH181) 1 180 (true, (init pH181), (init pH181))) 181 91 true = true :=
  fin_run (runOK_init (prmOK_of_and H181_fin) true) (by decide) rfl H181_fin ptTest_fst
theorem I181_fin : (prmOK pI181 181 && intTest pI181 (runFrom pI181 (fmask pI181) (cmask pI181) (hmask pI181) 1 180 (true, (init pI181), (init pI181))) 181 9 false) = true := by
  decide +kernel
theorem I181_ok : RunOK pI181 181 (runFrom pI181 (fmask pI181) (cmask pI181) (hmask pI181) 1 180 (true, (init pI181), (init pI181))) ∧ intTest pI181 (runFrom pI181 (fmask pI181) (cmask pI181) (hmask pI181) 1 180 (true, (init pI181), (init pI181))) 181 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I181_fin) true) (by decide) rfl I181_fin intTest_fst
theorem link181 : linkOK pL181 pH181 pI181 = true := by decide +kernel
theorem cvx181 : ConvexBetweenHumps 181 :=
  cvx_of L181_ok H181_ok I181_ok link181 (by decide)

/-! ### `N = 182` -/

def pL182 : Prm := ⟨61, 29, 29, 184, 11, 18446744073709551616, 625124386087368227, 625124386087368227⟩
def pH182 : Prm := ⟨61, 29, 29, 184, 11, 18446744073709551616, 625159570459457059, 625159570459457059⟩
def pI182 : Prm := ⟨54, 26, 25, 184, 11, 18446744073709551616, 625124386087368227, 625159570459457059⟩
theorem L182_fin : (prmOK pL182 182 && ptTest pL182 (runFrom pL182 (fmask pL182) (cmask pL182) (hmask pL182) 1 181 (true, (init pL182), (init pL182))) 182 91 false) = true := by
  decide +kernel
theorem L182_ok : RunOK pL182 182 (runFrom pL182 (fmask pL182) (cmask pL182) (hmask pL182) 1 181 (true, (init pL182), (init pL182))) ∧ ptTest pL182 (runFrom pL182 (fmask pL182) (cmask pL182) (hmask pL182) 1 181 (true, (init pL182), (init pL182))) 182 91 false = true :=
  fin_run (runOK_init (prmOK_of_and L182_fin) true) (by decide) rfl L182_fin ptTest_fst
theorem H182_fin : (prmOK pH182 182 && ptTest pH182 (runFrom pH182 (fmask pH182) (cmask pH182) (hmask pH182) 1 181 (true, (init pH182), (init pH182))) 182 91 true) = true := by
  decide +kernel
theorem H182_ok : RunOK pH182 182 (runFrom pH182 (fmask pH182) (cmask pH182) (hmask pH182) 1 181 (true, (init pH182), (init pH182))) ∧ ptTest pH182 (runFrom pH182 (fmask pH182) (cmask pH182) (hmask pH182) 1 181 (true, (init pH182), (init pH182))) 182 91 true = true :=
  fin_run (runOK_init (prmOK_of_and H182_fin) true) (by decide) rfl H182_fin ptTest_fst
theorem I182_fin : (prmOK pI182 182 && intTest pI182 (runFrom pI182 (fmask pI182) (cmask pI182) (hmask pI182) 1 181 (true, (init pI182), (init pI182))) 182 9 true) = true := by
  decide +kernel
theorem I182_ok : RunOK pI182 182 (runFrom pI182 (fmask pI182) (cmask pI182) (hmask pI182) 1 181 (true, (init pI182), (init pI182))) ∧ intTest pI182 (runFrom pI182 (fmask pI182) (cmask pI182) (hmask pI182) 1 181 (true, (init pI182), (init pI182))) 182 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I182_fin) true) (by decide) rfl I182_fin intTest_fst
theorem link182 : linkOK pL182 pH182 pI182 = true := by decide +kernel
theorem cvx182 : ConvexBetweenHumps 182 :=
  cvx_of L182_ok H182_ok I182_ok link182 (by decide)
theorem cenlink182 : cenLinkOK pI182 182 = true := by decide +kernel
theorem cen182 : CenterUniqueMin 182 ∧ DipHyp 182 ∧ OnePointHyps 182 :=
  cen_of L182_ok H182_ok I182_ok link182 cenlink182

/-! ### `N = 183` -/

def pL183 : Prm := ⟨60, 28, 29, 185, 11, 18446744073709551616, 622708044865533029, 622708044865533029⟩
def pH183 : Prm := ⟨60, 28, 29, 185, 11, 18446744073709551616, 622743229237621861, 622743229237621861⟩
def pI183 : Prm := ⟨54, 26, 25, 185, 11, 18446744073709551616, 622708044865533029, 622743229237621861⟩
theorem L183_fin : (prmOK pL183 183 && ptTest pL183 (runFrom pL183 (fmask pL183) (cmask pL183) (hmask pL183) 1 182 (true, (init pL183), (init pL183))) 183 92 false) = true := by
  decide +kernel
theorem L183_ok : RunOK pL183 183 (runFrom pL183 (fmask pL183) (cmask pL183) (hmask pL183) 1 182 (true, (init pL183), (init pL183))) ∧ ptTest pL183 (runFrom pL183 (fmask pL183) (cmask pL183) (hmask pL183) 1 182 (true, (init pL183), (init pL183))) 183 92 false = true :=
  fin_run (runOK_init (prmOK_of_and L183_fin) true) (by decide) rfl L183_fin ptTest_fst
theorem H183_fin : (prmOK pH183 183 && ptTest pH183 (runFrom pH183 (fmask pH183) (cmask pH183) (hmask pH183) 1 182 (true, (init pH183), (init pH183))) 183 92 true) = true := by
  decide +kernel
theorem H183_ok : RunOK pH183 183 (runFrom pH183 (fmask pH183) (cmask pH183) (hmask pH183) 1 182 (true, (init pH183), (init pH183))) ∧ ptTest pH183 (runFrom pH183 (fmask pH183) (cmask pH183) (hmask pH183) 1 182 (true, (init pH183), (init pH183))) 183 92 true = true :=
  fin_run (runOK_init (prmOK_of_and H183_fin) true) (by decide) rfl H183_fin ptTest_fst
theorem I183_fin : (prmOK pI183 183 && intTest pI183 (runFrom pI183 (fmask pI183) (cmask pI183) (hmask pI183) 1 182 (true, (init pI183), (init pI183))) 183 9 false) = true := by
  decide +kernel
theorem I183_ok : RunOK pI183 183 (runFrom pI183 (fmask pI183) (cmask pI183) (hmask pI183) 1 182 (true, (init pI183), (init pI183))) ∧ intTest pI183 (runFrom pI183 (fmask pI183) (cmask pI183) (hmask pI183) 1 182 (true, (init pI183), (init pI183))) 183 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I183_fin) true) (by decide) rfl I183_fin intTest_fst
theorem link183 : linkOK pL183 pH183 pI183 = true := by decide +kernel
theorem cvx183 : ConvexBetweenHumps 183 :=
  cvx_of L183_ok H183_ok I183_ok link183 (by decide)

/-! ### `N = 184` -/

def pL184 : Prm := ⟨61, 29, 29, 186, 11, 18446744073709551616, 620332461125467764, 620332461125467764⟩
def pH184 : Prm := ⟨61, 29, 29, 186, 11, 18446744073709551616, 620367645497556596, 620367645497556596⟩
def pI184 : Prm := ⟨54, 26, 25, 186, 11, 18446744073709551616, 620332461125467764, 620367645497556596⟩
theorem L184_fin : (prmOK pL184 184 && ptTest pL184 (runFrom pL184 (fmask pL184) (cmask pL184) (hmask pL184) 1 183 (true, (init pL184), (init pL184))) 184 92 false) = true := by
  decide +kernel
theorem L184_ok : RunOK pL184 184 (runFrom pL184 (fmask pL184) (cmask pL184) (hmask pL184) 1 183 (true, (init pL184), (init pL184))) ∧ ptTest pL184 (runFrom pL184 (fmask pL184) (cmask pL184) (hmask pL184) 1 183 (true, (init pL184), (init pL184))) 184 92 false = true :=
  fin_run (runOK_init (prmOK_of_and L184_fin) true) (by decide) rfl L184_fin ptTest_fst
theorem H184_fin : (prmOK pH184 184 && ptTest pH184 (runFrom pH184 (fmask pH184) (cmask pH184) (hmask pH184) 1 183 (true, (init pH184), (init pH184))) 184 92 true) = true := by
  decide +kernel
theorem H184_ok : RunOK pH184 184 (runFrom pH184 (fmask pH184) (cmask pH184) (hmask pH184) 1 183 (true, (init pH184), (init pH184))) ∧ ptTest pH184 (runFrom pH184 (fmask pH184) (cmask pH184) (hmask pH184) 1 183 (true, (init pH184), (init pH184))) 184 92 true = true :=
  fin_run (runOK_init (prmOK_of_and H184_fin) true) (by decide) rfl H184_fin ptTest_fst
theorem I184_fin : (prmOK pI184 184 && intTest pI184 (runFrom pI184 (fmask pI184) (cmask pI184) (hmask pI184) 1 183 (true, (init pI184), (init pI184))) 184 9 true) = true := by
  decide +kernel
theorem I184_ok : RunOK pI184 184 (runFrom pI184 (fmask pI184) (cmask pI184) (hmask pI184) 1 183 (true, (init pI184), (init pI184))) ∧ intTest pI184 (runFrom pI184 (fmask pI184) (cmask pI184) (hmask pI184) 1 183 (true, (init pI184), (init pI184))) 184 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I184_fin) true) (by decide) rfl I184_fin intTest_fst
theorem link184 : linkOK pL184 pH184 pI184 = true := by decide +kernel
theorem cvx184 : ConvexBetweenHumps 184 :=
  cvx_of L184_ok H184_ok I184_ok link184 (by decide)
theorem cenlink184 : cenLinkOK pI184 184 = true := by decide +kernel
theorem cen184 : CenterUniqueMin 184 ∧ DipHyp 184 ∧ OnePointHyps 184 :=
  cen_of L184_ok H184_ok I184_ok link184 cenlink184

/-! ### `N = 185` -/

def pL185 : Prm := ⟨61, 29, 29, 187, 11, 18446744073709551616, 617958102064981360, 617958102064981360⟩
def pH185 : Prm := ⟨61, 29, 29, 187, 11, 18446744073709551616, 617993286437070192, 617993286437070192⟩
def pI185 : Prm := ⟨55, 26, 26, 187, 11, 18446744073709551616, 617958102064981360, 617993286437070192⟩
theorem L185_fin : (prmOK pL185 185 && ptTest pL185 (runFrom pL185 (fmask pL185) (cmask pL185) (hmask pL185) 1 184 (true, (init pL185), (init pL185))) 185 93 false) = true := by
  decide +kernel
theorem L185_ok : RunOK pL185 185 (runFrom pL185 (fmask pL185) (cmask pL185) (hmask pL185) 1 184 (true, (init pL185), (init pL185))) ∧ ptTest pL185 (runFrom pL185 (fmask pL185) (cmask pL185) (hmask pL185) 1 184 (true, (init pL185), (init pL185))) 185 93 false = true :=
  fin_run (runOK_init (prmOK_of_and L185_fin) true) (by decide) rfl L185_fin ptTest_fst
theorem H185_fin : (prmOK pH185 185 && ptTest pH185 (runFrom pH185 (fmask pH185) (cmask pH185) (hmask pH185) 1 184 (true, (init pH185), (init pH185))) 185 93 true) = true := by
  decide +kernel
theorem H185_ok : RunOK pH185 185 (runFrom pH185 (fmask pH185) (cmask pH185) (hmask pH185) 1 184 (true, (init pH185), (init pH185))) ∧ ptTest pH185 (runFrom pH185 (fmask pH185) (cmask pH185) (hmask pH185) 1 184 (true, (init pH185), (init pH185))) 185 93 true = true :=
  fin_run (runOK_init (prmOK_of_and H185_fin) true) (by decide) rfl H185_fin ptTest_fst
theorem I185_fin : (prmOK pI185 185 && intTest pI185 (runFrom pI185 (fmask pI185) (cmask pI185) (hmask pI185) 1 184 (true, (init pI185), (init pI185))) 185 9 false) = true := by
  decide +kernel
theorem I185_ok : RunOK pI185 185 (runFrom pI185 (fmask pI185) (cmask pI185) (hmask pI185) 1 184 (true, (init pI185), (init pI185))) ∧ intTest pI185 (runFrom pI185 (fmask pI185) (cmask pI185) (hmask pI185) 1 184 (true, (init pI185), (init pI185))) 185 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I185_fin) true) (by decide) rfl I185_fin intTest_fst
theorem link185 : linkOK pL185 pH185 pI185 = true := by decide +kernel
theorem cvx185 : ConvexBetweenHumps 185 :=
  cvx_of L185_ok H185_ok I185_ok link185 (by decide)

/-! ### `N = 186` -/

def pL186 : Prm := ⟨63, 30, 30, 188, 11, 18446744073709551616, 615632102332427186, 615632102332427186⟩
def pH186 : Prm := ⟨63, 30, 30, 188, 11, 18446744073709551616, 615649694518471602, 615649694518471602⟩
def pI186 : Prm := ⟨53, 26, 24, 188, 11, 18446744073709551616, 615632102332427186, 615649694518471602⟩
theorem L186_fin : (prmOK pL186 186 && ptTest pL186 (runFrom pL186 (fmask pL186) (cmask pL186) (hmask pL186) 1 185 (true, (init pL186), (init pL186))) 186 93 false) = true := by
  decide +kernel
theorem L186_ok : RunOK pL186 186 (runFrom pL186 (fmask pL186) (cmask pL186) (hmask pL186) 1 185 (true, (init pL186), (init pL186))) ∧ ptTest pL186 (runFrom pL186 (fmask pL186) (cmask pL186) (hmask pL186) 1 185 (true, (init pL186), (init pL186))) 186 93 false = true :=
  fin_run (runOK_init (prmOK_of_and L186_fin) true) (by decide) rfl L186_fin ptTest_fst
theorem H186_fin : (prmOK pH186 186 && ptTest pH186 (runFrom pH186 (fmask pH186) (cmask pH186) (hmask pH186) 1 185 (true, (init pH186), (init pH186))) 186 93 true) = true := by
  decide +kernel
theorem H186_ok : RunOK pH186 186 (runFrom pH186 (fmask pH186) (cmask pH186) (hmask pH186) 1 185 (true, (init pH186), (init pH186))) ∧ ptTest pH186 (runFrom pH186 (fmask pH186) (cmask pH186) (hmask pH186) 1 185 (true, (init pH186), (init pH186))) 186 93 true = true :=
  fin_run (runOK_init (prmOK_of_and H186_fin) true) (by decide) rfl H186_fin ptTest_fst
theorem I186_fin : (prmOK pI186 186 && intTest pI186 (runFrom pI186 (fmask pI186) (cmask pI186) (hmask pI186) 1 185 (true, (init pI186), (init pI186))) 186 9 true) = true := by
  decide +kernel
theorem I186_ok : RunOK pI186 186 (runFrom pI186 (fmask pI186) (cmask pI186) (hmask pI186) 1 185 (true, (init pI186), (init pI186))) ∧ intTest pI186 (runFrom pI186 (fmask pI186) (cmask pI186) (hmask pI186) 1 185 (true, (init pI186), (init pI186))) 186 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I186_fin) true) (by decide) rfl I186_fin intTest_fst
theorem link186 : linkOK pL186 pH186 pI186 = true := by decide +kernel
theorem cvx186 : ConvexBetweenHumps 186 :=
  cvx_of L186_ok H186_ok I186_ok link186 (by decide)
theorem cenlink186 : cenLinkOK pI186 186 = true := by decide +kernel
theorem cen186 : CenterUniqueMin 186 ∧ DipHyp 186 ∧ OnePointHyps 186 :=
  cen_of L186_ok H186_ok I186_ok link186 cenlink186

/-! ### `N = 187` -/

def pL187 : Prm := ⟨63, 30, 30, 189, 11, 18446744073709551616, 613298582531152461, 613298582531152461⟩
def pH187 : Prm := ⟨63, 30, 30, 189, 11, 18446744073709551616, 613316174717196877, 613316174717196877⟩
def pI187 : Prm := ⟨53, 26, 24, 189, 11, 18446744073709551616, 613298582531152461, 613316174717196877⟩
theorem L187_fin : (prmOK pL187 187 && ptTest pL187 (runFrom pL187 (fmask pL187) (cmask pL187) (hmask pL187) 1 186 (true, (init pL187), (init pL187))) 187 94 false) = true := by
  decide +kernel
theorem L187_ok : RunOK pL187 187 (runFrom pL187 (fmask pL187) (cmask pL187) (hmask pL187) 1 186 (true, (init pL187), (init pL187))) ∧ ptTest pL187 (runFrom pL187 (fmask pL187) (cmask pL187) (hmask pL187) 1 186 (true, (init pL187), (init pL187))) 187 94 false = true :=
  fin_run (runOK_init (prmOK_of_and L187_fin) true) (by decide) rfl L187_fin ptTest_fst
theorem H187_fin : (prmOK pH187 187 && ptTest pH187 (runFrom pH187 (fmask pH187) (cmask pH187) (hmask pH187) 1 186 (true, (init pH187), (init pH187))) 187 94 true) = true := by
  decide +kernel
theorem H187_ok : RunOK pH187 187 (runFrom pH187 (fmask pH187) (cmask pH187) (hmask pH187) 1 186 (true, (init pH187), (init pH187))) ∧ ptTest pH187 (runFrom pH187 (fmask pH187) (cmask pH187) (hmask pH187) 1 186 (true, (init pH187), (init pH187))) 187 94 true = true :=
  fin_run (runOK_init (prmOK_of_and H187_fin) true) (by decide) rfl H187_fin ptTest_fst
theorem I187_fin : (prmOK pI187 187 && intTest pI187 (runFrom pI187 (fmask pI187) (cmask pI187) (hmask pI187) 1 186 (true, (init pI187), (init pI187))) 187 9 false) = true := by
  decide +kernel
theorem I187_ok : RunOK pI187 187 (runFrom pI187 (fmask pI187) (cmask pI187) (hmask pI187) 1 186 (true, (init pI187), (init pI187))) ∧ intTest pI187 (runFrom pI187 (fmask pI187) (cmask pI187) (hmask pI187) 1 186 (true, (init pI187), (init pI187))) 187 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I187_fin) true) (by decide) rfl I187_fin intTest_fst
theorem link187 : linkOK pL187 pH187 pI187 = true := by decide +kernel
theorem cvx187 : ConvexBetweenHumps 187 :=
  cvx_of L187_ok H187_ok I187_ok link187 (by decide)

/-! ### `N = 188` -/

def pL188 : Prm := ⟨63, 30, 30, 190, 11, 18446744073709551616, 611003478499645580, 611003478499645580⟩
def pH188 : Prm := ⟨63, 30, 30, 190, 11, 18446744073709551616, 611021070685689996, 611021070685689996⟩
def pI188 : Prm := ⟨53, 26, 24, 190, 11, 18446744073709551616, 611003478499645580, 611021070685689996⟩
theorem L188_fin : (prmOK pL188 188 && ptTest pL188 (runFrom pL188 (fmask pL188) (cmask pL188) (hmask pL188) 1 187 (true, (init pL188), (init pL188))) 188 94 false) = true := by
  decide +kernel
theorem L188_ok : RunOK pL188 188 (runFrom pL188 (fmask pL188) (cmask pL188) (hmask pL188) 1 187 (true, (init pL188), (init pL188))) ∧ ptTest pL188 (runFrom pL188 (fmask pL188) (cmask pL188) (hmask pL188) 1 187 (true, (init pL188), (init pL188))) 188 94 false = true :=
  fin_run (runOK_init (prmOK_of_and L188_fin) true) (by decide) rfl L188_fin ptTest_fst
theorem H188_fin : (prmOK pH188 188 && ptTest pH188 (runFrom pH188 (fmask pH188) (cmask pH188) (hmask pH188) 1 187 (true, (init pH188), (init pH188))) 188 94 true) = true := by
  decide +kernel
theorem H188_ok : RunOK pH188 188 (runFrom pH188 (fmask pH188) (cmask pH188) (hmask pH188) 1 187 (true, (init pH188), (init pH188))) ∧ ptTest pH188 (runFrom pH188 (fmask pH188) (cmask pH188) (hmask pH188) 1 187 (true, (init pH188), (init pH188))) 188 94 true = true :=
  fin_run (runOK_init (prmOK_of_and H188_fin) true) (by decide) rfl H188_fin ptTest_fst
theorem I188_fin : (prmOK pI188 188 && intTest pI188 (runFrom pI188 (fmask pI188) (cmask pI188) (hmask pI188) 1 187 (true, (init pI188), (init pI188))) 188 9 true) = true := by
  decide +kernel
theorem I188_ok : RunOK pI188 188 (runFrom pI188 (fmask pI188) (cmask pI188) (hmask pI188) 1 187 (true, (init pI188), (init pI188))) ∧ intTest pI188 (runFrom pI188 (fmask pI188) (cmask pI188) (hmask pI188) 1 187 (true, (init pI188), (init pI188))) 188 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I188_fin) true) (by decide) rfl I188_fin intTest_fst
theorem link188 : linkOK pL188 pH188 pI188 = true := by decide +kernel
theorem cvx188 : ConvexBetweenHumps 188 :=
  cvx_of L188_ok H188_ok I188_ok link188 (by decide)
theorem cenlink188 : cenLinkOK pI188 188 = true := by decide +kernel
theorem cen188 : CenterUniqueMin 188 ∧ DipHyp 188 ∧ OnePointHyps 188 :=
  cen_of L188_ok H188_ok I188_ok link188 cenlink188

/-! ### `N = 189` -/

def pL189 : Prm := ⟨63, 30, 30, 191, 11, 18446744073709551616, 608709697418337841, 608709697418337841⟩
def pH189 : Prm := ⟨63, 30, 30, 191, 11, 18446744073709551616, 608727289604382257, 608727289604382257⟩
def pI189 : Prm := ⟨53, 26, 24, 191, 11, 18446744073709551616, 608709697418337841, 608727289604382257⟩
theorem L189_fin : (prmOK pL189 189 && ptTest pL189 (runFrom pL189 (fmask pL189) (cmask pL189) (hmask pL189) 1 188 (true, (init pL189), (init pL189))) 189 95 false) = true := by
  decide +kernel
theorem L189_ok : RunOK pL189 189 (runFrom pL189 (fmask pL189) (cmask pL189) (hmask pL189) 1 188 (true, (init pL189), (init pL189))) ∧ ptTest pL189 (runFrom pL189 (fmask pL189) (cmask pL189) (hmask pL189) 1 188 (true, (init pL189), (init pL189))) 189 95 false = true :=
  fin_run (runOK_init (prmOK_of_and L189_fin) true) (by decide) rfl L189_fin ptTest_fst
theorem H189_fin : (prmOK pH189 189 && ptTest pH189 (runFrom pH189 (fmask pH189) (cmask pH189) (hmask pH189) 1 188 (true, (init pH189), (init pH189))) 189 95 true) = true := by
  decide +kernel
theorem H189_ok : RunOK pH189 189 (runFrom pH189 (fmask pH189) (cmask pH189) (hmask pH189) 1 188 (true, (init pH189), (init pH189))) ∧ ptTest pH189 (runFrom pH189 (fmask pH189) (cmask pH189) (hmask pH189) 1 188 (true, (init pH189), (init pH189))) 189 95 true = true :=
  fin_run (runOK_init (prmOK_of_and H189_fin) true) (by decide) rfl H189_fin ptTest_fst
theorem I189_fin : (prmOK pI189 189 && intTest pI189 (runFrom pI189 (fmask pI189) (cmask pI189) (hmask pI189) 1 188 (true, (init pI189), (init pI189))) 189 9 false) = true := by
  decide +kernel
theorem I189_ok : RunOK pI189 189 (runFrom pI189 (fmask pI189) (cmask pI189) (hmask pI189) 1 188 (true, (init pI189), (init pI189))) ∧ intTest pI189 (runFrom pI189 (fmask pI189) (cmask pI189) (hmask pI189) 1 188 (true, (init pI189), (init pI189))) 189 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I189_fin) true) (by decide) rfl I189_fin intTest_fst
theorem link189 : linkOK pL189 pH189 pI189 = true := by decide +kernel
theorem cvx189 : ConvexBetweenHumps 189 :=
  cvx_of L189_ok H189_ok I189_ok link189 (by decide)

/-! ### `N = 190` -/

def pL190 : Prm := ⟨63, 30, 30, 192, 11, 18446744073709551616, 606453229139371440, 606453229139371440⟩
def pH190 : Prm := ⟨63, 30, 30, 192, 11, 18446744073709551616, 606470821325415856, 606470821325415856⟩
def pI190 : Prm := ⟨54, 26, 25, 192, 11, 18446744073709551616, 606453229139371440, 606470821325415856⟩
theorem L190_fin : (prmOK pL190 190 && ptTest pL190 (runFrom pL190 (fmask pL190) (cmask pL190) (hmask pL190) 1 189 (true, (init pL190), (init pL190))) 190 95 false) = true := by
  decide +kernel
theorem L190_ok : RunOK pL190 190 (runFrom pL190 (fmask pL190) (cmask pL190) (hmask pL190) 1 189 (true, (init pL190), (init pL190))) ∧ ptTest pL190 (runFrom pL190 (fmask pL190) (cmask pL190) (hmask pL190) 1 189 (true, (init pL190), (init pL190))) 190 95 false = true :=
  fin_run (runOK_init (prmOK_of_and L190_fin) true) (by decide) rfl L190_fin ptTest_fst
theorem H190_fin : (prmOK pH190 190 && ptTest pH190 (runFrom pH190 (fmask pH190) (cmask pH190) (hmask pH190) 1 189 (true, (init pH190), (init pH190))) 190 95 true) = true := by
  decide +kernel
theorem H190_ok : RunOK pH190 190 (runFrom pH190 (fmask pH190) (cmask pH190) (hmask pH190) 1 189 (true, (init pH190), (init pH190))) ∧ ptTest pH190 (runFrom pH190 (fmask pH190) (cmask pH190) (hmask pH190) 1 189 (true, (init pH190), (init pH190))) 190 95 true = true :=
  fin_run (runOK_init (prmOK_of_and H190_fin) true) (by decide) rfl H190_fin ptTest_fst
theorem I190_fin : (prmOK pI190 190 && intTest pI190 (runFrom pI190 (fmask pI190) (cmask pI190) (hmask pI190) 1 189 (true, (init pI190), (init pI190))) 190 9 true) = true := by
  decide +kernel
theorem I190_ok : RunOK pI190 190 (runFrom pI190 (fmask pI190) (cmask pI190) (hmask pI190) 1 189 (true, (init pI190), (init pI190))) ∧ intTest pI190 (runFrom pI190 (fmask pI190) (cmask pI190) (hmask pI190) 1 189 (true, (init pI190), (init pI190))) 190 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I190_fin) true) (by decide) rfl I190_fin intTest_fst
theorem link190 : linkOK pL190 pH190 pI190 = true := by decide +kernel
theorem cvx190 : ConvexBetweenHumps 190 :=
  cvx_of L190_ok H190_ok I190_ok link190 (by decide)
theorem cenlink190 : cenLinkOK pI190 190 = true := by decide +kernel
theorem cen190 : CenterUniqueMin 190 ∧ DipHyp 190 ∧ OnePointHyps 190 :=
  cen_of L190_ok H190_ok I190_ok link190 cenlink190

/-! ### `N = 191` -/

def pL191 : Prm := ⟨63, 30, 30, 193, 11, 18446744073709551616, 604198126617934010, 604198126617934010⟩
def pH191 : Prm := ⟨63, 30, 30, 193, 11, 18446744073709551616, 604215718803978426, 604215718803978426⟩
def pI191 : Prm := ⟨54, 26, 25, 193, 11, 18446744073709551616, 604198126617934010, 604215718803978426⟩
theorem L191_fin : (prmOK pL191 191 && ptTest pL191 (runFrom pL191 (fmask pL191) (cmask pL191) (hmask pL191) 1 190 (true, (init pL191), (init pL191))) 191 96 false) = true := by
  decide +kernel
theorem L191_ok : RunOK pL191 191 (runFrom pL191 (fmask pL191) (cmask pL191) (hmask pL191) 1 190 (true, (init pL191), (init pL191))) ∧ ptTest pL191 (runFrom pL191 (fmask pL191) (cmask pL191) (hmask pL191) 1 190 (true, (init pL191), (init pL191))) 191 96 false = true :=
  fin_run (runOK_init (prmOK_of_and L191_fin) true) (by decide) rfl L191_fin ptTest_fst
theorem H191_fin : (prmOK pH191 191 && ptTest pH191 (runFrom pH191 (fmask pH191) (cmask pH191) (hmask pH191) 1 190 (true, (init pH191), (init pH191))) 191 96 true) = true := by
  decide +kernel
theorem H191_ok : RunOK pH191 191 (runFrom pH191 (fmask pH191) (cmask pH191) (hmask pH191) 1 190 (true, (init pH191), (init pH191))) ∧ ptTest pH191 (runFrom pH191 (fmask pH191) (cmask pH191) (hmask pH191) 1 190 (true, (init pH191), (init pH191))) 191 96 true = true :=
  fin_run (runOK_init (prmOK_of_and H191_fin) true) (by decide) rfl H191_fin ptTest_fst
theorem I191_fin : (prmOK pI191 191 && intTest pI191 (runFrom pI191 (fmask pI191) (cmask pI191) (hmask pI191) 1 190 (true, (init pI191), (init pI191))) 191 9 false) = true := by
  decide +kernel
theorem I191_ok : RunOK pI191 191 (runFrom pI191 (fmask pI191) (cmask pI191) (hmask pI191) 1 190 (true, (init pI191), (init pI191))) ∧ intTest pI191 (runFrom pI191 (fmask pI191) (cmask pI191) (hmask pI191) 1 190 (true, (init pI191), (init pI191))) 191 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I191_fin) true) (by decide) rfl I191_fin intTest_fst
theorem link191 : linkOK pL191 pH191 pI191 = true := by decide +kernel
theorem cvx191 : ConvexBetweenHumps 191 :=
  cvx_of L191_ok H191_ok I191_ok link191 (by decide)

/-! ### `N = 192` -/

def pL192 : Prm := ⟨63, 30, 30, 194, 11, 18446744073709551616, 601979276278255168, 601979276278255168⟩
def pH192 : Prm := ⟨63, 30, 30, 194, 11, 18446744073709551616, 601996868464299584, 601996868464299584⟩
def pI192 : Prm := ⟨54, 26, 25, 194, 11, 18446744073709551616, 601979276278255168, 601996868464299584⟩
theorem L192_fin : (prmOK pL192 192 && ptTest pL192 (runFrom pL192 (fmask pL192) (cmask pL192) (hmask pL192) 1 191 (true, (init pL192), (init pL192))) 192 96 false) = true := by
  decide +kernel
theorem L192_ok : RunOK pL192 192 (runFrom pL192 (fmask pL192) (cmask pL192) (hmask pL192) 1 191 (true, (init pL192), (init pL192))) ∧ ptTest pL192 (runFrom pL192 (fmask pL192) (cmask pL192) (hmask pL192) 1 191 (true, (init pL192), (init pL192))) 192 96 false = true :=
  fin_run (runOK_init (prmOK_of_and L192_fin) true) (by decide) rfl L192_fin ptTest_fst
theorem H192_fin : (prmOK pH192 192 && ptTest pH192 (runFrom pH192 (fmask pH192) (cmask pH192) (hmask pH192) 1 191 (true, (init pH192), (init pH192))) 192 96 true) = true := by
  decide +kernel
theorem H192_ok : RunOK pH192 192 (runFrom pH192 (fmask pH192) (cmask pH192) (hmask pH192) 1 191 (true, (init pH192), (init pH192))) ∧ ptTest pH192 (runFrom pH192 (fmask pH192) (cmask pH192) (hmask pH192) 1 191 (true, (init pH192), (init pH192))) 192 96 true = true :=
  fin_run (runOK_init (prmOK_of_and H192_fin) true) (by decide) rfl H192_fin ptTest_fst
theorem I192_fin : (prmOK pI192 192 && intTest pI192 (runFrom pI192 (fmask pI192) (cmask pI192) (hmask pI192) 1 191 (true, (init pI192), (init pI192))) 192 9 true) = true := by
  decide +kernel
theorem I192_ok : RunOK pI192 192 (runFrom pI192 (fmask pI192) (cmask pI192) (hmask pI192) 1 191 (true, (init pI192), (init pI192))) ∧ intTest pI192 (runFrom pI192 (fmask pI192) (cmask pI192) (hmask pI192) 1 191 (true, (init pI192), (init pI192))) 192 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I192_fin) true) (by decide) rfl I192_fin intTest_fst
theorem link192 : linkOK pL192 pH192 pI192 = true := by decide +kernel
theorem cvx192 : ConvexBetweenHumps 192 :=
  cvx_of L192_ok H192_ok I192_ok link192 (by decide)
theorem cenlink192 : cenLinkOK pI192 192 = true := by decide +kernel
theorem cen192 : CenterUniqueMin 192 ∧ DipHyp 192 ∧ OnePointHyps 192 :=
  cen_of L192_ok H192_ok I192_ok link192 cenlink192

/-! ### `N = 193` -/

def pL193 : Prm := ⟨63, 30, 30, 195, 11, 18446744073709551616, 599761830663929817, 599761830663929817⟩
def pH193 : Prm := ⟨63, 30, 30, 195, 11, 18446744073709551616, 599779422849974233, 599779422849974233⟩
def pI193 : Prm := ⟨54, 26, 25, 195, 11, 18446744073709551616, 599761830663929817, 599779422849974233⟩
theorem L193_fin : (prmOK pL193 193 && ptTest pL193 (runFrom pL193 (fmask pL193) (cmask pL193) (hmask pL193) 1 192 (true, (init pL193), (init pL193))) 193 97 false) = true := by
  decide +kernel
theorem L193_ok : RunOK pL193 193 (runFrom pL193 (fmask pL193) (cmask pL193) (hmask pL193) 1 192 (true, (init pL193), (init pL193))) ∧ ptTest pL193 (runFrom pL193 (fmask pL193) (cmask pL193) (hmask pL193) 1 192 (true, (init pL193), (init pL193))) 193 97 false = true :=
  fin_run (runOK_init (prmOK_of_and L193_fin) true) (by decide) rfl L193_fin ptTest_fst
theorem H193_fin : (prmOK pH193 193 && ptTest pH193 (runFrom pH193 (fmask pH193) (cmask pH193) (hmask pH193) 1 192 (true, (init pH193), (init pH193))) 193 97 true) = true := by
  decide +kernel
theorem H193_ok : RunOK pH193 193 (runFrom pH193 (fmask pH193) (cmask pH193) (hmask pH193) 1 192 (true, (init pH193), (init pH193))) ∧ ptTest pH193 (runFrom pH193 (fmask pH193) (cmask pH193) (hmask pH193) 1 192 (true, (init pH193), (init pH193))) 193 97 true = true :=
  fin_run (runOK_init (prmOK_of_and H193_fin) true) (by decide) rfl H193_fin ptTest_fst
theorem I193_fin : (prmOK pI193 193 && intTest pI193 (runFrom pI193 (fmask pI193) (cmask pI193) (hmask pI193) 1 192 (true, (init pI193), (init pI193))) 193 9 false) = true := by
  decide +kernel
theorem I193_ok : RunOK pI193 193 (runFrom pI193 (fmask pI193) (cmask pI193) (hmask pI193) 1 192 (true, (init pI193), (init pI193))) ∧ intTest pI193 (runFrom pI193 (fmask pI193) (cmask pI193) (hmask pI193) 1 192 (true, (init pI193), (init pI193))) 193 9 false = true :=
  fin_run (runOK_init (prmOK_of_and I193_fin) true) (by decide) rfl I193_fin intTest_fst
theorem link193 : linkOK pL193 pH193 pI193 = true := by decide +kernel
theorem cvx193 : ConvexBetweenHumps 193 :=
  cvx_of L193_ok H193_ok I193_ok link193 (by decide)

/-! ### `N = 194` -/

def pL194 : Prm := ⟨63, 30, 30, 196, 11, 18446744073709551616, 597579616930751162, 597579616930751162⟩
def pH194 : Prm := ⟨63, 30, 30, 196, 11, 18446744073709551616, 597597209116795578, 597597209116795578⟩
def pI194 : Prm := ⟨54, 26, 25, 196, 11, 18446744073709551616, 597579616930751162, 597597209116795578⟩
theorem L194_fin : (prmOK pL194 194 && ptTest pL194 (runFrom pL194 (fmask pL194) (cmask pL194) (hmask pL194) 1 193 (true, (init pL194), (init pL194))) 194 97 false) = true := by
  decide +kernel
theorem L194_ok : RunOK pL194 194 (runFrom pL194 (fmask pL194) (cmask pL194) (hmask pL194) 1 193 (true, (init pL194), (init pL194))) ∧ ptTest pL194 (runFrom pL194 (fmask pL194) (cmask pL194) (hmask pL194) 1 193 (true, (init pL194), (init pL194))) 194 97 false = true :=
  fin_run (runOK_init (prmOK_of_and L194_fin) true) (by decide) rfl L194_fin ptTest_fst
theorem H194_fin : (prmOK pH194 194 && ptTest pH194 (runFrom pH194 (fmask pH194) (cmask pH194) (hmask pH194) 1 193 (true, (init pH194), (init pH194))) 194 97 true) = true := by
  decide +kernel
theorem H194_ok : RunOK pH194 194 (runFrom pH194 (fmask pH194) (cmask pH194) (hmask pH194) 1 193 (true, (init pH194), (init pH194))) ∧ ptTest pH194 (runFrom pH194 (fmask pH194) (cmask pH194) (hmask pH194) 1 193 (true, (init pH194), (init pH194))) 194 97 true = true :=
  fin_run (runOK_init (prmOK_of_and H194_fin) true) (by decide) rfl H194_fin ptTest_fst
theorem I194_fin : (prmOK pI194 194 && intTest pI194 (runFrom pI194 (fmask pI194) (cmask pI194) (hmask pI194) 1 193 (true, (init pI194), (init pI194))) 194 9 true) = true := by
  decide +kernel
theorem I194_ok : RunOK pI194 194 (runFrom pI194 (fmask pI194) (cmask pI194) (hmask pI194) 1 193 (true, (init pI194), (init pI194))) ∧ intTest pI194 (runFrom pI194 (fmask pI194) (cmask pI194) (hmask pI194) 1 193 (true, (init pI194), (init pI194))) 194 9 true = true :=
  fin_run (runOK_init (prmOK_of_and I194_fin) true) (by decide) rfl I194_fin intTest_fst
theorem link194 : linkOK pL194 pH194 pI194 = true := by decide +kernel
theorem cvx194 : ConvexBetweenHumps 194 :=
  cvx_of L194_ok H194_ok I194_ok link194 (by decide)
theorem cenlink194 : cenLinkOK pI194 194 = true := by decide +kernel
theorem cen194 : CenterUniqueMin 194 ∧ DipHyp 194 ∧ OnePointHyps 194 :=
  cen_of L194_ok H194_ok I194_ok link194 cenlink194

/-! ### `N = 195` -/

def pL195 : Prm := ⟨63, 30, 30, 197, 11, 18446744073709551616, 595398843310993809, 595398843310993809⟩
def pH195 : Prm := ⟨63, 30, 30, 197, 11, 18446744073709551616, 595416435497038225, 595416435497038225⟩
def pI195 : Prm := ⟨54, 26, 25, 197, 11, 18446744073709551616, 595398843310993809, 595416435497038225⟩
theorem L195_fin : (prmOK pL195 195 && ptTest pL195 (runFrom pL195 (fmask pL195) (cmask pL195) (hmask pL195) 1 194 (true, (init pL195), (init pL195))) 195 98 false) = true := by
  decide +kernel
theorem L195_ok : RunOK pL195 195 (runFrom pL195 (fmask pL195) (cmask pL195) (hmask pL195) 1 194 (true, (init pL195), (init pL195))) ∧ ptTest pL195 (runFrom pL195 (fmask pL195) (cmask pL195) (hmask pL195) 1 194 (true, (init pL195), (init pL195))) 195 98 false = true :=
  fin_run (runOK_init (prmOK_of_and L195_fin) true) (by decide) rfl L195_fin ptTest_fst
theorem H195_fin : (prmOK pH195 195 && ptTest pH195 (runFrom pH195 (fmask pH195) (cmask pH195) (hmask pH195) 1 194 (true, (init pH195), (init pH195))) 195 98 true) = true := by
  decide +kernel
theorem H195_ok : RunOK pH195 195 (runFrom pH195 (fmask pH195) (cmask pH195) (hmask pH195) 1 194 (true, (init pH195), (init pH195))) ∧ ptTest pH195 (runFrom pH195 (fmask pH195) (cmask pH195) (hmask pH195) 1 194 (true, (init pH195), (init pH195))) 195 98 true = true :=
  fin_run (runOK_init (prmOK_of_and H195_fin) true) (by decide) rfl H195_fin ptTest_fst
theorem I195_fin : (prmOK pI195 195 && intTest pI195 (runFrom pI195 (fmask pI195) (cmask pI195) (hmask pI195) 1 194 (true, (init pI195), (init pI195))) 195 10 false) = true := by
  decide +kernel
theorem I195_ok : RunOK pI195 195 (runFrom pI195 (fmask pI195) (cmask pI195) (hmask pI195) 1 194 (true, (init pI195), (init pI195))) ∧ intTest pI195 (runFrom pI195 (fmask pI195) (cmask pI195) (hmask pI195) 1 194 (true, (init pI195), (init pI195))) 195 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I195_fin) true) (by decide) rfl I195_fin intTest_fst
theorem link195 : linkOK pL195 pH195 pI195 = true := by decide +kernel
theorem cvx195 : ConvexBetweenHumps 195 :=
  cvx_of L195_ok H195_ok I195_ok link195 (by decide)

/-! ### `N = 196` -/

def pL196 : Prm := ⟨63, 30, 30, 198, 11, 18446744073709551616, 593252319680714775, 593252319680714775⟩
def pH196 : Prm := ⟨63, 30, 30, 198, 11, 18446744073709551616, 593269911866759191, 593269911866759191⟩
def pI196 : Prm := ⟨54, 26, 25, 198, 11, 18446744073709551616, 593252319680714775, 593269911866759191⟩
theorem L196_fin : (prmOK pL196 196 && ptTest pL196 (runFrom pL196 (fmask pL196) (cmask pL196) (hmask pL196) 1 195 (true, (init pL196), (init pL196))) 196 98 false) = true := by
  decide +kernel
theorem L196_ok : RunOK pL196 196 (runFrom pL196 (fmask pL196) (cmask pL196) (hmask pL196) 1 195 (true, (init pL196), (init pL196))) ∧ ptTest pL196 (runFrom pL196 (fmask pL196) (cmask pL196) (hmask pL196) 1 195 (true, (init pL196), (init pL196))) 196 98 false = true :=
  fin_run (runOK_init (prmOK_of_and L196_fin) true) (by decide) rfl L196_fin ptTest_fst
theorem H196_fin : (prmOK pH196 196 && ptTest pH196 (runFrom pH196 (fmask pH196) (cmask pH196) (hmask pH196) 1 195 (true, (init pH196), (init pH196))) 196 98 true) = true := by
  decide +kernel
theorem H196_ok : RunOK pH196 196 (runFrom pH196 (fmask pH196) (cmask pH196) (hmask pH196) 1 195 (true, (init pH196), (init pH196))) ∧ ptTest pH196 (runFrom pH196 (fmask pH196) (cmask pH196) (hmask pH196) 1 195 (true, (init pH196), (init pH196))) 196 98 true = true :=
  fin_run (runOK_init (prmOK_of_and H196_fin) true) (by decide) rfl H196_fin ptTest_fst
theorem I196_fin : (prmOK pI196 196 && intTest pI196 (runFrom pI196 (fmask pI196) (cmask pI196) (hmask pI196) 1 195 (true, (init pI196), (init pI196))) 196 10 true) = true := by
  decide +kernel
theorem I196_ok : RunOK pI196 196 (runFrom pI196 (fmask pI196) (cmask pI196) (hmask pI196) 1 195 (true, (init pI196), (init pI196))) ∧ intTest pI196 (runFrom pI196 (fmask pI196) (cmask pI196) (hmask pI196) 1 195 (true, (init pI196), (init pI196))) 196 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I196_fin) true) (by decide) rfl I196_fin intTest_fst
theorem link196 : linkOK pL196 pH196 pI196 = true := by decide +kernel
theorem cvx196 : ConvexBetweenHumps 196 :=
  cvx_of L196_ok H196_ok I196_ok link196 (by decide)
theorem cenlink196 : cenLinkOK pI196 196 = true := by decide +kernel
theorem cen196 : CenterUniqueMin 196 ∧ DipHyp 196 ∧ OnePointHyps 196 :=
  cen_of L196_ok H196_ok I196_ok link196 cenlink196

/-! ### `N = 197` -/

def pL197 : Prm := ⟨63, 30, 30, 199, 11, 18446744073709551616, 591107268213857385, 591107268213857385⟩
def pH197 : Prm := ⟨63, 30, 30, 199, 11, 18446744073709551616, 591124860399901801, 591124860399901801⟩
def pI197 : Prm := ⟨54, 26, 25, 199, 11, 18446744073709551616, 591107268213857385, 591124860399901801⟩
theorem L197_fin : (prmOK pL197 197 && ptTest pL197 (runFrom pL197 (fmask pL197) (cmask pL197) (hmask pL197) 1 196 (true, (init pL197), (init pL197))) 197 99 false) = true := by
  decide +kernel
theorem L197_ok : RunOK pL197 197 (runFrom pL197 (fmask pL197) (cmask pL197) (hmask pL197) 1 196 (true, (init pL197), (init pL197))) ∧ ptTest pL197 (runFrom pL197 (fmask pL197) (cmask pL197) (hmask pL197) 1 196 (true, (init pL197), (init pL197))) 197 99 false = true :=
  fin_run (runOK_init (prmOK_of_and L197_fin) true) (by decide) rfl L197_fin ptTest_fst
theorem H197_fin : (prmOK pH197 197 && ptTest pH197 (runFrom pH197 (fmask pH197) (cmask pH197) (hmask pH197) 1 196 (true, (init pH197), (init pH197))) 197 99 true) = true := by
  decide +kernel
theorem H197_ok : RunOK pH197 197 (runFrom pH197 (fmask pH197) (cmask pH197) (hmask pH197) 1 196 (true, (init pH197), (init pH197))) ∧ ptTest pH197 (runFrom pH197 (fmask pH197) (cmask pH197) (hmask pH197) 1 196 (true, (init pH197), (init pH197))) 197 99 true = true :=
  fin_run (runOK_init (prmOK_of_and H197_fin) true) (by decide) rfl H197_fin ptTest_fst
theorem I197_fin : (prmOK pI197 197 && intTest pI197 (runFrom pI197 (fmask pI197) (cmask pI197) (hmask pI197) 1 196 (true, (init pI197), (init pI197))) 197 10 false) = true := by
  decide +kernel
theorem I197_ok : RunOK pI197 197 (runFrom pI197 (fmask pI197) (cmask pI197) (hmask pI197) 1 196 (true, (init pI197), (init pI197))) ∧ intTest pI197 (runFrom pI197 (fmask pI197) (cmask pI197) (hmask pI197) 1 196 (true, (init pI197), (init pI197))) 197 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I197_fin) true) (by decide) rfl I197_fin intTest_fst
theorem link197 : linkOK pL197 pH197 pI197 = true := by decide +kernel
theorem cvx197 : ConvexBetweenHumps 197 :=
  cvx_of L197_ok H197_ok I197_ok link197 (by decide)

/-! ### `N = 198` -/

def pL198 : Prm := ⟨63, 30, 30, 200, 11, 18446744073709551616, 588995521450842472, 588995521450842472⟩
def pH198 : Prm := ⟨63, 30, 30, 200, 11, 18446744073709551616, 589013113636886888, 589013113636886888⟩
def pI198 : Prm := ⟨53, 26, 24, 200, 11, 18446744073709551616, 588995521450842472, 589013113636886888⟩
theorem L198_fin : (prmOK pL198 198 && ptTest pL198 (runFrom pL198 (fmask pL198) (cmask pL198) (hmask pL198) 1 197 (true, (init pL198), (init pL198))) 198 99 false) = true := by
  decide +kernel
theorem L198_ok : RunOK pL198 198 (runFrom pL198 (fmask pL198) (cmask pL198) (hmask pL198) 1 197 (true, (init pL198), (init pL198))) ∧ ptTest pL198 (runFrom pL198 (fmask pL198) (cmask pL198) (hmask pL198) 1 197 (true, (init pL198), (init pL198))) 198 99 false = true :=
  fin_run (runOK_init (prmOK_of_and L198_fin) true) (by decide) rfl L198_fin ptTest_fst
theorem H198_fin : (prmOK pH198 198 && ptTest pH198 (runFrom pH198 (fmask pH198) (cmask pH198) (hmask pH198) 1 197 (true, (init pH198), (init pH198))) 198 99 true) = true := by
  decide +kernel
theorem H198_ok : RunOK pH198 198 (runFrom pH198 (fmask pH198) (cmask pH198) (hmask pH198) 1 197 (true, (init pH198), (init pH198))) ∧ ptTest pH198 (runFrom pH198 (fmask pH198) (cmask pH198) (hmask pH198) 1 197 (true, (init pH198), (init pH198))) 198 99 true = true :=
  fin_run (runOK_init (prmOK_of_and H198_fin) true) (by decide) rfl H198_fin ptTest_fst
theorem I198_fin : (prmOK pI198 198 && intTest pI198 (runFrom pI198 (fmask pI198) (cmask pI198) (hmask pI198) 1 197 (true, (init pI198), (init pI198))) 198 10 true) = true := by
  decide +kernel
theorem I198_ok : RunOK pI198 198 (runFrom pI198 (fmask pI198) (cmask pI198) (hmask pI198) 1 197 (true, (init pI198), (init pI198))) ∧ intTest pI198 (runFrom pI198 (fmask pI198) (cmask pI198) (hmask pI198) 1 197 (true, (init pI198), (init pI198))) 198 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I198_fin) true) (by decide) rfl I198_fin intTest_fst
theorem link198 : linkOK pL198 pH198 pI198 = true := by decide +kernel
theorem cvx198 : ConvexBetweenHumps 198 :=
  cvx_of L198_ok H198_ok I198_ok link198 (by decide)
theorem cenlink198 : cenLinkOK pI198 198 = true := by decide +kernel
theorem cen198 : CenterUniqueMin 198 ∧ DipHyp 198 ∧ OnePointHyps 198 :=
  cen_of L198_ok H198_ok I198_ok link198 cenlink198

/-! ### `N = 199` -/

def pL199 : Prm := ⟨61, 29, 29, 201, 11, 18446744073709551616, 586876479695191702, 586876479695191702⟩
def pH199 : Prm := ⟨61, 29, 29, 201, 11, 18446744073709551616, 586911664067280534, 586911664067280534⟩
def pI199 : Prm := ⟨54, 26, 25, 201, 11, 18446744073709551616, 586876479695191702, 586911664067280534⟩
theorem L199_fin : (prmOK pL199 199 && ptTest pL199 (runFrom pL199 (fmask pL199) (cmask pL199) (hmask pL199) 1 198 (true, (init pL199), (init pL199))) 199 100 false) = true := by
  decide +kernel
theorem L199_ok : RunOK pL199 199 (runFrom pL199 (fmask pL199) (cmask pL199) (hmask pL199) 1 198 (true, (init pL199), (init pL199))) ∧ ptTest pL199 (runFrom pL199 (fmask pL199) (cmask pL199) (hmask pL199) 1 198 (true, (init pL199), (init pL199))) 199 100 false = true :=
  fin_run (runOK_init (prmOK_of_and L199_fin) true) (by decide) rfl L199_fin ptTest_fst
theorem H199_fin : (prmOK pH199 199 && ptTest pH199 (runFrom pH199 (fmask pH199) (cmask pH199) (hmask pH199) 1 198 (true, (init pH199), (init pH199))) 199 100 true) = true := by
  decide +kernel
theorem H199_ok : RunOK pH199 199 (runFrom pH199 (fmask pH199) (cmask pH199) (hmask pH199) 1 198 (true, (init pH199), (init pH199))) ∧ ptTest pH199 (runFrom pH199 (fmask pH199) (cmask pH199) (hmask pH199) 1 198 (true, (init pH199), (init pH199))) 199 100 true = true :=
  fin_run (runOK_init (prmOK_of_and H199_fin) true) (by decide) rfl H199_fin ptTest_fst
theorem I199_fin : (prmOK pI199 199 && intTest pI199 (runFrom pI199 (fmask pI199) (cmask pI199) (hmask pI199) 1 198 (true, (init pI199), (init pI199))) 199 10 false) = true := by
  decide +kernel
theorem I199_ok : RunOK pI199 199 (runFrom pI199 (fmask pI199) (cmask pI199) (hmask pI199) 1 198 (true, (init pI199), (init pI199))) ∧ intTest pI199 (runFrom pI199 (fmask pI199) (cmask pI199) (hmask pI199) 1 198 (true, (init pI199), (init pI199))) 199 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I199_fin) true) (by decide) rfl I199_fin intTest_fst
theorem link199 : linkOK pL199 pH199 pI199 = true := by decide +kernel
theorem cvx199 : ConvexBetweenHumps 199 :=
  cvx_of L199_ok H199_ok I199_ok link199 (by decide)

/-! ### `N = 200` -/

def pL200 : Prm := ⟨61, 29, 29, 202, 11, 18446744073709551616, 584798628354979488, 584798628354979488⟩
def pH200 : Prm := ⟨61, 29, 29, 202, 11, 18446744073709551616, 584833812727068320, 584833812727068320⟩
def pI200 : Prm := ⟨54, 26, 25, 202, 11, 18446744073709551616, 584798628354979488, 584833812727068320⟩
theorem L200_fin : (prmOK pL200 200 && ptTest pL200 (runFrom pL200 (fmask pL200) (cmask pL200) (hmask pL200) 1 199 (true, (init pL200), (init pL200))) 200 100 false) = true := by
  decide +kernel
theorem L200_ok : RunOK pL200 200 (runFrom pL200 (fmask pL200) (cmask pL200) (hmask pL200) 1 199 (true, (init pL200), (init pL200))) ∧ ptTest pL200 (runFrom pL200 (fmask pL200) (cmask pL200) (hmask pL200) 1 199 (true, (init pL200), (init pL200))) 200 100 false = true :=
  fin_run (runOK_init (prmOK_of_and L200_fin) true) (by decide) rfl L200_fin ptTest_fst
theorem H200_fin : (prmOK pH200 200 && ptTest pH200 (runFrom pH200 (fmask pH200) (cmask pH200) (hmask pH200) 1 199 (true, (init pH200), (init pH200))) 200 100 true) = true := by
  decide +kernel
theorem H200_ok : RunOK pH200 200 (runFrom pH200 (fmask pH200) (cmask pH200) (hmask pH200) 1 199 (true, (init pH200), (init pH200))) ∧ ptTest pH200 (runFrom pH200 (fmask pH200) (cmask pH200) (hmask pH200) 1 199 (true, (init pH200), (init pH200))) 200 100 true = true :=
  fin_run (runOK_init (prmOK_of_and H200_fin) true) (by decide) rfl H200_fin ptTest_fst
theorem I200_fin : (prmOK pI200 200 && intTest pI200 (runFrom pI200 (fmask pI200) (cmask pI200) (hmask pI200) 1 199 (true, (init pI200), (init pI200))) 200 10 true) = true := by
  decide +kernel
theorem I200_ok : RunOK pI200 200 (runFrom pI200 (fmask pI200) (cmask pI200) (hmask pI200) 1 199 (true, (init pI200), (init pI200))) ∧ intTest pI200 (runFrom pI200 (fmask pI200) (cmask pI200) (hmask pI200) 1 199 (true, (init pI200), (init pI200))) 200 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I200_fin) true) (by decide) rfl I200_fin intTest_fst
theorem link200 : linkOK pL200 pH200 pI200 = true := by decide +kernel
theorem cvx200 : ConvexBetweenHumps 200 :=
  cvx_of L200_ok H200_ok I200_ok link200 (by decide)
theorem cenlink200 : cenLinkOK pI200 200 = true := by decide +kernel
theorem cen200 : CenterUniqueMin 200 ∧ DipHyp 200 ∧ OnePointHyps 200 :=
  cen_of L200_ok H200_ok I200_ok link200 cenlink200

/-! ### `N = 201` -/

def pL201 : Prm := ⟨61, 29, 29, 203, 11, 18446744073709551616, 582722304149154215, 582722304149154215⟩
def pH201 : Prm := ⟨61, 29, 29, 203, 11, 18446744073709551616, 582757488521243047, 582757488521243047⟩
def pI201 : Prm := ⟨55, 26, 26, 203, 11, 18446744073709551616, 582722304149154215, 582757488521243047⟩
theorem L201_fin : (prmOK pL201 201 && ptTest pL201 (runFrom pL201 (fmask pL201) (cmask pL201) (hmask pL201) 1 200 (true, (init pL201), (init pL201))) 201 101 false) = true := by
  decide +kernel
theorem L201_ok : RunOK pL201 201 (runFrom pL201 (fmask pL201) (cmask pL201) (hmask pL201) 1 200 (true, (init pL201), (init pL201))) ∧ ptTest pL201 (runFrom pL201 (fmask pL201) (cmask pL201) (hmask pL201) 1 200 (true, (init pL201), (init pL201))) 201 101 false = true :=
  fin_run (runOK_init (prmOK_of_and L201_fin) true) (by decide) rfl L201_fin ptTest_fst
theorem H201_fin : (prmOK pH201 201 && ptTest pH201 (runFrom pH201 (fmask pH201) (cmask pH201) (hmask pH201) 1 200 (true, (init pH201), (init pH201))) 201 101 true) = true := by
  decide +kernel
theorem H201_ok : RunOK pH201 201 (runFrom pH201 (fmask pH201) (cmask pH201) (hmask pH201) 1 200 (true, (init pH201), (init pH201))) ∧ ptTest pH201 (runFrom pH201 (fmask pH201) (cmask pH201) (hmask pH201) 1 200 (true, (init pH201), (init pH201))) 201 101 true = true :=
  fin_run (runOK_init (prmOK_of_and H201_fin) true) (by decide) rfl H201_fin ptTest_fst
theorem I201_fin : (prmOK pI201 201 && intTest pI201 (runFrom pI201 (fmask pI201) (cmask pI201) (hmask pI201) 1 200 (true, (init pI201), (init pI201))) 201 10 false) = true := by
  decide +kernel
theorem I201_ok : RunOK pI201 201 (runFrom pI201 (fmask pI201) (cmask pI201) (hmask pI201) 1 200 (true, (init pI201), (init pI201))) ∧ intTest pI201 (runFrom pI201 (fmask pI201) (cmask pI201) (hmask pI201) 1 200 (true, (init pI201), (init pI201))) 201 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I201_fin) true) (by decide) rfl I201_fin intTest_fst
theorem link201 : linkOK pL201 pH201 pI201 = true := by decide +kernel
theorem cvx201 : ConvexBetweenHumps 201 :=
  cvx_of L201_ok H201_ok I201_ok link201 (by decide)

/-! ### `N = 202` -/

def pL202 : Prm := ⟨61, 29, 29, 204, 11, 18446744073709551616, 580677497180673767, 580677497180673767⟩
def pH202 : Prm := ⟨61, 29, 29, 204, 11, 18446744073709551616, 580712681552762599, 580712681552762599⟩
def pI202 : Prm := ⟨54, 26, 25, 204, 11, 18446744073709551616, 580677497180673767, 580712681552762599⟩
theorem L202_fin : (prmOK pL202 202 && ptTest pL202 (runFrom pL202 (fmask pL202) (cmask pL202) (hmask pL202) 1 201 (true, (init pL202), (init pL202))) 202 101 false) = true := by
  decide +kernel
theorem L202_ok : RunOK pL202 202 (runFrom pL202 (fmask pL202) (cmask pL202) (hmask pL202) 1 201 (true, (init pL202), (init pL202))) ∧ ptTest pL202 (runFrom pL202 (fmask pL202) (cmask pL202) (hmask pL202) 1 201 (true, (init pL202), (init pL202))) 202 101 false = true :=
  fin_run (runOK_init (prmOK_of_and L202_fin) true) (by decide) rfl L202_fin ptTest_fst
theorem H202_fin : (prmOK pH202 202 && ptTest pH202 (runFrom pH202 (fmask pH202) (cmask pH202) (hmask pH202) 1 201 (true, (init pH202), (init pH202))) 202 101 true) = true := by
  decide +kernel
theorem H202_ok : RunOK pH202 202 (runFrom pH202 (fmask pH202) (cmask pH202) (hmask pH202) 1 201 (true, (init pH202), (init pH202))) ∧ ptTest pH202 (runFrom pH202 (fmask pH202) (cmask pH202) (hmask pH202) 1 201 (true, (init pH202), (init pH202))) 202 101 true = true :=
  fin_run (runOK_init (prmOK_of_and H202_fin) true) (by decide) rfl H202_fin ptTest_fst
theorem I202_fin : (prmOK pI202 202 && intTest pI202 (runFrom pI202 (fmask pI202) (cmask pI202) (hmask pI202) 1 201 (true, (init pI202), (init pI202))) 202 10 true) = true := by
  decide +kernel
theorem I202_ok : RunOK pI202 202 (runFrom pI202 (fmask pI202) (cmask pI202) (hmask pI202) 1 201 (true, (init pI202), (init pI202))) ∧ intTest pI202 (runFrom pI202 (fmask pI202) (cmask pI202) (hmask pI202) 1 201 (true, (init pI202), (init pI202))) 202 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I202_fin) true) (by decide) rfl I202_fin intTest_fst
theorem link202 : linkOK pL202 pH202 pI202 = true := by decide +kernel
theorem cvx202 : ConvexBetweenHumps 202 :=
  cvx_of L202_ok H202_ok I202_ok link202 (by decide)
theorem cenlink202 : cenLinkOK pI202 202 = true := by decide +kernel
theorem cen202 : CenterUniqueMin 202 ∧ DipHyp 202 ∧ OnePointHyps 202 :=
  cen_of L202_ok H202_ok I202_ok link202 cenlink202

/-! ### `N = 203` -/

def pL203 : Prm := ⟨61, 29, 29, 205, 11, 18446744073709551616, 578634240671602699, 578634240671602699⟩
def pH203 : Prm := ⟨61, 29, 29, 205, 11, 18446744073709551616, 578669425043691531, 578669425043691531⟩
def pI203 : Prm := ⟨55, 26, 26, 205, 11, 18446744073709551616, 578634240671602699, 578669425043691531⟩
theorem L203_fin : (prmOK pL203 203 && ptTest pL203 (runFrom pL203 (fmask pL203) (cmask pL203) (hmask pL203) 1 202 (true, (init pL203), (init pL203))) 203 102 false) = true := by
  decide +kernel
theorem L203_ok : RunOK pL203 203 (runFrom pL203 (fmask pL203) (cmask pL203) (hmask pL203) 1 202 (true, (init pL203), (init pL203))) ∧ ptTest pL203 (runFrom pL203 (fmask pL203) (cmask pL203) (hmask pL203) 1 202 (true, (init pL203), (init pL203))) 203 102 false = true :=
  fin_run (runOK_init (prmOK_of_and L203_fin) true) (by decide) rfl L203_fin ptTest_fst
theorem H203_fin : (prmOK pH203 203 && ptTest pH203 (runFrom pH203 (fmask pH203) (cmask pH203) (hmask pH203) 1 202 (true, (init pH203), (init pH203))) 203 102 true) = true := by
  decide +kernel
theorem H203_ok : RunOK pH203 203 (runFrom pH203 (fmask pH203) (cmask pH203) (hmask pH203) 1 202 (true, (init pH203), (init pH203))) ∧ ptTest pH203 (runFrom pH203 (fmask pH203) (cmask pH203) (hmask pH203) 1 202 (true, (init pH203), (init pH203))) 203 102 true = true :=
  fin_run (runOK_init (prmOK_of_and H203_fin) true) (by decide) rfl H203_fin ptTest_fst
theorem I203_fin : (prmOK pI203 203 && intTest pI203 (runFrom pI203 (fmask pI203) (cmask pI203) (hmask pI203) 1 202 (true, (init pI203), (init pI203))) 203 10 false) = true := by
  decide +kernel
theorem I203_ok : RunOK pI203 203 (runFrom pI203 (fmask pI203) (cmask pI203) (hmask pI203) 1 202 (true, (init pI203), (init pI203))) ∧ intTest pI203 (runFrom pI203 (fmask pI203) (cmask pI203) (hmask pI203) 1 202 (true, (init pI203), (init pI203))) 203 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I203_fin) true) (by decide) rfl I203_fin intTest_fst
theorem link203 : linkOK pL203 pH203 pI203 = true := by decide +kernel
theorem cvx203 : ConvexBetweenHumps 203 :=
  cvx_of L203_ok H203_ok I203_ok link203 (by decide)

/-! ### `N = 204` -/

def pL204 : Prm := ⟨61, 29, 29, 206, 11, 18446744073709551616, 576621656093527457, 576621656093527457⟩
def pH204 : Prm := ⟨61, 29, 29, 206, 11, 18446744073709551616, 576656840465616289, 576656840465616289⟩
def pI204 : Prm := ⟨55, 26, 26, 206, 11, 18446744073709551616, 576621656093527457, 576656840465616289⟩
theorem L204_fin : (prmOK pL204 204 && ptTest pL204 (runFrom pL204 (fmask pL204) (cmask pL204) (hmask pL204) 1 203 (true, (init pL204), (init pL204))) 204 102 false) = true := by
  decide +kernel
theorem L204_ok : RunOK pL204 204 (runFrom pL204 (fmask pL204) (cmask pL204) (hmask pL204) 1 203 (true, (init pL204), (init pL204))) ∧ ptTest pL204 (runFrom pL204 (fmask pL204) (cmask pL204) (hmask pL204) 1 203 (true, (init pL204), (init pL204))) 204 102 false = true :=
  fin_run (runOK_init (prmOK_of_and L204_fin) true) (by decide) rfl L204_fin ptTest_fst
theorem H204_fin : (prmOK pH204 204 && ptTest pH204 (runFrom pH204 (fmask pH204) (cmask pH204) (hmask pH204) 1 203 (true, (init pH204), (init pH204))) 204 102 true) = true := by
  decide +kernel
theorem H204_ok : RunOK pH204 204 (runFrom pH204 (fmask pH204) (cmask pH204) (hmask pH204) 1 203 (true, (init pH204), (init pH204))) ∧ ptTest pH204 (runFrom pH204 (fmask pH204) (cmask pH204) (hmask pH204) 1 203 (true, (init pH204), (init pH204))) 204 102 true = true :=
  fin_run (runOK_init (prmOK_of_and H204_fin) true) (by decide) rfl H204_fin ptTest_fst
theorem I204_fin : (prmOK pI204 204 && intTest pI204 (runFrom pI204 (fmask pI204) (cmask pI204) (hmask pI204) 1 203 (true, (init pI204), (init pI204))) 204 10 true) = true := by
  decide +kernel
theorem I204_ok : RunOK pI204 204 (runFrom pI204 (fmask pI204) (cmask pI204) (hmask pI204) 1 203 (true, (init pI204), (init pI204))) ∧ intTest pI204 (runFrom pI204 (fmask pI204) (cmask pI204) (hmask pI204) 1 203 (true, (init pI204), (init pI204))) 204 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I204_fin) true) (by decide) rfl I204_fin intTest_fst
theorem link204 : linkOK pL204 pH204 pI204 = true := by decide +kernel
theorem cvx204 : ConvexBetweenHumps 204 :=
  cvx_of L204_ok H204_ok I204_ok link204 (by decide)
theorem cenlink204 : cenLinkOK pI204 204 = true := by decide +kernel
theorem cen204 : CenterUniqueMin 204 ∧ DipHyp 204 ∧ OnePointHyps 204 :=
  cen_of L204_ok H204_ok I204_ok link204 cenlink204

/-! ### `N = 205` -/

def pL205 : Prm := ⟨61, 29, 29, 207, 11, 18446744073709551616, 574610642774414088, 574610642774414088⟩
def pH205 : Prm := ⟨61, 29, 29, 207, 11, 18446744073709551616, 574645827146502920, 574645827146502920⟩
def pI205 : Prm := ⟨55, 26, 26, 207, 11, 18446744073709551616, 574610642774414088, 574645827146502920⟩
theorem L205_fin : (prmOK pL205 205 && ptTest pL205 (runFrom pL205 (fmask pL205) (cmask pL205) (hmask pL205) 1 204 (true, (init pL205), (init pL205))) 205 103 false) = true := by
  decide +kernel
theorem L205_ok : RunOK pL205 205 (runFrom pL205 (fmask pL205) (cmask pL205) (hmask pL205) 1 204 (true, (init pL205), (init pL205))) ∧ ptTest pL205 (runFrom pL205 (fmask pL205) (cmask pL205) (hmask pL205) 1 204 (true, (init pL205), (init pL205))) 205 103 false = true :=
  fin_run (runOK_init (prmOK_of_and L205_fin) true) (by decide) rfl L205_fin ptTest_fst
theorem H205_fin : (prmOK pH205 205 && ptTest pH205 (runFrom pH205 (fmask pH205) (cmask pH205) (hmask pH205) 1 204 (true, (init pH205), (init pH205))) 205 103 true) = true := by
  decide +kernel
theorem H205_ok : RunOK pH205 205 (runFrom pH205 (fmask pH205) (cmask pH205) (hmask pH205) 1 204 (true, (init pH205), (init pH205))) ∧ ptTest pH205 (runFrom pH205 (fmask pH205) (cmask pH205) (hmask pH205) 1 204 (true, (init pH205), (init pH205))) 205 103 true = true :=
  fin_run (runOK_init (prmOK_of_and H205_fin) true) (by decide) rfl H205_fin ptTest_fst
theorem I205_fin : (prmOK pI205 205 && intTest pI205 (runFrom pI205 (fmask pI205) (cmask pI205) (hmask pI205) 1 204 (true, (init pI205), (init pI205))) 205 10 false) = true := by
  decide +kernel
theorem I205_ok : RunOK pI205 205 (runFrom pI205 (fmask pI205) (cmask pI205) (hmask pI205) 1 204 (true, (init pI205), (init pI205))) ∧ intTest pI205 (runFrom pI205 (fmask pI205) (cmask pI205) (hmask pI205) 1 204 (true, (init pI205), (init pI205))) 205 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I205_fin) true) (by decide) rfl I205_fin intTest_fst
theorem link205 : linkOK pL205 pH205 pI205 = true := by decide +kernel
theorem cvx205 : ConvexBetweenHumps 205 :=
  cvx_of L205_ok H205_ok I205_ok link205 (by decide)

/-! ### `N = 206` -/

def pL206 : Prm := ⟨61, 29, 29, 208, 11, 18446744073709551616, 572629486421041518, 572629486421041518⟩
def pH206 : Prm := ⟨61, 29, 29, 208, 11, 18446744073709551616, 572664670793130350, 572664670793130350⟩
def pI206 : Prm := ⟨55, 26, 26, 208, 11, 18446744073709551616, 572629486421041518, 572664670793130350⟩
theorem L206_fin : (prmOK pL206 206 && ptTest pL206 (runFrom pL206 (fmask pL206) (cmask pL206) (hmask pL206) 1 205 (true, (init pL206), (init pL206))) 206 103 false) = true := by
  decide +kernel
theorem L206_ok : RunOK pL206 206 (runFrom pL206 (fmask pL206) (cmask pL206) (hmask pL206) 1 205 (true, (init pL206), (init pL206))) ∧ ptTest pL206 (runFrom pL206 (fmask pL206) (cmask pL206) (hmask pL206) 1 205 (true, (init pL206), (init pL206))) 206 103 false = true :=
  fin_run (runOK_init (prmOK_of_and L206_fin) true) (by decide) rfl L206_fin ptTest_fst
theorem H206_fin : (prmOK pH206 206 && ptTest pH206 (runFrom pH206 (fmask pH206) (cmask pH206) (hmask pH206) 1 205 (true, (init pH206), (init pH206))) 206 103 true) = true := by
  decide +kernel
theorem H206_ok : RunOK pH206 206 (runFrom pH206 (fmask pH206) (cmask pH206) (hmask pH206) 1 205 (true, (init pH206), (init pH206))) ∧ ptTest pH206 (runFrom pH206 (fmask pH206) (cmask pH206) (hmask pH206) 1 205 (true, (init pH206), (init pH206))) 206 103 true = true :=
  fin_run (runOK_init (prmOK_of_and H206_fin) true) (by decide) rfl H206_fin ptTest_fst
theorem I206_fin : (prmOK pI206 206 && intTest pI206 (runFrom pI206 (fmask pI206) (cmask pI206) (hmask pI206) 1 205 (true, (init pI206), (init pI206))) 206 10 true) = true := by
  decide +kernel
theorem I206_ok : RunOK pI206 206 (runFrom pI206 (fmask pI206) (cmask pI206) (hmask pI206) 1 205 (true, (init pI206), (init pI206))) ∧ intTest pI206 (runFrom pI206 (fmask pI206) (cmask pI206) (hmask pI206) 1 205 (true, (init pI206), (init pI206))) 206 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I206_fin) true) (by decide) rfl I206_fin intTest_fst
theorem link206 : linkOK pL206 pH206 pI206 = true := by decide +kernel
theorem cvx206 : ConvexBetweenHumps 206 :=
  cvx_of L206_ok H206_ok I206_ok link206 (by decide)
theorem cenlink206 : cenLinkOK pI206 206 = true := by decide +kernel
theorem cen206 : CenterUniqueMin 206 ∧ DipHyp 206 ∧ OnePointHyps 206 :=
  cen_of L206_ok H206_ok I206_ok link206 cenlink206

/-! ### `N = 207` -/

def pL207 : Prm := ⟨63, 30, 30, 209, 11, 18446744073709551616, 570658715863132029, 570658715863132029⟩
def pH207 : Prm := ⟨63, 30, 30, 209, 11, 18446744073709551616, 570676308049176445, 570676308049176445⟩
def pI207 : Prm := ⟨54, 26, 25, 209, 11, 18446744073709551616, 570658715863132029, 570676308049176445⟩
theorem L207_fin : (prmOK pL207 207 && ptTest pL207 (runFrom pL207 (fmask pL207) (cmask pL207) (hmask pL207) 1 206 (true, (init pL207), (init pL207))) 207 104 false) = true := by
  decide +kernel
theorem L207_ok : RunOK pL207 207 (runFrom pL207 (fmask pL207) (cmask pL207) (hmask pL207) 1 206 (true, (init pL207), (init pL207))) ∧ ptTest pL207 (runFrom pL207 (fmask pL207) (cmask pL207) (hmask pL207) 1 206 (true, (init pL207), (init pL207))) 207 104 false = true :=
  fin_run (runOK_init (prmOK_of_and L207_fin) true) (by decide) rfl L207_fin ptTest_fst
theorem H207_fin : (prmOK pH207 207 && ptTest pH207 (runFrom pH207 (fmask pH207) (cmask pH207) (hmask pH207) 1 206 (true, (init pH207), (init pH207))) 207 104 true) = true := by
  decide +kernel
theorem H207_ok : RunOK pH207 207 (runFrom pH207 (fmask pH207) (cmask pH207) (hmask pH207) 1 206 (true, (init pH207), (init pH207))) ∧ ptTest pH207 (runFrom pH207 (fmask pH207) (cmask pH207) (hmask pH207) 1 206 (true, (init pH207), (init pH207))) 207 104 true = true :=
  fin_run (runOK_init (prmOK_of_and H207_fin) true) (by decide) rfl H207_fin ptTest_fst
theorem I207_fin : (prmOK pI207 207 && intTest pI207 (runFrom pI207 (fmask pI207) (cmask pI207) (hmask pI207) 1 206 (true, (init pI207), (init pI207))) 207 10 false) = true := by
  decide +kernel
theorem I207_ok : RunOK pI207 207 (runFrom pI207 (fmask pI207) (cmask pI207) (hmask pI207) 1 206 (true, (init pI207), (init pI207))) ∧ intTest pI207 (runFrom pI207 (fmask pI207) (cmask pI207) (hmask pI207) 1 206 (true, (init pI207), (init pI207))) 207 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I207_fin) true) (by decide) rfl I207_fin intTest_fst
theorem link207 : linkOK pL207 pH207 pI207 = true := by decide +kernel
theorem cvx207 : ConvexBetweenHumps 207 :=
  cvx_of L207_ok H207_ok I207_ok link207 (by decide)

/-! ### `N = 208` -/

def pL208 : Prm := ⟨63, 30, 30, 210, 11, 18446744073709551616, 568708220195546311, 568708220195546311⟩
def pH208 : Prm := ⟨63, 30, 30, 210, 11, 18446744073709551616, 568725812381590727, 568725812381590727⟩
def pI208 : Prm := ⟨54, 26, 25, 210, 11, 18446744073709551616, 568708220195546311, 568725812381590727⟩
theorem L208_fin : (prmOK pL208 208 && ptTest pL208 (runFrom pL208 (fmask pL208) (cmask pL208) (hmask pL208) 1 207 (true, (init pL208), (init pL208))) 208 104 false) = true := by
  decide +kernel
theorem L208_ok : RunOK pL208 208 (runFrom pL208 (fmask pL208) (cmask pL208) (hmask pL208) 1 207 (true, (init pL208), (init pL208))) ∧ ptTest pL208 (runFrom pL208 (fmask pL208) (cmask pL208) (hmask pL208) 1 207 (true, (init pL208), (init pL208))) 208 104 false = true :=
  fin_run (runOK_init (prmOK_of_and L208_fin) true) (by decide) rfl L208_fin ptTest_fst
theorem H208_fin : (prmOK pH208 208 && ptTest pH208 (runFrom pH208 (fmask pH208) (cmask pH208) (hmask pH208) 1 207 (true, (init pH208), (init pH208))) 208 104 true) = true := by
  decide +kernel
theorem H208_ok : RunOK pH208 208 (runFrom pH208 (fmask pH208) (cmask pH208) (hmask pH208) 1 207 (true, (init pH208), (init pH208))) ∧ ptTest pH208 (runFrom pH208 (fmask pH208) (cmask pH208) (hmask pH208) 1 207 (true, (init pH208), (init pH208))) 208 104 true = true :=
  fin_run (runOK_init (prmOK_of_and H208_fin) true) (by decide) rfl H208_fin ptTest_fst
theorem I208_fin : (prmOK pI208 208 && intTest pI208 (runFrom pI208 (fmask pI208) (cmask pI208) (hmask pI208) 1 207 (true, (init pI208), (init pI208))) 208 10 true) = true := by
  decide +kernel
theorem I208_ok : RunOK pI208 208 (runFrom pI208 (fmask pI208) (cmask pI208) (hmask pI208) 1 207 (true, (init pI208), (init pI208))) ∧ intTest pI208 (runFrom pI208 (fmask pI208) (cmask pI208) (hmask pI208) 1 207 (true, (init pI208), (init pI208))) 208 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I208_fin) true) (by decide) rfl I208_fin intTest_fst
theorem link208 : linkOK pL208 pH208 pI208 = true := by decide +kernel
theorem cvx208 : ConvexBetweenHumps 208 :=
  cvx_of L208_ok H208_ok I208_ok link208 (by decide)
theorem cenlink208 : cenLinkOK pI208 208 = true := by decide +kernel
theorem cen208 : CenterUniqueMin 208 ∧ DipHyp 208 ∧ OnePointHyps 208 :=
  cen_of L208_ok H208_ok I208_ok link208 cenlink208

/-! ### `N = 209` -/

def pL209 : Prm := ⟨63, 30, 30, 211, 11, 18446744073709551616, 566759330476227610, 566759330476227610⟩
def pH209 : Prm := ⟨63, 30, 30, 211, 11, 18446744073709551616, 566776922662272026, 566776922662272026⟩
def pI209 : Prm := ⟨54, 26, 25, 211, 11, 18446744073709551616, 566759330476227610, 566776922662272026⟩
theorem L209_fin : (prmOK pL209 209 && ptTest pL209 (runFrom pL209 (fmask pL209) (cmask pL209) (hmask pL209) 1 208 (true, (init pL209), (init pL209))) 209 105 false) = true := by
  decide +kernel
theorem L209_ok : RunOK pL209 209 (runFrom pL209 (fmask pL209) (cmask pL209) (hmask pL209) 1 208 (true, (init pL209), (init pL209))) ∧ ptTest pL209 (runFrom pL209 (fmask pL209) (cmask pL209) (hmask pL209) 1 208 (true, (init pL209), (init pL209))) 209 105 false = true :=
  fin_run (runOK_init (prmOK_of_and L209_fin) true) (by decide) rfl L209_fin ptTest_fst
theorem H209_fin : (prmOK pH209 209 && ptTest pH209 (runFrom pH209 (fmask pH209) (cmask pH209) (hmask pH209) 1 208 (true, (init pH209), (init pH209))) 209 105 true) = true := by
  decide +kernel
theorem H209_ok : RunOK pH209 209 (runFrom pH209 (fmask pH209) (cmask pH209) (hmask pH209) 1 208 (true, (init pH209), (init pH209))) ∧ ptTest pH209 (runFrom pH209 (fmask pH209) (cmask pH209) (hmask pH209) 1 208 (true, (init pH209), (init pH209))) 209 105 true = true :=
  fin_run (runOK_init (prmOK_of_and H209_fin) true) (by decide) rfl H209_fin ptTest_fst
theorem I209_fin : (prmOK pI209 209 && intTest pI209 (runFrom pI209 (fmask pI209) (cmask pI209) (hmask pI209) 1 208 (true, (init pI209), (init pI209))) 209 10 false) = true := by
  decide +kernel
theorem I209_ok : RunOK pI209 209 (runFrom pI209 (fmask pI209) (cmask pI209) (hmask pI209) 1 208 (true, (init pI209), (init pI209))) ∧ intTest pI209 (runFrom pI209 (fmask pI209) (cmask pI209) (hmask pI209) 1 208 (true, (init pI209), (init pI209))) 209 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I209_fin) true) (by decide) rfl I209_fin intTest_fst
theorem link209 : linkOK pL209 pH209 pI209 = true := by decide +kernel
theorem cvx209 : ConvexBetweenHumps 209 :=
  cvx_of L209_ok H209_ok I209_ok link209 (by decide)

/-! ### `N = 210` -/

def pL210 : Prm := ⟨63, 30, 30, 212, 11, 18446744073709551616, 564838753454668617, 564838753454668617⟩
def pH210 : Prm := ⟨63, 30, 30, 212, 11, 18446744073709551616, 564856345640713033, 564856345640713033⟩
def pI210 : Prm := ⟨54, 26, 25, 212, 11, 18446744073709551616, 564838753454668617, 564856345640713033⟩
theorem L210_fin : (prmOK pL210 210 && ptTest pL210 (runFrom pL210 (fmask pL210) (cmask pL210) (hmask pL210) 1 209 (true, (init pL210), (init pL210))) 210 105 false) = true := by
  decide +kernel
theorem L210_ok : RunOK pL210 210 (runFrom pL210 (fmask pL210) (cmask pL210) (hmask pL210) 1 209 (true, (init pL210), (init pL210))) ∧ ptTest pL210 (runFrom pL210 (fmask pL210) (cmask pL210) (hmask pL210) 1 209 (true, (init pL210), (init pL210))) 210 105 false = true :=
  fin_run (runOK_init (prmOK_of_and L210_fin) true) (by decide) rfl L210_fin ptTest_fst
theorem H210_fin : (prmOK pH210 210 && ptTest pH210 (runFrom pH210 (fmask pH210) (cmask pH210) (hmask pH210) 1 209 (true, (init pH210), (init pH210))) 210 105 true) = true := by
  decide +kernel
theorem H210_ok : RunOK pH210 210 (runFrom pH210 (fmask pH210) (cmask pH210) (hmask pH210) 1 209 (true, (init pH210), (init pH210))) ∧ ptTest pH210 (runFrom pH210 (fmask pH210) (cmask pH210) (hmask pH210) 1 209 (true, (init pH210), (init pH210))) 210 105 true = true :=
  fin_run (runOK_init (prmOK_of_and H210_fin) true) (by decide) rfl H210_fin ptTest_fst
theorem I210_fin : (prmOK pI210 210 && intTest pI210 (runFrom pI210 (fmask pI210) (cmask pI210) (hmask pI210) 1 209 (true, (init pI210), (init pI210))) 210 10 true) = true := by
  decide +kernel
theorem I210_ok : RunOK pI210 210 (runFrom pI210 (fmask pI210) (cmask pI210) (hmask pI210) 1 209 (true, (init pI210), (init pI210))) ∧ intTest pI210 (runFrom pI210 (fmask pI210) (cmask pI210) (hmask pI210) 1 209 (true, (init pI210), (init pI210))) 210 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I210_fin) true) (by decide) rfl I210_fin intTest_fst
theorem link210 : linkOK pL210 pH210 pI210 = true := by decide +kernel
theorem cvx210 : ConvexBetweenHumps 210 :=
  cvx_of L210_ok H210_ok I210_ok link210 (by decide)
theorem cenlink210 : cenLinkOK pI210 210 = true := by decide +kernel
theorem cen210 : CenterUniqueMin 210 ∧ DipHyp 210 ∧ OnePointHyps 210 :=
  cen_of L210_ok H210_ok I210_ok link210 cenlink210

/-! ### `N = 211` -/

def pL211 : Prm := ⟨64, 31, 30, 213, 11, 18446744073709551616, 562919796577474371, 562919796577474371⟩
def pH211 : Prm := ⟨63, 30, 30, 213, 11, 18446744073709551616, 562937388763518787, 562937388763518787⟩
def pI211 : Prm := ⟨54, 26, 25, 213, 11, 18446744073709551616, 562919796577474371, 562937388763518787⟩
theorem L211_fin : (prmOK pL211 211 && ptTest pL211 (runFrom pL211 (fmask pL211) (cmask pL211) (hmask pL211) 1 210 (true, (init pL211), (init pL211))) 211 106 false) = true := by
  decide +kernel
theorem L211_ok : RunOK pL211 211 (runFrom pL211 (fmask pL211) (cmask pL211) (hmask pL211) 1 210 (true, (init pL211), (init pL211))) ∧ ptTest pL211 (runFrom pL211 (fmask pL211) (cmask pL211) (hmask pL211) 1 210 (true, (init pL211), (init pL211))) 211 106 false = true :=
  fin_run (runOK_init (prmOK_of_and L211_fin) true) (by decide) rfl L211_fin ptTest_fst
theorem H211_fin : (prmOK pH211 211 && ptTest pH211 (runFrom pH211 (fmask pH211) (cmask pH211) (hmask pH211) 1 210 (true, (init pH211), (init pH211))) 211 106 true) = true := by
  decide +kernel
theorem H211_ok : RunOK pH211 211 (runFrom pH211 (fmask pH211) (cmask pH211) (hmask pH211) 1 210 (true, (init pH211), (init pH211))) ∧ ptTest pH211 (runFrom pH211 (fmask pH211) (cmask pH211) (hmask pH211) 1 210 (true, (init pH211), (init pH211))) 211 106 true = true :=
  fin_run (runOK_init (prmOK_of_and H211_fin) true) (by decide) rfl H211_fin ptTest_fst
theorem I211_fin : (prmOK pI211 211 && intTest pI211 (runFrom pI211 (fmask pI211) (cmask pI211) (hmask pI211) 1 210 (true, (init pI211), (init pI211))) 211 10 false) = true := by
  decide +kernel
theorem I211_ok : RunOK pI211 211 (runFrom pI211 (fmask pI211) (cmask pI211) (hmask pI211) 1 210 (true, (init pI211), (init pI211))) ∧ intTest pI211 (runFrom pI211 (fmask pI211) (cmask pI211) (hmask pI211) 1 210 (true, (init pI211), (init pI211))) 211 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I211_fin) true) (by decide) rfl I211_fin intTest_fst
theorem link211 : linkOK pL211 pH211 pI211 = true := by decide +kernel
theorem cvx211 : ConvexBetweenHumps 211 :=
  cvx_of L211_ok H211_ok I211_ok link211 (by decide)

/-! ### `N = 212` -/

def pL212 : Prm := ⟨64, 31, 30, 214, 11, 18446744073709551616, 561028420591389621, 561028420591389621⟩
def pH212 : Prm := ⟨63, 30, 30, 214, 11, 18446744073709551616, 561046012777434037, 561046012777434037⟩
def pI212 : Prm := ⟨54, 26, 25, 214, 11, 18446744073709551616, 561028420591389621, 561046012777434037⟩
theorem L212_fin : (prmOK pL212 212 && ptTest pL212 (runFrom pL212 (fmask pL212) (cmask pL212) (hmask pL212) 1 211 (true, (init pL212), (init pL212))) 212 106 false) = true := by
  decide +kernel
theorem L212_ok : RunOK pL212 212 (runFrom pL212 (fmask pL212) (cmask pL212) (hmask pL212) 1 211 (true, (init pL212), (init pL212))) ∧ ptTest pL212 (runFrom pL212 (fmask pL212) (cmask pL212) (hmask pL212) 1 211 (true, (init pL212), (init pL212))) 212 106 false = true :=
  fin_run (runOK_init (prmOK_of_and L212_fin) true) (by decide) rfl L212_fin ptTest_fst
theorem H212_fin : (prmOK pH212 212 && ptTest pH212 (runFrom pH212 (fmask pH212) (cmask pH212) (hmask pH212) 1 211 (true, (init pH212), (init pH212))) 212 106 true) = true := by
  decide +kernel
theorem H212_ok : RunOK pH212 212 (runFrom pH212 (fmask pH212) (cmask pH212) (hmask pH212) 1 211 (true, (init pH212), (init pH212))) ∧ ptTest pH212 (runFrom pH212 (fmask pH212) (cmask pH212) (hmask pH212) 1 211 (true, (init pH212), (init pH212))) 212 106 true = true :=
  fin_run (runOK_init (prmOK_of_and H212_fin) true) (by decide) rfl H212_fin ptTest_fst
theorem I212_fin : (prmOK pI212 212 && intTest pI212 (runFrom pI212 (fmask pI212) (cmask pI212) (hmask pI212) 1 211 (true, (init pI212), (init pI212))) 212 10 true) = true := by
  decide +kernel
theorem I212_ok : RunOK pI212 212 (runFrom pI212 (fmask pI212) (cmask pI212) (hmask pI212) 1 211 (true, (init pI212), (init pI212))) ∧ intTest pI212 (runFrom pI212 (fmask pI212) (cmask pI212) (hmask pI212) 1 211 (true, (init pI212), (init pI212))) 212 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I212_fin) true) (by decide) rfl I212_fin intTest_fst
theorem link212 : linkOK pL212 pH212 pI212 = true := by decide +kernel
theorem cvx212 : ConvexBetweenHumps 212 :=
  cvx_of L212_ok H212_ok I212_ok link212 (by decide)
theorem cenlink212 : cenLinkOK pI212 212 = true := by decide +kernel
theorem cen212 : CenterUniqueMin 212 ∧ DipHyp 212 ∧ OnePointHyps 212 :=
  cen_of L212_ok H212_ok I212_ok link212 cenlink212

/-! ### `N = 213` -/

def pL213 : Prm := ⟨63, 30, 30, 215, 11, 18446744073709551616, 559138677034057473, 559138677034057473⟩
def pH213 : Prm := ⟨64, 31, 30, 215, 11, 18446744073709551616, 559156269220101889, 559156269220101889⟩
def pI213 : Prm := ⟨54, 26, 25, 215, 11, 18446744073709551616, 559138677034057473, 559156269220101889⟩
theorem L213_fin : (prmOK pL213 213 && ptTest pL213 (runFrom pL213 (fmask pL213) (cmask pL213) (hmask pL213) 1 212 (true, (init pL213), (init pL213))) 213 107 false) = true := by
  decide +kernel
theorem L213_ok : RunOK pL213 213 (runFrom pL213 (fmask pL213) (cmask pL213) (hmask pL213) 1 212 (true, (init pL213), (init pL213))) ∧ ptTest pL213 (runFrom pL213 (fmask pL213) (cmask pL213) (hmask pL213) 1 212 (true, (init pL213), (init pL213))) 213 107 false = true :=
  fin_run (runOK_init (prmOK_of_and L213_fin) true) (by decide) rfl L213_fin ptTest_fst
theorem H213_fin : (prmOK pH213 213 && ptTest pH213 (runFrom pH213 (fmask pH213) (cmask pH213) (hmask pH213) 1 212 (true, (init pH213), (init pH213))) 213 107 true) = true := by
  decide +kernel
theorem H213_ok : RunOK pH213 213 (runFrom pH213 (fmask pH213) (cmask pH213) (hmask pH213) 1 212 (true, (init pH213), (init pH213))) ∧ ptTest pH213 (runFrom pH213 (fmask pH213) (cmask pH213) (hmask pH213) 1 212 (true, (init pH213), (init pH213))) 213 107 true = true :=
  fin_run (runOK_init (prmOK_of_and H213_fin) true) (by decide) rfl H213_fin ptTest_fst
theorem I213_fin : (prmOK pI213 213 && intTest pI213 (runFrom pI213 (fmask pI213) (cmask pI213) (hmask pI213) 1 212 (true, (init pI213), (init pI213))) 213 10 false) = true := by
  decide +kernel
theorem I213_ok : RunOK pI213 213 (runFrom pI213 (fmask pI213) (cmask pI213) (hmask pI213) 1 212 (true, (init pI213), (init pI213))) ∧ intTest pI213 (runFrom pI213 (fmask pI213) (cmask pI213) (hmask pI213) 1 212 (true, (init pI213), (init pI213))) 213 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I213_fin) true) (by decide) rfl I213_fin intTest_fst
theorem link213 : linkOK pL213 pH213 pI213 = true := by decide +kernel
theorem cvx213 : ConvexBetweenHumps 213 :=
  cvx_of L213_ok H213_ok I213_ok link213 (by decide)

/-! ### `N = 214` -/

def pL214 : Prm := ⟨64, 31, 30, 216, 11, 18446744073709551616, 557275807886276824, 557275807886276824⟩
def pH214 : Prm := ⟨64, 31, 30, 216, 11, 18446744073709551616, 557293400072321240, 557293400072321240⟩
def pI214 : Prm := ⟨54, 26, 25, 216, 11, 18446744073709551616, 557275807886276824, 557293400072321240⟩
theorem L214_fin : (prmOK pL214 214 && ptTest pL214 (runFrom pL214 (fmask pL214) (cmask pL214) (hmask pL214) 1 213 (true, (init pL214), (init pL214))) 214 107 false) = true := by
  decide +kernel
theorem L214_ok : RunOK pL214 214 (runFrom pL214 (fmask pL214) (cmask pL214) (hmask pL214) 1 213 (true, (init pL214), (init pL214))) ∧ ptTest pL214 (runFrom pL214 (fmask pL214) (cmask pL214) (hmask pL214) 1 213 (true, (init pL214), (init pL214))) 214 107 false = true :=
  fin_run (runOK_init (prmOK_of_and L214_fin) true) (by decide) rfl L214_fin ptTest_fst
theorem H214_fin : (prmOK pH214 214 && ptTest pH214 (runFrom pH214 (fmask pH214) (cmask pH214) (hmask pH214) 1 213 (true, (init pH214), (init pH214))) 214 107 true) = true := by
  decide +kernel
theorem H214_ok : RunOK pH214 214 (runFrom pH214 (fmask pH214) (cmask pH214) (hmask pH214) 1 213 (true, (init pH214), (init pH214))) ∧ ptTest pH214 (runFrom pH214 (fmask pH214) (cmask pH214) (hmask pH214) 1 213 (true, (init pH214), (init pH214))) 214 107 true = true :=
  fin_run (runOK_init (prmOK_of_and H214_fin) true) (by decide) rfl H214_fin ptTest_fst
theorem I214_fin : (prmOK pI214 214 && intTest pI214 (runFrom pI214 (fmask pI214) (cmask pI214) (hmask pI214) 1 213 (true, (init pI214), (init pI214))) 214 10 true) = true := by
  decide +kernel
theorem I214_ok : RunOK pI214 214 (runFrom pI214 (fmask pI214) (cmask pI214) (hmask pI214) 1 213 (true, (init pI214), (init pI214))) ∧ intTest pI214 (runFrom pI214 (fmask pI214) (cmask pI214) (hmask pI214) 1 213 (true, (init pI214), (init pI214))) 214 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I214_fin) true) (by decide) rfl I214_fin intTest_fst
theorem link214 : linkOK pL214 pH214 pI214 = true := by decide +kernel
theorem cvx214 : ConvexBetweenHumps 214 :=
  cvx_of L214_ok H214_ok I214_ok link214 (by decide)
theorem cenlink214 : cenLinkOK pI214 214 = true := by decide +kernel
theorem cen214 : CenterUniqueMin 214 ∧ DipHyp 214 ∧ OnePointHyps 214 :=
  cen_of L214_ok H214_ok I214_ok link214 cenlink214

/-! ### `N = 215` -/

def pL215 : Prm := ⟨64, 31, 30, 217, 11, 18446744073709551616, 555414581668851052, 555414581668851052⟩
def pH215 : Prm := ⟨64, 31, 30, 217, 11, 18446744073709551616, 555432173854895468, 555432173854895468⟩
def pI215 : Prm := ⟨54, 26, 25, 217, 11, 18446744073709551616, 555414581668851052, 555432173854895468⟩
theorem L215_fin : (prmOK pL215 215 && ptTest pL215 (runFrom pL215 (fmask pL215) (cmask pL215) (hmask pL215) 1 214 (true, (init pL215), (init pL215))) 215 108 false) = true := by
  decide +kernel
theorem L215_ok : RunOK pL215 215 (runFrom pL215 (fmask pL215) (cmask pL215) (hmask pL215) 1 214 (true, (init pL215), (init pL215))) ∧ ptTest pL215 (runFrom pL215 (fmask pL215) (cmask pL215) (hmask pL215) 1 214 (true, (init pL215), (init pL215))) 215 108 false = true :=
  fin_run (runOK_init (prmOK_of_and L215_fin) true) (by decide) rfl L215_fin ptTest_fst
theorem H215_fin : (prmOK pH215 215 && ptTest pH215 (runFrom pH215 (fmask pH215) (cmask pH215) (hmask pH215) 1 214 (true, (init pH215), (init pH215))) 215 108 true) = true := by
  decide +kernel
theorem H215_ok : RunOK pH215 215 (runFrom pH215 (fmask pH215) (cmask pH215) (hmask pH215) 1 214 (true, (init pH215), (init pH215))) ∧ ptTest pH215 (runFrom pH215 (fmask pH215) (cmask pH215) (hmask pH215) 1 214 (true, (init pH215), (init pH215))) 215 108 true = true :=
  fin_run (runOK_init (prmOK_of_and H215_fin) true) (by decide) rfl H215_fin ptTest_fst
theorem I215_fin : (prmOK pI215 215 && intTest pI215 (runFrom pI215 (fmask pI215) (cmask pI215) (hmask pI215) 1 214 (true, (init pI215), (init pI215))) 215 10 false) = true := by
  decide +kernel
theorem I215_ok : RunOK pI215 215 (runFrom pI215 (fmask pI215) (cmask pI215) (hmask pI215) 1 214 (true, (init pI215), (init pI215))) ∧ intTest pI215 (runFrom pI215 (fmask pI215) (cmask pI215) (hmask pI215) 1 214 (true, (init pI215), (init pI215))) 215 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I215_fin) true) (by decide) rfl I215_fin intTest_fst
theorem link215 : linkOK pL215 pH215 pI215 = true := by decide +kernel
theorem cvx215 : ConvexBetweenHumps 215 :=
  cvx_of L215_ok H215_ok I215_ok link215 (by decide)

/-! ### `N = 216` -/

def pL216 : Prm := ⟨64, 31, 30, 218, 11, 18446744073709551616, 553579547610674416, 553579547610674416⟩
def pH216 : Prm := ⟨64, 31, 30, 218, 11, 18446744073709551616, 553597139796718832, 553597139796718832⟩
def pI216 : Prm := ⟨54, 26, 25, 218, 11, 18446744073709551616, 553579547610674416, 553597139796718832⟩
theorem L216_fin : (prmOK pL216 216 && ptTest pL216 (runFrom pL216 (fmask pL216) (cmask pL216) (hmask pL216) 1 215 (true, (init pL216), (init pL216))) 216 108 false) = true := by
  decide +kernel
theorem L216_ok : RunOK pL216 216 (runFrom pL216 (fmask pL216) (cmask pL216) (hmask pL216) 1 215 (true, (init pL216), (init pL216))) ∧ ptTest pL216 (runFrom pL216 (fmask pL216) (cmask pL216) (hmask pL216) 1 215 (true, (init pL216), (init pL216))) 216 108 false = true :=
  fin_run (runOK_init (prmOK_of_and L216_fin) true) (by decide) rfl L216_fin ptTest_fst
theorem H216_fin : (prmOK pH216 216 && ptTest pH216 (runFrom pH216 (fmask pH216) (cmask pH216) (hmask pH216) 1 215 (true, (init pH216), (init pH216))) 216 108 true) = true := by
  decide +kernel
theorem H216_ok : RunOK pH216 216 (runFrom pH216 (fmask pH216) (cmask pH216) (hmask pH216) 1 215 (true, (init pH216), (init pH216))) ∧ ptTest pH216 (runFrom pH216 (fmask pH216) (cmask pH216) (hmask pH216) 1 215 (true, (init pH216), (init pH216))) 216 108 true = true :=
  fin_run (runOK_init (prmOK_of_and H216_fin) true) (by decide) rfl H216_fin ptTest_fst
theorem I216_fin : (prmOK pI216 216 && intTest pI216 (runFrom pI216 (fmask pI216) (cmask pI216) (hmask pI216) 1 215 (true, (init pI216), (init pI216))) 216 10 true) = true := by
  decide +kernel
theorem I216_ok : RunOK pI216 216 (runFrom pI216 (fmask pI216) (cmask pI216) (hmask pI216) 1 215 (true, (init pI216), (init pI216))) ∧ intTest pI216 (runFrom pI216 (fmask pI216) (cmask pI216) (hmask pI216) 1 215 (true, (init pI216), (init pI216))) 216 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I216_fin) true) (by decide) rfl I216_fin intTest_fst
theorem link216 : linkOK pL216 pH216 pI216 = true := by decide +kernel
theorem cvx216 : ConvexBetweenHumps 216 :=
  cvx_of L216_ok H216_ok I216_ok link216 (by decide)
theorem cenlink216 : cenLinkOK pI216 216 = true := by decide +kernel
theorem cen216 : CenterUniqueMin 216 ∧ DipHyp 216 ∧ OnePointHyps 216 :=
  cen_of L216_ok H216_ok I216_ok link216 cenlink216

/-! ### `N = 217` -/

def pL217 : Prm := ⟨64, 31, 30, 219, 11, 18446744073709551616, 551746165322089696, 551746165322089696⟩
def pH217 : Prm := ⟨64, 31, 30, 219, 11, 18446744073709551616, 551763757508134112, 551763757508134112⟩
def pI217 : Prm := ⟨54, 26, 25, 219, 11, 18446744073709551616, 551746165322089696, 551763757508134112⟩
theorem L217_fin : (prmOK pL217 217 && ptTest pL217 (runFrom pL217 (fmask pL217) (cmask pL217) (hmask pL217) 1 216 (true, (init pL217), (init pL217))) 217 109 false) = true := by
  decide +kernel
theorem L217_ok : RunOK pL217 217 (runFrom pL217 (fmask pL217) (cmask pL217) (hmask pL217) 1 216 (true, (init pL217), (init pL217))) ∧ ptTest pL217 (runFrom pL217 (fmask pL217) (cmask pL217) (hmask pL217) 1 216 (true, (init pL217), (init pL217))) 217 109 false = true :=
  fin_run (runOK_init (prmOK_of_and L217_fin) true) (by decide) rfl L217_fin ptTest_fst
theorem H217_fin : (prmOK pH217 217 && ptTest pH217 (runFrom pH217 (fmask pH217) (cmask pH217) (hmask pH217) 1 216 (true, (init pH217), (init pH217))) 217 109 true) = true := by
  decide +kernel
theorem H217_ok : RunOK pH217 217 (runFrom pH217 (fmask pH217) (cmask pH217) (hmask pH217) 1 216 (true, (init pH217), (init pH217))) ∧ ptTest pH217 (runFrom pH217 (fmask pH217) (cmask pH217) (hmask pH217) 1 216 (true, (init pH217), (init pH217))) 217 109 true = true :=
  fin_run (runOK_init (prmOK_of_and H217_fin) true) (by decide) rfl H217_fin ptTest_fst
theorem I217_fin : (prmOK pI217 217 && intTest pI217 (runFrom pI217 (fmask pI217) (cmask pI217) (hmask pI217) 1 216 (true, (init pI217), (init pI217))) 217 10 false) = true := by
  decide +kernel
theorem I217_ok : RunOK pI217 217 (runFrom pI217 (fmask pI217) (cmask pI217) (hmask pI217) 1 216 (true, (init pI217), (init pI217))) ∧ intTest pI217 (runFrom pI217 (fmask pI217) (cmask pI217) (hmask pI217) 1 216 (true, (init pI217), (init pI217))) 217 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I217_fin) true) (by decide) rfl I217_fin intTest_fst
theorem link217 : linkOK pL217 pH217 pI217 = true := by decide +kernel
theorem cvx217 : ConvexBetweenHumps 217 :=
  cvx_of L217_ok H217_ok I217_ok link217 (by decide)

/-! ### `N = 218` -/

def pL218 : Prm := ⟨64, 31, 30, 220, 11, 18446744073709551616, 549938316136373177, 549938316136373177⟩
def pH218 : Prm := ⟨64, 31, 30, 220, 11, 18446744073709551616, 549955908322417593, 549955908322417593⟩
def pI218 : Prm := ⟨54, 26, 25, 220, 11, 18446744073709551616, 549938316136373177, 549955908322417593⟩
theorem L218_fin : (prmOK pL218 218 && ptTest pL218 (runFrom pL218 (fmask pL218) (cmask pL218) (hmask pL218) 1 217 (true, (init pL218), (init pL218))) 218 109 false) = true := by
  decide +kernel
theorem L218_ok : RunOK pL218 218 (runFrom pL218 (fmask pL218) (cmask pL218) (hmask pL218) 1 217 (true, (init pL218), (init pL218))) ∧ ptTest pL218 (runFrom pL218 (fmask pL218) (cmask pL218) (hmask pL218) 1 217 (true, (init pL218), (init pL218))) 218 109 false = true :=
  fin_run (runOK_init (prmOK_of_and L218_fin) true) (by decide) rfl L218_fin ptTest_fst
theorem H218_fin : (prmOK pH218 218 && ptTest pH218 (runFrom pH218 (fmask pH218) (cmask pH218) (hmask pH218) 1 217 (true, (init pH218), (init pH218))) 218 109 true) = true := by
  decide +kernel
theorem H218_ok : RunOK pH218 218 (runFrom pH218 (fmask pH218) (cmask pH218) (hmask pH218) 1 217 (true, (init pH218), (init pH218))) ∧ ptTest pH218 (runFrom pH218 (fmask pH218) (cmask pH218) (hmask pH218) 1 217 (true, (init pH218), (init pH218))) 218 109 true = true :=
  fin_run (runOK_init (prmOK_of_and H218_fin) true) (by decide) rfl H218_fin ptTest_fst
theorem I218_fin : (prmOK pI218 218 && intTest pI218 (runFrom pI218 (fmask pI218) (cmask pI218) (hmask pI218) 1 217 (true, (init pI218), (init pI218))) 218 10 true) = true := by
  decide +kernel
theorem I218_ok : RunOK pI218 218 (runFrom pI218 (fmask pI218) (cmask pI218) (hmask pI218) 1 217 (true, (init pI218), (init pI218))) ∧ intTest pI218 (runFrom pI218 (fmask pI218) (cmask pI218) (hmask pI218) 1 217 (true, (init pI218), (init pI218))) 218 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I218_fin) true) (by decide) rfl I218_fin intTest_fst
theorem link218 : linkOK pL218 pH218 pI218 = true := by decide +kernel
theorem cvx218 : ConvexBetweenHumps 218 :=
  cvx_of L218_ok H218_ok I218_ok link218 (by decide)
theorem cenlink218 : cenLinkOK pI218 218 = true := by decide +kernel
theorem cen218 : CenterUniqueMin 218 ∧ DipHyp 218 ∧ OnePointHyps 218 :=
  cen_of L218_ok H218_ok I218_ok link218 cenlink218

/-! ### `N = 219` -/

def pL219 : Prm := ⟨64, 31, 30, 221, 11, 18446744073709551616, 548132126009737748, 548132126009737748⟩
def pH219 : Prm := ⟨64, 31, 30, 221, 11, 18446744073709551616, 548149718195782164, 548149718195782164⟩
def pI219 : Prm := ⟨55, 26, 26, 221, 11, 18446744073709551616, 548132126009737748, 548149718195782164⟩
theorem L219_fin : (prmOK pL219 219 && ptTest pL219 (runFrom pL219 (fmask pL219) (cmask pL219) (hmask pL219) 1 218 (true, (init pL219), (init pL219))) 219 110 false) = true := by
  decide +kernel
theorem L219_ok : RunOK pL219 219 (runFrom pL219 (fmask pL219) (cmask pL219) (hmask pL219) 1 218 (true, (init pL219), (init pL219))) ∧ ptTest pL219 (runFrom pL219 (fmask pL219) (cmask pL219) (hmask pL219) 1 218 (true, (init pL219), (init pL219))) 219 110 false = true :=
  fin_run (runOK_init (prmOK_of_and L219_fin) true) (by decide) rfl L219_fin ptTest_fst
theorem H219_fin : (prmOK pH219 219 && ptTest pH219 (runFrom pH219 (fmask pH219) (cmask pH219) (hmask pH219) 1 218 (true, (init pH219), (init pH219))) 219 110 true) = true := by
  decide +kernel
theorem H219_ok : RunOK pH219 219 (runFrom pH219 (fmask pH219) (cmask pH219) (hmask pH219) 1 218 (true, (init pH219), (init pH219))) ∧ ptTest pH219 (runFrom pH219 (fmask pH219) (cmask pH219) (hmask pH219) 1 218 (true, (init pH219), (init pH219))) 219 110 true = true :=
  fin_run (runOK_init (prmOK_of_and H219_fin) true) (by decide) rfl H219_fin ptTest_fst
theorem I219_fin : (prmOK pI219 219 && intTest pI219 (runFrom pI219 (fmask pI219) (cmask pI219) (hmask pI219) 1 218 (true, (init pI219), (init pI219))) 219 10 false) = true := by
  decide +kernel
theorem I219_ok : RunOK pI219 219 (runFrom pI219 (fmask pI219) (cmask pI219) (hmask pI219) 1 218 (true, (init pI219), (init pI219))) ∧ intTest pI219 (runFrom pI219 (fmask pI219) (cmask pI219) (hmask pI219) 1 218 (true, (init pI219), (init pI219))) 219 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I219_fin) true) (by decide) rfl I219_fin intTest_fst
theorem link219 : linkOK pL219 pH219 pI219 = true := by decide +kernel
theorem cvx219 : ConvexBetweenHumps 219 :=
  cvx_of L219_ok H219_ok I219_ok link219 (by decide)

/-! ### `N = 220` -/

def pL220 : Prm := ⟨64, 31, 30, 222, 11, 18446744073709551616, 546350832139192750, 546350832139192750⟩
def pH220 : Prm := ⟨64, 31, 30, 222, 11, 18446744073709551616, 546368424325237166, 546368424325237166⟩
def pI220 : Prm := ⟨55, 26, 26, 222, 11, 18446744073709551616, 546350832139192750, 546368424325237166⟩
theorem L220_fin : (prmOK pL220 220 && ptTest pL220 (runFrom pL220 (fmask pL220) (cmask pL220) (hmask pL220) 1 219 (true, (init pL220), (init pL220))) 220 110 false) = true := by
  decide +kernel
theorem L220_ok : RunOK pL220 220 (runFrom pL220 (fmask pL220) (cmask pL220) (hmask pL220) 1 219 (true, (init pL220), (init pL220))) ∧ ptTest pL220 (runFrom pL220 (fmask pL220) (cmask pL220) (hmask pL220) 1 219 (true, (init pL220), (init pL220))) 220 110 false = true :=
  fin_run (runOK_init (prmOK_of_and L220_fin) true) (by decide) rfl L220_fin ptTest_fst
theorem H220_fin : (prmOK pH220 220 && ptTest pH220 (runFrom pH220 (fmask pH220) (cmask pH220) (hmask pH220) 1 219 (true, (init pH220), (init pH220))) 220 110 true) = true := by
  decide +kernel
theorem H220_ok : RunOK pH220 220 (runFrom pH220 (fmask pH220) (cmask pH220) (hmask pH220) 1 219 (true, (init pH220), (init pH220))) ∧ ptTest pH220 (runFrom pH220 (fmask pH220) (cmask pH220) (hmask pH220) 1 219 (true, (init pH220), (init pH220))) 220 110 true = true :=
  fin_run (runOK_init (prmOK_of_and H220_fin) true) (by decide) rfl H220_fin ptTest_fst
theorem I220_fin : (prmOK pI220 220 && intTest pI220 (runFrom pI220 (fmask pI220) (cmask pI220) (hmask pI220) 1 219 (true, (init pI220), (init pI220))) 220 10 true) = true := by
  decide +kernel
theorem I220_ok : RunOK pI220 220 (runFrom pI220 (fmask pI220) (cmask pI220) (hmask pI220) 1 219 (true, (init pI220), (init pI220))) ∧ intTest pI220 (runFrom pI220 (fmask pI220) (cmask pI220) (hmask pI220) 1 219 (true, (init pI220), (init pI220))) 220 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I220_fin) true) (by decide) rfl I220_fin intTest_fst
theorem link220 : linkOK pL220 pH220 pI220 = true := by decide +kernel
theorem cvx220 : ConvexBetweenHumps 220 :=
  cvx_of L220_ok H220_ok I220_ok link220 (by decide)
theorem cenlink220 : cenLinkOK pI220 220 = true := by decide +kernel
theorem cen220 : CenterUniqueMin 220 ∧ DipHyp 220 ∧ OnePointHyps 220 :=
  cen_of L220_ok H220_ok I220_ok link220 cenlink220

/-! ### `N = 221` -/

def pL221 : Prm := ⟨64, 31, 30, 223, 11, 18446744073709551616, 544571203172598148, 544571203172598148⟩
def pH221 : Prm := ⟨64, 31, 30, 223, 11, 18446744073709551616, 544588795358642564, 544588795358642564⟩
def pI221 : Prm := ⟨55, 26, 26, 223, 11, 18446744073709551616, 544571203172598148, 544588795358642564⟩
theorem L221_fin : (prmOK pL221 221 && ptTest pL221 (runFrom pL221 (fmask pL221) (cmask pL221) (hmask pL221) 1 220 (true, (init pL221), (init pL221))) 221 111 false) = true := by
  decide +kernel
theorem L221_ok : RunOK pL221 221 (runFrom pL221 (fmask pL221) (cmask pL221) (hmask pL221) 1 220 (true, (init pL221), (init pL221))) ∧ ptTest pL221 (runFrom pL221 (fmask pL221) (cmask pL221) (hmask pL221) 1 220 (true, (init pL221), (init pL221))) 221 111 false = true :=
  fin_run (runOK_init (prmOK_of_and L221_fin) true) (by decide) rfl L221_fin ptTest_fst
theorem H221_fin : (prmOK pH221 221 && ptTest pH221 (runFrom pH221 (fmask pH221) (cmask pH221) (hmask pH221) 1 220 (true, (init pH221), (init pH221))) 221 111 true) = true := by
  decide +kernel
theorem H221_ok : RunOK pH221 221 (runFrom pH221 (fmask pH221) (cmask pH221) (hmask pH221) 1 220 (true, (init pH221), (init pH221))) ∧ ptTest pH221 (runFrom pH221 (fmask pH221) (cmask pH221) (hmask pH221) 1 220 (true, (init pH221), (init pH221))) 221 111 true = true :=
  fin_run (runOK_init (prmOK_of_and H221_fin) true) (by decide) rfl H221_fin ptTest_fst
theorem I221_fin : (prmOK pI221 221 && intTest pI221 (runFrom pI221 (fmask pI221) (cmask pI221) (hmask pI221) 1 220 (true, (init pI221), (init pI221))) 221 10 false) = true := by
  decide +kernel
theorem I221_ok : RunOK pI221 221 (runFrom pI221 (fmask pI221) (cmask pI221) (hmask pI221) 1 220 (true, (init pI221), (init pI221))) ∧ intTest pI221 (runFrom pI221 (fmask pI221) (cmask pI221) (hmask pI221) 1 220 (true, (init pI221), (init pI221))) 221 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I221_fin) true) (by decide) rfl I221_fin intTest_fst
theorem link221 : linkOK pL221 pH221 pI221 = true := by decide +kernel
theorem cvx221 : ConvexBetweenHumps 221 :=
  cvx_of L221_ok H221_ok I221_ok link221 (by decide)

/-! ### `N = 222` -/

def pL222 : Prm := ⟨64, 31, 30, 224, 11, 18446744073709551616, 542815854890554889, 542815854890554889⟩
def pH222 : Prm := ⟨64, 31, 30, 224, 11, 18446744073709551616, 542833447076599305, 542833447076599305⟩
def pI222 : Prm := ⟨55, 26, 26, 224, 11, 18446744073709551616, 542815854890554889, 542833447076599305⟩
theorem L222_fin : (prmOK pL222 222 && ptTest pL222 (runFrom pL222 (fmask pL222) (cmask pL222) (hmask pL222) 1 221 (true, (init pL222), (init pL222))) 222 111 false) = true := by
  decide +kernel
theorem L222_ok : RunOK pL222 222 (runFrom pL222 (fmask pL222) (cmask pL222) (hmask pL222) 1 221 (true, (init pL222), (init pL222))) ∧ ptTest pL222 (runFrom pL222 (fmask pL222) (cmask pL222) (hmask pL222) 1 221 (true, (init pL222), (init pL222))) 222 111 false = true :=
  fin_run (runOK_init (prmOK_of_and L222_fin) true) (by decide) rfl L222_fin ptTest_fst
theorem H222_fin : (prmOK pH222 222 && ptTest pH222 (runFrom pH222 (fmask pH222) (cmask pH222) (hmask pH222) 1 221 (true, (init pH222), (init pH222))) 222 111 true) = true := by
  decide +kernel
theorem H222_ok : RunOK pH222 222 (runFrom pH222 (fmask pH222) (cmask pH222) (hmask pH222) 1 221 (true, (init pH222), (init pH222))) ∧ ptTest pH222 (runFrom pH222 (fmask pH222) (cmask pH222) (hmask pH222) 1 221 (true, (init pH222), (init pH222))) 222 111 true = true :=
  fin_run (runOK_init (prmOK_of_and H222_fin) true) (by decide) rfl H222_fin ptTest_fst
theorem I222_fin : (prmOK pI222 222 && intTest pI222 (runFrom pI222 (fmask pI222) (cmask pI222) (hmask pI222) 1 221 (true, (init pI222), (init pI222))) 222 10 true) = true := by
  decide +kernel
theorem I222_ok : RunOK pI222 222 (runFrom pI222 (fmask pI222) (cmask pI222) (hmask pI222) 1 221 (true, (init pI222), (init pI222))) ∧ intTest pI222 (runFrom pI222 (fmask pI222) (cmask pI222) (hmask pI222) 1 221 (true, (init pI222), (init pI222))) 222 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I222_fin) true) (by decide) rfl I222_fin intTest_fst
theorem link222 : linkOK pL222 pH222 pI222 = true := by decide +kernel
theorem cvx222 : ConvexBetweenHumps 222 :=
  cvx_of L222_ok H222_ok I222_ok link222 (by decide)
theorem cenlink222 : cenLinkOK pI222 222 = true := by decide +kernel
theorem cen222 : CenterUniqueMin 222 ∧ DipHyp 222 ∧ OnePointHyps 222 :=
  cen_of L222_ok H222_ok I222_ok link222 cenlink222

/-! ### `N = 223` -/

def pL223 : Prm := ⟨64, 31, 30, 225, 11, 18446744073709551616, 541062176011161737, 541062176011161737⟩
def pH223 : Prm := ⟨64, 31, 30, 225, 11, 18446744073709551616, 541079768197206153, 541079768197206153⟩
def pI223 : Prm := ⟨55, 26, 26, 225, 11, 18446744073709551616, 541062176011161737, 541079768197206153⟩
theorem L223_fin : (prmOK pL223 223 && ptTest pL223 (runFrom pL223 (fmask pL223) (cmask pL223) (hmask pL223) 1 222 (true, (init pL223), (init pL223))) 223 112 false) = true := by
  decide +kernel
theorem L223_ok : RunOK pL223 223 (runFrom pL223 (fmask pL223) (cmask pL223) (hmask pL223) 1 222 (true, (init pL223), (init pL223))) ∧ ptTest pL223 (runFrom pL223 (fmask pL223) (cmask pL223) (hmask pL223) 1 222 (true, (init pL223), (init pL223))) 223 112 false = true :=
  fin_run (runOK_init (prmOK_of_and L223_fin) true) (by decide) rfl L223_fin ptTest_fst
theorem H223_fin : (prmOK pH223 223 && ptTest pH223 (runFrom pH223 (fmask pH223) (cmask pH223) (hmask pH223) 1 222 (true, (init pH223), (init pH223))) 223 112 true) = true := by
  decide +kernel
theorem H223_ok : RunOK pH223 223 (runFrom pH223 (fmask pH223) (cmask pH223) (hmask pH223) 1 222 (true, (init pH223), (init pH223))) ∧ ptTest pH223 (runFrom pH223 (fmask pH223) (cmask pH223) (hmask pH223) 1 222 (true, (init pH223), (init pH223))) 223 112 true = true :=
  fin_run (runOK_init (prmOK_of_and H223_fin) true) (by decide) rfl H223_fin ptTest_fst
theorem I223_fin : (prmOK pI223 223 && intTest pI223 (runFrom pI223 (fmask pI223) (cmask pI223) (hmask pI223) 1 222 (true, (init pI223), (init pI223))) 223 10 false) = true := by
  decide +kernel
theorem I223_ok : RunOK pI223 223 (runFrom pI223 (fmask pI223) (cmask pI223) (hmask pI223) 1 222 (true, (init pI223), (init pI223))) ∧ intTest pI223 (runFrom pI223 (fmask pI223) (cmask pI223) (hmask pI223) 1 222 (true, (init pI223), (init pI223))) 223 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I223_fin) true) (by decide) rfl I223_fin intTest_fst
theorem link223 : linkOK pL223 pH223 pI223 = true := by decide +kernel
theorem cvx223 : ConvexBetweenHumps 223 :=
  cvx_of L223_ok H223_ok I223_ok link223 (by decide)

/-! ### `N = 224` -/

def pL224 : Prm := ⟨64, 31, 30, 226, 11, 18446744073709551616, 539332182632620451, 539332182632620451⟩
def pH224 : Prm := ⟨64, 31, 30, 226, 11, 18446744073709551616, 539349774818664867, 539349774818664867⟩
def pI224 : Prm := ⟨55, 26, 26, 226, 11, 18446744073709551616, 539332182632620451, 539349774818664867⟩
theorem L224_fin : (prmOK pL224 224 && ptTest pL224 (runFrom pL224 (fmask pL224) (cmask pL224) (hmask pL224) 1 223 (true, (init pL224), (init pL224))) 224 112 false) = true := by
  decide +kernel
theorem L224_ok : RunOK pL224 224 (runFrom pL224 (fmask pL224) (cmask pL224) (hmask pL224) 1 223 (true, (init pL224), (init pL224))) ∧ ptTest pL224 (runFrom pL224 (fmask pL224) (cmask pL224) (hmask pL224) 1 223 (true, (init pL224), (init pL224))) 224 112 false = true :=
  fin_run (runOK_init (prmOK_of_and L224_fin) true) (by decide) rfl L224_fin ptTest_fst
theorem H224_fin : (prmOK pH224 224 && ptTest pH224 (runFrom pH224 (fmask pH224) (cmask pH224) (hmask pH224) 1 223 (true, (init pH224), (init pH224))) 224 112 true) = true := by
  decide +kernel
theorem H224_ok : RunOK pH224 224 (runFrom pH224 (fmask pH224) (cmask pH224) (hmask pH224) 1 223 (true, (init pH224), (init pH224))) ∧ ptTest pH224 (runFrom pH224 (fmask pH224) (cmask pH224) (hmask pH224) 1 223 (true, (init pH224), (init pH224))) 224 112 true = true :=
  fin_run (runOK_init (prmOK_of_and H224_fin) true) (by decide) rfl H224_fin ptTest_fst
theorem I224_fin : (prmOK pI224 224 && intTest pI224 (runFrom pI224 (fmask pI224) (cmask pI224) (hmask pI224) 1 223 (true, (init pI224), (init pI224))) 224 10 true) = true := by
  decide +kernel
theorem I224_ok : RunOK pI224 224 (runFrom pI224 (fmask pI224) (cmask pI224) (hmask pI224) 1 223 (true, (init pI224), (init pI224))) ∧ intTest pI224 (runFrom pI224 (fmask pI224) (cmask pI224) (hmask pI224) 1 223 (true, (init pI224), (init pI224))) 224 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I224_fin) true) (by decide) rfl I224_fin intTest_fst
theorem link224 : linkOK pL224 pH224 pI224 = true := by decide +kernel
theorem cvx224 : ConvexBetweenHumps 224 :=
  cvx_of L224_ok H224_ok I224_ok link224 (by decide)
theorem cenlink224 : cenLinkOK pI224 224 = true := by decide +kernel
theorem cen224 : CenterUniqueMin 224 ∧ DipHyp 224 ∧ OnePointHyps 224 :=
  cen_of L224_ok H224_ok I224_ok link224 cenlink224

/-! ### `N = 225` -/

def pL225 : Prm := ⟨64, 31, 30, 227, 11, 18446744073709551616, 537603861901179514, 537603861901179514⟩
def pH225 : Prm := ⟨64, 31, 30, 227, 11, 18446744073709551616, 537621454087223930, 537621454087223930⟩
def pI225 : Prm := ⟨55, 26, 26, 227, 11, 18446744073709551616, 537603861901179514, 537621454087223930⟩
theorem L225_fin : (prmOK pL225 225 && ptTest pL225 (runFrom pL225 (fmask pL225) (cmask pL225) (hmask pL225) 1 224 (true, (init pL225), (init pL225))) 225 113 false) = true := by
  decide +kernel
theorem L225_ok : RunOK pL225 225 (runFrom pL225 (fmask pL225) (cmask pL225) (hmask pL225) 1 224 (true, (init pL225), (init pL225))) ∧ ptTest pL225 (runFrom pL225 (fmask pL225) (cmask pL225) (hmask pL225) 1 224 (true, (init pL225), (init pL225))) 225 113 false = true :=
  fin_run (runOK_init (prmOK_of_and L225_fin) true) (by decide) rfl L225_fin ptTest_fst
theorem H225_fin : (prmOK pH225 225 && ptTest pH225 (runFrom pH225 (fmask pH225) (cmask pH225) (hmask pH225) 1 224 (true, (init pH225), (init pH225))) 225 113 true) = true := by
  decide +kernel
theorem H225_ok : RunOK pH225 225 (runFrom pH225 (fmask pH225) (cmask pH225) (hmask pH225) 1 224 (true, (init pH225), (init pH225))) ∧ ptTest pH225 (runFrom pH225 (fmask pH225) (cmask pH225) (hmask pH225) 1 224 (true, (init pH225), (init pH225))) 225 113 true = true :=
  fin_run (runOK_init (prmOK_of_and H225_fin) true) (by decide) rfl H225_fin ptTest_fst
theorem I225_fin : (prmOK pI225 225 && intTest pI225 (runFrom pI225 (fmask pI225) (cmask pI225) (hmask pI225) 1 224 (true, (init pI225), (init pI225))) 225 10 false) = true := by
  decide +kernel
theorem I225_ok : RunOK pI225 225 (runFrom pI225 (fmask pI225) (cmask pI225) (hmask pI225) 1 224 (true, (init pI225), (init pI225))) ∧ intTest pI225 (runFrom pI225 (fmask pI225) (cmask pI225) (hmask pI225) 1 224 (true, (init pI225), (init pI225))) 225 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I225_fin) true) (by decide) rfl I225_fin intTest_fst
theorem link225 : linkOK pL225 pH225 pI225 = true := by decide +kernel
theorem cvx225 : ConvexBetweenHumps 225 :=
  cvx_of L225_ok H225_ok I225_ok link225 (by decide)

/-! ### `N = 226` -/

def pL226 : Prm := ⟨64, 31, 30, 228, 11, 18446744073709551616, 535898651031640588, 535898651031640588⟩
def pH226 : Prm := ⟨64, 31, 30, 228, 11, 18446744073709551616, 535916243217685004, 535916243217685004⟩
def pI226 : Prm := ⟨55, 27, 25, 228, 11, 18446744073709551616, 535898651031640588, 535916243217685004⟩
theorem L226_fin : (prmOK pL226 226 && ptTest pL226 (runFrom pL226 (fmask pL226) (cmask pL226) (hmask pL226) 1 225 (true, (init pL226), (init pL226))) 226 113 false) = true := by
  decide +kernel
theorem L226_ok : RunOK pL226 226 (runFrom pL226 (fmask pL226) (cmask pL226) (hmask pL226) 1 225 (true, (init pL226), (init pL226))) ∧ ptTest pL226 (runFrom pL226 (fmask pL226) (cmask pL226) (hmask pL226) 1 225 (true, (init pL226), (init pL226))) 226 113 false = true :=
  fin_run (runOK_init (prmOK_of_and L226_fin) true) (by decide) rfl L226_fin ptTest_fst
theorem H226_fin : (prmOK pH226 226 && ptTest pH226 (runFrom pH226 (fmask pH226) (cmask pH226) (hmask pH226) 1 225 (true, (init pH226), (init pH226))) 226 113 true) = true := by
  decide +kernel
theorem H226_ok : RunOK pH226 226 (runFrom pH226 (fmask pH226) (cmask pH226) (hmask pH226) 1 225 (true, (init pH226), (init pH226))) ∧ ptTest pH226 (runFrom pH226 (fmask pH226) (cmask pH226) (hmask pH226) 1 225 (true, (init pH226), (init pH226))) 226 113 true = true :=
  fin_run (runOK_init (prmOK_of_and H226_fin) true) (by decide) rfl H226_fin ptTest_fst
theorem I226_fin : (prmOK pI226 226 && intTest pI226 (runFrom pI226 (fmask pI226) (cmask pI226) (hmask pI226) 1 225 (true, (init pI226), (init pI226))) 226 10 true) = true := by
  decide +kernel
theorem I226_ok : RunOK pI226 226 (runFrom pI226 (fmask pI226) (cmask pI226) (hmask pI226) 1 225 (true, (init pI226), (init pI226))) ∧ intTest pI226 (runFrom pI226 (fmask pI226) (cmask pI226) (hmask pI226) 1 225 (true, (init pI226), (init pI226))) 226 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I226_fin) true) (by decide) rfl I226_fin intTest_fst
theorem link226 : linkOK pL226 pH226 pI226 = true := by decide +kernel
theorem cvx226 : ConvexBetweenHumps 226 :=
  cvx_of L226_ok H226_ok I226_ok link226 (by decide)
theorem cenlink226 : cenLinkOK pI226 226 = true := by decide +kernel
theorem cen226 : CenterUniqueMin 226 ∧ DipHyp 226 ∧ OnePointHyps 226 :=
  cen_of L226_ok H226_ok I226_ok link226 cenlink226

/-! ### `N = 227` -/

def pL227 : Prm := ⟨64, 31, 30, 229, 11, 18446744073709551616, 534195114885475290, 534195114885475290⟩
def pH227 : Prm := ⟨64, 31, 30, 229, 11, 18446744073709551616, 534212707071519706, 534212707071519706⟩
def pI227 : Prm := ⟨55, 27, 25, 229, 11, 18446744073709551616, 534195114885475290, 534212707071519706⟩
theorem L227_fin : (prmOK pL227 227 && ptTest pL227 (runFrom pL227 (fmask pL227) (cmask pL227) (hmask pL227) 1 226 (true, (init pL227), (init pL227))) 227 114 false) = true := by
  decide +kernel
theorem L227_ok : RunOK pL227 227 (runFrom pL227 (fmask pL227) (cmask pL227) (hmask pL227) 1 226 (true, (init pL227), (init pL227))) ∧ ptTest pL227 (runFrom pL227 (fmask pL227) (cmask pL227) (hmask pL227) 1 226 (true, (init pL227), (init pL227))) 227 114 false = true :=
  fin_run (runOK_init (prmOK_of_and L227_fin) true) (by decide) rfl L227_fin ptTest_fst
theorem H227_fin : (prmOK pH227 227 && ptTest pH227 (runFrom pH227 (fmask pH227) (cmask pH227) (hmask pH227) 1 226 (true, (init pH227), (init pH227))) 227 114 true) = true := by
  decide +kernel
theorem H227_ok : RunOK pH227 227 (runFrom pH227 (fmask pH227) (cmask pH227) (hmask pH227) 1 226 (true, (init pH227), (init pH227))) ∧ ptTest pH227 (runFrom pH227 (fmask pH227) (cmask pH227) (hmask pH227) 1 226 (true, (init pH227), (init pH227))) 227 114 true = true :=
  fin_run (runOK_init (prmOK_of_and H227_fin) true) (by decide) rfl H227_fin ptTest_fst
theorem I227_fin : (prmOK pI227 227 && intTest pI227 (runFrom pI227 (fmask pI227) (cmask pI227) (hmask pI227) 1 226 (true, (init pI227), (init pI227))) 227 10 false) = true := by
  decide +kernel
theorem I227_ok : RunOK pI227 227 (runFrom pI227 (fmask pI227) (cmask pI227) (hmask pI227) 1 226 (true, (init pI227), (init pI227))) ∧ intTest pI227 (runFrom pI227 (fmask pI227) (cmask pI227) (hmask pI227) 1 226 (true, (init pI227), (init pI227))) 227 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I227_fin) true) (by decide) rfl I227_fin intTest_fst
theorem link227 : linkOK pL227 pH227 pI227 = true := by decide +kernel
theorem cvx227 : ConvexBetweenHumps 227 :=
  cvx_of L227_ok H227_ok I227_ok link227 (by decide)

/-! ### `N = 228` -/

def pL228 : Prm := ⟨64, 31, 30, 230, 11, 18446744073709551616, 532514131705519185, 532514131705519185⟩
def pH228 : Prm := ⟨64, 31, 30, 230, 11, 18446744073709551616, 532531723891563601, 532531723891563601⟩
def pI228 : Prm := ⟨55, 27, 25, 230, 11, 18446744073709551616, 532514131705519185, 532531723891563601⟩
theorem L228_fin : (prmOK pL228 228 && ptTest pL228 (runFrom pL228 (fmask pL228) (cmask pL228) (hmask pL228) 1 227 (true, (init pL228), (init pL228))) 228 114 false) = true := by
  decide +kernel
theorem L228_ok : RunOK pL228 228 (runFrom pL228 (fmask pL228) (cmask pL228) (hmask pL228) 1 227 (true, (init pL228), (init pL228))) ∧ ptTest pL228 (runFrom pL228 (fmask pL228) (cmask pL228) (hmask pL228) 1 227 (true, (init pL228), (init pL228))) 228 114 false = true :=
  fin_run (runOK_init (prmOK_of_and L228_fin) true) (by decide) rfl L228_fin ptTest_fst
theorem H228_fin : (prmOK pH228 228 && ptTest pH228 (runFrom pH228 (fmask pH228) (cmask pH228) (hmask pH228) 1 227 (true, (init pH228), (init pH228))) 228 114 true) = true := by
  decide +kernel
theorem H228_ok : RunOK pH228 228 (runFrom pH228 (fmask pH228) (cmask pH228) (hmask pH228) 1 227 (true, (init pH228), (init pH228))) ∧ ptTest pH228 (runFrom pH228 (fmask pH228) (cmask pH228) (hmask pH228) 1 227 (true, (init pH228), (init pH228))) 228 114 true = true :=
  fin_run (runOK_init (prmOK_of_and H228_fin) true) (by decide) rfl H228_fin ptTest_fst
theorem I228_fin : (prmOK pI228 228 && intTest pI228 (runFrom pI228 (fmask pI228) (cmask pI228) (hmask pI228) 1 227 (true, (init pI228), (init pI228))) 228 10 true) = true := by
  decide +kernel
theorem I228_ok : RunOK pI228 228 (runFrom pI228 (fmask pI228) (cmask pI228) (hmask pI228) 1 227 (true, (init pI228), (init pI228))) ∧ intTest pI228 (runFrom pI228 (fmask pI228) (cmask pI228) (hmask pI228) 1 227 (true, (init pI228), (init pI228))) 228 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I228_fin) true) (by decide) rfl I228_fin intTest_fst
theorem link228 : linkOK pL228 pH228 pI228 = true := by decide +kernel
theorem cvx228 : ConvexBetweenHumps 228 :=
  cvx_of L228_ok H228_ok I228_ok link228 (by decide)
theorem cenlink228 : cenLinkOK pI228 228 = true := by decide +kernel
theorem cen228 : CenterUniqueMin 228 ∧ DipHyp 228 ∧ OnePointHyps 228 :=
  cen_of L228_ok H228_ok I228_ok link228 cenlink228

/-! ### `N = 229` -/

def pL229 : Prm := ⟨64, 31, 30, 231, 11, 18446744073709551616, 530834824237571511, 530834824237571511⟩
def pH229 : Prm := ⟨64, 31, 30, 231, 11, 18446744073709551616, 530852416423615927, 530852416423615927⟩
def pI229 : Prm := ⟨55, 27, 25, 231, 11, 18446744073709551616, 530834824237571511, 530852416423615927⟩
theorem L229_fin : (prmOK pL229 229 && ptTest pL229 (runFrom pL229 (fmask pL229) (cmask pL229) (hmask pL229) 1 228 (true, (init pL229), (init pL229))) 229 115 false) = true := by
  decide +kernel
theorem L229_ok : RunOK pL229 229 (runFrom pL229 (fmask pL229) (cmask pL229) (hmask pL229) 1 228 (true, (init pL229), (init pL229))) ∧ ptTest pL229 (runFrom pL229 (fmask pL229) (cmask pL229) (hmask pL229) 1 228 (true, (init pL229), (init pL229))) 229 115 false = true :=
  fin_run (runOK_init (prmOK_of_and L229_fin) true) (by decide) rfl L229_fin ptTest_fst
theorem H229_fin : (prmOK pH229 229 && ptTest pH229 (runFrom pH229 (fmask pH229) (cmask pH229) (hmask pH229) 1 228 (true, (init pH229), (init pH229))) 229 115 true) = true := by
  decide +kernel
theorem H229_ok : RunOK pH229 229 (runFrom pH229 (fmask pH229) (cmask pH229) (hmask pH229) 1 228 (true, (init pH229), (init pH229))) ∧ ptTest pH229 (runFrom pH229 (fmask pH229) (cmask pH229) (hmask pH229) 1 228 (true, (init pH229), (init pH229))) 229 115 true = true :=
  fin_run (runOK_init (prmOK_of_and H229_fin) true) (by decide) rfl H229_fin ptTest_fst
theorem I229_fin : (prmOK pI229 229 && intTest pI229 (runFrom pI229 (fmask pI229) (cmask pI229) (hmask pI229) 1 228 (true, (init pI229), (init pI229))) 229 10 false) = true := by
  decide +kernel
theorem I229_ok : RunOK pI229 229 (runFrom pI229 (fmask pI229) (cmask pI229) (hmask pI229) 1 228 (true, (init pI229), (init pI229))) ∧ intTest pI229 (runFrom pI229 (fmask pI229) (cmask pI229) (hmask pI229) 1 228 (true, (init pI229), (init pI229))) 229 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I229_fin) true) (by decide) rfl I229_fin intTest_fst
theorem link229 : linkOK pL229 pH229 pI229 = true := by decide +kernel
theorem cvx229 : ConvexBetweenHumps 229 :=
  cvx_of L229_ok H229_ok I229_ok link229 (by decide)

/-! ### `N = 230` -/

def pL230 : Prm := ⟨64, 31, 30, 232, 11, 18446744073709551616, 529177530821251573, 529177530821251573⟩
def pH230 : Prm := ⟨64, 30, 31, 232, 11, 18446744073709551616, 529195123007295989, 529195123007295989⟩
def pI230 : Prm := ⟨55, 27, 25, 232, 11, 18446744073709551616, 529177530821251573, 529195123007295989⟩
theorem L230_fin : (prmOK pL230 230 && ptTest pL230 (runFrom pL230 (fmask pL230) (cmask pL230) (hmask pL230) 1 229 (true, (init pL230), (init pL230))) 230 115 false) = true := by
  decide +kernel
theorem L230_ok : RunOK pL230 230 (runFrom pL230 (fmask pL230) (cmask pL230) (hmask pL230) 1 229 (true, (init pL230), (init pL230))) ∧ ptTest pL230 (runFrom pL230 (fmask pL230) (cmask pL230) (hmask pL230) 1 229 (true, (init pL230), (init pL230))) 230 115 false = true :=
  fin_run (runOK_init (prmOK_of_and L230_fin) true) (by decide) rfl L230_fin ptTest_fst
theorem H230_fin : (prmOK pH230 230 && ptTest pH230 (runFrom pH230 (fmask pH230) (cmask pH230) (hmask pH230) 1 229 (true, (init pH230), (init pH230))) 230 115 true) = true := by
  decide +kernel
theorem H230_ok : RunOK pH230 230 (runFrom pH230 (fmask pH230) (cmask pH230) (hmask pH230) 1 229 (true, (init pH230), (init pH230))) ∧ ptTest pH230 (runFrom pH230 (fmask pH230) (cmask pH230) (hmask pH230) 1 229 (true, (init pH230), (init pH230))) 230 115 true = true :=
  fin_run (runOK_init (prmOK_of_and H230_fin) true) (by decide) rfl H230_fin ptTest_fst
theorem I230_fin : (prmOK pI230 230 && intTest pI230 (runFrom pI230 (fmask pI230) (cmask pI230) (hmask pI230) 1 229 (true, (init pI230), (init pI230))) 230 10 true) = true := by
  decide +kernel
theorem I230_ok : RunOK pI230 230 (runFrom pI230 (fmask pI230) (cmask pI230) (hmask pI230) 1 229 (true, (init pI230), (init pI230))) ∧ intTest pI230 (runFrom pI230 (fmask pI230) (cmask pI230) (hmask pI230) 1 229 (true, (init pI230), (init pI230))) 230 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I230_fin) true) (by decide) rfl I230_fin intTest_fst
theorem link230 : linkOK pL230 pH230 pI230 = true := by decide +kernel
theorem cvx230 : ConvexBetweenHumps 230 :=
  cvx_of L230_ok H230_ok I230_ok link230 (by decide)
theorem cenlink230 : cenLinkOK pI230 230 = true := by decide +kernel
theorem cen230 : CenterUniqueMin 230 ∧ DipHyp 230 ∧ OnePointHyps 230 :=
  cen_of L230_ok H230_ok I230_ok link230 cenlink230

/-! ### `N = 231` -/

def pL231 : Prm := ⟨64, 30, 31, 233, 11, 18446744073709551616, 527521913093254446, 527521913093254446⟩
def pH231 : Prm := ⟨64, 31, 30, 233, 11, 18446744073709551616, 527539505279298862, 527539505279298862⟩
def pI231 : Prm := ⟨55, 27, 25, 233, 11, 18446744073709551616, 527521913093254446, 527539505279298862⟩
theorem L231_fin : (prmOK pL231 231 && ptTest pL231 (runFrom pL231 (fmask pL231) (cmask pL231) (hmask pL231) 1 230 (true, (init pL231), (init pL231))) 231 116 false) = true := by
  decide +kernel
theorem L231_ok : RunOK pL231 231 (runFrom pL231 (fmask pL231) (cmask pL231) (hmask pL231) 1 230 (true, (init pL231), (init pL231))) ∧ ptTest pL231 (runFrom pL231 (fmask pL231) (cmask pL231) (hmask pL231) 1 230 (true, (init pL231), (init pL231))) 231 116 false = true :=
  fin_run (runOK_init (prmOK_of_and L231_fin) true) (by decide) rfl L231_fin ptTest_fst
theorem H231_fin : (prmOK pH231 231 && ptTest pH231 (runFrom pH231 (fmask pH231) (cmask pH231) (hmask pH231) 1 230 (true, (init pH231), (init pH231))) 231 116 true) = true := by
  decide +kernel
theorem H231_ok : RunOK pH231 231 (runFrom pH231 (fmask pH231) (cmask pH231) (hmask pH231) 1 230 (true, (init pH231), (init pH231))) ∧ ptTest pH231 (runFrom pH231 (fmask pH231) (cmask pH231) (hmask pH231) 1 230 (true, (init pH231), (init pH231))) 231 116 true = true :=
  fin_run (runOK_init (prmOK_of_and H231_fin) true) (by decide) rfl H231_fin ptTest_fst
theorem I231_fin : (prmOK pI231 231 && intTest pI231 (runFrom pI231 (fmask pI231) (cmask pI231) (hmask pI231) 1 230 (true, (init pI231), (init pI231))) 231 10 false) = true := by
  decide +kernel
theorem I231_ok : RunOK pI231 231 (runFrom pI231 (fmask pI231) (cmask pI231) (hmask pI231) 1 230 (true, (init pI231), (init pI231))) ∧ intTest pI231 (runFrom pI231 (fmask pI231) (cmask pI231) (hmask pI231) 1 230 (true, (init pI231), (init pI231))) 231 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I231_fin) true) (by decide) rfl I231_fin intTest_fst
theorem link231 : linkOK pL231 pH231 pI231 = true := by decide +kernel
theorem cvx231 : ConvexBetweenHumps 231 :=
  cvx_of L231_ok H231_ok I231_ok link231 (by decide)

/-! ### `N = 232` -/

def pL232 : Prm := ⟨64, 31, 30, 234, 11, 18446744073709551616, 525887787758310342, 525887787758310342⟩
def pH232 : Prm := ⟨64, 31, 30, 234, 11, 18446744073709551616, 525905379944354758, 525905379944354758⟩
def pI232 : Prm := ⟨55, 27, 25, 234, 11, 18446744073709551616, 525887787758310342, 525905379944354758⟩
theorem L232_fin : (prmOK pL232 232 && ptTest pL232 (runFrom pL232 (fmask pL232) (cmask pL232) (hmask pL232) 1 231 (true, (init pL232), (init pL232))) 232 116 false) = true := by
  decide +kernel
theorem L232_ok : RunOK pL232 232 (runFrom pL232 (fmask pL232) (cmask pL232) (hmask pL232) 1 231 (true, (init pL232), (init pL232))) ∧ ptTest pL232 (runFrom pL232 (fmask pL232) (cmask pL232) (hmask pL232) 1 231 (true, (init pL232), (init pL232))) 232 116 false = true :=
  fin_run (runOK_init (prmOK_of_and L232_fin) true) (by decide) rfl L232_fin ptTest_fst
theorem H232_fin : (prmOK pH232 232 && ptTest pH232 (runFrom pH232 (fmask pH232) (cmask pH232) (hmask pH232) 1 231 (true, (init pH232), (init pH232))) 232 116 true) = true := by
  decide +kernel
theorem H232_ok : RunOK pH232 232 (runFrom pH232 (fmask pH232) (cmask pH232) (hmask pH232) 1 231 (true, (init pH232), (init pH232))) ∧ ptTest pH232 (runFrom pH232 (fmask pH232) (cmask pH232) (hmask pH232) 1 231 (true, (init pH232), (init pH232))) 232 116 true = true :=
  fin_run (runOK_init (prmOK_of_and H232_fin) true) (by decide) rfl H232_fin ptTest_fst
theorem I232_fin : (prmOK pI232 232 && intTest pI232 (runFrom pI232 (fmask pI232) (cmask pI232) (hmask pI232) 1 231 (true, (init pI232), (init pI232))) 232 10 true) = true := by
  decide +kernel
theorem I232_ok : RunOK pI232 232 (runFrom pI232 (fmask pI232) (cmask pI232) (hmask pI232) 1 231 (true, (init pI232), (init pI232))) ∧ intTest pI232 (runFrom pI232 (fmask pI232) (cmask pI232) (hmask pI232) 1 231 (true, (init pI232), (init pI232))) 232 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I232_fin) true) (by decide) rfl I232_fin intTest_fst
theorem link232 : linkOK pL232 pH232 pI232 = true := by decide +kernel
theorem cvx232 : ConvexBetweenHumps 232 :=
  cvx_of L232_ok H232_ok I232_ok link232 (by decide)
theorem cenlink232 : cenLinkOK pI232 232 = true := by decide +kernel
theorem cen232 : CenterUniqueMin 232 ∧ DipHyp 232 ∧ OnePointHyps 232 :=
  cen_of L232_ok H232_ok I232_ok link232 cenlink232

/-! ### `N = 233` -/

def pL233 : Prm := ⟨64, 30, 31, 235, 11, 18446744073709551616, 524255337146278698, 524255337146278698⟩
def pH233 : Prm := ⟨63, 29, 31, 235, 11, 18446744073709551616, 524272929332323114, 524272929332323114⟩
def pI233 : Prm := ⟨55, 27, 25, 235, 11, 18446744073709551616, 524255337146278698, 524272929332323114⟩
theorem L233_fin : (prmOK pL233 233 && ptTest pL233 (runFrom pL233 (fmask pL233) (cmask pL233) (hmask pL233) 1 232 (true, (init pL233), (init pL233))) 233 117 false) = true := by
  decide +kernel
theorem L233_ok : RunOK pL233 233 (runFrom pL233 (fmask pL233) (cmask pL233) (hmask pL233) 1 232 (true, (init pL233), (init pL233))) ∧ ptTest pL233 (runFrom pL233 (fmask pL233) (cmask pL233) (hmask pL233) 1 232 (true, (init pL233), (init pL233))) 233 117 false = true :=
  fin_run (runOK_init (prmOK_of_and L233_fin) true) (by decide) rfl L233_fin ptTest_fst
theorem H233_fin : (prmOK pH233 233 && ptTest pH233 (runFrom pH233 (fmask pH233) (cmask pH233) (hmask pH233) 1 232 (true, (init pH233), (init pH233))) 233 117 true) = true := by
  decide +kernel
theorem H233_ok : RunOK pH233 233 (runFrom pH233 (fmask pH233) (cmask pH233) (hmask pH233) 1 232 (true, (init pH233), (init pH233))) ∧ ptTest pH233 (runFrom pH233 (fmask pH233) (cmask pH233) (hmask pH233) 1 232 (true, (init pH233), (init pH233))) 233 117 true = true :=
  fin_run (runOK_init (prmOK_of_and H233_fin) true) (by decide) rfl H233_fin ptTest_fst
theorem I233_fin : (prmOK pI233 233 && intTest pI233 (runFrom pI233 (fmask pI233) (cmask pI233) (hmask pI233) 1 232 (true, (init pI233), (init pI233))) 233 10 false) = true := by
  decide +kernel
theorem I233_ok : RunOK pI233 233 (runFrom pI233 (fmask pI233) (cmask pI233) (hmask pI233) 1 232 (true, (init pI233), (init pI233))) ∧ intTest pI233 (runFrom pI233 (fmask pI233) (cmask pI233) (hmask pI233) 1 232 (true, (init pI233), (init pI233))) 233 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I233_fin) true) (by decide) rfl I233_fin intTest_fst
theorem link233 : linkOK pL233 pH233 pI233 = true := by decide +kernel
theorem cvx233 : ConvexBetweenHumps 233 :=
  cvx_of L233_ok H233_ok I233_ok link233 (by decide)

/-! ### `N = 234` -/

def pL234 : Prm := ⟨64, 30, 31, 236, 11, 18446744073709551616, 522643873834528731, 522643873834528731⟩
def pH234 : Prm := ⟨64, 31, 30, 236, 11, 18446744073709551616, 522661466020573147, 522661466020573147⟩
def pI234 : Prm := ⟨55, 27, 25, 236, 11, 18446744073709551616, 522643873834528731, 522661466020573147⟩
theorem L234_fin : (prmOK pL234 234 && ptTest pL234 (runFrom pL234 (fmask pL234) (cmask pL234) (hmask pL234) 1 233 (true, (init pL234), (init pL234))) 234 117 false) = true := by
  decide +kernel
theorem L234_ok : RunOK pL234 234 (runFrom pL234 (fmask pL234) (cmask pL234) (hmask pL234) 1 233 (true, (init pL234), (init pL234))) ∧ ptTest pL234 (runFrom pL234 (fmask pL234) (cmask pL234) (hmask pL234) 1 233 (true, (init pL234), (init pL234))) 234 117 false = true :=
  fin_run (runOK_init (prmOK_of_and L234_fin) true) (by decide) rfl L234_fin ptTest_fst
theorem H234_fin : (prmOK pH234 234 && ptTest pH234 (runFrom pH234 (fmask pH234) (cmask pH234) (hmask pH234) 1 233 (true, (init pH234), (init pH234))) 234 117 true) = true := by
  decide +kernel
theorem H234_ok : RunOK pH234 234 (runFrom pH234 (fmask pH234) (cmask pH234) (hmask pH234) 1 233 (true, (init pH234), (init pH234))) ∧ ptTest pH234 (runFrom pH234 (fmask pH234) (cmask pH234) (hmask pH234) 1 233 (true, (init pH234), (init pH234))) 234 117 true = true :=
  fin_run (runOK_init (prmOK_of_and H234_fin) true) (by decide) rfl H234_fin ptTest_fst
theorem I234_fin : (prmOK pI234 234 && intTest pI234 (runFrom pI234 (fmask pI234) (cmask pI234) (hmask pI234) 1 233 (true, (init pI234), (init pI234))) 234 10 true) = true := by
  decide +kernel
theorem I234_ok : RunOK pI234 234 (runFrom pI234 (fmask pI234) (cmask pI234) (hmask pI234) 1 233 (true, (init pI234), (init pI234))) ∧ intTest pI234 (runFrom pI234 (fmask pI234) (cmask pI234) (hmask pI234) 1 233 (true, (init pI234), (init pI234))) 234 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I234_fin) true) (by decide) rfl I234_fin intTest_fst
theorem link234 : linkOK pL234 pH234 pI234 = true := by decide +kernel
theorem cvx234 : ConvexBetweenHumps 234 :=
  cvx_of L234_ok H234_ok I234_ok link234 (by decide)
theorem cenlink234 : cenLinkOK pI234 234 = true := by decide +kernel
theorem cen234 : CenterUniqueMin 234 ∧ DipHyp 234 ∧ OnePointHyps 234 :=
  cen_of L234_ok H234_ok I234_ok link234 cenlink234

/-! ### `N = 235` -/

def pL235 : Prm := ⟨64, 31, 30, 237, 11, 18446744073709551616, 521034083404632378, 521034083404632378⟩
def pH235 : Prm := ⟨64, 30, 31, 237, 11, 18446744073709551616, 521051675590676794, 521051675590676794⟩
def pI235 : Prm := ⟨55, 27, 25, 237, 11, 18446744073709551616, 521034083404632378, 521051675590676794⟩
theorem L235_fin : (prmOK pL235 235 && ptTest pL235 (runFrom pL235 (fmask pL235) (cmask pL235) (hmask pL235) 1 234 (true, (init pL235), (init pL235))) 235 118 false) = true := by
  decide +kernel
theorem L235_ok : RunOK pL235 235 (runFrom pL235 (fmask pL235) (cmask pL235) (hmask pL235) 1 234 (true, (init pL235), (init pL235))) ∧ ptTest pL235 (runFrom pL235 (fmask pL235) (cmask pL235) (hmask pL235) 1 234 (true, (init pL235), (init pL235))) 235 118 false = true :=
  fin_run (runOK_init (prmOK_of_and L235_fin) true) (by decide) rfl L235_fin ptTest_fst
theorem H235_fin : (prmOK pH235 235 && ptTest pH235 (runFrom pH235 (fmask pH235) (cmask pH235) (hmask pH235) 1 234 (true, (init pH235), (init pH235))) 235 118 true) = true := by
  decide +kernel
theorem H235_ok : RunOK pH235 235 (runFrom pH235 (fmask pH235) (cmask pH235) (hmask pH235) 1 234 (true, (init pH235), (init pH235))) ∧ ptTest pH235 (runFrom pH235 (fmask pH235) (cmask pH235) (hmask pH235) 1 234 (true, (init pH235), (init pH235))) 235 118 true = true :=
  fin_run (runOK_init (prmOK_of_and H235_fin) true) (by decide) rfl H235_fin ptTest_fst
theorem I235_fin : (prmOK pI235 235 && intTest pI235 (runFrom pI235 (fmask pI235) (cmask pI235) (hmask pI235) 1 234 (true, (init pI235), (init pI235))) 235 10 false) = true := by
  decide +kernel
theorem I235_ok : RunOK pI235 235 (runFrom pI235 (fmask pI235) (cmask pI235) (hmask pI235) 1 234 (true, (init pI235), (init pI235))) ∧ intTest pI235 (runFrom pI235 (fmask pI235) (cmask pI235) (hmask pI235) 1 234 (true, (init pI235), (init pI235))) 235 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I235_fin) true) (by decide) rfl I235_fin intTest_fst
theorem link235 : linkOK pL235 pH235 pI235 = true := by decide +kernel
theorem cvx235 : ConvexBetweenHumps 235 :=
  cvx_of L235_ok H235_ok I235_ok link235 (by decide)

/-! ### `N = 236` -/

def pL236 : Prm := ⟨64, 30, 31, 238, 11, 18446744073709551616, 519444791090958253, 519444791090958253⟩
def pH236 : Prm := ⟨64, 30, 31, 238, 11, 18446744073709551616, 519462383277002669, 519462383277002669⟩
def pI236 : Prm := ⟨55, 27, 25, 238, 11, 18446744073709551616, 519444791090958253, 519462383277002669⟩
theorem L236_fin : (prmOK pL236 236 && ptTest pL236 (runFrom pL236 (fmask pL236) (cmask pL236) (hmask pL236) 1 235 (true, (init pL236), (init pL236))) 236 118 false) = true := by
  decide +kernel
theorem L236_ok : RunOK pL236 236 (runFrom pL236 (fmask pL236) (cmask pL236) (hmask pL236) 1 235 (true, (init pL236), (init pL236))) ∧ ptTest pL236 (runFrom pL236 (fmask pL236) (cmask pL236) (hmask pL236) 1 235 (true, (init pL236), (init pL236))) 236 118 false = true :=
  fin_run (runOK_init (prmOK_of_and L236_fin) true) (by decide) rfl L236_fin ptTest_fst
theorem H236_fin : (prmOK pH236 236 && ptTest pH236 (runFrom pH236 (fmask pH236) (cmask pH236) (hmask pH236) 1 235 (true, (init pH236), (init pH236))) 236 118 true) = true := by
  decide +kernel
theorem H236_ok : RunOK pH236 236 (runFrom pH236 (fmask pH236) (cmask pH236) (hmask pH236) 1 235 (true, (init pH236), (init pH236))) ∧ ptTest pH236 (runFrom pH236 (fmask pH236) (cmask pH236) (hmask pH236) 1 235 (true, (init pH236), (init pH236))) 236 118 true = true :=
  fin_run (runOK_init (prmOK_of_and H236_fin) true) (by decide) rfl H236_fin ptTest_fst
theorem I236_fin : (prmOK pI236 236 && intTest pI236 (runFrom pI236 (fmask pI236) (cmask pI236) (hmask pI236) 1 235 (true, (init pI236), (init pI236))) 236 10 true) = true := by
  decide +kernel
theorem I236_ok : RunOK pI236 236 (runFrom pI236 (fmask pI236) (cmask pI236) (hmask pI236) 1 235 (true, (init pI236), (init pI236))) ∧ intTest pI236 (runFrom pI236 (fmask pI236) (cmask pI236) (hmask pI236) 1 235 (true, (init pI236), (init pI236))) 236 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I236_fin) true) (by decide) rfl I236_fin intTest_fst
theorem link236 : linkOK pL236 pH236 pI236 = true := by decide +kernel
theorem cvx236 : ConvexBetweenHumps 236 :=
  cvx_of L236_ok H236_ok I236_ok link236 (by decide)
theorem cenlink236 : cenLinkOK pI236 236 = true := by decide +kernel
theorem cen236 : CenterUniqueMin 236 ∧ DipHyp 236 ∧ OnePointHyps 236 :=
  cen_of L236_ok H236_ok I236_ok link236 cenlink236

/-! ### `N = 237` -/

def pL237 : Prm := ⟨64, 30, 31, 239, 11, 18446744073709551616, 517857169004226995, 517857169004226995⟩
def pH237 : Prm := ⟨64, 30, 31, 239, 11, 18446744073709551616, 517874761190271411, 517874761190271411⟩
def pI237 : Prm := ⟨55, 27, 25, 239, 11, 18446744073709551616, 517857169004226995, 517874761190271411⟩
theorem L237_fin : (prmOK pL237 237 && ptTest pL237 (runFrom pL237 (fmask pL237) (cmask pL237) (hmask pL237) 1 236 (true, (init pL237), (init pL237))) 237 119 false) = true := by
  decide +kernel
theorem L237_ok : RunOK pL237 237 (runFrom pL237 (fmask pL237) (cmask pL237) (hmask pL237) 1 236 (true, (init pL237), (init pL237))) ∧ ptTest pL237 (runFrom pL237 (fmask pL237) (cmask pL237) (hmask pL237) 1 236 (true, (init pL237), (init pL237))) 237 119 false = true :=
  fin_run (runOK_init (prmOK_of_and L237_fin) true) (by decide) rfl L237_fin ptTest_fst
theorem H237_fin : (prmOK pH237 237 && ptTest pH237 (runFrom pH237 (fmask pH237) (cmask pH237) (hmask pH237) 1 236 (true, (init pH237), (init pH237))) 237 119 true) = true := by
  decide +kernel
theorem H237_ok : RunOK pH237 237 (runFrom pH237 (fmask pH237) (cmask pH237) (hmask pH237) 1 236 (true, (init pH237), (init pH237))) ∧ ptTest pH237 (runFrom pH237 (fmask pH237) (cmask pH237) (hmask pH237) 1 236 (true, (init pH237), (init pH237))) 237 119 true = true :=
  fin_run (runOK_init (prmOK_of_and H237_fin) true) (by decide) rfl H237_fin ptTest_fst
theorem I237_fin : (prmOK pI237 237 && intTest pI237 (runFrom pI237 (fmask pI237) (cmask pI237) (hmask pI237) 1 236 (true, (init pI237), (init pI237))) 237 10 false) = true := by
  decide +kernel
theorem I237_ok : RunOK pI237 237 (runFrom pI237 (fmask pI237) (cmask pI237) (hmask pI237) 1 236 (true, (init pI237), (init pI237))) ∧ intTest pI237 (runFrom pI237 (fmask pI237) (cmask pI237) (hmask pI237) 1 236 (true, (init pI237), (init pI237))) 237 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I237_fin) true) (by decide) rfl I237_fin intTest_fst
theorem link237 : linkOK pL237 pH237 pI237 = true := by decide +kernel
theorem cvx237 : ConvexBetweenHumps 237 :=
  cvx_of L237_ok H237_ok I237_ok link237 (by decide)

/-! ### `N = 238` -/

def pL238 : Prm := ⟨64, 30, 31, 240, 11, 18446744073709551616, 516289571132380153, 516289571132380153⟩
def pH238 : Prm := ⟨64, 30, 31, 240, 11, 18446744073709551616, 516307163318424569, 516307163318424569⟩
def pI238 : Prm := ⟨55, 27, 25, 240, 11, 18446744073709551616, 516289571132380153, 516307163318424569⟩
theorem L238_fin : (prmOK pL238 238 && ptTest pL238 (runFrom pL238 (fmask pL238) (cmask pL238) (hmask pL238) 1 237 (true, (init pL238), (init pL238))) 238 119 false) = true := by
  decide +kernel
theorem L238_ok : RunOK pL238 238 (runFrom pL238 (fmask pL238) (cmask pL238) (hmask pL238) 1 237 (true, (init pL238), (init pL238))) ∧ ptTest pL238 (runFrom pL238 (fmask pL238) (cmask pL238) (hmask pL238) 1 237 (true, (init pL238), (init pL238))) 238 119 false = true :=
  fin_run (runOK_init (prmOK_of_and L238_fin) true) (by decide) rfl L238_fin ptTest_fst
theorem H238_fin : (prmOK pH238 238 && ptTest pH238 (runFrom pH238 (fmask pH238) (cmask pH238) (hmask pH238) 1 237 (true, (init pH238), (init pH238))) 238 119 true) = true := by
  decide +kernel
theorem H238_ok : RunOK pH238 238 (runFrom pH238 (fmask pH238) (cmask pH238) (hmask pH238) 1 237 (true, (init pH238), (init pH238))) ∧ ptTest pH238 (runFrom pH238 (fmask pH238) (cmask pH238) (hmask pH238) 1 237 (true, (init pH238), (init pH238))) 238 119 true = true :=
  fin_run (runOK_init (prmOK_of_and H238_fin) true) (by decide) rfl H238_fin ptTest_fst
theorem I238_fin : (prmOK pI238 238 && intTest pI238 (runFrom pI238 (fmask pI238) (cmask pI238) (hmask pI238) 1 237 (true, (init pI238), (init pI238))) 238 10 true) = true := by
  decide +kernel
theorem I238_ok : RunOK pI238 238 (runFrom pI238 (fmask pI238) (cmask pI238) (hmask pI238) 1 237 (true, (init pI238), (init pI238))) ∧ intTest pI238 (runFrom pI238 (fmask pI238) (cmask pI238) (hmask pI238) 1 237 (true, (init pI238), (init pI238))) 238 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I238_fin) true) (by decide) rfl I238_fin intTest_fst
theorem link238 : linkOK pL238 pH238 pI238 = true := by decide +kernel
theorem cvx238 : ConvexBetweenHumps 238 :=
  cvx_of L238_ok H238_ok I238_ok link238 (by decide)
theorem cenlink238 : cenLinkOK pI238 238 = true := by decide +kernel
theorem cen238 : CenterUniqueMin 238 ∧ DipHyp 238 ∧ OnePointHyps 238 :=
  cen_of L238_ok H238_ok I238_ok link238 cenlink238

/-! ### `N = 239` -/

def pL239 : Prm := ⟨64, 30, 31, 241, 11, 18446744073709551616, 514723640076728538, 514723640076728538⟩
def pH239 : Prm := ⟨64, 30, 31, 241, 11, 18446744073709551616, 514741232262772954, 514741232262772954⟩
def pI239 : Prm := ⟨56, 27, 26, 241, 11, 18446744073709551616, 514723640076728538, 514741232262772954⟩
theorem L239_fin : (prmOK pL239 239 && ptTest pL239 (runFrom pL239 (fmask pL239) (cmask pL239) (hmask pL239) 1 238 (true, (init pL239), (init pL239))) 239 120 false) = true := by
  decide +kernel
theorem L239_ok : RunOK pL239 239 (runFrom pL239 (fmask pL239) (cmask pL239) (hmask pL239) 1 238 (true, (init pL239), (init pL239))) ∧ ptTest pL239 (runFrom pL239 (fmask pL239) (cmask pL239) (hmask pL239) 1 238 (true, (init pL239), (init pL239))) 239 120 false = true :=
  fin_run (runOK_init (prmOK_of_and L239_fin) true) (by decide) rfl L239_fin ptTest_fst
theorem H239_fin : (prmOK pH239 239 && ptTest pH239 (runFrom pH239 (fmask pH239) (cmask pH239) (hmask pH239) 1 238 (true, (init pH239), (init pH239))) 239 120 true) = true := by
  decide +kernel
theorem H239_ok : RunOK pH239 239 (runFrom pH239 (fmask pH239) (cmask pH239) (hmask pH239) 1 238 (true, (init pH239), (init pH239))) ∧ ptTest pH239 (runFrom pH239 (fmask pH239) (cmask pH239) (hmask pH239) 1 238 (true, (init pH239), (init pH239))) 239 120 true = true :=
  fin_run (runOK_init (prmOK_of_and H239_fin) true) (by decide) rfl H239_fin ptTest_fst
theorem I239_fin : (prmOK pI239 239 && intTest pI239 (runFrom pI239 (fmask pI239) (cmask pI239) (hmask pI239) 1 238 (true, (init pI239), (init pI239))) 239 10 false) = true := by
  decide +kernel
theorem I239_ok : RunOK pI239 239 (runFrom pI239 (fmask pI239) (cmask pI239) (hmask pI239) 1 238 (true, (init pI239), (init pI239))) ∧ intTest pI239 (runFrom pI239 (fmask pI239) (cmask pI239) (hmask pI239) 1 238 (true, (init pI239), (init pI239))) 239 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I239_fin) true) (by decide) rfl I239_fin intTest_fst
theorem link239 : linkOK pL239 pH239 pI239 = true := by decide +kernel
theorem cvx239 : ConvexBetweenHumps 239 :=
  cvx_of L239_ok H239_ok I239_ok link239 (by decide)

/-! ### `N = 240` -/

def pL240 : Prm := ⟨64, 30, 31, 242, 11, 18446744073709551616, 513177274020832800, 513177274020832800⟩
def pH240 : Prm := ⟨64, 30, 31, 242, 11, 18446744073709551616, 513194866206877216, 513194866206877216⟩
def pI240 : Prm := ⟨56, 27, 26, 242, 11, 18446744073709551616, 513177274020832800, 513194866206877216⟩
theorem L240_fin : (prmOK pL240 240 && ptTest pL240 (runFrom pL240 (fmask pL240) (cmask pL240) (hmask pL240) 1 239 (true, (init pL240), (init pL240))) 240 120 false) = true := by
  decide +kernel
theorem L240_ok : RunOK pL240 240 (runFrom pL240 (fmask pL240) (cmask pL240) (hmask pL240) 1 239 (true, (init pL240), (init pL240))) ∧ ptTest pL240 (runFrom pL240 (fmask pL240) (cmask pL240) (hmask pL240) 1 239 (true, (init pL240), (init pL240))) 240 120 false = true :=
  fin_run (runOK_init (prmOK_of_and L240_fin) true) (by decide) rfl L240_fin ptTest_fst
theorem H240_fin : (prmOK pH240 240 && ptTest pH240 (runFrom pH240 (fmask pH240) (cmask pH240) (hmask pH240) 1 239 (true, (init pH240), (init pH240))) 240 120 true) = true := by
  decide +kernel
theorem H240_ok : RunOK pH240 240 (runFrom pH240 (fmask pH240) (cmask pH240) (hmask pH240) 1 239 (true, (init pH240), (init pH240))) ∧ ptTest pH240 (runFrom pH240 (fmask pH240) (cmask pH240) (hmask pH240) 1 239 (true, (init pH240), (init pH240))) 240 120 true = true :=
  fin_run (runOK_init (prmOK_of_and H240_fin) true) (by decide) rfl H240_fin ptTest_fst
theorem I240_fin : (prmOK pI240 240 && intTest pI240 (runFrom pI240 (fmask pI240) (cmask pI240) (hmask pI240) 1 239 (true, (init pI240), (init pI240))) 240 10 true) = true := by
  decide +kernel
theorem I240_ok : RunOK pI240 240 (runFrom pI240 (fmask pI240) (cmask pI240) (hmask pI240) 1 239 (true, (init pI240), (init pI240))) ∧ intTest pI240 (runFrom pI240 (fmask pI240) (cmask pI240) (hmask pI240) 1 239 (true, (init pI240), (init pI240))) 240 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I240_fin) true) (by decide) rfl I240_fin intTest_fst
theorem link240 : linkOK pL240 pH240 pI240 = true := by decide +kernel
theorem cvx240 : ConvexBetweenHumps 240 :=
  cvx_of L240_ok H240_ok I240_ok link240 (by decide)
theorem cenlink240 : cenLinkOK pI240 240 = true := by decide +kernel
theorem cen240 : CenterUniqueMin 240 ∧ DipHyp 240 ∧ OnePointHyps 240 :=
  cen_of L240_ok H240_ok I240_ok link240 cenlink240

/-! ### `N = 241` -/

def pL241 : Prm := ⟨64, 30, 31, 243, 11, 18446744073709551616, 511632570668799634, 511632570668799634⟩
def pH241 : Prm := ⟨64, 30, 31, 243, 11, 18446744073709551616, 511650162854844050, 511650162854844050⟩
def pI241 : Prm := ⟨56, 27, 26, 243, 11, 18446744073709551616, 511632570668799634, 511650162854844050⟩
theorem L241_fin : (prmOK pL241 241 && ptTest pL241 (runFrom pL241 (fmask pL241) (cmask pL241) (hmask pL241) 1 240 (true, (init pL241), (init pL241))) 241 121 false) = true := by
  decide +kernel
theorem L241_ok : RunOK pL241 241 (runFrom pL241 (fmask pL241) (cmask pL241) (hmask pL241) 1 240 (true, (init pL241), (init pL241))) ∧ ptTest pL241 (runFrom pL241 (fmask pL241) (cmask pL241) (hmask pL241) 1 240 (true, (init pL241), (init pL241))) 241 121 false = true :=
  fin_run (runOK_init (prmOK_of_and L241_fin) true) (by decide) rfl L241_fin ptTest_fst
theorem H241_fin : (prmOK pH241 241 && ptTest pH241 (runFrom pH241 (fmask pH241) (cmask pH241) (hmask pH241) 1 240 (true, (init pH241), (init pH241))) 241 121 true) = true := by
  decide +kernel
theorem H241_ok : RunOK pH241 241 (runFrom pH241 (fmask pH241) (cmask pH241) (hmask pH241) 1 240 (true, (init pH241), (init pH241))) ∧ ptTest pH241 (runFrom pH241 (fmask pH241) (cmask pH241) (hmask pH241) 1 240 (true, (init pH241), (init pH241))) 241 121 true = true :=
  fin_run (runOK_init (prmOK_of_and H241_fin) true) (by decide) rfl H241_fin ptTest_fst
theorem I241_fin : (prmOK pI241 241 && intTest pI241 (runFrom pI241 (fmask pI241) (cmask pI241) (hmask pI241) 1 240 (true, (init pI241), (init pI241))) 241 10 false) = true := by
  decide +kernel
theorem I241_ok : RunOK pI241 241 (runFrom pI241 (fmask pI241) (cmask pI241) (hmask pI241) 1 240 (true, (init pI241), (init pI241))) ∧ intTest pI241 (runFrom pI241 (fmask pI241) (cmask pI241) (hmask pI241) 1 240 (true, (init pI241), (init pI241))) 241 10 false = true :=
  fin_run (runOK_init (prmOK_of_and I241_fin) true) (by decide) rfl I241_fin intTest_fst
theorem link241 : linkOK pL241 pH241 pI241 = true := by decide +kernel
theorem cvx241 : ConvexBetweenHumps 241 :=
  cvx_of L241_ok H241_ok I241_ok link241 (by decide)

/-! ### `N = 242` -/

def pL242 : Prm := ⟨64, 30, 31, 244, 11, 18446744073709551616, 510106987218963746, 510106987218963746⟩
def pH242 : Prm := ⟨64, 30, 31, 244, 11, 18446744073709551616, 510124579405008162, 510124579405008162⟩
def pI242 : Prm := ⟨56, 27, 26, 244, 11, 18446744073709551616, 510106987218963746, 510124579405008162⟩
theorem L242_fin : (prmOK pL242 242 && ptTest pL242 (runFrom pL242 (fmask pL242) (cmask pL242) (hmask pL242) 1 241 (true, (init pL242), (init pL242))) 242 121 false) = true := by
  decide +kernel
theorem L242_ok : RunOK pL242 242 (runFrom pL242 (fmask pL242) (cmask pL242) (hmask pL242) 1 241 (true, (init pL242), (init pL242))) ∧ ptTest pL242 (runFrom pL242 (fmask pL242) (cmask pL242) (hmask pL242) 1 241 (true, (init pL242), (init pL242))) 242 121 false = true :=
  fin_run (runOK_init (prmOK_of_and L242_fin) true) (by decide) rfl L242_fin ptTest_fst
theorem H242_fin : (prmOK pH242 242 && ptTest pH242 (runFrom pH242 (fmask pH242) (cmask pH242) (hmask pH242) 1 241 (true, (init pH242), (init pH242))) 242 121 true) = true := by
  decide +kernel
theorem H242_ok : RunOK pH242 242 (runFrom pH242 (fmask pH242) (cmask pH242) (hmask pH242) 1 241 (true, (init pH242), (init pH242))) ∧ ptTest pH242 (runFrom pH242 (fmask pH242) (cmask pH242) (hmask pH242) 1 241 (true, (init pH242), (init pH242))) 242 121 true = true :=
  fin_run (runOK_init (prmOK_of_and H242_fin) true) (by decide) rfl H242_fin ptTest_fst
theorem I242_fin : (prmOK pI242 242 && intTest pI242 (runFrom pI242 (fmask pI242) (cmask pI242) (hmask pI242) 1 241 (true, (init pI242), (init pI242))) 242 10 true) = true := by
  decide +kernel
theorem I242_ok : RunOK pI242 242 (runFrom pI242 (fmask pI242) (cmask pI242) (hmask pI242) 1 241 (true, (init pI242), (init pI242))) ∧ intTest pI242 (runFrom pI242 (fmask pI242) (cmask pI242) (hmask pI242) 1 241 (true, (init pI242), (init pI242))) 242 10 true = true :=
  fin_run (runOK_init (prmOK_of_and I242_fin) true) (by decide) rfl I242_fin intTest_fst
theorem link242 : linkOK pL242 pH242 pI242 = true := by decide +kernel
theorem cvx242 : ConvexBetweenHumps 242 :=
  cvx_of L242_ok H242_ok I242_ok link242 (by decide)
theorem cenlink242 : cenLinkOK pI242 242 = true := by decide +kernel
theorem cen242 : CenterUniqueMin 242 ∧ DipHyp 242 ∧ OnePointHyps 242 :=
  cen_of L242_ok H242_ok I242_ok link242 cenlink242

/-! ### `N = 243` -/

def pL243 : Prm := ⟨64, 30, 31, 245, 11, 18446744073709551616, 508583061709893536, 508583061709893536⟩
def pH243 : Prm := ⟨64, 30, 31, 245, 11, 18446744073709551616, 508600653895937952, 508600653895937952⟩
def pI243 : Prm := ⟨56, 27, 26, 245, 11, 18446744073709551616, 508583061709893536, 508600653895937952⟩
theorem L243_fin : (prmOK pL243 243 && ptTest pL243 (runFrom pL243 (fmask pL243) (cmask pL243) (hmask pL243) 1 242 (true, (init pL243), (init pL243))) 243 122 false) = true := by
  decide +kernel
theorem L243_ok : RunOK pL243 243 (runFrom pL243 (fmask pL243) (cmask pL243) (hmask pL243) 1 242 (true, (init pL243), (init pL243))) ∧ ptTest pL243 (runFrom pL243 (fmask pL243) (cmask pL243) (hmask pL243) 1 242 (true, (init pL243), (init pL243))) 243 122 false = true :=
  fin_run (runOK_init (prmOK_of_and L243_fin) true) (by decide) rfl L243_fin ptTest_fst
theorem H243_fin : (prmOK pH243 243 && ptTest pH243 (runFrom pH243 (fmask pH243) (cmask pH243) (hmask pH243) 1 242 (true, (init pH243), (init pH243))) 243 122 true) = true := by
  decide +kernel
theorem H243_ok : RunOK pH243 243 (runFrom pH243 (fmask pH243) (cmask pH243) (hmask pH243) 1 242 (true, (init pH243), (init pH243))) ∧ ptTest pH243 (runFrom pH243 (fmask pH243) (cmask pH243) (hmask pH243) 1 242 (true, (init pH243), (init pH243))) 243 122 true = true :=
  fin_run (runOK_init (prmOK_of_and H243_fin) true) (by decide) rfl H243_fin ptTest_fst
theorem I243_fin : (prmOK pI243 243 && intTest pI243 (runFrom pI243 (fmask pI243) (cmask pI243) (hmask pI243) 1 242 (true, (init pI243), (init pI243))) 243 11 false) = true := by
  decide +kernel
theorem I243_ok : RunOK pI243 243 (runFrom pI243 (fmask pI243) (cmask pI243) (hmask pI243) 1 242 (true, (init pI243), (init pI243))) ∧ intTest pI243 (runFrom pI243 (fmask pI243) (cmask pI243) (hmask pI243) 1 242 (true, (init pI243), (init pI243))) 243 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I243_fin) true) (by decide) rfl I243_fin intTest_fst
theorem link243 : linkOK pL243 pH243 pI243 = true := by decide +kernel
theorem cvx243 : ConvexBetweenHumps 243 :=
  cvx_of L243_ok H243_ok I243_ok link243 (by decide)

/-! ### `N = 244` -/

def pL244 : Prm := ⟨64, 30, 31, 246, 11, 18446744073709551616, 507077824580716118, 507077824580716118⟩
def pH244 : Prm := ⟨64, 30, 31, 246, 11, 18446744073709551616, 507095416766760534, 507095416766760534⟩
def pI244 : Prm := ⟨56, 27, 26, 246, 11, 18446744073709551616, 507077824580716118, 507095416766760534⟩
theorem L244_fin : (prmOK pL244 244 && ptTest pL244 (runFrom pL244 (fmask pL244) (cmask pL244) (hmask pL244) 1 243 (true, (init pL244), (init pL244))) 244 122 false) = true := by
  decide +kernel
theorem L244_ok : RunOK pL244 244 (runFrom pL244 (fmask pL244) (cmask pL244) (hmask pL244) 1 243 (true, (init pL244), (init pL244))) ∧ ptTest pL244 (runFrom pL244 (fmask pL244) (cmask pL244) (hmask pL244) 1 243 (true, (init pL244), (init pL244))) 244 122 false = true :=
  fin_run (runOK_init (prmOK_of_and L244_fin) true) (by decide) rfl L244_fin ptTest_fst
theorem H244_fin : (prmOK pH244 244 && ptTest pH244 (runFrom pH244 (fmask pH244) (cmask pH244) (hmask pH244) 1 243 (true, (init pH244), (init pH244))) 244 122 true) = true := by
  decide +kernel
theorem H244_ok : RunOK pH244 244 (runFrom pH244 (fmask pH244) (cmask pH244) (hmask pH244) 1 243 (true, (init pH244), (init pH244))) ∧ ptTest pH244 (runFrom pH244 (fmask pH244) (cmask pH244) (hmask pH244) 1 243 (true, (init pH244), (init pH244))) 244 122 true = true :=
  fin_run (runOK_init (prmOK_of_and H244_fin) true) (by decide) rfl H244_fin ptTest_fst
theorem I244_fin : (prmOK pI244 244 && intTest pI244 (runFrom pI244 (fmask pI244) (cmask pI244) (hmask pI244) 1 243 (true, (init pI244), (init pI244))) 244 11 true) = true := by
  decide +kernel
theorem I244_ok : RunOK pI244 244 (runFrom pI244 (fmask pI244) (cmask pI244) (hmask pI244) 1 243 (true, (init pI244), (init pI244))) ∧ intTest pI244 (runFrom pI244 (fmask pI244) (cmask pI244) (hmask pI244) 1 243 (true, (init pI244), (init pI244))) 244 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I244_fin) true) (by decide) rfl I244_fin intTest_fst
theorem link244 : linkOK pL244 pH244 pI244 = true := by decide +kernel
theorem cvx244 : ConvexBetweenHumps 244 :=
  cvx_of L244_ok H244_ok I244_ok link244 (by decide)
theorem cenlink244 : cenLinkOK pI244 244 = true := by decide +kernel
theorem cen244 : CenterUniqueMin 244 ∧ DipHyp 244 ∧ OnePointHyps 244 :=
  cen_of L244_ok H244_ok I244_ok link244 cenlink244

/-! ### `N = 245` -/

def pL245 : Prm := ⟨64, 30, 31, 247, 11, 18446744073709551616, 505574240026201868, 505574240026201868⟩
def pH245 : Prm := ⟨64, 30, 31, 247, 11, 18446744073709551616, 505591832212246284, 505591832212246284⟩
def pI245 : Prm := ⟨56, 27, 26, 247, 11, 18446744073709551616, 505574240026201868, 505591832212246284⟩
theorem L245_fin : (prmOK pL245 245 && ptTest pL245 (runFrom pL245 (fmask pL245) (cmask pL245) (hmask pL245) 1 244 (true, (init pL245), (init pL245))) 245 123 false) = true := by
  decide +kernel
theorem L245_ok : RunOK pL245 245 (runFrom pL245 (fmask pL245) (cmask pL245) (hmask pL245) 1 244 (true, (init pL245), (init pL245))) ∧ ptTest pL245 (runFrom pL245 (fmask pL245) (cmask pL245) (hmask pL245) 1 244 (true, (init pL245), (init pL245))) 245 123 false = true :=
  fin_run (runOK_init (prmOK_of_and L245_fin) true) (by decide) rfl L245_fin ptTest_fst
theorem H245_fin : (prmOK pH245 245 && ptTest pH245 (runFrom pH245 (fmask pH245) (cmask pH245) (hmask pH245) 1 244 (true, (init pH245), (init pH245))) 245 123 true) = true := by
  decide +kernel
theorem H245_ok : RunOK pH245 245 (runFrom pH245 (fmask pH245) (cmask pH245) (hmask pH245) 1 244 (true, (init pH245), (init pH245))) ∧ ptTest pH245 (runFrom pH245 (fmask pH245) (cmask pH245) (hmask pH245) 1 244 (true, (init pH245), (init pH245))) 245 123 true = true :=
  fin_run (runOK_init (prmOK_of_and H245_fin) true) (by decide) rfl H245_fin ptTest_fst
theorem I245_fin : (prmOK pI245 245 && intTest pI245 (runFrom pI245 (fmask pI245) (cmask pI245) (hmask pI245) 1 244 (true, (init pI245), (init pI245))) 245 11 false) = true := by
  decide +kernel
theorem I245_ok : RunOK pI245 245 (runFrom pI245 (fmask pI245) (cmask pI245) (hmask pI245) 1 244 (true, (init pI245), (init pI245))) ∧ intTest pI245 (runFrom pI245 (fmask pI245) (cmask pI245) (hmask pI245) 1 244 (true, (init pI245), (init pI245))) 245 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I245_fin) true) (by decide) rfl I245_fin intTest_fst
theorem link245 : linkOK pL245 pH245 pI245 = true := by decide +kernel
theorem cvx245 : ConvexBetweenHumps 245 :=
  cvx_of L245_ok H245_ok I245_ok link245 (by decide)

/-! ### `N = 246` -/

def pL246 : Prm := ⟨64, 30, 31, 248, 11, 18446744073709551616, 504088925387061970, 504088925387061970⟩
def pH246 : Prm := ⟨64, 30, 31, 248, 11, 18446744073709551616, 504106517573106386, 504106517573106386⟩
def pI246 : Prm := ⟨55, 27, 25, 248, 11, 18446744073709551616, 504088925387061970, 504106517573106386⟩
theorem L246_fin : (prmOK pL246 246 && ptTest pL246 (runFrom pL246 (fmask pL246) (cmask pL246) (hmask pL246) 1 245 (true, (init pL246), (init pL246))) 246 123 false) = true := by
  decide +kernel
theorem L246_ok : RunOK pL246 246 (runFrom pL246 (fmask pL246) (cmask pL246) (hmask pL246) 1 245 (true, (init pL246), (init pL246))) ∧ ptTest pL246 (runFrom pL246 (fmask pL246) (cmask pL246) (hmask pL246) 1 245 (true, (init pL246), (init pL246))) 246 123 false = true :=
  fin_run (runOK_init (prmOK_of_and L246_fin) true) (by decide) rfl L246_fin ptTest_fst
theorem H246_fin : (prmOK pH246 246 && ptTest pH246 (runFrom pH246 (fmask pH246) (cmask pH246) (hmask pH246) 1 245 (true, (init pH246), (init pH246))) 246 123 true) = true := by
  decide +kernel
theorem H246_ok : RunOK pH246 246 (runFrom pH246 (fmask pH246) (cmask pH246) (hmask pH246) 1 245 (true, (init pH246), (init pH246))) ∧ ptTest pH246 (runFrom pH246 (fmask pH246) (cmask pH246) (hmask pH246) 1 245 (true, (init pH246), (init pH246))) 246 123 true = true :=
  fin_run (runOK_init (prmOK_of_and H246_fin) true) (by decide) rfl H246_fin ptTest_fst
theorem I246_fin : (prmOK pI246 246 && intTest pI246 (runFrom pI246 (fmask pI246) (cmask pI246) (hmask pI246) 1 245 (true, (init pI246), (init pI246))) 246 11 true) = true := by
  decide +kernel
theorem I246_ok : RunOK pI246 246 (runFrom pI246 (fmask pI246) (cmask pI246) (hmask pI246) 1 245 (true, (init pI246), (init pI246))) ∧ intTest pI246 (runFrom pI246 (fmask pI246) (cmask pI246) (hmask pI246) 1 245 (true, (init pI246), (init pI246))) 246 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I246_fin) true) (by decide) rfl I246_fin intTest_fst
theorem link246 : linkOK pL246 pH246 pI246 = true := by decide +kernel
theorem cvx246 : ConvexBetweenHumps 246 :=
  cvx_of L246_ok H246_ok I246_ok link246 (by decide)
theorem cenlink246 : cenLinkOK pI246 246 = true := by decide +kernel
theorem cen246 : CenterUniqueMin 246 ∧ DipHyp 246 ∧ OnePointHyps 246 :=
  cen_of L246_ok H246_ok I246_ok link246 cenlink246

/-! ### `N = 247` -/

def pL247 : Prm := ⟨64, 30, 31, 249, 11, 18446744073709551616, 502605257398081339, 502605257398081339⟩
def pH247 : Prm := ⟨64, 30, 31, 249, 11, 18446744073709551616, 502622849584125755, 502622849584125755⟩
def pI247 : Prm := ⟨55, 27, 25, 249, 11, 18446744073709551616, 502605257398081339, 502622849584125755⟩
theorem L247_fin : (prmOK pL247 247 && ptTest pL247 (runFrom pL247 (fmask pL247) (cmask pL247) (hmask pL247) 1 246 (true, (init pL247), (init pL247))) 247 124 false) = true := by
  decide +kernel
theorem L247_ok : RunOK pL247 247 (runFrom pL247 (fmask pL247) (cmask pL247) (hmask pL247) 1 246 (true, (init pL247), (init pL247))) ∧ ptTest pL247 (runFrom pL247 (fmask pL247) (cmask pL247) (hmask pL247) 1 246 (true, (init pL247), (init pL247))) 247 124 false = true :=
  fin_run (runOK_init (prmOK_of_and L247_fin) true) (by decide) rfl L247_fin ptTest_fst
theorem H247_fin : (prmOK pH247 247 && ptTest pH247 (runFrom pH247 (fmask pH247) (cmask pH247) (hmask pH247) 1 246 (true, (init pH247), (init pH247))) 247 124 true) = true := by
  decide +kernel
theorem H247_ok : RunOK pH247 247 (runFrom pH247 (fmask pH247) (cmask pH247) (hmask pH247) 1 246 (true, (init pH247), (init pH247))) ∧ ptTest pH247 (runFrom pH247 (fmask pH247) (cmask pH247) (hmask pH247) 1 246 (true, (init pH247), (init pH247))) 247 124 true = true :=
  fin_run (runOK_init (prmOK_of_and H247_fin) true) (by decide) rfl H247_fin ptTest_fst
theorem I247_fin : (prmOK pI247 247 && intTest pI247 (runFrom pI247 (fmask pI247) (cmask pI247) (hmask pI247) 1 246 (true, (init pI247), (init pI247))) 247 11 false) = true := by
  decide +kernel
theorem I247_ok : RunOK pI247 247 (runFrom pI247 (fmask pI247) (cmask pI247) (hmask pI247) 1 246 (true, (init pI247), (init pI247))) ∧ intTest pI247 (runFrom pI247 (fmask pI247) (cmask pI247) (hmask pI247) 1 246 (true, (init pI247), (init pI247))) 247 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I247_fin) true) (by decide) rfl I247_fin intTest_fst
theorem link247 : linkOK pL247 pH247 pI247 = true := by decide +kernel
theorem cvx247 : ConvexBetweenHumps 247 :=
  cvx_of L247_ok H247_ok I247_ok link247 (by decide)

/-! ### `N = 248` -/

def pL248 : Prm := ⟨64, 30, 31, 250, 11, 18446744073709551616, 501139453424015563, 501139453424015563⟩
def pH248 : Prm := ⟨64, 30, 31, 250, 11, 18446744073709551616, 501157045610059979, 501157045610059979⟩
def pI248 : Prm := ⟨55, 27, 25, 250, 11, 18446744073709551616, 501139453424015563, 501157045610059979⟩
theorem L248_fin : (prmOK pL248 248 && ptTest pL248 (runFrom pL248 (fmask pL248) (cmask pL248) (hmask pL248) 1 247 (true, (init pL248), (init pL248))) 248 124 false) = true := by
  decide +kernel
theorem L248_ok : RunOK pL248 248 (runFrom pL248 (fmask pL248) (cmask pL248) (hmask pL248) 1 247 (true, (init pL248), (init pL248))) ∧ ptTest pL248 (runFrom pL248 (fmask pL248) (cmask pL248) (hmask pL248) 1 247 (true, (init pL248), (init pL248))) 248 124 false = true :=
  fin_run (runOK_init (prmOK_of_and L248_fin) true) (by decide) rfl L248_fin ptTest_fst
theorem H248_fin : (prmOK pH248 248 && ptTest pH248 (runFrom pH248 (fmask pH248) (cmask pH248) (hmask pH248) 1 247 (true, (init pH248), (init pH248))) 248 124 true) = true := by
  decide +kernel
theorem H248_ok : RunOK pH248 248 (runFrom pH248 (fmask pH248) (cmask pH248) (hmask pH248) 1 247 (true, (init pH248), (init pH248))) ∧ ptTest pH248 (runFrom pH248 (fmask pH248) (cmask pH248) (hmask pH248) 1 247 (true, (init pH248), (init pH248))) 248 124 true = true :=
  fin_run (runOK_init (prmOK_of_and H248_fin) true) (by decide) rfl H248_fin ptTest_fst
theorem I248_fin : (prmOK pI248 248 && intTest pI248 (runFrom pI248 (fmask pI248) (cmask pI248) (hmask pI248) 1 247 (true, (init pI248), (init pI248))) 248 11 true) = true := by
  decide +kernel
theorem I248_ok : RunOK pI248 248 (runFrom pI248 (fmask pI248) (cmask pI248) (hmask pI248) 1 247 (true, (init pI248), (init pI248))) ∧ intTest pI248 (runFrom pI248 (fmask pI248) (cmask pI248) (hmask pI248) 1 247 (true, (init pI248), (init pI248))) 248 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I248_fin) true) (by decide) rfl I248_fin intTest_fst
theorem link248 : linkOK pL248 pH248 pI248 = true := by decide +kernel
theorem cvx248 : ConvexBetweenHumps 248 :=
  cvx_of L248_ok H248_ok I248_ok link248 (by decide)
theorem cenlink248 : cenLinkOK pI248 248 = true := by decide +kernel
theorem cen248 : CenterUniqueMin 248 ∧ DipHyp 248 ∧ OnePointHyps 248 :=
  cen_of L248_ok H248_ok I248_ok link248 cenlink248

/-! ### `N = 249` -/

def pL249 : Prm := ⟨64, 30, 31, 251, 11, 18446744073709551616, 499675289659077872, 499675289659077872⟩
def pH249 : Prm := ⟨64, 30, 31, 251, 11, 18446744073709551616, 499692881845122288, 499692881845122288⟩
def pI249 : Prm := ⟨55, 27, 25, 251, 11, 18446744073709551616, 499675289659077872, 499692881845122288⟩
theorem L249_fin : (prmOK pL249 249 && ptTest pL249 (runFrom pL249 (fmask pL249) (cmask pL249) (hmask pL249) 1 248 (true, (init pL249), (init pL249))) 249 125 false) = true := by
  decide +kernel
theorem L249_ok : RunOK pL249 249 (runFrom pL249 (fmask pL249) (cmask pL249) (hmask pL249) 1 248 (true, (init pL249), (init pL249))) ∧ ptTest pL249 (runFrom pL249 (fmask pL249) (cmask pL249) (hmask pL249) 1 248 (true, (init pL249), (init pL249))) 249 125 false = true :=
  fin_run (runOK_init (prmOK_of_and L249_fin) true) (by decide) rfl L249_fin ptTest_fst
theorem H249_fin : (prmOK pH249 249 && ptTest pH249 (runFrom pH249 (fmask pH249) (cmask pH249) (hmask pH249) 1 248 (true, (init pH249), (init pH249))) 249 125 true) = true := by
  decide +kernel
theorem H249_ok : RunOK pH249 249 (runFrom pH249 (fmask pH249) (cmask pH249) (hmask pH249) 1 248 (true, (init pH249), (init pH249))) ∧ ptTest pH249 (runFrom pH249 (fmask pH249) (cmask pH249) (hmask pH249) 1 248 (true, (init pH249), (init pH249))) 249 125 true = true :=
  fin_run (runOK_init (prmOK_of_and H249_fin) true) (by decide) rfl H249_fin ptTest_fst
theorem I249_fin : (prmOK pI249 249 && intTest pI249 (runFrom pI249 (fmask pI249) (cmask pI249) (hmask pI249) 1 248 (true, (init pI249), (init pI249))) 249 11 false) = true := by
  decide +kernel
theorem I249_ok : RunOK pI249 249 (runFrom pI249 (fmask pI249) (cmask pI249) (hmask pI249) 1 248 (true, (init pI249), (init pI249))) ∧ intTest pI249 (runFrom pI249 (fmask pI249) (cmask pI249) (hmask pI249) 1 248 (true, (init pI249), (init pI249))) 249 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I249_fin) true) (by decide) rfl I249_fin intTest_fst
theorem link249 : linkOK pL249 pH249 pI249 = true := by decide +kernel
theorem cvx249 : ConvexBetweenHumps 249 :=
  cvx_of L249_ok H249_ok I249_ok link249 (by decide)

/-! ### `N = 250` -/

def pL250 : Prm := ⟨64, 30, 31, 252, 11, 18446744073709551616, 498228596101155703, 498228596101155703⟩
def pH250 : Prm := ⟨64, 30, 31, 252, 11, 18446744073709551616, 498246188287200119, 498246188287200119⟩
def pI250 : Prm := ⟨55, 27, 25, 252, 11, 18446744073709551616, 498228596101155703, 498246188287200119⟩
theorem L250_fin : (prmOK pL250 250 && ptTest pL250 (runFrom pL250 (fmask pL250) (cmask pL250) (hmask pL250) 1 249 (true, (init pL250), (init pL250))) 250 125 false) = true := by
  decide +kernel
theorem L250_ok : RunOK pL250 250 (runFrom pL250 (fmask pL250) (cmask pL250) (hmask pL250) 1 249 (true, (init pL250), (init pL250))) ∧ ptTest pL250 (runFrom pL250 (fmask pL250) (cmask pL250) (hmask pL250) 1 249 (true, (init pL250), (init pL250))) 250 125 false = true :=
  fin_run (runOK_init (prmOK_of_and L250_fin) true) (by decide) rfl L250_fin ptTest_fst
theorem H250_fin : (prmOK pH250 250 && ptTest pH250 (runFrom pH250 (fmask pH250) (cmask pH250) (hmask pH250) 1 249 (true, (init pH250), (init pH250))) 250 125 true) = true := by
  decide +kernel
theorem H250_ok : RunOK pH250 250 (runFrom pH250 (fmask pH250) (cmask pH250) (hmask pH250) 1 249 (true, (init pH250), (init pH250))) ∧ ptTest pH250 (runFrom pH250 (fmask pH250) (cmask pH250) (hmask pH250) 1 249 (true, (init pH250), (init pH250))) 250 125 true = true :=
  fin_run (runOK_init (prmOK_of_and H250_fin) true) (by decide) rfl H250_fin ptTest_fst
theorem I250_fin : (prmOK pI250 250 && intTest pI250 (runFrom pI250 (fmask pI250) (cmask pI250) (hmask pI250) 1 249 (true, (init pI250), (init pI250))) 250 11 true) = true := by
  decide +kernel
theorem I250_ok : RunOK pI250 250 (runFrom pI250 (fmask pI250) (cmask pI250) (hmask pI250) 1 249 (true, (init pI250), (init pI250))) ∧ intTest pI250 (runFrom pI250 (fmask pI250) (cmask pI250) (hmask pI250) 1 249 (true, (init pI250), (init pI250))) 250 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I250_fin) true) (by decide) rfl I250_fin intTest_fst
theorem link250 : linkOK pL250 pH250 pI250 = true := by decide +kernel
theorem cvx250 : ConvexBetweenHumps 250 :=
  cvx_of L250_ok H250_ok I250_ok link250 (by decide)
theorem cenlink250 : cenLinkOK pI250 250 = true := by decide +kernel
theorem cen250 : CenterUniqueMin 250 ∧ DipHyp 250 ∧ OnePointHyps 250 :=
  cen_of L250_ok H250_ok I250_ok link250 cenlink250

/-! ### `N = 251` -/

def pL251 : Prm := ⟨64, 30, 31, 253, 11, 18446744073709551616, 496783535834094721, 496783535834094721⟩
def pH251 : Prm := ⟨64, 30, 31, 253, 11, 18446744073709551616, 496801128020139137, 496801128020139137⟩
def pI251 : Prm := ⟨55, 27, 25, 253, 11, 18446744073709551616, 496783535834094721, 496801128020139137⟩
theorem L251_fin : (prmOK pL251 251 && ptTest pL251 (runFrom pL251 (fmask pL251) (cmask pL251) (hmask pL251) 1 250 (true, (init pL251), (init pL251))) 251 126 false) = true := by
  decide +kernel
theorem L251_ok : RunOK pL251 251 (runFrom pL251 (fmask pL251) (cmask pL251) (hmask pL251) 1 250 (true, (init pL251), (init pL251))) ∧ ptTest pL251 (runFrom pL251 (fmask pL251) (cmask pL251) (hmask pL251) 1 250 (true, (init pL251), (init pL251))) 251 126 false = true :=
  fin_run (runOK_init (prmOK_of_and L251_fin) true) (by decide) rfl L251_fin ptTest_fst
theorem H251_fin : (prmOK pH251 251 && ptTest pH251 (runFrom pH251 (fmask pH251) (cmask pH251) (hmask pH251) 1 250 (true, (init pH251), (init pH251))) 251 126 true) = true := by
  decide +kernel
theorem H251_ok : RunOK pH251 251 (runFrom pH251 (fmask pH251) (cmask pH251) (hmask pH251) 1 250 (true, (init pH251), (init pH251))) ∧ ptTest pH251 (runFrom pH251 (fmask pH251) (cmask pH251) (hmask pH251) 1 250 (true, (init pH251), (init pH251))) 251 126 true = true :=
  fin_run (runOK_init (prmOK_of_and H251_fin) true) (by decide) rfl H251_fin ptTest_fst
theorem I251_fin : (prmOK pI251 251 && intTest pI251 (runFrom pI251 (fmask pI251) (cmask pI251) (hmask pI251) 1 250 (true, (init pI251), (init pI251))) 251 11 false) = true := by
  decide +kernel
theorem I251_ok : RunOK pI251 251 (runFrom pI251 (fmask pI251) (cmask pI251) (hmask pI251) 1 250 (true, (init pI251), (init pI251))) ∧ intTest pI251 (runFrom pI251 (fmask pI251) (cmask pI251) (hmask pI251) 1 250 (true, (init pI251), (init pI251))) 251 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I251_fin) true) (by decide) rfl I251_fin intTest_fst
theorem link251 : linkOK pL251 pH251 pI251 = true := by decide +kernel
theorem cvx251 : ConvexBetweenHumps 251 :=
  cvx_of L251_ok H251_ok I251_ok link251 (by decide)

/-! ### `N = 252` -/

def pL252 : Prm := ⟨64, 30, 31, 254, 11, 18446744073709551616, 495355563608388173, 495355563608388173⟩
def pH252 : Prm := ⟨64, 30, 31, 254, 11, 18446744073709551616, 495373155794432589, 495373155794432589⟩
def pI252 : Prm := ⟨55, 27, 25, 254, 11, 18446744073709551616, 495355563608388173, 495373155794432589⟩
theorem L252_fin : (prmOK pL252 252 && ptTest pL252 (runFrom pL252 (fmask pL252) (cmask pL252) (hmask pL252) 1 251 (true, (init pL252), (init pL252))) 252 126 false) = true := by
  decide +kernel
theorem L252_ok : RunOK pL252 252 (runFrom pL252 (fmask pL252) (cmask pL252) (hmask pL252) 1 251 (true, (init pL252), (init pL252))) ∧ ptTest pL252 (runFrom pL252 (fmask pL252) (cmask pL252) (hmask pL252) 1 251 (true, (init pL252), (init pL252))) 252 126 false = true :=
  fin_run (runOK_init (prmOK_of_and L252_fin) true) (by decide) rfl L252_fin ptTest_fst
theorem H252_fin : (prmOK pH252 252 && ptTest pH252 (runFrom pH252 (fmask pH252) (cmask pH252) (hmask pH252) 1 251 (true, (init pH252), (init pH252))) 252 126 true) = true := by
  decide +kernel
theorem H252_ok : RunOK pH252 252 (runFrom pH252 (fmask pH252) (cmask pH252) (hmask pH252) 1 251 (true, (init pH252), (init pH252))) ∧ ptTest pH252 (runFrom pH252 (fmask pH252) (cmask pH252) (hmask pH252) 1 251 (true, (init pH252), (init pH252))) 252 126 true = true :=
  fin_run (runOK_init (prmOK_of_and H252_fin) true) (by decide) rfl H252_fin ptTest_fst
theorem I252_fin : (prmOK pI252 252 && intTest pI252 (runFrom pI252 (fmask pI252) (cmask pI252) (hmask pI252) 1 251 (true, (init pI252), (init pI252))) 252 11 true) = true := by
  decide +kernel
theorem I252_ok : RunOK pI252 252 (runFrom pI252 (fmask pI252) (cmask pI252) (hmask pI252) 1 251 (true, (init pI252), (init pI252))) ∧ intTest pI252 (runFrom pI252 (fmask pI252) (cmask pI252) (hmask pI252) 1 251 (true, (init pI252), (init pI252))) 252 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I252_fin) true) (by decide) rfl I252_fin intTest_fst
theorem link252 : linkOK pL252 pH252 pI252 = true := by decide +kernel
theorem cvx252 : ConvexBetweenHumps 252 :=
  cvx_of L252_ok H252_ok I252_ok link252 (by decide)
theorem cenlink252 : cenLinkOK pI252 252 = true := by decide +kernel
theorem cen252 : CenterUniqueMin 252 ∧ DipHyp 252 ∧ OnePointHyps 252 :=
  cen_of L252_ok H252_ok I252_ok link252 cenlink252

/-! ### `N = 253` -/

def pL253 : Prm := ⟨64, 30, 31, 255, 11, 18446744073709551616, 493929217314823007, 493929217314823007⟩
def pH253 : Prm := ⟨64, 30, 31, 255, 11, 18446744073709551616, 493946809500867423, 493946809500867423⟩
def pI253 : Prm := ⟨55, 27, 25, 255, 11, 18446744073709551616, 493929217314823007, 493946809500867423⟩
theorem L253_fin : (prmOK pL253 253 && ptTest pL253 (runFrom pL253 (fmask pL253) (cmask pL253) (hmask pL253) 1 252 (true, (init pL253), (init pL253))) 253 127 false) = true := by
  decide +kernel
theorem L253_ok : RunOK pL253 253 (runFrom pL253 (fmask pL253) (cmask pL253) (hmask pL253) 1 252 (true, (init pL253), (init pL253))) ∧ ptTest pL253 (runFrom pL253 (fmask pL253) (cmask pL253) (hmask pL253) 1 252 (true, (init pL253), (init pL253))) 253 127 false = true :=
  fin_run (runOK_init (prmOK_of_and L253_fin) true) (by decide) rfl L253_fin ptTest_fst
theorem H253_fin : (prmOK pH253 253 && ptTest pH253 (runFrom pH253 (fmask pH253) (cmask pH253) (hmask pH253) 1 252 (true, (init pH253), (init pH253))) 253 127 true) = true := by
  decide +kernel
theorem H253_ok : RunOK pH253 253 (runFrom pH253 (fmask pH253) (cmask pH253) (hmask pH253) 1 252 (true, (init pH253), (init pH253))) ∧ ptTest pH253 (runFrom pH253 (fmask pH253) (cmask pH253) (hmask pH253) 1 252 (true, (init pH253), (init pH253))) 253 127 true = true :=
  fin_run (runOK_init (prmOK_of_and H253_fin) true) (by decide) rfl H253_fin ptTest_fst
theorem I253_fin : (prmOK pI253 253 && intTest pI253 (runFrom pI253 (fmask pI253) (cmask pI253) (hmask pI253) 1 252 (true, (init pI253), (init pI253))) 253 11 false) = true := by
  decide +kernel
theorem I253_ok : RunOK pI253 253 (runFrom pI253 (fmask pI253) (cmask pI253) (hmask pI253) 1 252 (true, (init pI253), (init pI253))) ∧ intTest pI253 (runFrom pI253 (fmask pI253) (cmask pI253) (hmask pI253) 1 252 (true, (init pI253), (init pI253))) 253 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I253_fin) true) (by decide) rfl I253_fin intTest_fst
theorem link253 : linkOK pL253 pH253 pI253 = true := by decide +kernel
theorem cvx253 : ConvexBetweenHumps 253 :=
  cvx_of L253_ok H253_ok I253_ok link253 (by decide)

/-! ### `N = 254` -/

def pL254 : Prm := ⟨64, 30, 31, 256, 11, 18446744073709551616, 492519588108974470, 492519588108974470⟩
def pH254 : Prm := ⟨64, 30, 31, 256, 11, 18446744073709551616, 492537180295018886, 492537180295018886⟩
def pI254 : Prm := ⟨55, 27, 25, 256, 11, 18446744073709551616, 492519588108974470, 492537180295018886⟩
theorem L254_fin : (prmOK pL254 254 && ptTest pL254 (runFrom pL254 (fmask pL254) (cmask pL254) (hmask pL254) 1 253 (true, (init pL254), (init pL254))) 254 127 false) = true := by
  decide +kernel
theorem L254_ok : RunOK pL254 254 (runFrom pL254 (fmask pL254) (cmask pL254) (hmask pL254) 1 253 (true, (init pL254), (init pL254))) ∧ ptTest pL254 (runFrom pL254 (fmask pL254) (cmask pL254) (hmask pL254) 1 253 (true, (init pL254), (init pL254))) 254 127 false = true :=
  fin_run (runOK_init (prmOK_of_and L254_fin) true) (by decide) rfl L254_fin ptTest_fst
theorem H254_fin : (prmOK pH254 254 && ptTest pH254 (runFrom pH254 (fmask pH254) (cmask pH254) (hmask pH254) 1 253 (true, (init pH254), (init pH254))) 254 127 true) = true := by
  decide +kernel
theorem H254_ok : RunOK pH254 254 (runFrom pH254 (fmask pH254) (cmask pH254) (hmask pH254) 1 253 (true, (init pH254), (init pH254))) ∧ ptTest pH254 (runFrom pH254 (fmask pH254) (cmask pH254) (hmask pH254) 1 253 (true, (init pH254), (init pH254))) 254 127 true = true :=
  fin_run (runOK_init (prmOK_of_and H254_fin) true) (by decide) rfl H254_fin ptTest_fst
theorem I254_fin : (prmOK pI254 254 && intTest pI254 (runFrom pI254 (fmask pI254) (cmask pI254) (hmask pI254) 1 253 (true, (init pI254), (init pI254))) 254 11 true) = true := by
  decide +kernel
theorem I254_ok : RunOK pI254 254 (runFrom pI254 (fmask pI254) (cmask pI254) (hmask pI254) 1 253 (true, (init pI254), (init pI254))) ∧ intTest pI254 (runFrom pI254 (fmask pI254) (cmask pI254) (hmask pI254) 1 253 (true, (init pI254), (init pI254))) 254 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I254_fin) true) (by decide) rfl I254_fin intTest_fst
theorem link254 : linkOK pL254 pH254 pI254 = true := by decide +kernel
theorem cvx254 : ConvexBetweenHumps 254 :=
  cvx_of L254_ok H254_ok I254_ok link254 (by decide)
theorem cenlink254 : cenLinkOK pI254 254 = true := by decide +kernel
theorem cen254 : CenterUniqueMin 254 ∧ DipHyp 254 ∧ OnePointHyps 254 :=
  cen_of L254_ok H254_ok I254_ok link254 cenlink254

/-! ### `N = 255` -/

def pL255 : Prm := ⟨64, 30, 31, 257, 11, 18446744073709551616, 491111577070645353, 491111577070645353⟩
def pH255 : Prm := ⟨64, 30, 31, 257, 11, 18446744073709551616, 491129169256689769, 491129169256689769⟩
def pI255 : Prm := ⟨55, 27, 25, 257, 11, 18446744073709551616, 491111577070645353, 491129169256689769⟩
theorem L255_fin : (prmOK pL255 255 && ptTest pL255 (runFrom pL255 (fmask pL255) (cmask pL255) (hmask pL255) 1 254 (true, (init pL255), (init pL255))) 255 128 false) = true := by
  decide +kernel
theorem L255_ok : RunOK pL255 255 (runFrom pL255 (fmask pL255) (cmask pL255) (hmask pL255) 1 254 (true, (init pL255), (init pL255))) ∧ ptTest pL255 (runFrom pL255 (fmask pL255) (cmask pL255) (hmask pL255) 1 254 (true, (init pL255), (init pL255))) 255 128 false = true :=
  fin_run (runOK_init (prmOK_of_and L255_fin) true) (by decide) rfl L255_fin ptTest_fst
theorem H255_fin : (prmOK pH255 255 && ptTest pH255 (runFrom pH255 (fmask pH255) (cmask pH255) (hmask pH255) 1 254 (true, (init pH255), (init pH255))) 255 128 true) = true := by
  decide +kernel
theorem H255_ok : RunOK pH255 255 (runFrom pH255 (fmask pH255) (cmask pH255) (hmask pH255) 1 254 (true, (init pH255), (init pH255))) ∧ ptTest pH255 (runFrom pH255 (fmask pH255) (cmask pH255) (hmask pH255) 1 254 (true, (init pH255), (init pH255))) 255 128 true = true :=
  fin_run (runOK_init (prmOK_of_and H255_fin) true) (by decide) rfl H255_fin ptTest_fst
theorem I255_fin : (prmOK pI255 255 && intTest pI255 (runFrom pI255 (fmask pI255) (cmask pI255) (hmask pI255) 1 254 (true, (init pI255), (init pI255))) 255 11 false) = true := by
  decide +kernel
theorem I255_ok : RunOK pI255 255 (runFrom pI255 (fmask pI255) (cmask pI255) (hmask pI255) 1 254 (true, (init pI255), (init pI255))) ∧ intTest pI255 (runFrom pI255 (fmask pI255) (cmask pI255) (hmask pI255) 1 254 (true, (init pI255), (init pI255))) 255 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I255_fin) true) (by decide) rfl I255_fin intTest_fst
theorem link255 : linkOK pL255 pH255 pI255 = true := by decide +kernel
theorem cvx255 : ConvexBetweenHumps 255 :=
  cvx_of L255_ok H255_ok I255_ok link255 (by decide)

/-! ### `N = 256` -/

def pL256 : Prm := ⟨64, 30, 31, 258, 11, 18446744073709551616, 489719922967166628, 489719922967166628⟩
def pH256 : Prm := ⟨64, 30, 31, 258, 11, 18446744073709551616, 489737515153211044, 489737515153211044⟩
def pI256 : Prm := ⟨55, 27, 25, 258, 11, 18446744073709551616, 489719922967166628, 489737515153211044⟩
theorem L256_fin : (prmOK pL256 256 && ptTest pL256 (runFrom pL256 (fmask pL256) (cmask pL256) (hmask pL256) 1 255 (true, (init pL256), (init pL256))) 256 128 false) = true := by
  decide +kernel
theorem L256_ok : RunOK pL256 256 (runFrom pL256 (fmask pL256) (cmask pL256) (hmask pL256) 1 255 (true, (init pL256), (init pL256))) ∧ ptTest pL256 (runFrom pL256 (fmask pL256) (cmask pL256) (hmask pL256) 1 255 (true, (init pL256), (init pL256))) 256 128 false = true :=
  fin_run (runOK_init (prmOK_of_and L256_fin) true) (by decide) rfl L256_fin ptTest_fst
theorem H256_fin : (prmOK pH256 256 && ptTest pH256 (runFrom pH256 (fmask pH256) (cmask pH256) (hmask pH256) 1 255 (true, (init pH256), (init pH256))) 256 128 true) = true := by
  decide +kernel
theorem H256_ok : RunOK pH256 256 (runFrom pH256 (fmask pH256) (cmask pH256) (hmask pH256) 1 255 (true, (init pH256), (init pH256))) ∧ ptTest pH256 (runFrom pH256 (fmask pH256) (cmask pH256) (hmask pH256) 1 255 (true, (init pH256), (init pH256))) 256 128 true = true :=
  fin_run (runOK_init (prmOK_of_and H256_fin) true) (by decide) rfl H256_fin ptTest_fst
theorem I256_fin : (prmOK pI256 256 && intTest pI256 (runFrom pI256 (fmask pI256) (cmask pI256) (hmask pI256) 1 255 (true, (init pI256), (init pI256))) 256 11 true) = true := by
  decide +kernel
theorem I256_ok : RunOK pI256 256 (runFrom pI256 (fmask pI256) (cmask pI256) (hmask pI256) 1 255 (true, (init pI256), (init pI256))) ∧ intTest pI256 (runFrom pI256 (fmask pI256) (cmask pI256) (hmask pI256) 1 255 (true, (init pI256), (init pI256))) 256 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I256_fin) true) (by decide) rfl I256_fin intTest_fst
theorem link256 : linkOK pL256 pH256 pI256 = true := by decide +kernel
theorem cvx256 : ConvexBetweenHumps 256 :=
  cvx_of L256_ok H256_ok I256_ok link256 (by decide)
theorem cenlink256 : cenLinkOK pI256 256 = true := by decide +kernel
theorem cen256 : CenterUniqueMin 256 ∧ DipHyp 256 ∧ OnePointHyps 256 :=
  cen_of L256_ok H256_ok I256_ok link256 cenlink256

/-! ### `N = 257` -/

def pL257 : Prm := ⟨64, 30, 31, 259, 11, 18446744073709551616, 488329878892983453, 488329878892983453⟩
def pH257 : Prm := ⟨64, 30, 31, 259, 11, 18446744073709551616, 488347471079027869, 488347471079027869⟩
def pI257 : Prm := ⟨55, 27, 25, 259, 11, 18446744073709551616, 488329878892983453, 488347471079027869⟩
theorem L257_fin : (prmOK pL257 257 && ptTest pL257 (runFrom pL257 (fmask pL257) (cmask pL257) (hmask pL257) 1 256 (true, (init pL257), (init pL257))) 257 129 false) = true := by
  decide +kernel
theorem L257_ok : RunOK pL257 257 (runFrom pL257 (fmask pL257) (cmask pL257) (hmask pL257) 1 256 (true, (init pL257), (init pL257))) ∧ ptTest pL257 (runFrom pL257 (fmask pL257) (cmask pL257) (hmask pL257) 1 256 (true, (init pL257), (init pL257))) 257 129 false = true :=
  fin_run (runOK_init (prmOK_of_and L257_fin) true) (by decide) rfl L257_fin ptTest_fst
theorem H257_fin : (prmOK pH257 257 && ptTest pH257 (runFrom pH257 (fmask pH257) (cmask pH257) (hmask pH257) 1 256 (true, (init pH257), (init pH257))) 257 129 true) = true := by
  decide +kernel
theorem H257_ok : RunOK pH257 257 (runFrom pH257 (fmask pH257) (cmask pH257) (hmask pH257) 1 256 (true, (init pH257), (init pH257))) ∧ ptTest pH257 (runFrom pH257 (fmask pH257) (cmask pH257) (hmask pH257) 1 256 (true, (init pH257), (init pH257))) 257 129 true = true :=
  fin_run (runOK_init (prmOK_of_and H257_fin) true) (by decide) rfl H257_fin ptTest_fst
theorem I257_fin : (prmOK pI257 257 && intTest pI257 (runFrom pI257 (fmask pI257) (cmask pI257) (hmask pI257) 1 256 (true, (init pI257), (init pI257))) 257 11 false) = true := by
  decide +kernel
theorem I257_ok : RunOK pI257 257 (runFrom pI257 (fmask pI257) (cmask pI257) (hmask pI257) 1 256 (true, (init pI257), (init pI257))) ∧ intTest pI257 (runFrom pI257 (fmask pI257) (cmask pI257) (hmask pI257) 1 256 (true, (init pI257), (init pI257))) 257 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I257_fin) true) (by decide) rfl I257_fin intTest_fst
theorem link257 : linkOK pL257 pH257 pI257 = true := by decide +kernel
theorem cvx257 : ConvexBetweenHumps 257 :=
  cvx_of L257_ok H257_ok I257_ok link257 (by decide)

/-! ### `N = 258` -/

def pL258 : Prm := ⟨64, 30, 31, 260, 11, 18446744073709551616, 486955842008492782, 486955842008492782⟩
def pH258 : Prm := ⟨64, 30, 31, 260, 11, 18446744073709551616, 486973434194537198, 486973434194537198⟩
def pI258 : Prm := ⟨55, 27, 25, 260, 11, 18446744073709551616, 486955842008492782, 486973434194537198⟩
theorem L258_fin : (prmOK pL258 258 && ptTest pL258 (runFrom pL258 (fmask pL258) (cmask pL258) (hmask pL258) 1 257 (true, (init pL258), (init pL258))) 258 129 false) = true := by
  decide +kernel
theorem L258_ok : RunOK pL258 258 (runFrom pL258 (fmask pL258) (cmask pL258) (hmask pL258) 1 257 (true, (init pL258), (init pL258))) ∧ ptTest pL258 (runFrom pL258 (fmask pL258) (cmask pL258) (hmask pL258) 1 257 (true, (init pL258), (init pL258))) 258 129 false = true :=
  fin_run (runOK_init (prmOK_of_and L258_fin) true) (by decide) rfl L258_fin ptTest_fst
theorem H258_fin : (prmOK pH258 258 && ptTest pH258 (runFrom pH258 (fmask pH258) (cmask pH258) (hmask pH258) 1 257 (true, (init pH258), (init pH258))) 258 129 true) = true := by
  decide +kernel
theorem H258_ok : RunOK pH258 258 (runFrom pH258 (fmask pH258) (cmask pH258) (hmask pH258) 1 257 (true, (init pH258), (init pH258))) ∧ ptTest pH258 (runFrom pH258 (fmask pH258) (cmask pH258) (hmask pH258) 1 257 (true, (init pH258), (init pH258))) 258 129 true = true :=
  fin_run (runOK_init (prmOK_of_and H258_fin) true) (by decide) rfl H258_fin ptTest_fst
theorem I258_fin : (prmOK pI258 258 && intTest pI258 (runFrom pI258 (fmask pI258) (cmask pI258) (hmask pI258) 1 257 (true, (init pI258), (init pI258))) 258 11 true) = true := by
  decide +kernel
theorem I258_ok : RunOK pI258 258 (runFrom pI258 (fmask pI258) (cmask pI258) (hmask pI258) 1 257 (true, (init pI258), (init pI258))) ∧ intTest pI258 (runFrom pI258 (fmask pI258) (cmask pI258) (hmask pI258) 1 257 (true, (init pI258), (init pI258))) 258 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I258_fin) true) (by decide) rfl I258_fin intTest_fst
theorem link258 : linkOK pL258 pH258 pI258 = true := by decide +kernel
theorem cvx258 : ConvexBetweenHumps 258 :=
  cvx_of L258_ok H258_ok I258_ok link258 (by decide)
theorem cenlink258 : cenLinkOK pI258 258 = true := by decide +kernel
theorem cen258 : CenterUniqueMin 258 ∧ DipHyp 258 ∧ OnePointHyps 258 :=
  cen_of L258_ok H258_ok I258_ok link258 cenlink258

/-! ### `N = 259` -/

def pL259 : Prm := ⟨64, 30, 31, 261, 11, 18446744073709551616, 485583406671798329, 485583406671798329⟩
def pH259 : Prm := ⟨64, 30, 31, 261, 11, 18446744073709551616, 485600998857842745, 485600998857842745⟩
def pI259 : Prm := ⟨55, 27, 25, 261, 11, 18446744073709551616, 485583406671798329, 485600998857842745⟩
theorem L259_fin : (prmOK pL259 259 && ptTest pL259 (runFrom pL259 (fmask pL259) (cmask pL259) (hmask pL259) 1 258 (true, (init pL259), (init pL259))) 259 130 false) = true := by
  decide +kernel
theorem L259_ok : RunOK pL259 259 (runFrom pL259 (fmask pL259) (cmask pL259) (hmask pL259) 1 258 (true, (init pL259), (init pL259))) ∧ ptTest pL259 (runFrom pL259 (fmask pL259) (cmask pL259) (hmask pL259) 1 258 (true, (init pL259), (init pL259))) 259 130 false = true :=
  fin_run (runOK_init (prmOK_of_and L259_fin) true) (by decide) rfl L259_fin ptTest_fst
theorem H259_fin : (prmOK pH259 259 && ptTest pH259 (runFrom pH259 (fmask pH259) (cmask pH259) (hmask pH259) 1 258 (true, (init pH259), (init pH259))) 259 130 true) = true := by
  decide +kernel
theorem H259_ok : RunOK pH259 259 (runFrom pH259 (fmask pH259) (cmask pH259) (hmask pH259) 1 258 (true, (init pH259), (init pH259))) ∧ ptTest pH259 (runFrom pH259 (fmask pH259) (cmask pH259) (hmask pH259) 1 258 (true, (init pH259), (init pH259))) 259 130 true = true :=
  fin_run (runOK_init (prmOK_of_and H259_fin) true) (by decide) rfl H259_fin ptTest_fst
theorem I259_fin : (prmOK pI259 259 && intTest pI259 (runFrom pI259 (fmask pI259) (cmask pI259) (hmask pI259) 1 258 (true, (init pI259), (init pI259))) 259 11 false) = true := by
  decide +kernel
theorem I259_ok : RunOK pI259 259 (runFrom pI259 (fmask pI259) (cmask pI259) (hmask pI259) 1 258 (true, (init pI259), (init pI259))) ∧ intTest pI259 (runFrom pI259 (fmask pI259) (cmask pI259) (hmask pI259) 1 258 (true, (init pI259), (init pI259))) 259 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I259_fin) true) (by decide) rfl I259_fin intTest_fst
theorem link259 : linkOK pL259 pH259 pI259 = true := by decide +kernel
theorem cvx259 : ConvexBetweenHumps 259 :=
  cvx_of L259_ok H259_ok I259_ok link259 (by decide)

/-! ### `N = 260` -/

def pL260 : Prm := ⟨64, 30, 31, 262, 11, 18446744073709551616, 484226638811236173, 484226638811236173⟩
def pH260 : Prm := ⟨64, 30, 31, 262, 11, 18446744073709551616, 484244230997280589, 484244230997280589⟩
def pI260 : Prm := ⟨56, 27, 26, 262, 11, 18446744073709551616, 484226638811236173, 484244230997280589⟩
theorem L260_fin : (prmOK pL260 260 && ptTest pL260 (runFrom pL260 (fmask pL260) (cmask pL260) (hmask pL260) 1 259 (true, (init pL260), (init pL260))) 260 130 false) = true := by
  decide +kernel
theorem L260_ok : RunOK pL260 260 (runFrom pL260 (fmask pL260) (cmask pL260) (hmask pL260) 1 259 (true, (init pL260), (init pL260))) ∧ ptTest pL260 (runFrom pL260 (fmask pL260) (cmask pL260) (hmask pL260) 1 259 (true, (init pL260), (init pL260))) 260 130 false = true :=
  fin_run (runOK_init (prmOK_of_and L260_fin) true) (by decide) rfl L260_fin ptTest_fst
theorem H260_fin : (prmOK pH260 260 && ptTest pH260 (runFrom pH260 (fmask pH260) (cmask pH260) (hmask pH260) 1 259 (true, (init pH260), (init pH260))) 260 130 true) = true := by
  decide +kernel
theorem H260_ok : RunOK pH260 260 (runFrom pH260 (fmask pH260) (cmask pH260) (hmask pH260) 1 259 (true, (init pH260), (init pH260))) ∧ ptTest pH260 (runFrom pH260 (fmask pH260) (cmask pH260) (hmask pH260) 1 259 (true, (init pH260), (init pH260))) 260 130 true = true :=
  fin_run (runOK_init (prmOK_of_and H260_fin) true) (by decide) rfl H260_fin ptTest_fst
theorem I260_fin : (prmOK pI260 260 && intTest pI260 (runFrom pI260 (fmask pI260) (cmask pI260) (hmask pI260) 1 259 (true, (init pI260), (init pI260))) 260 11 true) = true := by
  decide +kernel
theorem I260_ok : RunOK pI260 260 (runFrom pI260 (fmask pI260) (cmask pI260) (hmask pI260) 1 259 (true, (init pI260), (init pI260))) ∧ intTest pI260 (runFrom pI260 (fmask pI260) (cmask pI260) (hmask pI260) 1 259 (true, (init pI260), (init pI260))) 260 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I260_fin) true) (by decide) rfl I260_fin intTest_fst
theorem link260 : linkOK pL260 pH260 pI260 = true := by decide +kernel
theorem cvx260 : ConvexBetweenHumps 260 :=
  cvx_of L260_ok H260_ok I260_ok link260 (by decide)
theorem cenlink260 : cenLinkOK pI260 260 = true := by decide +kernel
theorem cen260 : CenterUniqueMin 260 ∧ DipHyp 260 ∧ OnePointHyps 260 :=
  cen_of L260_ok H260_ok I260_ok link260 cenlink260

/-! ### `N = 261` -/

def pL261 : Prm := ⟨64, 30, 31, 263, 11, 18446744073709551616, 482871463702195665, 482871463702195665⟩
def pH261 : Prm := ⟨64, 30, 31, 263, 11, 18446744073709551616, 482889055888240081, 482889055888240081⟩
def pI261 : Prm := ⟨56, 27, 26, 263, 11, 18446744073709551616, 482871463702195665, 482889055888240081⟩
theorem L261_fin : (prmOK pL261 261 && ptTest pL261 (runFrom pL261 (fmask pL261) (cmask pL261) (hmask pL261) 1 260 (true, (init pL261), (init pL261))) 261 131 false) = true := by
  decide +kernel
theorem L261_ok : RunOK pL261 261 (runFrom pL261 (fmask pL261) (cmask pL261) (hmask pL261) 1 260 (true, (init pL261), (init pL261))) ∧ ptTest pL261 (runFrom pL261 (fmask pL261) (cmask pL261) (hmask pL261) 1 260 (true, (init pL261), (init pL261))) 261 131 false = true :=
  fin_run (runOK_init (prmOK_of_and L261_fin) true) (by decide) rfl L261_fin ptTest_fst
theorem H261_fin : (prmOK pH261 261 && ptTest pH261 (runFrom pH261 (fmask pH261) (cmask pH261) (hmask pH261) 1 260 (true, (init pH261), (init pH261))) 261 131 true) = true := by
  decide +kernel
theorem H261_ok : RunOK pH261 261 (runFrom pH261 (fmask pH261) (cmask pH261) (hmask pH261) 1 260 (true, (init pH261), (init pH261))) ∧ ptTest pH261 (runFrom pH261 (fmask pH261) (cmask pH261) (hmask pH261) 1 260 (true, (init pH261), (init pH261))) 261 131 true = true :=
  fin_run (runOK_init (prmOK_of_and H261_fin) true) (by decide) rfl H261_fin ptTest_fst
theorem I261_fin : (prmOK pI261 261 && intTest pI261 (runFrom pI261 (fmask pI261) (cmask pI261) (hmask pI261) 1 260 (true, (init pI261), (init pI261))) 261 11 false) = true := by
  decide +kernel
theorem I261_ok : RunOK pI261 261 (runFrom pI261 (fmask pI261) (cmask pI261) (hmask pI261) 1 260 (true, (init pI261), (init pI261))) ∧ intTest pI261 (runFrom pI261 (fmask pI261) (cmask pI261) (hmask pI261) 1 260 (true, (init pI261), (init pI261))) 261 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I261_fin) true) (by decide) rfl I261_fin intTest_fst
theorem link261 : linkOK pL261 pH261 pI261 = true := by decide +kernel
theorem cvx261 : ConvexBetweenHumps 261 :=
  cvx_of L261_ok H261_ok I261_ok link261 (by decide)

/-! ### `N = 262` -/

def pL262 : Prm := ⟨64, 30, 31, 264, 11, 18446744073709551616, 481531626027613416, 481531626027613416⟩
def pH262 : Prm := ⟨64, 30, 31, 264, 11, 18446744073709551616, 481549218213657832, 481549218213657832⟩
def pI262 : Prm := ⟨56, 27, 26, 264, 11, 18446744073709551616, 481531626027613416, 481549218213657832⟩
theorem L262_fin : (prmOK pL262 262 && ptTest pL262 (runFrom pL262 (fmask pL262) (cmask pL262) (hmask pL262) 1 261 (true, (init pL262), (init pL262))) 262 131 false) = true := by
  decide +kernel
theorem L262_ok : RunOK pL262 262 (runFrom pL262 (fmask pL262) (cmask pL262) (hmask pL262) 1 261 (true, (init pL262), (init pL262))) ∧ ptTest pL262 (runFrom pL262 (fmask pL262) (cmask pL262) (hmask pL262) 1 261 (true, (init pL262), (init pL262))) 262 131 false = true :=
  fin_run (runOK_init (prmOK_of_and L262_fin) true) (by decide) rfl L262_fin ptTest_fst
theorem H262_fin : (prmOK pH262 262 && ptTest pH262 (runFrom pH262 (fmask pH262) (cmask pH262) (hmask pH262) 1 261 (true, (init pH262), (init pH262))) 262 131 true) = true := by
  decide +kernel
theorem H262_ok : RunOK pH262 262 (runFrom pH262 (fmask pH262) (cmask pH262) (hmask pH262) 1 261 (true, (init pH262), (init pH262))) ∧ ptTest pH262 (runFrom pH262 (fmask pH262) (cmask pH262) (hmask pH262) 1 261 (true, (init pH262), (init pH262))) 262 131 true = true :=
  fin_run (runOK_init (prmOK_of_and H262_fin) true) (by decide) rfl H262_fin ptTest_fst
theorem I262_fin : (prmOK pI262 262 && intTest pI262 (runFrom pI262 (fmask pI262) (cmask pI262) (hmask pI262) 1 261 (true, (init pI262), (init pI262))) 262 11 true) = true := by
  decide +kernel
theorem I262_ok : RunOK pI262 262 (runFrom pI262 (fmask pI262) (cmask pI262) (hmask pI262) 1 261 (true, (init pI262), (init pI262))) ∧ intTest pI262 (runFrom pI262 (fmask pI262) (cmask pI262) (hmask pI262) 1 261 (true, (init pI262), (init pI262))) 262 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I262_fin) true) (by decide) rfl I262_fin intTest_fst
theorem link262 : linkOK pL262 pH262 pI262 = true := by decide +kernel
theorem cvx262 : ConvexBetweenHumps 262 :=
  cvx_of L262_ok H262_ok I262_ok link262 (by decide)
theorem cenlink262 : cenLinkOK pI262 262 = true := by decide +kernel
theorem cen262 : CenterUniqueMin 262 ∧ DipHyp 262 ∧ OnePointHyps 262 :=
  cen_of L262_ok H262_ok I262_ok link262 cenlink262

/-! ### `N = 263` -/

def pL263 : Prm := ⟨64, 30, 31, 265, 11, 18446744073709551616, 480193372020140102, 480193372020140102⟩
def pH263 : Prm := ⟨64, 30, 31, 265, 11, 18446744073709551616, 480210964206184518, 480210964206184518⟩
def pI263 : Prm := ⟨56, 27, 26, 265, 11, 18446744073709551616, 480193372020140102, 480210964206184518⟩
theorem L263_fin : (prmOK pL263 263 && ptTest pL263 (runFrom pL263 (fmask pL263) (cmask pL263) (hmask pL263) 1 262 (true, (init pL263), (init pL263))) 263 132 false) = true := by
  decide +kernel
theorem L263_ok : RunOK pL263 263 (runFrom pL263 (fmask pL263) (cmask pL263) (hmask pL263) 1 262 (true, (init pL263), (init pL263))) ∧ ptTest pL263 (runFrom pL263 (fmask pL263) (cmask pL263) (hmask pL263) 1 262 (true, (init pL263), (init pL263))) 263 132 false = true :=
  fin_run (runOK_init (prmOK_of_and L263_fin) true) (by decide) rfl L263_fin ptTest_fst
theorem H263_fin : (prmOK pH263 263 && ptTest pH263 (runFrom pH263 (fmask pH263) (cmask pH263) (hmask pH263) 1 262 (true, (init pH263), (init pH263))) 263 132 true) = true := by
  decide +kernel
theorem H263_ok : RunOK pH263 263 (runFrom pH263 (fmask pH263) (cmask pH263) (hmask pH263) 1 262 (true, (init pH263), (init pH263))) ∧ ptTest pH263 (runFrom pH263 (fmask pH263) (cmask pH263) (hmask pH263) 1 262 (true, (init pH263), (init pH263))) 263 132 true = true :=
  fin_run (runOK_init (prmOK_of_and H263_fin) true) (by decide) rfl H263_fin ptTest_fst
theorem I263_fin : (prmOK pI263 263 && intTest pI263 (runFrom pI263 (fmask pI263) (cmask pI263) (hmask pI263) 1 262 (true, (init pI263), (init pI263))) 263 11 false) = true := by
  decide +kernel
theorem I263_ok : RunOK pI263 263 (runFrom pI263 (fmask pI263) (cmask pI263) (hmask pI263) 1 262 (true, (init pI263), (init pI263))) ∧ intTest pI263 (runFrom pI263 (fmask pI263) (cmask pI263) (hmask pI263) 1 262 (true, (init pI263), (init pI263))) 263 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I263_fin) true) (by decide) rfl I263_fin intTest_fst
theorem link263 : linkOK pL263 pH263 pI263 = true := by decide +kernel
theorem cvx263 : ConvexBetweenHumps 263 :=
  cvx_of L263_ok H263_ok I263_ok link263 (by decide)

/-! ### `N = 264` -/

def pL264 : Prm := ⟨64, 30, 31, 266, 11, 18446744073709551616, 478870134732954919, 478870134732954919⟩
def pH264 : Prm := ⟨64, 30, 31, 266, 11, 18446744073709551616, 478887726918999335, 478887726918999335⟩
def pI264 : Prm := ⟨56, 27, 26, 266, 11, 18446744073709551616, 478870134732954919, 478887726918999335⟩
theorem L264_fin : (prmOK pL264 264 && ptTest pL264 (runFrom pL264 (fmask pL264) (cmask pL264) (hmask pL264) 1 263 (true, (init pL264), (init pL264))) 264 132 false) = true := by
  decide +kernel
theorem L264_ok : RunOK pL264 264 (runFrom pL264 (fmask pL264) (cmask pL264) (hmask pL264) 1 263 (true, (init pL264), (init pL264))) ∧ ptTest pL264 (runFrom pL264 (fmask pL264) (cmask pL264) (hmask pL264) 1 263 (true, (init pL264), (init pL264))) 264 132 false = true :=
  fin_run (runOK_init (prmOK_of_and L264_fin) true) (by decide) rfl L264_fin ptTest_fst
theorem H264_fin : (prmOK pH264 264 && ptTest pH264 (runFrom pH264 (fmask pH264) (cmask pH264) (hmask pH264) 1 263 (true, (init pH264), (init pH264))) 264 132 true) = true := by
  decide +kernel
theorem H264_ok : RunOK pH264 264 (runFrom pH264 (fmask pH264) (cmask pH264) (hmask pH264) 1 263 (true, (init pH264), (init pH264))) ∧ ptTest pH264 (runFrom pH264 (fmask pH264) (cmask pH264) (hmask pH264) 1 263 (true, (init pH264), (init pH264))) 264 132 true = true :=
  fin_run (runOK_init (prmOK_of_and H264_fin) true) (by decide) rfl H264_fin ptTest_fst
theorem I264_fin : (prmOK pI264 264 && intTest pI264 (runFrom pI264 (fmask pI264) (cmask pI264) (hmask pI264) 1 263 (true, (init pI264), (init pI264))) 264 11 true) = true := by
  decide +kernel
theorem I264_ok : RunOK pI264 264 (runFrom pI264 (fmask pI264) (cmask pI264) (hmask pI264) 1 263 (true, (init pI264), (init pI264))) ∧ intTest pI264 (runFrom pI264 (fmask pI264) (cmask pI264) (hmask pI264) 1 263 (true, (init pI264), (init pI264))) 264 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I264_fin) true) (by decide) rfl I264_fin intTest_fst
theorem link264 : linkOK pL264 pH264 pI264 = true := by decide +kernel
theorem cvx264 : ConvexBetweenHumps 264 :=
  cvx_of L264_ok H264_ok I264_ok link264 (by decide)
theorem cenlink264 : cenLinkOK pI264 264 = true := by decide +kernel
theorem cen264 : CenterUniqueMin 264 ∧ DipHyp 264 ∧ OnePointHyps 264 :=
  cen_of L264_ok H264_ok I264_ok link264 cenlink264

/-! ### `N = 265` -/

def pL265 : Prm := ⟨64, 30, 31, 267, 11, 18446744073709551616, 477548471765396940, 477548471765396940⟩
def pH265 : Prm := ⟨64, 30, 31, 267, 11, 18446744073709551616, 477566063951441356, 477566063951441356⟩
def pI265 : Prm := ⟨56, 27, 26, 267, 11, 18446744073709551616, 477548471765396940, 477566063951441356⟩
theorem L265_fin : (prmOK pL265 265 && ptTest pL265 (runFrom pL265 (fmask pL265) (cmask pL265) (hmask pL265) 1 264 (true, (init pL265), (init pL265))) 265 133 false) = true := by
  decide +kernel
theorem L265_ok : RunOK pL265 265 (runFrom pL265 (fmask pL265) (cmask pL265) (hmask pL265) 1 264 (true, (init pL265), (init pL265))) ∧ ptTest pL265 (runFrom pL265 (fmask pL265) (cmask pL265) (hmask pL265) 1 264 (true, (init pL265), (init pL265))) 265 133 false = true :=
  fin_run (runOK_init (prmOK_of_and L265_fin) true) (by decide) rfl L265_fin ptTest_fst
theorem H265_fin : (prmOK pH265 265 && ptTest pH265 (runFrom pH265 (fmask pH265) (cmask pH265) (hmask pH265) 1 264 (true, (init pH265), (init pH265))) 265 133 true) = true := by
  decide +kernel
theorem H265_ok : RunOK pH265 265 (runFrom pH265 (fmask pH265) (cmask pH265) (hmask pH265) 1 264 (true, (init pH265), (init pH265))) ∧ ptTest pH265 (runFrom pH265 (fmask pH265) (cmask pH265) (hmask pH265) 1 264 (true, (init pH265), (init pH265))) 265 133 true = true :=
  fin_run (runOK_init (prmOK_of_and H265_fin) true) (by decide) rfl H265_fin ptTest_fst
theorem I265_fin : (prmOK pI265 265 && intTest pI265 (runFrom pI265 (fmask pI265) (cmask pI265) (hmask pI265) 1 264 (true, (init pI265), (init pI265))) 265 11 false) = true := by
  decide +kernel
theorem I265_ok : RunOK pI265 265 (runFrom pI265 (fmask pI265) (cmask pI265) (hmask pI265) 1 264 (true, (init pI265), (init pI265))) ∧ intTest pI265 (runFrom pI265 (fmask pI265) (cmask pI265) (hmask pI265) 1 264 (true, (init pI265), (init pI265))) 265 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I265_fin) true) (by decide) rfl I265_fin intTest_fst
theorem link265 : linkOK pL265 pH265 pI265 = true := by decide +kernel
theorem cvx265 : ConvexBetweenHumps 265 :=
  cvx_of L265_ok H265_ok I265_ok link265 (by decide)

/-! ### `N = 266` -/

def pL266 : Prm := ⟨64, 30, 31, 268, 11, 18446744073709551616, 476241513801817555, 476241513801817555⟩
def pH266 : Prm := ⟨64, 30, 31, 268, 11, 18446744073709551616, 476259105987861971, 476259105987861971⟩
def pI266 : Prm := ⟨56, 27, 26, 268, 11, 18446744073709551616, 476241513801817555, 476259105987861971⟩
theorem L266_fin : (prmOK pL266 266 && ptTest pL266 (runFrom pL266 (fmask pL266) (cmask pL266) (hmask pL266) 1 265 (true, (init pL266), (init pL266))) 266 133 false) = true := by
  decide +kernel
theorem L266_ok : RunOK pL266 266 (runFrom pL266 (fmask pL266) (cmask pL266) (hmask pL266) 1 265 (true, (init pL266), (init pL266))) ∧ ptTest pL266 (runFrom pL266 (fmask pL266) (cmask pL266) (hmask pL266) 1 265 (true, (init pL266), (init pL266))) 266 133 false = true :=
  fin_run (runOK_init (prmOK_of_and L266_fin) true) (by decide) rfl L266_fin ptTest_fst
theorem H266_fin : (prmOK pH266 266 && ptTest pH266 (runFrom pH266 (fmask pH266) (cmask pH266) (hmask pH266) 1 265 (true, (init pH266), (init pH266))) 266 133 true) = true := by
  decide +kernel
theorem H266_ok : RunOK pH266 266 (runFrom pH266 (fmask pH266) (cmask pH266) (hmask pH266) 1 265 (true, (init pH266), (init pH266))) ∧ ptTest pH266 (runFrom pH266 (fmask pH266) (cmask pH266) (hmask pH266) 1 265 (true, (init pH266), (init pH266))) 266 133 true = true :=
  fin_run (runOK_init (prmOK_of_and H266_fin) true) (by decide) rfl H266_fin ptTest_fst
theorem I266_fin : (prmOK pI266 266 && intTest pI266 (runFrom pI266 (fmask pI266) (cmask pI266) (hmask pI266) 1 265 (true, (init pI266), (init pI266))) 266 11 true) = true := by
  decide +kernel
theorem I266_ok : RunOK pI266 266 (runFrom pI266 (fmask pI266) (cmask pI266) (hmask pI266) 1 265 (true, (init pI266), (init pI266))) ∧ intTest pI266 (runFrom pI266 (fmask pI266) (cmask pI266) (hmask pI266) 1 265 (true, (init pI266), (init pI266))) 266 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I266_fin) true) (by decide) rfl I266_fin intTest_fst
theorem link266 : linkOK pL266 pH266 pI266 = true := by decide +kernel
theorem cvx266 : ConvexBetweenHumps 266 :=
  cvx_of L266_ok H266_ok I266_ok link266 (by decide)
theorem cenlink266 : cenLinkOK pI266 266 = true := by decide +kernel
theorem cen266 : CenterUniqueMin 266 ∧ DipHyp 266 ∧ OnePointHyps 266 :=
  cen_of L266_ok H266_ok I266_ok link266 cenlink266

/-! ### `N = 267` -/

def pL267 : Prm := ⟨64, 30, 31, 269, 11, 18446744073709551616, 474936120570760436, 474936120570760436⟩
def pH267 : Prm := ⟨64, 30, 31, 269, 11, 18446744073709551616, 474953712756804852, 474953712756804852⟩
def pI267 : Prm := ⟨56, 27, 26, 269, 11, 18446744073709551616, 474936120570760436, 474953712756804852⟩
theorem L267_fin : (prmOK pL267 267 && ptTest pL267 (runFrom pL267 (fmask pL267) (cmask pL267) (hmask pL267) 1 266 (true, (init pL267), (init pL267))) 267 134 false) = true := by
  decide +kernel
theorem L267_ok : RunOK pL267 267 (runFrom pL267 (fmask pL267) (cmask pL267) (hmask pL267) 1 266 (true, (init pL267), (init pL267))) ∧ ptTest pL267 (runFrom pL267 (fmask pL267) (cmask pL267) (hmask pL267) 1 266 (true, (init pL267), (init pL267))) 267 134 false = true :=
  fin_run (runOK_init (prmOK_of_and L267_fin) true) (by decide) rfl L267_fin ptTest_fst
theorem H267_fin : (prmOK pH267 267 && ptTest pH267 (runFrom pH267 (fmask pH267) (cmask pH267) (hmask pH267) 1 266 (true, (init pH267), (init pH267))) 267 134 true) = true := by
  decide +kernel
theorem H267_ok : RunOK pH267 267 (runFrom pH267 (fmask pH267) (cmask pH267) (hmask pH267) 1 266 (true, (init pH267), (init pH267))) ∧ ptTest pH267 (runFrom pH267 (fmask pH267) (cmask pH267) (hmask pH267) 1 266 (true, (init pH267), (init pH267))) 267 134 true = true :=
  fin_run (runOK_init (prmOK_of_and H267_fin) true) (by decide) rfl H267_fin ptTest_fst
theorem I267_fin : (prmOK pI267 267 && intTest pI267 (runFrom pI267 (fmask pI267) (cmask pI267) (hmask pI267) 1 266 (true, (init pI267), (init pI267))) 267 11 false) = true := by
  decide +kernel
theorem I267_ok : RunOK pI267 267 (runFrom pI267 (fmask pI267) (cmask pI267) (hmask pI267) 1 266 (true, (init pI267), (init pI267))) ∧ intTest pI267 (runFrom pI267 (fmask pI267) (cmask pI267) (hmask pI267) 1 266 (true, (init pI267), (init pI267))) 267 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I267_fin) true) (by decide) rfl I267_fin intTest_fst
theorem link267 : linkOK pL267 pH267 pI267 = true := by decide +kernel
theorem cvx267 : ConvexBetweenHumps 267 :=
  cvx_of L267_ok H267_ok I267_ok link267 (by decide)

/-! ### `N = 268` -/

def pL268 : Prm := ⟨64, 30, 31, 270, 11, 18446744073709551616, 473645129309535387, 473645129309535387⟩
def pH268 : Prm := ⟨64, 30, 31, 270, 11, 18446744073709551616, 473662721495579803, 473662721495579803⟩
def pI268 : Prm := ⟨56, 27, 26, 270, 11, 18446744073709551616, 473645129309535387, 473662721495579803⟩
theorem L268_fin : (prmOK pL268 268 && ptTest pL268 (runFrom pL268 (fmask pL268) (cmask pL268) (hmask pL268) 1 267 (true, (init pL268), (init pL268))) 268 134 false) = true := by
  decide +kernel
theorem L268_ok : RunOK pL268 268 (runFrom pL268 (fmask pL268) (cmask pL268) (hmask pL268) 1 267 (true, (init pL268), (init pL268))) ∧ ptTest pL268 (runFrom pL268 (fmask pL268) (cmask pL268) (hmask pL268) 1 267 (true, (init pL268), (init pL268))) 268 134 false = true :=
  fin_run (runOK_init (prmOK_of_and L268_fin) true) (by decide) rfl L268_fin ptTest_fst
theorem H268_fin : (prmOK pH268 268 && ptTest pH268 (runFrom pH268 (fmask pH268) (cmask pH268) (hmask pH268) 1 267 (true, (init pH268), (init pH268))) 268 134 true) = true := by
  decide +kernel
theorem H268_ok : RunOK pH268 268 (runFrom pH268 (fmask pH268) (cmask pH268) (hmask pH268) 1 267 (true, (init pH268), (init pH268))) ∧ ptTest pH268 (runFrom pH268 (fmask pH268) (cmask pH268) (hmask pH268) 1 267 (true, (init pH268), (init pH268))) 268 134 true = true :=
  fin_run (runOK_init (prmOK_of_and H268_fin) true) (by decide) rfl H268_fin ptTest_fst
theorem I268_fin : (prmOK pI268 268 && intTest pI268 (runFrom pI268 (fmask pI268) (cmask pI268) (hmask pI268) 1 267 (true, (init pI268), (init pI268))) 268 11 true) = true := by
  decide +kernel
theorem I268_ok : RunOK pI268 268 (runFrom pI268 (fmask pI268) (cmask pI268) (hmask pI268) 1 267 (true, (init pI268), (init pI268))) ∧ intTest pI268 (runFrom pI268 (fmask pI268) (cmask pI268) (hmask pI268) 1 267 (true, (init pI268), (init pI268))) 268 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I268_fin) true) (by decide) rfl I268_fin intTest_fst
theorem link268 : linkOK pL268 pH268 pI268 = true := by decide +kernel
theorem cvx268 : ConvexBetweenHumps 268 :=
  cvx_of L268_ok H268_ok I268_ok link268 (by decide)
theorem cenlink268 : cenLinkOK pI268 268 = true := by decide +kernel
theorem cen268 : CenterUniqueMin 268 ∧ DipHyp 268 ∧ OnePointHyps 268 :=
  cen_of L268_ok H268_ok I268_ok link268 cenlink268

/-! ### `N = 269` -/

def pL269 : Prm := ⟨64, 30, 31, 271, 11, 18446744073709551616, 472355692976074534, 472355692976074534⟩
def pH269 : Prm := ⟨64, 30, 31, 271, 11, 18446744073709551616, 472373285162118950, 472373285162118950⟩
def pI269 : Prm := ⟨56, 27, 26, 271, 11, 18446744073709551616, 472355692976074534, 472373285162118950⟩
theorem L269_fin : (prmOK pL269 269 && ptTest pL269 (runFrom pL269 (fmask pL269) (cmask pL269) (hmask pL269) 1 268 (true, (init pL269), (init pL269))) 269 135 false) = true := by
  decide +kernel
theorem L269_ok : RunOK pL269 269 (runFrom pL269 (fmask pL269) (cmask pL269) (hmask pL269) 1 268 (true, (init pL269), (init pL269))) ∧ ptTest pL269 (runFrom pL269 (fmask pL269) (cmask pL269) (hmask pL269) 1 268 (true, (init pL269), (init pL269))) 269 135 false = true :=
  fin_run (runOK_init (prmOK_of_and L269_fin) true) (by decide) rfl L269_fin ptTest_fst
theorem H269_fin : (prmOK pH269 269 && ptTest pH269 (runFrom pH269 (fmask pH269) (cmask pH269) (hmask pH269) 1 268 (true, (init pH269), (init pH269))) 269 135 true) = true := by
  decide +kernel
theorem H269_ok : RunOK pH269 269 (runFrom pH269 (fmask pH269) (cmask pH269) (hmask pH269) 1 268 (true, (init pH269), (init pH269))) ∧ ptTest pH269 (runFrom pH269 (fmask pH269) (cmask pH269) (hmask pH269) 1 268 (true, (init pH269), (init pH269))) 269 135 true = true :=
  fin_run (runOK_init (prmOK_of_and H269_fin) true) (by decide) rfl H269_fin ptTest_fst
theorem I269_fin : (prmOK pI269 269 && intTest pI269 (runFrom pI269 (fmask pI269) (cmask pI269) (hmask pI269) 1 268 (true, (init pI269), (init pI269))) 269 11 false) = true := by
  decide +kernel
theorem I269_ok : RunOK pI269 269 (runFrom pI269 (fmask pI269) (cmask pI269) (hmask pI269) 1 268 (true, (init pI269), (init pI269))) ∧ intTest pI269 (runFrom pI269 (fmask pI269) (cmask pI269) (hmask pI269) 1 268 (true, (init pI269), (init pI269))) 269 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I269_fin) true) (by decide) rfl I269_fin intTest_fst
theorem link269 : linkOK pL269 pH269 pI269 = true := by decide +kernel
theorem cvx269 : ConvexBetweenHumps 269 :=
  cvx_of L269_ok H269_ok I269_ok link269 (by decide)

/-! ### `N = 270` -/

def pL270 : Prm := ⟨64, 30, 31, 272, 11, 18446744073709551616, 471080363958064762, 471080363958064762⟩
def pH270 : Prm := ⟨64, 30, 31, 272, 11, 18446744073709551616, 471097956144109178, 471097956144109178⟩
def pI270 : Prm := ⟨56, 27, 26, 272, 11, 18446744073709551616, 471080363958064762, 471097956144109178⟩
theorem L270_fin : (prmOK pL270 270 && ptTest pL270 (runFrom pL270 (fmask pL270) (cmask pL270) (hmask pL270) 1 269 (true, (init pL270), (init pL270))) 270 135 false) = true := by
  decide +kernel
theorem L270_ok : RunOK pL270 270 (runFrom pL270 (fmask pL270) (cmask pL270) (hmask pL270) 1 269 (true, (init pL270), (init pL270))) ∧ ptTest pL270 (runFrom pL270 (fmask pL270) (cmask pL270) (hmask pL270) 1 269 (true, (init pL270), (init pL270))) 270 135 false = true :=
  fin_run (runOK_init (prmOK_of_and L270_fin) true) (by decide) rfl L270_fin ptTest_fst
theorem H270_fin : (prmOK pH270 270 && ptTest pH270 (runFrom pH270 (fmask pH270) (cmask pH270) (hmask pH270) 1 269 (true, (init pH270), (init pH270))) 270 135 true) = true := by
  decide +kernel
theorem H270_ok : RunOK pH270 270 (runFrom pH270 (fmask pH270) (cmask pH270) (hmask pH270) 1 269 (true, (init pH270), (init pH270))) ∧ ptTest pH270 (runFrom pH270 (fmask pH270) (cmask pH270) (hmask pH270) 1 269 (true, (init pH270), (init pH270))) 270 135 true = true :=
  fin_run (runOK_init (prmOK_of_and H270_fin) true) (by decide) rfl H270_fin ptTest_fst
theorem I270_fin : (prmOK pI270 270 && intTest pI270 (runFrom pI270 (fmask pI270) (cmask pI270) (hmask pI270) 1 269 (true, (init pI270), (init pI270))) 270 11 true) = true := by
  decide +kernel
theorem I270_ok : RunOK pI270 270 (runFrom pI270 (fmask pI270) (cmask pI270) (hmask pI270) 1 269 (true, (init pI270), (init pI270))) ∧ intTest pI270 (runFrom pI270 (fmask pI270) (cmask pI270) (hmask pI270) 1 269 (true, (init pI270), (init pI270))) 270 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I270_fin) true) (by decide) rfl I270_fin intTest_fst
theorem link270 : linkOK pL270 pH270 pI270 = true := by decide +kernel
theorem cvx270 : ConvexBetweenHumps 270 :=
  cvx_of L270_ok H270_ok I270_ok link270 (by decide)
theorem cenlink270 : cenLinkOK pI270 270 = true := by decide +kernel
theorem cen270 : CenterUniqueMin 270 ∧ DipHyp 270 ∧ OnePointHyps 270 :=
  cen_of L270_ok H270_ok I270_ok link270 cenlink270

/-! ### `N = 271` -/

def pL271 : Prm := ⟨64, 30, 31, 273, 11, 18446744073709551616, 469806579866068337, 469806579866068337⟩
def pH271 : Prm := ⟨64, 30, 31, 273, 11, 18446744073709551616, 469824172052112753, 469824172052112753⟩
def pI271 : Prm := ⟨56, 27, 26, 273, 11, 18446744073709551616, 469806579866068337, 469824172052112753⟩
theorem L271_fin : (prmOK pL271 271 && ptTest pL271 (runFrom pL271 (fmask pL271) (cmask pL271) (hmask pL271) 1 270 (true, (init pL271), (init pL271))) 271 136 false) = true := by
  decide +kernel
theorem L271_ok : RunOK pL271 271 (runFrom pL271 (fmask pL271) (cmask pL271) (hmask pL271) 1 270 (true, (init pL271), (init pL271))) ∧ ptTest pL271 (runFrom pL271 (fmask pL271) (cmask pL271) (hmask pL271) 1 270 (true, (init pL271), (init pL271))) 271 136 false = true :=
  fin_run (runOK_init (prmOK_of_and L271_fin) true) (by decide) rfl L271_fin ptTest_fst
theorem H271_fin : (prmOK pH271 271 && ptTest pH271 (runFrom pH271 (fmask pH271) (cmask pH271) (hmask pH271) 1 270 (true, (init pH271), (init pH271))) 271 136 true) = true := by
  decide +kernel
theorem H271_ok : RunOK pH271 271 (runFrom pH271 (fmask pH271) (cmask pH271) (hmask pH271) 1 270 (true, (init pH271), (init pH271))) ∧ ptTest pH271 (runFrom pH271 (fmask pH271) (cmask pH271) (hmask pH271) 1 270 (true, (init pH271), (init pH271))) 271 136 true = true :=
  fin_run (runOK_init (prmOK_of_and H271_fin) true) (by decide) rfl H271_fin ptTest_fst
theorem I271_fin : (prmOK pI271 271 && intTest pI271 (runFrom pI271 (fmask pI271) (cmask pI271) (hmask pI271) 1 270 (true, (init pI271), (init pI271))) 271 11 false) = true := by
  decide +kernel
theorem I271_ok : RunOK pI271 271 (runFrom pI271 (fmask pI271) (cmask pI271) (hmask pI271) 1 270 (true, (init pI271), (init pI271))) ∧ intTest pI271 (runFrom pI271 (fmask pI271) (cmask pI271) (hmask pI271) 1 270 (true, (init pI271), (init pI271))) 271 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I271_fin) true) (by decide) rfl I271_fin intTest_fst
theorem link271 : linkOK pL271 pH271 pI271 = true := by decide +kernel
theorem cvx271 : ConvexBetweenHumps 271 :=
  cvx_of L271_ok H271_ok I271_ok link271 (by decide)

/-! ### `N = 272` -/

def pL272 : Prm := ⟨64, 30, 31, 274, 11, 18446744073709551616, 468546616524998510, 468546616524998510⟩
def pH272 : Prm := ⟨64, 30, 31, 274, 11, 18446744073709551616, 468564208711042926, 468564208711042926⟩
def pI272 : Prm := ⟨57, 27, 27, 274, 11, 18446744073709551616, 468546616524998510, 468564208711042926⟩
theorem L272_fin : (prmOK pL272 272 && ptTest pL272 (runFrom pL272 (fmask pL272) (cmask pL272) (hmask pL272) 1 271 (true, (init pL272), (init pL272))) 272 136 false) = true := by
  decide +kernel
theorem L272_ok : RunOK pL272 272 (runFrom pL272 (fmask pL272) (cmask pL272) (hmask pL272) 1 271 (true, (init pL272), (init pL272))) ∧ ptTest pL272 (runFrom pL272 (fmask pL272) (cmask pL272) (hmask pL272) 1 271 (true, (init pL272), (init pL272))) 272 136 false = true :=
  fin_run (runOK_init (prmOK_of_and L272_fin) true) (by decide) rfl L272_fin ptTest_fst
theorem H272_fin : (prmOK pH272 272 && ptTest pH272 (runFrom pH272 (fmask pH272) (cmask pH272) (hmask pH272) 1 271 (true, (init pH272), (init pH272))) 272 136 true) = true := by
  decide +kernel
theorem H272_ok : RunOK pH272 272 (runFrom pH272 (fmask pH272) (cmask pH272) (hmask pH272) 1 271 (true, (init pH272), (init pH272))) ∧ ptTest pH272 (runFrom pH272 (fmask pH272) (cmask pH272) (hmask pH272) 1 271 (true, (init pH272), (init pH272))) 272 136 true = true :=
  fin_run (runOK_init (prmOK_of_and H272_fin) true) (by decide) rfl H272_fin ptTest_fst
theorem I272_fin : (prmOK pI272 272 && intTest pI272 (runFrom pI272 (fmask pI272) (cmask pI272) (hmask pI272) 1 271 (true, (init pI272), (init pI272))) 272 11 true) = true := by
  decide +kernel
theorem I272_ok : RunOK pI272 272 (runFrom pI272 (fmask pI272) (cmask pI272) (hmask pI272) 1 271 (true, (init pI272), (init pI272))) ∧ intTest pI272 (runFrom pI272 (fmask pI272) (cmask pI272) (hmask pI272) 1 271 (true, (init pI272), (init pI272))) 272 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I272_fin) true) (by decide) rfl I272_fin intTest_fst
theorem link272 : linkOK pL272 pH272 pI272 = true := by decide +kernel
theorem cvx272 : ConvexBetweenHumps 272 :=
  cvx_of L272_ok H272_ok I272_ok link272 (by decide)
theorem cenlink272 : cenLinkOK pI272 272 = true := by decide +kernel
theorem cen272 : CenterUniqueMin 272 ∧ DipHyp 272 ∧ OnePointHyps 272 :=
  cen_of L272_ok H272_ok I272_ok link272 cenlink272

/-! ### `N = 273` -/

def pL273 : Prm := ⟨64, 30, 31, 275, 11, 18446744073709551616, 467288187930567483, 467288187930567483⟩
def pH273 : Prm := ⟨64, 30, 31, 275, 11, 18446744073709551616, 467305780116611899, 467305780116611899⟩
def pI273 : Prm := ⟨57, 27, 27, 275, 11, 18446744073709551616, 467288187930567483, 467305780116611899⟩
theorem L273_fin : (prmOK pL273 273 && ptTest pL273 (runFrom pL273 (fmask pL273) (cmask pL273) (hmask pL273) 1 272 (true, (init pL273), (init pL273))) 273 137 false) = true := by
  decide +kernel
theorem L273_ok : RunOK pL273 273 (runFrom pL273 (fmask pL273) (cmask pL273) (hmask pL273) 1 272 (true, (init pL273), (init pL273))) ∧ ptTest pL273 (runFrom pL273 (fmask pL273) (cmask pL273) (hmask pL273) 1 272 (true, (init pL273), (init pL273))) 273 137 false = true :=
  fin_run (runOK_init (prmOK_of_and L273_fin) true) (by decide) rfl L273_fin ptTest_fst
theorem H273_fin : (prmOK pH273 273 && ptTest pH273 (runFrom pH273 (fmask pH273) (cmask pH273) (hmask pH273) 1 272 (true, (init pH273), (init pH273))) 273 137 true) = true := by
  decide +kernel
theorem H273_ok : RunOK pH273 273 (runFrom pH273 (fmask pH273) (cmask pH273) (hmask pH273) 1 272 (true, (init pH273), (init pH273))) ∧ ptTest pH273 (runFrom pH273 (fmask pH273) (cmask pH273) (hmask pH273) 1 272 (true, (init pH273), (init pH273))) 273 137 true = true :=
  fin_run (runOK_init (prmOK_of_and H273_fin) true) (by decide) rfl H273_fin ptTest_fst
theorem I273_fin : (prmOK pI273 273 && intTest pI273 (runFrom pI273 (fmask pI273) (cmask pI273) (hmask pI273) 1 272 (true, (init pI273), (init pI273))) 273 11 false) = true := by
  decide +kernel
theorem I273_ok : RunOK pI273 273 (runFrom pI273 (fmask pI273) (cmask pI273) (hmask pI273) 1 272 (true, (init pI273), (init pI273))) ∧ intTest pI273 (runFrom pI273 (fmask pI273) (cmask pI273) (hmask pI273) 1 272 (true, (init pI273), (init pI273))) 273 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I273_fin) true) (by decide) rfl I273_fin intTest_fst
theorem link273 : linkOK pL273 pH273 pI273 = true := by decide +kernel
theorem cvx273 : ConvexBetweenHumps 273 :=
  cvx_of L273_ok H273_ok I273_ok link273 (by decide)

/-! ### `N = 274` -/

def pL274 : Prm := ⟨64, 30, 31, 276, 11, 18446744073709551616, 466043301334587114, 466043301334587114⟩
def pH274 : Prm := ⟨64, 30, 31, 276, 11, 18446744073709551616, 466060893520631530, 466060893520631530⟩
def pI274 : Prm := ⟨57, 27, 27, 276, 11, 18446744073709551616, 466043301334587114, 466060893520631530⟩
theorem L274_fin : (prmOK pL274 274 && ptTest pL274 (runFrom pL274 (fmask pL274) (cmask pL274) (hmask pL274) 1 273 (true, (init pL274), (init pL274))) 274 137 false) = true := by
  decide +kernel
theorem L274_ok : RunOK pL274 274 (runFrom pL274 (fmask pL274) (cmask pL274) (hmask pL274) 1 273 (true, (init pL274), (init pL274))) ∧ ptTest pL274 (runFrom pL274 (fmask pL274) (cmask pL274) (hmask pL274) 1 273 (true, (init pL274), (init pL274))) 274 137 false = true :=
  fin_run (runOK_init (prmOK_of_and L274_fin) true) (by decide) rfl L274_fin ptTest_fst
theorem H274_fin : (prmOK pH274 274 && ptTest pH274 (runFrom pH274 (fmask pH274) (cmask pH274) (hmask pH274) 1 273 (true, (init pH274), (init pH274))) 274 137 true) = true := by
  decide +kernel
theorem H274_ok : RunOK pH274 274 (runFrom pH274 (fmask pH274) (cmask pH274) (hmask pH274) 1 273 (true, (init pH274), (init pH274))) ∧ ptTest pH274 (runFrom pH274 (fmask pH274) (cmask pH274) (hmask pH274) 1 273 (true, (init pH274), (init pH274))) 274 137 true = true :=
  fin_run (runOK_init (prmOK_of_and H274_fin) true) (by decide) rfl H274_fin ptTest_fst
theorem I274_fin : (prmOK pI274 274 && intTest pI274 (runFrom pI274 (fmask pI274) (cmask pI274) (hmask pI274) 1 273 (true, (init pI274), (init pI274))) 274 11 true) = true := by
  decide +kernel
theorem I274_ok : RunOK pI274 274 (runFrom pI274 (fmask pI274) (cmask pI274) (hmask pI274) 1 273 (true, (init pI274), (init pI274))) ∧ intTest pI274 (runFrom pI274 (fmask pI274) (cmask pI274) (hmask pI274) 1 273 (true, (init pI274), (init pI274))) 274 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I274_fin) true) (by decide) rfl I274_fin intTest_fst
theorem link274 : linkOK pL274 pH274 pI274 = true := by decide +kernel
theorem cvx274 : ConvexBetweenHumps 274 :=
  cvx_of L274_ok H274_ok I274_ok link274 (by decide)
theorem cenlink274 : cenLinkOK pI274 274 = true := by decide +kernel
theorem cen274 : CenterUniqueMin 274 ∧ DipHyp 274 ∧ OnePointHyps 274 :=
  cen_of L274_ok H274_ok I274_ok link274 cenlink274

/-! ### `N = 275` -/

def pL275 : Prm := ⟨64, 30, 31, 277, 11, 18446744073709551616, 464799939146306659, 464799939146306659⟩
def pH275 : Prm := ⟨64, 30, 31, 277, 11, 18446744073709551616, 464817531332351075, 464817531332351075⟩
def pI275 : Prm := ⟨57, 27, 27, 277, 11, 18446744073709551616, 464799939146306659, 464817531332351075⟩
theorem L275_fin : (prmOK pL275 275 && ptTest pL275 (runFrom pL275 (fmask pL275) (cmask pL275) (hmask pL275) 1 274 (true, (init pL275), (init pL275))) 275 138 false) = true := by
  decide +kernel
theorem L275_ok : RunOK pL275 275 (runFrom pL275 (fmask pL275) (cmask pL275) (hmask pL275) 1 274 (true, (init pL275), (init pL275))) ∧ ptTest pL275 (runFrom pL275 (fmask pL275) (cmask pL275) (hmask pL275) 1 274 (true, (init pL275), (init pL275))) 275 138 false = true :=
  fin_run (runOK_init (prmOK_of_and L275_fin) true) (by decide) rfl L275_fin ptTest_fst
theorem H275_fin : (prmOK pH275 275 && ptTest pH275 (runFrom pH275 (fmask pH275) (cmask pH275) (hmask pH275) 1 274 (true, (init pH275), (init pH275))) 275 138 true) = true := by
  decide +kernel
theorem H275_ok : RunOK pH275 275 (runFrom pH275 (fmask pH275) (cmask pH275) (hmask pH275) 1 274 (true, (init pH275), (init pH275))) ∧ ptTest pH275 (runFrom pH275 (fmask pH275) (cmask pH275) (hmask pH275) 1 274 (true, (init pH275), (init pH275))) 275 138 true = true :=
  fin_run (runOK_init (prmOK_of_and H275_fin) true) (by decide) rfl H275_fin ptTest_fst
theorem I275_fin : (prmOK pI275 275 && intTest pI275 (runFrom pI275 (fmask pI275) (cmask pI275) (hmask pI275) 1 274 (true, (init pI275), (init pI275))) 275 11 false) = true := by
  decide +kernel
theorem I275_ok : RunOK pI275 275 (runFrom pI275 (fmask pI275) (cmask pI275) (hmask pI275) 1 274 (true, (init pI275), (init pI275))) ∧ intTest pI275 (runFrom pI275 (fmask pI275) (cmask pI275) (hmask pI275) 1 274 (true, (init pI275), (init pI275))) 275 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I275_fin) true) (by decide) rfl I275_fin intTest_fst
theorem link275 : linkOK pL275 pH275 pI275 = true := by decide +kernel
theorem cvx275 : ConvexBetweenHumps 275 :=
  cvx_of L275_ok H275_ok I275_ok link275 (by decide)

/-! ### `N = 276` -/

def pL276 : Prm := ⟨64, 30, 31, 278, 11, 18446744073709551616, 463569847749715374, 463569847749715374⟩
def pH276 : Prm := ⟨64, 30, 31, 278, 11, 18446744073709551616, 463587439935759790, 463587439935759790⟩
def pI276 : Prm := ⟨57, 27, 27, 278, 11, 18446744073709551616, 463569847749715374, 463587439935759790⟩
theorem L276_fin : (prmOK pL276 276 && ptTest pL276 (runFrom pL276 (fmask pL276) (cmask pL276) (hmask pL276) 1 275 (true, (init pL276), (init pL276))) 276 138 false) = true := by
  decide +kernel
theorem L276_ok : RunOK pL276 276 (runFrom pL276 (fmask pL276) (cmask pL276) (hmask pL276) 1 275 (true, (init pL276), (init pL276))) ∧ ptTest pL276 (runFrom pL276 (fmask pL276) (cmask pL276) (hmask pL276) 1 275 (true, (init pL276), (init pL276))) 276 138 false = true :=
  fin_run (runOK_init (prmOK_of_and L276_fin) true) (by decide) rfl L276_fin ptTest_fst
theorem H276_fin : (prmOK pH276 276 && ptTest pH276 (runFrom pH276 (fmask pH276) (cmask pH276) (hmask pH276) 1 275 (true, (init pH276), (init pH276))) 276 138 true) = true := by
  decide +kernel
theorem H276_ok : RunOK pH276 276 (runFrom pH276 (fmask pH276) (cmask pH276) (hmask pH276) 1 275 (true, (init pH276), (init pH276))) ∧ ptTest pH276 (runFrom pH276 (fmask pH276) (cmask pH276) (hmask pH276) 1 275 (true, (init pH276), (init pH276))) 276 138 true = true :=
  fin_run (runOK_init (prmOK_of_and H276_fin) true) (by decide) rfl H276_fin ptTest_fst
theorem I276_fin : (prmOK pI276 276 && intTest pI276 (runFrom pI276 (fmask pI276) (cmask pI276) (hmask pI276) 1 275 (true, (init pI276), (init pI276))) 276 11 true) = true := by
  decide +kernel
theorem I276_ok : RunOK pI276 276 (runFrom pI276 (fmask pI276) (cmask pI276) (hmask pI276) 1 275 (true, (init pI276), (init pI276))) ∧ intTest pI276 (runFrom pI276 (fmask pI276) (cmask pI276) (hmask pI276) 1 275 (true, (init pI276), (init pI276))) 276 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I276_fin) true) (by decide) rfl I276_fin intTest_fst
theorem link276 : linkOK pL276 pH276 pI276 = true := by decide +kernel
theorem cvx276 : ConvexBetweenHumps 276 :=
  cvx_of L276_ok H276_ok I276_ok link276 (by decide)
theorem cenlink276 : cenLinkOK pI276 276 = true := by decide +kernel
theorem cen276 : CenterUniqueMin 276 ∧ DipHyp 276 ∧ OnePointHyps 276 :=
  cen_of L276_ok H276_ok I276_ok link276 cenlink276

/-! ### `N = 277` -/

def pL277 : Prm := ⟨64, 30, 31, 279, 11, 18446744073709551616, 462341270279384019, 462341270279384019⟩
def pH277 : Prm := ⟨64, 30, 31, 279, 11, 18446744073709551616, 462358862465428435, 462358862465428435⟩
def pI277 : Prm := ⟨57, 27, 27, 279, 11, 18446744073709551616, 462341270279384019, 462358862465428435⟩
theorem L277_fin : (prmOK pL277 277 && ptTest pL277 (runFrom pL277 (fmask pL277) (cmask pL277) (hmask pL277) 1 276 (true, (init pL277), (init pL277))) 277 139 false) = true := by
  decide +kernel
theorem L277_ok : RunOK pL277 277 (runFrom pL277 (fmask pL277) (cmask pL277) (hmask pL277) 1 276 (true, (init pL277), (init pL277))) ∧ ptTest pL277 (runFrom pL277 (fmask pL277) (cmask pL277) (hmask pL277) 1 276 (true, (init pL277), (init pL277))) 277 139 false = true :=
  fin_run (runOK_init (prmOK_of_and L277_fin) true) (by decide) rfl L277_fin ptTest_fst
theorem H277_fin : (prmOK pH277 277 && ptTest pH277 (runFrom pH277 (fmask pH277) (cmask pH277) (hmask pH277) 1 276 (true, (init pH277), (init pH277))) 277 139 true) = true := by
  decide +kernel
theorem H277_ok : RunOK pH277 277 (runFrom pH277 (fmask pH277) (cmask pH277) (hmask pH277) 1 276 (true, (init pH277), (init pH277))) ∧ ptTest pH277 (runFrom pH277 (fmask pH277) (cmask pH277) (hmask pH277) 1 276 (true, (init pH277), (init pH277))) 277 139 true = true :=
  fin_run (runOK_init (prmOK_of_and H277_fin) true) (by decide) rfl H277_fin ptTest_fst
theorem I277_fin : (prmOK pI277 277 && intTest pI277 (runFrom pI277 (fmask pI277) (cmask pI277) (hmask pI277) 1 276 (true, (init pI277), (init pI277))) 277 11 false) = true := by
  decide +kernel
theorem I277_ok : RunOK pI277 277 (runFrom pI277 (fmask pI277) (cmask pI277) (hmask pI277) 1 276 (true, (init pI277), (init pI277))) ∧ intTest pI277 (runFrom pI277 (fmask pI277) (cmask pI277) (hmask pI277) 1 276 (true, (init pI277), (init pI277))) 277 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I277_fin) true) (by decide) rfl I277_fin intTest_fst
theorem link277 : linkOK pL277 pH277 pI277 = true := by decide +kernel
theorem cvx277 : ConvexBetweenHumps 277 :=
  cvx_of L277_ok H277_ok I277_ok link277 (by decide)

/-! ### `N = 278` -/

def pL278 : Prm := ⟨64, 30, 31, 280, 11, 18446744073709551616, 461125699684096708, 461125699684096708⟩
def pH278 : Prm := ⟨64, 30, 31, 280, 11, 18446744073709551616, 461143291870141124, 461143291870141124⟩
def pI278 : Prm := ⟨57, 27, 27, 280, 11, 18446744073709551616, 461125699684096708, 461143291870141124⟩
theorem L278_fin : (prmOK pL278 278 && ptTest pL278 (runFrom pL278 (fmask pL278) (cmask pL278) (hmask pL278) 1 277 (true, (init pL278), (init pL278))) 278 139 false) = true := by
  decide +kernel
theorem L278_ok : RunOK pL278 278 (runFrom pL278 (fmask pL278) (cmask pL278) (hmask pL278) 1 277 (true, (init pL278), (init pL278))) ∧ ptTest pL278 (runFrom pL278 (fmask pL278) (cmask pL278) (hmask pL278) 1 277 (true, (init pL278), (init pL278))) 278 139 false = true :=
  fin_run (runOK_init (prmOK_of_and L278_fin) true) (by decide) rfl L278_fin ptTest_fst
theorem H278_fin : (prmOK pH278 278 && ptTest pH278 (runFrom pH278 (fmask pH278) (cmask pH278) (hmask pH278) 1 277 (true, (init pH278), (init pH278))) 278 139 true) = true := by
  decide +kernel
theorem H278_ok : RunOK pH278 278 (runFrom pH278 (fmask pH278) (cmask pH278) (hmask pH278) 1 277 (true, (init pH278), (init pH278))) ∧ ptTest pH278 (runFrom pH278 (fmask pH278) (cmask pH278) (hmask pH278) 1 277 (true, (init pH278), (init pH278))) 278 139 true = true :=
  fin_run (runOK_init (prmOK_of_and H278_fin) true) (by decide) rfl H278_fin ptTest_fst
theorem I278_fin : (prmOK pI278 278 && intTest pI278 (runFrom pI278 (fmask pI278) (cmask pI278) (hmask pI278) 1 277 (true, (init pI278), (init pI278))) 278 11 true) = true := by
  decide +kernel
theorem I278_ok : RunOK pI278 278 (runFrom pI278 (fmask pI278) (cmask pI278) (hmask pI278) 1 277 (true, (init pI278), (init pI278))) ∧ intTest pI278 (runFrom pI278 (fmask pI278) (cmask pI278) (hmask pI278) 1 277 (true, (init pI278), (init pI278))) 278 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I278_fin) true) (by decide) rfl I278_fin intTest_fst
theorem link278 : linkOK pL278 pH278 pI278 = true := by decide +kernel
theorem cvx278 : ConvexBetweenHumps 278 :=
  cvx_of L278_ok H278_ok I278_ok link278 (by decide)
theorem cenlink278 : cenLinkOK pI278 278 = true := by decide +kernel
theorem cen278 : CenterUniqueMin 278 ∧ DipHyp 278 ∧ OnePointHyps 278 :=
  cen_of L278_ok H278_ok I278_ok link278 cenlink278

/-! ### `N = 279` -/

def pL279 : Prm := ⟨64, 30, 31, 281, 11, 18446744073709551616, 459911632407029342, 459911632407029342⟩
def pH279 : Prm := ⟨64, 30, 31, 281, 11, 18446744073709551616, 459929224593073758, 459929224593073758⟩
def pI279 : Prm := ⟨57, 28, 26, 281, 11, 18446744073709551616, 459911632407029342, 459929224593073758⟩
theorem L279_fin : (prmOK pL279 279 && ptTest pL279 (runFrom pL279 (fmask pL279) (cmask pL279) (hmask pL279) 1 278 (true, (init pL279), (init pL279))) 279 140 false) = true := by
  decide +kernel
theorem L279_ok : RunOK pL279 279 (runFrom pL279 (fmask pL279) (cmask pL279) (hmask pL279) 1 278 (true, (init pL279), (init pL279))) ∧ ptTest pL279 (runFrom pL279 (fmask pL279) (cmask pL279) (hmask pL279) 1 278 (true, (init pL279), (init pL279))) 279 140 false = true :=
  fin_run (runOK_init (prmOK_of_and L279_fin) true) (by decide) rfl L279_fin ptTest_fst
theorem H279_fin : (prmOK pH279 279 && ptTest pH279 (runFrom pH279 (fmask pH279) (cmask pH279) (hmask pH279) 1 278 (true, (init pH279), (init pH279))) 279 140 true) = true := by
  decide +kernel
theorem H279_ok : RunOK pH279 279 (runFrom pH279 (fmask pH279) (cmask pH279) (hmask pH279) 1 278 (true, (init pH279), (init pH279))) ∧ ptTest pH279 (runFrom pH279 (fmask pH279) (cmask pH279) (hmask pH279) 1 278 (true, (init pH279), (init pH279))) 279 140 true = true :=
  fin_run (runOK_init (prmOK_of_and H279_fin) true) (by decide) rfl H279_fin ptTest_fst
theorem I279_fin : (prmOK pI279 279 && intTest pI279 (runFrom pI279 (fmask pI279) (cmask pI279) (hmask pI279) 1 278 (true, (init pI279), (init pI279))) 279 11 false) = true := by
  decide +kernel
theorem I279_ok : RunOK pI279 279 (runFrom pI279 (fmask pI279) (cmask pI279) (hmask pI279) 1 278 (true, (init pI279), (init pI279))) ∧ intTest pI279 (runFrom pI279 (fmask pI279) (cmask pI279) (hmask pI279) 1 278 (true, (init pI279), (init pI279))) 279 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I279_fin) true) (by decide) rfl I279_fin intTest_fst
theorem link279 : linkOK pL279 pH279 pI279 = true := by decide +kernel
theorem cvx279 : ConvexBetweenHumps 279 :=
  cvx_of L279_ok H279_ok I279_ok link279 (by decide)

/-! ### `N = 280` -/

def pL280 : Prm := ⟨64, 30, 31, 282, 11, 18446744073709551616, 458710315133338476, 458710315133338476⟩
def pH280 : Prm := ⟨64, 30, 31, 282, 11, 18446744073709551616, 458727907319382892, 458727907319382892⟩
def pI280 : Prm := ⟨57, 28, 26, 282, 11, 18446744073709551616, 458710315133338476, 458727907319382892⟩
theorem L280_fin : (prmOK pL280 280 && ptTest pL280 (runFrom pL280 (fmask pL280) (cmask pL280) (hmask pL280) 1 279 (true, (init pL280), (init pL280))) 280 140 false) = true := by
  decide +kernel
theorem L280_ok : RunOK pL280 280 (runFrom pL280 (fmask pL280) (cmask pL280) (hmask pL280) 1 279 (true, (init pL280), (init pL280))) ∧ ptTest pL280 (runFrom pL280 (fmask pL280) (cmask pL280) (hmask pL280) 1 279 (true, (init pL280), (init pL280))) 280 140 false = true :=
  fin_run (runOK_init (prmOK_of_and L280_fin) true) (by decide) rfl L280_fin ptTest_fst
theorem H280_fin : (prmOK pH280 280 && ptTest pH280 (runFrom pH280 (fmask pH280) (cmask pH280) (hmask pH280) 1 279 (true, (init pH280), (init pH280))) 280 140 true) = true := by
  decide +kernel
theorem H280_ok : RunOK pH280 280 (runFrom pH280 (fmask pH280) (cmask pH280) (hmask pH280) 1 279 (true, (init pH280), (init pH280))) ∧ ptTest pH280 (runFrom pH280 (fmask pH280) (cmask pH280) (hmask pH280) 1 279 (true, (init pH280), (init pH280))) 280 140 true = true :=
  fin_run (runOK_init (prmOK_of_and H280_fin) true) (by decide) rfl H280_fin ptTest_fst
theorem I280_fin : (prmOK pI280 280 && intTest pI280 (runFrom pI280 (fmask pI280) (cmask pI280) (hmask pI280) 1 279 (true, (init pI280), (init pI280))) 280 11 true) = true := by
  decide +kernel
theorem I280_ok : RunOK pI280 280 (runFrom pI280 (fmask pI280) (cmask pI280) (hmask pI280) 1 279 (true, (init pI280), (init pI280))) ∧ intTest pI280 (runFrom pI280 (fmask pI280) (cmask pI280) (hmask pI280) 1 279 (true, (init pI280), (init pI280))) 280 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I280_fin) true) (by decide) rfl I280_fin intTest_fst
theorem link280 : linkOK pL280 pH280 pI280 = true := by decide +kernel
theorem cvx280 : ConvexBetweenHumps 280 :=
  cvx_of L280_ok H280_ok I280_ok link280 (by decide)
theorem cenlink280 : cenLinkOK pI280 280 = true := by decide +kernel
theorem cen280 : CenterUniqueMin 280 ∧ DipHyp 280 ∧ OnePointHyps 280 :=
  cen_of L280_ok H280_ok I280_ok link280 cenlink280

/-! ### `N = 281` -/

def pL281 : Prm := ⟨64, 30, 31, 283, 11, 18446744073709551616, 457510490458187871, 457510490458187871⟩
def pH281 : Prm := ⟨64, 30, 31, 283, 11, 18446744073709551616, 457528082644232287, 457528082644232287⟩
def pI281 : Prm := ⟨57, 28, 26, 283, 11, 18446744073709551616, 457510490458187871, 457528082644232287⟩
theorem L281_fin : (prmOK pL281 281 && ptTest pL281 (runFrom pL281 (fmask pL281) (cmask pL281) (hmask pL281) 1 280 (true, (init pL281), (init pL281))) 281 141 false) = true := by
  decide +kernel
theorem L281_ok : RunOK pL281 281 (runFrom pL281 (fmask pL281) (cmask pL281) (hmask pL281) 1 280 (true, (init pL281), (init pL281))) ∧ ptTest pL281 (runFrom pL281 (fmask pL281) (cmask pL281) (hmask pL281) 1 280 (true, (init pL281), (init pL281))) 281 141 false = true :=
  fin_run (runOK_init (prmOK_of_and L281_fin) true) (by decide) rfl L281_fin ptTest_fst
theorem H281_fin : (prmOK pH281 281 && ptTest pH281 (runFrom pH281 (fmask pH281) (cmask pH281) (hmask pH281) 1 280 (true, (init pH281), (init pH281))) 281 141 true) = true := by
  decide +kernel
theorem H281_ok : RunOK pH281 281 (runFrom pH281 (fmask pH281) (cmask pH281) (hmask pH281) 1 280 (true, (init pH281), (init pH281))) ∧ ptTest pH281 (runFrom pH281 (fmask pH281) (cmask pH281) (hmask pH281) 1 280 (true, (init pH281), (init pH281))) 281 141 true = true :=
  fin_run (runOK_init (prmOK_of_and H281_fin) true) (by decide) rfl H281_fin ptTest_fst
theorem I281_fin : (prmOK pI281 281 && intTest pI281 (runFrom pI281 (fmask pI281) (cmask pI281) (hmask pI281) 1 280 (true, (init pI281), (init pI281))) 281 11 false) = true := by
  decide +kernel
theorem I281_ok : RunOK pI281 281 (runFrom pI281 (fmask pI281) (cmask pI281) (hmask pI281) 1 280 (true, (init pI281), (init pI281))) ∧ intTest pI281 (runFrom pI281 (fmask pI281) (cmask pI281) (hmask pI281) 1 280 (true, (init pI281), (init pI281))) 281 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I281_fin) true) (by decide) rfl I281_fin intTest_fst
theorem link281 : linkOK pL281 pH281 pI281 = true := by decide +kernel
theorem cvx281 : ConvexBetweenHumps 281 :=
  cvx_of L281_ok H281_ok I281_ok link281 (by decide)

/-! ### `N = 282` -/

def pL282 : Prm := ⟨64, 30, 31, 284, 11, 18446744073709551616, 456323165724454034, 456323165724454034⟩
def pH282 : Prm := ⟨64, 30, 31, 284, 11, 18446744073709551616, 456340757910498450, 456340757910498450⟩
def pI282 : Prm := ⟨57, 28, 26, 284, 11, 18446744073709551616, 456323165724454034, 456340757910498450⟩
theorem L282_fin : (prmOK pL282 282 && ptTest pL282 (runFrom pL282 (fmask pL282) (cmask pL282) (hmask pL282) 1 281 (true, (init pL282), (init pL282))) 282 141 false) = true := by
  decide +kernel
theorem L282_ok : RunOK pL282 282 (runFrom pL282 (fmask pL282) (cmask pL282) (hmask pL282) 1 281 (true, (init pL282), (init pL282))) ∧ ptTest pL282 (runFrom pL282 (fmask pL282) (cmask pL282) (hmask pL282) 1 281 (true, (init pL282), (init pL282))) 282 141 false = true :=
  fin_run (runOK_init (prmOK_of_and L282_fin) true) (by decide) rfl L282_fin ptTest_fst
theorem H282_fin : (prmOK pH282 282 && ptTest pH282 (runFrom pH282 (fmask pH282) (cmask pH282) (hmask pH282) 1 281 (true, (init pH282), (init pH282))) 282 141 true) = true := by
  decide +kernel
theorem H282_ok : RunOK pH282 282 (runFrom pH282 (fmask pH282) (cmask pH282) (hmask pH282) 1 281 (true, (init pH282), (init pH282))) ∧ ptTest pH282 (runFrom pH282 (fmask pH282) (cmask pH282) (hmask pH282) 1 281 (true, (init pH282), (init pH282))) 282 141 true = true :=
  fin_run (runOK_init (prmOK_of_and H282_fin) true) (by decide) rfl H282_fin ptTest_fst
theorem I282_fin : (prmOK pI282 282 && intTest pI282 (runFrom pI282 (fmask pI282) (cmask pI282) (hmask pI282) 1 281 (true, (init pI282), (init pI282))) 282 11 true) = true := by
  decide +kernel
theorem I282_ok : RunOK pI282 282 (runFrom pI282 (fmask pI282) (cmask pI282) (hmask pI282) 1 281 (true, (init pI282), (init pI282))) ∧ intTest pI282 (runFrom pI282 (fmask pI282) (cmask pI282) (hmask pI282) 1 281 (true, (init pI282), (init pI282))) 282 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I282_fin) true) (by decide) rfl I282_fin intTest_fst
theorem link282 : linkOK pL282 pH282 pI282 = true := by decide +kernel
theorem cvx282 : ConvexBetweenHumps 282 :=
  cvx_of L282_ok H282_ok I282_ok link282 (by decide)
theorem cenlink282 : cenLinkOK pI282 282 = true := by decide +kernel
theorem cen282 : CenterUniqueMin 282 ∧ DipHyp 282 ∧ OnePointHyps 282 :=
  cen_of L282_ok H282_ok I282_ok link282 cenlink282

/-! ### `N = 283` -/

def pL283 : Prm := ⟨64, 30, 31, 285, 11, 18446744073709551616, 455137322771886818, 455137322771886818⟩
def pH283 : Prm := ⟨64, 30, 31, 285, 11, 18446744073709551616, 455154914957931234, 455154914957931234⟩
def pI283 : Prm := ⟨57, 28, 26, 285, 11, 18446744073709551616, 455137322771886818, 455154914957931234⟩
theorem L283_fin : (prmOK pL283 283 && ptTest pL283 (runFrom pL283 (fmask pL283) (cmask pL283) (hmask pL283) 1 282 (true, (init pL283), (init pL283))) 283 142 false) = true := by
  decide +kernel
theorem L283_ok : RunOK pL283 283 (runFrom pL283 (fmask pL283) (cmask pL283) (hmask pL283) 1 282 (true, (init pL283), (init pL283))) ∧ ptTest pL283 (runFrom pL283 (fmask pL283) (cmask pL283) (hmask pL283) 1 282 (true, (init pL283), (init pL283))) 283 142 false = true :=
  fin_run (runOK_init (prmOK_of_and L283_fin) true) (by decide) rfl L283_fin ptTest_fst
theorem H283_fin : (prmOK pH283 283 && ptTest pH283 (runFrom pH283 (fmask pH283) (cmask pH283) (hmask pH283) 1 282 (true, (init pH283), (init pH283))) 283 142 true) = true := by
  decide +kernel
theorem H283_ok : RunOK pH283 283 (runFrom pH283 (fmask pH283) (cmask pH283) (hmask pH283) 1 282 (true, (init pH283), (init pH283))) ∧ ptTest pH283 (runFrom pH283 (fmask pH283) (cmask pH283) (hmask pH283) 1 282 (true, (init pH283), (init pH283))) 283 142 true = true :=
  fin_run (runOK_init (prmOK_of_and H283_fin) true) (by decide) rfl H283_fin ptTest_fst
theorem I283_fin : (prmOK pI283 283 && intTest pI283 (runFrom pI283 (fmask pI283) (cmask pI283) (hmask pI283) 1 282 (true, (init pI283), (init pI283))) 283 11 false) = true := by
  decide +kernel
theorem I283_ok : RunOK pI283 283 (runFrom pI283 (fmask pI283) (cmask pI283) (hmask pI283) 1 282 (true, (init pI283), (init pI283))) ∧ intTest pI283 (runFrom pI283 (fmask pI283) (cmask pI283) (hmask pI283) 1 282 (true, (init pI283), (init pI283))) 283 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I283_fin) true) (by decide) rfl I283_fin intTest_fst
theorem link283 : linkOK pL283 pH283 pI283 = true := by decide +kernel
theorem cvx283 : ConvexBetweenHumps 283 :=
  cvx_of L283_ok H283_ok I283_ok link283 (by decide)

/-! ### `N = 284` -/

def pL284 : Prm := ⟨64, 30, 31, 286, 11, 18446744073709551616, 453963736282604063, 453963736282604063⟩
def pH284 : Prm := ⟨64, 30, 31, 286, 11, 18446744073709551616, 453981328468648479, 453981328468648479⟩
def pI284 : Prm := ⟨57, 28, 26, 286, 11, 18446744073709551616, 453963736282604063, 453981328468648479⟩
theorem L284_fin : (prmOK pL284 284 && ptTest pL284 (runFrom pL284 (fmask pL284) (cmask pL284) (hmask pL284) 1 283 (true, (init pL284), (init pL284))) 284 142 false) = true := by
  decide +kernel
theorem L284_ok : RunOK pL284 284 (runFrom pL284 (fmask pL284) (cmask pL284) (hmask pL284) 1 283 (true, (init pL284), (init pL284))) ∧ ptTest pL284 (runFrom pL284 (fmask pL284) (cmask pL284) (hmask pL284) 1 283 (true, (init pL284), (init pL284))) 284 142 false = true :=
  fin_run (runOK_init (prmOK_of_and L284_fin) true) (by decide) rfl L284_fin ptTest_fst
theorem H284_fin : (prmOK pH284 284 && ptTest pH284 (runFrom pH284 (fmask pH284) (cmask pH284) (hmask pH284) 1 283 (true, (init pH284), (init pH284))) 284 142 true) = true := by
  decide +kernel
theorem H284_ok : RunOK pH284 284 (runFrom pH284 (fmask pH284) (cmask pH284) (hmask pH284) 1 283 (true, (init pH284), (init pH284))) ∧ ptTest pH284 (runFrom pH284 (fmask pH284) (cmask pH284) (hmask pH284) 1 283 (true, (init pH284), (init pH284))) 284 142 true = true :=
  fin_run (runOK_init (prmOK_of_and H284_fin) true) (by decide) rfl H284_fin ptTest_fst
theorem I284_fin : (prmOK pI284 284 && intTest pI284 (runFrom pI284 (fmask pI284) (cmask pI284) (hmask pI284) 1 283 (true, (init pI284), (init pI284))) 284 11 true) = true := by
  decide +kernel
theorem I284_ok : RunOK pI284 284 (runFrom pI284 (fmask pI284) (cmask pI284) (hmask pI284) 1 283 (true, (init pI284), (init pI284))) ∧ intTest pI284 (runFrom pI284 (fmask pI284) (cmask pI284) (hmask pI284) 1 283 (true, (init pI284), (init pI284))) 284 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I284_fin) true) (by decide) rfl I284_fin intTest_fst
theorem link284 : linkOK pL284 pH284 pI284 = true := by decide +kernel
theorem cvx284 : ConvexBetweenHumps 284 :=
  cvx_of L284_ok H284_ok I284_ok link284 (by decide)
theorem cenlink284 : cenLinkOK pI284 284 = true := by decide +kernel
theorem cen284 : CenterUniqueMin 284 ∧ DipHyp 284 ∧ OnePointHyps 284 :=
  cen_of L284_ok H284_ok I284_ok link284 cenlink284

/-! ### `N = 285` -/

def pL285 : Prm := ⟨64, 30, 31, 287, 11, 18446744073709551616, 452791620672572862, 452791620672572862⟩
def pH285 : Prm := ⟨64, 30, 31, 287, 11, 18446744073709551616, 452809212858617278, 452809212858617278⟩
def pI285 : Prm := ⟨57, 28, 26, 287, 11, 18446744073709551616, 452791620672572862, 452809212858617278⟩
theorem L285_fin : (prmOK pL285 285 && ptTest pL285 (runFrom pL285 (fmask pL285) (cmask pL285) (hmask pL285) 1 284 (true, (init pL285), (init pL285))) 285 143 false) = true := by
  decide +kernel
theorem L285_ok : RunOK pL285 285 (runFrom pL285 (fmask pL285) (cmask pL285) (hmask pL285) 1 284 (true, (init pL285), (init pL285))) ∧ ptTest pL285 (runFrom pL285 (fmask pL285) (cmask pL285) (hmask pL285) 1 284 (true, (init pL285), (init pL285))) 285 143 false = true :=
  fin_run (runOK_init (prmOK_of_and L285_fin) true) (by decide) rfl L285_fin ptTest_fst
theorem H285_fin : (prmOK pH285 285 && ptTest pH285 (runFrom pH285 (fmask pH285) (cmask pH285) (hmask pH285) 1 284 (true, (init pH285), (init pH285))) 285 143 true) = true := by
  decide +kernel
theorem H285_ok : RunOK pH285 285 (runFrom pH285 (fmask pH285) (cmask pH285) (hmask pH285) 1 284 (true, (init pH285), (init pH285))) ∧ ptTest pH285 (runFrom pH285 (fmask pH285) (cmask pH285) (hmask pH285) 1 284 (true, (init pH285), (init pH285))) 285 143 true = true :=
  fin_run (runOK_init (prmOK_of_and H285_fin) true) (by decide) rfl H285_fin ptTest_fst
theorem I285_fin : (prmOK pI285 285 && intTest pI285 (runFrom pI285 (fmask pI285) (cmask pI285) (hmask pI285) 1 284 (true, (init pI285), (init pI285))) 285 11 false) = true := by
  decide +kernel
theorem I285_ok : RunOK pI285 285 (runFrom pI285 (fmask pI285) (cmask pI285) (hmask pI285) 1 284 (true, (init pI285), (init pI285))) ∧ intTest pI285 (runFrom pI285 (fmask pI285) (cmask pI285) (hmask pI285) 1 284 (true, (init pI285), (init pI285))) 285 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I285_fin) true) (by decide) rfl I285_fin intTest_fst
theorem link285 : linkOK pL285 pH285 pI285 = true := by decide +kernel
theorem cvx285 : ConvexBetweenHumps 285 :=
  cvx_of L285_ok H285_ok I285_ok link285 (by decide)

/-! ### `N = 286` -/

def pL286 : Prm := ⟨64, 30, 31, 288, 11, 18446744073709551616, 451631524414569084, 451631524414569084⟩
def pH286 : Prm := ⟨64, 30, 31, 288, 11, 18446744073709551616, 451649116600613500, 451649116600613500⟩
def pI286 : Prm := ⟨57, 28, 26, 288, 11, 18446744073709551616, 451631524414569084, 451649116600613500⟩
theorem L286_fin : (prmOK pL286 286 && ptTest pL286 (runFrom pL286 (fmask pL286) (cmask pL286) (hmask pL286) 1 285 (true, (init pL286), (init pL286))) 286 143 false) = true := by
  decide +kernel
theorem L286_ok : RunOK pL286 286 (runFrom pL286 (fmask pL286) (cmask pL286) (hmask pL286) 1 285 (true, (init pL286), (init pL286))) ∧ ptTest pL286 (runFrom pL286 (fmask pL286) (cmask pL286) (hmask pL286) 1 285 (true, (init pL286), (init pL286))) 286 143 false = true :=
  fin_run (runOK_init (prmOK_of_and L286_fin) true) (by decide) rfl L286_fin ptTest_fst
theorem H286_fin : (prmOK pH286 286 && ptTest pH286 (runFrom pH286 (fmask pH286) (cmask pH286) (hmask pH286) 1 285 (true, (init pH286), (init pH286))) 286 143 true) = true := by
  decide +kernel
theorem H286_ok : RunOK pH286 286 (runFrom pH286 (fmask pH286) (cmask pH286) (hmask pH286) 1 285 (true, (init pH286), (init pH286))) ∧ ptTest pH286 (runFrom pH286 (fmask pH286) (cmask pH286) (hmask pH286) 1 285 (true, (init pH286), (init pH286))) 286 143 true = true :=
  fin_run (runOK_init (prmOK_of_and H286_fin) true) (by decide) rfl H286_fin ptTest_fst
theorem I286_fin : (prmOK pI286 286 && intTest pI286 (runFrom pI286 (fmask pI286) (cmask pI286) (hmask pI286) 1 285 (true, (init pI286), (init pI286))) 286 11 true) = true := by
  decide +kernel
theorem I286_ok : RunOK pI286 286 (runFrom pI286 (fmask pI286) (cmask pI286) (hmask pI286) 1 285 (true, (init pI286), (init pI286))) ∧ intTest pI286 (runFrom pI286 (fmask pI286) (cmask pI286) (hmask pI286) 1 285 (true, (init pI286), (init pI286))) 286 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I286_fin) true) (by decide) rfl I286_fin intTest_fst
theorem link286 : linkOK pL286 pH286 pI286 = true := by decide +kernel
theorem cvx286 : ConvexBetweenHumps 286 :=
  cvx_of L286_ok H286_ok I286_ok link286 (by decide)
theorem cenlink286 : cenLinkOK pI286 286 = true := by decide +kernel
theorem cen286 : CenterUniqueMin 286 ∧ DipHyp 286 ∧ OnePointHyps 286 :=
  cen_of L286_ok H286_ok I286_ok link286 cenlink286

/-! ### `N = 287` -/

def pL287 : Prm := ⟨65, 31, 31, 289, 11, 18446744073709551616, 450472888061664345, 450472888061664345⟩
def pH287 : Prm := ⟨65, 31, 31, 289, 11, 18446744073709551616, 450490480247708761, 450490480247708761⟩
def pI287 : Prm := ⟨57, 28, 26, 289, 11, 18446744073709551616, 450472888061664345, 450490480247708761⟩
theorem L287_fin : (prmOK pL287 287 && ptTest pL287 (runFrom pL287 (fmask pL287) (cmask pL287) (hmask pL287) 1 286 (true, (init pL287), (init pL287))) 287 144 false) = true := by
  decide +kernel
theorem L287_ok : RunOK pL287 287 (runFrom pL287 (fmask pL287) (cmask pL287) (hmask pL287) 1 286 (true, (init pL287), (init pL287))) ∧ ptTest pL287 (runFrom pL287 (fmask pL287) (cmask pL287) (hmask pL287) 1 286 (true, (init pL287), (init pL287))) 287 144 false = true :=
  fin_run (runOK_init (prmOK_of_and L287_fin) true) (by decide) rfl L287_fin ptTest_fst
theorem H287_fin : (prmOK pH287 287 && ptTest pH287 (runFrom pH287 (fmask pH287) (cmask pH287) (hmask pH287) 1 286 (true, (init pH287), (init pH287))) 287 144 true) = true := by
  decide +kernel
theorem H287_ok : RunOK pH287 287 (runFrom pH287 (fmask pH287) (cmask pH287) (hmask pH287) 1 286 (true, (init pH287), (init pH287))) ∧ ptTest pH287 (runFrom pH287 (fmask pH287) (cmask pH287) (hmask pH287) 1 286 (true, (init pH287), (init pH287))) 287 144 true = true :=
  fin_run (runOK_init (prmOK_of_and H287_fin) true) (by decide) rfl H287_fin ptTest_fst
theorem I287_fin : (prmOK pI287 287 && intTest pI287 (runFrom pI287 (fmask pI287) (cmask pI287) (hmask pI287) 1 286 (true, (init pI287), (init pI287))) 287 11 false) = true := by
  decide +kernel
theorem I287_ok : RunOK pI287 287 (runFrom pI287 (fmask pI287) (cmask pI287) (hmask pI287) 1 286 (true, (init pI287), (init pI287))) ∧ intTest pI287 (runFrom pI287 (fmask pI287) (cmask pI287) (hmask pI287) 1 286 (true, (init pI287), (init pI287))) 287 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I287_fin) true) (by decide) rfl I287_fin intTest_fst
theorem link287 : linkOK pL287 pH287 pI287 = true := by decide +kernel
theorem cvx287 : ConvexBetweenHumps 287 :=
  cvx_of L287_ok H287_ok I287_ok link287 (by decide)

/-! ### `N = 288` -/

def pL288 : Prm := ⟨64, 30, 31, 290, 11, 18446744073709551616, 449326040108123075, 449326040108123075⟩
def pH288 : Prm := ⟨64, 30, 31, 290, 11, 18446744073709551616, 449343632294167491, 449343632294167491⟩
def pI288 : Prm := ⟨57, 28, 26, 290, 11, 18446744073709551616, 449326040108123075, 449343632294167491⟩
theorem L288_fin : (prmOK pL288 288 && ptTest pL288 (runFrom pL288 (fmask pL288) (cmask pL288) (hmask pL288) 1 287 (true, (init pL288), (init pL288))) 288 144 false) = true := by
  decide +kernel
theorem L288_ok : RunOK pL288 288 (runFrom pL288 (fmask pL288) (cmask pL288) (hmask pL288) 1 287 (true, (init pL288), (init pL288))) ∧ ptTest pL288 (runFrom pL288 (fmask pL288) (cmask pL288) (hmask pL288) 1 287 (true, (init pL288), (init pL288))) 288 144 false = true :=
  fin_run (runOK_init (prmOK_of_and L288_fin) true) (by decide) rfl L288_fin ptTest_fst
theorem H288_fin : (prmOK pH288 288 && ptTest pH288 (runFrom pH288 (fmask pH288) (cmask pH288) (hmask pH288) 1 287 (true, (init pH288), (init pH288))) 288 144 true) = true := by
  decide +kernel
theorem H288_ok : RunOK pH288 288 (runFrom pH288 (fmask pH288) (cmask pH288) (hmask pH288) 1 287 (true, (init pH288), (init pH288))) ∧ ptTest pH288 (runFrom pH288 (fmask pH288) (cmask pH288) (hmask pH288) 1 287 (true, (init pH288), (init pH288))) 288 144 true = true :=
  fin_run (runOK_init (prmOK_of_and H288_fin) true) (by decide) rfl H288_fin ptTest_fst
theorem I288_fin : (prmOK pI288 288 && intTest pI288 (runFrom pI288 (fmask pI288) (cmask pI288) (hmask pI288) 1 287 (true, (init pI288), (init pI288))) 288 11 true) = true := by
  decide +kernel
theorem I288_ok : RunOK pI288 288 (runFrom pI288 (fmask pI288) (cmask pI288) (hmask pI288) 1 287 (true, (init pI288), (init pI288))) ∧ intTest pI288 (runFrom pI288 (fmask pI288) (cmask pI288) (hmask pI288) 1 287 (true, (init pI288), (init pI288))) 288 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I288_fin) true) (by decide) rfl I288_fin intTest_fst
theorem link288 : linkOK pL288 pH288 pI288 = true := by decide +kernel
theorem cvx288 : ConvexBetweenHumps 288 :=
  cvx_of L288_ok H288_ok I288_ok link288 (by decide)
theorem cenlink288 : cenLinkOK pI288 288 = true := by decide +kernel
theorem cen288 : CenterUniqueMin 288 ∧ DipHyp 288 ∧ OnePointHyps 288 :=
  cen_of L288_ok H288_ok I288_ok link288 cenlink288

/-! ### `N = 289` -/

def pL289 : Prm := ⟨65, 31, 31, 291, 11, 18446744073709551616, 448180641024690964, 448180641024690964⟩
def pH289 : Prm := ⟨64, 30, 31, 291, 11, 18446744073709551616, 448198233210735380, 448198233210735380⟩
def pI289 : Prm := ⟨57, 28, 26, 291, 11, 18446744073709551616, 448180641024690964, 448198233210735380⟩
theorem L289_fin : (prmOK pL289 289 && ptTest pL289 (runFrom pL289 (fmask pL289) (cmask pL289) (hmask pL289) 1 288 (true, (init pL289), (init pL289))) 289 145 false) = true := by
  decide +kernel
theorem L289_ok : RunOK pL289 289 (runFrom pL289 (fmask pL289) (cmask pL289) (hmask pL289) 1 288 (true, (init pL289), (init pL289))) ∧ ptTest pL289 (runFrom pL289 (fmask pL289) (cmask pL289) (hmask pL289) 1 288 (true, (init pL289), (init pL289))) 289 145 false = true :=
  fin_run (runOK_init (prmOK_of_and L289_fin) true) (by decide) rfl L289_fin ptTest_fst
theorem H289_fin : (prmOK pH289 289 && ptTest pH289 (runFrom pH289 (fmask pH289) (cmask pH289) (hmask pH289) 1 288 (true, (init pH289), (init pH289))) 289 145 true) = true := by
  decide +kernel
theorem H289_ok : RunOK pH289 289 (runFrom pH289 (fmask pH289) (cmask pH289) (hmask pH289) 1 288 (true, (init pH289), (init pH289))) ∧ ptTest pH289 (runFrom pH289 (fmask pH289) (cmask pH289) (hmask pH289) 1 288 (true, (init pH289), (init pH289))) 289 145 true = true :=
  fin_run (runOK_init (prmOK_of_and H289_fin) true) (by decide) rfl H289_fin ptTest_fst
theorem I289_fin : (prmOK pI289 289 && intTest pI289 (runFrom pI289 (fmask pI289) (cmask pI289) (hmask pI289) 1 288 (true, (init pI289), (init pI289))) 289 11 false) = true := by
  decide +kernel
theorem I289_ok : RunOK pI289 289 (runFrom pI289 (fmask pI289) (cmask pI289) (hmask pI289) 1 288 (true, (init pI289), (init pI289))) ∧ intTest pI289 (runFrom pI289 (fmask pI289) (cmask pI289) (hmask pI289) 1 288 (true, (init pI289), (init pI289))) 289 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I289_fin) true) (by decide) rfl I289_fin intTest_fst
theorem link289 : linkOK pL289 pH289 pI289 = true := by decide +kernel
theorem cvx289 : ConvexBetweenHumps 289 :=
  cvx_of L289_ok H289_ok I289_ok link289 (by decide)

/-! ### `N = 290` -/

def pL290 : Prm := ⟨65, 31, 31, 292, 11, 18446744073709551616, 447046805346367385, 447046805346367385⟩
def pH290 : Prm := ⟨65, 31, 31, 292, 11, 18446744073709551616, 447064397532411801, 447064397532411801⟩
def pI290 : Prm := ⟨57, 28, 26, 292, 11, 18446744073709551616, 447046805346367385, 447064397532411801⟩
theorem L290_fin : (prmOK pL290 290 && ptTest pL290 (runFrom pL290 (fmask pL290) (cmask pL290) (hmask pL290) 1 289 (true, (init pL290), (init pL290))) 290 145 false) = true := by
  decide +kernel
theorem L290_ok : RunOK pL290 290 (runFrom pL290 (fmask pL290) (cmask pL290) (hmask pL290) 1 289 (true, (init pL290), (init pL290))) ∧ ptTest pL290 (runFrom pL290 (fmask pL290) (cmask pL290) (hmask pL290) 1 289 (true, (init pL290), (init pL290))) 290 145 false = true :=
  fin_run (runOK_init (prmOK_of_and L290_fin) true) (by decide) rfl L290_fin ptTest_fst
theorem H290_fin : (prmOK pH290 290 && ptTest pH290 (runFrom pH290 (fmask pH290) (cmask pH290) (hmask pH290) 1 289 (true, (init pH290), (init pH290))) 290 145 true) = true := by
  decide +kernel
theorem H290_ok : RunOK pH290 290 (runFrom pH290 (fmask pH290) (cmask pH290) (hmask pH290) 1 289 (true, (init pH290), (init pH290))) ∧ ptTest pH290 (runFrom pH290 (fmask pH290) (cmask pH290) (hmask pH290) 1 289 (true, (init pH290), (init pH290))) 290 145 true = true :=
  fin_run (runOK_init (prmOK_of_and H290_fin) true) (by decide) rfl H290_fin ptTest_fst
theorem I290_fin : (prmOK pI290 290 && intTest pI290 (runFrom pI290 (fmask pI290) (cmask pI290) (hmask pI290) 1 289 (true, (init pI290), (init pI290))) 290 11 true) = true := by
  decide +kernel
theorem I290_ok : RunOK pI290 290 (runFrom pI290 (fmask pI290) (cmask pI290) (hmask pI290) 1 289 (true, (init pI290), (init pI290))) ∧ intTest pI290 (runFrom pI290 (fmask pI290) (cmask pI290) (hmask pI290) 1 289 (true, (init pI290), (init pI290))) 290 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I290_fin) true) (by decide) rfl I290_fin intTest_fst
theorem link290 : linkOK pL290 pH290 pI290 = true := by decide +kernel
theorem cvx290 : ConvexBetweenHumps 290 :=
  cvx_of L290_ok H290_ok I290_ok link290 (by decide)
theorem cenlink290 : cenLinkOK pI290 290 = true := by decide +kernel
theorem cen290 : CenterUniqueMin 290 ∧ DipHyp 290 ∧ OnePointHyps 290 :=
  cen_of L290_ok H290_ok I290_ok link290 cenlink290

/-! ### `N = 291` -/

def pL291 : Prm := ⟨65, 31, 31, 293, 11, 18446744073709551616, 445914407453172410, 445914407453172410⟩
def pH291 : Prm := ⟨65, 31, 31, 293, 11, 18446744073709551616, 445931999639216826, 445931999639216826⟩
def pI291 : Prm := ⟨57, 28, 26, 293, 11, 18446744073709551616, 445914407453172410, 445931999639216826⟩
theorem L291_fin : (prmOK pL291 291 && ptTest pL291 (runFrom pL291 (fmask pL291) (cmask pL291) (hmask pL291) 1 290 (true, (init pL291), (init pL291))) 291 146 false) = true := by
  decide +kernel
theorem L291_ok : RunOK pL291 291 (runFrom pL291 (fmask pL291) (cmask pL291) (hmask pL291) 1 290 (true, (init pL291), (init pL291))) ∧ ptTest pL291 (runFrom pL291 (fmask pL291) (cmask pL291) (hmask pL291) 1 290 (true, (init pL291), (init pL291))) 291 146 false = true :=
  fin_run (runOK_init (prmOK_of_and L291_fin) true) (by decide) rfl L291_fin ptTest_fst
theorem H291_fin : (prmOK pH291 291 && ptTest pH291 (runFrom pH291 (fmask pH291) (cmask pH291) (hmask pH291) 1 290 (true, (init pH291), (init pH291))) 291 146 true) = true := by
  decide +kernel
theorem H291_ok : RunOK pH291 291 (runFrom pH291 (fmask pH291) (cmask pH291) (hmask pH291) 1 290 (true, (init pH291), (init pH291))) ∧ ptTest pH291 (runFrom pH291 (fmask pH291) (cmask pH291) (hmask pH291) 1 290 (true, (init pH291), (init pH291))) 291 146 true = true :=
  fin_run (runOK_init (prmOK_of_and H291_fin) true) (by decide) rfl H291_fin ptTest_fst
theorem I291_fin : (prmOK pI291 291 && intTest pI291 (runFrom pI291 (fmask pI291) (cmask pI291) (hmask pI291) 1 290 (true, (init pI291), (init pI291))) 291 11 false) = true := by
  decide +kernel
theorem I291_ok : RunOK pI291 291 (runFrom pI291 (fmask pI291) (cmask pI291) (hmask pI291) 1 290 (true, (init pI291), (init pI291))) ∧ intTest pI291 (runFrom pI291 (fmask pI291) (cmask pI291) (hmask pI291) 1 290 (true, (init pI291), (init pI291))) 291 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I291_fin) true) (by decide) rfl I291_fin intTest_fst
theorem link291 : linkOK pL291 pH291 pI291 = true := by decide +kernel
theorem cvx291 : ConvexBetweenHumps 291 :=
  cvx_of L291_ok H291_ok I291_ok link291 (by decide)

/-! ### `N = 292` -/

def pL292 : Prm := ⟨66, 31, 32, 294, 11, 18446744073709551616, 444797751783351609, 444797751783351609⟩
def pH292 : Prm := ⟨67, 32, 32, 294, 11, 18446744073709551616, 444806547876373817, 444806547876373817⟩
def pI292 : Prm := ⟨57, 27, 27, 294, 11, 18446744073709551616, 444797751783351609, 444806547876373817⟩
theorem L292_fin : (prmOK pL292 292 && ptTest pL292 (runFrom pL292 (fmask pL292) (cmask pL292) (hmask pL292) 1 291 (true, (init pL292), (init pL292))) 292 146 false) = true := by
  decide +kernel
theorem L292_ok : RunOK pL292 292 (runFrom pL292 (fmask pL292) (cmask pL292) (hmask pL292) 1 291 (true, (init pL292), (init pL292))) ∧ ptTest pL292 (runFrom pL292 (fmask pL292) (cmask pL292) (hmask pL292) 1 291 (true, (init pL292), (init pL292))) 292 146 false = true :=
  fin_run (runOK_init (prmOK_of_and L292_fin) true) (by decide) rfl L292_fin ptTest_fst
theorem H292_fin : (prmOK pH292 292 && ptTest pH292 (runFrom pH292 (fmask pH292) (cmask pH292) (hmask pH292) 1 291 (true, (init pH292), (init pH292))) 292 146 true) = true := by
  decide +kernel
theorem H292_ok : RunOK pH292 292 (runFrom pH292 (fmask pH292) (cmask pH292) (hmask pH292) 1 291 (true, (init pH292), (init pH292))) ∧ ptTest pH292 (runFrom pH292 (fmask pH292) (cmask pH292) (hmask pH292) 1 291 (true, (init pH292), (init pH292))) 292 146 true = true :=
  fin_run (runOK_init (prmOK_of_and H292_fin) true) (by decide) rfl H292_fin ptTest_fst
theorem I292_fin : (prmOK pI292 292 && intTest pI292 (runFrom pI292 (fmask pI292) (cmask pI292) (hmask pI292) 1 291 (true, (init pI292), (init pI292))) 292 11 true) = true := by
  decide +kernel
theorem I292_ok : RunOK pI292 292 (runFrom pI292 (fmask pI292) (cmask pI292) (hmask pI292) 1 291 (true, (init pI292), (init pI292))) ∧ intTest pI292 (runFrom pI292 (fmask pI292) (cmask pI292) (hmask pI292) 1 291 (true, (init pI292), (init pI292))) 292 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I292_fin) true) (by decide) rfl I292_fin intTest_fst
theorem link292 : linkOK pL292 pH292 pI292 = true := by decide +kernel
theorem cvx292 : ConvexBetweenHumps 292 :=
  cvx_of L292_ok H292_ok I292_ok link292 (by decide)
theorem cenlink292 : cenLinkOK pI292 292 = true := by decide +kernel
theorem cen292 : CenterUniqueMin 292 ∧ DipHyp 292 ∧ OnePointHyps 292 :=
  cen_of L292_ok H292_ok I292_ok link292 cenlink292

/-! ### `N = 293` -/

def pL293 : Prm := ⟨67, 32, 32, 295, 11, 18446744073709551616, 443678124727193658, 443678124727193658⟩
def pH293 : Prm := ⟨66, 31, 32, 295, 11, 18446744073709551616, 443686920820215866, 443686920820215866⟩
def pI293 : Prm := ⟨57, 27, 27, 295, 11, 18446744073709551616, 443678124727193658, 443686920820215866⟩
theorem L293_fin : (prmOK pL293 293 && ptTest pL293 (runFrom pL293 (fmask pL293) (cmask pL293) (hmask pL293) 1 292 (true, (init pL293), (init pL293))) 293 147 false) = true := by
  decide +kernel
theorem L293_ok : RunOK pL293 293 (runFrom pL293 (fmask pL293) (cmask pL293) (hmask pL293) 1 292 (true, (init pL293), (init pL293))) ∧ ptTest pL293 (runFrom pL293 (fmask pL293) (cmask pL293) (hmask pL293) 1 292 (true, (init pL293), (init pL293))) 293 147 false = true :=
  fin_run (runOK_init (prmOK_of_and L293_fin) true) (by decide) rfl L293_fin ptTest_fst
theorem H293_fin : (prmOK pH293 293 && ptTest pH293 (runFrom pH293 (fmask pH293) (cmask pH293) (hmask pH293) 1 292 (true, (init pH293), (init pH293))) 293 147 true) = true := by
  decide +kernel
theorem H293_ok : RunOK pH293 293 (runFrom pH293 (fmask pH293) (cmask pH293) (hmask pH293) 1 292 (true, (init pH293), (init pH293))) ∧ ptTest pH293 (runFrom pH293 (fmask pH293) (cmask pH293) (hmask pH293) 1 292 (true, (init pH293), (init pH293))) 293 147 true = true :=
  fin_run (runOK_init (prmOK_of_and H293_fin) true) (by decide) rfl H293_fin ptTest_fst
theorem I293_fin : (prmOK pI293 293 && intTest pI293 (runFrom pI293 (fmask pI293) (cmask pI293) (hmask pI293) 1 292 (true, (init pI293), (init pI293))) 293 11 false) = true := by
  decide +kernel
theorem I293_ok : RunOK pI293 293 (runFrom pI293 (fmask pI293) (cmask pI293) (hmask pI293) 1 292 (true, (init pI293), (init pI293))) ∧ intTest pI293 (runFrom pI293 (fmask pI293) (cmask pI293) (hmask pI293) 1 292 (true, (init pI293), (init pI293))) 293 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I293_fin) true) (by decide) rfl I293_fin intTest_fst
theorem link293 : linkOK pL293 pH293 pI293 = true := by decide +kernel
theorem cvx293 : ConvexBetweenHumps 293 :=
  cvx_of L293_ok H293_ok I293_ok link293 (by decide)

/-! ### `N = 294` -/

def pL294 : Prm := ⟨67, 32, 32, 296, 11, 18446744073709551616, 442569628200771075, 442569628200771075⟩
def pH294 : Prm := ⟨67, 32, 32, 296, 11, 18446744073709551616, 442578424293793283, 442578424293793283⟩
def pI294 : Prm := ⟨57, 27, 27, 296, 11, 18446744073709551616, 442569628200771075, 442578424293793283⟩
theorem L294_fin : (prmOK pL294 294 && ptTest pL294 (runFrom pL294 (fmask pL294) (cmask pL294) (hmask pL294) 1 293 (true, (init pL294), (init pL294))) 294 147 false) = true := by
  decide +kernel
theorem L294_ok : RunOK pL294 294 (runFrom pL294 (fmask pL294) (cmask pL294) (hmask pL294) 1 293 (true, (init pL294), (init pL294))) ∧ ptTest pL294 (runFrom pL294 (fmask pL294) (cmask pL294) (hmask pL294) 1 293 (true, (init pL294), (init pL294))) 294 147 false = true :=
  fin_run (runOK_init (prmOK_of_and L294_fin) true) (by decide) rfl L294_fin ptTest_fst
theorem H294_fin : (prmOK pH294 294 && ptTest pH294 (runFrom pH294 (fmask pH294) (cmask pH294) (hmask pH294) 1 293 (true, (init pH294), (init pH294))) 294 147 true) = true := by
  decide +kernel
theorem H294_ok : RunOK pH294 294 (runFrom pH294 (fmask pH294) (cmask pH294) (hmask pH294) 1 293 (true, (init pH294), (init pH294))) ∧ ptTest pH294 (runFrom pH294 (fmask pH294) (cmask pH294) (hmask pH294) 1 293 (true, (init pH294), (init pH294))) 294 147 true = true :=
  fin_run (runOK_init (prmOK_of_and H294_fin) true) (by decide) rfl H294_fin ptTest_fst
theorem I294_fin : (prmOK pI294 294 && intTest pI294 (runFrom pI294 (fmask pI294) (cmask pI294) (hmask pI294) 1 293 (true, (init pI294), (init pI294))) 294 11 true) = true := by
  decide +kernel
theorem I294_ok : RunOK pI294 294 (runFrom pI294 (fmask pI294) (cmask pI294) (hmask pI294) 1 293 (true, (init pI294), (init pI294))) ∧ intTest pI294 (runFrom pI294 (fmask pI294) (cmask pI294) (hmask pI294) 1 293 (true, (init pI294), (init pI294))) 294 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I294_fin) true) (by decide) rfl I294_fin intTest_fst
theorem link294 : linkOK pL294 pH294 pI294 = true := by decide +kernel
theorem cvx294 : ConvexBetweenHumps 294 :=
  cvx_of L294_ok H294_ok I294_ok link294 (by decide)
theorem cenlink294 : cenLinkOK pI294 294 = true := by decide +kernel
theorem cen294 : CenterUniqueMin 294 ∧ DipHyp 294 ∧ OnePointHyps 294 :=
  cen_of L294_ok H294_ok I294_ok link294 cenlink294

/-! ### `N = 295` -/

def pL295 : Prm := ⟨67, 32, 32, 297, 11, 18446744073709551616, 441462547179019989, 441462547179019989⟩
def pH295 : Prm := ⟨67, 32, 32, 297, 11, 18446744073709551616, 441471343272042197, 441471343272042197⟩
def pI295 : Prm := ⟨57, 27, 27, 297, 11, 18446744073709551616, 441462547179019989, 441471343272042197⟩
theorem L295_fin : (prmOK pL295 295 && ptTest pL295 (runFrom pL295 (fmask pL295) (cmask pL295) (hmask pL295) 1 294 (true, (init pL295), (init pL295))) 295 148 false) = true := by
  decide +kernel
theorem L295_ok : RunOK pL295 295 (runFrom pL295 (fmask pL295) (cmask pL295) (hmask pL295) 1 294 (true, (init pL295), (init pL295))) ∧ ptTest pL295 (runFrom pL295 (fmask pL295) (cmask pL295) (hmask pL295) 1 294 (true, (init pL295), (init pL295))) 295 148 false = true :=
  fin_run (runOK_init (prmOK_of_and L295_fin) true) (by decide) rfl L295_fin ptTest_fst
theorem H295_fin : (prmOK pH295 295 && ptTest pH295 (runFrom pH295 (fmask pH295) (cmask pH295) (hmask pH295) 1 294 (true, (init pH295), (init pH295))) 295 148 true) = true := by
  decide +kernel
theorem H295_ok : RunOK pH295 295 (runFrom pH295 (fmask pH295) (cmask pH295) (hmask pH295) 1 294 (true, (init pH295), (init pH295))) ∧ ptTest pH295 (runFrom pH295 (fmask pH295) (cmask pH295) (hmask pH295) 1 294 (true, (init pH295), (init pH295))) 295 148 true = true :=
  fin_run (runOK_init (prmOK_of_and H295_fin) true) (by decide) rfl H295_fin ptTest_fst
theorem I295_fin : (prmOK pI295 295 && intTest pI295 (runFrom pI295 (fmask pI295) (cmask pI295) (hmask pI295) 1 294 (true, (init pI295), (init pI295))) 295 11 false) = true := by
  decide +kernel
theorem I295_ok : RunOK pI295 295 (runFrom pI295 (fmask pI295) (cmask pI295) (hmask pI295) 1 294 (true, (init pI295), (init pI295))) ∧ intTest pI295 (runFrom pI295 (fmask pI295) (cmask pI295) (hmask pI295) 1 294 (true, (init pI295), (init pI295))) 295 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I295_fin) true) (by decide) rfl I295_fin intTest_fst
theorem link295 : linkOK pL295 pH295 pI295 = true := by decide +kernel
theorem cvx295 : ConvexBetweenHumps 295 :=
  cvx_of L295_ok H295_ok I295_ok link295 (by decide)

/-! ### `N = 296` -/

def pL296 : Prm := ⟨67, 32, 32, 298, 11, 18446744073709551616, 440366388443093927, 440366388443093927⟩
def pH296 : Prm := ⟨67, 32, 32, 298, 11, 18446744073709551616, 440375184536116135, 440375184536116135⟩
def pI296 : Prm := ⟨57, 27, 27, 298, 11, 18446744073709551616, 440366388443093927, 440375184536116135⟩
theorem L296_fin : (prmOK pL296 296 && ptTest pL296 (runFrom pL296 (fmask pL296) (cmask pL296) (hmask pL296) 1 295 (true, (init pL296), (init pL296))) 296 148 false) = true := by
  decide +kernel
theorem L296_ok : RunOK pL296 296 (runFrom pL296 (fmask pL296) (cmask pL296) (hmask pL296) 1 295 (true, (init pL296), (init pL296))) ∧ ptTest pL296 (runFrom pL296 (fmask pL296) (cmask pL296) (hmask pL296) 1 295 (true, (init pL296), (init pL296))) 296 148 false = true :=
  fin_run (runOK_init (prmOK_of_and L296_fin) true) (by decide) rfl L296_fin ptTest_fst
theorem H296_fin : (prmOK pH296 296 && ptTest pH296 (runFrom pH296 (fmask pH296) (cmask pH296) (hmask pH296) 1 295 (true, (init pH296), (init pH296))) 296 148 true) = true := by
  decide +kernel
theorem H296_ok : RunOK pH296 296 (runFrom pH296 (fmask pH296) (cmask pH296) (hmask pH296) 1 295 (true, (init pH296), (init pH296))) ∧ ptTest pH296 (runFrom pH296 (fmask pH296) (cmask pH296) (hmask pH296) 1 295 (true, (init pH296), (init pH296))) 296 148 true = true :=
  fin_run (runOK_init (prmOK_of_and H296_fin) true) (by decide) rfl H296_fin ptTest_fst
theorem I296_fin : (prmOK pI296 296 && intTest pI296 (runFrom pI296 (fmask pI296) (cmask pI296) (hmask pI296) 1 295 (true, (init pI296), (init pI296))) 296 11 true) = true := by
  decide +kernel
theorem I296_ok : RunOK pI296 296 (runFrom pI296 (fmask pI296) (cmask pI296) (hmask pI296) 1 295 (true, (init pI296), (init pI296))) ∧ intTest pI296 (runFrom pI296 (fmask pI296) (cmask pI296) (hmask pI296) 1 295 (true, (init pI296), (init pI296))) 296 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I296_fin) true) (by decide) rfl I296_fin intTest_fst
theorem link296 : linkOK pL296 pH296 pI296 = true := by decide +kernel
theorem cvx296 : ConvexBetweenHumps 296 :=
  cvx_of L296_ok H296_ok I296_ok link296 (by decide)
theorem cenlink296 : cenLinkOK pI296 296 = true := by decide +kernel
theorem cen296 : CenterUniqueMin 296 ∧ DipHyp 296 ∧ OnePointHyps 296 :=
  cen_of L296_ok H296_ok I296_ok link296 cenlink296

/-! ### `N = 297` -/

def pL297 : Prm := ⟨67, 32, 32, 299, 11, 18446744073709551616, 439271634034661980, 439271634034661980⟩
def pH297 : Prm := ⟨67, 32, 32, 299, 11, 18446744073709551616, 439280430127684188, 439280430127684188⟩
def pI297 : Prm := ⟨57, 27, 27, 299, 11, 18446744073709551616, 439271634034661980, 439280430127684188⟩
theorem L297_fin : (prmOK pL297 297 && ptTest pL297 (runFrom pL297 (fmask pL297) (cmask pL297) (hmask pL297) 1 296 (true, (init pL297), (init pL297))) 297 149 false) = true := by
  decide +kernel
theorem L297_ok : RunOK pL297 297 (runFrom pL297 (fmask pL297) (cmask pL297) (hmask pL297) 1 296 (true, (init pL297), (init pL297))) ∧ ptTest pL297 (runFrom pL297 (fmask pL297) (cmask pL297) (hmask pL297) 1 296 (true, (init pL297), (init pL297))) 297 149 false = true :=
  fin_run (runOK_init (prmOK_of_and L297_fin) true) (by decide) rfl L297_fin ptTest_fst
theorem H297_fin : (prmOK pH297 297 && ptTest pH297 (runFrom pH297 (fmask pH297) (cmask pH297) (hmask pH297) 1 296 (true, (init pH297), (init pH297))) 297 149 true) = true := by
  decide +kernel
theorem H297_ok : RunOK pH297 297 (runFrom pH297 (fmask pH297) (cmask pH297) (hmask pH297) 1 296 (true, (init pH297), (init pH297))) ∧ ptTest pH297 (runFrom pH297 (fmask pH297) (cmask pH297) (hmask pH297) 1 296 (true, (init pH297), (init pH297))) 297 149 true = true :=
  fin_run (runOK_init (prmOK_of_and H297_fin) true) (by decide) rfl H297_fin ptTest_fst
theorem I297_fin : (prmOK pI297 297 && intTest pI297 (runFrom pI297 (fmask pI297) (cmask pI297) (hmask pI297) 1 296 (true, (init pI297), (init pI297))) 297 11 false) = true := by
  decide +kernel
theorem I297_ok : RunOK pI297 297 (runFrom pI297 (fmask pI297) (cmask pI297) (hmask pI297) 1 296 (true, (init pI297), (init pI297))) ∧ intTest pI297 (runFrom pI297 (fmask pI297) (cmask pI297) (hmask pI297) 1 296 (true, (init pI297), (init pI297))) 297 11 false = true :=
  fin_run (runOK_init (prmOK_of_and I297_fin) true) (by decide) rfl I297_fin intTest_fst
theorem link297 : linkOK pL297 pH297 pI297 = true := by decide +kernel
theorem cvx297 : ConvexBetweenHumps 297 :=
  cvx_of L297_ok H297_ok I297_ok link297 (by decide)

/-! ### `N = 298` -/

def pL298 : Prm := ⟨67, 32, 32, 300, 11, 18446744073709551616, 438187598900323865, 438187598900323865⟩
def pH298 : Prm := ⟨67, 32, 32, 300, 11, 18446744073709551616, 438196394993346073, 438196394993346073⟩
def pI298 : Prm := ⟨57, 28, 26, 300, 11, 18446744073709551616, 438187598900323865, 438196394993346073⟩
theorem L298_fin : (prmOK pL298 298 && ptTest pL298 (runFrom pL298 (fmask pL298) (cmask pL298) (hmask pL298) 1 297 (true, (init pL298), (init pL298))) 298 149 false) = true := by
  decide +kernel
theorem L298_ok : RunOK pL298 298 (runFrom pL298 (fmask pL298) (cmask pL298) (hmask pL298) 1 297 (true, (init pL298), (init pL298))) ∧ ptTest pL298 (runFrom pL298 (fmask pL298) (cmask pL298) (hmask pL298) 1 297 (true, (init pL298), (init pL298))) 298 149 false = true :=
  fin_run (runOK_init (prmOK_of_and L298_fin) true) (by decide) rfl L298_fin ptTest_fst
theorem H298_fin : (prmOK pH298 298 && ptTest pH298 (runFrom pH298 (fmask pH298) (cmask pH298) (hmask pH298) 1 297 (true, (init pH298), (init pH298))) 298 149 true) = true := by
  decide +kernel
theorem H298_ok : RunOK pH298 298 (runFrom pH298 (fmask pH298) (cmask pH298) (hmask pH298) 1 297 (true, (init pH298), (init pH298))) ∧ ptTest pH298 (runFrom pH298 (fmask pH298) (cmask pH298) (hmask pH298) 1 297 (true, (init pH298), (init pH298))) 298 149 true = true :=
  fin_run (runOK_init (prmOK_of_and H298_fin) true) (by decide) rfl H298_fin ptTest_fst
theorem I298_fin : (prmOK pI298 298 && intTest pI298 (runFrom pI298 (fmask pI298) (cmask pI298) (hmask pI298) 1 297 (true, (init pI298), (init pI298))) 298 11 true) = true := by
  decide +kernel
theorem I298_ok : RunOK pI298 298 (runFrom pI298 (fmask pI298) (cmask pI298) (hmask pI298) 1 297 (true, (init pI298), (init pI298))) ∧ intTest pI298 (runFrom pI298 (fmask pI298) (cmask pI298) (hmask pI298) 1 297 (true, (init pI298), (init pI298))) 298 11 true = true :=
  fin_run (runOK_init (prmOK_of_and I298_fin) true) (by decide) rfl I298_fin intTest_fst
theorem link298 : linkOK pL298 pH298 pI298 = true := by decide +kernel
theorem cvx298 : ConvexBetweenHumps 298 :=
  cvx_of L298_ok H298_ok I298_ok link298 (by decide)
theorem cenlink298 : cenLinkOK pI298 298 = true := by decide +kernel
theorem cen298 : CenterUniqueMin 298 ∧ DipHyp 298 ∧ OnePointHyps 298 :=
  cen_of L298_ok H298_ok I298_ok link298 cenlink298

/-! ### `N = 299` -/

def pL299 : Prm := ⟨67, 32, 32, 301, 11, 18446744073709551616, 437104956902836360, 437104956902836360⟩
def pH299 : Prm := ⟨67, 32, 32, 301, 11, 18446744073709551616, 437113752995858568, 437113752995858568⟩
def pI299 : Prm := ⟨56, 28, 25, 301, 11, 18446744073709551616, 437104956902836360, 437113752995858568⟩
theorem L299_fin : (prmOK pL299 299 && ptTest pL299 (runFrom pL299 (fmask pL299) (cmask pL299) (hmask pL299) 1 298 (true, (init pL299), (init pL299))) 299 150 false) = true := by
  decide +kernel
theorem L299_ok : RunOK pL299 299 (runFrom pL299 (fmask pL299) (cmask pL299) (hmask pL299) 1 298 (true, (init pL299), (init pL299))) ∧ ptTest pL299 (runFrom pL299 (fmask pL299) (cmask pL299) (hmask pL299) 1 298 (true, (init pL299), (init pL299))) 299 150 false = true :=
  fin_run (runOK_init (prmOK_of_and L299_fin) true) (by decide) rfl L299_fin ptTest_fst
theorem H299_fin : (prmOK pH299 299 && ptTest pH299 (runFrom pH299 (fmask pH299) (cmask pH299) (hmask pH299) 1 298 (true, (init pH299), (init pH299))) 299 150 true) = true := by
  decide +kernel
theorem H299_ok : RunOK pH299 299 (runFrom pH299 (fmask pH299) (cmask pH299) (hmask pH299) 1 298 (true, (init pH299), (init pH299))) ∧ ptTest pH299 (runFrom pH299 (fmask pH299) (cmask pH299) (hmask pH299) 1 298 (true, (init pH299), (init pH299))) 299 150 true = true :=
  fin_run (runOK_init (prmOK_of_and H299_fin) true) (by decide) rfl H299_fin ptTest_fst
theorem I299_fin : (prmOK pI299 299 && intTest pI299 (runFrom pI299 (fmask pI299) (cmask pI299) (hmask pI299) 1 298 (true, (init pI299), (init pI299))) 299 12 false) = true := by
  decide +kernel
theorem I299_ok : RunOK pI299 299 (runFrom pI299 (fmask pI299) (cmask pI299) (hmask pI299) 1 298 (true, (init pI299), (init pI299))) ∧ intTest pI299 (runFrom pI299 (fmask pI299) (cmask pI299) (hmask pI299) 1 298 (true, (init pI299), (init pI299))) 299 12 false = true :=
  fin_run (runOK_init (prmOK_of_and I299_fin) true) (by decide) rfl I299_fin intTest_fst
theorem link299 : linkOK pL299 pH299 pI299 = true := by decide +kernel
theorem cvx299 : ConvexBetweenHumps 299 :=
  cvx_of L299_ok H299_ok I299_ok link299 (by decide)

/-! ### `N = 300` -/

def pL300 : Prm := ⟨67, 32, 32, 302, 11, 18446744073709551616, 436032836235345683, 436032836235345683⟩
def pH300 : Prm := ⟨67, 32, 32, 302, 11, 18446744073709551616, 436041632328367891, 436041632328367891⟩
def pI300 : Prm := ⟨57, 28, 26, 302, 11, 18446744073709551616, 436032836235345683, 436041632328367891⟩
theorem L300_fin : (prmOK pL300 300 && ptTest pL300 (runFrom pL300 (fmask pL300) (cmask pL300) (hmask pL300) 1 299 (true, (init pL300), (init pL300))) 300 150 false) = true := by
  decide +kernel
theorem L300_ok : RunOK pL300 300 (runFrom pL300 (fmask pL300) (cmask pL300) (hmask pL300) 1 299 (true, (init pL300), (init pL300))) ∧ ptTest pL300 (runFrom pL300 (fmask pL300) (cmask pL300) (hmask pL300) 1 299 (true, (init pL300), (init pL300))) 300 150 false = true :=
  fin_run (runOK_init (prmOK_of_and L300_fin) true) (by decide) rfl L300_fin ptTest_fst
theorem H300_fin : (prmOK pH300 300 && ptTest pH300 (runFrom pH300 (fmask pH300) (cmask pH300) (hmask pH300) 1 299 (true, (init pH300), (init pH300))) 300 150 true) = true := by
  decide +kernel
theorem H300_ok : RunOK pH300 300 (runFrom pH300 (fmask pH300) (cmask pH300) (hmask pH300) 1 299 (true, (init pH300), (init pH300))) ∧ ptTest pH300 (runFrom pH300 (fmask pH300) (cmask pH300) (hmask pH300) 1 299 (true, (init pH300), (init pH300))) 300 150 true = true :=
  fin_run (runOK_init (prmOK_of_and H300_fin) true) (by decide) rfl H300_fin ptTest_fst
theorem I300_fin : (prmOK pI300 300 && intTest pI300 (runFrom pI300 (fmask pI300) (cmask pI300) (hmask pI300) 1 299 (true, (init pI300), (init pI300))) 300 12 true) = true := by
  decide +kernel
theorem I300_ok : RunOK pI300 300 (runFrom pI300 (fmask pI300) (cmask pI300) (hmask pI300) 1 299 (true, (init pI300), (init pI300))) ∧ intTest pI300 (runFrom pI300 (fmask pI300) (cmask pI300) (hmask pI300) 1 299 (true, (init pI300), (init pI300))) 300 12 true = true :=
  fin_run (runOK_init (prmOK_of_and I300_fin) true) (by decide) rfl I300_fin intTest_fst
theorem link300 : linkOK pL300 pH300 pI300 = true := by decide +kernel
theorem cvx300 : ConvexBetweenHumps 300 :=
  cvx_of L300_ok H300_ok I300_ok link300 (by decide)
theorem cenlink300 : cenLinkOK pI300 300 = true := by decide +kernel
theorem cen300 : CenterUniqueMin 300 ∧ DipHyp 300 ∧ OnePointHyps 300 :=
  cen_of L300_ok H300_ok I300_ok link300 cenlink300

/-! ### The range -/

theorem cvx_101_300 {N : ℕ} (h1 : 101 ≤ N) (h2 : N ≤ 300) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 200
  · by_cases h4 : N ≤ 150
    · by_cases h6 : N ≤ 125
      · by_cases h8 : N ≤ 112
        · by_cases h10 : N ≤ 106
          · by_cases h12 : N ≤ 103
            · by_cases h14 : N ≤ 101
              · obtain rfl : N = 101 := by omega
                exact cvx101
              · by_cases h16 : N ≤ 102
                · obtain rfl : N = 102 := by omega
                  exact cvx102
                · obtain rfl : N = 103 := by omega
                  exact cvx103
            · by_cases h14 : N ≤ 104
              · obtain rfl : N = 104 := by omega
                exact cvx104
              · by_cases h16 : N ≤ 105
                · obtain rfl : N = 105 := by omega
                  exact cvx105
                · obtain rfl : N = 106 := by omega
                  exact cvx106
          · by_cases h12 : N ≤ 109
            · by_cases h14 : N ≤ 107
              · obtain rfl : N = 107 := by omega
                exact cvx107
              · by_cases h16 : N ≤ 108
                · obtain rfl : N = 108 := by omega
                  exact cvx108
                · obtain rfl : N = 109 := by omega
                  exact cvx109
            · by_cases h14 : N ≤ 110
              · obtain rfl : N = 110 := by omega
                exact cvx110
              · by_cases h16 : N ≤ 111
                · obtain rfl : N = 111 := by omega
                  exact cvx111
                · obtain rfl : N = 112 := by omega
                  exact cvx112
        · by_cases h10 : N ≤ 118
          · by_cases h12 : N ≤ 115
            · by_cases h14 : N ≤ 113
              · obtain rfl : N = 113 := by omega
                exact cvx113
              · by_cases h16 : N ≤ 114
                · obtain rfl : N = 114 := by omega
                  exact cvx114
                · obtain rfl : N = 115 := by omega
                  exact cvx115
            · by_cases h14 : N ≤ 116
              · obtain rfl : N = 116 := by omega
                exact cvx116
              · by_cases h16 : N ≤ 117
                · obtain rfl : N = 117 := by omega
                  exact cvx117
                · obtain rfl : N = 118 := by omega
                  exact cvx118
          · by_cases h12 : N ≤ 121
            · by_cases h14 : N ≤ 119
              · obtain rfl : N = 119 := by omega
                exact cvx119
              · by_cases h16 : N ≤ 120
                · obtain rfl : N = 120 := by omega
                  exact cvx120
                · obtain rfl : N = 121 := by omega
                  exact cvx121
            · by_cases h14 : N ≤ 123
              · by_cases h16 : N ≤ 122
                · obtain rfl : N = 122 := by omega
                  exact cvx122
                · obtain rfl : N = 123 := by omega
                  exact cvx123
              · by_cases h16 : N ≤ 124
                · obtain rfl : N = 124 := by omega
                  exact cvx124
                · obtain rfl : N = 125 := by omega
                  exact cvx125
      · by_cases h8 : N ≤ 137
        · by_cases h10 : N ≤ 131
          · by_cases h12 : N ≤ 128
            · by_cases h14 : N ≤ 126
              · obtain rfl : N = 126 := by omega
                exact cvx126
              · by_cases h16 : N ≤ 127
                · obtain rfl : N = 127 := by omega
                  exact cvx127
                · obtain rfl : N = 128 := by omega
                  exact cvx128
            · by_cases h14 : N ≤ 129
              · obtain rfl : N = 129 := by omega
                exact cvx129
              · by_cases h16 : N ≤ 130
                · obtain rfl : N = 130 := by omega
                  exact cvx130
                · obtain rfl : N = 131 := by omega
                  exact cvx131
          · by_cases h12 : N ≤ 134
            · by_cases h14 : N ≤ 132
              · obtain rfl : N = 132 := by omega
                exact cvx132
              · by_cases h16 : N ≤ 133
                · obtain rfl : N = 133 := by omega
                  exact cvx133
                · obtain rfl : N = 134 := by omega
                  exact cvx134
            · by_cases h14 : N ≤ 135
              · obtain rfl : N = 135 := by omega
                exact cvx135
              · by_cases h16 : N ≤ 136
                · obtain rfl : N = 136 := by omega
                  exact cvx136
                · obtain rfl : N = 137 := by omega
                  exact cvx137
        · by_cases h10 : N ≤ 143
          · by_cases h12 : N ≤ 140
            · by_cases h14 : N ≤ 138
              · obtain rfl : N = 138 := by omega
                exact cvx138
              · by_cases h16 : N ≤ 139
                · obtain rfl : N = 139 := by omega
                  exact cvx139
                · obtain rfl : N = 140 := by omega
                  exact cvx140
            · by_cases h14 : N ≤ 141
              · obtain rfl : N = 141 := by omega
                exact cvx141
              · by_cases h16 : N ≤ 142
                · obtain rfl : N = 142 := by omega
                  exact cvx142
                · obtain rfl : N = 143 := by omega
                  exact cvx143
          · by_cases h12 : N ≤ 146
            · by_cases h14 : N ≤ 144
              · obtain rfl : N = 144 := by omega
                exact cvx144
              · by_cases h16 : N ≤ 145
                · obtain rfl : N = 145 := by omega
                  exact cvx145
                · obtain rfl : N = 146 := by omega
                  exact cvx146
            · by_cases h14 : N ≤ 148
              · by_cases h16 : N ≤ 147
                · obtain rfl : N = 147 := by omega
                  exact cvx147
                · obtain rfl : N = 148 := by omega
                  exact cvx148
              · by_cases h16 : N ≤ 149
                · obtain rfl : N = 149 := by omega
                  exact cvx149
                · obtain rfl : N = 150 := by omega
                  exact cvx150
    · by_cases h6 : N ≤ 175
      · by_cases h8 : N ≤ 162
        · by_cases h10 : N ≤ 156
          · by_cases h12 : N ≤ 153
            · by_cases h14 : N ≤ 151
              · obtain rfl : N = 151 := by omega
                exact cvx151
              · by_cases h16 : N ≤ 152
                · obtain rfl : N = 152 := by omega
                  exact cvx152
                · obtain rfl : N = 153 := by omega
                  exact cvx153
            · by_cases h14 : N ≤ 154
              · obtain rfl : N = 154 := by omega
                exact cvx154
              · by_cases h16 : N ≤ 155
                · obtain rfl : N = 155 := by omega
                  exact cvx155
                · obtain rfl : N = 156 := by omega
                  exact cvx156
          · by_cases h12 : N ≤ 159
            · by_cases h14 : N ≤ 157
              · obtain rfl : N = 157 := by omega
                exact cvx157
              · by_cases h16 : N ≤ 158
                · obtain rfl : N = 158 := by omega
                  exact cvx158
                · obtain rfl : N = 159 := by omega
                  exact cvx159
            · by_cases h14 : N ≤ 160
              · obtain rfl : N = 160 := by omega
                exact cvx160
              · by_cases h16 : N ≤ 161
                · obtain rfl : N = 161 := by omega
                  exact cvx161
                · obtain rfl : N = 162 := by omega
                  exact cvx162
        · by_cases h10 : N ≤ 168
          · by_cases h12 : N ≤ 165
            · by_cases h14 : N ≤ 163
              · obtain rfl : N = 163 := by omega
                exact cvx163
              · by_cases h16 : N ≤ 164
                · obtain rfl : N = 164 := by omega
                  exact cvx164
                · obtain rfl : N = 165 := by omega
                  exact cvx165
            · by_cases h14 : N ≤ 166
              · obtain rfl : N = 166 := by omega
                exact cvx166
              · by_cases h16 : N ≤ 167
                · obtain rfl : N = 167 := by omega
                  exact cvx167
                · obtain rfl : N = 168 := by omega
                  exact cvx168
          · by_cases h12 : N ≤ 171
            · by_cases h14 : N ≤ 169
              · obtain rfl : N = 169 := by omega
                exact cvx169
              · by_cases h16 : N ≤ 170
                · obtain rfl : N = 170 := by omega
                  exact cvx170
                · obtain rfl : N = 171 := by omega
                  exact cvx171
            · by_cases h14 : N ≤ 173
              · by_cases h16 : N ≤ 172
                · obtain rfl : N = 172 := by omega
                  exact cvx172
                · obtain rfl : N = 173 := by omega
                  exact cvx173
              · by_cases h16 : N ≤ 174
                · obtain rfl : N = 174 := by omega
                  exact cvx174
                · obtain rfl : N = 175 := by omega
                  exact cvx175
      · by_cases h8 : N ≤ 187
        · by_cases h10 : N ≤ 181
          · by_cases h12 : N ≤ 178
            · by_cases h14 : N ≤ 176
              · obtain rfl : N = 176 := by omega
                exact cvx176
              · by_cases h16 : N ≤ 177
                · obtain rfl : N = 177 := by omega
                  exact cvx177
                · obtain rfl : N = 178 := by omega
                  exact cvx178
            · by_cases h14 : N ≤ 179
              · obtain rfl : N = 179 := by omega
                exact cvx179
              · by_cases h16 : N ≤ 180
                · obtain rfl : N = 180 := by omega
                  exact cvx180
                · obtain rfl : N = 181 := by omega
                  exact cvx181
          · by_cases h12 : N ≤ 184
            · by_cases h14 : N ≤ 182
              · obtain rfl : N = 182 := by omega
                exact cvx182
              · by_cases h16 : N ≤ 183
                · obtain rfl : N = 183 := by omega
                  exact cvx183
                · obtain rfl : N = 184 := by omega
                  exact cvx184
            · by_cases h14 : N ≤ 185
              · obtain rfl : N = 185 := by omega
                exact cvx185
              · by_cases h16 : N ≤ 186
                · obtain rfl : N = 186 := by omega
                  exact cvx186
                · obtain rfl : N = 187 := by omega
                  exact cvx187
        · by_cases h10 : N ≤ 193
          · by_cases h12 : N ≤ 190
            · by_cases h14 : N ≤ 188
              · obtain rfl : N = 188 := by omega
                exact cvx188
              · by_cases h16 : N ≤ 189
                · obtain rfl : N = 189 := by omega
                  exact cvx189
                · obtain rfl : N = 190 := by omega
                  exact cvx190
            · by_cases h14 : N ≤ 191
              · obtain rfl : N = 191 := by omega
                exact cvx191
              · by_cases h16 : N ≤ 192
                · obtain rfl : N = 192 := by omega
                  exact cvx192
                · obtain rfl : N = 193 := by omega
                  exact cvx193
          · by_cases h12 : N ≤ 196
            · by_cases h14 : N ≤ 194
              · obtain rfl : N = 194 := by omega
                exact cvx194
              · by_cases h16 : N ≤ 195
                · obtain rfl : N = 195 := by omega
                  exact cvx195
                · obtain rfl : N = 196 := by omega
                  exact cvx196
            · by_cases h14 : N ≤ 198
              · by_cases h16 : N ≤ 197
                · obtain rfl : N = 197 := by omega
                  exact cvx197
                · obtain rfl : N = 198 := by omega
                  exact cvx198
              · by_cases h16 : N ≤ 199
                · obtain rfl : N = 199 := by omega
                  exact cvx199
                · obtain rfl : N = 200 := by omega
                  exact cvx200
  · by_cases h4 : N ≤ 250
    · by_cases h6 : N ≤ 225
      · by_cases h8 : N ≤ 212
        · by_cases h10 : N ≤ 206
          · by_cases h12 : N ≤ 203
            · by_cases h14 : N ≤ 201
              · obtain rfl : N = 201 := by omega
                exact cvx201
              · by_cases h16 : N ≤ 202
                · obtain rfl : N = 202 := by omega
                  exact cvx202
                · obtain rfl : N = 203 := by omega
                  exact cvx203
            · by_cases h14 : N ≤ 204
              · obtain rfl : N = 204 := by omega
                exact cvx204
              · by_cases h16 : N ≤ 205
                · obtain rfl : N = 205 := by omega
                  exact cvx205
                · obtain rfl : N = 206 := by omega
                  exact cvx206
          · by_cases h12 : N ≤ 209
            · by_cases h14 : N ≤ 207
              · obtain rfl : N = 207 := by omega
                exact cvx207
              · by_cases h16 : N ≤ 208
                · obtain rfl : N = 208 := by omega
                  exact cvx208
                · obtain rfl : N = 209 := by omega
                  exact cvx209
            · by_cases h14 : N ≤ 210
              · obtain rfl : N = 210 := by omega
                exact cvx210
              · by_cases h16 : N ≤ 211
                · obtain rfl : N = 211 := by omega
                  exact cvx211
                · obtain rfl : N = 212 := by omega
                  exact cvx212
        · by_cases h10 : N ≤ 218
          · by_cases h12 : N ≤ 215
            · by_cases h14 : N ≤ 213
              · obtain rfl : N = 213 := by omega
                exact cvx213
              · by_cases h16 : N ≤ 214
                · obtain rfl : N = 214 := by omega
                  exact cvx214
                · obtain rfl : N = 215 := by omega
                  exact cvx215
            · by_cases h14 : N ≤ 216
              · obtain rfl : N = 216 := by omega
                exact cvx216
              · by_cases h16 : N ≤ 217
                · obtain rfl : N = 217 := by omega
                  exact cvx217
                · obtain rfl : N = 218 := by omega
                  exact cvx218
          · by_cases h12 : N ≤ 221
            · by_cases h14 : N ≤ 219
              · obtain rfl : N = 219 := by omega
                exact cvx219
              · by_cases h16 : N ≤ 220
                · obtain rfl : N = 220 := by omega
                  exact cvx220
                · obtain rfl : N = 221 := by omega
                  exact cvx221
            · by_cases h14 : N ≤ 223
              · by_cases h16 : N ≤ 222
                · obtain rfl : N = 222 := by omega
                  exact cvx222
                · obtain rfl : N = 223 := by omega
                  exact cvx223
              · by_cases h16 : N ≤ 224
                · obtain rfl : N = 224 := by omega
                  exact cvx224
                · obtain rfl : N = 225 := by omega
                  exact cvx225
      · by_cases h8 : N ≤ 237
        · by_cases h10 : N ≤ 231
          · by_cases h12 : N ≤ 228
            · by_cases h14 : N ≤ 226
              · obtain rfl : N = 226 := by omega
                exact cvx226
              · by_cases h16 : N ≤ 227
                · obtain rfl : N = 227 := by omega
                  exact cvx227
                · obtain rfl : N = 228 := by omega
                  exact cvx228
            · by_cases h14 : N ≤ 229
              · obtain rfl : N = 229 := by omega
                exact cvx229
              · by_cases h16 : N ≤ 230
                · obtain rfl : N = 230 := by omega
                  exact cvx230
                · obtain rfl : N = 231 := by omega
                  exact cvx231
          · by_cases h12 : N ≤ 234
            · by_cases h14 : N ≤ 232
              · obtain rfl : N = 232 := by omega
                exact cvx232
              · by_cases h16 : N ≤ 233
                · obtain rfl : N = 233 := by omega
                  exact cvx233
                · obtain rfl : N = 234 := by omega
                  exact cvx234
            · by_cases h14 : N ≤ 235
              · obtain rfl : N = 235 := by omega
                exact cvx235
              · by_cases h16 : N ≤ 236
                · obtain rfl : N = 236 := by omega
                  exact cvx236
                · obtain rfl : N = 237 := by omega
                  exact cvx237
        · by_cases h10 : N ≤ 243
          · by_cases h12 : N ≤ 240
            · by_cases h14 : N ≤ 238
              · obtain rfl : N = 238 := by omega
                exact cvx238
              · by_cases h16 : N ≤ 239
                · obtain rfl : N = 239 := by omega
                  exact cvx239
                · obtain rfl : N = 240 := by omega
                  exact cvx240
            · by_cases h14 : N ≤ 241
              · obtain rfl : N = 241 := by omega
                exact cvx241
              · by_cases h16 : N ≤ 242
                · obtain rfl : N = 242 := by omega
                  exact cvx242
                · obtain rfl : N = 243 := by omega
                  exact cvx243
          · by_cases h12 : N ≤ 246
            · by_cases h14 : N ≤ 244
              · obtain rfl : N = 244 := by omega
                exact cvx244
              · by_cases h16 : N ≤ 245
                · obtain rfl : N = 245 := by omega
                  exact cvx245
                · obtain rfl : N = 246 := by omega
                  exact cvx246
            · by_cases h14 : N ≤ 248
              · by_cases h16 : N ≤ 247
                · obtain rfl : N = 247 := by omega
                  exact cvx247
                · obtain rfl : N = 248 := by omega
                  exact cvx248
              · by_cases h16 : N ≤ 249
                · obtain rfl : N = 249 := by omega
                  exact cvx249
                · obtain rfl : N = 250 := by omega
                  exact cvx250
    · by_cases h6 : N ≤ 275
      · by_cases h8 : N ≤ 262
        · by_cases h10 : N ≤ 256
          · by_cases h12 : N ≤ 253
            · by_cases h14 : N ≤ 251
              · obtain rfl : N = 251 := by omega
                exact cvx251
              · by_cases h16 : N ≤ 252
                · obtain rfl : N = 252 := by omega
                  exact cvx252
                · obtain rfl : N = 253 := by omega
                  exact cvx253
            · by_cases h14 : N ≤ 254
              · obtain rfl : N = 254 := by omega
                exact cvx254
              · by_cases h16 : N ≤ 255
                · obtain rfl : N = 255 := by omega
                  exact cvx255
                · obtain rfl : N = 256 := by omega
                  exact cvx256
          · by_cases h12 : N ≤ 259
            · by_cases h14 : N ≤ 257
              · obtain rfl : N = 257 := by omega
                exact cvx257
              · by_cases h16 : N ≤ 258
                · obtain rfl : N = 258 := by omega
                  exact cvx258
                · obtain rfl : N = 259 := by omega
                  exact cvx259
            · by_cases h14 : N ≤ 260
              · obtain rfl : N = 260 := by omega
                exact cvx260
              · by_cases h16 : N ≤ 261
                · obtain rfl : N = 261 := by omega
                  exact cvx261
                · obtain rfl : N = 262 := by omega
                  exact cvx262
        · by_cases h10 : N ≤ 268
          · by_cases h12 : N ≤ 265
            · by_cases h14 : N ≤ 263
              · obtain rfl : N = 263 := by omega
                exact cvx263
              · by_cases h16 : N ≤ 264
                · obtain rfl : N = 264 := by omega
                  exact cvx264
                · obtain rfl : N = 265 := by omega
                  exact cvx265
            · by_cases h14 : N ≤ 266
              · obtain rfl : N = 266 := by omega
                exact cvx266
              · by_cases h16 : N ≤ 267
                · obtain rfl : N = 267 := by omega
                  exact cvx267
                · obtain rfl : N = 268 := by omega
                  exact cvx268
          · by_cases h12 : N ≤ 271
            · by_cases h14 : N ≤ 269
              · obtain rfl : N = 269 := by omega
                exact cvx269
              · by_cases h16 : N ≤ 270
                · obtain rfl : N = 270 := by omega
                  exact cvx270
                · obtain rfl : N = 271 := by omega
                  exact cvx271
            · by_cases h14 : N ≤ 273
              · by_cases h16 : N ≤ 272
                · obtain rfl : N = 272 := by omega
                  exact cvx272
                · obtain rfl : N = 273 := by omega
                  exact cvx273
              · by_cases h16 : N ≤ 274
                · obtain rfl : N = 274 := by omega
                  exact cvx274
                · obtain rfl : N = 275 := by omega
                  exact cvx275
      · by_cases h8 : N ≤ 287
        · by_cases h10 : N ≤ 281
          · by_cases h12 : N ≤ 278
            · by_cases h14 : N ≤ 276
              · obtain rfl : N = 276 := by omega
                exact cvx276
              · by_cases h16 : N ≤ 277
                · obtain rfl : N = 277 := by omega
                  exact cvx277
                · obtain rfl : N = 278 := by omega
                  exact cvx278
            · by_cases h14 : N ≤ 279
              · obtain rfl : N = 279 := by omega
                exact cvx279
              · by_cases h16 : N ≤ 280
                · obtain rfl : N = 280 := by omega
                  exact cvx280
                · obtain rfl : N = 281 := by omega
                  exact cvx281
          · by_cases h12 : N ≤ 284
            · by_cases h14 : N ≤ 282
              · obtain rfl : N = 282 := by omega
                exact cvx282
              · by_cases h16 : N ≤ 283
                · obtain rfl : N = 283 := by omega
                  exact cvx283
                · obtain rfl : N = 284 := by omega
                  exact cvx284
            · by_cases h14 : N ≤ 285
              · obtain rfl : N = 285 := by omega
                exact cvx285
              · by_cases h16 : N ≤ 286
                · obtain rfl : N = 286 := by omega
                  exact cvx286
                · obtain rfl : N = 287 := by omega
                  exact cvx287
        · by_cases h10 : N ≤ 293
          · by_cases h12 : N ≤ 290
            · by_cases h14 : N ≤ 288
              · obtain rfl : N = 288 := by omega
                exact cvx288
              · by_cases h16 : N ≤ 289
                · obtain rfl : N = 289 := by omega
                  exact cvx289
                · obtain rfl : N = 290 := by omega
                  exact cvx290
            · by_cases h14 : N ≤ 291
              · obtain rfl : N = 291 := by omega
                exact cvx291
              · by_cases h16 : N ≤ 292
                · obtain rfl : N = 292 := by omega
                  exact cvx292
                · obtain rfl : N = 293 := by omega
                  exact cvx293
          · by_cases h12 : N ≤ 296
            · by_cases h14 : N ≤ 294
              · obtain rfl : N = 294 := by omega
                exact cvx294
              · by_cases h16 : N ≤ 295
                · obtain rfl : N = 295 := by omega
                  exact cvx295
                · obtain rfl : N = 296 := by omega
                  exact cvx296
            · by_cases h14 : N ≤ 298
              · by_cases h16 : N ≤ 297
                · obtain rfl : N = 297 := by omega
                  exact cvx297
                · obtain rfl : N = 298 := by omega
                  exact cvx298
              · by_cases h16 : N ≤ 299
                · obtain rfl : N = 299 := by omega
                  exact cvx299
                · obtain rfl : N = 300 := by omega
                  exact cvx300

theorem cen_101_300 {N : ℕ} (h1 : 101 ≤ N) (h2 : N ≤ 300) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 200
  · by_cases h4 : N ≤ 150
    · by_cases h6 : N ≤ 124
      · by_cases h8 : N ≤ 112
        · by_cases h10 : N ≤ 106
          · by_cases h12 : N ≤ 102
            · obtain rfl : N = 102 := by omega
              exact cen102
            · by_cases h14 : N ≤ 104
              · obtain rfl : N = 104 := by omega
                exact cen104
              · obtain rfl : N = 106 := by omega
                exact cen106
          · by_cases h12 : N ≤ 108
            · obtain rfl : N = 108 := by omega
              exact cen108
            · by_cases h14 : N ≤ 110
              · obtain rfl : N = 110 := by omega
                exact cen110
              · obtain rfl : N = 112 := by omega
                exact cen112
        · by_cases h10 : N ≤ 118
          · by_cases h12 : N ≤ 114
            · obtain rfl : N = 114 := by omega
              exact cen114
            · by_cases h14 : N ≤ 116
              · obtain rfl : N = 116 := by omega
                exact cen116
              · obtain rfl : N = 118 := by omega
                exact cen118
          · by_cases h12 : N ≤ 120
            · obtain rfl : N = 120 := by omega
              exact cen120
            · by_cases h14 : N ≤ 122
              · obtain rfl : N = 122 := by omega
                exact cen122
              · obtain rfl : N = 124 := by omega
                exact cen124
      · by_cases h8 : N ≤ 136
        · by_cases h10 : N ≤ 130
          · by_cases h12 : N ≤ 126
            · obtain rfl : N = 126 := by omega
              exact cen126
            · by_cases h14 : N ≤ 128
              · obtain rfl : N = 128 := by omega
                exact cen128
              · obtain rfl : N = 130 := by omega
                exact cen130
          · by_cases h12 : N ≤ 132
            · obtain rfl : N = 132 := by omega
              exact cen132
            · by_cases h14 : N ≤ 134
              · obtain rfl : N = 134 := by omega
                exact cen134
              · obtain rfl : N = 136 := by omega
                exact cen136
        · by_cases h10 : N ≤ 142
          · by_cases h12 : N ≤ 138
            · obtain rfl : N = 138 := by omega
              exact cen138
            · by_cases h14 : N ≤ 140
              · obtain rfl : N = 140 := by omega
                exact cen140
              · obtain rfl : N = 142 := by omega
                exact cen142
          · by_cases h12 : N ≤ 146
            · by_cases h14 : N ≤ 144
              · obtain rfl : N = 144 := by omega
                exact cen144
              · obtain rfl : N = 146 := by omega
                exact cen146
            · by_cases h14 : N ≤ 148
              · obtain rfl : N = 148 := by omega
                exact cen148
              · obtain rfl : N = 150 := by omega
                exact cen150
    · by_cases h6 : N ≤ 174
      · by_cases h8 : N ≤ 162
        · by_cases h10 : N ≤ 156
          · by_cases h12 : N ≤ 152
            · obtain rfl : N = 152 := by omega
              exact cen152
            · by_cases h14 : N ≤ 154
              · obtain rfl : N = 154 := by omega
                exact cen154
              · obtain rfl : N = 156 := by omega
                exact cen156
          · by_cases h12 : N ≤ 158
            · obtain rfl : N = 158 := by omega
              exact cen158
            · by_cases h14 : N ≤ 160
              · obtain rfl : N = 160 := by omega
                exact cen160
              · obtain rfl : N = 162 := by omega
                exact cen162
        · by_cases h10 : N ≤ 168
          · by_cases h12 : N ≤ 164
            · obtain rfl : N = 164 := by omega
              exact cen164
            · by_cases h14 : N ≤ 166
              · obtain rfl : N = 166 := by omega
                exact cen166
              · obtain rfl : N = 168 := by omega
                exact cen168
          · by_cases h12 : N ≤ 170
            · obtain rfl : N = 170 := by omega
              exact cen170
            · by_cases h14 : N ≤ 172
              · obtain rfl : N = 172 := by omega
                exact cen172
              · obtain rfl : N = 174 := by omega
                exact cen174
      · by_cases h8 : N ≤ 186
        · by_cases h10 : N ≤ 180
          · by_cases h12 : N ≤ 176
            · obtain rfl : N = 176 := by omega
              exact cen176
            · by_cases h14 : N ≤ 178
              · obtain rfl : N = 178 := by omega
                exact cen178
              · obtain rfl : N = 180 := by omega
                exact cen180
          · by_cases h12 : N ≤ 182
            · obtain rfl : N = 182 := by omega
              exact cen182
            · by_cases h14 : N ≤ 184
              · obtain rfl : N = 184 := by omega
                exact cen184
              · obtain rfl : N = 186 := by omega
                exact cen186
        · by_cases h10 : N ≤ 192
          · by_cases h12 : N ≤ 188
            · obtain rfl : N = 188 := by omega
              exact cen188
            · by_cases h14 : N ≤ 190
              · obtain rfl : N = 190 := by omega
                exact cen190
              · obtain rfl : N = 192 := by omega
                exact cen192
          · by_cases h12 : N ≤ 196
            · by_cases h14 : N ≤ 194
              · obtain rfl : N = 194 := by omega
                exact cen194
              · obtain rfl : N = 196 := by omega
                exact cen196
            · by_cases h14 : N ≤ 198
              · obtain rfl : N = 198 := by omega
                exact cen198
              · obtain rfl : N = 200 := by omega
                exact cen200
  · by_cases h4 : N ≤ 250
    · by_cases h6 : N ≤ 224
      · by_cases h8 : N ≤ 212
        · by_cases h10 : N ≤ 206
          · by_cases h12 : N ≤ 202
            · obtain rfl : N = 202 := by omega
              exact cen202
            · by_cases h14 : N ≤ 204
              · obtain rfl : N = 204 := by omega
                exact cen204
              · obtain rfl : N = 206 := by omega
                exact cen206
          · by_cases h12 : N ≤ 208
            · obtain rfl : N = 208 := by omega
              exact cen208
            · by_cases h14 : N ≤ 210
              · obtain rfl : N = 210 := by omega
                exact cen210
              · obtain rfl : N = 212 := by omega
                exact cen212
        · by_cases h10 : N ≤ 218
          · by_cases h12 : N ≤ 214
            · obtain rfl : N = 214 := by omega
              exact cen214
            · by_cases h14 : N ≤ 216
              · obtain rfl : N = 216 := by omega
                exact cen216
              · obtain rfl : N = 218 := by omega
                exact cen218
          · by_cases h12 : N ≤ 220
            · obtain rfl : N = 220 := by omega
              exact cen220
            · by_cases h14 : N ≤ 222
              · obtain rfl : N = 222 := by omega
                exact cen222
              · obtain rfl : N = 224 := by omega
                exact cen224
      · by_cases h8 : N ≤ 236
        · by_cases h10 : N ≤ 230
          · by_cases h12 : N ≤ 226
            · obtain rfl : N = 226 := by omega
              exact cen226
            · by_cases h14 : N ≤ 228
              · obtain rfl : N = 228 := by omega
                exact cen228
              · obtain rfl : N = 230 := by omega
                exact cen230
          · by_cases h12 : N ≤ 232
            · obtain rfl : N = 232 := by omega
              exact cen232
            · by_cases h14 : N ≤ 234
              · obtain rfl : N = 234 := by omega
                exact cen234
              · obtain rfl : N = 236 := by omega
                exact cen236
        · by_cases h10 : N ≤ 242
          · by_cases h12 : N ≤ 238
            · obtain rfl : N = 238 := by omega
              exact cen238
            · by_cases h14 : N ≤ 240
              · obtain rfl : N = 240 := by omega
                exact cen240
              · obtain rfl : N = 242 := by omega
                exact cen242
          · by_cases h12 : N ≤ 246
            · by_cases h14 : N ≤ 244
              · obtain rfl : N = 244 := by omega
                exact cen244
              · obtain rfl : N = 246 := by omega
                exact cen246
            · by_cases h14 : N ≤ 248
              · obtain rfl : N = 248 := by omega
                exact cen248
              · obtain rfl : N = 250 := by omega
                exact cen250
    · by_cases h6 : N ≤ 274
      · by_cases h8 : N ≤ 262
        · by_cases h10 : N ≤ 256
          · by_cases h12 : N ≤ 252
            · obtain rfl : N = 252 := by omega
              exact cen252
            · by_cases h14 : N ≤ 254
              · obtain rfl : N = 254 := by omega
                exact cen254
              · obtain rfl : N = 256 := by omega
                exact cen256
          · by_cases h12 : N ≤ 258
            · obtain rfl : N = 258 := by omega
              exact cen258
            · by_cases h14 : N ≤ 260
              · obtain rfl : N = 260 := by omega
                exact cen260
              · obtain rfl : N = 262 := by omega
                exact cen262
        · by_cases h10 : N ≤ 268
          · by_cases h12 : N ≤ 264
            · obtain rfl : N = 264 := by omega
              exact cen264
            · by_cases h14 : N ≤ 266
              · obtain rfl : N = 266 := by omega
                exact cen266
              · obtain rfl : N = 268 := by omega
                exact cen268
          · by_cases h12 : N ≤ 270
            · obtain rfl : N = 270 := by omega
              exact cen270
            · by_cases h14 : N ≤ 272
              · obtain rfl : N = 272 := by omega
                exact cen272
              · obtain rfl : N = 274 := by omega
                exact cen274
      · by_cases h8 : N ≤ 286
        · by_cases h10 : N ≤ 280
          · by_cases h12 : N ≤ 276
            · obtain rfl : N = 276 := by omega
              exact cen276
            · by_cases h14 : N ≤ 278
              · obtain rfl : N = 278 := by omega
                exact cen278
              · obtain rfl : N = 280 := by omega
                exact cen280
          · by_cases h12 : N ≤ 282
            · obtain rfl : N = 282 := by omega
              exact cen282
            · by_cases h14 : N ≤ 284
              · obtain rfl : N = 284 := by omega
                exact cen284
              · obtain rfl : N = 286 := by omega
                exact cen286
        · by_cases h10 : N ≤ 292
          · by_cases h12 : N ≤ 288
            · obtain rfl : N = 288 := by omega
              exact cen288
            · by_cases h14 : N ≤ 290
              · obtain rfl : N = 290 := by omega
                exact cen290
              · obtain rfl : N = 292 := by omega
                exact cen292
          · by_cases h12 : N ≤ 296
            · by_cases h14 : N ≤ 294
              · obtain rfl : N = 294 := by omega
                exact cen294
              · obtain rfl : N = 296 := by omega
                exact cen296
            · by_cases h14 : N ≤ 298
              · obtain rfl : N = 298 := by omega
                exact cen298
              · obtain rfl : N = 300 := by omega
                exact cen300

end Kagey131.PaperD.T7
