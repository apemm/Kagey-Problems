import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 868, …, 920` (generated)

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

/-! ### `N = 868` -/

def pL868 : Prm := ⟨75, 35, 37, 870, 11, 18446744073709551616, 193121905844293909, 193121905844293909⟩
def pH868 : Prm := ⟨75, 35, 37, 870, 11, 18446744073709551616, 193124104867549461, 193124104867549461⟩
def pI868 : Prm := ⟨63, 31, 29, 870, 11, 18446744073709551616, 193121905844293909, 193124104867549461⟩
theorem L868_fin : (prmOK pL868 868 && ptTest pL868 (runFrom pL868 (fmask pL868) (cmask pL868) (hmask pL868) 1 867 (true, (init pL868), (init pL868))) 868 434 false) = true := by
  decide +kernel
theorem L868_ok : RunOK pL868 868 (runFrom pL868 (fmask pL868) (cmask pL868) (hmask pL868) 1 867 (true, (init pL868), (init pL868))) ∧ ptTest pL868 (runFrom pL868 (fmask pL868) (cmask pL868) (hmask pL868) 1 867 (true, (init pL868), (init pL868))) 868 434 false = true :=
  fin_run (runOK_init (prmOK_of_and L868_fin) true) (by decide) rfl L868_fin ptTest_fst
theorem H868_fin : (prmOK pH868 868 && ptTest pH868 (runFrom pH868 (fmask pH868) (cmask pH868) (hmask pH868) 1 867 (true, (init pH868), (init pH868))) 868 434 true) = true := by
  decide +kernel
theorem H868_ok : RunOK pH868 868 (runFrom pH868 (fmask pH868) (cmask pH868) (hmask pH868) 1 867 (true, (init pH868), (init pH868))) ∧ ptTest pH868 (runFrom pH868 (fmask pH868) (cmask pH868) (hmask pH868) 1 867 (true, (init pH868), (init pH868))) 868 434 true = true :=
  fin_run (runOK_init (prmOK_of_and H868_fin) true) (by decide) rfl H868_fin ptTest_fst
theorem I868_fin : (prmOK pI868 868 && intTest pI868 (runFrom pI868 (fmask pI868) (cmask pI868) (hmask pI868) 1 867 (true, (init pI868), (init pI868))) 868 17 true) = true := by
  decide +kernel
theorem I868_ok : RunOK pI868 868 (runFrom pI868 (fmask pI868) (cmask pI868) (hmask pI868) 1 867 (true, (init pI868), (init pI868))) ∧ intTest pI868 (runFrom pI868 (fmask pI868) (cmask pI868) (hmask pI868) 1 867 (true, (init pI868), (init pI868))) 868 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I868_fin) true) (by decide) rfl I868_fin intTest_fst
theorem link868 : linkOK pL868 pH868 pI868 = true := by decide +kernel
theorem cvx868 : ConvexBetweenHumps 868 :=
  cvx_of L868_ok H868_ok I868_ok link868 (by decide)
theorem cenlink868 : cenLinkOK pI868 868 = true := by decide +kernel
theorem cen868 : CenterUniqueMin 868 ∧ DipHyp 868 ∧ OnePointHyps 868 :=
  cen_of L868_ok H868_ok I868_ok link868 cenlink868

/-! ### `N = 869` -/

def pL869 : Prm := ⟨75, 35, 37, 871, 11, 18446744073709551616, 192945669744266583, 192945669744266583⟩
def pH869 : Prm := ⟨75, 35, 37, 871, 11, 18446744073709551616, 192947868767522135, 192947868767522135⟩
def pI869 : Prm := ⟨63, 31, 29, 871, 11, 18446744073709551616, 192945669744266583, 192947868767522135⟩
theorem L869_fin : (prmOK pL869 869 && ptTest pL869 (runFrom pL869 (fmask pL869) (cmask pL869) (hmask pL869) 1 868 (true, (init pL869), (init pL869))) 869 435 false) = true := by
  decide +kernel
theorem L869_ok : RunOK pL869 869 (runFrom pL869 (fmask pL869) (cmask pL869) (hmask pL869) 1 868 (true, (init pL869), (init pL869))) ∧ ptTest pL869 (runFrom pL869 (fmask pL869) (cmask pL869) (hmask pL869) 1 868 (true, (init pL869), (init pL869))) 869 435 false = true :=
  fin_run (runOK_init (prmOK_of_and L869_fin) true) (by decide) rfl L869_fin ptTest_fst
theorem H869_fin : (prmOK pH869 869 && ptTest pH869 (runFrom pH869 (fmask pH869) (cmask pH869) (hmask pH869) 1 868 (true, (init pH869), (init pH869))) 869 435 true) = true := by
  decide +kernel
theorem H869_ok : RunOK pH869 869 (runFrom pH869 (fmask pH869) (cmask pH869) (hmask pH869) 1 868 (true, (init pH869), (init pH869))) ∧ ptTest pH869 (runFrom pH869 (fmask pH869) (cmask pH869) (hmask pH869) 1 868 (true, (init pH869), (init pH869))) 869 435 true = true :=
  fin_run (runOK_init (prmOK_of_and H869_fin) true) (by decide) rfl H869_fin ptTest_fst
theorem I869_fin : (prmOK pI869 869 && intTest pI869 (runFrom pI869 (fmask pI869) (cmask pI869) (hmask pI869) 1 868 (true, (init pI869), (init pI869))) 869 17 false) = true := by
  decide +kernel
theorem I869_ok : RunOK pI869 869 (runFrom pI869 (fmask pI869) (cmask pI869) (hmask pI869) 1 868 (true, (init pI869), (init pI869))) ∧ intTest pI869 (runFrom pI869 (fmask pI869) (cmask pI869) (hmask pI869) 1 868 (true, (init pI869), (init pI869))) 869 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I869_fin) true) (by decide) rfl I869_fin intTest_fst
theorem link869 : linkOK pL869 pH869 pI869 = true := by decide +kernel
theorem cvx869 : ConvexBetweenHumps 869 :=
  cvx_of L869_ok H869_ok I869_ok link869 (by decide)

/-! ### `N = 870` -/

def pL870 : Prm := ⟨75, 35, 37, 872, 11, 18446744073709551616, 192769963209438968, 192769963209438968⟩
def pH870 : Prm := ⟨75, 35, 37, 872, 11, 18446744073709551616, 192772162232694520, 192772162232694520⟩
def pI870 : Prm := ⟨63, 31, 29, 872, 11, 18446744073709551616, 192769963209438968, 192772162232694520⟩
theorem L870_fin : (prmOK pL870 870 && ptTest pL870 (runFrom pL870 (fmask pL870) (cmask pL870) (hmask pL870) 1 869 (true, (init pL870), (init pL870))) 870 435 false) = true := by
  decide +kernel
theorem L870_ok : RunOK pL870 870 (runFrom pL870 (fmask pL870) (cmask pL870) (hmask pL870) 1 869 (true, (init pL870), (init pL870))) ∧ ptTest pL870 (runFrom pL870 (fmask pL870) (cmask pL870) (hmask pL870) 1 869 (true, (init pL870), (init pL870))) 870 435 false = true :=
  fin_run (runOK_init (prmOK_of_and L870_fin) true) (by decide) rfl L870_fin ptTest_fst
theorem H870_fin : (prmOK pH870 870 && ptTest pH870 (runFrom pH870 (fmask pH870) (cmask pH870) (hmask pH870) 1 869 (true, (init pH870), (init pH870))) 870 435 true) = true := by
  decide +kernel
theorem H870_ok : RunOK pH870 870 (runFrom pH870 (fmask pH870) (cmask pH870) (hmask pH870) 1 869 (true, (init pH870), (init pH870))) ∧ ptTest pH870 (runFrom pH870 (fmask pH870) (cmask pH870) (hmask pH870) 1 869 (true, (init pH870), (init pH870))) 870 435 true = true :=
  fin_run (runOK_init (prmOK_of_and H870_fin) true) (by decide) rfl H870_fin ptTest_fst
theorem I870_fin : (prmOK pI870 870 && intTest pI870 (runFrom pI870 (fmask pI870) (cmask pI870) (hmask pI870) 1 869 (true, (init pI870), (init pI870))) 870 17 true) = true := by
  decide +kernel
theorem I870_ok : RunOK pI870 870 (runFrom pI870 (fmask pI870) (cmask pI870) (hmask pI870) 1 869 (true, (init pI870), (init pI870))) ∧ intTest pI870 (runFrom pI870 (fmask pI870) (cmask pI870) (hmask pI870) 1 869 (true, (init pI870), (init pI870))) 870 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I870_fin) true) (by decide) rfl I870_fin intTest_fst
theorem link870 : linkOK pL870 pH870 pI870 = true := by decide +kernel
theorem cvx870 : ConvexBetweenHumps 870 :=
  cvx_of L870_ok H870_ok I870_ok link870 (by decide)
theorem cenlink870 : cenLinkOK pI870 870 = true := by decide +kernel
theorem cen870 : CenterUniqueMin 870 ∧ DipHyp 870 ∧ OnePointHyps 870 :=
  cen_of L870_ok H870_ok I870_ok link870 cenlink870

/-! ### `N = 871` -/

def pL871 : Prm := ⟨75, 35, 37, 873, 11, 18446744073709551616, 192594430784980056, 192594430784980056⟩
def pH871 : Prm := ⟨75, 35, 37, 873, 11, 18446744073709551616, 192596629808235608, 192596629808235608⟩
def pI871 : Prm := ⟨63, 31, 29, 873, 11, 18446744073709551616, 192594430784980056, 192596629808235608⟩
theorem L871_fin : (prmOK pL871 871 && ptTest pL871 (runFrom pL871 (fmask pL871) (cmask pL871) (hmask pL871) 1 870 (true, (init pL871), (init pL871))) 871 436 false) = true := by
  decide +kernel
theorem L871_ok : RunOK pL871 871 (runFrom pL871 (fmask pL871) (cmask pL871) (hmask pL871) 1 870 (true, (init pL871), (init pL871))) ∧ ptTest pL871 (runFrom pL871 (fmask pL871) (cmask pL871) (hmask pL871) 1 870 (true, (init pL871), (init pL871))) 871 436 false = true :=
  fin_run (runOK_init (prmOK_of_and L871_fin) true) (by decide) rfl L871_fin ptTest_fst
theorem H871_fin : (prmOK pH871 871 && ptTest pH871 (runFrom pH871 (fmask pH871) (cmask pH871) (hmask pH871) 1 870 (true, (init pH871), (init pH871))) 871 436 true) = true := by
  decide +kernel
theorem H871_ok : RunOK pH871 871 (runFrom pH871 (fmask pH871) (cmask pH871) (hmask pH871) 1 870 (true, (init pH871), (init pH871))) ∧ ptTest pH871 (runFrom pH871 (fmask pH871) (cmask pH871) (hmask pH871) 1 870 (true, (init pH871), (init pH871))) 871 436 true = true :=
  fin_run (runOK_init (prmOK_of_and H871_fin) true) (by decide) rfl H871_fin ptTest_fst
theorem I871_fin : (prmOK pI871 871 && intTest pI871 (runFrom pI871 (fmask pI871) (cmask pI871) (hmask pI871) 1 870 (true, (init pI871), (init pI871))) 871 17 false) = true := by
  decide +kernel
theorem I871_ok : RunOK pI871 871 (runFrom pI871 (fmask pI871) (cmask pI871) (hmask pI871) 1 870 (true, (init pI871), (init pI871))) ∧ intTest pI871 (runFrom pI871 (fmask pI871) (cmask pI871) (hmask pI871) 1 870 (true, (init pI871), (init pI871))) 871 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I871_fin) true) (by decide) rfl I871_fin intTest_fst
theorem link871 : linkOK pL871 pH871 pI871 = true := by decide +kernel
theorem cvx871 : ConvexBetweenHumps 871 :=
  cvx_of L871_ok H871_ok I871_ok link871 (by decide)

/-! ### `N = 872` -/

def pL872 : Prm := ⟨75, 35, 37, 874, 11, 18446744073709551616, 192419424504347892, 192419424504347892⟩
def pH872 : Prm := ⟨75, 35, 37, 874, 11, 18446744073709551616, 192421623527603444, 192421623527603444⟩
def pI872 : Prm := ⟨63, 31, 29, 874, 11, 18446744073709551616, 192419424504347892, 192421623527603444⟩
theorem L872_fin : (prmOK pL872 872 && ptTest pL872 (runFrom pL872 (fmask pL872) (cmask pL872) (hmask pL872) 1 871 (true, (init pL872), (init pL872))) 872 436 false) = true := by
  decide +kernel
theorem L872_ok : RunOK pL872 872 (runFrom pL872 (fmask pL872) (cmask pL872) (hmask pL872) 1 871 (true, (init pL872), (init pL872))) ∧ ptTest pL872 (runFrom pL872 (fmask pL872) (cmask pL872) (hmask pL872) 1 871 (true, (init pL872), (init pL872))) 872 436 false = true :=
  fin_run (runOK_init (prmOK_of_and L872_fin) true) (by decide) rfl L872_fin ptTest_fst
theorem H872_fin : (prmOK pH872 872 && ptTest pH872 (runFrom pH872 (fmask pH872) (cmask pH872) (hmask pH872) 1 871 (true, (init pH872), (init pH872))) 872 436 true) = true := by
  decide +kernel
theorem H872_ok : RunOK pH872 872 (runFrom pH872 (fmask pH872) (cmask pH872) (hmask pH872) 1 871 (true, (init pH872), (init pH872))) ∧ ptTest pH872 (runFrom pH872 (fmask pH872) (cmask pH872) (hmask pH872) 1 871 (true, (init pH872), (init pH872))) 872 436 true = true :=
  fin_run (runOK_init (prmOK_of_and H872_fin) true) (by decide) rfl H872_fin ptTest_fst
theorem I872_fin : (prmOK pI872 872 && intTest pI872 (runFrom pI872 (fmask pI872) (cmask pI872) (hmask pI872) 1 871 (true, (init pI872), (init pI872))) 872 17 true) = true := by
  decide +kernel
theorem I872_ok : RunOK pI872 872 (runFrom pI872 (fmask pI872) (cmask pI872) (hmask pI872) 1 871 (true, (init pI872), (init pI872))) ∧ intTest pI872 (runFrom pI872 (fmask pI872) (cmask pI872) (hmask pI872) 1 871 (true, (init pI872), (init pI872))) 872 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I872_fin) true) (by decide) rfl I872_fin intTest_fst
theorem link872 : linkOK pL872 pH872 pI872 = true := by decide +kernel
theorem cvx872 : ConvexBetweenHumps 872 :=
  cvx_of L872_ok H872_ok I872_ok link872 (by decide)
theorem cenlink872 : cenLinkOK pI872 872 = true := by decide +kernel
theorem cen872 : CenterUniqueMin 872 ∧ DipHyp 872 ∧ OnePointHyps 872 :=
  cen_of L872_ok H872_ok I872_ok link872 cenlink872

/-! ### `N = 873` -/

def pL873 : Prm := ⟨75, 35, 37, 875, 11, 18446744073709551616, 192244591400181119, 192244591400181119⟩
def pH873 : Prm := ⟨75, 35, 37, 875, 11, 18446744073709551616, 192246790423436671, 192246790423436671⟩
def pI873 : Prm := ⟨63, 31, 29, 875, 11, 18446744073709551616, 192244591400181119, 192246790423436671⟩
theorem L873_fin : (prmOK pL873 873 && ptTest pL873 (runFrom pL873 (fmask pL873) (cmask pL873) (hmask pL873) 1 872 (true, (init pL873), (init pL873))) 873 437 false) = true := by
  decide +kernel
theorem L873_ok : RunOK pL873 873 (runFrom pL873 (fmask pL873) (cmask pL873) (hmask pL873) 1 872 (true, (init pL873), (init pL873))) ∧ ptTest pL873 (runFrom pL873 (fmask pL873) (cmask pL873) (hmask pL873) 1 872 (true, (init pL873), (init pL873))) 873 437 false = true :=
  fin_run (runOK_init (prmOK_of_and L873_fin) true) (by decide) rfl L873_fin ptTest_fst
theorem H873_fin : (prmOK pH873 873 && ptTest pH873 (runFrom pH873 (fmask pH873) (cmask pH873) (hmask pH873) 1 872 (true, (init pH873), (init pH873))) 873 437 true) = true := by
  decide +kernel
theorem H873_ok : RunOK pH873 873 (runFrom pH873 (fmask pH873) (cmask pH873) (hmask pH873) 1 872 (true, (init pH873), (init pH873))) ∧ ptTest pH873 (runFrom pH873 (fmask pH873) (cmask pH873) (hmask pH873) 1 872 (true, (init pH873), (init pH873))) 873 437 true = true :=
  fin_run (runOK_init (prmOK_of_and H873_fin) true) (by decide) rfl H873_fin ptTest_fst
theorem I873_fin : (prmOK pI873 873 && intTest pI873 (runFrom pI873 (fmask pI873) (cmask pI873) (hmask pI873) 1 872 (true, (init pI873), (init pI873))) 873 17 false) = true := by
  decide +kernel
theorem I873_ok : RunOK pI873 873 (runFrom pI873 (fmask pI873) (cmask pI873) (hmask pI873) 1 872 (true, (init pI873), (init pI873))) ∧ intTest pI873 (runFrom pI873 (fmask pI873) (cmask pI873) (hmask pI873) 1 872 (true, (init pI873), (init pI873))) 873 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I873_fin) true) (by decide) rfl I873_fin intTest_fst
theorem link873 : linkOK pL873 pH873 pI873 = true := by decide +kernel
theorem cvx873 : ConvexBetweenHumps 873 :=
  cvx_of L873_ok H873_ok I873_ok link873 (by decide)

/-! ### `N = 874` -/

def pL874 : Prm := ⟨75, 35, 37, 876, 11, 18446744073709551616, 192070281048278069, 192070281048278069⟩
def pH874 : Prm := ⟨75, 35, 37, 876, 11, 18446744073709551616, 192072480071533621, 192072480071533621⟩
def pI874 : Prm := ⟨63, 31, 29, 876, 11, 18446744073709551616, 192070281048278069, 192072480071533621⟩
theorem L874_fin : (prmOK pL874 874 && ptTest pL874 (runFrom pL874 (fmask pL874) (cmask pL874) (hmask pL874) 1 873 (true, (init pL874), (init pL874))) 874 437 false) = true := by
  decide +kernel
theorem L874_ok : RunOK pL874 874 (runFrom pL874 (fmask pL874) (cmask pL874) (hmask pL874) 1 873 (true, (init pL874), (init pL874))) ∧ ptTest pL874 (runFrom pL874 (fmask pL874) (cmask pL874) (hmask pL874) 1 873 (true, (init pL874), (init pL874))) 874 437 false = true :=
  fin_run (runOK_init (prmOK_of_and L874_fin) true) (by decide) rfl L874_fin ptTest_fst
theorem H874_fin : (prmOK pH874 874 && ptTest pH874 (runFrom pH874 (fmask pH874) (cmask pH874) (hmask pH874) 1 873 (true, (init pH874), (init pH874))) 874 437 true) = true := by
  decide +kernel
theorem H874_ok : RunOK pH874 874 (runFrom pH874 (fmask pH874) (cmask pH874) (hmask pH874) 1 873 (true, (init pH874), (init pH874))) ∧ ptTest pH874 (runFrom pH874 (fmask pH874) (cmask pH874) (hmask pH874) 1 873 (true, (init pH874), (init pH874))) 874 437 true = true :=
  fin_run (runOK_init (prmOK_of_and H874_fin) true) (by decide) rfl H874_fin ptTest_fst
theorem I874_fin : (prmOK pI874 874 && intTest pI874 (runFrom pI874 (fmask pI874) (cmask pI874) (hmask pI874) 1 873 (true, (init pI874), (init pI874))) 874 17 true) = true := by
  decide +kernel
theorem I874_ok : RunOK pI874 874 (runFrom pI874 (fmask pI874) (cmask pI874) (hmask pI874) 1 873 (true, (init pI874), (init pI874))) ∧ intTest pI874 (runFrom pI874 (fmask pI874) (cmask pI874) (hmask pI874) 1 873 (true, (init pI874), (init pI874))) 874 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I874_fin) true) (by decide) rfl I874_fin intTest_fst
theorem link874 : linkOK pL874 pH874 pI874 = true := by decide +kernel
theorem cvx874 : ConvexBetweenHumps 874 :=
  cvx_of L874_ok H874_ok I874_ok link874 (by decide)
theorem cenlink874 : cenLinkOK pI874 874 = true := by decide +kernel
theorem cen874 : CenterUniqueMin 874 ∧ DipHyp 874 ∧ OnePointHyps 874 :=
  cen_of L874_ok H874_ok I874_ok link874 cenlink874

/-! ### `N = 875` -/

def pL875 : Prm := ⟨75, 35, 37, 877, 11, 18446744073709551616, 191896142945688605, 191896142945688605⟩
def pH875 : Prm := ⟨75, 35, 37, 877, 11, 18446744073709551616, 191898341968944157, 191898341968944157⟩
def pI875 : Prm := ⟨63, 31, 29, 877, 11, 18446744073709551616, 191896142945688605, 191898341968944157⟩
theorem L875_fin : (prmOK pL875 875 && ptTest pL875 (runFrom pL875 (fmask pL875) (cmask pL875) (hmask pL875) 1 874 (true, (init pL875), (init pL875))) 875 438 false) = true := by
  decide +kernel
theorem L875_ok : RunOK pL875 875 (runFrom pL875 (fmask pL875) (cmask pL875) (hmask pL875) 1 874 (true, (init pL875), (init pL875))) ∧ ptTest pL875 (runFrom pL875 (fmask pL875) (cmask pL875) (hmask pL875) 1 874 (true, (init pL875), (init pL875))) 875 438 false = true :=
  fin_run (runOK_init (prmOK_of_and L875_fin) true) (by decide) rfl L875_fin ptTest_fst
theorem H875_fin : (prmOK pH875 875 && ptTest pH875 (runFrom pH875 (fmask pH875) (cmask pH875) (hmask pH875) 1 874 (true, (init pH875), (init pH875))) 875 438 true) = true := by
  decide +kernel
theorem H875_ok : RunOK pH875 875 (runFrom pH875 (fmask pH875) (cmask pH875) (hmask pH875) 1 874 (true, (init pH875), (init pH875))) ∧ ptTest pH875 (runFrom pH875 (fmask pH875) (cmask pH875) (hmask pH875) 1 874 (true, (init pH875), (init pH875))) 875 438 true = true :=
  fin_run (runOK_init (prmOK_of_and H875_fin) true) (by decide) rfl H875_fin ptTest_fst
theorem I875_fin : (prmOK pI875 875 && intTest pI875 (runFrom pI875 (fmask pI875) (cmask pI875) (hmask pI875) 1 874 (true, (init pI875), (init pI875))) 875 17 false) = true := by
  decide +kernel
theorem I875_ok : RunOK pI875 875 (runFrom pI875 (fmask pI875) (cmask pI875) (hmask pI875) 1 874 (true, (init pI875), (init pI875))) ∧ intTest pI875 (runFrom pI875 (fmask pI875) (cmask pI875) (hmask pI875) 1 874 (true, (init pI875), (init pI875))) 875 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I875_fin) true) (by decide) rfl I875_fin intTest_fst
theorem link875 : linkOK pL875 pH875 pI875 = true := by decide +kernel
theorem cvx875 : ConvexBetweenHumps 875 :=
  cvx_of L875_ok H875_ok I875_ok link875 (by decide)

/-! ### `N = 876` -/

def pL876 : Prm := ⟨75, 35, 37, 878, 11, 18446744073709551616, 191722524233240843, 191722524233240843⟩
def pH876 : Prm := ⟨75, 35, 37, 878, 11, 18446744073709551616, 191724723256496395, 191724723256496395⟩
def pI876 : Prm := ⟨63, 31, 29, 878, 11, 18446744073709551616, 191722524233240843, 191724723256496395⟩
theorem L876_fin : (prmOK pL876 876 && ptTest pL876 (runFrom pL876 (fmask pL876) (cmask pL876) (hmask pL876) 1 875 (true, (init pL876), (init pL876))) 876 438 false) = true := by
  decide +kernel
theorem L876_ok : RunOK pL876 876 (runFrom pL876 (fmask pL876) (cmask pL876) (hmask pL876) 1 875 (true, (init pL876), (init pL876))) ∧ ptTest pL876 (runFrom pL876 (fmask pL876) (cmask pL876) (hmask pL876) 1 875 (true, (init pL876), (init pL876))) 876 438 false = true :=
  fin_run (runOK_init (prmOK_of_and L876_fin) true) (by decide) rfl L876_fin ptTest_fst
theorem H876_fin : (prmOK pH876 876 && ptTest pH876 (runFrom pH876 (fmask pH876) (cmask pH876) (hmask pH876) 1 875 (true, (init pH876), (init pH876))) 876 438 true) = true := by
  decide +kernel
theorem H876_ok : RunOK pH876 876 (runFrom pH876 (fmask pH876) (cmask pH876) (hmask pH876) 1 875 (true, (init pH876), (init pH876))) ∧ ptTest pH876 (runFrom pH876 (fmask pH876) (cmask pH876) (hmask pH876) 1 875 (true, (init pH876), (init pH876))) 876 438 true = true :=
  fin_run (runOK_init (prmOK_of_and H876_fin) true) (by decide) rfl H876_fin ptTest_fst
theorem I876_fin : (prmOK pI876 876 && intTest pI876 (runFrom pI876 (fmask pI876) (cmask pI876) (hmask pI876) 1 875 (true, (init pI876), (init pI876))) 876 17 true) = true := by
  decide +kernel
theorem I876_ok : RunOK pI876 876 (runFrom pI876 (fmask pI876) (cmask pI876) (hmask pI876) 1 875 (true, (init pI876), (init pI876))) ∧ intTest pI876 (runFrom pI876 (fmask pI876) (cmask pI876) (hmask pI876) 1 875 (true, (init pI876), (init pI876))) 876 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I876_fin) true) (by decide) rfl I876_fin intTest_fst
theorem link876 : linkOK pL876 pH876 pI876 = true := by decide +kernel
theorem cvx876 : ConvexBetweenHumps 876 :=
  cvx_of L876_ok H876_ok I876_ok link876 (by decide)
theorem cenlink876 : cenLinkOK pI876 876 = true := by decide +kernel
theorem cen876 : CenterUniqueMin 876 ∧ DipHyp 876 ∧ OnePointHyps 876 :=
  cen_of L876_ok H876_ok I876_ok link876 cenlink876

/-! ### `N = 877` -/

def pL877 : Prm := ⟨75, 35, 37, 879, 11, 18446744073709551616, 191549076849669478, 191549076849669478⟩
def pH877 : Prm := ⟨75, 35, 37, 879, 11, 18446744073709551616, 191551275872925030, 191551275872925030⟩
def pI877 : Prm := ⟨63, 31, 29, 879, 11, 18446744073709551616, 191549076849669478, 191551275872925030⟩
theorem L877_fin : (prmOK pL877 877 && ptTest pL877 (runFrom pL877 (fmask pL877) (cmask pL877) (hmask pL877) 1 876 (true, (init pL877), (init pL877))) 877 439 false) = true := by
  decide +kernel
theorem L877_ok : RunOK pL877 877 (runFrom pL877 (fmask pL877) (cmask pL877) (hmask pL877) 1 876 (true, (init pL877), (init pL877))) ∧ ptTest pL877 (runFrom pL877 (fmask pL877) (cmask pL877) (hmask pL877) 1 876 (true, (init pL877), (init pL877))) 877 439 false = true :=
  fin_run (runOK_init (prmOK_of_and L877_fin) true) (by decide) rfl L877_fin ptTest_fst
theorem H877_fin : (prmOK pH877 877 && ptTest pH877 (runFrom pH877 (fmask pH877) (cmask pH877) (hmask pH877) 1 876 (true, (init pH877), (init pH877))) 877 439 true) = true := by
  decide +kernel
theorem H877_ok : RunOK pH877 877 (runFrom pH877 (fmask pH877) (cmask pH877) (hmask pH877) 1 876 (true, (init pH877), (init pH877))) ∧ ptTest pH877 (runFrom pH877 (fmask pH877) (cmask pH877) (hmask pH877) 1 876 (true, (init pH877), (init pH877))) 877 439 true = true :=
  fin_run (runOK_init (prmOK_of_and H877_fin) true) (by decide) rfl H877_fin ptTest_fst
theorem I877_fin : (prmOK pI877 877 && intTest pI877 (runFrom pI877 (fmask pI877) (cmask pI877) (hmask pI877) 1 876 (true, (init pI877), (init pI877))) 877 17 false) = true := by
  decide +kernel
theorem I877_ok : RunOK pI877 877 (runFrom pI877 (fmask pI877) (cmask pI877) (hmask pI877) 1 876 (true, (init pI877), (init pI877))) ∧ intTest pI877 (runFrom pI877 (fmask pI877) (cmask pI877) (hmask pI877) 1 876 (true, (init pI877), (init pI877))) 877 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I877_fin) true) (by decide) rfl I877_fin intTest_fst
theorem link877 : linkOK pL877 pH877 pI877 = true := by decide +kernel
theorem cvx877 : ConvexBetweenHumps 877 :=
  cvx_of L877_ok H877_ok I877_ok link877 (by decide)

/-! ### `N = 878` -/

def pL878 : Prm := ⟨75, 35, 37, 880, 11, 18446744073709551616, 191376145523300543, 191376145523300543⟩
def pH878 : Prm := ⟨75, 35, 37, 880, 11, 18446744073709551616, 191378344546556095, 191378344546556095⟩
def pI878 : Prm := ⟨63, 31, 29, 880, 11, 18446744073709551616, 191376145523300543, 191378344546556095⟩
theorem L878_fin : (prmOK pL878 878 && ptTest pL878 (runFrom pL878 (fmask pL878) (cmask pL878) (hmask pL878) 1 877 (true, (init pL878), (init pL878))) 878 439 false) = true := by
  decide +kernel
theorem L878_ok : RunOK pL878 878 (runFrom pL878 (fmask pL878) (cmask pL878) (hmask pL878) 1 877 (true, (init pL878), (init pL878))) ∧ ptTest pL878 (runFrom pL878 (fmask pL878) (cmask pL878) (hmask pL878) 1 877 (true, (init pL878), (init pL878))) 878 439 false = true :=
  fin_run (runOK_init (prmOK_of_and L878_fin) true) (by decide) rfl L878_fin ptTest_fst
theorem H878_fin : (prmOK pH878 878 && ptTest pH878 (runFrom pH878 (fmask pH878) (cmask pH878) (hmask pH878) 1 877 (true, (init pH878), (init pH878))) 878 439 true) = true := by
  decide +kernel
theorem H878_ok : RunOK pH878 878 (runFrom pH878 (fmask pH878) (cmask pH878) (hmask pH878) 1 877 (true, (init pH878), (init pH878))) ∧ ptTest pH878 (runFrom pH878 (fmask pH878) (cmask pH878) (hmask pH878) 1 877 (true, (init pH878), (init pH878))) 878 439 true = true :=
  fin_run (runOK_init (prmOK_of_and H878_fin) true) (by decide) rfl H878_fin ptTest_fst
theorem I878_fin : (prmOK pI878 878 && intTest pI878 (runFrom pI878 (fmask pI878) (cmask pI878) (hmask pI878) 1 877 (true, (init pI878), (init pI878))) 878 17 true) = true := by
  decide +kernel
theorem I878_ok : RunOK pI878 878 (runFrom pI878 (fmask pI878) (cmask pI878) (hmask pI878) 1 877 (true, (init pI878), (init pI878))) ∧ intTest pI878 (runFrom pI878 (fmask pI878) (cmask pI878) (hmask pI878) 1 877 (true, (init pI878), (init pI878))) 878 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I878_fin) true) (by decide) rfl I878_fin intTest_fst
theorem link878 : linkOK pL878 pH878 pI878 = true := by decide +kernel
theorem cvx878 : ConvexBetweenHumps 878 :=
  cvx_of L878_ok H878_ok I878_ok link878 (by decide)
theorem cenlink878 : cenLinkOK pI878 878 = true := by decide +kernel
theorem cen878 : CenterUniqueMin 878 ∧ DipHyp 878 ∧ OnePointHyps 878 :=
  cen_of L878_ok H878_ok I878_ok link878 cenlink878

/-! ### `N = 879` -/

def pL879 : Prm := ⟨75, 35, 37, 881, 11, 18446744073709551616, 191203384611956303, 191203384611956303⟩
def pH879 : Prm := ⟨75, 35, 37, 881, 11, 18446744073709551616, 191205583635211855, 191205583635211855⟩
def pI879 : Prm := ⟨63, 31, 29, 881, 11, 18446744073709551616, 191203384611956303, 191205583635211855⟩
theorem L879_fin : (prmOK pL879 879 && ptTest pL879 (runFrom pL879 (fmask pL879) (cmask pL879) (hmask pL879) 1 878 (true, (init pL879), (init pL879))) 879 440 false) = true := by
  decide +kernel
theorem L879_ok : RunOK pL879 879 (runFrom pL879 (fmask pL879) (cmask pL879) (hmask pL879) 1 878 (true, (init pL879), (init pL879))) ∧ ptTest pL879 (runFrom pL879 (fmask pL879) (cmask pL879) (hmask pL879) 1 878 (true, (init pL879), (init pL879))) 879 440 false = true :=
  fin_run (runOK_init (prmOK_of_and L879_fin) true) (by decide) rfl L879_fin ptTest_fst
theorem H879_fin : (prmOK pH879 879 && ptTest pH879 (runFrom pH879 (fmask pH879) (cmask pH879) (hmask pH879) 1 878 (true, (init pH879), (init pH879))) 879 440 true) = true := by
  decide +kernel
theorem H879_ok : RunOK pH879 879 (runFrom pH879 (fmask pH879) (cmask pH879) (hmask pH879) 1 878 (true, (init pH879), (init pH879))) ∧ ptTest pH879 (runFrom pH879 (fmask pH879) (cmask pH879) (hmask pH879) 1 878 (true, (init pH879), (init pH879))) 879 440 true = true :=
  fin_run (runOK_init (prmOK_of_and H879_fin) true) (by decide) rfl H879_fin ptTest_fst
theorem I879_fin : (prmOK pI879 879 && intTest pI879 (runFrom pI879 (fmask pI879) (cmask pI879) (hmask pI879) 1 878 (true, (init pI879), (init pI879))) 879 17 false) = true := by
  decide +kernel
theorem I879_ok : RunOK pI879 879 (runFrom pI879 (fmask pI879) (cmask pI879) (hmask pI879) 1 878 (true, (init pI879), (init pI879))) ∧ intTest pI879 (runFrom pI879 (fmask pI879) (cmask pI879) (hmask pI879) 1 878 (true, (init pI879), (init pI879))) 879 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I879_fin) true) (by decide) rfl I879_fin intTest_fst
theorem link879 : linkOK pL879 pH879 pI879 = true := by decide +kernel
theorem cvx879 : ConvexBetweenHumps 879 :=
  cvx_of L879_ok H879_ok I879_ok link879 (by decide)

/-! ### `N = 880` -/

def pL880 : Prm := ⟨75, 35, 37, 882, 11, 18446744073709551616, 191031136453725928, 191031136453725928⟩
def pH880 : Prm := ⟨75, 35, 37, 882, 11, 18446744073709551616, 191033335476981480, 191033335476981480⟩
def pI880 : Prm := ⟨63, 31, 29, 882, 11, 18446744073709551616, 191031136453725928, 191033335476981480⟩
theorem L880_fin : (prmOK pL880 880 && ptTest pL880 (runFrom pL880 (fmask pL880) (cmask pL880) (hmask pL880) 1 879 (true, (init pL880), (init pL880))) 880 440 false) = true := by
  decide +kernel
theorem L880_ok : RunOK pL880 880 (runFrom pL880 (fmask pL880) (cmask pL880) (hmask pL880) 1 879 (true, (init pL880), (init pL880))) ∧ ptTest pL880 (runFrom pL880 (fmask pL880) (cmask pL880) (hmask pL880) 1 879 (true, (init pL880), (init pL880))) 880 440 false = true :=
  fin_run (runOK_init (prmOK_of_and L880_fin) true) (by decide) rfl L880_fin ptTest_fst
theorem H880_fin : (prmOK pH880 880 && ptTest pH880 (runFrom pH880 (fmask pH880) (cmask pH880) (hmask pH880) 1 879 (true, (init pH880), (init pH880))) 880 440 true) = true := by
  decide +kernel
theorem H880_ok : RunOK pH880 880 (runFrom pH880 (fmask pH880) (cmask pH880) (hmask pH880) 1 879 (true, (init pH880), (init pH880))) ∧ ptTest pH880 (runFrom pH880 (fmask pH880) (cmask pH880) (hmask pH880) 1 879 (true, (init pH880), (init pH880))) 880 440 true = true :=
  fin_run (runOK_init (prmOK_of_and H880_fin) true) (by decide) rfl H880_fin ptTest_fst
theorem I880_fin : (prmOK pI880 880 && intTest pI880 (runFrom pI880 (fmask pI880) (cmask pI880) (hmask pI880) 1 879 (true, (init pI880), (init pI880))) 880 17 true) = true := by
  decide +kernel
theorem I880_ok : RunOK pI880 880 (runFrom pI880 (fmask pI880) (cmask pI880) (hmask pI880) 1 879 (true, (init pI880), (init pI880))) ∧ intTest pI880 (runFrom pI880 (fmask pI880) (cmask pI880) (hmask pI880) 1 879 (true, (init pI880), (init pI880))) 880 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I880_fin) true) (by decide) rfl I880_fin intTest_fst
theorem link880 : linkOK pL880 pH880 pI880 = true := by decide +kernel
theorem cvx880 : ConvexBetweenHumps 880 :=
  cvx_of L880_ok H880_ok I880_ok link880 (by decide)
theorem cenlink880 : cenLinkOK pI880 880 = true := by decide +kernel
theorem cen880 : CenterUniqueMin 880 ∧ DipHyp 880 ∧ OnePointHyps 880 :=
  cen_of L880_ok H880_ok I880_ok link880 cenlink880

/-! ### `N = 881` -/

def pL881 : Prm := ⟨75, 35, 37, 883, 11, 18446744073709551616, 190859057803254035, 190859057803254035⟩
def pH881 : Prm := ⟨75, 35, 37, 883, 11, 18446744073709551616, 190861256826509587, 190861256826509587⟩
def pI881 : Prm := ⟨63, 31, 29, 883, 11, 18446744073709551616, 190859057803254035, 190861256826509587⟩
theorem L881_fin : (prmOK pL881 881 && ptTest pL881 (runFrom pL881 (fmask pL881) (cmask pL881) (hmask pL881) 1 880 (true, (init pL881), (init pL881))) 881 441 false) = true := by
  decide +kernel
theorem L881_ok : RunOK pL881 881 (runFrom pL881 (fmask pL881) (cmask pL881) (hmask pL881) 1 880 (true, (init pL881), (init pL881))) ∧ ptTest pL881 (runFrom pL881 (fmask pL881) (cmask pL881) (hmask pL881) 1 880 (true, (init pL881), (init pL881))) 881 441 false = true :=
  fin_run (runOK_init (prmOK_of_and L881_fin) true) (by decide) rfl L881_fin ptTest_fst
theorem H881_fin : (prmOK pH881 881 && ptTest pH881 (runFrom pH881 (fmask pH881) (cmask pH881) (hmask pH881) 1 880 (true, (init pH881), (init pH881))) 881 441 true) = true := by
  decide +kernel
theorem H881_ok : RunOK pH881 881 (runFrom pH881 (fmask pH881) (cmask pH881) (hmask pH881) 1 880 (true, (init pH881), (init pH881))) ∧ ptTest pH881 (runFrom pH881 (fmask pH881) (cmask pH881) (hmask pH881) 1 880 (true, (init pH881), (init pH881))) 881 441 true = true :=
  fin_run (runOK_init (prmOK_of_and H881_fin) true) (by decide) rfl H881_fin ptTest_fst
theorem I881_fin : (prmOK pI881 881 && intTest pI881 (runFrom pI881 (fmask pI881) (cmask pI881) (hmask pI881) 1 880 (true, (init pI881), (init pI881))) 881 17 false) = true := by
  decide +kernel
theorem I881_ok : RunOK pI881 881 (runFrom pI881 (fmask pI881) (cmask pI881) (hmask pI881) 1 880 (true, (init pI881), (init pI881))) ∧ intTest pI881 (runFrom pI881 (fmask pI881) (cmask pI881) (hmask pI881) 1 880 (true, (init pI881), (init pI881))) 881 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I881_fin) true) (by decide) rfl I881_fin intTest_fst
theorem link881 : linkOK pL881 pH881 pI881 = true := by decide +kernel
theorem cvx881 : ConvexBetweenHumps 881 :=
  cvx_of L881_ok H881_ok I881_ok link881 (by decide)

/-! ### `N = 882` -/

def pL882 : Prm := ⟨75, 35, 37, 884, 11, 18446744073709551616, 190687488630289214, 190687488630289214⟩
def pH882 : Prm := ⟨75, 35, 37, 884, 11, 18446744073709551616, 190689687653544766, 190689687653544766⟩
def pI882 : Prm := ⟨63, 31, 29, 884, 11, 18446744073709551616, 190687488630289214, 190689687653544766⟩
theorem L882_fin : (prmOK pL882 882 && ptTest pL882 (runFrom pL882 (fmask pL882) (cmask pL882) (hmask pL882) 1 881 (true, (init pL882), (init pL882))) 882 441 false) = true := by
  decide +kernel
theorem L882_ok : RunOK pL882 882 (runFrom pL882 (fmask pL882) (cmask pL882) (hmask pL882) 1 881 (true, (init pL882), (init pL882))) ∧ ptTest pL882 (runFrom pL882 (fmask pL882) (cmask pL882) (hmask pL882) 1 881 (true, (init pL882), (init pL882))) 882 441 false = true :=
  fin_run (runOK_init (prmOK_of_and L882_fin) true) (by decide) rfl L882_fin ptTest_fst
theorem H882_fin : (prmOK pH882 882 && ptTest pH882 (runFrom pH882 (fmask pH882) (cmask pH882) (hmask pH882) 1 881 (true, (init pH882), (init pH882))) 882 441 true) = true := by
  decide +kernel
theorem H882_ok : RunOK pH882 882 (runFrom pH882 (fmask pH882) (cmask pH882) (hmask pH882) 1 881 (true, (init pH882), (init pH882))) ∧ ptTest pH882 (runFrom pH882 (fmask pH882) (cmask pH882) (hmask pH882) 1 881 (true, (init pH882), (init pH882))) 882 441 true = true :=
  fin_run (runOK_init (prmOK_of_and H882_fin) true) (by decide) rfl H882_fin ptTest_fst
theorem I882_fin : (prmOK pI882 882 && intTest pI882 (runFrom pI882 (fmask pI882) (cmask pI882) (hmask pI882) 1 881 (true, (init pI882), (init pI882))) 882 17 true) = true := by
  decide +kernel
theorem I882_ok : RunOK pI882 882 (runFrom pI882 (fmask pI882) (cmask pI882) (hmask pI882) 1 881 (true, (init pI882), (init pI882))) ∧ intTest pI882 (runFrom pI882 (fmask pI882) (cmask pI882) (hmask pI882) 1 881 (true, (init pI882), (init pI882))) 882 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I882_fin) true) (by decide) rfl I882_fin intTest_fst
theorem link882 : linkOK pL882 pH882 pI882 = true := by decide +kernel
theorem cvx882 : ConvexBetweenHumps 882 :=
  cvx_of L882_ok H882_ok I882_ok link882 (by decide)
theorem cenlink882 : cenLinkOK pI882 882 = true := by decide +kernel
theorem cen882 : CenterUniqueMin 882 ∧ DipHyp 882 ∧ OnePointHyps 882 :=
  cen_of L882_ok H882_ok I882_ok link882 cenlink882

/-! ### `N = 883` -/

def pL883 : Prm := ⟨75, 35, 37, 885, 11, 18446744073709551616, 190516088064346809, 190516088064346809⟩
def pH883 : Prm := ⟨75, 35, 37, 885, 11, 18446744073709551616, 190518287087602361, 190518287087602361⟩
def pI883 : Prm := ⟨63, 31, 29, 885, 11, 18446744073709551616, 190516088064346809, 190518287087602361⟩
theorem L883_fin : (prmOK pL883 883 && ptTest pL883 (runFrom pL883 (fmask pL883) (cmask pL883) (hmask pL883) 1 882 (true, (init pL883), (init pL883))) 883 442 false) = true := by
  decide +kernel
theorem L883_ok : RunOK pL883 883 (runFrom pL883 (fmask pL883) (cmask pL883) (hmask pL883) 1 882 (true, (init pL883), (init pL883))) ∧ ptTest pL883 (runFrom pL883 (fmask pL883) (cmask pL883) (hmask pL883) 1 882 (true, (init pL883), (init pL883))) 883 442 false = true :=
  fin_run (runOK_init (prmOK_of_and L883_fin) true) (by decide) rfl L883_fin ptTest_fst
theorem H883_fin : (prmOK pH883 883 && ptTest pH883 (runFrom pH883 (fmask pH883) (cmask pH883) (hmask pH883) 1 882 (true, (init pH883), (init pH883))) 883 442 true) = true := by
  decide +kernel
theorem H883_ok : RunOK pH883 883 (runFrom pH883 (fmask pH883) (cmask pH883) (hmask pH883) 1 882 (true, (init pH883), (init pH883))) ∧ ptTest pH883 (runFrom pH883 (fmask pH883) (cmask pH883) (hmask pH883) 1 882 (true, (init pH883), (init pH883))) 883 442 true = true :=
  fin_run (runOK_init (prmOK_of_and H883_fin) true) (by decide) rfl H883_fin ptTest_fst
theorem I883_fin : (prmOK pI883 883 && intTest pI883 (runFrom pI883 (fmask pI883) (cmask pI883) (hmask pI883) 1 882 (true, (init pI883), (init pI883))) 883 17 false) = true := by
  decide +kernel
theorem I883_ok : RunOK pI883 883 (runFrom pI883 (fmask pI883) (cmask pI883) (hmask pI883) 1 882 (true, (init pI883), (init pI883))) ∧ intTest pI883 (runFrom pI883 (fmask pI883) (cmask pI883) (hmask pI883) 1 882 (true, (init pI883), (init pI883))) 883 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I883_fin) true) (by decide) rfl I883_fin intTest_fst
theorem link883 : linkOK pL883 pH883 pI883 = true := by decide +kernel
theorem cvx883 : ConvexBetweenHumps 883 :=
  cvx_of L883_ok H883_ok I883_ok link883 (by decide)

/-! ### `N = 884` -/

def pL884 : Prm := ⟨75, 35, 37, 886, 11, 18446744073709551616, 190345193728546650, 190345193728546650⟩
def pH884 : Prm := ⟨75, 35, 37, 886, 11, 18446744073709551616, 190347392751802202, 190347392751802202⟩
def pI884 : Prm := ⟨63, 31, 29, 886, 11, 18446744073709551616, 190345193728546650, 190347392751802202⟩
theorem L884_fin : (prmOK pL884 884 && ptTest pL884 (runFrom pL884 (fmask pL884) (cmask pL884) (hmask pL884) 1 883 (true, (init pL884), (init pL884))) 884 442 false) = true := by
  decide +kernel
theorem L884_ok : RunOK pL884 884 (runFrom pL884 (fmask pL884) (cmask pL884) (hmask pL884) 1 883 (true, (init pL884), (init pL884))) ∧ ptTest pL884 (runFrom pL884 (fmask pL884) (cmask pL884) (hmask pL884) 1 883 (true, (init pL884), (init pL884))) 884 442 false = true :=
  fin_run (runOK_init (prmOK_of_and L884_fin) true) (by decide) rfl L884_fin ptTest_fst
theorem H884_fin : (prmOK pH884 884 && ptTest pH884 (runFrom pH884 (fmask pH884) (cmask pH884) (hmask pH884) 1 883 (true, (init pH884), (init pH884))) 884 442 true) = true := by
  decide +kernel
theorem H884_ok : RunOK pH884 884 (runFrom pH884 (fmask pH884) (cmask pH884) (hmask pH884) 1 883 (true, (init pH884), (init pH884))) ∧ ptTest pH884 (runFrom pH884 (fmask pH884) (cmask pH884) (hmask pH884) 1 883 (true, (init pH884), (init pH884))) 884 442 true = true :=
  fin_run (runOK_init (prmOK_of_and H884_fin) true) (by decide) rfl H884_fin ptTest_fst
theorem I884_fin : (prmOK pI884 884 && intTest pI884 (runFrom pI884 (fmask pI884) (cmask pI884) (hmask pI884) 1 883 (true, (init pI884), (init pI884))) 884 17 true) = true := by
  decide +kernel
theorem I884_ok : RunOK pI884 884 (runFrom pI884 (fmask pI884) (cmask pI884) (hmask pI884) 1 883 (true, (init pI884), (init pI884))) ∧ intTest pI884 (runFrom pI884 (fmask pI884) (cmask pI884) (hmask pI884) 1 883 (true, (init pI884), (init pI884))) 884 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I884_fin) true) (by decide) rfl I884_fin intTest_fst
theorem link884 : linkOK pL884 pH884 pI884 = true := by decide +kernel
theorem cvx884 : ConvexBetweenHumps 884 :=
  cvx_of L884_ok H884_ok I884_ok link884 (by decide)
theorem cenlink884 : cenLinkOK pI884 884 = true := by decide +kernel
theorem cen884 : CenterUniqueMin 884 ∧ DipHyp 884 ∧ OnePointHyps 884 :=
  cen_of L884_ok H884_ok I884_ok link884 cenlink884

/-! ### `N = 885` -/

def pL885 : Prm := ⟨75, 35, 37, 887, 11, 18446744073709551616, 190174467105452308, 190174467105452308⟩
def pH885 : Prm := ⟨75, 35, 37, 887, 11, 18446744073709551616, 190176666128707860, 190176666128707860⟩
def pI885 : Prm := ⟨63, 31, 29, 887, 11, 18446744073709551616, 190174467105452308, 190176666128707860⟩
theorem L885_fin : (prmOK pL885 885 && ptTest pL885 (runFrom pL885 (fmask pL885) (cmask pL885) (hmask pL885) 1 884 (true, (init pL885), (init pL885))) 885 443 false) = true := by
  decide +kernel
theorem L885_ok : RunOK pL885 885 (runFrom pL885 (fmask pL885) (cmask pL885) (hmask pL885) 1 884 (true, (init pL885), (init pL885))) ∧ ptTest pL885 (runFrom pL885 (fmask pL885) (cmask pL885) (hmask pL885) 1 884 (true, (init pL885), (init pL885))) 885 443 false = true :=
  fin_run (runOK_init (prmOK_of_and L885_fin) true) (by decide) rfl L885_fin ptTest_fst
theorem H885_fin : (prmOK pH885 885 && ptTest pH885 (runFrom pH885 (fmask pH885) (cmask pH885) (hmask pH885) 1 884 (true, (init pH885), (init pH885))) 885 443 true) = true := by
  decide +kernel
theorem H885_ok : RunOK pH885 885 (runFrom pH885 (fmask pH885) (cmask pH885) (hmask pH885) 1 884 (true, (init pH885), (init pH885))) ∧ ptTest pH885 (runFrom pH885 (fmask pH885) (cmask pH885) (hmask pH885) 1 884 (true, (init pH885), (init pH885))) 885 443 true = true :=
  fin_run (runOK_init (prmOK_of_and H885_fin) true) (by decide) rfl H885_fin ptTest_fst
theorem I885_fin : (prmOK pI885 885 && intTest pI885 (runFrom pI885 (fmask pI885) (cmask pI885) (hmask pI885) 1 884 (true, (init pI885), (init pI885))) 885 17 false) = true := by
  decide +kernel
theorem I885_ok : RunOK pI885 885 (runFrom pI885 (fmask pI885) (cmask pI885) (hmask pI885) 1 884 (true, (init pI885), (init pI885))) ∧ intTest pI885 (runFrom pI885 (fmask pI885) (cmask pI885) (hmask pI885) 1 884 (true, (init pI885), (init pI885))) 885 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I885_fin) true) (by decide) rfl I885_fin intTest_fst
theorem link885 : linkOK pL885 pH885 pI885 = true := by decide +kernel
theorem cvx885 : ConvexBetweenHumps 885 :=
  cvx_of L885_ok H885_ok I885_ok link885 (by decide)

/-! ### `N = 886` -/

def pL886 : Prm := ⟨75, 35, 37, 888, 11, 18446744073709551616, 190004243493063754, 190004243493063754⟩
def pH886 : Prm := ⟨75, 35, 37, 888, 11, 18446744073709551616, 190006442516319306, 190006442516319306⟩
def pI886 : Prm := ⟨63, 31, 29, 888, 11, 18446744073709551616, 190004243493063754, 190006442516319306⟩
theorem L886_fin : (prmOK pL886 886 && ptTest pL886 (runFrom pL886 (fmask pL886) (cmask pL886) (hmask pL886) 1 885 (true, (init pL886), (init pL886))) 886 443 false) = true := by
  decide +kernel
theorem L886_ok : RunOK pL886 886 (runFrom pL886 (fmask pL886) (cmask pL886) (hmask pL886) 1 885 (true, (init pL886), (init pL886))) ∧ ptTest pL886 (runFrom pL886 (fmask pL886) (cmask pL886) (hmask pL886) 1 885 (true, (init pL886), (init pL886))) 886 443 false = true :=
  fin_run (runOK_init (prmOK_of_and L886_fin) true) (by decide) rfl L886_fin ptTest_fst
theorem H886_fin : (prmOK pH886 886 && ptTest pH886 (runFrom pH886 (fmask pH886) (cmask pH886) (hmask pH886) 1 885 (true, (init pH886), (init pH886))) 886 443 true) = true := by
  decide +kernel
theorem H886_ok : RunOK pH886 886 (runFrom pH886 (fmask pH886) (cmask pH886) (hmask pH886) 1 885 (true, (init pH886), (init pH886))) ∧ ptTest pH886 (runFrom pH886 (fmask pH886) (cmask pH886) (hmask pH886) 1 885 (true, (init pH886), (init pH886))) 886 443 true = true :=
  fin_run (runOK_init (prmOK_of_and H886_fin) true) (by decide) rfl H886_fin ptTest_fst
theorem I886_fin : (prmOK pI886 886 && intTest pI886 (runFrom pI886 (fmask pI886) (cmask pI886) (hmask pI886) 1 885 (true, (init pI886), (init pI886))) 886 17 true) = true := by
  decide +kernel
theorem I886_ok : RunOK pI886 886 (runFrom pI886 (fmask pI886) (cmask pI886) (hmask pI886) 1 885 (true, (init pI886), (init pI886))) ∧ intTest pI886 (runFrom pI886 (fmask pI886) (cmask pI886) (hmask pI886) 1 885 (true, (init pI886), (init pI886))) 886 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I886_fin) true) (by decide) rfl I886_fin intTest_fst
theorem link886 : linkOK pL886 pH886 pI886 = true := by decide +kernel
theorem cvx886 : ConvexBetweenHumps 886 :=
  cvx_of L886_ok H886_ok I886_ok link886 (by decide)
theorem cenlink886 : cenLinkOK pI886 886 = true := by decide +kernel
theorem cen886 : CenterUniqueMin 886 ∧ DipHyp 886 ∧ OnePointHyps 886 :=
  cen_of L886_ok H886_ok I886_ok link886 cenlink886

/-! ### `N = 887` -/

def pL887 : Prm := ⟨75, 35, 37, 889, 11, 18446744073709551616, 189834186705446992, 189834186705446992⟩
def pH887 : Prm := ⟨75, 35, 37, 889, 11, 18446744073709551616, 189836385728702544, 189836385728702544⟩
def pI887 : Prm := ⟨63, 31, 29, 889, 11, 18446744073709551616, 189834186705446992, 189836385728702544⟩
theorem L887_fin : (prmOK pL887 887 && ptTest pL887 (runFrom pL887 (fmask pL887) (cmask pL887) (hmask pL887) 1 886 (true, (init pL887), (init pL887))) 887 444 false) = true := by
  decide +kernel
theorem L887_ok : RunOK pL887 887 (runFrom pL887 (fmask pL887) (cmask pL887) (hmask pL887) 1 886 (true, (init pL887), (init pL887))) ∧ ptTest pL887 (runFrom pL887 (fmask pL887) (cmask pL887) (hmask pL887) 1 886 (true, (init pL887), (init pL887))) 887 444 false = true :=
  fin_run (runOK_init (prmOK_of_and L887_fin) true) (by decide) rfl L887_fin ptTest_fst
theorem H887_fin : (prmOK pH887 887 && ptTest pH887 (runFrom pH887 (fmask pH887) (cmask pH887) (hmask pH887) 1 886 (true, (init pH887), (init pH887))) 887 444 true) = true := by
  decide +kernel
theorem H887_ok : RunOK pH887 887 (runFrom pH887 (fmask pH887) (cmask pH887) (hmask pH887) 1 886 (true, (init pH887), (init pH887))) ∧ ptTest pH887 (runFrom pH887 (fmask pH887) (cmask pH887) (hmask pH887) 1 886 (true, (init pH887), (init pH887))) 887 444 true = true :=
  fin_run (runOK_init (prmOK_of_and H887_fin) true) (by decide) rfl H887_fin ptTest_fst
theorem I887_fin : (prmOK pI887 887 && intTest pI887 (runFrom pI887 (fmask pI887) (cmask pI887) (hmask pI887) 1 886 (true, (init pI887), (init pI887))) 887 17 false) = true := by
  decide +kernel
theorem I887_ok : RunOK pI887 887 (runFrom pI887 (fmask pI887) (cmask pI887) (hmask pI887) 1 886 (true, (init pI887), (init pI887))) ∧ intTest pI887 (runFrom pI887 (fmask pI887) (cmask pI887) (hmask pI887) 1 886 (true, (init pI887), (init pI887))) 887 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I887_fin) true) (by decide) rfl I887_fin intTest_fst
theorem link887 : linkOK pL887 pH887 pI887 = true := by decide +kernel
theorem cvx887 : ConvexBetweenHumps 887 :=
  cvx_of L887_ok H887_ok I887_ok link887 (by decide)

/-! ### `N = 888` -/

def pL888 : Prm := ⟨75, 35, 37, 890, 11, 18446744073709551616, 189664629736677444, 189664629736677444⟩
def pH888 : Prm := ⟨75, 35, 37, 890, 11, 18446744073709551616, 189666828759932996, 189666828759932996⟩
def pI888 : Prm := ⟨63, 31, 29, 890, 11, 18446744073709551616, 189664629736677444, 189666828759932996⟩
theorem L888_fin : (prmOK pL888 888 && ptTest pL888 (runFrom pL888 (fmask pL888) (cmask pL888) (hmask pL888) 1 887 (true, (init pL888), (init pL888))) 888 444 false) = true := by
  decide +kernel
theorem L888_ok : RunOK pL888 888 (runFrom pL888 (fmask pL888) (cmask pL888) (hmask pL888) 1 887 (true, (init pL888), (init pL888))) ∧ ptTest pL888 (runFrom pL888 (fmask pL888) (cmask pL888) (hmask pL888) 1 887 (true, (init pL888), (init pL888))) 888 444 false = true :=
  fin_run (runOK_init (prmOK_of_and L888_fin) true) (by decide) rfl L888_fin ptTest_fst
theorem H888_fin : (prmOK pH888 888 && ptTest pH888 (runFrom pH888 (fmask pH888) (cmask pH888) (hmask pH888) 1 887 (true, (init pH888), (init pH888))) 888 444 true) = true := by
  decide +kernel
theorem H888_ok : RunOK pH888 888 (runFrom pH888 (fmask pH888) (cmask pH888) (hmask pH888) 1 887 (true, (init pH888), (init pH888))) ∧ ptTest pH888 (runFrom pH888 (fmask pH888) (cmask pH888) (hmask pH888) 1 887 (true, (init pH888), (init pH888))) 888 444 true = true :=
  fin_run (runOK_init (prmOK_of_and H888_fin) true) (by decide) rfl H888_fin ptTest_fst
theorem I888_fin : (prmOK pI888 888 && intTest pI888 (runFrom pI888 (fmask pI888) (cmask pI888) (hmask pI888) 1 887 (true, (init pI888), (init pI888))) 888 17 true) = true := by
  decide +kernel
theorem I888_ok : RunOK pI888 888 (runFrom pI888 (fmask pI888) (cmask pI888) (hmask pI888) 1 887 (true, (init pI888), (init pI888))) ∧ intTest pI888 (runFrom pI888 (fmask pI888) (cmask pI888) (hmask pI888) 1 887 (true, (init pI888), (init pI888))) 888 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I888_fin) true) (by decide) rfl I888_fin intTest_fst
theorem link888 : linkOK pL888 pH888 pI888 = true := by decide +kernel
theorem cvx888 : ConvexBetweenHumps 888 :=
  cvx_of L888_ok H888_ok I888_ok link888 (by decide)
theorem cenlink888 : cenLinkOK pI888 888 = true := by decide +kernel
theorem cen888 : CenterUniqueMin 888 ∧ DipHyp 888 ∧ OnePointHyps 888 :=
  cen_of L888_ok H888_ok I888_ok link888 cenlink888

/-! ### `N = 889` -/

def pL889 : Prm := ⟨75, 35, 37, 891, 11, 18446744073709551616, 189495238711128235, 189495238711128235⟩
def pH889 : Prm := ⟨75, 35, 37, 891, 11, 18446744073709551616, 189497437734383787, 189497437734383787⟩
def pI889 : Prm := ⟨63, 31, 29, 891, 11, 18446744073709551616, 189495238711128235, 189497437734383787⟩
theorem L889_fin : (prmOK pL889 889 && ptTest pL889 (runFrom pL889 (fmask pL889) (cmask pL889) (hmask pL889) 1 888 (true, (init pL889), (init pL889))) 889 445 false) = true := by
  decide +kernel
theorem L889_ok : RunOK pL889 889 (runFrom pL889 (fmask pL889) (cmask pL889) (hmask pL889) 1 888 (true, (init pL889), (init pL889))) ∧ ptTest pL889 (runFrom pL889 (fmask pL889) (cmask pL889) (hmask pL889) 1 888 (true, (init pL889), (init pL889))) 889 445 false = true :=
  fin_run (runOK_init (prmOK_of_and L889_fin) true) (by decide) rfl L889_fin ptTest_fst
theorem H889_fin : (prmOK pH889 889 && ptTest pH889 (runFrom pH889 (fmask pH889) (cmask pH889) (hmask pH889) 1 888 (true, (init pH889), (init pH889))) 889 445 true) = true := by
  decide +kernel
theorem H889_ok : RunOK pH889 889 (runFrom pH889 (fmask pH889) (cmask pH889) (hmask pH889) 1 888 (true, (init pH889), (init pH889))) ∧ ptTest pH889 (runFrom pH889 (fmask pH889) (cmask pH889) (hmask pH889) 1 888 (true, (init pH889), (init pH889))) 889 445 true = true :=
  fin_run (runOK_init (prmOK_of_and H889_fin) true) (by decide) rfl H889_fin ptTest_fst
theorem I889_fin : (prmOK pI889 889 && intTest pI889 (runFrom pI889 (fmask pI889) (cmask pI889) (hmask pI889) 1 888 (true, (init pI889), (init pI889))) 889 17 false) = true := by
  decide +kernel
theorem I889_ok : RunOK pI889 889 (runFrom pI889 (fmask pI889) (cmask pI889) (hmask pI889) 1 888 (true, (init pI889), (init pI889))) ∧ intTest pI889 (runFrom pI889 (fmask pI889) (cmask pI889) (hmask pI889) 1 888 (true, (init pI889), (init pI889))) 889 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I889_fin) true) (by decide) rfl I889_fin intTest_fst
theorem link889 : linkOK pL889 pH889 pI889 = true := by decide +kernel
theorem cvx889 : ConvexBetweenHumps 889 :=
  cvx_of L889_ok H889_ok I889_ok link889 (by decide)

/-! ### `N = 890` -/

def pL890 : Prm := ⟨75, 35, 37, 892, 11, 18446744073709551616, 189326344339887296, 189326344339887296⟩
def pH890 : Prm := ⟨75, 35, 37, 892, 11, 18446744073709551616, 189328543363142848, 189328543363142848⟩
def pI890 : Prm := ⟨63, 31, 29, 892, 11, 18446744073709551616, 189326344339887296, 189328543363142848⟩
theorem L890_fin : (prmOK pL890 890 && ptTest pL890 (runFrom pL890 (fmask pL890) (cmask pL890) (hmask pL890) 1 889 (true, (init pL890), (init pL890))) 890 445 false) = true := by
  decide +kernel
theorem L890_ok : RunOK pL890 890 (runFrom pL890 (fmask pL890) (cmask pL890) (hmask pL890) 1 889 (true, (init pL890), (init pL890))) ∧ ptTest pL890 (runFrom pL890 (fmask pL890) (cmask pL890) (hmask pL890) 1 889 (true, (init pL890), (init pL890))) 890 445 false = true :=
  fin_run (runOK_init (prmOK_of_and L890_fin) true) (by decide) rfl L890_fin ptTest_fst
theorem H890_fin : (prmOK pH890 890 && ptTest pH890 (runFrom pH890 (fmask pH890) (cmask pH890) (hmask pH890) 1 889 (true, (init pH890), (init pH890))) 890 445 true) = true := by
  decide +kernel
theorem H890_ok : RunOK pH890 890 (runFrom pH890 (fmask pH890) (cmask pH890) (hmask pH890) 1 889 (true, (init pH890), (init pH890))) ∧ ptTest pH890 (runFrom pH890 (fmask pH890) (cmask pH890) (hmask pH890) 1 889 (true, (init pH890), (init pH890))) 890 445 true = true :=
  fin_run (runOK_init (prmOK_of_and H890_fin) true) (by decide) rfl H890_fin ptTest_fst
theorem I890_fin : (prmOK pI890 890 && intTest pI890 (runFrom pI890 (fmask pI890) (cmask pI890) (hmask pI890) 1 889 (true, (init pI890), (init pI890))) 890 17 true) = true := by
  decide +kernel
theorem I890_ok : RunOK pI890 890 (runFrom pI890 (fmask pI890) (cmask pI890) (hmask pI890) 1 889 (true, (init pI890), (init pI890))) ∧ intTest pI890 (runFrom pI890 (fmask pI890) (cmask pI890) (hmask pI890) 1 889 (true, (init pI890), (init pI890))) 890 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I890_fin) true) (by decide) rfl I890_fin intTest_fst
theorem link890 : linkOK pL890 pH890 pI890 = true := by decide +kernel
theorem cvx890 : ConvexBetweenHumps 890 :=
  cvx_of L890_ok H890_ok I890_ok link890 (by decide)
theorem cenlink890 : cenLinkOK pI890 890 = true := by decide +kernel
theorem cen890 : CenterUniqueMin 890 ∧ DipHyp 890 ∧ OnePointHyps 890 :=
  cen_of L890_ok H890_ok I890_ok link890 cenlink890

/-! ### `N = 891` -/

def pL891 : Prm := ⟨75, 35, 37, 893, 11, 18446744073709551616, 189157615036531795, 189157615036531795⟩
def pH891 : Prm := ⟨75, 35, 37, 893, 11, 18446744073709551616, 189159814059787347, 189159814059787347⟩
def pI891 : Prm := ⟨63, 31, 29, 893, 11, 18446744073709551616, 189157615036531795, 189159814059787347⟩
theorem L891_fin : (prmOK pL891 891 && ptTest pL891 (runFrom pL891 (fmask pL891) (cmask pL891) (hmask pL891) 1 890 (true, (init pL891), (init pL891))) 891 446 false) = true := by
  decide +kernel
theorem L891_ok : RunOK pL891 891 (runFrom pL891 (fmask pL891) (cmask pL891) (hmask pL891) 1 890 (true, (init pL891), (init pL891))) ∧ ptTest pL891 (runFrom pL891 (fmask pL891) (cmask pL891) (hmask pL891) 1 890 (true, (init pL891), (init pL891))) 891 446 false = true :=
  fin_run (runOK_init (prmOK_of_and L891_fin) true) (by decide) rfl L891_fin ptTest_fst
theorem H891_fin : (prmOK pH891 891 && ptTest pH891 (runFrom pH891 (fmask pH891) (cmask pH891) (hmask pH891) 1 890 (true, (init pH891), (init pH891))) 891 446 true) = true := by
  decide +kernel
theorem H891_ok : RunOK pH891 891 (runFrom pH891 (fmask pH891) (cmask pH891) (hmask pH891) 1 890 (true, (init pH891), (init pH891))) ∧ ptTest pH891 (runFrom pH891 (fmask pH891) (cmask pH891) (hmask pH891) 1 890 (true, (init pH891), (init pH891))) 891 446 true = true :=
  fin_run (runOK_init (prmOK_of_and H891_fin) true) (by decide) rfl H891_fin ptTest_fst
theorem I891_fin : (prmOK pI891 891 && intTest pI891 (runFrom pI891 (fmask pI891) (cmask pI891) (hmask pI891) 1 890 (true, (init pI891), (init pI891))) 891 17 false) = true := by
  decide +kernel
theorem I891_ok : RunOK pI891 891 (runFrom pI891 (fmask pI891) (cmask pI891) (hmask pI891) 1 890 (true, (init pI891), (init pI891))) ∧ intTest pI891 (runFrom pI891 (fmask pI891) (cmask pI891) (hmask pI891) 1 890 (true, (init pI891), (init pI891))) 891 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I891_fin) true) (by decide) rfl I891_fin intTest_fst
theorem link891 : linkOK pL891 pH891 pI891 = true := by decide +kernel
theorem cvx891 : ConvexBetweenHumps 891 :=
  cvx_of L891_ok H891_ok I891_ok link891 (by decide)

/-! ### `N = 892` -/

def pL892 : Prm := ⟨75, 35, 37, 894, 11, 18446744073709551616, 188989379249988544, 188989379249988544⟩
def pH892 : Prm := ⟨75, 35, 37, 894, 11, 18446744073709551616, 188991578273244096, 188991578273244096⟩
def pI892 : Prm := ⟨63, 31, 29, 894, 11, 18446744073709551616, 188989379249988544, 188991578273244096⟩
theorem L892_fin : (prmOK pL892 892 && ptTest pL892 (runFrom pL892 (fmask pL892) (cmask pL892) (hmask pL892) 1 891 (true, (init pL892), (init pL892))) 892 446 false) = true := by
  decide +kernel
theorem L892_ok : RunOK pL892 892 (runFrom pL892 (fmask pL892) (cmask pL892) (hmask pL892) 1 891 (true, (init pL892), (init pL892))) ∧ ptTest pL892 (runFrom pL892 (fmask pL892) (cmask pL892) (hmask pL892) 1 891 (true, (init pL892), (init pL892))) 892 446 false = true :=
  fin_run (runOK_init (prmOK_of_and L892_fin) true) (by decide) rfl L892_fin ptTest_fst
theorem H892_fin : (prmOK pH892 892 && ptTest pH892 (runFrom pH892 (fmask pH892) (cmask pH892) (hmask pH892) 1 891 (true, (init pH892), (init pH892))) 892 446 true) = true := by
  decide +kernel
theorem H892_ok : RunOK pH892 892 (runFrom pH892 (fmask pH892) (cmask pH892) (hmask pH892) 1 891 (true, (init pH892), (init pH892))) ∧ ptTest pH892 (runFrom pH892 (fmask pH892) (cmask pH892) (hmask pH892) 1 891 (true, (init pH892), (init pH892))) 892 446 true = true :=
  fin_run (runOK_init (prmOK_of_and H892_fin) true) (by decide) rfl H892_fin ptTest_fst
theorem I892_fin : (prmOK pI892 892 && intTest pI892 (runFrom pI892 (fmask pI892) (cmask pI892) (hmask pI892) 1 891 (true, (init pI892), (init pI892))) 892 17 true) = true := by
  decide +kernel
theorem I892_ok : RunOK pI892 892 (runFrom pI892 (fmask pI892) (cmask pI892) (hmask pI892) 1 891 (true, (init pI892), (init pI892))) ∧ intTest pI892 (runFrom pI892 (fmask pI892) (cmask pI892) (hmask pI892) 1 891 (true, (init pI892), (init pI892))) 892 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I892_fin) true) (by decide) rfl I892_fin intTest_fst
theorem link892 : linkOK pL892 pH892 pI892 = true := by decide +kernel
theorem cvx892 : ConvexBetweenHumps 892 :=
  cvx_of L892_ok H892_ok I892_ok link892 (by decide)
theorem cenlink892 : cenLinkOK pI892 892 = true := by decide +kernel
theorem cen892 : CenterUniqueMin 892 ∧ DipHyp 892 ∧ OnePointHyps 892 :=
  cen_of L892_ok H892_ok I892_ok link892 cenlink892

/-! ### `N = 893` -/

def pL893 : Prm := ⟨75, 35, 37, 895, 11, 18446744073709551616, 188821307662267725, 188821307662267725⟩
def pH893 : Prm := ⟨75, 35, 37, 895, 11, 18446744073709551616, 188823506685523277, 188823506685523277⟩
def pI893 : Prm := ⟨63, 31, 29, 895, 11, 18446744073709551616, 188821307662267725, 188823506685523277⟩
theorem L893_fin : (prmOK pL893 893 && ptTest pL893 (runFrom pL893 (fmask pL893) (cmask pL893) (hmask pL893) 1 892 (true, (init pL893), (init pL893))) 893 447 false) = true := by
  decide +kernel
theorem L893_ok : RunOK pL893 893 (runFrom pL893 (fmask pL893) (cmask pL893) (hmask pL893) 1 892 (true, (init pL893), (init pL893))) ∧ ptTest pL893 (runFrom pL893 (fmask pL893) (cmask pL893) (hmask pL893) 1 892 (true, (init pL893), (init pL893))) 893 447 false = true :=
  fin_run (runOK_init (prmOK_of_and L893_fin) true) (by decide) rfl L893_fin ptTest_fst
theorem H893_fin : (prmOK pH893 893 && ptTest pH893 (runFrom pH893 (fmask pH893) (cmask pH893) (hmask pH893) 1 892 (true, (init pH893), (init pH893))) 893 447 true) = true := by
  decide +kernel
theorem H893_ok : RunOK pH893 893 (runFrom pH893 (fmask pH893) (cmask pH893) (hmask pH893) 1 892 (true, (init pH893), (init pH893))) ∧ ptTest pH893 (runFrom pH893 (fmask pH893) (cmask pH893) (hmask pH893) 1 892 (true, (init pH893), (init pH893))) 893 447 true = true :=
  fin_run (runOK_init (prmOK_of_and H893_fin) true) (by decide) rfl H893_fin ptTest_fst
theorem I893_fin : (prmOK pI893 893 && intTest pI893 (runFrom pI893 (fmask pI893) (cmask pI893) (hmask pI893) 1 892 (true, (init pI893), (init pI893))) 893 17 false) = true := by
  decide +kernel
theorem I893_ok : RunOK pI893 893 (runFrom pI893 (fmask pI893) (cmask pI893) (hmask pI893) 1 892 (true, (init pI893), (init pI893))) ∧ intTest pI893 (runFrom pI893 (fmask pI893) (cmask pI893) (hmask pI893) 1 892 (true, (init pI893), (init pI893))) 893 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I893_fin) true) (by decide) rfl I893_fin intTest_fst
theorem link893 : linkOK pL893 pH893 pI893 = true := by decide +kernel
theorem cvx893 : ConvexBetweenHumps 893 :=
  cvx_of L893_ok H893_ok I893_ok link893 (by decide)

/-! ### `N = 894` -/

def pL894 : Prm := ⟨75, 35, 37, 896, 11, 18446744073709551616, 188653726480537129, 188653726480537129⟩
def pH894 : Prm := ⟨75, 35, 37, 896, 11, 18446744073709551616, 188655925503792681, 188655925503792681⟩
def pI894 : Prm := ⟨63, 31, 29, 896, 11, 18446744073709551616, 188653726480537129, 188655925503792681⟩
theorem L894_fin : (prmOK pL894 894 && ptTest pL894 (runFrom pL894 (fmask pL894) (cmask pL894) (hmask pL894) 1 893 (true, (init pL894), (init pL894))) 894 447 false) = true := by
  decide +kernel
theorem L894_ok : RunOK pL894 894 (runFrom pL894 (fmask pL894) (cmask pL894) (hmask pL894) 1 893 (true, (init pL894), (init pL894))) ∧ ptTest pL894 (runFrom pL894 (fmask pL894) (cmask pL894) (hmask pL894) 1 893 (true, (init pL894), (init pL894))) 894 447 false = true :=
  fin_run (runOK_init (prmOK_of_and L894_fin) true) (by decide) rfl L894_fin ptTest_fst
theorem H894_fin : (prmOK pH894 894 && ptTest pH894 (runFrom pH894 (fmask pH894) (cmask pH894) (hmask pH894) 1 893 (true, (init pH894), (init pH894))) 894 447 true) = true := by
  decide +kernel
theorem H894_ok : RunOK pH894 894 (runFrom pH894 (fmask pH894) (cmask pH894) (hmask pH894) 1 893 (true, (init pH894), (init pH894))) ∧ ptTest pH894 (runFrom pH894 (fmask pH894) (cmask pH894) (hmask pH894) 1 893 (true, (init pH894), (init pH894))) 894 447 true = true :=
  fin_run (runOK_init (prmOK_of_and H894_fin) true) (by decide) rfl H894_fin ptTest_fst
theorem I894_fin : (prmOK pI894 894 && intTest pI894 (runFrom pI894 (fmask pI894) (cmask pI894) (hmask pI894) 1 893 (true, (init pI894), (init pI894))) 894 17 true) = true := by
  decide +kernel
theorem I894_ok : RunOK pI894 894 (runFrom pI894 (fmask pI894) (cmask pI894) (hmask pI894) 1 893 (true, (init pI894), (init pI894))) ∧ intTest pI894 (runFrom pI894 (fmask pI894) (cmask pI894) (hmask pI894) 1 893 (true, (init pI894), (init pI894))) 894 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I894_fin) true) (by decide) rfl I894_fin intTest_fst
theorem link894 : linkOK pL894 pH894 pI894 = true := by decide +kernel
theorem cvx894 : ConvexBetweenHumps 894 :=
  cvx_of L894_ok H894_ok I894_ok link894 (by decide)
theorem cenlink894 : cenLinkOK pI894 894 = true := by decide +kernel
theorem cen894 : CenterUniqueMin 894 ∧ DipHyp 894 ∧ OnePointHyps 894 :=
  cen_of L894_ok H894_ok I894_ok link894 cenlink894

/-! ### `N = 895` -/

def pL895 : Prm := ⟨75, 35, 37, 897, 11, 18446744073709551616, 188486308634727171, 188486308634727171⟩
def pH895 : Prm := ⟨75, 35, 37, 897, 11, 18446744073709551616, 188488507657982723, 188488507657982723⟩
def pI895 : Prm := ⟨63, 31, 29, 897, 11, 18446744073709551616, 188486308634727171, 188488507657982723⟩
theorem L895_fin : (prmOK pL895 895 && ptTest pL895 (runFrom pL895 (fmask pL895) (cmask pL895) (hmask pL895) 1 894 (true, (init pL895), (init pL895))) 895 448 false) = true := by
  decide +kernel
theorem L895_ok : RunOK pL895 895 (runFrom pL895 (fmask pL895) (cmask pL895) (hmask pL895) 1 894 (true, (init pL895), (init pL895))) ∧ ptTest pL895 (runFrom pL895 (fmask pL895) (cmask pL895) (hmask pL895) 1 894 (true, (init pL895), (init pL895))) 895 448 false = true :=
  fin_run (runOK_init (prmOK_of_and L895_fin) true) (by decide) rfl L895_fin ptTest_fst
theorem H895_fin : (prmOK pH895 895 && ptTest pH895 (runFrom pH895 (fmask pH895) (cmask pH895) (hmask pH895) 1 894 (true, (init pH895), (init pH895))) 895 448 true) = true := by
  decide +kernel
theorem H895_ok : RunOK pH895 895 (runFrom pH895 (fmask pH895) (cmask pH895) (hmask pH895) 1 894 (true, (init pH895), (init pH895))) ∧ ptTest pH895 (runFrom pH895 (fmask pH895) (cmask pH895) (hmask pH895) 1 894 (true, (init pH895), (init pH895))) 895 448 true = true :=
  fin_run (runOK_init (prmOK_of_and H895_fin) true) (by decide) rfl H895_fin ptTest_fst
theorem I895_fin : (prmOK pI895 895 && intTest pI895 (runFrom pI895 (fmask pI895) (cmask pI895) (hmask pI895) 1 894 (true, (init pI895), (init pI895))) 895 17 false) = true := by
  decide +kernel
theorem I895_ok : RunOK pI895 895 (runFrom pI895 (fmask pI895) (cmask pI895) (hmask pI895) 1 894 (true, (init pI895), (init pI895))) ∧ intTest pI895 (runFrom pI895 (fmask pI895) (cmask pI895) (hmask pI895) 1 894 (true, (init pI895), (init pI895))) 895 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I895_fin) true) (by decide) rfl I895_fin intTest_fst
theorem link895 : linkOK pL895 pH895 pI895 = true := by decide +kernel
theorem cvx895 : ConvexBetweenHumps 895 :=
  cvx_of L895_ok H895_ok I895_ok link895 (by decide)

/-! ### `N = 896` -/

def pL896 : Prm := ⟨75, 35, 37, 898, 11, 18446744073709551616, 188319378110556487, 188319378110556487⟩
def pH896 : Prm := ⟨75, 35, 37, 898, 11, 18446744073709551616, 188321577133812039, 188321577133812039⟩
def pI896 : Prm := ⟨63, 31, 29, 898, 11, 18446744073709551616, 188319378110556487, 188321577133812039⟩
theorem L896_fin : (prmOK pL896 896 && ptTest pL896 (runFrom pL896 (fmask pL896) (cmask pL896) (hmask pL896) 1 895 (true, (init pL896), (init pL896))) 896 448 false) = true := by
  decide +kernel
theorem L896_ok : RunOK pL896 896 (runFrom pL896 (fmask pL896) (cmask pL896) (hmask pL896) 1 895 (true, (init pL896), (init pL896))) ∧ ptTest pL896 (runFrom pL896 (fmask pL896) (cmask pL896) (hmask pL896) 1 895 (true, (init pL896), (init pL896))) 896 448 false = true :=
  fin_run (runOK_init (prmOK_of_and L896_fin) true) (by decide) rfl L896_fin ptTest_fst
theorem H896_fin : (prmOK pH896 896 && ptTest pH896 (runFrom pH896 (fmask pH896) (cmask pH896) (hmask pH896) 1 895 (true, (init pH896), (init pH896))) 896 448 true) = true := by
  decide +kernel
theorem H896_ok : RunOK pH896 896 (runFrom pH896 (fmask pH896) (cmask pH896) (hmask pH896) 1 895 (true, (init pH896), (init pH896))) ∧ ptTest pH896 (runFrom pH896 (fmask pH896) (cmask pH896) (hmask pH896) 1 895 (true, (init pH896), (init pH896))) 896 448 true = true :=
  fin_run (runOK_init (prmOK_of_and H896_fin) true) (by decide) rfl H896_fin ptTest_fst
theorem I896_fin : (prmOK pI896 896 && intTest pI896 (runFrom pI896 (fmask pI896) (cmask pI896) (hmask pI896) 1 895 (true, (init pI896), (init pI896))) 896 17 true) = true := by
  decide +kernel
theorem I896_ok : RunOK pI896 896 (runFrom pI896 (fmask pI896) (cmask pI896) (hmask pI896) 1 895 (true, (init pI896), (init pI896))) ∧ intTest pI896 (runFrom pI896 (fmask pI896) (cmask pI896) (hmask pI896) 1 895 (true, (init pI896), (init pI896))) 896 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I896_fin) true) (by decide) rfl I896_fin intTest_fst
theorem link896 : linkOK pL896 pH896 pI896 = true := by decide +kernel
theorem cvx896 : ConvexBetweenHumps 896 :=
  cvx_of L896_ok H896_ok I896_ok link896 (by decide)
theorem cenlink896 : cenLinkOK pI896 896 = true := by decide +kernel
theorem cen896 : CenterUniqueMin 896 ∧ DipHyp 896 ∧ OnePointHyps 896 :=
  cen_of L896_ok H896_ok I896_ok link896 cenlink896

/-! ### `N = 897` -/

def pL897 : Prm := ⟨75, 35, 37, 899, 11, 18446744073709551616, 188152610065510517, 188152610065510517⟩
def pH897 : Prm := ⟨75, 35, 37, 899, 11, 18446744073709551616, 188154809088766069, 188154809088766069⟩
def pI897 : Prm := ⟨63, 31, 29, 899, 11, 18446744073709551616, 188152610065510517, 188154809088766069⟩
theorem L897_fin : (prmOK pL897 897 && ptTest pL897 (runFrom pL897 (fmask pL897) (cmask pL897) (hmask pL897) 1 896 (true, (init pL897), (init pL897))) 897 449 false) = true := by
  decide +kernel
theorem L897_ok : RunOK pL897 897 (runFrom pL897 (fmask pL897) (cmask pL897) (hmask pL897) 1 896 (true, (init pL897), (init pL897))) ∧ ptTest pL897 (runFrom pL897 (fmask pL897) (cmask pL897) (hmask pL897) 1 896 (true, (init pL897), (init pL897))) 897 449 false = true :=
  fin_run (runOK_init (prmOK_of_and L897_fin) true) (by decide) rfl L897_fin ptTest_fst
theorem H897_fin : (prmOK pH897 897 && ptTest pH897 (runFrom pH897 (fmask pH897) (cmask pH897) (hmask pH897) 1 896 (true, (init pH897), (init pH897))) 897 449 true) = true := by
  decide +kernel
theorem H897_ok : RunOK pH897 897 (runFrom pH897 (fmask pH897) (cmask pH897) (hmask pH897) 1 896 (true, (init pH897), (init pH897))) ∧ ptTest pH897 (runFrom pH897 (fmask pH897) (cmask pH897) (hmask pH897) 1 896 (true, (init pH897), (init pH897))) 897 449 true = true :=
  fin_run (runOK_init (prmOK_of_and H897_fin) true) (by decide) rfl H897_fin ptTest_fst
theorem I897_fin : (prmOK pI897 897 && intTest pI897 (runFrom pI897 (fmask pI897) (cmask pI897) (hmask pI897) 1 896 (true, (init pI897), (init pI897))) 897 17 false) = true := by
  decide +kernel
theorem I897_ok : RunOK pI897 897 (runFrom pI897 (fmask pI897) (cmask pI897) (hmask pI897) 1 896 (true, (init pI897), (init pI897))) ∧ intTest pI897 (runFrom pI897 (fmask pI897) (cmask pI897) (hmask pI897) 1 896 (true, (init pI897), (init pI897))) 897 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I897_fin) true) (by decide) rfl I897_fin intTest_fst
theorem link897 : linkOK pL897 pH897 pI897 = true := by decide +kernel
theorem cvx897 : ConvexBetweenHumps 897 :=
  cvx_of L897_ok H897_ok I897_ok link897 (by decide)

/-! ### `N = 898` -/

def pL898 : Prm := ⟨75, 35, 37, 900, 11, 18446744073709551616, 187986326283891910, 187986326283891910⟩
def pH898 : Prm := ⟨75, 35, 37, 900, 11, 18446744073709551616, 187988525307147462, 187988525307147462⟩
def pI898 : Prm := ⟨63, 31, 29, 900, 11, 18446744073709551616, 187986326283891910, 187988525307147462⟩
theorem L898_fin : (prmOK pL898 898 && ptTest pL898 (runFrom pL898 (fmask pL898) (cmask pL898) (hmask pL898) 1 897 (true, (init pL898), (init pL898))) 898 449 false) = true := by
  decide +kernel
theorem L898_ok : RunOK pL898 898 (runFrom pL898 (fmask pL898) (cmask pL898) (hmask pL898) 1 897 (true, (init pL898), (init pL898))) ∧ ptTest pL898 (runFrom pL898 (fmask pL898) (cmask pL898) (hmask pL898) 1 897 (true, (init pL898), (init pL898))) 898 449 false = true :=
  fin_run (runOK_init (prmOK_of_and L898_fin) true) (by decide) rfl L898_fin ptTest_fst
theorem H898_fin : (prmOK pH898 898 && ptTest pH898 (runFrom pH898 (fmask pH898) (cmask pH898) (hmask pH898) 1 897 (true, (init pH898), (init pH898))) 898 449 true) = true := by
  decide +kernel
theorem H898_ok : RunOK pH898 898 (runFrom pH898 (fmask pH898) (cmask pH898) (hmask pH898) 1 897 (true, (init pH898), (init pH898))) ∧ ptTest pH898 (runFrom pH898 (fmask pH898) (cmask pH898) (hmask pH898) 1 897 (true, (init pH898), (init pH898))) 898 449 true = true :=
  fin_run (runOK_init (prmOK_of_and H898_fin) true) (by decide) rfl H898_fin ptTest_fst
theorem I898_fin : (prmOK pI898 898 && intTest pI898 (runFrom pI898 (fmask pI898) (cmask pI898) (hmask pI898) 1 897 (true, (init pI898), (init pI898))) 898 17 true) = true := by
  decide +kernel
theorem I898_ok : RunOK pI898 898 (runFrom pI898 (fmask pI898) (cmask pI898) (hmask pI898) 1 897 (true, (init pI898), (init pI898))) ∧ intTest pI898 (runFrom pI898 (fmask pI898) (cmask pI898) (hmask pI898) 1 897 (true, (init pI898), (init pI898))) 898 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I898_fin) true) (by decide) rfl I898_fin intTest_fst
theorem link898 : linkOK pL898 pH898 pI898 = true := by decide +kernel
theorem cvx898 : ConvexBetweenHumps 898 :=
  cvx_of L898_ok H898_ok I898_ok link898 (by decide)
theorem cenlink898 : cenLinkOK pI898 898 = true := by decide +kernel
theorem cen898 : CenterUniqueMin 898 ∧ DipHyp 898 ∧ OnePointHyps 898 :=
  cen_of L898_ok H898_ok I898_ok link898 cenlink898

/-! ### `N = 899` -/

def pL899 : Prm := ⟨75, 35, 37, 901, 11, 18446744073709551616, 187820204130671074, 187820204130671074⟩
def pH899 : Prm := ⟨75, 35, 37, 901, 11, 18446744073709551616, 187822403153926626, 187822403153926626⟩
def pI899 : Prm := ⟨63, 31, 29, 901, 11, 18446744073709551616, 187820204130671074, 187822403153926626⟩
theorem L899_fin : (prmOK pL899 899 && ptTest pL899 (runFrom pL899 (fmask pL899) (cmask pL899) (hmask pL899) 1 898 (true, (init pL899), (init pL899))) 899 450 false) = true := by
  decide +kernel
theorem L899_ok : RunOK pL899 899 (runFrom pL899 (fmask pL899) (cmask pL899) (hmask pL899) 1 898 (true, (init pL899), (init pL899))) ∧ ptTest pL899 (runFrom pL899 (fmask pL899) (cmask pL899) (hmask pL899) 1 898 (true, (init pL899), (init pL899))) 899 450 false = true :=
  fin_run (runOK_init (prmOK_of_and L899_fin) true) (by decide) rfl L899_fin ptTest_fst
theorem H899_fin : (prmOK pH899 899 && ptTest pH899 (runFrom pH899 (fmask pH899) (cmask pH899) (hmask pH899) 1 898 (true, (init pH899), (init pH899))) 899 450 true) = true := by
  decide +kernel
theorem H899_ok : RunOK pH899 899 (runFrom pH899 (fmask pH899) (cmask pH899) (hmask pH899) 1 898 (true, (init pH899), (init pH899))) ∧ ptTest pH899 (runFrom pH899 (fmask pH899) (cmask pH899) (hmask pH899) 1 898 (true, (init pH899), (init pH899))) 899 450 true = true :=
  fin_run (runOK_init (prmOK_of_and H899_fin) true) (by decide) rfl H899_fin ptTest_fst
theorem I899_fin : (prmOK pI899 899 && intTest pI899 (runFrom pI899 (fmask pI899) (cmask pI899) (hmask pI899) 1 898 (true, (init pI899), (init pI899))) 899 17 false) = true := by
  decide +kernel
theorem I899_ok : RunOK pI899 899 (runFrom pI899 (fmask pI899) (cmask pI899) (hmask pI899) 1 898 (true, (init pI899), (init pI899))) ∧ intTest pI899 (runFrom pI899 (fmask pI899) (cmask pI899) (hmask pI899) 1 898 (true, (init pI899), (init pI899))) 899 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I899_fin) true) (by decide) rfl I899_fin intTest_fst
theorem link899 : linkOK pL899 pH899 pI899 = true := by decide +kernel
theorem cvx899 : ConvexBetweenHumps 899 :=
  cvx_of L899_ok H899_ok I899_ok link899 (by decide)

/-! ### `N = 900` -/

def pL900 : Prm := ⟨75, 35, 37, 902, 11, 18446744073709551616, 187654563208564915, 187654563208564915⟩
def pH900 : Prm := ⟨75, 35, 37, 902, 11, 18446744073709551616, 187656762231820467, 187656762231820467⟩
def pI900 : Prm := ⟨63, 31, 29, 902, 11, 18446744073709551616, 187654563208564915, 187656762231820467⟩
theorem L900_fin : (prmOK pL900 900 && ptTest pL900 (runFrom pL900 (fmask pL900) (cmask pL900) (hmask pL900) 1 899 (true, (init pL900), (init pL900))) 900 450 false) = true := by
  decide +kernel
theorem L900_ok : RunOK pL900 900 (runFrom pL900 (fmask pL900) (cmask pL900) (hmask pL900) 1 899 (true, (init pL900), (init pL900))) ∧ ptTest pL900 (runFrom pL900 (fmask pL900) (cmask pL900) (hmask pL900) 1 899 (true, (init pL900), (init pL900))) 900 450 false = true :=
  fin_run (runOK_init (prmOK_of_and L900_fin) true) (by decide) rfl L900_fin ptTest_fst
theorem H900_fin : (prmOK pH900 900 && ptTest pH900 (runFrom pH900 (fmask pH900) (cmask pH900) (hmask pH900) 1 899 (true, (init pH900), (init pH900))) 900 450 true) = true := by
  decide +kernel
theorem H900_ok : RunOK pH900 900 (runFrom pH900 (fmask pH900) (cmask pH900) (hmask pH900) 1 899 (true, (init pH900), (init pH900))) ∧ ptTest pH900 (runFrom pH900 (fmask pH900) (cmask pH900) (hmask pH900) 1 899 (true, (init pH900), (init pH900))) 900 450 true = true :=
  fin_run (runOK_init (prmOK_of_and H900_fin) true) (by decide) rfl H900_fin ptTest_fst
theorem I900_fin : (prmOK pI900 900 && intTest pI900 (runFrom pI900 (fmask pI900) (cmask pI900) (hmask pI900) 1 899 (true, (init pI900), (init pI900))) 900 17 true) = true := by
  decide +kernel
theorem I900_ok : RunOK pI900 900 (runFrom pI900 (fmask pI900) (cmask pI900) (hmask pI900) 1 899 (true, (init pI900), (init pI900))) ∧ intTest pI900 (runFrom pI900 (fmask pI900) (cmask pI900) (hmask pI900) 1 899 (true, (init pI900), (init pI900))) 900 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I900_fin) true) (by decide) rfl I900_fin intTest_fst
theorem link900 : linkOK pL900 pH900 pI900 = true := by decide +kernel
theorem cvx900 : ConvexBetweenHumps 900 :=
  cvx_of L900_ok H900_ok I900_ok link900 (by decide)
theorem cenlink900 : cenLinkOK pI900 900 = true := by decide +kernel
theorem cen900 : CenterUniqueMin 900 ∧ DipHyp 900 ∧ OnePointHyps 900 :=
  cen_of L900_ok H900_ok I900_ok link900 cenlink900

/-! ### `N = 901` -/

def pL901 : Prm := ⟨75, 35, 37, 903, 11, 18446744073709551616, 187489083070124776, 187489083070124776⟩
def pH901 : Prm := ⟨75, 35, 37, 903, 11, 18446744073709551616, 187491282093380328, 187491282093380328⟩
def pI901 : Prm := ⟨63, 31, 29, 903, 11, 18446744073709551616, 187489083070124776, 187491282093380328⟩
theorem L901_fin : (prmOK pL901 901 && ptTest pL901 (runFrom pL901 (fmask pL901) (cmask pL901) (hmask pL901) 1 900 (true, (init pL901), (init pL901))) 901 451 false) = true := by
  decide +kernel
theorem L901_ok : RunOK pL901 901 (runFrom pL901 (fmask pL901) (cmask pL901) (hmask pL901) 1 900 (true, (init pL901), (init pL901))) ∧ ptTest pL901 (runFrom pL901 (fmask pL901) (cmask pL901) (hmask pL901) 1 900 (true, (init pL901), (init pL901))) 901 451 false = true :=
  fin_run (runOK_init (prmOK_of_and L901_fin) true) (by decide) rfl L901_fin ptTest_fst
theorem H901_fin : (prmOK pH901 901 && ptTest pH901 (runFrom pH901 (fmask pH901) (cmask pH901) (hmask pH901) 1 900 (true, (init pH901), (init pH901))) 901 451 true) = true := by
  decide +kernel
theorem H901_ok : RunOK pH901 901 (runFrom pH901 (fmask pH901) (cmask pH901) (hmask pH901) 1 900 (true, (init pH901), (init pH901))) ∧ ptTest pH901 (runFrom pH901 (fmask pH901) (cmask pH901) (hmask pH901) 1 900 (true, (init pH901), (init pH901))) 901 451 true = true :=
  fin_run (runOK_init (prmOK_of_and H901_fin) true) (by decide) rfl H901_fin ptTest_fst
theorem I901_fin : (prmOK pI901 901 && intTest pI901 (runFrom pI901 (fmask pI901) (cmask pI901) (hmask pI901) 1 900 (true, (init pI901), (init pI901))) 901 17 false) = true := by
  decide +kernel
theorem I901_ok : RunOK pI901 901 (runFrom pI901 (fmask pI901) (cmask pI901) (hmask pI901) 1 900 (true, (init pI901), (init pI901))) ∧ intTest pI901 (runFrom pI901 (fmask pI901) (cmask pI901) (hmask pI901) 1 900 (true, (init pI901), (init pI901))) 901 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I901_fin) true) (by decide) rfl I901_fin intTest_fst
theorem link901 : linkOK pL901 pH901 pI901 = true := by decide +kernel
theorem cvx901 : ConvexBetweenHumps 901 :=
  cvx_of L901_ok H901_ok I901_ok link901 (by decide)

/-! ### `N = 902` -/

def pL902 : Prm := ⟨75, 35, 37, 904, 11, 18446744073709551616, 187324081156072264, 187324081156072264⟩
def pH902 : Prm := ⟨75, 35, 37, 904, 11, 18446744073709551616, 187326280179327816, 187326280179327816⟩
def pI902 : Prm := ⟨64, 31, 30, 904, 11, 18446744073709551616, 187324081156072264, 187326280179327816⟩
theorem L902_fin : (prmOK pL902 902 && ptTest pL902 (runFrom pL902 (fmask pL902) (cmask pL902) (hmask pL902) 1 901 (true, (init pL902), (init pL902))) 902 451 false) = true := by
  decide +kernel
theorem L902_ok : RunOK pL902 902 (runFrom pL902 (fmask pL902) (cmask pL902) (hmask pL902) 1 901 (true, (init pL902), (init pL902))) ∧ ptTest pL902 (runFrom pL902 (fmask pL902) (cmask pL902) (hmask pL902) 1 901 (true, (init pL902), (init pL902))) 902 451 false = true :=
  fin_run (runOK_init (prmOK_of_and L902_fin) true) (by decide) rfl L902_fin ptTest_fst
theorem H902_fin : (prmOK pH902 902 && ptTest pH902 (runFrom pH902 (fmask pH902) (cmask pH902) (hmask pH902) 1 901 (true, (init pH902), (init pH902))) 902 451 true) = true := by
  decide +kernel
theorem H902_ok : RunOK pH902 902 (runFrom pH902 (fmask pH902) (cmask pH902) (hmask pH902) 1 901 (true, (init pH902), (init pH902))) ∧ ptTest pH902 (runFrom pH902 (fmask pH902) (cmask pH902) (hmask pH902) 1 901 (true, (init pH902), (init pH902))) 902 451 true = true :=
  fin_run (runOK_init (prmOK_of_and H902_fin) true) (by decide) rfl H902_fin ptTest_fst
theorem I902_fin : (prmOK pI902 902 && intTest pI902 (runFrom pI902 (fmask pI902) (cmask pI902) (hmask pI902) 1 901 (true, (init pI902), (init pI902))) 902 17 true) = true := by
  decide +kernel
theorem I902_ok : RunOK pI902 902 (runFrom pI902 (fmask pI902) (cmask pI902) (hmask pI902) 1 901 (true, (init pI902), (init pI902))) ∧ intTest pI902 (runFrom pI902 (fmask pI902) (cmask pI902) (hmask pI902) 1 901 (true, (init pI902), (init pI902))) 902 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I902_fin) true) (by decide) rfl I902_fin intTest_fst
theorem link902 : linkOK pL902 pH902 pI902 = true := by decide +kernel
theorem cvx902 : ConvexBetweenHumps 902 :=
  cvx_of L902_ok H902_ok I902_ok link902 (by decide)
theorem cenlink902 : cenLinkOK pI902 902 = true := by decide +kernel
theorem cen902 : CenterUniqueMin 902 ∧ DipHyp 902 ∧ OnePointHyps 902 :=
  cen_of L902_ok H902_ok I902_ok link902 cenlink902

/-! ### `N = 903` -/

def pL903 : Prm := ⟨75, 35, 37, 905, 11, 18446744073709551616, 187159239186912320, 187159239186912320⟩
def pH903 : Prm := ⟨75, 35, 37, 905, 11, 18446744073709551616, 187161438210167872, 187161438210167872⟩
def pI903 : Prm := ⟨63, 31, 29, 905, 11, 18446744073709551616, 187159239186912320, 187161438210167872⟩
theorem L903_fin : (prmOK pL903 903 && ptTest pL903 (runFrom pL903 (fmask pL903) (cmask pL903) (hmask pL903) 1 902 (true, (init pL903), (init pL903))) 903 452 false) = true := by
  decide +kernel
theorem L903_ok : RunOK pL903 903 (runFrom pL903 (fmask pL903) (cmask pL903) (hmask pL903) 1 902 (true, (init pL903), (init pL903))) ∧ ptTest pL903 (runFrom pL903 (fmask pL903) (cmask pL903) (hmask pL903) 1 902 (true, (init pL903), (init pL903))) 903 452 false = true :=
  fin_run (runOK_init (prmOK_of_and L903_fin) true) (by decide) rfl L903_fin ptTest_fst
theorem H903_fin : (prmOK pH903 903 && ptTest pH903 (runFrom pH903 (fmask pH903) (cmask pH903) (hmask pH903) 1 902 (true, (init pH903), (init pH903))) 903 452 true) = true := by
  decide +kernel
theorem H903_ok : RunOK pH903 903 (runFrom pH903 (fmask pH903) (cmask pH903) (hmask pH903) 1 902 (true, (init pH903), (init pH903))) ∧ ptTest pH903 (runFrom pH903 (fmask pH903) (cmask pH903) (hmask pH903) 1 902 (true, (init pH903), (init pH903))) 903 452 true = true :=
  fin_run (runOK_init (prmOK_of_and H903_fin) true) (by decide) rfl H903_fin ptTest_fst
theorem I903_fin : (prmOK pI903 903 && intTest pI903 (runFrom pI903 (fmask pI903) (cmask pI903) (hmask pI903) 1 902 (true, (init pI903), (init pI903))) 903 17 false) = true := by
  decide +kernel
theorem I903_ok : RunOK pI903 903 (runFrom pI903 (fmask pI903) (cmask pI903) (hmask pI903) 1 902 (true, (init pI903), (init pI903))) ∧ intTest pI903 (runFrom pI903 (fmask pI903) (cmask pI903) (hmask pI903) 1 902 (true, (init pI903), (init pI903))) 903 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I903_fin) true) (by decide) rfl I903_fin intTest_fst
theorem link903 : linkOK pL903 pH903 pI903 = true := by decide +kernel
theorem cvx903 : ConvexBetweenHumps 903 :=
  cvx_of L903_ok H903_ok I903_ok link903 (by decide)

/-! ### `N = 904` -/

def pL904 : Prm := ⟨75, 35, 37, 906, 11, 18446744073709551616, 186994872460740332, 186994872460740332⟩
def pH904 : Prm := ⟨75, 35, 37, 906, 11, 18446744073709551616, 186997071483995884, 186997071483995884⟩
def pI904 : Prm := ⟨64, 31, 30, 906, 11, 18446744073709551616, 186994872460740332, 186997071483995884⟩
theorem L904_fin : (prmOK pL904 904 && ptTest pL904 (runFrom pL904 (fmask pL904) (cmask pL904) (hmask pL904) 1 903 (true, (init pL904), (init pL904))) 904 452 false) = true := by
  decide +kernel
theorem L904_ok : RunOK pL904 904 (runFrom pL904 (fmask pL904) (cmask pL904) (hmask pL904) 1 903 (true, (init pL904), (init pL904))) ∧ ptTest pL904 (runFrom pL904 (fmask pL904) (cmask pL904) (hmask pL904) 1 903 (true, (init pL904), (init pL904))) 904 452 false = true :=
  fin_run (runOK_init (prmOK_of_and L904_fin) true) (by decide) rfl L904_fin ptTest_fst
theorem H904_fin : (prmOK pH904 904 && ptTest pH904 (runFrom pH904 (fmask pH904) (cmask pH904) (hmask pH904) 1 903 (true, (init pH904), (init pH904))) 904 452 true) = true := by
  decide +kernel
theorem H904_ok : RunOK pH904 904 (runFrom pH904 (fmask pH904) (cmask pH904) (hmask pH904) 1 903 (true, (init pH904), (init pH904))) ∧ ptTest pH904 (runFrom pH904 (fmask pH904) (cmask pH904) (hmask pH904) 1 903 (true, (init pH904), (init pH904))) 904 452 true = true :=
  fin_run (runOK_init (prmOK_of_and H904_fin) true) (by decide) rfl H904_fin ptTest_fst
theorem I904_fin : (prmOK pI904 904 && intTest pI904 (runFrom pI904 (fmask pI904) (cmask pI904) (hmask pI904) 1 903 (true, (init pI904), (init pI904))) 904 17 true) = true := by
  decide +kernel
theorem I904_ok : RunOK pI904 904 (runFrom pI904 (fmask pI904) (cmask pI904) (hmask pI904) 1 903 (true, (init pI904), (init pI904))) ∧ intTest pI904 (runFrom pI904 (fmask pI904) (cmask pI904) (hmask pI904) 1 903 (true, (init pI904), (init pI904))) 904 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I904_fin) true) (by decide) rfl I904_fin intTest_fst
theorem link904 : linkOK pL904 pH904 pI904 = true := by decide +kernel
theorem cvx904 : ConvexBetweenHumps 904 :=
  cvx_of L904_ok H904_ok I904_ok link904 (by decide)
theorem cenlink904 : cenLinkOK pI904 904 = true := by decide +kernel
theorem cen904 : CenterUniqueMin 904 ∧ DipHyp 904 ∧ OnePointHyps 904 :=
  cen_of L904_ok H904_ok I904_ok link904 cenlink904

/-! ### `N = 905` -/

def pL905 : Prm := ⟨75, 35, 37, 907, 11, 18446744073709551616, 186830664846590416, 186830664846590416⟩
def pH905 : Prm := ⟨75, 35, 37, 907, 11, 18446744073709551616, 186832863869845968, 186832863869845968⟩
def pI905 : Prm := ⟨64, 31, 30, 907, 11, 18446744073709551616, 186830664846590416, 186832863869845968⟩
theorem L905_fin : (prmOK pL905 905 && ptTest pL905 (runFrom pL905 (fmask pL905) (cmask pL905) (hmask pL905) 1 904 (true, (init pL905), (init pL905))) 905 453 false) = true := by
  decide +kernel
theorem L905_ok : RunOK pL905 905 (runFrom pL905 (fmask pL905) (cmask pL905) (hmask pL905) 1 904 (true, (init pL905), (init pL905))) ∧ ptTest pL905 (runFrom pL905 (fmask pL905) (cmask pL905) (hmask pL905) 1 904 (true, (init pL905), (init pL905))) 905 453 false = true :=
  fin_run (runOK_init (prmOK_of_and L905_fin) true) (by decide) rfl L905_fin ptTest_fst
theorem H905_fin : (prmOK pH905 905 && ptTest pH905 (runFrom pH905 (fmask pH905) (cmask pH905) (hmask pH905) 1 904 (true, (init pH905), (init pH905))) 905 453 true) = true := by
  decide +kernel
theorem H905_ok : RunOK pH905 905 (runFrom pH905 (fmask pH905) (cmask pH905) (hmask pH905) 1 904 (true, (init pH905), (init pH905))) ∧ ptTest pH905 (runFrom pH905 (fmask pH905) (cmask pH905) (hmask pH905) 1 904 (true, (init pH905), (init pH905))) 905 453 true = true :=
  fin_run (runOK_init (prmOK_of_and H905_fin) true) (by decide) rfl H905_fin ptTest_fst
theorem I905_fin : (prmOK pI905 905 && intTest pI905 (runFrom pI905 (fmask pI905) (cmask pI905) (hmask pI905) 1 904 (true, (init pI905), (init pI905))) 905 17 false) = true := by
  decide +kernel
theorem I905_ok : RunOK pI905 905 (runFrom pI905 (fmask pI905) (cmask pI905) (hmask pI905) 1 904 (true, (init pI905), (init pI905))) ∧ intTest pI905 (runFrom pI905 (fmask pI905) (cmask pI905) (hmask pI905) 1 904 (true, (init pI905), (init pI905))) 905 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I905_fin) true) (by decide) rfl I905_fin intTest_fst
theorem link905 : linkOK pL905 pH905 pI905 = true := by decide +kernel
theorem cvx905 : ConvexBetweenHumps 905 :=
  cvx_of L905_ok H905_ok I905_ok link905 (by decide)

/-! ### `N = 906` -/

def pL906 : Prm := ⟨75, 35, 37, 908, 11, 18446744073709551616, 186666929519134804, 186666929519134804⟩
def pH906 : Prm := ⟨75, 35, 37, 908, 11, 18446744073709551616, 186669128542390356, 186669128542390356⟩
def pI906 : Prm := ⟨64, 31, 30, 908, 11, 18446744073709551616, 186666929519134804, 186669128542390356⟩
theorem L906_fin : (prmOK pL906 906 && ptTest pL906 (runFrom pL906 (fmask pL906) (cmask pL906) (hmask pL906) 1 905 (true, (init pL906), (init pL906))) 906 453 false) = true := by
  decide +kernel
theorem L906_ok : RunOK pL906 906 (runFrom pL906 (fmask pL906) (cmask pL906) (hmask pL906) 1 905 (true, (init pL906), (init pL906))) ∧ ptTest pL906 (runFrom pL906 (fmask pL906) (cmask pL906) (hmask pL906) 1 905 (true, (init pL906), (init pL906))) 906 453 false = true :=
  fin_run (runOK_init (prmOK_of_and L906_fin) true) (by decide) rfl L906_fin ptTest_fst
theorem H906_fin : (prmOK pH906 906 && ptTest pH906 (runFrom pH906 (fmask pH906) (cmask pH906) (hmask pH906) 1 905 (true, (init pH906), (init pH906))) 906 453 true) = true := by
  decide +kernel
theorem H906_ok : RunOK pH906 906 (runFrom pH906 (fmask pH906) (cmask pH906) (hmask pH906) 1 905 (true, (init pH906), (init pH906))) ∧ ptTest pH906 (runFrom pH906 (fmask pH906) (cmask pH906) (hmask pH906) 1 905 (true, (init pH906), (init pH906))) 906 453 true = true :=
  fin_run (runOK_init (prmOK_of_and H906_fin) true) (by decide) rfl H906_fin ptTest_fst
theorem I906_fin : (prmOK pI906 906 && intTest pI906 (runFrom pI906 (fmask pI906) (cmask pI906) (hmask pI906) 1 905 (true, (init pI906), (init pI906))) 906 17 true) = true := by
  decide +kernel
theorem I906_ok : RunOK pI906 906 (runFrom pI906 (fmask pI906) (cmask pI906) (hmask pI906) 1 905 (true, (init pI906), (init pI906))) ∧ intTest pI906 (runFrom pI906 (fmask pI906) (cmask pI906) (hmask pI906) 1 905 (true, (init pI906), (init pI906))) 906 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I906_fin) true) (by decide) rfl I906_fin intTest_fst
theorem link906 : linkOK pL906 pH906 pI906 = true := by decide +kernel
theorem cvx906 : ConvexBetweenHumps 906 :=
  cvx_of L906_ok H906_ok I906_ok link906 (by decide)
theorem cenlink906 : cenLinkOK pI906 906 = true := by decide +kernel
theorem cen906 : CenterUniqueMin 906 ∧ DipHyp 906 ∧ OnePointHyps 906 :=
  cen_of L906_ok H906_ok I906_ok link906 cenlink906

/-! ### `N = 907` -/

def pL907 : Prm := ⟨75, 35, 37, 909, 11, 18446744073709551616, 186503352476641494, 186503352476641494⟩
def pH907 : Prm := ⟨75, 35, 37, 909, 11, 18446744073709551616, 186505551499897046, 186505551499897046⟩
def pI907 : Prm := ⟨64, 31, 30, 909, 11, 18446744073709551616, 186503352476641494, 186505551499897046⟩
theorem L907_fin : (prmOK pL907 907 && ptTest pL907 (runFrom pL907 (fmask pL907) (cmask pL907) (hmask pL907) 1 906 (true, (init pL907), (init pL907))) 907 454 false) = true := by
  decide +kernel
theorem L907_ok : RunOK pL907 907 (runFrom pL907 (fmask pL907) (cmask pL907) (hmask pL907) 1 906 (true, (init pL907), (init pL907))) ∧ ptTest pL907 (runFrom pL907 (fmask pL907) (cmask pL907) (hmask pL907) 1 906 (true, (init pL907), (init pL907))) 907 454 false = true :=
  fin_run (runOK_init (prmOK_of_and L907_fin) true) (by decide) rfl L907_fin ptTest_fst
theorem H907_fin : (prmOK pH907 907 && ptTest pH907 (runFrom pH907 (fmask pH907) (cmask pH907) (hmask pH907) 1 906 (true, (init pH907), (init pH907))) 907 454 true) = true := by
  decide +kernel
theorem H907_ok : RunOK pH907 907 (runFrom pH907 (fmask pH907) (cmask pH907) (hmask pH907) 1 906 (true, (init pH907), (init pH907))) ∧ ptTest pH907 (runFrom pH907 (fmask pH907) (cmask pH907) (hmask pH907) 1 906 (true, (init pH907), (init pH907))) 907 454 true = true :=
  fin_run (runOK_init (prmOK_of_and H907_fin) true) (by decide) rfl H907_fin ptTest_fst
theorem I907_fin : (prmOK pI907 907 && intTest pI907 (runFrom pI907 (fmask pI907) (cmask pI907) (hmask pI907) 1 906 (true, (init pI907), (init pI907))) 907 17 false) = true := by
  decide +kernel
theorem I907_ok : RunOK pI907 907 (runFrom pI907 (fmask pI907) (cmask pI907) (hmask pI907) 1 906 (true, (init pI907), (init pI907))) ∧ intTest pI907 (runFrom pI907 (fmask pI907) (cmask pI907) (hmask pI907) 1 906 (true, (init pI907), (init pI907))) 907 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I907_fin) true) (by decide) rfl I907_fin intTest_fst
theorem link907 : linkOK pL907 pH907 pI907 = true := by decide +kernel
theorem cvx907 : ConvexBetweenHumps 907 :=
  cvx_of L907_ok H907_ok I907_ok link907 (by decide)

/-! ### `N = 908` -/

def pL908 : Prm := ⟨75, 35, 37, 910, 11, 18446744073709551616, 186340244789322814, 186340244789322814⟩
def pH908 : Prm := ⟨75, 35, 37, 910, 11, 18446744073709551616, 186342443812578366, 186342443812578366⟩
def pI908 : Prm := ⟨64, 31, 30, 910, 11, 18446744073709551616, 186340244789322814, 186342443812578366⟩
theorem L908_fin : (prmOK pL908 908 && ptTest pL908 (runFrom pL908 (fmask pL908) (cmask pL908) (hmask pL908) 1 907 (true, (init pL908), (init pL908))) 908 454 false) = true := by
  decide +kernel
theorem L908_ok : RunOK pL908 908 (runFrom pL908 (fmask pL908) (cmask pL908) (hmask pL908) 1 907 (true, (init pL908), (init pL908))) ∧ ptTest pL908 (runFrom pL908 (fmask pL908) (cmask pL908) (hmask pL908) 1 907 (true, (init pL908), (init pL908))) 908 454 false = true :=
  fin_run (runOK_init (prmOK_of_and L908_fin) true) (by decide) rfl L908_fin ptTest_fst
theorem H908_fin : (prmOK pH908 908 && ptTest pH908 (runFrom pH908 (fmask pH908) (cmask pH908) (hmask pH908) 1 907 (true, (init pH908), (init pH908))) 908 454 true) = true := by
  decide +kernel
theorem H908_ok : RunOK pH908 908 (runFrom pH908 (fmask pH908) (cmask pH908) (hmask pH908) 1 907 (true, (init pH908), (init pH908))) ∧ ptTest pH908 (runFrom pH908 (fmask pH908) (cmask pH908) (hmask pH908) 1 907 (true, (init pH908), (init pH908))) 908 454 true = true :=
  fin_run (runOK_init (prmOK_of_and H908_fin) true) (by decide) rfl H908_fin ptTest_fst
theorem I908_fin : (prmOK pI908 908 && intTest pI908 (runFrom pI908 (fmask pI908) (cmask pI908) (hmask pI908) 1 907 (true, (init pI908), (init pI908))) 908 17 true) = true := by
  decide +kernel
theorem I908_ok : RunOK pI908 908 (runFrom pI908 (fmask pI908) (cmask pI908) (hmask pI908) 1 907 (true, (init pI908), (init pI908))) ∧ intTest pI908 (runFrom pI908 (fmask pI908) (cmask pI908) (hmask pI908) 1 907 (true, (init pI908), (init pI908))) 908 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I908_fin) true) (by decide) rfl I908_fin intTest_fst
theorem link908 : linkOK pL908 pH908 pI908 = true := by decide +kernel
theorem cvx908 : ConvexBetweenHumps 908 :=
  cvx_of L908_ok H908_ok I908_ok link908 (by decide)
theorem cenlink908 : cenLinkOK pI908 908 = true := by decide +kernel
theorem cen908 : CenterUniqueMin 908 ∧ DipHyp 908 ∧ OnePointHyps 908 :=
  cen_of L908_ok H908_ok I908_ok link908 cenlink908

/-! ### `N = 909` -/

def pL909 : Prm := ⟨75, 35, 37, 911, 11, 18446744073709551616, 186177294565735836, 186177294565735836⟩
def pH909 : Prm := ⟨75, 35, 37, 911, 11, 18446744073709551616, 186179493588991388, 186179493588991388⟩
def pI909 : Prm := ⟨64, 31, 30, 911, 11, 18446744073709551616, 186177294565735836, 186179493588991388⟩
theorem L909_fin : (prmOK pL909 909 && ptTest pL909 (runFrom pL909 (fmask pL909) (cmask pL909) (hmask pL909) 1 908 (true, (init pL909), (init pL909))) 909 455 false) = true := by
  decide +kernel
theorem L909_ok : RunOK pL909 909 (runFrom pL909 (fmask pL909) (cmask pL909) (hmask pL909) 1 908 (true, (init pL909), (init pL909))) ∧ ptTest pL909 (runFrom pL909 (fmask pL909) (cmask pL909) (hmask pL909) 1 908 (true, (init pL909), (init pL909))) 909 455 false = true :=
  fin_run (runOK_init (prmOK_of_and L909_fin) true) (by decide) rfl L909_fin ptTest_fst
theorem H909_fin : (prmOK pH909 909 && ptTest pH909 (runFrom pH909 (fmask pH909) (cmask pH909) (hmask pH909) 1 908 (true, (init pH909), (init pH909))) 909 455 true) = true := by
  decide +kernel
theorem H909_ok : RunOK pH909 909 (runFrom pH909 (fmask pH909) (cmask pH909) (hmask pH909) 1 908 (true, (init pH909), (init pH909))) ∧ ptTest pH909 (runFrom pH909 (fmask pH909) (cmask pH909) (hmask pH909) 1 908 (true, (init pH909), (init pH909))) 909 455 true = true :=
  fin_run (runOK_init (prmOK_of_and H909_fin) true) (by decide) rfl H909_fin ptTest_fst
theorem I909_fin : (prmOK pI909 909 && intTest pI909 (runFrom pI909 (fmask pI909) (cmask pI909) (hmask pI909) 1 908 (true, (init pI909), (init pI909))) 909 17 false) = true := by
  decide +kernel
theorem I909_ok : RunOK pI909 909 (runFrom pI909 (fmask pI909) (cmask pI909) (hmask pI909) 1 908 (true, (init pI909), (init pI909))) ∧ intTest pI909 (runFrom pI909 (fmask pI909) (cmask pI909) (hmask pI909) 1 908 (true, (init pI909), (init pI909))) 909 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I909_fin) true) (by decide) rfl I909_fin intTest_fst
theorem link909 : linkOK pL909 pH909 pI909 = true := by decide +kernel
theorem cvx909 : ConvexBetweenHumps 909 :=
  cvx_of L909_ok H909_ok I909_ok link909 (by decide)

/-! ### `N = 910` -/

def pL910 : Prm := ⟨75, 35, 37, 912, 11, 18446744073709551616, 186014810790319535, 186014810790319535⟩
def pH910 : Prm := ⟨75, 35, 37, 912, 11, 18446744073709551616, 186017009813575087, 186017009813575087⟩
def pI910 : Prm := ⟨64, 31, 30, 912, 11, 18446744073709551616, 186014810790319535, 186017009813575087⟩
theorem L910_fin : (prmOK pL910 910 && ptTest pL910 (runFrom pL910 (fmask pL910) (cmask pL910) (hmask pL910) 1 909 (true, (init pL910), (init pL910))) 910 455 false) = true := by
  decide +kernel
theorem L910_ok : RunOK pL910 910 (runFrom pL910 (fmask pL910) (cmask pL910) (hmask pL910) 1 909 (true, (init pL910), (init pL910))) ∧ ptTest pL910 (runFrom pL910 (fmask pL910) (cmask pL910) (hmask pL910) 1 909 (true, (init pL910), (init pL910))) 910 455 false = true :=
  fin_run (runOK_init (prmOK_of_and L910_fin) true) (by decide) rfl L910_fin ptTest_fst
theorem H910_fin : (prmOK pH910 910 && ptTest pH910 (runFrom pH910 (fmask pH910) (cmask pH910) (hmask pH910) 1 909 (true, (init pH910), (init pH910))) 910 455 true) = true := by
  decide +kernel
theorem H910_ok : RunOK pH910 910 (runFrom pH910 (fmask pH910) (cmask pH910) (hmask pH910) 1 909 (true, (init pH910), (init pH910))) ∧ ptTest pH910 (runFrom pH910 (fmask pH910) (cmask pH910) (hmask pH910) 1 909 (true, (init pH910), (init pH910))) 910 455 true = true :=
  fin_run (runOK_init (prmOK_of_and H910_fin) true) (by decide) rfl H910_fin ptTest_fst
theorem I910_fin : (prmOK pI910 910 && intTest pI910 (runFrom pI910 (fmask pI910) (cmask pI910) (hmask pI910) 1 909 (true, (init pI910), (init pI910))) 910 17 true) = true := by
  decide +kernel
theorem I910_ok : RunOK pI910 910 (runFrom pI910 (fmask pI910) (cmask pI910) (hmask pI910) 1 909 (true, (init pI910), (init pI910))) ∧ intTest pI910 (runFrom pI910 (fmask pI910) (cmask pI910) (hmask pI910) 1 909 (true, (init pI910), (init pI910))) 910 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I910_fin) true) (by decide) rfl I910_fin intTest_fst
theorem link910 : linkOK pL910 pH910 pI910 = true := by decide +kernel
theorem cvx910 : ConvexBetweenHumps 910 :=
  cvx_of L910_ok H910_ok I910_ok link910 (by decide)
theorem cenlink910 : cenLinkOK pI910 910 = true := by decide +kernel
theorem cen910 : CenterUniqueMin 910 ∧ DipHyp 910 ∧ OnePointHyps 910 :=
  cen_of L910_ok H910_ok I910_ok link910 cenlink910

/-! ### `N = 911` -/

def pL911 : Prm := ⟨75, 35, 37, 913, 11, 18446744073709551616, 185852483663159722, 185852483663159722⟩
def pH911 : Prm := ⟨75, 35, 37, 913, 11, 18446744073709551616, 185854682686415274, 185854682686415274⟩
def pI911 : Prm := ⟨64, 31, 30, 913, 11, 18446744073709551616, 185852483663159722, 185854682686415274⟩
theorem L911_fin : (prmOK pL911 911 && ptTest pL911 (runFrom pL911 (fmask pL911) (cmask pL911) (hmask pL911) 1 910 (true, (init pL911), (init pL911))) 911 456 false) = true := by
  decide +kernel
theorem L911_ok : RunOK pL911 911 (runFrom pL911 (fmask pL911) (cmask pL911) (hmask pL911) 1 910 (true, (init pL911), (init pL911))) ∧ ptTest pL911 (runFrom pL911 (fmask pL911) (cmask pL911) (hmask pL911) 1 910 (true, (init pL911), (init pL911))) 911 456 false = true :=
  fin_run (runOK_init (prmOK_of_and L911_fin) true) (by decide) rfl L911_fin ptTest_fst
theorem H911_fin : (prmOK pH911 911 && ptTest pH911 (runFrom pH911 (fmask pH911) (cmask pH911) (hmask pH911) 1 910 (true, (init pH911), (init pH911))) 911 456 true) = true := by
  decide +kernel
theorem H911_ok : RunOK pH911 911 (runFrom pH911 (fmask pH911) (cmask pH911) (hmask pH911) 1 910 (true, (init pH911), (init pH911))) ∧ ptTest pH911 (runFrom pH911 (fmask pH911) (cmask pH911) (hmask pH911) 1 910 (true, (init pH911), (init pH911))) 911 456 true = true :=
  fin_run (runOK_init (prmOK_of_and H911_fin) true) (by decide) rfl H911_fin ptTest_fst
theorem I911_fin : (prmOK pI911 911 && intTest pI911 (runFrom pI911 (fmask pI911) (cmask pI911) (hmask pI911) 1 910 (true, (init pI911), (init pI911))) 911 17 false) = true := by
  decide +kernel
theorem I911_ok : RunOK pI911 911 (runFrom pI911 (fmask pI911) (cmask pI911) (hmask pI911) 1 910 (true, (init pI911), (init pI911))) ∧ intTest pI911 (runFrom pI911 (fmask pI911) (cmask pI911) (hmask pI911) 1 910 (true, (init pI911), (init pI911))) 911 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I911_fin) true) (by decide) rfl I911_fin intTest_fst
theorem link911 : linkOK pL911 pH911 pI911 = true := by decide +kernel
theorem cvx911 : ConvexBetweenHumps 911 :=
  cvx_of L911_ok H911_ok I911_ok link911 (by decide)

/-! ### `N = 912` -/

def pL912 : Prm := ⟨75, 35, 37, 914, 11, 18446744073709551616, 185690620101460996, 185690620101460996⟩
def pH912 : Prm := ⟨75, 35, 37, 914, 11, 18446744073709551616, 185692819124716548, 185692819124716548⟩
def pI912 : Prm := ⟨64, 31, 30, 914, 11, 18446744073709551616, 185690620101460996, 185692819124716548⟩
theorem L912_fin : (prmOK pL912 912 && ptTest pL912 (runFrom pL912 (fmask pL912) (cmask pL912) (hmask pL912) 1 911 (true, (init pL912), (init pL912))) 912 456 false) = true := by
  decide +kernel
theorem L912_ok : RunOK pL912 912 (runFrom pL912 (fmask pL912) (cmask pL912) (hmask pL912) 1 911 (true, (init pL912), (init pL912))) ∧ ptTest pL912 (runFrom pL912 (fmask pL912) (cmask pL912) (hmask pL912) 1 911 (true, (init pL912), (init pL912))) 912 456 false = true :=
  fin_run (runOK_init (prmOK_of_and L912_fin) true) (by decide) rfl L912_fin ptTest_fst
theorem H912_fin : (prmOK pH912 912 && ptTest pH912 (runFrom pH912 (fmask pH912) (cmask pH912) (hmask pH912) 1 911 (true, (init pH912), (init pH912))) 912 456 true) = true := by
  decide +kernel
theorem H912_ok : RunOK pH912 912 (runFrom pH912 (fmask pH912) (cmask pH912) (hmask pH912) 1 911 (true, (init pH912), (init pH912))) ∧ ptTest pH912 (runFrom pH912 (fmask pH912) (cmask pH912) (hmask pH912) 1 911 (true, (init pH912), (init pH912))) 912 456 true = true :=
  fin_run (runOK_init (prmOK_of_and H912_fin) true) (by decide) rfl H912_fin ptTest_fst
theorem I912_fin : (prmOK pI912 912 && intTest pI912 (runFrom pI912 (fmask pI912) (cmask pI912) (hmask pI912) 1 911 (true, (init pI912), (init pI912))) 912 17 true) = true := by
  decide +kernel
theorem I912_ok : RunOK pI912 912 (runFrom pI912 (fmask pI912) (cmask pI912) (hmask pI912) 1 911 (true, (init pI912), (init pI912))) ∧ intTest pI912 (runFrom pI912 (fmask pI912) (cmask pI912) (hmask pI912) 1 911 (true, (init pI912), (init pI912))) 912 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I912_fin) true) (by decide) rfl I912_fin intTest_fst
theorem link912 : linkOK pL912 pH912 pI912 = true := by decide +kernel
theorem cvx912 : ConvexBetweenHumps 912 :=
  cvx_of L912_ok H912_ok I912_ok link912 (by decide)
theorem cenlink912 : cenLinkOK pI912 912 = true := by decide +kernel
theorem cen912 : CenterUniqueMin 912 ∧ DipHyp 912 ∧ OnePointHyps 912 :=
  cen_of L912_ok H912_ok I912_ok link912 cenlink912

/-! ### `N = 913` -/

def pL913 : Prm := ⟨75, 35, 37, 915, 11, 18446744073709551616, 185528912378243587, 185528912378243587⟩
def pH913 : Prm := ⟨75, 35, 37, 915, 11, 18446744073709551616, 185531111401499139, 185531111401499139⟩
def pI913 : Prm := ⟨64, 31, 30, 915, 11, 18446744073709551616, 185528912378243587, 185531111401499139⟩
theorem L913_fin : (prmOK pL913 913 && ptTest pL913 (runFrom pL913 (fmask pL913) (cmask pL913) (hmask pL913) 1 912 (true, (init pL913), (init pL913))) 913 457 false) = true := by
  decide +kernel
theorem L913_ok : RunOK pL913 913 (runFrom pL913 (fmask pL913) (cmask pL913) (hmask pL913) 1 912 (true, (init pL913), (init pL913))) ∧ ptTest pL913 (runFrom pL913 (fmask pL913) (cmask pL913) (hmask pL913) 1 912 (true, (init pL913), (init pL913))) 913 457 false = true :=
  fin_run (runOK_init (prmOK_of_and L913_fin) true) (by decide) rfl L913_fin ptTest_fst
theorem H913_fin : (prmOK pH913 913 && ptTest pH913 (runFrom pH913 (fmask pH913) (cmask pH913) (hmask pH913) 1 912 (true, (init pH913), (init pH913))) 913 457 true) = true := by
  decide +kernel
theorem H913_ok : RunOK pH913 913 (runFrom pH913 (fmask pH913) (cmask pH913) (hmask pH913) 1 912 (true, (init pH913), (init pH913))) ∧ ptTest pH913 (runFrom pH913 (fmask pH913) (cmask pH913) (hmask pH913) 1 912 (true, (init pH913), (init pH913))) 913 457 true = true :=
  fin_run (runOK_init (prmOK_of_and H913_fin) true) (by decide) rfl H913_fin ptTest_fst
theorem I913_fin : (prmOK pI913 913 && intTest pI913 (runFrom pI913 (fmask pI913) (cmask pI913) (hmask pI913) 1 912 (true, (init pI913), (init pI913))) 913 17 false) = true := by
  decide +kernel
theorem I913_ok : RunOK pI913 913 (runFrom pI913 (fmask pI913) (cmask pI913) (hmask pI913) 1 912 (true, (init pI913), (init pI913))) ∧ intTest pI913 (runFrom pI913 (fmask pI913) (cmask pI913) (hmask pI913) 1 912 (true, (init pI913), (init pI913))) 913 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I913_fin) true) (by decide) rfl I913_fin intTest_fst
theorem link913 : linkOK pL913 pH913 pI913 = true := by decide +kernel
theorem cvx913 : ConvexBetweenHumps 913 :=
  cvx_of L913_ok H913_ok I913_ok link913 (by decide)

/-! ### `N = 914` -/

def pL914 : Prm := ⟨75, 35, 37, 916, 11, 18446744073709551616, 185367665361776889, 185367665361776889⟩
def pH914 : Prm := ⟨75, 35, 37, 916, 11, 18446744073709551616, 185369864385032441, 185369864385032441⟩
def pI914 : Prm := ⟨64, 31, 30, 916, 11, 18446744073709551616, 185367665361776889, 185369864385032441⟩
theorem L914_fin : (prmOK pL914 914 && ptTest pL914 (runFrom pL914 (fmask pL914) (cmask pL914) (hmask pL914) 1 913 (true, (init pL914), (init pL914))) 914 457 false) = true := by
  decide +kernel
theorem L914_ok : RunOK pL914 914 (runFrom pL914 (fmask pL914) (cmask pL914) (hmask pL914) 1 913 (true, (init pL914), (init pL914))) ∧ ptTest pL914 (runFrom pL914 (fmask pL914) (cmask pL914) (hmask pL914) 1 913 (true, (init pL914), (init pL914))) 914 457 false = true :=
  fin_run (runOK_init (prmOK_of_and L914_fin) true) (by decide) rfl L914_fin ptTest_fst
theorem H914_fin : (prmOK pH914 914 && ptTest pH914 (runFrom pH914 (fmask pH914) (cmask pH914) (hmask pH914) 1 913 (true, (init pH914), (init pH914))) 914 457 true) = true := by
  decide +kernel
theorem H914_ok : RunOK pH914 914 (runFrom pH914 (fmask pH914) (cmask pH914) (hmask pH914) 1 913 (true, (init pH914), (init pH914))) ∧ ptTest pH914 (runFrom pH914 (fmask pH914) (cmask pH914) (hmask pH914) 1 913 (true, (init pH914), (init pH914))) 914 457 true = true :=
  fin_run (runOK_init (prmOK_of_and H914_fin) true) (by decide) rfl H914_fin ptTest_fst
theorem I914_fin : (prmOK pI914 914 && intTest pI914 (runFrom pI914 (fmask pI914) (cmask pI914) (hmask pI914) 1 913 (true, (init pI914), (init pI914))) 914 17 true) = true := by
  decide +kernel
theorem I914_ok : RunOK pI914 914 (runFrom pI914 (fmask pI914) (cmask pI914) (hmask pI914) 1 913 (true, (init pI914), (init pI914))) ∧ intTest pI914 (runFrom pI914 (fmask pI914) (cmask pI914) (hmask pI914) 1 913 (true, (init pI914), (init pI914))) 914 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I914_fin) true) (by decide) rfl I914_fin intTest_fst
theorem link914 : linkOK pL914 pH914 pI914 = true := by decide +kernel
theorem cvx914 : ConvexBetweenHumps 914 :=
  cvx_of L914_ok H914_ok I914_ok link914 (by decide)
theorem cenlink914 : cenLinkOK pI914 914 = true := by decide +kernel
theorem cen914 : CenterUniqueMin 914 ∧ DipHyp 914 ∧ OnePointHyps 914 :=
  cen_of L914_ok H914_ok I914_ok link914 cenlink914

/-! ### `N = 915` -/

def pL915 : Prm := ⟨75, 35, 37, 917, 11, 18446744073709551616, 185206573379642592, 185206573379642592⟩
def pH915 : Prm := ⟨75, 35, 37, 917, 11, 18446744073709551616, 185208772402898144, 185208772402898144⟩
def pI915 : Prm := ⟨64, 31, 30, 917, 11, 18446744073709551616, 185206573379642592, 185208772402898144⟩
theorem L915_fin : (prmOK pL915 915 && ptTest pL915 (runFrom pL915 (fmask pL915) (cmask pL915) (hmask pL915) 1 914 (true, (init pL915), (init pL915))) 915 458 false) = true := by
  decide +kernel
theorem L915_ok : RunOK pL915 915 (runFrom pL915 (fmask pL915) (cmask pL915) (hmask pL915) 1 914 (true, (init pL915), (init pL915))) ∧ ptTest pL915 (runFrom pL915 (fmask pL915) (cmask pL915) (hmask pL915) 1 914 (true, (init pL915), (init pL915))) 915 458 false = true :=
  fin_run (runOK_init (prmOK_of_and L915_fin) true) (by decide) rfl L915_fin ptTest_fst
theorem H915_fin : (prmOK pH915 915 && ptTest pH915 (runFrom pH915 (fmask pH915) (cmask pH915) (hmask pH915) 1 914 (true, (init pH915), (init pH915))) 915 458 true) = true := by
  decide +kernel
theorem H915_ok : RunOK pH915 915 (runFrom pH915 (fmask pH915) (cmask pH915) (hmask pH915) 1 914 (true, (init pH915), (init pH915))) ∧ ptTest pH915 (runFrom pH915 (fmask pH915) (cmask pH915) (hmask pH915) 1 914 (true, (init pH915), (init pH915))) 915 458 true = true :=
  fin_run (runOK_init (prmOK_of_and H915_fin) true) (by decide) rfl H915_fin ptTest_fst
theorem I915_fin : (prmOK pI915 915 && intTest pI915 (runFrom pI915 (fmask pI915) (cmask pI915) (hmask pI915) 1 914 (true, (init pI915), (init pI915))) 915 17 false) = true := by
  decide +kernel
theorem I915_ok : RunOK pI915 915 (runFrom pI915 (fmask pI915) (cmask pI915) (hmask pI915) 1 914 (true, (init pI915), (init pI915))) ∧ intTest pI915 (runFrom pI915 (fmask pI915) (cmask pI915) (hmask pI915) 1 914 (true, (init pI915), (init pI915))) 915 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I915_fin) true) (by decide) rfl I915_fin intTest_fst
theorem link915 : linkOK pL915 pH915 pI915 = true := by decide +kernel
theorem cvx915 : ConvexBetweenHumps 915 :=
  cvx_of L915_ok H915_ok I915_ok link915 (by decide)

/-! ### `N = 916` -/

def pL916 : Prm := ⟨75, 35, 37, 918, 11, 18446744073709551616, 185045939269344932, 185045939269344932⟩
def pH916 : Prm := ⟨75, 35, 37, 918, 11, 18446744073709551616, 185048138292600484, 185048138292600484⟩
def pI916 : Prm := ⟨64, 31, 30, 918, 11, 18446744073709551616, 185045939269344932, 185048138292600484⟩
theorem L916_fin : (prmOK pL916 916 && ptTest pL916 (runFrom pL916 (fmask pL916) (cmask pL916) (hmask pL916) 1 915 (true, (init pL916), (init pL916))) 916 458 false) = true := by
  decide +kernel
theorem L916_ok : RunOK pL916 916 (runFrom pL916 (fmask pL916) (cmask pL916) (hmask pL916) 1 915 (true, (init pL916), (init pL916))) ∧ ptTest pL916 (runFrom pL916 (fmask pL916) (cmask pL916) (hmask pL916) 1 915 (true, (init pL916), (init pL916))) 916 458 false = true :=
  fin_run (runOK_init (prmOK_of_and L916_fin) true) (by decide) rfl L916_fin ptTest_fst
theorem H916_fin : (prmOK pH916 916 && ptTest pH916 (runFrom pH916 (fmask pH916) (cmask pH916) (hmask pH916) 1 915 (true, (init pH916), (init pH916))) 916 458 true) = true := by
  decide +kernel
theorem H916_ok : RunOK pH916 916 (runFrom pH916 (fmask pH916) (cmask pH916) (hmask pH916) 1 915 (true, (init pH916), (init pH916))) ∧ ptTest pH916 (runFrom pH916 (fmask pH916) (cmask pH916) (hmask pH916) 1 915 (true, (init pH916), (init pH916))) 916 458 true = true :=
  fin_run (runOK_init (prmOK_of_and H916_fin) true) (by decide) rfl H916_fin ptTest_fst
theorem I916_fin : (prmOK pI916 916 && intTest pI916 (runFrom pI916 (fmask pI916) (cmask pI916) (hmask pI916) 1 915 (true, (init pI916), (init pI916))) 916 17 true) = true := by
  decide +kernel
theorem I916_ok : RunOK pI916 916 (runFrom pI916 (fmask pI916) (cmask pI916) (hmask pI916) 1 915 (true, (init pI916), (init pI916))) ∧ intTest pI916 (runFrom pI916 (fmask pI916) (cmask pI916) (hmask pI916) 1 915 (true, (init pI916), (init pI916))) 916 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I916_fin) true) (by decide) rfl I916_fin intTest_fst
theorem link916 : linkOK pL916 pH916 pI916 = true := by decide +kernel
theorem cvx916 : ConvexBetweenHumps 916 :=
  cvx_of L916_ok H916_ok I916_ok link916 (by decide)
theorem cenlink916 : cenLinkOK pI916 916 = true := by decide +kernel
theorem cen916 : CenterUniqueMin 916 ∧ DipHyp 916 ∧ OnePointHyps 916 :=
  cen_of L916_ok H916_ok I916_ok link916 cenlink916

/-! ### `N = 917` -/

def pL917 : Prm := ⟨75, 35, 37, 919, 11, 18446744073709551616, 184885459394838569, 184885459394838569⟩
def pH917 : Prm := ⟨75, 35, 37, 919, 11, 18446744073709551616, 184887658418094121, 184887658418094121⟩
def pI917 : Prm := ⟨64, 31, 30, 919, 11, 18446744073709551616, 184885459394838569, 184887658418094121⟩
theorem L917_fin : (prmOK pL917 917 && ptTest pL917 (runFrom pL917 (fmask pL917) (cmask pL917) (hmask pL917) 1 916 (true, (init pL917), (init pL917))) 917 459 false) = true := by
  decide +kernel
theorem L917_ok : RunOK pL917 917 (runFrom pL917 (fmask pL917) (cmask pL917) (hmask pL917) 1 916 (true, (init pL917), (init pL917))) ∧ ptTest pL917 (runFrom pL917 (fmask pL917) (cmask pL917) (hmask pL917) 1 916 (true, (init pL917), (init pL917))) 917 459 false = true :=
  fin_run (runOK_init (prmOK_of_and L917_fin) true) (by decide) rfl L917_fin ptTest_fst
theorem H917_fin : (prmOK pH917 917 && ptTest pH917 (runFrom pH917 (fmask pH917) (cmask pH917) (hmask pH917) 1 916 (true, (init pH917), (init pH917))) 917 459 true) = true := by
  decide +kernel
theorem H917_ok : RunOK pH917 917 (runFrom pH917 (fmask pH917) (cmask pH917) (hmask pH917) 1 916 (true, (init pH917), (init pH917))) ∧ ptTest pH917 (runFrom pH917 (fmask pH917) (cmask pH917) (hmask pH917) 1 916 (true, (init pH917), (init pH917))) 917 459 true = true :=
  fin_run (runOK_init (prmOK_of_and H917_fin) true) (by decide) rfl H917_fin ptTest_fst
theorem I917_fin : (prmOK pI917 917 && intTest pI917 (runFrom pI917 (fmask pI917) (cmask pI917) (hmask pI917) 1 916 (true, (init pI917), (init pI917))) 917 17 false) = true := by
  decide +kernel
theorem I917_ok : RunOK pI917 917 (runFrom pI917 (fmask pI917) (cmask pI917) (hmask pI917) 1 916 (true, (init pI917), (init pI917))) ∧ intTest pI917 (runFrom pI917 (fmask pI917) (cmask pI917) (hmask pI917) 1 916 (true, (init pI917), (init pI917))) 917 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I917_fin) true) (by decide) rfl I917_fin intTest_fst
theorem link917 : linkOK pL917 pH917 pI917 = true := by decide +kernel
theorem cvx917 : ConvexBetweenHumps 917 :=
  cvx_of L917_ok H917_ok I917_ok link917 (by decide)

/-! ### `N = 918` -/

def pL918 : Prm := ⟨75, 35, 37, 920, 11, 18446744073709551616, 184725434580774364, 184725434580774364⟩
def pH918 : Prm := ⟨75, 35, 37, 920, 11, 18446744073709551616, 184727633604029916, 184727633604029916⟩
def pI918 : Prm := ⟨64, 31, 30, 920, 11, 18446744073709551616, 184725434580774364, 184727633604029916⟩
theorem L918_fin : (prmOK pL918 918 && ptTest pL918 (runFrom pL918 (fmask pL918) (cmask pL918) (hmask pL918) 1 917 (true, (init pL918), (init pL918))) 918 459 false) = true := by
  decide +kernel
theorem L918_ok : RunOK pL918 918 (runFrom pL918 (fmask pL918) (cmask pL918) (hmask pL918) 1 917 (true, (init pL918), (init pL918))) ∧ ptTest pL918 (runFrom pL918 (fmask pL918) (cmask pL918) (hmask pL918) 1 917 (true, (init pL918), (init pL918))) 918 459 false = true :=
  fin_run (runOK_init (prmOK_of_and L918_fin) true) (by decide) rfl L918_fin ptTest_fst
theorem H918_fin : (prmOK pH918 918 && ptTest pH918 (runFrom pH918 (fmask pH918) (cmask pH918) (hmask pH918) 1 917 (true, (init pH918), (init pH918))) 918 459 true) = true := by
  decide +kernel
theorem H918_ok : RunOK pH918 918 (runFrom pH918 (fmask pH918) (cmask pH918) (hmask pH918) 1 917 (true, (init pH918), (init pH918))) ∧ ptTest pH918 (runFrom pH918 (fmask pH918) (cmask pH918) (hmask pH918) 1 917 (true, (init pH918), (init pH918))) 918 459 true = true :=
  fin_run (runOK_init (prmOK_of_and H918_fin) true) (by decide) rfl H918_fin ptTest_fst
theorem I918_fin : (prmOK pI918 918 && intTest pI918 (runFrom pI918 (fmask pI918) (cmask pI918) (hmask pI918) 1 917 (true, (init pI918), (init pI918))) 918 17 true) = true := by
  decide +kernel
theorem I918_ok : RunOK pI918 918 (runFrom pI918 (fmask pI918) (cmask pI918) (hmask pI918) 1 917 (true, (init pI918), (init pI918))) ∧ intTest pI918 (runFrom pI918 (fmask pI918) (cmask pI918) (hmask pI918) 1 917 (true, (init pI918), (init pI918))) 918 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I918_fin) true) (by decide) rfl I918_fin intTest_fst
theorem link918 : linkOK pL918 pH918 pI918 = true := by decide +kernel
theorem cvx918 : ConvexBetweenHumps 918 :=
  cvx_of L918_ok H918_ok I918_ok link918 (by decide)
theorem cenlink918 : cenLinkOK pI918 918 = true := by decide +kernel
theorem cen918 : CenterUniqueMin 918 ∧ DipHyp 918 ∧ OnePointHyps 918 :=
  cen_of L918_ok H918_ok I918_ok link918 cenlink918

/-! ### `N = 919` -/

def pL919 : Prm := ⟨75, 35, 37, 921, 11, 18446744073709551616, 184565563209512822, 184565563209512822⟩
def pH919 : Prm := ⟨75, 35, 37, 921, 11, 18446744073709551616, 184567762232768374, 184567762232768374⟩
def pI919 : Prm := ⟨64, 31, 30, 921, 11, 18446744073709551616, 184565563209512822, 184567762232768374⟩
theorem L919_fin : (prmOK pL919 919 && ptTest pL919 (runFrom pL919 (fmask pL919) (cmask pL919) (hmask pL919) 1 918 (true, (init pL919), (init pL919))) 919 460 false) = true := by
  decide +kernel
theorem L919_ok : RunOK pL919 919 (runFrom pL919 (fmask pL919) (cmask pL919) (hmask pL919) 1 918 (true, (init pL919), (init pL919))) ∧ ptTest pL919 (runFrom pL919 (fmask pL919) (cmask pL919) (hmask pL919) 1 918 (true, (init pL919), (init pL919))) 919 460 false = true :=
  fin_run (runOK_init (prmOK_of_and L919_fin) true) (by decide) rfl L919_fin ptTest_fst
theorem H919_fin : (prmOK pH919 919 && ptTest pH919 (runFrom pH919 (fmask pH919) (cmask pH919) (hmask pH919) 1 918 (true, (init pH919), (init pH919))) 919 460 true) = true := by
  decide +kernel
theorem H919_ok : RunOK pH919 919 (runFrom pH919 (fmask pH919) (cmask pH919) (hmask pH919) 1 918 (true, (init pH919), (init pH919))) ∧ ptTest pH919 (runFrom pH919 (fmask pH919) (cmask pH919) (hmask pH919) 1 918 (true, (init pH919), (init pH919))) 919 460 true = true :=
  fin_run (runOK_init (prmOK_of_and H919_fin) true) (by decide) rfl H919_fin ptTest_fst
theorem I919_fin : (prmOK pI919 919 && intTest pI919 (runFrom pI919 (fmask pI919) (cmask pI919) (hmask pI919) 1 918 (true, (init pI919), (init pI919))) 919 17 false) = true := by
  decide +kernel
theorem I919_ok : RunOK pI919 919 (runFrom pI919 (fmask pI919) (cmask pI919) (hmask pI919) 1 918 (true, (init pI919), (init pI919))) ∧ intTest pI919 (runFrom pI919 (fmask pI919) (cmask pI919) (hmask pI919) 1 918 (true, (init pI919), (init pI919))) 919 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I919_fin) true) (by decide) rfl I919_fin intTest_fst
theorem link919 : linkOK pL919 pH919 pI919 = true := by decide +kernel
theorem cvx919 : ConvexBetweenHumps 919 :=
  cvx_of L919_ok H919_ok I919_ok link919 (by decide)

/-! ### `N = 920` -/

def pL920 : Prm := ⟨75, 35, 37, 922, 11, 18446744073709551616, 184406144110560306, 184406144110560306⟩
def pH920 : Prm := ⟨75, 35, 37, 922, 11, 18446744073709551616, 184408343133815858, 184408343133815858⟩
def pI920 : Prm := ⟨64, 31, 30, 922, 11, 18446744073709551616, 184406144110560306, 184408343133815858⟩
theorem L920_fin : (prmOK pL920 920 && ptTest pL920 (runFrom pL920 (fmask pL920) (cmask pL920) (hmask pL920) 1 919 (true, (init pL920), (init pL920))) 920 460 false) = true := by
  decide +kernel
theorem L920_ok : RunOK pL920 920 (runFrom pL920 (fmask pL920) (cmask pL920) (hmask pL920) 1 919 (true, (init pL920), (init pL920))) ∧ ptTest pL920 (runFrom pL920 (fmask pL920) (cmask pL920) (hmask pL920) 1 919 (true, (init pL920), (init pL920))) 920 460 false = true :=
  fin_run (runOK_init (prmOK_of_and L920_fin) true) (by decide) rfl L920_fin ptTest_fst
theorem H920_fin : (prmOK pH920 920 && ptTest pH920 (runFrom pH920 (fmask pH920) (cmask pH920) (hmask pH920) 1 919 (true, (init pH920), (init pH920))) 920 460 true) = true := by
  decide +kernel
theorem H920_ok : RunOK pH920 920 (runFrom pH920 (fmask pH920) (cmask pH920) (hmask pH920) 1 919 (true, (init pH920), (init pH920))) ∧ ptTest pH920 (runFrom pH920 (fmask pH920) (cmask pH920) (hmask pH920) 1 919 (true, (init pH920), (init pH920))) 920 460 true = true :=
  fin_run (runOK_init (prmOK_of_and H920_fin) true) (by decide) rfl H920_fin ptTest_fst
theorem I920_fin : (prmOK pI920 920 && intTest pI920 (runFrom pI920 (fmask pI920) (cmask pI920) (hmask pI920) 1 919 (true, (init pI920), (init pI920))) 920 17 true) = true := by
  decide +kernel
theorem I920_ok : RunOK pI920 920 (runFrom pI920 (fmask pI920) (cmask pI920) (hmask pI920) 1 919 (true, (init pI920), (init pI920))) ∧ intTest pI920 (runFrom pI920 (fmask pI920) (cmask pI920) (hmask pI920) 1 919 (true, (init pI920), (init pI920))) 920 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I920_fin) true) (by decide) rfl I920_fin intTest_fst
theorem link920 : linkOK pL920 pH920 pI920 = true := by decide +kernel
theorem cvx920 : ConvexBetweenHumps 920 :=
  cvx_of L920_ok H920_ok I920_ok link920 (by decide)
theorem cenlink920 : cenLinkOK pI920 920 = true := by decide +kernel
theorem cen920 : CenterUniqueMin 920 ∧ DipHyp 920 ∧ OnePointHyps 920 :=
  cen_of L920_ok H920_ok I920_ok link920 cenlink920

/-! ### The range -/

theorem cvx_868_920 {N : ℕ} (h1 : 868 ≤ N) (h2 : N ≤ 920) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 893
  · by_cases h4 : N ≤ 880
    · by_cases h6 : N ≤ 873
      · by_cases h8 : N ≤ 870
        · by_cases h10 : N ≤ 868
          · obtain rfl : N = 868 := by omega
            exact cvx868
          · by_cases h12 : N ≤ 869
            · obtain rfl : N = 869 := by omega
              exact cvx869
            · obtain rfl : N = 870 := by omega
              exact cvx870
        · by_cases h10 : N ≤ 871
          · obtain rfl : N = 871 := by omega
            exact cvx871
          · by_cases h12 : N ≤ 872
            · obtain rfl : N = 872 := by omega
              exact cvx872
            · obtain rfl : N = 873 := by omega
              exact cvx873
      · by_cases h8 : N ≤ 876
        · by_cases h10 : N ≤ 874
          · obtain rfl : N = 874 := by omega
            exact cvx874
          · by_cases h12 : N ≤ 875
            · obtain rfl : N = 875 := by omega
              exact cvx875
            · obtain rfl : N = 876 := by omega
              exact cvx876
        · by_cases h10 : N ≤ 878
          · by_cases h12 : N ≤ 877
            · obtain rfl : N = 877 := by omega
              exact cvx877
            · obtain rfl : N = 878 := by omega
              exact cvx878
          · by_cases h12 : N ≤ 879
            · obtain rfl : N = 879 := by omega
              exact cvx879
            · obtain rfl : N = 880 := by omega
              exact cvx880
    · by_cases h6 : N ≤ 886
      · by_cases h8 : N ≤ 883
        · by_cases h10 : N ≤ 881
          · obtain rfl : N = 881 := by omega
            exact cvx881
          · by_cases h12 : N ≤ 882
            · obtain rfl : N = 882 := by omega
              exact cvx882
            · obtain rfl : N = 883 := by omega
              exact cvx883
        · by_cases h10 : N ≤ 884
          · obtain rfl : N = 884 := by omega
            exact cvx884
          · by_cases h12 : N ≤ 885
            · obtain rfl : N = 885 := by omega
              exact cvx885
            · obtain rfl : N = 886 := by omega
              exact cvx886
      · by_cases h8 : N ≤ 889
        · by_cases h10 : N ≤ 887
          · obtain rfl : N = 887 := by omega
            exact cvx887
          · by_cases h12 : N ≤ 888
            · obtain rfl : N = 888 := by omega
              exact cvx888
            · obtain rfl : N = 889 := by omega
              exact cvx889
        · by_cases h10 : N ≤ 891
          · by_cases h12 : N ≤ 890
            · obtain rfl : N = 890 := by omega
              exact cvx890
            · obtain rfl : N = 891 := by omega
              exact cvx891
          · by_cases h12 : N ≤ 892
            · obtain rfl : N = 892 := by omega
              exact cvx892
            · obtain rfl : N = 893 := by omega
              exact cvx893
  · by_cases h4 : N ≤ 906
    · by_cases h6 : N ≤ 899
      · by_cases h8 : N ≤ 896
        · by_cases h10 : N ≤ 894
          · obtain rfl : N = 894 := by omega
            exact cvx894
          · by_cases h12 : N ≤ 895
            · obtain rfl : N = 895 := by omega
              exact cvx895
            · obtain rfl : N = 896 := by omega
              exact cvx896
        · by_cases h10 : N ≤ 897
          · obtain rfl : N = 897 := by omega
            exact cvx897
          · by_cases h12 : N ≤ 898
            · obtain rfl : N = 898 := by omega
              exact cvx898
            · obtain rfl : N = 899 := by omega
              exact cvx899
      · by_cases h8 : N ≤ 902
        · by_cases h10 : N ≤ 900
          · obtain rfl : N = 900 := by omega
            exact cvx900
          · by_cases h12 : N ≤ 901
            · obtain rfl : N = 901 := by omega
              exact cvx901
            · obtain rfl : N = 902 := by omega
              exact cvx902
        · by_cases h10 : N ≤ 904
          · by_cases h12 : N ≤ 903
            · obtain rfl : N = 903 := by omega
              exact cvx903
            · obtain rfl : N = 904 := by omega
              exact cvx904
          · by_cases h12 : N ≤ 905
            · obtain rfl : N = 905 := by omega
              exact cvx905
            · obtain rfl : N = 906 := by omega
              exact cvx906
    · by_cases h6 : N ≤ 913
      · by_cases h8 : N ≤ 909
        · by_cases h10 : N ≤ 907
          · obtain rfl : N = 907 := by omega
            exact cvx907
          · by_cases h12 : N ≤ 908
            · obtain rfl : N = 908 := by omega
              exact cvx908
            · obtain rfl : N = 909 := by omega
              exact cvx909
        · by_cases h10 : N ≤ 911
          · by_cases h12 : N ≤ 910
            · obtain rfl : N = 910 := by omega
              exact cvx910
            · obtain rfl : N = 911 := by omega
              exact cvx911
          · by_cases h12 : N ≤ 912
            · obtain rfl : N = 912 := by omega
              exact cvx912
            · obtain rfl : N = 913 := by omega
              exact cvx913
      · by_cases h8 : N ≤ 916
        · by_cases h10 : N ≤ 914
          · obtain rfl : N = 914 := by omega
            exact cvx914
          · by_cases h12 : N ≤ 915
            · obtain rfl : N = 915 := by omega
              exact cvx915
            · obtain rfl : N = 916 := by omega
              exact cvx916
        · by_cases h10 : N ≤ 918
          · by_cases h12 : N ≤ 917
            · obtain rfl : N = 917 := by omega
              exact cvx917
            · obtain rfl : N = 918 := by omega
              exact cvx918
          · by_cases h12 : N ≤ 919
            · obtain rfl : N = 919 := by omega
              exact cvx919
            · obtain rfl : N = 920 := by omega
              exact cvx920

theorem cen_868_920 {N : ℕ} (h1 : 868 ≤ N) (h2 : N ≤ 920) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 892
  · by_cases h4 : N ≤ 878
    · by_cases h6 : N ≤ 872
      · by_cases h8 : N ≤ 868
        · obtain rfl : N = 868 := by omega
          exact cen868
        · by_cases h10 : N ≤ 870
          · obtain rfl : N = 870 := by omega
            exact cen870
          · obtain rfl : N = 872 := by omega
            exact cen872
      · by_cases h8 : N ≤ 874
        · obtain rfl : N = 874 := by omega
          exact cen874
        · by_cases h10 : N ≤ 876
          · obtain rfl : N = 876 := by omega
            exact cen876
          · obtain rfl : N = 878 := by omega
            exact cen878
    · by_cases h6 : N ≤ 884
      · by_cases h8 : N ≤ 880
        · obtain rfl : N = 880 := by omega
          exact cen880
        · by_cases h10 : N ≤ 882
          · obtain rfl : N = 882 := by omega
            exact cen882
          · obtain rfl : N = 884 := by omega
            exact cen884
      · by_cases h8 : N ≤ 888
        · by_cases h10 : N ≤ 886
          · obtain rfl : N = 886 := by omega
            exact cen886
          · obtain rfl : N = 888 := by omega
            exact cen888
        · by_cases h10 : N ≤ 890
          · obtain rfl : N = 890 := by omega
            exact cen890
          · obtain rfl : N = 892 := by omega
            exact cen892
  · by_cases h4 : N ≤ 906
    · by_cases h6 : N ≤ 898
      · by_cases h8 : N ≤ 894
        · obtain rfl : N = 894 := by omega
          exact cen894
        · by_cases h10 : N ≤ 896
          · obtain rfl : N = 896 := by omega
            exact cen896
          · obtain rfl : N = 898 := by omega
            exact cen898
      · by_cases h8 : N ≤ 902
        · by_cases h10 : N ≤ 900
          · obtain rfl : N = 900 := by omega
            exact cen900
          · obtain rfl : N = 902 := by omega
            exact cen902
        · by_cases h10 : N ≤ 904
          · obtain rfl : N = 904 := by omega
            exact cen904
          · obtain rfl : N = 906 := by omega
            exact cen906
    · by_cases h6 : N ≤ 912
      · by_cases h8 : N ≤ 908
        · obtain rfl : N = 908 := by omega
          exact cen908
        · by_cases h10 : N ≤ 910
          · obtain rfl : N = 910 := by omega
            exact cen910
          · obtain rfl : N = 912 := by omega
            exact cen912
      · by_cases h8 : N ≤ 916
        · by_cases h10 : N ≤ 914
          · obtain rfl : N = 914 := by omega
            exact cen914
          · obtain rfl : N = 916 := by omega
            exact cen916
        · by_cases h10 : N ≤ 918
          · obtain rfl : N = 918 := by omega
            exact cen918
          · obtain rfl : N = 920 := by omega
            exact cen920

end Kagey131.PaperD.T7
