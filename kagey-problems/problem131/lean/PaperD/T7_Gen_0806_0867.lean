import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 806, …, 867` (generated)

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

/-! ### `N = 806` -/

def pL806 : Prm := ⟨73, 34, 36, 808, 11, 18446744073709551616, 204778385544285895, 204778385544285895⟩
def pH806 : Prm := ⟨73, 34, 36, 808, 11, 18446744073709551616, 204782783590796999, 204782783590796999⟩
def pI806 : Prm := ⟨63, 31, 29, 808, 11, 18446744073709551616, 204778385544285895, 204782783590796999⟩
theorem L806_fin : (prmOK pL806 806 && ptTest pL806 (runFrom pL806 (fmask pL806) (cmask pL806) (hmask pL806) 1 805 (true, (init pL806), (init pL806))) 806 403 false) = true := by
  decide +kernel
theorem L806_ok : RunOK pL806 806 (runFrom pL806 (fmask pL806) (cmask pL806) (hmask pL806) 1 805 (true, (init pL806), (init pL806))) ∧ ptTest pL806 (runFrom pL806 (fmask pL806) (cmask pL806) (hmask pL806) 1 805 (true, (init pL806), (init pL806))) 806 403 false = true :=
  fin_run (runOK_init (prmOK_of_and L806_fin) true) (by decide) rfl L806_fin ptTest_fst
theorem H806_fin : (prmOK pH806 806 && ptTest pH806 (runFrom pH806 (fmask pH806) (cmask pH806) (hmask pH806) 1 805 (true, (init pH806), (init pH806))) 806 403 true) = true := by
  decide +kernel
theorem H806_ok : RunOK pH806 806 (runFrom pH806 (fmask pH806) (cmask pH806) (hmask pH806) 1 805 (true, (init pH806), (init pH806))) ∧ ptTest pH806 (runFrom pH806 (fmask pH806) (cmask pH806) (hmask pH806) 1 805 (true, (init pH806), (init pH806))) 806 403 true = true :=
  fin_run (runOK_init (prmOK_of_and H806_fin) true) (by decide) rfl H806_fin ptTest_fst
theorem I806_fin : (prmOK pI806 806 && intTest pI806 (runFrom pI806 (fmask pI806) (cmask pI806) (hmask pI806) 1 805 (true, (init pI806), (init pI806))) 806 17 true) = true := by
  decide +kernel
theorem I806_ok : RunOK pI806 806 (runFrom pI806 (fmask pI806) (cmask pI806) (hmask pI806) 1 805 (true, (init pI806), (init pI806))) ∧ intTest pI806 (runFrom pI806 (fmask pI806) (cmask pI806) (hmask pI806) 1 805 (true, (init pI806), (init pI806))) 806 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I806_fin) true) (by decide) rfl I806_fin intTest_fst
theorem link806 : linkOK pL806 pH806 pI806 = true := by decide +kernel
theorem cvx806 : ConvexBetweenHumps 806 :=
  cvx_of L806_ok H806_ok I806_ok link806 (by decide)
theorem cenlink806 : cenLinkOK pI806 806 = true := by decide +kernel
theorem cen806 : CenterUniqueMin 806 ∧ DipHyp 806 ∧ OnePointHyps 806 :=
  cen_of L806_ok H806_ok I806_ok link806 cenlink806

/-! ### `N = 807` -/

def pL807 : Prm := ⟨73, 34, 36, 809, 11, 18446744073709551616, 204577956116256037, 204577956116256037⟩
def pH807 : Prm := ⟨73, 34, 36, 809, 11, 18446744073709551616, 204582354162767141, 204582354162767141⟩
def pI807 : Prm := ⟨63, 31, 29, 809, 11, 18446744073709551616, 204577956116256037, 204582354162767141⟩
theorem L807_fin : (prmOK pL807 807 && ptTest pL807 (runFrom pL807 (fmask pL807) (cmask pL807) (hmask pL807) 1 806 (true, (init pL807), (init pL807))) 807 404 false) = true := by
  decide +kernel
theorem L807_ok : RunOK pL807 807 (runFrom pL807 (fmask pL807) (cmask pL807) (hmask pL807) 1 806 (true, (init pL807), (init pL807))) ∧ ptTest pL807 (runFrom pL807 (fmask pL807) (cmask pL807) (hmask pL807) 1 806 (true, (init pL807), (init pL807))) 807 404 false = true :=
  fin_run (runOK_init (prmOK_of_and L807_fin) true) (by decide) rfl L807_fin ptTest_fst
theorem H807_fin : (prmOK pH807 807 && ptTest pH807 (runFrom pH807 (fmask pH807) (cmask pH807) (hmask pH807) 1 806 (true, (init pH807), (init pH807))) 807 404 true) = true := by
  decide +kernel
theorem H807_ok : RunOK pH807 807 (runFrom pH807 (fmask pH807) (cmask pH807) (hmask pH807) 1 806 (true, (init pH807), (init pH807))) ∧ ptTest pH807 (runFrom pH807 (fmask pH807) (cmask pH807) (hmask pH807) 1 806 (true, (init pH807), (init pH807))) 807 404 true = true :=
  fin_run (runOK_init (prmOK_of_and H807_fin) true) (by decide) rfl H807_fin ptTest_fst
theorem I807_fin : (prmOK pI807 807 && intTest pI807 (runFrom pI807 (fmask pI807) (cmask pI807) (hmask pI807) 1 806 (true, (init pI807), (init pI807))) 807 17 false) = true := by
  decide +kernel
theorem I807_ok : RunOK pI807 807 (runFrom pI807 (fmask pI807) (cmask pI807) (hmask pI807) 1 806 (true, (init pI807), (init pI807))) ∧ intTest pI807 (runFrom pI807 (fmask pI807) (cmask pI807) (hmask pI807) 1 806 (true, (init pI807), (init pI807))) 807 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I807_fin) true) (by decide) rfl I807_fin intTest_fst
theorem link807 : linkOK pL807 pH807 pI807 = true := by decide +kernel
theorem cvx807 : ConvexBetweenHumps 807 :=
  cvx_of L807_ok H807_ok I807_ok link807 (by decide)

/-! ### `N = 808` -/

def pL808 : Prm := ⟨73, 34, 36, 810, 11, 18446744073709551616, 204378179104775370, 204378179104775370⟩
def pH808 : Prm := ⟨73, 34, 36, 810, 11, 18446744073709551616, 204382577151286474, 204382577151286474⟩
def pI808 : Prm := ⟨63, 31, 29, 810, 11, 18446744073709551616, 204378179104775370, 204382577151286474⟩
theorem L808_fin : (prmOK pL808 808 && ptTest pL808 (runFrom pL808 (fmask pL808) (cmask pL808) (hmask pL808) 1 807 (true, (init pL808), (init pL808))) 808 404 false) = true := by
  decide +kernel
theorem L808_ok : RunOK pL808 808 (runFrom pL808 (fmask pL808) (cmask pL808) (hmask pL808) 1 807 (true, (init pL808), (init pL808))) ∧ ptTest pL808 (runFrom pL808 (fmask pL808) (cmask pL808) (hmask pL808) 1 807 (true, (init pL808), (init pL808))) 808 404 false = true :=
  fin_run (runOK_init (prmOK_of_and L808_fin) true) (by decide) rfl L808_fin ptTest_fst
theorem H808_fin : (prmOK pH808 808 && ptTest pH808 (runFrom pH808 (fmask pH808) (cmask pH808) (hmask pH808) 1 807 (true, (init pH808), (init pH808))) 808 404 true) = true := by
  decide +kernel
theorem H808_ok : RunOK pH808 808 (runFrom pH808 (fmask pH808) (cmask pH808) (hmask pH808) 1 807 (true, (init pH808), (init pH808))) ∧ ptTest pH808 (runFrom pH808 (fmask pH808) (cmask pH808) (hmask pH808) 1 807 (true, (init pH808), (init pH808))) 808 404 true = true :=
  fin_run (runOK_init (prmOK_of_and H808_fin) true) (by decide) rfl H808_fin ptTest_fst
theorem I808_fin : (prmOK pI808 808 && intTest pI808 (runFrom pI808 (fmask pI808) (cmask pI808) (hmask pI808) 1 807 (true, (init pI808), (init pI808))) 808 17 true) = true := by
  decide +kernel
theorem I808_ok : RunOK pI808 808 (runFrom pI808 (fmask pI808) (cmask pI808) (hmask pI808) 1 807 (true, (init pI808), (init pI808))) ∧ intTest pI808 (runFrom pI808 (fmask pI808) (cmask pI808) (hmask pI808) 1 807 (true, (init pI808), (init pI808))) 808 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I808_fin) true) (by decide) rfl I808_fin intTest_fst
theorem link808 : linkOK pL808 pH808 pI808 = true := by decide +kernel
theorem cvx808 : ConvexBetweenHumps 808 :=
  cvx_of L808_ok H808_ok I808_ok link808 (by decide)
theorem cenlink808 : cenLinkOK pI808 808 = true := by decide +kernel
theorem cen808 : CenterUniqueMin 808 ∧ DipHyp 808 ∧ OnePointHyps 808 :=
  cen_of L808_ok H808_ok I808_ok link808 cenlink808

/-! ### `N = 809` -/

def pL809 : Prm := ⟨73, 34, 36, 811, 11, 18446744073709551616, 204178608866538375, 204178608866538375⟩
def pH809 : Prm := ⟨73, 34, 36, 811, 11, 18446744073709551616, 204183006913049479, 204183006913049479⟩
def pI809 : Prm := ⟨63, 31, 29, 811, 11, 18446744073709551616, 204178608866538375, 204183006913049479⟩
theorem L809_fin : (prmOK pL809 809 && ptTest pL809 (runFrom pL809 (fmask pL809) (cmask pL809) (hmask pL809) 1 808 (true, (init pL809), (init pL809))) 809 405 false) = true := by
  decide +kernel
theorem L809_ok : RunOK pL809 809 (runFrom pL809 (fmask pL809) (cmask pL809) (hmask pL809) 1 808 (true, (init pL809), (init pL809))) ∧ ptTest pL809 (runFrom pL809 (fmask pL809) (cmask pL809) (hmask pL809) 1 808 (true, (init pL809), (init pL809))) 809 405 false = true :=
  fin_run (runOK_init (prmOK_of_and L809_fin) true) (by decide) rfl L809_fin ptTest_fst
theorem H809_fin : (prmOK pH809 809 && ptTest pH809 (runFrom pH809 (fmask pH809) (cmask pH809) (hmask pH809) 1 808 (true, (init pH809), (init pH809))) 809 405 true) = true := by
  decide +kernel
theorem H809_ok : RunOK pH809 809 (runFrom pH809 (fmask pH809) (cmask pH809) (hmask pH809) 1 808 (true, (init pH809), (init pH809))) ∧ ptTest pH809 (runFrom pH809 (fmask pH809) (cmask pH809) (hmask pH809) 1 808 (true, (init pH809), (init pH809))) 809 405 true = true :=
  fin_run (runOK_init (prmOK_of_and H809_fin) true) (by decide) rfl H809_fin ptTest_fst
theorem I809_fin : (prmOK pI809 809 && intTest pI809 (runFrom pI809 (fmask pI809) (cmask pI809) (hmask pI809) 1 808 (true, (init pI809), (init pI809))) 809 17 false) = true := by
  decide +kernel
theorem I809_ok : RunOK pI809 809 (runFrom pI809 (fmask pI809) (cmask pI809) (hmask pI809) 1 808 (true, (init pI809), (init pI809))) ∧ intTest pI809 (runFrom pI809 (fmask pI809) (cmask pI809) (hmask pI809) 1 808 (true, (init pI809), (init pI809))) 809 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I809_fin) true) (by decide) rfl I809_fin intTest_fst
theorem link809 : linkOK pL809 pH809 pI809 = true := by decide +kernel
theorem cvx809 : ConvexBetweenHumps 809 :=
  cvx_of L809_ok H809_ok I809_ok link809 (by decide)

/-! ### `N = 810` -/

def pL810 : Prm := ⟨73, 34, 36, 812, 11, 18446744073709551616, 203979686510567092, 203979686510567092⟩
def pH810 : Prm := ⟨73, 34, 36, 812, 11, 18446744073709551616, 203984084557078196, 203984084557078196⟩
def pI810 : Prm := ⟨64, 31, 30, 812, 11, 18446744073709551616, 203979686510567092, 203984084557078196⟩
theorem L810_fin : (prmOK pL810 810 && ptTest pL810 (runFrom pL810 (fmask pL810) (cmask pL810) (hmask pL810) 1 809 (true, (init pL810), (init pL810))) 810 405 false) = true := by
  decide +kernel
theorem L810_ok : RunOK pL810 810 (runFrom pL810 (fmask pL810) (cmask pL810) (hmask pL810) 1 809 (true, (init pL810), (init pL810))) ∧ ptTest pL810 (runFrom pL810 (fmask pL810) (cmask pL810) (hmask pL810) 1 809 (true, (init pL810), (init pL810))) 810 405 false = true :=
  fin_run (runOK_init (prmOK_of_and L810_fin) true) (by decide) rfl L810_fin ptTest_fst
theorem H810_fin : (prmOK pH810 810 && ptTest pH810 (runFrom pH810 (fmask pH810) (cmask pH810) (hmask pH810) 1 809 (true, (init pH810), (init pH810))) 810 405 true) = true := by
  decide +kernel
theorem H810_ok : RunOK pH810 810 (runFrom pH810 (fmask pH810) (cmask pH810) (hmask pH810) 1 809 (true, (init pH810), (init pH810))) ∧ ptTest pH810 (runFrom pH810 (fmask pH810) (cmask pH810) (hmask pH810) 1 809 (true, (init pH810), (init pH810))) 810 405 true = true :=
  fin_run (runOK_init (prmOK_of_and H810_fin) true) (by decide) rfl H810_fin ptTest_fst
theorem I810_fin : (prmOK pI810 810 && intTest pI810 (runFrom pI810 (fmask pI810) (cmask pI810) (hmask pI810) 1 809 (true, (init pI810), (init pI810))) 810 17 true) = true := by
  decide +kernel
theorem I810_ok : RunOK pI810 810 (runFrom pI810 (fmask pI810) (cmask pI810) (hmask pI810) 1 809 (true, (init pI810), (init pI810))) ∧ intTest pI810 (runFrom pI810 (fmask pI810) (cmask pI810) (hmask pI810) 1 809 (true, (init pI810), (init pI810))) 810 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I810_fin) true) (by decide) rfl I810_fin intTest_fst
theorem link810 : linkOK pL810 pH810 pI810 = true := by decide +kernel
theorem cvx810 : ConvexBetweenHumps 810 :=
  cvx_of L810_ok H810_ok I810_ok link810 (by decide)
theorem cenlink810 : cenLinkOK pI810 810 = true := by decide +kernel
theorem cen810 : CenterUniqueMin 810 ∧ DipHyp 810 ∧ OnePointHyps 810 :=
  cen_of L810_ok H810_ok I810_ok link810 cenlink810

/-! ### `N = 811` -/

def pL811 : Prm := ⟨73, 34, 36, 813, 11, 18446744073709551616, 203780969750623613, 203780969750623613⟩
def pH811 : Prm := ⟨73, 34, 36, 813, 11, 18446744073709551616, 203785367797134717, 203785367797134717⟩
def pI811 : Prm := ⟨64, 31, 30, 813, 11, 18446744073709551616, 203780969750623613, 203785367797134717⟩
theorem L811_fin : (prmOK pL811 811 && ptTest pL811 (runFrom pL811 (fmask pL811) (cmask pL811) (hmask pL811) 1 810 (true, (init pL811), (init pL811))) 811 406 false) = true := by
  decide +kernel
theorem L811_ok : RunOK pL811 811 (runFrom pL811 (fmask pL811) (cmask pL811) (hmask pL811) 1 810 (true, (init pL811), (init pL811))) ∧ ptTest pL811 (runFrom pL811 (fmask pL811) (cmask pL811) (hmask pL811) 1 810 (true, (init pL811), (init pL811))) 811 406 false = true :=
  fin_run (runOK_init (prmOK_of_and L811_fin) true) (by decide) rfl L811_fin ptTest_fst
theorem H811_fin : (prmOK pH811 811 && ptTest pH811 (runFrom pH811 (fmask pH811) (cmask pH811) (hmask pH811) 1 810 (true, (init pH811), (init pH811))) 811 406 true) = true := by
  decide +kernel
theorem H811_ok : RunOK pH811 811 (runFrom pH811 (fmask pH811) (cmask pH811) (hmask pH811) 1 810 (true, (init pH811), (init pH811))) ∧ ptTest pH811 (runFrom pH811 (fmask pH811) (cmask pH811) (hmask pH811) 1 810 (true, (init pH811), (init pH811))) 811 406 true = true :=
  fin_run (runOK_init (prmOK_of_and H811_fin) true) (by decide) rfl H811_fin ptTest_fst
theorem I811_fin : (prmOK pI811 811 && intTest pI811 (runFrom pI811 (fmask pI811) (cmask pI811) (hmask pI811) 1 810 (true, (init pI811), (init pI811))) 811 17 false) = true := by
  decide +kernel
theorem I811_ok : RunOK pI811 811 (runFrom pI811 (fmask pI811) (cmask pI811) (hmask pI811) 1 810 (true, (init pI811), (init pI811))) ∧ intTest pI811 (runFrom pI811 (fmask pI811) (cmask pI811) (hmask pI811) 1 810 (true, (init pI811), (init pI811))) 811 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I811_fin) true) (by decide) rfl I811_fin intTest_fst
theorem link811 : linkOK pL811 pH811 pI811 = true := by decide +kernel
theorem cvx811 : ConvexBetweenHumps 811 :=
  cvx_of L811_ok H811_ok I811_ok link811 (by decide)

/-! ### `N = 812` -/

def pL812 : Prm := ⟨73, 34, 36, 814, 11, 18446744073709551616, 203582896381126771, 203582896381126771⟩
def pH812 : Prm := ⟨73, 34, 36, 814, 11, 18446744073709551616, 203587294427637875, 203587294427637875⟩
def pI812 : Prm := ⟨63, 31, 29, 814, 11, 18446744073709551616, 203582896381126771, 203587294427637875⟩
theorem L812_fin : (prmOK pL812 812 && ptTest pL812 (runFrom pL812 (fmask pL812) (cmask pL812) (hmask pL812) 1 811 (true, (init pL812), (init pL812))) 812 406 false) = true := by
  decide +kernel
theorem L812_ok : RunOK pL812 812 (runFrom pL812 (fmask pL812) (cmask pL812) (hmask pL812) 1 811 (true, (init pL812), (init pL812))) ∧ ptTest pL812 (runFrom pL812 (fmask pL812) (cmask pL812) (hmask pL812) 1 811 (true, (init pL812), (init pL812))) 812 406 false = true :=
  fin_run (runOK_init (prmOK_of_and L812_fin) true) (by decide) rfl L812_fin ptTest_fst
theorem H812_fin : (prmOK pH812 812 && ptTest pH812 (runFrom pH812 (fmask pH812) (cmask pH812) (hmask pH812) 1 811 (true, (init pH812), (init pH812))) 812 406 true) = true := by
  decide +kernel
theorem H812_ok : RunOK pH812 812 (runFrom pH812 (fmask pH812) (cmask pH812) (hmask pH812) 1 811 (true, (init pH812), (init pH812))) ∧ ptTest pH812 (runFrom pH812 (fmask pH812) (cmask pH812) (hmask pH812) 1 811 (true, (init pH812), (init pH812))) 812 406 true = true :=
  fin_run (runOK_init (prmOK_of_and H812_fin) true) (by decide) rfl H812_fin ptTest_fst
theorem I812_fin : (prmOK pI812 812 && intTest pI812 (runFrom pI812 (fmask pI812) (cmask pI812) (hmask pI812) 1 811 (true, (init pI812), (init pI812))) 812 17 true) = true := by
  decide +kernel
theorem I812_ok : RunOK pI812 812 (runFrom pI812 (fmask pI812) (cmask pI812) (hmask pI812) 1 811 (true, (init pI812), (init pI812))) ∧ intTest pI812 (runFrom pI812 (fmask pI812) (cmask pI812) (hmask pI812) 1 811 (true, (init pI812), (init pI812))) 812 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I812_fin) true) (by decide) rfl I812_fin intTest_fst
theorem link812 : linkOK pL812 pH812 pI812 = true := by decide +kernel
theorem cvx812 : ConvexBetweenHumps 812 :=
  cvx_of L812_ok H812_ok I812_ok link812 (by decide)
theorem cenlink812 : cenLinkOK pI812 812 = true := by decide +kernel
theorem cen812 : CenterUniqueMin 812 ∧ DipHyp 812 ∧ OnePointHyps 812 :=
  cen_of L812_ok H812_ok I812_ok link812 cenlink812

/-! ### `N = 813` -/

def pL813 : Prm := ⟨73, 34, 36, 815, 11, 18446744073709551616, 203385027439443878, 203385027439443878⟩
def pH813 : Prm := ⟨73, 34, 36, 815, 11, 18446744073709551616, 203389425485954982, 203389425485954982⟩
def pI813 : Prm := ⟨64, 31, 30, 815, 11, 18446744073709551616, 203385027439443878, 203389425485954982⟩
theorem L813_fin : (prmOK pL813 813 && ptTest pL813 (runFrom pL813 (fmask pL813) (cmask pL813) (hmask pL813) 1 812 (true, (init pL813), (init pL813))) 813 407 false) = true := by
  decide +kernel
theorem L813_ok : RunOK pL813 813 (runFrom pL813 (fmask pL813) (cmask pL813) (hmask pL813) 1 812 (true, (init pL813), (init pL813))) ∧ ptTest pL813 (runFrom pL813 (fmask pL813) (cmask pL813) (hmask pL813) 1 812 (true, (init pL813), (init pL813))) 813 407 false = true :=
  fin_run (runOK_init (prmOK_of_and L813_fin) true) (by decide) rfl L813_fin ptTest_fst
theorem H813_fin : (prmOK pH813 813 && ptTest pH813 (runFrom pH813 (fmask pH813) (cmask pH813) (hmask pH813) 1 812 (true, (init pH813), (init pH813))) 813 407 true) = true := by
  decide +kernel
theorem H813_ok : RunOK pH813 813 (runFrom pH813 (fmask pH813) (cmask pH813) (hmask pH813) 1 812 (true, (init pH813), (init pH813))) ∧ ptTest pH813 (runFrom pH813 (fmask pH813) (cmask pH813) (hmask pH813) 1 812 (true, (init pH813), (init pH813))) 813 407 true = true :=
  fin_run (runOK_init (prmOK_of_and H813_fin) true) (by decide) rfl H813_fin ptTest_fst
theorem I813_fin : (prmOK pI813 813 && intTest pI813 (runFrom pI813 (fmask pI813) (cmask pI813) (hmask pI813) 1 812 (true, (init pI813), (init pI813))) 813 17 false) = true := by
  decide +kernel
theorem I813_ok : RunOK pI813 813 (runFrom pI813 (fmask pI813) (cmask pI813) (hmask pI813) 1 812 (true, (init pI813), (init pI813))) ∧ intTest pI813 (runFrom pI813 (fmask pI813) (cmask pI813) (hmask pI813) 1 812 (true, (init pI813), (init pI813))) 813 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I813_fin) true) (by decide) rfl I813_fin intTest_fst
theorem link813 : linkOK pL813 pH813 pI813 = true := by decide +kernel
theorem cvx813 : ConvexBetweenHumps 813 :=
  cvx_of L813_ok H813_ok I813_ok link813 (by decide)

/-! ### `N = 814` -/

def pL814 : Prm := ⟨73, 34, 36, 816, 11, 18446744073709551616, 203187797438410230, 203187797438410230⟩
def pH814 : Prm := ⟨73, 34, 36, 816, 11, 18446744073709551616, 203192195484921334, 203192195484921334⟩
def pI814 : Prm := ⟨64, 31, 30, 816, 11, 18446744073709551616, 203187797438410230, 203192195484921334⟩
theorem L814_fin : (prmOK pL814 814 && ptTest pL814 (runFrom pL814 (fmask pL814) (cmask pL814) (hmask pL814) 1 813 (true, (init pL814), (init pL814))) 814 407 false) = true := by
  decide +kernel
theorem L814_ok : RunOK pL814 814 (runFrom pL814 (fmask pL814) (cmask pL814) (hmask pL814) 1 813 (true, (init pL814), (init pL814))) ∧ ptTest pL814 (runFrom pL814 (fmask pL814) (cmask pL814) (hmask pL814) 1 813 (true, (init pL814), (init pL814))) 814 407 false = true :=
  fin_run (runOK_init (prmOK_of_and L814_fin) true) (by decide) rfl L814_fin ptTest_fst
theorem H814_fin : (prmOK pH814 814 && ptTest pH814 (runFrom pH814 (fmask pH814) (cmask pH814) (hmask pH814) 1 813 (true, (init pH814), (init pH814))) 814 407 true) = true := by
  decide +kernel
theorem H814_ok : RunOK pH814 814 (runFrom pH814 (fmask pH814) (cmask pH814) (hmask pH814) 1 813 (true, (init pH814), (init pH814))) ∧ ptTest pH814 (runFrom pH814 (fmask pH814) (cmask pH814) (hmask pH814) 1 813 (true, (init pH814), (init pH814))) 814 407 true = true :=
  fin_run (runOK_init (prmOK_of_and H814_fin) true) (by decide) rfl H814_fin ptTest_fst
theorem I814_fin : (prmOK pI814 814 && intTest pI814 (runFrom pI814 (fmask pI814) (cmask pI814) (hmask pI814) 1 813 (true, (init pI814), (init pI814))) 814 17 true) = true := by
  decide +kernel
theorem I814_ok : RunOK pI814 814 (runFrom pI814 (fmask pI814) (cmask pI814) (hmask pI814) 1 813 (true, (init pI814), (init pI814))) ∧ intTest pI814 (runFrom pI814 (fmask pI814) (cmask pI814) (hmask pI814) 1 813 (true, (init pI814), (init pI814))) 814 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I814_fin) true) (by decide) rfl I814_fin intTest_fst
theorem link814 : linkOK pL814 pH814 pI814 = true := by decide +kernel
theorem cvx814 : ConvexBetweenHumps 814 :=
  cvx_of L814_ok H814_ok I814_ok link814 (by decide)
theorem cenlink814 : cenLinkOK pI814 814 = true := by decide +kernel
theorem cen814 : CenterUniqueMin 814 ∧ DipHyp 814 ∧ OnePointHyps 814 :=
  cen_of L814_ok H814_ok I814_ok link814 cenlink814

/-! ### `N = 815` -/

def pL815 : Prm := ⟨73, 34, 36, 817, 11, 18446744073709551616, 202990770705868006, 202990770705868006⟩
def pH815 : Prm := ⟨73, 34, 36, 817, 11, 18446744073709551616, 202995168752379110, 202995168752379110⟩
def pI815 : Prm := ⟨64, 31, 30, 817, 11, 18446744073709551616, 202990770705868006, 202995168752379110⟩
theorem L815_fin : (prmOK pL815 815 && ptTest pL815 (runFrom pL815 (fmask pL815) (cmask pL815) (hmask pL815) 1 814 (true, (init pL815), (init pL815))) 815 408 false) = true := by
  decide +kernel
theorem L815_ok : RunOK pL815 815 (runFrom pL815 (fmask pL815) (cmask pL815) (hmask pL815) 1 814 (true, (init pL815), (init pL815))) ∧ ptTest pL815 (runFrom pL815 (fmask pL815) (cmask pL815) (hmask pL815) 1 814 (true, (init pL815), (init pL815))) 815 408 false = true :=
  fin_run (runOK_init (prmOK_of_and L815_fin) true) (by decide) rfl L815_fin ptTest_fst
theorem H815_fin : (prmOK pH815 815 && ptTest pH815 (runFrom pH815 (fmask pH815) (cmask pH815) (hmask pH815) 1 814 (true, (init pH815), (init pH815))) 815 408 true) = true := by
  decide +kernel
theorem H815_ok : RunOK pH815 815 (runFrom pH815 (fmask pH815) (cmask pH815) (hmask pH815) 1 814 (true, (init pH815), (init pH815))) ∧ ptTest pH815 (runFrom pH815 (fmask pH815) (cmask pH815) (hmask pH815) 1 814 (true, (init pH815), (init pH815))) 815 408 true = true :=
  fin_run (runOK_init (prmOK_of_and H815_fin) true) (by decide) rfl H815_fin ptTest_fst
theorem I815_fin : (prmOK pI815 815 && intTest pI815 (runFrom pI815 (fmask pI815) (cmask pI815) (hmask pI815) 1 814 (true, (init pI815), (init pI815))) 815 17 false) = true := by
  decide +kernel
theorem I815_ok : RunOK pI815 815 (runFrom pI815 (fmask pI815) (cmask pI815) (hmask pI815) 1 814 (true, (init pI815), (init pI815))) ∧ intTest pI815 (runFrom pI815 (fmask pI815) (cmask pI815) (hmask pI815) 1 814 (true, (init pI815), (init pI815))) 815 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I815_fin) true) (by decide) rfl I815_fin intTest_fst
theorem link815 : linkOK pL815 pH815 pI815 = true := by decide +kernel
theorem cvx815 : ConvexBetweenHumps 815 :=
  cvx_of L815_ok H815_ok I815_ok link815 (by decide)

/-! ### `N = 816` -/

def pL816 : Prm := ⟨73, 34, 36, 818, 11, 18446744073709551616, 202794378505645914, 202794378505645914⟩
def pH816 : Prm := ⟨73, 34, 36, 818, 11, 18446744073709551616, 202798776552157018, 202798776552157018⟩
def pI816 : Prm := ⟨64, 31, 30, 818, 11, 18446744073709551616, 202794378505645914, 202798776552157018⟩
theorem L816_fin : (prmOK pL816 816 && ptTest pL816 (runFrom pL816 (fmask pL816) (cmask pL816) (hmask pL816) 1 815 (true, (init pL816), (init pL816))) 816 408 false) = true := by
  decide +kernel
theorem L816_ok : RunOK pL816 816 (runFrom pL816 (fmask pL816) (cmask pL816) (hmask pL816) 1 815 (true, (init pL816), (init pL816))) ∧ ptTest pL816 (runFrom pL816 (fmask pL816) (cmask pL816) (hmask pL816) 1 815 (true, (init pL816), (init pL816))) 816 408 false = true :=
  fin_run (runOK_init (prmOK_of_and L816_fin) true) (by decide) rfl L816_fin ptTest_fst
theorem H816_fin : (prmOK pH816 816 && ptTest pH816 (runFrom pH816 (fmask pH816) (cmask pH816) (hmask pH816) 1 815 (true, (init pH816), (init pH816))) 816 408 true) = true := by
  decide +kernel
theorem H816_ok : RunOK pH816 816 (runFrom pH816 (fmask pH816) (cmask pH816) (hmask pH816) 1 815 (true, (init pH816), (init pH816))) ∧ ptTest pH816 (runFrom pH816 (fmask pH816) (cmask pH816) (hmask pH816) 1 815 (true, (init pH816), (init pH816))) 816 408 true = true :=
  fin_run (runOK_init (prmOK_of_and H816_fin) true) (by decide) rfl H816_fin ptTest_fst
theorem I816_fin : (prmOK pI816 816 && intTest pI816 (runFrom pI816 (fmask pI816) (cmask pI816) (hmask pI816) 1 815 (true, (init pI816), (init pI816))) 816 17 true) = true := by
  decide +kernel
theorem I816_ok : RunOK pI816 816 (runFrom pI816 (fmask pI816) (cmask pI816) (hmask pI816) 1 815 (true, (init pI816), (init pI816))) ∧ intTest pI816 (runFrom pI816 (fmask pI816) (cmask pI816) (hmask pI816) 1 815 (true, (init pI816), (init pI816))) 816 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I816_fin) true) (by decide) rfl I816_fin intTest_fst
theorem link816 : linkOK pL816 pH816 pI816 = true := by decide +kernel
theorem cvx816 : ConvexBetweenHumps 816 :=
  cvx_of L816_ok H816_ok I816_ok link816 (by decide)
theorem cenlink816 : cenLinkOK pI816 816 = true := by decide +kernel
theorem cen816 : CenterUniqueMin 816 ∧ DipHyp 816 ∧ OnePointHyps 816 :=
  cen_of L816_ok H816_ok I816_ok link816 cenlink816

/-! ### `N = 817` -/

def pL817 : Prm := ⟨73, 34, 36, 819, 11, 18446744073709551616, 202598188423465605, 202598188423465605⟩
def pH817 : Prm := ⟨73, 34, 36, 819, 11, 18446744073709551616, 202602586469976709, 202602586469976709⟩
def pI817 : Prm := ⟨64, 31, 30, 819, 11, 18446744073709551616, 202598188423465605, 202602586469976709⟩
theorem L817_fin : (prmOK pL817 817 && ptTest pL817 (runFrom pL817 (fmask pL817) (cmask pL817) (hmask pL817) 1 816 (true, (init pL817), (init pL817))) 817 409 false) = true := by
  decide +kernel
theorem L817_ok : RunOK pL817 817 (runFrom pL817 (fmask pL817) (cmask pL817) (hmask pL817) 1 816 (true, (init pL817), (init pL817))) ∧ ptTest pL817 (runFrom pL817 (fmask pL817) (cmask pL817) (hmask pL817) 1 816 (true, (init pL817), (init pL817))) 817 409 false = true :=
  fin_run (runOK_init (prmOK_of_and L817_fin) true) (by decide) rfl L817_fin ptTest_fst
theorem H817_fin : (prmOK pH817 817 && ptTest pH817 (runFrom pH817 (fmask pH817) (cmask pH817) (hmask pH817) 1 816 (true, (init pH817), (init pH817))) 817 409 true) = true := by
  decide +kernel
theorem H817_ok : RunOK pH817 817 (runFrom pH817 (fmask pH817) (cmask pH817) (hmask pH817) 1 816 (true, (init pH817), (init pH817))) ∧ ptTest pH817 (runFrom pH817 (fmask pH817) (cmask pH817) (hmask pH817) 1 816 (true, (init pH817), (init pH817))) 817 409 true = true :=
  fin_run (runOK_init (prmOK_of_and H817_fin) true) (by decide) rfl H817_fin ptTest_fst
theorem I817_fin : (prmOK pI817 817 && intTest pI817 (runFrom pI817 (fmask pI817) (cmask pI817) (hmask pI817) 1 816 (true, (init pI817), (init pI817))) 817 17 false) = true := by
  decide +kernel
theorem I817_ok : RunOK pI817 817 (runFrom pI817 (fmask pI817) (cmask pI817) (hmask pI817) 1 816 (true, (init pI817), (init pI817))) ∧ intTest pI817 (runFrom pI817 (fmask pI817) (cmask pI817) (hmask pI817) 1 816 (true, (init pI817), (init pI817))) 817 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I817_fin) true) (by decide) rfl I817_fin intTest_fst
theorem link817 : linkOK pL817 pH817 pI817 = true := by decide +kernel
theorem cvx817 : ConvexBetweenHumps 817 :=
  cvx_of L817_ok H817_ok I817_ok link817 (by decide)

/-! ### `N = 818` -/

def pL818 : Prm := ⟨73, 34, 36, 820, 11, 18446744073709551616, 202402628506301877, 202402628506301877⟩
def pH818 : Prm := ⟨73, 34, 36, 820, 11, 18446744073709551616, 202407026552812981, 202407026552812981⟩
def pI818 : Prm := ⟨64, 31, 30, 820, 11, 18446744073709551616, 202402628506301877, 202407026552812981⟩
theorem L818_fin : (prmOK pL818 818 && ptTest pL818 (runFrom pL818 (fmask pL818) (cmask pL818) (hmask pL818) 1 817 (true, (init pL818), (init pL818))) 818 409 false) = true := by
  decide +kernel
theorem L818_ok : RunOK pL818 818 (runFrom pL818 (fmask pL818) (cmask pL818) (hmask pL818) 1 817 (true, (init pL818), (init pL818))) ∧ ptTest pL818 (runFrom pL818 (fmask pL818) (cmask pL818) (hmask pL818) 1 817 (true, (init pL818), (init pL818))) 818 409 false = true :=
  fin_run (runOK_init (prmOK_of_and L818_fin) true) (by decide) rfl L818_fin ptTest_fst
theorem H818_fin : (prmOK pH818 818 && ptTest pH818 (runFrom pH818 (fmask pH818) (cmask pH818) (hmask pH818) 1 817 (true, (init pH818), (init pH818))) 818 409 true) = true := by
  decide +kernel
theorem H818_ok : RunOK pH818 818 (runFrom pH818 (fmask pH818) (cmask pH818) (hmask pH818) 1 817 (true, (init pH818), (init pH818))) ∧ ptTest pH818 (runFrom pH818 (fmask pH818) (cmask pH818) (hmask pH818) 1 817 (true, (init pH818), (init pH818))) 818 409 true = true :=
  fin_run (runOK_init (prmOK_of_and H818_fin) true) (by decide) rfl H818_fin ptTest_fst
theorem I818_fin : (prmOK pI818 818 && intTest pI818 (runFrom pI818 (fmask pI818) (cmask pI818) (hmask pI818) 1 817 (true, (init pI818), (init pI818))) 818 17 true) = true := by
  decide +kernel
theorem I818_ok : RunOK pI818 818 (runFrom pI818 (fmask pI818) (cmask pI818) (hmask pI818) 1 817 (true, (init pI818), (init pI818))) ∧ intTest pI818 (runFrom pI818 (fmask pI818) (cmask pI818) (hmask pI818) 1 817 (true, (init pI818), (init pI818))) 818 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I818_fin) true) (by decide) rfl I818_fin intTest_fst
theorem link818 : linkOK pL818 pH818 pI818 = true := by decide +kernel
theorem cvx818 : ConvexBetweenHumps 818 :=
  cvx_of L818_ok H818_ok I818_ok link818 (by decide)
theorem cenlink818 : cenLinkOK pI818 818 = true := by decide +kernel
theorem cen818 : CenterUniqueMin 818 ∧ DipHyp 818 ∧ OnePointHyps 818 :=
  cen_of L818_ok H818_ok I818_ok link818 cenlink818

/-! ### `N = 819` -/

def pL819 : Prm := ⟨73, 34, 36, 821, 11, 18446744073709551616, 202207269565437154, 202207269565437154⟩
def pH819 : Prm := ⟨73, 34, 36, 821, 11, 18446744073709551616, 202211667611948258, 202211667611948258⟩
def pI819 : Prm := ⟨64, 31, 30, 821, 11, 18446744073709551616, 202207269565437154, 202211667611948258⟩
theorem L819_fin : (prmOK pL819 819 && ptTest pL819 (runFrom pL819 (fmask pL819) (cmask pL819) (hmask pL819) 1 818 (true, (init pL819), (init pL819))) 819 410 false) = true := by
  decide +kernel
theorem L819_ok : RunOK pL819 819 (runFrom pL819 (fmask pL819) (cmask pL819) (hmask pL819) 1 818 (true, (init pL819), (init pL819))) ∧ ptTest pL819 (runFrom pL819 (fmask pL819) (cmask pL819) (hmask pL819) 1 818 (true, (init pL819), (init pL819))) 819 410 false = true :=
  fin_run (runOK_init (prmOK_of_and L819_fin) true) (by decide) rfl L819_fin ptTest_fst
theorem H819_fin : (prmOK pH819 819 && ptTest pH819 (runFrom pH819 (fmask pH819) (cmask pH819) (hmask pH819) 1 818 (true, (init pH819), (init pH819))) 819 410 true) = true := by
  decide +kernel
theorem H819_ok : RunOK pH819 819 (runFrom pH819 (fmask pH819) (cmask pH819) (hmask pH819) 1 818 (true, (init pH819), (init pH819))) ∧ ptTest pH819 (runFrom pH819 (fmask pH819) (cmask pH819) (hmask pH819) 1 818 (true, (init pH819), (init pH819))) 819 410 true = true :=
  fin_run (runOK_init (prmOK_of_and H819_fin) true) (by decide) rfl H819_fin ptTest_fst
theorem I819_fin : (prmOK pI819 819 && intTest pI819 (runFrom pI819 (fmask pI819) (cmask pI819) (hmask pI819) 1 818 (true, (init pI819), (init pI819))) 819 17 false) = true := by
  decide +kernel
theorem I819_ok : RunOK pI819 819 (runFrom pI819 (fmask pI819) (cmask pI819) (hmask pI819) 1 818 (true, (init pI819), (init pI819))) ∧ intTest pI819 (runFrom pI819 (fmask pI819) (cmask pI819) (hmask pI819) 1 818 (true, (init pI819), (init pI819))) 819 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I819_fin) true) (by decide) rfl I819_fin intTest_fst
theorem link819 : linkOK pL819 pH819 pI819 = true := by decide +kernel
theorem cvx819 : ConvexBetweenHumps 819 :=
  cvx_of L819_ok H819_ok I819_ok link819 (by decide)

/-! ### `N = 820` -/

def pL820 : Prm := ⟨73, 34, 36, 822, 11, 18446744073709551616, 202012536462831401, 202012536462831401⟩
def pH820 : Prm := ⟨73, 34, 36, 822, 11, 18446744073709551616, 202016934509342505, 202016934509342505⟩
def pI820 : Prm := ⟨64, 31, 30, 822, 11, 18446744073709551616, 202012536462831401, 202016934509342505⟩
theorem L820_fin : (prmOK pL820 820 && ptTest pL820 (runFrom pL820 (fmask pL820) (cmask pL820) (hmask pL820) 1 819 (true, (init pL820), (init pL820))) 820 410 false) = true := by
  decide +kernel
theorem L820_ok : RunOK pL820 820 (runFrom pL820 (fmask pL820) (cmask pL820) (hmask pL820) 1 819 (true, (init pL820), (init pL820))) ∧ ptTest pL820 (runFrom pL820 (fmask pL820) (cmask pL820) (hmask pL820) 1 819 (true, (init pL820), (init pL820))) 820 410 false = true :=
  fin_run (runOK_init (prmOK_of_and L820_fin) true) (by decide) rfl L820_fin ptTest_fst
theorem H820_fin : (prmOK pH820 820 && ptTest pH820 (runFrom pH820 (fmask pH820) (cmask pH820) (hmask pH820) 1 819 (true, (init pH820), (init pH820))) 820 410 true) = true := by
  decide +kernel
theorem H820_ok : RunOK pH820 820 (runFrom pH820 (fmask pH820) (cmask pH820) (hmask pH820) 1 819 (true, (init pH820), (init pH820))) ∧ ptTest pH820 (runFrom pH820 (fmask pH820) (cmask pH820) (hmask pH820) 1 819 (true, (init pH820), (init pH820))) 820 410 true = true :=
  fin_run (runOK_init (prmOK_of_and H820_fin) true) (by decide) rfl H820_fin ptTest_fst
theorem I820_fin : (prmOK pI820 820 && intTest pI820 (runFrom pI820 (fmask pI820) (cmask pI820) (hmask pI820) 1 819 (true, (init pI820), (init pI820))) 820 17 true) = true := by
  decide +kernel
theorem I820_ok : RunOK pI820 820 (runFrom pI820 (fmask pI820) (cmask pI820) (hmask pI820) 1 819 (true, (init pI820), (init pI820))) ∧ intTest pI820 (runFrom pI820 (fmask pI820) (cmask pI820) (hmask pI820) 1 819 (true, (init pI820), (init pI820))) 820 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I820_fin) true) (by decide) rfl I820_fin intTest_fst
theorem link820 : linkOK pL820 pH820 pI820 = true := by decide +kernel
theorem cvx820 : ConvexBetweenHumps 820 :=
  cvx_of L820_ok H820_ok I820_ok link820 (by decide)
theorem cenlink820 : cenLinkOK pI820 820 = true := by decide +kernel
theorem cen820 : CenterUniqueMin 820 ∧ DipHyp 820 ∧ OnePointHyps 820 :=
  cen_of L820_ok H820_ok I820_ok link820 cenlink820

/-! ### `N = 821` -/

def pL821 : Prm := ⟨73, 34, 36, 823, 11, 18446744073709551616, 201818003203470292, 201818003203470292⟩
def pH821 : Prm := ⟨73, 34, 36, 823, 11, 18446744073709551616, 201822401249981396, 201822401249981396⟩
def pI821 : Prm := ⟨64, 31, 30, 823, 11, 18446744073709551616, 201818003203470292, 201822401249981396⟩
theorem L821_fin : (prmOK pL821 821 && ptTest pL821 (runFrom pL821 (fmask pL821) (cmask pL821) (hmask pL821) 1 820 (true, (init pL821), (init pL821))) 821 411 false) = true := by
  decide +kernel
theorem L821_ok : RunOK pL821 821 (runFrom pL821 (fmask pL821) (cmask pL821) (hmask pL821) 1 820 (true, (init pL821), (init pL821))) ∧ ptTest pL821 (runFrom pL821 (fmask pL821) (cmask pL821) (hmask pL821) 1 820 (true, (init pL821), (init pL821))) 821 411 false = true :=
  fin_run (runOK_init (prmOK_of_and L821_fin) true) (by decide) rfl L821_fin ptTest_fst
theorem H821_fin : (prmOK pH821 821 && ptTest pH821 (runFrom pH821 (fmask pH821) (cmask pH821) (hmask pH821) 1 820 (true, (init pH821), (init pH821))) 821 411 true) = true := by
  decide +kernel
theorem H821_ok : RunOK pH821 821 (runFrom pH821 (fmask pH821) (cmask pH821) (hmask pH821) 1 820 (true, (init pH821), (init pH821))) ∧ ptTest pH821 (runFrom pH821 (fmask pH821) (cmask pH821) (hmask pH821) 1 820 (true, (init pH821), (init pH821))) 821 411 true = true :=
  fin_run (runOK_init (prmOK_of_and H821_fin) true) (by decide) rfl H821_fin ptTest_fst
theorem I821_fin : (prmOK pI821 821 && intTest pI821 (runFrom pI821 (fmask pI821) (cmask pI821) (hmask pI821) 1 820 (true, (init pI821), (init pI821))) 821 17 false) = true := by
  decide +kernel
theorem I821_ok : RunOK pI821 821 (runFrom pI821 (fmask pI821) (cmask pI821) (hmask pI821) 1 820 (true, (init pI821), (init pI821))) ∧ intTest pI821 (runFrom pI821 (fmask pI821) (cmask pI821) (hmask pI821) 1 820 (true, (init pI821), (init pI821))) 821 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I821_fin) true) (by decide) rfl I821_fin intTest_fst
theorem link821 : linkOK pL821 pH821 pI821 = true := by decide +kernel
theorem cvx821 : ConvexBetweenHumps 821 :=
  cvx_of L821_ok H821_ok I821_ok link821 (by decide)

/-! ### `N = 822` -/

def pL822 : Prm := ⟨73, 34, 36, 824, 11, 18446744073709551616, 201624091495639979, 201624091495639979⟩
def pH822 : Prm := ⟨73, 34, 36, 824, 11, 18446744073709551616, 201628489542151083, 201628489542151083⟩
def pI822 : Prm := ⟨64, 31, 30, 824, 11, 18446744073709551616, 201624091495639979, 201628489542151083⟩
theorem L822_fin : (prmOK pL822 822 && ptTest pL822 (runFrom pL822 (fmask pL822) (cmask pL822) (hmask pL822) 1 821 (true, (init pL822), (init pL822))) 822 411 false) = true := by
  decide +kernel
theorem L822_ok : RunOK pL822 822 (runFrom pL822 (fmask pL822) (cmask pL822) (hmask pL822) 1 821 (true, (init pL822), (init pL822))) ∧ ptTest pL822 (runFrom pL822 (fmask pL822) (cmask pL822) (hmask pL822) 1 821 (true, (init pL822), (init pL822))) 822 411 false = true :=
  fin_run (runOK_init (prmOK_of_and L822_fin) true) (by decide) rfl L822_fin ptTest_fst
theorem H822_fin : (prmOK pH822 822 && ptTest pH822 (runFrom pH822 (fmask pH822) (cmask pH822) (hmask pH822) 1 821 (true, (init pH822), (init pH822))) 822 411 true) = true := by
  decide +kernel
theorem H822_ok : RunOK pH822 822 (runFrom pH822 (fmask pH822) (cmask pH822) (hmask pH822) 1 821 (true, (init pH822), (init pH822))) ∧ ptTest pH822 (runFrom pH822 (fmask pH822) (cmask pH822) (hmask pH822) 1 821 (true, (init pH822), (init pH822))) 822 411 true = true :=
  fin_run (runOK_init (prmOK_of_and H822_fin) true) (by decide) rfl H822_fin ptTest_fst
theorem I822_fin : (prmOK pI822 822 && intTest pI822 (runFrom pI822 (fmask pI822) (cmask pI822) (hmask pI822) 1 821 (true, (init pI822), (init pI822))) 822 17 true) = true := by
  decide +kernel
theorem I822_ok : RunOK pI822 822 (runFrom pI822 (fmask pI822) (cmask pI822) (hmask pI822) 1 821 (true, (init pI822), (init pI822))) ∧ intTest pI822 (runFrom pI822 (fmask pI822) (cmask pI822) (hmask pI822) 1 821 (true, (init pI822), (init pI822))) 822 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I822_fin) true) (by decide) rfl I822_fin intTest_fst
theorem link822 : linkOK pL822 pH822 pI822 = true := by decide +kernel
theorem cvx822 : ConvexBetweenHumps 822 :=
  cvx_of L822_ok H822_ok I822_ok link822 (by decide)
theorem cenlink822 : cenLinkOK pI822 822 = true := by decide +kernel
theorem cen822 : CenterUniqueMin 822 ∧ DipHyp 822 ∧ OnePointHyps 822 :=
  cen_of L822_ok H822_ok I822_ok link822 cenlink822

/-! ### `N = 823` -/

def pL823 : Prm := ⟨73, 34, 36, 825, 11, 18446744073709551616, 201430378506596132, 201430378506596132⟩
def pH823 : Prm := ⟨73, 34, 36, 825, 11, 18446744073709551616, 201434776553107236, 201434776553107236⟩
def pI823 : Prm := ⟨64, 31, 30, 825, 11, 18446744073709551616, 201430378506596132, 201434776553107236⟩
theorem L823_fin : (prmOK pL823 823 && ptTest pL823 (runFrom pL823 (fmask pL823) (cmask pL823) (hmask pL823) 1 822 (true, (init pL823), (init pL823))) 823 412 false) = true := by
  decide +kernel
theorem L823_ok : RunOK pL823 823 (runFrom pL823 (fmask pL823) (cmask pL823) (hmask pL823) 1 822 (true, (init pL823), (init pL823))) ∧ ptTest pL823 (runFrom pL823 (fmask pL823) (cmask pL823) (hmask pL823) 1 822 (true, (init pL823), (init pL823))) 823 412 false = true :=
  fin_run (runOK_init (prmOK_of_and L823_fin) true) (by decide) rfl L823_fin ptTest_fst
theorem H823_fin : (prmOK pH823 823 && ptTest pH823 (runFrom pH823 (fmask pH823) (cmask pH823) (hmask pH823) 1 822 (true, (init pH823), (init pH823))) 823 412 true) = true := by
  decide +kernel
theorem H823_ok : RunOK pH823 823 (runFrom pH823 (fmask pH823) (cmask pH823) (hmask pH823) 1 822 (true, (init pH823), (init pH823))) ∧ ptTest pH823 (runFrom pH823 (fmask pH823) (cmask pH823) (hmask pH823) 1 822 (true, (init pH823), (init pH823))) 823 412 true = true :=
  fin_run (runOK_init (prmOK_of_and H823_fin) true) (by decide) rfl H823_fin ptTest_fst
theorem I823_fin : (prmOK pI823 823 && intTest pI823 (runFrom pI823 (fmask pI823) (cmask pI823) (hmask pI823) 1 822 (true, (init pI823), (init pI823))) 823 17 false) = true := by
  decide +kernel
theorem I823_ok : RunOK pI823 823 (runFrom pI823 (fmask pI823) (cmask pI823) (hmask pI823) 1 822 (true, (init pI823), (init pI823))) ∧ intTest pI823 (runFrom pI823 (fmask pI823) (cmask pI823) (hmask pI823) 1 822 (true, (init pI823), (init pI823))) 823 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I823_fin) true) (by decide) rfl I823_fin intTest_fst
theorem link823 : linkOK pL823 pH823 pI823 = true := by decide +kernel
theorem cvx823 : ConvexBetweenHumps 823 :=
  cvx_of L823_ok H823_ok I823_ok link823 (by decide)

/-! ### `N = 824` -/

def pL824 : Prm := ⟨75, 35, 37, 826, 11, 18446744073709551616, 201238382333550947, 201238382333550947⟩
def pH824 : Prm := ⟨75, 35, 37, 826, 11, 18446744073709551616, 201240581356806499, 201240581356806499⟩
def pI824 : Prm := ⟨62, 31, 28, 826, 11, 18446744073709551616, 201238382333550947, 201240581356806499⟩
theorem L824_fin : (prmOK pL824 824 && ptTest pL824 (runFrom pL824 (fmask pL824) (cmask pL824) (hmask pL824) 1 823 (true, (init pL824), (init pL824))) 824 412 false) = true := by
  decide +kernel
theorem L824_ok : RunOK pL824 824 (runFrom pL824 (fmask pL824) (cmask pL824) (hmask pL824) 1 823 (true, (init pL824), (init pL824))) ∧ ptTest pL824 (runFrom pL824 (fmask pL824) (cmask pL824) (hmask pL824) 1 823 (true, (init pL824), (init pL824))) 824 412 false = true :=
  fin_run (runOK_init (prmOK_of_and L824_fin) true) (by decide) rfl L824_fin ptTest_fst
theorem H824_fin : (prmOK pH824 824 && ptTest pH824 (runFrom pH824 (fmask pH824) (cmask pH824) (hmask pH824) 1 823 (true, (init pH824), (init pH824))) 824 412 true) = true := by
  decide +kernel
theorem H824_ok : RunOK pH824 824 (runFrom pH824 (fmask pH824) (cmask pH824) (hmask pH824) 1 823 (true, (init pH824), (init pH824))) ∧ ptTest pH824 (runFrom pH824 (fmask pH824) (cmask pH824) (hmask pH824) 1 823 (true, (init pH824), (init pH824))) 824 412 true = true :=
  fin_run (runOK_init (prmOK_of_and H824_fin) true) (by decide) rfl H824_fin ptTest_fst
theorem I824_fin : (prmOK pI824 824 && intTest pI824 (runFrom pI824 (fmask pI824) (cmask pI824) (hmask pI824) 1 823 (true, (init pI824), (init pI824))) 824 17 true) = true := by
  decide +kernel
theorem I824_ok : RunOK pI824 824 (runFrom pI824 (fmask pI824) (cmask pI824) (hmask pI824) 1 823 (true, (init pI824), (init pI824))) ∧ intTest pI824 (runFrom pI824 (fmask pI824) (cmask pI824) (hmask pI824) 1 823 (true, (init pI824), (init pI824))) 824 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I824_fin) true) (by decide) rfl I824_fin intTest_fst
theorem link824 : linkOK pL824 pH824 pI824 = true := by decide +kernel
theorem cvx824 : ConvexBetweenHumps 824 :=
  cvx_of L824_ok H824_ok I824_ok link824 (by decide)
theorem cenlink824 : cenLinkOK pI824 824 = true := by decide +kernel
theorem cen824 : CenterUniqueMin 824 ∧ DipHyp 824 ∧ OnePointHyps 824 :=
  cen_of L824_ok H824_ok I824_ok link824 cenlink824

/-! ### `N = 825` -/

def pL825 : Prm := ⟨75, 35, 37, 827, 11, 18446744073709551616, 201045484251747116, 201045484251747116⟩
def pH825 : Prm := ⟨75, 35, 37, 827, 11, 18446744073709551616, 201047683275002668, 201047683275002668⟩
def pI825 : Prm := ⟨62, 31, 28, 827, 11, 18446744073709551616, 201045484251747116, 201047683275002668⟩
theorem L825_fin : (prmOK pL825 825 && ptTest pL825 (runFrom pL825 (fmask pL825) (cmask pL825) (hmask pL825) 1 824 (true, (init pL825), (init pL825))) 825 413 false) = true := by
  decide +kernel
theorem L825_ok : RunOK pL825 825 (runFrom pL825 (fmask pL825) (cmask pL825) (hmask pL825) 1 824 (true, (init pL825), (init pL825))) ∧ ptTest pL825 (runFrom pL825 (fmask pL825) (cmask pL825) (hmask pL825) 1 824 (true, (init pL825), (init pL825))) 825 413 false = true :=
  fin_run (runOK_init (prmOK_of_and L825_fin) true) (by decide) rfl L825_fin ptTest_fst
theorem H825_fin : (prmOK pH825 825 && ptTest pH825 (runFrom pH825 (fmask pH825) (cmask pH825) (hmask pH825) 1 824 (true, (init pH825), (init pH825))) 825 413 true) = true := by
  decide +kernel
theorem H825_ok : RunOK pH825 825 (runFrom pH825 (fmask pH825) (cmask pH825) (hmask pH825) 1 824 (true, (init pH825), (init pH825))) ∧ ptTest pH825 (runFrom pH825 (fmask pH825) (cmask pH825) (hmask pH825) 1 824 (true, (init pH825), (init pH825))) 825 413 true = true :=
  fin_run (runOK_init (prmOK_of_and H825_fin) true) (by decide) rfl H825_fin ptTest_fst
theorem I825_fin : (prmOK pI825 825 && intTest pI825 (runFrom pI825 (fmask pI825) (cmask pI825) (hmask pI825) 1 824 (true, (init pI825), (init pI825))) 825 17 false) = true := by
  decide +kernel
theorem I825_ok : RunOK pI825 825 (runFrom pI825 (fmask pI825) (cmask pI825) (hmask pI825) 1 824 (true, (init pI825), (init pI825))) ∧ intTest pI825 (runFrom pI825 (fmask pI825) (cmask pI825) (hmask pI825) 1 824 (true, (init pI825), (init pI825))) 825 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I825_fin) true) (by decide) rfl I825_fin intTest_fst
theorem link825 : linkOK pL825 pH825 pI825 = true := by decide +kernel
theorem cvx825 : ConvexBetweenHumps 825 :=
  cvx_of L825_ok H825_ok I825_ok link825 (by decide)

/-! ### `N = 826` -/

def pL826 : Prm := ⟨75, 35, 37, 828, 11, 18446744073709551616, 200853199266279807, 200853199266279807⟩
def pH826 : Prm := ⟨75, 35, 37, 828, 11, 18446744073709551616, 200855398289535359, 200855398289535359⟩
def pI826 : Prm := ⟨62, 31, 28, 828, 11, 18446744073709551616, 200853199266279807, 200855398289535359⟩
theorem L826_fin : (prmOK pL826 826 && ptTest pL826 (runFrom pL826 (fmask pL826) (cmask pL826) (hmask pL826) 1 825 (true, (init pL826), (init pL826))) 826 413 false) = true := by
  decide +kernel
theorem L826_ok : RunOK pL826 826 (runFrom pL826 (fmask pL826) (cmask pL826) (hmask pL826) 1 825 (true, (init pL826), (init pL826))) ∧ ptTest pL826 (runFrom pL826 (fmask pL826) (cmask pL826) (hmask pL826) 1 825 (true, (init pL826), (init pL826))) 826 413 false = true :=
  fin_run (runOK_init (prmOK_of_and L826_fin) true) (by decide) rfl L826_fin ptTest_fst
theorem H826_fin : (prmOK pH826 826 && ptTest pH826 (runFrom pH826 (fmask pH826) (cmask pH826) (hmask pH826) 1 825 (true, (init pH826), (init pH826))) 826 413 true) = true := by
  decide +kernel
theorem H826_ok : RunOK pH826 826 (runFrom pH826 (fmask pH826) (cmask pH826) (hmask pH826) 1 825 (true, (init pH826), (init pH826))) ∧ ptTest pH826 (runFrom pH826 (fmask pH826) (cmask pH826) (hmask pH826) 1 825 (true, (init pH826), (init pH826))) 826 413 true = true :=
  fin_run (runOK_init (prmOK_of_and H826_fin) true) (by decide) rfl H826_fin ptTest_fst
theorem I826_fin : (prmOK pI826 826 && intTest pI826 (runFrom pI826 (fmask pI826) (cmask pI826) (hmask pI826) 1 825 (true, (init pI826), (init pI826))) 826 17 true) = true := by
  decide +kernel
theorem I826_ok : RunOK pI826 826 (runFrom pI826 (fmask pI826) (cmask pI826) (hmask pI826) 1 825 (true, (init pI826), (init pI826))) ∧ intTest pI826 (runFrom pI826 (fmask pI826) (cmask pI826) (hmask pI826) 1 825 (true, (init pI826), (init pI826))) 826 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I826_fin) true) (by decide) rfl I826_fin intTest_fst
theorem link826 : linkOK pL826 pH826 pI826 = true := by decide +kernel
theorem cvx826 : ConvexBetweenHumps 826 :=
  cvx_of L826_ok H826_ok I826_ok link826 (by decide)
theorem cenlink826 : cenLinkOK pI826 826 = true := by decide +kernel
theorem cen826 : CenterUniqueMin 826 ∧ DipHyp 826 ∧ OnePointHyps 826 :=
  cen_of L826_ok H826_ok I826_ok link826 cenlink826

/-! ### `N = 827` -/

def pL827 : Prm := ⟨75, 35, 37, 829, 11, 18446744073709551616, 200661110776157560, 200661110776157560⟩
def pH827 : Prm := ⟨75, 35, 37, 829, 11, 18446744073709551616, 200663309799413112, 200663309799413112⟩
def pI827 : Prm := ⟨62, 31, 28, 829, 11, 18446744073709551616, 200661110776157560, 200663309799413112⟩
theorem L827_fin : (prmOK pL827 827 && ptTest pL827 (runFrom pL827 (fmask pL827) (cmask pL827) (hmask pL827) 1 826 (true, (init pL827), (init pL827))) 827 414 false) = true := by
  decide +kernel
theorem L827_ok : RunOK pL827 827 (runFrom pL827 (fmask pL827) (cmask pL827) (hmask pL827) 1 826 (true, (init pL827), (init pL827))) ∧ ptTest pL827 (runFrom pL827 (fmask pL827) (cmask pL827) (hmask pL827) 1 826 (true, (init pL827), (init pL827))) 827 414 false = true :=
  fin_run (runOK_init (prmOK_of_and L827_fin) true) (by decide) rfl L827_fin ptTest_fst
theorem H827_fin : (prmOK pH827 827 && ptTest pH827 (runFrom pH827 (fmask pH827) (cmask pH827) (hmask pH827) 1 826 (true, (init pH827), (init pH827))) 827 414 true) = true := by
  decide +kernel
theorem H827_ok : RunOK pH827 827 (runFrom pH827 (fmask pH827) (cmask pH827) (hmask pH827) 1 826 (true, (init pH827), (init pH827))) ∧ ptTest pH827 (runFrom pH827 (fmask pH827) (cmask pH827) (hmask pH827) 1 826 (true, (init pH827), (init pH827))) 827 414 true = true :=
  fin_run (runOK_init (prmOK_of_and H827_fin) true) (by decide) rfl H827_fin ptTest_fst
theorem I827_fin : (prmOK pI827 827 && intTest pI827 (runFrom pI827 (fmask pI827) (cmask pI827) (hmask pI827) 1 826 (true, (init pI827), (init pI827))) 827 17 false) = true := by
  decide +kernel
theorem I827_ok : RunOK pI827 827 (runFrom pI827 (fmask pI827) (cmask pI827) (hmask pI827) 1 826 (true, (init pI827), (init pI827))) ∧ intTest pI827 (runFrom pI827 (fmask pI827) (cmask pI827) (hmask pI827) 1 826 (true, (init pI827), (init pI827))) 827 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I827_fin) true) (by decide) rfl I827_fin intTest_fst
theorem link827 : linkOK pL827 pH827 pI827 = true := by decide +kernel
theorem cvx827 : ConvexBetweenHumps 827 :=
  cvx_of L827_ok H827_ok I827_ok link827 (by decide)

/-! ### `N = 828` -/

def pL828 : Prm := ⟨75, 35, 37, 830, 11, 18446744073709551616, 200469631213057187, 200469631213057187⟩
def pH828 : Prm := ⟨75, 35, 37, 830, 11, 18446744073709551616, 200471830236312739, 200471830236312739⟩
def pI828 : Prm := ⟨62, 31, 28, 830, 11, 18446744073709551616, 200469631213057187, 200471830236312739⟩
theorem L828_fin : (prmOK pL828 828 && ptTest pL828 (runFrom pL828 (fmask pL828) (cmask pL828) (hmask pL828) 1 827 (true, (init pL828), (init pL828))) 828 414 false) = true := by
  decide +kernel
theorem L828_ok : RunOK pL828 828 (runFrom pL828 (fmask pL828) (cmask pL828) (hmask pL828) 1 827 (true, (init pL828), (init pL828))) ∧ ptTest pL828 (runFrom pL828 (fmask pL828) (cmask pL828) (hmask pL828) 1 827 (true, (init pL828), (init pL828))) 828 414 false = true :=
  fin_run (runOK_init (prmOK_of_and L828_fin) true) (by decide) rfl L828_fin ptTest_fst
theorem H828_fin : (prmOK pH828 828 && ptTest pH828 (runFrom pH828 (fmask pH828) (cmask pH828) (hmask pH828) 1 827 (true, (init pH828), (init pH828))) 828 414 true) = true := by
  decide +kernel
theorem H828_ok : RunOK pH828 828 (runFrom pH828 (fmask pH828) (cmask pH828) (hmask pH828) 1 827 (true, (init pH828), (init pH828))) ∧ ptTest pH828 (runFrom pH828 (fmask pH828) (cmask pH828) (hmask pH828) 1 827 (true, (init pH828), (init pH828))) 828 414 true = true :=
  fin_run (runOK_init (prmOK_of_and H828_fin) true) (by decide) rfl H828_fin ptTest_fst
theorem I828_fin : (prmOK pI828 828 && intTest pI828 (runFrom pI828 (fmask pI828) (cmask pI828) (hmask pI828) 1 827 (true, (init pI828), (init pI828))) 828 17 true) = true := by
  decide +kernel
theorem I828_ok : RunOK pI828 828 (runFrom pI828 (fmask pI828) (cmask pI828) (hmask pI828) 1 827 (true, (init pI828), (init pI828))) ∧ intTest pI828 (runFrom pI828 (fmask pI828) (cmask pI828) (hmask pI828) 1 827 (true, (init pI828), (init pI828))) 828 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I828_fin) true) (by decide) rfl I828_fin intTest_fst
theorem link828 : linkOK pL828 pH828 pI828 = true := by decide +kernel
theorem cvx828 : ConvexBetweenHumps 828 :=
  cvx_of L828_ok H828_ok I828_ok link828 (by decide)
theorem cenlink828 : cenLinkOK pI828 828 = true := by decide +kernel
theorem cen828 : CenterUniqueMin 828 ∧ DipHyp 828 ∧ OnePointHyps 828 :=
  cen_of L828_ok H828_ok I828_ok link828 cenlink828

/-! ### `N = 829` -/

def pL829 : Prm := ⟨75, 35, 37, 831, 11, 18446744073709551616, 200278347046097291, 200278347046097291⟩
def pH829 : Prm := ⟨75, 35, 37, 831, 11, 18446744073709551616, 200280546069352843, 200280546069352843⟩
def pI829 : Prm := ⟨62, 31, 28, 831, 11, 18446744073709551616, 200278347046097291, 200280546069352843⟩
theorem L829_fin : (prmOK pL829 829 && ptTest pL829 (runFrom pL829 (fmask pL829) (cmask pL829) (hmask pL829) 1 828 (true, (init pL829), (init pL829))) 829 415 false) = true := by
  decide +kernel
theorem L829_ok : RunOK pL829 829 (runFrom pL829 (fmask pL829) (cmask pL829) (hmask pL829) 1 828 (true, (init pL829), (init pL829))) ∧ ptTest pL829 (runFrom pL829 (fmask pL829) (cmask pL829) (hmask pL829) 1 828 (true, (init pL829), (init pL829))) 829 415 false = true :=
  fin_run (runOK_init (prmOK_of_and L829_fin) true) (by decide) rfl L829_fin ptTest_fst
theorem H829_fin : (prmOK pH829 829 && ptTest pH829 (runFrom pH829 (fmask pH829) (cmask pH829) (hmask pH829) 1 828 (true, (init pH829), (init pH829))) 829 415 true) = true := by
  decide +kernel
theorem H829_ok : RunOK pH829 829 (runFrom pH829 (fmask pH829) (cmask pH829) (hmask pH829) 1 828 (true, (init pH829), (init pH829))) ∧ ptTest pH829 (runFrom pH829 (fmask pH829) (cmask pH829) (hmask pH829) 1 828 (true, (init pH829), (init pH829))) 829 415 true = true :=
  fin_run (runOK_init (prmOK_of_and H829_fin) true) (by decide) rfl H829_fin ptTest_fst
theorem I829_fin : (prmOK pI829 829 && intTest pI829 (runFrom pI829 (fmask pI829) (cmask pI829) (hmask pI829) 1 828 (true, (init pI829), (init pI829))) 829 17 false) = true := by
  decide +kernel
theorem I829_ok : RunOK pI829 829 (runFrom pI829 (fmask pI829) (cmask pI829) (hmask pI829) 1 828 (true, (init pI829), (init pI829))) ∧ intTest pI829 (runFrom pI829 (fmask pI829) (cmask pI829) (hmask pI829) 1 828 (true, (init pI829), (init pI829))) 829 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I829_fin) true) (by decide) rfl I829_fin intTest_fst
theorem link829 : linkOK pL829 pH829 pI829 = true := by decide +kernel
theorem cvx829 : ConvexBetweenHumps 829 :=
  cvx_of L829_ok H829_ok I829_ok link829 (by decide)

/-! ### `N = 830` -/

def pL830 : Prm := ⟨75, 35, 37, 832, 11, 18446744073709551616, 200087667675047825, 200087667675047825⟩
def pH830 : Prm := ⟨75, 35, 37, 832, 11, 18446744073709551616, 200089866698303377, 200089866698303377⟩
def pI830 : Prm := ⟨62, 31, 28, 832, 11, 18446744073709551616, 200087667675047825, 200089866698303377⟩
theorem L830_fin : (prmOK pL830 830 && ptTest pL830 (runFrom pL830 (fmask pL830) (cmask pL830) (hmask pL830) 1 829 (true, (init pL830), (init pL830))) 830 415 false) = true := by
  decide +kernel
theorem L830_ok : RunOK pL830 830 (runFrom pL830 (fmask pL830) (cmask pL830) (hmask pL830) 1 829 (true, (init pL830), (init pL830))) ∧ ptTest pL830 (runFrom pL830 (fmask pL830) (cmask pL830) (hmask pL830) 1 829 (true, (init pL830), (init pL830))) 830 415 false = true :=
  fin_run (runOK_init (prmOK_of_and L830_fin) true) (by decide) rfl L830_fin ptTest_fst
theorem H830_fin : (prmOK pH830 830 && ptTest pH830 (runFrom pH830 (fmask pH830) (cmask pH830) (hmask pH830) 1 829 (true, (init pH830), (init pH830))) 830 415 true) = true := by
  decide +kernel
theorem H830_ok : RunOK pH830 830 (runFrom pH830 (fmask pH830) (cmask pH830) (hmask pH830) 1 829 (true, (init pH830), (init pH830))) ∧ ptTest pH830 (runFrom pH830 (fmask pH830) (cmask pH830) (hmask pH830) 1 829 (true, (init pH830), (init pH830))) 830 415 true = true :=
  fin_run (runOK_init (prmOK_of_and H830_fin) true) (by decide) rfl H830_fin ptTest_fst
theorem I830_fin : (prmOK pI830 830 && intTest pI830 (runFrom pI830 (fmask pI830) (cmask pI830) (hmask pI830) 1 829 (true, (init pI830), (init pI830))) 830 17 true) = true := by
  decide +kernel
theorem I830_ok : RunOK pI830 830 (runFrom pI830 (fmask pI830) (cmask pI830) (hmask pI830) 1 829 (true, (init pI830), (init pI830))) ∧ intTest pI830 (runFrom pI830 (fmask pI830) (cmask pI830) (hmask pI830) 1 829 (true, (init pI830), (init pI830))) 830 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I830_fin) true) (by decide) rfl I830_fin intTest_fst
theorem link830 : linkOK pL830 pH830 pI830 = true := by decide +kernel
theorem cvx830 : ConvexBetweenHumps 830 :=
  cvx_of L830_ok H830_ok I830_ok link830 (by decide)
theorem cenlink830 : cenLinkOK pI830 830 = true := by decide +kernel
theorem cen830 : CenterUniqueMin 830 ∧ DipHyp 830 ∧ OnePointHyps 830 :=
  cen_of L830_ok H830_ok I830_ok link830 cenlink830

/-! ### `N = 831` -/

def pL831 : Prm := ⟨75, 35, 37, 833, 11, 18446744073709551616, 199897182609235285, 199897182609235285⟩
def pH831 : Prm := ⟨75, 35, 37, 833, 11, 18446744073709551616, 199899381632490837, 199899381632490837⟩
def pI831 : Prm := ⟨62, 31, 28, 833, 11, 18446744073709551616, 199897182609235285, 199899381632490837⟩
theorem L831_fin : (prmOK pL831 831 && ptTest pL831 (runFrom pL831 (fmask pL831) (cmask pL831) (hmask pL831) 1 830 (true, (init pL831), (init pL831))) 831 416 false) = true := by
  decide +kernel
theorem L831_ok : RunOK pL831 831 (runFrom pL831 (fmask pL831) (cmask pL831) (hmask pL831) 1 830 (true, (init pL831), (init pL831))) ∧ ptTest pL831 (runFrom pL831 (fmask pL831) (cmask pL831) (hmask pL831) 1 830 (true, (init pL831), (init pL831))) 831 416 false = true :=
  fin_run (runOK_init (prmOK_of_and L831_fin) true) (by decide) rfl L831_fin ptTest_fst
theorem H831_fin : (prmOK pH831 831 && ptTest pH831 (runFrom pH831 (fmask pH831) (cmask pH831) (hmask pH831) 1 830 (true, (init pH831), (init pH831))) 831 416 true) = true := by
  decide +kernel
theorem H831_ok : RunOK pH831 831 (runFrom pH831 (fmask pH831) (cmask pH831) (hmask pH831) 1 830 (true, (init pH831), (init pH831))) ∧ ptTest pH831 (runFrom pH831 (fmask pH831) (cmask pH831) (hmask pH831) 1 830 (true, (init pH831), (init pH831))) 831 416 true = true :=
  fin_run (runOK_init (prmOK_of_and H831_fin) true) (by decide) rfl H831_fin ptTest_fst
theorem I831_fin : (prmOK pI831 831 && intTest pI831 (runFrom pI831 (fmask pI831) (cmask pI831) (hmask pI831) 1 830 (true, (init pI831), (init pI831))) 831 17 false) = true := by
  decide +kernel
theorem I831_ok : RunOK pI831 831 (runFrom pI831 (fmask pI831) (cmask pI831) (hmask pI831) 1 830 (true, (init pI831), (init pI831))) ∧ intTest pI831 (runFrom pI831 (fmask pI831) (cmask pI831) (hmask pI831) 1 830 (true, (init pI831), (init pI831))) 831 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I831_fin) true) (by decide) rfl I831_fin intTest_fst
theorem link831 : linkOK pL831 pH831 pI831 = true := by decide +kernel
theorem cvx831 : ConvexBetweenHumps 831 :=
  cvx_of L831_ok H831_ok I831_ok link831 (by decide)

/-! ### `N = 832` -/

def pL832 : Prm := ⟨75, 35, 37, 834, 11, 18446744073709551616, 199707298246037560, 199707298246037560⟩
def pH832 : Prm := ⟨75, 35, 37, 834, 11, 18446744073709551616, 199709497269293112, 199709497269293112⟩
def pI832 : Prm := ⟨62, 31, 28, 834, 11, 18446744073709551616, 199707298246037560, 199709497269293112⟩
theorem L832_fin : (prmOK pL832 832 && ptTest pL832 (runFrom pL832 (fmask pL832) (cmask pL832) (hmask pL832) 1 831 (true, (init pL832), (init pL832))) 832 416 false) = true := by
  decide +kernel
theorem L832_ok : RunOK pL832 832 (runFrom pL832 (fmask pL832) (cmask pL832) (hmask pL832) 1 831 (true, (init pL832), (init pL832))) ∧ ptTest pL832 (runFrom pL832 (fmask pL832) (cmask pL832) (hmask pL832) 1 831 (true, (init pL832), (init pL832))) 832 416 false = true :=
  fin_run (runOK_init (prmOK_of_and L832_fin) true) (by decide) rfl L832_fin ptTest_fst
theorem H832_fin : (prmOK pH832 832 && ptTest pH832 (runFrom pH832 (fmask pH832) (cmask pH832) (hmask pH832) 1 831 (true, (init pH832), (init pH832))) 832 416 true) = true := by
  decide +kernel
theorem H832_ok : RunOK pH832 832 (runFrom pH832 (fmask pH832) (cmask pH832) (hmask pH832) 1 831 (true, (init pH832), (init pH832))) ∧ ptTest pH832 (runFrom pH832 (fmask pH832) (cmask pH832) (hmask pH832) 1 831 (true, (init pH832), (init pH832))) 832 416 true = true :=
  fin_run (runOK_init (prmOK_of_and H832_fin) true) (by decide) rfl H832_fin ptTest_fst
theorem I832_fin : (prmOK pI832 832 && intTest pI832 (runFrom pI832 (fmask pI832) (cmask pI832) (hmask pI832) 1 831 (true, (init pI832), (init pI832))) 832 17 true) = true := by
  decide +kernel
theorem I832_ok : RunOK pI832 832 (runFrom pI832 (fmask pI832) (cmask pI832) (hmask pI832) 1 831 (true, (init pI832), (init pI832))) ∧ intTest pI832 (runFrom pI832 (fmask pI832) (cmask pI832) (hmask pI832) 1 831 (true, (init pI832), (init pI832))) 832 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I832_fin) true) (by decide) rfl I832_fin intTest_fst
theorem link832 : linkOK pL832 pH832 pI832 = true := by decide +kernel
theorem cvx832 : ConvexBetweenHumps 832 :=
  cvx_of L832_ok H832_ok I832_ok link832 (by decide)
theorem cenlink832 : cenLinkOK pI832 832 = true := by decide +kernel
theorem cen832 : CenterUniqueMin 832 ∧ DipHyp 832 ∧ OnePointHyps 832 :=
  cen_of L832_ok H832_ok I832_ok link832 cenlink832

/-! ### `N = 833` -/

def pL833 : Prm := ⟨75, 35, 37, 835, 11, 18446744073709551616, 199517607105345117, 199517607105345117⟩
def pH833 : Prm := ⟨75, 35, 37, 835, 11, 18446744073709551616, 199519806128600669, 199519806128600669⟩
def pI833 : Prm := ⟨62, 31, 28, 835, 11, 18446744073709551616, 199517607105345117, 199519806128600669⟩
theorem L833_fin : (prmOK pL833 833 && ptTest pL833 (runFrom pL833 (fmask pL833) (cmask pL833) (hmask pL833) 1 832 (true, (init pL833), (init pL833))) 833 417 false) = true := by
  decide +kernel
theorem L833_ok : RunOK pL833 833 (runFrom pL833 (fmask pL833) (cmask pL833) (hmask pL833) 1 832 (true, (init pL833), (init pL833))) ∧ ptTest pL833 (runFrom pL833 (fmask pL833) (cmask pL833) (hmask pL833) 1 832 (true, (init pL833), (init pL833))) 833 417 false = true :=
  fin_run (runOK_init (prmOK_of_and L833_fin) true) (by decide) rfl L833_fin ptTest_fst
theorem H833_fin : (prmOK pH833 833 && ptTest pH833 (runFrom pH833 (fmask pH833) (cmask pH833) (hmask pH833) 1 832 (true, (init pH833), (init pH833))) 833 417 true) = true := by
  decide +kernel
theorem H833_ok : RunOK pH833 833 (runFrom pH833 (fmask pH833) (cmask pH833) (hmask pH833) 1 832 (true, (init pH833), (init pH833))) ∧ ptTest pH833 (runFrom pH833 (fmask pH833) (cmask pH833) (hmask pH833) 1 832 (true, (init pH833), (init pH833))) 833 417 true = true :=
  fin_run (runOK_init (prmOK_of_and H833_fin) true) (by decide) rfl H833_fin ptTest_fst
theorem I833_fin : (prmOK pI833 833 && intTest pI833 (runFrom pI833 (fmask pI833) (cmask pI833) (hmask pI833) 1 832 (true, (init pI833), (init pI833))) 833 17 false) = true := by
  decide +kernel
theorem I833_ok : RunOK pI833 833 (runFrom pI833 (fmask pI833) (cmask pI833) (hmask pI833) 1 832 (true, (init pI833), (init pI833))) ∧ intTest pI833 (runFrom pI833 (fmask pI833) (cmask pI833) (hmask pI833) 1 832 (true, (init pI833), (init pI833))) 833 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I833_fin) true) (by decide) rfl I833_fin intTest_fst
theorem link833 : linkOK pL833 pH833 pI833 = true := by decide +kernel
theorem cvx833 : ConvexBetweenHumps 833 :=
  cvx_of L833_ok H833_ok I833_ok link833 (by decide)

/-! ### `N = 834` -/

def pL834 : Prm := ⟨75, 35, 37, 836, 11, 18446744073709551616, 199328512611271189, 199328512611271189⟩
def pH834 : Prm := ⟨75, 35, 37, 836, 11, 18446744073709551616, 199330711634526741, 199330711634526741⟩
def pI834 : Prm := ⟨62, 31, 28, 836, 11, 18446744073709551616, 199328512611271189, 199330711634526741⟩
theorem L834_fin : (prmOK pL834 834 && ptTest pL834 (runFrom pL834 (fmask pL834) (cmask pL834) (hmask pL834) 1 833 (true, (init pL834), (init pL834))) 834 417 false) = true := by
  decide +kernel
theorem L834_ok : RunOK pL834 834 (runFrom pL834 (fmask pL834) (cmask pL834) (hmask pL834) 1 833 (true, (init pL834), (init pL834))) ∧ ptTest pL834 (runFrom pL834 (fmask pL834) (cmask pL834) (hmask pL834) 1 833 (true, (init pL834), (init pL834))) 834 417 false = true :=
  fin_run (runOK_init (prmOK_of_and L834_fin) true) (by decide) rfl L834_fin ptTest_fst
theorem H834_fin : (prmOK pH834 834 && ptTest pH834 (runFrom pH834 (fmask pH834) (cmask pH834) (hmask pH834) 1 833 (true, (init pH834), (init pH834))) 834 417 true) = true := by
  decide +kernel
theorem H834_ok : RunOK pH834 834 (runFrom pH834 (fmask pH834) (cmask pH834) (hmask pH834) 1 833 (true, (init pH834), (init pH834))) ∧ ptTest pH834 (runFrom pH834 (fmask pH834) (cmask pH834) (hmask pH834) 1 833 (true, (init pH834), (init pH834))) 834 417 true = true :=
  fin_run (runOK_init (prmOK_of_and H834_fin) true) (by decide) rfl H834_fin ptTest_fst
theorem I834_fin : (prmOK pI834 834 && intTest pI834 (runFrom pI834 (fmask pI834) (cmask pI834) (hmask pI834) 1 833 (true, (init pI834), (init pI834))) 834 17 true) = true := by
  decide +kernel
theorem I834_ok : RunOK pI834 834 (runFrom pI834 (fmask pI834) (cmask pI834) (hmask pI834) 1 833 (true, (init pI834), (init pI834))) ∧ intTest pI834 (runFrom pI834 (fmask pI834) (cmask pI834) (hmask pI834) 1 833 (true, (init pI834), (init pI834))) 834 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I834_fin) true) (by decide) rfl I834_fin intTest_fst
theorem link834 : linkOK pL834 pH834 pI834 = true := by decide +kernel
theorem cvx834 : ConvexBetweenHumps 834 :=
  cvx_of L834_ok H834_ok I834_ok link834 (by decide)
theorem cenlink834 : cenLinkOK pI834 834 = true := by decide +kernel
theorem cen834 : CenterUniqueMin 834 ∧ DipHyp 834 ∧ OnePointHyps 834 :=
  cen_of L834_ok H834_ok I834_ok link834 cenlink834

/-! ### `N = 835` -/

def pL835 : Prm := ⟨75, 35, 37, 837, 11, 18446744073709551616, 199139610265142808, 199139610265142808⟩
def pH835 : Prm := ⟨75, 35, 37, 837, 11, 18446744073709551616, 199141809288398360, 199141809288398360⟩
def pI835 : Prm := ⟨62, 31, 28, 837, 11, 18446744073709551616, 199139610265142808, 199141809288398360⟩
theorem L835_fin : (prmOK pL835 835 && ptTest pL835 (runFrom pL835 (fmask pL835) (cmask pL835) (hmask pL835) 1 834 (true, (init pL835), (init pL835))) 835 418 false) = true := by
  decide +kernel
theorem L835_ok : RunOK pL835 835 (runFrom pL835 (fmask pL835) (cmask pL835) (hmask pL835) 1 834 (true, (init pL835), (init pL835))) ∧ ptTest pL835 (runFrom pL835 (fmask pL835) (cmask pL835) (hmask pL835) 1 834 (true, (init pL835), (init pL835))) 835 418 false = true :=
  fin_run (runOK_init (prmOK_of_and L835_fin) true) (by decide) rfl L835_fin ptTest_fst
theorem H835_fin : (prmOK pH835 835 && ptTest pH835 (runFrom pH835 (fmask pH835) (cmask pH835) (hmask pH835) 1 834 (true, (init pH835), (init pH835))) 835 418 true) = true := by
  decide +kernel
theorem H835_ok : RunOK pH835 835 (runFrom pH835 (fmask pH835) (cmask pH835) (hmask pH835) 1 834 (true, (init pH835), (init pH835))) ∧ ptTest pH835 (runFrom pH835 (fmask pH835) (cmask pH835) (hmask pH835) 1 834 (true, (init pH835), (init pH835))) 835 418 true = true :=
  fin_run (runOK_init (prmOK_of_and H835_fin) true) (by decide) rfl H835_fin ptTest_fst
theorem I835_fin : (prmOK pI835 835 && intTest pI835 (runFrom pI835 (fmask pI835) (cmask pI835) (hmask pI835) 1 834 (true, (init pI835), (init pI835))) 835 17 false) = true := by
  decide +kernel
theorem I835_ok : RunOK pI835 835 (runFrom pI835 (fmask pI835) (cmask pI835) (hmask pI835) 1 834 (true, (init pI835), (init pI835))) ∧ intTest pI835 (runFrom pI835 (fmask pI835) (cmask pI835) (hmask pI835) 1 834 (true, (init pI835), (init pI835))) 835 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I835_fin) true) (by decide) rfl I835_fin intTest_fst
theorem link835 : linkOK pL835 pH835 pI835 = true := by decide +kernel
theorem cvx835 : ConvexBetweenHumps 835 :=
  cvx_of L835_ok H835_ok I835_ok link835 (by decide)

/-! ### `N = 836` -/

def pL836 : Prm := ⟨75, 35, 37, 838, 11, 18446744073709551616, 198951300546567023, 198951300546567023⟩
def pH836 : Prm := ⟨75, 35, 37, 838, 11, 18446744073709551616, 198953499569822575, 198953499569822575⟩
def pI836 : Prm := ⟨62, 31, 28, 838, 11, 18446744073709551616, 198951300546567023, 198953499569822575⟩
theorem L836_fin : (prmOK pL836 836 && ptTest pL836 (runFrom pL836 (fmask pL836) (cmask pL836) (hmask pL836) 1 835 (true, (init pL836), (init pL836))) 836 418 false) = true := by
  decide +kernel
theorem L836_ok : RunOK pL836 836 (runFrom pL836 (fmask pL836) (cmask pL836) (hmask pL836) 1 835 (true, (init pL836), (init pL836))) ∧ ptTest pL836 (runFrom pL836 (fmask pL836) (cmask pL836) (hmask pL836) 1 835 (true, (init pL836), (init pL836))) 836 418 false = true :=
  fin_run (runOK_init (prmOK_of_and L836_fin) true) (by decide) rfl L836_fin ptTest_fst
theorem H836_fin : (prmOK pH836 836 && ptTest pH836 (runFrom pH836 (fmask pH836) (cmask pH836) (hmask pH836) 1 835 (true, (init pH836), (init pH836))) 836 418 true) = true := by
  decide +kernel
theorem H836_ok : RunOK pH836 836 (runFrom pH836 (fmask pH836) (cmask pH836) (hmask pH836) 1 835 (true, (init pH836), (init pH836))) ∧ ptTest pH836 (runFrom pH836 (fmask pH836) (cmask pH836) (hmask pH836) 1 835 (true, (init pH836), (init pH836))) 836 418 true = true :=
  fin_run (runOK_init (prmOK_of_and H836_fin) true) (by decide) rfl H836_fin ptTest_fst
theorem I836_fin : (prmOK pI836 836 && intTest pI836 (runFrom pI836 (fmask pI836) (cmask pI836) (hmask pI836) 1 835 (true, (init pI836), (init pI836))) 836 17 true) = true := by
  decide +kernel
theorem I836_ok : RunOK pI836 836 (runFrom pI836 (fmask pI836) (cmask pI836) (hmask pI836) 1 835 (true, (init pI836), (init pI836))) ∧ intTest pI836 (runFrom pI836 (fmask pI836) (cmask pI836) (hmask pI836) 1 835 (true, (init pI836), (init pI836))) 836 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I836_fin) true) (by decide) rfl I836_fin intTest_fst
theorem link836 : linkOK pL836 pH836 pI836 = true := by decide +kernel
theorem cvx836 : ConvexBetweenHumps 836 :=
  cvx_of L836_ok H836_ok I836_ok link836 (by decide)
theorem cenlink836 : cenLinkOK pI836 836 = true := by decide +kernel
theorem cen836 : CenterUniqueMin 836 ∧ DipHyp 836 ∧ OnePointHyps 836 :=
  cen_of L836_ok H836_ok I836_ok link836 cenlink836

/-! ### `N = 837` -/

def pL837 : Prm := ⟨75, 35, 37, 839, 11, 18446744073709551616, 198763181909382935, 198763181909382935⟩
def pH837 : Prm := ⟨75, 35, 37, 839, 11, 18446744073709551616, 198765380932638487, 198765380932638487⟩
def pI837 : Prm := ⟨62, 31, 28, 839, 11, 18446744073709551616, 198763181909382935, 198765380932638487⟩
theorem L837_fin : (prmOK pL837 837 && ptTest pL837 (runFrom pL837 (fmask pL837) (cmask pL837) (hmask pL837) 1 836 (true, (init pL837), (init pL837))) 837 419 false) = true := by
  decide +kernel
theorem L837_ok : RunOK pL837 837 (runFrom pL837 (fmask pL837) (cmask pL837) (hmask pL837) 1 836 (true, (init pL837), (init pL837))) ∧ ptTest pL837 (runFrom pL837 (fmask pL837) (cmask pL837) (hmask pL837) 1 836 (true, (init pL837), (init pL837))) 837 419 false = true :=
  fin_run (runOK_init (prmOK_of_and L837_fin) true) (by decide) rfl L837_fin ptTest_fst
theorem H837_fin : (prmOK pH837 837 && ptTest pH837 (runFrom pH837 (fmask pH837) (cmask pH837) (hmask pH837) 1 836 (true, (init pH837), (init pH837))) 837 419 true) = true := by
  decide +kernel
theorem H837_ok : RunOK pH837 837 (runFrom pH837 (fmask pH837) (cmask pH837) (hmask pH837) 1 836 (true, (init pH837), (init pH837))) ∧ ptTest pH837 (runFrom pH837 (fmask pH837) (cmask pH837) (hmask pH837) 1 836 (true, (init pH837), (init pH837))) 837 419 true = true :=
  fin_run (runOK_init (prmOK_of_and H837_fin) true) (by decide) rfl H837_fin ptTest_fst
theorem I837_fin : (prmOK pI837 837 && intTest pI837 (runFrom pI837 (fmask pI837) (cmask pI837) (hmask pI837) 1 836 (true, (init pI837), (init pI837))) 837 17 false) = true := by
  decide +kernel
theorem I837_ok : RunOK pI837 837 (runFrom pI837 (fmask pI837) (cmask pI837) (hmask pI837) 1 836 (true, (init pI837), (init pI837))) ∧ intTest pI837 (runFrom pI837 (fmask pI837) (cmask pI837) (hmask pI837) 1 836 (true, (init pI837), (init pI837))) 837 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I837_fin) true) (by decide) rfl I837_fin intTest_fst
theorem link837 : linkOK pL837 pH837 pI837 = true := by decide +kernel
theorem cvx837 : ConvexBetweenHumps 837 :=
  cvx_of L837_ok H837_ok I837_ok link837 (by decide)

/-! ### `N = 838` -/

def pL838 : Prm := ⟨75, 35, 37, 840, 11, 18446744073709551616, 198575651917210080, 198575651917210080⟩
def pH838 : Prm := ⟨75, 35, 37, 840, 11, 18446744073709551616, 198577850940465632, 198577850940465632⟩
def pI838 : Prm := ⟨62, 31, 28, 840, 11, 18446744073709551616, 198575651917210080, 198577850940465632⟩
theorem L838_fin : (prmOK pL838 838 && ptTest pL838 (runFrom pL838 (fmask pL838) (cmask pL838) (hmask pL838) 1 837 (true, (init pL838), (init pL838))) 838 419 false) = true := by
  decide +kernel
theorem L838_ok : RunOK pL838 838 (runFrom pL838 (fmask pL838) (cmask pL838) (hmask pL838) 1 837 (true, (init pL838), (init pL838))) ∧ ptTest pL838 (runFrom pL838 (fmask pL838) (cmask pL838) (hmask pL838) 1 837 (true, (init pL838), (init pL838))) 838 419 false = true :=
  fin_run (runOK_init (prmOK_of_and L838_fin) true) (by decide) rfl L838_fin ptTest_fst
theorem H838_fin : (prmOK pH838 838 && ptTest pH838 (runFrom pH838 (fmask pH838) (cmask pH838) (hmask pH838) 1 837 (true, (init pH838), (init pH838))) 838 419 true) = true := by
  decide +kernel
theorem H838_ok : RunOK pH838 838 (runFrom pH838 (fmask pH838) (cmask pH838) (hmask pH838) 1 837 (true, (init pH838), (init pH838))) ∧ ptTest pH838 (runFrom pH838 (fmask pH838) (cmask pH838) (hmask pH838) 1 837 (true, (init pH838), (init pH838))) 838 419 true = true :=
  fin_run (runOK_init (prmOK_of_and H838_fin) true) (by decide) rfl H838_fin ptTest_fst
theorem I838_fin : (prmOK pI838 838 && intTest pI838 (runFrom pI838 (fmask pI838) (cmask pI838) (hmask pI838) 1 837 (true, (init pI838), (init pI838))) 838 17 true) = true := by
  decide +kernel
theorem I838_ok : RunOK pI838 838 (runFrom pI838 (fmask pI838) (cmask pI838) (hmask pI838) 1 837 (true, (init pI838), (init pI838))) ∧ intTest pI838 (runFrom pI838 (fmask pI838) (cmask pI838) (hmask pI838) 1 837 (true, (init pI838), (init pI838))) 838 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I838_fin) true) (by decide) rfl I838_fin intTest_fst
theorem link838 : linkOK pL838 pH838 pI838 = true := by decide +kernel
theorem cvx838 : ConvexBetweenHumps 838 :=
  cvx_of L838_ok H838_ok I838_ok link838 (by decide)
theorem cenlink838 : cenLinkOK pI838 838 = true := by decide +kernel
theorem cen838 : CenterUniqueMin 838 ∧ DipHyp 838 ∧ OnePointHyps 838 :=
  cen_of L838_ok H838_ok I838_ok link838 cenlink838

/-! ### `N = 839` -/

def pL839 : Prm := ⟨75, 35, 37, 841, 11, 18446744073709551616, 198388311947807172, 198388311947807172⟩
def pH839 : Prm := ⟨75, 35, 37, 841, 11, 18446744073709551616, 198390510971062724, 198390510971062724⟩
def pI839 : Prm := ⟨62, 31, 28, 841, 11, 18446744073709551616, 198388311947807172, 198390510971062724⟩
theorem L839_fin : (prmOK pL839 839 && ptTest pL839 (runFrom pL839 (fmask pL839) (cmask pL839) (hmask pL839) 1 838 (true, (init pL839), (init pL839))) 839 420 false) = true := by
  decide +kernel
theorem L839_ok : RunOK pL839 839 (runFrom pL839 (fmask pL839) (cmask pL839) (hmask pL839) 1 838 (true, (init pL839), (init pL839))) ∧ ptTest pL839 (runFrom pL839 (fmask pL839) (cmask pL839) (hmask pL839) 1 838 (true, (init pL839), (init pL839))) 839 420 false = true :=
  fin_run (runOK_init (prmOK_of_and L839_fin) true) (by decide) rfl L839_fin ptTest_fst
theorem H839_fin : (prmOK pH839 839 && ptTest pH839 (runFrom pH839 (fmask pH839) (cmask pH839) (hmask pH839) 1 838 (true, (init pH839), (init pH839))) 839 420 true) = true := by
  decide +kernel
theorem H839_ok : RunOK pH839 839 (runFrom pH839 (fmask pH839) (cmask pH839) (hmask pH839) 1 838 (true, (init pH839), (init pH839))) ∧ ptTest pH839 (runFrom pH839 (fmask pH839) (cmask pH839) (hmask pH839) 1 838 (true, (init pH839), (init pH839))) 839 420 true = true :=
  fin_run (runOK_init (prmOK_of_and H839_fin) true) (by decide) rfl H839_fin ptTest_fst
theorem I839_fin : (prmOK pI839 839 && intTest pI839 (runFrom pI839 (fmask pI839) (cmask pI839) (hmask pI839) 1 838 (true, (init pI839), (init pI839))) 839 17 false) = true := by
  decide +kernel
theorem I839_ok : RunOK pI839 839 (runFrom pI839 (fmask pI839) (cmask pI839) (hmask pI839) 1 838 (true, (init pI839), (init pI839))) ∧ intTest pI839 (runFrom pI839 (fmask pI839) (cmask pI839) (hmask pI839) 1 838 (true, (init pI839), (init pI839))) 839 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I839_fin) true) (by decide) rfl I839_fin intTest_fst
theorem link839 : linkOK pL839 pH839 pI839 = true := by decide +kernel
theorem cvx839 : ConvexBetweenHumps 839 :=
  cvx_of L839_ok H839_ok I839_ok link839 (by decide)

/-! ### `N = 840` -/

def pL840 : Prm := ⟨75, 35, 37, 842, 11, 18446744073709551616, 198201556676992857, 198201556676992857⟩
def pH840 : Prm := ⟨75, 35, 37, 842, 11, 18446744073709551616, 198203755700248409, 198203755700248409⟩
def pI840 : Prm := ⟨62, 31, 28, 842, 11, 18446744073709551616, 198201556676992857, 198203755700248409⟩
theorem L840_fin : (prmOK pL840 840 && ptTest pL840 (runFrom pL840 (fmask pL840) (cmask pL840) (hmask pL840) 1 839 (true, (init pL840), (init pL840))) 840 420 false) = true := by
  decide +kernel
theorem L840_ok : RunOK pL840 840 (runFrom pL840 (fmask pL840) (cmask pL840) (hmask pL840) 1 839 (true, (init pL840), (init pL840))) ∧ ptTest pL840 (runFrom pL840 (fmask pL840) (cmask pL840) (hmask pL840) 1 839 (true, (init pL840), (init pL840))) 840 420 false = true :=
  fin_run (runOK_init (prmOK_of_and L840_fin) true) (by decide) rfl L840_fin ptTest_fst
theorem H840_fin : (prmOK pH840 840 && ptTest pH840 (runFrom pH840 (fmask pH840) (cmask pH840) (hmask pH840) 1 839 (true, (init pH840), (init pH840))) 840 420 true) = true := by
  decide +kernel
theorem H840_ok : RunOK pH840 840 (runFrom pH840 (fmask pH840) (cmask pH840) (hmask pH840) 1 839 (true, (init pH840), (init pH840))) ∧ ptTest pH840 (runFrom pH840 (fmask pH840) (cmask pH840) (hmask pH840) 1 839 (true, (init pH840), (init pH840))) 840 420 true = true :=
  fin_run (runOK_init (prmOK_of_and H840_fin) true) (by decide) rfl H840_fin ptTest_fst
theorem I840_fin : (prmOK pI840 840 && intTest pI840 (runFrom pI840 (fmask pI840) (cmask pI840) (hmask pI840) 1 839 (true, (init pI840), (init pI840))) 840 17 true) = true := by
  decide +kernel
theorem I840_ok : RunOK pI840 840 (runFrom pI840 (fmask pI840) (cmask pI840) (hmask pI840) 1 839 (true, (init pI840), (init pI840))) ∧ intTest pI840 (runFrom pI840 (fmask pI840) (cmask pI840) (hmask pI840) 1 839 (true, (init pI840), (init pI840))) 840 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I840_fin) true) (by decide) rfl I840_fin intTest_fst
theorem link840 : linkOK pL840 pH840 pI840 = true := by decide +kernel
theorem cvx840 : ConvexBetweenHumps 840 :=
  cvx_of L840_ok H840_ok I840_ok link840 (by decide)
theorem cenlink840 : cenLinkOK pI840 840 = true := by decide +kernel
theorem cen840 : CenterUniqueMin 840 ∧ DipHyp 840 ∧ OnePointHyps 840 :=
  cen_of L840_ok H840_ok I840_ok link840 cenlink840

/-! ### `N = 841` -/

def pL841 : Prm := ⟨75, 35, 37, 843, 11, 18446744073709551616, 198014990378221947, 198014990378221947⟩
def pH841 : Prm := ⟨75, 35, 37, 843, 11, 18446744073709551616, 198017189401477499, 198017189401477499⟩
def pI841 : Prm := ⟨62, 31, 28, 843, 11, 18446744073709551616, 198014990378221947, 198017189401477499⟩
theorem L841_fin : (prmOK pL841 841 && ptTest pL841 (runFrom pL841 (fmask pL841) (cmask pL841) (hmask pL841) 1 840 (true, (init pL841), (init pL841))) 841 421 false) = true := by
  decide +kernel
theorem L841_ok : RunOK pL841 841 (runFrom pL841 (fmask pL841) (cmask pL841) (hmask pL841) 1 840 (true, (init pL841), (init pL841))) ∧ ptTest pL841 (runFrom pL841 (fmask pL841) (cmask pL841) (hmask pL841) 1 840 (true, (init pL841), (init pL841))) 841 421 false = true :=
  fin_run (runOK_init (prmOK_of_and L841_fin) true) (by decide) rfl L841_fin ptTest_fst
theorem H841_fin : (prmOK pH841 841 && ptTest pH841 (runFrom pH841 (fmask pH841) (cmask pH841) (hmask pH841) 1 840 (true, (init pH841), (init pH841))) 841 421 true) = true := by
  decide +kernel
theorem H841_ok : RunOK pH841 841 (runFrom pH841 (fmask pH841) (cmask pH841) (hmask pH841) 1 840 (true, (init pH841), (init pH841))) ∧ ptTest pH841 (runFrom pH841 (fmask pH841) (cmask pH841) (hmask pH841) 1 840 (true, (init pH841), (init pH841))) 841 421 true = true :=
  fin_run (runOK_init (prmOK_of_and H841_fin) true) (by decide) rfl H841_fin ptTest_fst
theorem I841_fin : (prmOK pI841 841 && intTest pI841 (runFrom pI841 (fmask pI841) (cmask pI841) (hmask pI841) 1 840 (true, (init pI841), (init pI841))) 841 17 false) = true := by
  decide +kernel
theorem I841_ok : RunOK pI841 841 (runFrom pI841 (fmask pI841) (cmask pI841) (hmask pI841) 1 840 (true, (init pI841), (init pI841))) ∧ intTest pI841 (runFrom pI841 (fmask pI841) (cmask pI841) (hmask pI841) 1 840 (true, (init pI841), (init pI841))) 841 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I841_fin) true) (by decide) rfl I841_fin intTest_fst
theorem link841 : linkOK pL841 pH841 pI841 = true := by decide +kernel
theorem cvx841 : ConvexBetweenHumps 841 :=
  cvx_of L841_ok H841_ok I841_ok link841 (by decide)

/-! ### `N = 842` -/

def pL842 : Prm := ⟨75, 35, 37, 844, 11, 18446744073709551616, 197829004867256098, 197829004867256098⟩
def pH842 : Prm := ⟨75, 35, 37, 844, 11, 18446744073709551616, 197831203890511650, 197831203890511650⟩
def pI842 : Prm := ⟨62, 31, 28, 844, 11, 18446744073709551616, 197829004867256098, 197831203890511650⟩
theorem L842_fin : (prmOK pL842 842 && ptTest pL842 (runFrom pL842 (fmask pL842) (cmask pL842) (hmask pL842) 1 841 (true, (init pL842), (init pL842))) 842 421 false) = true := by
  decide +kernel
theorem L842_ok : RunOK pL842 842 (runFrom pL842 (fmask pL842) (cmask pL842) (hmask pL842) 1 841 (true, (init pL842), (init pL842))) ∧ ptTest pL842 (runFrom pL842 (fmask pL842) (cmask pL842) (hmask pL842) 1 841 (true, (init pL842), (init pL842))) 842 421 false = true :=
  fin_run (runOK_init (prmOK_of_and L842_fin) true) (by decide) rfl L842_fin ptTest_fst
theorem H842_fin : (prmOK pH842 842 && ptTest pH842 (runFrom pH842 (fmask pH842) (cmask pH842) (hmask pH842) 1 841 (true, (init pH842), (init pH842))) 842 421 true) = true := by
  decide +kernel
theorem H842_ok : RunOK pH842 842 (runFrom pH842 (fmask pH842) (cmask pH842) (hmask pH842) 1 841 (true, (init pH842), (init pH842))) ∧ ptTest pH842 (runFrom pH842 (fmask pH842) (cmask pH842) (hmask pH842) 1 841 (true, (init pH842), (init pH842))) 842 421 true = true :=
  fin_run (runOK_init (prmOK_of_and H842_fin) true) (by decide) rfl H842_fin ptTest_fst
theorem I842_fin : (prmOK pI842 842 && intTest pI842 (runFrom pI842 (fmask pI842) (cmask pI842) (hmask pI842) 1 841 (true, (init pI842), (init pI842))) 842 17 true) = true := by
  decide +kernel
theorem I842_ok : RunOK pI842 842 (runFrom pI842 (fmask pI842) (cmask pI842) (hmask pI842) 1 841 (true, (init pI842), (init pI842))) ∧ intTest pI842 (runFrom pI842 (fmask pI842) (cmask pI842) (hmask pI842) 1 841 (true, (init pI842), (init pI842))) 842 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I842_fin) true) (by decide) rfl I842_fin intTest_fst
theorem link842 : linkOK pL842 pH842 pI842 = true := by decide +kernel
theorem cvx842 : ConvexBetweenHumps 842 :=
  cvx_of L842_ok H842_ok I842_ok link842 (by decide)
theorem cenlink842 : cenLinkOK pI842 842 = true := by decide +kernel
theorem cen842 : CenterUniqueMin 842 ∧ DipHyp 842 ∧ OnePointHyps 842 :=
  cen_of L842_ok H842_ok I842_ok link842 cenlink842

/-! ### `N = 843` -/

def pL843 : Prm := ⟨75, 35, 37, 845, 11, 18446744073709551616, 197643207285465425, 197643207285465425⟩
def pH843 : Prm := ⟨75, 35, 37, 845, 11, 18446744073709551616, 197645406308720977, 197645406308720977⟩
def pI843 : Prm := ⟨62, 31, 28, 845, 11, 18446744073709551616, 197643207285465425, 197645406308720977⟩
theorem L843_fin : (prmOK pL843 843 && ptTest pL843 (runFrom pL843 (fmask pL843) (cmask pL843) (hmask pL843) 1 842 (true, (init pL843), (init pL843))) 843 422 false) = true := by
  decide +kernel
theorem L843_ok : RunOK pL843 843 (runFrom pL843 (fmask pL843) (cmask pL843) (hmask pL843) 1 842 (true, (init pL843), (init pL843))) ∧ ptTest pL843 (runFrom pL843 (fmask pL843) (cmask pL843) (hmask pL843) 1 842 (true, (init pL843), (init pL843))) 843 422 false = true :=
  fin_run (runOK_init (prmOK_of_and L843_fin) true) (by decide) rfl L843_fin ptTest_fst
theorem H843_fin : (prmOK pH843 843 && ptTest pH843 (runFrom pH843 (fmask pH843) (cmask pH843) (hmask pH843) 1 842 (true, (init pH843), (init pH843))) 843 422 true) = true := by
  decide +kernel
theorem H843_ok : RunOK pH843 843 (runFrom pH843 (fmask pH843) (cmask pH843) (hmask pH843) 1 842 (true, (init pH843), (init pH843))) ∧ ptTest pH843 (runFrom pH843 (fmask pH843) (cmask pH843) (hmask pH843) 1 842 (true, (init pH843), (init pH843))) 843 422 true = true :=
  fin_run (runOK_init (prmOK_of_and H843_fin) true) (by decide) rfl H843_fin ptTest_fst
theorem I843_fin : (prmOK pI843 843 && intTest pI843 (runFrom pI843 (fmask pI843) (cmask pI843) (hmask pI843) 1 842 (true, (init pI843), (init pI843))) 843 17 false) = true := by
  decide +kernel
theorem I843_ok : RunOK pI843 843 (runFrom pI843 (fmask pI843) (cmask pI843) (hmask pI843) 1 842 (true, (init pI843), (init pI843))) ∧ intTest pI843 (runFrom pI843 (fmask pI843) (cmask pI843) (hmask pI843) 1 842 (true, (init pI843), (init pI843))) 843 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I843_fin) true) (by decide) rfl I843_fin intTest_fst
theorem link843 : linkOK pL843 pH843 pI843 = true := by decide +kernel
theorem cvx843 : ConvexBetweenHumps 843 :=
  cvx_of L843_ok H843_ok I843_ok link843 (by decide)

/-! ### `N = 844` -/

def pL844 : Prm := ⟨75, 35, 37, 846, 11, 18446744073709551616, 197457986615948011, 197457986615948011⟩
def pH844 : Prm := ⟨75, 35, 37, 846, 11, 18446744073709551616, 197460185639203563, 197460185639203563⟩
def pI844 : Prm := ⟨62, 31, 28, 846, 11, 18446744073709551616, 197457986615948011, 197460185639203563⟩
theorem L844_fin : (prmOK pL844 844 && ptTest pL844 (runFrom pL844 (fmask pL844) (cmask pL844) (hmask pL844) 1 843 (true, (init pL844), (init pL844))) 844 422 false) = true := by
  decide +kernel
theorem L844_ok : RunOK pL844 844 (runFrom pL844 (fmask pL844) (cmask pL844) (hmask pL844) 1 843 (true, (init pL844), (init pL844))) ∧ ptTest pL844 (runFrom pL844 (fmask pL844) (cmask pL844) (hmask pL844) 1 843 (true, (init pL844), (init pL844))) 844 422 false = true :=
  fin_run (runOK_init (prmOK_of_and L844_fin) true) (by decide) rfl L844_fin ptTest_fst
theorem H844_fin : (prmOK pH844 844 && ptTest pH844 (runFrom pH844 (fmask pH844) (cmask pH844) (hmask pH844) 1 843 (true, (init pH844), (init pH844))) 844 422 true) = true := by
  decide +kernel
theorem H844_ok : RunOK pH844 844 (runFrom pH844 (fmask pH844) (cmask pH844) (hmask pH844) 1 843 (true, (init pH844), (init pH844))) ∧ ptTest pH844 (runFrom pH844 (fmask pH844) (cmask pH844) (hmask pH844) 1 843 (true, (init pH844), (init pH844))) 844 422 true = true :=
  fin_run (runOK_init (prmOK_of_and H844_fin) true) (by decide) rfl H844_fin ptTest_fst
theorem I844_fin : (prmOK pI844 844 && intTest pI844 (runFrom pI844 (fmask pI844) (cmask pI844) (hmask pI844) 1 843 (true, (init pI844), (init pI844))) 844 17 true) = true := by
  decide +kernel
theorem I844_ok : RunOK pI844 844 (runFrom pI844 (fmask pI844) (cmask pI844) (hmask pI844) 1 843 (true, (init pI844), (init pI844))) ∧ intTest pI844 (runFrom pI844 (fmask pI844) (cmask pI844) (hmask pI844) 1 843 (true, (init pI844), (init pI844))) 844 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I844_fin) true) (by decide) rfl I844_fin intTest_fst
theorem link844 : linkOK pL844 pH844 pI844 = true := by decide +kernel
theorem cvx844 : ConvexBetweenHumps 844 :=
  cvx_of L844_ok H844_ok I844_ok link844 (by decide)
theorem cenlink844 : cenLinkOK pI844 844 = true := by decide +kernel
theorem cen844 : CenterUniqueMin 844 ∧ DipHyp 844 ∧ OnePointHyps 844 :=
  cen_of L844_ok H844_ok I844_ok link844 cenlink844

/-! ### `N = 845` -/

def pL845 : Prm := ⟨75, 35, 37, 847, 11, 18446744073709551616, 197272952840448284, 197272952840448284⟩
def pH845 : Prm := ⟨75, 35, 37, 847, 11, 18446744073709551616, 197275151863703836, 197275151863703836⟩
def pI845 : Prm := ⟨63, 31, 29, 847, 11, 18446744073709551616, 197272952840448284, 197275151863703836⟩
theorem L845_fin : (prmOK pL845 845 && ptTest pL845 (runFrom pL845 (fmask pL845) (cmask pL845) (hmask pL845) 1 844 (true, (init pL845), (init pL845))) 845 423 false) = true := by
  decide +kernel
theorem L845_ok : RunOK pL845 845 (runFrom pL845 (fmask pL845) (cmask pL845) (hmask pL845) 1 844 (true, (init pL845), (init pL845))) ∧ ptTest pL845 (runFrom pL845 (fmask pL845) (cmask pL845) (hmask pL845) 1 844 (true, (init pL845), (init pL845))) 845 423 false = true :=
  fin_run (runOK_init (prmOK_of_and L845_fin) true) (by decide) rfl L845_fin ptTest_fst
theorem H845_fin : (prmOK pH845 845 && ptTest pH845 (runFrom pH845 (fmask pH845) (cmask pH845) (hmask pH845) 1 844 (true, (init pH845), (init pH845))) 845 423 true) = true := by
  decide +kernel
theorem H845_ok : RunOK pH845 845 (runFrom pH845 (fmask pH845) (cmask pH845) (hmask pH845) 1 844 (true, (init pH845), (init pH845))) ∧ ptTest pH845 (runFrom pH845 (fmask pH845) (cmask pH845) (hmask pH845) 1 844 (true, (init pH845), (init pH845))) 845 423 true = true :=
  fin_run (runOK_init (prmOK_of_and H845_fin) true) (by decide) rfl H845_fin ptTest_fst
theorem I845_fin : (prmOK pI845 845 && intTest pI845 (runFrom pI845 (fmask pI845) (cmask pI845) (hmask pI845) 1 844 (true, (init pI845), (init pI845))) 845 17 false) = true := by
  decide +kernel
theorem I845_ok : RunOK pI845 845 (runFrom pI845 (fmask pI845) (cmask pI845) (hmask pI845) 1 844 (true, (init pI845), (init pI845))) ∧ intTest pI845 (runFrom pI845 (fmask pI845) (cmask pI845) (hmask pI845) 1 844 (true, (init pI845), (init pI845))) 845 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I845_fin) true) (by decide) rfl I845_fin intTest_fst
theorem link845 : linkOK pL845 pH845 pI845 = true := by decide +kernel
theorem cvx845 : ConvexBetweenHumps 845 :=
  cvx_of L845_ok H845_ok I845_ok link845 (by decide)

/-! ### `N = 846` -/

def pL846 : Prm := ⟨75, 35, 37, 848, 11, 18446744073709551616, 197088492136591251, 197088492136591251⟩
def pH846 : Prm := ⟨75, 35, 37, 848, 11, 18446744073709551616, 197090691159846803, 197090691159846803⟩
def pI846 : Prm := ⟨62, 31, 28, 848, 11, 18446744073709551616, 197088492136591251, 197090691159846803⟩
theorem L846_fin : (prmOK pL846 846 && ptTest pL846 (runFrom pL846 (fmask pL846) (cmask pL846) (hmask pL846) 1 845 (true, (init pL846), (init pL846))) 846 423 false) = true := by
  decide +kernel
theorem L846_ok : RunOK pL846 846 (runFrom pL846 (fmask pL846) (cmask pL846) (hmask pL846) 1 845 (true, (init pL846), (init pL846))) ∧ ptTest pL846 (runFrom pL846 (fmask pL846) (cmask pL846) (hmask pL846) 1 845 (true, (init pL846), (init pL846))) 846 423 false = true :=
  fin_run (runOK_init (prmOK_of_and L846_fin) true) (by decide) rfl L846_fin ptTest_fst
theorem H846_fin : (prmOK pH846 846 && ptTest pH846 (runFrom pH846 (fmask pH846) (cmask pH846) (hmask pH846) 1 845 (true, (init pH846), (init pH846))) 846 423 true) = true := by
  decide +kernel
theorem H846_ok : RunOK pH846 846 (runFrom pH846 (fmask pH846) (cmask pH846) (hmask pH846) 1 845 (true, (init pH846), (init pH846))) ∧ ptTest pH846 (runFrom pH846 (fmask pH846) (cmask pH846) (hmask pH846) 1 845 (true, (init pH846), (init pH846))) 846 423 true = true :=
  fin_run (runOK_init (prmOK_of_and H846_fin) true) (by decide) rfl H846_fin ptTest_fst
theorem I846_fin : (prmOK pI846 846 && intTest pI846 (runFrom pI846 (fmask pI846) (cmask pI846) (hmask pI846) 1 845 (true, (init pI846), (init pI846))) 846 17 true) = true := by
  decide +kernel
theorem I846_ok : RunOK pI846 846 (runFrom pI846 (fmask pI846) (cmask pI846) (hmask pI846) 1 845 (true, (init pI846), (init pI846))) ∧ intTest pI846 (runFrom pI846 (fmask pI846) (cmask pI846) (hmask pI846) 1 845 (true, (init pI846), (init pI846))) 846 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I846_fin) true) (by decide) rfl I846_fin intTest_fst
theorem link846 : linkOK pL846 pH846 pI846 = true := by decide +kernel
theorem cvx846 : ConvexBetweenHumps 846 :=
  cvx_of L846_ok H846_ok I846_ok link846 (by decide)
theorem cenlink846 : cenLinkOK pI846 846 = true := by decide +kernel
theorem cen846 : CenterUniqueMin 846 ∧ DipHyp 846 ∧ OnePointHyps 846 :=
  cen_of L846_ok H846_ok I846_ok link846 cenlink846

/-! ### `N = 847` -/

def pL847 : Prm := ⟨75, 35, 37, 849, 11, 18446744073709551616, 196904217299268260, 196904217299268260⟩
def pH847 : Prm := ⟨75, 35, 37, 849, 11, 18446744073709551616, 196906416322523812, 196906416322523812⟩
def pI847 : Prm := ⟨62, 31, 28, 849, 11, 18446744073709551616, 196904217299268260, 196906416322523812⟩
theorem L847_fin : (prmOK pL847 847 && ptTest pL847 (runFrom pL847 (fmask pL847) (cmask pL847) (hmask pL847) 1 846 (true, (init pL847), (init pL847))) 847 424 false) = true := by
  decide +kernel
theorem L847_ok : RunOK pL847 847 (runFrom pL847 (fmask pL847) (cmask pL847) (hmask pL847) 1 846 (true, (init pL847), (init pL847))) ∧ ptTest pL847 (runFrom pL847 (fmask pL847) (cmask pL847) (hmask pL847) 1 846 (true, (init pL847), (init pL847))) 847 424 false = true :=
  fin_run (runOK_init (prmOK_of_and L847_fin) true) (by decide) rfl L847_fin ptTest_fst
theorem H847_fin : (prmOK pH847 847 && ptTest pH847 (runFrom pH847 (fmask pH847) (cmask pH847) (hmask pH847) 1 846 (true, (init pH847), (init pH847))) 847 424 true) = true := by
  decide +kernel
theorem H847_ok : RunOK pH847 847 (runFrom pH847 (fmask pH847) (cmask pH847) (hmask pH847) 1 846 (true, (init pH847), (init pH847))) ∧ ptTest pH847 (runFrom pH847 (fmask pH847) (cmask pH847) (hmask pH847) 1 846 (true, (init pH847), (init pH847))) 847 424 true = true :=
  fin_run (runOK_init (prmOK_of_and H847_fin) true) (by decide) rfl H847_fin ptTest_fst
theorem I847_fin : (prmOK pI847 847 && intTest pI847 (runFrom pI847 (fmask pI847) (cmask pI847) (hmask pI847) 1 846 (true, (init pI847), (init pI847))) 847 17 false) = true := by
  decide +kernel
theorem I847_ok : RunOK pI847 847 (runFrom pI847 (fmask pI847) (cmask pI847) (hmask pI847) 1 846 (true, (init pI847), (init pI847))) ∧ intTest pI847 (runFrom pI847 (fmask pI847) (cmask pI847) (hmask pI847) 1 846 (true, (init pI847), (init pI847))) 847 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I847_fin) true) (by decide) rfl I847_fin intTest_fst
theorem link847 : linkOK pL847 pH847 pI847 = true := by decide +kernel
theorem cvx847 : ConvexBetweenHumps 847 :=
  cvx_of L847_ok H847_ok I847_ok link847 (by decide)

/-! ### `N = 848` -/

def pL848 : Prm := ⟨75, 35, 37, 850, 11, 18446744073709551616, 196720511727415919, 196720511727415919⟩
def pH848 : Prm := ⟨75, 35, 37, 850, 11, 18446744073709551616, 196722710750671471, 196722710750671471⟩
def pI848 : Prm := ⟨62, 31, 28, 850, 11, 18446744073709551616, 196720511727415919, 196722710750671471⟩
theorem L848_fin : (prmOK pL848 848 && ptTest pL848 (runFrom pL848 (fmask pL848) (cmask pL848) (hmask pL848) 1 847 (true, (init pL848), (init pL848))) 848 424 false) = true := by
  decide +kernel
theorem L848_ok : RunOK pL848 848 (runFrom pL848 (fmask pL848) (cmask pL848) (hmask pL848) 1 847 (true, (init pL848), (init pL848))) ∧ ptTest pL848 (runFrom pL848 (fmask pL848) (cmask pL848) (hmask pL848) 1 847 (true, (init pL848), (init pL848))) 848 424 false = true :=
  fin_run (runOK_init (prmOK_of_and L848_fin) true) (by decide) rfl L848_fin ptTest_fst
theorem H848_fin : (prmOK pH848 848 && ptTest pH848 (runFrom pH848 (fmask pH848) (cmask pH848) (hmask pH848) 1 847 (true, (init pH848), (init pH848))) 848 424 true) = true := by
  decide +kernel
theorem H848_ok : RunOK pH848 848 (runFrom pH848 (fmask pH848) (cmask pH848) (hmask pH848) 1 847 (true, (init pH848), (init pH848))) ∧ ptTest pH848 (runFrom pH848 (fmask pH848) (cmask pH848) (hmask pH848) 1 847 (true, (init pH848), (init pH848))) 848 424 true = true :=
  fin_run (runOK_init (prmOK_of_and H848_fin) true) (by decide) rfl H848_fin ptTest_fst
theorem I848_fin : (prmOK pI848 848 && intTest pI848 (runFrom pI848 (fmask pI848) (cmask pI848) (hmask pI848) 1 847 (true, (init pI848), (init pI848))) 848 17 true) = true := by
  decide +kernel
theorem I848_ok : RunOK pI848 848 (runFrom pI848 (fmask pI848) (cmask pI848) (hmask pI848) 1 847 (true, (init pI848), (init pI848))) ∧ intTest pI848 (runFrom pI848 (fmask pI848) (cmask pI848) (hmask pI848) 1 847 (true, (init pI848), (init pI848))) 848 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I848_fin) true) (by decide) rfl I848_fin intTest_fst
theorem link848 : linkOK pL848 pH848 pI848 = true := by decide +kernel
theorem cvx848 : ConvexBetweenHumps 848 :=
  cvx_of L848_ok H848_ok I848_ok link848 (by decide)
theorem cenlink848 : cenLinkOK pI848 848 = true := by decide +kernel
theorem cen848 : CenterUniqueMin 848 ∧ DipHyp 848 ∧ OnePointHyps 848 :=
  cen_of L848_ok H848_ok I848_ok link848 cenlink848

/-! ### `N = 849` -/

def pL849 : Prm := ⟨75, 35, 37, 851, 11, 18446744073709551616, 196536991002250926, 196536991002250926⟩
def pH849 : Prm := ⟨75, 35, 37, 851, 11, 18446744073709551616, 196539190025506478, 196539190025506478⟩
def pI849 : Prm := ⟨63, 31, 29, 851, 11, 18446744073709551616, 196536991002250926, 196539190025506478⟩
theorem L849_fin : (prmOK pL849 849 && ptTest pL849 (runFrom pL849 (fmask pL849) (cmask pL849) (hmask pL849) 1 848 (true, (init pL849), (init pL849))) 849 425 false) = true := by
  decide +kernel
theorem L849_ok : RunOK pL849 849 (runFrom pL849 (fmask pL849) (cmask pL849) (hmask pL849) 1 848 (true, (init pL849), (init pL849))) ∧ ptTest pL849 (runFrom pL849 (fmask pL849) (cmask pL849) (hmask pL849) 1 848 (true, (init pL849), (init pL849))) 849 425 false = true :=
  fin_run (runOK_init (prmOK_of_and L849_fin) true) (by decide) rfl L849_fin ptTest_fst
theorem H849_fin : (prmOK pH849 849 && ptTest pH849 (runFrom pH849 (fmask pH849) (cmask pH849) (hmask pH849) 1 848 (true, (init pH849), (init pH849))) 849 425 true) = true := by
  decide +kernel
theorem H849_ok : RunOK pH849 849 (runFrom pH849 (fmask pH849) (cmask pH849) (hmask pH849) 1 848 (true, (init pH849), (init pH849))) ∧ ptTest pH849 (runFrom pH849 (fmask pH849) (cmask pH849) (hmask pH849) 1 848 (true, (init pH849), (init pH849))) 849 425 true = true :=
  fin_run (runOK_init (prmOK_of_and H849_fin) true) (by decide) rfl H849_fin ptTest_fst
theorem I849_fin : (prmOK pI849 849 && intTest pI849 (runFrom pI849 (fmask pI849) (cmask pI849) (hmask pI849) 1 848 (true, (init pI849), (init pI849))) 849 17 false) = true := by
  decide +kernel
theorem I849_ok : RunOK pI849 849 (runFrom pI849 (fmask pI849) (cmask pI849) (hmask pI849) 1 848 (true, (init pI849), (init pI849))) ∧ intTest pI849 (runFrom pI849 (fmask pI849) (cmask pI849) (hmask pI849) 1 848 (true, (init pI849), (init pI849))) 849 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I849_fin) true) (by decide) rfl I849_fin intTest_fst
theorem link849 : linkOK pL849 pH849 pI849 = true := by decide +kernel
theorem cvx849 : ConvexBetweenHumps 849 :=
  cvx_of L849_ok H849_ok I849_ok link849 (by decide)

/-! ### `N = 850` -/

def pL850 : Prm := ⟨75, 35, 37, 852, 11, 18446744073709551616, 196354035770455676, 196354035770455676⟩
def pH850 : Prm := ⟨75, 35, 37, 852, 11, 18446744073709551616, 196356234793711228, 196356234793711228⟩
def pI850 : Prm := ⟨63, 31, 29, 852, 11, 18446744073709551616, 196354035770455676, 196356234793711228⟩
theorem L850_fin : (prmOK pL850 850 && ptTest pL850 (runFrom pL850 (fmask pL850) (cmask pL850) (hmask pL850) 1 849 (true, (init pL850), (init pL850))) 850 425 false) = true := by
  decide +kernel
theorem L850_ok : RunOK pL850 850 (runFrom pL850 (fmask pL850) (cmask pL850) (hmask pL850) 1 849 (true, (init pL850), (init pL850))) ∧ ptTest pL850 (runFrom pL850 (fmask pL850) (cmask pL850) (hmask pL850) 1 849 (true, (init pL850), (init pL850))) 850 425 false = true :=
  fin_run (runOK_init (prmOK_of_and L850_fin) true) (by decide) rfl L850_fin ptTest_fst
theorem H850_fin : (prmOK pH850 850 && ptTest pH850 (runFrom pH850 (fmask pH850) (cmask pH850) (hmask pH850) 1 849 (true, (init pH850), (init pH850))) 850 425 true) = true := by
  decide +kernel
theorem H850_ok : RunOK pH850 850 (runFrom pH850 (fmask pH850) (cmask pH850) (hmask pH850) 1 849 (true, (init pH850), (init pH850))) ∧ ptTest pH850 (runFrom pH850 (fmask pH850) (cmask pH850) (hmask pH850) 1 849 (true, (init pH850), (init pH850))) 850 425 true = true :=
  fin_run (runOK_init (prmOK_of_and H850_fin) true) (by decide) rfl H850_fin ptTest_fst
theorem I850_fin : (prmOK pI850 850 && intTest pI850 (runFrom pI850 (fmask pI850) (cmask pI850) (hmask pI850) 1 849 (true, (init pI850), (init pI850))) 850 17 true) = true := by
  decide +kernel
theorem I850_ok : RunOK pI850 850 (runFrom pI850 (fmask pI850) (cmask pI850) (hmask pI850) 1 849 (true, (init pI850), (init pI850))) ∧ intTest pI850 (runFrom pI850 (fmask pI850) (cmask pI850) (hmask pI850) 1 849 (true, (init pI850), (init pI850))) 850 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I850_fin) true) (by decide) rfl I850_fin intTest_fst
theorem link850 : linkOK pL850 pH850 pI850 = true := by decide +kernel
theorem cvx850 : ConvexBetweenHumps 850 :=
  cvx_of L850_ok H850_ok I850_ok link850 (by decide)
theorem cenlink850 : cenLinkOK pI850 850 = true := by decide +kernel
theorem cen850 : CenterUniqueMin 850 ∧ DipHyp 850 ∧ OnePointHyps 850 :=
  cen_of L850_ok H850_ok I850_ok link850 cenlink850

/-! ### `N = 851` -/

def pL851 : Prm := ⟨75, 35, 37, 853, 11, 18446744073709551616, 196171264372990459, 196171264372990459⟩
def pH851 : Prm := ⟨75, 35, 37, 853, 11, 18446744073709551616, 196173463396246011, 196173463396246011⟩
def pI851 : Prm := ⟨63, 31, 29, 853, 11, 18446744073709551616, 196171264372990459, 196173463396246011⟩
theorem L851_fin : (prmOK pL851 851 && ptTest pL851 (runFrom pL851 (fmask pL851) (cmask pL851) (hmask pL851) 1 850 (true, (init pL851), (init pL851))) 851 426 false) = true := by
  decide +kernel
theorem L851_ok : RunOK pL851 851 (runFrom pL851 (fmask pL851) (cmask pL851) (hmask pL851) 1 850 (true, (init pL851), (init pL851))) ∧ ptTest pL851 (runFrom pL851 (fmask pL851) (cmask pL851) (hmask pL851) 1 850 (true, (init pL851), (init pL851))) 851 426 false = true :=
  fin_run (runOK_init (prmOK_of_and L851_fin) true) (by decide) rfl L851_fin ptTest_fst
theorem H851_fin : (prmOK pH851 851 && ptTest pH851 (runFrom pH851 (fmask pH851) (cmask pH851) (hmask pH851) 1 850 (true, (init pH851), (init pH851))) 851 426 true) = true := by
  decide +kernel
theorem H851_ok : RunOK pH851 851 (runFrom pH851 (fmask pH851) (cmask pH851) (hmask pH851) 1 850 (true, (init pH851), (init pH851))) ∧ ptTest pH851 (runFrom pH851 (fmask pH851) (cmask pH851) (hmask pH851) 1 850 (true, (init pH851), (init pH851))) 851 426 true = true :=
  fin_run (runOK_init (prmOK_of_and H851_fin) true) (by decide) rfl H851_fin ptTest_fst
theorem I851_fin : (prmOK pI851 851 && intTest pI851 (runFrom pI851 (fmask pI851) (cmask pI851) (hmask pI851) 1 850 (true, (init pI851), (init pI851))) 851 17 false) = true := by
  decide +kernel
theorem I851_ok : RunOK pI851 851 (runFrom pI851 (fmask pI851) (cmask pI851) (hmask pI851) 1 850 (true, (init pI851), (init pI851))) ∧ intTest pI851 (runFrom pI851 (fmask pI851) (cmask pI851) (hmask pI851) 1 850 (true, (init pI851), (init pI851))) 851 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I851_fin) true) (by decide) rfl I851_fin intTest_fst
theorem link851 : linkOK pL851 pH851 pI851 = true := by decide +kernel
theorem cvx851 : ConvexBetweenHumps 851 :=
  cvx_of L851_ok H851_ok I851_ok link851 (by decide)

/-! ### `N = 852` -/

def pL852 : Prm := ⟨75, 35, 37, 854, 11, 18446744073709551616, 195989054730514723, 195989054730514723⟩
def pH852 : Prm := ⟨75, 35, 37, 854, 11, 18446744073709551616, 195991253753770275, 195991253753770275⟩
def pI852 : Prm := ⟨63, 31, 29, 854, 11, 18446744073709551616, 195989054730514723, 195991253753770275⟩
theorem L852_fin : (prmOK pL852 852 && ptTest pL852 (runFrom pL852 (fmask pL852) (cmask pL852) (hmask pL852) 1 851 (true, (init pL852), (init pL852))) 852 426 false) = true := by
  decide +kernel
theorem L852_ok : RunOK pL852 852 (runFrom pL852 (fmask pL852) (cmask pL852) (hmask pL852) 1 851 (true, (init pL852), (init pL852))) ∧ ptTest pL852 (runFrom pL852 (fmask pL852) (cmask pL852) (hmask pL852) 1 851 (true, (init pL852), (init pL852))) 852 426 false = true :=
  fin_run (runOK_init (prmOK_of_and L852_fin) true) (by decide) rfl L852_fin ptTest_fst
theorem H852_fin : (prmOK pH852 852 && ptTest pH852 (runFrom pH852 (fmask pH852) (cmask pH852) (hmask pH852) 1 851 (true, (init pH852), (init pH852))) 852 426 true) = true := by
  decide +kernel
theorem H852_ok : RunOK pH852 852 (runFrom pH852 (fmask pH852) (cmask pH852) (hmask pH852) 1 851 (true, (init pH852), (init pH852))) ∧ ptTest pH852 (runFrom pH852 (fmask pH852) (cmask pH852) (hmask pH852) 1 851 (true, (init pH852), (init pH852))) 852 426 true = true :=
  fin_run (runOK_init (prmOK_of_and H852_fin) true) (by decide) rfl H852_fin ptTest_fst
theorem I852_fin : (prmOK pI852 852 && intTest pI852 (runFrom pI852 (fmask pI852) (cmask pI852) (hmask pI852) 1 851 (true, (init pI852), (init pI852))) 852 17 true) = true := by
  decide +kernel
theorem I852_ok : RunOK pI852 852 (runFrom pI852 (fmask pI852) (cmask pI852) (hmask pI852) 1 851 (true, (init pI852), (init pI852))) ∧ intTest pI852 (runFrom pI852 (fmask pI852) (cmask pI852) (hmask pI852) 1 851 (true, (init pI852), (init pI852))) 852 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I852_fin) true) (by decide) rfl I852_fin intTest_fst
theorem link852 : linkOK pL852 pH852 pI852 = true := by decide +kernel
theorem cvx852 : ConvexBetweenHumps 852 :=
  cvx_of L852_ok H852_ok I852_ok link852 (by decide)
theorem cenlink852 : cenLinkOK pI852 852 = true := by decide +kernel
theorem cen852 : CenterUniqueMin 852 ∧ DipHyp 852 ∧ OnePointHyps 852 :=
  cen_of L852_ok H852_ok I852_ok link852 cenlink852

/-! ### `N = 853` -/

def pL853 : Prm := ⟨75, 35, 37, 855, 11, 18446744073709551616, 195807027917519530, 195807027917519530⟩
def pH853 : Prm := ⟨75, 35, 37, 855, 11, 18446744073709551616, 195809226940775082, 195809226940775082⟩
def pI853 : Prm := ⟨63, 31, 29, 855, 11, 18446744073709551616, 195807027917519530, 195809226940775082⟩
theorem L853_fin : (prmOK pL853 853 && ptTest pL853 (runFrom pL853 (fmask pL853) (cmask pL853) (hmask pL853) 1 852 (true, (init pL853), (init pL853))) 853 427 false) = true := by
  decide +kernel
theorem L853_ok : RunOK pL853 853 (runFrom pL853 (fmask pL853) (cmask pL853) (hmask pL853) 1 852 (true, (init pL853), (init pL853))) ∧ ptTest pL853 (runFrom pL853 (fmask pL853) (cmask pL853) (hmask pL853) 1 852 (true, (init pL853), (init pL853))) 853 427 false = true :=
  fin_run (runOK_init (prmOK_of_and L853_fin) true) (by decide) rfl L853_fin ptTest_fst
theorem H853_fin : (prmOK pH853 853 && ptTest pH853 (runFrom pH853 (fmask pH853) (cmask pH853) (hmask pH853) 1 852 (true, (init pH853), (init pH853))) 853 427 true) = true := by
  decide +kernel
theorem H853_ok : RunOK pH853 853 (runFrom pH853 (fmask pH853) (cmask pH853) (hmask pH853) 1 852 (true, (init pH853), (init pH853))) ∧ ptTest pH853 (runFrom pH853 (fmask pH853) (cmask pH853) (hmask pH853) 1 852 (true, (init pH853), (init pH853))) 853 427 true = true :=
  fin_run (runOK_init (prmOK_of_and H853_fin) true) (by decide) rfl H853_fin ptTest_fst
theorem I853_fin : (prmOK pI853 853 && intTest pI853 (runFrom pI853 (fmask pI853) (cmask pI853) (hmask pI853) 1 852 (true, (init pI853), (init pI853))) 853 17 false) = true := by
  decide +kernel
theorem I853_ok : RunOK pI853 853 (runFrom pI853 (fmask pI853) (cmask pI853) (hmask pI853) 1 852 (true, (init pI853), (init pI853))) ∧ intTest pI853 (runFrom pI853 (fmask pI853) (cmask pI853) (hmask pI853) 1 852 (true, (init pI853), (init pI853))) 853 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I853_fin) true) (by decide) rfl I853_fin intTest_fst
theorem link853 : linkOK pL853 pH853 pI853 = true := by decide +kernel
theorem cvx853 : ConvexBetweenHumps 853 :=
  cvx_of L853_ok H853_ok I853_ok link853 (by decide)

/-! ### `N = 854` -/

def pL854 : Prm := ⟨75, 35, 37, 856, 11, 18446744073709551616, 195625559154429932, 195625559154429932⟩
def pH854 : Prm := ⟨75, 35, 37, 856, 11, 18446744073709551616, 195627758177685484, 195627758177685484⟩
def pI854 : Prm := ⟨63, 31, 29, 856, 11, 18446744073709551616, 195625559154429932, 195627758177685484⟩
theorem L854_fin : (prmOK pL854 854 && ptTest pL854 (runFrom pL854 (fmask pL854) (cmask pL854) (hmask pL854) 1 853 (true, (init pL854), (init pL854))) 854 427 false) = true := by
  decide +kernel
theorem L854_ok : RunOK pL854 854 (runFrom pL854 (fmask pL854) (cmask pL854) (hmask pL854) 1 853 (true, (init pL854), (init pL854))) ∧ ptTest pL854 (runFrom pL854 (fmask pL854) (cmask pL854) (hmask pL854) 1 853 (true, (init pL854), (init pL854))) 854 427 false = true :=
  fin_run (runOK_init (prmOK_of_and L854_fin) true) (by decide) rfl L854_fin ptTest_fst
theorem H854_fin : (prmOK pH854 854 && ptTest pH854 (runFrom pH854 (fmask pH854) (cmask pH854) (hmask pH854) 1 853 (true, (init pH854), (init pH854))) 854 427 true) = true := by
  decide +kernel
theorem H854_ok : RunOK pH854 854 (runFrom pH854 (fmask pH854) (cmask pH854) (hmask pH854) 1 853 (true, (init pH854), (init pH854))) ∧ ptTest pH854 (runFrom pH854 (fmask pH854) (cmask pH854) (hmask pH854) 1 853 (true, (init pH854), (init pH854))) 854 427 true = true :=
  fin_run (runOK_init (prmOK_of_and H854_fin) true) (by decide) rfl H854_fin ptTest_fst
theorem I854_fin : (prmOK pI854 854 && intTest pI854 (runFrom pI854 (fmask pI854) (cmask pI854) (hmask pI854) 1 853 (true, (init pI854), (init pI854))) 854 17 true) = true := by
  decide +kernel
theorem I854_ok : RunOK pI854 854 (runFrom pI854 (fmask pI854) (cmask pI854) (hmask pI854) 1 853 (true, (init pI854), (init pI854))) ∧ intTest pI854 (runFrom pI854 (fmask pI854) (cmask pI854) (hmask pI854) 1 853 (true, (init pI854), (init pI854))) 854 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I854_fin) true) (by decide) rfl I854_fin intTest_fst
theorem link854 : linkOK pL854 pH854 pI854 = true := by decide +kernel
theorem cvx854 : ConvexBetweenHumps 854 :=
  cvx_of L854_ok H854_ok I854_ok link854 (by decide)
theorem cenlink854 : cenLinkOK pI854 854 = true := by decide +kernel
theorem cen854 : CenterUniqueMin 854 ∧ DipHyp 854 ∧ OnePointHyps 854 :=
  cen_of L854_ok H854_ok I854_ok link854 cenlink854

/-! ### `N = 855` -/

def pL855 : Prm := ⟨75, 35, 37, 857, 11, 18446744073709551616, 195444272223350085, 195444272223350085⟩
def pH855 : Prm := ⟨75, 35, 37, 857, 11, 18446744073709551616, 195446471246605637, 195446471246605637⟩
def pI855 : Prm := ⟨63, 31, 29, 857, 11, 18446744073709551616, 195444272223350085, 195446471246605637⟩
theorem L855_fin : (prmOK pL855 855 && ptTest pL855 (runFrom pL855 (fmask pL855) (cmask pL855) (hmask pL855) 1 854 (true, (init pL855), (init pL855))) 855 428 false) = true := by
  decide +kernel
theorem L855_ok : RunOK pL855 855 (runFrom pL855 (fmask pL855) (cmask pL855) (hmask pL855) 1 854 (true, (init pL855), (init pL855))) ∧ ptTest pL855 (runFrom pL855 (fmask pL855) (cmask pL855) (hmask pL855) 1 854 (true, (init pL855), (init pL855))) 855 428 false = true :=
  fin_run (runOK_init (prmOK_of_and L855_fin) true) (by decide) rfl L855_fin ptTest_fst
theorem H855_fin : (prmOK pH855 855 && ptTest pH855 (runFrom pH855 (fmask pH855) (cmask pH855) (hmask pH855) 1 854 (true, (init pH855), (init pH855))) 855 428 true) = true := by
  decide +kernel
theorem H855_ok : RunOK pH855 855 (runFrom pH855 (fmask pH855) (cmask pH855) (hmask pH855) 1 854 (true, (init pH855), (init pH855))) ∧ ptTest pH855 (runFrom pH855 (fmask pH855) (cmask pH855) (hmask pH855) 1 854 (true, (init pH855), (init pH855))) 855 428 true = true :=
  fin_run (runOK_init (prmOK_of_and H855_fin) true) (by decide) rfl H855_fin ptTest_fst
theorem I855_fin : (prmOK pI855 855 && intTest pI855 (runFrom pI855 (fmask pI855) (cmask pI855) (hmask pI855) 1 854 (true, (init pI855), (init pI855))) 855 17 false) = true := by
  decide +kernel
theorem I855_ok : RunOK pI855 855 (runFrom pI855 (fmask pI855) (cmask pI855) (hmask pI855) 1 854 (true, (init pI855), (init pI855))) ∧ intTest pI855 (runFrom pI855 (fmask pI855) (cmask pI855) (hmask pI855) 1 854 (true, (init pI855), (init pI855))) 855 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I855_fin) true) (by decide) rfl I855_fin intTest_fst
theorem link855 : linkOK pL855 pH855 pI855 = true := by decide +kernel
theorem cvx855 : ConvexBetweenHumps 855 :=
  cvx_of L855_ok H855_ok I855_ok link855 (by decide)

/-! ### `N = 856` -/

def pL856 : Prm := ⟨75, 35, 37, 858, 11, 18446744073709551616, 195263539670056276, 195263539670056276⟩
def pH856 : Prm := ⟨75, 35, 37, 858, 11, 18446744073709551616, 195265738693311828, 195265738693311828⟩
def pI856 : Prm := ⟨63, 31, 29, 858, 11, 18446744073709551616, 195263539670056276, 195265738693311828⟩
theorem L856_fin : (prmOK pL856 856 && ptTest pL856 (runFrom pL856 (fmask pL856) (cmask pL856) (hmask pL856) 1 855 (true, (init pL856), (init pL856))) 856 428 false) = true := by
  decide +kernel
theorem L856_ok : RunOK pL856 856 (runFrom pL856 (fmask pL856) (cmask pL856) (hmask pL856) 1 855 (true, (init pL856), (init pL856))) ∧ ptTest pL856 (runFrom pL856 (fmask pL856) (cmask pL856) (hmask pL856) 1 855 (true, (init pL856), (init pL856))) 856 428 false = true :=
  fin_run (runOK_init (prmOK_of_and L856_fin) true) (by decide) rfl L856_fin ptTest_fst
theorem H856_fin : (prmOK pH856 856 && ptTest pH856 (runFrom pH856 (fmask pH856) (cmask pH856) (hmask pH856) 1 855 (true, (init pH856), (init pH856))) 856 428 true) = true := by
  decide +kernel
theorem H856_ok : RunOK pH856 856 (runFrom pH856 (fmask pH856) (cmask pH856) (hmask pH856) 1 855 (true, (init pH856), (init pH856))) ∧ ptTest pH856 (runFrom pH856 (fmask pH856) (cmask pH856) (hmask pH856) 1 855 (true, (init pH856), (init pH856))) 856 428 true = true :=
  fin_run (runOK_init (prmOK_of_and H856_fin) true) (by decide) rfl H856_fin ptTest_fst
theorem I856_fin : (prmOK pI856 856 && intTest pI856 (runFrom pI856 (fmask pI856) (cmask pI856) (hmask pI856) 1 855 (true, (init pI856), (init pI856))) 856 17 true) = true := by
  decide +kernel
theorem I856_ok : RunOK pI856 856 (runFrom pI856 (fmask pI856) (cmask pI856) (hmask pI856) 1 855 (true, (init pI856), (init pI856))) ∧ intTest pI856 (runFrom pI856 (fmask pI856) (cmask pI856) (hmask pI856) 1 855 (true, (init pI856), (init pI856))) 856 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I856_fin) true) (by decide) rfl I856_fin intTest_fst
theorem link856 : linkOK pL856 pH856 pI856 = true := by decide +kernel
theorem cvx856 : ConvexBetweenHumps 856 :=
  cvx_of L856_ok H856_ok I856_ok link856 (by decide)
theorem cenlink856 : cenLinkOK pI856 856 = true := by decide +kernel
theorem cen856 : CenterUniqueMin 856 ∧ DipHyp 856 ∧ OnePointHyps 856 :=
  cen_of L856_ok H856_ok I856_ok link856 cenlink856

/-! ### `N = 857` -/

def pL857 : Prm := ⟨75, 35, 37, 859, 11, 18446744073709551616, 195082987958606337, 195082987958606337⟩
def pH857 : Prm := ⟨75, 35, 37, 859, 11, 18446744073709551616, 195085186981861889, 195085186981861889⟩
def pI857 : Prm := ⟨63, 31, 29, 859, 11, 18446744073709551616, 195082987958606337, 195085186981861889⟩
theorem L857_fin : (prmOK pL857 857 && ptTest pL857 (runFrom pL857 (fmask pL857) (cmask pL857) (hmask pL857) 1 856 (true, (init pL857), (init pL857))) 857 429 false) = true := by
  decide +kernel
theorem L857_ok : RunOK pL857 857 (runFrom pL857 (fmask pL857) (cmask pL857) (hmask pL857) 1 856 (true, (init pL857), (init pL857))) ∧ ptTest pL857 (runFrom pL857 (fmask pL857) (cmask pL857) (hmask pL857) 1 856 (true, (init pL857), (init pL857))) 857 429 false = true :=
  fin_run (runOK_init (prmOK_of_and L857_fin) true) (by decide) rfl L857_fin ptTest_fst
theorem H857_fin : (prmOK pH857 857 && ptTest pH857 (runFrom pH857 (fmask pH857) (cmask pH857) (hmask pH857) 1 856 (true, (init pH857), (init pH857))) 857 429 true) = true := by
  decide +kernel
theorem H857_ok : RunOK pH857 857 (runFrom pH857 (fmask pH857) (cmask pH857) (hmask pH857) 1 856 (true, (init pH857), (init pH857))) ∧ ptTest pH857 (runFrom pH857 (fmask pH857) (cmask pH857) (hmask pH857) 1 856 (true, (init pH857), (init pH857))) 857 429 true = true :=
  fin_run (runOK_init (prmOK_of_and H857_fin) true) (by decide) rfl H857_fin ptTest_fst
theorem I857_fin : (prmOK pI857 857 && intTest pI857 (runFrom pI857 (fmask pI857) (cmask pI857) (hmask pI857) 1 856 (true, (init pI857), (init pI857))) 857 17 false) = true := by
  decide +kernel
theorem I857_ok : RunOK pI857 857 (runFrom pI857 (fmask pI857) (cmask pI857) (hmask pI857) 1 856 (true, (init pI857), (init pI857))) ∧ intTest pI857 (runFrom pI857 (fmask pI857) (cmask pI857) (hmask pI857) 1 856 (true, (init pI857), (init pI857))) 857 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I857_fin) true) (by decide) rfl I857_fin intTest_fst
theorem link857 : linkOK pL857 pH857 pI857 = true := by decide +kernel
theorem cvx857 : ConvexBetweenHumps 857 :=
  cvx_of L857_ok H857_ok I857_ok link857 (by decide)

/-! ### `N = 858` -/

def pL858 : Prm := ⟨75, 35, 37, 860, 11, 18446744073709551616, 194902986985418276, 194902986985418276⟩
def pH858 : Prm := ⟨75, 35, 37, 860, 11, 18446744073709551616, 194905186008673828, 194905186008673828⟩
def pI858 : Prm := ⟨63, 31, 29, 860, 11, 18446744073709551616, 194902986985418276, 194905186008673828⟩
theorem L858_fin : (prmOK pL858 858 && ptTest pL858 (runFrom pL858 (fmask pL858) (cmask pL858) (hmask pL858) 1 857 (true, (init pL858), (init pL858))) 858 429 false) = true := by
  decide +kernel
theorem L858_ok : RunOK pL858 858 (runFrom pL858 (fmask pL858) (cmask pL858) (hmask pL858) 1 857 (true, (init pL858), (init pL858))) ∧ ptTest pL858 (runFrom pL858 (fmask pL858) (cmask pL858) (hmask pL858) 1 857 (true, (init pL858), (init pL858))) 858 429 false = true :=
  fin_run (runOK_init (prmOK_of_and L858_fin) true) (by decide) rfl L858_fin ptTest_fst
theorem H858_fin : (prmOK pH858 858 && ptTest pH858 (runFrom pH858 (fmask pH858) (cmask pH858) (hmask pH858) 1 857 (true, (init pH858), (init pH858))) 858 429 true) = true := by
  decide +kernel
theorem H858_ok : RunOK pH858 858 (runFrom pH858 (fmask pH858) (cmask pH858) (hmask pH858) 1 857 (true, (init pH858), (init pH858))) ∧ ptTest pH858 (runFrom pH858 (fmask pH858) (cmask pH858) (hmask pH858) 1 857 (true, (init pH858), (init pH858))) 858 429 true = true :=
  fin_run (runOK_init (prmOK_of_and H858_fin) true) (by decide) rfl H858_fin ptTest_fst
theorem I858_fin : (prmOK pI858 858 && intTest pI858 (runFrom pI858 (fmask pI858) (cmask pI858) (hmask pI858) 1 857 (true, (init pI858), (init pI858))) 858 17 true) = true := by
  decide +kernel
theorem I858_ok : RunOK pI858 858 (runFrom pI858 (fmask pI858) (cmask pI858) (hmask pI858) 1 857 (true, (init pI858), (init pI858))) ∧ intTest pI858 (runFrom pI858 (fmask pI858) (cmask pI858) (hmask pI858) 1 857 (true, (init pI858), (init pI858))) 858 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I858_fin) true) (by decide) rfl I858_fin intTest_fst
theorem link858 : linkOK pL858 pH858 pI858 = true := by decide +kernel
theorem cvx858 : ConvexBetweenHumps 858 :=
  cvx_of L858_ok H858_ok I858_ok link858 (by decide)
theorem cenlink858 : cenLinkOK pI858 858 = true := by decide +kernel
theorem cen858 : CenterUniqueMin 858 ∧ DipHyp 858 ∧ OnePointHyps 858 :=
  cen_of L858_ok H858_ok I858_ok link858 cenlink858

/-! ### `N = 859` -/

def pL859 : Prm := ⟨75, 35, 37, 861, 11, 18446744073709551616, 194723165871176222, 194723165871176222⟩
def pH859 : Prm := ⟨75, 35, 37, 861, 11, 18446744073709551616, 194725364894431774, 194725364894431774⟩
def pI859 : Prm := ⟨63, 31, 29, 861, 11, 18446744073709551616, 194723165871176222, 194725364894431774⟩
theorem L859_fin : (prmOK pL859 859 && ptTest pL859 (runFrom pL859 (fmask pL859) (cmask pL859) (hmask pL859) 1 858 (true, (init pL859), (init pL859))) 859 430 false) = true := by
  decide +kernel
theorem L859_ok : RunOK pL859 859 (runFrom pL859 (fmask pL859) (cmask pL859) (hmask pL859) 1 858 (true, (init pL859), (init pL859))) ∧ ptTest pL859 (runFrom pL859 (fmask pL859) (cmask pL859) (hmask pL859) 1 858 (true, (init pL859), (init pL859))) 859 430 false = true :=
  fin_run (runOK_init (prmOK_of_and L859_fin) true) (by decide) rfl L859_fin ptTest_fst
theorem H859_fin : (prmOK pH859 859 && ptTest pH859 (runFrom pH859 (fmask pH859) (cmask pH859) (hmask pH859) 1 858 (true, (init pH859), (init pH859))) 859 430 true) = true := by
  decide +kernel
theorem H859_ok : RunOK pH859 859 (runFrom pH859 (fmask pH859) (cmask pH859) (hmask pH859) 1 858 (true, (init pH859), (init pH859))) ∧ ptTest pH859 (runFrom pH859 (fmask pH859) (cmask pH859) (hmask pH859) 1 858 (true, (init pH859), (init pH859))) 859 430 true = true :=
  fin_run (runOK_init (prmOK_of_and H859_fin) true) (by decide) rfl H859_fin ptTest_fst
theorem I859_fin : (prmOK pI859 859 && intTest pI859 (runFrom pI859 (fmask pI859) (cmask pI859) (hmask pI859) 1 858 (true, (init pI859), (init pI859))) 859 17 false) = true := by
  decide +kernel
theorem I859_ok : RunOK pI859 859 (runFrom pI859 (fmask pI859) (cmask pI859) (hmask pI859) 1 858 (true, (init pI859), (init pI859))) ∧ intTest pI859 (runFrom pI859 (fmask pI859) (cmask pI859) (hmask pI859) 1 858 (true, (init pI859), (init pI859))) 859 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I859_fin) true) (by decide) rfl I859_fin intTest_fst
theorem link859 : linkOK pL859 pH859 pI859 = true := by decide +kernel
theorem cvx859 : ConvexBetweenHumps 859 :=
  cvx_of L859_ok H859_ok I859_ok link859 (by decide)

/-! ### `N = 860` -/

def pL860 : Prm := ⟨75, 35, 37, 862, 11, 18446744073709551616, 194543891887861455, 194543891887861455⟩
def pH860 : Prm := ⟨75, 35, 37, 862, 11, 18446744073709551616, 194546090911117007, 194546090911117007⟩
def pI860 : Prm := ⟨63, 31, 29, 862, 11, 18446744073709551616, 194543891887861455, 194546090911117007⟩
theorem L860_fin : (prmOK pL860 860 && ptTest pL860 (runFrom pL860 (fmask pL860) (cmask pL860) (hmask pL860) 1 859 (true, (init pL860), (init pL860))) 860 430 false) = true := by
  decide +kernel
theorem L860_ok : RunOK pL860 860 (runFrom pL860 (fmask pL860) (cmask pL860) (hmask pL860) 1 859 (true, (init pL860), (init pL860))) ∧ ptTest pL860 (runFrom pL860 (fmask pL860) (cmask pL860) (hmask pL860) 1 859 (true, (init pL860), (init pL860))) 860 430 false = true :=
  fin_run (runOK_init (prmOK_of_and L860_fin) true) (by decide) rfl L860_fin ptTest_fst
theorem H860_fin : (prmOK pH860 860 && ptTest pH860 (runFrom pH860 (fmask pH860) (cmask pH860) (hmask pH860) 1 859 (true, (init pH860), (init pH860))) 860 430 true) = true := by
  decide +kernel
theorem H860_ok : RunOK pH860 860 (runFrom pH860 (fmask pH860) (cmask pH860) (hmask pH860) 1 859 (true, (init pH860), (init pH860))) ∧ ptTest pH860 (runFrom pH860 (fmask pH860) (cmask pH860) (hmask pH860) 1 859 (true, (init pH860), (init pH860))) 860 430 true = true :=
  fin_run (runOK_init (prmOK_of_and H860_fin) true) (by decide) rfl H860_fin ptTest_fst
theorem I860_fin : (prmOK pI860 860 && intTest pI860 (runFrom pI860 (fmask pI860) (cmask pI860) (hmask pI860) 1 859 (true, (init pI860), (init pI860))) 860 17 true) = true := by
  decide +kernel
theorem I860_ok : RunOK pI860 860 (runFrom pI860 (fmask pI860) (cmask pI860) (hmask pI860) 1 859 (true, (init pI860), (init pI860))) ∧ intTest pI860 (runFrom pI860 (fmask pI860) (cmask pI860) (hmask pI860) 1 859 (true, (init pI860), (init pI860))) 860 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I860_fin) true) (by decide) rfl I860_fin intTest_fst
theorem link860 : linkOK pL860 pH860 pI860 = true := by decide +kernel
theorem cvx860 : ConvexBetweenHumps 860 :=
  cvx_of L860_ok H860_ok I860_ok link860 (by decide)
theorem cenlink860 : cenLinkOK pI860 860 = true := by decide +kernel
theorem cen860 : CenterUniqueMin 860 ∧ DipHyp 860 ∧ OnePointHyps 860 :=
  cen_of L860_ok H860_ok I860_ok link860 cenlink860

/-! ### `N = 861` -/

def pL861 : Prm := ⟨75, 35, 37, 863, 11, 18446744073709551616, 194364796787807506, 194364796787807506⟩
def pH861 : Prm := ⟨75, 35, 37, 863, 11, 18446744073709551616, 194366995811063058, 194366995811063058⟩
def pI861 : Prm := ⟨63, 31, 29, 863, 11, 18446744073709551616, 194364796787807506, 194366995811063058⟩
theorem L861_fin : (prmOK pL861 861 && ptTest pL861 (runFrom pL861 (fmask pL861) (cmask pL861) (hmask pL861) 1 860 (true, (init pL861), (init pL861))) 861 431 false) = true := by
  decide +kernel
theorem L861_ok : RunOK pL861 861 (runFrom pL861 (fmask pL861) (cmask pL861) (hmask pL861) 1 860 (true, (init pL861), (init pL861))) ∧ ptTest pL861 (runFrom pL861 (fmask pL861) (cmask pL861) (hmask pL861) 1 860 (true, (init pL861), (init pL861))) 861 431 false = true :=
  fin_run (runOK_init (prmOK_of_and L861_fin) true) (by decide) rfl L861_fin ptTest_fst
theorem H861_fin : (prmOK pH861 861 && ptTest pH861 (runFrom pH861 (fmask pH861) (cmask pH861) (hmask pH861) 1 860 (true, (init pH861), (init pH861))) 861 431 true) = true := by
  decide +kernel
theorem H861_ok : RunOK pH861 861 (runFrom pH861 (fmask pH861) (cmask pH861) (hmask pH861) 1 860 (true, (init pH861), (init pH861))) ∧ ptTest pH861 (runFrom pH861 (fmask pH861) (cmask pH861) (hmask pH861) 1 860 (true, (init pH861), (init pH861))) 861 431 true = true :=
  fin_run (runOK_init (prmOK_of_and H861_fin) true) (by decide) rfl H861_fin ptTest_fst
theorem I861_fin : (prmOK pI861 861 && intTest pI861 (runFrom pI861 (fmask pI861) (cmask pI861) (hmask pI861) 1 860 (true, (init pI861), (init pI861))) 861 17 false) = true := by
  decide +kernel
theorem I861_ok : RunOK pI861 861 (runFrom pI861 (fmask pI861) (cmask pI861) (hmask pI861) 1 860 (true, (init pI861), (init pI861))) ∧ intTest pI861 (runFrom pI861 (fmask pI861) (cmask pI861) (hmask pI861) 1 860 (true, (init pI861), (init pI861))) 861 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I861_fin) true) (by decide) rfl I861_fin intTest_fst
theorem link861 : linkOK pL861 pH861 pI861 = true := by decide +kernel
theorem cvx861 : ConvexBetweenHumps 861 :=
  cvx_of L861_ok H861_ok I861_ok link861 (by decide)

/-! ### `N = 862` -/

def pL862 : Prm := ⟨75, 35, 37, 864, 11, 18446744073709551616, 194186245243240676, 194186245243240676⟩
def pH862 : Prm := ⟨75, 35, 37, 864, 11, 18446744073709551616, 194188444266496228, 194188444266496228⟩
def pI862 : Prm := ⟨63, 31, 29, 864, 11, 18446744073709551616, 194186245243240676, 194188444266496228⟩
theorem L862_fin : (prmOK pL862 862 && ptTest pL862 (runFrom pL862 (fmask pL862) (cmask pL862) (hmask pL862) 1 861 (true, (init pL862), (init pL862))) 862 431 false) = true := by
  decide +kernel
theorem L862_ok : RunOK pL862 862 (runFrom pL862 (fmask pL862) (cmask pL862) (hmask pL862) 1 861 (true, (init pL862), (init pL862))) ∧ ptTest pL862 (runFrom pL862 (fmask pL862) (cmask pL862) (hmask pL862) 1 861 (true, (init pL862), (init pL862))) 862 431 false = true :=
  fin_run (runOK_init (prmOK_of_and L862_fin) true) (by decide) rfl L862_fin ptTest_fst
theorem H862_fin : (prmOK pH862 862 && ptTest pH862 (runFrom pH862 (fmask pH862) (cmask pH862) (hmask pH862) 1 861 (true, (init pH862), (init pH862))) 862 431 true) = true := by
  decide +kernel
theorem H862_ok : RunOK pH862 862 (runFrom pH862 (fmask pH862) (cmask pH862) (hmask pH862) 1 861 (true, (init pH862), (init pH862))) ∧ ptTest pH862 (runFrom pH862 (fmask pH862) (cmask pH862) (hmask pH862) 1 861 (true, (init pH862), (init pH862))) 862 431 true = true :=
  fin_run (runOK_init (prmOK_of_and H862_fin) true) (by decide) rfl H862_fin ptTest_fst
theorem I862_fin : (prmOK pI862 862 && intTest pI862 (runFrom pI862 (fmask pI862) (cmask pI862) (hmask pI862) 1 861 (true, (init pI862), (init pI862))) 862 17 true) = true := by
  decide +kernel
theorem I862_ok : RunOK pI862 862 (runFrom pI862 (fmask pI862) (cmask pI862) (hmask pI862) 1 861 (true, (init pI862), (init pI862))) ∧ intTest pI862 (runFrom pI862 (fmask pI862) (cmask pI862) (hmask pI862) 1 861 (true, (init pI862), (init pI862))) 862 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I862_fin) true) (by decide) rfl I862_fin intTest_fst
theorem link862 : linkOK pL862 pH862 pI862 = true := by decide +kernel
theorem cvx862 : ConvexBetweenHumps 862 :=
  cvx_of L862_ok H862_ok I862_ok link862 (by decide)
theorem cenlink862 : cenLinkOK pI862 862 = true := by decide +kernel
theorem cen862 : CenterUniqueMin 862 ∧ DipHyp 862 ∧ OnePointHyps 862 :=
  cen_of L862_ok H862_ok I862_ok link862 cenlink862

/-! ### `N = 863` -/

def pL863 : Prm := ⟨75, 35, 37, 865, 11, 18446744073709551616, 194007871613333025, 194007871613333025⟩
def pH863 : Prm := ⟨75, 35, 37, 865, 11, 18446744073709551616, 194010070636588577, 194010070636588577⟩
def pI863 : Prm := ⟨63, 31, 29, 865, 11, 18446744073709551616, 194007871613333025, 194010070636588577⟩
theorem L863_fin : (prmOK pL863 863 && ptTest pL863 (runFrom pL863 (fmask pL863) (cmask pL863) (hmask pL863) 1 862 (true, (init pL863), (init pL863))) 863 432 false) = true := by
  decide +kernel
theorem L863_ok : RunOK pL863 863 (runFrom pL863 (fmask pL863) (cmask pL863) (hmask pL863) 1 862 (true, (init pL863), (init pL863))) ∧ ptTest pL863 (runFrom pL863 (fmask pL863) (cmask pL863) (hmask pL863) 1 862 (true, (init pL863), (init pL863))) 863 432 false = true :=
  fin_run (runOK_init (prmOK_of_and L863_fin) true) (by decide) rfl L863_fin ptTest_fst
theorem H863_fin : (prmOK pH863 863 && ptTest pH863 (runFrom pH863 (fmask pH863) (cmask pH863) (hmask pH863) 1 862 (true, (init pH863), (init pH863))) 863 432 true) = true := by
  decide +kernel
theorem H863_ok : RunOK pH863 863 (runFrom pH863 (fmask pH863) (cmask pH863) (hmask pH863) 1 862 (true, (init pH863), (init pH863))) ∧ ptTest pH863 (runFrom pH863 (fmask pH863) (cmask pH863) (hmask pH863) 1 862 (true, (init pH863), (init pH863))) 863 432 true = true :=
  fin_run (runOK_init (prmOK_of_and H863_fin) true) (by decide) rfl H863_fin ptTest_fst
theorem I863_fin : (prmOK pI863 863 && intTest pI863 (runFrom pI863 (fmask pI863) (cmask pI863) (hmask pI863) 1 862 (true, (init pI863), (init pI863))) 863 17 false) = true := by
  decide +kernel
theorem I863_ok : RunOK pI863 863 (runFrom pI863 (fmask pI863) (cmask pI863) (hmask pI863) 1 862 (true, (init pI863), (init pI863))) ∧ intTest pI863 (runFrom pI863 (fmask pI863) (cmask pI863) (hmask pI863) 1 862 (true, (init pI863), (init pI863))) 863 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I863_fin) true) (by decide) rfl I863_fin intTest_fst
theorem link863 : linkOK pL863 pH863 pI863 = true := by decide +kernel
theorem cvx863 : ConvexBetweenHumps 863 :=
  cvx_of L863_ok H863_ok I863_ok link863 (by decide)

/-! ### `N = 864` -/

def pL864 : Prm := ⟨75, 35, 37, 866, 11, 18446744073709551616, 193830037994960915, 193830037994960915⟩
def pH864 : Prm := ⟨75, 35, 37, 866, 11, 18446744073709551616, 193832237018216467, 193832237018216467⟩
def pI864 : Prm := ⟨63, 31, 29, 866, 11, 18446744073709551616, 193830037994960915, 193832237018216467⟩
theorem L864_fin : (prmOK pL864 864 && ptTest pL864 (runFrom pL864 (fmask pL864) (cmask pL864) (hmask pL864) 1 863 (true, (init pL864), (init pL864))) 864 432 false) = true := by
  decide +kernel
theorem L864_ok : RunOK pL864 864 (runFrom pL864 (fmask pL864) (cmask pL864) (hmask pL864) 1 863 (true, (init pL864), (init pL864))) ∧ ptTest pL864 (runFrom pL864 (fmask pL864) (cmask pL864) (hmask pL864) 1 863 (true, (init pL864), (init pL864))) 864 432 false = true :=
  fin_run (runOK_init (prmOK_of_and L864_fin) true) (by decide) rfl L864_fin ptTest_fst
theorem H864_fin : (prmOK pH864 864 && ptTest pH864 (runFrom pH864 (fmask pH864) (cmask pH864) (hmask pH864) 1 863 (true, (init pH864), (init pH864))) 864 432 true) = true := by
  decide +kernel
theorem H864_ok : RunOK pH864 864 (runFrom pH864 (fmask pH864) (cmask pH864) (hmask pH864) 1 863 (true, (init pH864), (init pH864))) ∧ ptTest pH864 (runFrom pH864 (fmask pH864) (cmask pH864) (hmask pH864) 1 863 (true, (init pH864), (init pH864))) 864 432 true = true :=
  fin_run (runOK_init (prmOK_of_and H864_fin) true) (by decide) rfl H864_fin ptTest_fst
theorem I864_fin : (prmOK pI864 864 && intTest pI864 (runFrom pI864 (fmask pI864) (cmask pI864) (hmask pI864) 1 863 (true, (init pI864), (init pI864))) 864 17 true) = true := by
  decide +kernel
theorem I864_ok : RunOK pI864 864 (runFrom pI864 (fmask pI864) (cmask pI864) (hmask pI864) 1 863 (true, (init pI864), (init pI864))) ∧ intTest pI864 (runFrom pI864 (fmask pI864) (cmask pI864) (hmask pI864) 1 863 (true, (init pI864), (init pI864))) 864 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I864_fin) true) (by decide) rfl I864_fin intTest_fst
theorem link864 : linkOK pL864 pH864 pI864 = true := by decide +kernel
theorem cvx864 : ConvexBetweenHumps 864 :=
  cvx_of L864_ok H864_ok I864_ok link864 (by decide)
theorem cenlink864 : cenLinkOK pI864 864 = true := by decide +kernel
theorem cen864 : CenterUniqueMin 864 ∧ DipHyp 864 ∧ OnePointHyps 864 :=
  cen_of L864_ok H864_ok I864_ok link864 cenlink864

/-! ### `N = 865` -/

def pL865 : Prm := ⟨75, 35, 37, 867, 11, 18446744073709551616, 193652381329748343, 193652381329748343⟩
def pH865 : Prm := ⟨75, 35, 37, 867, 11, 18446744073709551616, 193654580353003895, 193654580353003895⟩
def pI865 : Prm := ⟨63, 31, 29, 867, 11, 18446744073709551616, 193652381329748343, 193654580353003895⟩
theorem L865_fin : (prmOK pL865 865 && ptTest pL865 (runFrom pL865 (fmask pL865) (cmask pL865) (hmask pL865) 1 864 (true, (init pL865), (init pL865))) 865 433 false) = true := by
  decide +kernel
theorem L865_ok : RunOK pL865 865 (runFrom pL865 (fmask pL865) (cmask pL865) (hmask pL865) 1 864 (true, (init pL865), (init pL865))) ∧ ptTest pL865 (runFrom pL865 (fmask pL865) (cmask pL865) (hmask pL865) 1 864 (true, (init pL865), (init pL865))) 865 433 false = true :=
  fin_run (runOK_init (prmOK_of_and L865_fin) true) (by decide) rfl L865_fin ptTest_fst
theorem H865_fin : (prmOK pH865 865 && ptTest pH865 (runFrom pH865 (fmask pH865) (cmask pH865) (hmask pH865) 1 864 (true, (init pH865), (init pH865))) 865 433 true) = true := by
  decide +kernel
theorem H865_ok : RunOK pH865 865 (runFrom pH865 (fmask pH865) (cmask pH865) (hmask pH865) 1 864 (true, (init pH865), (init pH865))) ∧ ptTest pH865 (runFrom pH865 (fmask pH865) (cmask pH865) (hmask pH865) 1 864 (true, (init pH865), (init pH865))) 865 433 true = true :=
  fin_run (runOK_init (prmOK_of_and H865_fin) true) (by decide) rfl H865_fin ptTest_fst
theorem I865_fin : (prmOK pI865 865 && intTest pI865 (runFrom pI865 (fmask pI865) (cmask pI865) (hmask pI865) 1 864 (true, (init pI865), (init pI865))) 865 17 false) = true := by
  decide +kernel
theorem I865_ok : RunOK pI865 865 (runFrom pI865 (fmask pI865) (cmask pI865) (hmask pI865) 1 864 (true, (init pI865), (init pI865))) ∧ intTest pI865 (runFrom pI865 (fmask pI865) (cmask pI865) (hmask pI865) 1 864 (true, (init pI865), (init pI865))) 865 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I865_fin) true) (by decide) rfl I865_fin intTest_fst
theorem link865 : linkOK pL865 pH865 pI865 = true := by decide +kernel
theorem cvx865 : ConvexBetweenHumps 865 :=
  cvx_of L865_ok H865_ok I865_ok link865 (by decide)

/-! ### `N = 866` -/

def pL866 : Prm := ⟨75, 35, 37, 868, 11, 18446744073709551616, 193475261163257838, 193475261163257838⟩
def pH866 : Prm := ⟨75, 35, 37, 868, 11, 18446744073709551616, 193477460186513390, 193477460186513390⟩
def pI866 : Prm := ⟨63, 31, 29, 868, 11, 18446744073709551616, 193475261163257838, 193477460186513390⟩
theorem L866_fin : (prmOK pL866 866 && ptTest pL866 (runFrom pL866 (fmask pL866) (cmask pL866) (hmask pL866) 1 865 (true, (init pL866), (init pL866))) 866 433 false) = true := by
  decide +kernel
theorem L866_ok : RunOK pL866 866 (runFrom pL866 (fmask pL866) (cmask pL866) (hmask pL866) 1 865 (true, (init pL866), (init pL866))) ∧ ptTest pL866 (runFrom pL866 (fmask pL866) (cmask pL866) (hmask pL866) 1 865 (true, (init pL866), (init pL866))) 866 433 false = true :=
  fin_run (runOK_init (prmOK_of_and L866_fin) true) (by decide) rfl L866_fin ptTest_fst
theorem H866_fin : (prmOK pH866 866 && ptTest pH866 (runFrom pH866 (fmask pH866) (cmask pH866) (hmask pH866) 1 865 (true, (init pH866), (init pH866))) 866 433 true) = true := by
  decide +kernel
theorem H866_ok : RunOK pH866 866 (runFrom pH866 (fmask pH866) (cmask pH866) (hmask pH866) 1 865 (true, (init pH866), (init pH866))) ∧ ptTest pH866 (runFrom pH866 (fmask pH866) (cmask pH866) (hmask pH866) 1 865 (true, (init pH866), (init pH866))) 866 433 true = true :=
  fin_run (runOK_init (prmOK_of_and H866_fin) true) (by decide) rfl H866_fin ptTest_fst
theorem I866_fin : (prmOK pI866 866 && intTest pI866 (runFrom pI866 (fmask pI866) (cmask pI866) (hmask pI866) 1 865 (true, (init pI866), (init pI866))) 866 17 true) = true := by
  decide +kernel
theorem I866_ok : RunOK pI866 866 (runFrom pI866 (fmask pI866) (cmask pI866) (hmask pI866) 1 865 (true, (init pI866), (init pI866))) ∧ intTest pI866 (runFrom pI866 (fmask pI866) (cmask pI866) (hmask pI866) 1 865 (true, (init pI866), (init pI866))) 866 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I866_fin) true) (by decide) rfl I866_fin intTest_fst
theorem link866 : linkOK pL866 pH866 pI866 = true := by decide +kernel
theorem cvx866 : ConvexBetweenHumps 866 :=
  cvx_of L866_ok H866_ok I866_ok link866 (by decide)
theorem cenlink866 : cenLinkOK pI866 866 = true := by decide +kernel
theorem cen866 : CenterUniqueMin 866 ∧ DipHyp 866 ∧ OnePointHyps 866 :=
  cen_of L866_ok H866_ok I866_ok link866 cenlink866

/-! ### `N = 867` -/

def pL867 : Prm := ⟨75, 35, 37, 869, 11, 18446744073709551616, 193298316995400099, 193298316995400099⟩
def pH867 : Prm := ⟨75, 35, 37, 869, 11, 18446744073709551616, 193300516018655651, 193300516018655651⟩
def pI867 : Prm := ⟨63, 31, 29, 869, 11, 18446744073709551616, 193298316995400099, 193300516018655651⟩
theorem L867_fin : (prmOK pL867 867 && ptTest pL867 (runFrom pL867 (fmask pL867) (cmask pL867) (hmask pL867) 1 866 (true, (init pL867), (init pL867))) 867 434 false) = true := by
  decide +kernel
theorem L867_ok : RunOK pL867 867 (runFrom pL867 (fmask pL867) (cmask pL867) (hmask pL867) 1 866 (true, (init pL867), (init pL867))) ∧ ptTest pL867 (runFrom pL867 (fmask pL867) (cmask pL867) (hmask pL867) 1 866 (true, (init pL867), (init pL867))) 867 434 false = true :=
  fin_run (runOK_init (prmOK_of_and L867_fin) true) (by decide) rfl L867_fin ptTest_fst
theorem H867_fin : (prmOK pH867 867 && ptTest pH867 (runFrom pH867 (fmask pH867) (cmask pH867) (hmask pH867) 1 866 (true, (init pH867), (init pH867))) 867 434 true) = true := by
  decide +kernel
theorem H867_ok : RunOK pH867 867 (runFrom pH867 (fmask pH867) (cmask pH867) (hmask pH867) 1 866 (true, (init pH867), (init pH867))) ∧ ptTest pH867 (runFrom pH867 (fmask pH867) (cmask pH867) (hmask pH867) 1 866 (true, (init pH867), (init pH867))) 867 434 true = true :=
  fin_run (runOK_init (prmOK_of_and H867_fin) true) (by decide) rfl H867_fin ptTest_fst
theorem I867_fin : (prmOK pI867 867 && intTest pI867 (runFrom pI867 (fmask pI867) (cmask pI867) (hmask pI867) 1 866 (true, (init pI867), (init pI867))) 867 17 false) = true := by
  decide +kernel
theorem I867_ok : RunOK pI867 867 (runFrom pI867 (fmask pI867) (cmask pI867) (hmask pI867) 1 866 (true, (init pI867), (init pI867))) ∧ intTest pI867 (runFrom pI867 (fmask pI867) (cmask pI867) (hmask pI867) 1 866 (true, (init pI867), (init pI867))) 867 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I867_fin) true) (by decide) rfl I867_fin intTest_fst
theorem link867 : linkOK pL867 pH867 pI867 = true := by decide +kernel
theorem cvx867 : ConvexBetweenHumps 867 :=
  cvx_of L867_ok H867_ok I867_ok link867 (by decide)

/-! ### The range -/

theorem cvx_806_867 {N : ℕ} (h1 : 806 ≤ N) (h2 : N ≤ 867) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 836
  · by_cases h4 : N ≤ 820
    · by_cases h6 : N ≤ 812
      · by_cases h8 : N ≤ 808
        · by_cases h10 : N ≤ 806
          · obtain rfl : N = 806 := by omega
            exact cvx806
          · by_cases h12 : N ≤ 807
            · obtain rfl : N = 807 := by omega
              exact cvx807
            · obtain rfl : N = 808 := by omega
              exact cvx808
        · by_cases h10 : N ≤ 810
          · by_cases h12 : N ≤ 809
            · obtain rfl : N = 809 := by omega
              exact cvx809
            · obtain rfl : N = 810 := by omega
              exact cvx810
          · by_cases h12 : N ≤ 811
            · obtain rfl : N = 811 := by omega
              exact cvx811
            · obtain rfl : N = 812 := by omega
              exact cvx812
      · by_cases h8 : N ≤ 816
        · by_cases h10 : N ≤ 814
          · by_cases h12 : N ≤ 813
            · obtain rfl : N = 813 := by omega
              exact cvx813
            · obtain rfl : N = 814 := by omega
              exact cvx814
          · by_cases h12 : N ≤ 815
            · obtain rfl : N = 815 := by omega
              exact cvx815
            · obtain rfl : N = 816 := by omega
              exact cvx816
        · by_cases h10 : N ≤ 818
          · by_cases h12 : N ≤ 817
            · obtain rfl : N = 817 := by omega
              exact cvx817
            · obtain rfl : N = 818 := by omega
              exact cvx818
          · by_cases h12 : N ≤ 819
            · obtain rfl : N = 819 := by omega
              exact cvx819
            · obtain rfl : N = 820 := by omega
              exact cvx820
    · by_cases h6 : N ≤ 828
      · by_cases h8 : N ≤ 824
        · by_cases h10 : N ≤ 822
          · by_cases h12 : N ≤ 821
            · obtain rfl : N = 821 := by omega
              exact cvx821
            · obtain rfl : N = 822 := by omega
              exact cvx822
          · by_cases h12 : N ≤ 823
            · obtain rfl : N = 823 := by omega
              exact cvx823
            · obtain rfl : N = 824 := by omega
              exact cvx824
        · by_cases h10 : N ≤ 826
          · by_cases h12 : N ≤ 825
            · obtain rfl : N = 825 := by omega
              exact cvx825
            · obtain rfl : N = 826 := by omega
              exact cvx826
          · by_cases h12 : N ≤ 827
            · obtain rfl : N = 827 := by omega
              exact cvx827
            · obtain rfl : N = 828 := by omega
              exact cvx828
      · by_cases h8 : N ≤ 832
        · by_cases h10 : N ≤ 830
          · by_cases h12 : N ≤ 829
            · obtain rfl : N = 829 := by omega
              exact cvx829
            · obtain rfl : N = 830 := by omega
              exact cvx830
          · by_cases h12 : N ≤ 831
            · obtain rfl : N = 831 := by omega
              exact cvx831
            · obtain rfl : N = 832 := by omega
              exact cvx832
        · by_cases h10 : N ≤ 834
          · by_cases h12 : N ≤ 833
            · obtain rfl : N = 833 := by omega
              exact cvx833
            · obtain rfl : N = 834 := by omega
              exact cvx834
          · by_cases h12 : N ≤ 835
            · obtain rfl : N = 835 := by omega
              exact cvx835
            · obtain rfl : N = 836 := by omega
              exact cvx836
  · by_cases h4 : N ≤ 851
    · by_cases h6 : N ≤ 843
      · by_cases h8 : N ≤ 839
        · by_cases h10 : N ≤ 837
          · obtain rfl : N = 837 := by omega
            exact cvx837
          · by_cases h12 : N ≤ 838
            · obtain rfl : N = 838 := by omega
              exact cvx838
            · obtain rfl : N = 839 := by omega
              exact cvx839
        · by_cases h10 : N ≤ 841
          · by_cases h12 : N ≤ 840
            · obtain rfl : N = 840 := by omega
              exact cvx840
            · obtain rfl : N = 841 := by omega
              exact cvx841
          · by_cases h12 : N ≤ 842
            · obtain rfl : N = 842 := by omega
              exact cvx842
            · obtain rfl : N = 843 := by omega
              exact cvx843
      · by_cases h8 : N ≤ 847
        · by_cases h10 : N ≤ 845
          · by_cases h12 : N ≤ 844
            · obtain rfl : N = 844 := by omega
              exact cvx844
            · obtain rfl : N = 845 := by omega
              exact cvx845
          · by_cases h12 : N ≤ 846
            · obtain rfl : N = 846 := by omega
              exact cvx846
            · obtain rfl : N = 847 := by omega
              exact cvx847
        · by_cases h10 : N ≤ 849
          · by_cases h12 : N ≤ 848
            · obtain rfl : N = 848 := by omega
              exact cvx848
            · obtain rfl : N = 849 := by omega
              exact cvx849
          · by_cases h12 : N ≤ 850
            · obtain rfl : N = 850 := by omega
              exact cvx850
            · obtain rfl : N = 851 := by omega
              exact cvx851
    · by_cases h6 : N ≤ 859
      · by_cases h8 : N ≤ 855
        · by_cases h10 : N ≤ 853
          · by_cases h12 : N ≤ 852
            · obtain rfl : N = 852 := by omega
              exact cvx852
            · obtain rfl : N = 853 := by omega
              exact cvx853
          · by_cases h12 : N ≤ 854
            · obtain rfl : N = 854 := by omega
              exact cvx854
            · obtain rfl : N = 855 := by omega
              exact cvx855
        · by_cases h10 : N ≤ 857
          · by_cases h12 : N ≤ 856
            · obtain rfl : N = 856 := by omega
              exact cvx856
            · obtain rfl : N = 857 := by omega
              exact cvx857
          · by_cases h12 : N ≤ 858
            · obtain rfl : N = 858 := by omega
              exact cvx858
            · obtain rfl : N = 859 := by omega
              exact cvx859
      · by_cases h8 : N ≤ 863
        · by_cases h10 : N ≤ 861
          · by_cases h12 : N ≤ 860
            · obtain rfl : N = 860 := by omega
              exact cvx860
            · obtain rfl : N = 861 := by omega
              exact cvx861
          · by_cases h12 : N ≤ 862
            · obtain rfl : N = 862 := by omega
              exact cvx862
            · obtain rfl : N = 863 := by omega
              exact cvx863
        · by_cases h10 : N ≤ 865
          · by_cases h12 : N ≤ 864
            · obtain rfl : N = 864 := by omega
              exact cvx864
            · obtain rfl : N = 865 := by omega
              exact cvx865
          · by_cases h12 : N ≤ 866
            · obtain rfl : N = 866 := by omega
              exact cvx866
            · obtain rfl : N = 867 := by omega
              exact cvx867

theorem cen_806_867 {N : ℕ} (h1 : 806 ≤ N) (h2 : N ≤ 867) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 834
  · by_cases h4 : N ≤ 818
    · by_cases h6 : N ≤ 810
      · by_cases h8 : N ≤ 806
        · obtain rfl : N = 806 := by omega
          exact cen806
        · by_cases h10 : N ≤ 808
          · obtain rfl : N = 808 := by omega
            exact cen808
          · obtain rfl : N = 810 := by omega
            exact cen810
      · by_cases h8 : N ≤ 814
        · by_cases h10 : N ≤ 812
          · obtain rfl : N = 812 := by omega
            exact cen812
          · obtain rfl : N = 814 := by omega
            exact cen814
        · by_cases h10 : N ≤ 816
          · obtain rfl : N = 816 := by omega
            exact cen816
          · obtain rfl : N = 818 := by omega
            exact cen818
    · by_cases h6 : N ≤ 826
      · by_cases h8 : N ≤ 822
        · by_cases h10 : N ≤ 820
          · obtain rfl : N = 820 := by omega
            exact cen820
          · obtain rfl : N = 822 := by omega
            exact cen822
        · by_cases h10 : N ≤ 824
          · obtain rfl : N = 824 := by omega
            exact cen824
          · obtain rfl : N = 826 := by omega
            exact cen826
      · by_cases h8 : N ≤ 830
        · by_cases h10 : N ≤ 828
          · obtain rfl : N = 828 := by omega
            exact cen828
          · obtain rfl : N = 830 := by omega
            exact cen830
        · by_cases h10 : N ≤ 832
          · obtain rfl : N = 832 := by omega
            exact cen832
          · obtain rfl : N = 834 := by omega
            exact cen834
  · by_cases h4 : N ≤ 850
    · by_cases h6 : N ≤ 842
      · by_cases h8 : N ≤ 838
        · by_cases h10 : N ≤ 836
          · obtain rfl : N = 836 := by omega
            exact cen836
          · obtain rfl : N = 838 := by omega
            exact cen838
        · by_cases h10 : N ≤ 840
          · obtain rfl : N = 840 := by omega
            exact cen840
          · obtain rfl : N = 842 := by omega
            exact cen842
      · by_cases h8 : N ≤ 846
        · by_cases h10 : N ≤ 844
          · obtain rfl : N = 844 := by omega
            exact cen844
          · obtain rfl : N = 846 := by omega
            exact cen846
        · by_cases h10 : N ≤ 848
          · obtain rfl : N = 848 := by omega
            exact cen848
          · obtain rfl : N = 850 := by omega
            exact cen850
    · by_cases h6 : N ≤ 858
      · by_cases h8 : N ≤ 854
        · by_cases h10 : N ≤ 852
          · obtain rfl : N = 852 := by omega
            exact cen852
          · obtain rfl : N = 854 := by omega
            exact cen854
        · by_cases h10 : N ≤ 856
          · obtain rfl : N = 856 := by omega
            exact cen856
          · obtain rfl : N = 858 := by omega
            exact cen858
      · by_cases h8 : N ≤ 862
        · by_cases h10 : N ≤ 860
          · obtain rfl : N = 860 := by omega
            exact cen860
          · obtain rfl : N = 862 := by omega
            exact cen862
        · by_cases h10 : N ≤ 864
          · obtain rfl : N = 864 := by omega
            exact cen864
          · obtain rfl : N = 866 := by omega
            exact cen866

end Kagey131.PaperD.T7
