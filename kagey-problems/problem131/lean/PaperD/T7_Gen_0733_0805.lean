import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 733, …, 805` (generated)

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

/-! ### `N = 733` -/

def pL733 : Prm := ⟨73, 35, 35, 735, 11, 18446744073709551616, 220668431023004335, 220668431023004335⟩
def pH733 : Prm := ⟨74, 36, 35, 735, 11, 18446744073709551616, 220672829069515439, 220672829069515439⟩
def pI733 : Prm := ⟨62, 31, 28, 735, 11, 18446744073709551616, 220668431023004335, 220672829069515439⟩
theorem L733_fin : (prmOK pL733 733 && ptTest pL733 (runFrom pL733 (fmask pL733) (cmask pL733) (hmask pL733) 1 732 (true, (init pL733), (init pL733))) 733 367 false) = true := by
  decide +kernel
theorem L733_ok : RunOK pL733 733 (runFrom pL733 (fmask pL733) (cmask pL733) (hmask pL733) 1 732 (true, (init pL733), (init pL733))) ∧ ptTest pL733 (runFrom pL733 (fmask pL733) (cmask pL733) (hmask pL733) 1 732 (true, (init pL733), (init pL733))) 733 367 false = true :=
  fin_run (runOK_init (prmOK_of_and L733_fin) true) (by decide) rfl L733_fin ptTest_fst
theorem H733_fin : (prmOK pH733 733 && ptTest pH733 (runFrom pH733 (fmask pH733) (cmask pH733) (hmask pH733) 1 732 (true, (init pH733), (init pH733))) 733 367 true) = true := by
  decide +kernel
theorem H733_ok : RunOK pH733 733 (runFrom pH733 (fmask pH733) (cmask pH733) (hmask pH733) 1 732 (true, (init pH733), (init pH733))) ∧ ptTest pH733 (runFrom pH733 (fmask pH733) (cmask pH733) (hmask pH733) 1 732 (true, (init pH733), (init pH733))) 733 367 true = true :=
  fin_run (runOK_init (prmOK_of_and H733_fin) true) (by decide) rfl H733_fin ptTest_fst
theorem I733_fin : (prmOK pI733 733 && intTest pI733 (runFrom pI733 (fmask pI733) (cmask pI733) (hmask pI733) 1 732 (true, (init pI733), (init pI733))) 733 16 false) = true := by
  decide +kernel
theorem I733_ok : RunOK pI733 733 (runFrom pI733 (fmask pI733) (cmask pI733) (hmask pI733) 1 732 (true, (init pI733), (init pI733))) ∧ intTest pI733 (runFrom pI733 (fmask pI733) (cmask pI733) (hmask pI733) 1 732 (true, (init pI733), (init pI733))) 733 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I733_fin) true) (by decide) rfl I733_fin intTest_fst
theorem link733 : linkOK pL733 pH733 pI733 = true := by decide +kernel
theorem cvx733 : ConvexBetweenHumps 733 :=
  cvx_of L733_ok H733_ok I733_ok link733 (by decide)

/-! ### `N = 734` -/

def pL734 : Prm := ⟨74, 36, 35, 736, 11, 18446744073709551616, 220432520769390248, 220432520769390248⟩
def pH734 : Prm := ⟨74, 36, 35, 736, 11, 18446744073709551616, 220436918815901352, 220436918815901352⟩
def pI734 : Prm := ⟨62, 31, 28, 736, 11, 18446744073709551616, 220432520769390248, 220436918815901352⟩
theorem L734_fin : (prmOK pL734 734 && ptTest pL734 (runFrom pL734 (fmask pL734) (cmask pL734) (hmask pL734) 1 733 (true, (init pL734), (init pL734))) 734 367 false) = true := by
  decide +kernel
theorem L734_ok : RunOK pL734 734 (runFrom pL734 (fmask pL734) (cmask pL734) (hmask pL734) 1 733 (true, (init pL734), (init pL734))) ∧ ptTest pL734 (runFrom pL734 (fmask pL734) (cmask pL734) (hmask pL734) 1 733 (true, (init pL734), (init pL734))) 734 367 false = true :=
  fin_run (runOK_init (prmOK_of_and L734_fin) true) (by decide) rfl L734_fin ptTest_fst
theorem H734_fin : (prmOK pH734 734 && ptTest pH734 (runFrom pH734 (fmask pH734) (cmask pH734) (hmask pH734) 1 733 (true, (init pH734), (init pH734))) 734 367 true) = true := by
  decide +kernel
theorem H734_ok : RunOK pH734 734 (runFrom pH734 (fmask pH734) (cmask pH734) (hmask pH734) 1 733 (true, (init pH734), (init pH734))) ∧ ptTest pH734 (runFrom pH734 (fmask pH734) (cmask pH734) (hmask pH734) 1 733 (true, (init pH734), (init pH734))) 734 367 true = true :=
  fin_run (runOK_init (prmOK_of_and H734_fin) true) (by decide) rfl H734_fin ptTest_fst
theorem I734_fin : (prmOK pI734 734 && intTest pI734 (runFrom pI734 (fmask pI734) (cmask pI734) (hmask pI734) 1 733 (true, (init pI734), (init pI734))) 734 16 true) = true := by
  decide +kernel
theorem I734_ok : RunOK pI734 734 (runFrom pI734 (fmask pI734) (cmask pI734) (hmask pI734) 1 733 (true, (init pI734), (init pI734))) ∧ intTest pI734 (runFrom pI734 (fmask pI734) (cmask pI734) (hmask pI734) 1 733 (true, (init pI734), (init pI734))) 734 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I734_fin) true) (by decide) rfl I734_fin intTest_fst
theorem link734 : linkOK pL734 pH734 pI734 = true := by decide +kernel
theorem cvx734 : ConvexBetweenHumps 734 :=
  cvx_of L734_ok H734_ok I734_ok link734 (by decide)
theorem cenlink734 : cenLinkOK pI734 734 = true := by decide +kernel
theorem cen734 : CenterUniqueMin 734 ∧ DipHyp 734 ∧ OnePointHyps 734 :=
  cen_of L734_ok H734_ok I734_ok link734 cenlink734

/-! ### `N = 735` -/

def pL735 : Prm := ⟨73, 35, 35, 737, 11, 18446744073709551616, 220196868058886741, 220196868058886741⟩
def pH735 : Prm := ⟨74, 36, 35, 737, 11, 18446744073709551616, 220201266105397845, 220201266105397845⟩
def pI735 : Prm := ⟨62, 31, 28, 737, 11, 18446744073709551616, 220196868058886741, 220201266105397845⟩
theorem L735_fin : (prmOK pL735 735 && ptTest pL735 (runFrom pL735 (fmask pL735) (cmask pL735) (hmask pL735) 1 734 (true, (init pL735), (init pL735))) 735 368 false) = true := by
  decide +kernel
theorem L735_ok : RunOK pL735 735 (runFrom pL735 (fmask pL735) (cmask pL735) (hmask pL735) 1 734 (true, (init pL735), (init pL735))) ∧ ptTest pL735 (runFrom pL735 (fmask pL735) (cmask pL735) (hmask pL735) 1 734 (true, (init pL735), (init pL735))) 735 368 false = true :=
  fin_run (runOK_init (prmOK_of_and L735_fin) true) (by decide) rfl L735_fin ptTest_fst
theorem H735_fin : (prmOK pH735 735 && ptTest pH735 (runFrom pH735 (fmask pH735) (cmask pH735) (hmask pH735) 1 734 (true, (init pH735), (init pH735))) 735 368 true) = true := by
  decide +kernel
theorem H735_ok : RunOK pH735 735 (runFrom pH735 (fmask pH735) (cmask pH735) (hmask pH735) 1 734 (true, (init pH735), (init pH735))) ∧ ptTest pH735 (runFrom pH735 (fmask pH735) (cmask pH735) (hmask pH735) 1 734 (true, (init pH735), (init pH735))) 735 368 true = true :=
  fin_run (runOK_init (prmOK_of_and H735_fin) true) (by decide) rfl H735_fin ptTest_fst
theorem I735_fin : (prmOK pI735 735 && intTest pI735 (runFrom pI735 (fmask pI735) (cmask pI735) (hmask pI735) 1 734 (true, (init pI735), (init pI735))) 735 16 false) = true := by
  decide +kernel
theorem I735_ok : RunOK pI735 735 (runFrom pI735 (fmask pI735) (cmask pI735) (hmask pI735) 1 734 (true, (init pI735), (init pI735))) ∧ intTest pI735 (runFrom pI735 (fmask pI735) (cmask pI735) (hmask pI735) 1 734 (true, (init pI735), (init pI735))) 735 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I735_fin) true) (by decide) rfl I735_fin intTest_fst
theorem link735 : linkOK pL735 pH735 pI735 = true := by decide +kernel
theorem cvx735 : ConvexBetweenHumps 735 :=
  cvx_of L735_ok H735_ok I735_ok link735 (by decide)

/-! ### `N = 736` -/

def pL736 : Prm := ⟨74, 36, 35, 738, 11, 18446744073709551616, 219962064191378900, 219962064191378900⟩
def pH736 : Prm := ⟨74, 36, 35, 738, 11, 18446744073709551616, 219966462237890004, 219966462237890004⟩
def pI736 : Prm := ⟨63, 31, 29, 738, 11, 18446744073709551616, 219962064191378900, 219966462237890004⟩
theorem L736_fin : (prmOK pL736 736 && ptTest pL736 (runFrom pL736 (fmask pL736) (cmask pL736) (hmask pL736) 1 735 (true, (init pL736), (init pL736))) 736 368 false) = true := by
  decide +kernel
theorem L736_ok : RunOK pL736 736 (runFrom pL736 (fmask pL736) (cmask pL736) (hmask pL736) 1 735 (true, (init pL736), (init pL736))) ∧ ptTest pL736 (runFrom pL736 (fmask pL736) (cmask pL736) (hmask pL736) 1 735 (true, (init pL736), (init pL736))) 736 368 false = true :=
  fin_run (runOK_init (prmOK_of_and L736_fin) true) (by decide) rfl L736_fin ptTest_fst
theorem H736_fin : (prmOK pH736 736 && ptTest pH736 (runFrom pH736 (fmask pH736) (cmask pH736) (hmask pH736) 1 735 (true, (init pH736), (init pH736))) 736 368 true) = true := by
  decide +kernel
theorem H736_ok : RunOK pH736 736 (runFrom pH736 (fmask pH736) (cmask pH736) (hmask pH736) 1 735 (true, (init pH736), (init pH736))) ∧ ptTest pH736 (runFrom pH736 (fmask pH736) (cmask pH736) (hmask pH736) 1 735 (true, (init pH736), (init pH736))) 736 368 true = true :=
  fin_run (runOK_init (prmOK_of_and H736_fin) true) (by decide) rfl H736_fin ptTest_fst
theorem I736_fin : (prmOK pI736 736 && intTest pI736 (runFrom pI736 (fmask pI736) (cmask pI736) (hmask pI736) 1 735 (true, (init pI736), (init pI736))) 736 16 true) = true := by
  decide +kernel
theorem I736_ok : RunOK pI736 736 (runFrom pI736 (fmask pI736) (cmask pI736) (hmask pI736) 1 735 (true, (init pI736), (init pI736))) ∧ intTest pI736 (runFrom pI736 (fmask pI736) (cmask pI736) (hmask pI736) 1 735 (true, (init pI736), (init pI736))) 736 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I736_fin) true) (by decide) rfl I736_fin intTest_fst
theorem link736 : linkOK pL736 pH736 pI736 = true := by decide +kernel
theorem cvx736 : ConvexBetweenHumps 736 :=
  cvx_of L736_ok H736_ok I736_ok link736 (by decide)
theorem cenlink736 : cenLinkOK pI736 736 = true := by decide +kernel
theorem cen736 : CenterUniqueMin 736 ∧ DipHyp 736 ∧ OnePointHyps 736 :=
  cen_of L736_ok H736_ok I736_ok link736 cenlink736

/-! ### `N = 737` -/

def pL737 : Prm := ⟨74, 36, 35, 739, 11, 18446744073709551616, 219727516286243246, 219727516286243246⟩
def pH737 : Prm := ⟨74, 36, 35, 739, 11, 18446744073709551616, 219731914332754350, 219731914332754350⟩
def pI737 : Prm := ⟨63, 31, 29, 739, 11, 18446744073709551616, 219727516286243246, 219731914332754350⟩
theorem L737_fin : (prmOK pL737 737 && ptTest pL737 (runFrom pL737 (fmask pL737) (cmask pL737) (hmask pL737) 1 736 (true, (init pL737), (init pL737))) 737 369 false) = true := by
  decide +kernel
theorem L737_ok : RunOK pL737 737 (runFrom pL737 (fmask pL737) (cmask pL737) (hmask pL737) 1 736 (true, (init pL737), (init pL737))) ∧ ptTest pL737 (runFrom pL737 (fmask pL737) (cmask pL737) (hmask pL737) 1 736 (true, (init pL737), (init pL737))) 737 369 false = true :=
  fin_run (runOK_init (prmOK_of_and L737_fin) true) (by decide) rfl L737_fin ptTest_fst
theorem H737_fin : (prmOK pH737 737 && ptTest pH737 (runFrom pH737 (fmask pH737) (cmask pH737) (hmask pH737) 1 736 (true, (init pH737), (init pH737))) 737 369 true) = true := by
  decide +kernel
theorem H737_ok : RunOK pH737 737 (runFrom pH737 (fmask pH737) (cmask pH737) (hmask pH737) 1 736 (true, (init pH737), (init pH737))) ∧ ptTest pH737 (runFrom pH737 (fmask pH737) (cmask pH737) (hmask pH737) 1 736 (true, (init pH737), (init pH737))) 737 369 true = true :=
  fin_run (runOK_init (prmOK_of_and H737_fin) true) (by decide) rfl H737_fin ptTest_fst
theorem I737_fin : (prmOK pI737 737 && intTest pI737 (runFrom pI737 (fmask pI737) (cmask pI737) (hmask pI737) 1 736 (true, (init pI737), (init pI737))) 737 16 false) = true := by
  decide +kernel
theorem I737_ok : RunOK pI737 737 (runFrom pI737 (fmask pI737) (cmask pI737) (hmask pI737) 1 736 (true, (init pI737), (init pI737))) ∧ intTest pI737 (runFrom pI737 (fmask pI737) (cmask pI737) (hmask pI737) 1 736 (true, (init pI737), (init pI737))) 737 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I737_fin) true) (by decide) rfl I737_fin intTest_fst
theorem link737 : linkOK pL737 pH737 pI737 = true := by decide +kernel
theorem cvx737 : ConvexBetweenHumps 737 :=
  cvx_of L737_ok H737_ok I737_ok link737 (by decide)

/-! ### `N = 738` -/

def pL738 : Prm := ⟨74, 36, 35, 740, 11, 18446744073709551616, 219493810755623321, 219493810755623321⟩
def pH738 : Prm := ⟨74, 36, 35, 740, 11, 18446744073709551616, 219498208802134425, 219498208802134425⟩
def pI738 : Prm := ⟨63, 31, 29, 740, 11, 18446744073709551616, 219493810755623321, 219498208802134425⟩
theorem L738_fin : (prmOK pL738 738 && ptTest pL738 (runFrom pL738 (fmask pL738) (cmask pL738) (hmask pL738) 1 737 (true, (init pL738), (init pL738))) 738 369 false) = true := by
  decide +kernel
theorem L738_ok : RunOK pL738 738 (runFrom pL738 (fmask pL738) (cmask pL738) (hmask pL738) 1 737 (true, (init pL738), (init pL738))) ∧ ptTest pL738 (runFrom pL738 (fmask pL738) (cmask pL738) (hmask pL738) 1 737 (true, (init pL738), (init pL738))) 738 369 false = true :=
  fin_run (runOK_init (prmOK_of_and L738_fin) true) (by decide) rfl L738_fin ptTest_fst
theorem H738_fin : (prmOK pH738 738 && ptTest pH738 (runFrom pH738 (fmask pH738) (cmask pH738) (hmask pH738) 1 737 (true, (init pH738), (init pH738))) 738 369 true) = true := by
  decide +kernel
theorem H738_ok : RunOK pH738 738 (runFrom pH738 (fmask pH738) (cmask pH738) (hmask pH738) 1 737 (true, (init pH738), (init pH738))) ∧ ptTest pH738 (runFrom pH738 (fmask pH738) (cmask pH738) (hmask pH738) 1 737 (true, (init pH738), (init pH738))) 738 369 true = true :=
  fin_run (runOK_init (prmOK_of_and H738_fin) true) (by decide) rfl H738_fin ptTest_fst
theorem I738_fin : (prmOK pI738 738 && intTest pI738 (runFrom pI738 (fmask pI738) (cmask pI738) (hmask pI738) 1 737 (true, (init pI738), (init pI738))) 738 16 true) = true := by
  decide +kernel
theorem I738_ok : RunOK pI738 738 (runFrom pI738 (fmask pI738) (cmask pI738) (hmask pI738) 1 737 (true, (init pI738), (init pI738))) ∧ intTest pI738 (runFrom pI738 (fmask pI738) (cmask pI738) (hmask pI738) 1 737 (true, (init pI738), (init pI738))) 738 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I738_fin) true) (by decide) rfl I738_fin intTest_fst
theorem link738 : linkOK pL738 pH738 pI738 = true := by decide +kernel
theorem cvx738 : ConvexBetweenHumps 738 :=
  cvx_of L738_ok H738_ok I738_ok link738 (by decide)
theorem cenlink738 : cenLinkOK pI738 738 = true := by decide +kernel
theorem cen738 : CenterUniqueMin 738 ∧ DipHyp 738 ∧ OnePointHyps 738 :=
  cen_of L738_ok H738_ok I738_ok link738 cenlink738

/-! ### `N = 739` -/

def pL739 : Prm := ⟨74, 36, 35, 741, 11, 18446744073709551616, 219260359619623698, 219260359619623698⟩
def pH739 : Prm := ⟨74, 36, 35, 741, 11, 18446744073709551616, 219264757666134802, 219264757666134802⟩
def pI739 : Prm := ⟨63, 31, 29, 741, 11, 18446744073709551616, 219260359619623698, 219264757666134802⟩
theorem L739_fin : (prmOK pL739 739 && ptTest pL739 (runFrom pL739 (fmask pL739) (cmask pL739) (hmask pL739) 1 738 (true, (init pL739), (init pL739))) 739 370 false) = true := by
  decide +kernel
theorem L739_ok : RunOK pL739 739 (runFrom pL739 (fmask pL739) (cmask pL739) (hmask pL739) 1 738 (true, (init pL739), (init pL739))) ∧ ptTest pL739 (runFrom pL739 (fmask pL739) (cmask pL739) (hmask pL739) 1 738 (true, (init pL739), (init pL739))) 739 370 false = true :=
  fin_run (runOK_init (prmOK_of_and L739_fin) true) (by decide) rfl L739_fin ptTest_fst
theorem H739_fin : (prmOK pH739 739 && ptTest pH739 (runFrom pH739 (fmask pH739) (cmask pH739) (hmask pH739) 1 738 (true, (init pH739), (init pH739))) 739 370 true) = true := by
  decide +kernel
theorem H739_ok : RunOK pH739 739 (runFrom pH739 (fmask pH739) (cmask pH739) (hmask pH739) 1 738 (true, (init pH739), (init pH739))) ∧ ptTest pH739 (runFrom pH739 (fmask pH739) (cmask pH739) (hmask pH739) 1 738 (true, (init pH739), (init pH739))) 739 370 true = true :=
  fin_run (runOK_init (prmOK_of_and H739_fin) true) (by decide) rfl H739_fin ptTest_fst
theorem I739_fin : (prmOK pI739 739 && intTest pI739 (runFrom pI739 (fmask pI739) (cmask pI739) (hmask pI739) 1 738 (true, (init pI739), (init pI739))) 739 16 false) = true := by
  decide +kernel
theorem I739_ok : RunOK pI739 739 (runFrom pI739 (fmask pI739) (cmask pI739) (hmask pI739) 1 738 (true, (init pI739), (init pI739))) ∧ intTest pI739 (runFrom pI739 (fmask pI739) (cmask pI739) (hmask pI739) 1 738 (true, (init pI739), (init pI739))) 739 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I739_fin) true) (by decide) rfl I739_fin intTest_fst
theorem link739 : linkOK pL739 pH739 pI739 = true := by decide +kernel
theorem cvx739 : ConvexBetweenHumps 739 :=
  cvx_of L739_ok H739_ok I739_ok link739 (by decide)

/-! ### `N = 740` -/

def pL740 : Prm := ⟨74, 36, 35, 742, 11, 18446744073709551616, 219027744456086593, 219027744456086593⟩
def pH740 : Prm := ⟨74, 36, 35, 742, 11, 18446744073709551616, 219032142502597697, 219032142502597697⟩
def pI740 : Prm := ⟨63, 31, 29, 742, 11, 18446744073709551616, 219027744456086593, 219032142502597697⟩
theorem L740_fin : (prmOK pL740 740 && ptTest pL740 (runFrom pL740 (fmask pL740) (cmask pL740) (hmask pL740) 1 739 (true, (init pL740), (init pL740))) 740 370 false) = true := by
  decide +kernel
theorem L740_ok : RunOK pL740 740 (runFrom pL740 (fmask pL740) (cmask pL740) (hmask pL740) 1 739 (true, (init pL740), (init pL740))) ∧ ptTest pL740 (runFrom pL740 (fmask pL740) (cmask pL740) (hmask pL740) 1 739 (true, (init pL740), (init pL740))) 740 370 false = true :=
  fin_run (runOK_init (prmOK_of_and L740_fin) true) (by decide) rfl L740_fin ptTest_fst
theorem H740_fin : (prmOK pH740 740 && ptTest pH740 (runFrom pH740 (fmask pH740) (cmask pH740) (hmask pH740) 1 739 (true, (init pH740), (init pH740))) 740 370 true) = true := by
  decide +kernel
theorem H740_ok : RunOK pH740 740 (runFrom pH740 (fmask pH740) (cmask pH740) (hmask pH740) 1 739 (true, (init pH740), (init pH740))) ∧ ptTest pH740 (runFrom pH740 (fmask pH740) (cmask pH740) (hmask pH740) 1 739 (true, (init pH740), (init pH740))) 740 370 true = true :=
  fin_run (runOK_init (prmOK_of_and H740_fin) true) (by decide) rfl H740_fin ptTest_fst
theorem I740_fin : (prmOK pI740 740 && intTest pI740 (runFrom pI740 (fmask pI740) (cmask pI740) (hmask pI740) 1 739 (true, (init pI740), (init pI740))) 740 16 true) = true := by
  decide +kernel
theorem I740_ok : RunOK pI740 740 (runFrom pI740 (fmask pI740) (cmask pI740) (hmask pI740) 1 739 (true, (init pI740), (init pI740))) ∧ intTest pI740 (runFrom pI740 (fmask pI740) (cmask pI740) (hmask pI740) 1 739 (true, (init pI740), (init pI740))) 740 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I740_fin) true) (by decide) rfl I740_fin intTest_fst
theorem link740 : linkOK pL740 pH740 pI740 = true := by decide +kernel
theorem cvx740 : ConvexBetweenHumps 740 :=
  cvx_of L740_ok H740_ok I740_ok link740 (by decide)
theorem cenlink740 : cenLinkOK pI740 740 = true := by decide +kernel
theorem cen740 : CenterUniqueMin 740 ∧ DipHyp 740 ∧ OnePointHyps 740 :=
  cen_of L740_ok H740_ok I740_ok link740 cenlink740

/-! ### `N = 741` -/

def pL741 : Prm := ⟨74, 36, 35, 743, 11, 18446744073709551616, 218795382132293732, 218795382132293732⟩
def pH741 : Prm := ⟨73, 35, 35, 743, 11, 18446744073709551616, 218799780178804836, 218799780178804836⟩
def pI741 : Prm := ⟨63, 31, 29, 743, 11, 18446744073709551616, 218795382132293732, 218799780178804836⟩
theorem L741_fin : (prmOK pL741 741 && ptTest pL741 (runFrom pL741 (fmask pL741) (cmask pL741) (hmask pL741) 1 740 (true, (init pL741), (init pL741))) 741 371 false) = true := by
  decide +kernel
theorem L741_ok : RunOK pL741 741 (runFrom pL741 (fmask pL741) (cmask pL741) (hmask pL741) 1 740 (true, (init pL741), (init pL741))) ∧ ptTest pL741 (runFrom pL741 (fmask pL741) (cmask pL741) (hmask pL741) 1 740 (true, (init pL741), (init pL741))) 741 371 false = true :=
  fin_run (runOK_init (prmOK_of_and L741_fin) true) (by decide) rfl L741_fin ptTest_fst
theorem H741_fin : (prmOK pH741 741 && ptTest pH741 (runFrom pH741 (fmask pH741) (cmask pH741) (hmask pH741) 1 740 (true, (init pH741), (init pH741))) 741 371 true) = true := by
  decide +kernel
theorem H741_ok : RunOK pH741 741 (runFrom pH741 (fmask pH741) (cmask pH741) (hmask pH741) 1 740 (true, (init pH741), (init pH741))) ∧ ptTest pH741 (runFrom pH741 (fmask pH741) (cmask pH741) (hmask pH741) 1 740 (true, (init pH741), (init pH741))) 741 371 true = true :=
  fin_run (runOK_init (prmOK_of_and H741_fin) true) (by decide) rfl H741_fin ptTest_fst
theorem I741_fin : (prmOK pI741 741 && intTest pI741 (runFrom pI741 (fmask pI741) (cmask pI741) (hmask pI741) 1 740 (true, (init pI741), (init pI741))) 741 16 false) = true := by
  decide +kernel
theorem I741_ok : RunOK pI741 741 (runFrom pI741 (fmask pI741) (cmask pI741) (hmask pI741) 1 740 (true, (init pI741), (init pI741))) ∧ intTest pI741 (runFrom pI741 (fmask pI741) (cmask pI741) (hmask pI741) 1 740 (true, (init pI741), (init pI741))) 741 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I741_fin) true) (by decide) rfl I741_fin intTest_fst
theorem link741 : linkOK pL741 pH741 pI741 = true := by decide +kernel
theorem cvx741 : ConvexBetweenHumps 741 :=
  cvx_of L741_ok H741_ok I741_ok link741 (by decide)

/-! ### `N = 742` -/

def pL742 : Prm := ⟨74, 36, 35, 744, 11, 18446744073709551616, 218563849444525247, 218563849444525247⟩
def pH742 : Prm := ⟨74, 36, 35, 744, 11, 18446744073709551616, 218568247491036351, 218568247491036351⟩
def pI742 : Prm := ⟨63, 31, 29, 744, 11, 18446744073709551616, 218563849444525247, 218568247491036351⟩
theorem L742_fin : (prmOK pL742 742 && ptTest pL742 (runFrom pL742 (fmask pL742) (cmask pL742) (hmask pL742) 1 741 (true, (init pL742), (init pL742))) 742 371 false) = true := by
  decide +kernel
theorem L742_ok : RunOK pL742 742 (runFrom pL742 (fmask pL742) (cmask pL742) (hmask pL742) 1 741 (true, (init pL742), (init pL742))) ∧ ptTest pL742 (runFrom pL742 (fmask pL742) (cmask pL742) (hmask pL742) 1 741 (true, (init pL742), (init pL742))) 742 371 false = true :=
  fin_run (runOK_init (prmOK_of_and L742_fin) true) (by decide) rfl L742_fin ptTest_fst
theorem H742_fin : (prmOK pH742 742 && ptTest pH742 (runFrom pH742 (fmask pH742) (cmask pH742) (hmask pH742) 1 741 (true, (init pH742), (init pH742))) 742 371 true) = true := by
  decide +kernel
theorem H742_ok : RunOK pH742 742 (runFrom pH742 (fmask pH742) (cmask pH742) (hmask pH742) 1 741 (true, (init pH742), (init pH742))) ∧ ptTest pH742 (runFrom pH742 (fmask pH742) (cmask pH742) (hmask pH742) 1 741 (true, (init pH742), (init pH742))) 742 371 true = true :=
  fin_run (runOK_init (prmOK_of_and H742_fin) true) (by decide) rfl H742_fin ptTest_fst
theorem I742_fin : (prmOK pI742 742 && intTest pI742 (runFrom pI742 (fmask pI742) (cmask pI742) (hmask pI742) 1 741 (true, (init pI742), (init pI742))) 742 16 true) = true := by
  decide +kernel
theorem I742_ok : RunOK pI742 742 (runFrom pI742 (fmask pI742) (cmask pI742) (hmask pI742) 1 741 (true, (init pI742), (init pI742))) ∧ intTest pI742 (runFrom pI742 (fmask pI742) (cmask pI742) (hmask pI742) 1 741 (true, (init pI742), (init pI742))) 742 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I742_fin) true) (by decide) rfl I742_fin intTest_fst
theorem link742 : linkOK pL742 pH742 pI742 = true := by decide +kernel
theorem cvx742 : ConvexBetweenHumps 742 :=
  cvx_of L742_ok H742_ok I742_ok link742 (by decide)
theorem cenlink742 : cenLinkOK pI742 742 = true := by decide +kernel
theorem cen742 : CenterUniqueMin 742 ∧ DipHyp 742 ∧ OnePointHyps 742 :=
  cen_of L742_ok H742_ok I742_ok link742 cenlink742

/-! ### `N = 743` -/

def pL743 : Prm := ⟨74, 36, 35, 745, 11, 18446744073709551616, 218332568054297861, 218332568054297861⟩
def pH743 : Prm := ⟨74, 36, 35, 745, 11, 18446744073709551616, 218336966100808965, 218336966100808965⟩
def pI743 : Prm := ⟨63, 31, 29, 745, 11, 18446744073709551616, 218332568054297861, 218336966100808965⟩
theorem L743_fin : (prmOK pL743 743 && ptTest pL743 (runFrom pL743 (fmask pL743) (cmask pL743) (hmask pL743) 1 742 (true, (init pL743), (init pL743))) 743 372 false) = true := by
  decide +kernel
theorem L743_ok : RunOK pL743 743 (runFrom pL743 (fmask pL743) (cmask pL743) (hmask pL743) 1 742 (true, (init pL743), (init pL743))) ∧ ptTest pL743 (runFrom pL743 (fmask pL743) (cmask pL743) (hmask pL743) 1 742 (true, (init pL743), (init pL743))) 743 372 false = true :=
  fin_run (runOK_init (prmOK_of_and L743_fin) true) (by decide) rfl L743_fin ptTest_fst
theorem H743_fin : (prmOK pH743 743 && ptTest pH743 (runFrom pH743 (fmask pH743) (cmask pH743) (hmask pH743) 1 742 (true, (init pH743), (init pH743))) 743 372 true) = true := by
  decide +kernel
theorem H743_ok : RunOK pH743 743 (runFrom pH743 (fmask pH743) (cmask pH743) (hmask pH743) 1 742 (true, (init pH743), (init pH743))) ∧ ptTest pH743 (runFrom pH743 (fmask pH743) (cmask pH743) (hmask pH743) 1 742 (true, (init pH743), (init pH743))) 743 372 true = true :=
  fin_run (runOK_init (prmOK_of_and H743_fin) true) (by decide) rfl H743_fin ptTest_fst
theorem I743_fin : (prmOK pI743 743 && intTest pI743 (runFrom pI743 (fmask pI743) (cmask pI743) (hmask pI743) 1 742 (true, (init pI743), (init pI743))) 743 16 false) = true := by
  decide +kernel
theorem I743_ok : RunOK pI743 743 (runFrom pI743 (fmask pI743) (cmask pI743) (hmask pI743) 1 742 (true, (init pI743), (init pI743))) ∧ intTest pI743 (runFrom pI743 (fmask pI743) (cmask pI743) (hmask pI743) 1 742 (true, (init pI743), (init pI743))) 743 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I743_fin) true) (by decide) rfl I743_fin intTest_fst
theorem link743 : linkOK pL743 pH743 pI743 = true := by decide +kernel
theorem cvx743 : ConvexBetweenHumps 743 :=
  cvx_of L743_ok H743_ok I743_ok link743 (by decide)

/-! ### `N = 744` -/

def pL744 : Prm := ⟨74, 36, 35, 746, 11, 18446744073709551616, 218102110028404778, 218102110028404778⟩
def pH744 : Prm := ⟨74, 36, 35, 746, 11, 18446744073709551616, 218106508074915882, 218106508074915882⟩
def pI744 : Prm := ⟨63, 31, 29, 746, 11, 18446744073709551616, 218102110028404778, 218106508074915882⟩
theorem L744_fin : (prmOK pL744 744 && ptTest pL744 (runFrom pL744 (fmask pL744) (cmask pL744) (hmask pL744) 1 743 (true, (init pL744), (init pL744))) 744 372 false) = true := by
  decide +kernel
theorem L744_ok : RunOK pL744 744 (runFrom pL744 (fmask pL744) (cmask pL744) (hmask pL744) 1 743 (true, (init pL744), (init pL744))) ∧ ptTest pL744 (runFrom pL744 (fmask pL744) (cmask pL744) (hmask pL744) 1 743 (true, (init pL744), (init pL744))) 744 372 false = true :=
  fin_run (runOK_init (prmOK_of_and L744_fin) true) (by decide) rfl L744_fin ptTest_fst
theorem H744_fin : (prmOK pH744 744 && ptTest pH744 (runFrom pH744 (fmask pH744) (cmask pH744) (hmask pH744) 1 743 (true, (init pH744), (init pH744))) 744 372 true) = true := by
  decide +kernel
theorem H744_ok : RunOK pH744 744 (runFrom pH744 (fmask pH744) (cmask pH744) (hmask pH744) 1 743 (true, (init pH744), (init pH744))) ∧ ptTest pH744 (runFrom pH744 (fmask pH744) (cmask pH744) (hmask pH744) 1 743 (true, (init pH744), (init pH744))) 744 372 true = true :=
  fin_run (runOK_init (prmOK_of_and H744_fin) true) (by decide) rfl H744_fin ptTest_fst
theorem I744_fin : (prmOK pI744 744 && intTest pI744 (runFrom pI744 (fmask pI744) (cmask pI744) (hmask pI744) 1 743 (true, (init pI744), (init pI744))) 744 16 true) = true := by
  decide +kernel
theorem I744_ok : RunOK pI744 744 (runFrom pI744 (fmask pI744) (cmask pI744) (hmask pI744) 1 743 (true, (init pI744), (init pI744))) ∧ intTest pI744 (runFrom pI744 (fmask pI744) (cmask pI744) (hmask pI744) 1 743 (true, (init pI744), (init pI744))) 744 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I744_fin) true) (by decide) rfl I744_fin intTest_fst
theorem link744 : linkOK pL744 pH744 pI744 = true := by decide +kernel
theorem cvx744 : ConvexBetweenHumps 744 :=
  cvx_of L744_ok H744_ok I744_ok link744 (by decide)
theorem cenlink744 : cenLinkOK pI744 744 = true := by decide +kernel
theorem cen744 : CenterUniqueMin 744 ∧ DipHyp 744 ∧ OnePointHyps 744 :=
  cen_of L744_ok H744_ok I744_ok link744 cenlink744

/-! ### `N = 745` -/

def pL745 : Prm := ⟨74, 36, 35, 747, 11, 18446744073709551616, 217871901770485671, 217871901770485671⟩
def pH745 : Prm := ⟨74, 36, 35, 747, 11, 18446744073709551616, 217876299816996775, 217876299816996775⟩
def pI745 : Prm := ⟨63, 31, 29, 747, 11, 18446744073709551616, 217871901770485671, 217876299816996775⟩
theorem L745_fin : (prmOK pL745 745 && ptTest pL745 (runFrom pL745 (fmask pL745) (cmask pL745) (hmask pL745) 1 744 (true, (init pL745), (init pL745))) 745 373 false) = true := by
  decide +kernel
theorem L745_ok : RunOK pL745 745 (runFrom pL745 (fmask pL745) (cmask pL745) (hmask pL745) 1 744 (true, (init pL745), (init pL745))) ∧ ptTest pL745 (runFrom pL745 (fmask pL745) (cmask pL745) (hmask pL745) 1 744 (true, (init pL745), (init pL745))) 745 373 false = true :=
  fin_run (runOK_init (prmOK_of_and L745_fin) true) (by decide) rfl L745_fin ptTest_fst
theorem H745_fin : (prmOK pH745 745 && ptTest pH745 (runFrom pH745 (fmask pH745) (cmask pH745) (hmask pH745) 1 744 (true, (init pH745), (init pH745))) 745 373 true) = true := by
  decide +kernel
theorem H745_ok : RunOK pH745 745 (runFrom pH745 (fmask pH745) (cmask pH745) (hmask pH745) 1 744 (true, (init pH745), (init pH745))) ∧ ptTest pH745 (runFrom pH745 (fmask pH745) (cmask pH745) (hmask pH745) 1 744 (true, (init pH745), (init pH745))) 745 373 true = true :=
  fin_run (runOK_init (prmOK_of_and H745_fin) true) (by decide) rfl H745_fin ptTest_fst
theorem I745_fin : (prmOK pI745 745 && intTest pI745 (runFrom pI745 (fmask pI745) (cmask pI745) (hmask pI745) 1 744 (true, (init pI745), (init pI745))) 745 16 false) = true := by
  decide +kernel
theorem I745_ok : RunOK pI745 745 (runFrom pI745 (fmask pI745) (cmask pI745) (hmask pI745) 1 744 (true, (init pI745), (init pI745))) ∧ intTest pI745 (runFrom pI745 (fmask pI745) (cmask pI745) (hmask pI745) 1 744 (true, (init pI745), (init pI745))) 745 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I745_fin) true) (by decide) rfl I745_fin intTest_fst
theorem link745 : linkOK pL745 pH745 pI745 = true := by decide +kernel
theorem cvx745 : ConvexBetweenHumps 745 :=
  cvx_of L745_ok H745_ok I745_ok link745 (by decide)

/-! ### `N = 746` -/

def pL746 : Prm := ⟨74, 36, 35, 748, 11, 18446744073709551616, 217642510669073424, 217642510669073424⟩
def pH746 : Prm := ⟨74, 36, 35, 748, 11, 18446744073709551616, 217646908715584528, 217646908715584528⟩
def pI746 : Prm := ⟨63, 31, 29, 748, 11, 18446744073709551616, 217642510669073424, 217646908715584528⟩
theorem L746_fin : (prmOK pL746 746 && ptTest pL746 (runFrom pL746 (fmask pL746) (cmask pL746) (hmask pL746) 1 745 (true, (init pL746), (init pL746))) 746 373 false) = true := by
  decide +kernel
theorem L746_ok : RunOK pL746 746 (runFrom pL746 (fmask pL746) (cmask pL746) (hmask pL746) 1 745 (true, (init pL746), (init pL746))) ∧ ptTest pL746 (runFrom pL746 (fmask pL746) (cmask pL746) (hmask pL746) 1 745 (true, (init pL746), (init pL746))) 746 373 false = true :=
  fin_run (runOK_init (prmOK_of_and L746_fin) true) (by decide) rfl L746_fin ptTest_fst
theorem H746_fin : (prmOK pH746 746 && ptTest pH746 (runFrom pH746 (fmask pH746) (cmask pH746) (hmask pH746) 1 745 (true, (init pH746), (init pH746))) 746 373 true) = true := by
  decide +kernel
theorem H746_ok : RunOK pH746 746 (runFrom pH746 (fmask pH746) (cmask pH746) (hmask pH746) 1 745 (true, (init pH746), (init pH746))) ∧ ptTest pH746 (runFrom pH746 (fmask pH746) (cmask pH746) (hmask pH746) 1 745 (true, (init pH746), (init pH746))) 746 373 true = true :=
  fin_run (runOK_init (prmOK_of_and H746_fin) true) (by decide) rfl H746_fin ptTest_fst
theorem I746_fin : (prmOK pI746 746 && intTest pI746 (runFrom pI746 (fmask pI746) (cmask pI746) (hmask pI746) 1 745 (true, (init pI746), (init pI746))) 746 16 true) = true := by
  decide +kernel
theorem I746_ok : RunOK pI746 746 (runFrom pI746 (fmask pI746) (cmask pI746) (hmask pI746) 1 745 (true, (init pI746), (init pI746))) ∧ intTest pI746 (runFrom pI746 (fmask pI746) (cmask pI746) (hmask pI746) 1 745 (true, (init pI746), (init pI746))) 746 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I746_fin) true) (by decide) rfl I746_fin intTest_fst
theorem link746 : linkOK pL746 pH746 pI746 = true := by decide +kernel
theorem cvx746 : ConvexBetweenHumps 746 :=
  cvx_of L746_ok H746_ok I746_ok link746 (by decide)
theorem cenlink746 : cenLinkOK pI746 746 = true := by decide +kernel
theorem cen746 : CenterUniqueMin 746 ∧ DipHyp 746 ∧ OnePointHyps 746 :=
  cen_of L746_ok H746_ok I746_ok link746 cenlink746

/-! ### `N = 747` -/

def pL747 : Prm := ⟨74, 36, 35, 749, 11, 18446744073709551616, 217413367818538026, 217413367818538026⟩
def pH747 : Prm := ⟨74, 36, 35, 749, 11, 18446744073709551616, 217417765865049130, 217417765865049130⟩
def pI747 : Prm := ⟨63, 31, 29, 749, 11, 18446744073709551616, 217413367818538026, 217417765865049130⟩
theorem L747_fin : (prmOK pL747 747 && ptTest pL747 (runFrom pL747 (fmask pL747) (cmask pL747) (hmask pL747) 1 746 (true, (init pL747), (init pL747))) 747 374 false) = true := by
  decide +kernel
theorem L747_ok : RunOK pL747 747 (runFrom pL747 (fmask pL747) (cmask pL747) (hmask pL747) 1 746 (true, (init pL747), (init pL747))) ∧ ptTest pL747 (runFrom pL747 (fmask pL747) (cmask pL747) (hmask pL747) 1 746 (true, (init pL747), (init pL747))) 747 374 false = true :=
  fin_run (runOK_init (prmOK_of_and L747_fin) true) (by decide) rfl L747_fin ptTest_fst
theorem H747_fin : (prmOK pH747 747 && ptTest pH747 (runFrom pH747 (fmask pH747) (cmask pH747) (hmask pH747) 1 746 (true, (init pH747), (init pH747))) 747 374 true) = true := by
  decide +kernel
theorem H747_ok : RunOK pH747 747 (runFrom pH747 (fmask pH747) (cmask pH747) (hmask pH747) 1 746 (true, (init pH747), (init pH747))) ∧ ptTest pH747 (runFrom pH747 (fmask pH747) (cmask pH747) (hmask pH747) 1 746 (true, (init pH747), (init pH747))) 747 374 true = true :=
  fin_run (runOK_init (prmOK_of_and H747_fin) true) (by decide) rfl H747_fin ptTest_fst
theorem I747_fin : (prmOK pI747 747 && intTest pI747 (runFrom pI747 (fmask pI747) (cmask pI747) (hmask pI747) 1 746 (true, (init pI747), (init pI747))) 747 16 false) = true := by
  decide +kernel
theorem I747_ok : RunOK pI747 747 (runFrom pI747 (fmask pI747) (cmask pI747) (hmask pI747) 1 746 (true, (init pI747), (init pI747))) ∧ intTest pI747 (runFrom pI747 (fmask pI747) (cmask pI747) (hmask pI747) 1 746 (true, (init pI747), (init pI747))) 747 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I747_fin) true) (by decide) rfl I747_fin intTest_fst
theorem link747 : linkOK pL747 pH747 pI747 = true := by decide +kernel
theorem cvx747 : ConvexBetweenHumps 747 :=
  cvx_of L747_ok H747_ok I747_ok link747 (by decide)

/-! ### `N = 748` -/

def pL748 : Prm := ⟨72, 33, 36, 750, 11, 18446744073709551616, 217185035979825252, 217185035979825252⟩
def pH748 : Prm := ⟨74, 36, 35, 750, 11, 18446744073709551616, 217189434026336356, 217189434026336356⟩
def pI748 : Prm := ⟨63, 31, 29, 750, 11, 18446744073709551616, 217185035979825252, 217189434026336356⟩
theorem L748_fin : (prmOK pL748 748 && ptTest pL748 (runFrom pL748 (fmask pL748) (cmask pL748) (hmask pL748) 1 747 (true, (init pL748), (init pL748))) 748 374 false) = true := by
  decide +kernel
theorem L748_ok : RunOK pL748 748 (runFrom pL748 (fmask pL748) (cmask pL748) (hmask pL748) 1 747 (true, (init pL748), (init pL748))) ∧ ptTest pL748 (runFrom pL748 (fmask pL748) (cmask pL748) (hmask pL748) 1 747 (true, (init pL748), (init pL748))) 748 374 false = true :=
  fin_run (runOK_init (prmOK_of_and L748_fin) true) (by decide) rfl L748_fin ptTest_fst
theorem H748_fin : (prmOK pH748 748 && ptTest pH748 (runFrom pH748 (fmask pH748) (cmask pH748) (hmask pH748) 1 747 (true, (init pH748), (init pH748))) 748 374 true) = true := by
  decide +kernel
theorem H748_ok : RunOK pH748 748 (runFrom pH748 (fmask pH748) (cmask pH748) (hmask pH748) 1 747 (true, (init pH748), (init pH748))) ∧ ptTest pH748 (runFrom pH748 (fmask pH748) (cmask pH748) (hmask pH748) 1 747 (true, (init pH748), (init pH748))) 748 374 true = true :=
  fin_run (runOK_init (prmOK_of_and H748_fin) true) (by decide) rfl H748_fin ptTest_fst
theorem I748_fin : (prmOK pI748 748 && intTest pI748 (runFrom pI748 (fmask pI748) (cmask pI748) (hmask pI748) 1 747 (true, (init pI748), (init pI748))) 748 16 true) = true := by
  decide +kernel
theorem I748_ok : RunOK pI748 748 (runFrom pI748 (fmask pI748) (cmask pI748) (hmask pI748) 1 747 (true, (init pI748), (init pI748))) ∧ intTest pI748 (runFrom pI748 (fmask pI748) (cmask pI748) (hmask pI748) 1 747 (true, (init pI748), (init pI748))) 748 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I748_fin) true) (by decide) rfl I748_fin intTest_fst
theorem link748 : linkOK pL748 pH748 pI748 = true := by decide +kernel
theorem cvx748 : ConvexBetweenHumps 748 :=
  cvx_of L748_ok H748_ok I748_ok link748 (by decide)
theorem cenlink748 : cenLinkOK pI748 748 = true := by decide +kernel
theorem cen748 : CenterUniqueMin 748 ∧ DipHyp 748 ∧ OnePointHyps 748 :=
  cen_of L748_ok H748_ok I748_ok link748 cenlink748

/-! ### `N = 749` -/

def pL749 : Prm := ⟨74, 36, 35, 751, 11, 18446744073709551616, 216956950887177731, 216956950887177731⟩
def pH749 : Prm := ⟨74, 36, 35, 751, 11, 18446744073709551616, 216961348933688835, 216961348933688835⟩
def pI749 : Prm := ⟨63, 31, 29, 751, 11, 18446744073709551616, 216956950887177731, 216961348933688835⟩
theorem L749_fin : (prmOK pL749 749 && ptTest pL749 (runFrom pL749 (fmask pL749) (cmask pL749) (hmask pL749) 1 748 (true, (init pL749), (init pL749))) 749 375 false) = true := by
  decide +kernel
theorem L749_ok : RunOK pL749 749 (runFrom pL749 (fmask pL749) (cmask pL749) (hmask pL749) 1 748 (true, (init pL749), (init pL749))) ∧ ptTest pL749 (runFrom pL749 (fmask pL749) (cmask pL749) (hmask pL749) 1 748 (true, (init pL749), (init pL749))) 749 375 false = true :=
  fin_run (runOK_init (prmOK_of_and L749_fin) true) (by decide) rfl L749_fin ptTest_fst
theorem H749_fin : (prmOK pH749 749 && ptTest pH749 (runFrom pH749 (fmask pH749) (cmask pH749) (hmask pH749) 1 748 (true, (init pH749), (init pH749))) 749 375 true) = true := by
  decide +kernel
theorem H749_ok : RunOK pH749 749 (runFrom pH749 (fmask pH749) (cmask pH749) (hmask pH749) 1 748 (true, (init pH749), (init pH749))) ∧ ptTest pH749 (runFrom pH749 (fmask pH749) (cmask pH749) (hmask pH749) 1 748 (true, (init pH749), (init pH749))) 749 375 true = true :=
  fin_run (runOK_init (prmOK_of_and H749_fin) true) (by decide) rfl H749_fin ptTest_fst
theorem I749_fin : (prmOK pI749 749 && intTest pI749 (runFrom pI749 (fmask pI749) (cmask pI749) (hmask pI749) 1 748 (true, (init pI749), (init pI749))) 749 16 false) = true := by
  decide +kernel
theorem I749_ok : RunOK pI749 749 (runFrom pI749 (fmask pI749) (cmask pI749) (hmask pI749) 1 748 (true, (init pI749), (init pI749))) ∧ intTest pI749 (runFrom pI749 (fmask pI749) (cmask pI749) (hmask pI749) 1 748 (true, (init pI749), (init pI749))) 749 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I749_fin) true) (by decide) rfl I749_fin intTest_fst
theorem link749 : linkOK pL749 pH749 pI749 = true := by decide +kernel
theorem cvx749 : ConvexBetweenHumps 749 :=
  cvx_of L749_ok H749_ok I749_ok link749 (by decide)

/-! ### `N = 750` -/

def pL750 : Prm := ⟨74, 36, 35, 752, 11, 18446744073709551616, 216729670723963250, 216729670723963250⟩
def pH750 : Prm := ⟨74, 36, 35, 752, 11, 18446744073709551616, 216734068770474354, 216734068770474354⟩
def pI750 : Prm := ⟨63, 31, 29, 752, 11, 18446744073709551616, 216729670723963250, 216734068770474354⟩
theorem L750_fin : (prmOK pL750 750 && ptTest pL750 (runFrom pL750 (fmask pL750) (cmask pL750) (hmask pL750) 1 749 (true, (init pL750), (init pL750))) 750 375 false) = true := by
  decide +kernel
theorem L750_ok : RunOK pL750 750 (runFrom pL750 (fmask pL750) (cmask pL750) (hmask pL750) 1 749 (true, (init pL750), (init pL750))) ∧ ptTest pL750 (runFrom pL750 (fmask pL750) (cmask pL750) (hmask pL750) 1 749 (true, (init pL750), (init pL750))) 750 375 false = true :=
  fin_run (runOK_init (prmOK_of_and L750_fin) true) (by decide) rfl L750_fin ptTest_fst
theorem H750_fin : (prmOK pH750 750 && ptTest pH750 (runFrom pH750 (fmask pH750) (cmask pH750) (hmask pH750) 1 749 (true, (init pH750), (init pH750))) 750 375 true) = true := by
  decide +kernel
theorem H750_ok : RunOK pH750 750 (runFrom pH750 (fmask pH750) (cmask pH750) (hmask pH750) 1 749 (true, (init pH750), (init pH750))) ∧ ptTest pH750 (runFrom pH750 (fmask pH750) (cmask pH750) (hmask pH750) 1 749 (true, (init pH750), (init pH750))) 750 375 true = true :=
  fin_run (runOK_init (prmOK_of_and H750_fin) true) (by decide) rfl H750_fin ptTest_fst
theorem I750_fin : (prmOK pI750 750 && intTest pI750 (runFrom pI750 (fmask pI750) (cmask pI750) (hmask pI750) 1 749 (true, (init pI750), (init pI750))) 750 16 true) = true := by
  decide +kernel
theorem I750_ok : RunOK pI750 750 (runFrom pI750 (fmask pI750) (cmask pI750) (hmask pI750) 1 749 (true, (init pI750), (init pI750))) ∧ intTest pI750 (runFrom pI750 (fmask pI750) (cmask pI750) (hmask pI750) 1 749 (true, (init pI750), (init pI750))) 750 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I750_fin) true) (by decide) rfl I750_fin intTest_fst
theorem link750 : linkOK pL750 pH750 pI750 = true := by decide +kernel
theorem cvx750 : ConvexBetweenHumps 750 :=
  cvx_of L750_ok H750_ok I750_ok link750 (by decide)
theorem cenlink750 : cenLinkOK pI750 750 = true := by decide +kernel
theorem cen750 : CenterUniqueMin 750 ∧ DipHyp 750 ∧ OnePointHyps 750 :=
  cen_of L750_ok H750_ok I750_ok link750 cenlink750

/-! ### `N = 751` -/

def pL751 : Prm := ⟨74, 36, 35, 753, 11, 18446744073709551616, 216502635814232619, 216502635814232619⟩
def pH751 : Prm := ⟨74, 36, 35, 753, 11, 18446744073709551616, 216507033860743723, 216507033860743723⟩
def pI751 : Prm := ⟨63, 31, 29, 753, 11, 18446744073709551616, 216502635814232619, 216507033860743723⟩
theorem L751_fin : (prmOK pL751 751 && ptTest pL751 (runFrom pL751 (fmask pL751) (cmask pL751) (hmask pL751) 1 750 (true, (init pL751), (init pL751))) 751 376 false) = true := by
  decide +kernel
theorem L751_ok : RunOK pL751 751 (runFrom pL751 (fmask pL751) (cmask pL751) (hmask pL751) 1 750 (true, (init pL751), (init pL751))) ∧ ptTest pL751 (runFrom pL751 (fmask pL751) (cmask pL751) (hmask pL751) 1 750 (true, (init pL751), (init pL751))) 751 376 false = true :=
  fin_run (runOK_init (prmOK_of_and L751_fin) true) (by decide) rfl L751_fin ptTest_fst
theorem H751_fin : (prmOK pH751 751 && ptTest pH751 (runFrom pH751 (fmask pH751) (cmask pH751) (hmask pH751) 1 750 (true, (init pH751), (init pH751))) 751 376 true) = true := by
  decide +kernel
theorem H751_ok : RunOK pH751 751 (runFrom pH751 (fmask pH751) (cmask pH751) (hmask pH751) 1 750 (true, (init pH751), (init pH751))) ∧ ptTest pH751 (runFrom pH751 (fmask pH751) (cmask pH751) (hmask pH751) 1 750 (true, (init pH751), (init pH751))) 751 376 true = true :=
  fin_run (runOK_init (prmOK_of_and H751_fin) true) (by decide) rfl H751_fin ptTest_fst
theorem I751_fin : (prmOK pI751 751 && intTest pI751 (runFrom pI751 (fmask pI751) (cmask pI751) (hmask pI751) 1 750 (true, (init pI751), (init pI751))) 751 16 false) = true := by
  decide +kernel
theorem I751_ok : RunOK pI751 751 (runFrom pI751 (fmask pI751) (cmask pI751) (hmask pI751) 1 750 (true, (init pI751), (init pI751))) ∧ intTest pI751 (runFrom pI751 (fmask pI751) (cmask pI751) (hmask pI751) 1 750 (true, (init pI751), (init pI751))) 751 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I751_fin) true) (by decide) rfl I751_fin intTest_fst
theorem link751 : linkOK pL751 pH751 pI751 = true := by decide +kernel
theorem cvx751 : ConvexBetweenHumps 751 :=
  cvx_of L751_ok H751_ok I751_ok link751 (by decide)

/-! ### `N = 752` -/

def pL752 : Prm := ⟨74, 36, 35, 754, 11, 18446744073709551616, 216276399813028444, 216276399813028444⟩
def pH752 : Prm := ⟨72, 33, 36, 754, 11, 18446744073709551616, 216280797859539548, 216280797859539548⟩
def pI752 : Prm := ⟨63, 31, 29, 754, 11, 18446744073709551616, 216276399813028444, 216280797859539548⟩
theorem L752_fin : (prmOK pL752 752 && ptTest pL752 (runFrom pL752 (fmask pL752) (cmask pL752) (hmask pL752) 1 751 (true, (init pL752), (init pL752))) 752 376 false) = true := by
  decide +kernel
theorem L752_ok : RunOK pL752 752 (runFrom pL752 (fmask pL752) (cmask pL752) (hmask pL752) 1 751 (true, (init pL752), (init pL752))) ∧ ptTest pL752 (runFrom pL752 (fmask pL752) (cmask pL752) (hmask pL752) 1 751 (true, (init pL752), (init pL752))) 752 376 false = true :=
  fin_run (runOK_init (prmOK_of_and L752_fin) true) (by decide) rfl L752_fin ptTest_fst
theorem H752_fin : (prmOK pH752 752 && ptTest pH752 (runFrom pH752 (fmask pH752) (cmask pH752) (hmask pH752) 1 751 (true, (init pH752), (init pH752))) 752 376 true) = true := by
  decide +kernel
theorem H752_ok : RunOK pH752 752 (runFrom pH752 (fmask pH752) (cmask pH752) (hmask pH752) 1 751 (true, (init pH752), (init pH752))) ∧ ptTest pH752 (runFrom pH752 (fmask pH752) (cmask pH752) (hmask pH752) 1 751 (true, (init pH752), (init pH752))) 752 376 true = true :=
  fin_run (runOK_init (prmOK_of_and H752_fin) true) (by decide) rfl H752_fin ptTest_fst
theorem I752_fin : (prmOK pI752 752 && intTest pI752 (runFrom pI752 (fmask pI752) (cmask pI752) (hmask pI752) 1 751 (true, (init pI752), (init pI752))) 752 16 true) = true := by
  decide +kernel
theorem I752_ok : RunOK pI752 752 (runFrom pI752 (fmask pI752) (cmask pI752) (hmask pI752) 1 751 (true, (init pI752), (init pI752))) ∧ intTest pI752 (runFrom pI752 (fmask pI752) (cmask pI752) (hmask pI752) 1 751 (true, (init pI752), (init pI752))) 752 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I752_fin) true) (by decide) rfl I752_fin intTest_fst
theorem link752 : linkOK pL752 pH752 pI752 = true := by decide +kernel
theorem cvx752 : ConvexBetweenHumps 752 :=
  cvx_of L752_ok H752_ok I752_ok link752 (by decide)
theorem cenlink752 : cenLinkOK pI752 752 = true := by decide +kernel
theorem cen752 : CenterUniqueMin 752 ∧ DipHyp 752 ∧ OnePointHyps 752 :=
  cen_of L752_ok H752_ok I752_ok link752 cenlink752

/-! ### `N = 753` -/

def pL753 : Prm := ⟨72, 33, 36, 755, 11, 18446744073709551616, 216050407584846226, 216050407584846226⟩
def pH753 : Prm := ⟨72, 33, 36, 755, 11, 18446744073709551616, 216054805631357330, 216054805631357330⟩
def pI753 : Prm := ⟨63, 31, 29, 755, 11, 18446744073709551616, 216050407584846226, 216054805631357330⟩
theorem L753_fin : (prmOK pL753 753 && ptTest pL753 (runFrom pL753 (fmask pL753) (cmask pL753) (hmask pL753) 1 752 (true, (init pL753), (init pL753))) 753 377 false) = true := by
  decide +kernel
theorem L753_ok : RunOK pL753 753 (runFrom pL753 (fmask pL753) (cmask pL753) (hmask pL753) 1 752 (true, (init pL753), (init pL753))) ∧ ptTest pL753 (runFrom pL753 (fmask pL753) (cmask pL753) (hmask pL753) 1 752 (true, (init pL753), (init pL753))) 753 377 false = true :=
  fin_run (runOK_init (prmOK_of_and L753_fin) true) (by decide) rfl L753_fin ptTest_fst
theorem H753_fin : (prmOK pH753 753 && ptTest pH753 (runFrom pH753 (fmask pH753) (cmask pH753) (hmask pH753) 1 752 (true, (init pH753), (init pH753))) 753 377 true) = true := by
  decide +kernel
theorem H753_ok : RunOK pH753 753 (runFrom pH753 (fmask pH753) (cmask pH753) (hmask pH753) 1 752 (true, (init pH753), (init pH753))) ∧ ptTest pH753 (runFrom pH753 (fmask pH753) (cmask pH753) (hmask pH753) 1 752 (true, (init pH753), (init pH753))) 753 377 true = true :=
  fin_run (runOK_init (prmOK_of_and H753_fin) true) (by decide) rfl H753_fin ptTest_fst
theorem I753_fin : (prmOK pI753 753 && intTest pI753 (runFrom pI753 (fmask pI753) (cmask pI753) (hmask pI753) 1 752 (true, (init pI753), (init pI753))) 753 16 false) = true := by
  decide +kernel
theorem I753_ok : RunOK pI753 753 (runFrom pI753 (fmask pI753) (cmask pI753) (hmask pI753) 1 752 (true, (init pI753), (init pI753))) ∧ intTest pI753 (runFrom pI753 (fmask pI753) (cmask pI753) (hmask pI753) 1 752 (true, (init pI753), (init pI753))) 753 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I753_fin) true) (by decide) rfl I753_fin intTest_fst
theorem link753 : linkOK pL753 pH753 pI753 = true := by decide +kernel
theorem cvx753 : ConvexBetweenHumps 753 :=
  cvx_of L753_ok H753_ok I753_ok link753 (by decide)

/-! ### `N = 754` -/

def pL754 : Prm := ⟨72, 33, 36, 756, 11, 18446744073709551616, 215825208304992114, 215825208304992114⟩
def pH754 : Prm := ⟨74, 36, 35, 756, 11, 18446744073709551616, 215829606351503218, 215829606351503218⟩
def pI754 : Prm := ⟨63, 31, 29, 756, 11, 18446744073709551616, 215825208304992114, 215829606351503218⟩
theorem L754_fin : (prmOK pL754 754 && ptTest pL754 (runFrom pL754 (fmask pL754) (cmask pL754) (hmask pL754) 1 753 (true, (init pL754), (init pL754))) 754 377 false) = true := by
  decide +kernel
theorem L754_ok : RunOK pL754 754 (runFrom pL754 (fmask pL754) (cmask pL754) (hmask pL754) 1 753 (true, (init pL754), (init pL754))) ∧ ptTest pL754 (runFrom pL754 (fmask pL754) (cmask pL754) (hmask pL754) 1 753 (true, (init pL754), (init pL754))) 754 377 false = true :=
  fin_run (runOK_init (prmOK_of_and L754_fin) true) (by decide) rfl L754_fin ptTest_fst
theorem H754_fin : (prmOK pH754 754 && ptTest pH754 (runFrom pH754 (fmask pH754) (cmask pH754) (hmask pH754) 1 753 (true, (init pH754), (init pH754))) 754 377 true) = true := by
  decide +kernel
theorem H754_ok : RunOK pH754 754 (runFrom pH754 (fmask pH754) (cmask pH754) (hmask pH754) 1 753 (true, (init pH754), (init pH754))) ∧ ptTest pH754 (runFrom pH754 (fmask pH754) (cmask pH754) (hmask pH754) 1 753 (true, (init pH754), (init pH754))) 754 377 true = true :=
  fin_run (runOK_init (prmOK_of_and H754_fin) true) (by decide) rfl H754_fin ptTest_fst
theorem I754_fin : (prmOK pI754 754 && intTest pI754 (runFrom pI754 (fmask pI754) (cmask pI754) (hmask pI754) 1 753 (true, (init pI754), (init pI754))) 754 16 true) = true := by
  decide +kernel
theorem I754_ok : RunOK pI754 754 (runFrom pI754 (fmask pI754) (cmask pI754) (hmask pI754) 1 753 (true, (init pI754), (init pI754))) ∧ intTest pI754 (runFrom pI754 (fmask pI754) (cmask pI754) (hmask pI754) 1 753 (true, (init pI754), (init pI754))) 754 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I754_fin) true) (by decide) rfl I754_fin intTest_fst
theorem link754 : linkOK pL754 pH754 pI754 = true := by decide +kernel
theorem cvx754 : ConvexBetweenHumps 754 :=
  cvx_of L754_ok H754_ok I754_ok link754 (by decide)
theorem cenlink754 : cenLinkOK pI754 754 = true := by decide +kernel
theorem cen754 : CenterUniqueMin 754 ∧ DipHyp 754 ∧ OnePointHyps 754 :=
  cen_of L754_ok H754_ok I754_ok link754 cenlink754

/-! ### `N = 755` -/

def pL755 : Prm := ⟨74, 36, 35, 757, 11, 18446744073709551616, 215600251329633111, 215600251329633111⟩
def pH755 : Prm := ⟨72, 33, 36, 757, 11, 18446744073709551616, 215604649376144215, 215604649376144215⟩
def pI755 : Prm := ⟨63, 31, 29, 757, 11, 18446744073709551616, 215600251329633111, 215604649376144215⟩
theorem L755_fin : (prmOK pL755 755 && ptTest pL755 (runFrom pL755 (fmask pL755) (cmask pL755) (hmask pL755) 1 754 (true, (init pL755), (init pL755))) 755 378 false) = true := by
  decide +kernel
theorem L755_ok : RunOK pL755 755 (runFrom pL755 (fmask pL755) (cmask pL755) (hmask pL755) 1 754 (true, (init pL755), (init pL755))) ∧ ptTest pL755 (runFrom pL755 (fmask pL755) (cmask pL755) (hmask pL755) 1 754 (true, (init pL755), (init pL755))) 755 378 false = true :=
  fin_run (runOK_init (prmOK_of_and L755_fin) true) (by decide) rfl L755_fin ptTest_fst
theorem H755_fin : (prmOK pH755 755 && ptTest pH755 (runFrom pH755 (fmask pH755) (cmask pH755) (hmask pH755) 1 754 (true, (init pH755), (init pH755))) 755 378 true) = true := by
  decide +kernel
theorem H755_ok : RunOK pH755 755 (runFrom pH755 (fmask pH755) (cmask pH755) (hmask pH755) 1 754 (true, (init pH755), (init pH755))) ∧ ptTest pH755 (runFrom pH755 (fmask pH755) (cmask pH755) (hmask pH755) 1 754 (true, (init pH755), (init pH755))) 755 378 true = true :=
  fin_run (runOK_init (prmOK_of_and H755_fin) true) (by decide) rfl H755_fin ptTest_fst
theorem I755_fin : (prmOK pI755 755 && intTest pI755 (runFrom pI755 (fmask pI755) (cmask pI755) (hmask pI755) 1 754 (true, (init pI755), (init pI755))) 755 16 false) = true := by
  decide +kernel
theorem I755_ok : RunOK pI755 755 (runFrom pI755 (fmask pI755) (cmask pI755) (hmask pI755) 1 754 (true, (init pI755), (init pI755))) ∧ intTest pI755 (runFrom pI755 (fmask pI755) (cmask pI755) (hmask pI755) 1 754 (true, (init pI755), (init pI755))) 755 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I755_fin) true) (by decide) rfl I755_fin intTest_fst
theorem link755 : linkOK pL755 pH755 pI755 = true := by decide +kernel
theorem cvx755 : ConvexBetweenHumps 755 :=
  cvx_of L755_ok H755_ok I755_ok link755 (by decide)

/-! ### `N = 756` -/

def pL756 : Prm := ⟨72, 33, 36, 758, 11, 18446744073709551616, 215376081402374226, 215376081402374226⟩
def pH756 : Prm := ⟨72, 33, 36, 758, 11, 18446744073709551616, 215380479448885330, 215380479448885330⟩
def pI756 : Prm := ⟨63, 31, 29, 758, 11, 18446744073709551616, 215376081402374226, 215380479448885330⟩
theorem L756_fin : (prmOK pL756 756 && ptTest pL756 (runFrom pL756 (fmask pL756) (cmask pL756) (hmask pL756) 1 755 (true, (init pL756), (init pL756))) 756 378 false) = true := by
  decide +kernel
theorem L756_ok : RunOK pL756 756 (runFrom pL756 (fmask pL756) (cmask pL756) (hmask pL756) 1 755 (true, (init pL756), (init pL756))) ∧ ptTest pL756 (runFrom pL756 (fmask pL756) (cmask pL756) (hmask pL756) 1 755 (true, (init pL756), (init pL756))) 756 378 false = true :=
  fin_run (runOK_init (prmOK_of_and L756_fin) true) (by decide) rfl L756_fin ptTest_fst
theorem H756_fin : (prmOK pH756 756 && ptTest pH756 (runFrom pH756 (fmask pH756) (cmask pH756) (hmask pH756) 1 755 (true, (init pH756), (init pH756))) 756 378 true) = true := by
  decide +kernel
theorem H756_ok : RunOK pH756 756 (runFrom pH756 (fmask pH756) (cmask pH756) (hmask pH756) 1 755 (true, (init pH756), (init pH756))) ∧ ptTest pH756 (runFrom pH756 (fmask pH756) (cmask pH756) (hmask pH756) 1 755 (true, (init pH756), (init pH756))) 756 378 true = true :=
  fin_run (runOK_init (prmOK_of_and H756_fin) true) (by decide) rfl H756_fin ptTest_fst
theorem I756_fin : (prmOK pI756 756 && intTest pI756 (runFrom pI756 (fmask pI756) (cmask pI756) (hmask pI756) 1 755 (true, (init pI756), (init pI756))) 756 16 true) = true := by
  decide +kernel
theorem I756_ok : RunOK pI756 756 (runFrom pI756 (fmask pI756) (cmask pI756) (hmask pI756) 1 755 (true, (init pI756), (init pI756))) ∧ intTest pI756 (runFrom pI756 (fmask pI756) (cmask pI756) (hmask pI756) 1 755 (true, (init pI756), (init pI756))) 756 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I756_fin) true) (by decide) rfl I756_fin intTest_fst
theorem link756 : linkOK pL756 pH756 pI756 = true := by decide +kernel
theorem cvx756 : ConvexBetweenHumps 756 :=
  cvx_of L756_ok H756_ok I756_ok link756 (by decide)
theorem cenlink756 : cenLinkOK pI756 756 = true := by decide +kernel
theorem cen756 : CenterUniqueMin 756 ∧ DipHyp 756 ∧ OnePointHyps 756 :=
  cen_of L756_ok H756_ok I756_ok link756 cenlink756

/-! ### `N = 757` -/

def pL757 : Prm := ⟨74, 36, 35, 759, 11, 18446744073709551616, 215152152322944858, 215152152322944858⟩
def pH757 : Prm := ⟨72, 33, 36, 759, 11, 18446744073709551616, 215156550369455962, 215156550369455962⟩
def pI757 : Prm := ⟨63, 31, 29, 759, 11, 18446744073709551616, 215152152322944858, 215156550369455962⟩
theorem L757_fin : (prmOK pL757 757 && ptTest pL757 (runFrom pL757 (fmask pL757) (cmask pL757) (hmask pL757) 1 756 (true, (init pL757), (init pL757))) 757 379 false) = true := by
  decide +kernel
theorem L757_ok : RunOK pL757 757 (runFrom pL757 (fmask pL757) (cmask pL757) (hmask pL757) 1 756 (true, (init pL757), (init pL757))) ∧ ptTest pL757 (runFrom pL757 (fmask pL757) (cmask pL757) (hmask pL757) 1 756 (true, (init pL757), (init pL757))) 757 379 false = true :=
  fin_run (runOK_init (prmOK_of_and L757_fin) true) (by decide) rfl L757_fin ptTest_fst
theorem H757_fin : (prmOK pH757 757 && ptTest pH757 (runFrom pH757 (fmask pH757) (cmask pH757) (hmask pH757) 1 756 (true, (init pH757), (init pH757))) 757 379 true) = true := by
  decide +kernel
theorem H757_ok : RunOK pH757 757 (runFrom pH757 (fmask pH757) (cmask pH757) (hmask pH757) 1 756 (true, (init pH757), (init pH757))) ∧ ptTest pH757 (runFrom pH757 (fmask pH757) (cmask pH757) (hmask pH757) 1 756 (true, (init pH757), (init pH757))) 757 379 true = true :=
  fin_run (runOK_init (prmOK_of_and H757_fin) true) (by decide) rfl H757_fin ptTest_fst
theorem I757_fin : (prmOK pI757 757 && intTest pI757 (runFrom pI757 (fmask pI757) (cmask pI757) (hmask pI757) 1 756 (true, (init pI757), (init pI757))) 757 16 false) = true := by
  decide +kernel
theorem I757_ok : RunOK pI757 757 (runFrom pI757 (fmask pI757) (cmask pI757) (hmask pI757) 1 756 (true, (init pI757), (init pI757))) ∧ intTest pI757 (runFrom pI757 (fmask pI757) (cmask pI757) (hmask pI757) 1 756 (true, (init pI757), (init pI757))) 757 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I757_fin) true) (by decide) rfl I757_fin intTest_fst
theorem link757 : linkOK pL757 pH757 pI757 = true := by decide +kernel
theorem cvx757 : ConvexBetweenHumps 757 :=
  cvx_of L757_ok H757_ok I757_ok link757 (by decide)

/-! ### `N = 758` -/

def pL758 : Prm := ⟨72, 33, 36, 760, 11, 18446744073709551616, 214929004450527885, 214929004450527885⟩
def pH758 : Prm := ⟨72, 33, 36, 760, 11, 18446744073709551616, 214933402497038989, 214933402497038989⟩
def pI758 : Prm := ⟨63, 31, 29, 760, 11, 18446744073709551616, 214929004450527885, 214933402497038989⟩
theorem L758_fin : (prmOK pL758 758 && ptTest pL758 (runFrom pL758 (fmask pL758) (cmask pL758) (hmask pL758) 1 757 (true, (init pL758), (init pL758))) 758 379 false) = true := by
  decide +kernel
theorem L758_ok : RunOK pL758 758 (runFrom pL758 (fmask pL758) (cmask pL758) (hmask pL758) 1 757 (true, (init pL758), (init pL758))) ∧ ptTest pL758 (runFrom pL758 (fmask pL758) (cmask pL758) (hmask pL758) 1 757 (true, (init pL758), (init pL758))) 758 379 false = true :=
  fin_run (runOK_init (prmOK_of_and L758_fin) true) (by decide) rfl L758_fin ptTest_fst
theorem H758_fin : (prmOK pH758 758 && ptTest pH758 (runFrom pH758 (fmask pH758) (cmask pH758) (hmask pH758) 1 757 (true, (init pH758), (init pH758))) 758 379 true) = true := by
  decide +kernel
theorem H758_ok : RunOK pH758 758 (runFrom pH758 (fmask pH758) (cmask pH758) (hmask pH758) 1 757 (true, (init pH758), (init pH758))) ∧ ptTest pH758 (runFrom pH758 (fmask pH758) (cmask pH758) (hmask pH758) 1 757 (true, (init pH758), (init pH758))) 758 379 true = true :=
  fin_run (runOK_init (prmOK_of_and H758_fin) true) (by decide) rfl H758_fin ptTest_fst
theorem I758_fin : (prmOK pI758 758 && intTest pI758 (runFrom pI758 (fmask pI758) (cmask pI758) (hmask pI758) 1 757 (true, (init pI758), (init pI758))) 758 16 true) = true := by
  decide +kernel
theorem I758_ok : RunOK pI758 758 (runFrom pI758 (fmask pI758) (cmask pI758) (hmask pI758) 1 757 (true, (init pI758), (init pI758))) ∧ intTest pI758 (runFrom pI758 (fmask pI758) (cmask pI758) (hmask pI758) 1 757 (true, (init pI758), (init pI758))) 758 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I758_fin) true) (by decide) rfl I758_fin intTest_fst
theorem link758 : linkOK pL758 pH758 pI758 = true := by decide +kernel
theorem cvx758 : ConvexBetweenHumps 758 :=
  cvx_of L758_ok H758_ok I758_ok link758 (by decide)
theorem cenlink758 : cenLinkOK pI758 758 = true := by decide +kernel
theorem cen758 : CenterUniqueMin 758 ∧ DipHyp 758 ∧ OnePointHyps 758 :=
  cen_of L758_ok H758_ok I758_ok link758 cenlink758

/-! ### `N = 759` -/

def pL759 : Prm := ⟨72, 33, 36, 761, 11, 18446744073709551616, 214706095981025412, 214706095981025412⟩
def pH759 : Prm := ⟨72, 33, 36, 761, 11, 18446744073709551616, 214710494027536516, 214710494027536516⟩
def pI759 : Prm := ⟨63, 31, 29, 761, 11, 18446744073709551616, 214706095981025412, 214710494027536516⟩
theorem L759_fin : (prmOK pL759 759 && ptTest pL759 (runFrom pL759 (fmask pL759) (cmask pL759) (hmask pL759) 1 758 (true, (init pL759), (init pL759))) 759 380 false) = true := by
  decide +kernel
theorem L759_ok : RunOK pL759 759 (runFrom pL759 (fmask pL759) (cmask pL759) (hmask pL759) 1 758 (true, (init pL759), (init pL759))) ∧ ptTest pL759 (runFrom pL759 (fmask pL759) (cmask pL759) (hmask pL759) 1 758 (true, (init pL759), (init pL759))) 759 380 false = true :=
  fin_run (runOK_init (prmOK_of_and L759_fin) true) (by decide) rfl L759_fin ptTest_fst
theorem H759_fin : (prmOK pH759 759 && ptTest pH759 (runFrom pH759 (fmask pH759) (cmask pH759) (hmask pH759) 1 758 (true, (init pH759), (init pH759))) 759 380 true) = true := by
  decide +kernel
theorem H759_ok : RunOK pH759 759 (runFrom pH759 (fmask pH759) (cmask pH759) (hmask pH759) 1 758 (true, (init pH759), (init pH759))) ∧ ptTest pH759 (runFrom pH759 (fmask pH759) (cmask pH759) (hmask pH759) 1 758 (true, (init pH759), (init pH759))) 759 380 true = true :=
  fin_run (runOK_init (prmOK_of_and H759_fin) true) (by decide) rfl H759_fin ptTest_fst
theorem I759_fin : (prmOK pI759 759 && intTest pI759 (runFrom pI759 (fmask pI759) (cmask pI759) (hmask pI759) 1 758 (true, (init pI759), (init pI759))) 759 16 false) = true := by
  decide +kernel
theorem I759_ok : RunOK pI759 759 (runFrom pI759 (fmask pI759) (cmask pI759) (hmask pI759) 1 758 (true, (init pI759), (init pI759))) ∧ intTest pI759 (runFrom pI759 (fmask pI759) (cmask pI759) (hmask pI759) 1 758 (true, (init pI759), (init pI759))) 759 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I759_fin) true) (by decide) rfl I759_fin intTest_fst
theorem link759 : linkOK pL759 pH759 pI759 = true := by decide +kernel
theorem cvx759 : ConvexBetweenHumps 759 :=
  cvx_of L759_ok H759_ok I759_ok link759 (by decide)

/-! ### `N = 760` -/

def pL760 : Prm := ⟨72, 33, 36, 762, 11, 18446744073709551616, 214483962935905343, 214483962935905343⟩
def pH760 : Prm := ⟨72, 33, 36, 762, 11, 18446744073709551616, 214488360982416447, 214488360982416447⟩
def pI760 : Prm := ⟨63, 31, 29, 762, 11, 18446744073709551616, 214483962935905343, 214488360982416447⟩
theorem L760_fin : (prmOK pL760 760 && ptTest pL760 (runFrom pL760 (fmask pL760) (cmask pL760) (hmask pL760) 1 759 (true, (init pL760), (init pL760))) 760 380 false) = true := by
  decide +kernel
theorem L760_ok : RunOK pL760 760 (runFrom pL760 (fmask pL760) (cmask pL760) (hmask pL760) 1 759 (true, (init pL760), (init pL760))) ∧ ptTest pL760 (runFrom pL760 (fmask pL760) (cmask pL760) (hmask pL760) 1 759 (true, (init pL760), (init pL760))) 760 380 false = true :=
  fin_run (runOK_init (prmOK_of_and L760_fin) true) (by decide) rfl L760_fin ptTest_fst
theorem H760_fin : (prmOK pH760 760 && ptTest pH760 (runFrom pH760 (fmask pH760) (cmask pH760) (hmask pH760) 1 759 (true, (init pH760), (init pH760))) 760 380 true) = true := by
  decide +kernel
theorem H760_ok : RunOK pH760 760 (runFrom pH760 (fmask pH760) (cmask pH760) (hmask pH760) 1 759 (true, (init pH760), (init pH760))) ∧ ptTest pH760 (runFrom pH760 (fmask pH760) (cmask pH760) (hmask pH760) 1 759 (true, (init pH760), (init pH760))) 760 380 true = true :=
  fin_run (runOK_init (prmOK_of_and H760_fin) true) (by decide) rfl H760_fin ptTest_fst
theorem I760_fin : (prmOK pI760 760 && intTest pI760 (runFrom pI760 (fmask pI760) (cmask pI760) (hmask pI760) 1 759 (true, (init pI760), (init pI760))) 760 16 true) = true := by
  decide +kernel
theorem I760_ok : RunOK pI760 760 (runFrom pI760 (fmask pI760) (cmask pI760) (hmask pI760) 1 759 (true, (init pI760), (init pI760))) ∧ intTest pI760 (runFrom pI760 (fmask pI760) (cmask pI760) (hmask pI760) 1 759 (true, (init pI760), (init pI760))) 760 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I760_fin) true) (by decide) rfl I760_fin intTest_fst
theorem link760 : linkOK pL760 pH760 pI760 = true := by decide +kernel
theorem cvx760 : ConvexBetweenHumps 760 :=
  cvx_of L760_ok H760_ok I760_ok link760 (by decide)
theorem cenlink760 : cenLinkOK pI760 760 = true := by decide +kernel
theorem cen760 : CenterUniqueMin 760 ∧ DipHyp 760 ∧ OnePointHyps 760 :=
  cen_of L760_ok H760_ok I760_ok link760 cenlink760

/-! ### `N = 761` -/

def pL761 : Prm := ⟨72, 33, 36, 763, 11, 18446744073709551616, 214262067860406205, 214262067860406205⟩
def pH761 : Prm := ⟨72, 33, 36, 763, 11, 18446744073709551616, 214266465906917309, 214266465906917309⟩
def pI761 : Prm := ⟨63, 31, 29, 763, 11, 18446744073709551616, 214262067860406205, 214266465906917309⟩
theorem L761_fin : (prmOK pL761 761 && ptTest pL761 (runFrom pL761 (fmask pL761) (cmask pL761) (hmask pL761) 1 760 (true, (init pL761), (init pL761))) 761 381 false) = true := by
  decide +kernel
theorem L761_ok : RunOK pL761 761 (runFrom pL761 (fmask pL761) (cmask pL761) (hmask pL761) 1 760 (true, (init pL761), (init pL761))) ∧ ptTest pL761 (runFrom pL761 (fmask pL761) (cmask pL761) (hmask pL761) 1 760 (true, (init pL761), (init pL761))) 761 381 false = true :=
  fin_run (runOK_init (prmOK_of_and L761_fin) true) (by decide) rfl L761_fin ptTest_fst
theorem H761_fin : (prmOK pH761 761 && ptTest pH761 (runFrom pH761 (fmask pH761) (cmask pH761) (hmask pH761) 1 760 (true, (init pH761), (init pH761))) 761 381 true) = true := by
  decide +kernel
theorem H761_ok : RunOK pH761 761 (runFrom pH761 (fmask pH761) (cmask pH761) (hmask pH761) 1 760 (true, (init pH761), (init pH761))) ∧ ptTest pH761 (runFrom pH761 (fmask pH761) (cmask pH761) (hmask pH761) 1 760 (true, (init pH761), (init pH761))) 761 381 true = true :=
  fin_run (runOK_init (prmOK_of_and H761_fin) true) (by decide) rfl H761_fin ptTest_fst
theorem I761_fin : (prmOK pI761 761 && intTest pI761 (runFrom pI761 (fmask pI761) (cmask pI761) (hmask pI761) 1 760 (true, (init pI761), (init pI761))) 761 16 false) = true := by
  decide +kernel
theorem I761_ok : RunOK pI761 761 (runFrom pI761 (fmask pI761) (cmask pI761) (hmask pI761) 1 760 (true, (init pI761), (init pI761))) ∧ intTest pI761 (runFrom pI761 (fmask pI761) (cmask pI761) (hmask pI761) 1 760 (true, (init pI761), (init pI761))) 761 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I761_fin) true) (by decide) rfl I761_fin intTest_fst
theorem link761 : linkOK pL761 pH761 pI761 = true := by decide +kernel
theorem cvx761 : ConvexBetweenHumps 761 :=
  cvx_of L761_ok H761_ok I761_ok link761 (by decide)

/-! ### `N = 762` -/

def pL762 : Prm := ⟨72, 33, 36, 764, 11, 18446744073709551616, 214040942484379341, 214040942484379341⟩
def pH762 : Prm := ⟨72, 33, 36, 764, 11, 18446744073709551616, 214045340530890445, 214045340530890445⟩
def pI762 : Prm := ⟨63, 31, 29, 764, 11, 18446744073709551616, 214040942484379341, 214045340530890445⟩
theorem L762_fin : (prmOK pL762 762 && ptTest pL762 (runFrom pL762 (fmask pL762) (cmask pL762) (hmask pL762) 1 761 (true, (init pL762), (init pL762))) 762 381 false) = true := by
  decide +kernel
theorem L762_ok : RunOK pL762 762 (runFrom pL762 (fmask pL762) (cmask pL762) (hmask pL762) 1 761 (true, (init pL762), (init pL762))) ∧ ptTest pL762 (runFrom pL762 (fmask pL762) (cmask pL762) (hmask pL762) 1 761 (true, (init pL762), (init pL762))) 762 381 false = true :=
  fin_run (runOK_init (prmOK_of_and L762_fin) true) (by decide) rfl L762_fin ptTest_fst
theorem H762_fin : (prmOK pH762 762 && ptTest pH762 (runFrom pH762 (fmask pH762) (cmask pH762) (hmask pH762) 1 761 (true, (init pH762), (init pH762))) 762 381 true) = true := by
  decide +kernel
theorem H762_ok : RunOK pH762 762 (runFrom pH762 (fmask pH762) (cmask pH762) (hmask pH762) 1 761 (true, (init pH762), (init pH762))) ∧ ptTest pH762 (runFrom pH762 (fmask pH762) (cmask pH762) (hmask pH762) 1 761 (true, (init pH762), (init pH762))) 762 381 true = true :=
  fin_run (runOK_init (prmOK_of_and H762_fin) true) (by decide) rfl H762_fin ptTest_fst
theorem I762_fin : (prmOK pI762 762 && intTest pI762 (runFrom pI762 (fmask pI762) (cmask pI762) (hmask pI762) 1 761 (true, (init pI762), (init pI762))) 762 16 true) = true := by
  decide +kernel
theorem I762_ok : RunOK pI762 762 (runFrom pI762 (fmask pI762) (cmask pI762) (hmask pI762) 1 761 (true, (init pI762), (init pI762))) ∧ intTest pI762 (runFrom pI762 (fmask pI762) (cmask pI762) (hmask pI762) 1 761 (true, (init pI762), (init pI762))) 762 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I762_fin) true) (by decide) rfl I762_fin intTest_fst
theorem link762 : linkOK pL762 pH762 pI762 = true := by decide +kernel
theorem cvx762 : ConvexBetweenHumps 762 :=
  cvx_of L762_ok H762_ok I762_ok link762 (by decide)
theorem cenlink762 : cenLinkOK pI762 762 = true := by decide +kernel
theorem cen762 : CenterUniqueMin 762 ∧ DipHyp 762 ∧ OnePointHyps 762 :=
  cen_of L762_ok H762_ok I762_ok link762 cenlink762

/-! ### `N = 763` -/

def pL763 : Prm := ⟨72, 33, 36, 765, 11, 18446744073709551616, 213820053656116823, 213820053656116823⟩
def pH763 : Prm := ⟨72, 33, 36, 765, 11, 18446744073709551616, 213824451702627927, 213824451702627927⟩
def pI763 : Prm := ⟨63, 31, 29, 765, 11, 18446744073709551616, 213820053656116823, 213824451702627927⟩
theorem L763_fin : (prmOK pL763 763 && ptTest pL763 (runFrom pL763 (fmask pL763) (cmask pL763) (hmask pL763) 1 762 (true, (init pL763), (init pL763))) 763 382 false) = true := by
  decide +kernel
theorem L763_ok : RunOK pL763 763 (runFrom pL763 (fmask pL763) (cmask pL763) (hmask pL763) 1 762 (true, (init pL763), (init pL763))) ∧ ptTest pL763 (runFrom pL763 (fmask pL763) (cmask pL763) (hmask pL763) 1 762 (true, (init pL763), (init pL763))) 763 382 false = true :=
  fin_run (runOK_init (prmOK_of_and L763_fin) true) (by decide) rfl L763_fin ptTest_fst
theorem H763_fin : (prmOK pH763 763 && ptTest pH763 (runFrom pH763 (fmask pH763) (cmask pH763) (hmask pH763) 1 762 (true, (init pH763), (init pH763))) 763 382 true) = true := by
  decide +kernel
theorem H763_ok : RunOK pH763 763 (runFrom pH763 (fmask pH763) (cmask pH763) (hmask pH763) 1 762 (true, (init pH763), (init pH763))) ∧ ptTest pH763 (runFrom pH763 (fmask pH763) (cmask pH763) (hmask pH763) 1 762 (true, (init pH763), (init pH763))) 763 382 true = true :=
  fin_run (runOK_init (prmOK_of_and H763_fin) true) (by decide) rfl H763_fin ptTest_fst
theorem I763_fin : (prmOK pI763 763 && intTest pI763 (runFrom pI763 (fmask pI763) (cmask pI763) (hmask pI763) 1 762 (true, (init pI763), (init pI763))) 763 16 false) = true := by
  decide +kernel
theorem I763_ok : RunOK pI763 763 (runFrom pI763 (fmask pI763) (cmask pI763) (hmask pI763) 1 762 (true, (init pI763), (init pI763))) ∧ intTest pI763 (runFrom pI763 (fmask pI763) (cmask pI763) (hmask pI763) 1 762 (true, (init pI763), (init pI763))) 763 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I763_fin) true) (by decide) rfl I763_fin intTest_fst
theorem link763 : linkOK pL763 pH763 pI763 = true := by decide +kernel
theorem cvx763 : ConvexBetweenHumps 763 :=
  cvx_of L763_ok H763_ok I763_ok link763 (by decide)

/-! ### `N = 764` -/

def pL764 : Prm := ⟨72, 33, 36, 766, 11, 18446744073709551616, 213599928859416887, 213599928859416887⟩
def pH764 : Prm := ⟨72, 33, 36, 766, 11, 18446744073709551616, 213604326905927991, 213604326905927991⟩
def pI764 : Prm := ⟨63, 31, 29, 766, 11, 18446744073709551616, 213599928859416887, 213604326905927991⟩
theorem L764_fin : (prmOK pL764 764 && ptTest pL764 (runFrom pL764 (fmask pL764) (cmask pL764) (hmask pL764) 1 763 (true, (init pL764), (init pL764))) 764 382 false) = true := by
  decide +kernel
theorem L764_ok : RunOK pL764 764 (runFrom pL764 (fmask pL764) (cmask pL764) (hmask pL764) 1 763 (true, (init pL764), (init pL764))) ∧ ptTest pL764 (runFrom pL764 (fmask pL764) (cmask pL764) (hmask pL764) 1 763 (true, (init pL764), (init pL764))) 764 382 false = true :=
  fin_run (runOK_init (prmOK_of_and L764_fin) true) (by decide) rfl L764_fin ptTest_fst
theorem H764_fin : (prmOK pH764 764 && ptTest pH764 (runFrom pH764 (fmask pH764) (cmask pH764) (hmask pH764) 1 763 (true, (init pH764), (init pH764))) 764 382 true) = true := by
  decide +kernel
theorem H764_ok : RunOK pH764 764 (runFrom pH764 (fmask pH764) (cmask pH764) (hmask pH764) 1 763 (true, (init pH764), (init pH764))) ∧ ptTest pH764 (runFrom pH764 (fmask pH764) (cmask pH764) (hmask pH764) 1 763 (true, (init pH764), (init pH764))) 764 382 true = true :=
  fin_run (runOK_init (prmOK_of_and H764_fin) true) (by decide) rfl H764_fin ptTest_fst
theorem I764_fin : (prmOK pI764 764 && intTest pI764 (runFrom pI764 (fmask pI764) (cmask pI764) (hmask pI764) 1 763 (true, (init pI764), (init pI764))) 764 16 true) = true := by
  decide +kernel
theorem I764_ok : RunOK pI764 764 (runFrom pI764 (fmask pI764) (cmask pI764) (hmask pI764) 1 763 (true, (init pI764), (init pI764))) ∧ intTest pI764 (runFrom pI764 (fmask pI764) (cmask pI764) (hmask pI764) 1 763 (true, (init pI764), (init pI764))) 764 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I764_fin) true) (by decide) rfl I764_fin intTest_fst
theorem link764 : linkOK pL764 pH764 pI764 = true := by decide +kernel
theorem cvx764 : ConvexBetweenHumps 764 :=
  cvx_of L764_ok H764_ok I764_ok link764 (by decide)
theorem cenlink764 : cenLinkOK pI764 764 = true := by decide +kernel
theorem cen764 : CenterUniqueMin 764 ∧ DipHyp 764 ∧ OnePointHyps 764 :=
  cen_of L764_ok H764_ok I764_ok link764 cenlink764

/-! ### `N = 765` -/

def pL765 : Prm := ⟨72, 33, 36, 767, 11, 18446744073709551616, 213380039200061692, 213380039200061692⟩
def pH765 : Prm := ⟨72, 33, 36, 767, 11, 18446744073709551616, 213384437246572796, 213384437246572796⟩
def pI765 : Prm := ⟨63, 31, 29, 767, 11, 18446744073709551616, 213380039200061692, 213384437246572796⟩
theorem L765_fin : (prmOK pL765 765 && ptTest pL765 (runFrom pL765 (fmask pL765) (cmask pL765) (hmask pL765) 1 764 (true, (init pL765), (init pL765))) 765 383 false) = true := by
  decide +kernel
theorem L765_ok : RunOK pL765 765 (runFrom pL765 (fmask pL765) (cmask pL765) (hmask pL765) 1 764 (true, (init pL765), (init pL765))) ∧ ptTest pL765 (runFrom pL765 (fmask pL765) (cmask pL765) (hmask pL765) 1 764 (true, (init pL765), (init pL765))) 765 383 false = true :=
  fin_run (runOK_init (prmOK_of_and L765_fin) true) (by decide) rfl L765_fin ptTest_fst
theorem H765_fin : (prmOK pH765 765 && ptTest pH765 (runFrom pH765 (fmask pH765) (cmask pH765) (hmask pH765) 1 764 (true, (init pH765), (init pH765))) 765 383 true) = true := by
  decide +kernel
theorem H765_ok : RunOK pH765 765 (runFrom pH765 (fmask pH765) (cmask pH765) (hmask pH765) 1 764 (true, (init pH765), (init pH765))) ∧ ptTest pH765 (runFrom pH765 (fmask pH765) (cmask pH765) (hmask pH765) 1 764 (true, (init pH765), (init pH765))) 765 383 true = true :=
  fin_run (runOK_init (prmOK_of_and H765_fin) true) (by decide) rfl H765_fin ptTest_fst
theorem I765_fin : (prmOK pI765 765 && intTest pI765 (runFrom pI765 (fmask pI765) (cmask pI765) (hmask pI765) 1 764 (true, (init pI765), (init pI765))) 765 16 false) = true := by
  decide +kernel
theorem I765_ok : RunOK pI765 765 (runFrom pI765 (fmask pI765) (cmask pI765) (hmask pI765) 1 764 (true, (init pI765), (init pI765))) ∧ intTest pI765 (runFrom pI765 (fmask pI765) (cmask pI765) (hmask pI765) 1 764 (true, (init pI765), (init pI765))) 765 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I765_fin) true) (by decide) rfl I765_fin intTest_fst
theorem link765 : linkOK pL765 pH765 pI765 = true := by decide +kernel
theorem cvx765 : ConvexBetweenHumps 765 :=
  cvx_of L765_ok H765_ok I765_ok link765 (by decide)

/-! ### `N = 766` -/

def pL766 : Prm := ⟨72, 33, 36, 768, 11, 18446744073709551616, 213160907960566618, 213160907960566618⟩
def pH766 : Prm := ⟨72, 33, 36, 768, 11, 18446744073709551616, 213165306007077722, 213165306007077722⟩
def pI766 : Prm := ⟨63, 31, 29, 768, 11, 18446744073709551616, 213160907960566618, 213165306007077722⟩
theorem L766_fin : (prmOK pL766 766 && ptTest pL766 (runFrom pL766 (fmask pL766) (cmask pL766) (hmask pL766) 1 765 (true, (init pL766), (init pL766))) 766 383 false) = true := by
  decide +kernel
theorem L766_ok : RunOK pL766 766 (runFrom pL766 (fmask pL766) (cmask pL766) (hmask pL766) 1 765 (true, (init pL766), (init pL766))) ∧ ptTest pL766 (runFrom pL766 (fmask pL766) (cmask pL766) (hmask pL766) 1 765 (true, (init pL766), (init pL766))) 766 383 false = true :=
  fin_run (runOK_init (prmOK_of_and L766_fin) true) (by decide) rfl L766_fin ptTest_fst
theorem H766_fin : (prmOK pH766 766 && ptTest pH766 (runFrom pH766 (fmask pH766) (cmask pH766) (hmask pH766) 1 765 (true, (init pH766), (init pH766))) 766 383 true) = true := by
  decide +kernel
theorem H766_ok : RunOK pH766 766 (runFrom pH766 (fmask pH766) (cmask pH766) (hmask pH766) 1 765 (true, (init pH766), (init pH766))) ∧ ptTest pH766 (runFrom pH766 (fmask pH766) (cmask pH766) (hmask pH766) 1 765 (true, (init pH766), (init pH766))) 766 383 true = true :=
  fin_run (runOK_init (prmOK_of_and H766_fin) true) (by decide) rfl H766_fin ptTest_fst
theorem I766_fin : (prmOK pI766 766 && intTest pI766 (runFrom pI766 (fmask pI766) (cmask pI766) (hmask pI766) 1 765 (true, (init pI766), (init pI766))) 766 16 true) = true := by
  decide +kernel
theorem I766_ok : RunOK pI766 766 (runFrom pI766 (fmask pI766) (cmask pI766) (hmask pI766) 1 765 (true, (init pI766), (init pI766))) ∧ intTest pI766 (runFrom pI766 (fmask pI766) (cmask pI766) (hmask pI766) 1 765 (true, (init pI766), (init pI766))) 766 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I766_fin) true) (by decide) rfl I766_fin intTest_fst
theorem link766 : linkOK pL766 pH766 pI766 = true := by decide +kernel
theorem cvx766 : ConvexBetweenHumps 766 :=
  cvx_of L766_ok H766_ok I766_ok link766 (by decide)
theorem cenlink766 : cenLinkOK pI766 766 = true := by decide +kernel
theorem cen766 : CenterUniqueMin 766 ∧ DipHyp 766 ∧ OnePointHyps 766 :=
  cen_of L766_ok H766_ok I766_ok link766 cenlink766

/-! ### `N = 767` -/

def pL767 : Prm := ⟨72, 33, 36, 769, 11, 18446744073709551616, 212942010459286088, 212942010459286088⟩
def pH767 : Prm := ⟨72, 33, 36, 769, 11, 18446744073709551616, 212946408505797192, 212946408505797192⟩
def pI767 : Prm := ⟨63, 31, 29, 769, 11, 18446744073709551616, 212942010459286088, 212946408505797192⟩
theorem L767_fin : (prmOK pL767 767 && ptTest pL767 (runFrom pL767 (fmask pL767) (cmask pL767) (hmask pL767) 1 766 (true, (init pL767), (init pL767))) 767 384 false) = true := by
  decide +kernel
theorem L767_ok : RunOK pL767 767 (runFrom pL767 (fmask pL767) (cmask pL767) (hmask pL767) 1 766 (true, (init pL767), (init pL767))) ∧ ptTest pL767 (runFrom pL767 (fmask pL767) (cmask pL767) (hmask pL767) 1 766 (true, (init pL767), (init pL767))) 767 384 false = true :=
  fin_run (runOK_init (prmOK_of_and L767_fin) true) (by decide) rfl L767_fin ptTest_fst
theorem H767_fin : (prmOK pH767 767 && ptTest pH767 (runFrom pH767 (fmask pH767) (cmask pH767) (hmask pH767) 1 766 (true, (init pH767), (init pH767))) 767 384 true) = true := by
  decide +kernel
theorem H767_ok : RunOK pH767 767 (runFrom pH767 (fmask pH767) (cmask pH767) (hmask pH767) 1 766 (true, (init pH767), (init pH767))) ∧ ptTest pH767 (runFrom pH767 (fmask pH767) (cmask pH767) (hmask pH767) 1 766 (true, (init pH767), (init pH767))) 767 384 true = true :=
  fin_run (runOK_init (prmOK_of_and H767_fin) true) (by decide) rfl H767_fin ptTest_fst
theorem I767_fin : (prmOK pI767 767 && intTest pI767 (runFrom pI767 (fmask pI767) (cmask pI767) (hmask pI767) 1 766 (true, (init pI767), (init pI767))) 767 16 false) = true := by
  decide +kernel
theorem I767_ok : RunOK pI767 767 (runFrom pI767 (fmask pI767) (cmask pI767) (hmask pI767) 1 766 (true, (init pI767), (init pI767))) ∧ intTest pI767 (runFrom pI767 (fmask pI767) (cmask pI767) (hmask pI767) 1 766 (true, (init pI767), (init pI767))) 767 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I767_fin) true) (by decide) rfl I767_fin intTest_fst
theorem link767 : linkOK pL767 pH767 pI767 = true := by decide +kernel
theorem cvx767 : ConvexBetweenHumps 767 :=
  cvx_of L767_ok H767_ok I767_ok link767 (by decide)

/-! ### `N = 768` -/

def pL768 : Prm := ⟨72, 33, 36, 770, 11, 18446744073709551616, 212723865821780151, 212723865821780151⟩
def pH768 : Prm := ⟨72, 33, 36, 770, 11, 18446744073709551616, 212728263868291255, 212728263868291255⟩
def pI768 : Prm := ⟨63, 31, 29, 770, 11, 18446744073709551616, 212723865821780151, 212728263868291255⟩
theorem L768_fin : (prmOK pL768 768 && ptTest pL768 (runFrom pL768 (fmask pL768) (cmask pL768) (hmask pL768) 1 767 (true, (init pL768), (init pL768))) 768 384 false) = true := by
  decide +kernel
theorem L768_ok : RunOK pL768 768 (runFrom pL768 (fmask pL768) (cmask pL768) (hmask pL768) 1 767 (true, (init pL768), (init pL768))) ∧ ptTest pL768 (runFrom pL768 (fmask pL768) (cmask pL768) (hmask pL768) 1 767 (true, (init pL768), (init pL768))) 768 384 false = true :=
  fin_run (runOK_init (prmOK_of_and L768_fin) true) (by decide) rfl L768_fin ptTest_fst
theorem H768_fin : (prmOK pH768 768 && ptTest pH768 (runFrom pH768 (fmask pH768) (cmask pH768) (hmask pH768) 1 767 (true, (init pH768), (init pH768))) 768 384 true) = true := by
  decide +kernel
theorem H768_ok : RunOK pH768 768 (runFrom pH768 (fmask pH768) (cmask pH768) (hmask pH768) 1 767 (true, (init pH768), (init pH768))) ∧ ptTest pH768 (runFrom pH768 (fmask pH768) (cmask pH768) (hmask pH768) 1 767 (true, (init pH768), (init pH768))) 768 384 true = true :=
  fin_run (runOK_init (prmOK_of_and H768_fin) true) (by decide) rfl H768_fin ptTest_fst
theorem I768_fin : (prmOK pI768 768 && intTest pI768 (runFrom pI768 (fmask pI768) (cmask pI768) (hmask pI768) 1 767 (true, (init pI768), (init pI768))) 768 16 true) = true := by
  decide +kernel
theorem I768_ok : RunOK pI768 768 (runFrom pI768 (fmask pI768) (cmask pI768) (hmask pI768) 1 767 (true, (init pI768), (init pI768))) ∧ intTest pI768 (runFrom pI768 (fmask pI768) (cmask pI768) (hmask pI768) 1 767 (true, (init pI768), (init pI768))) 768 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I768_fin) true) (by decide) rfl I768_fin intTest_fst
theorem link768 : linkOK pL768 pH768 pI768 = true := by decide +kernel
theorem cvx768 : ConvexBetweenHumps 768 :=
  cvx_of L768_ok H768_ok I768_ok link768 (by decide)
theorem cenlink768 : cenLinkOK pI768 768 = true := by decide +kernel
theorem cen768 : CenterUniqueMin 768 ∧ DipHyp 768 ∧ OnePointHyps 768 :=
  cen_of L768_ok H768_ok I768_ok link768 cenlink768

/-! ### `N = 769` -/

def pL769 : Prm := ⟨72, 33, 36, 771, 11, 18446744073709551616, 212505953534463498, 212505953534463498⟩
def pH769 : Prm := ⟨72, 33, 36, 771, 11, 18446744073709551616, 212510351580974602, 212510351580974602⟩
def pI769 : Prm := ⟨63, 31, 29, 771, 11, 18446744073709551616, 212505953534463498, 212510351580974602⟩
theorem L769_fin : (prmOK pL769 769 && ptTest pL769 (runFrom pL769 (fmask pL769) (cmask pL769) (hmask pL769) 1 768 (true, (init pL769), (init pL769))) 769 385 false) = true := by
  decide +kernel
theorem L769_ok : RunOK pL769 769 (runFrom pL769 (fmask pL769) (cmask pL769) (hmask pL769) 1 768 (true, (init pL769), (init pL769))) ∧ ptTest pL769 (runFrom pL769 (fmask pL769) (cmask pL769) (hmask pL769) 1 768 (true, (init pL769), (init pL769))) 769 385 false = true :=
  fin_run (runOK_init (prmOK_of_and L769_fin) true) (by decide) rfl L769_fin ptTest_fst
theorem H769_fin : (prmOK pH769 769 && ptTest pH769 (runFrom pH769 (fmask pH769) (cmask pH769) (hmask pH769) 1 768 (true, (init pH769), (init pH769))) 769 385 true) = true := by
  decide +kernel
theorem H769_ok : RunOK pH769 769 (runFrom pH769 (fmask pH769) (cmask pH769) (hmask pH769) 1 768 (true, (init pH769), (init pH769))) ∧ ptTest pH769 (runFrom pH769 (fmask pH769) (cmask pH769) (hmask pH769) 1 768 (true, (init pH769), (init pH769))) 769 385 true = true :=
  fin_run (runOK_init (prmOK_of_and H769_fin) true) (by decide) rfl H769_fin ptTest_fst
theorem I769_fin : (prmOK pI769 769 && intTest pI769 (runFrom pI769 (fmask pI769) (cmask pI769) (hmask pI769) 1 768 (true, (init pI769), (init pI769))) 769 16 false) = true := by
  decide +kernel
theorem I769_ok : RunOK pI769 769 (runFrom pI769 (fmask pI769) (cmask pI769) (hmask pI769) 1 768 (true, (init pI769), (init pI769))) ∧ intTest pI769 (runFrom pI769 (fmask pI769) (cmask pI769) (hmask pI769) 1 768 (true, (init pI769), (init pI769))) 769 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I769_fin) true) (by decide) rfl I769_fin intTest_fst
theorem link769 : linkOK pL769 pH769 pI769 = true := by decide +kernel
theorem cvx769 : ConvexBetweenHumps 769 :=
  cvx_of L769_ok H769_ok I769_ok link769 (by decide)

/-! ### `N = 770` -/

def pL770 : Prm := ⟨72, 33, 36, 772, 11, 18446744073709551616, 212288788609678081, 212288788609678081⟩
def pH770 : Prm := ⟨72, 33, 36, 772, 11, 18446744073709551616, 212293186656189185, 212293186656189185⟩
def pI770 : Prm := ⟨63, 31, 29, 772, 11, 18446744073709551616, 212288788609678081, 212293186656189185⟩
theorem L770_fin : (prmOK pL770 770 && ptTest pL770 (runFrom pL770 (fmask pL770) (cmask pL770) (hmask pL770) 1 769 (true, (init pL770), (init pL770))) 770 385 false) = true := by
  decide +kernel
theorem L770_ok : RunOK pL770 770 (runFrom pL770 (fmask pL770) (cmask pL770) (hmask pL770) 1 769 (true, (init pL770), (init pL770))) ∧ ptTest pL770 (runFrom pL770 (fmask pL770) (cmask pL770) (hmask pL770) 1 769 (true, (init pL770), (init pL770))) 770 385 false = true :=
  fin_run (runOK_init (prmOK_of_and L770_fin) true) (by decide) rfl L770_fin ptTest_fst
theorem H770_fin : (prmOK pH770 770 && ptTest pH770 (runFrom pH770 (fmask pH770) (cmask pH770) (hmask pH770) 1 769 (true, (init pH770), (init pH770))) 770 385 true) = true := by
  decide +kernel
theorem H770_ok : RunOK pH770 770 (runFrom pH770 (fmask pH770) (cmask pH770) (hmask pH770) 1 769 (true, (init pH770), (init pH770))) ∧ ptTest pH770 (runFrom pH770 (fmask pH770) (cmask pH770) (hmask pH770) 1 769 (true, (init pH770), (init pH770))) 770 385 true = true :=
  fin_run (runOK_init (prmOK_of_and H770_fin) true) (by decide) rfl H770_fin ptTest_fst
theorem I770_fin : (prmOK pI770 770 && intTest pI770 (runFrom pI770 (fmask pI770) (cmask pI770) (hmask pI770) 1 769 (true, (init pI770), (init pI770))) 770 16 true) = true := by
  decide +kernel
theorem I770_ok : RunOK pI770 770 (runFrom pI770 (fmask pI770) (cmask pI770) (hmask pI770) 1 769 (true, (init pI770), (init pI770))) ∧ intTest pI770 (runFrom pI770 (fmask pI770) (cmask pI770) (hmask pI770) 1 769 (true, (init pI770), (init pI770))) 770 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I770_fin) true) (by decide) rfl I770_fin intTest_fst
theorem link770 : linkOK pL770 pH770 pI770 = true := by decide +kernel
theorem cvx770 : ConvexBetweenHumps 770 :=
  cvx_of L770_ok H770_ok I770_ok link770 (by decide)
theorem cenlink770 : cenLinkOK pI770 770 = true := by decide +kernel
theorem cen770 : CenterUniqueMin 770 ∧ DipHyp 770 ∧ OnePointHyps 770 :=
  cen_of L770_ok H770_ok I770_ok link770 cenlink770

/-! ### `N = 771` -/

def pL771 : Prm := ⟨72, 33, 36, 773, 11, 18446744073709551616, 212071854658161632, 212071854658161632⟩
def pH771 : Prm := ⟨72, 33, 36, 773, 11, 18446744073709551616, 212076252704672736, 212076252704672736⟩
def pI771 : Prm := ⟨64, 31, 30, 773, 11, 18446744073709551616, 212071854658161632, 212076252704672736⟩
theorem L771_fin : (prmOK pL771 771 && ptTest pL771 (runFrom pL771 (fmask pL771) (cmask pL771) (hmask pL771) 1 770 (true, (init pL771), (init pL771))) 771 386 false) = true := by
  decide +kernel
theorem L771_ok : RunOK pL771 771 (runFrom pL771 (fmask pL771) (cmask pL771) (hmask pL771) 1 770 (true, (init pL771), (init pL771))) ∧ ptTest pL771 (runFrom pL771 (fmask pL771) (cmask pL771) (hmask pL771) 1 770 (true, (init pL771), (init pL771))) 771 386 false = true :=
  fin_run (runOK_init (prmOK_of_and L771_fin) true) (by decide) rfl L771_fin ptTest_fst
theorem H771_fin : (prmOK pH771 771 && ptTest pH771 (runFrom pH771 (fmask pH771) (cmask pH771) (hmask pH771) 1 770 (true, (init pH771), (init pH771))) 771 386 true) = true := by
  decide +kernel
theorem H771_ok : RunOK pH771 771 (runFrom pH771 (fmask pH771) (cmask pH771) (hmask pH771) 1 770 (true, (init pH771), (init pH771))) ∧ ptTest pH771 (runFrom pH771 (fmask pH771) (cmask pH771) (hmask pH771) 1 770 (true, (init pH771), (init pH771))) 771 386 true = true :=
  fin_run (runOK_init (prmOK_of_and H771_fin) true) (by decide) rfl H771_fin ptTest_fst
theorem I771_fin : (prmOK pI771 771 && intTest pI771 (runFrom pI771 (fmask pI771) (cmask pI771) (hmask pI771) 1 770 (true, (init pI771), (init pI771))) 771 16 false) = true := by
  decide +kernel
theorem I771_ok : RunOK pI771 771 (runFrom pI771 (fmask pI771) (cmask pI771) (hmask pI771) 1 770 (true, (init pI771), (init pI771))) ∧ intTest pI771 (runFrom pI771 (fmask pI771) (cmask pI771) (hmask pI771) 1 770 (true, (init pI771), (init pI771))) 771 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I771_fin) true) (by decide) rfl I771_fin intTest_fst
theorem link771 : linkOK pL771 pH771 pI771 = true := by decide +kernel
theorem cvx771 : ConvexBetweenHumps 771 :=
  cvx_of L771_ok H771_ok I771_ok link771 (by decide)

/-! ### `N = 772` -/

def pL772 : Prm := ⟨73, 34, 36, 774, 11, 18446744073709551616, 211855662622148040, 211855662622148040⟩
def pH772 : Prm := ⟨73, 34, 36, 774, 11, 18446744073709551616, 211860060668659144, 211860060668659144⟩
def pI772 : Prm := ⟨63, 31, 29, 774, 11, 18446744073709551616, 211855662622148040, 211860060668659144⟩
theorem L772_fin : (prmOK pL772 772 && ptTest pL772 (runFrom pL772 (fmask pL772) (cmask pL772) (hmask pL772) 1 771 (true, (init pL772), (init pL772))) 772 386 false) = true := by
  decide +kernel
theorem L772_ok : RunOK pL772 772 (runFrom pL772 (fmask pL772) (cmask pL772) (hmask pL772) 1 771 (true, (init pL772), (init pL772))) ∧ ptTest pL772 (runFrom pL772 (fmask pL772) (cmask pL772) (hmask pL772) 1 771 (true, (init pL772), (init pL772))) 772 386 false = true :=
  fin_run (runOK_init (prmOK_of_and L772_fin) true) (by decide) rfl L772_fin ptTest_fst
theorem H772_fin : (prmOK pH772 772 && ptTest pH772 (runFrom pH772 (fmask pH772) (cmask pH772) (hmask pH772) 1 771 (true, (init pH772), (init pH772))) 772 386 true) = true := by
  decide +kernel
theorem H772_ok : RunOK pH772 772 (runFrom pH772 (fmask pH772) (cmask pH772) (hmask pH772) 1 771 (true, (init pH772), (init pH772))) ∧ ptTest pH772 (runFrom pH772 (fmask pH772) (cmask pH772) (hmask pH772) 1 771 (true, (init pH772), (init pH772))) 772 386 true = true :=
  fin_run (runOK_init (prmOK_of_and H772_fin) true) (by decide) rfl H772_fin ptTest_fst
theorem I772_fin : (prmOK pI772 772 && intTest pI772 (runFrom pI772 (fmask pI772) (cmask pI772) (hmask pI772) 1 771 (true, (init pI772), (init pI772))) 772 16 true) = true := by
  decide +kernel
theorem I772_ok : RunOK pI772 772 (runFrom pI772 (fmask pI772) (cmask pI772) (hmask pI772) 1 771 (true, (init pI772), (init pI772))) ∧ intTest pI772 (runFrom pI772 (fmask pI772) (cmask pI772) (hmask pI772) 1 771 (true, (init pI772), (init pI772))) 772 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I772_fin) true) (by decide) rfl I772_fin intTest_fst
theorem link772 : linkOK pL772 pH772 pI772 = true := by decide +kernel
theorem cvx772 : ConvexBetweenHumps 772 :=
  cvx_of L772_ok H772_ok I772_ok link772 (by decide)
theorem cenlink772 : cenLinkOK pI772 772 = true := by decide +kernel
theorem cen772 : CenterUniqueMin 772 ∧ DipHyp 772 ∧ OnePointHyps 772 :=
  cen_of L772_ok H772_ok I772_ok link772 cenlink772

/-! ### `N = 773` -/

def pL773 : Prm := ⟨73, 34, 36, 775, 11, 18446744073709551616, 211639700193385124, 211639700193385124⟩
def pH773 : Prm := ⟨72, 33, 36, 775, 11, 18446744073709551616, 211644098239896228, 211644098239896228⟩
def pI773 : Prm := ⟨64, 31, 30, 775, 11, 18446744073709551616, 211639700193385124, 211644098239896228⟩
theorem L773_fin : (prmOK pL773 773 && ptTest pL773 (runFrom pL773 (fmask pL773) (cmask pL773) (hmask pL773) 1 772 (true, (init pL773), (init pL773))) 773 387 false) = true := by
  decide +kernel
theorem L773_ok : RunOK pL773 773 (runFrom pL773 (fmask pL773) (cmask pL773) (hmask pL773) 1 772 (true, (init pL773), (init pL773))) ∧ ptTest pL773 (runFrom pL773 (fmask pL773) (cmask pL773) (hmask pL773) 1 772 (true, (init pL773), (init pL773))) 773 387 false = true :=
  fin_run (runOK_init (prmOK_of_and L773_fin) true) (by decide) rfl L773_fin ptTest_fst
theorem H773_fin : (prmOK pH773 773 && ptTest pH773 (runFrom pH773 (fmask pH773) (cmask pH773) (hmask pH773) 1 772 (true, (init pH773), (init pH773))) 773 387 true) = true := by
  decide +kernel
theorem H773_ok : RunOK pH773 773 (runFrom pH773 (fmask pH773) (cmask pH773) (hmask pH773) 1 772 (true, (init pH773), (init pH773))) ∧ ptTest pH773 (runFrom pH773 (fmask pH773) (cmask pH773) (hmask pH773) 1 772 (true, (init pH773), (init pH773))) 773 387 true = true :=
  fin_run (runOK_init (prmOK_of_and H773_fin) true) (by decide) rfl H773_fin ptTest_fst
theorem I773_fin : (prmOK pI773 773 && intTest pI773 (runFrom pI773 (fmask pI773) (cmask pI773) (hmask pI773) 1 772 (true, (init pI773), (init pI773))) 773 16 false) = true := by
  decide +kernel
theorem I773_ok : RunOK pI773 773 (runFrom pI773 (fmask pI773) (cmask pI773) (hmask pI773) 1 772 (true, (init pI773), (init pI773))) ∧ intTest pI773 (runFrom pI773 (fmask pI773) (cmask pI773) (hmask pI773) 1 772 (true, (init pI773), (init pI773))) 773 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I773_fin) true) (by decide) rfl I773_fin intTest_fst
theorem link773 : linkOK pL773 pH773 pI773 = true := by decide +kernel
theorem cvx773 : ConvexBetweenHumps 773 :=
  cvx_of L773_ok H773_ok I773_ok link773 (by decide)

/-! ### `N = 774` -/

def pL774 : Prm := ⟨74, 34, 37, 776, 11, 18446744073709551616, 211425573798238469, 211425573798238469⟩
def pH774 : Prm := ⟨75, 35, 37, 776, 11, 18446744073709551616, 211427772821494021, 211427772821494021⟩
def pI774 : Prm := ⟨62, 31, 28, 776, 11, 18446744073709551616, 211425573798238469, 211427772821494021⟩
theorem L774_fin : (prmOK pL774 774 && ptTest pL774 (runFrom pL774 (fmask pL774) (cmask pL774) (hmask pL774) 1 773 (true, (init pL774), (init pL774))) 774 387 false) = true := by
  decide +kernel
theorem L774_ok : RunOK pL774 774 (runFrom pL774 (fmask pL774) (cmask pL774) (hmask pL774) 1 773 (true, (init pL774), (init pL774))) ∧ ptTest pL774 (runFrom pL774 (fmask pL774) (cmask pL774) (hmask pL774) 1 773 (true, (init pL774), (init pL774))) 774 387 false = true :=
  fin_run (runOK_init (prmOK_of_and L774_fin) true) (by decide) rfl L774_fin ptTest_fst
theorem H774_fin : (prmOK pH774 774 && ptTest pH774 (runFrom pH774 (fmask pH774) (cmask pH774) (hmask pH774) 1 773 (true, (init pH774), (init pH774))) 774 387 true) = true := by
  decide +kernel
theorem H774_ok : RunOK pH774 774 (runFrom pH774 (fmask pH774) (cmask pH774) (hmask pH774) 1 773 (true, (init pH774), (init pH774))) ∧ ptTest pH774 (runFrom pH774 (fmask pH774) (cmask pH774) (hmask pH774) 1 773 (true, (init pH774), (init pH774))) 774 387 true = true :=
  fin_run (runOK_init (prmOK_of_and H774_fin) true) (by decide) rfl H774_fin ptTest_fst
theorem I774_fin : (prmOK pI774 774 && intTest pI774 (runFrom pI774 (fmask pI774) (cmask pI774) (hmask pI774) 1 773 (true, (init pI774), (init pI774))) 774 16 true) = true := by
  decide +kernel
theorem I774_ok : RunOK pI774 774 (runFrom pI774 (fmask pI774) (cmask pI774) (hmask pI774) 1 773 (true, (init pI774), (init pI774))) ∧ intTest pI774 (runFrom pI774 (fmask pI774) (cmask pI774) (hmask pI774) 1 773 (true, (init pI774), (init pI774))) 774 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I774_fin) true) (by decide) rfl I774_fin intTest_fst
theorem link774 : linkOK pL774 pH774 pI774 = true := by decide +kernel
theorem cvx774 : ConvexBetweenHumps 774 :=
  cvx_of L774_ok H774_ok I774_ok link774 (by decide)
theorem cenlink774 : cenLinkOK pI774 774 = true := by decide +kernel
theorem cen774 : CenterUniqueMin 774 ∧ DipHyp 774 ∧ OnePointHyps 774 :=
  cen_of L774_ok H774_ok I774_ok link774 cenlink774

/-! ### `N = 775` -/

def pL775 : Prm := ⟨74, 34, 37, 777, 11, 18446744073709551616, 211210576143561554, 211210576143561554⟩
def pH775 : Prm := ⟨75, 35, 37, 777, 11, 18446744073709551616, 211212775166817106, 211212775166817106⟩
def pI775 : Prm := ⟨62, 31, 28, 777, 11, 18446744073709551616, 211210576143561554, 211212775166817106⟩
theorem L775_fin : (prmOK pL775 775 && ptTest pL775 (runFrom pL775 (fmask pL775) (cmask pL775) (hmask pL775) 1 774 (true, (init pL775), (init pL775))) 775 388 false) = true := by
  decide +kernel
theorem L775_ok : RunOK pL775 775 (runFrom pL775 (fmask pL775) (cmask pL775) (hmask pL775) 1 774 (true, (init pL775), (init pL775))) ∧ ptTest pL775 (runFrom pL775 (fmask pL775) (cmask pL775) (hmask pL775) 1 774 (true, (init pL775), (init pL775))) 775 388 false = true :=
  fin_run (runOK_init (prmOK_of_and L775_fin) true) (by decide) rfl L775_fin ptTest_fst
theorem H775_fin : (prmOK pH775 775 && ptTest pH775 (runFrom pH775 (fmask pH775) (cmask pH775) (hmask pH775) 1 774 (true, (init pH775), (init pH775))) 775 388 true) = true := by
  decide +kernel
theorem H775_ok : RunOK pH775 775 (runFrom pH775 (fmask pH775) (cmask pH775) (hmask pH775) 1 774 (true, (init pH775), (init pH775))) ∧ ptTest pH775 (runFrom pH775 (fmask pH775) (cmask pH775) (hmask pH775) 1 774 (true, (init pH775), (init pH775))) 775 388 true = true :=
  fin_run (runOK_init (prmOK_of_and H775_fin) true) (by decide) rfl H775_fin ptTest_fst
theorem I775_fin : (prmOK pI775 775 && intTest pI775 (runFrom pI775 (fmask pI775) (cmask pI775) (hmask pI775) 1 774 (true, (init pI775), (init pI775))) 775 16 false) = true := by
  decide +kernel
theorem I775_ok : RunOK pI775 775 (runFrom pI775 (fmask pI775) (cmask pI775) (hmask pI775) 1 774 (true, (init pI775), (init pI775))) ∧ intTest pI775 (runFrom pI775 (fmask pI775) (cmask pI775) (hmask pI775) 1 774 (true, (init pI775), (init pI775))) 775 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I775_fin) true) (by decide) rfl I775_fin intTest_fst
theorem link775 : linkOK pL775 pH775 pI775 = true := by decide +kernel
theorem cvx775 : ConvexBetweenHumps 775 :=
  cvx_of L775_ok H775_ok I775_ok link775 (by decide)

/-! ### `N = 776` -/

def pL776 : Prm := ⟨74, 34, 37, 778, 11, 18446744073709551616, 210996309670208674, 210996309670208674⟩
def pH776 : Prm := ⟨75, 35, 37, 778, 11, 18446744073709551616, 210998508693464226, 210998508693464226⟩
def pI776 : Prm := ⟨62, 31, 28, 778, 11, 18446744073709551616, 210996309670208674, 210998508693464226⟩
theorem L776_fin : (prmOK pL776 776 && ptTest pL776 (runFrom pL776 (fmask pL776) (cmask pL776) (hmask pL776) 1 775 (true, (init pL776), (init pL776))) 776 388 false) = true := by
  decide +kernel
theorem L776_ok : RunOK pL776 776 (runFrom pL776 (fmask pL776) (cmask pL776) (hmask pL776) 1 775 (true, (init pL776), (init pL776))) ∧ ptTest pL776 (runFrom pL776 (fmask pL776) (cmask pL776) (hmask pL776) 1 775 (true, (init pL776), (init pL776))) 776 388 false = true :=
  fin_run (runOK_init (prmOK_of_and L776_fin) true) (by decide) rfl L776_fin ptTest_fst
theorem H776_fin : (prmOK pH776 776 && ptTest pH776 (runFrom pH776 (fmask pH776) (cmask pH776) (hmask pH776) 1 775 (true, (init pH776), (init pH776))) 776 388 true) = true := by
  decide +kernel
theorem H776_ok : RunOK pH776 776 (runFrom pH776 (fmask pH776) (cmask pH776) (hmask pH776) 1 775 (true, (init pH776), (init pH776))) ∧ ptTest pH776 (runFrom pH776 (fmask pH776) (cmask pH776) (hmask pH776) 1 775 (true, (init pH776), (init pH776))) 776 388 true = true :=
  fin_run (runOK_init (prmOK_of_and H776_fin) true) (by decide) rfl H776_fin ptTest_fst
theorem I776_fin : (prmOK pI776 776 && intTest pI776 (runFrom pI776 (fmask pI776) (cmask pI776) (hmask pI776) 1 775 (true, (init pI776), (init pI776))) 776 16 true) = true := by
  decide +kernel
theorem I776_ok : RunOK pI776 776 (runFrom pI776 (fmask pI776) (cmask pI776) (hmask pI776) 1 775 (true, (init pI776), (init pI776))) ∧ intTest pI776 (runFrom pI776 (fmask pI776) (cmask pI776) (hmask pI776) 1 775 (true, (init pI776), (init pI776))) 776 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I776_fin) true) (by decide) rfl I776_fin intTest_fst
theorem link776 : linkOK pL776 pH776 pI776 = true := by decide +kernel
theorem cvx776 : ConvexBetweenHumps 776 :=
  cvx_of L776_ok H776_ok I776_ok link776 (by decide)
theorem cenlink776 : cenLinkOK pI776 776 = true := by decide +kernel
theorem cen776 : CenterUniqueMin 776 ∧ DipHyp 776 ∧ OnePointHyps 776 :=
  cen_of L776_ok H776_ok I776_ok link776 cenlink776

/-! ### `N = 777` -/

def pL777 : Prm := ⟨75, 35, 37, 779, 11, 18446744073709551616, 210782270104499261, 210782270104499261⟩
def pH777 : Prm := ⟨75, 35, 37, 779, 11, 18446744073709551616, 210784469127754813, 210784469127754813⟩
def pI777 : Prm := ⟨62, 31, 28, 779, 11, 18446744073709551616, 210782270104499261, 210784469127754813⟩
theorem L777_fin : (prmOK pL777 777 && ptTest pL777 (runFrom pL777 (fmask pL777) (cmask pL777) (hmask pL777) 1 776 (true, (init pL777), (init pL777))) 777 389 false) = true := by
  decide +kernel
theorem L777_ok : RunOK pL777 777 (runFrom pL777 (fmask pL777) (cmask pL777) (hmask pL777) 1 776 (true, (init pL777), (init pL777))) ∧ ptTest pL777 (runFrom pL777 (fmask pL777) (cmask pL777) (hmask pL777) 1 776 (true, (init pL777), (init pL777))) 777 389 false = true :=
  fin_run (runOK_init (prmOK_of_and L777_fin) true) (by decide) rfl L777_fin ptTest_fst
theorem H777_fin : (prmOK pH777 777 && ptTest pH777 (runFrom pH777 (fmask pH777) (cmask pH777) (hmask pH777) 1 776 (true, (init pH777), (init pH777))) 777 389 true) = true := by
  decide +kernel
theorem H777_ok : RunOK pH777 777 (runFrom pH777 (fmask pH777) (cmask pH777) (hmask pH777) 1 776 (true, (init pH777), (init pH777))) ∧ ptTest pH777 (runFrom pH777 (fmask pH777) (cmask pH777) (hmask pH777) 1 776 (true, (init pH777), (init pH777))) 777 389 true = true :=
  fin_run (runOK_init (prmOK_of_and H777_fin) true) (by decide) rfl H777_fin ptTest_fst
theorem I777_fin : (prmOK pI777 777 && intTest pI777 (runFrom pI777 (fmask pI777) (cmask pI777) (hmask pI777) 1 776 (true, (init pI777), (init pI777))) 777 16 false) = true := by
  decide +kernel
theorem I777_ok : RunOK pI777 777 (runFrom pI777 (fmask pI777) (cmask pI777) (hmask pI777) 1 776 (true, (init pI777), (init pI777))) ∧ intTest pI777 (runFrom pI777 (fmask pI777) (cmask pI777) (hmask pI777) 1 776 (true, (init pI777), (init pI777))) 777 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I777_fin) true) (by decide) rfl I777_fin intTest_fst
theorem link777 : linkOK pL777 pH777 pI777 = true := by decide +kernel
theorem cvx777 : ConvexBetweenHumps 777 :=
  cvx_of L777_ok H777_ok I777_ok link777 (by decide)

/-! ### `N = 778` -/

def pL778 : Prm := ⟨75, 35, 37, 780, 11, 18446744073709551616, 210568956431672164, 210568956431672164⟩
def pH778 : Prm := ⟨74, 34, 37, 780, 11, 18446744073709551616, 210571155454927716, 210571155454927716⟩
def pI778 : Prm := ⟨62, 31, 28, 780, 11, 18446744073709551616, 210568956431672164, 210571155454927716⟩
theorem L778_fin : (prmOK pL778 778 && ptTest pL778 (runFrom pL778 (fmask pL778) (cmask pL778) (hmask pL778) 1 777 (true, (init pL778), (init pL778))) 778 389 false) = true := by
  decide +kernel
theorem L778_ok : RunOK pL778 778 (runFrom pL778 (fmask pL778) (cmask pL778) (hmask pL778) 1 777 (true, (init pL778), (init pL778))) ∧ ptTest pL778 (runFrom pL778 (fmask pL778) (cmask pL778) (hmask pL778) 1 777 (true, (init pL778), (init pL778))) 778 389 false = true :=
  fin_run (runOK_init (prmOK_of_and L778_fin) true) (by decide) rfl L778_fin ptTest_fst
theorem H778_fin : (prmOK pH778 778 && ptTest pH778 (runFrom pH778 (fmask pH778) (cmask pH778) (hmask pH778) 1 777 (true, (init pH778), (init pH778))) 778 389 true) = true := by
  decide +kernel
theorem H778_ok : RunOK pH778 778 (runFrom pH778 (fmask pH778) (cmask pH778) (hmask pH778) 1 777 (true, (init pH778), (init pH778))) ∧ ptTest pH778 (runFrom pH778 (fmask pH778) (cmask pH778) (hmask pH778) 1 777 (true, (init pH778), (init pH778))) 778 389 true = true :=
  fin_run (runOK_init (prmOK_of_and H778_fin) true) (by decide) rfl H778_fin ptTest_fst
theorem I778_fin : (prmOK pI778 778 && intTest pI778 (runFrom pI778 (fmask pI778) (cmask pI778) (hmask pI778) 1 777 (true, (init pI778), (init pI778))) 778 16 true) = true := by
  decide +kernel
theorem I778_ok : RunOK pI778 778 (runFrom pI778 (fmask pI778) (cmask pI778) (hmask pI778) 1 777 (true, (init pI778), (init pI778))) ∧ intTest pI778 (runFrom pI778 (fmask pI778) (cmask pI778) (hmask pI778) 1 777 (true, (init pI778), (init pI778))) 778 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I778_fin) true) (by decide) rfl I778_fin intTest_fst
theorem link778 : linkOK pL778 pH778 pI778 = true := by decide +kernel
theorem cvx778 : ConvexBetweenHumps 778 :=
  cvx_of L778_ok H778_ok I778_ok link778 (by decide)
theorem cenlink778 : cenLinkOK pI778 778 = true := by decide +kernel
theorem cen778 : CenterUniqueMin 778 ∧ DipHyp 778 ∧ OnePointHyps 778 :=
  cen_of L778_ok H778_ok I778_ok link778 cenlink778

/-! ### `N = 779` -/

def pL779 : Prm := ⟨74, 34, 37, 781, 11, 18446744073709551616, 210355868332678257, 210355868332678257⟩
def pH779 : Prm := ⟨75, 35, 37, 781, 11, 18446744073709551616, 210358067355933809, 210358067355933809⟩
def pI779 : Prm := ⟨62, 31, 28, 781, 11, 18446744073709551616, 210355868332678257, 210358067355933809⟩
theorem L779_fin : (prmOK pL779 779 && ptTest pL779 (runFrom pL779 (fmask pL779) (cmask pL779) (hmask pL779) 1 778 (true, (init pL779), (init pL779))) 779 390 false) = true := by
  decide +kernel
theorem L779_ok : RunOK pL779 779 (runFrom pL779 (fmask pL779) (cmask pL779) (hmask pL779) 1 778 (true, (init pL779), (init pL779))) ∧ ptTest pL779 (runFrom pL779 (fmask pL779) (cmask pL779) (hmask pL779) 1 778 (true, (init pL779), (init pL779))) 779 390 false = true :=
  fin_run (runOK_init (prmOK_of_and L779_fin) true) (by decide) rfl L779_fin ptTest_fst
theorem H779_fin : (prmOK pH779 779 && ptTest pH779 (runFrom pH779 (fmask pH779) (cmask pH779) (hmask pH779) 1 778 (true, (init pH779), (init pH779))) 779 390 true) = true := by
  decide +kernel
theorem H779_ok : RunOK pH779 779 (runFrom pH779 (fmask pH779) (cmask pH779) (hmask pH779) 1 778 (true, (init pH779), (init pH779))) ∧ ptTest pH779 (runFrom pH779 (fmask pH779) (cmask pH779) (hmask pH779) 1 778 (true, (init pH779), (init pH779))) 779 390 true = true :=
  fin_run (runOK_init (prmOK_of_and H779_fin) true) (by decide) rfl H779_fin ptTest_fst
theorem I779_fin : (prmOK pI779 779 && intTest pI779 (runFrom pI779 (fmask pI779) (cmask pI779) (hmask pI779) 1 778 (true, (init pI779), (init pI779))) 779 16 false) = true := by
  decide +kernel
theorem I779_ok : RunOK pI779 779 (runFrom pI779 (fmask pI779) (cmask pI779) (hmask pI779) 1 778 (true, (init pI779), (init pI779))) ∧ intTest pI779 (runFrom pI779 (fmask pI779) (cmask pI779) (hmask pI779) 1 778 (true, (init pI779), (init pI779))) 779 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I779_fin) true) (by decide) rfl I779_fin intTest_fst
theorem link779 : linkOK pL779 pH779 pI779 = true := by decide +kernel
theorem cvx779 : ConvexBetweenHumps 779 :=
  cvx_of L779_ok H779_ok I779_ok link779 (by decide)

/-! ### `N = 780` -/

def pL780 : Prm := ⟨75, 35, 37, 782, 11, 18446744073709551616, 210143500889683599, 210143500889683599⟩
def pH780 : Prm := ⟨74, 34, 37, 782, 11, 18446744073709551616, 210145699912939151, 210145699912939151⟩
def pI780 : Prm := ⟨62, 31, 28, 782, 11, 18446744073709551616, 210143500889683599, 210145699912939151⟩
theorem L780_fin : (prmOK pL780 780 && ptTest pL780 (runFrom pL780 (fmask pL780) (cmask pL780) (hmask pL780) 1 779 (true, (init pL780), (init pL780))) 780 390 false) = true := by
  decide +kernel
theorem L780_ok : RunOK pL780 780 (runFrom pL780 (fmask pL780) (cmask pL780) (hmask pL780) 1 779 (true, (init pL780), (init pL780))) ∧ ptTest pL780 (runFrom pL780 (fmask pL780) (cmask pL780) (hmask pL780) 1 779 (true, (init pL780), (init pL780))) 780 390 false = true :=
  fin_run (runOK_init (prmOK_of_and L780_fin) true) (by decide) rfl L780_fin ptTest_fst
theorem H780_fin : (prmOK pH780 780 && ptTest pH780 (runFrom pH780 (fmask pH780) (cmask pH780) (hmask pH780) 1 779 (true, (init pH780), (init pH780))) 780 390 true) = true := by
  decide +kernel
theorem H780_ok : RunOK pH780 780 (runFrom pH780 (fmask pH780) (cmask pH780) (hmask pH780) 1 779 (true, (init pH780), (init pH780))) ∧ ptTest pH780 (runFrom pH780 (fmask pH780) (cmask pH780) (hmask pH780) 1 779 (true, (init pH780), (init pH780))) 780 390 true = true :=
  fin_run (runOK_init (prmOK_of_and H780_fin) true) (by decide) rfl H780_fin ptTest_fst
theorem I780_fin : (prmOK pI780 780 && intTest pI780 (runFrom pI780 (fmask pI780) (cmask pI780) (hmask pI780) 1 779 (true, (init pI780), (init pI780))) 780 16 true) = true := by
  decide +kernel
theorem I780_ok : RunOK pI780 780 (runFrom pI780 (fmask pI780) (cmask pI780) (hmask pI780) 1 779 (true, (init pI780), (init pI780))) ∧ intTest pI780 (runFrom pI780 (fmask pI780) (cmask pI780) (hmask pI780) 1 779 (true, (init pI780), (init pI780))) 780 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I780_fin) true) (by decide) rfl I780_fin intTest_fst
theorem link780 : linkOK pL780 pH780 pI780 = true := by decide +kernel
theorem cvx780 : ConvexBetweenHumps 780 :=
  cvx_of L780_ok H780_ok I780_ok link780 (by decide)
theorem cenlink780 : cenLinkOK pI780 780 = true := by decide +kernel
theorem cen780 : CenterUniqueMin 780 ∧ DipHyp 780 ∧ OnePointHyps 780 :=
  cen_of L780_ok H780_ok I780_ok link780 cenlink780

/-! ### `N = 781` -/

def pL781 : Prm := ⟨75, 35, 37, 783, 11, 18446744073709551616, 209931357697226498, 209931357697226498⟩
def pH781 : Prm := ⟨75, 35, 37, 783, 11, 18446744073709551616, 209933556720482050, 209933556720482050⟩
def pI781 : Prm := ⟨62, 31, 28, 783, 11, 18446744073709551616, 209931357697226498, 209933556720482050⟩
theorem L781_fin : (prmOK pL781 781 && ptTest pL781 (runFrom pL781 (fmask pL781) (cmask pL781) (hmask pL781) 1 780 (true, (init pL781), (init pL781))) 781 391 false) = true := by
  decide +kernel
theorem L781_ok : RunOK pL781 781 (runFrom pL781 (fmask pL781) (cmask pL781) (hmask pL781) 1 780 (true, (init pL781), (init pL781))) ∧ ptTest pL781 (runFrom pL781 (fmask pL781) (cmask pL781) (hmask pL781) 1 780 (true, (init pL781), (init pL781))) 781 391 false = true :=
  fin_run (runOK_init (prmOK_of_and L781_fin) true) (by decide) rfl L781_fin ptTest_fst
theorem H781_fin : (prmOK pH781 781 && ptTest pH781 (runFrom pH781 (fmask pH781) (cmask pH781) (hmask pH781) 1 780 (true, (init pH781), (init pH781))) 781 391 true) = true := by
  decide +kernel
theorem H781_ok : RunOK pH781 781 (runFrom pH781 (fmask pH781) (cmask pH781) (hmask pH781) 1 780 (true, (init pH781), (init pH781))) ∧ ptTest pH781 (runFrom pH781 (fmask pH781) (cmask pH781) (hmask pH781) 1 780 (true, (init pH781), (init pH781))) 781 391 true = true :=
  fin_run (runOK_init (prmOK_of_and H781_fin) true) (by decide) rfl H781_fin ptTest_fst
theorem I781_fin : (prmOK pI781 781 && intTest pI781 (runFrom pI781 (fmask pI781) (cmask pI781) (hmask pI781) 1 780 (true, (init pI781), (init pI781))) 781 16 false) = true := by
  decide +kernel
theorem I781_ok : RunOK pI781 781 (runFrom pI781 (fmask pI781) (cmask pI781) (hmask pI781) 1 780 (true, (init pI781), (init pI781))) ∧ intTest pI781 (runFrom pI781 (fmask pI781) (cmask pI781) (hmask pI781) 1 780 (true, (init pI781), (init pI781))) 781 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I781_fin) true) (by decide) rfl I781_fin intTest_fst
theorem link781 : linkOK pL781 pH781 pI781 = true := by decide +kernel
theorem cvx781 : ConvexBetweenHumps 781 :=
  cvx_of L781_ok H781_ok I781_ok link781 (by decide)

/-! ### `N = 782` -/

def pL782 : Prm := ⟨75, 35, 37, 784, 11, 18446744073709551616, 209719929974817036, 209719929974817036⟩
def pH782 : Prm := ⟨74, 34, 37, 784, 11, 18446744073709551616, 209722128998072588, 209722128998072588⟩
def pI782 : Prm := ⟨62, 31, 28, 784, 11, 18446744073709551616, 209719929974817036, 209722128998072588⟩
theorem L782_fin : (prmOK pL782 782 && ptTest pL782 (runFrom pL782 (fmask pL782) (cmask pL782) (hmask pL782) 1 781 (true, (init pL782), (init pL782))) 782 391 false) = true := by
  decide +kernel
theorem L782_ok : RunOK pL782 782 (runFrom pL782 (fmask pL782) (cmask pL782) (hmask pL782) 1 781 (true, (init pL782), (init pL782))) ∧ ptTest pL782 (runFrom pL782 (fmask pL782) (cmask pL782) (hmask pL782) 1 781 (true, (init pL782), (init pL782))) 782 391 false = true :=
  fin_run (runOK_init (prmOK_of_and L782_fin) true) (by decide) rfl L782_fin ptTest_fst
theorem H782_fin : (prmOK pH782 782 && ptTest pH782 (runFrom pH782 (fmask pH782) (cmask pH782) (hmask pH782) 1 781 (true, (init pH782), (init pH782))) 782 391 true) = true := by
  decide +kernel
theorem H782_ok : RunOK pH782 782 (runFrom pH782 (fmask pH782) (cmask pH782) (hmask pH782) 1 781 (true, (init pH782), (init pH782))) ∧ ptTest pH782 (runFrom pH782 (fmask pH782) (cmask pH782) (hmask pH782) 1 781 (true, (init pH782), (init pH782))) 782 391 true = true :=
  fin_run (runOK_init (prmOK_of_and H782_fin) true) (by decide) rfl H782_fin ptTest_fst
theorem I782_fin : (prmOK pI782 782 && intTest pI782 (runFrom pI782 (fmask pI782) (cmask pI782) (hmask pI782) 1 781 (true, (init pI782), (init pI782))) 782 16 true) = true := by
  decide +kernel
theorem I782_ok : RunOK pI782 782 (runFrom pI782 (fmask pI782) (cmask pI782) (hmask pI782) 1 781 (true, (init pI782), (init pI782))) ∧ intTest pI782 (runFrom pI782 (fmask pI782) (cmask pI782) (hmask pI782) 1 781 (true, (init pI782), (init pI782))) 782 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I782_fin) true) (by decide) rfl I782_fin intTest_fst
theorem link782 : linkOK pL782 pH782 pI782 = true := by decide +kernel
theorem cvx782 : ConvexBetweenHumps 782 :=
  cvx_of L782_ok H782_ok I782_ok link782 (by decide)
theorem cenlink782 : cenLinkOK pI782 782 = true := by decide +kernel
theorem cen782 : CenterUniqueMin 782 ∧ DipHyp 782 ∧ OnePointHyps 782 :=
  cen_of L782_ok H782_ok I782_ok link782 cenlink782

/-! ### `N = 783` -/

def pL783 : Prm := ⟨75, 35, 37, 785, 11, 18446744073709551616, 209508725190071909, 209508725190071909⟩
def pH783 : Prm := ⟨75, 35, 37, 785, 11, 18446744073709551616, 209510924213327461, 209510924213327461⟩
def pI783 : Prm := ⟨62, 31, 28, 785, 11, 18446744073709551616, 209508725190071909, 209510924213327461⟩
theorem L783_fin : (prmOK pL783 783 && ptTest pL783 (runFrom pL783 (fmask pL783) (cmask pL783) (hmask pL783) 1 782 (true, (init pL783), (init pL783))) 783 392 false) = true := by
  decide +kernel
theorem L783_ok : RunOK pL783 783 (runFrom pL783 (fmask pL783) (cmask pL783) (hmask pL783) 1 782 (true, (init pL783), (init pL783))) ∧ ptTest pL783 (runFrom pL783 (fmask pL783) (cmask pL783) (hmask pL783) 1 782 (true, (init pL783), (init pL783))) 783 392 false = true :=
  fin_run (runOK_init (prmOK_of_and L783_fin) true) (by decide) rfl L783_fin ptTest_fst
theorem H783_fin : (prmOK pH783 783 && ptTest pH783 (runFrom pH783 (fmask pH783) (cmask pH783) (hmask pH783) 1 782 (true, (init pH783), (init pH783))) 783 392 true) = true := by
  decide +kernel
theorem H783_ok : RunOK pH783 783 (runFrom pH783 (fmask pH783) (cmask pH783) (hmask pH783) 1 782 (true, (init pH783), (init pH783))) ∧ ptTest pH783 (runFrom pH783 (fmask pH783) (cmask pH783) (hmask pH783) 1 782 (true, (init pH783), (init pH783))) 783 392 true = true :=
  fin_run (runOK_init (prmOK_of_and H783_fin) true) (by decide) rfl H783_fin ptTest_fst
theorem I783_fin : (prmOK pI783 783 && intTest pI783 (runFrom pI783 (fmask pI783) (cmask pI783) (hmask pI783) 1 782 (true, (init pI783), (init pI783))) 783 16 false) = true := by
  decide +kernel
theorem I783_ok : RunOK pI783 783 (runFrom pI783 (fmask pI783) (cmask pI783) (hmask pI783) 1 782 (true, (init pI783), (init pI783))) ∧ intTest pI783 (runFrom pI783 (fmask pI783) (cmask pI783) (hmask pI783) 1 782 (true, (init pI783), (init pI783))) 783 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I783_fin) true) (by decide) rfl I783_fin intTest_fst
theorem link783 : linkOK pL783 pH783 pI783 = true := by decide +kernel
theorem cvx783 : ConvexBetweenHumps 783 :=
  cvx_of L783_ok H783_ok I783_ok link783 (by decide)

/-! ### `N = 784` -/

def pL784 : Prm := ⟨75, 35, 37, 786, 11, 18446744073709551616, 209298230739745532, 209298230739745532⟩
def pH784 : Prm := ⟨75, 35, 37, 786, 11, 18446744073709551616, 209300429763001084, 209300429763001084⟩
def pI784 : Prm := ⟨62, 31, 28, 786, 11, 18446744073709551616, 209298230739745532, 209300429763001084⟩
theorem L784_fin : (prmOK pL784 784 && ptTest pL784 (runFrom pL784 (fmask pL784) (cmask pL784) (hmask pL784) 1 783 (true, (init pL784), (init pL784))) 784 392 false) = true := by
  decide +kernel
theorem L784_ok : RunOK pL784 784 (runFrom pL784 (fmask pL784) (cmask pL784) (hmask pL784) 1 783 (true, (init pL784), (init pL784))) ∧ ptTest pL784 (runFrom pL784 (fmask pL784) (cmask pL784) (hmask pL784) 1 783 (true, (init pL784), (init pL784))) 784 392 false = true :=
  fin_run (runOK_init (prmOK_of_and L784_fin) true) (by decide) rfl L784_fin ptTest_fst
theorem H784_fin : (prmOK pH784 784 && ptTest pH784 (runFrom pH784 (fmask pH784) (cmask pH784) (hmask pH784) 1 783 (true, (init pH784), (init pH784))) 784 392 true) = true := by
  decide +kernel
theorem H784_ok : RunOK pH784 784 (runFrom pH784 (fmask pH784) (cmask pH784) (hmask pH784) 1 783 (true, (init pH784), (init pH784))) ∧ ptTest pH784 (runFrom pH784 (fmask pH784) (cmask pH784) (hmask pH784) 1 783 (true, (init pH784), (init pH784))) 784 392 true = true :=
  fin_run (runOK_init (prmOK_of_and H784_fin) true) (by decide) rfl H784_fin ptTest_fst
theorem I784_fin : (prmOK pI784 784 && intTest pI784 (runFrom pI784 (fmask pI784) (cmask pI784) (hmask pI784) 1 783 (true, (init pI784), (init pI784))) 784 16 true) = true := by
  decide +kernel
theorem I784_ok : RunOK pI784 784 (runFrom pI784 (fmask pI784) (cmask pI784) (hmask pI784) 1 783 (true, (init pI784), (init pI784))) ∧ intTest pI784 (runFrom pI784 (fmask pI784) (cmask pI784) (hmask pI784) 1 783 (true, (init pI784), (init pI784))) 784 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I784_fin) true) (by decide) rfl I784_fin intTest_fst
theorem link784 : linkOK pL784 pH784 pI784 = true := by decide +kernel
theorem cvx784 : ConvexBetweenHumps 784 :=
  cvx_of L784_ok H784_ok I784_ok link784 (by decide)
theorem cenlink784 : cenLinkOK pI784 784 = true := by decide +kernel
theorem cen784 : CenterUniqueMin 784 ∧ DipHyp 784 ∧ OnePointHyps 784 :=
  cen_of L784_ok H784_ok I784_ok link784 cenlink784

/-! ### `N = 785` -/

def pL785 : Prm := ⟨75, 35, 37, 787, 11, 18446744073709551616, 209087957924485104, 209087957924485104⟩
def pH785 : Prm := ⟨75, 35, 37, 787, 11, 18446744073709551616, 209090156947740656, 209090156947740656⟩
def pI785 : Prm := ⟨62, 31, 28, 787, 11, 18446744073709551616, 209087957924485104, 209090156947740656⟩
theorem L785_fin : (prmOK pL785 785 && ptTest pL785 (runFrom pL785 (fmask pL785) (cmask pL785) (hmask pL785) 1 784 (true, (init pL785), (init pL785))) 785 393 false) = true := by
  decide +kernel
theorem L785_ok : RunOK pL785 785 (runFrom pL785 (fmask pL785) (cmask pL785) (hmask pL785) 1 784 (true, (init pL785), (init pL785))) ∧ ptTest pL785 (runFrom pL785 (fmask pL785) (cmask pL785) (hmask pL785) 1 784 (true, (init pL785), (init pL785))) 785 393 false = true :=
  fin_run (runOK_init (prmOK_of_and L785_fin) true) (by decide) rfl L785_fin ptTest_fst
theorem H785_fin : (prmOK pH785 785 && ptTest pH785 (runFrom pH785 (fmask pH785) (cmask pH785) (hmask pH785) 1 784 (true, (init pH785), (init pH785))) 785 393 true) = true := by
  decide +kernel
theorem H785_ok : RunOK pH785 785 (runFrom pH785 (fmask pH785) (cmask pH785) (hmask pH785) 1 784 (true, (init pH785), (init pH785))) ∧ ptTest pH785 (runFrom pH785 (fmask pH785) (cmask pH785) (hmask pH785) 1 784 (true, (init pH785), (init pH785))) 785 393 true = true :=
  fin_run (runOK_init (prmOK_of_and H785_fin) true) (by decide) rfl H785_fin ptTest_fst
theorem I785_fin : (prmOK pI785 785 && intTest pI785 (runFrom pI785 (fmask pI785) (cmask pI785) (hmask pI785) 1 784 (true, (init pI785), (init pI785))) 785 16 false) = true := by
  decide +kernel
theorem I785_ok : RunOK pI785 785 (runFrom pI785 (fmask pI785) (cmask pI785) (hmask pI785) 1 784 (true, (init pI785), (init pI785))) ∧ intTest pI785 (runFrom pI785 (fmask pI785) (cmask pI785) (hmask pI785) 1 784 (true, (init pI785), (init pI785))) 785 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I785_fin) true) (by decide) rfl I785_fin intTest_fst
theorem link785 : linkOK pL785 pH785 pI785 = true := by decide +kernel
theorem cvx785 : ConvexBetweenHumps 785 :=
  cvx_of L785_ok H785_ok I785_ok link785 (by decide)

/-! ### `N = 786` -/

def pL786 : Prm := ⟨75, 35, 37, 788, 11, 18446744073709551616, 208878390357728510, 208878390357728510⟩
def pH786 : Prm := ⟨75, 35, 37, 788, 11, 18446744073709551616, 208880589380984062, 208880589380984062⟩
def pI786 : Prm := ⟨62, 31, 28, 788, 11, 18446744073709551616, 208878390357728510, 208880589380984062⟩
theorem L786_fin : (prmOK pL786 786 && ptTest pL786 (runFrom pL786 (fmask pL786) (cmask pL786) (hmask pL786) 1 785 (true, (init pL786), (init pL786))) 786 393 false) = true := by
  decide +kernel
theorem L786_ok : RunOK pL786 786 (runFrom pL786 (fmask pL786) (cmask pL786) (hmask pL786) 1 785 (true, (init pL786), (init pL786))) ∧ ptTest pL786 (runFrom pL786 (fmask pL786) (cmask pL786) (hmask pL786) 1 785 (true, (init pL786), (init pL786))) 786 393 false = true :=
  fin_run (runOK_init (prmOK_of_and L786_fin) true) (by decide) rfl L786_fin ptTest_fst
theorem H786_fin : (prmOK pH786 786 && ptTest pH786 (runFrom pH786 (fmask pH786) (cmask pH786) (hmask pH786) 1 785 (true, (init pH786), (init pH786))) 786 393 true) = true := by
  decide +kernel
theorem H786_ok : RunOK pH786 786 (runFrom pH786 (fmask pH786) (cmask pH786) (hmask pH786) 1 785 (true, (init pH786), (init pH786))) ∧ ptTest pH786 (runFrom pH786 (fmask pH786) (cmask pH786) (hmask pH786) 1 785 (true, (init pH786), (init pH786))) 786 393 true = true :=
  fin_run (runOK_init (prmOK_of_and H786_fin) true) (by decide) rfl H786_fin ptTest_fst
theorem I786_fin : (prmOK pI786 786 && intTest pI786 (runFrom pI786 (fmask pI786) (cmask pI786) (hmask pI786) 1 785 (true, (init pI786), (init pI786))) 786 17 true) = true := by
  decide +kernel
theorem I786_ok : RunOK pI786 786 (runFrom pI786 (fmask pI786) (cmask pI786) (hmask pI786) 1 785 (true, (init pI786), (init pI786))) ∧ intTest pI786 (runFrom pI786 (fmask pI786) (cmask pI786) (hmask pI786) 1 785 (true, (init pI786), (init pI786))) 786 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I786_fin) true) (by decide) rfl I786_fin intTest_fst
theorem link786 : linkOK pL786 pH786 pI786 = true := by decide +kernel
theorem cvx786 : ConvexBetweenHumps 786 :=
  cvx_of L786_ok H786_ok I786_ok link786 (by decide)
theorem cenlink786 : cenLinkOK pI786 786 = true := by decide +kernel
theorem cen786 : CenterUniqueMin 786 ∧ DipHyp 786 ∧ OnePointHyps 786 :=
  cen_of L786_ok H786_ok I786_ok link786 cenlink786

/-! ### `N = 787` -/

def pL787 : Prm := ⟨75, 35, 37, 789, 11, 18446744073709551616, 208669043133695868, 208669043133695868⟩
def pH787 : Prm := ⟨75, 35, 37, 789, 11, 18446744073709551616, 208671242156951420, 208671242156951420⟩
def pI787 : Prm := ⟨62, 31, 28, 789, 11, 18446744073709551616, 208669043133695868, 208671242156951420⟩
theorem L787_fin : (prmOK pL787 787 && ptTest pL787 (runFrom pL787 (fmask pL787) (cmask pL787) (hmask pL787) 1 786 (true, (init pL787), (init pL787))) 787 394 false) = true := by
  decide +kernel
theorem L787_ok : RunOK pL787 787 (runFrom pL787 (fmask pL787) (cmask pL787) (hmask pL787) 1 786 (true, (init pL787), (init pL787))) ∧ ptTest pL787 (runFrom pL787 (fmask pL787) (cmask pL787) (hmask pL787) 1 786 (true, (init pL787), (init pL787))) 787 394 false = true :=
  fin_run (runOK_init (prmOK_of_and L787_fin) true) (by decide) rfl L787_fin ptTest_fst
theorem H787_fin : (prmOK pH787 787 && ptTest pH787 (runFrom pH787 (fmask pH787) (cmask pH787) (hmask pH787) 1 786 (true, (init pH787), (init pH787))) 787 394 true) = true := by
  decide +kernel
theorem H787_ok : RunOK pH787 787 (runFrom pH787 (fmask pH787) (cmask pH787) (hmask pH787) 1 786 (true, (init pH787), (init pH787))) ∧ ptTest pH787 (runFrom pH787 (fmask pH787) (cmask pH787) (hmask pH787) 1 786 (true, (init pH787), (init pH787))) 787 394 true = true :=
  fin_run (runOK_init (prmOK_of_and H787_fin) true) (by decide) rfl H787_fin ptTest_fst
theorem I787_fin : (prmOK pI787 787 && intTest pI787 (runFrom pI787 (fmask pI787) (cmask pI787) (hmask pI787) 1 786 (true, (init pI787), (init pI787))) 787 17 false) = true := by
  decide +kernel
theorem I787_ok : RunOK pI787 787 (runFrom pI787 (fmask pI787) (cmask pI787) (hmask pI787) 1 786 (true, (init pI787), (init pI787))) ∧ intTest pI787 (runFrom pI787 (fmask pI787) (cmask pI787) (hmask pI787) 1 786 (true, (init pI787), (init pI787))) 787 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I787_fin) true) (by decide) rfl I787_fin intTest_fst
theorem link787 : linkOK pL787 pH787 pI787 = true := by decide +kernel
theorem cvx787 : ConvexBetweenHumps 787 :=
  cvx_of L787_ok H787_ok I787_ok link787 (by decide)

/-! ### `N = 788` -/

def pL788 : Prm := ⟨75, 35, 37, 790, 11, 18446744073709551616, 208460396121302038, 208460396121302038⟩
def pH788 : Prm := ⟨75, 35, 37, 790, 11, 18446744073709551616, 208462595144557590, 208462595144557590⟩
def pI788 : Prm := ⟨62, 31, 28, 790, 11, 18446744073709551616, 208460396121302038, 208462595144557590⟩
theorem L788_fin : (prmOK pL788 788 && ptTest pL788 (runFrom pL788 (fmask pL788) (cmask pL788) (hmask pL788) 1 787 (true, (init pL788), (init pL788))) 788 394 false) = true := by
  decide +kernel
theorem L788_ok : RunOK pL788 788 (runFrom pL788 (fmask pL788) (cmask pL788) (hmask pL788) 1 787 (true, (init pL788), (init pL788))) ∧ ptTest pL788 (runFrom pL788 (fmask pL788) (cmask pL788) (hmask pL788) 1 787 (true, (init pL788), (init pL788))) 788 394 false = true :=
  fin_run (runOK_init (prmOK_of_and L788_fin) true) (by decide) rfl L788_fin ptTest_fst
theorem H788_fin : (prmOK pH788 788 && ptTest pH788 (runFrom pH788 (fmask pH788) (cmask pH788) (hmask pH788) 1 787 (true, (init pH788), (init pH788))) 788 394 true) = true := by
  decide +kernel
theorem H788_ok : RunOK pH788 788 (runFrom pH788 (fmask pH788) (cmask pH788) (hmask pH788) 1 787 (true, (init pH788), (init pH788))) ∧ ptTest pH788 (runFrom pH788 (fmask pH788) (cmask pH788) (hmask pH788) 1 787 (true, (init pH788), (init pH788))) 788 394 true = true :=
  fin_run (runOK_init (prmOK_of_and H788_fin) true) (by decide) rfl H788_fin ptTest_fst
theorem I788_fin : (prmOK pI788 788 && intTest pI788 (runFrom pI788 (fmask pI788) (cmask pI788) (hmask pI788) 1 787 (true, (init pI788), (init pI788))) 788 17 true) = true := by
  decide +kernel
theorem I788_ok : RunOK pI788 788 (runFrom pI788 (fmask pI788) (cmask pI788) (hmask pI788) 1 787 (true, (init pI788), (init pI788))) ∧ intTest pI788 (runFrom pI788 (fmask pI788) (cmask pI788) (hmask pI788) 1 787 (true, (init pI788), (init pI788))) 788 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I788_fin) true) (by decide) rfl I788_fin intTest_fst
theorem link788 : linkOK pL788 pH788 pI788 = true := by decide +kernel
theorem cvx788 : ConvexBetweenHumps 788 :=
  cvx_of L788_ok H788_ok I788_ok link788 (by decide)
theorem cenlink788 : cenLinkOK pI788 788 = true := by decide +kernel
theorem cen788 : CenterUniqueMin 788 ∧ DipHyp 788 ∧ OnePointHyps 788 :=
  cen_of L788_ok H788_ok I788_ok link788 cenlink788

/-! ### `N = 789` -/

def pL789 : Prm := ⟨75, 35, 37, 791, 11, 18446744073709551616, 208251968169398980, 208251968169398980⟩
def pH789 : Prm := ⟨75, 35, 37, 791, 11, 18446744073709551616, 208254167192654532, 208254167192654532⟩
def pI789 : Prm := ⟨62, 31, 28, 791, 11, 18446744073709551616, 208251968169398980, 208254167192654532⟩
theorem L789_fin : (prmOK pL789 789 && ptTest pL789 (runFrom pL789 (fmask pL789) (cmask pL789) (hmask pL789) 1 788 (true, (init pL789), (init pL789))) 789 395 false) = true := by
  decide +kernel
theorem L789_ok : RunOK pL789 789 (runFrom pL789 (fmask pL789) (cmask pL789) (hmask pL789) 1 788 (true, (init pL789), (init pL789))) ∧ ptTest pL789 (runFrom pL789 (fmask pL789) (cmask pL789) (hmask pL789) 1 788 (true, (init pL789), (init pL789))) 789 395 false = true :=
  fin_run (runOK_init (prmOK_of_and L789_fin) true) (by decide) rfl L789_fin ptTest_fst
theorem H789_fin : (prmOK pH789 789 && ptTest pH789 (runFrom pH789 (fmask pH789) (cmask pH789) (hmask pH789) 1 788 (true, (init pH789), (init pH789))) 789 395 true) = true := by
  decide +kernel
theorem H789_ok : RunOK pH789 789 (runFrom pH789 (fmask pH789) (cmask pH789) (hmask pH789) 1 788 (true, (init pH789), (init pH789))) ∧ ptTest pH789 (runFrom pH789 (fmask pH789) (cmask pH789) (hmask pH789) 1 788 (true, (init pH789), (init pH789))) 789 395 true = true :=
  fin_run (runOK_init (prmOK_of_and H789_fin) true) (by decide) rfl H789_fin ptTest_fst
theorem I789_fin : (prmOK pI789 789 && intTest pI789 (runFrom pI789 (fmask pI789) (cmask pI789) (hmask pI789) 1 788 (true, (init pI789), (init pI789))) 789 17 false) = true := by
  decide +kernel
theorem I789_ok : RunOK pI789 789 (runFrom pI789 (fmask pI789) (cmask pI789) (hmask pI789) 1 788 (true, (init pI789), (init pI789))) ∧ intTest pI789 (runFrom pI789 (fmask pI789) (cmask pI789) (hmask pI789) 1 788 (true, (init pI789), (init pI789))) 789 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I789_fin) true) (by decide) rfl I789_fin intTest_fst
theorem link789 : linkOK pL789 pH789 pI789 = true := by decide +kernel
theorem cvx789 : ConvexBetweenHumps 789 :=
  cvx_of L789_ok H789_ok I789_ok link789 (by decide)

/-! ### `N = 790` -/

def pL790 : Prm := ⟨75, 35, 37, 792, 11, 18446744073709551616, 208044235440803095, 208044235440803095⟩
def pH790 : Prm := ⟨75, 35, 37, 792, 11, 18446744073709551616, 208046434464058647, 208046434464058647⟩
def pI790 : Prm := ⟨62, 31, 28, 792, 11, 18446744073709551616, 208044235440803095, 208046434464058647⟩
theorem L790_fin : (prmOK pL790 790 && ptTest pL790 (runFrom pL790 (fmask pL790) (cmask pL790) (hmask pL790) 1 789 (true, (init pL790), (init pL790))) 790 395 false) = true := by
  decide +kernel
theorem L790_ok : RunOK pL790 790 (runFrom pL790 (fmask pL790) (cmask pL790) (hmask pL790) 1 789 (true, (init pL790), (init pL790))) ∧ ptTest pL790 (runFrom pL790 (fmask pL790) (cmask pL790) (hmask pL790) 1 789 (true, (init pL790), (init pL790))) 790 395 false = true :=
  fin_run (runOK_init (prmOK_of_and L790_fin) true) (by decide) rfl L790_fin ptTest_fst
theorem H790_fin : (prmOK pH790 790 && ptTest pH790 (runFrom pH790 (fmask pH790) (cmask pH790) (hmask pH790) 1 789 (true, (init pH790), (init pH790))) 790 395 true) = true := by
  decide +kernel
theorem H790_ok : RunOK pH790 790 (runFrom pH790 (fmask pH790) (cmask pH790) (hmask pH790) 1 789 (true, (init pH790), (init pH790))) ∧ ptTest pH790 (runFrom pH790 (fmask pH790) (cmask pH790) (hmask pH790) 1 789 (true, (init pH790), (init pH790))) 790 395 true = true :=
  fin_run (runOK_init (prmOK_of_and H790_fin) true) (by decide) rfl H790_fin ptTest_fst
theorem I790_fin : (prmOK pI790 790 && intTest pI790 (runFrom pI790 (fmask pI790) (cmask pI790) (hmask pI790) 1 789 (true, (init pI790), (init pI790))) 790 17 true) = true := by
  decide +kernel
theorem I790_ok : RunOK pI790 790 (runFrom pI790 (fmask pI790) (cmask pI790) (hmask pI790) 1 789 (true, (init pI790), (init pI790))) ∧ intTest pI790 (runFrom pI790 (fmask pI790) (cmask pI790) (hmask pI790) 1 789 (true, (init pI790), (init pI790))) 790 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I790_fin) true) (by decide) rfl I790_fin intTest_fst
theorem link790 : linkOK pL790 pH790 pI790 = true := by decide +kernel
theorem cvx790 : ConvexBetweenHumps 790 :=
  cvx_of L790_ok H790_ok I790_ok link790 (by decide)
theorem cenlink790 : cenLinkOK pI790 790 = true := by decide +kernel
theorem cen790 : CenterUniqueMin 790 ∧ DipHyp 790 ∧ OnePointHyps 790 :=
  cen_of L790_ok H790_ok I790_ok link790 cenlink790

/-! ### `N = 791` -/

def pL791 : Prm := ⟨75, 35, 37, 793, 11, 18446744073709551616, 207836720500462936, 207836720500462936⟩
def pH791 : Prm := ⟨75, 35, 37, 793, 11, 18446744073709551616, 207838919523718488, 207838919523718488⟩
def pI791 : Prm := ⟨62, 31, 28, 793, 11, 18446744073709551616, 207836720500462936, 207838919523718488⟩
theorem L791_fin : (prmOK pL791 791 && ptTest pL791 (runFrom pL791 (fmask pL791) (cmask pL791) (hmask pL791) 1 790 (true, (init pL791), (init pL791))) 791 396 false) = true := by
  decide +kernel
theorem L791_ok : RunOK pL791 791 (runFrom pL791 (fmask pL791) (cmask pL791) (hmask pL791) 1 790 (true, (init pL791), (init pL791))) ∧ ptTest pL791 (runFrom pL791 (fmask pL791) (cmask pL791) (hmask pL791) 1 790 (true, (init pL791), (init pL791))) 791 396 false = true :=
  fin_run (runOK_init (prmOK_of_and L791_fin) true) (by decide) rfl L791_fin ptTest_fst
theorem H791_fin : (prmOK pH791 791 && ptTest pH791 (runFrom pH791 (fmask pH791) (cmask pH791) (hmask pH791) 1 790 (true, (init pH791), (init pH791))) 791 396 true) = true := by
  decide +kernel
theorem H791_ok : RunOK pH791 791 (runFrom pH791 (fmask pH791) (cmask pH791) (hmask pH791) 1 790 (true, (init pH791), (init pH791))) ∧ ptTest pH791 (runFrom pH791 (fmask pH791) (cmask pH791) (hmask pH791) 1 790 (true, (init pH791), (init pH791))) 791 396 true = true :=
  fin_run (runOK_init (prmOK_of_and H791_fin) true) (by decide) rfl H791_fin ptTest_fst
theorem I791_fin : (prmOK pI791 791 && intTest pI791 (runFrom pI791 (fmask pI791) (cmask pI791) (hmask pI791) 1 790 (true, (init pI791), (init pI791))) 791 17 false) = true := by
  decide +kernel
theorem I791_ok : RunOK pI791 791 (runFrom pI791 (fmask pI791) (cmask pI791) (hmask pI791) 1 790 (true, (init pI791), (init pI791))) ∧ intTest pI791 (runFrom pI791 (fmask pI791) (cmask pI791) (hmask pI791) 1 790 (true, (init pI791), (init pI791))) 791 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I791_fin) true) (by decide) rfl I791_fin intTest_fst
theorem link791 : linkOK pL791 pH791 pI791 = true := by decide +kernel
theorem cvx791 : ConvexBetweenHumps 791 :=
  cvx_of L791_ok H791_ok I791_ok link791 (by decide)

/-! ### `N = 792` -/

def pL792 : Prm := ⟨75, 35, 37, 794, 11, 18446744073709551616, 207629895843004506, 207629895843004506⟩
def pH792 : Prm := ⟨75, 35, 37, 794, 11, 18446744073709551616, 207632094866260058, 207632094866260058⟩
def pI792 : Prm := ⟨62, 31, 28, 794, 11, 18446744073709551616, 207629895843004506, 207632094866260058⟩
theorem L792_fin : (prmOK pL792 792 && ptTest pL792 (runFrom pL792 (fmask pL792) (cmask pL792) (hmask pL792) 1 791 (true, (init pL792), (init pL792))) 792 396 false) = true := by
  decide +kernel
theorem L792_ok : RunOK pL792 792 (runFrom pL792 (fmask pL792) (cmask pL792) (hmask pL792) 1 791 (true, (init pL792), (init pL792))) ∧ ptTest pL792 (runFrom pL792 (fmask pL792) (cmask pL792) (hmask pL792) 1 791 (true, (init pL792), (init pL792))) 792 396 false = true :=
  fin_run (runOK_init (prmOK_of_and L792_fin) true) (by decide) rfl L792_fin ptTest_fst
theorem H792_fin : (prmOK pH792 792 && ptTest pH792 (runFrom pH792 (fmask pH792) (cmask pH792) (hmask pH792) 1 791 (true, (init pH792), (init pH792))) 792 396 true) = true := by
  decide +kernel
theorem H792_ok : RunOK pH792 792 (runFrom pH792 (fmask pH792) (cmask pH792) (hmask pH792) 1 791 (true, (init pH792), (init pH792))) ∧ ptTest pH792 (runFrom pH792 (fmask pH792) (cmask pH792) (hmask pH792) 1 791 (true, (init pH792), (init pH792))) 792 396 true = true :=
  fin_run (runOK_init (prmOK_of_and H792_fin) true) (by decide) rfl H792_fin ptTest_fst
theorem I792_fin : (prmOK pI792 792 && intTest pI792 (runFrom pI792 (fmask pI792) (cmask pI792) (hmask pI792) 1 791 (true, (init pI792), (init pI792))) 792 17 true) = true := by
  decide +kernel
theorem I792_ok : RunOK pI792 792 (runFrom pI792 (fmask pI792) (cmask pI792) (hmask pI792) 1 791 (true, (init pI792), (init pI792))) ∧ intTest pI792 (runFrom pI792 (fmask pI792) (cmask pI792) (hmask pI792) 1 791 (true, (init pI792), (init pI792))) 792 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I792_fin) true) (by decide) rfl I792_fin intTest_fst
theorem link792 : linkOK pL792 pH792 pI792 = true := by decide +kernel
theorem cvx792 : ConvexBetweenHumps 792 :=
  cvx_of L792_ok H792_ok I792_ok link792 (by decide)
theorem cenlink792 : cenLinkOK pI792 792 = true := by decide +kernel
theorem cen792 : CenterUniqueMin 792 ∧ DipHyp 792 ∧ OnePointHyps 792 :=
  cen_of L792_ok H792_ok I792_ok link792 cenlink792

/-! ### `N = 793` -/

def pL793 : Prm := ⟨75, 35, 37, 795, 11, 18446744073709551616, 207423287711472659, 207423287711472659⟩
def pH793 : Prm := ⟨75, 35, 37, 795, 11, 18446744073709551616, 207425486734728211, 207425486734728211⟩
def pI793 : Prm := ⟨62, 31, 28, 795, 11, 18446744073709551616, 207423287711472659, 207425486734728211⟩
theorem L793_fin : (prmOK pL793 793 && ptTest pL793 (runFrom pL793 (fmask pL793) (cmask pL793) (hmask pL793) 1 792 (true, (init pL793), (init pL793))) 793 397 false) = true := by
  decide +kernel
theorem L793_ok : RunOK pL793 793 (runFrom pL793 (fmask pL793) (cmask pL793) (hmask pL793) 1 792 (true, (init pL793), (init pL793))) ∧ ptTest pL793 (runFrom pL793 (fmask pL793) (cmask pL793) (hmask pL793) 1 792 (true, (init pL793), (init pL793))) 793 397 false = true :=
  fin_run (runOK_init (prmOK_of_and L793_fin) true) (by decide) rfl L793_fin ptTest_fst
theorem H793_fin : (prmOK pH793 793 && ptTest pH793 (runFrom pH793 (fmask pH793) (cmask pH793) (hmask pH793) 1 792 (true, (init pH793), (init pH793))) 793 397 true) = true := by
  decide +kernel
theorem H793_ok : RunOK pH793 793 (runFrom pH793 (fmask pH793) (cmask pH793) (hmask pH793) 1 792 (true, (init pH793), (init pH793))) ∧ ptTest pH793 (runFrom pH793 (fmask pH793) (cmask pH793) (hmask pH793) 1 792 (true, (init pH793), (init pH793))) 793 397 true = true :=
  fin_run (runOK_init (prmOK_of_and H793_fin) true) (by decide) rfl H793_fin ptTest_fst
theorem I793_fin : (prmOK pI793 793 && intTest pI793 (runFrom pI793 (fmask pI793) (cmask pI793) (hmask pI793) 1 792 (true, (init pI793), (init pI793))) 793 17 false) = true := by
  decide +kernel
theorem I793_ok : RunOK pI793 793 (runFrom pI793 (fmask pI793) (cmask pI793) (hmask pI793) 1 792 (true, (init pI793), (init pI793))) ∧ intTest pI793 (runFrom pI793 (fmask pI793) (cmask pI793) (hmask pI793) 1 792 (true, (init pI793), (init pI793))) 793 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I793_fin) true) (by decide) rfl I793_fin intTest_fst
theorem link793 : linkOK pL793 pH793 pI793 = true := by decide +kernel
theorem cvx793 : ConvexBetweenHumps 793 :=
  cvx_of L793_ok H793_ok I793_ok link793 (by decide)

/-! ### `N = 794` -/

def pL794 : Prm := ⟨75, 35, 37, 796, 11, 18446744073709551616, 207217364969749888, 207217364969749888⟩
def pH794 : Prm := ⟨75, 35, 37, 796, 11, 18446744073709551616, 207219563993005440, 207219563993005440⟩
def pI794 : Prm := ⟨62, 31, 28, 796, 11, 18446744073709551616, 207217364969749888, 207219563993005440⟩
theorem L794_fin : (prmOK pL794 794 && ptTest pL794 (runFrom pL794 (fmask pL794) (cmask pL794) (hmask pL794) 1 793 (true, (init pL794), (init pL794))) 794 397 false) = true := by
  decide +kernel
theorem L794_ok : RunOK pL794 794 (runFrom pL794 (fmask pL794) (cmask pL794) (hmask pL794) 1 793 (true, (init pL794), (init pL794))) ∧ ptTest pL794 (runFrom pL794 (fmask pL794) (cmask pL794) (hmask pL794) 1 793 (true, (init pL794), (init pL794))) 794 397 false = true :=
  fin_run (runOK_init (prmOK_of_and L794_fin) true) (by decide) rfl L794_fin ptTest_fst
theorem H794_fin : (prmOK pH794 794 && ptTest pH794 (runFrom pH794 (fmask pH794) (cmask pH794) (hmask pH794) 1 793 (true, (init pH794), (init pH794))) 794 397 true) = true := by
  decide +kernel
theorem H794_ok : RunOK pH794 794 (runFrom pH794 (fmask pH794) (cmask pH794) (hmask pH794) 1 793 (true, (init pH794), (init pH794))) ∧ ptTest pH794 (runFrom pH794 (fmask pH794) (cmask pH794) (hmask pH794) 1 793 (true, (init pH794), (init pH794))) 794 397 true = true :=
  fin_run (runOK_init (prmOK_of_and H794_fin) true) (by decide) rfl H794_fin ptTest_fst
theorem I794_fin : (prmOK pI794 794 && intTest pI794 (runFrom pI794 (fmask pI794) (cmask pI794) (hmask pI794) 1 793 (true, (init pI794), (init pI794))) 794 17 true) = true := by
  decide +kernel
theorem I794_ok : RunOK pI794 794 (runFrom pI794 (fmask pI794) (cmask pI794) (hmask pI794) 1 793 (true, (init pI794), (init pI794))) ∧ intTest pI794 (runFrom pI794 (fmask pI794) (cmask pI794) (hmask pI794) 1 793 (true, (init pI794), (init pI794))) 794 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I794_fin) true) (by decide) rfl I794_fin intTest_fst
theorem link794 : linkOK pL794 pH794 pI794 = true := by decide +kernel
theorem cvx794 : ConvexBetweenHumps 794 :=
  cvx_of L794_ok H794_ok I794_ok link794 (by decide)
theorem cenlink794 : cenLinkOK pI794 794 = true := by decide +kernel
theorem cen794 : CenterUniqueMin 794 ∧ DipHyp 794 ∧ OnePointHyps 794 :=
  cen_of L794_ok H794_ok I794_ok link794 cenlink794

/-! ### `N = 795` -/

def pL795 : Prm := ⟨75, 35, 37, 797, 11, 18446744073709551616, 207011657501456670, 207011657501456670⟩
def pH795 : Prm := ⟨75, 35, 37, 797, 11, 18446744073709551616, 207013856524712222, 207013856524712222⟩
def pI795 : Prm := ⟨62, 31, 28, 797, 11, 18446744073709551616, 207011657501456670, 207013856524712222⟩
theorem L795_fin : (prmOK pL795 795 && ptTest pL795 (runFrom pL795 (fmask pL795) (cmask pL795) (hmask pL795) 1 794 (true, (init pL795), (init pL795))) 795 398 false) = true := by
  decide +kernel
theorem L795_ok : RunOK pL795 795 (runFrom pL795 (fmask pL795) (cmask pL795) (hmask pL795) 1 794 (true, (init pL795), (init pL795))) ∧ ptTest pL795 (runFrom pL795 (fmask pL795) (cmask pL795) (hmask pL795) 1 794 (true, (init pL795), (init pL795))) 795 398 false = true :=
  fin_run (runOK_init (prmOK_of_and L795_fin) true) (by decide) rfl L795_fin ptTest_fst
theorem H795_fin : (prmOK pH795 795 && ptTest pH795 (runFrom pH795 (fmask pH795) (cmask pH795) (hmask pH795) 1 794 (true, (init pH795), (init pH795))) 795 398 true) = true := by
  decide +kernel
theorem H795_ok : RunOK pH795 795 (runFrom pH795 (fmask pH795) (cmask pH795) (hmask pH795) 1 794 (true, (init pH795), (init pH795))) ∧ ptTest pH795 (runFrom pH795 (fmask pH795) (cmask pH795) (hmask pH795) 1 794 (true, (init pH795), (init pH795))) 795 398 true = true :=
  fin_run (runOK_init (prmOK_of_and H795_fin) true) (by decide) rfl H795_fin ptTest_fst
theorem I795_fin : (prmOK pI795 795 && intTest pI795 (runFrom pI795 (fmask pI795) (cmask pI795) (hmask pI795) 1 794 (true, (init pI795), (init pI795))) 795 17 false) = true := by
  decide +kernel
theorem I795_ok : RunOK pI795 795 (runFrom pI795 (fmask pI795) (cmask pI795) (hmask pI795) 1 794 (true, (init pI795), (init pI795))) ∧ intTest pI795 (runFrom pI795 (fmask pI795) (cmask pI795) (hmask pI795) 1 794 (true, (init pI795), (init pI795))) 795 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I795_fin) true) (by decide) rfl I795_fin intTest_fst
theorem link795 : linkOK pL795 pH795 pI795 = true := by decide +kernel
theorem cvx795 : ConvexBetweenHumps 795 :=
  cvx_of L795_ok H795_ok I795_ok link795 (by decide)

/-! ### `N = 796` -/

def pL796 : Prm := ⟨75, 35, 37, 798, 11, 18446744073709551616, 206806630576625478, 206806630576625478⟩
def pH796 : Prm := ⟨75, 35, 37, 798, 11, 18446744073709551616, 206808829599881030, 206808829599881030⟩
def pI796 : Prm := ⟨62, 31, 28, 798, 11, 18446744073709551616, 206806630576625478, 206808829599881030⟩
theorem L796_fin : (prmOK pL796 796 && ptTest pL796 (runFrom pL796 (fmask pL796) (cmask pL796) (hmask pL796) 1 795 (true, (init pL796), (init pL796))) 796 398 false) = true := by
  decide +kernel
theorem L796_ok : RunOK pL796 796 (runFrom pL796 (fmask pL796) (cmask pL796) (hmask pL796) 1 795 (true, (init pL796), (init pL796))) ∧ ptTest pL796 (runFrom pL796 (fmask pL796) (cmask pL796) (hmask pL796) 1 795 (true, (init pL796), (init pL796))) 796 398 false = true :=
  fin_run (runOK_init (prmOK_of_and L796_fin) true) (by decide) rfl L796_fin ptTest_fst
theorem H796_fin : (prmOK pH796 796 && ptTest pH796 (runFrom pH796 (fmask pH796) (cmask pH796) (hmask pH796) 1 795 (true, (init pH796), (init pH796))) 796 398 true) = true := by
  decide +kernel
theorem H796_ok : RunOK pH796 796 (runFrom pH796 (fmask pH796) (cmask pH796) (hmask pH796) 1 795 (true, (init pH796), (init pH796))) ∧ ptTest pH796 (runFrom pH796 (fmask pH796) (cmask pH796) (hmask pH796) 1 795 (true, (init pH796), (init pH796))) 796 398 true = true :=
  fin_run (runOK_init (prmOK_of_and H796_fin) true) (by decide) rfl H796_fin ptTest_fst
theorem I796_fin : (prmOK pI796 796 && intTest pI796 (runFrom pI796 (fmask pI796) (cmask pI796) (hmask pI796) 1 795 (true, (init pI796), (init pI796))) 796 17 true) = true := by
  decide +kernel
theorem I796_ok : RunOK pI796 796 (runFrom pI796 (fmask pI796) (cmask pI796) (hmask pI796) 1 795 (true, (init pI796), (init pI796))) ∧ intTest pI796 (runFrom pI796 (fmask pI796) (cmask pI796) (hmask pI796) 1 795 (true, (init pI796), (init pI796))) 796 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I796_fin) true) (by decide) rfl I796_fin intTest_fst
theorem link796 : linkOK pL796 pH796 pI796 = true := by decide +kernel
theorem cvx796 : ConvexBetweenHumps 796 :=
  cvx_of L796_ok H796_ok I796_ok link796 (by decide)
theorem cenlink796 : cenLinkOK pI796 796 = true := by decide +kernel
theorem cen796 : CenterUniqueMin 796 ∧ DipHyp 796 ∧ OnePointHyps 796 :=
  cen_of L796_ok H796_ok I796_ok link796 cenlink796

/-! ### `N = 797` -/

def pL797 : Prm := ⟨75, 35, 37, 799, 11, 18446744073709551616, 206601817682503585, 206601817682503585⟩
def pH797 : Prm := ⟨75, 35, 37, 799, 11, 18446744073709551616, 206604016705759137, 206604016705759137⟩
def pI797 : Prm := ⟨62, 31, 28, 799, 11, 18446744073709551616, 206601817682503585, 206604016705759137⟩
theorem L797_fin : (prmOK pL797 797 && ptTest pL797 (runFrom pL797 (fmask pL797) (cmask pL797) (hmask pL797) 1 796 (true, (init pL797), (init pL797))) 797 399 false) = true := by
  decide +kernel
theorem L797_ok : RunOK pL797 797 (runFrom pL797 (fmask pL797) (cmask pL797) (hmask pL797) 1 796 (true, (init pL797), (init pL797))) ∧ ptTest pL797 (runFrom pL797 (fmask pL797) (cmask pL797) (hmask pL797) 1 796 (true, (init pL797), (init pL797))) 797 399 false = true :=
  fin_run (runOK_init (prmOK_of_and L797_fin) true) (by decide) rfl L797_fin ptTest_fst
theorem H797_fin : (prmOK pH797 797 && ptTest pH797 (runFrom pH797 (fmask pH797) (cmask pH797) (hmask pH797) 1 796 (true, (init pH797), (init pH797))) 797 399 true) = true := by
  decide +kernel
theorem H797_ok : RunOK pH797 797 (runFrom pH797 (fmask pH797) (cmask pH797) (hmask pH797) 1 796 (true, (init pH797), (init pH797))) ∧ ptTest pH797 (runFrom pH797 (fmask pH797) (cmask pH797) (hmask pH797) 1 796 (true, (init pH797), (init pH797))) 797 399 true = true :=
  fin_run (runOK_init (prmOK_of_and H797_fin) true) (by decide) rfl H797_fin ptTest_fst
theorem I797_fin : (prmOK pI797 797 && intTest pI797 (runFrom pI797 (fmask pI797) (cmask pI797) (hmask pI797) 1 796 (true, (init pI797), (init pI797))) 797 17 false) = true := by
  decide +kernel
theorem I797_ok : RunOK pI797 797 (runFrom pI797 (fmask pI797) (cmask pI797) (hmask pI797) 1 796 (true, (init pI797), (init pI797))) ∧ intTest pI797 (runFrom pI797 (fmask pI797) (cmask pI797) (hmask pI797) 1 796 (true, (init pI797), (init pI797))) 797 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I797_fin) true) (by decide) rfl I797_fin intTest_fst
theorem link797 : linkOK pL797 pH797 pI797 = true := by decide +kernel
theorem cvx797 : ConvexBetweenHumps 797 :=
  cvx_of L797_ok H797_ok I797_ok link797 (by decide)

/-! ### `N = 798` -/

def pL798 : Prm := ⟨75, 35, 37, 800, 11, 18446744073709551616, 206397680531668869, 206397680531668869⟩
def pH798 : Prm := ⟨75, 35, 37, 800, 11, 18446744073709551616, 206399879554924421, 206399879554924421⟩
def pI798 : Prm := ⟨62, 31, 28, 800, 11, 18446744073709551616, 206397680531668869, 206399879554924421⟩
theorem L798_fin : (prmOK pL798 798 && ptTest pL798 (runFrom pL798 (fmask pL798) (cmask pL798) (hmask pL798) 1 797 (true, (init pL798), (init pL798))) 798 399 false) = true := by
  decide +kernel
theorem L798_ok : RunOK pL798 798 (runFrom pL798 (fmask pL798) (cmask pL798) (hmask pL798) 1 797 (true, (init pL798), (init pL798))) ∧ ptTest pL798 (runFrom pL798 (fmask pL798) (cmask pL798) (hmask pL798) 1 797 (true, (init pL798), (init pL798))) 798 399 false = true :=
  fin_run (runOK_init (prmOK_of_and L798_fin) true) (by decide) rfl L798_fin ptTest_fst
theorem H798_fin : (prmOK pH798 798 && ptTest pH798 (runFrom pH798 (fmask pH798) (cmask pH798) (hmask pH798) 1 797 (true, (init pH798), (init pH798))) 798 399 true) = true := by
  decide +kernel
theorem H798_ok : RunOK pH798 798 (runFrom pH798 (fmask pH798) (cmask pH798) (hmask pH798) 1 797 (true, (init pH798), (init pH798))) ∧ ptTest pH798 (runFrom pH798 (fmask pH798) (cmask pH798) (hmask pH798) 1 797 (true, (init pH798), (init pH798))) 798 399 true = true :=
  fin_run (runOK_init (prmOK_of_and H798_fin) true) (by decide) rfl H798_fin ptTest_fst
theorem I798_fin : (prmOK pI798 798 && intTest pI798 (runFrom pI798 (fmask pI798) (cmask pI798) (hmask pI798) 1 797 (true, (init pI798), (init pI798))) 798 17 true) = true := by
  decide +kernel
theorem I798_ok : RunOK pI798 798 (runFrom pI798 (fmask pI798) (cmask pI798) (hmask pI798) 1 797 (true, (init pI798), (init pI798))) ∧ intTest pI798 (runFrom pI798 (fmask pI798) (cmask pI798) (hmask pI798) 1 797 (true, (init pI798), (init pI798))) 798 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I798_fin) true) (by decide) rfl I798_fin intTest_fst
theorem link798 : linkOK pL798 pH798 pI798 = true := by decide +kernel
theorem cvx798 : ConvexBetweenHumps 798 :=
  cvx_of L798_ok H798_ok I798_ok link798 (by decide)
theorem cenlink798 : cenLinkOK pI798 798 = true := by decide +kernel
theorem cen798 : CenterUniqueMin 798 ∧ DipHyp 798 ∧ OnePointHyps 798 :=
  cen_of L798_ok H798_ok I798_ok link798 cenlink798

/-! ### `N = 799` -/

def pL799 : Prm := ⟨73, 34, 36, 801, 11, 18446744073709551616, 206192656666806175, 206192656666806175⟩
def pH799 : Prm := ⟨73, 34, 36, 801, 11, 18446744073709551616, 206197054713317279, 206197054713317279⟩
def pI799 : Prm := ⟨63, 31, 29, 801, 11, 18446744073709551616, 206192656666806175, 206197054713317279⟩
theorem L799_fin : (prmOK pL799 799 && ptTest pL799 (runFrom pL799 (fmask pL799) (cmask pL799) (hmask pL799) 1 798 (true, (init pL799), (init pL799))) 799 400 false) = true := by
  decide +kernel
theorem L799_ok : RunOK pL799 799 (runFrom pL799 (fmask pL799) (cmask pL799) (hmask pL799) 1 798 (true, (init pL799), (init pL799))) ∧ ptTest pL799 (runFrom pL799 (fmask pL799) (cmask pL799) (hmask pL799) 1 798 (true, (init pL799), (init pL799))) 799 400 false = true :=
  fin_run (runOK_init (prmOK_of_and L799_fin) true) (by decide) rfl L799_fin ptTest_fst
theorem H799_fin : (prmOK pH799 799 && ptTest pH799 (runFrom pH799 (fmask pH799) (cmask pH799) (hmask pH799) 1 798 (true, (init pH799), (init pH799))) 799 400 true) = true := by
  decide +kernel
theorem H799_ok : RunOK pH799 799 (runFrom pH799 (fmask pH799) (cmask pH799) (hmask pH799) 1 798 (true, (init pH799), (init pH799))) ∧ ptTest pH799 (runFrom pH799 (fmask pH799) (cmask pH799) (hmask pH799) 1 798 (true, (init pH799), (init pH799))) 799 400 true = true :=
  fin_run (runOK_init (prmOK_of_and H799_fin) true) (by decide) rfl H799_fin ptTest_fst
theorem I799_fin : (prmOK pI799 799 && intTest pI799 (runFrom pI799 (fmask pI799) (cmask pI799) (hmask pI799) 1 798 (true, (init pI799), (init pI799))) 799 17 false) = true := by
  decide +kernel
theorem I799_ok : RunOK pI799 799 (runFrom pI799 (fmask pI799) (cmask pI799) (hmask pI799) 1 798 (true, (init pI799), (init pI799))) ∧ intTest pI799 (runFrom pI799 (fmask pI799) (cmask pI799) (hmask pI799) 1 798 (true, (init pI799), (init pI799))) 799 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I799_fin) true) (by decide) rfl I799_fin intTest_fst
theorem link799 : linkOK pL799 pH799 pI799 = true := by decide +kernel
theorem cvx799 : ConvexBetweenHumps 799 :=
  cvx_of L799_ok H799_ok I799_ok link799 (by decide)

/-! ### `N = 800` -/

def pL800 : Prm := ⟨73, 34, 36, 802, 11, 18446744073709551616, 205989403302376169, 205989403302376169⟩
def pH800 : Prm := ⟨73, 34, 36, 802, 11, 18446744073709551616, 205993801348887273, 205993801348887273⟩
def pI800 : Prm := ⟨63, 31, 29, 802, 11, 18446744073709551616, 205989403302376169, 205993801348887273⟩
theorem L800_fin : (prmOK pL800 800 && ptTest pL800 (runFrom pL800 (fmask pL800) (cmask pL800) (hmask pL800) 1 799 (true, (init pL800), (init pL800))) 800 400 false) = true := by
  decide +kernel
theorem L800_ok : RunOK pL800 800 (runFrom pL800 (fmask pL800) (cmask pL800) (hmask pL800) 1 799 (true, (init pL800), (init pL800))) ∧ ptTest pL800 (runFrom pL800 (fmask pL800) (cmask pL800) (hmask pL800) 1 799 (true, (init pL800), (init pL800))) 800 400 false = true :=
  fin_run (runOK_init (prmOK_of_and L800_fin) true) (by decide) rfl L800_fin ptTest_fst
theorem H800_fin : (prmOK pH800 800 && ptTest pH800 (runFrom pH800 (fmask pH800) (cmask pH800) (hmask pH800) 1 799 (true, (init pH800), (init pH800))) 800 400 true) = true := by
  decide +kernel
theorem H800_ok : RunOK pH800 800 (runFrom pH800 (fmask pH800) (cmask pH800) (hmask pH800) 1 799 (true, (init pH800), (init pH800))) ∧ ptTest pH800 (runFrom pH800 (fmask pH800) (cmask pH800) (hmask pH800) 1 799 (true, (init pH800), (init pH800))) 800 400 true = true :=
  fin_run (runOK_init (prmOK_of_and H800_fin) true) (by decide) rfl H800_fin ptTest_fst
theorem I800_fin : (prmOK pI800 800 && intTest pI800 (runFrom pI800 (fmask pI800) (cmask pI800) (hmask pI800) 1 799 (true, (init pI800), (init pI800))) 800 17 true) = true := by
  decide +kernel
theorem I800_ok : RunOK pI800 800 (runFrom pI800 (fmask pI800) (cmask pI800) (hmask pI800) 1 799 (true, (init pI800), (init pI800))) ∧ intTest pI800 (runFrom pI800 (fmask pI800) (cmask pI800) (hmask pI800) 1 799 (true, (init pI800), (init pI800))) 800 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I800_fin) true) (by decide) rfl I800_fin intTest_fst
theorem link800 : linkOK pL800 pH800 pI800 = true := by decide +kernel
theorem cvx800 : ConvexBetweenHumps 800 :=
  cvx_of L800_ok H800_ok I800_ok link800 (by decide)
theorem cenlink800 : cenLinkOK pI800 800 = true := by decide +kernel
theorem cen800 : CenterUniqueMin 800 ∧ DipHyp 800 ∧ OnePointHyps 800 :=
  cen_of L800_ok H800_ok I800_ok link800 cenlink800

/-! ### `N = 801` -/

def pL801 : Prm := ⟨73, 34, 36, 803, 11, 18446744073709551616, 205786361511954980, 205786361511954980⟩
def pH801 : Prm := ⟨73, 34, 36, 803, 11, 18446744073709551616, 205790759558466084, 205790759558466084⟩
def pI801 : Prm := ⟨63, 31, 29, 803, 11, 18446744073709551616, 205786361511954980, 205790759558466084⟩
theorem L801_fin : (prmOK pL801 801 && ptTest pL801 (runFrom pL801 (fmask pL801) (cmask pL801) (hmask pL801) 1 800 (true, (init pL801), (init pL801))) 801 401 false) = true := by
  decide +kernel
theorem L801_ok : RunOK pL801 801 (runFrom pL801 (fmask pL801) (cmask pL801) (hmask pL801) 1 800 (true, (init pL801), (init pL801))) ∧ ptTest pL801 (runFrom pL801 (fmask pL801) (cmask pL801) (hmask pL801) 1 800 (true, (init pL801), (init pL801))) 801 401 false = true :=
  fin_run (runOK_init (prmOK_of_and L801_fin) true) (by decide) rfl L801_fin ptTest_fst
theorem H801_fin : (prmOK pH801 801 && ptTest pH801 (runFrom pH801 (fmask pH801) (cmask pH801) (hmask pH801) 1 800 (true, (init pH801), (init pH801))) 801 401 true) = true := by
  decide +kernel
theorem H801_ok : RunOK pH801 801 (runFrom pH801 (fmask pH801) (cmask pH801) (hmask pH801) 1 800 (true, (init pH801), (init pH801))) ∧ ptTest pH801 (runFrom pH801 (fmask pH801) (cmask pH801) (hmask pH801) 1 800 (true, (init pH801), (init pH801))) 801 401 true = true :=
  fin_run (runOK_init (prmOK_of_and H801_fin) true) (by decide) rfl H801_fin ptTest_fst
theorem I801_fin : (prmOK pI801 801 && intTest pI801 (runFrom pI801 (fmask pI801) (cmask pI801) (hmask pI801) 1 800 (true, (init pI801), (init pI801))) 801 17 false) = true := by
  decide +kernel
theorem I801_ok : RunOK pI801 801 (runFrom pI801 (fmask pI801) (cmask pI801) (hmask pI801) 1 800 (true, (init pI801), (init pI801))) ∧ intTest pI801 (runFrom pI801 (fmask pI801) (cmask pI801) (hmask pI801) 1 800 (true, (init pI801), (init pI801))) 801 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I801_fin) true) (by decide) rfl I801_fin intTest_fst
theorem link801 : linkOK pL801 pH801 pI801 = true := by decide +kernel
theorem cvx801 : ConvexBetweenHumps 801 :=
  cvx_of L801_ok H801_ok I801_ok link801 (by decide)

/-! ### `N = 802` -/

def pL802 : Prm := ⟨73, 34, 36, 804, 11, 18446744073709551616, 205583986000958728, 205583986000958728⟩
def pH802 : Prm := ⟨73, 34, 36, 804, 11, 18446744073709551616, 205588384047469832, 205588384047469832⟩
def pI802 : Prm := ⟨63, 31, 29, 804, 11, 18446744073709551616, 205583986000958728, 205588384047469832⟩
theorem L802_fin : (prmOK pL802 802 && ptTest pL802 (runFrom pL802 (fmask pL802) (cmask pL802) (hmask pL802) 1 801 (true, (init pL802), (init pL802))) 802 401 false) = true := by
  decide +kernel
theorem L802_ok : RunOK pL802 802 (runFrom pL802 (fmask pL802) (cmask pL802) (hmask pL802) 1 801 (true, (init pL802), (init pL802))) ∧ ptTest pL802 (runFrom pL802 (fmask pL802) (cmask pL802) (hmask pL802) 1 801 (true, (init pL802), (init pL802))) 802 401 false = true :=
  fin_run (runOK_init (prmOK_of_and L802_fin) true) (by decide) rfl L802_fin ptTest_fst
theorem H802_fin : (prmOK pH802 802 && ptTest pH802 (runFrom pH802 (fmask pH802) (cmask pH802) (hmask pH802) 1 801 (true, (init pH802), (init pH802))) 802 401 true) = true := by
  decide +kernel
theorem H802_ok : RunOK pH802 802 (runFrom pH802 (fmask pH802) (cmask pH802) (hmask pH802) 1 801 (true, (init pH802), (init pH802))) ∧ ptTest pH802 (runFrom pH802 (fmask pH802) (cmask pH802) (hmask pH802) 1 801 (true, (init pH802), (init pH802))) 802 401 true = true :=
  fin_run (runOK_init (prmOK_of_and H802_fin) true) (by decide) rfl H802_fin ptTest_fst
theorem I802_fin : (prmOK pI802 802 && intTest pI802 (runFrom pI802 (fmask pI802) (cmask pI802) (hmask pI802) 1 801 (true, (init pI802), (init pI802))) 802 17 true) = true := by
  decide +kernel
theorem I802_ok : RunOK pI802 802 (runFrom pI802 (fmask pI802) (cmask pI802) (hmask pI802) 1 801 (true, (init pI802), (init pI802))) ∧ intTest pI802 (runFrom pI802 (fmask pI802) (cmask pI802) (hmask pI802) 1 801 (true, (init pI802), (init pI802))) 802 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I802_fin) true) (by decide) rfl I802_fin intTest_fst
theorem link802 : linkOK pL802 pH802 pI802 = true := by decide +kernel
theorem cvx802 : ConvexBetweenHumps 802 :=
  cvx_of L802_ok H802_ok I802_ok link802 (by decide)
theorem cenlink802 : cenLinkOK pI802 802 = true := by decide +kernel
theorem cen802 : CenterUniqueMin 802 ∧ DipHyp 802 ∧ OnePointHyps 802 :=
  cen_of L802_ok H802_ok I802_ok link802 cenlink802

/-! ### `N = 803` -/

def pL803 : Prm := ⟨73, 34, 36, 805, 11, 18446744073709551616, 205381820849843492, 205381820849843492⟩
def pH803 : Prm := ⟨73, 34, 36, 805, 11, 18446744073709551616, 205386218896354596, 205386218896354596⟩
def pI803 : Prm := ⟨63, 31, 29, 805, 11, 18446744073709551616, 205381820849843492, 205386218896354596⟩
theorem L803_fin : (prmOK pL803 803 && ptTest pL803 (runFrom pL803 (fmask pL803) (cmask pL803) (hmask pL803) 1 802 (true, (init pL803), (init pL803))) 803 402 false) = true := by
  decide +kernel
theorem L803_ok : RunOK pL803 803 (runFrom pL803 (fmask pL803) (cmask pL803) (hmask pL803) 1 802 (true, (init pL803), (init pL803))) ∧ ptTest pL803 (runFrom pL803 (fmask pL803) (cmask pL803) (hmask pL803) 1 802 (true, (init pL803), (init pL803))) 803 402 false = true :=
  fin_run (runOK_init (prmOK_of_and L803_fin) true) (by decide) rfl L803_fin ptTest_fst
theorem H803_fin : (prmOK pH803 803 && ptTest pH803 (runFrom pH803 (fmask pH803) (cmask pH803) (hmask pH803) 1 802 (true, (init pH803), (init pH803))) 803 402 true) = true := by
  decide +kernel
theorem H803_ok : RunOK pH803 803 (runFrom pH803 (fmask pH803) (cmask pH803) (hmask pH803) 1 802 (true, (init pH803), (init pH803))) ∧ ptTest pH803 (runFrom pH803 (fmask pH803) (cmask pH803) (hmask pH803) 1 802 (true, (init pH803), (init pH803))) 803 402 true = true :=
  fin_run (runOK_init (prmOK_of_and H803_fin) true) (by decide) rfl H803_fin ptTest_fst
theorem I803_fin : (prmOK pI803 803 && intTest pI803 (runFrom pI803 (fmask pI803) (cmask pI803) (hmask pI803) 1 802 (true, (init pI803), (init pI803))) 803 17 false) = true := by
  decide +kernel
theorem I803_ok : RunOK pI803 803 (runFrom pI803 (fmask pI803) (cmask pI803) (hmask pI803) 1 802 (true, (init pI803), (init pI803))) ∧ intTest pI803 (runFrom pI803 (fmask pI803) (cmask pI803) (hmask pI803) 1 802 (true, (init pI803), (init pI803))) 803 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I803_fin) true) (by decide) rfl I803_fin intTest_fst
theorem link803 : linkOK pL803 pH803 pI803 = true := by decide +kernel
theorem cvx803 : ConvexBetweenHumps 803 :=
  cvx_of L803_ok H803_ok I803_ok link803 (by decide)

/-! ### `N = 804` -/

def pL804 : Prm := ⟨73, 34, 36, 806, 11, 18446744073709551616, 205180317313322104, 205180317313322104⟩
def pH804 : Prm := ⟨73, 34, 36, 806, 11, 18446744073709551616, 205184715359833208, 205184715359833208⟩
def pI804 : Prm := ⟨63, 31, 29, 806, 11, 18446744073709551616, 205180317313322104, 205184715359833208⟩
theorem L804_fin : (prmOK pL804 804 && ptTest pL804 (runFrom pL804 (fmask pL804) (cmask pL804) (hmask pL804) 1 803 (true, (init pL804), (init pL804))) 804 402 false) = true := by
  decide +kernel
theorem L804_ok : RunOK pL804 804 (runFrom pL804 (fmask pL804) (cmask pL804) (hmask pL804) 1 803 (true, (init pL804), (init pL804))) ∧ ptTest pL804 (runFrom pL804 (fmask pL804) (cmask pL804) (hmask pL804) 1 803 (true, (init pL804), (init pL804))) 804 402 false = true :=
  fin_run (runOK_init (prmOK_of_and L804_fin) true) (by decide) rfl L804_fin ptTest_fst
theorem H804_fin : (prmOK pH804 804 && ptTest pH804 (runFrom pH804 (fmask pH804) (cmask pH804) (hmask pH804) 1 803 (true, (init pH804), (init pH804))) 804 402 true) = true := by
  decide +kernel
theorem H804_ok : RunOK pH804 804 (runFrom pH804 (fmask pH804) (cmask pH804) (hmask pH804) 1 803 (true, (init pH804), (init pH804))) ∧ ptTest pH804 (runFrom pH804 (fmask pH804) (cmask pH804) (hmask pH804) 1 803 (true, (init pH804), (init pH804))) 804 402 true = true :=
  fin_run (runOK_init (prmOK_of_and H804_fin) true) (by decide) rfl H804_fin ptTest_fst
theorem I804_fin : (prmOK pI804 804 && intTest pI804 (runFrom pI804 (fmask pI804) (cmask pI804) (hmask pI804) 1 803 (true, (init pI804), (init pI804))) 804 17 true) = true := by
  decide +kernel
theorem I804_ok : RunOK pI804 804 (runFrom pI804 (fmask pI804) (cmask pI804) (hmask pI804) 1 803 (true, (init pI804), (init pI804))) ∧ intTest pI804 (runFrom pI804 (fmask pI804) (cmask pI804) (hmask pI804) 1 803 (true, (init pI804), (init pI804))) 804 17 true = true :=
  fin_run (runOK_init (prmOK_of_and I804_fin) true) (by decide) rfl I804_fin intTest_fst
theorem link804 : linkOK pL804 pH804 pI804 = true := by decide +kernel
theorem cvx804 : ConvexBetweenHumps 804 :=
  cvx_of L804_ok H804_ok I804_ok link804 (by decide)
theorem cenlink804 : cenLinkOK pI804 804 = true := by decide +kernel
theorem cen804 : CenterUniqueMin 804 ∧ DipHyp 804 ∧ OnePointHyps 804 :=
  cen_of L804_ok H804_ok I804_ok link804 cenlink804

/-! ### `N = 805` -/

def pL805 : Prm := ⟨73, 34, 36, 807, 11, 18446744073709551616, 204979022931887983, 204979022931887983⟩
def pH805 : Prm := ⟨73, 34, 36, 807, 11, 18446744073709551616, 204983420978399087, 204983420978399087⟩
def pI805 : Prm := ⟨63, 31, 29, 807, 11, 18446744073709551616, 204979022931887983, 204983420978399087⟩
theorem L805_fin : (prmOK pL805 805 && ptTest pL805 (runFrom pL805 (fmask pL805) (cmask pL805) (hmask pL805) 1 804 (true, (init pL805), (init pL805))) 805 403 false) = true := by
  decide +kernel
theorem L805_ok : RunOK pL805 805 (runFrom pL805 (fmask pL805) (cmask pL805) (hmask pL805) 1 804 (true, (init pL805), (init pL805))) ∧ ptTest pL805 (runFrom pL805 (fmask pL805) (cmask pL805) (hmask pL805) 1 804 (true, (init pL805), (init pL805))) 805 403 false = true :=
  fin_run (runOK_init (prmOK_of_and L805_fin) true) (by decide) rfl L805_fin ptTest_fst
theorem H805_fin : (prmOK pH805 805 && ptTest pH805 (runFrom pH805 (fmask pH805) (cmask pH805) (hmask pH805) 1 804 (true, (init pH805), (init pH805))) 805 403 true) = true := by
  decide +kernel
theorem H805_ok : RunOK pH805 805 (runFrom pH805 (fmask pH805) (cmask pH805) (hmask pH805) 1 804 (true, (init pH805), (init pH805))) ∧ ptTest pH805 (runFrom pH805 (fmask pH805) (cmask pH805) (hmask pH805) 1 804 (true, (init pH805), (init pH805))) 805 403 true = true :=
  fin_run (runOK_init (prmOK_of_and H805_fin) true) (by decide) rfl H805_fin ptTest_fst
theorem I805_fin : (prmOK pI805 805 && intTest pI805 (runFrom pI805 (fmask pI805) (cmask pI805) (hmask pI805) 1 804 (true, (init pI805), (init pI805))) 805 17 false) = true := by
  decide +kernel
theorem I805_ok : RunOK pI805 805 (runFrom pI805 (fmask pI805) (cmask pI805) (hmask pI805) 1 804 (true, (init pI805), (init pI805))) ∧ intTest pI805 (runFrom pI805 (fmask pI805) (cmask pI805) (hmask pI805) 1 804 (true, (init pI805), (init pI805))) 805 17 false = true :=
  fin_run (runOK_init (prmOK_of_and I805_fin) true) (by decide) rfl I805_fin intTest_fst
theorem link805 : linkOK pL805 pH805 pI805 = true := by decide +kernel
theorem cvx805 : ConvexBetweenHumps 805 :=
  cvx_of L805_ok H805_ok I805_ok link805 (by decide)

/-! ### The range -/

theorem cvx_733_805 {N : ℕ} (h1 : 733 ≤ N) (h2 : N ≤ 805) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 768
  · by_cases h4 : N ≤ 750
    · by_cases h6 : N ≤ 741
      · by_cases h8 : N ≤ 736
        · by_cases h10 : N ≤ 734
          · by_cases h12 : N ≤ 733
            · obtain rfl : N = 733 := by omega
              exact cvx733
            · obtain rfl : N = 734 := by omega
              exact cvx734
          · by_cases h12 : N ≤ 735
            · obtain rfl : N = 735 := by omega
              exact cvx735
            · obtain rfl : N = 736 := by omega
              exact cvx736
        · by_cases h10 : N ≤ 738
          · by_cases h12 : N ≤ 737
            · obtain rfl : N = 737 := by omega
              exact cvx737
            · obtain rfl : N = 738 := by omega
              exact cvx738
          · by_cases h12 : N ≤ 739
            · obtain rfl : N = 739 := by omega
              exact cvx739
            · by_cases h14 : N ≤ 740
              · obtain rfl : N = 740 := by omega
                exact cvx740
              · obtain rfl : N = 741 := by omega
                exact cvx741
      · by_cases h8 : N ≤ 745
        · by_cases h10 : N ≤ 743
          · by_cases h12 : N ≤ 742
            · obtain rfl : N = 742 := by omega
              exact cvx742
            · obtain rfl : N = 743 := by omega
              exact cvx743
          · by_cases h12 : N ≤ 744
            · obtain rfl : N = 744 := by omega
              exact cvx744
            · obtain rfl : N = 745 := by omega
              exact cvx745
        · by_cases h10 : N ≤ 747
          · by_cases h12 : N ≤ 746
            · obtain rfl : N = 746 := by omega
              exact cvx746
            · obtain rfl : N = 747 := by omega
              exact cvx747
          · by_cases h12 : N ≤ 748
            · obtain rfl : N = 748 := by omega
              exact cvx748
            · by_cases h14 : N ≤ 749
              · obtain rfl : N = 749 := by omega
                exact cvx749
              · obtain rfl : N = 750 := by omega
                exact cvx750
    · by_cases h6 : N ≤ 759
      · by_cases h8 : N ≤ 754
        · by_cases h10 : N ≤ 752
          · by_cases h12 : N ≤ 751
            · obtain rfl : N = 751 := by omega
              exact cvx751
            · obtain rfl : N = 752 := by omega
              exact cvx752
          · by_cases h12 : N ≤ 753
            · obtain rfl : N = 753 := by omega
              exact cvx753
            · obtain rfl : N = 754 := by omega
              exact cvx754
        · by_cases h10 : N ≤ 756
          · by_cases h12 : N ≤ 755
            · obtain rfl : N = 755 := by omega
              exact cvx755
            · obtain rfl : N = 756 := by omega
              exact cvx756
          · by_cases h12 : N ≤ 757
            · obtain rfl : N = 757 := by omega
              exact cvx757
            · by_cases h14 : N ≤ 758
              · obtain rfl : N = 758 := by omega
                exact cvx758
              · obtain rfl : N = 759 := by omega
                exact cvx759
      · by_cases h8 : N ≤ 763
        · by_cases h10 : N ≤ 761
          · by_cases h12 : N ≤ 760
            · obtain rfl : N = 760 := by omega
              exact cvx760
            · obtain rfl : N = 761 := by omega
              exact cvx761
          · by_cases h12 : N ≤ 762
            · obtain rfl : N = 762 := by omega
              exact cvx762
            · obtain rfl : N = 763 := by omega
              exact cvx763
        · by_cases h10 : N ≤ 765
          · by_cases h12 : N ≤ 764
            · obtain rfl : N = 764 := by omega
              exact cvx764
            · obtain rfl : N = 765 := by omega
              exact cvx765
          · by_cases h12 : N ≤ 766
            · obtain rfl : N = 766 := by omega
              exact cvx766
            · by_cases h14 : N ≤ 767
              · obtain rfl : N = 767 := by omega
                exact cvx767
              · obtain rfl : N = 768 := by omega
                exact cvx768
  · by_cases h4 : N ≤ 786
    · by_cases h6 : N ≤ 777
      · by_cases h8 : N ≤ 772
        · by_cases h10 : N ≤ 770
          · by_cases h12 : N ≤ 769
            · obtain rfl : N = 769 := by omega
              exact cvx769
            · obtain rfl : N = 770 := by omega
              exact cvx770
          · by_cases h12 : N ≤ 771
            · obtain rfl : N = 771 := by omega
              exact cvx771
            · obtain rfl : N = 772 := by omega
              exact cvx772
        · by_cases h10 : N ≤ 774
          · by_cases h12 : N ≤ 773
            · obtain rfl : N = 773 := by omega
              exact cvx773
            · obtain rfl : N = 774 := by omega
              exact cvx774
          · by_cases h12 : N ≤ 775
            · obtain rfl : N = 775 := by omega
              exact cvx775
            · by_cases h14 : N ≤ 776
              · obtain rfl : N = 776 := by omega
                exact cvx776
              · obtain rfl : N = 777 := by omega
                exact cvx777
      · by_cases h8 : N ≤ 781
        · by_cases h10 : N ≤ 779
          · by_cases h12 : N ≤ 778
            · obtain rfl : N = 778 := by omega
              exact cvx778
            · obtain rfl : N = 779 := by omega
              exact cvx779
          · by_cases h12 : N ≤ 780
            · obtain rfl : N = 780 := by omega
              exact cvx780
            · obtain rfl : N = 781 := by omega
              exact cvx781
        · by_cases h10 : N ≤ 783
          · by_cases h12 : N ≤ 782
            · obtain rfl : N = 782 := by omega
              exact cvx782
            · obtain rfl : N = 783 := by omega
              exact cvx783
          · by_cases h12 : N ≤ 784
            · obtain rfl : N = 784 := by omega
              exact cvx784
            · by_cases h14 : N ≤ 785
              · obtain rfl : N = 785 := by omega
                exact cvx785
              · obtain rfl : N = 786 := by omega
                exact cvx786
    · by_cases h6 : N ≤ 795
      · by_cases h8 : N ≤ 790
        · by_cases h10 : N ≤ 788
          · by_cases h12 : N ≤ 787
            · obtain rfl : N = 787 := by omega
              exact cvx787
            · obtain rfl : N = 788 := by omega
              exact cvx788
          · by_cases h12 : N ≤ 789
            · obtain rfl : N = 789 := by omega
              exact cvx789
            · obtain rfl : N = 790 := by omega
              exact cvx790
        · by_cases h10 : N ≤ 792
          · by_cases h12 : N ≤ 791
            · obtain rfl : N = 791 := by omega
              exact cvx791
            · obtain rfl : N = 792 := by omega
              exact cvx792
          · by_cases h12 : N ≤ 793
            · obtain rfl : N = 793 := by omega
              exact cvx793
            · by_cases h14 : N ≤ 794
              · obtain rfl : N = 794 := by omega
                exact cvx794
              · obtain rfl : N = 795 := by omega
                exact cvx795
      · by_cases h8 : N ≤ 800
        · by_cases h10 : N ≤ 797
          · by_cases h12 : N ≤ 796
            · obtain rfl : N = 796 := by omega
              exact cvx796
            · obtain rfl : N = 797 := by omega
              exact cvx797
          · by_cases h12 : N ≤ 798
            · obtain rfl : N = 798 := by omega
              exact cvx798
            · by_cases h14 : N ≤ 799
              · obtain rfl : N = 799 := by omega
                exact cvx799
              · obtain rfl : N = 800 := by omega
                exact cvx800
        · by_cases h10 : N ≤ 802
          · by_cases h12 : N ≤ 801
            · obtain rfl : N = 801 := by omega
              exact cvx801
            · obtain rfl : N = 802 := by omega
              exact cvx802
          · by_cases h12 : N ≤ 803
            · obtain rfl : N = 803 := by omega
              exact cvx803
            · by_cases h14 : N ≤ 804
              · obtain rfl : N = 804 := by omega
                exact cvx804
              · obtain rfl : N = 805 := by omega
                exact cvx805

theorem cen_733_805 {N : ℕ} (h1 : 733 ≤ N) (h2 : N ≤ 805) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 768
  · by_cases h4 : N ≤ 750
    · by_cases h6 : N ≤ 740
      · by_cases h8 : N ≤ 736
        · by_cases h10 : N ≤ 734
          · obtain rfl : N = 734 := by omega
            exact cen734
          · obtain rfl : N = 736 := by omega
            exact cen736
        · by_cases h10 : N ≤ 738
          · obtain rfl : N = 738 := by omega
            exact cen738
          · obtain rfl : N = 740 := by omega
            exact cen740
      · by_cases h8 : N ≤ 744
        · by_cases h10 : N ≤ 742
          · obtain rfl : N = 742 := by omega
            exact cen742
          · obtain rfl : N = 744 := by omega
            exact cen744
        · by_cases h10 : N ≤ 746
          · obtain rfl : N = 746 := by omega
            exact cen746
          · by_cases h12 : N ≤ 748
            · obtain rfl : N = 748 := by omega
              exact cen748
            · obtain rfl : N = 750 := by omega
              exact cen750
    · by_cases h6 : N ≤ 758
      · by_cases h8 : N ≤ 754
        · by_cases h10 : N ≤ 752
          · obtain rfl : N = 752 := by omega
            exact cen752
          · obtain rfl : N = 754 := by omega
            exact cen754
        · by_cases h10 : N ≤ 756
          · obtain rfl : N = 756 := by omega
            exact cen756
          · obtain rfl : N = 758 := by omega
            exact cen758
      · by_cases h8 : N ≤ 762
        · by_cases h10 : N ≤ 760
          · obtain rfl : N = 760 := by omega
            exact cen760
          · obtain rfl : N = 762 := by omega
            exact cen762
        · by_cases h10 : N ≤ 764
          · obtain rfl : N = 764 := by omega
            exact cen764
          · by_cases h12 : N ≤ 766
            · obtain rfl : N = 766 := by omega
              exact cen766
            · obtain rfl : N = 768 := by omega
              exact cen768
  · by_cases h4 : N ≤ 786
    · by_cases h6 : N ≤ 776
      · by_cases h8 : N ≤ 772
        · by_cases h10 : N ≤ 770
          · obtain rfl : N = 770 := by omega
            exact cen770
          · obtain rfl : N = 772 := by omega
            exact cen772
        · by_cases h10 : N ≤ 774
          · obtain rfl : N = 774 := by omega
            exact cen774
          · obtain rfl : N = 776 := by omega
            exact cen776
      · by_cases h8 : N ≤ 780
        · by_cases h10 : N ≤ 778
          · obtain rfl : N = 778 := by omega
            exact cen778
          · obtain rfl : N = 780 := by omega
            exact cen780
        · by_cases h10 : N ≤ 782
          · obtain rfl : N = 782 := by omega
            exact cen782
          · by_cases h12 : N ≤ 784
            · obtain rfl : N = 784 := by omega
              exact cen784
            · obtain rfl : N = 786 := by omega
              exact cen786
    · by_cases h6 : N ≤ 794
      · by_cases h8 : N ≤ 790
        · by_cases h10 : N ≤ 788
          · obtain rfl : N = 788 := by omega
            exact cen788
          · obtain rfl : N = 790 := by omega
            exact cen790
        · by_cases h10 : N ≤ 792
          · obtain rfl : N = 792 := by omega
            exact cen792
          · obtain rfl : N = 794 := by omega
            exact cen794
      · by_cases h8 : N ≤ 798
        · by_cases h10 : N ≤ 796
          · obtain rfl : N = 796 := by omega
            exact cen796
          · obtain rfl : N = 798 := by omega
            exact cen798
        · by_cases h10 : N ≤ 800
          · obtain rfl : N = 800 := by omega
            exact cen800
          · by_cases h12 : N ≤ 802
            · obtain rfl : N = 802 := by omega
              exact cen802
            · obtain rfl : N = 804 := by omega
              exact cen804

end Kagey131.PaperD.T7
