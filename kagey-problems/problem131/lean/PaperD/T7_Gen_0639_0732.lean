import PaperD.T7_Final
import PaperD.T7_Eval

/-!
# Paper D, track T7: kernel-checked certificates for `N = 639, …, 732` (generated)

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

/-! ### `N = 639` -/

def pL639 : Prm := ⟨72, 34, 35, 641, 11, 18446744073709551616, 245664372722449999, 245664372722449999⟩
def pH639 : Prm := ⟨72, 34, 35, 641, 11, 18446744073709551616, 245668770768961103, 245668770768961103⟩
def pI639 : Prm := ⟨62, 30, 29, 641, 11, 18446744073709551616, 245664372722449999, 245668770768961103⟩
theorem L639_fin : (prmOK pL639 639 && ptTest pL639 (runFrom pL639 (fmask pL639) (cmask pL639) (hmask pL639) 1 638 (true, (init pL639), (init pL639))) 639 320 false) = true := by
  decide +kernel
theorem L639_ok : RunOK pL639 639 (runFrom pL639 (fmask pL639) (cmask pL639) (hmask pL639) 1 638 (true, (init pL639), (init pL639))) ∧ ptTest pL639 (runFrom pL639 (fmask pL639) (cmask pL639) (hmask pL639) 1 638 (true, (init pL639), (init pL639))) 639 320 false = true :=
  fin_run (runOK_init (prmOK_of_and L639_fin) true) (by decide) rfl L639_fin ptTest_fst
theorem H639_fin : (prmOK pH639 639 && ptTest pH639 (runFrom pH639 (fmask pH639) (cmask pH639) (hmask pH639) 1 638 (true, (init pH639), (init pH639))) 639 320 true) = true := by
  decide +kernel
theorem H639_ok : RunOK pH639 639 (runFrom pH639 (fmask pH639) (cmask pH639) (hmask pH639) 1 638 (true, (init pH639), (init pH639))) ∧ ptTest pH639 (runFrom pH639 (fmask pH639) (cmask pH639) (hmask pH639) 1 638 (true, (init pH639), (init pH639))) 639 320 true = true :=
  fin_run (runOK_init (prmOK_of_and H639_fin) true) (by decide) rfl H639_fin ptTest_fst
theorem I639_fin : (prmOK pI639 639 && intTest pI639 (runFrom pI639 (fmask pI639) (cmask pI639) (hmask pI639) 1 638 (true, (init pI639), (init pI639))) 639 15 false) = true := by
  decide +kernel
theorem I639_ok : RunOK pI639 639 (runFrom pI639 (fmask pI639) (cmask pI639) (hmask pI639) 1 638 (true, (init pI639), (init pI639))) ∧ intTest pI639 (runFrom pI639 (fmask pI639) (cmask pI639) (hmask pI639) 1 638 (true, (init pI639), (init pI639))) 639 15 false = true :=
  fin_run (runOK_init (prmOK_of_and I639_fin) true) (by decide) rfl I639_fin intTest_fst
theorem link639 : linkOK pL639 pH639 pI639 = true := by decide +kernel
theorem cvx639 : ConvexBetweenHumps 639 :=
  cvx_of L639_ok H639_ok I639_ok link639 (by decide)

/-! ### `N = 640` -/

def pL640 : Prm := ⟨72, 34, 35, 642, 11, 18446744073709551616, 245365650201153511, 245365650201153511⟩
def pH640 : Prm := ⟨72, 34, 35, 642, 11, 18446744073709551616, 245370048247664615, 245370048247664615⟩
def pI640 : Prm := ⟨62, 30, 29, 642, 11, 18446744073709551616, 245365650201153511, 245370048247664615⟩
theorem L640_fin : (prmOK pL640 640 && ptTest pL640 (runFrom pL640 (fmask pL640) (cmask pL640) (hmask pL640) 1 639 (true, (init pL640), (init pL640))) 640 320 false) = true := by
  decide +kernel
theorem L640_ok : RunOK pL640 640 (runFrom pL640 (fmask pL640) (cmask pL640) (hmask pL640) 1 639 (true, (init pL640), (init pL640))) ∧ ptTest pL640 (runFrom pL640 (fmask pL640) (cmask pL640) (hmask pL640) 1 639 (true, (init pL640), (init pL640))) 640 320 false = true :=
  fin_run (runOK_init (prmOK_of_and L640_fin) true) (by decide) rfl L640_fin ptTest_fst
theorem H640_fin : (prmOK pH640 640 && ptTest pH640 (runFrom pH640 (fmask pH640) (cmask pH640) (hmask pH640) 1 639 (true, (init pH640), (init pH640))) 640 320 true) = true := by
  decide +kernel
theorem H640_ok : RunOK pH640 640 (runFrom pH640 (fmask pH640) (cmask pH640) (hmask pH640) 1 639 (true, (init pH640), (init pH640))) ∧ ptTest pH640 (runFrom pH640 (fmask pH640) (cmask pH640) (hmask pH640) 1 639 (true, (init pH640), (init pH640))) 640 320 true = true :=
  fin_run (runOK_init (prmOK_of_and H640_fin) true) (by decide) rfl H640_fin ptTest_fst
theorem I640_fin : (prmOK pI640 640 && intTest pI640 (runFrom pI640 (fmask pI640) (cmask pI640) (hmask pI640) 1 639 (true, (init pI640), (init pI640))) 640 15 true) = true := by
  decide +kernel
theorem I640_ok : RunOK pI640 640 (runFrom pI640 (fmask pI640) (cmask pI640) (hmask pI640) 1 639 (true, (init pI640), (init pI640))) ∧ intTest pI640 (runFrom pI640 (fmask pI640) (cmask pI640) (hmask pI640) 1 639 (true, (init pI640), (init pI640))) 640 15 true = true :=
  fin_run (runOK_init (prmOK_of_and I640_fin) true) (by decide) rfl I640_fin intTest_fst
theorem link640 : linkOK pL640 pH640 pI640 = true := by decide +kernel
theorem cvx640 : ConvexBetweenHumps 640 :=
  cvx_of L640_ok H640_ok I640_ok link640 (by decide)
theorem cenlink640 : cenLinkOK pI640 640 = true := by decide +kernel
theorem cen640 : CenterUniqueMin 640 ∧ DipHyp 640 ∧ OnePointHyps 640 :=
  cen_of L640_ok H640_ok I640_ok link640 cenlink640

/-! ### `N = 641` -/

def pL641 : Prm := ⟨72, 34, 35, 643, 11, 18446744073709551616, 245067276995408689, 245067276995408689⟩
def pH641 : Prm := ⟨72, 34, 35, 643, 11, 18446744073709551616, 245071675041919793, 245071675041919793⟩
def pI641 : Prm := ⟨62, 30, 29, 643, 11, 18446744073709551616, 245067276995408689, 245071675041919793⟩
theorem L641_fin : (prmOK pL641 641 && ptTest pL641 (runFrom pL641 (fmask pL641) (cmask pL641) (hmask pL641) 1 640 (true, (init pL641), (init pL641))) 641 321 false) = true := by
  decide +kernel
theorem L641_ok : RunOK pL641 641 (runFrom pL641 (fmask pL641) (cmask pL641) (hmask pL641) 1 640 (true, (init pL641), (init pL641))) ∧ ptTest pL641 (runFrom pL641 (fmask pL641) (cmask pL641) (hmask pL641) 1 640 (true, (init pL641), (init pL641))) 641 321 false = true :=
  fin_run (runOK_init (prmOK_of_and L641_fin) true) (by decide) rfl L641_fin ptTest_fst
theorem H641_fin : (prmOK pH641 641 && ptTest pH641 (runFrom pH641 (fmask pH641) (cmask pH641) (hmask pH641) 1 640 (true, (init pH641), (init pH641))) 641 321 true) = true := by
  decide +kernel
theorem H641_ok : RunOK pH641 641 (runFrom pH641 (fmask pH641) (cmask pH641) (hmask pH641) 1 640 (true, (init pH641), (init pH641))) ∧ ptTest pH641 (runFrom pH641 (fmask pH641) (cmask pH641) (hmask pH641) 1 640 (true, (init pH641), (init pH641))) 641 321 true = true :=
  fin_run (runOK_init (prmOK_of_and H641_fin) true) (by decide) rfl H641_fin ptTest_fst
theorem I641_fin : (prmOK pI641 641 && intTest pI641 (runFrom pI641 (fmask pI641) (cmask pI641) (hmask pI641) 1 640 (true, (init pI641), (init pI641))) 641 15 false) = true := by
  decide +kernel
theorem I641_ok : RunOK pI641 641 (runFrom pI641 (fmask pI641) (cmask pI641) (hmask pI641) 1 640 (true, (init pI641), (init pI641))) ∧ intTest pI641 (runFrom pI641 (fmask pI641) (cmask pI641) (hmask pI641) 1 640 (true, (init pI641), (init pI641))) 641 15 false = true :=
  fin_run (runOK_init (prmOK_of_and I641_fin) true) (by decide) rfl I641_fin intTest_fst
theorem link641 : linkOK pL641 pH641 pI641 = true := by decide +kernel
theorem cvx641 : ConvexBetweenHumps 641 :=
  cvx_of L641_ok H641_ok I641_ok link641 (by decide)

/-! ### `N = 642` -/

def pL642 : Prm := ⟨72, 34, 35, 644, 11, 18446744073709551616, 244770151179195379, 244770151179195379⟩
def pH642 : Prm := ⟨72, 34, 35, 644, 11, 18446744073709551616, 244774549225706483, 244774549225706483⟩
def pI642 : Prm := ⟨62, 30, 29, 644, 11, 18446744073709551616, 244770151179195379, 244774549225706483⟩
theorem L642_fin : (prmOK pL642 642 && ptTest pL642 (runFrom pL642 (fmask pL642) (cmask pL642) (hmask pL642) 1 641 (true, (init pL642), (init pL642))) 642 321 false) = true := by
  decide +kernel
theorem L642_ok : RunOK pL642 642 (runFrom pL642 (fmask pL642) (cmask pL642) (hmask pL642) 1 641 (true, (init pL642), (init pL642))) ∧ ptTest pL642 (runFrom pL642 (fmask pL642) (cmask pL642) (hmask pL642) 1 641 (true, (init pL642), (init pL642))) 642 321 false = true :=
  fin_run (runOK_init (prmOK_of_and L642_fin) true) (by decide) rfl L642_fin ptTest_fst
theorem H642_fin : (prmOK pH642 642 && ptTest pH642 (runFrom pH642 (fmask pH642) (cmask pH642) (hmask pH642) 1 641 (true, (init pH642), (init pH642))) 642 321 true) = true := by
  decide +kernel
theorem H642_ok : RunOK pH642 642 (runFrom pH642 (fmask pH642) (cmask pH642) (hmask pH642) 1 641 (true, (init pH642), (init pH642))) ∧ ptTest pH642 (runFrom pH642 (fmask pH642) (cmask pH642) (hmask pH642) 1 641 (true, (init pH642), (init pH642))) 642 321 true = true :=
  fin_run (runOK_init (prmOK_of_and H642_fin) true) (by decide) rfl H642_fin ptTest_fst
theorem I642_fin : (prmOK pI642 642 && intTest pI642 (runFrom pI642 (fmask pI642) (cmask pI642) (hmask pI642) 1 641 (true, (init pI642), (init pI642))) 642 15 true) = true := by
  decide +kernel
theorem I642_ok : RunOK pI642 642 (runFrom pI642 (fmask pI642) (cmask pI642) (hmask pI642) 1 641 (true, (init pI642), (init pI642))) ∧ intTest pI642 (runFrom pI642 (fmask pI642) (cmask pI642) (hmask pI642) 1 641 (true, (init pI642), (init pI642))) 642 15 true = true :=
  fin_run (runOK_init (prmOK_of_and I642_fin) true) (by decide) rfl I642_fin intTest_fst
theorem link642 : linkOK pL642 pH642 pI642 = true := by decide +kernel
theorem cvx642 : ConvexBetweenHumps 642 :=
  cvx_of L642_ok H642_ok I642_ok link642 (by decide)
theorem cenlink642 : cenLinkOK pI642 642 = true := by decide +kernel
theorem cen642 : CenterUniqueMin 642 ∧ DipHyp 642 ∧ OnePointHyps 642 :=
  cen_of L642_ok H642_ok I642_ok link642 cenlink642

/-! ### `N = 643` -/

def pL643 : Prm := ⟨72, 34, 35, 645, 11, 18446744073709551616, 244473372305230982, 244473372305230982⟩
def pH643 : Prm := ⟨72, 34, 35, 645, 11, 18446744073709551616, 244477770351742086, 244477770351742086⟩
def pI643 : Prm := ⟨62, 30, 29, 645, 11, 18446744073709551616, 244473372305230982, 244477770351742086⟩
theorem L643_fin : (prmOK pL643 643 && ptTest pL643 (runFrom pL643 (fmask pL643) (cmask pL643) (hmask pL643) 1 642 (true, (init pL643), (init pL643))) 643 322 false) = true := by
  decide +kernel
theorem L643_ok : RunOK pL643 643 (runFrom pL643 (fmask pL643) (cmask pL643) (hmask pL643) 1 642 (true, (init pL643), (init pL643))) ∧ ptTest pL643 (runFrom pL643 (fmask pL643) (cmask pL643) (hmask pL643) 1 642 (true, (init pL643), (init pL643))) 643 322 false = true :=
  fin_run (runOK_init (prmOK_of_and L643_fin) true) (by decide) rfl L643_fin ptTest_fst
theorem H643_fin : (prmOK pH643 643 && ptTest pH643 (runFrom pH643 (fmask pH643) (cmask pH643) (hmask pH643) 1 642 (true, (init pH643), (init pH643))) 643 322 true) = true := by
  decide +kernel
theorem H643_ok : RunOK pH643 643 (runFrom pH643 (fmask pH643) (cmask pH643) (hmask pH643) 1 642 (true, (init pH643), (init pH643))) ∧ ptTest pH643 (runFrom pH643 (fmask pH643) (cmask pH643) (hmask pH643) 1 642 (true, (init pH643), (init pH643))) 643 322 true = true :=
  fin_run (runOK_init (prmOK_of_and H643_fin) true) (by decide) rfl H643_fin ptTest_fst
theorem I643_fin : (prmOK pI643 643 && intTest pI643 (runFrom pI643 (fmask pI643) (cmask pI643) (hmask pI643) 1 642 (true, (init pI643), (init pI643))) 643 15 false) = true := by
  decide +kernel
theorem I643_ok : RunOK pI643 643 (runFrom pI643 (fmask pI643) (cmask pI643) (hmask pI643) 1 642 (true, (init pI643), (init pI643))) ∧ intTest pI643 (runFrom pI643 (fmask pI643) (cmask pI643) (hmask pI643) 1 642 (true, (init pI643), (init pI643))) 643 15 false = true :=
  fin_run (runOK_init (prmOK_of_and I643_fin) true) (by decide) rfl I643_fin intTest_fst
theorem link643 : linkOK pL643 pH643 pI643 = true := by decide +kernel
theorem cvx643 : ConvexBetweenHumps 643 :=
  cvx_of L643_ok H643_ok I643_ok link643 (by decide)

/-! ### `N = 644` -/

def pL644 : Prm := ⟨72, 34, 35, 646, 11, 18446744073709551616, 244177829945077407, 244177829945077407⟩
def pH644 : Prm := ⟨72, 34, 35, 646, 11, 18446744073709551616, 244182227991588511, 244182227991588511⟩
def pI644 : Prm := ⟨62, 30, 29, 646, 11, 18446744073709551616, 244177829945077407, 244182227991588511⟩
theorem L644_fin : (prmOK pL644 644 && ptTest pL644 (runFrom pL644 (fmask pL644) (cmask pL644) (hmask pL644) 1 643 (true, (init pL644), (init pL644))) 644 322 false) = true := by
  decide +kernel
theorem L644_ok : RunOK pL644 644 (runFrom pL644 (fmask pL644) (cmask pL644) (hmask pL644) 1 643 (true, (init pL644), (init pL644))) ∧ ptTest pL644 (runFrom pL644 (fmask pL644) (cmask pL644) (hmask pL644) 1 643 (true, (init pL644), (init pL644))) 644 322 false = true :=
  fin_run (runOK_init (prmOK_of_and L644_fin) true) (by decide) rfl L644_fin ptTest_fst
theorem H644_fin : (prmOK pH644 644 && ptTest pH644 (runFrom pH644 (fmask pH644) (cmask pH644) (hmask pH644) 1 643 (true, (init pH644), (init pH644))) 644 322 true) = true := by
  decide +kernel
theorem H644_ok : RunOK pH644 644 (runFrom pH644 (fmask pH644) (cmask pH644) (hmask pH644) 1 643 (true, (init pH644), (init pH644))) ∧ ptTest pH644 (runFrom pH644 (fmask pH644) (cmask pH644) (hmask pH644) 1 643 (true, (init pH644), (init pH644))) 644 322 true = true :=
  fin_run (runOK_init (prmOK_of_and H644_fin) true) (by decide) rfl H644_fin ptTest_fst
theorem I644_fin : (prmOK pI644 644 && intTest pI644 (runFrom pI644 (fmask pI644) (cmask pI644) (hmask pI644) 1 643 (true, (init pI644), (init pI644))) 644 15 true) = true := by
  decide +kernel
theorem I644_ok : RunOK pI644 644 (runFrom pI644 (fmask pI644) (cmask pI644) (hmask pI644) 1 643 (true, (init pI644), (init pI644))) ∧ intTest pI644 (runFrom pI644 (fmask pI644) (cmask pI644) (hmask pI644) 1 643 (true, (init pI644), (init pI644))) 644 15 true = true :=
  fin_run (runOK_init (prmOK_of_and I644_fin) true) (by decide) rfl I644_fin intTest_fst
theorem link644 : linkOK pL644 pH644 pI644 = true := by decide +kernel
theorem cvx644 : ConvexBetweenHumps 644 :=
  cvx_of L644_ok H644_ok I644_ok link644 (by decide)
theorem cenlink644 : cenLinkOK pI644 644 = true := by decide +kernel
theorem cen644 : CenterUniqueMin 644 ∧ DipHyp 644 ∧ OnePointHyps 644 :=
  cen_of L644_ok H644_ok I644_ok link644 cenlink644

/-! ### `N = 645` -/

def pL645 : Prm := ⟨72, 34, 35, 647, 11, 18446744073709551616, 243882632175231323, 243882632175231323⟩
def pH645 : Prm := ⟨72, 34, 35, 647, 11, 18446744073709551616, 243887030221742427, 243887030221742427⟩
def pI645 : Prm := ⟨62, 30, 29, 647, 11, 18446744073709551616, 243882632175231323, 243887030221742427⟩
theorem L645_fin : (prmOK pL645 645 && ptTest pL645 (runFrom pL645 (fmask pL645) (cmask pL645) (hmask pL645) 1 644 (true, (init pL645), (init pL645))) 645 323 false) = true := by
  decide +kernel
theorem L645_ok : RunOK pL645 645 (runFrom pL645 (fmask pL645) (cmask pL645) (hmask pL645) 1 644 (true, (init pL645), (init pL645))) ∧ ptTest pL645 (runFrom pL645 (fmask pL645) (cmask pL645) (hmask pL645) 1 644 (true, (init pL645), (init pL645))) 645 323 false = true :=
  fin_run (runOK_init (prmOK_of_and L645_fin) true) (by decide) rfl L645_fin ptTest_fst
theorem H645_fin : (prmOK pH645 645 && ptTest pH645 (runFrom pH645 (fmask pH645) (cmask pH645) (hmask pH645) 1 644 (true, (init pH645), (init pH645))) 645 323 true) = true := by
  decide +kernel
theorem H645_ok : RunOK pH645 645 (runFrom pH645 (fmask pH645) (cmask pH645) (hmask pH645) 1 644 (true, (init pH645), (init pH645))) ∧ ptTest pH645 (runFrom pH645 (fmask pH645) (cmask pH645) (hmask pH645) 1 644 (true, (init pH645), (init pH645))) 645 323 true = true :=
  fin_run (runOK_init (prmOK_of_and H645_fin) true) (by decide) rfl H645_fin ptTest_fst
theorem I645_fin : (prmOK pI645 645 && intTest pI645 (runFrom pI645 (fmask pI645) (cmask pI645) (hmask pI645) 1 644 (true, (init pI645), (init pI645))) 645 15 false) = true := by
  decide +kernel
theorem I645_ok : RunOK pI645 645 (runFrom pI645 (fmask pI645) (cmask pI645) (hmask pI645) 1 644 (true, (init pI645), (init pI645))) ∧ intTest pI645 (runFrom pI645 (fmask pI645) (cmask pI645) (hmask pI645) 1 644 (true, (init pI645), (init pI645))) 645 15 false = true :=
  fin_run (runOK_init (prmOK_of_and I645_fin) true) (by decide) rfl I645_fin intTest_fst
theorem link645 : linkOK pL645 pH645 pI645 = true := by decide +kernel
theorem cvx645 : ConvexBetweenHumps 645 :=
  cvx_of L645_ok H645_ok I645_ok link645 (by decide)

/-! ### `N = 646` -/

def pL646 : Prm := ⟨72, 34, 35, 648, 11, 18446744073709551616, 243588660171255965, 243588660171255965⟩
def pH646 : Prm := ⟨72, 34, 35, 648, 11, 18446744073709551616, 243593058217767069, 243593058217767069⟩
def pI646 : Prm := ⟨62, 30, 29, 648, 11, 18446744073709551616, 243588660171255965, 243593058217767069⟩
theorem L646_fin : (prmOK pL646 646 && ptTest pL646 (runFrom pL646 (fmask pL646) (cmask pL646) (hmask pL646) 1 645 (true, (init pL646), (init pL646))) 646 323 false) = true := by
  decide +kernel
theorem L646_ok : RunOK pL646 646 (runFrom pL646 (fmask pL646) (cmask pL646) (hmask pL646) 1 645 (true, (init pL646), (init pL646))) ∧ ptTest pL646 (runFrom pL646 (fmask pL646) (cmask pL646) (hmask pL646) 1 645 (true, (init pL646), (init pL646))) 646 323 false = true :=
  fin_run (runOK_init (prmOK_of_and L646_fin) true) (by decide) rfl L646_fin ptTest_fst
theorem H646_fin : (prmOK pH646 646 && ptTest pH646 (runFrom pH646 (fmask pH646) (cmask pH646) (hmask pH646) 1 645 (true, (init pH646), (init pH646))) 646 323 true) = true := by
  decide +kernel
theorem H646_ok : RunOK pH646 646 (runFrom pH646 (fmask pH646) (cmask pH646) (hmask pH646) 1 645 (true, (init pH646), (init pH646))) ∧ ptTest pH646 (runFrom pH646 (fmask pH646) (cmask pH646) (hmask pH646) 1 645 (true, (init pH646), (init pH646))) 646 323 true = true :=
  fin_run (runOK_init (prmOK_of_and H646_fin) true) (by decide) rfl H646_fin ptTest_fst
theorem I646_fin : (prmOK pI646 646 && intTest pI646 (runFrom pI646 (fmask pI646) (cmask pI646) (hmask pI646) 1 645 (true, (init pI646), (init pI646))) 646 15 true) = true := by
  decide +kernel
theorem I646_ok : RunOK pI646 646 (runFrom pI646 (fmask pI646) (cmask pI646) (hmask pI646) 1 645 (true, (init pI646), (init pI646))) ∧ intTest pI646 (runFrom pI646 (fmask pI646) (cmask pI646) (hmask pI646) 1 645 (true, (init pI646), (init pI646))) 646 15 true = true :=
  fin_run (runOK_init (prmOK_of_and I646_fin) true) (by decide) rfl I646_fin intTest_fst
theorem link646 : linkOK pL646 pH646 pI646 = true := by decide +kernel
theorem cvx646 : ConvexBetweenHumps 646 :=
  cvx_of L646_ok H646_ok I646_ok link646 (by decide)
theorem cenlink646 : cenLinkOK pI646 646 = true := by decide +kernel
theorem cen646 : CenterUniqueMin 646 ∧ DipHyp 646 ∧ OnePointHyps 646 :=
  cen_of L646_ok H646_ok I646_ok link646 cenlink646

/-! ### `N = 647` -/

def pL647 : Prm := ⟨72, 34, 35, 649, 11, 18446744073709551616, 243295030426786646, 243295030426786646⟩
def pH647 : Prm := ⟨72, 34, 35, 649, 11, 18446744073709551616, 243299428473297750, 243299428473297750⟩
def pI647 : Prm := ⟨62, 30, 29, 649, 11, 18446744073709551616, 243295030426786646, 243299428473297750⟩
theorem L647_fin : (prmOK pL647 647 && ptTest pL647 (runFrom pL647 (fmask pL647) (cmask pL647) (hmask pL647) 1 646 (true, (init pL647), (init pL647))) 647 324 false) = true := by
  decide +kernel
theorem L647_ok : RunOK pL647 647 (runFrom pL647 (fmask pL647) (cmask pL647) (hmask pL647) 1 646 (true, (init pL647), (init pL647))) ∧ ptTest pL647 (runFrom pL647 (fmask pL647) (cmask pL647) (hmask pL647) 1 646 (true, (init pL647), (init pL647))) 647 324 false = true :=
  fin_run (runOK_init (prmOK_of_and L647_fin) true) (by decide) rfl L647_fin ptTest_fst
theorem H647_fin : (prmOK pH647 647 && ptTest pH647 (runFrom pH647 (fmask pH647) (cmask pH647) (hmask pH647) 1 646 (true, (init pH647), (init pH647))) 647 324 true) = true := by
  decide +kernel
theorem H647_ok : RunOK pH647 647 (runFrom pH647 (fmask pH647) (cmask pH647) (hmask pH647) 1 646 (true, (init pH647), (init pH647))) ∧ ptTest pH647 (runFrom pH647 (fmask pH647) (cmask pH647) (hmask pH647) 1 646 (true, (init pH647), (init pH647))) 647 324 true = true :=
  fin_run (runOK_init (prmOK_of_and H647_fin) true) (by decide) rfl H647_fin ptTest_fst
theorem I647_fin : (prmOK pI647 647 && intTest pI647 (runFrom pI647 (fmask pI647) (cmask pI647) (hmask pI647) 1 646 (true, (init pI647), (init pI647))) 647 15 false) = true := by
  decide +kernel
theorem I647_ok : RunOK pI647 647 (runFrom pI647 (fmask pI647) (cmask pI647) (hmask pI647) 1 646 (true, (init pI647), (init pI647))) ∧ intTest pI647 (runFrom pI647 (fmask pI647) (cmask pI647) (hmask pI647) 1 646 (true, (init pI647), (init pI647))) 647 15 false = true :=
  fin_run (runOK_init (prmOK_of_and I647_fin) true) (by decide) rfl I647_fin intTest_fst
theorem link647 : linkOK pL647 pH647 pI647 = true := by decide +kernel
theorem cvx647 : ConvexBetweenHumps 647 :=
  cvx_of L647_ok H647_ok I647_ok link647 (by decide)

/-! ### `N = 648` -/

def pL648 : Prm := ⟨72, 34, 35, 650, 11, 18446744073709551616, 243002615826183879, 243002615826183879⟩
def pH648 : Prm := ⟨72, 34, 35, 650, 11, 18446744073709551616, 243007013872694983, 243007013872694983⟩
def pI648 : Prm := ⟨62, 30, 29, 650, 11, 18446744073709551616, 243002615826183879, 243007013872694983⟩
theorem L648_fin : (prmOK pL648 648 && ptTest pL648 (runFrom pL648 (fmask pL648) (cmask pL648) (hmask pL648) 1 647 (true, (init pL648), (init pL648))) 648 324 false) = true := by
  decide +kernel
theorem L648_ok : RunOK pL648 648 (runFrom pL648 (fmask pL648) (cmask pL648) (hmask pL648) 1 647 (true, (init pL648), (init pL648))) ∧ ptTest pL648 (runFrom pL648 (fmask pL648) (cmask pL648) (hmask pL648) 1 647 (true, (init pL648), (init pL648))) 648 324 false = true :=
  fin_run (runOK_init (prmOK_of_and L648_fin) true) (by decide) rfl L648_fin ptTest_fst
theorem H648_fin : (prmOK pH648 648 && ptTest pH648 (runFrom pH648 (fmask pH648) (cmask pH648) (hmask pH648) 1 647 (true, (init pH648), (init pH648))) 648 324 true) = true := by
  decide +kernel
theorem H648_ok : RunOK pH648 648 (runFrom pH648 (fmask pH648) (cmask pH648) (hmask pH648) 1 647 (true, (init pH648), (init pH648))) ∧ ptTest pH648 (runFrom pH648 (fmask pH648) (cmask pH648) (hmask pH648) 1 647 (true, (init pH648), (init pH648))) 648 324 true = true :=
  fin_run (runOK_init (prmOK_of_and H648_fin) true) (by decide) rfl H648_fin ptTest_fst
theorem I648_fin : (prmOK pI648 648 && intTest pI648 (runFrom pI648 (fmask pI648) (cmask pI648) (hmask pI648) 1 647 (true, (init pI648), (init pI648))) 648 15 true) = true := by
  decide +kernel
theorem I648_ok : RunOK pI648 648 (runFrom pI648 (fmask pI648) (cmask pI648) (hmask pI648) 1 647 (true, (init pI648), (init pI648))) ∧ intTest pI648 (runFrom pI648 (fmask pI648) (cmask pI648) (hmask pI648) 1 647 (true, (init pI648), (init pI648))) 648 15 true = true :=
  fin_run (runOK_init (prmOK_of_and I648_fin) true) (by decide) rfl I648_fin intTest_fst
theorem link648 : linkOK pL648 pH648 pI648 = true := by decide +kernel
theorem cvx648 : ConvexBetweenHumps 648 :=
  cvx_of L648_ok H648_ok I648_ok link648 (by decide)
theorem cenlink648 : cenLinkOK pI648 648 = true := by decide +kernel
theorem cen648 : CenterUniqueMin 648 ∧ DipHyp 648 ∧ OnePointHyps 648 :=
  cen_of L648_ok H648_ok I648_ok link648 cenlink648

/-! ### `N = 649` -/

def pL649 : Prm := ⟨72, 34, 35, 651, 11, 18446744073709551616, 242710541175185859, 242710541175185859⟩
def pH649 : Prm := ⟨72, 34, 35, 651, 11, 18446744073709551616, 242714939221696963, 242714939221696963⟩
def pI649 : Prm := ⟨62, 30, 29, 651, 11, 18446744073709551616, 242710541175185859, 242714939221696963⟩
theorem L649_fin : (prmOK pL649 649 && ptTest pL649 (runFrom pL649 (fmask pL649) (cmask pL649) (hmask pL649) 1 648 (true, (init pL649), (init pL649))) 649 325 false) = true := by
  decide +kernel
theorem L649_ok : RunOK pL649 649 (runFrom pL649 (fmask pL649) (cmask pL649) (hmask pL649) 1 648 (true, (init pL649), (init pL649))) ∧ ptTest pL649 (runFrom pL649 (fmask pL649) (cmask pL649) (hmask pL649) 1 648 (true, (init pL649), (init pL649))) 649 325 false = true :=
  fin_run (runOK_init (prmOK_of_and L649_fin) true) (by decide) rfl L649_fin ptTest_fst
theorem H649_fin : (prmOK pH649 649 && ptTest pH649 (runFrom pH649 (fmask pH649) (cmask pH649) (hmask pH649) 1 648 (true, (init pH649), (init pH649))) 649 325 true) = true := by
  decide +kernel
theorem H649_ok : RunOK pH649 649 (runFrom pH649 (fmask pH649) (cmask pH649) (hmask pH649) 1 648 (true, (init pH649), (init pH649))) ∧ ptTest pH649 (runFrom pH649 (fmask pH649) (cmask pH649) (hmask pH649) 1 648 (true, (init pH649), (init pH649))) 649 325 true = true :=
  fin_run (runOK_init (prmOK_of_and H649_fin) true) (by decide) rfl H649_fin ptTest_fst
theorem I649_fin : (prmOK pI649 649 && intTest pI649 (runFrom pI649 (fmask pI649) (cmask pI649) (hmask pI649) 1 648 (true, (init pI649), (init pI649))) 649 15 false) = true := by
  decide +kernel
theorem I649_ok : RunOK pI649 649 (runFrom pI649 (fmask pI649) (cmask pI649) (hmask pI649) 1 648 (true, (init pI649), (init pI649))) ∧ intTest pI649 (runFrom pI649 (fmask pI649) (cmask pI649) (hmask pI649) 1 648 (true, (init pI649), (init pI649))) 649 15 false = true :=
  fin_run (runOK_init (prmOK_of_and I649_fin) true) (by decide) rfl I649_fin intTest_fst
theorem link649 : linkOK pL649 pH649 pI649 = true := by decide +kernel
theorem cvx649 : ConvexBetweenHumps 649 :=
  cvx_of L649_ok H649_ok I649_ok link649 (by decide)

/-! ### `N = 650` -/

def pL650 : Prm := ⟨72, 34, 35, 652, 11, 18446744073709551616, 242419671170049232, 242419671170049232⟩
def pH650 : Prm := ⟨72, 34, 35, 652, 11, 18446744073709551616, 242424069216560336, 242424069216560336⟩
def pI650 : Prm := ⟨62, 30, 29, 652, 11, 18446744073709551616, 242419671170049232, 242424069216560336⟩
theorem L650_fin : (prmOK pL650 650 && ptTest pL650 (runFrom pL650 (fmask pL650) (cmask pL650) (hmask pL650) 1 649 (true, (init pL650), (init pL650))) 650 325 false) = true := by
  decide +kernel
theorem L650_ok : RunOK pL650 650 (runFrom pL650 (fmask pL650) (cmask pL650) (hmask pL650) 1 649 (true, (init pL650), (init pL650))) ∧ ptTest pL650 (runFrom pL650 (fmask pL650) (cmask pL650) (hmask pL650) 1 649 (true, (init pL650), (init pL650))) 650 325 false = true :=
  fin_run (runOK_init (prmOK_of_and L650_fin) true) (by decide) rfl L650_fin ptTest_fst
theorem H650_fin : (prmOK pH650 650 && ptTest pH650 (runFrom pH650 (fmask pH650) (cmask pH650) (hmask pH650) 1 649 (true, (init pH650), (init pH650))) 650 325 true) = true := by
  decide +kernel
theorem H650_ok : RunOK pH650 650 (runFrom pH650 (fmask pH650) (cmask pH650) (hmask pH650) 1 649 (true, (init pH650), (init pH650))) ∧ ptTest pH650 (runFrom pH650 (fmask pH650) (cmask pH650) (hmask pH650) 1 649 (true, (init pH650), (init pH650))) 650 325 true = true :=
  fin_run (runOK_init (prmOK_of_and H650_fin) true) (by decide) rfl H650_fin ptTest_fst
theorem I650_fin : (prmOK pI650 650 && intTest pI650 (runFrom pI650 (fmask pI650) (cmask pI650) (hmask pI650) 1 649 (true, (init pI650), (init pI650))) 650 15 true) = true := by
  decide +kernel
theorem I650_ok : RunOK pI650 650 (runFrom pI650 (fmask pI650) (cmask pI650) (hmask pI650) 1 649 (true, (init pI650), (init pI650))) ∧ intTest pI650 (runFrom pI650 (fmask pI650) (cmask pI650) (hmask pI650) 1 649 (true, (init pI650), (init pI650))) 650 15 true = true :=
  fin_run (runOK_init (prmOK_of_and I650_fin) true) (by decide) rfl I650_fin intTest_fst
theorem link650 : linkOK pL650 pH650 pI650 = true := by decide +kernel
theorem cvx650 : ConvexBetweenHumps 650 :=
  cvx_of L650_ok H650_ok I650_ok link650 (by decide)
theorem cenlink650 : cenLinkOK pI650 650 = true := by decide +kernel
theorem cen650 : CenterUniqueMin 650 ∧ DipHyp 650 ∧ OnePointHyps 650 :=
  cen_of L650_ok H650_ok I650_ok link650 cenlink650

/-! ### `N = 651` -/

def pL651 : Prm := ⟨72, 34, 35, 653, 11, 18446744073709551616, 242129138825313305, 242129138825313305⟩
def pH651 : Prm := ⟨72, 34, 35, 653, 11, 18446744073709551616, 242133536871824409, 242133536871824409⟩
def pI651 : Prm := ⟨63, 30, 30, 653, 11, 18446744073709551616, 242129138825313305, 242133536871824409⟩
theorem L651_fin : (prmOK pL651 651 && ptTest pL651 (runFrom pL651 (fmask pL651) (cmask pL651) (hmask pL651) 1 650 (true, (init pL651), (init pL651))) 651 326 false) = true := by
  decide +kernel
theorem L651_ok : RunOK pL651 651 (runFrom pL651 (fmask pL651) (cmask pL651) (hmask pL651) 1 650 (true, (init pL651), (init pL651))) ∧ ptTest pL651 (runFrom pL651 (fmask pL651) (cmask pL651) (hmask pL651) 1 650 (true, (init pL651), (init pL651))) 651 326 false = true :=
  fin_run (runOK_init (prmOK_of_and L651_fin) true) (by decide) rfl L651_fin ptTest_fst
theorem H651_fin : (prmOK pH651 651 && ptTest pH651 (runFrom pH651 (fmask pH651) (cmask pH651) (hmask pH651) 1 650 (true, (init pH651), (init pH651))) 651 326 true) = true := by
  decide +kernel
theorem H651_ok : RunOK pH651 651 (runFrom pH651 (fmask pH651) (cmask pH651) (hmask pH651) 1 650 (true, (init pH651), (init pH651))) ∧ ptTest pH651 (runFrom pH651 (fmask pH651) (cmask pH651) (hmask pH651) 1 650 (true, (init pH651), (init pH651))) 651 326 true = true :=
  fin_run (runOK_init (prmOK_of_and H651_fin) true) (by decide) rfl H651_fin ptTest_fst
theorem I651_fin : (prmOK pI651 651 && intTest pI651 (runFrom pI651 (fmask pI651) (cmask pI651) (hmask pI651) 1 650 (true, (init pI651), (init pI651))) 651 15 false) = true := by
  decide +kernel
theorem I651_ok : RunOK pI651 651 (runFrom pI651 (fmask pI651) (cmask pI651) (hmask pI651) 1 650 (true, (init pI651), (init pI651))) ∧ intTest pI651 (runFrom pI651 (fmask pI651) (cmask pI651) (hmask pI651) 1 650 (true, (init pI651), (init pI651))) 651 15 false = true :=
  fin_run (runOK_init (prmOK_of_and I651_fin) true) (by decide) rfl I651_fin intTest_fst
theorem link651 : linkOK pL651 pH651 pI651 = true := by decide +kernel
theorem cvx651 : ConvexBetweenHumps 651 :=
  cvx_of L651_ok H651_ok I651_ok link651 (by decide)

/-! ### `N = 652` -/

def pL652 : Prm := ⟨72, 34, 35, 654, 11, 18446744073709551616, 241839800750717080, 241839800750717080⟩
def pH652 : Prm := ⟨72, 34, 35, 654, 11, 18446744073709551616, 241844198797228184, 241844198797228184⟩
def pI652 : Prm := ⟨63, 30, 30, 654, 11, 18446744073709551616, 241839800750717080, 241844198797228184⟩
theorem L652_fin : (prmOK pL652 652 && ptTest pL652 (runFrom pL652 (fmask pL652) (cmask pL652) (hmask pL652) 1 651 (true, (init pL652), (init pL652))) 652 326 false) = true := by
  decide +kernel
theorem L652_ok : RunOK pL652 652 (runFrom pL652 (fmask pL652) (cmask pL652) (hmask pL652) 1 651 (true, (init pL652), (init pL652))) ∧ ptTest pL652 (runFrom pL652 (fmask pL652) (cmask pL652) (hmask pL652) 1 651 (true, (init pL652), (init pL652))) 652 326 false = true :=
  fin_run (runOK_init (prmOK_of_and L652_fin) true) (by decide) rfl L652_fin ptTest_fst
theorem H652_fin : (prmOK pH652 652 && ptTest pH652 (runFrom pH652 (fmask pH652) (cmask pH652) (hmask pH652) 1 651 (true, (init pH652), (init pH652))) 652 326 true) = true := by
  decide +kernel
theorem H652_ok : RunOK pH652 652 (runFrom pH652 (fmask pH652) (cmask pH652) (hmask pH652) 1 651 (true, (init pH652), (init pH652))) ∧ ptTest pH652 (runFrom pH652 (fmask pH652) (cmask pH652) (hmask pH652) 1 651 (true, (init pH652), (init pH652))) 652 326 true = true :=
  fin_run (runOK_init (prmOK_of_and H652_fin) true) (by decide) rfl H652_fin ptTest_fst
theorem I652_fin : (prmOK pI652 652 && intTest pI652 (runFrom pI652 (fmask pI652) (cmask pI652) (hmask pI652) 1 651 (true, (init pI652), (init pI652))) 652 15 true) = true := by
  decide +kernel
theorem I652_ok : RunOK pI652 652 (runFrom pI652 (fmask pI652) (cmask pI652) (hmask pI652) 1 651 (true, (init pI652), (init pI652))) ∧ intTest pI652 (runFrom pI652 (fmask pI652) (cmask pI652) (hmask pI652) 1 651 (true, (init pI652), (init pI652))) 652 15 true = true :=
  fin_run (runOK_init (prmOK_of_and I652_fin) true) (by decide) rfl I652_fin intTest_fst
theorem link652 : linkOK pL652 pH652 pI652 = true := by decide +kernel
theorem cvx652 : ConvexBetweenHumps 652 :=
  cvx_of L652_ok H652_ok I652_ok link652 (by decide)
theorem cenlink652 : cenLinkOK pI652 652 = true := by decide +kernel
theorem cen652 : CenterUniqueMin 652 ∧ DipHyp 652 ∧ OnePointHyps 652 :=
  cen_of L652_ok H652_ok I652_ok link652 cenlink652

/-! ### `N = 653` -/

def pL653 : Prm := ⟨72, 34, 35, 655, 11, 18446744073709551616, 241550798067738053, 241550798067738053⟩
def pH653 : Prm := ⟨72, 34, 35, 655, 11, 18446744073709551616, 241555196114249157, 241555196114249157⟩
def pI653 : Prm := ⟨63, 30, 30, 655, 11, 18446744073709551616, 241550798067738053, 241555196114249157⟩
theorem L653_fin : (prmOK pL653 653 && ptTest pL653 (runFrom pL653 (fmask pL653) (cmask pL653) (hmask pL653) 1 652 (true, (init pL653), (init pL653))) 653 327 false) = true := by
  decide +kernel
theorem L653_ok : RunOK pL653 653 (runFrom pL653 (fmask pL653) (cmask pL653) (hmask pL653) 1 652 (true, (init pL653), (init pL653))) ∧ ptTest pL653 (runFrom pL653 (fmask pL653) (cmask pL653) (hmask pL653) 1 652 (true, (init pL653), (init pL653))) 653 327 false = true :=
  fin_run (runOK_init (prmOK_of_and L653_fin) true) (by decide) rfl L653_fin ptTest_fst
theorem H653_fin : (prmOK pH653 653 && ptTest pH653 (runFrom pH653 (fmask pH653) (cmask pH653) (hmask pH653) 1 652 (true, (init pH653), (init pH653))) 653 327 true) = true := by
  decide +kernel
theorem H653_ok : RunOK pH653 653 (runFrom pH653 (fmask pH653) (cmask pH653) (hmask pH653) 1 652 (true, (init pH653), (init pH653))) ∧ ptTest pH653 (runFrom pH653 (fmask pH653) (cmask pH653) (hmask pH653) 1 652 (true, (init pH653), (init pH653))) 653 327 true = true :=
  fin_run (runOK_init (prmOK_of_and H653_fin) true) (by decide) rfl H653_fin ptTest_fst
theorem I653_fin : (prmOK pI653 653 && intTest pI653 (runFrom pI653 (fmask pI653) (cmask pI653) (hmask pI653) 1 652 (true, (init pI653), (init pI653))) 653 16 false) = true := by
  decide +kernel
theorem I653_ok : RunOK pI653 653 (runFrom pI653 (fmask pI653) (cmask pI653) (hmask pI653) 1 652 (true, (init pI653), (init pI653))) ∧ intTest pI653 (runFrom pI653 (fmask pI653) (cmask pI653) (hmask pI653) 1 652 (true, (init pI653), (init pI653))) 653 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I653_fin) true) (by decide) rfl I653_fin intTest_fst
theorem link653 : linkOK pL653 pH653 pI653 = true := by decide +kernel
theorem cvx653 : ConvexBetweenHumps 653 :=
  cvx_of L653_ok H653_ok I653_ok link653 (by decide)

/-! ### `N = 654` -/

def pL654 : Prm := ⟨72, 34, 35, 656, 11, 18446744073709551616, 241262979399597382, 241262979399597382⟩
def pH654 : Prm := ⟨72, 34, 35, 656, 11, 18446744073709551616, 241267377446108486, 241267377446108486⟩
def pI654 : Prm := ⟨63, 30, 30, 656, 11, 18446744073709551616, 241262979399597382, 241267377446108486⟩
theorem L654_fin : (prmOK pL654 654 && ptTest pL654 (runFrom pL654 (fmask pL654) (cmask pL654) (hmask pL654) 1 653 (true, (init pL654), (init pL654))) 654 327 false) = true := by
  decide +kernel
theorem L654_ok : RunOK pL654 654 (runFrom pL654 (fmask pL654) (cmask pL654) (hmask pL654) 1 653 (true, (init pL654), (init pL654))) ∧ ptTest pL654 (runFrom pL654 (fmask pL654) (cmask pL654) (hmask pL654) 1 653 (true, (init pL654), (init pL654))) 654 327 false = true :=
  fin_run (runOK_init (prmOK_of_and L654_fin) true) (by decide) rfl L654_fin ptTest_fst
theorem H654_fin : (prmOK pH654 654 && ptTest pH654 (runFrom pH654 (fmask pH654) (cmask pH654) (hmask pH654) 1 653 (true, (init pH654), (init pH654))) 654 327 true) = true := by
  decide +kernel
theorem H654_ok : RunOK pH654 654 (runFrom pH654 (fmask pH654) (cmask pH654) (hmask pH654) 1 653 (true, (init pH654), (init pH654))) ∧ ptTest pH654 (runFrom pH654 (fmask pH654) (cmask pH654) (hmask pH654) 1 653 (true, (init pH654), (init pH654))) 654 327 true = true :=
  fin_run (runOK_init (prmOK_of_and H654_fin) true) (by decide) rfl H654_fin ptTest_fst
theorem I654_fin : (prmOK pI654 654 && intTest pI654 (runFrom pI654 (fmask pI654) (cmask pI654) (hmask pI654) 1 653 (true, (init pI654), (init pI654))) 654 16 true) = true := by
  decide +kernel
theorem I654_ok : RunOK pI654 654 (runFrom pI654 (fmask pI654) (cmask pI654) (hmask pI654) 1 653 (true, (init pI654), (init pI654))) ∧ intTest pI654 (runFrom pI654 (fmask pI654) (cmask pI654) (hmask pI654) 1 653 (true, (init pI654), (init pI654))) 654 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I654_fin) true) (by decide) rfl I654_fin intTest_fst
theorem link654 : linkOK pL654 pH654 pI654 = true := by decide +kernel
theorem cvx654 : ConvexBetweenHumps 654 :=
  cvx_of L654_ok H654_ok I654_ok link654 (by decide)
theorem cenlink654 : cenLinkOK pI654 654 = true := by decide +kernel
theorem cen654 : CenterUniqueMin 654 ∧ DipHyp 654 ∧ OnePointHyps 654 :=
  cen_of L654_ok H654_ok I654_ok link654 cenlink654

/-! ### `N = 655` -/

def pL655 : Prm := ⟨72, 34, 35, 657, 11, 18446744073709551616, 240975493874526487, 240975493874526487⟩
def pH655 : Prm := ⟨72, 34, 35, 657, 11, 18446744073709551616, 240979891921037591, 240979891921037591⟩
def pI655 : Prm := ⟨63, 30, 30, 657, 11, 18446744073709551616, 240975493874526487, 240979891921037591⟩
theorem L655_fin : (prmOK pL655 655 && ptTest pL655 (runFrom pL655 (fmask pL655) (cmask pL655) (hmask pL655) 1 654 (true, (init pL655), (init pL655))) 655 328 false) = true := by
  decide +kernel
theorem L655_ok : RunOK pL655 655 (runFrom pL655 (fmask pL655) (cmask pL655) (hmask pL655) 1 654 (true, (init pL655), (init pL655))) ∧ ptTest pL655 (runFrom pL655 (fmask pL655) (cmask pL655) (hmask pL655) 1 654 (true, (init pL655), (init pL655))) 655 328 false = true :=
  fin_run (runOK_init (prmOK_of_and L655_fin) true) (by decide) rfl L655_fin ptTest_fst
theorem H655_fin : (prmOK pH655 655 && ptTest pH655 (runFrom pH655 (fmask pH655) (cmask pH655) (hmask pH655) 1 654 (true, (init pH655), (init pH655))) 655 328 true) = true := by
  decide +kernel
theorem H655_ok : RunOK pH655 655 (runFrom pH655 (fmask pH655) (cmask pH655) (hmask pH655) 1 654 (true, (init pH655), (init pH655))) ∧ ptTest pH655 (runFrom pH655 (fmask pH655) (cmask pH655) (hmask pH655) 1 654 (true, (init pH655), (init pH655))) 655 328 true = true :=
  fin_run (runOK_init (prmOK_of_and H655_fin) true) (by decide) rfl H655_fin ptTest_fst
theorem I655_fin : (prmOK pI655 655 && intTest pI655 (runFrom pI655 (fmask pI655) (cmask pI655) (hmask pI655) 1 654 (true, (init pI655), (init pI655))) 655 16 false) = true := by
  decide +kernel
theorem I655_ok : RunOK pI655 655 (runFrom pI655 (fmask pI655) (cmask pI655) (hmask pI655) 1 654 (true, (init pI655), (init pI655))) ∧ intTest pI655 (runFrom pI655 (fmask pI655) (cmask pI655) (hmask pI655) 1 654 (true, (init pI655), (init pI655))) 655 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I655_fin) true) (by decide) rfl I655_fin intTest_fst
theorem link655 : linkOK pL655 pH655 pI655 = true := by decide +kernel
theorem cvx655 : ConvexBetweenHumps 655 :=
  cvx_of L655_ok H655_ok I655_ok link655 (by decide)

/-! ### `N = 656` -/

def pL656 : Prm := ⟨72, 34, 35, 658, 11, 18446744073709551616, 240689182227697399, 240689182227697399⟩
def pH656 : Prm := ⟨72, 34, 35, 658, 11, 18446744073709551616, 240693580274208503, 240693580274208503⟩
def pI656 : Prm := ⟨63, 30, 30, 658, 11, 18446744073709551616, 240689182227697399, 240693580274208503⟩
theorem L656_fin : (prmOK pL656 656 && ptTest pL656 (runFrom pL656 (fmask pL656) (cmask pL656) (hmask pL656) 1 655 (true, (init pL656), (init pL656))) 656 328 false) = true := by
  decide +kernel
theorem L656_ok : RunOK pL656 656 (runFrom pL656 (fmask pL656) (cmask pL656) (hmask pL656) 1 655 (true, (init pL656), (init pL656))) ∧ ptTest pL656 (runFrom pL656 (fmask pL656) (cmask pL656) (hmask pL656) 1 655 (true, (init pL656), (init pL656))) 656 328 false = true :=
  fin_run (runOK_init (prmOK_of_and L656_fin) true) (by decide) rfl L656_fin ptTest_fst
theorem H656_fin : (prmOK pH656 656 && ptTest pH656 (runFrom pH656 (fmask pH656) (cmask pH656) (hmask pH656) 1 655 (true, (init pH656), (init pH656))) 656 328 true) = true := by
  decide +kernel
theorem H656_ok : RunOK pH656 656 (runFrom pH656 (fmask pH656) (cmask pH656) (hmask pH656) 1 655 (true, (init pH656), (init pH656))) ∧ ptTest pH656 (runFrom pH656 (fmask pH656) (cmask pH656) (hmask pH656) 1 655 (true, (init pH656), (init pH656))) 656 328 true = true :=
  fin_run (runOK_init (prmOK_of_and H656_fin) true) (by decide) rfl H656_fin ptTest_fst
theorem I656_fin : (prmOK pI656 656 && intTest pI656 (runFrom pI656 (fmask pI656) (cmask pI656) (hmask pI656) 1 655 (true, (init pI656), (init pI656))) 656 16 true) = true := by
  decide +kernel
theorem I656_ok : RunOK pI656 656 (runFrom pI656 (fmask pI656) (cmask pI656) (hmask pI656) 1 655 (true, (init pI656), (init pI656))) ∧ intTest pI656 (runFrom pI656 (fmask pI656) (cmask pI656) (hmask pI656) 1 655 (true, (init pI656), (init pI656))) 656 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I656_fin) true) (by decide) rfl I656_fin intTest_fst
theorem link656 : linkOK pL656 pH656 pI656 = true := by decide +kernel
theorem cvx656 : ConvexBetweenHumps 656 :=
  cvx_of L656_ok H656_ok I656_ok link656 (by decide)
theorem cenlink656 : cenLinkOK pI656 656 = true := by decide +kernel
theorem cen656 : CenterUniqueMin 656 ∧ DipHyp 656 ∧ OnePointHyps 656 :=
  cen_of L656_ok H656_ok I656_ok link656 cenlink656

/-! ### `N = 657` -/

def pL657 : Prm := ⟨72, 34, 35, 659, 11, 18446744073709551616, 240403201495386936, 240403201495386936⟩
def pH657 : Prm := ⟨72, 34, 35, 659, 11, 18446744073709551616, 240407599541898040, 240407599541898040⟩
def pI657 : Prm := ⟨63, 30, 30, 659, 11, 18446744073709551616, 240403201495386936, 240407599541898040⟩
theorem L657_fin : (prmOK pL657 657 && ptTest pL657 (runFrom pL657 (fmask pL657) (cmask pL657) (hmask pL657) 1 656 (true, (init pL657), (init pL657))) 657 329 false) = true := by
  decide +kernel
theorem L657_ok : RunOK pL657 657 (runFrom pL657 (fmask pL657) (cmask pL657) (hmask pL657) 1 656 (true, (init pL657), (init pL657))) ∧ ptTest pL657 (runFrom pL657 (fmask pL657) (cmask pL657) (hmask pL657) 1 656 (true, (init pL657), (init pL657))) 657 329 false = true :=
  fin_run (runOK_init (prmOK_of_and L657_fin) true) (by decide) rfl L657_fin ptTest_fst
theorem H657_fin : (prmOK pH657 657 && ptTest pH657 (runFrom pH657 (fmask pH657) (cmask pH657) (hmask pH657) 1 656 (true, (init pH657), (init pH657))) 657 329 true) = true := by
  decide +kernel
theorem H657_ok : RunOK pH657 657 (runFrom pH657 (fmask pH657) (cmask pH657) (hmask pH657) 1 656 (true, (init pH657), (init pH657))) ∧ ptTest pH657 (runFrom pH657 (fmask pH657) (cmask pH657) (hmask pH657) 1 656 (true, (init pH657), (init pH657))) 657 329 true = true :=
  fin_run (runOK_init (prmOK_of_and H657_fin) true) (by decide) rfl H657_fin ptTest_fst
theorem I657_fin : (prmOK pI657 657 && intTest pI657 (runFrom pI657 (fmask pI657) (cmask pI657) (hmask pI657) 1 656 (true, (init pI657), (init pI657))) 657 16 false) = true := by
  decide +kernel
theorem I657_ok : RunOK pI657 657 (runFrom pI657 (fmask pI657) (cmask pI657) (hmask pI657) 1 656 (true, (init pI657), (init pI657))) ∧ intTest pI657 (runFrom pI657 (fmask pI657) (cmask pI657) (hmask pI657) 1 656 (true, (init pI657), (init pI657))) 657 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I657_fin) true) (by decide) rfl I657_fin intTest_fst
theorem link657 : linkOK pL657 pH657 pI657 = true := by decide +kernel
theorem cvx657 : ConvexBetweenHumps 657 :=
  cvx_of L657_ok H657_ok I657_ok link657 (by decide)

/-! ### `N = 658` -/

def pL658 : Prm := ⟨72, 34, 35, 660, 11, 18446744073709551616, 240118384621674087, 240118384621674087⟩
def pH658 : Prm := ⟨72, 34, 35, 660, 11, 18446744073709551616, 240122782668185191, 240122782668185191⟩
def pI658 : Prm := ⟨63, 30, 30, 660, 11, 18446744073709551616, 240118384621674087, 240122782668185191⟩
theorem L658_fin : (prmOK pL658 658 && ptTest pL658 (runFrom pL658 (fmask pL658) (cmask pL658) (hmask pL658) 1 657 (true, (init pL658), (init pL658))) 658 329 false) = true := by
  decide +kernel
theorem L658_ok : RunOK pL658 658 (runFrom pL658 (fmask pL658) (cmask pL658) (hmask pL658) 1 657 (true, (init pL658), (init pL658))) ∧ ptTest pL658 (runFrom pL658 (fmask pL658) (cmask pL658) (hmask pL658) 1 657 (true, (init pL658), (init pL658))) 658 329 false = true :=
  fin_run (runOK_init (prmOK_of_and L658_fin) true) (by decide) rfl L658_fin ptTest_fst
theorem H658_fin : (prmOK pH658 658 && ptTest pH658 (runFrom pH658 (fmask pH658) (cmask pH658) (hmask pH658) 1 657 (true, (init pH658), (init pH658))) 658 329 true) = true := by
  decide +kernel
theorem H658_ok : RunOK pH658 658 (runFrom pH658 (fmask pH658) (cmask pH658) (hmask pH658) 1 657 (true, (init pH658), (init pH658))) ∧ ptTest pH658 (runFrom pH658 (fmask pH658) (cmask pH658) (hmask pH658) 1 657 (true, (init pH658), (init pH658))) 658 329 true = true :=
  fin_run (runOK_init (prmOK_of_and H658_fin) true) (by decide) rfl H658_fin ptTest_fst
theorem I658_fin : (prmOK pI658 658 && intTest pI658 (runFrom pI658 (fmask pI658) (cmask pI658) (hmask pI658) 1 657 (true, (init pI658), (init pI658))) 658 16 true) = true := by
  decide +kernel
theorem I658_ok : RunOK pI658 658 (runFrom pI658 (fmask pI658) (cmask pI658) (hmask pI658) 1 657 (true, (init pI658), (init pI658))) ∧ intTest pI658 (runFrom pI658 (fmask pI658) (cmask pI658) (hmask pI658) 1 657 (true, (init pI658), (init pI658))) 658 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I658_fin) true) (by decide) rfl I658_fin intTest_fst
theorem link658 : linkOK pL658 pH658 pI658 = true := by decide +kernel
theorem cvx658 : ConvexBetweenHumps 658 :=
  cvx_of L658_ok H658_ok I658_ok link658 (by decide)
theorem cenlink658 : cenLinkOK pI658 658 = true := by decide +kernel
theorem cen658 : CenterUniqueMin 658 ∧ DipHyp 658 ∧ OnePointHyps 658 :=
  cen_of L658_ok H658_ok I658_ok link658 cenlink658

/-! ### `N = 659` -/

def pL659 : Prm := ⟨72, 34, 35, 661, 11, 18446744073709551616, 239833896453740515, 239833896453740515⟩
def pH659 : Prm := ⟨72, 34, 35, 661, 11, 18446744073709551616, 239838294500251619, 239838294500251619⟩
def pI659 : Prm := ⟨63, 30, 30, 661, 11, 18446744073709551616, 239833896453740515, 239838294500251619⟩
theorem L659_fin : (prmOK pL659 659 && ptTest pL659 (runFrom pL659 (fmask pL659) (cmask pL659) (hmask pL659) 1 658 (true, (init pL659), (init pL659))) 659 330 false) = true := by
  decide +kernel
theorem L659_ok : RunOK pL659 659 (runFrom pL659 (fmask pL659) (cmask pL659) (hmask pL659) 1 658 (true, (init pL659), (init pL659))) ∧ ptTest pL659 (runFrom pL659 (fmask pL659) (cmask pL659) (hmask pL659) 1 658 (true, (init pL659), (init pL659))) 659 330 false = true :=
  fin_run (runOK_init (prmOK_of_and L659_fin) true) (by decide) rfl L659_fin ptTest_fst
theorem H659_fin : (prmOK pH659 659 && ptTest pH659 (runFrom pH659 (fmask pH659) (cmask pH659) (hmask pH659) 1 658 (true, (init pH659), (init pH659))) 659 330 true) = true := by
  decide +kernel
theorem H659_ok : RunOK pH659 659 (runFrom pH659 (fmask pH659) (cmask pH659) (hmask pH659) 1 658 (true, (init pH659), (init pH659))) ∧ ptTest pH659 (runFrom pH659 (fmask pH659) (cmask pH659) (hmask pH659) 1 658 (true, (init pH659), (init pH659))) 659 330 true = true :=
  fin_run (runOK_init (prmOK_of_and H659_fin) true) (by decide) rfl H659_fin ptTest_fst
theorem I659_fin : (prmOK pI659 659 && intTest pI659 (runFrom pI659 (fmask pI659) (cmask pI659) (hmask pI659) 1 658 (true, (init pI659), (init pI659))) 659 16 false) = true := by
  decide +kernel
theorem I659_ok : RunOK pI659 659 (runFrom pI659 (fmask pI659) (cmask pI659) (hmask pI659) 1 658 (true, (init pI659), (init pI659))) ∧ intTest pI659 (runFrom pI659 (fmask pI659) (cmask pI659) (hmask pI659) 1 658 (true, (init pI659), (init pI659))) 659 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I659_fin) true) (by decide) rfl I659_fin intTest_fst
theorem link659 : linkOK pL659 pH659 pI659 = true := by decide +kernel
theorem cvx659 : ConvexBetweenHumps 659 :=
  cvx_of L659_ok H659_ok I659_ok link659 (by decide)

/-! ### `N = 660` -/

def pL660 : Prm := ⟨72, 34, 35, 662, 11, 18446744073709551616, 239550562240015623, 239550562240015623⟩
def pH660 : Prm := ⟨72, 34, 35, 662, 11, 18446744073709551616, 239554960286526727, 239554960286526727⟩
def pI660 : Prm := ⟨63, 30, 30, 662, 11, 18446744073709551616, 239550562240015623, 239554960286526727⟩
theorem L660_fin : (prmOK pL660 660 && ptTest pL660 (runFrom pL660 (fmask pL660) (cmask pL660) (hmask pL660) 1 659 (true, (init pL660), (init pL660))) 660 330 false) = true := by
  decide +kernel
theorem L660_ok : RunOK pL660 660 (runFrom pL660 (fmask pL660) (cmask pL660) (hmask pL660) 1 659 (true, (init pL660), (init pL660))) ∧ ptTest pL660 (runFrom pL660 (fmask pL660) (cmask pL660) (hmask pL660) 1 659 (true, (init pL660), (init pL660))) 660 330 false = true :=
  fin_run (runOK_init (prmOK_of_and L660_fin) true) (by decide) rfl L660_fin ptTest_fst
theorem H660_fin : (prmOK pH660 660 && ptTest pH660 (runFrom pH660 (fmask pH660) (cmask pH660) (hmask pH660) 1 659 (true, (init pH660), (init pH660))) 660 330 true) = true := by
  decide +kernel
theorem H660_ok : RunOK pH660 660 (runFrom pH660 (fmask pH660) (cmask pH660) (hmask pH660) 1 659 (true, (init pH660), (init pH660))) ∧ ptTest pH660 (runFrom pH660 (fmask pH660) (cmask pH660) (hmask pH660) 1 659 (true, (init pH660), (init pH660))) 660 330 true = true :=
  fin_run (runOK_init (prmOK_of_and H660_fin) true) (by decide) rfl H660_fin ptTest_fst
theorem I660_fin : (prmOK pI660 660 && intTest pI660 (runFrom pI660 (fmask pI660) (cmask pI660) (hmask pI660) 1 659 (true, (init pI660), (init pI660))) 660 16 true) = true := by
  decide +kernel
theorem I660_ok : RunOK pI660 660 (runFrom pI660 (fmask pI660) (cmask pI660) (hmask pI660) 1 659 (true, (init pI660), (init pI660))) ∧ intTest pI660 (runFrom pI660 (fmask pI660) (cmask pI660) (hmask pI660) 1 659 (true, (init pI660), (init pI660))) 660 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I660_fin) true) (by decide) rfl I660_fin intTest_fst
theorem link660 : linkOK pL660 pH660 pI660 = true := by decide +kernel
theorem cvx660 : ConvexBetweenHumps 660 :=
  cvx_of L660_ok H660_ok I660_ok link660 (by decide)
theorem cenlink660 : cenLinkOK pI660 660 = true := by decide +kernel
theorem cen660 : CenterUniqueMin 660 ∧ DipHyp 660 ∧ OnePointHyps 660 :=
  cen_of L660_ok H660_ok I660_ok link660 cenlink660

/-! ### `N = 661` -/

def pL661 : Prm := ⟨72, 34, 35, 663, 11, 18446744073709551616, 239267554542902655, 239267554542902655⟩
def pH661 : Prm := ⟨72, 34, 35, 663, 11, 18446744073709551616, 239271952589413759, 239271952589413759⟩
def pI661 : Prm := ⟨63, 30, 30, 663, 11, 18446744073709551616, 239267554542902655, 239271952589413759⟩
theorem L661_fin : (prmOK pL661 661 && ptTest pL661 (runFrom pL661 (fmask pL661) (cmask pL661) (hmask pL661) 1 660 (true, (init pL661), (init pL661))) 661 331 false) = true := by
  decide +kernel
theorem L661_ok : RunOK pL661 661 (runFrom pL661 (fmask pL661) (cmask pL661) (hmask pL661) 1 660 (true, (init pL661), (init pL661))) ∧ ptTest pL661 (runFrom pL661 (fmask pL661) (cmask pL661) (hmask pL661) 1 660 (true, (init pL661), (init pL661))) 661 331 false = true :=
  fin_run (runOK_init (prmOK_of_and L661_fin) true) (by decide) rfl L661_fin ptTest_fst
theorem H661_fin : (prmOK pH661 661 && ptTest pH661 (runFrom pH661 (fmask pH661) (cmask pH661) (hmask pH661) 1 660 (true, (init pH661), (init pH661))) 661 331 true) = true := by
  decide +kernel
theorem H661_ok : RunOK pH661 661 (runFrom pH661 (fmask pH661) (cmask pH661) (hmask pH661) 1 660 (true, (init pH661), (init pH661))) ∧ ptTest pH661 (runFrom pH661 (fmask pH661) (cmask pH661) (hmask pH661) 1 660 (true, (init pH661), (init pH661))) 661 331 true = true :=
  fin_run (runOK_init (prmOK_of_and H661_fin) true) (by decide) rfl H661_fin ptTest_fst
theorem I661_fin : (prmOK pI661 661 && intTest pI661 (runFrom pI661 (fmask pI661) (cmask pI661) (hmask pI661) 1 660 (true, (init pI661), (init pI661))) 661 16 false) = true := by
  decide +kernel
theorem I661_ok : RunOK pI661 661 (runFrom pI661 (fmask pI661) (cmask pI661) (hmask pI661) 1 660 (true, (init pI661), (init pI661))) ∧ intTest pI661 (runFrom pI661 (fmask pI661) (cmask pI661) (hmask pI661) 1 660 (true, (init pI661), (init pI661))) 661 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I661_fin) true) (by decide) rfl I661_fin intTest_fst
theorem link661 : linkOK pL661 pH661 pI661 = true := by decide +kernel
theorem cvx661 : ConvexBetweenHumps 661 :=
  cvx_of L661_ok H661_ok I661_ok link661 (by decide)

/-! ### `N = 662` -/

def pL662 : Prm := ⟨72, 34, 35, 664, 11, 18446744073709551616, 238985691009204482, 238985691009204482⟩
def pH662 : Prm := ⟨72, 34, 35, 664, 11, 18446744073709551616, 238990089055715586, 238990089055715586⟩
def pI662 : Prm := ⟨62, 31, 28, 664, 11, 18446744073709551616, 238985691009204482, 238990089055715586⟩
theorem L662_fin : (prmOK pL662 662 && ptTest pL662 (runFrom pL662 (fmask pL662) (cmask pL662) (hmask pL662) 1 661 (true, (init pL662), (init pL662))) 662 331 false) = true := by
  decide +kernel
theorem L662_ok : RunOK pL662 662 (runFrom pL662 (fmask pL662) (cmask pL662) (hmask pL662) 1 661 (true, (init pL662), (init pL662))) ∧ ptTest pL662 (runFrom pL662 (fmask pL662) (cmask pL662) (hmask pL662) 1 661 (true, (init pL662), (init pL662))) 662 331 false = true :=
  fin_run (runOK_init (prmOK_of_and L662_fin) true) (by decide) rfl L662_fin ptTest_fst
theorem H662_fin : (prmOK pH662 662 && ptTest pH662 (runFrom pH662 (fmask pH662) (cmask pH662) (hmask pH662) 1 661 (true, (init pH662), (init pH662))) 662 331 true) = true := by
  decide +kernel
theorem H662_ok : RunOK pH662 662 (runFrom pH662 (fmask pH662) (cmask pH662) (hmask pH662) 1 661 (true, (init pH662), (init pH662))) ∧ ptTest pH662 (runFrom pH662 (fmask pH662) (cmask pH662) (hmask pH662) 1 661 (true, (init pH662), (init pH662))) 662 331 true = true :=
  fin_run (runOK_init (prmOK_of_and H662_fin) true) (by decide) rfl H662_fin ptTest_fst
theorem I662_fin : (prmOK pI662 662 && intTest pI662 (runFrom pI662 (fmask pI662) (cmask pI662) (hmask pI662) 1 661 (true, (init pI662), (init pI662))) 662 16 true) = true := by
  decide +kernel
theorem I662_ok : RunOK pI662 662 (runFrom pI662 (fmask pI662) (cmask pI662) (hmask pI662) 1 661 (true, (init pI662), (init pI662))) ∧ intTest pI662 (runFrom pI662 (fmask pI662) (cmask pI662) (hmask pI662) 1 661 (true, (init pI662), (init pI662))) 662 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I662_fin) true) (by decide) rfl I662_fin intTest_fst
theorem link662 : linkOK pL662 pH662 pI662 = true := by decide +kernel
theorem cvx662 : ConvexBetweenHumps 662 :=
  cvx_of L662_ok H662_ok I662_ok link662 (by decide)
theorem cenlink662 : cenLinkOK pI662 662 = true := by decide +kernel
theorem cen662 : CenterUniqueMin 662 ∧ DipHyp 662 ∧ OnePointHyps 662 :=
  cen_of L662_ok H662_ok I662_ok link662 cenlink662

/-! ### `N = 663` -/

def pL663 : Prm := ⟨72, 34, 35, 665, 11, 18446744073709551616, 238704151822319961, 238704151822319961⟩
def pH663 : Prm := ⟨72, 34, 35, 665, 11, 18446744073709551616, 238708549868831065, 238708549868831065⟩
def pI663 : Prm := ⟨61, 31, 27, 665, 11, 18446744073709551616, 238704151822319961, 238708549868831065⟩
theorem L663_fin : (prmOK pL663 663 && ptTest pL663 (runFrom pL663 (fmask pL663) (cmask pL663) (hmask pL663) 1 662 (true, (init pL663), (init pL663))) 663 332 false) = true := by
  decide +kernel
theorem L663_ok : RunOK pL663 663 (runFrom pL663 (fmask pL663) (cmask pL663) (hmask pL663) 1 662 (true, (init pL663), (init pL663))) ∧ ptTest pL663 (runFrom pL663 (fmask pL663) (cmask pL663) (hmask pL663) 1 662 (true, (init pL663), (init pL663))) 663 332 false = true :=
  fin_run (runOK_init (prmOK_of_and L663_fin) true) (by decide) rfl L663_fin ptTest_fst
theorem H663_fin : (prmOK pH663 663 && ptTest pH663 (runFrom pH663 (fmask pH663) (cmask pH663) (hmask pH663) 1 662 (true, (init pH663), (init pH663))) 663 332 true) = true := by
  decide +kernel
theorem H663_ok : RunOK pH663 663 (runFrom pH663 (fmask pH663) (cmask pH663) (hmask pH663) 1 662 (true, (init pH663), (init pH663))) ∧ ptTest pH663 (runFrom pH663 (fmask pH663) (cmask pH663) (hmask pH663) 1 662 (true, (init pH663), (init pH663))) 663 332 true = true :=
  fin_run (runOK_init (prmOK_of_and H663_fin) true) (by decide) rfl H663_fin ptTest_fst
theorem I663_fin : (prmOK pI663 663 && intTest pI663 (runFrom pI663 (fmask pI663) (cmask pI663) (hmask pI663) 1 662 (true, (init pI663), (init pI663))) 663 16 false) = true := by
  decide +kernel
theorem I663_ok : RunOK pI663 663 (runFrom pI663 (fmask pI663) (cmask pI663) (hmask pI663) 1 662 (true, (init pI663), (init pI663))) ∧ intTest pI663 (runFrom pI663 (fmask pI663) (cmask pI663) (hmask pI663) 1 662 (true, (init pI663), (init pI663))) 663 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I663_fin) true) (by decide) rfl I663_fin intTest_fst
theorem link663 : linkOK pL663 pH663 pI663 = true := by decide +kernel
theorem cvx663 : ConvexBetweenHumps 663 :=
  cvx_of L663_ok H663_ok I663_ok link663 (by decide)

/-! ### `N = 664` -/

def pL664 : Prm := ⟨72, 34, 35, 666, 11, 18446744073709551616, 238423747120046535, 238423747120046535⟩
def pH664 : Prm := ⟨72, 34, 35, 666, 11, 18446744073709551616, 238428145166557639, 238428145166557639⟩
def pI664 : Prm := ⟨62, 30, 29, 666, 11, 18446744073709551616, 238423747120046535, 238428145166557639⟩
theorem L664_fin : (prmOK pL664 664 && ptTest pL664 (runFrom pL664 (fmask pL664) (cmask pL664) (hmask pL664) 1 663 (true, (init pL664), (init pL664))) 664 332 false) = true := by
  decide +kernel
theorem L664_ok : RunOK pL664 664 (runFrom pL664 (fmask pL664) (cmask pL664) (hmask pL664) 1 663 (true, (init pL664), (init pL664))) ∧ ptTest pL664 (runFrom pL664 (fmask pL664) (cmask pL664) (hmask pL664) 1 663 (true, (init pL664), (init pL664))) 664 332 false = true :=
  fin_run (runOK_init (prmOK_of_and L664_fin) true) (by decide) rfl L664_fin ptTest_fst
theorem H664_fin : (prmOK pH664 664 && ptTest pH664 (runFrom pH664 (fmask pH664) (cmask pH664) (hmask pH664) 1 663 (true, (init pH664), (init pH664))) 664 332 true) = true := by
  decide +kernel
theorem H664_ok : RunOK pH664 664 (runFrom pH664 (fmask pH664) (cmask pH664) (hmask pH664) 1 663 (true, (init pH664), (init pH664))) ∧ ptTest pH664 (runFrom pH664 (fmask pH664) (cmask pH664) (hmask pH664) 1 663 (true, (init pH664), (init pH664))) 664 332 true = true :=
  fin_run (runOK_init (prmOK_of_and H664_fin) true) (by decide) rfl H664_fin ptTest_fst
theorem I664_fin : (prmOK pI664 664 && intTest pI664 (runFrom pI664 (fmask pI664) (cmask pI664) (hmask pI664) 1 663 (true, (init pI664), (init pI664))) 664 16 true) = true := by
  decide +kernel
theorem I664_ok : RunOK pI664 664 (runFrom pI664 (fmask pI664) (cmask pI664) (hmask pI664) 1 663 (true, (init pI664), (init pI664))) ∧ intTest pI664 (runFrom pI664 (fmask pI664) (cmask pI664) (hmask pI664) 1 663 (true, (init pI664), (init pI664))) 664 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I664_fin) true) (by decide) rfl I664_fin intTest_fst
theorem link664 : linkOK pL664 pH664 pI664 = true := by decide +kernel
theorem cvx664 : ConvexBetweenHumps 664 :=
  cvx_of L664_ok H664_ok I664_ok link664 (by decide)
theorem cenlink664 : cenLinkOK pI664 664 = true := by decide +kernel
theorem cen664 : CenterUniqueMin 664 ∧ DipHyp 664 ∧ OnePointHyps 664 :=
  cen_of L664_ok H664_ok I664_ok link664 cenlink664

/-! ### `N = 665` -/

def pL665 : Prm := ⟨72, 34, 35, 667, 11, 18446744073709551616, 238143664613936209, 238143664613936209⟩
def pH665 : Prm := ⟨72, 34, 35, 667, 11, 18446744073709551616, 238148062660447313, 238148062660447313⟩
def pI665 : Prm := ⟨62, 30, 29, 667, 11, 18446744073709551616, 238143664613936209, 238148062660447313⟩
theorem L665_fin : (prmOK pL665 665 && ptTest pL665 (runFrom pL665 (fmask pL665) (cmask pL665) (hmask pL665) 1 664 (true, (init pL665), (init pL665))) 665 333 false) = true := by
  decide +kernel
theorem L665_ok : RunOK pL665 665 (runFrom pL665 (fmask pL665) (cmask pL665) (hmask pL665) 1 664 (true, (init pL665), (init pL665))) ∧ ptTest pL665 (runFrom pL665 (fmask pL665) (cmask pL665) (hmask pL665) 1 664 (true, (init pL665), (init pL665))) 665 333 false = true :=
  fin_run (runOK_init (prmOK_of_and L665_fin) true) (by decide) rfl L665_fin ptTest_fst
theorem H665_fin : (prmOK pH665 665 && ptTest pH665 (runFrom pH665 (fmask pH665) (cmask pH665) (hmask pH665) 1 664 (true, (init pH665), (init pH665))) 665 333 true) = true := by
  decide +kernel
theorem H665_ok : RunOK pH665 665 (runFrom pH665 (fmask pH665) (cmask pH665) (hmask pH665) 1 664 (true, (init pH665), (init pH665))) ∧ ptTest pH665 (runFrom pH665 (fmask pH665) (cmask pH665) (hmask pH665) 1 664 (true, (init pH665), (init pH665))) 665 333 true = true :=
  fin_run (runOK_init (prmOK_of_and H665_fin) true) (by decide) rfl H665_fin ptTest_fst
theorem I665_fin : (prmOK pI665 665 && intTest pI665 (runFrom pI665 (fmask pI665) (cmask pI665) (hmask pI665) 1 664 (true, (init pI665), (init pI665))) 665 16 false) = true := by
  decide +kernel
theorem I665_ok : RunOK pI665 665 (runFrom pI665 (fmask pI665) (cmask pI665) (hmask pI665) 1 664 (true, (init pI665), (init pI665))) ∧ intTest pI665 (runFrom pI665 (fmask pI665) (cmask pI665) (hmask pI665) 1 664 (true, (init pI665), (init pI665))) 665 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I665_fin) true) (by decide) rfl I665_fin intTest_fst
theorem link665 : linkOK pL665 pH665 pI665 = true := by decide +kernel
theorem cvx665 : ConvexBetweenHumps 665 :=
  cvx_of L665_ok H665_ok I665_ok link665 (by decide)

/-! ### `N = 666` -/

def pL666 : Prm := ⟨72, 34, 35, 668, 11, 18446744073709551616, 237864707023944805, 237864707023944805⟩
def pH666 : Prm := ⟨72, 34, 35, 668, 11, 18446744073709551616, 237869105070455909, 237869105070455909⟩
def pI666 : Prm := ⟨62, 30, 29, 668, 11, 18446744073709551616, 237864707023944805, 237869105070455909⟩
theorem L666_fin : (prmOK pL666 666 && ptTest pL666 (runFrom pL666 (fmask pL666) (cmask pL666) (hmask pL666) 1 665 (true, (init pL666), (init pL666))) 666 333 false) = true := by
  decide +kernel
theorem L666_ok : RunOK pL666 666 (runFrom pL666 (fmask pL666) (cmask pL666) (hmask pL666) 1 665 (true, (init pL666), (init pL666))) ∧ ptTest pL666 (runFrom pL666 (fmask pL666) (cmask pL666) (hmask pL666) 1 665 (true, (init pL666), (init pL666))) 666 333 false = true :=
  fin_run (runOK_init (prmOK_of_and L666_fin) true) (by decide) rfl L666_fin ptTest_fst
theorem H666_fin : (prmOK pH666 666 && ptTest pH666 (runFrom pH666 (fmask pH666) (cmask pH666) (hmask pH666) 1 665 (true, (init pH666), (init pH666))) 666 333 true) = true := by
  decide +kernel
theorem H666_ok : RunOK pH666 666 (runFrom pH666 (fmask pH666) (cmask pH666) (hmask pH666) 1 665 (true, (init pH666), (init pH666))) ∧ ptTest pH666 (runFrom pH666 (fmask pH666) (cmask pH666) (hmask pH666) 1 665 (true, (init pH666), (init pH666))) 666 333 true = true :=
  fin_run (runOK_init (prmOK_of_and H666_fin) true) (by decide) rfl H666_fin ptTest_fst
theorem I666_fin : (prmOK pI666 666 && intTest pI666 (runFrom pI666 (fmask pI666) (cmask pI666) (hmask pI666) 1 665 (true, (init pI666), (init pI666))) 666 16 true) = true := by
  decide +kernel
theorem I666_ok : RunOK pI666 666 (runFrom pI666 (fmask pI666) (cmask pI666) (hmask pI666) 1 665 (true, (init pI666), (init pI666))) ∧ intTest pI666 (runFrom pI666 (fmask pI666) (cmask pI666) (hmask pI666) 1 665 (true, (init pI666), (init pI666))) 666 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I666_fin) true) (by decide) rfl I666_fin intTest_fst
theorem link666 : linkOK pL666 pH666 pI666 = true := by decide +kernel
theorem cvx666 : ConvexBetweenHumps 666 :=
  cvx_of L666_ok H666_ok I666_ok link666 (by decide)
theorem cenlink666 : cenLinkOK pI666 666 = true := by decide +kernel
theorem cen666 : CenterUniqueMin 666 ∧ DipHyp 666 ∧ OnePointHyps 666 :=
  cen_of L666_ok H666_ok I666_ok link666 cenlink666

/-! ### `N = 667` -/

def pL667 : Prm := ⟨72, 34, 35, 669, 11, 18446744073709551616, 237586069498429204, 237586069498429204⟩
def pH667 : Prm := ⟨72, 34, 35, 669, 11, 18446744073709551616, 237590467544940308, 237590467544940308⟩
def pI667 : Prm := ⟨62, 30, 29, 669, 11, 18446744073709551616, 237586069498429204, 237590467544940308⟩
theorem L667_fin : (prmOK pL667 667 && ptTest pL667 (runFrom pL667 (fmask pL667) (cmask pL667) (hmask pL667) 1 666 (true, (init pL667), (init pL667))) 667 334 false) = true := by
  decide +kernel
theorem L667_ok : RunOK pL667 667 (runFrom pL667 (fmask pL667) (cmask pL667) (hmask pL667) 1 666 (true, (init pL667), (init pL667))) ∧ ptTest pL667 (runFrom pL667 (fmask pL667) (cmask pL667) (hmask pL667) 1 666 (true, (init pL667), (init pL667))) 667 334 false = true :=
  fin_run (runOK_init (prmOK_of_and L667_fin) true) (by decide) rfl L667_fin ptTest_fst
theorem H667_fin : (prmOK pH667 667 && ptTest pH667 (runFrom pH667 (fmask pH667) (cmask pH667) (hmask pH667) 1 666 (true, (init pH667), (init pH667))) 667 334 true) = true := by
  decide +kernel
theorem H667_ok : RunOK pH667 667 (runFrom pH667 (fmask pH667) (cmask pH667) (hmask pH667) 1 666 (true, (init pH667), (init pH667))) ∧ ptTest pH667 (runFrom pH667 (fmask pH667) (cmask pH667) (hmask pH667) 1 666 (true, (init pH667), (init pH667))) 667 334 true = true :=
  fin_run (runOK_init (prmOK_of_and H667_fin) true) (by decide) rfl H667_fin ptTest_fst
theorem I667_fin : (prmOK pI667 667 && intTest pI667 (runFrom pI667 (fmask pI667) (cmask pI667) (hmask pI667) 1 666 (true, (init pI667), (init pI667))) 667 16 false) = true := by
  decide +kernel
theorem I667_ok : RunOK pI667 667 (runFrom pI667 (fmask pI667) (cmask pI667) (hmask pI667) 1 666 (true, (init pI667), (init pI667))) ∧ intTest pI667 (runFrom pI667 (fmask pI667) (cmask pI667) (hmask pI667) 1 666 (true, (init pI667), (init pI667))) 667 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I667_fin) true) (by decide) rfl I667_fin intTest_fst
theorem link667 : linkOK pL667 pH667 pI667 = true := by decide +kernel
theorem cvx667 : ConvexBetweenHumps 667 :=
  cvx_of L667_ok H667_ok I667_ok link667 (by decide)

/-! ### `N = 668` -/

def pL668 : Prm := ⟨72, 34, 35, 670, 11, 18446744073709551616, 237308547429339251, 237308547429339251⟩
def pH668 : Prm := ⟨72, 34, 35, 670, 11, 18446744073709551616, 237312945475850355, 237312945475850355⟩
def pI668 : Prm := ⟨62, 30, 29, 670, 11, 18446744073709551616, 237308547429339251, 237312945475850355⟩
theorem L668_fin : (prmOK pL668 668 && ptTest pL668 (runFrom pL668 (fmask pL668) (cmask pL668) (hmask pL668) 1 667 (true, (init pL668), (init pL668))) 668 334 false) = true := by
  decide +kernel
theorem L668_ok : RunOK pL668 668 (runFrom pL668 (fmask pL668) (cmask pL668) (hmask pL668) 1 667 (true, (init pL668), (init pL668))) ∧ ptTest pL668 (runFrom pL668 (fmask pL668) (cmask pL668) (hmask pL668) 1 667 (true, (init pL668), (init pL668))) 668 334 false = true :=
  fin_run (runOK_init (prmOK_of_and L668_fin) true) (by decide) rfl L668_fin ptTest_fst
theorem H668_fin : (prmOK pH668 668 && ptTest pH668 (runFrom pH668 (fmask pH668) (cmask pH668) (hmask pH668) 1 667 (true, (init pH668), (init pH668))) 668 334 true) = true := by
  decide +kernel
theorem H668_ok : RunOK pH668 668 (runFrom pH668 (fmask pH668) (cmask pH668) (hmask pH668) 1 667 (true, (init pH668), (init pH668))) ∧ ptTest pH668 (runFrom pH668 (fmask pH668) (cmask pH668) (hmask pH668) 1 667 (true, (init pH668), (init pH668))) 668 334 true = true :=
  fin_run (runOK_init (prmOK_of_and H668_fin) true) (by decide) rfl H668_fin ptTest_fst
theorem I668_fin : (prmOK pI668 668 && intTest pI668 (runFrom pI668 (fmask pI668) (cmask pI668) (hmask pI668) 1 667 (true, (init pI668), (init pI668))) 668 16 true) = true := by
  decide +kernel
theorem I668_ok : RunOK pI668 668 (runFrom pI668 (fmask pI668) (cmask pI668) (hmask pI668) 1 667 (true, (init pI668), (init pI668))) ∧ intTest pI668 (runFrom pI668 (fmask pI668) (cmask pI668) (hmask pI668) 1 667 (true, (init pI668), (init pI668))) 668 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I668_fin) true) (by decide) rfl I668_fin intTest_fst
theorem link668 : linkOK pL668 pH668 pI668 = true := by decide +kernel
theorem cvx668 : ConvexBetweenHumps 668 :=
  cvx_of L668_ok H668_ok I668_ok link668 (by decide)
theorem cenlink668 : cenLinkOK pI668 668 = true := by decide +kernel
theorem cen668 : CenterUniqueMin 668 ∧ DipHyp 668 ∧ OnePointHyps 668 :=
  cen_of L668_ok H668_ok I668_ok link668 cenlink668

/-! ### `N = 669` -/

def pL669 : Prm := ⟨72, 34, 35, 671, 11, 18446744073709551616, 237031343311761246, 237031343311761246⟩
def pH669 : Prm := ⟨72, 34, 35, 671, 11, 18446744073709551616, 237035741358272350, 237035741358272350⟩
def pI669 : Prm := ⟨62, 30, 29, 671, 11, 18446744073709551616, 237031343311761246, 237035741358272350⟩
theorem L669_fin : (prmOK pL669 669 && ptTest pL669 (runFrom pL669 (fmask pL669) (cmask pL669) (hmask pL669) 1 668 (true, (init pL669), (init pL669))) 669 335 false) = true := by
  decide +kernel
theorem L669_ok : RunOK pL669 669 (runFrom pL669 (fmask pL669) (cmask pL669) (hmask pL669) 1 668 (true, (init pL669), (init pL669))) ∧ ptTest pL669 (runFrom pL669 (fmask pL669) (cmask pL669) (hmask pL669) 1 668 (true, (init pL669), (init pL669))) 669 335 false = true :=
  fin_run (runOK_init (prmOK_of_and L669_fin) true) (by decide) rfl L669_fin ptTest_fst
theorem H669_fin : (prmOK pH669 669 && ptTest pH669 (runFrom pH669 (fmask pH669) (cmask pH669) (hmask pH669) 1 668 (true, (init pH669), (init pH669))) 669 335 true) = true := by
  decide +kernel
theorem H669_ok : RunOK pH669 669 (runFrom pH669 (fmask pH669) (cmask pH669) (hmask pH669) 1 668 (true, (init pH669), (init pH669))) ∧ ptTest pH669 (runFrom pH669 (fmask pH669) (cmask pH669) (hmask pH669) 1 668 (true, (init pH669), (init pH669))) 669 335 true = true :=
  fin_run (runOK_init (prmOK_of_and H669_fin) true) (by decide) rfl H669_fin ptTest_fst
theorem I669_fin : (prmOK pI669 669 && intTest pI669 (runFrom pI669 (fmask pI669) (cmask pI669) (hmask pI669) 1 668 (true, (init pI669), (init pI669))) 669 16 false) = true := by
  decide +kernel
theorem I669_ok : RunOK pI669 669 (runFrom pI669 (fmask pI669) (cmask pI669) (hmask pI669) 1 668 (true, (init pI669), (init pI669))) ∧ intTest pI669 (runFrom pI669 (fmask pI669) (cmask pI669) (hmask pI669) 1 668 (true, (init pI669), (init pI669))) 669 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I669_fin) true) (by decide) rfl I669_fin intTest_fst
theorem link669 : linkOK pL669 pH669 pI669 = true := by decide +kernel
theorem cvx669 : ConvexBetweenHumps 669 :=
  cvx_of L669_ok H669_ok I669_ok link669 (by decide)

/-! ### `N = 670` -/

def pL670 : Prm := ⟨72, 34, 35, 672, 11, 18446744073709551616, 236755245298128090, 236755245298128090⟩
def pH670 : Prm := ⟨72, 34, 35, 672, 11, 18446744073709551616, 236759643344639194, 236759643344639194⟩
def pI670 : Prm := ⟨62, 30, 29, 672, 11, 18446744073709551616, 236755245298128090, 236759643344639194⟩
theorem L670_fin : (prmOK pL670 670 && ptTest pL670 (runFrom pL670 (fmask pL670) (cmask pL670) (hmask pL670) 1 669 (true, (init pL670), (init pL670))) 670 335 false) = true := by
  decide +kernel
theorem L670_ok : RunOK pL670 670 (runFrom pL670 (fmask pL670) (cmask pL670) (hmask pL670) 1 669 (true, (init pL670), (init pL670))) ∧ ptTest pL670 (runFrom pL670 (fmask pL670) (cmask pL670) (hmask pL670) 1 669 (true, (init pL670), (init pL670))) 670 335 false = true :=
  fin_run (runOK_init (prmOK_of_and L670_fin) true) (by decide) rfl L670_fin ptTest_fst
theorem H670_fin : (prmOK pH670 670 && ptTest pH670 (runFrom pH670 (fmask pH670) (cmask pH670) (hmask pH670) 1 669 (true, (init pH670), (init pH670))) 670 335 true) = true := by
  decide +kernel
theorem H670_ok : RunOK pH670 670 (runFrom pH670 (fmask pH670) (cmask pH670) (hmask pH670) 1 669 (true, (init pH670), (init pH670))) ∧ ptTest pH670 (runFrom pH670 (fmask pH670) (cmask pH670) (hmask pH670) 1 669 (true, (init pH670), (init pH670))) 670 335 true = true :=
  fin_run (runOK_init (prmOK_of_and H670_fin) true) (by decide) rfl H670_fin ptTest_fst
theorem I670_fin : (prmOK pI670 670 && intTest pI670 (runFrom pI670 (fmask pI670) (cmask pI670) (hmask pI670) 1 669 (true, (init pI670), (init pI670))) 670 16 true) = true := by
  decide +kernel
theorem I670_ok : RunOK pI670 670 (runFrom pI670 (fmask pI670) (cmask pI670) (hmask pI670) 1 669 (true, (init pI670), (init pI670))) ∧ intTest pI670 (runFrom pI670 (fmask pI670) (cmask pI670) (hmask pI670) 1 669 (true, (init pI670), (init pI670))) 670 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I670_fin) true) (by decide) rfl I670_fin intTest_fst
theorem link670 : linkOK pL670 pH670 pI670 = true := by decide +kernel
theorem cvx670 : ConvexBetweenHumps 670 :=
  cvx_of L670_ok H670_ok I670_ok link670 (by decide)
theorem cenlink670 : cenLinkOK pI670 670 = true := by decide +kernel
theorem cen670 : CenterUniqueMin 670 ∧ DipHyp 670 ∧ OnePointHyps 670 :=
  cen_of L670_ok H670_ok I670_ok link670 cenlink670

/-! ### `N = 671` -/

def pL671 : Prm := ⟨72, 34, 35, 673, 11, 18446744073709551616, 236479463141618901, 236479463141618901⟩
def pH671 : Prm := ⟨72, 34, 35, 673, 11, 18446744073709551616, 236483861188130005, 236483861188130005⟩
def pI671 : Prm := ⟨62, 30, 29, 673, 11, 18446744073709551616, 236479463141618901, 236483861188130005⟩
theorem L671_fin : (prmOK pL671 671 && ptTest pL671 (runFrom pL671 (fmask pL671) (cmask pL671) (hmask pL671) 1 670 (true, (init pL671), (init pL671))) 671 336 false) = true := by
  decide +kernel
theorem L671_ok : RunOK pL671 671 (runFrom pL671 (fmask pL671) (cmask pL671) (hmask pL671) 1 670 (true, (init pL671), (init pL671))) ∧ ptTest pL671 (runFrom pL671 (fmask pL671) (cmask pL671) (hmask pL671) 1 670 (true, (init pL671), (init pL671))) 671 336 false = true :=
  fin_run (runOK_init (prmOK_of_and L671_fin) true) (by decide) rfl L671_fin ptTest_fst
theorem H671_fin : (prmOK pH671 671 && ptTest pH671 (runFrom pH671 (fmask pH671) (cmask pH671) (hmask pH671) 1 670 (true, (init pH671), (init pH671))) 671 336 true) = true := by
  decide +kernel
theorem H671_ok : RunOK pH671 671 (runFrom pH671 (fmask pH671) (cmask pH671) (hmask pH671) 1 670 (true, (init pH671), (init pH671))) ∧ ptTest pH671 (runFrom pH671 (fmask pH671) (cmask pH671) (hmask pH671) 1 670 (true, (init pH671), (init pH671))) 671 336 true = true :=
  fin_run (runOK_init (prmOK_of_and H671_fin) true) (by decide) rfl H671_fin ptTest_fst
theorem I671_fin : (prmOK pI671 671 && intTest pI671 (runFrom pI671 (fmask pI671) (cmask pI671) (hmask pI671) 1 670 (true, (init pI671), (init pI671))) 671 16 false) = true := by
  decide +kernel
theorem I671_ok : RunOK pI671 671 (runFrom pI671 (fmask pI671) (cmask pI671) (hmask pI671) 1 670 (true, (init pI671), (init pI671))) ∧ intTest pI671 (runFrom pI671 (fmask pI671) (cmask pI671) (hmask pI671) 1 670 (true, (init pI671), (init pI671))) 671 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I671_fin) true) (by decide) rfl I671_fin intTest_fst
theorem link671 : linkOK pL671 pH671 pI671 = true := by decide +kernel
theorem cvx671 : ConvexBetweenHumps 671 :=
  cvx_of L671_ok H671_ok I671_ok link671 (by decide)

/-! ### `N = 672` -/

def pL672 : Prm := ⟨72, 34, 35, 674, 11, 18446744073709551616, 236204777842255159, 236204777842255159⟩
def pH672 : Prm := ⟨72, 34, 35, 674, 11, 18446744073709551616, 236209175888766263, 236209175888766263⟩
def pI672 : Prm := ⟨62, 30, 29, 674, 11, 18446744073709551616, 236204777842255159, 236209175888766263⟩
theorem L672_fin : (prmOK pL672 672 && ptTest pL672 (runFrom pL672 (fmask pL672) (cmask pL672) (hmask pL672) 1 671 (true, (init pL672), (init pL672))) 672 336 false) = true := by
  decide +kernel
theorem L672_ok : RunOK pL672 672 (runFrom pL672 (fmask pL672) (cmask pL672) (hmask pL672) 1 671 (true, (init pL672), (init pL672))) ∧ ptTest pL672 (runFrom pL672 (fmask pL672) (cmask pL672) (hmask pL672) 1 671 (true, (init pL672), (init pL672))) 672 336 false = true :=
  fin_run (runOK_init (prmOK_of_and L672_fin) true) (by decide) rfl L672_fin ptTest_fst
theorem H672_fin : (prmOK pH672 672 && ptTest pH672 (runFrom pH672 (fmask pH672) (cmask pH672) (hmask pH672) 1 671 (true, (init pH672), (init pH672))) 672 336 true) = true := by
  decide +kernel
theorem H672_ok : RunOK pH672 672 (runFrom pH672 (fmask pH672) (cmask pH672) (hmask pH672) 1 671 (true, (init pH672), (init pH672))) ∧ ptTest pH672 (runFrom pH672 (fmask pH672) (cmask pH672) (hmask pH672) 1 671 (true, (init pH672), (init pH672))) 672 336 true = true :=
  fin_run (runOK_init (prmOK_of_and H672_fin) true) (by decide) rfl H672_fin ptTest_fst
theorem I672_fin : (prmOK pI672 672 && intTest pI672 (runFrom pI672 (fmask pI672) (cmask pI672) (hmask pI672) 1 671 (true, (init pI672), (init pI672))) 672 16 true) = true := by
  decide +kernel
theorem I672_ok : RunOK pI672 672 (runFrom pI672 (fmask pI672) (cmask pI672) (hmask pI672) 1 671 (true, (init pI672), (init pI672))) ∧ intTest pI672 (runFrom pI672 (fmask pI672) (cmask pI672) (hmask pI672) 1 671 (true, (init pI672), (init pI672))) 672 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I672_fin) true) (by decide) rfl I672_fin intTest_fst
theorem link672 : linkOK pL672 pH672 pI672 = true := by decide +kernel
theorem cvx672 : ConvexBetweenHumps 672 :=
  cvx_of L672_ok H672_ok I672_ok link672 (by decide)
theorem cenlink672 : cenLinkOK pI672 672 = true := by decide +kernel
theorem cen672 : CenterUniqueMin 672 ∧ DipHyp 672 ∧ OnePointHyps 672 :=
  cen_of L672_ok H672_ok I672_ok link672 cenlink672

/-! ### `N = 673` -/

def pL673 : Prm := ⟨72, 34, 35, 675, 11, 18446744073709551616, 235930406323945019, 235930406323945019⟩
def pH673 : Prm := ⟨72, 34, 35, 675, 11, 18446744073709551616, 235934804370456123, 235934804370456123⟩
def pI673 : Prm := ⟨62, 30, 29, 675, 11, 18446744073709551616, 235930406323945019, 235934804370456123⟩
theorem L673_fin : (prmOK pL673 673 && ptTest pL673 (runFrom pL673 (fmask pL673) (cmask pL673) (hmask pL673) 1 672 (true, (init pL673), (init pL673))) 673 337 false) = true := by
  decide +kernel
theorem L673_ok : RunOK pL673 673 (runFrom pL673 (fmask pL673) (cmask pL673) (hmask pL673) 1 672 (true, (init pL673), (init pL673))) ∧ ptTest pL673 (runFrom pL673 (fmask pL673) (cmask pL673) (hmask pL673) 1 672 (true, (init pL673), (init pL673))) 673 337 false = true :=
  fin_run (runOK_init (prmOK_of_and L673_fin) true) (by decide) rfl L673_fin ptTest_fst
theorem H673_fin : (prmOK pH673 673 && ptTest pH673 (runFrom pH673 (fmask pH673) (cmask pH673) (hmask pH673) 1 672 (true, (init pH673), (init pH673))) 673 337 true) = true := by
  decide +kernel
theorem H673_ok : RunOK pH673 673 (runFrom pH673 (fmask pH673) (cmask pH673) (hmask pH673) 1 672 (true, (init pH673), (init pH673))) ∧ ptTest pH673 (runFrom pH673 (fmask pH673) (cmask pH673) (hmask pH673) 1 672 (true, (init pH673), (init pH673))) 673 337 true = true :=
  fin_run (runOK_init (prmOK_of_and H673_fin) true) (by decide) rfl H673_fin ptTest_fst
theorem I673_fin : (prmOK pI673 673 && intTest pI673 (runFrom pI673 (fmask pI673) (cmask pI673) (hmask pI673) 1 672 (true, (init pI673), (init pI673))) 673 16 false) = true := by
  decide +kernel
theorem I673_ok : RunOK pI673 673 (runFrom pI673 (fmask pI673) (cmask pI673) (hmask pI673) 1 672 (true, (init pI673), (init pI673))) ∧ intTest pI673 (runFrom pI673 (fmask pI673) (cmask pI673) (hmask pI673) 1 672 (true, (init pI673), (init pI673))) 673 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I673_fin) true) (by decide) rfl I673_fin intTest_fst
theorem link673 : linkOK pL673 pH673 pI673 = true := by decide +kernel
theorem cvx673 : ConvexBetweenHumps 673 :=
  cvx_of L673_ok H673_ok I673_ok link673 (by decide)

/-! ### `N = 674` -/

def pL674 : Prm := ⟨72, 34, 35, 676, 11, 18446744073709551616, 235657122520186582, 235657122520186582⟩
def pH674 : Prm := ⟨72, 34, 35, 676, 11, 18446744073709551616, 235661520566697686, 235661520566697686⟩
def pI674 : Prm := ⟨62, 30, 29, 676, 11, 18446744073709551616, 235657122520186582, 235661520566697686⟩
theorem L674_fin : (prmOK pL674 674 && ptTest pL674 (runFrom pL674 (fmask pL674) (cmask pL674) (hmask pL674) 1 673 (true, (init pL674), (init pL674))) 674 337 false) = true := by
  decide +kernel
theorem L674_ok : RunOK pL674 674 (runFrom pL674 (fmask pL674) (cmask pL674) (hmask pL674) 1 673 (true, (init pL674), (init pL674))) ∧ ptTest pL674 (runFrom pL674 (fmask pL674) (cmask pL674) (hmask pL674) 1 673 (true, (init pL674), (init pL674))) 674 337 false = true :=
  fin_run (runOK_init (prmOK_of_and L674_fin) true) (by decide) rfl L674_fin ptTest_fst
theorem H674_fin : (prmOK pH674 674 && ptTest pH674 (runFrom pH674 (fmask pH674) (cmask pH674) (hmask pH674) 1 673 (true, (init pH674), (init pH674))) 674 337 true) = true := by
  decide +kernel
theorem H674_ok : RunOK pH674 674 (runFrom pH674 (fmask pH674) (cmask pH674) (hmask pH674) 1 673 (true, (init pH674), (init pH674))) ∧ ptTest pH674 (runFrom pH674 (fmask pH674) (cmask pH674) (hmask pH674) 1 673 (true, (init pH674), (init pH674))) 674 337 true = true :=
  fin_run (runOK_init (prmOK_of_and H674_fin) true) (by decide) rfl H674_fin ptTest_fst
theorem I674_fin : (prmOK pI674 674 && intTest pI674 (runFrom pI674 (fmask pI674) (cmask pI674) (hmask pI674) 1 673 (true, (init pI674), (init pI674))) 674 16 true) = true := by
  decide +kernel
theorem I674_ok : RunOK pI674 674 (runFrom pI674 (fmask pI674) (cmask pI674) (hmask pI674) 1 673 (true, (init pI674), (init pI674))) ∧ intTest pI674 (runFrom pI674 (fmask pI674) (cmask pI674) (hmask pI674) 1 673 (true, (init pI674), (init pI674))) 674 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I674_fin) true) (by decide) rfl I674_fin intTest_fst
theorem link674 : linkOK pL674 pH674 pI674 = true := by decide +kernel
theorem cvx674 : ConvexBetweenHumps 674 :=
  cvx_of L674_ok H674_ok I674_ok link674 (by decide)
theorem cenlink674 : cenLinkOK pI674 674 = true := by decide +kernel
theorem cen674 : CenterUniqueMin 674 ∧ DipHyp 674 ∧ OnePointHyps 674 :=
  cen_of L674_ok H674_ok I674_ok link674 cenlink674

/-! ### `N = 675` -/

def pL675 : Prm := ⟨72, 34, 35, 677, 11, 18446744073709551616, 235384150439581425, 235384150439581425⟩
def pH675 : Prm := ⟨72, 34, 35, 677, 11, 18446744073709551616, 235388548486092529, 235388548486092529⟩
def pI675 : Prm := ⟨62, 30, 29, 677, 11, 18446744073709551616, 235384150439581425, 235388548486092529⟩
theorem L675_fin : (prmOK pL675 675 && ptTest pL675 (runFrom pL675 (fmask pL675) (cmask pL675) (hmask pL675) 1 674 (true, (init pL675), (init pL675))) 675 338 false) = true := by
  decide +kernel
theorem L675_ok : RunOK pL675 675 (runFrom pL675 (fmask pL675) (cmask pL675) (hmask pL675) 1 674 (true, (init pL675), (init pL675))) ∧ ptTest pL675 (runFrom pL675 (fmask pL675) (cmask pL675) (hmask pL675) 1 674 (true, (init pL675), (init pL675))) 675 338 false = true :=
  fin_run (runOK_init (prmOK_of_and L675_fin) true) (by decide) rfl L675_fin ptTest_fst
theorem H675_fin : (prmOK pH675 675 && ptTest pH675 (runFrom pH675 (fmask pH675) (cmask pH675) (hmask pH675) 1 674 (true, (init pH675), (init pH675))) 675 338 true) = true := by
  decide +kernel
theorem H675_ok : RunOK pH675 675 (runFrom pH675 (fmask pH675) (cmask pH675) (hmask pH675) 1 674 (true, (init pH675), (init pH675))) ∧ ptTest pH675 (runFrom pH675 (fmask pH675) (cmask pH675) (hmask pH675) 1 674 (true, (init pH675), (init pH675))) 675 338 true = true :=
  fin_run (runOK_init (prmOK_of_and H675_fin) true) (by decide) rfl H675_fin ptTest_fst
theorem I675_fin : (prmOK pI675 675 && intTest pI675 (runFrom pI675 (fmask pI675) (cmask pI675) (hmask pI675) 1 674 (true, (init pI675), (init pI675))) 675 16 false) = true := by
  decide +kernel
theorem I675_ok : RunOK pI675 675 (runFrom pI675 (fmask pI675) (cmask pI675) (hmask pI675) 1 674 (true, (init pI675), (init pI675))) ∧ intTest pI675 (runFrom pI675 (fmask pI675) (cmask pI675) (hmask pI675) 1 674 (true, (init pI675), (init pI675))) 675 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I675_fin) true) (by decide) rfl I675_fin intTest_fst
theorem link675 : linkOK pL675 pH675 pI675 = true := by decide +kernel
theorem cvx675 : ConvexBetweenHumps 675 :=
  cvx_of L675_ok H675_ok I675_ok link675 (by decide)

/-! ### `N = 676` -/

def pL676 : Prm := ⟨72, 34, 35, 678, 11, 18446744073709551616, 235112257033627250, 235112257033627250⟩
def pH676 : Prm := ⟨72, 34, 35, 678, 11, 18446744073709551616, 235116655080138354, 235116655080138354⟩
def pI676 : Prm := ⟨62, 30, 29, 678, 11, 18446744073709551616, 235112257033627250, 235116655080138354⟩
theorem L676_fin : (prmOK pL676 676 && ptTest pL676 (runFrom pL676 (fmask pL676) (cmask pL676) (hmask pL676) 1 675 (true, (init pL676), (init pL676))) 676 338 false) = true := by
  decide +kernel
theorem L676_ok : RunOK pL676 676 (runFrom pL676 (fmask pL676) (cmask pL676) (hmask pL676) 1 675 (true, (init pL676), (init pL676))) ∧ ptTest pL676 (runFrom pL676 (fmask pL676) (cmask pL676) (hmask pL676) 1 675 (true, (init pL676), (init pL676))) 676 338 false = true :=
  fin_run (runOK_init (prmOK_of_and L676_fin) true) (by decide) rfl L676_fin ptTest_fst
theorem H676_fin : (prmOK pH676 676 && ptTest pH676 (runFrom pH676 (fmask pH676) (cmask pH676) (hmask pH676) 1 675 (true, (init pH676), (init pH676))) 676 338 true) = true := by
  decide +kernel
theorem H676_ok : RunOK pH676 676 (runFrom pH676 (fmask pH676) (cmask pH676) (hmask pH676) 1 675 (true, (init pH676), (init pH676))) ∧ ptTest pH676 (runFrom pH676 (fmask pH676) (cmask pH676) (hmask pH676) 1 675 (true, (init pH676), (init pH676))) 676 338 true = true :=
  fin_run (runOK_init (prmOK_of_and H676_fin) true) (by decide) rfl H676_fin ptTest_fst
theorem I676_fin : (prmOK pI676 676 && intTest pI676 (runFrom pI676 (fmask pI676) (cmask pI676) (hmask pI676) 1 675 (true, (init pI676), (init pI676))) 676 16 true) = true := by
  decide +kernel
theorem I676_ok : RunOK pI676 676 (runFrom pI676 (fmask pI676) (cmask pI676) (hmask pI676) 1 675 (true, (init pI676), (init pI676))) ∧ intTest pI676 (runFrom pI676 (fmask pI676) (cmask pI676) (hmask pI676) 1 675 (true, (init pI676), (init pI676))) 676 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I676_fin) true) (by decide) rfl I676_fin intTest_fst
theorem link676 : linkOK pL676 pH676 pI676 = true := by decide +kernel
theorem cvx676 : ConvexBetweenHumps 676 :=
  cvx_of L676_ok H676_ok I676_ok link676 (by decide)
theorem cenlink676 : cenLinkOK pI676 676 = true := by decide +kernel
theorem cen676 : CenterUniqueMin 676 ∧ DipHyp 676 ∧ OnePointHyps 676 :=
  cen_of L676_ok H676_ok I676_ok link676 cenlink676

/-! ### `N = 677` -/

def pL677 : Prm := ⟨72, 34, 35, 679, 11, 18446744073709551616, 234840673310874714, 234840673310874714⟩
def pH677 : Prm := ⟨72, 34, 35, 679, 11, 18446744073709551616, 234845071357385818, 234845071357385818⟩
def pI677 : Prm := ⟨62, 30, 29, 679, 11, 18446744073709551616, 234840673310874714, 234845071357385818⟩
theorem L677_fin : (prmOK pL677 677 && ptTest pL677 (runFrom pL677 (fmask pL677) (cmask pL677) (hmask pL677) 1 676 (true, (init pL677), (init pL677))) 677 339 false) = true := by
  decide +kernel
theorem L677_ok : RunOK pL677 677 (runFrom pL677 (fmask pL677) (cmask pL677) (hmask pL677) 1 676 (true, (init pL677), (init pL677))) ∧ ptTest pL677 (runFrom pL677 (fmask pL677) (cmask pL677) (hmask pL677) 1 676 (true, (init pL677), (init pL677))) 677 339 false = true :=
  fin_run (runOK_init (prmOK_of_and L677_fin) true) (by decide) rfl L677_fin ptTest_fst
theorem H677_fin : (prmOK pH677 677 && ptTest pH677 (runFrom pH677 (fmask pH677) (cmask pH677) (hmask pH677) 1 676 (true, (init pH677), (init pH677))) 677 339 true) = true := by
  decide +kernel
theorem H677_ok : RunOK pH677 677 (runFrom pH677 (fmask pH677) (cmask pH677) (hmask pH677) 1 676 (true, (init pH677), (init pH677))) ∧ ptTest pH677 (runFrom pH677 (fmask pH677) (cmask pH677) (hmask pH677) 1 676 (true, (init pH677), (init pH677))) 677 339 true = true :=
  fin_run (runOK_init (prmOK_of_and H677_fin) true) (by decide) rfl H677_fin ptTest_fst
theorem I677_fin : (prmOK pI677 677 && intTest pI677 (runFrom pI677 (fmask pI677) (cmask pI677) (hmask pI677) 1 676 (true, (init pI677), (init pI677))) 677 16 false) = true := by
  decide +kernel
theorem I677_ok : RunOK pI677 677 (runFrom pI677 (fmask pI677) (cmask pI677) (hmask pI677) 1 676 (true, (init pI677), (init pI677))) ∧ intTest pI677 (runFrom pI677 (fmask pI677) (cmask pI677) (hmask pI677) 1 676 (true, (init pI677), (init pI677))) 677 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I677_fin) true) (by decide) rfl I677_fin intTest_fst
theorem link677 : linkOK pL677 pH677 pI677 = true := by decide +kernel
theorem cvx677 : ConvexBetweenHumps 677 :=
  cvx_of L677_ok H677_ok I677_ok link677 (by decide)

/-! ### `N = 678` -/

def pL678 : Prm := ⟨72, 34, 35, 680, 11, 18446744073709551616, 234570159324145065, 234570159324145065⟩
def pH678 : Prm := ⟨72, 34, 35, 680, 11, 18446744073709551616, 234574557370656169, 234574557370656169⟩
def pI678 : Prm := ⟨62, 30, 29, 680, 11, 18446744073709551616, 234570159324145065, 234574557370656169⟩
theorem L678_fin : (prmOK pL678 678 && ptTest pL678 (runFrom pL678 (fmask pL678) (cmask pL678) (hmask pL678) 1 677 (true, (init pL678), (init pL678))) 678 339 false) = true := by
  decide +kernel
theorem L678_ok : RunOK pL678 678 (runFrom pL678 (fmask pL678) (cmask pL678) (hmask pL678) 1 677 (true, (init pL678), (init pL678))) ∧ ptTest pL678 (runFrom pL678 (fmask pL678) (cmask pL678) (hmask pL678) 1 677 (true, (init pL678), (init pL678))) 678 339 false = true :=
  fin_run (runOK_init (prmOK_of_and L678_fin) true) (by decide) rfl L678_fin ptTest_fst
theorem H678_fin : (prmOK pH678 678 && ptTest pH678 (runFrom pH678 (fmask pH678) (cmask pH678) (hmask pH678) 1 677 (true, (init pH678), (init pH678))) 678 339 true) = true := by
  decide +kernel
theorem H678_ok : RunOK pH678 678 (runFrom pH678 (fmask pH678) (cmask pH678) (hmask pH678) 1 677 (true, (init pH678), (init pH678))) ∧ ptTest pH678 (runFrom pH678 (fmask pH678) (cmask pH678) (hmask pH678) 1 677 (true, (init pH678), (init pH678))) 678 339 true = true :=
  fin_run (runOK_init (prmOK_of_and H678_fin) true) (by decide) rfl H678_fin ptTest_fst
theorem I678_fin : (prmOK pI678 678 && intTest pI678 (runFrom pI678 (fmask pI678) (cmask pI678) (hmask pI678) 1 677 (true, (init pI678), (init pI678))) 678 16 true) = true := by
  decide +kernel
theorem I678_ok : RunOK pI678 678 (runFrom pI678 (fmask pI678) (cmask pI678) (hmask pI678) 1 677 (true, (init pI678), (init pI678))) ∧ intTest pI678 (runFrom pI678 (fmask pI678) (cmask pI678) (hmask pI678) 1 677 (true, (init pI678), (init pI678))) 678 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I678_fin) true) (by decide) rfl I678_fin intTest_fst
theorem link678 : linkOK pL678 pH678 pI678 = true := by decide +kernel
theorem cvx678 : ConvexBetweenHumps 678 :=
  cvx_of L678_ok H678_ok I678_ok link678 (by decide)
theorem cenlink678 : cenLinkOK pI678 678 = true := by decide +kernel
theorem cen678 : CenterUniqueMin 678 ∧ DipHyp 678 ∧ OnePointHyps 678 :=
  cen_of L678_ok H678_ok I678_ok link678 cenlink678

/-! ### `N = 679` -/

def pL679 : Prm := ⟨72, 34, 35, 681, 11, 18446744073709551616, 234299952998411184, 234299952998411184⟩
def pH679 : Prm := ⟨72, 34, 35, 681, 11, 18446744073709551616, 234304351044922288, 234304351044922288⟩
def pI679 : Prm := ⟨62, 30, 29, 681, 11, 18446744073709551616, 234299952998411184, 234304351044922288⟩
theorem L679_fin : (prmOK pL679 679 && ptTest pL679 (runFrom pL679 (fmask pL679) (cmask pL679) (hmask pL679) 1 678 (true, (init pL679), (init pL679))) 679 340 false) = true := by
  decide +kernel
theorem L679_ok : RunOK pL679 679 (runFrom pL679 (fmask pL679) (cmask pL679) (hmask pL679) 1 678 (true, (init pL679), (init pL679))) ∧ ptTest pL679 (runFrom pL679 (fmask pL679) (cmask pL679) (hmask pL679) 1 678 (true, (init pL679), (init pL679))) 679 340 false = true :=
  fin_run (runOK_init (prmOK_of_and L679_fin) true) (by decide) rfl L679_fin ptTest_fst
theorem H679_fin : (prmOK pH679 679 && ptTest pH679 (runFrom pH679 (fmask pH679) (cmask pH679) (hmask pH679) 1 678 (true, (init pH679), (init pH679))) 679 340 true) = true := by
  decide +kernel
theorem H679_ok : RunOK pH679 679 (runFrom pH679 (fmask pH679) (cmask pH679) (hmask pH679) 1 678 (true, (init pH679), (init pH679))) ∧ ptTest pH679 (runFrom pH679 (fmask pH679) (cmask pH679) (hmask pH679) 1 678 (true, (init pH679), (init pH679))) 679 340 true = true :=
  fin_run (runOK_init (prmOK_of_and H679_fin) true) (by decide) rfl H679_fin ptTest_fst
theorem I679_fin : (prmOK pI679 679 && intTest pI679 (runFrom pI679 (fmask pI679) (cmask pI679) (hmask pI679) 1 678 (true, (init pI679), (init pI679))) 679 16 false) = true := by
  decide +kernel
theorem I679_ok : RunOK pI679 679 (runFrom pI679 (fmask pI679) (cmask pI679) (hmask pI679) 1 678 (true, (init pI679), (init pI679))) ∧ intTest pI679 (runFrom pI679 (fmask pI679) (cmask pI679) (hmask pI679) 1 678 (true, (init pI679), (init pI679))) 679 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I679_fin) true) (by decide) rfl I679_fin intTest_fst
theorem link679 : linkOK pL679 pH679 pI679 = true := by decide +kernel
theorem cvx679 : ConvexBetweenHumps 679 :=
  cvx_of L679_ok H679_ok I679_ok link679 (by decide)

/-! ### `N = 680` -/

def pL680 : Prm := ⟨73, 35, 35, 682, 11, 18446744073709551616, 234030807569942766, 234030807569942766⟩
def pH680 : Prm := ⟨73, 35, 35, 682, 11, 18446744073709551616, 234035205616453870, 234035205616453870⟩
def pI680 : Prm := ⟨62, 30, 29, 682, 11, 18446744073709551616, 234030807569942766, 234035205616453870⟩
theorem L680_fin : (prmOK pL680 680 && ptTest pL680 (runFrom pL680 (fmask pL680) (cmask pL680) (hmask pL680) 1 679 (true, (init pL680), (init pL680))) 680 340 false) = true := by
  decide +kernel
theorem L680_ok : RunOK pL680 680 (runFrom pL680 (fmask pL680) (cmask pL680) (hmask pL680) 1 679 (true, (init pL680), (init pL680))) ∧ ptTest pL680 (runFrom pL680 (fmask pL680) (cmask pL680) (hmask pL680) 1 679 (true, (init pL680), (init pL680))) 680 340 false = true :=
  fin_run (runOK_init (prmOK_of_and L680_fin) true) (by decide) rfl L680_fin ptTest_fst
theorem H680_fin : (prmOK pH680 680 && ptTest pH680 (runFrom pH680 (fmask pH680) (cmask pH680) (hmask pH680) 1 679 (true, (init pH680), (init pH680))) 680 340 true) = true := by
  decide +kernel
theorem H680_ok : RunOK pH680 680 (runFrom pH680 (fmask pH680) (cmask pH680) (hmask pH680) 1 679 (true, (init pH680), (init pH680))) ∧ ptTest pH680 (runFrom pH680 (fmask pH680) (cmask pH680) (hmask pH680) 1 679 (true, (init pH680), (init pH680))) 680 340 true = true :=
  fin_run (runOK_init (prmOK_of_and H680_fin) true) (by decide) rfl H680_fin ptTest_fst
theorem I680_fin : (prmOK pI680 680 && intTest pI680 (runFrom pI680 (fmask pI680) (cmask pI680) (hmask pI680) 1 679 (true, (init pI680), (init pI680))) 680 16 true) = true := by
  decide +kernel
theorem I680_ok : RunOK pI680 680 (runFrom pI680 (fmask pI680) (cmask pI680) (hmask pI680) 1 679 (true, (init pI680), (init pI680))) ∧ intTest pI680 (runFrom pI680 (fmask pI680) (cmask pI680) (hmask pI680) 1 679 (true, (init pI680), (init pI680))) 680 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I680_fin) true) (by decide) rfl I680_fin intTest_fst
theorem link680 : linkOK pL680 pH680 pI680 = true := by decide +kernel
theorem cvx680 : ConvexBetweenHumps 680 :=
  cvx_of L680_ok H680_ok I680_ok link680 (by decide)
theorem cenlink680 : cenLinkOK pI680 680 = true := by decide +kernel
theorem cen680 : CenterUniqueMin 680 ∧ DipHyp 680 ∧ OnePointHyps 680 :=
  cen_of L680_ok H680_ok I680_ok link680 cenlink680

/-! ### `N = 681` -/

def pL681 : Prm := ⟨72, 34, 35, 683, 11, 18446744073709551616, 233761967797843991, 233761967797843991⟩
def pH681 : Prm := ⟨73, 35, 35, 683, 11, 18446744073709551616, 233766365844355095, 233766365844355095⟩
def pI681 : Prm := ⟨62, 30, 29, 683, 11, 18446744073709551616, 233761967797843991, 233766365844355095⟩
theorem L681_fin : (prmOK pL681 681 && ptTest pL681 (runFrom pL681 (fmask pL681) (cmask pL681) (hmask pL681) 1 680 (true, (init pL681), (init pL681))) 681 341 false) = true := by
  decide +kernel
theorem L681_ok : RunOK pL681 681 (runFrom pL681 (fmask pL681) (cmask pL681) (hmask pL681) 1 680 (true, (init pL681), (init pL681))) ∧ ptTest pL681 (runFrom pL681 (fmask pL681) (cmask pL681) (hmask pL681) 1 680 (true, (init pL681), (init pL681))) 681 341 false = true :=
  fin_run (runOK_init (prmOK_of_and L681_fin) true) (by decide) rfl L681_fin ptTest_fst
theorem H681_fin : (prmOK pH681 681 && ptTest pH681 (runFrom pH681 (fmask pH681) (cmask pH681) (hmask pH681) 1 680 (true, (init pH681), (init pH681))) 681 341 true) = true := by
  decide +kernel
theorem H681_ok : RunOK pH681 681 (runFrom pH681 (fmask pH681) (cmask pH681) (hmask pH681) 1 680 (true, (init pH681), (init pH681))) ∧ ptTest pH681 (runFrom pH681 (fmask pH681) (cmask pH681) (hmask pH681) 1 680 (true, (init pH681), (init pH681))) 681 341 true = true :=
  fin_run (runOK_init (prmOK_of_and H681_fin) true) (by decide) rfl H681_fin ptTest_fst
theorem I681_fin : (prmOK pI681 681 && intTest pI681 (runFrom pI681 (fmask pI681) (cmask pI681) (hmask pI681) 1 680 (true, (init pI681), (init pI681))) 681 16 false) = true := by
  decide +kernel
theorem I681_ok : RunOK pI681 681 (runFrom pI681 (fmask pI681) (cmask pI681) (hmask pI681) 1 680 (true, (init pI681), (init pI681))) ∧ intTest pI681 (runFrom pI681 (fmask pI681) (cmask pI681) (hmask pI681) 1 680 (true, (init pI681), (init pI681))) 681 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I681_fin) true) (by decide) rfl I681_fin intTest_fst
theorem link681 : linkOK pL681 pH681 pI681 = true := by decide +kernel
theorem cvx681 : ConvexBetweenHumps 681 :=
  cvx_of L681_ok H681_ok I681_ok link681 (by decide)

/-! ### `N = 682` -/

def pL682 : Prm := ⟨73, 35, 35, 684, 11, 18446744073709551616, 233494180182648190, 233494180182648190⟩
def pH682 : Prm := ⟨73, 35, 35, 684, 11, 18446744073709551616, 233498578229159294, 233498578229159294⟩
def pI682 : Prm := ⟨62, 30, 29, 684, 11, 18446744073709551616, 233494180182648190, 233498578229159294⟩
theorem L682_fin : (prmOK pL682 682 && ptTest pL682 (runFrom pL682 (fmask pL682) (cmask pL682) (hmask pL682) 1 681 (true, (init pL682), (init pL682))) 682 341 false) = true := by
  decide +kernel
theorem L682_ok : RunOK pL682 682 (runFrom pL682 (fmask pL682) (cmask pL682) (hmask pL682) 1 681 (true, (init pL682), (init pL682))) ∧ ptTest pL682 (runFrom pL682 (fmask pL682) (cmask pL682) (hmask pL682) 1 681 (true, (init pL682), (init pL682))) 682 341 false = true :=
  fin_run (runOK_init (prmOK_of_and L682_fin) true) (by decide) rfl L682_fin ptTest_fst
theorem H682_fin : (prmOK pH682 682 && ptTest pH682 (runFrom pH682 (fmask pH682) (cmask pH682) (hmask pH682) 1 681 (true, (init pH682), (init pH682))) 682 341 true) = true := by
  decide +kernel
theorem H682_ok : RunOK pH682 682 (runFrom pH682 (fmask pH682) (cmask pH682) (hmask pH682) 1 681 (true, (init pH682), (init pH682))) ∧ ptTest pH682 (runFrom pH682 (fmask pH682) (cmask pH682) (hmask pH682) 1 681 (true, (init pH682), (init pH682))) 682 341 true = true :=
  fin_run (runOK_init (prmOK_of_and H682_fin) true) (by decide) rfl H682_fin ptTest_fst
theorem I682_fin : (prmOK pI682 682 && intTest pI682 (runFrom pI682 (fmask pI682) (cmask pI682) (hmask pI682) 1 681 (true, (init pI682), (init pI682))) 682 16 true) = true := by
  decide +kernel
theorem I682_ok : RunOK pI682 682 (runFrom pI682 (fmask pI682) (cmask pI682) (hmask pI682) 1 681 (true, (init pI682), (init pI682))) ∧ intTest pI682 (runFrom pI682 (fmask pI682) (cmask pI682) (hmask pI682) 1 681 (true, (init pI682), (init pI682))) 682 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I682_fin) true) (by decide) rfl I682_fin intTest_fst
theorem link682 : linkOK pL682 pH682 pI682 = true := by decide +kernel
theorem cvx682 : ConvexBetweenHumps 682 :=
  cvx_of L682_ok H682_ok I682_ok link682 (by decide)
theorem cenlink682 : cenLinkOK pI682 682 = true := by decide +kernel
theorem cen682 : CenterUniqueMin 682 ∧ DipHyp 682 ∧ OnePointHyps 682 :=
  cen_of L682_ok H682_ok I682_ok link682 cenlink682

/-! ### `N = 683` -/

def pL683 : Prm := ⟨73, 35, 35, 685, 11, 18446744073709551616, 233226696236609632, 233226696236609632⟩
def pH683 : Prm := ⟨72, 34, 35, 685, 11, 18446744073709551616, 233231094283120736, 233231094283120736⟩
def pI683 : Prm := ⟨63, 30, 30, 685, 11, 18446744073709551616, 233226696236609632, 233231094283120736⟩
theorem L683_fin : (prmOK pL683 683 && ptTest pL683 (runFrom pL683 (fmask pL683) (cmask pL683) (hmask pL683) 1 682 (true, (init pL683), (init pL683))) 683 342 false) = true := by
  decide +kernel
theorem L683_ok : RunOK pL683 683 (runFrom pL683 (fmask pL683) (cmask pL683) (hmask pL683) 1 682 (true, (init pL683), (init pL683))) ∧ ptTest pL683 (runFrom pL683 (fmask pL683) (cmask pL683) (hmask pL683) 1 682 (true, (init pL683), (init pL683))) 683 342 false = true :=
  fin_run (runOK_init (prmOK_of_and L683_fin) true) (by decide) rfl L683_fin ptTest_fst
theorem H683_fin : (prmOK pH683 683 && ptTest pH683 (runFrom pH683 (fmask pH683) (cmask pH683) (hmask pH683) 1 682 (true, (init pH683), (init pH683))) 683 342 true) = true := by
  decide +kernel
theorem H683_ok : RunOK pH683 683 (runFrom pH683 (fmask pH683) (cmask pH683) (hmask pH683) 1 682 (true, (init pH683), (init pH683))) ∧ ptTest pH683 (runFrom pH683 (fmask pH683) (cmask pH683) (hmask pH683) 1 682 (true, (init pH683), (init pH683))) 683 342 true = true :=
  fin_run (runOK_init (prmOK_of_and H683_fin) true) (by decide) rfl H683_fin ptTest_fst
theorem I683_fin : (prmOK pI683 683 && intTest pI683 (runFrom pI683 (fmask pI683) (cmask pI683) (hmask pI683) 1 682 (true, (init pI683), (init pI683))) 683 16 false) = true := by
  decide +kernel
theorem I683_ok : RunOK pI683 683 (runFrom pI683 (fmask pI683) (cmask pI683) (hmask pI683) 1 682 (true, (init pI683), (init pI683))) ∧ intTest pI683 (runFrom pI683 (fmask pI683) (cmask pI683) (hmask pI683) 1 682 (true, (init pI683), (init pI683))) 683 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I683_fin) true) (by decide) rfl I683_fin intTest_fst
theorem link683 : linkOK pL683 pH683 pI683 = true := by decide +kernel
theorem cvx683 : ConvexBetweenHumps 683 :=
  cvx_of L683_ok H683_ok I683_ok link683 (by decide)

/-! ### `N = 684` -/

def pL684 : Prm := ⟨72, 34, 35, 686, 11, 18446744073709551616, 232960255804178325, 232960255804178325⟩
def pH684 : Prm := ⟨73, 35, 35, 686, 11, 18446744073709551616, 232964653850689429, 232964653850689429⟩
def pI684 : Prm := ⟨62, 30, 29, 686, 11, 18446744073709551616, 232960255804178325, 232964653850689429⟩
theorem L684_fin : (prmOK pL684 684 && ptTest pL684 (runFrom pL684 (fmask pL684) (cmask pL684) (hmask pL684) 1 683 (true, (init pL684), (init pL684))) 684 342 false) = true := by
  decide +kernel
theorem L684_ok : RunOK pL684 684 (runFrom pL684 (fmask pL684) (cmask pL684) (hmask pL684) 1 683 (true, (init pL684), (init pL684))) ∧ ptTest pL684 (runFrom pL684 (fmask pL684) (cmask pL684) (hmask pL684) 1 683 (true, (init pL684), (init pL684))) 684 342 false = true :=
  fin_run (runOK_init (prmOK_of_and L684_fin) true) (by decide) rfl L684_fin ptTest_fst
theorem H684_fin : (prmOK pH684 684 && ptTest pH684 (runFrom pH684 (fmask pH684) (cmask pH684) (hmask pH684) 1 683 (true, (init pH684), (init pH684))) 684 342 true) = true := by
  decide +kernel
theorem H684_ok : RunOK pH684 684 (runFrom pH684 (fmask pH684) (cmask pH684) (hmask pH684) 1 683 (true, (init pH684), (init pH684))) ∧ ptTest pH684 (runFrom pH684 (fmask pH684) (cmask pH684) (hmask pH684) 1 683 (true, (init pH684), (init pH684))) 684 342 true = true :=
  fin_run (runOK_init (prmOK_of_and H684_fin) true) (by decide) rfl H684_fin ptTest_fst
theorem I684_fin : (prmOK pI684 684 && intTest pI684 (runFrom pI684 (fmask pI684) (cmask pI684) (hmask pI684) 1 683 (true, (init pI684), (init pI684))) 684 16 true) = true := by
  decide +kernel
theorem I684_ok : RunOK pI684 684 (runFrom pI684 (fmask pI684) (cmask pI684) (hmask pI684) 1 683 (true, (init pI684), (init pI684))) ∧ intTest pI684 (runFrom pI684 (fmask pI684) (cmask pI684) (hmask pI684) 1 683 (true, (init pI684), (init pI684))) 684 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I684_fin) true) (by decide) rfl I684_fin intTest_fst
theorem link684 : linkOK pL684 pH684 pI684 = true := by decide +kernel
theorem cvx684 : ConvexBetweenHumps 684 :=
  cvx_of L684_ok H684_ok I684_ok link684 (by decide)
theorem cenlink684 : cenLinkOK pI684 684 = true := by decide +kernel
theorem cen684 : CenterUniqueMin 684 ∧ DipHyp 684 ∧ OnePointHyps 684 :=
  cen_of L684_ok H684_ok I684_ok link684 cenlink684

/-! ### `N = 685` -/

def pL685 : Prm := ⟨73, 35, 35, 687, 11, 18446744073709551616, 232694117070884228, 232694117070884228⟩
def pH685 : Prm := ⟨73, 35, 35, 687, 11, 18446744073709551616, 232698515117395332, 232698515117395332⟩
def pI685 : Prm := ⟨62, 30, 29, 687, 11, 18446744073709551616, 232694117070884228, 232698515117395332⟩
theorem L685_fin : (prmOK pL685 685 && ptTest pL685 (runFrom pL685 (fmask pL685) (cmask pL685) (hmask pL685) 1 684 (true, (init pL685), (init pL685))) 685 343 false) = true := by
  decide +kernel
theorem L685_ok : RunOK pL685 685 (runFrom pL685 (fmask pL685) (cmask pL685) (hmask pL685) 1 684 (true, (init pL685), (init pL685))) ∧ ptTest pL685 (runFrom pL685 (fmask pL685) (cmask pL685) (hmask pL685) 1 684 (true, (init pL685), (init pL685))) 685 343 false = true :=
  fin_run (runOK_init (prmOK_of_and L685_fin) true) (by decide) rfl L685_fin ptTest_fst
theorem H685_fin : (prmOK pH685 685 && ptTest pH685 (runFrom pH685 (fmask pH685) (cmask pH685) (hmask pH685) 1 684 (true, (init pH685), (init pH685))) 685 343 true) = true := by
  decide +kernel
theorem H685_ok : RunOK pH685 685 (runFrom pH685 (fmask pH685) (cmask pH685) (hmask pH685) 1 684 (true, (init pH685), (init pH685))) ∧ ptTest pH685 (runFrom pH685 (fmask pH685) (cmask pH685) (hmask pH685) 1 684 (true, (init pH685), (init pH685))) 685 343 true = true :=
  fin_run (runOK_init (prmOK_of_and H685_fin) true) (by decide) rfl H685_fin ptTest_fst
theorem I685_fin : (prmOK pI685 685 && intTest pI685 (runFrom pI685 (fmask pI685) (cmask pI685) (hmask pI685) 1 684 (true, (init pI685), (init pI685))) 685 16 false) = true := by
  decide +kernel
theorem I685_ok : RunOK pI685 685 (runFrom pI685 (fmask pI685) (cmask pI685) (hmask pI685) 1 684 (true, (init pI685), (init pI685))) ∧ intTest pI685 (runFrom pI685 (fmask pI685) (cmask pI685) (hmask pI685) 1 684 (true, (init pI685), (init pI685))) 685 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I685_fin) true) (by decide) rfl I685_fin intTest_fst
theorem link685 : linkOK pL685 pH685 pI685 = true := by decide +kernel
theorem cvx685 : ConvexBetweenHumps 685 :=
  cvx_of L685_ok H685_ok I685_ok link685 (by decide)

/-! ### `N = 686` -/

def pL686 : Prm := ⟨73, 35, 35, 688, 11, 18446744073709551616, 232429013303584922, 232429013303584922⟩
def pH686 : Prm := ⟨73, 35, 35, 688, 11, 18446744073709551616, 232433411350096026, 232433411350096026⟩
def pI686 : Prm := ⟨62, 30, 29, 688, 11, 18446744073709551616, 232429013303584922, 232433411350096026⟩
theorem L686_fin : (prmOK pL686 686 && ptTest pL686 (runFrom pL686 (fmask pL686) (cmask pL686) (hmask pL686) 1 685 (true, (init pL686), (init pL686))) 686 343 false) = true := by
  decide +kernel
theorem L686_ok : RunOK pL686 686 (runFrom pL686 (fmask pL686) (cmask pL686) (hmask pL686) 1 685 (true, (init pL686), (init pL686))) ∧ ptTest pL686 (runFrom pL686 (fmask pL686) (cmask pL686) (hmask pL686) 1 685 (true, (init pL686), (init pL686))) 686 343 false = true :=
  fin_run (runOK_init (prmOK_of_and L686_fin) true) (by decide) rfl L686_fin ptTest_fst
theorem H686_fin : (prmOK pH686 686 && ptTest pH686 (runFrom pH686 (fmask pH686) (cmask pH686) (hmask pH686) 1 685 (true, (init pH686), (init pH686))) 686 343 true) = true := by
  decide +kernel
theorem H686_ok : RunOK pH686 686 (runFrom pH686 (fmask pH686) (cmask pH686) (hmask pH686) 1 685 (true, (init pH686), (init pH686))) ∧ ptTest pH686 (runFrom pH686 (fmask pH686) (cmask pH686) (hmask pH686) 1 685 (true, (init pH686), (init pH686))) 686 343 true = true :=
  fin_run (runOK_init (prmOK_of_and H686_fin) true) (by decide) rfl H686_fin ptTest_fst
theorem I686_fin : (prmOK pI686 686 && intTest pI686 (runFrom pI686 (fmask pI686) (cmask pI686) (hmask pI686) 1 685 (true, (init pI686), (init pI686))) 686 16 true) = true := by
  decide +kernel
theorem I686_ok : RunOK pI686 686 (runFrom pI686 (fmask pI686) (cmask pI686) (hmask pI686) 1 685 (true, (init pI686), (init pI686))) ∧ intTest pI686 (runFrom pI686 (fmask pI686) (cmask pI686) (hmask pI686) 1 685 (true, (init pI686), (init pI686))) 686 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I686_fin) true) (by decide) rfl I686_fin intTest_fst
theorem link686 : linkOK pL686 pH686 pI686 = true := by decide +kernel
theorem cvx686 : ConvexBetweenHumps 686 :=
  cvx_of L686_ok H686_ok I686_ok link686 (by decide)
theorem cenlink686 : cenLinkOK pI686 686 = true := by decide +kernel
theorem cen686 : CenterUniqueMin 686 ∧ DipHyp 686 ∧ OnePointHyps 686 :=
  cen_of L686_ok H686_ok I686_ok link686 cenlink686

/-! ### `N = 687` -/

def pL687 : Prm := ⟨72, 34, 35, 689, 11, 18446744073709551616, 232164209282447583, 232164209282447583⟩
def pH687 : Prm := ⟨73, 35, 35, 689, 11, 18446744073709551616, 232168607328958687, 232168607328958687⟩
def pI687 : Prm := ⟨62, 30, 29, 689, 11, 18446744073709551616, 232164209282447583, 232168607328958687⟩
theorem L687_fin : (prmOK pL687 687 && ptTest pL687 (runFrom pL687 (fmask pL687) (cmask pL687) (hmask pL687) 1 686 (true, (init pL687), (init pL687))) 687 344 false) = true := by
  decide +kernel
theorem L687_ok : RunOK pL687 687 (runFrom pL687 (fmask pL687) (cmask pL687) (hmask pL687) 1 686 (true, (init pL687), (init pL687))) ∧ ptTest pL687 (runFrom pL687 (fmask pL687) (cmask pL687) (hmask pL687) 1 686 (true, (init pL687), (init pL687))) 687 344 false = true :=
  fin_run (runOK_init (prmOK_of_and L687_fin) true) (by decide) rfl L687_fin ptTest_fst
theorem H687_fin : (prmOK pH687 687 && ptTest pH687 (runFrom pH687 (fmask pH687) (cmask pH687) (hmask pH687) 1 686 (true, (init pH687), (init pH687))) 687 344 true) = true := by
  decide +kernel
theorem H687_ok : RunOK pH687 687 (runFrom pH687 (fmask pH687) (cmask pH687) (hmask pH687) 1 686 (true, (init pH687), (init pH687))) ∧ ptTest pH687 (runFrom pH687 (fmask pH687) (cmask pH687) (hmask pH687) 1 686 (true, (init pH687), (init pH687))) 687 344 true = true :=
  fin_run (runOK_init (prmOK_of_and H687_fin) true) (by decide) rfl H687_fin ptTest_fst
theorem I687_fin : (prmOK pI687 687 && intTest pI687 (runFrom pI687 (fmask pI687) (cmask pI687) (hmask pI687) 1 686 (true, (init pI687), (init pI687))) 687 16 false) = true := by
  decide +kernel
theorem I687_ok : RunOK pI687 687 (runFrom pI687 (fmask pI687) (cmask pI687) (hmask pI687) 1 686 (true, (init pI687), (init pI687))) ∧ intTest pI687 (runFrom pI687 (fmask pI687) (cmask pI687) (hmask pI687) 1 686 (true, (init pI687), (init pI687))) 687 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I687_fin) true) (by decide) rfl I687_fin intTest_fst
theorem link687 : linkOK pL687 pH687 pI687 = true := by decide +kernel
theorem cvx687 : ConvexBetweenHumps 687 :=
  cvx_of L687_ok H687_ok I687_ok link687 (by decide)

/-! ### `N = 688` -/

def pL688 : Prm := ⟨73, 35, 35, 690, 11, 18446744073709551616, 231900431774084563, 231900431774084563⟩
def pH688 : Prm := ⟨73, 35, 35, 690, 11, 18446744073709551616, 231904829820595667, 231904829820595667⟩
def pI688 : Prm := ⟨63, 30, 30, 690, 11, 18446744073709551616, 231900431774084563, 231904829820595667⟩
theorem L688_fin : (prmOK pL688 688 && ptTest pL688 (runFrom pL688 (fmask pL688) (cmask pL688) (hmask pL688) 1 687 (true, (init pL688), (init pL688))) 688 344 false) = true := by
  decide +kernel
theorem L688_ok : RunOK pL688 688 (runFrom pL688 (fmask pL688) (cmask pL688) (hmask pL688) 1 687 (true, (init pL688), (init pL688))) ∧ ptTest pL688 (runFrom pL688 (fmask pL688) (cmask pL688) (hmask pL688) 1 687 (true, (init pL688), (init pL688))) 688 344 false = true :=
  fin_run (runOK_init (prmOK_of_and L688_fin) true) (by decide) rfl L688_fin ptTest_fst
theorem H688_fin : (prmOK pH688 688 && ptTest pH688 (runFrom pH688 (fmask pH688) (cmask pH688) (hmask pH688) 1 687 (true, (init pH688), (init pH688))) 688 344 true) = true := by
  decide +kernel
theorem H688_ok : RunOK pH688 688 (runFrom pH688 (fmask pH688) (cmask pH688) (hmask pH688) 1 687 (true, (init pH688), (init pH688))) ∧ ptTest pH688 (runFrom pH688 (fmask pH688) (cmask pH688) (hmask pH688) 1 687 (true, (init pH688), (init pH688))) 688 344 true = true :=
  fin_run (runOK_init (prmOK_of_and H688_fin) true) (by decide) rfl H688_fin ptTest_fst
theorem I688_fin : (prmOK pI688 688 && intTest pI688 (runFrom pI688 (fmask pI688) (cmask pI688) (hmask pI688) 1 687 (true, (init pI688), (init pI688))) 688 16 true) = true := by
  decide +kernel
theorem I688_ok : RunOK pI688 688 (runFrom pI688 (fmask pI688) (cmask pI688) (hmask pI688) 1 687 (true, (init pI688), (init pI688))) ∧ intTest pI688 (runFrom pI688 (fmask pI688) (cmask pI688) (hmask pI688) 1 687 (true, (init pI688), (init pI688))) 688 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I688_fin) true) (by decide) rfl I688_fin intTest_fst
theorem link688 : linkOK pL688 pH688 pI688 = true := by decide +kernel
theorem cvx688 : ConvexBetweenHumps 688 :=
  cvx_of L688_ok H688_ok I688_ok link688 (by decide)
theorem cenlink688 : cenLinkOK pI688 688 = true := by decide +kernel
theorem cen688 : CenterUniqueMin 688 ∧ DipHyp 688 ∧ OnePointHyps 688 :=
  cen_of L688_ok H688_ok I688_ok link688 cenlink688

/-! ### `N = 689` -/

def pL689 : Prm := ⟨73, 35, 35, 691, 11, 18446744073709551616, 231636952075694806, 231636952075694806⟩
def pH689 : Prm := ⟨73, 35, 35, 691, 11, 18446744073709551616, 231641350122205910, 231641350122205910⟩
def pI689 : Prm := ⟨63, 30, 30, 691, 11, 18446744073709551616, 231636952075694806, 231641350122205910⟩
theorem L689_fin : (prmOK pL689 689 && ptTest pL689 (runFrom pL689 (fmask pL689) (cmask pL689) (hmask pL689) 1 688 (true, (init pL689), (init pL689))) 689 345 false) = true := by
  decide +kernel
theorem L689_ok : RunOK pL689 689 (runFrom pL689 (fmask pL689) (cmask pL689) (hmask pL689) 1 688 (true, (init pL689), (init pL689))) ∧ ptTest pL689 (runFrom pL689 (fmask pL689) (cmask pL689) (hmask pL689) 1 688 (true, (init pL689), (init pL689))) 689 345 false = true :=
  fin_run (runOK_init (prmOK_of_and L689_fin) true) (by decide) rfl L689_fin ptTest_fst
theorem H689_fin : (prmOK pH689 689 && ptTest pH689 (runFrom pH689 (fmask pH689) (cmask pH689) (hmask pH689) 1 688 (true, (init pH689), (init pH689))) 689 345 true) = true := by
  decide +kernel
theorem H689_ok : RunOK pH689 689 (runFrom pH689 (fmask pH689) (cmask pH689) (hmask pH689) 1 688 (true, (init pH689), (init pH689))) ∧ ptTest pH689 (runFrom pH689 (fmask pH689) (cmask pH689) (hmask pH689) 1 688 (true, (init pH689), (init pH689))) 689 345 true = true :=
  fin_run (runOK_init (prmOK_of_and H689_fin) true) (by decide) rfl H689_fin ptTest_fst
theorem I689_fin : (prmOK pI689 689 && intTest pI689 (runFrom pI689 (fmask pI689) (cmask pI689) (hmask pI689) 1 688 (true, (init pI689), (init pI689))) 689 16 false) = true := by
  decide +kernel
theorem I689_ok : RunOK pI689 689 (runFrom pI689 (fmask pI689) (cmask pI689) (hmask pI689) 1 688 (true, (init pI689), (init pI689))) ∧ intTest pI689 (runFrom pI689 (fmask pI689) (cmask pI689) (hmask pI689) 1 688 (true, (init pI689), (init pI689))) 689 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I689_fin) true) (by decide) rfl I689_fin intTest_fst
theorem link689 : linkOK pL689 pH689 pI689 = true := by decide +kernel
theorem cvx689 : ConvexBetweenHumps 689 :=
  cvx_of L689_ok H689_ok I689_ok link689 (by decide)

/-! ### `N = 690` -/

def pL690 : Prm := ⟨73, 35, 35, 692, 11, 18446744073709551616, 231374490529941166, 231374490529941166⟩
def pH690 : Prm := ⟨73, 35, 35, 692, 11, 18446744073709551616, 231378888576452270, 231378888576452270⟩
def pI690 : Prm := ⟨63, 30, 30, 692, 11, 18446744073709551616, 231374490529941166, 231378888576452270⟩
theorem L690_fin : (prmOK pL690 690 && ptTest pL690 (runFrom pL690 (fmask pL690) (cmask pL690) (hmask pL690) 1 689 (true, (init pL690), (init pL690))) 690 345 false) = true := by
  decide +kernel
theorem L690_ok : RunOK pL690 690 (runFrom pL690 (fmask pL690) (cmask pL690) (hmask pL690) 1 689 (true, (init pL690), (init pL690))) ∧ ptTest pL690 (runFrom pL690 (fmask pL690) (cmask pL690) (hmask pL690) 1 689 (true, (init pL690), (init pL690))) 690 345 false = true :=
  fin_run (runOK_init (prmOK_of_and L690_fin) true) (by decide) rfl L690_fin ptTest_fst
theorem H690_fin : (prmOK pH690 690 && ptTest pH690 (runFrom pH690 (fmask pH690) (cmask pH690) (hmask pH690) 1 689 (true, (init pH690), (init pH690))) 690 345 true) = true := by
  decide +kernel
theorem H690_ok : RunOK pH690 690 (runFrom pH690 (fmask pH690) (cmask pH690) (hmask pH690) 1 689 (true, (init pH690), (init pH690))) ∧ ptTest pH690 (runFrom pH690 (fmask pH690) (cmask pH690) (hmask pH690) 1 689 (true, (init pH690), (init pH690))) 690 345 true = true :=
  fin_run (runOK_init (prmOK_of_and H690_fin) true) (by decide) rfl H690_fin ptTest_fst
theorem I690_fin : (prmOK pI690 690 && intTest pI690 (runFrom pI690 (fmask pI690) (cmask pI690) (hmask pI690) 1 689 (true, (init pI690), (init pI690))) 690 16 true) = true := by
  decide +kernel
theorem I690_ok : RunOK pI690 690 (runFrom pI690 (fmask pI690) (cmask pI690) (hmask pI690) 1 689 (true, (init pI690), (init pI690))) ∧ intTest pI690 (runFrom pI690 (fmask pI690) (cmask pI690) (hmask pI690) 1 689 (true, (init pI690), (init pI690))) 690 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I690_fin) true) (by decide) rfl I690_fin intTest_fst
theorem link690 : linkOK pL690 pH690 pI690 = true := by decide +kernel
theorem cvx690 : ConvexBetweenHumps 690 :=
  cvx_of L690_ok H690_ok I690_ok link690 (by decide)
theorem cenlink690 : cenLinkOK pI690 690 = true := by decide +kernel
theorem cen690 : CenterUniqueMin 690 ∧ DipHyp 690 ∧ OnePointHyps 690 :=
  cen_of L690_ok H690_ok I690_ok link690 cenlink690

/-! ### `N = 691` -/

def pL691 : Prm := ⟨73, 35, 35, 693, 11, 18446744073709551616, 231112324874684835, 231112324874684835⟩
def pH691 : Prm := ⟨73, 35, 35, 693, 11, 18446744073709551616, 231116722921195939, 231116722921195939⟩
def pI691 : Prm := ⟨62, 30, 29, 693, 11, 18446744073709551616, 231112324874684835, 231116722921195939⟩
theorem L691_fin : (prmOK pL691 691 && ptTest pL691 (runFrom pL691 (fmask pL691) (cmask pL691) (hmask pL691) 1 690 (true, (init pL691), (init pL691))) 691 346 false) = true := by
  decide +kernel
theorem L691_ok : RunOK pL691 691 (runFrom pL691 (fmask pL691) (cmask pL691) (hmask pL691) 1 690 (true, (init pL691), (init pL691))) ∧ ptTest pL691 (runFrom pL691 (fmask pL691) (cmask pL691) (hmask pL691) 1 690 (true, (init pL691), (init pL691))) 691 346 false = true :=
  fin_run (runOK_init (prmOK_of_and L691_fin) true) (by decide) rfl L691_fin ptTest_fst
theorem H691_fin : (prmOK pH691 691 && ptTest pH691 (runFrom pH691 (fmask pH691) (cmask pH691) (hmask pH691) 1 690 (true, (init pH691), (init pH691))) 691 346 true) = true := by
  decide +kernel
theorem H691_ok : RunOK pH691 691 (runFrom pH691 (fmask pH691) (cmask pH691) (hmask pH691) 1 690 (true, (init pH691), (init pH691))) ∧ ptTest pH691 (runFrom pH691 (fmask pH691) (cmask pH691) (hmask pH691) 1 690 (true, (init pH691), (init pH691))) 691 346 true = true :=
  fin_run (runOK_init (prmOK_of_and H691_fin) true) (by decide) rfl H691_fin ptTest_fst
theorem I691_fin : (prmOK pI691 691 && intTest pI691 (runFrom pI691 (fmask pI691) (cmask pI691) (hmask pI691) 1 690 (true, (init pI691), (init pI691))) 691 16 false) = true := by
  decide +kernel
theorem I691_ok : RunOK pI691 691 (runFrom pI691 (fmask pI691) (cmask pI691) (hmask pI691) 1 690 (true, (init pI691), (init pI691))) ∧ intTest pI691 (runFrom pI691 (fmask pI691) (cmask pI691) (hmask pI691) 1 690 (true, (init pI691), (init pI691))) 691 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I691_fin) true) (by decide) rfl I691_fin intTest_fst
theorem link691 : linkOK pL691 pH691 pI691 = true := by decide +kernel
theorem cvx691 : ConvexBetweenHumps 691 :=
  cvx_of L691_ok H691_ok I691_ok link691 (by decide)

/-! ### `N = 692` -/

def pL692 : Prm := ⟨73, 35, 35, 694, 11, 18446744073709551616, 230851169103662078, 230851169103662078⟩
def pH692 : Prm := ⟨73, 35, 35, 694, 11, 18446744073709551616, 230855567150173182, 230855567150173182⟩
def pI692 : Prm := ⟨63, 30, 30, 694, 11, 18446744073709551616, 230851169103662078, 230855567150173182⟩
theorem L692_fin : (prmOK pL692 692 && ptTest pL692 (runFrom pL692 (fmask pL692) (cmask pL692) (hmask pL692) 1 691 (true, (init pL692), (init pL692))) 692 346 false) = true := by
  decide +kernel
theorem L692_ok : RunOK pL692 692 (runFrom pL692 (fmask pL692) (cmask pL692) (hmask pL692) 1 691 (true, (init pL692), (init pL692))) ∧ ptTest pL692 (runFrom pL692 (fmask pL692) (cmask pL692) (hmask pL692) 1 691 (true, (init pL692), (init pL692))) 692 346 false = true :=
  fin_run (runOK_init (prmOK_of_and L692_fin) true) (by decide) rfl L692_fin ptTest_fst
theorem H692_fin : (prmOK pH692 692 && ptTest pH692 (runFrom pH692 (fmask pH692) (cmask pH692) (hmask pH692) 1 691 (true, (init pH692), (init pH692))) 692 346 true) = true := by
  decide +kernel
theorem H692_ok : RunOK pH692 692 (runFrom pH692 (fmask pH692) (cmask pH692) (hmask pH692) 1 691 (true, (init pH692), (init pH692))) ∧ ptTest pH692 (runFrom pH692 (fmask pH692) (cmask pH692) (hmask pH692) 1 691 (true, (init pH692), (init pH692))) 692 346 true = true :=
  fin_run (runOK_init (prmOK_of_and H692_fin) true) (by decide) rfl H692_fin ptTest_fst
theorem I692_fin : (prmOK pI692 692 && intTest pI692 (runFrom pI692 (fmask pI692) (cmask pI692) (hmask pI692) 1 691 (true, (init pI692), (init pI692))) 692 16 true) = true := by
  decide +kernel
theorem I692_ok : RunOK pI692 692 (runFrom pI692 (fmask pI692) (cmask pI692) (hmask pI692) 1 691 (true, (init pI692), (init pI692))) ∧ intTest pI692 (runFrom pI692 (fmask pI692) (cmask pI692) (hmask pI692) 1 691 (true, (init pI692), (init pI692))) 692 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I692_fin) true) (by decide) rfl I692_fin intTest_fst
theorem link692 : linkOK pL692 pH692 pI692 = true := by decide +kernel
theorem cvx692 : ConvexBetweenHumps 692 :=
  cvx_of L692_ok H692_ok I692_ok link692 (by decide)
theorem cenlink692 : cenLinkOK pI692 692 = true := by decide +kernel
theorem cen692 : CenterUniqueMin 692 ∧ DipHyp 692 ∧ OnePointHyps 692 :=
  cen_of L692_ok H692_ok I692_ok link692 cenlink692

/-! ### `N = 693` -/

def pL693 : Prm := ⟨73, 35, 35, 695, 11, 18446744073709551616, 230590307320115171, 230590307320115171⟩
def pH693 : Prm := ⟨72, 34, 35, 695, 11, 18446744073709551616, 230594705366626275, 230594705366626275⟩
def pI693 : Prm := ⟨63, 30, 30, 695, 11, 18446744073709551616, 230590307320115171, 230594705366626275⟩
theorem L693_fin : (prmOK pL693 693 && ptTest pL693 (runFrom pL693 (fmask pL693) (cmask pL693) (hmask pL693) 1 692 (true, (init pL693), (init pL693))) 693 347 false) = true := by
  decide +kernel
theorem L693_ok : RunOK pL693 693 (runFrom pL693 (fmask pL693) (cmask pL693) (hmask pL693) 1 692 (true, (init pL693), (init pL693))) ∧ ptTest pL693 (runFrom pL693 (fmask pL693) (cmask pL693) (hmask pL693) 1 692 (true, (init pL693), (init pL693))) 693 347 false = true :=
  fin_run (runOK_init (prmOK_of_and L693_fin) true) (by decide) rfl L693_fin ptTest_fst
theorem H693_fin : (prmOK pH693 693 && ptTest pH693 (runFrom pH693 (fmask pH693) (cmask pH693) (hmask pH693) 1 692 (true, (init pH693), (init pH693))) 693 347 true) = true := by
  decide +kernel
theorem H693_ok : RunOK pH693 693 (runFrom pH693 (fmask pH693) (cmask pH693) (hmask pH693) 1 692 (true, (init pH693), (init pH693))) ∧ ptTest pH693 (runFrom pH693 (fmask pH693) (cmask pH693) (hmask pH693) 1 692 (true, (init pH693), (init pH693))) 693 347 true = true :=
  fin_run (runOK_init (prmOK_of_and H693_fin) true) (by decide) rfl H693_fin ptTest_fst
theorem I693_fin : (prmOK pI693 693 && intTest pI693 (runFrom pI693 (fmask pI693) (cmask pI693) (hmask pI693) 1 692 (true, (init pI693), (init pI693))) 693 16 false) = true := by
  decide +kernel
theorem I693_ok : RunOK pI693 693 (runFrom pI693 (fmask pI693) (cmask pI693) (hmask pI693) 1 692 (true, (init pI693), (init pI693))) ∧ intTest pI693 (runFrom pI693 (fmask pI693) (cmask pI693) (hmask pI693) 1 692 (true, (init pI693), (init pI693))) 693 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I693_fin) true) (by decide) rfl I693_fin intTest_fst
theorem link693 : linkOK pL693 pH693 pI693 = true := by decide +kernel
theorem cvx693 : ConvexBetweenHumps 693 :=
  cvx_of L693_ok H693_ok I693_ok link693 (by decide)

/-! ### `N = 694` -/

def pL694 : Prm := ⟨73, 35, 35, 696, 11, 18446744073709551616, 230330447242935915, 230330447242935915⟩
def pH694 : Prm := ⟨73, 35, 35, 696, 11, 18446744073709551616, 230334845289447019, 230334845289447019⟩
def pI694 : Prm := ⟨63, 30, 30, 696, 11, 18446744073709551616, 230330447242935915, 230334845289447019⟩
theorem L694_fin : (prmOK pL694 694 && ptTest pL694 (runFrom pL694 (fmask pL694) (cmask pL694) (hmask pL694) 1 693 (true, (init pL694), (init pL694))) 694 347 false) = true := by
  decide +kernel
theorem L694_ok : RunOK pL694 694 (runFrom pL694 (fmask pL694) (cmask pL694) (hmask pL694) 1 693 (true, (init pL694), (init pL694))) ∧ ptTest pL694 (runFrom pL694 (fmask pL694) (cmask pL694) (hmask pL694) 1 693 (true, (init pL694), (init pL694))) 694 347 false = true :=
  fin_run (runOK_init (prmOK_of_and L694_fin) true) (by decide) rfl L694_fin ptTest_fst
theorem H694_fin : (prmOK pH694 694 && ptTest pH694 (runFrom pH694 (fmask pH694) (cmask pH694) (hmask pH694) 1 693 (true, (init pH694), (init pH694))) 694 347 true) = true := by
  decide +kernel
theorem H694_ok : RunOK pH694 694 (runFrom pH694 (fmask pH694) (cmask pH694) (hmask pH694) 1 693 (true, (init pH694), (init pH694))) ∧ ptTest pH694 (runFrom pH694 (fmask pH694) (cmask pH694) (hmask pH694) 1 693 (true, (init pH694), (init pH694))) 694 347 true = true :=
  fin_run (runOK_init (prmOK_of_and H694_fin) true) (by decide) rfl H694_fin ptTest_fst
theorem I694_fin : (prmOK pI694 694 && intTest pI694 (runFrom pI694 (fmask pI694) (cmask pI694) (hmask pI694) 1 693 (true, (init pI694), (init pI694))) 694 16 true) = true := by
  decide +kernel
theorem I694_ok : RunOK pI694 694 (runFrom pI694 (fmask pI694) (cmask pI694) (hmask pI694) 1 693 (true, (init pI694), (init pI694))) ∧ intTest pI694 (runFrom pI694 (fmask pI694) (cmask pI694) (hmask pI694) 1 693 (true, (init pI694), (init pI694))) 694 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I694_fin) true) (by decide) rfl I694_fin intTest_fst
theorem link694 : linkOK pL694 pH694 pI694 = true := by decide +kernel
theorem cvx694 : ConvexBetweenHumps 694 :=
  cvx_of L694_ok H694_ok I694_ok link694 (by decide)
theorem cenlink694 : cenLinkOK pI694 694 = true := by decide +kernel
theorem cen694 : CenterUniqueMin 694 ∧ DipHyp 694 ∧ OnePointHyps 694 :=
  cen_of L694_ok H694_ok I694_ok link694 cenlink694

/-! ### `N = 695` -/

def pL695 : Prm := ⟨73, 35, 35, 697, 11, 18446744073709551616, 230070879266554865, 230070879266554865⟩
def pH695 : Prm := ⟨73, 35, 35, 697, 11, 18446744073709551616, 230075277313065969, 230075277313065969⟩
def pI695 : Prm := ⟨63, 30, 30, 697, 11, 18446744073709551616, 230070879266554865, 230075277313065969⟩
theorem L695_fin : (prmOK pL695 695 && ptTest pL695 (runFrom pL695 (fmask pL695) (cmask pL695) (hmask pL695) 1 694 (true, (init pL695), (init pL695))) 695 348 false) = true := by
  decide +kernel
theorem L695_ok : RunOK pL695 695 (runFrom pL695 (fmask pL695) (cmask pL695) (hmask pL695) 1 694 (true, (init pL695), (init pL695))) ∧ ptTest pL695 (runFrom pL695 (fmask pL695) (cmask pL695) (hmask pL695) 1 694 (true, (init pL695), (init pL695))) 695 348 false = true :=
  fin_run (runOK_init (prmOK_of_and L695_fin) true) (by decide) rfl L695_fin ptTest_fst
theorem H695_fin : (prmOK pH695 695 && ptTest pH695 (runFrom pH695 (fmask pH695) (cmask pH695) (hmask pH695) 1 694 (true, (init pH695), (init pH695))) 695 348 true) = true := by
  decide +kernel
theorem H695_ok : RunOK pH695 695 (runFrom pH695 (fmask pH695) (cmask pH695) (hmask pH695) 1 694 (true, (init pH695), (init pH695))) ∧ ptTest pH695 (runFrom pH695 (fmask pH695) (cmask pH695) (hmask pH695) 1 694 (true, (init pH695), (init pH695))) 695 348 true = true :=
  fin_run (runOK_init (prmOK_of_and H695_fin) true) (by decide) rfl H695_fin ptTest_fst
theorem I695_fin : (prmOK pI695 695 && intTest pI695 (runFrom pI695 (fmask pI695) (cmask pI695) (hmask pI695) 1 694 (true, (init pI695), (init pI695))) 695 16 false) = true := by
  decide +kernel
theorem I695_ok : RunOK pI695 695 (runFrom pI695 (fmask pI695) (cmask pI695) (hmask pI695) 1 694 (true, (init pI695), (init pI695))) ∧ intTest pI695 (runFrom pI695 (fmask pI695) (cmask pI695) (hmask pI695) 1 694 (true, (init pI695), (init pI695))) 695 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I695_fin) true) (by decide) rfl I695_fin intTest_fst
theorem link695 : linkOK pL695 pH695 pI695 = true := by decide +kernel
theorem cvx695 : ConvexBetweenHumps 695 :=
  cvx_of L695_ok H695_ok I695_ok link695 (by decide)

/-! ### `N = 696` -/

def pL696 : Prm := ⟨73, 35, 35, 698, 11, 18446744073709551616, 229812304907902445, 229812304907902445⟩
def pH696 : Prm := ⟨73, 35, 35, 698, 11, 18446744073709551616, 229816702954413549, 229816702954413549⟩
def pI696 : Prm := ⟨63, 30, 30, 698, 11, 18446744073709551616, 229812304907902445, 229816702954413549⟩
theorem L696_fin : (prmOK pL696 696 && ptTest pL696 (runFrom pL696 (fmask pL696) (cmask pL696) (hmask pL696) 1 695 (true, (init pL696), (init pL696))) 696 348 false) = true := by
  decide +kernel
theorem L696_ok : RunOK pL696 696 (runFrom pL696 (fmask pL696) (cmask pL696) (hmask pL696) 1 695 (true, (init pL696), (init pL696))) ∧ ptTest pL696 (runFrom pL696 (fmask pL696) (cmask pL696) (hmask pL696) 1 695 (true, (init pL696), (init pL696))) 696 348 false = true :=
  fin_run (runOK_init (prmOK_of_and L696_fin) true) (by decide) rfl L696_fin ptTest_fst
theorem H696_fin : (prmOK pH696 696 && ptTest pH696 (runFrom pH696 (fmask pH696) (cmask pH696) (hmask pH696) 1 695 (true, (init pH696), (init pH696))) 696 348 true) = true := by
  decide +kernel
theorem H696_ok : RunOK pH696 696 (runFrom pH696 (fmask pH696) (cmask pH696) (hmask pH696) 1 695 (true, (init pH696), (init pH696))) ∧ ptTest pH696 (runFrom pH696 (fmask pH696) (cmask pH696) (hmask pH696) 1 695 (true, (init pH696), (init pH696))) 696 348 true = true :=
  fin_run (runOK_init (prmOK_of_and H696_fin) true) (by decide) rfl H696_fin ptTest_fst
theorem I696_fin : (prmOK pI696 696 && intTest pI696 (runFrom pI696 (fmask pI696) (cmask pI696) (hmask pI696) 1 695 (true, (init pI696), (init pI696))) 696 16 true) = true := by
  decide +kernel
theorem I696_ok : RunOK pI696 696 (runFrom pI696 (fmask pI696) (cmask pI696) (hmask pI696) 1 695 (true, (init pI696), (init pI696))) ∧ intTest pI696 (runFrom pI696 (fmask pI696) (cmask pI696) (hmask pI696) 1 695 (true, (init pI696), (init pI696))) 696 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I696_fin) true) (by decide) rfl I696_fin intTest_fst
theorem link696 : linkOK pL696 pH696 pI696 = true := by decide +kernel
theorem cvx696 : ConvexBetweenHumps 696 :=
  cvx_of L696_ok H696_ok I696_ok link696 (by decide)
theorem cenlink696 : cenLinkOK pI696 696 = true := by decide +kernel
theorem cen696 : CenterUniqueMin 696 ∧ DipHyp 696 ∧ OnePointHyps 696 :=
  cen_of L696_ok H696_ok I696_ok link696 cenlink696

/-! ### `N = 697` -/

def pL697 : Prm := ⟨73, 35, 35, 699, 11, 18446744073709551616, 229554020779511489, 229554020779511489⟩
def pH697 : Prm := ⟨73, 35, 35, 699, 11, 18446744073709551616, 229558418826022593, 229558418826022593⟩
def pI697 : Prm := ⟨63, 30, 30, 699, 11, 18446744073709551616, 229554020779511489, 229558418826022593⟩
theorem L697_fin : (prmOK pL697 697 && ptTest pL697 (runFrom pL697 (fmask pL697) (cmask pL697) (hmask pL697) 1 696 (true, (init pL697), (init pL697))) 697 349 false) = true := by
  decide +kernel
theorem L697_ok : RunOK pL697 697 (runFrom pL697 (fmask pL697) (cmask pL697) (hmask pL697) 1 696 (true, (init pL697), (init pL697))) ∧ ptTest pL697 (runFrom pL697 (fmask pL697) (cmask pL697) (hmask pL697) 1 696 (true, (init pL697), (init pL697))) 697 349 false = true :=
  fin_run (runOK_init (prmOK_of_and L697_fin) true) (by decide) rfl L697_fin ptTest_fst
theorem H697_fin : (prmOK pH697 697 && ptTest pH697 (runFrom pH697 (fmask pH697) (cmask pH697) (hmask pH697) 1 696 (true, (init pH697), (init pH697))) 697 349 true) = true := by
  decide +kernel
theorem H697_ok : RunOK pH697 697 (runFrom pH697 (fmask pH697) (cmask pH697) (hmask pH697) 1 696 (true, (init pH697), (init pH697))) ∧ ptTest pH697 (runFrom pH697 (fmask pH697) (cmask pH697) (hmask pH697) 1 696 (true, (init pH697), (init pH697))) 697 349 true = true :=
  fin_run (runOK_init (prmOK_of_and H697_fin) true) (by decide) rfl H697_fin ptTest_fst
theorem I697_fin : (prmOK pI697 697 && intTest pI697 (runFrom pI697 (fmask pI697) (cmask pI697) (hmask pI697) 1 696 (true, (init pI697), (init pI697))) 697 16 false) = true := by
  decide +kernel
theorem I697_ok : RunOK pI697 697 (runFrom pI697 (fmask pI697) (cmask pI697) (hmask pI697) 1 696 (true, (init pI697), (init pI697))) ∧ intTest pI697 (runFrom pI697 (fmask pI697) (cmask pI697) (hmask pI697) 1 696 (true, (init pI697), (init pI697))) 697 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I697_fin) true) (by decide) rfl I697_fin intTest_fst
theorem link697 : linkOK pL697 pH697 pI697 = true := by decide +kernel
theorem cvx697 : ConvexBetweenHumps 697 :=
  cvx_of L697_ok H697_ok I697_ok link697 (by decide)

/-! ### `N = 698` -/

def pL698 : Prm := ⟨73, 35, 35, 700, 11, 18446744073709551616, 229296722268274896, 229296722268274896⟩
def pH698 : Prm := ⟨73, 35, 35, 700, 11, 18446744073709551616, 229301120314786000, 229301120314786000⟩
def pI698 : Prm := ⟨63, 30, 30, 700, 11, 18446744073709551616, 229296722268274896, 229301120314786000⟩
theorem L698_fin : (prmOK pL698 698 && ptTest pL698 (runFrom pL698 (fmask pL698) (cmask pL698) (hmask pL698) 1 697 (true, (init pL698), (init pL698))) 698 349 false) = true := by
  decide +kernel
theorem L698_ok : RunOK pL698 698 (runFrom pL698 (fmask pL698) (cmask pL698) (hmask pL698) 1 697 (true, (init pL698), (init pL698))) ∧ ptTest pL698 (runFrom pL698 (fmask pL698) (cmask pL698) (hmask pL698) 1 697 (true, (init pL698), (init pL698))) 698 349 false = true :=
  fin_run (runOK_init (prmOK_of_and L698_fin) true) (by decide) rfl L698_fin ptTest_fst
theorem H698_fin : (prmOK pH698 698 && ptTest pH698 (runFrom pH698 (fmask pH698) (cmask pH698) (hmask pH698) 1 697 (true, (init pH698), (init pH698))) 698 349 true) = true := by
  decide +kernel
theorem H698_ok : RunOK pH698 698 (runFrom pH698 (fmask pH698) (cmask pH698) (hmask pH698) 1 697 (true, (init pH698), (init pH698))) ∧ ptTest pH698 (runFrom pH698 (fmask pH698) (cmask pH698) (hmask pH698) 1 697 (true, (init pH698), (init pH698))) 698 349 true = true :=
  fin_run (runOK_init (prmOK_of_and H698_fin) true) (by decide) rfl H698_fin ptTest_fst
theorem I698_fin : (prmOK pI698 698 && intTest pI698 (runFrom pI698 (fmask pI698) (cmask pI698) (hmask pI698) 1 697 (true, (init pI698), (init pI698))) 698 16 true) = true := by
  decide +kernel
theorem I698_ok : RunOK pI698 698 (runFrom pI698 (fmask pI698) (cmask pI698) (hmask pI698) 1 697 (true, (init pI698), (init pI698))) ∧ intTest pI698 (runFrom pI698 (fmask pI698) (cmask pI698) (hmask pI698) 1 697 (true, (init pI698), (init pI698))) 698 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I698_fin) true) (by decide) rfl I698_fin intTest_fst
theorem link698 : linkOK pL698 pH698 pI698 = true := by decide +kernel
theorem cvx698 : ConvexBetweenHumps 698 :=
  cvx_of L698_ok H698_ok I698_ok link698 (by decide)
theorem cenlink698 : cenLinkOK pI698 698 = true := by decide +kernel
theorem cen698 : CenterUniqueMin 698 ∧ DipHyp 698 ∧ OnePointHyps 698 :=
  cen_of L698_ok H698_ok I698_ok link698 cenlink698

/-! ### `N = 699` -/

def pL699 : Prm := ⟨73, 35, 35, 701, 11, 18446744073709551616, 229039712132701011, 229039712132701011⟩
def pH699 : Prm := ⟨73, 35, 35, 701, 11, 18446744073709551616, 229044110179212115, 229044110179212115⟩
def pI699 : Prm := ⟨63, 30, 30, 701, 11, 18446744073709551616, 229039712132701011, 229044110179212115⟩
theorem L699_fin : (prmOK pL699 699 && ptTest pL699 (runFrom pL699 (fmask pL699) (cmask pL699) (hmask pL699) 1 698 (true, (init pL699), (init pL699))) 699 350 false) = true := by
  decide +kernel
theorem L699_ok : RunOK pL699 699 (runFrom pL699 (fmask pL699) (cmask pL699) (hmask pL699) 1 698 (true, (init pL699), (init pL699))) ∧ ptTest pL699 (runFrom pL699 (fmask pL699) (cmask pL699) (hmask pL699) 1 698 (true, (init pL699), (init pL699))) 699 350 false = true :=
  fin_run (runOK_init (prmOK_of_and L699_fin) true) (by decide) rfl L699_fin ptTest_fst
theorem H699_fin : (prmOK pH699 699 && ptTest pH699 (runFrom pH699 (fmask pH699) (cmask pH699) (hmask pH699) 1 698 (true, (init pH699), (init pH699))) 699 350 true) = true := by
  decide +kernel
theorem H699_ok : RunOK pH699 699 (runFrom pH699 (fmask pH699) (cmask pH699) (hmask pH699) 1 698 (true, (init pH699), (init pH699))) ∧ ptTest pH699 (runFrom pH699 (fmask pH699) (cmask pH699) (hmask pH699) 1 698 (true, (init pH699), (init pH699))) 699 350 true = true :=
  fin_run (runOK_init (prmOK_of_and H699_fin) true) (by decide) rfl H699_fin ptTest_fst
theorem I699_fin : (prmOK pI699 699 && intTest pI699 (runFrom pI699 (fmask pI699) (cmask pI699) (hmask pI699) 1 698 (true, (init pI699), (init pI699))) 699 16 false) = true := by
  decide +kernel
theorem I699_ok : RunOK pI699 699 (runFrom pI699 (fmask pI699) (cmask pI699) (hmask pI699) 1 698 (true, (init pI699), (init pI699))) ∧ intTest pI699 (runFrom pI699 (fmask pI699) (cmask pI699) (hmask pI699) 1 698 (true, (init pI699), (init pI699))) 699 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I699_fin) true) (by decide) rfl I699_fin intTest_fst
theorem link699 : linkOK pL699 pH699 pI699 = true := by decide +kernel
theorem cvx699 : ConvexBetweenHumps 699 :=
  cvx_of L699_ok H699_ok I699_ok link699 (by decide)

/-! ### `N = 700` -/

def pL700 : Prm := ⟨73, 35, 35, 702, 11, 18446744073709551616, 228783679700554495, 228783679700554495⟩
def pH700 : Prm := ⟨73, 35, 35, 702, 11, 18446744073709551616, 228788077747065599, 228788077747065599⟩
def pI700 : Prm := ⟨62, 31, 28, 702, 11, 18446744073709551616, 228783679700554495, 228788077747065599⟩
theorem L700_fin : (prmOK pL700 700 && ptTest pL700 (runFrom pL700 (fmask pL700) (cmask pL700) (hmask pL700) 1 699 (true, (init pL700), (init pL700))) 700 350 false) = true := by
  decide +kernel
theorem L700_ok : RunOK pL700 700 (runFrom pL700 (fmask pL700) (cmask pL700) (hmask pL700) 1 699 (true, (init pL700), (init pL700))) ∧ ptTest pL700 (runFrom pL700 (fmask pL700) (cmask pL700) (hmask pL700) 1 699 (true, (init pL700), (init pL700))) 700 350 false = true :=
  fin_run (runOK_init (prmOK_of_and L700_fin) true) (by decide) rfl L700_fin ptTest_fst
theorem H700_fin : (prmOK pH700 700 && ptTest pH700 (runFrom pH700 (fmask pH700) (cmask pH700) (hmask pH700) 1 699 (true, (init pH700), (init pH700))) 700 350 true) = true := by
  decide +kernel
theorem H700_ok : RunOK pH700 700 (runFrom pH700 (fmask pH700) (cmask pH700) (hmask pH700) 1 699 (true, (init pH700), (init pH700))) ∧ ptTest pH700 (runFrom pH700 (fmask pH700) (cmask pH700) (hmask pH700) 1 699 (true, (init pH700), (init pH700))) 700 350 true = true :=
  fin_run (runOK_init (prmOK_of_and H700_fin) true) (by decide) rfl H700_fin ptTest_fst
theorem I700_fin : (prmOK pI700 700 && intTest pI700 (runFrom pI700 (fmask pI700) (cmask pI700) (hmask pI700) 1 699 (true, (init pI700), (init pI700))) 700 16 true) = true := by
  decide +kernel
theorem I700_ok : RunOK pI700 700 (runFrom pI700 (fmask pI700) (cmask pI700) (hmask pI700) 1 699 (true, (init pI700), (init pI700))) ∧ intTest pI700 (runFrom pI700 (fmask pI700) (cmask pI700) (hmask pI700) 1 699 (true, (init pI700), (init pI700))) 700 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I700_fin) true) (by decide) rfl I700_fin intTest_fst
theorem link700 : linkOK pL700 pH700 pI700 = true := by decide +kernel
theorem cvx700 : ConvexBetweenHumps 700 :=
  cvx_of L700_ok H700_ok I700_ok link700 (by decide)
theorem cenlink700 : cenLinkOK pI700 700 = true := by decide +kernel
theorem cen700 : CenterUniqueMin 700 ∧ DipHyp 700 ∧ OnePointHyps 700 :=
  cen_of L700_ok H700_ok I700_ok link700 cenlink700

/-! ### `N = 701` -/

def pL701 : Prm := ⟨73, 35, 35, 703, 11, 18446744073709551616, 228527933805317685, 228527933805317685⟩
def pH701 : Prm := ⟨73, 35, 35, 703, 11, 18446744073709551616, 228532331851828789, 228532331851828789⟩
def pI701 : Prm := ⟨62, 31, 28, 703, 11, 18446744073709551616, 228527933805317685, 228532331851828789⟩
theorem L701_fin : (prmOK pL701 701 && ptTest pL701 (runFrom pL701 (fmask pL701) (cmask pL701) (hmask pL701) 1 700 (true, (init pL701), (init pL701))) 701 351 false) = true := by
  decide +kernel
theorem L701_ok : RunOK pL701 701 (runFrom pL701 (fmask pL701) (cmask pL701) (hmask pL701) 1 700 (true, (init pL701), (init pL701))) ∧ ptTest pL701 (runFrom pL701 (fmask pL701) (cmask pL701) (hmask pL701) 1 700 (true, (init pL701), (init pL701))) 701 351 false = true :=
  fin_run (runOK_init (prmOK_of_and L701_fin) true) (by decide) rfl L701_fin ptTest_fst
theorem H701_fin : (prmOK pH701 701 && ptTest pH701 (runFrom pH701 (fmask pH701) (cmask pH701) (hmask pH701) 1 700 (true, (init pH701), (init pH701))) 701 351 true) = true := by
  decide +kernel
theorem H701_ok : RunOK pH701 701 (runFrom pH701 (fmask pH701) (cmask pH701) (hmask pH701) 1 700 (true, (init pH701), (init pH701))) ∧ ptTest pH701 (runFrom pH701 (fmask pH701) (cmask pH701) (hmask pH701) 1 700 (true, (init pH701), (init pH701))) 701 351 true = true :=
  fin_run (runOK_init (prmOK_of_and H701_fin) true) (by decide) rfl H701_fin ptTest_fst
theorem I701_fin : (prmOK pI701 701 && intTest pI701 (runFrom pI701 (fmask pI701) (cmask pI701) (hmask pI701) 1 700 (true, (init pI701), (init pI701))) 701 16 false) = true := by
  decide +kernel
theorem I701_ok : RunOK pI701 701 (runFrom pI701 (fmask pI701) (cmask pI701) (hmask pI701) 1 700 (true, (init pI701), (init pI701))) ∧ intTest pI701 (runFrom pI701 (fmask pI701) (cmask pI701) (hmask pI701) 1 700 (true, (init pI701), (init pI701))) 701 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I701_fin) true) (by decide) rfl I701_fin intTest_fst
theorem link701 : linkOK pL701 pH701 pI701 = true := by decide +kernel
theorem cvx701 : ConvexBetweenHumps 701 :=
  cvx_of L701_ok H701_ok I701_ok link701 (by decide)

/-! ### `N = 702` -/

def pL702 : Prm := ⟨73, 35, 35, 704, 11, 18446744073709551616, 228273157785392588, 228273157785392588⟩
def pH702 : Prm := ⟨73, 35, 35, 704, 11, 18446744073709551616, 228277555831903692, 228277555831903692⟩
def pI702 : Prm := ⟨62, 31, 28, 704, 11, 18446744073709551616, 228273157785392588, 228277555831903692⟩
theorem L702_fin : (prmOK pL702 702 && ptTest pL702 (runFrom pL702 (fmask pL702) (cmask pL702) (hmask pL702) 1 701 (true, (init pL702), (init pL702))) 702 351 false) = true := by
  decide +kernel
theorem L702_ok : RunOK pL702 702 (runFrom pL702 (fmask pL702) (cmask pL702) (hmask pL702) 1 701 (true, (init pL702), (init pL702))) ∧ ptTest pL702 (runFrom pL702 (fmask pL702) (cmask pL702) (hmask pL702) 1 701 (true, (init pL702), (init pL702))) 702 351 false = true :=
  fin_run (runOK_init (prmOK_of_and L702_fin) true) (by decide) rfl L702_fin ptTest_fst
theorem H702_fin : (prmOK pH702 702 && ptTest pH702 (runFrom pH702 (fmask pH702) (cmask pH702) (hmask pH702) 1 701 (true, (init pH702), (init pH702))) 702 351 true) = true := by
  decide +kernel
theorem H702_ok : RunOK pH702 702 (runFrom pH702 (fmask pH702) (cmask pH702) (hmask pH702) 1 701 (true, (init pH702), (init pH702))) ∧ ptTest pH702 (runFrom pH702 (fmask pH702) (cmask pH702) (hmask pH702) 1 701 (true, (init pH702), (init pH702))) 702 351 true = true :=
  fin_run (runOK_init (prmOK_of_and H702_fin) true) (by decide) rfl H702_fin ptTest_fst
theorem I702_fin : (prmOK pI702 702 && intTest pI702 (runFrom pI702 (fmask pI702) (cmask pI702) (hmask pI702) 1 701 (true, (init pI702), (init pI702))) 702 16 true) = true := by
  decide +kernel
theorem I702_ok : RunOK pI702 702 (runFrom pI702 (fmask pI702) (cmask pI702) (hmask pI702) 1 701 (true, (init pI702), (init pI702))) ∧ intTest pI702 (runFrom pI702 (fmask pI702) (cmask pI702) (hmask pI702) 1 701 (true, (init pI702), (init pI702))) 702 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I702_fin) true) (by decide) rfl I702_fin intTest_fst
theorem link702 : linkOK pL702 pH702 pI702 = true := by decide +kernel
theorem cvx702 : ConvexBetweenHumps 702 :=
  cvx_of L702_ok H702_ok I702_ok link702 (by decide)
theorem cenlink702 : cenLinkOK pI702 702 = true := by decide +kernel
theorem cen702 : CenterUniqueMin 702 ∧ DipHyp 702 ∧ OnePointHyps 702 :=
  cen_of L702_ok H702_ok I702_ok link702 cenlink702

/-! ### `N = 703` -/

def pL703 : Prm := ⟨73, 35, 35, 705, 11, 18446744073709551616, 228018666479230140, 228018666479230140⟩
def pH703 : Prm := ⟨73, 35, 35, 705, 11, 18446744073709551616, 228023064525741244, 228023064525741244⟩
def pI703 : Prm := ⟨62, 31, 28, 705, 11, 18446744073709551616, 228018666479230140, 228023064525741244⟩
theorem L703_fin : (prmOK pL703 703 && ptTest pL703 (runFrom pL703 (fmask pL703) (cmask pL703) (hmask pL703) 1 702 (true, (init pL703), (init pL703))) 703 352 false) = true := by
  decide +kernel
theorem L703_ok : RunOK pL703 703 (runFrom pL703 (fmask pL703) (cmask pL703) (hmask pL703) 1 702 (true, (init pL703), (init pL703))) ∧ ptTest pL703 (runFrom pL703 (fmask pL703) (cmask pL703) (hmask pL703) 1 702 (true, (init pL703), (init pL703))) 703 352 false = true :=
  fin_run (runOK_init (prmOK_of_and L703_fin) true) (by decide) rfl L703_fin ptTest_fst
theorem H703_fin : (prmOK pH703 703 && ptTest pH703 (runFrom pH703 (fmask pH703) (cmask pH703) (hmask pH703) 1 702 (true, (init pH703), (init pH703))) 703 352 true) = true := by
  decide +kernel
theorem H703_ok : RunOK pH703 703 (runFrom pH703 (fmask pH703) (cmask pH703) (hmask pH703) 1 702 (true, (init pH703), (init pH703))) ∧ ptTest pH703 (runFrom pH703 (fmask pH703) (cmask pH703) (hmask pH703) 1 702 (true, (init pH703), (init pH703))) 703 352 true = true :=
  fin_run (runOK_init (prmOK_of_and H703_fin) true) (by decide) rfl H703_fin ptTest_fst
theorem I703_fin : (prmOK pI703 703 && intTest pI703 (runFrom pI703 (fmask pI703) (cmask pI703) (hmask pI703) 1 702 (true, (init pI703), (init pI703))) 703 16 false) = true := by
  decide +kernel
theorem I703_ok : RunOK pI703 703 (runFrom pI703 (fmask pI703) (cmask pI703) (hmask pI703) 1 702 (true, (init pI703), (init pI703))) ∧ intTest pI703 (runFrom pI703 (fmask pI703) (cmask pI703) (hmask pI703) 1 702 (true, (init pI703), (init pI703))) 703 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I703_fin) true) (by decide) rfl I703_fin intTest_fst
theorem link703 : linkOK pL703 pH703 pI703 = true := by decide +kernel
theorem cvx703 : ConvexBetweenHumps 703 :=
  cvx_of L703_ok H703_ok I703_ok link703 (by decide)

/-! ### `N = 704` -/

def pL704 : Prm := ⟨73, 35, 35, 706, 11, 18446744073709551616, 227765137304805178, 227765137304805178⟩
def pH704 : Prm := ⟨73, 35, 35, 706, 11, 18446744073709551616, 227769535351316282, 227769535351316282⟩
def pI704 : Prm := ⟨62, 31, 28, 706, 11, 18446744073709551616, 227765137304805178, 227769535351316282⟩
theorem L704_fin : (prmOK pL704 704 && ptTest pL704 (runFrom pL704 (fmask pL704) (cmask pL704) (hmask pL704) 1 703 (true, (init pL704), (init pL704))) 704 352 false) = true := by
  decide +kernel
theorem L704_ok : RunOK pL704 704 (runFrom pL704 (fmask pL704) (cmask pL704) (hmask pL704) 1 703 (true, (init pL704), (init pL704))) ∧ ptTest pL704 (runFrom pL704 (fmask pL704) (cmask pL704) (hmask pL704) 1 703 (true, (init pL704), (init pL704))) 704 352 false = true :=
  fin_run (runOK_init (prmOK_of_and L704_fin) true) (by decide) rfl L704_fin ptTest_fst
theorem H704_fin : (prmOK pH704 704 && ptTest pH704 (runFrom pH704 (fmask pH704) (cmask pH704) (hmask pH704) 1 703 (true, (init pH704), (init pH704))) 704 352 true) = true := by
  decide +kernel
theorem H704_ok : RunOK pH704 704 (runFrom pH704 (fmask pH704) (cmask pH704) (hmask pH704) 1 703 (true, (init pH704), (init pH704))) ∧ ptTest pH704 (runFrom pH704 (fmask pH704) (cmask pH704) (hmask pH704) 1 703 (true, (init pH704), (init pH704))) 704 352 true = true :=
  fin_run (runOK_init (prmOK_of_and H704_fin) true) (by decide) rfl H704_fin ptTest_fst
theorem I704_fin : (prmOK pI704 704 && intTest pI704 (runFrom pI704 (fmask pI704) (cmask pI704) (hmask pI704) 1 703 (true, (init pI704), (init pI704))) 704 16 true) = true := by
  decide +kernel
theorem I704_ok : RunOK pI704 704 (runFrom pI704 (fmask pI704) (cmask pI704) (hmask pI704) 1 703 (true, (init pI704), (init pI704))) ∧ intTest pI704 (runFrom pI704 (fmask pI704) (cmask pI704) (hmask pI704) 1 703 (true, (init pI704), (init pI704))) 704 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I704_fin) true) (by decide) rfl I704_fin intTest_fst
theorem link704 : linkOK pL704 pH704 pI704 = true := by decide +kernel
theorem cvx704 : ConvexBetweenHumps 704 :=
  cvx_of L704_ok H704_ok I704_ok link704 (by decide)
theorem cenlink704 : cenLinkOK pI704 704 = true := by decide +kernel
theorem cen704 : CenterUniqueMin 704 ∧ DipHyp 704 ∧ OnePointHyps 704 :=
  cen_of L704_ok H704_ok I704_ok link704 cenlink704

/-! ### `N = 705` -/

def pL705 : Prm := ⟨73, 35, 35, 707, 11, 18446744073709551616, 227511891036454179, 227511891036454179⟩
def pH705 : Prm := ⟨73, 35, 35, 707, 11, 18446744073709551616, 227516289082965283, 227516289082965283⟩
def pI705 : Prm := ⟨62, 31, 28, 707, 11, 18446744073709551616, 227511891036454179, 227516289082965283⟩
theorem L705_fin : (prmOK pL705 705 && ptTest pL705 (runFrom pL705 (fmask pL705) (cmask pL705) (hmask pL705) 1 704 (true, (init pL705), (init pL705))) 705 353 false) = true := by
  decide +kernel
theorem L705_ok : RunOK pL705 705 (runFrom pL705 (fmask pL705) (cmask pL705) (hmask pL705) 1 704 (true, (init pL705), (init pL705))) ∧ ptTest pL705 (runFrom pL705 (fmask pL705) (cmask pL705) (hmask pL705) 1 704 (true, (init pL705), (init pL705))) 705 353 false = true :=
  fin_run (runOK_init (prmOK_of_and L705_fin) true) (by decide) rfl L705_fin ptTest_fst
theorem H705_fin : (prmOK pH705 705 && ptTest pH705 (runFrom pH705 (fmask pH705) (cmask pH705) (hmask pH705) 1 704 (true, (init pH705), (init pH705))) 705 353 true) = true := by
  decide +kernel
theorem H705_ok : RunOK pH705 705 (runFrom pH705 (fmask pH705) (cmask pH705) (hmask pH705) 1 704 (true, (init pH705), (init pH705))) ∧ ptTest pH705 (runFrom pH705 (fmask pH705) (cmask pH705) (hmask pH705) 1 704 (true, (init pH705), (init pH705))) 705 353 true = true :=
  fin_run (runOK_init (prmOK_of_and H705_fin) true) (by decide) rfl H705_fin ptTest_fst
theorem I705_fin : (prmOK pI705 705 && intTest pI705 (runFrom pI705 (fmask pI705) (cmask pI705) (hmask pI705) 1 704 (true, (init pI705), (init pI705))) 705 16 false) = true := by
  decide +kernel
theorem I705_ok : RunOK pI705 705 (runFrom pI705 (fmask pI705) (cmask pI705) (hmask pI705) 1 704 (true, (init pI705), (init pI705))) ∧ intTest pI705 (runFrom pI705 (fmask pI705) (cmask pI705) (hmask pI705) 1 704 (true, (init pI705), (init pI705))) 705 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I705_fin) true) (by decide) rfl I705_fin intTest_fst
theorem link705 : linkOK pL705 pH705 pI705 = true := by decide +kernel
theorem cvx705 : ConvexBetweenHumps 705 :=
  cvx_of L705_ok H705_ok I705_ok link705 (by decide)

/-! ### `N = 706` -/

def pL706 : Prm := ⟨73, 35, 35, 708, 11, 18446744073709551616, 227259599239571935, 227259599239571935⟩
def pH706 : Prm := ⟨73, 35, 35, 708, 11, 18446744073709551616, 227263997286083039, 227263997286083039⟩
def pI706 : Prm := ⟨62, 31, 28, 708, 11, 18446744073709551616, 227259599239571935, 227263997286083039⟩
theorem L706_fin : (prmOK pL706 706 && ptTest pL706 (runFrom pL706 (fmask pL706) (cmask pL706) (hmask pL706) 1 705 (true, (init pL706), (init pL706))) 706 353 false) = true := by
  decide +kernel
theorem L706_ok : RunOK pL706 706 (runFrom pL706 (fmask pL706) (cmask pL706) (hmask pL706) 1 705 (true, (init pL706), (init pL706))) ∧ ptTest pL706 (runFrom pL706 (fmask pL706) (cmask pL706) (hmask pL706) 1 705 (true, (init pL706), (init pL706))) 706 353 false = true :=
  fin_run (runOK_init (prmOK_of_and L706_fin) true) (by decide) rfl L706_fin ptTest_fst
theorem H706_fin : (prmOK pH706 706 && ptTest pH706 (runFrom pH706 (fmask pH706) (cmask pH706) (hmask pH706) 1 705 (true, (init pH706), (init pH706))) 706 353 true) = true := by
  decide +kernel
theorem H706_ok : RunOK pH706 706 (runFrom pH706 (fmask pH706) (cmask pH706) (hmask pH706) 1 705 (true, (init pH706), (init pH706))) ∧ ptTest pH706 (runFrom pH706 (fmask pH706) (cmask pH706) (hmask pH706) 1 705 (true, (init pH706), (init pH706))) 706 353 true = true :=
  fin_run (runOK_init (prmOK_of_and H706_fin) true) (by decide) rfl H706_fin ptTest_fst
theorem I706_fin : (prmOK pI706 706 && intTest pI706 (runFrom pI706 (fmask pI706) (cmask pI706) (hmask pI706) 1 705 (true, (init pI706), (init pI706))) 706 16 true) = true := by
  decide +kernel
theorem I706_ok : RunOK pI706 706 (runFrom pI706 (fmask pI706) (cmask pI706) (hmask pI706) 1 705 (true, (init pI706), (init pI706))) ∧ intTest pI706 (runFrom pI706 (fmask pI706) (cmask pI706) (hmask pI706) 1 705 (true, (init pI706), (init pI706))) 706 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I706_fin) true) (by decide) rfl I706_fin intTest_fst
theorem link706 : linkOK pL706 pH706 pI706 = true := by decide +kernel
theorem cvx706 : ConvexBetweenHumps 706 :=
  cvx_of L706_ok H706_ok I706_ok link706 (by decide)
theorem cenlink706 : cenLinkOK pI706 706 = true := by decide +kernel
theorem cen706 : CenterUniqueMin 706 ∧ DipHyp 706 ∧ OnePointHyps 706 :=
  cen_of L706_ok H706_ok I706_ok link706 cenlink706

/-! ### `N = 707` -/

def pL707 : Prm := ⟨73, 35, 35, 709, 11, 18446744073709551616, 227007588556459554, 227007588556459554⟩
def pH707 : Prm := ⟨73, 35, 35, 709, 11, 18446744073709551616, 227011986602970658, 227011986602970658⟩
def pI707 : Prm := ⟨62, 31, 28, 709, 11, 18446744073709551616, 227007588556459554, 227011986602970658⟩
theorem L707_fin : (prmOK pL707 707 && ptTest pL707 (runFrom pL707 (fmask pL707) (cmask pL707) (hmask pL707) 1 706 (true, (init pL707), (init pL707))) 707 354 false) = true := by
  decide +kernel
theorem L707_ok : RunOK pL707 707 (runFrom pL707 (fmask pL707) (cmask pL707) (hmask pL707) 1 706 (true, (init pL707), (init pL707))) ∧ ptTest pL707 (runFrom pL707 (fmask pL707) (cmask pL707) (hmask pL707) 1 706 (true, (init pL707), (init pL707))) 707 354 false = true :=
  fin_run (runOK_init (prmOK_of_and L707_fin) true) (by decide) rfl L707_fin ptTest_fst
theorem H707_fin : (prmOK pH707 707 && ptTest pH707 (runFrom pH707 (fmask pH707) (cmask pH707) (hmask pH707) 1 706 (true, (init pH707), (init pH707))) 707 354 true) = true := by
  decide +kernel
theorem H707_ok : RunOK pH707 707 (runFrom pH707 (fmask pH707) (cmask pH707) (hmask pH707) 1 706 (true, (init pH707), (init pH707))) ∧ ptTest pH707 (runFrom pH707 (fmask pH707) (cmask pH707) (hmask pH707) 1 706 (true, (init pH707), (init pH707))) 707 354 true = true :=
  fin_run (runOK_init (prmOK_of_and H707_fin) true) (by decide) rfl H707_fin ptTest_fst
theorem I707_fin : (prmOK pI707 707 && intTest pI707 (runFrom pI707 (fmask pI707) (cmask pI707) (hmask pI707) 1 706 (true, (init pI707), (init pI707))) 707 16 false) = true := by
  decide +kernel
theorem I707_ok : RunOK pI707 707 (runFrom pI707 (fmask pI707) (cmask pI707) (hmask pI707) 1 706 (true, (init pI707), (init pI707))) ∧ intTest pI707 (runFrom pI707 (fmask pI707) (cmask pI707) (hmask pI707) 1 706 (true, (init pI707), (init pI707))) 707 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I707_fin) true) (by decide) rfl I707_fin intTest_fst
theorem link707 : linkOK pL707 pH707 pI707 = true := by decide +kernel
theorem cvx707 : ConvexBetweenHumps 707 :=
  cvx_of L707_ok H707_ok I707_ok link707 (by decide)

/-! ### `N = 708` -/

def pL708 : Prm := ⟨73, 35, 35, 710, 11, 18446744073709551616, 226756524766727442, 226756524766727442⟩
def pH708 : Prm := ⟨73, 35, 35, 710, 11, 18446744073709551616, 226760922813238546, 226760922813238546⟩
def pI708 : Prm := ⟨62, 31, 28, 710, 11, 18446744073709551616, 226756524766727442, 226760922813238546⟩
theorem L708_fin : (prmOK pL708 708 && ptTest pL708 (runFrom pL708 (fmask pL708) (cmask pL708) (hmask pL708) 1 707 (true, (init pL708), (init pL708))) 708 354 false) = true := by
  decide +kernel
theorem L708_ok : RunOK pL708 708 (runFrom pL708 (fmask pL708) (cmask pL708) (hmask pL708) 1 707 (true, (init pL708), (init pL708))) ∧ ptTest pL708 (runFrom pL708 (fmask pL708) (cmask pL708) (hmask pL708) 1 707 (true, (init pL708), (init pL708))) 708 354 false = true :=
  fin_run (runOK_init (prmOK_of_and L708_fin) true) (by decide) rfl L708_fin ptTest_fst
theorem H708_fin : (prmOK pH708 708 && ptTest pH708 (runFrom pH708 (fmask pH708) (cmask pH708) (hmask pH708) 1 707 (true, (init pH708), (init pH708))) 708 354 true) = true := by
  decide +kernel
theorem H708_ok : RunOK pH708 708 (runFrom pH708 (fmask pH708) (cmask pH708) (hmask pH708) 1 707 (true, (init pH708), (init pH708))) ∧ ptTest pH708 (runFrom pH708 (fmask pH708) (cmask pH708) (hmask pH708) 1 707 (true, (init pH708), (init pH708))) 708 354 true = true :=
  fin_run (runOK_init (prmOK_of_and H708_fin) true) (by decide) rfl H708_fin ptTest_fst
theorem I708_fin : (prmOK pI708 708 && intTest pI708 (runFrom pI708 (fmask pI708) (cmask pI708) (hmask pI708) 1 707 (true, (init pI708), (init pI708))) 708 16 true) = true := by
  decide +kernel
theorem I708_ok : RunOK pI708 708 (runFrom pI708 (fmask pI708) (cmask pI708) (hmask pI708) 1 707 (true, (init pI708), (init pI708))) ∧ intTest pI708 (runFrom pI708 (fmask pI708) (cmask pI708) (hmask pI708) 1 707 (true, (init pI708), (init pI708))) 708 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I708_fin) true) (by decide) rfl I708_fin intTest_fst
theorem link708 : linkOK pL708 pH708 pI708 = true := by decide +kernel
theorem cvx708 : ConvexBetweenHumps 708 :=
  cvx_of L708_ok H708_ok I708_ok link708 (by decide)
theorem cenlink708 : cenLinkOK pI708 708 = true := by decide +kernel
theorem cen708 : CenterUniqueMin 708 ∧ DipHyp 708 ∧ OnePointHyps 708 :=
  cen_of L708_ok H708_ok I708_ok link708 cenlink708

/-! ### `N = 709` -/

def pL709 : Prm := ⟨73, 35, 35, 711, 11, 18446744073709551616, 226505740313568974, 226505740313568974⟩
def pH709 : Prm := ⟨73, 35, 35, 711, 11, 18446744073709551616, 226510138360080078, 226510138360080078⟩
def pI709 : Prm := ⟨62, 31, 28, 711, 11, 18446744073709551616, 226505740313568974, 226510138360080078⟩
theorem L709_fin : (prmOK pL709 709 && ptTest pL709 (runFrom pL709 (fmask pL709) (cmask pL709) (hmask pL709) 1 708 (true, (init pL709), (init pL709))) 709 355 false) = true := by
  decide +kernel
theorem L709_ok : RunOK pL709 709 (runFrom pL709 (fmask pL709) (cmask pL709) (hmask pL709) 1 708 (true, (init pL709), (init pL709))) ∧ ptTest pL709 (runFrom pL709 (fmask pL709) (cmask pL709) (hmask pL709) 1 708 (true, (init pL709), (init pL709))) 709 355 false = true :=
  fin_run (runOK_init (prmOK_of_and L709_fin) true) (by decide) rfl L709_fin ptTest_fst
theorem H709_fin : (prmOK pH709 709 && ptTest pH709 (runFrom pH709 (fmask pH709) (cmask pH709) (hmask pH709) 1 708 (true, (init pH709), (init pH709))) 709 355 true) = true := by
  decide +kernel
theorem H709_ok : RunOK pH709 709 (runFrom pH709 (fmask pH709) (cmask pH709) (hmask pH709) 1 708 (true, (init pH709), (init pH709))) ∧ ptTest pH709 (runFrom pH709 (fmask pH709) (cmask pH709) (hmask pH709) 1 708 (true, (init pH709), (init pH709))) 709 355 true = true :=
  fin_run (runOK_init (prmOK_of_and H709_fin) true) (by decide) rfl H709_fin ptTest_fst
theorem I709_fin : (prmOK pI709 709 && intTest pI709 (runFrom pI709 (fmask pI709) (cmask pI709) (hmask pI709) 1 708 (true, (init pI709), (init pI709))) 709 16 false) = true := by
  decide +kernel
theorem I709_ok : RunOK pI709 709 (runFrom pI709 (fmask pI709) (cmask pI709) (hmask pI709) 1 708 (true, (init pI709), (init pI709))) ∧ intTest pI709 (runFrom pI709 (fmask pI709) (cmask pI709) (hmask pI709) 1 708 (true, (init pI709), (init pI709))) 709 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I709_fin) true) (by decide) rfl I709_fin intTest_fst
theorem link709 : linkOK pL709 pH709 pI709 = true := by decide +kernel
theorem cvx709 : ConvexBetweenHumps 709 :=
  cvx_of L709_ok H709_ok I709_ok link709 (by decide)

/-! ### `N = 710` -/

def pL710 : Prm := ⟨73, 35, 35, 712, 11, 18446744073709551616, 226255895256849516, 226255895256849516⟩
def pH710 : Prm := ⟨73, 35, 35, 712, 11, 18446744073709551616, 226260293303360620, 226260293303360620⟩
def pI710 : Prm := ⟨62, 31, 28, 712, 11, 18446744073709551616, 226255895256849516, 226260293303360620⟩
theorem L710_fin : (prmOK pL710 710 && ptTest pL710 (runFrom pL710 (fmask pL710) (cmask pL710) (hmask pL710) 1 709 (true, (init pL710), (init pL710))) 710 355 false) = true := by
  decide +kernel
theorem L710_ok : RunOK pL710 710 (runFrom pL710 (fmask pL710) (cmask pL710) (hmask pL710) 1 709 (true, (init pL710), (init pL710))) ∧ ptTest pL710 (runFrom pL710 (fmask pL710) (cmask pL710) (hmask pL710) 1 709 (true, (init pL710), (init pL710))) 710 355 false = true :=
  fin_run (runOK_init (prmOK_of_and L710_fin) true) (by decide) rfl L710_fin ptTest_fst
theorem H710_fin : (prmOK pH710 710 && ptTest pH710 (runFrom pH710 (fmask pH710) (cmask pH710) (hmask pH710) 1 709 (true, (init pH710), (init pH710))) 710 355 true) = true := by
  decide +kernel
theorem H710_ok : RunOK pH710 710 (runFrom pH710 (fmask pH710) (cmask pH710) (hmask pH710) 1 709 (true, (init pH710), (init pH710))) ∧ ptTest pH710 (runFrom pH710 (fmask pH710) (cmask pH710) (hmask pH710) 1 709 (true, (init pH710), (init pH710))) 710 355 true = true :=
  fin_run (runOK_init (prmOK_of_and H710_fin) true) (by decide) rfl H710_fin ptTest_fst
theorem I710_fin : (prmOK pI710 710 && intTest pI710 (runFrom pI710 (fmask pI710) (cmask pI710) (hmask pI710) 1 709 (true, (init pI710), (init pI710))) 710 16 true) = true := by
  decide +kernel
theorem I710_ok : RunOK pI710 710 (runFrom pI710 (fmask pI710) (cmask pI710) (hmask pI710) 1 709 (true, (init pI710), (init pI710))) ∧ intTest pI710 (runFrom pI710 (fmask pI710) (cmask pI710) (hmask pI710) 1 709 (true, (init pI710), (init pI710))) 710 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I710_fin) true) (by decide) rfl I710_fin intTest_fst
theorem link710 : linkOK pL710 pH710 pI710 = true := by decide +kernel
theorem cvx710 : ConvexBetweenHumps 710 :=
  cvx_of L710_ok H710_ok I710_ok link710 (by decide)
theorem cenlink710 : cenLinkOK pI710 710 = true := by decide +kernel
theorem cen710 : CenterUniqueMin 710 ∧ DipHyp 710 ∧ OnePointHyps 710 :=
  cen_of L710_ok H710_ok I710_ok link710 cenlink710

/-! ### `N = 711` -/

def pL711 : Prm := ⟨73, 35, 35, 713, 11, 18446744073709551616, 226006327774504689, 226006327774504689⟩
def pH711 : Prm := ⟨73, 35, 35, 713, 11, 18446744073709551616, 226010725821015793, 226010725821015793⟩
def pI711 : Prm := ⟨62, 31, 28, 713, 11, 18446744073709551616, 226006327774504689, 226010725821015793⟩
theorem L711_fin : (prmOK pL711 711 && ptTest pL711 (runFrom pL711 (fmask pL711) (cmask pL711) (hmask pL711) 1 710 (true, (init pL711), (init pL711))) 711 356 false) = true := by
  decide +kernel
theorem L711_ok : RunOK pL711 711 (runFrom pL711 (fmask pL711) (cmask pL711) (hmask pL711) 1 710 (true, (init pL711), (init pL711))) ∧ ptTest pL711 (runFrom pL711 (fmask pL711) (cmask pL711) (hmask pL711) 1 710 (true, (init pL711), (init pL711))) 711 356 false = true :=
  fin_run (runOK_init (prmOK_of_and L711_fin) true) (by decide) rfl L711_fin ptTest_fst
theorem H711_fin : (prmOK pH711 711 && ptTest pH711 (runFrom pH711 (fmask pH711) (cmask pH711) (hmask pH711) 1 710 (true, (init pH711), (init pH711))) 711 356 true) = true := by
  decide +kernel
theorem H711_ok : RunOK pH711 711 (runFrom pH711 (fmask pH711) (cmask pH711) (hmask pH711) 1 710 (true, (init pH711), (init pH711))) ∧ ptTest pH711 (runFrom pH711 (fmask pH711) (cmask pH711) (hmask pH711) 1 710 (true, (init pH711), (init pH711))) 711 356 true = true :=
  fin_run (runOK_init (prmOK_of_and H711_fin) true) (by decide) rfl H711_fin ptTest_fst
theorem I711_fin : (prmOK pI711 711 && intTest pI711 (runFrom pI711 (fmask pI711) (cmask pI711) (hmask pI711) 1 710 (true, (init pI711), (init pI711))) 711 16 false) = true := by
  decide +kernel
theorem I711_ok : RunOK pI711 711 (runFrom pI711 (fmask pI711) (cmask pI711) (hmask pI711) 1 710 (true, (init pI711), (init pI711))) ∧ intTest pI711 (runFrom pI711 (fmask pI711) (cmask pI711) (hmask pI711) 1 710 (true, (init pI711), (init pI711))) 711 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I711_fin) true) (by decide) rfl I711_fin intTest_fst
theorem link711 : linkOK pL711 pH711 pI711 = true := by decide +kernel
theorem cvx711 : ConvexBetweenHumps 711 :=
  cvx_of L711_ok H711_ok I711_ok link711 (by decide)

/-! ### `N = 712` -/

def pL712 : Prm := ⟨73, 35, 35, 714, 11, 18446744073709551616, 225757692271642694, 225757692271642694⟩
def pH712 : Prm := ⟨73, 35, 35, 714, 11, 18446744073709551616, 225762090318153798, 225762090318153798⟩
def pI712 : Prm := ⟨62, 31, 28, 714, 11, 18446744073709551616, 225757692271642694, 225762090318153798⟩
theorem L712_fin : (prmOK pL712 712 && ptTest pL712 (runFrom pL712 (fmask pL712) (cmask pL712) (hmask pL712) 1 711 (true, (init pL712), (init pL712))) 712 356 false) = true := by
  decide +kernel
theorem L712_ok : RunOK pL712 712 (runFrom pL712 (fmask pL712) (cmask pL712) (hmask pL712) 1 711 (true, (init pL712), (init pL712))) ∧ ptTest pL712 (runFrom pL712 (fmask pL712) (cmask pL712) (hmask pL712) 1 711 (true, (init pL712), (init pL712))) 712 356 false = true :=
  fin_run (runOK_init (prmOK_of_and L712_fin) true) (by decide) rfl L712_fin ptTest_fst
theorem H712_fin : (prmOK pH712 712 && ptTest pH712 (runFrom pH712 (fmask pH712) (cmask pH712) (hmask pH712) 1 711 (true, (init pH712), (init pH712))) 712 356 true) = true := by
  decide +kernel
theorem H712_ok : RunOK pH712 712 (runFrom pH712 (fmask pH712) (cmask pH712) (hmask pH712) 1 711 (true, (init pH712), (init pH712))) ∧ ptTest pH712 (runFrom pH712 (fmask pH712) (cmask pH712) (hmask pH712) 1 711 (true, (init pH712), (init pH712))) 712 356 true = true :=
  fin_run (runOK_init (prmOK_of_and H712_fin) true) (by decide) rfl H712_fin ptTest_fst
theorem I712_fin : (prmOK pI712 712 && intTest pI712 (runFrom pI712 (fmask pI712) (cmask pI712) (hmask pI712) 1 711 (true, (init pI712), (init pI712))) 712 16 true) = true := by
  decide +kernel
theorem I712_ok : RunOK pI712 712 (runFrom pI712 (fmask pI712) (cmask pI712) (hmask pI712) 1 711 (true, (init pI712), (init pI712))) ∧ intTest pI712 (runFrom pI712 (fmask pI712) (cmask pI712) (hmask pI712) 1 711 (true, (init pI712), (init pI712))) 712 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I712_fin) true) (by decide) rfl I712_fin intTest_fst
theorem link712 : linkOK pL712 pH712 pI712 = true := by decide +kernel
theorem cvx712 : ConvexBetweenHumps 712 :=
  cvx_of L712_ok H712_ok I712_ok link712 (by decide)
theorem cenlink712 : cenLinkOK pI712 712 = true := by decide +kernel
theorem cen712 : CenterUniqueMin 712 ∧ DipHyp 712 ∧ OnePointHyps 712 :=
  cen_of L712_ok H712_ok I712_ok link712 cenlink712

/-! ### `N = 713` -/

def pL713 : Prm := ⟨73, 35, 35, 715, 11, 18446744073709551616, 225509332595824391, 225509332595824391⟩
def pH713 : Prm := ⟨73, 35, 35, 715, 11, 18446744073709551616, 225513730642335495, 225513730642335495⟩
def pI713 : Prm := ⟨62, 31, 28, 715, 11, 18446744073709551616, 225509332595824391, 225513730642335495⟩
theorem L713_fin : (prmOK pL713 713 && ptTest pL713 (runFrom pL713 (fmask pL713) (cmask pL713) (hmask pL713) 1 712 (true, (init pL713), (init pL713))) 713 357 false) = true := by
  decide +kernel
theorem L713_ok : RunOK pL713 713 (runFrom pL713 (fmask pL713) (cmask pL713) (hmask pL713) 1 712 (true, (init pL713), (init pL713))) ∧ ptTest pL713 (runFrom pL713 (fmask pL713) (cmask pL713) (hmask pL713) 1 712 (true, (init pL713), (init pL713))) 713 357 false = true :=
  fin_run (runOK_init (prmOK_of_and L713_fin) true) (by decide) rfl L713_fin ptTest_fst
theorem H713_fin : (prmOK pH713 713 && ptTest pH713 (runFrom pH713 (fmask pH713) (cmask pH713) (hmask pH713) 1 712 (true, (init pH713), (init pH713))) 713 357 true) = true := by
  decide +kernel
theorem H713_ok : RunOK pH713 713 (runFrom pH713 (fmask pH713) (cmask pH713) (hmask pH713) 1 712 (true, (init pH713), (init pH713))) ∧ ptTest pH713 (runFrom pH713 (fmask pH713) (cmask pH713) (hmask pH713) 1 712 (true, (init pH713), (init pH713))) 713 357 true = true :=
  fin_run (runOK_init (prmOK_of_and H713_fin) true) (by decide) rfl H713_fin ptTest_fst
theorem I713_fin : (prmOK pI713 713 && intTest pI713 (runFrom pI713 (fmask pI713) (cmask pI713) (hmask pI713) 1 712 (true, (init pI713), (init pI713))) 713 16 false) = true := by
  decide +kernel
theorem I713_ok : RunOK pI713 713 (runFrom pI713 (fmask pI713) (cmask pI713) (hmask pI713) 1 712 (true, (init pI713), (init pI713))) ∧ intTest pI713 (runFrom pI713 (fmask pI713) (cmask pI713) (hmask pI713) 1 712 (true, (init pI713), (init pI713))) 713 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I713_fin) true) (by decide) rfl I713_fin intTest_fst
theorem link713 : linkOK pL713 pH713 pI713 = true := by decide +kernel
theorem cvx713 : ConvexBetweenHumps 713 :=
  cvx_of L713_ok H713_ok I713_ok link713 (by decide)

/-! ### `N = 714` -/

def pL714 : Prm := ⟨73, 35, 35, 716, 11, 18446744073709551616, 225261897561503256, 225261897561503256⟩
def pH714 : Prm := ⟨73, 35, 35, 716, 11, 18446744073709551616, 225266295608014360, 225266295608014360⟩
def pI714 : Prm := ⟨62, 31, 28, 716, 11, 18446744073709551616, 225261897561503256, 225266295608014360⟩
theorem L714_fin : (prmOK pL714 714 && ptTest pL714 (runFrom pL714 (fmask pL714) (cmask pL714) (hmask pL714) 1 713 (true, (init pL714), (init pL714))) 714 357 false) = true := by
  decide +kernel
theorem L714_ok : RunOK pL714 714 (runFrom pL714 (fmask pL714) (cmask pL714) (hmask pL714) 1 713 (true, (init pL714), (init pL714))) ∧ ptTest pL714 (runFrom pL714 (fmask pL714) (cmask pL714) (hmask pL714) 1 713 (true, (init pL714), (init pL714))) 714 357 false = true :=
  fin_run (runOK_init (prmOK_of_and L714_fin) true) (by decide) rfl L714_fin ptTest_fst
theorem H714_fin : (prmOK pH714 714 && ptTest pH714 (runFrom pH714 (fmask pH714) (cmask pH714) (hmask pH714) 1 713 (true, (init pH714), (init pH714))) 714 357 true) = true := by
  decide +kernel
theorem H714_ok : RunOK pH714 714 (runFrom pH714 (fmask pH714) (cmask pH714) (hmask pH714) 1 713 (true, (init pH714), (init pH714))) ∧ ptTest pH714 (runFrom pH714 (fmask pH714) (cmask pH714) (hmask pH714) 1 713 (true, (init pH714), (init pH714))) 714 357 true = true :=
  fin_run (runOK_init (prmOK_of_and H714_fin) true) (by decide) rfl H714_fin ptTest_fst
theorem I714_fin : (prmOK pI714 714 && intTest pI714 (runFrom pI714 (fmask pI714) (cmask pI714) (hmask pI714) 1 713 (true, (init pI714), (init pI714))) 714 16 true) = true := by
  decide +kernel
theorem I714_ok : RunOK pI714 714 (runFrom pI714 (fmask pI714) (cmask pI714) (hmask pI714) 1 713 (true, (init pI714), (init pI714))) ∧ intTest pI714 (runFrom pI714 (fmask pI714) (cmask pI714) (hmask pI714) 1 713 (true, (init pI714), (init pI714))) 714 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I714_fin) true) (by decide) rfl I714_fin intTest_fst
theorem link714 : linkOK pL714 pH714 pI714 = true := by decide +kernel
theorem cvx714 : ConvexBetweenHumps 714 :=
  cvx_of L714_ok H714_ok I714_ok link714 (by decide)
theorem cenlink714 : cenLinkOK pI714 714 = true := by decide +kernel
theorem cen714 : CenterUniqueMin 714 ∧ DipHyp 714 ∧ OnePointHyps 714 :=
  cen_of L714_ok H714_ok I714_ok link714 cenlink714

/-! ### `N = 715` -/

def pL715 : Prm := ⟨73, 35, 35, 717, 11, 18446744073709551616, 225014736621541588, 225014736621541588⟩
def pH715 : Prm := ⟨73, 35, 35, 717, 11, 18446744073709551616, 225019134668052692, 225019134668052692⟩
def pI715 : Prm := ⟨62, 31, 28, 717, 11, 18446744073709551616, 225014736621541588, 225019134668052692⟩
theorem L715_fin : (prmOK pL715 715 && ptTest pL715 (runFrom pL715 (fmask pL715) (cmask pL715) (hmask pL715) 1 714 (true, (init pL715), (init pL715))) 715 358 false) = true := by
  decide +kernel
theorem L715_ok : RunOK pL715 715 (runFrom pL715 (fmask pL715) (cmask pL715) (hmask pL715) 1 714 (true, (init pL715), (init pL715))) ∧ ptTest pL715 (runFrom pL715 (fmask pL715) (cmask pL715) (hmask pL715) 1 714 (true, (init pL715), (init pL715))) 715 358 false = true :=
  fin_run (runOK_init (prmOK_of_and L715_fin) true) (by decide) rfl L715_fin ptTest_fst
theorem H715_fin : (prmOK pH715 715 && ptTest pH715 (runFrom pH715 (fmask pH715) (cmask pH715) (hmask pH715) 1 714 (true, (init pH715), (init pH715))) 715 358 true) = true := by
  decide +kernel
theorem H715_ok : RunOK pH715 715 (runFrom pH715 (fmask pH715) (cmask pH715) (hmask pH715) 1 714 (true, (init pH715), (init pH715))) ∧ ptTest pH715 (runFrom pH715 (fmask pH715) (cmask pH715) (hmask pH715) 1 714 (true, (init pH715), (init pH715))) 715 358 true = true :=
  fin_run (runOK_init (prmOK_of_and H715_fin) true) (by decide) rfl H715_fin ptTest_fst
theorem I715_fin : (prmOK pI715 715 && intTest pI715 (runFrom pI715 (fmask pI715) (cmask pI715) (hmask pI715) 1 714 (true, (init pI715), (init pI715))) 715 16 false) = true := by
  decide +kernel
theorem I715_ok : RunOK pI715 715 (runFrom pI715 (fmask pI715) (cmask pI715) (hmask pI715) 1 714 (true, (init pI715), (init pI715))) ∧ intTest pI715 (runFrom pI715 (fmask pI715) (cmask pI715) (hmask pI715) 1 714 (true, (init pI715), (init pI715))) 715 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I715_fin) true) (by decide) rfl I715_fin intTest_fst
theorem link715 : linkOK pL715 pH715 pI715 = true := by decide +kernel
theorem cvx715 : ConvexBetweenHumps 715 :=
  cvx_of L715_ok H715_ok I715_ok link715 (by decide)

/-! ### `N = 716` -/

def pL716 : Prm := ⟨73, 35, 35, 718, 11, 18446744073709551616, 224768493062918236, 224768493062918236⟩
def pH716 : Prm := ⟨73, 35, 35, 718, 11, 18446744073709551616, 224772891109429340, 224772891109429340⟩
def pI716 : Prm := ⟨62, 31, 28, 718, 11, 18446744073709551616, 224768493062918236, 224772891109429340⟩
theorem L716_fin : (prmOK pL716 716 && ptTest pL716 (runFrom pL716 (fmask pL716) (cmask pL716) (hmask pL716) 1 715 (true, (init pL716), (init pL716))) 716 358 false) = true := by
  decide +kernel
theorem L716_ok : RunOK pL716 716 (runFrom pL716 (fmask pL716) (cmask pL716) (hmask pL716) 1 715 (true, (init pL716), (init pL716))) ∧ ptTest pL716 (runFrom pL716 (fmask pL716) (cmask pL716) (hmask pL716) 1 715 (true, (init pL716), (init pL716))) 716 358 false = true :=
  fin_run (runOK_init (prmOK_of_and L716_fin) true) (by decide) rfl L716_fin ptTest_fst
theorem H716_fin : (prmOK pH716 716 && ptTest pH716 (runFrom pH716 (fmask pH716) (cmask pH716) (hmask pH716) 1 715 (true, (init pH716), (init pH716))) 716 358 true) = true := by
  decide +kernel
theorem H716_ok : RunOK pH716 716 (runFrom pH716 (fmask pH716) (cmask pH716) (hmask pH716) 1 715 (true, (init pH716), (init pH716))) ∧ ptTest pH716 (runFrom pH716 (fmask pH716) (cmask pH716) (hmask pH716) 1 715 (true, (init pH716), (init pH716))) 716 358 true = true :=
  fin_run (runOK_init (prmOK_of_and H716_fin) true) (by decide) rfl H716_fin ptTest_fst
theorem I716_fin : (prmOK pI716 716 && intTest pI716 (runFrom pI716 (fmask pI716) (cmask pI716) (hmask pI716) 1 715 (true, (init pI716), (init pI716))) 716 16 true) = true := by
  decide +kernel
theorem I716_ok : RunOK pI716 716 (runFrom pI716 (fmask pI716) (cmask pI716) (hmask pI716) 1 715 (true, (init pI716), (init pI716))) ∧ intTest pI716 (runFrom pI716 (fmask pI716) (cmask pI716) (hmask pI716) 1 715 (true, (init pI716), (init pI716))) 716 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I716_fin) true) (by decide) rfl I716_fin intTest_fst
theorem link716 : linkOK pL716 pH716 pI716 = true := by decide +kernel
theorem cvx716 : ConvexBetweenHumps 716 :=
  cvx_of L716_ok H716_ok I716_ok link716 (by decide)
theorem cenlink716 : cenLinkOK pI716 716 = true := by decide +kernel
theorem cen716 : CenterUniqueMin 716 ∧ DipHyp 716 ∧ OnePointHyps 716 :=
  cen_of L716_ok H716_ok I716_ok link716 cenlink716

/-! ### `N = 717` -/

def pL717 : Prm := ⟨73, 35, 35, 719, 11, 18446744073709551616, 224522521880561501, 224522521880561501⟩
def pH717 : Prm := ⟨73, 35, 35, 719, 11, 18446744073709551616, 224526919927072605, 224526919927072605⟩
def pI717 : Prm := ⟨62, 31, 28, 719, 11, 18446744073709551616, 224522521880561501, 224526919927072605⟩
theorem L717_fin : (prmOK pL717 717 && ptTest pL717 (runFrom pL717 (fmask pL717) (cmask pL717) (hmask pL717) 1 716 (true, (init pL717), (init pL717))) 717 359 false) = true := by
  decide +kernel
theorem L717_ok : RunOK pL717 717 (runFrom pL717 (fmask pL717) (cmask pL717) (hmask pL717) 1 716 (true, (init pL717), (init pL717))) ∧ ptTest pL717 (runFrom pL717 (fmask pL717) (cmask pL717) (hmask pL717) 1 716 (true, (init pL717), (init pL717))) 717 359 false = true :=
  fin_run (runOK_init (prmOK_of_and L717_fin) true) (by decide) rfl L717_fin ptTest_fst
theorem H717_fin : (prmOK pH717 717 && ptTest pH717 (runFrom pH717 (fmask pH717) (cmask pH717) (hmask pH717) 1 716 (true, (init pH717), (init pH717))) 717 359 true) = true := by
  decide +kernel
theorem H717_ok : RunOK pH717 717 (runFrom pH717 (fmask pH717) (cmask pH717) (hmask pH717) 1 716 (true, (init pH717), (init pH717))) ∧ ptTest pH717 (runFrom pH717 (fmask pH717) (cmask pH717) (hmask pH717) 1 716 (true, (init pH717), (init pH717))) 717 359 true = true :=
  fin_run (runOK_init (prmOK_of_and H717_fin) true) (by decide) rfl H717_fin ptTest_fst
theorem I717_fin : (prmOK pI717 717 && intTest pI717 (runFrom pI717 (fmask pI717) (cmask pI717) (hmask pI717) 1 716 (true, (init pI717), (init pI717))) 717 16 false) = true := by
  decide +kernel
theorem I717_ok : RunOK pI717 717 (runFrom pI717 (fmask pI717) (cmask pI717) (hmask pI717) 1 716 (true, (init pI717), (init pI717))) ∧ intTest pI717 (runFrom pI717 (fmask pI717) (cmask pI717) (hmask pI717) 1 716 (true, (init pI717), (init pI717))) 717 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I717_fin) true) (by decide) rfl I717_fin intTest_fst
theorem link717 : linkOK pL717 pH717 pI717 = true := by decide +kernel
theorem cvx717 : ConvexBetweenHumps 717 :=
  cvx_of L717_ok H717_ok I717_ok link717 (by decide)

/-! ### `N = 718` -/

def pL718 : Prm := ⟨73, 35, 35, 720, 11, 18446744073709551616, 224277460896288707, 224277460896288707⟩
def pH718 : Prm := ⟨73, 35, 35, 720, 11, 18446744073709551616, 224281858942799811, 224281858942799811⟩
def pI718 : Prm := ⟨62, 31, 28, 720, 11, 18446744073709551616, 224277460896288707, 224281858942799811⟩
theorem L718_fin : (prmOK pL718 718 && ptTest pL718 (runFrom pL718 (fmask pL718) (cmask pL718) (hmask pL718) 1 717 (true, (init pL718), (init pL718))) 718 359 false) = true := by
  decide +kernel
theorem L718_ok : RunOK pL718 718 (runFrom pL718 (fmask pL718) (cmask pL718) (hmask pL718) 1 717 (true, (init pL718), (init pL718))) ∧ ptTest pL718 (runFrom pL718 (fmask pL718) (cmask pL718) (hmask pL718) 1 717 (true, (init pL718), (init pL718))) 718 359 false = true :=
  fin_run (runOK_init (prmOK_of_and L718_fin) true) (by decide) rfl L718_fin ptTest_fst
theorem H718_fin : (prmOK pH718 718 && ptTest pH718 (runFrom pH718 (fmask pH718) (cmask pH718) (hmask pH718) 1 717 (true, (init pH718), (init pH718))) 718 359 true) = true := by
  decide +kernel
theorem H718_ok : RunOK pH718 718 (runFrom pH718 (fmask pH718) (cmask pH718) (hmask pH718) 1 717 (true, (init pH718), (init pH718))) ∧ ptTest pH718 (runFrom pH718 (fmask pH718) (cmask pH718) (hmask pH718) 1 717 (true, (init pH718), (init pH718))) 718 359 true = true :=
  fin_run (runOK_init (prmOK_of_and H718_fin) true) (by decide) rfl H718_fin ptTest_fst
theorem I718_fin : (prmOK pI718 718 && intTest pI718 (runFrom pI718 (fmask pI718) (cmask pI718) (hmask pI718) 1 717 (true, (init pI718), (init pI718))) 718 16 true) = true := by
  decide +kernel
theorem I718_ok : RunOK pI718 718 (runFrom pI718 (fmask pI718) (cmask pI718) (hmask pI718) 1 717 (true, (init pI718), (init pI718))) ∧ intTest pI718 (runFrom pI718 (fmask pI718) (cmask pI718) (hmask pI718) 1 717 (true, (init pI718), (init pI718))) 718 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I718_fin) true) (by decide) rfl I718_fin intTest_fst
theorem link718 : linkOK pL718 pH718 pI718 = true := by decide +kernel
theorem cvx718 : ConvexBetweenHumps 718 :=
  cvx_of L718_ok H718_ok I718_ok link718 (by decide)
theorem cenlink718 : cenLinkOK pI718 718 = true := by decide +kernel
theorem cen718 : CenterUniqueMin 718 ∧ DipHyp 718 ∧ OnePointHyps 718 :=
  cen_of L718_ok H718_ok I718_ok link718 cenlink718

/-! ### `N = 719` -/

def pL719 : Prm := ⟨73, 35, 35, 721, 11, 18446744073709551616, 224032670584504353, 224032670584504353⟩
def pH719 : Prm := ⟨73, 35, 35, 721, 11, 18446744073709551616, 224037068631015457, 224037068631015457⟩
def pI719 : Prm := ⟨62, 31, 28, 721, 11, 18446744073709551616, 224032670584504353, 224037068631015457⟩
theorem L719_fin : (prmOK pL719 719 && ptTest pL719 (runFrom pL719 (fmask pL719) (cmask pL719) (hmask pL719) 1 718 (true, (init pL719), (init pL719))) 719 360 false) = true := by
  decide +kernel
theorem L719_ok : RunOK pL719 719 (runFrom pL719 (fmask pL719) (cmask pL719) (hmask pL719) 1 718 (true, (init pL719), (init pL719))) ∧ ptTest pL719 (runFrom pL719 (fmask pL719) (cmask pL719) (hmask pL719) 1 718 (true, (init pL719), (init pL719))) 719 360 false = true :=
  fin_run (runOK_init (prmOK_of_and L719_fin) true) (by decide) rfl L719_fin ptTest_fst
theorem H719_fin : (prmOK pH719 719 && ptTest pH719 (runFrom pH719 (fmask pH719) (cmask pH719) (hmask pH719) 1 718 (true, (init pH719), (init pH719))) 719 360 true) = true := by
  decide +kernel
theorem H719_ok : RunOK pH719 719 (runFrom pH719 (fmask pH719) (cmask pH719) (hmask pH719) 1 718 (true, (init pH719), (init pH719))) ∧ ptTest pH719 (runFrom pH719 (fmask pH719) (cmask pH719) (hmask pH719) 1 718 (true, (init pH719), (init pH719))) 719 360 true = true :=
  fin_run (runOK_init (prmOK_of_and H719_fin) true) (by decide) rfl H719_fin ptTest_fst
theorem I719_fin : (prmOK pI719 719 && intTest pI719 (runFrom pI719 (fmask pI719) (cmask pI719) (hmask pI719) 1 718 (true, (init pI719), (init pI719))) 719 16 false) = true := by
  decide +kernel
theorem I719_ok : RunOK pI719 719 (runFrom pI719 (fmask pI719) (cmask pI719) (hmask pI719) 1 718 (true, (init pI719), (init pI719))) ∧ intTest pI719 (runFrom pI719 (fmask pI719) (cmask pI719) (hmask pI719) 1 718 (true, (init pI719), (init pI719))) 719 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I719_fin) true) (by decide) rfl I719_fin intTest_fst
theorem link719 : linkOK pL719 pH719 pI719 = true := by decide +kernel
theorem cvx719 : ConvexBetweenHumps 719 :=
  cvx_of L719_ok H719_ok I719_ok link719 (by decide)

/-! ### `N = 720` -/

def pL720 : Prm := ⟨73, 35, 35, 722, 11, 18446744073709551616, 223788783363328788, 223788783363328788⟩
def pH720 : Prm := ⟨73, 35, 35, 722, 11, 18446744073709551616, 223793181409839892, 223793181409839892⟩
def pI720 : Prm := ⟨62, 31, 28, 722, 11, 18446744073709551616, 223788783363328788, 223793181409839892⟩
theorem L720_fin : (prmOK pL720 720 && ptTest pL720 (runFrom pL720 (fmask pL720) (cmask pL720) (hmask pL720) 1 719 (true, (init pL720), (init pL720))) 720 360 false) = true := by
  decide +kernel
theorem L720_ok : RunOK pL720 720 (runFrom pL720 (fmask pL720) (cmask pL720) (hmask pL720) 1 719 (true, (init pL720), (init pL720))) ∧ ptTest pL720 (runFrom pL720 (fmask pL720) (cmask pL720) (hmask pL720) 1 719 (true, (init pL720), (init pL720))) 720 360 false = true :=
  fin_run (runOK_init (prmOK_of_and L720_fin) true) (by decide) rfl L720_fin ptTest_fst
theorem H720_fin : (prmOK pH720 720 && ptTest pH720 (runFrom pH720 (fmask pH720) (cmask pH720) (hmask pH720) 1 719 (true, (init pH720), (init pH720))) 720 360 true) = true := by
  decide +kernel
theorem H720_ok : RunOK pH720 720 (runFrom pH720 (fmask pH720) (cmask pH720) (hmask pH720) 1 719 (true, (init pH720), (init pH720))) ∧ ptTest pH720 (runFrom pH720 (fmask pH720) (cmask pH720) (hmask pH720) 1 719 (true, (init pH720), (init pH720))) 720 360 true = true :=
  fin_run (runOK_init (prmOK_of_and H720_fin) true) (by decide) rfl H720_fin ptTest_fst
theorem I720_fin : (prmOK pI720 720 && intTest pI720 (runFrom pI720 (fmask pI720) (cmask pI720) (hmask pI720) 1 719 (true, (init pI720), (init pI720))) 720 16 true) = true := by
  decide +kernel
theorem I720_ok : RunOK pI720 720 (runFrom pI720 (fmask pI720) (cmask pI720) (hmask pI720) 1 719 (true, (init pI720), (init pI720))) ∧ intTest pI720 (runFrom pI720 (fmask pI720) (cmask pI720) (hmask pI720) 1 719 (true, (init pI720), (init pI720))) 720 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I720_fin) true) (by decide) rfl I720_fin intTest_fst
theorem link720 : linkOK pL720 pH720 pI720 = true := by decide +kernel
theorem cvx720 : ConvexBetweenHumps 720 :=
  cvx_of L720_ok H720_ok I720_ok link720 (by decide)
theorem cenlink720 : cenLinkOK pI720 720 = true := by decide +kernel
theorem cen720 : CenterUniqueMin 720 ∧ DipHyp 720 ∧ OnePointHyps 720 :=
  cen_of L720_ok H720_ok I720_ok link720 cenlink720

/-! ### `N = 721` -/

def pL721 : Prm := ⟨73, 35, 35, 723, 11, 18446744073709551616, 223545165125178162, 223545165125178162⟩
def pH721 : Prm := ⟨73, 35, 35, 723, 11, 18446744073709551616, 223549563171689266, 223549563171689266⟩
def pI721 : Prm := ⟨62, 31, 28, 723, 11, 18446744073709551616, 223545165125178162, 223549563171689266⟩
theorem L721_fin : (prmOK pL721 721 && ptTest pL721 (runFrom pL721 (fmask pL721) (cmask pL721) (hmask pL721) 1 720 (true, (init pL721), (init pL721))) 721 361 false) = true := by
  decide +kernel
theorem L721_ok : RunOK pL721 721 (runFrom pL721 (fmask pL721) (cmask pL721) (hmask pL721) 1 720 (true, (init pL721), (init pL721))) ∧ ptTest pL721 (runFrom pL721 (fmask pL721) (cmask pL721) (hmask pL721) 1 720 (true, (init pL721), (init pL721))) 721 361 false = true :=
  fin_run (runOK_init (prmOK_of_and L721_fin) true) (by decide) rfl L721_fin ptTest_fst
theorem H721_fin : (prmOK pH721 721 && ptTest pH721 (runFrom pH721 (fmask pH721) (cmask pH721) (hmask pH721) 1 720 (true, (init pH721), (init pH721))) 721 361 true) = true := by
  decide +kernel
theorem H721_ok : RunOK pH721 721 (runFrom pH721 (fmask pH721) (cmask pH721) (hmask pH721) 1 720 (true, (init pH721), (init pH721))) ∧ ptTest pH721 (runFrom pH721 (fmask pH721) (cmask pH721) (hmask pH721) 1 720 (true, (init pH721), (init pH721))) 721 361 true = true :=
  fin_run (runOK_init (prmOK_of_and H721_fin) true) (by decide) rfl H721_fin ptTest_fst
theorem I721_fin : (prmOK pI721 721 && intTest pI721 (runFrom pI721 (fmask pI721) (cmask pI721) (hmask pI721) 1 720 (true, (init pI721), (init pI721))) 721 16 false) = true := by
  decide +kernel
theorem I721_ok : RunOK pI721 721 (runFrom pI721 (fmask pI721) (cmask pI721) (hmask pI721) 1 720 (true, (init pI721), (init pI721))) ∧ intTest pI721 (runFrom pI721 (fmask pI721) (cmask pI721) (hmask pI721) 1 720 (true, (init pI721), (init pI721))) 721 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I721_fin) true) (by decide) rfl I721_fin intTest_fst
theorem link721 : linkOK pL721 pH721 pI721 = true := by decide +kernel
theorem cvx721 : ConvexBetweenHumps 721 :=
  cvx_of L721_ok H721_ok I721_ok link721 (by decide)

/-! ### `N = 722` -/

def pL722 : Prm := ⟨73, 35, 35, 724, 11, 18446744073709551616, 223302442944981167, 223302442944981167⟩
def pH722 : Prm := ⟨73, 35, 35, 724, 11, 18446744073709551616, 223306840991492271, 223306840991492271⟩
def pI722 : Prm := ⟨62, 31, 28, 724, 11, 18446744073709551616, 223302442944981167, 223306840991492271⟩
theorem L722_fin : (prmOK pL722 722 && ptTest pL722 (runFrom pL722 (fmask pL722) (cmask pL722) (hmask pL722) 1 721 (true, (init pL722), (init pL722))) 722 361 false) = true := by
  decide +kernel
theorem L722_ok : RunOK pL722 722 (runFrom pL722 (fmask pL722) (cmask pL722) (hmask pL722) 1 721 (true, (init pL722), (init pL722))) ∧ ptTest pL722 (runFrom pL722 (fmask pL722) (cmask pL722) (hmask pL722) 1 721 (true, (init pL722), (init pL722))) 722 361 false = true :=
  fin_run (runOK_init (prmOK_of_and L722_fin) true) (by decide) rfl L722_fin ptTest_fst
theorem H722_fin : (prmOK pH722 722 && ptTest pH722 (runFrom pH722 (fmask pH722) (cmask pH722) (hmask pH722) 1 721 (true, (init pH722), (init pH722))) 722 361 true) = true := by
  decide +kernel
theorem H722_ok : RunOK pH722 722 (runFrom pH722 (fmask pH722) (cmask pH722) (hmask pH722) 1 721 (true, (init pH722), (init pH722))) ∧ ptTest pH722 (runFrom pH722 (fmask pH722) (cmask pH722) (hmask pH722) 1 721 (true, (init pH722), (init pH722))) 722 361 true = true :=
  fin_run (runOK_init (prmOK_of_and H722_fin) true) (by decide) rfl H722_fin ptTest_fst
theorem I722_fin : (prmOK pI722 722 && intTest pI722 (runFrom pI722 (fmask pI722) (cmask pI722) (hmask pI722) 1 721 (true, (init pI722), (init pI722))) 722 16 true) = true := by
  decide +kernel
theorem I722_ok : RunOK pI722 722 (runFrom pI722 (fmask pI722) (cmask pI722) (hmask pI722) 1 721 (true, (init pI722), (init pI722))) ∧ intTest pI722 (runFrom pI722 (fmask pI722) (cmask pI722) (hmask pI722) 1 721 (true, (init pI722), (init pI722))) 722 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I722_fin) true) (by decide) rfl I722_fin intTest_fst
theorem link722 : linkOK pL722 pH722 pI722 = true := by decide +kernel
theorem cvx722 : ConvexBetweenHumps 722 :=
  cvx_of L722_ok H722_ok I722_ok link722 (by decide)
theorem cenlink722 : cenLinkOK pI722 722 = true := by decide +kernel
theorem cen722 : CenterUniqueMin 722 ∧ DipHyp 722 ∧ OnePointHyps 722 :=
  cen_of L722_ok H722_ok I722_ok link722 cenlink722

/-! ### `N = 723` -/

def pL723 : Prm := ⟨73, 35, 35, 725, 11, 18446744073709551616, 223059988072402027, 223059988072402027⟩
def pH723 : Prm := ⟨73, 35, 35, 725, 11, 18446744073709551616, 223064386118913131, 223064386118913131⟩
def pI723 : Prm := ⟨62, 31, 28, 725, 11, 18446744073709551616, 223059988072402027, 223064386118913131⟩
theorem L723_fin : (prmOK pL723 723 && ptTest pL723 (runFrom pL723 (fmask pL723) (cmask pL723) (hmask pL723) 1 722 (true, (init pL723), (init pL723))) 723 362 false) = true := by
  decide +kernel
theorem L723_ok : RunOK pL723 723 (runFrom pL723 (fmask pL723) (cmask pL723) (hmask pL723) 1 722 (true, (init pL723), (init pL723))) ∧ ptTest pL723 (runFrom pL723 (fmask pL723) (cmask pL723) (hmask pL723) 1 722 (true, (init pL723), (init pL723))) 723 362 false = true :=
  fin_run (runOK_init (prmOK_of_and L723_fin) true) (by decide) rfl L723_fin ptTest_fst
theorem H723_fin : (prmOK pH723 723 && ptTest pH723 (runFrom pH723 (fmask pH723) (cmask pH723) (hmask pH723) 1 722 (true, (init pH723), (init pH723))) 723 362 true) = true := by
  decide +kernel
theorem H723_ok : RunOK pH723 723 (runFrom pH723 (fmask pH723) (cmask pH723) (hmask pH723) 1 722 (true, (init pH723), (init pH723))) ∧ ptTest pH723 (runFrom pH723 (fmask pH723) (cmask pH723) (hmask pH723) 1 722 (true, (init pH723), (init pH723))) 723 362 true = true :=
  fin_run (runOK_init (prmOK_of_and H723_fin) true) (by decide) rfl H723_fin ptTest_fst
theorem I723_fin : (prmOK pI723 723 && intTest pI723 (runFrom pI723 (fmask pI723) (cmask pI723) (hmask pI723) 1 722 (true, (init pI723), (init pI723))) 723 16 false) = true := by
  decide +kernel
theorem I723_ok : RunOK pI723 723 (runFrom pI723 (fmask pI723) (cmask pI723) (hmask pI723) 1 722 (true, (init pI723), (init pI723))) ∧ intTest pI723 (runFrom pI723 (fmask pI723) (cmask pI723) (hmask pI723) 1 722 (true, (init pI723), (init pI723))) 723 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I723_fin) true) (by decide) rfl I723_fin intTest_fst
theorem link723 : linkOK pL723 pH723 pI723 = true := by decide +kernel
theorem cvx723 : ConvexBetweenHumps 723 :=
  cvx_of L723_ok H723_ok I723_ok link723 (by decide)

/-! ### `N = 724` -/

def pL724 : Prm := ⟨73, 35, 35, 726, 11, 18446744073709551616, 222818422298926784, 222818422298926784⟩
def pH724 : Prm := ⟨73, 35, 35, 726, 11, 18446744073709551616, 222822820345437888, 222822820345437888⟩
def pI724 : Prm := ⟨62, 31, 28, 726, 11, 18446744073709551616, 222818422298926784, 222822820345437888⟩
theorem L724_fin : (prmOK pL724 724 && ptTest pL724 (runFrom pL724 (fmask pL724) (cmask pL724) (hmask pL724) 1 723 (true, (init pL724), (init pL724))) 724 362 false) = true := by
  decide +kernel
theorem L724_ok : RunOK pL724 724 (runFrom pL724 (fmask pL724) (cmask pL724) (hmask pL724) 1 723 (true, (init pL724), (init pL724))) ∧ ptTest pL724 (runFrom pL724 (fmask pL724) (cmask pL724) (hmask pL724) 1 723 (true, (init pL724), (init pL724))) 724 362 false = true :=
  fin_run (runOK_init (prmOK_of_and L724_fin) true) (by decide) rfl L724_fin ptTest_fst
theorem H724_fin : (prmOK pH724 724 && ptTest pH724 (runFrom pH724 (fmask pH724) (cmask pH724) (hmask pH724) 1 723 (true, (init pH724), (init pH724))) 724 362 true) = true := by
  decide +kernel
theorem H724_ok : RunOK pH724 724 (runFrom pH724 (fmask pH724) (cmask pH724) (hmask pH724) 1 723 (true, (init pH724), (init pH724))) ∧ ptTest pH724 (runFrom pH724 (fmask pH724) (cmask pH724) (hmask pH724) 1 723 (true, (init pH724), (init pH724))) 724 362 true = true :=
  fin_run (runOK_init (prmOK_of_and H724_fin) true) (by decide) rfl H724_fin ptTest_fst
theorem I724_fin : (prmOK pI724 724 && intTest pI724 (runFrom pI724 (fmask pI724) (cmask pI724) (hmask pI724) 1 723 (true, (init pI724), (init pI724))) 724 16 true) = true := by
  decide +kernel
theorem I724_ok : RunOK pI724 724 (runFrom pI724 (fmask pI724) (cmask pI724) (hmask pI724) 1 723 (true, (init pI724), (init pI724))) ∧ intTest pI724 (runFrom pI724 (fmask pI724) (cmask pI724) (hmask pI724) 1 723 (true, (init pI724), (init pI724))) 724 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I724_fin) true) (by decide) rfl I724_fin intTest_fst
theorem link724 : linkOK pL724 pH724 pI724 = true := by decide +kernel
theorem cvx724 : ConvexBetweenHumps 724 :=
  cvx_of L724_ok H724_ok I724_ok link724 (by decide)
theorem cenlink724 : cenLinkOK pI724 724 = true := by decide +kernel
theorem cen724 : CenterUniqueMin 724 ∧ DipHyp 724 ∧ OnePointHyps 724 :=
  cen_of L724_ok H724_ok I724_ok link724 cenlink724

/-! ### `N = 725` -/

def pL725 : Prm := ⟨74, 36, 35, 727, 11, 18446744073709551616, 222577122171626497, 222577122171626497⟩
def pH725 : Prm := ⟨73, 35, 35, 727, 11, 18446744073709551616, 222581520218137601, 222581520218137601⟩
def pI725 : Prm := ⟨62, 31, 28, 727, 11, 18446744073709551616, 222577122171626497, 222581520218137601⟩
theorem L725_fin : (prmOK pL725 725 && ptTest pL725 (runFrom pL725 (fmask pL725) (cmask pL725) (hmask pL725) 1 724 (true, (init pL725), (init pL725))) 725 363 false) = true := by
  decide +kernel
theorem L725_ok : RunOK pL725 725 (runFrom pL725 (fmask pL725) (cmask pL725) (hmask pL725) 1 724 (true, (init pL725), (init pL725))) ∧ ptTest pL725 (runFrom pL725 (fmask pL725) (cmask pL725) (hmask pL725) 1 724 (true, (init pL725), (init pL725))) 725 363 false = true :=
  fin_run (runOK_init (prmOK_of_and L725_fin) true) (by decide) rfl L725_fin ptTest_fst
theorem H725_fin : (prmOK pH725 725 && ptTest pH725 (runFrom pH725 (fmask pH725) (cmask pH725) (hmask pH725) 1 724 (true, (init pH725), (init pH725))) 725 363 true) = true := by
  decide +kernel
theorem H725_ok : RunOK pH725 725 (runFrom pH725 (fmask pH725) (cmask pH725) (hmask pH725) 1 724 (true, (init pH725), (init pH725))) ∧ ptTest pH725 (runFrom pH725 (fmask pH725) (cmask pH725) (hmask pH725) 1 724 (true, (init pH725), (init pH725))) 725 363 true = true :=
  fin_run (runOK_init (prmOK_of_and H725_fin) true) (by decide) rfl H725_fin ptTest_fst
theorem I725_fin : (prmOK pI725 725 && intTest pI725 (runFrom pI725 (fmask pI725) (cmask pI725) (hmask pI725) 1 724 (true, (init pI725), (init pI725))) 725 16 false) = true := by
  decide +kernel
theorem I725_ok : RunOK pI725 725 (runFrom pI725 (fmask pI725) (cmask pI725) (hmask pI725) 1 724 (true, (init pI725), (init pI725))) ∧ intTest pI725 (runFrom pI725 (fmask pI725) (cmask pI725) (hmask pI725) 1 724 (true, (init pI725), (init pI725))) 725 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I725_fin) true) (by decide) rfl I725_fin intTest_fst
theorem link725 : linkOK pL725 pH725 pI725 = true := by decide +kernel
theorem cvx725 : ConvexBetweenHumps 725 :=
  cvx_of L725_ok H725_ok I725_ok link725 (by decide)

/-! ### `N = 726` -/

def pL726 : Prm := ⟨73, 35, 35, 728, 11, 18446744073709551616, 222336704257463458, 222336704257463458⟩
def pH726 : Prm := ⟨73, 35, 35, 728, 11, 18446744073709551616, 222341102303974562, 222341102303974562⟩
def pI726 : Prm := ⟨62, 31, 28, 728, 11, 18446744073709551616, 222336704257463458, 222341102303974562⟩
theorem L726_fin : (prmOK pL726 726 && ptTest pL726 (runFrom pL726 (fmask pL726) (cmask pL726) (hmask pL726) 1 725 (true, (init pL726), (init pL726))) 726 363 false) = true := by
  decide +kernel
theorem L726_ok : RunOK pL726 726 (runFrom pL726 (fmask pL726) (cmask pL726) (hmask pL726) 1 725 (true, (init pL726), (init pL726))) ∧ ptTest pL726 (runFrom pL726 (fmask pL726) (cmask pL726) (hmask pL726) 1 725 (true, (init pL726), (init pL726))) 726 363 false = true :=
  fin_run (runOK_init (prmOK_of_and L726_fin) true) (by decide) rfl L726_fin ptTest_fst
theorem H726_fin : (prmOK pH726 726 && ptTest pH726 (runFrom pH726 (fmask pH726) (cmask pH726) (hmask pH726) 1 725 (true, (init pH726), (init pH726))) 726 363 true) = true := by
  decide +kernel
theorem H726_ok : RunOK pH726 726 (runFrom pH726 (fmask pH726) (cmask pH726) (hmask pH726) 1 725 (true, (init pH726), (init pH726))) ∧ ptTest pH726 (runFrom pH726 (fmask pH726) (cmask pH726) (hmask pH726) 1 725 (true, (init pH726), (init pH726))) 726 363 true = true :=
  fin_run (runOK_init (prmOK_of_and H726_fin) true) (by decide) rfl H726_fin ptTest_fst
theorem I726_fin : (prmOK pI726 726 && intTest pI726 (runFrom pI726 (fmask pI726) (cmask pI726) (hmask pI726) 1 725 (true, (init pI726), (init pI726))) 726 16 true) = true := by
  decide +kernel
theorem I726_ok : RunOK pI726 726 (runFrom pI726 (fmask pI726) (cmask pI726) (hmask pI726) 1 725 (true, (init pI726), (init pI726))) ∧ intTest pI726 (runFrom pI726 (fmask pI726) (cmask pI726) (hmask pI726) 1 725 (true, (init pI726), (init pI726))) 726 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I726_fin) true) (by decide) rfl I726_fin intTest_fst
theorem link726 : linkOK pL726 pH726 pI726 = true := by decide +kernel
theorem cvx726 : ConvexBetweenHumps 726 :=
  cvx_of L726_ok H726_ok I726_ok link726 (by decide)
theorem cenlink726 : cenLinkOK pI726 726 = true := by decide +kernel
theorem cen726 : CenterUniqueMin 726 ∧ DipHyp 726 ∧ OnePointHyps 726 :=
  cen_of L726_ok H726_ok I726_ok link726 cenlink726

/-! ### `N = 727` -/

def pL727 : Prm := ⟨73, 35, 35, 729, 11, 18446744073709551616, 222096550341793748, 222096550341793748⟩
def pH727 : Prm := ⟨74, 36, 35, 729, 11, 18446744073709551616, 222100948388304852, 222100948388304852⟩
def pI727 : Prm := ⟨62, 31, 28, 729, 11, 18446744073709551616, 222096550341793748, 222100948388304852⟩
theorem L727_fin : (prmOK pL727 727 && ptTest pL727 (runFrom pL727 (fmask pL727) (cmask pL727) (hmask pL727) 1 726 (true, (init pL727), (init pL727))) 727 364 false) = true := by
  decide +kernel
theorem L727_ok : RunOK pL727 727 (runFrom pL727 (fmask pL727) (cmask pL727) (hmask pL727) 1 726 (true, (init pL727), (init pL727))) ∧ ptTest pL727 (runFrom pL727 (fmask pL727) (cmask pL727) (hmask pL727) 1 726 (true, (init pL727), (init pL727))) 727 364 false = true :=
  fin_run (runOK_init (prmOK_of_and L727_fin) true) (by decide) rfl L727_fin ptTest_fst
theorem H727_fin : (prmOK pH727 727 && ptTest pH727 (runFrom pH727 (fmask pH727) (cmask pH727) (hmask pH727) 1 726 (true, (init pH727), (init pH727))) 727 364 true) = true := by
  decide +kernel
theorem H727_ok : RunOK pH727 727 (runFrom pH727 (fmask pH727) (cmask pH727) (hmask pH727) 1 726 (true, (init pH727), (init pH727))) ∧ ptTest pH727 (runFrom pH727 (fmask pH727) (cmask pH727) (hmask pH727) 1 726 (true, (init pH727), (init pH727))) 727 364 true = true :=
  fin_run (runOK_init (prmOK_of_and H727_fin) true) (by decide) rfl H727_fin ptTest_fst
theorem I727_fin : (prmOK pI727 727 && intTest pI727 (runFrom pI727 (fmask pI727) (cmask pI727) (hmask pI727) 1 726 (true, (init pI727), (init pI727))) 727 16 false) = true := by
  decide +kernel
theorem I727_ok : RunOK pI727 727 (runFrom pI727 (fmask pI727) (cmask pI727) (hmask pI727) 1 726 (true, (init pI727), (init pI727))) ∧ intTest pI727 (runFrom pI727 (fmask pI727) (cmask pI727) (hmask pI727) 1 726 (true, (init pI727), (init pI727))) 727 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I727_fin) true) (by decide) rfl I727_fin intTest_fst
theorem link727 : linkOK pL727 pH727 pI727 = true := by decide +kernel
theorem cvx727 : ConvexBetweenHumps 727 :=
  cvx_of L727_ok H727_ok I727_ok link727 (by decide)

/-! ### `N = 728` -/

def pL728 : Prm := ⟨73, 35, 35, 730, 11, 18446744073709551616, 221857271825181600, 221857271825181600⟩
def pH728 : Prm := ⟨73, 35, 35, 730, 11, 18446744073709551616, 221861669871692704, 221861669871692704⟩
def pI728 : Prm := ⟨62, 31, 28, 730, 11, 18446744073709551616, 221857271825181600, 221861669871692704⟩
theorem L728_fin : (prmOK pL728 728 && ptTest pL728 (runFrom pL728 (fmask pL728) (cmask pL728) (hmask pL728) 1 727 (true, (init pL728), (init pL728))) 728 364 false) = true := by
  decide +kernel
theorem L728_ok : RunOK pL728 728 (runFrom pL728 (fmask pL728) (cmask pL728) (hmask pL728) 1 727 (true, (init pL728), (init pL728))) ∧ ptTest pL728 (runFrom pL728 (fmask pL728) (cmask pL728) (hmask pL728) 1 727 (true, (init pL728), (init pL728))) 728 364 false = true :=
  fin_run (runOK_init (prmOK_of_and L728_fin) true) (by decide) rfl L728_fin ptTest_fst
theorem H728_fin : (prmOK pH728 728 && ptTest pH728 (runFrom pH728 (fmask pH728) (cmask pH728) (hmask pH728) 1 727 (true, (init pH728), (init pH728))) 728 364 true) = true := by
  decide +kernel
theorem H728_ok : RunOK pH728 728 (runFrom pH728 (fmask pH728) (cmask pH728) (hmask pH728) 1 727 (true, (init pH728), (init pH728))) ∧ ptTest pH728 (runFrom pH728 (fmask pH728) (cmask pH728) (hmask pH728) 1 727 (true, (init pH728), (init pH728))) 728 364 true = true :=
  fin_run (runOK_init (prmOK_of_and H728_fin) true) (by decide) rfl H728_fin ptTest_fst
theorem I728_fin : (prmOK pI728 728 && intTest pI728 (runFrom pI728 (fmask pI728) (cmask pI728) (hmask pI728) 1 727 (true, (init pI728), (init pI728))) 728 16 true) = true := by
  decide +kernel
theorem I728_ok : RunOK pI728 728 (runFrom pI728 (fmask pI728) (cmask pI728) (hmask pI728) 1 727 (true, (init pI728), (init pI728))) ∧ intTest pI728 (runFrom pI728 (fmask pI728) (cmask pI728) (hmask pI728) 1 727 (true, (init pI728), (init pI728))) 728 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I728_fin) true) (by decide) rfl I728_fin intTest_fst
theorem link728 : linkOK pL728 pH728 pI728 = true := by decide +kernel
theorem cvx728 : ConvexBetweenHumps 728 :=
  cvx_of L728_ok H728_ok I728_ok link728 (by decide)
theorem cenlink728 : cenLinkOK pI728 728 = true := by decide +kernel
theorem cen728 : CenterUniqueMin 728 ∧ DipHyp 728 ∧ OnePointHyps 728 :=
  cen_of L728_ok H728_ok I728_ok link728 cenlink728

/-! ### `N = 729` -/

def pL729 : Prm := ⟨74, 36, 35, 731, 11, 18446744073709551616, 221618255673068637, 221618255673068637⟩
def pH729 : Prm := ⟨73, 35, 35, 731, 11, 18446744073709551616, 221622653719579741, 221622653719579741⟩
def pI729 : Prm := ⟨62, 31, 28, 731, 11, 18446744073709551616, 221618255673068637, 221622653719579741⟩
theorem L729_fin : (prmOK pL729 729 && ptTest pL729 (runFrom pL729 (fmask pL729) (cmask pL729) (hmask pL729) 1 728 (true, (init pL729), (init pL729))) 729 365 false) = true := by
  decide +kernel
theorem L729_ok : RunOK pL729 729 (runFrom pL729 (fmask pL729) (cmask pL729) (hmask pL729) 1 728 (true, (init pL729), (init pL729))) ∧ ptTest pL729 (runFrom pL729 (fmask pL729) (cmask pL729) (hmask pL729) 1 728 (true, (init pL729), (init pL729))) 729 365 false = true :=
  fin_run (runOK_init (prmOK_of_and L729_fin) true) (by decide) rfl L729_fin ptTest_fst
theorem H729_fin : (prmOK pH729 729 && ptTest pH729 (runFrom pH729 (fmask pH729) (cmask pH729) (hmask pH729) 1 728 (true, (init pH729), (init pH729))) 729 365 true) = true := by
  decide +kernel
theorem H729_ok : RunOK pH729 729 (runFrom pH729 (fmask pH729) (cmask pH729) (hmask pH729) 1 728 (true, (init pH729), (init pH729))) ∧ ptTest pH729 (runFrom pH729 (fmask pH729) (cmask pH729) (hmask pH729) 1 728 (true, (init pH729), (init pH729))) 729 365 true = true :=
  fin_run (runOK_init (prmOK_of_and H729_fin) true) (by decide) rfl H729_fin ptTest_fst
theorem I729_fin : (prmOK pI729 729 && intTest pI729 (runFrom pI729 (fmask pI729) (cmask pI729) (hmask pI729) 1 728 (true, (init pI729), (init pI729))) 729 16 false) = true := by
  decide +kernel
theorem I729_ok : RunOK pI729 729 (runFrom pI729 (fmask pI729) (cmask pI729) (hmask pI729) 1 728 (true, (init pI729), (init pI729))) ∧ intTest pI729 (runFrom pI729 (fmask pI729) (cmask pI729) (hmask pI729) 1 728 (true, (init pI729), (init pI729))) 729 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I729_fin) true) (by decide) rfl I729_fin intTest_fst
theorem link729 : linkOK pL729 pH729 pI729 = true := by decide +kernel
theorem cvx729 : ConvexBetweenHumps 729 :=
  cvx_of L729_ok H729_ok I729_ok link729 (by decide)

/-! ### `N = 730` -/

def pL730 : Prm := ⟨74, 36, 35, 732, 11, 18446744073709551616, 221380108176898173, 221380108176898173⟩
def pH730 : Prm := ⟨74, 36, 35, 732, 11, 18446744073709551616, 221384506223409277, 221384506223409277⟩
def pI730 : Prm := ⟨62, 31, 28, 732, 11, 18446744073709551616, 221380108176898173, 221384506223409277⟩
theorem L730_fin : (prmOK pL730 730 && ptTest pL730 (runFrom pL730 (fmask pL730) (cmask pL730) (hmask pL730) 1 729 (true, (init pL730), (init pL730))) 730 365 false) = true := by
  decide +kernel
theorem L730_ok : RunOK pL730 730 (runFrom pL730 (fmask pL730) (cmask pL730) (hmask pL730) 1 729 (true, (init pL730), (init pL730))) ∧ ptTest pL730 (runFrom pL730 (fmask pL730) (cmask pL730) (hmask pL730) 1 729 (true, (init pL730), (init pL730))) 730 365 false = true :=
  fin_run (runOK_init (prmOK_of_and L730_fin) true) (by decide) rfl L730_fin ptTest_fst
theorem H730_fin : (prmOK pH730 730 && ptTest pH730 (runFrom pH730 (fmask pH730) (cmask pH730) (hmask pH730) 1 729 (true, (init pH730), (init pH730))) 730 365 true) = true := by
  decide +kernel
theorem H730_ok : RunOK pH730 730 (runFrom pH730 (fmask pH730) (cmask pH730) (hmask pH730) 1 729 (true, (init pH730), (init pH730))) ∧ ptTest pH730 (runFrom pH730 (fmask pH730) (cmask pH730) (hmask pH730) 1 729 (true, (init pH730), (init pH730))) 730 365 true = true :=
  fin_run (runOK_init (prmOK_of_and H730_fin) true) (by decide) rfl H730_fin ptTest_fst
theorem I730_fin : (prmOK pI730 730 && intTest pI730 (runFrom pI730 (fmask pI730) (cmask pI730) (hmask pI730) 1 729 (true, (init pI730), (init pI730))) 730 16 true) = true := by
  decide +kernel
theorem I730_ok : RunOK pI730 730 (runFrom pI730 (fmask pI730) (cmask pI730) (hmask pI730) 1 729 (true, (init pI730), (init pI730))) ∧ intTest pI730 (runFrom pI730 (fmask pI730) (cmask pI730) (hmask pI730) 1 729 (true, (init pI730), (init pI730))) 730 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I730_fin) true) (by decide) rfl I730_fin intTest_fst
theorem link730 : linkOK pL730 pH730 pI730 = true := by decide +kernel
theorem cvx730 : ConvexBetweenHumps 730 :=
  cvx_of L730_ok H730_ok I730_ok link730 (by decide)
theorem cenlink730 : cenLinkOK pI730 730 = true := by decide +kernel
theorem cen730 : CenterUniqueMin 730 ∧ DipHyp 730 ∧ OnePointHyps 730 :=
  cen_of L730_ok H730_ok I730_ok link730 cenlink730

/-! ### `N = 731` -/

def pL731 : Prm := ⟨73, 35, 35, 733, 11, 18446744073709551616, 221142221424735769, 221142221424735769⟩
def pH731 : Prm := ⟨74, 36, 35, 733, 11, 18446744073709551616, 221146619471246873, 221146619471246873⟩
def pI731 : Prm := ⟨62, 31, 28, 733, 11, 18446744073709551616, 221142221424735769, 221146619471246873⟩
theorem L731_fin : (prmOK pL731 731 && ptTest pL731 (runFrom pL731 (fmask pL731) (cmask pL731) (hmask pL731) 1 730 (true, (init pL731), (init pL731))) 731 366 false) = true := by
  decide +kernel
theorem L731_ok : RunOK pL731 731 (runFrom pL731 (fmask pL731) (cmask pL731) (hmask pL731) 1 730 (true, (init pL731), (init pL731))) ∧ ptTest pL731 (runFrom pL731 (fmask pL731) (cmask pL731) (hmask pL731) 1 730 (true, (init pL731), (init pL731))) 731 366 false = true :=
  fin_run (runOK_init (prmOK_of_and L731_fin) true) (by decide) rfl L731_fin ptTest_fst
theorem H731_fin : (prmOK pH731 731 && ptTest pH731 (runFrom pH731 (fmask pH731) (cmask pH731) (hmask pH731) 1 730 (true, (init pH731), (init pH731))) 731 366 true) = true := by
  decide +kernel
theorem H731_ok : RunOK pH731 731 (runFrom pH731 (fmask pH731) (cmask pH731) (hmask pH731) 1 730 (true, (init pH731), (init pH731))) ∧ ptTest pH731 (runFrom pH731 (fmask pH731) (cmask pH731) (hmask pH731) 1 730 (true, (init pH731), (init pH731))) 731 366 true = true :=
  fin_run (runOK_init (prmOK_of_and H731_fin) true) (by decide) rfl H731_fin ptTest_fst
theorem I731_fin : (prmOK pI731 731 && intTest pI731 (runFrom pI731 (fmask pI731) (cmask pI731) (hmask pI731) 1 730 (true, (init pI731), (init pI731))) 731 16 false) = true := by
  decide +kernel
theorem I731_ok : RunOK pI731 731 (runFrom pI731 (fmask pI731) (cmask pI731) (hmask pI731) 1 730 (true, (init pI731), (init pI731))) ∧ intTest pI731 (runFrom pI731 (fmask pI731) (cmask pI731) (hmask pI731) 1 730 (true, (init pI731), (init pI731))) 731 16 false = true :=
  fin_run (runOK_init (prmOK_of_and I731_fin) true) (by decide) rfl I731_fin intTest_fst
theorem link731 : linkOK pL731 pH731 pI731 = true := by decide +kernel
theorem cvx731 : ConvexBetweenHumps 731 :=
  cvx_of L731_ok H731_ok I731_ok link731 (by decide)

/-! ### `N = 732` -/

def pL732 : Prm := ⟨74, 36, 35, 734, 11, 18446744073709551616, 220905196655406194, 220905196655406194⟩
def pH732 : Prm := ⟨74, 36, 35, 734, 11, 18446744073709551616, 220909594701917298, 220909594701917298⟩
def pI732 : Prm := ⟨63, 31, 29, 734, 11, 18446744073709551616, 220905196655406194, 220909594701917298⟩
theorem L732_fin : (prmOK pL732 732 && ptTest pL732 (runFrom pL732 (fmask pL732) (cmask pL732) (hmask pL732) 1 731 (true, (init pL732), (init pL732))) 732 366 false) = true := by
  decide +kernel
theorem L732_ok : RunOK pL732 732 (runFrom pL732 (fmask pL732) (cmask pL732) (hmask pL732) 1 731 (true, (init pL732), (init pL732))) ∧ ptTest pL732 (runFrom pL732 (fmask pL732) (cmask pL732) (hmask pL732) 1 731 (true, (init pL732), (init pL732))) 732 366 false = true :=
  fin_run (runOK_init (prmOK_of_and L732_fin) true) (by decide) rfl L732_fin ptTest_fst
theorem H732_fin : (prmOK pH732 732 && ptTest pH732 (runFrom pH732 (fmask pH732) (cmask pH732) (hmask pH732) 1 731 (true, (init pH732), (init pH732))) 732 366 true) = true := by
  decide +kernel
theorem H732_ok : RunOK pH732 732 (runFrom pH732 (fmask pH732) (cmask pH732) (hmask pH732) 1 731 (true, (init pH732), (init pH732))) ∧ ptTest pH732 (runFrom pH732 (fmask pH732) (cmask pH732) (hmask pH732) 1 731 (true, (init pH732), (init pH732))) 732 366 true = true :=
  fin_run (runOK_init (prmOK_of_and H732_fin) true) (by decide) rfl H732_fin ptTest_fst
theorem I732_fin : (prmOK pI732 732 && intTest pI732 (runFrom pI732 (fmask pI732) (cmask pI732) (hmask pI732) 1 731 (true, (init pI732), (init pI732))) 732 16 true) = true := by
  decide +kernel
theorem I732_ok : RunOK pI732 732 (runFrom pI732 (fmask pI732) (cmask pI732) (hmask pI732) 1 731 (true, (init pI732), (init pI732))) ∧ intTest pI732 (runFrom pI732 (fmask pI732) (cmask pI732) (hmask pI732) 1 731 (true, (init pI732), (init pI732))) 732 16 true = true :=
  fin_run (runOK_init (prmOK_of_and I732_fin) true) (by decide) rfl I732_fin intTest_fst
theorem link732 : linkOK pL732 pH732 pI732 = true := by decide +kernel
theorem cvx732 : ConvexBetweenHumps 732 :=
  cvx_of L732_ok H732_ok I732_ok link732 (by decide)
theorem cenlink732 : cenLinkOK pI732 732 = true := by decide +kernel
theorem cen732 : CenterUniqueMin 732 ∧ DipHyp 732 ∧ OnePointHyps 732 :=
  cen_of L732_ok H732_ok I732_ok link732 cenlink732

/-! ### The range -/

theorem cvx_639_732 {N : ℕ} (h1 : 639 ≤ N) (h2 : N ≤ 732) : ConvexBetweenHumps N := by
  by_cases h2 : N ≤ 685
  · by_cases h4 : N ≤ 661
    · by_cases h6 : N ≤ 649
      · by_cases h8 : N ≤ 643
        · by_cases h10 : N ≤ 640
          · by_cases h12 : N ≤ 639
            · obtain rfl : N = 639 := by omega
              exact cvx639
            · obtain rfl : N = 640 := by omega
              exact cvx640
          · by_cases h12 : N ≤ 641
            · obtain rfl : N = 641 := by omega
              exact cvx641
            · by_cases h14 : N ≤ 642
              · obtain rfl : N = 642 := by omega
                exact cvx642
              · obtain rfl : N = 643 := by omega
                exact cvx643
        · by_cases h10 : N ≤ 646
          · by_cases h12 : N ≤ 644
            · obtain rfl : N = 644 := by omega
              exact cvx644
            · by_cases h14 : N ≤ 645
              · obtain rfl : N = 645 := by omega
                exact cvx645
              · obtain rfl : N = 646 := by omega
                exact cvx646
          · by_cases h12 : N ≤ 647
            · obtain rfl : N = 647 := by omega
              exact cvx647
            · by_cases h14 : N ≤ 648
              · obtain rfl : N = 648 := by omega
                exact cvx648
              · obtain rfl : N = 649 := by omega
                exact cvx649
      · by_cases h8 : N ≤ 655
        · by_cases h10 : N ≤ 652
          · by_cases h12 : N ≤ 650
            · obtain rfl : N = 650 := by omega
              exact cvx650
            · by_cases h14 : N ≤ 651
              · obtain rfl : N = 651 := by omega
                exact cvx651
              · obtain rfl : N = 652 := by omega
                exact cvx652
          · by_cases h12 : N ≤ 653
            · obtain rfl : N = 653 := by omega
              exact cvx653
            · by_cases h14 : N ≤ 654
              · obtain rfl : N = 654 := by omega
                exact cvx654
              · obtain rfl : N = 655 := by omega
                exact cvx655
        · by_cases h10 : N ≤ 658
          · by_cases h12 : N ≤ 656
            · obtain rfl : N = 656 := by omega
              exact cvx656
            · by_cases h14 : N ≤ 657
              · obtain rfl : N = 657 := by omega
                exact cvx657
              · obtain rfl : N = 658 := by omega
                exact cvx658
          · by_cases h12 : N ≤ 659
            · obtain rfl : N = 659 := by omega
              exact cvx659
            · by_cases h14 : N ≤ 660
              · obtain rfl : N = 660 := by omega
                exact cvx660
              · obtain rfl : N = 661 := by omega
                exact cvx661
    · by_cases h6 : N ≤ 673
      · by_cases h8 : N ≤ 667
        · by_cases h10 : N ≤ 664
          · by_cases h12 : N ≤ 662
            · obtain rfl : N = 662 := by omega
              exact cvx662
            · by_cases h14 : N ≤ 663
              · obtain rfl : N = 663 := by omega
                exact cvx663
              · obtain rfl : N = 664 := by omega
                exact cvx664
          · by_cases h12 : N ≤ 665
            · obtain rfl : N = 665 := by omega
              exact cvx665
            · by_cases h14 : N ≤ 666
              · obtain rfl : N = 666 := by omega
                exact cvx666
              · obtain rfl : N = 667 := by omega
                exact cvx667
        · by_cases h10 : N ≤ 670
          · by_cases h12 : N ≤ 668
            · obtain rfl : N = 668 := by omega
              exact cvx668
            · by_cases h14 : N ≤ 669
              · obtain rfl : N = 669 := by omega
                exact cvx669
              · obtain rfl : N = 670 := by omega
                exact cvx670
          · by_cases h12 : N ≤ 671
            · obtain rfl : N = 671 := by omega
              exact cvx671
            · by_cases h14 : N ≤ 672
              · obtain rfl : N = 672 := by omega
                exact cvx672
              · obtain rfl : N = 673 := by omega
                exact cvx673
      · by_cases h8 : N ≤ 679
        · by_cases h10 : N ≤ 676
          · by_cases h12 : N ≤ 674
            · obtain rfl : N = 674 := by omega
              exact cvx674
            · by_cases h14 : N ≤ 675
              · obtain rfl : N = 675 := by omega
                exact cvx675
              · obtain rfl : N = 676 := by omega
                exact cvx676
          · by_cases h12 : N ≤ 677
            · obtain rfl : N = 677 := by omega
              exact cvx677
            · by_cases h14 : N ≤ 678
              · obtain rfl : N = 678 := by omega
                exact cvx678
              · obtain rfl : N = 679 := by omega
                exact cvx679
        · by_cases h10 : N ≤ 682
          · by_cases h12 : N ≤ 680
            · obtain rfl : N = 680 := by omega
              exact cvx680
            · by_cases h14 : N ≤ 681
              · obtain rfl : N = 681 := by omega
                exact cvx681
              · obtain rfl : N = 682 := by omega
                exact cvx682
          · by_cases h12 : N ≤ 683
            · obtain rfl : N = 683 := by omega
              exact cvx683
            · by_cases h14 : N ≤ 684
              · obtain rfl : N = 684 := by omega
                exact cvx684
              · obtain rfl : N = 685 := by omega
                exact cvx685
  · by_cases h4 : N ≤ 708
    · by_cases h6 : N ≤ 696
      · by_cases h8 : N ≤ 690
        · by_cases h10 : N ≤ 687
          · by_cases h12 : N ≤ 686
            · obtain rfl : N = 686 := by omega
              exact cvx686
            · obtain rfl : N = 687 := by omega
              exact cvx687
          · by_cases h12 : N ≤ 688
            · obtain rfl : N = 688 := by omega
              exact cvx688
            · by_cases h14 : N ≤ 689
              · obtain rfl : N = 689 := by omega
                exact cvx689
              · obtain rfl : N = 690 := by omega
                exact cvx690
        · by_cases h10 : N ≤ 693
          · by_cases h12 : N ≤ 691
            · obtain rfl : N = 691 := by omega
              exact cvx691
            · by_cases h14 : N ≤ 692
              · obtain rfl : N = 692 := by omega
                exact cvx692
              · obtain rfl : N = 693 := by omega
                exact cvx693
          · by_cases h12 : N ≤ 694
            · obtain rfl : N = 694 := by omega
              exact cvx694
            · by_cases h14 : N ≤ 695
              · obtain rfl : N = 695 := by omega
                exact cvx695
              · obtain rfl : N = 696 := by omega
                exact cvx696
      · by_cases h8 : N ≤ 702
        · by_cases h10 : N ≤ 699
          · by_cases h12 : N ≤ 697
            · obtain rfl : N = 697 := by omega
              exact cvx697
            · by_cases h14 : N ≤ 698
              · obtain rfl : N = 698 := by omega
                exact cvx698
              · obtain rfl : N = 699 := by omega
                exact cvx699
          · by_cases h12 : N ≤ 700
            · obtain rfl : N = 700 := by omega
              exact cvx700
            · by_cases h14 : N ≤ 701
              · obtain rfl : N = 701 := by omega
                exact cvx701
              · obtain rfl : N = 702 := by omega
                exact cvx702
        · by_cases h10 : N ≤ 705
          · by_cases h12 : N ≤ 703
            · obtain rfl : N = 703 := by omega
              exact cvx703
            · by_cases h14 : N ≤ 704
              · obtain rfl : N = 704 := by omega
                exact cvx704
              · obtain rfl : N = 705 := by omega
                exact cvx705
          · by_cases h12 : N ≤ 706
            · obtain rfl : N = 706 := by omega
              exact cvx706
            · by_cases h14 : N ≤ 707
              · obtain rfl : N = 707 := by omega
                exact cvx707
              · obtain rfl : N = 708 := by omega
                exact cvx708
    · by_cases h6 : N ≤ 720
      · by_cases h8 : N ≤ 714
        · by_cases h10 : N ≤ 711
          · by_cases h12 : N ≤ 709
            · obtain rfl : N = 709 := by omega
              exact cvx709
            · by_cases h14 : N ≤ 710
              · obtain rfl : N = 710 := by omega
                exact cvx710
              · obtain rfl : N = 711 := by omega
                exact cvx711
          · by_cases h12 : N ≤ 712
            · obtain rfl : N = 712 := by omega
              exact cvx712
            · by_cases h14 : N ≤ 713
              · obtain rfl : N = 713 := by omega
                exact cvx713
              · obtain rfl : N = 714 := by omega
                exact cvx714
        · by_cases h10 : N ≤ 717
          · by_cases h12 : N ≤ 715
            · obtain rfl : N = 715 := by omega
              exact cvx715
            · by_cases h14 : N ≤ 716
              · obtain rfl : N = 716 := by omega
                exact cvx716
              · obtain rfl : N = 717 := by omega
                exact cvx717
          · by_cases h12 : N ≤ 718
            · obtain rfl : N = 718 := by omega
              exact cvx718
            · by_cases h14 : N ≤ 719
              · obtain rfl : N = 719 := by omega
                exact cvx719
              · obtain rfl : N = 720 := by omega
                exact cvx720
      · by_cases h8 : N ≤ 726
        · by_cases h10 : N ≤ 723
          · by_cases h12 : N ≤ 721
            · obtain rfl : N = 721 := by omega
              exact cvx721
            · by_cases h14 : N ≤ 722
              · obtain rfl : N = 722 := by omega
                exact cvx722
              · obtain rfl : N = 723 := by omega
                exact cvx723
          · by_cases h12 : N ≤ 724
            · obtain rfl : N = 724 := by omega
              exact cvx724
            · by_cases h14 : N ≤ 725
              · obtain rfl : N = 725 := by omega
                exact cvx725
              · obtain rfl : N = 726 := by omega
                exact cvx726
        · by_cases h10 : N ≤ 729
          · by_cases h12 : N ≤ 727
            · obtain rfl : N = 727 := by omega
              exact cvx727
            · by_cases h14 : N ≤ 728
              · obtain rfl : N = 728 := by omega
                exact cvx728
              · obtain rfl : N = 729 := by omega
                exact cvx729
          · by_cases h12 : N ≤ 730
            · obtain rfl : N = 730 := by omega
              exact cvx730
            · by_cases h14 : N ≤ 731
              · obtain rfl : N = 731 := by omega
                exact cvx731
              · obtain rfl : N = 732 := by omega
                exact cvx732

theorem cen_639_732 {N : ℕ} (h1 : 639 ≤ N) (h2 : N ≤ 732) (hev : N % 2 = 0) :
    CenterUniqueMin N ∧ DipHyp N ∧ OnePointHyps N := by
  by_cases h2 : N ≤ 684
  · by_cases h4 : N ≤ 660
    · by_cases h6 : N ≤ 648
      · by_cases h8 : N ≤ 642
        · by_cases h10 : N ≤ 640
          · obtain rfl : N = 640 := by omega
            exact cen640
          · obtain rfl : N = 642 := by omega
            exact cen642
        · by_cases h10 : N ≤ 644
          · obtain rfl : N = 644 := by omega
            exact cen644
          · by_cases h12 : N ≤ 646
            · obtain rfl : N = 646 := by omega
              exact cen646
            · obtain rfl : N = 648 := by omega
              exact cen648
      · by_cases h8 : N ≤ 654
        · by_cases h10 : N ≤ 650
          · obtain rfl : N = 650 := by omega
            exact cen650
          · by_cases h12 : N ≤ 652
            · obtain rfl : N = 652 := by omega
              exact cen652
            · obtain rfl : N = 654 := by omega
              exact cen654
        · by_cases h10 : N ≤ 656
          · obtain rfl : N = 656 := by omega
            exact cen656
          · by_cases h12 : N ≤ 658
            · obtain rfl : N = 658 := by omega
              exact cen658
            · obtain rfl : N = 660 := by omega
              exact cen660
    · by_cases h6 : N ≤ 672
      · by_cases h8 : N ≤ 666
        · by_cases h10 : N ≤ 662
          · obtain rfl : N = 662 := by omega
            exact cen662
          · by_cases h12 : N ≤ 664
            · obtain rfl : N = 664 := by omega
              exact cen664
            · obtain rfl : N = 666 := by omega
              exact cen666
        · by_cases h10 : N ≤ 668
          · obtain rfl : N = 668 := by omega
            exact cen668
          · by_cases h12 : N ≤ 670
            · obtain rfl : N = 670 := by omega
              exact cen670
            · obtain rfl : N = 672 := by omega
              exact cen672
      · by_cases h8 : N ≤ 678
        · by_cases h10 : N ≤ 674
          · obtain rfl : N = 674 := by omega
            exact cen674
          · by_cases h12 : N ≤ 676
            · obtain rfl : N = 676 := by omega
              exact cen676
            · obtain rfl : N = 678 := by omega
              exact cen678
        · by_cases h10 : N ≤ 680
          · obtain rfl : N = 680 := by omega
            exact cen680
          · by_cases h12 : N ≤ 682
            · obtain rfl : N = 682 := by omega
              exact cen682
            · obtain rfl : N = 684 := by omega
              exact cen684
  · by_cases h4 : N ≤ 708
    · by_cases h6 : N ≤ 696
      · by_cases h8 : N ≤ 690
        · by_cases h10 : N ≤ 686
          · obtain rfl : N = 686 := by omega
            exact cen686
          · by_cases h12 : N ≤ 688
            · obtain rfl : N = 688 := by omega
              exact cen688
            · obtain rfl : N = 690 := by omega
              exact cen690
        · by_cases h10 : N ≤ 692
          · obtain rfl : N = 692 := by omega
            exact cen692
          · by_cases h12 : N ≤ 694
            · obtain rfl : N = 694 := by omega
              exact cen694
            · obtain rfl : N = 696 := by omega
              exact cen696
      · by_cases h8 : N ≤ 702
        · by_cases h10 : N ≤ 698
          · obtain rfl : N = 698 := by omega
            exact cen698
          · by_cases h12 : N ≤ 700
            · obtain rfl : N = 700 := by omega
              exact cen700
            · obtain rfl : N = 702 := by omega
              exact cen702
        · by_cases h10 : N ≤ 704
          · obtain rfl : N = 704 := by omega
            exact cen704
          · by_cases h12 : N ≤ 706
            · obtain rfl : N = 706 := by omega
              exact cen706
            · obtain rfl : N = 708 := by omega
              exact cen708
    · by_cases h6 : N ≤ 720
      · by_cases h8 : N ≤ 714
        · by_cases h10 : N ≤ 710
          · obtain rfl : N = 710 := by omega
            exact cen710
          · by_cases h12 : N ≤ 712
            · obtain rfl : N = 712 := by omega
              exact cen712
            · obtain rfl : N = 714 := by omega
              exact cen714
        · by_cases h10 : N ≤ 716
          · obtain rfl : N = 716 := by omega
            exact cen716
          · by_cases h12 : N ≤ 718
            · obtain rfl : N = 718 := by omega
              exact cen718
            · obtain rfl : N = 720 := by omega
              exact cen720
      · by_cases h8 : N ≤ 726
        · by_cases h10 : N ≤ 722
          · obtain rfl : N = 722 := by omega
            exact cen722
          · by_cases h12 : N ≤ 724
            · obtain rfl : N = 724 := by omega
              exact cen724
            · obtain rfl : N = 726 := by omega
              exact cen726
        · by_cases h10 : N ≤ 728
          · obtain rfl : N = 728 := by omega
            exact cen728
          · by_cases h12 : N ≤ 730
            · obtain rfl : N = 730 := by omega
              exact cen730
            · obtain rfl : N = 732 := by omega
              exact cen732

end Kagey131.PaperD.T7
