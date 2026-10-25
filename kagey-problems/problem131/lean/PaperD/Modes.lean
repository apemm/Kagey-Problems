import PaperD.Modes.NearOneNumeric
import PaperD.Modes.SignTools
import PaperD.Modes.SpLimit
import PaperD.Modes.HeightWindow
import PaperD.Modes.NearOneProb
import PaperD.Modes.GammaMoments
import PaperD.Modes.NearOne
import PaperD.Modes.SpDerivative
import PaperD.Modes.PolySigns
import PaperD.Modes.PolySigns2
import PaperD.Modes.PolyValues
import PaperD.Modes.Smoothing
import PaperD.Modes.Dichotomy
import PaperD.Modes.ExpSignsA
import PaperD.Modes.ExpDescartes
import PaperD.Modes.ExpValues
import PaperD.Modes.GaussDeriv
import PaperD.Modes.EdgeBounds
import PaperD.Modes.StepTwoA
import PaperD.Modes.StepTwoB
import PaperD.Modes.Mollify
import PaperD.Modes.TwoModes

/-!
# Paper D, the number of modes of the fair-start limit law

Sub-root for the modules in `PaperD/Modes/`. They formalize the sign-pattern lemmas of `app_modes.tex`
(`lem:descartes`, for equally spaced exponents and for arbitrary real exponents, `lem:sp-limit`,
`lem:sp-derivative`), Steps 1 to 5 of the proof of `thm:two-modes` and its assembly with the
limit-law hypotheses (`TwoModes`), the numerical and probabilistic core and the moment bounds of
`thm:two-modes-near-one`, and `cor:height-window`. The computer-assisted `thm:threshold` is not
included.
-/
