import PaperD.U2_LandauFacts
import PaperD.U2_LandauClosedForm
import PaperD.U2_LandauLocal
import PaperD.U2_LandauNat
import PaperD.U2_LandauLaw
import PaperD.U2_LandauLimit
import PaperD.U2_LandauClassL
import PaperD.U2_LandauSharp
import PaperD.U2_LandauDensity
import PaperD.U2_LandauLimitSharp
import PaperD.U2_LandauCharFun

/-!
# Track U2: Paper D, Theorem 3.9 (`thm:landau`) and Appendix C.2

See `U2_LandauLocal` (parts (a), (b), `C = 3600`), `U2_LandauSharp` (parts (a), (b), `C = 889`),
`U2_LandauNat` (U1-indexed interface), `U2_LandauLaw`, `U2_LandauLimit` and `U2_LandauLimitSharp`
(part (c)), `U2_LandauDensity` (`f_L` is a probability density, proved), `U2_LandauCharFun`
(`e^B` is its characteristic function; self-decomposability).
This module does not import track U1; `U2_Bridge` (which imports `PaperD.U1_CP`) discharges the
Theorem 3.8 hypothesis and states the final theorems with only classical hypotheses.
-/
