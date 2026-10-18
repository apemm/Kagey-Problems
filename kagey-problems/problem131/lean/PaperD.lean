import PaperD.Words
import PaperD.Elephant
import PaperD.ElephantAlgebra
import PaperD.ElephantFirstOrder
import PaperD.ElephantCrossing
import PaperD.ElephantEndpoint
import PaperD.ElephantUnimodal
import PaperD.CenterConvex
import PaperD.SignChain1
import PaperD.SignChain2
import PaperD.SignChain3
import PaperD.SignChain4
import PaperD.SignChain5
import PaperD.RecursiveTree
import PaperD.HeavyRuns
import PaperD.Aging
import PaperD.AgingExact
import PaperD.AgingCrossing
import PaperD.AgingSmall
import PaperD.AgingAveraging
import PaperD.AgingSwitches
import PaperD.BetaBinomial
import PaperD.T1_All
import PaperD.T2_All
import PaperD.T8_RRTRelabel
import PaperD.T3_Urn
import PaperD.T4_All
import PaperD.A4_Full
import PaperD.T5_Kernel
import PaperD.T6_Crossing
import PaperD.T6_CrossingAsymp
import PaperD.T6_DipHyp
import PaperD.T6_Markov
import PaperD.T6_SmallRatios
import PaperD.T6_Eventual
import PaperD.T6_DipHypExact
import PaperD.T7_Kernel_All
import PaperD.EndToEnd
import PaperD.EndToEnd_Cert
import PaperD.U1_Anc
import PaperD.U1_CP
import PaperD.U1_CPLaw
import PaperD.U1_Complex
import PaperD.U1_Depth
import PaperD.U1_Steps
import PaperD.U1_Variance
import PaperD.U2_All
import PaperD.U2_Bridge
import PaperD.U2_LandauCharFun
import PaperD.U2_LandauClassL
import PaperD.U2_LandauClosedForm
import PaperD.U2_LandauDensity
import PaperD.U2_LandauFacts
import PaperD.U2_LandauLaw
import PaperD.U2_LandauLimit
import PaperD.U2_LandauLimitSharp
import PaperD.U2_LandauLocal
import PaperD.U2_LandauNat
import PaperD.U2_LandauSharp
import PaperD.U3_Asymp
import PaperD.U3_Hyp
import PaperD.U3_LandauMode
import PaperD.U3_Main
import PaperD.U3_Mode
import PaperD.U3_Odd
import PaperD.U3_OddCrossing
import PaperD.U3_Shape
import PaperD.U3_Transfer
import PaperD.U3_Window
import PaperD.U4_All
import PaperD.U4_Bridge
import PaperD.U4_Btail
import PaperD.U4_Hyper
import PaperD.U4_Moments
import PaperD.U4_Path
import PaperD.U4_Refined
import PaperD.U4_Remark
import PaperD.U4_SecondOrder
import PaperD.U4_Uniform
import PaperD.U4_Weights
import PaperD.U4_WeightsLimit
import PaperD.U5_Chain
import PaperD.U5_CumDecomp
import PaperD.U5_CumUpper
import PaperD.U5_CumUpperFinal
import PaperD.U5_CumUpperMain
import PaperD.U5_Late
import PaperD.U5_LocalLower
import PaperD.U5_LocalLowerMain
import PaperD.U5_LocalUpper
import PaperD.U5_LocalUpperMain
import PaperD.U5_Mode
import PaperD.U5_Odd
import PaperD.U5_Profile
import PaperD.U5_ProfileWitness
import PaperD.U5_Sandwich
import PaperD.U5_Tail
import PaperD.U5_Urn
import PaperD.U6_Bridge
import PaperD.U6_Cert
import PaperD.U6_Code
import PaperD.U6_Contour
import PaperD.U6_Landau
import PaperD.U6_Lemma
import PaperD.U6_Piece
import PaperD.U6_Scalar
import PaperD.U6_Series
import PaperD.U6_TMSound
import PaperD.U_EndToEnd

/-!
# Paper D (Problem 131 under memory), root module

Imports every module of the Lean proofs for Paper D: the elephant random walk near total recall
(topic D1), the random recursive tree behind its profile (D2), heavy-tailed runs and the
golden-ratio exponent (D3), and the aging walk (D4). The topics D3 and D4 are now Paper F. See
`PaperD/MAP.md` for the map from the paper's and the research notes' statements to theorem names.

The modules `T1_*` to `T8_*` are the tracks of October 2026 (sign chain, random recursive tree,
first flip and lower bound, upper bound, certificate checker, crossing analysis, kernel-checked
certificates for `101 ≤ N ≤ 2000`, and the relabeling of Lemma 3.2). `EndToEnd` and
`EndToEnd_Cert` compose them.

The modules `U1_*` to `U5_*` are the tracks of October 18, 2026: the compound Poisson bulk
(Theorem 3.8, U1), the Landau limit (Theorem 3.9, U2), the mode and convexity for large `N`
(Lemma 3.10, Corollary 3.11, Theorem 3.21, Corollary 3.23, Proposition 3.25(b), (d), U3), the
second order and the bridge of Online Resource 1, Section S1 (U4), and Appendix B with the tail
of Online Resource 1, Section S2 (U5). The modules `U6_*` prove the certified numbers of
Lemma 3.10 by kernel-checked integration (U6), and the contour rotation that turns the Fourier
form of the Landau density into the real integral. `U_EndToEnd` composes U1 to U3 and U6, so
that every statement about the bulk rests only on the named classical inputs listed in
`PaperD/MAP.md`.

Every module is checked by the kernel. No module uses `native_decide`, and every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
`lake build PaperD` checks the whole library.
-/
