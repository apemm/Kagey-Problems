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

/-!
# Paper D (Problem 131 under memory), root module

Imports every module of the Lean proofs for Paper D: the elephant random walk near total recall
(topic D1), the random recursive tree behind its profile (D2), heavy-tailed runs and the
golden-ratio exponent (D3), and the aging walk (D4). The topics D3 and D4 are now Paper F. See
`PaperD/MAP.md` for the map from the paper's and the research notes' statements to theorem names.

The modules `T1_*` to `T8_*` are the tracks of October 2026 (sign chain, random recursive tree,
first flip and lower bound, upper bound, certificate checker, crossing analysis, kernel-checked
certificates for `101 ≤ N ≤ 2000`, and the relabeling of Lemma 3.2). `EndToEnd` and
`EndToEnd_Cert` compose them. Every module is checked by the kernel. No module uses
`native_decide`, and every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
`lake build PaperD` checks the whole library.
-/
