import PaperD.T2_RRT
import PaperD.T2_RRTFamilies
import PaperD.T2_RRTForced
import PaperD.T2_RRTFirstD
import PaperD.T2_RRTMarkov
import PaperD.T2_RRTFirstFlip
import PaperD.T2_UrnClosed
import PaperD.T2_RRTSplit

/-!
# Paper D, track T2 (random recursive tree): root of the new modules

The root `PaperD.lean` imports this module, so `lake build PaperD` builds every T2 module. The
relabeling step of Lemma 3.2 is in `PaperD.T8_RRTRelabel`, which the root imports too.
-/
