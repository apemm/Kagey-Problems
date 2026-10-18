import PaperD.T5_Compute
import PaperD.T5_Checker
import PaperD.T5_Data
import PaperD.T5_Interface
import PaperD.T5_Crossing
import PaperD.T5_Run

/-!
# Paper D, track T5: aggregate of the kernel-checked modules

`PaperD.lean` imports this aggregate, so a plain `lake build PaperD` checks it.

It contains only kernel-checked results (standard axioms `propext`, `Classical.choice`,
`Quot.sound`). The certificate runs for `101 ≤ N ≤ 2000` are checked in the kernel by track T7
(`PaperD.T7_Kernel_All`). The earlier compiled runs (`native_decide`) of track T5 were removed
from the library on October 17, 2026.
-/
