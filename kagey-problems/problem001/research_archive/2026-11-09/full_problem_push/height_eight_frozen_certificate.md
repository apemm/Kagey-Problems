# A stronger exact height-eight canonical lower certificate

9 November 2026. The parity sea's canonical component satisfies

\[
\boxed{\lambda_*(8)\ge 2.928738.}
\]

This is a certified lower bound from an induced graph on the saved states. The full height-eight sea graph remains unresolved. The earlier processed-prefix lower bound 2.591155 is preserved in its original files and is strengthened here.

## The completed frozen model

The original sparse checkpoint contains 55,967,492 discovered states, of which 20,360,000 had processed outgoing transitions. The frozen continuation computed outgoing transitions for every saved state without adding states or residual blocks. Exact full-key comparisons resolve all hash collisions. A valid transition whose target was absent from the saved state set was omitted.

The frozen pass completed in 8,696.83 seconds, with recorded working memory at completion of 19,479.29 MiB. It recorded 90,323,380 transitions to states outside the fixed set. Consequently completion of this pass does not establish completeness of the full graph.

The extracted graph has 55,967,492 states and 119,990,358 retained labeled edges. No target was dropped by the final processed-source extraction, because every source in the fixed set was processed. The extraction verified the raw-file length and checkpoint/residual fingerprints and saved the graph hash.

## Independent component checks

The two-pass SCC computation found 37,377,109 components: 37,377,108 acyclic singletons and one cyclic component of size 18,590,384. A separately implemented iterative Tarjan pass checked the complete partition bijection and the complete cyclic-component list. Both computations agree.

The cyclic component has ID 12,054,551. It contains the constant-row states for rows 2 through 7. The row-one and row-eight fixed states are absent from this finite induced graph. The adjacent-row parity bridge theorem places all constant-row states in the same component of the full sea graph. Therefore this finite cyclic component is contained in the full canonical component. Its self-loops also make it primitive.

The SCC computation took 35.76 seconds with peak memory 4,094.94 MiB; the independent Tarjan check took 27.33 seconds with peak memory 3,591.33 MiB.

## Exact spectral inequalities

The proposed positive weights have scale approximately 10^60. The smallest saved weight is

4885598076547554399607566491334458831011840.

An independent checker streamed the original graph and component files and verified, for every component state i,

\[
2928738\,v_i
\le 10^6\sum_{i\to j}v_j
\le 2928739\,v_i.
\]

The sum uses only targets in the same component and counts labeled edges with their multiplicity. The checker verified all 18,590,384 rows and 44,183,669 internal labeled edges using arbitrary-precision integers. Thus this finite component's Perron root belongs to [2.928738,2.928739]. Extending the lower-certificate vector by zero proves the lower bound for the full canonical component. The upper endpoint does not bound that full component.

Floating-point iteration only proposed the weights. It ran 380 iterations; the generation phase took 570.15 seconds, and the separate exact check took 37.48 seconds. The reported enclosure follows from the integer inequalities, not from a numerical convergence tolerance.

## Certificate files

- Frozen transition status: [sea_frozen_h8.status.json](sea_frozen_h8.status.json).
- Extraction: [sea_frozen_h8_prefix.extraction.json](sea_frozen_h8_prefix.extraction.json).
- Component report: [sea_frozen_h8_prefix.json](sea_frozen_h8_prefix.json).
- Independent SCC check: [sea_frozen_h8_prefix.tarjan.json](sea_frozen_h8_prefix.tarjan.json).
- Integer certificate: [sea_frozen_h8_prefix.perron_wide.12054551.json](sea_frozen_h8_prefix.perron_wide.12054551.json).
- Independent integer check: [sea_frozen_h8_prefix.perron_wide.12054551.check.json](sea_frozen_h8_prefix.perron_wide.12054551.check.json).

The graph SHA-256 is 67f7ee62cba8d9eb0e1175d923c10676302e47265842c08aa3a947445839b434.

The component-file SHA-256 is 7691538b26673f606314ad39f9f61f5ebf43bb2039f3cc14288935d8f842d0b1.

The weight-file SHA-256 is a55badc887c44805c1c6c0d22e9c2b7df37b1a40b4020655a5fe21e194632c2c.

The original checkpoint and all earlier certificates remain unchanged. No graph computation is left running by this certificate workflow.
