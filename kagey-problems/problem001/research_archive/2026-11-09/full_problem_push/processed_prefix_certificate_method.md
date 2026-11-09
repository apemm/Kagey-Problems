# Exact lower certificates from an incomplete sea-graph search

9 November 2026. An incomplete breadth-first search can give a rigorous finite lower model without identifying the full sea graph. This note specifies that distinction and the independent checks used here.

Suppose the search has discovered \(n\) states and fully processed states \(0,\ldots,p-1\). The checkpoint contains all \(hp\) labeled transitions from these processed states. Form the graph on \(0,\ldots,p-1\) by retaining a transition exactly when its target is also below \(p\). Targets in the unprocessed frontier are replaced by absent transitions.

This is an induced subgraph of the exact sea automaton. Every retained edge is known, and no transition is inferred from an unprocessed state. Its finite graph is fully specified even though the full sea graph is unresolved.

## Extraction and independent checks

[extract_sparse_processed_prefix.py](extract_sparse_processed_prefix.py) reads the format-five header, verifies the residual-table fingerprint, and seeks over the block pool, sparse byte records, offsets, and state hashes. It checks
\[
 \#\text{stored transitions}=hp
\]
and the exact checkpoint length before streaming the transition table. It validates every target, drops only frontier targets, and records graph and checkpoint hashes.

On the saved height-six checkpoint, its \(60,000\) extracted labeled transitions agree exactly with the complete height-six graph restricted to the same \(10,000\) states. The test includes both retained transitions and dropped frontier targets.

[SeaPrefixComponents.cs](SeaPrefixComponents.cs) uses the unchanged two-pass SCC routine from the audited graph builder. [SeaPrefixTarjanCheck.cs](SeaPrefixTarjanCheck.cs) independently computes all components by iterative Tarjan search, and checks a bijection between the two complete component partitions. It also checks the cyclic-component list. Calibration passes both the height-six prefix, which has three cyclic components, and the complete height-six graph.

The generated prefix report sets its own finite-model completion flag to true, and separately records

    full_graph_complete: false

These flags must not be conflated.

## Canonical-component spectral meaning

If the prefix contains the constant-row-one fixed state, every state in its strongly connected component belongs to the canonical component of the full sea graph. Both directions of reachability already use retained edges.

For the parity partition it is enough that the component contain any
constant-row fixed state. The proved adjacent-row full-shift lemma joins
every constant row to row one in the full graph. The height-eight prefix
uses this version: its cyclic component contains constants 2 through 7,
although constants 1 and 8 are outside the processed prefix.

A positive integer weight vector on this finite component gives a lower certificate by checking
\[
 L v_i\le\sum_{i\to j}v_j
\]
at every component state. Extend the weights by zero to the rest of the full canonical component. The inequality remains true, because omitted edges have nonnegative contributions. Iteration therefore gives
\[
 \lambda_*(h)\ge L.
\]
The fixed final row-pair set and the exact local-pattern model are unchanged.

An upper Collatz inequality for the extracted finite component bounds only that component's Perron root. It is not an upper bound for the full canonical component or for the full sea graph. Likewise, its SCC count does not classify the full graph.

The existing independent integer checker verifies every Collatz inequality from the saved graph and weights. The source model, graph hashes, exact component, and rational bound are retained in the certificate files.
