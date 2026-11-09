# Independent audit of the native sea graph and fiber encoding

9 November 2026. This review checks `SeaGraphExact.cs` and
`export_sea_residuals.py` against `sea_sparse_automaton.py`, and checks the
parsimonious variant in `presentation_fiber_factorization.md`. It does not
complete the height-seven graph or assert a new strongly connected component
result.

## Exact transition semantics

The exporter constructs the same residual universe and uses exactly the same
ordering as the Python implementation. A residual is a nonempty set of future
column/row requirements. Its proper subsets appear earlier because cardinality
is the first sorting key. For a residual whose first offset is positive, deleting
one unit from every offset gives the immediately preceding identifier; the
exporter's assertion checks this property for every such residual.

The native transition has the same three steps as Python:

1. Reject when a one-cell residual at offset zero matches the new letter.
2. Shift residuals whose first offset is positive, and collect the tails of
   matching offset-zero residuals together with newly started patterns.
3. Retain the inclusion-minimal union of these two collections.

The shifted collection is already an antichain: the shift is injective and
preserves subset inclusion. The merge checks whether an existing residual is a
subset of each addition; otherwise it deletes existing and pending supersets.
Thus the native merge computes precisely the Python antichain, including
inclusions crossing a 64-bit word boundary. The carry from the next word implements
the same single right shift as Python's arbitrary-precision integer operation.
All output words are overwritten before merging. An early rejection leaves an
irrelevant output buffer, since the caller ignores it.

The exporter raises `TimeoutError` if geometric generation reaches its time cap;
it does not quietly export a partial forbidden-pattern list.

## Encoded equality and graph construction

Each stored state begins with its live-residual count and then gives the sorted
residual identifiers as nonnegative base-128 differences. The first identifier
may be zero. Because the implementation requires fewer than 65,536 residuals,
the two-byte count and at most three bytes per difference are sufficient.

State equality checks the count and verifies that every stored identifier occurs
in the candidate bitset. For correctly encoded states these conditions imply set
equality. Hash collisions therefore cannot merge different states: all entries
with the same 64-bit hash are searched and compared exactly.

The graph queue is the insertion-ordered state array. Each processed state
receives exactly one transition per row, including explicit rejected edges.
Checkpointing occurs only after a complete source state has been processed.
The SCC pass is invoked only when every discovered state has been processed.
Its first iterative DFS constructs finishing order; its reverse CSR traversal in
decreasing finishing order is the standard exact Kosaraju algorithm. Duplicate
labeled edges do not affect this argument.

The existing complete crosscheck compares **all labeled transitions**, including
state identifiers, at heights four, five, and six. Its recorded state counts are
59, 1,600, and 67,689. This is stronger than merely comparing SCC counts.

Two implementation qualifications should remain explicit:

- A checkpoint currently authenticates only height and the number of 64-bit
  residual words. It should also store a hash of the complete exported residual
  table. Different row partitions, including reflected partitions, can have
  equal table dimensions but different letter masks and residual identifiers.
  The reviewed runs use matching checkpoint inputs, so this is a future-resume
  hazard rather than an identified error in those runs.
- The SCC neighbor cursor is a byte, and edge-array sizes and offsets are signed
  32-bit integers. The implementation is appropriate for the current small
  heights and graph sizes, but is not an unrestricted all-height implementation.
  The reported `memory_mb` is a sampled BFS measurement, not a measured peak over
  the later SCC pass.

The height-seven parity result remains incomplete: the saved run discovered
8,353,662 states and processed 6,030,000 before its memory cap. Its `components`
field correctly remains null.

## Bounded storage probe

`sea_state_storage_probe.py` reads a bounded prefix of a checkpoint without
resuming the search. It independently decodes every sampled varint state and
checks the encoded count against both the number of decoded entries and the
population count of the resulting bitset.

For the first 200,000 height-seven states, the average current sparse payload is
374.82 bytes and the average number of live residuals is 362.99. A global pool of
equal fixed-width bit blocks gives the following packed-storage estimates:

| Block width | Identifiers per state | Distinct blocks | Estimated bytes per state |
|---|---:|---:|---:|
| 64 bits | 128 | 415,118 | 539.67 |
| 128 bits | 64 | 522,410 | 311.72 |
| 256 bits | 32 | 573,990 | 235.14 |
| 512 bits | 16 | 565,907 | 260.18 |

The estimate includes four bytes per block identifier, fixed-width block payloads,
and a four-byte open-addressing slot at load 0.75 for the shared block dictionary.
It excludes the state dictionary, transitions, runtime array headers, allocator
slack, and SCC work arrays. It is not a resident-memory benchmark. This initial
BFS prefix need not represent the later frontier. The 50,000-state and
200,000-state probes took approximately 5.4 and 23.3 seconds respectively.

An exact implementation can intern 256-bit blocks by comparing all four 64-bit
words, store each state as 32 packed block identifiers, and hash/compare those
identifier vectors. This changes storage only, not the state equivalence or
graph. Packed slabs avoid one managed allocation per state. A separate
open-addressed state table can store state identifiers and resolve collisions by
full identifier-vector comparison. These changes are more directly supported by
the measurements than another generic decision-diagram run.

The earlier decision-diagram probe reduced the height-six graph from 67,689 to
64,585 states, only about 4.6 percent, while adding substantial intermediate-node
and union-cache storage. Symbolic SCC computation would require a separate,
carefully verified transition representation; the current data do not establish
that it would outperform packed explicit storage. No further height-seven or
height-eight search was launched for this audit.

### Review of the subsequent packed implementation

`PackedSeaStorage.cs` and the generated `SeaGraphPacked.cs` implement the
256-bit scheme exactly. Both open-addressed tables resolve collisions by complete
key comparisons. State comparison checks the hash and every full block; it does
not rely on identifier or hash coincidence alone. The final partial block is
zero-padded consistently, and dense reconstruction writes every genuine word.
Slab insertion order preserves all state and edge identifiers.

The new checkpoint format stores the SHA-256 digest of the exported residual
input and rejects mismatches. This addresses the original resume hazard for new
checkpoints. Importing a legacy checkpoint still requires confirming its input
identity, and the importer states that limitation explicitly. Serialization and
reconstruction preserve the block pool, state vectors, state hashes, and edge
order. The existing height-six binary and checkpoint/resume comparisons are
consistent with this code review. The finite integer-capacity qualifications
above still apply. No additional large graph run was started by this audit.

## Parsimonious presentation fibers

The fiber factorization is exact for arbitrary finite point sets. Distinct
rectangles share at most two vertices. A collision with a two-point intersection
is detected by the complement-pair fiber; a one-point intersection is detected
by the corner-triple fiber; disjoint rectangles can collide only when both are
hidden. Conversely, two true conjunctions in any fiber directly give identical
presentations, regardless of the colors of the shared points.

The counting modification fixes every conjunction flag to its actual Boolean
conjunction. For an at-most-one list, the added equivalences fix every prefix
flag to the actual prefix OR. Thus each point assignment determines all
auxiliaries uniquely, and has a satisfying extension exactly when its
presentations are distinct. Lists of length zero or one need no prefix variables;
the displayed count `4k-5` applies only for `k >= 2`.

The general clause bound is

\[
3(6M)+4(4M)+5M+4(6M+4M+M)=83M.
\]

When the no-hidden theorem applies, remove hidden flags, use one no-hidden clause
per rectangle, and obtain

\[
3(6M)+4(4M)+M+4(6M+4M)=75M.
\]

The auxiliary-variable bounds remain respectively `22M` and `20M`. Exact
cardinality recurrences with equivalences also have unique extensions, so they
preserve parsimony. The result counts all valid point assignments, or those of a
specified black cardinality; counting maximum blackouts still requires the
maximum cardinality to be established separately.

The saved geometric checker tests the conjunction-level factorization on every
blackout of the 2 by 2, 3 by 3, 3 by 4, and 4 by 4 grids. It is not itself a CNF
model-counter test. The unique-extension argument above supplies the additional
counting justification.

The subsequent `presentation_fiber_cnf.py` implementation also passes source
review. Its reverse conjunction and reverse prefix-OR clauses implement exactly
the unique-extension proof. `verify_presentation_fiber_cnf.py` then enumerates
complete models, checks that no point assignment occurs twice, and compares all
point assignments with direct presentation validity on those four grids. This
is an actual test of parsimony. As usual, model counting treats the declared
point-variable universe as part of the input; in the special case of no
rectangles, a caller must still declare those free variables rather than infer
the variable universe from an empty list of clauses.
