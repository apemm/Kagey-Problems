# Frozen-state transition completion

9 November 2026.

The sparse height-eight search stopped at its memory cap after discovering
55,967,492 states and fully processing 20,360,000 of them. The new frozen
engine computes additional transitions within that fixed state set.
It never inserts a state or a 256-bit block. A valid transition whose
target is absent from the fixed set is omitted.

The original residual transition and dense-state hash are copied unchanged
by [build_frozen_sea.py](build_frozen_sea.py) into
[SeaGraphFrozen.cs](SeaGraphFrozen.cs).
[SeaFrozenStorage.cs](SeaFrozenStorage.cs) reads the original sparse
checkpoint. Its block pool has no insertion operation, and state hash
matches are resolved by comparing every original 256-bit block.
It does not rebuild the unused block-interning hash table.

Transitions stream to disk. The raw format contains the input checkpoint
and residual-table SHA-256 hashes, fixed state count, original processed
boundary, and complete labeled source rows. An atomic status file records
the committed source boundary only after the edge stream has been flushed.
A resume validates both input hashes and the raw header, then discards any
uncommitted trailing bytes before continuing. Source rows are never
partially committed.

The independent height-six calibration checks every one of 127,032
labeled transitions on a frozen set of 21,172 states against the original
complete height-six graph, after dropping exactly the targets outside
that set. It includes a stop and resume at source 11,000. The result is
[sea_frozen_h6_independent_check.json](sea_frozen_h6_independent_check.json).
A separate forced-collision check loads 256 distinct states with one
shared hash, verifies all exact lookups and dense reconstructions, rejects
an absent state with the same hash, and verifies that the store did not
change.

An independent source review also passed. It checked the immutable pool
and lookup, equality after hash collisions, copied transition semantics,
initial edge preservation, complete-row flush before status advancement,
input fingerprint checks on resume, and truncation of an uncommitted
suffix.

The height-eight run has a hard UTC deadline of 18:10 on 9 November 2026
and a 20.5 GiB memory cap. Its checkpoint remains untouched. Whether this
frozen run finishes or stops early,
[extract_frozen_prefix.py](extract_frozen_prefix.py) retains only fully
processed sources and targets within their committed prefix. The resulting
finite graph is an exact induced lower model of the full sea graph.
Completing the frozen graph would not complete the full sea graph: targets
outside the saved state set remain unexamined.
