# Exact sparse sea-state engine

9 November 2026. The new engine uses the sparse record measured in [the compression probe](sea_h8_compression_probe.md). Its files are [SeaSparseStorage.cs](SeaSparseStorage.cs), [SeaGraphSparse.cs](SeaGraphSparse.cs), and [run_sparse_sea_graph.ps1](run_sparse_sea_graph.ps1). It retains the block pool and scalar slabs in [PackedSeaStorage.cs](PackedSeaStorage.cs); that older file and engine are unchanged.

## Representation and exactness

A state is still the same vector of original residual bits. Its 256-bit block identifiers are stored using a bitmap for nonzero positions and a fixed bit width recorded separately for each state. Zero positions decode to the canonical all-zero block, whose pool identifier is checked to be zero. Later block-pool growth cannot change existing records.

The global state hash table is unchanged in meaning. A hash match compares every decoded original 256-bit block with the candidate state. Hash collisions therefore never identify different states. Each packing step leaves fewer than eight pending bits before appending an identifier of at most 31 bits, so the 64-bit accumulator cannot overflow.

Byte records use 16 MiB slabs and do not straddle a slab boundary. The total byte count is a signed 64-bit integer and each per-state byte offset is an unsigned 64-bit integer. Unused bytes at the end of a slab are serialized, preserving offsets exactly. The new representation does not form an integer-sized array indexed by state count times 117; it therefore removes the old height-eight vector-index limit near 18.35 million states.

Checkpoint format five, magic 0x53454135, stores the original residual-input SHA256, block pool, byte slabs, offsets, hashes, and processed edges. It accepts format-four imports by reading one old identifier vector at a time and immediately encoding it. It never allocates the old full vector table. New checkpoint writes go to a separate pending file and replace the preceding sparse checkpoint only after writing finishes. The original packed checkpoint is preserved.

The generated engine keeps the audited transition and SCC code. The generator changes storage, checkpoint handling, progress fields, and final garbage collection. A separate code audit confirmed this scope.

## Completed checks

The full height-six graph has 67,689 states. Each of the following runs produced exactly the same labeled binary graph:

* the existing packed engine;
* a fresh sparse run;
* a sparse checkpoint followed by a sparse resume;
* streaming import of an old packed checkpoint followed by completion.

All four SHA256 values are

e54354241e7f28bd6bdc09ea12df2c02195152741950ef5ceb4f736488805af8.

The SCC output also agrees: 2,276 components, of which the sole cyclic component has 65,414 states and contains every constant-row state. The recorded checks and source hashes are in [sea_sparse_storage_validation.json](sea_sparse_storage_validation.json). These binary hashes were recomputed independently.

The separate [SeaSparseCollisionCheck.cs](SeaSparseCollisionCheck.cs) deliberately assigns the same hash to 256 different residual vectors. Every state remains distinct, every repeated lookup returns the original identifier, every dense reconstruction agrees, and the same checks pass after serialization and reloading. Its result is [sea_sparse_collision_check.txt](sea_sparse_collision_check.txt).

## Height-eight run

A bounded height-eight import/resume started at approximately 13:46 UTC on 9 November, with a 7,200-second limit, a 60-million-state cap, and a 20,480 MiB memory cap. It writes only files beginning with sea_sparse_h8. The original packed checkpoint contains 14,233,880 discovered states and 4,460,000 processed states.

The import completed and breadth-first enumeration resumed successfully. The byte store crossed two billion bytes during import. This running experiment is not yet a complete graph certificate. The final status must be read from the complete flag, processed and discovered counts, and stop reason in the resulting JSON file; a partial checkpoint proves no SCC or dominance conclusion by itself.
