# Audit of sparse sea-state storage

9 November 2026. `SeaSparseStorage.cs` and the generated `SeaGraphSparse.cs`
pass independent review for checkpoints written by these engines.

The state encoding preserves the exact vector of 256-bit pool blocks.
Each record stores its own identifier width and a bitmap of nonzero blocks.
Before appending an identifier the packing accumulator contains fewer than
eight bits. An identifier uses at most 31 bits, so the 64-bit accumulator
cannot overflow. Decoding uses the same order and bit widths. Unset bitmap
positions recover the explicitly verified zero block.

Records do not cross 16 MiB slab boundaries. Both the serialized byte count
and offsets include boundary padding, so reconstruction preserves every
record location. The offsets are 64-bit values. The old packed import reads
one fixed-width identifier row at a time, verifies its identifiers, and
re-encodes it without allocating the old flat state matrix.

Hash matches still compare every original block. Sparse storage therefore
does not introduce a probabilistic state quotient. A direct source diff
confirms that transition generation and SCC analysis are unchanged; the
engine changes concern storage, version-four/version-five checkpoint loading,
checkpoint replacement, progress metadata, and final garbage collection.

An independent SHA256 calculation gives the same digest for all four
height-six labeled graph binaries:

```
e54354241e7f28bd6bdc09ea12df2c02195152741950ef5ceb4f736488805af8
```

These are the old packed graph, a fresh sparse run, a sparse checkpoint
resume, and an import of an old packed checkpoint. All contain 67,689 states.
This verifies representation and resume compatibility at height six. It is
not a completeness claim for an unfinished larger-height computation.
