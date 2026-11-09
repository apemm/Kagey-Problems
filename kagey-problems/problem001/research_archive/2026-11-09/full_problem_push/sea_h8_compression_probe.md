# Exact state-compression measurements for height eight

9 November 2026. These are bounded representation probes, not another graph enumeration. The original packed engine and checkpoint were left unchanged. The checkpoint remains incomplete: 14,233,880 discovered states, 4,460,000 processed states, and 35,680,000 recorded transitions.

Each state has 117 identifiers for interned 256-bit blocks. The flat identifier vector therefore costs 468 bytes per state, excluding the shared block pool, state hashes, lookup table, and graph edges. The checkpoint contains 28,280,865 distinct blocks. Its residual-input SHA256 is

4a8dc51ab6b91b49fb4823bfc9a308e028784d93521890e9081ce38334ead125.

## Binary hash-consing is not the next implementation to try

[sea_hierarchy_probe.py](sea_hierarchy_probe.py) interns adjacent pairs recursively after padding to 128 entries. Every interning step compares complete keys through exact lexical uniqueness and verifies reconstruction of every input pair. The estimated storage includes eight bytes per distinct pair, a power-of-two four-byte hash table at load at most 0.72, and the remaining per-state identifier vector. Common block-pool and graph costs are excluded from both sides.

| Sample | Flat vector | One binary level | Full binary hierarchy |
|---|---:|---:|---:|
| 10,000 uniformly spread states | 468 | 689.11 | 1,216.16 |
| 100,000 uniformly spread states | 468 | 557.15 | 857.93 |
| Last 20,000 states | 468 | 501.90 | 851.06 |

All entries are bytes per sampled state. Direct interning of four-entry chunks was somewhat better: 425.68 bytes per state in the 100,000-state sample, but 451.56 in the late contiguous sample. Simple run-length encoding was worse than the flat vector. A position-wise modal base was scarcely better than the all-zero base.

Larger dictionaries can create more reuse, so the sample does not prove that a full-checkpoint tree would be larger. It does show that this hierarchy needs substantial additional reuse to compete with a much simpler sparse record. The 100,000-state hierarchy experiment took 38.08 seconds and reached 553.4 MiB peak working set; the late 20,000-state experiment took 3.16 seconds and reached 100.3 MiB.

## A sparse bit-packed record saves about 38 percent

The native prototype [SeaSparseRecordProbe.cs](SeaSparseRecordProbe.cs) stores each state as:

1. one byte giving the bit width of its largest block identifier;
2. a 15-byte bitmap marking the nonzero positions among 117 entries;
3. the nonzero identifiers, packed at that record's fixed bit width;
4. one eight-byte offset per state.

Identifier zero was explicitly checked to mean the zero 256-bit block. The per-record width is immutable; subsequent growth of the block pool does not change old records. Every decoded identifier was compared with its original value. Thus state equality is exact, without any assumption about hash collisions.

| Sample | Record and offset bytes/state | Saving from 468 bytes |
|---|---:|---:|
| 100,000 uniformly spread states | 285.92 | 38.91% |
| Last 100,000 states | 293.56 | 37.27% |

The first sample encoded in 0.190 seconds. Ten complete decode passes took 1.449 seconds, or about 1.45 microseconds per state. The late sample encoded in 0.109 seconds and ten decode passes took 0.761 seconds. Direct flat-array copying was faster, at about 0.03 seconds per million states; the record method is a memory tradeoff. These are short native-process measurements, not end-to-end engine timings.

Peak working sets were 258.3 and 265.0 MiB, respectively. The prototype keeps both original and compressed samples for full comparison, and its growing memory stream has unused capacity. Production storage should use byte slabs and eight-byte offsets, with each record contained in a single slab. The prototype's single-array decoder is intentionally limited to these bounded samples.

At the current state count, the uniform-sample rate projects a saving of about 2.59 billion bytes, or 2.41 GiB, in state vectors alone. This is a projection, not a measurement of a converted full checkpoint. The shared block pool, state hashes and table, graph edges, and slab padding still need their own memory budgets.

A separate 100,000-block sample found about 29.95 set bits per distinct 256-bit block. Storing sparse bit positions, even adaptively falling back to raw blocks, projects only about an eleven-percent block-pool saving after offsets. That is a lower-priority complication.

## Recommended next validation

If height-eight enumeration is resumed, the sparse record is the best measured candidate. Before a full run, a separate engine should retain the existing exact state hash table and compare complete decoded records after hash matches. It should then reproduce a completed smaller graph's labeled transitions and demonstrate checkpoint/resume equivalence. None of those engine-level tests is claimed by this storage probe.

The saved measurement files are:

* [Uniform 10,000-state hierarchy](sea_hierarchy_h8_uniform_10000.json)
* [Uniform 100,000-state hierarchy](sea_hierarchy_h8_uniform_100000.json)
* [Late 20,000-state hierarchy](sea_hierarchy_h8_last_20000.json)
* [Uniform 100,000-state sparse records](sea_sparse_record_h8_uniform_100000.json)
* [Late 100,000-state sparse records](sea_sparse_record_h8_last_100000.json)
* [Block-pool sparsity sample](sea_h8_pool_sparsity_sample.json)

No full-checkpoint conversion or new graph search was started.

## Later implementation and a smaller optional refinement

After these probes, a separate sparse engine was implemented and validated; see [Sparse engine validation](sparse_sea_engine_validation.md). That later run does not change the scope of the sample measurements above.

A subsequent sizing-only check on the same 100,000 uniformly spread old states found that a zero bitmap plus seven-bit variable-length nonzero identifiers would average 266.85 bytes per state including an eight-byte offset, compared with 285.92 for the implemented fixed-width record. This is about a seven-percent record reduction, without a measured decoder or complete-engine validation. It is saved in [the varint sizing sample](sea_h8_varint_sizing_sample.json). The running engine was not changed.
