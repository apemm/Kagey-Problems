# Audit of the width-fourteen excess-ten count

9 November 2026. This audits the projected counting setup for 24 black cells on a seven-row, fourteen-column board. It does not report a completed total for the main counting shards.

## Complete structural families

If there are \(z\) empty columns, the excess over nonempty columns is \(10+z\). The established large-column bound excludes every column of size at least four. A triple forces excess at most ten, so it permits only \(z=0\); the equality classification at that excess gives one triple and eight doubles. Without triples, the double graph is triangle-free and has \(10+z\) distinct edges, so Mantel's bound gives \(z\le2\).

The existing catalog contains exactly:

| Triples | Doubles | Empty columns | Vertical-reflection representatives |
|---:|---:|---:|---:|
|0|10|0|1,497|
|1|8|0|957|
|0|11|1|210|

These 2,664 records were complete at width thirteen. Width fourteen adds a fourth possibility: twelve doubles forming \(K_{3,4}\), with two empty columns. There are 35 labeled balanced splits and 19 vertical-reflection representatives. This family cannot be omitted merely because it was absent at width thirteen.

## Counting and symmetry in the existing shards

[count_seven_excess_ten.py](count_seven_excess_ten.py) projects models to their black-cell sets. The encoder fixes the multiplicity of every non-singleton column type and every empty column, so every model has exactly 24 black cells. Adding a clause negating all those black cells therefore excludes exactly that projected board, regardless of auxiliary-variable assignments.

The anchor is the first, unique non-singleton mask in the sorted core. At width fourteen, exactly one of a board and its horizontal reflection puts that mask in a column less than seven. Hence every retained model has horizontal weight two. A core whose vertical reflection is a different core has vertical weight two; a self-reflected core has weight one, because its reflected boards are already enumerated within the same core. These weights remain valid even when a board has a combined horizontal/vertical symmetry.

The crops used by these shards are the already established general bounds, including width thirteen at most 23. They do not impose the stronger no-triple crop on triple cores. Every returned model is checked directly against all rectangle presentations.

Only a completed exhaustion supplies a count. Timeouts or model caps remain unresolved and cannot be included as exact totals.

## The two-empty family is now excluded

[count_seven_fourteen_two_empty.py](count_seven_fourteen_two_empty.py) independently builds the 35 full bipartite cores and their 19 reflection representatives. It preserves the original encoder source. Its wrapper removes exactly the 92 clauses imposing at least one empty column and at most one empty column, then imposes exactly two occurrences of the same empty type.

The original crop literals remain correct: for a crop of length \(L\), the expression counting nonempty columns plus double and triple excess gives the actual black-cell count, regardless of how many empty columns are inside the crop. Twelve distinct doubles and two empties fill all fourteen columns, so no singleton is possible in this added family.

All 19 added cores completed UNSAT in 13.562 seconds. There are no models to contribute to the count. The catalog and source hashes are in [the manifest](seven_fourteen_two_empty_manifest.json), individual outcomes are in [the JSONL record](seven_fourteen_two_empty_count.jsonl), and complete coverage is recorded in [the summary](seven_fourteen_two_empty_summary.json).

These are completed exact-solver exclusions. No separately checked formal UNSAT proof trace is claimed. Together with these additional exclusions, the main 2,664-core shards have the correct structural scope for the full width-fourteen count once all their cores are completed.
