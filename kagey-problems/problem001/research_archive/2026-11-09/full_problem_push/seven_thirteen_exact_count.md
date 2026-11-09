# Exactly eight maximum blackouts on the seven-by-thirteen board

9 November 2026. With labeled row and column positions,

\[
\boxed{f(7,13)=23,\qquad a_7(13)=8.}
\]

The maximum size was established previously. The new result is the exact
multiplicity. There are two orbits under horizontal and vertical reflection,
represented by the column words

```
56,45,34,23,2,12,1,2,3,14,25,367,17
567,45,34,23,2,12,1,2,3,14,25,37,17
```

Each word and its three nontrivial rectangular-board reflections is a distinct
maximum blackout. There are no others. Rotating a 7 by 13 board by ninety degrees
changes its dimensions and is not included in this count.

## Complete row-core reduction

The complete excess-ten classification has 2,664 row-core classes modulo vertical
reflection. Every remaining column is allowed to choose any singleton row, and
all column orders are free up to one horizontal-reflection anchor.

| Core type | Reflection classes |
|---|---:|
| Ten double columns, no empty column | 1,497 |
| Eleven double columns and one empty column | 210 |
| One triple column and eight double columns | 957 |

For a 23-point board, the excess is `10+z`, where `z` is the number of empty
columns. A column of size at least four is impossible by the large-column bound.
A triple forces `z=0` and equality in the excess-ten large-column classification:
there is exactly one triple. If there is no triple, at most one empty column is
possible, giving the first two families.

The companion verifier regenerates these cores independently. For the double-only
families it enumerates all triangle-free row graphs with ten or eleven edges.
For the triple family, choose its three rows and a complete bipartite `K_(2,2)`
on the other four rows. Each outside row attaches to one triple row, and adjacent
outside rows must attach to different triple rows to avoid a three-column axis
six-cycle. There are eighteen such attachment maps for each of the three
partitions of the four outside rows. This gives `35*3*18=1890` labeled triple
cores and 957 reflection classes. The regenerated catalog agrees with the full
stored catalog, including all row labels and empty-column flags.

Completed earlier searches exclude every core except indices 996, 998, and 999.
The only previously unchecked double-only case, index 997, was separately
proved UNSAT. Thus the new enumeration needs only those three triple cores.

## Projected enumeration and symmetry accounting

`count_seven_thirteen_optima.py` enumerates black point assignments, not full
assignments to SAT auxiliaries. After a model with black set `B` is found, it adds
the clause saying that at least one point of `B` must be white. Every model in
that core has exactly 23 black points, so this blocks exactly that black set and
all its auxiliary extensions. It cannot block a different 23-point blackout.

The compact geometric encoding gives:

| Core index | Anchored black point assignments |
|---:|---:|
| 996 | 1 |
| 998 | 0 |
| 999 | 1 |

This enumeration terminates with UNSAT after its listed models, so these are
exhaustive projected counts. The complete-rectangle presentation-fiber encoding
independently gives the identical two point assignments and the same final
UNSAT statuses. The compact run took approximately 5.05 seconds; the fiber run
took 51.875 seconds.

For both surviving assignments, the fixed anchor pair `12` lies in column six.
The width-13 symmetry cut permits columns one through seven. Horizontal
reflection moves this pair to column eight, so exactly one member of each
horizontal pair appears in the anchored search. Each row core has a distinct
vertical reflection. Consequently each of the two anchored assignments gives
four labeled boards, for a total of eight.

No multiplier for repeated singleton rows is needed. Their positions and row
choices are already part of each point assignment. The verifier explicitly
expands both reflection orbits, checks that all eight point sets are distinct,
and verifies 23 black points and 2,333 distinct rectangle presentations for each.
It also checks that the equal-diagonal and perpendicular-side rectangle generators
agree.

## Audit artifacts and scope

The complete projected runs are in
`seven_thirteen_optimum_count_compact.json` and
`seven_thirteen_optimum_count_fiber.json`. The independent catalog, coverage,
symmetry, and geometric checks are implemented in
`verify_seven_thirteen_optimum_count.py`; its saved output is
`seven_thirteen_optimum_count_check.json`. That output lists all eight column
words and records hashes of the source result files.

This is a computer-assisted exact count. Its mathematical reduction and symmetry
factors are explicit; the remaining finite inputs are completed SAT exclusions
and projected enumeration termination. No asymptotic counting claim follows
from this one finite value.
