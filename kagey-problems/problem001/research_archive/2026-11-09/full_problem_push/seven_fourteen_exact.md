# The exact value on the seven-by-fourteen board

9 November 2026. **\(f(7,14)=24\).** The lower bound is an explicit witness. The upper bound uses a complete structural classification followed by 229 exact SAT checks.

## Witness and preliminary upper bound

The column word
\[
7,\ 56,\ 45,\ 34,\ 23,\ 2,\ 12,\ 1,\ 2,\ 3,\ 14,\ 25,\ 367,\ 17
\]
has 24 black points and distinct presentations for every rectangle. `verify_seven_fourteen.py` checks the witness using both equal-diagonal and perpendicular-side rectangle generators.

The boundary-cropping recurrence and \(f(7,13)=23\) give
\[
f(7,14)\le\max(14+12-3,\ f(7,13)+2)=25.
\]
It remains to exclude exactly 25 black points.

## Complete classification of 25-point candidates

Let \(z\) be the number of empty columns. The total column excess is
\[
e=25-(14-z)=11+z.
\]
The large-column theorem bounds this excess by 10 whenever a column has at least three black points. Thus every nonempty column is a singleton or double. Its distinct double pairs form a triangle-free graph on the seven rows. The number of double columns equals \(e\), so Mantel's bound gives \(11+z\le12\). There are only two cases:

| Empty columns | Double columns | Singleton columns | Row graph |
|---:|---:|---:|---|
| 0 | 11 | 3 | \(K_{3,4}\) with one edge removed |
| 1 | 12 | 1 | \(K_{3,4}\) |

For completeness, a triangle-free nonbipartite graph on seven vertices has at most ten edges. If it contains a five-cycle, each of the other two vertices meets at most two cycle vertices; the five cycle edges, four possible attachments, and one edge between the remaining vertices total at most ten. A chord of the five-cycle would make a triangle. If there is no five-cycle, a shortest odd cycle has length seven. Every chord of that cycle makes a triangle or a five-cycle, so the graph then has only seven edges.

An eleven-edge bipartite graph on seven vertices must have part sizes three and four: the other possible products are at most ten. It is therefore \(K_{3,4}\) minus one edge. There are \(\binom73\cdot12=420\) labeled graphs. The twelve-edge case has \(\binom73=35\) graphs. After vertical reflection these yield 210 and 19 classes, respectively, for 229 cores.

`verify_seven_fourteen.py` independently enumerates all triangle-free graphs with eleven or twelve edges, without assuming they are bipartite. It obtains exactly these 420 and 35 graphs and matches the entire 229-core catalog.

## Exact ordering checks

`fixed_excess_eleven_sat.py` places every edge of a chosen core exactly once, puts its prescribed empty column exactly once when present, and lets every remaining column choose any singleton row. All column orders remain free, up to placing one fixed double in the first half by horizontal reflection.

Its point variables are equivalent to the chosen column masks. The fixed-row-graph compact geometry constraints in `compact_equality_sat.md` and `pair_owner_sat.md` exclude exactly the forbidden tilted presentations. The feasible-support filter discards a support only if it demands a nonexistent row pair, more rows than that pair's unique owner column contains, or the same owner column in two distinct positions.

The following established subboard bounds are added to every fitting contiguous window:
\[
f(7,9)=17,\quad f(7,10)=18,\quad f(7,11)=20,\quad
f(7,12)=21,\quad f(7,13)=23.
\]
No width-14 bound is used within the SAT instances. The window cardinality constraints count one point per nonempty column, one extra point per double, and the appropriate correction for an empty column.

All 229 instances return UNSAT in 150.797 seconds total. `fixed_core_h7_w14_0_cadical195.json` records the full consecutive index range 0 through 228. The coverage checker checks every index, the status of every instance, the independently generated row-core catalog, and the 24-point witness. It records a hash of the completed run in `seven_fourteen_exact_check.json`.

The upper bound is computer-assisted. The complete structural reduction and exact SAT equivalence are mathematical; the finite UNSAT checks supply the remaining step.

## Consequence for the equality threshold

Any seven-row equality board has \(m+12\) black points and at most two black points in each column. Hence \(m\ge12\). The exact values at widths 12 and 13 exclude those widths, so an equality width has \(m\ge14\). Cropping to fourteen columns then gives
\[
m+12\le f(7,14)+2(m-14)=24+2m-28,
\]
and therefore **\(m\ge16\)**.

The separate final-row-graph window argument in `equality_window_capacity.md` strengthens this to \(m\ge17\). That improvement uses extra information inherited from an equality board, beyond the unrestricted value \(f(7,14)=24\).
