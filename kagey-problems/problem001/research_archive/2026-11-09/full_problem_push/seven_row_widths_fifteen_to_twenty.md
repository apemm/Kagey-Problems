# Exact seven-row values from width thirteen onward

9 November 2026. The completed checks give
\[
\begin{array}{c|rrrrrr}
m&15&16&17&18&19&20\\\hline
f(7,m)&25&26&27&29&30&31.
\end{array}
\tag{1}
\]
Together with the earlier
[width-thirteen result](seven_thirteen_exact.md),
[width-fourteen result](seven_fourteen_exact.md), and the
[equality threshold](seven_row_equality_width_exclusions.md), this gives
\[
\boxed{f(7,m)=
\begin{cases}
m+10,&13\le m\le17,\\
m+11,&18\le m\le20,\\
m+12,&m\ge21.
\end{cases}}
\tag{2}
\]
The last line uses the [infinite-tail certificate](seven_row_equality_tail.md),
so it covers every larger width, not only a finite collection of witnesses.

## Complete classification at target \(m+11\)

Suppose a valid seven-row board has \(m+11\) black cells, and let z be its
number of empty columns. Its excess over its nonempty columns is \(11+z\).
The large-column bound gives excess at most 10 when a column contains at
least three black cells. Thus every nonempty column here is a singleton or
a double.

The double pairs form a simple triangle-free graph on the seven rows. A
repeated pair would create an axis 4-cycle; a triangle would create an axis
6-cycle. Its edge count is \(11+z\), so Mantel's theorem gives \(z\le1\).

A nonbipartite triangle-free graph on seven vertices has at most ten edges.
Indeed, a shortest odd cycle of length five has five edges; each of the two
remaining vertices has at most two neighbors on it, and there is at most
one edge between them. If the shortest odd cycle has length seven, any
chord creates a shorter odd cycle, so the graph is just the 7-cycle.

Consequently the double graph is bipartite. Eleven edges require a balanced
3-by-4 bipartition: all other bipartitions have at most ten edges. The only
possibilities are therefore

- eleven distinct doubles forming \(K_{3,4}\) with one edge removed, no
  empty column, and \(m-11\) singleton columns;
- all twelve doubles of \(K_{3,4}\), one empty column, and \(m-13\)
  singleton columns.

There are 420 and 35 labeled row graphs in the two cases. Vertical reflection
reduces these to 210 and 19 representatives, respectively. These are the
229 cores used by the exact searches. An independent enumeration of all
triangle-free eleven-edge and twelve-edge graphs reconstructs the catalog.

For an eleven-edge core, the fixed axis pair set contains exactly its eleven
actual edges. The absent balanced-completion edge is not added. In
particular, the stronger fourteen-column bound for a complete final pair set
cannot be used here.

## Exact encoding and completed exclusions

`seven_row_deficit_one_sat.py` uses the existing fixed-core encoding with
every double owner occurring once. All singleton choices and orders are
allowed. One specified double is placed in the left half only to remove
horizontal reflection. The geometric clauses use the actual complete set
of axis pair owners for that core.

The initial crop bounds are
\[
(9,17),(10,18),(11,20),(12,21),(13,22),(14,24).
\]
The thirteen-column bound 22 applies because these boards have no triple
columns. The fourteen-column bound is the ordinary bound 24. After the
width-15 proof finishes, the stronger runner also uses \((15,25)\).
After the width-16 proof finishes, the final continuation uses \((16,26)\)
only at widths at least 17.

The complementary runner writes the same crop restrictions in a second,
equivalent form. Let \(D_j\) and \(E_j\) indicate a double and an empty
column. The whole board has excess \(\sum_j(D_j-E_j)=11\). Therefore an
L-column crop with black upper bound B forces
\[
 \sum_{j\text{ outside the crop}}(D_j-E_j)\ge11+L-B.
\]
For a core with an empty column, the encoder uses \(D_j+(1-E_j)\) and adds
the outside length to the right side. These are logical consequences of the
existing exact total and crop bounds. They improve propagation without
restricting the family. In particular, at width 17 the two endpoint columns
must be doubles, by the certified width-16 bound.

At width 15, the pilot completed 143 cores as UNSAT. Its one interrupted
case was not counted. The continuation completed the other 86 cores as
UNSAT. Their union covers all 229 indices, proving that 26 black cells are
impossible. The 25-point witness in the next section proves
\(f(7,15)=25\).

At width 16, the first pass completed 111 cores as UNSAT, and the continuation
completed the remaining 118. The combined checker verifies all 229
exclusions and the 26-point witness, proving \(f(7,16)=26\). The two bounded
runs took 600 and 586.984 seconds, respectively; the first pass's partial
case was rerun and completed in the continuation.

At width 17, six bounded files have disjoint completed UNSAT sets of sizes
26, 71, 46, 5, 65, and 16. Their union is again all 229 cores. The tags in
`deficit_one_h7_w17_<tag>_cadical195.json` are, respectively, `pilot`,
`stronger`, `final`, `complement_hard`, `complement_finish`, and
`complement_last`. Interrupted cases were rerun; none remains unresolved.
The final 16-core continuation took 127.016 seconds. The checked 27-point
witness proves \(f(7,17)=27\).

The SAT searches at widths 18 and 19 supply 29-point and 30-point witnesses.
Their matching upper bounds follow from the complete equality exclusions
below width 21. The width-20 result follows in the same way from its
31-point cropped equality witness.

`verify_seven_row_deficit_one.py` checks the catalog, recorded source hashes,
crop-bound dependencies, completed core coverage, and every SAT witness.
Unknown and interrupted runs never contribute an exclusion. The output is
`seven_row_deficit_one_check.json`. The UNSAT results use completed exact
solver calls; this record does not include a separately checked formal proof
trace.
Separate independent audits in `seven_row_width16_independent_audit.json`
and `seven_row_width17_independent_audit.json` reconstruct the catalogs,
confirm the disjoint completed coverage and all source hashes, and verify
the lower witnesses with both rectangle generators.

## Explicit lower witnesses

Each comma-separated entry lists the black rows in one column.

| Width | Black cells | Column word |
|---|---:|---|
|15|25|`1,1,123,34,45,56,6,67,7,6,5,47,36,15,17`|
|16|26|`1,1,1,123,34,45,56,6,67,7,6,5,47,36,15,17`|
|17|27|`1,1,1,1,123,34,45,56,6,67,7,6,5,47,36,15,17`|
|18|29|`56,45,34,23,1,1,14,12,2,27,7,7,1,47,2,25,16,67`|
|19|30|`47,67,25,1,36,12,1,1,16,1,2,1,14,1,1,23,34,45,56`|
|20|31|`36,5,25,2,2,14,7,12,27,2,7,67,7,47,7,7,56,45,34,23`|

The checker independently generates all rectangles by equal diagonals and
by perpendicular sides, compares the two sets, and verifies that every
rectangle has a distinct white presentation. The checks at widths 15 through
19 contain 3,070, 3,470, 3,891, 4,333, and 4,796 presentations, respectively.

The first three witnesses come from the same 13-column, 23-point core by
prepending row-1 singletons. A separate checked 20-singleton prefix also
proves that this core admits arbitrarily long constant-row-1 prefixes.
The height-seven tilted span is ten and the two-tilt support span is twenty.
Any new collision farther left therefore lies entirely in the constant
boundary sea, while all axis pair owners remain unchanged in the fixed core.
Thus this construction gives the additional uniform lower bound
\(f(7,m)\ge m+10\) for every \(m\ge13\).
