# The exact seven-row equality threshold is 21

9 November 2026. **The seven-row equality threshold is exactly 21.**
Complete exact SAT checks exclude widths 17, 18, 19, and 20. Earlier bounds
exclude every smaller width. The explicit tail in `seven_row_equality_tail.md`
constructs equality at every width from 21 onward. Thus

\[
m_0(7)=21,\qquad f(7,m)=m+12\quad(m\ge21),\qquad f(7,20)=31.
\]

The structural reduction,
the cropped constraints, and the coverage verification are described below.
The remaining computational input is the exact solver's completed UNSAT
output; these runs do not contain independently checked proof logs.

## Complete row-core classification

An equality board of height seven and width `m` has `m+12` black cells. Every
column is a singleton or double, and the twelve distinct double pairs form
one complete balanced bipartite row graph `K_(3,4)`. There are 35 labeled row
graphs. Vertical reflection fixes three of them, giving 19 reflection classes.

For each class, the SAT instance places each of its twelve double types
exactly once. Every remaining column chooses any of the seven singleton rows.
The point variables are equivalent to these column choices. One fixed double
is required to lie in the first half, which loses no board because horizontal
reflection preserves validity. The first half includes the middle column
when the width is odd.

Thus the 19 instances cover every equality board at the chosen width. No sea
parity restriction or prescribed double order is imposed.

## Geometry and cropped bounds

The exact compact geometry compiler uses the full final row graph in every
axis-rival test. Its positive supports exclude hidden tilted rectangles,
tilted/axis collisions, and tilted/tilted collisions. The no-hidden theorem
applies because both dimensions are at least four. The support-feasibility
filter uses the actual distinct double owners; here these are exactly all
edges of the final graph.

Every fitting contiguous window receives the following black-cell bound:

| Window width | Black-cell bound | Reason |
|---:|---:|---|
| 9 | 17 | Exact unrestricted value |
| 10 | 18 | Exact unrestricted value |
| 11 | 20 | Exact unrestricted value |
| 12 | 21 | Exact unrestricted value |
| 13 | 22 | Valid boards with at most two black cells per column |
| 14 | 23 | Final-row-graph equality windows have at most nine doubles |

The final two bounds are proved and independently checked in
`equality_window_capacity.md`. The width-14 bound is specific to a window in
an equality board: it uses row pairs whose owners may lie outside that
window. Those pairs are guaranteed by the complete final graph. This does
not assert the unrestricted bound `f(7,14)<=23`, which would be false.

Because every column is nonempty and has at most two black cells, a window
of length `k` contains exactly `k` plus its number of doubles black cells.
The cardinality constraints in `fixed_row_core_sat.encode` therefore translate
the displayed bounds directly into double-column caps.

## Completed checks

`seven_row_equality_threshold_sat.py` runs each row core in a separate bounded
process, records each result, and distinguishes an interrupted instance from
UNSAT. The individual caps were 45 seconds at widths 17 and 18, 90 seconds
at width 19, and 120 seconds at width 20. Every instance completed within
its cap.

| Width | Equality target | Completed UNSAT cores | Total elapsed time |
|---:|---:|---:|---:|
| 17 | 29 black cells | 19 of 19 | 27.422 seconds |
| 18 | 30 black cells | 19 of 19 | 111.344 seconds |
| 19 | 31 black cells | 19 of 19 | 230.031 seconds |
| 20 | 32 black cells | 19 of 19 | 603.391 seconds |

The results are stored in `equality_h7_w17_0_19_cadical195.json`,
`equality_h7_w18_0_19_cadical195.json`,
`equality_h7_w19_0_19_cadical195.json`, and
`equality_h7_w20_0_19_cadical195.json`. Every record includes the source hashes,
row cores, cropped bounds, solver statistics, and completed status.

`verify_seven_row_equality_threshold.py` independently enumerates every
triangle-free twelve-edge graph on seven labeled vertices. It obtains 35
graphs and checks that their reflection quotient is exactly the searched
19-core list. It also checks all consecutive result indices, every UNSAT
status, all recorded source hashes, the target dimensions, and the cropped
bounds. Its saved output is `seven_row_equality_threshold_check.json`.
The runner and the final-graph crop semantics received a separate code audit.

The earlier equality-window theorem already excludes all widths below 17.
The four complete new runs therefore establish the lower bound 21.
Equivalently, the equality value is not attained at these widths, so
`f(7,17)<=28`, `f(7,18)<=29`, `f(7,19)<=30`, and `f(7,20)<=31`.
The first three statements do not determine the exact extremal values at
those widths. At width 20 the upper bound is sharp: crop the first double
column from the 33-point width-21 witness to obtain the valid 31-point word

```
36,5,25,2,2,14,7,12,27,2,7,67,7,47,7,7,56,45,34,23
```

The separate explicit tail construction in `seven_row_equality_tail.md`
proves equality for every width at least 21. The finite-width exclusions and
that all-width upper construction settle both the first equality width and
the eventual-equality threshold. No monotonicity assumption about equality
widths is needed.
