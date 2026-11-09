# Independent exact count for the seven-by-eight grid

9 November 2026.

There are exactly
\[
 f(7,8)=16,\qquad a_7(8)=18
\]
on the labeled grid. The optimum 16 was already established. The earlier repository enumeration stored eighteen boards, but its single completed method was recorded conservatively as a lower bound. A second enumeration now covers every first-column mask and recovers exactly the same eighteen boards.

## Encoding and coverage

[independent_seven_eight_count.py](independent_seven_eight_count.py) generates the 866 rectangles by pairing equal-length diagonals with a common midpoint. It forbids every four- or six-cell symmetric difference of intersecting rectangles and every hidden rectangle. There are 58,074 distinct forbidden supports. At these dimensions the proved no-hidden-rectangle theorem makes this equivalent to distinct rectangle presentations: a collision between disjoint rectangles would hide both rectangles.

The encoding imposes exactly sixteen black cells. It also uses previously established necessary bounds on contiguous subboards of dimensions \(7\times7\), \(6\times8\), \(6\times7\), \(6\times6\), \(5\times6\), \(5\times7\), \(3\times8\), and \(7\times3\). The large-column bound permits at most four black cells in a column and at most five in a row. Cropping the first or last column forces at least two black cells there; cropping the first or last row forces at least one.

Projected enumeration blocks only the sixteen selected grid variables, so auxiliary cardinality assignments do not create multiple counts. All 128 first-column masks are covered by completed direct searches, vertical reflections of completed searches, or the proved boundary and large-column exclusions. There are 100 completed direct masks. Repeated completed searches agree exactly.

Some early completed shards used the same forbidden-support encoding with fewer redundant crop and boundary constraints. The final script includes the stronger necessary constraints. Both versions enumerate the same target class; the weaker version only makes a search harder.

## Independent verification

[verify_seven_eight_independent.py](verify_seven_eight_independent.py) checks the coverage and reflection maps, expands all projected models, checks their cardinality and first-column masks, and regenerates all rectangles using the repository's perpendicular-side-vector generator. For every board it checks that all 866 actual visible rectangle presentations are distinct.

The resulting board set agrees with the eighteen boards in the older enumeration. The [verification record](seven_eight_independent_check.json) contains every board, all coverage sources, and source hashes.

The enumeration, projected blocking, analytical mask exclusions, and complete reflection coverage also passed a separate [source audit](seven_eight_count_independent_audit.md).

This is an exhaustive computational count supported by two encodings and independent geometric verification. The solver exhaustion records do not include separate DRAT certificates.

