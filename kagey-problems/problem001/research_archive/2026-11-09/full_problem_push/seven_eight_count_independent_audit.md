# Source audit of the independent seven-by-eight count

9 November 2026. The source logic in independent_seven_eight_count.py and verify_seven_eight_independent.py passes review.

Equal-length diagonals with a common midpoint enumerate every rectangle. Distinct diagonal pairs in one group have four distinct endpoints, and deduplication by the four-cell mask removes repeated descriptions. The independent verification uses the perpendicular-vector generator and obtains the same 866 rectangles.

For intersecting rectangles, equality of presentations is equivalent to their symmetric difference being black. The four- and six-cell clauses impose exactly these exclusions. Disjoint rectangles can share a presentation only when both are hidden. Hidden-rectangle clauses are valid on this board: reflection and subdivision exclude all shapes except a possible unit diamond, and in dimensions at least four a unit diamond admits an additional parallel side inside the board, producing a same-side collision.

The exact-cardinality constraint makes blocking only the sixteen positive cell variables a valid projected-model blocker. It removes precisely that black-cell set, regardless of auxiliary assignments. Every returned model is also checked by direct presentation enumeration.

The auxiliary bounds are necessary. A column with at least five cells violates the large-column excess bound at sixteen total cells; transposing gives the row bound of five. Removing a boundary column leaves a seven-by-seven board with at most fourteen cells, so each boundary column has at least two. Removing a boundary row leaves a six-by-eight board with at most fifteen cells, so each boundary row is nonempty. The remaining listed contiguous crops use established bounds.

The verifier uses only completed mask records, checks duplicate records for exact equality, and expands vertical reflections exactly. First-column masks of weight below two or above four are excluded analytically. It explicitly computes missing masks among all 128 possibilities and reports an exact count only when none remain. Board sets from different first-column masks are disjoint by definition. The saved result also compares the complete recovered set with the earlier eighteen boards.

This is an independent encoding, exhaustion, and geometric verification. The stated qualification that the SAT exhaustion has no separate DRAT certificate remains appropriate.
