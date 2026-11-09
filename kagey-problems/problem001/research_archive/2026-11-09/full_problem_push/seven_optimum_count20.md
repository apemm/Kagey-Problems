# The exact optimum count at seven rows and twenty columns

9 November 2026. A completed projected enumeration gives
\[
\boxed{f(7,20)=31,\qquad a_7(20)=3364.}
\]
The optimum size was already established by
[the seven-row threshold proof](seven_row_equality_width_exclusions.md).
The new calculation determines its multiplicity.

## Complete analytical reduction

For a 31-point board on twenty columns, write \(z\) for the number
of empty columns. The row-tree excess is \(11+z\), while Mantel's
bound is twelve. Hence \(z\in\{0,1\}\).

The near-bound classification excludes triple or larger columns:
at seven rows, any such column limits the intrinsic excess to ten.
The double graph is also bipartite, because a nonbipartite
triangle-free graph on seven vertices has at most ten edges.
Thus the only possibilities are:

* Eleven distinct double pairs, no empty column, and singleton
  columns elsewhere. Their graph is \(K_{3,4}\) with one edge removed.
* All twelve pairs of a \(K_{3,4}\), one empty column, and singleton
  columns elsewhere.

There are 420 labeled eleven-edge graphs and 35 labeled twelve-edge
graphs. Vertical reflection reduces these to 210 and 19 classes,
respectively, for a total of 229 row cores.

## Projected enumeration and symmetry

[count_seven_excess_eleven.py](count_seven_excess_eleven.py) uses the
fixed-row-core encoding and enumerates actual black-cell sets.
After each model, the clause containing the negatives of all its
black-cell variables blocks that projected board. Every model has
the same fixed size, so this excludes exactly that black set among
the feasible projected solutions, regardless of auxiliary-variable
assignments.

Each core has a distinguished smallest row-pair mask, which occurs
in exactly one column. Requiring its column to lie in the left half
of the even-width board chooses exactly one of each pair of
horizontal reflections. The horizontal weight is therefore two.
The vertical weight is one for a reflection-invariant core and two
otherwise.

All 229 cores have completed enumeration records. Time-limited
attempts are excluded from the total. Duplicate completed attempts
must agree in both projected model set and count.
The completed records contain 843 projected models, with total
reflection weight 3364.

The sliding-window restrictions use the already established
optimum upper bounds at widths nine through nineteen. Each is
necessary because restricting a valid blackout to consecutive
columns preserves validity.

## Independent verification

[verify_seven_optimum_count20.py](verify_seven_optimum_count20.py)
constructs the core catalog independently by enumerating every
triangle-free graph with eleven or twelve edges on seven vertices.
It then:

1. Matches every completed record to that independent catalog.
2. Expands horizontal and vertical reflections and verifies that
   the weighted total equals the number of distinct resulting boards.
3. Generates all rectangles independently from pairs of equal-length
   diagonals with the same midpoint.
4. Checks that the presentations of all 5,280 rectangles are distinct
   on every one of the 3,364 boards.
5. Checks every stated sliding-window bound on every board.

The saved
[verification record](seven_optimum_count20_independent_check.json)
has status PASS, no missing cores, and the full board list with
source hashes. The upper count relies on the completed SAT
enumerations; this run does not include a separate DRAT proof
of each final exhaustion.

The encoding, completeness reduction, projection, and symmetry accounting
also passed a separate
[independent audit](seven_optimum_count20_independent_audit.md).
Its fresh verifier execution reproduced the same complete count.

The result is consistent with the sharp change at the equality
threshold: the preceding width has 3,364 optima of size 31, while
[width twenty-one](seven_equality_count21_independent_audit.md)
has exactly four optima of size 33.

