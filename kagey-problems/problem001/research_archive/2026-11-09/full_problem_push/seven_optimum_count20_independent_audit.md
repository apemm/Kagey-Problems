# Independent audit of the width-twenty optimum count

9 November 2026. The completed enumeration supports
\[
 a_7(20)=3364.
\]
The structural catalog, projected model blockers, reflection weights, crop bounds, and independent geometric verifier pass review. A fresh execution of the verifier also returned `PASS`, with 229 completed cores, 843 projected models, and 3,364 distinct reflected boards. Its separate output is [seven_optimum_count20_audit_recheck.json](seven_optimum_count20_audit_recheck.json).

This is an exact computational enumeration using completed SAT records. No independently checked DRAT exhaustion certificate is claimed.

## Complete target family

The known optimum is \(f(7,20)=31\). A target board has excess eleven over its width. If it has \(z\) empty columns, its excess over its nonempty columns is \(11+z\).

The previously proved large-column bound limits that excess to ten whenever a column has at least three black cells. Thus every nonempty column is a singleton or a double. The double pairs form a simple triangle-free graph. Its edge count is \(11+z\), so Mantel's bound gives \(z\le1\).

A nonbipartite triangle-free graph on seven vertices has at most ten edges. A shortest odd cycle has length five or seven. In the five-cycle case, the two remaining vertices each have at most two neighbors on the cycle, and contribute at most one edge between themselves. In the seven-cycle case, a chord would create a shorter odd cycle. Therefore a graph with eleven or twelve edges is bipartite. Its bipartition must have sizes three and four, since the other bipartitions have capacity at most ten.

The complete possibilities are consequently:

- eleven doubles forming \(K_{3,4}\) with one edge removed, and nine singletons;
- twelve doubles forming \(K_{3,4}\), seven singletons, and one empty column.

There are 420 and 35 labeled row graphs. Quotienting by vertical reflection gives 210 and 19 representatives. The catalog in [fixed_excess_eleven_sat.py](fixed_excess_eleven_sat.py) enumerates these 229 cases. The independent verifier reconstructs the same catalog by testing every eleven-edge and twelve-edge graph on seven labeled vertices for triangles. It does not assume that the catalog generator's bipartite construction is complete.

## Encoding and crop bounds

[count_seven_excess_eleven.py](count_seven_excess_eleven.py) uses [fixed_row_core_sat.py](fixed_row_core_sat.py). Every column has exactly one allowed type. Each prescribed double occurs exactly once; in the second family, the empty type also occurs exactly once. The point/type equivalences are bidirectional. Hence every satisfying assignment has exactly 31 black cells, regardless of auxiliary-variable choices.

The compact geometric clauses use the actual eleven-edge or twelve-edge owner set. The missing edge of an eleven-edge balanced completion is not supplied as a virtual axis rival. The support feasibility test only removes conjunctions that cannot occur with these unique column owners. Hidden tilted rectangles, tilted/axis collisions, and the four-/six-cell symmetric differences of intersecting tilted rectangles are covered by the already audited compact encoding. Axis-only validity follows from the simple triangle-free row graph.

The runner uses the established ordinary crop bounds
\[
 (9,17),(10,18),(11,20),(12,21),(13,23),(14,24),
 (15,25),(16,26),(17,27),(18,29),(19,30).
\]
In particular it uses the ordinary width-fourteen bound 24, not the stronger final-pair-set bound 23. The width-thirteen bound is the valid ordinary bound 23. For an empty-column core, the encoded crop sum is
\(\sum(D_j+1-E_j)\), exactly the crop's black count. Without an empty column, it is \(\sum D_j\), with the crop length subtracted from the black-count bound. Thus the crop clauses do not exclude any board in the target family.

## Projected counting

After each model, the runner adds the clause consisting of the negations of its 31 true point variables. Since every model has exactly 31 black cells, this clause excludes exactly that black set. It excludes all of its auxiliary extensions and cannot exclude a different 31-point board. The loop therefore counts projected boards, not total satisfying assignments.

A record receives status `complete` only after the solver returns UNSAT under all accumulated blockers. Timeouts, errors, and model-cap exits have different statuses. The verifier counts only completed records, requires coverage of all 229 indices, and checks that duplicate completed records have identical projected model sets. Interrupted records do not supply exhaustion evidence.

## Reflection weights

One fixed double, the first mask in the core, is constrained to columns 1 through 10. It occurs exactly once. At even width twenty, horizontal reflection moves its column to the other half, so precisely one member of every horizontal pair satisfies the anchor. The horizontal weight is therefore two.

If vertical reflection changes the row core, its reflected boards belong to the omitted core representative, giving a further factor two. If the core is invariant, no extra vertical factor is used: the enumeration already includes all anchored boards with that core, including the needed vertical images after horizontal re-anchoring.

The independent verifier explicitly generates all four horizontal/vertical images of each projected model. It checks that the size of their union equals the weighted sum. This confirms the reflection accounting, including vertically invariant cores, rather than relying only on the weight formulas.

## Independent geometric check and coverage

[verify_seven_optimum_count20.py](verify_seven_optimum_count20.py) generates rectangles by pairing diagonals with the same midpoint and squared length. Distinct such diagonal pairs give four distinct corners of a nondegenerate rectangle, and every rectangle occurs this way. This construction is independent of the search's rectangle generator.

The fresh run reconstructed 5,280 rectangles. For each of the 3,364 boards, it checked that all 5,280 white presentations are distinct. It also checked the black count, the core, the empty-column count, every crop bound, and the reflected-board deduplication. All 229 catalog indices have completed records, with no missing cases.

These checks validate every listed board directly and confirm catalog and record coverage. Exhaustion beyond those boards uses the completed SAT searches and the reviewed encoding, as stated in the result file.
