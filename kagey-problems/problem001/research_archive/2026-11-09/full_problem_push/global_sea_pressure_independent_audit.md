# Independent audit of the global leading sea coefficient

9 November 2026. [global_sea_leading_pressure.md](global_sea_leading_pressure.md) passes independent review. This audit uses the separately reviewed full protected-row assembly and checks the changes required for an arbitrary balanced partition at row distance o(h).

## Uniform witnesses and phase roots

The far-block estimate applies to the union of all actual phase words, not to one prescribed phase. The proof in Section 7 of near_maximal_partition_rigidity.md remains uniform when the actual balanced row coloring is o(h)-close to a protected reference: changing those rows alters only o(h⁴ log h) tests in the comparable-direction family. Container purification and the protected-row inverse then give the same fixed far-phase gap. The reference itself may have class-size imbalance O(1).

For each fixed wall or one-sided phase-root shape, the completion row has Theta(h) eligible translations. Prescribing any one exceptional corner row removes at most one translation. Deleting the entire E geometry therefore costs O(r/h) of the mean, uniformly in the primitive cutoff and interval cap. All surviving color relations, including the completion-row relation, hold for the actual partition. Their conditional extension bounds only decrease under these deletions.

## Old bulk and the additional row roots

Retaining full witnesses that avoid E is sufficient: all old row-pair relations and geometric collision certificates remain valid under the actual final F. The fixed-row support estimates include common white corners and bound the deleted mean by C_eta r h^(-2+eta) per column. Actual and reference allowed alphabet sizes differ by only O(1), even though their individual letters differ in r rows. For the absolute product-space proof, their logarithms differ by O(1/h), and probabilities of retained arity-at-most-six assignments differ by a relative O(1/h). An exact alphabet bijection is not needed for this step.

For bounded r these errors are o(log⁴h/h), so row roots can be omitted. For r tending to infinity, a constant reference phase has a positive fraction of eligible changed rows because the two directed changes differ by O(1). A nonconstant phase supplies the same fraction on average over its fixed period. Accordingly the row-root mean must be read as a period-averaged or interval mean, not as a lower bound at every individual column. The existing O(sqrt(rh)) end term absorbs this finite-period correction.

The row-root family has mean at least a(r/h)log²(h/r) per averaged column, one-/two-assignment pressure o(1), and span-weighted end loss O(sqrt(rh)). Deleting a phase-error column costs only C P_h raw mean: translation invariance of each shape, with its period at most four and bounded number of column roles, gives this bound directly. It is not the larger conditional one-cell bound.

Row roots complete on E, while phase roots complete on its complement. Three prescribed right-angle corners determine the unique fourth point, so cross-family three-assignment coincidences are impossible. Mixed one- and two-assignment sums are controlled by the separate uniform extension estimates. The joint unthinned criterion therefore holds. Since P_h tends to zero, the phase-root weight absorbs C P_h per error while retaining its profile-summation penalty.

## Guards, limits, and optimization

For fixed guard parameter D, the extra lost row mean per witness is O(D hP_h+sqrt(rh))=o(h). It is absorbed by the unchanged fixed witness deficit. The old-bulk deletion and alphabet errors are o(P_h) when r tends to infinity. The bulk-first, joint-roots-second ordering preserves coefficient one on the old protected mean. Truncation and all boundary costs are handled exactly as in the fixed-row theorem.

The row penalty has a coefficient independent of the fixed bulk truncation parameter. Taking h to infinity first and then that parameter to zero gives the stated near-protected bound, including its negative P_h term. Bounded and unbounded row-distance subsequences cover arbitrary sequences at distance o(h).

For a globally maximizing partition, the quadratic protected lower bound and partition rigidity provide an o(h)-close protected reference. An ordinary reference is incompatible with the strict protected ordinary/quadratic coefficient gap. A quadratic reference gives the matching global leading upper bound. If its distance were at least epsilon log²h on a subsequence, monotonicity of r log²(h/r) for r<h/e² would make the negative row penalty a fixed multiple of log⁴h/h, contradicting the quadratic lower bound. Thus the claimed o(log²h) distance conclusion follows.

The maximum-blackout exponential limsup is bounded above by the maximum sea spectral radius: fixed-height equality series have finitely many double markers and only sea eigenvalues as exponential bases. The balanced quadratic canonical capture and positive collared insertions supply the matching protected lower bound. This verifies the same leading coefficient for that limsup.

The resulting statements are R_h=h/2−(d_Q/2)log⁴h+o(log⁴h), the same expansion for the fixed-height maximum-blackout exponential limsup, and o(log²h) quadratic-row distance of maximizing partitions. They do not identify the exact maximizing partition at each height, a unique maximal component, or the polynomial factor and leading constant in width.
