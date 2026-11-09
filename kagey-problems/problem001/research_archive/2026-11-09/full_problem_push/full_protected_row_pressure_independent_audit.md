# Independent audit of full protected-row leading pressure

9 November 2026. [full_protected_row_leading_pressure.md](full_protected_row_leading_pressure.md) passes independent review. The one-sided root construction resolves the guard-edge obstruction in the earlier assembly sketch. The theorem now compares all column phases for a fixed balanced protected row partition.

## Witnesses and guards

The far-block container estimate counts the union of all far-phase row words, with the prescribed final F. It therefore supplies an actual exp(-gamma h) deficit without an extra 2^h phase factor. The generic all-phase block estimate is equally applicable to the necessary restriction of a full sea word.

For two adjacent good blocks with different matched labels, the marked wall family uses only black cells in the first block and a wrong-class completion in the second. Deleting error columns loses O(epsilon_0 h) marked mean. The error-set entropy is 2h H_2(epsilon_0), and the finite label choices cost O(1). Thus epsilon_0 can be fixed sufficiently small to give a positive wall-witness deficit before the far-block constant gamma is chosen.

A maximal set of well-separated witness starts has disjoint witness units. Its fixed-radius expansions contain every witness, and merging gaps shorter than D adds only O(Dk) blocks. Outside the final guards, every block is good and adjacent labels are equal. The remaining intervals therefore have a single matched law. Counting selected witness units with their deficit and every other guard block with the generic union bound gives the stated guard count. For fixed D, the generic o(h) cost per block is absorbed. This order of choices avoids any comparison between gamma(epsilon_0) and a power of epsilon_0.

## One-sided roots and the common cap

With the completion row in the middle third, U=(4ka,4kb) and V=(4lb,-4la) are perpendicular and stay vertically inside the strip under the stated scale ranges. Their horizontal components have the same sign. After removing ka=lb, the three black columns are distinct and strictly on that side of the completion. Choosing the longer available horizontal direction and capping R by M/C keeps the entire geometry inside the good interval, including a root next to a guard edge.

The fixed-cell/completion-column count is unchanged: in the opposite role the scale equation becomes ka+lb=d, with the same one-parameter progression bound. The primitive mean, deleted-error mean, dyadic one-/two-assignment pressure, and uniqueness of three-assignment completion all remain valid. Root variables never enter the guards.

The capped maximal inequality is also valid. Its cap T is common to the whole interval. If a bad index i witnesses L_i*<min(L_i,T)/2 through j, then L_j<T and the capped weight at j equals its uncapped weight. The same decreasing-envelope distance sum charges at most O(epsilon_0^(3/4)) of the total weight. The resulting error activity is bounded by M exp(-c log²h)+C hM exp(-c log²M).

The second term depends on the whole interval length, not the distance from its guard edge. Since every remaining interval has M>=D, choosing fixed D sufficiently large makes this term arbitrarily small compared with gamma h per selected witness. This is the essential repair; merely widening a guard would not have sufficed for two-sided roots.

## Preservation of the leading coefficient

Within each good interval retain the original minimal protected bulk of span at most H_delta=C h^(2-delta), avoiding all error columns. Apply the protected Suen bound to this bulk first. Then apply the exact conditional lower-probability estimate to the rooted events. This ordering retains coefficient one on the bulk mean. The old compatible-extension estimates apply to the prescribed three black assignments, and guards and different intervals have disjoint variables.

The bulk deletion at an error column costs O(log⁴h/h), and the alphabet-size change costs O(1/h). The capped root weight per error is bounded below by a positive constant for fixed D and epsilon_0, so both costs are absorbed uniformly for large h. Common-corner colors do not need to be prescribed in the retained positive support events.

Truncation omits at most C delta log⁴h/h+o_delta(log⁴h/h) mean per column. Each good-interval boundary loses at most C H_delta log⁴h/h. Replacing protected pressure on the O(Dk) guard blocks by their generic baseline costs O(Dk log⁴h). For fixed delta>0 and fixed D, both per-witness costs are o(h), so the retained exp(-gamma hk) deficit absorbs them. This remains a valid upper estimate if there is little or no bulk: a negative lower estimate for the mean only weakens the avoidance bound.

Selected starts and types, together with the constant laws of the good intervals, have at most binomial(ceil(m/h),k) C^k descriptions. The remaining exp(-c gamma hk) deficit sums directly to an exponentially small per-block activity. A separate low/high witness-density split is unnecessary. The case k=0 is the one-law adaptive theorem; short end intervals and phase remainders cost only O_h(1) in the logarithm.

Taking h to infinity with delta fixed, and then delta to zero, proves log rho(c_0,h)=log rho_0(c_0,h)+o(log⁴h/h). The reverse inequality follows from inclusion of each protected phase. The explicit protected constants therefore give the corresponding leading full-shift constants, and the full quadratic row partition eventually has greater entropy than ordinary parity.

The audit does not establish a maximizing arbitrary balanced row partition, uniqueness of a maximal component, or insertion into every maximal component. Those conclusions are not asserted by the theorem.
