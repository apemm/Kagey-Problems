# Independent audit of the disjoint-influence width barrier

9 November 2026. The proposition in [Full disjoint influence sets](disjoint_influence_width_obstruction.md) passes an independent analytical audit.

For an interior row \(r\), every positive divisor \(u\) of \((r-1)(h-r)\), except its possible square root, produces the stated three-black tilted rectangle. The two sea columns are distinct and nonzero, all four columns are distinct, and the completion stays in the strip. Reflecting horizontally supplies the negative offsets. Thus an edge containing \(r\) really contributes at least \(2d_r\) offsets to the full influence set.

For each parity edge, \(2\max(d_a,d_b)\ge d_a+d_b\). Each row belongs to \(h/2\) edges, so summing reduces the width bound to the elementary divisor sum. The estimate
\[
 \sum_{r=1}^h d_r\ge h\log h-O(h)
\]
has the correct leading coefficient, giving
\[
 m\ge \frac{h^2}{2}\log h-O(h^2).
\]

This conclusion uses both hypotheses explicitly: the full influence sets are disjoint, and their translates are contained in the finite board. It does not constrain constructions with compatible overlaps, smaller blocking sets, or different background alphabets, and is not a lower bound for the actual equality threshold.

The subsequent prime-height addendum also passes. If \(h-1=p\) is prime, then \(a\) and \(p-a\) are coprime. For coprime \(d,e\le p^{1/4}\), the congruences have at least \(p/(de)-2\) solutions in the stated interval. The union bound for common divisors leaves harmonic mass at least \((11/36)H_X^2\). The \(O(X^2)\) counting error and at most \(p-1\) square-factor exceptions are negligible. Hence the same method requires \(\Omega(h^2\log^2h)\) columns along infinitely many even heights, with exactly the same scope restriction.
