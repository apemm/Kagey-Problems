# Independent audit of the global vertical-rival color graph

9 November 2026. The three claims in [Global P-coloring progress](global_P_coloring_progress.md) pass an independent audit. Their scope is only the vertical-rival constraints for the stated scaffold.

For the upper bound, a conflict oriented from its odd-row source gives an integer right triangle with even horizontal leg, odd vertical leg, and hypotenuse at most \(h-1\). Thus the usual primitive parameterization has no extra leg-order factor. Each triangle allows at most four sign choices for the target coordinates. Adding the same-odd-row clique gives the stated outdegree, and the same bound applies in every induced subgraph. The degeneracy argument therefore proves \(O(h\log h)\) colors.

For the fixed-affine obstruction, the chosen \(d\) makes \(\alpha d/\beta\) an even multiple of \(M\). Consequently both even-row coordinates have the correct parity and agree modulo \(M\); the odd coordinates do also. The two affine values agree exactly. The explicit \(a,h\) keep every row positive and put both white rows \(a-d^2,a+1\) in the strip. The case \(\beta=0\) fails already on a same-odd-row clique.

For the joined-clique construction, the \(3^t\) absolute differences
\[
 |4q^2/u-u|,\qquad u\mid q^2,
\]
are all distinct. Equality with the same sign follows only from equal \(u\), because the signed expression is strictly decreasing. Equality with opposite signs would require \(uu'=4q^2\), impossible for odd divisors \(u,u'\). The two signs give \(2\cdot3^t\) distinct even rows, and every indicated white row lies between one and \(8q^2+6\). The constructed clique therefore has exactly the asserted \(n+2\cdot3^t\) vertices.

The lower bound excludes \(n+O(1)\) colors, while the upper bound gives \(O(h\log h)\). Neither implies or excludes an \(O(h)\) palette, and neither addresses the remaining rectangle constraints.

## The subsequent linear-palette theorem

The stronger argument in [Global P linear coloring](global_P_linear_coloring.md) also passes an independent proof audit. It resolves the palette question left open above: the strengthened vertical-rival graph has chromatic number \(O(h)\).

For the Pell estimate, dividing by \(\gcd(X,Y)\) makes \(Y_0\) invertible modulo the nonzero norm. Two solutions with the same root modulo that norm have a quotient in \(\mathbb Z[\sqrt5]\) with norm one. Their positive real embeddings lie in a polynomially bounded interval, so each unit orbit contributes \(O(\log h)\) solutions. The modulus-five and modulus-two exceptions in the root count are covered by the stated constant. The fixed-row-pair factorization gives the required uniform subpolynomial multiplicity.

For a single band, conditioning on inclusion of the clique's own row leaves all blocker indicators independent. Pairwise disjoint blocker sets therefore give independent avoidance events. The intersection-graph degree is bounded by the product of blocker size and within-clique blocker multiplicity. Its subpolynomial bound justifies the \(h^{1/32}\) denominator uniformly. The two Hall regimes work as stated: individual eligibility handles small subsets, and large subsets have a neighborhood with mean at least \(32N\). The failure probability \(e^{-4N}\) is enough for the union over at most \(h2^N\) row-subset choices.

Eligibility also handles conflicts in either direction between cliques: if two eligible vertices share a color, each of their own rows belongs to that color's selected row set, while neither can belong to the other's blocker set. Separate matchings remove all same-row conflicts.

Finally, the small-band orientation points from the odd-row source into the vertex defining its blocker. For each offset, the possible targets are counted by \(D(u)\); this direction is essential to the claimed outdegree bound. Summing small bands costs \(h^{1/3+o(1)}\), and the total weighted mass of large bands is \(O(h)\).

The quadratic-width consequence is therefore justified for vertical rivals. The proof does not remove three-black tilted rectangles or the other mixed supports of the full construction.
