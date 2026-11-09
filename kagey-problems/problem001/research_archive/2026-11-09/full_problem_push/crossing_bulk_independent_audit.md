# Independent audit of the span-weighted interface bound

9 November 2026. protected_crossing_bulk_weight.md passes independent
review. The total protected four/six event weight crossing one cut
is \(O(h(1+\log h)^2)\).

The primitive rectangle parametrization gives
\(D(W)=O(h^2\log^2h)\) and
\(S(W)=O(h^4)\). Dropping the joint vertical-span restriction
only enlarges the count. Summing each horizontal component over
the two scale variables yields
\(O(h^3(a^{-2}+b^{-2}))\), whose double sum is \(O(h^4)\).
The finite orientations and possible choices of corner contribute
only constants.

The horizontal mixed case is also controlled: its sum of diagonal
lengths is \(O(\sigma(v^2))\), and
\(\sum_{v\le h}\sigma(v^2)=O(h^3)\).
Writing a divisor as \(ab^2\) with \(a\) squarefree proves the
latter estimate through the convergent sum
\(\sum a^{-2}b^{-3}\).

For the oblique mixed case,
\(r_2(k^2N)\le r_2(N)R(k)\), with
\(\sum_{k\le K}R(k)=O(K\log K)\).
Summing the three span terms over the connector and side scales
gives exactly
\[
 h^4\!\sum_{(a,b)=1}r_2(a^2+b^2)\log(2h/b)
       (a^{-2}+b^{-2}+(ab)^{-1}).
\]
The fixed-\(a\) divisor-hyperbola estimate is uniform: coprimality
makes \(a\) invertible modulo every divisor, leaving at most
\(\varrho(d)\) residue classes. Its summatory bound is
\(O(B\log(2(a+B))+a+B)\).
Partial summation gives the required
\(O((h+a)\log h)\) weighted bound. The displayed double sum
therefore gives \(O(h^5\log^2h)\), as claimed.

For six cells, the union span is at most the sum of the two
rectangle spans. Thus \(2D(W)S(W)\), summed over the root row,
is a valid upper bound. Non-genuine repeated-column configurations
need not be assigned event probabilities; omitting them only
decreases the count.

The conditional local lemma then gives the exact cross-cut
partition-function inequality. Period padding is used at the
partition-function level, not as an assertion that every individual
prefix extends. The full changed-row family loses at most
\(O(rh)\) mean at the ends because each root rectangle loses
at most its span in horizontal placements.

The resulting domain-density comparison has the stated range.
The local wall penalty \(ch\) is still smaller than the available
upper bound \(Ch\log^2h\) on the old bulk cut cost, so these
bounds do not determine the sign of the relative interface free
energy or prove general canonical dominance.
