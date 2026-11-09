# Independent audit of the changed-row pressure estimate

9 November 2026. The argument in
[Changed-row relative pressure](changed_row_relative_pressure.md)
passes an independent audit under its stated class-size-preserving
hypothesis and common normalized-support convention.

The geometric counts are sufficient. With one corner and a second
corner's row fixed, adjacent-corner cases factor a nonzero vertical
difference, and opposite-corner cases choose two positive vertical
products with a fixed sum or difference. This gives
\(O_\epsilon(h^{1+\epsilon})\) rectangles uniformly, including equal
rows in the opposite-corner case. For two prescribed black points in
distinct columns, the completion lies on finitely many circles or
nonhorizontal perpendicular lines. Each changed row therefore
contributes only \(O(1)\) possibilities.

The rooted lower bound is uniform in the missing corner's height.
Use it as the lowest corner in the lower half of the strip and as
the highest in the upper half. Taking both side scales divisible
by four preserves every protected coordinate residue. The primitive
harmonic sum gives \(\gg h^2\log^2 h\) choices; repeated columns and
other corners on changed rows contribute lower-order losses when
\(r\le h^{1-d}\) and \(\epsilon<d\).

The retained bulk has exactly the same joint distribution in both
models, not merely the same individual event probabilities. In each
column, choose a bijection between the two equal-sized alphabets that
fixes every unchanged row and pairs the removed and inserted rows.
This bijection preserves every retained certificate. Including all
geometric and partition-dependent certificate rows in the exclusion
set is necessary for this argument and is part of the stated
definition.

The rooted event family has incident probability
\(O(r\log^2 h/h)=o(1)\). Conditioning on a root's three assignments
leaves compatible one-point overlaps of total probability
\(O_\epsilon(rh^{-1+\epsilon})\), and two-point overlaps of
\(O(r/h)\). The established bulk extension bounds are smaller.
Deduplication removes a distinct event with the same three
assignments. Thus the unthinned conditional local-lemma comparison
applies uniformly.

Finally, removing old certificates whose geometry meets the changed
rows costs \(O_\epsilon(rh^{-2+\epsilon})\) per column. This is
negligible compared with the newly forced
\(\gg r\log^2 h/h\) rooted pressure. The exact old partition function
can therefore be restored without an extensive bulk-error term.
The result strictly lowers the fixed-phase growth rate. It makes no
comparison with other phases that the changed partition may favor.

## Spatial changes and protected domains

Sections 6--8 also pass. The two rooted families have distinct completion
locations, so a shared three-assignment support cannot be counted as two
different events across families. The marked spatial-to-row and
row-to-spatial conditional sums are bounded by the existing geometric
kernel and the two-row count, respectively. The loss
\(O(|S|r\log^2h/h)\) in row-root mean is absorbed by the spatial penalty.
For the local-density variant, each fixed black point sees roots from at
most one \(2L\)-cluster. Cluster-dependent thinning therefore keeps the
same conditional bound. Neither argument allows an unrestricted dense
defect set.

The domain argument uses conditional LLL to restore cross-cut bulk
events, with cost \(O(L\log^4h/h)\) per cut. Quasi-supermultiplicativity
then bounds the finite-word count by its exact growth rate with that
boundary factor. The padding step is correctly stated as a lower bound
on extensions on average, rather than extension of every valid prefix.
The changed-row endpoint loss is \(O(rL\log^2h/h)\), including short
domains. Counting cuts and the four matched phase laws gives the
claimed strict inequality at the stated switching frequency.

## Unequal labeled class sizes

Section 9 passes with its separate one-row exception. For the retained
bulk, changed letters are interchangeable dummy symbols. Sequentially
deleting one such symbol per affected column costs at most
\(\exp(O(m/h))\), by the arbitrary-event conditional local lemma.
This compares exact retained-bulk counts even when the two balanced
partitions have their labeled class sizes reversed.

If the selected constant even class grows by one odd row \(r_0\),
the ordinary changed-completion three-point family has no roots.
The replacement vertical-pair family is valid. The displayed black
diagonal has the same midpoint and norm as the vertical pair on rows
\(r_0,r_0+2\sigma d\). Selecting \(r_0\) at the middle column changes
the rival to a singleton presentation and does not remove it.
Odd multiples of primitive Pythagorean triples yield
\(\Theta(h\log h)\) supports uniformly in \(r_0\).

For a fixed black row \(a\), the identity
\[
 (x'-x)^2=4(a-r_0)(b-r_0)
\]
forces \(b-r_0\) into one signed square class, giving only
\(O(\sqrt h)\) partner rows and at most two horizontal signs.
The conditional overlap is therefore \(O(h^{-1/2})\).
The resulting \(\log h/h\) penalty exceeds the \(O(1/h)\) alphabet
comparison cost. A black-root three-point argument would instead have
the previously identified \(\Theta(\log^2h)\) conditional clique and
would not justify this conclusion.

Sections 6--8 retain their original class-size-preserving hypotheses.
Section 9 removes that hypothesis for the fixed-phase statement only;
its exceptional two-point family has not been silently substituted
into the earlier mixed-family estimates.
# Review of the later arbitrary-cluster density extension

Section 10 of changed_row_relative_pressure.md also passes independent
review. Its original class-size-preserving hypotheses remain in force.
The retained row-root events avoid both the changed row set and every
phase-error column, including their completion column. Their mean loss
is at most \(C|S|r\log^2h/h\), obtained from the translated rooted
family's total incidence. All retained bulk and root events therefore
have the same product law after the classwise alphabet correspondence.
The flipped columns contribute only an \(\exp(O(|S|/h))\)
cardinality ratio.

Restoring protected bulk events touching the error columns costs
\(\exp(O(|S|\log^4h/h))\). This uses the sharp four/six support
count, as stated, rather than the weaker subpower estimate. The
resulting comparison is valid for arbitrary clustering of \(S\).
Summing error locations adds \(H_2(\sigma)\), and
\(\sigma\le b r\log h/h\) makes this cost smaller than the
changed-row pressure for sufficiently small absolute \(b\), fixed
\(d>0\), and \(r\le h^{1-d}\).

This extension compares words close to one global protected phase.
It does not imply a comparison for several domains occupying positive
fractions of the word.

