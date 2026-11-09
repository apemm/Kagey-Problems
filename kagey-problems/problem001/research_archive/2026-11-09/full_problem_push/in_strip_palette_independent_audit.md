# Audit of the in-strip palette embedding

9 November 2026. The finite embedding in in_strip_p_palette_obstruction.md
is correct, conditional only on the already-audited positive-odd graph theorem.

For an oriented edge \(u\to v\), the strict inequality \(z>u\) follows from
\(u\ne v\). The lower offset \((u-z)/2\) is negative, and the upper offset
\((u+z)/2\) is positive. The constants \(A,C\) therefore control both white
rows and every selected black odd row. For example,
\(h\ge4\max\{A+1,C\}\) makes the stated condition hold for every even
\(B\) in the central half.

The two white rows are integral and have odd difference \(z\), so their pair
belongs to the final parity graph. Neither white row equals \(B\), because
that would require \(z=u\) or \(z=-u\). Its even-row block is therefore different
from the original block. The owner lies outside the original block's column
interval when \(p>10h\), while the white presentation column is between the
two original black columns. This establishes that the axis rival is a distinct
rectangle.

The unbounded chromatic number of the positive-odd graph supplies a finite
graph of chromatic number greater than any fixed \(K\), by the finite-subgraph
characterization of graph colorability. Once that finite graph is fixed, the
preceding uniform central-half embedding applies at every sufficiently large
height. Thus the minimum of the central-block in-strip chromatic numbers
diverges as stated.

The width consequence applies to the prescribed separated full-layer lifting
rule. It does not exclude overlapping layers, nonlinear repositioning, or
other quadratic-width constructions.
