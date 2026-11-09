# The in-strip P graphs also need unbounded palettes

9 November 2026. The unbounded-chromatic-number theorem for the odd
Pythagorean graph remains an obstruction after restoring the actual strip
condition in the one-prime scaffold. This is a finite embedding consequence
of [the odd-input theorem](odd_graph_odd_folner_adaptation.md), rather than
another partition-regularity argument.

The finite embedding and axis-owner argument passed independent review.
[A direct integer check](in_strip_p_embedding_check.json) embeds all 825
edges of the saved 199-vertex five-chromatic graph at height 15,484, with
even block row 7,742. The embedding itself needs only the stated block
separation inequality, so the checker does not impose an unnecessary prime
condition on its separation parameter.

## Finite embedding

Let G be any finite graph on positive odd integers. For each edge choose an
orientation u to v and a positive integer z satisfying
\[
 z^2=u^2+4(v-u)^2.
\]
The integer z is odd and strictly larger than u. Define
\[
 A=\max_{u\to v}\frac{z-u}{2},\qquad
 C=\max\left(\max_{u\in V(G)}u,\ 
              \max_{u\to v}\frac{z+u}{2}\right).
\]
Take an even row B with
\[
 1+A\le B\le h-C.                                      \tag{1}
\]
In the block of the one-prime scaffold whose even row is B, use the odd-row
vertices B+u for u in G. They all lie in the strip. Their column indices have
the form
\[
 x_u=4\left(\frac{B+u-1}{2}+p\,\frac{B-2}{2}\right).
\]
Thus the segment from the odd point in column u to the even point in column v
has horizontal component 2(v-u), vertical component -u, and length z. Its
alternative vertical diagonal has column (x_u+x_v)/2 and endpoint rows
\[
 B+\frac{u-z}{2},\qquad B+\frac{u+z}{2}.                 \tag{2}
\]
Condition (1) puts both endpoints in the strip. The endpoints are integral
and have opposite parity because their difference is the odd integer z.
Consequently every edge of G is an actual in-strip P obstruction.

The vertical presentation column lies between the two original columns.
Its opposite-parity row pair has an owner among the complete parity doubles.
That owner's even row differs from B, since z>u. It is therefore in another
block and cannot be the presentation column when p>10h. This gives a
distinct axis rectangle with the same presentation. The argument still
applies if other points of the presentation have also been blackened:
the symmetric difference of the two rectangles is already black.

## Consequences for palettes

For each fixed K, the odd-input theorem supplies a finite G with
\(\chi(G)>K\). Its constants A,C are fixed. At every sufficiently large
height, every even B in the central half of the strip satisfies (1).
Therefore
\[
 \min_{\substack{B\ {\rm even}\\h/4\le B\le3h/4}}
 \chi(P_{h,B})\longrightarrow\infty.
\]
Here \(P_{h,B}\) is the actual in-strip P graph of that block, without adding
any out-of-strip obstruction.

In particular, dropping the strip condition was not the reason a bounded
palette failed. The original separated-layer version of the one-prime
scaffold requires an unbounded number of layers, even for the true P tests.
Because one such layer has width of order \(h^2\), that fixed lifting rule
cannot have an absolute quadratic-width bound.

This statement concerns the prescribed one-prime positions and their
separated lifts. It does not exclude nonlinear repositioning, different
scaffolds, or arbitrary quadratic-width equality boards.
