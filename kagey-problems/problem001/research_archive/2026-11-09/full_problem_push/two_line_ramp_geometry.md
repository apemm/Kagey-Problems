# What a round-robin ramp excludes

9 November 2026. Consider the black points
\[
A_i=(8i,4i+a),\qquad B_i=(8i,2i+b),
\]
for integer indices in an interval, with \(a\) odd and \(b\) even. Only indices
whose rows fit the strip are retained.

This ramp has no three-black right angle, no hidden rectangle, and no mixed
four-black collision supported entirely on its double points. These claims
do not concern supports using boundary sea points. They also do not exclude
axis rivals supplied by the final complete parity graph.

## Three-point and hidden-rectangle exclusions

If a right angle uses two points on the odd branch and one on the even branch,
and its vertex is on the odd branch, its dot product has the form
\[
64mn+4m\,u=4m(16n+u),\qquad u\text{ odd},\quad m\ne0.
\]
It is nonzero. A vertex on the even branch instead has two vectors whose
vertical components are odd, so their dot product is odd. With two even
branch points and one odd branch point, the analogous expression is
\(2m(32n+u)\). Three points on a single branch are collinear.

A hidden rectangle cannot have three points on one branch. If it has two
points on each branch, these pairs cannot be sides, since the two branch
lines are not parallel. If they are diagonals, equality of squared lengths
would give
\[
80m^2=68n^2,\qquad\text{or}\qquad20m^2=17n^2,
\]
which has no nonzero integer solution.

## The mixed four-point exclusion

As in the usual two-white-presentation reduction, a mixed collision consists
of a black side from one rectangle and a black diagonal from another.
The total sum of the four black row coordinates must be even. A distribution
of three odd-branch points and one even-branch point is therefore impossible,
as is its reverse. Four points on one branch would force the side and
diagonal centers to coincide and make the side rectangle degenerate.

If the side endpoints lie on one branch and the diagonal endpoints lie on
the other, their equal lengths again require \(20m^2=17n^2\).
It remains to consider the side \(A_iB_j\) and diagonal \(A_kB_l\).
Set
\[
m=j-i,\quad p=k-i,\quad q=l-j,\quad u=2j+b-4i-a.
\]
The integer \(u\) is odd. The side vector is \((8m,u)\). Orthogonality
between this vector and the connector of the two centers gives
\[
u(2p+q)=-32m(p+q).
\tag{1}
\]
Equality of squared lengths gives
\[
16(q-p)(2m+q-p)+(q-2p)(u+q-2p)=0.
\tag{2}
\]
The four black points are distinct, so \(p,q\ne0\). A shared black corner
would already give three common corners and identical rectangles.

Write \(P=v_2(p)\) and \(Q=v_2(q)\). For \(m\ne0\), equation (1) rules
out \(Q<P\), \(Q=P\), and \(Q>P+1\), by comparing valuations on its two
sides. Thus \(Q=P+1\), and
\[
v_2(2p+q)\ge P+5,
\qquad v_2(q-2p)=P+2,
\qquad v_2(q-p)=P.
\]
If \(m=0\), equation (1) gives \(q=-2p\) and the last two conclusions
still hold. In (2), the first summand is divisible by \(2^{P+4}\), while
the second has valuation exactly \(P+2\). They cannot sum to zero.

## A surviving vertical rival

The preceding exclusions do not make the ramp safe against the complete
parity graph. In the ordinary round-robin order inside the odd row class
\(1\pmod4\), one ramp has consecutive edges
\[
\{5,18\},\qquad\{9,20\}.
\]
Use the black point at row five in the first column and the black point at
row twenty in the next column. Their horizontal gap is eight and their
vertical gap is fifteen, so their diagonal length is seventeen. The
alternative vertical diagonal in the midpoint column has rows four and
twenty-one. It lies inside every strip of height at least twenty-one.

The full parity graph contains the edge \(\{4,21\}\), so it supplies an
axis rival. If either prospective white point is black, the same positive
support is still forbidden by the no-hidden theorem. For the standard
round-robin order on both row classes at heights \(h=3\pmod4\), the displayed
ramp exists for every \(h\ge23\).

Thus interleaving repeated rows eliminates one class of vertical rivals, but
the unmodified round-robin construction still fails through cross-edge
vertical rivals. A successful ordering must control these pairs as well as
the transitions between ramps and between background orientations.
