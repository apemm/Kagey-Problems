# One-label separability in binary boundary seas

9 November 2026. Let \(h\ge2\), let column zero contain a proposed
odd/even double \(\{a,b\}\), and suppose every other occupied column
has just one black point, in row 1 or row \(h\). The binary choices may
be arbitrary and the horizontal interval may be finite.

**Theorem.** Every failure has a rectangle-pair witness whose symmetric
difference uses at most one of \((0,a),(0,b)\). Consequently the
double insertion is identifying if and only if both separate
single-point insertions are identifying. This equivalence includes
failures already present in the punctured background. It does not
assert that an arbitrary binary background is valid.

The same row-by-row reduction applies to local one-label constraints
with a fixed final parity graph supplying distant axis rivals. Thus a
label's admissible sea prescriptions are exactly the intersection of
the prescriptions for its two rows; there is no additional genuinely
two-row one-label condition.

## 1. Three black corners

A tilted right angle using both central points is impossible. If the
angle is at a central point, its leg to the other central point is
vertical, so the other leg would be horizontal and the rectangle would
be axis-aligned. If the angle is at a sea point \((x,s)\), then
\[
x^2+(s-a)(s-b)=0,
\]
where \(s\in\{1,h\}\) lies outside or at the boundary of \([a,b]\).
The left side is strictly positive because \(x\ne0\).

Three sea points cannot be corners of an in-strip tilted rectangle.
Two are on the same boundary row. A right angle at either of these
would require two sea points in one column. An angle at the third
point completes the rectangle beyond the opposite boundary.

Suppose instead that a tilted rectangle has exactly one central black
point \((0,r)\) and two sea black points. For an in-strip completion,
the sea points must be on opposite boundaries, and the angle must be
at the central point. For \(1<r<h\), write them as
\((u,1),(v,h)\). Then
\[
uv=(r-1)(h-r)>0,
\qquad W=(u+v,h+1-r).
\tag{1}
\]
The boundary cases \(r=1,h\) produce no tilted instance: (1) would
force a sea point into column zero. In particular \(W_x\ne0\).

For a fixed \(r\) and completion \(W\), the sum and product in (1)
determine \(\{u,v\}\). Only one assignment of low/high sea rows to
these two columns can occur, since each sea column has one black point.
Thus at most one such tilted rectangle has the given completion.
Different central rows have different completion rows \(h+1-r\).

This excludes a six-cell symmetric-difference collision of two tilted
singleton presentations, whether it uses one or both central rows.
An axis rectangle with three black corners must use both central
points. A tilted singleton rectangle must use a central point, so it
shares that black corner with any such axis rectangle. Their
intersection then has at least two corners, and the collision is a
four-cell case instead. Two axis rectangles cannot collide: the
column/row incidence graph has only one nonsingleton column and has no
four- or six-cycle.

The same observations exclude hidden rectangles in this one-label
configuration. An axis hidden rectangle needs two nonsingleton
columns. A tilted hidden rectangle would contain either three sea
corners or a tilted right angle using both central points.

## 2. Four-cell collisions using both central points

Same-side and same-diagonal collisions reduce to a hidden rectangle,
which has just been excluded. For the remaining mixed case, let
\(A,B\) be the black side and \(C,D\) the black diagonal. The common
white pair is
\[
(C+D\pm(B-A))/2.
\tag{2}
\]
These formulas apply even if a common corner is also black: the
symmetric difference is still the four prescribed black points.

Suppose these four points include both opposite-parity central
points. If the two sea points are on the same boundary, their four
row coordinates have odd sum, so (2) cannot have integral rows.

Now put the two sea points on opposite boundaries. If the central
pair is the black side, it is vertical and has length at most
\(h-1\), whereas the boundary-to-boundary black diagonal has greater
length. If the central pair is the black diagonal, the same argument
applies with the roles reversed. There is no such instance.

The remaining pairing puts one central point in each black pair.
Reflect vertically if necessary so the black side uses the low sea
point. Write
\[
A=(0,a),\quad B=(x,1),\quad C=(0,b),\quad D=(z,h),
\]
and set \(H=h-1\), \(\alpha=a-1\), \(\beta=h-b\). Equal lengths
and the side/center perpendicularity condition are
\[
z^2-x^2=\alpha^2-\beta^2,
\qquad x(z-x)=\alpha(2H-\alpha-\beta).
\tag{3}
\]
If the right side of the second equation is positive, then \(x,z\)
have the same sign and \(|z|>|x|\). The first equation gives
\(\alpha>\beta\). But
\[
x(z-x)
 =\frac{|x|}{|z|+|x|}(\alpha^2-\beta^2)
 <\alpha(\alpha-\beta),
\]
whereas
\[
\alpha(2H-\alpha-\beta)
 \ge \alpha(\alpha-\beta)
\]
because \(\alpha\le H\). This is a contradiction.

If that right side is zero, either \(\alpha=0\), which forces
\(\beta=0\) and parallel side/diagonal vectors, or
\(\alpha=\beta=H\), which makes the two centers coincide. Both are
degenerate. Thus no four-cell witness needs both central points.

Together with Section 1 and the elementary classification by the
number of common rectangle corners, this proves the theorem.

## 3. Virtual axis rivals do not introduce a two-row condition

A singleton axis rival of (1) uses the retained sea point at column
\(u+v\), which is nonzero. With a fixed final parity graph its
availability therefore depends on \(r\), the sea, and that graph,
without using the other central row.

There is no one-label vertical-pair rival. A black diagonal joining an
interior central row to a boundary point has length strictly greater
than its vertical difference, so its vertical alternative extends
beyond that boundary. The central-central vertical diagonal has no
distinct vertical alternative. Two sea points likewise have no
in-strip vertical alternative.

Horizontal axis rivals are already four-cell mixed collisions covered
by Section 2. If a putative singleton description happens to use both
central points through its axis owner, their common central corner
cancels from the symmetric difference, leaving a one-row four-cell
witness. This is why one must compare positive symmetric-difference
supports rather than only count black corners in each rectangle.

## 4. The zero-label qualification

At even height every binary boundary sea is identifying. The only
possible zero-label mixed collision would have a horizontal black
side on one boundary and a black diagonal joining opposite boundaries.
Its lengths satisfy
\[
L^2=d^2+(h-1)^2.
\]
Integral common columns require \(L\equiv d\pmod2\), which is
impossible when \(h-1\) is odd. All other mixed cases are degenerate
or have a side spanning the full height, leaving no perpendicular
translation inside the strip.

At odd height this conclusion fails. At \(h=5\), make the sea low at
columns \(-1,0,4\), and high at column 3. The rectangles
\[
\{(-1,1),(4,1),(-1,3),(4,3)\}
\]
and
\[
\{(0,1),(3,5),(-1,3),(4,3)\}
\]
have the same white presentation \(\{(-1,3),(4,3)\}\).

This example occurs in the quadratic-character sea modulo seven,
with row five at nonzero quadratic residues and row one at
nonresidues: translate by six to get low columns \(5,6,10\) and high
column 9. None of these columns is zero modulo seven, so the choice
at zero residues cannot repair it. Vertical reflection gives the
corresponding example for the flipped character sea.

Thus any use of character seas at odd heights needs a separate
zero-label check. Boundary-row insertions may also be unsafe there;
the theorem asserts separability, not universal safety of either row.
