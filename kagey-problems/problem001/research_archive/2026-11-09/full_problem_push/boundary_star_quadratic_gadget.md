# A quadratic-width gadget for an entire boundary star

9 November 2026. This construction places all opposite-parity edges incident
to row one in a single block. It is tested against the complete final
parity pair set, including edges not present in this block. It does not
place the other parity edges.

Let \(h\ge2\), \(n=\lfloor h/2\rfloor\), and choose an integer p divisible
by four with \(p>h\). In the infinite strip put row one in every column,
and add
\[
 (pi,2i+2),\qquad 0\le i<n.
 \tag{1}
\]
Thus the double columns contain exactly
\(\{1,2\},\{1,4\},\ldots,\{1,2n\}\).

**Theorem.** This word is hidden-free and valid relative to the complete
opposite-parity pair set. A finite block of width
\[
 p(n-1)+1=O(h^2)
 \tag{2}
\]
contains all its doubles and has arbitrary constant row-one tails.
Any subset of the displayed doubles can be retained.

For definiteness one may take \(p=4\lceil(h+1)/4\rceil\).
The exact proof is below. It passed the
[independent audit](wide_linear_star_independent_audit.md).
Independent side/diagonal completion checks passed at every height from
four through thirty, including constant collars and the full final
parity pair set; see wide_linear_star_check.json.

Call the added points extra points and call row one the baseline.
The extra points are collinear, with successive displacement \((p,2)\),
and all have even row.

## 1. Hidden rectangles and singleton presentations

A hidden rectangle cannot have three points on either line. If it had
two baseline points and two extra points, the baseline pair would be a
horizontal side or a horizontal diagonal. A horizontal side requires a
second horizontal side, whereas the extra points have distinct rows.
A horizontal diagonal would require extra points on opposite sides of
the baseline. All extra points are above it. Thus there is no hidden
rectangle.

A tilted rectangle with three black corners must use two extra points
and one baseline point. Three collinear points cannot be its corners.
Two baseline points cannot accompany one extra point, since their
horizontal diagonal would put the fourth corner below the strip.

The right angle cannot be at an extra point of row \(2i+2\). The line
through the two extra points has direction \((p,2)\). Its perpendicular
through that point meets row one at horizontal displacement
\[
 \frac{2(2i+1)}p,
\]
which is not an integer, since \(4\mid p\). Therefore the right angle is
at the baseline point.

Let the extra indices be \(i<j\), the baseline point be \(C=(x,1)\), and
the fourth corner be \(W\). Then
\[
 W_y=2(i+j)+3,\qquad W_x=p(i+j)-x.
 \tag{3}
\]
In particular, \(W_y\) is odd.

The column of W cannot be an extra column. Otherwise (3) makes x a
multiple of p as well. The two horizontal legs at C are then nonzero
multiples of p, while their vertical components have absolute value
at most \(h-1\). Their dot product cannot vanish because
\(p^2>(h-1)^2\). A zero horizontal leg cannot occur at a right angle
with both other points strictly above the baseline.

Consequently W's column contains only the row-one black cell. Both
that cell and W have odd row, so the singleton presentation has no
virtual parity-axis rival.

Moreover, a white corner W determines at most one such rectangle.
Equation (3) determines \(i+j\) and x. The right-angle equation is
\[
 (pi-x)(pj-x)+(2i+1)(2j+1)=0.
 \tag{4}
\]
For fixed \(i+j\) and x, its coefficient of \(ij\) is \(p^2+4\), so it
determines \(ij\) and hence the unordered pair \(\{i,j\}\).
Thus two distinct tilted rectangles cannot have the same singleton
presentation.

## 2. Vertical presentations have no parity-axis rival

If a black diagonal uses a baseline point and another point, a longer
vertical diagonal with the same midpoint extends below row one.
The same is true for two baseline points.

If its endpoints are both extra points, both rows are even. Any integral
vertical alternative has even length, so its displayed row pair has the
same parity. It is not an edge of the full parity pair set.

These arguments also cover the case when the two black points belong
to the same double column: a vertical diagonal has no distinct vertical
alternative.

## 3. Four-cell mixed supports

Two rectangles sharing a side in both or a diagonal in both would force
a hidden rectangle. The only remaining two-common-corner case is a
mixed support: its four black points split into a black side U and a
black diagonal V, with
\[
 |U|=|V|,\qquad U\cdot H=0,
 \tag{5}
\]
where H is the difference of the two black-pair sums. The common corners
must be integral and lie inside the strip.

Every such four-cell symmetric difference has even total row sum.
Since baseline rows are odd and extra rows are even, a mixed support
cannot have an odd number of extra points. Four points on one line are
also impossible in (5). It therefore uses exactly two extra points
and two baseline points.

If the extra points form one black pair and the baseline points the
other, equality of lengths is impossible. An extra-pair length is
\[
 |i-j|\sqrt{p^2+4},
\]
which is irrational: for \(p\ge4\), \(p^2<p^2+4<(p+1)^2\). A baseline
pair has integer length.

It remains to consider the crossed pairing. Subtract one from every
row, so the baseline is at height zero. Let the side's extra height be
a and the diagonal's extra height be b. Both are positive odd integers.
The common-corner heights are \((b-a)/2,(b+a)/2\). They must be
nonnegative. The case \(b=a\) repeats the same extra point in both
black pairs and is not a four-point support. Thus
\[
 b=a+2D,\qquad D\ge1.
\]

Orient the side and diagonal from their baseline points to their extra
points, writing their horizontal components as u and v. Their extra
horizontal coordinates differ by \(pD\), so their pair-sum difference
has components
\[
 H_x=2pD+u-v,\qquad H_y=2D.
\]
Equal norms give \(|u|>|v|\). If \(u\ge0\), both terms in \(U\cdot H\)
are positive, so (5) fails. Hence put \(u=-U\), where \(U>0\).

Because a and b are odd, the norm equation modulo four makes U and v
have the same parity. Define positive integers
\[
 x=(U+v)/2,\qquad y=(U-v)/2,\qquad U=x+y.
\]
Orthogonality becomes
\[
 (pD-x)U=Da.
 \tag{6}
\]
Thus \(z=pD-x\) is a positive integer, \(zU=Da\), and
\[
 pD=x+z\le U+\frac{Da}{U}\le Da+1.
 \tag{7}
\]
The last inequality holds for every \(1\le U\le Da\), since
\((U-1)(U-Da)\le0\).
It follows that
\[
 p\le a+\frac1D\le h,
\]
contrary to the choice of p. This excludes the crossed mixed support.

## 4. Completion of the validity proof

Distinct tilted rectangles with a common presentation of at least
three points coincide. Presentations of two points were excluded in
Section 3, and singleton collisions in Section 1. Hidden rectangles
were excluded outright.

Every singleton or vertical axis rival is excluded in Sections 1--2.
Horizontal and oblique axis rivals are among the same hidden or mixed
four-cell cases in Section 3. Axis-axis uniqueness holds because the
distinct double edges form a star.

The argument is made in the infinite strip. Restricting to any finite
interval preserves validity, and the constant baseline tails have
already been included. Removing selected extra points preserves
hidden-free validity with the same final parity pair set, by the
deletion lemma in hereditary_marked_bridges.md.

This is a boundary-star construction, not a construction of all q
parity doubles. Its purpose is to handle an entire exceptional
boundary-edge family at quadratic cost.
