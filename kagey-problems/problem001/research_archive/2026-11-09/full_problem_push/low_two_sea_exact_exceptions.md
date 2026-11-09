# Exact one-label exceptions for the gap (1,2,1)

9 November 2026. Put a black point on row one in every odd column, and on
row two in every column congruent to two modulo four. Leave the columns
divisible by four empty. The geometry is considered in the infinite
horizontal strip of rows \(1,\ldots,h\), with \(h\ge4\).

Insert one parity edge \(\{a,b\}\) in column zero, where \(a\) is odd and
\(b\) is even. Singleton and vertical axis rivals are interpreted against
the final complete parity graph. Other double slots supply no required black
points in this local test.

**Theorem.** The empty background is safe. The inserted edge is safe against
every zero-label or one-label forbidden support if and only if it is not
\[
\{1,4v^2+2\},\qquad v\text{ a positive odd integer},\qquad4v^2+2\le h.
\tag{1}
\]
There are only \(O(\sqrt h)\) exceptional edges. In particular, every edge
not incident with row one is safe in this local sense, at every height.

This is not a construction of an equality board. Supports involving two or
more labels remain, and some occur between adjacent slots.

## 1. Checkerboard and low-row restrictions

Every background point has \(x+y\) even. The even central point also has
this property, while the odd central point has \(x+y\) odd.

The sum modulo two of \(x+y\) over the four vertices of any lattice rectangle
is zero. Consequently the symmetric difference of two rectangles also has
an even number of points with \(x+y\) odd. A four-point forbidden support
cannot contain the odd central point. If the odd central point is a shared
corner, it is absent from the symmetric difference and the four-point
analysis below still applies.

No hidden rectangle exists. One containing the odd central point violates
checkerboard parity. Without that point, a hidden rectangle would have one
high point and three points on the two low rows, or all its points on the two
low rows. Three low points include a horizontal pair; neither the side nor
diagonal interpretation can accommodate the remaining high point. When all
points lie on the two low rows, the rectangle is axis-aligned, but each
column has at most one available black point.

A tilted rectangle with two background black points must use one point on
each low row as a side. A diagonal joining rows one and two has row sum
three, so any alternative integral diagonal staying in the strip also uses
these two rows and gives an axis rectangle. A horizontal diagonal with both
black endpoints on row two has length divisible by four. Its only possible
nonhorizontal alternative staying above row zero would require a square
exactly four below that squared length, which is impossible. Row-one
horizontal diagonals cannot tilt inside the strip.

These observations exclude background-only collisions. In particular, two
background sides with the same white pair would give a hidden rectangle;
the mixed alternative would require a background black diagonal.

## 2. Classifying three-black tilted rectangles

First suppose the rectangle uses only one central point \((0,r)\).
Two sea points on the same low row cannot form a tilted three-black rectangle
inside the strip. For two row-two points, the only possible central rows are
one or three, but the right-angle product would be \(-1\), whereas both
horizontal offsets are two modulo four. The row-one case immediately leaves
the strip or is degenerate.

Let the two sea points be \((p,1)\) and \((q,2)\), with \(p\) odd and
\(q=2\pmod4\). A right angle at the central point would have completion row
\(3-r\), forcing \(r\le2\), when its right-angle product is zero and the
rectangle is degenerate. The other possibilities are
\[
\begin{array}{c|c|c}
\text{right-angle vertex}&\text{equation}&\text{completion}\\ \hline
(p,1)&p(q-p)=r-1&(q-p,r+1)\\
(q,2)&q(q-p)=r-2&(p-q,r-1).
\end{array}
\tag{2}
\]
The first equation forces \(r\) even; the second forces \(r=0\pmod4\).
In both cases the completion column and row are odd. Its retained sea point
is therefore row one, of the same parity, so there is no singleton axis
rival. The completion is not a double column.

For a fixed central point and a fixed singleton completion, each line of
(2) determines its two sea points uniquely. The two lines have different
completion rows. Thus these rectangles cannot collide with one another.

Now suppose the rectangle uses both central points. They must form a
vertical diagonal. A sea point strictly between their rows can only be on
row two, so the central edge must be \(\{1,b\}\). The circle equation is
\[
x^2=(2-1)(b-2)=b-2.
\]
The sea condition \(x=2\pmod4\) gives exactly \(b=4v^2+2\) with \(v\)
odd. The other corner is \((-2v,b-1)\). It is a white odd-row point over a
retained row-two sea point, so the full parity graph supplies a singleton
axis rival. This proves necessity of excluding (1).

It also completes the singleton classification. These exceptional
completions have an even column, whereas completions in (2) have an odd
column. The two mirror-image exceptional rectangles have different
completion columns. No additional singleton collision was omitted.

## 3. Vertical rivals

A complementary vertical white diagonal has midpoint column half the sum
of the black columns. If the odd central point is paired with a row-one sea
point, that midpoint is not integral. If it is paired with a row-two sea
point, its squared length is five modulo eight, so the required vertical
length is not integral.

A black pair containing only checkerboard-even points cannot have a vertical
white pair of opposite row parity, by the rectangle checkerboard identity.
The two central points already form a vertical diagonal, whose only vertical
alternative is the same pair. Hence there are no vertical parity rivals.

## 4. Mixed four-point supports

The standard two-white-presentation reduction leaves only the mixed case:
one black pair is a side and the other is a diagonal. Same-side and
same-diagonal cases would give a hidden rectangle. By Section 1, a mixed
support using the central label must use its even point \((0,r)\) and three
sea points. Integrality of the common white corners requires the total black
row sum to be even. Thus either all three sea points lie on row two, or two
lie on row one and one on row two.

Suppose first that \(r\ge4\). If all three sea points lie on row two, one
black pair is horizontal with length divisible by four, and the other has
horizontal component two modulo four and even vertical component. Its
squared length is four or eight modulo sixteen, a contradiction.

With two row-one points and one row-two point, there are two pairings.

* Pair the central point with the row-two point. If this is the side, the
  translated row-two corner has row \(2-r/2\le0\). If it is the diagonal,
  an integral horizontal alternative has length two modulo four and both
  endpoint columns even. It cannot be the side above two row-one sea points,
  whose columns are odd.
* Pair the central point with a row-one point. If this is the side, its
  translated low corner again has row \(2-r/2\le0\). Otherwise the side
  joins the other row-one point to the row-two point and has vector
  \((d,1)\), with \(d\) odd. Its perpendicular translation has vertical
  component \((r-2)/2\), so \(d\mid(r-2)/2\). But equality of lengths with
  the central-to-row-one diagonal requires \(|d|\ge r-1\), contradicting
  \(|d|\le(r-2)/2\).

For \(r=2\), all four black points lie on the two adjacent low rows.
Horizontal pairings are degenerate. In a cross pairing both pair centers
have row \(3/2\). Their connector is horizontal, while the side has nonzero
horizontal component, so orthogonality forces a zero connector and again a
degenerate rectangle.

This includes horizontal and oblique axis rivals, since their black pairs
are covered by the same side/diagonal classification. Sections 1 through 4
prove sufficiency outside the exceptional family.

## 5. Verification and a remaining obstruction

`verify_low_two_sea_one_label.py` uses independent side and diagonal
completion. It tests the empty background and every parity edge for each
height from four through thirty. Every case agrees with (1): below six there
are no exceptions, and from six through thirty the only exception is
\(\{1,6\}\). The tested interval extends at least twice the general tilted
span bound \(1+\lfloor(h-1)^2/4\rfloor\) on each side.

Multi-label singleton collisions remain. For \(r=2\pmod4\), \(r\ge6\),
place row-\(r\) points at columns zero and \(r-2\). The two triples
\[
\{(0,r),(1,1),(r,2)\},\qquad
\{(r-2,r),(2r-3,1),(2r-2,2)\}
\]
complete to the same white point \((r-1,r+1)\), whenever \(h\ge r+1\).
At \(r=6\), the two required double columns are adjacent slots. Thus the
one-label theorem does not justify grouping each even row into a constant
block. Separating repetitions of each row can remove this particular
obstruction, but additional multi-label conditions still need control.
