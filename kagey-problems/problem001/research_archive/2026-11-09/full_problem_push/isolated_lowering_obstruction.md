# A periodic sea that is frozen under isolated lowering

9 November 2026. For every height \(h\ge7\), the ordinary-parity sea
\[
 b(x)=\begin{cases}1,&x=0\pmod3,\\4,&x\ne0\pmod3\end{cases}
 \tag{1}
\]
is valid, but replacing any one row-4 letter by any smaller row creates a
collision. Thus an internal greedy-reset proof cannot proceed by asserting
that every nonconstant periodic sea permits an isolated lowering followed by
its original future. This does not disprove greedy reset: a smaller internal
successor may require changing later letters as well.

## Validity of the periodic sea

A tilted rectangle with three black corners on rows 1 and 4 must repeat one
row on a diagonal. If the repeated row is 1, its fourth row is \(-2\), outside
the strip. Otherwise the right-angle vertex is \((x,1)\), so \(3\mid x\).
Writing the horizontal displacements to its two row-4 neighbors as \(u,v\),
orthogonality gives \(uv=-9\). At least one of \(u,v\) is divisible by three.
That neighbor therefore lies in a column whose actual black row is 1, a
contradiction. There are no three-black tilted rectangles or hidden ones.

It remains to exclude two-white collisions. A vertical displayed pair can
only be a diagonal of a tilted rectangle. If its complementary black
diagonal uses rows 1 and 4, its length \(L>3\), and its lower displayed row is
\((5-L)/2<1\). If both black endpoints have the same row, an integral
vertical alternative has two white rows of the same parity. It has no rival
from the ordinary parity pair set.

For two rectangles sharing a displayed pair, the side/side and
diagonal/diagonal configurations would produce a hidden black rectangle;
that is impossible in a sea with only these two row levels. In a mixed
side/diagonal configuration, let \(U\) be the complementary black side and
\(V\) the complementary black diagonal. Their lengths agree, and the
translation from the black side to the displayed side is perpendicular to
\(U\). Both vertical components belong to \(\{0,3,-3\}\).

- If exactly one component is zero, the displayed side would either be a
  horizontal pair at half-integral row \(5/2\), or have odd vertical
  difference and integral midpoint row. Both are impossible for lattice
  points.
- If both components are nonzero, both black-pair midpoint rows are
  \(5/2\). The perpendicular translation has vertical component zero, so
  perpendicularity forces it to be zero. The rectangle degenerates.
- If both components are zero, the displayed side and complementary black
  diagonal are horizontal with the same midpoint and length, hence coincide.

This also excludes horizontal and oblique axis rivals, by treating the axis
rectangle as the second rectangle. All singleton collisions have already
been excluded by the absence of three-black rectangles. Hence (1) is valid
for every \(h\ge7\).

## Exact obstruction certificates

It suffices to modify a column \(x=1\pmod3\); the other row-4 phase follows
by horizontal reflection. Translate the changed column to zero. The
unchanged sea has row 1 exactly at offsets \(-1\pmod3\).

If the new row is 1, the tilted rectangle
\[
 \{(0,1),(-9,4),(1,4),(-8,7)\}
\]
has the singleton white presentation \(\{(-8,7)\}\). Its column has black
row 4, and \(\{4,7\}\) is a parity-axis pair. Thus it has a singleton axis
rival.

If the new row is 2, the tilted rectangle
\[
 \{(-1,1),(0,2),(-3,3),(-2,4)\}
\]
has the singleton white presentation \(\{(-3,3)\}\). Its column has black
row 4, and the axis pair \(\{3,4\}\) gives the rival.

If the new row is 3, the two tilted rectangles
\[
\begin{aligned}
 R&=\{(-4,1),(-1,2),(-5,4),(-2,5)\},\\
 T&=\{(-1,2),(0,3),(-3,4),(-2,5)\}
\end{aligned}
\]
have the same white presentation
\(\{(-1,2),(-2,5)\}\). Their four nonshared corners are black. Direct dot
products at \((-4,1)\) and \((0,3)\), respectively, are
\((3,1)\cdot(-1,3)=0\) and \((-1,-1)\cdot(-2,2)=0\).

All coordinates lie in rows 1 through 7. The singleton certificates use the
fixed complete parity axis pair set; the two-rectangle certificate is fully
local and does not use an external owner.

## Independent check and scope

`isolated_lowering_probe.py` found the three rotations of \((1,4,4)\) as the
first frozen periodic examples at height 7, among all periods at most three.
`verify_isolated_lowering_obstruction.py` independently generated rectangles
by equal diagonals, verified the periodic word using a 23-column window
(period three plus the complete height-seven support span 20), and checked
all six isolated replacements in a 64-column word. Its exact output is
`isolated_lowering_obstruction_check.json`.

The explicit proof above removes dependence on that finite search and works
for all heights at least seven. At height seven the already certified
internal greedy map nevertheless reaches row 1 from every recurrent state.
The example isolates the missing step: a valid reset may need a coordinated
change of the future rather than a single-site modification.

## A direct constant cut can fail in every phase

There is a second obstruction to a reset shortcut. If \(a<b\) have the same
parity, the alternating two-row sea \((a,b)^{\mathbb Z}\) is valid for the
ordinary parity model, at every height containing those rows. A three-black
tilt would have a right-angle vertex on one level and its two neighbors on
the other. Both horizontal legs would be odd, whereas the product of their
vertical components is even. Their dot product cannot vanish.

For a mixed two-white collision, a horizontal complementary black pair has
even horizontal difference, whereas a cross-level pair has odd horizontal
difference and even vertical difference. Their norms have different parity.
If both pairs cross levels, their midpoint rows agree and perpendicularity
forces a zero connector. The two horizontal-pair case is degenerate as
before. A cross-level black diagonal has a half-integral midpoint column,
so it has no lattice vertical alternative; a same-level alternative has
same-parity white rows. This proves validity.

Nevertheless \((1,5)^{\mathbb Z}\), at every \(h\ge5\), cannot be followed
directly by constant row 1 at either phase. Put the cut at column zero.
If the past has row 1 on even columns, the black diagonal
\[
 (0,1),(-3,5)
\]
has horizontal white alternative \((-4,3),(1,3)\). Both displayed columns
have black row 1, so a horizontal axis rectangle gives the same presentation.
For the other phase use black diagonal \((1,1),(-2,5)\) and white pair
\((-3,3),(2,3)\). Each diagonal has length five.

`constant_cut_probe.py` independently finds this example already at period
two and height seven. The proof above is valid at all heights at least five.
Thus choosing a favorable phase of the recurrent word does not by itself
justify immediate constant padding. A successful general reset must allow
intermediate rows or a longer transition.
