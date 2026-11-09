# Nine columns determine every full row-class box

9 November 2026. The arbitrary-phase full-box classification can be proved
using nine consecutive columns. This also explains why the Boolean check
needed only forbidden supports of horizontal span at most four.

Let \(h\ge8\), or \(h=6\). Let \(c:[1,h]\to\mathbb F_2\) be balanced.
At each of nine consecutive columns x, allow the complete class
\(B_{t_x}=\{y:c(y)=t_x\}\). Suppose every assignment avoids singleton-axis
and vertical-pair axis rivals relative to the complete cross-class pair set.
Then, throughout the row interval and the column interval,
\[
 c(y)=\kappa q(y)+\alpha y+\beta,\qquad
 t_x=\kappa q(x)+\gamma x+\delta,
 \quad q(n)=\binom n2\pmod2.
 \tag{1}
\]
This classifies those two rival families only. It does not remove the other
four-cell and six-cell collisions.

## Two short symmetry defects suffice

Define
\[
 D_s=\{k\ge1:\text{some }a\in B_s\text{ has }a\pm k\in[1,h]
       \text{ and }c(a-k)\ne c(a+k)\}.
\]
If \(1\notin D_s\), the proper class \(B_s\) contains no adjacent pair.
Indeed an adjacent pair propagates in both directions by unit reflections
about its members, and would fill the entire row interval.

If also \(2\notin D_s\), a pair at distance two similarly propagates the
entire physical parity class. Any extra member would be adjacent to a member
of that class, which is impossible. Thus either \(B_s\) is one whole parity
class, or its distinct members are separated by at least three. The second
case has size at most \(\lceil h/3\rceil\), whereas balance gives
\[
 |B_s|\ge\lfloor h/2\rfloor>\lceil h/3\rceil.
\]
The strict inequality holds at all the stated heights.

Consequently, if c is not ordinary parity, each \(D_s\) meets \(\{1,2\}\).
At least one contains 1: if both omitted 1, neither color could have adjacent
members, and the row coloring would alternate.

## The asymmetric case is impossible on nine columns

Every \(k\in D_s\) forbids \(t_x=t_{x+2k}=s\). The two allowed black cells
at row a form a horizontal diagonal of a tilted square, whose vertical
diagonal is a cross-class pair. The midpoint column can choose another row
from its full class so that both displayed cells are white.

Suppose one \(D_s\) contains 1 and the other omits 1. The latter contains 2.
Restricting t to one column parity therefore gives, after possibly swapping
colors, a binary word with no adjacent 11 and no 00 at distance two.
Nine columns contain five positions of one parity, but no such binary word
has length five. If its middle bit is 1, its two adjacent bits are 0, already
forbidden at distance two. If its middle bit is 0, its two endpoints must be
1; these again force the two adjacent bits to be 0.

Thus every nonparity row partition surviving the hypotheses has
\(1\in D_0\cap D_1\). It follows directly that
\[
 t_{x+2}=1-t_x
\]
whenever both columns lie in the interval. Hence
\(t_x=q(x)+\gamma x+\delta\) throughout it.

## Two templates recover the row coloring

Use rectangles with adjacent vectors \((1,2),(2,-1)\), and
\((1,3),(3,-1)\). Their corner columns have spans three and four. Each
rectangle and its two-column horizontal translate fit in seven columns.
The column phases in these two contexts are complementary. An odd
four-corner XOR of \(c(y)+t_x\) would therefore give exactly three allowed
corners in one context and a singleton-axis rival.

Writing \(e_y=c(y)+c(y+1)\), the two templates consequently give
\[
 e_y+e_{y+2}=0\quad(1\le y\le h-3),\qquad
 e_y+e_{y+3}=1\quad(1\le y\le h-4).
\]
The first makes e two-periodic; the second makes its two parity values
different. Therefore \(c(y)=q(y)+\alpha y+\beta\), proving (1) in the
nonparity case.

If c is ordinary parity, a unit vertical shift complements all four row
colors in either template. Both placements fit at every stated height.
Their column-phase XORs must vanish. With \(d_x=t_x+t_{x+1}\), this says
\(d_x=d_{x+2}=d_{x+3}\). The relations connect all bonds of an interval
of at least five columns, so \(t_x=\gamma x+\delta\).

Finally, the forms in (1) are sufficient: the four-corner XOR on a rectangle
with perpendicular adjacent vectors u and v is
\(\kappa(u_xv_x+u_yv_y)=0\). This excludes singleton rivals. For a vertical
displayed pair, its two column contributions cancel, forcing its row colors
to agree and excluding a cross-class vertical rival.

The height-seven exception \(B_1=\{1,4,7\}\), \(t_x=1\), remains valid for
these two rival families. It is exactly the three-separated possibility that
the strict density inequality excludes at the stated heights. The proof
above does not claim that width nine is optimal.
