# Two modular reductions for multi-label collisions

9 November 2026. The period-seven profiles have additional restrictions
on multi-label mixed supports. These restrictions can help a correlated
placement argument. They do not by themselves construct a complete
quadratic-width board.

Use normalized inserted row residues \(0,5\), and sea points
\[
\{(x,0):x\in\{3,5,6\}\}
\cup\{(x,1):x\in\{1,2,4\}\}
\cup\{(0,3)\}
\subset\mathbb F_7^2.
\tag{1}
\]
Every inserted point has column residue zero. The normalization and
physical parities are those of
[safe_triangle_pair_first_moment.md](safe_triangle_pair_first_moment.md).

## 1. Three inserted points and one sea point never form a mixed support

**Lemma.** There is no mixed four-cell support using three inserted
points and one sea point from (1). This applies whether the inserted
points belong to two or three labels.

Let the inserted row residues be \(r,s,t\in\{0,5\}\), and the
sea point be \((x,u)\). First put two inserted points in the black
side. Equal norms and perpendicularity become
\[
(s-r)^2=x^2+(u-t)^2,\qquad
(s-r)(t+u-r-s)=0.
\tag{2}
\]
If \(r=s\), anisotropy of the norm over \(\mathbb F_7\) forces
\(x=0,u=t\). The only sea point with zero column has row three,
so this is impossible. If \(r\ne s\), their sum is five and
their squared difference is four. The second equation requires
\(t+u=5\). The choice \(t=0\) would require sea row five.
The choice \(t=5\) requires \(u=0\), and the first equation then
forces \(x=0\), impossible for a low sea point.

The other pairing puts an inserted point and the sea point in the
black side, with the other two inserted points as black diagonal.
Eliminating \(x^2\) from the norm and perpendicularity equations gives
\[
(u-r)(s+t-2r)=(t-s)^2.
\tag{3}
\]
If \(s=t\), the norm equation again forces \(x=0,u=r\),
impossible. Otherwise \(s+t=5\) and \((t-s)^2=4\).
For \(r=0\), (3) requires \(u=5\). For \(r=5\), it requires
\(u=0\), and the perpendicularity equation forces \(x=0\).
Neither is a sea point. This proves the lemma.

## 2. Full occupation removes the two-label horizontal family

**Lemma.** Consider a finite region in which every column congruent
to zero modulo seven is occupied by a distinct real double label of
one oriented profile. Every other column has its prescribed low or
high binary sea point. No horizontal mixed support contained in this
region uses exactly two labels.

If the black horizontal side consists of sea points, both are on the
same level \(L\) or \(H\), and the black diagonal uses one point
from each label. A mixed-residue diagonal has odd physical row sum,
so its horizontal white alternative is not integral. A same-residue
diagonal has zero norm modulo seven. Thus the horizontal sea-side gap
is zero modulo seven. The common horizontal midpoint equals the
diagonal midpoint, whose column is zero modulo seven. The sea-side
endpoints must therefore both have column residue zero, contradicting
their binary sea type.

A black horizontal side cannot use one label point and one sea point,
because label rows are bulk rows. If both side points are label
points, any other point from either label lies in a side-endpoint
column. A nonhorizontal diagonal of the same length has both endpoint
columns strictly between those columns, so it cannot use either
label again. Its two sea endpoints cannot help: opposite binary levels
give a half-integral horizontal midpoint row, and equal levels give
a degenerate horizontal diagonal. These cases exhaust two-label
horizontal mixed supports.

This is a statement about supports contained in the fully occupied
region. An \(F\)-filled collar can reintroduce the horizontal family
near its ends. A collared construction would need to control those
boundary interactions separately.

## 3. Exact finite verification

`verify_mod7_multilabel_reductions.py` exhausts all modular pairings
for the first lemma. It also checks the integer coordinates in the
horizontal filler family for \(1\le k\le100\), and verifies the
divisor count of those witnesses. These checks validate the finite
algebra; the incidence estimate and the containment statements above
are analytical.
