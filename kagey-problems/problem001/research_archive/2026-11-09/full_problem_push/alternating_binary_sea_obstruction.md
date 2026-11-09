# A mixed collision defeats the alternating binary sea

9 November 2026. Consider doubles at \(x=0\bmod8\), row 1 at every odd sea
column, and row \(h\) at every even sea column. This periodic background
eliminates two large classes of one-double obstruction when \(h=3\bmod4\).
Nevertheless it fails for every pair order at infinitely many heights.

## Two obstructions that the background removes

A three-black tilted rectangle using one double label cannot use both points
of that double: they would form a vertical diagonal, whose other corners lie
strictly between its row levels and therefore cannot be boundary sea points.
Otherwise its two sea points must lie in rows 1 and \(h\), at offsets \(p,q\)
from a central black point in row \(r\), and
\[
pq=(r-1)(h-r).
\]
The row-1 offset is odd. The row-\(h\) offset is even but not divisible by
eight, so the left side has 2-adic valuation one or two. If \(r\) is even,
the right side is odd. If \(r\) is odd and \(h=3\bmod4\), the right side is
divisible by eight. Neither case is possible.

A one-label horizontal axis rival with all three sea points in one boundary
row has offsets \(-p,q,q-p\), where \(pq=k^2\). These cannot all be odd, so
the row-1 rival is excluded. For row \(h\), all three offsets would have to
be even and not divisible by eight. Write \(p=2a,q=2b\), so \(ab\) is a square.
If \(a,b\) are odd, they are equal modulo four. If exactly one is even,
its 2-adic valuation is a positive even integer. If both are even, either
one is divisible by four or both are two modulo four. In all cases at least
one of \(a,b,b-a\) is divisible by four. Thus at least one of \(p,q,q-p\)
is divisible by eight and touches another double slot. This is not a
one-label support.

## The unavoidable mixed obstruction

Let \(t\) be positive and odd, and set
\[
h=38t+1,\qquad r=34t+1.
\]
Suppose one double containing row \(r\) is at column zero, with at least
\(21t\) columns available to its right. The following points are black:
\[
A=(0,1+34t),\quad B=(17t,1),\quad
C=(13t,1),\quad E=(12t,1+38t).
\]
Here \(17t,13t\) are odd, while \(12t=4\bmod8\), so all three noncentral
points are sea points of the prescribed color. Define
\[
P=(4t,1+36t),\qquad Q=(21t,1+2t).
\]
The set \(R=\{A,B,P,Q\}\) is a rectangle: its adjacent side vectors are
\((17t,-34t)\) and \((4t,2t)\), which are perpendicular. The set
\(S=\{C,E,P,Q\}\) is also a rectangle, because its two diagonals have the
same midpoint and squared length
\[
(1+38^2)t^2=(17^2+34^2)t^2=1445t^2.
\]
Both \(P,Q\) are white. Their sea columns have rows \(h\) and 1 respectively,
which differ from their displayed interior rows. Thus both rectangles have
exactly the same presentation \(\{P,Q\}\).

Translating by any multiple of eight preserves the background. The even
partner of row \(r\) in the central double is irrelevant to the collision.
In a complete parity graph, row \(r\) occurs in \(19t\) distinct double
columns. At most \(\lceil21t/8\rceil\le3t\) double slots lie too close to the
right endpoint for this certificate. At least one of its \(19t\) occurrences
therefore admits the collision.

Consequently this alternating background is impossible for every complete
parity-edge order at heights
\[
39,115,191,\ldots.
\]
The result concerns this prescribed periodic sea. Arbitrary binary sea choices
remain possible, as the completed height-15 spacing-eight board demonstrates.
It also shows why excluding one-label three-black and horizontal-rival
supports alone is insufficient: a mixed four-black support survives.
