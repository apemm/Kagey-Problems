# Filling every fourth column removes isolated horizontal rivals

9 November 2026. This is a reduction for a possible quadratic construction, not an existence theorem for the required edge ordering.

Let \(h\ge4\) and \(q=\lfloor h^2/4\rfloor\). On columns \(1,\ldots,4q\), put one opposite-parity double in every column divisible by four, using every parity edge exactly once. Put a row-1 singleton in every remaining column. The black count is \(4q+q\), so any valid ordering would attain the general upper bound at width \(4q\).

**Proposition.** Every forbidden geometric support of this board involves black cells from at least two double labels. Thus the one-double private prescriptions used in the positional construction are unnecessary for this fully occupied four-slot layout.

The conclusion refers to actual supports in the finite board. Every required black point in a double column is attributed to that double label, even when its row is one.

## 1. Three-black tilted rectangles cannot use one double

A tilted rectangle contained in the strip has at most one corner in its bottom row. Two bottom-row corners would either be a horizontal side, making the rectangle axis-aligned, or a horizontal diagonal, forcing another corner below the strip.

If three black corners used only one double label, two would have to be the two points of that double. They cannot form a vertical side of a tilted rectangle, so they would be its vertical diagonal. The circle with this vertical diameter has no other point in row 1: row 1 is below the circle, or is its unique bottom endpoint when the double contains row 1. The third black point therefore cannot be a row-1 singleton.

This also excludes hidden tilted rectangles using at most one double label.

## 2. The only remaining isolated four-cell case is horizontal

Every four-cell symmetric difference of two rectangles has even total row sum. Indeed, each rectangle has even total row sum, and the common corners are subtracted twice. A support consisting of both opposite-parity points of one double and two row-1 points has odd total row sum, so it cannot occur.

A four-cell support with only one point from a double has three row-1 points. Two tilted rectangles cannot supply it, since each has at most one bottom-row corner. An oblique or vertical axis rival cannot supply it either: its two nonshared corners have different rows, so at most one is in row 1. The only remaining case is a horizontal axis rival of a tilted rectangle.

Let the central black point be \((X,2d+1)\), with \(X\equiv0\pmod4\). Its other tilted black diagonal endpoint is \((X+z,1)\). If the common white diagonal is horizontal and integral, write its length as \(L\). Then
\[
L^2-z^2=4d^2.
\]
The positive integers
\[
p=(L-z)/2,\qquad q'=(L+z)/2
\]
satisfy \(pq'=d^2\). The three required row-1 black cells are at offsets
\[
-p,\qquad q'-p,\qquad q'
\]
from \(X\). The middle one is the other black diagonal endpoint; the outer two supply the axis rival. The case \(p=q'\) would ask for a row-1 point in the central double together with another odd row, incompatible with an opposite-parity double. Thus the three offsets are nonzero in any actual one-label support.

At least one of \(p,q',q'-p\) is divisible by four. To see this, suppose neither \(p\) nor \(q'\) is divisible by four. If both are even, both are two modulo four and their difference is divisible by four. If both are odd, their product is a square only when their residues modulo four agree, again making the difference divisible by four. If exactly one is even, their product is two modulo four and cannot be a square.

Therefore one required row-1 black cell lies in another column divisible by four. All such columns in the finite board are doubles. If the row-1 point is absent there, the support is broken. If it is present, the support involves that second double label. Either way it is not a one-label support.

## 3. Vertical rivals and the resulting reduction

A black diagonal joining a row-1 point to a higher point has no integral vertical alternative inside the strip: its length strictly exceeds its vertical displacement, so the lower endpoint of the vertical alternative lies below row 1. A same-row boundary diagonal has the same problem. The two points of one double form a vertical diagonal and cannot have a different vertical alternative. Hence no isolated virtual vertical-axis rival remains.

Axis-axis uniqueness follows from the unique complete bipartite double-edge family. The preceding arguments prove the proposition.

In particular, it would suffice to order the \(q\) labels in these \(q\) fixed double slots so that the resulting board has no three-black tilted rectangle, no nonvertical mixed four-cell support, and no opposite-parity vertical rival. All such tests involve at least two labels. This is a finite permutation problem with every singleton already filled, rather than an incomplete double-only scaffold.

No ordering theorem is proved here. Nor does a valid ordering at width \(4q\) automatically give every larger width: adding a row-1 tail creates unoccupied columns divisible by four, so the shielding argument can fail at the new boundary. Both the ordering and an extension mechanism remain necessary for a threshold theorem.
