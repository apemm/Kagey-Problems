# Odd sea rows separate the unconditional P constraints

9 November 2026. Put every parity edge in a double column \(x=4j\). Permit arbitrary odd singleton rows in the other columns. Then every unconditional vertical-presentation obstruction has both black corners in double columns. Its constraints therefore depend only on the edge order.

Let two black points be \((x,r)\), \((z,s)\). A vertical diagonal with the same midpoint and length has endpoints
\[
\left(\frac{x+z}{2},\frac{r+s-L}{2}\right),\qquad
\left(\frac{x+z}{2},\frac{r+s+L}{2}\right),
\]
where
\[
L^2=(x-z)^2+(r-s)^2.
\]
The vertical pair belongs to the parity row graph exactly when \(L\) is odd. Its integral midpoint then makes \(r-s\) odd too. The difference of these two odd squares is divisible by eight, so \((x-z)^2\) is divisible by eight and hence \(x-z\) is divisible by four.

One of the black rows \(r,s\) is even. It must occur in a double column, since every sea row is odd. That column is divisible by four, and the preceding arithmetic forces the other black column to be divisible by four as well. This proves the reduction.

Conversely, for two double slots at distance \(d>0\), the forbidden row pairs are exactly those satisfying
\[
L^2=16d^2+(r-s)^2,\qquad L\text{ odd},\qquad
1\le\frac{r+s-L}{2}<\frac{r+s+L}{2}\le h.
\]
When this condition holds, the tilted rectangle and a vertical axis rival have equal presentations. If a prospective white point becomes black, the same rival remains or the tilted rectangle is hidden. Thus no sea choice repairs this event.

At height 9, the complete list is slot distance one and row pairs
\[
(2,5),\ (3,6),\ (4,7),\ (5,8).
\]
At height 15, the complete list is slot distance one and pairs
\[
(2,5),\ (3,6),\ldots,(11,14),
\]
together with slot distance three and pairs \((5,10)\), \((6,11)\).

`p_only_order_sat.py` computes the list directly from the displayed integer equation and solves the edge-permutation constraints. The height-15 instance is SAT in 0.015 seconds, with all 56 edges used once. `p_only_spacing4_h15.json` records and directly checks the order. This proves feasibility of the P-only ordering problem at height 15. It does not prove that the remaining presentations can be separated by a sea filling.

## P is not the full order-only condition

The height-15 P-free order starts with double labels
\[
69,\ 11\!\cdot\!14,\ 56,\ 7\!\cdot\!10
\]
at columns \(0,4,8,12\). These four labels already force a collision, independently of every sea cell. The tilted rectangle
\[
R=\{(0,6),(4,14),(12,10),(8,2)\}
\]
has three black corners. The vectors from \((4,14)\) to \((0,6)\) and \((12,10)\) are \((-4,-8)\) and \((8,-4)\), whose dot product is zero. Its only white corner is \((8,2)\), while \((8,5)\) is black in the same column.

The complete parity graph contains the pair \(\{2,5\}\) in another double column \(z\). The axis rectangle with columns \(8,z\) and rows \(2,5\) also has exactly the white point \((8,2)\). No sea filling can remove this collision. This gives an explicit four-double obstruction that passes every P-only constraint.

Accordingly, a construction must first avoid all obstructions supported entirely on double points, including these singleton rivals. The P reduction isolates one necessary subsystem; it does not reduce the full order-only subsystem to P alone.

## A one-cell repair at height nine

The constant-row-1 scaffold at height 9 is infeasible. Allowing every sea column to choose either boundary row 1 or 9 also remains infeasible in the completed 8.875-second run. However, one interior sea cell suffices if even rows are allowed.

Use the double order
\[
25,14,69,16,67,12,78,23,89,34,58,47,38,27,18,29,36,49,45,56.
\]
Keep all sea cells in row 1 except column 74, using zero-based columns, whose black point is in row 2. Double columns remain \(0,4,\ldots,76\). The result has width 77 and 97 black points. Direct enumeration checks all 123,104 rectangle presentations. The record is `constant_sea_h9_one_defect_check.json`.

The same solver proves that one or two exceptional odd sea rows cannot repair the constant sea, even when the entire edge order remains free. An unrestricted odd-sea pilot first reaches its 60-second cap with status `unknown`. A subsequent warm run finds a valid odd-sea board in 191.39 seconds. It uses rows 1 and 9 except for row 7 at zero-based sea columns 15 and 74. The record is `constant_sea_h9_cadical195_seed18_odd57.json`; independent black-pair completion verifies all 14,256 weak presentations in its companion `_pair_check.json`.

None of the four choices of constant row-1 or row-9 collars of length 17 on both sides preserves that particular board. `h9_odd_sea_collar_check.json` records explicit collisions. Thus the finite odd-sea example does not establish its extendability.
