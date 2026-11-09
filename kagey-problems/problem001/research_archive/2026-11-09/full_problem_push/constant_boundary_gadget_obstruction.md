# A horizontal rival defeats the constant boundary gadget

9 November 2026. A single opposite-parity double cannot in general be inserted into a sea whose every singleton is row 1. The following family is an exact obstruction, not a numerical search result.

Let the double column be zero and let its odd endpoint be \(2k+1\), where \(k\ge2\) and \(2k+1\le h\). Its even endpoint can be any permitted even row. All other columns have their black cell in row 1.

Define
\[
\begin{aligned}
P&=(0,2k+1),& Q&=(k^2-1,1),\\
W&=(-1,k+1),& Z&=(k^2,k+1).
\end{aligned}
\]
The pairs \(P,Q\) and \(W,Z\) have the same midpoint, and both have length \(k^2+1\), because
\[
(k^2-1)^2+(2k)^2=(k^2+1)^2.
\]
They are distinct diagonal pairs, so
\[
R=\{P,Q,W,Z\}
\]
is a nondegenerate tilted rectangle. Its black corners are exactly \(P,Q\), and its white presentation is \(\{W,Z\}\).

The axis rectangle
\[
T=\{(-1,1),(k^2,1),W,Z\}
\]
has the same white presentation. All relevant rows lie between 1 and \(2k+1\). The two rectangles use columns from \(-1\) through \(k^2\), and the three required row-1 sea cells are at offsets
\[
-1,\qquad k^2-1,\qquad k^2.
\]
The even point in the central double lies in neither rectangle, so its choice has no effect.

For \(k=2\), the tilted rectangle is
\[
\{(0,5),(3,1),(-1,3),(4,3)\},
\]
and its axis rival uses the row-1 cells in columns \(-1,4\). Thus a double such as \(\{2,5\}\) already defeats the proposed gadget.

More generally, every factorization \(pq=k^2\) with \(p,q>0\), \(p\ne q\), gives a black diagonal \((0,2k+1),(q-p,1)\), horizontal white diagonal \((-p,k+1),(q,k+1)\), and the same type of axis rival. A successful sea-filling rule must break these divisor-indexed supports.

This obstruction does not affect the proved monotone-gadget constructions. The separate note [quadratic_influence_barrier.md](quadratic_influence_barrier.md) shows that requiring all of their private influence sets to be disjoint incurs an \(\Omega(h^2\log h)\) width cost. Compatible overlaps or partial prescriptions remain possible ways around that cost.
