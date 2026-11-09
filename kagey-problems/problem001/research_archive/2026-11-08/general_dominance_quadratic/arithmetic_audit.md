# Audit of the double-only arithmetic construction

8 November 2026. This independently checks Theorem 2 in [quadratic_arithmetic.md](quadratic_arithmetic.md).

The theorem is correct as stated: the prescribed double cells alone form an identifying set of width \(O(h^{5/2})\). The proof does not establish an equality board, because all other columns remain empty of black cells.

## Divisibility checks

Let \(S\) be the least power of two with \(S^2>4h\). Every marked horizontal coordinate is divisible by \(S\).

For a tilted right angle, a same-parity nonzero vertical difference has absolute value less than \(S^2\). Multiplying it by an odd vertical difference cannot produce a multiple of \(S^2\). This validates the mixed-parity valuation argument. When all three rows have one parity, reduction modulo \(p\) or \(q\) has coefficient \(S^2+4\), which is nonzero because the prime exceeds that coefficient. The row-index differences are smaller than the prime, so a modular zero is an actual zero.

For a vertical pair of opposite-parity rows, both the diagonal length \(L\) and its black vertical component \(d\) are odd. Since \(X\ne0\), \(L>|d|\). Exactly one positive factor \(L-d,L+d\) has valuation one. The other must be at least \(S^2/2>2h\), while both are at most \(2(h-1)\). There is no sign or zero-factor exception.

In an oblique mixed side/diagonal collision, if both vertical increments are odd, the same valuation argument forces equal absolute vertical increments. The orthogonality equation then gives \(S^2\mid H_y\), so \(H_y=H_x=0\), which is degenerate.

If all four rows have the same parity, the bounds on \(t+u,t-u,L\) in the CRT argument are indeed strictly below \(h<p,q\). Thus its two congruences imply the asserted integer identities.

For two pairs of opposite row parities, write
\[
 U_y=2t,\quad V_y=2u,\quad H_y=2L,\quad K=S^2/4.
\]
The equations give
\[
 K\mid u^2-t^2,\qquad K\mid Lt.
\]
The first implies \(t,u\) have the same parity. The explicit row formulas give \(L+t+u\) odd, hence \(L\) odd. Since \(K\) is a power of two, \(K\mid t\). The bound \(0<|t|<h/2<K\) gives the contradiction. This covers the parity case that cannot be settled by a single CRT modulus.

The horizontal-rival argument also has the required strict gap: two marked points at the same row have physical separation at least \(S\min(p,q)\). If the tilted diagonal has horizontal separation \(Se\), its nonzero vertical component satisfies
\[
 v^2=S^2(d^2-e^2)\ge S^2(2d-1)>h^2.
\]
This remains valid when \(e=0\).

## Completeness of the collision classification

If one colliding rectangle is tilted and the two rectangles share at most one corner, at least three tilted corners must be marked, which is impossible. If they share two corners and either common corner is marked, the same three-marked-corners obstruction applies. Their common corners are therefore genuinely white.

Common sides or common diagonals give a hidden rectangle on the four complementary marked corners. The mixed case is exactly the oblique, vertical, or horizontal case checked in the theorem.

For two axis rectangles, a shared diagonal determines the rectangle. A vertical two-point presentation identifies its unique parity edge column. A horizontal two-point presentation in two distinct rectangles would repeat one double edge in two columns.

For a singleton presentation at \((x,r)\), any realizing axis rectangle uses another row \(s\), a marked point \((x,s)\), and the uniquely occurring edge \(\{r,s\}\) in its other column. Two different realizations either repeat that edge or require two distinct rows \(s,t\) of the same parity in column \(x\). The construction has one odd and one even marked row per occupied column, so the latter is impossible.

There are no hidden rectangles. This completes all possible collisions.

## Limitation of a completion argument

Identification of a partial marked set does not by itself guarantee that every empty column has a permissible singleton fill. If two three-black tilted rectangles complete at different rows of opposite parity in one empty column, their singleton presentations are distinct before filling. Once the full parity edge set occurs elsewhere, every singleton choice in that column creates an axis rival with at least one of those presentations.

An eventual sea-completion proof must prevent such opposite-parity completion pairs, in addition to retaining the double-only collision exclusions proved here.
