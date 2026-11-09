# Arithmetic spacing gives a boundary star in width \(h^{3/2+o(1)}\)

9 November 2026. A counting choice of spacing improves the [uniform \(h^{5/3}\) construction](boundary_star_five_thirds_gadget.md). There is also a matching exponent obstruction for every spacing, not only for square spacings.

Use row one in every column and add the complete boundary star
\[
 (pi,2i+2),\qquad 0\le i<\lfloor h/2\rfloor,
 \tag{1}
\]
where \(4\mid p\). Validity is tested relative to the complete parity pair set, with arbitrary constant row-one tails.

**Theorem.** For every height \(h\), there is an admissible spacing
\[
 p=h^{1/2+o(1)}
\]
for which (1) is hidden-free and identifying. Its core width is
\[
 h^{3/2+o(1)}.
 \tag{2}
\]
Conversely, every spacing divisible by four produces a mixed collision by height \(p^2/2\), including the constant tail. Thus every valid full boundary star of this form has \(p>\sqrt{2h}\). The width exponent \(3/2\) is optimal for this family, up to the subpolynomial factor in (2).

This result still places only the boundary star. It is not a complete equality-threshold construction.

## 1. A small divisor set covers all bad spacings

The preceding proof excludes every possible collision except crossed mixed four-cell supports. Every such support supplies positive integers \(z,D,k\) with
\[
 k(pD-2z)=z^2+D^2,\qquad D\mid z^2,
 \tag{3}
\]
and its lower extra height \(a\) satisfies
\[
 a=\frac{z(pD+k)}D>pz.
 \tag{4}
\]
In particular, a collision in height \(h\) has \(z<h/p\).

Define
\[
 T_h=\max_{1\le u\le 2h^2}\tau(u),\qquad
 P=\max\left(16,\left\lceil8\sqrt h\,T_h\right\rceil\right).
 \tag{5}
\]
Consider candidate spacings \(p\in[P,2P]\) divisible by four.

For any bad candidate, (4) gives \(1\le z<h/P\). Since \(P\ge\sqrt h\), we have \(z^2\le h\). For each \(z\), there are at most \(T_h\) choices of \(D\mid z^2\), and \(D\le z^2\le h\). Then
\[
 z^2+D^2\le h+h^2\le2h^2.
\]
Equation (3) makes \(k\) a positive divisor of this integer, with at most \(T_h\) choices. Finally, the triple \((z,D,k)\) determines at most one candidate spacing:
\[
 p=\frac{2z+(z^2+D^2)/k}{D}.
 \tag{6}
\]
Therefore the number of bad candidates is at most
\[
 \frac hP T_h^2\le \frac P{64}.
 \tag{7}
\]
The interval \([P,2P]\) contains at least \(P/4-1>P/64\) multiples of four. One of them is therefore good.

This counts a superset of the bad spacings: nonintegral values in (6), incorrect parities, and triples violating other geometric conditions can simply be discarded. No sufficiency claim for arbitrary parameter triples is needed.

The standard elementary maximal-divisor bound gives \(T_h=h^{o(1)}\). One proof is to fix \(\varepsilon>0\), absorb the finitely many primes below \(2^{2/\varepsilon}\) into an \(O_\varepsilon(n^{\varepsilon/2})\) factor, and use \(e+1\le p^{\varepsilon e/2}\) for the remaining prime powers. Thus \(\tau(n)\le C_\varepsilon n^\varepsilon\), uniformly in \(n\), which is enough for the asserted little-o exponent. Equations (5)--(7) give \(p\le2P=h^{1/2+o(1)}\), proving (2).

The choice is finite and constructive: enumerate the displayed triples, mark their integral candidate values, and select an unmarked multiple of four. Efficiency of that enumeration is not claimed.

## 2. Every spacing has a quadratic-height obstruction

Let \(p\ge4\) be divisible by four and put
\[
 D=z=\frac{p-2}{2},\qquad k=1,\qquad
 a=pD+1,\qquad h_0=a+2D+1=\frac{p^2}{2}.
 \tag{8}
\]
Here \(D\) and \(a\) are odd. The two equations in (3) hold because
\[
 pD-2D=D(p-2)=2D^2=z^2+D^2.
\]

Set \(i=(a-1)/2\) and \(X=pi\). At height \(h_0\), the star contains
\[
 A=(X,a+1),\qquad C=(X+pD,h_0).
\]
Their indices are \(i\) and \(i+D=h_0/2-1\), so \(C\) is the last extra point. The baseline contains
\[
 B=(X+a,1),\qquad E=(X+p-1,1).
\]
Take the side pair \(B,A\) and the diagonal pair \(E,C\). Their vectors are
\[
 (-a,a),\qquad (a-p,a+2D),
\]
and have equal squared length \(2a^2\). Translating the side pair by \((D,D)\) is perpendicular to it and produces the common white pair
\[
 W=(X+a+D,D+1),\qquad Z=(X+D,a+D+1).
 \tag{9}
\]
Their midpoint is the midpoint of \(E,C\). Thus these are two distinct nondegenerate rectangles with the same presentation.

Both displayed rows are in \([1,h_0]\) and exceed one. The displayed column residues modulo \(p\) are
\[
 W_x\equiv D+1=p/2,\qquad Z_x\equiv D.
\]
They are nonzero, so neither displayed corner is an extra point. Both are white regardless of the other extra points.

The point \(W\) lies \(D+1\) columns after the last double. Thus (9) is an obstruction to the star with its constant tail at height \(h_0\). At height \(h_0+2\), one more extra column is present beyond \(W\), so the same collision lies entirely inside the bare block of doubles. It persists at every larger height.

Consequently even without tails, this collinear family needs spacing \(\Omega(\sqrt h)\); with the arbitrary-tail requirement it needs \(p>\sqrt{2h}\). Its full-star width is therefore \(\Omega(h^{3/2})\).

## 3. Scope and review

The counting argument uses the complete collision classification from the preceding boundary-star theorem, including virtual rivals through final parity edges. Hence its output is a filled, identifying boundary gadget, not merely an identifying set of double cells.

No statement is made that arbitrary interior stars have the same construction. Indeed, a constant baseline at an interior odd row \(r\), together with the edge \(\{r,r-1\}\), already gives the unit diamond with three black corners
\[
 (0,r-1),\quad(-1,r),\quad(1,r)
\]
and missing corner \((0,r+1)\). When \(3\le r<h\), the latter has a singleton rival through the opposite-parity row \(r\). Joining many interior stars therefore needs a different baseline or compatible local modifications.
