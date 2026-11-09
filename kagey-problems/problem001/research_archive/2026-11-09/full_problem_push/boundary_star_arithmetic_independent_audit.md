# Independent audit of arithmetic boundary-star spacing

9 November 2026. The theorem in boundary_star_arithmetic_spacing.md passes
independent review.

The preceding collision classification applies to every spacing divisible
by four, without an assumption \(p>h\). Its singleton completion is in an
odd column, since the two vertical legs have odd product. This prevents a
singleton rival even when the spacing is small.

Every remaining mixed obstruction gives positive integers \(z,D,k\) with
\(z<h/p\), \(D\mid z^2\), and
\[
k(pD-2z)=z^2+D^2.
\]
For \(p\in[P,2P]\) and \(P\ge\sqrt h\), these imply \(z^2\le h\) and
\(z^2+D^2\le2h^2\). Choosing \(z,D,k\) determines at most one \(p\).
The estimate \(hT_h^2/P\le P/64\) therefore counts a superset of all bad
candidate spacings. The interval supplies at least \(P/4-1>P/64\) multiples
of four. The existence proof and the resulting width
\(h^{3/2+o(1)}\) are valid.

The universal obstruction at height \(h_0=p^2/2\) also checks. With
\(D=(p-2)/2\) and \(a=pD+1\), its side and diagonal vectors
\[
(-a,a),\qquad(a-p,a+2D)
\]
have equal squared norm. Translation by \((D,D)\) is perpendicular to the
side, and the common white pair has the same midpoint as the other
diagonal. The two marked extra indices are present at height \(h_0\).
The common white columns have residues \(D,D+1\) modulo \(p\), so neither
is an extra column. All displayed rows lie in the strip.

One white point uses the constant tail. Thus the strict spacing bound
\(p>\sqrt{2h}\) has the stated arbitrary-tail hypothesis. Increasing the
height by two places the same obstruction inside the bare double block.
The theorem proves optimal exponent \(3/2\) for this collinear
boundary-star family. It does not prove that exponent for a complete
parity-edge construction.
