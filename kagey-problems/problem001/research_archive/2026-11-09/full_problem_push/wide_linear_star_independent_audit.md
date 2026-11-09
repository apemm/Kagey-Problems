# Audit of the wide linear boundary star

9 November 2026. Choose a multiple \(p\) of four with \(p>h\). Put a row-one
black point in every column, and add
\[
(pi,2i+2),\qquad 0\le i<\lfloor h/2\rfloor.
\tag{1}
\]
The doubles are precisely the row-one parity star. The construction is valid
against the complete parity graph for singleton and vertical rivals. Its
constant row-one tails can extend indefinitely in either direction. The
core width is \(p(\lfloor h/2\rfloor-1)+1=O(h^2)\) when \(p\) is the least
multiple of four exceeding \(h\).

The proof passes independent review. The following details make the mixed
case and its sign choices explicit.

## Singleton and axial cases

A three-black tilted rectangle has two added points and one baseline point.
A right angle at an added point would require
\(p(x-pi)=2(2i+1)\), impossible because \(p\) is divisible by four. If its
right angle is at the baseline point, the completion row determines
\(i+j\), its column determines that baseline point, and orthogonality then
determines \(ij\). Thus the unordered pair of added points is unique.

The completion row is odd. Its column cannot be a double column: otherwise
the baseline right-angle vertex is also a multiple of \(p\), and the two
nonzero horizontal legs have product of magnitude at least \(p^2>h^2\),
larger than the product of their vertical legs. Hence the completion is
above a retained row-one point of the same parity and has no singleton
axis rival.

A diagonal from the baseline to an added point has any vertical alternative
extend below the strip. A diagonal between added points has even vertical
length whenever integral, so its vertical alternative cannot have opposite
row parity. Its horizontal length would be
\(\sqrt{p^2+4}\,|i-j|\), which is irrational. These observations exclude
vertical and horizontal rivals of these types.

There is no hidden rectangle: three added points or three baseline points
are collinear, and two points on each of the two nonparallel lines cannot
form opposite sides or have diagonals with the same center row.

## The remaining mixed case

A mixed support with three added points and one baseline point has odd total
black row sum and cannot have integral shared white corners. Four points on
either line give degeneracy. Pairing two added points against two baseline
points would equate an irrational added-pair length with a horizontal integer
length. Thus the only remaining case pairs each added point with one baseline
point.

Subtract the baseline row and translate the first added point horizontally.
Write the two added points as
\[
(0,a),\quad(pD,b),\qquad a=2i+1,\quad b=a+2D.
\]
Suppose the first pair is the black side and the second is the black
diagonal. The common-white translation raises the side's baseline endpoint
by \(D\). Containment therefore forces \(D\ge0\). The case \(D=0\) shares
the same added point, which would give three common corners and identical
rectangles. Thus \(D>0\).

Let the side's baseline endpoint have coordinate \(U\), and write the
diagonal's horizontal component as \(V\). Equal lengths give
\(|V|<|U|\). Orthogonality is
\[
U(2pD-V-U)=2Da.
\tag{2}
\]
If \(U<0\), its second factor is positive because \(|V|<|U|\), contradicting
(2). Hence \(U>0\). Integral white corners give positive integers
\[
x=(U+V)/2,\qquad z=pD-x,
\]
with \(Uz=Da\). In particular \(1\le U\le Da\) and \(x\le U\). Therefore
\[
pD=x+z\le U+Da/U\le Da+1,
\]
where the last inequality follows from
\((U-1)(U-Da)\le0\). Consequently
\[
p\le a+1/D\le h,
\]
contrary to \(p>h\). This excludes the mixed case.

## Independent geometry checks

`verify_wide_linear_star.py` checks all heights four through thirty using
integer side and diagonal completion, including virtual full-parity
singleton and vertical rivals. Every case passes. Each core has a row-one
collar of length \(2W\) on both sides, where
\(W=1+\lfloor(h-1)^2/4\rfloor\). Every tilted collision touching the core
fits into this checked interval. The proof itself does not depend on the
finite checks or on horizontal endpoints.

This provides a complete \(O(h^2)\)-width block for the row-one edges. It does
not complete the bulk of the parity graph or prove that an arbitrary bulk
construction can be concatenated without appropriate collars and transition
conditions.
