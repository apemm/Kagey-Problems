# A fixed-anchor obstruction beyond every linear buffer

9 November 2026. The short-buffer capture theorem cannot be upgraded
to an extension theorem for every admissible protected core with the
same prescribed anchor. This note gives an explicit family. It does
not obstruct an adaptive entrance path, a different anchor, or general
canonical-component capture.

## 1. Two prescribed protected cells can be completed

For all sufficiently large \(h\), any two prescribed cells in
distinct columns, compatible with one fixed protected law, occur
in a valid bi-infinite protected sea.

Use the four/six positive support language for that law and condition
the independent row choices on the two cells. The uniform extension
bounds in crossed_codegree_and_avoidance.md give
\[
 M_{4,j}\ll_\varepsilon h^{3-j+\varepsilon},\qquad
 M_{6,j}\ll_\varepsilon h^{5-j+\varepsilon}.
\]
For \(j=1,2\), the total conditional probability of supports containing
a specified set of \(j\) pins is \(O_\varepsilon(h^{-1+\varepsilon})\):
divide these counts by \(h^{4-j}\) or \(h^{6-j}\).
Supports avoiding the pins have the usual
\(O_\varepsilon(h^{-1+\varepsilon})\) incident weight at every
free column. There is no all-fixed forbidden support with only two
pins.

Consequently the product-form local lemma applies on every finite
interval containing the pins, uniformly in its length. Compactness
gives a bi-infinite completion. The language is normalized by required
black supports, so the conclusion includes possible common white
corners outside any chosen finite core.

## 2. An immutable mixed collision

Take \(u\equiv1\pmod4\), \(u>0\), and set
\[
 h=15u^2+2.
\]
Use the protected quadratic law
\[
 q(y)=q(x),\qquad q(t)=\binom t2\bmod2,
\]
whose low anchor is the period-four word \(1,1,2,2\), indexed so
that column zero has row one.

The two anchor points are
\[
 A=(0,1),\qquad C=(2u,2).
\]
Prescribe the two core points
\[
 B=(18u^3+3u,\,3u^2+1),\qquad
 D=(18u^3-u,\,15u^2+2).
\]
All four points obey \(q(y)=q(x)\). The pins lie in the stated
anchor: \(2u\equiv2\pmod4\). Both core columns are one modulo
four, while their rows are zero and one modulo four, respectively.
Thus both core cells belong to the allowed quadratic row class.

Put
\[
 U=B-A=(18u^3+3u,\,3u^2),\qquad
 T=(-u,\,6u^2+1),\qquad
 V=D-C=(18u^3-3u,\,15u^2).
\]
Direct calculation gives
\[
 U\cdot T=0,\qquad |U|^2=|V|^2.
\]
The common white points are
\[
 W=A+T=(-u,\,6u^2+2),\qquad
 Z=B+T=(18u^3+2u,\,9u^2+2).
\]
They satisfy \(W+Z=C+D\). Therefore
\(\{A,B,W,Z\}\) and \(\{C,D,W,Z\}\) are two distinct,
nondegenerate tilted rectangles. Their symmetric difference is
exactly the four black points \(A,B,C,D\).

All six row coordinates lie in \([1,h]\). Moreover, \(W\) and
\(Z\) violate \(q(y)=q(x)\), so they are white in every word
obeying this protected law. The same collision would persist even
without that last observation, because its symmetric difference
consists entirely of the four prescribed black cells.

## 3. Place the pair inside a valid core

End the fixed anchor tail at column \(2u\), put \(B_h\) variable
columns after it, and start the core at \(2u+B_h+1\).
The earlier of the two core points is \(D\), at distance
\[
 D_x-2u=18u^3-3u
       =\Theta(h^{3/2})
\]
from the last tail column. Hence, for every fixed constant \(C_0\),
both prescribed points lie inside the core when
\(B_h=\lceil C_0h\rceil\) and \(u\) is sufficiently large.

By Section 1, the two points have a valid bi-infinite protected
completion. Take a finite core from it, starting at the designated
position and long enough to contain \(B,D\) and to have length at
least the full memory bound \(L\). This is an admissible protected
core in exactly the support language used by the capture theorem.

Every filling of the variable buffer retains \(A,C,B,D\), so every
such extension has the collision above. The right buffer and right
tail cannot remove it.

Thus a fixed positive fraction of cores can extend through linear
variable buffers, while some admissible cores cannot extend through
those same buffers and anchor. The two statements are compatible.
No conclusion about the existence of another finite entrance path
for the obstructed core follows from this example.

## 4. The same obstruction for an all-odd core and constant row one

There is also an ordinary-parity family. Let \(n\) be a positive
integer and put
\[
 s=2n-1,\qquad p=2n^2,\qquad
 y=ps^2+2,\qquad x=py,\qquad
 v=y+2ps,\qquad h=v+1.
\]
Take constant-row-one tail points
\[
 A=(0,1),\qquad C=(1,1),
\]
and prescribe the two all-odd core points
\[
 B=(x,y+1),\qquad D=(x-2s-1,v+1).
\]
Both core rows are odd because \(p,y,v\) are even. Define
\[
 T=(-s,ps),\qquad
 W=A+T,\qquad Z=B+T.
\]
Then \(U=B-A=(py,y)\) satisfies \(U\cdot T=0\).
The other black diagonal is \(V=D-C=(x-2s-2,v)\).
The identity \(2p=(s+1)^2\) gives
\[
 \begin{aligned}
 x^2-(x-2s-2)^2
 &=4(s+1)(py-s-1)\\
 &=4ps(y+ps)=v^2-y^2.
 \end{aligned}
\]
Thus \(|U|=|V|\), while \(W+Z=C+D\).
The two rectangles with common corners \(W,Z\) are distinct and
nondegenerate. Every row lies in the strip.

Here \(W\) is white in the fixed tail. The core letter at \(Z\)
may be black or white; either way the two rectangles have the
same presentation, because their symmetric difference is
\(\{A,B,C,D\}\).

The first prescribed core point is at distance
\[
 D_x-1=x-2s-2=\Theta(n^6)=\Theta(h^{3/2})
\]
from the last fixed tail column. Section 1 supplies a valid
bi-infinite all-odd completion of \(B,D\) for sufficiently large
heights in this family. Taking a core from that completion proves
the same failure of universal extension through any prescribed
linear buffer to constant row one.

This version does not require a quadratic phase or a periodic
two-row anchor.
