# Higher-arity mixed supports have a power margin

9 November 2026. For mixed supports whose four black points are all
inserted label points, the relative template degrees satisfy
\[
 D_3=O_\varepsilon(h^{3+\varepsilon}),\qquad
 D_4=O_\varepsilon(h^{5+\varepsilon}).
\tag{1}
\]
Here \(D_k\) is incidence at a fixed parity label for a support
using exactly \(k\) distinct labels. Vertical black sides are
handled separately by the virtual vertical-rival family. At
\(n\asymp h^2\), both terms in (1) are below the
\(n^{k-1}\) permutation scales. This isolates the three-inserted-point
right-angle family as a different higher-arity problem; it is not a
full construction theorem.

The same-column completion calculation and all label multiplicities
have passed independent review in
[inserted_mixed_higher_arity_independent_audit.md](inserted_mixed_higher_arity_independent_audit.md).

## 1. A crossed pair in one column

A mixed support has black side \(AB\) and black diagonal \(CD\),
with
\[
 |B-A|^2=|D-C|^2,\qquad
 (B-A)\cdot(C+D-A-B)=0.
\tag{2}
\]
Fix distinct \(A,C\) in the same column. Translate them to
\(A=(0,0)\), \(C=(0,q)\), where \(0<|q|\le H=h-1\).
Write \(B=(x,b)\), \(D=(z,d)\), and set
\[
 s=x-z,\qquad t=d-q-b.
\]
Expanding (2) gives
\[
 s^2+t^2=4qb,\qquad xs=b(t+2q).
\tag{3}
\]
If \(s=0\), the second equation forces either \(b=0,t=0\)
or \(t=-2q,b=q\). The first case makes the diagonal rectangle
degenerate, and the second makes the side rectangle degenerate.
Neither is retained.

For \(s\ne0\), strip containment and the first equation give
\(|s|,|t|\le2H\). Integrality of the second equation implies
\[
 s\mid t^2(t+2q).
\tag{4}
\]
For each \(t\notin\{0,-2q\}\), its right side is a nonzero
integer of size \(O(h^3)\). There are \(h^{o(1)}\) signed
divisors \(s\), and each determines \(b,x,z,d\) through (3).
The two exceptional values of \(t\) have only \(O(h)\)
possible \(s\)'s. Consequently two fixed crossed points in one
column have \(O_\varepsilon(h^{1+\varepsilon})\) completions.

Combined with the distinct-column argument in
[crossed_codegree_and_avoidance.md](crossed_codegree_and_avoidance.md),
this gives the same two-point bound without a distinct-column
restriction on the fixed pair. If the fixed points constitute one
black pair, choose the equal-length vector in \(h^{o(1)}\) ways
and the perpendicular connector in \(O(h)\) ways. Thus that
role has the same bound as well.

## 2. One fixed point

The one-point bound is \(O_\varepsilon(h^{2+\varepsilon})\),
also without requiring all black columns to be distinct. For an
oblique side, write
\[
 U=k(u,v),\qquad T=l(-v,u),\qquad (u,v)=1,
\]
where \(u,v,k,l\ne0\). Strip containment gives
\(|kv|\le H\), \(|lu|\le H\). Summing the scale choices
over primitive directions costs at most
\[
 O\left(H^2\sum_{1\le |u|,|v|\le H}\frac1{|uv|}\right)
 =O(h^2\log^2h).
\]
The alternative diagonal of length \(|U|\) has
\(h^{o(1)}\) integer directions. Fixing one prescribed black
point determines the translation, regardless of its role.

For a horizontal black side, write its length as \(u\) and the
other diagonal vector as \((r,s)\), with \(s\ne0\).
Then \((u-r)(u+r)=s^2\), \(|s|\le H\). There are
\(O(h^{1+\varepsilon})\) choices of \(u,r,s\), and
\(O(h)\) perpendicular vertical connectors. This gives the
same bound. A vertical black side is the separately retained
vertical-axis-rival role and is not included here.

## 3. Translate point codegrees into label degrees

For a four-label support, a fixed label supplies one selected point.
The one-point bound counts all relative point geometries. Each of
the other three labels has one unused endpoint, contributing at
most \(h^3\) choices. This gives \(D_4\ll h^{5+\varepsilon}\).

For a three-label support, exactly one label supplies two points.
If it is the fixed label, its two actual points are fixed in one
column. The two-point bound gives \(O(h^{1+\varepsilon})\)
geometries, and the two remaining labels have \(h^2\) possible
unused mates. If another label supplies the two points, use the
one-point bound and choose only the unused mate of the remaining
single-point label, a factor \(h\). Both cases give
\(D_3\ll h^{3+\varepsilon}\). Endpoint choices and pairings
cost only absolute constants.

If a vertical side consists of the two points of an inserted label,
its row pair already belongs to the final complete parity graph.
The other diagonal's two label points are exactly a virtual vertical
rival. Counting its owner as a third label would duplicate that
separate two-label constraint, so it is excluded from (1).

Together with the modulo-seven exclusion of three inserted points
and one sea point, (1) removes mixed four-cell supports from the
leading higher-arity budget in a quadratic-sized occupied block.
It does not remove vertical rivals, three-point right angles,
restored singleton collisions, or boundary interactions. In
particular it does not address the incidence lower bound in
[occupied_phase_three_label_incidence.md](occupied_phase_three_label_incidence.md).
