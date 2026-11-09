# Hidden rectangles are impossible when both dimensions are at least four

Let \(V=[m]\times[h]\), let \(\mathcal R\) be the family of nondegenerate lattice rectangles with vertices in \(V\), and let \(S\subseteq V\) be black. A valid blackout requires the map

\[
R\longmapsto R\setminus S
\]

to be injective on \(\mathcal R\). The definition alone permits one empty presentation. Geometry rules out that possibility once both board dimensions are at least four.

**Theorem.** If \(h,m\ge4\), every valid blackout contains no fully black rectangle.

The proof gives a stronger certificate. For every rectangle \(R\), there are distinct rectangles \(T,U\) in the same board such that

\[
T\mathbin\triangle U=R.
\tag{1}
\]

Thus blackening all four vertices of \(R\) makes the presentations of \(T\) and \(U\) equal, regardless of the colors of their common vertices.

## Cross-reflection for a tilted rectangle

First suppose \(R=\{A,B,C,D\}\) is tilted and has an oblique diagonal \(AC\). Write

\[
A=(x,a),\qquad C=(z,c),\qquad x\ne z,\quad a\ne c,
\]

and define the crossed corners

\[
P=(x,c),\qquad Q=(z,a).
\]

The set \(T=\{A,C,P,Q\}\) is an axis-aligned rectangle. The pairs \(P,Q\) and \(B,D\) have the same midpoint and the same length, since each has the midpoint and length of the diagonal \(A,C\). They are therefore the diagonals of a rectangle

\[
U=\{P,Q,B,D\}.
\]

This rectangle is nondegenerate. Otherwise its two diagonal endpoint pairs would coincide, giving \(\{B,D\}=\{P,Q\}\) and making \(R\) axis-aligned. The same observation shows that \(P,Q\) are distinct from all four vertices of \(R\).

Both new rectangles lie in the original rectangle's axis-aligned bounding box. Their common vertices are exactly \(P,Q\), so (1) holds.

## Splitting a side at a lattice point

Suppose a side vector \(u\) of \(R\) is not primitive. Write \(u=g u_0\) with \(g\ge2\) and integral \(u_0\). Let the adjacent perpendicular side vector be \(v\), so

\[
R=\{A,A+g u_0,A+v,A+g u_0+v\}.
\]

Split the rectangle along the side joining \(A+u_0\) and \(A+u_0+v\). The two resulting rectangles are

\[
\begin{aligned}
T&=\{A,A+u_0,A+v,A+u_0+v\},\\
U&=\{A+u_0,A+g u_0,A+u_0+v,A+g u_0+v\}.
\end{aligned}
\]

They lie inside \(R\), share exactly the split side, and satisfy (1). The split does not need to bisect the side.

This handles any axis-aligned rectangle having a side of length at least two. It also handles every diamond

\[
\{(x-d,y),(x,y-d),(x+d,y),(x,y+d)\}
\]

with integer \(d\ge2\), because its side vectors are \((d,d)\) and \((d,-d)\).

## The two unit cases

An axis-aligned unit square extends by one unit in at least one horizontal direction when \(m\ge3\). Write it as

\[
R=\{A,A+u,A+v,A+u+v\},
\]

choosing its unit horizontal side \(u\) to point toward such an extension. The translated square

\[
T=R+u
\]

and the doubled rectangle

\[
U=\{A,A+2u,A+v,A+2u+v\}
\]

both fit in the board and satisfy (1).

The remaining tilted case has both diagonals axis-parallel. Equal diagonal lengths force it to be a diamond. Only the unit diamond remains after the splitting argument:

\[
R=\{(x-1,y),(x,y-1),(x+1,y),(x,y+1)\}.
\]

Its center has \(2\le x\le m-1\) and \(2\le y\le h-1\). Since \(m\ge4\), choose \(\sigma\in\{-1,1\}\) so that

\[
2\le x+\sigma\le m-1.
\]

Independently, since \(h\ge4\), choose \(\tau\in\{-1,1\}\) so that

\[
2\le y+\tau\le h-1.
\]

The vector \(u=(\sigma,\tau)\) is one of the unit diamond's directed side vectors. The translated diamond \(T=R+u\) fits in the board. Represent \(R\) with this directed side as

\[
R=\{A,A+u,A+v,A+u+v\},\qquad u\cdot v=0.
\]

The doubled rectangle \(U=\{A,A+2u,A+v,A+2u+v\}\) has all its vertices among the vertices of \(R\cup T\), so it also fits. Again \(T\triangle U=R\). This completes the proof.

## The dimension condition is necessary

On a \(3\times m\) board, \(m\ge3\), blacken just

\[
S=\{(c-1,2),(c,1),(c+1,2),(c,3)\},
\qquad 2\le c\le m-1.
\]

This is a valid blackout with one hidden unit diamond. Its axis incidence graph is a forest, so its axis presentations are distinct. Every tilted rectangle on a three-row board is a unit diamond: its two positive vertical side components must both be one, and perpendicularity then forces both horizontal side components to be one. A different unit diamond has at most one black vertex of \(S\), hence at least three white vertices. Such a presentation cannot coincide with any other rectangle's presentation. The original unit diamond alone has an empty presentation.

Thus the theorem does not extend to height three, even at arbitrarily large width. The transposed example handles width three.

## An exact forbidden-hypergraph description

For \(h,m\ge4\), form a hypergraph on the board cells whose edges are

\[
R\triangle T,
\qquad R,T\in\mathcal R,\quad R\ne T,\quad R\cap T\ne\varnothing.
\tag{2}
\]

Two distinct rectangles share at most two vertices, since three corners determine a rectangle. Therefore the edges in (2) have size four or six.

**Corollary.** A black set is valid exactly when it is independent in this 4- and 6-uniform hypergraph. There is no need for edges of size eight.

Necessity follows directly from equality of the two presentations. Conversely, independence in (2) excludes all fully black rectangles by (1), since the two witness rectangles in (1) share two vertices. If two disjoint rectangles had equal presentations, both presentations would be empty. This would give two fully black rectangles, already excluded. Every remaining presentation collision comes from intersecting rectangles and is excluded by (2).

This is an exact equivalence for general boards, including arbitrary double-column row partitions. It strengthens constructions that had imposed the absence of hidden rectangles as a sufficient extra condition. It also removes any exceptional hidden-rectangle flag from an exact finite-state model once both dimensions are at least four.

## Finite check accompanying the proof

For the \(7\times9\) board, `build_seven_nine_differences.py` independently enumerates all 1,113 rectangles and all pairwise symmetric differences. The distinct support counts are:

| Support size | All supports | Inclusion-minimal supports |
|---:|---:|---:|
| 4 | 3,947 | 3,947 |
| 6 | 82,921 | 73,952 |
| 8 | 466,951 | 0 |

These counts agree with the theorem. The proof applies to every height and width at least four and does not depend on the finite check.
