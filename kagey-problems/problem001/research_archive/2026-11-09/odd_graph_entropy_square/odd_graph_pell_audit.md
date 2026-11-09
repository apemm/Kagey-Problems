# Audit of the anchored Pell obstruction

9 November 2026. The anchored theorem, local-constancy corollary, and positive
edge parametrization in [odd_graph_progress.md](odd_graph_progress.md) are
correct. The argument does not resolve bounded chromatic number.

## 1. The Pell construction

The matrix

\[
 A=\begin{pmatrix}9&20\\4&9\end{pmatrix}
\]

preserves \(X^2-5Y^2\) and has determinant one. Thus its reduction modulo
\(10M\) belongs to a finite group. Some positive integer \(t\) satisfies
\(A^t=I\pmod{10M}\). Applying \(A^{jt}\) to \((1,1)\), for
\(j\ge1\), gives positive solutions of norm \(-4\), with both coordinates
congruent to 1 modulo \(10M\). All entries of \(A\) are positive, so these
solutions increase strictly.

Write \(X=1+10Mk\). Then

\[
 z=\frac{X+4}{5}=1+2Mk
\]

is an odd integer greater than one. Substitution into the norm equation
gives

\[
 (5z-4)^2-5Y^2=-4
 \quad\Longleftrightarrow\quad
 5z^2-8z+4=Y^2
 \quad\Longleftrightarrow\quad
 z^2+4(z-1)^2=Y^2.
\]

For every nonzero odd anchor \(v\), the point \(w=zv\) is an odd integer
of the same sign, is congruent to \(v\) modulo \(M\), and satisfies

\[
 w^2+4(v-w)^2=(vY)^2.
\]

Strict growth of \(z\) gives infinitely many distinct such neighbors with
unbounded absolute value. The displayed example \(z=105\), \(Y=233\)
also satisfies the identity.

## 2. The continuity and digit consequences

If a coloring is constant on a congruence neighborhood of even one anchor
\(v\), the theorem gives a same-colored neighbor inside that neighborhood.
Therefore a proper coloring cannot be locally constant at any vertex.
The proof does not require the palette to be finite.

A deterministic rule that reads finitely many lower \(p\)-adic digits before
halting at \(v\) has a finite computation trace. Every input agreeing on
those digits follows the same trace and gets the same color. The largest
queried digit position therefore supplies a congruence neighborhood on which
the color is constant. Adaptive stopping does not avoid the obstruction.
The same argument applies to finitely many fixed primes.

For the valuation claim, if \(F(v)\ne0\), set \(e=v_p(F(v))\). To fix
this valuation and the first \(r\) unit digits, it suffices to require
\(x\equiv v\pmod{p^{e+r}}\). Integer polynomials respect this congruence,
so

\[
 F(x)\equiv F(v)\pmod{p^{e+r}}.
\]

This fixes both the valuation and the unit residue. Intersecting finitely
many such neighborhoods handles a finite collection of data. The stated
qualification about nonzero polynomial values is appropriate.

These arguments concern access to lower digits of an infinite \(p\)-adic
stream. A finite binary representation also supplies its end position, which
is different information. Rules using representation length, unrestricted
factorization, or digit depths depending on a finite interval are not ruled
out by this argument.

## 3. Positive edge parametrization

Fix the orientation

\[
 u^2+4(v-u)^2=s^2,
 \qquad u,v>0\text{ odd},\quad u\ne v.
\]

Let \(g=\gcd(u,2|v-u|)\). It is positive and odd. Dividing the two legs
by \(g\) gives a primitive integer right triangle with odd leg \(u/g\)
and even leg \(2|v-u|/g\). Hence there are coprime integers \(m>n>0\)
of opposite parity such that

\[
 u=g(m^2-n^2),\qquad |v-u|=gmn,
 \qquad s=g(m^2+n^2).
\]

This is exactly the claimed formula with either sign and with \(v>0\).
Conversely, the formulas give the square identity. Opposite parity of
\(m,n\) makes \(m^2-n^2\) odd and \(mn\) even, so both colored values
are odd. For an edge of the symmetrized graph, one might first need to swap
\(u\) and \(v\) to obtain this orientation.

The signed-versus-positive chromatic inequalities also hold. Negation is a
graph automorphism, and disjoint palettes handle the two signs. Compactness
for a fixed finite palette follows from the finitely branching tree of
proper colorings of successive finite positive intervals.

## 4. Why the chromatic question remains open

The local-neighbor property alone does not imply unbounded chromatic number.
For an abstract countermodel on the same odd-integer vertex set, partition
vertices by the parity of \(\lfloor\log_2|v|\rfloor\), then put an edge
between every pair in opposite parts. This graph is bipartite. Every
congruence class nevertheless contains arbitrarily large same-sign vertices
in both parts, since the corresponding dyadic intervals grow without bound.
Thus every vertex has arbitrarily large neighbors in every congruence
neighborhood. This is not a coloring or subgraph claim about the actual
Pythagorean graph. It only isolates the logical limit of the anchored
property.

The cited [Frantzikinakis--Klurman--Moreira
paper](https://arxiv.org/html/2407.08360v2) states its partition and density
regularity conclusions on the positive integers. Its binary-form results
do not directly supply the odd-input restriction needed here. The report
correctly treats such a restriction as an additional step, rather than
claiming that the cited theorem settles this graph.

No finite enumeration or additional computational assumption enters this
audit.
