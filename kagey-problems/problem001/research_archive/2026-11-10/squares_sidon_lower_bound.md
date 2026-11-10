# Square boards: structured host sets do not beat n^(6/5)

10 November 2026. Problem 001, square board. The question was whether the
host-set method of Janosik, Nador, Nagy and Simon (arXiv:2601.14465,
Theorem 3.7: rhombus-free sets of size \(n^{4/3}(\log n)^{-1/3}\) by
alteration inside \([1,n]\times T\), \(T\) a Sidon set) improves

\[
 f(n,n)=\Omega\bigl(n^{6/5}(\log n)^{-1/5}\bigr).
\]

**Outcome. No exponent above 6/5 is proved here.** The note proves that the
proposed family of hosts cannot give one, and it isolates what a host would
need. In short:

1. In \([n]\times T\) with \(T\) Sidon, every tilted obstruction family is
   small, as hoped. But the axis-parallel families are as large as possible,
   and every valid subset of \([n]\times T\) has at most
   \(n+\binom{|T|}{2}+1\le(3/2+o(1))n\) points (Theorem 2). The rhombus
   template survives only because axis-parallel rectangles are not rhombi.
2. For every product host \(A\times B\) the alteration method gives at most
   \(2(|A||B|)^{3/5}\le 2n^{6/5}\) points (Theorem 3). Inside a
   Sidon host it gives \(\Theta(n^{9/10})\).
3. For every host with at least \(Cn^{4/3}\) points the alteration method
   gives \(O(n^{6/5})\) (Theorem 4, modulo a cited supersaturation theorem).
4. No condition on the row set \(T\) reduces the tilted six-point count below
   the random count: \([n]\times T\) contains at least \(c|T|^6\) pairs of
   tilted right angles with a common completion (Theorem 5). A girth-eight
   axis graph placed in \([n]\times T\) with random labels has at least
   \(cN^6/n^6\) six-point obstructions in expectation (Theorem 6), which is
   again the exponent 6/5.

Section 7 states the exact requirement on a host that would beat 6/5 and
explains, heuristically, why all direction scales must be controlled at once.

Status labels: **[proved]** means a complete proof is given here.
**[proved, cited]** means the proof uses one theorem that I quote from the
literature file and did not check in the primary source.
**[heuristic]** means a count without proof.

## 0. Conventions

Cells are \((x,y)\) with column \(x\in[n]\) and row \(y\in[n]\). A host is a
set \(G\subseteq[n]^2\). Write \(m=|T|\), \(N=|G|\), and
\(d_{\max}=\max_{1\le k\le n^2}d(k)\), where \(d\) is the divisor function.
The divisor bound is \(d(k)\le C_\varepsilon k^\varepsilon\), so
\(d_{\max}\le C_\varepsilon n^{2\varepsilon}\).

A *right angle* in \(G\) is a set \(\{V;U,W\}\subseteq G\) of three distinct
cells with \((U-V)\cdot(W-V)=0\). Its vertex is \(V\) and its *completion* is
\(P=U+W-V\). Only completions in \([n]^2\) matter. The completion need not
lie in \(G\). Write \(r_G(P)\) for the number of right angles of \(G\) with
completion \(P\), and

\[
 \Pi(G)=\sum_{P\in[n]^2}\binom{r_G(P)}{2}.
\]

Two distinct right angles with the same completion \(P\) give two distinct
rectangles through \(P\) whose other corners lie in \(G\). They cannot share
three corners. If they share only \(P\), the six other corners are an (X)
obstruction. If they share \(P\) and one more corner, the four remaining
corners are an (H) or (F) obstruction. So a set \(S\) with \(\Pi(S)>0\) is
not valid (treating a hidden rectangle as forbidden).

The obstruction counts are counts of distinct point sets:
\(N_H(G)\) for rectangles in \(G\), \(N_F(G)\) for mixed four-point
configurations, \(N_X(G)\) for six-point configurations. A six-point set
arises from at most 10 pairs of right angles (one per split into two
triples), so \(N_X(G)\ge\Pi_1(G)/10\), where \(\Pi_1\) counts the pairs that
share exactly one corner.

The *alteration bound* of a host is

\[
 \mathrm{Alt}(G)=\max_{0\le p\le1}\Bigl(pN-p^4\bigl(N_H+N_F\bigr)-p^6N_X\Bigr).
 \tag{1}
\]

This is what the argument "keep each cell of \(G\) with probability \(p\),
delete one cell per surviving obstruction" proves. Up to constants,

\[
 \mathrm{Alt}(G)\asymp
 \min\Bigl(N,\ \frac{N^{4/3}}{(N_H+N_F)^{1/3}},\ \frac{N^{6/5}}{N_X^{1/5}}\Bigr).
 \tag{2}
\]

The linear-hypergraph refinement used in the note of 9 November changes (2)
by a power of \(\log n\) only. It needs the surviving six-uniform hypergraph
to have average degree \(T^5\) with \(T\) a small power of \(n\), and it
returns \(N'T^{-1}(\log T)^{1/5}\). No statement below is sensitive to
logarithms, so I do not carry it through.

## 1. The Sidon host: exact structure

Let \(T\subseteq[n]\) be a Sidon set (all differences \(a-b\), \(a\ne b\),
distinct) and \(G=[n]\times T\).

**Lemma 1.1 (rectangles) [proved].** Every rectangle with four corners in
\(G\) is axis-parallel, and \(N_H(G)=\binom n2\binom m2\).

*Proof.* Let the corners be \(P_1,\dots,P_4\) in cyclic order, with rows
\(y_i\). Then \(P_1+P_3=P_2+P_4\) gives \(y_1+y_3=y_2+y_4\). The Sidon
property gives \(\{y_1,y_3\}=\{y_2,y_4\}\), so \(y_1=y_2\) or \(y_1=y_4\).
A horizontal side makes the rectangle axis-parallel. The count is the number
of choices of two columns and two rows. \(\square\)

**Lemma 1.2 (right angles) [proved].** Write a right angle as
\(V=(x,b)\), \(U=(x+s,a)\), \(W=(x+t,c)\) with \(a,b,c\in T\) and

\[
 st+(a-b)(c-b)=0.
 \tag{3}
\]

The completion is \(P=(x+s+t,\ a+c-b)\).

* (a) Either the angle is axis-parallel (one arm horizontal, one vertical)
  or it is tilted, meaning \(s,t,a-b,c-b\) are all nonzero.
* (b) The number of axis-parallel right angles is \(nm(n-1)(m-1)\), and every
  one has its completion in \(G\).
* (c) The completion row of a tilted right angle is not in \(T\).
* (d) For each \(z\), at most \(m\) ordered row triples \((a,b,c)\) with
  \(a\ne b\ne c\) satisfy \(a+c-b=z\).
* (e) The number of tilted right angles is at most \(nm^3d_{\max}\).

*Proof.* (a) If \(s=0\) then \(a\ne b\), so (3) forces \(c=b\) and then
\(t\ne0\). The cases \(t=0\), \(a=b\), \(c=b\) are the same.
(b) Choose the vertex, another cell in its row and another in its column.
(c) If \(a+c-b=y\in T\) then \(a+c=b+y\), so \(b\in\{a,c\}\), which a tilted
angle excludes. (d) For fixed \(c\), \(a-b=z-c\). This is nonzero, so the
Sidon property leaves at most one pair \((a,b)\). (e) For ordered arms there
are at most \(m^3\) row triples, at most \(2d(|(a-b)(c-b)|)\) pairs \((s,t)\)
in (3), and at most \(n\) values of \(x\). Halve for unordered arms.
\(\square\)

**Lemma 1.3 (pairs of right angles) [proved].** In \(G=[n]\times T\):

* (a) Axis and axis. \(r^{\mathrm{ax}}_G(P)=(n-1)(m-1)\) if the row of \(P\)
  is in \(T\) and \(0\) otherwise. The six-point sets from these pairs are
  exactly the 6-cycles of the complete bipartite axis graph, and their number
  is \(6\binom n3\binom m3\).
* (b) Axis and tilted. There are none.
* (c) Tilted and tilted. The number of pairs is at most
  \(\tfrac12 d_{\max}^2\,nm^4\).

Hence

\[
 6\binom n3\binom m3\ \le\ N_X(G)\ \le\ 6\binom n3\binom m3+\tfrac12d_{\max}^2nm^4 .
 \tag{4}
\]

*Proof.* (a) An axis-parallel angle with completion \((x,y)\) consists of
\((x,y'),(x',y'),(x',y)\), so \(y\in T\), and \((x',y')\) is free with
\(x'\ne x\), \(y'\ne y\). Two such angles with \(x_1'\ne x_2'\) and
\(y_1'\ne y_2'\) form a 6-cycle on three rows and three columns. Conversely
a 2-regular bipartite graph on \(3+3\) vertices is one 6-cycle, so distinct
6-cycles are distinct six-point sets. \(K_{3,3}\) has 6 Hamiltonian cycles.
(b) By Lemma 1.2 the completion row of an axis angle is in \(T\) and that of
a tilted angle is not. (c) By Lemma 1.2(d) the number of ordered pairs of
ordered row triples with equal completion row is at most
\(m\cdot m^3\). Each triple has at most \(2d_{\max}\) column pairs
\((s,t)\). The column \(x\) of the first vertex is free and the second is
then fixed by the completion column. This gives \(4d_{\max}^2nm^4\) ordered
objects, and each unordered pair of unordered angles is counted 8 times.
\(\square\)

**Lemma 1.4 (mixed four-point configurations) [proved].** Write an (F)
configuration as \(A=(x,a)\), \(B=(x+s,b)\) (the side) and \(C=(x',c)\),
\(D=(x'+s',d)\) (the diagonal). The conditions are

\[
 s^2+(b-a)^2=s'^2+(d-c)^2,\qquad
 (2x'+s'-2x-s)\,s+(c+d-a-b)(b-a)=0,
 \tag{5}
\]

with shared corners \(P=A+w\), \(Q=B+w\), \(w=\tfrac12(C+D-A-B)\ne0\)
integral and \(P,Q\in[n]^2\). In the Sidon host every such configuration has
\(|d-c|\ne|b-a|\) and \(s\ne0\), and

\[
 N_F(G)\le\tfrac12\,d_{\max}\,nm^4 .
 \tag{6}
\]

*Proof.* Put \(K=(d-c)^2-(b-a)^2\), so \((s-s')(s+s')=K\). Suppose \(K=0\).
Then \(s'=\pm s\). If \(a=b\) then \(c=d\) and \(s\ne0\), and the second
equation in (5) gives \(\{C,D\}=\{A+(0,c-a),B+(0,c-a)\}=\{P,Q\}\), which is
degenerate. If \(a\ne b\), the Sidon property gives \(\{c,d\}=\{a,b\}\).
With \((c,d)=(a,b)\): \(s'=s\) forces \(x'=x\), so \(C=A\). And \(s'=-s\)
forces \(x'=x+s\), so \(w=0\). The case \((c,d)=(b,a)\) is the same with
\(C,D\) exchanged. (These two steps divide by \(s\). If \(s=0\) and \(K=0\)
then \(s'=0\), so \(C,D\) lie in one column on the rows \(a,b\), and
\(\{C,D\}=\{P,Q\}\).) Finally, if \(s=0\) and \(K\ne0\), then (5) gives
\(c+d=a+b\), the Sidon property gives \(\{c,d\}=\{a,b\}\), and \(K=0\), a
contradiction. So \(K\ne0\) and \(s\ne0\). For
ordered \((A,B,C,D)\) there are at most \(m^4\) row choices, at most
\(2d(|K|)\) pairs \((s,s')\), at most \(n\) values of \(x\), and \(x'\) is
then determined by (5). Each configuration is counted 4 times. \(\square\)

**Summary of Section 1.** With \(m\asymp n^{1/2}\):

| family | count in \([n]\times T\) | order |
|---|---|---|
| \(N_H\), axis rectangles | \(\binom n2\binom m2\) | \(n^3\) |
| tilted rectangles | \(0\) | |
| \(N_F\) | \(\le\frac12d_{\max}nm^4\) | \(\le n^{3+\varepsilon}\) |
| \(N_X\), axis 6-cycles | \(6\binom n3\binom m3\) | \(n^{9/2}\) |
| \(N_X\), axis with tilted | \(0\) | |
| \(N_X\), tilted with tilted | \(\le\frac12d_{\max}^2nm^4\) | \(\le n^{3+\varepsilon}\) |

For comparison, a uniformly random set of the same density \(n^{-1/2}\) has
about \(n^{3}\) tilted six-point configurations (up to logarithms), so the
Sidon rows do not lower the tilted-tilted count. They remove tilted
rectangles and axis-tilted pairs. The completion point is free to leave the
host, exactly as anticipated.

## 2. The Sidon host is capped at linear size

**Theorem 2 [proved].** Let \(T\subseteq[n]\) be any set of \(m\) rows. Every
\(S\subseteq[n]\times T\) with no axis-parallel rectangle has
\(|S|\le n+\binom m2\). Consequently every valid \(S\subseteq[n]\times T\)
has \(|S|\le n+\binom m2+1\). If \(T\) is Sidon this is at most
\((3/2+o(1))n\).

*Proof.* Let \(d_x\) be the number of cells of \(S\) in column \(x\). Two
rows share at most one column, so \(\sum_x\binom{d_x}{2}\le\binom m2\).
Since \(d-1\le\binom d2\) for every integer \(d\ge0\),
\(|S|-n\le\sum_x(d_x-1)\le\binom m2\). A valid set contains at most one
rectangle; remove one of its corners. A Sidon set in \([n]\) has
\(m\le n^{1/2}+n^{1/4}+1\). \(\square\)

A full row is valid, so the truth inside a Sidon host is \(\Theta(n)\).

With the girth-eight bound (Neuwirth, Proposition 17, as recorded in
`LITERATURE_right_angles.md`: a bipartite graph on \(v+w\) vertices with no
4-cycle and no 6-cycle has at most \(2^{1/3}(vw)^{2/3}\) edges when
\(\max(v,w)\le\lfloor\min(v,w)^2/4\rfloor\)), the same argument gives:

**Corollary 2.1 [proved, cited].** A valid subset of \(A\times B\) has at
most \(2^{1/3}(|A||B|)^{2/3}+1\) points in that range. To exceed
\(n^{6/5}\) inside \([n]\times T\) one needs \(|T|\ge n^{4/5}/\sqrt2\). A set
of that size has some difference repeated at least \(cn^{3/5}\) times, so it
is far from Sidon.

This is the difference from the rhombus problem. There the axis-parallel
members of the forbidden family are squares only, so the complete bipartite
structure of \([1,n]\times T\) is harmless. Here the axis graph of \(S\) must
have girth at least eight.

## 3. Alteration in product hosts

**Theorem 3 [proved].** For \(A,B\subseteq[n]\) with \(|A|=a\), \(|B|=b\),
\(a,b\ge6\),

\[
 \mathrm{Alt}(A\times B)\le 24^{1/5}\,(ab)^{3/5}\le 2\,n^{6/5}.
\]

*Proof.* As in Lemma 1.3(a), every 6-cycle of the complete bipartite axis
graph is a distinct (X) obstruction, so
\(N_X(A\times B)\ge6\binom a3\binom b3\ge a^3b^3/24\) for \(a,b\ge6\).
The bracket in (1) is positive only if \(p^5a^2b^2/24<1\), and then
\(pab<24^{1/5}(ab)^{3/5}\). \(\square\)

So the exponent of the alteration method in \([n]\times T\) with
\(|T|=n^\mu\) is at most \(3(1+\mu)/5\). It equals \(6/5\) only for
\(\mu=1\), the unstructured grid.

**Proposition 3.1 (Sidon host) [proved].** If \(T\) is Sidon with
\(m\asymp n^{1/2}\) then \(\mathrm{Alt}([n]\times T)=\Theta(n^{9/10})\).

*Proof.* The upper bound is Theorem 3. For the lower bound take
\(p=c(nm)^{-2/5}\). By the table in Section 1, with \(N=nm\):
\(p^4N_H/(pN)\asymp p^3nm\to0\),
\(p^4N_F/(pN)\le p^3m^3d_{\max}\le n^{-3/10+\varepsilon}\),
the tilted part of \(p^6N_X/(pN)\) is at most
\(p^5m^3d_{\max}^2\le n^{-3/2+\varepsilon}\), and the 6-cycle part is
\(p^5n^2m^2/6=c^5/6\). \(\square\)

The exponent \(9/10\) is below the trivial exponent \(1\) and far below
\(6/5\). The six-point family is still the bottleneck, but now through its
axis-parallel members.

## 4. Alteration in arbitrary large hosts

**Theorem 4 [proved, cited].** There are absolute constants \(C,C'\) such
that every host \(G\subseteq[n]^2\) with \(N\ge Cn^{4/3}\) has
\(N_X(G)\ge cN^6/n^6\) and \(\mathrm{Alt}(G)\le C'n^{6/5}\).

*Proof.* The axis graph of \(G\) has \(2n\) vertices and \(N\) edges. The
supersaturation theorem for even cycles (Jiang and Yepremyan, quoted as item
C2 of the literature file) gives at least \(c(N/n)^6\) copies of \(C_6\).
Each is a distinct (X) obstruction. Then (1) is positive only if
\(p^5N^5<n^6/c\). \(\square\)

So a host that beats 6/5 by alteration has
\(n^{6/5}<N\le Cn^{4/3}\). It is at most as large as the conjectured optimum
and the sampling probability is at least \(n^{-2/15}\). The host must already
be close to valid. This rules out the "large host, heavy sparsification"
shape of the rhombus argument.

## 5. No row condition lowers the tilted six-point count

Section 1 suggests replacing "Sidon" by a weaker condition (bounded
difference multiplicity, \(B_3\), distinct values of \(a+c-b\)) on a larger
row set. The next theorem shows that the row set cannot help.

**Theorem 5 [proved].** There are absolute constants \(c,C\) such that for
every \(T\subseteq[n]\) with \(m=|T|\ge Cn^{1/2}\), the host
\(G=[n]\times T\) contains at least \(cm^6\) pairs of tilted right angles
with a common completion in \([n]^2\) and with six distinct rows and six
distinct columns among their six cells. In particular
\(N_X(G)\ge cm^6/10\) from tilted pairs alone.

*Proof.* Cut \([1,n]\) into 32 intervals of length at most
\(\lceil n/32\rceil\). One of them, \(I\), contains \(k\ge m/32\) elements
of \(T\). For \(a<b<c\) in \(T\cap I\) with \(c-b\ne b-a\) and
\(1\le x\le n-2\lceil n/32\rceil\) take

\[
 V=(x,b),\quad U=(x+c-b,\ a),\quad W=(x+b-a,\ c),\quad
 P=(x+c-a,\ a+c-b).
\]

The arms are \((c-b,a-b)\) and \((b-a,c-b)\), which are perpendicular, and
all four coordinates of the arms are nonzero. The three cells have distinct
rows, and distinct columns because \(c-b\ne b-a\). All cells lie in
\([n]\times T\), and \(P\) lies in \([n]\times I\) because \(a<a+c-b<c\).
This gives \(R\ge(\binom k3-k^2)\,n/2\) distinct tilted right angles whose
completions lie in a set of at most \(n\lceil n/32\rceil\le n^2/16\) cells.
By convexity the number of pairs with a common completion is at least
\(\tfrac12R\,(16R/n^2-1)\ge cm^6\) once \(m^3\ge C'n\).

A pair fails the distinctness condition only if a row or a column of one
angle equals a row or a column of the other. Fix the first angle, at most
\(k^3n\) choices. The second has the same completion, so its vertex column
is determined by its rows and its three rows satisfy \(a'+c'-b'=a+c-b\).
Each coincidence is one more linear condition on \((a',b',c')\), leaving at
most \(k\) choices. There are at most 18 coincidences, so at most
\(18k^4n\) pairs fail. This is at most half of \(cm^6\) once
\(m\ge Cn^{1/2}\). Pairs with six distinct rows share only the corner \(P\),
so each gives an (X) obstruction, and a six-point set comes from at most 10
pairs. \(\square\)

The random count at density \(m/n\) is \(n^6(m/n)^6=m^6\) up to logarithms.
So for every row set of size at least \(Cn^{1/2}\) the tilted six-point
count of \([n]\times T\) is at least a constant times the random count.
The reason is that the family used in the proof (two arms obtained from each
other by a quarter turn) exists for every row triple, and the completion
rows \(a+c-b\) with \(a<b<c\) stay inside the grid. A "weak Sidon condition
for \(a+c-b\)" can only hold up to \(m\approx n^{1/3}\), and Corollary 2.1
needs \(m\ge n^{4/5}/\sqrt2\).

The same computation with columns and rows exchanged covers
\(T'\times[n]\). For \(T'\times T\) Theorem 3 already applies.

## 6. Girth-eight axis graphs with unstructured labels

The natural repair of Section 2 is to keep only a girth-eight axis graph
\(H\) inside the host (for example a generalized quadrangle or the Wenger
graph \(W_2(q)\)), so that all axis-parallel obstructions vanish, and then
to delete tilted obstructions. If the labels of \(H\) are unrelated to the
integer geometry, this fails at the same exponent.

**Theorem 6 [proved].** Let \(T\subseteq[n]\) with \(m=|T|\ge Cn^{1/2}\).
Let \(H\) be a bipartite graph between a set of \(n\) column vertices and a
set of \(m\) row vertices with \(N\) edges and maximum degree at most
\(N/60\). Label the column vertices by \([n]\) and the row vertices by \(T\)
with independent uniformly random bijections, and let \(G\) be the resulting
subset of \([n]\times T\). Then

\[
 \mathbb E\,N_X(G)\ \ge\ c\,\frac{N^6}{n^6}.
\]

*Proof.* Fix six cells of \([n]\times T\) with distinct rows and distinct
columns. The probability that all six lie in \(G\) is the number of ordered
6-tuples of edges of \(H\) that form a matching, divided by
\((n)_6(m)_6\). The number of ordered 6-tuples of edges in which some two
edges meet is at most \(15\cdot2\cdot(N/60)\cdot N^5=N^6/2\). So the
probability is at least \(N^6/(2n^6m^6)\). Sum over the \(cm^6/10\)
six-point sets of Theorem 5. \(\square\)

Hence \(\mathbb E N_X(G)\gg N\) as soon as \(N\gg n^{6/5}\), for every row
set and every axis graph. With \(T=[n]\) and \(H\) a generalized quadrangle
of order \((q,q)\), \(N\asymp n^{4/3}\): the expected tilted six-point count
is at least \(cn^2\), against \(n^{4/3}\) points. For any labeling with at
least the expected count, (2) gives an alteration bound \(O(n^{6/5})\). The
theorem bounds an expectation over labelings. It does not exclude a special
labeling with far fewer obstructions.

A borderline case is worth recording. With \(m\asymp n^{4/5}\) and \(H\) the
incidence graph of a generalized quadrangle of order \((q,q^2)\), one has
\(N\asymp n^{6/5}\) and \(N^6/n^6\asymp N\). So this host is within a
constant-factor deletion of a valid set of size \(cn^{6/5}\), if the upper
bound matching Theorem 6 holds **[heuristic]**. That would remove the factor
\((\log n)^{-1/5}\) from the current lower bound, but not change the
exponent. I have not checked the (F) count or the logarithms in the tilted
count for this host.

## 7. What a host must do, and why this is hard

**Proposition 7 (exact requirement) [proved, cited].** The alteration method
in a host \(G\) gives \(n^{6/5+\gamma}\) with \(\gamma>0\) if and only if,
up to constants,

\[
 n^{6/5+\gamma}\le N\le Cn^{4/3},\qquad
 N_X(G)\le\frac{N^6}{n^{6+5\gamma}},\qquad
 N_H(G)+N_F(G)\le\frac{N^4}{n^{18/5+3\gamma}} .
 \tag{7}
\]

*Proof.* This is (2) together with Theorem 4. \(\square\)

So the host needs a polynomial saving \(n^{5\gamma}\) over the random
six-point count \(N^6/n^6\), at a size above \(n^{6/5}\). To reach
\(n^{4/3-o(1)}\) one needs \(N_X(G)\le n^{4/3+o(1)}\) for a host of
\(n^{4/3-o(1)}\) points, against the random value \(n^2\). That is, the host
is already valid up to a deletion of comparable size. The structured-host
method then reduces to the original problem.

**Why partial structure gives no polynomial saving [heuristic].** Sort right
angles by the size \(D\) of the primitive direction of an arm. In the grid
there are about \(n^4\) rectangles for each dyadic range of \(D\) between
\(1\) and \(n\), which is the source of the factor \(\log n\) in the rectangle
count. In a set that is random with respect to the tilted geometry, each
dyadic range contributes about \(N^3/n^2\) right angles, and each pair of
ranges contributes about \(N^6/n^6\) pairs with a common completion. So:

* Removing all axis-parallel obstructions (\(D=1\)) with a girth-eight axis
  graph changes the count by a factor \(1-O(1/\log n)\). Theorem 6 is the
  rigorous form.
* Removing all right angles with \(D\le n^\theta\) changes the count by the
  factor \((1-\theta)^2\).
* A polynomial saving needs control of almost all pairs of scales, including
  right angles whose arms are primitive vectors of length near \(n\).

Supersaturation forces right angles only for \(D\le N/n\le n^{1/3}\): for a
direction of size \(D\) the two families of lines have about \(nD\) members
each, and a bipartite graph with \(N\) edges on \(nD+nD\) vertices has forced
paths of length three only when \(N\gg nD\). So for larger \(D\) the right
angles are not forced, but every host examined here has them at the random
rate. A host that beats 6/5 must therefore have (i) polynomially fewer
right angles than random at the scales \(D>N/n\), and (ii) polynomially
fewer coincident completions than random at the scales \(D\le N/n\), where
the right angles are forced.

**What I tried for (i) and (ii), and why each fails.**

1. *Sidon rows.* Kills tilted rectangles and axis-tilted pairs, not
   tilted-tilted pairs. Capped at \(O(n)\) by Theorem 2.
2. *Larger row sets with a \(B_3\)-type condition.* Theorem 5: the count
   \(cm^6\) holds for every row set.
3. *Rows in a residue class, or a product of two progressions.* Rows in a
   class modulo \(q\) give a stretched lattice. It has right angles at the
   random rate, and all completions fall back into the host rows, which
   concentrates them by a factor \(q\). A product of two progressions with
   the same difference is a scaled grid with \(N^2\log N\) right angles,
   more than the random count \(N^3n^{-2}\log n\). A product of progressions
   with no tilted right angle at all (differences \(q,q'\) with \(qq'>n\))
   has \(N<n\).
4. *Hosts periodic modulo \(q\) in both coordinates* (for example
   \(y\equiv x^2\bmod q\)). Columns \(x\) and \(x+q\) have equal
   neighbourhoods, so the axis graph is full of 4-cycles.
5. *Girth-eight graphs with digit labels* (Wenger graph with base-\(q\)
   digits as coordinates). Axis-parallel obstructions vanish. Tilted
   geometry involves integer products \(st=-uv\) and carries, which are
   unrelated to the field structure. Theorem 6 is the model, and it gives
   6/5.
6. *Rows near the boundary, so that completions leave the grid.* Triples
   \(a<b<c\) always complete inside, which is the proof of Theorem 5. Only
   constant factors are available.
7. *Well-separated small blocks.* The number of blocks that avoid right
   angles across blocks is too small. The total size is below \(n\).

**Is \(n^{4/3-o(1)}\) reachable?** Not by alteration in a product host
(Theorem 3), not by alteration in any host of more than \(Cn^{4/3}\) points
(Theorem 4), and not from a girth-eight axis graph whose labels ignore the
tilted geometry (Theorem 6). Whether \(f(n,n)=n^{4/3-o(1)}\) is open. The
results here neither support nor refute it. The exponent the proposed family
gives is \(3(1+\mu)/5\le6/5\) for a row set of size \(n^\mu\), and \(9/10\)
in the Sidon case.

**The remaining open route.** A set whose axis graph has girth eight and
whose labels are tied to the Gaussian-integer structure of the grid, so that
for each small direction \(d\) the incidence structure (lines parallel to
\(d\), lines parallel to \(id\), points of \(S\)) is also close to a partial
generalized quadrangle, and completions from different directions avoid each
other. I know no candidate. Condition (7) is the test for one: count pairs
of right angles with a common completion and compare with \(N^6/n^6\).

## 8. Finite checks

[squares_sidon_check.py](squares_sidon_check.py) enumerates, for a Sidon
host, all rectangles, all right angles with completion in the grid, all
pairs of right angles with a common completion, and all (F) configurations.
Run it as `py squares_sidon_check.py big`. Results:

| quantity | \(n=12\), \(T=\{1,2,5,11\}\) | \(n=24\), \(T=\{1,2,5,10,16,23\}\) | \(n=34\), \(T=\{1,2,5,10,16,23,33\}\) |
|---|---|---|---|
| rectangles in \(G\) (all axis-parallel) | 396 | 4140 | 11781 |
| \(\binom n2\binom m2\) | 396 | 4140 | 11781 |
| tilted rectangles | 0 | 0 | 0 |
| axis right angles | 1584 | 16560 | 47124 |
| \(nm(n-1)(m-1)\) | 1584 | 16560 | 47124 |
| tilted right angles | 176 | 2332 | 6918 |
| axis-axis pairs | 25344 | 943920 | 4641714 |
| \(nm\binom{(n-1)(m-1)}2\) | 25344 | 943920 | 4641714 |
| distinct axis six-point sets | 5280 | 242880 | 1256640 |
| \(6\binom n3\binom m3\) | 5280 | 242880 | 1256640 |
| axis-tilted pairs | 0 | 0 | 0 |
| tilted-tilted pairs | 188 | 7164 | 32006 |
| \(nm^4\) | 3072 | 31104 | 81634 |
| (F) configurations | 144 | 1324 | 3816 |

The script also asserts that no tilted completion row lies in \(T\), that
every tilted angle has four nonzero arm coordinates, and that every (F)
configuration has \(|d-c|\ne|b-a|\). All assertions pass. The tilted-tilted
and (F) counts are well inside the bounds (4) and (6). The ratios to
\(nm^4\) grow slowly with \(n\), consistent with divisor-function factors.

These checks cover Lemmas 1.1 to 1.4. Theorems 2 to 6 are not checked
numerically. Their constants are not optimized, and they do not depend on
finite enumeration.

## 9. Proved and not proved

Proved here: Lemmas 1.1 to 1.4, Theorem 2, Theorem 3, Proposition 3.1,
Theorem 5, Theorem 6.

Proved modulo a quoted theorem that I have not read in the primary source:
Corollary 2.1 (Neuwirth), Theorem 4 and Proposition 7 (Jiang and Yepremyan).

Heuristic: the scale decomposition in Section 7, the statements about
stretched lattices, digit labels and separated blocks in the list of failed
attempts, and the borderline claim at the end of Section 6.

Not obtained: any lower bound for \(f(n,n)\) with exponent above \(6/5\).
