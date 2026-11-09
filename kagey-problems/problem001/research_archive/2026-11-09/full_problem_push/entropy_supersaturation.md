# Supersaturation for singleton-rival supports above half density

9 November 2026. This note supplies the geometric supersaturation input for a container upper bound on sea entropy, uniformly over balanced row bipartitions. It is independent of any dominance assumption.

Let \(V_h=[h]^2\), and fix a partition \(\pi\) of the rows into parts of sizes \(\lfloor h/2\rfloor,\lceil h/2\rceil\). Define a four-uniform hypergraph \(\mathcal H_{h,\pi}\) on \(V_h\) as follows. Take three corners \(A,B,C\) of a tilted lattice rectangle whose fourth corner \(D\) also lies in \(V_h\). Require that the rectangle's four columns are distinct. Choose a cell \(E\in V_h\) in the column of \(D\), with its row in the other part of \(\pi\). Then
\[
\{A,B,C,E\}
\]
is an edge. Repeated descriptions of the same edge are identified.

Every sea word for the complete bipartite pair set of \(\pi\) is an independent transversal of \(\mathcal H_{h,\pi}\): if these four cells were its selected cells, the tilted rectangle would have the singleton presentation \(\{D\}\), with a virtual axis rival supplied by the selected cell \(E\) from the other row part in its column.

**Theorem.** For each fixed \(\varepsilon>0\), there are \(c_\varepsilon>0\) and \(h_0(\varepsilon)\) such that, whenever \(h\ge h_0(\varepsilon)\) and
\[
|U|\ge(1/2+\varepsilon)h^2,
\]
the induced hypergraph satisfies
\[
e(\mathcal H_{h,\pi}[U])\ge c_\varepsilon h^5\log h.       \tag{1}
\]

The constants are uniform over all balanced partitions \(\pi\). The proof has two steps. A dense cell set contains many tilted rectangles in distinct columns. More than half density then supplies many vertical shifts for which both endpoints belong to \(U\) and their rows are in different parts of \(\pi\).

## 1. Dense sets contain many tilted rectangles

**Lemma.** For each fixed \(\delta>0\), every \(B\subseteq[h]^2\) with \(|B|\ge\delta h^2\) contains at least
\[
c_\delta h^4\log h                              \tag{2}
\]
tilted rectangles with four distinct columns, once \(h\) is sufficiently large in terms of \(\delta\).

Fix a primitive vector \(w=(a,b)\) with \(a,b>0\), and put
\[
w^\perp=(-b,a),\qquad r=\sqrt{a^2+b^2}.
\]
We use directions with \(a+b\le h^{1/4}\). The lattice
\[
\Lambda_w=\mathbb Zw+\mathbb Zw^\perp
\]
has index \(r^2\) in \(\mathbb Z^2\). In every coset, tile its integer coordinate plane by disjoint \(k\times k\) squares, where
\[
k=\left\lfloor\frac{\eta h}{r}\right\rfloor,
\]
and \(\eta>0\) is a sufficiently small fixed multiple of \(\delta\). Each tile consists of \(k^2\) lattice points. Its Euclidean diameter is at most \(\sqrt2\eta h\).

Retain only tiles all of whose points lie in \([h]^2\). Every discarded point of the board belongs to a tile meeting the exterior, and hence lies within distance \(\sqrt2\eta h\) of the boundary. The number of discarded board points is therefore \(O(\eta h^2+h)\). This estimate is uniform in the cosets and in \(w\), because the tiles partition all lattice points. Choose \(\eta\) so that at least \(3\delta h^2/4\) points of \(B\) remain for large \(h\).

The retained tiles contain at most \(h^2\) points altogether. Tiles having fewer than \((\delta/4)k^2\) points of \(B\) account for at most \(\delta h^2/4\) black points. Thus at least \(\delta h^2/2\) black points lie in the remaining dense tiles. There are at least
\[
\frac{\delta h^2}{2k^2}
\]
such tiles, since no tile contains more than \(k^2\) black points.

Regard a tile as a bipartite graph on its two coordinate axes. The elementary dense \(C_4\) bound says that a subset of density at least \(\delta/4\) in a \(k\times k\) array contains at least \(c\delta^4k^4\) axis rectangles once \(k\) is sufficiently large in terms of \(\delta\). This follows by applying convexity first to column degrees and then to the common-neighbor counts of pairs of rows. Here \(r\le h^{1/4}\), so
\[
k\ge\frac{\eta h}{2r}\ge\frac\eta2h^{3/4}
\]
for large \(h\), uniformly over the chosen directions.

Transforming back to the original grid, these are tilted rectangles with sides parallel to \(w,w^\perp\). The number obtained for this direction is at least
\[
c\delta^5h^2k^2
\ge c_\delta\frac{h^4}{a^2+b^2}.                \tag{3}
\]
Tiles are disjoint, so no rectangle has been counted twice within a direction.

### Excluding repeated columns

Write the side vectors of a rectangle of this direction as
\[
u(a,b),\qquad v(-b,a),\qquad u,v\ge1.
\]
Relative to its lowest vertex, the four horizontal coordinates are
\[
0,\quad ua,\quad-vb,\quad ua-vb.
\]
Two coincide exactly when \(ua=vb\). Since \(a,b\) are coprime, this forces
\[
u=bt,\qquad v=at,
\]
and its total vertical span is \(t(a^2+b^2)\). There are at most \(h/(a^2+b^2)\) possible positive integers \(t\), and at most \(h^2\) choices of the lowest vertex. Therefore all repeated-column rectangles of this direction number at most
\[
\frac{h^3}{a^2+b^2}.                            \tag{4}
\]
For sufficiently large \(h\), this is at most half the lower bound in (3).

Finally, different primitive directions with both coordinates positive give different perpendicular side-direction pairs. Summing (3), after subtracting (4), yields
\[
c_\delta h^4
\sum_{\substack{a,b>0,\ (a,b)=1\\a+b\le h^{1/4}}}
\frac1{a^2+b^2}
\ge
c_\delta h^4
\sum_{s\le h^{1/4}}\frac{\varphi(s)}{s^2}
\gg_\delta h^4\log h.
\]
The harmless \(s=1\) term is omitted. The logarithmic lower bound is elementary: in each fixed-ratio annulus there are a positive proportion of coprime integer pairs, so its weighted contribution is bounded below by a positive constant. An explicit proof of this estimate appears in [the local completion-budget note](../../2026-11-08/square_local_budget.md), Section 2. This proves (2). \(\square\)

## 2. Cross-partition shifts create many dense intersections

For a nonzero integer \(s\) with \(|s|\le h-1\), let
\[
B_s=\{(x,y)\in U:(x,y+s)\in U,\ \pi(y)\ne\pi(y+s)\}.
\]
Write \(e_x,o_x\) for the numbers of selected rows in the two parts in column \(x\). Summing over signed shifts counts each ordered cross-partition pair in a column exactly once:
\[
\sum_{s\ne0}|B_s|=2\sum_{x=1}^h e_xo_x.          \tag{5}
\]

Let \(E=\lceil h/2\rceil\) and \(O=\lfloor h/2\rfloor\), assigning the labels to the larger and smaller row parts as needed. Since the two column counts are bounded by \(E,O\),
\[
e_xo_x\ge O(e_x+o_x)-EO.
\]
Hence
\[
\sum_x e_xo_x\ge O(|U|-Eh)
\ge c\varepsilon h^3                           \tag{6}
\]
for all sufficiently large \(h\). The rounding error is only \(O(h^2)\).

There are fewer than \(2h\) signed shifts, and every \(|B_s|\le h^2\). Equations (5) and (6) therefore imply that at least \(c_\varepsilon h\) shifts satisfy
\[
|B_s|\ge c_\varepsilon h^2.                      \tag{7}
\]
For example, after increasing the height threshold, both constants can be taken as a fixed sufficiently small multiple of \(\varepsilon\).

## 3. Counting distinct hyperedges

For each shift satisfying (7), the lemma supplies at least \(c_\varepsilon h^4\log h\) tilted rectangles in \(B_s\), each using four distinct columns. Choose one of its corners \(D\) by any fixed rule, and let \(A,B,C\) be the other three. Because every rectangle corner lies in \(B_s\),
\[
A,B,C\in U,
\qquad E=D+(0,s)\in U.
\]
The four cells \(A,B,C,E\) have distinct columns, and the rows of \(E,D\) belong to different parts of \(\pi\). They form an edge of \(\mathcal H_{h,\pi}[U]\).

Each hyperedge has at most four preimages under this construction. Choose which of its four cells is \(E\). The other three, if they form a right triangle at all, determine their right-angle vertex and their unique rectangle completion \(D\). The vertical displacement from \(D\) to \(E\) then determines \(s\). Thus neither different directions nor different shifts create an unbounded multiplicity.

There are \(c_\varepsilon h\) good shifts, each giving \(c_\varepsilon h^4\log h\) rectangles. Dividing by the constant multiplicity proves (1). \(\square\)

## 4. Scope of the input

The theorem is a supersaturation statement for arbitrary cell sets, not just transversals. The four-distinct-column restriction is essential when applying it to sea words, and was retained throughout the proof. The class-crossing condition and actual rectangle containment handle the row partition and finite boundaries directly. For the ordinary parity partition, this condition reduces to odd shifts, recovering the initial special case.

A container argument still needs the hypergraph's degree and codegree estimates and a count specialized to transversals. Those steps are separate from this geometric proof. No statement about the square blackout exponent follows from (1) alone.
