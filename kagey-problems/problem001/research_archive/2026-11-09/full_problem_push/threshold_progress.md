# Complete polynomial threshold constructions

9 November 2026. The construction below fills every column. It is not a double-only scaffold.

The later [positional local-lemma construction](near_quadratic_threshold.md) improves the all-height bound to \(h^{2+o(1)}\). This note retains the explicit greedy method, its directly checked examples, and the cubic limitation of its strong pair exclusion.

**Theorem.** For every fixed \(\epsilon>0\), there is a constant \(C_\epsilon\) such that, for every even height \(h\ge4\) and every
\[
 m\ge C_\epsilon h^{3+\epsilon},
\]
there is an identifying blackout with exactly
\[
 m+h^2/4
\]
black cells. Every non-double column has its black cell in row 1 or row \(h\). The double columns contain every opposite-parity row pair exactly once.

Equivalently, the equality threshold at even heights is \(h^{3+o(1)}\) or smaller. The proof is constructive by finite enumeration and greedy placement. Its divisor estimates are uniform in the row labels.

**All-height theorem.** For every fixed \(\epsilon>0\), there is a constant \(C_\epsilon\) such that every height \(h\ge3\) and every \(m\ge C_\epsilon h^{3+\epsilon}\) admit an identifying blackout with exactly \(m+\lfloor h^2/4\rfloor\) black cells. Sections 9--10 handle odd heights with two boundary-sea alphabets and a small family of isolated insertions. Thus the equality threshold is \(h^{3+o(1)}\) or smaller at every height.

## 1. Geometry and notation

Work first in the infinite horizontal strip \(\mathbb Z\times\{1,\ldots,h\}\). A tilted rectangle means a non-axis-aligned rectangle with lattice corners. Put
\[
 W=1+\left\lfloor (h-1)^2/4\right\rfloor.
\]
Every tilted rectangle has horizontal span at most \(W\). Two tilted rectangles sharing a corner have union span at most \(2W\).

Let \(\mathcal E\) be the set of opposite-parity row pairs, and let \(q=|\mathcal E|=h^2/4\). Each edge will occupy one double column. All other columns will choose one of the two boundary rows.

For estimates, write
\[
 T(h)=\max_{1\le n\le 16h^4}\tau(n)=h^{o(1)}.
\]
All constants below are absolute. Powers of \(T(h)\) can be absorbed into \(h^\epsilon\).

Two distinct rectangles have the same presentation exactly when every point of their symmetric difference is black. Their common corners need not be prescribed white in this formulation. Three common corners determine a rectangle, so distinct rectangles have at most two common corners.

If two rectangles share a pair that is a side in both, or a diagonal in both, their four nonshared corners form a rectangle. Thus such a collision gives a hidden rectangle. The remaining two-common-corner case is a mixed side/diagonal collision.

## 2. Three finite counting lemmas

### 2.1. Differences that allow two points on a tilted rectangle

Fix rows \(r,s\). The set of nonzero horizontal differences \(D\) for which \((0,r),(D,s)\) are corners of some tilted rectangle contained in the strip has cardinality
\[
 O(hT(h)).                                      \tag{3}
\]
The other corners can lie anywhere horizontally. This qualification is useful when applying a reflection later.

If the two points are adjacent corners, their vertical difference \(d=s-r\) is nonzero. Write the side vector as \(g(u,v)\), with \(\gcd(u,v)=1\) and \(g\mid |d|\). An integral perpendicular side has vertical component a nonzero multiple of \(u\). Hence \(|u|\le h-1\). There are at most \(2h\tau(|d|)\) possible horizontal differences \(D=gu\). If \(d=0\), the side would be horizontal and the rectangle axis-aligned.

If the points are opposite corners, let \((x,y)\) be the other diagonal vector. Then
\[
 (D-x)(D+x)=y^2-d^2,
 \qquad |y|\le h-1.                            \tag{4}
\]
For nonzero right side, its ordered signed factor pairs give \(O(T(h))\) possibilities for \(D\), for each \(y\). If the right side is zero, the alternative diagonal is the original diagonal or its coordinate reflection. These give either a degenerate rectangle or an axis-aligned rectangle. Thus they contribute no tilted rectangle. This proves (3).

### 2.2. Mixed collisions with four fixed rows

Fix the four black rows \(a,b,c,d\). Let the complementary black side be \(A B\), and the complementary black diagonal be \(C D\). Assume the side is not vertical. Up to common horizontal translation, there are
\[
 O(T(h))                                       \tag{5}
\]
mixed geometries with these rows, with both rectangles nondegenerate and contained in the strip.

Write
\[
 U=B-A=(x,y),\quad V=D-C=(z,v),\quad
 H=A+B-C-D,
\]
where \(y=b-a\), \(v=d-c\), and \(H_y=s=a+b-c-d\). The necessary and sufficient equations, before integrality and strip membership are imposed, are
\[
 x^2+y^2=z^2+v^2,\qquad H_xx+sy=0,
 \qquad H\ne0,\quad V\ne\pm U.                 \tag{6}
\]
If \(y\ne0\), then \(s\ne0\), since \(s=0\) would force \(H=0\). Therefore \(x\mid sy\), with \(0<|sy|<2h^2\). Each of the \(O(T(h))\) choices for \(x\) allows at most two choices for \(z\). The value \(H_x=-sy/x\) then fixes all horizontal coordinates up to translation.

If \(y=0\), then \(H_x=0\). The case \(v=0\) would give \(V=\pm U\), so \(v\ne0\). Now
\[
 (x-z)(x+z)=v^2,                               \tag{7}
\]
which again gives \(O(T(h))\) choices. All integrality, distinctness, and strip conditions only reduce the count.

The excluded vertical-side case is handled geometrically in Section 6; no finiteness assertion for that case is needed.

### 2.3. Horizontal hypotenuse differences

The set
\[
 \mathcal H_h={L>0:\ L^2-D^2=d^2
       \text{ for integers }D,\ 0<|d|<h\}
\]
has size \(O(hT(h))\). Indeed, \((L-D)(L+D)=d^2\). It also has maximum element \(O(h^2)\).

## 3. Boundary seas and one-double influence sets

For even \(h\), every bi-infinite word on the alphabet \(\{1,h\}\) is valid, even when axis rivals are tested against the full parity pair set.

A tilted rectangle has at most one corner on either boundary row. If both boundary rows occur, those corners are opposite. Thus there are at most two black corners. A horizontal presentation from a black boundary diagonal would have midpoint row \((h+1)/2\), which is not integral. A vertical presentation would extend beyond the strip. An oblique axis rival would require a black interior crossed cell. Two tilted rectangles with the same white pair have the same black diagonal: its endpoint rows, midpoint, and length leave at most two reflected choices. Those choices use the same columns with swapped boundary rows, so they cannot both be black in a singleton sea. This proves the assertion.

Fix an edge \(e=\{a,b\}\) at column zero. Define its influence set \(A_e\) by listing the following in-grid positive black-support configurations:

1. A tilted rectangle with three black corners, at least one in \(\{(0,a),(0,b)\}\), and every remaining black corner in a boundary row at a nonzero column.
2. A mixed collision with nonvertical complementary black side, at least one of its four support points in that central pair, and all remaining support points in boundary rows at nonzero columns.

For each configuration, include in \(A_e\) the nonzero columns of its boundary support points. A support can use both central points. Require all its fixed column-zero points to belong to \(e\).

Then
\[
 |A_e|=O(T(h)),\qquad A_e\subseteq[-2W,2W].       \tag{8}
\]
For the first type, two central corners and a boundary corner are impossible: the central pair is a vertical diagonal, whose other corners lie strictly between its endpoint rows. Otherwise the two sea corners must be \((u,1),(v,h)\), with central corner \((0,c)\), and
\[
 uv=(c-1)(h-c)>0.                              \tag{9}
\]
The divisor bound proves the count. For the second type, there are only constantly many assignments of the four row roles from \(\{a,b,1,h\}\). Lemma 2.2 and the anchoring of one central point give (8).

Prescribe at every column of \(A_e\) the value from the isolated-double pattern
\[
 \cdots111\ \{a,b\}\ hhh\cdots :
 \quad 1\text{ at negative offsets},\quad
 h\text{ at positive offsets}.                \tag{10}
\]
This simultaneously breaks every listed support. The isolated-double pattern is valid for every row pair: a complete geometric proof appears in [the independent insertion audit](../../2026-11-08/dominance_bridge/construction_audit.md), Section 4. The particular facts needed here are that it has no three-black tilted rectangle and no mixed collision. They can also be read directly from the geometry: black-diagonal white pairs straddle zero; black-side white pairs lie wholly on one side; midpoint and length make each type unique.

The choice (10) is applied only on the finite set \(A_e\), not on a whole interval surrounding the double.

## 4. Pairwise forbidden differences

For each two distinct labeled edges \(e,f\), forbid a signed difference \(x_f-x_e\) if any of the following holds.

* The translates of \(A_e\cup\{0\}\) and \(A_f\cup\{0\}\) intersect.
* Some point of the double \(e\) and some point of the double \(f\) are corners of a tilted rectangle contained in the infinite strip.
* The absolute difference belongs to \(\mathcal H_h\).
* There is an in-grid mixed collision with nonvertical black side, containing a required black point from each of the two double columns, with every other required black point either in those same doubles or in a boundary row.

In the last item the configuration may use several points from a double, but every point in that column must belong to its edge. Required boundary support at other columns remains unassigned for this test.

The number of forbidden differences for each pair is
\[
 O(T(h)^2+hT(h))=h^{1+o(1)}.                   \tag{11}
\]
The first item follows from (8). The second follows from Lemma 2.1 and four choices of endpoint rows. The third is Lemma 2.3. For the fourth, choose the four row roles from the at most six rows in \(e\cup f\cup\{1,h\}\). Lemma 2.2 gives \(O(T(h))\) patterns up to translation. Choosing which support point anchors each double gives only a constant factor.

## 5. Greedy placement and full completion

Let \(K(h)\) be a common upper bound in (11), including both signs. Place the \(q\) labeled doubles greedily in an interval of
\[
 N=1+(q-1)K(h)
\]
integer positions. When placing the next edge, each previous edge excludes at most \(K(h)\) positions, so an available position remains.

The translated influence sets, including their double centers, are disjoint. Apply (10) on each translated \(A_e\). In every other non-double column, choose row 1 or row \(h\) arbitrarily. This defines a full blackout on the infinite strip.

In particular, prescriptions never land on another double column. The arbitrary choices can vary independently, and no empty column is introduced.

## 6. Proof that the completed blackout identifies rectangles

Every tilted rectangle contains black points from at most one double column, by the second forbidden-difference rule. If it had three black corners, it would therefore be one of the one-double configurations listed in Section 3. Its influence prescription breaks that support. Thus every tilted rectangle has at most two black corners. There are no hidden tilted rectangles or tilted singleton presentations. Collisions with six nonshared black corners are impossible for the same reason.

Axis-aligned rectangles are identified because every column has at most two black points, every double pair occurs once, and the double graph is bipartite. More explicitly, duplicate vertical presentations or hidden axis rectangles require a repeated double pair. Duplicate horizontal presentations require two columns sharing two black rows. Competing singleton axis presentations would give a triangle of double pairs. All are excluded.

It remains to consider a tilted rectangle with two black corners and another rectangle with the same white pair.

**Two tilted rectangles.** Side/side and diagonal/diagonal collisions give a hidden rectangle. If it is tilted, this contradicts the preceding three-black exclusion. If it is axis-aligned, it contradicts uniqueness of the double pairs. In a mixed collision, each tilted rectangle contributes black points from at most one double column. Thus there are at most two double labels in its four-point support. With no double label it contradicts the boundary-sea lemma. With one label it is broken by that influence prescription. With two labels it is excluded by the last forbidden-difference rule.

**A vertical axis presentation.** The tilted black diagonal contains at most one double column. If it contains a boundary point, a vertical alternative diagonal extends beyond that boundary. Otherwise both black points are the same double's vertical pair, which cannot have a distinct vertical alternative diagonal. Thus this case is impossible, irrespective of how far away an axis double lies.

**A horizontal axis presentation.** The axis rectangle's complementary black side has two points in distinct columns. If both are double columns, their separation \(L\) and the tilted black-diagonal vector \((D,d)\) satisfy \(L^2-D^2=d^2\), with \(d\ne0\). This is excluded by \(\mathcal H_h\). Otherwise the axis black side uses at most one double column, while the tilted rectangle uses at most one. The resulting mixed support has at most two double labels and is handled exactly as above.

**An oblique axis presentation.** If that pair is a diagonal of the tilted rectangle, the diagonal/diagonal reduction gives a hidden rectangle, already excluded. Otherwise it is a side of the tilted rectangle. Write its shared corners as
\[
 P=(x,r),\qquad Q=(z,s).
\]
The axis rectangle's complementary black diagonal is the crossed pair
\[
 C=(x,s),\qquad D=(z,r).
\]
If both crossed points are double points from distinct columns, reflect the tilted rectangle in the vertical line \(X=(x+z)/2\). Its reflected side is \(DC\), and all its row coordinates remain unchanged. This produces a tilted rectangle in the infinite strip containing both double columns, contradicting the second forbidden-difference rule. The reflected corners need not lie inside the eventual finite horizontal board; this is why Lemma 2.1 was formulated in the strip. Otherwise the axis black diagonal uses at most one double column. The mixed support again uses at most two double labels and is excluded.

This exhausts all presentations of size at most two. A presentation containing at least three corners determines its rectangle uniquely. The full infinite-strip blackout is therefore identifying.

## 7. Finite boards and the threshold bound

Take any finite interval containing all double centers and their influence sets. Adding at most \(4W\) columns to the greedy interval is enough. Its width is
\[
 N+4W=O\bigl(h^2(T(h)^2+hT(h))+h^2\bigr)
      =h^{3+o(1)}.                            \tag{12}
\]
Restricting an identifying blackout to a smaller grid preserves identification for all rectangles contained in that grid. The finite interval contains each parity edge once and has one black cell in every other column. Its black count is therefore exactly \(m+q\).

Every larger width is obtained by taking a larger finite interval of the same infinite-strip construction. The arbitrary unprescribed boundary choices cause no new restrictions. This proves the theorem for every sufficiently large width, rather than for a subsequence of widths.

## 8. What prevents an immediate odd-height extension

For odd \(h\ge5\), the binary sea \(\{1,h-1\}\) is also valid for the parity pair set. This follows from the same presentation classification, with two extra observations. A three-black rectangle using those two rows would have a fourth row outside the strip. A mixed collision involving a black diagonal repeated in row \(h-1\) would require a common corner at row \((3h-4)/2>h\). A repeated-row vertical black diagonal has an even-gap vertical presentation and hence no parity axis rival.

However, the one-double gadget (10) does not survive this replacement. At height seven, a central double containing row 3 and a right sea point \((4,6)\) give the black diagonal
\[
 (0,3),(4,6)
\]
whose white diagonal is
\[
 (2,2),(2,7).
\]
The opposite-parity pair \(\{2,7\}\) has an axis rival in every equality board. More generally, an odd central row \(r\ge3\) with \(h-r=s^2\) gives this obstruction at horizontal distance \(2s\), with white rows \(r-1,h\).

There is also a three-black obstruction whenever the central double contains row \(h\): the points
\[
 (0,h),\quad (1,h-1),\quad (3-h,1)
\]
complete to \((2-h,2)\). In the proposed monotone sea its column is black in row 1, so the remaining singleton has a parity axis rival.

These obstructions prevent using the same one-double gadget for every odd-height edge. They do not prevent using it for most edges, as the next section shows.

## 9. An all-height bound of order \(h^{7/2}\)

Let \(h\ge5\) be odd and put \(H=h-1\). Define the exceptional odd row set
\[
 B_h=\{h\}\cup\{h-4j^2:\ j\ge1,\ h-4j^2\ge3\}.                 \tag{13}
\]
It has \(O(\sqrt h)\) members. Call a parity edge good if neither endpoint belongs to \(B_h\), and bad otherwise. There are \(O(h^{3/2})\) bad edges.

### 9.1. The binary sea and the monotone one-double gadget

Every word on \(\{1,H\}\) is valid in the height-\(h\) strip against the full parity pair set.

For a three-black tilted rectangle, two black corners must repeat a sea row and hence be a horizontal diagonal. The fourth row would be \(2-H<1\) or \(2H-1>h\). Thus there is no such rectangle. Horizontal presentations from a mixed-row black diagonal have a half-integral midpoint row. A vertical presentation from a mixed-row black diagonal extends below row 1; one from a repeated-row black diagonal has even row difference and has no parity axis rival.

The remaining collision possibilities are hidden-rectangle reductions or mixed supports. A tilted black side must use both sea rows, so its vertical component is odd. Integrality of the shared pair forces the black diagonal to have odd row sum, and hence also to use both sea rows. The two black-pair row sums are then equal. Equation (6) forces the connector to vanish. This excludes tilted collisions and the mixed oblique-axis case. Axis rectangles alone are identified because all columns are singletons.

Now fix a good edge \(e\), and consider
\[
 1^\infty\ e\ H^\infty.                                         \tag{14}
\]
All its black points form a chain in the coordinatewise order: points to the left have row 1, the two central rows lie in \([1,H]\), and points to the right have row \(H\).

A coordinatewise chain has no three corners of a tilted rectangle. At a middle point, the two displacement vectors have opposite coordinate signs; their dot product can vanish only when the two legs are horizontal and vertical. At an endpoint, both displacement vectors have the same coordinate signs, with the same conclusion. Those zero-dot-product cases give axis-aligned rectangles.

A coordinatewise chain also has no mixed collision with nonvertical complementary black side. Orient that side \(AB\) so that \(U=B-A\) has positive horizontal component and nonnegative vertical component. Orient the black diagonal \(CD\) in the chain order. Let \(p(X)=(X-A)\cdot U\). The midpoint and norm equations give
\[
 p(C)+p(D)=|U|^2,\qquad
 |p(D)-p(C)|=|V\cdot U|<|U|^2.
\]
The last inequality is strict because \(|V|=|U|\) and \(V\ne\pm U\). Hence both \(p(C),p(D)\) lie strictly between \(p(A)=0\) and \(p(B)=|U|^2\). If both components of \(U\) are positive, the chain order forces \(A\le C\le D\le B\). Consequently \(0\le V\le U\) componentwise, and equal norms force \(V=U\), a contradiction. If \(U\) is horizontal, the strict projections put both diagonal endpoints strictly between the side's endpoint columns. The chain then forces their rows to equal \(A_y=B_y\), so the same contradiction follows. This lemma also excludes horizontal axis rivals, whose complementary black side is horizontal.

It remains to classify vertical axis rivals. A black diagonal involving row 1 has no in-grid vertical alternative. The central vertical pair cannot have a distinct vertical alternative. Two equal-row sea points have a vertical alternative with even row difference, which has no parity axis rival.

The remaining black diagonal joins \((0,r)\) to a right sea point \((x,H)\). Put \(d=H-r\). Its vertical alternative has length \(L>d\), and its upper endpoint fits below row \(h=H+1\) only if \(L\le d+2\). Integrality requires \(L\equiv d\pmod2\). Therefore
\[
 L=d+2,\qquad x^2=L^2-d^2=4(h-r),                               \tag{15}
\]
and the white rows are exactly \(r-1,h\). This is a parity axis rival precisely when \(r\) is odd, \(r\ge3\), and \(h-r\) is a square. Since \(h-r\) is even, its square root must be even. These are exactly the exceptional rows in (13). A good edge has none of them.

Side/side and diagonal/diagonal collisions would create a hidden rectangle, already excluded by the chain argument. This proves that (14) is valid against the full parity pair set and has no three-black tilted rectangle.

### 9.2. Complete the good-edge bulk

Apply Sections 2--5 to the good edges, using the two sea rows \(1,H\), while retaining the actual strip height \(h\) in every geometric test. Define one-double influence sets from three-black tilted rectangles and nonvertical mixed supports, as before. Their prescriptions now copy (14).

The only counting change is that the two sea points in a three-black configuration can repeat row \(H\). For a fixed central row and two fixed sea rows, choose the right-angle vertex among the three roles. Orthogonality equates a product of two horizontal offsets to a product of two fixed row differences. If a row difference is zero, either the rectangle is axis-aligned or two required points coincide. Every nondegenerate role choice therefore still has \(O(T(h))\) geometries. Two central points and a sea point remain impossible, since the sea rows are extremal among the central and sea black rows. The influence size stays \(O(T(h))\).

All pairwise forbidden-difference counts remain unchanged. The completed good-edge bulk has no three-black tilted rectangle. Its nonvertical two-point collisions are excluded by the same at-most-two-label argument, the horizontal hypotenuse rule, and vertical reflection.

The vertical-axis case uses classification (15), rather than the even-height boundary argument. A tilted black diagonal contains black points from at most one double column. If it uses row 1, a vertical alternative exits the strip. If it is the central vertical pair, no distinct vertical alternative exists. Two sea points in row \(H\) give an even-gap vertical presentation. Finally, a central point and a row-\(H\) sea point can give an opposite-parity vertical presentation only through an exceptional odd row. Good edges exclude those rows. Hence the good-edge completion is valid against the full parity pair set.

This gives a complete good-edge block of width \(h^{3+o(1)}\). Choose every sufficiently distant unprescribed sea column to be row 1, and retain row-1 collars of length \(L=2W\) at both ends.

### 9.3. Insert the exceptional edges and glue the blocks

For each bad edge \(e\), use the closed insertion word
\[
 1^L\ e\ h^L\ 1^L.                                             \tag{16}
\]
The isolated-double proof validates \(1^\infty e h^\infty\) against the full parity pair set. The single boundary switch \(h^\infty1^\infty\) is valid as well. The central double and the second switch are separated by a constant row-\(h\) interval of length \(L\), so (16), extended by row 1 on both sides, is valid. Its length is \(3L+1=O(h^2)\).

Concatenate the good-edge block and the closed insertion blocks, matching their row-1 collars. Every tilted rectangle has span at most \(W\). Every pair of tilted rectangles with a common corner has union span at most \(2W=L\). A local tilted failure crossing a join is therefore already present in one of the two blocks extended by its constant row-1 tail. Those extensions are valid.

Possible far axis rivals are also covered: singleton and vertical rivals are tested against the full final parity pair set in every block. Horizontal and oblique rivals use the columns of their white presentation and are local. Axis-axis uniqueness follows globally from the distinct parity edges. Thus the concatenated full board is identifying.

Its width is
\[
 h^{3+o(1)}+O(h^{3/2})O(h^2)=O(h^{7/2}).                         \tag{17}
\]
Every parity edge appears once, and every other column has one black cell. The black count is exactly \(m+\lfloor h^2/4\rfloor\). Constant row-1 tails extend the board to every larger width. The fixed height three is handled by the original isolated insertion construction and is absorbed into the absolute constant.

This first odd-height construction gives an actual full-board bound. A second sea alphabet improves it to match the even-height exponent, as follows.

## 10. A second sea gives the all-height near-cubic bound

For odd \(h\ge9\), put
\[
 g_1=h-1,\qquad g_2=h-3.
\]
Both are even and satisfy \(2g_i-1>h\). More generally, whenever an even \(g\le h\) satisfies \(2g-1>h\), the full binary sea \(\{1,g\}\) is valid against the parity pair set. The proof in Section 9.1 uses only this inequality, the lower boundary row 1, and the parity of \(g\).

For an edge with both endpoints in \([1,g]\), the monotone gadget
\[
 1^\infty\ e\ g^\infty
\]
has the same chain property. Only its virtual vertical-axis rivals remain to be tested. A central odd row \(r\) and a row-\(g\) sea point give such a rival exactly when, for some integer \(j\),
\[
 1\le j\le h-g,\quad r-j\ge1,\qquad
 j(g-r+j)\text{ is a square}.                                  \tag{18}
\]
Indeed, the vertical length must be \(g-r+2j\); the horizontal separation squared is \(4j(g-r+j)\), and the white rows are \(r-j,g+j\). An even central row instead gives an even-gap presentation and hence no parity rival.

The first bulk uses \(g_1\) and all edges with odd endpoint outside \(B_h\). Send each remaining edge with odd endpoint
\[
 r=h-4u^2\ge3,
\]
and even endpoint at most \(h-3\), to a second bulk using \(g_2\). These endpoint rows lie in \([1,g_2]\). For this odd row, the three possible values in (18) are
\[
 \begin{array}{c|c}
 j&j(g_2-r+j)\\ \hline
 1&4u^2-2\\
 2&8u^2-2\\
 3&12u^2.
 \end{array}                                                    \tag{19}
\]
None is a square. The first lies strictly between \((2u-1)^2\) and \((2u)^2\). The second is 6 modulo 8. The third has odd 3-adic valuation.

Thus every second-bulk edge has a valid monotone gadget. The complete influence-and-placement proof applies to that group too. The repeated-row three-black count, nonvertical mixed count, and pairwise exclusions are unchanged. The vertical-axis check is exactly (18). The sea inequality \(2g_2-1>h\) excludes sea-only three-black rectangles.

There are at most \(O(h^{3/2})\) second-bulk edges, so its width is
\[
 O\bigl(h^{3/2}(hT(h)+T(h)^2)+h^2\bigr)=h^{5/2+o(1)}.
\]
Only two types of edges remain: edges incident to row \(h\), and edges joining an exceptional row \(h-4u^2\) to the top even row \(h-1\). Their total number is \(O(h)\). Use the closed insertions (16) for these edges, at total cost \(O(h^3)\).

Give both bulk blocks row-1 collars and concatenate them with those closed insertion blocks. Section 9.3 proves that this gluing preserves identification against the full final parity graph. The total width is
\[
 h^{3+o(1)}+h^{5/2+o(1)}+O(h^3)=h^{3+o(1)}.                    \tag{20}
\]
All parity edges occur once, all other columns contain one black cell, and constant tails give every larger width. The finitely many odd heights below nine are absorbed into the constants using the earlier construction. This proves the stated all-height theorem.

The gap to a quadratic threshold remains. The current greedy estimate pays \(h^{1+o(1)}\) forbidden differences per pair of double labels. Its main linear factor comes from ruling out every tilted rectangle through two prescribed double points and from the universal horizontal hypotenuse gap set. Neither exclusion is asserted necessary for all valid completions.

## 11. Direct finite checks

The companion `threshold_progress_check.py` constructs the influence sets and forbidden shifts, places the doubles greedily, and fills every remaining column. It then freshly enumerates every tilted rectangle in each finite board, hashes its actual white presentation, and checks the full parity-axis rival rules. This final verification does not reuse the forbidden-shift test.

For even heights 4, 6, 8, and 10, the constructed widths are respectively 27, 102, 320, and 719. Three independent choices of all unprescribed boundary letters passed at each height. The checker also constructs the complete odd-height boards at heights 5, 7, 9, and 11, using two choices of unprescribed sea letters. These checks include the bulk joins and all residual closed insertion blocks. Exact widths, rectangle counts, and runtime are saved in `threshold_progress_check.json`. The widths are verification examples, not claimed minima.

## 12. A cubic barrier for the strong pair exclusion

The condition that no tilted rectangle in the strip contains black points from two different double columns cannot support a quadratic-width proof. This is a limitation of that sufficient condition, not a lower bound for identifying boards.

Fix \(k<h\), and consider the \(q_k=\lfloor k^2/4\rfloor\) required parity edges whose endpoints lie in rows \(1,\ldots,k\). Take any two of their distinct double columns, at positive separation \(D\). Choose a point from each column with distinct rows \(r\ne s\), which is always possible because each column contains two rows. Put
\[
 U=(D,s-r),\quad d=\gcd(D,|s-r|),\quad
 V=(-(s-r)/d,D/d).
\]
These are nonzero perpendicular lattice vectors, and neither is axis-parallel. If \(D\le h-k\), the rectangle obtained by translating the side \(U\) by \(V\) is in the height-\(h\) strip: its new rows are
\[
 r+D/d,\quad s+D/d\le k+D\le h,
\]
and no row drops below 1. Thus the strong pair exclusion forces every two of these \(q_k\) double centers to be at distance at least \(h-k+1\). Consequently their total horizontal span is at least
\[
 (q_k-1)(h-k+1).
\]
Taking \(k=\lfloor2h/3\rfloor\) gives the necessary width
\[
 m\ge \frac{h^3}{27}+O(h^2)                                  \tag{21}
\]
for any construction that imposes this strong exclusion on the full parity edge family. Other horizontal corners of the witnessing rectangles can lie outside the finite board, because the condition itself was imposed in the infinite strip.

A quadratic advance must therefore permit some tilted rectangles containing points from two doubles. For a fixed pair of double labels, the weaker bad shifts that actually create a three-black rectangle with a boundary sea point are only divisor-many. The same is true for mixed four-point supports using two double labels and boundary sea points. These follow from the fixed-row product and mixed equations used above. Their combined pairwise cost is \(h^{o(1)}\), which would be compatible with greedy width \(h^{2+o(1)}\).

However, removing the strong exclusion exposes three-double right angles, mixed supports with three or four double labels, and vertical Pythagorean rivals. The existing one-prime and two-prime scaffold results address some of these immutable configurations but do not supply a complete boundary-sea extension. No conclusion about a quadratic threshold follows from the divisor-many weaker shifts alone.
