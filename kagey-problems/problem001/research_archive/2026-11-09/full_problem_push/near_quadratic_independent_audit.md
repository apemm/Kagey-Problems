# Independent audit of the near-quadratic full-board construction

9 November 2026. The positional local-lemma argument in [near_quadratic_threshold.md](near_quadratic_threshold.md) supplies an actual singleton completion of all parity doubles, at width \(h^{2+o(1)}\). This audit checks the support classification, the probability calculation, and the odd-height cover. It does not assert a constant multiple of \(h^2\).

## 1. The finite support families

Fix a valid binary background \(\{a,g\}\), and a group of labeled parity doubles whose isolated monotone gadgets are valid against the full final parity pair set. Let \(q'\le q_h=\lfloor h^2/4\rfloor\) be the number of labels in this group. Assign independent centers \(X_e\), uniform in \(\{1,\ldots,N\}\).

Write \(T(h)=h^{o(1)}\) for a common divisor bound at all the polynomial-size integers appearing below. Constants in the number of row-role assignments are absolute: a support has at most four cells, even when there are many edge labels.

The private influence set of an edge records every one-label three-black tilted rectangle and every one-label nonvertical mixed side/diagonal support, with the other required points in the two background rows. Fixed row roles give \(O(T)\) shapes up to horizontal translation. The influence set therefore has \(O(T)\) columns, and prescribing its letters from the valid isolated gadget breaks all these supports at once.

The positional bad events are:

* overlap of two translated influence sets, each enlarged to include its center;
* a tilted three-black right angle involving at least two distinct double labels;
* a nonvertical mixed side/diagonal four-cell support involving at least two distinct labels;
* a vertical Pythagorean rival whose complementary black diagonal uses two distinct double labels.

In the support events, attribute every required point lying in a double column to that double label, including a point whose row happens to equal a background row. This convention is essential: it makes the split into zero-label, one-label, and several-label supports exhaustive.

## 2. Fixed-label counts and probabilities

For a fixed set of \(k\) distinct labels, \(2\le k\le4\), choose the assignments of labels and background rows to the at most four support roles. There are only a constant number of choices.

For a three-black tilted rectangle, select its right-angle vertex. Orthogonality makes the product of two horizontal offsets equal the negative product of two fixed row differences. Both row differences are nonzero: a zero difference would make one leg horizontal and the other vertical, giving an axis rectangle rather than a tilted one. Thus there are \(O(T)\) horizontal geometries.

For a mixed four-cell support, the nonvertical complementary side \(U=(x,b-a)\) and midpoint displacement satisfy
\[
 xH_x+(b-a)(a+b-c-d)=0.
\]
If \(b-a\ne0\), the row-sum factor cannot be zero without forcing the two black pairs to have the same midpoint and making the side rectangle degenerate. Hence \(x\) divides a fixed nonzero integer. If \(b-a=0\), equality of the side and diagonal norms gives
\[
 (x-z)(x+z)=(d-c)^2,
\]
with a nonzero right side in the nondegenerate case. Both cases have \(O(T)\) geometries. The argument permits repeated row values and repeated columns; impossible assignments are simply discarded.

Each geometry fixes all \(k\) center differences relative to one chosen center. Its occurrence probability is at most \(N^{-(k-1)}\). Taking a union over the \(O(T)\) shapes gives
\[
 \Pr(B_{\mathcal E})\le C\,T(h)N^{-(k-1)}.
\tag{1}
\]
The same bound follows by counting at most \(N\) translations among \(N^k\) assignments. It requires no independence between the different shapes grouped into one event.

For a vertical rival, fixed distinct endpoint rows have difference \(d\ne0\), and
\[
 (L-D)(L+D)=d^2.
\]
This gives \(O(T)\) allowable center gaps. If \(d=0\), integral midpoint coordinates force \(D\) and \(L=|D|\) even, so the vertical white pair has equal row parity and no parity-axis rival. Thus vertical rivals contribute only the two-label version of (1).

Two influence sets, including centers, have \(O(T^2)\) possible overlapping displacements. Their event probability is at most \(CT^2/N\). Enlarging by the centers simultaneously excludes equal centers and influence prescriptions landing on another double.

A one-label vertical rival cannot be repaired or created by the choice of left versus right background letter. Its geometry depends only on the absolute horizontal distance. The isolated monotone gadget contains every central-row/background-row pair at all positive distances on one side, and reflection supplies the other side. Thus validity of that gadget excludes every one-label vertical rival, for every background assignment.

## 3. Local-lemma dependency calculation

Two events are dependent only when they use a common center variable. For a fixed label, the number of \(k\)-label events containing it is \(O((q')^{k-1})\). With weights twice the probability upper bounds, the total incident weight is therefore
\[
 O\!\left(
 \frac{q'T(h)^2}{N}
 +\sum_{k=2}^4 T(h)
       \left(\frac{q'}N\right)^{k-1}
 \right).
\tag{2}
\]
Every event has at most four center variables. Choosing
\[
 N=C_0q'T(h)^2
\]
with a sufficiently large absolute \(C_0\) makes the sum of neighboring weights at most \(1/2\), and every event weight at most \(1/2\). The product inequality
\[
 \prod_{F\sim E}(1-x_F)\ge1-\sum_{F\sim E}x_F\ge\tfrac12
\]
then verifies \(\Pr(E)\le x_E\prod_{F\sim E}(1-x_F)\).

Consequently a simultaneous placement avoiding every listed event exists. This argument replaces the earlier condition forbidding every tilted rectangle through two marked points. That earlier sufficient condition has a cubic width barrier; it is not used here.

## 4. Completeness after the sea is filled

Prescribe the disjoint private influence sets and choose either background row independently at every other singleton column.

There is no three-black tilted rectangle. A putative support uses zero labels, one label, or at least two: these cases are excluded respectively by the binary sea lemma, its private prescription, or its positional event. This also excludes hidden tilted rectangles and all singleton presentations.

Two tilted rectangles with the same two-point presentation either reduce to a hidden rectangle or give a mixed four-cell support. The latter uses at most four double labels and has already been excluded by the same zero/one/several-label classification.

A vertical axis rival is excluded by the vertical Pythagorean events and the one-label argument above. A horizontal or oblique axis rival is itself a nonvertical mixed support, or reduces to a hidden rectangle. There is no need to infer that an auxiliary rectangle through two chosen double cells fits the strip: the actual support is counted directly. This covers supports with three and four labels, which were the obstacle to the earlier greedy construction.

Axis-axis identification follows from distinct parity double labels and the bipartite double graph. All possible collisions are therefore covered. The resulting infinite-strip assignment is identifying.

All influence offsets are \(O(W_h)\). Restrict to an interval containing the centers and influences, and retain constant exterior collars. Its width is
\[
 O(q'T(h)^2+W_h)=h^{2+o(1)}.
\]
This is a full board with one black cell in each non-double column, not an identifying scaffold with empty columns.

## 5. The four-background cover at odd height

For odd \(h\ge9\), use the binary seas
\[
 \{1,h-1\},\quad \{2,h\},\quad
 \{1,h-3\},\quad \{4,h\}.
\]
The second and fourth are reflections of the first and third. Their full-sea validity and isolated-gadget criteria were proved in [threshold_progress.md](threshold_progress.md), Sections 9–10.

Write a parity edge as an odd row \(r\) and an even row \(s\). Edges with \(r=1\) or \(r=h\) are covered by the first or second background. An edge that fails both first backgrounds must have
\[
 r=h-4u^2=1+4v^2,\qquad u,v\ge1.
\tag{3}
\]
For the third background, the only possible vertical obstructions at this \(r\) would require one of
\[
 4u^2-2,\qquad8u^2-2,\qquad12u^2
\]
to be a square. The first two have 2-adic valuation one, and the third has odd 3-adic valuation. Thus every such edge with \(s\le h-3\) is covered.

The only remaining even endpoint is \(s=h-1\). Reflecting the edge gives even endpoint \(2\) and odd endpoint \(h-4v^2\), so it is covered by the reflected third background. Hence the four groups cover every parity edge.

Apply the positional local lemma independently to these at most four groups. Their constant collars can be connected by the established adjacent-row switches and boundary switches, at cost \(O(W_h)\) per join. All blocks are checked against the same full final parity pair set, so far vertical and singleton axis rivals remain covered. A local tilted collision crossing a join lies inside one of the constant-tail extensions. Each label is assigned to only one group.

The finitely many smaller odd heights are absorbed by the earlier fixed-height construction. Constant row-1 tails provide every larger width. Thus the audited conclusion is an all-height equality threshold
\[
 m_h\le h^{2+o(1)}.
\]

The exact order \(m_h=O(h^2)\) remains unproved.

## 6. Audit of the averaged-divisor refinement

The subsequent [polylogarithmic threshold proof](polylogarithmic_threshold.md) replaces the maximum divisor function by a uniform second moment and gives
\[
 m_h=O\!\left(h^2(1+\log h)^{16}\right).
\]
I checked its fixed-edge affine-form coverage, height-only exceptions, and dyadic summation.

For the private influence count, every ordinary row factor is a nonconstant bounded-coefficient affine form in the central edge rows. The only pure-height three-black factor has the two sea points adjacent; the missing corner then forces the central row to be at most \(h-g+1\le4\). A mixed side using both sea rows has a positive integral vertical translate \(j\le h-g\le3\); its one-label case forces the central row \(1+2j\le7\). These are covered by the explicit low-row weight.

For the several-label squared count, a varying affine form takes each value only \(O(h^{d-1})\) times in a \(d\)-dimensional row box. Thus \(\sum_{n\le Ch}\tau(n)^4=O(h(1+\log h)^{15})\) supplies the stated uniform moment. If a factor is constant in the other labels, it is already in the fixed-edge weight. Reusing the same endpoint to cancel a variable would repeat a point, which is excluded from a genuine support.

The remaining pure-height mixed family has its side on the sea rows and exactly two double labels on the black diagonal. Its row-sum constraint leaves only \(O(h)\) partner labels for a fixed edge. Hence its squared contribution is \(O(h\tau(g-1)^2)=O(h^2)\), within the required bound.

Finally, the class width
\[
 C\left(nw^2+\sqrt{nQ}\,w(1+\log h)^8\right)
\]
satisfies the weighted local lemma. Summing over \(O(\log h)\) dyadic classes and using \(\sum nw^2=O(Q(1+\log h)^{15})\) yields \(O(Q(1+\log h)^{16})\). The constant-tail gluing cost is smaller. No gap was found in this refinement; the absolute quadratic bound still remains open.


