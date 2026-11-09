# Near-quadratic equality thresholds at every height

9 November 2026. This construction controls actual forbidden black supports directly. It replaces the strong pair exclusion in `threshold_progress.md`, whose cubic limitation is proved in Section 12 of that note.

The [averaged-divisor refinement](polylogarithmic_threshold.md) makes the width bound explicit as \(O(h^2(1+\log h)^{16})\). This note supplies the underlying positional construction and its complete geometric proof.

**Theorem.** The equality threshold satisfies
\[
 m_0(h)\le h^{2+o(1)}.
\]
Equivalently, for every fixed \(\epsilon>0\), there is \(C_\epsilon\) such that every height \(h\ge3\) and every width \(m\ge C_\epsilon h^{2+\epsilon}\) admit exactly \(m+\lfloor h^2/4\rfloor\) black cells in an identifying blackout. All columns are filled, every opposite-parity pair occurs in exactly one double column, and the construction extends to every larger width. Combined with the established axis upper bound, this determines the extremal value throughout that width range.

Write
\[
 W=1+\left\lfloor(h-1)^2/4\right\rfloor.
\]
A tilted lattice rectangle has horizontal span at most \(W\), and two such rectangles sharing a corner have union span at most \(2W\). Work first in the infinite horizontal strip, and later restrict to finite intervals. Let \(F\) be the full opposite-parity pair set. Every local vertical or singleton axis-rival test uses this full set, including pairs assigned to other blocks.

Two rectangles have identical white presentations if and only if their symmetric difference is black. Common corners remain uncolored in this criterion. Three common corners determine a rectangle. If two rectangles share a pair that is a side in both or a diagonal in both, their four nonshared points form a hidden rectangle. The remaining two-common-corner case is a mixed side/diagonal support.

## 1. The variables and the events

First fix one valid binary sea alphabet and a family of \(q\) parity edges, each admitting a valid monotone one-double gadget on that alphabet. Choose the double centers \(X_e\) independently and uniformly from \(\{1,\ldots,N\}\). Coincident centers are initially allowed by the product measure and subsequently forbidden by an overlap event.

Let \(A_e\) be the one-double influence set: the required sea columns in every three-black tilted rectangle or nonvertical mixed four-black support that uses this double and otherwise only the two sea rows. Every translated configuration is anchored at the double center. The fixed-row factorization arguments give
\[
 |A_e|\le CT,
 \qquad T=\max_{1\le n\le16h^4}\tau(n)=h^{o(1)}.
\]
Prescribe the values from the valid monotone gadget on \(A_e\). Include zero in \(A_e^*=A_e\cup\{0\}\).

Use the following events.

* For every pair of labels, forbid intersecting translates of their \(A_e^*\). This simultaneously ensures that all centers differ, prescriptions do not land on another double, and prescriptions do not conflict.
* For every set of \(k=2,3\) double labels, forbid a three-black tilted rectangle whose required black support uses exactly those labels and whose remaining support points use sea rows.
* For every set of \(k=2,3,4\) labels, forbid a nonvertical mixed four-black support using those labels, with all remaining support points in sea rows.
* For every pair of labels, forbid a tilted black diagonal through those doubles that admits an in-grid vertical white diagonal with opposite-parity endpoints.

For a fixed label set, a point can take either endpoint row of its edge. It can also take either of the two sea rows if it has no double label. At most four points occur. Thus the number of role and row choices is bounded by an absolute constant, not by a power of \(h\).

## 2. Finite geometry counts, including degeneracies

A tilted three-corner support has a right-angle vertex. With its three rows fixed, orthogonality is
\[
 (x_1-x_0)(x_2-x_0)=-(r_1-r_0)(r_2-r_0).
\]
The right side is nonzero. A zero row difference would make one leg horizontal and the other vertical, giving an axis-aligned rectangle, or would make two corners coincide. There are therefore \(O(T)\) translated geometries for fixed rows.

For a mixed support, write \(U=(x,y)\) for the black side vector, \(V=(z,v)\) for the black diagonal vector, and \(H\) for the difference of black-pair sums. With rows fixed and \(x\ne0\), the equations are
\[
 x^2+y^2=z^2+v^2,\qquad xH_x+yH_y=0,
 \quad H\ne0,\quad V\ne\pm U.
\]
If \(y\ne0\), then \(H_y\ne0\), and \(x\mid yH_y\). If \(y=0\), then \(H_x=0\), \(v\ne0\), and \((x-z)(x+z)=v^2\). Both cases give \(O(T)\) translated geometries. Repeated double columns and repeated rows merely impose additional filters. Common corners remain uncolored.

For a vertical rival, let the tilted black diagonal have vector \((D,d)\) and the vertical diagonal length be \(L\). If \(d\ne0\), then
\[
 (L-D)(L+D)=d^2,
\]
so there are \(O(T)\) possible gaps. The case \(d=0\) is not a missing infinite family: integral vertical endpoints require \(L\) even, so the presentation has same-parity rows and no parity axis rival. Two black points in the same double column cannot have a distinct vertical alternative diagonal.

For each translated geometry using \(k\) labels, the relative positions of all \(k\) centers are fixed. There are at most \(N\) allowed common translations in the \(N^k\) position assignments. Hence
\[
 \Pr(E_k)\le \frac{CT}{N^{k-1}},
 \qquad
 \Pr(E_{\mathrm{overlap}})\le \frac{CT^2}{N}.       \tag{1}
\]

## 3. The dependency estimate

Events depend only on their explicitly named double-center variables. Events on disjoint label sets are independent, even if their possible geometric sea supports could overlap. The sea letters have not yet been randomized or assigned; they do not enter the event measure.

For precision, combine all bad conditions on a given label set into one event. For a two-label set this includes influence overlap, triple supports, mixed supports, and vertical rivals. For three labels it includes triple and mixed supports. For four labels it includes mixed supports. Increasing a universal constant \(C\) if needed, their probability bounds are
\[
 p_2=CT^2/N,\qquad p_3=CT/N^2,\qquad p_4=CT/N^3.              \tag{2a}
\]
There is at most one combined event for each label subset.

Assign an arity-\(k\) event weight \(x_k=2p_k\). A variable is incident to at most \(q^{k-1}\) events of arity \(k\). Its incident weight sum is bounded by
\[
 2C\left(\frac{qT^2}{N}
       +\frac{q^2T}{N^2}+\frac{q^3T}{N^3}\right).               \tag{2}
\]
Choose \(N=\lceil C_0(q+1)T^2\rceil\), where the absolute constant \(C_0\) satisfies
\[
 2C(C_0^{-1}+C_0^{-2}+C_0^{-3})\le1/8
 \quad\text{and}\quad C_0\ge8C.
\]
Then (2) is at most \(1/8\), and every event weight is less than one. Each event uses at most four variables, so its neighbors' weight sum is at most \(1/2\). Therefore
\[
 \prod_{F\sim E}(1-x_F)\ge1-\sum_{F\sim E}x_F\ge\tfrac12,
\]
and \(\Pr(E)\le x_E\prod_{F\sim E}(1-x_F)\). The asymmetric local lemma gives a position assignment avoiding all events.

The estimate requires no independence between different row roles of a single event. Those roles were combined by a union bound before applying the local lemma.

## 4. Completeness after the sea is filled

Copy each gadget on its translated influence set, and fill every other non-double column with either sea row. All prescriptions are consistent.

Every actual required support point at a double column must be attributed to that double label, even if its row is also a sea row. With that convention, a forbidden support has zero labels, one label, or at least two labels. Zero-label supports are excluded by the valid binary sea. One-label supports are broken by the gadget prescription. Supports with at least two labels are excluded by the positional events.

In particular, every tilted rectangle has at most two black corners. This eliminates hidden tilted rectangles, tilted singleton presentations, and six-black collisions. Side/side and diagonal/diagonal collisions reduce to a hidden rectangle. A hidden axis rectangle would require a repeated double edge, which is absent. Every remaining tilted collision or horizontal/oblique axis rival is a nonvertical mixed four-point support and was covered directly, irrespective of whether it uses two, three, or four double labels.

A vertical rival with two different double labels was explicitly forbidden. A vertical rival with at most one double label is excluded by the chosen good-gadget background: the direct row analysis applies to a central point and either sea row at arbitrary horizontal separation. It is not merely a claim that one particular monotone sea arrangement is safe. This distinction is necessary and is satisfied by the backgrounds below.

The global axis-axis test uses unique opposite-parity double edges, so the double graph is bipartite. Thus all rectangles are identified, with exactly one black cell in every non-double column.

## 5. Four backgrounds cover every odd-height edge

For even \(h\), the single alphabet \(\{1,h\}\) handles every parity edge.

For odd \(h\ge9\), use
\[
 \{1,h-1\},\quad \{2,h\},\quad
 \{1,h-3\},\quad \{4,h\}.                       \tag{3}
\]
The second and fourth are the row reflections of the first and third. For an even \(g\) satisfying \(2g-1>h\), the alphabet \(\{1,g\}\) is a full valid parity sea. An edge contained in \([1,g]\) has a valid monotone one-double gadget unless its odd endpoint \(r\) satisfies
\[
 j(g-r+j)\text{ is a square},\qquad
 1\le j\le h-g,\quad r-j\ge1.                   \tag{4}
\]
These are exactly its opposite-parity vertical rivals. An even central row gives an even-gap presentation, so it cannot produce such a rival.

Here are complete proofs of the two background assertions used in this section.

**The binary sea.** In a three-black tilted rectangle on two row levels, two black corners repeat a row and form a horizontal diagonal. The fourth row would be \(2-g<1\) or \(2g-1>h\). Thus there are no three-black or hidden tilted rectangles. A mixed-row black diagonal has a half-integral midpoint row, so it has no horizontal presentation. Its vertical alternative extends below row 1. A repeated-row black diagonal instead has an even-gap vertical presentation and hence no parity axis rival.

A tilted black side must join rows 1 and \(g\), so its vertical component is odd. In a mixed collision, integrality of the shared pair forces the black diagonal to have odd row sum. It therefore also uses rows 1 and \(g\). The two black-pair row sums are equal, so \(H_y=0\); perpendicularity and the side's nonzero horizontal component force \(H_x=0\), a degeneracy. This handles tilted mixed collisions and the mixed oblique-axis case. The other two-common-corner collisions give hidden rectangles. An axis rectangle cannot be hidden because every sea column is a singleton. This exhausts sea failures.

**The one-double gadget.** If \(e\subset[1,g]\), the black points of \(1^\infty e g^\infty\) form a chain in the coordinatewise order. A chain contains no three corners of a tilted rectangle: the dot product at any candidate right-angle vertex can vanish only for a horizontal and a vertical leg, giving an axis-aligned rectangle.

Nor can a chain contain a nonvertical mixed support. Orient its side \(AB\) so that \(U=B-A\) has positive horizontal component and nonnegative vertical component. Orient the diagonal \(CD\) in the chain order, and put \(p(X)=(X-A)\cdot U\). The mixed equations give
\[
 p(C)+p(D)=|U|^2,\qquad
 |p(D)-p(C)|=|V\cdot U|<|U|^2.
\]
The inequality is strict because \(|V|=|U|\) and \(V\ne\pm U\). Both diagonal endpoints therefore have projection strictly between those of \(A,B\). If both components of \(U\) are positive, the chain order forces \(A\le C\le D\le B\), whence \(0\le V\le U\) componentwise. Equal norms force \(V=U\), a contradiction. If \(U\) is horizontal, the strict projections put the diagonal endpoint columns strictly between those of \(A,B\); their rows must equal \(A_y=B_y\), giving the same contradiction. This also excludes horizontal axis rivals.

The hidden-rectangle reductions exclude side/side and diagonal/diagonal collisions. Axis-axis uniqueness holds because there is only one double. There are no tilted singleton presentations. The only remaining possible failure is a virtual vertical-axis rival.

A diagonal involving row 1 has no in-grid vertical alternative. The central vertical pair cannot have a distinct vertical alternative, and repeated-row sea diagonals give even-gap presentations. The remaining diagonal joins a central row \(r\) to sea row \(g\). Put \(d=g-r\). A vertical alternative has length \(L>d\), must satisfy \(L\equiv d\pmod2\), and has endpoints within the strip exactly when
\[
 L=d+2j,\quad1\le j\le h-g,\quad r-j\ge1.
\]
Its horizontal separation squared is \(L^2-d^2=4j(g-r+j)\). The white row difference is odd exactly when \(r\) is odd. This proves (4), including its necessity and sufficiency.

For even \(h\), take \(g=h\). Then there is no positive \(j\le h-g\), so every parity edge has a good gadget. For the reflected alphabets in (3), apply the row reflection \(r\mapsto h+1-r\). It preserves the full parity pair set.

The first background fails only at odd row \(h\), or at
\[
 r=h-4u^2\ge3.
\]
Its reflection fails only at row 1, or at
\[
 r=1+4v^2\le h-2.
\]
Rows 1 and \(h\) are consequently covered. A row missed by both satisfies
\[
 r=h-4u^2=1+4v^2,
 \qquad5\le r\le h-4.                          \tag{5}
\]

If its even partner is at most \(h-3\), use the third background. The three values in (4) are
\[
 4u^2-2,\qquad8u^2-2,\qquad12u^2.
\]
The first lies between consecutive squares, the second is 6 modulo 8, and the third has odd 3-adic valuation. None is a square.

If the even partner is \(h-1\), reflect the edge. Its even partner becomes 2, and (5) gives reflected odd row \(h-4v^2\). The third-background argument now applies to the reflected edge, so the original edge belongs to the fourth background. This exhausts all parity edges. In fact, for \(h\equiv3\pmod4\), the first two backgrounds already suffice, since (5) would force \(4\mid h-1\).

## 6. Width, gluing, and the scope of the conclusion

Partition the parity edges among the at most four backgrounds. Apply the local lemma independently to each group. The sum of their center intervals has length
\[
 O\left(\sum_i(q_i+1)T^2\right)=O(h^2T^2).
\]
Influence sets have offsets in \([-2W,2W]\). Add margins containing those sets and constant collars of length \(L=2W\). Each block can choose its distant unprescribed sea letters to be its anchor row, which is 1 or \(h\). Connect different anchors with single boundary switches \(1^\infty h^\infty\) or their reflections. Such switches are valid: their black points form a chain, so the preceding no-three-corner and mixed-support arguments apply; a vertical presentation from a mixed boundary diagonal exits the strip. There are only constantly many blocks and switches, so the collars and connections cost \(O(W)=O(h^2)\) columns.

The locality argument uses length \(2W\) for a pair of tilted rectangles. Far singleton and vertical axis rivals were already tested against the full parity pair set in every block. Axis-axis uniqueness holds globally because each edge was assigned to exactly one group. Thus gluing preserves identification.

Finally, constant tails extend the construction to every larger width. For each fixed height below nine, concatenate the isolated words \(1^L e h^L1^L\), one per parity edge. Their validity follows from the same chain proof and boundary-switch gluing. These finitely many heights are absorbed into the constants.

The standard elementary divisor estimate gives \(T(h)=h^{o(1)}\). One quick proof of the needed uniform estimate is to fix \(\delta>0\). For all sufficiently large primes \(p\), \(a+1\le p^{\delta a}\) for every \(a\ge0\). For each of the finitely many smaller primes, the supremum of \((a+1)p^{-\delta a}\) is finite. Multiplying these bounds gives \(\tau(n)\le C_\delta n^\delta\). Apply this with \(n\le16h^4\) and arbitrarily small \(\delta\).

Thus the width bound \(O(h^2T(h)^2+h^2)\) is \(h^{2+o(1)}\). The necessary number of double columns is \(\lfloor h^2/4\rfloor\), so this reaches the optimal polynomial exponent. It does not prove an absolute \(O(h^2)\) bound or determine the exact threshold.

## 7. Finite verification and reproducibility

The companion `near_quadratic_threshold_check.py` implements bounded positional resampling, copies the private prescriptions, adds the constant collars and boundary switches, and fills every other column. It then uses direct presentation hashing of every tilted rectangle and the full parity-axis rival tests to verify the resulting board. Axis-axis validity is checked through the complete list of distinct parity doubles. The final presentation check does not reuse the positional event test.

The saved run in `near_quadratic_threshold_check.json` verifies complete boards at heights 4, 6, 8, and 9, of widths 261, 1062, 1843, and 2457. The height-nine example uses all four background alphabets, so it tests both reflections and every type of connection. The run checks 948,576 tilted rectangles and takes about 0.74 seconds. The interval multiplier 128 is an empirical choice for these examples, not a claimed value of the universal constant in the theorem.

The earlier explicit greedy boards and their checks remain in `threshold_progress.md` and `threshold_progress_check.json`. The smaller widths in some of those examples are compatible with the present theorem: the asymptotic local-lemma proof is not a claim that random placement minimizes small-height width.
