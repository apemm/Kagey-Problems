# A linear P palette with additional linear-level constraints

9 November 2026. Fix a finite set \(\mathcal K\) of integers, none equal
to \(-1\). In addition to the global P graph, require different colors for
two labels \((a,b),(a',b')\) whenever
\[
b+ka=b'+ka'\qquad\text{for some }k\in\mathcal K.
\tag{1}
\]
Then the augmented graph still has chromatic number \(O_{\mathcal K}(h)\).

For example, \(k=0,4\) make the even rows and the levels \(b+4a\) distinct
within each color block. These conditions exclude some additional
collisions. They do not settle all remaining three- or four-point geometry.

The proof retains the arithmetic bands from global_P_linear_coloring.md.
It replaces Hall's theorem by independent thinning, concentration, and
a list-coloring local lemma.

## 1. Blocker frequency along a linear level

Fix an odd row \(s\) and a level \(b+ka=t\). A vertex on that level whose
blocker set contains \(s\) satisfies
\[
(s-t+ka)^2+4(s-a)^2=L^2,\qquad 1\le L\le h-1.
\]
Put \(A=k^2+4\) and \(X=Aa+k(s-t)-4s\). Completing the square gives
\[
X^2-A L^2=-4\bigl((k+1)s-t\bigr)^2.
\tag{2}
\]
The right side is nonzero: \(t=b+ka\) has parity \(k\), whereas
\((k+1)s\) has parity \(k+1\).

If \(k\ne0\), the integer \(k^2+4\) is nonsquare. The primitive root-class
argument from global_P_fixed_scale_corollary.md applies to (2). The fixed
coefficients give norm \(O_k(h^2)\) and coordinates \(O_k(h)\), so it gives
\(h^{o(1)}\) solutions uniformly in \(s,t\).

If \(k=0\), the even row \(b=t\) is fixed. The factorization
\[
\bigl(L-2(s-a)\bigr)\bigl(L+2(s-a)\bigr)=(s-t)^2
\]
gives the same bound. Thus a fixed odd row belongs to the blocker sets of
only \(h^{o(1)}\) vertices in any one added clique. The original odd-row
cliques have this frequency bound by the P theorem. All blocker sets
also have size \(h^{o(1)}\).

## 2. Equalizing eligibility probabilities

Consider a band of \(N\) offsets \(u=a-b\), with
\[
D(u)\le2R\log h,\qquad R\ge1,\qquad N\ge h^{1/3}.
\]
Each original odd-row clique has at most \(N\) vertices in this band.
An added clique does too: on \(b+ka=t\), the offset is
\(u=(k+1)a-t\), which determines at most one vertex since \(k+1\ne0\).

Write \(r=|\mathcal K|\), and take
\[
K=\left\lceil8192(r+1)RN\right\rceil,\qquad
p=\frac1{64R},\qquad q=h^{-1/8}.
\tag{3}
\]
For each color independently, sample a subset \(S\) of the odd rows,
including each row with probability \(p\). For each vertex \(v=(a,b)\)
and color, also sample an independent coin with success probability
\[
\theta_v=\frac{q}{(1-p)^{|B(v)|}}.
\tag{4}
\]
This is at most one for large \(h\), because
\((1-p)^{|B(v)|}\ge h^{-1/16}\).

The color is eligible for \(v\) when \(a\in S\), \(B(v)\cap S\) is empty,
and the coin succeeds. Conditional on \(a\in S\), its probability is
exactly \(q\); unconditionally it is \(pq\). Eligibility still excludes
all P edges between distinct odd-row cliques. Thinning only deletes
eligible vertices.

## 3. List and color-degree bounds

For each vertex, the \(K\) colors are independent. Its expected eligible
list length is
\[
Kpq\ge128(r+1)Nq.
\]
Chernoff's bound and a union bound over at most \(h^2\) vertices show that
all lists have length at least
\[
L=\left\lfloor64(r+1)Nq\right\rfloor
\tag{5}
\]
with probability tending to one.

Fix a color and one clique. In an odd-row clique, condition on its common
odd row belonging to \(S\). If it does not, the count is zero; if it does,
each vertex is eligible with probability \(q\). In an added clique,
each vertex has unconditional eligibility probability \(pq\le q\).
In either case the expected eligible count is at most \(Nq\).

The relevant indicators have a dependency graph of maximum degree
\(h^{o(1)}\). For an odd-row clique, their shared random variables are
blocker-row choices. For an added clique, include each vertex's own-row
choice. A row occurs in at most one own-row position in that clique and
in only \(h^{o(1)}\) blocker sets by Section 1. Each indicator uses
\(h^{o(1)}\) rows and one private coin.

Here is the concentration estimate explicitly. Properly color that
dependency graph with \(J=h^{o(1)}\) classes. Indicators in each class
are independent. If their total is \(Z\), Hölder's inequality gives
\[
\mathbb E e^{tZ/J}
 \le \exp\!\left(\frac{(e^t-1)\mathbb EZ}{J}\right).
\]
Taking \(t=\log2\) and \(\mathbb EZ\le Nq\) gives
\[
\Pr(Z>2Nq)\le
 \exp\!\left(-\frac{(2\log2-1)Nq}{J}\right).
\tag{6}
\]
Since \(Nq\ge h^{5/24}\), the exponent dominates every fixed multiple of
\(\log h\). There are \(O_{\mathcal K}(h)\) cliques and
\(K=h^{1+o(1)}\) colors. Thus every color has at most \(2Nq\) eligible
vertices in every clique, with probability tending to one.

Fix palettes satisfying both bounds and trim each list to length \(L\).
In the graph consisting of original and added clique edges, every vertex
and color have at most
\[
d_{\rm col}=2(r+1)Nq
\tag{7}
\]
neighbors eligible for that color.

## 4. The final list-coloring local lemma

Independently assign each vertex a uniform color from its trimmed list.
For each clique edge and each color in both endpoint lists, the bad
event that both endpoints choose that color has probability \(L^{-2}\).

A vertex belongs to at most \(L\,d_{\rm col}\) such events. Each bad event
therefore depends on at most \(2L\,d_{\rm col}\) other events. For large \(h\),
\[
e\,\frac{2L\,d_{\rm col}+1}{L^2}<1.
\tag{8}
\]
The symmetric local lemma supplies a coloring with no bad event.
It is proper on all original and added cliques. P edges across original
cliques were already excluded by eligibility.

Thus a large band uses \(O_{\mathcal K}(RN)\) colors. For a small band,
the P orientation has outdegree \(O(RN\log h)\), and each added clique
contributes at most \(N-1\) neighbors per vertex. The same greedy bound
therefore applies, up to a constant depending on \(\mathcal K\).

The original band estimates
\[
\sum RN=O(h),\qquad
\text{total small-band cost}=h^{1/3+o(1)}=o(h)
\]
complete the proof.

## 5. A geometric consequence and its limit

Within a block, put \(u=b_0-a_0\), \(w=b_1-a_1\),
\(d=a_1-a_0\), and \(t=a_2-a_0\). An angle centered at the even
point of label zero, with one other even point and one odd point, obeys
\[
(5d+w-u)t=u(d+w-u).
\]
The denominator cannot vanish in a nondegenerate instance. If \(w\ne u\),
it follows that
\[
5d+w-u\mid4u(w-u),
\]
leaving divisor-many possibilities for fixed offsets. If \(w=u\),
the equation requires \(5t=u\), impossible because \(t\) is even and
\(u\) odd.

For three even points, put \(d_i=a_i-a_0\) and
\(v_i=(b_i-a_i)-(b_0-a_0)\). The right-angle equation is
\[
(5d_1+v_1)(5d_2+v_2)=-4v_1v_2.
\tag{9}
\]
If one \(v_i\) vanishes, the other factor must vanish, giving two
labels with the same \(b+4a\). The choice \(k=4\) excludes this
degenerate case. If both \(v_i\) are nonzero, (9) still leaves
divisor-many possibilities for fixed offsets.

The theorem does not exclude these nondegenerate solutions, the generic
even-odd angle equation, mixed four-cell collisions, or cross-block
configurations. It is a palette refinement, not a complete identifying
construction.

This limitation has a small certificate. At height twenty, the labels
\[
(1,12),(3,20),(11,2),(13,10)
\]
are P-free, have distinct even rows, and have distinct \(b+4a\) values
\(16,32,46,62\). Yet their even points
\[
(0,12),(4,20),(20,2),(24,10)
\]
form a hidden rectangle with perpendicular sides \((4,8),(20,-10)\).
The two half-rectangles share the white pair \((2,16),(22,6)\), so this
is an immutable collision. The \(k=0,4\) refinement does not exclude it.

More generally, no fixed finite family of these level rules automatically
excludes every hidden rectangle. Choose an integer
\(r>10+\max(\{0\}\cup\{|k|:k\in\mathcal K\})\), and put \(t=8(r+2)^2\).
Use the labels
\[
(1,2t),\quad(3,2t+2r),\quad
(2r+1,2t-8),\quad(2r+3,2t+2r-8)
\]
at height \(h=2t+2r\). Their even points have perpendicular side vectors
\((4,2r)\) and \((4r,-8)\). All levels \(b+ka\) are distinct: the four
possible difference types, after division by two, are
\[
r+k,\quad rk-4,\quad(k+1)r+k-4,\quad(1-k)r+k+4,
\]
all nonzero for the chosen \(r\).

Every odd-to-even vertical difference \(d\) exceeds \(8(r+1)^2\), whereas
every horizontal difference \(X\) has \(|X|\le4(r+1)\). Thus
\(X^2<2d+1\), and \(d^2+X^2\) lies strictly between consecutive squares.
These labels are P-free. Halving the first rectangle side again gives
an in-strip pair of colliding rectangles. This does not prevent a
carefully chosen augmented coloring from avoiding such examples; it
shows that the finite list of level rules alone does not imply validity.

## 6. Review and arithmetic checks

The independent review in global_P_linear_levels_independent_audit.md
checks the norm reduction, thinning, dependency-graph concentration,
local-lemma event count, and band sum. No gap was found.
The standard-library checker verify_global_P_extensions.py additionally
verified 40,950 instances of the completed-square identity and the
explicit hidden-rectangle certificates. Its data are in
global_P_extensions_arithmetic_check.json.

