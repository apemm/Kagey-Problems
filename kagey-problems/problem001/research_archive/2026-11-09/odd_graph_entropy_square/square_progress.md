# Square boards: a stronger lower bound and a limit of local budgets

9 November 2026. No exponent improvement is proved here. The lower bound gains
a logarithmic factor:

\[
 \boxed{\displaystyle
 f(n,n)=\Omega\!\left(\frac{n^{6/5}}{(\log(n+2))^{1/5}}\right).}
 \tag{1}
\]

The previous deletion bound was
\(\Omega(n^{6/5}(\log(n+2))^{-2/5})\). The upper bound from
[square_local_budget.md](../../2026-11-08/square_local_budget.md) remains

\[
 f(n,n)=O\!\left(\frac{n^{4/3}}{(\log(n+2))^{1/3}}\right).
 \tag{2}
\]

The proof of (1) controls overlaps between six-point obstructions, then uses
the independent-set theorem for linear hypergraphs. A second theorem shows
that the numerical local-box budgets used for (2), even together with their
global counterpart, admit sets at the scale of (2). Improving that method
requires information beyond these aggregate inequalities.

## 1. The obstruction hypergraphs

Write \(V=\{0,\ldots,n-1\}^2\) and \(\Lambda=1+\log n\). A rectangle always
means a nondegenerate rectangle with four corners in \(V\), including tilted
rectangles. Let \(d(P)\) count rectangles through \(P\), and let \(m(P,Q)\)
count rectangles containing two distinct fixed points. Put

\[
 D=\max_Pd(P),\qquad M=\max_{P\ne Q}m(P,Q).
\]

The primitive-direction count in the existing square appendix gives

\[
 D\le8n^2\Lambda,
 \qquad |\mathcal R|\le2n^4\Lambda.
 \tag{3}
\]

Also \(M\le6n\). If \(PQ\) is a side, the other side is obtained by an
integral perpendicular translation, giving \(O(n)\) choices. If \(PQ\) is a
diagonal, a third corner lies on its diameter circle. For each integer
horizontal coordinate there are at most two possible vertical coordinates.
This again gives \(O(n)\) choices, and the displayed constant is sufficient.

Use the same two hypergraphs as the existing deletion proof:

* \(\mathcal A\) contains the four corners of every rectangle, and the
  four-point symmetric differences of rectangles sharing two corners that
  form a side of one rectangle and a diagonal of the other.
* \(\mathcal B\) contains the six-point symmetric differences of rectangle
  pairs sharing exactly one corner.

They are simple hypergraphs: repeated descriptions of the same edge do not
create repeated edges. The established counts, with the divisor-bound
parameter fixed at \(1/20\), give

\[
 |\mathcal A|=O(n^{41/10}\Lambda),\qquad
 |\mathcal B|=O(n^6\Lambda^2).
 \tag{4}
\]

For the first estimate, a rectangle side can be the diagonal of at most
\(O(n^{1/10})\) rectangles, by the standard divisor bound for sums of two
squares. The second follows from
\( |\mathcal B|\le\sum_X\binom{d(X)}2\).

Avoiding both hypergraphs is sufficient for validity. Two rectangles sharing
no corner would require two fully black rectangles. If their two shared
corners form sides of both or diagonals of both, their four-point symmetric
difference is itself a rectangle. The remaining two-corner case belongs to
\(\mathcal A\), and the one-corner case belongs to \(\mathcal B\).
Three distinct corners determine a rectangle uniquely, so distinct
rectangles cannot share three corners.

These observations and (4) are already present in
[the square appendix](../../../jis/sections/appC_square.tex). The following
codegree estimates are the extra input.

## 2. Six-point obstructions have small codegrees

For \(j\ge1\), let \(\Delta_j\) be the largest number of edges of
\(\mathcal B\) containing a specified \(j\)-point set.

**Codegree lemma.** The following bounds hold:

\[
 \begin{array}{c|c|c}
 j&\text{explicit bound}&\text{asymptotic bound}\\ \hline
 1&3D^2&O(n^4\Lambda^2)\\
 2&5MD&O(n^3\Lambda)\\
 3&D+6M^2&O(n^2\Lambda)\\
 4&10M&O(n)\\
 5&10&O(1).
 \end{array}
 \tag{5}
\]

**Proof.** Every edge in \(\mathcal B\) decomposes into two disjoint triples.
Each triple consists of three rectangle corners, and both triples have the
same missing corner \(X\). A specified triple determines its rectangle and
its completion uniquely. A specified pair belongs to at most \(M\)
rectangles, with at most two choices of missing corner in each. For fixed
\(X\), the number of these triples containing a specified point \(P\) is
at most \(m(X,P)\). Moreover,

\[
 \sum_{X\ne P}m(X,P)=3d(P).
 \tag{6}
\]

For \(j=1\), choose a rectangle through the fixed point, choose one of its
other three corners as \(X\), then choose the other rectangle through
\(X\). This gives \(3D^2\).

For \(j=2\), the fixed pair either lies in one triple or is split between
the triples. The first case has at most \(2MD\) choices. The second has at
most
\(\sum_Xm(X,P)m(X,Q)\le3MD\), by (6).

For \(j=3\), all three fixed points in one triple leave at most \(D\)
choices for the other rectangle. Otherwise the split is \(2+1\). There
are three choices of fixed pair, at most \(2M\) possible completions for
that pair, and at most \(M\) partner rectangles at each completion. The
bound is \(D+6M^2\).

For \(j=4\), a \(3+1\) split has four choices for its triple and at most
\(M\) choices for the partner rectangle. A \(2+2\) split has three
unordered pair partitions. The first pair permits at most \(2M\)
completions. Each completion and the second pair determine at most one
rectangle. This gives \(4M+6M\).

For \(j=5\), the only split is \(3+2\). There are ten choices of triple,
and its completion together with the remaining pair determines at most one
partner rectangle. Overcounting multiple decompositions only increases these
upper bounds. \(\square\)

## 3. A sparse sample can be made linear

Choose each point of \(V\) independently with probability

\[
 p=n^{-79/100},\qquad N_0=n^2p=n^{121/100}.
 \tag{7}
\]

Let \(U\) be the resulting set. Delete one point from every surviving edge
of \(\mathcal A\). Also delete one point from the union of every pair of
distinct surviving \(\mathcal B\)-edges intersecting in at least two
points. It is enough to choose all deletions from the initial sample, before
performing them. The number of deleted points is bounded by the number of
listed objects. The surviving \(\mathcal B\)-hypergraph is linear.

The expected number of four-point edges, divided by \(N_0\), is

\[
 O(n^{41/10}\Lambda p^4/N_0)
   =O(n^{-27/100}\Lambda)=o(1).
 \tag{8}
\]

For two six-point edges whose intersection has exactly \(j\) points, their
union has \(12-j\) points. Their number is at most
\(\binom6j|\mathcal B|\Delta_j\). Equations (4), (5), and (7) therefore
give the following expected counts, divided by \(N_0\):

\[
 \begin{array}{c|c|c}
 j&\text{bound before substituting }p&\text{bound after substituting }p\\ \hline
 2&O(n^7\Lambda^3p^9)&O(n^{-11/100}\Lambda^3)\\
 3&O(n^6\Lambda^3p^8)&O(n^{-32/100}\Lambda^3)\\
 4&O(n^5\Lambda^2p^7)&O(n^{-53/100}\Lambda^2)\\
 5&O(n^4\Lambda^2p^6)&O(n^{-74/100}\Lambda^2).
 \end{array}
 \tag{9}
\]

All four expressions tend to zero. Thus the deletions cost \(o(N_0)\)
points in expectation.

The expected number of surviving six-point edges before deletion is at most
\(Cn^6\Lambda^2p^6\). Chernoff's inequality gives
\(|U|\ge3N_0/4\) with probability tending to one. Markov's inequality
simultaneously gives at most \(N_0/4\) deletions and at most
\(4Cn^6\Lambda^2p^6\) surviving six-point edges with positive probability.
Consequently, there exists \(U'\subseteq U\) such that

\[
 |U'|\ge N_0/2,\qquad
 \mathcal A[U']=\varnothing,\qquad
 \mathcal B[U']\text{ is linear},
\]

and its average degree is at most

\[
 d_0=C_0n^4p^5\Lambda^2=C_0n^{1/20}\Lambda^2.
 \tag{10}
\]

The choice \(79/100\) is convenient, not optimal. Any fixed sampling
exponent strictly between \(7/9\) and \(4/5\) has the required properties.

## 4. Applying the linear-hypergraph theorem

The Duke--Lefmann--Rödl theorem gives a logarithmic improvement for a
linear uniform hypergraph, where linear means that distinct edges intersect
in at most one vertex. It does not require absence of three- or four-edge
cycles. See the primary paper
[On uncrowded hypergraphs](https://doi.org/10.1002/rsa.3240060208),
Random Structures & Algorithms 6 (1995), 209--212.

One convenient formulation is the uniform case of Theorem 6 in
[Lee and Lefmann, The independence number of non-uniform uncrowded
hypergraphs](https://arxiv.org/pdf/1602.03569). For a linear six-uniform
hypergraph on \(N\) vertices, average degree at most \(T^5\), and
\(T\ge1.5\), it gives

\[
 \alpha\ge c_6\frac NT(\log T)^{1/5}.
 \tag{11}
\]

The theorem's additional prohibition concerns cycles made entirely of
two-element edges. A six-uniform hypergraph has no such edges. Its statement
allows an upper bound on average degree, so no lower bound on the actual
degree is needed.

Apply (11) to \(\mathcal B[U']\), taking \(T=d_0^{1/5}\). By (7) and
(10),

\[
 \begin{aligned}
 \alpha(\mathcal B[U'])
 &\ge c\frac{n^2p}{(n^4p^5\Lambda^2)^{1/5}}
       \bigl(\log(C_0n^{1/20}\Lambda^2)\bigr)^{1/5}\\
 &\ge c' n^{6/5}\Lambda^{-1/5}.
 \end{aligned}
\]

An independent set in this hypergraph also avoids \(\mathcal A\), since
\(U'\) already does. It is therefore a valid blackout. This proves (1).
All uses of probability establish existence. The geometric codegree bounds
and the exponents in the deletion estimates are analytical.

## 5. The local-box inequalities permit the upper-bound scale

The next result is a limitation of a particular proof method. It does not
construct valid blackouts of order \(n^{4/3}\).

For an axis-aligned square \(Q\) of side \(\ell\), let \(T_Q(S)\) count
right-angle triples with all three points in \(S\cap Q\), whether or not
their fourth corner lies in \(Q\). Coordinates and side lengths of squares
are integral.

**Aggregate-budget theorem.** There is an absolute \(c>0\) such that, for
all sufficiently large \(n\), some set \(S\subseteq V\) satisfies

\[
 |S|\ge c\frac{n^{4/3}}{(\log n)^{1/3}},\qquad
 T_Q(S)\le\frac{\ell^2}{4}\quad
 \text{for every square }Q\text{ in the board}.
 \tag{12}
\]

The set can be restricted to one checkerboard class and can contain no fully
black rectangle. It then satisfies every local inequality

\[
 T_Q(S)\le |Q^*\setminus S|+4
 \tag{13}
\]

used in the local-budget upper bound, whenever the threefold expansion
\(Q^*\) lies in the board. It also satisfies the global numerical budget
\(T(S)\le n^2-|S|+4\).

**Proof.** Select only cells with even coordinate sum, each independently
with probability

\[
 q=c_0 n^{-2/3}(\log(n+2))^{-1/3}.
\]

Write \(S_0\) for the sample. Use an overlapping dyadic covering family:
for each power of two \(L\) with \(2\le L<4n\), take all squares of side
\(L\), anchored at multiples of \(L/2\), that meet the board. Squares in
this family may extend outside the board. There are \(O(n^2/L^2)\) at
each scale.

For a covering square \(R\), put \(N_R=|S_0\cap R|\). A primitive-direction
count, identical to (3) but without requiring the fourth corner to stay in
\(R\), bounds the number of possible right-angle triples in \(R\) by
\(CL^4\log(L+2)\). For any fixed triple, its contribution to
\(\mathbb E[N_RT_R]\) is at most \(3q^3+L^2q^4\): its own three
points are already forced, and every other point is sampled independently.
Hence

\[
 \mathbb E[N_RT_R]
 \le C(q^3L^4+q^4L^6)\log(L+2).
 \tag{14}
\]

Call \(R\) bad if \(T_R(S_0)>L^2/64\), and empty every bad covering
square. Initially good covering squares only lose points, and initially bad
ones become empty. Thus the resulting set satisfies \(T_R(S)\le L^2/64\)
for every covering square.

Every square \(Q\) of side \(\ell\le n\) lies inside a covering square
\(R\) with \(2\ell\le L<4\ell\). To find it, choose this dyadic \(L\)
and round each lower coordinate of \(Q\) down to a multiple of \(L/2\).
Consequently \(T_Q(S)\le T_R(S)<\ell^2/4\), as required in (12).

The expected number of removed points is at most

\[
 \begin{aligned}
 \sum_R\mathbb E[N_R\mathbf1_{R\text{ bad}}]
 &\le64\sum_R\frac{\mathbb E[N_RT_R]}{L^2}\\
 &\le Cn^2\bigl(q^3\log^2(n+2)+q^4n^2\log(n+2)\bigr).
 \end{aligned}
 \tag{15}
\]

Summing over the covering squares and their dyadic scales gives (15).
Meanwhile \(\mathbb E|S_0|\ge q(n^2-1)/2\). Dividing the right
side of (15) by \(qn^2\) gives

\[
 O\bigl(q^2\log^2(n+2)+q^3n^2\log(n+2)\bigr)
   =o(1)+O(c_0^3).
\]

Choose \(c_0\) sufficiently small. Then \(\mathbb E|S|\ge c_1qn^2\),
so some outcome has the required size.

We can also delete one point from each fully black rectangle in the initial
sample. Their expected number is at most \(Cn^4\Lambda q^4\), which is
\(O(c_0^3)\) times \(qn^2\). A smaller choice of \(c_0\) absorbs this
additional loss. These deletions preserve all the triple-count inequalities
and ensure that no rectangle is fully black.

Every threefold square \(Q^*\) contains at least
\(\lfloor9\ell^2/2\rfloor\) cells of the unselected checkerboard class.
They remain white. Thus (12) implies (13). The whole-board condition gives
\(T(S)\le T_V(S)\le n^2/4\), while the checkerboard restriction leaves
at least \(\lfloor n^2/2\rfloor\) white cells. This proves the global
budget too. \(\square\)

This theorem retains the actual number of white cells in the relevant box
budgets. It therefore also addresses the proposed refinement that regions
with fewer whites should have smaller budgets. What it does not control is
the number of triples completing to each individual cell. That injectivity,
and the constraints from two-white presentations, remain possible sources
of a stronger upper bound.

## 6. Scope and verification

The proved square interval is now

\[
 \Omega\!\left(n^{6/5}(\log n)^{-1/5}\right)
 \ \le f(n,n)\le
 O\!\left(n^{4/3}(\log n)^{-1/3}\right).
\]

The new lower bound improves the logarithm only. The aggregate-budget theorem
explains why the existing local line-counting argument cannot close the
exponent gap using those budgets alone. It is not an impossibility theorem
for stronger incidence arguments.

[square_codegree_check.py](square_codegree_check.py) independently enumerates
small rectangle families and checks the explicit codegree bounds in (5).
It also checks the rational sampling exponents. These finite checks support
the bookkeeping; neither theorem depends on finite enumeration.
