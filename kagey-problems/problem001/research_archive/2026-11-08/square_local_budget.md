# A local completion budget removes the iterated logarithm

Research note, 8 November 2026. This note proves a refinement of section 5.1 of the 7 November REPORT.md. It does not change the earlier reports or manuscripts.

**Theorem.** There is an absolute constant \(C\) such that
\[
 f(n,n)\le C\frac{n^{4/3}}{(\log(n+2))^{1/3}}.
\]
The same proof gives, for \(2\le h\le m\),
\[
 f(h,m)\le C\frac{m h^{1/3}}{(\log(h+2))^{1/3}}.
\]

The square bound removes the factor \((\log\log n)^{2/3}\) in the report's Whitney refinement. The argument uses only injectivity of singleton presentations and the fact that at most one rectangle can have empty presentation. It makes no assumption about the column structure of a maximum blackout.

## 1. The completion budget is local

Use grid coordinates \(\{0,\ldots,n-1\}^2\). A black right angle is a triple \((A,B,C)\), with the endpoints \(A,C\) unordered, such that \(A,B,C\in S\), both endpoints differ from \(B\), and
\[
 (A-B)\mathbin\cdot(C-B)=0.
\]
Its completion is \(X=A+C-B\). When \(X\) is in the grid, the four points form a nondegenerate rectangle. Different triples with the same completion give different rectangles: a rectangle and its missing corner determine the opposite vertex and the unordered pair of adjacent vertices.

If \(X\notin S\), injectivity of presentations permits at most one such triple at \(X\). If \(X\in S\), the rectangle is entirely black. There is at most one entirely black rectangle, contributing exactly four right-angle triples. Consequently, for any region \(U\) in the grid,
\[
 \#\{\text{black right angles whose completion lies in }U\}
 \le |U\setminus S|+4\le |U|+4. \tag{1}
\]

Now let
\[
 Q=[a,a+\ell)\times[b,b+\ell),\qquad
 Q^*=[a-\ell,a+2\ell)\times[b-\ell,b+2\ell),
\]
where all endpoints and \(\ell\ge1\) are integers. Suppose \(Q^*\subseteq[0,n)^2\). Every completion of three lattice points in \(Q\) lies in \(Q^*\): each coordinate is between the lower endpoint minus \(\ell-1\) and the lower endpoint plus \(2\ell-2\). If \(T_Q\) counts right angles with all three black points in \(Q\), (1) therefore gives
\[
 T_Q\le9\ell^2+4. \tag{2}
\]
This replaces the global \(n^2\) budget by a budget at the scale of the box.

## 2. A local density estimate

Put \(N=|S\cap Q|\). Fix a primitive direction \(w=(a,b)\), where \(a\ge1\), \(b\ge0\), and let \(s=a+b\). The lines parallel to \(w\) that meet the lattice points of \(Q\) number at most \(s\ell\), because their integer invariants \(bx-ay\) lie in an interval of length \(s(\ell-1)\). The same bound holds for the perpendicular lines.

Let \(t=N/(4s\ell)\). At most \(N/4\) points lie on lines of the first family containing at most \(t\) black points, and the same statement holds for the second family. Thus at least \(N/2\) points lie on two lines, each containing more than \(t\) black points. If \(t\ge2\), each such point is the vertex of at least \((t-1)^2\ge t^2/4\) right angles with endpoints in \(S\cap Q\). Therefore this direction pair contributes at least
\[
 \frac{N^3}{128s^2\ell^2}. \tag{3}
\]

There are \(\varphi(s)\) primitive pairs with \(a+b=s\) for \(s\ge2\), and one axis direction pair for \(s=1\). These direction pairs are distinct, and every right angle counted in (3) has a unique direction pair. With \(H(L)=\sum_{s\le L}\varphi(s)/s^2\), summing (3) gives
\[
 T_Q\ge \frac{N^3}{128\ell^2}
 H\left(\left\lfloor\frac{N}{8\ell}\right\rfloor\right). \tag{4}
\]

For completeness, \(H(L)\ge c\log L\) for all sufficiently large \(L\) has an elementary proof that does not need an asymptotic for the totient function. Among the \(M^2\) positive pairs \(a,b\le M\), the number with a common divisor greater than one is at most
\[
 \sum_{d=2}^{M}\lfloor M/d\rfloor^2
 \le M^2\sum_{d=2}^{\infty}d^{-2}
 \le \frac{25}{36}M^2.
\]
Here \(\sum_{d=2}^{\infty}d^{-2}\le1/4+1/9+\int_3^\infty x^{-2}\,dx=25/36\). At least \(11M^2/36\) pairs are primitive. Removing the inner square \(a,b\le M/2\) leaves at least \(M^2/18\) primitive pairs with
\[
 M/2<a+b\le2M.
\]
Their contribution to \(H(2M)-H(M/2)\) is at least \(1/72\). Taking \(M=4^j\) gives disjoint intervals of sums and proves the logarithmic lower bound.

Combining (2) and (4) yields, when \(N/\ell\) is sufficiently large,
\[
 N^3\log(N/\ell)\le C_0\ell^4. \tag{5}
\]
For large \(\ell\), split into two cases. If \(N\le\ell^{7/6}\), then \(N\le C_1\ell^{4/3}/(\log(\ell+2))^{1/3}\). Otherwise \(\log(N/\ell)\ge(\log\ell)/6\), and the same bound follows from (5). Enlarging the absolute constant handles bounded \(\ell\). Thus every admissible square satisfies
\[
 |S\cap Q|\le C_2\frac{\ell^{4/3}}{(\log(\ell+2))^{1/3}}. \tag{6}
\]

## 3. An explicit dyadic covering

Consider dyadic squares
\[
 [a,a+\ell)\times[b,b+\ell),\qquad
 \ell=2^j,\quad j\ge0,\quad a,b\in\ell\mathbb Z.
\]
Call one admissible when its expansion \(Q^*\) is contained in \([0,n)^2\). Select all maximal admissible squares. Dyadic squares are either disjoint or nested, so the selected squares are disjoint. Every grid point off the outermost rows and columns lies in an admissible unit square, hence in a maximal one. The uncovered grid points therefore number at most \(4n\).

If a maximal square has side \(\ell\), its dyadic parent of side \(2\ell\) is not admissible. The parent's expansion must cross a side of the grid. Since the square is one of its four children, the entire square lies within distance \(4\ell\) of that side. Consequently all maximal squares of side \(\ell\) lie in the boundary strip of width \(4\ell\). Disjointness bounds their number by
\[
 \frac{16n\ell}{\ell^2}=\frac{16n}{\ell}. \tag{7}
\]
The estimate remains valid when the strip fills the whole grid. No selected square has side greater than \(n/3\), because its threefold expansion must fit.

Equations (6) and (7) imply
\[
 |S|\le4n+C_3 n\sum_{\substack{\ell=2^j\\\ell\le n/3}}
 \frac{\ell^{1/3}}{(\log(\ell+2))^{1/3}}. \tag{8}
\]
For \(\ell<\sqrt n\), the sum is \(O(n^{1/6})\) by a geometric series. For \(\ell\ge\sqrt n\), replace the denominator by \(c(\log n)^{1/3}\) and sum another geometric series. The second contribution is \(O(n^{1/3}/(\log n)^{1/3})\), and it dominates the first. This proves
\[
 |S|=O\left(\frac{n^{4/3}}{(\log n)^{1/3}}\right).
\]

For an \(h\times m\) grid, use the same construction inside \([0,m)\times[0,h)\). The uncovered boundary has \(O(h+m)\) points, at most \(C(h+m)/\ell=O(m/\ell)\) selected squares have side \(\ell\), and \(\ell\le h/3\). Replacing \(n\) in the sum's upper limit by \(h\), and the prefactor by \(m\), proves the rectangular statement.

## 4. Scope

The theorem matches the logarithmic scale suggested by the report's local line-counting method. It does not improve the exponent \(4/3\), construct a larger blackout, settle the proposed exponent \(6/5\), or determine the optimal constant. No numerical or SAT assumption enters the proof. The decisive extra observation is (2): each box has its own completion budget.
