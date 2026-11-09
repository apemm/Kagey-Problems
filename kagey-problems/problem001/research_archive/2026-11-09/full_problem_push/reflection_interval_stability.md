# Linear stability for reflection closure on an interval

9 November 2026. The argument below gives an absolute, nonnumerical linear stability constant for every balanced row block at height at least eight. It uses arithmetic removal and the asymmetric integer \(3k-4\) theorem. The elementary near-parity estimate is explicit. The complete argument and both primary theorem inputs passed [independent review](reflection_interval_independent_audit.md).

Let \(A\subseteq[1,h]\) have size \(\lfloor h/2\rfloor\) or \(\lceil h/2\rceil\). Write
\[
 V(A)=\#\{(a,b)\in A^2:2a-b\in[1,h]\setminus A\},
 \qquad
 r(A)=\min_{P\text{ a physical parity class}}|A\triangle P|.
\tag{1}
\]
Equivalently, \(V(A)\) counts unordered same-parity endpoint pairs with different membership in A whose midpoint belongs to A.

**Theorem.** There is an absolute constant \(C\) such that, for every \(h\ge8\) and every balanced A,
\[
 r(A)\le C\,\frac{V(A)}h.
\tag{2}
\]
In particular, if
\[
 n_A(k)=\#\{a\in A:a-k,a+k\in[1,h],\
                      1_A(a-k)\ne1_A(a+k)\}
\]
satisfies \(n_A(k)\le2M\) for every positive k, then
\[
 r(A)\le CM.
\tag{3}
\]
This proves the approximate reflection-closure statement without a separate bound on adjacent pairs or parity-domain walls.

For even height \(h=2n\), put \(e=|A\cap2\mathbb Z|\) and \(o=n-e\). Since \(r(A)=2\min(e,o)\), (2) also implies
\[
 V(A)\ge c\,eo
\tag{4}
\]
for an absolute \(c>0\). The constants here are not asserted to be sharp or numerically useful.

## 1. The two external inputs

We use the arithmetic removal lemma in the following standard form: if subsets X,Y,Z of cyclic groups of order \(O(n)\) have \(o(n^2)\) solutions to \(x+y=z\), one can delete \(o(n)\) elements from each set to remove all solutions. This is the three-variable case of Theorems 1 and 2 in [Kráľ, Serra and Vena, *A combinatorial proof of the Removal Lemma for Groups*](https://arxiv.org/html/0804.4847).

We also use the asymmetric integer \(3k-4\) theorem: if finite nonempty integer sets X,Y satisfy
\[
 |X+Y|=|X|+|Y|-1+\rho,\qquad
 \rho\le\min(|X|,|Y|)-3,
\]
then X,Y lie in arithmetic progressions of the same positive step, each with at most \(\rho\) holes. This is the Lev–Smeliansky–Stanchescu theorem, stated explicitly as Theorem 13 of [Bollobás, Leader and Tiba, *Large sumsets from small subsets*](https://api.repository.cam.ac.uk/server/api/core/bitstreams/c0df9132-de28-4a03-b7d3-50bb078d3bf7/content). The original two-summand theorem is [Lev and Smeliansky, *On addition of two distinct sets of integers*](https://doi.org/10.4064/AA-70-1-85-91).

No induced-removal theorem or assumption about periodic boundary conditions is used.

## 2. Few violations imply qualitative closeness to parity

We prove the uniform implication
\[
 V(A)=o(h^2)\quad\Longrightarrow\quad r(A)=o(h)
\tag{5}
\]
for any sequence of balanced sets with heights tending to infinity.

Suppose otherwise. Pass to a subsequence on which \(r(A)\ge\varepsilon h\), for some fixed \(\varepsilon>0\), and put \(n=\lfloor h/2\rfloor\). Define the even-row index sets
\[
 E=\{i\in[1,n]:2i\in A\},\qquad F=[1,n]\setminus E.
\]
Balance and the lower bound on r imply
\[
 |E|,|F|\ge\delta n
\tag{6}
\]
for some fixed \(\delta>0\), after discarding finitely many terms.

Every solution
\[
 x\in E,\quad y\in F,\quad x+y\in A
\]
is a violation counted by V: its endpoints are \(2x\in A\) and \(2y\notin A\), and its midpoint is \(x+y\in A\). Thus there are \(o(n^2)\) such solutions.

Embed the three sets \(E,F,A\) in the cyclic group of order \(4h+1\). Since \(x+y\in[2,2n]\) and \(A\subseteq[1,h]\), modular solutions are exactly integer solutions. Arithmetic removal gives
\[
 E'\subseteq E,\quad F'\subseteq F,\quad A'\subseteq A
\]
with \(o(n)\) deletions from each, and
\[
 S:=E'+F'\subseteq [2,2n]\setminus A'
             \subseteq A^c\cup(A\setminus A').
\]
Here and below \(A^c\) means the complement inside \([1,h]\). Consequently,
\[
 n-o(n)\le |S|\le n+o(n).
\tag{7}
\]
The lower bound is the elementary integer sumset inequality. Also
\[
 |E'|+|F'|=n-o(n),\qquad
 \rho:=|S|-|E'|-|F'|+1=o(n).
\]
Together with (6), this meets the asymmetric \(3k-4\) hypothesis for all sufficiently large n.

We obtain progressions \(P_E\supseteq E'\), \(P_F\supseteq F'\) of common step d, with only \(o(n)\) holes. Trim their endpoints to the extreme members of E' and F'. They then lie inside \([1,n]\). Moreover,
\[
 |P_E\triangle E|=o(n),\qquad
 |P_F\triangle F|=o(n).
\tag{8}
\]
Their union therefore contains all but \(o(n)\) points of \([1,n]\), and their intersection has size \(o(n)\).

If \(d\ge3\), two residue classes modulo d contain at most \(2n/3+2\) points of \([1,n]\), contradicting this coverage. Hence \(d=1\) or \(d=2\).

### Step two is impossible in the mixed regime

If \(d=2\), the progressions must occupy opposite parity classes; one class alone has only \(n/2+O(1)\) points. Their sumset S lies in one physical parity class of \([1,h]\). By (7), S contains all but \(o(n)\) points of that class, and \(S\setminus A^c\) has size \(o(n)\). Since \(|A^c|=n+O(1)\), it follows that \(A^c\), and hence A, differs from a physical parity class in \(o(n)\) points. This contradicts \(r(A)\ge\varepsilon h\).

### Step one is also impossible in the mixed regime

If \(d=1\), (8) says that E and F are within \(o(n)\) points of two intervals whose overlap and uncovered part both have size \(o(n)\). Pass to a subsequence on which \(|E|/n\to\theta\), with \(\delta\le\theta\le1-\delta\). Up to exchanging left and right, the two interval limits are
\[
 E\approx[1,\theta n],\qquad F\approx[\theta n,n].
\tag{9}
\]
The symbol \(\approx\) in this paragraph denotes symmetric difference \(o(n)\), with integer rounding absorbed in the error. To justify (9), order the two interval hulls by their left endpoints. Coverage forces the first left endpoint to be \(o(n)\) from 1 and the second right endpoint to be \(o(n)\) from n; their overlap or gap is \(o(n)\). Their cardinalities then locate the common cut at \(\theta n+o(n)\).

The interval \(P_E+P_F\) consequently has endpoints \(\theta n+o(n)\) and \((1+\theta)n+o(n)\). It contains S, and both sets have size \(n+o(n)\). Therefore
\[
 S\approx J:=[\theta n,(1+\theta)n].
\]
Since S is contained in \(A^c\) except for \(o(n)\) points and \(|A^c|=n+O(1)\), we have
\[
 A^c\approx J.
\tag{10}
\]
Any interval of length \(n+o(n)\) has \(n/2+o(n)\) even rows. Thus (10) forces \(|E|=n/2+o(n)\), so \(\theta=1/2\). But its even-row index complement has the shape
\[
 E\approx[1,n/4]\ \cup\ [3n/4,n].
\tag{11}
\]
This differs in \(n/2+o(n)\) points from either endpoint half-interval in (9), a contradiction. The argument with E near the right endpoint is identical.

Both possible steps are excluded. This proves (5).

## 3. An explicit estimate near parity

Choose the better parity class P, and let Q be the other one. Put
\[
 t=|P\setminus A|,\qquad m=|A\cap Q|,\qquad r=t+m,
 \qquad N_P=|P|,\quad N_Q=|Q|.
\]
Balance gives \(|t-m|\le1\).

For each missing row \(u\in P\setminus A\), consider endpoints \(v\in P\) for which the midpoint \((u+v)/2\) is also in P. There are at least \(\lfloor N_P/2\rfloor\) such v. At most t are missing endpoints and at most t have a missing midpoint. Hence these pairs contribute at least
\[
 t\bigl(\lfloor N_P/2\rfloor-2t\bigr)
\]
violations.

For each inserted row \(u\in A\cap Q\), consider endpoints \(v\in Q\) whose midpoint lies in P. There are at least \(\lfloor N_Q/2\rfloor\) choices. At most m fail \(v\notin A\), and at most t have a missing midpoint. They contribute at least
\[
 m\bigl(\lfloor N_Q/2\rfloor-m-t\bigr).
\]
The two families have different endpoint parities and are disjoint. Every midpoint lies between its endpoints, so there is no boundary loss.

Writing \(n=\lfloor h/2\rfloor\), we obtain
\[
 \begin{aligned}
 V(A)
 &\ge t\bigl(\lfloor N_P/2\rfloor-2t\bigr)
       +m\bigl(\lfloor N_Q/2\rfloor-m-t\bigr)\\
 &\ge r\bigl(\lfloor n/2\rfloor-r-1\bigr).
 \end{aligned}
\tag{12}
\]
For the second inequality, use
\(2t^2+m^2+mt=r^2+t(t-m)\le r^2+r\).

In particular, if \(h\ge64\) and \(r\le h/16\), then
\[
 V(A)\ge rh/8.
\tag{13}
\]
At even height the more precise estimate
\[
 V(A)\ge2m\bigl(\lfloor n/2\rfloor-2m\bigr)
\]
is recorded separately in [Reflection stability: partial bounds](reflection_stability_partial.md).

## 4. Combine the two regimes

By (5), there are absolute constants \(\eta>0\) and \(h_0\ge64\) such that, whenever \(h\ge h_0\) and \(r(A)>h/16\),
\[
 V(A)\ge\eta h^2.
\]
Since \(r(A)\le h\), this gives \(r(A)\le\eta^{-1}V(A)/h\). In the complementary regime, (13) gives the same conclusion with constant 8.

Only finitely many heights \(8\le h<h_0\) remain. If \(V(A)=0\), A is closed under all in-interval reflections about its own members. The minimum-positive-gap argument shows that such a nonempty set is a full residue class modulo some d, or a singleton: a pair attaining the minimum gap generates the entire residue class by successive reflections, and any extra point would have a smaller gap from that progression. Balance and
\[
 \lfloor h/2\rfloor>\lceil h/3\rceil\qquad(h\ge8)
\]
force \(d=2\). Thus \(V(A)=0\) implies \(r(A)=0\). The finitely many remaining positive ratios \(r(A)h/V(A)\) have a finite maximum. Enlarging C to include them proves (2).

Finally,
\[
 V(A)=\sum_{k=1}^{\lfloor(h-1)/2\rfloor}n_A(k)\le Mh,
\]
which proves (3).

The removal lemma supplies existence of an absolute constant, not a practical numerical value. The cyclic Fourier estimate and its periodic transfer remain useful explicit alternatives, but no wraparound estimate is required for this interval theorem.

## 5. Almost balanced sets

For an arbitrary \(A\subseteq[1,h]\), let
\[
 d=\min\bigl\{\bigl||A|-\lfloor h/2\rfloor\bigr|,
                 \bigl||A|-\lceil h/2\rceil\bigr|\bigr\}.
\]
Choose a balanced set \(A_0\) by toggling d rows. A fixed row can occur as the center, the in-set endpoint, or the reflected endpoint of at most \(3h\) relevant ordered triples. Hence
\[
 V(A_0)\le V(A)+3hd.
\]
The triangle inequality for symmetric difference and (2) give
\[
 \min_P|A\triangle P|
 \le C\,V(A)/h+(3C+1)d.
\tag{14}
\]
Thus a size deficit contributes additively to the stability estimate.

