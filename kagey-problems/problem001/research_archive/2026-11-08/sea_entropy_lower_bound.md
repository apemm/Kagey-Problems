# A polynomial lower bound for the sea entropy

Research note, 8 November 2026. This settles the unboundedness question in section 2.4 of the 7 November REPORT.md for the parity-partition sea shift. It does not assert that this partition is dominant, or establish the conditional product formula for maximum blackouts.

**Theorem.** There are absolute constants \(c>0,h_0\) such that
\[
 \rho_h\ge c h^{1/3}\qquad(h\ge h_0).
\]
More precisely, for any fixed \(0<\epsilon<1/3\), every sufficiently large \(h\) admits a Sidon alphabet \(A\) of odd rows, of size \(k\asymp h^{1/3}\), whose sea subshift has growth rate
\[
 \rho(A)\ge k\exp(-C_\epsilon h^\epsilon/k),
 \qquad 0<\epsilon<1/3. \tag{1}
\]
In particular \(\rho(A)/k\to1\). Constants are independent of the word length.

The proof selects a sparse row alphabet before choosing the sea word. Sidon relations remove the large families of four-point coincidences. A local lemma bounds the entropy cost of the remaining sparse patterns.

## 1. Definitions and arithmetic estimates

Fix height \(h\), with \(F\) the row pairs of opposite parity. A sea word has one black point in each column. Its shift excludes hidden tilted rectangles, tilted presentations with an axis-aligned rival computed through \(F\), and collisions of distinct tilted presentations. This is the hidden-free sea shift in the entropy scripts.

An alphabet \(A\subseteq\{1,\ldots,h\}\) is Sidon if \(a+b=c+d\) implies equality of the unordered pairs, including multiplicities. All alphabets here contain only odd rows.

A pattern is a set of specified black cells modulo common horizontal translation. Normalize its leftmost black column to zero. Discard patterns specifying two different rows in one column. A retained \(r\)-cell pattern therefore specifies \(r\) distinct word positions and has probability \(k^{-r}\) under an independent uniform word on a \(k\)-letter alphabet.

We use
\[
 \tau(N)=O_\eta(N^\eta),\qquad r_2(N)\le4\tau(N), \tag{2}
\]
where \(r_2\) counts ordered signed representations as two squares. The divisor bound is elementary. Write \(N=\prod p^{e_p}\). For \(p\ge2^{1/\eta}\), \(e+1\le2^e\le p^{\eta e}\). For each of the finitely many smaller primes, \(\sup_{e\ge0}(e+1)p^{-\eta e}<\infty\). Multiply these estimates.

The representation bound follows from Gaussian integer factorization: a split prime of exponent \(e\) permits at most \(e+1\) allocations between its conjugate factors, other primes permit at most one, and there are four units. Equivalently, use Jacobi's formula \(r_2(N)=4(d_1(N)-d_3(N))\). A formal proof and statement appear in [Manuel Eberl, The Sum-of-Squares Function and Jacobi's Two-Square Theorem](https://isa-afp.org/entries/Sum_Of_Squares_Count.html).

We decrease the exponent in (2) as needed, absorbing products of divisor bounds and powers of \(\log h\) into \(O_\epsilon(h^\epsilon)\).

## 2. The complete list of surviving patterns

Every tilted rectangle has a strictly lowest row, a strictly highest row, and two intermediate rows. Its opposite row sums agree, giving a nontrivial Sidon relation. Thus it cannot have all four corner rows in \(A\), and in particular cannot be hidden.

A tilted rectangle with one white corner has a white completion in an odd row, since its three black rows are odd. The black row in that column is odd too, so its pair with the completion row is not in \(F\). Hence there is no singleton axis-aligned rival.

For a vertical two-point presentation, the two black corners form the other diagonal. Their row difference is even, and their column difference is even because their midpoint column is integral. An integral diagonal length is therefore even. The two white rows have even difference, so their pair is not in \(F\).

For an oblique two-point presentation, an axis-aligned rival requires the two crossed cells to be black. All four row coordinates of the tilted rectangle would belong to \(A\), contradicting Sidon.

Next consider two tilted rectangles sharing two corners. Regard these as a geometric shared pair without specifying their colors. The collision condition is exactly that their four nonshared corners are black.

* If the shared pair is a side in both rectangles, the opposite black sides have the same nonzero ordered row difference. Sidon implies that nonzero ordered differences are unique. Thus the two opposite sides have the same ordered rows. Their perpendicular translations from the shared side agree, so the rectangles coincide.
* If the shared pair is a diagonal in both, the black row multisets have equal sums and are identical. For fixed midpoint and length, distinct black diagonals with those rows can only be vertical mirror images. When their rows differ, they require two black rows in the same columns, impossible in a sea. When their rows agree, the horizontal diagonal is unique.

The only surviving types are:

1. A tilted rectangle with a horizontal axis-aligned rival: four specified black cells.
2. Two tilted rectangles whose shared pair is a side in one and a diagonal in the other: four specified black cells.
3. Two tilted rectangles sharing exactly one corner: six specified black cells.

Three shared corners determine the rectangle. Disjoint rectangles could collide only if both were hidden. A one-white collision that shares another black corner is already a four-cell symmetric-difference event. It does not create a five-cell case. Any repeated black column makes the pattern impossible and is discarded.

## 3. Four-cell pattern counts

Let \(B_4(A)\) count the retained four-cell patterns.

For a horizontal rival, write \(a\ne b\) for the black diagonal rows and \(c\) for the common black row in the two white columns. If \(x\) is the black diagonal's horizontal component and \(L\) the white diagonal length, then
\[
 L^2-x^2=(a-b)^2.
\]
Factorization gives \(O_\epsilon(h^\epsilon)\) choices per row triple. Therefore
\[
 B_{\rm hor}(A)\le C_\epsilon |A|^3h^\epsilon. \tag{3}
\]

For a mixed side/diagonal collision, write its common side as \(P,Q=P+(x,y)\). Let the opposite black side have rows \(c,d\), and the other rectangle's black diagonal have rows \(a,b\). Then
\[
 y=d-c\ne0,\qquad z=\frac{c+d-a-b}{2}
\]
is the vertical component of the perpendicular translation from the shared side to its opposite black side. Common parity makes \(z\) integral. Also \(z\ne0\): if \(z=0\), perpendicularity with \(y\ne0\) forces the whole translation to vanish. Its horizontal component is \(-yz/x\), so
\[
 x\mid yz,\qquad 0<|yz|\le h^2. \tag{4}
\]
For each \(x\), the black diagonal horizontal component \(r\) satisfies
\[
 r^2=x^2+y^2-(b-a)^2.
\]
Thus each ordered quadruple of black rows gives \(O_\epsilon(h^\epsilon)\) patterns.

A stronger aggregate count handles four distinct rows. Parameterize the common side by
\[
 U=\alpha(u,v),\qquad \gcd(|u|,|v|)=1,\quad uv\ne0,
\]
and the perpendicular connector by \(V=\beta(-v,u)\). Integrality and primitivity make \(\alpha,\beta\) integers. Allow a constant number of signs and take \(u,v,\alpha,|\beta|\ge1\). Vertical containment gives \(\alpha v\le h\), \(|\beta|u\le h\), hence \(u,v\le h\). There are at most \(h/v\) choices for \(\alpha\), \(h/u\) for \(|\beta|\), and \(h\) vertical translations.

The other rectangle's second diagonal has the same squared length as \(U\), at most \(2h^4\). By (2) there are \(O_\epsilon(h^\epsilon)\) such integer vectors. Therefore the total mixed pattern count over all rows is
\[
 O_\epsilon\left(h^{1+\epsilon}
 \sum_{u,v\le h}\frac{h}{u}\frac{h}{v}\right)
 =O_\epsilon(h^{3+\epsilon}). \tag{5}
\]
The last exponent absorbs the logarithms by starting with a smaller exponent in (2).

Sample rows independently with probability \(p\), and put \(k\asymp hp\). Four distinct rows cost \(p^4\), so (5) contributes \(O_\epsilon(k^4h^{-1+\epsilon})\). Quadruples with \(d\le3\) distinct rows have \(O(h^d)\) choices and the fixed-row bound (4), contributing \(O_\epsilon(k^dh^\epsilon)\). Equation (3) obeys the same three-row estimate. Hence
\[
 \mathbb E B_4(A_0)\le
 C_\epsilon h^\epsilon(k^3+k^4/h). \tag{6}
\]

## 4. Six-cell pattern counts

For two rectangles sharing exactly one corner \(X\), orient their remaining corners as right angles with vertex rows \(b,e\) and endpoint rows \(a,c\) and \(d,f\). Their completion rows agree:
\[
 a+c-b=d+f-e. \tag{7}
\]
Relative to the horizontal coordinate of \(X\), let the first endpoints have coordinates \(s,t\). Its vertex then has coordinate \(s+t\), and perpendicularity is
\[
 st=-(a-b)(c-b). \tag{8}
\]
The product is nonzero. If one adjacent row difference vanished, one leg would be horizontal and the other vertical, requiring two black points in one column. Its magnitude is at most \(h^2\). Thus each fixed triple of rows allows divisor-many positions. Applying this to both triples gives \(O_\epsilon(h^\epsilon)\) patterns per ordered row sextuple.

For six distinct rows, (7) leaves \(O(h^5)\) tuples. For \(d\le5\) distinct rows, the trivial \(O(h^d)\) bound suffices. Therefore
\[
 \mathbb E B_6(A_0)\le
 C_\epsilon h^\epsilon(k^5+k^6/h). \tag{9}
\]
The six black points are distinct because the rectangles intersect only at \(X\). Retained patterns have six distinct columns. Repeated row values change the row-sampling probability but do not change the six-variable word-event probability.

## 5. A sparse Sidon alphabet with few patterns

Let \(N=\lceil h/2\rceil\). Choose a sufficiently small absolute \(c_0>0\), set \(k=\lfloor c_0h^{1/3}\rfloor\), and sample each odd row with probability \(p=4k/N\). Then \(\mathbb E|A_0|=4k\) and \(\Pr(|A_0|<2k)=o(1)\), for example by Chebyshev.

A nontrivial Sidon equation has either four distinct rows, with \(O(h^3)\) choices, or three distinct rows, with \(O(h^2)\) choices. There is no nontrivial two-row case. Its expected count \(Z\) is
\[
 \mathbb E Z\le C(k^4/h+k^3/h). \tag{10}
\]
Choose \(c_0\) so small that this is at most \(k/16\) for large \(h\). Markov gives \(\Pr(Z>k)\le1/16\).

Markov with factor eight in (6) and (9), combined with the preceding events, gives positive probability that simultaneously
\[
 |A_0|\ge2k,\quad Z\le k,\quad
 B_4(A_0)\le C_\epsilon k^3h^\epsilon,\quad
 B_6(A_0)\le C_\epsilon k^5h^\epsilon.
\]
Delete one row from each surviving Sidon equation, using at most \(Z\) deletions, and trim to exactly \(k\) rows. Deletions cannot create patterns. The resulting Sidon alphabet satisfies
\[
 B_4(A)\le C_\epsilon k^3h^\epsilon,\qquad
 B_6(A)\le C_\epsilon k^5h^\epsilon. \tag{11}
\]

## 6. Local lemma and entropy

Choose a uniform independent word in \(A^m\). Each translate of a retained pattern whose specified black columns lie in the word defines a bad event. We can include an event even when an unspecified rectangle corner lies beyond the word: this only strengthens the avoidance condition.

A fixed column belongs to at most \(4B_4(A)\) four-variable events and \(6B_6(A)\) six-variable events. This bound counts specified columns and is independent of the patterns' spans.

For an \(r\)-variable event set \(x_E=2k^{-r}\). Events on disjoint column sets are independent. The sum of all neighboring event weights is at most
\[
 6\left(8B_4(A)k^{-4}+12B_6(A)k^{-6}\right)
 =O_\epsilon(h^\epsilon/k). \tag{12}
\]
Fix \(0<\epsilon<1/3\). For large \(h\), (12) is at most \(1/2\). The elementary inequality \(\prod_j(1-x_j)\ge1-\sum_jx_j\) therefore bounds the neighbor product below by \(1/2\), so
\[
 \Pr(E)=k^{-r}\le x_E\prod_{F\sim E}(1-x_F).
\]
The local lemma, including its product lower bound, gives
\[
 \Pr(\text{no bad events})\ge\prod_E(1-x_E).
\]
For an explicit statement, see [Moser and Tardos, A constructive proof of the general Lovász Local Lemma, Theorem 1.1](https://arxiv.org/html/0903.0544v3).

There are at most \(mB_r(A)\) events of arity \(r\). Since \(\log(1-x)\ge-2x\) for \(x\le1/2\),
\[
 \Pr(\text{no bad events})
 \ge \exp\left[-4m\left(B_4(A)k^{-4}+B_6(A)k^{-6}\right)\right]
 \ge \exp(-C_\epsilon m h^\epsilon/k).
\]
All these words satisfy the sea constraints by section 2. Consequently their number is at least
\[
 k^m\exp(-C_\epsilon m h^\epsilon/k). \tag{13}
\]

For fixed \(h\), the forbidden patterns have finite span. The exponential rate of finite admissible words equals the spectral radius of this finite-type shift. Nonextendable transient paths do not change that rate. Taking \(m\)-th roots in (13) proves (1), and hence \(\rho_h\ge ch^{1/3}\).

## 7. Scope

This proves unbounded parity sea entropy with a polynomial lower bound. It replaces the need for a boundary-band entropy argument. It does not determine the sharp order of \(\rho_h\), construct the double order, prove insertion into a dominant component, or establish parity dominance among balanced partitions. The proof is an existence argument; no SAT computation or unproved independence assumption enters it.
