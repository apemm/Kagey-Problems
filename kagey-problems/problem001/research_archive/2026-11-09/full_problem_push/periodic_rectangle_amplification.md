# Amplifying a periodic rectangle obstruction across many directions

9 November 2026. This proves the aggregate rectangle inverse test for bounded-period full row-class boxes, and gives a uniform quantitative version for moderately growing periods. It does not settle the inverse test for arbitrary row and column words. The proof has passed two independent reviews.

Let c,t be binary functions on \(\mathbb Z\), both periodic with an even period P, and suppose c takes each value at exactly \(P/2\) residues. On the \(h\times h\) board put
\[
 W=\{(x,y):c(y)=t(x)\}.
\]
Write \(N_3^{(4)}(W)\) for the number of tilted lattice rectangles in four distinct columns with exactly three corners in W.

Call the pair protected if there are bits \(\kappa,\alpha,\beta,\gamma,\delta\) with
\[
 c(y)=\kappa q(y)+\alpha y+\beta,\qquad
 t(x)=\kappa q(x)+\gamma x+\delta
 \quad\text{on }\mathbb Z,
\tag{1}
\]
where \(q(z)=\binom z2\bmod2\) and \(\alpha=1\) when \(\kappa=0\).

**Theorem.** There are absolute constants \(c_*>0,h_*>0\) such that, whenever
\[
 h\ge h_*,\qquad P\le h^{1/16},
\]
every nonprotected pair satisfies
\[
 N_3^{(4)}(W)\ge c_*\,\frac{h^4\log h}{P^6}.
\tag{2}
\]
Every protected pair has \(N_3(W)=0\), even without the distinct-column restriction.

Consequently, for any fixed period bound, the condition
\[
 N_3(W)=o(h^4\log h)
\]
forces the row and column laws to be protected for all sufficiently large h. For a growing period, the same conclusion follows under the stronger error condition
\[
 N_3(W)=o(h^4\log h/P^6).
\]

## 1. A nonprotected periodic pair has a finite obstruction

Suppose there were no tilted rectangle anywhere in \(\mathbb Z^2\) with exactly three corners in W. Then the corresponding full row-class Cartesian box would avoid every singleton-axis rival.

It would also avoid every vertical-pair rival. Indeed if a tilted rectangle had a black diagonal in W and its other diagonal were a vertical pair of opposite row colors, exactly one of those two vertical corners would belong to W, according to the phase of their common column. The rectangle would then have exactly three W-corners, a contradiction.

Apply the [exact full-row-class theorem](full_row_class_phase_classification.md) in arbitrarily large finite boards whose heights are multiples of P. These row partitions are balanced. That theorem forces (1); the parameters agree on overlapping intervals, since three row values and three consecutive phase values determine the relevant quadratic laws. Thus a nonprotected pair has a finite three-corner obstruction.

Choose its lowest vertex as \((x_0,y_0)\). Its side vectors have the unique form
\[
 k_0(a_0,b_0),\qquad l_0(-b_0,a_0),
\tag{3}
\]
where \(a_0,b_0,k_0,l_0\) are positive integers and \(\gcd(a_0,b_0)=1\). The original rectangle may have a repeated column. That does not affect its residue pattern, and the amplification below removes the repeated-column family at the end.

## 2. Primitive directions in a prescribed residue class

Fix residues \(a_0,b_0\pmod P\) with \(\gcd(a_0,b_0,P)=1\). Uniformly in these residues, the number of pairs
\[
 R\le a,b<2R,\qquad
 a\equiv a_0\pmod P,\quad b\equiv b_0\pmod P,\quad
 \gcd(a,b)=1
\]
is
\[
 \frac{R^2}{P^2}
 \prod_{p\nmid P}(1-p^{-2})
 +O\!\left(\frac{R\log(2R)}P+R+\frac R{P^2}\right).
\tag{4}
\]

For completeness, insert
\[
 1_{\{\gcd(a,b)=1\}}=\sum_{d\mid a,\ d\mid b}\mu(d).
\]
A divisor sharing a prime with P contributes nothing, because the two prescribed residues are not both zero at that prime. For \(\gcd(d,P)=1\), the Chinese remainder theorem gives \(R/(Pd)+O(1)\) choices for each coordinate. Summing the resulting error gives the first two terms in (4); extending the main sum beyond \(2R\) costs \(O(R/P^2)\). The Euler product is at least \(1/\zeta(2)\).

In particular there are at least \(cR^2/P^2\) such directions whenever
\[
 R\ge C_0P^2(\log h)^2,\qquad R\le h^{1/4},
\tag{5}
\]
for sufficiently large absolute \(C_0,h\). The logarithmic factor is deliberately generous.

## 3. Every admissible direction reproduces the same coloring pattern

For each primitive direction counted in (4), choose positive scales k,l satisfying
\[
 \frac{h}{100R}\le k,l\le\frac{2h}{100R},\qquad
 k\equiv k_0\pmod P,\quad l\equiv l_0\pmod P.
\tag{6}
\]
Because \(R\le h^{1/4}\) and \(P\le h^{1/16}\), each interval in (6) contains at least \(ch/(PR)\) admissible integers for all sufficiently large h.

Choose a lowest vertex \((x,y)\) with
\[
 h/3\le x,y\le2h/3,\qquad
 x\equiv x_0\pmod P,\quad y\equiv y_0\pmod P.
\tag{7}
\]
There are at least \(ch^2/P^2\) choices.

The resulting sides
\[
 k(a,b),\qquad l(-b,a)
\]
are perpendicular. Their horizontal and vertical extents are at most \(8R\cdot h/(100R)<h/10\), so the four corners remain inside the board for every choice in (7). All four corner coordinates agree modulo P with those of the original witness (3). Periodicity therefore gives exactly the same three-selected-corner pattern.

For a fixed primitive direction, (6)--(7) produce at least
\[
 c\,\frac{h^4}{P^4R^2}
\tag{8}
\]
rectangles. The representation by lowest vertex, positive-slope primitive direction, and two positive side scales is unique. Thus there is no multiplicity loss when we sum directions or disjoint dyadic ranges.

Multiplying (8) by the \(cR^2/P^2\) directions from (4), every dyadic range satisfying (5) contributes
\[
 c\,h^4/P^6.
\tag{9}
\]

## 4. Sum the logarithmically many scales

When \(P\le h^{1/16}\), the ratio between the upper and lower limits in (5) is at least
\[
 \frac{h^{1/8}}{C_0(\log h)^2}.
\]
Hence there are at least \(c\log h\) disjoint dyadic ranges satisfying (5), once h exceeds an absolute threshold. Summing (9) gives
\[
 N_3(W)\ge c\,h^4\log h/P^6.
\tag{10}
\]

The number of tilted rectangles with a repeated column is \(O(h^3\log h)\). To recall the count, for primitive direction \((a,b)\) a repeated column forces the side scales to be \(k=bt,l=at\), and its vertical span is \(t(a^2+b^2)\). There are at most \(h/(a^2+b^2)\) scales and \(h^2\) basepoints. Summing the primitive directions gives the stated bound.

Since \(P^6\le h^{3/8}\), this exceptional family is \(o(h^4\log h/P^6)\), uniformly in the allowed periods. Removing it proves (2).

Finally, for a protected pair the XOR of the four values \(c(y)+t(x)\) on any rectangle is \(\kappa\,u\cdot v=0\pmod2\), where u,v are its perpendicular side vectors. The number of selected corners is therefore even, so there is no three-corner obstruction.

## 5. What this does and does not resolve

The theorem shows that a fixed periodic obstruction cannot hide in finitely many low-weight directions: congruence-preserving primitive directions reproduce it at a positive fraction of logarithmically many scales.

The factor \(P^{-6}\) is a safe counting bound, not an optimized constant. It is not uniform enough to settle the [aggregate inverse test](container_stability_reduction.md) for arbitrary colorings. In particular, the period of a row or column word may grow comparably with h, and the preceding residue-count argument then gives no useful lower bound.

