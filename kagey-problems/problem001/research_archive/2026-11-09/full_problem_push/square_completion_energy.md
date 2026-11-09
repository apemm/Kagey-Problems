# Completion energy and a limitation of the paraboloid route

9 November 2026. This note records an exact reduction for the remaining square upper-bound problem and a concrete obstruction to replacing it by a standard additive-energy problem. It does not improve the proved exponent \(4/3\).

## 1. The pointwise quantity that an improved bound must control

For a black set \(S\) and a grid point \(X\), let \(r_S(X)\) be the number of nondegenerate rectangles whose other three corners are black and whose fourth corner is \(X\). For a hidden-free valid set,
\[
r_S(X)=0\quad(X\in S),\qquad r_S(X)\le1\quad(X\notin S).
\]
Write
\[
T(S)=\sum_X r_S(X),\qquad
E_{\rm comp}(S)=\sum_X r_S(X)^2.
\]
Then
\[
E_{\rm comp}(S)-T(S)
=2\sum_X\binom{r_S(X)}2.                       \tag{1}
\]
The right side counts pairs of three-black rectangles competing for the same completion. If hidden rectangles and four-cell mixed supports have already been excluded, every such pair has six distinct nonshared black corners. Thus (1) is exactly the remaining six-support collision count, with its natural multiplicities.

Together with the absence of hidden rectangles and mixed four-cell supports, the pointwise condition \(r_S\le1\) is sufficient for validity. Indeed, two rectangles sharing one white corner would violate that condition; two sharing two corners either give a mixed support or have a fully black rectangular symmetric difference; disjoint rectangles could collide only if both were hidden.

Cauchy–Schwarz gives only
\[
E_{\rm comp}(S)\ge\frac{T(S)^2}{|V|}.
\]
Combined with \(E_{\rm comp}=T\), this recovers the completion budget \(T\le|V|\). Applying this argument locally recovers the existing local-budget method. A stronger square exponent therefore requires an additional lower bound for the off-diagonal quantity in (1), not merely this first-moment budget.

## 2. The exact paraboloid formulation

Define
\[
\Phi(x,y)=(x,y,x^2+y^2).
\]
A nondegenerate three-black completion satisfies
\[
\Phi(A)+\Phi(B)=\Phi(C)+\Phi(X),                \tag{2}
\]
where \(C\) is opposite \(X\). Conversely, (2), with distinct relevant points, implies
\[
X=A+B-C,
\qquad (A-C)\cdot(B-C)=0,
\]
so it is exactly a rectangle completion.

Hidden-freeness is equivalent to \(\Phi(S)\) being a Sidon set: two different unordered pairs with the same lifted sum are the two equal-length diagonals of a rectangle. A repeated point in one pair cannot give a nontrivial equality, by strict convexity of the squared norm.

However, the six-support condition is much weaker than the assertion that \(\Phi(S)\) is a \(B_3\) set. The following example makes the distinction exact.

## 3. A globally valid six-point set whose lift is not \(B_3\)

Let
\[
\begin{aligned}
A&=(1,0),& B&=(2,5),& C&=(-3,-5),\\
D&=(0,1),& E&=(-5,2),& F&=(5,-3).
\end{aligned}
\tag{3}
\]
The first three points and the last three points each have vector sum zero and total squared norm 64. Hence
\[
\Phi(A)+\Phi(B)+\Phi(C)
=\Phi(D)+\Phi(E)+\Phi(F)=(0,0,64).              \tag{4}
\]
This is a nontrivial equality between disjoint triples.

Nevertheless, blackening precisely these six cells identifies every rectangle in the entire integer lattice. In particular, translating them by \((5,5)\) gives a valid set on the \(11\times11\) grid with coordinates \(0,\ldots,10\).

To prove the global claim, first note that the squared-distance matrix is
\[
\begin{pmatrix}
0&26&41&2&40&25\\
26&0&125&20&58&73\\
41&125&0&45&53&68\\
2&20&45&0&26&41\\
40&58&53&26&0&125\\
25&73&68&41&125&0
\end{pmatrix}.
\]
Among its positive distance values, the only sums of two values that equal a third are
\[
20+20=40,\qquad20+25=45,\qquad20+53=73.
\]
There is only one edge of squared length 20, namely \(BD\). The edges of squared lengths 25 and 53 are \(AF\) and \(CE\), both disjoint from \(BD\). None of these numerical equalities is therefore a right triangle on the six points. No rectangle has three black corners, so there are no hidden rectangles and no singleton-presentation collisions.

It remains to exclude collisions with two common corners. If those corners are sides in both rectangles or diagonals in both, the four nonshared black corners would form a rectangle, already impossible. In the mixed case, the black side pair and black diagonal pair must have equal length. The only disjoint equal-length pairs are
\[
(AB,DE),\qquad(AC,DF),\qquad(BC,EF).
\]
For each pair, put \(U\) and \(V\) for the two segment vectors and let \(H\) be the difference between the sums of their endpoints. A mixed collision requires \(H\cdot U=0\) or \(H\cdot V=0\), depending on which pair is the side. The respective dot-product pairs are
\[
(-18,38),\qquad(-43,23),\qquad(5,15).
\]
None vanishes. No mixed collision exists. Rectangles with at least three white corners cannot collide because three corners determine a rectangle. This proves the claim.

The example rules out the implication
\[
\text{valid blackout}\quad\Longrightarrow\quad
\text{the paraboloid lift is }B_3.
\]
It does not rule out a more refined additive or incidence argument that retains the special completion condition (2).

## 4. What remains open in this route

The current square bounds remain
\[
\Omega\!\left(\frac{n^{6/5}}{(\log n)^{1/5}}\right)
\le f(n,n)
\le
O\!\left(\frac{n^{4/3}}{(\log n)^{1/3}}\right).
\]
The aggregate-budget construction in [square_progress.md](../odd_graph_entropy_square/square_progress.md) shows why numerical completion budgets alone do not close this gap. A possible next target is a lower bound for \(E_{\rm comp}-T\) on rectangle-free sets, using the special equality (2) rather than unrestricted equal sums of three lifted points.
