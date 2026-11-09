# A uniform periodic test for a constant column phase

9 November 2026. This note strengthens the periodic amplification estimate when the column phase is constant. Its loss depends only on the prime divisors of the row period, rather than on a power of that period. This is a quantitative ingredient for the arbitrary-row aggregate inverse problem; by itself it does not prove that inverse theorem.

Write
\[
 \lambda_N=\prod_{p\mid N}\frac{p-1}{p+1}.
\]
For a set \(A\) of residues modulo an even integer \(N\), let
\[
 \alpha=\frac{|A|}{N},\qquad
 p_A=\frac1N\sum_{r\bmod N}(2\,1_A(r)-1)(-1)^r .
\]
The distance from \(A\) to the nearer ordinary parity class is
\((1-|p_A|)N/2\).

**Periodic amplification lemma.** Fix \(\varepsilon>0\). There are absolute constants \(c,C>0\) such that, if
\[
 |\alpha-1/2|\le c\varepsilon,\qquad
 \frac{1-|p_A|}{2}\ge\varepsilon,
\tag{1}
\]
then the periodic row set \(A_h=\{r\in[1,h]:r\bmod N\in A\}\), with a constant selected column phase, has at least
\[
 c\varepsilon\lambda_N h^4\log h
\tag{2}
\]
tilted rectangles with exactly three selected corners and four distinct columns, for all sufficiently large \(h\), with \(N\) fixed.

All rectangles counted in (2) may be restricted to comparable primitive side directions
\[
 a,b\in[R,2R),\qquad
 h^{1/32}\le R\le h^{1/16},
\]
and positive side scales at most \(\eta h/R\), where one fixed absolute \(0<\eta<1/100\) is used throughout.

## 1. A Fourier energy bound on the cyclic row set

Let \(g=2\,1_A-1\), and normalize Fourier coefficients by
\[
 \widehat g(\xi)=\frac1N\sum_{r\bmod N}g(r)e^{-2\pi i\xi r/N}.
\]
Put \(\mu=\widehat g(0)=2\alpha-1\). Parseval gives
\[
 \sum_\xi|\widehat g(\xi)|^2=1.
\]
The coefficient at \(N/2\) is \(p_A\). Every other nonzero frequency occurs in a distinct conjugate pair. Consequently
\[
 \sum_{\xi\ne0}|\widehat g(\xi)|^4
 \le p_A^4+\frac12(1-\mu^2-p_A^2)^2
 \le p_A^4+\frac12(1-p_A^2)^2.
\tag{3}
\]
For the first inequality, group the remaining coefficients into conjugate pairs. A pair with total squared mass \(w\) contributes \(w^2/2\), and the sum is maximized by putting all remaining mass into one pair.

Let
\[
 E(A)=\#\{a+b=c+d:a,b,c,d\in A\}.
\]
The normalized energy is
\[
 \frac{E(A)}{N^3}
 =\alpha^4+\frac1{16}\sum_{\xi\ne0}|\widehat g(\xi)|^4.
\]
Thus the number of triples \(a,b,c\in A\) with \(a+c-b\notin A\) satisfies
\[
 \begin{aligned}
 \frac{|A|^3-E(A)}{N^3}
 &\ge \alpha^3(1-\alpha)
 -\frac1{16}\left[p_A^4+\frac12(1-p_A^2)^2\right]\\
 &\ge \frac{1-p_A^2}{32}-C|\alpha-1/2|.
 \end{aligned}
\tag{4}
\]
At \(\alpha=1/2\), the last calculation uses
\[
 1-p_A^4-\frac12(1-p_A^2)^2
 =(1-p_A^2)\left(\frac12+\frac32p_A^2\right).
\]
Condition (1), with its constant chosen sufficiently small, therefore gives a proportion at least \(c\varepsilon\) of additive parallelograms with the first three specified corners in \(A\) and the fourth outside \(A\). Allowing any of the four corners to be missing can only increase the count.

An odd period can be replaced by twice that period. Thus the even-period convention loses nothing.

## 2. Primitive directions that preserve uniform residue sampling

For fixed \(N\), Möbius inversion gives
\[
 \#\{a,b\in[R,2R): (a,b)=1,\ (ab,N)=1\}
 =\left(\frac{\lambda_N}{\zeta(2)}+o_N(1)\right)R^2.
\tag{5}
\]
Indeed the density is
\[
 \left(\frac{\varphi(N)}N\right)^2
 \prod_{p\nmid N}(1-p^{-2})
 =\frac1{\zeta(2)}
 \prod_{p\mid N}\frac{(1-p^{-1})^2}{1-p^{-2}}
 =\frac{\lambda_N}{\zeta(2)}.
\]
One may first truncate the Möbius sum and then let the truncation grow; the usual \(O(R\log R)\) lattice error is \(o(R^2)\) for each fixed \(N\).

Fix one such primitive direction and put \(K=\lfloor\eta h/R\rfloor\). Rectangles have sides
\[
 U=k(a,b),\qquad V=l(-b,a),\qquad 1\le k,l\le K.
\]
Choose their lowest vertex \((x,y)\) with
\[
 2\eta h+2\le x\le h-2\eta h-2,\qquad
 1\le y\le h-4\eta h-2.
\]
The four corners then lie in the board. Because \(a,b\) are units modulo \(N\), the residues of \(kb\) and \(la\), as \(k,l\) vary, become independently uniform modulo \(N\). The residue of \(y\) is also uniform up to \(O(N/h)\).

Equation (4) therefore supplies at least \(c\varepsilon K^2h^2\) three-selected-corner rectangles for each direction, once \(h\) is large enough for the fixed \(N\). The lowest vertex, primitive direction, and two scales uniquely specify the rectangle. Equation (5) gives \(c\varepsilon\lambda_N h^4\) rectangles per dyadic range, and there are \(\Theta(\log h)\) disjoint ranges.

The only repeated-column case is \(ka=lb\). Primitivity makes \(k=bt,l=at\), so a direction supplies \(O(h/R^2)\) such scale pairs. Including translations and summing directions and dyadic ranges gives only \(O(h^3\log h)\) repeated-column rectangles. This proves (2).

## 3. The period loss is only a squared iterated logarithm

Uniformly for \(N\ge2\),
\[
 \lambda_N\ge \frac{c}{(\log\log(3N))^2}.
\tag{6}
\]
Here is an elementary proof. The estimate
\[
 \prod_{p\le X}(1-p^{-1})^{-1}\le C\log X
\tag{7}
\]
follows by taking \(\sigma=1+1/\log X\), comparing the Euler product at \(1\) with that at \(\sigma\), and using
\[
 \sum_{p\le X}\frac{\log p}{p-1}=O(\log X),\qquad
 \zeta(\sigma)\le1+\frac1{\sigma-1}.
\]
The first estimate follows by partial summation from Chebyshev's elementary bound \(\sum_{p\le X}\log p=O(X)\). That bound follows in turn from the central-binomial-coefficient estimate on each dyadic prime interval.

Take \(X=(\log(3N))^2\). The prime divisors of \(N\) exceeding \(X\) have reciprocal sum at most
\[
 \frac{\log N}{X\log X}=O(1).
\]
Their factors \(1-p^{-1}\) therefore have product bounded below by an absolute positive constant. The factors at primes at most \(X\) have product at least \(c/\log X\) by (7). Finally
\[
 \lambda_N
 =\prod_{p\mid N}\frac{(1-p^{-1})^2}{1-p^{-2}}
 \ge\prod_{p\mid N}(1-p^{-1})^2,
\]
which gives (6).

## 4. Stability under row edits and the bounded-period reduction

In the comparable-direction family used above, changing one row of the selected set changes at most
\[
 C h^3\log h
\tag{8}
\]
rectangle tests. For one direction, a specified row can occupy any of four corners, the two scales have at most \(K^2\) choices, and there are at most \(h\) horizontal translates. There are \(O(R^2)\) directions in a dyadic range, so its contribution is \(O(h^3)\); summing the ranges proves (8).

Consequently changing at most \(\delta h\) rows changes this test count by at most \(C\delta h^4\log h\).

This removes a useful quantitative obstruction to a bounded-period repair argument. Suppose that, for every fixed sufficiently small \(\delta>0\), a sequence of balanced row sets with vanishing normalized three-corner count can be approximated within \(C_0\delta^a h+o_\delta(h)\) row edits by a periodic set of period
\[
 N\le 2M!,\qquad M\le C_1\delta^{-b},
\tag{9}
\]
where \(a,b,C_0,C_1>0\) are fixed. Then those row sets must be \(o(h)\)-close to ordinary parity.

To see this, otherwise their distance from both parity classes exceeds \(\varepsilon h\) on a subsequence. Choose \(\delta\) so small that the approximants remain nearly balanced and at least \(\varepsilon/2\)-far from parity. Equations (2), (6), and (9) give a lower test density at least
\[
 \frac{c\varepsilon}{(\log(1/\delta))^2}.
\]
Equation (8) subtracts only \(C C_0\delta^a\). The former dominates the latter for a sufficiently small fixed \(\delta\), contradicting the assumed vanishing count. Periods and patterns may vary with \(h\), since there are only finitely many of them under (9) for that fixed \(\delta\).

The stated bounded-period repair, with \(a=1/2\) and \(b=1\), is proved in [Component-permutation repair](component_permutation_repair.md). Its overlap argument is an additional ingredient; a general induced-\(P_4\) removal theorem alone does not supply it. Together the two notes establish the constant-column-phase aggregate inverse theorem.
