# Mixed four-cell pressure has exactly four logarithms

9 November 2026. The mixed side/diagonal family cannot be discarded as a lower-order term in the protected-phase entropy comparison. This note determines its order up to constant factors, not its asymptotic constant or the ordering of the phases. Both bounds and their entropy consequences passed [independent review](protected_phase_pressure_independent_audit.md).

Let \(\mu_{4,\mathrm{mix},X}(h)\) be the mean per column of distinct mixed four-cell positive supports in protected phase \(X\in\{\mathrm O,\mathrm C,\mathrm Q\}\), under independent uniform choices from the allowed row class. Then there are absolute \(c,C>0\) such that, for all sufficiently large \(h\),
\[
 c\frac{(\log h)^4}{h}
 \le\mu_{4,\mathrm{mix},X}(h)
 \le C\frac{(\log h)^4}{h}
 \qquad(X=\mathrm O,\mathrm C,\mathrm Q).
\tag{1}
\]
In particular, an \(o(\log^4 h/h)\) upper bound for this family is false.

## 1. A family for which the strip imposes no circle restriction

Take dyadic numbers \(A,B\) satisfying
\[
 h^{1/10}\le A,\qquad 2A\le B,\qquad 2B\le h^{1/5}.
\tag{2}
\]
Choose odd coprime integers
\[
 A\le a<2A,\qquad B\le b<2B.
\]
Put \(K=h/(400B)\), \(J=h/(400A)\), and choose
\[
 K\le k<2K,\quad 8\mid k,
 \qquad
 J\le l<2J,\quad 4\mid l.
\tag{3}
\]
Define
\[
 U=k(a,b),\qquad T=l(-b,a),\qquad N=a^2+b^2.
\]
For every integer vector \(V\) with \(|V|^2=k^2N\), positive horizontal component, and \(V\ne U\), use the common pair \(0,U\) and required black cells
\[
 T,\quad T+U,\quad C=(U+V)/2,\quad D=(U-V)/2.
\tag{4}
\]
The first rectangle has common side \(0,U\), and the second has common diagonal \(0,U\). They are nondegenerate because \(T\ne0\) and \(V\ne\pm U\).

Since \(a,b\) are odd, \(\nu_2(N)=1\). The identity
\(V_x^2+V_y^2=k^2N\) therefore forces
\(\nu_2(V_x)=\nu_2(V_y)=\nu_2(k)\ge3\). Consequently every coordinate of the four points in (4) is divisible by four.

The inequalities in (2)--(3) give
\[
 0<U_x,U_y<h/100,\qquad 0<T_y<h/100,
 \qquad |V_y|\le |U|<h/50.
\]
All six points \(0,U,T,T+U,C,D\) thus have vertical span less than \(h/10\). There are at least \(c_1h\) vertical translations that put them in the strip and make every required black cell belong to any one of O, C, or Q, averaged over the horizontal phase. This uses only that all their relative coordinates are multiples of four: the base point has the required phase for half its residue classes.

For fixed \(U,T\), only \(O(1)\) circle representations must be discarded because two of the four black columns coincide. The pair \(T,T+U\) already has different columns; so does \(C,D\) when \(V_x>0\). Any crossed column equality fixes \(V_x\), and the norm equation then leaves at most two values of \(V_y\). Degenerate representations and a zero horizontal component cost another \(O(1)\). Hence the number of retained vectors is
\[
 \tfrac12r_2(k^2N)-O(1).
\tag{5}
\]

## 2. The arithmetic lower bound

Let \(\mathcal P\) be the primes congruent to one modulo four. For odd coprime \(a,b\), every odd prime dividing \(N=a^2+b^2\) is in \(\mathcal P\). The sum-of-two-squares formula gives
\[
 \frac14r_2(k^2N)
 =\prod_{p\in\mathcal P}(\nu_p(N)+2\nu_p(k)+1).
\]
Prime by prime, the right side is at least
\[
 \sum_{\substack{D\mid N,\ E\mid k\\
 D,E\text{ squarefree, supported on }\mathcal P\\(D,E)=1}}
 2^{\omega(E)}.
\tag{6}
\]
Indeed the local terms retained are \(1\), a term \(1\) when \(p\mid N\), or a term \(2\) when \(p\mid k\); choosing both at the same prime is forbidden. Their sum is at most \(\nu_p(N)+2\nu_p(k)+1\).

Fix \(\eta=1/1000\) and \(Y=h^\eta\). We retain only the terms \(DE\le Y\) in (6).

### A uniform primitive congruence count

For squarefree \(D\) supported on \(\mathcal P\), put
\[
 G(D)=\prod_{p\mid D}\frac p{p+1}.
\]
Uniformly for \(D\le Y\) and the boxes in (2),
\[
 \#\{(a,b):a,b\text{ odd},\ (a,b)=1,\ D\mid a^2+b^2\}
 =\frac{AB}{3\zeta(2)}\frac{2^{\omega(D)}G(D)}D
 +O\!\left(2^{\omega(D)}[(A+B)\log h+DA]\right).
\tag{7}
\]
The count is over the two indicated dyadic intervals.

To verify (7), a primitive solution modulo D has both coordinates coprime to D. There are \(2^{\omega(D)}\varphi(D)\) such odd residue pairs modulo \(2D\): choose the unit second coordinate and one of the roots of \(-1\) modulo D. Apply Möbius inversion to the common divisor, restricted to integers coprime to \(2D\). For a divisor r, counting these residue pairs in the rescaled box has error
\[
 O\!\left(2^{\omega(D)}[(A+B)/r+D]\right).
\]
Sum for \(r\le2A\). The main Euler product is
\[
 \frac{2^{\omega(D)}\varphi(D)}{4D^2}
 \prod_{p\nmid2D}(1-p^{-2})
 =\frac1{3\zeta(2)}\frac{2^{\omega(D)}G(D)}D.
\]
The tail of the Möbius sum is absorbed by the error in (7).

The error is uniformly smaller than half the main term for large h. For example \(G(D)\ge D^{-1/2}\), and the relative error is
\[
 O\!\left(D^{3/2}\log h/A+D^{5/2}/B\right)=o(1).
\]
Thus (7) gives a uniform lower bound by a constant times its main term.

Since E is odd and \(K/E\to\infty\) uniformly for \(E\le Y\), the number of k in (3) divisible by E is at least \(c_2K/E\). Summing (6), then using (7), gives
\[
 \sum_{a,b,k}r_2(k^2(a^2+b^2))
 \ge c_3ABK
 \sum_{\substack{DE\le Y\\D,E\text{ squarefree on }\mathcal P\\(D,E)=1}}
 \frac{2^{\omega(D)+\omega(E)}G(D)}{DE}.
\tag{8}
\]

### Two arithmetic logarithms

For \(F=DE\), assigning each prime factor to D or E rewrites the last sum as
\[
 S(Y)=\sum_{\substack{F\le Y\\F\text{ squarefree on }\mathcal P}}
 \frac1F\prod_{p\mid F}\left(4-\frac2{p+1}\right).
\tag{9}
\]
We need only the lower bound \(S(Y)\gg(\log Y)^2\).

Here is a short truncation proof. Put \(z=Y^{1/100}\) and
\[
 w_p=\frac{4-2/(p+1)}p,
 \qquad Z(z)=\prod_{\substack{p\le z\\p\in\mathcal P}}(1+w_p).
\]
Mertens' theorem in the progression \(1\bmod4\) implies
\[
 Z(z)\asymp(\log z)^2\asymp(\log Y)^2.
\]
The needed progression product is a special case of Theorem 1 in [Kenneth S. Williams, *Mertens' Theorem for Arithmetic Progressions*](https://people.math.carleton.ca/~williams/papers/pdf/057.pdf).

Normalize the expansion of Z as a probability distribution on squarefree products of these primes, selecting p independently with probability \(w_p/(1+w_p)\). Then the elementary Mertens bound \(\sum_{p\le z}\log p/p=O(\log z)\), or its usual Chebyshev proof, gives
\[
 \mathbb E\log F
 \le4\sum_{p\le z}\frac{\log p}p
 =(4+o(1))\log z<\tfrac12\log Y
\]
for large Y. Markov's inequality leaves at least half the mass on \(F\le Y\). That part of the product expansion is included in (9), proving
\[
 S(Y)\gg(\log Y)^2\gg(\log h)^2.
\tag{10}
\]

## 3. Sum the dyadic boxes and remove multiplicity

There are \(\gg(\log h)^2\) pairs of dyadic scales satisfying (2). They correspond to disjoint pairs \((a,b)\). For one such pair of scales, (8)--(10), the \(\gg J\) choices of l, and the \(\gg h\) translations give
\[
 \gg h\,ABKJ(\log h)^2
 \gg h^3(\log h)^2
\]
phase-compatible mixed supports before the \(O(1)\)-per-circle exclusions in (5). These exclusions contribute only \(O(h^3)\) per box. Summing the boxes gives
\[
 \gg h^3(\log h)^4
\tag{11}
\]
supports in each protected phase, per horizontal translation.

There is no hidden multiplicity in this count. In (4), the required black side AB and diagonal CD have equal lengths. The other two pairings have squared-length differences \(\pm2T\cdot V\). If either vanished, then \(T\perp V\) and \(T\perp U\) would force \(V=\pm U\), a discarded degeneracy. Swapping the side and diagonal roles also requires \(T\cdot V=0\). Thus the equal-length pairing and its roles are unique. Orienting both U and V with positive horizontal component then determines the common pair, k, the primitive direction \((a,b)\), and l uniquely.

Nor can such a support be a hidden rectangle: the three possible parallelogram midpoint identities force \(T=0\) or \(V=\pm U\). Protected phases have no forbidden supports of fewer than four cells. Consequently (11) counts distinct minimal mixed four-cell events.

Each event has probability \((2/h)^4(1+O(1/h))\), proving the lower bound in (1).

## 4. A matching elementary upper bound

Write \(\rho(d)\) for the number of roots of \(-1\) modulo d, with \(\rho(1)=1\). Its prime-power factors show pointwise that
\[
 \rho(d)\le r_2(d)/4.
\]
Counting lattice points in a disk therefore gives
\[
 \sum_{d\le X}\rho(d)=O(X),\qquad
 \sum_{d\le X}\frac{\rho(d)}d=O(\log(2X)).
\tag{12}
\]
The first estimate needs only the enclosing square bound for the disk; the second follows by partial summation.

Put \(R(k)=r_2(k^2)/4\). Its Euler factors give the exact identity
\[
 R(k)=\sum_{\substack{d\mid k\\d\text{ odd}}}\rho(d).
\]
For primes \(1\bmod4\), both sides have factor \(2\nu_p(k)+1\); primes \(3\bmod4\) and the prime two contribute one. Thus
\[
 \sum_{k\le K}R(k)=O(K\log(2K)).
\tag{13}
\]
Also, for every primitive \(N=a^2+b^2\),
\[
 r_2(k^2N)\le r_2(N)R(k).
\tag{14}
\]
This follows prime by prime from \(n+2e+1\le(n+1)(2e+1)\).

We next need a uniform rectangular-box bound:
\[
 \sum_{\substack{A\le a<2A,\ B\le b<2B\\(a,b)=1}}
 r_2(a^2+b^2)
 =O\bigl(AB\log(2\max(A,B))\bigr).
\tag{15}
\]
Assume \(A\le B\). Divisor pairing gives
\[
 r_2(a^2+b^2)
 \le8\sum_{\substack{d\le\sqrt{a^2+b^2}\\d\mid a^2+b^2}}1.
\]
Primitivity implies \((a,d)=1\), so \(b\equiv\nu a\pmod d\) for one of the \(\rho(d)\) roots of \(-1\). Since \(d<3B\), the number of such pairs for fixed d is at most
\(O(A\rho(d)(B/d+1))\). Equation (12) proves (15). Interchanging a and b covers the other order of box sizes.

Summing (15) over dyadic boxes gives
\[
 \sum_{\substack{a,b\le h\\(a,b)=1}}
 \frac{r_2(a^2+b^2)}{ab}
 =O((\log(2h))^3).
\tag{16}
\]
Indeed each box contributes \(O(\log(2\max(A,B)))\), and there are \(O((\log(2h))^2)\) boxes.

For a mixed support with oblique common side, orient its side vector as
\(U=k(a,b)\), where \(a>0\), \(b\ne0\), and \((a,b)=1\). The connector is \(T=l(-b,a)\), with \(l\ne0\). In-strip geometry forces
\[
 a,|b|\le h,\qquad k|b|\le h,
 \qquad |l|a\le h.
\]
There are at most \(2h/a\) connectors, h vertical translations, and \(r_2(k^2(a^2+b^2))\) alternate diagonal vectors. Ignoring all additional restrictions only enlarges the count. Equations (13)--(16) give the bound
\[
 \begin{aligned}
 N_{\mathrm{mix,oblique}}(h)
 &\le C h^2
   \sum_{\substack{a,b\le h\\(a,b)=1}}
    \frac1a\sum_{k\le h/b}r_2(k^2(a^2+b^2))\\
 &\le C h^3
   \sum_{\substack{a,b\le h\\(a,b)=1}}
    \frac{r_2(a^2+b^2)}{ab}\log(2h/b)\\
 &=O(h^3(\log(2h))^4).
 \end{aligned}
\tag{17}
\]
The constant absorbs the sign of b and the orientations. No asymptotic equidistribution of circle directions is used.

For a horizontal common side, write \(U=(u,0)\), \(V=(v,w)\) with \(u,v>0\), and \(T=(0,t)\), \(t\ne0\). Here \(w\ne0\) and
\[
 (u-v)(u+v)=w^2,\qquad |w|,|t|<h.
\]
For fixed w there are at most \(\tau(w^2)\) choices of \((u,v)\). Since
\(\tau(w^2)\le d_3(w)\) prime by prime and
\(\sum_{w\le h}d_3(w)\le h(1+\log h)^2\), the connectors and translations give
\[
 N_{\mathrm{mix,horizontal}}(h)
 =O(h^3(\log(2h))^2).
\tag{18}
\]
A vertical black side requests two black cells in one column and cannot occur in a sea.

Every phase-compatible event has probability \(O(h^{-4})\). Equations (17)--(18) prove the upper bound in (1).

## 5. Consequence for the entropy comparison

The total protected-phase mean satisfies
\[
 \mu_X(h)=\Theta(\log^4h/h),
 \qquad X\in\{\mathrm O,\mathrm C,\mathrm Q\},
\]
because the six-cell mean has that order and hidden rectangles contribute only \(O(\log^2h/h)\). Combining this with the independently reviewed expansion in [crossed_codegree_and_avoidance.md](crossed_codegree_and_avoidance.md) gives
\[
 \log r_X(h)=\bar\ell_X(h)-\Theta(\log^4h/h).
\tag{19}
\]
Here \(\bar\ell_X\) is the period-average logarithm of the available row-class size. In particular,
\[
 r_X(h)=h/2-\Theta((\log h)^4).
\tag{20}
\]
The bounded difference between the row-class sizes and h/2 is absorbed by the growing logarithmic deficit.

The exact entropy-capture theorems for the boundary components therefore improve their lower bounds to
\[
 \lambda_*(h)\ge h/2-O((\log h)^4),\qquad
 \lambda_{\partial,\mathrm Q}(h)\ge h/2-O((\log h)^4).
\tag{21}
\]
These statements hold for all sufficiently large heights. The first uses capture of the ordinary all-odd phase, and the second uses [quadratic_parity_entropy_capture.md](quadratic_parity_entropy_capture.md). They are lower bounds for the full components, not logarithmic-deficit upper bounds for them.

The smaller six-cell coefficient for Q still does not settle protected-phase ordering. Its mixed term has exactly the same logarithmic order and needs its own comparison. None of these statements compares a protected phase with the full ordinary or quadratic boundary component.
