# A power saving for the low/high mixed pair role

9 November 2026. The surviving low/high mixed role has a uniform square-compatibility saving. Its incidence at a fixed endpoint in the black side is \(O_\varepsilon(h^{3/4+\varepsilon})\) without congruence restrictions, and \(O_\varepsilon(h^{1/2+\varepsilon})\) in the intended modulo-seven block. Removing a sublinear set of possible diagonal endpoint rows makes the incidence uniformly sublinear in both roles. Consequently this pair family can be handled below the quadratic placement scale, after transferring a subquadratic number of labels to the existing exceptional-label construction.

This result treats one mixed-pair family. It does not settle complete occupation, the other pair families, or higher-arity placement.

Both the unrestricted bound and the stronger oriented-profile bound have passed independent review in [mixed_power_savings_independent_audit.md](mixed_power_savings_independent_audit.md).

## 1. Geometric normalization

Translate the low sea row to zero and put the high sea row at \(d>0\). Both label points are strictly between these rows. Let the fixed label point in the black side be
\[
 C=(0,d-s),\qquad 0<s<d.
\]
Its side partner is a high-sea point. A horizontal reflection lets the side vector be
\[
 U=k(p,q),\qquad k,p,q>0,\quad(p,q)=1,\quad kq=s.
\tag{1}
\]
Thus \(k\mid s\), and the high point is \((kp,d)\).

The other black pair is a diagonal joining a low-sea point to a label point at row \(a\), with \(0<a<d\). Its midpoint is at height \(a/2\). The common white side is an integral perpendicular translate of the first side. Its connector therefore has the form
\[
 T=(mq,-mp),\qquad m>0,
\]
because its vertical displacement is \((a+s-2d)/2<0\). It follows that
\[
 a=2d-s-2mp,\qquad mp<d.
\tag{2}
\]

If \(v\) is the signed horizontal component of the black diagonal, equal lengths require
\[
 \begin{aligned}
 v^2
 &=k^2p^2+s^2-a^2\\
 &=(k^2-4m^2)p^2+4m(2d-s)p-4d(d-s).
 \end{aligned}
\tag{3}
\]
For fixed \(k,p,m,v\), all four required black points and the common pair are determined, up to a bounded choice of orientations. Counting solutions of (3) therefore bounds the desired incidence. Ignoring midpoint parity, coloring, repeated columns, and strip containment only enlarges this count.

## 2. A uniform quadratic-norm lemma

Fix an absolute \(C>0\). Suppose \(A,N\) are integers, \(A\ne0\), \(N\ne0\), and
\[
 |A|,|N|,|X|,|Y|\le H^C.
\]
Then
\[
 \#\{(X,Y):X^2-AY^2=N\}=O_{C,\varepsilon}(H^\varepsilon)
\tag{4}
\]
for every \(\varepsilon>0\), uniformly in \(A,N\).

If \(A\) is a positive square, factor the left side. Its nonzero factor pairs give the bound through \(\tau(|N|)\).

Otherwise use the quadratic field \(K=\mathbb Q(\sqrt A)\), removing the square factor of \(A\) when identifying the field. Every \(\alpha=X+Y\sqrt A\) is an algebraic integer in the maximal order, even when it lies in a smaller suborder. Its principal ideal has norm \(|N|\). Unique ideal factorization gives at most \(\tau(|N|)\) ideals of that norm: a split rational prime with exponent \(e\) has \(e+1\) allocations, while inert and ramified primes have at most one. These standard ideal and norm facts are proved in Keith Conrad's [Factoring in quadratic fields](https://kconrad.math.uconn.edu/blurbs/gradnumthy/quadraticgrad.pdf) and [Ideal factorization](https://kconrad.math.uconn.edu/blurbs/gradnumthy/idealfactor.pdf).

Generators of one principal ideal differ by units. In a real quadratic field, both embeddings of \(\alpha\) have polynomial size. Their nonzero integral product also bounds each embedding below by a reciprocal polynomial. Distinct positive absolute values within one unit orbit are uniformly separated multiplicatively: a real quadratic unit \(u>1\) has norm \(\pm1\) and integral trace, so
\[
 u\ge\frac{1+\sqrt5}{2}.
\]
There are therefore only \(O_C(\log H)\) possible associates in the coordinate box. In an imaginary quadratic field, the unit group has bounded size. Thus the number of solutions is at most \(O_C(\tau(|N|)\log(2H))\). The uniform divisor bound proves (4).

The nonzero condition on \(N\) is essential. It will hold with a strictly positive expression in the application.

## 3. Split the two small side parameters

Equation (2) implies that either \(p\le\sqrt d\) or \(m\le\sqrt d\).

If \(p\le\sqrt d\), fix \(p\) and a divisor \(k\mid s\). The black diagonal is an integral representation of
\[
 v^2+a^2=k^2p^2+s^2.
\]
There are at most \(r_2(k^2p^2+s^2)=d^{o(1)}\) such pairs. Each one determines \(m\) through (2). Since \(\tau(s)=d^{o(1)}\), this range contributes
\[
 O_\varepsilon(d^{1/2+\varepsilon}).
\tag{5}
\]

In the other range, fix \(m\le\sqrt d\) and \(k\mid s\). Put
\[
 A=k^2-4m^2,\quad B=4m(2d-s),\quad C=-4d(d-s).
\]
When \(A\ne0\), completing the square in (3) gives
\[
 (2Ap+B)^2-A(2v)^2
 =B^2-4AC
 =16\bigl[m^2s^2+k^2d(d-s)\bigr]>0.
\tag{6}
\]
Every coefficient and variable has polynomial size in \(d\). The norm in (6) is strictly positive because \(0<s<d\). The uniform lemma gives \(d^{o(1)}\) solutions for each \(m,k\). This range also contributes \(O_\varepsilon(d^{1/2+\varepsilon})\).

## 4. The zero quadratic coefficient

The exceptional case \(A=0\) means \(k=2m\). In the small-\(m\) range,
\[
 k\le2\sqrt d,
\]
and (3) becomes
\[
 v^2=Bp+C,\qquad B=2k(2d-s)\asymp kd.
\tag{7}
\]
Also \(kp=2mp<2d\), so the circle equation bounds \(|v|\le3d\).

For every modulus \(B\) and integer \(C\), the number of roots of
\(v^2\equiv C\pmod B\) is at most
\[
 2^{\omega(B)+1}\sqrt B.
\tag{8}
\]
This follows prime by prime. If \(C\) vanishes modulo a prime power, its roots have the required half valuation. Otherwise the valuation of \(C\) must be even, leaving at most two unit roots for odd primes and at most four at the prime two.

An interval of length \(O(d)\) contains only \(O(d/B+1)=O(1)\) copies of each residue class, because \(B\gg kd\). Thus (7) has at most
\[
 d^{o(1)}\sqrt B\ll d^{3/4+o(1)}
\]
solutions for each exceptional divisor \(k\). Summing over \(k\mid s\) preserves the exponent. Combining the three ranges proves the uniform fixed-side bound
\[
 \boxed{I_{\mathrm{side}}(s;d)
       =O_\varepsilon(d^{3/4+\varepsilon}).}
\tag{9}
\]
The argument includes both signs of the horizontal side after multiplying by an absolute constant.

### The exceptional case vanishes in the intended profile

For the oriented modulo-seven block, let \(g=H-L\not\equiv0\pmod7\). The odd diagonal endpoint has normalized residue zero, and the even side endpoint has normalized residue five. Thus
\[
 d\equiv g,\qquad a\equiv0,\qquad s\equiv3g\pmod7.
\]
If \(A=0\), then \(k=2m\), and (2) gives
\[
 kp=2mp=2d-s-a\equiv-g\pmod7.
\]
The original norm equation would imply
\[
 v^2\equiv(kp)^2+s^2-a^2
       \equiv g^2+9g^2=3g^2\pmod7.
\]
This is impossible because three is a nonsquare. Therefore only the two \(d^{1/2+\varepsilon}\) ranges remain in this block:
\[
 \boxed{I_{\mathrm{side},\,0/5}(s;d)
       =O_\varepsilon(d^{1/2+\varepsilon}).}
\tag{10}
\]
This exclusion does not use any extra restriction on the label-column phases.

## 5. Remove a sublinear set of high-incidence diagonal rows

Summing (9) over the possible side-label rows gives at most
\[
 O_\varepsilon(d^{7/4+\varepsilon})
\tag{11}
\]
normalized geometries. Each has one diagonal-label row. Let \(\mathcal B_d\) be the set of rows whose incidence in that role exceeds \(d^{7/8}\). Then
\[
 |\mathcal B_d|=O_\varepsilon(d^{7/8+\varepsilon}).
\tag{12}
\]
Outside this set, diagonal incidence is at most \(d^{7/8}\), while (9) gives a smaller power for the side role. Thus the remaining endpoint rows have uniformly
\[
 O_\varepsilon(h^{7/8+\varepsilon})
\tag{13}
\]
incident geometries when \(d\le h\). A fixed finite family of profiles has a union of exceptional rows of the same order.

Each geometry involving one fixed label leaves at most \(h\) choices for the unused endpoint of its partner label. Therefore the remaining low/high pair events have incident label count
\[
 O_\varepsilon(h^{15/8+\varepsilon})=o(h^2)
\tag{14}
\]
after fixing \(\varepsilon<1/8\). The labels meeting the exceptional rows also number at most \(O_\varepsilon(h^{15/8+\varepsilon})\). They can be transferred to the already proved exceptional-label positional construction: its internal width is \(n h^{o(1)}=o(h^2)\) after fixing a sufficiently small \(\varepsilon\), and its fixed number of collars costs \(O(h^2)\).

This is a reduction for this pair family only. It does not assert that all other placement constraints satisfy a quadratic local-lemma budget.

For the intended modulo-seven block, use the stronger bound (10). The total incidence is \(O_\varepsilon(h^{3/2+\varepsilon})\). Declaring diagonal rows of degree greater than \(h^{3/4}\) exceptional removes only
\(O_\varepsilon(h^{3/4+\varepsilon})\) rows. Outside them, both endpoint roles have incidence \(O_\varepsilon(h^{3/4+\varepsilon})\). The exceptional-label count and the remaining incident label-pair count are therefore both
\[
 \boxed{O_\varepsilon(h^{7/4+\varepsilon})=o(h^2).}
\tag{15}
\]
The same exceptional-label transfer applies, with a larger power margin than in the unrestricted estimate.

## 6. Finite checks and exact scope

[probe_low_high_mixed_squares.py](probe_low_high_mixed_squares.py) enumerates the normalized role at selected finite heights by the independent circle test in (3). [low_high_mixed_square_probe.json](low_high_mixed_square_probe.json) records the exact finite counts through height 1024, including the subset satisfying the modulo-seven and two-phase restrictions. These data motivated the square-compatibility bound; they are not used in its proof or claimed to establish an asymptotic.

The proof permits any \(0<L<H\) after translation, with both selected label rows strictly between them. It therefore applies to the inset boundary profiles as well as to actual boundary rows. It makes no extra assumption about congruence classes. Any refined modular restrictions only reduce the incidence bound.
