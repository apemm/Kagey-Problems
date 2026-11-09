# A subquadratic count for the phase-flipped boundary family

9 November 2026. This note closes the arithmetic counting problem isolated in [checkerboard_bridge_counting.md](checkerboard_bridge_counting.md). The argument counts a larger family than the geometrically admissible supports, so the strip and ordering filters can only improve the bound.

**Theorem.** For every fixed \(\varepsilon>0\), the number \(B_{\rm flip}(h)\) of normalized phase-flipped, cross-pair mixed supports satisfies
\[
B_{\rm flip}(h)=O_\varepsilon(h^{3/2+\varepsilon}).                 \tag{1}
\]
In particular, \(B_{\rm flip}(h)=o(h^2/(\log h)^2)\).

The proof uses elementary divisor estimates and unique factorization of ideals in a quadratic number field. It does not use a distribution theorem for primes. The prime pool enters only through a congruence that excludes one degenerate conic.

## 1. The equations to count

There are only constantly many choices of pin rows \(a,c\in\{1,2\}\). Write
\[
\alpha=3-2a,\qquad \delta=c-a,\qquad
y=2p+\alpha,\qquad \Delta=q-p,
\]
where \(p,q\equiv3\pmod4\) are primes and \(q>p\). The two black pair vectors are
\[
(x,y),\qquad (z,y+2\Delta-2\delta),
\]
with positive odd \(x,z\). The established mixed-support equations give
\[
x\mid y\Delta,\qquad
z^2=x^2-4(\Delta-\delta)(y+\Delta-\delta).          \tag{2}
\]
We may use the relaxed bounds
\[
1\le y,\Delta\le h,\qquad 1\le x\le h^2.        \tag{3}
\]
The second inequality follows from the divisibility in (2).

For fixed \(a,c,x,z,y,\Delta\), the relative pin displacement is forced:
\[
C_x-A_x=\frac{x-z}{2}-\frac{y\Delta}{x}.          \tag{4}
\]
Thus each arithmetic tuple specifies at most constantly many normalized supports. Requiring the correct phase of (4), that both pins precede the free points, and that every corner lies in the strip only removes tuples.

Put
\[
g=\gcd(x,y),\qquad x=gX,\qquad y=gY,
\qquad \gcd(X,Y)=1.
\]
Since \(x,y\) are odd, \(g\) is odd. The first equation in (2) becomes \(X\mid\Delta\), so
\[
\Delta=XT,\qquad T\ge1,\qquad XT\le h.           \tag{5}
\]
We split at \(X=\sqrt h\).

## 2. A uniform quadratic-equation lemma

We use the following form, with constants uniform in the coefficients.

**Lemma.** Fix \(C_0>0\). Suppose integers \(A,B,C\) satisfy
\[
A\ne0,\qquad N=B^2-4AC\ne0,
\]
and all coefficients and the sought integer coordinates \(u,v\) have absolute value at most \(H^{C_0}\). Then
\[
v^2=Au^2+Bu+C                                  \tag{6}
\]
has \(O_{C_0,\varepsilon}(H^\varepsilon)\) such solutions.

**Proof.** Completing the square gives
\[
(2Au+B)^2-4Av^2=N.                              \tag{7}
\]
If \(A=d^2\) is a nonzero square, factor the left side as
\[
(2Au+B-2dv)(2Au+B+2dv)=N.
\]
Each signed factor pair determines at most one solution, giving \(O(\tau(|N|))\) possibilities.

Otherwise let \(K=\mathbb Q(\sqrt A)\), and work in its maximal ring of integers. The element
\[
\eta=(2Au+B)+2v\sqrt A
\]
is an algebraic integer of norm \(N\). Consequently its principal ideal has norm \(|N|\). Unique factorization of ideals bounds the number of ideals of this norm by \(\tau(|N|)\): above a split prime, an exponent \(e\) has \(e+1\) allocations between the two prime ideals; an inert or ramified prime has at most that many.

For each principal ideal, any two generators of norm \(N\) differ by a unit of norm one. In an imaginary quadratic field there are at most six units. In a real quadratic field, two distinct absolute values of norm-one units have ratio at least
\[
\frac{3+\sqrt5}{2}>1.
\]
Indeed, a positive norm-one unit \(u>1\) has integral trace \(u+u^{-1}>2\), so that trace is at least three. Both embeddings of \(\eta\) are polynomially bounded in \(H\); since their nonzero product is the integer \(N\), each embedding also has absolute value bounded below by a negative fixed power of \(H\). There are therefore only \(O_{C_0}(\log H)\) possible unit multiples within these bounds. This argument needs no description of a fundamental unit.

Thus (7) has \(O_{C_0}(\tau(|N|)\log H)\) solutions. The usual divisor bound, applied to the polynomially bounded integer \(|N|\), proves the lemma. The map from \((u,v)\) to \(\eta\) is injective because \(A\ne0\). \(\square\)

## 3. Small reduced horizontal offset

Suppose \(X\le\sqrt h\). There are at most
\[
\lfloor\sqrt h\rfloor\sum_{g\le h}\lfloor h/g\rfloor
=O(h^{3/2}(1+\log h))                            \tag{8}
\]
triples \((g,Y,X)\) with \(gY\le h\). We have deliberately dropped coprimality and parity restrictions.

For each such triple, (2) can be written as
\[
z^2+(y+2\Delta-2\delta)^2=x^2+y^2.               \tag{9}
\]
The right side is a positive integer bounded by \(2h^4\). The sum-of-two-squares divisor estimate gives \(O_\varepsilon(h^\varepsilon)\) possible ordered pairs on the left. Each determines \(\Delta\), since \(y\) and \(\delta\) are fixed. Equations (8) and (9) give \(O_\varepsilon(h^{3/2+\varepsilon})\) tuples in this branch, after absorbing the logarithm.

## 4. Large reduced horizontal offset

Suppose \(X>\sqrt h\). By (5), \(T<\sqrt h\). Hence the number of triples \((g,Y,T)\) with \(gY\le h\) is again \(O(h^{3/2}(1+\log h))\).

For fixed \((g,Y,T)\), substitution into (2) gives the conic
\[
z^2=AX^2+BX+C,                                 \tag{10}
\]
where
\[
\begin{aligned}
A&=g^2-4T^2,\\
B&=4T(2\delta-gY),\\
C&=4\delta gY-4\delta^2.
\end{aligned}                                  \tag{11}
\]
Its discriminant is
\[
N=16g^2\bigl(T^2Y^2-\delta gY+\delta^2\bigr).    \tag{12}
\]
We check both degeneracies explicitly.

First, \(A=0\) would imply \(g=2T\), contrary to the oddness of \(g\).

Second, if \(\delta=0\), then \(N=16g^2T^2Y^2>0\). If \(\delta=\pm1\) and \(N=0\), reduction of the factor in parentheses modulo \(Y\) gives \(Y=1\). The remaining equation is
\[
\delta g=T^2+1.
\]
Since \(g>0\), this forces \(\delta=1\) and \(g=T^2+1\). But \(\delta=1\) means \(a=1,c=2,\alpha=1\), so
\[
y=gY=T^2+1=2p+1\equiv7\pmod8.
\]
No square is congruent to six modulo eight. This is impossible.

All coefficients in (11), the coordinates \(X,z\), and the two embeddings used in the lemma are bounded by fixed powers of \(h\). The lemma therefore gives \(O_\varepsilon(h^\varepsilon)\) solutions for each triple \((g,Y,T)\). Summing over those triples proves the same bound as in the small-offset branch. Together they prove (1). \(\square\)

## 5. Consequence and scope

The sufficient counting criterion in [checkerboard_bridge_counting.md](checkerboard_bridge_counting.md) requires
\[
B_{\rm flip}(h)=o(h^2/(\log h)^2).
\]
Equation (1) supplies this. Its contribution to the local-lemma pressure is
\[
O_\varepsilon\bigl(h^{-1/2+\varepsilon}(\log h)^2\bigr),
\]
which tends to zero when \(\varepsilon<1/2\). Combined with the other boundary-family counts and the finite-buffer conditional argument, this removes the stated arithmetic obstruction to capturing checkerboard-parity core entropy in the canonical component.

The theorem concerns this boundary family. It neither proves global dominance over arbitrary mixed-parity sea components nor improves the square blackout exponent by itself.

## 6. Matching phases and a dense buffer alphabet

The same method removes the need for primes in the buffer. Allow any positive integers
\[
p,q\equiv3\pmod4,
\]
and keep rows \(1+(x\bmod2)+2p\). For matching phases, the black vectors have the form
\[
U=(2x,2p),\qquad V=(2z,2q),\qquad x,z>0.
\]
Put \(\Delta=q-p\) and \(\delta=c-a\). The common lower white row and nondegeneracy imply \(q>p\), hence \(\Delta\ge4\). Perpendicularity and equal norms give
\[
x\mid p(\Delta+\delta),\qquad
z^2=x^2+p^2-q^2.                                \tag{13}
\]
Let
\[
g=\gcd(x,p),\quad x=gX,\quad p=gY,
\quad \Delta+\delta=XT.
\]
Then \(gY\le h\) and \(XT\le h+1\). The small-\(X\) branch is handled by the circle equation \(z^2+q^2=x^2+p^2\), exactly as before. In the large-\(X\) branch, \(T\le\sqrt{h+1}\), and
\[
z^2=AX^2+BX+C
\]
with
\[
\begin{aligned}
A&=g^2-T^2,\\
B&=2T(\delta-gY),\\
C&=2\delta gY-\delta^2,\\
N&=4g^2(T^2Y^2-2\delta gY+\delta^2).
\end{aligned}                                  \tag{14}
\]

The leading coefficient can vanish here, but no genuine support has this property. Indeed, \(A=0\) gives \(g=T\), hence
\[
x=gX=TX=\Delta+\delta\le\Delta+1.
\]
On the other hand, \(z>0\) in (13) implies
\[
x>\sqrt{\Delta(2p+\Delta)}>\Delta+1,
\]
where the last inequality follows from \(p\ge3\) and \(\Delta\ge4\). This is a contradiction.

The discriminant is also nonzero for every admissible support. If \(\delta\le0\), its factor in parentheses is positive. If \(\delta=1\) and that factor vanishes, reduction modulo \(Y\) forces \(Y=1\), and then
\[
g=(T^2+1)/2.
\]
For this to be an integer, \(T\) is odd; consequently \(g\equiv1\pmod4\). But \(p=gY=g\equiv3\pmod4\), a contradiction.

The uniform conic lemma therefore applies, proving the matching-phase count
\[
O_\varepsilon(h^{3/2+\varepsilon}).             \tag{15}
\]
The phase-flipped proof already used only the congruence \(p\equiv3\pmod4\), so it remains valid for this dense pool. The other estimates in the boundary classification use only that different parameters differ by at least four and that the free rows are at least seven. They therefore remain valid as well.

There are \(h/8+O(1)\) available parameters in each phase. Thus both cross-pair families have local-lemma pressure \(O_\varepsilon(h^{-1/2+\varepsilon})\), and all other boundary families have pressure tending to zero. The finite-buffer entropy-capture argument may consequently use the dense residue pool instead of a prime pool. No prime number theorem or quadratic nonresidue input is needed for this checkerboard bridge.

## 7. A universal low-pin bound, with no residue restriction

The residue restriction can also be removed by counting the degenerate conics instead of excluding them. This gives a more general geometric statement.

**Theorem.** Suppose a mixed side/diagonal support has one pin in each black pair. Both pins lie in rows \(\{1,2\}\), both free points lie in rows at least seven, and both pins precede both free points horizontally. The number of normalized supports in a height-\(h\) strip is
\[
O_\varepsilon(h^{3/2+\varepsilon}),
\]
without any row or column congruence restrictions.

Write the pin rows as \(a,c\), let \(\delta=c-a\), and orient both black vectors from their pin to their free endpoint:
\[
U=(x,y),\qquad V=(z,v),\qquad x,z>0,\quad y,v\ge5.
\]
The connector's vertical component is an integer \(\Delta\), and
\[
v=y+2\Delta-2\delta,
\qquad x\mid y\Delta,
\qquad z^2=x^2-4(\Delta-\delta)(y+\Delta-\delta).
\tag{16}
\]
The lower common white row is \(a+\Delta\), so \(\Delta\ge1-a\ge-1\). Its upper row also lies in the strip, giving \(|\Delta|\le h\). If \(\Delta=0\), perpendicularity makes the entire connector zero, which is not a mixed support.

As before, write \(x=gX,y=gY\), with \(\gcd(X,Y)=1\), and \(\Delta=XT\). The small branch \(X\le\sqrt h\) is bounded by the circle equation (9), using only \(gY\le h\). In particular, the possible negative shift \(\Delta=-1\) belongs to this branch, since it forces \(X=1\).

In the large branch, \(\Delta>0\) and \(1\le T<\sqrt h\). The coefficients and discriminant are still (11) and (12). Every nondegenerate conic is counted by the uniform lemma. There are two exceptional cases to address.

If \(A=0\), then \(g=2T\) and \(x=2\Delta\). The norm equation becomes
\[
z^2=-2xy+4\delta(x+y)-4\delta^2.
\]
For \(\delta\le0\), the right side is negative. For \(\delta=1\), it equals
\[
4-2(x-2)(y-2).
\]
Since \(x=2\Delta\) is positive and even and \(y\ge5\), positivity forces \(x=z=2\). The pin displacement (4) is then \(-y/2\), and the free diagonal endpoint has horizontal coordinate \(2-y/2<0\) relative to the side pin. This contradicts the required same-tail ordering. In fact \(\Delta=1\) would already put this case in the small branch.

If \(N=0\), then the calculation in Section 4 gives
\[
\delta=1,\qquad Y=1,\qquad g=T^2+1.
\]
For each \(T\le\sqrt h\), the condition \(\Delta=XT\le h\) leaves at most \(h/T\) values of \(X\). The norm equation then determines at most one positive \(z\), and (4) determines the normalized pin displacement. The total number of these exceptional supports is therefore
\[
O\!\left(\sum_{T\le\sqrt h}\frac hT\right)
=O(h\log h),
\]
which is smaller than the claimed bound. No congruence exclusion is needed.

This proves the universal theorem. The same-pair two-pin estimates in the boundary classification also need no residue restriction: the two free rows differ by \(O(\sqrt h)\) or by at most two, giving respectively \(O(h^{3/2})\) and \(O(h)\) row choices. Thus arbitrary dense high-row alphabets may replace the special residue pools whenever the underlying coloring law already excludes singleton and vertical rivals in the bulk. The earlier residue arguments remain valid special cases.
