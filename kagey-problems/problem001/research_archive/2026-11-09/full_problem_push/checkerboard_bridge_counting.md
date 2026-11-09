# Counting the remaining checkerboard boundary supports

9 November 2026. The direct checkerboard prime buffer has genuine two-pin mixed collisions, as shown in [affine_prime_anchor_obstruction.md](affine_prime_anchor_obstruction.md). This note isolates the arithmetic family that initially blocked the bridge and proves the complete multiple-pin classification. The missing count is now proved in [checkerboard_flip_conic_bound.md](checkerboard_flip_conic_bound.md), and the completed theorem appears in [dense_residue_entropy_capture.md](dense_residue_entropy_capture.md).

Use the tail \(y_x=1+(x\bmod2)\), and free buffer rows
\[
 y_x=1+(x\bmod2)+2p,\qquad p\equiv3\pmod4\text{ prime}.
\tag{1}
\]
A two-pin support meeting a constant-length boundary lies in one tail when the core is sufficiently long. Reflect horizontally if necessary so both pins are left of every free point.

A mixed support consists of a black side \(AB\) and a black diagonal \(CD\), with
\[
 U=B-A,\quad V=D-C,\quad
 T=(C+D-A-B)/2,
 \qquad |U|=|V|,\quad U\cdot T=0.
\tag{2}
\]
The common white pair is \((C+D)/2\pm U/2\). All four support points are distinct. Fixed row quadruples give \(O_\epsilon(h^\epsilon)\) translated geometries, by the established mixed-support divisor lemma.

## 1. Both pins in the same black pair

Suppose first that \(A,B\) are the two pins. Orient them from left to right, so \(U_x>0\) and \(|U_y|\le1\). The midpoint of the free pair \(C,D\) is both higher and farther right than the pin midpoint. In fact
\[
 T_x>U_x/2,\qquad 0<T_y\le h-1.
\]
The perpendicularity equation forces \(U_y=-1\). Therefore
\[
 U_x^2/2<U_xT_x=T_y\le h-1.
\]
Since \(|V|=|U|\), the two free rows differ by at most \(\sqrt{2h+1}\). There are only \(O(h^{3/2})\) free row pairs, and hence
\[
 O_\epsilon(h^{3/2+\epsilon})
\tag{3}
\]
translated patterns of this type.

Suppose instead that \(C,D\) are the two pins. Their midpoint row is at most 2. The two common white corners, whose difference is \(U\), must both have row at least 1. Thus
\[
 |U_y|\le2.
\]
The two free rows differ by at most 2. In the pool (1), distinct primes have difference at least 4, so these free rows must use the same prime. There are \(O(h)\) row pairs, yielding
\[
 O_\epsilon(h^{1+\epsilon})
\tag{4}
\]
translated patterns.

With a free alphabet of size \(\asymp h/\log h\), both (3) and (4), divided by the square of the alphabet size, tend to zero for sufficiently small fixed \(\epsilon>0\).

## 2. Cross-pair pins with matching phases are impossible

Now let \(A,C\) be the pins, of rows \(a,c\in\{1,2\}\), and let \(B,D\) be their free partners. Put \(\delta=c-a\).

Suppose each free partner has the same column parity as its pin. Then their vertical offsets are \(2p,2q\), for primes \(p,q\equiv3\pmod4\). Their horizontal offsets are even, so write
\[
 U=(2X,2p),\qquad V=(2Z,2q).
\]
The lower common white row is \(c+q-p\), so containment and the prime progression give \(q\ge p\). Equality makes either the connector or the second rectangle degenerate. Thus \(q-p\ge4\).

The connector has vertical component \(q-p+\delta\), and integer horizontal component. Perpendicularity gives
\[
 X\mid p(q-p+\delta).
\tag{5}
\]
Norm equality gives
\[
 Z^2=X^2+p^2-q^2.
\tag{6}
\]
Since both free points lie to the right of their pins, \(X,Z>0\), and
\[
 X>\sqrt{q^2-p^2}>q-p+1.
\tag{7}
\]
The second inequality follows from \(p\ge3\) and \(q-p\ge4\).

If \(p\nmid X\), (5) makes \(X\) divide \(q-p+\delta\), contradicting (7). If \(p\mid X\), reduction of (6) modulo \(p\) gives \(Z^2\equiv-q^2\pmod p\), impossible because \(p\ne q\) and \(-1\) is a nonresidue. Thus no matching-phase cross-pair event exists.

## 3. Exact equations for the remaining phase-flipped family

Integrality of the common white midpoint forces the two vertical offsets to have the same parity. Thus if the matching-phase case does not apply, both partners have the opposite column parity from their pins.

Set
\[
 \alpha=3-2a\in\{-1,1\},\qquad
 \delta=c-a\in\{-1,0,1\},\qquad
 \Delta=q-p.
\]
The black side and diagonal vectors are
\[
 U=(x,2p+\alpha),\qquad
 V=(z,2q+\alpha-2\delta),
\]
where \(x,z\) are positive odd integers. The connector's vertical component is exactly \(\Delta\). Its lower common white row is \(a+\Delta\), so containment again forces \(q\ge p\); equality makes the connector zero. Hence \(q>p\) and \(\Delta\ge4\).

The necessary arithmetic conditions are
\[
 x\mid(2p+\alpha)\Delta,
\tag{8}
\]
and
\[
 z^2
 =x^2-4(\Delta-\delta)
            (2p+\alpha+\Delta-\delta).
\tag{9}
\]
The horizontal displacement between the pins must also be an integer of the parity \(c-a\):
\[
 C_x-A_x
 =\frac{x-z}{2}
  -\frac{(2p+\alpha)\Delta}{x}.
\tag{10}
\]
The same-tail inequalities and the remaining row bounds are additional filters.

Equations (8)–(10) cover the actual counterexamples in the companion note. The previous nonresidue proof no longer applies because \(2p+\alpha\) need not be prime.

A bound of the form
\[
 O_\epsilon(h^{2-\eta+\epsilon})
\]
for some fixed \(\eta>0\), on these normalized patterns, would make their two-free-variable local-lemma pressure tend to zero. Together with the other pinned-event estimates, this would recover exact entropy capture for checkerboard-parity cores through the canonical component.

The immediate divisor estimate gives only \(O_\epsilon(h^{2+\epsilon})\), which is insufficient after division by an alphabet of size \(\asymp h/\log h\). The subsequent conic argument improves this to \(O_\epsilon(h^{3/2+\epsilon})\). The counterexamples remain useful: they rule out replacing this counting argument by a zero-event claim.

## 4. The other multiple-pin families

The alternating low tail permits more pins than a constant row tail, but their counts are small.

A hidden tilted rectangle with two pins has those pins as an adjacent side: if they were a diagonal, the other two high free rows could not have the same midpoint. The free rows therefore differ by at most 1, giving \(O_\epsilon(h^{1+\epsilon})\) patterns. Three pins would be three corners of a unit diamond on rows 1 and 2, whose fourth row is 0 or 3, not an allowed free row.

A horizontal axis rival cannot have two pins. If its complementary horizontal black side contains a pin, both its points are pins, because every free row is at least 7. The tilted black diagonal lies strictly inside the horizontal extent of the common horizontal white diagonal, so it cannot then contain a free point to the right of both side columns. If both pins instead form the tilted black diagonal, their midpoint row is either half-integral or equal to their repeated low row; the latter case makes a horizontal alternative diagonal degenerate.

A mixed support cannot have three pins. If the two-pin pair is the diagonal, its midpoint row is at most 2, whereas the side containing the free point has vertical difference at least 5; a common white corner lies below the strip. If the two-pin pair is the side, orient it to the right. Its vertical component is \(0,\pm1\), while the other diagonal has positive vertical difference \(v\ge5\). For the free endpoint to lie to the right of the pin side's right endpoint, one must have
\[
 T_x>(U_x-V_x)/2.
\]
The cases \(U_y\ge0\) contradict perpendicularity immediately. When \(U_y=-1\), perpendicularity gives \(T_x=T_y/U_x\), and norm equality gives
\[
 U_x-V_x=\frac{v^2-1}{U_x+V_x}.
\]
Consequently \(4T_y>v^2-1\). But the pin rows are 1 or 2, so \(4T_y\le2v+2\), impossible for \(v\ge5\).

For a six-cell collision, classify its two three-black rectangles by the number of pins in each.

* At most two pins leave the usual nontrivial completion-row equation, giving \(O_\epsilon(h^{5-j+\epsilon})\) patterns with \(j\) pins.
* Three pins can be distributed as \((2,1)\), leaving three free row variables with one nontrivial relation, hence \(O_\epsilon(h^{2+\epsilon})\). The alternative \((3,0)\) is impossible: a three-pin rectangle is a unit diamond whose in-grid white completion lies at row 3 in the tail. A rectangle with that corner and three free points, all higher and farther right, would have two adjacent vectors with positive dot product.
* Four pins have distributions \((2,2)\) or \((3,1)\). In the first, each white completion differs from its free corner row by at most 1. In the second, the three-pin completion is at row 3, so the other rectangle's two free rows differ by 1 or 2. There are \(O(h)\) free row pairs and \(O_\epsilon(h^{1+\epsilon})\) geometries.
* Five pins would have distribution \((3,2)\). The first completion is at row 3, while the second differs from a free row by at most 1 and is therefore at least 6. This is impossible. Six pins lie entirely in the valid adjacent-row tail.

The fixed-row divisor estimate applies in all these cases; any zero row product gives an axis rectangle or coincident points and is discarded. Thus none of these families adds a new high-pressure event.

## 5. A precise sufficient counting criterion

Let \(B_{\rm flip}(h)\) be the number of normalized phase-flipped cross-pair mixed supports from Section 3, with free rows in the prime pools (1), retaining all integrality and strip-containment conditions.

The current prime alphabet has size \(k_h\asymp h/\log h\). The preceding classification shows that the weighted event mass incident to a free buffer column is bounded by
\[
 O_\epsilon\!\left(
 h^{-1+\epsilon}(\log h)^6
 +h^{-1/2+\epsilon}(\log h)^2
 \right)
 +O\!\left(\frac{B_{\rm flip}(h)}{k_h^2}\right).
\tag{11}
\]
Each normalized support can meet a fixed free column in only constantly many translations.

Therefore the single estimate
\[
 B_{\rm flip}(h)=o\!\left(\frac{h^2}{(\log h)^2}\right)
\tag{12}
\]
would suffice for the full product-form local lemma. A power saving would be more than enough.

Using finite prime buffers and conditioning first on all core-only events, exactly as in the canonical entropy-capture proof, (12) would imply that a fixed positive fraction of all admissible checkerboard-parity core words have extensions through the adjacent-row tail. Those tails lie in the canonical component. This would capture the full checkerboard entropy inside that component, not merely establish another lower bound of the same order. Strict Perron comparison with the proper checkerboard subgraph would then give strict canonical dominance over every purely checkerboard-parity component.

The conic bound now proves (12), and also handles matching phases without primality. Thus the full capture theorem can use dense residue buffers rather than prime buffers.


