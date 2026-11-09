# CRT scaffold: angle exclusion and the remaining chain obstruction

9 November 2026. The CRT placement excludes every tilted rectangle
with three inserted black corners in quadratic width. Its remaining
vertical rivals reduce to fixed-offset chains. A positive-density
family of unsafe chains persists for every fixed rational slope and
even for every finite collection of such slopes. Thus discarding all
unsafe chains is not a subquadratic exceptional-set strategy.

This is an independent verification and extension of the CRT proposal.
It does not prove that a bounded chain coloring is impossible, nor
does it exclude choosing different slopes for different labels.

## 1. The placement and all three-black tilted angles

Let \(P,Q\) be fixed coprime positive integers, with \(P\) even
and \(Q\) odd. Choose distinct primes \(p,q>C_{P,Q}h\),
coprime to \(98Q\), where the fixed constant is larger than
\(P^2+Q^2\), \(P+Q\), and two. A parity label
\(e=\{a,b\}\), with \(a\) odd and \(b\) even, has its
unique center \(x_e\in[0,98pq)\) specified by
\[
 98\mid x_e,\qquad Qx_e\equiv Pa\pmod p,
 \qquad Qx_e\equiv Pb\pmod q.
\tag{1}
\]
Different labels have different centers: equality determines both
endpoint rows because \(p,q>h\). The width is \(O(h^2)\).
The slope-one version uses \(P=Q=1\); the angle argument below
still works for that separate case because the mixed coefficient is
the odd sum described after (3).

All horizontal coordinate differences are even. A right angle rooted
at the sole point of one physical row parity has two odd vertical
differences, so its scalar product is odd and cannot vanish.

Suppose instead that the root and a second point are odd, at rows
\(a_1,a_2\), and the third point is even, at row \(b_3\),
belonging to label \(\{a_3,b_3\}\). Multiplying the scalar
product by \(Q^2\) and reducing modulo \(p\) gives
\[
 (a_2-a_1)
 \bigl[P^2a_3+Q^2b_3-(P^2+Q^2)a_1\bigr].
\tag{2}
\]
The bracket is odd, hence nonzero, and has absolute value less than
\((P^2+Q^2)h<p\). If \(a_2\ne a_1\), neither factor
vanishes modulo \(p\). If \(a_2=a_1\), that leg is
horizontal, so an actual right angle has a vertical other leg and
is axis-aligned. The even-root case is identical modulo \(q\).

For three odd points, the same calculation is
\[
 (P^2+Q^2)(a_2-a_1)(a_3-a_1)\pmod p.
\tag{3}
\]
Any zero row difference again gives an axis-aligned angle, and all
other factors are nonzero modulo \(p\). Three even points use
\(q\). For slope one, (2) has bracket
\(a_3+b_3-2a_1\), which is likewise odd and has absolute
value less than \(2h\), while (3) has coefficient two.

These cases include a triple using both endpoints of one label.
Therefore every inserted-only three-black tilted rectangle is absent.
In particular there is no inserted-only tilted hidden rectangle.
The argument survives adding independent integer multiples of
\(98pq\) to the centers, because all the congruences persist.

## 2. Monochromatic mixed supports are absent

Suppose four selected odd points form a mixed support with black side
\(AB\) and black diagonal \(CD\). Modulo \(p\), all four
points lie on the line with direction \((P/Q,1)\), whose norm
\((P^2+Q^2)/Q^2\) is nonzero.

If the side has different endpoint rows, perpendicularity forces the
two black pairs to have the same row sum modulo \(p\). The row
sum difference has absolute value less than \(2h<p\), so their
actual sums agree. Equal norms then force their row differences to
agree up to sign modulo \(p\). The same size bound makes this an
actual equality. Thus the two black pairs have the same unordered
pair of actual rows.

Their actual vertical components have equal absolute values. Equal
norms give equal absolute horizontal components, and perpendicularity
with equal vertical centers forces equal horizontal centers. The
connector of the side rectangle is therefore zero, a degeneracy.

If the side is horizontal, its norm is zero modulo \(p\), so
the black diagonal has equal endpoint rows. Both black pairs are
horizontal, again making the diagonal rectangle degenerate. Four even
points give the same argument modulo \(q\).

A three-to-one physical parity split has odd total row sum, whereas
an integral common-corner pair requires an even sum. Consequently
only two-odd/two-even mixed supports remain in this scaffold.

## 3. Vertical rivals are slope chains

Let a possible vertical rival have black diagonal consisting of odd
row \(a_1\) from one label and even row \(b_2\) from another.
Write \(D=x_2-x_1\). A vertical alternative contained in the
strip has \(|D|\le h\). Equations (1), together with
\(|QD-P(a_2-a_1)|\le(P+Q)h<p\), force
\[
 QD=P(a_2-a_1)=P(b_2-b_1).
\tag{4}
\]
Thus both labels have the same offset \(t=b-a\). Coprimality
gives \(D=Pk\), \(a_2-a_1=b_2-b_1=Qk\), with \(k\)
even. The remaining norm equation is
\[
 P^2k^2+(Qk+t)^2=s^2.
\tag{5}
\]
For \((P,Q)=(4,3)\), this becomes
\[
 (5s-25k-3t)(5s+25k+3t)=16t^2.
\tag{6}
\]
The finite divisor parametrization is correct, but it does not make
the unsafe offsets \(t\) a zero-density set.

There is no wrap ambiguity for the positive short increments used
below. If \(D\le h\), \(x_1+D\ge98pq\) would give
\(x_1=98pq-r\) for \(0<r\le D\). Then
\(Qr+Pa_1\) is a positive multiple of \(p\), but is less
than \((P+Q)h<p\), a contradiction. Hence a congruence-compatible
increment in (4) is the actual center difference.

## 4. A universal positive-density unsafe-chain family

Under the \(P\)-even, \(Q\)-odd hypotheses, fix \(P,Q\).
Choose a fixed positive integer \(r\) large
enough that
\[
 T=(49Pr)^2-98Qr-1>0,
 \qquad N=(49Pr)^2+1.
\tag{7}
\]
The integer \(T\) is odd and \(T\equiv-1\pmod7\).
For every positive odd \(v\), take the two parity labels
\[
 \begin{aligned}
 e_1&=\{v+2,\ (T+1)v+2\},\\
 e_2&=\{(98Qr+1)v+2,\ (49Pr)^2v+2\}.
 \end{aligned}
\tag{8}
\]
Both have offset \(t=Tv\). Their row increment is \(98Qrv\),
and their actual center increment is \(98Prv\), by (1) and
the no-wrap argument. All coordinates lie in height \(Nv+2\).

Select the odd point of the first label and the even point of the
second. Their diagonal vector has components
\[
 (98Prv,\ ((49Pr)^2-1)v),
\]
and length \(Nv\), by the elementary Pythagorean identity
\((2m)^2+(m^2-1)^2=(m^2+1)^2\), with \(m=49Pr\).
Its vertical alternative has rows exactly
\[
 2,\qquad Nv+2.
\tag{9}
\]
The final complete parity graph owns this opposite-parity row pair.
Its owner is in a different column from the common vertical pair,
as follows already by reducing its odd endpoint modulo \(p\).
The tilted and axis rectangles therefore have the same presentation,
regardless of the colors of their common corners.

For every large \(h\), all odd multiples \(t=Tv\) with
\(Nv+2\le h\) are unsafe offsets. There are \(\Theta(h)\)
such offsets. Restricting further to \(t\le h/4\), if needed,
leaves the same order and gives \(\Theta(h)\) labels per chain.
Thus discarding entire unsafe chains discards \(\Theta(h^2)\)
labels. Taking \(7\nmid v\) shows that this persists among
offsets nonzero modulo seven, not only in the all-zero profile family.

For any fixed finite collection of slopes, form the corresponding
odd integers \(T_i\), and put \(T_*={\rm lcm}_i T_i\).
Every \(t=T_*v\), with \(v\) odd and not divisible by seven,
is unsafe for every slope whenever
\[
 h\ge 2+t\max_i\frac{N_i}{T_i}.
\tag{10}
\]
The quotient \(t/T_i\) is odd, so each construction (8)
applies. Hence a finite menu of slopes does not make the intersection
of unsafe-chain sets sparse. This conclusion concerns assigning or
discarding whole chains. It does not rule out bounded chain coloring,
label-by-label slope choices, or a different structured placement.

## 5. A smaller numerical witness for slope four-thirds

The triple \((8,15,17)\), scaled by \(49v\), gives an even
smaller family at slope \(4/3\):
\[
 \begin{aligned}
 t&=441v,\qquad D=392v,\qquad a_2-a_1=294v,\\
 e_1&=\{49v+2,490v+2\},\qquad
 e_2=\{343v+2,784v+2\}.
 \end{aligned}
\]
For odd \(v\), the vertical white pair has rows \(2\) and
\(833v+2\). Thus at height 835 the labels \(\{51,492\}\)
and \(\{345,786\}\) already give a rival with horizontal gap
392 and diagonal length 833, for every admissible choice of CRT primes.

[verify_crt_chain_obstruction.py](verify_crt_chain_obstruction.py)
constructs the actual CRT centers, checks primality directly, and
verifies the symmetric difference of the two rectangle corner sets.
[crt_chain_obstruction_check.json](crt_chain_obstruction_check.json)
records seven passing exact certificates, including the height-835
example and four rational slopes. The positive-density and finite-menu
claims are proved by (7)–(10), not inferred from these finite checks.
