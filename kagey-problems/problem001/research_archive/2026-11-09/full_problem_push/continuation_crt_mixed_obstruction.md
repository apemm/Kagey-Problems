# CRT mixed collisions survive angle exclusion and local P tests

9 November 2026. The quadratic-width CRT scaffold has genuine crossed
mixed collisions. The two certificates below obey all the stated prime
and strip bounds. Each uses four labels which have no vertical P rival
among themselves. Thus a P coloring alone does not validate the scaffold.

The slope-one example also has both primes larger than \(4h\), with two
a quadratic nonresidue at both primes. The rational Pythagorean slope
\(4/3\) does not remove the mixed obstruction either.

## 1. A four-point template

Let \(S>0\) be even, let \(\ell>0\) be even, let y be positive and odd,
and let a be odd. Choose the four black points
\[
 A=(0,a),\quad B=(S,a+y),\quad
 C=(S-\ell y,a+\ell S),\quad
 D=(-\ell y,a+y+\ell S).
\]
The first black side has vector \(U=(S,y)\). Translate it by
\[
 T=(-\ell y,\ell S).
\]
Then \(U\cdot T=0\), so A, B and the two points
\[
 W_1=(-\ell y,a+\ell S),\qquad
 W_2=(S-\ell y,a+y+\ell S)
\tag{1}
\]
are a nondegenerate tilted rectangle. The four points C, D, \(W_1,W_2\)
are also an axis-aligned rectangle. The two rectangles have the same
white presentation if A, B, C, D are black and \(W_1,W_2\) are white.

This template includes exactly two odd and two even selected black
points. It is therefore the crossed mixed role left by the CRT
parity reductions.

For slope \(P/Q\), put \(\delta=QS/P\), assumed to be a positive even
integer. The four double labels are
\[
\begin{aligned}
 &(a,a+y-\delta),\quad(a+\delta,a+y),\\
 &(a+\ell S,a+y+\ell S+\delta),\quad
 (a+\ell S-\delta,a+y+\ell S).
\end{aligned}
\tag{2}
\]
The first coordinate in each label is odd. In the columns of C and D,
the unused mate differs from the proposed white row by \(\delta\).
Thus neither white point in (1) is covered.

The CRT center equations
\[
 Qx\equiv P a_{\rm odd}\pmod p,\qquad
 Qx\equiv P b_{\rm even}\pmod q
\]
are compatible with the relative columns \(0,S,S-\ell y,-\ell y\)
provided
\[
 p\mid QS-\ell(Qy+PS),\qquad
 q\mid QS+\ell(Qy+PS).
\tag{3}
\]
The first congruence checks both odd mates C and D; the second checks
both even mates. The A/B mate differences already agree exactly.
We separately check that the canonical representatives modulo \(98pq\)
have these relative positions, so there is no wraparound assumption.

## 2. Slope one, with both nonresidue hypotheses

Take
\[
 p=4\,000\,291,\quad q=4\,000\,301,\quad
 S=490,\quad\ell=784,\quad y=499\,547,\quad a=1.
\]
Both p and q are prime. They are respectively 3 and 5 modulo eight,
so two is a quadratic nonresidue at each. At height
\[
 h=884\,198
\]
both primes exceed \(4h\). The four labels are
\[
 (1,499058),\ (491,499548),\
 (384161,884198),\ (383671,883708).
\]
Their canonical centers, satisfying \(98\mid x\), \(x\equiv a\pmod p\)
and \(x\equiv b\pmod q\), are
\[
\begin{array}{r}
491073062966486\\
491073062966976\\
491072671322128\\
491072671321638.
\end{array}
\]
Their relative centers are \(0,490,-391644358,-391644848\), exactly
the template above. The squared side length is \(249547445309\).

The construction arises from \(p+q=16\cdot500037\),
\(S=49(q-p)\) and \(\ell=49\cdot16\).
Consequently the two quantities in (3) are \(-98p\) and \(98q\).

## 3. Slope four thirds

Take
\[
 P=4,\quad Q=3,\quad
 p=40\,000\,463,\quad q=40\,000\,487,
\]
\[
 S=392,\quad\ell=2450,\quad y=532817,\quad a=1.
\]
Here \(\delta=294\). Both primes exceed
\((P^2+Q^2)h=25h\), with
\[
 h=1\,493\,512.
\]
The labels are
\[
 (1,532524),\ (295,532818),\
 (960401,1493512),\ (960107,1493218).
\]
Their canonical centers for \(98\mid x\),
\(3x\equiv4a\pmod p\), \(3x\equiv4b\pmod q\), are
\[
\begin{array}{r}
47022155608484518\\
47022155608484910\\
47022154303083260\\
47022154303082868.
\end{array}
\]
Their relative centers are
\(0,392,-1305401258,-1305401650\).
Equation (3) again gives \(-98p\) and \(98q\), since
\(QS=49(q-p)\) and
\(\ell(Qy+PS)=49(p+q)\).

This example satisfies the large-prime hypothesis used to exclude all
inserted-only tilted right angles. It shows that choosing a slope whose
squared direction norm is a rational square does not remove mixed
collisions.

## 4. No vertical rival among the four labels

In each example, the pairs A/B and C/D are the only pairs of double
columns at horizontal distance at most \(h-1\).
For every odd/even black selection across either such pair, the
nonzero vertical difference v satisfies
\[
 S^2<2|v|+1.
\]
Therefore \(v^2+S^2\) lies strictly between the consecutive squares
\(v^2\) and \((|v|+1)^2\). It cannot be the square of a vertical
alternative length. All other column pairs are farther apart than
\(h-1\), so their vertical alternatives do not fit in the strip.

This statement concerns the four-label subconfiguration. The complete
CRT scaffold has many more labels and may also have P rivals elsewhere.
The conclusion is that the P test does not imply the mixed test, even
on a P-free subconfiguration of the prescribed scaffold.

## 5. Verification and scope

[The standard-library checker](verify_continuation_crt_mixed.py) verifies
primality by trial division, all CRT representatives, all row and prime
bounds, and both actual rectangle presentations. Its rectangle test uses
equal diagonal midpoints and lengths rather than the displayed
orthogonality derivation. It also exhausts every possible odd/even
vertical-rival selection among these four labels.

The exact output is saved in
[the certificate file](verify_continuation_crt_mixed.json).
Both certificates passed [independent arithmetic and geometric
review](continuation_crt_mixed_independent_audit.md).

No quadratic-width impossibility follows. A different prime selection,
a refinement which separates these four-label supports, or a different
placement may still work. These examples disprove automatic mixed
exclusion under the currently stated CRT hypotheses.

