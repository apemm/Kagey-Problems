# A quadratic scaffold with symmetric prime control

9 November 2026. This note gives an unconditional scaffold of width
\(O(h^2)\) containing every odd/even row pair once. It excludes every
tilted right angle on three required black cells. It also reduces the
remaining four-cell collisions to a specific two-block arithmetic system.
The scaffold is not yet proved identifying, and its other columns are
empty. No filled-board or quadratic threshold conclusion follows here.

## 1. Placement and the prime input

Let \(p<q=p+D\) be odd primes, put
\[
K=4D^2+1,\qquad p>100(D^2+1)h,
\tag{1}
\]
and place the label \((a,b)\), with \(a\) odd and \(b\) even in
\([1,h]\), at
\[
x(a,b)=2qa-2pb=2Da+2p(a-b).
\tag{2}
\]
A translation makes the smallest column zero. Distinct labels have
distinct columns: equality in (2) implies \(p\mid a-a'\) and
\(q\mid b-b'\), hence both differences vanish. All marked columns are
congruent to two modulo four before translation. Their total span is at
most \(2(p+q)(h-1)\).

There is an absolute constant \(D_0\) such that, for every sufficiently
large \(N\), two primes in \([N,2N+O(1)]\) differ by an even integer
\(D\in[2,D_0]\). The needed statement follows directly from the proof of
Maynard's Proposition 4.2: the weighted sum is over
\(N\le n<2N\), and equation (4.4) is positive for every sufficiently
large \(N\). Proposition 4.3 gives \(M_{105}>4\), so a fixed admissible
105-tuple supplies two primes in each such interval. For example, the
first 105 primes exceeding 105 form a fixed admissible tuple. This uses
the interval calculation, not just the theorem's liminf formulation.
[Maynard, *Small gaps between primes*, pp. 388–390](https://annals.math.princeton.edu/wp-content/uploads/annals-v181-n1-p07-p.pdf).

Taking \(N\) to be a sufficiently large constant times \(h\), using the
largest possible \(D_0\) in (1), therefore gives \(p,q=O(h)\).
The finitely many smaller heights can be absorbed into the absolute
constant. The actual difference \(D\) may vary with \(h\).

Write \(u=a-b\), which is always odd. Labels with the same \(u\) form
an **offset block**. In this block the odd and even black points lie on
the two parallel lines
\[
(x,y)=(2Da+2pu,a),\qquad (2Da+2pu,a-u).
\tag{3}
\]

## 2. No three-black tilted right angle

At a black vertex, two legs to points of the opposite row parity have
odd vertical components and horizontal components divisible by four.
Their dot product is odd, so they cannot be perpendicular.

At an odd vertex, reduce the other cases modulo \(p\). For every label,
\(x\equiv2Da\pmod p\). If both other points are odd, the dot product is
\[
K(a_1-a_0)(a_2-a_0)\pmod p.
\]
Since \(p>K\) and \(p>h\), one of the row differences is zero. That leg
is horizontal; a perpendicular leg would have to be vertical. A column
contains only one odd point, so this gives only an axis-aligned angle.

If the first other point is odd and the second is even, the reduction is
\[
(a_1-a_0)\bigl(4D^2(a_2-a_0)+b_2-a_0\bigr).
\]
The bracket is odd, nonzero, and has absolute value below \(Kh<p\).
Again the same-parity leg must be horizontal, leaving only an
axis-aligned angle.

The even-vertex argument is identical modulo \(q\), because
\(x\equiv2Db\pmod q\). Thus every tilted rectangle has at most two
required black corners. In particular there are no hidden tilted
rectangles, no singleton presentations of tilted rectangles, and no
six-black collision of singleton presentations.

## 3. Vertical rivals reduce to fixed-offset distance graphs

Two black points that can have an in-strip vertical alternative diagonal
must have horizontal separation at most \(h-1\). Distinct offset blocks
have horizontal separation at least
\[
4p-2D(h-1)>h-1.
\]
Thus every such rival is internal to one offset block. Only an
odd/even black pair can rival a vertical axis side in the final parity
graph. For labels of common offset \(u\), let \(d=a-a'\), an even
nonzero integer. The exact length equation is
\[
(2Dd)^2+(u+d)^2=L^2,
\tag{4}
\]
together with the actual vertical-completion containment conditions.
This is the fixed-offset distance graph with horizontal scale \(2D\).
Its uniformly bounded chromatic number is not known here. The earlier
five-color lower bound at scale two does not settle this question.

## 4. Four-point mixed collisions: notation

The remaining tilted/tilted or tilted/axis collision has a common white
pair which is a side of one rectangle and a diagonal of the other. Let
\(A,B\) be the black side, \(C,E\) the black diagonal, and write
\[
U=B-A,\quad V=E-C,\quad T=(C+E-A-B)/2.
\]
The necessary and sufficient geometric equations, before containment,
are
\[
|U|=|V|,\qquad U\cdot T=0.
\tag{5}
\]
The common pair is \((C+E\pm U)/2\). Its coordinates must be integral,
and both rectangles must be nondegenerate. In particular \(T\ne0\)
and \(U,V\) are not parallel. The four black corners are distinct: a
shared black corner, together with the common white pair, would make
the two rectangles share three corners and hence coincide.

Same-side and same-diagonal collisions reduce to a hidden rectangle;
the no-three-corner result therefore excludes them. Axis/axis collisions
are excluded by the complete bipartite row-pair graph. Hence (4) and (5)
exhaust the possible failures of the empty scaffold.

## 5. A collision cannot cross blocks in its black side

Suppose the side joins different blocks. Orient \(U_x>0\), and orient
the black diagonal so that \(V_x>0\). Put \(H=h-1\). A pair within one
block has length at most \(\sqrt K H\), while a cross-block pair has
horizontal separation at least \(4p-2DH\). Thus the diagonal also
joins different blocks.

Write the respective offset differences as \(w,w'\), and the odd-index
differences as \(d,d'\). Both \(w,w'\) are positive even integers.
Equal norms give
\[
|U_x-V_x|\le \frac{H^2}{U_x+V_x}.
\]
Since \(U_x=2pw+2Dd\), the bounds in (1) imply \(w=w'\): otherwise
\(2p|w-w'|\ge4p\), whereas the remaining terms have total magnitude
at most \(4DH+H^2/(8p-4DH)<4p\).

Similarly, \(U\cdot T=0\) gives
\(|T_x|\le H^2/(4p-2DH)\). Writing the difference of the two offset
sums as \(W\), and the difference of their odd-index sums as \(S\),
we have \(T_x=pW+DS\), with \(|S|\le2H\). If \(W\ne0\), its even
parity gives \(p|W|\ge2p\), contradicting this bound. Thus the offset
sums also agree. After the chosen orientations,
\[
u_C=u_A=u,\qquad u_E=u_B=v,\qquad w=v-u>0.
\tag{6}
\]

Let \(\alpha=a_C-a_A\), \(\beta=a_E-a_B\), and
\(S=\alpha+\beta\). Both differences are even. Integrality of the
common white rows says that the number of parity changes in the two
matched pairs \((A,C),(B,E)\) is even.

If neither pair changes parity, then \(T=(DS,S/2)\).
Orthogonality forces \(S=0\). Equal norms then give either
\(\alpha=0\), making the black pairs identical, or
\(K\alpha=2DU_x+U_y\), which is impossible by (1) and
\(|\alpha|\le H\).

If both matched pairs change parity in opposite directions, then
\(T_y=(S\pm w)/2\). Orthogonality gives
\[
(2DU_x+U_y)S=\mp U_yw.
\]
The right-to-left coefficient ratio has magnitude below one by (1), so
the integer \(S\) is zero. This would force \(U_y=0\), but the two
side points have opposite row parity.

It remains that both changes have the same direction. The side is then
monochromatic in row parity, and the diagonal has the other parity.
For an odd side with \(U_y\ne0\), reduction modulo \(p\) gives
\[
K S=u+v.
\]
The congruence is an equality because its difference has magnitude less
than \(p\). Substituting into the original orthogonality equation gives
\(4Dp wS=0\). Thus \(S=u+v=0\), and \(T=0\), a degeneracy.
For an even side the same argument modulo \(q\) gives
\(KS=-(u+v)\), followed by the same conclusion.

Finally suppose this monochromatic side is horizontal. Orthogonality
gives \(S=0\). Its horizontal component is \(2pw\) or \(2qw\).
Equal norms take the form
\[
8D\alpha U_x=4K\alpha^2\pm4\alpha w+w^2.
\]
The case \(\alpha=0\) is impossible. Otherwise, dividing absolute
values by \(|\alpha w|\), and using the nonzero even integers
\(\alpha,w\), would give
\[
16Dp\le (2K+1)H+4,
\]
contrary to (1). This also excludes horizontal axis rivals.

## 6. The only remaining mixed system

The side and the diagonal must each lie in one offset block. Their
blocks may be different. If the side is monochromatic in row parity,
its vector is parallel to \((2D,1)\). Write its parity indicator as
\(\varepsilon\in\{0,1\}\), and the diagonal's as \(\eta\). The
orthogonality equation, after division by the nonzero odd-index
difference, is
\[
KS+8Dp(v-u)-2\eta v+2\varepsilon u=0.
\]
Condition (1) therefore forces \(v=u\). In one block,
equal-length monochromatic vectors are parallel, making the diagonal
rectangle degenerate. If the side is mixed, integrality forces the
diagonal to be mixed too. If both pairs have the same block, their
center difference is tangent to the lines in (3), and its dot product
with the side has the nonzero odd coefficient \(Kd+u\). Again the
centers coincide.

Therefore every remaining mixed collision has one odd and one even
black point in each of two distinct blocks \(u,v\). Orient both black
pairs from their even endpoint to their odd endpoint. Let their
odd-index differences be \(d,e\), and the difference between the two
odd-index sums be \(S\). All three are even. The exact equations are
\[
\begin{aligned}
K d^2+2du+u^2&=K e^2+2ev+v^2,\\
(Kd+u)S&=(d+u-8Dp d)(v-u).
\end{aligned}
\tag{7}
\]
They must be supplemented with endpoint row bounds, integral labels,
white-row containment, and nondegeneracy. The case \(d=0\) is a
vertical side and belongs to the P test (4).

For \(d\ne0\), write \(g=\gcd(2Dd,d+u)\), an odd integer. The integer
perpendicular connector is
\[
T=t\bigl(-(d+u)/g,\,2Dd/g\bigr),\qquad t\in\mathbb Z\setminus\{0\}.
\]
Equivalently, (7) implies
\[
(Kd+u)t=-g(p+q)(v-u),\qquad |t|\le h-1.
\tag{8}
\]
Thus any prime divisor of \(p+q\) exceeding \(Kh\) would exclude this
last mixed class: it could divide neither factor on the left. This is
an arithmetic sufficient condition, not a prime-existence assertion.
The nearby-prime theorem alone supplies no such factor of \(p+q\).
Here \(|Kd+u|<Kh\) follows directly from the row bounds, since
\(Kd+u=(K-1)d+(d+u)\) and both \(|d|\) and \(|d+u|\) are at most
\(h-1\).

The remaining task is to control (4) and (7) at bounded additional
width cost. The two-prime placement does not remove them automatically,
and filling the empty columns is a further task.

## 7. The remaining mixed class is nonempty, even without P rivals

There is an explicit four-label counterexample to dropping (7). Let
\(m\) be even and \(A\) odd, and suppose
\[
p=mA-1,\qquad q=mA+1
\]
are prime. At height \(h=A+64m-28\), take the four labels
\[
\begin{aligned}
&(A+64m-30,\,64m+4),\quad(A+64m-28,\,64m+6),\\
&(A-26,\,4),\quad(A-28,\,2).
\end{aligned}
\tag{9}
\]
Their offsets are respectively \(A-34,A-34,A-30,A-30\).
After translation their columns are
\[
0,\quad 8,\quad T+8,\quad T,
\qquad T=8m(A-32).
\]
The rectangles
\[
\begin{aligned}
R={}&\{(0,64m+4),(8,h),(T,4),(T+8,A-28)\},\\
R'={}&\{(T+8,4),(T,A-28),(T,4),(T+8,A-28)\}
\end{aligned}
\]
have the common white presentation
\(\{(T,4),(T+8,A-28)\}\). For \(R\), the side vector
\((8,A-32)\) is perpendicular to the translation
\((T,-64m)\). The rectangle \(R'\) is axis-aligned.
The other two cells in each double column do not cover either common
white corner.

For a concrete instance, take
\[
m=1200,\quad A=1{,}000{,}049,\quad h=1{,}076{,}821,
\]
\[
p=1{,}200{,}058{,}799,\qquad q=1{,}200{,}058{,}801.
\]
Both numbers are prime, and \(p>500h\), as required by (1) with
\(D=2\). The four selected labels have no vertical P rival at this
height. Across their two offset blocks the horizontal separations exceed
\(h\). Within a block the relevant nonvertical squared lengths have
the form \(Y^2+64\), with \(Y\ge A-36>32\), strictly between
consecutive squares. Thus the mixed condition is independent of the
P condition, even in the nearby-prime scaffold.

## 8. Verification and review

`verify_nearby_prime_scaffold.py` checks every point-vector right angle
and every equal-norm side/diagonal pair at heights
\(4,8,12,16,20,24,28\), using explicitly verified twin primes satisfying
(1). It checks the predicted location of every vertical rival and every
mixed collision. The same script verifies the large four-label
certificate by exact integer arithmetic and trial-division primality.
Results are in `nearby_prime_scaffold_checks.json`.

The scaffold reduction and the primary-source interval argument passed
an independent mathematical audit. The finite checks are supporting
verification; the claims above follow from the displayed proofs.
