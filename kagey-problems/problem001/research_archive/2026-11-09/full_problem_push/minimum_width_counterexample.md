# The minimum-width conjecture fails first at height 655

9 November 2026. The minimum-entry conjecture listed in the paper's open
questions is false:
\[
 \min\{\text{row 655 of A338885}\}=104
 \quad\text{but}\quad A228286(655)=115.
\]
The two values at height 655 have elementary proofs. A complete finite
enumeration, checked independently, verifies that 655 is the first
counterexample.

These heights and widths are geometric coordinate spans, as in
[A338885](https://oeis.org/A338885). A grid containing the displayed
rectangle has 656 rows of points and 105 columns of points. This result
concerns the rectangle-width spectrum, not the equality threshold of the
blackout problem.

## 1. The exact optimization problem

After reflection and translation, the adjacent sides of any tilted lattice
rectangle can be written
\[
 (kp,kq),\qquad(-lq,lp),
 \qquad k,l,p,q\in\mathbb Z_{>0}.
\]
For example, divide the coordinates of the first side by their greatest
common divisor to obtain the primitive direction \((p,q)\). Every integral
perpendicular side is then an integral multiple of \((-q,p)\).

Its bounding height and width are
\[
 n=kq+lp,\qquad w=kp+lq.                         \tag{1}
\]
Allowing nonprimitive \((p,q)\) does not change the set of possibilities.

If any of the four positive parameters equals one, the resulting
optimization is exactly
\[
 A228286(n)=
 \min_{\substack{x,y,z\ge1\\xy+z=n}}(x+yz).       \tag{2}
\]
For example, \(k=1\) corresponds to \((x,y,z)=(p,l,q)\), and \(q=1\)
corresponds to \((x,y,z)=(l,p,k)\). The other two cases follow by symmetry.
Conversely every triple in (2) occurs by taking \(k=1\).

Thus the conjecture asserts that a width minimizer in (1) always has at
least one parameter equal to one. The counterexample requires four
parameters greater than one.

## 2. A rectangle of height 655 and width 104

Take
\[
 (k,l,p,q)=(2,31,21,2).
\]
Then
\[
 kq+lp=4+651=655,\qquad kp+lq=42+62=104.
\]
One translated set of corners is
\[
 (62,0),\quad(104,4),\quad(42,655),\quad(0,651).
                                                        \tag{3}
\]
Its adjacent side vectors are \((42,4)\) and \((-62,651)\). Their dot
product is
\[
 42(-62)+4(651)=-2604+2604=0.
\]
Both vectors have nonzero horizontal and vertical components. The
rectangle is tilted and touches all four sides of its \(104\times655\)
bounding box.

## 3. The restricted minimum is 115

The triple \((x,y,z)=(109,6,1)\) gives
\[
 xy+z=655,\qquad x+yz=115.
\]
It remains to rule out a value at most 114.

Suppose \(xy+z=655\) and \(x+yz\le114\). Then \(z\le114\), and
the arithmetic-geometric mean inequality gives
\[
 (x+yz)^2\ge4xyz=4z(655-z).                      \tag{4}
\]
The function \(z(655-z)\) increases for \(1\le z\le114\). At \(z=5\),
the right side of (4) is \(13000>114^2=12996\). Therefore \(z\le4\).

Factoring the four possible values of \(xy\) gives:

| \(z\) | Factorization of \(655-z\) | Minimum \(x+yz\) over its factor pairs |
|---:|---|---:|
| 1 | \(654=2\cdot3\cdot109\) | 115 |
| 2 | \(653\), prime | 655 |
| 3 | \(652=4\cdot163\) | 175 |
| 4 | \(651=3\cdot7\cdot31\) | 115 |

For the last row the minimum occurs at \((x,y)=(31,21)\).
The finite factorizations exclude every value at most 114. Hence
\[
 A228286(655)=115.                              \tag{5}
\]
This uses the defining formula in [A228286](https://oeis.org/A228286),
rather than relying on a downloaded sequence value.

## 4. No tilted rectangle at this height has width below 104

Suppose (1) holds with \(n=655\) and \(w\le103\).
No parameter equals one, by (5). Hence all four parameters are at least
two.

Since
\[
 n-w=(p-q)(l-k)>0,
\]
simultaneously swapping \(p,q\) and \(k,l\), if needed, lets us assume
\[
 p>q,\qquad l>k.
\]
Put \(t=kq\). Then \(t\ge4\), \(lp=655-t\), and \(t<655/2\).
Another arithmetic-geometric mean bound gives
\[
 w^2=(kp+lq)^2\ge4klpq=4t(655-t).               \tag{6}
\]
If \(t\ge5\), the right side of (6) is at least
\[
 4\cdot5\cdot650=13000>103^2.
\]
Thus \(t=4\). Because \(k,q\ge2\), this forces \(k=q=2\), and
\[
 lp=651,\qquad w=2(p+l).
\]
The closest positive factor pair of \(651\) is \(21,31\), so
\[
 w\ge2(21+31)=104,
\]
contradicting \(w\le103\). Together with (3), this proves that the exact
minimum is 104.

## 5. Certification that this is the first counterexample

The independent checker [minimum_width_audit.py](minimum_width_audit.py)
examines all heights \(2\le n\le655\). It computes (2) through a complete
finite search, and separately checks the value at 655 by direct enumeration
of positive \(x,y\).

For fixed \(y>1\), the expression
\[
 x+yz=\frac ny+z\left(y-\frac1y\right)
\]
increases with \(z\). Therefore the least positive residue of \(n\)
modulo \(y\) suffices, with residue zero replaced by \(y\).

For the unrestricted problem, any counterexample has \(w<A228286(n)\).
The already computed restricted values give a common finite upper bound
on \(w\). Enumerating positive parameters in (1) below that width bound
is complete. Cases with a parameter one are already accounted for by
(2); every other case can be normalized to \(p>q\) and \(l>k\).

The independent [factorization checker](minimum_width_factor_check.py)
uses the paper's leftmost-corner parameters instead: height \(b+d=n\),
width \(a+c\), and \(ac=bd\). It enumerates factor pairs of \(b(n-b)\).
The lower bound \(a+c\ge2\sqrt{b(n-b)}\) makes its stopping criterion
exact.

The two independent scans find equality for every \(2\le n<655\), and
the single discrepancy
\[
 (n,\text{actual minimum},A228286(n))=(655,104,115).
\]
The exact values at 655 do not depend on this scan. Its additional
contribution is the finite minimality statement.

The checker and its JSON output are kept beside this note. No OEIS
submission or external message has been made.
