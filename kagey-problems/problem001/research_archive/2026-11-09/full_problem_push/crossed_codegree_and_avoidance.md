# A crossed-pair codegree bound and a first-order avoidance expansion

9 November 2026. Independent review checked the crossed-pair calculation, overlap bookkeeping, and entropy consequence. The probability input is the arbitrary-indicator version of Suen's inequality, not the increasing-event form of Janson's inequality.

Consider any of the protected O, C, or Q laws in [phase_local_densities.md](phase_local_densities.md). At each column choose uniformly and independently among its allowed rows. Let \(\mathcal E_h\) be the distinct inclusion-minimal forbidden positive supports compatible with this law. They have four or six cells, all in distinct columns. Let \(\mu_h\) be their mean number per column, averaged over the period of the law. It is a finite, explicit geometric sum at each fixed height.

If \(r_X(h)\) is the entropy of this protected-phase sea language, and \(\bar\ell_X(h)\) is the period average of the logarithm of its allowed-row count, then
\[
 \boxed{\displaystyle
 \log r_X(h)=\bar\ell_X(h)-\mu_h
                 +O_\varepsilon(h^{-2+\varepsilon}).}
\tag{1}
\]
The constant is uniform over the finite set of protected laws. This does not give the entropy of the full ordinary-parity component, whose words need not obey a protected law.

## 1. Two-point completions of a mixed four-cell support

A mixed support consists of a black side \(AB\) and a black diagonal \(CD\), satisfying
\[
 |B-A|=|D-C|,\qquad
 (B-A)\cdot(C+D-A-B)=0.
\tag{2}
\]
The associated two rectangles are required to be nondegenerate and contained in the height-\(h\) strip. Every support cell lies in a different column.

**Crossed-pair lemma.** Fix \(A,C\) in different black pairs. If they lie in distinct columns, there are at most
\[
 O_\varepsilon(h^{1+\varepsilon})
\tag{3}
\]
mixed supports containing them in these roles.

Translate \(A\) to zero and write
\[
 C=(p,q),\quad B=(x,b),\quad D=(z,d),\qquad p\ne0.
\]
Put \(H=h-1\). All vertical differences from A have magnitude at most H. Define
\[
 s=x-z+p,\qquad t=d-q-b,\qquad
 K=s-2p,\qquad n=pt+qs.
\tag{4}
\]
In particular \(|t|\le3H\). The diagonal vector \(D-C\) is \((x-s,b+t)\). Expanding (2) gives
\[
 s^2+t^2=4(px+qb),\qquad x(s-2p)=b(t+2q).
\tag{5}
\]

### The zero determinant

If \(n=0\), then \(pt=-qs\), and the second equation in (5) gives
\[
 (s-2p)(px+qb)=0.
\]
Combining this with the first equation yields
\[
 (s-2p)(s^2+t^2)=0.
\]
If \(s=t=0\), the black diagonal vector equals the common white vector, so the diagonal rectangle is degenerate. Otherwise \(s=2p,t=-2q\), and the connector \(C+D-A-B=(2p-s,2q+t)\) vanishes, making the side rectangle degenerate. Thus every retained support has \(n\ne0\).

Solving (5) now gives
\[
 x=\frac{(t+2q)(s^2+t^2)}{4n},\qquad
 b=\frac{K(s^2+t^2)}{4n}.
\tag{6}
\]

### Only \(O(h)\) values of \(s\)

Since \(|b|\le H\), (6) gives
\[
 |K|s^2
 \le4H|n|
 \le12H^2|p|+4H^2|s|
 \le10H^2(|s|+|K|).
\tag{7}
\]
Here \(2|p|\le|s|+|K|\). If both \(|s|\) and \(|K|\) exceeded \(5H\), then
\[
 \frac{|K|s^2}{|s|+|K|}> \frac{25}2H^2,
\]
contradicting (7). Therefore
\[
 |s|\le5H\quad\text{or}\quad |s-2p|\le5H.
\tag{8}
\]
There are only \(O(h)\) integer choices.

For \(s\ne0,2p\), integrality in (6) implies
\[
 n\mid K(s^2+t^2).
\]
Since \(pt\equiv-qs\pmod n\), multiplication by \(p^2\) gives
\[
 n\mid K s^2(p^2+q^2).
\tag{9}
\]
The right side is nonzero. A signed divisor \(n\) determines \(t=(n-qs)/p\), then (6) determines \(x,b\), and (4) determines \(z,d\). The standard divisor bound therefore gives \(h^{o(1)}\) completions per s, once the polynomial coordinate bound below is recorded.

The exceptional values \(s=0,2p\) each have at most \(6H+1\) choices of t; the case \(n=0\) has already been excluded. This proves (3).

### Polynomial horizontal span

The divisor argument is uniform because every retained mixed support has horizontal diameter \(O(h^2)\). For an oblique black side \(U=(u,v)\), its nonzero integral perpendicular connector \(T\) has \(|v|,|T_y|\le H\). Both \(u,T_x\) are nonzero, and
\[
 |uT_x|=|vT_y|\le H^2.
\]
Thus \(|u|,|T_x|\le H^2\). The other black diagonal has the same length as U, hence horizontal component \(O(h^2)\).

If the black side is horizontal, the other diagonal has a nonzero vertical component w. Otherwise the diagonal rectangle would be degenerate. Writing its horizontal component as z,
\[
 (|u|-|z|)(|u|+|z|)=w^2\le H^2
\]
bounds \(|u|,|z|\) by \(O(h^2)\); the perpendicular connector is vertical. In both cases \(|p|=O(h^2)\), and all integers in (9) have polynomial size in h. A vertical black side would require two black cells in one column and is not a sea support.

## 2. Extension bounds after fixing support cells

Let \(M_{s,r}(h)\) be the maximum number of size-s forbidden supports containing r fixed black cells in distinct columns, for \(1\le r<s\). For every fixed \(\varepsilon>0\),
\[
 M_{4,r}(h)=O_\varepsilon(h^{3-r+\varepsilon}),
 \qquad
 M_{6,r}(h)=O_\varepsilon(h^{5-r+\varepsilon}).
\tag{10}
\]
The minimal-family restriction can only decrease these counts.

For four-cell supports:

* With one fixed cell, the rooted primitive-vector/divisor count gives \(O_\varepsilon(h^{2+\varepsilon})\). Fixing the cell removes the vertical-translation factor from the global \(O_\varepsilon(h^{3+\varepsilon})\) count.
* With two fixed cells in one black pair of a mixed support, choose the other equal-length vector in \(h^{o(1)}\) ways and the perpendicular connector in \(O(h)\) ways. With the cells in different pairs, use Section 1. Hidden rectangles through two fixed points have \(O(h)\) possibilities.
* With three fixed cells, one black pair is fixed. The remaining point lies on a specified circle and a nontrivial line, so there are at most two choices. For a hidden rectangle, three corners determine the fourth.

The horizontal-rival supports are included as the horizontal-side case of (2). The same-side and same-diagonal families reduce to hidden rectangles.

For six-cell supports, let \(D(P)=O(h^2\log^2 h)\) count tilted rectangles through a fixed point P, and let \(K(P,W)\) count rectangles through two distinct specified corners. Then
\[
 K(P,W)=O(h),\qquad
 \sum_WK(P,W)=3D(P).
\tag{11}
\]
For two points in the same column, a vertical-side completion would be axis-aligned and is excluded; the diagonal-circle case still has \(O(h)\) choices. Thus (11) holds in that case too.

With one fixed black cell, choose its rectangle and common corner W, then the other rectangle, giving \(O(h^4\log^4h)\). With two fixed cells in the same rectangle, (11) gives \(O(h^3\log^2h)\). If they belong to different rectangles, Cauchy–Schwarz gives
\[
 \sum_W K(P,W)K(P',W)
 \le
 \left(\sum_WK(P,W)^2\sum_WK(P',W)^2\right)^{1/2}
 =O(h^3\log^2h).
\tag{12}
\]
With three fixed cells distributed \(2+1\), choose the first rectangle in \(O(h)\) ways, then the second through W and the third cell in \(O(h)\) ways. In the \(3+0\) case, the fixed black triple determines W and leaves \(D(W)=O(h^2\log^2h)\) choices for the partner. With four fixed cells, the \(3+1\) distribution gives \(O(h)\) choices; in the \(2+2\) distribution W lies in an intersection of perpendicular lines or Thales circles, with \(O(h)\) strip points even if the loci coincide. The fixed pairs have distinct columns, so their perpendicular lines are not horizontal; vertical lines also contain only h strip points. With five fixed cells, one full black triple fixes W, and the other rectangle is determined. These are the remaining cases of (10).

## 3. The event dependency graph

For a finite core of length m, retain the events in \(\mathcal E_h\) whose black supports are contained in that core. They are canonical assignment events for independent categorical row variables.

Connect two events whenever they use a common column. This is a **strong** dependency graph: if two event families have no edge between them, their underlying sets of column variables are disjoint, so the families are independent.

Let
\[
 \mu_m=\sum_Ep_E,\qquad
 \delta_m=\max_E\sum_{F\sim E}p_F,\qquad
 \Delta_m=\sum_{\{E,F\}:E\sim F}\Pr(E\cap F),
\tag{13}
\]
where the final sum is over unordered pairs. All allowed-row counts are \(h/2+O(1)\).

The global support counts give
\[
 \mu_m=O_\varepsilon(mh^{-1+\varepsilon}),
 \qquad
 \delta_m=O_\varepsilon(h^{-1+\varepsilon}).
\tag{14}
\]
For \(\Delta_m\), conflicting assignments have joint probability zero. Compatible events sharing r columns share exactly r black cells. If their sizes are s,t, their joint probability is \(O(h^{-(s+t-r)})\). There are \(O_\varepsilon(mh^{s-1+\varepsilon})\) first events and, by (10), at most \(O_\varepsilon(h^{t-r-1+\varepsilon})\) second events through any selected r cells. The number of choices of those cells is bounded by an absolute constant. Hence
\[
 \Delta_m=O_\varepsilon(mh^{-2+\varepsilon}).
\tag{15}
\]
Identical events were deduplicated, and containment pairs were removed by minimality. This also handles the case where a four-cell support would be contained in a six-cell support.

## 4. The upper probability bound uses Suen's inequality

The primary input is [Janson, *New versions of Suen's correlation inequality*, Theorem 2](https://www2.math.uu.se/~svantejs/papers/sj121.pdf), with its strong-dependency-graph definition in Section 2. The author-hosted primary text was checked directly: the theorem applies to arbitrary indicator variables, and gives
\[
 \Pr(\text{avoid all events})
 \le\exp(-\mu_m+\Delta_m e^{2\delta_m}).
\tag{16}
\]
No monotonicity in Bernoulli point variables is assumed. This is why the theorem applies to categorical row assignments. Mutually conflicting events contribute zero to \(\Delta_m\).

Equations (14)–(16) give
\[
 \log\Pr(\text{avoid all})\le
 -\mu_m+O_\varepsilon(mh^{-2+\varepsilon}).
\tag{17}
\]

## 5. The matching lower probability bound

For sufficiently large h, put \(x_E=(1+4\delta_m)p_E\). The sum of neighboring weights is at most \((1+4\delta_m)\delta_m\). The elementary bound \(\prod(1-x_F)\ge1-\sum x_F\) shows
\[
 p_E\le x_E\prod_{F\sim E}(1-x_F).
\]
The product lower bound from the local lemma therefore gives
\[
 \Pr(\text{avoid all})\ge\prod_E(1-x_E).
\]
Expanding the logarithm, using \(\max p_E=O(h^{-4})\), yields
\[
 \log\Pr(\text{avoid all})
 \ge-\mu_m-O(\delta_m\mu_m)-O\!\left(\sum_Ep_E^2\right)
 =-\mu_m-O_\varepsilon(mh^{-2+\varepsilon}).
\tag{18}
\]
To obtain any stated exponent \(\varepsilon\), apply the intermediate support bounds with a smaller exponent, such as \(\varepsilon/3\).

Together, (17) and (18) give a uniform first-order avoidance expansion for every core length m.

## 6. Pass to protected-phase entropy

At fixed h, all support spans are bounded and the column alphabets are periodic. Consequently
\[
 \mu_m=m\mu_h+O_h(1).
\]
The total product-space size has logarithm \(m\bar\ell_X(h)+O_h(1)\). Avoiding the complete normalized positive-support family gives exactly the protected-phase finite-type language, whose recurrent entropy is unchanged by the finite-end convention.

Divide (17)–(18) by m and let \(m\to\infty\). This proves (1).

The mean \(\mu_h\) includes the minimal mixed four-cell events as well as the six-cell events. The six-cell contribution is evaluated in [six_support_leading_pressure.md](six_support_leading_pressure.md); the mixed four-cell contribution still needs its own weighted asymptotic. Even after comparing protected-phase entropies, a separate argument would be needed to control unrestricted parity excursions in the full canonical component.

