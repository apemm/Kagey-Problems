# Full disjoint influence sets require a logarithmic width loss

9 November 2026. This identifies a limitation of the proved positional
construction. It does not give a lower bound for the true equality
threshold.

Let \(h=2n\), use the binary sea alphabet \(\{1,h\}\), and assign every
opposite-parity double once. For each edge \(e\), let \(A_e\) be the full
one-double influence set used in
[the near-quadratic construction](near_quadratic_threshold.md): it contains
every sea-column offset appearing in a three-black tilted rectangle or a
nonvertical mixed support with that double as its only label.

**Proposition.** If all translates \(X_e+(A_e\cup\{0\})\) are disjoint and
contained in a finite board of width \(m\), then
\[
 m\ge \frac{h^2}{2}\log h-O(h^2).
 \tag{1}
\]
In particular, optimizing only the placement of these full disjoint
influence sets cannot prove a width \(O(h^2)\).

## A divisor family inside every influence set

For an interior row \(2\le r\le h-1\), put
\[
 N_r=(r-1)(h-r),\qquad
 d_r=\tau(N_r)-1_{\{N_r\text{ is a square}\}}.
\]
Set \(d_1=d_h=0\).

For each positive divisor \(u\mid N_r\), put \(v=N_r/u\).
If \(u\ne v\), the three points
\[
 (0,r),\quad (u,1),\quad (v,h)
 \tag{2}
\]
form a tilted right triangle at \((0,r)\), because
\[
 uv+(1-r)(h-r)=0.
\]
Its fourth corner is
\[
 (u+v,h+1-r).
 \tag{3}
\]
Every row is inside the strip. Its span satisfies
\[
 u+v\le N_r+1\le
 1+\left\lfloor\frac{(h-1)^2}{4}\right\rfloor=W_h.
\]
The two required sea cells occupy distinct nonzero columns. Thus they
are a potential one-label three-black support for every edge containing
\(r\). Reflecting horizontally gives the negative offsets as well.
Consequently, for every such edge,
\[
 |A_e|\ge 2d_r.
 \tag{4}
\]
The excluded square factor \(u=v\) would require both sea rows in one
column and is correctly omitted.

This argument uses the definition of the full influence set. It does
not assert that all configurations (2) survive the final sea assignment,
or that each one individually causes a collision. The positional proof
deliberately excludes every three-black tilted rectangle.

## Sum over all labels

For \(e=\{a,b\}\), (4) gives
\[
 |A_e|\ge2\max(d_a,d_b)\ge d_a+d_b.
 \tag{5}
\]
Every row belongs to exactly \(n\) parity edges, so
\[
 \sum_e |A_e|\ge n\sum_{r=1}^h d_r.
 \tag{6}
\]
Since \(r-1\mid N_r\), one has
\[
 d_r\ge\tau(r-1)-1
 \qquad (2\le r\le h-1).
\]
Writing \(H=h-2\), the elementary divisor-sum identity gives
\[
 \begin{aligned}
 \sum_{r=1}^h d_r
 &\ge \sum_{s=1}^{H}\tau(s)-H\\
 &=\sum_{d=2}^{H}\left\lfloor\frac Hd\right\rfloor\\
 &\ge H\sum_{d=2}^{H}\frac1d-(H-1)
 =h\log h-O(h).
 \end{aligned}
 \tag{7}
\]
Disjoint translates contained in \(m\) columns have total cardinality
at most \(m\). Equations (6)--(7) prove (1).

## A squared-logarithm obstruction along an infinite sequence

When \(h-1=p\) is an odd prime, the same method gives the stronger bound
\[
 m\ge c h^2(\log h)^2
 \tag{8}
\]
for an absolute \(c>0\) and all sufficiently large such heights.

Indeed, for \(1\le a\le p-1\), the integers \(a,p-a\) are coprime, so
\[
 \tau(a(p-a))=\tau(a)\tau(p-a).
 \tag{9}
\]
Put \(X=\lfloor p^{1/4}\rfloor\). For each coprime pair \(d,e\le X\),
the Chinese remainder theorem gives at least \(p/(de)-2\) values
\(a\in[1,p-1]\) with \(d\mid a\) and \(e\mid p-a\). Therefore
\[
 \sum_{a=1}^{p-1}\tau(a)\tau(p-a)
 \ge p\!\sum_{\substack{d,e\le X\\(d,e)=1}}\frac1{de}-2X^2.
 \tag{10}
\]
The harmonic mass of coprime pairs is at least
\[
 \left(1-\sum_{k=2}^{\infty}k^{-2}\right)
       \left(\sum_{d\le X}\frac1d\right)^2
 \ge \frac{11}{36}\left(\sum_{d\le X}\frac1d\right)^2.
 \tag{11}
\]
For (11), bound the mass of pairs having a common divisor \(k\ge2\)
by a union bound. The mass of multiples of \(k\) in one coordinate is
\(k^{-1}H_{\lfloor X/k\rfloor}\le k^{-1}H_X\), and
\(\sum_{k\ge2}k^{-2}\le1/4+1/9+\int_3^\infty x^{-2}\,dx=25/36\).

Equations (9)--(11), after subtracting at most \(p-1\) square-divisor
exceptions, give
\[
 \sum_{r=1}^h d_r\ge c' h(\log h)^2.
 \tag{12}
\]
Equation (6) proves (8). Infinitely many odd primes give infinitely many
even heights. This is still a lower bound on the disjoint-influence
method, not on optimal blackouts.

## Consequence for the construction strategy

The existing \(O(h^2\log^{16}h)\) theorem remains valid. Its logarithmic
exponent is not optimal, but the full-disjoint-influence condition itself
already forces a growing factor.

A quadratic construction through this route must change at least one
structural requirement: allow compatible prescriptions to overlap, use
smaller selected blocking sets in place of the full influence sets, or
choose another sea layout. Improving a local-lemma constant or the divisor
moment estimate alone cannot remove the entire logarithm.
