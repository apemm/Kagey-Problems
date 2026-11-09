# A threshold with logarithmic exponent arbitrarily close to eight

9 November 2026. This note refines polylogarithmic_threshold.md by retaining
the divisor function of each actual product of two linear forms. It also
uses moments on both sides of the second moment when summing the
arithmetic classes.

**Theorem.** For every \(\varepsilon>0\), there is a constant
\(C_\varepsilon\) such that
\[
 m_0(h)\le C_\varepsilon h^2(1+\log h)^{8+\varepsilon}.
 \tag{1}
\]
Consequently \(f(h,m)=m+\lfloor h^2/4\rfloor\) throughout this width
range. The construction and its extensions to every larger width are
the complete positional construction from near_quadratic_threshold.md.
This refinement does not prove an absolute quadratic threshold.

The arithmetic, geometric exceptions, and moment summation have passed
independent review; see sharper_polylogarithmic_threshold_independent_audit.md.

## 1. A uniform moment bound for two affine factors

Write \(\Lambda=1+\log h\) and
\(\ell=1+\log\log(3h)\). Fix the number of variables and a bound on all
linear coefficients. The constant terms below can have magnitude \(O(h)\).
For \(s\) in a sufficiently small fixed neighborhood of two, put
\[
 \beta(s)=3^s-1.
\]
If \(L_1,L_2\) are nonconstant integer affine forms on an integer box
of side \(h\), then
\[
 \frac1{h^d}\sum_{\mathbf n\in[1,h]^d}
       \tau_+\bigl(L_1(\mathbf n)L_2(\mathbf n)\bigr)^s
 \le C_s\Lambda^{\beta(s)}\ell^{C_s}.
 \tag{2}
\]
Here \(\tau_+(0)=1\), and otherwise \(\tau_+(n)=\tau(|n|)\).
The constants are uniform in the constant terms of the affine forms.

The external input is the discriminant-uniform upper bound of
[Henriot, *Nair--Tenenbaum bounds uniform with respect to the
discriminant*](https://arxiv.org/pdf/1102.1643), Corollary 2, with the
corrections in the
[2014 erratum](https://doi.org/10.1017/S0305004114000280).
The corrected exceptional-prime parameter includes the leading
coefficient of the squarefree part of the polynomial. Only the upper
bound is used.

Here is the specialization and its parameter check. First suppose both
forms depend on one common variable. Fix all other variables and write
them as \(an+u,bn+v\), with nonzero bounded \(a,b\).
Their contents divide \(a,b\), so removing contents costs only a fixed
factor in the divisor moment. Translate \(1\le n\le h\) to
\(h<n'\le2h\). The product polynomial has height \(O(h^2)\).
Henriot's size condition holds, for example with its parameter
\(\delta=1/3\), for all sufficiently large \(h\).
The growth and submultiplicativity hypotheses hold for
\(F(n)=\tau(n)^s\), since
\(\tau(mn)\le\tau(m)\tau(n)\) and \(\tau(n)=O_\eta(n^\eta)\).
Possible polynomial zeros contribute \(O(1)\) and are treated separately.

If the two primitive factors are distinct, the ordinary-prime Euler
factor in that bound is
\[
 1+\frac{2(2^s-1)}p+O_s(p^{-2}).
 \tag{3}
\]
The exceptional primes divide a bounded coefficient times \(av-bu\).
The theorem bounds their extra factor by
\(\prod_{p\mid D}(1+1/p)^{C_s}\), where
\(0<|D|\le C h^2\). This is \(O_s(\ell^{C_s})\).
For example, split the prime divisors at \(\log(3h)\), use the prime
harmonic sum below this cutoff, and use the product bound on the
remaining prime divisors.
Thus the moment is
\[
 O_s\bigl(h\Lambda^{\,2(2^s-1)}\ell^{C_s}\bigr).
 \tag{4}
\]
If the primitive factors agree up to sign, their product is a fixed
bounded multiple of the square of one primitive linear form. The
corresponding function at a prime is \(\tau(p^2)^s=3^s\), and the
Euler factor gives
\[
 O_s(h\Lambda^{\,3^s-1}).
 \tag{5}
\]
There is no growing content in this repeated-factor case.
Near \(s=2\), \(2(2^s-1)<3^s-1\), so (4)--(5) prove (2)
after summing the fixed other variables.

If no variable occurs in both forms, their variable supports are
disjoint. Apply the single-linear-form bound separately to the two
factors. The product moment has exponent \(2(2^s-1)\), again at most
\(\beta(s)\). This exhausts the possibilities.

Parity restrictions on the row box only reduce the unrestricted sum.
Since the number of permitted labels is comparable to \(h^2\), the
same normalized estimate applies to the full parity edge family.

## 2. Row weights without the fourth-power loss

Use one of the canonical backgrounds \(\{1,g\}\) from the preceding
construction, with \(g=h,h-1\), or \(h-3\), and reflect coordinates for
the reflected backgrounds. Let \(\mathcal L\) be the same fixed finite
family of nonconstant affine forms in the two endpoints \(a,b\)
used in polylogarithmic_threshold.md. Enlarge it by a fixed amount if
necessary to include every factor in a row-product calculation.
Define
\[
 w(e)=1+
 \sum_{L_1,L_2\in\mathcal L}
       \tau_+\bigl(L_1(e)L_2(e)\bigr)
 +\mathbf1_{\min(a,b)\le7}\tau(g-1).
 \tag{6}
\]
Repeated forms are included. In particular, \(w(e)\) bounds every
\(\tau_+(L(e)^2)\) and every \(\tau_+(L(e))\).
Also \(w(e)=O(h)\), since every product has magnitude \(O(h^2)\)
and \(\tau(n)\le2\sqrt n\). Thus there are only \(O(\log h)\)
nonempty dyadic classes, as required for the collar count.

The private influence set obeys
\[
 |A_e|+1\le Cw(e).
 \tag{7}
\]
Indeed its translated geometries are counted by
\(\tau(L_1L_2)\) or \(\tau(L^2)\) before the earlier proof replaced
these quantities by sums of \(\tau(L)^2\). Retain the original
quantities instead. The two height-only exceptions still contribute
only \(O(\tau(g-1))\) on the indicated \(O(h)\) labels.

Write \(Q=\lfloor h^2/4\rfloor\). By (2) and the inequality for a fixed
finite sum,
\[
 \sum_{e\in F}w(e)^s
 \le C_s Q\Lambda^{\beta(s)}\ell^{C_s}
 \qquad(s\text{ near }2).
 \tag{8}
\]
For the exceptional term, use
\(\tau(g-1)^s\le C_s h^{1/2}\), uniformly for \(s\) in a compact
neighborhood of two, by the elementary subpower divisor bound.
Its contribution on \(O(h)\) labels is \(O_s(h^{3/2})\), absorbed
in (8). In particular,
\[
 \sum_e w(e)^2\le C Q\Lambda^8\ell^C.
 \tag{9}
\]

## 3. The squared geometry-count estimate

Let \(G_J\) count translated relative geometries using exactly the
label set \(J\), as in the preceding construction. Influence-overlap
events are excluded from \(G_J\). For \(k=2,3,4\) and a fixed label
\(e\),
\[
 \sum_{\substack{J\ni e\\|J|=k}}G_J^2
 \le C Q^{k-1} w(e)^2\Lambda^8\ell^C.
 \tag{10}
\]

Keep the exact product divisor counts in each of the finitely many
role assignments. If both factors vary with the other labels, (2)
with \(s=2\) applies to that row box. If one factor is fixed at
\(c(e)\), use
\(\tau(c(e)L)^2\le\tau(c(e))^2\tau(L)^2\);
the varying factor has mean \(O(\Lambda^3)\), and
\(\tau(c(e))\le Cw(e)\). If both factors are fixed, their product
divisor count is one of the terms covered by (6).
These statements also cover a repeated varying factor.

The exceptional mixed support with its black side on both sea rows
still has exactly two labels and imposes
\(r+t=1+g+2j\), \(1\le j\le h-g\le3\).
For fixed \(e\), it contributes
\[
 O\bigl(h\tau(g-1)^2\bigr)=O(Q),
 \tag{11}
\]
using \(\tau(g-1)\le2\sqrt h\), exactly as in the original proof.
The classification there shows that no other height-only factor
survives with a full set of free label parameters.
Thus (10) retains the complete geometric event family.

## 4. Placement in one arithmetic class

In a dyadic class of \(n\) labels with \(w/2<w(e)\le w\), the
same Cauchy--Schwarz calculation now gives
\[
 \sum_{\substack{J\ni e,\ J\text{ in class}\\|J|=k}}G_J
 \le C(nQ)^{(k-1)/2}w\Lambda^4\ell^C.
 \tag{12}
\]
Choose the independent center domain length
\[
 N=\left\lceil C_0\bigl(nw^2+
             \sqrt{nQ}\,w\Lambda^4\ell^C\bigr)\right\rceil.
 \tag{13}
\]
The influence-overlap and geometric event weights then have total
incident weight at most \(1/8\), for a sufficiently large absolute
\(C_0\), after increasing the fixed exponent of \(\ell\).
The product-form local lemma, private prescriptions, collars, and
complete forbidden-support proof are unchanged.

## 5. Sum the class widths with two nearby moments

The first terms of (13) sum to \(O(Q\Lambda^8\ell^C)\) by (9).
For the second terms, fix a small constant \(d>0\) and put
\[
 p=2-d,\qquad r=2+d.
\]
For each dyadic class, (8) gives
\[
 n_j\le C_d Q\ell^{C_d}
       \min\bigl(\Lambda^{\beta(p)}w_j^{-p},
                 \Lambda^{\beta(r)}w_j^{-r}\bigr).
 \tag{14}
\]
Harmless factors \(2^p,2^r\) from the class endpoints are included
in \(C_d\). The two bounds cross at
\[
 w=\Lambda^{(\beta(r)-\beta(p))/(r-p)}.
\]
Below this point the bound for \(w_j\sqrt{n_j}\) grows
geometrically with exponent \(d/2\); above it the bound decays
with the same exponent. Summing the two geometric series gives
\[
 \sum_j w_j\sqrt{n_j}
 \le C_d\sqrt Q\,\ell^{C_d}
       \Lambda^{(\beta(2-d)+\beta(2+d))/4}.
 \tag{15}
\]
This avoids a factor \(\sqrt{\log h}\) from counting the classes.

The total width from the second terms in (13) is therefore
\[
 O_d\left(
 Q\,\Lambda^{\,4+(\beta(2-d)+\beta(2+d))/4}\ell^{C_d}
 \right).
 \tag{16}
\]
Since
\[
 4+\frac{\beta(2-d)+\beta(2+d)}4
 =8+\frac92\bigl(\cosh(d\log3)-1\bigr),
 \tag{17}
\]
choose \(d=d(\varepsilon)>0\) so the excess in (17) is less than
\(\varepsilon/2\). The fixed power of \(\ell\) is at most
\(C_\varepsilon\Lambda^{\varepsilon/2}\).
The finitely many background families and the
\(O(h^2\log h)\) collar cost are absorbed in (1).

All double labels occur exactly once. The existing constant-tail
extension gives every greater width, completing the threshold claim.
