# A fractional-moment refinement of the filled threshold

9 November 2026. The complete compatible-profile construction gives
the explicit bound
\[
 m_0(h)\ll h^2(1+\log h)^{16/5}.
 \tag{1}
\]
This note records an independent refinement of
compatible_profile_threshold.md. It retains the same filled profiles,
finite collars, exceptional-label treatment, and positional local lemma.
Only the moment exponent used in Hölder's inequality changes.

The slightly sharper numerical exponent obtainable from this argument
is not essential. In particular, (1) has an absolute implied constant
and does not need an additional arbitrary positive exponent.

Write \(Q=\lfloor h^2/4\rfloor\), \(\Lambda=1+\log h\), and
\(\ell=1+\log\log(3h)\). Keep the row weight
\[
 v(e)=1+\sum_{r\in e,\ s\in\{L,F,H\}}\tau(|r-s|).
\]

## 1. Geometry moments at an arbitrary fixed exponent

Fix \(1<p<2\). Put
\[
 \alpha(p)=2^p-1,\qquad \beta(p)=3^p-1.
\]
The same geometry-role proof as in the fourth-logarithm note gives
\[
 \sum_{J\ni e,\ |J|=k}G_J^p
 \ll_p Q^{k-1}
       \bigl(\Lambda^{\beta(p)}\ell^{C_p}
                   +v(e)^p\Lambda^{\alpha(p)}\bigr),
 \qquad k=2,3,4.
 \tag{2}
\]

For completeness, the uniform two-linear-factor moment comes from
the same [Henriot upper bound](https://arxiv.org/pdf/1102.1643)
and corrected exceptional-prime parameter used in
sharper_polylogarithmic_threshold.md. Distinct primitive factors give
the exponent \(2(2^p-1)\), while a repeated factor gives \(3^p-1\).
The latter is at least the former for \(p\ge1\).
One fixed factor is extracted using \(v(e)\); the varying factor
has exponent \(2^p-1\).

The exceptional geometry roles do not depend on the choice \(p=2\).
A long sea side leaves only \(O(h)\) possible partner labels. A
horizontal fixed diagonal loses one free row parameter. In both cases
the fixed \(p\)-th power of the uniform subpower divisor bound is
absorbed by that parameter loss. A varying square difference is the
repeated-factor moment already included in \(\beta(p)\).

Likewise, for every fixed \(s>1\),
\[
 \sum_e v(e)^s\ll_s Q\Lambda^{2^s-1}.
 \tag{3}
\]
Only finitely many fixed moments near \(s=5/2\) will be used. The
single-form source theorem has no restriction requiring \(s\) to
be near two.

## 2. Class widths from Hölder's inequality

Set
\[
 \theta=1-\frac1p,\qquad q=\frac1\theta=\frac p{p-1}.
\]
In a dyadic class with \(n\) labels and upper weight \(w\), Hölder
and (2) imply
\[
 \sum_{\substack{J\ni e,\ |J|=k\\J\text{ in the class}}}G_J
 \ll_p n^{\theta(k-1)}Q^{(k-1)/p}
 \left(\Lambda^{\beta(p)/p}\ell^{C_p}
                  +w\Lambda^{\alpha(p)/p}\right).
 \tag{4}
\]
Thus it is enough to choose
\[
 N=C_p n^\theta Q^{1/p}
 \left(\Lambda^{\beta(p)/p}\ell^{C_p}
                  +w\Lambda^{\alpha(p)/p}\right)
 \tag{5}
\]
period-zero slots for the class.

Indeed, a fixed geometry involving \(k\) center variables has
probability at most \(N^{-(k-1)}\). For \(k=2\), (4)--(5) make
the total incident weight small by choosing \(C_p\) large. For
\(k=3,4\), the additional powers of the bracket in (5) only help.
Coincidence events are controlled because
\(n^\theta Q^{1/p}\ge n\). The same local lemma therefore produces
a complete valid class block.

## 3. Sum the dyadic classes

The first moment \(\sum_e v(e)\ll Q\Lambda\) gives
\[
 \sum_j n_j^\theta
 \ll_p Q^\theta(1+\log\Lambda)^{1-\theta}.
 \tag{6}
\]
For \(w_j\le\Lambda^2\), use Hölder across the
\(O(1+\log\Lambda)\) classes. For \(w_j>\Lambda^2\), use
\(n_j\ll Q\Lambda/w_j\) and sum a geometric series.

For the weighted sum, choose fixed small \(d>0\) and put
\[
 A_\pm=\sum_j n_jw_j^{q\pm d}.
\]
Splitting at a threshold \(W\), the two geometric tails give
\[
 \begin{aligned}
 \sum_j w_jn_j^\theta
 &\ll_{p,d}A_-^\theta W^{\theta d}
                 +A_+^\theta W^{-\theta d}\\
 &\ll_{p,d}(A_-A_+)^{\theta/2}.
 \end{aligned}
 \tag{7}
\]
Using (3), and then taking \(d\) sufficiently small, proves
\[
 \sum_jw_jn_j^\theta
 \ll_{p,\eta}Q^\theta
      \Lambda^{\theta(2^q-1)+\eta}
 \qquad(\eta>0).
 \tag{8}
\]
There is no extra factor counting the dyadic classes in (7).

Summing (5) now yields
\[
 \sum_jN_j
 \ll_{p,\eta}Q\left[
 \Lambda^{A(p)}\ell^{C_p}
 +\Lambda^{B(p)+\eta}\right],
 \tag{9}
\]
where
\[
 A(p)=\frac{3^p-1}{p},\qquad
 B(p)=\frac{2^p-1}{p}
       +\left(1-\frac1p\right)
           \left(2^{p/(p-1)}-1\right).
 \tag{10}
\]
The harmless power of \(1+\log\Lambda\) from (6) is included in
\(\ell^{C_p}\).

## 4. A simple explicit exponent

Take \(p=5/3\), so \(\theta=2/5\) and \(q=5/2\). Then
\[
 A(5/3)=\frac35(3^{5/3}-1)<3.15,
\]
and
\[
 B(5/3)=\frac35(2^{5/3}-1)
             +\frac25(4\sqrt2-1)
       <3.168.
\]
For example, the elementary bounds
\(3^{5/3}<6.25\), \(2^{5/3}<3.175\), and
\(4\sqrt2<5.657\) suffice for these strict inequalities.
Choose \(\eta>0\) small enough that both exponents in (9) stay
strictly below \(16/5=3.2\). Every fixed power of \(\ell\) is then
absorbed by the remaining positive logarithmic margin.

The \(O(h^2\log h)\) class collars and the \(O(h^2)\)
exceptional-label construction are smaller than (1). The finite
profile family contributes only an absolute factor. Complete
boundary tails still give every larger width.

This argument improves the logarithmic exponent without changing
the profile or the geometry that is forbidden. It does not remove
the logarithmic loss or establish an absolute quadratic threshold.
