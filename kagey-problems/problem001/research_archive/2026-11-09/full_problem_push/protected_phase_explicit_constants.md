# Explicit leading constants for protected phases

9 November 2026. The leading obstruction pressures and growth constants are explicit for the ordinary constant-parity phase O, ordinary checkerboard phase C, and matched quadratic phase Q. The synthesis, including its global normalization, passed [independent review](protected_ordering_independent_audit.md). This theorem concerns their protected languages, not unrestricted recurrent components.

Define
\[
 \mathcal P=
 \prod_{p\equiv1\ (4)}
 \frac{(p-1)(p^2+4p+1)}{(p+1)^3}
 =\prod_{p\equiv1\ (4)}
 \left(1-\frac{6p+2}{(p+1)^3}\right).
\tag{1}
\]
Every factor is positive, and the product converges to a positive number because the omitted part of each factor is \(O(p^{-2})\).

Let \(\mu_{4,\mathrm{mix},X}(h)\) be the mean per column of distinct minimal mixed four-cell supports under uniform independent choices from the allowed rows of phase \(X\). Let \(\mu_X(h)\) include all minimal forbidden supports. Write \(r_X(h)\) for the exponential growth rate of the valid words obeying that protected law.

**Theorem.** As \(h\to\infty\),
\[
 \mu_{4,\mathrm{mix},X}(h)
 \sim m_X\frac{(\log h)^4}{h},\qquad
 \mu_X(h)\sim d_X\frac{(\log h)^4}{h},
\tag{2}
\]
where

| Phase \(X\) | Mixed coefficient \(m_X\) | Total pressure coefficient \(d_X\) |
|---|---:|---:|
| O | \(32\mathcal P/(9\pi^4)\) | \((45+32\mathcal P/9)/\pi^4\) |
| C | \(40\mathcal P/(9\pi^4)\) | \((324/5+40\mathcal P/9)/\pi^4\) |
| Q | \(26\mathcal P/(9\pi^4)\) | \((144/5+26\mathcal P/9)/\pi^4\) |

Consequently,
\[
 \boxed{\displaystyle
 r_X(h)=\frac h2-\frac{d_X}{2}(\log h)^4
                   +o((\log h)^4).}
\tag{3}
\]
In particular,
\[
 \begin{aligned}
 r_{\mathrm Q}-r_{\mathrm O}
 &\sim\frac{81/10+\mathcal P/3}{\pi^4}(\log h)^4,\\
 r_{\mathrm O}-r_{\mathrm C}
 &\sim\frac{99/10+4\mathcal P/9}{\pi^4}(\log h)^4.
 \end{aligned}
\tag{4}
\]
The same leading coefficients apply to the finitely many translated or complemented protected laws, including the balanced representatives when a balanced row partition is required.

Certified numerical intervals are recorded in
[protected_entropy_constant_intervals.json](protected_entropy_constant_intervals.json),
with the reproducible checker
[certify_protected_entropy_constants.py](certify_protected_entropy_constants.py).
The additive coefficients \(d_X/2\) are approximately 0.2454402 for O,
0.3506873 for C, and 0.1595753 for Q.

## 1. The absolute primitive weight

For each primitive parity type \(T\in\{\mathrm{OO},\mathrm{OE},\mathrm{EO}\}\), [primitive_weight_absolute_constant.md](primitive_weight_absolute_constant.md) proves
\[
 \sum_{\substack{1\le b\le h,\ 1\le a\le b/\log h\\
                   (a,b)=1,\ (a,b)\text{ of type }T}}
 \frac{A_{a^2+b^2}}{ab}\log(h/b)
 \sim\frac{4\mathcal P}{3\pi^4}(\log h)^4.
\tag{5}
\]
Here \(A_N\) is the leading coefficient of the scale sum \(\sum_{k\le K}r_2(k^2N)\). The proof and normalization passed [independent review](primitive_parity_weight_independent_audit.md).

The nearly horizontal and balanced direction ranges are lower order. The [averaged angle theorem](averaged_circle_angles.md) and its [audit](averaged_circle_angles_independent_audit.md) supply the nontrivial horizontal estimate. In the vertical range, the geometric span is independent of the chosen circle representation at leading order.

## 2. Global normalization of the mixed count

Use the common-pair description
\[
 U=k(a,b),\qquad T=l(-b,a),\qquad |V|=|U|,
\]
with black cells
\[
 T,\quad T+U,\quad (U+V)/2,\quad (U-V)/2.
\]
The side vector is oriented with positive horizontal component, and the diagonal vector is also oriented with positive horizontal component. Outside the discarded degeneracies, the black support determines its equal-length pairing and the side/diagonal roles uniquely.

For a positive primitive pair \(a,b\), both connector signs give
\[
 \sum_{l\ne0}(h-kb-|l|a)_+
 =\frac{(h-kb)_+^2}{a}+O(h).
\]
The weighted scale integral then supplies
\[
 \frac{h^3}{3ab}A_{a^2+b^2}\log(h/b)
\tag{6}
\]
as its leading geometric weight. The scale-linear term is only
\(O(h^3\log^3h(1+\log\log h))\) after summation. This passage has a separate [normalization audit](mixed_scale_weight_independent_audit.md).

There are two signs of the vertical component of the oriented side vector, giving a factor two. Restricting a generic circle representation to positive horizontal diagonal component gives a factor one half. These factors cancel. Both connector signs have already been included in (6). Therefore the formal leading geometry, before integrality and protected color conditions, is
\[
 \frac{h^3}{3}\sum_T W_T(h,1/\log h)
 \sim\frac{4\mathcal P}{3\pi^4}h^3(\log h)^4.
\tag{7}
\]
Horizontal translation is averaged over the phase period. There is no additional quotient by a reflection or an unordered-pair factor: the oriented side/diagonal description already counts each mixed support once.

The [exact phase table](phase_local_densities.md), averaged using the proved scale, connector, base, and primitive-type distributions, gives the fractions
\[
 \mathrm O:\frac16,\qquad
 \mathrm C:\frac5{24},\qquad
 \mathrm Q:\frac{13}{96}.
\tag{8}
\]
These include the integrality loss for odd scales of opposite-parity primitive directions. The residue averaging has an [independent audit](mixed_residue_average_independent_audit.md); [short-scale truncation](mixed_short_scale_truncation.md) removes the restriction to polynomially long scale ranges.

Each admissible four-cell support has probability
\((2/h)^4(1+O(1/h))\). Multiplying (7) by (8) and by this probability gives
\[
 (m_{\mathrm O},m_{\mathrm C},m_{\mathrm Q})
 =\frac{\mathcal P}{9\pi^4}(32,40,26),
\]
as claimed. In particular, the mixed ratios are \(13/16\) for Q/O and \(5/4\) for C/O.

## 3. Total pressure and the growth expansion

The independently checked [six-cell coefficients](six_support_leading_pressure.md) are
\[
 \frac{45}{\pi^4},\qquad
 \frac{324}{5\pi^4},\qquad
 \frac{144}{5\pi^4}
\]
for O, C, and Q. Hidden four-cell supports have mean
\(O(\log^2h/h)\), so they do not contribute to the coefficient in (2). Adding the six-cell and mixed coefficients gives the displayed \(d_X\).

The [avoidance expansion](crossed_codegree_and_avoidance.md), with its [independent review](protected_phase_pressure_independent_audit.md), states
\[
 \log r_X(h)=\bar\ell_X(h)-\mu_X(h)
                       +O_\varepsilon(h^{-2+\varepsilon}),
\tag{9}
\]
where \(\bar\ell_X\) is the period average of the logarithm of the allowed-row count. For every protected law,
\(\bar\ell_X(h)=\log(h/2)+O(1/h)\).
Substituting (2) into (9) and exponentiating proves (3). Subtracting its coefficients gives (4).

## 4. Full components remain a separate comparison

A full ordinary or quadratic sea component contains words that do not obey a single protected law. Its growth rate can therefore exceed the corresponding \(r_X\). Equations (2)–(4) neither give an additive upper bound for those full components nor prove eventual dominance of the quadratic partition among all balanced partitions.

The theorem does determine the exact leading loss inside every protected phase. The remaining component comparison must control the contribution from phase defects and transitions, rather than an unknown protected-phase coefficient.
