# Audit of the weighted scale integral

9 November 2026. The passage from the uniform circle-scale mean to the primitive-direction weight is correct. The coefficient is \(1/3\) when both connector signs and all circle representations are included. Fixed orientation conventions multiply every phase by the same constant.

For \(U=k(a,b)\), with \(a,b>0\), the angle-independent vertical span is \(kb+|l|a\). Consequently
\[
 \sum_{l\ne0}(h-kb-|l|a)_+
 =\frac{(h-kb)_+^2}{a}+O(h).
\tag{1}
\]
The established bound for the number of \((U,V)\) pairs makes the total error \(O(h^3\log^3(2h))\). The geometric replacement of the actual span and the excluded degenerate representations have separate lower-order bounds in [mixed_four_leading_ratio_reduction.md](mixed_four_leading_ratio_reduction.md).

Write the expansion from [uniform_circle_scale_valuation.md](uniform_circle_scale_valuation.md) as
\[
 F_N(x)=A_Nx\log x+B_Nx+
 O_\eta\bigl(r_2(N)N^\eta x^{3/4}\log(2x)\bigr).
\tag{2}
\]
The Euler-product estimates there give
\[
 |B_N|\ll A_N(1+\log\log(3h))
\]
uniformly for \(N\le2h^2\).

For \(K=h/b\), partial summation yields
\[
 \begin{aligned}
 \sum_{k\le K}r_2(k^2N)(1-k/K)^2
 =K\left(\frac{A_N}{3}\log K
          +\frac{B_N}{3}-\frac{5A_N}{18}\right)
 +O_\eta\bigl(r_2(N)N^\eta K^{3/4}\log(2K)\bigr).
 \end{aligned}
\tag{3}
\]
The numerical constants follow from
\[
 \int_0^1(1-x)^2\,dx=\frac13,\qquad
 \int_0^1(1-x)^2(1+\log x)\,dx=-\frac5{18}.
\]
The bounded contribution near \(x=0\) is absorbed by the error in (3).

Multiplying (3) by \(h^2/a\) gives the leading direction weight
\[
 \frac{h^3}{3ab}A_{a^2+b^2}\log\frac hb.
\tag{4}
\]
The linear term contributes at most
\[
 C h^3(1+\log\log(3h))
 \sum_{\substack{a,b\le h\\(a,b)=1}}
 \frac{A_{a^2+b^2}}{ab}
 \ll h^3\log^3(2h)(1+\log\log(3h)).
\tag{5}
\]
The final inequality follows from the primitive divisor box bound, or directly from Section 2 of [primitive_parity_weight_equidistribution.md](primitive_parity_weight_equidistribution.md).

For every fixed \(\varepsilon>0\), the error in (3) is uniformly negligible when \(K\ge h^\varepsilon\), after choosing \(\eta\) sufficiently small. When \(K<h^\varepsilon\), every available scale is short. [mixed_short_scale_truncation.md](mixed_short_scale_truncation.md) bounds their total by
\[
 O(h^3\log^3(2h))+O(\varepsilon^2h^3\log^4(2h)).
\]
First let \(h\to\infty\), then let \(\varepsilon\to0\). This justifies (4) for the full leading vertical term. The same argument applies to each fixed scale-valuation category, using its exact two-adic partial-sum identity.

The linear term is lower order and cannot change the primitive parity weights or the phase ratios. This audit does not address full recurrent-component dominance.
