# Uniform connector and base residues at the leading mixed scale

9 November 2026. Two residue-distribution hypotheses from
[mixed_four_leading_ratio_reduction.md](mixed_four_leading_ratio_reduction.md)
follow from bounded variation and the established divisor upper bounds.
This note does not address the primitive-direction parity weights or
the short arcs in nearly horizontal directions.

Use the normalization
\[
U=k(a,b),\qquad T=l(-b,a),\qquad |V|=|U|,
\]
with \((a,b)=1\), \(a>0\), \(b\ne0\), \(k>0\), \(l\ne0\).
The common pair is \(0,U\); the black cells are
\[
T,\quad T+U,\quad (U+V)/2,\quad (U-V)/2.
\]
Retain integral, nondegenerate configurations with distinct black
columns. Horizontal \(U\) is lower order and is omitted here.

**Theorem.** Choose any subset of the admissible pairs \((U,V)\),
independently of \(l\) and the vertical base translation \(y\).
This subset can impose primitive parity types, scale valuations,
angular ranges, or fixed generic circle-orbit roles.
Let \(N(h)\) count the resulting in-strip mixed geometries per
horizontal translation, and let \(N_{r,s}(h)\) impose
\(l\equiv r\pmod4\), \(y\equiv s\pmod4\). Then, uniformly in the subset,
\[
N_{r,s}(h)=\frac1{16}N(h)+O(h^3(1+\log h)^3).
\tag{1}
\]
The error is \(o(h^3\log^4h)\). It is an absolute leading-scale
statement; if the chosen subset is lower order, no relative
equidistribution claim is implied.

## 1. Translation in the strip

Fix \(U,V\), and let \(s(l)\) be the vertical span of the six
points. The exact number of vertical translations into
\(\{0,\ldots,h-1\}\) is
\[
w(l)=(h-s(l))_+.
\]
For any residue \(s\), the corresponding translation count is
\[
w(l)/4+O(1).
\tag{2}
\]
This is true even when \(w(l)=0\).

The total error in (2), summed over all triples \((U,V,l)\),
is \(O(h^2(1+\log h)^4)\). Indeed the proof of the mixed upper
bound gives this immediately on removing its final factor \(h\)
for vertical translations:
\[
\sum_{a,b}\frac ha
 \sum_{k\le h/|b|}r_2(k^2(a^2+b^2))
 \ll h^2(1+\log h)^4.
\tag{3}
\]
Restricting the pairs \((U,V)\) can only decrease this bound.

## 2. Connector residues

For a fixed integral pair \(U,V\), the vertical coordinates other
than the translated side \(T,T+U\) form a fixed interval. The latter
side's vertical interval translates by \(al\). The span of their
union is convex and piecewise linear in \(l\). Therefore \(w(l)\)
is supported on one interval, is unimodal there, and has total
variation at most \(2h\).

Sampling a bounded-variation sequence on one residue class modulo
four gives
\[
\sum_{l\equiv r\ (4)}w(l)
=\frac14\sum_l w(l)+O(h).
\tag{4}
\]
For example, group consecutive terms in blocks of four and bound
the difference from their average by the variation in each block.

The condition \(l\ne0\) removes one term. Each equality between a
black column of \(T,T+U\) and a black column of
\((U+V)/2,(U-V)/2\) determines at most one \(l\), since \(b\ne0\).
There are only constantly many such equalities. Removing these
terms changes each side of (4) by \(O(h)\).
Pairs \((U,V)\) whose own two diagonal columns coincide are omitted
before this calculation. Thus (4) holds for the full admissibility
filter.

## 3. The summed connector error loses one logarithm

By the sum-of-two-squares scale bound already proved in
[mixed_four_logarithmic_lower_bound.md](mixed_four_logarithmic_lower_bound.md),
\[
\begin{aligned}
\#\{(U,V)\}
&\le C\sum_{\substack{a,|b|\le h\\(a,b)=1}}
 \sum_{k\le h/|b|}r_2(k^2(a^2+b^2))\\
&\le Ch\sum_{\substack{a,b\le h\\(a,b)=1}}
 \frac{r_2(a^2+b^2)}b\log(2h/b).
\end{aligned}
\tag{5}
\]
The second line absorbs the sign of \(b\) and orientation choices.

On a dyadic box \(a\asymp A,b\asymp B\), the primitive quadratic
divisor estimate gives
\[
\sum r_2(a^2+b^2)\ll AB\log(2\max(A,B)).
\]
Thus the last sum in (5), on this box, is at most
\[
C A\log(2\max(A,B))\log(2h/B).
\]
Summing \(A\) first gives \(O(h\log(2h))\); summing the
remaining dyadic \(B\)-weights gives \(O((1+\log h)^2)\).
Consequently
\[
\#\{(U,V)\}\ll h^2(1+\log h)^3.
\tag{6}
\]
The \(O(h)\) error per pair in (4) therefore totals
\(O(h^3(1+\log h)^3)\). Combining (2)--(6) proves (1).

## 4. Consequence for the remaining ratio calculation

Connector and vertical-base residues can now be averaged uniformly
in every leading mixed-support calculation, with a lower-order
error. The scale-valuation weights on polynomially long boxes are
proved separately in
[uniform_circle_scale_valuation.md](uniform_circle_scale_valuation.md).

The remaining candidate-ratio hypotheses concern the leading
primitive parity-type weights, the handling of short scale ranges,
and the contribution of circle arcs in nearly horizontal directions.
Equation (1) alone does not prove the ratios \(13/16\) and \(5/4\).

