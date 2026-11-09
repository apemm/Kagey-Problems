# Short-scale truncation in the leading mixed count

9 November 2026. The scale-valuation theorem can be applied to the full
leading vertical contribution, after an elementary small-scale
truncation. This removes the short-scale qualification from that
specific use of
[uniform_circle_scale_valuation.md](uniform_circle_scale_valuation.md).

Put \(\Lambda=1+\log h\). In the usual mixed normalization
\(U=k(a,b)\), \(T=l(-b,a)\), let \(N_{\rm short}(h,\delta)\)
count all admissible geometries with \(k\le h^\delta\), before
any protected color restriction, per horizontal translation.

**Lemma.** Uniformly for \(0<\delta\le1/2\),
\[
N_{\rm short}(h,\delta)
\ll h^3\Lambda^3+\delta^2h^3\Lambda^4.
\tag{1}
\]
The implied constant is absolute. In particular, this contribution
can be made arbitrarily small at the \(h^3\log^4h\) scale by
first taking \(h\to\infty\) and then \(\delta\downarrow0\).

## 1. The count with a truncated scale

For each primitive \(a,b>0\), the number of connectors is at most
\(Ch/a\), the number of base translations at most \(h\), and the
circle count is \(r_2(k^2(a^2+b^2))\). Thus
\[
N_{\rm short}
\ll h^2\sum_{\substack{a,b\le h\\(a,b)=1}}\frac1a
 r_2(a^2+b^2)\,K_b\log(2K_b),
\qquad K_b=\min(h/b,h^\delta).
\tag{2}
\]
Signs and orientations cost a fixed factor. Equation (2) uses the
established inequality
\[
\sum_{k\le K}r_2(k^2N)\ll r_2(N)K\log(2K).
\]

On a dyadic box \(a\asymp A,b\asymp B\), the primitive quadratic
divisor estimate is
\[
\sum r_2(a^2+b^2)\ll AB\log(2\max(A,B)).
\tag{3}
\]
Split the \(B\)-boxes at \(h^{1-\delta}\), allowing a fixed
factor of overlap to absorb boxes meeting the split.

For \(B\le h^{1-\delta}\), use \(K_b\le h^\delta\).
The box contribution is at most
\[
C h^{2+\delta}B
 \log(2\max(A,B))\log(2h^\delta).
\]
Summing \(A\) gives \(O(\Lambda^2)\), and summing the dyadic
\(B\)'s gives \(O(h^{1-\delta})\). This range is
\(O(h^3\Lambda^3)\), uniformly in \(\delta\le1/2\).

For \(B>h^{1-\delta}\), use \(K_b\le Ch/B\).
The box contribution is at most
\[
C h^3\log(2\max(A,B))\log(2h/B).
\]
Again the sum over \(A\) is \(O(\Lambda^2)\). The remaining
dyadic sum is
\[
\sum_{B>h^{1-\delta}}\log(2h/B)
\ll1+\delta\log h+\delta^2(\log h)^2.
\]
It contributes \(O(h^3\Lambda^3+\delta^2h^3\Lambda^4)\),
which proves (1).

## 2. Use in the very vertical range

Consider primitive directions \(a/b\le1/\log h\).
The span comparison in
[mixed_four_leading_ratio_reduction.md](mixed_four_leading_ratio_reduction.md)
replaces the vertical translation weight by
\[
(h-kb-|l|a)_+
\]
with error \(O(h^3\log^2h)\). The generic circle-orbit weight
is then independent of its angle.

Summing over \(l\ne0\) gives
\[
\sum_{l\ne0}(h-kb-|l|a)_+
=\frac{(h-kb)_+^2}{a}+O(h).
\tag{4}
\]
The total \(O(h)\) error over \((U,V)\) is
\(O(h^3\Lambda^3)\), by
[uniform_connector_base_residues.md](uniform_connector_base_residues.md).

For fixed \(a,b\), the remaining scale weight is therefore
the bounded-variation function \((h-kb)_+^2/a\).
On dyadic \(k\)-intervals with \(k\ge h^\delta\), the scale
valuation theorem applies uniformly, with \(N=a^2+b^2\le2h^2\).
Its absolute error, relative to the corresponding arithmetic
main-term majorant, is uniformly \(o(1)\). Summing the majorant
costs at most \(O(h^3\Lambda^4)\). Intervals whose weight has
very small integral can be controlled by the same absolute
partial-summation error, using the full dyadic interval as a
majorant. No lower bound on each individual weighted interval
is required.

Equation (1) handles the discarded intervals. Letting
\(\delta\downarrow0\) proves that, before the known integrality
filter, the three scale categories have leading weights
\(1/2,1/4,1/4\) throughout the very vertical contribution,
with error \(o(h^3\log^4h)\). For an opposite-parity primitive
direction and odd \(k\), exactly half the generic orbit has
the correct coordinate parities for \((U\pm V)/2\) to be integral.
That explicit factor remains part of the phase table.

The connector and base-residue theorem supplies the other two
uniform residue averages. Thus the remaining unproved inputs
for the candidate protected mixed ratios are the leading primitive
parity-type weights and the nearly horizontal short-arc contribution.

