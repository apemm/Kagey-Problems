# Reductions for the leading mixed-support ratios

9 November 2026. The order \(h^3\log^4h\) is proved in [mixed_four_logarithmic_lower_bound.md](mixed_four_logarithmic_lower_bound.md). This note isolates easier geometric reductions from the remaining arithmetic comparison. No leading ratio is claimed.

Use the normalization
\[
 U=k(a,b),\quad T=l(-b,a),\quad |V|=|U|,
 \qquad (a,b)=1, a>0, b\ne0, k>0, l\ne0.
\]
The common pair is \(0,U\), and the required black cells are
\(T,T+U,(U+V)/2,(U-V)/2\). A horizontal common side has only \(O(h^3\log^2h)\) supports and can be omitted at the leading scale. Reflections let us discuss \(b>0\) in the bounds below.

## 1. Balanced directions are lower order

The contribution of directions satisfying
\[
 (\log h)^{-1}\le a/b\le\log h
\]
is
\[
 O(h^3\log^3h\log\log h)=o(h^3\log^4h).
\tag{1}
\]
Indeed the upper bound in the logarithmic-order note weights the primitive direction by
\[
 h^3\frac{r_2(a^2+b^2)}{ab}\log(2h/b).
\]
On one dyadic box its sum is \(O(h^3\log^2h)\), by the uniform primitive-box bound there. The balanced range meets only \(O(\log h\log\log h)\) dyadic boxes.

## 2. Very vertical directions have an angle-independent span

Assume \(0<a/b\le\delta\le1\). The side rectangle alone has vertical span
\[
 s_0=kb+|l|a.
\]
Its vertical interval contains \([0,kb]\). For any equal-norm V,
\[
 \frac{(|V_y|-kb)_+}{2}
 \le\frac{\sqrt{k^2(a^2+b^2)}-kb}{2}
 \le\frac{k a^2}{4b}.
\]
Thus the full six-point span s satisfies
\[
 0\le s-s_0\le\frac{k a^2}{2b}.
\tag{2}
\]
For the uncolored count, replacing the vertical translation weight \((h-s)_+\) by \((h-s_0)_+\) changes the total by at most
\[
 O(\delta^2 h^3\log^4h).
\tag{3}
\]
To prove this, there are \(O(h/a)\) possible l for a nonzero replacement weight. The error for fixed \((a,b,k)\), summed over l and V, is at most
\[
 C\frac ha\frac{k a^2}b\,r_2(k^2(a^2+b^2)).
\]
Using the k-mean bound from the logarithmic-order note and \(k\le h/b\), its sum over k is at most
\[
 C h^3\frac{r_2(a^2+b^2)}{ab}
       (a/b)^2\log(2h/b).
\]
Summing gives (3). In particular, \(\delta=1/\log h\) makes this an \(O(h^3\log^2h)\) geometric error.

This is a statement about uncolored geometric translation weights. Passing from it to exact colored residue averages additionally requires controlling the residue-class counting errors. The estimate does not, by itself, assert their asymptotic equidistribution.

## 3. Exceptional circle orbits are lower order

For each U, omit the orbit of U under sign changes and coordinate swaps, together with representations on an axis or on a diagonal line \(V_x=\pm V_y\). This discards only O(1) choices of V. The resulting loss is at most
\[
 C h\sum_{a,b\le h}\frac ha\frac hb
 =O(h^3\log^2h).
\tag{4}
\]
The same estimate covers repeated-black-column choices when there are only O(1) forbidden V for fixed U,T. Consequently generic eight-element circle orbits suffice at leading order. The phase table in [phase_local_densities.md](phase_local_densities.md) applies to those orbits.

## 4. A precise candidate, with its missing hypotheses

Suppose the leading weighted count has equal primitive parity-type weights for OO, OE, EO; scale valuations \(\nu_2(k)=0,1,\ge2\) have respective weights \(1/2,1/4,1/4\), independently of those types; connector and base-translation residues are uniform modulo four; and generic orbit members have equal geometric weights before integrality is imposed. Under these hypotheses, the residue table gives
\[
 \mathrm O:\frac16,\qquad
 \mathrm C:\frac5{24},\qquad
 \mathrm Q:\frac{13}{96}.
\tag{5}
\]
The integrality factor \(1/2\) for odd k and an opposite-parity primitive direction is included here. The corresponding candidate ratios are
\[
 \frac{\mu_{4,\mathrm{mix},\mathrm Q}}{\mu_{4,\mathrm{mix},\mathrm O}}
 \longrightarrow\frac{13}{16},
 \qquad
 \frac{\mu_{4,\mathrm{mix},\mathrm C}}{\mu_{4,\mathrm{mix},\mathrm O}}
 \longrightarrow\frac54.
\tag{6}
\]
Equation (5) is an exact calculation under the stated weighted-distribution hypotheses; those hypotheses are not proved here.

Two main issues remain. First, directions \(a/b>\log h\) restrict V to short arcs near the horizontal axis. Bounding them by all circle representations still gives the full logarithmic order, so a genuine average arc estimate is needed to prove that range negligible. Second, even in the vertical range where (2) removes angle dependence from the leading geometric weight, the divisor-weighted primitive directions, scale residues, and connector residues need an actual asymptotic equidistribution proof. Neither ordinary unweighted parity density nor the exact local table alone supplies it.

### Subsequent progress on the residue hypotheses

The scale weights \(1/2,1/4,1/4\) are now proved uniformly on
polynomially long scale intervals in
[uniform_circle_scale_valuation.md](uniform_circle_scale_valuation.md).
The proof gives an explicit Euler product for the mean coefficient
of \(r_2(k^2N)\), uniformly for polynomially bounded \(N\).

Connector and vertical-base residues are now uniformly distributed
at the leading scale, with absolute error \(O(h^3\log^3h)\), even
after selecting any set of \((U,V)\) pairs independently of those
two residues. See
[uniform_connector_base_residues.md](uniform_connector_base_residues.md).
Both results passed
[independent review](mixed_residue_average_independent_audit.md).

The short-scale qualification is removed by
[mixed_short_scale_truncation.md](mixed_short_scale_truncation.md).
The nearly horizontal range is now proved to be
\(o(h^3\log^4h)\) in
[averaged_circle_angles.md](averaged_circle_angles.md), with
[independent review](averaged_circle_angles_independent_audit.md).
That argument uses fixed angular Fourier modes averaged over the scale,
so it does not assume equidistribution on individual circles.

The leading primitive parity-type weights are the remaining input.
The candidate ratios (6) are still conditional on that one comparison.

If (6) were established, the already proved six-cell coefficients and avoidance expansion would imply that Q has larger protected-phase entropy than O and C for sufficiently large h. It would still not compare Q with the full ordinary-parity component: profiles with large weighted local defect density are not controlled by the current cluster estimates.
