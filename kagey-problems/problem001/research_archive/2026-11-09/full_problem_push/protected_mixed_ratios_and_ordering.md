# Protected mixed ratios and the ordering of phase entropies

9 November 2026. The weighted-distribution inputs to the mixed-support
comparison are now proved. This establishes the ordering of the three
protected phase entropies at sufficiently large height. It does not
identify the dominant recurrent component of a full sea graph.

Let O denote a constant ordinary row-parity phase, C an ordinary
checkerboard phase, and Q a matched quadratic phase. Translates and
complements have the same leading formulas. Let
\(\mu_{4,\mathrm{mix},X}(h)\) be the mean per column of distinct
minimal mixed four-cell supports in phase \(X\), with each column
chosen uniformly from its allowed row class.

**Theorem.** As \(h\to\infty\),
\[
\frac{\mu_{4,\mathrm{mix},\mathrm Q}}
     {\mu_{4,\mathrm{mix},\mathrm O}}\longrightarrow\frac{13}{16},
\qquad
\frac{\mu_{4,\mathrm{mix},\mathrm C}}
     {\mu_{4,\mathrm{mix},\mathrm O}}\longrightarrow\frac54.
\tag{1}
\]
In particular, for all sufficiently large \(h\),
\[
r_{\mathrm Q}(h)>r_{\mathrm O}(h)>r_{\mathrm C}(h),
\tag{2}
\]
where \(r_X\) is the entropy of the protected-phase language.
Both differences in (2) have order \((\log h)^4\).

## 1. Reduce the geometry to one weighted primitive sum

Use
\[
U=k(a,b),\qquad T=l(-b,a),\qquad |V|=|U|,
\]
with primitive \(a,b>0\), \(k>0\), and \(l\ne0\).
The common white pair is \(0,U\), and the four required black cells are
\[
T,\quad T+U,\quad (U+V)/2,\quad (U-V)/2.
\]

The reductions already proved give the following absolute errors,
before applying any color restriction.

* Balanced directions \(1/\log h\le a/b\le\log h\) contribute
  \(o(h^3\log^4h)\).
* Nearly horizontal directions \(a/b>\log h\) contribute
  \(o(h^3\log^4h)\), by
  [the averaged circle-angle theorem](averaged_circle_angles.md).
* In the remaining nearly vertical range, replacing the full vertical
  span by \(kb+|l|a\) costs \(O(h^3\log^2h)\).
* Exceptional circle orbits and repeated black columns cost
  \(O(h^3\log^2h)\).
* Connector and vertical-base residues modulo four have uniform
  leading weights, with error \(O(h^3\log^3h)\), by
  [the residue theorem](uniform_connector_base_residues.md).
* Scales \(k\le h^\epsilon\) contribute at most
  \(O(h^3\log^3h)+O(\epsilon^2h^3\log^4h)\), with an absolute
  constant, by
  [short-scale truncation](mixed_short_scale_truncation.md).

All estimates also hold for colored subfamilies, by positivity.
Horizontal translation is averaged over the fixed phase period.

Summing both nonzero connector signs gives
\[
\sum_{l\ne0}(h-kb-|l|a)_+
 =\frac{(h-kb)_+^2}{a}+O(h).
\tag{3}
\]
The total error is \(O(h^3\log^3h)\).

The uniform circle-scale theorem writes
\[
F_N(K)=\sum_{k\le K}r_2(k^2N)
      =A_NK\log K+B_NK+E_N(K),
\]
where \(N=a^2+b^2\),
\[
|B_N|\ll A_N(1+\log\log(3h)),
\]
and the error is uniformly negligible on polynomially long scales.
For \(K=h/b\), partial summation gives
\[
\sum_{k\le K}r_2(k^2N)(1-k/K)^2
 =K\left(\frac{A_N}{3}\log K+\frac{B_N}{3}
                            -\frac{5A_N}{18}\right)
   +\text{controlled error}.
\tag{4}
\]
Thus the direction's leading geometric weight, before fixed global
orientation factors, is
\[
\frac{h^3}{3ab}A_{a^2+b^2}\log(h/b).
\tag{5}
\]
The sum of the linear terms is
\(O(h^3\log^3h(1+\log\log(3h)))\), since
\(\sum_{\mathrm{primitive}\ a,b\le h}A_{a^2+b^2}/(ab)
 =O(\log^3h)\).
Apply the uniform scale estimate above \(h^\epsilon\), use the
short-scale bound below it, then let \(\epsilon\downarrow0\).

The remaining direction sum is therefore precisely the sum treated in
[primitive_parity_weight_equidistribution.md](primitive_parity_weight_equidistribution.md).
That theorem proves that OO, OE, and EO each carry one third of its
leading weight in the range \(a/b\le1/\log h\).
Its total is \(\Theta(\log^4h)\).

## 2. Average the exact residue table

The scale categories \(\nu_2(k)=0,1,\ge2\) have leading weights
\(1/2,1/4,1/4\), uniformly within each primitive type. This follows
from the exact doubling identity for \(r_2(k^2N)\), the uniform mean,
and the short-scale argument.

In the nearly vertical range the geometric weight is independent
of the angle of a generic eight-member circle orbit. For odd scale
and an opposite-parity primitive type, exactly half its members
make \((U\pm V)/2\) integral. Include this factor before averaging.

The exact table in
[phase_local_densities.md](phase_local_densities.md), averaged over
scale categories, connector residues, base residues, and generic
orbit members, then gives:
\[
\begin{array}{c|ccc}
\text{primitive type}&\mathrm O&\mathrm C&\mathrm Q\\ \hline
\mathrm{OO}&1/8&3/8&7/32\\
\mathrm{OE}&3/16&1/8&3/32\\
\mathrm{EO}&3/16&1/8&3/32.
\end{array}
\tag{6}
\]
Averaging the three rows with equal leading weight yields
\[
\mathrm O:\frac16,\qquad
\mathrm C:\frac5{24},\qquad
\mathrm Q:\frac{13}{96}.
\tag{7}
\]

These are counts of distinct minimal supports after the same geometric
normalization. The equal-length side/diagonal pairing and its roles
are unique outside the discarded degeneracies, as proved in
[mixed_four_logarithmic_lower_bound.md](mixed_four_logarithmic_lower_bound.md).
Thus no phase-dependent multiplicity remains.

Each admissible four-cell support has probability
\[
(2/h)^4(1+O(1/h))
\]
uniformly across the finitely many protected phases, including heights
where the two row classes differ by one or two rows.
Consequently the geometric ratios (7) give the probability ratios (1).

The proof of (1) does not require the common absolute coefficient
of the weighted primitive sum to have a limit. That coefficient is now
evaluated in [primitive_weight_absolute_constant.md](primitive_weight_absolute_constant.md).
The resulting explicit pressures and growth expansions are collected in
[protected_phase_explicit_constants.md](protected_phase_explicit_constants.md).

## 3. Compare the protected entropies

Put
\[
L_h=\frac{(\log h)^4}{h},\qquad
M_h=\frac{\mu_{4,\mathrm{mix},\mathrm O}(h)}{L_h}.
\]
The logarithmic-order theorem gives absolute bounds
\(0<c\le M_h\le C<\infty\). The subsequent absolute evaluation strengthens
this to \(M_h\to32\mathcal P/(9\pi^4)\), where
\(\mathcal P=\prod_{p\equiv1\ (4)}(p-1)(p^2+4p+1)/(p+1)^3\).

The known six-cell coefficients are
\[
c_{\mathrm O}=\frac{45}{\pi^4},\qquad
c_{\mathrm C}=\frac{324}{5\pi^4},\qquad
c_{\mathrm Q}=\frac{144}{5\pi^4}.
\]
Hidden four-cell supports contribute \(O(\log^2h/h)=o(L_h)\).
The audited avoidance expansion therefore becomes
\[
\begin{aligned}
\log r_{\mathrm O}
 &=\bar\ell_{\mathrm O}
   -\left(M_h+\frac{45}{\pi^4}\right)L_h+o(L_h),\\
\log r_{\mathrm C}
 &=\bar\ell_{\mathrm C}
   -\left(\frac54M_h+\frac{324}{5\pi^4}\right)L_h+o(L_h),\\
\log r_{\mathrm Q}
 &=\bar\ell_{\mathrm Q}
   -\left(\frac{13}{16}M_h+\frac{144}{5\pi^4}\right)L_h+o(L_h).
\end{aligned}
\tag{8}
\]
Here \(\bar\ell_X\) is the period average of the logarithm of the
allowed-row count. Every such quantity is \(\log(h/2)+O(1/h)\);
hence their differences are \(o(L_h)\).

Subtracting gives
\[
\log r_{\mathrm Q}-\log r_{\mathrm O}
 =\left(\frac3{16}M_h+\frac{81}{5\pi^4}\right)L_h+o(L_h)>0,
\tag{9}
\]
and
\[
\log r_{\mathrm O}-\log r_{\mathrm C}
 =\left(\frac14M_h+\frac{99}{5\pi^4}\right)L_h+o(L_h)>0.
\tag{10}
\]
Since all three entropies are asymptotic to \(h/2\), their
corresponding additive gaps are \(\Theta((\log h)^4)\).

The finite set of translated or complemented protected laws has
the same leading coefficients. Thus the ordering survives taking
the best phase of each type, subject to any balancing requirement
on the associated row partition.

## 4. What the comparison does not prove

Equation (2) compares protected languages. A full ordinary-parity
sea component contains words with nonprotected phase patterns,
so its entropy may exceed \(r_{\mathrm O}\).
The result does not prove that the quadratic partition dominates
all balanced partitions, or that its boundary component is globally
dominant. Those remain separate questions.

The absolute leading mixed coefficient is now evaluated separately.
The [explicit-constants theorem](protected_phase_explicit_constants.md)
replaces \(M_h\) by its limiting Euler product and gives
\(r_X=h/2-(d_X/2)(\log h)^4+o((\log h)^4)\). The unrestricted-component
qualification remains unchanged.

The proof chain has independent audits for the scale and residue
averages, short-scale truncation, angular estimate, primitive parity
weights, six-cell constants, and avoidance expansion. This synthesis
must be read with those exact hypotheses.

