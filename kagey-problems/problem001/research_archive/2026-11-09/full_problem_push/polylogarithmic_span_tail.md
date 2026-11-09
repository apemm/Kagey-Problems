# Polylogarithmic span truncation and a smaller optimizer neighborhood

9 November 2026. An elementary aspect-ratio truncation gives an explicit error smaller than the leading pressure. It uses exact protected obstruction means, so it requires no convergence rate in the angular or primitive-weight asymptotics.

Put
\[
 \Lambda=1+\log h,\qquad \ell_h=1+\log\Lambda.
\]

**Span-tail theorem.** The minimal protected four/six support family has a subfamily of support span at most
\[
 H_h=C h^2/\Lambda^6
\tag{1}
\]
whose omitted per-column probability mean is at most
\[
 C\Lambda^2\ell_h^2/h.
\tag{2}
\]
All constants are absolute and uniform over the finitely many protected laws.

Consequently every balanced partition maximizing full sea entropy differs from a translated or complemented quadratic row law in at most
\[
 O((1+\log\log h)^2)
\tag{3}
\]
rows. This sharpens the \(o(\log^2h)\) neighborhood in the global leading theorem; it does not prove exact quadratic optimality.

## 1. Truncate primitive aspect ratios

First take a parameter \(2\le P\le h^{1/4}\). Retain only tilted rectangles whose primitive direction satisfies
\[
 P/h\le a/b\le h/P.
\tag{4}
\]
For a rectangle with side vectors \(k(a,b)\) and \(l(-b,a)\), vertical containment gives
\[
 kb+|l|a\le h.
\]
Its horizontal span is at most
\[
 ka+|l|b\le h(a/b+b/a)\le2h^2/P.
\tag{5}
\]
For a mixed side/diagonal witness, the alternate diagonal has the same norm as \(k(a,b)\), hence its horizontal component is at most \(ka+h\). The complete mixed witness therefore also has span \(O(h^2/P)\) under (4). Two retained rectangles sharing a corner have the same span bound up to a constant.

The discarded direction harmonic sum satisfies
\[
 \sum_{\substack{a,b\le h\\b/a>h/P}}\frac1{ab}
 \le
 \sum_{a\le P}\frac1a
       \left(1+\log(P/a)\right)
 \le C\log^2(2P),
\tag{6}
\]
and the opposite aspect range has the same bound.

At a prescribed corner, the number of omitted rectangles is at most
\(Ch^2\log^2(2P)\), whereas the full degree is \(Ch^2\Lambda^2\).
For six-cell supports, pair one omitted rectangle with any second rectangle, sum the h possible rows of the common corner, and multiply by \(O(h^{-6})\). The omitted six-cell mean is at most
\[
 C\Lambda^2\log^2(2P)/h.
\tag{7}
\]

## 2. Mixed four-cell tails

The arithmetic inputs from
[the crossing-weight proof](protected_crossing_bulk_weight.md) are
\[
 r_2(k^2N)\le r_2(N)R(k),\qquad
 \sum_{k\le K}R(k)\le CK\log(2K),
\tag{8}
\]
for \(N=a^2+b^2\), and the uniform fixed-coordinate estimate
\[
 F_a(B):=\sum_{\substack{b\le B\\(a,b)=1}}r_2(a^2+b^2)
 \le C\{B\log(2(a+B))+a+B\}.
\tag{9}
\]
The latter follows from the divisor hyperbola and the average number of roots of minus one.

For each primitive a,b, there are at most h vertical translates and \(h/a\) connector scales. Summing the side scales \(k\le h/b\) by (8), the mixed tail count per horizontal translation is at most
\[
 Ch^3
 \sum_{\rm tail}\frac{r_2(a^2+b^2)}{ab}
                  \log(2h/b).
\tag{10}
\]

In the nearly vertical tail \(b/a>h/P\), one has \(a\le P\) and \(b>ha/P\). Here b is larger than a. On each dyadic b-interval, (9) bounds the sum of r_2 by \(CB\Lambda\). Summing these intervals with the displayed logarithmic weight gives
\[
 \sum_{b>ha/P}\frac{r_2(a^2+b^2)}b\log(2h/b)
 \le C\Lambda\log^2(2P/a).
\]
Therefore
\[
 \sum_{\substack{a,b\le h\\b/a>h/P}}
 \frac{r_2(a^2+b^2)}{ab}\log(2h/b)
 \le C\Lambda\log^3(2P).
\tag{11}
\]

In the nearly horizontal tail \(a/b>h/P\), one has \(b\le P\) and \(a>hb/P\). Use (9) with the coordinates interchanged, and bound \(\log(2h/b)\le C\Lambda\). This gives
\[
 \sum_{\substack{a,b\le h\\a/b>h/P}}
 \frac{r_2(a^2+b^2)}{ab}\log(2h/b)
 \le C\Lambda^2
       \sum_{b\le P}\frac{\log(2P/b)}b
 \le C\Lambda^2\log^2(2P).
\tag{12}
\]
Since \(\log(2P)\le C\Lambda\), (11) is no larger than the bound in (12), up to constants.

Multiplying (10) by \(O(h^{-4})\), the omitted mixed-four mean is at most
\[
 C\Lambda^2\log^2(2P)/h.
\tag{13}
\]
This upper bound includes alternate axis rectangles and does not use circle-angle equidistribution.

Omit all hidden-four and horizontal mixed-four supports as well. Their full means are \(O(\Lambda^2/h)\), so they fit within (13). Vertical shared-side patterns are impossible in a one-black-per-column sea. Restrict the remaining supports to the original minimal-event family; every omitted minimal event is charged to an omitted geometric witness.

Taking \(P=\Lambda^6\) proves (1)--(2).

## 3. Protected quadratic reference shifts cost only O(1/h)

All four matched quadratic column laws are horizontal translates of one another, so they have exactly the same growth at a fixed row law. Complementing the row law only relabels the phase.

The two quadratic row laws \(q(y)\) and \(q(y)+y=q(y+1)\) correspond, after a vertical translation, to the same law on the two height-h strips
\([1,h]\) and \([2,h+1]\). Their common strip is \([2,h]\).

Restricting a protected model to the common strip deletes at most one allowed letter from each column. Add the corresponding singleton exclusion events to the protected local-lemma family. Their probabilities are \(O(1/h)\), and the joint criterion holds because the protected incident mass tends to zero. The conditional product bound shows that this restriction costs at most
\[
 \exp(Cm/h)
\tag{14}
\]
in the length-m count.

On the common alphabet, use the deduplicated canonical positive-support
family: hidden rectangles, mixed four-cell supports, and genuine
one-common-corner six-cell supports. Discard certificates containing a
support already forbidden in both models. In particular, a same-side
or same-diagonal collision whose complementary black cells form a
common hidden rectangle adds no new event; its potentially many
displayed-pair witnesses are not counted.

The two remaining families can differ only through canonical mixed
or six-cell witnesses involving row 1 or row h+1. A mixed support
determines its witness after a bounded choice of pairings, and a
six-cell support does so after a bounded choice of its two triples.
The uniform fixed-row four/six counts therefore give total additional
event weight \(O_\eta(mh^{-2+\eta})\), for any fixed eta>0.
The union of these deduplicated families is a protected local-lemma
family on the common alphabet. The conditional product estimate
compares the two avoidance probabilities at this cost, without
assuming that minimal-event status stays unchanged.

Explicitly, let \(Z_i\) be either full-strip count, \(Z_i'\) its
common-alphabet restriction, and \(Z_U\) the count avoiding the union
of the two restricted event families. For i=1,2,
\[
 e^{-Cm/h}Z_i\le Z_i'\le Z_i,\qquad
 e^{-C_\eta mh^{-2+\eta}}Z_i'\le Z_U\le Z_i'.
\]
Consequently
\[
 Z_1\le e^{Cm/h+C_\eta mh^{-2+\eta}}Z_2,
 \qquad
 Z_2\le e^{Cm/h+C_\eta mh^{-2+\eta}}Z_1.
\]
Taking, for example, eta=1/2 makes both bounds \(e^{O(m/h)}\).

Taking growth rates,
\[
 |\log r_{\rm Q,shift}(h)-\log r_{\rm Q}(h)|
 \le C/h.
\tag{15}
\]
This includes the slightly unbalanced quadratic reference at heights \(h\equiv2\pmod4\). The same argument handles finite-end conventions with fixed-height constants.

## 4. Quantitative near-protected pressure

Repeat the full witness-guard proof with the span cutoff (1), rather than a fixed power \(h^{2-\delta}\). Its per-cut loss is at most
\[
 H_h\cdot C\Lambda^4/h
       =O(h/\Lambda^2)=o(h),
\tag{16}
\]
so the witness deficit still absorbs it. The omitted mean is now the explicit quantity (2). Suen's \(O_\eta(h^{-2+\eta})\) error is smaller than (2).

For an actual balanced partition at row distance \(r=o(h)\) from a quadratic protected reference, with r tending to infinity, the joint row-root proof therefore gives
\[
 \log\rho_c(h)
 \le \log r_{\rm Q,ref}(h)
       -a(r/h)\log^2(h/r)
       +C\Lambda^2\ell_h^2/h.
\tag{17}
\]
The unchanged-row bulk deletion, product-alphabet errors, guard/end losses, and phase-profile activity are treated as in
[global_sea_leading_pressure.md](global_sea_leading_pressure.md).
The retained row penalty absorbs the \(O(rh^{-2+\eta})\) bulk loss and O(1/h) product error. No angular asymptotic error appears, since (17) compares with the exact protected mean and exact protected avoidance expansion.

A maximizing partition is already o(h)-close to a quadratic law by the global theorem. Its entropy is at least \(r_{\rm Q}(h)\). Equations (15)--(17) imply
\[
 r\log^2(h/r)\le C\Lambda^2\ell_h^2.
\tag{18}
\]
The left side increases for \(r<h/e^2\). If \(r\ge K\ell_h^2\), it is at least
\((K+o(1))\Lambda^2\ell_h^2\). Taking K sufficiently large contradicts (18). Bounded r already satisfies (3). This proves the stated optimizer neighborhood.

## 5. An exact-reference remainder bound

The same argument gives
\[
 0\le R_h-r_{\rm Q}(h)
 \le C(\log h)^2(1+\log\log h)^2.
\tag{19}
\]
For unbounded optimizer distance, drop the negative term in (17) and
use (15). For bounded distance, omit the auxiliary row roots; the
discarded fixed-row bulk has weight \(O(h^{-2+\eta})\), which is smaller
than (2). In either case the logarithmic excess is at most
\(C\Lambda^2\ell_h^2/h\). Since both growth rates are asymptotic to h/2,
exponentiating gives (19).

Both the fixed-height liminf and limsup exponential rates of maximum
blackout counts lie between \(r_{\rm Q}\) and \(R_h\), as proved in the
global counting corollary. They satisfy the same upper remainder
bound. The canonical quadratic component also lies in this interval.

Equation (19) compares with the exact protected growth rate, not just
its leading expansion. It requires no convergence rate for the
arithmetic coefficient \(d_{\rm Q}\).

The complete argument passed
[independent review](polylog_span_tail_independent_audit.md), including
the exact-reference remainder bound.

