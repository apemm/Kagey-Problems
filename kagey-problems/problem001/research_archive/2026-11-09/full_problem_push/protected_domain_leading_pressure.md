# Leading protected pressure survives long domains and dilute packets

9 November 2026. The sign of the exact interface free energy is not needed to compare the leading \(\log^4h/h\) pressure. Truncate only a small fraction of the bulk mean, so the remaining supports have span \(h^{2-\delta}\). Competitive wall densities then lose a negligible amount of that mean.

Fix a protected row law \(c_0\). Let \(\mathcal X(c_0)\) be its four matched protected column laws, and put
\[
 \rho_0(h)=\max_{X\in\mathcal X(c_0)}\rho_{c_0,X}(h),
 \qquad \Lambda=1+\log h.
\]
Let \(\mathcal D_h\) be the normalized fixed-final-F language of profiles consisting of protected domains of minimum length \(C_0h\), with the relatively dilute phase-error packets from
[domains with dilute packets](domains_with_dilute_packets.md).
The first and last domains may be shorter. Packets have widths at most \(h/(U_h\Lambda^2)\), and their expansions by \(U_h\Lambda^3\) times their widths are disjoint.

**Leading-pressure claim.** As \(h\to\infty\),
\[
 \log\rho(\mathcal D_h)=
 \log\rho_0(h)+o(\Lambda^4/h).
\tag{1}
\]
The same conclusion holds with no packets. The statement concerns this specified language, not the full sea shift or an arbitrary recurrent component. The complete proof passed [independent review](domains_packets_independent_audit.md).

## 1. Bulk events of shorter span retain the leading mean

Let \(\mu_X(h)\) be the per-column mean of the complete minimal four/six positive-support family in protected phase X. The audited avoidance expansion gives
\[
 \log\rho_{c_0,X}(h)
 =\bar\ell_X(h)-\mu_X(h)+O_\epsilon(h^{-2+\epsilon}),
\tag{2}
\]
where \(\bar\ell_X\) is the mean logarithm of the selected alphabet size. Uniformly over the finitely many protected laws,
\[
 \mu_X(h)=O(\Lambda^4/h).
\]

Fix \(0<\delta<1/2\). There is a subfamily with horizontal support span at most
\[
 H_\delta=Ch^{2-\delta}
\tag{3}
\]
and per-column mean \(\mu_X^{(\delta)}\) satisfying
\[
 0\le\mu_X-\mu_X^{(\delta)}
 \le C\delta\,\Lambda^4/h+o_\delta(\Lambda^4/h).
\tag{4}
\]

For six-cell supports, restrict both tilted rectangles to primitive directions
\[
 1\le a,b\le h^{1-\delta}.
\]
At a fixed common corner, the full rectangle degree is \(O(h^2\Lambda^2)\). The omitted degree is at most
\[
 Ch^2
 \sum_{\substack{a,b\le h\\\max(a,b)>h^{1-\delta}}}\frac1{ab}
 \le C\delta h^2\Lambda^2+Ch^2\Lambda.
\]
Thus omitted rectangle pairs have count
\(O(\delta h^4\Lambda^4+h^4\Lambda^3)\) per common-corner row.
Summing the h rows and multiplying by \(O(h^{-6})\) gives the contribution asserted in (4). Every retained rectangle has span \(O(h^{2-\delta})\), since its scale bounds are \(k\le h/b\), \(t\le h/a\).

For mixed four-cell supports, discard the balanced and nearly horizontal directions. Their mean is \(o(\Lambda^4/h)\), by
[the geometric reduction](mixed_four_leading_ratio_reduction.md) and
[the averaged angular estimate](averaged_circle_angles.md).
The remaining directions satisfy \(a/b<1/\log h\). Discard also \(k\le h^\delta\); the
[short-scale lemma](mixed_short_scale_truncation.md) costs at most
\[
 C\delta^2\Lambda^4/h+O(\Lambda^3/h).
\]
For every retained geometry, \(b\le h^{1-\delta}\) and \(a\le b\). Its side has horizontal length \(ka\le kb<h\), its alternate diagonal has length \(O(h)\), and its connector has horizontal length
\[
 |t|b\le hb/a\le h^{2-\delta}.
\]
This proves the span bound.

Hidden-four and horizontal mixed-four means are only \(O(\Lambda^2/h)\), so they may all be omitted. Restrict the resulting family to the original minimal events. An omitted minimal event is charged to an omitted geometric representation; the preceding counts are therefore valid upper bounds despite any multiplicity.

## 2. The short bulk inside domains

For a fixed domain description, retain only the truncated bulk supports lying within one domain and whose black columns avoid the phase-error set S. Events in different domains use disjoint variable sets.

A cut removes at most
\[
 C H_\delta\Lambda^4/h
\tag{5}
\]
mean. Indeed each normalized support has at most its span many translates crossing the cut, and all retained spans are at most \(H_\delta\). The period-four residue counts change only the absolute constant.

Deleting the required black columns in S loses at most
\[
 C|S|\Lambda^4/h.
\tag{6}
\]
The strong dependency graph and compatible-overlap bounds from
[the protected avoidance expansion](crossed_codegree_and_avoidance.md)
remain valid for this subfamily. Suen's inequality therefore gives the upper avoidance probability with exponent equal to minus its mean, plus \(O_\epsilon(mh^{-2+\epsilon})\). No bulk coefficient is lost.

If the domains have lengths \(n_i\) and laws \(X_i\), their old product-space logarithm is
\[
 \sum_i n_i\bar\ell_{X_i}+O((J+1)/h),
\]
where J is the number of walls. Flipping the selected alphabet at S changes this by at most \(C|S|/h\). These terms are smaller than (5)--(6).

## 3. Restore packet pressure without changing the bulk coefficient

Use the guard decomposition at distance \(H_*=hU_h\) from domain walls. Guard errors have total number at most
\[
 C hJ/\Lambda^3+O_h(1),
\tag{7}
\]
and all their descriptions cost \(\exp(G_hJ+O_h(1))\), where
\[
 G_h=O\left(\frac h{\Lambda^3}\log(eU_h\Lambda^3)\right)=o(h).
\tag{8}
\]

Active packet roots use primitive cutoff \(U_h/C\), so their geometries lie inside their domain and their mean is at least
\[
 cQ_h|S_{\rm active}|,\qquad Q_h=\log^2U_h.
\]
Their global raw and conditional counts are the established relatively dilute bounds.

List the retained truncated bulk first. Then apply the exact conditional lower-probability lemma to the marked active packet roots. Their mean is preserved by a fixed factor, even after conditioning on all that bulk. Thus the probability bound is
\[
 \exp[-\mu_{\rm retained}
       +O_\epsilon(mh^{-2+\epsilon})
       -cQ_h|S_{\rm active}|].
\tag{9}
\]
The packet term absorbs (6) and the alphabet-size cost at active errors because \(Q_h\gg\Lambda^4/h\).

Combining (2), (4)--(9), a fixed description satisfies an upper bound with logarithm
\[
 \begin{split}
 m\log\rho_0
 &+C\delta\,m\Lambda^4/h+o_\delta(m\Lambda^4/h)\\
 &+CJH_\delta\Lambda^4/h
 +CJ\Lambda
 -c'Q_h|S_{\rm active}|+O_h(1).
 \end{split}
\tag{10}
\]
The \(J\Lambda\) term bounds the bulk deletion at guard errors using (7).
Summing active packet descriptions costs only
\(\exp(m e^{-cQ_h})\), as in the packet activity estimate. Guard descriptions contribute (8).

## 4. Separate low and high wall densities

Set
\[
 \nu_h=A\Lambda^4/h^2,
\tag{11}
\]
where A is a sufficiently large absolute constant.

For \(J\le\nu_hm\), summing the at most
\(4^{J+1}\binom{m-1}{J}\) domain descriptions contributes
\(H_2(\nu_h)+\nu_h\log4=o(\Lambda^4/h)\).
Every additional term in (10) is lower order for fixed delta:
\[
 \nu_h H_\delta\Lambda^4/h
 =O(h^{-1-\delta}\Lambda^8)=o(\Lambda^4/h),
\]
\[
 \nu_h\Lambda=o(\Lambda^4/h),\qquad
 \nu_hG_h=o(\Lambda^4/h),\qquad
 e^{-cQ_h}=o(\Lambda^4/h).
\]
Consequently the low-wall class has logarithmic growth at most
\[
 \log\rho_0+C\delta\Lambda^4/h+o_\delta(\Lambda^4/h).
\tag{12}
\]

For \(J>\nu_hm\), use only the absolute joint wall/packet count. Guard-error losses and their description entropy are absorbed by the marked wall mean. Active-packet activities are summable. The resulting upper bound is
\[
 \log\lceil h/2\rceil-c h\nu_h+o(\Lambda^4/h)
\tag{13}
\]
after decreasing c. Here the wall-location entropy is harmless:
for every \(s\ge\nu_h\), \(H_2(s)+s\log4=O(\Lambda s)\ll hs\).

The protected lower bound \(\rho_0\ge h/2-C_0'\Lambda^4\) lets A be chosen so that (13) is strictly below \(\log\rho_0\).

## 5. Limit order and consequence

The language contains every pure protected phase, so its growth is at least \(\rho_0\). For every fixed delta, (12)--(13) give
\[
 0\le
 \limsup_{h\to\infty}
 \frac{\log\rho(\mathcal D_h)-\log\rho_0}{\Lambda^4/h}
 \le C\delta.
\]
Now let \(\delta\downarrow0\). This proves (1).

Thus a strict leading protected-pressure separation between two protected row models persists for their domain-and-dilute-packet languages. This consequence does not compare either model with its full sea shift. Arbitrary dense clusters and unrestricted phase profiles remain outside the theorem.

In particular, the now proved [protected ordering](protected_mixed_ratios_and_ordering.md) has
\[
 \log r_{\mathrm Q}(h)-\log r_{\mathrm O}(h)
 =\Theta(\Lambda^4/h),\qquad r_{\mathrm O}>r_{\mathrm C}.
\]
For ordinary row parity, \(\rho_0=r_{\mathrm O}\) to this leading precision. Equation (1) therefore shows that the quadratic protected phase has strictly larger entropy than the entire ordinary-parity domain-and-dilute-packet language, for sufficiently large h. This still does not compare it with the full ordinary-parity sea shift.

The argument also leaves the exact relative free energy of a long wall unresolved. It uses an absolute wall penalty only to identify the wall-density range relevant to the leading pressure.

