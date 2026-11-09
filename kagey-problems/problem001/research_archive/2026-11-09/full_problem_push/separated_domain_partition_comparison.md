# Joint row and wall pressure for separated protected domains

9 November 2026. Row-defect roots and marked domain-wall roots satisfy one conditional local-lemma estimate. Their combined absolute pressure avoids any protected interface factor. In this subclass, a competitive row partition has distance \(O(\log^2h)\) from a protected law.

This is a restricted-language theorem. Near-maximal partition rigidity alone does not supply the quantitative phase-error bound used here.

## 1. Statement and conventions

Let \(c_0\) be a protected row law, and let \(\mathcal X(c_0)\) be its four matched protected column laws. Its classes have sizes \(h/2+O(1)\); exact balance of \(c_0\) is not required. Let c be balanced, and put
\[
 E=\{y:c(y)\ne c_0(y)\},\qquad r=|E|,\qquad
 \Lambda=1+\log h,\qquad P_h(r)=\frac rh\log^2\frac hr.
\]
Write \(\rho_0=\max_{X\in\mathcal X(c_0)}\rho_{c_0,X}(h)\).

A domain profile \(t^0\) concatenates restrictions of laws in \(\mathcal X(c_0)\), using global column coordinates. Merge adjacent domains with the same law. Every domain has length at least \(D_h=C_0h\), for a sufficiently large absolute \(C_0\). The first and last domain may be shorter; they affect only a fixed-height endpoint factor.

The actual phase is \(t=t^0+1_S\), with \(|S|\le\sigma m+O_h(1)\), where \(0\le\sigma\le1/2\). Let \(\rho_{\mathrm{dom},\sigma}(c)\) be the exponential growth rate of the union over these profiles and error sets. Use the normalized fixed-final-F sea language.

**Joint-pressure theorem.** There are absolute \(R_0,\delta_0,a,C>0\) such that, for sufficiently large h and \(R_0\le r\le\delta_0h\),
\[
 \log\rho_{\mathrm{dom},\sigma}(c)
 \le \log\lceil h/2\rceil-aP_h(r)
       +H_2(\sigma)+C\sigma+Ce^{-ah}.
\tag{1}
\]
Consequently, suitable absolute \(K,b>0\) give
\[
 \rho_{\mathrm{dom},\sigma}(c)<\rho_0
\]
whenever
\[
 K\Lambda^2\le r\le\delta_0h,\qquad
 \sigma\le b\,\frac{P_h(r)}{\log(e/P_h(r))}.
\tag{2}
\]
Errors may cluster arbitrarily. Exact separated domains therefore have residual row distance \(O(\log^2h)\). The full joint-family proof passed [independent review](separated_domain_pressure_independent_audit.md).

## 2. Row roots inside each domain

Use the [adaptive primitive-direction family](adaptive_row_root_pressure.md), with
\[
 q=r/h,\qquad R=\lfloor q^{-1/2}\rfloor.
\]
Each root is a changed completion row in E; all three prescribed black rows avoid E. Its rectangle lies within one domain. Remove any root whose black or completion column belongs to S.

The total unmarked row-root mean is at least
\[
 a_1P_h(r)m-C_1\sqrt{rh}(J+1)
       -C_2|S|qR\log R,
\tag{3}
\]
where J is the number of domain walls.

The endpoint term follows from the span first moment \(O(rR)\) per domain. It remains valid for a short domain, even when the resulting lower bound is negative. The S loss follows from the fixed-cell bound at black columns and the \(O(q\log^2R)\) mass at a completion column.

Uniformly in the actual profile, one prescribed black cell belongs to at most
\[
 O(rhR\log R)
\tag{4}
\]
row roots, while two prescribed cells belong to \(O(r)\). Three prescribed noncollinear right-triangle corners determine their unique completion. Deduplication removes identical events.

Every changed row is eligible for a fixed fraction of columns under a nonconstant matched phase. Under a constant phase, at least \((r-1)/2\ge r/3\) rows are eligible when \(r\ge3\). Thus the mean in (3) is uniform over all domain labels, including slightly unbalanced quadratic references.

## 3. Marked wall roots

The [local wall construction](protected_domain_wall_pressure.md) supplies singleton-rival events at each wall with:

- all four corners within \(C_3h\) columns of the wall;
- three black corners on one side and the completion on the other;
- unmarked mean at least \(a_2h\log h\);
- one-cell and two-cell counts \(O(h^2\log h)\) and \(O(h)\).

Its primitive directions are comparable and its side scales are multiples of four. Distinct matched phases disagree on a fixed positive fraction of completion residues.

Delete every event whose rectangle has a row in E. Prescribing one corner row fixes the vertical translate; the remaining direction, scale, and wall-translate count is \(O(h^3\log h)\). Hence the deleted probability mass is at most \(Cr\log h\) per wall. For sufficiently small \(\delta_0\), a fixed fraction of the mean survives.

Delete also events whose black or completion column is in S. At a prescribed column, the probability mass is \(O(\log h)\). For completion columns, fix the horizontal translate in the same shape count.

Choose \(C_0>4C_3\), so wall neighborhoods are disjoint. Mark each retained wall event independently with probability
\[
 \theta=b_0/\log h,
\]
where the absolute constant \(b_0>0\) is small. The total marked mean is then at least
\[
 a_3hJ-C_4|S|-O_h(1).
\tag{5}
\]
Marks at distinct events are independent. Wall events whose geometries avoid E have completion rows outside E.

## 4. One conditional estimate for both families

Every row event is unmarked; every wall event includes its independent mark. Each underlying event prescribes three row choices, with probability \(\Theta(h^{-3})\).

After fixing either type of event, compatible row-root neighbors sharing one or two assignments have total probability at most
\[
 O(rhR\log R)\,O(h^{-2})+
 O(r)\,O(h^{-1})
 =O(qR\log R+q).
\tag{6}
\]
Compatible marked wall neighbors contribute at most
\[
 \theta O(h^2\log h)\,O(h^{-2})+
 \theta O(h)\,O(h^{-1})
 =O(b_0).
\tag{7}
\]
The raw incident sums obey the same bounds. The wall-neighborhood separation prevents an additional factor from the number of walls.

No distinct cross-family events share all three black assignments. The three black corners determine one completion, whereas a row-root completion is in E and a wall-root completion is outside E. Identical within-family events have already been deduplicated.

Choose \(b_0\) first so that (7) is small. Then choose \(\delta_0\) so that (6) is small, using
\[
 qR\log R=O(\sqrt q\log(1/q)).
\]
The joint unthinned/marked family satisfies the local-lemma criterion and the exact conditional lower bound
\[
 \Pr(A\mid\text{avoid any earlier listed events})\ge\Pr(A)/2.
\tag{8}
\]
This is the same conditional argument used in the row and wall proofs; the mixed overlap estimates (6)--(7) verify its additional hypotheses.

Avoiding the original unmarked forbidden configurations implies avoiding the joint family. Sequentially applying (8) therefore bounds the count by the product-space size times an exponential loss proportional to the sum of (3) and (5).

Now reduce \(\delta_0\) further, if necessary, so that
\[
 C_1\sqrt{\delta_0}\le a_3/2.
\tag{9}
\]
Then the row-root endpoint loss per domain is absorbed by half the marked wall mean:
\[
 C_1\sqrt{rh}\,J\le a_3hJ/2.
\]
The first and last endpoints cost only \(O_h(1)\).

Since \(qR\log R\) is bounded absolutely, the result for each fixed profile is
\[
 Z_c(t)\le C_h\lceil h/2\rceil^m
 \exp[-a_4P_h(r)m-a_5hJ+C_5|S|].
\tag{10}
\]
No protected bulk partition function was retained, restored, or compared in this argument. In particular, there is no \(O(h\log^2h)\) interface factor to pay.

## 5. Sum the phase descriptions

There are at most \(4^{J+1}\binom{m-1}{J}\) domain descriptions with J walls. Overcounting short-domain descriptions is harmless when summing their upper weights. Thus
\[
 \sum_J4^{J+1}\binom{m-1}{J}e^{-a_5hJ}
 \le4(1+4e^{-a_5h})^m.
\]
For \(0\le\sigma\le1/2\), summing \(e^{C_5|S|}\) over \(|S|\le\sigma m+O_h(1)\) has exponential rate at most
\[
 \exp[H_2(\sigma)+C_5\sigma].
\]
Equation (1) follows.

For \(\delta_0<e^{-2}\), \(q\log^2(1/q)\) increases on \(0<q\le\delta_0\). Hence
\[
 r\ge K\Lambda^2
 \quad\Longrightarrow\quad
 P_h(r)\ge cK\Lambda^4/h
\]
for sufficiently large h. The protected lower bound
\[
 \rho_0\ge h/2-C_6\Lambda^4
\]
gives
\[
 \log\lceil h/2\rceil-\log\rho_0\le C_7\Lambda^4/h.
\]
Choose K large enough to absorb this term.

Finally, \(H_2(\sigma)\le\sigma\log(e/\sigma)\) shows that the error allowance in (2), with small b, gives
\[
 H_2(\sigma)+C\sigma\le aP_h(r)/2.
\]
The exponentially small wall-description term is negligible. This proves (2).

## 6. Scope

This theorem compares a quantitatively specified domain-and-error language with the best protected reference entropy. It does not show that every word in a near-maximal component has the required representation and error density. It does not prove boundary-component dominance within a fixed partition.

The joint-family argument improves the weaker interpolation comparison, which lost a factor \(\log^2h\) in the row penalty. The improvement is possible because the adaptive row-root endpoint loss is \(O(\sqrt{rh})\), which the actual marked wall roots absorb when \(r/h\) is small.

