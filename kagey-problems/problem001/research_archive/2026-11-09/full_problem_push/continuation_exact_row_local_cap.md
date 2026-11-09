# Continuation: exact row pressure under a fixed local phase-error cap

9 November 2026. The exact-reference comparison can absorb the entire adaptive phase-error language, rather than requiring a vanishing global error density. This gives a strict comparison for every nonzero small row perturbation of a quadratic law, provided its column phases stay locally near one matched law.

Let c_0 be a quadratic protected row law, possibly the slightly unbalanced translated law at an even height. Let c be balanced, and put
\[
 E=\{y:c(y)\ne c_0(y)\},\qquad 1\le r=|E|\le\delta_0h,
 \qquad P_h(r)=\frac rh\log^2\frac hr,
\]
Fix a matched quadratic column law X. In aligned h-column blocks \(I_i\), let
\[
 q_i=|S\cap I_i|,\qquad q_i\le\epsilon_0h,
\tag{1}
\]
where epsilon_0 is a sufficiently small absolute constant. Let \(Z_{c,S}(m)\) count valid words of actual phase \(X+1_S\), and let \(Z_{0,X}(m)\) be the exact protected reference count. All counts use the normalized fixed-final-F support language.

Here delta_0 is a sufficiently small absolute constant. **Theorem.** There are absolute \(a,b>0\) and a height threshold such that
\[
 Z_{c,S}(m)\le C_h Z_{0,X}(m)
 \exp\!\left[
 -aP_h(r)m
 -b\sum_iq_i\log^2(h/q_i)
 \right].
\tag{2}
\]
The constant \(C_h\) is independent of m and S. Empty-block summands are zero.

After summing all S satisfying (1),
\[
 \log\rho_{\rm cap}(c;X)
 \le \log r_{c_0,X}
       -a'P_h(r).
\tag{3}
\]
There is no extensive protected-bulk approximation error in (2)--(3).

For a slightly unbalanced quadratic reference, the exact reference-shift comparison is O(1/h) in logarithmic growth. Thus every class in (3) has smaller entropy than the balanced quadratic protected sea for large h. This includes a single changed row.

The theorem does not compare full arbitrary-phase sea shifts. A competing nonquadratic component must escape this fixed-cap phase language; the remaining issue is its transitions between different local laws.

## 1. The common old bulk

Use the deduplicated canonical protected support family: hidden four-cell, mixed four-cell, and genuine six-cell supports. Certificates containing an already common forbidden support may be discarded.

Retain only witnesses whose entire row set avoids E and whose required black columns avoid S. Call this family B_0. It remains forbidden under the actual partition. Under the reference product measure, the omitted mean is at most
\[
 C_\eta r m h^{-2+\eta}
   +C|S|\log^4h/h+O_h(1),
\tag{4}
\]
for any fixed eta>0. The first term counts changed rows in the entire witness, including common white corners; the second uses the sharp protected incident probability.

At columns outside S, the unchanged allowed rows coincide in the two models. Changed rows are invisible to B_0 and can be viewed as dummy letters. The two alphabet sizes differ by O(1), even when the reference has imbalance two. At columns in S, B_0 uses no variable at all.

Consequently the retained-bulk counts in the two product alphabets differ by at most \(\exp(Cm/h)\). Here is an exact justification. Relabel dummy letters to match them as far as possible, then add or delete the O(1) excess dummy letters per column. To delete one such letter, add its singleton exclusion event. Its probability is O(1/h), and it satisfies the joint local-lemma criterion with B_0, whose incident mass tends to zero. The conditional product bound costs at most \(\exp(Cm/h)\). Apply this comparison in both directions. At S the comparison is just the product of the alphabet-size ratios.

Thus no equality of old and new class sizes is assumed.

## 2. Row-root events

Use the truncated primitive row-root family from
[adaptive_row_root_pressure.md](adaptive_row_root_pressure.md), with
\(R=\lfloor\sqrt{h/r}\rfloor\).
Its completion lies in E and is eligible when its old row color equals X at that column. All other geometric rows avoid E. Retain roots whose completion and black columns avoid S.

Every changed row is eligible in half the columns of the period-four law X. Hence, before deleting S, the period-averaged mean is
\[
 \Theta(P_h(r)).
\tag{5}
\]
The deleted-row count is \(O(rhR\log R)\) per completion row, against \(\Theta(h^2\log^2R)\) initial choices. Its relative size is \(O(\sqrt{r/h}/\log(h/r))\), so a fixed positive fraction survives for small delta_0. The finite-end mean loss is \(O(rR)=O(\sqrt{rh})\).

Deleting a single error column removes at most \(CP_h(r)\) mean. This follows by translating the normalized rooted family: its period is bounded, its total mean per translation is \(O(P_h(r))\), and a witness has only a fixed number of required or completion columns. Therefore the retained row-root mean is at least
\[
 aP_h(r)m-CP_h(r)|S|-O(\sqrt{rh}).
\tag{6}
\]

Writing \(q=r/h\), the raw and compatible one-/two-cell extension sums of this family are bounded by
\[
 O\bigl(qR\log R+q\bigr)
 =O\bigl(\sqrt q\log(1/q)+q\bigr).
\tag{7}
\]
This tends to zero with delta_0, uniformly in the stated range. There is no one-row growing-class exception here: every matched quadratic phase is nonconstant, so every changed row is eligible in a fixed positive fraction of columns. The dummy-letter cost is also uniformly absorbed because \(\min_{1\le r\le\delta_0h}r\log^2(h/r)=\log^2h\) for large h.

## 3. Adaptive phase-root events

Use the density majorant and varying cutoff from
[adaptive_local_phase_sparsity.md](adaptive_local_phase_sparsity.md).
For q_i>0 define
\[
 Q_i=\max_j\min\!\left(q_j,h\left(\frac K{1+|i-j|}\right)^4\right),
 \qquad R_i=\lfloor c(h/Q_i)^{1/4}\rfloor.
\]
The phase-root completion lies in \(E^c\cap S\), in the old selected row class. Delete every geometry touching E in any row, and delete every geometry whose black columns meet S.

Deleting E loses only an O(r/h) fraction of the phase-root mean: for each direction/scale shape, the permitted vertical translations number Theta(h), and fixing any one corner row removes at most one translation. This estimate is uniform in R_i. Reduce delta_0 so that a fixed positive fraction survives.

The dyadic cutoff proof gives raw and compatible one-/two-cell masses
\[
 O(\epsilon_0^{1/4})+O(\epsilon_0^{3/4}),
\tag{8}
\]
and the weighted maximal inequality gives retained total mean at least
\[
 b\sum_iq_i\log^2(h/q_i).
\tag{9}
\]
All black assignments in these events lie outside E and outside S, so they have the same permitted geometric positions as the reference phase.

## 4. The two root families coexist without thinning

Three noncollinear right-angle corners determine their unique completion. A row-root completion belongs to E, and a phase-root completion belongs to \(E^c\). Hence distinct events from the two families cannot share all three assignments.

The one-/two-cell mixed conditional sums are bounded by (7)--(8), according to which family is being extended. Compatible protected-bulk extensions through a root's three prescribed assignments contribute \(O_\eta(h^{-1+\eta})\).

Choose epsilon_0 and delta_0 sufficiently small, then h large. The joint unthinned local-lemma criterion holds for B_0 and both root families. The conditional lower-probability lemma gives a fixed positive fraction of each root event's original probability after avoiding any earlier subfamily.

Avoid B_0 first, then both root families. Equations (6) and (9) give
\[
 \Pr(\hbox{avoid roots}\mid\hbox{avoid }B_0)
 \le C_h\exp\!\left[
 -aP_h(r)m+CP_h(r)|S|
 -b\sum_iq_i\log^2(h/q_i)
 \right].
\tag{10}
\]

The quantity \(P_h(r)\le\delta_0\log^2(1/\delta_0)\) can be made arbitrarily small. Thus \(CP_h(r)|S|\) is absorbed by half the phase-root term. Each nonempty block has
\(\log(h/q_i)\ge\log(1/\epsilon_0)\).

## 5. Restore the exact reference and sum phase errors

The reference bulk satisfies the local lemma. Its conditional product estimate restores the omitted events at the cost in (4). The retained-alphabet comparison costs \(\exp(Cm/h)\).

The restoration terms are absorbed as follows:
\[
 r h^{-2+\eta}+h^{-1}=o(P_h(r)),
\]
uniformly for \(1\le r\le\delta_0h\), with any fixed \(0<\eta<1\), and
\[
 |S|\log^4h/h
 =o\!\left(\sum_iq_i\log^2(h/q_i)\right).
\]
Combining these with (10) proves (2).

For the phase union, the blockwise estimate
\[
 \sum_{1\le q\le\epsilon_0h}
 \binom hq e^{-bq\log^2(h/q)}
 \le e^{-b'\log^2h}
\]
is already proved in the adaptive local-density note. Thus summing S costs at most
\[
 \exp\!\left[(m/h+O(1))e^{-b'\log^2h}\right].
\]
This is negligible even compared with the one-row penalty \(\log^2h/h\), proving (3). The finite number of matched phases does not change the exponential rate.

## 6. Precise remaining obstruction

The result allows a fixed positive local phase-error cap and arbitrary clustering inside it. It therefore strictly improves the earlier relative comparison that required a vanishing global error density or separated phase defects.

It does not handle an arbitrary concatenation of different matched phases under an exact reference comparison. The absolute guard argument resolves those concatenations only up to the span-tail remainder. Eliminating that remainder, or proving canonical escape for the remaining high-entropy components, is still necessary for exact quadratic optimality.

The complete comparison passed [independent review](continuation_exact_row_pressure_independent_audit.md).

