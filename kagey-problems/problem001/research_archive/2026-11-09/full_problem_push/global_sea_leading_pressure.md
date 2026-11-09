# The global leading sea-entropy coefficient

9 November 2026. The full protected-row argument extends to every balanced row partition differing in o(h) rows from a protected law. Combined with partition rigidity, this determines the leading growth rate over all balanced partitions.

For a balanced row partition pi, let \(\rho_\pi(h)\) be the full normalized fixed-final-F sea growth rate, with arbitrary column phases. Define
\[
 R_h=\max_{\pi\ {\rm balanced}}\rho_\pi(h).
\]
Write \(\rho_{\rm parity}\) for the ordinary row-parity shift; it is not the same quantity as R_h.

Let
\[
 \mathcal P=\prod_{p\equiv1\ (4)}
 \frac{(p-1)(p^2+4p+1)}{(p+1)^3},
 \qquad
 d_{\rm Q}=\frac{144/5+26\mathcal P/9}{\pi^4}.
\tag{1}
\]
The protected constants and their normalization are proved in
[protected_phase_explicit_constants.md](protected_phase_explicit_constants.md).

**Global theorem.**
\[
 \boxed{\displaystyle
 R_h=\frac h2-\frac{d_{\rm Q}}2(\log h)^4
                  +o((\log h)^4).}
\tag{2}
\]
The additive coefficient \(d_{\rm Q}/2\) is approximately 0.1595753.

Every entropy-maximizing balanced row partition differs in \(o(\log^2h)\) rows from a translated or complemented quadratic protected row law. This is an asymptotic structural statement. It does not identify the exact maximizing partition at a fixed height or its dominant recurrent component.

## 1. A near-protected upper bound

Let c_h be balanced, and let c_h^0 be a protected row law with
\[
 E_h=\{y:c_h(y)\ne c_h^0(y)\},\qquad r_h=|E_h|=o(h).
\]
The protected reference may have class sizes h/2+O(1); exact balance of the reference is not required. Put
\[
 \rho_0(h)=\max_{X\in\mathcal X(c_h^0)}r_{c_h^0,X}(h),
 \qquad \mu_h=(\log h)^4/h.
\]
Then
\[
 \log\rho_{c_h}(h)\le\log\rho_0(h)+o(\mu_h).
\tag{3}
\]
If \(r_h\to\infty\), there is an absolute a>0 such that the stronger estimate holds:
\[
 \log\rho_{c_h}(h)
 \le\log\rho_0(h)
       -a\frac{r_h}{h}\log^2(h/r_h)+o(\mu_h).
\tag{4}
\]
The little-o terms concern the stated sequence. The negative row penalty in (4) has a uniform absolute coefficient.

We prove these claims by modifying
[the full protected-row argument](full_protected_row_leading_pressure.md).
The modifications are recorded explicitly below.

## 2. The bad-block and transition witnesses remain uniform

Fix the small local phase-error cap epsilon_0 used in that proof. Section 7 of
[near-maximal partition rigidity](near_maximal_partition_rigidity.md)
proves that, uniformly when the row distance tends to zero, the union of valid h-block words whose actual phase \(c_h(w_x)\) is epsilon_0-far from every phase matched to \(c_h^0\) has count at most
\[
 (h/2)^h e^{-\gamma h}
\tag{5}
\]
for some fixed gamma>0.

The universal generic block count is still
\((h/2)^h e^{o(h)}\), uniformly over balanced partitions.

For a transition between two good blocks with different matched labels, use the old local wall family but delete every geometry touching E_h. For each shape, fixing a corner row determines its vertical translation. There are Theta(h) permitted translations, so deleting r_h rows removes only \(O(r_h/h)\) of its mean. Its marked mean therefore remains at least ch. Phase-error deletions and the sum over their descriptions are handled exactly as before.

Consequently both witness types retain a fixed positive deficit gamma_0 h. The selected-witness guards and their independent counts are unchanged.

## 3. One-sided phase roots survive the changed rows

Inside a good interval, use the same one-sided adaptive phase roots, with completion rows in the central h-band and outside E_h. Delete all geometries having any corner row in E_h.

For every fixed direction/scale shape, there are Theta(h) completion-row translations in the chosen old class. Any prescribed exceptional corner row removes at most one translation. Thus the total deletion is an \(O(r_h/h)\) fraction, uniformly in the direction cutoff and the interval-length cap.

The raw and compatible extension counts can only decrease under these deletions. The adaptive maximal inequality and block activity therefore retain the same positive constants.

The phase-root completion row lies outside E_h. Its actual row color equals the reference color, but its column phase is flipped. All three black corners avoid E_h and the phase-error set S. Hence it remains a valid singleton-rival obstruction for the actual partition.

## 4. Retained old bulk and the auxiliary row roots

Retain reference protected bulk supports whose entire geometric witness avoids E_h, whose required black columns avoid S, and whose support lies within its good interval. All row-color relations in such a witness are unchanged, so these events remain forbidden for the actual partition.

The established fixed-row four/six support counts bound the lost bulk mean by
\[
 C_\eta r_h h^{-2+\eta}
\tag{6}
\]
per column, for any fixed \(0<\eta<1\). This includes exceptional rows appearing as common white corners, not just required black cells. Restricting to the short-span bulk only decreases this loss.

Actual and reference selected alphabet sizes are h/2+O(1). Their product logarithms differ by O(m/h), and every retained event probability differs by a relative O(1/h), because its arity is at most six. These errors are negligible at the leading scale mu_h. No exact equality of the two class sizes is needed here.

If r_h remains bounded, (6) and O(1/h) are already o(mu_h). Omit the auxiliary row roots. The full protected-row proof gives (3).

Now suppose \(r=r_h\to\infty\). Put
\[
 P_h=\frac rh\log^2(h/r).
\tag{7}
\]
Use the unthinned adaptive row-root family from
[adaptive_row_root_pressure.md](adaptive_row_root_pressure.md).
Its completion row lies in E_h, all other geometric rows avoid E_h, and its completion and black columns avoid S.

For each matched reference phase, the period average of the number of eligible changed rows is a fixed positive fraction of r for large r. In a constant phase, the two directed row-change counts differ by at most O(1), because both partitions have class sizes h/2+O(1). In a nonconstant matched phase, every changed row is eligible in a fixed positive fraction of columns. Thus the family has period-averaged mean at least aP_h per column. The bounded-period correction on a finite interval is absorbed by the end loss below.

Its raw and conditional one-/two-cell pressures are
\[
 O\!\left(\sqrt{r/h}\log(h/r)+r/h\right)=o(1).
\tag{8}
\]
The end loss in an arbitrary finite good interval is at most \(C\sqrt{rh}\), from the span-weighted adaptive estimate. This remains a valid lower bound even when the interval is short enough that the resulting bound is negative.

Deleting an error COLUMN from this row-root family removes at most CP_h mean. Indeed, the translated family has fixed period at most four, total mean O(P_h) per translation, and a fixed number of required or completion columns. Summing these roles gives the stated raw column incidence. This is a raw-mean estimate, not the larger one-cell conditional extension bound.

The phase roots have completion rows in \(E_h^c\), whereas row roots have completion rows in E_h. Three prescribed noncollinear right-angle corners have a unique completion. Hence distinct events from the two families cannot share all three assignments. Their one-/two-cell mixed conditional sums are bounded by their already established uniform extension estimates. The joint unthinned local-lemma criterion holds.

Since \(P_h\to0\), the loss \(CP_h|S|\) is absorbed by the phase-root penalty, whose weight per error has a fixed positive lower bound after the good-interval length cutoff. The row-root mean retained over the good intervals is at least
\[
 aP_hm
 -C P_h\,|\hbox{guard columns}|
 -C\sqrt{rh}\,(\hbox{number of good intervals})
 -CP_h|S|.
\tag{9}
\]

For k selected witnesses, guard length is O(Dhk) and there are at most k+1 good intervals. Both additional per-witness costs are o(h):
\[
 D hP_h=D r\log^2(h/r)=o(h),\qquad
 \sqrt{rh}=o(h).
\tag{10}
\]
They are absorbed by the fixed witness deficit gamma_0 h.

Finally, (6) and the product-alphabet O(1/h) error are absorbed by a fixed fraction of P_h:
\[
 \frac{r h^{-2+\eta}}{P_h}
 =\frac{h^{-1+\eta}}{\log^2(h/r)}\longrightarrow0,
 \qquad
 \frac{h^{-1}}{P_h}
 =\frac1{r\log^2(h/r)}\longrightarrow0.
\tag{11}
\]

## 5. Complete the near-protected estimate

Fix a bulk truncation parameter delta>0. Apply Suen to the retained short-span bulk first, then the joint row/phase-root conditional estimate. The common-cap maximal inequality and error-profile sum are unchanged. The guard boundary activity is absorbed by the same choice of D, and (10) is absorbed for sufficiently large h.

For each selected-witness description, the resulting bound is
\[
 \begin{split}
 \log N
 \le\;&m\log\rho_0-aP_hm
       +C\delta\mu_hm+o_\delta(\mu_h)m\\
     &-c\gamma_0hk+O_h(1)
 \end{split}
\tag{12}
\]
when \(r_h\to\infty\). For bounded r omit the P_h term. As in the fixed-row proof, the short-support cut cost is
\(O(h^{1-\delta}\log^4h)=o(h)\) per witness and is absorbed before writing (12).

Summing selected-witness descriptions costs only
\(\exp(O(mh^{-1}e^{-c\gamma_0h}))\).
For every fixed delta, divide by m and let m tend to infinity. Then take h to infinity, and finally delta to zero. This proves (3)--(4).

No quantitative rate in the far-block inverse theorem is used: epsilon_0 and gamma_0 are fixed, D is chosen from them, and the row distance r_h/h tends to zero afterward.

## 6. Optimize over all balanced partitions

Choose a maximizing balanced partition pi_h. The quadratic protected phase is contained in a balanced quadratic sea, so
\[
 R_h\ge r_{\rm Q}(h)
 =h/2-\tfrac12d_{\rm Q}\log^4h+o(\log^4h).
\]
The uniform half-entropy upper bound and
[partition rigidity](near_maximal_partition_rigidity.md)
therefore give a protected reference \(c_h^0\) at row distance o(h).

Apply (3). If the reference is ordinary, its best protected coefficient is d_O, strictly larger than d_Q. This contradicts the quadratic lower bound along any such subsequence. Hence maximizing partitions are near quadratic references for all sufficiently large heights.

All translated or complemented quadratic protected phases have the same leading coefficient d_Q, including slightly unbalanced references. Equation (3) now gives the matching upper bound in (2).

There is also a sharper distance consequence. If an optimizing sequence had
\[
 r_h\ge\epsilon\log^2h
\]
along a subsequence for some fixed epsilon>0, then r_h tends to infinity and (4) applies. The function \(r\log^2(h/r)\) is increasing for \(r<h/e^2\). Since r_h=o(h),
\[
 P_h\ge(\epsilon+o(1))\,\log^4h/h.
\]
The negative term in (4) would contradict the quadratic protected lower bound. Therefore the distance of every maximizing partition from the quadratic protected family is \(o(\log^2h)\).

## 7. Exponential growth of maximum blackouts

Let a_h(m) count maximum blackouts at fixed height h, and define
\[
 A_h=\limsup_{m\to\infty}a_h(m)^{1/m}.
\]
Then
\[
 \boxed{\displaystyle
 A_h=\frac h2-\frac{d_{\rm Q}}2(\log h)^4
                 +o((\log h)^4).}
\tag{13}
\]

The eventual finite-state marked-resolvent description has only sea
eigenvalues as exponential bases. The finitely many double labels can
change polynomial factors but not introduce a larger exponential base.
Consequently \(A_h\le R_h\).

For the lower bound, the balanced quadratic partition has a canonical
component containing its protected quadratic language in the entropy
sense proved by the audited capture theorem. Every required double has
a positive collared insertion through that component. The resulting
maximum-blackout counts have exponential growth at least \(r_{\rm Q}(h)\).
Thus
\[
r_{\rm Q}(h)\le A_h\le R_h,
\]
and the two endpoints have the same expansion by (2).

The canonical component is primitive and its collared insertions work
for every sufficiently large width. Therefore the same lower bound
holds for \(\liminf_{m\to\infty}a_h(m)^{1/m}\). Both the liminf and limsup
have expansion (13) as h tends to infinity; this does not assert that
they agree at each fixed height.

This argument uses the exact counting framework in
[the SCC/resolvent note](../../2026-11-08/counting_followup/exact_counting_scc_and_resolvent.md)
and the canonical insertion/capture results cited there and in
[quadratic parity capture](quadratic_parity_entropy_capture.md).
It does not determine the polynomial factor in m, its leading constant,
or a simultaneous next-order regime with m depending on h.

## 8. Scope

The theorem gives the global leading sea-entropy coefficient and a vanishing logarithmic row-distance bound for maximizing partitions. It does not prove that a maximizing partition is exactly quadratic, that its full sea has a unique maximal component, or that every maximal component admits every double insertion.

Those exact finite-height questions remain separate from the asymptotic coefficient in (2).

The complete proof passed [independent adversarial review](global_sea_pressure_independent_audit.md), including the global optimization and maximum-blackout counting consequences.

