# A logarithmic barrier for disjoint private influences

9 November 2026. The positional construction in [near_quadratic_threshold.md](near_quadratic_threshold.md) prescribes each one-double gadget on a finite influence set and requires the translated influence sets to be disjoint. This note shows that this particular requirement cannot give an absolute quadratic width bound. It also records a counterexample to replacing every singleton by the bottom boundary row.

Neither result is an obstruction to an \(O(h^2)\) equality board.

## 1. The existing influence sets have total size at least \(ch^2\log h\)

Let \(h=2n\), use the binary sea \(\{1,h\}\), and include every opposite-parity double edge. For an edge \(e\), let \(A_e\) have exactly the meaning used in the positional construction: it includes the required sea columns in every three-black tilted rectangle or nonvertical mixed support involving that double and otherwise only the two sea rows.

Fix an interior odd endpoint \(a=2j+1\), where \(1\le j\le n-1\), and put
\[
N_a=(a-1)(h-a).
\]
For any positive divisor \(u\mid N_a\), write \(v=N_a/u\). The three points
\[
(0,a),\qquad (u,1),\qquad(v,h)
\]
form a right angle at \((0,a)\), since
\[
(u,1-a)\cdot(v,h-a)=uv-(a-1)(h-a)=0.
\]
Their rectangle completion is
\[
(u+v,h+1-a).
\]
All four rows lie in the strip. If \(u\ne v\), the four columns \(0,u,v,u+v\) are distinct, so the two sea requirements are feasible. Thus every divisor \(u\) except possibly \(\sqrt{N_a}\) belongs to \(A_e\), for every edge \(e\) incident with \(a\). In particular,
\[
|A_e|\ge\tau(N_a)-1\ge\tau(a-1)-1=\tau(2j)-1.      \tag{1}
\]
The horizontal span is at most \(N_a+1\), so these are precisely finite strip configurations of the type included in the construction.

Each odd endpoint has \(n\) even partners. Summing (1), and using \(\tau(2j)\ge\tau(j)\), gives
\[
\begin{aligned}
\sum_e|A_e|
&\ge n\sum_{j=1}^{n-1}(\tau(j)-1)\\
&\ge n(n-1)(H_{n-1}-2)\\
&=\frac14h^2\log h-O(h^2).
\end{aligned}                                                    \tag{2}
\]
Here \(\sum_{j\le M}\tau(j)=\sum_{d\le M}\lfloor M/d\rfloor\ge M H_M-M\).

If all translated influence sets are pairwise disjoint and retained inside the completed board, their union has size \(\sum_e|A_e|\). Consequently any board produced with that requirement has width
\[
\Omega(h^2\log h).                                  \tag{3}
\]
Splitting the labels into separate blocks does not remove this lower bound: the widths of disjoint blocks add. This is a counting obstruction to literal influence disjointness, independent of the local-lemma estimates or the method used to choose the centers.

Compatible overlaps remain a possible route forward. In a monotone gadget, many prescribed values agree, so disjointness is stronger than consistency. Alternatively, one could prescribe fewer cells or retain the local constraints between sea variables instead of fixing all their values in advance. Equation (3) does not apply to those changes.

## 2. A constant boundary sea does not eliminate the issue

It is tempting to replace every singleton by row 1. This fails even with one opposite-parity double. Put the double \(\{2,5\}\) in column zero and row 1 in every other column. At any height at least five, consider
\[
\begin{aligned}
R&=\{(0,5),(3,1),(-1,3),(4,3)\},\\
T&=\{(-1,1),(4,1),(-1,3),(4,3)\}.
\end{aligned}
\tag{4}
\]
The first is a tilted rectangle: its two diagonals have midpoint \((3/2,3)\) and length five. The second is an axis rectangle. Both have exactly the white presentation
\[
\{(-1,3),(4,3)\}.
\]
Thus a constant-boundary one-double lemma would be false.

The mechanism is general. If an odd double endpoint is \(a=2d+1\), with \(d\ge2\), the identity
\[
(d^2-1)^2+(2d)^2=(d^2+1)^2
\]
gives a tilted rectangle whose black diagonal is
\[
(0,2d+1),\qquad(d^2-1,1),
\]
and whose horizontal white diagonal is
\[
(-1,d+1),\qquad(d^2,d+1).
\]
The row-1 cells below these two white points give an axis rival. Hence every single double whose odd endpoint is at least five fails in the constant row-1 sea, regardless of its even endpoint.

More generally, if \(pq=d^2\) with \(p,q>0\) and \(p\ne q\), the same failure uses the row-1 columns
\[
-p,\qquad q-p,\qquad q.
\]
These divisor-indexed horizontal rivals explain why the boundary sea cannot simply be fixed before the double positions are chosen.

## 3. Current conclusion

The proved \(O(h^2(1+\log h)^{16})\) threshold remains valid. The new conic counts do not by themselves remove the logarithmic obstruction in (2). An absolute quadratic construction must change the private prescription step, exploit compatible overlaps, or find another complete sea-filling mechanism. The counterexample in (4) rules out the simplest constant-boundary replacement.

## 4. The exact weaker compatibility condition

There is a precise way to relax the existing overlap event. Fix one binary background and orient every good one-double gadget with its lower sea row on the left and its upper sea row on the right. The influence set is symmetric under horizontal reflection. Write
\[
A_e\setminus\{0\}=S_e\cup(-S_e),\qquad S_e\subset\mathbb Z_{>0}.
\]
At center \(X_e\), the prescribed lower-row columns are \(X_e-S_e\), and the prescribed upper-row columns are \(X_e+S_e\).

For two centers \(X_e<X_f\), their prescriptions disagree exactly at overlaps of the form
\[
X_e+p=X_f-q,
\qquad p\in S_e,\quad q\in S_f.
\]
Thus the exact pairwise conflict condition, before removing double columns themselves, is
\[
X_f-X_e\in S_e+S_f.                              \tag{5}
\]
Equal-sign overlaps prescribe the same value and need not be excluded. This is substantially weaker than forbidding every difference in \(A_e-A_f\).

Furthermore, no singleton prescription needs to be enforced at a double column. In the completeness proof, a required black cell at any double column is attributed to that label. Consequently a forbidden support that meets another double is already a multiple-label event. Every actual one-label support has all its other required points at singleton columns, where the gadget prescriptions remain in force.

It is therefore sufficient to require distinct centers, exclude conflicts in (5) at singleton columns, and retain the multiple-label geometric exclusions from the positional theorem. One may still exclude every occurrence of (5), including a conflict covered by a third double, to keep pairwise event dependencies. This stronger version is also sufficient.

This reduction removes the total-cardinality packing argument in (2): same-value prescriptions can now overlap arbitrarily. A direct union bound still gives \(|S_e+S_f|\le|S_e||S_f|\), so it does not yet improve the proved width. The remaining task is a structured packing or local-lemma argument for the sumsets in (5), together with the other geometric events. No \(O(h^2)\) packing theorem is claimed here.
