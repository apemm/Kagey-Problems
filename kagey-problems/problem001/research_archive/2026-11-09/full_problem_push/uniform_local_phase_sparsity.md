# Exact protected pressure for uniformly locally sparse phase errors

9 November 2026. A common direction cutoff controls arbitrary error clusters when every interval of h columns has small error density. No packet separation, internal packet density, or bound on the total number of clusters is needed.

Fix a protected row law c_0 and a matched protected column law X. Let Z_X(m) count the normalized fixed-final-F support language. For S contained in the column interval, let Z_{X,S}(m) count the phase X+1_S with the same row partition and final F. Selected alphabet sizes are h/2+O(1), including the slightly unbalanced protected reference.

Put \(\Lambda=1+\log h\), and let \(L=Ch^2\) exceed every forbidden support span. Assume initially that S has distance at least L from the two finite ends.

## 1. Uniform statement

There are absolute constants \(\epsilon_0,c,H>0\) such that, whenever
\[
 h\ge H,\qquad h^{-1}\le\epsilon\le\epsilon_0,\qquad
 |S\cap[j,j+h-1]|\le\epsilon h\quad\hbox{for every }j,
\tag{1}
\]
one has
\[
 Z_{X,S}(m)\le Z_X(m)
       \exp[-c|S|\log^2(1/\epsilon)].
\tag{2}
\]
The constants and height threshold are uniform throughout the displayed range of epsilon.

Consequently the union of all profiles satisfying (1) has exponential growth at most
\[
 \rho_X(h)\bigl(1+\exp[-c\log^2(1/\epsilon)]\bigr).
\tag{3}
\]
Finite-end errors change only a fixed-height multiplicative constant.

In particular, for any sufficiently large fixed A,
\[
 \epsilon_h=\exp(-A\sqrt{\log h})
\tag{4}
\]
gives an error activity \(h^{-cA^2}\). Choosing A so that \(cA^2>2\), the language in (3) has
\[
 \log\rho_{\mathrm{local}}(h)
   =\log\rho_X(h)+o(\log^4h/h).
\tag{5}
\]
The reverse inequality follows by taking S empty.

## 2. A uniform completion-column count

Set
\[
 R=\lfloor\epsilon^{-1/4}\rfloor.
\tag{6}
\]
By reducing epsilon_0, R exceeds any fixed required constant. By (1), \(R\le h^{1/4}\).

For a root \(W=(j,w)\), \(j\in S\), choose w with \(c_0(w)=X(j)\), and choose a vertical sign toward the farther boundary. For primitive \(1\le a,b\le R\), take
\[
 U=(4ka,4\eta kb),\qquad
 V=(-4lb,4\eta la),
\tag{7}
\]
where
\[
 h/(100b)\le k\le h/(50b),\qquad
 h/(100a)\le l\le h/(50a).
\tag{8}
\]
The three required black cells are W+U, W+V, and W+U+V. The rectangle fits vertically, has horizontal span at most ChR, and preserves every protected row/column residue rule.

Discard ka=lb, and discard every geometry whose black support meets S. The remaining supports have three distinct black columns, all outside S. Their completion W has the wrong row class at its flipped column, so each is a genuine singleton-axis rival in the new model.

Here is the elementary estimate replacing the full divisor kernel:
\[
 \#\{\hbox{geometries through a prescribed black cell P,
                   with prescribed completion column j}\}
       \le ChR^2.
\tag{9}
\]
The completion row is not fixed in (9).

For a side corner, its horizontal displacement gives either \(ka=d\) or \(lb=d\), after dividing by four and taking a sign. The relevant direction coordinate is a divisor of d and is at most R. Summing over the other direction coordinate and over the remaining scale gives at most
\[
 C\sum_{a\le R}\sum_{b\le R}h/a
 \le ChR(1+\log R)\le ChR^2.
\]
For the opposite corner, the equation is \(ka-lb=d\). Since \(\gcd(a,b)=1\), its solutions have the form
\(k=k_0+bt,\ l=l_0+at\). The scale intervals allow at most
\[
 C\bigl(h/\max(a^2,b^2)+1\bigr)
 \le C(h/(ab)+1)
\]
values of t. Summing over a,b gives \(C(h\log^2(2R)+R^2)\le ChR^2\).
The fixed row of P determines the root row for each geometry, so there is no additional factor h.

The same estimate holds with a prescribed completion cell W and a prescribed black column, without fixing the black row: once the directions and scales are chosen, that row is determined.

## 3. Mean and local dependence

Before deletions, the primitive harmonic sum gives
\(\Theta(h^2\log^2R)\) shapes per eligible root row and \(\Theta(h)\) eligible rows. Thus the probability mean at each root column is at least
\[
 c_1\log^2R.
\tag{10}
\]
All rounding estimates are uniform for \(R\le h^{1/4}\). The family ka=lb has only \(O(h\log(2R))\) scale choices per root row, so its probability mean is \(O(\log(2R)/h)\).

For a fixed root column, all relevant black columns lie in an interval of length ChR. Assumption (1) bounds the number of those columns belonging to S by \(C\epsilon hR\). Equation (9), summed over the possible row of a black point and weighted by \(O(h^{-3})\), bounds the mean lost to each such column by \(CR^2/h\). The total loss is therefore
\[
 C\epsilon R^3\le C\epsilon^{1/4}.
\tag{11}
\]
After decreasing epsilon_0, the retained mean is at least \(c_2\log^2R\).

The same calculation gives both the raw incident probability at a free column and the compatible conditional mass through one fixed black assignment:
\[
 C\epsilon R^3.
\tag{12}
\]
Only \(C\epsilon hR\) root columns can interact with that column.

Two prescribed black cells in distinct columns and a prescribed completion column have O(1) tilted completions. The completion locus is a circle or a perpendicular line. A vertical perpendicular line would require a horizontal black side and hence an axis rectangle, which this family excludes. Thus, after fixing two assignments, the total compatible rooted mass is at most
\[
 C\epsilon hR\cdot h^{-1}=C\epsilon R.
\tag{13}
\]
Three noncollinear right-angle corners determine their unique fourth corner. Deduplicate supports, so distinct root events never share all three assignments.

Equations (12)--(13) tend uniformly to zero as epsilon_0 tends to zero. The old protected four/six-cell family has vanishing raw pressure and \(O_\eta(h^{-1+\eta})\) compatible extensions through the prescribed cells of a root event, as established in the protected overlap bounds.

## 4. Exact comparison with the old partition function

Retain the old protected bulk events B_0 whose required black columns avoid S. Their joint product law is unchanged by the phase errors. They remain forbidden regardless of the colors of their common corners.

Choose epsilon_0 small enough, then H large enough. The joint local-lemma criterion holds for B_0 and the unthinned root family. The conditional lower-probability lemma from [the exact relative-pressure argument](relative_sparse_defect_pressure.md) gives
\[
 \Pr(E\mid\hbox{avoid any previously listed events})
       \ge \Pr(E)/2
\]
for each rooted event E. Avoid B_0 first, then list all roots. Equations (10)--(13) give an additional avoidance factor
\[
 \exp[-c_3|S|\log^2R].
\tag{14}
\]

Restoring the omitted old bulk costs at most
\(\exp(C|S|\Lambda^4/h)\), by the sharp protected incident-weight bound and the conditional local-lemma product estimate. Alphabet-size changes cost at most \(\exp(C|S|/h)\). Hence
\[
 \frac{Z_{X,S}(m)}{Z_X(m)}
 \le
 \exp[-c_3|S|\log^2R+C|S|\Lambda^4/h].
\tag{15}
\]
Since \(\log R\ge c_4\log(1/\epsilon)\) and this logarithm has a fixed positive lower bound, the positive term is absorbed uniformly for h large. This proves (2).

Summing (2) over all subsets S, even those failing (1), overcounts by
\[
 \bigl(1+\exp[-c\log^2(1/\epsilon)]\bigr)^m.
\]
This proves (3). For end errors, trim fixed L collars and use the fixed-height bounded-shift comparison of protected partition functions; no assertion that every individual protected prefix extends is needed.

## 5. Scope and the remaining step

This theorem controls arbitrary clustering inside each h-window, subject only to its uniform density cap. It is an exact-reference statement, not an absolute product-space pressure estimate.

It does not show that every competitive phase profile satisfies (1), or that every profile decomposes into domains with this property. The existing qualitative entropy concentration does not provide the rate in (4). A multiscale treatment of intervals of intermediate error density is still needed for unrestricted dominance.

The complete argument passed [independent review](local_phase_sparsity_independent_audit.md). The domain extension, including domains of length h divided by any fixed logarithmic power, is developed in [locally sparse errors in protected domains](locally_sparse_errors_in_protected_domains.md).

