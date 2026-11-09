# Exact pressure for every sufficiently small row perturbation

9 November 2026. A rectangular subfamily with no divisor loss extends the exact row comparison to \(r\le\delta_0h\), for an absolute \(\delta_0>0\). In particular, the comparison covers the entire \(o(h)\) neighborhood supplied by [near-maximal partition rigidity](near_maximal_partition_rigidity.md).

Fix a protected row/column pair \((c_0,t)\). Its two row classes have size \(h/2+O(1)\); the reference need not be exactly balanced at this height. Let c be a balanced row coloring, and put
\[
 E=\{y:c(y)\ne c_0(y)\},\qquad r=|E|.
\]
Let \(Z_0(m)\) be the exact protected partition function for \((c_0,t)\), using the normalized fixed-final-pair-set language.

**Robust comparison.** There are absolute \(a,\delta_0>0\) such that, for all sufficiently large h and every \(1\le r\le\delta_0h\),
\[
 Z_c(m)\le C_h Z_0(m)e^{-a r m/h}.
\tag{1}
\]
For a sufficiently small absolute b, the same strict comparison holds after taking the union over all column-phase profiles differing from t in at most
\[
 \sigma m+O_h(1)\quad\text{columns},\qquad
 \sigma\le b\,\frac{r/h}{\log(eh/r)}.
\tag{2}
\]
More precisely, their exponential growth rate is at most
\[
 \rho_{c_0,t}(h)e^{-a' r/h}.
\tag{3}
\]
Phase-error columns may be arbitrarily clustered. The balanced-reference theorem and its phase-error extension passed [independent review](robust_row_pressure_independent_audit.md). Section 5 records the additional, slightly unbalanced quadratic reference.

The stronger logarithmic penalty in [changed_row_relative_pressure.md](changed_row_relative_pressure.md) remains available in its earlier range. This note replaces that penalty by \(r/h\) in order to remove the fixed power-saving restriction on r.

## 1. A rectangular family with two free integer parameters

Fix a changed completion point \(W=(x,w)\) whose old row color is \(t(x)\). Choose a sign \(\epsilon\in\{-1,1\}\) pointing toward the farther row boundary. Let
\[
 I_h=[h/100,h/50]\cap\mathbb Z.
\]
For \(u,v\in I_h\), take perpendicular side vectors
\[
 U=(4u,4\epsilon u),\qquad
 V=(-4v,4\epsilon v).
\tag{4}
\]
They satisfy \(U\cdot V=0\). Their vertical span is at most \(4(u+v)\le4h/25\), so all four corners lie in the strip for sufficiently large h.

Every coordinate change is divisible by four. Therefore W and all three other corners obey the same protected row/column law. The three prescribed black points are
\[
 P=W+U,\qquad Q=W+V,\qquad R=W+U+V.
\tag{5}
\]
Their columns are distinct. If \(u=v\), W shares the column of R; this does not identify two prescribed black variables. W changes row class while R does not, so the singleton-axis rival is still present. The completion W lies between the extreme black columns. The entire rectangle has horizontal span \(4(u+v)=O(h)\).

There are \(|I_h|^2=\Theta(h^2)\) choices. For a fixed root row w, requiring one of the three black rows to belong to E imposes one of
\[
 w+4\epsilon u\in E,\qquad
 w+4\epsilon v\in E,\qquad
 w+4\epsilon(u+v)\in E.
\]
Each condition removes at most \(r|I_h|\) parameter pairs. If \(r\le\delta_0h\) and \(\delta_0\) is sufficiently small, at least a fixed positive fraction remains.

The retained three black rows are unchanged by c. The completion row changes color, so the three-point support produces a singleton-axis rival in the new model. Three black corners determine their right triangle and completion, so the parametrization has at most a bounded multiplicity; deduplicate the events.

If t is nonconstant, every changed row is eligible in a fixed positive fraction of columns. If t is constant and the two labeled class sizes are preserved, exactly half of the changed rows are eligible. Thus the total event mean is
\[
 \sum_{A\in R}\Pr(A)\ge
 a_1\frac rh\,m-O_h(1).
\tag{6}
\]
Each probability is \(\Theta(h^{-3})\). Since the span is \(O(h)\), the finite-end mean loss is \(O(r)\), uniformly in the word length.

## 2. Uniform conditional overlap counts

A fixed black cell and a fixed completion row leave only \(O(h)\) choices in (4). If the cell plays the role P or Q, one parameter is fixed by its row. If it plays R, the sum \(u+v\) is fixed. Its column then determines the horizontal translation. Hence at most
\[
 O(rh)
\tag{7}
\]
retained events contain any specified black cell.

Two fixed black cells leave only \(O(r)\) events. There are three pair roles:

- The pair Q,R is separated by U. It fixes u; each completion row in E then fixes v and the translation.
- The pair P,R is separated by V. It fixes v; each completion row in E then fixes u and the translation.
- The pair P,Q fixes \(u+v\) from its horizontal difference and \(u-v\) from its vertical difference, hence fixes both parameters and the translation.

There are only constantly many choices of point roles and the vertical sign. A distinct event cannot share all three prescribed cells.

The total event probability incident to one column is \(O(r/h)\), obtained by summing (7) over its possible rows. Conditional on one event, compatible neighbors sharing one or two black assignments have total probability
\[
 O(rh)\,O(h^{-2})+O(r)\,O(h^{-1})=O(r/h).
\tag{8}
\]
There is no maximum-divisor factor in these bounds.

## 3. Retain and restore the exact old bulk

Let \(B_0\) contain old protected four/six certificates whose entire row geometry avoids E. Under equal labeled class sizes, its joint law is preserved by the coordinatewise alphabet bijection fixing every unchanged row.

The protected bulk has incident weight \(o(1)\), and its compatible extensions through the three prescribed cells contribute \(O_\varepsilon(h^{-1+\varepsilon})\). Choose \(\delta_0\) small enough that the raw and conditional sums in (8) are below the fixed thresholds in the local-lemma argument. Then, with \(x_A=2\Pr(A)\), the unthinned criterion holds and
\[
 \Pr(A\mid\text{avoid any previously listed events})
 \ge\Pr(A)/2
\tag{9}
\]
for every row-root event.

Avoid B0 first, then these roots. By (6), the extra cost is \(\exp[-a_2rm/h+O_h(1)]\). Restoring old certificates deleted because they meet E costs only
\[
 \exp[O_\varepsilon(rm h^{-2+\varepsilon})+O_h(1)].
\tag{10}
\]
For a fixed \(\varepsilon<1\), this is negligible compared with \(rm/h\), uniformly over \(1\le r\le\delta_0h\). This proves (1) when labeled class sizes agree.

If they differ by one at odd height, a constant phase still has at least \((r-1)/2\ge r/3\) eligible rows when \(r\ge3\). The retained-bulk dummy-letter comparison costs at most \(\exp(Cm/h)\). For \(r\ge R_0\), with a sufficiently large absolute \(R_0\), this is absorbed by the \(a_2rm/h\) penalty after reducing its constant. For \(r<R_0\), the earlier fixed-r comparison gives the stronger \(\log^2h/h\) penalty, except for the one-row growing even-class case, which gives \(\log h/h\). Both imply (1) for sufficiently large h. Thus (1) holds for every balanced c in the stated range.

## 4. Arbitrarily clustered phase changes

Let \(S\subseteq[1,m]\), and use the new phase \(t_S=t+1_S\). Retain only old bulk certificates whose geometry avoids E and whose black columns avoid S. Retain only the events (5) whose black columns and completion column avoid S.

At any specified column, the probability mass of events using it as a black or completion column is \(O(r/h)\). Removing the roots that meet S therefore loses at most
\[
 C|S|r/h
\tag{11}
\]
from their mean. For \(|S|\le\sigma_0m\), with a small absolute \(\sigma_0\), a fixed fraction of (6) remains.

Restoring the protected bulk deleted at S costs
\[
 \exp[C|S|\log^4h/h].
\tag{12}
\]
All retained events avoid S, so their product-space comparison is exact outside those columns. At S, changing the selected balanced class costs only \(\exp(O(|S|/h))\). This is absorbed by (12).

For class-size-preserving changes, the result is
\[
 Z_{c,S}(m)\le C_hZ_0(m)
 \exp[-a_3rm/h+C|S|\log^4h/h].
\tag{13}
\]
The same proof works for \(r\ge R_0\) without class-size preservation, absorbing the dummy-letter cost as in Section 3.

For the finitely bounded values \(r<R_0\), use the stronger old rooted families. Their means remain a fixed fraction after deleting roots at S, and the restoration cost is still (12). In the one-row growing-class exception, retain its two-black vertical-rival family outside S. Its lost mean is \(O(|S|\log h/h)\), while its original mean is \(\Omega(m\log h/h)\). No spatial-root family is added, so no new mixed-family overlap estimate is needed. These cases also imply (13), after decreasing its absolute constant.

Summing (13) over all \(|S|\le\sigma m+O_h(1)\) gives
\[
 \rho_{c,\le\sigma}(h)\le
 \rho_{c_0,t}(h)
 \exp[-a_3r/h+C\sigma\log^4h/h+H_2(\sigma)].
\tag{14}
\]
Set \(q=r/h\). For sufficiently small fixed b,
\[
 \sigma\le bq/\log(e/q)
 \quad\Longrightarrow\quad
 H_2(\sigma)\le a_3q/4.
\]
Also \(C\sigma\log^4h/h=o(q)\), uniformly in \(1/h\le q\le\delta_0\). This proves (2)--(3).

A finite union over matched protected base phases replaces \(\rho_{c_0,t}\) by their maximum. The conclusion still requires closeness to one global phase; positive-density domains of several different phases are outside its scope.

## 5. The slightly unbalanced quadratic reference

The protected law \(c_0(y)=q(y)+y+\beta\) has class-size difference two when \(h\equiv2\pmod4\). Its class sizes are \(h/2-1\) and \(h/2+1\). A balanced c has both sizes \(h/2\), so each selected alphabet changes size by at most one.

Every matched quadratic column law is nonconstant and assumes each value in exactly half of a period. Consequently, each changed row remains eligible for roots in half the columns, including when \(r=1\). The growing constant-class exception from Section 3 does not occur here.

All protected bulk and rooted-family estimates use only alphabet sizes \(h/2+O(1)\). The retained-bulk dummy-letter comparison again costs \(\exp(O(m/h))\). For \(r\ge R_0\), the rectangular family absorbs this cost exactly as before. For \(r<R_0\), the full changed-completion family has mean \(\Omega(rm\log^2h/h)\) and the same vanishing conditional overlap sums. It therefore absorbs the dummy-letter cost too.

Deleting every root meeting S loses only a fixed fraction of that mean when \(|S|\le\sigma_0m\). The proof of (13)--(14) is unchanged. This proves (1)--(3) for this last protected reference, so the theorem covers every \(o(h)\) row neighborhood supplied by near-maximal partition rigidity.

