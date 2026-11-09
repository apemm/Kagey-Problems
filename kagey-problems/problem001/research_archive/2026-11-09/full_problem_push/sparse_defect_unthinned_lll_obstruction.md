# Why the shared-variable local lemma does not directly capture sparse defects

9 November 2026. The complete singleton-rival family at one isolated parity defect already prevents an unthinned local-lemma certificate on the shared-variable dependency graph. The same obstruction survives the usual incompatible-assignment refinement. A conditioned block model or another entropy-capture method remains possible. The complete argument, including Section 2.1, has passed independent review.

Consider the ordinary parity partition. The column at zero chooses an even black row uniformly; every other column chooses an odd black row uniformly. Work in the infinite strip, or in a finite interval containing the support range around zero.

**Proposition.** There is a family \(\mathcal A_h\) of genuine singleton-axis-rival assignment events such that every event uses the row variable at column zero and
\[
 \sum_{E\in\mathcal A_h}\Pr(E)\ge c(\log h)^2
\tag{1}
\]
for an absolute \(c>0\) and all sufficiently large h.

Consequently no standard asymmetric local-lemma certificate exists for the complete event family on its shared-variable graph. The same obstruction applies to the clique-expansion criterion on that graph.

## 1. A logarithmically large clique of black-root events

Choose an even row \(r\in[h/4,h/2]\), primitive odd positive integers \(a,b\), and odd positive scales k,l. Use the black points
\[
 A=(0,r),\qquad
 B=(ka,r+kb),\qquad
 C=(-lb,r+la).
\tag{2}
\]
The two side vectors at A are perpendicular. Their fourth corner is
\[
 D=(ka-lb,r+kb+la).
\]
The rows of B and C are odd, while the rows of A and D are even. Require
\[
 a,b\le h/32,\qquad
 1\le k\le h/(8b),\qquad
 1\le l\le h/(8a),
\]
with k,l odd. All four rows then lie in the strip.

Except when \(ka=lb\), the four corner columns are distinct. The completion D is in a nondefect column, whose black row is odd. Therefore its even row has the opposite partition color, and the three prescribed black points produce a singleton-axis rival.

For each direction, there are at least \(ch^2/(ab)\) admissible odd scale pairs. The standard odd primitive harmonic sum gives
\[
 \sum_{\substack{a,b\le h/32\\a,b\ {\rm odd}\\(a,b)=1}}\frac1{ab}
 \asymp(\log h)^2.
\]
This follows directly by Möbius inversion; the same calculation appears in [the fixed-corner rectangle count](six_support_leading_pressure.md), Section 2. Thus (2), before excluding repeated columns, supplies \(\Omega(h^3\log^2h)\) distinct triples.

If \(ka=lb\), primitivity gives \(k=bt,l=at\). Summing
\[
 O\!\left(\frac h{\max(a^2,b^2)}\right)
\]
over directions gives \(O(h\log h)\) possibilities per row r, hence only \(O(h^2\log h)\) excluded triples. The remaining triples determine their right triangle and rectangle uniquely, so no event multiplicity remains.

Every event has probability
\[
 \frac1{\lfloor h/2\rfloor\lceil h/2\rceil^2}
 =\Theta(h^{-3}).
\]
This proves (1).

## 2. The clique obstruction is a necessary condition

All events in \(\mathcal A_h\) use the variable at column zero, so they form a clique in the shared-variable graph. Suppose an asymmetric local-lemma certificate assigned numbers \(0<x_E<1\). Its inequalities, after discarding neighbors outside this clique, would imply
\[
 \Pr(E)\le x_E\prod_{\substack{F\in\mathcal A_h\\F\ne E}}(1-x_F).
\]
Summing gives
\[
 \sum_{E\in\mathcal A_h}\Pr(E)
 \le
 \sum_E x_E\prod_{F\ne E}(1-x_F)
 \le1.
\tag{3}
\]
The middle expression is the probability of exactly one success among independent Bernoulli variables with parameters \(x_E\). Equation (1) contradicts (3).

For the clique-expansion criterion, the independent-set polynomial of this clique is \(1+\sum_E\mu_E\). Its corresponding inequalities imply
\[
 \sum_E\Pr(E)\le
 \frac{\sum_E\mu_E}{1+\sum_E\mu_E}<1,
\]
again contradicting (1). Equivalently, the clique restriction already fails the necessary clique inequality in the optimal dependency-graph region.

This first argument concerns the shared-variable graph. Many events sharing column zero prescribe the same row there, so the usual lopsided assignment graph need not contain this clique. The next argument addresses that refinement directly.

### 2.1 The incompatible-assignment graph also fails

Group the events by the even row r prescribed at column zero. Every pair from different groups has conflicting assignments there, so the natural incompatible-assignment graph contains all cross-group edges. Put
\[
 p_r=\sum_{\substack{E\in\mathcal A_h\\E\text{ prescribes }r}}\Pr(E).
\]
The fixed-corner rectangle bound gives, uniformly in r,
\[
 p_r=O((\log h)^2/h)=o(1),\qquad
 \sum_rp_r=\Omega((\log h)^2).
\tag{5}
\]

Here is a general necessary condition for a standard or cluster-expansion local-lemma certificate on such a graph. Let \(\mu_E>0\) be its weights, put \(M_r=\sum_{E\text{ in }r}\mu_E\), and \(M=\sum_rM_r\). The closed-neighborhood independent-set polynomial contains the empty set and every singleton from the other groups. Thus the cluster-expansion inequality implies
\[
 \Pr(E)\le\frac{\mu_E}{1+M-M_r}.
\]
The standard asymmetric criterion implies the same bound after setting \(\mu_E=x_E/(1-x_E)\), because its product denominator contains these singleton terms. Additional edges or neighboring events only strengthen the bound.

Summing over group r and rearranging gives
\[
 M_r\ge\frac{p_r}{1+p_r}(1+M).
\]
Summing again shows that
\[
 \sum_r\frac{p_r}{1+p_r}<1
\tag{6}
\]
is necessary. Equation (5) contradicts (6) for large h.

Therefore neither of these unthinned criteria works on the usual incompatible-assignment graph either. This remains a statement about this event representation and these criteria. Conditioning on an entire root neighborhood, changing variables, or proving a direct conditional extension estimate is not ruled out.

## 3. Why the completion-root subfamily looks better

There is a different family in [the relative-pressure proof](relative_sparse_defect_pressure.md): the defect column is the missing corner's column, and all three black corners lie in ordinary odd columns. Its incident probability at a fixed other column is bounded, rather than logarithmically divergent.

Put \(k=\lceil h/2\rceil\) and identify the odd rows with \([k]\). Fix a nonzero horizontal displacement d from the missing corner to one prescribed black side corner. If the missing row is w and the two vertical side increments are \(2a,2b\), orthogonality fixes the other horizontal increment to
\[
 -4ab/d.
\]
Thus the number of events in which the selected column is a side corner is at most
\[
 \sum_{a,b\ne0}(k-|a|-|b|)_+
 =4\binom k3.
\]
After dividing by \(k^3\), its incident probability is at most \(2/3+O(1/h)\). Divisibility and repeated-column exclusions only decrease this bound. At \(d=1\), divisibility is automatic and no repeated-column case occurs, so the leading constant \(2/3\) is attained.

If the selected column is the opposite diagonal corner, choose its row and the missing row in \(O(h^2)\) ways. The alternate diagonal has only \(h^{o(1)}\) possibilities by the sum-of-two-squares divisor bound, uniformly for the polynomial support span. Its incident probability is \(h^{-1+o(1)}\).

Hence the total completion-root incident probability is at most
\[
 2/3+o(1).
 \tag{7}
\]
This suggests that a one-heavy-variable clique argument might handle that subfamily. It cannot handle the complete sparse-profile event family by itself, because Section 1's black-root events are also necessary. In particular, removing the artificial thinning from only the previously selected completion-root events does not establish exact entropy capture of sparse-defect words.

