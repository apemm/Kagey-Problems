# Full protected-row pressure from one-sided roots and guarded witnesses

9 November 2026. The full sea shift for a balanced protected row partition has the same leading pressure as its best protected column phase. The proof combines the finite-block container gap with one-sided adaptive root families. The one-sided geometry is essential: enlarging an independently counted guard alone does not make a distance-from-guard-edge activity small.

Fix a balanced protected row law
\[
 c_0(y)=\kappa q(y)+\beta y+\eta,\qquad q(y)=\binom y2\bmod2,
\]
among the nonconstant protected row laws, at heights where it is balanced. Let
\(\mathcal X(c_0)=\{\kappa q(x)+\gamma x+\delta\}\)
be its matched protected phases. Let \(\rho(c_0,h)\) be the growth rate of the full normalized fixed-final-F sea shift, with arbitrary column phase, and let
\[
 \rho_0(c_0,h)=\max_{X\in\mathcal X(c_0)}\rho_{c_0,X}(h).
\]
Put \(\Lambda=1+\log h\).

**Theorem.**
\[
 \log\rho(c_0,h)
   =\log\rho_0(c_0,h)+o(\Lambda^4/h).
\tag{1}
\]
The limit is along balanced heights for the chosen row law. In particular, the previously proved protected quadratic-over-ordinary gap implies
\[
 \rho(c_{\rm Q},h)>\rho(c_{\rm O},h)
\]
for all sufficiently large h, where \(c_{\rm Q}=q(y)\) and \(c_{\rm O}=y\bmod2\). More precisely, their logarithmic gap is the protected gap plus \(o(\Lambda^4/h)\), and their growth-rate gap is \(\Theta(\Lambda^4)\).

Equation (1) concerns the full shifts for these specified row partitions. It does not identify the optimal balanced partition, prove uniqueness of a recurrent component, or give exact fixed-height Perron dominance.

## 1. Local witnesses with a fixed positive deficit

Partition a long word into aligned h-column blocks. End remainders cost only a fixed-height factor.

Choose a sufficiently small absolute epsilon_0. Call a block good if its phase is within epsilon_0 h positions of some matched protected phase. For large h this phase is unique, because distinct matched laws disagree on at least \(h/2-O(1)\) columns. Call all other blocks bad.

Two existing finite-block inputs are used:
\[
 T_h\le(h/2)^h e^{\eta_hh},\qquad \eta_h\longrightarrow0,
\tag{2}
\]
for the union of all valid h-block words, and
\[
 B_h(\epsilon_0)\le(h/2)^h e^{-\gamma h}
\tag{3}
\]
for the union of valid bad-block words, with a fixed \(\gamma>0\).
Both count all phase descriptions together. They hold for the fixed-final-F finite-block necessary language, by
[the half-entropy container bound](sea_entropy_half_container.md) and
[the protected phase entropy gap](protected_partition_entropy_stability.md).

A second witness is a pair of adjacent good blocks with different matched labels. Its union count is at most
\[
 (h/2)^{2h}e^{-\gamma' h}
\tag{4}
\]
for a fixed \(\gamma'>0\).

To see (4), fix the two labels and their error sets. Use the marked local wall family at physical scale ch, with its three black corners in the first block and its completion in the second. Restrict completion residues to those on which the two labels differ. Its marked mean is at least \(a h\), and its raw/conditional neighbor sums are small. Deleting geometries meeting either block's error set loses at most \(C\epsilon_0h\), by the bounded marked incidence at each prescribed column. Thus the valid count is at most the product alphabet count times \(e^{-a'h}\). Summing error descriptions costs at most
\(\exp(2hH_2(\epsilon_0)+O(1))\); summing the finitely many label pairs costs O(1). Choose epsilon_0 small enough that these losses are absorbed. Alphabet sizes h/2+O(1) change the two-block product by only \(e^{O(1)}\). This proves (4).

Let \(\gamma_0=\min(\gamma,\gamma')>0\). The order of choices is important: epsilon_0 is fixed first, then gamma_0 is fixed, and the guard parameter below is chosen afterward. No quantitative lower bound on gamma_0 as epsilon_0 tends to zero is assumed.

## 2. A deterministic guard decomposition

A local witness occupies one bad block or a pair of adjacent good blocks with different labels.

Fix a large integer D, to be chosen in Section 5. Choose a maximal set of witness starts separated by at least \(4D+10\) blocks. Let k be the number chosen. The selected witness units are disjoint.

Expand each selected start by \(4D+12\) blocks in both directions. Maximality ensures that these guards contain every local witness. Merge guard components across gaps of fewer than D blocks. The final guard set G contains at most
\[
 |G|\le C D k
\tag{5}
\]
blocks, apart from a bounded end correction. The merging adds at most D blocks per original gap and hence preserves (5).

Every remaining interval consists entirely of good blocks with one common matched phase. After absorbing short end intervals, each such interval has M blocks with \(M\ge D\). There are at most \(k+1\) remaining intervals.

For fixed selected starts and witness types, count the guard variables independently. Each selected witness retains its deficit from (3) or (4); every other guard block uses (2). Since the witness units are disjoint,
\[
 \#\{\hbox{guard words}\}
 \le (h/2)^{h|G|}
       \exp[-\gamma_0hk+\eta_hh|G|].
\tag{6}
\]
For fixed D and sufficiently large h, (5)--(6) give
\[
 \#\{\hbox{guard words}\}
 \le (h/2)^{h|G|}e^{-\gamma_0hk/2}.
\tag{7}
\]
Ignoring constraints between guard blocks only enlarges this count.

The number of selected-start/type descriptions is at most
\(\binom{\lceil m/h\rceil}{k}C^k\).
The constant phase labels of the remaining intervals contribute at most
\(4^{k+1}\). No separate phase-description factor is attached to guard words: (2)--(4) already count all their row words.

## 3. One-sided roots inside a good interval

Consider one remaining interval of M h-blocks, with common matched law X. Its error counts satisfy \(q_i\le\epsilon_0h\).

Use the density majorant from [adaptive local sparsity](adaptive_local_phase_sparsity.md), computed only over blocks in this interval:
\[
 Q_i=\max_j\min\!\left(q_j,h\left(\frac K{1+|i-j|}\right)^4\right),
 \quad L_i=\log(h/q_i),\quad L_i^*=\log(h/Q_i).
\tag{8}
\]
At each root column in block i, use
\[
 R_i=\left\lfloor\min\{c(h/Q_i)^{1/4},\,M/C_1\}\right\rfloor.
\tag{9}
\]

The geometry is now one-sided. Choose the completion row w in the central band \([h/3,2h/3]\), in the old selected row class, and take
\[
 U=(4ka,4kb),\qquad V=(4lb,-4la),
\tag{10}
\]
with primitive \(a,b\le R_i\) and the old scale intervals
\[
 h/(100b)\le k\le h/(50b),\qquad
 h/(100a)\le l\le h/(50a).
\]
Both horizontal components are positive. All three black corners lie strictly to the right of the completion. Reflect horizontally when the leftward available interval is longer.

For every root, one direction has at least Mh/2 available columns. Taking C_1 sufficiently large makes the complete support lie in the good interval, even when the root is adjacent to a guard edge. Vertical containment follows from the central row band.

Discard ka=lb, which would put two black corners in one column, and discard every support meeting an error column. The discarded equality family is lower order. The primitive harmonic count still gives \(\Theta(h^3\log^2R_i)\) events per root column before these deletions.

The fixed-cell/completion-column bound remains \(ChR^2\). In the opposite-corner case its equation is now \(ka+lb=d\); the solution progression and its \(O(h/(ab)+1)\) bound are unchanged. The one-/two-cell dyadic pressure sums remain \(O(\epsilon_0^{1/4})\) and \(O(\epsilon_0^{3/4})\). Three assignments determine the completion, so distinct events have no three-assignment overlap.

Every root support avoids every guard variable. Different good intervals have disjoint root-variable sets. Thus their counting is compatible with the independent guard count (7).

## 4. A common cap preserves the maximal-weight argument

Put \(T=\log(M/C_2)\), with constants adjusted so that T is positive for \(M\ge D\). The root mean in block i is at least a constant times
\[
 q_i\min\{(L_i^*)^2,T^2\}.
\]
The weighted maximal argument also gives
\[
 \sum_iq_i\min\{(L_i^*)^2,T^2\}
 \ge c\sum_iq_i\min\{L_i^2,T^2\}.
\tag{11}
\]

For completeness, set \(M_i=\min(L_i,T)\). If \(L_i^*<M_i/2\), a witness j in (8) has
\[
 L_j<M_i/2,\qquad
 M_i\ge8\log((1+|i-j|)/K).
\]
Since T is common throughout the interval, \(M_j=L_j\). Also
\(q_iM_i^2\le h e^{-M_i}M_i^2\).
The same distance sum as in the uncapped proof bounds all bad weight charged to j by
\(CK\epsilon_0^{3/4}q_jM_j^2\). For small epsilon_0 this absorbs at most half the total. On the remaining indices, the capped root weight is at least \(q_iM_i^2/4\). This proves (11).

Retain any protected bulk subfamily whose supports lie in this interval and avoid error columns. List that bulk first, then the roots. The exact conditional lower-probability lemma gives the additional factor
\[
 \exp\!\left[-c\sum_iq_i\min\{\log^2(h/q_i),\log^2M\}\right].
\tag{12}
\]
The old bulk extension bounds through prescribed root cells are unchanged.

Deleting error columns from the retained bulk costs at most
\(C|S|\Lambda^4/h\), and alphabet changes cost at most \(C|S|/h\). Both are absorbed into (12) for fixed D and large h.

For each block, use \(e^{-\min(a,b)}\le e^{-a}+e^{-b}\). The error-description activity is therefore bounded by
\[
 1+\sum_{1\le q\le\epsilon_0h}\binom hq
       e^{-cq\min(\log^2(h/q),\log^2M)}
 \le e^{-c'\log^2h}+(1+e^{-c'\log^2M})^h.
\]
Consequently the logarithmic activity for the whole good interval is at most
\[
 M e^{-c'\log^2h}
   +C hM e^{-c'\log^2M}.
\tag{13}
\]

This is the point at which the one-sided family removes the guard-edge problem. The cutoff is determined by the entire good-interval length M, not by the root's distance from its nearest guard.

## 5. Choose guards, then retain the leading bulk

Choose D so large that
\[
 \sup_{M\ge D} C M e^{-c'\log^2M}<\gamma_0/100.
\tag{14}
\]
This is possible because \(M e^{-c'\log^2M}\to0\). Summing (13) over at most \(k+1\) good intervals costs at most
\[
 (m/h)e^{-c'\log^2h}+\gamma_0 h k/50+O_h(1).
\tag{15}
\]
Thus most of the guard deficit in (7) remains available. This choice does not compare gamma_0 with any power of epsilon_0.

Fix \(\delta>0\). In each good interval retain the minimal protected bulk of span at most \(H_\delta=Ch^{2-\delta}\) from
[the leading-pressure truncation](protected_domain_leading_pressure.md).
It omits only
\[
 C\delta\Lambda^4/h+o_\delta(\Lambda^4/h)
\]
mean per column. A boundary removes at most
\(CH_\delta\Lambda^4/h\) retained mean.

Apply Suen to the retained bulk before the conditional root count, preserving coefficient one on its mean. The generic guard baseline \((h/2)^{h|G|}\), compared with the best protected pressure, loses at most \(C Dk\Lambda^4\), because \(\rho_0\ge h/2-C\Lambda^4\).

For a fixed selected-witness description, after summing good-interval error sets, the logarithmic count is at most
\[
 \begin{split}
 m\log\rho_0
 &+C\delta m\Lambda^4/h+o_\delta(m\Lambda^4/h)\\
 &+CkH_\delta\Lambda^4/h
  +CDk\Lambda^4
  -c\gamma_0hk
  +(m/h)e^{-c'\log^2h}+O_h(1).
 \end{split}
\tag{16}
\]
For each fixed delta and D, both positive per-witness terms are smaller than its deficit:
\[
 H_\delta\Lambda^4/h=O(h^{1-\delta}\Lambda^4)=o(h),
 \qquad D\Lambda^4=o(h).
\]
Thus, for sufficiently large h, (16) is at most
\[
 m\log\rho_0+C\delta m\Lambda^4/h
   +o_\delta(m\Lambda^4/h)-c'\gamma_0hk+O_h(1).
\tag{17}
\]
This estimate remains valid if guards occupy most or all columns. The lower bound used for the retained bulk mean may then be negative, but substituting such a lower bound into the avoidance upper bound only weakens that bound.

Sum the selected-start/type and interval-label descriptions directly:
\[
 \sum_k\binom{\lceil m/h\rceil}{k}C^k e^{-c'\gamma_0hk}
 \le (1+C e^{-c'\gamma_0h})^{\lceil m/h\rceil}.
\]
Its logarithmic growth contribution is \(O(h^{-1}e^{-c'\gamma_0h})\), much smaller than \(\Lambda^4/h\). Hence the full shift has rate at most
\[
 \log\rho_0+C\delta\Lambda^4/h+o_\delta(\Lambda^4/h).
\tag{18}
\]

Take h to infinity first and then delta to zero. The full shift contains every protected phase, so the opposite inequality is immediate. This proves (1).

## 6. Consequences and remaining questions

The proof compares all column phases for a fixed balanced protected row partition. The established protected constants therefore describe the leading full-shift pressure for ordinary and quadratic row partitions, and the quadratic row partition eventually has strictly greater full sea entropy than ordinary parity.

The theorem does not address row partitions differing from protected ones, except through earlier separate perturbation results. It also leaves exact recurrent-component dominance and insertion into every maximal component open. Those questions require more than the leading-pressure identity (1).

The full argument passed [independent adversarial review](full_protected_row_pressure_independent_audit.md).

