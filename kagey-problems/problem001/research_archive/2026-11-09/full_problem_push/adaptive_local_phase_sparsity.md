# Adaptive local-density pressure with a fixed sparsity cap

9 November 2026. The direction cutoff can vary with the local error density. A weighted maximal inequality then recovers the full blockwise entropy cost. This removes the vanishing-density assumption from the earlier uniformly locally sparse theorem.

Fix a protected row/column pair \((c_0,X)\), with the same normalized fixed-final-F convention as [the uniform local theorem](uniform_local_phase_sparsity.md). Partition the column line into aligned blocks of h columns. For a phase-error set S, let
\[
 q_i=|S\cap I_i|.
\]
Empty blocks are omitted from sums. Initially keep S a full support collar away from both finite ends.

**Theorem.** There are absolute constants \(\epsilon_0,c,H>0\) such that, if \(h\ge H\) and
\[
 q_i\le\epsilon_0h\quad\hbox{for every }i,
\tag{1}
\]
then
\[
 Z_{X,S}(m)\le Z_X(m)
 \exp\!\left[-c\sum_iq_i\log^2(h/q_i)\right].
\tag{2}
\]
Consequently the union of all profiles satisfying (1) has exponential growth
\[
 \rho_X(h)\le\rho_{\rm cap}(h)
 \le\rho_X(h)\exp\!\left[h^{-1}e^{-c\log^2h}\right].
\tag{3}
\]
Changing the constant c absorbs finite ends and integer block remainders. In particular, this entire class has the same protected pressure through the leading \(\log^4h/h\) term.

## 1. A density majorant adapted to the geometric radius

Choose a large absolute K. For every occupied block define
\[
 Q_i=\max_j\min\!\left(q_j,\,
             h\left(\frac K{1+|i-j|}\right)^4\right),
 \qquad L_i=\log(h/q_i),\qquad L_i^*=\log(h/Q_i).
\tag{4}
\]
The maximum ranges over occupied blocks. Thus
\[
 1\le q_i\le Q_i\le\epsilon_0h,\qquad L_i^*\le L_i.
\]
Choose a small absolute c_0 and set
\[
 R_i=\left\lfloor c_0(h/Q_i)^{1/4}\right\rfloor.
\tag{5}
\]
Taking epsilon_0 small ensures R_i exceeds the fixed minimum needed by the primitive harmonic estimate.

A root in block i uses the primitive family (7)--(8) from the uniform local theorem, with cutoff R_i. All its required columns lie within \(ChR_i\). Choose c_0 so that
\[
 CR_i+2<\tfrac K2(h/Q_i)^{1/4}.
\tag{6}
\]
If a block j in this neighborhood had \(q_j>Q_i\), both entries in the minimum defining Q_i would exceed Q_i, a contradiction. Hence every block seen by this root has \(q_j\le Q_i\).

Delete ka=lb and every geometry whose black columns meet S. The crude \(ChR_i^2\) completion-column count gives a lost probability mean at most
\[
 C(Q_i/h)R_i^3\le C(Q_i/h)^{1/4}.
\tag{7}
\]
The remaining mean at each root column is therefore at least
\[
 c\log^2(h/Q_i)=c(L_i^*)^2.
\tag{8}
\]

## 2. All density levels coexist in one local-lemma family

Group roots according to dyadic Q-levels \(Q\le Q_i<2Q\). The cutoff at that level is at most \(C(h/Q)^{1/4}\). Any physical block containing level-Q roots has at most 2Q such roots, because \(q_i\le Q_i\).

At a fixed free column, only \(O(R)\) blocks of that level can contribute. The completion-column bound \(ChR^2\) therefore bounds both raw incident mass and compatible one-cell conditional mass by
\[
 C(Q/h)R^3\le C(Q/h)^{1/4}.
\tag{9}
\]
The two-fixed-cell/completion-column bound O(1) gives compatible mass at most
\[
 C(Q/h)R\le C(Q/h)^{3/4}.
\tag{10}
\]
Summing the dyadic levels up to \(\epsilon_0h\) gives
\[
 C\epsilon_0^{1/4}+C\epsilon_0^{3/4}.
\tag{11}
\]
This is a geometric sum, not a logarithmic loss.

Distinct root events cannot share all three assignments, because the three black corners determine their unique completion. The unchanged protected bulk has the same vanishing extension bounds as before. Choose epsilon_0 small and then h large. The joint unthinned local-lemma criterion and conditional lower-probability estimate hold uniformly across all levels.

Retaining old bulk whose black columns avoid S, listing it first, and then listing all roots gives the extra factor
\[
 \exp\!\left[-c\sum_iq_i(L_i^*)^2\right].
\tag{12}
\]

## 3. The weighted maximal inequality

We claim that, after reducing epsilon_0,
\[
 \sum_iq_i(L_i^*)^2\ge\frac18\sum_iq_iL_i^2.
\tag{13}
\]
Call i bad if \(L_i^*<L_i/2\). For each bad i choose a witnessing j in (4). Then
\[
 L_j<L_i/2,\qquad
 1+|i-j|<K e^{L_i/8}.
\tag{14}
\]
Thus, with \(d=|i-j|\),
\[
 L_i\ge\max\{2L_j,\ 8\log((d+1)/K)\}.
\tag{15}
\]
The function \(e^{-u}u^2\) decreases for \(u\ge2\). Since \(q_i=h e^{-L_i}\), the total bad weight charged to a fixed j is at most
\[
 Ch\sum_{d\ge0}
 e^{-\max(2L_j,\,8\log((d+1)/K))}
 \max(2L_j,\,8\log((d+1)/K))^2.
\tag{16}
\]
Split this sum at \(d+1=K e^{L_j/4}\). The initial segment has at most \(CKe^{L_j/4}\) terms, each at most \(Ce^{-2L_j}L_j^2\). The remaining sum is bounded by the integral of
\(K^8d^{-8}\log^2(d/K)\). Both contributions are at most
\[
 CK h e^{-7L_j/4}L_j^2
 =CK e^{-3L_j/4}q_jL_j^2
 \le CK\epsilon_0^{3/4}q_jL_j^2.
\tag{17}
\]
Choose epsilon_0 so that the last coefficient is at most 1/2. Summing over j shows that bad indices carry at most half of \(\sum q_iL_i^2\). On every remaining index, \((L_i^*)^2\ge L_i^2/4\). This proves (13).

No assumption on the distances between occupied blocks enters this inequality.

## 4. Restore the exact reference and sum all profiles

Restoring omitted old bulk and comparing alphabet sizes costs
\[
 \exp(C|S|\Lambda^4/h).
\]
Since \(L_i\ge\log(1/\epsilon_0)>0\), this is absorbed into (12)--(13) for large h. Equation (2) follows.

For a block with q errors there are \(\binom hq\) choices. Since
\[
 \binom hq\le(eh/q)^q,
\]
choosing epsilon_0 smaller if necessary gives
\[
 \binom hq e^{-cq\log^2(h/q)}
 \le e^{-c' q\log^2(h/q)}
 \quad(1\le q\le\epsilon_0h).
\]
The function \(q\log^2(h/q)\) increases on this range. Its minimum is \(\log^2h\), attained at q=1. Therefore
\[
 \sum_{1\le q\le\epsilon_0h}
 \binom hq e^{-cq\log^2(h/q)}
 \le e^{-c''\log^2h}.
\tag{18}
\]
Overcounting all block choices independently proves (3).

The exact-reference argument uses full support collars. For unrestricted finite ends, trim collars rounded to the protected phase period and use bounded fixed-height partition-function shifts. The resulting factor is independent of m and does not change (3).

## 5. Consequence and scope

For a fixed protected law, an arbitrary phase profile whose error count is at most a sufficiently small fixed fraction in each aligned h-block has only a superpolynomial correction to the exact protected growth. This is stronger than requiring an error density tending to zero at a prescribed rate.

It does not yet control domains with different protected base laws. Applying the cutoff near a wall requires a distance truncation and a separate summation of the resulting near-wall error activity. Nor does it prove that every phase profile can be represented by such domains.

The complete proof passed [independent review](adaptive_local_sparsity_independent_audit.md).

