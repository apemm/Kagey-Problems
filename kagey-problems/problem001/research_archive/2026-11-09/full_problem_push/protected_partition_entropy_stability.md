# Entropy concentration of column phases in a protected row partition

9 November 2026. This note derives an entropy consequence of the independently reviewed [aggregate inverse theorem](protected_row_aggregate_inverse.md). The counting argument has also passed [independent review](rectangle_inverse_independent_audit.md).

Fix a height at which the row partition
\[
 c(y)=\kappa q(y)+\alpha y+\beta,\qquad q(y)=\binom y2\bmod2,
\]
is balanced, with \(\alpha=1\) when \(\kappa=0\). The matched column phases are
\[
 \mathcal P_\kappa=\{\kappa q(x)+\gamma x+\delta:\gamma,\delta\in\mathbb F_2\}.
\]
A sea word \(w_1,\ldots,w_h\) has phase \(t_x=c(w_x)\). Call its phase \(\varepsilon\)-far if its Hamming distance from every member of \(\mathcal P_\kappa\) is at least \(\varepsilon h\).

**Theorem.** For every fixed \(\varepsilon>0\), there is \(\gamma_\varepsilon>0\) such that, for all sufficiently large balanced heights, the number \(B_h(\varepsilon)\) of valid length-h sea words with \(\varepsilon\)-far phase satisfies
\[
 B_h(\varepsilon)\le \bigl((1/2-\gamma_\varepsilon)h\bigr)^h.
\tag{1}
\]
The same bound holds for all independent transversals of the singleton-rival hypergraph with such a phase. Thus it also holds under either the finite-board or normalized-support convention for valid sea words with the prescribed final axis-pair set F. An isolated finite singleton board without those fixed external axis-pair owners is a different model.

The statement counts all far phase words together. There is no separate factor \(2^h\) for choosing a phase profile.

## 1. A quantitative form of container stability

Let \(H=H_\pi\) be the four-uniform singleton-rival hypergraph on \([h]^2\), as defined in [the half-entropy bound](sea_entropy_half_container.md). Its estimates, uniformly over balanced row partitions, are
\[
 e(H)=\Theta(h^5\log h),\qquad
 \Delta_1=O(h^3\log h),\quad
 \Delta_2=O(h^2),\quad
 \Delta_3=O(h),\quad \Delta_4=1.
\tag{2}
\]
The [purification lemma](container_stability_reduction.md) and the aggregate inverse theorem imply the following quantitative compactness statement. For every \(\theta>0\), there are constants \(\eta,\delta>0\) and \(h_0\) such that, when \(h\ge h_0\), every \(C\subseteq[h]^2\) satisfying
\[
 |C|\ge(1/2-\eta)h^2,\qquad e(H[C])\le\delta h^5\log h
\tag{3}
\]
differs in at most \(\theta h^2\) cells from a protected product box
\[
 P=\{(x,y):c(y)=\kappa q(x)+\gamma x+\delta_0\}.
\tag{4}
\]
Here \(\delta_0\) is a phase bit, unrelated to the edge-density constant.

To justify the quantifiers, if this failed for some \(\theta\), choose a sequence with \(\eta,\delta\downarrow0\) and \(h\to\infty\). It would contradict the little-o structural theorem. There are only finitely many protected row laws, so the constants may be uniform over them.

Apply [Balogh--Morris--Samotij, Theorem 2.2](https://arxiv.org/html/1204.6530#S2.Thm2) to the increasing family
\[
 \mathcal F=\{U:e(H[U])>\delta h^5\log h\}.
\]
The minimum-size hypothesis follows from \(4e(H[U])\le |U|\Delta_1(H)\); the density hypothesis follows from (2). The codegree conditions hold with
\[
 p=\frac1{h(\log h)^{1/3}}.
\]
Consequently every independent transversal I has a fingerprint \(S\subseteq I\), of size
\[
 j\le s_h=O_{\varepsilon,\theta,\delta}
       \bigl(h/(\log h)^{1/3}\bigr)=o(h),
\]
and an associated container C with
\[
 I\setminus S\subseteq C,\qquad e(H[C])\le\delta h^5\log h.
\tag{5}
\]
The container depends only on S. A fingerprint has at most one cell in each column.

## 2. Counting the small containers

If \(|C|<(1/2-\eta)h^2\), the number of completions after specifying a j-cell fingerprint is at most
\[
 \left(\frac{(1/2-\eta)h^2}{h-j}\right)^{h-j}
\]
by arithmetic--geometric mean across the remaining columns. Summing over at most \(\binom hjh^j\) fingerprints of size j gives
\[
 \sum_{j\le s_h}\binom hjh^j
 \left(\frac{(1/2-\eta)h^2}{h-j}\right)^{h-j}
 \le \bigl((1/2-\eta+o(1))h\bigr)^h.
\tag{6}
\]
The factors \(h^j\) replace the h-sized choices from the removed columns; they do not produce an extra exponential factor.

## 3. A weighted count for the large containers

For a large C, choose one protected box P supplied by (3)--(4), using any fixed tie-breaking rule. In column x, write
\[
 a_x=|C_x\cap P_x|,\qquad b_x=|C_x\setminus P_x|.
\]
Then
\[
 \sum_xa_x\le h^2/2+O(h),\qquad
 \sum_xb_x\le\theta h^2.
\tag{7}
\]

If I has an \(\varepsilon\)-far phase, it uses at least \(\varepsilon h\) cells outside this P. At most j of them belong to its fingerprint. Weight an off-P choice by two. The number of possible remaining choices is therefore at most
\[
 2^{j-\varepsilon h}\prod_{\text{unfixed }x}(a_x+2b_x)
 \le
 2^{j-\varepsilon h}
 \left(\frac{(1/2+2\theta+O(1/h))h^2}{h-j}\right)^{h-j}.
\tag{8}
\]
This is just the generating-function bound for at least \(\varepsilon h-j\) off-P choices, followed by arithmetic--geometric mean. It remains valid if \(\varepsilon h-j<0\), although eventually \(j=o(h)\).

Sum (8) over fingerprints. Since \(s_h=o(h)\), the resulting hth root is at most
\[
 \bigl(2^{-\varepsilon}(1/2+2\theta)+o(1)\bigr)h.
\tag{9}
\]
Indeed, after extracting \(h^h\), the remaining fingerprint factor is bounded using
\[
 \frac1h\log\binom hj=o(1),\qquad
 \frac jh=o(1),\qquad
 -\left(1-\frac jh\right)\log\left(1-\frac jh\right)=o(1),
\]
uniformly for \(j\le s_h\).

Choose \(\theta>0\) small enough that
\[
 1/2+2\theta<2^{\varepsilon/2}/2.
\]
Then (9) is strictly below \(h/2\). Combining it with (6), and decreasing the fixed gap to absorb their sum, proves (1).

## 4. A positive density of far blocks has smaller entropy

Fix \(\varepsilon,\zeta>0\). Partition a long word of length m into \(b=\lfloor m/h\rfloor\) disjoint length-h blocks, leaving fewer than h columns. Translation preserves the family \(\mathcal P_\kappa\), since \(q(x+x_0)-q(x)\) is affine.

Let \(N_{h,m}(\varepsilon,\zeta)\) count valid sea words for which at least \(\zeta b\) of these blocks have \(\varepsilon\)-far phase. Let \(T_h\) count all independent transversals of H. The half-entropy bound gives
\[
 T_h\le((1/2+o_h(1))h)^h.
\]
Ignoring compatibility between blocks only increases the count. Choosing their far/nonfar statuses gives
\[
 N_{h,m}(\varepsilon,\zeta)
 \le h^h\,2^b\,
       B_h(\varepsilon)^{\zeta b}T_h^{(1-\zeta)b},
\tag{10}
\]
with harmless rounding of \(\zeta b\). Thus
\[
 \limsup_{h\to\infty}\limsup_{m\to\infty}
 \frac{N_{h,m}(\varepsilon,\zeta)^{1/m}}h
 \le (1/2-\gamma_\varepsilon)^\zeta(1/2)^{1-\zeta}
 <1/2.
\tag{11}
\]
In particular, for every fixed \(\varepsilon,\zeta>0\), these words have a fixed exponential growth gap below the canonical component for all sufficiently large balanced heights, since its Perron root is \(h/2-o(h)\).

The order of limits is explicit: h first determines a finite alphabet and block size, then the word length tends to infinity, and finally h tends to infinity.

## 5. Consequence for high-entropy stationary measures

Let \(\mu_h\) be any stationary measure on the sea shift in this protected row partition, with entropy rate
\[
 \mathsf h(\mu_h)\ge\log(h/2)-o_h(1).
\tag{12}
\]
This includes a measure of maximal entropy on any recurrent component whose Perron root is at least that of the canonical component.

Let \(p_h\) be the probability that a length-h phase block is \(\varepsilon\)-far. The entropy of that block is at most
\[
 H_2(p_h)+(1-p_h)\log T_h+p_h\log B_h(\varepsilon).
\]
It is at least \(h\,\mathsf h(\mu_h)\). Therefore
\[
 \mathsf h(\mu_h)
 \le \log h+\log(1/2+o_h(1))
 -p_h\log\frac{1/2+o_h(1)}{1/2-\gamma_\varepsilon}
 +\frac{\log2}{h}.
\tag{13}
\]
Equations (12)--(13) imply \(p_h=o_h(1)\).

Thus every asymptotically maximal component in a protected row partition has, with probability tending to one, board-sized phase blocks close to a matched protected phase. This is local phase concentration. Different blocks may follow different phases, and the theorem does not prove one global phase, irreducibility, or fixed-height dominance.

## 6. Overlapping windows identify phase domains

The local conclusion has a deterministic consequence. Fix \(0<\varepsilon<1/16\), \(h\ge32\), and put \(\ell=\lfloor h/4\rfloor\). For a phase word of length \(m\ge h\), inspect the length-h windows beginning at
\[
 1,\ 1+\ell,\ 1+2\ell,\ldots
\]
that lie in the word. Call a window good when it is within \(\varepsilon h\) changes of one matched protected phase, and let B be the number of bad windows.

Every good window has a unique matching phase. Indeed two distinct laws in \(\mathcal P_\kappa\) differ on at least half of any interval, up to one position. Two adjacent good windows must choose the same global law: their overlap has length at least \(3h/4\), and different laws would disagree there in at least \(3h/8-1>2\varepsilon h\) positions.

Assign to each length-\(\ell\) block the law of its good window. Consecutive good windows form runs with one common law. Fill each intervening run of bad blocks with either neighboring law, and extend a chosen law over the final fewer than h positions. This produces a piecewise protected phase with at most \(B+1\) boundaries between its laws, and Hamming distance at most
\[
 5\varepsilon m+\ell B+h
\tag{14}
\]
from the original phase word. Here \(h/\ell\le5\), so the sum of the good-window error bounds is at most \(5\varepsilon m\). A boundary means a change of the pair \((\gamma,\delta)\); a checkerboard law may change its bit at every column while having no such boundary.

For a stationary measure as in (12), the expected fraction of bad windows is \(p_h(\varepsilon)=o_h(1)\). Markov's inequality shows that, with probability at least \(1-\sqrt{p_h(\varepsilon)}\), their number is at most \(\sqrt{p_h(\varepsilon)}\) times the total number of inspected windows. On that event, (14) gives at most
\[
 (5\varepsilon+\sqrt{p_h(\varepsilon)})m+h
\]
errors and at most
\[
 5\sqrt{p_h(\varepsilon)}\,m/h+1
\]
phase boundaries.

A diagonal choice \(\varepsilon=\varepsilon_h\downarrow0\) with
\(p_h(\varepsilon_h)\to0\) therefore gives the following statement. As
\(h\to\infty\) and \(m/h\to\infty\), with probability tending to one the phase word is within \(o(m)\) edits of protected domains having \(o(m/h)\) boundaries. This permits long domains of different phases. It does not assign a fixed energetic cost to every individual changed column.

There is also a direct entropy consequence. A good length-h phase block has at most
\[
 4\sum_{j\le\varepsilon h}\binom hj
 \le \exp[hH_2(\varepsilon)+O(\log h)]
\]
possible values, while any phase block has at most \(2^h\). Hence the phase process has entropy rate at most
\[
 H_2(\varepsilon)+p_h(\varepsilon)\log2+o_h(1).
\tag{15}
\]
First let h grow and then let \(\varepsilon\downarrow0\). The phase-process entropy rate is \(o_h(1)\) for every family of measures satisfying (12).

