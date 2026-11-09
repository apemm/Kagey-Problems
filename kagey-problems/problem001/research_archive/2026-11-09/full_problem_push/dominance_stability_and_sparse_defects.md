# What container stability gives for general sea dominance

9 November 2026. This note records two rigorous consequences of the sharp entropy bound and the affine-parity capture theorem. Independent review checked the parity-template recurrences, defect cuts, and stationary entropy bound. They constrain a possible competing component, but do not establish general dominance.

The sources are [the container entropy proof](sea_entropy_half_container.md), [its geometric supersaturation input](entropy_supersaturation.md), and [dense residue entropy capture](dense_residue_entropy_capture.md). Throughout the last two sections, the row partition is ordinary parity and \(h\) is sufficiently large for the strict affine-capture theorem.

## 1. Containers with little mixing inside columns

Fix any balanced row partition \(\pi\). For a cell set \(U\subseteq[h]^2\), let \(a_x,b_x\) be its two class counts in column \(x\), and put
\[
 M_\pi(U)=\sum_{x=1}^h a_xb_x.
\]

**Mixing supersaturation.** For each fixed \(\delta>0\), there is \(c_\delta>0\) such that
\[
 M_\pi(U)\ge\delta h^3
 \quad\Longrightarrow\quad
 e(H_\pi[U])\ge c_\delta h^5\log h
\tag{1}
\]
for all sufficiently large \(h\), uniformly over balanced partitions.

Indeed, use the cross-partition intersections \(B_s\) from the supersaturation proof. Their total size is \(2M_\pi(U)\). At least \(c\delta h\) of them have size at least \(c\delta h^2\). The rotated-lattice rectangle lemma gives \(c_\delta h^4\log h\) rectangles for each such shift, and each resulting four-cell support has at most four descriptions. The density assumption \(|U|>(1/2+\varepsilon)h^2\) was only one way to make \(M_\pi(U)\) large; it is unnecessary for (1).

Apply the same [Balogh–Morris–Samotij container theorem](https://arxiv.org/html/1204.6530#S2.Thm2) to the increasing family
\[
 \mathcal F_\delta=\{U:M_\pi(U)\ge\delta h^3\}.
\]
Its members have size at least \(4\delta h^2\), since \(a_xb_x\le h(a_x+b_x)/4\). Thus the required positive lower bound on member sizes holds. The degree estimates and \(p=1/[h(\log h)^{1/3}]\) are unchanged.

Every independent transversal has a fingerprint of size
\[
 O_\delta\bigl(h/(\log h)^{1/3}\bigr)
\]
and a deterministic remainder container \(C\) with
\[
 M_\pi(C)<\delta h^3.
\tag{2}
\]
Let \(c_x=\min(a_x,b_x)\) for this container. By Cauchy–Schwarz,
\[
 \sum_x c_x
 \le\sqrt{h\sum_x c_x^2}
 \le\sqrt{hM_\pi(C)}
 <\sqrt\delta\,h^2.
\tag{3}
\]
Delete the minority class in each column. At most \(\sqrt\delta h^2\) cells are deleted, and the remainder uses only one partition class in each column. In particular,
\[
 |C|\le \lceil h/2\rceil h+\sqrt\delta\,h^2.
\]

This is stability of the **containers**. Their columnwise majority-class template can depend on the fingerprint. Equation (3) alone does not imply an affine parity law or an extension to the canonical component.

## 2. Exact classification of complete parity boxes

For a binary word \(t=(t_1,\ldots,t_m)\), define the complete parity box
\[
 U_t=\{(x,r):1\le x\le m,\ 1\le r\le h,\ r\equiv t_x\pmod2\}.
\]
Use the four-cell singleton-rival hypergraph on the actual \(h\times m\) board.

**Proposition.** If \(h\ge6\) and \(m\ge5\), then \(U_t\) is independent in this hypergraph if and only if
\[
 t_x=\alpha x+\beta\pmod2
\tag{4}
\]
for some \(\alpha,\beta\in\{0,1\}\).

The forward implication follows from two small rectangles. The adjacent vectors
\[
 (1,2),\quad (2,-1)
\]
give four distinct columns \(i,i+1,i+2,i+3\). If the XOR of \(t\) on these columns is odd, compare it with the four corner-row parities of this rectangle. The rectangle's own parity XOR is even. Hence either that parity pattern or its complement agrees with \(t\) at exactly three corners. Two consecutive vertical translations fitting in the board realize both choices. Replacing the unmatched fourth corner by a row of parity \(t\) in its column gives a hyperedge in \(U_t\). Therefore
\[
 t_i+t_{i+1}+t_{i+2}+t_{i+3}=0.
\tag{5}
\]
The adjacent vectors
\[
 (1,3),\quad(3,-1)
\]
have vertical span four and give columns \(i,i+1,i+3,i+4\). The same argument, valid for \(h\ge6\), gives
\[
 t_i+t_{i+1}+t_{i+3}+t_{i+4}=0.
\tag{6}
\]
Writing \(d_i=t_i+t_{i+1}\), these say \(d_i=d_{i+2}\) and \(d_i=d_{i+3}\) whenever the indices fit. For \(m\ge5\), the step-two and step-three relations connect all \(d_1,\ldots,d_{m-1}\). Thus they are constant, proving (4).

Conversely, three corners whose row parities obey (4) have a fourth corner obeying the same law, because both coordinates satisfy the parallelogram identity. Its column contains only rows of that parity in \(U_t\), so no singleton-rival support can be present.

There is a quantitative version. Let \(D(t)\) count the violated equations (5) and (6). Suppose \(U\subseteq U_t\) omits \(M=|U_t\setminus U|\) cells. For all sufficiently large \(h\), there are absolute constants \(c,C>0\) with
\[
 e(H_{\rm parity}[U])\ge c h^2D(t)-ChM.
\tag{7}
\]
For each violated equation, one parity of the vertical translation gives at least \(ch\) placements matching exactly three corners; the replacement column contributes at least \(ch\) rows. Supports from different equations have different four-column sets, so they do not overlap. A deleted cell destroys at most \(Ch\) of these supports: it lies in only constantly many of the designated four-column windows, and within one window it is either an original corner, fixing the translation, or the replacement point, allowing only \(O(h)\) translations. This proves (7).

In particular, an independent \(U\) satisfies \(D(t)\le CM/h\). A nearly complete independent parity box therefore has few local parity-law violations.

The current containers need not be independent. Their edge bound is measured against \(h^5\log h\), whereas (7) detects local template violations at the \(h^3\) scale. Passing from (2) to nearly affine templates would require an additional argument at this finer scale. The complete-box proposition does not supply it.

## 3. A fixed-height entropy gap for sparse parity defects

Let
\[
 r_h=\max_{\alpha,\beta}\rho_{\alpha,\beta}(h)
 <\lambda_*(h).
\]
Choose any \(\tau\) with \(r_h<\tau<\lambda_*(h)\). Let \(N_{\rm aff}(n)\) count valid normalized-support sea words of length \(n\) satisfying at least one of the four affine parity laws. Since these are finite-type languages with exponential rate \(r_h\), there is a finite constant \(C=C_h(\tau)\ge1\) such that
\[
 N_{\rm aff}(n)\le C\tau^n
 \qquad(n\ge1).
\tag{8}
\]
The constant is effective from the four finite transition matrices. For example, a convergent matrix resolvent at \(1/\tau\), including their finite initial prefixes, bounds the sum of \(N_{\rm aff}(n)\tau^{-n}\) and hence gives a valid \(C\).

For a sea word \(w_1\cdots w_m\), put
\[
 D_i(w)=1_{\{w_i\not\equiv w_{i+2}\pmod2\}},
 \qquad 1\le i\le m-2.
\tag{9}
\]
These are defects from a period-two parity law. If the defect set has size \(k\), cut after \(i+1\) for each defect \(i\). Every resulting segment has period-two parity and therefore an affine parity law. Each segment is itself an admissible normalized-support sea word. Given the defect set, (8) bounds the number of possible words by \(C^{k+1}\tau^m\). Consequently
\[
 \#\{w:\text{at most }k\text{ defects}\}
 \le C\tau^m\sum_{j=0}^k\binom{m-2}{j}C^j.
\tag{10}
\]

For any \(k=o(m)\), the sum on the right is \(\exp(o(m))\). The exponential rate of words with a sublinear number of defects is therefore at most \(r_h\), by letting \(\tau\downarrow r_h\). In particular, bounded parity defects cannot produce a competing exponential rate.

There is a useful measure form, which does not assume that every path has few defects. Let \(\mu\) be any stationary sea measure, and let
\[
 \delta=\mu(w_0\not\equiv w_2\pmod2).
\]
Use natural logarithms and write \(H_2(u)=-u\log u-(1-u)\log(1-u)\). The entropy of the defect vector is at most \((m-2)H_2(\delta)\). Conditional on that vector, (8) bounds the word entropy by \(m\log\tau+(k+1)\log C\). Dividing by \(m\) and taking the limit gives
\[
 h_\mu\le\log\tau+H_2(\delta)+\delta\log C.
\tag{11}
\]

Choose \(0<\delta_h<1/2\) sufficiently small that
\[
 H_2(\delta_h)+\delta_h\log C
 <\log(\lambda_*/\tau).
\tag{12}
\]
The left side is increasing on \([0,1/2]\). Every stationary sea measure of defect frequency at most \(\delta_h\) then has entropy strictly below \(\log\lambda_*\).

Thus a recurrent component with Perron root at least \(\lambda_*\) must have a maximal-entropy stationary measure with defect frequency greater than \(\delta_h\). This includes periodic irreducible components: their stationary Parry measure still exists and has entropy equal to the logarithm of the Perron root.

The gap \(\delta_h\) is positive and computable at each fixed height where affine capture holds. No useful uniform lower bound in \(h\) is proved here. Positive-density mixed-parity components remain the unresolved case.

