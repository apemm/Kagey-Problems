# An entropy gap for nonprotected bounded-period profiles

9 November 2026. The periodic rectangle amplification and the container theorem give a fixed positive entropy gap for every nonprotected profile of bounded period. Sections 1--3 have passed two independent reviews; the robustness argument and unknown-partition corollary in Sections 4--5 have also passed independent review. The argument intersects containers with the profile box; it does not assume that containers are independent.

Fix an even period P. Let c,t be P-periodic binary functions, with c balanced over one period. At height h assume that the restriction of c is a balanced row partition, and consider valid seas satisfying
\[
 c(w_x)=t(x)
\tag{1}
\]
in every column. Let \(r_{c,t}(h)\) denote their exponential growth rate, allowing the finitely many horizontal shifts of t if desired.

**Theorem.** There is an absolute \(b>0\) such that, for every fixed P, all sufficiently large admissible heights h have the following property: if c,t are not a protected pair with a common quadratic coefficient, then
\[
 r_{c,t}(h)\le\left(\frac12-\frac b{P^6}\right)h.
\tag{2}
\]
The height threshold may depend on P. The statement is uniform over the finitely many profiles with that period.

## 1. Every small-edge container loses a positive part of the profile box

Let W be the full row-class box (1) on h consecutive columns. Every horizontal phase of t is still nonprotected. The [periodic amplification theorem](periodic_rectangle_amplification.md) and the multiplicity estimate in [the container reduction](container_stability_reduction.md) give
\[
 e(H_\pi[W])\ge aP^{-6}h^5\log h
\tag{3}
\]
for an absolute \(a>0\), once h is large. Here \(H_\pi\) is the four-cell singleton-rival hypergraph, whose uniform estimates are
\[
 e(H_\pi)\asymp h^5\log h,\qquad
 \Delta_1(H_\pi)\le A h^3\log h
\tag{4}
\]
for an absolute A.

Apply [Balogh--Morris--Samotij, Theorem 2.2](https://arxiv.org/html/1204.6530#S2.Thm2) to the increasing family
\[
 \mathcal F_P=
 \{U:e(H_\pi[U])\ge(a/2)P^{-6}h^5\log h\}.
\tag{5}
\]
Its density parameter is a positive constant depending on P. Its members also have size at least \(cP^{-6}h^2\), because
\(4e(H_\pi[U])\le |U|\Delta_1(H_\pi)\). Thus the theorem's minimum-size hypothesis is satisfied after choosing the same parameter smaller if necessary.

The codegree estimates from [the sea entropy proof](sea_entropy_half_container.md) apply with
\[
 p=\frac1{h(\log h)^{1/3}}.
\]
Every independent set I has a fingerprint \(S\subseteq I\) with
\[
 |S|\le s_h=O_P\bigl(h/(\log h)^{1/3}\bigr)=o_P(h),
 \qquad I\setminus S\subseteq C(S),
\tag{6}
\]
where \(C(S)\notin\mathcal F_P\).

For a transversal \(I\subseteq W\), replace its container by \(C(S)\cap W\). By (3)--(5), deleting \(W\setminus C(S)\) destroys at least \((a/2)P^{-6}h^5\log h\) edges. Each deleted vertex destroys at most \(\Delta_1(H_\pi)\) edges. Hence
\[
 |W\setminus C(S)|\ge\frac a{2A}P^{-6}h^2.
\tag{7}
\]
Also \(|W|=h^2/2+O(h)\), because the row partition at the chosen height is balanced. Absorbing the rounding error, there is an absolute \(b_0>0\) such that
\[
 |C(S)\cap W|
 \le \left(\frac12-b_0P^{-6}\right)h^2
 =:\alpha_P h^2.
\tag{8}
\]

## 2. Count transversals while retaining their fingerprints

A size-j fingerprint of a transversal occupies j distinct columns and has at most
\[
 \binom hj h^j
\]
possible values. Once it is fixed, the remaining \(h-j\) selected cells lie in \(C(S)\cap W\). The arithmetic-geometric mean inequality bounds their number by
\[
 \left(\frac{\alpha_Ph^2}{h-j}\right)^{h-j}.
\]
Thus the number \(T_{c,t}(h)\) of valid length-h blocks is at most
\[
 \sum_{j=0}^{s_h}
 \binom hj h^j
 \left(\frac{\alpha_Ph^2}{h-j}\right)^{h-j}.
\tag{9}
\]
For fixed P, \(s_h=o(h)\). Dividing each summand by \(h^h\) shows that its h-th root is at most \(\alpha_P+o_P(1)\). Therefore
\[
 T_{c,t}(h)^{1/h}\le(\alpha_P+o_P(1))h.
\tag{10}
\]
There are only P possible initial phases; the same bound holds uniformly for all of them. Splitting an arbitrarily long sea into consecutive blocks of length h gives the same upper bound for its exponential rate. Reduce \(b_0\) by a factor of two to absorb the final error and obtain (2).

## 3. A within-partition dominance consequence

Now take the ordinary parity row partition, at any height. Fix a positive integer \(P_0\), and let \(\mathcal L_{\le P_0}\) be the union of valid sea languages whose row-parity sequence has a period at most \(P_0\). There are finitely many such profiles.

An affine parity profile
\[
 t_x=\gamma x+\delta
\]
belongs to the protected affine family. Its entropy is strictly below the canonical component radius \(\lambda_*(h)\), for sufficiently large h, by [the exact entropy-capture theorem](dense_residue_entropy_capture.md).

For every other profile of period \(p\le P_0\), use the common even period
\(\operatorname{lcm}(2,p)\le2P_0\) in (2). Its entropy is at most
\[
 \left(\frac12-\frac b{(2P_0)^6}\right)h.
\]
The canonical lower bound
\[
 \lambda_*(h)\ge h/2-O(\log^4h)
\]
eventually exceeds this for each fixed \(P_0\). Taking the maximum over the finite collection gives
\[
 \rho(\mathcal L_{\le P_0})<\lambda_*(h)
 \qquad\text{for all sufficiently large }h.
\tag{11}
\]

In particular, every recurrent sea component confined to a fixed bounded-period parity profile, or to finitely many shifts of such profiles, is strictly subdominant to the canonical component at sufficiently large height.

This does not prove general component dominance. A competing component may generate parity profiles with no fixed period bound; neither (2) nor (11) controls that possibility. Also, the height threshold in (11) depends on the chosen period bound.

## 4. Robustness under an arbitrary sparse set of phase changes

For every fixed nonprotected P-periodic pair c,t above, there are constants
\(\delta_P,\gamma_P>0\) such that the language of valid sea words whose phase differs from t in at most \(\delta_Pm\) positions has growth rate at most
\[
 (1/2-\gamma_P)h
\tag{12}
\]
for all sufficiently large admissible heights. No spacing, cluster-size, or periodicity condition is imposed on the changed positions. The constants may be chosen with
\[
 \gamma_P\ge cP^{-6},\qquad
 \delta_P\ge\frac{cP^{-6}}{\log(P+2)}
\tag{13}
\]
after decreasing an absolute c. The height threshold still depends on P.

Here is a more general argument that will also be used below. Suppose a family of base profiles has, in every length-h block and every starting phase, a uniform lower bound
\[
 e(H_\pi[W_{\rm base}])\ge a_0h^5\log h
\tag{14}
\]
with fixed \(a_0>0\). Changing D phase columns changes at most Dh cells of the box. By the maximum-degree bound (4), it changes the edge count by at most
\[
 A D h^4\log h.
\]
Thus for some fixed \(\eta_0>0\), every profile differing from the base in at most \(\eta_0h\) positions retains half of (14). The container-intersection proof of Sections 1--2 then gives a uniform length-h bound
\[
 (\alpha h)^h,\qquad \alpha=1/2-\epsilon_0<1/2,
\tag{15}
\]
for every such fixed perturbed profile, once h is large.

For arbitrary length-h blocks, the uniform half-entropy theorem gives
\[
 (\beta h)^h,\qquad \beta=1/2+\epsilon_0/4,
\tag{16}
\]
for sufficiently large h. Consider a fixed length-m phase profile with at most \(\delta m\) changes from the base. Partition it into length-h blocks. At most
\[
 (\delta/\eta_0)\lfloor m/h\rfloor+O_h(1)
\]
blocks can have more than \(\eta_0h\) changes. Ignore compatibility across blocks and use (15) on the others, and (16) on these exceptional blocks.

There are at most
\[
 \sum_{j\le\delta m}\binom mj
 =\exp[(H_2(\delta)+o_m(1))m]
\]
possible phase changes, for fixed \(0<\delta<1/2\). Hence the full language has growth rate at most
\[
 h\exp\left[
  \log\alpha+
  \frac{\delta}{\eta_0}\log\frac{\beta}{\alpha}
  +H_2(\delta)\right].
\tag{17}
\]
Choose \(\delta>0\) sufficiently small. The expression is then strictly below \(h/2\), proving (12).

For the P-periodic application, (3) allows
\(\eta_0\asymp P^{-6}\) and \(\epsilon_0\asymp P^{-6}\).
For \(0<\epsilon_0\le1/10\),
\[
 \log\alpha\le\log(1/2)-2\epsilon_0,\qquad
 \log(\beta/\alpha)\le4\epsilon_0.
\]
Take \(\delta\le\eta_0/8\) and \(H_2(\delta)\le\epsilon_0/2\).
Equation (17) then has logarithm at most
\(\log(h/2)-\epsilon_0\). Such a choice gives (13).

This is a neighborhood of a nonprotected base profile. A large domain of a different protected phase is not covered by a claim that every changed column has a fixed cost.

## 5. A partial comparison for arbitrary balanced row partitions

The same robust argument now has an application without a periodicity assumption on the row partition.

Fix \(\varepsilon>0\). Let c be any balanced row coloring on \([1,h]\), and let
\[
 t_0(x)=\kappa q(x)+\gamma x+\delta_0
\]
be a protected column phase. Suppose c has Hamming distance at least \(\varepsilon h\) from every matched row law
\[
 c_0(y)=\kappa q(y)+\alpha y+\beta,
 \qquad \alpha=1\text{ if }\kappa=0.
\tag{18}
\]
Then there are constants \(\delta_\varepsilon,\gamma_\varepsilon>0\), independent of c and h, such that for all sufficiently large h the valid sea words whose phase differs from \(t_0\) in at most \(\delta_\varepsilon m\) columns have growth rate at most
\[
 (1/2-\gamma_\varepsilon)h.
\tag{19}
\]
The distance in (18) is measured from the indicated laws even when one law is not exactly balanced at a particular finite height.

To obtain (14), first suppose \(t_0\) is nonconstant. Transpose the h-by-h board. Its row law is now the protected law \(t_0\), and its column phase is the arbitrary word c. The [protected-row aggregate inverse](protected_row_aggregate_inverse.md) gives a fixed positive \(h^4\log h\) lower bound for its three-corner count unless c is close to a law with the same quadratic coefficient. For \(\kappa=0\), the constant alternatives are excluded by the balance of c.

If \(t_0\) is constant, use the [constant-phase aggregate inverse](component_permutation_repair.md) instead. It gives the same positive lower bound whenever c is far from ordinary parity.

Repeated-column rectangles contribute only \(O(h^3\log h)\), so the lower bounds persist with four distinct columns. The full-box support multiplicity estimate converts them to (14), uniformly over all such c and over starting phases. Apply the robust argument (15)--(17) to prove (19).

Consequently, a row partition far from every protected row law cannot have asymptotically maximal entropy inside a sufficiently small phase neighborhood of any protected column law. This is a partial partition comparison. It does not control profiles far from all protected column laws, and it does not prove a general dominance theorem.

