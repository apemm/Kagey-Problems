# Small clusters of parity defects preserve the protected pressure

9 November 2026. This strengthens [dilute_parity_defects.md](dilute_parity_defects.md). The new ingredient is a divisor-weight bound uniform over arbitrary sets of column distances. Both the bounded-cluster theorem in Sections 1--5 and the weighted local-density extension in Section 6 passed independent review.

Let \(L=2W_h=O(h^2)\), so every relevant support has diameter at most L. In a parity sea, call an even-row letter a defect relative to the all-odd phase. Join consecutive defects whenever their column gap is at most \(2L\); the connected components are the defect clusters.

**Theorem.** There are absolute constants \(a,c>0\) such that, if \(r_{\mathrm{small}}(h)\) is the entropy of valid parity seas whose every defect cluster has size at most
\[
 Q_h=\left\lfloor\exp(a\sqrt{\log h})\right\rfloor,
\]
then, for every fixed \(\varepsilon>0\),
\[
 \log r_{\mathrm{small}}(h)
 \le \log r_{\mathrm O}(h)
       +O_\varepsilon(h^{-2+\varepsilon})
       +\exp[-c(\log h)^2].
\tag{1}
\]
The all-odd phase is contained in this class, so its entropy is also a lower bound. A q-defect cluster can have diameter up to \(2L(q-1)\). Larger clusters, including persistent opposite-parity domains, remain untreated.

## 1. Arbitrary distance sets

For any set \(D\) of q distinct positive integers,
\[
 \sum_{d\in D}\frac{\tau(d)}d=O((\log(q+1))^2).
\tag{2}
\]
There is no dependence on the largest distance. Pairing divisors gives
\[
 \sum_{d\in D}\frac{\tau(d)}d
 \le2\sum_{u\ge1}\frac1u
    \sum_{\substack{v\ge u\\uv\in D}}\frac1v.
\]
For fixed u, the inner sum has at most q terms and is maximized by the consecutive choices \(v=u,\ldots,u+q-1\). It is at most \(u^{-1}+\log(1+q/u)\). Summing over \(u\le q\) gives \(O(\log^2(q+1))\), and the sum over \(u>q\) is O(1). The estimate also holds with multiplicity at most two, as for absolute distances from a fixed column.

## 2. Rooted incidence at a specified distance

Fix a completion column j. Each all-odd tilted rectangle with four distinct corner columns and a corner W in column j gives a three-cell event requiring its other three corners to be black. If j is a defect, this event has a singleton parity-axis rival and is forbidden.

For another column x, put \(d=|x-j|>0\). Two specified corners P,W with horizontal difference d and vertical difference v admit at most
\[
 C\frac{h\gcd(d,v)}d+O_\eta(h^\eta)
\tag{3}
\]
tilted rectangles in the strip, for every fixed \(\eta>0\). For a side pair, the primitive perpendicular vector has vertical step \(d/\gcd(d,v)\). For a diagonal pair, use \(r_2(d^2+v^2)\) and the divisor bound; here \(d\le L=O(h^2)\). Including axis rectangles in this upper bound does no harm.

The divisor identity for gcd gives
\[
 \sum_{|v|<h}\gcd(d,v)\le Ch\tau(d)+d.
\]
Thus for fixed P, summing (3) over W's rows gives
\[
 O_\eta\left(h^2\frac{\tau(d)}d+h^{1+\eta}\right)
\tag{4}
\]
rooted events through P. Sum over P's h rows and multiply by \(O(h^{-3})\). The probability incident with column x is at most
\[
 O_\eta\left(\frac{\tau(d)}d+h^{-1+\eta}\right).
\tag{5}
\]
All these quantities are zero outside the support range.

For q roots, (2) bounds the incident probability at any column by \(C_\eta D_h(q)\), where
\[
 D_h(q)=(\log(q+1))^2+qh^{-1+\eta}.
\tag{6}
\]
The number of events through one fixed black point is at most \(C_\eta h^2D_h(q)\).

For the rest of the rooted-event estimates fix \(\eta=1/8\). All constants determining the cluster cutoff are then absolute. The separate bulk/bulk error may use any requested positive exponent.

## 3. One cluster's mean and overlaps

Fix a parity profile and a cluster of q defects. Retain only rooted events whose black support avoids every defect column. Other clusters cannot affect this exclusion: they are separated by more than \(2L\).

Each root initially has mean \(\nu_j\sim20\log^2h/(3\pi^2)\). Deleting events using the other flipped columns loses at most \(C_\eta D_h(q)\) per root, by (5)--(6). For \(q\le Q_h\), this is \(O(\log h)=o(\log^2h)\). The retained cluster mean is therefore at least \(c_0q\log^2h\), uniformly in the positions of its defects.

There are \(O(qh^3\log^2h)\) retained events. Pairs sharing one black assignment have total joint probability at most
\[
 O_\eta(qh^3\log^2h\cdot h^2D_h(q)\cdot h^{-5})
 =O_\eta(q\log^2h\,D_h(q)).
\tag{7}
\]
For two fixed black points in distinct columns, each completion column admits O(1) possibilities, by the perpendicular-line/Thales-circle argument in the dilute note. Sharing two assignments therefore costs at most \(O(q^2h^{-1}\log^2h)\), which is included in (7). Three fixed black points determine their rectangle and completion uniquely. Conflicting assignments have joint probability zero. Rooted families from distinct clusters use disjoint row variables.

## 4. Cluster-dependent thinning with the bulk retained

Keep all ordinary minimal four/six events avoiding the defects. With n total defects, their mean is
\[
 m\mu_{\mathrm O}(h)-O_\eta(nh^{-1+\eta})+O_h(1).
\]
Their overlap sum is \(O_\varepsilon(mh^{-2+\varepsilon})\), for any fixed \(\varepsilon>0\). The joint rooted/bulk overlap is \(O_\eta(nh^{-1+\eta})\), by the extension table used in the dilute proof, with the fixed \(\eta=1/8\).

Independently mark each rooted event in a q-cluster with probability \(\theta_q=b/D_h(q)\), for a sufficiently small constant b, with \(\theta_q\le1\). Keep the indicator only if its marker is one. The rows and independent markers have a strong shared-variable dependency graph.

Equation (6) bounds the maximum neighboring probability sum by O(b)+o(1). A column meets rooted events from at most one cluster. A bulk event meets at most six such clusters, so its neighbor sum obeys the same bound. The thinned mean from a q-cluster is at least \(c_0bq\log^2h/D_h(q)\); (7) contributes at most \(Cb^2q\log^2h/D_h(q)\) to the joint overlap. Choose b small enough to absorb the latter, including the bounded Suen factor \(e^{2\delta}\), into half the former. Deleted-bulk and rooted/bulk terms are smaller and absorbed too.

Suen's arbitrary-indicator upper bound now gives
\[
 \Pr(\text{valid}\mid\text{profile})
 \le\exp\left[
 -m\mu_{\mathrm O}(h)
 -c_1\sum_{\text{clusters }C}
    \frac{|C|\log^2h}{(\log(|C|+1))^2}
 +O_\varepsilon(mh^{-2+\varepsilon})+O_h(1)
 \right].
\tag{8}
\]
The rooted/bulk and deleted-bulk errors are absorbed into the cluster penalty, so only the bulk/bulk overlap requires the arbitrary exponent \(\varepsilon\). Since \(Q_h=h^{o(1)}\), the second term of \(D_h(q)\) is uniformly negligible. Avoiding the original events implies avoiding the thinned family, which is the required direction for this upper bound.

## 5. Cluster enumeration

A q-cluster is determined by its first column and q-1 successive gaps, each at most \(2L\). Its overcounted activity per first column is therefore
\[
 z_h=\sum_{q=1}^{Q_h}(2L)^{q-1}
 \exp\left[-c_1\frac{q\log^2h}{(\log(q+1))^2}\right].
\tag{9}
\]
For sufficiently small a,
\[
 z_h\le\exp[-c_2\log^2h].
\tag{10}
\]
Indeed \(\log(2L)\le3\log h\) for large h. If \(q\ge\log h\), then \((\log(q+1))^2\le2a^2\log h\). Choose a so \(c_1/(2a^2)>10\); each term is at most \(\exp[-7\log^2h]\). For \(q<\log h\), the positive gap-counting term is uniformly negligible compared with the negative term, since \(\log h/(\log\log h)^2\to\infty\). The function \(q/(\log(q+1))^2\) has a positive minimum on positive integers, so these terms are at most \(\exp[-c_3\log^2h]\). The number \(Q_h=\exp[O(\sqrt{\log h})]\) of terms is absorbed.

Allow an arbitrary subset of columns to be cluster starts, with independently chosen candidates. This overcounts all permissible profiles, giving weighted sum at most \((1+z_h)^m\). Each profile has at most \(\lceil h/2\rceil^m\) row choices. Clusters meeting an end lie in strips of length \(O(LQ_h)\), so they affect only a height-dependent factor. Equation (8) yields
\[
 \log r_{\mathrm{small}}(h)
 \le\log\lceil h/2\rceil-\mu_{\mathrm O}(h)
       +O_\varepsilon(h^{-2+\varepsilon})+z_h.
\]
The protected-phase expansion proves (1). This rules out a first-order pressure advantage from clusters below the stated threshold. It does not control large clusters or prove general component dominance.

## 6. A criterion allowing arbitrarily large clusters

The same proof covers a class defined by weighted local density instead of cluster size. For a defect set S, define
\[
 \mathcal D_h(S)=1+\sup_{x\in\mathbb Z}\left[
 \sum_{\substack{j\in S\\0<|j-x|\le L}}
       \frac{\tau(|j-x|)}{|j-x|}
 +h^{-7/8}|S\cap[x-L,x+L]|
 \right].
\tag{11}
\]
The condition depends on a finite window and makes sense for finite or infinite S. For a finite cluster C, write \(D(C)=\mathcal D_h(C)\).

**Extension.** There are absolute \(\kappa,c>0\) such that the entropy \(r_{\mathrm{loc}}(h)\) of valid parity seas satisfying
\[
 \mathcal D_h(S)\le\kappa\log h
\tag{12}
\]
obeys
\[
 \log r_{\mathrm{loc}}(h)
 \le\log r_{\mathrm O}(h)
       +O_\varepsilon(h^{-2+\varepsilon})
       +\exp[-c\log^2h].
\tag{13}
\]
There is no cluster-size restriction in this statement.

Here are the changes to the proof. The incident probability bound is \(O(D(C))\) directly from (5) and (11). Each root loses only \(O(D(C))=O(\log h)\) of its \(\Theta(\log^2h)\) mean. Through any fixed black point there are at most \(Ch^2D(C)\) events. For two fixed black points, only completion columns within L of them can occur. Their number is at most \(D(C)h^{7/8}\) by the second term of (11). The two-shared-cell overlap is therefore at most
\[
 O(qh^3\log^2h\cdot D(C)h^{7/8}\cdot h^{-4})
 =O(q\log^2h\,D(C)h^{-1/8}),
\]
which is smaller than the one-shared-cell bound \(O(q\log^2h\,D(C))\).

Thin the cluster at rate \(b/D(C)\). The resulting penalty is at least
\[
 c_4 q\log^2h/D(C).
\tag{14}
\]
For small q, (2) still gives
\(D(C)\le C_0[1+\log^2(q+1)+qh^{-7/8}]\). For every q, (12) gives \(D(C)\le\kappa\log h\). Thus q below \(\log h\) has the same activity bound as before. For q at least \(\log h\), choose \(\kappa\) so small that \(c_4/\kappa>10\). The activity is then at most \(\exp[-7q\log h]\), after paying \((2L)^{q-1}\). The sum over all \(q\ge\log h\), with no upper cutoff, is \(\exp[-\Omega(\log^2h)]\). The profile sum and bulk expansion finish (13).

For finite words, omit rooted events at the at most \(2L\) columns near the ends. The lost penalty is \(O_h(1)\), even if an omitted root belongs to a very large cluster. Every other step uses only completion columns and black variables in the word. Restricting an infinite profile satisfying (12) can only decrease \(\mathcal D_h\), so this finite-word bound applies to its language.

This extension includes the bounded-cluster theorem after decreasing a. It also permits infinite connected clusters: for example, defects at every \(2L\)-th column have at most two roots in any radius-L window, so their \(\mathcal D_h\) is bounded by an absolute constant for large h. What remains untreated is large weighted local defect density, not cluster length by itself.
