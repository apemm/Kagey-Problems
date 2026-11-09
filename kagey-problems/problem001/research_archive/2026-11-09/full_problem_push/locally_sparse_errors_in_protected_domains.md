# Leading protected pressure with uniformly locally sparse domain errors

9 November 2026. The common truncated-direction family removes the packet-separation condition. It also permits protected domains of length h divided by any fixed power of log h.

Fix a protected row law c_0. Let \(\mathcal X(c_0)\) be its finite family of matched protected column laws and
\[
 \rho_0(h)=\max_{X\in\mathcal X(c_0)}\rho_{c_0,X}(h),
 \qquad \Lambda=1+\log h.
\]
Fix \(B\ge0\). Choose a sufficiently large fixed A, and set
\[
 \epsilon_h=e^{-A\sqrt{\log h}},\qquad
 R_h=\lfloor\epsilon_h^{-1/4}\rfloor.
\tag{1}
\]
A profile in \(\mathcal D_{h,B,A}\) consists of matched protected domains of minimum length \(h/\Lambda^B\), with adjacent domain laws distinct, followed by an arbitrary phase-error set S satisfying
\[
 |S\cap[j,j+h-1]|\le\epsilon_hh
 \quad\hbox{for every }j.
\tag{2}
\]
The first and last domains may be shorter. There is no separation condition on errors or error clusters.

All validity and partition functions use the normalized fixed-final-F support language.

**Theorem.** For every fixed B and all sufficiently large fixed A,
\[
 \log\rho(\mathcal D_{h,B,A})
   =\log\rho_0(h)+o(\Lambda^4/h).
\tag{3}
\]
Thus the proved quadratic-over-ordinary protected gap persists for this entire ordinary-row domain language. Equation (3) is not a claim about the full ordinary sea shift.

## 1. Guard errors cost less than a rescaled wall

Put \(H_*=C_*hR_h\), with C_* large enough to contain twice the support radius of every root in [the locally sparse theorem](uniform_local_phase_sparsity.md). Call an error a guard error if it has distance at most H_* from a wall.

For each wall, (2) bounds the number of guard errors assigned to it by
\[
 C\epsilon_hhR_h.
\tag{4}
\]
Overlaps between guard intervals only reduce the actual count. Assign each guard error to one nearby wall to avoid ambiguity. Overcounting all possible assignments, their descriptions per wall cost at most
\[
 \exp(G_h),\qquad
 G_h=C\epsilon_hhR_h\log(e/\epsilon_h)
     =h\exp[-(3A/4)\sqrt{\log h}]\,O_A(\sqrt{\log h}).
\tag{5}
\]
Every active error lies farther than H_* from all walls, so its truncated root family lies completely in its own domain and stays away from the wall-root neighborhoods.

Use the rescaled wall family from [the finite-island estimate](finite_protected_island_pressure.md), at physical scale
\[
 d_h=c\,h/\Lambda^B.
\]
Each wall has a marked probability mean bounded below by
\[
 cW_h(d_h),\qquad
 W_h(d)=\frac{d^3\log d}{h^2+d^2\log d}.
\tag{6}
\]
For fixed B, a convenient conservative bound is
\[
 W_h(d_h)\ge c_B w_h,\qquad
 w_h=h/\Lambda^{3B+1}.
\tag{7}
\]
The black-variable windows for distinct walls are disjoint: choose the geometric constant c small enough that each lies inside a short interval in the preceding domain.

Delete wall roots whose completion or black columns meet S. A prescribed column has O(1) marked incident mass, while each local wall interval contains at most \(C\epsilon_hh\) errors by (2). The lost mean is at most \(C\epsilon_hh=o(w_h)\). Hence the wall penalty remains \(\exp(-c_Bw_h)\) per wall.

Both \(G_h=o(w_h)\) and \(\epsilon_hh=o(w_h)\). Guard descriptions and all guard-error losses are therefore absorbed by the wall penalty in absolute counting estimates. This holds even when many guard intervals overlap.

## 2. Active errors preserve the coefficient of the retained bulk

For each active error use the unthinned truncated family with cutoff R_h. Its total mean is at least
\[
 c\log^2(1/\epsilon_h)
   =cA^2\log h
\tag{8}
\]
per error. The raw and conditional one-/two-cell bounds are
\(O(\epsilon_hR_h^3)+O(\epsilon_hR_h)=o(1)\), uniformly over all error placements satisfying (2).

Delete every root geometry meeting S. This is already included in the mean estimate in the locally sparse theorem. Wall roots and active roots have disjoint black-variable neighborhoods, by the choice of H_*. No new cross-family conditional estimate is required.

For the low-wall estimate, fix \(\delta>0\) and retain the protected bulk of span at most
\[
 H_\delta=Ch^{2-\delta}
\]
constructed in [the domain leading-pressure proof](protected_domain_leading_pressure.md). Its omitted per-column mean is at most
\[
 C\delta\Lambda^4/h+o_\delta(\Lambda^4/h).
\tag{9}
\]
Retain only those supports lying within a single domain and avoiding S.

Apply Suen's inequality to this bulk first. Then apply the exact conditional lower-probability lemma to active roots. Their mean retains a fixed positive factor after conditioning on the bulk, so the coefficient of the bulk mean stays one.

Deleting active-error columns from the bulk costs at most
\(C|S_{\rm active}|\Lambda^4/h\), which is absorbed by (8). Summing all possible active-error sets then costs at most
\[
 \exp(mz_h),\qquad z_h=h^{-cA^2}.
\tag{10}
\]
Take A large enough that \(z_h=o(\Lambda^4/h)\).

Deleting guard-error columns costs at most
\[
 CJ\epsilon_hR_h\Lambda^4+O_h(1),
\tag{11}
\]
where J is the wall count. The extra product-alphabet cost is smaller. This estimate uses (4), not the length of the full guard interval.

A cut removes at most \(CH_\delta\Lambda^4/h\) retained mean. Thus a fixed domain description, after summing errors, has logarithmic count at most
\[
 \begin{split}
 m\log\rho_0
 &+C\delta m\Lambda^4/h+o_\delta(m\Lambda^4/h)\\
 &+CJH_\delta\Lambda^4/h
  +CJ\epsilon_hR_h\Lambda^4
  +JG_h+mz_h+O_h(1).
 \end{split}
\tag{12}
\]

## 3. Low and high wall densities

Set
\[
 \nu_h=K_B\frac{\Lambda^4}{hw_h}
      =K_B\frac{\Lambda^{3B+5}}{h^2},
\tag{13}
\]
where K_B is a sufficiently large fixed constant.

For \(J\le\nu_hm\), the domain-description entropy is
\[
 H_2(\nu_h)+\nu_h\log|\mathcal X(c_0)|
   =o(\Lambda^4/h).
\]
For fixed delta, every additional term in (12) is lower order:
\[
 \nu_hH_\delta\Lambda^4/h
   =O_B(h^{-1-\delta}\Lambda^{3B+9})
   =o(\Lambda^4/h),
\]
\[
 \nu_hG_h=o(\Lambda^4/h),\qquad
 \nu_h\epsilon_hR_h\Lambda^4=o(\Lambda^4/h),
 \qquad z_h=o(\Lambda^4/h).
\]
The first relation for G_h follows directly from \(G_h=o(w_h)\).

For \(J>\nu_hm\), omit the bulk and use the absolute joint wall/active-root count. Active-error activities are summable. Guard descriptions and losses are absorbed by the wall mean. The word count has logarithmic rate at most
\[
 \log\lceil h/2\rceil-c_Bw_h\nu_h+o(\Lambda^4/h).
\tag{14}
\]
Wall-location entropy is absorbed because, for \(s\ge\nu_h\),
\[
 H_2(s)+s\log|\mathcal X(c_0)|=O_B(\Lambda s)
       =o(w_hs).
\]
Choose K_B so that (14) lies below \(\log\rho_0\), using
\(\rho_0\ge h/2-C\Lambda^4\).

The low-wall estimate is at most
\(\log\rho_0+C\delta\Lambda^4/h+o_\delta(\Lambda^4/h)\).
Take h to infinity first and then delta to zero. Pure protected phases belong to the language, so the reverse bound is immediate. This proves (3).

## 4. What remains outside this class

The theorem covers arbitrary clustering and arbitrary total numbers of locally sparse errors, and domains shorter than h by every fixed logarithmic factor. It does not prove that a general high-entropy phase profile has a representation satisfying (2). The qualitative phase-concentration theorem does not currently supply the rate \(\epsilon_h=e^{-A\sqrt{\log h}}\).

Intervals of intermediate error density, and mixtures of those intervals across scales, remain the obstruction to unrestricted comparison.

The complete proof passed [independent review](local_phase_sparsity_independent_audit.md).

