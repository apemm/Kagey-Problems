# Near-maximal sea entropy forces a protected row partition

9 November 2026. Vertical-pair rivals close the unknown-row entropy-stability argument. The proof combines exact two-cell pressure, reflection stability, and the previously established bounded-period inverse theorem. It does not require a general inverse theorem for arbitrary full boxes with few three-corner rectangles.

Let \(\mathcal P_h\) be the six protected binary row laws on \([1,h]\):
\[
 c_0(y)=\kappa q(y)+\alpha y+\beta,\qquad
 q(y)=\binom y2\bmod2,
\]
where \(\alpha=1\) when \(\kappa=0\). A protected law need not be exactly balanced at a particular finite height; its class sizes always differ from \(h/2\) by \(O(1)\).

For a balanced row coloring c, let \(\rho_c(h)\) be the growth rate of its fixed-final-pair-set sea shift.

**Partition-stability theorem.** For every \(\eta>0\), there are \(\gamma_\eta>0\) and \(h_\eta\) such that
\[
 \min_{c_0\in\mathcal P_h}
   |\{y:c(y)\ne c_0(y)\}|\ge\eta h
 \quad\Longrightarrow\quad
 \rho_c(h)\le(1/2-\gamma_\eta)h
\tag{1}
\]
for every \(h\ge h_\eta\) and every balanced c.

Equivalently, any sequence of balanced partitions satisfying
\[
 \rho_{c_h}(h)=h/2-o(h)
\tag{2}
\]
is \(o(h)\)-close to one of the ordinary or quadratic row laws. The complete theorem and the phase-concentration corollary in Section 7 have passed [independent review](dense_antiperiod_independent_audit.md).

The theorem does not assert that the maximizing finite-height partition is itself protected. It also does not prove that the boundary component is the unique dominant component.

## 1. Vertical-pair violations and their exact pressure

For \(s\in\{0,1\}\), define
\[
 n_s(k)=\#\{a:c(a)=s,\ a-k,a+k\in[1,h],\
                         c(a-k)\ne c(a+k)\}.
\tag{3}
\]
Only \(1\le k\le(h-1)/2\) can contribute.

Fix a finite column phase word t. Whenever
\[
 t_x=t_{x+2k}=s,
\]
each row a counted by \(n_s(k)\) gives the two-black event
\[
 w_x=w_{x+2k}=a.
\tag{4}
\]
The corresponding tilted rectangle has vertical complementary corners
\[
 (x+k,a-k),\qquad(x+k,a+k).
\]
Their row colors differ, so the fixed final axis-pair set supplies a rival. If the middle column selects one of these corners, the presentation becomes a singleton and the same axis edge still supplies its rival. Thus (4) is a necessary exclusion regardless of the middle column's selected row.

Let \(V_m(t)\) be the number of events (4), including their row choices, with both black columns in \([1,m]\):
\[
 V_m(t)=
 \sum_{k\le(h-1)/2}\ \sum_{x=1}^{m-2k}
 n_{t_x}(k)\,1_{\{t_x=t_{x+2k}\}}.
\tag{5}
\]
There is an absolute \(a_0>0\) such that the valid-word count with phase t satisfies
\[
 Z_c(t)\le
 \left(\prod_{x=1}^m |c^{-1}(t_x)|\right)
 \exp[-a_0V_m(t)/h^2].
\tag{6}
\]

Here is the conditional local-lemma proof. Each event has probability \(\Theta(h^{-2})\) under independent uniform choices from the indicated row classes. There are \(O(h^2)\) events incident to a column. After conditioning on one prescribed black cell, only \(O(h)\) compatible events remain, each with residual probability \(O(h^{-1})\). Two prescribed cells determine the event, so deduplication removes distinct two-cell overlaps.

Mark each event independently with a sufficiently small absolute probability b. The raw incident weight and the compatible conditional neighbor sums are then both \(O(b)\). Set \(x_E=2\Pr(E)\) for the marked family. The shared-variable local-lemma criterion holds, and the exact conditional lower bound from [relative_sparse_defect_pressure.md](relative_sparse_defect_pressure.md), Section 1, gives
\[
 \Pr(E\mid\text{avoid any previously listed marked events})
 \ge\Pr(E)/2.
\]
Sequential avoidance costs \(\exp[-cV_m(t)/h^2]\). Every valid word avoids all the unmarked events, hence also the marked ones, proving (6). This argument uses no monotonicity assumption.

## 2. Entropy turns the pressure into a stationary energy bound

Let \(\mu_h\) be any stationary sea measure for c, and let
\[
 T_x=c(w_x)
\]
be its phase factor. Write \(\mathsf h(\mu_h)\) and \(\mathsf h(T)\) for the two entropy rates.

Conditional on a phase block, the row block is supported on at most \(Z_c(t)\) words. Apply (6), average, divide by m, and let \(m\to\infty\), with h fixed. Stationarity gives
\[
 \mathsf h(\mu_h)
 \le \mathsf h(T)+\log\lceil h/2\rceil
 -\frac{a_0}{h^2}
 \sum_{s=0}^1\sum_k
 n_s(k)\Pr(T_0=T_{2k}=s).
\tag{7}
\]

The profile-complexity theorem in [low_rectangle_profile_complexity.md](low_rectangle_profile_complexity.md) already proves, uniformly over arbitrary balanced row partitions, that
\[
 \mathsf h(\mu_h)\ge\log(h/2)-o(1)
 \quad\Longrightarrow\quad
 \mathsf h(T)=o(1).
\tag{8}
\]
Consequently every such sequence of high-entropy measures satisfies
\[
 \frac1{h^2}
 \sum_{s,k}n_s(k)\Pr(T_0=T_{2k}=s)=o(1).
\tag{9}
\]

## 3. Reflection stability produces many approximate antiperiods

Suppose the row coloring stays at least \(\eta h\) from both ordinary parity laws. Apply [interval reflection stability](reflection_interval_stability.md) to each balanced color class. It gives a constant \(\delta=\delta_\eta>0\) such that
\[
 \sum_k n_s(k)\ge\delta h^2,\qquad s=0,1.
\tag{10}
\]
The sums in (10) are exactly the reflection-violation counts of the two color classes.

Choose \(\epsilon_h\downarrow0\) slowly enough that (9) implies
\[
 \sum_{\{k:\Pr(T_0=T_{2k}=s)>\epsilon_h\}}
 n_s(k)=o(h^2).
\]
Since \(n_s(k)\le h\), for each s there is a set \(D_s\) of at least \(\delta h/2\) distinct lags \(2k\in[1,h]\) such that
\[
 \Pr(T_0=T_{2k}=s)\le\epsilon_h.
\tag{11}
\]

Write \(p_s=\Pr(T_0=s)\). For any stationary binary process,
\[
 \Pr(T_0=T_d=s)\ge2p_s-1,
\]
so one lag from each \(D_s\) gives \(p_s=1/2+O(\epsilon_h)\). Also
\[
 \Pr(T_0=T_d=0)-\Pr(T_0=T_d=1)=p_0-p_1.
\]
Thus every lag in \(D_0\cup D_1\) is an approximate antiperiod:
\[
 \Pr(T_0=T_d)\le C\epsilon_h.
\tag{12}
\]
Only one of the two positive-density sets is needed below.

## 4. Dense approximate antiperiods give a bounded approximate period

We use an elementary stationary lemma.

**Lemma.** Fix \(\delta>0\). Suppose a stationary binary process T has a set
\[
 D\subseteq[1,H],\qquad |D|\ge\delta H,
\]
such that \(\Pr(T_0=T_d)\le\epsilon\) for every \(d\in D\). For sufficiently large H there is an integer
\[
 1\le g\le 2/\delta
\]
such that the expected Hamming distance of \(T_1,\ldots,T_H\) from a g-periodic binary word is at most
\[
 C_\delta\epsilon H.
\tag{13}
\]
The comparison word may depend on the sampled block.

Put \(\ell=\max D-\min D\), and \(g=\gcd(D-D)\). Then
\[
 \ell\ge|D|-1,\qquad g\le\ell/(|D|-1)\le2/\delta.
\]
Every difference \(u-v\in D-D\) is an approximate period:
\[
 \Pr(T_0\ne T_{u-v})\le2\epsilon.
\tag{14}
\]

Normalize \(A=(D-\min D)/g\), and put \(N=\ell/g\). The set A contains 0 and N and has gcd one. Its differences generate \(\mathbb Z_N\). The Cayley graph with closed generating neighborhood \((A-A)\bmod N\) is connected and has at least \(|D|-1\) vertices in every closed neighborhood.

Along a geodesic, the closed neighborhoods of every third vertex are disjoint. Hence the diameter is at most
\[
 K\le 3N/(|D|-1)+2=O_\delta(1).
\tag{15}
\]
The case \(N=1\) is immediate. Lift a Cayley path to an integer sum of at most K differences from \(A-A\). The sum differs from its chosen representative in \([-N,N]\) by at most \(K+1\) multiples of N. Since \(\pm N\in A-A\), at most \(2K+1\) differences represent every integer in that interval.

Therefore every multiple of g of absolute value at most \(\ell\) is a sum of \(O_\delta(1)\) members of \(D-D\). By stationarity, (14), and the union bound,
\[
 \Pr(T_0\ne T_{jg})\le C_\delta\epsilon
 \qquad(|jg|\le\ell).
\]
Since \(\ell\ge\delta H-1\), every multiple of g up to H is a sum of only \(O_\delta(1)\) such shifts. The same bound holds for all \(|jg|\le H\).

Use the first g sampled bits as a periodic template. Each later bit differs from its template value with probability at most \(C_\delta\epsilon\), proving (13). This argument never iterates an approximate one-step period H times.

Applying the lemma to (12) shows that high-entropy phase blocks are \(o(h)\)-close, with probability \(1-o(1)\), to one of finitely many binary words of period at most \(2/\delta\).

## 5. Finish the partition-stability theorem

Suppose (1) fails. Then for some fixed \(\eta>0\) there are heights tending to infinity and balanced row laws \(c_h\), each at least \(\eta h\) from every protected row law, whose sea growth satisfies (2).

Choose a stationary maximal-entropy measure on a maximal recurrent sea component. Its entropy is \(\log\rho_{c_h}(h)=\log(h/2)-o(1)\). Sections 1--4 apply. With probability \(1-o(1)\), its length-h phase block lies within \(o(h)\) of a word from a fixed finite collection of bounded-period phases.

The uniform inverse theorem in [bounded_phase_arbitrary_row_inverse.md](bounded_phase_arbitrary_row_inverse.md) gives a positive three-corner density for each of these phase templates when \(c_h\) is \(\eta h\)-far from every protected law. Its robust container consequence gives fixed \(\xi,\gamma>0\) such that the total number of valid length-h row words whose phase is within \(\xi h\) of this finite collection is at most
\[
 ((1/2-\gamma)h)^h
\tag{16}
\]
for all large h. To include all nearby profiles, take \(\xi\) small enough that their Hamming-ball entropy is absorbed by half the fixed-profile gap.

Let \(q_h\to1\) be the measure of this set of row blocks. Its complement has at most \(h^h\) row words. The entropy of the set-membership indicator is at most \(\log2\), so
\[
 \frac1h H_\mu(w_1,\ldots,w_h)
 \le \log h+q_h\log(1/2-\gamma)+\frac{\log2}{h}.
\tag{17}
\]
The right side is \(\log(h/2)-c_\gamma+o(1)\), contradicting
\[
 \mathsf h(\mu_h)\le
 \frac1hH_\mu(w_1,\ldots,w_h)
\]
and the assumed near-maximal entropy. This proves (1).

## 6. Scope and the remaining exact comparison

The proof treats arbitrary balanced row partitions and arbitrary stationary column phases. It does not assume a bounded phase period, sparse defects, or a fixed row-period bound at the start.

Its conclusion is asymptotic stability. Row changes numbering \(o(h)\) remain possible, and the theorem does not compare their exact Perron roots. The exact fixed-phase penalty in [changed_row_relative_pressure.md](changed_row_relative_pressure.md) handles such changes only inside its stated phase classes.

The argument also leaves open the stronger pure geometric implication
\[
 N_3(c_h,t_h)=o(h^4\log h)
 \ \Longrightarrow\
 (c_h,t_h)\text{ is close to a protected pair}
\]
for arbitrary balanced c and arbitrary finite t. Here the additional vertical-rival exclusions and stationary entropy are essential inputs.


## 7. Matching phase concentration for arbitrary near-maximal partitions

The theorem also extends the protected phase/domain concentration to arbitrary near-maximal partitions.

Let \(c_h\) be balanced with \(\rho_{c_h}(h)=h/2-o(h)\), and let \(\mu_h\) be any stationary sea measures with entropy \(\log(h/2)-o(1)\). Choose \(c_h^0\in\mathcal P_h\) with
\[
 |\{c_h\ne c_h^0\}|=o(h).
\]
Let \(\mathcal X_h\) be the four column laws matched to \(c_h^0\). Then for every fixed \(\eta>0\),
\[
 \Pr_{\mu_h}\left(
  \operatorname{dist}\bigl(T_1,\ldots,T_h,\mathcal X_h\bigr)
  >\eta h\right)\longrightarrow0.
\tag{18}
\]
Here \(T_x=c_h(w_x)\) is the actual phase for the changed partition.

We record why the container argument remains uniform under the row changes. Fix a target error \(\eta\). The existing purification lemma turns a near-half, small-edge container for the balanced coloring \(c_h\) into a full box \(W(c_h,t)\), with small relative cell error and small normalized three-corner count. Restrict to the comparable primitive-direction test family used in the protected-row inverse theorem.

Changing one row changes only \(O(h^3\log h)\) tests in this family. Therefore changing the \(o(h)\) exceptional rows gives
\[
 N_3(c_h^0,t)=N_3(c_h,t)+o(h^4\log h)
\]
within that test family. The protected-row inverse theorem applies to \(c_h^0\); its proof does not require exact balance of that protected law. It makes t close to some \(X\in\mathcal X_h\).

Consequently every sufficiently large near-half container with sufficiently few edges is close in cells to \(W(c_h,X)\) for one of these four laws. The row coloring in this last box is the actual balanced coloring \(c_h\), so its class sizes remain \(h/2+O(1)\).

Now apply the weighted fingerprint count from [protected_partition_entropy_stability.md](protected_partition_entropy_stability.md). In a container close to \(W(c_h,X)\), a transversal whose actual phase is farther than \(\eta h\) from X must use at least \(\eta h-j\) off-box cells after removing its j fingerprint cells. Weight off-box choices by two and apply arithmetic-geometric mean. The factor \(2^{-\eta h+j}\) gives a fixed entropy loss; the \(h^j\) fingerprint choices cancel the missing j coordinates. Smaller containers have a fixed loss directly.

Thus, for some \(\gamma_\eta>0\),
\[
 \#\{\text{valid length-h words with actual phase farther than }
       \eta h\text{ from }\mathcal X_h\}
 \le ((1/2-\gamma_\eta)h)^h.
\tag{19}
\]
The constants are uniform once the row distance is sufficiently small. The uniform full-block bound is \(((1/2+o(1))h)^h\). Applying the two-set entropy bound as in Section 5 gives (18).

The overlap argument from Section 6 of the protected phase-stability note now applies without change. On windows of length h stepped by \(\lfloor h/4\rfloor\), neighboring good windows select the same globally indexed law, because distinct matched laws differ on at least half of their overlap. Choosing \(\eta_h\downarrow0\) slowly gives the following local-domain description: with probability tending to one, a long phase word is \(o(m)\)-close to a concatenation of matched protected laws with \(o(m/h)\) domain boundaries, in the stated joint long-word regime of that note.

This is local phase concentration. It does not imply a single global phase, a zero phase entropy at fixed height, or exact canonical capture of every such domain word.


