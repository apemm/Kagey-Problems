# Repairing overlap-consistent matrices by component permutations

9 November 2026. This note supplies an elementary induced-three-corner removal argument and a finite-component repair lemma. Together with [the periodic Fourier amplification](constant_phase_periodic_amplification.md), they prove the aggregate inverse theorem for a constant column phase. The proof has passed [independent review](component_permutation_independent_audit.md).

Let \(A_h\subseteq[1,h]\) be balanced. Consider the full box consisting of the selected rows \(A_h\) in every column, and let \(N_3(A_h)\) count its tilted rectangles with exactly three selected corners.

**Theorem.**
\[
 N_3(A_h)=o(h^4\log h)
 \quad\Longrightarrow\quad
 \min_{P\text{ an ordinary parity class}}|A_h\triangle P|=o(h).
\tag{1}
\]
The row partition is arbitrary. This is complementary to the [protected-row inverse theorem](protected_row_aggregate_inverse.md), which allows an arbitrary column phase but fixes the row law.

## 1. An elementary biclique-union removal lemma

A binary \(K\times K\) matrix with at most \(\epsilon K^4\) subrectangles having exactly three ones can be changed in \(O(\epsilon^{1/3}K^2)\) entries to a disjoint union of complete bipartite blocks.

Here is a direct algorithm. In the bipartite graph of ones, pivot on an edge \((i,j)\), set \(R=N(j)\) and \(C=N(i)\), fill \(R\times C\), and delete all edges from R to columns outside C and from rows outside R to C. Each edit corresponds to a three-one rectangle containing the pivot edge. Summed over all pivot edges, the edit costs are at most three times the total number of such rectangles.

While the current graph has \(E\ge\tau K^2\) edges,
\[
 \sum_{(i,j)\text{ edge}}(\deg i+\deg j)
 =\sum_v\deg(v)^2
 \ge 2E^2/K\ge2\tau^2K^3.
\]
Some pivot therefore has edit cost divided by \(\deg i+\deg j\) at most \(C\epsilon K/\tau^2\). Perform those edits and remove its rows R and columns C. The remaining graph is the original induced graph on the unremoved vertices, so its three-one count never exceeds the original count.

Over all pivots, the sum of the removed row and column counts is at most \(2K\). Thus the total edit cost before stopping is at most \(C\epsilon K^2/\tau^2\). Delete the final fewer than \(\tau K^2\) edges. Take \(\tau=\epsilon^{1/3}\).

Write the resulting matrix as
\[
 H_{ij}=1_{\{U(i)=V(j)\ne0\}}.
\tag{2}
\]
Every nonzero label \(\ell\) has a row set \(R_\ell\) and column set \(C_\ell\). These sets are pairwise disjoint within their respective sides. Label zero denotes isolated rows or columns.

## 2. A local overlap-consistent matrix

Let \(a,b\in[R,2R]\) be coprime, with \(K/R\to\infty\), and suppose
\[
 G_{ij}=f(y_0+bi+aj),\qquad1\le i,j\le K.
\tag{3}
\]
Assume its three-one subrectangle count is \(o(K^4)\). The preceding lemma gives a matrix H of the form (2), with
\[
 |\{G\ne H\}|\le e_KK^2,\qquad e_K\to0.
\tag{4}
\]
The exact overlaps in G are
\[
 G_{i+sa,j-sb}=G_{ij}
\tag{5}
\]
whenever both entries exist.

Fix a small constant \(0<d<1/100\). We will produce a periodic binary function g, of period dividing \(M!ab\), with \(M\le C/d\), such that on the central interval
\[
 y_0+(a+b)K/2-\min(a,b)K/8
 \le y\le
 y_0+(a+b)K/2+\min(a,b)K/8
\tag{6}
\]
it differs from f in at most
\[
 C dKR+o_d(KR)
\tag{7}
\]
positions.

### 2.1 Choose a component-size gap

For each nonzero component put
\[
 m_\ell=\min(|R_\ell|,|C_\ell|)/K.
\]
At most \(2/d\) components have \(m_\ell\ge d/2\). Consequently there are a threshold \(\theta\in[d,2d]\) and a number \(\gamma\ge c d^2\) such that no \(m_\ell\) lies in
\[
 [\theta-\gamma,\theta+\gamma].
\tag{8}
\]
For example, divide a fixed interior subinterval of \([d,2d]\) into more than \(2/d\) equal intervals and choose an empty interval, slightly shrinking it if necessary.

Call components with \(m_\ell>\theta\) retained. There are \(M\le1/d\) of them. Their row and column sizes are at least \((\theta+\gamma)K\). Set
\[
 S=\left\lfloor\frac{\gamma K}{20R}\right\rfloor.
\tag{9}
\]
For \(1\le s\le S\), the shifts \(sa,sb\) are at most \(\gamma K/10\). In particular every retained component loses only this many rows or columns to the overlap boundary.

### 2.2 Each overlap permutes the retained components

Fix s. On the overlap rectangle, (4)--(5) show that H and its shifted copy disagree in at most \(2e_KK^2\) entries.

Take a retained component \(\ell\). Restrict \(R_\ell,C_\ell\) to the overlap. Their Cartesian product has all ones in H and has both side sizes at least dK. Except for the mismatch entries, their shifted row and column labels agree and are nonzero.

The following elementary observation applies. If independent finite-valued random variables have agreement probability at least \(1-\xi\), some common value has probability at least \(1-2\xi\) under each distribution, provided \(\xi\) is sufficiently small. Indeed one marginal has an atom of size at least \(1-\xi\); agreement then forces the other marginal to put at least \(1-2\xi\) on that atom.

It follows that all but \(O(e_KK/d)\) of these rows and columns land in one common component, denoted \(\sigma_s(\ell)\). More precisely, if \(E_\ell\) counts the mismatch entries in the component rectangle, the exceptional row and column counts are \(O(E_\ell/(dK))\). Since the component rectangles are disjoint, their total exceptions are \(O(e_KK/d)\).

The image component has both side sizes at least
\[
 (\theta+\gamma)K-\gamma K/10-O(e_KK/d).
\]
For fixed d and large K, this exceeds \(\theta K\), so (8) makes the image retained.

Two distinct retained components cannot have the same image. Otherwise a set of at least \(dK/2\) rows from the first and \(dK/2\) columns from the second would be zero before shifting and one after shifting. This would contribute at least \(d^2K^2/4\) mismatches, contrary to (4) for large K. Thus \(\sigma_s\) is an injection of a finite set into itself, and hence a permutation.

Give every unretained row and column the single inactive label zero, which all permutations fix. The label increment identities
\[
 U(i+sa)=\sigma_s U(i),\qquad
 V(j-sb)=\sigma_s V(j)
\tag{10}
\]
hold outside \(O(e_KK/d)\) indices on their respective overlap intervals. For retained labels this was just proved. For an inactive row that shifts into a retained image component, use the retained preimage's columns: at least \(dK/2\) of them shift into that same component, so every such row contributes that many mismatches. This bounds inactive-to-retained exceptions as well. The column argument is identical.

### 2.3 The permutations satisfy an exact addition law

For \(s+t\le S\), fix a retained row label \(\ell\). Its row set has at least dK members. At most \((s+t)a\le\gamma K/10\) fail the common overlap condition, and at most \(O(e_KK/d)\) fail one of the three increment identities. Some row remains for large K, giving
\[
 \sigma_{s+t}(\ell)=\sigma_t\sigma_s(\ell).
\]
The inactive label is fixed. Thus
\[
 \sigma_s=\sigma^s,\qquad \sigma=\sigma_1.
\tag{11}
\]
There is no accumulation of approximation errors in this conclusion: the finite permutations satisfy the identities exactly.

### 2.4 Repair all residue chains

Twist the row labels by
\[
 \widetilde U(i)=
 \sigma^{-\lfloor(i-1)/a\rfloor}U(i).
\]
For every \(s\le S\), at most \(O(e_KK/d)\) pairs \(i,i+sa\) have different twisted labels. Summing over s bounds all disagreeing pairs at distance at most S within the residue chains modulo a by \(O(e_KKS/d)\).

Each residue chain has length between \(c_dS\) and \(C_dS\), with \(1\le c_d<C_d<\infty\), for fixed d and large K. For any fixed \(C_d\), a chain of length between S and \(C_dS\) differs from a constant in at most \(O_d(E/S)\) positions, where E is the number of unequal-label pairs at distance at most S.

One proof first treats binary labels. Partition into a bounded number of blocks of sizes between \(S/6\) and \(S/2\). Internal minority counts give \(cS\) times their sum in disagreeing pairs. If adjacent block majorities differ, their cross pairs give \(cS^2\), which controls the total minority count because the chain has length at most \(C_dS\). For multiple labels, apply this binary cut bound to the indicator of each label and sum; every unequal pair is counted twice, and the sum of the minority counts is at least the number of entries outside a most frequent label.

Therefore the twisted row labels can be made constant on each residue chain by changing \(o_d(K)\) labels. Apply the same argument to columns, twisting by
\[
 \widetilde V(j)=
 \sigma^{\lfloor(j-1)/b\rfloor}V(j).
\]
The repaired labels extend to all integers with
\[
 U^*(i+a)=\sigma U^*(i),\qquad
 V^*(j+b)=\sigma^{-1}V^*(j).
\tag{12}
\]

Unretained components together have at most \(4dK^2\) one entries: components with a row side at most \(2dK\) contribute at most \(2dK^2\), and those with a column side at most \(2dK\) contribute at most another \(2dK^2\). Replacing all of them by zero and then repairing the retained labels gives
\[
 \#\{G_{ij}\ne1_{\{U^*(i)=V^*(j)\ne0\}}\}
 \le 4dK^2+o_d(K^2).
\tag{13}
\]

### 2.5 Return to the physical word

Every integer y has a representation \(y=y_0+bi+aj\), since \((a,b)=1\). Two representations differ by a multiple of \((a,-b)\). Under that change, both labels in (12) are acted on by the same power of \(\sigma\). Thus
\[
 g(y)=1_{\{U^*(i)=V^*(j)\ne0\}}
\]
is well-defined.

If \(q=\operatorname{ord}(\sigma)\), then g has period qab; since \(q\mid M!\), it also has period \(M!ab\). Every y in (6) has at least \(cK/R\) representations with \(1\le i,j\le K\). This follows by intersecting the line \(bi+aj=y-y_0\) with the index square: in the central interval it has an i-projection of length at least cK, and the permitted i form one residue class modulo a.

Each physical error in (6) therefore accounts for at least \(cK/R\) errors in (13). This proves (7).

## 3. Good primitive directions give bounded-period row approximations

Assume \(N_3(A_h)=o(h^4\log h)\). Use dyadic ranges
\[
 h^{1/32}\le R\le h^{1/16}.
\]
For at least one range, all but \(o(R^2)\) primitive directions have three-corner count \(o(h^4/R^2)\), with a common vanishing error. This is the same averaging argument as in the protected-row inverse theorem.

Fix a small \(\eta>0\), set \(K=\lfloor\eta h/R\rfloor\), and consider
\[
 G_{ij}=1_{A_h}(y_0+bi+aj)
\]
on index squares lying in the row interval. Every three-one matrix rectangle corresponds to a physical rectangle of that direction. Its side scales are at most K and its horizontal span is at most \(4\eta h\), so it has at least ch horizontal translates in the board. For a fixed row basepoint and scale pair, at most \(K/R+1\) index pairs represent it. Thus a good direction gives \(o_\eta(K^4)\) three-one matrix rectangles, uniformly in \(y_0\).

For fixed d, Section 2 gives a period-\(M!ab\) approximation on each central interval, with at most \(Cd\) relative error plus \(o_d(1)\). Use the common factorial \(M_0!\), where \(M_0=\lceil C/d\rceil\), for every local matrix.

A chain of \(O(1/\eta)\) overlapping central intervals covers all but \(O(\eta h)\) rows. Adjacent intervals overlap in \(c\eta h\) rows. Their periodic approximants have the same period \(M_0!ab=o(h)\), so agreement with \(A_h\) outside \(O(d\eta h)+o_{d,\eta}(h)\) errors implies that their period words differ on an \(O(d)+o_{d,\eta}(1)\) fraction of one period.

Following the chain and using one approximant on the entire interior gives a global approximation error at most
\[
 C(\eta+d/\eta)h+o_{d,\eta}(h).
\tag{14}
\]
The endpoint loss is included here.

As in the protected-row theorem, choose odd a,b such that
\[
 (a,b),\quad(a+2,b),\quad(a,b+2),\quad(a+2,b+2)
\]
are all primitive and good. Such quadruples have positive density, by the elementary finite-prime sieve. The four approximate periods are
\[
 M_0!ab,\quad M_0!(a+2)b,\quad
 M_0!a(b+2),\quad M_0!(a+2)(b+2).
\]
Their gcd is \(M_0!\), and their pairwise lcms are \(O_d(R^4)=o(h)\). The binary Chinese-remainder comparison from the protected-row theorem therefore replaces them by one \(M_0!\)-periodic function, increasing the error in (14) only by an absolute factor.

Taking \(\eta=\sqrt d\), we conclude:

**Bounded-period approximation.** For every sufficiently small fixed d, a sequence with vanishing normalized three-corner count is within
\[
 C\sqrt d\,h+o_d(h)
\tag{15}
\]
row edits of a periodic set of period \(N\le M_0!\), where \(M_0\le C/d\).

## 4. Finish the constant-phase aggregate inverse

Suppose, contrary to (1), that the original balanced row sets remain at least \(\varepsilon h\) from both parity classes along a subsequence. Choose d small enough that the approximants in (15) are nearly balanced and remain at least \(\varepsilon h/2\) from both classes.

The periodic Fourier amplification gives at least
\[
 \frac{c\varepsilon}{(\log(1/d))^2}\,h^4\log h
\tag{16}
\]
three-corner rectangles in its comparable-direction family. Indeed its period loss is
\[
 \prod_{p\mid N}\frac{p-1}{p+1}
 \gg(\log\log(3N))^{-2}
 \gg(\log(1/d))^{-2}.
\]
The constants are uniform over the finitely many approximants for this fixed d.

Changing \(C\sqrt d\,h+o_d(h)\) rows changes at most
\[
 (C'\sqrt d+o_d(1))h^4\log h
\]
tests in the same family. For sufficiently small fixed d, this is less than half of (16), because
\[
 \sqrt d\,(\log(1/d))^2\longrightarrow0.
\]
The original row sets would therefore have a positive normalized three-corner count, a contradiction. This proves (1).

The conclusion is qualitative in the edit distance. It supplies a fixed positive aggregate test density for every fixed positive distance from ordinary parity, but no explicit dependence of that density on the distance is claimed.

