# The aggregate rectangle inverse test for a protected row partition

9 November 2026. This note proves the phase part of the container inverse test when the row partition is already ordinary or quadratic parity. The column phase is arbitrary. The proof has passed two independent reviews, including the saved [independent audit](rectangle_inverse_independent_audit.md).

Let
\[
 c(y)=\kappa q(y)+\alpha y+\beta,\qquad
 q(y)=\binom y2\bmod2,
\]
where \(\alpha=1\) if \(\kappa=0\). For an arbitrary binary word \(t:[1,h]\to\mathbb F_2\), put
\[
 W=\{(x,y)\in[h]^2:c(y)=t(x)\}.
\]
Let \(N_3(W)\) count tilted lattice rectangles with exactly three corners in W.

**Theorem.** Uniformly over these finitely many row laws,
\[
 N_3(W)=o(h^4\log h)
 \quad\Longrightarrow\quad
 \min_{\gamma,\delta}
 \#\{x:t(x)\ne\kappa q(x)+\gamma x+\delta\}=o(h).
\tag{1}
\]
Equivalently, for every \(\varepsilon>0\), there are \(\delta_\varepsilon>0\) and \(h_\varepsilon\) such that phase distance at least \(\varepsilon h\) forces
\[
 N_3(W)\ge\delta_\varepsilon h^4\log h.
\tag{2}
\]
The conclusion concerns one board-sized phase word. It is not a component-connectivity statement.

## 1. Three-corner failures become a one-dimensional XOR test

Subtract the prescribed quadratic phase and write
\[
 s(x)=t(x)+\kappa q(x).
\]
For a rectangle with sides
\[
 k(a,b),\qquad l(-b,a),
\]
the XOR of its four row colors is \(\kappa klab\). The XOR of \(\kappa q(x)\) on its four columns is the same. Thus the rectangle has an odd number of selected corners exactly when
\[
 s(x)+s(x+ka)+s(x-lb)+s(x+ka-lb)=1.
\tag{3}
\]

For ordinary row parity, shifting every row by one complements all four row colors. For quadratic row parity, shifting every row by two does so. Therefore, whenever a horizontal pattern (3) is a failure and the rectangle's vertical span is at most \(h/10\), at least \(ch\) valid vertical translations have exactly three selected corners, for an absolute \(c>0\).

Fix a small number \(0<\eta<1/100\). For a primitive direction \(a,b\in[R,2R]\), put
\[
 K=\lfloor\eta h/R\rfloor.
\]
For \(1\le k,l\le K\), the vertical span is at most \(4\eta h<h/10\). Let \(B_{a,b}\) count failures (3) for these k,l and all horizontal basepoints whose four columns remain in the board. If \(N_{a,b}\) is the three-corner rectangle count for this primitive direction, then
\[
 B_{a,b}\le C N_{a,b}/h.
\tag{4}
\]

## 2. A good primitive direction gives an approximate short period

We prove the following local lemma.

**Lemma.** Suppose \(a,b\in[R,2R]\) are coprime, \(R\to\infty\), \(R^2=o(h)\), and
\[
 N_{a,b}=o(h^4/R^2).
\tag{5}
\]
For each fixed \(\eta>0\), there is a binary function g of period \(2ab\) that agrees with s at all but \(o_\eta(h)\) positions of
\[
 [10\eta h,(1-10\eta)h].
\tag{6}
\]

### 2.1 A lifted matrix is close to rank one

Choose an integer \(x_0\) such that all the entries of
\[
 G_{ij}=s(x_0+ai-bj),\qquad 1\le i,j\le K,
\tag{7}
\]
lie in \([1,h]\). Every odd-XOR subrectangle of G corresponds to a failure counted by \(B_{a,b}\). For a fixed physical basepoint x and two index differences k,l, the equation
\[
 ai-bj=x-x_0
\]
has at most \(K/R+1\) solutions in the index square, since its solutions differ by \((b,a)\). Thus (4)--(5) imply that G has
\[
 O((K/R+1)N_{a,b}/h)=o_\eta(K^4)
\tag{8}
\]
odd-XOR subrectangles.

A binary matrix with \(o(K^4)\) odd-XOR subrectangles differs from a matrix \(u_i+v_j\) in \(o(K^2)\) entries. To see this, average over an anchor \((i_0,j_0)\), and use
\[
 u_i=G_{i,j_0},\qquad
 v_j=G_{i_0,j}+G_{i_0,j_0}.
\]
The error at \((i,j)\) is exactly the XOR on the rectangle determined by that point and the anchor. Hence some anchor has the stated error bound. Write
\[
 \#\{(i,j):G_{ij}\ne u_i+v_j\}\le\epsilon K^2,
 \qquad \epsilon=o_\eta(1).
\tag{9}
\]

### 2.2 Exact overlaps repair the two factors

The lifted matrix has the exact consistency identity
\[
 G_{i+sb,j+sa}=G_{ij}
\tag{10}
\]
whenever both entries exist. Put \(S=\lfloor K/(8R)\rfloor\), which tends to infinity. For every \(1\le s\le S\), both remaining index intervals have length at least \(3K/4\). Equations (9)--(10) give
\[
 u_{i+sb}+u_i=v_{j+sa}+v_j
\]
outside at most \(2\epsilon K^2\) pairs \((i,j)\).

The left side depends only on i and the right side only on j. Therefore there is a common bit \(\sigma_s\) such that each side differs from \(\sigma_s\) at at most \(3\epsilon K\) indices, for all sufficiently small \(\epsilon\). This follows by comparing the two binary distributions: the fraction of mismatching independent samples bounds the minority fraction in either distribution, and their majority bits must agree.

If \(s+t\le S\), choose i at which the three corresponding increment identities hold. At most \(9\epsilon K\) indices are excluded from an interval of length at least \(3K/4\), so
\[
 \sigma_{s+t}=\sigma_s+\sigma_t.
\]
Hence
\[
 \sigma_s=s\sigma_1.
\tag{11}
\]

Put \(\sigma=\sigma_1\) and
\[
 \widetilde u_i=u_i+\sigma\lfloor(i-1)/b\rfloor.
\]
For each \(1\le s\le S\), at most \(3\epsilon K\) pairs \(i,i+sb\) have different \(\widetilde u\)-values. Summing over s bounds the number of disagreeing pairs at index distance at most S within all residue chains modulo b by \(3\epsilon KS\).

Each such chain has length between \(3S\) and \(9S\), for large h: its length is \(K/b+O(1)\), while \(R\le b\le2R\) and \(S=K/(8R)+O(1)\). A binary chain of length n with \(3S\le n\le9S\) and minority count m has at least \(cSm\) disagreeing pairs at distance at most S. Here is an elementary proof. Partition the chain into a bounded number of consecutive blocks, each of size between \(S/6\) and \(S/2\), with adjacent blocks together having diameter at most S. If A is the sum of the minority counts within the blocks, their internal disagreeing pairs contribute at least \(cSA\). If all block majorities agree, \(A=m\). Otherwise two adjacent blocks have opposite majorities, giving at least \(cS^2\) disagreeing pairs; since \(m\le n/2\le9S/2\), this is at least \(c'Sm\).

Consequently \(\widetilde u\) differs from a function constant on each residue class modulo b in \(O(\epsilon K)\) entries. The same argument applies to v modulo a. We may therefore repair u,v in \(o(K)\) entries to functions \(u^*,v^*\) satisfying, on their integer extensions,
\[
 u^*(i+b)=u^*(i)+\sigma,\qquad
 v^*(j+a)=v^*(j)+\sigma.
\tag{12}
\]
The repaired matrix still differs from G in \(o(K^2)\) entries.

### 2.3 The repaired matrix defines a physical period

Because \(\gcd(a,b)=1\), every integer n can be written as
\(n=x_0+ai-bj\). Two representations differ by a multiple of \((b,a)\). By (12), the value
\[
 g(n)=u^*(i)+v^*(j)
\]
is independent of that representation. Also
\[
 g(n+ab)=g(n)+\sigma,
\]
so g has period \(2ab\).

Every n in the central interval
\[
 x_0-bK/4\le n\le x_0+aK/4
\tag{13}
\]
has at least \(cK/R\) representations in the index square. Indeed the permissible i-values form an interval of length at least \(K/4-O(1)\), in one residue class modulo b. Since \(K/R\to\infty\), the claimed lower bound follows. Each erroneous physical value therefore accounts for at least \(cK/R\) erroneous matrix entries. Thus s and g differ in \(o(KR)=o_\eta(h)\) positions of (13).

Choose a bounded number, depending only on \(\eta\), of such lifted matrices with overlapping central intervals covering (6). Adjacent overlaps have length \(c_\eta h\), while the period \(2ab=O(R^2)=o(h)\). Their periodic approximants agree with s except at \(o_\eta(h)\) points, so they disagree on only an \(o_\eta(1)\) fraction of one period. Following the finite chain of overlaps gives one period-\(2ab\) function agreeing with s outside \(o_\eta(h)\) errors throughout (6). This proves the lemma.

## 3. Four nearby good directions have period gcd two

Consider dyadic ranges
\[
 h^{1/32}\le R\le h^{1/16}.
\]
There are \(\Theta(\log h)\) such ranges. Distinct primitive directions count disjoint rectangles. If \(N_3(W)=o(h^4\log h)\), at least one range satisfies
\[
 \sum_{\substack{a,b\in[R,2R]\\(a,b)=1}}N_{a,b}=o(h^4).
\tag{14}
\]
It follows that all but \(o(R^2)\) primitive directions in this range satisfy (5), with a common error tending to zero.

There is a positive absolute proportion of odd pairs a,b in the interior of this square for which all four directions
\[
 (a,b),\quad(a+2,b),\quad(a,b+2),\quad(a+2,b+2)
\tag{15}
\]
are primitive. One elementary sieve proof is to impose the required congruences at finitely many primes by the Chinese remainder theorem. At an odd prime p, the forbidden residue pairs are the four pairs with
\(a\in\{0,-2\}\), \(b\in\{0,-2\}\), so the local permitted fraction is \(1-4/p^2\). Their product is positive. Larger primes contribute at most
\[
 O\!\left(R^2\sum_{p>Q}p^{-2}+R\log R+R\right)
\]
exceptions. Choose Q sufficiently large and then let R grow. Oddness handles the prime two.

Removing \(o(R^2)\) bad directions eliminates only \(o(R^2)\) possible quadruples. Hence some quadruple (15) consists entirely of good directions.

The lemma supplies four approximants to s, with respective periods
\[
 2ab,\quad2(a+2)b,\quad2a(b+2),\quad2(a+2)(b+2).
\tag{16}
\]
Their gcd is two, since a,b are odd and
\(\gcd(a,a+2)=\gcd(b,b+2)=1\). Every pairwise lcm is \(O(R^4)=o(h)\).

## 4. Compatible short periods collapse by the Chinese remainder theorem

We use a simple comparison principle. Suppose functions f,g have periods P,Q, their lcm is \(o(h)\), and they disagree at \(o(h)\) points of an interval of length comparable with h. Then both are \(o(h)\)-close on that interval to a function of period \(\gcd(P,Q)\).

To prove it, let \(d=\gcd(P,Q)\). A uniform residue modulo \(\operatorname{lcm}(P,Q)\), conditional on its residue modulo d, gives independent uniform residues modulo P and Q subject to that common residue. The observed disagreement on a long interval differs from this uniform average by \(O(\operatorname{lcm}(P,Q)/h)=o(1)\).

For two independent binary random variables with success probabilities p,q, their disagreement probability is \(p+q-2pq\). Choosing one common constant bit makes the sum of their error probabilities
\[
 \min(p+q,2-p-q)\le2(p+q-2pq).
\]
Choose that constant separately in each residue class modulo d. This gives the desired d-periodic approximation.

Apply the principle successively to the four functions in (16). Intermediate periods only decrease, so all needed lcms remain \(O(R^4)=o(h)\). We obtain a period-two function agreeing with s at all but \(o_\eta(h)\) positions of (6). Every binary period-two function has the form \(\gamma x+\delta\).

Thus, for each fixed \(\eta>0\), s differs from an affine parity law in at most \(20\eta h+o_\eta(h)\) positions of the whole interval. Let h tend to infinity and then let \(\eta\downarrow0\). There are only four affine laws, so taking the minimum over them proves (1).

## 5. Consequence for containers in a protected row partition

At heights where the protected row partition is balanced, the [container purification](container_stability_reduction.md) gives the following uniform structural statement:
\[
 |U|\ge(1/2-o(1))h^2,\qquad
 e(H_\pi[U])=o(h^5\log h)
\]
implies that U differs in \(o(h^2)\) cells from one of the matched protected product patterns.

Indeed purification gives a full row-class box W within \(o(h^2)\) edits, with \(N_3(W)=o(h^4\log h)\). The theorem identifies its phase up to \(o(h)\) exceptional columns, which change only \(o(h^2)\) cells.

This resolves the aggregate inverse test when the row partition is protected. The unknown-row-partition case remains open: there, three selected corners do not directly supply an XOR tester, because a bounded vertical shift need not complement the row coloring.

