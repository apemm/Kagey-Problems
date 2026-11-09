# Sharp leading sea entropy from independent transversals

9 November 2026. The geometric supersaturation input is proved in the companion note [entropy_supersaturation.md](entropy_supersaturation.md). Independent review checked the primary-source container theorem, the degree hypotheses, the rotated-lattice argument, and the transversal count.

Let \(\pi=(A,B)\) be any balanced partition of the \(h\) rows, and use its full pair set \(F_\pi=A\times B\) in the sea-rival tests. Write \(\rho_\pi(h)\) for the largest recurrent sea-component radius. The result is
\[
 \max_{\pi\ {\rm balanced}}\rho_\pi(h)
 \le \left(\frac12+o(1)\right)h.                         \tag{1}
\]
The error is uniform over the partitions. Combined with the established canonical parity-component lower bound,
\[
 \lambda_*(h)\ge h/2-O_\epsilon(h^\epsilon),
\]
this gives
\[
 \lambda_*(h)\sim\rho_{\rm parity}(h)
 \sim\max_{\pi\ {\rm balanced}}\rho_\pi(h)\sim h/2.       \tag{2}
\]
This does not prove exact component dominance at a fixed height. Components can have the same leading asymptotic in \(h\) while differing at every finite height.

## 1. The four-cell hypergraph

Work on the square \(V=[h]\times[h]\), with the first coordinate denoting the column. Define a simple four-uniform hypergraph \(H_\pi\) as follows.

Choose a tilted lattice rectangle \(R\subset V\) whose four corners lie in distinct columns. Choose one of its corners \(D=(x,r)\), and choose \(t\in[h]\) in the opposite partition class from \(r\). Include the edge
\[
 (C(R)\setminus\{D\})\cup\{(x,t)\}.                    \tag{3}
\]
Repeated constructions of the same edge produce only one edge.

Every \(F_\pi\)-valid sea word on these \(h\) columns is an independent transversal of \(H_\pi\). It chooses exactly one cell in each column. If it contained (3), then \(D\) would be white, the other three rectangle corners would be black, and the singleton presentation \(\{D\}\) would have the virtual axis rival supplied by \(\{r,t\}\in F_\pi\).

This implication is all the proof uses. Many independent transversals of \(H_\pi\) can fail other sea-validity tests.

## 2. Uniform degrees and codegrees

There are absolute constants \(c,C>0\) such that, for sufficiently large \(h\),
\[
 ch^5\log h\le e(H_\pi)\le Ch^5\log h,                 \tag{4}
\]
and
\[
 \Delta_1(H_\pi)\le Ch^3\log h,\qquad
 \Delta_2(H_\pi)\le Ch^2,\qquad
 \Delta_3(H_\pi)\le Ch,\qquad
 \Delta_4(H_\pi)\le1.                                \tag{5}
\]
All bounds are uniform in \(\pi\).

To bound the rectangles through a fixed corner, write their adjacent vectors as
\[
 k(a,b),\qquad \ell(-b,a),
\]
with \(a,b\) positive and coprime, allowing a bounded number of reflections and choices of corner. Put \(r=\max(a,b)\). Containment in the square forces \(k,\ell\le h/r\). There are \(O(r)\) possible directions with this value of \(r\), so the total is
\[
 O\!\left(\sum_{r\le h}r(h/r)^2\right)=O(h^2\log h).
\]
If a fixed hypergraph vertex is one of the three original corners, multiply this count by at most \(h\) choices of the replacement row. If it is the replacement point, choose the missing corner's row in at most \(h\) ways and use the same rectangle count. This proves the first bound in (5), and hence the upper bound in (4).

For \(\Delta_2\), there are only constantly many assignments of two specified cells to their roles.

* If both are original corners and form a side, the other side lies on a perpendicular lattice line and has \(O(h)\) possible endpoints in the square. If they form a diagonal, a circle meets each horizontal grid row at most twice, again giving \(O(h)\) possibilities. There are at most \(h\) replacement rows.
* If one is the replacement cell, first choose the missing corner's row in at most \(h\) ways. The other specified corner and that missing corner determine a side or diagonal, giving \(O(h)\) rectangles as before.

Thus every pair belongs to \(O(h^2)\) edges.

For \(\Delta_3\), three original corners determine the rectangle, leaving at most \(h\) replacement rows. Otherwise two cells are original corners and the third is the replacement cell. The missing corner's column is fixed. If the two original corners form a side, the missing corner lies on one of two perpendicular lines, each intersecting that column at most once. These lines are not vertical because the rectangle is tilted. If they form a diagonal, the missing corner lies on a circle, with at most two points in that column. Thus this role assignment gives only constantly many edges.

The lower bound in (4) follows from the supersaturation lemma in the next section, applied to \(U=V\), with any fixed density margin less than \(1/2\).

## 3. Supersaturation above half density

The companion proof establishes that, for every fixed \(\eta>0\), there is \(c_\eta>0\) such that
\[
 |U|\ge(1/2+\eta)h^2
 \quad\Longrightarrow\quad
 e(H_\pi[U])\ge c_\eta h^5\log h                     \tag{6}
\]
for sufficiently large \(h\), uniformly in the balanced partition.

Here is the reduction identifying its input. For each nonzero vertical shift \(s\), put
\[
 B_s=\{(x,r)\in U:(x,r+s)\in U,\ 
           r\text{ and }r+s\text{ are in opposite classes}\}.
\]
If \(a_x,b_x\) are the two class counts in column \(x\), then
\[
 \sum_s|B_s|=2\sum_x a_xb_x.
\]
Both \(a_x,b_x\) are at most \(M=\lceil h/2\rceil\). The inequality
\[
 a_xb_x\ge M(a_x+b_x-M)
\]
therefore gives
\[
 \sum_s|B_s|\ge2M(|U|-Mh)\ge c\eta h^3.
\]
There are at most \(2h\) shifts and each \(B_s\) has at most \(h^2\) cells. Consequently at least \(c\eta h\) shifts have \(|B_s|\ge c\eta h^2\).

A set of fixed positive density in the square contains at least \(c_\eta h^4\log h\) tilted rectangles with distinct corner columns. This is the rotated-lattice rectangle lemma in the companion proof. Apply it to every dense \(B_s\). An all-\(B_s\) rectangle gives an edge of \(H_\pi[U]\) by replacing a corner \(D\) with \(D+(0,s)\). An unordered edge is counted at most four times: choosing which point is the replacement fixes the other three corners, the missing corner, and the shift. This proves (6).

## 4. The container input

Apply [Balogh, Morris, and Samotij, Theorem 2.2](https://arxiv.org/html/1204.6530#S2.Thm2) with \(k=4\), vertex count \(N=h^2\), and increasing family
\[
 \mathcal F=\{U:|U|\ge(1/2+\eta)h^2\}.
\]
Equations (4) and (6) give its density hypothesis with a positive constant depending only on \(\eta\). Equations (4) and (5) give its codegree hypotheses at
\[
 p=\frac{1}{h(\log h)^{1/3}}.                         \tag{7}
\]
Indeed \(e(H_\pi)/N\asymp h^3\log h\), and the four required bounds are respectively of orders
\[
 h^3\log h,\quad h^2(\log h)^{2/3},\quad
 h(\log h)^{1/3},\quad1.
\]

The theorem supplies a deterministic container \(C(S)\) for each allowed fingerprint \(S\). Every independent set \(I\) has a fingerprint \(S\subseteq I\) with
\[
 |S|\le C_\eta pN
      =C_\eta h/(\log h)^{1/3},\qquad
 I\setminus S\subseteq C(S),\qquad
 |C(S)|<(1/2+\eta)h^2.                               \tag{8}
\]
The fingerprint lies inside the independent set. This matters for counting transversals.

## 5. Count transversals, keeping their fingerprints

Let \(T_\pi(h)\) count independent transversals of \(H_\pi\). Set
\[
 \alpha=1/2+\eta,\qquad
 s_h=\left\lfloor C_\eta h/(\log h)^{1/3}\right\rfloor.
\]
A size-\(t\) fingerprint of a transversal uses \(t\) distinct columns, so there are at most \(\binom ht h^t\) possibilities.

Fix such a fingerprint. In each of the remaining \(h-t\) columns, the point must lie in \(C(S)\). The total number of available cells in these columns is at most \(\alpha h^2\). The arithmetic-geometric mean inequality bounds the number of completions by
\[
 \left(\frac{\alpha h^2}{h-t}\right)^{h-t}.
\]
Thus
\[
 T_\pi(h)\le
 \sum_{t=0}^{s_h}\binom ht h^t
 \left(\frac{\alpha h^2}{h-t}\right)^{h-t}.            \tag{9}
\]

For fixed \(\eta\), \(s_h/h\to0\). Writing \(\theta=t/h\), each summand divided by \(h^h\) is
\[
 \binom ht
 \left(\frac{\alpha}{1-\theta}\right)^{(1-\theta)h}.
\]
Uniformly for \(0\le t\le s_h\), its \(h\)-th root is at most \(\alpha+o(1)\). The number of summands has \(h\)-th root tending to one. Therefore
\[
 T_\pi(h)^{1/h}\le(\alpha+o(1))h,                    \tag{10}
\]
uniformly over \(\pi\).

Using a bound on the total number of containers would introduce an unnecessary factor involving \(\log h\). In (9), the \(h^t\) choices for fingerprint rows replace the \(t\) column choices already fixed by that fingerprint. Only a vanishing fraction of columns pays this cost.

## 6. Pass from blocks to entropy

Every length-\(h\) block in an infinite \(F_\pi\)-valid sea is counted by \(T_\pi(h)\). Splitting a length-\(m\) word into such blocks and a terminal block of length less than \(h\) gives
\[
 \#\{\text{sea words of length }m\}
 \le T_\pi(h)^{\lfloor m/h\rfloor}h^h.
\]
Hence
\[
 \rho_\pi(h)\le T_\pi(h)^{1/h}
 \le(1/2+\eta+o(1))h.
\]
Take the supremum over balanced partitions, then let \(h\to\infty\) and finally \(\eta\downarrow0\). This proves (1). The canonical lower bound proves (2).

No assertion here requires deciding which recurrent component or balanced partition is the exact maximizer at a particular height.

## 7. Consequence for optimal-blackout counts

For fixed \(h\), write
\[
 R_h^+=\limsup_{m\to\infty}a_h(m)^{1/m},\qquad
 R_h^-=\liminf_{m\to\infty}a_h(m)^{1/m}.
\]
The canonical insertion lower bound gives \(R_h^-\ge\lambda_*(h)\). Above the equality threshold, every optimal word uses exactly the \(q_h\) edges of a balanced complete bipartite row graph, with one singleton in every remaining column.

The exact marked transfer automaton has only finitely many double letters at fixed \(h\). Its recurrent components are copies of ordinary sea components, indexed by the already used double labels. Thus its exponential rate is at most \(\max_\pi\rho_\pi(h)\). The finite sum over partitions and every polynomial factor disappear under the \(m\)-th root. Consequently
\[
 \lambda_*(h)\le R_h^-\le R_h^+
 \le\max_\pi\rho_\pi(h),
\]
and (2) yields
\[
 \boxed{\displaystyle
 \lim_{h\to\infty}\frac{R_h^-}{h}
 =\lim_{h\to\infty}\frac{R_h^+}{h}=\frac12.}
\]
This statement does not assume that the limit in \(m\) exists at every fixed height, or interchange the two limits.
