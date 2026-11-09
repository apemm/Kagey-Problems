# Individual completions and structure near the row bound

9 November 2026. The square exponent remains open. This note uses individual
axis-completion constraints to prove an exact finite-width theorem for the
axis-only problem and a structural classification for full blackouts close
to the row bound. It also records an independent audit of the counterexample
to the minimum-width conjecture in A338885.

Let \(q_h=\lfloor h^2/4\rfloor\). Write \(f_{\rm ax}(h,m)\) for the
maximum blackout that distinguishes axis-aligned rectangles only. The full
problem has \(f(h,m)\le f_{\rm ax}(h,m)\). Assume \(m\ge3\), so
axis-validity is equivalent to the row-column incidence graph having no
four- or six-cycle.

## 1. Individual completion injectivity restricts a large column

Let the nonempty black-row sets of the columns be \(B_i\), and let \(t\)
be their number. Choose a tree on every \(B_i\) and take their union \(H\)
on the row vertices. The paper's row-graph lemma gives

\[
 H\text{ simple and triangle-free},\qquad e(H)=|S|-t.
 \tag{1}
\]

**Large-column bound.** If one column has \(k\) black points, then

\[
 |S|-t\le h-1+q_{h-k},
 \qquad |S|-m\le h-1+q_{h-k}.
 \tag{2}
\]

**Proof.** Let \(B\) be the distinguished column's \(k\)-point row set.
Choose its tree to be a star. No other column contains two rows of \(B\),
since that would give a four-cycle. Thus \(H[B]\) has exactly \(k-1\)
edges.

Every row \(x\notin B\) has at most one neighbor in \(B\) in \(H\).
If two such edges came from the same column, that column would meet \(B\)
twice and give a four-cycle. If they came from different columns, those
columns and the distinguished column would give a six-cycle. Equivalently,
two axis right angles would complete at the same cell \((\text{column }B,x)\).

There are consequently at most \(h-k\) edges from \(B\) to its complement.
The complementary induced graph is triangle-free and has at most
\(q_{h-k}\) edges. Adding these three contributions gives
\((k-1)+(h-k)+q_{h-k}=h-1+q_{h-k}\). Finally \(t\le m\).
\(\square\)

For \(k\ge3\), (2) yields

\[
 |S|-t\le h-1+q_{h-3}
          =q_h-\lfloor h/2\rfloor+1.
 \tag{3}
\]

This is a pointwise completion restriction, rather than an aggregate count
of all completions in a region.

## 2. The same threshold forces the row graph to be bipartite

**Triangle-free graph bound.** If a triangle-free graph on \(h\) vertices is
not bipartite, then

\[
 e(H)\le q_{h-1}+1=q_h-\lfloor h/2\rfloor+1.
 \tag{4}
\]

**Proof.** Its shortest odd cycle has length \(2s+1\), where \(s\ge2\),
and is chordless. Put \(u=h-2s-1\). Each outside vertex has at most \(s\)
neighbors on the cycle, because its neighbors form an independent subset of
that odd cycle. The outside graph is triangle-free. Therefore

\[
 e(H)\le2s+1+su+\lfloor u^2/4\rfloor.
\]

On the other hand,

\[
 q_{h-1}+1=\lfloor u^2/4\rfloor+su+s^2+1.
\]

The latter exceeds the preceding bound by \(s(s-2)\ge0\).
\(\square\)

The proof is included to make the threshold independent of a graph stability
theorem. At this threshold, a five-cycle with two adjacent vertices replaced
by independent sets can attain equality.

## 3. Classification within a linear-size deficit

Put \(r=\lfloor h/2\rfloor\), and suppose

\[
 |S|=m+q_h-\delta.
\]

Let \(z=m-t\) be the number of empty columns. Its intrinsic row-graph
deficit is

\[
 \eta=q_h-(|S|-t)=\delta-z.
 \tag{5}
\]

Mantel's bound gives \(0\le z\le\delta\).

**Near-bound classification.** If \(\eta<r-1\), every nonempty column is
a singleton or a double. The distinct row pairs of the doubles form a
bipartite graph. In particular this conclusion holds whenever
\(\delta<r-1\).

**Proof.** A column of size at least three contradicts (3). Once all columns
have size at most two, \(H\) is precisely the graph of double pairs.
If this graph were not bipartite, (4) would contradict \(\eta<r-1\).
\(\square\)

This gives a complete axis-only description. The double graph has

\[
 d=q_h-\delta+z
\]

edges. For some bipartition of sizes \(a,h-a\), it is obtained from
\(K_{a,h-a}\) by deleting exactly

\[
 b=\delta-z-\bigl(q_h-a(h-a)\bigr)\ge0
 \tag{6}
\]

edges. Every such graph, with its edges assigned to distinct double columns,
and arbitrary remaining singleton rows, is axis-valid. Full validity still
requires the tilted-rectangle tests.

The allowed imbalance is explicit. For \(h=2r\), write \(a=r+j\). Then
\(q_h-a(h-a)=j^2\). For \(h=2r+1\), write the smaller part as \(r-j\).
Then the loss is \(j(j+1)\). Thus a fixed small deficit allows only a few
part sizes and a few missing cross-edges.

For \(h=6\), \(\delta=1\), (6) gives exactly the paper's three cases:
\(K_{3,3}\) minus one edge, \(K_{2,4}\), or one empty column and the full
\(K_{3,3}\). The argument now applies at every height and to every deficit
less than \(\lfloor h/2\rfloor-1\).

## 4. An exact finite-width theorem for the axis problem

**Theorem.** If \(h\ge4\), \(m\ge3\), and
\(m\ge q_h-\lfloor h/2\rfloor+1\), then

\[
 \boxed{\displaystyle
 f_{\rm ax}(h,m)=\min\{2m,m+q_h\}.}
 \tag{7}
\]

**Proof.** First suppose \(q_h-r+1\le m\le q_h\). If an axis-valid
blackout had more than \(2m\) points, its deficit would satisfy

\[
 \delta=m+q_h-|S|<q_h-m\le r-1.
\]

The near-bound classification would make every column have at most two
black points, a contradiction. Conversely, choose any \(m\) distinct edges
of a balanced complete bipartite graph on the rows and use them as double
columns. This is axis-valid and has \(2m\) black points.

For \(m\ge q_h\), use all \(q_h\) cross-edges as doubles and use
arbitrary singletons in the remaining columns. This attains the row bound
\(m+q_h\). \(\square\)

Consequently the full problem has the finite-width upper bound

\[
 f(h,m)\le2m
 \quad\text{when }q_h-\lfloor h/2\rfloor+1\le m\le q_h.
 \tag{8}
\]

The theorem does not assert equality in (8). Tilted rectangles can decrease
the optimum. For example, the known full values at \((h,m)=(6,7),(6,8)\)
are 13 and 15, while their axis-only values are 14 and 16.

**Sharpness of the width threshold.** For every \(h\ge5\), put
\(m=q_h-r\). There is an axis-valid blackout with \(2m+1\) points.
Choose three distinguished rows \(B=\{b_0,b_1,b_2\}\), and partition
the remaining \(h-3\) rows into balanced parts \(A,C\). Use the columns

\[
 B,\qquad
 \{b_0,a\}\ (a\in A),\qquad
 \{b_1,c\}\ (c\in C),\qquad
 \{a,c\}\ (a\in A,c\in C).
\]

There are
\(1+(h-3)+q_{h-3}=q_h-r=m\) columns. One is a triple and all others
are doubles, giving \(2m+1\) black points. No row pair occurs twice.
The graph formed by the doubles is bipartite. A six-cycle involving the
triple column would require an outside row attached to two rows of \(B\),
which the construction excludes. Thus its incidence graph has neither a
four- nor a six-cycle.

This construction also shows that the strict deficit threshold in Section 3
is sharp for axis-validity. It is not asserted to distinguish tilted
rectangles.

In fact it is optimal at that width:
\(f_{\rm ax}(h,q_h-r)=2(q_h-r)+1\). One further black point would make
\(\delta\le r-2\), forcing all columns to have size at most two and
contradicting the claimed size.

## 5. Counting the axis-valid candidates near the bound

For \(0\le\delta<r-1\), the double graph has more than \(q_{h-1}\)
edges and is connected. Indeed, among disconnected triangle-free graphs,
the sum of the Mantel bounds for the components is at most \(q_{h-1}\).
The bipartition is therefore unique up to swapping its sides.

The exact number of axis-valid blackouts of size \(m+q_h-\delta\) is

\[
 \sum_{z=0}^{\delta}
 \frac{m!\,h^{s_z}}{2z!s_z!}
 \sum_{a=1}^{h-1}\binom ha\binom{a(h-a)}{d_z},
 \qquad
 d_z=q_h-\delta+z,\quad s_z=m-q_h+\delta-2z,
 \tag{9}
\]

where terms with \(s_z<0\) are omitted. Choose the bipartition and its
\(d_z\) edges, divide by two for swapping the sides, then place the
distinct double edges and \(z\) indistinguishable empty columns. The
\(s_z\) singleton rows each have \(h\) choices. For \(\delta=0\), (9)
reduces to the established equality-structure count.

Equation (9) counts candidates for the full geometric problem. It does not
count full valid blackouts without an additional tilted-rectangle filter.

## 6. The next borderline on seven rows

The bounds identify a small structural family for a possible 19-point
blackout on a \(7\times9\) grid. Here \(q_7=12\), \(r=3\), and
\(\delta=2\). Empty columns would make \(\eta<2\), forcing doubles only
and hence at most 18 points. A column of size four or more would give
\(|S|-t\le6+q_3=8\), also impossible. Thus there is a triple column.

Fix its three rows \(B\). Equality in (2) forces the graph on the other
four rows to be \(K_{2,2}\), and each outside row has exactly one neighbor
in \(B\). No second triple column is possible. If it met \(B\) in two
rows it would give a four-cycle. If it met \(B\) in one row, choose its
tree as a star centered at that row. Its two outside rows either form an
outside edge, causing a repeated row pair, or lie in the same part of
\(K_{2,2}\), where a common neighbor gives a six-cycle. If it avoided
\(B\), its three-row tree is a two-edge path in \(K_{2,2}\). The path's
endpoints have a second common neighbor outside that column, again giving
a four- or six-cycle in the incidence graph.

Therefore there is exactly one triple and eight doubles. The doubles are the
four \(K_{2,2}\) edges and four attachments to \(B\). The attachments give
a proper three-coloring of \(K_{2,2}\): endpoints of an outside edge cannot
attach to the same row of \(B\), since that gives a six-cycle.

There are \(\binom73\cdot3\cdot18=1890\) labeled column-multiset
patterns before arranging the nine columns. This is a reduction for a future
exact check, not a claim that the full 19-point case is satisfiable or
unsatisfiable. No SAT result is asserted here.

## 7. A resolved minimum-width conjecture

[A338885](https://oeis.org/A338885) defines its row index as the geometric
height span of the enclosing rectangle. Its conjecture that the smallest
width equals [A228286](https://oeis.org/A228286) is false at height 655.
The corners

\[
 (62,0),\quad(104,4),\quad(42,655),\quad(0,651)
\]

form a tilted rectangle of width 104 and height 655. The adjacent vectors
\((42,4)\) and \((-62,651)\) have dot product zero. Exact minimization
gives

\[
 \min\{\text{rectangle width at height }655\}=104,
 \qquad A228286(655)=115.
\]

Both minima have short arithmetic certificates. For A228286, suppose
\(xy+z=655\) and \(x+yz\le114\). Necessarily \(z\le114\), while

\[
 (x+yz)^2\ge4xyz=4z(655-z).
\]

For \(5\le z\le114\), the right side is at least
\(4\cdot5\cdot650=13000>114^2\). Thus only \(z=1,2,3,4\) need checking.
The factorizations

\[
 654=2\cdot3\cdot109,\quad 653\text{ prime},\quad
 652=4\cdot163,\quad 651=3\cdot7\cdot31
\]

give respective minima of \(x+zy\) equal to 115, 655, 175, and 115.
The choice \((x,y,z)=(109,6,1)\) attains 115.

For the unrestricted rectangle minimum, parameterize its perpendicular
sides using positive integers \(k,l,p,q\). Its height and width are
\(kq+lp\) and \(kp+lq\). A width smaller than its height can be
normalized to \(p>q\) and \(l>k\), by swapping both pairs if necessary.
If any factor equals one, the two expressions reduce, after relabeling, to
the A228286 optimization. Otherwise all factors are at least two. Put
\(t=kq\), so \(4\le t<655/2\). Then

\[
 (kp+lq)^2\ge4klpq=4t(655-t).
\]

A width at most 103 therefore forces \(t=4\). Thus \(k=q=2\) and
\(lp=651\). Its closest positive factor pair is \(21,31\), giving
\(kp+lq=2(p+l)\ge104\), a contradiction. The displayed rectangle attains
104. This proves both claimed values without relying on the search.

[minimum_width_audit.py](minimum_width_audit.py) independently scans every
height from 2 through 655 and finds no earlier counterexample. It computes
the unrestricted minimum from positive integers \(a,b,c,d\) satisfying
\(ac=bd\), \(b+d=n\), with width \(a+c\). The AM--GM pruning test
\(4b(n-b)>(a+c)^2\) is rigorous. A separate exhaustive \((x,y)\) scan
checks the value of A228286 at 655. The saved results are in
[minimum_width_audit.json](minimum_width_audit.json).

These dimensions are coordinate spans. The rectangle would occupy a grid
with 656 rows and 105 columns if both boundary endpoints are counted as
grid points. The counterexample settles this auxiliary conjecture, not the
blackout extremal function.

## 8. Remaining square question

No argument here improves the square exponents. The proved bounds remain
\(\Omega(n^{6/5}(\log n)^{-1/5})\) and
\(O(n^{4/3}(\log n)^{-1/3})\), as established in
[square_progress.md](../odd_graph_entropy_square/square_progress.md).
The finite-width results use exact individual completion constraints and
give a restricted family near the row bound. They leave the interaction of
singleton completions from different directions, and repeated two-white
presentations, unresolved in the square regime.

[near_bound_axis_check.py](near_bound_axis_check.py) exhaustively checks the
large-column and near-bound conclusions for column families on at most six
rows with at most four nonsingleton columns. It also checks the sharpness
construction for heights 5 through 30 and all 1890 seven-row borderline
patterns. All checks pass. They verify finite cases; the general theorems
follow from the proofs above.
