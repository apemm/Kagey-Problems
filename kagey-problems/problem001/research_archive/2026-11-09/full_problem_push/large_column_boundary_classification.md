# Classification at the large-column boundary

Write \(q_h=\lfloor h^2/4\rfloor\) and \(r=\lfloor h/2\rfloor\). For an axis-valid board, replace each nonempty black column by any tree on its black rows. The resulting row graph \(H\) is simple and triangle-free. A column with \(k\) black rows gives the bound

\[
e(H)\le h-1+q_{h-k}.
\tag{1}
\]

The proof of (1) uses the individual completion restriction: after choosing a star on the distinguished column's rows, each outside row has at most one neighbor in that row set. This is stronger information than a total right-angle budget.

The first boundary admitting a triple column is

\[
e_*=h-1+q_{h-3}=q_h-r+1.
\]

The following theorem classifies equality for every \(h\ge7\).

**Theorem.** Suppose an axis-valid column family on \(h\ge7\) rows has a column of size at least three and its row-tree graph has \(e_*\) edges. Then it has exactly one triple column \(B\), and no larger column. Apart from empty and singleton columns, its remaining columns are:

1. Every edge of a balanced complete bipartite graph \(K_{a,b}\) on the other \(h-3\) rows, where \(a=\lfloor(h-3)/2\rfloor\) and \(b=\lceil(h-3)/2\rceil\).
2. Exactly one double column \(\{x,c(x)\}\) for each outside row \(x\), where \(c(x)\in B\).

The function \(c\) is a proper three-coloring of \(K_{a,b}\). Conversely, every family of this form is axis-valid and has \(e_*\) row-tree edges.

## Proof of the classification

For \(h\ge7\), the bound in (1) is strictly smaller than \(e_*\) when \(k\ge4\). Thus a distinguished large column has size exactly three.

Choose its tree to be a star. Equality in (1) forces every outside row to have exactly one neighbor in \(B\). It also forces the outside graph to attain Mantel's bound. That graph is therefore a balanced \(K_{a,b}\). Both parts have size at least two.

There cannot be a second triple \(C\). If \(|B\cap C|\ge2\), two rows occur together in two columns, giving an incidence 4-cycle.

Suppose \(|B\cap C|=1\). Choose the tree of \(C\) to be a star rooted at the common row. Its other two rows either lie in opposite parts of the outside \(K_{a,b}\), in which case their pair occurs in another column and creates a 4-cycle, or they lie in the same part. In the latter case they have a common outside neighbor. The two edges through that neighbor belong either to one other column, creating a 4-cycle, or to distinct columns, creating a 6-cycle together with \(C\).

Finally, suppose \(C\cap B=\varnothing\). Its tree is a two-edge path in \(K_{a,b}\). The endpoints have another common neighbor, since the opposite part has size at least two. The two edges through this second neighbor again give an incidence 4-cycle or 6-cycle.

Thus \(B\) is the only triple. Every other row-tree edge belongs to a double column. The outside edges are exactly those of \(K_{a,b}\), and each outside row has exactly one attachment to \(B\).

If two adjacent outside rows attached to the same row of \(B\), the three double columns would give an incidence 6-cycle. Hence the attachment map is a proper three-coloring.

Conversely, take a family described in the theorem. No row pair is repeated, so its incidence graph has no 4-cycle. A 6-cycle using three double columns would be a triangle in the double graph. The outside graph is bipartite, and the proper-coloring condition excludes triangles using one row of \(B\). A 6-cycle using the triple column would require an outside row attached to two rows of \(B\), which does not occur. The family is axis-valid.

## Exact size and number of boundary cores

The number of nonsingleton columns is

\[
1+ab+(h-3)=q_h-r.
\]

The number of black points in these columns is

\[
3+2ab+2(h-3)=2(q_h-r)+1.
\]

Thus the classification describes every axis-extremal board at the sharp width \(m=q_h-r\), for \(h\ge7\). Empty columns cannot occur at this optimum: they would increase \(e(H)\) beyond \(e_*\). If a board attaining this optimum had only double and singleton columns, it would contain at most \(2m\) black points.

There are

\[
P_{a,b}(3)=3(2^a+2^b-2)
\tag{2}
\]

proper three-colorings of \(K_{a,b}\). To count them, first let the \(a\)-part use one color. There are \(3\cdot2^b\) choices. If it uses two colors, there are \(3(2^a-2)\) choices and the other part must use the remaining color. It cannot use all three colors.

The total number of labeled column multisets is consequently

\[
\boxed{
\binom h3\,
\frac{\binom{h-3}{a}}{1+\mathbf1_{a=b}}\,
3(2^a+2^b-2).
}
\tag{3}
\]

There is no overcount from a different choice of triple or outside partition. The triple is unique, and the connected outside complete bipartite graph determines its bipartition up to swapping parts.

For \(h=7,8,9\), formula (3) gives respectively 1,890, 16,800, and 35,280 multisets. These counts concern axis-valid cores. Their geometric row order is fixed, and their column permutations still have to satisfy all tilted-rectangle constraints.

At height seven, the 1,890 core multisets have no valid full-rectangle ordering. The subsequent analysis also excludes every 18-point board at width nine, giving the exact full value \(f(7,9)=17\). The general theorem does not assert that the higher-height boundary cores admit or fail to admit full-rectangle orderings.
