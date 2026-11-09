# A reduction of container stability to an aggregate rectangle test

9 November 2026. This note separates a proved purification step from the unresolved stability statement needed to apply the Cartesian-box theorem to entropy containers.

Fix a balanced row partition \(\pi=(B_0,B_1)\). Let \(\mathcal H_{h,\pi}\) be the four-uniform singleton-rival hypergraph from [the supersaturation proof](entropy_supersaturation.md), on the \(h\times h\) board. Its edges consist of three tilted rectangle corners and an opposite-block selected cell in the fourth corner's column; the four rectangle columns are distinct.

## 1. Few hyperedges force almost pure columns

Suppose a sequence of cell sets \(U\subseteq[h]^2\) satisfies
\[
 |U|\ge(1/2-o(1))h^2,\qquad
 e(\mathcal H_{h,\pi}[U])=o(h^5\log h).
\tag{1}
\]
Write
\[
 a_x=|U_x\cap B_0|,\qquad b_x=|U_x\cap B_1|.
\]
Then
\[
 \sum_{x=1}^h a_xb_x=o(h^3).
\tag{2}
\]

Indeed, if the left side were at least \(\varepsilon h^3\) on a subsequence, the shifted-intersection argument in the supersaturation note would apply directly. The identity
\[
 \sum_{s\ne0}
 \#\{(x,y)\in U:(x,y+s)\in U,\ \pi(y)\ne\pi(y+s)\}
 =2\sum_x a_xb_x
\]
would give \(c_\varepsilon h\) dense shifted intersections. Each contains \(c_\varepsilon h^4\log h\) tilted rectangles, and the bounded-multiplicity map gives \(c_\varepsilon h^5\log h\) hyperedges. This contradicts (1). The argument uses mixed-column mass rather than a density excess above one half.

Choose \(t_x\) to be a block with the larger column count, and define the full row-class box
\[
 W=\{(x,y):y\in B_{t_x}\}.
\tag{3}
\]
Since \(\min(a_x,b_x)\le\sqrt{a_xb_x}\), Cauchy--Schwarz and (2) give
\[
 \sum_x\min(a_x,b_x)=o(h^2).
\]
The total number of retained majority-block points is therefore at least \(h^2/2-o(h^2)\). Each full block has size \(h/2+O(1)\), so its total deficit is \(o(h^2)\). Consequently,
\[
 |U\triangle W|=o(h^2).
\tag{4}
\]

The maximum-degree estimate
\[
 \Delta_1(\mathcal H_{h,\pi})=O(h^3\log h)
\]
from [the container proof](sea_entropy_half_container.md) now implies
\[
 e(\mathcal H_{h,\pi}[W])=o(h^5\log h).
\tag{5}
\]
Adding or deleting one cell changes at most \(\Delta_1\) hyperedges, so (4) preserves the small-edge condition.

Thus an almost-half container with few singleton-rival hyperedges is close to a **full** row-class box with few hyperedges. This is stronger than merely obtaining small average omissions.

## 2. The remaining statement is an orthogonal-rectangle test

For a full row-class box W, let \(N_3(W)\) count tilted lattice rectangles with exactly three corners in W. First restrict to rectangles in four distinct columns.

Every such rectangle produces at least \(\lfloor h/2\rfloor\) hyperedge descriptions, by choosing the selected cell in its missing corner's column. Conversely a hyperedge has at most four descriptions: choose which of its four cells is the selected opposite-block cell; the other three determine the right triangle and its completion. Therefore
\[
 \frac{\lfloor h/2\rfloor}{4}N_3^{(4)}(W)
 \le e(\mathcal H_{h,\pi}[W])
 \le \lceil h/2\rceil N_3^{(4)}(W).
\tag{6}
\]
The number of tilted rectangles with a repeated column is \(O(h^3\log h)\), by summing the repeated-column estimate in the supersaturation proof over primitive directions. They are negligible at the \(h^4\log h\) scale. Hence (5) is equivalent, up to this negligible family, to
\[
 N_3(W)=o(h^4\log h).
\tag{7}
\]

A sufficient missing theorem is the following aggregate stability statement.

> For balanced row colorings c and arbitrary column phases t, if the product coloring
> \[
> 1_W(x,y)=1_{\{c(y)=t_x\}}
> \]
> has (7), then c and t differ in \(o(h)\) positions from laws
> \[
> c_0(y)=\kappa q(y)+\alpha y+\beta,\qquad
> t_0(x)=\kappa q(x)+\gamma x+\delta,
> \]
> with the same quadratic coefficient and with \(\alpha=1\) when \(\kappa=0\).

Together with (4), this would place U within \(o(h^2)\) cells of a protected product pattern. The statement is not proved here.

## 3. Why the current Cartesian theorem does not establish the target

The [near-full Cartesian theorem](near_full_variable_box_stability.md) assumes that every word in the box avoids the relevant rivals. Condition (7) allows some forbidden rectangles, and does not bound their number separately for each geometry.

The square-step identities in that theorem come from a small set of specified directions and scales. A fixed primitive direction contributes \(O(h^4)\) rectangles, whereas all directions together contribute \(\Theta(h^4\log h)\). Thus a whole specified direction may be defective while still contributing only \(o(h^4\log h)\). The same problem applies to the low-span templates used to identify the phase.

There is also a boundary issue in applying the finite theorem literally: it uses a column interval of length \(4h+20\), while the entropy container is initially defined on an \(h\times h\) block. One can formulate containers on a fixed wider aspect ratio, but that does not remove the aggregate-versus-pointwise distinction.

The existing purification step therefore does not justify deleting a few cells to make W an independent Cartesian box. Such a repair theorem, or the weaker aggregate rectangle-test statement above, is an additional mathematical input.

## 4. A possible route and its exact missing link

For one primitive perpendicular direction pair, decompose the grid into cosets of the rotated lattice. In each coset, tilted rectangles become ordinary \(2\times2\) submatrices. Exactly three selected corners are induced three-edge paths in the corresponding bipartite graph. An induced removal theorem would make a graph with few such patterns close to a disjoint union of complete bipartite components.

This observation identifies a possible inverse approach, but two further steps are needed:

1. The small total in (7) must supply enough useful perpendicular directions, with uniform error after weighting by their geometric contribution.
2. The resulting approximate component structures in different rotated coordinate systems must be reconciled with the original separable form \(1_{\{c(y)=t_x\}}\).

No such reconciliation is proved here. In particular, the statement that every high-entropy component follows a protected phase would be stronger than the established results.

