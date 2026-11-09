# An unconditional finite formula at every width

9 November 2026. The structural scalar formulas remain incomplete. There is nevertheless an exact finite transfer formula that simultaneously returns the optimum and its multiplicity at every width. This note makes that computational answer explicit. It does not replace the unresolved dominance theorem by an assumption.

Fix \(h\ge4\). For \(m\ge4\), let
\[
 Z_{h,m}(t)=\sum_{S\text{ valid on }[h]\times[m]}t^{|S|}.
\]
Then
\[
 f(h,m)=\deg_t Z_{h,m}(t),\qquad
 a_h(m)=[t^{f(h,m)}]Z_{h,m}(t).                 \tag{1}
\]
The construction below expresses \(Z_{h,m}\) through finitely many matrices depending only on \(h\). It counts all sizes before extracting the largest one.

## 1. The finite choices of nonsingleton columns

Let \(\mathfrak B_h\) consist of all unordered families \(\mathcal B\) of distinct subsets of \([h]\), each of size at least two, whose row-column incidence graph has no four- or six-cycle. Include the empty family.

Every axis-valid board determines exactly one such family: discard its empty and singleton columns and forget the order of the remaining row sets. A row pair cannot occur in two columns. Conversely, any order of a family in \(\mathfrak B_h\), together with arbitrary empty and singleton columns, identifies axis-aligned rectangles.

The row-tree bound gives
\[
 \sum_{B\in\mathcal B}(|B|-1)\le q_h
 =\lfloor h^2/4\rfloor.
\]
In particular, \(|\mathcal B|\le q_h\). Thus \(\mathfrak B_h\) is finite independently of the width.

For a fixed family put
\[
 F_{\mathcal B}=\bigcup_{B\in\mathcal B}\binom B2,\qquad
 \mathcal A_{\mathcal B}=\{\varnothing,\{1\},\ldots,\{h\}\}\cup\mathcal B.
\]
The pair set used in every virtual axis-rival test is this complete final set, including columns not yet read.

## 2. A finite local matrix

Put \(L=2W_h\), where \(W_h=1+\lfloor(h-1)^2/4\rfloor\). Use histories of at most \(L\) letters from \(\mathcal A_{\mathcal B}\), including the empty history. Appending one column rejects a transition exactly when it completes:

1. a hidden tilted rectangle;
2. a tilted presentation with one or two white corners and an axis rival, using \(F_{\mathcal B}\);
3. two tilted rectangles with the same nonempty presentation.

Use actual rectangle-contained tests, rather than normalizing a black support across an unavailable boundary. The initial short histories and acceptance of every terminal history handle the two finite ends exactly.

These tests have memory at most \(L\). The first two involve one tilted rectangle, of span at most \(W_h\). Two tilted rectangles sharing a shown point have union span at most \(2W_h\). A presentation with at least three points determines its rectangle. By [the no-hidden theorem](hidden_rectangles_and_exact_hypergraph.md), no valid board with \(h,m\ge4\) has a hidden rectangle, so no global hidden counter is needed.

Let \(D_B\) be the zero-one matrix for appending column \(B\) under these rules. It is indexed by the finite history set. Introduce commuting markers \(x_B\), one for each \(B\in\mathcal B\), with \(x_B^2=0\), and set
\[
 M_{\mathcal B}(t,\mathbf x)
 =D_{\varnothing}
  +t\sum_{r=1}^hD_{\{r\}}
  +\sum_{B\in\mathcal B}x_Bt^{|B|}D_B.
\tag{2}
\]
Let \(\alpha\) select the empty history and let \(\beta\) be one on every history.

## 3. The exact formula

For every \(h,m\ge4\),
\[
 \boxed{\displaystyle
 Z_{h,m}(t)=
 \sum_{\mathcal B\in\mathfrak B_h}
 \left[\prod_{B\in\mathcal B}x_B\right]
 \alpha M_{\mathcal B}(t,\mathbf x)^m\beta.}
\tag{3}
\]

The marker coefficient requires each nonsingleton column exactly once. No other nonsingleton columns are allowed in that summand. The weight records the number of black cells. Every valid board appears in the summand for its unique family \(\mathcal B\), and the deterministic history path counts it once.

Conversely, each accepted path satisfies axis-axis uniqueness by its family choice. The local tests exclude every collision involving a tilted rectangle. Two disjoint hidden rectangles cannot be an omitted collision because hidden rectangles are already rejected. Thus every counted word is valid.

Equation (3) is also a finite algorithm for obtaining both numbers in (1), with integer arithmetic only. It is typically too large for direct use at a large height.

## 4. Rationality in width and black-cell weight

Define
\[
 \mathcal R_h(z,t)=
 \sum_{\mathcal B\in\mathfrak B_h}
 \left[\prod_{B\in\mathcal B}x_B\right]
 \alpha(I-zM_{\mathcal B}(t,\mathbf x))^{-1}\beta.
\tag{4}
\]
Expanding the nilpotent markers makes this a finite sum of products of ordinary finite-matrix resolvents. Hence \(\mathcal R_h(z,t)\) is rational in \(z,t\). Its coefficient of \(z^m\) is exactly \(Z_{h,m}(t)\) for \(m\ge4\). The finitely many shorter-width coefficients can be replaced separately if a series starting at width zero is wanted.

This supplies an unconditional general finite form, including widths below the equality threshold. It does not simplify \(f(h,m)\) to a scalar expression, or identify the dominant eigenvalue controlling the optimal coefficient. The refined construction determines that coefficient's degree for all \(m\ge C_\varepsilon h^2(1+\log h)^{2+\varepsilon}\). General dominance is still needed for the proposed single product asymptotic for its leading coefficient.

For optimal counts beyond the threshold,
[the exact sea-resolvent formula](sea_resolvent_counting_formula.md)
uses \(q_h+1\) unmarked resolvents in each summand. It also gives
an eventual integer recurrence whose denominator is controlled
by ordinary singleton-sea determinants.

## 5. Include the thin grids by symmetry

To apply the computational answer to every nonempty rectangular grid,
first interchange the dimensions if necessary so \(h\le m\).
The cases \(h\le3\) already have explicit answers:

| Dimensions | Optimum | Number of optima |
|---|---:|---:|
| \(h=1\) | \(m\) | \(1\) |
| \(h=m=2\) | \(4\) | \(1\) |
| \(h=2,\ m\ge3\) | \(m+1\) | \(m2^{m-1}\) |
| \(h=m=3\) | \(5\) | \(53\) |
| \(h=3,\ m\ge4\) | \(m+2\) | The existing closed form below |

On two rows and at least three columns, two fully black columns
would give the same presentation with any third column. An optimum
therefore has exactly one fully black column and a singleton in
each other column. Choosing that column and the remaining black rows
gives \(m2^{m-1}\). The one-row and two-by-two cases have at most one
rectangle, so blackening the entire grid is valid.

For three rows, the already proved formula in
[the manuscript](../../../jis/sections/sec05_three.tex) is
\[
a_3(m)=4(m-1)(3m+2)3^{m-5}
       +p_+(m)(1+\sqrt3)^m+p_-(m)(1-\sqrt3)^m
       +(-2)^{\lfloor m/2\rfloor}\kappa(m)
\quad(m\ge4),
\]
where
\[
432p_\pm(m)=(19\pm11\sqrt3)m^2
 +(61\pm41\sqrt3)m+104\pm28\sqrt3,
\]
and
\[
\kappa(m)=
\begin{cases}
(2m^2+41m-104)/216,&m\text{ even},\\
(7m^2-32m-175)/432,&m\text{ odd}.
\end{cases}
\]
These thin-grid results are recalled from the existing work, not
claimed as new. Together with (1)--(3) for \(h,m\ge4\), they give
an unconditional exact finite algorithm for the optimum and its
multiplicity on every nonempty grid.
