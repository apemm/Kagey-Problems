# The exact value on seven by nine

The computer-assisted result is

\[
f(7,9)=17.
\]

The lower bound has a short explicit witness. The upper bound combines an analytical classification of all possible column multisets with a complete finite search over their orders. This is an exact finite result, not an asymptotic theorem or a claim based on a failed heuristic search.

## A verified lower bound

Read each entry as the black row set in one column, with rows numbered from 1:

\[
17,\quad7,\quad47,\quad67,\quad6,\quad6,\quad56,\quad345,\quad123.
\]

These nine columns contain 17 points. All 1,113 lattice rectangles in the board have distinct white presentations. The check uses both the bitset rectangle generator in `verify_narrow.py` and the constructive generator in `solver/enumerate.py`.

The reproducible witness and checks are in `seven_nine_seventeen_witness.py` and `seven_nine_seventeen_witness.json`.

The older report states \(c(7,9)\ge2\), where \(f(h,m)=h+m-1+c(h,m)\). That statement supplies a lower bound of 17, not 18.

## Why every 18-point candidate has a small column description

Write \(B_i\subseteq\{1,\dots,7\}\) for column \(i\)'s black rows. Axis-aligned identification is necessary for full identification. Its incidence graph has neither a 4-cycle nor a 6-cycle.

For each nonempty \(B_i\), choose a tree on its rows. The union is a simple triangle-free graph \(H\). If there are \(z\) empty columns and 18 black points, then

\[
e(H)=18-(9-z)=9+z.
\tag{1}
\]

Suppose a column contains \(k\) black rows. Choose its tree to be a star. Its row set \(B\) has exactly \(k-1\) induced edges in \(H\). A vertex outside \(B\) has at most one neighbor in \(B\), since two would create an incidence 4-cycle or 6-cycle. Mantel's bound applies to the graph on the other \(7-k\) vertices. Consequently,

\[
e(H)\le (k-1)+(7-k)+\left\lfloor\frac{(7-k)^2}{4}\right\rfloor
=6+\left\lfloor\frac{(7-k)^2}{4}\right\rfloor.
\tag{2}
\]

In particular, a column of size at least four would force \(e(H)\le8\), contradicting (1). Every column therefore has size at most three.

There are no empty columns. To prove this, suppose \(z\ge1\). If all nonempty columns have size at most two, they contain at most \(2(9-z)<18\) points. Thus a triple column exists. Equation (2) gives \(e(H)\le10\), so (1) forces \(z=1\) and \(e(H)=10\).

Equality in (2) for a triple \(B\) has a rigid form. The four remaining rows induce \(K_{2,2}\), and each is attached to exactly one row of \(B\). There cannot be another triple column:

* A second triple meeting \(B\) twice repeats a row pair, giving an incidence 4-cycle.
* If it meets \(B\) once, its other two rows are either in opposite parts of \(K_{2,2}\), repeating a row pair, or in the same part, sharing another neighbor and giving a 4-cycle or 6-cycle.
* If it is disjoint from \(B\), its two tree edges form a path in \(K_{2,2}\). The endpoints have a second common neighbor. The two edges through that neighbor belong either to one other column, giving a 4-cycle, or to distinct columns, giving a 6-cycle.

Thus equality requires one triple and eight double columns, already nine nonempty columns. This contradicts \(z=1\).

Let \(t,d,s\) count triple, double, and singleton columns. The two equations

\[
t+d+s=9,\qquad 3t+2d+s=18
\]

give

\[
s=t,\qquad d=9-2t,\qquad 0\le t\le4.
\tag{3}
\]

Equations (2) and (3), including the exclusion of empty columns, are the analytical reduction. No arbitrary row permutation is used: the actual seven row labels remain fixed throughout the search.

## Complete enumeration of the column multisets

The pair shadow of a column family joins two rows when some column contains both. When a new nonsingleton column is added, its rows must have pairwise distance at least three in the previous pair shadow.

This is an exact test. A distance-one pair repeats a pair of rows and creates an incidence 4-cycle. A distance-two pair creates a 6-cycle unless both old edges belong to one old column, in which case the pair was already at distance one. Conversely, every new 4-cycle or 6-cycle has one of these forms. An incidence 6-cycle uses three distinct columns, so adding two or three pair-shadow edges from a single new triple does not introduce an additional case.

`build_seven_nine_eighteen.py` exhausts the choices in (3). It first selects distinct triple columns and then distinct double columns. Singleton rows are selected with repetition. The exact counts are:

| Triple columns \(t\) | Double columns | Singleton columns | Nonsingleton families | Full column multisets |
|---:|---:|---:|---:|---:|
| 0 | 9 | 0 | 12,670 | 12,670 |
| 1 | 7 | 1 | 18,480 | 129,360 |
| 2 | 5 | 2 | 3,780 | 105,840 |
| 3 | 3 | 3 | 0 | 0 |
| 4 | 1 | 4 | 0 | 0 |
| Total | | | | 247,870 |

The singleton multiplicity factor is \(\binom{6+t}{t}\). Vertical reflection reduces this list to 124,087 representatives. Each is stored explicitly in `seven_nine_eighteen_data.json`.

`audit_seven_nine_families.py` independently repeats the complete enumeration using row-pair owners. It checks every row triple for three distinct column owners, rather than using the incremental pair-shadow distance test. It obtains the same five nonsingleton counts and exactly the same set of 124,087 representatives. The audit completed in 6.375 seconds.

## Exact rectangle checks during the ordering search

The search orders every candidate multiset, rejecting a prefix only when its current black points already force a collision in every completion of that prefix. Newly completed tilted rectangles are grouped by their rightmost column. Rectangles with at least three white corners need no comparison, since three corners determine at most one rectangle.

For presentations with at most two white corners, the search compares against all earlier tilted presentations. It also uses the exact axis-rival tests below. Let \(F\) contain every row pair appearing in any column of the candidate multiset. Its definition includes pairs in triple columns.

* A singleton presentation at \((c,r)\) has an axis rival exactly when some \(s\in B_c\) satisfies \(\{r,s\}\in F\).
* A vertical white pair in rows \(r,s\) has an axis rival exactly when \(\{r,s\}\in F\).
* A horizontal white pair in columns \(c,d\) has an axis rival exactly when \(B_c\cap B_d\ne\varnothing\).
* An oblique white pair \((c,r),(d,s)\) has an axis rival exactly when \(s\in B_c\) and \(r\in B_d\).

Using all of \(F\) before every column has been ordered is sound: every unassigned column in the multiset must occur later. The white corner conditions ensure that a column witnessing the rival is distinct from the presentation's column when required.

An empty presentation is allowed once. The program does not reject a hidden rectangle merely because it is hidden.

The first complete run used horizontal reflection to put one selected triple, when present, in the first five positions. This is valid with either one or two triples: select a particular triple from the sorted input multiset and reflect the whole board if needed. The initial output's field describing it as a "unique triple" is an imprecise label inherited from the earlier 19-point search. The implemented reduction only selects one triple and does not assume there is only one. A second run disables this reduction.

The first run completed all 124,087 representatives, visited 114,087,364 search nodes, and found no valid order. Its wall time was 92.459 seconds. The output `seven_nine_eighteen_0.json` records every representative's completed status. The second run also completed every representative without horizontal reflection, visited 134,608,986 nodes, and found no valid order in 137.721 seconds. Its output is `seven_nine_eighteen_0_no_horizontal.json`.

The upper bound follows because any valid board with more than 18 black points could have points restored to white to produce a valid 18-point board.

## Reproduction and audit status

Run these scripts from this directory, using Python 3 and Node:

```text
python build_seven_nine_search.py
python build_seven_nine_eighteen.py
node seven_nine_permutation_search.js 120 0 seven_nine_eighteen_data.json
node seven_nine_permutation_search.js 420 0 seven_nine_eighteen_data.json --no-horizontal
python seven_nine_seventeen_witness.py
```

An additional independent checker, `seven_nine_direct_presentations.js`, compares the white presentations of all 1,113 rectangles directly. It uses neither the axis-rival lemma nor horizontal reflection. Its rectangles are generated independently by `build_seven_nine_all_rectangles.py`. This checker completed representatives 0 through 36,052, then reached its 480-second cap during representative 36,053. It visited 133,914,624 nodes and found no witness. This is an incomplete cross-check and is not used as an exhaustive certificate.

The earlier 19-point upper bound has also passed a separately written Python search over its smaller complete family. The 18-point result is the stronger statement and makes that earlier upper bound redundant.
