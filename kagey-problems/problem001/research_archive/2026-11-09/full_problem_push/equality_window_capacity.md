# Equality-window capacity and threshold lower bounds

9 November 2026. **Every seven-row equality board has width at least 17.**
The new step is a complete computer-assisted proof that every fourteen-column
window of such a board has at most nine double columns.

Write `q = floor(h^2/4)`. An equality board has exactly `q`
double columns, all other columns are singletons, and its double pairs are the
edges of one balanced complete bipartite row graph `F`. This note gives a window
packing bound, records a stronger seven-row restricted bound, and distinguishes
what these arguments do and do not establish for growing height.

## 1. The correct restricted window invariant

Fix a balanced row partition and its complete bipartite graph `F`. An
`F`-admissible window has the following properties:

- every column is a singleton or double;
- its double pairs are distinct edges of `F`;
- no rectangle wholly contained in the window is hidden;
- local tilted-rectangle comparisons pass the exact positive-support tests,
  including virtual axis rivals supplied by **all of the final graph `F`**.

The last condition uses the fixed-`F` local tests from the exact counting and
compact-support notes. In particular, it is potentially stronger than validity
of the isolated window: an edge of `F` may be supplied outside that window in the
eventual board. Required black corners in the support must still be available
inside the window. The support-feasibility test must therefore use its actual
double owners, while the axis-rival test uses all of `F`.

Every contiguous window of a full equality board is admissible in this sense.
For an actual white singleton or vertical white pair, a required `F` edge is
present somewhere in the full board. Its owner cannot be a column in which one
of those displayed white cells would be black, so it supplies the genuine axis
rival used by the test. Horizontal and oblique axis rivals use their prescribed
black cells directly. If prospective white cells are black, the positive-support
argument gives the same collision or a hidden rectangle. Thus fixed final `F`
does not create a false rejection of an equality-board window.

Let `d_F(h,k)` be the maximum number of double columns in an admissible width-`k`
window, and let `d(h,k)` be the maximum over balanced partitions. Any upper bound
on the ordinary extremal value also gives

\[
d(h,k)\le \min\{k,f(h,k)-k\}.
\tag{1}
\]

However, a smaller bound can follow from the restricted column family or the
virtual final graph, even when unrestricted extremal examples contain triples.
Admissibility is only a necessary condition for occurring in a full equality
board; a SAT window by itself does not establish such an extension.

## 2. Global capacity from a single window length

**Window-capacity theorem.** Suppose every width-`k` equality window has at most
`d` double columns, where `1 <= d < k`. Every equality width `m >= k` satisfies

\[
q\le d\left\lfloor\frac m k\right\rfloor+
       \min\{d,m\bmod k\}.
\tag{2}
\]

Consequently

\[
m\ge
k\left\lfloor\frac{q-1}{d}\right\rfloor
 +1+((q-1)\bmod d).
\tag{3}
\]

**Proof.** Encode double columns by ones and singleton columns by zeros. Partition
the first `k floor(m/k)` columns into length-`k` intervals. Each contains at most
`d` ones. The final remainder has at most its length in ones and at most `d`,
because it is contained in the final length-`k` interval. This proves (2).
Inverting its integer-valued right side gives (3). The binary word formed by
repeating `d` ones followed by `k-d` zeros attains the capacity in (2) for every
prefix length. Thus the estimate is sharp if only this one binary window
constraint is retained. It need not be attainable by a geometric board.

When `d < q <= 2d`, formula (3) becomes

\[
m\ge q+k-d.
\tag{4}
\]

Using (1) recovers `m >= q+2k-f(h,k)`. Formula (3) is stronger when enough
double columns require several windows.

The range condition matters. A bound at length `k` can be applied immediately if
`k <= q`, because equality already implies `m >= q`. For a larger `k`, first
establish `m >= k`, possibly by a shorter-window bound. This permits a rigorous
bootstrap through a finite list of known window capacities.

## 3. A new restricted seven-by-thirteen bound

Every valid 7 by 13 board with at most two black points per column has at most
22 black points. This statement allows empty columns and does not assume a fixed
balanced partition, so it also bounds all equality windows.

For a 23-point candidate let `z` be its number of empty columns. Its double graph
has `10+z` edges. The complete excess-ten catalog has 2,664 reflection classes;
exactly 1,707 contain no triple. All of these 1,707 classes now have completed
UNSAT checks. The old runs cover indices 0 through 995 and 1000 through 2663.
Among the four omitted indices, 996, 998, and 999 contain triples. The remaining
index 997 has only doubles and was checked separately:

`fixed_core_h7_w13_997_cadical195_crop.json` records one completed UNSAT instance,
with a total elapsed time of approximately 0.812 seconds.

The fixed-core formulation lets every double occur once, every prescribed empty
column occur once, and every remaining column choose any singleton row. Its
point variables are equivalent to these column masks. The feasible-support
callback discards only impossible black requirements, and its cropped-cardinality
constraints use established smaller-width upper bounds. Therefore the completed
no-triple coverage proves the stated upper bound, without needing the unresolved
triple cases. Ruling out 23 points rules out every larger count as well: removing
black points preserves validity, because a collision after removal would require
the same rectangle symmetric difference to have been black before removal.
The property of having at most two black points per column is also preserved.

`verify_equality_window_capacity.py` checks all 1,707 required indices against
the completed result files and records their hashes. It independently enumerates
all ten-edge row graphs to verify the later width-14 catalog. Its width-14 output
remains explicitly pending unless every required core has a completed UNSAT
record.

In the window notation this gives

\[
d(7,13)\le9.
\tag{5}
\]

The ordinary no-triple upper bound 22 is sharp. Removing row 7 from the triple
in the known 23-point witness gives

```
56,45,34,23,2,12,1,2,3,14,25,36,17
```

with 22 black points and only singleton/double columns. It remains valid by
black-deletion monotonicity. Nevertheless, it is not admissible for its unique
balanced completion, whose classes are `{1,3,5}` and `{2,4,6,7}`. The black
diagonal `(1,5),(5,2)` has the white vertical diagonal `(3,1),(3,6)`: both have
the same midpoint and length five. The final pair `{1,6}`, absent from the
window's own double graph, would supply its axis rival elsewhere in an equality
board. This gives an explicit distinction between intrinsic window validity and
final-`F` admissibility. It does not show that the bound in (5) is sharp for the
latter.

For comparison, the unrestricted value `f(7,13)=23` gives only the bound 10.
The width-12 value `f(7,12)=21` first gives every equality width `m >= 15`, so
the width-13 constraint is applicable. Formula (4) then gives `m >= 16`.

## 4. Audit of the seven-by-fourteen exact value

The independent audit of `f(7,14)=24` found no gap. For 25 points, the excess is
`11+z`. A triple column would force excess at most ten, so every candidate has
only singletons, doubles, and at most one empty column. Its triangle-free row
graph is either `K_(3,4)` minus one edge, with no empties, or `K_(3,4)`, with one
empty column.

There are 420 and 35 labeled graphs. No eleven-edge graph is fixed by vertical
reflection: its unique balanced partition would have to be reflection-invariant,
and its unique deleted cross-edge would also have to be invariant, which is
impossible. Among the 35 complete graphs, exactly three partitions are invariant.
The orbit counts are consequently 210 and 19, totaling 229.

A separate execution enumerated every triangle-free eleven- and twelve-edge
graph, matched these 229 cores, checked the complete consecutive UNSAT index
range 0 through 228, and checked the 24-point witness against both rectangle
generators. It has 2,691 distinct presentations. These checks do not replace a
formal UNSAT proof log; the remaining computational input is the exact SAT
solver's completed output for each instance.

The ordinary width-14 bound gives `d(7,14) <= 10`, and hence again `m >= 16`.
The stronger final-`F` window bound `d(7,14) <= 9` is now proved and gives
`m >= 17`. It suffices to exclude nonempty 24-point candidates: ten doubles and
four singletons. A fourteen-column window cannot have eleven or more doubles,
because deleting one boundary column would leave at least ten doubles in
thirteen columns, contrary to Section 3.
Their row graph is `K_(3,4)` minus two edges. There are
`35 binom(12,2)=2310` labeled cores. Exactly 18 are reflection-invariant: one of
three invariant balanced partitions, with one of six reflected edge pairs
deleted. Thus there are `(2310+18)/2 = 1164` reflection classes.

The new width-13 bound forces both boundary columns of such a width-14 candidate
to be doubles. Removing a singleton boundary would otherwise leave a forbidden
23-point, no-triple width-13 board.

All 1,164 final-`F` instances have now returned UNSAT. The completed ranges are:

| Result file | Completed indices | Recorded elapsed time |
|---|---:|---:|
| `equality_window14_0_cadical195.json` | 0--825 | 1200-second capped run |
| `equality_window14_826_cadical195.json` | 826--999 | 213.062 seconds |
| `equality_window14_1000_cadical195.json` | 1000--1163 | 180.843 seconds |

The first file has an overall incomplete status because its cap interrupted the
next instance; only its 826 completed UNSAT records are used. The remaining two
files complete the catalog without gaps. `verify_equality_window_capacity.py`
checks the target dimensions, contiguous range records, every individual UNSAT
status, and the independently enumerated row catalog. The final saved result is
`equality_window_capacity_check.json`, which records all source-file hashes and
confirms all 1,164 cases.

Applying (4) with `q=12`, `k=14`, and `d=9` proves `m >= 17`. The earlier bound
`m >= 16` already ensures the needed range condition `m >= 14`. This is a
computer-assisted lower bound for equality width; it is not a claim that every
intrinsically valid fourteen-column, no-triple board has at most 23 points.

The binary words

```
DDDSDDSDDSDDSDDD
DDDSDSDDSDDSDSDDD
```

each contain twelve double markers. The first has length 16 and satisfies the
capacities available before the completed width-14 search, including the
width-13 capacity nine. The second has length 17 and satisfies the now-proved
width-14 capacity nine. Checking every contiguous interval gives maximum
double counts respectively `(7,7,8,9,9,10)` and `(6,7,8,8,9,9)` for lengths
9 through 14. Thus recombining only these binary interval constraints cannot
improve the corresponding bounds 16 and 17. Neither binary word is asserted to
admit valid row labels.

## 5. What is still needed for a growing-height lower bound

Near-Mantel row structure and column counting alone cannot improve `m >= q`.
For every balanced partition, putting its `q` distinct cross-edges into `q`
double columns is axis-valid, in any order. A stronger general threshold bound
must therefore use tilted geometry, not just the row graph or its edge count.

The window theorem isolates one sufficient route. A uniform estimate

\[
d(h,k_h)\le k_h-c h,\qquad k_h\le q_h,
\]

would already give `m >= q_h+c h` whenever `q_h > d(h,k_h)`. The current general
square upper bounds do not supply this estimate: at width comparable to `h`,
they are larger than the two-points-per-column regime. Neither this note nor the
finite seven-row checks establish a growing surplus for arbitrary height.

Deleting interior columns and compressing the remaining coordinates is not a
valid shortcut. Such compression can create new tilted rectangles. All window
arguments above retain contiguous coordinates and use only genuine cropping.
