# The exact value on seven by twelve

The computer-assisted result is

\[
f(7,12)=21.
\]

An explicit 21-point column word is

\[
7,\quad567,\quad345,\quad23,\quad1,\quad1,\quad1,\quad14,\quad12,\quad2,\quad26,\quad17.
\]

Two independent rectangle generators verify that all 1,996 rectangles have different white presentations.

## Complete classification at 22 points

Let \(z\) be the number of empty columns. A hypothetical 22-point board has an axis row-tree graph with

\[
e(H)=22-(12-z)=10+z.
\]

The large-column bound excludes columns of size at least four. If a triple exists, then \(e(H)\le10\), with equality exactly in the unique-triple boundary family. There cannot be two empty columns: then no triple could occur, and ten nonempty columns of size at most two could not contain 22 points.

If \(z=0\), there are two cases:

* Ten double columns and two singleton columns. The doubles form one of the 2,961 triangle-free ten-edge graphs on seven labeled rows.
* One triple, its eight-double boundary core, and three singleton columns. There are 1,890 labeled cores.

If \(z=1\), all eleven nonempty columns must be doubles. Their row graph has eleven edges. A triangle-free nonbipartite graph on seven vertices has at most ten edges, so this graph is bipartite. Its only possible part sizes are three and four, and it is \(K_{3,4}\) with one edge deleted. There are \(\binom73\cdot12=420\) such graphs. Each is connected, so its bipartition is unique up to swapping the parts.

The complete multiset counts are:

| Column structure | Multisets |
|---|---:|
| Ten doubles, two singletons | \(2,961\binom82=82,908\) |
| One triple, eight doubles, three singletons | \(1,890\binom93=158,760\) |
| Eleven doubles, one empty column | 420 |
| Total | 242,088 |

Vertical reflection reduces these to 121,158 representatives. `build_seven_twelve_upper.py` generates the entire list. In particular, it includes the empty-column case, which cannot be omitted at this width.

## Exact cropping constraints and exhaustive coverage

The ordering search uses the exact presentation tests described in `seven_nine_exact.md`. It also uses the previously proved bounds

\[
f(7,9)=17,\qquad f(7,10)=18,\qquad f(7,11)=20.
\]

Every consecutive subboard of a valid board must satisfy these bounds. An assigned prefix may therefore be rejected if it already contains an overfull cropped subboard, or if its unassigned suffix would necessarily contain too many black points. This is the exact restriction argument in `boundary_cropping_recurrence.md`.

The complete cropped search used two bounded runs:

| Run | Fully completed representatives | Nodes, including partial work | Seconds |
|---|---|---:|---:|
| First | 0 through 42,957 | 154,206,208 | 300.006 |
| Continuation | 42,958 through 121,157 | 197,785,600 | 223.537 |

The first run stopped during representative 42,958. The continuation restarted that representative from its root. Every candidate was fully checked, and none has a valid order. The combined work was 351,991,808 nodes and 523.543 seconds.

An additional uncropped search completed representatives 0 through 58,650 before its 600-second cap. It found no valid order, but that partial run is not used as the exhaustive certificate. A separate general SAT pilot was also unresolved after 180 seconds and supplies no upper bound.

`verify_seven_twelve.py` verifies the union of completed ranges, checks that the cropped and uncropped candidate lists agree, verifies the exact crop bounds used, and independently checks the 21-point witness. Its output is `seven_twelve_exact_check.json`.

Because restoring black points to white preserves validity, excluding 22 points excludes every larger blackout. The explicit lower bound completes the proof.

## Consequence for the seven-row equality width

An equality board has \(m+12\) black points and at most two in each column. Restricting it to twelve columns gives

\[
m+12-2(m-12)\le f(7,12)=21,
\]

so every equality width has \(m\ge15\). The restriction to twelve columns is legitimate because equality already requires \(m\ge12\).

This does not settle the proposed equality threshold near 20. The established finite-width values are now

\[
f(7,9)=17,\quad f(7,10)=18,\quad f(7,11)=20,\quad f(7,12)=21.
\]
