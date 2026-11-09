# The exact value on seven by eleven

The computer-assisted result is

\[
f(7,11)=20.
\]

Together with the two preceding widths, the established values are

\[
f(7,9)=17,\qquad f(7,10)=18,\qquad f(7,11)=20.
\]

## An explicit 20-point construction

The column word is

\[
567,\quad345,\quad23,\quad1,\quad1,\quad1,\quad14,\quad12,\quad2,\quad26,\quad17.
\]

It has two triple columns, five double columns, and four singleton columns. All 1,680 rectangles have distinct white presentations. The bitset and constructive rectangle generators check this independently.

The two triple columns are material to the comparison with earlier restricted searches. The older report only found \(c=3\) from doubles in \(K_{3,4}\) starting at width 12. The present construction obtains \(c(7,11)=3\) at width 11 using triples. It agrees with the numerical strip formula at this width.

The construction was found by adding one admissible double row pair to a stored seven-by-eight nonsingleton family, allowing all singleton-row choices, and reordering the resulting columns. This was a focused lower-bound search, not a complete search at size 20. A complete search at size 20 is unnecessary after finding the witness and proving the upper bound.

## Complete classification at 21 black points

Suppose a valid seven-by-eleven board has 21 black points and \(z\) empty columns. Its axis row-tree graph has

\[
e(H)=21-(11-z)=10+z.
\]

The large-column bound excludes every column of size at least four. If a triple occurs, the same bound gives \(e(H)\le10\). The equality classification then forces exactly one triple, eight double columns, and the remaining singleton or empty columns.

There can be no empty column. If \(z\ge1\), the edge count is at least 11, so there are no triples. With all columns of size at most two, there would be at most \(2(11-z)\le20\) black points, a contradiction.

Thus \(z=0\), and there are precisely two possibilities:

1. Ten double columns and one singleton. The ten double row pairs form a triangle-free graph on seven labeled rows.
2. One triple, the eight doubles in its rigid boundary core, and two singleton columns.

There are 2,961 labeled triangle-free ten-edge graphs on seven rows, as verified by exhaustive enumeration of the \(\binom{21}{10}\) possible edge sets. The unique-triple core count is 1,890, proved analytically in `large_column_boundary_classification.md`. The full axis-family counts are therefore

\[
2,961\cdot7=20,727
\]

and

\[
1,890\binom82=52,920,
\]

for a total of 73,647 labeled column multisets. Vertical reflection gives 36,888 representatives. No arbitrary permutation of row labels is used.

`build_seven_eleven_upper.py` generates exactly this family by adding a singleton to every member of the corrected, complete seven-by-ten 20-point family. Every case just listed has a singleton that can be removed, so this generation is complete.

## Exhaustive upper bound and independent witness check

`finite_column_order_search.js` checked every column ordering of these representatives, subject only to exact presentation pruning and geometric reflection. It found no valid 21-point board. The run visited 114,130,128 search nodes in 173.341 seconds and completed all 36,888 representatives.

The result file is `seven_eleven_21_0.json`. The full candidate list is `seven_eleven_21_data.json`. The independent summary in `seven_eleven_exact_check.json` verifies both exhaustive coverage and the 20-point witness against all 1,680 rectangles. The code is `verify_seven_eleven.py`.

Since restoring black points to white preserves validity, the absence of a 21-point board also excludes all larger blackouts. This completes the proof of the exact value.

## Reproduction

```text
python build_seven_ten_search.py 20
python build_seven_eleven_upper.py
node finite_column_order_search.js seven_eleven_21_data.json 180 0
python build_seven_eleven_lower_probe.py
node finite_column_order_search.js seven_eleven_20_probe_data.json 120 0
python verify_seven_eleven.py
```

All upper-bound runs must finish with `UNSAT`. A time-capped run marked `incomplete` does not prove the upper bound.
