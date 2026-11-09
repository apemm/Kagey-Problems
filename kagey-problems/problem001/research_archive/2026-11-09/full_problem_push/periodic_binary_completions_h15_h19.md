# Repeated binary gaps at heights 15 and 19

9 November 2026. A fixed seven-cell gap already suffices for compact equality
boards at heights 15 and 19. At height 19, a checked tail transition proves
\[
f(19,m)=m+90\qquad(m\ge713).
\]
These are finite computer-assisted constructions. The fixed-gap design is not
universal: period_eight_binary_sea_impossibility.md rules out every such gap
at heights \(39,115,191,\ldots\).

## Height 15: all three surviving gaps work

Put doubles at columns \(8j+1\), \(0\le j<56\). The three gap patterns left
by the analytical classification all admit a pair order:

| Mask | Repeated singleton rows | Search seconds | Independent check |
|---|---|---:|---:|
| 8 | \(1,1,1,15,1,1,1\) | 14.984 | 917,627 weak rectangles |
| 10 | \(1,15,1,15,1,1,1\) | 18.609 | 761,877 weak rectangles |
| 42 | \(1,15,1,15,1,15,1\) | 7.375 | 13,265 weak tilted rectangles |

Every board has width 441 and 497 black points. The orders and full column
lists are in the three files
constant_sea_h15_cadical195_seed101_high385_s8_mask8.json,
constant_sea_h15_cadical195_seed102_high385_s8_mask10.json, and
constant_sea_h15_cadical195_seed103_high385_s8_mask42.json.
Their independent check files have the suffix _pair_check.json for the first
two and _tilted_pair_check.json for the third.

The smaller tilted count in the last row reflects a different verifier, not
a different definition of identification. Its treatment of axis rectangles
is explained below.

## Height 19: an explicit repeated-gap board

Use the gap
\[
1,1,1,19,1,1,1
\]
between every pair of consecutive doubles. The double columns are \(8j+1\),
\(0\le j<90\), in this order:

    (9,18),(2,13),(9,10),(5,8),(16,19),(15,16),(1,8),(11,12),(1,4),(4,13),
    (15,18),(4,5),(13,18),(4,15),(3,8),(6,7),(2,9),(6,11),(7,18),(7,10),
    (3,12),(2,5),(1,12),(10,11),(1,14),(13,16),(5,14),(3,10),(10,19),(2,17),
    (9,14),(4,7),(11,14),(3,6),(10,13),(5,6),(8,9),(4,19),(3,14),(1,6),
    (16,17),(7,16),(2,3),(1,2),(11,18),(8,11),(1,16),(12,13),(14,15),(17,18),
    (13,14),(3,16),(5,16),(7,14),(2,7),(5,18),(1,18),(11,16),(3,4),(2,15),
    (3,18),(1,10),(2,11),(14,19),(5,10),(18,19),(6,15),(2,19),(10,15),(12,19),
    (4,11),(6,9),(6,19),(10,17),(14,17),(4,17),(4,9),(6,13),(6,17),(7,8),
    (9,12),(8,17),(5,12),(8,13),(9,16),(8,19),(12,17),(8,15),(7,12),(12,15)

These are exactly the 90 opposite-parity pairs. The width is 713 and the
black count is 803. The source is
constant_sea_h19_cadical195_seed101_high623_s8_mask8.json; all one-based
coordinates are in height19_width713_binary_coordinates.json.

The search took 325 models and 11,901 learned geometric clauses. Its solving
time was 109.781 seconds, with 114.156 seconds total. The independent checker
found 29,033 weak tilted rectangles, all with distinct presentations and no
axis rival. The mask-10 and mask-42 runs at height 19 ended unknown at their
120-second caps.

## A sixteen-column transition proves an eventual equality theorem

Append these singleton rows to the width-713 board:

    1,1,1,1,9,19,19,19,19,5,19,19,1,1,1,1

Then append 164 copies of row 2. The resulting width-893 board has 983 black
points. The independent checker found 30,797 weak tilted rectangles with
distinct presentations and no axis rival. The full board is saved in
constant_sea_h19_cadical195_seed101_high623_s8_mask8_tail.json.

A tilted rectangle in 19 rows has span at most
\[
ac+1=bd+1\le(18/2)^2+1=82.
\]
Two tilted rectangles with a shared corner have union span at most 164.
The nonconstant prefix ends at column 729, and the checked constant tail
occupies columns 730 through 893. Any new local failure beyond column 893
would need span at least 165 to touch that prefix. Thus every genuinely new
local support lies in the constant row-2 sea, which is valid for the parity
graph.

The full parity graph is already owned in the first 713 columns. Singleton
and vertical tilted-axis comparisons are therefore covered by the same fixed
graph at every later width. Horizontal and oblique axis comparisons remain
local. Axis-axis uniqueness is unchanged because only singleton columns are
added.

The checked width-893 board can consequently be extended by any further
row-2 tail. Its prefixes give every width from 713 through 893, retaining
all 90 doubles. This proves the displayed eventual equality formula.
The transition and tail use rows beyond the two boundary sea rows, so the
eventual theorem is about unrestricted equality boards, not the binary
family at every width.

## The memory-efficient independent verifier

The script verify_parity_board_pair_geometry.py completes every black pair
both as a diagonal and as a side, using equal-midpoint/equal-length arithmetic
and all integral perpendicular translations. It keeps only tilted rectangles.
It does not use the SAT shape compiler.

Axis-axis uniqueness follows from the checked complete list of distinct
parity pairs and singleton remaining columns. For a tilted presentation,
the verifier checks the exact axis-rival conditions:

* a singleton has an opposite-parity mate in its column;
* a vertical pair has opposite-parity rows;
* a horizontal pair has a common black row in its two columns;
* an oblique pair has both crossed cells black.

It also checks that no tilted rectangle is hidden and no two tilted
presentations agree. Every omitted rectangle has at least three white corners
or is an axis rectangle handled as stated. This is a complete verification.
The generated tilted sets match the original all-rectangle black-pair
generator on two independent calibration boards.
