# Structure of the equality boards at heights 7, 11, 15 and 19

9 November 2026. This note reads the tables in `structure_tables.md`. The numbers come from
`structure.py` (per board) and `cross_board.py` (between boards); `make_tables.py` writes the tables.

## Boards and verification

| Height | Boards | Source |
|---|---|---|
| 7 | the four 7 x 21 boards, one orbit under the two reflections | `seven_equality_count21_independent_check.json` |
| 11 | 11 x 169, core in columns 27 to 143 | `2026-11-07/data/cegar_h11_warm_t3.json` |
| 15 | 15 x 441 with an odd-row sea; 15 x 441 with fillers in rows 1 and 15 only | `height15_width441_coordinates.json`, `height15_width441_binary_coordinates.json` |
| 19 | 19 x 713, gap word 1,1,1,19,1,1,1 | `height19_width713_binary_coordinates.json` |

Controls: the 9 x 77 board, three more 11 x 169 boards, and the three repeated-gap 15 x 441 boards
(gap words 1,1,1,15,1,1,1 and 1,15,1,15,1,1,1 and 1,15,1,15,1,15,1).

Every board was checked again with `rectlib.check_board` before any statistic was computed. The check
builds each rectangle as two equal-length segments with a common midpoint, counts all of them (5,785 at
7 x 21, 872,549 at 11 x 169, 11,027,771 at 15 x 441, 46,778,973 at 19 x 713), and compares the
presentations of all rectangles with two or more black corners. The totals agree with a separate count
from perpendicular side vectors. All fifteen boards are valid equality boards (`verify_all.json`).

## What the four heights share

1. **Partition.** Every board uses the parity partition. The doubles are all odd-even row pairs, once
   each.

2. **Fillers stay off the even rows and prefer the boundary.** Share of core fillers in rows 1 and h:
   56% at height 7, 82% at height 11, 57% in the odd-sea board at height 15, 100% in the binary boards at
   15 and 19. Even rows hold 3 of 9 fillers at height 7, 13% at height 11 (all inside the six free
   transition gaps at the two ends of the core), and none at 15 and 19.

3. **Triangles always complete into a filler column of the same class.** In every board, every tilted
   rectangle with three black corners has its white corner in a singleton column, in a row of the same
   parity as that column's filler. This is forced: a white corner in a double column, or opposite in
   parity to the filler, has a single axis rival through the double that owns the two rows. The counts
   are small: 7 triangles at 7 x 21, 86 at 11 x 169, 137 to 199 in the binary boards at height 15, 388 at
   19 x 713 (0.2 to 0.55 per column). A label sits in 1.3 triangles on average at height 7, 4 to 5 at
   heights 11 and 15, 6.7 at height 19 (maximum 18). Triangles with three label cells occur only at
   height 7 (two per board). In the binary boards no triangle is made of fillers only.

4. **No vertical rival, and the boundary is the only thing that blocks the pairs that are present.**
   A black pair in opposite classes at an offset (dx, dy) with dx^2 + dy^2 = L^2 is fatal when the
   vertical segment of length L through its midpoint fits in the grid. L is odd, so dx is a multiple of
   4. All such pairs present in the boards (2 at height 7, 4 at height 11, 24 to 31 at height 15, 65 at
   height 19) have a vertical diagonal that leaves the grid. A filler in row 1 or h can never be in a
   fatal pair: the vertical diagonal is longer than |dy| and has the same midpoint, so it passes the
   boundary row. Boundary fillers are therefore immune to this law, and only label-label pairs and
   interior fillers have to be arranged.

5. **No tilted shape is switched off.** Every shape class that fits (22, 93, 235, 452 classes at heights
   7, 11, 15, 19) has a placement with two black corners, and a fifth to a half of the classes have a
   placement with three. What the layout lowers is the density: the share of tilted placements with two
   or more black corners is 0.040 at height 11 against 0.059 for the same columns with random filler
   rows, 0.014 to 0.018 against 0.030 in the binary boards at height 15, and 0.0086 against 0.019 at
   height 19. At 7 x 21 there is no reduction (0.209 against about 0.20). The mechanism in the binary
   boards is exact: a tilted rectangle has at most one corner in row 1 and one in row h, and two such
   corners are opposite corners of a rectangle of full height h - 1. So two fillers are never adjacent
   corners, and they are opposite corners only in full-height shapes (5,878 and 5,279 such rectangles at
   heights 15 and 19, none of any other kind). The remaining weak rectangles all contain a label cell.

## What differs

| | 7 x 21 | 11 x 169 | 15 x 441 | 19 x 713 |
|---|---|---|---|---|
| Label columns | gaps 1, 2, 3 (five adjacent pairs of label columns) | 27 + 4j | 1 + 8j | 1 + 8j |
| Fillers between labels | 0 to 2 cells, rows 1 or 7 and 2, 3, 5, 6 | 1,11,11 or 1,1,11 in 23 of 29 gaps; six free gaps at the ends | odd-sea board: 53 different gap words; binary board: 39 words over rows 1, 15 | 1,1,1,19,1,1,1 in all 89 gaps |
| Period of the core word | none (best match 0.53) | 4 (match 0.82) | 8 (match 0.42 and 0.70) | 8 (exact) |
| Width / h^2 | 0.43 | 0.97 (core 117) | 1.96 | 1.98 |
| Consecutive labels sharing a row (random order) | 0.73 (0.45) | 0.38 (0.30) | 0.26 to 0.38 (0.23) | 0.18 (0.19) |

The 7 x 21 boards are the only ones that are tight, and they look different in kind: labels touch each
other, a staircase 23, 34, 45, 56 (or its mirror image) fills four adjacent columns at one end, and
consecutive labels share a row far more often than in a random order. The boards at 11, 15 and 19 are
dilute: every label is isolated by three or seven fillers, and consecutive labels are unrelated.

**How much the order has to do.** Keep the columns and fillers of a board and shuffle its labels. The
number of fatal triangles (white corner facing a black cell of the other class in its column) is then
about 2 per label at spacing 4 (59 on average at height 11, 23 at height 7) and 0.36 to 0.56 per label
at spacing 8 with a repeated gap (20 at height 15, 51 at height 19). The two height-15 boards without a
repeated gap are worse (1.5 per label for the non-periodic binary sea, 4.0 for the odd-row sea). Vertical rivals: 12 on average at
height 11, never fewer than 5 in 30 shuffles; exactly 0 in every shuffle of the binary boards at height
15; 3.9 on average at height 19. The reason is arithmetic. Labels at spacing 4 see the triple (4,3,5) at
slot distance 1 (and (12,5,13), (12,9,15) at slot distance 3 once h >= 14 and h >= 16). Labels at spacing 8 see only dx = 8, 16, 24, ...,
and the first triple with an odd hypotenuse and such a leg is (8,15,17), which needs h >= 18. The middle
filler of each gap, at offset 4, is the only cell at a dangerous distance from a label, and in the
binary boards it lies in row 1 or h, where it is immune (item 4). Spacing 8 buys a four to five times
lower violation density for twice the width.

## Is there one rule?

**Columns and fillers: yes, for the dilute boards.** The rule "doubles at columns 1 + 8j, fillers
1,1,1,h,1,1,1 in every gap" reproduces all label columns and all fillers of the 19 x 713 board and of
the 15 x 441 board with that gap word. The rule "doubles at every fourth column, fillers 1,x,h with x in
{1, h}" reproduces 23 of the 29 gaps at height 11 (and 14 of 19 gaps at height 9 follow the fixed word
1,9,1); the other gaps are the free transition gaps next to the pads. Neither rule describes the 7 x 21
boards. `period_eight_binary_sea_impossibility.md` already shows that the spacing-8 rule cannot hold at
every height.

**Label order: I found none.** The tests, all in `structure_tables.md`:

- Linear fit of the slot (or column) by the two rows: R^2 between 0.03 and 0.15, inside the range of
  shuffled orders for the boards at 7 and 11 and near the top of that range, without structure, at 15
  and 19 (0.07 against a shuffled maximum of 0.16 at height 19).
- Modular rules slot = alpha i + beta j + gamma (mod N), N <= 12, all alpha, beta, gamma, with i, j the
  ranks of the two rows in their classes: no exact rule for any N, and the best match is at the level of
  shuffled orders (isolated excesses at one modulus in three of fifteen boards, none repeated).
- Slot mod 2 or mod 4 as a function of the rows mod 4 or mod 8: at chance level.
- Between heights: the rank correlation of the slots of shared pairs between the 15-row and 19-row
  repeated-gap boards is 0.02, 0.19, 0.08 for row shifts 0, 2, 4 (95% point of the null: 0.25). The same
  holds between different boards of one height (three boards at height 15, three at height 11).
- Restriction: the 19-row order, restricted to a 15-row window and placed with the 15-row gap word, is
  not valid (47, 62, 76 clashing presentations for the three windows, 16 to 35 fatal triangles, which is
  the level of a random order).

So the label columns and fillers of more than one board follow one rule, and the label orders do not
follow any rule I could detect. The orders behave like independent solutions of a constraint problem
whose constraint density is set by the spacing and the gap word.
