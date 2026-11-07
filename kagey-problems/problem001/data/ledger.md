# Ledger: hand-verified ground truth (solver test fixtures)

| grid (n x m) | max blackout | # maximum blackouts | status |
|---|---|---|---|
| 2 x 2 | 4 | 1 | hand-proved (vacuous: one rectangle) |
| 2 x 3 | 4 | 12 | hand-proved; witnesses characterized |
| 2 x 4 | 5 | 32 | hand-proved (Strip Theorem instance); 15-row table verified twice |
| 2 x 5 | 6 | 80 | VERIFIED 2026-08-25: engine + brute agree; pre-registered prediction confirmed |
| 3 x 3 | 5 | 53 | VERIFIED 2026-08-25: engine + brute agree (10 rectangles, 1 tilted) |
| 3 x 4 | 6 | 224 | VERIFIED 2026-08-25: engine + brute agree (20 rectangles) |
| 3 x 5 | 7 | 892 | VERIFIED 2026-08-25: engine + brute agree (33 rectangles) |
| 4 x 4 | 7 | 316 | VERIFIED 2026-08-25: engine + brute agree (44 rectangles) |
| 4 x 5 | 8 | 1810 | VERIFIED 2026-08-25: engine + brute agree (74 rectangles) |
| 5 x 5 | 10 | 8 | VERIFIED 2026-08-25: engine + brute agree (130 rectangles). REFUTES pre-registered prediction 9 (kept 15, not 16). Only 8 maximum blackouts. |
| 3 x 6 | 8 | 3420 | VERIFIED 2026-08-25: engine + brute agree (49 rectangles); pre-registered prediction 8 confirmed |
| 4 x 6 | 10 | 26 | VERIFIED 2026-08-25: engine + brute agree (110 rectangles = A289832); kept 14 |
| 5 x 6 | 11 | - | engine 2026-08-25 (value-only, 198 rectangles); kept 19 = (n-1)(m-1) - 1; brute infeasible (2^30) |
| 3 x 7 | 9 | 12704 | VERIFIED 2026-08-25: engine + brute agree (68 rectangles = A289832); H_sum REFUTED |
| 3 x 8 | 10 | 45864 | VERIFIED 2026-08-25: engine + brute agree (90 rectangles = A289832); H_area REFUTED |
| 4 x 7 | 11 | 292 | VERIFIED 2026-08-25: engine + brute agree (152 rectangles = A289832); kept 17; excess-1 confirmed |
| 3 x 9 | 11 | 161992 | VERIFIED 2026-08-25: engine + brute agree (115 rectangles = A289832); Three-Row confirmed |
| 4 x 8 | 12 | - | engine 2026-08-25 value-only (200 rectangles = A289832); kept 20; Four-Row REFUTED (said 13), excess-1 confirmed; brute infeasible (2^32) |
| 5 x 7 | 12 | - | engine 2026-08-25 value-only, 723s (276 rectangles = A289832); kept 23; excess-1 confirmed; brute infeasible (2^35) |
| 3 x 10 | 12 | - | engine 2026-08-25 value-only (143 rectangles = A289832); kept 18; Three-Row confirmed (8 cells); brute infeasible (2^30) |
| 6 x 6 | 12 | - | engine 2026-08-25 value-only, 1063s (313 rectangles = A085582); kept 24; excess-1 confirmed (7 cells); brute infeasible (2^36) |

Strip Theorem (2026-08-24): for 2 x m, m >= 3, every maximum valid blackout has size m+1;
there are exactly m * 2^(m-1); characterized as complements of kept sets with one survivor
per column, missing exactly one column. Proof: two pigeonholes + exactness line (see paper).

TODO: transcribe the verified 2x4 fifteen-row difference-set table here verbatim (fixture for
the table/pruning module).

Kept-Set Conjecture (2026-08-25) -- REFUTED same night, see below: for an n x m grid with at least two rectangles, the minimum
kept set (complement of a maximum blackout) has size (n-1)(m-1); equivalently max blackout =
n + m - 1. Fits every verified entry above without exception: kept = 2,3,4 (2 x 3..5),
4,6,8 (3 x 3..5), 9,12 (4 x 4..5). The Strip Theorem is the proven n = 2 case. 2 x 2 (one
rectangle, vacuous) is outside the hypothesis. No witness-count formula is conjectured yet.
Predictions above (5 x 5 -> 9, 3 x 6 -> 8) were written before any code ran on those grids.

Outcome (2026-08-25, later): 3 x 6 confirmed the prediction (blackout 8, kept 10); 5 x 5 refuted
it (blackout 10, kept 15, predicted 9 / 16), engine and brute agreeing. The conjecture is dead
as stated. Kept sizes on squares are now 4, 9, 15 (3 x 3, 4 x 4, 5 x 5); the 5 x 5 case has only
8 maximum blackouts versus 1810 for 4 x 5, so the structure changes character at 5 x 5. The
Strip Theorem remains proven for n = 2 and the formula still holds for every n <= 4 entry.

Enumeration referee: square rectangle counts 1, 10, 44, 130 (2 x 2 .. 5 x 5) match OEIS A085582
("number of rectangles, orthogonal or not, with corners on an n X n grid of points":
0, 1, 10, 44, 130, 313, ...) term for term.

5 x 5 structure (2026-08-25): the 8 maximum blackouts form a single orbit of the dihedral group
D4 with trivial stabilizer -- the extremal object is unique up to symmetry and has none of its
own. Representative blackout (rows top to bottom, '#' = blacked out, '.' = kept):
    ..###
    ..#..
    .##..
    ##...
    #...#
i.e. a 9-point anti-diagonal staircase band (= n+m-1) plus the isolated corner (5,5). The kept
set is two triangular blocks of 5 and 10 points on either side of the band.

Threshold experiment (2026-08-25): 3 x 6 obeys n+m-1; 4 x 6, 5 x 5, 5 x 6 each exceed it by
exactly 1. Squareness is ruled out (4 x 6 breaks). Two hypotheses fit all data for n >= 3:
  H_area: blackout = n+m-1 + [nm >= 24]
  H_sum:  blackout = n+m-1 + [n+m >= 10]     (n = 2 excluded: Strip Theorem gives m+1 always)
Pre-registered before running: 3 x 7 -> H_area 9 / H_sum 10; 3 x 8 -> 11 (both); 4 x 7 -> 11
if the excess stays 1. Lesson already paid for above: eight confirming cells died at the ninth.

Threshold outcome (2026-08-25, later): 3 x 7 = 9 kills H_sum; 3 x 8 = 10 kills H_area. Both dead.
Enumeration counts 3 x 7 = 68, 3 x 8 = 90, 4 x 7 = 152 match OEIS A289832 (triangle of rectangle
counts on rectangular grids), which with A085582 is the enumeration's literature citation.

What survives: every three-row grid 3 x 3 .. 3 x 8 has blackout m+2 (kept 2(m-1)), the shape of
the Strip Theorem one row up. The break is a min-dimension >= 4 phenomenon. Four-row kept sizes
9, 12, 14, 17 (m = 4..7) increment 3,2,3 -- consistent with kept(4,m) = ceil(5m/2) - 1, i.e.
2.5 kept points per column against exactly 2 (n=3) and 1 (n=2).
  Three-Row hypothesis: blackout(3,m) = m+2 for all m >= 3.
  Four-Row hypothesis:  blackout(4,m) = 4m - ceil(5m/2) + 1  (= 7, 8, 10, 11, 13, 14, ...).
Pre-registered before running: 3 x 9 -> 11; 4 x 8 -> 13 (Four-Row) vs 12 (excess-1); 5 x 7 -> 12
(excess-1, low confidence). Fitting 4 cells with a formula is exactly how the last one died.

Row-hypothesis outcome (2026-08-25, later): 3 x 9 = 11 confirms Three-Row (now 3 x 3 .. 3 x 9,
seven cells). 4 x 8 = 12 REFUTES Four-Row (ceil(5m/2)-1) on its first test. The survivor is the
plain reading: four-row kept 9, 12, 14, 17, 20 is (n-1)(m-1) - 1 from m = 6 on, and every
large cell so far (4 x 6, 4 x 7, 4 x 8, 5 x 5, 5 x 6) has blackout exactly n+m.
  Excess-1 hypothesis: for min(n,m) >= 4 and the cell not in {4x4, 4x5}, blackout = n+m.
  Three-Row hypothesis: blackout(3,m) = m+2 for all m >= 3 (candidate theorem; Strip-style proof?).
Pre-registered before running: 5 x 7 -> 12 (in flight); 3 x 10 -> 12; 6 x 6 -> 12. A 6 x 6 value
of 13 would mean the excess grows and excess-1 is dead.

Round close (2026-08-25): 3 x 10 = 12 (Three-Row, 8 cells) and 6 x 6 = 12 (excess-1, 7 cells:
4x6, 4x7, 4x8, 5x5, 5x6, 5x7, 6x6) both confirmed as pre-registered. Both hypotheses survive the
night. Next kill attempts are 5 x 8 and 6 x 7 (40-42 points, engine ~30+ min each) and 3 x 11.

Correction (2026-09-18): the legend of the 5 x 5 representative above originally read '.' = blacked
out, '#' = kept, which was backwards. The '#' set has 10 points and is the valid maximum blackout;
the '.' set has 15 points and is the kept set (as a blackout it is invalid). Checked with the
definitional brute: valid(# set) = True, valid(. set) = False. The picture itself and the text
around it (9-point staircase plus the corner (5,5); kept blocks of 5 and 10) were already correct.

## Proof update: 2026-09-21

Entries above are unchanged. Three-Row is now proved: blackout(3,m) = m+2 for every m >= 3.
The four-row case of Excess-1 is also proved: blackout(4,m) = m+4 for every m >= 6 (not the
refuted ceil(5m/2)-1 kept-set formula). 4x4 and 4x5 are settled by checking all 72 and 1,440
blackouts that could reach the upper bound (verify_narrow.py).

Proof: the axis-aligned rectangles are identifiable iff the row-column incidence graph has no
C4 or C6. Replacing each column by a tree on its black rows gives a triangle-free graph on the
rows, and Mantel bounds its edges. The constructions are checked against every tilted rectangle
on three and four rows. See paper/narrow_rows.tex.

Still open: Excess-1 with both dimensions >= 5, and the optimum counts beyond strips.

## Lower bound n+m on the open cells (2026-09-24)

While building the game in `game/`, an exhaustive search found that every monotone staircase from
one corner to the opposite corner (n+m-1 points) is a valid blackout on every size from 5 x 5 to
10 x 10, and that every one of these sizes also has valid blackouts made of a staircase plus one
more point (from 18 of them on 5 x 6 up to 173,716 on 10 x 10). So blackout(n,m) >= n+m on every
open cell up to 10 x 10, which is the lower half of Excess-1. The game stores one checked example
per size. This has only been checked by one program so far, so it still needs a second check
(engine or brute) before it goes in the paper.

## Second check of the n+m lower bound and the 5 x 5 value (2026-10-01)

The 21 staircase-plus-one blackouts stored in `game/game.js` (5 x 5 to 10 x 10, n+m points each)
were rechecked by `verify_narrow.py`, which enumerates rectangles from equal diagonals with a
common midpoint and shares no code with the game. All 21 are valid, and the rectangle counts on
the squares (130, 313, 640, 1192, 2044, 3305) match OEIS A085582. So blackout(n,m) >= n+m on every
cell up to 10 x 10 with both sides at least 5, now by 2 independent programs.

5 x 5 is proved: a bipartite graph on 10 vertices with no C4 or C6 has at most 10 edges, so the
upper bound is 10 by hand. The same script lists all 44,640 ten-point blackouts of the 5 x 5 grid
with no short cycle and finds exactly the 8 optima, one D4 orbit.

## Pre-registered predictions for the paper computations (2026-10-17)

Written before any of these runs. Coordinates here are one-based as in the notes, (column, row),
(1,1) top left. Two independent methods for every value, as always.

1. Five rows, whole row. Prediction: blackout(5,m) = m+5 for 5 <= m <= 12, and the smallest width
   m_0 with blackout(5,m) = m+6 is 17 (interval 13 <= m_0 <= 20; the known family starts at 21).
   Once m+6 is reached it stays reached at every larger width through 20. Excess-5 witnesses
   (staircase plus one, or any) exist at every 11 <= m <= 16. Falsifiers: an m+6 witness at
   m <= 12, non-monotone attainment, or a width 11..16 with no m+5 witness.
   Method: the equality structure (six doubles forming K_{3,2} on the rows, singletons elsewhere)
   turns "exists a blackout of m+6 points" into a SAT instance per 2+3 row partition. UNSAT for all
   partitions proves m+5. Second method: a second SAT backend on an independently written encoding,
   and at m <= 12 the unstructured encoding and CBC where it finishes. Every witness is rechecked by
   verify_narrow.collision.
2. Small cells: blackout(5,8) = 13, blackout(5,9) = 14, blackout(6,7) = 13, blackout(6,8) = 14,
   blackout(7,7) = 14 (excess 1 on all five). Same SAT route, UNSAT confirmed by a second backend.
3. Four rows, optimum counts. Prediction: a_4(8) between 1,500 and 4,000; the dominant row support
   is rows {1,3} against {2,4} (the middle partition); the growth rate rho of a_4(m) satisfies
   3.4 <= rho < 212^(1/4) = 3.8158; the generating function has a pole of order 5 at 1/rho; the
   recurrence order lies between 20 and 300; a_4(m) / (3 (m)_4 4^(m-4)) decreases from m = 7 on.
   Method: exact DP over (used edges, geometry state) on the exported machines, then a guessed
   recurrence certified by an all-coordinate annihilation identity. Second method: direct
   enumeration of all 1,290,240 equality candidates at width 8 against every rectangle.
4. Three rows. Prediction: E_4, E_5, E_6 = 168, 620, 2220 (these follow from the stored class
   counts, so they are a consistency check); the closed form of E_m has quadratic coefficient
   polynomials on (1+sqrt3)^m and (1-sqrt3)^m with a positive leading coefficient on the first;
   E_m > 0 for all m >= 4. Orbits under row reflection and column reversal: o_3(3) = 15,
   o_3(4) = 58; no reversal-fixed optimum at even width; reflection-fixed optima only at m = 3.
   Second method: exact fractions arithmetic without sympy against the transfer counts, and brute
   enumeration of the group action for m <= 10.
5. Five rows at width 21: between 4 and 1,000 labelled optima; the published witness is fixed by
   the half turn, so its orbit under reflections has size 2.
6. Six rows: about even odds that some width at most 60 attains the row bound m+9. Nothing is
   claimed either way until a witness passes the collar test or the searches finish.

## Outcomes, part 1 (2026-10-17): three rows and four rows

Item 4 (three rows) confirmed on every point. E_4, E_5, E_6 = 168, 620, 2220, and the closed form
is E_m = p_+(m)(1+sqrt3)^m + p_-(m)(1-sqrt3)^m + T_m with
p_+-(m) = ((19 +- 11 sqrt3) m^2 + (61 +- 41 sqrt3) m + (104 +- 28 sqrt3))/432 and
T_m = (-1)^(m/2) 2^(m/2) (2m^2+41m-104)/216 for even m, (-1)^((m-1)/2) 2^((m-1)/2) (7m^2-32m-175)/432
for odd m. Proved as an exact identity two ways (sympy partial fractions of 4G_AB+G_X; fractions-only
recurrence check against the transfer counts through width 100). E_m > 0 for m >= 4. Orbits:
o_3(3..15) = 15, 58, 227, 864, 3190, 11502, 40549, 140863, 482755, 1636860, 5497794, 18325769,
60680951; no reversal-fixed optimum at even width; reflection-fixed only bXb at m = 3. Burnside
formulas and definitional enumeration (m <= 10) agree. Scripts jis/scripts/three_row_*.py.

Item 3 (four rows): a_4(8) = 2118 (in the predicted range), a_4(9) = 13332, a_4(10) = 75398, each by
the machine DP and by enumerating every equality candidate against every rectangle; a_4(m) for
m <= 1500 by the machine. The dominant support is rows {1,3} against {2,4} (confirmed), the pole
order is 5 (confirmed), the survival ratio decreases from m = 7 on (confirmed, exactly through 1500).
Two guesses were WRONG: the growth rate is rho = 3.351996777310..., below the predicted 3.4
(the largest real root of a degree-20 polynomial), and the minimal recurrence has order 420, not
20..300. The generating function is P_4/Q_4 with deg P_4 = 444, deg Q_4 = 420, certified by an
all-coordinate annihilation check on the three product automata (6,128, 7,792 and 4,912 states),
and rechecked by independent polynomial arithmetic. Scripts jis/scripts/four_row_*.py, data in
jis/data/four_row_*.json.

## Outcomes, part 2 (2026-10-17): five, six and seven rows

Item 1 (five rows): REFUTED in the interesting direction. blackout(5,m) = m+5 for m = 5, 6, 7 and
blackout(5,m) = m+6 for every m >= 8, so m_0 = 8, not the predicted 17 (interval 13..20 also wrong).
blackout(5,8) = 14 and blackout(5,9) = 15, against the predicted 13 and 14. Attainment is monotone, as
predicted. The four 5 x 8 optima form one orbit. Every width from 8 on comes from one board: the
width-8 optimum (1,1),(1,4),(2,4),(2,5),(3,2),(3,5),(4,5),(5,5),(6,3),(6,4),(7,2),(7,3),(8,1),(8,2)
padded on the right by top-row singletons; the width-13 collar board is valid, so the collar theorem
gives every width. Checked by three SAT routes (two encodings, cadical153 and glucose4, plus the
unstructured one through width 12), a solver-free enumeration of all 5,040,000 width-8 candidates,
brute.py, and a separate check with its own code (glucose3, lingeling). Counts: a_5(8..12) = 4, 44,
350, 3004, 24706 (two methods); a_5(13..23) = 193406, 1346758, 8650416, 52128242, 299349210,
1653637492, 8828301226, 45743165894, 230934909328, 1139486126866, 5510071794736 (two exact counters,
both using the equality theorem). The published width-21 witness is NOT fixed by the half turn.

Item 2 (small cells): blackout(6,7) = 13 and blackout(7,7) = 14 as predicted. blackout(6,8) = 15,
NOT 14: the first cell where the excess over n+m-1 reaches 2. Witness (1,1),(1,5),(2,1),(3,1),(3,2),
(3,3),(4,3),(4,4),(5,4),(6,4),(7,4),(7,5),(7,6),(8,2),(8,6). Upper bounds by UNSAT in two independent
encodings (three solvers), rechecked by separate code. Excess-1 is dead on a small grid.

Item 6 (six rows): yes. blackout(6,m) = m+9 exactly from m = 15 on (for m >= 8). Widths 8..14: all ten
3+3 partitions UNSAT with two encoders (the separate recheck did not finish this part). Width 15: one
partition SAT. The width-16 witness passes the W_6 = 7 collar test, so every m >= 16 follows. Side
facts: blackout(6,9) in {16,17}, blackout(6,10) in {17,18}.

Item 5 (five rows at width 21): REFUTED. a_5(21) = 230,934,909,328, not between 4 and 1,000. Three
independently written exact counters agree on a_5(m) for every 5 <= m <= 23, partition by partition
(all three rest on the equality theorem and the span bound W_5 = 5); explicit listings of 10,001
optima at widths 21, 22 and 23 were each checked against the definition. The published width-21
witness is NOT fixed by the half turn (its image has the singletons in row 5), so its orbit has size
4. Under the equality theorem no five-row optimum is fixed by a reflection, so every orbit has size 4
or 2.

## Pre-registered predictions for the remaining table counts (2026-10-17)

Written before any of these runs. These are guesses at orders of magnitude only, with no model behind
them beyond the nearby counts a_4(5) = 1,810, a_4(6) = 26, a_5(5) = 8 and a_5(8) = 4. Here a_h(m) is
the number of valid blackouts of the h x m grid of size f(h,m).

1. a_5(6) (11 points): order 10^2, anywhere from 10 to 1,000.
2. a_5(7) (12 points): order 10^3, anywhere from 100 to 10,000.
3. a_6(6) (12 points): order 10 to 10^2, a multiple of 8 orbits counted with their sizes.
4. a_6(7) (13 points): order 10^2, anywhere from 10 to 10,000.
5. a_7(7) (14 points): order 10 to 10^2.
6. a_6(8) (15 points): very few, between 1 and 50, since 6 x 8 is the first cell with excess 2.
7. f(7,8): 16, with low confidence (15 is also plausible).
Method: SAT model enumeration with blocking clauses on encoding A of small_cells_sat.py, with the
cardinality fixed to f(h,m) and every model rechecked by verify_narrow.collision. Second method: a
separately written column-by-column search with its own rectangle list, pruned by the known values
of f on narrower grids. A count is recorded as established only if both agree.

## Outcomes for the remaining table counts (2026-10-17)

a_5(6) = 76 (guess 10..1,000, right order), a_5(7) = 1,184 (guess 100..10,000, right), a_6(6) = 160 (guess
10..100, a bit above), a_6(7) = 2,536 (guess 10..10,000, right), a_7(7) = 7,300 (guess 10..100, WRONG by
two orders), a_6(8) = 8 (guess 1..50, right). Each by two SAT encodings on different solvers and a
column search without a solver; 7 x 7 also by a split SAT run. f(7,8) = 16 (guess 16, right): no valid
17-point blackout by two split SAT runs, and 16 points are attained. The count a_7(8) = 18 comes from one
method only; the second count was stopped before it finished. Data in jis/data/table_counts/.

## Pre-registered predictions for six rows at widths 9..14 (2026-11-06)

Written before any of these runs. Known: m+7 <= blackout(6,m) <= m+8 for 9 <= m <= 14 (the m+9
structure is UNSAT there, and the 6 x 9 board of 16 points passes the collar test).

1. Structure (proved by hand before the runs, to go in the paper): a valid 6 x m blackout with m+8
   points has every column a singleton or a double, the doubles on distinct row pairs, and the
   double pairs form one of: K_{3,3} minus an edge (90 labelled cases), K_{2,4} (15 cases), or
   K_{3,3} with one empty column (10 cases). Reason: |S| = t + e(H) with e(H) <= 9 and t <= m, so
   (t, e(H)) = (m, 8) or (m-1, 9); a triangle-free graph on 6 vertices with 8 edges is bipartite and
   connected (K_{3,3}-e or K_{2,4}), and a column with 3 or more black rows gives a triangle under a
   re-chosen tree (two same-side vertices of these graphs have a second common neighbour).
2. Prediction: blackout(6,m) = m+8 holds from some width m_1 on and fails below it, with m_1 = 11
   (interval 10 <= m_1 <= 13). Attainment is monotone in m. K_{2,4} is never used by an optimum
   (low confidence).
3. Falsifiers: m+8 at m = 9; a gap (m+8 at some width, m+7 at a larger width <= 14); no m+8 at any
   width 9..14.
Method: the 115 cases per width as SAT instances under two separately written encodings (A on
cadical153, B on glucose4). UNSAT on every case under both proves blackout(6,m) = m+7. Every model is
rechecked against the full rectangle list by two enumerators.

## Pre-registered predictions for seven rows (2026-11-06)

Written before any of these runs. Row bound: blackout(7,m) <= m+12 (q_7 = 12), equality only with
twelve doubles on the edges of a K_{3,4} and singletons elsewhere; W_7 = 10.
1. Some width m <= 40 has a valid 7 x m blackout of m+12 points that passes the collar test (10
   boundary-row singletons per side), so blackout(7,m) = m+12 for all large m. Confidence: about 70%.
2. The smallest width with an m+12 blackout lies in 20..32 (point guess 25; the first widths were 8
   for five rows and 15 for six rows).
Method: six_row_structured_sat.py --rows 7 (35 partitions, encoder A, cadical153), witness rechecked by
verify_narrow and the side-vector enumerator, collar test by both enumerators. Second method for a
witness: brute.py or the Lean kernel check.

Side observation (2026-11-06, exploration, not a prediction): spreading the doubles more than 2 W_h
apart in a sea of row-1 singletons is NEVER valid for h >= 5. A double with a black point d rows below
row 1, d = 4, gives the tilted rectangle with diagonals (y,1)-(x,1+d) and a horizontal one (3-4-5),
showing a horizontal pair whose axis rival uses two row-1 singletons. Seen at 5 x 77 and 6 x 150.

## Outcomes for six rows at widths 9..14 (2026-11-06)

Item 1 (structure): proved by hand as stated (paper, Lemma "one point below the bound").
Item 2: blackout(6,m) = m+7 for m = 9, 10, 11 and m+8 for m = 12, 13, 14. So m_1 = 12: inside the
predicted interval 10..13, but the point guess 11 was WRONG. Attainment is monotone, as predicted.
The K_{2,4} family is never used by the witnesses found, but this was not checked exhaustively at 12..14.
- Widths 9, 10, 11: all 115 cases UNSAT under encoder A (cadical153) and encoder B (glucose4),
  jis/data/six_row_excess8_w{9,10,11}_{A,B}.json. LRAT certificates for all 345 encoder-A instances
  (CaDiCaL 2.1.2), each passing drat-trim lrat-check and the Lean LRAT checker:
  jis/data/six_row_excess8_certificates.json (proofs, 1.87 GB, kept in lean-work/unsat/proofs).
- Widths 12, 13, 14: SAT witnesses in case K (K_{3,3} minus an edge). One family covers all three:
  16,36,25,12,1^k,23,34,45,56 (k = m-8), valid for k = 4..11 by verify_narrow and the side-vector
  enumerator, and for widths 12, 13, 14 also by solver/brute.py (six_row_excess8_family.json).
  It fails for k <= 3, as it must.
- Calibration: width 8 all 115 UNSAT (f(6,8) = 15 = m+7); width 15 case K SAT (f(6,15) = 24 >= m+8).
So f(h,m) is now known for every h <= 6 and every m.

## Outcomes for seven rows (2026-11-06)

Item 1: CONFIRMED. Partition {2,4,6} | {1,3,5,7} gives m+12 blackouts at widths 26, 28, 30, 32, 34 (and
{1,4,7} at 32). The width-28 witness
34,2,2,2,47,2,2,27,25,7,7,7,7,7,67,36,23,2,12,1,1,16,1,1,14,1,45,56
passes the collar test with 10 row-7 singletons on the left (both enumerators), so f(7,m) = m+12 for
every m >= 28 by the collar theorem; f(7,26) = 38 too. brute.py check running.
Item 2: smallest width <= 26; 20, 22, 24 still unresolved; 27 launched.

Second, independent construction (gadget decomposition, new, exploratory). Put each double of
K_{A,B} in its own cluster, clusters separated by >= W_h row-1 singletons. A tilted rectangle then
meets at most one cluster, and the only coupling between clusters is an axis rival through a double
of another cluster, which can only rival a vertical pair {r,s} in F or a singleton (x,r) with
{r,s} in F, s in B_x. So the board is valid iff each cluster, padded by W_h row-1 columns on both sides,
is valid and avoids those two F-relative presentations ("gadget"). SAT finds single-edge gadgets
for every edge, partition odd|even rows:
  h = 5, 6: 12,14,16,23,34,36 alone; 25: 5,5,5,25; 45: 5,5,5,45; 56: 6,6,6,6,56.
  h = 7: as above with 25: 5,7,5,25; 45: 5,7,5,45; 27: 4,5,7,5,27,6; 47: 3,47,5,5,5; 67: 6,7,7,7,7,67,6.
Assembled boards checked directly by verify_narrow: 5 x 47 (excess 6), 6 x 89 (excess 9), 7 x 167
(excess 12), all valid with W_h end padding, hence collar boards.
Why lone doubles fail: with padding row 1, a black (0,c) and a row-1 corner (y,1) are opposite corners
of a tilted rectangle whose other diagonal is horizontal whenever c-1 = 2k >= 4 (leg of the triple
(k^2-1, 2k, k^2+1)); it shows a horizontal pair of two row-1 columns, which has an axis rival. So
exactly the odd rows c >= 5 need shielding. The general theorem f(h,m) = m + q_h (m large) reduces to a
uniform family of shields for these rows. Open.

## Pre-registered predictions: staircase junctions (2026-11-06, general-theorem search)

Written before the runs at h >= 6. Setup: F = all pairs {odd row, even row}. A *step junction* is a
sea of row-s singletons, one double {s,t}, then a sea of row-t singletons (s, t of opposite parity);
a *switch* is a sea of row s followed directly by a sea of row t (s != t). A window is the junction
with 2 W_h + 1 sea columns on each side. A window is *good* if it is valid, hides no tilted
rectangle, and no weak tilted rectangle shows a vertical pair in F or a singleton (x,r) with
{r,u} in F for some u in B_x. On five rows every step junction (both directions) and every switch is
good (checked 2026-11-06 with W_5 + 1 sea columns).
Prediction: for every 6 <= h <= 12, every step junction and every switch is good. Confidence: 50%.
Falsifier: one bad window. Method: junction.py (scratchpad, to be copied into jis/scripts if it holds),
direct collision test with verify_narrow.rectangles, then assembled full boards checked directly.
Outcome: FALSIFIED at h = 6. Bad windows: switch and step between rows 2 and 5 (both directions);
at h = 7 also 3 <-> 6. Reason: a black point of each sea as opposite corners with diagonal (4,3)
and a vertical other diagonal of length 5 shows the vertical pair {(s+t-5)/2, (s+t+5)/2}, of
opposite parity, hence in F. Odd distances d >= 3 are traps; d = 1 never is (1 is no leg).

## Pre-registered prediction: staircase of seas with loops (2026-11-06)

Construction S_h: seas in rows 1, 2, ..., h from left to right; sea a and sea a+1 are joined by the
double {a,a+1} (step); every other pair {a,b} of F with b >= a+3 is a *loop*: one double {a,b} inside
the sea of row a (that is, the extra point (x,b) in a column of sea a). Junctions are > 2 W_h apart.
Prediction: every step window a -> a+1 and every loop window (a,{a,b},a) is good for all h <= 12, and
the assembled boards are valid for h = 5..9. Confidence 40%. Falsifier: one bad window or board.
Outcome: FALSIFIED at h = 6 (loops at row distance 3: same vertical-pair trap). Steps a -> a+1 were good
for every h <= 8.

## Pre-registered prediction: alternating boundary seas (2026-11-06)

Construction Z_h: seas alternate between row 1 and row h; every double {a,b} of F sits at a switch
(sea 1, double, sea h) or (sea h, double, sea 1). Reason to expect it: with both seas in boundary
rows, every odd-distance vertical trap needs hypotenuse L <= d (impossible), and every even-distance
horizontal trap straddles the switch column, so its two endpoints lie in different seas.
Seen first at h = 7, top|bottom partition: all 12 edges good in both directions.
Prediction: for every 5 <= h <= 12 and both partitions (odd|even and top|bottom), every edge is good
at a 1 -> h switch and at an h -> 1 switch, and assembled boards Z_h are valid for 5 <= h <= 9.
Confidence 60%. Falsifier: one bad window or board.
Outcome (alternating boundary seas): CONFIRMED on every check run. Windows: no bad window for
h = 5..10, both partitions (h = 11, 12 still running). Full boards checked directly by
verify_narrow.collision: Z_5, Z_6, Z_7 (both partitions, end padding 2W_h + 1 and also none),
Z_8 odd|even (width 421, excess 16), and C_5 on 5 and 7 rows (non-bipartite H, excess 5). Gap W_h
also passes at h <= 7; gap floor(W_h/2) fails.
Hand proof written (notes/general_theorem_gadgets.md): for every h >= 3 and every triangle-free H on
the rows, alternating boundary seas with gaps >= 2W_h + 1 give a valid blackout with m + e(H) points.
With H = K_{floor(h/2),ceil(h/2)}: f(h,m) = m + q_h for all m >= q_h + (q_h - 1)(2W_h + 1).
Needs an independent audit before it is used.

## Seven rows, widths 26..28, and corrections to earlier entries (2026-11-06)

Width 27 is SAT for the partition {1,4,7} | {2,3,5,6}:
57,1,16,37,3,67,1,7,1,1,34,7,24,1,15,27,7,1,7,7,45,1,46,7,13,6,12.
With widths 26 and 28 and the width-28 collar board, f(7,m) = m+12 for every m >= 26. The witnesses of
widths 26, 27, 28 and the 7 x 38 collar board are valid by verify_narrow, the side-vector enumerator,
and solver/brute.py (seven_row_witness_brute.json). Item 2 of the seven-row predictions: the
smallest width is at most 26 (inside 20..32); widths 20..25 are not settled.

Corrections to earlier entries (kept as written above):
- The 2026-09-21 entry points to paper/narrow_rows.tex, which no longer exists. The proofs are in
  jis/pemmasani.tex (sections 4 to 6).
- Outcomes part 2 (2026-10-17) says the separate six-row recheck "did not finish". The DFS checks for
  widths 9..13 have since finished, and width 14 rests on the two SAT routes; all 70 instances
  also have LRAT certificates.
- The table-count outcomes call a_7(8) = 18 "the count". Only a_7(8) >= 18 is established (one method).

## General theorem: audit and second check (2026-11-06)

An independent read of the hand proof in notes/general_theorem_gadgets.md found it correct, with
three wording gaps (alpha: whiteness must follow the straddle; gamma-diag: c >= 3; side-side: both
endpoint matchings must be checked). All three are fixed in the note. A separately written board
check (jis/scripts/general_theorem_board_check.py, random balanced partition, random edge order,
random end padding, minimal gap 2 W_h + 1) is valid for h = 5, 6, 7 (two seeds each) and h = 8, with
excess exactly q_h (jis/data/general_theorem_board_check.txt). So f(h,m) = m + floor(h^2/4) for every
h >= 3 and every m >= q_h + (q_h - 1)(2 W_h + 1).

Side experiment (square grids): the GQ(2,2) incidence graph placed on the 15 x 15 grid under random
row and column orders keeps at most 28 of its 45 points after the fewest deletions that make it
valid (3 orders tried). That is below 2n = 30, so it does not answer "first n with f(n,n) > 2n".

## Seven rows down to width 24 (2026-11-06)

Widths 24 and 25 are SAT for the partition {2,4,6} | {1,3,5,7}:
56,45,34,23,1,1,14,1,12,1,6,16,7,1,47,6,67,7,7,6,25,7,36,27 and
16,25,7,27,1,7,7,7,12,2,14,1,1,23,34,45,56,7,7,47,6,6,4,36,67.
Both pass verify_narrow, the side-vector enumerator and solver/brute.py. So f(7,m) = m+12 for every
m >= 24. Widths 20 and 22 are still running; the least width is open (open question 2).

## General theorem in the paper and in Lean (2026-11-06)

The theorem is now Section 8 of jis/pemmasani.tex (Theorem "large widths" and Proposition
"alternating seas"), with intro Theorem D. The h = 9 board (width 708, excess 20) is also valid.
The Lean files lean/KageyProblems/Problem001/GeneralLocal.lean and GeneralTheorem.lean prove
fval_general : 3 <= h -> Mh h <= m -> fval h m = m + h^2/4 symbolically for every h, with the
Proposition for any triangle-free graph (AltHyp.alt_sea); #print axioms gives only propext,
Classical.choice and Quot.sound. Open question 2 now asks for the growth of the least such width.
