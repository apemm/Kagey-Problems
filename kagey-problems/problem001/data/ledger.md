# Ledger — hand-verified ground truth (solver test fixtures)

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
| 6 x 6 | ? | - | PREDICTION pre-registered 2026-08-25: excess-1 says 12 (kept 24); first cell with both dims >= 6 |

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
own. Representative blackout (rows top to bottom, '.' = blacked out, '#' = kept):
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
