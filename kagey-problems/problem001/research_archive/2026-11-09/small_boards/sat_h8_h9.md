# Bounded SAT attempts at m_0(8) and m_0(9)

9 November 2026. Neither threshold is determined. The outcome is

    17 <= m_0(8) <= 39,        20 <= m_0(9) <= 54.

Both upper bounds are new (the earlier bounds were 46 and 58, `2026-11-07/REPORT.md`, section 4.1) and
come with explicit boards that are checked independently. The lower bounds are weak: at height 8 only
width 16 is excluded by a complete run, and at height 9 no width beyond the paper's bound m >= q_h = 20
is excluded.

Each height had one process, `sat_threshold_run.py`, with a budget of 39 minutes (2,281 s and 2,282 s
used). Nothing was restarted. The logs are `sat_threshold_h8.json` and `sat_threshold_h9.json`. Before
the two runs, a 150 s smoke test of the driver ran at height 8; it reached b = 40 and its log was
overwritten by the real run. With it, height 8 used about 40.5 minutes in total.

## Encoder

`equality_sat.py` generalizes the positive-support formulation of `compact_equality_sat.md` to any
height and any balanced partition. It differs from the seven-row script in one point that matters:
every support carries the column extent of the rectangles it comes from, and a clause is placed only
where that whole extent is on the board. A two-point support, for instance, needs the column of the two
removed corners to exist. Without the extent the clause set is too strong near the two ends of the board
(my first version rejected the stored 7 x 21 boards).

Calibration (`calibrate_encoder.py`, `calibrate_encoder.json`):

| Test | Result |
|---|---|
| height 4, widths 5 and 6, all partitions | UNSAT at 5; boards at 6 |
| height 5, widths 7 and 8, all partitions | UNSAT at 7; board at 8 (parity partition only) |
| height 6, widths 14 and 15, all partitions | UNSAT at 14; board at 15 (parity partition only) |
| the four stored 7 x 21 boards | satisfy all 62,021 geometric clauses |

These agree with m_0(4) = 6, m_0(5) = 8, m_0(6) = 15. Width 21 at height 7 was not solved again: the
stored record shows 3,379 s for that instance, and the stored exclusion of width 20 needed cropped
window bounds that are not available at heights 8 and 9.

## Upper bounds

The search looks for a board of the following form: free columns, with all doubles among the first b of
them, followed by W_h columns that are black in row 1 only (W_8 = 13, W_9 = 17). By the finite collar
theorem of the paper such a board stays valid when further row-1 columns are appended, and its prefixes
of width at least b are valid by restriction and contain every double. So f(h, m) = m + q_h for every
m >= b. Only the parity partition is used. The run starts from the stored collar boards (b = 46 and
b = 58) and lowers b, warm starting the solver from the current board with singleton columns deleted.

| Height | b reached | Solver time for the steps | Next step |
|---|---|---|---|
| 8 | 46, 44, 42, 40, 39 | 7 s, 15 s, 62 s, 0.4 s | b = 38: undecided after 1,697 s, 12.9 million conflicts, 68 warm starts |
| 9 | 58, 57, 56, 55, 54 | 202 s, 17 s, 10 s, 3 s | b = 53: undecided after 1,542 s, 7.5 million conflicts, 60 warm starts |

A step can land below its target, because the solver is free to put the last double earlier. Each run
also contains one failed attempt at a step of two columns with a 75 s cap (to 42 at height 8, to 56 at
height 9); the same targets were reached afterwards in single steps.

**Height 8, core of 39 columns** (rows of each column, left to right):

    18,78,27,25,7,7,7,47,7,6,7,58,6,7,67,6,16,6,6,6,56,5,45,4,4,3,4,34,3,23,2,12,1,1,2,38,14,2,36

With 13 further row-1 columns this is an 8 x 52 board with 68 black cells. So f(8, m) = m + 16 for
every m >= 39.

**Height 9, core of 54 columns:**

    78,7,67,6,16,5,6,47,5,6,56,5,45,4,4,34,3,23,2,2,2,12,1,29,2,1,14,1,4,69,9,2,49,1,9,38,8,8,89,9,9,
    18,8,8,5,27,7,7,7,6,58,7,36,25

With 17 further row-1 columns this is a 9 x 71 board with 91 black cells. So f(9, m) = m + 20 for
every m >= 54.

Verification. `rectlib.check_board` enumerates every rectangle as a pair of equal-length segments with
a common midpoint and compares presentations; it shares no code with the encoder. For the two collar
test boards it finds 49,178 rectangles at 8 x 55 and 114,248 at 9 x 74 (the boards as returned, with
three extra row-1 columns), no hidden rectangle and no repeated presentation. The plain-Python version
`check_board_plain`, which compares all presentations directly, agrees. The boards with exactly W_h pad
columns (8 x 52, 9 x 71) are restrictions and were checked as well (`new_boards_h8_h9.json`).

Both cores keep the shape of the boards they were compressed from: a descending staircase 67, 56, 45,
34, 23, 12 in the middle with zero to three fillers after each double, and fillers that mostly sit in
a row of a neighbouring double. Label gaps are 1 to 5 columns (five gaps of 2 and four gaps of 1 and of 4 at
height 8; nine gaps of 3 and six of 2 at height 9).

What the undecided steps mean: no parity-partition collar board with b = 38 (height 8) or b = 53
(height 9) was found, and none was excluded. Boards with another partition, or with a different tail,
were not searched at all.

## Lower bounds

For w = q_h, q_h + 1, ... the run tests every balanced partition (one per vertical reflection class:
23 at height 8, 66 at height 9) at width w, with the horizontal reflection removed by an anchor on one
double. A width is excluded only when every partition is UNSAT. The budget for this phase was 420 s.

| Height | Width | Result |
|---|---|---|
| 8 | 16 | all 23 partitions UNSAT (281 s) |
| 8 | 17 | incomplete: 5 partitions UNSAT, the sixth undecided at the end of the phase |
| 9 | 20 | incomplete: 3 of 66 partitions UNSAT (278 s and 106 s for two of them), the fourth undecided |

Together with the paper's bound f(h, m) <= m + q_h - 1 for m < q_h this gives: equality is impossible
at height 8 for m <= 16, and at height 9 for m <= 19. Hence m_0(8) >= 17 and m_0(9) >= 20. These runs
have no proof logs.

The lower-bound side is far from the truth. Width 16 at height 8 is the case where every column is a
double, and it already costs 12 s per partition on average. A real lower bound near 30 would need the cropped
window bounds that made width 20 feasible at height 7, that is, exact values of f(8, k) for short
windows, which are not known.

## Files

| File | Content |
|---|---|
| `equality_sat.py` | encoder, solver wrapper, partition list |
| `calibrate_encoder.py`, `calibrate_encoder.json` | calibration at heights 4 to 7 |
| `sat_threshold_run.py` | the bounded run (lower phase, then upper phase) |
| `sat_threshold_h8.json`, `sat_threshold_h9.json` | full logs with every solver call |
| `new_boards_h8_h9.json` | the two cores, their collar test boards and checks |
| `rectlib.py` | independent rectangle enumeration and presentation check |
