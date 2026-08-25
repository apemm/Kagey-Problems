# Ledger — hand-verified ground truth (solver test fixtures)

| grid (r x m) | max blackout | # maximum blackouts | status |
|---|---|---|---|
| 2 x 2 | 4 | 1 | hand-proved (vacuous: one rectangle) |
| 2 x 3 | 4 | 12 | hand-proved; witnesses characterized |
| 2 x 4 | 5 | 32 | hand-proved (Strip Theorem instance); 15-row table verified twice |
| 2 x 5 | 6 | 80 | PREDICTION, pre-registered 2026-08-24, from Strip Theorem; solver must confirm before promotion |
| 3 x 3 | ? | ? | first engine target; tilted rectangles enter |

Strip Theorem (2026-08-24): for 2 x m, m >= 3, every maximum valid blackout has size m+1;
there are exactly m * 2^(m-1); characterized as complements of kept sets with one survivor
per column, missing exactly one column. Proof: two pigeonholes + exactness line (see paper).

TODO: transcribe the verified 2x4 fifteen-row difference-set table here verbatim (fixture for
the table/pruning module).
