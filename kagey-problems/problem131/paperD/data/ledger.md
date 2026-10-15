# Problem 131 Paper D ledger

Predictions were written down before the computation that tests them. Each prediction has a kill
condition, and the outcome is recorded below it without changes, also when it refutes the
prediction. The entries are kept in one file per topic. Each ledger uses the statement numbers of
its date. The section numbers below are those of the current papers.

- [ledger_D1.md](ledger_D1.md): the elephant walk, center against end, and the comparison with the
  Markov walk (Section 2). Predictions D1-P1 to D1-P18.
- [ledger_D2.md](ledger_D2.md): the elephant law near its crossing, its profile and its shape
  (Section 3). Predictions D2-P1 to D2-P15, and a correction after an independent check.
- [ledger_D3.md](../../paperF/data/ledger_D3.md): heavy-tailed runs and the golden-ratio exponent
  (now Section 2 of Paper F). Predictions D3-P1 to D3-P8 and D3-V1.
- [ledger_D4.md](../../paperF/data/ledger_D4.md): the aging walk (now Section 3 of Paper F).
  Predictions P1 to P15.

The refuted predictions are D2-P9 (convexity of the law given the first step), D2-P11 (the mode at x
= 320), D2-P12 (the dip for small n), D2-P15 (2 scaling laws for a finite-n shift of the mode), the
closed-range form of the convexity conjecture (found by a separate check for n <= 99), part 2 of
D3-P2 (a slope tolerance), the point value in D3-V1(b) (a slip in reading a rounded root), and D4-P7
(a remainder term). All of them are recorded in the topic files, and none of them concerns a
statement that the paper calls a theorem.

The output of the check scripts is in `verify_output.txt` (quick run) and `verify_output_full.txt`,
both from September 26, 2026, and in `verify_output_2026-10-09.txt` (quick run). All 3 predate the
split and use the statement numbers of their dates.

Note of October 13, 2026. The ledgers `ledger_D3.md` and `ledger_D4.md` (heavy tails and aging) moved to `../../paperF/data` with Paper F.
