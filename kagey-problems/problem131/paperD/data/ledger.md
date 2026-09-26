# Problem 131 Paper D ledger

Predictions were written down before the computation that tests them. Each prediction has a kill
condition, and the outcome is recorded below it without changes, also when it refutes the
prediction. The entries are kept in one file per topic.

- [ledger_D1.md](ledger_D1.md): the elephant walk, center against end, and the comparison with the
  Markov walk (Section 2). Predictions D1-P1 to D1-P18.
- [ledger_D2.md](ledger_D2.md): the elephant law near its crossing, its profile and its shape
  (Section 3). Predictions D2-P1 to D2-P15, and a correction after an independent check.
- [ledger_D3.md](ledger_D3.md): heavy-tailed runs and the golden-ratio exponent (Section 4).
  Predictions D3-P1 to D3-P8 and D3-V1.
- [ledger_D4.md](ledger_D4.md): the aging walk (Remark 4.8). Predictions P1 to P15.

The refuted predictions are D2-P9 (convexity of the law given the first step), D2-P11 (the mode at x
= 320), D2-P12 (the dip for small n), D2-P15 (2 scaling laws for a finite-n shift of the mode), the
closed-range form of the convexity conjecture (found by a separate check for n <= 99), part 2 of
D3-P2 (a slope tolerance), the point value in D3-V1(b) (a slip in reading a rounded root), and D4-P7
(a remainder term). All of them are recorded in the topic files, and none of them concerns a
statement that the paper calls a theorem.

The output of the check scripts is in `verify_output.txt` (quick run) and `verify_output_full.txt`.
