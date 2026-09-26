# Problem 131 ledger

Current status: H1 and H2 are both proved. The entries below are left as they were written; the
last section records the proof of H2.

Notation: N = number of bounces (Kagey's row N+1), p_N = the unique p in (0,1) at which the middle
bin of row N+1 has the same probability as the two extreme bins, u_N = (1-p_N)/p_N.
u_N is the positive root of S_N(u) = 1, where S_N(u) = sum_j W(N, floor(N/2), j) u^j and W counts
words by number of direction changes (Theorem 2.1 of the paper).

Everything that is proved in the paper is not listed here. This file only tracks the two statements
that were read off from data.

## State of the data when the predictions were written

Exact roots had been computed (float bisection on the exact integer polynomial S_N) for
N = 2..29 and N = 50, 51, 100, 101, 200, 201, 400. Nothing beyond N = 400 had been computed;
an attempt at N = 800 stopped with a float overflow before producing a number.

Observed on that range:
- p_N increasing in N for N = 2..29 (consecutive) and along 50, 100, 200, 400.
- Bessel heuristic: let x_B(m) solve 2x(I_0(2x) + I_1(2x)) = m and put u_B(N) = x_B(N/2)/(N/2).
  Ratio u_B/u_N: 0.8669 (N=10), 0.9176 (20), 0.9586 (50), 0.9761 (100), 0.9864 (200), 0.9924 (400).
  The defect 1 - ratio roughly halves (a bit less) with each doubling of N.

## H1 (monotonicity). Registered before computing any p_N with 30 <= N <= 600 other than those listed above

Prediction: p_N < p_{N+1} for every N with 2 <= N <= 600. In particular no even/odd oscillation
breaks monotonicity (the scaled roots m*u_N do oscillate with parity, so this is a real test).

Kill condition: a single N <= 600 with p_{N+1} <= p_N.

## H2 (Bessel approximation). Registered before computing u_N for N = 800, 1600, 3200

Predicted values from the Bessel equation (these use no information about S_N at these N):

| N    | x_B(N/2) | u_B        | 1 - p_B    |
|------|----------|------------|------------|
| 800  | 2.699282 | 0.00674821 | 0.00670297 |
| 1600 | 3.016712 | 0.00377089 | 0.00375672 |
| 3200 | 3.336975 | 0.00208561 | 0.00208127 |

Prediction: the ratio u_B/u_N lies in [0.9950, 0.9970] at N = 800, in [0.9970, 0.9985] at N = 1600
and in [0.9983, 0.9992] at N = 3200, and u_B < u_N in all three cases.

Kill condition: any ratio outside its window, or u_B >= u_N.

## Results

### H1: confirmed, then proved

Computed p_N for every N from 2 to 601 (exact integer bisection on S_N, 80-bit abscissae).
Monotone violations: none. p_601 = 0.9914770241.

After the run we found a two-line proof: W(N+1, mid, j) >= W(N, mid, j) for every j, with strict
inequality at j = 2, so S_{N+1}(u) > S_N(u) for u > 0 and the root moves left. H1 is therefore
Theorem 5.1(b) of the paper and no longer a conjecture. verify.py checks the coefficient inequality
for N <= 300 and the monotonicity of the computed roots for N <= 121.

### H2: confirmed

| N    | u_N (exact root) | u_B        | u_B/u_N | window            | verdict |
|------|------------------|------------|---------|-------------------|---------|
| 800  | 0.00677674       | 0.00674821 | 0.99579 | [0.9950, 0.9970]  | inside  |
| 1600 | 0.00377962       | 0.00377089 | 0.99769 | [0.9970, 0.9985]  | inside  |
| 3200 | 0.00208823       | 0.00208561 | 0.99874 | [0.9983, 0.9992]  | inside  |

u_B < u_N in all three cases. The exact roots were confirmed by a second method (sign change of the
float dynamic program at p_N -+ 5e-9). H2 remains a heuristic: the paper proves only the leading
term N(1 - p_N) ~ log N and states the Bessel refinement as unproved.

### Refuted along the way

A closed form written down by hand for the row-5 difference, P_4(2) - P_4(0) = (1-p)(1-p+2p^2) - p^3/2,
failed the exact check in verify.py at the first run. The correct polynomial is
(1-p)(1-p+p^2) - p^3/2, i.e. p_4 is the root of 3p^3 - 4p^2 + 4p - 2.


## H2 proved (September 2026)

H2 is now the uniform Bessel approximation theorem in the paper. With h = N/2, x = hu and
F(x) = 2x(I_0(2x) + I_1(2x)), we get 0 <= 1 - h S_N(x/h)/F(x) <= x(x+1)/h for all N >= 2 and
x > 0, for both parities and including the terms past the degree of S_N. Hence
0 <= u_N - u_B = O(log(N)^2/N^2), which gives the log log term, the constant, and one more term in
1/log N. `check_bessel.py` checks the bound and the roots numerically; the output is in
`bessel_verification.txt`.

## Later ledgers for Paper A

Two later computations for Paper A have their own ledgers, kept the same way (predictions first,
then the outcome, with nothing deleted).

- [ledger_every_n.md](ledger_every_n.md): the crossing at every N. Predictions P1 to P8 were
  written before any code ran, and guards G1 to G6 were added after a second check of the proofs.
  Outcome: P1 to P6 and G1 to G6 confirmed. P7 is partly refuted (its bounds on R_N hold, but R_N
  turns negative at N = 4, not near N = 15), and the runtime estimates of P8 were partly missed.
- [ledger_llt.md](ledger_llt.md): the uniform local law. Predictions P1 to P18. Outcome: all
  confirmed except the numeric window of P12 (at N = 101, q = 0.999 the error is +0.578, outside
  the predicted window, although it has the predicted sign).

## Later ledgers for Paper B

Two later computations for Paper B have their own ledgers, kept the same way (predictions first,
then the outcome, with nothing deleted).

- [ledger_B_tie.md](ledger_B_tie.md): the tie on the complete graph, the law with a start, and the
  tree form of the constants a_k (`verify_general_start.py` and `verify_B_tie_repair.py`).
  Predictions T1 to T4, then T4', T1(e'), T4'' and T4''' after a repair pass. Outcome: T1(e) is
  refuted on its tolerance (a finite-difference check that was not precise enough, and the exact test
  T1(e') later covers the same identity), and T4 is refuted at N = 90 and N = 1002 because its
  window equations left out the discrete z^2/N terms. The corrected T4' on new cells and all the
  other predictions are confirmed.
- [ledger_B_crossover.md](ledger_B_crossover.md): the complete first-order factor in the crossover
  theorem for coordinates of order N/(log N)^2 (`verify_crossover_factor.py`). Predictions R1 to
  R8, the scan (a) to (c), L1 and L2, and the repair checks X1 to X3. Outcome: all confirmed (R7
  after a correction to its diagnostic). A side claim in the notes about the leading behavior of
  the correction for 2 or more rare counts is refuted by X1 and was removed.

## Ledgers of Papers C and D

- [../paperC/data/ledger.md](../paperC/data/ledger.md) indexes the ledgers of Paper C.
- [../paperD/data/ledger.md](../paperD/data/ledger.md) indexes the ledgers of Paper D.

## Rerun after the move to 4 papers (2026-09-26)

No new prediction is registered here. After `verify_all.py` and `SUPPLEMENT.md` were set up for the
4 papers, we ran `python -B verify_all.py --paper a` and `python -B verify_all.py --paper b` without
`--full`. Both finished with exit code 0. In the scripts that report their checks in their output,
the guards G1 to G7 all held, the smallest distance from zeta_N to a certified interval was again
1.6562e-5 at N = 218, and the only lines marked False belong to T4, the registered prediction in
`ledger_B_tie.md` that failed.
