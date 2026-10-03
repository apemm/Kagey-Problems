# First checks for the general version of Problem 137

Date 2026-10-02. Setup: f(x) = x + 1, g_m(x) = -1/(m x), root 0, rank d(x) = least number of moves
from 0, a_m(n) = number of rationals of rank n, q = order of g_m f (q = 3, 4, 6 for m = 1, 2, 3 and
infinite for m >= 4). Predictions and verbatim outcomes are in `ledger.md` (G1 to G13).
Scripts: `../explore.py` (run 1), `../words.py` (runs 2 and 3). Raw output: `explore_run1.txt`,
`words_m1.txt`, `words_m2.txt`, `words_m3.txt`, `words_free.txt`, `words_gf.txt`, `g10.txt`,
`oeis_lookup.txt`, `oeis_lookup2.txt`.

## Methods

1. BFS over the tree in exact reduced fractions. Two separate implementations (`explore.py` and the
   `bfs` function of `words.py`) give identical counts on every common depth.
2. Enumeration of reduced digit strings (rule below), each evaluated as f^{c_1} g f^{c_2} g ... g f^{c_k}(0)
   in Python `Fraction`s, compared with BFS point by point (value, multiplicity, rank).
3. Generating function of the reduced strings from the run-counter transfer matrix, solved in sympy,
   plus a hand proof (below).

## Counts

All entries are computer-checked by BFS and by string enumeration to the depth shown, and agree.

| m | q | depth | a_m(0), a_m(1), ... |
|---|---|---|---|
| 1 | 3 | 24 | 1, 1, 2, 2, 3, 5, 7, 10, 15, 22, 32, 47, 69, 101, 148, 217, 318, 466, 683, 1001, 1467, 2150, 3151, 4618, 6768 |
| 2 | 4 | 28 | 1, 1, 2, 3, 5, 7, 11, 18, 28, 44, 69, 108, 170, 267, 419, 658, 1033, 1622, 2547, 3999, 6279, 9859, 15480, 24306, 38164, 59923, 94088, 147732, 231961 |
| 3 | 6 | 30 | 1, 1, 2, 3, 5, 8, 13, 21, 34, 54, 87, 141, 227, 366, 590, 951, 1533, 2471, 3983, 6420, 10349, 16682, 26890, 43345, 69869, 112624, 181542, 292633, 471704, 760354, 1225638 |
| 4, 5, 6 | inf | 22 (24 for m = 4 by BFS) | F(n+1): 1, 1, 2, 3, 5, 8, ..., 28657 |

Points enumerated: 638804 (m = 2), 3228541 (m = 3), 75024 (each of m = 4, 5, 6).

## Generating functions

Write N_q(t) = 1 + t^2 + t^4 + ... + t^{2q-4} - t^{2q-3} and D_q(t) = 1 - t - t^3 - t^5 - ... - t^{2q-3}.

| m | q | generating function | recurrence | from n = |
|---|---|---|---|---|
| 1 | 3 | (1 + t^2 - t^3)/(1 - t - t^3) | a(n) = a(n-1) + a(n-3) | 4 |
| 2 | 4 | (1 + t^2 + t^4 - t^5)/(1 - t - t^3 - t^5) | a(n) = a(n-1) + a(n-3) + a(n-5) | 6 |
| 3 | 6 | (1 + t^2 + t^4 + t^6 + t^8 - t^9)/(1 - t - t^3 - t^5 - t^7 - t^9) | a(n) = a(n-1) + a(n-3) + a(n-5) + a(n-7) + a(n-9) | 10 |
| >= 4 | inf | 1/(1 - t - t^2) | Fibonacci | 2 |

Fit checks (computer-checked).

- m = 2. Numerator fitted from terms 0..5 with the preregistered denominator D_4. It matches the 23
  further BFS terms 6..28. A blind (d, d) Pade fit first succeeds at d = 5 (terms 0..10) and matches
  18 further BFS terms. It returns D_4.
- m = 3. Numerator fitted from terms 0..9 with D_6. It matches the 21 further BFS terms 10..30. The blind
  Pade fit first succeeds at d = 9 (terms 0..18) and matches 12 further BFS terms, which is below the
  15-term standard. So the D_6 fit is the one that meets it.
- m = 1. Numerator from terms 0..3 with D_3 matches 21 further terms. This is Theorem A.

Growth constants (positive root of psi^{2q-3} = psi^{2q-4} + psi^{2q-6} + ... + 1): q = 3: 1.46557,
q = 4: 1.57015, q = 6: 1.61193. The observed ratios a(28)/a(27) = 1.5701 for m = 2 and a(30)/a(29) =
1.6119 for m = 3 agree.

## The reduced-word rule (final, unchanged from the vision file)

A word is f^{c_1} g f^{c_2} g ... g f^{c_k}, applied right to left starting at 0, with c_1 >= 0 and
c_2, ..., c_k >= 1. Its weight is c_1 + ... + c_k + k - 1.

- q = 4 (m = 2). No two consecutive digits among c_2, ..., c_k equal 1, except that c_2 = c_3 = 1 is
  allowed when c_1 = 0 (and then c_4, if present, is at least 2).
- q = 6 (m = 3). No four consecutive digits among c_2, ..., c_k equal 1, except that a run of exactly
  four 1's starting at c_2 is allowed when c_1 = 0.
- q = 3 (m = 1, control). No digit among c_2, ..., c_k equals 1, except c_2 = 1 when c_1 = 0. This is
  Theorem B(ii).
- q infinite (m >= 4). No restriction.

Status: computer-checked. For m = 2 to rank 28 and m = 3 to rank 30 every point of the tree has exactly
one reduced word of weight at most the depth, that weight is its rank, no reduced word applies g at 0,
and every reduced word of weight at most the depth lands on a point of exactly that rank. The same holds
for m = 4, 5, 6 with no restriction to rank 22. A point could in principle have a second reduced word of
weight above the depth. The check cannot see that.

## Counting the reduced words (proved, for every q >= 3)

This part is about the word language only, so it holds for every q, including q = 5 and q >= 7 where
no rational tree exists. Give each interior digit c_j (j >= 2) the weight c_j + 1, which counts the g
after it, and give c_1 the weight c_1. Then a digit 1 costs u = t^2, a digit c >= 2 costs
B = t^3/(1 - t), and the weight of the word is the total. Let R = 1 + u + ... + u^{q-3}, the runs of 1's
of length at most q - 3. The words split three ways.

1. k = 1. The word is f^{c_1}, giving 1/(1 - t).
2. k >= 2 and every run among c_2, ..., c_k has length at most q - 3. The digits c_k, ..., c_2 form a
   nonempty sequence with generating function R/(1 - BR) - 1, and c_1 >= 0 contributes 1/(1 - t).
3. k >= 2, c_1 = 0 and the run at c_2 has length exactly q - 2. Then c_k, ..., c_{q} is empty or ends in a
   digit at least 2, giving 1/(1 - BR), followed by u^{q-2}.

Hence the total is R/((1 - t)(1 - BR)) + u^{q-2}/(1 - BR) = (R + (1 - t)u^{q-2})/((1 - t)(1 - BR)).
Note that (1 - t)(1 - BR) = 1 - t - t^3 R = D_q, since t^3 R = t^3 + t^5 + ... + t^{2q-3}. The numerator is
1 + t^2 + ... + t^{2q-6} + t^{2q-4} - t^{2q-3} = N_q. So the generating function is N_q/D_q. For q = 3,
R = 1 and this is (1 + t^2 - t^3)/(1 - t - t^3). With no restriction R = 1/(1 - u), case 3 is empty, and
(1 - t)(1 - BR) = (1 - t - t^2)/(1 - t^2), so the total is 1/(1 - t - t^2). The sympy transfer matrix
agrees for q = 3, ..., 8 and finds no cancellation there.

Hence Conjecture A_q follows from Conjecture B_q (proved implication). B_q itself is computer-checked
only, for q = 4 and 6, to the ranks above.

## Predictions

| id | statement (short) | status |
|---|---|---|
| G1 | m = 2 recurrence with lags 1, 3, 5 from n_0 <= 8 | held, n_0 = 6, checked to n = 28 by both methods |
| G2 | m = 3 recurrence with lags 1, 3, 5, 7, 9 from n_0 <= 12 | held, n_0 = 10, checked to n = 30 by both methods |
| G3 | m = 4 counts F(n+1) | held to n = 24 (BFS), 22 (strings) |
| G4 | m = 5, 6 same as m = 4 | held to n = 22, both methods |
| G5 | reduced-word rule and rank formula for m = 2, 3 | held to rank 28 and 30 |
| G6 | reached by g iff negative, never by both | held for m = 2 to 28, m = 3 to 26 (also m = 1, 4, 5, 6) |
| G7 | parent map reaches 0 for m = 2, 3, \|p\|, q <= 60; fails for m = 4 | held (3726 failures for m = 4) |
| G8 | m = 1 control | held |
| G9 | string counts equal BFS, GF denominator D_q | held |
| G10 | m = 4 parent map cycles at 1/2 | held |
| G11 | parent-map steps equal rank | observed at every BFS point for m = 1, 2, 3 (not a blind test) |
| G12 | free case: unrestricted strings, distinct values, rank = weight | held to 22 |
| G13 | GF = N_q/D_q, no cancellation | held for q = 3..8, now proved for all q |

No prediction failed, so no corrected rule was needed. The vision file expected a missed shortcut at an
end of the word. There is none in range. The root shortcut is already excluded. Since (g f)^{q-2}(0) = -1, a run
c_k = ... = c_{k-q+3} = 1 followed by any f-block can be shortened, and the rule forbids that run
unless it is the whole of c_2, ..., c_k with c_1 = 0, which is the point -1 itself.

Note on G6 and G11. Since d(x) equals the number of parent-map steps at every point checked, the
parent map is a shortest-path retraction in range, which is the analogue of Theorem 3.6 that a proof
would need.

## OEIS (checked 2026-10-02 by the `fmt=text` search)

- m = 2 sequence 1, 1, 2, 3, 5, 7, 11, 18, 28, 44, 69, ...: no results. Not in the OEIS.
- m = 3 sequence 1, 1, 2, 3, 5, 8, 13, 21, 34, 54, 87, ...: no results. Not in the OEIS.
- 1/D_4 = 1, 1, 1, 2, 3, 5, 8, 12, 19, 30, ... is A060961 (compositions of n into parts 1, 3, 5).
  So a_2 = (1 + t^2 + t^4 - t^5) times A060961.
- 1/D_6 (compositions into parts 1, 3, 5, 7, 9): no results.

## Open, for the paper

- Proofs of B_q for q = 4, 6 (existence and uniqueness of the reduced word, rank = weight) and of the
  reachability statement for m = 2, 3. Both are computer-checked only.
- A proof of G6 for m = 2, 3, and the conjugacy claims for Gamma_0(2)+ and Gamma_0(3)+, which were not
  checked against a source here.

## Status update (2026-10-02, after the proof files; the lines above are kept as written)

- "Hence A_q follows from B_q ... B_q itself is computer-checked only" is out of date. B_q is now
  proved for every q >= 3 (proofs_route1.md, Lemma 7, Lemma 7' and Theorem 8), and for q = 4, 6 on all
  of Q also by proofs_route2.md, Lemma 7 and Theorem 8. So A_q is proved for every q.
- "Open, for the paper" is out of date. Reachability of all of Q for m = 2, 3 is proved
  (proofs_route1.md Theorem 6, and independently proofs_route2.md Lemma 4 with Theorem 5). G6 is
  proved for every q (proofs_route1.md Corollary 5(c)) and for m = 2, 3 also by proofs_route2.md
  Corollary 6(b). The Gamma_0(m)+ identification for m = 2, 3 is recorded in literature.md Section 3
  (Im and Lee, FULL for Sections 1 and 2, plus a hand conjugation). It is not used in any proof.
- Wording of case 3 in "Counting the reduced words". Read left to right in the order c_2, ..., c_k,
  the block after the run c_2 = ... = c_{q-1} = 1 starts with c_q >= 2 if it exists, followed by blocks
  (one digit at least 2, then a run of at most q - 3 ones). This gives 1/(1 - BR). The count itself is
  unchanged. The paper uses the positive-only count of proofs_route2.md Theorem 9 together with
  a(n) = r(n) + r(n - 1), printed in full in proofs_final.md.
