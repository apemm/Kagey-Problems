# Ledger for the general version of Problem 137

Predictions are written here before the computation that tests them, with what would refute them.
Outcomes are recorded below each one and nothing is deleted.

Setup. f(x) = x + 1, g_m(x) = -1/(m x), root 0. The rank d(x) is the least number of moves from 0
to x, and a_m(n) is the number of rationals of rank n. q is the order of g_m f, so q = 3, 4, 6 for
m = 1, 2, 3 and q is infinite for m >= 4.

## 2026-10-02, before any code was run

- G1 (m = 2). a(n) = a(n-1) + a(n-3) + a(n-5) for all n >= n_0 with n_0 <= 8. Refuted if it fails
  at some n in [8, 28].
- G2 (m = 3). a(n) = a(n-1) + a(n-3) + a(n-5) + a(n-7) + a(n-9) for all n >= n_0 with n_0 <= 12.
  Refuted if it fails at some n in [12, 26].
- G3 (m = 4). a(n) = F(n+1) (Fibonacci, F(1) = F(2) = 1) for every n >= 0. Refuted by any n <= 26.
- G4 (m = 5, 6). The same counts as m = 4.
- G5 (rank formula, m = 2, 3). Call a digit string (c_1, ..., c_k) with c_1 >= 0 and
  c_2, ..., c_k >= 1 reduced if no q - 2 consecutive digits among c_2, ..., c_k equal 1, except
  that a run starting at c_2 may have length q - 2 when c_1 = 0. Every point of rank <= 20 is the
  value of exactly one reduced string, and its rank is c_1 + ... + c_k + k - 1. Refuted by one
  point with 0 or 2 reduced strings, or by one wrong rank.
- G6 (colors, m = 2, 3). A point of rank <= 24 is reached at its rank by g if and only if it is
  negative, and no point is reached at its rank by both f and g. Refuted by one counterexample.
- G7 (reachability, m = 2, 3). The parent map P(x) = x - 1 for x > 0, P(x) = -1/(m x) for x < 0
  reaches 0 from every rational p/q with |p|, q <= 60. For m = 4 it does not reach 0 from 1/2.
- G8 (m = 1, control). The script reproduces the known counts 1, 1, 2, 2, 3, 5, 7, 10, 15, 22.

### Outcomes of explore.py, run 1 (2026-10-02, unmodified script, output in data/explore_run1.txt, 87 s)

explore.py ran as written, no fix needed. BFS in exact reduced fractions (p, q).

- m = 1 counts to depth 22: 1, 1, 2, 2, 3, 5, 7, 10, 15, 22, 32, 47, 69, 101, 148, 217, 318, 466, 683,
  1001, 1467, 2150, 3151. Lags 1,3 fail only at n = 3. G8 HELD.
- m = 2 counts to depth 28: 1, 1, 2, 3, 5, 7, 11, 18, 28, 44, 69, 108, 170, 267, 419, 658, 1033, 1622,
  2547, 3999, 6279, 9859, 15480, 24306, 38164, 59923, 94088, 147732, 231961. Lags 1,3,5 fail only at
  n = 5, so the recurrence holds for 6 <= n <= 28. G1 HELD (n_0 = 6) by BFS. Second method pending (G5, G9).
- m = 3 counts to depth 26: 1, 1, 2, 3, 5, 8, 13, 21, 34, 54, 87, 141, 227, 366, 590, 951, 1533, 2471,
  3983, 6420, 10349, 16682, 26890, 43345, 69869, 112624, 181542. Lags 1,3,5,7,9 fail only at n = 9,
  so the recurrence holds for 10 <= n <= 26. G2 HELD (n_0 = 10) by BFS. Second method pending.
- m = 4 to depth 24, m = 5, 6 to depth 22: counts equal F(n+1) at every n. G3 and G4 HELD by BFS.
- G6: for m = 1..6 (to the depths above) no point is reached at its rank by both f and g, and
  "reached by g" equals "negative" at every point. G6 HELD (to depth 28 for m = 2, 26 for m = 3).
  Also true for m = 4, 5, 6, which G6 did not predict.
- G7: for m = 2, 3 the parent map reaches 0 from all rationals p/q with |p|, q <= 60. For m = 4 it fails
  from 3726 of them, the first being -1, -2, -3, ... (1/2 not yet checked by name, see run 2).
  Unpredicted extra: for m = 1, 2, 3 the number of parent-map steps equals the BFS rank at every point
  of the BFS (9918, 638804, 478212 points).

## 2026-10-02, before run 2 (words.py, the second method)

words.py enumerates digit strings by the G5 rule (q = 4 for m = 2, q = 6 for m = 3), evaluates each as
x = c_1 - 1/(m c_2 - 1/(c_3 - 1/(m c_4 - ...))) in exact rationals by applying f^{c_k}, g, ..., f^{c_1}
to 0, and compares with an independent BFS (its own code, not explore.py).
G5 is already registered above. Its range is extended to the full BFS depth (28 for m = 2, 29 for m = 3),
with the same refutation criteria.

- G9 (counts from words). The number of reduced strings of weight w = c_1 + ... + c_k + k - 1 equals the
  BFS count a_m(w) for every w up to the BFS depth. Its generating function, computed symbolically from
  the run-counter transfer matrix, has denominator D_q(t) = 1 - t - t^3 - ... - t^{2q-3} after
  cancellation, and its numerator has degree <= 2q - 3 (this degree bound is informed by run 1).
  Refuted by any count mismatch or by a different reduced denominator.
- G10 (m = 4 fixed point). The parent map for m = 4 cycles 1/2 -> -1/2 -> 1/2 and never reaches 0.
- G11 (rank equals parent-map steps). For m = 2, 3 the number of steps of P from x to 0 equals d(x) at
  every point of the BFS. Already observed in run 1, so this is a recorded observation, not a test.

### Outcomes of run 2 (2026-10-02, words.py; output in data/words_m1.txt, words_m2.txt, words_m3.txt)

- Control m = 1 (q = 3) to depth 24: 21304 strings, counts equal BFS, no value with 2 strings, every
  weight equals the BFS rank, no BFS point missing. GF = (1 + t^2 - t^3)/(1 - t - t^3), which is
  Theorem A. The control works.
- m = 2 (q = 4) to depth 28: 638804 strings and 638804 BFS points. No string applies g at 0. No value
  has 2 strings. Every weight equals the BFS rank. Every BFS point has a string. G5 HELD to rank 28.
  Transfer-matrix GF = (1 + t^2 + t^4 - t^5)/(1 - t - t^3 - t^5), denominator exactly D_4, numerator
  degree 5 = 2q - 3. Its coefficients equal the BFS counts for 0..28. G9 HELD. G1 now has its second method.
  Numerator fitted with D_4 on terms 0..5 matches the 23 further BFS terms 6..28. A blind (d, d) Pade fit
  first succeeds at d = 5 (fitted on terms 0..10, matches 18 further BFS terms) and returns D_4.
- m = 3 (q = 6) to depth 30 (BFS deepened from 26): 3228541 strings and 3228541 BFS points. Same
  outcome on every check. G5 HELD to rank 30. GF = (1 + t^2 + t^4 + t^6 + t^8 - t^9)/(1 - t - t^3 - t^5
  - t^7 - t^9), denominator exactly D_6. Coefficients equal BFS for 0..30. G9 HELD. G2 now has its
  second method and holds for 10 <= n <= 30. Numerator fitted with D_6 on terms 0..9 matches the 21
  further BFS terms 10..30. Blind Pade first succeeds at d = 9 (fitted on 0..18, 12 further BFS terms,
  fewer than 15, so the D_6-denominator fit is the one that meets the 15-term standard) and returns D_6.
- No prediction failed, so no corrected run rule was needed. The G5 rule as written is the final rule.
- Observation (not predicted): in all three cases the numerator is
  N_q(t) = 1 + t^2 + t^4 + ... + t^{2q-4} - t^{2q-3}.

## 2026-10-02, before run 3 (words.py extended to the free case, and G10)

- G12 (free case, m = 4, 5, 6). With no run restriction (every string with c_1 >= 0 and c_2, ..., c_k
  >= 1), the strings of weight <= 22 take distinct values, never apply g at 0, and each weight equals the
  BFS rank. Refuted by one collision, one pole, or one wrong rank.
- G13 (closed form). For q = 5, 7, 8 (no tree, the transfer matrix alone) the reduced-string GF is
  N_q(t)/D_q(t) with N_q = 1 + t^2 + ... + t^{2q-4} - t^{2q-3}, with no cancellation. Refuted by any
  other reduced form. This is a statement about the counting language only.

### Outcomes of run 3 (2026-10-02; data/words_free.txt, words_gf.txt, g10.txt)

- G12 HELD. For m = 4, 5, 6 to weight 22: 75024 unrestricted strings and 75024 BFS points, no pole,
  no collision, every weight equals the BFS rank, counts F(n+1).
- G13 HELD. For q = 3, 4, 5, 6, 7, 8 the transfer-matrix GF reduces to N_q/D_q with denominator exactly
  D_q. A hand proof for every q >= 3 (and the free case giving 1/(1 - t - t^2)) is in checks_report.md.
- G10 HELD. For m = 4 the parent map from 1/2 gives 1/2, -1/2, 1/2, -1/2, ... and never reaches 0.

### OEIS referee (2026-10-02; data/oeis_lookup.txt, oeis_lookup2.txt)

- m = 2 counts 1,1,2,3,5,7,11,18,28,44,69,108,170,267,419,658,1033: no results. Also no results for the
  tail 7,11,...,419.
- m = 3 counts 1,1,2,3,5,8,13,21,34,54,87,...,1533: no results. Also no results for 34,54,...,2471.
- Coefficients of 1/D_4, 1,1,1,2,3,5,8,12,19,30,...: A060961 (compositions of n into parts 1, 3, 5).
- Coefficients of 1/D_6, 1,1,1,2,3,5,8,13,21,34,55,88,...: no results.

## 2026-10-02, before run 4 (q5.py, a check of the all-q proofs in data/proofs_route1.md at q = 5)

Written after the hand proofs in proofs_route1.md and before any code for q = 5. Setup in
X-coordinates: F(X) = X + lambda, G(X) = -1/X, root 0, lambda = 2 cos(pi/5) = (1 + sqrt 5)/2, exact
arithmetic in Q(sqrt 5) (pairs of Fractions, exact sign test).

- G14 (counts, q = 5). The BFS counts a(n) for n <= 20 equal the coefficients of
  N_5/D_5 = (1 + t^2 + t^4 + t^6 - t^7)/(1 - t - t^3 - t^5 - t^7), so a(n) = a(n-1) + a(n-3) + a(n-5)
  + a(n-7) for 8 <= n <= 20 and it fails at n = 7. Refuted by one mismatch.
- G15 (words, q = 5). Every reduced string (run rule with q = 5, no three consecutive 1's among
  c_2..c_k except a run of exactly three starting at c_2 when c_1 = 0) of weight <= 20 never applies G
  at 0, takes a value with BFS rank equal to its weight, and distinct strings take distinct values.
  Every BFS point of rank <= 20 is hit. Refuted by one pole, collision, wrong rank or missed point.
- G16 (parent map and colors, q = 5). At every BFS point the parent map P(X) = X - lambda (X > 0),
  -1/X (X < 0) reaches 0 in exactly d(X) steps, and the point is reached by G at its rank iff X < 0,
  never by both F and G. Refuted by one counterexample.

### Outcomes of run 4 (2026-10-02, q5.py 20, output in data/q5_run4.txt, under 2 s)

- G14 HELD. BFS counts to n = 20: 1, 1, 2, 3, 5, 8, 13, 20, 32, 52, 83, 133, 213, 341, 546, 874, 1400,
  2242, 3590, 5749, 9206, equal to the series of N_5/D_5. The lag 1, 3, 5, 7 recurrence fails only at
  n = 7 in range.
- G15 HELD. 24514 reduced strings and 24514 BFS points, no pole, no collision, every weight equals the
  BFS rank, no point missed.
- G16 HELD. Parent-step count equals rank at all 24514 points, and the color rule holds at all of them.
- OEIS (2026-10-02, fmt=text search): q = 5 counts 1,1,2,3,5,8,13,20,32,52,83,133,213,341,546: no results.

## 2026-10-02, before run R2 (route2_checks.py, a check of the hand proofs in data/proofs_route2.md)

Written after the hand proofs of route 2 (x-coordinates, m = 2, 3, and m >= 4) and before any code
for them. IDs carry the prefix R2 so they do not clash with the route 1 IDs.

- R2-1 (the jump, m = 2, 3). For every x < 0 with d(x) <= depth - (2q - 3), d(x - 1) = d(x) + 2q - 3,
  that is + 5 for m = 2 and + 9 for m = 3. Both ranks by BFS, and again by the weight of the reduced
  string computed by the parent algorithm from p/q alone (no BFS). Refuted by one x.
- R2-2 (height). With ht(p/q) = q^2 / gcd(q, m), ht(x + 1) = ht(x) and ht(-1/(m x)) = m x^2 ht(x)
  for every rational x != 0 with |p|, q <= 200, m = 2, 3, 4, 5. Along the parent sequence of every such
  x (m = 2, 3) the value of ht right after each flip whose digit is >= 2 is strictly smaller than at
  the previous such flip, and runs of flip digits equal to 1 have length <= q - 3 (<= q - 2 for the run
  right after a first flip from x < 0). Refuted by one counterexample.
- R2-3 (free case, m = 4, 5, 6). Every negative point of the tree of rank <= 22 lies in
  (-2/m, 0), every positive point lies in some (c - 2/m, c] with c a positive integer, and neither -1
  nor 1/2 appears. Refuted by one point outside.
- R2-4 (asymptotics). With t_0 the root of D_q in (0, 1) and psi_q = 1/t_0,
  C_q = (1 + t_0) R_q(t_0) / (-D_q'(t_0)), R_q(t) = 1 + t^2 + ... + t^{2q-6}, the BFS counts satisfy
  |a(n) - C_q psi_q^n| < 1 for 15 <= n <= 28 (m = 2) and 20 <= n <= 30 (m = 3). Also every other root of
  D_q has modulus > t_0. Predicted values C_4 approx 0.7 to 0.75, C_6 approx 0.7 to 0.75 (a guess from
  C_3 = 0.702 and C_inf = phi/sqrt 5 = 0.7236). Refuted by one n outside the bound, or a second root
  of modulus <= t_0. The interval guess for C_q is a guess and may fail on its own.

## 2026-10-02, proofs (data/proofs_route1.md)

Hand proofs, no new computation beyond run 4. Status changes: G1, G2, G5, G6, G7 (m = 2, 3), G9, G13
now proved for all n (and A_q, B_q, C_q for every q >= 3). G3, G4, G12 proved for every lambda >= 2.
G10 is consistent with the proof of Theorem 6 (the descent stalls exactly at |y| = 1/2 when m = 4).

### Outcomes of run R2 (2026-10-02, route2_checks.py, output verbatim in data/route2_run.txt, under 1 min)

One fix before the run counted: the first draft let a final run of 1's (ending at 0) be one longer than
the bound. The hand proof (tail values) says the bound is the same for a final run, so the slack was
removed before the run below. The script was not otherwise changed.

```
R2-1 m=2: checked 26043 negative x of rank <= 23, failures 0
R2-1 m=3: checked 2491 negative x of rank <= 17, failures 0
R2-2 m=2: height identities on |p|, q <= 200: failures 0
R2-2 m=3: height identities on |p|, q <= 200: failures 0
R2-2 m=4: height identities on |p|, q <= 200: failures 0
R2-2 m=5: height identities on |p|, q <= 200: failures 0
R2-2 m=2: drop failures 0, run failures 0, longest closed run (first run from x<0: 2, other: 1)
R2-2 m=3: drop failures 0, run failures 0, longest closed run (first run from x<0: 4, other: 3)
R2-3 m=4: 75024 points, outside the intervals 0, -1 present False, 1/2 present False
R2-3 m=5: 75024 points, outside the intervals 0, -1 present False, 1/2 present False
R2-3 m=6: 75024 points, outside the intervals 0, -1 present False, 1/2 present False
R2-4 q=4: t0 = 0.636882916801845, psi = 1.57014731219605, C = 0.756978942343591, blue share 1/(1+psi) = 0.3890827562
      root moduli [0.636883, 1.099895, 1.099895, 1.13925, 1.13925]; smallest other modulus 1.099895 (> t0: True); max |a(n) - C psi^n| for 15 <= n <= 28: 0.105238
R2-4 q=6: t0 = 0.620374181249719, psi = 1.61193039656412, C = 0.737859436963762, blue share 1/(1+psi) = 0.3828585943
      root moduli [0.620374, 1.034326, 1.034326, 1.054637, 1.054637, 1.074723, 1.074723, 1.082969, 1.082969]; smallest other modulus 1.034326 (> t0: True); max |a(n) - C psi^n| for 20 <= n <= 30: 0.113894
```

- R2-1 HELD (m = 2 to rank 23 of x, m = 3 to rank 17 of x, by BFS and by string weight).
- R2-2 HELD. The longest runs reach the bounds q - 3 and q - 2 exactly, so the bounds are sharp in range.
- R2-3 HELD.
- R2-4 main part HELD: no other root of modulus <= t_0, and the error is below 0.12 in range. The guess
  "C_q in 0.7 to 0.75" FAILED for q = 4 (C_4 = 0.75698). It held for q = 6 (C_6 = 0.73786). The guess was
  only an interpolation and nothing depends on it.
- Unpredicted: every other root of D_4 and D_6 has modulus > 1, so the error tends to 0. A hand proof
  (Rouche on |t| = r just below 1) is in proofs_route2.md and covers every q >= 3.

## 2026-10-02, before run R2b (explicit rounding range)

- R2-5. With the partial fraction a(n) = C psi^n + sum over the other roots t_i of c_i t_i^{-n} (n >= 1),
  the bound E(n) = sum |c_i| |t_i|^{-n} is below 1/2 for every n >= 1 when q = 4, and for every
  n >= 1 when q = 6. Then a(n) is the nearest integer to C_q psi_q^n for all n >= 1. Refuted if the
  bound exceeds 1/2 at some n >= 1 (then we report the first n from which it holds).

### Outcomes of run R2b (2026-10-02, inline mpmath script, 40 digits, output verbatim in data/route2b_run.txt)

The first attempt had a bug (the dominant root was not removed from the error sum, so E(n) grew). It
was fixed by selecting the dominant root by index. Output of the fixed run:

```
q=3: t0=0.682327803828019 psi=1.46557123187677 C=0.701931067901537; min other modulus 1.2106078; sum|c_i|=0.742613; n>=1 with E(n)>=1/2: [1, 2]
   n in 1..80 where nearest integer of C psi^n != a(n) (series of N_q/D_q): []
q=4: t0=0.636882916801845 psi=1.57014731219605 C=0.756978942343591; min other modulus 1.0998945; sum|c_i|=0.889356; n>=1 with E(n)>=1/2: [1, 2, 3, 4, 5]
   n in 1..80 where nearest integer of C psi^n != a(n) (series of N_q/D_q): []
q=6: t0=0.620374181249719 psi=1.61193039656412 C=0.737859436963762; min other modulus 1.0343262; sum|c_i|=0.967375; n>=1 with E(n)>=1/2: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
   n in 1..80 where nearest integer of C psi^n != a(n) (series of N_q/D_q): []
```

- R2-5 REFUTED as stated: the triangle bound E(n) is below 1/2 only from n = 6 (q = 4) and n = 11
  (q = 6), not from n = 1. The weaker conclusion still holds. Since E is decreasing, a(n) is the nearest
  integer to C_q psi_q^n for n >= 6 (q = 4) and n >= 11 (q = 6) by the bound, and for the smaller n
  by direct comparison, so for all n >= 1 (computer-checked, floating point with 40 digits, not
  interval arithmetic). The q = 3 control gives C_3 = 0.7019310679, as in the existing paper.
- C_q agrees between two formulas: (1 + t_0) R_q(t_0)/(-D_q'(t_0)) in run R2 and the residue
  -N_q(t_0)/(t_0 D_q'(t_0)) here.

## 2026-10-02, before the A060961 offset lookup (proof repair, no new computation)

- O1 (OEIS offset). The OEIS entry A060961 has offset 0 with A060961(0) = 1, so A060961(j) is the
  coefficient of t^j in 1/D_4. Then r(n) = A060961(n - 1) + A060961(n - 3) for m = 2 (n >= 1, with
  A060961(j) = 0 for j < 0) follows from sum r(n) t^n = (t + t^3)/D_4. Refuted if the %O line of
  A060961 gives an offset other than 0 (then the identity is restated with the shift).

### Outcome of O1 (2026-10-02, https://oeis.org/search?q=id:A060961&fmt=text)

```
%S A060961 1,1,1,2,3,5,8,12,19,30,47,74,116,182,286,449,705,1107,1738,2729,4285,
%F A060961 G.f.: 1 / (1-(x+x^3+x^5)).
%O A060961 0,4
```

- O1 HELD. Offset 0, A060961(0) = 1. So r(n) = A060961(n - 1) + A060961(n - 3) for m = 2 holds for
  every n >= 1 (proved from Theorem 9 of proofs_route2.md and the g.f. on the OEIS page). Hand check
  against the BFS counts: r(1..6) = 1, 1, 2, 3, 4, 7 from both sides.

## 2026-10-02, correction to the proofs entry above (proof repair, nothing deleted)

- The line "G10 is consistent with the proof of Theorem 6 (the descent stalls exactly at |y| = 1/2
  when m = 4)" overstates. For m = 4 the set T_4 is not closed under x -> x - 1 (by Theorem 11(a) of
  proofs_route1.md it misses all of (-infinity, -1/2] in x-coordinates), so the centering step of the
  descent does not apply at all. The remark is at most an analogy and is not evidence for G10. G10 is
  covered by proofs_route2.md Theorem 10(e) and the remark after it (1/2 and -1/2 are unreachable and
  the parent map cycles between them), and by run 3.

## 2026-10-02, before verify_general.py (the paper's check script)

Written before verify_general.py exists. It re-derives every number printed in the paper by two
independent methods. Most items reproduce outcomes above. The new items are V3 to V6.

- V1 (reproduction). BFS in exact rationals and enumeration of reduced strings give the same counts as
  checks_report.md: m = 1 to rank 24, m = 2 to rank 28, m = 3 to rank 30, m = 4, 5, 6 to rank 22,
  and q = 5 (exact arithmetic in Q(sqrt 5)) to rank 20, all equal to the series of N_q/D_q
  (1/(1 - t - t^2) in the free case). Refuted by one mismatch.
- V2 (examples, by hand before the run). For m = 2: d(1/2) = 3 with digits (1, 1), d(-1) = 4,
  d(3/5) = 11 with digits (1, 2, 1, 2, 1). For every q, d(-lambda) = 2q - 4, so in x-coordinates
  d(-1) = 2, 4, 8 for m = 1, 2, 3. The rank-0 to rank-5 sets for m = 2 are {0}, {1}, {2, -1/2},
  {3, -1/4, 1/2}, {4, -1/6, 3/4, 3/2, -1}, {5, -1/8, 5/6, 7/4, -2/3, 5/2, -1/3}. Refuted by one
  wrong rank, digit string or set.
- V3 (q = 5 constants, new). psi_5 lies strictly between psi_4 = 1.57015 and psi_6 = 1.61193 (this
  is Proposition 10(c)). Guess, not implied by anything: C_5 lies in (0.73, 0.76). Refuted by a value
  outside.
- V4 (nearest integer, q = 5 new). a(n) is the nearest integer to C_q psi_q^n for 1 <= n <= 80 and
  q = 3, 4, 5, 6, checked by 40-digit arithmetic against the exact series. Refuted by one n.
- V5 (figure sizes). The m = 1 tree to rank 7 has 31 vertices and the m = 2 tree to rank 7 has 48.
- V6 (OEIS, the q = 5 counts and m = 2, 3 counts). Already "no results" above. Not re-run.

### Outcomes of verify_general.py (2026-10-02, output verbatim in data/verify_run2.txt, 280 s)

The first run had one script bug, in the free-case closed form for C (it used R = 1/(1 - t^2) where the
positive series is t/(1 - t - t^2), so R must be 1). The residue formula and a(400)/psi^400 agreed
with each other and with phi/sqrt 5. It was fixed and the run repeated. Nothing else was changed.

- V1 HELD. Every count agrees by BFS, by reduced strings and by the series, in every case listed.
  Also, at every BFS point the parent map takes exactly d(x) steps and its digit string is the reduced
  string, each point is reached at its rank by exactly one edge, and "reached by g iff negative".
- V2 HELD. d(1/2) = 3, d(-1) = 4, d(3/5) = 11 with digits (1, 2, 1, 2, 1) for m = 2, d(-1) = 2, 4, 8
  for m = 1, 2, 3, d(-lambda) = 6 at q = 5, and the rank 0 to 5 sets for m = 2 are as predicted.
  Extra: d(-3/2) = 7 = d(-1/2) + 5 for m = 2.
- V3 HELD. psi_5 = 1.60134733379, between psi_4 and psi_6. C_5 = 0.748789913636, inside the guessed
  (0.73, 0.76).
- V4 HELD for q = 3, 4, 5, 6 and the free case, 1 <= n <= 80.
- V5 HELD (31 and 48).

## 2026-10-02, before verify_general.py run 3 (table check added)

- V7. The ten-decimal values printed in Table 3 of the paper (psi_q, C_q, 1/(1 + psi_q) for
  q = 3, 4, 5, 6, infinity) equal the 40-digit values rounded to ten decimals, and the hard-coded
  rows of Table 4 (counts, n <= 20) equal the BFS counts. Refuted by one differing digit.

### Outcome of V7 (2026-10-02, verify_general.py runs 3 and 4; final output verbatim in data/verify_run4.txt)

- V7 REFUTED for one entry in run 3. The paper's table had 1/(1 + psi_3) = 0.4055855243, typed from a
  nine-digit printout plus a guessed tenth digit. The correct ten-decimal value is 0.4055855240. Every
  other entry of Table 3 and all of Table 4 matched. The paper and the script were corrected, and run 4
  (327 s) printed ALL CHECKS PASSED.

## 2026-10-02, provenance note (referee round, no computation)

- The outcomes of verify_general.py runs 1 and 2 above say "output verbatim in data/verify_run2.txt".
  That file was not kept. Its output was superseded by run 4 (data/verify_run4.txt), which repeats
  every check of run 2 and passed. The V1 to V5 outcomes above are kept as written.

## 2026-10-02, before verify_general.py run 5 (referee round)

Changes to the script before the run. The printed labels are renamed to match the compiled paper
(Theorem D, Theorem E(a),(e), Proposition "growth", Table 2), and one check is added. Nothing else.

- V8 (rounding bound, second implementation). In the growth section of verify_general.py, compute the
  partial-fraction bound E(n) = sum over the other roots t_i of |c_i| |t_i|^{-n}, with c_i the residue
  of N_q/D_q at t_i (times -1/t_i). The smallest n0 with E(n) < 1/2 for all n0 <= n <= 80 is n0 = 3, 6, 11
  for q = 3, 4, 6, as in run R2b (route2_asymp.py, which used the numerator (1 + t) t R_q instead).
  Refuted if any threshold differs.
- V9. Every other check of run 4 still passes (ALL CHECKS PASSED), since no number in the paper's
  tables changed.

### Outcomes of verify_general.py run 5 (2026-10-02, output verbatim in data/verify_run5.txt, 328 s)

```
  q = 3: E(n) < 1/2 for 3 <= n <= 80
  [ok] q = 3: rounding bound E(n) < 1/2 from n = 3 on  (3)
  q = 4: E(n) < 1/2 for 6 <= n <= 80
  [ok] q = 4: rounding bound E(n) < 1/2 from n = 6 on  (6)
  q = 6: E(n) < 1/2 for 11 <= n <= 80
  [ok] q = 6: rounding bound E(n) < 1/2 from n = 11 on  (11)
total 328s; ALL CHECKS PASSED
```

- V8 HELD. The thresholds 3, 6, 11 agree with run R2b, computed here from the residues of N_q/D_q.
- V9 HELD. ALL CHECKS PASSED, with the labels renamed to the compiled paper.
