# Route T7-B: computational check of the cycle-tree reconstruction

Base checkpoint: commit `6add913` of this repository. Date: October 24, 2026.

Inputs read in full: `00_targets.md` (this folder); `research_notes/C modal hierarchy and metastability/01_exact_cycle_checks.py`;
`research_notes/C modal hierarchy and metastability/01_cycle_conjecture_math.md` (Sections 1 and 2, formulas (1) to (36)).

Files written: this note; scripts `05_core.py` (exact machinery) and `05_run_checks.py` (driver);
archived outputs `05_reconstruction_output.txt` (full log) and `05_reconstruction_output.json` (all rows).
Run: `py -I 05_run_checks.py` in this folder (about 100 seconds, fixed seeds, deterministic).

## 0. Summary

1. The candidate criterion of (7b), "C is a cycle iff D(C) > D(C') for every nonempty proper subset C'", agrees with the
   definition of a global Freidlin and Wentzell cycle (exit probabilities, item (4)) on every matrix tested. There is no
   disagreement. Count: 2 named examples, 70 random matrices (1460 faces), 7 tied families, 4096 exhaustive 3-state matrices
   (costs in {0,..,3}), 1500 random 4-state matrices. Reversible and non-reversible cases are both included.
2. Ties do not break the criterion. Disjoint cycles of equal depth, a noncycle face with the same depth as a contained
   cycle, and fully symmetric cost matrices all occur in the tests and are classified correctly. The only thing that could
   break it is a pair of nested cycles C' strictly inside C with D(C') = D(C). None occurs in any test, and for reversible
   families it is impossible (proof in Section 4).
3. The suppression observable of (7a), as stated in `00_targets.md` (suppress the complement of F with a field -M, read off the
   height at which the exact winner leaves F, claim it equals D(F)), is NOT confirmed. The exact finite-eta winners show
   that the leaving height is not D(F) for any of the four suppression strengths tried. For strong suppression it is
   strictly larger than D(F) on every face tested (370 of 370), and it moves with the suppression strength. For weak
   suppression it equals D(F) on about two thirds of the faces (255 of 370) and differs on the rest (88 earlier, 27 later). This is an obstruction
   to the design as stated, not to the reconstruction (Section 6).
4. The prefactor routine reproduces (29) to (33) of the cycle note exactly: `a_12 = 2`, `a_123 = 2/3`, `a_124 = 2`, and the
   window winners `{1,2}`, `{1,2,3}`, `{1,2,3,4}` with endpoints `3/4` and `3/2`.

## 1. What is implemented

States `0..d-1` internally, printed as `1..d`. A cost matrix `V` has integer entries `V_ij >= 0` (zeros allowed); `q_ij = t^{V_ij}`,
`t = exp(-1/eta)`. Laurent polynomials in `t` are dictionaries with integer coefficients, so every determinant is exact.

1. Killed matrices. `A_F = -Q_F` with the full exit diagonal `q_i = sum_{j != i} q_ij` for every nonempty proper face `F`.
2. Depth by formula (24): `D(F) = nu(det A_F) - min_{i in F} nu(det A_{F minus i})`, with `det A_empty = 1`. Determinants by
   Laplace expansion with cached minors.
3. Prefactor by formula (23): the entries of `B_F = lim t^{D(F)} A_F^{-1}` are read from the leading coefficients of the
   cofactors and of `det A_F` (the code asserts that no entry has a pole of higher order than `t^{-D(F)}`, which is the content
   of (12) and (13)). `rho(B_F)` is the largest real root of the exact characteristic polynomial of the rational matrix `B_F`
   (sympy real-root isolation). `a_F = 1/rho(B_F)`.
4. Global cycles from the definition. A nonempty proper set `C` is a cycle if it is a singleton or if for all distinct `x, y`
   in `C` the exponent of `P_x(tau_{C^c} < tau_y)` is positive. The probability is the solution of the jump-chain system
   `(I - P_L) u = b` on `L = C minus {y}`, `b_z = sum_{w notin C} p_zw`, `p_zw = q_zw / q_z`. Multiplying row `z` by `q_z`
   turns this into `A_L u = r` with `r_z = sum_{w notin C} q_zw`, which is solved by Cramer's rule in polynomial arithmetic;
   `nu(u_x) = nu(numerator) - nu(det A_L)`. As a guard, the two formulations were compared in sympy rational functions for all
   42 `(C, x, y)` triples of the two named examples: 0 mismatches.
5. The criterion is evaluated from the computed `D` and compared with item 4 on every proper face.

Additional consistency checks run on every matrix (all passed, 0 failures): Theorem D, `D(F) = max{D(C): C a cycle, C subset F}`;
the singleton formula (8), `D({i}) = min_j V_ij`; for reversible matrices, the energy description (strict energy cycle by saddle
connectivity, and `D(C) = b(C) - min U` of formula (10)) agrees with item 4 on every face.

## 2. The named examples

Example (27), `U = (0,1,1,1)`, so `V = [[*,2,3,5],[1,*,2,4],[2,2,*,2],[4,4,2,*]]`.

| F | D(F) | a_F | cycle (item 4) | criterion (item 5) |
|---|---|---|---|---|
| {1} | 2 | 1 | yes | yes |
| {2} | 1 | 1 | yes | yes |
| {3} | 2 | 3 | yes | yes |
| {4} | 2 | 1 | yes | yes |
| {1,2} | 3 | 2 | yes | yes |
| {1,2,3} | 3 | 2/3 | no | no |
| {1,2,4} | 3 | 2 | no | no |
| {1,3}, {1,4}, {2,3}, {2,4} | 2 | 1, 1, 3, 1 | no | no |
| {3,4}, {1,3,4}, {2,3,4} | 2 | (2 - sqrt 2) = 0.5858... (irrational) | no | no |

The unique nonsingleton cycle is `{1,2}`, the three faces of depth 3 are `{1,2}`, `{1,2,3}`, `{1,2,4}` with prefactors `2`, `2/3`, `2`,
exactly as in (29) to (32). The lower envelope of the limiting scores `m_F + x a_F` (faces with `D = 3`, plus `E` with score `3`)
has winners `{1,2}` for `x < 3/4`, `{1,2,3}` for `3/4 < x < 3/2`, and `E` beyond: this is (33). No disagreement.

Example (34), `V = [[*,3,3],[5,*,1],[5,1,*]]`: cycles `{1}` (3), `{2}` (1), `{3}` (1), `{2,3}` (5); `D({1,2}) = D({1,3}) = 3`.
No disagreement.

## 3. Random matrices and tied families

Random matrices (seeded `random.Random(20261024)`): 4 states, 20 reversible plus 20 non-reversible; 5 states, 15 reversible plus
15 non-reversible; 70 matrices, 1460 proper faces. Reversible: `U_i` uniform in {0,..,3}, `H_ij = max(U_i, U_j) + {0..3}`,
`V_ij = H_ij - U_i`. Non-reversible: `V_ij` uniform in {0,..,4}, arbitrary. Result: 0 disagreements; all consistency checks pass.
Cycle counts per matrix (nonsingleton): 0 to 3. Of the 20 non-reversible 4-state matrices, 11 have no nonsingleton cycle, so the non-reversible evidence for the nonsingleton case comes mainly from the 5-state matrices,
F5 and F6 below, and the 1500-matrix search.

Tied families. Each row was checked for the existence of equal-depth pairs from the computed cycle list.

| Family | Type | Cycles with depths | Tie present | Disagreements |
|---|---|---|---|---|
| F1 `U = 0`, `H_12 = H_34 = 1`, other `H = 4` | rev, 4 | singletons 1; `{1,2}`, `{3,4}` both 4 | two disjoint nonsingleton cycles, equal depth 4; 8 noncycle faces share depth with a contained cycle | 0 |
| F2 `U = 0`, `H_12 = H_34 = 1`, `H_i5 = 2`, other `H = 6` | rev, 5 | singletons 1,1,1,1,2; `{1,2}`, `{3,4}` both 2 | three mutually disjoint cycles `{5}`, `{1,2}`, `{3,4}` of depth 2 | 0 |
| F3 all `H = 3`, `U = 0` | rev, 4 | four singletons, all 3 | complete symmetry; every `D` equals 3 | 0 |
| F4 variant of (27) with `H_14 = H_24 = 6` | rev, 4 | as (27) | `{1,2,3}` and `{1,2,4}` tie with `{1,2}` in depth | 0 |
| F5 `V = [[*,1,5,5],[2,*,5,5],[5,5,*,1],[5,5,2,*]]` | non-rev, 4 | singletons 1,2,1,2; `{1,2}`, `{3,4}` both 5 | two disjoint identical blocks | 0 |
| F6 searched (`random.Random(6)`, trial 83), `V` printed in the log | non-rev, 5 | `{1,5}`, `{2,4}` both 2 inside `{1,2,4,5}` (3) | two disjoint nonsingleton cycles of equal depth, nested in a deeper cycle; three singletons of depth 0 | 0 |
| F7 `U = 0`, `H_12 = H_34 = 1`, `H_13 = 3`, `H_i5 = 5`, other `H = 6` | rev, 5 | `{1,2}`, `{3,4}` both 3 inside `{1,2,3,4}` (5) | equal-depth pair nested in a deeper cycle | 0 |

Nested equal depth. The target asked for "nested cycles of equal depth if possible". None could be produced: in all
families, in the exhaustive 3-state search (4096 matrices, 0 found) and in the 1500 random 4-state matrices (half reversible, half
not), there is no pair of cycles `C' strictly inside C` with `D(C') = D(C)`. The Theorem D / formula (8) consistency checks also
passed on all 5596 search matrices. Section 4 shows why for reversible families.

## 4. The criterion, classification of failures, and a proof

Classification used when the two tests differ: "tie" if C is a cycle and `D(C) = max over proper subsets of D(C')`; "genuine failure"
otherwise (including any set the criterion calls a cycle that is not one). Count of each: none, none.

Proposition. Assume Theorem D (formula (11) of the cycle note) and

(S) strictness: if `C' strictly inside C` are both cycles, then `D(C') < D(C)`.

Then, for every nonempty proper `C`, `C` is a cycle iff `D(C) > D(C')` for every nonempty proper subset `C'`.

Proof. Singletons have no proper nonempty subsets, so both sides hold. Let `|C| >= 2`.
(Forward) Let `C` be a cycle and `C'` a nonempty proper subset. By (11), `D(C') = D(C'')` for some cycle `C''` inside `C'`
(the maximum in (11) is attained, and cycles `C''` satisfy `D(C'') = Gamma(C'')`). Then `C''` is strictly inside `C`, so (S) gives
`D(C'') < D(C)`.
(Backward) Let `C` be a noncycle. By (11) there is a cycle `C*` inside `C` with `D(C) = D(C*) = Gamma(C*)`, and `C* != C`
because `C` is not a cycle. So `C*` is a nonempty proper subset with `D(C*) = D(C)`, and the strict test fails. QED.

The backward direction needs only Theorem D. Only the forward direction uses (S).

(S) for reversible families. Use (10): `Gamma(C) = b(C) - min_C U`, where `b(C)` is the minimum saddle height `H_ij` over `i in C`,
`j notin C`, and a strict energy cycle has all its pairs connected by paths of maximal height strictly below `b(C)`. Let `C'` be
strictly inside `C`, both cycles. Take `x in C'` and `y in C minus C'`. A path from `x` to `y` of maximal height `< b(C)` exists,
and it stays in `C` (a step leaving `C` would have height `>= b(C)`). It contains an edge from `C'` to its complement of height
`< b(C)`, so `b(C') < b(C)`. Also `min_{C'} U >= min_C U`. Hence `Gamma(C') < Gamma(C)`. QED.

For non-reversible families (S) is not proved here. Evidence: no nested equal-depth pair in 35 random non-reversible matrices,
F5 and F6, the 4096 exhaustive 3-state matrices (arbitrary costs, almost all non-reversible) and about 750 random non-reversible 4-state matrices. A proof would go through the exit-time form of
`Gamma` (the mean exit time from `C` exceeds the mean exit time from `C'` by the factor `1/P(exit C before returning to C')`,
which is exponentially large for a cycle). I have not written this out, so it is a plan, not a proof.

Consequence for (7b). Ties never break the naive criterion. An explicit counterexample to the criterion does not exist for reversible
families, and none was found otherwise. What ties do affect is the observable (supports at heights, windows at critical depths):
see the next two sections.

## 5. What the computation says about (7c) and (7d)

(7c), the window of example (27). By (26), the score of a face at the critical depth `3` is `m_F + x a_F`, and `E` has score `3`.
The two endpoints are `x_1 = 3/4` from `1 + 2x = 2 + (2/3)x`, and `x_2 = 3/2` from `2 + (2/3)x = 3`.
With the dimensions known and `E` as the absolute reference (`m_E = d - 1`), `x_2` gives `a_123 = (3 - 2)/x_2 = 2/3`, and
then `x_1` gives `a_12 = a_123 + 1/x_1 = 2`. The face `{1,2,4}` never wins; its score `2 + a x` exceeds the minimum of the
other three for all `x > 0` exactly when `a >= 2/3` (the supremum of `(min - 2)/x` is `2/3`, attained on the whole middle interval),
so any `a_124 >= 2/3` gives the same winners. Hence from the two endpoints and the dimensions, `a_12 = 2` and `a_123 = 2/3`
are recoverable and `a_124 = 2` is not (only the bound `a_124 >= 2/3`). The two `a`-values were reproduced by the script from
the determinants; the endpoint algebra above is by hand.

(7d), reversibility. Items (1) to (5) use only the cost matrix, Cramer's rule and the leading coefficients; no step uses
detailed balance. Non-reversible matrices (35 random, F5, F6, and the non-reversible members of the searches) pass all checks with the
reversible ones. Reversibility enters only in the independent description (10) of `Gamma` and in the proof of (S) above.

## 6. The suppression observable of (7a)

Design tested. For a face `F` and `g` an integer, add the killing `M = t^{-g}` (field `v_k = -M`) on every state `k notin F`.
For every nonempty `G` the score is `Phi_G(h) = (|G| - 1) + t^{-h} lambda_G(v)`, `lambda_G(v)` the smallest eigenvalue of
`A_G + M diag(1_{G minus F})`. These are the exact finite-eta scores of (5) and (6), with no asymptotic simplification: the
matrices are exact rationals at `t = 10^{-16}` and again at `t = 10^{-24}`, `lambda_G` comes from the exact characteristic
polynomial by Newton iteration from 0 (monotone from the left, so it cannot skip the smallest root) at several hundred
digits, and heights are sampled at `h = j/4 + 1/8`. This part is high-precision arithmetic, not exact arithmetic. The two
values of `t` give the same winner sequences on every `(face, design)` pair (0 disagreements out of 1480), so the finite-`t`
shift of a breakpoint is below the sampling resolution. Cases: ex (27), ex (34), families F1 to F7, six random 4-state and
four random 5-state matrices; 370 faces in all. The leaving height is the first sampled height at which the winner is not
contained in `F`; the class "eq" means this is `D(F)` up to the sampling resolution (first outside sample at `D(F) + 1/8`).

| design | meaning | eq | gt (leaves later than D(F)) | lt (leaves earlier) |
|---|---|---|---|---|
| g = 2 | strong, `M = t^{-2}` | 0 | 370 | 0 |
| g = 0 | `M = 1` | 136 | 234 | 0 |
| g = -1 | `M = t` | 233 | 130 | 7 |
| g = -3 | weak, `M = t^3` | 255 | 27 | 88 |

Sorted by cycle versus noncycle, the pattern is the same (strong: all "gt" for cycles and noncycles; weak: "lt" 34 of 106 cycles,
54 of 264 noncycles). 93 of the 95 early exits (class "lt") are won by a set disjoint from `F` (an unsuppressed cycle elsewhere, or
a suppressed singleton, wins before `D(F)`); the other 2 overlap `F`. Full rows are in the archive.

Mechanism, verified on the examples. Take (27), `F = {1}` (`D(F) = 2`). The pair `G = {1,2}` has
`lambda_G = lambda_{1} - q_12 q_21 / (M + q_2 - lambda) + ...`, so `lambda_{1} - lambda_G ~ t^{V_12 + V_21 + g} = t^{3+g}`.
At heights `2 < h < 3 + g` all scores diverge (each is about `t^{-(h-2)}`), but they agree to leading order and differ by
`t^{-h} * t^{3+g} -> 0`, so the comparison is decided by the dimension term `|G| - 1` and `{1}` still wins. It is replaced only when
`t^{-h} t^{3+g}` reaches order one, at `h = 3 + g`. The script gives exactly this: leaving heights 3 (g = 0) and 5 (g = 2) for `F = {1}`.

Three structural facts explain the table.

1. Domain monotonicity. For `G'` strictly inside `G`, `lambda_G < lambda_{G'}` strictly (`A_{G'}(v)` is a principal submatrix of the
   irreducible M-matrix `A_G(v)`). Supersets of `F` that contain suppressed states have rates below `r_F` but, in the example, only by a
   gap of order `t^{3 + g}`: stronger suppression pushes the gap to higher powers and delays the exit. So the leaving
   height is `D(F)` plus a suppression-dependent shift, not `D(F)`.
2. A suppressed singleton `{k}` has rate `q_k + t^{-g}`, depth `-g`, and score about `t^{-(h+g)}`; it diverges at every `h > 0` when `g >= 0`
   and never wins there. The expectation in `00_targets.md` that the winner for `h > D(F)` is a suppressed singleton is therefore
   wrong for `g >= 0`. The winner after `D(F)` is a superset of `F` (314 of 370 faces at `g = 2`) or, in the remaining 56,
   a set that overlaps `F` without containing it.
3. With weak suppression the complement is no longer excluded: unsuppressed cycles outside `F`, and suppressed singletons with
   small `M`, can win at heights below `D(F)`, which produces the "lt" class.

So there is no single suppression strength in this family that makes the leaving height equal `D(F)` on all faces: as `g` decreases,
the class "gt" gives way to "lt", and no tested value removes both (g = -1 still has 130 "gt" and 7 "lt"). The claim (7a) as
phrased needs a different observable or a different design. Candidates that the data suggest but that I have not tested:
suppression with face-dependent strength, or reading `D(F)` from the winner sequence of the unsuppressed problem together with a
calibrated field (the route of (7c)), where a bounded-score competitor with larger dimension exists above `D(F)`. For the
unsuppressed problem the exact limiting rule (minimize `(|G|-1, -D(G), a_G)` over faces with `D(G) > h`) is the limiting
rule (26) of the cycle note; the numerical winners above are for the suppressed design only.

## 7. Limits of this check

- Finite sampling: 5675 matrices for the criterion (exact), 370 faces for the suppression observable (high precision). Neither is a proof.
- Costs are small integers (0 to 6). Zero costs are included. Real-valued costs and larger state spaces were not tried.
- The suppression observable was tested for four values of `g` with a single field value per excluded state. Other designs
  (state-dependent `M`, positive calibrated fields, partial suppression) are untested.
- The strictness (S) is proved for reversible families only.
- Archived outputs are `05_reconstruction_output.txt` and `05_reconstruction_output.json` in this folder; they are additional
  to the two files named in the write scope.

Status: obstruction found for the suppression observable of (7a) as stated in `00_targets.md` (the leaving height of the exact winner is not
`D(F)` for any tested suppression strength; mechanism in Section 6); the criterion of (7b) is proved under a stated hypothesis, strictness (S)
of depth along nested cycles, which is proved for reversible families and unproved but never violated in 5675 reversible and non-reversible tests; computation found no disagreement between the criterion and the definition.
