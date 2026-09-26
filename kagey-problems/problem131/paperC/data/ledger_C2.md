# Problem 131 Paper C, topic C2 ledger: complete-graph degeneracy, cycle cascades, two triangles, geometry of winners

Conventions. P_N = I + (T/N)Q, uniform start, n = visit counts of the N-step word, T = tau log N. "Mode type" = the support of the global maximiser of P(n), up to graph symmetry. tau_N := T/log N at a finite-N transition. First-order law assumed: cost_F(tau) = tau*lambda_F + |F| - 1. Code: scratchpad/research131/code/C2_*.py (engine C2_dp.py, checked against an exact-rational brute-force oracle and against cascade.py's cube DP, max relative difference below 1e-15).

## 2026-09-25, entry 0: disclosure of computations run before this ledger existed (not pre-registered)

These were run before the ledger file was created. None of them is a DP test of a new cell, but I list them so nothing is hidden.

1. `C2_theory_checks.py` (exact first-order algebra, 40 digits): K_d all faces for d = 2..7, cycle C_d all 2^d - 1 faces for d = 3..12, and the arc reduction for d up to 400. These verify proved statements (C2.1, C2.3) and reproduce hull.py. Outcome: all consistent, and K(d) = floor(2d/3) for 4 <= d <= 400 (this pattern was noticed in the output, not predicted; it was proved afterwards).
2. `C2_two_triangles.py` (exact first-order algebra): winner sequence of the two-triangle graph for eps in [1e-3, 1e3]. Outcome, not predicted in advance: the sequence (vertex, inner edge, triangle, whole graph) holds only for eps < eps_1 = (64 + sqrt 46)/60 = 1.179705...; for eps_1 < eps < eps_2 = 4.481078... (root of eps^3 + 2eps^2 - 19eps - 45) the 4-state face {1,2,3,4} also wins; for eps > eps_2 the triangle never wins. The pendant-triangle graph gives non-nested winners {l}, {l,h}, {h,a,b}, all (I derived this by hand before running it, but did not write it down first).
3. `C2_run_calibration.py`: reproduction of the cells already in program.md (C_4 and K_4, N = 40, 72), with T-step 0.1 and bisection to 1e-5. Outcome:
   - C_4, N=40: vertex -> adjacent pair at T = 2.53811 (tau_N 0.6880), pair -> full at T = 4.42955 (tau_N 1.2008).
   - C_4, N=72: vertex -> pair at T = 3.07756 (tau_N 0.7196), pair -> full at T = 5.43702 (tau_N 1.2713).
   - K_4, N=40: vertex -> full centre at T = 2.29217 (tau_N 0.6214); K_4, N=72: T = 2.81194 (tau_N 0.6575). No intermediate face.
   - The C_4 vertex -> pair T agrees to 5 decimals with N u/(1+2u), u = Paper B's exact edge root u_{N,2} (2.538112 and 3.077562). This is an identity, not a coincidence (see C2.md, Prop. C2.7).

## 2026-09-25, entry 1: 5-cycle C_5, unit rates, N = 40 and N = 72 (PRE-REGISTERED)

Grid: T from 0.2 to 0.999 N/2 in steps of 0.1, transitions bisected to 1e-5.
First-order theory (Thm C2.3): arcs 1, 2, 3 then the whole cycle, at tau = 1, 1+sqrt2 = 2.41421, 2+sqrt2 = 3.41421; arcs of 4 states never win.

- P1.1 (order). At both N the mode types occur in the order arc1 -> arc2 -> arc3 -> full(5), and arc4 and every non-arc support are never the mode. Kill: any other order, a missing arc3 phase, or an arc4/non-arc mode at either N.
- P1.2 (exact first transition). arc1 -> arc2 happens at the same T as on C_4, namely N u_{N,2}/(1+2u_{N,2}) = 2.538112 (N=40) and 3.077562 (N=72). Kill: |difference| > 1e-4.
- P1.3 (finite-N shift). tau_N(arc2 -> arc3) lies in [1.25, 1.75] at N=40 and [1.35, 1.80] at N=72; tau_N(arc3 -> full) lies in [1.70, 2.15] at N=40 and [1.80, 2.30] at N=72; each tau_N increases from N=40 to N=72. (Model: each extra dimension costs log N - (1/2)log T + c with c in [-0.9, -0.3].) Kill: any value outside its interval, or a decrease with N.
- P1.4 (arc-3 window). T(arc3 -> full)/T(arc2 -> arc3) lies in [1.0, 1.7] (first order: sqrt 2 = 1.414; I expect about 1.25). Kill: outside.
- P1.5 (mode positions). arc2 modes are (N/2, N/2); arc3 modes are symmetric (a, b, a), with b/N in [0.35, 0.60] (quasi-ergodic law (1/4, 1/2, 1/4)); full modes are balanced (max - min <= 1). Kill: any violation.

## 2026-09-25, entry 2: two triangles, eps = 1, N = 30 and N = 48 (PRE-REGISTERED)

States 1,2,3 | 4,5,6, bridge 3-4 with rate eps = 1 < eps_1. Grid: T from 0.2 to 0.999 N/3 (the bridge vertices have exit rate 3), step 0.1, bisection to 1e-5.
First order: vertex (tau < 1), inner edge {1,2} (1 < tau < (2+sqrt12)/4 = 1.36603), triangle {1,2,3} (1.36603 < tau < 6 + 3 sqrt3 = 11.19615), whole graph. At these N, T_max/log N is 2.94 (N=30) and 4.13 (N=48), so the whole-graph phase is out of reach at first order.

- Q2.1 (order). At both N: degree-2 vertex -> inner edge -> triangle, then no further change up to T_max. Never a support of size 4, 5 or 6, never the bridge vertex alone, never an edge or path containing the bridge. Kill: any other type appears as the mode, or the triangle phase is missing.
- Q2.2 (exact first transition). vertex -> inner edge occurs at N u_{N,2}/(1+2u_{N,2}) = 2.281928 (N=30) and 2.703532 (N=48), the same K_3 edge root. Kill: |difference| > 1e-4 (conditional on the edge phase existing).
- Q2.3 (edge window). The inner-edge phase exists at both N, with T-width between 0.1 and 1.5. Heuristic behind it: in K_3 the triangle overtakes the vertex before the edge does (a_3 < a_2), but the leak costs the triangle about e^{-T lambda_A}, which is enough to let the edge in. I am least sure about N=30. Kill: no edge phase at either N.
- Q2.4 (triangle mode). The triangle mode is (a, a, b) on {1,2,3} (or its mirror), with b < a and b/N in [0.20, 0.33). First-order value: b/N = 0.2113. Kill: b >= a or b/N outside.

## 2026-09-25, entry 3: pendant triangle, N = 72 and N = 150 (PRE-REGISTERED)

Leaf l joined to hub h; triangle {h, a, b}; unit rates. Grid: T from 0.2 to 0.999 N/3, step 0.1, bisection to 1e-5.
First order (Prop. C2.12): {l} (tau < 1+sqrt2 = 2.41421), {l,h} (to sqrt2+sqrt3 = 3.14626), {h,a,b} (to 2+sqrt3 = 3.73205), all four.

- R3.1 (non-nested phase at N=150). At N=150 the mode types are {l} -> {l,h} -> {h,a,b} -> all, so the mode leaves the leaf and sits on the triangle before spreading. Kill: the triangle phase is missing or the order differs.
- R3.2 (N=72). Same order, but the triangle window is narrow (first-order ratio 1.186), and I give it only about a 60% chance of surviving at N=72. No firm prediction; I record the outcome either way.
- R3.3. No other support type (paths {l,h,a}, pairs {h,a}, {a,b}, single a) is ever the mode at either N. Kill: any such mode.

## 2026-09-25, entry 4: K_3 (unit rates), N = 30 and N = 48 (PRE-REGISTERED)

Control for entry 2. Paper B's Cor. simplex-modes says that for large N the vertex jumps straight to the centre (a_3 < a_2).
- K3.1. At N=30 and N=48 the mode goes vertex -> full triangle directly, with no edge phase. Kill: an edge phase at either N.

## 2026-09-25, entry 5: C_4 convergence, N = 150 and N = 300 (PRE-REGISTERED)

Only T in [3, 14] is scanned, with step 0.1 and bisection to 1e-5.
Model calibrated on N=40, 72: pair -> full at T = 2(log N - (1/2) log T + c(N)), with c(N) = -0.599 - 0.483/log N (fitted to the two calibration points).
- C4.1. tau_N(pair -> full) = 1.342 at N=150 and 1.395 at N=300, within +-0.013 and +-0.015 respectively. Kill: outside these bands.
- C4.2. The vertex -> pair transition is at N u/(1+2u): 3.766790 (N=150) and 4.422331 (N=300). Kill: |difference| > 1e-4.
- C4.3. No three-state arc is ever the mode in the scanned T range. Kill: an arc3 mode.

## 2026-09-25, entry 6: structural conjecture on consecutive winners (PRE-REGISTERED, first-order algebra only)

- S1 (low confidence, about 40%). For irreducible symmetric Q, consecutive first-order winners (the faces on adjacent vertices of the lower-left hull) always intersect. Winners need not be nested; the pendant triangle already shows that. Test: `C2_random_graphs.py` draws random symmetric rate matrices, d = 4..7, with random sparsity and log-uniform rates on [1e-2, 1e2], 20000 graphs, and checks every consecutive pair on the exact hull (float64 screen, then 40-digit confirmation). Kill: one confirmed counterexample.
- S2 (high confidence, it is a theorem). Winner sizes strictly increase and winner eigenvalues strictly decrease along the sequence, every winner is connected, and the last winner is the whole state space. Kill: any violation in the same sample, which would mean a bug or a wrong proof.

### Outcome of entry 6 (2026-09-25, verbatim from out/C2_random_graphs.txt)
graphs tested: 16624; S2 violations (float screen): 0; S1 disjoint consecutive pairs (float screen): 15422. The first 5 candidates were all confirmed at 40 digits, for example d=4 with winners {2} -> {1,3,4} -> {1,2,3,4} (tau 14.7257, 14.8523).
**S1 REFUTED.** Consecutive winners can be disjoint, and in random weighted graphs this is common. The mechanism is a vertex x with small exit rate eta, followed by its complement R = V \ {x}. The Rayleigh quotient of the constant vector gives lambda_R <= eta/|R|, with equality only when every other state feeds x at the same rate. So R lies below the chord from {x} to V whenever the rates into x are unequal (worked out after the fact, see C2.md, Prop. C2.10).
**S2 survives** (0 violations in 16624 graphs), as the theorem says it should.

## 2026-09-25, entry 7: all connected unit-rate graphs, d <= 6 (PRE-REGISTERED)

- S3 (a theorem, used here as a code check). A connected unit-rate graph on d <= 6 vertices has the single-jump sequence vertex -> V iff it is complete. Kill: any other single-jump graph.
- S4 (prediction). Some connected unit-rate graph with d <= 6 has disjoint consecutive winners, and the smallest such graph has d <= 5. I expect a leaf hanging off a clique, where the leaf wins first and the clique side wins next. Kill: none for d <= 6, or the smallest example has d = 6.
- S5 (prediction). Non-nested winner sequences (some winner not contained in a later one) occur for unit-rate graphs from d = 4 on; the pendant triangle is one. Kill: none at d = 4.

### Outcome of entry 7 (2026-09-25, from out/C2_unit_graphs.txt)
(My first run used a wrong notion of "disjoint": it counted a pair as disjoint when one choice among symmetric tied minimisers was disjoint. I corrected it to "every winner of phase i is disjoint from every winner of phase i+1" (forced-disjoint), and I also count "stranded" winners, meaning some tied winner F all of whose successors miss it. The numbers below are from the corrected run.)
- d=3: 2 graphs, single-jump 1 (K_3), forced-disjoint 0, non-nested 0.
- d=4: 6 graphs, single-jump 1 (K_4), forced-disjoint 0, non-nested 1 (the paw = pendant triangle: {4} -> {1,4} -> {1,2,3} -> all at 2.414214, 3.146264, 3.732051).
- d=5: 21 graphs, single-jump 1 (K_5), forced-disjoint 2, stranded 3, non-nested 7. Examples: the house graph (square 1-2-3-4 with roof vertex 5 joined to 1,2) gives {3},{4},{5} -> {3,4} -> {1,2,5} -> all at tau = 1, 2.414214, 3.414214 (the mode jumps from the floor edge to the roof triangle). K_4 plus a vertex 5 joined to 1,2 gives {5} -> {1,2,3,4} -> all at 1.921165, 2.280776.
- d=6: 112 graphs, single-jump 1 (K_6), forced-disjoint 10, stranded 24, non-nested 55.
**S3 confirmed** (single jump iff complete, d <= 6). **S4 confirmed on its kill condition** (examples exist and the smallest has d = 5), but my guessed mechanism (a leaf off a clique) was wrong: the minimal examples are the house graph (floor edge -> roof triangle) and the complement mechanism ({5} -> V \ {5}). **S5 confirmed** (the only non-nested graph at d = 4 is the paw).

## 2026-09-25, entry 8: house graph (square 1-2-3-4 plus roof vertex 5 joined to 1 and 2), N = 40 and N = 72 (PRE-REGISTERED)

First order (exact, entry 7): degree-2 vertices {3},{4},{5} -> floor edge {3,4} (tau=1) -> roof triangle {1,2,5} (tau = 1+sqrt2) -> all (tau = 2+sqrt2). This is a forced disjoint jump: the floor edge and the roof share no state. The eigenvalues 1 and 2 - sqrt2 are the same as C_5's arc2 and arc3.
Grid: T from 0.2 to 0.999 N/3 (vertices 1 and 2 have exit rate 3), step 0.1, bisection to 1e-5. (When I wrote this, C_5 at N=40 had already given arc2->arc3 at 5.12298 and arc3->full at 6.88353, and C_5 at N=72 was still running.)
- H1 (order). At both N: degree-2 vertex -> {3,4} -> {1,2,5} -> all, and no other type ever the mode. Kill: any other order or type, or a missing roof phase.
- H2 (exact first transition, Prop. C2.7). vertex -> {3,4} at 2.538112 (N=40) and 3.077562 (N=72). Kill: |difference| > 1e-4.
- H3 (comparison with C_5). T({3,4} -> roof) and T(roof -> all) are each within +-15% of C_5's arc2 -> arc3 and arc3 -> full values at the same N. Kill: a deviation larger than 15%.

### Protocol note for entry 5 (2026-09-25)
The registered N=300 scan (T step 0.1 on [3,14]) is estimated to take more than 2 hours. I started a second, coarser run in parallel with the same predictions and kill conditions: T step 0.5 on [3,14], then bisection to 1e-5 with 7 points per pass (`C2_c4_300_coarse.py`). The coarse grid only weakens C4.3 (an arc3 phase narrower than 0.5 in T could be missed). If the fine run finishes, I will report both.

### Outcome of entry 4 (K_3), 2026-09-25, verbatim from out/C2_cell_K3.txt
```
== K3 N=30 logN=3.40120  T grid 0.20..14.90 step 0.1
   size1 -> size3 at T in [2.234094,2.234096]  tau_N=0.65686; new mode (10, 10, 10)
   distinct mode types on grid, in order: ['size1', 'size3']
== K3 N=48 logN=3.87120  T grid 0.20..23.90 step 0.1
   size1 -> size3 at T in [2.636023,2.636024]  tau_N=0.68093; new mode (16, 16, 16)
   distinct mode types on grid, in order: ['size1', 'size3']
```
**K3.1 confirmed** at both N: the mode jumps from a vertex straight to the centre, with no edge phase. Note that the K_3 centre overtakes the vertex (T = 2.2341 at N=30) before the edge would (2.2819, the Paper B edge root).

## 2026-09-25, entry 9: cycle arc2 -> arc3 crossing at large N via locality (PRE-REGISTERED)

By Prop. C2.8 (checked exactly at N=40: the killed-path computation gives 5.1229815, and the C_5 DP bracket is [5.122981, 5.122983]; `out/C2_locality_check.txt`), the arc2 -> arc3 crossing on any C_d (d >= 5) depends only on the paths P_2 and P_3 with diagonal 2. It can therefore be computed with 2- and 3-state killed DPs at large N. Cells: N = 300, 1000, 3000 (`C2_arc_large_N.py`, Brent root of log(best arc3 ratio) - log(best arc2 ratio)).
Model: T(1 - lambda_3) = log N - (1/2) log T + c(N), with c(N) = -0.620 - 0.48/log N (N=40 value -0.750; drift slope borrowed from C_4).
- A9.1. tau_N(arc2 -> arc3) = 1.643 (N=300), 1.739 (N=1000), 1.806 (N=3000), each within +-0.02. First order: 2.414. Kill: any value outside its band.
- A9.2. tau_N increases with N and stays below 2.414 at N=3000. Kill: a decrease, or a value >= 2.414.
(2026-09-25, later) I stopped the fine-grid N=300 run before it printed anything, to free the machine; the coarse run stands in for it. Entry 5 at N=300 is therefore reported from the coarse run only.

## 2026-09-25, entry 10: path graph P_d, unit rates, first-order winners (PRE-REGISTERED, exact algebra only)

Derivation (hand): an end-arc of k states has -Q = tridiag with diagonal (1,2,...,2), so lambda'_k = 2 - 2cos(pi/(2k+1)) = lambda_{2k} in cycle notation. Interior arcs and disconnected faces are dominated. So only end-arcs and P_d compete, and the cycle argument goes through with lambda'_k.
- PA1 (guess, by analogy with the cycle). The winners are the end-arcs of sizes 1, ..., floor(2d/3), then P_d. Kill: any d in 4..300 where the largest winning end-arc size differs from floor(2d/3) (checked by the arc-reduction formula, and by brute force over all faces for d <= 10).
### Outcome of entry 10 (verbatim from out/C2_path.txt)
P_3..P_10: the winners (end-arc sizes, then d) match brute force over all faces, e.g. P_4: [1, 2]+[4] tau_full=5.236067977, P_10: [1..6]+[10] tau_full=68.82742907; no degenerate ties. "d in 4..300 with K'(d) != floor(2d/3): [] count 0".
**PA1 confirmed.** Afterwards I proved it (C2.md, Cor. C2.6'), with the same D-bounds argument as for the cycle; the bounds now hold from k = 2 on. The first transition on a path is at the golden ratio (1+sqrt5)/2.

### Outcome of entry 1 (C_5), 2026-09-25, verbatim from out/C2_cell_C5.txt
```
== C5 N=40 logN=3.68888  T grid 0.20..19.90 step 0.1
   arc1 -> arc2 at T in [2.538112,2.538113]  tau_N=0.68804; new mode (20, 20, 0, 0, 0)
   arc2 -> arc3 at T in [5.122981,5.122983]  tau_N=1.38876; new mode (9, 22, 9, 0, 0)
   arc3 -> full(5) at T in [6.883528,6.883530]  tau_N=1.86602; new mode (8, 8, 8, 8, 8)
   phase arc3: mode comps seen: [(9, 21, 10, 0, 0), (9, 22, 9, 0, 0), (10, 21, 9, 0, 0), (22, 9, 0, 0, 9)]
   distinct mode types on grid, in order: ['arc1', 'arc2', 'arc3', 'full(5)']
== C5 N=72 logN=4.27667  T grid 0.20..35.90 step 0.1
   arc1 -> arc2 at T in [3.077562,3.077563]  tau_N=0.71962; new mode (36, 36, 0, 0, 0)
   arc2 -> arc3 at T in [6.389394,6.389395]  tau_N=1.49401; new mode (16, 39, 17, 0, 0)
   arc3 -> full(5) at T in [8.601750,8.601752]  tau_N=2.01132; new mode (14, 14, 14, 15, 15)
   phase arc3: mode comps seen: [(16, 39, 17, 0, 0), (17, 0, 0, 17, 38), (17, 38, 17, 0, 0), (17, 39, 16, 0, 0), (39, 17, 0, 0, 16)]
   phase full(5): mode comps seen: [(14, 14, 14, 15, 15), ... rotations]
   distinct mode types on grid, in order: ['arc1', 'arc2', 'arc3', 'full(5)']
```
- P1.1 **confirmed** at both N: arc1 -> arc2 -> arc3 -> full(5); no arc4 or non-arc mode.
- P1.2 **confirmed**: 2.538112 and 3.077562, identical to C_4.
- P1.3 **confirmed**. tau_N(arc2->arc3) = 1.389 (N=40, band [1.25,1.75]) and 1.494 (N=72, band [1.35,1.80]); tau_N(arc3->full) = 1.866 ([1.70,2.15]) and 2.011 ([1.80,2.30]). Both increase with N.
- P1.4 **confirmed**: the window ratio is 1.344 (N=40) and 1.346 (N=72), inside [1.0,1.7].
- P1.5 **partly killed.** b/N = 0.525-0.55 (N=40) and 0.528-0.542 (N=72), inside [0.35,0.60], and arc2 and full modes are as predicted. But the arc3 mode is not always symmetric: (9,21,10) and (16,39,17) occur, one unit off (a,b,a) when N - b is odd. The literal "(a,b,a)" clause is refuted, and I should have written "symmetric up to lattice parity".

### Outcome of entry 3 (paw / pendant triangle), 2026-09-25, verbatim from out/C2_cell_pend.txt
```
== pendant triangle N=72 logN=4.27667
   {l} -> {l,h} at T in [5.665164,5.665166]  tau_N=1.32467; new mode (65, 7, 0, 0)
   {l,h} -> {h,a,b} at T in [7.973793,7.973795]  tau_N=1.86449; new mode (0, 14, 29, 29)
   {h,a,b} -> all4 at T in [10.662181,10.662183]  tau_N=2.49311; new mode (17, 19, 18, 18)
   distinct mode types on grid, in order: ['{l}', '{l,h}', '{h,a,b}', 'all4']
== pendant triangle N=150 logN=5.01064
   {l} -> {l,h} at T in [7.276967,7.276968]  tau_N=1.45230; new mode (134, 16, 0, 0)
   {l,h} -> {h,a,b} at T in [10.085275,10.085277]  tau_N=2.01277; new mode (0, 30, 60, 60)
   {h,a,b} -> all4 at T in [13.057977,13.057979]  tau_N=2.60605; new mode (35, 39, 38, 38)
   distinct mode types on grid, in order: ['{l}', '{l,h}', '{h,a,b}', 'all4']
```
- R3.1 **confirmed**: the non-nested triangle phase is present at N=150 (window ratio 1.295, first order 1.186).
- R3.2: the triangle phase **is present** at N=72 too (ratio 1.337). I had given it about 60%.
- R3.3 **confirmed**: no other support type came within 0.05 decades of the mode at either N.

### Outcome of entry 5 at N=150 (C_4), verbatim from out/C2_cell_C4big.txt
```
== C4 N=150 logN=5.01064  T grid 3.00..13.90 step 0.1
   arc1 -> arc2 at T in [3.766789,3.766791]  tau_N=0.75176; new mode (75, 75, 0, 0)
   arc2 -> full(4) at T in [6.739153,6.739154]  tau_N=1.34497; new mode (38, 38, 37, 37)
   distinct mode types on grid, in order: ['arc1', 'arc2', 'full(4)']
```
- C4.1 at N=150 **confirmed**: tau_N = 1.34497, inside 1.342 +- 0.013.
- C4.2 at N=150 **confirmed**: 3.766790 (bracket [3.766789, 3.766791]).
- C4.3 at N=150 **confirmed**: no arc3 mode.

### Outcome of entry 9 (arc2 -> arc3 at large N), verbatim from out/C2_arc_large_N.txt
```
N=300: arc2->arc3 crossing T=9.598481 tau_N=1.68283; arc3 mode (71, 159, 70), arc2 mode (150, 150); arc2/vertex log ratio there 5.965
N=1000: arc2->arc3 crossing T=12.335774 tau_N=1.78579; arc3 mode (237, 525, 238), arc2 mode (500, 500); arc2/vertex log ratio there 7.374
```
- A9.1 **REFUTED** at both N it reached: predicted 1.643 +- 0.02 and 1.739 +- 0.02, observed 1.683 and 1.786. The fitted constant c = Pi - (log N - (1/2)log T) drifts upward faster than the C_4-borrowed slope: -0.750 (N=40), -0.703 (N=72), -0.597 (N=300), -0.54 (N=1000). N=3000 was **not run**: at 450 s per N=1000 root it would take about 3.4 h, so I stopped it. A9.1 at N=3000 is untested.
- A9.2 **confirmed** where tested: tau_N rises 1.389, 1.494, 1.683, 1.786 (N = 40, 72, 300, 1000) and stays below 2.414.

## 2026-09-25, entry 11: is the Theta_1 N=30 "triangle+bridge" mode a discrete-time artefact? (PRE-REGISTERED)

Hypothesis: the mode (11,11,7,1,0,0) at T >= 9.52 comes from P_33 = 1 - 3h being close to 0 (h near 1/3). It does not come from the slow-switching regime that (FS) describes.
- X11.1. Replace P = I + (T/N)Q by P = exp((T/N)Q), which has the same continuous-time limit but P_33 >= e^{-3h} > 0.22. At N=30, eps=1, on the same grid T in [0.2, 9.9] step 0.1, the mode types are then deg2-vertex -> inner-edge -> triangle, and triangle+bridge never appears. Kill: triangle+bridge (or any size >= 4 type) is the mode anywhere on the grid.

### Outcome of entry 8 (house graph), verbatim from out/C2_cell_house.txt
```
== house N=40 logN=3.68888  T grid 0.20..13.30 step 0.1
   deg2-floor-vertex -> floor-edge at T in [2.538112,2.538113]  tau_N=0.68804; new mode (0, 0, 20, 20, 0)
   floor-edge -> roof-triangle at T in [4.290617,4.290619]  tau_N=1.16312; new mode (9, 9, 0, 0, 22)
   roof-triangle -> all5 at T in [6.946777,6.946779]  tau_N=1.88317; new mode (8, 8, 8, 8, 8)
   distinct mode types on grid, in order: ['deg2-floor-vertex', 'floor-edge', 'roof-triangle', 'all5']
== house N=72 logN=4.27667  T grid 0.20..23.90 step 0.1
   deg2-floor-vertex -> floor-edge at T in [3.077562,3.077563]  tau_N=0.71962; new mode (0, 0, 36, 36, 0)
   floor-edge -> roof-triangle at T in [5.511197,5.511198]  tau_N=1.28867; new mode (17, 17, 0, 0, 38)
   roof-triangle -> all5 at T in [8.649695,8.649696]  tau_N=2.02253; new mode (15, 15, 14, 14, 14)
   distinct mode types on grid, in order: ['deg2-floor-vertex', 'floor-edge', 'roof-triangle', 'all5']
```
(The degree-2 floor vertex and the roof vertex tie exactly at small T; the mode type is reported as the floor vertex by tie order. Both are first-order winners.)
- H1 **confirmed** at both N: floor edge -> roof triangle (a forced disjoint jump), then all.
- H2 **confirmed**: 2.538112 and 3.077562.
- H3: floor -> roof versus C_5 arc2 -> arc3 is -16.2% at N=40 (4.2906 vs 5.1230) and -13.7% at N=72 (5.5112 vs 6.3894). Roof -> all versus C_5 arc3 -> full is +0.9% (6.9468 vs 6.8835) and +0.6% (8.6497 vs 8.6018). **H3 is killed at N=40** (outside +-15%) and holds at N=72. The roof triangle is favoured by its second-order constant, since its apex has no outside edge.

### Outcome of entry 11, verbatim from out/C2_expchain.txt
```
== two-triangles eps=1, P=expm(hQ) N=30 logN=3.40120  T grid 0.20..9.90 step 0.1
   deg2-vertex -> inner-edge at T in [2.592928,2.592929]  tau_N=0.76236; new mode (15, 15, 0, 0, 0, 0)
   inner-edge -> triangle at T in [3.179729,3.179730]  tau_N=0.93489; new mode (0, 0, 0, 5, 12, 13)
   phase triangle: grid T 3.20..9.90; mode comps seen: [(0,0,0,5,12,13), (0,0,0,5,13,12), (0,0,0,6,12,12), (12,12,6,0,0,0), (12,13,5,0,0,0), (13,12,5,0,0,0)]
   distinct mode types on grid, in order: ['deg2-vertex', 'inner-edge', 'triangle']
```
**X11.1 confirmed.** With P = exp(hQ) the triangle+bridge mode never appears up to T = 9.9, so the N=30 anomaly of entry 2 is a feature of the linear discretisation P = I + hQ near h = 1/3. The exponential chain's thresholds are also shifted: vertex -> edge at 2.5929 against 2.2819, and edge -> triangle at 3.1797 against 2.6153. So the choice of discretisation moves finite-N thresholds by 10-20%, which is another finite-N effect that first order ignores.

### Outcome of entry 2 (two triangles, eps=1), verbatim from out/C2_cell_tri.txt
```
== two-triangles eps=1 N=30 logN=3.40120  T grid 0.20..9.90 step 0.1
   deg2-vertex -> inner-edge at T in [2.281927,2.281929]  tau_N=0.67092; new mode (15, 15, 0, 0, 0, 0)
   inner-edge -> triangle at T in [2.615251,2.615253]  tau_N=0.76892; new mode (12, 13, 5, 0, 0, 0)
   triangle -> triangle+bridge at T in [9.523221,9.523222]  tau_N=2.79996; new mode (11, 11, 7, 1, 0, 0)
   phase triangle: mode comps seen: [(0,0,0,5,13,12), (0,0,0,6,12,12), (12,12,6,0,0,0), (12,13,5,0,0,0)]
   distinct mode types on grid, in order: ['deg2-vertex', 'inner-edge', 'triangle', 'triangle+bridge']
== two-triangles eps=1 N=48 logN=3.87120  T grid 0.20..15.90 step 0.1
   deg2-vertex -> inner-edge at T in [2.703531,2.703532]  tau_N=0.69837; new mode (24, 24, 0, 0, 0, 0)
   inner-edge -> triangle at T in [3.143411,3.143413]  tau_N=0.81200; new mode (20, 20, 8, 0, 0, 0)
   triangle -> triangle+bridge at T in [12.702495,12.702496]  tau_N=3.28128; new mode (0, 0, 1, 11, 18, 18)
   phase triangle: mode comps seen: [(0,0,0,8,20,20), (0,0,0,9,19,20), (0,0,0,9,20,19), (0,0,0,10,19,19), (19,19,10,0,0,0), (19,20,9,0,0,0)] ...
   distinct mode types on grid, in order: ['deg2-vertex', 'inner-edge', 'triangle', 'triangle+bridge']
```
- Q2.1 **KILLED at both N.** vertex -> inner edge -> triangle happens as predicted, but then a "triangle + exactly one visit to the far bridge vertex" mode takes over: at T >= 9.5232 (h = 0.317) for N=30 and at T >= 12.7025 (h = 0.265, P_33 = 0.21) for N=48. It is not a first-order phase (first order never selects {1,2,3,4} at eps=1). Its onset tau_N rises from 2.80 to 3.28 between the two N, and with P = exp(hQ) it is absent at N=30 up to T = 9.9 (entry 11). My reading, which is heuristic: a single-step excursion 3 -> 4 -> 3 has relative weight of order (eps h)^2 times the O(N) positions it can occupy, that is O(T^2/N). That vanishes as N grows at fixed tau, but here T^2/N is about 3. So this is a finite-N effect of the regime where h is not small.
- Q2.2 **confirmed**: 2.281928 and 2.703532, the K_3 edge root.
- Q2.3 **confirmed**: edge-window widths are 0.333 (N=30) and 0.440 (N=48), inside [0.1, 1.5]. First-order widths are 0.366 log N = 1.245 and 1.417.
- Q2.4 **KILLED**: the triangle mode has b/N = 5/30 = 0.167 (N=30) and 8/48 = 0.167 (N=48), below the predicted floor 0.20 (first order 0.211). a is not always equal to a', for example (12,13,5) and (19,20,9), a parity effect.
(2026-09-25, 20:19) The coarse N=300 run had printed its grid (arc1 on T = 3.0..4.0, arc2 on 4.5..7.5, full(4) from 8.0, no arc3), but after an hour it was still bisecting the first bracket. I stopped it and started `C2_c4_300_focus.py`. That script checks C4.2 with two evaluations at 4.422331 -+ 1e-4 and bisects only the pair -> full bracket (7.5, 8.0) to 2e-5. The predictions and kill conditions are unchanged.
(2026-09-25, 20:30) Focused run, first output: "C4.2 check: [(4.422231, 'arc1', (300, 0, 0, 0)), (4.422431, 'arc2', (150, 150, 0, 0))]", so **C4.2 is confirmed at N=300** (the transition lies within 1e-4 of 4.422331). Because the machine is heavily loaded, each 7-point pass takes about 15 min, so I replaced the pair -> full bisection by a verbose version (`C2_c4_300_bisect.py`). It evaluates the kill-band edges first and prints every pass.

### Outcome of entry 5 at N=300, verbatim from out/C2_cell_C4_300_bisect.txt (and the coarse grid)
```
grid (step 0.5): arc1 at T=3.0..4.0, arc2 at 4.5..7.5, full(4) from 8.0 on; no arc3
C4.2 check: [(4.422231, 'arc1', (300, 0, 0, 0)), (4.422431, 'arc2', (150, 150, 0, 0))]
band check: [(7.87122, 'arc2', (150, 150, 0, 0)), (7.95678, 'arc2', (150, 150, 0, 0)), (8.04233, 'full(4)', (75, 75, 75, 75))]
```
- C4.1 at N=300 **confirmed**: pair -> full lies in T in (7.9568, 8.0423), that is tau_N in (1.395, 1.410), inside the predicted 1.395 +- 0.015 (upper half).
- C4.2 at N=300 **confirmed**.
- C4.3 at N=300 **confirmed at coarse resolution**: no arc3 on the step-0.5 grid.
(2026-09-25, 20:45) I stopped the N=300 bisection after the band check. Each further pass took more than 10 min on the loaded machine, and the band check already settles C4.1. The final reported bracket is T in (7.9568, 8.0423), that is tau_N in (1.395, 1.410).

## Summary of this ledger (2026-09-25)
Confirmed: P1.1-P1.4, Q2.2, Q2.3, R3.1, R3.3, K3.1, C4.1-C4.3 (N=150, 300), S2, S3, S4 (kill condition), S5, H1, H2, A9.2, PA1, X11.1.
Refuted or killed: P1.5 (literal symmetry clause, a parity effect), Q2.1 (boundary mode at large h, both N), Q2.4 (bridge share 0.167 < 0.20), H3 at N=40 (-16.2% versus +-15%), A9.1 at N=300 and 1000 (c drifts faster than modelled), S1 (consecutive winners can be disjoint).
Not tested: A9.1 at N=3000 (too slow).

## 2026-09-26, erratum and external cells (appended in the C2 repair; the entries above are left as written)

Nothing was run for this entry. It corrects cross-references and records results from the independent verifier's pre-registered ledger (`scratchpad/research131/code/C2_rigor_ledger.md`).

- **Cross-reference errata.** Entry 0 item 3 and entry 8 (H2) cite locality as "Prop. C2.7"; in C2.md it is **Prop. C2.8**. The S1 outcome cites the complement mechanism as "Prop. C2.10"; it is **Prop. C2.9** (the bound itself is C2.5(a)). Entry 3 cites the paw's first-order sequence as "Prop. C2.12"; it is **Prop. C2.10**.
- **Definition behind the "non-nested" counts in entry 7.** The pre-registered wording of S5 says "some winner not contained in a later one". The count reported (d=4: 1, d=5: 7, d=6: 55) comes from `C2_unit_graphs.py`, which uses a stronger notion: phases i < j exist such that no minimiser of phase i is contained in any minimiser of phase j. The verifier's counts under two weaker notions are consistent with this: 8/58 for "no inclusion chain" and 9/68 for "some winner not contained in any next-phase winner". At d=4 the paw is the only example under all three notions, so S5 stands. The 7/55 counts are not independently reproduced.
- **Units in entry 0 item 3 and C2.md Prop. C2.8.** The parenthetical values 2.538112 and 3.077562 (and in C2.8 also 2.281928, ...) are transition values T = N u/(1+2u), not u_{N,2}. The roots themselves are u = 0.072676 and 0.046740 (0.089712 at N=30).
- **External cell, P_4 (verifier V2, V5, pre-registered there).** First order (C2.6') predicts leaf -> end edge -> P_4, with no 3-state phase. The exact law gives leaf -> end edge -> end-arc of 3 -> P_4 at N = 40, 72, 150, 300. The arc-3 windows are T in (9.381, 12.502), (12.176, 15.142), (15.804, 18.443), (19.292, 21.590), with ratios 1.333, 1.244, 1.167, 1.119. A second implementation confirms N = 40 and 72. **This refutes the general reading of C2.12**, that first order gets the order of phases right at feasible N. See C2.md Section 7.1.
- **External cell, C_6 at N = 40 (verifier V3).** Arcs 1-4 then C_6, at T = 2.538112, 5.122981, 8.569684, 9.817136, as first order predicts.
- **Q2.1 mechanism.** The ledger's reading ("T^2/N about 3") is superseded. The boundary mode is driven by P_33 = 1 - 3h being small, near T_max: an excursion 3->4->3 has weight (h/P_33)^2 = 64 at N=30, T=9.6 (verifier V4.3). See C2.md 7.5.
