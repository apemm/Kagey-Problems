# Research log: general formula / threshold / squares (2026-11-06 night)

## Facts in hand
- f(h,m) = m + q_h for m >= M_h (alternating seas, Lean-checked). Thresholds m_h: m_3=2(?),
  m_4=6, m_5=8, m_6=15, m_7 <= 22. f(8,8) >= 17 (so first n with f(n,n) > 2n is 8).
- Dangerous gaps: black points at displacement (dx,dy) are the diagonal of a rectangle whose other
  diagonal is vertical iff dx^2+dy^2 = L^2; D(dy) = {(dy^2/k - k)/2}. Legs 1, 2 never occur.
- A double {a,b} with b-a an odd hypotenuse (5,13,17,...) is itself the diagonal of tilted rectangles
  (4u^2 + (2k+1)^2 = (b-a)^2) whose other corners sit at column distance u (u=2 for 3-4-5).

## Regular spacing test (doubles every g+1 columns, seas any row, SAT)
- h=6: g=1 UNSAT, g=2 SAT (w=27), g=3 SAT.
- h=7: g=1 UNSAT, g=2 SAT (w=36).
- h=8: running.
=> conjecture: g=2 works for all h, giving m_h <= 3 q_h - 2 + O(1) = O(h^2).

## 2026-11-07 ~01:10
- Seven rows: SAT at widths 21, 22, 23 (and 24-28, collar from 28) => f(7,m) = m+12 for all m >= 21 (m_7 <= 21).
  Width 20 still running (partitions 246, 147).
- Regular spacing: g=2 (doubles every 3rd column), free seas: SAT for h=6,7,8. g=1 UNSAT for h=6,7.
  With built-in W_h padding (collar-extendable): SAT for h=6,7 at g=2.
- Boundary-only seas (rows 1, h): g=3 SAT for h=6,7,8; g=2 UNSAT for h=7. h=8 g=3 solution: one long row-1 sea
  holding 10 edges at spacing 4, then a row-8 sea holding the 5 edges with large rows.
- Lemma (spacing 4 kills primitive horizontal traps): u=(p-dx,1), d=(p,c), primitive (dx,dy,L), dy=c-1 even =>
  shown columns p-t, p+s, s t = (dy/2)^2, gcd=1, s+t=L odd => the even one of s,t is = 0 mod 4 => lands on a
  double column (row 1 not black there) => no rival.
- Reflection obstruction (interior star seas die), parity form of vertical mechanism (dx even, dy odd, odd hyp).
- COUNTS: sea-subshift entropy = growth rate of a_h(m). h=4 transfer-graph Perron root 3.351996777310375 equals the
  paper's rho_4 to all 12 digits; h=3 gives 3. Other 4-row partitions: {12|34} 2.931997, {14|23} 2.856928.
  Conjecture: a_h(m) ~ c_h m^{q_h} rho_h^m, rho_h = entropy of the sea shift for the best balanced partition.
  h=5: A401225 counts, geometric extrapolation of m^6-corrected ratios -> ~3.556; sea DP partial ~3.54.
- Cyclomatic profile c(h,m) = f - (h+m-1) (symmetric): c>=1 iff min>=4 and h+m>=10; c>=2 iff min>=5, max>=8;
  six rows: c = 1,2,3,4 from widths 4, 8, 12, 15. Cap floor((h-2)^2/4).

## 2026-11-07 ~02:20  COUNT FORMULA CONFIRMED (h=4, constant included)
- rho_5 = 3.5438756463 (sea graph); the paper's own five-row counter with doubles fixed near the left gives
  ratios -> 3.5438756623 at m=58 (agreement ~8 digits). (Counter overflows a packed slot past m~58.)
- Product formula a_h(m) ~ B * prod_e kappa_e * m^{q_h} * rho^m.  h=4: B = 1.66850499788,
  kappa_12 = kappa_34 = kappa_14 = 0.091516, kappa_23 = 0.068333 (one-double marked counts, pair set fixed to
  all of K_{A,B}); predicted c_4 = 8.16109707754e-5; paper encloses c_4 in [8.1610970775, 8.1610970776]e-5.
- Windowed upper bounds rho_K for h=5: K=6: 3.55250, 7: 3.54902, 8: 3.54731, 9: 3.54473, 11 (exact) 3.54388.
- Structured constant-spacing families: even h split (row-1 sea then row-h sea), odd h periodic "h D 1 1";
  diagonal staircase blocks L_d = {{a,a+d}} with alternating directions (h=6 spacing 4, h=7 spacing 3).

## 2026-11-07 ~02:10
- f(8,m) = m+16 for all m >= 46 (padded spacing-3 board, free seas; 72 columns with W_8=13 row-1 padding each
  side; verify_narrow and fastcheck both valid). Core: 25,3,3,36,7,3,47,7,7,58,8,8,78,8,7,27,8,7,67,6,6,56,5,5,45,
  4,4,34,3,2,23,3,4,38,1,1,16,2,2,14,1,1,18,8,4,12.
- c_5 ~ 1.3208e-8 from the counter with the 6 doubles fixed 20 apart (N/(6! rho^m)); same method on h=4 gives
  8.160607e-5 vs exact 8.161097e-5 (finite-spacing error ~6e-5). a_5/(m^6 rho^m) ~ c_5 (1 - 15.2/m) fits m=31..44.
- Counter slot width SW=80 overflows near 1e24 (m ~ 41+ for a_5 totals); scratch copy with SW=256 used.
- rho_6 windowed upper bounds: K=8 3.62532, K=9 3.60033 (K=10 running). Guess rho_6 ~ 3.58-3.59.
- h=8: periodic boundary pattern UNSAT, diag blocks spacing 3 UNSAT; split (row-1 then row-8 seas) SAT.

## PRE-REGISTERED 2026-11-07 02:15 (before the results of the runs named below were read)
Conjecture (strip formula): for 4 <= h <= m, f(h,m) = h + m - 1 + min( floor((h-2)^2/4), floor((m - 3 + [h odd])/3) ),
with exceptions near squares (known: (6,8) gives 15 not 14; (8,8) >= 17 not 16).
Predictions:
 P1 m_7 = 20: 7x20 has an m+12 blackout (runs rows_sat 7 20 {246,147} going since ~00:30).
 P2 m_8 = 30: 8x30 has an m+16 blackout (rows_sat 8 30 1357 going since ~00:30); 8x29 does not.
 P3 seven rows, e=11: SAT at width 17, not at 16 (profile runs going).
 P4 f(7,11) >= 18 (c=3 at width 11): K_{3,4}-subgraph doubles are UNSAT there, so it must use another
    triangle-free graph (K_{2,5} subgraph or partition 147/135/...). Launching those now.
 P5 thresholds m_h = 3 floor((h-2)^2/4) + 3 - [h odd]: 6, 8, 15, 20, 30, 38, 51 (h = 4..10).

## Outcomes (02:15)
- P4 REFUTED for doubles-only structures: 7x11 with 9 distinct doubles UNSAT for partitions 246, 135, 147
  (K_{3,4}) and 16, 17 (K_{2,5}). f(7,11) >= 18 would need triples or a non-bipartite triangle-free graph.
- P3 half confirmed so far: e=11 at width 16 UNSAT (K_{3,4} doubles); width 17 pending.
- Partition entropies h=5 (K=8 windows): {135}|{24} 3.5473, {13} 3.4055, {12} 3.3294, {14} 3.2965, {15} 3.1654,
  {23} 3.1376: the parity partition dominates, as on four rows.
- Poisson heuristic lambda_h (violations/column, uniform random sea): 0.262, 0.453, 0.725, 0.883, 1.147, 1.505,
  1.761 for h = 4,5,6,7,8,10,12; true log(h/rho_h) ~ 0.7 lambda_h for h = 4,5,6.

## 02:20
- SMC estimates of rho_h (pop 300/200, 120/100 steps; calibration h=4: 3.344 vs 3.352, h=5: 3.560 vs 3.544):
  h=6 3.585, h=7 3.783, h=8 3.732, h=9 3.797, h=10 3.866, h=11 4.122 (h=12 running). Increasing, odd h above
  even neighbours. So no plateau: the Poisson heuristic's clumping factor is not constant.
- 7x20 with e=11 (K_{3,4} doubles) SAT. 8x42 lost (solver worker died during a memory squeeze).
- Memory ran out (0.2 GB free of 31.4); the system stopped two finished sweeps and a watcher; I stopped 8 low-priority SAT runs (diagonal blocks h=8,9; fixed-pattern h=8; one
  h=9 pattern; h=9 boundary-only; two leftover order sweeps). Free memory back to 11.8 GB.
- rho_12 ~ 4.149 (SMC). Sequence h=3..12: 3, 3.352, 3.544, 3.585, 3.783, 3.732, 3.797, 3.866, 4.122, 4.149.
- Five-row recount with 256-bit slots: SW=80 values were correct through m=44. a_5(m)/(c_5 m^6 rho_5^m) =
  0.617 (40), 0.655 (44), 0.6872 (48) vs 1 - 15/m = 0.625, 0.659, 0.6875: a_5(m) ~ 1.3208e-8 m^5 (m-15) rho_5^m.

## 02:45 analytic
- Lemma (Pythagorean exclusion): black p, p+(4,+-3) with exposed (x+2, r-1), (x+2, r+4) in grid, white, and
  {r-1, r+4} in F => invalid. General: (dx,dy) dx even, dy odd, L odd. For optima F = K_{odd,even} always.
  Explains staircase failure at h >= 6 and boundary immunity.
- Adjacent disjoint non-parallel doubles are fine locally (SAT: every pair of K_{3,3} edges fits adjacent in a
  6-row board); density limits are global (accumulated Diophantine coincidences).
- Random-order heuristic: vertical coincidences ~ (2/pi) log h per double (only within h/4 slots); horizontal
  ~ c log^2 h / s per double => random orders need spacing ~ log^2 h; Theta(h^2) needs arithmetic cancellation.
- lambda_h ~ 2 N_h / h^3, N_h = sum_{b+d<h} tau(bd)(h-b-d) ~ h^3 log^2 h => predicts rho_h peaks then falls to
  rho_inf >= 2 (even h: words over rows {1,h}).
- rho_11 (corrected averaging) ~ 4.20; rho_9 3.820, rho_10 3.911.
- Dead end: lattice x = alpha y mod 3^K kills all Pythagorean vectors but a double's two points cannot both lie
  in it once 3^K > h; mod-3/mod-4 obstructions alone cannot cover >3 doubles within range.
- 03:20 h=9 periodic boundary pattern (spacing 4): UNSAT.
- 03:25 alternating gaps 1,2 (double density 2/5), free seas: SAT for h=6 (w=23) and h=7 (w=30). So 1/3 is not a packing limit; thresholds use runs (q/m = 0.6 at h=6, >= 0.57 at h=7).

## 03:30 Square upper bound (analytic)
- Completion budget: black right angles (A,B,C), completion X=A+C-B in grid, number <= n^2 - N + 4 (each white X completes at most one rectangle with three black corners; at most one fully black rectangle).
- Line lemma per direction pair {w,w_perp} in l x l boxes + sum phi(s)/s^2 ~ (6/pi^2) ln S gives T >= c^3 n^2 log n for N = c n^{4/3}.
- Theorem: f(n,n) = O(n^{4/3} (log n)^{-1/6}); boundary handled by strips (axis budget inside a strip).
- Written into REPORT.md 5.1. Next: Whitney refinement; injectivity (birthday) for a polynomial saving.

## 03:45 More analytic results
- Parity closure lemma: odd-only, even-only or checkerboard seas have no single or vertical rivals (tally: zero). Heuristic: band seas with k ~ log^2 h give rho_h -> infinity.
- Lemma 6: alternating seas, h odd, t=(h-1)/2, t^2=ab (2<=a<b): gaps 2<=D<=b-a are invalid for every pair of edges. h=9 checked (D<=6).
- Threshold LLL sketch: base must be alternating seas (row-1 sea both sides fails at one double: (y,a), a odd, triple (dx,a-1,g)).
- Corrected: unbalanced grids gain only when m/h <= polylog.
- Lemma 7 (all h): double with odd row 2s+1, row-h gap D-1 then row-1 sea to column s^2: invalid if D+2 <= s^2. Corollary: uniform alternating seas fail for all orders for 5<=D<=s_max^2-2, D!=8 (about W_h). h=8 random orders: none valid D<=12, all from 14.
- Whitney refinement: f(n,n) = O(n^{4/3} (loglog n)^{2/3} (log n)^{-1/3}).
- Uniform gaps escaping Lemma 7: exactly D in {1,2,3,4,8} (squares mod 2D avoid [D+2,2D-1]); checked D<400.
- a_5 exact form: degree-6 polynomial times rho_5^m fits counts to 1e-14 from m=48; residuals decay ~0.58/col (rho' ~ 2.06); c_5 = 1.32152e-8, ratio -10.25.
- Gap scans h=8,10: jumps at D = s^2-1 (8, 15); all pairs valid from D = W_h.
- Affine orders and staircase blocks: negative (see report 4.3).
- Alternating gap 4 dead (edges failing alone in both roles, h=6..10). anneal4 (boundary seas, spacing 4) found a valid 6x45 board.
- Lemma 8 (2-adic): row-1 sea spacing 4, sea point + two double points, opposite parity: vertex at u needs odd row = 5 mod 8; vertex at p needs r1 odd, v2(r1-1) in {v2(d)+2, v2(d)+3}, 4d | (r1-1)(r2-r1), r2 > r1. Adjacent rule: rows 5 mod 8 / 9 mod 16 forbid larger even rows next door. Verification running.
- Random-order interior violation rate per double (row-1 sea, spacing 4): 0.64, 1.46, 1.93, 2.36, 2.97 for h = 6..14.
- Lemma 8(c) verified: 12/12, 32/32, 48/48 predicted adjacent violations found (h=8,10,12).
- One-switch spacing-4, 1-col margins: 6x35 valid (order 25,34,23,14,12,16,36,45,56, switch after 7th double). h=8,10,12 running.
- anneal4 margin 1: valid 7x47 (59 points), gaps 1x7 (row h before each double, row 1 after). Order 23,12,16,27,67,56,47,36,25,14,34,45.
- Lemma 9: 1,x,h family escapes Lemma 6 for h=3 mod 4. gap family: h7 found, h6 best 6, h9 ~60, h11 improving.
- Lemma 10: in 1,x,h family, h=1 mod 4 every double killed by (0,c),(1,1),((c-1)(h-c),h), c even; h=3 mod 4 only free-cell events with odd c. Tally agrees (h9: 1.8/double singles; h7,h11 none).
- anneal4 margin 1: valid 8x63 (79 points), row-8 part 36,45,56,67,58,78,27 then row-1 part 38,12,14,23,34,25,47,16,18; obeys the safety rule.
- rho_odd(20) = 4.167; loss ln(h/2/rho) 0.866 (18), 0.875 (20): leveling.
- dfs_gap.py (backtracking): h8 switch found (8x63). h11 gap reaches depth 29/30; h15 gap 39/56.
- dfs plateaus: gap h11 29/30 (leftovers row-5 edges), h15 45/56; switch h9 19/20, h10 21/25, h12 28/36. Rigid families may fail from h=9.
- Softened 6/5 conjecture: axis-only deletion also gives 6/5 but GQ gives 4/3, so structure may beat deletion.
- Leftovers: h9 switch -> row-5 edges (centre row unsafe both seas); h11 gap -> rows 5,7 (v2=2 on one side).
- Forcing row-5 edges to the ends (h9 switch): still 19/20.
- 06:22 SAT: h9 spacing 3 padded (L=R=17 row 1) valid 9x92; collar => f(9,m) = m+20 for all m >= 58 (paper M_9 = 685).
- L_1 tracking block (row-h pad left, row-1 right, spacing 3) valid h=5..13 with full F; fails from 14 (5-12-13). L_3, L_5 blocks on 9 rows: none (exhaustive, restricted seas); L_1, L_7 found.
- 07:55 stopped split h10 (spacing 4, 6h, unresolved); restarted pad h10 spacing 3 (L=R=21, part 13579).
- 08:45 final export of report and files; pad h10 spacing 3 SAT still running.
