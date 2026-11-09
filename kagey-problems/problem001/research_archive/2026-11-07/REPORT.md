# Problem 001: research notes, 6–7 November 2026

Informal notes on an attempt at a general formula for the maximum blackout f(h,m) of the h x m grid
and for the number a_h(m) of maximum blackouts. Nothing here has been refereed. Proofs are sketches
unless marked otherwise, and every numerical claim names the computation behind it (section 8).

Notation. h <= m, q_h = floor(h^2/4), W_h = 1 + floor((h-1)^2/4), and a *sea* column is a singleton
column. Unless we say otherwise the doubles use the parity partition A = odd rows, B = even rows, whose
edge set is K_{odd,even}; its pair set F is all pairs of rows at odd distance.

## 1. Summary

1. **Counting (new; strongly supported, conditional proof).** For m beyond the threshold,
   a_h(m) ~ B_h * (prod over the q_h edges e of kappa_e) * m^{q_h} * rho_h^m,
   where rho_h is the entropy of an explicit shift of finite type (the *sea shift*), B_h is its boundary
   constant and kappa_e is the insertion weight of the double e. Verified exactly on four rows (growth to
   12 digits, constant to 10 digits against the paper's interval enclosure) and on five rows (growth to
   8 digits against the paper's own counter). On five rows the exact counts to m = 64 fit
   rho_5^m P(m) with P of degree 6 to relative error 1e-14, the exact form the transfer-matrix argument
   predicts (Corollary A4), and a random optimum has its doubles at asymptotically uniform positions in
   a uniformly random order (Corollary A5).
2. **Thresholds are of order h^2 (numerical; new exact values).** Valid boards with a double in every
   third or fourth column exist for h = 6, 7, 8 (SAT, and also annealing and backtracking in rigid
   spacing-4 families) and for h = 9 (SAT at spacing 3 with free interior seas, collar-extendable). For
   9 to 15 rows the rigid spacing-4 families stall one or more doubles short of the end (4.3), so free
   interior seas seem to be needed from nine rows on. New: f(7,m) = m+12 for every m >= 21 and
   f(8,m) = m+16 for every m >= 46 and f(9,m) = m+20 for every m >= 58 (the theorem in the paper gives
   M_8 = 421 and M_9 = 685). Also a valid 11 x 119 board in the rigid "1, x, h" family (the case
   h = 3 mod 4 that Lemmas 9 and 10 single out), so f(11,119) = 149. Then, with the end layers that
   Lemma 11 predicts, a collar board: **f(11,m) = m + 30 for every m >= 117** (4.1).
3. **Mechanisms (proved lemmas).** A Pythagorean exclusion principle, a reflection obstruction for
   interior seas, the spacing-4 lemma for boundary seas, and a reduction of spacing-4 boards to explicit
   Diophantine conditions. A counting heuristic shows that random edge orders need spacing about
   log^2 h, so an O(h^2) threshold needs arithmetic cancellation. Lemmas 6 and 7 show that the paper's
   alternating seas with uniform gaps fail for every edge order at every gap from 5 up to about W_h
   except 8, and one-double right angles kill gap 4 on 6 to 10 rows,
   so constructions of that kind are stuck at order h^4. Lemma 8 gives the 2-adic rule behind the main
   family of right angles at spacing 4, and it matches the layout of the six- and eight-row boards: a
   row-1 sea holding the edges whose odd row is 1, 3 mod 4 or 1 mod 16, one switch, and a row-h sea
   holding the reflected ones.
4. **Intermediate widths (conjecture, partly refuted).** With f = h + m - 1 + c, each extra cycle c costs
   about three columns; the rule c = min(floor((h-2)^2/4), floor((m - 3 + [h odd])/3)) fits all known
   values for h <= 6 except (6,8), and fails at 7 x 11 for doubles-only blackouts.
5. **Squares.** f(8,8) >= 17, so the first n with f(n,n) > 2n is 8. We explain why random embedding
   plus deletion stops at n^{6/5}, and prove f(n,n) = O(n^{4/3} (log n)^{-1/6}) = o(n^{4/3}) from a
   completion budget: each white cell completes at most one rectangle with three black corners (5.1).
   Whitney boxes improve this to O(n^{4/3} (log log n)^{2/3} (log n)^{-1/3}), essentially the limit of
   the method. Random deletion, thinned generalized quadrangles and level-line sets all stop at
   n^{6/5}. For the axis part alone deletion also stops at n^{6/5} while generalized quadrangles reach
   n^{4/3}, so this is weak evidence; 6/5 is the natural guess only if no algebraic set controls the
   tilted completions.
6. **Growth of rho_h.** Seas confined to one parity class (or the checkerboard) have no single or
   vertical rivals (parity closure, 2.4). Their entropy keeps growing with h (2.37 to 4.17 for
   h = 6 to 20), and a heuristic with bands of boundary rows suggests rho_h is unbounded, against our
   first guess of a peak. This is not proved.
7. **Toward validity of the "1, x, h" family (proved reductions, 4.5).** For h = 3 mod 4 every
   three-corner violation in the interior follows one complete law (Proposition 16). Its main part,
   law (D), reads e = w + d' mod 4 with a range of phi(r)/4 slots (Lemma 22). For a fixed order the
   middle cells are exactly a 2-SAT problem (Proposition 17, now proved in full), so validity is a
   question about the order alone. Residues mod 4 protect about half of the vertices at every
   distance (the slot rules, Propositions 18 and 19), no residue rule can protect more
   (Proposition 20, Lemma 21), and the other half needs sizes: the window principle (Lemma 23)
   protects a vertex at every distance when the doubles on the one track it points at have their
   even rows on its near side. What is still open is an explicit arrangement for general h. The rule
   is compatible with validity on eleven rows (valid 11 x 169 collar boards obeying it).

## 2. Counting the maximum blackouts

### 2.1 Localization

Beyond the threshold every maximum blackout has the equality structure (Theorem "equality"). Fix the
bipartition pi and so the pair set F_pi. Then validity of a word over the h singleton letters and the
q_h double letters (each double exactly once) is local:

- axis-aligned pairs are automatic (distinct edges of a bipartite graph give no 4- or 6-cycle);
- by Lemma "rival", a tilted presentation of one or two points has an axis-aligned rival only through
  the black rows of its own columns and through F_pi, which is fixed;
- two tilted rectangles with the same presentation lie within 2 W_h columns of each other;
- a hidden tilted rectangle is a local event.

So the optimal words are the words with each double letter exactly once that avoid a finite set of
forbidden factors of length at most 2 W_h + 1.

### 2.2 The sea shift and the product formula

The **sea shift** Sigma_pi is the set of bi-infinite words over the rows (one black point per column)
avoiding hidden tilted rectangles, rivals (with F_pi), and repeated tilted presentations. Its transfer
graph Gamma_pi has as states the words of length 2 W_h. Let rho_pi be its Perron root.

**Theorem (conditional).** Suppose (i) Gamma_pi has a unique strongly connected component of maximal
spectral radius and it is aperiodic, and (ii) every double e can be inserted between two states of that
component. Then
    |L_pi(m)| = B_pi * prod_e kappa_e * m^{q_h} * rho_pi^m * (1 + O(1/m)),
with B_pi = <l|v><u|r>/<u|v> (u, v the left and right Perron vectors, l, r the boundary vectors) and
kappa_e = <u|E_e|v> / (rho^{|w_e|} <u|v>), E_e the transfer through a window containing e.

*Sketch.* Cut a word at its doubles. The generating function is a sum over the q_h! orders of products
R(z) E_{e_1} R(z) ... E_{e_q} R(z) with R(z) = (I - zT)^{-1}. Near z = 1/rho, R(z) ~ v u^T/(1 - rho z),
so each product has a pole of order q_h + 1, and the leading coefficient prod <u|E_e|v> does not depend
on the order. The q_h! orders cancel the 1/q_h! in the coefficient of (1 - rho z)^{-(q+1)}, which leaves
m^{q_h}. Hidden rectangles cannot occur in a sea for h = 4, 5 (otherwise one hidden rectangle would add a
factor m; the observed ratios converge to rho itself, not rho(1 + 1/m)).

In words: an optimum is a stationary random sea in which the q_h doubles sit at independent uniform
positions, each surviving with weight kappa_e. Writing pi_e for the probability that inserting e into a
context drawn from the measure of maximal entropy of the sea is valid, kappa_e = pi_e / rho_h, so

    a_h(m) ~ B_h * m^{q_h} * rho_h^{m - q_h} * prod_e pi_e.

**Three rows by hand.** For the pair set F = {A, C} (pairs {1,2} and {2,3}), B = {1,3} is not in F, so by
Lemma "singleton dichotomy" no singleton window fails: the sea shift is the full shift on three letters,
rho = 3 and N_0(m) = 3^m, so B_3 = 1. A double A between random singletons s, t fails exactly for
st in {bb, bc, cb} (Lemma "six of nine"), so pi_A = 2/3 and kappa_A = 2/9, and likewise kappa_C = 2/9.
The product formula gives (2/9)^2 m^2 3^m = (4/81) m^2 3^m, the leading term of Theorem B. For the pair set
{A, B} the windows bsb are forbidden, the sea shift has entropy 1 + sqrt 3, and that is the growth rate of
E_m in Theorem "three-row closed form".

**Unconditional upper bound.** The sea segments of an optimum are valid sea words, and the number of
paths of length n in the sea graph is at most C n^{k-1} rho_pi^n, with k the largest number of
maximal-entropy components on one path. Hence a_pi(m) <= C m^{q_h + k - 1} rho_pi^m with no hypothesis;
the theorem above adds the matching lower bound (k = 1) under (i) and (ii).

**Proposition (rho_h >= 2 for even h).** For even h every word over the two rows {1, h} is a valid sea
word. *Proof.* A tilted rectangle has at most one corner in row 1 and one in row h, and these are opposite
(facts F1, F2 of the paper), so it has at most two black corners, forming a diagonal. The other diagonal
lies in rows 2 to h-1: it is not horizontal, since the centre row (1+h)/2 is not an integer, and not
vertical, since its rows would leave the grid; an oblique shown pair has its crossed points in interior
rows, which are white, so it has no rival. Three black corners cannot occur. A second rectangle showing
the same pair would need its own black diagonal in rows 1 and h with the same midpoint and length, that
is the mirrored pair, which needs a column black in both rows; and no black side exists by F1 and F2. ∎
So the full 2-shift sits inside the sea shift. For odd h the horizontal exposure in row (1+h)/2 adds
constraints, and they are the only ones: by F1 and F2 a word over {1, h} has no hidden rectangle, no
three black corners, no vertical or oblique rival and no repeated presentation, so it is valid iff no
pair (x, 1), (x + p, h) (or the mirror) with p^2 + (h - 1)^2 = L^2 has both ends x + (p -+ L)/2 of the
horizontal diagonal black in the same row (Lemma 6's mechanism). Words whose switches between rows 1 and
h are more than max L = ((h-1)/2)^2 + 1 apart are valid (each such window then contains exactly one
switch), so rho_h > 1 for odd h as well. Sequential Monte Carlo gives the entropy of the {1, h} words
as 1.55, 1.34, 1.53, 1.20 for h = 7, 9, 11, 13, lower when h - 1 is a leg of more Pythagorean triples.

### 2.3 Numbers

| h | rho_h | how |
|---|---|---|
| 3 | 3 | matches a_3(m) ~ (4/81) m^2 3^m |
| 4 | 3.351996777310375 | transfer graph; the paper's rho_4 = 3.351996777310... (all 12 printed digits) |
| 5 | 3.5438756463 | transfer graph (1,066,807 states); the paper's counter with the six doubles fixed near the left gives ratios 3.5438756623 at m = 58 |
| 6 | about 3.585; at most 3.5979 | Monte Carlo; windowed upper bound (window 10) |
| 7 | about 3.783 | Monte Carlo |
| 8 | about 3.732 | Monte Carlo |
| 9 | about 3.820 | Monte Carlo |
| 10 | about 3.911 | Monte Carlo |
| 11 | about 4.20 | Monte Carlo |

The Monte Carlo estimator (sequential Monte Carlo on valid sea words) gives 3.344 for h = 4 and 3.560 for
h = 5, so it is good to about 0.5%. Windowed upper bounds on five rows (window 6, 7, 8, 9, exact 11):
3.5525, 3.5490, 3.5473, 3.5447, 3.5439.

Four rows, constant: from one-double marked counts to width 40, B_4 = 1.66850499788,
kappa_{12} = kappa_{34} = kappa_{14} = 0.091516, kappa_{23} = 0.068333, and
B_4 * prod kappa_e = 8.16109707754e-5. The paper encloses c_4 in [8.1610970775, 8.1610970776] x 10^-5.

Five rows, constant: the counter with the six doubles fixed 20 columns apart gives
N/(6! rho_5^m) -> 1.3208e-8 (the same method gives 8.1606e-5 on four rows, an error of 6e-5 from the
finite spacing). The exact counts for the parity partition, recomputed to m = 64 with wider slots, satisfy
a_5(m)/(c_5 m^6 rho_5^m) = 0.617, 0.655, 0.6872 at m = 40, 44, 48, against 1 - 15/m = 0.625, 0.659, 0.6875.
A cleaner fit (Corollary A4) is a_5(m) = 3.5438756463^m P(m) with P of degree 6 and
P(m) = 1.32152e-8 (m^6 - 10.25 m^5 + ...), exact to relative error 1e-14 from m = 48 on. Its leading
coefficient differs from the fixed-spacing value 1.3208e-8 by a relative 5e-4. That is the same kind
of finite-spacing error as the 6e-5 on four rows, larger here because there are six doubles instead of four.

**The parity partition dominates.** Four rows: parity 3.351997, {1,2}|{3,4} 2.931997, {1,4}|{2,3}
2.856928. Five rows (window 8): parity 3.5473, {1,3} 3.4055, {1,2} 3.3294, {1,4} 3.2965, {1,5} 3.1654,
{2,3} 3.1376. So almost all optima use the parity partition.

**Typical sea words look random.** Under the measure of maximal entropy the rows are used almost
uniformly (0.2495, 0.2505, 0.2505, 0.2495 on four rows; 0.1996, 0.1919, 0.2169, 0.1919, 0.1996 on five).

### 2.4 How rho_h should behave for large h (heuristic)

Let lambda_h be the expected number of violated sea constraints per column of a uniformly random word.
The dominant term (three black corners and a singleton rival) is about 2 N_h / h^3, where
N_h = sum_{b+d<h} tau(bd)(h - b - d) counts tilted rectangles per column, so lambda_h is of order
log^2 h. Measured: 0.262, 0.453, 0.725, 0.883, 1.147, 1.505, 1.761 for h = 4, 5, 6, 7, 8, 10, 12, and
log(h/rho_h) is about 0.65 lambda_h for h = 4, 5, 6. Uniform-row seas must therefore die out, and the
maximal-entropy seas must become structured, concentrated near the boundary rows, which are immune
(2.1 and 4). For even h every word over the rows 1 and h is valid (Proposition in 2.2), so rho_h >= 2
for all even h. (We first expected rho_h to peak and then decrease to a limit. The parity closure below
points the other way.)

**Lemma (parity closure).** Take the parity partition, and a sea word whose black points all lie in one
coset of an index-2 sublattice that fixes row parity: all rows odd, all rows even, or the checkerboard
(row = column mod 2). Then no tilted rectangle of the word shows a single point with a rival, and none
shows a vertical pair with a rival.

*Proof.* The coset is closed under A + C - B, so the fourth corner X of a tilted rectangle with black
corners A, B, C lies in the same coset. Its row therefore has the parity of the black point in its
column, and Lemma 5 gives no rival. For two black corners P, Q with a white vertical pair, P and Q are
opposite (one black point per column), the vertical diagonal has length L = |PQ|, and it has a rival
only if L is odd. With constant row parity, dy is even and the integer midpoint column forces dx even,
so L is even. On the checkerboard dx = dy mod 2: if both are odd, dx^2 + dy^2 = 2 mod 4 is not a
square. ∎

So the two families that dominate random words (single rivals 0.81 and vertical rivals 0.07 per column
on 12 rows, `scripts/conf_tally.py`) vanish identically. What remains are coincidences of four black
points: hidden rectangles, horizontal and oblique rivals, and repeated presentations. For uniformly
random odd-row words these cost 0.26, 0.61 and 1.16 per column on 6, 8 and 12 rows, and sequential Monte
Carlo gives odd-row entropies 2.37, 2.70, 2.89, 3.29, 3.44, 3.66, 3.79 and 4.17 on 6, 8, ..., 20 rows
(`scripts/smc_conf.py`), lower bounds for rho_h that keep growing. (The loss against h/2 letters,
log(h/(2 rho)), is 0.24, 0.39, 0.55, 0.60, 0.71, 0.78, 0.87, 0.88: it grows at first and then seems to
level off, which would make this subshift's entropy grow roughly linearly in h; Monte Carlo noise is a
few percent, so this is suggestive only.) Bands of fixed width behave as the heuristic below predicts:
odd rows within 4 of an edge (four letters) give 2.66 on 12 rows and 2.04 on 16 rows, so a fixed
number of boundary rows loses entropy as h grows, and the band has to widen with h.

**Heuristic: rho_h grows without bound.** Confine the sea to the odd rows within 2k of the top or bottom
edge, 2k letters in all. A four-point coincidence needs its black points in these bands. Most tilted
rectangles that reach both bands are tall and thin, with a short side (a, b), b <= 2k, and a long side of
height about h, so there are about k^3 log h of them per column. Each needs three or four specified band
cells, which costs (2k)^{-3} or (2k)^{-4}. The horizontal rivals between the bands add about
avg tau(dy^2) / (4k), which is of order log^2 h / k. So the cost per column is
O(log h / k + log^2 h / k), and with k = C log^2 h the band seas should have entropy at least
c log^2 h. A proof would need an entropy lower bound for constraints that fix few columns spread over
windows of length h^2 (a local lemma for words with gaps), which we do not have.

## 3. Intermediate widths: about three columns per cycle

Write f(h,m) = h + m - 1 + c(h,m). Then c is the number of independent cycles of the row-column graph
beyond a spanning tree (the boundary cross has c = 0), c is symmetric in h and m, and c <= floor((h-2)^2/4),
the cyclomatic number of K_{floor(h/2), ceil(h/2)}.

Known: c(4,m) = 0, 0, 1 for m = 4, 5, >= 6; c(5,m) = 1, 1, 1, 2 for m = 5, 6, 7, >= 8;
c(6,m) = 1, 1, 2, 2, 2, 2, 3, 3, 3, 4 for m = 6, ..., 15; c(7,7) = 1, c(7,8) = 2, c(7,m) = 6 for m >= 21;
and from SAT, c(7,9) >= 2, c(7,10) >= 2 (all structures), and with doubles from K_{3,4}: c >= 3 first
at width 12, c >= 4 at 14, c >= 5 at 19 or less (UNSAT at 15 and 16).

**Strip conjecture.** For 4 <= h <= m, c(h,m) = min(floor((h-2)^2/4), floor((m - 3 + [h odd])/3)),
with exceptions near squares. It fits every known value for h <= 6 except (6,8) (whose optimum uses two
triple columns), and f(7,7), f(7,8), f(7,9), f(7,10). It predicts thresholds
m_h = 3 floor((h-2)^2/4) + 3 - [h odd]: 6, 8, 15, 20, 30, 38, 51 for h = 4, ..., 10, so m_h ~ 3h^2/4.

**Not a packing law.** The "three columns per cycle" is not the inverse of a maximum packing density of
doubles: doubles at alternating gaps of 1 and 2 (density 2/5) with free seas are SAT on six rows (width 23)
and seven rows (width 30), while strict alternation (density 1/2) is UNSAT there. The thresholds pack even
more densely by mixing runs of consecutive doubles (staircases) with spaced ones: q_6/m_6 = 9/15 = 0.6 and
q_7/m_7 >= 12/21. So the right model is runs and gaps, and the asymptotic constant in m_h ~ C h^2 is open
(between 1/4 and about 3/4 on present evidence).

**Refuted for doubles only.** It predicts c(7,11) = 3, but no 7 x 11 blackout made of nine distinct doubles
(partitions {2,4,6}, {1,3,5}, {1,4,7}, {1,6}, {1,7}) and singletons is valid. So either triple columns or a
non-bipartite triangle-free graph is needed there, or the rule is only approximate. (Run outcomes at the
end of the night: section 7.)

## 4. Thresholds and the arithmetic of the obstructions

### 4.1 New exact facts

- f(7,m) = m+12 for every m >= 21 (SAT witnesses at widths 21 to 28, the width-28 collar board).
- f(8,m) = m+16 for every m >= 46: a 72-column board, a 46-column core with W_8 = 13 row-1 columns on
  each side, valid by verify_narrow and by our fast checker; the collar theorem extends it. Core:
  25,3,3,36,7,3,47,7,7,58,8,8,78,8,7,27,8,7,67,6,6,56,5,5,45,4,4,34,3,2,23,3,4,38,1,1,16,2,2,14,1,1,18,8,4,12.
- f(9,m) = m+20 for every m >= 58 (new this morning): a spacing-3 board (a double in every third
  column), 58-column core, with W_9 = 17 row-1 columns on each side, 9 x 92 with 112 = m + 20 points,
  valid by verify_narrow and by the fast checker (`data/sp_h9_g2_L17_R17_p2468_none_11.json`); the
  collar theorem with padding row 1 on both sides gives every width from 58 on. The paper's theorem
  gives M_9 = 685. Core:
  27,8,1,16,6,1,78,8,1,67,6,6,56,5,5,45,4,3,34,4,3,23,2,1,12,1,1,29,2,1,14,1,9,69,9,2,49,1,9,38,8,8,
  89,9,9,18,8,8,58,7,7,47,3,7,36,3,3,25.
  Its core width is 3 q_9 - 2, and its middle is the descending staircase 78, 67, 56, 45, 34, 23, 12
  with two sea cells after each double, as on eight rows. So m_9 <= 58, against the strip conjecture's
  prediction m_9 = 38 (section 3).
- f(11,m) = m+30 for every m >= 117: a 117-column core (spacing 4) with W_11 = 26 columns of row 1 on
  the left and of row 11 on the right, 11 x 169 with 199 points, valid by verify_narrow
  (`data/cegar_h11_s4_hyb_t3_111.json`, found by `scripts/cegar_board.py`). Deleting end sea columns
  keeps a board valid and the collar theorem lengthens the pads, so every width from 117 on follows;
  the paper's theorem gives M_11 of order h^4. Structure, slot by slot (odd row, even row; gap after):
  three free transition gaps at each end; in between every gap is "1, x, 11", with x = 1 in slots
  3 to 6 and 21 to 25 and x = 11 in the band 7 to 20. The doubles next to the transition layers have
  extreme even rows (row 2 at slots 4, 5; rows 2 and 10 at slots 21, 22, 24, 25), and the first
  centre-row double inside the "1, x, h" part is at column 52 > phi(6) = 25, as the graded layer of
  Lemma 11 requires. The same layout with one transition gap at each end is UNSAT (a proof, for that
  layout).
- f(8,8) >= 17 (verify_narrow and solver/brute.py), so the first n with f(n,n) > 2n is 8.

### 4.2 Constant spacing (SAT)

Doubles in every (g+1)-th column, all q_h edges, singletons elsewhere:

| seas | g = 1 | g = 2 | g = 3 |
|---|---|---|---|
| any row | UNSAT h = 6, 7 | SAT h = 6, 7, 8; with W_h padding (collar-extendable) h = 6, 7, 8, 9 | SAT h = 6 |
| rows 1 and h only | | UNSAT h = 7 | SAT h = 6, 7, 8 (rigid families stall at 9 to 15, 4.3) |

Structured families that worked: for even h, a row-1 sea followed by a row-h sea (h = 6, 8); for odd h
the repeated pattern "h, double, 1, 1" (h = 7); diagonal staircase blocks with alternating directions
(h = 6 at spacing 4, h = 7 at spacing 3). Adjacent disjoint, non-parallel doubles are fine locally: every
pair of edges of K_{3,3} can sit in adjacent columns of a valid six-row board. So the limit on density is
global, an accumulation of coincidences.

### 4.3 Lemmas

**Lemma 1 (Pythagorean exclusion).** Let S be valid with pair set F. If p = (x, r) and q = (x+4, r+3)
are black, the points (x+2, r-1) and (x+2, r+4) lie in the grid and are white, and {r-1, r+4} is in F,
then S is not valid. The same holds for q = (x+4, r-3), and for every displacement (dx, dy) with dx even,
dy odd, dx^2 + dy^2 = L^2 and L odd, with exposed points (x + dx/2, r + dy/2 +- L/2).

*Proof.* p and q are opposite corners of the rectangle whose other diagonal is the vertical segment
through the midpoint with the same length. It shows exactly that vertical pair, and so does the
axis-aligned rectangle on its two rows and a column containing both. ∎

For maximum blackouts F = K_{odd,even}, so the last condition always holds. This explains why long
staircases fail from h = 6 on: in a staircase of five consecutive doubles, (x, a+1) and (x+4, a+4) differ
by (4, 3). It also explains why boundary seas are immune: the exposed rows leave the grid.

**Theorem 1' (optima are Pythagorean-free in the interior).** Let S be a maximum blackout whose pair set
contains every pair of rows at odd distance (the parity partition, beyond the threshold). Then S contains no
two black points p, q with q - p = (dx, dy), dx even, dy odd, dx^2 + dy^2 = L^2, L odd, whose exposed rows
mid(p,q) +- L/2 both lie in [1, h], except possibly when the rectangle is hidden and no extension of
Lemma A2 fits in the grid.

*Proof.* Let x be the exposed column and r1, r2 the exposed rows; r2 - r1 = L is odd, so {r1, r2} is in F.
If column x is a sea in a row other than r1, r2, the rectangle shows the vertical pair, which has a rival.
If it is a sea in row r1 (or r2), the rectangle shows only the other exposed point, whose row differs from
the sea row by L, which is odd, so it has a rival by Lemma 5. If x is a double containing exactly one exposed
row, the single shown point lies in a double column and has a rival by Lemma 5. If x is the double
{r1, r2}, the rectangle is hidden, and Lemma A2 gives two rectangles with equal presentations. ∎

For (4, 3): no optimum has black points at (x, r) and (x+4, r+-3) with 2 <= r, r+4 <= h (for +3), and the
same holds for (12, 5), (8, 15), (24, 7), (20, 21), (40, 9), and so on. This applies to every black point,
sea or double. Beyond the threshold the interior of an optimum is therefore a Pythagorean-free point set, an
analogue of a forbidden-distance problem; boundary seas escape because their exposures leave the grid.
Since the exposed segment has length L <= h - 1, for 6 <= h <= 13 the theorem forbids exactly one
displacement, the knight-like (4, +-3) (L = 5); (12, 5) enters at h = 14, (12, 9) at 16, (8, 15) at 18.
All seven known optima we checked (six to eight rows) contain no forbidden pair. In the eight-row board of
4.1 the middle part 67, 56, 45, 34, 23 (each followed by two sea columns in the shared row) is a classic
descending staircase with runs of three, which drops at most two rows over four columns and so never meets
the (4, 3) rule.

**Lemma 2 (reflection obstruction).** If row v is black on an interval of columns containing a double
{u, v}, then every Pythagorean triple with leg |u - v| gives a tilted rectangle with two black corners in
row v and one at the double, whose only shown corner is the reflection of the double's point in row
2v - u; it has an axis-aligned rival through row v. So interior "star" seas fail, and boundary seas are
immune because 2v - u leaves the grid.

**Lemma 3 (spacing 4).** Take a row-1 sea with a double in every column = 0 mod 4. Then a row-1 corner u
and a double point d never give a violation, apart from finitely many cases in which the double at the
landing column contains row 1 or the exposed row:
- vertical exposure leaves the grid (the exposed rows are (1 + c +- L)/2 with L > c - 1);
- horizontal exposure sits in columns p - t and p + s with s t = (dy/2)^2; for every Pythagorean triple,
  primitive or scaled, one of s, t is = 0 mod 4, so one shown point lands on a double column, which is
  not black in row 1, and there is no rival.

**Lemma 4 (reduction to Diophantine conditions).** In the same setting, take doubles at 4i and 4j,
d = j - i, and a cross pair of rows with dy = |r - r'|.
- Vertical danger iff dy is odd and (4d)^2 + dy^2 = L^2 with L <= h - 1; in particular d < h/4.
- Horizontal danger iff dy is even, (4d)^2 + dy^2 = L^2, and the shown columns 2(i+j) +- L/2 are both sea
  columns: exactly when dy = 2 mod 4, or dy = 0 mod 4 and i + j + L/4 is odd.
- Safe zones: dy < sqrt(8d + 1) (a leg's partner is at least sqrt(2 * leg + 1)); 3 does not divide d or
  dy (every Pythagorean triple has a leg divisible by 3); dy = v d with v != 3 (16 + v^2 is a square only
  for v = 3).

**Pell sparsity.** Lay out a diagonal staircase L_g = {{a, a+g}} with one row per step. The cross
differences are d and |d +- g|, so a danger needs 17 d^2 +- 2 d g + g^2 = L^2, that is
X^2 - 17 L^2 = -16 g^2 with X = 17 d +- g. The solutions are exponentially sparse; for g = 1 the first is
d = 6 (the triangle 24-7-25), which matters only once h >= 26.

**Counting heuristic.** For a uniformly random edge order at spacing s, the expected number of vertical
coincidences per double is about (2/pi) log h (only doubles within h/4 slots can collide), and of
horizontal coincidences about c log^2 h / s (divisor sums over Pythagorean partners). So random orders
need spacing of order log^2 h, a threshold of order h^2 log^2 h. A threshold of order h^2 needs orders
whose coincidences cancel, which the SAT solutions for h <= 8 show is possible.

**Dead end.** A lattice condition x = alpha y (mod 3^K) excludes every Pythagorean vector, but the two
points of a double share a column and cannot both lie in it once 3^K > h; conditions modulo 3 or 4 alone
cannot cover more than three doubles within range.

**Lemma 5 (singleton rivals).** In a board of singletons and doubles with pair set F = K_{odd,even}, a
white point (x, r) shown alone always has an axis-aligned rival when column x is a double (one of its two
rows has the parity opposite to r), and when column x is a sea in row sigma it has one exactly when
r and sigma have different parity.

**Pell structure of a staircase.** Lay out L_g = {{a, a+g}} (g odd) at spacing 4 with the rows moving by
one per double. Cross differences at slot distance d are d (never dangerous: 17 d^2 is not a square) and
|d +- g|, dangerous only if 16 d^2 + (d +- g)^2 = L^2, that is X^2 - 17 L^2 = -16 g^2 with X = 17 d +- g.
The solution classes give d = 6g (dy = 7g, L = 25g: the triangle 24-7-25 scaled) and d = 10g (dy = 9g,
L = 41g), both vertical, and d = 63g (dy = 64g, L = 260g), horizontal but cancelled by the residue
condition of Lemma 4 (j - i = 63g is odd, so i + j + L/4 is even and the shown columns are doubles).
So a staircase is internally valid whenever 25 g > h - 1; for h < 26 every staircase is. The same
algebra applies between staircases: all double points lie on lines of slope 1/4, a cross pair from lines
with intercepts c, c' has dy = d + (c' - c), and dangers occur only near d = 6|c' - c| or 10|c' - c|.
Velocity 2 is worse: X^2 - 5 L^2 = -4 g^2 has the solution (11, 5), which is the 3-4-5 danger at d = g.

**The perpendicular mechanism.** An ascending staircase steps by (4, 1). From a double point in row
1 + 4k the perpendicular (1, -4)k reaches a row-1 sea point, and the fourth corner falls in row 2 of a
sea column, a singleton with a rival by Lemma 5. For a descending staircase (step (4, -1)) the fourth
corner falls in row 0, outside the grid. So descending staircases suit a row-1 sea, ascending ones a
row-h sea.

**What still fails.** Descending staircases, contiguous at spacing 4 in a row-1 sea, still have 6, 24,
45 and 70 violations for h = 6, 8, 10, 12. Classified by their black corners, they are: (i) the exceptions
of Lemma 3 (the landing double contains row 1); (ii) the double-to-double dangers of Lemma 4; (iii) three
black corners (one sea point and two double points, mostly from doubles 1 to 3 slots apart) forming a
tilted right angle whose fourth corner is forbidden by Lemma 5; (iv) repeated oblique presentations.
Type (iii) dominates and grows with h. So an O(h^2) construction has to control tilted right angles among
double points, not only Pythagorean distances.

**The right-angle family, explicitly.** Let u = (x0, 1) be a row-1 point and p = (x1, r1), q = (x2, r2)
double points from doubles d slots apart (x2 - x1 = 4d).
- Right angle at u: (x0 - x1)(x2 - x0) = (r1 - 1)(r2 - 1), so u exists iff 4 d^2 - (r1 - 1)(r2 - 1) is a
  perfect square; the fourth corner is in row r1 + r2 - 1.
- Right angle at p: 4d (x0 - x1) = (r1 - 1)(r2 - r1), a divisibility condition; the fourth corner is in
  row 1 + r2 - r1.
- In both cases the fourth corner's row is odd exactly when r1 and r2 have the same parity, and then, on a
  row-1 sea column, Lemma 5 makes it harmless. So the fatal instances are the opposite-parity pairs, and
  any fourth corner on a double column.
Example: adjacent doubles (d = 1) with points in rows 2 and 5 give 4 - 1*4 = 0, a right angle at a row-1
point between them, and a fourth corner in row 6.

**The design problem.** A spacing-4 boundary-sea board is valid iff its edge order avoids: the Pythagorean
distance relations of Lemma 4 (with the residue rule), the square relations 4 d^2 - (r1 - 1)(r2 - 1) = k^2
and divisibility relations 4d | (r1 - 1)(r2 - r1) for opposite-parity cross pairs (and for fourth corners on
double columns), the exceptions of Lemma 3, and repeated oblique presentations. All of these involve only
doubles within W_h/4 slots of each other, and the relations get sparser as d grows. An order meeting them
for every h would prove m_h = O(h^2) with the explicit constant 4.

**Lemma 6 (alternating seas cannot be packed, h = 1 mod 4).** Let h be odd, t = (h - 1)/2, and write
t^2 = a b with 2 <= a < b. In the paper's alternating seas (row 1 left of a double, row h between two
consecutive doubles, row 1 again after the next), if two consecutive doubles are at columns 0 and D with
2 <= D <= b - a, and the row-1 region to the left of column 0 has at least a - 1 columns, the blackout
is invalid, whatever the two edges are. For h = 1 mod 4 take a = 2: every gap other than 1 must exceed
(h - 1)^2/8 - 2, about W_h/2. Reflecting the rows gives the same for gaps whose sea is in row 1.

*Proof.* Put p = b - a and L = a + b, so p^2 + (h - 1)^2 = L^2. The points (1, h) (in the row-h gap) and
(1 + p, 1) (to the right of D, since D <= p) are black. They are opposite corners of the rectangle whose
other diagonal is horizontal in row (h + 1)/2, centred at column 1 + p/2, with ends at columns
1 + (p - L)/2 = 1 - a < 0 and 1 + (p + L)/2 = 1 + b > D. Both ends lie in row-1 regions and away from
the two doubles, so the axis-aligned rectangle on rows 1 and (h + 1)/2 through those columns has black
row-1 corners and shows the same two white points. ∎

*Example (h = 9).* t^2 = 16 = 2 * 8, p = 6, L = 10 (the 6-8-10 triangle). With doubles at 0 and D, for
2 <= D <= 6, the black points (1, 9) and (7, 1) are opposite corners of the rectangle whose other
diagonal is (-1, 5)-(9, 5), and the axis-aligned rectangle with black corners (-1, 1) and (9, 1) shows the
same two points. So nine-row alternating seas need spacing at least 7, while W_9 = 17. The fast checker
confirms it: with edges {2,5}, {4,7} or {3,8}, {1,6}, every gap 2 <= D <= 6 has row-5 horizontal rivals,
and they stop at D = 7 for the first pair (edge-dependent violations remain up to D = 9 for the second).

A scan over all ordered edge pairs (`scripts/pair_gap.py`, two doubles with alternating seas and wide
margins) matches the lemma exactly on nine rows: valid pairs 54, 0, 0, 0, 0, 0, 44, 104, 132 of 380
for D = 1, ..., 9. On six and eight rows (even, so the lemma is empty) there is no gap without valid
pairs: on eight rows 54, 48, 54, 68, 82, 102, 108, 164, 198, 202, 232, 210 of 240 for D = 1, ..., 12,
and all 240 from D = 13 = W_8 on (six rows: all 72 from D = 7 on). On ten rows the counts are 88, 80,
98, 142, 102, 82, 84, then 222 at D = 8, ..., 322 at D = 14, then 484 at D = 15, and all 600 from
D = 21 = W_10 on. The jumps at D = 8 and D = 15 (and at D = 8 on eight rows) are D = s^2 - 1 for s = 3
and s = 4: the two-double form of Lemma 7 below kills an edge with odd row 2s + 1 exactly while
D <= s^2 - 2. So "every edge pair works" starts at
D = W_h, which is presumably the sense in which alternating seas cannot be packed below about W_h. For
even h, a packing at a smaller gap needs an edge order whose consecutive pairs avoid the bad 60-80
percent, together with the longer-range conditions.

For h = 3 mod 4 the family needs a divisor 2 <= a < t of t^2 with b = t^2/a, so the bound is t^2/q - q
with q the least prime factor of t, and it is empty when t is prime. For even h the centre row is not an
integer, and oblique rivals cannot occur in a pure alternating sea (a tilted rectangle has at most one
corner in each boundary row), so any packing obstruction for even h must involve the double points.

**Lemma 7 (a double point next to a short boundary sea, every h).** Let a double containing the odd
row c = 2s + 1 (s >= 1) sit at column 0, with black row 1 at column -1, row h on columns 1 to D - 1, and
row 1 on columns D + 1 to D + B (the next double is at column D). If D + 2 <= s^2 <= D + B, the blackout
is invalid. The same holds mirrored in the columns, with the rows unchanged.

*Proof.* The points (0, c) and (s^2 - 1, 1) are black, since D < s^2 - 1 < D + B. Their difference
(s^2 - 1, -2s) has length s^2 + 1, so they are opposite corners of the rectangle whose other diagonal is
horizontal in row s + 1, centred at column (s^2 - 1)/2, with ends at columns -1 and s^2. Both ends are
row-1 sea columns, so the axis-aligned rectangle on rows 1 and s + 1 shows the same two white points. ∎

(Lemma 6 is the case of a row-h sea point instead of the double point, with other factorizations.)

**Corollary (uniform alternating seas need spacing about W_h).** With alternating seas and every gap
equal to D (so B = D - 1), the blackout is invalid for every edge order when some s <= s_max has
s^2 in [D + 2, 2D - 1], where s_max = floor((h - 1)/2). Every odd row from 3 to 2 s_max + 1 lies in some
edge, and both roles of a double reduce to the lemma (mirror the columns). The interval [D + 2, 2D - 1]
contains a square for D = 5, 6, 7 and for every D >= 9. So uniform spacing fails for all
5 <= D <= s_max^2 - 2 with D != 8, and s_max^2 - 2 is about (h - 1)^2/4, that is about W_h. Uniform
alternating seas therefore need width about q_h W_h, of order h^4/16, which is the order of the
paper's M_h = q_h + (q_h - 1)(2 W_h + 1). An O(h^2) construction has to leave this family: irregular
gaps (the lemma then fires only for some (double, gap) pairs) or interior seas.

The exceptions are arithmetic. With gap D the seas repeat with period 2D, and the lemma's points at
s^2 - 1 and s^2 lie in a far row-1 stretch exactly when s^2 mod 2D lies in [D + 2, 2D - 1]. The squares
mod 2D avoid that window precisely for 2D = 2, 4, 6, 8, 16 (squares mod 8 are 0, 1, 4; mod 16 they are
0, 1, 4, 9). That is, D = 1, 2, 3, 4, 8, and D = 4 is the same fact as the "one of s, t is divisible
by 4" in Lemma 3. So the lemma rules out every uniform gap below about W_h except these five.

At D = 4 the whole family is dead, for every factorization. The general form of Lemmas 6 and 7 uses
s^2 = a b (a < b): the black points (0, 2s + 1) and (b - a, 1), and the ends -a and b, all three of which
must be row-1 sea columns. With gap 4 the row-1 columns relative to a double whose left side is row 1
are exactly the residues 5, 6, 7 mod 8. So a = 1, 2, 3 mod 8, and both b and b - a are 5, 6 or 7 mod 8.
For a = 1 mod 8 this needs b in {6, 7} mod 8, but b = s^2 a^{-1} = s^2 mod 8 lies in {0, 1, 4}. For
a = 2 mod 8 it needs b = 7 mod 8; then b is odd and a is even, so s is even, 4 divides a b and hence a,
contradicting a = 2 mod 8. For a = 3 mod 8 it needs b - 3 in {5, 6, 7}, so b in {0, 1, 2} mod 8,
disjoint from {5, 6, 7}. (D = 8 is not immune: s = 6, a = 3, b = 12 fires once h >= 13.) So
alternating seas at spacing 4, width about 4 q_h = h^2, avoid every horizontal rival of this kind.

They fail anyway, through right angles at one double. Example (six rows): a double containing row 4
whose left sea is row 6 has black (0, 4), (1, 1) and (6, 6) (columns 1 to 3 are row 1, 5 to 7 are
row 6). The legs (1, -3) and (6, 2) are perpendicular, and the fourth corner (7, 3) sits in a row-6 sea
column with the opposite row parity, so Lemma 5 gives a rival. In general the legs are (1, 1 - c) and
((h - c)(c - 1), h - c), and whether the corner is fatal depends on (h - c)(c - 1) mod 8. Inside the
run of doubles such one-double events depend only on the edge and its role. Edges that fail alone in
both roles, so that no order can work, exist on every height tested: {1,4}, {3,4}, {4,5} on six rows,
and 8, 13, 20, 12 edges on 7, 8, 9, 10 rows. So uniform alternating seas are dead below about W_h,
except possibly at gaps 1, 2, 3 and 8.

*Check (`scripts/uniform_alt.py`, eight rows, 20 random edge orders per gap).* No order is valid for
D = 2, ..., 12; 4 of 20 are valid at D = 13 = W_8, and all 20 from D = 14 on. For D = 5, 6, 7 every
board contains the lemma's rival with c = 7 (s = 3).

**Right angles among double points (spacing-4 row-1 sea).** In this setting a tilted rectangle with
three black double corners at slots i, j, k (vertex at slot j) completes in column 4(i + k - j), a
double column. Its fourth corner is white there, and Lemma 5 gives it a rival. So every such right
angle is fatal: an edge order must avoid 16 (i - j)(k - j) = -(r_i - r_j)(r_k - r_j) for every choice
of rows r_i in e_i, r_j in e_j, r_k in e_k, with the completion in the grid. Three sea points cannot
carry a tilted right angle (F1), and for a sea point with two double points the completion's row
parity decides (fatal exactly for opposite-parity pairs, as in the right-angle family above). For
consecutive slots the condition reads (r_i - r_j)(r_k - r_j) != 16, so for example the two neighbours
of a double may not both contain the row 4 above one of its rows.

**Lemma 8 (2-adic form of the sea right angles, row-1 sea at spacing 4).** Let p = (4i, r1) and
q = (4j, r2) be points of two different doubles, d = j - i, with r1 and r2 of opposite parity (the
fatal case), and u = (x0, 1) a sea point (x0 not = 0 mod 4).
- (a) A right angle at u needs (x0 - 4i)(4j - x0) = (r1 - 1)(r2 - 1). The left side is odd times odd
  (impossible, the right side is even) or 4 times an odd number (x0 - 4i = 2 mod 4). So it exists only
  if the odd one of r1, r2 is = 5 mod 8.
- (b) A right angle at p needs 4d (x0 - 4i) = (r1 - 1)(r2 - r1) with x0 - 4i not = 0 mod 4. Since
  r2 - r1 is odd, r1 must be odd with v2(r1 - 1) in {v2(d) + 2, v2(d) + 3}, and 4d | (r1 - 1)(r2 - r1).
  The fourth corner is u + q - p, in row 1 + r2 - r1, so it lies in the grid only when r2 > r1; it
  sits in a sea column and has even row, so Lemma 5 makes it fatal.
- (c) So rows = 3 mod 4 are never the vertex, rows = 1 mod 16 only for even d, and for adjacent
  doubles (d = +-1) a double point in an odd row r1 = 5 mod 8 or = 9 mod 16 forbids every even row
  above r1 in both neighbouring doubles. (Example on eight rows: 45 next to 38 gives p = (0, 5),
  u = (3, 1), q = (4, 8), legs (3, -4) and (4, 3), fourth corner (7, 4).) Check
  (`scripts/check_lemma8.py`, four random orders each): every predicted adjacent violation is found
  by the checker, 12 of 12 on eight rows, 32 of 32 on ten, 48 of 48 on twelve.
For uniformly random orders the interior violations per double are 0.64, 1.46, 1.93, 2.36, 2.97 for
h = 6, 8, 10, 12, 14; the largest class is exactly this family (single shown point, two double
corners, one sea corner: 0.33 to 1.19 per double), followed by the Pythagorean pairs of Lemma 4 (two
double corners, a shown pair). Lemma 8 says which rows can carry this family at all, and it is the kind of arithmetic an
O(h^2) order has to respect: residues of the rows mod 8 and 16 against the 2-adic valuation of the
slot distance.

**Reading the eight-row witness with Lemma 8.** Call an odd row r *safe* if r = 1, r = 3 mod 4 or
r = 1 mod 16: by Lemma 8 such a row is never in the family for odd slot distance d (it is not 5 mod 8,
and it is a vertex only when v2(d) >= 1). An edge {a, b} (a odd,
b even) is safe in a row-1 sea if a is safe, and safe in a row-h sea if h + 1 - b is (reflect the rows).
On eight rows the only edge safe in neither is {4, 5}. The SAT witness (4.2) has a row-1 sea holding
38, 14, 23, 12, 34, 25, 47, 36, 27, 16 and a row-8 tail holding 67, 78, 18, 58, 56; all five tail edges
are row-8 safe. The one row-5 double inside the row-1 part, 25, has neighbours 34 and 47 whose even rows
are below 5, as Lemma 8(c) requires. The unsafe edge 45 sits in the second slot, next to 38 (even row 8),
where the would-be fourth corner (-2, 4) is outside the grid. Seeding a search with this split alone
still leaves 20, 35 and 78 violations on 8, 10 and 12 rows, so Lemma 8 is one necessary ingredient
among several.

**Affine orders (negative).** Orders given by an affine map from the slot index (written as n t + r,
n = h/2) to the edge (i, j) in Z_n x Z_n all fail in a pure spacing-4 row-1 sea: the fewest violations
inside the run of doubles are 2 on six rows and 15 on eight rows (`scripts/affine_orders.py`). The
eight-row SAT order itself has 9 such violations in a pure row-1 sea; the witness needs its row-8 sea
tail and an isolated row-8 point near the start. So the row-1 sea at spacing 4 is not enough by itself
either, and the valid boards use at least one switch to a row-h sea.

**Interior plus end caps.** In a pure row-1 sea at spacing 4 no violation involves a single double: a
tilted rectangle has at most one row-1 corner, the two points of one double cannot sit on a right angle
with a row-1 point (that needs (x - y)^2 = (1 - c1)(c2 - 1), negative unless c1 = 1), and the horizontal rivals of Lemma 7 land on a
double column (squares mod 8). So every violation involves two or more doubles, and the board splits
into an interior problem (rectangles inside the run of doubles) and two end problems (landing columns
beyond the run). Local search finds both parts separately (`scripts/anneal_row1.py` for the order,
`scripts/endcaps.py` for the sea cells within 2 W_h of the ends). On six rows the order
56, 45, 34, 16, 36, 23, 12, 14, 25 has no interior violation, and flipping end cells gives a valid
6 x 51 board with 60 = m + 9 points; the caps turn the first stretch into a row-6 sea, so the board is
row 6 around the descending staircase 56, 45, 34 and row 1 after it. (Results for 8 and 10 rows: 7.)

**One-switch boards at spacing 4.** With one-column margins (as in the SAT witness) a search over the
order and the switch slot (`scripts/anneal_split.py`) finds the valid six-row board

    1,25,1,1,1,34,1,1,1,23,1,1,1,14,1,1,1,12,1,1,1,16,1,1,1,36,6,6,6,45,6,6,6,56,6

of width 35 = 4 q_6 - 1 + 2 with 44 = m + 9 points: a row-1 sea, one switch, a row-6 sea. It follows the
safety rule exactly. The row-1 part holds 34, 23, 14, 12, 16, 36, whose odd rows 1 and 3 are safe; the
row-6 part holds 45 and 56, safe after reflection (7 - 4 = 3, 7 - 6 = 1); the one edge safe in neither,
25, takes the first slot, where its dangerous corners leave the grid. On eight rows the cell-flip search
finds, independently of the SAT witness, the valid 8 x 63 board

    1,36,8,8,8,45,8,8,8,56,8,8,8,67,8,8,8,58,8,8,8,78,8,8,8,27,1,8,8,38,1,1,1,12,1,1,1,14,1,1,1,
    23,1,1,1,34,1,1,1,25,1,1,1,47,1,1,1,16,8,1,8,18,8

(79 = m + 16 points; confirmed by the fast checker and by the paper's `verify_narrow`). It is a row-8
sea holding 36, 45, 56, 67, 58, 78, 27 and then a row-1 sea holding 38, 12, 14, 23, 34, 25, 47, 16, 18.
Again every edge is safe in its sea except 45 (first slot, at the edge of the board) and 25, whose
neighbours 34 and 47 have even rows below 5, as Lemma 8(c) requires. (Ten and twelve rows: 7.)

On seven rows a search that also flips single sea cells (`scripts/anneal4.py` with one-column margins)
finds a valid 7 x 47 board (59 = m + 12 points, width 4 q_7 - 1 + 2) with order
23, 12, 16, 27, 67, 56, 47, 36, 25, 14, 34, 45. Every gap between doubles reads 1, x, 7 with x in
{1, 7}: each double has row 7 immediately before it and row 1 immediately after it. This is the
"h, double, 1, 1" family of 4.2 with the middle cell relaxed, and the SAT witness has the same local
rule. It escapes Lemma 7 for the same reason as Lemma 3: relative to a double the row-1 columns on the
far side are 1 and possibly 2 mod 4, and one of s^2 - 1, s^2 is 0 mod 4, so the lemma's corner lands on
a double column.

**Lemma 9 (the "1, x, h" family for h = 3 mod 4).** Take spacing 4, row h just before each double,
row 1 just after, and free middle cells. If h = 3 mod 4, the Lemma 6 family never fires. *Proof.*
t = (h - 1)/2 is odd, so in every factorization t^2 = a b both factors are odd and a b = 1 mod 4 forces
a = b mod 4, so p = b - a = 0 mod 4. The black points (x0, 1) and (x0 + p, h) then lie in the same
residue class mod 4. Residue 1 is always row 1 and residue 3 always row h, so both must be free cells
(residue 2), and then the ends x0 - a and x0 + b of the horizontal diagonal have residues 2 - a and
2 + a mod 4, which are 1 and 3 in some order: one end is black in row 1, the other in row h, and there
is no rival. ∎ For h = 1 mod 4, t is even and even factors a are allowed, so the family can fire. The
searches agree (`scripts/anneal_gap.py`): seven rows is found in seconds (a second valid 7 x 47
board), six rows bottoms out at 6 violations, nine rows at about 60, while eleven rows keeps improving
(15 violations after a few minutes; final result in 7).

**Lemma 10 (one-double right angles in the "1, x, h" family, h odd).** A tilted rectangle with one
double point d = (0, c), one row-1 point u = (x1, 1) and one row-h point v = (x2, h) (at most one of each
by F1) can only have its right angle at d (at u or v the fourth corner leaves the grid), which needs
x1 x2 = (c - 1)(h - c). Its fourth corner is (x1 + x2, 1 + h - c), whose row has the parity of c.
- If h = 1 mod 4, take c the even row of the edge. Then (c - 1)(h - c) = 3 mod 4, so x1 = 1 (the
  fixed row-1 cell) and x2 = (c - 1)(h - c), which is 3 mod 4 (a fixed row-h cell), give a right angle
  whose fourth corner lies in column 1 + x2 = 0 mod 4, a double column, where Lemma 5 gives a rival.
  So every double of a long board is killed, and the family is impossible for h = 1 mod 4.
- If h = 3 mod 4, then (c - 1)(h - c) = 1 mod 4 for even c and = 0 mod 4 for odd c. The first cannot
  be a product x1 x2 with x1 = 1 or 2 and x2 = 3 or 2 mod 4 at all (the products are 3, 2, 2, 0 mod 4;
  the residues are the same on the left of d, where the product of two negatives is positive), and the
  second needs x1 = x2 = 2 mod 4, two free cells, with the fourth corner on a double column. So the
  only one-double events use two free cells and an odd-row double point. (Lemma 12 below shows that
  even these never occur.)
The classification of random boards agrees: on nine rows the largest class is single rivals with one
double corner (1.8 per double) and centre-row horizontal rivals from sea corners alone (0.42 per
double, Lemma 6); on seven and eleven rows both classes are absent, and what is left involves two
double corners. So for h = 3 mod 4 the "1, x, h" family at spacing 4 (width 4 q_h + 1) is the natural
candidate for an O(h^2) threshold, and for h = 1 mod 4 it is ruled out. For uniformly random orders and
middle cells the family still has 0.92, 1.69 and 2.54 violations per double on 7, 11 and 15 rows. On
eleven rows they are single rivals with two double corners (0.73 per double; right angles at a double
point, with the 2-adic conditions of Lemma 8 restricted to fixed cells, y = 1 mod 4), shown pairs with
two double corners (0.35, Lemma 4) and shown pairs with one double corner (0.32, which depend on the
free cells). So the order has to be designed, and the growth with h is the arithmetic an O(h^2)
construction has to beat.

**Where the spacing-4 families stand, by h mod 4.**
- h even: a row-1 sea, one switch, a row-h sea, with the edges split by the safety rule of Lemma 8.
  Valid boards on six rows (this note) and eight rows (SAT, and the annealed 8 x 63 board above).
- h = 3 mod 4: the "1, x, h" family, which escapes Lemmas 6, 7 and the fixed-cell part of Lemma 10.
  Valid boards on seven rows (SAT and annealing); eleven and fifteen rows: 7.
- h = 1 mod 4: the "1, x, h" family is impossible (Lemma 10, and the SAT run "pat11h" on nine rows is
  UNSAT), uniform alternating seas are impossible (Lemma 7), and the one-switch family is open
  (nine rows: 7 violations left after annealing). Five rows has m_5 = 8 and needs no family.

*Beyond eight rows (`scripts/dfs_gap.py`).* A left-to-right backtracking search checks each rectangle
when its last column is placed, so every prefix it keeps is valid. It finds the six-, seven- and
eight-row boards in seconds (a third 8 x 63 board). On larger heights it stalls just short of the end:
the "1, x, h" family reaches 29 of 30 doubles on eleven rows and 45 of 56 on fifteen; the one-switch
family reaches 19 of 20 on nine rows, 21 of 25 on ten and 28 of 36 on twelve (dozens of restarts each,
random, hard-edges-first and adaptive priorities). On eleven rows the edges left over are always among
{4,5}, {5,6}, {5,8}: row 5, the row that Lemma 8 constrains most (with fixed cells it forbids even rows
6 and 10 in the next double, 8 in the previous one, and 8 and 10 at slot distances 3 and 5). On nine rows (one switch) the leftovers are always row-5 edges ({2,5}, {4,5}, {5,6}, {5,8}): row 5 is the
centre row, its own reflection, and v2(5 - 1) = 2, so it is unsafe in both seas. On eleven rows in the
"1, x, h" family, where every double faces both seas, the leftovers are row-5 and row-7 edges, the two
rows with v2 = 2 on one side (5 - 1 = 4, and 12 - 7 - 1 = 4). Lemma 8 only restricts the neighbours of
such edges (it does not forbid them), so this is a diagnosis, not a proof. For h = 1 mod 4 the centre
row (h + 1)/2 is odd and self-reflected, and it is unsafe in both seas exactly when v2((h - 1)/2) is 2
or 3 (h = 9, 17, 25, 41, 49, ...). Forcing one row-5 edge into the first slot and one into the last
(where corners leave the grid) does not help on nine rows: the search still stalls at 19 of 20. So the
rigid families may well fail from nine rows on, and the O(h^2) question stays open; a construction
probably needs the freedom of the SAT boards (sea cells chosen per column).

*Update (09:40): the "1, x, h" family works on eleven rows.* Seed 23 of the backtracking search found a
valid 11 x 119 board, 30 doubles at spacing 4 with sea pattern "1, x, 11" in every gap
(`data/dfs_gap_h11_s23.json`, order (5,10), (1,4), (1,6), (6,11), (4,5), (3,4), (2,11), (2,3), (10,11),
(5,6), (4,11), (2,5), (4,9), (1,2), (2,9), (9,10), (8,11), (6,7), (1,8), (3,10), (8,9), (7,8), (2,7),
(3,6), (1,10), (3,8), (7,10), (5,8), (4,7), (6,9)). It has 149 = m + q_11 points, it is valid by
verify_narrow (`scripts/verify_h11.py`), and with the upper bound m + q_h it gives f(11,119) = 149.
So the diagnosis of the preceding paragraph was too pessimistic for h = 3 mod 4: the leftover row-5
and row-7 edges can be placed, with enough restarts (14471 nodes in the successful run). This is the
case Lemmas 9 and 10 single out, and it is a valid board of width 4 q_h - 1, of order h^2, on eleven
rows. It is not yet a threshold: the board tolerates at most two extra columns on each side (row 1 or
row 11), well short of the W_11 = 26 that the collar theorem needs, so it gives f(11,m) = m + 30 only
for m = 119, 120, 121 (plus the two-sided cases we did not test). A padded version of the search, with
W_11 sea columns fixed at both ends (`dfs_gap_pad.py`), is running.

**Lemma 11 (pad lemma).** Put a row-1 sea of any length on the left of a board (columns < 0) that uses
every pair of F. Then:
(a) No right angle (A, B, C) of black cells may have its completion X = A + C - B in a pad column on an
even row (the pad column is black at row 1 and {1, r} is in F, so the double {1, r} gives an
axis-aligned rival, Lemma 5), nor on row 1 (X would be black: a hidden rectangle). So every completion
that falls left of the board must land on an odd row >= 3.
(b) In particular (A in the pad): for black board cells B = (bx, by) and C = (bx - e, by + d) with
e >= 1, d odd and e | (by - 1) d, the cell A = (bx - (by - 1) d / e, 1) is in the pad as soon as
(by - 1) d / e >= bx + 1, and then X = A + C - B lies in the pad on the even row 1 + d. This is the
only way a pad cell can be a corner of a single-white rectangle completing into the pad: a pad cell
can't be the right-angle vertex (both legs point right and up, so their dot product is positive) and
two pad cells can't be corners (adjacent ones force an axis-aligned rectangle inside the pad, diagonal
ones put X below row 1).
*Check.* On seven rows, pad + {1,2}, 1, 1, 7, {3,4}: the completions into the pad on even rows are
exactly B = (4,4), C = (3,7), A = (-5,1), X = (-6,4) (case (b), e = 1, d = 3) and the all-board right
angle B = (4,3), A = (0,2), C = (3,7), X = (-1,6) (case (a)); the remaining ones are axis-aligned with
the double {1,2} and harmless.

*Corollary (graded boundary layer).* Take e = 1 in (b): a double at column bx whose even row b sits
directly right of a row-h cell (odd distance d = h - b) is killed unless bx >= (b - 1)(h - b). In the
"1, x, h" family every double is preceded by row h, so near a row-1 left pad a double with even row b
can sit only at column >= phi(b) = (b - 1)(h - b). The largest value is t^2 = (h - 1)^2 / 4 (centre
row) and the smallest is h - 2 (rows 2 and h - 1). On eleven rows phi = 9, 21, 25, 21, 9 for
b = 2, ..., 10, so the first three slots of the family (columns 0, 4, 8) can hold no double at all.
This proves the observations: "1, x, h" right after a row-1 pad dies at the second double on seven
rows (all 264 cases), and the found 11 x 119 board can't be padded. By the 180-degree rotation, which
maps the "1, x, h" family to itself and a row-1 left pad to a row-h right pad, the same holds at the
right end with row-1 cells directly after the doubles.

So a collar-extendable board in this family has a boundary layer of width about t^2 = W_h - 1 at each
end, of order h^2 like the board itself, inside which the rule "row h directly before a double" is
replaced. The natural replacement is a row-1 sea (row 1 is below every cell, so case (b) with B or C
in the sea never fires), with its doubles subject to the 2-adic row-1 safety rule of Lemma 8; then
come the interior "1, x, h" gaps, and a mirror row-h layer at the right end. This is the same shape
as the even-h boards (row-1 sea, switch, row-h sea), with the switch region widened to an interior
band. A layer of width W_h at spacing 4 holds about h^2/16 of the q_h = h^2/4 doubles, and the doubles
the layer must avoid are graded: a double with even row b is excluded from the "1, x, h" part only
in its first phi(b) columns, so the extreme rows (b = 2, h - 1) can enter the interior band almost at
once and the centre rows last. Seven rows confirms the shape: with three free transition gaps at each
end and "1, x, h" in between, valid collar boards exist (the lazy solver of section 8 finds them in
seconds, and finds one with a single free gap at each end).

### 4.5 Toward a validity proof for the "1, x, h" family (h = 3 mod 4)

Setting: h = 2k + 1 = 3 mod 4, t = k odd, doubles e_j = {o_j, ε_j} (o odd, ε even) at columns 4j,
then row 1 at 4j + 1, row x_j in {1, h} at 4j + 2, row h at 4j + 3. Every pair of F occurs once. We
look at the interior (all corners at least W_h columns from the ends; the ends are handled by
Lemma 11). Columns = 0 mod 4 are *double columns*, the others *sea columns*.

**Fact G (roles).** Write a tilted rectangle as bottom B, right R = B + u, left L = B + v, top T, with
u = (a, b), v = (-c, d), a, b, c, d >= 1, ac = bd. Rows strictly increase from B to the middle corners
to T, so a black cell in row 1 can only be B and one in row h only T, and a black middle corner is a
double cell (interior rows are black only in double columns). In particular a rectangle has at most
two black sea corners, and if it has two they are B (row 1) and T (row h).

**Lemma 12 (no one-double right angles, h = 3 mod 4).** No tilted rectangle has three black corners
of which exactly one is a double cell. *Proof.* By Fact G the double cell d = (0, c) is a middle corner
and the other two black corners are B = (x1, 1) and T = (x2, h), so the right angle is at d and
x1 x2 = (c - 1)(h - c). Relative to d, row-1 sea cells sit at residues 1 or 2 mod 4 and row-h cells at
3 or 2, so x1 x2 is 3, 2, 2 or 0 mod 4, and it is 0 mod 4 only when x1 = x2 = 2 mod 4, and then
x1 x2 = 4 mod 8. If c is even, (c - 1)(h - c) = 1 mod 4. If c is odd, one of c - 1, h - c is 2 mod 4
and the other 0 mod 4 (their sum h - 1 is 2 mod 4), so (c - 1)(h - c) = 0 mod 8. Neither value is
possible. ∎
(For h = 1 mod 4 this family is exactly what kills the "1, x, h" layout, Lemma 10.)

**Lemma 13 (sea-only rectangles, h = 3 mod 4).** If a tilted rectangle has black corners B and T in
the seas and white middle corners, its presentation {L, R} has a rival only through double cells:
either an axis-aligned rectangle whose two other corners are double cells, or a tilted rectangle
with at least one black double corner. *Proof.* The shared-row case (L and R on the centre row, both
columns sharing a sea row) is Lemma 9. A tilted rival with diagonal LR and sea endpoints would need
the crossed diagonal (x_T, 1), (x_B, h), that is, a sea column black in both rows 1 and h, which
does not exist. A tilted rival with LR as a side has its two black corners adjacent, so they can't be
B and T, and two row-1 or two row-h corners are excluded by Fact G. An axis-aligned rival on L and R
needs the cells (x_L, y_R) and (x_R, y_L), which are on interior rows. ∎

So **every interior violation involves at least two double cells**, counting the corners of the
rectangle and of its rival together. This follows from Lemmas 9, 12 and 13, together with the
Lemma 7 type found in the classification of random boards, whose rival corner is the second double.
(The classification by corner role and cell kind on random 11- and 15-row boards finds no other
type.) Validity of the interior is therefore a list of conditions on pairs and triples of doubles
together with the cells x_j, and it is local:

**Lemma 14 (locality).** A tilted rectangle in an h-row grid spans at most W_h = 1 + t^2 columns
(a + c <= 1 + ac and ac = bd <= t^2 since b + d <= h - 1), and an axis-aligned rival of a two-white
presentation uses the same columns. So two doubles interact only if they are at most floor(W_h / 4)
slots apart, about h^2/16, and the conditions on slot j involve x-cells within W_h columns of it.

**The adjacent-pair rules (slot distance 1).** Let e at column 0 and e' at column 4 be consecutive,
r in e and r' in e' rows of opposite parity, and x = x_j the cell at column 2.
- (A) Knight rule (Lemma 1, the 3-4-5 triangle): |r - r'| = 3 with 2 <= min and max <= h - 1 is
  fatal; the exposed vertical pair is in the x-column. There is no even-dy analogue (16 + dy^2 is
  never a square for dy even and nonzero).
- (B) Right angle at the x-cell: if x = 1, rows 2 and 5 split between e and e' are fatal (vertex
  (2, 1), legs (-2, 1) and (2, 4), fourth corner (2, 6) on an even row of a row-1 sea column); if
  x = h, rows h - 1 and h - 4 split are fatal (the half-turn image). The fixed cells give products
  x0 (4 - x0) = 3, whose row pairs {2, 4} and {h - 1, h - 3} have equal parity and are harmless.
- (C) Horizontal rival through the fixed row-h cell (the Lemma 7 type): e containing the odd row
  h - 4 and e' containing h is fatal (diagonal (0, h - 4)-(3, h), the 3-4-5 triangle, ends at
  columns -1 and 4, both black in row h); by the half-turn, e containing 1 and e' containing 5 is
  fatal. The next members of this family use (6, 8, 10) (involving x_{j-1} and the double at j + 2)
  and (7, 24, 25) (only for h >= 25).
- (D) Right angles at a double point with a sea point (Lemma 8 in this layout): with vertex (0, r),
  q = (4, r') and s = (x0, 1), the number x0 = (r - 1)(r' - r)/4 must not be an integer at which row 1
  is black (x0 = 1 mod 4 always; x0 = 2 mod 4 when that x-cell is 1) while the fourth corner
  (x0 + 4, 1 + r' - r) is in the grid; for opposite parity the fourth corner has an even row and the
  rectangle is always fatal. With s = (x0, h) the same holds with x0 = -(h - r)(r' - r)/4. Since |x0|
  can be as large as about t^2, these rules tie the pair to x-cells far away. This is how the x-cells
  couple distant parts of the board, and presumably the source of the band structure (x = 1 near the
  end layers, x = h in the middle) of the eleven-row board.

**Proposition 15 (no linear order).** Write the odd rows as 2i + 1 (i in Z_{k+1}) and the even rows as
2l + 2 (l in Z_k). No order of the form j -> (a j + b mod k + 1, c j + d mod k) (a Chinese-remainder
bijection, gcd(a, k + 1) = gcd(c, k) = 1) gives a valid "1, x, h" board for h >= 7, whatever the x_j.
*Proof.* As j runs over the slots, the pair (i_j, l_{j+1}) = (i_j, l_j + c) runs over all of
Z_{k+1} x Z_k, so the odd row of each double meets every even row in the next double. In particular
some consecutive pair splits rows 3 and 6 (opposite parity, distance 3, 2 <= 3 and 6 <= h - 1 for
h >= 7), which rule (A) forbids. ∎
The same argument kills any order in which j -> (o_j, ε_{j+1}) hits a knight pair, so a valid order
must correlate neighbours. A check of all 48 Chinese-remainder orders on seven rows, with the x_j
free, agrees (all UNSAT). Concatenated staircases L_1, L_3, L_5 (any block order, each up or down)
avoid rule (A) inside each block but fail as well on seven rows (all 48 UNSAT), so rules (B) to (D)
and the junctions matter too.

**What a proof needs.** By Lemmas 12 to 14 the interior is valid if and only if the order and the
x_j avoid an explicit finite list of conditions on doubles at most W_h/4 slots apart: the Pythagorean
relations of Lemma 4 (with the residue rule), the right-angle relations (D) and their analogues at
larger distances, the Lemma 7 type (C), and the three-double right angles (16 (i - j)(k - j) =
-(r_i - r_j)(r_k - r_j), completions on double columns). Rule (A) alone says that consecutive doubles
form a path in the *knight-free graph* on the q_h edges (e -> e' allowed unless they split a knight
pair inside [2, h - 1]), and the order must be a Hamiltonian path of that graph that also meets the
longer-range relations. What is missing is an explicit, arithmetically described path. The found
boards for h = 7 and 11 show that such paths exist, but not yet their rule.

**The L_1 block with tracking seas (positive).** The middle of the nine-row core (4.1) is the staircase
L_1 = {a, a+1} descending, each double followed by two sea cells in its own lower row a. Lemma 2 (the
reflection obstruction for interior seas) needs a Pythagorean triple with leg |u - v| = 1, and there is
none, so this interior sea is safe. Tested as a block (doubles {h-1,h}, {h-2,h-1}, ..., {1,2} at
spacing 3, sea cells "a, a" after each, W_h columns of row h on the left and of row 1 on the right) with
the full pair set F = K_{odd,even} (`scripts/fastcheck_F.py`), it is valid for every h from 5 to 13.
From h = 14 on it has 1, 2, 3, 4, 5 violations (h = 14, ..., 18): points four slots apart differ by
(12, 5), the 5-12-13 triangle of Theorem 1', whose exposure fits once h >= 14. (With the other
padding choices, row 1 on both sides or row h on both sides, it fails at every h, always through the
pad meeting the top of the staircase.) So for h <= 13 the h - 1 edges of L_1 can be placed in 3h - 5
columns as one block that behaves like a single isolated double with row h on its left and row 1 on
its right. A spacing-4 version would push the first Pythagorean danger out to h = 26 (the Pell
analysis of staircases above).

*Other staircases do not form blocks (nine rows).* If every L_g had such a block, about h/2 blocks
separated by the paper's gaps of 2 W_h + 2 would give width of order h^3 instead of h^4/8 (blocks chain
when the right pad row of one equals the left pad row of the next, and isolated doubles fit in either
orientation). An exhaustive search (`scripts/block_dfs.py`: any order of the edges, spacing 3 or 4, sea
rows from {1, 9} and the rows of the two neighbouring doubles, all four pad pairs, full F) finds blocks
for L_1 and L_7 on nine rows but none for L_3 or L_5. The nine-row core of 4.1 works because it
interleaves staircases (L_1 in the middle, the others around it). So the h^3 route needs mixed blocks.

**Staircase blocks (negative).** An O(h^3) route would isolate whole staircases L_g, as the paper isolates
single doubles. With constant seas, or one switch between row 1 and row h, a contiguous L_g at spacing
2 to 6, ascending or descending, is invalid for g = 1 and g = 3 on six, seven and eight rows
(`scripts/stair_blocks.py`). Only the short staircases (g >= 5) have valid configurations. So blocks
also need interior seas.

**Towards m_h = O(h^2 log^2 h) (sketch with a gap).** A row-1 sea on both sides of sparse doubles fails
at a single double: a double point (y, a) with a odd and a Pythagorean triple (dx, a - 1, g), together
with the row-1 points (y - dx, 1) and (y - (dx +- g)/2, 1), gives an axis rectangle and a tilted one that
show the same two white points in row (a + 1)/2. Lemma 3 survives only because at spacing 4 one of those
columns is a double. So start from the paper's alternating seas instead (row 1 to the left of each
double, row h to the right, switching at every double), where an isolated double is valid (the
Proposition on alternating seas). Put the doubles in every 4t-th column and assign the q_h edges to the
slots by a uniformly random bijection. Every violation is then an event that depends on the edges of at
least two and at most four slots, all within W_h columns of each other. For two-slot families of the kind in the design problem (we have not redone that list for
alternating seas), the expected number of bad partners of a given double is O(log^2 h / t): vertical dangers need 4td < h, and horizontal and
right-angle dangers need j (4td - j) <= h^2 for some j >= 1, with divisor-sum weights. The lopsided local
lemma for random permutations (Lu and Szekely) then gives a valid order once t >= C log^2 h, provided the
three- and four-slot families (repeated oblique presentations) also contribute O(1/C) per double. That
would give m_h <= 4 t q_h + O(h^2) = O(h^2 log^2 h), against the paper's M_h ~ h^4/8. The gaps are the
event list for alternating seas at spacing 4t, a check that every two-slot event has probability
O(polylog h / h^2) rather than a constant (a deterministic two-slot event would break the argument), and
the bound for the three- and four-slot events.

*Update: the base fails.* Lemmas 6 and 7 are exactly such deterministic events. By the corollary to
Lemma 7, for every h, uniform alternating gaps fail for every edge order at every gap from 9 up to about
W_h, so spacing 4t with t a power of log h is ruled out (only 4t = 4 and 8 escape). A row-1 sea with
sparse doubles fails at a single double. A row-1 sea at spacing 4 has only random events (Lemma 3),
but about log^2 h of them per double, which is too many for the local lemma. So the probabilistic route
needs a base pattern with no deterministic failures at spacing polylog h, and we do not know one. The
SAT boards for h <= 8 (a row-1 sea followed by a row-h sea, or "h, double, 1, 1") are the only evidence
that such bases exist.

**The complete three-corner law.** Write σ(r) for the *active side* of an odd row r not in {1, h}:
σ = 1 if r = 1 mod 4 and σ = h if r = 3 mod 4. Since (r - 1) + (h - r) = h - 1 = 2 mod 4, exactly one
of r - 1, h - r is divisible by 4, and |r - σ| = 2^τ u with u odd and τ = τ(r) >= 2. Rows 1 and h
are inert (they are never the vertex of a right angle with a sea corner). Call r *hot* if τ(r) = 2,
and put w(r) = u if σ = 1 and w(r) = -u if σ = h, taken mod 4.

**Proposition 16 (three black corners, h = 3 mod 4).** In the interior, a tilted rectangle with
exactly three black corners and white fourth corner X is fatal (X has an axis-aligned rival) exactly
in the following cases.
- (i) Three double corners. The completion lies on a double column, so it is fatal whenever it is in
  the grid: 16 (i - j)(k - j) = -(r_i - r_j)(r_k - r_j) with vertex slot j.
- (ii) Law (D): the vertex is a double point (4i, r) with r odd, the other corners are a double point
  (4(i + d), e) with e even on the far side of r (e > r if σ(r) = 1, e < r if σ(r) = h) and a sea
  cell in row σ(r). Then v2(d) = τ - 2 or τ - 3.
  - If v2(d) = τ - 2, write d = 2^(τ-2) d'. The sea corner is a fixed cell, and the rectangle exists
    and is fatal exactly when d' divides u (e - r) and
    e = 1 + u d' (mod 4) if σ = 1,   e = 3 + u d' (mod 4) if σ = h.
  - If v2(d) = τ - 3, the sea corner is the middle cell at column 4i + (r - 1)(e - r)/(4d) (σ = 1)
    or 4i - (h - r)(e - r)/(4d) (σ = h), and it is fatal exactly when that cell has the value σ.
- (iii) Law (E2): the vertex is a middle cell with value σ, and the other corners are a hot odd row o
  with σ(o) = σ and an even row e, in doubles at slots i < j with D = j - i. Writing |o - σ| = 4u, the
  rectangle exists when u |e - σ| = p q with p + q = 2D (p, q odd), the vertex is at column 4i + 2p,
  and the fourth corner is in the grid (o + e <= h + 1 if σ = 1, o + e >= h + 1 if σ = h).
- Nothing else. One double and two seas is Lemma 12. A sea vertex with two even rows e, e' needs
  (e - 1)(e' - 1) = c (4D - c) with the vertex at a fixed cell, and its completion is a white odd-row
  sea cell (harmless) unless e + e' = h + 1, when the rectangle would be hidden; but then
  (e - 1)(h - e) = 1 mod 4, so every factor pair has sum 2 mod 4, never 4D. A sea vertex with two odd
  rows needs (o - 1)(o' - 1) = 4 mod 8 at a middle cell, which forces o + o' = 2 mod 4, so the
  completion is a white odd-row cell.

*Proof.* By Fact G a sea corner is B or T, so a right angle with a sea corner either has its vertex at
a double point (case ii) or at the sea corner (case iii and the last bullet). For (ii) with σ = 1 the
vertex condition is 4d (x0 - 4i) = (r - 1)(e - r) with x0 the sea column. Relative to a double, row 1
is black at offsets 1 mod 4 and at the middle cell when x = 1, so x0 - 4i is 1 mod 4 (fixed cell) or
2 mod 4 (middle cell). Since e - r is odd, v2(r - 1) = v2(d) + 2 or v2(d) + 3, and r must be odd with
σ(r) = 1. In the first case x0 - 4i = u (e - r)/d' must be an odd integer that is 1 mod 4, that is
u (e - 1) d' = 1 mod 4 (using 1/d' = d' mod 4 and r = 1 mod 4), which is the displayed congruence.
The fourth corner is (x0 + 4d, 1 + e - r): it is in the grid iff e > r, it lies on a sea column, and
its row is even, so Lemma 5 gives the rival. Same-parity partners give an odd row and no rival. The
case σ = h is the half-turn image (even rows map to h + 1 - e = -e mod 4, and d to -d). For (iii) the
legs from a middle cell are 2 mod 4, so the product of the offsets is 4 mod 8, which forces one row odd
with v2(o - σ) = 2 and the other even, and then c/2 and 2D - c/2 are the factors p, q. ∎

*Check (`v1laws.py`, `lawD_mod4.py`, random boards).* Every three-corner violation on random boards
with 7, 11 and 15 rows falls under (i), (ii) or (iii) (0 exceptions among about 800), and the
fixed-cell part of (ii) predicts the checker's list exactly on 11, 15 and 19 rows (32, 92 and 172
events; the one extra prediction is reported by the checker as a repeated presentation, since another
rectangle has the same white corner).

So the fixed cells contribute (i) and the congruence form of (ii), conditions on the order alone, and
the middle cells enter through (iii) and the second half of (ii), which say "this middle cell must not
be σ". This is the band structure of the eleven-row board: σ = 1 pairs (hot row 5) push x to h, and
σ = h pairs (hot row 7) push x to 1. In that board the pairs 7.2 at slot 4 and 11.8 at slot 6 force the
middle cells of gaps 4 and 5 to be 1 (case iii with D = 2), as they are.

**Proposition 17 (the middle cells are a 2-SAT problem).** For a fixed order, every interior violation
depends on at most two middle cells, so the admissible middle cells are the solutions of a 2-SAT
formula: valid middle cells exist iff its implication graph has no cycle through a literal and its
negation. *Proof for at most one white corner.* A hidden rectangle has at most two sea corners (B and
T). With three black corners and white X, at most one black corner is a sea cell, since two sea
corners would leave a single double (Lemma 12). X itself is not a variable cell: X in row 1 would be
B with the right angle at T, which is the impossible e + e' = h + 1 case of Proposition 16, and
symmetrically for row h. A one-white rival adds only X's own column and a double column, and a second
rectangle with the same white X adds at most one more sea corner.

*Proof for two white corners.* Three facts. (F1) In a tilted rectangle only the lowest corner B can
be in row 1 and only the highest corner T in row h. (F2) A cell in rows 2 to h - 1 of a sea column is
a constant white cell, so a variable cell is a cell in row 1 or h of a middle column, and every rival
cell in an interior row must lie on a double column. (F3) All cells of one middle column are one
variable. By (F1) and (F2) the rectangle itself involves at most the columns of B and T. Let the
whites be W1 = (x, r) and W2 = (z, s).
- x = z: the rival test is membership of {r, s} in F, a constant.
- r ≠ s and x ≠ z: the rival cells are (x, s) and (z, r), in the columns of the whites. If the whites
  are B and T, they add nothing new. If they are L and R, both rival cells are interior, so x and z
  are double columns. If they are B and L (or any other side), the rival cell (x_B, y_L) is interior,
  so B is on a double column and is constant, and the only new column is x_L, while the blacks are T
  and a corner in an interior row (a double). In every case at most two middle columns occur.
- r = s: the whites are L and R (two corners of a tilted rectangle in one row are opposite), and the
  rival asks for a common black row in columns x_L and x_R. Suppose three middle columns occur. If B
  and T are both middle cells (rows 1 and h), the horizontal diagonal LR has length D with
  D^2 = P^2 + (h - 1)^2, where P = x_T - x_B = 0 mod 4. Since (h - 1)^2 = 4 k^2 with k odd, D = 2 mod 4.
  Then x_L, x_R = M_x -+ D/2 with M_x even, so L and R are on fixed columns of different kinds
  (offsets 1 and 3), which share no black row, and there is no rival. If B, L, R are middle cells,
  then x_B = M_x - α = 2 mod 4 with M_x = 2 + D/2 and D = 0 mod 4 forces x_T = M_x + α = 2 mod 4, so T is a
  middle cell too, and all four are, which needs (D - P)(D + P) = 4 k^2 with both factors = 0 mod 4,
  so k even, a contradiction. The case T, L, R is the half-turn image.
- Tilt-tilt (a second rectangle with the same whites). If the whites are B and T of the first
  rectangle, they are the lowest and highest corners of the second as well, so its blacks are
  interior and are doubles. If the whites are L and R and LR is a diagonal of the second rectangle,
  its other corners lie on the circle with diameter LR. A row-1 corner of it is the mirror image of B
  in the vertical line through the centre, so it is in column x_T, and its row-h corner is in column
  x_B, which adds no new column. If LR is a side of the second rectangle, its new corners P and Q
  differ by the vector LR, so they can't be in rows 1 and h at once. Three middle columns then need
  B, T and one of P, Q to be middle cells. With B and T middle cells, R - L = (D_x, D_y) has
  D_x^2 + D_y^2 = 4 mod 16 and M_x = 2 mod 4. If D_x/2 is odd, L is on an odd column and so is P. If
  D_x/2 is even, P and Q are in the same class mod 4, so Q is a middle cell too, in an interior row,
  hence white, and the second rectangle presents three whites. If the whites are B and L, the second
  rectangle either has BL as a side (its top corner is then in row h only if it is the first
  rectangle) or as a diagonal (its lowest corner is B, its highest is L, and the other two are
  interior), and nothing new appears. ∎

So, for h = 3 mod 4 and a fixed order, the middle cells form a 2-SAT problem, and that is now a
theorem. The counts of `midcount.py` (none of about 1,700 violations on random 11-, 15- and 19-row
boards uses more than two middle cells) agree.

**Proposition 18 (a slot rule that removes the hot part of law D).** Suppose that, in the interior,
(a) every double whose odd row is hot sits at an even slot, at a slot = 0 mod 4 if w = 1 and = 2 mod 4
if w = 3, and (b) every double at an odd slot has a non-hot odd row and an even row = 0 mod 4 at slots
= 1 mod 4 and = 2 mod 4 at slots = 3 mod 4. Then no hot row is ever the vertex of a law-(D) event.
*Proof.* For a hot vertex v2(d) = 0, so d' = d is odd and the partner is at an odd slot, whose class is
fixed by the slot mod 4. For w = 1 at slot 0 mod 4, the partner at offset d = 1 mod 4 has e = 0 mod 4,
while the fatal class is 1 + u d = 2 (σ = 1, u = 1) or 3 + u d = 2 (σ = h, u = 3); for d = 3 mod 4 the
partner has e = 2 and the fatal class is 0. The case w = 3 is the same with the residues shifted by 2. ∎

This is row arithmetic mod 4 replacing locality: the hot rows are about half of the odd rows, and the
rule disposes of all their events at every distance at once, whatever the sizes. *Counting.* The rule
is feasible exactly when h = 3 mod 8. With k = (h - 1)/2, the hot rows number (k - 1)/2 if k = 1 mod 4
(h = 3 mod 8) and (k + 1)/2 if k = 3 mod 4 (h = 7 mod 8). In the first case the hot edges fill
k (k - 1)/2 of the k (k + 1)/2 even slots, and the (k + 3)/2 non-hot rows supply (k^2 + 2k - 3)/4 edges
of class 0 mod 4 and (k^2 + 4k + 3)/4 of class 2 for about (k^2 + k)/4 odd slots of each kind, so
there is room. In the second case the hot edges fill every even slot, and the odd slots are left
with (k^2 - 1)/4 class-0 edges for about (k^2 + k)/4 slots, short by about k/4. On seven rows this
is visible at once: the odd slots would have to hold only edges through rows 1 and 7, and only two of
those have even row 4.

*What the rule cannot do.* A τ = 3 vertex needs d = 2 d' with d' odd, so its partners are at slots of
its own parity. The hot rows fill most even slots, so the τ = 3 rows (about a quarter of the odd rows)
sit at odd slots, where the class is constant along i + 2 + 4Z. So exactly one of the slots i + 2,
i - 2 (and its continuation at distances 2 d' with d' in one residue class mod 4) carries the fatal
class, and there the condition must be met by size: that double's even row must lie on the near side
of r, or d' must not divide u (e - r). No slot-residue rule can protect τ = 2 and τ = 3 at once, since
the first forces period 4 on the odd slots and the second needs period 8 along them. Rule (A) is not
removed either: for a hot vertex with w = 1 the safe class at the right neighbour is 0 mod 4, which
is also the class of the knight row r + 3.

*Test on eleven rows (11 = 3 mod 8).* Imposing the rule on the interior slots of the hybrid layout
(lazy solver, `RULE=mod4:j0` with the rule's residues shifted by j0) gives: with three transition gaps
at each end, UNSAT for every offset; with four, UNSAT at once for offsets 0 and 3 and valid 11 x 169
collar boards for offsets 1 and 2 (`data/cegar_h11_mod4_j1_t4.json`, `data/cegar_h11_mod4_j2_t4.json`,
both valid by verify_narrow, found in under three minutes); with five, valid boards for offsets 1 and
2 as well. So the slot rule is compatible with validity on eleven rows: every hot row is placed by
residue alone, and the solver only has to arrange the rest.

**Law (D) in one congruence.** For odd u and d', (u - 1)(d' - 1) = 0 mod 4, so u d' = d' + u - 1 mod 4.
With this, both halves of the fixed-cell case of Proposition 16 (ii) read the same way: the event at
distance d = 2^s d' (s = τ - 2, d' odd) is fatal by class exactly when

  e = w + d' (mod 4),

and the class w + d' + 2 is safe. (For σ = 1, 1 + u d' = u + d' = w + d'. For σ = h, 3 + u d' = 2 + u + d'
and u = -w, 2 - w = w mod 4.) Call s the *level* of the vertex and P(a) = a + 2^s (2Z + 1) the
*progression* of a vertex at slot a: these are the slots of its partners, and the class each one
must avoid is a function of the slot alone, w + (j - a)/2^s.

**Proposition 19 (the 2-adic slot rule).** Give the double at slot j an even row of class
c(j) = o(j) - 1 (mod 4), where o(j) is the odd part of j. Then a vertex of level s and type w at slot a
is protected by residue from every fixed-cell law-(D) event, at every distance at once, if and only
if v2(a) >= s + 2 (w = 1) or v2(a) = s + 1 (w = 3). *Proof.* If v2(a) > s, every partner j = a + 2^s d'
has v2(j) = s and o(j) = a/2^s + d', so c(j) = a/2^s + d' - 1, which is the safe class w + d' + 2 for
every d' exactly when a/2^s = w - 1 mod 4. If v2(a) <= s, the partners have v2(j) = v2(a) (or larger
when v2(a) = s), and c(j) is constant on the classes d' = 1 and d' = 3 mod 4, or unrelated to d', while
the safe class alternates. ∎

For s = 0 this is Proposition 18: hot rows with w = 1 at slots 0 mod 4, with w = 3 at slots 2 mod 4,
and odd slots of class j - 1. The point of the general form is that one class function serves every
level, because a partner of a level-s vertex always has v2 = s. It is not a construction, for a
counting reason: slots with v2 = 0 can carry no protected vertex, they are half of all slots, and only
the 2k edges through rows 1 and h are inert.

**Proposition 20 (residues can't protect everything).** Ignore the size conditions of law (D) (far
side, divisibility, grid).
- (a) Two vertices of the same level s at slots a = b mod 2^(s+1) make the same demands on
  P(a) ∩ P(b) iff (b - a)/2^s = w_b - w_a mod 4. For other a, b of the same level the progressions are
  disjoint.
- (b) If b lies in P(a) and b has the higher level s' > s, the two slots b + 2^(s') d'' and
  b + 2^(s') (d'' + 2) both lie in P(a), and a demands the same class at both (the step 2^(s'+1) is a
  multiple of 2^(s+2)), while b demands different classes. So a and b can't both be protected there.
- (c) No order protects every vertex. *Proof.* By (b), a fully protected hot vertex leaves no
  vertex of level >= 1 at slots of the other parity. If hot vertices occupied both parities, there
  would be no room for the edges of level >= 1 at all. So hot vertices use one parity, all vertices of
  level >= 1 the same parity, and the other parity holds inert edges only: about q/2 slots for 2k
  edges, impossible for k >= 3. ∎

The interaction range is finite in reality (the divisibility d' | u(e - r) and the grid cut it off at
about h^2/16 slots), but it grows with h, so (c) is the honest statement: the residues mod 4 can
handle about half of the vertices, and the other half need the sizes. There is also a tight version
that needs no range argument. At |d'| = 1 the divisibility is automatic, so only the far side can
save an event.

**Lemma 21 (hot sandwich).** If slot b carries a vertex with τ = 3 and slots b - 1, b + 1 carry hot
vertices (all in the interior), then at least one of the six tight events among them (each hot
vertex with its two neighbours, the τ = 3 vertex with b - 2 and b + 2) is fatal by class, and it is
escaped only if that partner's even row lies on the near side. *Proof.* Tight protection of a hot
vertex at a means c(a + 1) = w_a - 1 and c(a - 1) = w_a + 1. At slot b this forces w_(b+1) = w_(b-1) + 2,
and then c(b - 2) = w_(b-1) + 1 = w_(b+1) - 1 = c(b + 2). The τ = 3 vertex needs c(b + 2) = w_b - 1 and
c(b - 2) = w_b + 1, which differ. ∎

**What the sizes have to do under the slot rule.** At an odd slot i, a vertex of level s >= 1 sees the
constant class i + 1 (s = 1) or i - 1 (s >= 2) mod 4 at all its partners. So it is fatal by class exactly
for d' = δ mod 4, with δ = i + 1 - w (s = 1) or i - 1 - w (s >= 2). One tight partner, at i + 2^s δ
with δ = ±1, is always class-fatal and must have its even row on the near side. The rest of the class
(|d'| = 3, 5, ...) needs the near side or d' ∤ u (e - r). For τ = 3 the tight pointers form a fixed
pattern of slots mod 8: for w = 1, slots 1 and 3 point at each other, and so do 5 and 7; for w = 3, slots
1 and 7 point at each other, and so do 3 and 5. The near side is shortest for the rows closest to their
active side (row 9 when σ = 1 must see an even row in {2, 4, 6, 8} at its tight partner), so these rows
decide the size design.

*Check on the two eleven-row boards (`tight.py`).* In the interior, every class-fatal tight event
is escaped by the near side (13 and 12 events), and the class-fatal events at |d'| >= 3 are escaped
by the near side (40 and 43) or by non-divisibility (28 and 38). The only fatal-looking events have a
corner in a transition gap, where law (D) does not apply.

**Lemma 22 (the range of law (D) is phi / 4).** A law-(D) event with vertex row r joins doubles at
most phi(r)/4 slots apart, where phi(r) = (r - 1)(h - r) is the function of Lemma 11. *Proof.* For
σ = 1 the far side is r < e <= h - 1. In the fixed-cell case d' divides u (e - r), so
|d| = 2^(τ-2) |d'| <= 2^(τ-2) u (h - 1 - r) = (r - 1)(h - 1 - r)/4. In the middle-cell case the sea
column 4i + (r - 1)(e - r)/(4d) is at offset at least 2 from the vertex, so |d| <= (r - 1)(h - 1 - r)/8.
The case σ = h is the half-turn image, with (h - r)(r - 1), the same product. ∎

So the rows next to the boundary (r = 3 or h - 2, phi = 2(h - 3)) interact over about h/2 slots and the
centre rows over about h^2/16, the same grading as the boundary layer of Lemma 11.

**Lemma 23 (the window principle).** Call the odd slots = 1 mod 4 track A and those = 3 mod 4 track B
(under rule (b), track A carries even rows = 0 mod 4 and track B rows = 2 mod 4). A non-hot vertex r
at an odd slot has its fixed-cell law-(D) partners at distance 2^(τ-2) times an odd number: on the
other track if τ = 3, and on its own track if τ >= 4. If every double on that track within phi(r)/4
slots has its even row on the near side of r (below r for σ = 1, above r for σ = h), the vertex has
no fixed-cell law-(D) event at all, whatever the classes and the divisibilities. *Proof.* The far
side is part of every event (Proposition 16), and the range is Lemma 22. ∎

This is the size half of the design, and it does not use the residues: it protects a vertex at
every distance at once, as the slot rule does for the hot rows. A block of slots can satisfy it for
all its vertices in three ways. Write E_A and E_B for the even rows on the two tracks inside the block.
- *Band:* E_A and E_B both in a window [E1, E2], every σ = 1 vertex above E2, every σ = h vertex below
  E1. It holds non-inverted edges only.
- *Zig-zag, A low and B high:* σ = 1 vertices are τ = 3 on track B or τ >= 4 on track A, all above
  max E_A; σ = h vertices are τ = 3 on track A or τ >= 4 on track B, all below min E_B.
- *Zig-zag, A high and B low:* the same with the tracks exchanged.

Since rule (b) fixes the track of an edge by the class of its even row, every edge through a τ = 3
row fits one of the zig-zag types, *inverted or not* (for example σ = 1, τ = 3 with e = 2 mod 4 goes to
track B of an "A low, B high" block, whatever the size of e). A τ >= 4 edge fits only if it is
non-inverted, because its own even row sits on the track it points at. So the size design comes down
to two concrete problems: placing the inverted τ >= 4 edges (about q/8 of all edges) as isolated
outliers whose even row is harmless to the vertices around them, and supplying enough small even
rows for the low tracks next to the σ = 1 rows near their active side (row 9 needs track A rows in
{4, 8} within 2(h - 9) slots, and only about k edges at odd slots have those even rows).

*Mixing the two mechanisms.* A vertex's own even row is never one of its partners, so a hot vertex
at an odd slot (partners at the even slots) is window-protectable whether its edge is inverted or
not. That suggests a swap: put the inverted τ >= 4 edges at even slots, residue-protected by
Proposition 19 (type w = 3 at v2 = τ - 1, type w = 1 at v2 >= τ), and move the displaced hot edges with
w = 1 to odd slots under windows. By counting (`alloc.py`) this fits for every h = 3 mod 8 up to 67
and fails from h = 99 on. The inverted edges through rows of level τ number about q 2^(-τ), and the
ones that need slots with v2 >= 4 (type w = 1 at τ = 4, and all of τ >= 5) need about 3q/32 slots
against the q/16 that exist. So for large h some inverted τ >= 4 edges have to be outliers under a
window after all, about q/32 of them.

**Where the validity proof stands.** For h = 3 mod 4 the interior of a "1, x, h" board is valid if and
only if (1) the order of the doubles avoids the order-only conditions: three-double right angles,
the fixed-cell half of law (D), the graded boundary layer of Lemma 11, and the violations that use
no middle cell (the knight rule and its relatives); and (2) the 2-SAT instance of Proposition 17 is
satisfiable. Part (2) is decided in linear time once the order is fixed. In part (1), residues mod 4
(Propositions 18 and 19) dispose of the law-(D) events of about half the vertices at every distance,
and Proposition 20 shows that no residue rule can do more. What is missing is a size design for the
other half: an arrangement of the non-hot edges at the odd slots in which each tight pointer lands on
a double whose even row is on the near side, and each longer pointer on the near side or on a
non-divisible distance. Lemma 23 reduces this to two problems: the inverted τ >= 4 edges (σ = 1 with
e > r, or σ = h with e < r), which fit no block type, and the supply of small even rows next to the
rows near their active side. The binary 2-SAT clauses are not local in general (on random boards they join gaps up to
nine apart on 15 rows, `bindist.py`), though in the two valid eleven-row boards all of them join gaps at
distance 1 or 2 (`clauses2sat.py`).

### 4.6 The order-only conditions

By Proposition 17 validity is a question about the order alone, once the 2-SAT part is satisfiable.
To see which conditions on the order are left, I drew random orders that obey the slot rule
(`residual.py`, 19 rows, interior only) and sorted every violation that uses no middle cell. There
are about 90 per board of 90 doubles. Each falls into one of the following laws, each checked
against the checker on 19- and 27-row boards.

- **(i) Three doubles** (Proposition 16 (i)): 16 (i - j)(k - j) = -(r_i - r_j)(r_k - r_j). This is the
  largest class (about 21 per board), and it absorbs several others. A fully black rectangle of four
  double points is a case of it. So is a *tilt-tilt* pair of rectangles that have two double corners
  each and share their two whites as a side of both: if K1 = W1 + v, K2 = W2 + v, K3 = W1 + v', K4 = W2 + v',
  then K1 K2 K4 K3 is a rectangle of double points. The same holds when the shared whites are a
  diagonal of both, since then K1 K2 and K3 K4 are diameters of one circle.
- **(D)** The fixed-cell half of law (D) (Proposition 16 (ii)), from the odd-slot vertices.
- **(P) Pythagorean exposure.** Doubles at slots i < j with D = j - i odd, rows a and b of opposite
  parity, one in each, and 16 D^2 + (b - a)^2 = Λ^2. The rectangle has its vertical diagonal at the middle
  column 2(i + j), in rows (a + b -+ Λ)/2. If both ends are interior it is fatal (the two whites are in
  one column with rows of opposite parity, a pair of F). If one end is in row 1 or h it is a unit
  clause of the 2-SAT. The solutions are Λ ± (b - a) = 2m and 8D^2/m with m odd dividing D^2. D = 1 gives
  only (4, 3, 5), the knight rule (A). D = 3 gives |b - a| = 5, 9, 35. (`cm_check.py`: 123 of 123.)
- **(C) Thales pairs with a boundary row.** Whites L, R in one row, B a fixed row-1 cell, T = (x_T, t) a
  double point, LR and BT diameters of one circle, so p^2 + (t - 1)^2 = n^2 with p = |x_T - x_B| and
  n = |x_R - x_L|. One of L, R is on a fixed row-1 column and the other on a double column, and the rival
  is fatal exactly when that double contains row 1, so the edge is (1, e). The half-turn gives the
  row-h version. Triples seen: (3, 4, 5), (5, 12, 13), (8, 15, 17), (9, 12, 15), (12, 35, 37),
  (16, 63, 65), (7, 24, 25), (20, 21, 29), (24, 45, 51) and others. The first is rule (C) of 4.3.
  (`c_check.py`: 48 of 48.)
- **(Q) Four double columns.** A tilted rectangle with all four corners on double columns, two black
  and two white, whose crossed cells (x_W1, y_W2) and (x_W2, y_W1) are black. This is a relation among
  four doubles, like (i).
- **(T) Collisions of harmless rectangles.** Two rectangles whose completion X is the same white cell.
  For example, a right angle at a fixed row-1 cell with two even-row double corners completes at a
  white odd-row sea cell. That is harmless alone (Proposition 16, last case) but fatal when a second
  rectangle has the same X.

So the conditions on the order are all Diophantine relations among two, three or four doubles at
slot distance at most about h^2/16, with the inert edges (1, e), (h, e) singled out by law (C). Laws (P)
and (C) have closed forms, and (i), (D) were known. (Q) and (T) are described here but not yet reduced to
closed form.

**Growth of the order-only conditions.** On random slot-rule orders (`residual.py`, interior only) the
order-only violations number 0.41, 0.94 and 1.59 per double on 11, 19 and 27 rows, and the growth is led by
law (i): 0.5, 17 and 82 three-double right angles per board. So law (i) is the first thing an explicit
order has to remove wholesale.

**Proposition 24 (a 2-adic map for the odd rows kills law (i) at odd vertices).** Write the odd row of
the double at slot j as o_j = 2 a_j + 1. Let M = 2^S divide k + 1 with M >= k/16, and put
a_j = (j mod M) + M floor(j / (kM)), so that each block of kM consecutive slots uses M odd rows, each k times
at spacing M. Then no three-double right angle has its vertex on an odd row, whatever the even rows.
*Proof.* A right angle at (4j, r_j) with legs to (4i, r_i) and (4l, r_l) needs
(r_i - r_j)(r_l - r_j) = -16 (i - j)(l - j). The absolute values of the two row differences add up to at
most h - 1: if they have opposite signs, because both leg endpoints are in the grid, and if they have
the same sign, because the vertex and the completion (row r_i + r_l - r_j) are. So their product is at most (h - 1)^2/4 and |i - j| <= k^2/16 <= kM: the
slots i, j lie in one block or in adjacent blocks. In that range a_i = a_j or v2(a_i - a_j) <= v2(i - j).
If i = j mod M, then a_i - a_j is 0 or ±M. Otherwise a_i - a_j = i - j mod M and is nonzero mod M. A leg to
an odd row then has v2(r_i - r_j) = 1 + v2(a_i - a_j) <= 1 + v2(i - j), and a leg to an even row has an odd
difference. A zero difference is impossible, since the right side is nonzero. So the left side has
valuation at most 2 + v2(i - j) + v2(l - j), less than the 4 + v2(i - j) + v2(l - j) of the right side. ∎

The same argument for the even rows would need a power of 2 dividing k, and k is odd. The counts make it
impossible at the first level: the even rows would have to split evenly by parity between even and odd
slots, but there are (k + 1)/2 even values of the index and (k - 1)/2 odd ones. *Check (`ddd.py`).* With
the map, the odd-vertex count is 0 on 15 (M = 8), 23 (M = 4) and 31 rows (M = 16), against 46 to 161 on
random orders. The even-vertex count doesn't change (2 to 125).

**Proposition 25 (the map and the slot rule exclude each other).** Proposition 24 extends to
a_j = ψ(j mod M) + M floor(j / (kM)) for any permutation ψ of Z/M that preserves v2 of differences (an
automorphism of the binary tree of residues). Every such ψ sends the even slots onto one parity class of
the index a. But the hot odd rows have a = 2 or 3 mod 4 when h = 3 mod 8, and a = 1 or 2 mod 4 when
h = 7 mod 8, so they lie in both parity classes, and rule (a) of Proposition 18 (hot rows on even slots)
fails. Without the slot rule, law (D) gets no help from residues at all. For ψ the identity and a σ = 1 partner at slot j', the
fatal class from the vertex at slot j is oddpart(j') - oddpart(j) mod 4, and both values occur among
the vertices in range. *Check.* Annealing on 15 rows inside the structure of Proposition 24 (swaps only
between doubles with the same odd row) stalls at 72 and 75 violations, against 19 for unrestricted
annealing. The excess is in laws (P) and (D) (23 and 16 against 4 and 3). So the two 2-adic mechanisms, one
for law (i) and one for law (D), compete for the same residues of the slot index, and an explicit
order has to split the residues between them.

*Search on 15 and 19 rows (`inc_anneal.py`).* An incremental annealer, whose cost is exactly the
checker's violation count, reaches 3 violations on 11 rows. From there the lazy SAT search, started on
that board's order and cells, finds a valid 11 x 169 board in 24 seconds. On 15 and 19 rows annealing
stops at 19 and 53 violations, and the warm-started SAT searches end unresolved after 90 minutes (15
rows) and 2 hours (19 rows). So no board on 15 or more rows is known in this family.

### 4.4 The decomposition into diagonal staircases

The edges of K_{odd,even} split exactly into L_d = {{a, a+d} : 1 <= a <= h - d}, d odd, with
sum (h - d) = q_h. Witnesses repeatedly lay out an L_d as consecutive or evenly spaced doubles (for
example 47, 36, 25, 14 and 23, 34, 45, 56, 67 on seven rows). The points of one staircase lie on two
parallel lines of slope 1/s, and two points on one line differ by (s k, k), whose length k sqrt(s^2 + 1)
is never an integer.

## 5. Squares

- f(8,8) >= 17. The strip rule gives 16 there, so squares gain from structures in both directions.
- If the strip rule held for squares, f(n,n) would be about 7n/3, which the deletion bound
  0.29 n^{6/5} (1 + ln n)^{-2/5} overtakes only near n = 10^7.
- Every violation is a black set of 4, 6 or 8 points (the symmetric difference of two corner sets).
  Random embedding of a generalized quadrangle followed by random deletion fails for the same reason as
  plain deletion: inside such a set the 6-point obstructions made of an L-shape and three tilted corners
  number about n^2 log n, which forces the exponent back to 6/5. GQ(2,2) on the 15 x 15 grid keeps at
  most 28 of 45 points under three random orders.
- The first idea for o(n^{4/3}) was a supersaturation lemma with equidistributed fourth corners. It
  turns out that a plain counting budget is enough; see 5.1.

### 5.1 f(n,n) = o(n^{4/3})

**The completion budget.** Call a triple (A, B, C) of black points a *black right angle* if BA is
perpendicular to BC and X = A + C - B is a grid cell; X is its *completion*. The rectangle ABCX has
X as a corner and its other three corners black. If X is white, the presentation of ABCX is {X}, so a
second black right angle completing to X would give two rectangles with the same presentation. If X is
black, ABCX is fully black, and a valid blackout has at most one of those. A rectangle and its missing
corner determine the triple (B is the corner opposite X). So in a valid blackout of an h x m grid

    T(S) := number of black right angles <= hm - |S| + 4.                           (budget)

The axis-aligned right angles are the paths of length three in the row-column graph, so the budget
restricted to them is the injection behind the girth-8 bound. The new input is that every direction
pair {w, w^perp} contributes, and their contributions add.

**Directions.** Write w = (a, b) with a >= 1, b >= 0, gcd(a, b) = 1 and s = a + b. Every right angle
has its legs along exactly one pair {w, w^perp}, w^perp = (-b, a). Inside an l x l box Q, at most s l
lines of direction w meet Q, and the same for w^perp. If B lies on a w-line with k black points of Q
and on a w^perp-line with k' black points of Q, then B is the vertex of (k - 1)(k' - 1) right angles
with legs along w and w^perp and A, C in Q.

**Line lemma.** Let a set of N points lie on L lines of one family and L lines of a second family,
each point on one line of each family. At most N/4 points lie on lines of the first family holding at
most t = N/(4L) points, and the same for the second family. So at least N/2 points lie on two lines
holding more than t points each, and the number of pairs (A on the first line of B, C on the second) is
at least (N/2)(t - 1)^2, which is at least N t^2/8 when t >= 2.

**Strips.** In a horizontal strip of n/K rows and n columns, an axis right angle completes inside the
strip. The line lemma with the two thresholds K N'/(4n) and N'/(4n) and the budget n^2/K give
N' <= 5.1 n^{4/3} K^{-2/3} + 8n for the number N' of black points in the strip.

**Theorem.** f(n,n) = O(n^{4/3} (log n)^{-1/6}). In particular f(n,n) = o(n^{4/3}).

*Proof.* Cut the grid into K^2 boxes of side l = n/K. The boxes in the outer ring lie in four strips,
which hold at most 21 n^{4/3} K^{-2/3} + 32n black points. For an inner box Q, any A, B, C in Q have
A + C - B within l of Q, so inside the grid. Let N_Q = |S cap Q|. For every w with
s <= S_Q := N_Q/(8 l), the line lemma with L = s l gives at least N_Q^3/(128 s^2 l^2) right angles
along {w, w^perp} inside Q. There are phi(s) admissible w with a + b = s (one for s = 1), and
sum_{s <= S} phi(s)/s^2 = (6/pi^2) ln S + O(1). Summing over directions and inner boxes and using the
budget,

    n^2 >= sum over inner Q of  N_Q^3/(128 l^2) * ((6/pi^2) ln(N_Q/(8 l)) - O(1)).

The inner boxes holding at least N_int/(2K^2) points each hold at least N_int/2 points together, where
N_int is the number of black points in inner boxes. By the power mean over at most K^2 boxes,

    N_int^3 <= 1024 (pi^2/6) K^2 n^4 / (ln(N_int/(16 K n)) - O(1)).

If N_int >= n^{4/3}/ln n, the logarithm is (1/3 - o(1)) ln n, so N_int = O(K^{2/3} n^{4/3} (ln n)^{-1/3}).
With the ring bound, |S| = O(K^{-2/3} n^{4/3} + K^{2/3} n^{4/3} (ln n)^{-1/3}). Take K = (ln n)^{1/4}.

*Check.* `scripts/budget_check.py` lists all black right angles of a board. On the valid 7 x 21,
7 x 23 and 8 x 72 boards the white completions are distinct and no completion is black (T = 90 + 7,
96 + 14 and 320 + 26 axis + tilted, against budgets 118, 130 and 492). A random 7 x 21 board shows 5
colliding cells.

**Theorem (Whitney refinement).** f(n,n) = O(n^{4/3} (log log n)^{2/3} (log n)^{-1/3}).

*Proof.* Use Whitney boxes: the ring of cells at distance between n 2^{-j} and n 2^{1-j} from the
boundary is covered by about 16 * 2^j boxes of side about n 2^{-j}/2, each at distance at least its side
from the boundary, so completions stay in the grid. In ring j the power mean over its boxes gives at
least c N_j^3 ln n / n^2 right angles, with no dependence on j (box count times side is about n). The
strip bound puts at most C 2^{-2j/3} n^{4/3} + O(n) points in ring j. If N = c n^{4/3}, the rings
j > j0 = (3/2) log_2 (C'/c) hold at most N/2 points, so the rings j <= j0 hold at least N/2, and
sum N_j^3 >= (N/2)^3 / j0^2. The budget gives c^3 = O(j0^2 / ln n) = O(log^2(1/c) / log n). ∎

*Remarks.*
1. The log n is the sum over directions of 1/s^2 per direction, the same log n that makes the grid
   contain about n^4 log n rectangles. The line lemma cannot do better than (log n)^{-1/3}, because a
   pseudo-random set has about N^3 log n / n^2 right angles. The Whitney refinement below gets within
   a power of log log n of that limit.
2. On h x m grids the gain shrinks fast as m/h grows. The axis part gives T_axis >= N^3/(8hm). A
   tilted direction (a, b) has about a h + b m lines and its partner about b h + a m, so it adds about
   N^3/((ah + bm)(bh + am)), which is smaller by a factor of about h/m for small a and b. Boxes do not
   help, because cutting the long rows loses the girth-8 bound itself. So the method improves
   (hm)^{2/3} only when m/h is at most a power of log h.
3. What is left between n^{6/5} and n^{4/3} (log n)^{-1/3} is a birthday-versus-pigeonhole gap. The
   budget only asks that the T(S) completions number at most n^2, but validity asks that they be
   distinct. A generalized quadrangle meets the axis part exactly (every non-incident cell is the
   completion of exactly one axis path of length three, so T_axis = n^2 - N), so it leaves no room at
   all for tilted right angles. Random-like sets have about T^2/n^2 collisions, which forces
   N <= n^{6/5}. Any construction above n^{6/5} must make tilted completions injective by structure, as
   a generalized quadrangle does for the axis ones.

4. A third route also stops at n^{6/5}. Take a linear form l(x,y) = x - lambda y and
   S = {(x,y) : l(x,y) in D}, a union of |D| lines of slope 1/lambda, each with about n/lambda cells.
   The row-column graph has girth 8 when D is a B_3 set, which allows |D| up to about (lambda n)^{1/3}.
   Four corners of a rectangle give l-values with d1 + d3 = d2 + d4, so a Sidon D forces every fully
   black rectangle to have a side along a level line. The perpendicular side is k(-1, lambda), which
   changes l by k(1 + lambda^2), so those rectangles disappear exactly when D has distinct residues mod
   1 + lambda^2. This needs (lambda n)^{1/3} <= lambda^2, so lambda >= n^{1/5} and
   |S| = |D| n / lambda <= n^{6/5}. (Completion collisions add further conditions. B_3 reduces them to
   right angles whose vertices lie on the same three level lines.)

   Random deletion, thinned generalized quadrangles and these level-line sets all stop at n^{6/5}.
   This is weaker evidence than it looks. For the axis-aligned constraints alone (girth 8), deletion
   also stops at n^{6/5}, and generalized quadrangles reach n^{4/3}: structure beats deletion there. So
   6/5 is the natural guess only if no algebraic set can make the tilted completions injective as well;
   we have no argument either way, and the only upper bound we have is the one above.

**Literature.** We found no bound for grid subsets avoiding rectangles of every orientation. The survey
of Janosik, Nador, Nagy and Simon (arXiv 2601.14465, 2026) covers axis-parallel rectangles (Reiman),
squares, parallelograms (two-dimensional Sidon sets, n + O(n^{2/3})) and rhombi
(Omega(n^{4/3} (log n)^{-1/3}) by alteration over a Sidon set of rows). Their rhombus count rests on the
O(n log n) Pythagorean pairs below n; our log factor comes from the analogous divisor-type sum over
directions, sum phi(s)/s^2.

## 6. Open problems and next steps

1. Prove the product formula for all h: primitivity of the dominant part of the sea graph and positive
   insertion weights. Corollary A4 then gives the exact form rho^m P(m) + O(rho'^m m^q), which fits the
   five-row counts to 1e-14.
2. Is rho_h unbounded? Parity-confined seas give lower bounds that still grow at h = 20 (4.17); a proof needs
   an entropy lower bound for sparse constraints spread over windows of length about h^2.
3. An explicit, provable O(h^2) construction. Uniform alternating seas are excluded (Lemmas 6 and 7 and
   the one-double right angles at gap 4). The candidate is spacing 4 with boundary seas and one switch
   from row 1 to row h, as in the SAT boards for h <= 8 and the six-row annealed boards. An order has to
   meet Lemma 4 (Pythagorean pairs), Lemma 8 (2-adic right angles), the three-double right angles, the
   landing exceptions of Lemma 3, and the end conditions within W_h of each end.
4. Exact c(7,m) for 11 <= m <= 20, with triple columns allowed, to settle the strip rule.
5. The square exponent: n^{6/5 - o(1)} <= f(n,n) <= O(n^{4/3} (log log n)^{2/3} (log n)^{-1/3}). The
   natural guess is 6/5, but the axis analogy (deletion 6/5, generalized quadrangles 4/3) warns against
   it. Beating 6/5 needs a set whose tilted completions are injective by design, the way a
   generalized quadrangle makes the axis completions injective.

## 7. Outcomes of the runs still going at the time of writing

Predictions P1 to P5 were written in the research log before the runs. "Unresolved" means the solver hit
its time cap.

| Run | Question | Outcome |
|---|---|---|
| 7 x 20, doubles from {1,4,7} vs rest | P1: m_7 = 20 | UNSAT |
| 7 x 20, parity partition {2,4,6} | P1: m_7 = 20 | unresolved (6 h cap) |
| 8 x 30, 8 x 34, 8 x 38, parity partition | P2: m_8 = 30 | unresolved at all three widths (6 h cap) |
| 7 x 17, excess 11, K_{3,4} doubles | P3: width 17 | unresolved (2 h cap) |
| 7 x 11 at 20 points, small-cells encoding | P4: f(7,11) >= 20? | unresolved |
| 8 x 8 at 18 points, encodings A and B | f(8,8) >= 18? | unresolved (both) |
| 9 x 9 at 20 and 21 points | f(9,9) | unresolved (30 min cap each) |
| nine rows, periodic boundary pattern | spacing-3 periodic boards | UNSAT |
| nine rows, "h, double, 1, 1" pattern | spacing-3 pattern | UNSAT |
| nine rows, padded spacing 3 | collar-extendable board | SAT (8365 s): f(9,m) = m + 20 for m >= 58 |
| ten rows, padded spacing 3 | collar-extendable board | first run lost when memory ran out; restarted at 07:55 (pending) |
| ten rows, spacing 4, one switch at the middle | O(h^2) family | unresolved after 6 h (stopped to free memory) |
| sequential Monte Carlo, h = 9, 10, 11 | rho_h | 3.820, 3.911, 4.201 |
| odd-row seas, h = 6 to 20 | parity closure | 2.37, 2.70, 2.89, 3.29, 3.44, 3.66, 3.79, 4.17 |
| band seas (odd rows within 4 of an edge) | fixed-width bands | 2.66, 2.04, 2.17, about 1.95 for h = 12, 16, 20, 24 |
| annealing and backtracking, spacing 4, boundary seas | O(h^2) families | valid 6 x 35, 6 x 45, 6 x 51, four 7 x 47 and two 8 x 63 boards; 9 to 15 rows stall one or more doubles short (4.3) |

## Appendix A. The count theorem, stated carefully

Fix h >= 4 and a balanced bipartition pi of the rows with edge set E_pi (|E_pi| = q_h) and pair set F_pi.
Words are over the alphabet R u E_pi (R the h singleton letters), and K = 2 W_h + 1.

*Forbidden factors.* A word of length at most K is *bad* if, in the blackout it describes (black rows of a
letter = its rows), some tilted rectangle inside it (a) has a shown set of one or two points with an
axis-aligned rival in the sense of Lemma "rival" computed with the pair set F_pi, or (b) shows the same set
as another tilted rectangle inside it, or (c) is hidden and some extension of it inside the factor (below)
makes it a symmetric difference of two other rectangles.

*Lemma A1 (localization).* Let m >= 3 and let w be a word of length m using every e in E_pi exactly once.
Then w is a valid blackout iff no factor of w of length at most K is bad, apart from the global condition
that at most one tilted rectangle is hidden. (Axis-aligned pairs are automatic; a tilted rectangle and an
axis-aligned one collide only through Lemma "rival", whose conditions involve F_pi and the columns of the
shown set; two colliding tilted rectangles both contain the shown set and lie within K columns.)

*Lemma A2 (hidden rectangles).* If R has corners p, p+v, p+w, p+v+w, then with R1 = {p, p+v, p+2w, p+v+2w}
and R2 = {p+w, p+v+w, p+2w, p+v+2w} we have C(R1) symmetric-difference C(R2) = C(R). So if one of the four
extensions (by +-v or +-w) stays in the grid, a hidden R gives two rectangles with equal presentations, and
hidden rectangles are excluded locally. Only rectangles too large in both directions escape this; the
five-row data (exponent 6, not 7) shows they do not contribute there.

*Theorem A3.* Let T be the transfer matrix of the sea graph (states: words over R of length K - 1, edges:
appending a letter without creating a bad factor), and suppose (i) T has a unique irreducible component of
maximal spectral radius rho, which is aperiodic, and (ii) for every e there is a word s e w t, with s, t
states of that component and w over R, that has no bad factor. Then
|L_pi(m)| = c_pi m^{q_h} rho^m (1 + O(1/m)), with c_pi = B_pi prod_e kappa_e as in 2.2.

*Proof sketch.* Group a word as (sea segment)(window around e_1)(sea segment)...(sea segment); the series is
the sum over the q_h! orders of l^T R(z) M_{e_1}(z) R(z) ... M_{e_q}(z) R(z) r, with R(z) = (I - zT)^{-1} and
M_e(z) the polynomial transfer through a window containing e. By (i), R(z) = v u^T / ((1 - rho z) u^T v) +
H(z) with H analytic in a disc of radius larger than 1/rho; by (ii), u^T M_e(1/rho) v > 0. The term with
q_h + 1 poles dominates, its coefficient is independent of the order, and the transfer theorem
(Flajolet–Sedgewick, Theorem VI.1) gives the asymptotics; the q_h! orders cancel the 1/q_h! of
[z^m](1 - rho z)^{-(q_h + 1)}. ∎

*Corollary A4 (exact form).* Under (i) and (ii) the series is rational: it is a finite sum of products of
the rational matrices R(z) and the polynomial matrices M_e(z). Its only singularity on |z| = 1/rho is the
pole at 1/rho, of order exactly q_h + 1, and every other pole lies at 1/lambda with |lambda| <= rho' < rho,
where rho' is the largest modulus among the other eigenvalues of T. Hence

    |L_pi(m)| = rho^m P_pi(m) + O(m^{q_h} rho'^m),   P_pi a polynomial of degree q_h,

with leading coefficient c_pi. Summing over the balanced bipartitions,
a_h(m) = sum_pi rho_pi^m P_pi(m) + O(m^{q_h} rho'^m), and the parity partition gives the dominant term.
*Corollary A5 (what a random optimum looks like).* Under (i) and (ii), let S be a uniformly random
maximum blackout of the h x m grid. As m -> infinity:
1. with probability 1 - O((rho_other / rho)^m) it uses the parity partition, where rho_other is the
   largest entropy among the other balanced bipartitions (3.4055 against 3.5439 on five rows);
2. the scaled positions p_1/m < ... < p_q/m of its q_h double columns converge in law to the order
   statistics of q_h independent uniform points on [0, 1], and the order in which the edges appear is
   uniform over all q_h! orders and independent of the positions;
3. away from the doubles, the sea converges locally to the measure of maximal entropy of the sea shift.
The reason is that the number of words with doubles at given positions in a given order is
B prod_e kappa_e rho^m (1 + o(1)) whenever all gaps tend to infinity, with no dependence on the
positions or the order, while configurations with a bounded gap have a vanishing share. In particular
the smallest gap between two doubles is of order m / q_h^2, and close pairs of doubles occur with
the frequencies of a Poisson process.

*Test on five rows.* Take rho_5 = 3.5438756463 and fit a degree-6 polynomial exactly through
a_5(m)/rho_5^m at m = 46, 49, ..., 64. The relative residuals at the other widths are 2.1e-7, 4.5e-8,
7.0e-9, 1.1e-9, 1.3e-10, 4.9e-12 at m = 30, 33, ..., 45 and stay below 1.1e-14 from m = 48 on (the floor
set by the ten digits of rho_5). They decay by about 0.58 per column, so rho' is about 2.06. The fit
gives P(m) = c_5 (m^6 - 10.25 m^5 + ...) with c_5 = 1.32152e-8; a second set of fitting points
(m = 52, 54, ..., 64) gives the same leading coefficient to six digits. This is the exact form
predicted by A4, and the earlier "(1 - 15/m)" was a cruder fit of the same second coefficient.

## 8. Files

`scripts/` (run from that folder; paths are relative to the repository):
- `fastcheck.py`: fast validity checker for singleton/double boards (agrees with verify_narrow).
- `sea_entropy.py`, `sea_graph.py`: sea shift by words and by an explicit transfer graph
  (`python sea_graph.py h A [window]`; prints the Perron root and row frequencies).
- `count_marked.py`: marked counts N_0, N_e for B_h and kappa_e.
- `smc_entropy.py`: Monte Carlo estimate of rho_h. `lambda_mc.py`: violation rates of random words.
- `five_row_dp_wide.py`: the paper's five-row counter with 256-bit slots (the original 80-bit slots
  overflow near 10^24, beyond width 44 for a_5; the published counts to width 23 are unaffected).
  `a5_oddeven.py`, `a5_fixed.py`, `a4_fixed.py` use it.
- `rows_sat.py`, `spaced_sat.py`, `fixed_sat.py`, `profile_sat.py`: structured SAT searches built on
  jis/scripts/six_row_structured_sat.py. `collar_test.py`, `adjacent_test.py`, `row1sea.py`,
  `diag_blocks.py`, `faxis.py`: smaller experiments.
- Added on the second morning: `budget_check.py` (completion budget, 5.1); `conf_tally.py`, `smc_conf.py`
  (parity-confined and band seas, 2.4); `pair_gap.py`, `uniform_alt.py` (alternating seas, Lemmas 6 and 7);
  `check_lemma8.py` (Lemma 8); `affine_orders.py`, `anneal4.py`, `anneal_row1.py`, `endcaps.py`,
  `anneal_split.py`, `anneal_safe.py`, `anneal_gap.py`, `anneal_gap_fast.py`, `anneal_alt.py`,
  `dfs_gap.py` (searches in the spacing-4 families); `stair_blocks.py`, `fastcheck_F.py`, `block_dfs.py`
  (staircase blocks, with the full pair set).

`data/`: the witnesses cited above (seven rows at widths 21 and 23, the padded eight-row board, padded six-
and seven-row boards, the structured families), the four-row marked counts, the five-row counts, the boards found on the second morning (six, seven,
eight rows at spacing 4; nine rows at spacing 3, `sp_h9_g2_L17_R17_p2468_none_11.json`), and the
running research log (`research_log.md`) with the predictions written before the runs and their outcomes.
