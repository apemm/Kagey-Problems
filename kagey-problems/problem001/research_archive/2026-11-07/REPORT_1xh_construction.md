# Problem 001: toward an explicit construction in the "1, x, h" family

Informal research report, 7 to 8 November 2026. Nothing here has been refereed. Each result is marked
as *proved*, *checked* (verified by a computation named in the text) or *heuristic*. Paths are relative
to this folder (`research/2026-11-07/`). The companion notes `REPORT.md` (sections 4.5 and 4.6) hold the
same material in running form; this report collects it in one place, with the newest results added.

## Contents

1. The question
2. Setting and notation
3. Summary of results
4. Structure of a tilted rectangle in the family
5. The complete three-corner law (Proposition 16)
6. The middle cells are a 2-SAT problem (Proposition 17)
7. Law (D) in one congruence, and what residues can do (Propositions 18 to 20, Lemma 21)
8. What sizes have to do (Lemmas 22 and 23)
9. The order-only conditions
10. Two 2-adic mechanisms that compete (Propositions 24 and 25)
11. Negative results for structured orders
12. Computations
13. Where the construction stands
14. Open problems and next steps
15. Files

## 1. The question

A blackout of the h x m grid with doubles from the parity partition uses each pair of F = K_{odd,even}
(rows at odd distance) exactly once, as the black pair of a double column, and fills the other columns
with singletons. The paper's construction proves f(h, m) = m + q_h for m at least a threshold M_h of order
h^4/8. The computations suggest that the true threshold is of order h^2. A proof of that would need, for
every h, an explicit valid board of width O(h^2) that contains all q_h doubles.

The "1, x, h" family is the most rigid candidate with width O(h^2). The doubles sit in every fourth
column, and the three sea columns between consecutive doubles are row 1, a free cell x in {1, h}, and
row h. The family is singled out by Lemmas 9 and 10 of `REPORT.md`: for h = 1 mod 4 every double is
killed by a one-double right angle, and for h = 3 mod 4 none is. Valid boards in the family exist on 7 and
11 rows. The goal of this report is an explicit order of the doubles, and a choice of the cells x, that
is valid for every h = 3 mod 4, or a proof that none exists.

That goal is not reached. What follows reduces validity to explicit arithmetic conditions on the order,
proves which of them residues can remove and which they can't, and records the searches on 15 and 19
rows.

## 2. Setting and notation

- h = 2k + 1 = 3 mod 4, so k is odd. q = q_h = k(k + 1), W = W_h = 1 + k^2.
- Slots j = 0, ..., q - 1. The double e_j = {o_j, ε_j} (o_j odd, ε_j even) is in column 4j. Then row 1 is
  black in column 4j + 1, the *middle cell* x_j in {1, h} in column 4j + 2, and row h in column 4j + 3.
  Columns = 0 mod 4 are *double columns*, the others *sea columns*. Columns 4j + 1 and 4j + 3 are *fixed
  cells*.
- *Interior* means that every corner is at least W columns from both ends. The ends are handled
  separately: free transition gaps and pads of W boundary columns (section 12).
- *Active side.* For an odd row r not in {1, h}, σ(r) = 1 if r = 1 mod 4 and σ(r) = h if r = 3 mod 4.
  Since (r - 1) + (h - r) = h - 1 = 2 mod 4, exactly one of r - 1, h - r is divisible by 4, and
  |r - σ| = 2^τ u with u odd and τ = τ(r) >= 2. Put w(r) = u if σ = 1 and w(r) = -u if σ = h, mod 4. Call
  r *hot* if τ = 2. The *level* of r is s = τ - 2. Rows 1 and h are *inert*.
- *Far side.* An even row e is on the far side of r if e > r when σ(r) = 1 and e < r when σ(r) = h, and
  on the *near side* otherwise.
- φ(r) = (r - 1)(h - r), the boundary-layer function of Lemma 11 of `REPORT.md`.
- *Tracks.* Odd slots = 1 mod 4 form track A, odd slots = 3 mod 4 form track B.
- v2 is the 2-adic valuation, and oddpart(n) = n / 2^(v2 n).

## 3. Summary of results

Proved:
1. **The complete three-corner law (Proposition 16).** In the interior, a tilted rectangle with three
   black corners is fatal exactly in three explicit cases: three double corners (law (i)), law (D) (a
   double vertex with a far-side partner and a sea corner) and law (E2) (a middle-cell vertex). Law (D)
   has a mod-4 form.
2. **The middle cells are a 2-SAT problem (Proposition 17).** For a fixed order, every interior
   violation depends on at most two middle cells. So validity is a question about the order alone,
   followed by a linear-time 2-SAT test.
3. **Law (D) in one congruence.** The fixed-cell event at distance d = 2^s d' is fatal by class exactly
   when e = w + d' (mod 4), for both active sides.
4. **Residues.** A slot rule removes every law-(D) event of the hot rows at every distance
   (Proposition 18). It is feasible by counting exactly when h = 3 mod 8. A 2-adic class function
   protects each level s on slots of a fixed valuation (Proposition 19). No residue rule protects every
   vertex (Proposition 20), and a hot-τ3-hot sandwich is always tight (Lemma 21).
5. **Sizes.** Law (D) has range φ(r)/4 slots (Lemma 22). A vertex is protected at every distance when
   the doubles on the one track it points at have their even rows on its near side (Lemma 23, the
   window principle). The edges that fit no window block are exactly the inverted edges with τ >= 4.
6. **The order-only conditions** are three-double right angles, law (D), Pythagorean exposure (P) with
   a closed form, Thales pairs through an inert edge (C) with a closed form, four-double relations (Q)
   and collisions (T).
7. **New: a 2-adic map for the odd rows removes every three-double right angle with an odd-row vertex
   (Proposition 24).** The same is impossible for the even rows, because k is odd.
8. **New: that map and the slot rule exclude each other (Proposition 25).** The two 2-adic mechanisms
   compete for the residues of the slot index.
9. **New: star runs fail (Proposition 26).** A run of doubles that share one row can hold only a few rows
   on the far side of that row.

Checked:
- Valid boards: 7 x 65 and 11 x 169 (collar boards, so f(11, m) = m + 30 for every m >= 117). There are
  now four independent eleven-row boards, two of them obeying the slot rule.
- The order-only violations of random slot-rule orders number 0.41, 0.94 and 1.59 per double on 11, 19
  and 27 rows, and the growth is led by law (i).
- No valid board is known on 15 or more rows. The best boards found have 19 violations (15 rows) and 53
  (19 rows), and the exact searches started from them end unresolved after 90 minutes and 2 hours.

## 4. Structure of a tilted rectangle in the family

**Fact G (roles; proved).** Write a tilted rectangle as bottom B, right R = B + u, left L = B + v, top T,
with u = (a, b), v = (-c, d), a, b, c, d >= 1, ac = bd. Rows strictly increase from B to the middle
corners to T. So a black cell in row 1 can only be B and one in row h only T, and a black middle corner is
a double cell (interior rows are black only on double columns). A rectangle has at most two black sea
corners, and if it has two they are B (row 1) and T (row h).

**Lemma 12 (no one-double right angles; proved).** No tilted rectangle has three black corners of
which exactly one is a double cell. *Proof.* The double cell (0, c) is a middle corner and the other black
corners are B = (x1, 1) and T = (x2, h), so the right angle is at the double and
x1 x2 = (c - 1)(h - c). Relative to a double, row-1 cells sit at residues 1 or 2 mod 4 and row-h cells at 3
or 2, so x1 x2 is 3, 2, 2 or 0 mod 4, and 0 mod 4 only as 4 mod 8. If c is even, (c - 1)(h - c) = 1 mod 4.
If c is odd, it is 0 mod 8. ∎ (For h = 1 mod 4 this family kills the layout, Lemma 10 of `REPORT.md`.)

**Lemma 13 (sea-only rectangles; proved).** If B and T are black sea cells and L, R are white, the
presentation {L, R} has a rival only through double cells. So every interior violation involves at least
two double cells, counting the rectangle and its rival together.

**Lemma 14 (locality; proved).** A tilted rectangle spans at most W columns, so two doubles interact only
if they are at most about W/4 = h^2/16 slots apart.

**The adjacent-pair rules (slot distance 1; proved).** (A) the knight rule: rows at distance 3 split
between consecutive doubles, both in [2, h - 1], are fatal. (B) a right angle at the middle cell. (C) a
horizontal rival through a fixed boundary cell (the 3-4-5 triangle). (D) the right angles at a double
point with a sea point, which section 5 makes complete.

**Proposition 15 (no linear order; proved).** No Chinese-remainder order
j -> (a j + b mod (k + 1), c j + d mod k) gives a valid board for h >= 7, whatever the x_j, because the
pairs (o_j, ε_(j+1)) run over all of Z_(k+1) x Z_k and so hit a knight pair. All 48 such orders on seven
rows are UNSAT, and so are all 48 concatenations of the staircases L_1, L_3, L_5.

## 5. The complete three-corner law

**Proposition 16 (proved; checked).** In the interior, a tilted rectangle with exactly three black
corners and white fourth corner X is fatal (X has an axis-aligned rival) exactly in these cases.
- **(i) Three double corners.** 16 (i - j)(l - j) = -(r_i - r_j)(r_l - r_j), with the vertex at slot j. The
  completion lies on a double column, so it is fatal whenever it is in the grid.
- **(ii) Law (D).** The vertex is a double point (4i, r) with r odd, the other corners are a double point
  (4(i + d), e) with e even on the far side of r and a sea cell in row σ(r). Then v2(d) = τ - 2 or τ - 3.
  - If v2(d) = τ - 2, write d = 2^(τ-2) d'. The sea corner is a fixed cell, and the event is fatal exactly
    when d' divides u(e - r) and e = 1 + u d' (σ = 1) or e = 3 + u d' (σ = h), mod 4.
  - If v2(d) = τ - 3, the sea corner is the middle cell at column 4i + (r - 1)(e - r)/(4d) (σ = 1) or
    4i - (h - r)(e - r)/(4d) (σ = h), and the event is fatal exactly when that cell has the value σ.
- **(iii) Law (E2).** The vertex is a middle cell with value σ, the other corners are a hot odd row o with
  σ(o) = σ and an even row e, in doubles at slots i < j with D = j - i. With |o - σ| = 4u, the rectangle
  exists when u |e - σ| = pq with p + q = 2D (p, q odd), the vertex is at column 4i + 2p, and the fourth
  corner is in the grid.
- Nothing else.

*Proof sketch.* By Fact G a sea corner is B or T, so a right angle with a sea corner has its vertex at a
double point (case ii) or at the sea corner (case iii and the excluded cases). For (ii) with σ = 1 the
vertex condition is 4d(x0 - 4i) = (r - 1)(e - r), with x0 - 4i = 1 mod 4 (fixed cell) or 2 mod 4 (middle
cell). Since e - r is odd, v2(r - 1) = v2(d) + 2 or v2(d) + 3. In the first case x0 - 4i = u(e - r)/d' must
be an integer that is 1 mod 4, which is the displayed congruence. The fourth corner
(x0 + 4d, 1 + e - r) is in the grid iff e > r and lies on a sea column in an even row, so Lemma 5 of
`REPORT.md` gives the rival. The case σ = h is the half-turn image. For (iii) the legs from a middle cell
are 2 mod 4, which forces a hot odd row and an even row. The excluded cases fail mod 4 or mod 8 (a sea
vertex with two even rows needs e + e' = h + 1 and then a factor sum of 2 mod 4; a sea vertex with two odd
rows has a white odd-row completion). ∎

*Check (`scripts/v1laws.py`, `scripts/lawD_mod4.py`).* Every three-corner violation on random boards
with 7, 11 and 15 rows falls under (i), (ii) or (iii), with 0 exceptions among about 800. The fixed-cell
half of (ii) predicts the checker's list exactly on 11, 15 and 19 rows (32, 92 and 172 events).

So the fixed cells contribute law (i) and the congruence half of law (D), which are conditions on the
order alone. The middle cells enter through (iii) and the second half of (ii), which both say "this
middle cell must not be σ". This explains the band structure of the eleven-row boards: σ = 1 pairs push
x to h, and σ = h pairs push x to 1.

## 6. The middle cells are a 2-SAT problem

**Proposition 17 (proved; checked).** For h = 3 mod 4 and a fixed order, every interior violation
depends on at most two middle cells. So the admissible middle cells are the solutions of a 2-SAT formula,
decided in linear time.

*Proof outline.* Three facts. (F1) Only B can be in row 1 and only T in row h. (F2) A cell in rows 2 to
h - 1 of a sea column is a constant white cell, so a variable cell is a row-1 or row-h cell of a middle
column, and every rival cell in an interior row lies on a double column. (F3) All cells of one middle
column are one variable.

With at most one white corner, at most one black corner is a sea cell (two would leave one double,
Lemma 12), and X is not a variable cell (the excluded case e + e' = h + 1 of Proposition 16). A rival
adds at most one more column.

With two white corners W1 = (x, r), W2 = (z, s):
- x = z: the rival test is whether {r, s} is in F, a constant.
- r ≠ s and x ≠ z: the rival cells (x, s), (z, r) are in the columns of the whites, and in each
  arrangement (B and T, L and R, or a side) at most two middle columns occur.
- r = s: the whites are L and R, and the rival asks for a common black row in their columns. Three middle
  columns would need B and T both middle cells, which forces D = 2 mod 4 and puts L and R on fixed
  columns of different kinds with no common row. Otherwise all four corners are middle cells, which
  needs k even.
- A second tilted rectangle with the same whites adds no new middle column, by the same parity
  arguments (circle with diameter LR, or translation by the vector LR). ∎

*Check (`scripts/midcount.py`).* None of about 1,700 violations on random 11-, 15- and 19-row boards uses
more than two middle cells. On a valid eleven-row board the formula has 4 unit clauses and 21 binary
clauses, all joining gaps at distance 1 or 2 (`scripts/clauses2sat.py`). On random boards binary clauses
reach distance 9 (15 rows, `scripts/bindist.py`), so there is no locality theorem for the 2-SAT part.

## 7. Law (D) in one congruence, and what residues can do

**Law (D) in one congruence (proved).** For odd u and d', (u - 1)(d' - 1) = 0 mod 4, so
u d' = u + d' - 1 mod 4. Both halves of the fixed-cell case then read the same way: the event at distance
d = 2^s d' (s = τ - 2, d' odd) is fatal by class exactly when

    e = w + d' (mod 4),

and the class w + d' + 2 is safe. The partners of a vertex at slot a form the progression
P(a) = a + 2^s(2Z + 1), and the class each partner must avoid is a function of its slot alone.

**Proposition 18 (a slot rule for the hot rows; proved; checked).** Suppose that in the interior
(a) every double with a hot odd row is at an even slot, at a slot = 0 mod 4 if w = 1 and = 2 mod 4 if w = 3,
and (b) every double at an odd slot has a non-hot odd row and an even row = 0 mod 4 at slots = 1 mod 4 and
= 2 mod 4 at slots = 3 mod 4. Then no hot row is the vertex of a law-(D) event, at any distance.

*Proof.* For a hot vertex d' = d is odd, so the partner is at an odd slot, whose class is fixed by the
slot mod 4, and that class is the safe one in each of the four cases. ∎

*Counting (proved).* The rule is feasible exactly when h = 3 mod 8. Then the hot edges fill k(k - 1)/2 of
the k(k + 1)/2 even slots and the odd slots have room. When h = 7 mod 8 the hot edges fill every even slot,
and the odd slots are short of class-0 edges by about k/4.

*Check.* With the rule on the interior of eleven-row boards, the lazy SAT search finds valid 11 x 169
collar boards for offsets 1 and 2 (`data/cegar_h11_mod4_j1_t4.json`, `data/cegar_h11_mod4_j2_t4.json`),
and UNSAT for offsets 0 and 3. So the rule is compatible with validity on eleven rows.

**Proposition 19 (the 2-adic slot rule; proved).** Give the double at slot j an even row of class
c(j) = oddpart(j) - 1 (mod 4). A vertex of level s and type w at slot a is then protected by residue from
every fixed-cell law-(D) event, at every distance at once, if and only if v2(a) >= s + 2 (w = 1) or
v2(a) = s + 1 (w = 3). *Proof.* If v2(a) > s, every partner j = a + 2^s d' has v2(j) = s and
oddpart(j) = a/2^s + d', so c(j) is the safe class for every d' exactly when a/2^s = w - 1 mod 4. If
v2(a) <= s, c(j) doesn't alternate with d' as the safe class does. ∎

One class function serves every level, because a partner of a level-s vertex always has v2 = s. It is not
a construction: slots with v2 = 0, half of all slots, can carry no protected vertex, and only the 2k edges
through rows 1 and h are inert.

**Proposition 20 (residues can't protect everything; proved).** Ignore the size conditions of law (D).
(a) Two vertices of the same level s at slots a = b mod 2^(s+1) make the same demands on P(a) ∩ P(b) iff
(b - a)/2^s = w_b - w_a mod 4, and otherwise the progressions are disjoint. (b) If b is in P(a) and has
the higher level s' > s, then a demands the same class at b + 2^(s') d'' and b + 2^(s')(d'' + 2) and b
demands different ones. (c) No order protects every vertex: by (b) the protected hot vertices and the
vertices of level >= 1 must use one slot parity, and the other parity would hold only the 2k inert edges.

**Lemma 21 (the hot sandwich; proved).** If slot b holds a τ = 3 vertex and slots b ± 1 hold hot vertices,
then one of the six tight events among them is fatal by class and is escaped only if that partner's even
row is on the near side.

**Under the slot rule (proved).** At an odd slot i, a vertex of level s >= 1 sees the constant class i + 1
(s = 1) or i - 1 (s >= 2) at all its partners, so exactly one tight partner, at i + 2^s δ with δ = ±1, is
class-fatal and must have its even row on the near side. For τ = 3 the tight pointers form a fixed pattern
of slots mod 8: for w = 1, slots 1 and 3 point at each other, and so do 5 and 7; for w = 3, slots 1 and 7,
and 3 and 5. *Check (`scripts/tight.py`).* On the two slot-rule eleven-row boards every class-fatal tight
event in the interior is escaped by the near side (13 and 12 events), and the class-fatal events at
|d'| >= 3 are escaped by the near side (40 and 43) or by non-divisibility (28 and 38).

## 8. What sizes have to do

**Lemma 22 (range; proved).** A law-(D) event with vertex row r joins doubles at most φ(r)/4 slots apart.
*Proof.* For σ = 1 the far side is r < e <= h - 1, and d' divides u(e - r), so
|d| <= 2^(τ-2) u (h - 1 - r) = (r - 1)(h - 1 - r)/4. The middle-cell case gives half of that, and σ = h is
the half-turn image. ∎ So rows next to the boundary interact over about h/2 slots and the centre rows over
about h^2/16, the same grading as the boundary layer of Lemma 11.

**Lemma 23 (the window principle; proved).** A non-hot vertex r at an odd slot has its fixed-cell
law-(D) partners at distance 2^(τ-2) times an odd number: on the other track if τ = 3, on its own track if
τ >= 4. If every double on that track within φ(r)/4 slots has its even row on the near side of r, the
vertex has no fixed-cell law-(D) event at all. *Proof.* The far side is part of every event, and the
range is Lemma 22. ∎

A block of slots satisfies the window principle for all its vertices in three ways (E_A, E_B are the even
rows on the two tracks in the block):
- *Band:* E_A and E_B in a window [E1, E2], σ = 1 vertices above E2, σ = h vertices below E1.
- *Zig-zag, A low and B high:* σ = 1 vertices are τ = 3 on track B or τ >= 4 on track A, all above
  max E_A, and σ = h vertices are τ = 3 on track A or τ >= 4 on track B, all below min E_B.
- *Zig-zag, A high and B low:* the same with the tracks exchanged.

Every edge through a τ = 3 row fits one of the zig-zag types, inverted or not. A τ >= 4 edge fits only if
it is non-inverted (e on the near side of its own odd row), because its own even row sits on the track it
points at. So the size design comes down to two problems: placing the inverted τ >= 4 edges, about q/8
of all edges, and supplying enough small even rows to the low tracks next to the rows close to their
active side.

*Mixing residues and sizes (checked by counting, `scripts/alloc.py`).* A hot vertex at an odd slot has
its partners at even slots, so it can be protected by a window whatever its edge. That suggests putting
the inverted τ >= 4 edges at even slots under Proposition 19 and moving displaced hot edges with w = 1 to
odd slots under windows. By counting, this fits for every h = 3 mod 8 up to 67 and fails from h = 99 on,
where about 3q/32 edges need slots with v2 >= 4 and only q/16 exist.

## 9. The order-only conditions

By Proposition 17, validity is a question about the order once the 2-SAT part is satisfiable. I drew
random orders that obey the slot rule (`scripts/residual.py`, interior only) and sorted every violation
that uses no middle cell. Each falls under one of the following laws, each checked against the checker
on 19- and 27-row boards.

- **(i) Three doubles** (Proposition 16 (i)). It absorbs the fully black rectangles of four double points
  and the tilt-tilt pairs of rectangles with two double corners each that share their whites as a side or
  as a diagonal.
- **(D)** The fixed-cell half of law (D), from the odd-slot vertices.
- **(P) Pythagorean exposure.** Doubles at slots i < j with D = j - i odd, rows a, b of opposite parity,
  one in each, and 16 D^2 + (b - a)^2 = Λ^2. The two whites lie in the middle column 2(i + j) in rows
  (a + b ∓ Λ)/2. If both are interior the event is fatal; if one is in row 1 or h it is a unit clause of
  the 2-SAT. The solutions are Λ ± (b - a) = 2m and 8D^2/m with m odd dividing D^2. D = 1 gives only
  (4, 3, 5), the knight rule, and D = 3 gives |b - a| = 5, 9, 35. For every odd D the scaled triangle
  |b - a| = 3D is a solution. (`scripts/cm_check.py`: 123 of 123.)
- **(C) Thales pairs through an inert edge.** Whites L, R in one row, B a fixed row-1 cell, T a double
  point, LR and BT diameters of one circle, so p^2 + (t - 1)^2 = n^2. The rival is fatal exactly when the
  double on the white's column contains row 1, so the edge is (1, e). The half-turn gives the row-h
  version. Triples seen: (3, 4, 5), (5, 12, 13), (8, 15, 17), (9, 12, 15), (12, 35, 37), (16, 63, 65),
  (7, 24, 25), (20, 21, 29), (24, 45, 51) and others. (`scripts/c_check.py`: 48 of 48.)
- **(Q) Four double columns.** A tilted rectangle with all corners on double columns, two black and two
  white, whose crossed cells are black.
- **(T) Collisions.** Two harmless rectangles with the same white completion.

So the conditions on the order are Diophantine relations among two, three or four doubles at slot
distance at most about h^2/16. Laws (P) and (C) have closed forms, and (Q) and (T) are described but not
reduced to closed form.

**Growth (checked, `scripts/residual.py`).** On random slot-rule orders the order-only violations
number 0.41, 0.94 and 1.59 per double on 11, 19 and 27 rows (interior only). Law (i) leads the growth:
0.5, 17 and 82 three-double right angles per board. The next classes on 27 rows are two-white rivals
with both whites on middle columns (mostly law (P), 45 per board), repeated presentations, and law (D).
So an explicit order has to remove law (i) in bulk, which is what section 10 tries.

## 10. Two 2-adic mechanisms that compete

**Proposition 24 (a 2-adic map for the odd rows; proved; checked).** Write o_j = 2 a_j + 1. Let M = 2^S
divide k + 1 with M >= k/16, and put

    a_j = (j mod M) + M floor(j / (kM)),

so that each block of kM consecutive slots uses M odd rows, each k times at spacing M. Then no
three-double right angle has its vertex on an odd row, whatever the even rows are.

*Proof.* A right angle at (4j, r_j) with legs to (4i, r_i) and (4l, r_l) needs
(r_i - r_j)(r_l - r_j) = -16 (i - j)(l - j). The absolute values of the two row differences add up to at most
h - 1: if they have opposite signs, because both leg endpoints are in the grid, and if they have the
same sign, because the vertex and the completion (row r_i + r_l - r_j) are. So their product is at most (h - 1)^2/4. Hence |i - j| <= k^2/16 <= kM,
and the slots i, j lie in one block or in adjacent blocks. In that range, a_i = a_j or
v2(a_i - a_j) <= v2(i - j): if i = j mod M then a_i - a_j is 0 or ±M, and otherwise
a_i - a_j = i - j mod M and is nonzero mod M. A leg to an odd row has v2(r_i - r_j) = 1 + v2(a_i - a_j)
<= 1 + v2(i - j), and a leg to an even row has an odd difference. A zero difference is impossible because
the right side is nonzero. So the left side has valuation at most 2 + v2(i - j) + v2(l - j), less than the
4 + v2(i - j) + v2(l - j) of the right side. ∎

The condition M >= k/16 holds when the odd part of k + 1 is at most 15, so the proposition applies to
h = 2^(S+1) c - 1 with c odd and c <= 15 (for example h = 15, 23, 31, 47, 63).

*The even rows can't be treated the same way (proved).* The analogue needs v2(b_i - b_j) <= v2(i - j)
for the even-row index b in [0, k - 1], each value used k + 1 times. At the first level, distinct values on
slots of opposite parity must have opposite parity, so the even and odd values of b must split evenly
between even and odd slots. But k is odd, so there are (k + 1)/2 even values and (k - 1)/2 odd ones, and
the counts don't match. The same splitting has to repeat at every level, which needs a power of 2
dividing k.

*Check (`scripts/ddd.py`).* With the map, the odd-vertex count of three-double right angles is 0 on 15
(M = 8), 23 (M = 4) and 31 rows (M = 16), in three random fillings of the even rows each. Random orders
give 46 to 161. The even-vertex count is unchanged (2 to 125).

**Proposition 25 (the map and the slot rule exclude each other; proved; checked).** Proposition 24
holds for a_j = ψ(j mod M) + M floor(j / (kM)) with ψ any permutation of Z/M that preserves v2 of
differences (an automorphism of the binary tree of residues). Every such ψ sends the even slots onto one
parity class of a. But the hot odd rows have a = 2 or 3 mod 4 when h = 3 mod 8 (rows 5 mod 8 for σ = 1 and
h - 4 mod 8 for σ = h), and a = 1 or 2 mod 4 when h = 7 mod 8, so they lie in both parity classes, and
rule (a) of Proposition 18 fails.

Without the slot rule, law (D) gets no help from residues. With ψ the identity and a σ = 1 vertex at slot
j, the partners at distance 2^(τ-2) d' sit at slots j' with v2(j') = v2(j) - 1, and the fatal class there is
oddpart(j') - oddpart(j) mod 4. Both values occur among the vertices in range of a given partner, so only
sizes can protect it.

*Check.* Annealing on 15 rows inside the structure of Proposition 24, with swaps only between doubles that
share an odd row, stalls at 72 and 75 violations, against 19 for unrestricted annealing. The excess is in
law (P) (23 against 4) and law (D) (16 against 3).

So the 2-adic structure of the slot index has to serve two masters: law (i) wants the odd rows to follow
j mod M, and law (D) wants the hot rows on even slots with the even rows following the slot mod 4. An
explicit order has to split the residues between them, for example by giving the 2-adic map only to the
odd slots, where the non-hot rows live.

## 11. Negative results for structured orders

**Proposition 26 (star runs; proved).** Let slots p, ..., p + L - 1 (interior) hold doubles that all
contain the odd row o, not inert, with τ = τ(o) and type w. Every even row e of the run on the far side of
o, at position t, satisfies t - p < 2^(τ-2) if e = w + 1 mod 4, and p + L - 1 - t < 2^(τ-2) if e = w - 1
mod 4. So the run holds at most 2^(τ-1) far-side rows. *Proof.* Every double of the run is a vertex with
row o. At d' = ±1 the divisibility of law (D) is automatic, so the vertex at t - 2^(τ-2) (d' = 1) is fatal
when e = w + 1, and the vertex at t + 2^(τ-2) (d' = -1) is fatal when e = w - 1. Since w is odd, w ± 1 are
the two even classes, and every far-side row is in one of them. ∎

The same argument for a run that shares an even row E puts every odd row whose far side contains E within
2^(τ-2) of an end of the run. About half of the odd rows have E on their far side, so long runs of either
kind fail. Only the inert rows 1 and h can form long runs. *Check.* Fixed-order tests on 11 rows (middle
and transition cells annealed, `scripts/mkorder.py`) leave 44 (odd-row runs) and 39 (even-row runs)
violations, against 49 for a random order. The eleven-row valid boards contain runs of length 2 or 3 only.

Earlier negative results, from `REPORT.md`: no Chinese-remainder order (Proposition 15), no
concatenation of staircases on seven rows, no affine orders, and the rigid "1, x, h" depth-first search
stalls at 45 of 56 doubles on 15 rows.

## 12. Computations

**Layout of the searches.** W pad columns of row 1 on the left and row h on the right, then the q doubles
at spacing 4. The first and last TR gaps have free sea cells (any row), and the other gaps are "1, x, h".
The free transition gaps are needed: a pad followed directly by "1, x, h" dies at the second double, by
Lemma 11 of `REPORT.md`. A valid board of this layout is a collar board and gives f(h, m) = m + q_h for
every m at least its core width.

**Tools.**
- `scripts/fastcheck.py` and `check` in `scripts/cegar_board.py`: exact checker for boards whose doubles
  are distinct pairs of a triangle-free graph. It counts hidden rectangles, presentations with an
  axis-aligned rival, and repeated presentations. Boards are re-verified independently with
  `verify_narrow` (`scripts/verify_cols.py`).
- `scripts/cegar_board.py`: lazy SAT search. Each violation of a candidate is turned into an exact
  no-good on at most 8 cells, so UNSAT is a proof that the layout has no valid board. Options: the slot
  rule (`RULE=mod4:j0`, `RULE_TR`), and new here a warm start (`PHASE=board.json`), which sets the
  solver's preferred values to a stored board's order and cells.
- `scripts/inc_anneal.py` (new): simulated annealing whose cost is exactly the checker's violation
  count, maintained incrementally. A move (swap two doubles, flip a middle cell, redraw a transition
  cell) changes one or two columns, and only rectangle placements with a corner in those columns are
  re-evaluated. This is exact because F is constant (every pair is used) and every rival depends only on
  the columns of the white corners. The cost after a run agrees with the full checker in every run. It
  does about 4,000 moves per second on 11 rows and 600 on 19 rows (compiled with numba). Options: a
  fixed or starting order (`ORDERFILE`, `INITFILE`), swaps restricted to doubles sharing an odd row
  (`SAMEODD=1`), and the slot rule.

**Results.**

| Rows | Search | Result |
|---|---|---|
| 7 | lazy SAT, hybrid | valid 7 x 65 collar board |
| 11 | lazy SAT, hybrid, three transition gaps | valid 11 x 169 (`data/cegar_h11_s4_hyb_t3_111.json`) |
| 11 | lazy SAT with the slot rule, four transition gaps | valid for offsets 1, 2; UNSAT for 0, 3 |
| 11 | annealing, 15 min | 3 to 5 violations |
| 11 | annealing, then warm-started lazy SAT | valid 11 x 169 in 24 s (`data/cegar_h11_warm_t3.json`, verified) |
| 15 | annealing, 25 min, three seeds | 19, 20, 26 violations (`data/anneal_h15_best19.json`) |
| 15 | warm-started lazy SAT, 90 min | unresolved (1,717 iterations, 262k no-goods) |
| 15 | annealing inside Proposition 24 | 72, 75 violations |
| 19 | lazy SAT, four transition gaps, with or without rule | UNSAT at once (pads and Lemma 11) |
| 19 | lazy SAT, eight gaps, rule in the whole interior | UNSAT in 3 s (Lemma 11 kills the class-0 rows at slot 10) |
| 19 | lazy SAT, eight gaps, rule from slot 20 on, two offsets | unresolved at 90 min (492 iterations each) |
| 19 | annealing, 30 + 60 min | 53 to 67 violations (`data/anneal_h19_best53.json`) |
| 19 | warm-started lazy SAT, 2 h | unresolved (1,072 iterations, 376k no-goods) |

So f(11, m) = m + 30 for every m >= 117, from four independent boards, and nothing is known in this
family from 15 rows on. On the best 19-row board, about half of the 57 violations are in the end layers
and half in the interior.

*Why the search gets harder (heuristic).* The order-only violations per double grow roughly like h
(section 9), while the freedom of a random order is only about log q per double. A first-moment count
with independent violations would let random-like orders survive only up to moderate h, and the
counting of section 8 fails from about 99 rows. Both say the same thing: a valid board for large h needs
arithmetic structure that removes whole laws, not a better search.

## 13. Where the construction stands

**Reduction theorem (proved, for h = 3 mod 4).** The interior of a "1, x, h" board is valid if and only if
(1) the order avoids the order-only conditions of section 9 (laws (i), (D), (P), (C), (Q), (T) and their
boundary-layer versions), and (2) the 2-SAT formula of Proposition 17 is satisfiable. Part (2) is decided
in linear time once the order is fixed.

What is known about part (1):
- Residues mod 4 dispose of the law-(D) events of the hot rows at every distance (Proposition 18), and no
  residue rule can do the same for all rows (Proposition 20).
- A 2-adic map for the odd rows disposes of law (i) at odd vertices (Proposition 24), but it is
  incompatible with the slot rule (Proposition 25).
- Windows protect the rest of law (D) by size (Lemma 23), except for the inverted τ >= 4 edges.
- Laws (P) and (C) are explicit Pythagorean conditions, (Q) and (T) are described but not in closed form,
  and law (i) at even vertices has no residue mechanism, since k is odd.

What is missing is an order that does all of this at once: a split of the slot residues between the
mechanisms for law (i) and law (D), a size design for the odd slots, and a check that the remaining
Pythagorean laws can be avoided.

## 14. Open problems and next steps

1. **Split the residues.** Give the 2-adic odd-row map only to the odd slots (which hold the non-hot rows
   under the slot rule) and keep the hot rows on even slots by w. Prove or refute that this removes law (i)
   at odd vertices whose two legs go to odd slots. Then measure what is left with `scripts/ddd.py` and
   `scripts/residual.py`.
2. **Law (i) at even vertices.** Find a size mechanism (the product bound (h - 1)^2/4 limits the slot
   distance to k^2/16) or a mod-3 mechanism, since the 2-adic one is impossible.
3. **Inverted τ >= 4 edges.** Show that about q/32 of them can be outliers under windows, or that they
   can't, which would bound the family.
4. **Is the family valid from 15 rows on at all?** A proof of infeasibility for some h would be as useful
   as a construction. The lazy SAT search can prove UNSAT for a fixed layout; a run with the order
   restricted by Proposition 18 and a longer cap is the natural test on 19 rows.
5. **Relax the family.** If the rigid family fails, allow free interior seas in a sparse set of gaps
   (one in every few), which the nine-row SAT boards suggest are needed from nine rows on.

## 15. Files

All paths are relative to this folder.

| File | Contents |
|---|---|
| `REPORT.md` | Running notes; sections 4.5 and 4.6 are the source of sections 4 to 9 here |
| `scripts/fastcheck.py` | exact checker for doubles from a triangle-free graph |
| `scripts/cegar_board.py` | lazy SAT search; slot rule; warm start (`PHASE`) |
| `scripts/cegar_core.py` | UNSAT cores with selector assumptions |
| `scripts/inc_anneal.py` | incremental exact annealer (new) |
| `scripts/ddd.py` | three-double right angles by vertex parity; Proposition 24 check (new) |
| `scripts/mkorder.py` | random, odd-row-run and even-row-run orders (new) |
| `scripts/v1laws.py`, `scripts/lawD_mod4.py` | Proposition 16 checks |
| `scripts/midcount.py`, `scripts/clauses2sat.py`, `scripts/bindist.py` | Proposition 17 checks and the 2-SAT clauses |
| `scripts/tight.py`, `scripts/slotread.py` | tight law-(D) events on the eleven-row boards |
| `scripts/alloc.py` | counting for the mixed residue and window design |
| `scripts/residual.py`, `scripts/resid_examples.py`, `scripts/v2classes.py` | order-only violations by class |
| `scripts/cm_check.py`, `scripts/c_check.py` | laws (P) and (C) |
| `scripts/verify_cols.py` | independent verification with `verify_narrow` |
| `data/cegar_h11_s4_hyb_t3_111.json` | valid 11 x 169 board |
| `data/cegar_h11_mod4_j1_t4.json`, `data/cegar_h11_mod4_j2_t4.json` | valid 11 x 169 boards with the slot rule |
| `data/cegar_h11_warm_t3.json` | valid 11 x 169 board from the warm-started search (new) |
| `data/anneal_h15_best19.json` | best 15-row board, 19 violations (new) |
| `data/anneal_h19_best53.json` | best 19-row board, 53 violations (new) |
