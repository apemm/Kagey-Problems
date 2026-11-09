# Singleton completion of the O(h^(5/2)) identifying set

9 November 2026. This note attacks the question of whether the identifying set of
`../2026-11-08/general_dominance_quadratic/quadratic_arithmetic.md`, section 3, can be
completed to an equality board. It cannot yet. The method splits the needed
statements into structural lemmas, which are proved below, and one counting
statement, which is open. Earlier reports and the manuscript are unchanged.

**Summary**

1. **Residue lemma.** Some configurations can't occur because of column residues
   modulo `S`. Every violation whose black symmetric difference contains exactly
   one sea cell is impossible when that cell lies in a column of odd residue. The
   same holds for one side-role case at residue `2 (mod 4)`.
2. **Lifts.** Theorem 2 of the scaffold survives arbitrary lifts of the CRT
   indices by multiples of `pq`, and survives deleting doubles. Random layering
   is therefore available at a width cost of `L`.
3. **Forced parity.** With an odd sea alphabet, Lemma 3.1 of
   `dominance_attempt.md` turns some right angles into constraints on a single
   letter. At odd residue only configurations with the vertex at a double cell
   contribute. Their elementary count is `O(h (log h)^2)` per column, and random
   layering with `L = O(log h)` brings this below the alphabet threshold in
   expectation.
4. **Pseudo-double columns.** Sea columns of residue 0 are unavoidable. At
   residue 0 the 2-adic parts of Theorem 2 survive and the parts that use `p` and
   `q` don't.
5. **Stuck point.** We need a uniform bound `|F_x| <= h/16` on the letters that a
   column loses to mixed side/diagonal collisions with one sea cell and two or
   three doubles. These collisions occur only at even residue, including residue
   0. Elementary counts give polynomially large bounds, and layering can't absorb
   them at width `h^{5/2+o(1)}`.

No threshold bound is claimed.

## 0. Setting

The setting follows `quadratic_arithmetic.md` section 3.

* `S=2^s` is the least power of two with `S^2>4h`. So `S^2<=16h` and `S>=8` once
  `h>=16`.
* `p` and `q` are the primes specified there. Edge `(a,b)` sits in column
  `S x_ab` with `x_ab=CRT(a mod p, b mod q)`.
* `B` is the set of the `2q_h` double cells.
* Every other column is a **sea column** and receives one black cell, its
  **letter**.
* For a column `x`, write `rho(x)=x mod S` and `nu=v_2(rho)` when `rho!=0`.

The board is valid when no two distinct rectangles `R!=R'` have
`C(R) symdiff C(R')` contained in the black set. Write `E` for this symmetric
difference. By the shared-corner count (`quadratic_arithmetic.md` section 3.5),
`|E|` is 4, 6, or 8. Every violation is one of the following:

* two hidden rectangles (`|E|=8`);
* two rectangles sharing exactly one corner (`|E|=6`);
* two rectangles sharing a pair `{P,Q}` as two sides, two diagonals, or one side
  and one diagonal (`|E|=4`).

The colors of the shared corners are irrelevant. Write `s(E)` for the number of
sea cells in `E` and `j(E)` for the number of distinct double columns meeting
`E`. Theorem 2 of the scaffold is exactly the statement that no violation has
`s(E)=0`.

## 1. The residue lemma and violations with one sea cell

**Lemma 1.1 (residues).** The corners of any lattice rectangle, axis-aligned or
tilted, satisfy `P_1+P_3=P_2+P_4` for each pair of opposite corners. So the four
corner columns `c_i` satisfy `c_1+c_3=c_2+c_4`. In particular no rectangle has
exactly one corner in a column of nonzero residue modulo `S` and its other three
corners in double columns.

*Proof.* Opposite corners have the same midpoint. Every double column is
`0 (mod S)`. QED.

**Proposition 1.2.** Let `E` have exactly one sea cell `A=(x,r)`, with all its
other cells double cells.

* (i) If `rho(x)` is odd, no such violation exists.
* (ii) Suppose `rho(x)=2 (mod 4)` and `S>=8`. Then no such violation has `A` in
  the side pair of a mixed side/diagonal collision.

*Proof.* **The cases that aren't mixed side/diagonal.**

* *Hidden pairs, side/side, and diagonal/diagonal.* Each yields a rectangle with
  corners `A` and three double cells. Lemma 1.1 rules that rectangle out.
* *One shared corner `Z`.* The rectangle not containing `A` has three black
  double corners and `Z`. Lemma 1.1 forces `rho(Z)=0`. The rectangle containing
  `A` then has residues `rho, 0, 0, 0`, which Lemma 1.1 rules out.

These arguments use only `rho!=0`.

**Mixed side/diagonal.** The rectangles are `{A,B,P,Q}` (side `AB`) and
`{C,D,P,Q}` (diagonal `CD`). Put `H=A+B-C-D`. The white points are
`P=A-H/2` and `Q=B-H/2`, so `H` has even coordinates. Whether `A` is in the side
pair or the diagonal pair, `H_x = +-rho (mod S)`.

* *(i).* If `rho` is odd, `H_x` is odd. That's impossible.
* *(ii).* Put `U=B-A` and `V=D-C`.
  - Here `U_x = 2 (mod 4)` and `V_x = 0 (mod 8)`. So `U_x^2 = 4 (mod 32)` and
    `V_x^2 = 0 (mod 64)`.
  - The norm equation gives `V_y^2-U_y^2 = 4 (mod 32)`. Odd `U_y` and `V_y` would
    give `0 (mod 8)`. So both are even, `U_y=2u` and `V_y=2v`, with
    `v^2-u^2 = 1 (mod 8)`. This forces `v` odd and `4 | u`, so `8 | U_y`.
  - In the perpendicularity equation `H_xU_x + H_yU_y = 0`, the first term has
    2-adic valuation exactly 2, because `H_x` and `U_x` are both `2 (mod 4)`. The
    second term has valuation at least 3, or is 0. So the sum can't vanish.

QED.

The same computation with `A` in the diagonal pair at `rho = 2 (mod 4)` gives
`U_y = 2 (mod 4)`, `8 | V_y`, and `S | H_y`. That isn't a contradiction, and this
case survives. At `nu>=2` the valuation pattern with `U_y` and `V_y` both odd
also survives the 2-adic test. For example, at `nu=2` the test only forces
`v_2(H_y)=4`.

## 2. Lifts and deletions preserve Theorem 2

**Lemma 2.1.** Let `x'_ab` be any distinct integers with
`x'_ab = x_ab (mod pq)`. Let `B' subset B` be the cells of any subset of the
edges, placed in columns `S x'_ab`. Then `B'` is an identifying set.

*Proof.* Every step of sections 3.1 to 3.5 of `quadratic_arithmetic.md` uses only
three facts:

* horizontal coordinates divisible by `S`;
* the congruences `x'=a (mod p)` for odd cells and `x'=b (mod q)` for even cells;
* the sizes of rows.

Section 3.4 also uses that two cells in one odd row lie in distinct columns with
indices differing by a nonzero multiple of `p`, and the same with `q` for even
rows. Lifting by multiples of `pq` preserves all of this. Deleting cells from an
identifying set can't create a violation, because `E` must lie in the black set.
QED.

**Random layering.** Give each edge an independent uniform color in `{1..L}`.
Layer `l` is a translate of the board `[0,Spq)` containing only the color-`l`
doubles. Consecutive layers are separated by `2W_h` extra sea columns.

* Every rectangle has span at most `W_h`, so every violation lies in one layer
  or in one separating gap.
* A configuration that uses `j` distinct doubles of the unlifted geometry
  survives with probability `L^{-j}`.
* The width is multiplied by `L+o(1)`, and each layer satisfies Lemma 2.1.

## 3. Forced parity and constraints on one letter

Use an odd sea alphabet. Lemma 3.1 of `dominance_attempt.md` concerns three black
cells that form a tilted right angle with completion `W=(c,y)` inside the strip,
in a sea column. It says the letter of `c` must have the parity of `y` and differ
from `y`.

If `y` is even, every odd letter at `c` is fatal. So a right angle made of the sea
cell `A=(x,r)` and two double cells, with an even completion row in a sea column,
forbids the letter `r` at `x` outright. This is a constraint on one letter, even
though `s(E)=2`.

**Proposition 3.1.** Let `rho(x)` be odd. Every such forbidden configuration
satisfies all of the following:

* its right angle has its vertex at a double cell `D_1=(Sx_1, r_1)`;
* its other double cell `D_2=(Sx_2, r_2)` has `r_2-r_1` odd;
* `d_1 := x - Sx_1` is odd;
* with `Delta := x_2-x_1`,

      d_1 S Delta = -(r-r_1)(r_2-r_1),    v_2(r-r_1) = s + v_2(Delta),
      0 < |d_1 S Delta| < h^2.

*Proof.* **Vertex at `A`.** The horizontal product `(Sx_1-x)(Sx_2-x)` is odd. So
`(r_1-r)(r_2-r)` is odd, and both partners are even cells. The completion row
`r_1+r_2-r` is then odd.

**Vertex at `D_1`.** The completion row `r+r_2-r_1` is even exactly when
`r_2-r_1` is odd. The dot product condition is the displayed equation. Since
`d_1` and `r_2-r_1` are odd, the valuations agree.

**Degenerate cases.** If `Delta=0`, the leg `D_1D_2` is vertical and the angle is
axis-aligned. If the completion lies in a double column, the rectangle has
residues `rho, 0, 0, 0`, which Lemma 1.1 rules out. QED.

**Counting.** Put `r-r_1 = S m'`. Then `d_1 Delta = -m'(r_2-r_1)` with
`0<|r_2-r_1|<h`, so `|Delta| < h|m'|/|d_1|`. Fix `m'` (at most `h/S` choices) and
`D_1` (with `|d_1|<h|m'|`). The number of admissible `Delta` is at most
`2h gcd(m',d_1)/|d_1|`, and each gives at most two cells of `D_2`. Summing over
`d_1 = x (mod S)` gives

    |F_x^RA| <= C sum_{m'<=h/S} tau(m') (h/S) log h <= C' h (log h)^2.

This bound holds deterministically. It ignores whether the index `x_1+Delta` is
a double, which would contribute a heuristic factor of about 1/512.

Under random layering the two distinct doubles must share `A`'s layer.

* So `E|F_x^RA| <= C' h (log h)^2 / L^2`.
* Taking `L = C'' log h` puts this below `h/64` in expectation, at width
  `h^{5/2+o(1)}`.
* Turning this into a bound for every column needs a concentration step that is
  not carried out here: a bounded-difference argument over the colors, then
  Chernoff for a random alphabet of size `k=h^{Omega(1)}`.

## 4. Sea columns of residue zero are unavoidable

There are `pq-n_on_e >= (1-1/32)pq` multiples of `S` that aren't double columns,
and the same holds under any lift. At such a column every argument of
Proposition 1.2 is empty.

The 2-adic parts of Theorem 2 extend to a cell `(Sy,r)` with any `r`: section 3.1
in the opposite-parity case, and sections 3.2 and 3.3 in the odd-increment and
mixed-parity cases. The same-parity parts need `y = (r-1)/2 (mod p)` or
`y = (r-2)/2 (mod q)` for some letter in range. A virtual letter of that kind
exists for fewer than `n_o/p + n_e/q < 1/4` of these columns.

So residue-0 columns lose letters to the same-parity mechanisms of sections 3.1,
3.3, and 3.4. These are again constraints on one letter, coming from
configurations with one sea cell and two or three doubles.

## 5. Events with several sea cells

These events look manageable by the local lemma over random letters from a
random sparse Sidon set of odd rows, as in `sea_entropy_lower_bound.md`.

* Vertical rivals through actual doubles coincide with the virtual pair set,
  because every parity edge is a double.
* Pure sea events are therefore exactly those of that note, apart from new
  completions that land in double columns.
* Three odd sea cells complete at an odd row. If the completion lands in a double
  column, the even cell of that column supplies an axis rival. That is an event
  with three letters and one double, and its trivial weight per column is
  `h^{o(1)}` rather than `o(1)`.
* With random layering its weight drops to `h^{o(1)}/L`. Taking `L=h^{2eps}` (for
  every `eps>0`, this costs width `h^{5/2+o(1)}`) makes it small in expectation.
* Two things are still missing: a uniform bound on the largest single
  contribution, and the counts for events with two sea cells and two doubles.

## 6. Stuck point

Every route needs this uniform bound, for every sea column `x`:

    |F_x| <= h/16,

where `F_x` is the set of letters at `x` forbidden by violations with one free
sea cell. Then a random Sidon odd alphabet keeps at least `k/2` letters in every
column, and the local lemma can run. There are three sources:

1. **Forced-parity right angles** with two doubles (section 3). The elementary
   bound is `O(h (log h)^2)`. This is acceptable after layering with
   `L = O(log h)`, modulo concentration.
2. **Mixed side/diagonal collisions with one sea cell at even residue.** These
   use the Thales reformulation `(A-B).(A-B')=0`, `|A-B|=|D-C|`, with
   `B' = C+D-B`. Given three cells the fourth is determined up to two choices.
   But the number of candidate triples of doubles near `x` is about `h^3`, or
   about `h^{3/2}` when two of the cells share a double column. Layering divides
   these counts by `L^3` or `L^2`. Bringing the count below `h` would need
   `L >= h^{2/3}` or `L >= h^{1/4}`, which destroys the width.
3. **Residue-0 columns** (section 4). These are the same-parity mechanisms with
   one sea cell.

So the missing ingredient is arithmetic: an `h^{1+o(1)}` (or `o(h)`) count of
mixed configurations with one sea cell and three CRT-placed double cells
through a fixed column. For roughly this count, the heuristic density gives
`h^{1+o(1)}/512`. This is the same kind of uniform integer-point counting that
blocks the cross-block coloring in `mixed_collision_coloring.md`, now with CRT
moduli in place of one prime.

## 7. Audit

* The residue lemma depends only on equal midpoints of the diagonals. It covers
  axis-aligned rectangles too.
* Proposition 1.2(ii) was rederived using only arithmetic modulo 8 in the
  perpendicularity step. The norm step needs `S>=8`.
* The diagonal-role computation at `rho = 2 (mod 4)` was checked and found not to
  give a contradiction, as stated.
* In Proposition 3.1 the vertex-at-`A` parity argument needs `rho` odd, and the
  `Delta=0` case is axis-aligned.
* Lemma 2.1 was checked line by line against sections 3.1 to 3.5. Section 3.4
  needs only that same-row cells have index differences that are nonzero
  multiples of `p` or `q`.
* The layer gap `2W_h` exceeds every rectangle span.
* No computations were run for this note.
