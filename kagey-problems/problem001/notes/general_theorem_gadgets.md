# The general theorem: alternating boundary seas

Status (2026-11-06): hand proof below, checked by computer for h <= 8 on full boards and for
h <= 10 on every junction window. An independent audit of the proof found it correct up to three
wording gaps, fixed below (alpha, gamma-diag, and the side-side case). A second, separately written
board check confirms random balanced partitions, random edge orders and random end padding for
h = 5, 6, 7, 8. The proof is now Section 8 of jis/pemmasani.tex (Theorem "large widths").

## Statement

**Theorem.** Let h >= 3, put q_h = floor(h^2/4) and W_h = 1 + floor((h-1)^2/4). Then
f(h,m) = m + q_h for every m >= M_h := q_h + (q_h - 1)(2W_h + 1).

The upper bound is the row bound. For the lower bound we prove the following, which only needs
a triangle-free graph H on the rows.

**Proposition.** Let H be a triangle-free graph on the rows {1,...,h} with edges e_1,...,e_q.
Let Z be the blackout of an h x m grid with double columns p_1 < ... < p_q, where column p_j is
black exactly in the two rows of e_j, and p_{j+1} - p_j >= 2W_h + 2. Every other column is black
in one row only: row 1 to the left of p_1, and the row alternates between 1 and h at each double
(row 1 before p_1, row h between p_1 and p_2, row 1 between p_2 and p_3, and so on). Then Z is
valid, and |Z| = m + q.

With H = K_{floor(h/2), ceil(h/2)} this gives the theorem. Any column interval containing all q
doubles works, and so does any extension by more sea columns at either end.

## Proof

We call the singleton columns *seas*. A sea is black only in row 1 or only in row h.

**Axis-aligned pairs.** The doubles carry distinct edges of a triangle-free graph and the
singletons are leaves of G_Z, so G_Z has no four- or six-cycle. Lemma "girth" makes Z
axis-valid, and no axis-aligned rectangle is hidden.

**Locality.** A tilted rectangle R has span at most W_h (Lemma "span"), so its column range
contains at most one double column. If it contains none, every black point in the range lies in
one boundary row, and R has at most one black corner (Lemma "leftmost": a tilted rectangle has a
unique corner in its smallest and in its largest row). So it shows at least three points. Hence
we fix one double, shift it to column 0, and write D = {(0,a),(0,b)}, a < b. By the row
reflection we may assume the sea is in row 1 to the left of column 0 and in row h to the right.
Inside the range of R the black set is L ∪ D ∪ Rt, where L = {(x,1) : x < 0} and
Rt = {(x,h) : x > 0}.

Two facts are used throughout.

- (F1) A tilted rectangle has at most one corner in row 1 and at most one in row h.
- (F2) If a tilted rectangle has a corner in row 1 and a corner in row h, they are opposite.
  If they were adjacent, the side would be (dx, h-1), the other two corners would be these plus
  n with n perpendicular to the side, and both rows stay in [1,h] only if n_2 = 0. Then
  n_1 dx = 0, so dx = 0, and the side is vertical.

Two corners in one column are opposite, since a vertical side makes the rectangle axis-aligned.

Let K be the black corners of a tilted R and P = C(R) \ K. We only need |K| >= 2. Write
ℓ = (x_1, 1) with x_1 < 0, r = (x_2, h) with x_2 > 0, and d = (0,c) with c in {a,b}. A point
(0,1) or (0,h) in D counts as a d.

**The cases.**

- (alpha) K = {ℓ, r}. These are opposite by (F2). The other diagonal is M ± w with
  M = ((x_1+x_2)/2, (1+h)/2) and |w|^2 = ((x_2-x_1)^2 + (h-1)^2)/4. Its endpoints are not in row 1
  or h, by (F1) and (F2), so their rows lie in [2, h-1] and |w_2| <= (h-3)/2. This gives
  w_1^2 > (x_2-x_1)^2/4. Hence the two shown points straddle: one column is < x_1 < 0, and the
  other is > x_2 > 0. In particular neither is in column 0, and a point outside column 0 with row
  in [2, h-1] is white. So both shown points are white.
- (beta) K = D. The other diagonal has midpoint (0,(a+b)/2) and w_1 != 0, so |w_2| < (b-a)/2.
  The shown points lie strictly between rows a and b, in columns -w_1 < 0 < w_1, and are white.
- (gamma-diag) K = {ℓ, d}, opposite, with c >= 2 (c = 1 contradicts F1). The other diagonal is
  M ± w with M = (x_1/2, (1+c)/2) and |w|^2 = (x_1^2 + (c-1)^2)/4. Its endpoints are not in row
  1 (F1) or row h (F2), and not in column 0, because two corners in a column are opposite. So
  both are white. A vertical diagonal is impossible, since its lower row would be below 1. Rows
  >= 2 force |w_2| <= (c-3)/2. So c >= 3 (for c = 2 no such rectangle exists), w_1^2 > x_1^2/4,
  and the shown points straddle column 0.
- (gamma-side) K = {ℓ, d}, adjacent. The other corners are ℓ + n and d + n with
  n = k(-(c-1), |x_1|) for a real k > 0 that makes n an integer vector (k < 0 puts ℓ + n
  above row 1). Here c >= 2 by (F1). Both have negative column and row
  > 1, so they are white. They form an oblique pair with both columns negative.
- The rotated cases {r, d} follow by the half turn.
- |K| = 3 is impossible. With {ℓ, D}, beta puts the other diagonal strictly inside (a,b). With
  {ℓ, d, r}, ℓ and r are opposite and d is adjacent to both, so
  (−x_1, c-1)·(−x_2, c-h) = 0, that is, x_1 x_2 = (c-1)(h-c). The left side is negative and the
  right side is nonnegative.

So no tilted rectangle is hidden, and every weak one shows exactly two points, never a
singleton and never a vertical pair. In particular the pair set H never enters, so the argument
works for every H.

**No axis-aligned rival** (Lemma "rival").

- *Horizontal pairs* occur only in alpha, beta, and gamma-diag, and there the two columns straddle
  column 0. Their black rows are {1} and {h}, which are disjoint.
- *Oblique pairs*: the rival needs the two crossed points (col e_+, row e_-) and
  (col e_-, row e_+). In alpha, beta, and gamma-diag their rows are those of P, inside [2, h-1],
  so they are black only in column 0, and they cannot both be in column 0. In gamma-side both
  crossed points have negative column and row > 1, so they are white.

**No two weak tilted rectangles show the same P.** Both contain P, so their doubles are within
2W_h of each other, hence the same double, by the gap.

- If P is a diagonal of both, their black diagonals have the same midpoint and length. Comparing
  the black pairs of alpha {ℓ,r}, beta D, gamma {ℓ,d}, and gamma' {d,r} shows that only identical
  pairs agree. For example, alpha against gamma forces c = h, x_1' = x_1 + x_2, and
  |x_1'| = x_2 - x_1, so x_2 = 0.
- If P is a side of one (gamma-side), it is not a diagonal of the other: diagonal presentations
  straddle column 0, while gamma-side presentations lie on one side.
- If P is a side of both, the black sides are translates B' = B + t with t = n - n'. A translate
  either keeps the order of the endpoints by column or swaps it, and since B + t = B' as sets we
  check both matchings. Two left sides {ℓ, d}, {ℓ', d'}: matching ℓ to ℓ' and d to d' gives
  t_1 = 0 (both d in column 0) and t_2 = 0 (both ℓ in row 1), so t = 0; matching ℓ to d' gives
  t = (-x_1, c'-1) and then ℓ' = d + t has column -x_1 > 0, impossible. Two right sides follow
  by the half turn. A left side {ℓ, d} and a right side {d', r'}: matching d to d' gives t_1 = 0
  but then ℓ + t = r' needs x'_2 = x_1 < 0, impossible; matching ℓ to d' gives
  t_1 = -x_1 > 0, while t_1 = n_1 - n'_1 < 0 because n_1 = -k(c-1) < 0 and n'_1 > 0 (the
  other corners of a right side lie at positive columns). So t = 0 and R = R'.

Presentations of three or more points are unique by Lemma "three corners". So Z is valid.

## Evidence

- Windows (sea 1, double, sea h and the reverse, 2W_h + 1 sea columns each side): every edge is
  good for both odd|even and top|bottom partitions, h = 5..10 (h = 11, 12 running).
- Minimal boards (no end padding, gap 2W_h + 1), checked directly by `verify_narrow.collision`:
  h = 5, 6, 7 (both partitions), h = 8 (odd|even, width 421, excess 16), and a C_5 graph on 5 and
  7 rows (excess 5). With gap W_h they still pass for h <= 7. With gap floor(W_h/2) they fail.
- Board check: `jis/scripts/general_theorem_board_check.py`, results in `jis/data/general_theorem_board_check.txt`.
- Exploratory scripts (not in the repository): `junction.py`, `alt.py`, `zmin.py`,
  `zboard.py`.

## Dead ends, kept

- Spreading the doubles in a sea of row 1: a row c with c - 1 even and >= 4 gives the horizontal
  trap ((k^2-1, 2k, k^2+1)).
- Steps between seas at odd distance >= 3: the vertical trap (3-4-5).
- Loops inside interior seas: the same traps.
- Both traps vanish when the two seas are the two boundary rows. That is the whole idea.
