# A mixed collision in the one-prime placement

8 November 2026. The placement in `one_prime_scaffold.md` puts the parity double
indexed by `(a,b)` in column `4(a+p b)`, where `p>10h` is prime. It excludes
every tilted right angle on three marked cells. Separating its Pythagorean
pair graph also has a subpolynomial layer bound. Neither fact excludes the
four-black mixed side/diagonal mechanism.

The following exact example shows that the mixed mechanism really occurs.
It concerns an allowed prime choice, not every choice of prime at this height.
It also does not assert that the collision survives every coloring of the
Pythagorean graph.

## 1. A parameter identity

Let `k` be a positive even integer, and put

    t = 16 k^2 + 16 k + 5,
    c = 8 k + 2,
    p = (k t - c)/2,
    h = t + c + 1.

Whenever `p` is prime and `p>10h`, these are permitted parameters for the
one-prime placement. Set

    b_1 = (t-3)/2,       b_2 = (t+1)/2 = b_1+2.

Take the following four marked points, specifying their double indices and
their selected row:

| Point | Double index `(a,b)` | Selected row |
|---|---|---|
| A | `(1,b_1)` | `3`, odd |
| B | `(c+1,b_2)` | `t+3`, even |
| C | `(0,b_1)` | `t-1`, even |
| D | `(c+1,b_2)` | `2c+3`, odd |

The points `B,D` are the two cells of one double. All three double indices
are within the height-`h` ranges. Let `X_A,X_B,X_C,X_D` be their physical
columns. Define the two additional lattice points

    W = (X_A-2, c+1),
    Z = (X_B-2, t+c+1).

These points are white in the double-only placement: their columns are
congruent to `2 mod 4`, while every double column is divisible by four.
All six rows lie between `1` and `h`.

The first rectangle has sides

    U = B-A = (4kt,t),
    T = W-A = (-2,8k),

because `2p+c=kt`. Thus `U dot T=0`, and `ABZW` is a nondegenerate tilted
rectangle. The second rectangle uses `C,D` and `W,Z` as its two diagonals.
Their midpoints agree, and

    V = D-C = (4kt+4,16k+8-t),
    |V|^2-|U|^2 = 16(16k^2+16k+5-t) = 0.

The equal, distinct diagonals therefore form a nondegenerate tilted
rectangle. Equivalently, with `H=A+B-C-D=(4,-16k)`, the mixed equations are

    |U|^2 = |V|^2,     H dot U = 0,     H != 0,     V != +/-U.

Both rectangles have exactly the white presentation `{W,Z}`. Their symmetric
difference is `{A,B,C,D}`, so subsequent singleton choices cannot repair this
particular double placement. Coloring `W` or `Z` black leaves the two
presentations equal.

## 2. An explicit prime instance

Take

    k=24,  t=9605,  c=194,  p=115163,  h=9800.

Trial division through `floor(sqrt(p))=339` verifies that `p` is prime, and
`115163>98000`. The points are

    A=(2211590256,3),       B=(2212512336,9608),
    C=(2211590252,9604),    D=(2212512336,391),
    W=(2211590254,195),     Z=(2212512334,9800).

In particular,

    U=(922080,9605),
    V=(922084,-9213),
    H=(4,-384).

The two distinct tilted rectangles are `{A,B,W,Z}` and `{C,D,W,Z}`.
This verifies that the remaining mixed-collision condition is substantive,
even though small-height scans of related arithmetic placements found none.

The parameter identity does not assert that its cubic polynomial `p(k)`
takes prime values infinitely often. One verified prime instance is enough
to disprove universal mixed-collision exclusion for the one-prime placement.

## 3. The remaining coloring problem

The Pythagorean graph uses pairs of double indices. This certificate instead
uses three double indices, including both marked cells of one of them. A
coloring construction must therefore account for a hypergraph of mixed
certificates as well as the Pythagorean graph.

Separate color classes by gaps exceeding `2W_h`. A tilted collision using
black cells in different classes then cannot fit across the gap. Vertical
axis rivals still depend on the full parity edge set, so their Pythagorean
pairs must be separated explicitly. Three-marked-corner obstructions are
already excluded by the arithmetic placement. The remaining mixed
certificates involve two, three, or four distinct double indices.

A bounded number of colors for both kinds of certificate would yield an
identifying set of doubles of quadratic width. It would still leave the
singleton completion problem. The present divisor bound controls only the
Pythagorean graph, and supplies no bound for the mixed hypergraph.

`check_one_prime_mixed.py` verifies the numerical certificate directly using
integer coordinates, including primality, edge indices, midpoint equality,
perpendicularity, equal norms, row containment, and the two presentations.
