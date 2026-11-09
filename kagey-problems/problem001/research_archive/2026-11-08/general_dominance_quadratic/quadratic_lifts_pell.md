# Layered CRT placements and the Pythagorean pair graph

8 November 2026.

The P obstruction in the quadratic CRT placement can be removed with
h^(o(1)) layers. This preserves the exclusion of every three-double tilted
right angle and gives width h^(2+o(1)). Four-double mixed collisions and sea
completion remain separate requirements.

A constant number of layers is not established. Four layers are already
necessary for one P pair graph. Moreover, every coloring with a fixed period
along a diagonal track fails at some sufficiently large height. The latter
does not exclude a bounded number of colors with aperiodic assignments.

## 1. Layering preserves the modular scaffold

Use the notation of `quadratic_arithmetic.md`. Choose primes p,q>10h of
order h, and set M=pq. Edge (a,b) initially occupies slot

    x_ab = CRT(a mod p,b mod q),    0<=x_ab<M,

with physical column 4x_ab. Assign each edge a color k_ab in
{0,...,K-1}, and replace its slot by

    x'_ab = x_ab + 2 k_ab M.

The CRT congruences are unchanged. The proof of Theorem 1 in the preceding
note therefore still excludes all three-double tilted right angles.

Different layers are separated by more than M slots, hence by more than
4M physical columns. This exceeds both h and 2W_h, where
W_h=1+floor((h-1)^2/4). In particular, no vertical Pythagorean completion can
use black diagonal points from different layers. The width is at most
4(2K-1)M+1=O(Kh^2).

## 2. The exact pair graph lies on diagonal tracks

Suppose two double cells support a vertical P completion. Its vertical
diagonal has length L<=h-1, so its horizontal component 4delta satisfies
0<4delta<=L. Orient the two double columns from left to right.

For their edge indices, the CRT congruences imply

    a_2-a_1 = b_2-b_1 = delta.

Indeed, each index difference has absolute value below h, and delta<h/4.
The congruences modulo p and q therefore lift to integer equalities.
Consequently, the two edges lie on one track b-a=k. Put t=2k+1, an odd
nonzero integer with |t|<=h-1. The two choices of opposite-parity black
diagonal give

    L^2 = 20delta^2 + 4t delta + t^2,
    L^2 = 20delta^2 - 4t delta + t^2.

The completion must also fit vertically, but dropping that condition gives a
convenient graph containing all forbidden pairs. For T=|t|, let D_T(h) contain
the positive integers delta for which one of these equations has an integer
L between 1 and h-1. Join two track indices when their difference belongs
to D_T(h).

Each graph has maximum degree at most 2|D_T(h)|. The same color palette can
be reused on different tracks, because no P pair joins two tracks.

## 3. A self-contained bound on the P distances

**Proposition.** Uniformly for odd 1<=T<=h-1,

    |D_T(h)| <= 2 tau(T^2)^2 R_h,

where tau is the positive divisor function and

    R_h = 1 + floor(log(9h^2)/log((3+sqrt(5))/2)).

**Proof.** For either sign, put X=10delta+/-T and Y=L. Then

    X^2-5Y^2 = -4T^2.

Both X and Y are odd. Therefore

    alpha=(X+Y sqrt(5))/2

belongs to R=Z[phi], where phi=(1+sqrt(5))/2, and its norm is -T^2.

The ring R is norm-Euclidean. To see this, write a quotient as u+v phi and
round u,v separately to integers. The residual coefficients lie in
[-1/2,1/2], and their norm u^2+uv-v^2 has absolute value at most 3/4<1.
The Euclidean algorithm gives unique factorization.

Since alpha times its conjugate equals -T^2, alpha divides T^2 in R.
If an ordinary prime r occurs in T with exponent e, its factorization in R
has at most two prime factors counted with multiplicity. Its contribution
to the number of divisor classes of T^2 is at most (2e+1)^2. In the
ramified case the count is 4e+1, which satisfies the same bound. Thus there
are at most

    product_{r^e || T}(2e+1)^2 = tau(T^2)^2

possible associate classes for alpha.

It remains to count representatives of one class. The horizontal diagonal
bound gives delta<h/4, so |X|<3.5h and Y<h. The negative norm gives
alpha>0 and conjugate(alpha)<0. Hence

    1/(3h) < alpha < 3h.

Two positive associated elements with the same norm have ratio a positive
unit of norm 1. If the ratio u exceeds 1, its trace u+1/u is an integer
greater than 2. Thus u+1/u>=3, giving u>=(3+sqrt(5))/2. Representatives
in one associate class are multiplicatively separated by at least this
factor. At most R_h representatives lie in the displayed interval.

Finally, one pair (X,Y) determines at most two positive values of delta,
one for each sign of T. Multiplying by 2 proves the bound. QED.

This proof needs no classification of the unit group. The usual elementary
divisor estimate tau(n)=n^(o(1)) now gives

    max_{1<=T<h} |D_T(h)| = h^(o(1)).

For completeness, the divisor estimate follows by fixing epsilon>0. For all
sufficiently large primes r and all e>=1, e+1<=r^(epsilon e). The finitely
many smaller primes contribute at most a constant times n^epsilon, after
slightly increasing epsilon. This proves tau(n)<=C_epsilon n^epsilon.

## 4. Consequence for the layered placement

Greedy coloring of each track needs at most

    K_h = 1 + 4 R_h max_{1<=T<h, T odd} tau(T^2)^2

colors. Reuse this palette for all tracks, and use the lifted columns in
section 1. The resulting placement has these properties:

- Every parity edge occurs exactly once.
- No three marked cells form a tilted right angle.
- No marked pair has an in-strip vertical P completion.
- Its width is h^(2+o(1)).

This is a partial scaffold theorem. It does not assert that four-double mixed
collisions are absent, or that singleton cells can fill the remaining columns.

## 5. A four-color lower bound

Take t=55 and track-index offsets 0,4,15,25. Every pair of offsets has a P
distance. The following table gives the sign in
L^2=20delta^2+/-4t delta+t^2.

| Offsets | delta | Sign | L |
| --- | ---: | :---: | ---: |
| 0,4 | 4 | + | 65 |
| 0,15 | 15 | - | 65 |
| 0,25 | 25 | + | 145 |
| 4,15 | 11 | - | 55 |
| 4,25 | 21 | - | 85 |
| 15,25 | 10 | + | 85 |

Set the first track index to a=10, so b=a+27. The four required edges are

    {21,76}, {29,84}, {51,106}, {71,126}.

All six vertical completions fit in rows 1 through 146. Their lower and
upper rows are, in table order,

    (20,85), (31,96), (1,146),
    (40,95), (35,120), (46,131).

Their horizontal differences are exactly four times the listed deltas. The
CRT residues on this track increase by those deltas without wrapping, since
all involved row indices are below p and q. Thus the actual P graph contains
a K_4 at h=146, and at every larger height. A layering scheme assigning only
three colors cannot remove every P pair.

## 6. Every fixed-period coloring eventually fails

**Proposition.** Fix a positive integer N. There is a height H_N such that,
for h>=H_N, no coloring periodic with period N along the track b=a removes
all P pairs. This holds regardless of the number of colors.

**Proof.** Use the Pell equation

    X^2-5Y^2=-4.

Start from (X,Y)=(1,1), and repeatedly multiply X+Y sqrt(5) by
9+4sqrt(5). The update matrix

    [[9,20],[4,9]]

has determinant 1, so it acts as a permutation modulo 10N. A positive power
returns (1,1) to itself modulo 10N. The corresponding positive integers
X,Y have X>1 and satisfy X=1 mod 10N. Set delta=(X-1)/10. Then
delta is a positive multiple of N and

    Y^2=20delta^2+4delta+1.

On the track b=a, edges a and a+delta therefore have a Pythagorean black
diagonal. Choose a sufficiently large constant so the lower completion row
is at least 1, then choose H_N to contain the upper completion row and both
doubles. Their colors agree by period N, and their within-layer physical
separation is 4delta. The collision survives the lift. QED.

The same argument applies to any rule periodic in both row indices, or in
the original slot index. It rules out bounded-period arithmetic colorings.
It does not rule out a bounded number of colors arranged aperiodically.

## 7. Remaining arithmetic question

The unresolved constant-color problem is concrete: are the chromatic numbers
of these finite P graphs bounded independently of h and t? The four-color
example and periodic-color obstruction are insufficient to answer it.
The divisor argument proves a subpolynomial upper bound and supplies an
explicit finite coloring procedure.
