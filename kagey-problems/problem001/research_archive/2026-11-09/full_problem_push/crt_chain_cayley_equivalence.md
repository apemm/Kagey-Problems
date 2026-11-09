# One countable graph for the rational-slope CRT P problem

9 November 2026. Uniformly bounded coloring of all actual vertical-rival
chain graphs for the 4/3 CRT placement is equivalent to finite
chromatic number of the countable graph defined below. This is a P-only
equivalence. A coloring does not automatically exclude mixed supports
or provide the remaining singleton cells.

Let R be the rational numbers with odd denominator. Define a graph G
on 2R. Distinct vertices u,v are adjacent if either

    25(u-v)^2+6(u-v)+1,
    25(u-v)^2-6(u-v)+1

is a rational square. The graph is undirected and translation invariant.
Its chromatic number is at least four. Whether it is finite remains open
in this work.

## From the CRT chain graphs to G

At height h, choose distinct primes p,q>25h, and put the parity label
{a,b}, with a odd and b even, at its unique column in [0,98pq) satisfying

    98 divides x,  3x=4a mod p,  3x=4b mod q.

For a vertical rival, its diagonal's horizontal gap D has |D|<h.
The congruences and the row bounds force

    3D=4(a_2-a_1)=4(b_2-b_1).

Consequently both owner labels have the same odd offset t=b-a. Write
D=4k and a_2-a_1=3k. Row parity makes k even, and 98 divides D
makes k a multiple of 98. Each connected P component therefore lies
in one fixed-t chain and one odd-row residue class modulo 294.

Choose a reference label in that component. Assign the label at
increment k the rational vertex k/t in 2R. The two possible opposite-
parity black diagonals have squared lengths

    25k^2+6tk+t^2,  25k^2-6tk+t^2.

Dividing by t^2 gives exactly the two edge tests defining G. The strip
containment test can only remove edges. A proper coloring of G therefore
colors every actual P component, and the same colors can be reused in
all components.

## Embedding every finite subgraph back into a strip

Take a finite vertex set in G and translate it so that its minimum is
zero. Choose a positive odd common denominator t that clears every
vertex and every rational square root used by its edges. These square
roots have odd denominators: their squares do, so their reduced
denominators cannot contain two. Multiply t by 49.

Writing k_i=t u_i now gives k_i in 98Z. Choose an odd integer a_0 and
use the labels

    a_i=a_0+3k_i,  b_i=a_i+t.

Every a_i is odd and every b_i is even. Each selected graph edge has
an integral odd diagonal length. Increase a_0 enough to make all its
vertical white endpoints positive, then choose h to contain every
label row and every selected endpoint. Increase h also beyond every
horizontal gap 4|k_i-k_j|.

For any distinct primes p,q>25h, the CRT congruences make the label
centers differ by 4(k_i-k_j) modulo 98pq. These are the actual
differences. Indeed, if a positive increment D<h wrapped across 98pq,
write the starting center as 98pq-r, with 0<r<=D. The congruence
would make the positive integer 3r+4a_i a multiple of p, although
it is less than 7h<p. This is impossible.

The resulting strip realizes every selected graph edge as an actual
vertical rival. Its vertical white pair has opposite row parity, so
the complete parity family supplies an axis rival. The owner cannot
occupy the common white column: that would create a tilted rectangle
with at least three inserted black corners, which this CRT placement
excludes. Thus the two compared rectangles are nondegenerate.

It follows that, for every positive integer C, the following are
equivalent:

1. Every actual in-strip 4/3 CRT P-chain graph has a proper C-coloring.
2. Every finite subgraph of G has a proper C-coloring.
3. G has a proper C-coloring.

For the last implication, enumerate the countable vertices. Proper
C-colorings of the first n vertices form a finitely branching tree
with a nonempty level at every n. An infinite branch gives the coloring.

## A four-color lower bound with actual strip containment

Take t=18375 and height h=62182. The four labels and relative columns are

| Odd row | Even row | Relative column |
|---:|---:|---:|
| 785 | 19160 | 0 |
| 7547 | 25922 | 9016 |
| 20777 | 39152 | 26656 |
| 39887 | 58262 | 52136 |

Every pair has a contained vertical rival. In lexicographic pair order,
the vertical completion intervals are

    [1,26706], [6616,33321], [1471,57576],
    [14162,32537], [10242,55567], [16857,62182].

The corresponding diagonal lengths are 26705,26705,56105,18375,45325,
and 45325. Thus these four vertices form K4 in an actual strip, not
only in the graph with containment omitted.

[verify_crt_cayley_k4.py](verify_crt_cayley_k4.py) independently checks
the six norms, containment, actual CRT centers, and the axis-rival
owners from the complete parity family. Its exact output is
[crt_cayley_k4_check.json](crt_cayley_k4_check.json).

The finite-menu unsafe-chain obstruction in
[crt_scaffold_independent_reductions.md](crt_scaffold_independent_reductions.md)
does not decide this coloring question. Discarding an entire chain and
coloring its vertices are different operations.

## Finite congruence colors cannot suffice

The graph has generators arbitrarily close to zero in both the real
and 2-adic metrics. For every integer r>=4, put

    z_r=3+2^r,
    d_r=2(z_r-3)/(25-z_r^2)
       =2^(r-3)/(1-3*2^(r-3)-2^(2r-4)).

The displayed denominator is odd, so d_r is in 2R and its exact
2-adic valuation is r-3. Direct substitution gives

    25d_r^2+6d_r+1=(1+z_r d_r)^2.

Thus x and x+d_r are adjacent for every vertex x. Moreover d_r tends
to zero in the real metric and in the 2-adic metric. A proper coloring
cannot be locally constant at any vertex in either metric.

More algebraically, no coloring that factors through a finite additive
quotient of 2R can be proper. Every such quotient is a finite 2-group:
multiplication by any odd integer is invertible on 2R and therefore
on its quotient. If its exponent is 2^s, choose r>=s+4. Then d_r
belongs to 2^s(2R) and maps to zero in the quotient, so adjacent
vertices receive the same quotient value.

This excludes finite congruence schemes. It does not exclude a finite
coloring with no such regularity, and it does not prove that G has
infinite chromatic number.

The generator identity, exact valuation, both convergence statements,
and finite-quotient argument have passed a separate independent review.
