# Two exact collision laws for the 1, x, h construction

8 November 2026. These are new analytical reductions, not an existence theorem. Coordinates are
(column, row), with double columns divisible by 4. The pure family has h congruent to 3 modulo 4.
Every double contains one odd and one even row. Statements about a pure region apply when every
rectangle under discussion stays in that region. Free transition gaps require separate checking.

## 1. The hidden-rectangle qualification

The definition permits one hidden rectangle. Rejecting every hidden rectangle is therefore not a
general-purpose validity test. The following local argument, communicated during the parallel audit,
makes that rejection sound in a pure 1, x, h region.

If a hidden lattice rectangle has an even side vector v, divide that side into two equal pieces.
The two half rectangles have the same presentation: their common midpoint side, with any black
points on it removed. Their symmetric difference consists of the four original black corners.
Thus such a hidden rectangle is invalid even when no outward extension fits.

A hidden rectangle in a pure 1, x, h region is necessarily tilted: a hidden axis-aligned rectangle
would require the same row pair in two double columns, contrary to distinctness of the double edges.
Every hidden tilted rectangle in the pure region is all-double. It cannot have two sea corners by
Lemma 12 of REPORT_1xh_construction.md. If it had one sea corner, the other three corners would have
columns divisible by 4, forcing the fourth column to be divisible by 4 as well. Write the all-double
rectangle's sides as (a,-b) and (c,d), with a,c positive multiples of 4 and ac=bd. At least one of b,d
is even, so at least one side vector is even. The bisection argument applies.

Consequently, excluding the report's law (i), including its hidden-completion case, is sound in the
pure region. This does not validate blanket hidden rejection in unrestricted free-gap layouts.

## 2. Only mixed side/diagonal collisions remain

Suppose two distinct tilted rectangles show the same two white cells W,Z.

If W,Z are a side of both rectangles, their black complementary sides have the form
{W+v,Z+v} and {W+w,Z+w}, where v and w are distinct vectors perpendicular to Z-W. The four
black points form a nondegenerate hidden rectangle.

If W,Z are a diagonal of both rectangles, the two black complementary pairs are distinct diameters
of the same circle. Their union is again a hidden rectangle.

In the pure family, that hidden rectangle is all-double by section 1, and hence contains a
three-double right angle. Thus, after law (i) has been excluded, a surviving tilted collision must
use W,Z as a side of one rectangle and a diagonal of the other. This supplies the precise residual
meaning of law (T).

The same argument applies to an oblique axis rival when W,Z are a diagonal of the tilted rectangle:
the tilted black diagonal and the axis black diagonal make a hidden rectangle. Thus the residual
four-double law (Q) also has W,Z as a side of the tilted rectangle.

In a mixed collision the two complementary black pairs are disjoint. A common black cell, together
with W and Z, would give three common corners and force the two rectangles to be identical.

## 3. One equation system contains both Q and T

Let A,B,C,D be four distinct black cells. Set

    U = B-A,  V = D-C,  S = (A+B)/2,  M = (C+D)/2.

Assume U has two nonzero components. The black pair A,B can be the complementary side of one
tilted rectangle, and C,D the complementary diagonal of a second rectangle with the same white
pair, exactly under these conditions:

    |U|^2 = |V|^2,
    (A+B-C-D) dot U = 0,
    W = (C+D-U)/2 and Z = (C+D+U)/2 are integral white grid cells,
    S != M and V != U,-U.

The second rectangle is axis-aligned exactly when

    V = (U_x,-U_y) or V = (-U_x,U_y).

These are law (Q). All remaining nondegenerate choices give a tilted second rectangle and hence
law (T).

Proof. The side rectangle has vertices W,Z,A,B. Its corresponding side vectors are U and S-M,
which are perpendicular precisely by the displayed dot-product condition. Its area is positive
because U is nonzero and S differs from M. The other rectangle has diagonals WZ and CD, with the
same midpoint and equal lengths. The exclusions V != +/-U prevent coincident diagonals. Equal
diagonal lengths and a common midpoint imply a rectangle because its adjacent sides are
(U+V)/2 and (U-V)/2, whose dot product is zero. Those sides are axis-aligned exactly in the two
reflection cases. Conversely, every mixed collision has these midpoint and length relations.

For all-double black cells, write

    A=(4i,r), B=(4j,s), C=(4k,t), D=(4l,u).

The two equations become the integer relations

    16(j-i)^2 + (s-r)^2 = 16(l-k)^2 + (u-t)^2,
    16(i+j-k-l)(j-i) + (r+s-t-u)(s-r) = 0.

The white cells are

    ( 2(k+l-j+i), (t+u-s+r)/2 ),
    ( 2(k+l+j-i), (t+u+s-r)/2 ).

Thus integrality requires r+s+t+u even. The whites are in even columns. If their columns are 2
modulo 4 and their rows are strictly between 1 and h, they are automatically white, independently
of the middle-cell choices. If they lie in double columns, their whiteness is checked against those
two double edges. A genuine all-double mixed tilted collision must have |j-i| != |l-k|: equality,
together with the length equation, gives either a degenerate pair or the axis reflection case.

For Q alone there is a shorter factorization. Up to reflections, take positive integers d,n,b,c
with

    bc = 16dn.

The four required black cells are

    (4i,r),                 (4(i+d),r+b),
    (4(i+n),r+b-c),         (4(i+n+d),r-c).

The white cells are (4(i+n),r-c) and (4(i+n+d),r+b-c). Conversely, every all-double Q configuration
has this form after orienting the tilted side and applying reflections. Thus Q asks for two equally
spaced slot pairs, oppositely directed row increments, and one product identity. If n=d, the two
middle forced black cells share a column and their row difference c must be odd. Whiteness and the
parity-double conditions are still part of the test.

## 4. A local law T missed by three-double right angles

For any positive odd d and integer r, the following four black cells force a mixed collision:

    A=(4i,r),             B=(4(i+d),r+8d),
    C=(4i,r+d),           D=(4(i+2d),r+5d).

The two whites are

    W=(4i+2d,r-d),        Z=(4i+6d,r+7d).

The vectors U=(4d,8d) and V=(8d,4d) have equal squared length 80d^2, while
S-M=(-2d,d) is perpendicular to U. Because d is odd, A,C can occupy one parity double, and W,Z
are middle columns. If

    2 <= r-d and r+8d <= h,

then both white rows are strictly interior. The collision is therefore independent of every x_j.
Equivalently, an order must not simultaneously contain

    {r,r+d} at slot i,
    row r+8d at slot i+d,
    row r+5d at slot i+2d.

Reflections give the other orientations. This is a family of constraints involving three slots,
rather than an unspecified collision between two rectangles.

The smallest displayed instance is h=11,d=1,r=3. The consecutive doubles

    {3,4}, {2,11}, {1,8}

force the two rectangles

    {(2,2),(6,10),(0,3),(4,11)},
    {(2,2),(6,10),(0,4),(8,8)}.

Their common presentation is {(2,2),(6,10)}. None of the six black cells in these three doubles
forms a right angle. This was checked by exact integer dot products. The example proves that the
mixed law is not implied just by excluding law (i). It does not assert that all other laws are absent.

## 5. Four-double law Q first appears at height 13

Claim. A four-double oblique axis-rival configuration whose whites are a side of the tilted rectangle
requires h>=13. At h=13 such a configuration exists. Among the admissible heights h=3 mod 4, its
first possible height is therefore 15.

Proof. In the standard tilted-rectangle representation the positive horizontal components a,c
are multiples of 4, with ac=bd and total row span b+d. If a=c, the two middle corners share a
column. For any choice of a white side, one original black corner and one crossed rival cell then
occupy that column. Their row difference is b or d. These distinct black cells must have opposite
parities, so that vertical component is odd. Since bd=a^2 is divisible by 16, the other component
is at least 16. Thus b+d>=17 in this case. If a!=c, they are distinct positive multiples of 4, so
bd=ac>=32. The inequality (b+d)^2>=4bd gives b+d>=12. Both cases imply h>=13.

For sharpness, use the black cells

    A=(0,9), B=(4,13), C=(8,5), D=(12,1).

The tilted rectangle has white side W=(8,1), Z=(12,5) and black side A,B. Its axis rival has
white diagonal W,Z and black diagonal C,D. These fit in height 13. They can be completed to
the four distinct parity doubles

    {2,9}, {4,13}, {5,6}, {1,8}.

No three of these eight black cells forms a right angle. Thus Q is another independent obstruction,
and it introduces a genuinely new geometric constraint at h=15 in the pure admissible family.
This does not prove that the family fails at height 15.

## 6. Verification

The dependency-free Node script `check_construction_obstructions.js` checks both rectangle pairs,
checks absence of three-black right angles in the two displayed completed patches, verifies the
scaled mixed family for every odd d<=19, and exhausts all all-double tilted shapes through height 15
to verify the minimum-height claim for Q. These finite checks support the formulas. The proofs above
establish the general statements.

These reductions leave the global ordering problem open. They replace the report's undescribed
Q/T relations with exact quadratic equations and isolate two independent local obstructions.
