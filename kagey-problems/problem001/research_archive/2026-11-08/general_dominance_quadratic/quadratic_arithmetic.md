# Arithmetic placements of every parity double

8 November 2026.

Two explicit placements are available for every height. The first has quadratic
width and excludes every tilted right angle supported on double cells. The second
has width O(h^(5/2)) and gives an identifying set consisting of all required
doubles, with the other columns empty of black cells. The second placement
therefore excludes every collision forced by double cells alone.

Neither result supplies the singleton cells in the remaining columns. In
particular, neither proves an equality construction of quadratic width.

## 1. A quadratic placement with no three-double right angle

Put n_o=ceil(h/2) and n_e=floor(h/2). Index the odd rows by
o_a=2a+1, 0<=a<n_o, and the even rows by e_b=2b+2, 0<=b<n_e.
Choose distinct primes p,q>10h. For each edge (a,b), let

    x_ab = CRT(a mod p, b mod q),    0 <= x_ab < pq.

Place the double {o_a,e_b} in column 4x_ab. Each edge occurs exactly once,
and distinct edges occupy distinct columns. Taking p between 10h and 20h
and q between 20h and 40h gives width less than 3200h^2+1.

**Theorem 1.** No three marked cells form a tilted right angle. The statement
does not require the fourth corner to lie in the strip.

**Proof.** Consider an odd-row vertex at the edge (a_0,b_0). If both other
rows are even, the product of the vertical leg components is odd. The product
of the horizontal components is divisible by 16, so their dot product is nonzero.

If both other rows are odd, reduce the dot product modulo p. It becomes

    20(a_1-a_0)(a_2-a_0).

Since p>10h, one of the actual index differences must be zero. That leg is
horizontal. A right angle containing a horizontal leg is axis-aligned.

For one odd-row leg and one even-row leg, reduction modulo p gives

    2(a_1-a_0) [8a_2+2b_2-10a_0+1].

The bracket is an odd integer of absolute value less than 10h. It is nonzero
modulo p. Hence a_1=a_0, and the angle is again axis-aligned.

At an even-row vertex, use q instead. The same-parity coefficient is 20,
and the mixed bracket is

    8b_2+2a_2-10b_0-1.

It has the same nonvanishing property. This covers all parity choices. A leg
joining two points in one double column is already vertical, so it cannot
produce an omitted tilted right angle. QED.

This theorem resolves the three-double placement problem without a split-track
capacity restriction. It does not address the P, Q, or T laws by itself.

## 2. The quadratic placement has an unavoidable P collision

The edges (a,a) and (a+1,a+1) occupy columns 4a and 4a+4. Their marked cells

    A=(4a,2a+1),    C=(4a+4,2a+4)

have diagonal length 5. Their other vertical diagonal is

    W=(4a+2,2a),    Z=(4a+2,2a+5).

For a>=1 and 2a+5<=h, both cells lie in the strip. The parity double
{2a,2a+5} occurs elsewhere in the construction. It gives an axis rectangle
with the same presentation as the tilted rectangle with diagonal AC.
Their symmetric difference consists of four required double cells. Coloring
W or Z black cannot repair the collision.

In particular, the quadratic placement fails from h=7 onward, independently
of every later singleton choice. At h=7, take a=1.

Changing the two CRT coefficients to fixed positive coprime constants A,B does
not remove this mechanism in all sufficiently large heights. The index increment
(B,A) gives CRT column increment AB when it does not wrap. Its physical
horizontal difference is D=4AB. The integer Pythagorean triple

    D, (D^2-4)/4, (D^2+4)/4

has an odd vertical leg and an odd hypotenuse. A mixed odd/even row difference
can realize that vertical leg by choosing the starting edge appropriately.
For sufficiently large h, there are more than AB translates of the row indices
for which both vertical completion rows lie inside the strip. The corresponding
starting CRT residues are distinct. At most AB residues can wrap when AB is
added, so one translate has the stated column difference. Thus fixed coefficients
cannot make this family an all-height equality construction.

## 3. A wider placement excludes every double-supported collision

Let S be the least power of two such that S^2>4h. Then S<=4 sqrt(h).
Choose primes

    S^2+4 < p < 2(S^2+4),
    2(S^2+4) < q < 4(S^2+4).

Use the same CRT indices, now placing edge (a,b) at column Sx_ab.
The width is less than Spq+1=O(h^(5/2)). Let B be the set of these marked
double cells. Every other cell, including every cell in a non-double column,
is white in the following theorem.

**Theorem 2.** B is an identifying set for the rectangles in its strip.
Equivalently, no two distinct rectangles have symmetric difference contained
in B. All parity doubles occur once, but the non-double columns have no black
cell, so this is not an equality board.

The proof uses four reductions.

### 3.1 Three marked tilted corners are impossible

For three rows of the same parity, reduction modulo p or q gives

    (S^2+4)(a_1-a_0)(a_2-a_0)=0

or its even-row counterpart. The prime exceeds both S^2+4 and the index
range, so one leg is horizontal.

If both nonvertex rows have parity opposite to the vertex, the vertical
product is odd and cannot cancel a multiple of S^2. If exactly one has
opposite parity, a horizontal leg already gives an axis-aligned angle. Otherwise
the vertical product has the same 2-adic valuation as the
nonzero same-parity row difference. That difference has absolute value at most
h-1<S^2. Its valuation is therefore less than v_2(S^2), again impossible.

No tilted rectangle has three marked vertices. No axis rectangle has four
marked vertices, because its row pair would occur in two double columns.
Thus there is no hidden rectangle.

### 3.2 Vertical axis rivals are impossible

Such a rival needs an odd-length vertical white diagonal, because its row pair
is a parity edge. The tilted black diagonal therefore has odd vertical
component d and horizontal component X divisible by S. If its length is L,

    (L-d)(L+d)=X^2.

Both L and d are odd. Exactly one of L-d,L+d has 2-adic valuation 1.
The other has valuation at least 2v_2(S)-1 and absolute value at least S^2/2.
But an in-strip vertical completion has L<=h-1 and |d|<=h-1, giving
|L+d|,|L-d|<=2(h-1)<S^2/2. This is impossible.

### 3.3 Mixed side/diagonal collisions with an oblique side are impossible

Let A,B be the marked complementary side and C,D the marked complementary
diagonal. Write

    U=B-A,  V=D-C,  H=A+B-C-D.

The mixed equations are

    |U|^2=|V|^2,    H dot U=0,

with U_x U_y nonzero, H nonzero, and V not equal to U or -U.
Every horizontal coordinate is divisible by S. The norm equation implies
that U_y and V_y have the same parity.

If U_y and V_y are odd, then

    S^2 divides (V_y-U_y)(V_y+U_y).

Unless V_y=+/-U_y, exactly one factor has valuation 1. The other must have
absolute value at least S^2/2>2h, contrary to the row range. Thus
V_y=+/-U_y and |V_x|=|U_x|. The perpendicularity equation then implies
S^2 divides H_y, since U_y is odd. But |H_y|<=2(h-1)<S^2, so H_y=0,
and then H_x=0. This violates nondegeneracy.

Suppose both increments are even. Each marked pair then has one row parity.
If all four rows have the same parity, use p for odd rows or q for even rows.
For odd rows, write t=a_B-a_A, u=a_D-a_C, and
L=a_A+a_B-a_C-a_D. The two equations imply

    (S^2+4)(t^2-u^2)=0 mod p,
    (S^2+4)Lt=0 mod p.

Since |t+u|,|t-u|<h<p, the first gives u=+/-t as integers. Since t is
nonzero and |L|<h<p, the second gives L=0. The row midpoints agree.
Perpendicularity forces the column midpoints to agree as well, violating
H nonzero. The even-row case is identical.

It remains to put the side pair on odd rows and the diagonal pair on even
rows, or the reverse. Write U_y=2t, V_y=2u, H_y=2L, and K=S^2/4.
Then

    K divides u^2-t^2,    K divides Lt,
    L+t+u is odd.

The last assertion follows by writing the side rows as 2a+1 and the diagonal
rows as 2b+2. Since K is an even power of two, the first divisibility forces
t and u to have the same parity. Hence L is odd, and the second forces
K to divide t. But |t|<h/2<K, so t=0. This contradicts the oblique-side
assumption. The reverse parity assignment gives the same parity identity.

### 3.4 Horizontal axis rivals are impossible

Their marked complementary side has two cells at the same row. If that row is
odd, the corresponding CRT indices differ by a nonzero multiple of p.
For an even row use q. Thus the horizontal side length L=S d satisfies
d>=min(p,q)>S^2>4h.

The marked tilted diagonal has horizontal length S e and nonzero vertical
component v. Equal diagonal lengths require

    v^2 = S^2(d^2-e^2) >= S^2(2d-1) > h^2,

because |e|<d. This contradicts |v|<=h-1.

### 3.5 Completion of the identifying-set proof

Two distinct rectangles cannot share three corners. Hence a collision involving
a tilted rectangle with at most one shared corner would require three marked
tilted corners, already excluded. With two shared corners, neither can be black:
a black shared corner would again give three marked tilted corners. Thus a
collision with two shared corners has a common white pair. If that pair is a side in both rectangles or a diagonal in
both, the four complementary marked cells form a hidden rectangle. Otherwise
the collision is mixed side/diagonal and is excluded by sections 3.2 to 3.4.

For two axis rectangles, a diagonal white pair determines the rectangle.
A vertical white pair uses a uniquely occurring double edge. Two different
rectangles with one common white cell would need two black rows of the same
parity in its column. Two rectangles with the same horizontal white pair would
repeat a double edge in two columns. Each alternative is impossible. There are
no hidden rectangles, so these cases prove injectivity. QED.

## 4. What the arithmetic reduction leaves open

Theorem 2 removes every immutable obstruction supported on the required doubles.
A sea-completion argument could therefore start from a valid marked set.
It must still assign one black cell to every other column while preserving
identification. Three-corner and collision certificates using both sea cells
and double cells remain possible. Validity of the initial marked set does not
imply such a completion exists.

For quadratic width, Theorem 1 gives a specific alternative to the earlier
split-track condition. Its failure in section 2 identifies the next arithmetic
requirement: vary the column rule sufficiently to eliminate odd-length
Pythagorean completions, while keeping the modular right-angle argument.
Fixed CRT coefficients do not meet that requirement.

The O(h^(5/2)) placement shows that a power-of-two separation removes the
remaining double-supported laws at a square-root cost in width. Reducing that
cost requires a nonuniform placement or a different invariant. It cannot come
from filling the sea around the unmodified quadratic CRT placement.

## 5. Independent finite checks

`quadratic_arithmetic_check.py` constructs the columns by CRT and checks actual
integer coordinates. It does not use modular divisibility to reject candidates.

- Heights 3 through 31: the quadratic placement has no tilted marked right angle.
- Height 7: it finds an in-strip Pythagorean vertical completion in the quadratic
  placement.
- Heights 3 through 25: the wider placement has no tilted marked right angle,
  no in-strip vertical P configuration, and no solution of the nondegenerate
  oblique mixed equations. A separate scan allows horizontal and vertical
  sides and finds no mixed solution whose completion stays in the height.

The complete run took 3.19 seconds. Results are saved in
`quadratic_arithmetic_checks.json`. The proofs establish the all-height claims.
