# When a filler can retain an inserted right angle

9 November 2026. An inserted right angle is not automatically fatal.
Its completion must be in a singleton column, and the filler there must
have the same row-part as the completion without occupying that cell.
Several triangles impose additional consistency and uniqueness tests.

This note gives the exact local rule, exhibits two such triangles in an
already valid equality board, and proves a limitation on universal
filler schemes. If a fixed set of double columns must work for every
assignment of the complete balanced pair family, its width is
Omega(h^(5/2)). This last statement allows the fillers to depend on the
assignment. It does not obstruct coordinated placement of the labels.

## 1. The exact completion rule

Partition the rows into nonempty parts A and B. Each edge of the
complete bipartite graph A times B occurs as a double in exactly one
column. Write D for these columns and S_D for their fixed black cells.
Every other column will receive one black filler cell.

Consider only tilted rectangles with three corners in S_D and fourth
corner W inside the board. The three black corners and W are distinct.
Completions outside the board do not create a rectangle in this family.

If W is in a double column, no filler can repair the rectangle.
If W is already black, it is a hidden rectangle. Such a rectangle is
invalid on boards with both dimensions at least four, by
[the hidden-rectangle theorem](hidden_rectangles_and_exact_hypergraph.md).
If W is white, its column contains an endpoint z in the opposite row
part from W_y. The label {z,W_y} occurs in another double column,
giving an axis rectangle with the same singleton presentation {W}.
The two rectangles are distinct because the original is tilted.

Suppose instead that W lies in a singleton column x with filler row f_x.
There are exactly three possibilities relevant to this rectangle:

* If f_x=W_y, the rectangle is hidden.
* If f_x and W_y belong to opposite row parts, the label {f_x,W_y}
  supplies an axis rectangle with the same singleton presentation.
* If f_x and W_y are different rows in the same part, W remains white
  and this rectangle has no axis singleton rival.

The last condition is sufficient for the axis test, not for every
possible tilted competitor.

For each singleton column x, let T_x be the set of rows of its
inserted-triangle completions. Also record the number of distinct
tilted rectangles completing at each cell (x,y). If two distinct
rectangles complete at the same cell, no filler repairs their collision:
they have presentation {(x,y)} when it is white, and both have empty
presentation when it is black.

Consequently the following is an exact local criterion. It is possible
to make every inserted-triangle completion white, avoid all its axis
singleton rivals, and distinguish all these rectangles from each other
if and only if:

1. No in-board completion is in D.
2. Each completion cell belongs to only one distinct tilted rectangle.
3. At each singleton column with T_x nonempty, T_x lies in one row part
   and does not exhaust that part.

When these conditions hold, choose f_x from that part minus T_x.
The choices at different columns are independent for this particular
test. Columns with no completion impose no restriction here.

This criterion concerns triangles supported by S_D. Fillers can create
additional triangles, mixed four-cell collisions, or singleton
collisions involving fewer than three inserted cells. A complete-board
proof must still exclude those events.
There can also be an immutable mixed collision already in S_D with no
inserted right angle at all, as in
[the one-prime counterexample](../../2026-11-08/general_dominance_quadratic/one_prime_mixed_obstruction.md).
Thus the local criterion is not a substitute for checking the fixed
double scaffold itself.

## 2. The rule already retains triangles in an equality board

The verified seven-row, twenty-one-column board has these column sets,
in zero-based order:

    16,36,5,25,2,2,14,7,12,27,2,7,67,7,47,7,7,56,45,34,23.

It contains all twelve odd/even labels and 33 black cells. Exactly two
in-board tilted triangles use three of its fixed double cells:

| Right-angle vertex | Other two black corners | Completion | Filler |
|---|---|---|---|
| (17,6) | (14,4), (19,3) | (16,1) | (16,7) |
| (6,4) | (8,2), (9,7) | (11,5) | (11,7) |

Their perpendicular leg dot products are -6+6 and 6-6. Both completion
rows are odd and differ from the odd filler row seven. Neither cell is
the completion of another inserted triangle. Thus both triangles pass
the exact local rule.

The standalone checker
[verify_filler_triangle_mechanisms.py](verify_filler_triangle_mechanisms.py)
also enumerates every rectangle in this finite board by equal
midpoint and diagonal length. Every white presentation is distinct.
This verifies that retaining these triangles is compatible with full
identification, not only with the local axis test.
The exact output is
[filler_triangle_mechanisms_check.json](filler_triangle_mechanisms_check.json).

## 3. Reserving completion columns is not enough

Even when the completion column contains no double, two triangles can
demand opposite filler parts. In the parity family, put labels

    {3,4} at column 0, {5,6} at column 1, {1,2} at column 4.

The odd selected points (0,3),(1,5),(4,1) form a right triangle:
(1,2) dot (4,-2)=0. Its completion is (5,3). The even endpoints
give the translated triangle completing at (5,4).

If column five is a singleton, either filler parity creates an axis
rival for one triangle. Selecting row three or four instead makes one
rectangle hidden. If column five is a double, the first obstruction
in Section 1 applies. Thus these three assigned labels are immutable
in a completed parity equality board.

This example scales to any fixed horizontal grid step d: use the
labels {2d+1,2d+2}, {4d+1,4d+2}, {1,2} at columns 0,d,4d.
The two completion cells at column 5d have rows 2d+1 and 2d+2.
All rows fit once h>=4d+2.

There is a different obstruction even when all completion rows have
the same parity. The two rectangles with common corner W=(0,5) and
other corners

    (1,7),(4,3),(5,5),
    (2,9),(8,1),(10,5)

have perpendicular side vectors (1,2),(4,-2) and (2,4),(8,-4).
Their six other corners can be inserted using six distinct parity
labels, for example

    {7,2}, {3,2}, {5,2}, {9,2}, {1,2}, {5,4}

at the respective columns. They share the same completion W, so no
choice at column zero separates their presentations. The completion
uniqueness condition is independent of the filler-part condition.

## 4. A universal filler scheme needs superquadratic width

Here is a precise limitation that does not assume the parity partition.
Let h>=10, and let A,B be any balanced bipartition of the h rows.
Put Q=|A||B|=floor(h^2/4). Fix Q distinct double columns D in a
board of width m. Suppose that for every bijection from A times B to D,
some singleton filling makes the full board identifying.

Then, with

    K_h=floor((1+sqrt(8h-7))/2),

one has

    Q <= ceil(m/h) K_h,
    m >= h(Q/K_h-1)
      = (1/(4 sqrt(2))+o(1)) h^(5/2).           (1)

The assumption permits an adaptive filler choice after seeing all
labels. It requires the double columns to tolerate every label order.

### 4.1 Repeated short differences force a bad label assignment

Take any h consecutive columns. If two distinct positive pairs of D
have the same difference, their union has either three or four columns.

In the three-column case they are c,c+d,c+2d, with 2d<=h-1.
Prescribe inserted points at

    (c+d,1), (c,1+d), (c+2d,1+d).

Their completion W=(c+d,1+2d) is in the middle double column.
Let R={1,1+d,1+2d}. Each row part has at least five members. Choose
the root's opposite-part mate outside R, and choose two distinct
opposite-part mates outside R for the two occurrences of row 1+d.
These are three distinct labels, and W is white in the root's column.
The final complete pair family then supplies the axis rival from
Section 1. Remaining labels may be assigned arbitrarily.

In the four-column case write them as

    x, x+u, x+v, x+u+v,  0<u<v, u+v<=h-1.

Prescribe the four black points

    A=(x,1+v),          B=(x+u,1+u+v),
    C=(x+v,1),          D=(x+u+v,1+u).

They form a tilted rectangle with perpendicular sides (u,u),(v,-v).
Their four rows are distinct and lie in [1,h]. For each selected row,
choose its opposite-part mate outside these four rows. Such a mate
exists because each part has at least five rows. All four resulting
labels are distinct: each contains one selected row and one row
outside the selected set.

The failure has an explicit two-rectangle certificate, so it does not
depend on a general rule about hidden rectangles. Put

    P=(x,1+u), Q=(x+u+v,1+v).

The rectangles {A,D,P,Q} and {B,C,P,Q} have symmetric difference
{A,B,C,D}. The first is axis aligned and nondegenerate because u!=v.
The second has equal-length diagonals BC and PQ with the same midpoint.
All six cells lie in the board. The common cells P,Q are white under
the prescribed labels because their rows belong to the selected row
set, while the mates were chosen outside it. Later fillers cannot
alter these double-column cells.

Thus a universally completable column set has no repeated positive
difference inside any h-column interval.

### 4.2 Count the columns

If an h-column block contains k double columns, its binom(k,2)
positive differences lie in {1,...,h-1}. They must be distinct, so
binom(k,2)<=h-1 and k<=K_h. Partition the width into ceil(m/h)
blocks. Summing their populations proves (1).

This theorem rules out a filler-only repair of an arbitrary ordering
at quadratic width. It leaves open a correlated construction that
chooses label positions and fillers together. The valid board in
Section 2 demonstrates that such a construction need not exclude
every inserted right angle.

## 5. Consequence for the construction strategy

Filler freedom can remove the axis danger of an inserted triangle only
after three structural requirements have been met: its completion
column is not occupied by a double, its required row part is consistent
with all other completions there, and its completion cell is unique.
Those requirements already depend on the assigned labels and their
positions. A fixed dense set of columns cannot satisfy them uniformly
over every assignment.

The remaining constructive question is therefore specific: arrange
the labels in quadratic width so these completion demands are
consistent, then choose fillers that also avoid the newly created
four- and six-cell supports. No claim that this has been achieved is
made here.
