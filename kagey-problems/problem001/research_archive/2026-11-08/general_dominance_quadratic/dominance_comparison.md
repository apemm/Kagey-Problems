# Structural comparisons for general sea dominance

8 November 2026. These results identify additional words that belong to the boundary component
and quantify a loss suffered by every nonparity balanced partition. They do not prove dominance
at arbitrary height.

Let W=1+floor((h-1)^2/4), and use memory L=2W for the full-history sea graph. For any row
partition pi, let C_boundary,pi be its primitive component containing the constant boundary
states. For parity this is C_*, which contains all constant-row states.

## 1. A constant boundary run of length W identifies the component

**Boundary flattening lemma.** Suppose a bi-infinite valid sea contains W consecutive copies of
row 1. Replacing everything strictly before that run by row 1 preserves validity. Replacing
everything strictly after the run by row 1 also preserves validity. The same statements hold
for row h and for every row partition.

Proof. A tilted rectangle has horizontal span at most W and at most one corner in row 1.
After flattening the past, a weak tilted rectangle touching a changed column would need a
non-row-1 black corner beyond the entire run. Its span would exceed W. Therefore no weak
rectangle touches a changed column. Every remaining weak tilted rectangle has unchanged
corners and unchanged black rows in its white-corner columns. Its presentation and its
axis-rival test are consequently unchanged. No tilted collision or new axis rival is created.
The future version follows by horizontal reflection, and row h by vertical reflection.

**Component consequence.** A recurrent component containing a word 1^W or h^W is
C_boundary,pi. Close a path containing that run to a periodic path in the component.
Flattening its past gives a path from the boundary constant state into the component;
flattening its future gives a path back. Thus the components coincide.

This improves the tautological run length 2W to W. It is a sufficient reset criterion, not a
proof that every recurrent component contains such a run.

## 2. Every valid monotone word has an immediate boundary extension

**Monotone classification.** Suppose the sea rows are nondecreasing with the column. Its only
possible violations are vertical presentations with an axis rival. Explicitly, black points
(x,a),(z,b), with x<z and a<=b, can cause a violation precisely when

    D^2=(z-x)^2+(b-a)^2,
    x+z is even,
    r_-=(a+b-D)/2 and r_+=(a+b+D)/2 are integral rows in [1,h],
    {r_-,r_+} belongs to F_pi.

The vertical white diagonal is at column (x+z)/2. Both of its cells are white: D>b-a, so its
rows lie strictly outside [a,b], whereas the black row in the midpoint column lies in [a,b].

Here is the exclusion of all other mechanisms.

* Three black points cannot form a right angle. At an extreme-column vertex both horizontal
  leg components have the same sign and the vertical components have compatible signs, so
  their dot product is positive. At the middle-column vertex the horizontal product is
  negative and the vertical product is nonpositive, so their dot product is negative.
  This excludes hidden rectangles and singleton presentations.
* For a horizontal white diagonal, the two black diagonal rows must satisfy a<b. The white
  columns lie strictly outside the black columns. Monotonicity therefore makes their black
  rows different, so there is no horizontal axis rival.
* An oblique white side has a parallel complementary black side. Its crossed rival pair would
  have the opposite slope, impossible for a monotone black graph. If the oblique white pair
  is a diagonal, its black diagonal and the crossed black diagonal form a hidden rectangle,
  already excluded.
* Two tilted rectangles sharing their white pair as two sides or two diagonals similarly
  produce a hidden black rectangle. In the remaining mixed case, let U=B-A be the black side
  vector and V=D-C the black diagonal vector, oriented with positive horizontal components.
  Then U has both coordinates positive, V has nonnegative coordinates, and |U|=|V|.
  The midpoint difference is perpendicular to U. Hence the projections of C,D onto U lie
  between those of A,B, by Cauchy--Schwarz. Since the four black points form a coordinatewise
  chain, this forces A<=C<=D<=B coordinatewise. Thus V<=U. Equal norms force V=U and then
  C=A,D=B, contradicting distinctness of the rectangles.

These arguments prove the classification for every partition, rather than only parity.

**Monotone bridge theorem.** If a finite nondecreasing sea word w is valid, then

    1^infinity w h^infinity

is valid for the same partition. If w is nonincreasing, use h on the left and 1 on the right.

Proof. The extended word remains monotone. Every new black pair has a boundary-row endpoint.
For an endpoint in row 1, a prospective vertical white diagonal has lower row
(1+b-D)/2<1 because D>b-1. For an endpoint in row h, its upper white row exceeds h.
Thus no new vertical exposure fits in the strip. The classification excludes every other
violation. A vertical exposure using two old black points has its midpoint column inside w,
so finite validity of w already excludes it.

In particular, every valid monotone full-window state lies in C_boundary,pi: the displayed
extension connects it to the two boundary constants. This gives a bridge without adding a
long constant collar to the word itself.

## 3. A short monotone factor is not a reset word

The monotone bridge theorem applies to the entire word being extended. A monotone factor
inside an arbitrary word is insufficient, even when it traverses every row.

At h=14, exhaustive geometric checking verifies that

    w=(1,2,3,4,5,6,7,8,9,10,11,12,13,14,2,14,2,14,6)

is a valid finite parity sea. However, 1^3 w is invalid. In the padded word, the black pairs

    A=(1,1), B=(21,6),
    C=(2,1), D=(18,14)

give a mixed collision with common white cells

    P=(0,5), Q=(20,10).

Indeed, |B-A|^2=20^2+5^2=425=16^2+13^2=|D-C|^2, and
(A+B-C-D) dot (B-A)=(2,-8) dot (20,5)=0. The two rectangles have exactly the
same white presentation {P,Q}. The initial staircase in w has length h, so a complete
height-spanning staircase does not justify flattening the preceding context.

The finite validity assertion is computationally checked; the displayed collision is an
explicit arithmetic certificate of failure after padding. The example does not exhibit a
different recurrent component.

## 4. Every nonparity balanced partition loses about half the fixed points

Recall the exact constant-sea criterion: row r is allowed as a constant sea if and only if
every symmetric pair {r-d,r+d} inside the strip is monochromatic under pi. Thus the forbidden
constant rows are exactly the midpoints of same-parity row pairs separated by pi.

Write the odd rows as 2i+1. If their indices split into nonempty sets S,T under pi, their
cross-pair midpoints form S+T+1. The elementary integer sumset inequality

    |S+T| >= |S|+|T|-1

follows by listing the strictly increasing sums obtained by first increasing the element of S
and then the element of T. The even-row version gives S+T+2.

**Odd height.** At h=2k+1, every nonparity balanced partition admits at most k+1 constant-row
seas. This bound is sharp. The k+1 odd rows must split: if they were monochromatic, they would
fill the larger block and force the parity partition. Their cross-pair midpoint set has at
least k elements. Hence at least k of the h constant seas are forbidden.

To attain equality, put all k even rows and one odd row in the larger block, with the other
k odd rows in the smaller block. There are exactly k separated same-parity pairs, with
distinct midpoints. Precisely k+1 constant seas remain.

**Even height.** At h=2k, every nonparity balanced partition admits at most k+1 constant-row
seas. Both parity classes split, and either one supplies at least k-1 forbidden midpoints.
For odd k this bound is sharp: partition the first k rows from the last k rows. Both midpoint
sets are the same interval of length k-1. No sharpness claim is needed here for even k.

There is also an exact count of the extra two-letter prohibitions. Every separated same-parity
pair {a,b} gives the forbidden pattern

    w_j=w_{j+b-a}=(a+b)/2.

Distinct row pairs give distinct patterns. Each is absent from the parity shift's restrictions,
as witnessed by the corresponding valid parity constant word. If h=2k and a balanced block has
t even rows, their number is 2t(k-t), hence at least h-2 for every nonparity partition. If
h=2k+1 and the larger block has t even rows, their number is t(h-2t), hence at least k when
the partition is nonparity.

These are distinct prohibitions, not probabilistically independent events. Their number and
the loss of fixed points alone do not establish a spectral comparison.

## 5. What the reset criterion gives as an entropy bound

A parity component outside C_* must avoid both 1^W and h^W. Ignoring every other constraint
gives an explicit upper bound lambda(h,W), the entropy of the full h-letter shift with just
those two runs forbidden. For h>=3, its Perron root is the largest root greater than one of

    (h-lambda) lambda^W = lambda+h-2.

For example, this follows by distinguishing the h-2 ordinary letters and the run lengths
1,...,W-1 of each boundary letter. The geometric sum of weights for one boundary run is
sum_{j=1}^{W-1}lambda^{-j}; eliminating the two symmetric run-state weights gives the equation.

The bound is strict below h, but asymptotically

    h-lambda(h,W) ~ 2(h-1) h^{-W}.

It therefore lies far above the proved polynomial lower bound for rho_*. This route does not
prove dominance. The monotone bridge theorem supplies more forbidden windows for an external
component, but no quantitative argument currently forces enough such windows to close the gap.

There is a concrete limitation to using only these two bridge criteria. Split the row alphabet
into a lower band of floor(h/2) rows and an upper band of ceil(h/2) rows, and alternate the bands
at successive columns. This abstract symbolic family has entropy

    sqrt(floor(h/2) ceil(h/2)) ~ h/2.

Every three-column factor has a strict peak or valley. Hence it contains no monotone factor of
length three, and no constant run of length two. It satisfies both of the necessary avoidance
conditions for an external component while retaining linear alphabet entropy. This family is
not asserted to be a valid sea. It proves that those avoidance conditions alone cannot supply
the desired comparison with the currently proved lower bound for rho_*. The missing step must
use additional rectangle constraints, rather than only the absence of reset factors.

## 6. Status

The proved advances are the boundary flattening criterion, the full monotone classification and
bridge, and the fixed-point/diamond-defect bounds for arbitrary balanced partitions. The short
staircase counterexample blocks a tempting stronger reset claim. General dominance remains open:
neither strict parity dominance over every partition nor maximality of C_* among all parity
components has been proved at arbitrary height.

`check_dominance_comparison.py` independently checks the monotone classification and boundary
extensions, the finite staircase counterexample, and the fixed-point bounds on small heights.
