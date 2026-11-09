# A height-15 equality board at every width at least 441

9 November 2026. The completed spacing-eight board proves
\[
f(15,m)=m+56\qquad(m\ge441).
\]
The finite witnesses are computer-assisted. The extension to every larger
width follows from the locality proof below. No claim is made that 441 is the
minimum equality width.

## The finite completion

Place all 56 opposite-parity row pairs at columns \(8j+1\), \(0\le j<56\).
The pinned empty scaffold is in spacing8_h15_seed17_empty.json.
The exact odd-sea fiber formulation supplies one odd black row in each of its
385 remaining columns. The resulting board has width 441 and 497 black points.

The complete column list is in
pinned_fiber_spacing8_h15_seed17_empty_odd_cadical195.json.
The companion height15_width441_coordinates.json gives every black coordinate,
with both coordinates starting at one. The solver used 1,383,345 variables and
5,121,617 clauses. Compilation and solving took 62.11 seconds.

An independent verifier completes each pair of black points both as a side and
as a diagonal. It enumerates every rectangle with at least two black corners.
It found 398,247 rectangles and 398,247 distinct white presentations. Every
other rectangle has at least three white corners, which already determine it
uniquely. The standalone result and input hash are in the matching
_pair_check.json file. This verifier does not reuse the SAT fiber construction.

The two earlier 300-second lazy filling runs ended unknown. They are not used
as impossibility certificates.

## An explicit transition to a constant tail

Appending a constant row immediately fails for every row, on either end.
The exact transition search instead appends the following 40 singleton rows:

    15,15,15,1,15,1,13,1,3,1,15,1,15,11,3,1,13,1,11,1,
    3,9,9,1,1,13,15,15,7,1,1,13,1,1,15,1,9,1,1,11

It then appends 100 copies of row 2. The full width-581 board has 637 black
points. Independent pair completion finds 610,529 weak rectangles and distinct
presentations. The full columns and verification counts are in
pinned_fiber_spacing8_h15_seed17_empty_odd_cadical195_tail.json.
The local SAT certificate is
pinned_fiber_tail_frame_h15_gap40_row2_odd_cadical195.json.

Only the last 100 columns of the original board were variable-context input
to that local search. They were fixed, not recolored. The transition columns
were free odd rows, and the final 100 columns were fixed in row 2. The search
retained the final complete parity graph for remote axis rivals. The full
width-581 verification establishes the final board directly, independently
of the local-context reduction.

## Why the finite certificate extends indefinitely

Every tilted rectangle in 15 rows has horizontal span at most 50. Indeed,
write its adjacent sides from the leftmost corner as \((a,-b),(c,d)\), with
positive integer components. Then
\[
a+c\le ac+1=bd+1\le\frac{(b+d)^2}{4}+1\le50.
\]
Two tilted rectangles with a common corner have union span at most 100.
A collision of two rectangles has zero, one, or two common corners. Hidden
rectangles are already excluded; the remaining tilted-tilted comparisons
have a common corner and hence this bound.

Axis-axis presentations remain distinct because the full double graph is the
simple parity graph and all added columns are singletons. A tilted-axis
collision is tested locally against the unchanged full parity pair set:
singleton and vertical presentations use that final pair set, while horizontal
and oblique presentations use black points in the tilted rectangle's columns.
Thus no new long-distance axis effect appears when the tail is extended.

Beyond the checked width 581, any new local failure that touches the prefix
through column 481 would have span at least 101. This exceeds the bound.
All remaining new local supports lie entirely in the constant row-2 sea.
That sea is valid for the parity graph. It has no three-black tilted rectangle.
Its vertical alternative diagonals have even row difference, so no parity
axis rival exists. Other two-white comparisons either force a hidden rectangle
or are degenerate.

Consequently any further row-2 tail is valid. Prefixes of the checked board
give every width from 441 through 581, because deleting columns cannot create
a presentation collision among rectangles that remain. Every such prefix
retains all 56 double columns, so it has \(m+56\) black points. The axis upper
bound gives equality.

## Scope of the spacing choice

The result is a finite, fixed-spacing completion. The general odd-spacing
scaffold theorem uses \(D>(h-1)/2\) and supplies only empty-sea scaffolds of
width \(O(h^3)\). It does not prove that fixed spacing eight works at all
heights, nor that the present filling pattern generalizes to a quadratic
construction.
