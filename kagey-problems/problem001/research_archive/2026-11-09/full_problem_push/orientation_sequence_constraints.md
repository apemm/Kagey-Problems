# One-double constraints on the gap orientation

9 November 2026. Complementing the repeated gap according to an orientation
sequence avoids the fixed-period-eight obstruction, but introduces exact
equality constraints on that sequence.

For \(h=3\bmod4\), put doubles at \(8j\). Let \(\sigma_j\in\{0,1\}\).
In gap \(j\), use the pattern
\[
(1,1,1,h,1,1,1)
\]
if \(\sigma_j=0\), and its row reflection if \(\sigma_j=1\).
All rows in this note are one-based.

## The equality constraints

Consider a central black point \((8j,r)\) and positive or negative nonzero
offsets \(p,q\) such that
\[
pq=(r-1)(h-r).
\]
Assume both offsets are sea columns and all four corners fit. If the two sea
points have different boundary colors, they form a three-black tilted rectangle
with completion
\[
(8j+p+q,h+1-r).
\]
Swapping the two boundary colors leaves the product equation unchanged.

If \(r\) is even, then \(p,q\) are odd. The completion has an even row, and
every column has an odd black point. If the completion is white, the full
parity graph supplies its axis rival. If it is black, the resulting hidden
rectangle is forbidden. The sea values at both odd
offsets are the uncomplemented orientation bits. Consequently the label
containing \(r\) requires
\[
\sigma_{j+\lfloor p/8\rfloor}
=\sigma_{j+\lfloor q/8\rfloor}.
\tag{1}
\]

If \(r\) is odd, this completion gives an axis rival or a hidden rectangle
exactly when it lies in another double column. This requires
\(p+q=0\bmod8\). Since \((r-1)(h-r)\) is divisible by eight and neither
offset is a double column, this forces \(p=q=4\bmod8\). Both sea colors
are then complemented orientation bits, so the same equality (1) applies.
In particular this case requires
\[
v_2((r-1)(h-r))=4.
\]

These statements classify the one-double three-black **axis-rival** constraints.
They do not classify tilted-tilted collisions or horizontal rivals. A white
odd-row completion in a sea column is outside this axis-rival class.

## Alternation and Thue–Morse both fail at height 39

At height 39, a double containing even row 4 has
\[
(r-1)(h-r)=3\cdot35=105.
\]
The factorizations \(105=7\cdot15=5\cdot21\) give
\[
\sigma_j=\sigma_{j+1},\qquad
\sigma_j=\sigma_{j+2}.
\]
The rectangles need right margin at most 26. Row 4 occurs in 20 doubles,
while at most \(\lceil26/8\rceil=4\) slots lack that margin. Thus a valid
board requires at least sixteen row-4 occurrences at the starts of constant
orientation triples.

Alternation has no constant triple. Neither does the Thue–Morse sequence:
in each aligned pair its values are opposite, and every three consecutive
positions contain such a pair. Both proposed orientation rules therefore
fail at height 39, independently of the double order.

The mixed obstruction provides an additional labeled condition. At height 39,
an occurrence of odd row 35 forbids
\[
(\sigma_{j+1},\sigma_{j+2})=(0,0),
\]
while odd row 5 forbids \((1,1)\), whenever its 21-column frame fits.
These follow from the common-white-pair certificate in
period_eight_binary_sea_impossibility.md and its row reflection.

Thus assigning long constant runs to different row classes remains possible
at the level of these necessary conditions. Arbitrary aperiodicity alone
does not resolve them.
