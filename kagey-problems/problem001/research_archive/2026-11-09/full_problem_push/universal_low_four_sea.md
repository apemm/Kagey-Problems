# A fixed periodic sea valid at every height

9 November 2026. For every \(h\ge4\), the period-four sea
\[
4,1,2,1,4,1,2,1,\ldots
\tag{1}
\]
is identifying, including its singleton and vertical rivals against the
complete parity graph on all \(h\) rows. The statement holds on the infinite
horizontal strip and therefore for every finite restriction.

It does not permit arbitrary parity doubles to replace the row-four points.
Many isolated substitutions already fail; a concrete example is given below.

## Three-black rectangles

Call the points on row four the high points. There are no three-black tilted
rectangles supported only on rows one and two. A rectangle with one high
point at \((4j,4)\) must use one point on each low row. The only possibilities
are the two horizontal reflections of
\[
\{(4j,4),(4j+1,1),(4j+2,2)\},
\]
whose completion is \((4j-1,3)\). Each odd completion column selects exactly
one of the two orientations modulo four, so the rectangle is unique.

A rectangle with two high points and one row-one point is impossible modulo
four: the product of its horizontal legs is one modulo four, whereas the
required product is \(-3^2=3\pmod4\). With a row-two point, the right angle
must be at that low point. Its horizontal product is \(-2^2=-4\), forcing
the unique diamond
\[
\{(4j,4),(4j+4,4),(4j+2,2)\}
\]
with completion \((4j+2,6)\). This completion is present only when \(h\ge6\),
and determines its rectangle uniquely. Three high points are collinear.

The row-three completions are above retained row-one points. The row-six
completions are above retained row-two points. In each case the two rows
have the same parity, so there is no singleton axis rival. The two types
have different completion rows and cannot collide with one another.

## Two-white presentations

There is no hidden rectangle. With two high and two low points, two low
points on different rows give odd total row sum. Two low points on the same
row cannot form opposite sides with the high pair because their column
classes differ, and cannot form diagonals because their center rows differ.
Three high points are collinear. The remaining cases reduce to the low-two
background and one-even-central analysis in `low_two_sea_exact_exceptions.md`.

Same-side and same-diagonal two-white collisions therefore cannot occur.
Consider a mixed collision, and count its row-four black points.

* Zero or one high point is excluded by the low-two background and the
  one-even-central mixed argument.
* With two high points, the low points must lie on the same row, by row-sum
  parity. In a cross pairing the two pair centers have the same row. Their
  connector is horizontal, and the side has nonzero horizontal component,
  so orthogonality forces a zero connector and degeneracy. Pairing the two
  horizontal high points against the two horizontal low points is also
  degenerate, since the common white pair would equal the black diagonal.
* Three high points and one row-one point give odd total row sum. With a
  row-two point, the high-to-low pair has squared length eight modulo
  sixteen, while the pair of high points has squared length zero modulo
  sixteen. Their lengths cannot agree.
* Four high points are collinear.

All black points in (1) have \(x+y\) even. A vertical white pair of opposite
row parity is therefore impossible by the rectangle checkerboard identity.
Horizontal and oblique axis rivals are included in the same mixed-case
analysis. Together with the singleton classification, this proves the claim.

## Computational checks and the substitution limitation

`verify_periodic_low_four_sea.py` generates tilted rectangles from black
pairs and compares their presentations modulo period-four translation.
Every height from four through one hundred passes. The pair span bound and
the surrounding margins ensure that this is an exact infinite-periodic
check, not a test of a short periodic sample.

However, replacing a row-four point by an arbitrary parity edge is unsafe.
At height ten, place a double containing row ten at column zero. The black
side
\[
\{(-4,4),(5,1)\}
\]
and black diagonal
\[
\{(0,10),(3,1)\}
\]
have squared length ninety. Their shared white pair is
\(\{(-3,7),(6,4)\}\). Both points are white in the periodic background,
independently of the odd partner of row ten. Thus every such isolated edge
fails at height at least ten.

`verify_low_four_sea_substitutions.py` checks all isolated parity edges at
heights four through twenty and saves explicit failures. At height twenty,
66 of the 100 edges fail. The universal sea is consequently useful as a
background or transition candidate, but it does not eliminate the local
insertion problem.
