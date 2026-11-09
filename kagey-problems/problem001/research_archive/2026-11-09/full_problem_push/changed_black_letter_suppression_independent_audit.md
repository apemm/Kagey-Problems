# Independent audit of changed-letter restoration

9 November 2026. The theorem in
[continuation_changed_black_letter_suppression.md](continuation_changed_black_letter_suppression.md)
passes this independent audit. For one fixed matched quadratic phase,
restoring changed letters contributes at most

    C(r/h) exp[-c(1+log h)^(3/2)]

per permitted column to the exact logarithmic partition function,
uniformly for r<=h^(1/4). Arbitrary clusters are included. The result
uses the stated normalized support convention and does not condition
on an arbitrary exterior word.

## The local geometric family

The vectors U=(2ku,2 epsilon kv) and V=(4lv,-4 epsilon lu) are
perpendicular. With u>1000v and the stated scale ranges, the two free
black cells lie on one chosen horizontal side of the root. Their
maximum distance is O(hR), R=h^(1/8). Choosing the side with more
available room handles roots at finite ends once the interval has
length at least ChR.

All vertical displacements point toward the farther boundary and are
less than h/4. Adding U flips the adjusted quadratic color because
k is odd and u+v is odd. Adding V preserves it because both
coordinates are multiples of four. Thus the two free points belong to
the common alphabet, and the completion is of the wrong reference
color. Removing geometries with another row in E makes this a genuine
singleton rival for the final partition.

The retained primitive harmonic sum is of order log^2 R. The loss from
specified changed rows is smaller, uniformly in r<=h^(1/4). Removing
Pythagorean directions costs bounded harmonic weight and makes every
free pair have noninteger Euclidean length. This prevents a free pair
from coinciding with a base two-cell vertical-rival event.

## The three star tests

Each test has a distinct necessary role.

1. The free-cell star bounds compatible one-assignment overlaps. Its
   row sum follows from the divisor count in the side role and the
   circle count in the diagonal role.
2. The deletion star bounds the mean removed by other occupied
   columns. Summing it counts each root pair at most twice, with at
   most r candidate changed letters per column.
3. The duplicate-pair star bounds distinct occurrences with both free
   assignments equal. A fixed pair fixes V, and each changed row gives
   at most constantly many roots on its perpendicular line.

Their largest total weight is h^(3/8+o(1)), below h^(1/2). All positive
weights are at least an inverse fixed power of h, so only O(log h)
dyadic bins occur. The number of star centers is at most the number
of permitted columns times a fixed power of h.

The maximal vertex-disjoint hyperedge matching is valid even though
the original letters are categorical: the actual selected vertex set
contains at most one letter per column. Its remainder has every star
sum O(H), H=ceil(sqrt(1+log h)). The deleted hyperedges remove roots
from the comparison, not letters from the actual word.

Deletion of a bad occupied column costs O(H) total mean across the
remaining roots. To see this, multiply each free-cell conditional
incidence by that cell's common-alphabet probability and sum over its
row. This proves the essential O(H|B|) loss without a separation
assumption.

## Marking and exact count comparison

Marking each surviving pair occurrence independently at rate b/H makes
all three conditional overlap sums small. Duplicate pairs are kept as
distinct marked events, so conditioning on one occurrence leaves the
other markers independent. The duplicate-pair star is exactly what
controls that case.

The retained common-alphabet base has o(1) incident and extension sums.
There is no base event contained in the two assignments of a root
pair: the only possible two-cell type was excluded by the noninteger
length condition. Thus the conditional local-lemma lower bound applies
to every marked occurrence after the base and any earlier occurrences
have been avoided.

The base-restoration inequality compares exact partition functions.
Omitting base constraints that touch changed columns costs only
exp(O(delta_h |S|)), and fixing those columns divides the common
product-space size by their alphabet sizes. This yields the factor
(C/h)^|S| before the additional root penalty. There is no hidden
replacement by arbitrary boundary-conditioned probabilities.

Each overloaded hyperedge has size at least cH. Its summed activity
is bounded by h^(-b_j/3). The polynomial number of centers and bins
is absorbed into exp(-c H log h). Summing over all hyperedge
collections and all remaining good letters only overcounts the
maximal-matching descriptions. This proves the claimed exact ratio.
The factor r/h in the final statement is valid because r>=1, and
the extra factor h is absorbed by decreasing c.

Uniformity in fugacity on [0,1] gives the finite-volume mean bound by
convexity. The weighted variational principle then gives the same
frequency bound for any maximum-entropy measure of this fixed-phase
shift. These are averaged statements, not pointwise exterior bounds.

## The collar consequence

Restoring changed letters in polynomially many collar columns changes
each relevant logarithmic partition function by o(1). The common-
alphabet surface comparison therefore survives that restoration.

The separate bound for restoring old protected letters also has the
stated order. A useful justification of its uniform fixed-row crossing
count is height enlargement. Translate a fixed-row configuration in a
height-h strip vertically by multiples of four into a strip of height
2h. There are Theta(h) permitted translates. They preserve the
protected phase and the horizontal cut. The known global crossing
bound at height 2h therefore bounds the fixed-row crossing weight by
O(log^2 h). This avoids assuming that a uniform row bound follows
merely by dividing an average by h.

The scope remains one fixed phase and controlled collars. A genuine
wall changes the completion phase of crossing rectangles. Neither
the restoration theorem nor this audit supplies the constraint family
or pressure estimate for such a wall, or proves exact component
dominance.
