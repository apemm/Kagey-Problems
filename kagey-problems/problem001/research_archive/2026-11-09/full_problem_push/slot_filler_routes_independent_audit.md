# Audit of the list-palette and filler routes

9 November 2026. The following checks concern the new construction
lemmas, not a completed quadratic-width construction.

## 1. Arbitrary lists for the P palette

[global_P_linear_list_coloring.md](global_P_linear_list_coloring.md)
passes review. In a large offset band, restricting a color to the
vertices whose original lists contain it decreases every clique
color-degree. It does not affect the individual binomial lower bound,
because colors are sampled independently. The dependency graph for
the eligible vertices of one clique retains its subpolynomial degree.
The same list-coloring local lemma therefore applies.

The routing step removes a possible hidden common-palette assumption.
After trimming all original lists, there are only O(h^3) color names.
Each name is assigned to one band independently. A band's routing
weight is proportional to its required list size, and the sum of the
weights is O(h). The small-band bucket receives an additional
64 log h minimum weight, ensuring simultaneous concentration even
when its degeneracy is bounded. Greedy list coloring of that bucket
and separate large-band colorings use disjoint names.

The exclusion of level slope -1 is necessary for this proof: an
offset no longer determines a unique vertex on that level. It is
stated in the theorem. The theorem proves choice number O(h), not
right-angle exclusion.

## 2. Completion compatibility

[filler_safe_inserted_triangles.md](filler_safe_inserted_triangles.md)
has the correct exact local criterion. At a singleton completion
column, a filler in the opposite row part creates an axis singleton
rival, while filling the completion cell creates a hidden rectangle.
A different row in the same part excludes that axis rival. Two
inserted triangles with the same completion cell remain
indistinguishable for every filler.

Therefore completion rows at one column must lie in one part, leave
an unused row of that part, and occur without multiplicity at a cell.
No completion may lie in a double column. These conditions are
sufficient only for the specified hidden, axis-singleton, and
duplicate-completion tests. They do not exclude other four- and
six-cell supports or collisions introduced by the chosen fillers.

## 3. Universal label-order obstruction

The Omega(h^(5/2)) lower bound in the same note is valid under its
universal-order premise. It allows the filler to depend on the order,
but requires the fixed double-column set to tolerate every bijection
of the complete balanced pair family.

Two distinct equal positive differences in an h-column interval
produce either a three-term progression or four columns
x,x+u,x+v,x+u+v with 0<u<v and u+v<=h-1.

In the progression case, the prescribed triangle completes in the
middle double column. Each row part has at least five members, so the
chosen mates can avoid the three designated rows and keep the three
labels distinct. The completion remains white and has a separate
axis owner.

In the four-column case, the prescribed selected rows are
1,1+u,1+v,1+u+v. Choosing each mate outside this four-row set makes
all labels distinct. The claimed two rectangles have the same
midpoint and diagonal length:

    BC: (v-u,-u-v),    PQ: (u+v,v-u).

Their common cells are white, and their symmetric difference consists
of the four inserted selected points. The first rectangle is axis
aligned and the second is nondegenerate and tilted.

Consequently every h-column interval has distinct positive pair
differences and at most

    floor((1+sqrt(8h-7))/2)

double columns. Summing over consecutive intervals gives the stated
width lower bound. This is not a lower bound on the optimal
identifying-board threshold, because that problem chooses the label
order together with the filler.

## 4. Geometric slot filtering

The separate
[independent audit](linear_slot_filter_independent_audit.md)
checks the root argument in
[linear_slot_filter_obstruction.md](linear_slot_filter_obstruction.md).
It rules out fixed linear-size admissible lists that automatically
eliminate right angles in the one-prime block coordinates, even after
P and finitely many level rules. It does not rule out an adaptive
coloring that uses the surviving geometric constraints.
