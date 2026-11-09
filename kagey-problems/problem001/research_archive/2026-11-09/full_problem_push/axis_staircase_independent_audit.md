# Independent audit of the axis staircase

9 November 2026. The proof in
[axis_borderline_single_triple.md](axis_borderline_single_triple.md),
including its linear-range staircase, passes this independent review.
The conclusion concerns axis rectangles only.

The intrinsic excess uses the number of nonempty columns. If there are
T triples, S singletons and E empty columns, then the excess over twice
the full width is T-S-2E. Thus the upper-bound argument does not silently
assume every column is occupied.

At intrinsic deficit delta, a column of size four would already cost
floor((h-3)/2), which the stated range excludes. For a distinguished
triple B, the outside triangle-free graph has at least its Mantel bound
minus delta edges. The cited nonbipartite bound makes it bipartite in
this range. Its two parts have more than 4 delta vertices and at most
delta missing cross-edges.

The alternate-common-neighbor argument excludes triples disjoint from B.
Every remaining triple uses one vertex in each outside part, and different
triples have disjoint outside pairs. A shared outside row would either
repeat a row pair or create a six-cycle with B. Coloring outside vertices
by their attachment to B gives

    sum_i a_i c_i <= delta.

The part-size bound permits at most one color on both parts. Hence T-1
extra triples force (T-1)^2 missing cross-pairs. This proves the stated
structural inequality. The width calculation then gives the exact
staircase, and deleting extra double columns preserves axis validity.

The matching construction has w-k(k+1) columns and k+1 triples. Its
deleted k-by-k cross-product removes every possible six-cycle involving
two added triples. The stated height condition also leaves enough doubles
for the final deletions.

There is a further equality case at h>=9 and width w-2. Any optimum has
exactly two triples and no singleton or empty columns. The outside graph
is balanced complete bipartite with one edge deleted. All outside vertices
are attached to B, and the endpoints of the missing edge form the second
triple with one row of B. This is precisely the construction in Section 3.
The multiset count is

    3 binom(h,3) beta_(h-3) floor((h-3)/2) ceil((h-3)/2).

Choosing which remaining row of B attaches to each part contributes two;
choosing which of the two triples is distinguished also contributes two,
so these factors cancel. The smaller heights 7 and 8 are excluded from
this equality classification because disjoint-triple configurations can
then occur.

No tilted-validity or square-exponent conclusion follows from this audit.
