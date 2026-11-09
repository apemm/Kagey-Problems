# The first triple-column boundary at every height

9 November 2026. Let q=floor(h²/4), r=floor(h/2), and w=q−r. For h>=7, the seven-row triple-column classification extends to the exact intrinsic excess q−r+1 at every height. It also determines two more widths in the axis-only extremal problem:

    f_ax(h,w−1)=2(w−1)+1,
    f_ax(h,w−2)=2(w−2)+2.

These are axis-only values. They give upper bounds for the full geometric problem, but the constructions below are not asserted to distinguish tilted rectangles. The square exponent remains unchanged.

## 1. Equality in the large-column bound

Let t be the number of nonempty columns and e=|S|−t. Assume the row-column incidence graph has no four- or six-cycle, and

    e=q−r+1=h−1+floor((h−3)²/4).

Suppose there is a column of size at least three. Then there is exactly one such column, and it has size three.

To prove this, recall the large-column inequality

    e<=h−1+floor((h−k)²/4)

for a column containing k rows. It first excludes k>=4. Let B be a triple column. Choose a star on B and a tree on every other nonempty column, giving the simple triangle-free row graph H with e edges. Every outside row has at most one neighbor in B. Equality therefore forces every outside row to have exactly one such neighbor, and forces H outside B to be a balanced complete bipartite graph K_(a,b), where a+b=h−3 and |a−b|<=1. Since h>=7, both parts have size at least two.

Suppose a second triple column C exists. It cannot meet B twice. If it meets B once, choose its tree as the star centered at that shared row. The other two rows u,v are nonadjacent in the outside graph, since their pair already occurs in C. They lie in the same part of K_(a,b). Any common neighbor x in the other part gives edges ux,vx from columns distinct from C and from each other. If those two owners were equal, that owner would repeat the pair uv. The three columns consequently form a forbidden six-cycle.

If C is disjoint from B, choose its tree as a path u−v−z. The endpoints u,z lie in one part of the outside complete bipartite graph, and v lies in the other. Choose another vertex x in v's part. The edges ux,zx again have distinct owners outside C, giving a six-cycle. Thus C cannot exist.

Every other nonsingleton column is therefore a double. The outside doubles are exactly the edges of K_(a,b). Every outside row has one attachment double to B. Attachments are a proper three-coloring of K_(a,b), with the three rows of B as colors: an outside edge with equally colored endpoints would form a six-cycle with their two attachment columns. Conversely, every such proper coloring gives an axis-valid column family. There are no repeated row pairs, no triangle among the double owners, and no six-cycle using the triple, because each outside row has only one attachment to B.

The number of doubles is h−3+ab=w−1. Thus every family in this classification has exactly w nonsingleton columns, before adding arbitrary singleton or empty columns.

## 2. Counting the classified nonsingleton patterns

Put n=h−3, a=floor(n/2), b=ceil(n/2), and

    beta_n=binom(n,a)/2 if a=b,
    beta_n=binom(n,a) otherwise.

The number of labeled nonsingleton column multisets in Section 1 is

    binom(h,3) * beta_n * 3(2^a+2^b−2).

The last factor is the number of proper three-colorings of K_(a,b). If its first part uses one color there are 3*2^b choices; if it uses exactly two colors there are 3(2^a−2) choices. This recovers 1890 patterns at h=7. It counts the classified axis-only multisets, not full geometric blackouts.

## 3. The two additional exact widths

At m=w−1, a set of at least 2m+2 points has intrinsic excess e>=m+2=w+1. Some column has at least three points. The large-column bound forces e=w+1, and Section 1 then requires at least w nonsingleton columns, impossible in width m. Hence f_ax<=2m+1. Delete one double column from any minimal w-column family in Section 1 to attain 2m+1.

At m=w−2, a set of at least 2m+3 points similarly has e>=m+3=w+1, so the same contradiction gives f_ax<=2m+2. The following two-triple family attains that value.

Choose B={b0,b1,b2}, split the other rows into balanced parts A,C, and choose u in A and v in C. Use the columns

    B, {b0,u,v},
    {b1,x} for x in A except u,
    {b2,y} for y in C except v,
    {x,y} for (x,y) in A×C except (u,v).

There are 2+(a−1)+(b−1)+(ab−1)=w−2 columns. Two are triples and all others are doubles, giving 2m+2 black points.

No row pair repeats. The double-column graph is bipartite. A six-cycle using only the first triple would require an outside row attached twice to B, which does not occur. A six-cycle using only the second triple would require a common double-neighbor of u,v, or a double-neighbor of b0; neither exists. A six-cycle using both triples would require a double between {b1,b2} and {u,v}; all four such doubles were omitted. Thus the family is axis-valid.

Together with the previous value f_ax(h,w)=2w+1, this determines three consecutive widths immediately below the range where f_ax(h,m)=2m. It strengthens a finite-width structural description, not the square asymptotic bound.

## 4. A staircase across a linear range of widths

There is a wider exact statement. Put n=h−3. If ell is a nonnegative integer and n>=12(ell+1), then

    f_ax(h,w−ell)
      =2(w−ell)+1+floor((sqrt(4ell+1)−1)/2).

The constant 12 is a convenient sufficient condition, not an optimized endpoint.

First prove a structural lemma. Suppose a triple column exists and the intrinsic excess is

    e=w+1−delta,  where delta>=0 and n>=12(delta+1).

Then all columns have size at most three, and their number T of triple columns satisfies

    (T−1)²<=delta.

A column of size at least four would force delta>=floor(n/2), by the large-column bound, so none exists. Fix a triple B and choose its star. Let u be the number of outside rows lacking a neighbor in B in the row-tree graph H. As before, every outside row has at most one such neighbor. The induced outside graph therefore has

    e_out=floor(n²/4)−delta+u,

with 0<=u<=delta. The nonbipartite triangle-free bound from square_finitewidth_progress.md forces this outside graph to be bipartite. Choose its parts A,C of sizes a,b. If mu=ab−e_out is the number of missing cross-edges, then

    mu<=delta,  floor(n²/4)−ab<=delta,
    min(a,b)>=n/2−delta−1>4delta.

The same argument works for any choice of trees in the remaining columns. If another triple avoids B, choose its tree as a two-edge path. Its endpoints lie in the same outside part. They have at least min(a,b)−mu common neighbors, including one other than the middle point of the path, which gives the forbidden six-cycle used in Section 1. Hence every other triple meets B once.

Choose all these triple trees to be stars centered in B. For a triple with outside rows x,y, those rows must lie in opposite parts: if they lay in the same part, a common outside neighbor would again give a six-cycle. Distinct such triples cannot share an outside row. If their centers in B agree, they would repeat a row pair; if their centers differ, the two triples together with B would give a six-cycle.

Color every attached outside row by its unique neighbor in B. At most u<=delta rows are uncolored. Let a_i,c_i be the numbers of rows of color i in the two outside parts. Every same-color cross-pair is a missing outside edge. If its attachments have the same owner triple, that pair already co-occurs in the triple; if their owners differ, an outside edge would close a six-cycle. Thus

    sum_(i=1)^3 a_i c_i<=mu<=delta.

At most one color can occur in both parts. Indeed, each such mixed color has a_i,c_i<=delta. If two colors are mixed and the third is not, one part has at most 2delta colored vertices and delta uncolored vertices. If all three are mixed, each part has at most 3delta colored vertices and delta uncolored vertices. Both conclusions contradict min(a,b)>4delta.

Every triple other than B uses a mixed color, and their outside row pairs are disjoint. They therefore all use the same mixed color, with a_i,c_i>=T−1. Its missing cross-pairs give delta>=a_i c_i>=(T−1)², proving the lemma.

For the upper bound, let

    k=floor((sqrt(4ell+1)−1)/2),  G=k+1,

so k(k+1)<=ell<(k+1)(k+2). Suppose a width m=w−ell family has at least 2m+G+1 points. Some column has at least three points, and the large-column bound gives e<=w+1. With delta=w+1−e, intrinsic excess gives 0<=delta<=ell−G. The structural lemma applies. Since all columns have size at most three, the excess over 2m is at most T, so T>=G+1. Consequently delta>=G² and ell>=G²+G, contradicting ell<(k+1)(k+2)=G²+G.

For the matching construction, start with B={b0,b1,b2} and balanced outside parts A,C. Choose disjoint lists u_1,...,u_k in A and v_1,...,v_k in C. Use B and the k triples {b0,u_i,v_i}. Attach each remaining row of A to b1 and each remaining row of C to b2. Use every outside double from A×C except the complete k-by-k product {u_i}×{v_i}.

This gives w−k(k+1) columns and k+1 triples; all other columns are doubles. Its double graph is bipartite. Six-cycles involving one triple are excluded as in Section 3. Two additional triples share b0, and the outside edge that could close a six-cycle lies in the deleted k-by-k product. A six-cycle involving B and another triple would require an omitted attachment to a selected row. Three triples cannot form a six-cycle because they share only the same row b0. No pair repeats. Hence the family is axis-valid.

Delete ell−k(k+1) double columns, retaining the k+1 triples. The number deleted is at most 2k+1, and there are more than that many doubles under n>=12(ell+1). The resulting width is w−ell and its size is exactly 2(w−ell)+k+1, proving the formula.

This staircase begins with gains 1,1,2,2,2,2,3,... above twice the width. It concerns widths of order h² and therefore does not improve the square-board exponent.

[verify_axis_borderline_staircase.py](verify_axis_borderline_staircase.py) independently checks the row-pair owners in 21 explicit constructions at heights 15 through 75. It verifies the absence of axis four- and six-cycles and the width and size formulas. The general upper bound and its equality range follow from the proof above, not from these finite checks.

## 5. Exact axis-only multiplicity at width w−2

For h>=9, every axis-optimal family at width m=w−2 is the two-triple construction in Section 3. Consequently its number of ordered axis-valid optimal blackouts is

    3 * binom(h,3) * beta_(h−3) * a*b * m!,

where a,b and beta are defined in Section 2. These are labeled row and column positions; no reflection quotient is taken.

Here is the equality classification. The optimum has 2m+2 points. If z columns are empty, its intrinsic excess is e=w+z. The large-column bound gives z<=1. The case z=1 would be the single-triple boundary of Section 1, requiring w nonsingleton columns in width w−2. Hence z=0 and e=w, so the deficit from that boundary is delta=1. Columns of size at least four are excluded by the large-column inequality. If T is the number of triples and s the number of singletons, the size identity gives s=T−2, so T>=2.

Fix one triple B. The outside graph has e_out=floor(n²/4)−1+u, with u in {0,1}. For n=h−3>=6, the nonbipartite triangle-free bound forces it to be bipartite. Its imbalance loss and number mu of missing cross-edges sum to 1−u. Both parts have size at least two. If mu=1, both parts are balanced and have size at least three; if mu=0, no common neighbor is lost. In either case, the alternate-neighbor argument excludes a triple disjoint from B and forces each other triple to use one row from each outside part.

Each such additional triple supplies a distinct missing cross-edge. Since T>=2, necessarily mu=1, u=0, there is no imbalance loss, and T=2. Thus s=0 as well. The unique missing edge joins the two outside rows of the second triple, whose shared center with B is b0. Every outside row has an attachment to B. Only the two selected rows can use color b0, since any further such row would force another missing cross-edge. The other two attachment colors must be constant and opposite on the two remaining outside parts. This is exactly Section 3's construction.

To count its multisets, first distinguish one of the two triples as B. Choose B in binom(h,3) ways, its shared center in three ways, the balanced outside partition in beta_n ways, and the missing edge in ab ways. The two other rows of B can be assigned to the two outside parts in two ways. Every resulting multiset has exactly two choices of distinguished triple, cancelling this factor two. All m column sets are distinct, so multiplying by m! counts their orders.

The restriction h>=9 is substantive for this classification. At heights seven and eight, disjoint-triple alternatives can occur at the same axis-only optimum. The exact extremal values from Section 3 still hold there, but the multiplicity formula above is not asserted for those heights.
