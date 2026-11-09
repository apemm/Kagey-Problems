# Exact axis-only multiplicities at the staircase jumps

9 November 2026. This note determines every optimal column family at the jump widths in the axis-only staircase. It does not assert tilted-rectangle validity.

Let

    q=floor(h²/4), r=floor(h/2), w=q−r,
    ell=k(k+1), m=w−ell,

where k≥1 and h−3≥12(ell+1). The staircase theorem in [axis_borderline_single_triple.md](axis_borderline_single_triple.md), Section 4, gives

    f_ax(h,m)=2m+k+1.

Every optimal family has the following form. Choose a row c, partition the other h−1 rows into balanced unordered parts X,Y, choose k+1 special rows in each part, and match the two special sets bijectively. For every matched pair x,y use the triple column {c,x,y}. Use every double column {x,y} with x in X and y in Y except those in the complete product of the two special sets. There are no singleton or empty columns.

Put

    A=floor((h−1)/2), B=ceil((h−1)/2), t=k+1,
    beta_N=binom(N,floor(N/2))/2 if N is even,
    beta_N=binom(N,floor(N/2)) otherwise.

The number of optimal labeled column multisets is exactly

    M(h,k)=h beta_(h−1) binom(A,t) binom(B,t) t!.

All column sets are distinct. The number of ordered axis-optimal blackouts is therefore M(h,k)m!. Equivalently,

    M(h,k)=h! / [2^(1_{h odd}) t! (A−t)! (B−t)!].

Rows and columns remain labeled; no horizontal or vertical reflection quotient is taken. The factor two when h is odd only makes the equal-sized bipartition unordered.

## 1. Equality excludes empty and singleton columns

Let an optimum have z empty columns, s singleton columns and T triple columns. Some column has at least three points because its size exceeds 2m. Its intrinsic excess, the number of points minus the number of nonempty columns, is

    e=(2m+k+1)−(m−z)=w+1−k²+z.

Thus its deficit from the single-triple boundary is delta=k²−z. The large-column bound gives delta≥0, and the structural lemma from the staircase theorem applies because h−3≥12(ell+1)≥12(delta+1). It excludes columns of size at least four and gives

    (T−1)²≤delta.

The size identity is

    T−s−2z=k+1.

Consequently T−1≥k+2z, whereas (T−1)²≤k²−z. Since k≥1 and z≥0, these inequalities force z=0 and T=k+1. The size identity then forces s=0, and delta=k².

## 2. Equality forces the complete deleted product

Fix one triple B0. Write n=h−3 and choose the row-tree graph as in the structural lemma, with every other triple represented by its star at its common row with B0. The lemma shows that every other triple meets B0 exactly once, uses one row from each of the outside bipartition parts, and has outside rows disjoint from those of every other triple.

Let the outside part sizes be a,b. Let u count outside rows with no attachment to B0, and let mu count missing cross-edges of the outside row-tree graph. The exact deficit identity is

    delta=[floor(n²/4)−ab]+mu+u.

Color each attached outside row by its unique neighbor in B0. At most one of the three colors occurs in both parts. All k additional triples use that mixed color, and their disjoint outside pairs force its sizes a0,c0 to satisfy a0,c0≥k. Every same-color cross-pair is a missing outside edge. Hence

    k²=delta≥mu≥a0 c0≥k².

Equality holds throughout. In particular, u=0, the outside partition is balanced, a0=c0=k, and its only missing cross-edges are the entire k-by-k product of the mixed-color sets. The k triples match these two sets perfectly and share the mixed-color row c in B0.

Each outside part still has unselected rows, because its size is much larger than k under the height hypothesis. The other two colors cannot be mixed. Since every outside row is attached, one remaining color fills the unselected rows of the first part and the other fills those of the second part. This is exactly the jump construction in the staircase theorem, with no additional choices or omitted doubles.

Write B0={c,b1,b2}, with b1 attached to the first outside part and b2 to the second. Moving b2 into the first part and b1 into the second gives the global bipartition X,Y above. Its special sets consist of the k mixed-color outside rows on each side together with b2 and b1, respectively. The original triple B0 supplies the extra matched pair. Thus the construction has t=k+1 triples through c and precisely the stated double columns.

## 3. Validity and uniqueness of the description

Conversely, the global construction is axis-valid. No row pair repeats: the triples use disjoint matched pairs and distinct pairs involving c, while all pairs between special sets are absent from the double graph. Its double graph is bipartite. A six-cycle using exactly one triple would require a common double neighbor of its matched endpoints, which lie in opposite parts, or a double incident with c; neither is possible. A six-cycle using two triples would require a double between special vertices from distinct matched pairs, and every such cross-pair was removed. Three distinct triples cannot form a six-cycle because their pairwise intersections are all the same row c.

The number of columns is

    AB−t²+t=w−k(k+1)=m,

since AB=floor((h−1)²/4)=w. Their total size is 2m+t, as required.

The description is unique up to interchanging equal-sized parts. Since t≥2, the common center c is the unique intersection of the triple columns. The double graph on the remaining rows is connected: both parts have ordinary vertices, all ordinary cross-pairs are present, and each special vertex is adjacent to every ordinary vertex on the other side. Its unordered bipartition is therefore unique. The triple columns then recover the two special sets and their matching. This proves that the formula M(h,k) counts each multiset exactly once.

## 4. Comparison with the distinguished-triple count

With a=floor((h−3)/2) and b=ceil((h−3)/2), the same number is

    [6/(k+1)] binom(h,3) beta_(h−3)
        binom(a,k) binom(b,k) k!.

Here the factor six chooses the common center in the distinguished triple and assigns its other two rows to the outside parts. Every family has exactly k+1 choices of distinguished triple. Choosing another triple preserves balanced outside sizes: remove its two matched vertices from X,Y, leaving parts of sizes a,b. Thus division by k+1 is exact, not a symmetry assumption about the row labels.

The identity with the global-center formula follows by A=a+1, B=b+1 and cancellation of factorials. At k=1 it reduces to the previously established two-triple count 3 binom(h,3) beta_(h−3) ab. The case k=0 is deliberately excluded: a single triple does not identify a unique common center, and the boundary families allow the more general proper three-colorings counted in Section 2 of the earlier note.
