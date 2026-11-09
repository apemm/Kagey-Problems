# Arbitrary linear lists for the global P palette

9 November 2026. The global P graph has choice number O(h). The conclusion remains true after adding the level cliques b+ka=constant for any fixed finite set of integers k other than -1. Thus the palette theorem can use arbitrary prescribed slot lists of size C h, rather than a common palette. This addresses the list-coloring step only. It does not supply right-angle-free slot lists or a filled identifying board.

## 1. Statement and existing arithmetic inputs

Let G_h be the graph from [global_P_linear_coloring.md](global_P_linear_coloring.md). Its vertices are opposite-parity labels (a,b), with a odd and b even in [1,h]. Vertices with the same odd row form a clique. A vertex v=(a,b) conflicts with every vertex whose odd row is in

    B(v)={s odd, s != a : (s-b)^2+4(s-a)^2=L^2 for some 1<=L<=h-1}.

Take the undirected union of these conflicts. Fix a finite set K of integers not containing -1, and add the cliques b+ka=t for k in K. Write r=|K|.

There is a constant C_K such that every assignment of finite color lists A(v) with

    |A(v)| >= C_K h

admits a proper list coloring of this augmented graph. Color names can be arbitrary. In particular, if the lists are subsets of an integer interval [1,C' h], the coloring uses those actual slot numbers. No relabeling of physical slots is required.

The proof uses the arithmetic facts already proved in the two linked palette notes. For odd offsets u=a-b, let D(u) bound |B(a,b)| as in the original theorem. Then

    sum_u D(u)=O(h log h),    max_u D(u)=h^{o(1)}.

Within any original or added clique, a fixed odd row belongs to the blocker sets of only h^{o(1)} vertices. This is the completed-square calculation in [global_P_linear_levels.md](global_P_linear_levels.md), Section 1. Every clique meets a set of N offsets in at most N vertices. For an added level, this uses k != -1.

## 2. A band accepts arbitrary lists

Consider N offsets satisfying D(u)<=2R log h, where R>=1 and N>=h^{1/3}. Give each vertex in this band an arbitrary list of

    K_b=ceil(8192(r+1) R N)

candidate colors. Trim larger lists first. Their union has at most h^2 K_b colors, which is polynomial in h because R=h^{o(1)}.

For every color in this union, independently choose a set S of odd rows, including each row with probability p=1/(64R). Independently for every vertex/color incidence, toss a private coin with probability

    theta_v=q/(1-p)^{|B(v)|},    q=h^{-1/8}.

As in the common-palette proof, theta_v<=1 for large h. A color in the prescribed list is eligible for v=(a,b) exactly when a belongs to S, no member of B(v) belongs to S, and the private coin succeeds. A candidate color is eligible with probability p q, independently across colors. The expected eligible list size is at least 128(r+1)Nq. Chernoff's bound and a union bound give eligible lists of size at least

    L=floor(64(r+1)Nq)

for every vertex, with probability tending to one.

For a fixed color and clique, consider only vertices whose prescribed lists contain that color. In an original odd-row clique, condition on the common odd row belonging to S. Each remaining indicator then has mean q. In an added clique its unconditional mean is p q<=q. In either case the expected eligible count is at most Nq. Restricting the candidate set cannot increase its dependency degree: the blocker-frequency bounds give a dependency graph of maximum degree h^{o(1)}.

The dependency-graph Chernoff estimate from the level-palette proof therefore gives

    Pr(eligible count > 2Nq) <= exp(-Nq/h^{o(1)}).

Here Nq>=h^{5/24}. The union bound still holds over the polynomial number of colors and cliques. Consequently every color has at most 2Nq eligible vertices in each clique, simultaneously with the lower list-size bound.

Fix such eligible lists and trim them to size L. P conflicts between distinct odd-row cliques are already excluded by eligibility. For original and added clique edges, independently select a uniform color from each list. A monochromatic edge/color event has probability L^{-2}. Each vertex belongs to at most

    L * 2(r+1)Nq

such events. The symmetric local lemma applies because L is at least 31 times 2(r+1)Nq for large h. It supplies a proper coloring from the prescribed lists.

This proves the band lemma without a common-palette hypothesis. Lists need not overlap, have comparable unions, or satisfy a separate Hall condition.

## 3. Route the original colors into disjoint bands

Use the offset bands of the original P theorem: the low band D(u)<=log h has R=1; higher bands have 2^j log h<D(u)<=2^{j+1}log h and R=2^j. They satisfy

    sum_b R_b N_b=O(h).

For each large band N_b>=h^{1/3}, reserve a routing weight w_b=K_b from Section 2.

Combine all small bands into one bucket U_small. Put N_small=|U_small| and M_small=sum_{u in U_small}D(u). Orient each non-clique P edge from its source odd point to the target even point. The outdegree into this bucket is at most M_small. Original and added clique edges contribute at most (r+1)N_small more. Thus every induced subgraph has average degree at most twice this bound. The bucket has a greedy list-coloring bound

    d_small=ceil(2M_small+2(r+1)N_small)+1=h^{1/3+o(1)}.

Set its routing weight to max(d_small,64 log h). The added logarithmic weight ensures concentration even if the small bucket is sparse. If the bucket is empty, it can instead be omitted.

The sum W of all routing weights is O_K(h). Choose C_K so that the original lists, after trimming to ceil(C_K h) colors, have size at least 4W. Their union has O_K(h^3) colors. Assign each color independently to one bucket, with probability w_b/W for bucket b.

A vertex in bucket b has a binomial number of routed colors with expectation at least 4w_b. The probability that it receives fewer than w_b colors is at most exp(-w_b). Large-band weights grow faster than log h, and the small-bucket weight is at least 64 log h. A union bound over at most h^2 vertices proves that some routing gives every vertex its required number of colors.

Fix that routing. Apply Section 2 separately in each large band and greedy list coloring in the small bucket. Different buckets use disjoint sets of color names, so all conflicts between buckets are automatically respected. This proves the theorem for large h. Increasing C_K covers the finitely many remaining heights.

## 4. The exact interface with a geometric slot rule

Take a prime p>10h and the physical placement

    x(a,b)=2(a-1)+4p c(a,b).

Suppose a separate argument supplies allowed slot sets A(a,b) inside [1,C' h], each of size at least C_K h, and proves the desired geometric exclusions for every selection satisfying the P and level constraints. The theorem then selects slots with those constraints in width O(h^2). The phrase 'every selection' is essential: a restriction on each label separately must also control configurations involving several labels and different slots.

A bounded proper precoloring can be preserved. Delete its used colors from all uncolored lists, color the remaining induced graph using the theorem, and retain the prescribed colors. This is deliberately stronger than deleting colors only at neighbors. It costs at most the number of precolored colors per list. Thus four P/level-compatible labels can be forced into one common allowed slot whenever all other lists retain C_K h colors after deleting that slot.

Neither the original common-palette proof nor this list extension excludes tilted right angles, mixed four-cell collisions, or filling obstructions. The construction problem now has a precise combinatorial interface: it needs a geometric rule that leaves sufficiently large lists and remains valid under a globally proper selection.
