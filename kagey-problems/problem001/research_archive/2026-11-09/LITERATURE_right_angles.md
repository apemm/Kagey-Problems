# Literature: right angles, rectangles, and girth-eight bipartite graphs

Date: 2026-11-09. Scope: Problem 001 (blackout sets for lattice rectangles of every orientation).

## Conventions

- S is the blacked-out set in the h x m grid, h <= m. "Axis graph" means the bipartite graph rows x columns with edge set S. For axis-aligned rectangles only, the conditions say the axis graph has no C4 and no C6 (girth at least 8).
- Each item gives a citation, a statement, and one sentence on the bearing.
- Verification labels:
  - **[read]**: I read the statement in the paper's own text.
  - **[abstract]**: I read only the abstract page.
  - **[secondary]**: the statement is taken from another paper that quotes it. The quoting paper is named.
  - **[search excerpt]**: the statement appeared only in a search-engine excerpt of the source. Treat it as unverified until the source is opened.
- Exponent arithmetic that I did myself is marked "my substitution".

---

## A. Unbalanced bipartite Turan numbers for {C4, C6}-free graphs

### A1. Neuwirth, girth eight (the most relevant item in this section)

S. Neuwirth, "The size of bipartite graphs with girth eight", arXiv:math/0102210 (2001). https://arxiv.org/abs/math/0102210 **[read]**

- Theorem 1 / Theorem 8. "Let G be a bipartite graph on v + w vertices. (i) If G contains no cycle of length 4 and 6, then its size e satisfies e^3 - (v + w)e^2 + 2vwe - v^2 w^2 <= 0. (ii) If v >= floor(w^2/4), then furthermore e <= v + floor(w^2/4)." Equality in (i) holds exactly for stars (v = 1 or w = 1) and for incidence graphs of weak generalized quadrangles.
- Corollary 16 (balanced case). If v = w and the girth is at least 8, then e < v^(4/3) + (2/3)v - (2/9)v^(2/3) - (20/81)v^(1/3).
- Proposition 17. For a bipartite graph with no C4 and no C6: e <= 2^(1/3) (vw)^(2/3) if max(v, w) <= floor(min(v, w)^2/4), and e <= floor(min(v, w)^2/4) + max(v, w) otherwise. The second alternative is attained: take the complete bipartite graph on a balanced split of the small side V, subdivide every edge (the subdivision vertices go to the large side W), and attach the remaining vertices of W as leaves.
- Proposition 3. With no C4 and no C6, if w > floor(v^2/4) then at least ceil(w - v^2/4) vertices of W have degree 0 or 1. If the minimum degree is at least 2, then w <= floor(v^2/4) and v <= floor(w^2/4).
- Corollary 13 (path count). A bipartite graph on v + w vertices with minimum degree 2 has at least e(e/v - 1)(e/w - 1) paths of length 3. In a graph with no C4 and no C6 the number of such paths is at most vw - e.
- Remark 15. The cubic bound does not always give the right order: de Caen and Szekely find a counterexample to the expectation e ~ (vw)^(2/3) when v "lies in an interval just slightly below" w^2, and they conjecture this happens as soon as v >> w^(5/4) and v << w^2.

Bearing: Proposition 17 is the axis-only upper bound m + floor(h^2/4) for every m > floor(h^2/4), so in the strip range h^2/4 < m < h^2 polylog(h) the only open question is whether the extremal subdivision construction survives the tilted conditions. Corollary 16 shows that the axis conditions alone give n^(4/3)(1 + o(1)) in the square, and A4 shows that this is attained by abstract graphs, so any improvement of the exponent 4/3 must use tilted rectangles.

### A2. Naor and Verstraete, ex(m, n, C_{2k})

A. Naor and J. Verstraete, "A note on bipartite graphs without 2k-cycles", Combin. Probab. Comput. 14 (2005) 845-849. Preprint dated December 9, 2003: https://web.math.princeton.edu/~naor/homepage%20files/bipartitec2k.pdf **[read]** (preprint; journal details not checked against the journal page)

- Corollary 2. ex(m, n, C_{2k}) <= (2k - 3)[(mn)^((k+1)/(2k)) + m + n] if k is odd, and (2k - 3)[m^((k+2)/(2k)) n^(1/2) + m + n] if k is even. (The abstract of the preprint prints the exponents as (k+1)/k and (k+2)/k. The body, Theorem 1 and Corollary 2, has the denominators 2k.)
- For k = 3 (my substitution): ex(m, n, C6) <= 3[(mn)^(2/3) + m + n].
- Theorem 1 is stated for gamma(m, n, g, k), the maximum size of an m by n bipartite graph of girth at least 2g with no 2k-cycle. The paper notes that results of Hoory and of Lam give gamma(m, n, k, k) <= (mn)^((k+1)/(2k)) + m + n style bounds with constant 1, and that generalized polygons show constant 1 is best possible for k in {2, 3, 5} when m = n.
- Theorem 4. gamma((k - 1)m, n, k, k) >= (k - 1) gamma(m, n, 2, k). With generalized quadrangles this gives liminf gamma(n, 2n, 3, 3)/gamma(n, 2n, 2, 3) >= 2^(1/3).

Bearing: gives the order (hm)^(2/3) + h + m for the axis graph in every strip, with a worse constant than A1; it adds nothing to A1 for girth 8.

### A3. Furedi, Naor and Verstraete, the hexagon

Z. Furedi, A. Naor and J. Verstraete, "On the Turan number for the hexagon", Adv. Math. 203 (2006) 476-496. https://web.math.princeton.edu/~naor/homepage%20files/hexagons.pdf **[search excerpt]**

- ex(m, n, C6) < 2^(1/3) (mn)^(2/3) + 16(m + n), and for n = 2m this is asymptotically tight: ex(m, 2m, C6) = 2^(1/3)(mn)^(2/3) + O(n) for infinitely many m.
- ex(n, C6) < 0.6272 n^(4/3) for large n.

Bearing: C6-free graphs may contain C4, so these bounds are weaker than A1 for this problem; listed only to complete the picture.

### A4. Constructions: generalized quadrangles

- Neuwirth, Remark 10 **[read]**: equality in the cubic inequality forces a biregular graph with v = (t + 1)(1 + st), w = (s + 1)(1 + st), e = (s + 1)(t + 1)(1 + st). Generalized quadrangles with parameters (s, t) in (q, q), (q, q^2), (q^2, q^3), (q - 1, q + 1) exist for prime powers q, and "all known ones fit in this list". For s = 1 the extremal graph is the point-line incidence graph of a (t + 1) x (t + 1) grid of lines, the de Caen and Szekely example.
- Lazebnik and Wang survey (A6), Theorem 8 **[read]**: for k = 2, 3, 5 and v = 2(q^k + ... + q + 1), ex(v, {C3, ..., C_{2k+1}}) = (q + 1)(q^k + ... + q + 1), and every extremal graph is a generalized (k + 1)-gon.

Bearing: GQ(q, q) gives an abstract axis graph with n ~ q^3 rows and columns and ~ n^(4/3) edges; GQ(q, q^2) gives sides h ~ q^4 and m ~ q^5 with e ~ q^6 = (hm)^(2/3) edges, that is m ~ h^(5/4) (my substitution from Remark 10 with s = q, t = q^2). Both are candidates for the "embed, then repair tilted violations" tests in the final section.

### A5. de Caen and Szekely

- D. de Caen and L. A. Szekely, "The maximum size of 4- and 6-cycle free bipartite graphs on m, n vertices", in Sets, Graphs and Numbers (Budapest, 1991), Colloq. Math. Soc. Janos Bolyai 60, North-Holland, 1992, 135-142. **[secondary]** (Neuwirth; Lazebnik and Wang)
- D. de Caen and L. A. Szekely, "On dense bipartite graphs of girth eight and upper bounds for certain configurations in planar point-line systems", J. Combin. Theory Ser. A 77 (1997) 268-278. **[secondary]** (Neuwirth)

Statements as quoted by others:
- Neuwirth: their Theorem 1 gives (i) e <= 2^(1/3)(vw)^(2/3) if the minimum degree is at least 2, and (ii) e = O((vw)^(2/3)) if v = O(w^2) or w = O(v^2). Their Theorem 4 gives a counterexample to e ~ (vw)^(2/3) for v slightly below w^2, and they conjecture this for w^(5/4) << v << w^2.
- Lazebnik and Wang, Section 4.10: let f(n, m) be the maximum size of a girth >= 8 bipartite graph with sides n >= m. Erdos conjectured f(n, m) = O(n) for m = O(n^(2/3)). de Caen and Szekely refuted this with graphs having m ~ n^(2/3) and n^(1 + 1/57 + o(1)) edges, and proved the upper bound O(n^(1 + 1/9)).

Bearing: for the axis graph with h ~ m^(2/3) (that is, m ~ h^(3/2)) the truth lies between m^(1 + 1/15) (A6) and m^(1 + 1/9), so the strip problem is open even without tilted rectangles in the range h^(5/4) << m << h^2.

I could not obtain either de Caen and Szekely paper directly.

### A6. Lazebnik, Ustimenko and Woldar; Wenger graphs

F. Lazebnik and Y. Wang, "Some families of graphs, hypergraphs and digraphs defined by systems of equations", arXiv:2503.07915 (2025). https://arxiv.org/abs/2503.07915 **[read]**

- Section 4.10: Lazebnik, Ustimenko and Woldar (J. Combin. Theory Ser. B 61 (1994) 111-117) "explicitly constructed an infinite family of (n^(2/3), n)-bipartite graphs of girth 8 with n^(1 + 1/15) edges". The graph has P = F_q x F_{q^2} x F_q restricted to a first coordinate set A of size q^(1/3), L = F_{q^2} x F_{q^2} x F_q, with adjacency l2 + p2 = p1 l1 and l3 + p3 = -(p2 conj(l1) + conj(p2) l1), where n = q^2. Problem 5 of the survey asks to improve either exponent in c1 n^(1 + 1/15) <= f(n^(2/3), n) <= c2 n^(1 + 1/9).
- Section 4.4: the Wenger graph W_m(q) has 2q^(m+1) vertices, is q-regular, has q^(m+2) edges, and is defined by l_{k+1} + p_{k+1} = l_k p_1 for k = 1..m. Wenger's graphs H_k(p), k = 2, 3, 5, have no C4, C6, C10 respectively and reach the order v^(1 + 1/k). (W_2(q) is the girth-8 case: q^3 + q^3 vertices, q^4 edges.)
- Section 7.1 (Furedi, Lazebnik, Seress, Ustimenko, Woldar, J. Combin. Theory Ser. B 64 (1995) 228-239): biregular graphs of bidegree (r, s) and girth exactly 2t exist for all r, s, t >= 2, and the algebraic construction (for r, s >= t) contains (r', s', t)-graphs as induced subgraphs for all smaller bidegrees.

Bearing: W_2(q) and D(3, q) are explicit, coordinate-defined girth-8 axis graphs of the extremal order n^(4/3) in the square, and the induced-subgraph property gives unbalanced girth-8 graphs for strips; these are the natural algebraic seeds for a lower bound above n^(6/5).

### A7. What is known when m is about n^2

- Neuwirth Proposition 17 settles the axis problem exactly once the long side exceeds floor(short^2/4): the maximum is long + floor(short^2/4).
- Below that threshold the bound is 2^(1/3)(vw)^(2/3), which at v = w^2/4 equals w^2/2 (my substitution), consistent with the two alternatives meeting.
- By A5, (vw)^(2/3) is not the true order for v slightly below w^2.

---

## B. Right angles and right triangles in point sets and grids

### B1. Pach and Sharir, repeated angles

J. Pach and M. Sharir, "Repeated angles in the plane and related problems", J. Combin. Theory Ser. A 59 (1992) 12-22. **[secondary]** (Aires)

M. Aires, "Repeated angles in the plane for angles with algebraic tangents", arXiv:2201.10688 (2022). https://arxiv.org/abs/2201.10688 **[read]**

- As quoted by Aires: "Pach and Sharir proved that, for all 0 < theta < pi, any set of n points in the Euclidean plane contains at most O(n^2 log n) triples which determine an angle with measure theta. They also showed that, for tan(theta) = a sqrt(m)/b with a, b, m positive integers, this upper bound is tight".
- Aires, Theorem 2.1: "If tan(theta) is algebraic over Q, then for n >= 3, there exist arrangements of n points in the Euclidean plane with Omega_theta(n^2 ln n) triples determining angle theta." The construction generalizes "the original approach of Pach and Sharir from rectangle lattice grids to similar grid-like sets".

Bearing: a set S with N points spans at most O(N^2 log N) right angles, which caps the number of completion events from above; condition (2) needs the opposite direction (a lower bound on right angles with completion in the grid), so Pach and Sharir alone does not improve n^(4/3). The log factor is the same Pythagorean log that appears in the known n^(4/3)(log n)^(-1/3) bound.

I could not open the Pach and Sharir paper itself; I did not verify that the right angle (tan undefined) is covered by the tightness statement, although the construction is on a rectangular lattice.

### B2. Counting Pythagorean pairs (the source of the log factors)

M. Benito and J. L. Varona, "Pythagorean triangles with legs less than n", J. Comput. Appl. Math. 143 (2002) 117-126. **[secondary]** (Janosik, Nador, Nagy and Simon, Lemma 3.8)

- "The number of ordered Pythagorean triples (a, b, c) such that a < n, b < n and a^2 + b^2 = c^2 is O(n log n)."

Bearing: this is the standard input for counting tilted lattice configurations whose side lengths must be integers (rhombi); for rectangles the relevant count is of orthogonal lattice vector pairs, which is larger, so this lemma applies only to sub-families such as rectangles with integer side lengths.

### B3. Isosceles right triangles in [n]^2 (corners and tilted corners)

G. Karolyi and J. Solymosi, "A Salem-Spencer-type construction for large subsets of integer grids with no isosceles right triangles", arXiv:2607.22828 (2026). https://arxiv.org/abs/2607.22828 **[read]**

- F(n) is the largest subset of {0, ..., n-1}^2 with no nondegenerate isosceles right triangle (any orientation).
- Theorem 4.2. "For every integer n > 1, F(n) >> n^alpha / (log n)^140, where alpha = log 281 / log|51 + 51i| = 1.317865..."
- Upper bound quoted from Pilatte (Discrete Analysis 2022, Paper 16): F(n) << n^2/(log n)^(1 + c) for some absolute constant c > 0.
- Method. Observation 2.1: a, b, c in Z[i] form an isosceles right triangle with right angle at b if and only if a + ic = (1 + i)b. Theorem 2.6: a carry-free digit alphabet P in base beta with a "peeling order" of size q gives F(n) >> n^(log q/log|beta|)/(log n)^((q-1)/2). The 281-point alphabet in base 51 + 51i was found by computer search and is verified by a finite check.
- "From the other direction, even a superlinear lower bound is not obvious."

M. Janosik, A. Nador, Z. L. Nagy and L. B. Simon, "Avoiding configurations of small size in the square grid", arXiv:2601.14465 (2026). https://arxiv.org/abs/2601.14465 **[read]**

- Theorem 2.3 (Shkredov): every subset of [n] x [n] of size at least n^2/(log log n)^C contains an axis-parallel corner {(a, b), (a + d, b), (a, b + d)}.
- Theorem 2.4 (Pilatte), as stated there: the maximum isosceles-right-triangle-free set in [n]^2 has size O(n^2/(log n)^(1 + eps)). (The quantifier on eps differs from the Karolyi and Solymosi wording; check Pilatte before citing.)

I. D. Shkredov and J. Solymosi, "Tilted corners in integer grids", arXiv:2103.01645; INTEGERS 21A (2021). https://arxiv.org/abs/2103.01645 **[search excerpt]** Treats corner-free sets with rotated corners in [n] x [n] and F_p x F_p. I did not read the statements.

Bearing: a rectangle with a missing corner whose two legs are equal is a tilted corner, so these results concern the square sub-case of condition (2); they show that forbidding one fixed shape of right angle still allows n^(1.31) points, far above n^(4/3) in spirit but for a much weaker condition, and the digit method only handles a single linear equation (one fixed leg ratio).

### B4. Right triangles of arbitrary shape in the grid

I found no paper that bounds the largest subset of [n]^2 with no right triangle of any orientation and any leg ratio. Checked: the Janosik et al. survey (lists right triangles as "well-studied" in the abstract but states results only for isosceles right triangles and corners), OEIS full-text search (no entry; A271906 is the isosceles case), and general web search. For axis-parallel right triangles the maximum is linear by a folklore argument (my remark, not sourced).

Bearing: none available; the problem here allows right angles in S and only restricts their completions, so right-angle-free sets are a much smaller class.

### B5. Right-angle-free subsets of arbitrary planar sets (Erdos and Silverman)

**[search excerpt]** MathWorld "RAT-Free Set" (https://mathworld.wolfram.com/RAT-FreeSet.html) reports that every set of n coplanar points contains a right-triangle-free subset of size f(n) with sqrt(n) <= f(n) <= 2 sqrt(n), citing Abbott (J. Combin. Theory Ser. A 29 (1980)). Search results also list Gamble, Pulleyblank, Reed and Shepherd, "Right angle free subsets in the plane" (Graphs Combin. 1995) and a 2009 note by Elekes. I did not open any of these.

P. J. Dukes, "The deviation from right angles in k-subsets of points in the plane", arXiv:2605.01281 (2026). **[abstract]** Studies the Erdos and Silverman threshold r(k) and the angle deviation Gamma_k(n); 8 <= r(4) <= 10.

Bearing: the sqrt(N) scale is for worst-case point sets and gives nothing new for the grid.

### B6. Right angles in F_q^n

G. Ge and C. Shangguan, "Maximum subsets of F_q^n containing no right angles", arXiv:1612.08255; J. Algebraic Combin. (2020). https://arxiv.org/abs/1612.08255 **[search excerpt]** Upper bound binom(n + q, q - 1) + 3 for odd prime powers q, improving Bennett's O(q^((n+2)/3)).

Bearing: high-dimensional, fixed q; not applicable to [n]^2.

### B7. Rectangles and squares in the grid

Janosik, Nador, Nagy and Simon (arXiv:2601.14465) **[read]**:

- Theorem 3.18 (Reiman): (1 + o(1)) n^(3/2) <= f_axrec(n) <= (n/2)(1 + sqrt(4n - 3)) for subsets of [n]^2 with no axis-parallel rectangle.
- Theorem 3.22: f_sq(n) = Omega(n^(3/2)/e^(O(sqrt(log n)))) for subsets with no square of any orientation. Proof: intersect an axis-square-free set with S x [n], S a Sidon set; a tilted square would force a repeated difference among x-coordinates.
- Theorem 3.23 (Prendiville; see also Shkredov and Solymosi): f_sq(n) = O(n^2/(log log n)^c).
- Theorem 3.7: the largest rhombus-free subset of [n]^2 has size Omega(n^(4/3)/(log n)^(1/3)). Proof: take [1, n] x S with S a Sidon set (n^(3/2) points); by Proposition 3.9 this set contains only O(n^2 log n) rhombi (Sidon forces two horizontal sides, then Benito and Varona counts the shapes); keep each point with probability q ~ n^(-1/6)(log n)^(-1/3) and delete one point per rhombus. Remark 3.12: replacing the Sidon set by a set with differences repeated at most g times does not change the bound.
- Theorem 3.6 (Thiele; Dong and Xu): n - o(n) <= f_cyclic(n) <= 2.5n - 1.5 for subsets with no four concyclic points (collinear counts as concyclic). Ghosal, Goenka and Keevash (arXiv:2509.06935) give 7n/12 by a randomized construction.

I found no result on the largest subset of [n]^2 with no rectangle of any orientation. The survey does not define such a function, and OEIS has entries only for axis-parallel rectangles (A072567) and for squares (A240443 any orientation, A227133 axis-parallel).

Bearing: Theorem 3.7 is the closest published template: a structured host set (line x Sidon) cuts the number of tilted configurations to n^2 log n, and alteration then gives n^(4/3)(log n)^(-1/3), the same expression as the current upper bound for Problem 001; the same host-set idea is the most promising route to beat n^(6/5) from below. Concyclic-free sets avoid all rectangles but are linear in size.

---

## C. Supersaturation and counting

### C1. Paths of length three in girth-8 graphs

Neuwirth, Theorem 11 and Corollary 13 (see A1) **[read]**. For a nonnegative matrix with row sums >= 2 rho and column sums >= 2 gamma, sum a_ij (a_i* - rho)(a_*j - gamma) >= e(e/v - rho)(e/w - gamma). This refines the Atkinson, Watterson and Moran inequality sum a_ij a_i* a_*j >= e^3/(vw).

Bearing: in the axis graph a path of length 3 is an axis-aligned right angle together with its completion cell, and "no C6" says each non-edge cell is completed at most once; the inequality is exactly the supersaturation step behind the axis part of the n^(4/3) bound, and a tilted analogue (a lower bound on tilted right angles in S landing in the grid) is the missing ingredient.

### C2. Supersaturation for even cycles, balanced

Stated in Vassilevska Williams and Westover (C3) as Theorem 2, attributed to T. Jiang and L. Yepremyan, Combin. Probab. Comput. 29 (2020) 698-721 **[secondary]**: "For every integer k >= 2, there exist constants c, C such that if G is an n-node graph with m >= C n^(1 + 1/k) edges, then G contains at least c (m/n)^(2k) copies of C_{2k}."

Bearing: for k = 3 this gives at least c (e/n)^6 hexagons once e >= C n^(4/3); it concerns C6 counts in graphs that may contain C4, so it is a tool only if one relaxes to "few violations".

### C3. Unbalanced supersaturation for C6

V. Vassilevska Williams and A. Westover, "Listing 6-cycles in sparse graphs", ITCS 2025, arXiv:2411.07499. https://arxiv.org/abs/2411.07499 **[read]**

- Theorem 1 (Dahlgaard, Knudsen, Stockel): a bipartite graph with sides L, R and m > 100k(L + R + (LR)^((k+1)/(2k))) edges contains a C_{2k}.
- Conjecture 25 (Jin and Zhou, unbalanced supersaturation): if m >= 100k(|A| + |B| + (|A||B|)^((k+1)/(2k))) then the number t of 2k-cycles satisfies t >= Omega(m^(2k)/(|A|^k |B|^k)). Open.
- Theorem 12 (partial result for k = 3): with L = |A| <= R = |B|, L >= 100, d_L = m/L, d_R = m/R and m/ceil(log(L + R))^10 > L + R + (LR)^(2/3), the number of hexagons is at least d_R^3 d_L^3 min(1, d_R^3/L, d_L^2 d_R^2/L^2) c/log^70 n.
- Facts 10 and 11 (folklore path supersaturation): m >= 2R gives at least L(m/L)(m/R)/2 two-paths A-B-A; m >= 50(L + R) gives Omega(L (m/L)^2 (m/R)^2) four-paths A-B-A-B-A.

Bearing: these are the available tools for counting forced hexagons in an h x m axis graph in the open strip range h < m < h^2; they do not involve tilted rectangles.

### C4. Regularity for graphs with few 4-cycles

D. Conlon, J. Fox, B. Sudakov and Y. Zhao, "The regularity method for graphs with few 4-cycles", arXiv:2004.10180. https://arxiv.org/abs/2004.10180 **[abstract]** Develops sparse regularity for graphs with few 4-cycles and proves counting and removal lemmas for 5-cycles; one corollary is that r-graphs (r >= 3) of girth greater than 5 on n vertices have o(n^(3/2)) edges.

Bearing: shows that a removal-lemma argument can turn a "girth plus one more forbidden pattern" hypothesis into a little-o gain over the Turan bound; a comparable statement for girth 8 plus tilted completions would give o(n^(4/3)), but no such statement exists in the literature I found.

### C5. Szemeredi-Trotter and lattice rectangles

- The Pach and Sharir bound (B1) is proved by incidence methods; I could not check the proof.
- I found no paper that uses point-line incidences to count lattice rectangles of all orientations with three corners in a given set, and none that bounds pairs of right angles sharing a completion point.
- Related but different: Solymosi, "Dense arrangements are locally very dense I", SIAM J. Discrete Math. 20 (2006) 623-627, arXiv:math/0504009 **[read via ar5iv summary]**. Theorem 1: n points and n lines with at least c n^(4/3) incidences contain, for n >= n0(k, c), k points in general position with every pair joined by a line of the arrangement. Lemma 2 gives delta n^3 triangles by triangle removal.
- M. Mirzaei and A. Suk, "On grids in point-line arrangements in the plane", arXiv:1812.11162, Discrete Comput. Geom. 65 (2021) **[read via ar5iv summary]**. Theorem 1.6: n points and n lines with no natural t x t grid have O(n^(4/3 - eps(t))) incidences.

Bearing: these say that real point-line incidence graphs of girth 8 have o(n^(4/3)) edges, so a generalized quadrangle cannot be drawn with real lines; they do not constrain the axis graph of S, which is an abstract bipartite graph, but they would apply to any reformulation of the tilted conditions as point-line incidences.

---

## D. The exact problem

### D1. Source

P. Kagey, Open Problem Collection, Problem 1. https://peterkagey.com/problems/001/ **[read]**

- Statement: in an n x m grid a rectangle is chosen with corners on grid points; "How many vertices may be blacked out so that every rectangle can still be uniquely identified?"
- Related questions listed: interior lit instead; perimeter points lit; squares only; parallelograms; rectangles that are horizontal, vertical or at 45 degrees; triangular grid with equilateral triangles; higher dimensions.
- Only reference on the page: P. Kagey, "Removing points from a triangular array without losing information", Math Stack Exchange question 2465571. I could not open that page (the site refused the fetch).
- The page states no results and links no OEIS sequences.

### D2. OEIS

OEIS full-text search for the problem returns exactly two entries **[read, search page]**:

- A397315: "Table read by antidiagonals: T(n,k) = maximum number of points that can be blacked out..." of an n x k grid so that every rectangle, tilted ones included, is identified by its visible corners.
- A399580: number of maximum blackouts of the n x k grid.

Both credit Kagey's Problem 001 and the 2026 preprint and repository for this project. No third-party sequence or paper on the problem turned up.

Rectangle counts: A289832 (triangle T(n, k) = number of rectangles with vertices on an (n+1) x (k+1) grid, H. J. Partridge, 2017) and A085582 (its diagonal) **[read]**. Neither cites any bound or paper.

### D3. Searches that returned nothing relevant

- "identifying set", "separating code", "metric dimension" for rectangles in grids.
- "distinct presentations", rectangles "determined by" corners outside a set.
- "Golomb rectangle" as an avoidance problem (results are about the Golomb puzzle and Golomb rulers).
- Sidon sets in Z^2 avoiding rectangles. (A two-dimensional Sidon set is parallelogram-free, hence rectangle-free, but Lindstrom's theorem gives size n + O(n^(2/3)) in [n]^2; see Janosik et al., Theorem 3.3 **[read]**.)

Bearing: no prior work on the exact problem was found, so the n^(6/5) and n^(4/3) bounds stand as the state of the art.

---

## E. Algebraic constructions where lattice geometry matters

### E1. Line x Sidon host sets

Janosik et al., Proposition 3.9 and Theorem 3.7 (see B7) **[read]**. In [1, n] x S with S Sidon, every rhombus has two horizontal sides and the number of rhombi is O(n^2 log n).

Bearing: in a host set [1, n] x S the Sidon property removes most tilted coincidences among second coordinates; the analogous count of tilted rectangle pairs in such a host has not been done and is a concrete computation to try.

### E2. Carry-free digit sets over Z[i]

Karolyi and Solymosi (B3) **[read]**. A linear equation over Z[i] (here a + ic = (1 + i)b) can be avoided by a digit construction with exponent log q/log|beta|, and the alphabet need not itself avoid the pattern if it has a peeling order.

Bearing: a right angle with leg ratio lambda is the linear equation a - b = i lambda (c - b); the method handles one ratio at a time, so it could build sets with no right angle of a few prescribed shapes (for example the shapes that are most frequent in the n x n grid) but not all shapes at once.

### E3. Concyclic-free algebraic sets

Thiele, "The no-four-on-circle problem", J. Combin. Theory Ser. A 71 (1995) 332-334; Dong and Xu, arXiv:2506.18113; Ghosal, Goenka and Keevash, arXiv:2509.06935. **[secondary]** (Janosik et al., Theorem 3.6 and the text after it)

Bearing: these sets contain no rectangle of any orientation but have at most 2.5n - 1.5 points, so they are useful only as the linear "spine" of a strip construction.

### E4. Point-line arrangements with large girth

M. Mirzaei, A. Suk and J. Verstraete, "Constructions of point-line arrangements in the plane with large girth", arXiv:1911.11713. https://arxiv.org/abs/1911.11713 **[abstract]** Constructs n points and n lines in the plane whose incidence graph has girth at least k + 5 and at least Omega(n^(1 + 4/(k^2 + 6k - 3))) incidences. For girth 8 (k = 3) the exponent is 1 + 1/6 (my substitution).

Bearing: a geometric girth-8 graph with n^(7/6) edges; n^(7/6) is below the current n^(6/5), so this does not help directly.

### E5. Generalized quadrangles, Wenger graphs or norm graphs placed in the grid

I found no paper that embeds a generalized quadrangle, a Wenger graph, or a norm graph into the integer grid and studies right angles or tilted rectangles of the resulting point set. Girth-8 monomial graphs and their uniqueness are surveyed in Lazebnik and Wang, Section 4.9 (not read in detail).

---

## F. Pythagorean pairs (brief)

N. Frantzikinakis, O. Klurman and J. Moreira, "Partition regularity of Pythagorean pairs", Forum Math. Pi 13 (2025) e5, arXiv:2309.10636. https://arxiv.org/abs/2309.10636 **[search excerpt of the abstract]**

- Every finite colouring of the positive integers contains a monochromatic pair x, y with x^2 + y^2 = z^2 for some integer z; a density version holds for level sets of multiplicative functions.
- Follow-up: "Partition regularity of generalized Pythagorean pairs", arXiv:2407.08360, treats a x^2 + b y^2 = c z^2, in some cases conditionally on an Elliott-type conjecture.

Bearing: any colouring argument that assigns colours to leg lengths so that no two legs of the same colour form a Pythagorean pair must use an unbounded number of colours, which limits colouring-based constructions for rectangles with integer side lengths.

---

## Summary

### Results that could bear directly on the upper bound n^(4/3)

1. Neuwirth, Corollary 16 with the generalized quadrangle GQ(q, q): the axis conditions alone cannot give an exponent below 4/3. An improvement must count tilted completions.
2. Neuwirth, Corollary 13 (paths of length 3) is the sharp supersaturation inequality for axis right angles. The missing result is its tilted analogue. I found none in the literature.
3. Conlon, Fox, Sudakov and Zhao show a removal-lemma route to little-o gains for sparse girth-type problems. Whether it adapts to girth 8 plus tilted completions is open.
4. Pach and Sharir bound right angles from above by O(N^2 log N). This is the wrong direction for the upper bound on |S| but fixes the log scale.

### Results that could bear directly on the lower bound n^(6/5)

1. Janosik, Nador, Nagy and Simon, Theorem 3.7: alteration inside [1, n] x (Sidon set) gives n^(4/3)(log n)^(-1/3) for rhombi. The same scheme for Problem 001 needs a count of violating configurations in a structured host set.
2. Algebraic girth-8 axis graphs with n^(4/3) edges: GQ(q, q) incidence graphs, Wenger graph W_2(q), D(3, q) (Lazebnik and Wang survey).
3. Karolyi and Solymosi: digit constructions over Z[i] reach n^(1.317) for one right-angle shape.

### Strip regime

1. Neuwirth, Proposition 17: the axis-only maximum is exactly m + floor(h^2/4) for m > floor(h^2/4). The gap to the known threshold m >= h^2 polylog(h) is purely a tilted-rectangle question.
2. For h^(5/4) << m << h^2 even the axis-only problem is open (de Caen and Szekely; Lazebnik, Ustimenko and Woldar: between m^(1 + 1/15) and m^(1 + 1/9) at m = h^(3/2)).

### Constructions worth testing

1. Host set [1, n] x T with T a Sidon set or a set with bounded difference multiplicity: count pairs of rectangles whose symmetric difference lies in the host, then apply alteration. Compare the resulting exponent with 6/5.
2. Wenger graph W_2(q) or GQ(q, q) as the axis graph on a q^3 x q^3 grid, with row and column labels chosen (a) at random, (b) so that rows or columns form a Sidon-like set of labels. Count tilted violations and delete.
3. The Neuwirth extremal strip graph (subdivided complete bipartite graph plus leaves) with the m columns ordered to minimize tilted violations, for h^2/4 < m < h^2 polylog(h).
4. Furedi, Lazebnik, Seress, Ustimenko and Woldar biregular girth-8 graphs as axis graphs for strips with h < m < h^2.
5. A Karolyi and Solymosi style digit set that avoids the two or three most frequent right-angle shapes, used as a host set for alteration.

### Not found

- Any prior work on the exact problem beyond Kagey's page and the two OEIS entries of this project.
- A bound for the largest subset of [n]^2 with no right triangle of arbitrary shape and orientation.
- A bound for the largest subset of [n]^2 with no rectangle of arbitrary orientation.
- Supersaturation or counting results for tilted lattice right angles or rectangles with three corners in a dense set; any Szemeredi-Trotter treatment of lattice rectangles.
- Generalized quadrangles, Wenger graphs or norm graphs embedded in the grid with rectangle or right-angle avoidance.
- Primary texts not obtained: both de Caen and Szekely papers, Pach and Sharir, Furedi, Naor and Verstraete (search excerpt only), Shkredov and Solymosi, Abbott, Gamble et al., Elekes, the Math Stack Exchange question.
