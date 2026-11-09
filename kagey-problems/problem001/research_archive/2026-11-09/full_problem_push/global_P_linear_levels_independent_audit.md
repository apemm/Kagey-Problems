# Independent audit of the linear-level palette extension

9 November 2026. The proof in global_P_linear_levels.md passes the
following independent checks. It establishes a palette of \(O_{\mathcal K}(h)\)
colors for the strengthened P graph and any fixed finite collection of
cliques \(b+ka=\mathrm{constant}\), with \(k\ne-1\).

1. Completing the square gives exactly
   \[
   \bigl((k^2+4)a+k(s-t)-4s\bigr)^2-(k^2+4)L^2
   =-4((k+1)s-t)^2.
   \]
   The final square has nonzero argument: the two terms have opposite
   parity. For nonzero integer \(k\), \(k^2+4\) is nonsquare. The
   fixed-discriminant norm bound therefore gives the required
   \(h^{o(1)}\) blocker frequency. The \(k=0\) factorization is separate
   and valid.
2. An added clique contains at most one vertex with a specified offset
   \(a-b\), because \(k+1\ne0\). Thus a band of \(N\) offsets meets each
   clique in at most \(N\) vertices. This is the reason for the excluded
   value \(k=-1\).
3. The thinning probability is at most one. Eligibility has conditional
   probability exactly \(q\) after fixing the vertex's own row as
   selected. The own row is absent from its blocker set.
4. Within an original odd-row clique, conditioning on the common own-row
   choice leaves a dependency graph whose degree is \(h^{o(1)}\).
   Within an added clique, own rows are distinct. Each row appears in
   only \(h^{o(1)}\) blocker sets, and each indicator uses only
   \(h^{o(1)}\) rows. Private thinning coins introduce no extra
   dependencies.
5. The displayed exponential-moment bound follows from Hölder applied
   to a proper coloring of that dependency graph. Since
   \(Nq\ge h^{5/24}\), its failure bound permits a union bound over all
   cliques and palette colors.
6. After list trimming, an event specifying the common color of an
   adjacent pair has probability \(L^{-2}\) and at most
   \(2L d_{\rm col}\) dependencies. The chosen constants give
   \(L/d_{\rm col}\to32\), so the symmetric local-lemma inequality has
   a fixed margin.
7. Original P edges across odd-row cliques remain excluded before the
   final coloring. The final local lemma only handles clique edges.
   Separate palettes for arithmetic bands make their costs additive,
   preserving the earlier \(O(h)\) sum.

The scope is also checked. The four labels
\((1,12),(3,20),(11,2),(13,10)\) have distinct even rows and distinct
\(b+4a\), but their even points form the stated hidden rectangle.
The added cliques therefore do not prove a complete quadratic-width
construction.
