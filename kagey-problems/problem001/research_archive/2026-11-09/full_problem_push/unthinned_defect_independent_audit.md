# Independent audit of the unthinned defect obstruction

9 November 2026. The proof in [Sparse-defect unthinned local-lemma obstruction](sparse_defect_unthinned_lll_obstruction.md) passes an independent audit.

The primitive odd direction pair and positive odd side scales give a unique right triangle with its right-angle vertex at the even defect cell. All rows lie in the strip. Once the repeated-column case is removed, its completion lies in an ordinary column at an even row, so the fixed parity row-pair set supplies a singleton rival. The primitive harmonic sum gives \(\Omega(h^3\log^2h)\) distinct assignment events, while the excluded equal-horizontal-offset family has only \(O(h^2\log h)\) members. Each event has probability \(\Theta(h^{-3})\).

Every event uses the defect row variable. Summing the ordinary asymmetric local-lemma inequalities over that clique gives the probability of exactly one success among auxiliary independent Bernoulli variables, which is at most one. The divergent total event probability therefore rules out this certificate. The same clique restriction rules out the stated clique-expansion certificate. This does not rule out a different dependency graph, conditioning, or another proof method.

The completion-root calculation is also correct. For a specified side column, summing the available vertical placements gives \(4\binom{k}{3}\), and division by \(k^3\) gives the limiting incident mass \(2/3\). At horizontal displacement one, divisibility is automatic and the horizontal offsets \(1\) and \(-4ab\) cannot coincide or make a repeated completion column. The diagonal-root contribution is \(h^{-1+o(1)}\). The bounded completion-root mass therefore does not contradict the logarithmically divergent black-root clique.

The later refinement to the incompatible-assignment graph also passes. Group events by their prescribed even defect row \(r\). Every pair from different groups is adjacent. Writing \(p_r\) for a group's probability sum and \(M_r\) for its certificate-weight sum, either stated criterion implies
\[
 p_r\le\frac{M_r}{1+\sum_{s\ne r}M_s}.
\]
Rearrangement and summation require
\[
 \sum_r\frac{p_r}{1+p_r}<1.
\]
Here each \(p_r=O(\log^2h/h)=o(1)\), while their sum is \(\Omega(\log^2h)\), so the necessary inequality fails. This uses only the complete cross-group adjacency and does not need a general dependency-region theorem.
