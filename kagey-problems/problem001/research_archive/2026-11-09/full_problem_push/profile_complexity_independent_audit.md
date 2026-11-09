# Independent audit of the general profile-complexity theorem

9 November 2026. The argument in [Low rectangle profile complexity](low_rectangle_profile_complexity.md) passes an independent audit. It applies to arbitrary binary row and column words, without a balance or protected-law assumption.

The normalization by lattice cosets is essential and correct. A good primitive direction has total defect bound \(O(\varepsilon h^4/R^2)\), whereas a lifted matrix has \(K^4\asymp_\eta h^4/R^4\) possible subrectangles. Averaging over its \(D=a^2+b^2\asymp R^2\) cosets supplies the missing factor. Representatives in a fundamental parallelogram move the chosen center by only \(O(R)=o(KR)\), so all cosets cover the same smaller physical square while remaining inside the board. Their rectangle families are disjoint.

The physical incidence graph in that square is exactly a union of \(D\) complete bipartite graphs. Coprimality gives \((a,D)=(b,D)=1\), and either inverse-coordinate congruence implies the other. Each row residue specifies one column residue, with both component sides of size \(\asymp K/R\).

The minimum-error XOR fit is valid. The true labels provide a fit with at most the original matrix error, so an optimal fit differs from the true edge sums in at most twice that error. On a complete bipartite graph, simultaneous complementation of both vertex classes gives the stated bound \(2F/\min(r,s)\) on vertex-label errors. One orientation bit per residue component therefore suffices. There is no missing exponential factor for the labels.

A biclique-union matrix has at most \((K+1)^{2K}\) descriptions. Adding the coset and \(D\) orientation bits still costs only \(\exp(o(h))\). A bounded number of tiles for each fixed boundary parameter covers the row and column words. Assigning overlapping positions to predetermined tiles avoids any need to count consistency choices. Hamming-ball counting and then sending the boundary parameter to zero prove the subexponential count of all low-defect profile pairs.

The stronger aggregated estimate is also valid. Choose tile centers with spacing a fixed fraction of their common inner-square side. Their outer rotated squares have bounded overlap. Hence their chosen coset defect counts \(n_t\) satisfy
\[
 \sum_t n_t\le C N_{a,b}/D.
\]
The pivot-removal cost on tile \(t\) is \(O(K^{2/3}n_t^{1/3})\). Hölder over \(O(1/\eta)\) tiles, followed by the physical vertex-error conversion, gives total error fraction
\[
 O\!\left(\eta+\frac{\varepsilon^{1/3}}{\eta}\right).
\]
Taking \(\eta=\varepsilon^{1/6}\) gives the logarithmic profile-count rate
\[
 O\!\left(\varepsilon^{1/6}\log(1/\varepsilon)\right)
\]
in the stated fixed-\(\varepsilon\), then large-height order of limits.

Both container consequences pass. A nearly maximal partition must have a large sparse-edge container; purification keeps its exact row coloring and supplies one low-test phase. Counting the row projections therefore gives only \(\exp(o(h))\) possible nearly maximal partitions. For stationary measures, each fingerprint determines one associated low-test phase, so the weighted far-profile count requires no factor for the full phase list. Block entropy then concentrates on Hamming neighborhoods of a subexponential list and gives phase entropy \(o(1)\), uniformly over balanced row partitions.

These are complexity and entropy statements. They do not classify every low-defect profile as ordinary or quadratic parity, or prove fixed-height component dominance.
