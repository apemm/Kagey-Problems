# Five-row partition dominance and the unconditional count theorem

Research note, 8 November 2026. The finite graph computation below completes the previously conditional five-row asymptotic. It does not establish dominance at every height.

**Result.** Every balanced partition on five rows has exactly one recurrent sea component. That component contains the two boundary constant states and has period one. Exact rational spectral bounds give
\[
 3.543875646281<\rho_5<3.543875646290
\]
for the parity partition, while every other partition has
\[
 \rho_\pi<3.400032010919.
\]
The parity partition therefore strictly dominates.

The graph computation is exhaustive. Floating-point iteration only proposes positive integer vectors; all final Collatz bounds and their comparisons use rational arithmetic.

## 1. Complete partition scan

The smaller block determines a balanced \(2+3\) partition uniquely. All ten blocks were enumerated, including reflected pairs separately.

| Smaller block | Reachable compressed states | Recurrent components | Perron root, approximately |
|---|---:|---:|---:|
| \(\{1,2\}\) | 1,212 | 1 | 3.3248373821 |
| \(\{1,3\}\) | 1,372 | 1 | 3.4000320109 |
| \(\{1,4\}\) | 1,168 | 1 | 3.2912136854 |
| \(\{1,5\}\) | 1,251 | 1 | 3.1619105337 |
| \(\{2,3\}\) | 961 | 1 | 3.1341894967 |
| \(\{2,4\}\), parity | 1,600 | 1 | 3.5438756463 |
| \(\{2,5\}\) | 1,168 | 1 | 3.2912136854 |
| \(\{3,4\}\) | 961 | 1 | 3.1341894967 |
| \(\{3,5\}\) | 1,372 | 1 | 3.4000320109 |
| \(\{4,5\}\) | 1,212 | 1 | 3.3248373821 |

All recurrent components have period one. For parity, the recurrent component has 1,436 states; the other 164 states are transient.

The comparison uses the exact fractions
\[
 \rho_5\ge\frac{2703542684891}{762877412961},
 \qquad
 \max_{\pi\ne{\rm par}}\rho_\pi
 \le\frac{831945314801}{244687494744}.
\]
The first rational number is strictly larger than the second.

## 2. Why the computation gives the count asymptotic

The sparse automaton recognizes exactly the bi-infinite sea shift, using live residual positive forbidden patterns. Every residual expires within \(2W_h\) steps, so its state on a bi-infinite word is determined by a bounded suffix. The residual and full-history presentations therefore have conjugate recurrent edge shifts. The exhaustive graph scan determines the sea components, their periods, and their spectral radii.

This does not identify the finite-board counting series. A normalized pattern can have its required black cells inside a finite word while its collision's common white cells lie beyond an end. The sparse automaton can then reject a geometrically valid finite word. The boundary vectors and insertion matrices in the count formula below come from the exact end-aware full-history construction, not from declaring all sparse states accepting.

The single recurrent component contains the boundary constants. Its period is one, and the isolated-double construction gives positive insertion weight for every edge. The hidden-rectangle classification excludes hidden rectangles in all parity equality words.

Apply the exact marked-resolvent theorem in [exact_counting_scc_and_resolvent.md](../counting_followup/exact_counting_scc_and_resolvent.md), with \(q_5=6\). The parity count has an order-seven dominant pole. All other partitions have a strictly smaller exponential base. Consequently there is a degree-six polynomial \(P_5\) with positive leading coefficient such that
\[
 a_5(m)=\rho_5^mP_5(m)+O(\theta_5^m)
 \qquad\text{for some }\theta_5<\rho_5.
\]
In particular
\[
 a_5(m)\sim c_5m^6\rho_5^m,\qquad
 c_5=B_5\prod_{e\in K_{\{1,3,5\},\{2,4\}}}\kappa_e>0.
\]
The quantities \(B_5,\kappa_e\) are the exact Perron boundary and insertion weights from the marked-history construction. This scan does not certify a numerical value of \(c_5\).

The nonparity contribution is
\[
 O\!\left(m^6(3.400032010919)^m\right).
\]
No numerical bound for the modulus of the parity component's subdominant eigenvalues is asserted here, so the first display uses an unspecified \(\theta_5<\rho_5\).

The rank-one marked-resolvent argument also makes the distributional conclusions unconditional at height five: almost every maximum blackout uses parity, its six scaled double positions converge to six independent uniform points in increasing order, and the edge-label order is asymptotically uniform over the \(6!\) orders and independent of those positions.

## 3. Reproduction and validation

The runner is [run_partitions.py](run_partitions.py), using the partition-aware engine [sea_sparse_automaton.py](sea_sparse_automaton.py). Full results and exact fractions are in [partition_graphs_h5.json](partition_graphs_h5.json).

For each partition, the runner compared the sparse automaton with a direct geometric presentation checker on every length-six word, 15,625 words per partition and 156,250 comparisons altogether. It also checked 40 longer walk/mutation samples per partition. All comparisons passed. The engine's tilted-rectangle templates had already been checked against the independent equal-diagonal rectangle enumerator.

All ten graphs completed in 13.47 seconds under a collective 120-second cap and a 512 MB per-process cap. There were no capped or unresolved five-row cases.

The sampled finite-word comparisons are validation data, not a general finite-language equivalence theorem. The joint height-five and height-six result, with periodic validation and the finite-end qualification, is recorded in [partition_dominance_h5_h6.md](partition_dominance_h5_h6.md).
