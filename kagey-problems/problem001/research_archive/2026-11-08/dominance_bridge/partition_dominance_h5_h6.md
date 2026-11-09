# Partition dominance and exact count asymptotics at heights five and six

Research note, 8 November 2026. Exhaustive finite graph computations establish the spectral hypotheses of the count theorem at heights five and six. They do not establish dominance at arbitrary height.

For every balanced partition at either height, the sea shift has exactly one recurrent component. This component contains both boundary constant states and has period one. The parity partition has strictly larger entropy than every other balanced partition. Consequently
\[
 a_5(m)\sim C_5m^6\rho_5^m,
 \qquad
 a_6(m)\sim C_6m^9\rho_6^m,
 \qquad C_5,C_6>0.
\tag{1}
\]
These are unconditional consequences of the exhaustive graph certificates and the analytical insertion and marked-resolvent theorems.

## 1. Exhaustive partition comparison

At height five, the smaller block identifies each balanced partition. At height six, choose the block containing row 1 to avoid counting complementary blocks twice. There are ten partitions at each height. Every case was enumerated to completion, including reflected cases separately.

| Height | Partition block | Reachable compressed states | Recurrent states | Perron root, approximately |
|---|---|---:|---:|---:|
| 5 | \(\{1,2\}\) | 1,212 | 1,126 | 3.3248373821 |
| 5 | \(\{1,3\}\) | 1,372 | 1,285 | 3.4000320109 |
| 5 | \(\{1,4\}\) | 1,168 | 1,081 | 3.2912136854 |
| 5 | \(\{1,5\}\) | 1,251 | 1,113 | 3.1619105337 |
| 5 | \(\{2,3\}\) | 961 | 840 | 3.1341894967 |
| 5 | \(\{2,4\}\), parity | 1,600 | 1,436 | 3.5438756463 |
| 5 | \(\{2,5\}\) | 1,168 | 1,081 | 3.2912136854 |
| 5 | \(\{3,4\}\) | 961 | 840 | 3.1341894967 |
| 5 | \(\{3,5\}\) | 1,372 | 1,285 | 3.4000320109 |
| 5 | \(\{4,5\}\) | 1,212 | 1,126 | 3.3248373821 |
| 6 | \(\{1,2,3\}\) | 43,839 | 42,340 | 3.3667396264 |
| 6 | \(\{1,2,4\}\) | 49,329 | 47,716 | 3.3260778194 |
| 6 | \(\{1,2,5\}\) | 43,127 | 41,867 | 3.3387252188 |
| 6 | \(\{1,2,6\}\) | 35,578 | 32,289 | 3.3014677172 |
| 6 | \(\{1,3,4\}\) | 43,127 | 41,867 | 3.3387252188 |
| 6 | \(\{1,3,5\}\), parity | 67,689 | 65,414 | 3.5896958403 |
| 6 | \(\{1,3,6\}\) | 38,755 | 36,698 | 3.4474427544 |
| 6 | \(\{1,4,5\}\) | 43,487 | 41,850 | 3.2460798784 |
| 6 | \(\{1,4,6\}\) | 38,755 | 36,698 | 3.4474427544 |
| 6 | \(\{1,5,6\}\) | 35,578 | 32,289 | 3.3014677172 |

Each row has one recurrent component, of period one. The remaining states are transient.

The final spectral bounds use positive integer vectors and exact Collatz ratios. Floating-point iteration only proposes the vectors. The comparisons themselves use rational arithmetic:
\[
 \frac{2703542684891}{762877412961}\le \rho_5
 <3.543875646290,
 \qquad
 \max_{\pi\ne{\rm par}}\rho_\pi
 \le\frac{831945314801}{244687494744}
 <3.400032010919;
\tag{2}
\]
\[
 \frac{38857515261}{10824737524}
 \le\rho_6\le
 \frac{46131803631}{12851173381},
 \qquad
 \max_{\pi\ne{\rm par}}\rho_\pi
 \le\frac{141165131866}{40947781273}
 <3.447442754587.
\tag{3}
\]
Thus \(3.589695840185<\rho_6<3.589695840476\). At both heights, the parity lower bound exceeds every other partition's upper bound.

## 2. Exact scope of the compressed presentation

The engine uses positive forbidden patterns, normalized by their required black cells. These patterns characterize the bi-infinite sea shift exactly. A residual constraint expires within \(L=2W_h\) steps, so the residual state at any position of a bi-infinite word is determined by its last \(L\) letters. Conversely, a bi-infinite labeled path supplies all its length-\(L\) histories. These bounded-window maps identify the recurrent edge shifts of the compressed and full-history presentations.

In particular, the exhaustive scan determines the recurrent components, periods, and spectral radii needed for the analytical count theorem. Parallel edges with different row labels count separately in the adjacency matrix.

The compressed automaton does not give the exact finite-board counting series when every state is accepted. A pattern's required black cells can lie inside a finite board while its colliding rectangles share a white point beyond an end. For example, at height six the parity word
\[
 (1,1,6,1,4,6,4)
\]
is valid on its finite board but fails the sparse pattern test. All six one-column extensions on its left are invalid. Such finite-end effects do not change the bi-infinite shift or its recurrent components.

All boundary vectors and insertion matrices used below therefore come from the exact end-aware full-history construction in [exact_counting_scc_and_resolvent.md](../counting_followup/exact_counting_scc_and_resolvent.md). No finite-board boundary constant is extracted from the sparse automaton.

## 3. From spectral dominance to maximum-blackout counts

Write \(q_h=\lfloor h^2/4\rfloor\). For each partition, the unique recurrent component contains the boundary constants. The analytical isolated-double construction gives a positive insertion bridge for every double edge, as proved in [insertion_adjacent_component.md](../counting_followup/insertion_adjacent_component.md). Period one makes its Perron pole simple.

Parity equality words contain no hidden rectangles. In the marked-resolvent expansion, a term using every double once has \(q_h+1\) sea resolvents. Taking the Perron term in each factor gives a pole of order \(q_h+1\), with positive coefficient. Every other exponential base has strictly smaller modulus, because the recurrent component is primitive and unique. Equivalently, the remaining generating-function poles lie farther from the origin.

For either \(h=5\) or \(h=6\), there is a real polynomial \(P_h\) of degree \(q_h\), with positive leading coefficient, and a number \(\theta_h<\rho_h\), such that
\[
 a_h(m)=\rho_h^mP_h(m)+O(\theta_h^m).
\tag{4}
\]
To obtain (4), choose \(\theta_h\) strictly larger than the moduli of all subdominant bases. This absorbs their polynomial factors. The computation does not certify a numerical value of \(\theta_h\).

Using the exact end-aware Perron boundary factor \(B_h\) and insertion factors \(\kappa_e\), the leading coefficient is
\[
 C_h=B_h\prod_{e\in E_{\rm par}}\kappa_e>0.
\tag{5}
\]
Each edge order contributes \(1/q_h!\) times this product, and there are \(q_h!\) orders. This explains the absence of a factorial in (5). No numerical value of \(C_h\) is certified here.

The nonparity contribution is bounded by
\[
 O\!\left(m^6(3.400032010919)^m\right)\quad(h=5),
 \qquad
 O\!\left(m^9(3.447442754587)^m\right)\quad(h=6).
\tag{6}
\]
The nonparity partitions can have a hidden unit diamond. The exact hidden-aware resolvent theorem still bounds their dominant pole order by \(q_h+1\). They cannot affect (4) because of (2) and (3).

The same rank-one expansion gives the distributional conclusions at both heights. A uniformly selected maximum blackout uses parity with probability tending to one. Its \(q_h\) double columns, divided by \(m\), converge to the order statistics of \(q_h\) independent uniform points in \([0,1]\). The edge-label order is asymptotically uniform over all \(q_h!\) orders and independent of these positions. Configurations with a bounded gap between doubles contribute only \(O(m^{q_h-1}\rho_h^m)\), so they do not change this limit.

## 4. Reproduction and validation

[run_partitions.py](run_partitions.py) enumerates all partitions using [sea_sparse_automaton.py](sea_sparse_automaton.py). The complete graph statistics and rational bounds are in [partition_graphs_h5.json](partition_graphs_h5.json) and [partition_graphs_h6.json](partition_graphs_h6.json).

The original scans compared finite words against an independent geometric presentation checker. At height five, all 15,625 length-six words were checked for each partition. At height six, all 7,776 length-five words were checked for each partition. Each partition also had 40 longer walk and mutation checks. These sampled comparisons all agreed. Agreement on these samples does not imply finite-language equivalence.

The corrected runner asserts the general sound direction: sparse acceptance implies finite geometric validity. It records any finite valid words pruned by the stronger sparse pattern test.

[validate_partition_periods.py](validate_partition_periods.py) separately checks every period of lengths one through four against direct geometry. For a period of length \(n\), a window of length \(n+2W_h\) contains every possible full-support collision in every phase. All 780 periods per five-row partition and 1,554 periods per six-row partition agree, for 23,340 periodic comparisons. The script also verifies the finite-boundary example in Section 2. Results are in [partition_periodic_validation.json](partition_periodic_validation.json).

The height-five scan completed in 13.47 seconds and the height-six scan in 110.91 seconds. Each used a collective 120-second cap and a 512 MB per-process cap. Every graph completed, and no partition remained unresolved.
