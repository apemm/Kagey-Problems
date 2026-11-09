# Independent audit of the rectangle inverse arguments

9 November 2026. The periodic amplification, bounded-period entropy gap, and protected-row arbitrary-phase inverse arguments have been checked independently.

## Periodic amplification

The proof in [Periodic rectangle amplification](periodic_rectangle_amplification.md) is sound. Möbius inversion gives the stated uniform count in a prescribed primitive residue pair. Its error is small on the chosen range \(R\ge CP^2(\log h)^2\). For \(P\le h^{1/16}\), there are logarithmically many disjoint admissible dyadic ranges before \(R=h^{1/4}\).

The primitive direction and the two positive side scales uniquely specify the rectangle from its lowest vertex. The residue conditions reproduce the original three-selected-corner pattern exactly, and all selected translates remain inside the board. Repeated-column rectangles contribute only \(O(h^3\log h)\), which is negligible uniformly in the stated period range.

The subsequent [bounded-period entropy gap](bounded_period_entropy_gap.md) uses the container theorem correctly. Its increasing edge-count family satisfies both the density and minimum-size conditions. Intersecting a container with the prescribed full box removes \(\Omega(P^{-6}h^2)\) vertices. In the transversal count, the \(h^j\) choices of fingerprint rows cancel the \(j\) omitted coordinates in the main product; there is no hidden factor exponential in \(h\log h\). The within-partition dominance consequence is correctly restricted to a fixed period bound.

## Protected row partition, arbitrary column phase

The substantive proof in [Protected-row aggregate inverse](protected_row_aggregate_inverse.md) is sound. Its crucial uniformity points are:

* Every lifted-matrix XOR failure comes from a physical failure with multiplicity at most \(K/R+1\). The hypothesis therefore gives a uniformly \(o(K^2)\) rank-one repair for each lifted matrix.
* Exact overlap for every shift \(s\le K/(8R)\) gives small increment error separately for each shift. A common good starting index makes the corresponding increment bits exactly additive. The proof never iterates a single approximate-period estimate.
* Summing all short-shift discrepancies bounds the cut of a bounded-radius power of each residue chain. The actual chains have lengths between \(3S\) and \(9S\), for sufficiently large height. Under these two bounds, the displayed block proof gives a cut of at least \(cS\) times the minority count, and hence a uniform \(o(K)\) repair of each factor.
* The repaired factors define an exact period-\(2ab\) function. Every point in the stated central physical interval has \(\Omega(K/R)\) representations, converting matrix error to \(o(h)\) word error without a factor growing with \(a,b\).
* The overlapping local intervals have length comparable with \(h\) for each fixed \(\eta\). Since the exact period is \(o(h)\), their approximants can be compared on complete periods and merged with only \(o_\eta(h)\) error.
* The sieve supplies a positive proportion of primitive neighboring direction quadruples. Their periods have gcd two and lcm bounded by \(2a(a+2)b(b+2)=O(R^4)=o(h)\). The Chinese-remainder comparison therefore remains uniform as the directions grow.

One wording correction was requested during review: a chain of length merely at most \(9S\) need not satisfy the displayed \(cSm\) cut bound when its length is much smaller than \(S\). The application has the needed lower bound \(3S\), so stating that bound fixes the issue without changing the proof or conclusion.

The resulting inverse theorem concerns a protected row partition and arbitrary phase. It does not classify arbitrary row partitions or prove component connectivity.

## Entropy concentration in a protected partition

The argument in [Protected-partition entropy stability](protected_partition_entropy_stability.md) passes an independent audit. Purification and the inverse theorem imply the stated quantitative compactness form by contradiction. Its constants may depend on the desired distance, and the container theorem is applied only after those constants are fixed.

For a container close to a protected product box, weighting each choice outside that box by two gives the factor \(2^{j-\varepsilon h}\) after a fingerprint of size \(j\) is fixed. Arithmetic--geometric mean then gives the claimed root bound \(2^{-\varepsilon}(1/2+2\theta)h+o(h)\). This counts every far phase simultaneously. There is no additional phase-choice factor.

Summing the fingerprints introduces only \(\exp(o(h))\) after their \(h^j\) row choices cancel the missing \(j\) coordinates. The small-container bound has the same cancellation. Choosing \(\theta\) first and then absorbing the fingerprint error gives a fixed entropy gap.

For the block-density consequence, ignoring compatibility between consecutive blocks is a valid upper bound, and the \(2^{\lfloor m/h\rfloor}\) status choices contribute only \(2^{1/h}\) to the growth rate. The stationary-measure conclusion follows directly from the entropy of the far/nonfar indicator and the two conditional support sizes. It proves concentration of individual height-length blocks, not agreement of all blocks with one global phase.

The finite-end interpretation retains the fixed final row-pair set \(F\) used by the sea model. An isolated singleton board with no such external axis owners should not be substituted for that model.

The later overlapping-window domain statement also passes. Distinct protected laws differ on at least half an interval, up to one endpoint, so adjacent good windows must choose the same global law. Summing their errors over blocks of length \(\lfloor h/4\rfloor\) gives the factor five. Bad windows account for at most their total block length and at most one additional domain boundary each. Stationarity and Markov's inequality give the stated high-probability conclusion without an ergodicity assumption. The separate phase-entropy estimate follows by counting Hamming balls around the four protected laws and then letting their radius tend to zero.

## Bounded-period phase with arbitrary row partition

The proof in [Bounded-phase arbitrary-row inverse](bounded_phase_arbitrary_row_inverse.md) passes. Restricting both side scales to multiples of the fixed phase period makes all four column phases equal. Since a nonconstant periodic phase supplies both bit values among horizontal translates, every odd row-XOR failure produces a positive fixed proportion of three-corner placements.

The existing lifted XOR repair applies separately to each row residue modulo that period. The same four good directions work for every residue, because their bad counts are bounded by the total count. It gives an \(o(h)\) repair to a \(2P\)-periodic row word. The finite collection of periodic approximants then permits the earlier amplification theorem to be used with no circular dependence between an edit error and a growing period.

A finite-height clarification was requested: a row word balanced over its period need not be exactly balanced at an arbitrary endpoint. Applying the periodic theorem on the largest square whose side is divisible by \(2P\) loses only \(O(P)\) rows and columns and supplies its literal balanced-height hypothesis.

The subsequent uniform entropy gap follows by contradiction over the finite family of bounded-period phases, followed by the already audited robust profile-neighborhood count. The result remains restricted to a fixed period bound.

The robust-neighborhood argument in Sections 4--5 of [Bounded-period entropy gap](bounded_period_entropy_gap.md) also passes. A change in \(D\) profile columns changes at most \(Dh\) vertices, so the maximum-degree estimate controls the loss of hyperedges. The good/bad block estimate and the global binary-entropy cost of choosing changed columns give the stated \(P^{-6}/\log(P+2)\) neighborhood scale. Transposition handles nonconstant protected phases with arbitrary rows; the constant-phase inverse handles the remaining case.

## Periodic row laws with arbitrary phases

Sections 5--6 of [Bounded-phase arbitrary-row inverse](bounded_phase_arbitrary_row_inverse.md) also pass. The intermediate fiber repair never uses balance. After transposition, the original balanced periodic row word is a nonconstant periodic phase, and the arbitrary column word is repaired to period \(2P\). Transposing back restores the balanced periodic row hypothesis before invoking finite periodic amplification.

Transposition preserves the family of comparable primitive directions, up to reversing the orientation of a side. Thus the lower test density can be asserted in that same restricted family. Its uniform per-row edit bound justifies the robustness under a sufficiently small fraction of row changes.

For a fixed period bound there are only finitely many row laws. The inverse contradiction therefore supplies a common positive test density for every nonprotected one and every arbitrary phase. Uniform container purification and the fingerprint-aware transversal count give the stated full sea entropy gap. This does not constrain row laws whose period grows with height.
