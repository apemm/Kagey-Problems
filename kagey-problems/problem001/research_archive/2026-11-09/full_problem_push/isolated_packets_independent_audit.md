# Independent audit of isolated phase packets

9 November 2026. [isolated_short_phase_packets.md](isolated_short_phase_packets.md) passes independent review, including its exact partition-function comparison and the separated-packet activity bound.

The far-black construction is valid. With B=Aℓ(1+log h) and R of order h/B, each individual horizontal leg is much larger than B. For fixed direction and one scale, excluding the near-cancellation of the two horizontal legs removes O(B/b+1) values of the other scale, a uniformly small fraction after fixing the numerical constant in R. All three required black columns are then outside the packet and at distance at least B from it. The coordinate increments are multiples of four, so the same construction works for every protected row/phase pair.

The remaining family has order h³log²R geometries per flipped completion column, including its eligible completion rows. Multiplicity is bounded because the three black corners determine the completion. Its probability mean is therefore at least a constant times log²(h/ℓ), uniformly for ℓ≤h^(1−δ) once h is sufficiently large depending on δ.

The interval divisor estimate is the main improvement over a bound based only on the number of roots. The distances from a free point to a packet form an interval starting at D≥B. Hyperbola summation gives total one-cell conditional mass at most Cℓ log h/B+C/√B+O(ℓh^(−1+η)). Choosing A first and η<δ makes it small. Two fixed black cells and a prescribed completion column give O(1) tilted completions: a vertical perpendicular locus would require a horizontal side and hence an axis rectangle; a horizontal diagonal uses the circle locus. Thus the two-cell conditional contribution is O(ℓ/h).

The old protected bulk can be retained when its required black columns avoid S. Its joint product law is unchanged, and its compatible extensions through the three assignments of a root event have vanishing total weight. Raw incidence establishes the joint local lemma; the conditional lower-probability estimate is then applied to the rooted events. Restoring the old bulk costs exp(O(|S|log⁴h/h)), and the possible alphabet-size ratio costs exp(O(|S|/h)). Both are absorbed by the retained root mean. This proves a ratio against the exact normalized-support partition function, without an extensive bulk approximation error.

For packets separated by at least 3L, the rooted neighborhoods are disjoint. The old bulk remains controlled by the same incident and extension estimates. For a packet of length ℓ, summing nonempty subsets gives activity (1+exp(−c log²(h/ℓ)))^ℓ−1. Summing over all polynomially many permitted lengths still gives exp(−c_δ log²h). Allowing a packet to start at every column overcounts the permitted descriptions and yields the stated entropy upper bound.

The end collars and the separation hypothesis are essential to the written argument. It does not handle interacting packets, packets of width comparable to h, or all phases of a full recurrent component.

## Relative dilution and near-linear widths

The subsequent [relatively_dilute_phase_packets.md](relatively_dilute_phase_packets.md) also passes review. It replaces the preceding full-memory isolation hypothesis by disjoint packet expansions of radius g_hℓ_i, where g_h=U_hΛ³ and U_h=exp(C log h/log log h) is an absolute divisor majorant. It permits widths up to h/(U_hΛ²). This extension still imposes relative separation; it is not an arbitrary interacting-packet theorem.

Delete every new rooted event whose black columns enter any smaller buffer V_i of radius AΛℓ_i before computing incidence. At a free point there is at most one nearby expanded packet. The interval divisor estimate handles that packet. For all others, integration of 1/d over their disjoint central half-intervals gives Σℓ_i/D_i≤CΛ/g_h. The diagonal part has the same bound after splitting at D_i=h. The kernel therefore gives a uniform O(1/Λ²) far-packet contribution.

At a root in I_i, all other expanded packets are far. Their smaller buffers remove at most C A T_hΛ²/g_h=O(1/Λ) mean. A buffer can intersect the support neighborhood even if its central interval starts just beyond distance L; the packing bound should be applied with cutoff 2L in this step. Its proof is unchanged, with the central halves contained within distance 3L.

The total completion locus through two fixed black points has O(h) points across all packets. A fixed small independent marking rate controls this O(1) conditional mass; no packet-count factor is needed. The absolute divisor majorant makes the near-packet diagonal contribution at most 1/Λ². The exact bulk restoration and alphabet-size comparison are therefore the same as in the isolated proof.

The minimum retained penalty is a constant times log²h/(log log h)² per flipped column. This dominates the logarithm of the polynomial number of packet lengths and starts. Summing all admissible descriptions yields the stated relative entropy factor 1+exp(−c log²h/(log log h)²). The conclusion is against the exact protected partition function and retains the fixed-final-F, end-collar, width-cap, and relative-separation hypotheses.
