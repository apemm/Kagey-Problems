# Independent audit of adaptive local phase sparsity

9 November 2026. [adaptive_local_phase_sparsity.md](adaptive_local_phase_sparsity.md) passes independent review. Its fixed aligned-block sparsity cap is sufficient for the exact protected-reference comparison; no separation hypothesis on errors is needed.

The density majorant Q_i is consistent with the chosen radius. If a block j is within the geometric neighborhood of a root in block i, the cutoff inequality makes h[K/(1+|i-j|)]⁴ strictly larger than Q_i. Consequently q_j>Q_i would contradict the definition of Q_i. There are O(R_i) relevant blocks, each containing at most Q_i errors. The deleted-root mean is therefore O((Q_i/h)R_i³), uniformly small. All rounding estimates remain uniform because an occupied block has Q_i>=1 and R_i<=C h^(1/4).

For conditional dependence, group roots by dyadic Q. A fixed free cell can see only O((h/Q)^(1/4)) blocks in that group, each with at most 2Q roots. The fixed completion-column count gives O((Q/h)^(1/4)) one-assignment mass, and the two-assignment locus bound gives O((Q/h)^(3/4)). Summation over density levels is geometric. It introduces no log h loss, even when the number of occupied blocks is unbounded.

The weighted maximal inequality is valid. If L_i*<L_i/2, a witnessing j has L_i>=max(2L_j,8 log((d+1)/K)). Since exp(-u)u² decreases above 2, the total weight charged to j is bounded by the sum of this decreasing envelope. Splitting distances at K exp(L_j/4) gives O(K h exp(-7L_j/4)L_j²). Relative to q_j L_j² this is O(K epsilon_0^(3/4)). Every bad i is assigned to one witness, so summing over j is legitimate and bounds the entire bad mass by half the total after fixing epsilon_0. The factor 1/8 in the stated inequality follows.

The local-lemma criterion and conditional lower-probability bound use the same unchanged old-bulk family as the uniform local proof. Restoring deleted old bulk costs O(|S|log⁴h/h), uniformly absorbed because every L_i is bounded below by the fixed log(1/epsilon_0). This produces an exact ratio with Z_X, not merely an absolute product-space bound.

The block entropy sum is also uniform. For q<=epsilon_0 h, the binomial entropy is O(q log(h/q)), whereas the retained penalty is c q log²(h/q). Taking epsilon_0 small makes the latter dominate. The function q log²(h/q) increases on the entire allowed range, with minimum log²h. Summing all q and then all aligned blocks gives the stated exp(h^(-1) exp(-c log²h)) growth correction. Fixed-height end collars, rounded to the phase period, affect only the multiplicative constant.

The theorem concerns errors relative to one protected base law. A later domain or all-profile argument needs its own interface treatment; that extension is not implicit in this audit.
