# Independent audit of joint row and wall pressure

9 November 2026. The joint-family version of [separated_domain_partition_comparison.md](separated_domain_partition_comparison.md) passes independent review. It proves the stated O(log²h) residual row distance for its separated-domain language, with arbitrarily clustered phase errors at the specified density. It does not classify all phases in a near-maximal component.

The two event families can be combined directly. After fixing three black assignments, compatible row-root events sharing one or two assignments have total conditional mass O(qR log R+q). The corresponding marked wall mass is O(b₀). The raw incident bounds have the same orders. The one-cell wall estimate is O(h² log h); the two-cell estimate is O(h), from the nonhorizontal perpendicular-line and circle completion loci. These estimates are uniform for a fixed event from either family.

There is no overlooked three-assignment overlap between the families. Three noncollinear right-angle corners determine a unique rectangle and completion. Row-root completions lie in the changed row set E, while all four rows of a retained wall geometry avoid E. Independent marks cause no additional geometric dependency. The standard conditional lower-probability argument therefore applies jointly after choosing b₀ small and then q≤δ₀ sufficiently small.

The adaptive row-family span sum gives O(rR)≤O(√(rh)) loss per domain. A marked wall supplies a positive constant times h. Choosing δ₀ after the wall-mark constant makes the former at most half the latter. This is the essential improvement over multiplying protected finite-domain partition functions: the proof pays the actual row-root endpoint loss, not a bulk interface bound.

Deleting all events incident with an error column costs O(|S|qR log R) for row roots and O(|S|) for marked wall roots. The wall neighborhoods are disjoint because the internal domains have length at least C₀h. The two external endpoints contribute only a fixed-height factor. These estimates remain valid for clustered errors and even when the displayed mean lower bound becomes negative.

The resulting fixed-profile estimate has exponent −aP_h(r)m−chJ+C|S| relative to the absolute alphabet bound ceil(h/2)^m. Summing domain descriptions costs only O(exp(−ch)) in pressure; summing error sets costs H₂(σ)+Cσ. For r≥K(1+log h)², monotonicity of q log²(1/q) gives P_h(r)≥cK(1+log h)⁴/h. This exceeds the known protected entropy deficit for sufficiently large K. The allowed error density σ≤bP_h(r)/log(e/P_h(r)) pays its entropy uniformly.

Section 4 of [adaptive_row_root_pressure.md](adaptive_row_root_pressure.md) also passes: the same deletion estimate gives an exact one-global-phase comparison with error cost C|S| and allowance σ≤bP_h(r)/log(e/P_h(r)). Its reference is the protected partition function, whereas the joint wall proof above uses the absolute product space. The two statements keep these references distinct.
