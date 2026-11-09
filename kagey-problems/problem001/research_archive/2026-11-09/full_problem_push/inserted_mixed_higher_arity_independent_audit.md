# Independent audit of inserted mixed-support degrees

9 November 2026. [inserted_mixed_higher_arity_bounds.md](inserted_mixed_higher_arity_bounds.md) passes review. Vertical black sides remain assigned to the separate virtual parity-rival family throughout.

For a crossed fixed pair A=(0,0), C=(0,q), set B=(x,b), D=(z,d), s=x−z, and t=d−q−b. Expanding equal norms and perpendicularity gives exactly s²+t²=4qb and xs=b(t+2q). If s=0, either b=t=0, in which case the proposed black and white diagonals coincide, or t=−2q and b=q, in which case the side connector is zero. These are the two excluded degeneracies.

For s nonzero, strip containment gives |s|,|t|<=2(h−1). Multiplying the second equation by 4q and substituting the first yields s dividing t²(t+2q). For each of the O(h) nonexceptional t values, the nonzero right side has polynomial size and therefore only h^(o(1)) signed divisors. The values t=0 and t=−2q each leave only O(h) choices of s. The equations then determine b,x,z,d uniquely. Thus the same-column crossed codegree is O_epsilon(h^(1+epsilon)).

If a fixed pair is one complete black pair, its equal-norm counterpart has h^(o(1)) orientations. A nonvertical side determines its perpendicular connector from its bounded vertical coordinate, leaving O(h) choices. Together with the previously audited distinct-column crossed case, this supplies every required two-point role. The exclusion of vertical sides is necessary here, since their horizontal connectors would not be bounded by the strip alone.

For one fixed point and an oblique side, the primitive side and connector representation gives |kv|<=h−1 and |lu|<=h−1, hence O(h² log²h) scale/direction choices. The alternative circle representation contributes only h^(o(1)), and the chosen point fixes the translation. Horizontal sides are bounded instead by (u−r)(u+r)=s² with nonzero |s|<=h−1, followed by O(h) vertical connectors. Coincident black columns do not increase either estimate.

A four-label support uses one endpoint of the fixed label and three unused mates, giving O(h^(2+epsilon))*h³=O(h^(5+epsilon)). A three-label support has distribution 2+1+1. If the fixed label is repeated, the two-point bound and two unused mates give O(h^(1+epsilon))*h². If another label is repeated, the one-point geometry already fixes both of its endpoints, leaving only one unused mate, for O(h^(2+epsilon))*h. These are O(h^(3+epsilon)) in both cases. Endpoint and role choices cost only a constant.

When a vertical side is the two-point owner label, its row pair belongs to final F; the remaining diagonal is already a two-label virtual vertical rival. Treating the owner as an additional label would duplicate that event. The note correctly removes this case before asserting the higher-arity bounds.

These estimates put the stated mixed families below their permutation scales n² and n³ when n is of order h². They do not remove the separate three-point right-angle load, vertical rivals, restored singleton collisions, or end interactions, and imply no new complete-threshold bound by themselves.
