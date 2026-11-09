# Independent audit of the new mixed-family savings

9 November 2026. Both [low_high_mixed_power_saving.md](low_high_mixed_power_saving.md) and [same_sea_global_first_moment.md](same_sea_global_first_moment.md) pass review. Their conclusions remain geometric incidence estimates for specified pair roles, not a complete quadratic-width placement theorem.

## Low/high roles

With both label rows strictly between the two sea levels, the midpoint equation gives a=2d-s-2mp and mp<d. Thus p or m is at most sqrt(d). The small-p case is bounded by the sum-of-two-squares representation count. In the small-m case the completed-square norm is exactly 16[m²s²+k²d(d-s)], which is strictly positive. There is no zero-norm Pell degeneration.

The uniform quadratic-norm lemma is valid. The maximal quadratic order contains X+Y sqrt(A), including when A has square factors. An ideal of fixed norm |N| has at most tau(|N|) possibilities, by the split/inert/ramified prime cases. Generators of one principal ideal differ by units. Polynomial bounds on both embeddings and their nonzero integral product bound each absolute embedding between reciprocal-polynomial and polynomial scales. The integral trace and norm give a uniform multiplicative gap of at least the golden ratio between distinct positive absolute unit values. Hence only O(log H) associates occur. Imaginary units have at most six possibilities. These facts agree with the primary expositions [Factoring in quadratic fields](https://kconrad.math.uconn.edu/blurbs/gradnumthy/quadraticgrad.pdf) and [Ideal factorization](https://kconrad.math.uconn.edu/blurbs/gradnumthy/idealfactor.pdf).

When the quadratic coefficient vanishes, k=2m<=2 sqrt(d), B is of order kd, and |v|<=3d. The square-root residue bound gives at most d^(o(1)) sqrt(B) possibilities, since a length-O(d) interval meets each residue class only O(1) times. This is d^(3/4+o(1)). Multiplication by the divisor count does not change the exponent.

The resulting total incidence is O(d^(7/4+epsilon)). Removing diagonal rows above degree d^(7/8) removes O(d^(7/8+epsilon)) rows. Adding unused label partners gives O(h^(15/8+epsilon)) labels or incident events. The cited exceptional-label construction can absorb that number below h² after fixing small exponents, with its order-h² collars retained. This reduction applies only to the stated low/high family.

## Same-sea global moment

For a positive connector, v²=k²p²-4lp(a+lp)>=0 forces l<k/2. Combining this with lp<=h and the squarefree divisibility gives the minimum of the two scale bounds with no additive error.

Writing p=2^e u v² yields F_k(X)<=C sqrt(X) sigma_{-1/2}(k). Partial summation then bounds the tail weighted by 1/p. Splitting at X=h/k produces O(sqrt(kh) sigma_{-1/2}(k)), and summing k|a gives O(sqrt(ah) sigma_{-1/2}(a)²).

The bounded-margin negative connectors satisfy |lp|<=M because a common white corner has height lp relative to the sea. Only O_M(1) such pairs occur. Their divisor factor is harmless. For every fixed positive power, sigma_{-1/2}(a) has bounded mean: its nonnegative convolution with the Möbius function has Euler factors 1+O(p^(-3/2)) at exponent one. Summation gives the asserted O(h²) global incidence and bounded moments of the fixed-side arithmetic weight.

The result remains asymmetric. An average over diagonal endpoints does not supply a uniform diagonal bound, a restricted-class estimate, or a simultaneous placement satisfying the other support families.

## The subsequent square-root upgrades

Section 7 of the low/high note correctly removes the zero-quadratic-coefficient case in the intended oriented 0/5 profile. There d=g, s=3g, and a=0 modulo seven. If k=2m, then kp=2d-s-a=-g modulo seven, so the circle norm would give v²=3g² modulo seven. Since g is nonzero and 3 is a nonsquare, this is impossible. The restriction is specific to that normalized role; it is not asserted for every all-zero block.

The later [same_sea_mixed_power_saving.md](same_sea_mixed_power_saving.md) also passes. For a positive connector, k>2l makes A=k²−4l² strictly positive. Completing the square gives the nonzero norm 16l²a². Split p or l at sqrt(h), using the circle count in the first range and the reviewed uniform norm lemma in the second. There is no zero-coefficient branch. Negative connectors at a bounded boundary margin have |lp|=O(1) and contribute only a divisor factor.

Both intended roles consequently have fixed-side incidence O(h^(1/2+epsilon)) and global incidence O(h^(3/2+epsilon)). Removing diagonal rows above degree h^(3/4) leaves O(h^(3/4+epsilon)) exceptional rows, and the unused label partners give O(h^(7/4+epsilon)) exceptional labels or incident pair events. These remain reductions for the specified families, with no new complete-threshold claim.

## Remaining costs and the finite valuation filter

The scope in [refined_scaffold_remaining_costs.md](refined_scaffold_remaining_costs.md) is correct. Hypotenuse containment bounds the vertical-parity pair incidence by the number of integer right triangles of hypotenuse at most h, which is O(h log h) by Euclid's parametrization. The unused endpoint gives O(h² log h) per fixed label. Without a restricted-class weight this does not remove the final logarithm after summing classes. Complete hole occupation, equal-residue opposite-parity triangles, higher-arity moments, and collar costs remain independent requirements.

The local exclusion in [equal_residue_triangle_valuation_filter.md](equal_residue_triangle_valuation_filter.md) also passes. Opposite-parity endpoint differences have 7-adic valuation exactly one. The low-row difference has valuation one, whereas the high/filler difference has valuation zero. Their products therefore have valuation two or one; a center difference divisible by 343 makes the horizontal product have valuation at least three. The filler case increases that lower bound to four. The choice of an odd low row among 1 through 98 always leaves at least five admissible residues. This is a finite enlargement of the profile parameters. It neither covers equal endpoint residues modulo 49 nor preserves full occupation, as the note explicitly states.
