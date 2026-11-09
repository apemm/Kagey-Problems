# Independent audit of mixed-support residue averages

9 November 2026. Both [uniform_circle_scale_valuation.md](uniform_circle_scale_valuation.md) and [uniform_connector_base_residues.md](uniform_connector_base_residues.md) pass independent review. These are partial arithmetic inputs to the leading mixed-support ratios, not a proof of those ratios.

For the scale average, four times the root count of −1 modulo an odd integer is its primitive sum-of-two-squares representation count. Opposite-parity disk counting and odd Möbius inversion therefore give the coefficient 1/π in (5). The hyperbola split gives the stated K^(3/4) log K error without a sharp circle estimate.

At a split prime p^ν dividing N, the ratio of local generating functions is 1−[2ν/(ν+1)]x/(1+x). This gives the alternating correction exactly, including the prime-two and inert-prime cases. Convolution gives the linear term B D_N(1)+D_N′(1)/π with the displayed positive derivative sign. The logarithmic tail is controlled by K^(−1/4) times the absolute 3/4-moment. Splitting the prime divisors at log(3N) gives the lower bound for D_N(1) and the O(log log N) logarithmic derivative. Choosing a fixed sufficiently small exponent in the subpower bound makes the relative error uniform when N is polynomially bounded and K is polynomially long.

The exact identity r₂(4k²N)=r₂(k²N) then gives the weights 1/2, 1/4, 1/4. Differences of the uniform summatory formula give dyadic intervals, and partial summation gives the stated fixed bounded-variation weights away from zero. No conclusion is being drawn for all short scale ranges.

For connector residues, the six-point vertical span is the span of a fixed interval and one interval translated by al. Its truncated translation count is unimodal and has variation at most 2h. Sampling a residue class modulo four therefore costs O(h) per pair (U,V). The nonzero-connector condition and the distinct-black-column conditions remove only O(1) connector values. Degenerate fixed diagonal pairs are removed before this argument.

The primitive dyadic quadratic-divisor estimate gives O(h² log³h) admissible (U,V) pairs after summing the scale bound. Thus connector errors total O(h³ log³h). Counting vertical-base residues costs O(1) per triple (U,V,l), or O(h² log⁴h) overall. Both bounds hold after restricting to any subset of (U,V) independent of connector and base translation. The qualification is important: the error is uniform in an absolute sense, and need not be small relative to a lower-order selected subset.

Primitive parity-type weights and the nearly horizontal short-arc contribution remain unresolved. These two audited inputs alone do not establish the candidate ratios 13/16 and 5/4 or an ordering of the full component entropies.

## Short-scale extension

The subsequent [mixed_short_scale_truncation.md](mixed_short_scale_truncation.md) also passes review. Splitting the dyadic vertical direction coordinate B at h^(1−δ) gives an absolute short-scale bound O(h³Λ³+δ²h³Λ⁴), uniformly for 0<δ≤1/2. In the lower range the B sum is geometric; in the upper range the sum of log(2h/B) is quadratic in δ log h. Thus the bound is small at leading scale by taking h to infinity before δ to zero.

In the very vertical range, summing connectors replaces the translation weight by (h−kb)²/a with an O(h) error per (U,V). The already audited pair count makes the total error O(h³Λ³). The uniform scale mean can be partially summed on every long dyadic interval using the weight's supremum and total variation as an absolute majorant. No positive lower bound on each interval's weighted integral is necessary. Summing these majorants costs O(h³Λ⁴). This extends the valuation weights to the complete leading vertical contribution, before the explicit integrality filter, with absolute error o(h³log⁴h).

The short-scale issue is therefore resolved for that use of the vertical reduction. The primitive parity-type weights and the nearly horizontal short arcs are still not proved by these arguments.
