# Appendix A and family-estimate audit

Reviewed November 1, 2026. Files read in full: `app_erw_bounds.tex`, `app_erw_profile.tex`, and `or_family_proofs.tex`. The first-flip, urn, and conditional-unimodality statements in the main text were checked as dependencies.

## Result and revisions

No gap was found in the center comparison or the family estimates. Two domain clarifications were implemented:

1. State explicitly that the starting count `b` in the Polya hitting-probability lemma is an integer.
2. In the tail proof, extend the vertex sums to all nonroot vertices and use upper bounds for the size sums. The original equalities omitted the truncation at family size `t - 1`; the stated bound already held, including when `z > t`.

The center lower bound was also strengthened using Jensen's inequality on the same first-flip weights. The new factor is `(1 - epsilon)^(2 - 12/(N + 4))`, which improves `1 - 2 epsilon` throughout the stated range and is exact at `N = 2`. This follows from the already established mean of the weights and requires no new input.

## Mathematical checks

- The beta-binomial hitting probability, conditioned transition `(h-b)/(N-s)`, and backward comparison have matching state domains. At the edge of the feasible set the zero continuation has the required sign.
- The digamma bound gives the stated derivative of the logarithmic hitting probability. The cancellation `2(kappa-alpha)/(1+2 alpha) = kappa` is exact. The remaining positive terms are bounded by `16 kappa W/(3s)` and the negative term by `-18 kappa W/[s(1+2 alpha)]`. Their sum is negative for the stated reversal range.
- The center-bound series truncation and constant budget are consistent: the proof only needs the series below `(5200 - 3)/50.4`, leaving room above its stated enclosure.
- The first-family argument uses independent whole chains, as constructed in the main text. The path `d - Y_d + Z_(N-d)` moves by at most one and hits the target before `m + Y_(2m)`. The index remains admissible because `2m + j <= N` in the chosen early-flip range.
- The late-flip estimate uses `floor(N/8) >= (N-1)/9` for `N >= 64`. Its geometric tail and the conversion to `20 m exp(-m/9)` are valid.
- The mode proof's five errors sum to less than one half. Its final constant is `202 * 19 * 4 = 15352`, below `A_0 = 15400`. The sufficient loading condition implies the local-lower-bound domain.

## Independent computation

Ran `check_family_bounds.py` with Python's standard library. It checks hitting probabilities through backward recursions rather than by substituting the manuscript's beta formula.

| Check | Scope | Result |
| --- | --- | --- |
| Lower Polya comparison | 14,664 exact rational comparisons; even `N <= 24`, four reversal probabilities, three allowed comparison weights at each time | Passed |
| Jensen center lower bound | 48 checks against exact rational backward probabilities; even `N <= 24` and four reversal probabilities | Passed |
| Upper one-step factor | 21,816 floating-point checks; `N` through 128 and reversal probabilities through 0.24 | Passed; largest bound excess `-1.5706605150772596e-6` |
| Family-size identities | 3,081 pairs of exact rational identities, `2 <= N <= 79` | Passed |

These computations stress-test the arguments on a finite grid. They do not replace the general proofs or the separate Lean checks.

This review does not cover the remaining arXiv-only Sections S1–S5 in full. No claim of a full-paper formal verification is made here.

## Independent check of the final strengthening

Also read the revised proof of `thm:two-modes`, the new `thm:two-modes-near-one` proof, and the weak-convergence transfer in `app_erw_bulk.tex`. These checks are analytic, not new kernel checks.

**Curvature classification.** The argument is valid. A positive-half-line sign pattern of length `k` for the even function `g_a''` reflects to a pattern of length `2k - 1`. The five-block bound therefore permits at most three such blocks. The first nonconstant even Taylor coefficient fixes the sign near zero. The last sign is positive: eventual nonpositive curvature would make `g_a'` nonincreasing with limit zero, hence nonnegative, contradicting a positive density tending to zero. This forces the patterns `(-,+)` or `(+,-,+)`. Analyticity rules out intervals of zero curvature, giving strict concavity/convexity and exactly the stated number of inflection points. Isolated zeros without a sign change are still allowed. Integrating curvature from `g_a'(0)=0` and back from `g_a'(+infinity)=0` gives `g_a'(d_1)>0>g_a'(d_2)`, placing the positive mode strictly between the two positive inflection points.

**Two modes for `a >= 4/5`.** The Khinchine representation yields the necessary kurtosis bound `E L^4 / (E L^2)^2 >= 9/5` for case (a). The exact moment recursion gives the displayed beta-function ratio. The comparison `B(2a,2a) <= pi 2^(-4a)` holds for `a >= 3/4` by factoring out `[t(1-t)]^(2a-3/2)`. The logarithmic-derivative inequality reduces to `4a(4a^2+a-2)>=0`. Finally, `pi<22/7` and `(8/7)^5<2` give the strict bound `1551/880<9/5` at `a=4/5`. Symmetrization preserves both even moments. No numerical certificate is needed for this proof.

**Weaker hypothesis for the weak Landau limit.** The additional compound-Poisson jumps of sizes at least `N` have total intensity `x/N`. Omitting them has coupling cost at most `1-exp(-x/N)`. The hypothesis `x -> infinity` and `x^2 log^2(N)/N -> 0` makes both this cost and the original total-variation bound vanish. The common affine normalization preserves the comparison. The existing characteristic-function limit then proves weak convergence. This strengthens weak convergence only; the local limit still needs its stronger error condition.

None of these arguments proves uniqueness of the transition inside the certified memory interval, excludes all stationary points of even multiplicity, or establishes the general first-step-bias conjecture.
