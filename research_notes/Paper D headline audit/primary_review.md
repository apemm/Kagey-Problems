# Review of the two headline proofs

Reviewed on November 1, 2026, after the transition and centred-interval additions.
The review starts from the statements and equations in the current sources. It
does not treat the earlier manuscript review as evidence for these additions.

## Theorem 4.4

The uniqueness argument is valid on the stated domain. Write `Q(a) = g_a''(0)`.
The old signed cover excludes zeros through `0.6712` outside the short bracket.
The derivative certificate gives `0.68 < Q'(a) < 0.70` on the interior of a
larger interval containing that bracket. Continuity and the endpoint signs
therefore give exactly one zero. At that zero, evenness and the negative fourth
derivative give a negative cubic leading term for `g_a'(x)` as `x` decreases
to zero from the right. The previously proved shape dichotomy puts this critical
density in the unimodal branch. The outside-bracket shape certificate then
gives the global modal transition. This does not prove that central curvature
has no other zero above `0.6712`, and the theorem does not claim that.

The differentiated smoothing calculation was re-derived term by term:

- Differentiating the mixing probability contributes one `f(x) f(y)` term.
  Its derivative is `1/2`, and the difference of the two reflected transforms
  has modulus at most `2 f(y)`.
- Reflection about `v = 1/2` gives two copies of each half-interval term.
  The factor `2^{a(beta-1)}` in the smaller-argument frequency bound includes
  both this factor of two and the integral of `v^a` over `(0,1/2)`.
- Splitting the smaller memory argument at `(T2/t)^{1/a}` gives the displayed
  `J`, `A0`, and `kappa`. The denominator is `a gamma - 1`; there is no missing
  Jacobian factor. The larger argument is controlled by `H_gamma <= H_beta`.
- The logarithmic forcing term uses the exact integral of `v^a (-log v)`.
  The weight derivative contributes `C R / T` after conversion to exponent
  `gamma = beta - 1`.
- The compact-maximum argument bounds the frequency derivative first. Its
  bound is then used as a forcing term for the memory derivative. It does not
  assume either tail bound in order to prove it.
- The resulting uniform integrable envelope permits differentiation of the
  actual Fourier integral. Differentiating an earlier error bar would not
  justify this step; the proof and program do not do that.

The program was checked against these formulas. Its parameter remainder is
the differentiated geometric tail, its omitted moment series uses the Cauchy
radius `rho-w`, and its frequency remainder bounds the actual high derivative
on the complex parameter domain. The cutoff condition is checked indirectly
but correctly: the helper defines `T3 = upper(2^{a_hi} T2)`, and the new program
requires `T3 < 10`. The bound on the absolute first moment follows from
`E|L| <= sqrt(E L^2)` and the enclosure of twice the second series coefficient.

A fresh run with 1,100 moments and 1,600-bit precision under `python -O`
passed all 19 checks. It returned `Q' = [0.6890 +/- 8.16e-5]` and
`g''''(0) = [-0.07921 +/- 4.05e-6]`. The numerical source files were unchanged.
The fresh output is in `kagey-problems/problem131/paperD/verification`.

## Theorem 4.6 and Propositions F.5--F.6

The finite first-difference recurrence has positive coefficients at every
interior location used in the proof, even for negative memory. Its boundary
ratio recursion gives `delta_{t+1} = (t-b) delta_t/(t+1) + A/(t+1)` with
`b < 1` and `A > 0`. Hence an increasing boundary ratio cannot later decrease.
The augmented-row argument includes both deterministic initial-step cases.
An alternating sequence of output signs has strictly ordered parents; adjacent
opposite signs cannot choose their shared parent. This proves the claimed
four-block exclusion without overlooking endpoint modes.

For Proposition F.6, reflection dominance follows from the positive forward
recurrence for the difference of complementary-bias laws. A new central value
cancels by reflection. In the dominant-half first-difference argument, the
only parent that can lie outside the previous half belongs to the new central
difference of an odd row. Reflection dominance makes this difference
nonnegative. It cannot start the forbidden negative-positive pair.

The limiting affine-mixture argument is also valid. For bias at least one half,
a strict valley is equivalent to a descent at two points on the negative half.
Reflection dominance proves one direction; the absence of a positive-half
valley proves the other. Conditional unimodality makes every such affine
difference nonpositive at bias one. Positivity is therefore downward closed
as the bias moves toward one half. Openness and reflection give the centred
open interval. Integrability supplies outer low points, and absence of flat
intervals identifies valleys with two literal local maxima. These steps cover
empty intervals, endpoints, and the possibility that the lower endpoint is zero.

The original use of the span-two local limit was correct, including its factor
`N^a/2` and the parity rounding. It was nevertheless an unnecessary dependency
on an unrefereed preprint. The replacement Lemma F.7 uses only weak convergence:
short disjoint lattice windows have convergent normalized mass averages; choose
maxima in the high windows and minima in the low windows. Five such choices
contradict F.5, and three contradict F.6. Reflection dominance passes through
interval probabilities. This argument makes no claim that box convolution
preserves a prescribed number of sign changes.

## Source checks in this pass

| Source | Reading scope | Use |
| --- | --- | --- |
| [Guérin, Laulin, Raschel and Simon](https://arxiv.org/html/2409.06836v1) | Theorem 1.1, its complete Section 2 proof, and Remark 2.1(b), read again in full within that scope | Conditional unimodality and the exact conjecture, including its endpoint convention. The paper's radius is `1/2-b_a`. This was a targeted rereading, not a new full-paper review. |
| [Trinas and Valle](https://arxiv.org/html/2609.14753v1) | Proposition 2.1 and Section 3, including the complete local-limit proof, read again; current abstract/version record checked | The original transfer is supported. The revised proof no longer requires this result. The citation identifies it as an unrefereed arXiv preprint. This was not a fresh review of the entire paper. |
| Paper D | Theorem 4.4 and its classification proof; all of S6.D; `certify_transition.py`; the Taylor-model helper and its written moment, truncation, cell, and tail bounds; all of F.5--F.6 and Theorem 4.6 | Direct proof and implementation audit. |

No new claim about priority in the older correlated-Bernoulli literature is
made. The outstanding Drezner--Farnum and Heyde full-text comparisons remain
outstanding.

## Verification boundary

The final rebuilt PDF was checked directly: page 27 of Section 5 explicitly
states that the characteristic-function instantiation and assembly of the
uniform tail bounds remain a written analytic proof, and that the Arb
enclosures remain numerical. The new formal modules reduce that boundary,
but do not turn the Arb transcendental computations into Lean proofs.
Page 24 labels the alternative local limit as an unrefereed arXiv preprint
and says the proof does not depend on it. The final build record and coverage
map specify the exact added coverage. Eleven rendered pages were inspected,
including the headline statements, Section 5, F.6--F.7 and S6.D.
