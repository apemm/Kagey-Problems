# The centred interval of bimodal initial biases

## Scope and finding

The audit reread the complete proofs of Theorem 4.6 and Propositions F.5–F.6, then checked the corresponding finite, limit-transfer and affine-mixture Lean modules. The proof is sound. The local limit theorem previously used for the passage to the density is stronger than necessary. A direct argument from weak convergence removes that dependency.

## Finite proof

1. Subtracting consecutive forward equations gives the stated two-parent recurrence for first differences. Both interior coefficients are strictly positive for every `0 < ε < 1`, including the negative-memory range.
2. The boundary ratio recurrence gives
   `δ_(t+1) = ((t-b)δ_t + A)/(t+1)`.
   Here `b < 1` and `A > 0`, so an increment that has become nonnegative is followed by a positive one. This gives the two stated temporal sign restrictions, including the zero cases.
3. The augmented-row argument is valid. Consecutive output entries can share a parent only if their indices are adjacent; opposite strict signs prevent the same parent from witnessing both. The selected parent indices are therefore strictly ordered. Copying the boundary values introduces no exception.
4. Reflection gives the upper-half skew recurrence. The only new-centre case cancels exactly. The resulting nonnegative central difference is the point needed when the half-line moves between odd and even rows.
5. In Proposition F.6, a negative entry in the new upper half must satisfy `2i > t`. Both its parents are then in the preceding upper half. A later positive entry supplies a strictly later parent. This proves the restricted-row exclusion without assuming it at the new centre.

These steps are proved for the actual recursively defined finite mass function, rather than for an abstract sequence assumed to have the desired limiting shape.

## Transfer using weak convergence

Let the scaled lattice have mesh `δ_N = 2 N^(-a)`. For a fixed interval `I = [x,x+r]`, `r > 0`, write

`A_N(I) = μ_N(I)/(δ_N · #{lattice points in I})`.

Weak convergence to a continuous density implies convergence of `μ_N(I)` to the density integral over `I`. The interval boundary has limiting probability zero. Elementary floor and ceiling bounds give

`|δ_N · #{lattice points in I} - r| ≤ δ_N`.

Thus `A_N(I)` tends to the density average over `I`.

If a continuous limiting density had two successive strict valleys, five sufficiently short, ordered, equal-length intervals would have the same four strict high–low comparisons in their averages. For large `N`, the lattice block averages have those comparisons too. Select a maximum in each high block and a minimum in each low block. The five selected lattice indices are ordered and preserve all four strict inequalities, contradicting Proposition F.5.

The same argument with three intervals transfers Proposition F.6. Right-hand windows `[x,x+r]` allow `x=0` directly. Reflection dominance passes by comparing the two biases on each nonnegative window, taking the weak limit, and shrinking the window. This argument does not assume that arbitrary averaging kernels diminish four sign changes.

## The interval in the bias parameter

For `q ≥ 1/2`, reflection dominance and absence of a valley on the positive half-line make a global strict valley equivalent to a strict decrease at two points on the nonpositive half-line. Conditional unimodality at `q=1` makes every such difference nonpositive at `q=1`. The difference is affine in `q`, so positivity at one bias persists down to `1/2`. Strict witnesses also make the set relatively open. Reflection gives the centred open interval.

The endpoint conclusion does not rely on a derivative being nonzero. A strict valley is equivalent to two local maxima after using positivity, integrability and absence of flat intervals. At the bias endpoints there is no strict valley, hence the density is unimodal with one local maximum. The result permits an empty interval and permits its lower endpoint to be zero; no unproved strict positivity or regularity of that endpoint is claimed.

## Formalization

The new `BiasWeakTransfer*` modules formalize finite block extrema, the forbidden-pattern transfer, the actual span-two lattice windows, floor/ceiling geometry, their normalized lengths, shrinking density averages through the fundamental theorem of calculus, reflection dominance and the centred-interval assembly. The final probability interface is bounded-interval mass convergence for the actual finite mass function. A separate probability wrapper connects that interface to ordinary weak convergence and the identity of the finite law's interval masses.

The five averaging, geometry, transfer, count and assembly modules contain 18 new theorems and passed their combined target build (8,742 jobs). Their final entry is `biased_modes_centered_interval_of_interval_masses`. The probability wrapper and the repository-wide axiom audit are recorded separately in the final verification report. No new local-limit theorem is needed for the mathematical argument.
