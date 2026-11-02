# Independent review of the bias interval

The new interval argument is mathematically sound on the stated assumptions.
I read the manuscript proof fragment and the five new finite, transfer,
mixture and assembly modules. I also reviewed `TransitionClassification.lean`.
This is a mathematical audit, not a substitute for the final build and axiom
audit. I did not rerun a full build during this review.

## Finite dominant half and transfer

- Reflection dominance follows from the forward equation for the skew
  `P(n,k)-P(n,n-k)`. For an odd-to-even step, the new centre has skew zero.
  Away from that centre both parents are in the old upper half. At the outer
  support edge the out-of-support parent vanishes, so its coefficient need
  not be treated as a transition probability outside the old support.
- For first differences the correct half is `2k+1 >= n`, rather than
  `2k >= n`. On an even-to-odd step, its new central entry can have a parent
  outside the old half. That entry is nonnegative by reflection dominance,
  so it cannot be the negative member of a forbidden negative-positive pair.
- The temporal outer boundary is handled correctly. For `q >= 1/2` it is
  the negative of the left boundary with bias `1-q <= 1/2`. The previously
  proved absence of a positive-then-negative temporal pair therefore gives
  absence of a negative-then-positive pair on the right boundary. The
  initial augmented restricted row consequently has pattern contained in
  positive, negative.
- Selecting parents of opposite signs preserves strict index order. For
  adjacent children the only possible equal parent would have both signs,
  which is impossible. This closes the induction at the moving centre.
- The limit transfer uses the actual span-two grid. For `x >= 0`, the floor
  inequality gives `n <= 2k+1`; strict limit inequalities force distinct
  indices even when the finite interpolation has plateaus. Reflection
  dominance is transferred using the complement-bias law at the same positive
  point. It does not incorrectly identify the floors at `x` and `-x`.

## Interval of literal modes

- Reflection dominance plus the absence of a right-half valley makes a strict
  valley equivalent to a strict descent somewhere in the negative half.
  If the valley bottom is positive, applying the right-half property to
  `(0,y,z)` replaces it by a descent from `x` to zero. The reverse implication
  uses `-x` as the right witness.
- Conditional unimodality and reflection dominance imply that the positive-
  first-step density is nondecreasing on the negative half. Thus the descent
  difference is affine in the bias and nonpositive at bias one. Positivity
  at a bias `q <= 1` persists at every smaller bias down to one half. This is
  a proof of downward closure, not an assumption of connectedness.
- Strict inequalities at fixed spatial witnesses are open in the bias. The
  supremum argument handles both the empty interval and the possible endpoint
  zero correctly. Reflection supplies the other half of the interval.
- A strict valley gives two genuine local maxima: integrability supplies a
  lower value on each outer tail, and compact maximization supplies one
  interior maximum on each side. Conversely, no flat interval forces a lower
  point between two distinct local maxima. The existing global at-most-two
  result then gives exactly two, not merely two stationary points.
- Outside the interval, the no-valley argument constructs a global mode and
  proves monotonicity on either side. No-flatness makes its local-mode set a
  singleton. Therefore both endpoints of the open bimodal-bias interval are
  correctly assigned to the unimodal case.

The final assembly derives dominance, the right-half property, no-flatness and
the global mode bound from the actual recurrence, local limits and Fourier
inputs. It does not assume the new interval or mode-count conclusions.

## Scope and the transition theorem

The result permits a lower bias endpoint in `[0,1/2]`. It does not prove that
this endpoint is positive for every memory below one, or monotone as a function
of memory. Those assertions should not be folded into a statement that every
clause of a literature conjecture has been settled without checking its exact
wording. The near-one profile proves convergence of the lower endpoint to zero,
without a rate and without assuming a uniform theorem for endpoint biases.

`TransitionClassification.lean` correctly separates a local unique zero from
a global unique modal transition. Its global theorem takes the old outside
shape branches as inputs, not a global sign condition on central curvature.
The critical case uses the negative fourth derivative to exclude central
convexity. Strict convexity alone would not exclude an isolated zero of the
second derivative in the already bimodal region. The new formal theorem avoids
that mistake.

No mathematical correction is required by this review. A numerical map of bias
sets is no longer needed to support connectedness, since the theorem proves it
for every superdiffusive memory. Omitting such a map would help keep the paper
shorter.
