# Review of the new deductions

## Bias boundary

Write `A(t)=h_a'(t)` and `B(t)=h_a'(-t)`. The existing half-line theorem gives
`B(t) >= 0`. For a bias `q >= 1/2`, the derivative on the negative half-line is
`q B(t) - (1-q) A(t)`. It is negative exactly when `A(t)>0` and
`1-q > B(t)/(A(t)+B(t))`. The existing no-valley and two-mode theorems make
such a decrease equivalent to bimodality. Taking the union of these strict
inequalities proves the infimum formula, including the empty-set convention.

At an attained interior minimum, differentiating the ratio gives
`A(t) B'(t) - B(t) A'(t)=0`. Since `B'(t)=-h_a''(-t)`, this is exactly the
second stationary equation for the mixture at `q=1-b_a`; the first follows
from equality in the ratio. There is no need to assume a unique minimizer,
and the statement does not assert one. The cutoff and stationary deductions
have new Lean proofs with their regularity hypotheses explicit.

## Critical top and fair modes

The certified Fourier tail with exponent eight makes spatial derivatives
through order six continuous uniformly near the threshold. The parameter
derivative tail with exponent seven permits differentiation of the central
curvature and of the lower spatial derivatives needed below. The compact
frequency part follows from the locally uniform moment series.

Set `C = partial_a g_a''(0)|_(a*)` and `B = -g_(a*)''''(0)`. Both are strictly
positive by the existing interval certificate. Evenness eliminates odd
derivatives and the central curvature is zero. Taylor's theorem therefore
gives the negative quartic top, with a uniform sixth-order remainder.

For `delta=a-a*>0`, the divided derivative is
`g_a'(u)/u = C delta + o(delta) - (B+o(1))u^2/6 + O(u^4)`.
Evaluating at fixed multiples of `sqrt(delta)` brackets the positive mode.
Uniqueness of that mode comes from the existing fair-shape theorem; it is
not inferred from the local Taylor expansion alone. Substitution into the
density expansion gives the peak excess `3 C^2 delta^2/(2B)`.

The certified intervals `C in (0.68,0.70)` and `B in (0.07,0.09)` imply the
stated quartic and square-root coefficient bounds by direct arithmetic.

## Three-halves opening and local monotonicity

The cutoff formula gives the half-width as the positive supremum of
`g_a'(t)/(h_a'(t)+h_a'(-t))`. The numerator is nonpositive after the positive
fair mode, so the positive part is supported on an interval of length
`O(sqrt(delta))`. The independently checked value `H=h_(a*)'(0)>0` keeps the
denominator positive there.

With `t=v sqrt(delta)`, the ratio divided by `delta^(3/2)` converges uniformly
on the relevant bounded interval to `(Cv-Bv^3/6)/(2H)`. Its unique positive
maximum is at `v=sqrt(2C/B)` and equals `sqrt(2) C^(3/2)/(3H sqrt(B))`.
The support endpoint tends to `sqrt(6C/B)`, so this maximizer stays inside
the interval. This proves the claimed coefficient without differentiating
an optimizer or assuming its uniqueness for nearby parameters.

For local continuity, choose a small fixed interval on which the denominator
stays positive and contains all positive numerator values. A maximum of a
continuous function over that compact interval varies continuously in the
parameter. For strict widening, the parameter derivative of the ratio is
positive at every `0<t<=r` after reducing both neighborhoods. This follows
from `partial_a g_a'(t)=Ct+o(t)` and the bounded parameter derivative of the
denominator. Evaluating at an earlier positive maximizer proves strict
increase. These are local arguments; they do not prove global monotonicity.

The three-halves exponent is a local cubic-maximization consequence, not a
claim to have discovered a new general bifurcation exponent. Its content
here is the verified applicability and explicit constant for this density.

## Computation-free range

The old fourth-moment envelope decreases on `[3/4,1]`. At `79/100`,
`111^25 < 16*100^25` gives `2^(4/25)>111/100`. With `pi<22/7`, the envelope
is below `33517/18648<9/5`, contradicting the unimodal fourth-moment bound.
The exact comparison is formalized. This modest extension does not replace
the numerical proof of the global transition or locate the threshold.

## Explicit mode constant and wider range

The Landau curvature certificate gives a quadratic gap with coefficient
`0.039` in a small interval around its mode, and an absolute gap greater
than `kappa_L` outside that interval. The approximation first localizes a
discrete maximizer inside the interval; only then is `0.039` used. Replacing
the global `kappa_L` by `0.039` without this localization would be invalid.

The manuscript's total comparison error `E'` includes rounding and the
reflected tail. Uniformly for `log N <= x <= 2 log N`, it is eventually at
most `2000 log x/x`. Hence `x sqrt(2E'/0.039) <= 400 sqrt(x log x)`.
The Lean proof uses slightly different existing rounding/mirror allowances
and checks the still sufficient inequality `4002/0.039 < 400^2`.
The full interface and its classical inputs are in `lean-mode-constant.md`.

Under `x^3 log^2 N/N -> 0`, the error tends to zero and the conditional mode
is eventually below `N/4`, as required by the existing mode comparison.
Taking the square root of the displayed error gives the wider localization
rate. It does not imply an approximation for fixed nonzero reversal rates.

## Corrections made during review

- Used the local curvature constant only after proving localization.
- Kept the factor `889` in the `x/N` contribution to the error estimate.
- Separated local bias monotonicity from the unproved global claim.
- Made the attained-boundary hypothesis explicit in the stationary equations.
- Made the numerical script check the complete stated slope enclosure, not
  merely positivity; it passed again under optimization.
- Named Drezner and Farnum explicitly where the abstract credit could otherwise
  be read as referring to James, James and Qi.
- Shortened theorem headings and displayed a long bound to remove overfull boxes.
- Exposed new helper lemmas to the repository's full axiom audit.
