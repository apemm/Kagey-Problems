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

The refined uniform certificate gives the narrow rational enclosures in
the manuscript's critical-constant table. The broad interval certificate
continues to provide the regularity on a larger neighborhood.

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

Squaring the coefficient gives `2 C^3/(9 H^2 B)`. The refined derivative
certificate evaluates this expression with outward rounding, giving
`9.86698768 < Q_* < 9.86698770`.
For nearby parameters the positive maximum is attained inside the interval,
since the ratio vanishes at both endpoints. Every scaled maximizer converges
to the unique maximum of the limiting cubic. Therefore every boundary
stationary location has distance `kappa_a/sqrt(3) + o(sqrt(delta))` from zero.
This does not assert uniqueness of the maximizing location at fixed memory.

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

The global Landau gap is at least `(1/50) min(1, distance^2)`. The proof
uses curvature on the quarter-unit neighborhood, 188 closed cells on each
side, and unimodality beyond the covered region. Each interval evaluation
has a proved integration-tail error and a Fourier derivative Lipschitz
allowance. The record is `paperD/data/landau_gap_certificate.json`.
The local curvature coefficient `0.039` is not substituted for the global
gap. The latter gives the displacement `x sqrt(100 E')` directly when
`2E' < 1/50`.

The same certificate checks `-Re Psi_infinity(theta) >= 2 abs(theta)/5`.
Near zero the existing remainder estimate proves this analytically. On
`[1/10, pi]` a closed cover evaluates the exact elementary expression.
Integrating the Fourier comparison with this decay, and taking the logarithm
tangent at eight, gives the local error `(47+10.4 log x)/x + 2.7x/N`.
The numerical constants are Arb proof inputs. The existing Lean integral
proof still establishes the weaker constants `889`, `165`, `6.6`.

For `log N >= 30000`, the polynomial lower bound on the exponential gives
`N >= 160 (log N)^6`. Uniformly on `log N <= x <= 2 log N`, each of the
truncation, coupling, mirror and rounding contributions to `E'` is at most
`log x/x`. Thus `E' < 20 log x/x < 1/100`, and the family mode is below
`N/4`. The displacement is below `sqrt(2000 x log x)`, hence below
`50 sqrt(x log x)`. This proves the explicit threshold `ceil(exp(30000))`.
It is a conservative theoretical threshold, not a practical numerical bound.

`EJPGlobalModeGap` formalizes the globalization and stability implications,
with the local, annular and endpoint inequalities as explicit hypotheses.
It does not replay the Arb cover. The earlier formal eventual bound with
constant `400` remains valid. The new constant `50` and length threshold
have the written proof just described.

Under `x^3 log^2 N/N -> 0`, the error tends to zero and the conditional mode
is eventually below `N/4`, as required by the existing mode comparison.
Taking the square root of the displayed error gives the wider localization
rate. It does not imply an approximation for fixed nonzero reversal rates.

## Quantitative bias boundary near memory one

Let `mu = E L_a > 0` and `rho = Var(L_a)/mu^2`. Three adjacent intervals
centered at `-mu`, zero and `mu`, each of length `mu`, have equal lengths.
Chebyshev gives conditional mass at least `1-4rho` in the right interval
and at most `4rho` in the middle. Reflection gives the left version.
For the bias mixture, both outer average densities therefore exceed the
middle one whenever `4rho/(1-4rho) < q < 1-4rho/(1-4rho)`.
Continuity supplies an ordered strict valley, so the established
classification gives bimodality. The interval is nonempty for `rho<1/12`.

The exact moments give
`rho = Gamma(1+a)^2 / ((2a-1) Gamma(2a)) - 1`.
At one, its value is zero and its derivative is exactly minus two, since
the two digamma terms cancel. Hence
`b_a <= 4rho/(1-4rho) = 8(1-a)+O((1-a)^2)`.
This is an explicit upper rate for the bias cutoff. It does not establish
global monotonicity, a matching asymptotic equivalent, or a rate for the
uniform density approximation. The proof is written, not formalized.

## Corrections made during review

- Used the certified global gap in the displacement inequality.
- Retained the separate truncation coefficient `2.7` in the sharpened error.
- Separated local bias monotonicity from the unproved global claim.
- Made the attained-boundary hypothesis explicit in the stationary equations.
- Made the numerical script check the complete stated slope enclosure, not
  merely positivity; it passed again under optimization.
- Named Drezner and Farnum explicitly where the abstract credit could otherwise
  be read as referring to James, James and Qi.
- Shortened theorem headings and displayed a long bound to remove overfull boxes.
- Exposed new helper lemmas to the repository's full axiom audit.
- Replaced "two-parent average" by "two-parent sum" in the proof overview.
  The coefficients are positive but need not add to one.
- Removed repeated Landau definitions and repeated statements of the mixture
  conjecture, and added a direct pointer to the arbitrary-bias proof.
- Restricted a broad description of formal coverage to the two shape theorems
  it actually describes. The critical asymptotics remain written proofs.
