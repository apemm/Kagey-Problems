# Scalar estimates in the transition proof

This review checks the estimates in Section S6.D and their implementation in
`certify_transition.py`. The proof and the certificate script were read in
full. In `threshold_taylor.py`, the complex majorant, coefficient recurrence,
`tailS`, and complete `TaylorModel.certify` implementation were checked. The
stored 1600-bit, 1100-moment certificate was also read. This review did not
rerun the numerical certificate; the final verification run is recorded
separately.

## Conclusion

The scalar estimates and their implemented acceptance checks agree. No missing
factor, reversed Fourier sign, or omitted remainder was found. The transition
argument proves uniqueness of the curvature zero in the certified region and
uses the existing shape certificate outside it. It does not need a claim that
central curvature has no further zeros in the already bimodal region.

## Checks that carry the derivative certificate

1. The half-interval cutoff is verified in the code. `TaylorModel.certify`
   defines `T3` as an upper enclosure of `2^a_hi T2`; the new script checks
   `T3 < 10`. Thus the larger argument is at least `T2` whenever the new tail
   argument applies. The stored upper cutoff is approximately 9.53859.
2. The global frequency-derivative bound follows from the second moment:
   `2*cS[2] < M^2` implies `E|X| < M` by Cauchy--Schwarz. The coefficient
   `cS[2]` bounds the actual real-parameter second-moment coefficient because
   its complex square contains the entire real memory interval.
3. Reflection of the smoothing integral yields two copies of each half-range
   term. For the smaller frequency argument, replacing
   `(1-v)^(-a beta)` by `2^(a beta)` and integrating `v^a` gives exactly
   `2^(a(beta-1))/(a+1)`. The numerical forcing constant therefore has the
   factor stated in S6.D.
4. At `v0=(T2/t)^(1/a)`, the compact part of the memory integral is bounded
   by `Ma*v0`; the remaining power integral is at most
   `v0^(1-a gamma)/(a gamma-1)`. After multiplication by the outer factors,
   both parts have the factor `t^(-beta-1/a)`. Multiplication by `t^gamma`
   then gives the stated `J`, `A0` and `kappa` because
   `gamma-beta-1/a < 0`.
5. The smaller logarithmic term uses the exact primitive
   `v^(a+1){-log(v)/(a+1)+1/(a+1)^2}`. Its limit at zero is zero.
   The larger logarithmic term is bounded using `-log(1-v) <= log 2`.
   The derivative of the mixing weight contributes one copy of `f(x)f(y)`:
   the derivative `p'=1/2` cancels the factor two in the difference bound.
6. The memory-derivative Taylor remainder is the differentiated geometric
   tail, starting at coefficient `K+1`, with factor
   `q^K((K+1)-Kq)/(rho(1-q)^2)`. The omitted moment series is a separate
   analytic remainder; Cauchy's estimate gives the divisor `rho-w`.
   Neither operation differentiates an already established approximation
   error as though it were an identity.
7. The frequency-cell remainder bounds the actual derivative of order 48
   (or 49 for the frequency derivative) using the complex coefficient
   majorant and the omitted-series bound. It does not use a probability
   moment evaluated at complex memory. Cells cover the whole closed interval
   `[0,10]`, including both sides of the cutoff at six.
8. The parameter derivative of central curvature has the negative Fourier
   sign and weight `t^2`; the fourth spatial derivative has the positive
   sign and weight `t^4`. Their tail bounds are respectively
   `Da*T^(3-gamma)/(pi*(gamma-3))` and
   `C*T^(5-beta)/(pi*(beta-5))`. At the adopted constants, the first is
   `1/(10000*pi)` and the second is `C*T^(-3)/(3*pi)`.
9. All 19 named numerical acceptance checks use `require`. Optimized Python
   execution does not remove them. Degree selection uses a floating-point
   heuristic only to choose a finite polynomial degree; the subsequent
   remainder is evaluated for that actual degree with interval arithmetic.

## Additional formal coverage

`PaperD/Modes/TransitionIntegrals.lean` proves:

- the differentiated geometric-tail identity, including the Cauchy-radius
  divisor;
- the full and truncated power-tail integrals for the smaller memory
  argument;
- the general Fourier power-tail integral and a bound on the integral of an
  actual measurable function controlled by that envelope;
- the logarithmic antiderivative, its integral from zero, and the half-range
  evaluation;
- the complete scalar half-range inequality supplying the frequency forcing
  constant;
- the directly weighted logarithmic half-range inequality supplying the
  smaller chain-rule forcing constant, including the factor
  `2^(a(beta-1))`.

These are symbolic integral and series results. They reduce the written
portion of the scalar calculation. They do not certify the Arb evaluations,
the holomorphic moment majorant, or the complete assembly of the differentiated
smoothing estimates into the actual characteristic-function tail. Those
boundaries must remain explicit in Section 5.

The final focused build passed with all eleven theorems and no warnings:

```text
lake build PaperD.Modes.TransitionIntegrals
Built PaperD.Modes.TransitionIntegrals (22s)
Build completed successfully (3403 jobs).
```

The repository-wide build and axiom audit are separate final checks.

## Additional check of the weak-transfer replacement

The new weak-shape-transfer lemma in `app_bias_interval.tex`, its use in
`sec_bulk_applications.tex`, and the five `BiasWeakTransfer*.lean` modules
were read separately. Ordinary weak convergence suffices under the lemma's
uniform-lattice and continuous-density hypotheses. No local limit theorem is
needed for this step.

- Unequal lattice counts cause no problem: each window mean divides by its
  own `eta * card`, which tends to the common window length. Comparing raw
  window masses without that normalization would not be enough.
- The same maximizing atom in the third window works for both adjacent
  inequalities. The two minimizing atoms also work simultaneously with
  their respective neighbouring maxima.
- Bounded interval endpoints are continuity points of the limiting measure.
  Open or closed endpoint conventions therefore give the same limit; the
  lattice-count error tends to zero in either case.
- A witness beginning at zero can be moved slightly right by continuity.
  The formal proof uses forward windows, whose lattice points already lie
  in the required half, including when the left endpoint is zero.
- Reflection is an exact bijection of the reflected lattices. Its mass
  inequality passes to fixed interval masses before the intervals shrink.
- The formal assembly takes convergence of actual finite-law interval
  masses as an input. That input is weaker than a local limit and contains
  no shape conclusion. The implication from ordinary weak convergence to
  these continuity-set limits remains a written measure-theoretic step.

For clarity, the lemma should explicitly refer to the lattice mass sequences
including zero masses. Reading “atom masses” as only the positive support
points would not justify selecting minima among every lattice point in a
window. The finite-law application and the formal definitions already use
the required full lattice sequence.
