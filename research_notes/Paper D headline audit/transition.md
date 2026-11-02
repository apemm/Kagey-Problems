# Transition certificate audit

Audit date: 1 November 2026.

## Scope and verdict

This review re-derived Section S6.D independently from the smoothing equation and compared every new bound with `paperD/certify_transition.py`. It also inspected the coefficient-majorant and tail interfaces in `threshold_taylor.py`. The analytic reduction is valid under the regularity and uniform Fourier bounds stated in S6.D. No missing factor or reversed inequality was found in the derivative certificate.

This verdict concerns the analytic reduction and its implementation. It does not identify Arb evaluation with a Lean proof. Reproduction logs for the complete numerical certificate and the final manuscript build belong to the main audit record.

## Derivative identities

Write `x = t v^a`, `y = t (1-v)^a`, and `p = (1+a)/2`. The derivative of the positive path in memory is

`∂a φ_a(x) + x log(v) ∂t φ_a(x)`.

The negative path contributes `∂a φ_a(-y) - y log(1-v) ∂t φ_a(-y)`. Conjugate symmetry gives the same derivative moduli at opposite frequencies. Since `p` and `1-p` are nonnegative and sum to one, both intrinsic derivative mixtures are bounded by their common modulus. The derivative of the weight is

`(1/2)(φ_a(y)-φ_a(-y))`.

Its norm is at most `f(y)`. Multiplication by `φ_a(x)` therefore contributes `f(x)f(y)`, exactly as printed. It contributes neither one half nor two copies of that product.

The same product rule in frequency gives the two terms `v^a u(x)f(y)` and `(1-v)^a f(x)u(y)`. Their signs before taking norms are harmless, including the negative-frequency branch.

## Reflection and the constants

For an integrable function `h` on `[0,1]`, reflection gives

`∫₀¹ h(v) dv = ∫₀¹⁄² [h(v)+h(1-v)] dv`.

Consequently, each pair of exchanged derivative terms contributes twice its sum over the half interval. The mixing product is already symmetric and also contributes twice its half-interval integral. These factors agree with `H_β = 2∫₀¹⁄² f(tv^a)(1-v)^(-aβ) dv`.

The smaller frequency argument uses

`2 ∫₀¹⁄² v^a (1-v)^(-aβ) dv ≤ 2^(a(β-1))/(a+1)`.

For the larger argument, the extra factor `(1-v)^a ≤ 1` permits the use of `H_β`. This gives the stated `A₁ + R D₁` bound.

For the smaller memory argument, the cutoff `v₀=(T₂/t)^(1/a)` lies in the half interval because `t ≥ 2^a T₂`. Integrating the constant bound below `v₀` and the power bound above it gives

`2 C 2^(aβ) t^(-β-1/a) [M_a T₂^(1/a) + D_a T₂^(1/a-γ)/(aγ-1)]`.

Extending the upper tail integral to infinity is an upper bound because `aγ>1`. Multiplication by `t^γ` and `γ-β-1/a<0` allows replacement of `t` by `T`. The resulting coefficients are exactly `A₀` and the additional term in `κ`.

The larger memory argument uses `H_γ ≤ H_β`, since `γ<β` and `0<1-v≤1`. No decay assumption on `w` beyond the compact interval is used: the candidate decay constant is replaced by the weighted maximum on each finite interval during the bootstrap.

For the chain terms, the smaller argument gives the printed logarithmic integral and hence

`M C 2^(a(β-1)) [log(2)/(a+1)+1/(a+1)^2] t^(-γ)`.

The larger argument uses `-log(1-v) ≤ log(2)` and `(1-v)^a ≤ 1`, yielding `D₁ log(2) R t^(-γ)`. The mixing product contributes `C R t^(-β) ≤ (C R/T)t^(-γ)`. Thus all three parts of `A_S` agree with the script.

## Propagation and Fourier differentiation

The maximum argument is sound. The weighted derivative is continuous on each compact interval. At a maximum beyond the initial cells, the integral inequality holds with that maximum replacing the proposed constant. Strict contraction then prevents the maximum from reaching the barrier. The frequency bound is established first, so its use in the memory forcing term is not circular.

The global bound on `u` follows from the absolute first moment. The certificate checks the stronger second-moment inequality `E[L²]<4`, using `2*cS[2]<4`, and Cauchy–Schwarz gives `E|L|<2`.

Local analytic dependence follows from the complex moment majorant, not from the numerical parameter polynomial alone. At `v=0` or `v=1`, no derivative of `log(0)` is needed. Endpoints have measure zero, and `v^a |log(v)|` has a finite continuous extension there, uniformly for `a` in the compact memory interval. The uniform `t^(2-γ)` bound is integrable because `γ>3`; the local envelope covers the finite-frequency part.

With `D_a=4`, `γ=7`, and `T=10`, the Fourier remainder is `1/(10000π)`. The fourth-spatial-derivative remainder is `C T^(-3)/(3π)`. The signs and powers used in the script agree with the even-frequency Fourier formulas.

## Numerical source inspection

`derivative_cells` encloses the parameter-polynomial derivatives directly. For each parameter order it sums norms of the frequency-polynomial coefficients, so its use of `i*w^(i-1)` is valid on the whole symmetric interval, including its centre.

The missing parameter coefficients use `q^K((K+1)-Kq)/(ρ(1-q)^2)`. The omitted moment series uses Cauchy's derivative estimate with distance `ρ-w`. The frequency Taylor remainder bounds the actual high derivative using `Pabs` and `tailS`; it does not use a probability moment at complex memory.

The finite-frequency integral uses signed polynomial coefficients before interval evaluation. Its parameter and moment-series remainder terms are then added as symmetric intervals. The fourth derivative uses the correct positive Fourier sign. Initial-cell checks use the right endpoint for weighted power bounds and include every cell meeting the required interval.

All acceptance checks in the production script call `require`, so `python -O` does not suppress them. The script records hashes of itself and both numerical dependencies. It tests cell nonemptiness and finite upper bounds.

## Formal coverage

`PaperD/Modes/TransitionSmoothing.lean` proves the exponent-path derivative, joint chain rules in memory and frequency, the smoothing product/weight derivatives, the pointwise norm inequalities, and exact half-interval reflection. It also proves the factor-two identity for symmetric envelopes. The inputs are ordinary differentiability and component norm bounds. The target smoothing inequality is not an input.

`TransitionSmoothingIntegral.lean` proves dominated differentiation of the smoothing integral from the component paths and an integrable local envelope. It derives the complete derivative envelope, including the mixing-weight contribution, before applying dominated differentiation. Both the derivative formula and its integral norm bound are conclusions.

`TransitionBounds.lean` already proves the compact-maximum propagation, the dominated Fourier differentiation theorem, exact numerical slack, and the rational tail comparison.

The remaining analytic interface includes deriving joint differentiability of the actual characteristic function from its complex moment majorant, supplying the concrete local envelope and measurability for its smoothing integral, and instantiating the resulting estimates with every global power/logarithmic bound. Numerical transcendental and coefficient enclosures remain outside Lean. A checked algebraic or analytic interface is not a kernel check of the complete characteristic-function certificate.

## Build verification

The final versions of both modules passed `lake build PaperD.Modes.TransitionSmoothingIntegral` on 1 November 2026 with Lean 4.33.1. The target rebuild checked `TransitionSmoothing` and then `TransitionSmoothingIntegral`; it exited successfully with no warnings. The two files contain thirteen proved theorems and four definitions. They contain no `sorry`, `admit`, or new axioms.

Build workspace: `C:/Users/arjun/lean-work/paperD`. Compiler: `C:/Users/arjun/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake.exe`. The workspace's source directory points to the repository's `kagey-problems/problem131/lean` directory.
