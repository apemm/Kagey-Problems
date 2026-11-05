# Paper D EJP mode-location constant

Both sidecar modules live directly under `lean/PaperD/`, separate from the
`lean/PaperD/Modes/EJP*` modules.

## Bound for the revision

- The existing certificate puts the Landau mode in
  `(-0.22278299, -0.22278297)` and gives a local gap of at least
  `0.0393 (u - m)^2` on `[-0.2229, -0.2227]`. The sidecar uses `0.039`.
- Each endpoint is at least `0.00008297` from the mode. The local gap at each
  endpoint exceeds `2.6e-10`. Unimodality extends that absolute gap to the
  corresponding tail. The weaker global statement `κ min(1, (u - m)^2)`
  still suffices for the preliminary bound on the remote mirror term.
- A gap of at most `2E < 2.6e-10` gives the displacement bound
  `x sqrt(2E / 0.039)`. For the discrete comparison, add the lattice rounding
  loss `1/(2x)` and, for a symmetric mode, the mirror loss `8x/(3N)`.
- The generic window theorem uses `E ≤ 2000 log x / x`. Each extra loss is
  eventually at most `log x / x`, uniformly for `log N ≤ x ≤ 2 log N`.
  The total coefficient is `4002`, and `4002 / 0.039 < 400^2`.
- The existing `C = 889` Landau estimate gives the eventual upper bound
  `(889 log x + 1779) / x`, which implies the `2000` envelope in that
  window. The same `K = 400` covers both families of modes and both crossing
  parities. The threshold `N₁` is existential.

The paper's `E'` includes its lattice and mirror allowances. The generic
Lean theorem bounds the raw density error by `2000 log x / x` and adds its
allowances separately. It uses the existing Lean bound from the monotone tail
and total mass for the mirror term.

In `EJPModeStability.lean`, `ejp_landau_mode_gaps` proves the local and
off-interval bounds, `ejp_landau_mode_sqrt` gives the rescaled displacement
bound, `ejp_uniform_mode_rate_400` proves the generic window result, and
`ejp_cor_mode_location_400` specializes it to the Landau density at the crossing.

## Conditional inputs

The generic result takes the existing `LandauCertHyp`, `UnimodalHyp`, and
`LandauModeHyp`, plus the uniform approximation estimate. The Landau crossing
specialization obtains the mode data from the kernel-checked certificate and
uses the existing crossing window. Its remaining inputs are
`U2.LatticeFourierInversionHyp`, `U1.CPCharHyp`, `U1.EfronSteinHyp`, and
`UnimodalHyp landauDensity`. These represent lattice Fourier inversion, the
compound-Poisson characteristic function, the Efron–Stein inequality, and
unimodality of the Landau density.

## Analytic range

`EJPModeAnalyticRange.lean` reuses the monotonicity of the fourth-moment
envelope and checks `(111/100)^25 < 16` and `33517/18648 < 9/5` by exact
arithmetic. `Modes.EJPAnalyticRange.two_modes_of_ge` proves the existing
two-mode branch for the symmetric limit for `79/100 ≤ a < 1`. In that
branch, the density is nondecreasing up to some `c > 0` on the positive
half-line and nonincreasing after it, with `g(0) < g(c)`.
The theorem takes the existing density and law-convergence hypotheses
and the GLR second and fourth moment formulas, including integrability
of the moments.

## Verification

Both modules compiled without warnings with Lean 4.33.1 and the Mathlib
v4.33.1 cache. The checks used `lean -o` on source copies in
`%TEMP%/paperD-ejp-mode-sidecar`, with `LEAN_PATH` pointing to the
existing compiled dependencies under `~/lean-work/paperD/.lake/build/lib/lean`
and `~/lean-work/kagey131/.lake/packages`.

`#print axioms` reported exactly `propext`, `Classical.choice`, and
`Quot.sound` for each of the eight declarations in `EJPModeStability`
and each of the three declarations in `EJPModeAnalyticRange`, including
the private lemmas.

## Integrated verification

The final revision exposes the helper lemmas to the full declaration audit.
The integrated November 5 build passed for 374 modules and 23,905 declarations,
with only the three standard axioms. The final source hashes are in
`verification-manifest.json`; the earlier local hashes above describe the
sidecar check before that visibility change.
