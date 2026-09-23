# Verification supplement for the two Problem 131 papers

The analytic proofs are in the manuscripts. The scripts below provide independent
finite and numerical checks; high-precision asymptotic evaluations are not interval
certificates. All scripts use standard-library Python 3.

## Paper A: binary crossings

Run `python -B verify_all.py --paper a` from this folder.

| Script | Coverage |
| --- | --- |
| `verify.py` | Exact run-count probabilities, independent dynamic programming and word enumeration; normalization; generating functions; the two lattice-path bijections; variance and normal approximation; exact bracketing of central crossings and coefficient monotonicity. This original checker also retains a few multistate baseline checks. |
| `check_bessel.py` | 1,400 central Bessel-bound cases and high-precision crossing comparisons through N=10^8. |
| `verify_adjacent.py` | Exact adjacent-bin ratio and global extrema in 474 rational distributions through N=80; rational adjacent thresholds; independent word enumeration for the positive central/adjacent cubic gap through N=12, with N=2,3 ties and the p=0 exception. |
| `verify_allbin.py` | 5,476 exact coefficient comparisons, 264 all-bin Bessel inequalities, 28 Laguerre--Bessel inequalities, and 80-digit crossing/edge expansions. |
| `verify_periodic_window.py` | 66 cyclic run polynomials checked by enumeration, 120 relative-error inequalities, and root/critical-window samples through N=10^12. |

`verify.py` checks the exact law against enumeration for N<=16 and 20 rational
probabilities; its polynomial degree is less than N, so these comparisons also
establish the corresponding finite polynomial identities for those N. The
central-root table is checked by exact rational signs at neighboring decimal
brackets. Larger-root checks and asymptotic residuals use numerical arithmetic.

## Paper B: multistate occupations

Run `python -B verify_all.py --paper b` from this folder.

| Script | Coverage |
| --- | --- |
| `verify_geometry.py` | 6,733 exact rational bin probabilities in 237 distributions against an independent dynamic program; 158 distributions also checked by word enumeration; normalization, moments, and parameter boundaries. |
| `verify_simplex_threshold.py` | Positive refresh formula, balancing transfers, a finite edge-mode counterexample, and high-precision balanced-face crossings. |
| `verify_frontier_boundary.py` | Composition-uniform bounds, mixed-face crossover, fixed rare-count formulas and crossings. |
| `verify_frontier_modes.py` | Spatial profiles, lattice-volume limits, exact finite-mode comparisons, and weak-field support hierarchies. |
| `verify_vertex_completion.py` | 462 exact representation identities, 200 rational elasticity checks, 16 quantitative root brackets, and four growing-rare-count stress cases with two series cutoffs. |

`python -B verify_all.py` runs both groups. Recorded numerical outputs are in
`data/`; dated logs distinguish earlier manuscript versions from the current split.

## Formalization scope

`python -B lean/verify_lean.py` compiles three files using Lean 4.33.1 and `Std`;
use `--lean /path/to/lean` when the executable is not on PATH. The 27 declarations
verify clipped-product deficits, finite coefficient identities and monotonicity,
and consequences of explicit Taylor-coefficient hypotheses. The compiler output,
source hashes, and axiom dependencies are recorded in `lean/build-log.txt` and
`lean/verification-manifest.json`.

The probability model, infinite Bessel sums, analytic inversion, saddle estimates,
and complete limiting theorems are not formalized in Lean. See `lean/README.md`
and the precise source statements for the limits of the checked coverage.
