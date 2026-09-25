# Checks for the two Problem 131 papers

The proofs are in the papers. The scripts below check the finite statements exactly and the
asymptotic ones numerically. The high-precision checks are not interval arithmetic, so they support
the proofs but do not replace them. Everything uses standard-library Python 3.

## Paper A: binary crossings

Run `python -B verify_all.py --paper a`.

| Script | What it checks |
| --- | --- |
| `verify.py` | Run-count probabilities against a dynamic program and against word enumeration; normalization; generating functions; the two lattice-path bijections; variance and normal approximation; central crossings by exact bracketing, and coefficient monotonicity. It also has a few checks of the d-direction law. |
| `check_bessel.py` | The central Bessel bound at 1,400 points, and crossing comparisons at high precision up to N = 10^8. |
| `verify_adjacent.py` | Adjacent-bin ratio and global extrema in 474 exact distributions up to N = 80; exact adjacent thresholds; the cubic gap between the central and adjacent polynomials by word enumeration up to N = 12, the ties at N = 2, 3, and the exception at p = 0. |
| `verify_allbin.py` | 5,476 exact coefficient comparisons, 264 all-bin Bessel inequalities, 28 Laguerre-Bessel inequalities, and the crossing and edge expansions at 80 digits. |
| `verify_periodic_window.py` | 66 cyclic run polynomials against enumeration, 120 relative-error inequalities, and root and critical-window samples up to N = 10^12. |

`verify.py` checks the exact law against enumeration for N <= 16 at 20 rational values of p. The
polynomials have degree less than N, so for those N this proves the polynomial identities. The table
of central roots is checked by exact rational signs at the neighboring decimals. The larger roots and
the asymptotic residuals use floating point.

## Paper B: d directions

Run `python -B verify_all.py --paper b`.

| Script | What it checks |
| --- | --- |
| `verify_geometry.py` | 6,733 exact bin probabilities in 237 distributions against a dynamic program, 158 of the distributions also by word enumeration; normalization, moments, and the values at p = 0, 1. |
| `verify_simplex_threshold.py` | The positive refresh formula, balancing transfers, the edge-mode example at N = 4, and the balanced-face crossings at high precision. |
| `verify_frontier_boundary.py` | The bound for all compositions, the mixed-face crossover, and the fixed rare-count formulas and crossings. |
| `verify_frontier_modes.py` | Spatial profiles, lattice-volume limits, exact finite-N mode comparisons, and the weak-field support hierarchy. |
| `verify_vertex_completion.py` | 462 exact identities for the gamma representation, 200 exact elasticity checks, 16 root brackets, and 4 large cases with growing rare counts, each at two series cutoffs. |

`python -B verify_all.py` runs both groups. The output is in `data/`; the dated logs are from
earlier versions of the manuscripts, before the split into two papers.

## Lean

`python -B lean/verify_lean.py` compiles the three Lean files with Lean 4.33.1 and `Std` (use
`--lean /path/to/lean` if `lean` is not on PATH). The 27 theorems cover the clipped-product
deficits, finite coefficient identities and monotonicity, and the algebra that follows from given
Taylor coefficients. The build output, source hashes and axioms are in `lean/build-log.txt` and
`lean/verification-manifest.json`.

The probability model, the infinite Bessel series, the asymptotic inversions, the saddle-point
estimates and the limit theorems are not in Lean. See `lean/README.md`.
