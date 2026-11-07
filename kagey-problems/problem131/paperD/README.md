# The bias interval of the elephant random walk

The [27-page manuscript](problem131_memory.pdf) proves the GLRS bias-interval
conjecture for every superdiffusive memory. Theorem 1.1 gives the interval,
Theorem 1.2 gives its analytic threshold and critical behavior, and
Proposition 1.3 reports numerical constants.

The boundary is positive, continuous, continuously differentiable above
the threshold, and strictly decreasing just above it. The analytic proofs
also establish the quartic critical top and the square-root and three-halves
laws. Interval certificates only locate the threshold and enclose constants.
Global decrease of the boundary and an all-length finite-threshold theorem
remain open.

The [seven-page supplement](paperD_supplement.pdf) contains the complete
certificate error analysis and an independent fourth-moment check. It is
part of the journal submission and an ancillary PDF in the arXiv package.
Both main entry points contain the same paper. Source builds automatically
regenerate the cross-document labels.

The [archived combined version](archive/combined-2026-11-06/README.md)
retains the rare-reversal material. The present proofs do not depend on it.
See [submission_notes.md](submission_notes.md) for packages and build commands.

The [coverage map](../lean/PaperD/MAP.md) distinguishes formal proofs,
classical inputs, and written arguments. The existing Lean library derives
the actual moments, randomized transform, Fourier representation, and
unique curvature crossing from the finite walk and ordinary weak convergence.
It retains a checked weak-transfer proof, while the manuscript uses a
shorter derivative-limit argument. The new analytic quartic-sign and
boundary-regularity proofs are written proofs, not additional Lean theorems.

## Certificate files

| Claim or illustration | Script | Records |
| --- | --- | --- |
| Transition derivative and fourth derivative | certify_transition.py | data/transition_derivative_* |
| Independent endpoint check and conditional slope | check_critical_shape.py | data/critical_shape_check.json |
| Refined critical constants | certify_critical_constants.py | data/critical_constants_certificate.json |
| Finite-length examples | verify_elephant_modes.py | Computed illustrations, not certificates |
| Augmented-row diagram | Native LaTeX in sec_shape_engine.tex | Exact schematic, no numerical data |
| Phase illustration | figures/make_phase_figure.py | data/limit_phase_illustration.npz |

The transition records use Python 3.12.14, python-flint 0.8.0, 1100 moments
and 1600 bits. The independent endpoint check uses python-flint 0.9.0,
1800 moments and 2000 bits, and 1200 moments for the conditional slope.
The refined constants use 2000 moments and 2600 bits. Both refined scripts
retain their acceptance tests under python -O.
