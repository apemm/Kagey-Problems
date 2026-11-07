# The bias interval of the elephant random walk

## Fixed-memory EJP manuscript

The [33-page manuscript](problem131_memory.pdf) proves the GLRS bias-interval
conjecture for every superdiffusive memory. Theorem 1.1 contains the analytic
classification. Theorem 1.2 separates the computer-assisted threshold and
critical asymptotics.

The paper also gives the finite shape bounds, the variational bias boundary,
its positive continuously differentiable branch, the quartic critical top,
and the three-halves opening law. The analytic theorem states positivity
of the bias boundary explicitly, so sufficiently biased starts are unimodal.
The finite-threshold development remains in the combined archive.
Global decrease of the bias boundary and an all-length finite-threshold
theorem are open questions, not additional claims of this submission.

The rare-reversal results, Luria–Delbrück and Landau estimates, near-one
profile, crossings, finite-threshold development and their proofs are preserved in the
[archived 70-page combined version](archive/combined-2026-11-06/README.md).
The fixed-memory manuscript does not depend on that archive for a proof.
The journal and arXiv entry points contain the same paper.

See [submission_notes.md](submission_notes.md) for the source packages and
build commands, and [the verification record](../../../reports/paperD-ejp-2026-11-05/README.md)
for the declaration audit. The Lean library includes both present and
archived results. Its [coverage map](../lean/PaperD/MAP.md) distinguishes
formal proofs, hypotheses and written analysis.

## Certificate files

| Claim or illustration | Script | Records |
| --- | --- | --- |
| Parameter cover | certify_threshold.py, threshold_taylor.py, threshold_hankel.py, threshold_pointwise.py | data/threshold_*.txt |
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

Historical descriptions are in [archive/README-before-fixed-split.md](archive/README-before-fixed-split.md).
