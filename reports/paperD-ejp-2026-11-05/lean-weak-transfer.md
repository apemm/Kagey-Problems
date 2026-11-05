# Paper D weak transfer and the variational bias boundary

## Existing weak transfer

`Modes.biased_modes_centered_interval_of_weak_probability` already proves the bias-interval classification from ordinary weak convergence of the scaled count laws. `BiasWeakTransferProbability` evaluates the exact atomic probabilities on closed intervals and applies Portmanteau. `BiasWeakTransferCounts` normalizes by the lattice window length, and `BiasWeakTransfer` transfers the two-valley bound, the dominant-half valley bound, and reflection dominance. This covers the count lattice application of `lem:weak-shape-transfer` in `app_bias_interval.tex`. The manuscript lemma also allows arbitrary shrinking affine lattices.

The existing classification takes weak convergence and the scaled law and density identifications as inputs, along with conditional unimodality and the characteristic-function smoothing and Fourier representation. The proof uses neither pointwise local limits nor assumptions on the limiting mixture's mode count. The eleven inspected transfer and interval modules match their source hashes in the November 1 headline audit. The six key transfer and classification declarations listed there depend only on `propext`, `Classical.choice`, and `Quot.sound`. [Headline audit](../paperD-headline-audit-2026-11-01/README.md)

## New variational boundary proof

`PaperD.Modes.EJPBiasDerivativeCutoff` formalizes the variational equation in `prop:bias-boundary` and its attained-endpoint derivative conclusion. Write `x = -t < 0`. The Lean cutoff is the infimum of `h'(x) / (h'(x) + h'(-x))` over points with `h'(-x) > 0`, with `1/2` inserted in the set. This gives the clipped infimum in the manuscript, including `1/2` when the candidate set is empty. [Manuscript](../../kagey-problems/problem131/paperD/sec_critical_shape.tex)

- `reflectedMixture_valley_interval_derivative` derives conditional derivative nonnegativity on the open negative half-line from reflection dominance and the absence of a valley in the conditional law. The mean value theorem and monotonicity convert a mixture valley into a negative derivative witness. The affine derivative inequality gives the candidate ratio and the infimum gives the strict bias bounds.
- `reflectedMixture_modes_interval_derivative` identifies the exact two-local-maximum interval. It uses the existing valley-to-mode theorem with integrability, nonnegativity, no flat intervals, and the two-mode upper bound.
- `reflectedMixture_stationary_of_attained_cutoff` proves that the first derivative is zero at an interior spatial point attaining the clipped ratio. The endpoint derivative has a local minimum there, so its derivative is zero when it is differentiable there.

The new proofs are generic over a differentiable conditional density. In the count law application, weak transfer gives reflection dominance and the half-line and mode bounds. Conditional unimodality supplies the no-valley input, and Fourier regularity supplies differentiability and no flat intervals. The near-one limit of the endpoint already has a separate proof in `BiasIntervalEndpoint`. The new module covers the endpoint equation and the conditional double zero. Attainment, the cusp asymptotics, and the critical quartic and square-root asymptotics are outside this check.

## Integration and verification

The integration import is `import PaperD.Modes.EJPBiasDerivativeCutoff` in `PaperD/Revision.lean`. The module imports `PaperD.Modes.BiasIntervalAssembly` for existing mixture facts and adds two Mathlib calculus imports.

The exact module copy compiled with exit code 0 and no warnings. The run used `lake env lean --root=<scratch>/source-only -o <output.olean> <module.lean>` from `C:/Users/arjun/lean-work/paperD`, with the existing dependency cache. The toolchain was Lean 4.33.1 and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The copy and repository source have SHA-256 `c48e03f17baa6f6a0da6f2f0de9cab2f734d728f1467676cb324fbc014d4a485`.

A second run appended `#print axioms` to the same proof source. The cutoff definition and all three public theorems each depend only on `propext`, `Classical.choice`, and `Quot.sound`. The module contains no proof admissions or custom axioms. This is a module check using cached dependencies, with a source and manifest audit of the existing weak transfer.

Changed paths are [the Lean module](../../kagey-problems/problem131/lean/PaperD/Modes/EJPBiasDerivativeCutoff.lean) and this report.

## Integrated verification

The final revision exposes the helper lemmas to the full declaration audit.
The integrated November 5 build passed for 374 modules and 23,905 declarations,
with only the three standard axioms. The final source hashes are in
`verification-manifest.json`; the earlier local hashes above describe the
sidecar check before that visibility change.
