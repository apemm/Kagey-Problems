# Paper D formalization of the November 1 additions

This report covers the five mathematical additions to *Shape transitions and rare
reversals in the elephant random walk*. The entry point is
[`PaperD.Revision`](../../kagey-problems/problem131/lean/PaperD/Revision.lean), imported
by the full `PaperD` library. It does not claim a formalization of the whole paper
or of every cited result.

## Results and proof correspondence

| Manuscript result | Lean result, below `Kagey131.PaperD` | What the proof establishes |
| --- | --- | --- |
| Theorem 2.6(a) | `thm_erw_bounds_a_jensen`, `jensen_factor_ge_linear` | The first-flip weights give exponent `2 − 12/(N+4)` and recover the previous linear factor. The endpoint `N=2` is included. |
| Theorem 3.9(c) | `RevisionWeak.thm_landau_quadratic_final` | Weak convergence of the centered, scaled walk under `x → ∞` and `x² log² N/N → 0`. |
| Lemma F.4 | `Modes.charFun_stretched_decay_of_density` | For every `1 < r < 1/a`, the conditional characteristic function is bounded by `2 exp(−c |t|^r)` for some positive `c`. |
| Lemma F.4 | `Modes.fair_entire_extension_from_probability_measure` | An actual entire complex function agrees with the fair-start density on the real axis. |
| Theorem 4.2 | `Modes.strict_shape_of_conditional_fourier` | Strict unimodal or bimodal branches, the exact set of local maxima, and all strict convexity and concavity intervals. |
| Theorem 4.2 | `Modes.StrictUnimodalShape.inflections`, `Modes.StrictBimodalShape.inflections` | The complete inflection sets are `{−d,d}` or `{−d₂,−d₁,d₁,d₂}`. The positive thresholds satisfy `0 < d₁ < c < d₂` in the bimodal case. |
| Theorem 4.3 | `Modes.main_limit_four_fifths`, `Modes.strict_bimodal_four_fifths` | Bimodality for `4/5 ≤ a < 1`; the second theorem also gives the strict shape and curvature partition. |

The Jensen proof applies convexity to the exact first-flip weights. It needs no
additional probabilistic input beyond the already formalized finite walk.

The weak-limit proof uses the finite-tree coupling to control characteristic
functions, then applies Mathlib's Lévy continuity theorem. It does not assume
the manuscript's total variation bound and does not use the earlier separate
Scheffé hypothesis.

The analytic proof first constructs a barrier for the smoothing inequality, then
proves exponential integrability of the Fourier transform. Differentiation
under the integral gives an entire extension and bounded first and second
derivatives that vanish at infinity. The identity theorem excludes flat
intervals for the density and its first derivative.

The curvature proof transfers the finite five-sign bound to the second
derivative by differentiating the Gaussian mollification on the density side.
It derives the curvature thresholds from the sign pattern. The final theorems
do not assume those thresholds, strictness, analyticity, or an inflection count.
`IsStrictInflection` means a change between adjacent intervals of strict
convexity and strict concavity. A zero of the second derivative without such a
change is not counted.

The fourth-moment proof establishes the sharp unimodal kurtosis bound `9/5`
directly by comparing an even decreasing density with a uniform density of the
same variance. A quartic polynomial controls the signed difference. The beta
integral and a rational bound then put the stated moment ratio below
`141/80 < 9/5`. Khinchine's representation is not a hypothesis.

## Explicit assumptions

The following mathematical inputs remain hypotheses, not custom Lean axioms:

- **Density and convergence in law:** the existing `DensityHyp` and
  `LawConvHyp` interfaces encode the published limit-law input. Density
  normalization is derived from convergence against the constant test function.
- **Conditional fixed point and fair inversion:** the smoothing inequality
  concerns the conditional-first-step characteristic function. The fair-start
  density is the inverse Fourier transform of its real part. The two functions
  are kept separate throughout. `conditionalFourierHyp_of_probability_measure`
  derives continuity, the unit bound, conjugate-norm symmetry, and decay from a
  probability law with a measurable density.
- **Raw moments:** `GLRFourthMomentsHyp` states integrability and the published
  second- and fourth-moment formulas. It does not assume the kurtosis comparison
  or the conclusion of bimodality.
- **Weak-limit classical inputs:** lattice Fourier inversion, the compound
  Poisson characteristic-function formula, and Efron–Stein remain the library's
  named hypotheses LFI, CP, and ES.

The almost-sure limit theorem, distributional fixed-point identity, Fourier
identification, and published raw moment formulas have not been reconstructed
from the underlying probability space in this task. Their consequences above
are formal proofs with these inputs visible in the theorem statements.

The earlier total variation upgrade, fixed-memory bridge, threshold certificate,
and likelihood theorem remain outside this formal coverage.

## Verification

**Passed:** the full library build and axiom audit cover 331 modules and 23,638
theorem/lemma declarations, including 135 declarations in 23 added modules.
The import closure leaves no source modules unimported. Every recorded source
hash was checked against the working files after the audit; all match. The 20
reported warnings are linter or deprecation warnings, not proof admissions.

The toolchain is Lean 4.33.1 with the repository's pinned Mathlib revision
`0df444a360ea`. The full-library audit runs `lake build PaperD`, checks the import
closure, rejects proof admissions, compares source theorem declarations with
Lean's theorem inventory, and requests `#print axioms` for every theorem.

The machine-readable results are in `verification-manifest.json`; the complete
transcript is in `build-log.txt`. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. Existing Mathlib and unchanged library build artifacts
can be reused; this is not described as a clean rebuild of all dependencies.

Run from the repository root, using a Lake workspace outside OneDrive whose
`PaperD` source directory points to this checkout:

```text
python reports/paperD-formalization-2026-11-01/run_verification.py --workspace C:/Users/arjun/lean-work/paperD
```

An independent source review checked the manuscript correspondence, the
conditional/fair distinction, inverse-Fourier sign and normalization, the
relation `a=1−2ε`, the included `a=4/5` endpoint, and the derived curvature
thresholds. Kernel checking and this correspondence review answer different
questions; neither replaces examination of the published input hypotheses.
