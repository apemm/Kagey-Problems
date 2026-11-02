# Paper D transition and bias-interval verification

The journal manuscript is 51 pages, the same length as the preceding revision.
It now includes a unique fair-start transition and the full centred interval
of bimodal initial biases at every superdiffusive memory. The extended version
has 72 pages. Its complete transition proof and bibliography also appear in
the 9-page review extract. Nothing has been submitted to a journal or arXiv.

The complete Lean build and axiom audit passed: **361 modules and 23,841 theorem
and lemma declarations**. This adds eight modules and 64 declarations to the
preceding audit. There are no unimported source files. Every audited declaration
uses only `propext`, `Classical.choice`, `Quot.sound`, or a subset of them.
The build reports 28 linter or deprecation warnings and no errors. The final
hash check confirms that every audited source still matches its build input.

## Results and formal interfaces

| Result | Paper location | Main Lean entry |
| --- | --- | --- |
| Reflection dominance and absence of a valley on the half favoured by the bias | Proposition F.6 | `BiasedModes.mass_upper_dominates`, `diff_right_no_MP`, `no_right_valley` in `Modes/BiasIntervalFinite.lean` |
| Transfer of the dominant-half properties through the actual span-two local limit | Proof of Theorem 4.6 | `biased_limit_noRightValley`, `conditional_limit_reflection_dominance` in `Modes/BiasIntervalTransfer.lean` |
| One centred open interval of exactly bimodal biases, with unique unimodality outside it and at its endpoints | Theorem 4.6 | `biased_modes_centered_interval_of_smoothing` in `Modes/BiasIntervalAssembly.lean` |
| The lower bias endpoint tends to zero as memory tends to one | After Corollary 4.8 | `bias_endpoint_tendsto_zero_of_uniform_profiles` in `Modes/BiasIntervalEndpoint.lean` |
| Inhomogeneous bootstrap, dominated Fourier differentiation and derivative positivity from an enclosure | Section S6.D | `inhomogeneous_bootstrap`, `hasDerivAt_centralCurvatureFourier`, `centralCurvature_deriv_pos_of_certificate` in `Modes/TransitionBounds.lean` |
| Unique modal transition, with unimodal critical density | Theorem 4.4 | `shape_transition_of_conditional_fourier` in `Modes/TransitionClassification.lean` |

The two generic mixture modules are `BiasMixtureInterval.lean` and
`BiasMixtureIntervalModes.lean`. They prove the affine-descent argument,
openness, symmetry, and the equivalence between valleys and literal local
maxima. The actual-model assembly derives its half-line and mode-count
properties from the finite count recurrence. It does not assume an interval
of bimodal biases. Its published inputs are conditional unimodality, Fourier
smoothing and representation, and the actual lattice local limits.

The transition certificate passed all 19 checks at 1600-bit precision with
1100 moments under `python -O`. On the interior of
`[0.66881285, 0.66881287]`, it proves
`0.68 < d/da g_a''(0) < 0.70` and `-0.09 < g_a''''(0) < -0.07`.
The compact-maximum argument propagates the actual parameter derivative's
tail bound, allowing differentiation under the Fourier integral.

The Arb gamma, reciprocal-gamma and power-series enclosures are **not**
replayed in Lean. The detailed differentiated-smoothing integral reduction
also remains a written analytic proof. These substantive bounds are explicit
inputs to the formal transition interface. The earlier weak-bridge martingale
proof and total variation coupling upgrade retain their documented boundaries.
No claim is made that every proof step in the manuscript is kernel-checked.

The unique transition is global in memory. Uniqueness of the zero of central
curvature is claimed only through `a = 0.6712`. No strict positivity,
continuity, monotonicity or rate in memory is asserted for the lower bias
endpoint. The endpoint convention exactly matches GLRS Remark 2.1(b).

## Checks and presentation

- `verification-manifest.json` and `build-log.txt` record the complete import,
  declaration and axiom audit, including each Lean source hash.
- `final-state.json` records matching source hashes and all release references
  to `paperD-arxiv-v2`. The 14 original reviewed threshold files still match
  commit `b3fe997` byte for byte.
- `pdf-checks.json` records successful isolated builds, exact archive/source
  agreement, complete citation sets, embedded fonts, and no Type 3 fonts.
  Neither TeX log contains an undefined reference, undefined citation or
  overfull box. The review extract matches the extended PDF.
- Nine pages were rendered and inspected: the title, epigraph, new theorems,
  dominant-half proof, verification section and complete transition extension.
  Their locations are in `rendered-pages.json`.
- The crossing and shape sections lost 607 redundant words while retaining
  72 protected mathematical blocks and every distinct inline formula. The
  introduction and verification section were shortened separately. All
  mathematical results and proofs remain available.

The epigraph, callback and acknowledgments are unchanged. The complete main
manuscript is checked against the verified source commit. Commands in the
numerical records use portable names; Python and dependency versions are
recorded separately.

The [research report](../Paper%20D%20transition%20closure.md) records the
independent proof review and precise source-reading scope. James, James and
Qi was read in full. The complete mathematical text and references of
Trinas and Valle were read in this pass. The GLRS comparison was a targeted
rereading. Heyde and Drezner–Farnum still need full-text comparison. No
unqualified claim of first priority is made for the finite-chain theorem.

## Reproduction

Use Python with `numpy`, `scipy`, `mpmath`, `python-flint`, `pypdf` and
`pypdfium2`, Lean 4.33.1, and Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`.

```text
python reports/paperD-transition-2026-11-01/run_verification.py --workspace C:/Users/arjun/lean-work/paperD --toolchain C:/Users/arjun/.elan/toolchains/leanprover--lean4---v4.33.1/bin
python reports/paperD-transition-2026-11-01/run_release_numerics.py --commit <source-commit>
python reports/paperD-transition-2026-11-01/verify_release_build.py --commit <source-commit> --workspace C:/Users/arjun/lean-work/paperD --toolchain C:/Users/arjun/.elan/toolchains/leanprover--lean4---v4.33.1/bin
```

The absolute runtime paths describe this machine. The numerical runner exports
the specified commit to an isolated directory and runs the seven-script quick
suite. It verifies the archived threshold records, reruns three short threshold
probes, and freshly runs the complete new derivative certificate. It does not
rerun the nine original heavy threshold jobs or the older full center and
convexity sweeps. The final build runner rebuilds the committed Lean sources
and checks that they match the full axiom audit. The `release-*-verification`
records identify the verified source commit and precise check scope.

`package_revision.py` creates both upload archives from the compiled PDFs and
current source set. `check_jtp_package.py` compares them with independent builds
under `.pdf-build/paperD-transition-clean-2026-11-01/build`. `render_pages.py`
recreates the inspected page images. The release tag is immutable: later
scientific source changes need a new tag and verification run.
