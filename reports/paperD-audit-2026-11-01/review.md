# Paper D referee review and revision audit

November 1, 2026. Revised title: **Shape transitions and rare reversals in the elephant random walk**.

## Assessment

The revised paper has a clearer common argument: a finite-step sign theorem controls both
the crossing law and the fixed-memory limit. The quantitative rare-reversal approximation
and the limit-law shape results remain distinct contributions, but the connection is explicit.
The threshold result is no longer presented as a proof of a unique transition in memory.

No unresolved load-bearing error was found in the arguments audited below. Several statements
were strengthened with short proofs. These are additions to the manuscript, not new Lean
theorems. An acceptance probability cannot be justified from this review.

## Strengthened statements

| Location | Previous statement | Revised statement and reason |
| --- | --- | --- |
| Lemma F.4; Theorem 4.2 | Non-strict shape, allowing a flat modal interval | A fixed-point majorant gives `abs(phi_a(t)) <= 2 exp(-c abs(t)^r)` for `1 < r < 1/a`. The densities are entire, so there is one unique mode or two unique symmetric modes. |
| Theorem 4.2 | Number and arrangement of modes | Exactly two inflection points in the unimodal case and four in the bimodal case. Symmetry, the five-block curvature bound, and derivative limits determine the curvature pattern. Isolated zeros without a sign change are not counted as inflection points. |
| Theorem 4.3 | Computer-free bimodality for `a >= 39/40` | Bimodality for `a >= 4/5`. Symmetric unimodality requires kurtosis at least `9/5`; exact fourth moments and a beta-integral estimate give a bound below `141/80`. The replacement proof is shorter. |
| Theorem 2.6(a) | Lower factor `1 - 2 eps` | Factor `(1-eps)^(2-12/(N+4))`, by Jensen's inequality for the first-flip weights. It dominates the old bound and is exact at `N=2`. |
| Theorem 3.9(c) | Weak convergence under `x^3 log^2(N)/N -> 0` | Weak convergence under `x^2 log^2(N)/N -> 0`, with `x -> infinity`. The missing Poisson jumps have total rate `x/N`; total variation transfers the untruncated Landau limit directly. The local-limit hypothesis is not weakened. |

The regularity, curvature, fourth-moment and weak-limit arguments received independent
mathematical checks. The Jensen bound was also compared with exact finite recursions.
No separate priority claim is made for the general regularity argument.

## Corrections made

- Added `N >= 3` and `0 < eps < 1/2` to the abstract's sign statement.
- Added the requested epigraph directly below the Introduction heading, its callback after
  the early-reversal explanation, and the acknowledgment to the author's mother.
- Improved Figure 2's contrast and line-style consistency, and changed its count variable
  to `k`. Figure 1's diagram needed no visual change. See `figures-review.md` for the data check.
- Removed the claim that the computer-assisted calculation settles a unique memory threshold.
  GLRS's conjecture concerns the first-step bias at each fixed memory; the paper addresses
  the fair-start case and classifies its memory ranges outside the short open interval.
- Fixed the Fourier-integral sign in the scaled discussion of S6.
- Specified that the scaled endpoint certificate encloses `sigma^3 g_a''(0)`.
  The unscaled density is not defined at `a=1/2`.
- Corrected the claim about analyticity of scaled moments at `a=1/2`: the even moments and
  the odd moments after division by their square-root factor are analytic.
- Made the count-state domain explicit in Appendix A and repaired the tail proof for a
  requested threshold exceeding the finite population.
- Corrected a verification label that had confused coarse five-decimal agreement with
  containment in a `3.3e-15` bracket. The script now checks exact containment of the
  certified bracket within its coarse bisection bracket.
- Routed the three self-references through the combined-build conditional.
- Retitled the manuscript, PDF metadata, cover letter, repository guides and Lean map.
  Paper F's source citation now uses the new title; its arXiv identifier is still pending.
- Added the two suggested preprints with a precise regime comparison. The moment preprint
  is context, not a new proof input.
- Prepared a separate review-only PDF containing S6 and the bibliography, and updated the
  cover letter so referees receive the threshold proof with the submission.
- Prepared a minimal arXiv source ZIP, metadata, explicit upload list and `spec_version: 1`.
  The unused crossing figure, data, scripts and removed proofs are excluded from the upload.

## Audit scope

The review checked the journal theorem statements and the load-bearing arguments for the
count-chain reduction, crossing monotonicity, first-flip decomposition, center bounds,
family estimates, total variation approximation, Fourier local limit, second-difference
sign propagation, fixed-memory smoothing limit, modality and threshold certificate.
The appendix audit read Appendices A, B and D in full; the modality reviewer read Section 4,
Appendices F and G, and Section S6 in full. The bulk and sign proofs in C and E were
checked separately. The all-even shape was also re-elaborated directly from its Lean source.

Sections S1–S5 were not each re-derived line by line in this audit. Their numerical checks
ran with the suite, and the relevant existing formal statements were included in the Lean
inventory. These checks should not be described as a new complete human proof audit of the
entire extended version. The new regularity proof is a written argument, not an interval
certificate or a kernel proof.

## Verification

- The six-script quick suite passed, followed by a separate rerun of the final revised
  modes script with exact fourth-moment and bracket-inclusion checks.
- The threshold checker validated the hashes and coverage of all stored records. Fresh
  Taylor and Hankel probes passed. The nine full threshold runs were not repeated.
- The Lean build passed. A fresh axiom and completeness audit checked all 308 modules and
  23,503 declarations. It found only `propext`, `Classical.choice` and `Quot.sound`.
- `ShapeAllEven.lean` was directly re-elaborated, in addition to the cached library build.
- Independent appendix checks passed: 14,664 exact Polya comparisons, 3,081 exact family
  identity pairs, 21,816 floating-point upper-factor checks, and 48 exact center checks.
  Floating-point checks are diagnostic, not proofs.
- Both manuscript builds and the isolated arXiv upload build completed. Final PDF page
  counts, source hashes and extract pages are in `delivery-manifest.json`.
- The final journal and arXiv PDFs have 46 and 66 pages, up from 45 and 64.
  The isolated build has identical extracted text on all 66 pages. No undefined references,
  overfull boxes or Type 3 fonts remain. The opening, strengthened-proof and disclosure
  pages were rendered and inspected.

The formalization description retains its named classical hypotheses and states explicitly
that the new strengthenings are not formalized. The unchanged proof-producing certificates
and Lean sources retain their original commit pin. The illustrative modes script has a new
matching run record and is distinguished from that pin.

## Source reading and remaining issues

See `literature-review.md` for source links and reading scope. Vishwakarma's substantive
full text was read in this audit. Murahara–Tokumitsu's introduction and principal local-limit
statement were read, not its full 47-page proof. Relevant GLR/GLRS passages were checked;
they were not both reread in full. No unresolved access request is being hidden by this wording.

The remaining mathematical limitations are the unclassified interval `(z-,z+)`, uniqueness
of the transition there, the biased-start modality problem, and the previously listed
effective-constant/finite-convexity questions. None is presented as solved by numerical
agreement. The title and abstract now distinguish these limits from the proved results.

Before posting, the author should review the new proofs and the drafted disclosure, read
the newly added sources, and confirm the author-history statements. The disclosure does not
say that no proof was proposed by a model: this revision contains new proof arguments.
After the arXiv announcement, insert its assigned identifier and rebuild the journal version.
No submission, email or Zenodo deposit was made. The author subsequently requested a
repository push; the accompanying commit contains this revision and its validation records.

The [JTP author instructions](https://link.springer.com/journal/10959/submission-guidelines)
were checked on November 1. They specify a 150–250-word abstract and 4–6 keywords; the
revised manuscript has six keywords and an abstract within that range. No 45-page cap was
stated on the page examined. The revision retains the original font size and margins.
