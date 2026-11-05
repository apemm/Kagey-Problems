# Paper D revision for EJP

November 5, 2026

The manuscript now leads with the resolved Guérin–Laulin–Raschel–Simon
bias-interval conjecture. The fixed-memory transition, its local geometry and
the rare-reversal results share one finite shape argument. Keeping them in
one paper is defensible. The complete submission is 59 pages, compared with
72 pages for the previous complete extended version. The previous shorter
journal PDF omitted essential threshold proofs and is not the right length
comparison.

The mathematical revision is substantial, but not every proposed research
target is settled. Do not describe the unfinished extensions below as proved.


## What changed

| Request | Result |
| --- | --- |
| Put the GLRS conjecture first | New title and two-part, 197-word abstract; conjecture opens the introduction; Theorem 1.1 gives the bias interval and unique threshold. |
| Reorder the main results | Bias classification, near-one profile and finite shape bounds precede the rare-reversal theorems. |
| Explain the common proof | Added a proof-architecture subsection explaining boundary histories, the dominant half, weak transfer, curvature and the near-one connection. |
| Remove the extended-version dependency | All essential threshold proofs, including the differentiated smoothing argument, are now in the article. Both PDF entry points contain the same complete paper. |
| Trim secondary material | The second-order center expansion, separate tail theorem, odd-center crossing and assay-likelihood material are excluded. Their historical sources remain in the repository. The proven height-based convexity window stays. |
| EJP format | Uses the official `ejpecp` class, version 1.12.3. Removed Springer declarations and Online Resource language. |
| Describe the bias boundary | Added a variational equation, stationary equations at an attained endpoint, and the limit `b_a -> 0` near memory one. No attainment or uniqueness of the optimizer is assumed without a hypothesis. |
| Critical shape | Added a negative quartic coefficient at criticality, square-root mode locations and quadratic peak excess, with constants expressed through certified derivatives. |
| Bias interval near criticality | Added the three-halves opening law, a coefficient between 9 and 11, and continuity and strict widening near the threshold. At a boundary the stationary location is asymptotic to the fair mode divided by the square root of three. |
| Phase diagram | Added a numerical bias diagram and three density panels. The caption distinguishes the illustration from certified bounds. |
| Computation-free range | Extended the fourth-moment argument from `a >= 4/5` to `a >= 79/100` using an exact power comparison. Global uniqueness of the transition still uses certificates. |
| Explicit mode constant | Replaced unspecified `K` by `400`. The length threshold remains existential. |
| Wider rare-reversal range | Mode localization now explicitly applies whenever `x -> infinity` and `x^3 log^2 N / N -> 0`, with a displayed rate. |
| Independent threshold check | A real-parameter moment evaluation confirms both endpoint signs without using the parameter Taylor models that generated the bracket. It also bounds the conditional slope needed for the bias cusp. |
| Lean | Three new modules check the derivative cutoff, attained-boundary stationary equations, analytic range and explicit mode constant. Helpers are included in the full declaration audit. |
| Literature and cover letter | Added Trinas's last-return paper and Dekking–Kong; clarified the Drezner–Farnum credit; rewrote the letter around the resolved conjecture. |

## What remains open

- Global continuity and monotonicity of the bias width have not been proved.
  The variational formula alone does not supply compactness of all maximizing
  locations uniformly in memory. Local continuity and strict monotonicity near
  the threshold are proved.
- A unique finite-length memory threshold, convergence to `a_*`, and a rate
  need parameter and derivative control of the lattice law. A bound on the
  number of modes does not establish these claims. The two finite numerical
  thresholds already in the paper remain illustrations.
- The stronger convexity window beginning at `2m_*+1` is not proved for every
  length. The retained maximum-height window is a theorem for every even
  `N >= 8`; it can be smaller and must not be renamed as the stronger result.
- The widened Landau regime is still a rare-reversal regime. Neither a uniform
  density approximation up to fixed memory nor rates for the near-one profile
  are established. Weak convergence cannot supply those rates on its own.
- A nonfair innovation probability in the Drezner–Farnum model is different
  from changing the first-step bias. The reflected-mixture proof does not
  automatically extend to that model.
- In dimensions at least two, the fixed-point theorem supplies densities but
  not the one-dimensional variation-diminishing order used here. The usual
  axis-step model is not rotationally invariant, so a radial crater claim
  would itself need a precise formulation. No multidimensional shape theorem
  was added.

These extensions would enlarge the project substantially. The revised paper
does not need them to state a clear advance. Their absence does prevent a
literal claim that every ambition in the request has been completed.

## Proof and verification review

[proof-review.md](proof-review.md) records the new deductions and their limits.
The complete Lean build and declaration audit are recorded in
[verification-manifest.json](verification-manifest.json) and
[build-log.txt](build-log.txt). All checks passed for 374 modules and 23,905
declarations, with zero unimported files. Only `propext`, `Classical.choice`
and `Quot.sound` occurred. The build retained 28 existing linter/deprecation
warnings. The map in `lean/PaperD/MAP.md` distinguishes
formal deductions from cited probabilistic inputs and numerical enclosures.
The quartic, square-root and three-halves expansions remain written proofs.

The new short pointwise check runs with Python 3.12.14 and python-flint 0.9.0,
at 2000-bit precision. Endpoint checks use 1800 moments; the conditional-slope
check uses 1200. Its two signs are approximately `-1.1275e-15` and `1.128e-15`,
with outward radii below `3.3e-19`. The conditional derivative at criticality
is in `(0.097074, 0.097076)`. The check passed under `python -O`.

This is an independent evaluation path, not an independent implementation of
Arb or the smoothing theorem. The full old parameter sweep was not repeated.
The retained certificate records and their source hashes remain part of the
evidence. Numerical figure agreement under grid refinement is not a rigorous
phase-boundary enclosure.

The package script verifies both source packages in isolation, checks all
references and overfull boxes, compares extracted journal/arXiv text, records
hashes, and renders representative pages. The official class produces a benign
`pagebackref` option warning; it does not affect references or PDF output.

## Editorial assessment

The strongest reason for EJP consideration is the resolved conjecture from a
recent EJP paper, followed by the precise critical geometry. The long
rare-reversal half earns its place through the same finite shape bounds and
the near-one profile. Keeping one paper is preferable to splitting before
an editor has assessed that connection.

The length remains a possible referee concern. The most defensible cuts were
the secondary extensions, rather than essential threshold proofs. A later
editor-requested split could put the fixed-memory shape results first and the
quantitative mutation/crossing analysis in a separate article. ECP is not an
automatic home for the latter: its official guidance concerns papers shorter
than twelve pages.

The review found no counterexample or missing hypothesis in the new local
deductions after the corrections recorded in the proof review. That is not a
guarantee of acceptance or an independent specialist's endorsement of every
existing theorem. The remaining source-access limitation is explicit in
[sources.md](sources.md).

## Posting and archive status

The protected disclosure is unchanged. Its original text and normalized hash
are saved beside this report.

The current packages and metadata are linked from the paper's
`submission_notes.md`. `paperD-ejp-v1` is the release tag for this revision.
The verification archive is published on GitHub. A Zenodo deposit is deferred
at the author's request. No DOI has been reserved, and no arXiv identifier
or journal submission has been created here.
Courtesy messages are drafted for use after a public preprint exists.
The cover letter retains the related-paper submission statuses from the old
letter; the author should confirm them and referee conflicts in the portal.

No other paper was edited.
