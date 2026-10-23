# Integration and verification record

The parent applied the reviewer feedback and the localized precision findings from the mathematical audit. The accurate disclosure was preserved byte for byte. No Lean proof file was edited or built. This is a revision and editorial audit, not a complete certification of the manuscript.

## Implemented

- Abstract shortened from about 308 words to 235. Removed the duplicate Contributions subsection and shortened the planar heuristic. Kept the main introductory theorem statements and all principal results.
- Weak-field hypotheses and the uniform-start Potts interpretation corrected. Coincident lines use the field-shifted constant. The missing log d was restored. The compact field set no longer collides with the crossing function Xi.
- Historical B boundary claim qualified so that sizes of small coordinates can drop out while their number still changes the leading and logarithmic coefficients. The citation is pinned to arXiv:2610.09258v1.
- Consolidated the refresh/Laguerre polynomial definition in Section 5. Renamed the Appendix C nuisance coefficients, weights and polynomial variable, and the higher-order Taylor polynomials/power sums/log-amplitude parts.
- Corrected the domains of the two Appendix D bounds, the finite-window coordinates, local covariance description, undeclared normalized switch coordinate, supplement references, and duplicated monotonicity/constant explanations.
- Corrected the approximate-saddle rounding explanation without weakening the stated error bound. Qualified when the next correction is resolved. Added the zero-generator case and corrected prose about irreducible admissible faces and unresolved identical lines. The compressed weak-field proof was independently reread and approved by the math reviewer.
- Moved the detailed higher-order Laplace proof and complete next-term proof intact to supplement S3/S4. Retained Lemma B.2, the full next-term proposition, coefficient formulas and leading Laplace proof in the main paper. Both PDFs must accompany the journal submission. Supplement support is verified in the official author package. A specific current policy on supplementary proofs was not independently confirmed.
- Added the vector analytic complete-graph envelope figure. Its formulas and all 15 supports of K4 were checked. It explicitly depicts limiting scores, not finite-N ties. A final layout pass places it before the edge/full-hierarchy examples so it does not interrupt the vertex-law discussion.
- Added Hervé–Ledoux, Bouguet–Cloez and a narrowly worded Iltis comparison to the literature discussion. Iltis was available only through publisher abstract/snippets in the research task, so no detailed theorem/hypothesis comparison is claimed. The Kim–Landim reference now pins v2 for Lemma 5.7.
- Archived all 41 historical B files under `kagey-problems/problem131/archive/paperB`, preserving all mathematical sources, scripts, data and PDFs. Only its live README was updated. The Lean library `lean/PaperB` stays in place because C uses it. Active runner paths, navigation, program-figure data path and ledger links were updated.
- Extracted logS, uN_runs, paperA_law and uN_dp unchanged into `common/two_state.py`. Both C's sticky checker and E's planar checker import the shared implementation. E no longer imports the sticky-prior verification script. Updated E's code-availability dependencies and A v3 citation and rebuilt E because its source changed.
- Updated E's existing Lean-map rows to its current 3.x numbers, preserving the exact distinction between algebraic checks and asymptotic results. No new formalization is claimed. C's map records current theorem numbers and final page counts.

## Verification

- `tmp/paperC-ejp-review-2026-10-22/cleanup_checks.json` records identical function ASTs after extraction, successful imports from both papers, normalized probabilities and agreement of independent two-state crossing methods at N=4,16,64,256. Errors were below 2e-13.
- `tmp/paperC-ejp-review-2026-10-22/weak_field_check.txt` records all 22 assertions of the focused weak-field checker passing. No full expensive sweep was run.
- Archive hashes were checked immediately after the move. Final checks confirmed that all 40 historical mathematical/code/data/PDF files are hash-identical; only the archive README changed.
- `tmp/paperC-ejp-review-2026-10-22/build_checks.json` records the latest cyclic main/supplement builds and E build. The final builds are 64 pages main, 14 pages supplement and 25 pages for E, with no unresolved references/citations or overfull boxes.
- PDF page renders and contact sheets are under `tmp/paperC-ejp-review-2026-10-22/render`. New figure print/grayscale/bilevel QA is in `paperC/figures/qa`.

## Scope boundaries

The implementation is recorded in commit [4c18775](https://github.com/apemm/Kagey-Problems/commit/4c187751182d0fa33097dc7eddcac289173ba7db), which includes the final code layout, shared routines and historical B archive. The article's availability statement pins this revision. The compiled article and supplement are rebuilt after inserting that pin. The compact build, archive-preservation and focused-check records are saved in the adjacent `validation` folder.

The user's request targets merged C. The attached plan is for D, E and F. Applied its C-related dependency, citation, archive and Lean-map recommendations. Did not retitle/revise D or F, invent disclosures for them, create future release tags, upload anything to arXiv, or submit to a journal. E's future release tag still needs creation at posting, as its own plan says. The original D/E/F posting calendar is a plan, not a verified journal or arXiv requirement.

The paper has a coherent EJP case. The residual editorial risk is the length and the extent of the advance over sharp occupation-density/spectral methods, not a major mathematical defect established by this audit. Optional further cuts should remove an example or move a coherent independent proof block, rather than compress the boundary-control and maximization arguments that support the leading theorems.
