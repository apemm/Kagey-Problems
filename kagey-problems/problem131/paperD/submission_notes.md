# Paper D posting and submission files

Revision of November 2, 2026. Nothing has been posted or submitted by this workflow.

## Read and review

| File | Purpose |
| --- | --- |
| `problem131_memory.pdf` | Journal manuscript, including its appendices |
| `problem131_arxiv.pdf` | Extended manuscript, including Sections S1 to S6 |
| `threshold_proofs_review.pdf` | Identification cover, Section S6, and bibliography for journal referees |
| `cover_letter.md` | Draft letter explaining the contribution and review material |
| `paperD_jtp_submission.zip` | Journal package with editable sources, all three PDFs, figure files, cover letter, and package README |
| `paperD_arxiv_source.zip` | Separate source-only package for arXiv |
| `arxiv_metadata.json` | Title, abstract, suggested categories, and build-derived page counts |
| `../../../reports/paperD-final-audit-2026-11-02/delivery-manifest.json` | Current file inventory, page counts, and hashes |

The review extract retains the extended manuscript's page and statement numbers after
its identification cover. Read it with the journal manuscript. It is designated **For peer
review only**, not a publication supplement. The extended manuscript is also supplied so
that every pointer in the journal manuscript has an accessible destination. It is not
described as an already posted arXiv paper.

The final audit folder records the consistency review and package validation. The
earlier `reports/paperD-audit-2026-11-01/` folder contains the source-reading record,
`jtp-guideline-check.md`, and `jtp-reference-check.md`. The current manifest records
the final page counts. Historical counts in `README.md` describe earlier builds.

## Journal submission

Use `paperD_jtp_submission.zip` as the journal file package. It includes the sources needed
to rebuild the manuscript and extended version. Figures are named `figures/Fig1.pdf` and
`figures/Fig2.pdf`, with EPS counterparts for the journal's preferred vector format.
Use the archive's README to assign files to the submission system's categories. Attach
`threshold_proofs_review.pdf` as review-only material, and identify the extended PDF as
additional review material. The handling editor can decide whether any of this material
should become published supplementary information.

The [official JTP instructions](https://link.springer.com/journal/10959/submission-guidelines)
request a 150 to 250-word abstract, four to six keywords, MSC codes, editable sources, and
a compiled PDF. They recommend the Springer LaTeX template; they do not require it.
The standard `article` class is retained. No manuscript page cap was stated on the page
checked on November 1, 2026. The earlier 45-page target was an editorial target, not a
verified journal rule.

Public preprints remain explicitly labelled as preprints. The guidelines restrict
bibliographies to published or accepted work, but current JTP articles include arXiv
references. `jtp-reference-check.md` records the examples and the limits of that evidence.
No acceptance status has been inferred or invented.

## arXiv upload

`paperD_arxiv_source.zip` contains the following source files:

```text
00README.json
problem131_arxiv.tex
problem131_memory.tex
sec_intro.tex
sec_erw_crossing.tex
sec_erw_shape.tex
sec_bulk_applications.tex
sec_verify.tex
app_erw_bounds.tex
app_erw_profile.tex
app_erw_bulk.tex
app_erw_signs.tex
app_modes.tex
app_bias_interval.tex
app_threshold.tex
or_family_proofs.tex
or_transition_proofs.tex
online_resource_body.tex
online_resource_bib.tex
figures/Fig1.pdf
figures/Fig2.pdf
```

The top-level file is `problem131_arxiv.tex`. `00README.json` declares it and includes
`spec_version: 1`. The bibliography is inline. The source ZIP is separate from the journal
package. Keep data, scripts, audit files, removed proofs, and the review-only PDF out of it.

Use `arxiv_metadata.json` for the title, abstract, comments, and suggested categories.
The primary category is `math.PR`, with `cond-mat.stat-mech` suggested as a cross-list.
`math.CO` is optional. Select the license in the upload interface. The suggested
non-exclusive arXiv license leaves copyright with the author; no selection has been made.

## Before posting or journal submission

1. Review the statement correspondence for the formalized additions: Lemma F.4,
   the strict modes and curvature in Theorem 4.2, Theorem 4.3's fourth-moment
   argument, the Jensen bound, and the enlarged weak-limit range. The explicit
   published-law hypotheses and build evidence are listed in
   `reports/paperD-formalization-2026-11-01/README.md` at the repository root.
   The subsequent all-bias theorem and uniform near-one profiles are mapped in
   `reports/paperD-strengthening-2026-11-01/README.md`. The latter retains the
   fixed-memory weak bridge as an explicit input. Resolve or qualify the
   outstanding generalized-binomial full-text comparisons listed in
   `reports/Paper D transition and modes.md` before making a priority claim.
   The unique transition, centred bias interval and their formal/numerical
   boundaries are recorded in `reports/paperD-transition-2026-11-01/README.md`.
   The current reading record is `reports/Paper D transition closure.md`.
2. Confirm the disclosure's author-history statements. Read the added Murahara-Tokumitsu
   and Vishwakarma preprints before affirming that every cited source has been read.
   The audit's reading record describes the audit's scope, not the author's reading.
3. Check the compiled journal and extended PDFs, including figure labels, links,
   references, and the review extract's identification cover. Confirm that the archive
   inventory and hashes describe these final files.
4. Confirm that the manuscript is not under consideration elsewhere, as stated in the
   cover letter. Complete the journal portal's funding, contribution, competing-interest,
   and data/code fields; manuscript declarations do not fill those fields automatically.
5. If an arXiv identifier is assigned before journal submission, add the real identifier
   to the journal's extended-version pointer and Paper F's citation, then rebuild.
   There is no placeholder identifier in the journal bibliography.
6. If the editor requests a publication supplement, replace the review-only designation
   with the required Online Resource identification, captions, and manuscript citations.

A Zenodo archive of the proof-code commit is optional. No DOI has been created or guessed.

To regenerate the packages, metadata, and review extract after rebuilding both manuscripts
and `threshold_review_cover.tex`,
run `python reports/paperD-final-audit-2026-11-02/package_revision.py` from the repository root.
