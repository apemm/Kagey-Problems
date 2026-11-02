# Paper D posting and submission files

Revision of November 1, 2026. Nothing has been posted or submitted by this workflow.

## Read and review

- `problem131_memory.pdf`: journal manuscript, with its proofs and appendices.
- `problem131_arxiv.pdf`: the longer version, including Sections S1–S6.
- `threshold_proofs_review.pdf`: Section S6 and the bibliography, extracted for journal review.
  It retains the page and statement numbers of the longer version. Read it with the journal manuscript.
- `cover_letter.md`: draft journal cover letter, describing the review-only supplement.
- `../../../reports/paperD-audit-2026-11-01/`: audit, source-reading record, and validation outputs.

The current builds have 46 journal pages and 66 arXiv pages, compared with 45 and 64 before
the revision. The added regularity and curvature arguments account for most of the increase.
The layout, font size, and margins have not been compressed.

## arXiv upload

`paperD_arxiv_source.zip` contains only the following 19 files:

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
app_threshold.tex
or_family_proofs.tex
online_resource_body.tex
online_resource_bib.tex
figures/family.pdf
figures/shape.pdf
```

The top-level file is `problem131_arxiv.tex`. `00README.json` declares it and includes
`spec_version: 1`. The bibliography is inline. The source ZIP was built separately from
this exact file set. Do not add `crossing.pdf`, `removed_proofs/`, `data/`, scripts,
audit files, or the review-only PDF to that ZIP.

Use `arxiv_metadata.json` for the title, abstract, comments, and category suggestions.
The primary category is `math.PR`, with `cond-mat.stat-mech` suggested as a cross-list.
`math.CO` is optional. The non-exclusive arXiv license leaves copyright with the author;
select the license in the upload interface. No license selection has been made here.

## Before posting or journal submission

1. Review the new written proofs: Lemma F.4, the curvature clause of Theorem 4.2,
   Theorem 4.3's fourth-moment proof, the Jensen bound, and the weaker weak-limit hypothesis.
   The current Lean sources do not formalize these strengthenings.
2. Confirm the disclosure's author-history statements. It records Opus literature search
   and citation checking, the author's reading, Codex revisions, and GPT-6 Astra edits to
   Lean. It also identifies the mathematical additions developed in this revision.
   Read the two newly added preprints before affirming that every cited source has been read.
3. After arXiv assigns an identifier, replace the `arxivD` placeholder in
   `problem131_memory.tex`, rebuild the journal PDF, and add that identifier to Paper F's
   citation. Its title has already been updated.
4. Attach `threshold_proofs_review.pdf` as review-only material with the journal submission.
   If the editor requests it as published supplementary information instead, adjust the
   designation and cover letter.
5. A Zenodo archive of the proof-code commit remains an optional later action. No DOI has
   been created or guessed.

The [current JTP instructions](https://link.springer.com/journal/10959/submission-guidelines)
request a 150–250-word abstract, 4–6 keywords, editable source files, and a compiled PDF.
The present version follows those length and file requirements. The page examined on
November 1 did not state a 45-page cap; 45 pages was the earlier editorial target.

To regenerate the source ZIP, metadata and referee extract after rebuilding both PDFs, run
`python reports/paperD-audit-2026-11-01/package_revision.py` from the repository root.
Its manifest records the source and PDF hashes.
