# Paper D EJP submission files

Fixed-memory revision of November 6, 2026. Both entry points build the same
complete 33-page paper. The combined 70-page manuscript, including the
rare-reversal material, is preserved in archive/combined-2026-11-06.

| File | Purpose |
| --- | --- |
| problem131_memory.pdf | EJP manuscript with all proofs |
| problem131_arxiv.pdf | Same paper through the arXiv entry point |
| paperD_ejp_submission.zip | Source, figures, manuscript, cover letter and verification archive |
| paperD_arxiv_source.zip | Source-only upload with one declared entry point |
| paperD_verification_archive.zip | Certificate code/data and shared Lean library |
| arxiv_metadata.json | Current title, abstract and page count |

The [EJP submission instructions](https://imstat.org/journals-and-publications/electronic-journal-of-probability/electronic-journal-of-probability-manuscript-submission/)
require the EJP template and PDF submission through EJMS. This manuscript uses
the official ejpecp class. The abstract is under 200 words. The 33-page length
is an editorial target, not a published EJP page limit.

## Building

Run pdflatex three times on problem131_memory.tex and problem131_arxiv.tex.
From the repository root, run
python reports/paperD-ejp-2026-11-05/package_revision.py
to build both packages in isolation, verify their text and write hashes.

The completed Lean audit is in reports/paperD-ejp-2026-11-05.
Run Lean only in the separate workspace C:/Users/arjun/lean-work/paperD,
never inside OneDrive. The shared library includes archived results as
specified in its MAP.md. The structural split does not change Lean sources
or certificate inputs.

## Scope

The global bias-boundary monotonicity problem remains open. The finite
central-curvature threshold remains an open question at every length.
The earlier eventual-threshold development is retained in the combined
archive rather than included as an additional theorem. The full boundary curve in the figure is
an illustration, not an interval certificate.

The author confirmed on November 6 that he read Drezner–Farnum and Heyde
in full. The obsolete abstract-only qualification has been removed.
The source-access records distinguish this confirmation from the earlier
automated retrieval limits. The two mixture-history citations are confined
to claims supported by their publisher abstracts; full texts were not
retrieved in this pass. See reports/paperD-ejp-2026-11-05/sources.md.

No journal submission, courtesy email or Zenodo deposit is made by the
build workflow. A Zenodo DOI remains deferred at the author's request.
The cover letter retains the author's stated related-submission statuses.
