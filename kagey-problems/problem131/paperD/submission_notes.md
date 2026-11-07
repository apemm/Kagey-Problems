# Paper D EJP submission files

Focused revision of November 7, 2026. Both entry points build the same
27-page paper, with a seven-page numerical supplement. The combined 70-page manuscript, including the
rare-reversal material, is preserved in archive/combined-2026-11-06.

| File | Purpose |
| --- | --- |
| problem131_memory.pdf | Main EJP manuscript with analytic proofs |
| paperD_supplement.pdf | Complete certificate error analysis and independent moment check |
| problem131_arxiv.pdf | Same paper through the arXiv entry point |
| paperD_ejp_submission.zip | Main paper, supplement, source, figures, cover letter and verification archive |
| paperD_arxiv_source.zip | One declared main entry point and ancillary supplement PDF |
| paperD_verification_archive.zip | Certificate code/data and shared Lean library |
| arxiv_metadata.json | Current title, abstract and page count |

The paper uses the official ejpecp class and includes affiliations, MSC codes,
keywords, and an abstract under 200 words. The accessible
[journal submission-page mirror](https://www.maths.tcd.ie/EMIS/journals/EJP-ECP/about/submissions.html)
allows supplementary files and encourages the class. The current IMS page
could not be retrieved during this check, so this is not a claim about a
newly verified submission policy. Upload the supplement with the main PDF
and ask that its complete numerical proofs be refereed.

## Building

From the repository root, run
python kagey-problems/problem131/paperD/build_submission.py
to build both main entry points and the supplement in isolation, stabilize
the cross-document labels, compare their text and write hashes. The automatic
GitHub build also updates the supplement and generated reference inputs.

The completed Lean audit is in paperD/verification/.
Run Lean only in the separate workspace C:/Users/arjun/lean-work/paperD,
never inside OneDrive. The shared library includes archived results as
specified in its MAP.md. The analytic uniqueness modules construct the H-series
and identify the actual randomized transform and curvature integral. The map
lists their checked steps and cited probabilistic inputs. The numerical certificate
inputs are unchanged.

## Scope

The global bias-boundary monotonicity problem remains open. The finite
central-curvature threshold remains an open question at every length.
The earlier eventual-threshold development is retained in the combined
archive rather than included as an additional theorem. The full boundary curve in the figure is
an illustration, not an interval certificate.

I read Drezner–Farnum and Heyde in full. The two mixture-history citations
use only claims supported by their publisher abstracts.

No journal submission, courtesy email or Zenodo deposit is made by the
build workflow. A Zenodo DOI remains deferred at the author's request.
The cover letter retains the author's stated related-submission statuses.
