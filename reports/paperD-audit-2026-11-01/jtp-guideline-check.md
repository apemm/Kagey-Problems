# JTP submission-format check

Checked November 1, 2026 against the [official Journal of Theoretical Probability submission guidelines](https://link.springer.com/journal/10959/submission-guidelines).
Scope: title material, text structure, declarations, data, and submission files.
See `jtp-reference-check.md` for reference eligibility and publication-status checks.

## Requirements and recommendations

The instructions request editable sources and a PDF, a 150 to 250-word abstract, four to six
keywords, MSC codes, corresponding-author details, title-page acknowledgments, decimal
headings with at most three levels, and applicable declarations. Authors must also
complete the submission portal's declaration fields.

Springer's LaTeX template is recommended, not mandatory. The checked page states no
manuscript page limit. Public data deposits and persistent identifiers are encouraged.
Published supplements need identification details and manuscript citations; text
supplements use PDF and the journal's Online Resource naming.

## Changes and retained choices

- The standard `article` class is retained. A class conversion is not necessary to meet
  a template recommendation.
- The abstract falls within the requested range under the source-based count, treating
  formulas as single units. There are six keywords and an MSC line.
- The author block includes the author's name, department, institution, city, state,
  country, email, and ORCID. It now explicitly identifies the corresponding author.
- Acknowledgments have moved into the title material. Funding and author contributions
  remain in the declarations.
- The main numbered structure uses sections and subsections. Unnumbered paragraph
  labels are short signposts. Appendices retain conventional letter labels. The
  extended version's `S6.A` labels belong to the supplied extended manuscript, not a
  separately prepared publication supplement.
- Declarations cover funding, competing interests, ethics/consent, data, code, and the
  sole author's contribution. The separate disclosure describes the assistance used
  during revision. Author verification of those statements remains a pre-submission step.
- The data and code statements distinguish generated computation outputs from external
  data. A pinned repository identifies the proof-code version. A later archive DOI is
  useful for preservation but is not a prerequisite established by the checked page.
- The figures are named `Fig1` and `Fig2`. PDF files serve the LaTeX builds; EPS
  counterparts accompany the journal package. Final visual and font checks are recorded
  with the build and artwork checks.
- The review extract has an identification cover and retains the original page and
  statement numbers in its extracted body. Its purpose is explicit: **For peer review
  only**. It is not presented as an already accepted Online Resource.
- The journal points to the supplied extended manuscript. The unassigned `arxivD`
  bibliography placeholder has been removed.
- Public preprints remain labelled as preprints. Current JTP articles provide direct
  evidence that arXiv references appear in practice. The formal eligibility wording
  and the limits of this evidence are recorded in the reference check.
- `paperD_jtp_submission.zip` collects editable sources, journal and extended PDFs,
  the review extract, figures, the cover letter, and a package README.
  `paperD_arxiv_source.zip` is separate and contains only the arXiv source set.

## Final verification and author checks

The generated `delivery-manifest.json` records final page counts, file inventories,
and hashes. Counts from earlier builds are not final submission counts. Rebuild and
regenerate the packages after any source change. Verify that the final package contains
every imported source and figure and that neither PDF has missing citations or references.

The final check passed: 47 journal pages, 66 extended pages, and seven review-extract
pages including the cover. Both manuscripts compile from the isolated 19-file source
set, and their extracted text matches the delivered PDFs page for page. Every
bibliography entry is cited in its build, with no missing citations, undefined
references, or overfull boxes. All PDF fonts are embedded and none is Type 3.
The 27-file journal package and the arXiv package match the local files byte for byte.
The extracted threshold proof pages match the extended manuscript. These checks are
reproducible with `check_jtp_package.py` and recorded in `pdf-checks.json`.

Visual inspection covered the title page, introduction and intact epigraph, both
figures and captions, the final bibliography page, and the review supplement's cover.
The dedicated title page keeps its acknowledgments separate from the introduction.

The author should review the added regularity, curvature, fourth-moment, center-bound,
and weak-limit arguments before submission. These additions are not part of the
existing Lean formalization. The author should also read the added sources before
affirming the disclosure's reading statement, confirm the cover letter's exclusivity
statement, and complete the journal portal's declarations.

If the editor requests publication of the threshold proofs as supplementary information,
prepare a publication supplement with the required identification, citations, and
Online Resource designation. That decision should not be inferred from the review-only
file prepared here. No journal submission, arXiv upload, or external message was made
by this compliance check.
