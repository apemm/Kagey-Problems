# Paper D EJP submission files

Revision of November 5, 2026.

The journal and arXiv PDFs now contain the same complete paper. Use the new EJP
package. The older JTP archive and threshold review extract are historical files.
They are not part of this submission.

| File | Purpose |
| --- | --- |
| `problem131_memory.pdf` | Complete EJP manuscript, including every threshold proof |
| `problem131_arxiv.pdf` | The same manuscript built through the arXiv entry point |
| `paperD_ejp_submission.zip` | Editable source, figures, manuscript, cover letter, numerical records and verification material |
| `paperD_arxiv_source.zip` | Source-only arXiv upload, with one declared entry point |
| `paperD_verification_archive.zip` | Certificate code/data and Lean sources for archival deposit |
| `cover_letter.md` | EJP cover letter |
| `arxiv_metadata.json` | Current title, abstract, categories and page count |
| `../../../reports/paperD-ejp-2026-11-05/README.md` | Revision decisions, proof review and remaining limits |
| `../../../reports/paperD-ejp-2026-11-05/delivery-manifest.json` | Package inventory and SHA-256 hashes |

## Journal requirements

The [current EJP submission instructions](https://imstat.org/journals-and-publications/electronic-journal-of-probability/electronic-journal-of-probability-manuscript-submission/)
require the EJP LaTeX template and a PDF submission through EJMS. This revision
uses `ejpecp` version 1.12.3, dated March 4, 2026, from the
[official template repository](https://vtex-soft.github.io/texsupport.ims-ejpecp/).
The instructions permit referee suggestions. The
[production instructions](https://imstat.org/journals-and-publications/electronic-journal-of-probability/electronic-journal-of-probability-preparation-of-manuscripts/)
prefer an inline bibliography and no separate macro/style files beyond the class.
The EJP source package includes every section file needed by
`problem131_memory.tex`. No external macro file or publication supplement is
needed. Keeping the section boundaries preserves the repository PDF's layout.

No numerical abstract limit or maximum article length was found in these official
instructions. The abstract is about 200 words. EJP describes itself as a venue for
full-length probability papers, so the manuscript is kept together. This is an
editorial judgment, not an assurance of acceptance.

## Before public posting

1. Read the new results and the complete manuscript. The local bias-width law,
   critical expansion and enlarged mode range are written proofs. The formal
   coverage is stated separately in `lean/PaperD/MAP.md`.
2. Confirm the cover letter's submission-status statements and any referee
   conflicts. The related-paper statuses are retained from the existing letter.
3. Drezner–Farnum (1993) was checked through the publisher's abstract, which
   explicitly mentions bimodality. Its full text remains unavailable in this
   review. The detailed transition-rule comparison uses James–James–Qi (2008).
4. Use the tagged GitHub verification archive for this revision. A Zenodo
   deposit is deferred at the author's request. No DOI has been reserved.
5. Post the preprint, then use its real public identifier in the courtesy email
   drafts and journal submission. No arXiv or journal submission has been made
   by this revision workflow. Courtesy emails have not been sent before a
   public preprint is available.

## Rebuilding

Compile `problem131_memory.tex` with `pdflatex` three times. Compile
`problem131_arxiv.tex` the same way. Then run
`python reports/paperD-ejp-2026-11-05/package_revision.py` from the repository root.
The script builds and checks both source packages in isolation, writes hashes,
and renders review pages. It does not submit or publish anything.

Run the Lean verifier in the existing workspace outside OneDrive:

```text
python reports/paperD-ejp-2026-11-05/run_verification.py --workspace C:/Users/arjun/lean-work/paperD --toolchain C:/Users/arjun/.elan/toolchains/leanprover--lean4---v4.33.1/bin
```

The numerical verification records state the precision, software versions and
source hashes. From the paper's directory, `python -O check_critical_shape.py`
independently checks the threshold endpoints. The refined checks are
`python -O certify_critical_constants.py` and `python -O certify_landau_gap.py`.
The full phase boundary is a numerical illustration. The separate hatched
region plots the sufficient moment inequality proved in the paper.
