# Paper D editorial corrections, November 2, 2026

The abstract, introduction, cover letter and generated arXiv metadata now
state that the centred interval of bimodal biases is empty exactly when
`a <= a_*`. Section 5 counts five numerical certificates and links the full
source inventory and axiom audit to
[evidence commit c24791a](https://github.com/apemm/Kagey-Problems/tree/c24791af4f3a9aa0d985fce1b0a2a68f03f33432/reports/paperD-headline-audit-2026-11-01).
The verified proof-code release remains `paperD-arxiv-v3`.

The cover letter qualifies the Drezner–Farnum identification by citing the
formulation of James, James and Qi. The original-source comparison remains
pending receipt of the library copy. It also identifies C1 by its full title
and notes that it is under consideration at the Journal of Theoretical
Probability, as recorded in the repository and confirmed by the author.

These changes do not alter a theorem, proof, Lean module, numerical program
or certificate. The existing formal and numerical audit remains the relevant
verification of those unchanged sources. No new Lean or numerical run is
claimed for this editorial revision.

The document build uses `.pdf-build/paperD-editorial-2026-11-02`.
`package_revision.py` regenerates the PDFs, review extract, metadata and both
upload archives, and copies the source set to
`.pdf-build/paperD-editorial-clean-2026-11-02`. Compile both manuscripts in
that copy with output directory `build`, then run `check_jtp_package.py`.
The check compares the isolated builds, citation sets, embedded fonts and
every file in both upload archives. `pdf-checks.json` and
`delivery-manifest.json` identify the resulting files.

Both ordinary and isolated builds passed. The journal version has 52 pages,
the extended version 73, and the review extract 9. The arXiv abstract has
1,543 characters. All 21 arXiv-package files and 29 journal-package files
match their current source bytes. Fonts are embedded, citations resolve,
and the build logs have no overfull boxes. The rendered abstracts and
verification pages were inspected. The evidence-commit hyperlink is present
on page 28 of both manuscripts and targets the commit containing the manifest.
The proof sources, numerical programs, certificate data and Lean library
were compared with `paperD-arxiv-v3` and are unchanged.

The earlier headline-audit records and all three source-release tags are
preserved. This revision has not been submitted or posted, and no message
has been sent to the conjecture's authors.
