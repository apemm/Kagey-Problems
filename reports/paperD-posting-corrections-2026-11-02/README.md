# Paper D corrections before posting

## Scope and decisions

- The abstract, introduction and cover letter use an approximation sign for
  `a_* ≈ 0.6688128600146`. Exact rational comparison puts the entire certified
  bracket inside the rounding cell `[0.66881286001455, 0.66881286001465)`,
  but the displayed decimal itself lies inside the bracket. Its status is
  therefore a rounded value, not a certified decimal prefix.
- The introduction identifies the Trinas–Valle local limit as an alternative
  from an unrefereed preprint. The proof uses weak convergence and the existing
  weak-transfer lemma.
- The cover letter uses plain text. It identifies Paper A by its current
  finite-Ising-chain title and notes its consideration at J. Stat. Mech.,
  using the author's stated status. C1's JTP disclosure remains.
- Section 5 identifies nine record files. Appendix G groups their computations
  into three method/range rows; seven scaled jobs, one zero job and one Hankel
  job produced the records.
- Theorem 1.4(a) explicitly restricts the second differences to indices
  `1,...,N-1`. Theorem 4.6 explicitly quantifies every initial bias in `[0,1]`
  in its finite-time clause. These clarify the existing proved statements.
- Both descriptions of the extended version include odd lengths and the assay
  likelihood bound. The coin-turning comparison uses `c` rather than the
  memory parameter `a`. The right-boundary difference is `u_t`, distinct from
  the transition rate `r_t(k)`; its subsequent use is updated too.
- The acknowledgments use semicolons, both figure captions have final periods,
  and the odd-length proposition has no one-item list. All three extended-version
  references to its former part (a) are updated.
- The general observation about mixtures cites Dharmadhikari and Joag-dev.
  This citation change does not assert a new full-text reading.

The exponential factor in `delta_B` is retained as requested when formal
statements depend on it. It occurs in `U1.deltaB` (`U1_CP.lean`),
`U2.deltaB` (`U2_LandauLocal.lean`) and `PaperD.deltaB` (`U3_Hyp.lean`).
`U1.deltaSharp_le_deltaB` explicitly uses the exponential being at least one.
The written proof already gives the sharper intermediate bound without that
factor. There is no change to a numerical bound or to the Lean library.

## Verification and reproduction

The verified proof-code tag remains `paperD-arxiv-v3`. The full axiom-audit
evidence remains at commit `c24791a`, linked from Section 5. Earlier audit
and document-build records are preserved. This revision changes presentation,
explicit quantifiers and local notation, without adding a mathematical claim.
It does not claim a new numerical or Lean run.

Compile both manuscripts and `threshold_review_cover.tex` into
`.pdf-build/paperD-posting-corrections-2026-11-02`. Run `package_revision.py`
in this folder to regenerate PDFs, metadata, both upload archives and a source
copy at `.pdf-build/paperD-posting-clean-2026-11-02`. Compile both manuscripts
in that source copy with output directory `build`, then run
`check_jtp_package.py`. The manifests record hashes and the package checks.

Both ordinary and isolated builds passed, with no undefined references or
overfull boxes. All fonts are embedded. The journal version has 52 pages,
the extended version 72, and the review extract 9. The arXiv abstract has
1,543 characters. Every file in the 21-file arXiv archive and the 29-file
journal archive matches the current source bytes. Fifteen rendered pages
were inspected across the two manuscripts, covering all changed passages.
`precision-and-text-checks.json` records the exact rational rounding check
and the absence of markup in the cover letter.

The Lean library, numerical programs and certificate data were compared
with `paperD-arxiv-v3` and remain unchanged. The manuscript proof edits
rename a local boundary sequence and remove an obsolete part label; they
do not alter the arguments. The clarified statement ranges match the
existing formal results.

No journal or arXiv submission has been made and no email has been sent.
