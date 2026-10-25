# What the occupation functional of a finite Markov chain determines

Paper C2. Full title "What the occupation functional of a finite Markov chain determines:
principal minors, modal supports and cycle trees". Target journal Stochastic Processes and their
Applications (Elsevier). On October 24, 2026 the old Paper C was split in two. The forward theory
stays in `../paperC` as Paper C1, "Occupation counts of rarely switching Markov chains: stratified
local laws, support selection and the boundary layer", and this folder holds the identifiability
half. The split proposal is `research_notes/Paper C audits/09_split_proposal.md`, the record of the
split is `12_C2_split_report.md`, and the revision of October 25 after the second referee report
is `26_C2_second_review_fixes.md` in the same folder.

The question is the inverse problem: what does the occupation measure of a chain determine about
its generator Q? It is answered at the level of the Donsker and Varadhan functional J_V, of the
first-order modal supports of a discretized chain killed at known rates, and at low temperature.

## Two builds

- `problem131_reconstruction.tex`, the journal version (`elsarticle`, `preprint,12pt`), 33 pages.
- `problem131_reconstruction_arxiv.tex`, the arXiv version (`article`, 11pt), 37 pages. It inputs
  the same section files and keeps the reversible design (`sec_reversible.tex`) as its final
  Section 7.

The switch is `\newif\ifarxivbuild`, set in each top-level file. Sections 1 to 6 and all their
statement numbers are the same in both builds. The journal version points to the arXiv version
for the reversible design in one sentence at the end of Section 1.3.

## What is proved

The numbers are those of the builds of October 25, 2026. The introduction states Theorems A to C,
Corollary 1.1 and the reserved place for a theorem on the exact occupation law (a comment only,
nothing is claimed).

- Section 2 states the results of C1 that are used (Lemmas 2.1, 2.2 and 2.4, Proposition 2.3,
  Theorem 2.5, Definition 2.6, Proposition 2.7, Theorems 2.8 and 2.9), each with its C1 number.
- Section 3, Theorem A. The polynomial of a face is irreducible (Lemma 3.1, by Lemma 5.1 of Al
  Ahmadieh), the Perron branch determines the principal minors (Lemma 3.2), and J_V determines
  exactly the principal minors of -Q (Theorem 3.3). The survival probability gives them at once
  (Remark 3.4). Definition 3.5 (generator points and the cut-transpose orbit). The generator fiber
  is Corollary 3.6, credited to Loewy, Hartfiel and Loewy, Al Ahmadieh and Chatterjee, Ghosh,
  Gurjar and Raj. The stationary start (Remark 3.8, path reversal) and the amplitudes, which
  separate every two members of the fiber for a generic start (Proposition 3.9).
- Section 4, Theorem B. The controlled score law (Proposition 4.1), the two labels and the strict
  regions (Lemma 4.2), controlled boundaries (Definition 4.3), suppression (Lemma 4.4), exposure by
  descent (Lemma 4.5) and Theorem 4.6. "Exactly" is said only for the first-order map W_Q.
- Section 5, Theorem C. The depth of a face (Theorem 5.1), noncritical heights (Theorem 5.2),
  prefactors (Proposition 5.3), critical windows (Theorem 5.4) with Examples 5.5 and 5.6, the
  threshold design (Theorem 5.11), the cycle criterion (Theorem 5.12), the cycle tree from the
  functionals (Corollary 5.13) and the prefactors from window endpoints (Theorem 5.14).
- arXiv only, Section 7. The reversible design (Theorem 7.2), the dimension count (Proposition
  7.3), stability (Theorem 7.5), uniform face maxima imported from C1 (Proposition 7.6) and the
  finite horizon (Theorem 7.7).

## What is conditional

Nothing. The C1 numbers are those of `../paperC/EXPORTS.md` of October 25, 2026, and C1 is cited
as arXiv:2610.09258v2.

## What rests on computation

Every statement is proved in the text. The explicit numbers of the four-state cut-transpose
example after Corollary 3.6 (and, in the arXiv version, of Remark 7.9) were computed, and the
scripts check them. The leading cofactors of Example 5.5 are now given by hand.

## Files

- The two top-level files above, `abstract.tex` (shared), the sections `sec_intro.tex`,
  `sec_prelim.tex`, `sec_minors.tex`, `sec_modal.tex`, `sec_lowtemp.tex`, `sec_verify.tex`,
  `sec_reversible.tex` (arXiv only) and the bibliography `bib_switching.tex`.
- Scripts. `verify_all.py` runs the five checks and writes `data/<script>_output.txt`, each headed
  by the sha256 of its script. `verify_reconstruction.py` (Sections 3 and 4 and the reversible
  design), `verify_finite_horizon.py` and `verify_threshold.py` (the arXiv Section 7),
  `verify_cycles.py` (Examples 5.5 and 5.6) and `verify_attraction.py` with `attraction_core.py`
  (Theorem 5.11).
- `TEMPLATE.md` records the SPA guide and the choices made, `cover_letter.md` is the cover letter.

## Build and run

    pdflatex -interaction=nonstopmode problem131_reconstruction.tex         (three times)
    pdflatex -interaction=nonstopmode problem131_reconstruction_arxiv.tex   (three times)
    py -I verify_all.py            (about four minutes)

The scripts need Python 3 with numpy, scipy, sympy and mpmath. TeX Live 2026 built the PDFs.

## Statement labels

Each statement has a `\label` that names its content. The introduction's theorems are `thm:A`,
`thm:B` and `thm:D` (printed as Theorem C, the low-temperature theorem), and the fiber corollary is
`cor:A-fiber`. In the body `thm:nonreversible` is now a corollary, `prop:stationary` became
`rem:stationary`, `prop:identifiability` was merged into `thm:modal`, `thm:minimality` is a
proposition, and `def:orbit` and `cor:tree-from-dv` are new.

## History

Until October 24, 2026 this material was Sections 9 and 10 of Paper C (`../paperC`, commit
0ffc041). The split followed `research_notes/Paper C audits/10_external_referee_report.md`. The
revision of October 25 cut the reversible design from the journal version and reframed the paper
around the inverse problem.
