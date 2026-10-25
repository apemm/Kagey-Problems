# What the occupation law of a finite Markov chain determines

Paper C2. Full title "What the occupation law of a finite Markov chain determines: time reversal,
principal minors and cycle trees". Target journal Stochastic Processes and their Applications
(Elsevier). On October 24, 2026 the old Paper C was split in two. The forward theory stays in
`../paperC` as Paper C1, "Occupation counts of rarely switching Markov chains: stratified local
laws, support selection and the boundary layer", and this folder holds the identifiability half.
The split proposal is `research_notes/Paper C audits/09_split_proposal.md`, the record of the
split is `12_C2_split_report.md`, the revision of October 25 after the second referee report is
`26_C2_second_review_fixes.md`, and the integration of the exact-law theorem is
`29_C2_O1_integration.md`, all in the same folder.

The question is the inverse problem: what does the occupation measure of a chain determine about
its generator Q? It is answered at three resolutions, the exact law of the occupation times, the
Donsker and Varadhan functional J_V, and the first-order modal supports of a discretized chain
killed at known rates, and at low temperature.

## Two builds

- `problem131_reconstruction.tex`, the journal version (`elsarticle`, `preprint,12pt`), 43 pages.
- `problem131_reconstruction_arxiv.tex`, the arXiv version (`article`, 11pt), 46 pages. It inputs
  the same section files and keeps the reversible design (`sec_reversible.tex`) as its final
  Section 8.

The switch is `\newif\ifarxivbuild`, set in each top-level file. Sections 1 to 7 and all their
statement numbers are the same in both builds. The journal version points to the arXiv version
for the reversible design in one sentence at the end of Section 1.4.

## What is proved

The numbers are those of the builds of October 25, 2026. The introduction states Theorems A to D
and Corollary 1.1.

- Section 2 states the results of C1 that are used (Lemmas 2.1, 2.2 and 2.4, Proposition 2.3,
  Theorem 2.5, Definition 2.6, Proposition 2.7, Theorems 2.8 and 2.9), each with its C1 number.
- Section 3, Theorem A. The polynomial of a face is irreducible (Lemma 3.1, by Lemma 5.1 of Al
  Ahmadieh), the Perron branch determines the principal minors (Lemma 3.2), and J_V determines
  exactly the principal minors of -Q (Theorem 3.3). The survival probability gives them at once
  (Remark 3.4). Definition 3.5 (generator points and the cut-transpose orbit). The generator fiber
  is Corollary 3.6, credited to Loewy, Hartfiel and Loewy, Al Ahmadieh and Chatterjee, Ghosh,
  Gurjar and Raj. The stationary start (Remark 3.8, path reversal) and the amplitudes, which
  separate every two members of the fiber for a generic start (Proposition 3.9).
- Section 4, Theorem B, the exact occupation law. Reductions to the stationary Laplace transform,
  to the counts of I + hQ at a fixed h and to the second moments (Lemma 4.1). One time determines
  every time, from any start, and gives the principal minors (Lemma 4.2, Theorem 4.3). A generic
  start determines Q (Theorem 4.4). Second moments give Q up to time reversal for d <= 4 (to order
  T^4) and generically (to order T^5) (Theorem 4.5). The stationary start gives Q up to time
  reversal for d <= 4, without a cut, and generically (Theorem 4.6). One fixed N, with
  E_pi[n n^T] = N^2 D + sum_k h^k C(N+1, k+2) Sigma_k (Remark 4.7). The gluing formula across a cut
  (Proposition 4.8), the balance criterion (Corollary 4.9) and its necessary conditions (Remark
  4.10). Memoryless blocks (Definition 4.11), whose reversal keeps the stationary law (Theorem
  4.12) and which are balanced sides (Remark 4.13). The five-state example where the stationary law
  does not determine Q up to time reversal (Example 4.14). Conjectures 4.15 (the stationary fiber)
  and 4.16 (balanced sides) are stated as conjectures.
- Section 5, Theorem C. The controlled score law (Proposition 5.1), the two labels and the strict
  regions (Lemma 5.2), controlled boundaries (Definition 5.3), suppression (Lemma 5.4), exposure by
  descent (Lemma 5.5) and Theorem 5.6. "Exactly" is said only for the first-order map W_Q.
- Section 6, Theorem D. The depth of a face (Theorem 6.1), noncritical heights (Theorem 6.2),
  prefactors (Proposition 6.3), critical windows (Theorem 6.4) with Examples 6.5 and 6.6, the
  threshold design (Theorem 6.11), the cycle criterion (Theorem 6.12), the cycle tree from the
  functionals (Corollary 6.13) and the prefactors from window endpoints (Theorem 6.14).
- arXiv only, Section 8. The reversible design (Theorem 8.2), the dimension count (Proposition
  8.3), stability (Theorem 8.5), uniform face maxima imported from C1 (Proposition 8.6) and the
  finite horizon (Theorem 8.7).

## What is conditional

Nothing. The C1 numbers are those of `../paperC/EXPORTS.md` of October 25, 2026, and C1 is cited
as arXiv:2610.09258v2. Conjectures 4.15 and 4.16 are labelled as conjectures, and their proved
parts are said separately.

## What rests on computation

Every statement is proved in the text. The explicit numbers of the four-state cut-transpose
example after Corollary 3.6, its first separating moment 29(w1 - w2)(w3 - w4)/9673 after Theorem
4.6, the spectrum of K^2 and the start e_1 in Example 4.14 (and, in the arXiv version, the numbers
of Remark 8.9) were computed, and the scripts check them. The leading cofactors of Example 6.5 are
given by hand.

## Files

- The two top-level files above, `abstract.tex` (shared), the sections `sec_intro.tex`,
  `sec_prelim.tex`, `sec_minors.tex`, `sec_exactlaw.tex`, `sec_modal.tex`, `sec_lowtemp.tex`,
  `sec_verify.tex`, `sec_reversible.tex` (arXiv only) and the bibliography `bib_switching.tex`.
- Scripts. `verify_all.py` runs the six checks and writes `data/<script>_output.txt`, each headed
  by the sha256 of its script. `verify_reconstruction.py` (Sections 3 and 5 and the reversible
  design), `verify_exactlaw.py` (Section 4, in exact arithmetic), `verify_finite_horizon.py` and
  `verify_threshold.py` (the arXiv Section 8), `verify_cycles.py` (Examples 6.5 and 6.6) and
  `verify_attraction.py` with `attraction_core.py` (Theorem 6.11).
- `TEMPLATE.md` records the SPA guide and the choices made, `cover_letter.md` is the cover letter.

## Build and run

    pdflatex -interaction=nonstopmode problem131_reconstruction.tex         (three times)
    pdflatex -interaction=nonstopmode problem131_reconstruction_arxiv.tex   (three times)
    py -I verify_all.py            (about four minutes)

The scripts need Python 3 with numpy, scipy, sympy and mpmath. TeX Live 2026 built the PDFs.

## Statement labels

Each statement has a `\label` that names its content. The introduction's theorems are `thm:A`,
`thm:law` (printed as Theorem B, the exact law), `thm:B` (printed as Theorem C, the modal
supports) and `thm:D` (Theorem D, the low-temperature theorem), and the fiber corollary is
`cor:A-fiber`. The new section uses `lem:reductions`, `lem:graph`, `thm:one-horizon`,
`thm:generic-start`, `thm:second-moments`, `thm:stationary-law`, `rem:one-N`, `prop:gluing`,
`cor:balance`, `rem:balance-necessary`, `def:memoryless`, `thm:memoryless`,
`rem:memoryless-cut`, `ex:five-state`, `conj:fiber` and `conj:balanced`. In the body
`thm:nonreversible` is a corollary, `prop:stationary` became `rem:stationary`,
`prop:identifiability` was merged into `thm:modal` and `thm:minimality` is a proposition.

## History

Until October 24, 2026 this material was Sections 9 and 10 of Paper C (`../paperC`, commit
0ffc041). The split followed `research_notes/Paper C audits/10_external_referee_report.md`. The
revision of October 25 cut the reversible design from the journal version and reframed the paper
around the inverse problem. Later that day the exact occupation law became Section 4 and Theorem
B, the title changed from "occupation functional" to "occupation law", and the later sections and
introductory theorems moved up by one.
