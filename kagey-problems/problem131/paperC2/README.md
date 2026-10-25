# What the occupation law of a finite Markov chain determines

Paper C2. Full title "What the occupation law of a finite Markov chain determines: principal
minors, modal supports and cycle trees". Target journal Stochastic Processes and their
Applications (Elsevier). On October 24, 2026 the old Paper C was split in two. The forward theory
stays in `../paperC` as Paper C1, "Occupation counts of rarely switching Markov chains", and this
folder holds the identifiability and reconstruction half. The split proposal is
`research_notes/Paper C audits/09_split_proposal.md`, and the record of the split is
`research_notes/Paper C audits/12_C2_split_report.md`.

A Markov chain on d states with transition matrix I + (T/N)Q runs for N steps, with
T = tau log N. Its composition is the vector of occupation counts, and C1 describes which face of
the simplex carries the most likely composition. This paper asks what such coarse functionals of
the law determine about Q.

## What is proved

The numbers are those of the build of October 24, 2026 (`problem131_reconstruction.pdf`, 40
pages). The introduction states Theorems D to G, continuing the letters A to C of C1.

- Section 2 states the results of C1 that are used (Lemmas 2.1, 2.2 and 2.4, Proposition 2.3,
  Theorem 2.5, Definition 2.6, Proposition 2.7, Theorems 2.8 and 2.9), each with its C1 number,
  and Proposition 5.6 imports the uniform face maxima.
- The Donsker and Varadhan functional (Section 3, Theorem D). The polynomial of a face is
  irreducible (Lemma 3.1, by Lemma 5.1 of Al Ahmadieh), the Perron branch on an open set of
  fields determines the principal minors (Lemma 3.2), and J_V determines exactly the principal
  minors of -Q (Theorem 3.3). The survival probability gives them at once (Remark 3.4). The
  generator fiber (Theorem 3.5) is finite, is {Q, Q*} without a cut and for d <= 3, {Q} for
  reversible Q, and in general the set of generator points of the cut-transpose orbit. From the
  stationary start the law of the composition is the same under Q and Q* (Proposition 3.7). The
  second-order amplitudes separate the fiber for a generic start (Proposition 3.8).
- Modal supports (Section 4, Theorem E). The controlled score law (Proposition 4.1), the strict
  regions (Lemma 4.2), the precise definition of equal controlled boundaries (Definition 4.3),
  suppression without reversibility (Lemma 4.4), exposure by descent (Lemma 4.5), the
  identifiability proposition (Proposition 4.6) and Theorem 4.7, which says that the controlled
  boundaries determine exactly the principal minors.
- The reversible design and finite horizons (Section 5, Theorem F). Suppression (Lemma 5.1),
  reconstruction from m + d - 1 boundaries of a design fixed in advance (Theorem 5.2),
  minimality (Theorem 5.3), partial data (Remark 5.4), stability (Theorem 5.5), uniform face
  maxima on the class (Proposition 5.6, imported from C1), finite-horizon recovery uniformly over the class
  (Theorem 5.7) and the start that defeats every horizon (Remark 5.8).
- Low temperature (Section 6, Theorem G). The depth of a face (Theorem 6.1), noncritical heights
  (Theorem 6.2), prefactors (Proposition 6.3, classical in substance), critical windows (Theorem
  6.4) with the noncycle window (Example 6.5) and a branch switch (Example 6.6). The cycle tree is
  read from calibrated rewards (Theorem 6.11), cycles are the sets whose proper subsets are
  strictly shallower (Theorem 6.12), and the window endpoints give the prefactors on the
  envelope (Theorem 6.13).

## What is conditional

Nothing. The paper uses the results of C1 listed in Section 2 and the uniform face maxima of
Proposition 5.6, which is Proposition 5.16 of C1. The C1 numbers were taken from
`../paperC/EXPORTS.md` on October 24, 2026, and must be updated if C1 renumbers.

## What rests on computation

No proof rests on a computation. Section 7 lists what the scripts check.

## Files

- `problem131_reconstruction.tex`, the main file (`elsarticle`, options `preprint,12pt`).
  `TEMPLATE.md` records the SPA guide for authors and the choices made.
- Sections `sec_intro.tex`, `sec_prelim.tex`, `sec_minors.tex`, `sec_modal.tex`,
  `sec_reversible.tex`, `sec_lowtemp.tex`, `sec_verify.tex`, and the bibliography
  `bib_switching.tex`.
- Scripts. `verify_all.py` runs the five checks and writes `data/<script>_output.txt`, each
  headed by the sha256 of its script.
  - `verify_reconstruction.py` checks Sections 3 to 5 (symbolic identities, the reversible design
    on random chains, stability, cut-transposes, the Perron-branch derivative, fibers on three
    states).
  - `verify_finite_horizon.py` checks Theorem 5.7 and Remark 5.9 by the exact run expansion.
  - `verify_threshold.py` computes the least horizon N at which I + (T/N)Q is stochastic on the
    whole range of the design, for two families with b from 1/2 to 1/256 (the sentence after
    Theorem 5.7, standard library only).
  - `verify_cycles.py` checks Examples 6.5 and 6.6 in exact arithmetic (standard library only).
  - `verify_attraction.py` with the module `attraction_core.py` checks Theorem 6.11 on 138 faces.
- `data/` holds the five outputs.
- `cover_letter.md`, the cover letter for SPA.

## Build and run

    pdflatex -interaction=nonstopmode problem131_reconstruction.tex      (three times)
    py -I verify_all.py            (a few minutes)

The scripts need Python 3 with numpy, scipy, sympy and mpmath. The outputs in `data/` were made with
Python 3.14.3, numpy 2.4.2, scipy 1.17.1, sympy 1.14.0 and mpmath 1.3.0, and TeX Live 2026 built the
PDF.

## Statement labels

Each statement has a `\label` that names its content, and the scripts refer to statements by these
keys. Labels kept from the old Paper C include `thm:nonreversible`, `lem:perron-branch`,
`lem:exposure`, `def:controlled`, `thm:reversible-reconstruction`, `thm:finite-horizon` and the
low-temperature labels. New labels are `thm:dv` (the functional part of Theorem D, formerly
`cor:dv-fiber`), `prop:stationary` and `prop:amplitudes` (formerly part (f) of
`thm:nonreversible`), `lem:strict`, `prop:identifiability` and `thm:modal` (formerly part (a) of
`thm:nonreversible` and the modal half of `cor:dv-fiber`). The parts of `thm:nonreversible` are
relettered (a) to (d).

## History

Until October 24, 2026 this material was Sections 9 and 10 of Paper C (`../paperC`, commit
0ffc041). The split followed the referee report in
`research_notes/Paper C audits/10_external_referee_report.md`. The changes made in the split are
listed in `research_notes/Paper C audits/12_C2_split_report.md`.
