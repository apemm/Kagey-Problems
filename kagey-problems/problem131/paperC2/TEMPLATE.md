# Paper C2 in the Elsevier template (Stochastic Processes and their Applications)

`problem131_reconstruction.tex` uses the `elsarticle` class with the options `preprint,12pt`.
The class comes with TeX Live 2026 (`kpsewhich elsarticle.cls` gives
`texmf-dist/tex/latex/elsarticle/elsarticle.cls`), so nothing is copied into the repository.

## What the journal asks for

The source is the SPA guide for authors at
https://www.sciencedirect.com/journal/stochastic-processes-and-their-applications/publish/guide-for-authors,
read on 2026-10-24 and checked again against the live page later that day. The facts below are
the ones that shape the manuscript.

- Length. "Research papers are generally expected to be 30–40 pages in length." Longer papers are
  not excluded, but the cover letter must then explain why the length is needed.
- Review. Single anonymized. The editors screen first, then at least two reviewers.
- Title page. Concise title without abbreviations or formulae where possible, author names,
  affiliation with full postal address and country, corresponding author clearly indicated, with
  email.
- Abstract. At most 250 words, standing alone, no references (if one is essential, cite author
  and year), no uncommon abbreviations. The reference section of the guide adds that references
  cited in the abstract must be given in full, so the one reference in our abstract carries the
  journal, volume, year and article number.
- Keywords. 1 to 7, in English, avoiding multi-word keywords joined by "and" or "of".
- Highlights. Encouraged, not required. 3 to 5 bullets of at most 85 characters each, uploaded
  as a separate file with "highlights" in the file name.
- Structure. Numbered sections and subsections (1.1, 1.1.1), abstract not numbered.
  Acknowledgements in a separate section directly before the references. Appendices lettered
  A, B with equations (A.1), (B.1).
- Proofs (journal-specific). Main ideas and the key steps of the principal proofs should be
  outlined before the details. Technical arguments that do not help understanding should be
  short or moved to an appendix.
- References. Numbers in square brackets in the text. The list is arranged alphabetically and
  then numbered. Journal names abbreviated by the ISO List of Title Word Abbreviations. DOIs
  where available. Preprints marked with the server name. "In press" only for accepted work.
- Declarations. Competing interests through the declarations tool in the submission system (a
  .docx is generated and uploaded). Funding must be stated, and if there is none the guide gives
  the sentence "This research did not receive any specific grant from funding agencies in the
  public, commercial, or not-for-profit sectors."
- Research data. Option A, deposit and cite encouraged.
- Submission. Editable source (.tex), not only a PDF. Authors are strongly encouraged to post
  the paper on arXiv at submission and to give the arXiv reference in the cover letter. The
  cover letter should be short (ideally under a page), say how the work fits the journal and
  why it is new, and include a length justification where needed. It should not contain funding,
  declarations or suggested reviewers.
- MSC codes. The guide does not mention them. The `elsarticle` class supports `\MSC[2020]`
  inside the `keyword` environment, and we give the 2020 codes there.

## Choices in the main file

- `\documentclass[preprint,12pt]{elsarticle}` with `geometry` margins of 1in, `amsthm`
  environments numbered within sections, and the introduction's theorems lettered A to D.
- `\journal{Stochastic Processes and their Applications}`, one `\author` with `\ead`, marked
  as corresponding author with `\corref` and `\cortext`, and a structured `\affiliation`
  (organization, street address, city, postcode, state, country).
- Abstract of 250 words or fewer (234 by a whitespace count in the journal build, in `abstract.tex`, shared with the
  arXiv build), with the one reference given in full as "Kim and Landim (Stochastic Process.
  Appl. 189 (2025) 104733)".
- Seven keywords, separated by `\sep`, and `\MSC[2020] 60J27 \sep 60F10 \sep 60J10 \sep 15A15
  \sep 15A18 \sep 15A29 \sep 15B48`.
- Unnumbered sections after the last numbered one, in the order Data and code availability,
  Funding, Declaration of competing interest, Acknowledgments, then the references.
- The bibliography is a hand-written `thebibliography` in `bib_switching.tex`, alphabetical and
  numbered, in the Elsevier numbered style (authors with initials, title, abbreviated journal,
  volume (year) pages, DOI link). Paper C1 is entry `paperC1`, cited as an arXiv preprint.
- No figures and no appendices.

## Build

    pdflatex -interaction=nonstopmode problem131_reconstruction.tex   (three times)

The build of 2026-10-25, after the exact-law section was added, has 43 pages, no undefined
references, no multiply defined labels and no overfull boxes. That is 3 pages over the guide's 30
to 40, so the cover letter carries a short length justification. The arXiv build
`problem131_reconstruction_arxiv.tex` (article class, 46 pages)
adds the reversible design as a final section. The switch `\ifarxivbuild` is set in each
top-level file.

## For submission

- Upload `problem131_reconstruction.tex`, `abstract.tex`, the section files `sec_*.tex` other
  than `sec_reversible.tex`, and `bib_switching.tex` (or a single flattened .tex), and the PDF.
- Highlights (optional), for a separate file `highlights.txt`.
  - The Donsker-Varadhan functional fixes exactly the principal minors of -Q
  - The exact occupation law at one time fixes the law at every time
  - From the stationary start it fixes Q up to reversal for d <= 4 and generically
  - Reversing a memoryless block keeps the stationary occupation law
  - The functionals determine every depth and the Freidlin-Wentzell cycle tree
- Competing interests and funding through the declarations tool, consistent with the sections at
  the end of the manuscript.
