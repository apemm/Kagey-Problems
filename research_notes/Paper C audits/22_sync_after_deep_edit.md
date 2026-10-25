# 22. Sync of the other files to the deep edit of Paper C1

October 24, 2026. This note records how the files that cite Paper C1 were brought in line with the
deep edit of item 20. C1 itself was not touched. Every number below was checked against the text of
`paperC/problem131_chains.pdf` (59 pages) and, for the page count, `problem131_chains_sn.pdf` (65
pages).

## Paper C2

- C2 cites 16 numbered statements or equations of C1. We checked each one against the C1 PDF, including the lettered parts.
  Lemma 2.2(b) and (c), Lemma 2.3, Lemma 3.2, Propositions 3.1 and 3.4, Lemma 4.1 with (6),
  equation (1), Theorem 4.2 with parts (ii) and (iii), Remark 4.3, Theorem 4.4, Definition 5.1 and
  the text after it, Proposition 5.2, and Theorems 5.6 to 5.8 keep their numbers.
- The one change is in `sec_reversible.tex`. The uniform face maxima on the class are now
  Proposition 5.12 of C1 (they were 5.15). C2 does not name the section that holds it.
- The C1 entry of `bib_switching.tex` has the new subtitle "stratified local laws, support
  selection and the boundary layer".
- Three pdflatex runs give 40 pages with no undefined reference or citation. The title change did
  not add a page. The auxiliary files were deleted and the PDF kept.
- `paperC2/README.md` now gives C1's full title and Proposition 5.12, with the earlier numbers 5.16
  and 5.15.

## The Lean map

- `lean/PaperC/MAP.md` has the new title, the page counts 59, 65 and 40, and the C1 numbers after
  the deep edit. Example 5.14 is 5.11, Lemma 5.12 is 7.1 and sits in the Section 7 table,
  Theorems 7.5 and 7.6 are 7.4 and 7.5, Corollary 7.7 is 7.6 and Remark 7.8 is 7.7. The equations
  after the removed (21) moved down by one, so the bracket is (24), the form of Theorem 8.2 is
  (25), the ratio and integral forms are (33) and (34), and the equations of Appendix D are (35)
  to (38).
- The rows for Proposition 7.1, Corollary 7.2 and both rows of Remark 7.4 moved to a new
  subsection of "Statements cut from C1 on October 24, 2026", with their Lean theorems unchanged.
  That subsection also names Proposition 5.11, Lemma A.5, Figure 4 and the display (21), which had
  no Lean rows.
- The row for Theorem 7.4(i) no longer speaks of a bin. It says that the face maximum lies above
  the vertex below the crossing.
- No Lean docstring cites a C1 statement number that moved. The docstrings cite the research notes
  by their own numbers, and `DVRestriction.lean` cites Section 3.1, Proposition 3.1 and equation
  (3) of C1, which did not move. So no Lean file changed and no rebuild was needed.

## The problem README

`problem131/README.md` has C1's new title, 59 and 65 pages, and a paragraph on what the deep edit
removed. C2 is 40 pages and its introduction is said to state Theorems A to D. Paper D has its new
title, 40 pages for the journal version, and Sections S1 to S4 of the arXiv build in place of the
Online Resource. The description of Paper F speaks of points of the range instead of bins.

## The arXiv files

`18_abstract_C1.txt` holds the current abstract of `problem131_chains.tex` as plain text, 1420
characters. `18_arxiv_form_C1.txt` has the new title, 59 pages and 3 figures. Its comments now say
that the results of the first version appear in Section 7 (the complete graph) and Section 8 (near
a vertex), and that the next term of the crossing equation, the Bessel majorant and the boundary
crossover stay in the first version.

## Sweep

In the files above, "bin" and "bins" remain only in the problem README, in the statement of
Kagey's question, in the description of Paper A and in the paragraph on earlier work, where the
Galton board is the subject. "Kagey" remains in the problem README (the problem statement and the
description of Paper E) and in the C2 bibliography entry for Problem 131. "Model" occurs only in
paper titles and in "hidden Markov models". Nothing else was found.
