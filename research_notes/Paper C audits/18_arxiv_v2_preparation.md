# 18. Paper C1 as version 2 of arXiv:2610.09258

October 24, 2026. Paper C1 ("Occupation counts of rarely switching Markov chains: stratified local
laws, crossings and the boundary layer", `kagey-problems/problem131/paperC`) will replace Paper B
("Vertex crossings in a symmetric Markov multinomial model", arXiv:2610.09258v1) as version 2 of the
same entry. The source bundle waits until the next round of edits to the paper.

## Edits to C1

- `sec_intro.tex` 224 to 231. The paragraph that first credits Paper B now says once that this
  paper replaces the preprint, which is the first version of the same arXiv entry, and that its
  results on the crossings with a vertex and near a vertex appear in Sections 7 and 8 as cases of
  the general theory. We cite the first version for the rest.
- `bib_switching.tex` 168 to 171. The entry `paperB` reads "arXiv:2610.09258v1, 2026, the first
  version of the present preprint", with the link to v1.
- "The preprint" became "The first version" in `sec_complete.tex` 83, 134 and 186, in
  `sec_vertex.tex` 82, and in the acknowledgments of both main files (line 106).
- The other citations of `paperB` (`sec_model.tex` 239, `sec_secondorder.tex` 656 and 726,
  `sec_complete.tex` 62, 64, 149 and 270, `sec_verify.tex` 4) read correctly as citations of the
  first version and are unchanged.

We did not write "in sharpened form". Section 7 has the exact parts of v1 (unique crossing at every
N, exact balancing, one mode change) and derives the asymptotic parts from the general theory,
uniformly for 1 <= T <= N^(1/3). But its crossing equation has error O(1/L), while v1 Theorem 3.2
has the next term 1/(8T) and error O(L^-2). Section 7 also cites v1 for that term, and Section 8
cites it for the Bessel majorant and the boundary crossover. So Section 7 is wider in range and
weaker in the crossing expansion.

## Edits elsewhere

- `paperC2/bib_switching.tex` 98 to 101. The entry `paperC1` has the full title and subtitle,
  "preprint, arXiv:2610.09258, 2026" and the link without a version.
- `paperF/problem131_levy.tex`. Paper F cites neither B nor C1, so it is unchanged. Its `paperD`
  entry stays "In preparation".
- READMEs. `archive/paperB/README.md`, the top-level `problem131/README.md` (lines 10 to 13 and 52
  to 58) and `paperC/README.md` (companion papers and a new paragraph on the arXiv plan at the end
  of the history).

## Builds

- C1, article class, three passes. 70 pages, no undefined references or citations, no missing
  files.
- C1, Springer class, three passes with `TEXINPUTS=".;../common/sn-jnl;"`. 77 pages, clean.
- C2, elsarticle, three passes. 41 pages, clean.
- Auxiliary files removed in both folders. The PDFs are kept.

## The form

`18_arxiv_form_C1.txt` has the form and `18_abstract_C1.txt` the abstract (1337 characters).

## What the bundle will need

- `problem131_chains.tex`.
- The sections `sec_intro.tex`, `sec_model.tex`, `sec_dv.tex`, `sec_firstorder.tex`,
  `sec_secondorder.tex`, `sec_boundary.tex`, `sec_complete.tex`, `sec_vertex.tex`,
  `sec_verify.tex`.
- The appendices `app_torus.tex`, `app_laplace.tex`, `app_complete.tex`, `app_vertex.tex`.
- The bibliography `bib_switching.tex` (inline `thebibliography`, so no `.bbl`). It ends the
  document.
- `figures/fig_complete_envelope.pdf`, `figures/fig_simplex.pdf`, `figures/fig_cycles.pdf` (the
  main file sets `\graphicspath{{figures/}}`). The 4-cycle figure is TikZ.
- Packages are all standard (geometry, amsmath, amssymb, amsthm, graphicx, booktabs, float,
  microtype, xcolor, tikz, enumitem, hyperref). No fontspec, minted or shell escape.
- One top-level file, so no `00README.json` is needed.
- Nothing else. Not the Springer file, the PDFs, the scripts, `data/`, the PNGs or the figure JSON.

## To decide before posting

- The comments line. The short form says the complete-graph results of v1 are Section 7, but the
  near-vertex results are in Section 8 and three results stay only in v1. The form gives an
  accurate version.
- The Springer file shares `bib_switching.tex`, so the JTP version will also call v1 "the first
  version of the present preprint". That reads oddly in a journal. One option is a switch in the
  bibliography entry for the Springer build.
- The cross-list to cond-mat.stat-mech is optional.
