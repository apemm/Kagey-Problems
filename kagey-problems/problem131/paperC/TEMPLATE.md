# Paper C in the Springer Nature template (JTP)

`problem131_chains_sn.tex` is the Journal of Theoretical Probability version of
`problem131_chains.tex`. Both main files input the same section files, appendices and
bibliography, so the content never forks: edit the `sec_*.tex` / `app_*.tex` files and both
versions follow.

## Template source

- Journal page: https://link.springer.com/journal/10959/submission-guidelines links "Springer
  Nature LaTeX template" to https://www.springernature.com/gp/authors/campaigns/latex-author-support
- Zip downloaded from that page (the "journal article template", December 2024 release):
  https://cms-resources.apps.public.k8s.springernature.io/springer-cms/rest/v1/content/18782940/data/v12
- Downloaded 2026-10-24, saved as `../common/sn-jnl/download/sn-article-template.zip`
  (901,814 bytes, entries dated 2024-12-13).
- sha256 of the zip: `812e76dcaa9c28dc1bff1fb6065d51729b67d4ea140552a05088317414a3ecae`
- sha256 of `sn-jnl.cls`: `36d0c3273a59d48dc6a9c7b080dfa1ec50dc10229d8751568d1f2e490ffa5ecc`
- Version string in `sn-jnl.cls`: `\ProvidesClass{sn-jnl}[2019/11/18 v0.1: An authoring template
  for Springer Journal articles]`. Springer never bumped this string; the file dates (2024-12-13)
  are the real version marker.

Copied into `../common/sn-jnl/`: `sn-jnl.cls`, the nine `.bst` files (`sn-mathphys-num.bst` is
the one we would use), the sample `sn-article.tex` with its PDF `sn-article.pdf`, and
`user-manual.pdf`. The sample `.bib` and `.eps` files were not copied. Note that `sn-jnl.cls`
and `sn-article.tex` use bare CR line endings, so view them with `tr '\r' '\n'`.

## Choices in the main file

- Class options `[pdflatex,sn-mathphys-num]`, as in the sample. JTP's guidelines ask for numbered
  references, and `sn-mathphys-num` loads natbib with `numbers,sort&compress`.
- Running title: "Occupation counts of rarely switching Markov chains".
- Author and affiliation through `\author*`, `\fnm`, `\sur`, `\email`, `\affil*`, `\orgdiv`,
  `\orgname`, `\orgaddress`, `\city`, `\state`, `\postcode`, `\country` (names checked against
  the sample).
- ORCID left out. The class has `\orcid`, but it needs an `Orcidlogo.eps` that the zip does not
  ship, and Springer collects the ORCID in the submission system anyway.
- Abstract copied verbatim into `\abstract{...}`. After the revision of October 24 it is about 240
  words by `wc`, within the limit of 250, and it defines every term it uses.
- `\keywords{...}` and `\pacs[MSC Classification]{...}` carry the keywords and the 2020 MSC codes
  of the article version. The `\pacs` argument spells out "Primary 60J10; Secondary 60J27, 60F10,
  60F05, 15A18, 15B48, 15A29" so that the split shows (82C26 was replaced by 15A29).
- Theorems use the class styles: `thmstyleone` for theorem, lemma, proposition, corollary,
  conjecture, introtheorem and hypothesis (Hypothesis L, declared in both preambles); `thmstylethree` for definition and example; `thmstyletwo` for
  remark and question ("Open problem"). Numbering is within sections as before, and introtheorem
  stays alphabetic (Theorem A, B, ...).
- The class turns `proof` into its own `spiproof` (small type, open square). Nothing to change in
  the section files for that.
- All the notation macros (`\Z`, `\R`, `\E`, `\Prob`, `\Var`, `\Cov`, `\supp`, `\ones`, `\tree`,
  `\arb`) are defined in the new preamble. The drafting macro `\proofpending` and the EJP
  environment `acks` were removed on October 24, since no section file uses them.
- `float` is loaded so that the `[H]` figure in `sec_intro.tex` still builds.
- `xr-hyper`, `\externaldocument[S-]{supplement}` and `\sref` were removed on October 24 from
  both main files. The supplement is no longer part of the paper, and the text has no pointer
  to it, to `removed_proofs` or to the earlier version. The repository is named only in the
  Code availability statement. `mathtools` and `array` were
  dropped too, since nothing uses them.
- After `\backmatter`: `\bmhead{Acknowledgments}`, then `\section*{Statements and Declarations}`
  (the heading of the JTP guidelines) as an itemized list (Funding, Competing interests, Ethics
  approval and consent to participate, Consent for publication, Data availability, Materials
  availability, Code availability, Author contribution), text copied from the article version. The Data and Code availability items
  carry the same text as the article version and point to Section `sec:verify`.
- Appendices go inside `\begin{appendices} ... \end{appendices}` as the class requires; they come
  out as "Appendix A ...", "Appendix B ...".
- The bibliography stays the inline `thebibliography` of `bib_switching.tex`, input as before.
  The class accepts it. Converting to a `.bib` file with `\bibliography{...}` and
  `sn-mathphys-num.bst` is optional; Springer's production asks for the reference list in the
  `.tex` in either case.

## Build

From this folder, with the class found through TEXINPUTS (no files copied next to the main file;
this works on TeX Live 2026 in Git Bash):

    TEXINPUTS=".;../common/sn-jnl;" pdflatex -interaction=nonstopmode problem131_chains_sn.tex

Run it twice. After the revision of October 24 both builds have no errors, no undefined
references, no multiply defined labels and no overfull boxes. The sn version has 104 pages and
the article version 95 (before the revision 109 and 100). `\graphicspath` is `{figures/}` only,
since every figure is in `figures/`.

## Zip for Snapp (the JTP submission system)

Snapp compiles with pdflatex on TeX Live 2021 from one zip and does not know `TEXINPUTS`. So the
zip must be flat with respect to the class:

1. `problem131_chains_sn.tex` at the top level, with `sn-jnl.cls` copied from `../common/sn-jnl`
   beside it (no `.bst` is needed, since the bibliography is the inline `thebibliography`).
2. The eleven input files `sec_intro.tex`, `sec_model.tex`, `sec_dv.tex`, `sec_firstorder.tex`,
   `sec_secondorder.tex`, `sec_boundary.tex`, `sec_complete.tex`, `sec_vertex.tex`,
   `sec_reconstruction.tex`, `sec_lowtemp.tex`, `sec_verify.tex`, the four appendices
   `app_torus.tex`, `app_laplace.tex`, `app_complete.tex`, `app_vertex.tex`, and
   `bib_switching.tex`.
3. The folder `figures/` with `fig_complete_envelope.pdf`, `fig_simplex.pdf` and
   `fig_cycles.pdf` (the fourth figure is TikZ).
4. Test once without `TEXINPUTS`, in a scratch copy of the zip contents:
   `pdflatex -interaction=nonstopmode problem131_chains_sn.tex`, twice.

## Fixes made in the section files (October 24, 2026)

The narrower text block of the class (372pt, about 13.1 cm, against 462pt, about 16.3 cm, in the
article version) made four boxes overfull. They are fixed in the section files, so both versions
follow.

1. `sec_boundary.tex`, the display defining `f^{(z)}_G` and `W_z` in Lemma `lem:layer-exact`: now a
   `gather*` with the two formulas on two lines.
2. `sec_complete.tex`, equation `eq:interior`: the body is a `gathered` with `D(\alpha)=` on its own
   line.
3. `app_torus.tex`, the display bounding `\E_w(M-1)^2`: now an `align*` broken before `\le`.
4. `sec_firstorder.tex`, the table `tab:C4worked`: `\tabcolsep` set to 5.5pt inside the table.
5. `app_vertex.tex`, the proof of Lemma `lem:uniform-laguerre-bessel`: `\qedhere` dropped, so the
   class's box falls after the display in both versions and amsthm no longer warns.
6. The outcomes table of `sec_examples.tex` is gone with that file, which neither main file inputs.

`sec_verify.tex` now uses unnumbered `\subsection*` headings. The sn build still gives one
harmless hyperref warning about bookmark levels at `\bmhead{Acknowledgments}`, which the class
sets at paragraph level directly after a section.
