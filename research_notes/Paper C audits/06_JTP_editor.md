# Paper C audit 06: handling editor's report, Journal of Theoretical Probability

Date: October 24, 2026. Manuscript: "Occupation counts of rarely switching Markov chains: stratified
local large deviations, modal supports and spectral reconstruction", sole author. Read from the
Springer Nature build `kagey-problems/problem131/paperC/problem131_chains_sn.tex` (109 pages) and the
section and appendix files it inputs; page counts are also given for the article build
`problem131_chains.tex` (100 pages). No manuscript file was edited. Line numbers are `file:line` in
the sources of October 24, 2026; page numbers are read from `problem131_chains_sn.aux` and
`problem131_chains.aux`.

Sources for the requirements:

- JTP submission guidelines, https://link.springer.com/journal/10959/submission-guidelines, fetched
  today (the quotations below are from that fetch).
- The earlier survey `reports/Paper D JTP guidelines.md` (October 16, 2026). It lives in `reports/`,
  not in `research_notes/`. Nothing in today's fetch contradicts it.
- The template notes `paperC/TEMPLATE.md` and the class `../common/sn-jnl/sn-jnl.cls` (December 2024
  package).

---

## Part 1. Desk check

### 1.1 What the guidelines require, in brief

- Title "concise and informative". Title page: names, affiliation, corresponding author's e-mail,
  ORCID "if available".
- Abstract "of 150 to 250 words", without "undefined abbreviations or unspecified references".
- "4 to 6 keywords". "An appropriate number of MSC codes".
- "Statements and Declarations": "submissions that do not include relevant declarations will be
  returned as incomplete." The summary asks for a "Declarations" section before the references with
  Funding and Competing interests, and "Ethics approval, Consent, Data, Material and/or Code
  availability and Authors' contribution statements." Author contributions and competing interests
  must also be entered in the submission system.
- The title-page section also asks that the use of certain writing tools beyond copy editing "be
  properly documented ... (if a Methods section is not available, in a suitable alternative part) of
  the manuscript."
- LaTeX: the Springer Nature template is recommended, not required. "Please ensure you provide all
  relevant editable source files at every submission and revision. Failing to submit a complete set
  of editable source files will result in your article not being considered for review." Snapp
  compiles with pdflatex on TeX Live 2021 from a single zip (see the D survey, Section 4).
- "Please use the decimal system of headings with no more than three levels."
- References numbered in square brackets, "numbered consecutively", DOIs as full links; only
  published or accepted works in the list, though arXiv preprints are accepted in practice.
- Figures: "cited in text in consecutive numerical order"; captions start with bold "Fig." and
  number, "nor is any punctuation to be placed at the end of the caption." Tables numbered, captioned
  and cited in order.
- Supplementary material: "Refer to the supplementary files as 'Online Resource'", each cited in the
  text and given a caption.
- Length: the guidelines set no page or word limit.

### 1.2 Item by item

| Item | Finding | Status |
|---|---|---|
| Title (`problem131_chains_sn.tex:55`) | 17 words in three clauses. "Spectral reconstruction" describes the matrix-theoretic half only loosely (the data are Perron roots and principal minors). Not a formal violation, but not concise. | change |
| Running title (`:55`) | 51 characters, fine. | ok |
| Author, affiliation, e-mail (`:57-59`) | `\author*`, `\fnm`, `\sur`, `\email`, `\affil*` with `\orgdiv`, `\orgname`, `\orgaddress` are used correctly. ORCID is in the article build but not here (`TEMPLATE.md` explains why). Optional, since Snapp collects it. | ok |
| Abstract (`:61-81`) | 248 words by `wc` with each formula counted as one word, so it is at the ceiling; a submission system that counts tokens differently may put it over 250. No references, no abbreviations. Two problems of content: "winning regions" (`:74`) and "calibrated" (`:73`) are not defined, and "for larger faces under one stated lemma" (`:69-70`) misdescribes both the scope (the result is unconditional up to three states, not only for pairs) and the status (the "lemma" is unproved). | change |
| Keywords (`:83`) | Six. At the limit, acceptable. | ok |
| MSC (`:85`) | `\pacs[MSC Classification]{...}` is the template's macro. The class prints the codes flat, so "Primary 60J10" is lost. 82C26 (dynamic phase transitions) does not describe anything in the paper; 15A29 (inverse problems in linear algebra) and 15A15 (determinants, principal minors) describe Part III better than 15B48. | change |
| Statements and Declarations (`:118-151`) | Heading is the template's "Declarations"; the guidelines' own heading is "Statements and Declarations" (the article build uses it). Funding, Competing interests, Ethics and consent, Consent for publication, Data availability, Code availability and Author contribution are present. Materials availability is absent (say "Not applicable"). Data availability (`:125-136`) points to an unpublished "earlier version" in the repository that "contains ... which this version leaves out"; that is neither data nor an Online Resource, and a referee cannot be asked to treat it as part of the submission. Code availability (`:137-149`) points to a live GitHub repository with no archival identifier; the guidelines ask for a repository and a data citation with a persistent identifier. | change |
| Disclosure of writing and research tools | The earlier main file carried a disclosure section (`problem131_switching.tex:89-98`). Neither new main file has one, and the guidelines require it in the manuscript when the use goes beyond copy editing. Restore it, updated, as an item of the Statements and Declarations block or as an unnumbered section after the acknowledgments. | must add |
| Acknowledgments (`:113-116`) | `\bmhead{Acknowledgments}` in the back matter, as the template does. Fine. | ok |
| Template macros | `\documentclass[pdflatex,sn-mathphys-num]{sn-jnl}` (`:8`), `\maketitle`, `\backmatter` (`:111`), `\bmhead`, `appendices` environment (`:153-158`), class theorem styles (`:22-35`): all correct. The bibliography is an inline `thebibliography` (`bib_switching.tex`), so `sn-mathphys-num.bst` is never used; the class accepts this, and Springer asks for the list inside the source anyway. | ok |
| Build for Snapp | The build relies on `TEXINPUTS=".;../common/sn-jnl;"` (`:4-6`); Snapp will not have that path. The zip must contain `sn-jnl.cls` (and the `.bst` if a `.bib` is used) next to the main file, all eleven `\input` files and the four figure files. `\graphicspath{{figures/}{../figures/}}` (`:49`) should drop `../figures/`, which points outside the folder. Test once on TeX Live 2021 or Overleaf's 2021 image. | change |
| Headings | Sections and subsections only, plus three run-in `\paragraph` headings in `sec_verify.tex:8,61,144`. At most three levels. The `\paragraph` directly under a section causes the hyperref bookmark warnings; harmless. | ok |
| Figures | Four figures and one table. Fig. 2 (`fig:simplex`, placed in `sec_model.tex:261`) is cited at `sec_intro.tex:43`, before Fig. 1 (`fig:complete-envelope`, placed and first cited at `sec_intro.tex:144-164`). That breaks "consecutive numerical order". All captions end with a full stop, which the caption rule forbids (production usually fixes this, but it costs nothing to fix now). The caption of Fig. 2 (`sec_model.tex:264-278`) runs to fifteen lines and contains derivations; "concise" is not met. Fig. 1 is placed with `[H]` (`sec_intro.tex:151`); acceptable. | change |
| Tables | Table 1 (`sec_firstorder.tex:63-85`) is captioned and cited. | ok |
| References (`bib_switching.tex`) | 49 entries, 38 with DOI links. Numbered in list order, but the list is alphabetical only up to `whittle1955` (`:170`) and then continues with eleven appended entries (Al Ahmadieh to Good, `:175-253`), so numbers jump around in the text. Not a desk reason, but sort before acceptance. Six arXiv preprints, including the author's two companion preprints `paperA` and `paperB`; acceptable in practice. | later |
| Online Resources | None at present. The text still refers the reader to repository files that play the role of a supplement: `sec_secondorder.tex:791-792` (the next-term computation in `supplement.tex` and `removed_proofs`), `sec_complete.tex:130-131` (`supplement.tex`), `sec_verify.tex:136` ("the earlier version"), and Data availability (`problem131_chains_sn.tex:128-136`). Either delete these pointers or make the material Online Resource 1 with a caption and a citation in the text. Since no statement depends on it, deleting is simpler. | change |
| Unproved statement labelled as a lemma | "Lemma L" (`sec_boundary.tex:363-375`) is stated and explicitly not proved for `|G|>=3` (`sec_boundary.tex:359-361`, `434-455`). A referee will object to the label. Call it Hypothesis L (or Conjecture L), and say so in the abstract (`problem131_chains_sn.tex:68-70`), the introduction (`sec_intro.tex:105-108`), Theorem `thm:layer` (`sec_boundary.tex:468`) and `sec_verify.tex:146`. | change |
| Internal vocabulary in the text | `sec_verify.tex:16, 35, 117, 149, 151` speak of "Part I" to "Part IV", which the paper never defines (they exist only in source comments). `sec_verify.tex:35` ("Four modules added on October 24, 2026") and `:117` ("The six older scripts") read as a changelog. | change |
| Source comments | The editable source goes with the submission. `sec_dv.tex:3-5`, `sec_reconstruction.tex:3-10` and `sec_lowtemp.tex:3-8, 372-374` name working files and audits by path. Strip them. | change |
| Cover letter (`paperC/cover_letter.md`) | Still the Electronic Journal of Probability letter, with the old title, and it asks the editor to send the (now withdrawn) supplement to referees. It must be rewritten for JTP: new title, arXiv identifier and licence of this paper if posted, the incorporation of `paperB` (arXiv:2610.09258) and the relation to `paperA` (arXiv:2610.06935), and a statement that the companion paper on the elephant walk under consideration elsewhere (if it is sent to JTP too) is a different study. | must rewrite |
| Length | No limit in the guidelines. Editorial judgment, Part 2. | see Part 2 |

### 1.3 The list of changes before refereeing

Must change (I would return the submission as incomplete or not send it out without these):

1. `problem131_chains_sn.tex:118` and `:120-151`: retitle the block "Statements and Declarations";
   add "Materials availability: Not applicable"; add the disclosure item that the earlier main file
   carried (`problem131_switching.tex:89-98`), brought up to date.
2. `problem131_chains_sn.tex:125-136`: Data availability without the "earlier version". State that
   the computational outputs are archived, and give the identifier.
3. `problem131_chains_sn.tex:137-149`: archive a snapshot of `problem131/paperC` and `problem131/lean`
   (code and data only, not the working notes the repository also tracks) on Zenodo or similar, cite
   it with a DOI in the reference list as a dataset, and point Code availability to it.
4. `paperC/cover_letter.md`: rewrite for JTP (see the table).
5. `sec_boundary.tex:363`, `:468`; `sec_intro.tex:105-108`; `problem131_chains_sn.tex:68-70`;
   `sec_verify.tex:146`: Lemma L becomes Hypothesis L everywhere, and the abstract states the
   result as unconditional for faces of at most three states and conditional beyond.
6. `sec_secondorder.tex:791-792`, `sec_complete.tex:130-131`, `sec_verify.tex:136`: delete the
   pointers to `supplement.tex`, `removed_proofs` and the earlier version, or replace them with
   "Online Resource 1" and supply it.
7. Submission zip: `sn-jnl.cls` beside the main file, `problem131_chains_sn.tex:49` without
   `../figures/`, and a test build without `TEXINPUTS`.

Should change before refereeing (cheap, and a referee will notice):

8. `problem131_chains_sn.tex:61-81`: shorten the abstract to about 200 to 230 words; define or
   remove "winning regions" and "calibrated".
9. `problem131_chains_sn.tex:85`: write "Primary 60J10; Secondary 60J27, 60F10, 60F05, 15A18, 15A29"
   (drop 82C26, consider 15A15) inside the `\pacs` argument so the split shows.
10. `problem131_chains_sn.tex:55`: a shorter title (suggestions in Part 2, which depend on the split).
11. `sec_intro.tex:43`: cite the figures in order (move Fig. `fig:simplex` into the introduction, or
    cite it first after Fig. `fig:complete-envelope`); remove the final full stops of the four
    captions (`sec_intro.tex:154-162`, `sec_model.tex:264-278`, `sec_firstorder.tex:87-125`,
    `sec_firstorder.tex:391-398`) and shorten the caption of Fig. 2.
12. `sec_verify.tex:16, 35, 117, 149, 151`: replace "Part I-IV" by section numbers, and remove the
    dated changelog sentences.
13. `sec_dv.tex:3-5`, `sec_reconstruction.tex:3-10`, `sec_lowtemp.tex:3-8, 372-374`: strip comments.

Before acceptance only: sort `bib_switching.tex` (alphabetically, as the numeric Springer style
expects), add the missing DOIs, and name figure files `Fig1.pdf` and so on.

---

## Part 2. Editorial judgment

### 2.1 Scope

Within scope. JTP publishes "original papers in all areas of probability theory". The core of the
paper is a local large deviation theorem for the occupation counts of a finite Markov chain with a
vanishing switching rate, the location of the mode of that law, and an identifiability question for
the Donsker and Varadhan functional, all of which are standard JTP material. Two parts sit at the
edge of scope and need the right referees: the principal-minor fiber in Section 9.3 is matrix
theory, and Section 10 is metastability in the Freidlin and Wentzell framework. Neither is a reason
to decline. The paper does not depend on its origin in Kagey's problem collection, and the
introduction (`sec_intro.tex:299-302`) is right to mention it only at the end.

### 2.2 What the paper contributes, in the order I would put it to a referee

I keep the author's order but say for each item what is new and what is not.

1. **The stratified local law, with the restriction identity.** Theorem `thm:local`
   (`sec_secondorder.tex:186-193`, proof in Appendix A) is a local limit theorem for the occupation
   vector of the killed chain, uniform in `T>=1`, with the explicit constant `C_F` of Definition
   `def:tilt`; Lemma `lem:discrete` transfers it to the lattice for `T<=N^{1/2}`, and Theorem
   `thm:stratified` (`sec_secondorder.tex:228-238`) puts all faces in one display. The probability
   input is Good's exact law (run expansion and continuum density, `sec_model.tex:160-237`), and the
   paper says so at `sec_model.tex:169-172`, `212-214` and `sec_intro.tex:237-244`. What is new is
   the saddle-point analysis Good proposed and did not do, uniformly in `T`, with its constant and
   its tree formula (Proposition `prop:constant`(b)). The restriction identity
   (Proposition `prop:restriction`, `sec_dv.tex:309-328`) is a four-line observation and the author
   says it is elementary (`sec_dv.tex:333-336`). It organizes the paper but is not a contribution;
   the introduction should not lead with it as one. The consequences that a referee will value most
   are the face maxima with a field (Theorem `thm:facemax`), the crossing equation with the
   universal coefficient `1/2` of `log log N` (Theorem `thm:crossing`) and the tie windows (Theorem
   `thm:window`).
2. **The boundary layer and the near-vertex case.** An exact contour representation of the density
   near a facet (Lemmas `lem:layer-exact`, `lem:layer-exact-discrete`), the Bessel kernel for pair
   faces with an explicit two-sided bound (Proposition `prop:pair-face`), the expansion of the rate
   at a facet with the resistance interpretation of `gamma - q_i` (Proposition
   `prop:layer-constants`), prefactor matching, and the facet theorem (Theorem `thm:layer`),
   unconditional for at most three states and conditional on Lemma L beyond. This is the most
   original analytic part, and also the least finished: the general case is a hypothesis, and three
   subsections are heuristics or numerics (`sec_boundary.tex:646-707`). The near-vertex law
   (Section 8, `sec_vertex.tex`; proofs in Appendix D) is a sharp, elementary result in the regime
   `T` of order `sqrt N`, for the complete graph only.
3. **The crossings and the complete graph.** Theorem C: on `K_d` every face ties at first order, the
   constants decide, the balanced composition crosses each vertex exactly once for every `N`, exact
   balancing holds for every `N` (Theorem `thm:simplex-balance`) and the mode changes exactly once
   (Corollary `cor:simplex-modes`). These are complete and exact, and they are the results of the
   incorporated preprint `paperB`. With a start or a weak field an intermediate face can win
   (Example `ex:K3-start`, Corollaries `cor:weakfield-phases` and
   `cor:weakfield-full-hierarchy`); pleasant, but secondary.
4. **The reconstruction theorems.** The cleanest result of the paper is Corollary `cor:dv-fiber`
   (`sec_reconstruction.tex:123-131`): two irreducible generators have the same Donsker and Varadhan
   functional exactly when they have the same principal minors. This answers the question that Kim
   and Landim raise in their Section 5. Together with Theorem `thm:nonreversible`(b)-(e) it says
   what the functional determines: `Q` up to time reversal when there is no rank-one cut, `Q` when
   it is reversible, and a finite cut-transpose orbit in general. The argument for what is new is
   written out at `sec_reconstruction.tex:713-740`, and it is honest: the fiber of the principal
   minor map is matrix theory (Hartfiel and Loewy, Loewy, Al Ahmadieh, Chatterjee, Ghosh, Gurjar
   and Raj), and the paper adds (a) the translation to generators through the normalization (N),
   with the blockwise description of a cut-transpose as `Q` on one side and `Q*` on the other, (b)
   the data, that is, the Perron-branch lemma (`lem:perron-branch`) and the exposure lemma
   (`lem:exposure`), which read every principal minor off a finite label, and (c) the amplitude
   obstruction in part (f), that from the stationary start the composition law is the same under
   `Q` and `Q*` for every `N` and `T` while a generic start separates the fiber. The reversible
   design (Theorem `thm:reversible-reconstruction`) with minimality and stability, and the uniform
   finite-horizon recovery (Theorem `thm:finite-horizon`), are correct-looking and carefully
   quantified, but they are where most of the 16.5 pages go.
5. **The low-temperature classification and the cycle tree.** The depth of a face is the largest
   depth of a cycle inside it (Theorem `thm:depth`, a short consequence of Catoni's exit theorem, as
   the paper says at `sec_lowtemp.tex:21-27`); away from finitely many heights the winner is a
   cycle of least size among those deeper than the height (Theorem `thm:noncritical`); at a critical
   depth a finite problem with prefactors decides, and a noncycle wins on an open window (Theorem
   `thm:critical-window`, Example `ex:four-state`). The cycle tree is read from a calibrated reward
   (Theorems `thm:attraction`, `thm:cycles-from-depths`, `thm:window-prefactors`). The
   characterization "a set is a cycle exactly when every proper subset is strictly shallower" holds
   with no nondegeneracy, which is a nice clean statement.

### 2.3 Does the introduction argue the reconstruction contribution, and does the reframing work?

Partly. The introduction (`sec_intro.tex:166-213`) does state the question as "which coarse
functionals of the occupation law determine the generator" (`:173-175`), and it names the three
lemmas, including the exposure lemma (`:190-195`). But its explicit sentence of novelty, "What this
paper adds is the translation to generators" (`:199-205`), lists only item (a) above. The exposure
lemma is described as a step and is not claimed, and the amplitude obstruction appears as a remark.
The full three-part statement exists only in the body (`sec_reconstruction.tex:713-740`). A referee
who reads the introduction and the related-work paragraph (`sec_intro.tex:278-290`) will conclude
that the section repackages known matrix theory. Two changes fix this:

- Move the paragraph `sec_reconstruction.tex:713-740` into the introduction in condensed form, and
  state the reconstruction result as an introductory theorem (a Theorem D: the equivalence of
  Corollary `cor:dv-fiber` plus Theorem `thm:nonreversible`(b)-(d)), as the forward results already
  are (Theorems A, B, C). Corollary `cor:dv-fiber` is the paper's most citable sentence and should
  not carry the label "corollary".
- Lead with the Donsker and Varadhan statement, and present the modal-support model second. The
  proof of (i)<->(iii) in Corollary `cor:dv-fiber` (`sec_reconstruction.tex:917-934`) uses only the
  variational formula, the irreducibility of `R_F` and the Perron-branch lemma. It does not use the
  occupation scaling or the controlled observation at all. So the identifiability theorem stands on
  its own, and the modal-support result then reads as a strengthening: even the coarsest functional
  of the law, a single label, loses nothing that the Donsker and Varadhan functional keeps.

On the contrived impression: the reframing in Section 9 (`sec_reconstruction.tex:11-25`) helps,
and the killing interpretation of a nonpositive field (`:29-61`) is a good answer to "where would
such data come from". It does not remove the impression on its own, because the section still
spends most of its pages on the reversible design (constants `bar delta = 2R`, `U = 8R/b^2`, `bar v
= 4R + 4UR^2`, `:166-176`) and on the finite-horizon class with its 78-line uniform face maxima
proof. The design reads as an algorithm specification. With the order reversed as above, the
design becomes a secondary, constructive result (finitely many coordinates suffice and fewer do
not), and the impression mostly goes. The same pattern appears at low temperature, where
Theorem `thm:cycles-from-depths` is a statement about the depths alone and the attraction design is
the way to observe them; the introduction (`sec_intro.tex:226-233`) already says this well.

### 2.4 Is the length justified?

No, not at 100 (article) or 109 (template) pages. JTP has no limit, but papers over 60 pages are
rare there, and the reason is practical: I need referees who can check the proofs in a reasonable
time. This manuscript needs three distinct kinds of expertise (local limit theorems for Markov
additive functionals, identifiability and matrix theory, metastability), and no single referee will
check all of it. The pages split as follows (article build; template build in brackets):

| Unit | Article pp. | sn pp. |
|---|---|---|
| Introduction | 5.5 | 6 |
| 2 Setting and exact law | 4 | 4 |
| 3 Killed functional | 4 | 4 |
| 4 First order | 5 | 6 |
| 5 Second order | 12 | 13 |
| 6 Boundary layer | 11 | 12 |
| 7 Complete graph | 7 | 8 |
| 8 Near a vertex | 1.5 | 1.5 |
| 9 Reconstruction | 16.5 | 18 |
| 10 Low temperature | 11 | 13 |
| 11 Verification | 3 | 3 |
| App. A-D | 15 | 16 |
| References | 4 | 4 |

The logical dependence between the halves is thin and one-directional. Sections 9 and 10 use only
the first-order scores with a field (Remark `rem:first-field`, Proposition `prop:controlled-score`,
which is a few lines from Theorem `thm:first` and Theorem `thm:facemax`), plus the uniform face
maxima of Proposition `prop:uniform-facemax`, which Section 9.4 proves for itself. Nothing in
Sections 5 to 8 depends on Sections 9 and 10. Sections 1 to 8 use the second-order theory
throughout; Sections 9 and 10 use none of it except in Theorem `thm:finite-horizon` and part (f) of
Theorem `thm:nonreversible`. That is the natural line for a split.

A single paper of 60 to 70 pages is possible, but only by removing whole results: the ten pages
listed in 2.8 bring the article build to about 87 pages, and reaching 70 then requires removing
also the finite-horizon subsection (4 pages), the near-vertex law with its appendix (3.5 pages),
the start and weak-field material on the complete graph (2.5 pages) and the window prefactors
(1.5 pages), and compressing the related work and the proofs of minimality and stability (2
pages). That loses more than a split does.

### 2.5 The split I would ask for

**Paper C1.** Suggested title: "Occupation counts of rarely switching Markov chains: a stratified
local law, crossings and the boundary layer".

| Section | Content (current labels) | Article pp. | sn pp. |
|---|---|---|---|
| 1 Introduction | Theorems A, B, C, the layer in prose, related work (Good, Pedler, Hervé and Ledoux, Kontoyiannis and Meyn) | 4 | 4.5 |
| 2 Setting and the exact law | Def. `def:faces`, Lemmas `lem:admissible`, `lem:runs`, `lem:continuum`, Fig. `fig:simplex` | 3.5 | 4 |
| 3 The rate on a face | Prop. `prop:restriction` (as a remark), Lemma `lem:face-monotone`, Props. `prop:rate`, `prop:variational` | 3 | 3.5 |
| 4 First-order face selection | Lemma `lem:upper`, Thms. `thm:first`, `thm:hull`, Fig. `fig:cycles`; the 4-cycle cut to a paragraph | 3.5 | 4 |
| 5 The local law, face maxima, crossings | Def. `def:tilt`, Prop. `prop:constant`, Cor. `cor:symface`, Thms. `thm:local`, `thm:stratified`, `thm:facemax`, `thm:crossing`, `thm:window`, Lemma `lem:weighted-cayley`; reducible face as a short remark | 8 | 9 |
| 6 The boundary layer at a facet | Lemmas `lem:layer-exact`, `lem:layer-exact-discrete`, Props. `prop:pair-face`, `prop:layer-constants`, `prop:layer-prefactor`, Hypothesis L, Lemma `lem:L-two`, Thm. `thm:layer`, Rem. `rem:layer-discrete` | 8 | 9 |
| 7 The complete graph | Prop. `prop:pair`, Cors. `cor:paperA`, `cor:paperB`, Thms. `thm:simplex-crossing`, `thm:simplex-balance`, Cor. `cor:simplex-modes`, Fig. `fig:complete-envelope`; start and weak field as remarks | 5 | 5.5 |
| 8 Near a vertex | Thm. `thm:vertex-uniform-root` and its link to Section 6 | 1.5 | 1.5 |
| 9 Open questions; computations | one paragraph each | 1 | 1 |
| App. A | Local law and first-order bounds, without A.7 | 7.5 | 8 |
| App. B, C, D | Laplace lemma; complete graph; near a vertex | 6 | 6.5 |
| References | | 2.5 | 3 |
| **Total** | | **about 53** | **about 59** |

**Paper C2.** Suggested title: "Which coarse functionals of the occupation law determine a Markov
generator?" or "The Donsker and Varadhan functional, principal minors and modal supports of finite
Markov chains".

| Section | Content (current labels) | Article pp. | sn pp. |
|---|---|---|---|
| 1 Introduction | The question; Theorem D (DV fiber and generator fiber), Theorem E (reversible design), Theorem F (cycles from depths); borrowed versus new | 3.5 | 4 |
| 2 Setting | The killed functional, variational formula and the controlled score law (Prop. `prop:controlled-score`, citing C1 for `thm:first` and `thm:facemax`) | 3 | 3.5 |
| 3 The DV functional and principal minors | Lemmas `lem:RF-irreducible`, `lem:perron-branch`; normalization (N); Thm. `thm:nonreversible`(b)-(e); Cor. `cor:dv-fiber` promoted to a theorem; the cut-transpose example | 5.5 | 6 |
| 4 Reading the minors from modal supports | Lemmas `lem:suppression-nr`, `lem:exposure`; Thm. `thm:nonreversible`(a), (f) | 4 | 4.5 |
| 5 The reversible design | Lemma `lem:suppression`, Thms. `thm:reversible-reconstruction`, `thm:minimality`, `thm:stability` | 4.5 | 5 |
| 6 Finite horizons | Prop. `prop:uniform-facemax` (proof shortened by reference to C1, with only the uniformity argued), Thm. `thm:finite-horizon` | 3 | 3.5 |
| 7 Low temperature | Thms. `thm:depth`, `thm:noncritical`, Prop. `prop:prefactor`, Thm. `thm:critical-window`, Examples `ex:four-state`, `ex:branch-switch` | 6 | 6.5 |
| 8 Reading the cycle tree | Prop. `prop:unperturbed`, Lemmas `lem:laminar`, `lem:killed-depth`, `lem:nested`, Thms. `thm:attraction`, `thm:cycles-from-depths`, `thm:window-prefactors`; the suppression discussion cut to one paragraph | 4 | 4.5 |
| 9 Open questions; computations | | 1 | 1 |
| References | | 2.5 | 3 |
| **Total** | | **about 37** | **about 41** |

Each paper then has one referee pool, and each is of ordinary JTP length. This is not the salami
slicing the guidelines warn against ("A single study should not be split up into several parts"):
C1 answers a forward question about the law of the counts and C2 an inverse question about what the
law determines, with different methods and a one-way dependence. C2 can cite C1 as a preprint. If
the author prefers to keep one paper, I would accept a single resubmission of at most 70 article
pages along the lines of 2.4, but I would not send the present version out.

### 2.6 Referees and the risks I would flag

1. **Local limit theorems and exact occupation laws of finite Markov chains** (for Sections 2 to 8
   and Appendices A to D). For example someone working on quantitative local limit theorems for
   Markov additive processes, in the line of Hervé and Ledoux, or on sharp large deviations for
   Markov chains, in the line of Kontoyiannis and Meyn. Risks to flag: (a) the uniformity of
   Theorem `thm:local` in `T>=1` and in the field, and of Lemma `lem:discrete` up to `T<=N^{1/2}`,
   which carry everything else; the torus representation (Lemma `lem:torus`) and the Laplace lemma
   with a parameter (Lemma `lem:laplace`) are where to look; (b) whether the local law is new
   against the sharp large deviation literature for Markov chains (Ney and Nummelin, Iltis), which
   the paper does not cite; the answer is probably yes because of the killing and the shrinking
   switching rate, but the paper should say why; (c) Theorem `thm:layer` for `k>=4` rests on an
   unproved hypothesis, and the sketch at `sec_boundary.tex:434-455` is not a proof; (d) Theorem
   B(ii) and Theorem `thm:crossing` give the location of every crossing but not its uniqueness
   (`sec_verify.tex:147-149` says so), and the reducible-face exponent is only bracketed (Theorem
   `thm:first`(ii)).
2. **Large deviations of empirical measures and identifiability, with matrix theory** (for Section
   9). For example someone in the Bertini, Faggionato, Gabrielli and Landim school of level-two and
   level-2.5 functionals; a matrix theorist on the principal-minor map (for example from the Loewy
   or Al Ahmadieh line) as a second opinion on Section 9.3 if needed. Risks: (a) whether the
   contribution beyond the cited matrix theory is enough for a probability journal; the referee
   should be shown `sec_reconstruction.tex:713-740` and asked about it directly; (b) the
   Perron-branch lemma, a Zariski-density argument whose step from a real-analytic piece of the
   hypersurface to the whole irreducible hypersurface should be checked; (c) the exposure lemma's
   exceptional set (closed, nowhere dense) and the descent through faces; (d) the definition of
   "the same controlled boundaries" (`sec_reconstruction.tex:106-118`), which quantifies over starts
   and fields and decides what the theorem means; (e) part (f) of Theorem `thm:nonreversible`
   concerns amplitudes that the paper does not show to be observable (`sec_reconstruction.tex:709-711`).
3. **Metastability and Freidlin and Wentzell cycles** (for Section 10). For example someone in the
   Olivieri and Vares, Catoni, or Cirillo and Nardi line. Risks: (a) the order of limits, `N` to
   infinity at fixed temperature and then temperature to zero (`sec_lowtemp.tex:47-56`), and
   whether the constants of Theorem `thm:facemax` may depend on the temperature as the section
   allows; (b) that the hypotheses of Catoni's exit theorem cover every cost matrix used, including
   non-reversible ones and ties of costs; (c) Example `ex:four-state` passes from limiting scores
   to the mode by an argument the formal checks do not cover (`sec_verify.tex:57-58`).

If only two referees can be found, I would pair 1 with 2 and ask referee 2 to read Section 10 at the
level of statements; but that is a reason for the split, not an alternative to it.

General instruction to all referees: the Lean files and scripts are described in Section 11 and in
the Code availability statement, no proof relies on them, and they are not part of what is being
refereed.

### 2.7 Decision

**Return to the author before refereeing: desk changes plus a split (preferred) or cuts to at
most 70 pages.**

Reasons:

1. The desk items of Part 1 (missing disclosure item, Data availability built on an unpublished
   earlier version, no archival identifier for the code, a stale cover letter, an unproved
   statement labelled as a lemma) would make me return the submission anyway.
2. At 100 to 109 pages the manuscript needs three referees of disjoint expertise, and the halves
   share only a thin interface. Two papers of about 53 and 37 article pages can each be refereed
   properly by one or two people.
3. The strongest result of the second half, the identification of the Donsker and Varadhan fiber,
   does not need the modal-support model, and the present arrangement hides it behind 16 pages
   that read as an observation protocol. A separate paper can lead with it, which also answers the
   author's own worry that the controlled observation model looks contrived.
4. The forward half is solid and in scope, but its strongest selling point, the local law uniform
   in `T` with an explicit constant and the universal `1/2 log log N`, is diluted by worked
   examples, heuristics and numerical subsections that a JTP referee will ask to remove anyway.

I would not decline. Both halves are within scope, carefully written and honest about what is
borrowed (Good, the principal-minor literature, Catoni).

### 2.8 The ten most expendable pages, for an editor who wants 60 to 70 pages

Article-build pages, each about one page or a little more; in order of how readily I would cut.

1. `sec_firstorder.tex:6-86`. The worked 4-cycle and Table 1 (about 1.2 pp.). A heuristic that
   says itself "we do not give proofs" (`:22`), and Theorem `thm:hull` with Fig. `fig:cycles`
   makes the same point rigorously. Keep three sentences.
2. `sec_firstorder.tex:87-155`. Fig. 3 and the "comparison" and "general rule" paragraphs (about
   1 p.). The figure duplicates Fig. `fig:cycles`(a); the general rule repeats the introduction.
3. `sec_lowtemp.tex:434-592`. The suppression design: Lemma `lem:mixed-rates`, Proposition
   `prop:suppression-lowtemp` (cited nowhere) and the two- and three-state computations (about
   2 pp.). It proves that a natural design fails. One paragraph saying so, with the two-state
   example, is enough.
4. `sec_secondorder.tex:552-660`. Proposition `prop:forest`, the tree formula on a general face, and
   its proof (about 1.5 pp.). Cited only in the introduction and Section 11; Proposition
   `prop:constant`(b) covers the reversible faces that the rest of the paper uses.
5. `app_torus.tex:574-685`. The forest formula for the covariance (Appendix A.7, about 1.5 pp.),
   used only by item 4.
6. `sec_boundary.tex:434-455` and `646-707`. The unfinished route to Lemma L, the "two corrections
   to the heuristic", the heuristic comparison with the near-vertex case ("not a statement",
   `:685`) and the numerical checks (about 1.6 pp.). Keep two sentences linking Section 8.
7. `sec_secondorder.tex:703-795`. Remark `rem:flows`, the reducible 3-cycle (Example
   `ex:threecycle` and its 20-line proof) and Remark `rem:nextterm`, which points to the withdrawn
   supplement (about 1.3 pp.). The 3-cycle can stay as a two-line remark on the coefficient of
   `log log N`.
8. `sec_verify.tex:35-142`. The dated list of Lean modules and the inventory of eleven scripts
   (about 1.5 pp.). Move it to the README of the archived snapshot; keep one paragraph on what the
   formal proofs cover and the archive identifier.
9. `sec_complete.tex:254-323`. The subsection "A start": Corollary `cor:start-crossings` (cited
   nowhere) and Example `ex:K3-start` with its 21-line proof (about 1 p.). Keep the example as a
   remark without proof, or cite it as a consequence of Theorem `thm:window`.
10. `sec_reconstruction.tex:970-1063`. Proposition `prop:uniform-facemax` and its 78-line proof
    (about 1.4 pp.), which redoes Theorem `thm:facemax` with constants uniform over a class. In the
    split this stays in C2 but can be halved by proving only the uniformity; in a single paper it
    goes with the finite-horizon subsection.

These come to about 13 to 14 article pages. Next in line, if more is needed: the finite-horizon
theorem and its remarks (`sec_reconstruction.tex:1065-1193`, about 2 pp.), the weak field on the
complete graph (`sec_complete.tex:324-427`, about 2 pp., with Fig. `fig:complete-envelope`(b)),
Theorem `thm:window-prefactors` and Remark `rem:design` (`sec_lowtemp.tex:776-870`, about 1.3
pp.), the proofs of minimality and stability (`sec_reconstruction.tex:309-332`, `371-421`, about
1.2 pp.), and the related-work section (`sec_intro.tex:235-302`, trim from 2 pp. to 1.2).
