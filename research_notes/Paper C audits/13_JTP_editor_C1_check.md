# Paper C audit 13: editor's check of Paper C1 before refereeing (JTP)

October 24, 2026. A handling editor's read of `kagey-problems/problem131/paperC` (Paper C1) after
the split recorded in audit 11, against the referee report of audit 10. Both main files were read
in full, with every section, appendix and the bibliography. Nothing outside `paperC` was edited
apart from this note, and `paperC2` was only read.

## Decision

Send to referees after the small fixes below, which are made. The forward theory is complete and
self-contained, no proof uses anything from the companion paper, and the referee's items for
Sections 1 to 8 are done and correct. The paper is still long for JTP at 72 pages in the journal
class. The author should consider one or two of the cuts listed in section 5 before submission,
but nothing there is required for refereeing.

## 1. Referee items in Sections 1 to 8

| Item (audit 10) | Status | Check |
|---|---|---|
| Hypothesis L, `thm:layer` for faces with 2 or 3 states | Verified | `thm:layer` reads k = abs(F) in {2,3} with no condition. Its proof uses the facet chain only through Lemma `lem:L-two`, which is proved for facets with 1 or 2 states (closed Bessel forms). `rem:layer-four` states the four-state case as open. No proof in Sections 7 and 8 or in Appendices A to D cites `thm:layer`, `lem:L-two`, `eq:L-facet` or `rem:layer-four`. Section 8 names `thm:layer` only in its opening sentence, as context. The `hypothesis` environment is gone from both preambles. |
| Bessel claim in the abstract | Verified | The abstract says the kernel holds with relative error O(1/T) near a facet of a face with at most three states, Bessel for reversible chains while x = o(T), and without reversibility in logarithmic form and in relative form only up to order T^(1/3). This matches `thm:layer`(a) to (c) and the discussion after it. The abstract does not repeat the range x <= delta T, which "near a facet" covers. |
| Opening of Section 6 | Verified | Exponent matched for every irreducible Q, prefactor matched for reversible Q (Proposition 6.5), not proved otherwise. |
| w = b u^2 identity | Verified | Section 6.7 now has w = b u^2 = omega S h / p^2. With u = h/p, S = hb and omega = 1 this is exact. |
| Heuristic before `thm:simplex-balance` | Verified | The text now says the balanced split maximizes the run-length count only when all states have the same number of runs. Checked: a state with one run has count 1 whatever its visits, and a state with m >= 2 runs has binom(n-1, m-1), increasing in n. |
| Kim and Landim numbering note | Verified | Note removed, the published version (SPA 189 (2025) 104733) is cited as a whole. |
| Results quoted from paperA | Verified | The plan names Proposition 4.1 (used in Proposition 7.1) and Lemma 3.2(b) (used in Appendix D), and the z_N expansion and the fixed-edge expansion as recalled for comparison. All four uses agree with the text. |
| "Incorporates" for paperB | Verified | Introduction, after Theorem 7.5 and the acknowledgments now say that the results are reproved and the rest is cited. |
| Exponent in Good's formula | Verified against the text | The introduction and `sec_model.tex` both say m_i - 1 for the continuum density (10) and n_i - 1 for the coefficient identity (3). Good's paper itself was not reread here. |
| "Solved exactly" | Verified | Gone. The introduction ties each claim to Theorem 7.5, Theorem 7.6 and Corollary 7.7. |
| Notation within statements | Verified | No statement of Sections 2 to 8 uses d, delta, tau, D or h in two senses. G is a facet in Section 6 and a graph in Section 5.7, S the facet time and the symmetrized matrix. README says so. |
| Split along the interface | Verified | See section 2. |

Items for paperC2 (`def:controlled`, `thm:nonreversible`(d), (f), Q' irreducible, exact ties,
`lem:killed-depth`, the exposure proposition, the observation model, borrowed versus new) were
not checked here.

## 2. Seams of the split

Searched all `.tex` and `.md` files of `paperC` for reconstruction, identifiability, exposure,
Perron-branch, principal minor, cut-transpose, finite horizon, low temperature, cycle tree,
Theorem D, Hypothesis L, and the labels of the removed statements (`thm:D`, `def:controlled`,
`lem:exposure`, `lem:RF-irreducible`, `lem:perron-branch`, `thm:nonreversible`,
`thm:finite-horizon`, `lem:killed-depth`, `ex:four-state`, `sec:reconstruction`, `sec:lowtemp`).

- No reference to a removed section or statement is left in the paper. The remaining hits are
  intended: the companion-paper paragraph at the end of the introduction, one clause in Section
  5.7, "principal minors" in the proof of Proposition 5.11 (the forest formula, a different use),
  and the records in README, TEMPLATE and EXPORTS.
- Fixed. The companion-paper paragraph said that paperC2 reconstructs "the generator from modal
  supports at a finite horizon and at low temperature". At low temperature paperC2 recovers the
  Freidlin and Wentzell cycle tree, not the generator, and the finite-horizon result is for a
  reversible generator on a known graph. The paragraph now says that (`sec_intro.tex` 250 to
  257).
- Fixed. The bibliography entry `paperC2` carried a placeholder title, "Reconstruction of a Markov
  generator from the modal supports of its occupation law". The paperC2 source has the title "What
  the occupation law of a finite Markov chain determines: principal minors, modal supports and
  cycle trees". The entry and README now use it.
- Section 5.7. All design objects (G, b, R, mu_*, w_ij, S, the class C, the starts M, U, bar v,
  v^{ij}(delta), V) are defined before Proposition 5.16. The paragraph read as a fragment of the
  companion paper ("fields of one special form", "reading a generator off finite-horizon data").
  It now says that the proof uses only the compactness of V and that this V is fixed because the
  companion paper uses it. I checked that claim against the proof: every step uses V only through
  the compactness of C x M x V. The statement is unchanged.
- EXPORTS.md. All 36 labels in its tables were checked against the `.aux` of both builds after
  the edits. Every statement number matches (Theorem 4.2, Remark 4.3, Proposition 5.16,
  Definition 5.1, and the rest). Equation (31) is A3 in the Springer build, as stated.

## 3. Line edit

Concision only. No result, proof, example or figure was removed, and no statement or proof was
changed. Cuts:

- Paragraphs that restate a theorem in words right after it: after `thm:first`, `thm:hull`,
  `prop:constant`, `thm:window`, and the restatement inside the comments after `thm:local`,
  `lem:discrete` and `thm:facemax` (the lattice-cell and Gaussian-peak explanation, already given
  in Section 4.1 and in the introduction).
- Overlong transitions: the opening sentence of Section 4, the forward pointer at the end of
  Section 2.1, the opening paragraph of Section 5 (shortened), the opening of Section 7
  (shortened), the sentence before Theorem 7.5, the summary sentence after Corollary 7.7, the
  second half of the sentence after Corollary 7.9, and the two-sentence comment on the identity
  after Proposition 3.1 (merged into one).
- Repeated statements: the three sentences after `thm:layer` that restated parts (a) and (c).
- Restated definitions: the reminder of what Sigma_alpha is, before (eq:interior), and the full
  restatement of the conclusion of Lemma 6.6 inside Remark 6.8, which now says "the conclusion of
  Lemma 6.6 holds for G" and points to (19). The open statement is the same. If the author wants
  the remark to stand alone, the old text is in the history.

Pages: article 67 to 65, Springer 74 to 72. Statement numbers did not move.

## 4. Candidate cuts of proved results (for the author)

Article pages, measured in the build after the line edit.

| Candidate | Saves | What depends on it |
|---|---|---|
| Forest formula, Proposition 5.11 with its proof and Appendix A.7 | about 3 | Example 5.14(i) takes K_{123} from part (c), so it would need a three-line computation of its own. The introduction mentions it once. `verify_forest.py` stays as evidence. |
| Weak field, Section 5.6 and Section 7.4 | about 3 | Figure 1(b) illustrates Corollary 7.12, and the introduction mentions both. The figure would need panel (a) only. |
| Start, Section 7.3 (Corollary 7.9, Example 7.10) | about 1.2 | Mentioned in the introduction. Nothing else uses it. |
| Reducible face, Section 5.5 (Example 5.14) | about 0.8 | Cited in Theorem 4.2's comment, Remark 5.10 and Section 9. A one-paragraph remark could keep the point. |
| Remark 7.4, first-order winners on other graphs | about 0.5 | Nothing uses it. |
| Remark 7.8, an intermediate face at finite N | about 0.3 | Nothing uses it. |

The first three would bring the article version to about 58 pages and the Springer version to
about 64.

## 5. JTP format

Checked against `common/sn-jnl/sn-article.tex` and the class.

- Title page. Title, running title, author with `\fnm`, `\sur`, `\email`, affiliation with
  `\orgdiv`, `\orgname`, `\orgaddress`. ORCID omitted for the reason in TEMPLATE.md. Correct.
- Abstract. 248 words by `wc`, under 250. No citation. It contains inline math ($\tau\log N$,
  $o(1)$, $T^{1/3}$), which the sample's guidance discourages but JTP abstracts commonly have.
  Fixed: $\frac12$ became $1/2$, which reads better in the abstract and in the metadata.
- Keywords. Six, in `\keywords`. Correct.
- MSC. 2020 codes in `\pacs[MSC Classification]`, Primary 60J10, Secondary 60J27, 60F10, 60F05,
  15B48. Correct. The class prints a space before each comma, as in the sample.
- Declarations. The heading is "Statements and Declarations" (JTP's wording, the sample has
  "Declarations"), with the eight items of the sample in its order. Funding, Competing interests,
  Ethics, Consent, Data, Materials, Code, Author contribution. Fixed: the article version said
  "Author contributions" and the Springer version "Author contribution". Both now say "Author
  contribution", as in the sample.
- Acknowledgments in `\bmhead` after `\backmatter`. Correct.
- Appendices inside `appendices`. Fixed: the class did not reset the equation counter at each
  appendix, so Appendix C began at C8 and Appendix D at D10. A reset after `\begin{appendices}`
  gives A1 to A7, C1, C2 and D1 to D4. `eq:A-radii` is still A3.
- Bibliography. Inline `thebibliography`, numbered, sorted by author, with DOIs. Accepted by the
  class. Springer prefers a `.bib` with `sn-mathphys-num.bst` for production, so the entries will
  be restyled there. Not changed.
- Figures. Fixed: Figure 1 used `[H]`, which left the lower 40 percent of page 4 empty in the
  Springer build. It is now a top float, on page 4 of the article build and page 5 of the Springer
  build. The other three
  figures are `[t]` and appear on or near the page of their first reference.
- Consistency of the two builds. Both input the same nine sections, four appendices and the
  bibliography. The `.aux` files agree on every label except the appendix equations, which is the
  documented difference. The abstracts are identical. The front matter differs only in the class
  commands.

## 6. Edits made

| File | Line(s) | Edit |
|---|---|---|
| `sec_intro.tex` | 158 | Figure 1 `[H]` to `[t]` |
| `sec_intro.tex` | 250 to 257 | Companion-paper paragraph made accurate |
| `bib_switching.tex` | 172 to 175 | `paperC2` title, placeholder comment removed |
| `problem131_chains.tex`, `problem131_chains_sn.tex` | 66 | $\frac12$ to $1/2$ in the abstract |
| `problem131_chains.tex` | 141 | "Author contribution" |
| `problem131_chains_sn.tex` | 138 | Equation counter reset per appendix |
| `sec_model.tex` | 71 to 73 | Forward pointer removed |
| `sec_dv.tex` | 46 to 48 | Two sentences merged |
| `sec_firstorder.tex` | 1 to 3, after 131, after 219 | Opening sentence and two restatements removed |
| `sec_secondorder.tex` | 3 to 5 | Opening shortened |
| `sec_secondorder.tex` | after 100, 174, 190, 214, 262, after 450 | Restatements removed |
| `sec_secondorder.tex` | 782 to 786 | Section 5.7 opening, compactness sentence |
| `sec_boundary.tex` | 455 | Restatement of (a) and (c) removed |
| `sec_boundary.tex` | 582 to 588 | Remark 6.8 points to Lemma 6.6 instead of restating it |
| `sec_complete.tex` | 3 to 4, 135, before 155, 228, 270 | Transitions and a restated definition removed |
| `README.md`, `TEMPLATE.md`, `EXPORTS.md` | | Page counts, paperC2 title, figure and equation notes |

## 7. Problems not fixed

- Lemma 6.6 identifies its functions with the rate and constant of Section 6.1 "because for real
  z >= 0 both are the limit of S^{1/2} e^{S J_G} f^{(z)}_G". For the Section 6.1 constant this
  needs the local law of the weighted chain with the end vector e^{(z)} in place of 1, which the
  paper states only in Remark 6.8 ("needs only one change"). The identification feeds the formula
  (18) for c_1 used in Theorem 6.7(c). A sentence in Appendix A saying that the proof of Theorem
  5.4 holds for any positive start and end vectors, with b(z') changed as in Remark 6.8, would
  close it. This touches a proof, so I did not edit it.
- Equation (18) for c_1(beta) is stated with a one-line justification (Kirchhoff's rule). A
  referee may ask for the computation.
- `verify_layer.py` still names two removed labels in its docstring (audit 11). Left, since
  editing it changes its hash.
- The paperC2 source should cite C1 by the numbers in EXPORTS.md (outside this folder).

## 8. Page counts, builds and scripts

| Build | Before | After |
|---|---|---|
| `problem131_chains.pdf` (article) | 67 | 65 |
| `problem131_chains_sn.pdf` (Springer) | 74 | 72 |

Both main files were built three times in `paperC` with `pdflatex -interaction=nonstopmode`, the
Springer one with `TEXINPUTS=".;../common/sn-jnl;"`. Both logs have no errors, no undefined
references or citations, no multiply defined labels and no overfull boxes. The Springer log has
the class's usual underfull vbox warnings and the one bookmark-level warning at `\bmhead`.

`py -I verify_all.py --quick` in `paperC` passed all seven scripts in 497 s:
`verify_first_order.py` 12 s, `verify_second_order.py` 50 s, `verify_forest.py` 310 s,
`verify_rate_flows.py` 2 s, `verify_weak_field.py` 17 s, `verify_examples.py` 11 s,
`verify_layer.py` 95 s. The outputs in `data/` were rewritten by the run.

The auxiliary files (`.aux`, `.log`, `.out`, `.toc`, `.bbl`, `.blg`) were deleted after the
builds, and both PDFs were kept.
