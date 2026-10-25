# Paper C audit 11: the split, Paper C1 (the forward theory)

October 24, 2026. This note records how `kagey-problems/problem131/paperC` became Paper C1 after
the decision to split Paper C along the interface named in report 10. The second paper is built in
`../paperC2` from a full copy of the folder, and nothing there was touched for this note. Nor were
the Lean folder, paperF or any file outside `paperC`, apart from this note.

Title kept, with a new subtitle: "Occupation counts of rarely switching Markov chains: stratified
local laws, crossings and the boundary layer". This is the C1 title of report 09. A shorter
alternative, if the editor prefers one, is "Stratified local laws and the boundary layer for
occupation counts of rarely switching Markov chains".

## 1. What moved out

- Section 9 (`sec_reconstruction.tex`) and Section 10 (`sec_lowtemp.tex`). Both files are deleted
  from `paperC`. They are in `paperC2`.
- Theorem D of the introduction (`thm:D`), the introduction subsections on what the occupation law
  determines and on low temperature, the borrowed-versus-new paragraph, and the related-work
  paragraphs on the principal-minor matrix theory (Hartfiel and Loewy, Loewy, Engel and Schneider,
  Al Ahmadieh, Chatterjee, Ghosh, Gurjar and Raj, Delmas, Dronnier and Zitt, Wolfer and Watanabe)
  and on the cycle framework (Freidlin and Wentzell, Catoni, Olivieri and Vares, Trouve, Cirillo,
  Nardi and Sohier, Wentzell). Kim and Landim's Section 5 (identifiability) went too.
- The exposure lemma, the Perron-branch lemma and the irreducibility lemma, with the rest of
  Section 9. No forward section used any of them (checked by grepping every `\ref` in the kept
  files against the labels of the two removed files: the only users were the introduction, one
  sentence of `sec_dv.tex` and `sec_verify.tex`, all rewritten).
- Bibliography entries cited only there: `alahmadieh2023`, `catoni1999`, `cggr2024`,
  `cirillonardisohier2015`, `cohen1981`, `ddz2024`, `engelschneider1980`,
  `freidlinwentzell2012`, `friedland1981`, `hartfielloewy1984`, `loewy1986`,
  `olivierivares2005`, `trouve1996`, `wentzell1972`, `wolferwatanabe2021`. The list is now in
  author order (report 06 had asked for that).
- Scripts and outputs that serve only Sections 9 and 10: `verify_reconstruction.py`,
  `verify_finite_horizon.py`, `verify_attraction.py`, `attraction_core.py`, `verify_cycles.py`, and
  `data/verify_{reconstruction,finite_horizon,attraction,cycles}_output.txt`. Copies were checked
  to exist in `paperC2` before deletion. No figure or figure-data file served only those sections
  (`figdata_cycles40/72.json` belong to `fig_cycles`, the 5-cycle figure of Section 4, and stay).
- The MSC codes 15A18 and 15A29 and the keywords "principal minors" and "Freidlin and Wentzell
  cycles".

## 2. What stayed, and why

- Sections 1 to 8 and Appendices A to D, with every statement and proof. The forward sections use
  nothing from Sections 9 and 10, so no result had to be brought back for them.
- Proposition `prop:uniform-facemax` (uniform face maxima on a compact class). It sat in the
  finite-horizon subsection of Section 9, but the brief lists it as part of the interface and asks
  that it be kept in C1 exactly as stated. It is now Proposition 5.16 in a new Section 5.7
  (`sec:uniform-class`), with the statement word for word as before and the same label. The
  objects it needs from the reversible design (the graph G, the bounds R, b, mu_*, the matrix S,
  the products w_ij, the class C, the starts M, the design fields v^{ij}(delta) with
  U = 8R/b^2 and bar v = 4R + 4UR^2, and the compact set V) are defined in the paragraph before
  it, so C1 is self-contained. The proof is the old one, with one sentence added (S is positive
  semidefinite, so q_l <= R), which the old proof took from the reversible-design subsection.
- Theorem `thm:first`, Remark `rem:first-field` and Definition `def:tilt` are unchanged.

## 3. EXPORTS

`paperC/EXPORTS.md` has the full table for the C2 editor. The interface:

| Label | C1 number | Content |
|---|---|---|
| `thm:first` | Theorem 4.2 | First-order face selection, (i) to (iv), for every start |
| `rem:first-field` | Remark 4.3 | The same with a field v, Phi_{tau,v}, strict minimizers carry the weighted maximizers |
| `prop:uniform-facemax` | Proposition 5.16 | Face maxima uniform over the reversible class C, starts M and design fields V |
| `def:tilt` | Definition 5.1 | Tilt, tilted generator, Sigma_alpha, C_F(alpha), K_F, and K_F(v) after it |

The rest of what Sections 9 and 10 of the joint paper cite is also listed there with numbers
(Definition 2.1, Lemmas 2.2 to 2.4, equation (1), Proposition 3.1 to 3.4, Lemma 4.1, equation (6),
Theorem 4.4, Proposition 5.2, Theorem 5.4, Lemma 5.5, Theorems 5.6 to 5.8, equation (9), Appendix
A, Lemma A.2, equation (31), Lemma B.1). Statement numbers agree in the two builds. The only
equation that differs is (31), which is (A3) in the Springer build.

## 4. The author's instructions and the referee's items

| Item | Status | Where |
|---|---|---|
| 1. Abstract without hypothesis, Bessel claim qualified | Done. The abstract says the facet law is the facet law times an explicit kernel with relative error O(1/T) for faces with at most three states, Bessel with small relative error for reversible chains while x = o(T), and without reversibility in logarithmic form and in relative form only for x up to order T^(1/3), with the cycle numerics. 248 words by `wc`. | both main files |
| 2. Hypothesis L removed | Done. `thm:layer` now reads "k = abs(F) in {2,3}" with no condition. Lemma `lem:L-two` states the weighted facet local law for facets with one or two states in full (equation `eq:L-facet`), with the one-state case moved into its proof. Remark `rem:layer-four` (Remark 6.8) states the missing local law for facets with three or more states precisely, word for word the old hypothesis, says the real-z case goes through and the complex case is open, and says nothing uses it. The open-problems paragraph still names the missing step (a Laplace lemma for a complex symmetric Hessian with positive definite real part, with constants). The `hypothesis` environment is gone from both preambles. | `sec_boundary.tex`, both main files |
| 3. Opening of Section 6 | Done. It now says the exponent matches the local law for every irreducible Q, the prefactor matches for reversible Q (Proposition 6.5), and the prefactor match is not proved without reversibility. | `sec_boundary.tex`, first paragraph |
| 4a. w = b u^2 = omega S h | Done. Now w = b u^2 = omega S h / p^2, which is omega S h up to the factor p^(-2) = 1 + O(h). Check: u = h/p, S = hb, omega = 1, so b u^2 = b h^2/p^2 and omega S h = b h^2. | `sec_boundary.tex`, Section 6.7 |
| 4b. Heuristic before `thm:simplex-balance` | Done. The false sentence ("splitting evenly gives the most ways once the run counts are fixed") is replaced. It now says the balanced split maximizes the run-length count when all states have the same number of runs but not in general (one state with a single run against one with several), and that the proof sums over run counts first and uses log-concavity of B_n. | `sec_complete.tex`, before Theorem 7.6 |
| 5a. Kim and Landim numbering note | Fixed. The note in `bib_switching.tex` listed Lemma 5.1, Corollary 5.3, Example 5.4 and Lemma 5.7 as "numbered as in version 2", which no longer matched any use, and it omitted Corollary 5.8, which the old introduction cited. C1 cites Kim and Landim only as a whole (level-two expansions with the flow), so the note is removed and the published version is cited. The C2 editor should restore a note listing the statements C2 cites. | `bib_switching.tex`, `sec_intro.tex` |
| 5b. Results quoted from paperA | Fixed. The plan listed "the run count, the growth of S_{a,b}, the uniform Bessel bound eq:planar-bessel and the expansion of z_N". The run count is our Lemma 2.3, not quoted. The Bessel bound was recalled as a display and never used, so the display is removed. The plan now lists what is used (Proposition 4.1 of paperA in Proposition 7.1, its Lemma 3.2(b) in Appendix D) and what is recalled for comparison only (the expansion of z_N, its Theorem 4.10 in Section 8). | `sec_intro.tex` plan, `sec_model.tex` |
| 5c. "incorporates" for paperB | Fixed in three places (introduction, after Theorem 7.5, both acknowledgments). The text now says that its results on the crossings with a vertex and near a vertex are reproved here as cases of the general theory and that it is cited for the results not reproved (its Theorem 3.2 next term, Theorem 4.4, Theorem 6.2, Remark 6.3, Theorem C.1). | `sec_intro.tex`, `sec_complete.tex`, main files |
| 5d. Exponent in Good's formula | Fixed. The introduction said Good's (10) matches Lemma 2.4 "up to the killing and the exponent n_i - 1". The exponents in the continuum density are m_i - 1 (m_i runs in state i), as `sec_model.tex` already said, so the introduction now says m_i - 1 and that the proof checks them. The discrete statement (Good's (3) with exponents n_i - 1) is unchanged and agrees with audit 05. Good's text itself was not reread. | `sec_intro.tex`, related work |
| 6. "Solved exactly" | Done. The phrase is gone from the abstract, which now lists the three results. The introduction says after Theorem C that parts (i) and (ii) hold at every N and part (iii) gives the mode for large N. | main files, `sec_intro.tex` |
| 7. Notation | Checked in Sections 2 to 8. No statement uses d, delta, tau, D or h in two senses. Changes: tau(z) in the proof of Lemma 6.6 renamed varpi(z) (tau is T/L), and the factor b(z') of Lemma A.2 marked as distinct from the edge bound b in the proof of Proposition 5.16. Lines: Section 7 used ell_S(t,xi) with a different normalization from ell_F of Theorem 5.9 and wrote ell_1, ell_2, ell_3 for sizes in Example 7.10. Section 7.4 now says ell_S(t,xi) = ell^xi_S(t) - ell_{1}(t), the line of Proposition 5.15(c) at tau* = 1 measured from the line -log d - (d-1)t of a vertex without field, with lambda_S = d - abs(S) and log K_S = log D_abs(S) - log d, and ell_k is defined as ell_{1..k}. Example 7.10 now writes g_1, g_2, g_3. The score Phi_tau, the rate J (J_F = d - A^2 on the complete graph, consistent with eq:interior) and lambda (lambda_F = d - k) are oriented as in Sections 3 to 5. Remaining reuse across sections, not within a statement: ell is also the number of rare counts in Section 8, S is the facet time in Section 6 and the symmetrized matrix in Section 5.7, G is a facet in Section 6 and a graph in Section 5.7. | `sec_boundary.tex`, `sec_complete.tex`, `sec_secondorder.tex` |
| 8. Introduction | Rewritten. The forward theory is the paper. The last paragraph names the companion paper `\cite{paperC2}` (bibliography entry "in preparation", placeholder title marked `% placeholder title`). Positioning against Good kept in full (the forward theory needs it). Kim and Landim kept only as rate-functional expansions, with one sentence on how they differ from the face competition. The 2024 principal-minor paper is not needed by the forward theory and is not cited. The introduction also mentions Proposition 5.16. | `sec_intro.tex`, `bib_switching.tex` |
| 9. Verification and scripts | Done. Five scripts and four outputs removed, `verify_all.py` lists the seven remaining scripts and accepts `--quick` (the top-level runner passes it, and the old runner rejected it). `sec_verify.tex` rewritten (Lean coverage without the Section 9 and 10 items, seven scripts, open questions without the C2 items). | `verify_all.py`, `sec_verify.tex` |
| 10. README, TEMPLATE, cover letter | Rewritten. The README history says the identifiability half became the companion paper in `paperC2` on October 24, 2026. The cover letter covers the forward theory only and mentions the companion paper in one sentence. | `README.md`, `TEMPLATE.md`, `cover_letter.md` |
| 11. Top-level files | Not edited. Needed edits in section 8 below. | |

Referee items that belong to C2 and were not touched here: `def:controlled`, `thm:nonreversible`(d)
and (f) with v = 0, irreducibility of Q' in the survival paragraph, the remark on exact ties in
`sec_lowtemp.tex`, the uniformization bound in `lem:killed-depth`, the promotion of the exposure
induction, the observation model and the borrowed-versus-new sentence.

## 5. Builds

Both main files built three times each with `pdflatex -interaction=nonstopmode` (the Springer one
with `TEXINPUTS=".;../common/sn-jnl;"`). The logs show no errors, no undefined references or
citations, no multiply defined labels and no overfull boxes. The Springer log has the usual
underfull vbox warnings of the class with `\raggedbottom`.

| Build | Pages | Joint paper before the split |
|---|---|---|
| `problem131_chains.pdf` (article) | 67 | 95 |
| `problem131_chains_sn.pdf` (Springer) | 74 | 104 |

The target was about 53 article pages. The split alone gives 67. Report 09's estimate of 53 assumed
further cuts that the brief did not ask for and that would remove proved results, so I did not make
them. In article pages, the candidates are the following.

| Candidate | Saves | Note |
|---|---|---|
| Forest formula, Proposition 5.11 and Appendix A.7 | about 4.5 | report 09 left it out of C1. Example 5.14(i) uses part (c) for K_{123}, so the example would need its own short computation |
| Weak field, Section 5.6 and Section 7.4 | about 3.5 | report 09 kept both as remarks. Figure 1(b) shows Corollary 7.12 |
| Start, Section 7.3 | about 1.3 | report 09 kept it as a remark |
| Reducible face, Section 5.5 | about 0.8 | a short remark in report 09 |
| Remark 7.4, winners on other graphs | about 0.6 | |
| Line edit of Sections 3, 5 and Appendix A | 3 to 5 | proofs of prop:rate, thm:window and the torus appendix are the longest |

Taking the first four and a line edit would reach about 53. Per the author's trimming rule,
anything kept as a theorem keeps its proof, and anything cut becomes a remark with its evidence
(here `verify_forest.py` and `verify_weak_field.py`).

## 6. Scripts

`py -I verify_all.py` in `paperC`, October 24, 2026, Python 3.14.3, numpy 2.4.2, scipy 1.17.1,
sympy 1.14.0, mpmath 1.3.0. All seven passed in 479 s.

| Script | Result | Time | sha256 (first 16) |
|---|---|---|---|
| `verify_first_order.py` | PASS | 15 s | 420607c73ce22d1f |
| `verify_second_order.py` | PASS | 51 s | 56ac3bd92af5c54e |
| `verify_forest.py` | PASS | 296 s | 6613127f96ca169e |
| `verify_rate_flows.py` | PASS | 2 s | a65676e745deca35 |
| `verify_weak_field.py` | PASS | 17 s | 87be695600e93f86 |
| `verify_examples.py` | PASS | 11 s | 7e08e629e488826d |
| `verify_layer.py` | PASS | 87 s | 4632e39d8e8c7246 |

The outputs in `data/` are rewritten with these headers. No script was changed, so the hashes
are those of the joint paper's scripts. The README and `sec_verify.tex` quote no hash. The run
time in the Code availability statements and the README is now "about eight minutes". The
docstring of `verify_layer.py` still names two labels removed earlier (`sec:layer-numerics`,
`rem:layer-discrete`). I left it, since editing it changes its hash.

## 7. Declined or left open

- The page target (section 5).
- The older combined logs `data/verify_output*.txt` and the ledgers in `data/` still contain the
  checks of the joint paper. They are historical and I left them.
- The text of Good (1961) was not reread. Item 5d rests on the agreement of `sec_model.tex` with
  audit 05.

## 8. Edits needed outside `paperC`

- `kagey-problems/problem131/README.md`, lines 52 to 83 (the Paper C section). The heading
  "Paper C: Face selection for slowly switching Markov chains" and the paragraph describe the old
  EJP paper and then the joint paper. Replace with Paper C1 (title above, Sections 2 to 8, the
  layer for faces with at most three states, the complete graph and near a vertex) and add a
  Paper C2 entry pointing to `paperC2`. Line 52 says the merged Paper C replaces arXiv:2610.09258
  under the same identifier. With the split, C1 is the paper that contains Paper B's results, so
  say so. Line 13 ("Paper C (slowly switching chains, in `paperC`)") and lines 176 to 177 (build
  instructions) need C2 added.
- `kagey-problems/problem131/verify_all.py`. Add `'c2'` to the `--paper` choices and the default
  list, with folder `paperC2`, and update the docstring times (Paper C quick run now about eight
  minutes). The C1 runner now accepts `--quick`, which this script passes. Before this change the
  call failed with "unrecognized arguments: --quick".
- `lean/PaperC/MAP.md`. The rows for Section 9 and Section 10 statements (`R_F`, (N),
  `thm:nonreversible`, `ex:four-state`, `CriticalWindow`, `GeneratorFiber`, `PrincipalMinors`) now
  belong to paperC2. Proposition `prop:uniform-facemax` is now 5.16 (it was 9.15). The
  verification section is now Section 9 (it was 11). Hypothesis L no longer exists.
- `paperC2`. It needs a bibliography entry for C1 and should cite the numbers in `EXPORTS.md`.
  Its copy of the Kim and Landim note should list the statements C2 cites (Lemma 5.1, Corollary
  5.3, Example 5.4, Lemma 5.7, Corollary 5.8) and the version they are numbered by.
