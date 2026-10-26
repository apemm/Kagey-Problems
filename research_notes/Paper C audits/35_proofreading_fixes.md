# 35. Paper C1, proofreading fixes and the new journal build

October 25, 2026. The proofreading of commit 1e33329 (summary and 86 findings, each with a quote and
a proposed fix) found no error in a theorem. We fixed every finding that still applies after the
journal build was restructured, and we restructured it. The arXiv version
(`problem131_chains.tex`, `\arxivbuildtrue`) has 82 pages (81 before, the new note before the
declarations and a definition in Appendix C added a page). The journal version
(`problem131_chains_sn.tex`, `\arxivbuildfalse`) has 79 pages (72 before). No statement, label or
exported number changed.

## The journal build

- Every proof that audit 33 moved to the arXiv version is back in the journal version. These are
  Lemmas A.1, B.1, B.3, 6.9 and 6.10, Proposition 6.2, Appendices A.7, E.3 and E.4, Theorem 4.4(a)
  and (b), the determinant in Proposition 5.2(b), the continuum route to Theorem 5.7(b), Theorem 5.9,
  Corollary 5.10, Example 5.11, Proposition 5.12, Proposition 6.7 and the derivation of (18), and
  the detail of the computations in Section 9. We did this by removing the switch around each of
  them, so both builds now print the same text there.
- The journal version leaves out Sections 7 and 8 and Appendices C and D. The main file does not
  input `sec_complete.tex`, `sec_vertex.tex`, `app_complete.tex` and `app_vertex.tex`. It sets the
  section counter to 8 before `sec_verify.tex` and to 4 before `app_counts.tex`, so Section 9 and
  Appendix E keep their numbers. The journal sections are 1 to 6 and 9, and its appendices A, B and
  E. The organization paragraph of the introduction says so.
- In place of Theorem C, Figure 1 and the text after them, Section 1.3 of the journal version is one
  paragraph, "The complete graph and the layer near a vertex". It states the unique crossing with
  its equation and a_k, exact balancing for T <= N/d, the single mode change, and the vertex law
  with the lattice kernel, and it cites the arXiv version for them. The subsection keeps its number,
  so Section 1.4 does too.
- Places outside Sections 7 and 8 that used them now have a journal branch. The definition of B_n
  is written out where the lattice kernel uses it (Section 6.9), and so is the function I(y) in the
  proof of Theorem 6.11(d). The remark after Theorem 6.11, the range paragraph after Theorem 5.7,
  the paragraph before Theorem 5.9 (now self-contained, with lambda_F = d - |F|), Section 9 and the
  introduction cite the arXiv version for the complete graph, each with `\cite{arxivC1}`.
- Table 1 in the journal version has the rows for Theorem 3.3 and Lemma 3.4 of Paper B. The
  sentence before it names the results of Paper B that Sections 7 and 8 of the arXiv version
  reprove and points to Table 1 there.
- The macro `\arxivpointer` is gone, since no journal pointer to a single proof is left. No journal
  sentence says "this appendix proves" over a pointer, and no "Proof of" heading stands over a
  pointer. The bibliography entry `arxivC1` now describes v2 as the arXiv version with Sections 7
  and 8.
- The journal abstract drops the complete-graph sentence and has 248 words, counting each formula
  as one word (the JTP range is 150 to 250). The arXiv abstract keeps that sentence and has 263
  words and 1701 characters.

## Numbers

We compared the `.aux` of both new builds with those of the previous builds (built from commit
1e33329). No label of the arXiv build changed its number. Every label of the journal build has the
number it has in the arXiv build, apart from the appendix equations (A1 to A7 against 26 to 32, the
class convention noted in `EXPORTS.md`) and the two figures, which are numbered from 1 in the
journal build. Every label of `EXPORTS.md` that C1 defines is defined in both builds with the same
number. C2 cites Lemma 2.2, 2.3, 3.2, 4.1, Propositions 3.1, 3.3, 3.4, 5.2, 5.12, Theorems 4.2, 4.4,
5.6, 5.7, 5.8, Remark 4.3, Definition 5.1 and equations (1) and (6), and each lands on the same
statement in both builds. The proof of Proposition 5.12, which C2 imports, is again in the journal
version.

## The findings of the summary

1. Abstract crossing sentence. Both abstracts now read "If an admissible face has Delta >= 1 more
   states than another and an exit rate smaller by delta > 0, we locate every crossing of their
   largest probabilities for large T <= N^(1/3) up to O(1/log N)." The dangling "there" is gone.
2. Lemma D.1. "On (0, infinity) the polynomial B is convex, log B is concave and kappa is
   nondecreasing."
3. Section 8. "nonnegative coefficients".
4. Section 8. "where X, a gamma variable plus a compound binomial sum, has mean 2+(b-1)u".
5. Section 9. The two test cases are joined by "namely", which keeps them two without a colon.
6. Heuristic for p_F. "contributes h^(k*-1) T^(-(k*-1)/2)".
7. `sec_secondorder.tex`, proof of Proposition 5.12. "since q_ij q_ji >= w_*^2 and q_ji <= R".
8. After Theorem 5.6. "the coefficient of L in (b)".
9. Section 7, after Corollary 7.3. "for the uniform start" added.
10. Before Theorem 4.2. "the only part that bounds the face maxima of reducible faces".
11. Unbound symbols. mu and q_i are defined in the first sentences of the introduction and in
    Theorem A ("the law mu of X_1", also in Theorem B), T_1 in Theorem A ("with T_1 a large
    constant (Theorem 4.5)"), N_j in Remark 4.3 ("of length N_j"), N_0 in Lemma E.1 ("There are N_0
    and C_0"), omega_max in the proof of Lemma E.5 (defined as the maximum of omega_beta over K), and
    D_x = diag x after Proposition 3.4 and in Section 5.5.
12. Theorem A. The face now has k = |F| states, the first display is stated "If k >= 2", and the
    continuum form has "(with K_{i} = mu_i)".
13. Table 1. Lemma 3.4 of Paper B (occupation covariance, the formula for det Sigma) was checked
    against the archived v1 (`archive/paperB/simplex_thresholds.tex` and the PDF, where it is
    Lemma 3.4 between Theorem 3.3 and Lemma 3.5). It is reproved in full by Proposition 5.2(b). The
    arXiv row now reads "Lemmas 3.4 and 3.5, Prop. 3.6", and the journal table has its own row.

Overloaded letters. The scalar remainder of Proposition 6.2 is now fraktur r_beta, in its
definition, the statement, the proof and Section 9. The angular cutoff in the proof of Theorem 6.8
is epsilon_0. The other clashes are fixed as in findings 1, 3, 9, 10, 11 and 18 below.

## The 86 findings

| # | Place | Fix |
|---|---|---|
| 1 | app_complete, proof of Cor. 7.6 | delta renamed eta |
| 2 | app_counts, Lemma E.1 | "There are N_0 and C_0" |
| 3 | app_counts, proof of Lemma E.4 | compact set renamed calligraphic E |
| 4 | app_counts, proof of Lemma E.5 | omega_max defined |
| 5 | app_vertex, Lemma D.1 | domain at the front |
| 6 | abstract | "minus the log-probability of counts n with support F" and "with exit rates q_i" |
| 7 | abstract | crossing sentence, both builds |
| 8 | sec_boundary, Prop. 6.2 | remainder renamed fraktur r_beta |
| 9 | proof of Lemma 6.10(c) | map renamed calligraphic G, contraction calligraphic T_z |
| 10 | proof of Lemma 6.10(e) | b_1(z) = (A(z)_{j1})_{j>=2} |
| 11 | proof of Theorem 6.8 | sentence saying that Psi and chi play the roles of Psi and a in Lemma B.3 |
| 12 | proof of Theorem 6.8 | cutoff renamed epsilon_0 in Steps 1 and 3 |
| 13 | proof of Theorem 6.1(a) | epsilon_0 fixed with B_Psi epsilon_0 <= 3/4, gap eta = (1 - cos epsilon_0)/2 |
| 14 | sec_complete | "for the uniform start" |
| 15 | sec_dv and sec_secondorder | D_x = diag x |
| 16 | Remark 4.3 | "of length N_j" |
| 17 | after Theorem 4.5 | factor h^(k*-1) |
| 18 | after Corollary 4.6 | corollary constant renamed b_FG, and "where q_12 = b" |
| 19 | introduction | mu and q_i defined |
| 20 | Theorem A | K_{i} = mu_i, and the k >= 2 clause restructured |
| 21 | Theorem A | T_1 introduced |
| 22 | after Theorem 5.6 | "coefficient of L" |
| 23 | proof of Prop. 5.12 | index fixed |
| 24 | sec_vertex | "nonnegative" |
| 25 | proof of Lemma 6.10(e) | "the first fact" and "the second fact of Appendix A" |
| 26 | Section 6.8 | headings name Theorem 6.1 |
| 27 | intro, Table 1 | Lemma 3.4 added |
| 28 | sec_verify spacing | the switches are gone, so the control spaces are too |
| 29 | Appendix C title | no longer applies, Appendix C is arXiv only |
| 30 | Appendix C, refresh | definition of a refresh added to the first paragraph |
| 31 | E.3 and E.4 headings | proofs restored |
| 32 | app_counts pointer | removed with the restored proofs |
| 33 | Appendix B "proves" | proofs restored, the sentence is true |
| 34 | Appendix A title | A.7 restored, the title is true |
| 35 | appendix equation numbers | kept as before (A1, A2 in the Springer class), as the finding allows |
| 36 | A.7 heading | proof restored |
| 37 | Appendix D title | no longer applies, Appendix D is arXiv only |
| 38 | bibliography [39], [40] | paperB says "version 1 of the arXiv entry of [40]" in the journal build |
| 39 | journal abstract | 248 words |
| 40 | sec_boundary line 6 | proofs restored, the sentence is true |
| 41 | "The next proposition proves this" | proof restored, the sentence is true |
| 42 | sec_boundary pointer | removed with the restored proof |
| 43 | Lemma 6.9 "given in the proof" | proof restored |
| 44 | "proofs ... in Appendix E" | proofs restored |
| 45 | Lemma 7.1 "classical" | arXiv only, keeps its short proof |
| 46 | sec_complete pointer | removed |
| 47 | "the same arXiv entry" | "this arXiv entry" |
| 48 | sec_secondorder pointer | removed with the restored proof |
| 49 | Lemma A.3 | "and their series are dominated ..., in place of having nonnegative coefficients" |
| 50 | proof of Theorem 8.2 | "The final inequality of the display" |
| 51 | proof of Prop. 6.5 | "For a pair face, beta = (1) and ..." |
| 52 | proof of Lemma 6.9 | "the computation above" |
| 53 | proof of Theorem 6.1(c) | "hence on the whole disc by holomorphy" |
| 54 | after Theorem 6.12 | "as in the proof of Lemma 5.5" |
| 55 | after Cor. 7.6 | proof sentence moved to the end of the paragraph, referent named |
| 56 | before Theorem 4.2 | see summary 10 |
| 57 | after Theorem 5.6 | comma after "For a singleton" |
| 58 | continuum route | journal branch gone, and "together with" in the remaining text |
| 59 | Section 9 | two test cases, see summary 5 |
| 60 | sec_vertex | "upper bounds on S_n bound P_N(n) for every start" |
| 61 | sec_vertex | "convergence of Laguerre polynomials to Bessel functions" |
| 62 | sec_vertex | "the elasticity kappa(y) of B" |
| 63 | sec_vertex | see summary 4 |
| 64 | Appendix A opening | "Except in Appendix A.7" |
| 65 | A.2 | "the switching rates A_F of the killed chain" |
| 66 | proof of Lemma 6.3 | "accounts for the term -z c^- o c^+ of d(z)" |
| 67 | Section 6.9 | Lambda-tilde is the integrand without e^(-q_i x), e^(x/z) and z^(-2) |
| 68 | sec_complete | "the numbers of blocks between refreshes" |
| 69 | sec_complete | "edge centers" |
| 70 | sec_dv | "Donsker and Varadhan functional" |
| 71 | introduction | "the count vector n, which we also call a composition" |
| 72 | introduction | classes renamed components |
| 73 | before Theorem 5.9 | "switch value tau* = tau_i of Theorem 4.4(a)" |
| 74 | Appendix A opening | the sentence no longer starts with a symbol |
| 75 | A.8 | comma after the display of a_h |
| 76 | Appendix D journal sentence | no longer applies |
| 77 | bibliography | ties before the volume in three entries |
| 78 | bibliography | MathSciNet forms for PNAS, JRSS B and Rev. Modern Phys. |
| 79 | bibliography, DLMF | "Release 1.2.4 of 2025-03-15" added (see below) |
| 80 | bibliography | paperB and arxivC1 in the form "preprint, 2026. arXiv:..." |
| 81 | Section 4.1 | "1--2--3" |
| 82 | Theorem 4.2 | \textup{(H)} |
| 83 | Figure caption | "1--2--3" |
| 84 | Section 5 theorems and Prop. 6.7 | \textup{(H)} |
| 85 | Theorem 8.2 | stray control space removed |
| 86 | after Theorem 8.2 | comma after the reference |

## For the author

- The DLMF release in the bibliography is the release current at the last check we know of. If the
  equations were read in a later release, change the release and date.
- The new note before the declarations, in both builds and marked with a comment, has to be
  reviewed by the author before posting.
- The bookmark warning of the Springer class at the acknowledgments (`\bmhead`) was there before
  and is not a reference warning.

## Checks

- Both builds compile in three passes with no undefined or multiply defined reference or citation
  and no overfull box. The arXiv build has 82 pages and the journal build 79.
- `py -I verify_all.py --quick` passes, 9 of 9 scripts in 216 s. No script changed. The outputs in
  `data/` differ only in their date and run time.
- Aux files and `__pycache__` removed. The PDFs are kept.

## Files

- `kagey-problems/problem131/paperC/`. Both main files (abstracts, the switch comment, the counters
  and the inputs of the journal build, the new note and the declarations), `sec_intro.tex`,
  `sec_model.tex`, `sec_dv.tex`, `sec_firstorder.tex`, `sec_secondorder.tex`, `sec_boundary.tex`,
  `sec_complete.tex`, `sec_vertex.tex`, `sec_verify.tex`, `app_torus.tex`, `app_laplace.tex`,
  `app_complete.tex`, `app_vertex.tex`, `app_counts.tex`, `bib_switching.tex`, `README.md`,
  `cover_letter.md` and `EXPORTS.md` (a change note).
- `research_notes/Paper C audits/18_abstract_C1.txt`, `18_arxiv_form_C1.txt` (the new abstract and
  the page count) and `18_arxiv_v2_preparation.md` (an update).
