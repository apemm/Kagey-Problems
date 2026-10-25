# 33. Paper C1, review fixes and the journal trim

October 25, 2026. The review of the October 25 updates found no false theorem in C1 and no gap.
It asked for six wording fixes and a shorter journal version. We made both. The arXiv version
(`problem131_chains.tex`, `\arxivbuildtrue`) keeps every proof and has 81 pages. The journal
version (`problem131_chains_sn.tex`, `\arxivbuildfalse`) went from 89 to 72 pages. No statement,
label or exported number changed.

## The six wording points

1. The exponent (abstract, `sec_intro.tex` 15 to 20). The old text said one power of N per
   dimension plus N times the functional. Theorem 5.6(a) has the term -((k-1)/2) log T, which is
   half a power of N per dimension when T is of order N. The abstract and the introduction now
   say that, up to O(1), -log P_N(n) is (|F|-1) log(N/sqrt(T)) plus N times the Donsker and
   Varadhan functional of the chain I + (T/N)Q at n/N. Indeed T J^(h)_V = N (h J^(h)_V), and
   h J^(h)_V is the functional of the discrete chain. The introduction adds that a dimension costs
   a factor N up to a power of log N for T of order log N, and a factor of order sqrt(N) for T of
   order N.
2. The order-m criterion (abstract, `sec_intro.tex` 145 to 165). Proposition 6.2(d) is proved at a
   fixed beta where r_beta has a first nonzero coefficient. The abstract now says "at a profile
   where the rate has a first correction, of order m >= 3". The introduction defines the facet
   profile beta, writes pi^in_beta and pi^out_beta, says that equal laws hold at every beta for
   reversible Q and at some beta for some chains that are not, and says that we do not know
   whether such a term exists whenever the two laws differ. This is the open question of Section 9.
   The cycle example is now "at the uniform profile on a facet of 2 states".
3. "The time goes to one class" (`sec_intro.tex` 84 to 87, `sec_firstorder.tex` 304 to 308). With
   k* = 1 two flat singletons can tie, and then every split of the time is a maximizer. Both
   places now say that the time goes to the classes of least exit rate and least size k*, and to
   one of them when k* >= 2. Theorem 4.5 and its proof are unchanged, as the review says.
4. "Explicit" K^red (abstract, Theorem A). Now "a constant given by a finite-dimensional
   variational formula". The power p_F stays explicit.
5. The proof sketch of Theorem 5.4 (`sec_secondorder.tex` 226 to 228). It said that nothing
   compares the discrete law with the continuum. The bounded-T step of the proof of 5.4(b) uses
   Lemma 5.5. The sketch now says so, and the introduction says that only for bounded T do we
   compare with the continuum.
6. The motivation before Theorem 6.11 (`sec_boundary.tex`, the paragraph before
   `thm:pair-counts`). It cited Lemma 5.5 for P_N(n) near the facet, where n/N is not in a compact
   subset of the open face. It now cites Lemma 5.5 for P_N'(n-hat) only (the path j^N' when
   G = {j}), and Theorems 6.1(a) and 6.12(b) for P_N(n), which give the factor 1 + O(1/T + T^2/N)
   in the range of Theorem 6.12, also for small n_i.

The cover letter, the README and `18_abstract_C1.txt` carry the same fixes.

## The trim

The review's estimate (Appendices C and D, the verification detail and the window theorem) gives
about 8 pages, not 19. Moving the proofs that are not on the main line took the journal version
from 89 to 80 pages, and Proposition 5.12 and the determinant in Proposition 5.2(b) took off
about one more. To reach 72 we also moved some main-line proofs, listed separately below, and cut
every pointer to one sentence. Theorem 4.2(ii) now follows from Theorem 4.5 in both versions, so its direct proof
could move without leaving a gap. Each moved item has one sentence in the journal version, at the
place of the proof, that names the section of the arXiv version. The journal build cites
arXiv:2610.09258v2 as `arxivC1`, an entry that only this build has. The macro `\arxivpointer`
adds "of the arXiv version of this paper" after a reference such as "The proof is in Appendix C".
The introduction of the journal version says once that the arXiv version numbers its sections and
statements as the journal version does and contains every proof. Section 9 of the journal version
says that every statement is proved here or in the arXiv version.

### Moved items that are not on the main line

| Item | Journal pointer |
|---|---|
| Appendix C, proofs of Lemma C.1, Theorems 7.4 and 7.5 and Corollary 7.6 (Lemma C.1 stays stated) | end of Appendix C, and after Theorems 7.4, 7.5 and Corollary 7.6 |
| Appendix D, proofs of Lemmas 8.1, D.1, D.2 and Theorem 8.2 (both lemmas stay stated) | end of Appendix D, and after Lemma 8.1 and Theorem 8.2 |
| Proofs of Lemma 7.1 (weighted Cayley) and Corollary 7.3 | after each statement |
| Section 9, what each script checks and its numbers | Section 9 |
| Theorem 4.4(a) and (b), the hull (the proof of (c) stays) | in the proof |
| Theorem 5.9, the tie windows | after the statement |
| Corollary 5.10, the mode changes | after the statement |
| Example 5.11, the directed 3-cycle | after the example |
| Proposition 5.12 and the continuum route to Theorem 5.7(b) | after 5.12, and at the end of the proof of 5.7 |
| Proposition 6.7 (prefactor matching) and the derivation of equation (18) for c_1 | after each |
| Appendix A.7, the direct proof of Theorem 4.2(ii) | the heading of A.7 stays, with one sentence |
| Proposition 5.2(b), the determinant of Sigma_alpha (the formula for r_alpha stays proved) | in the proof |

### Moved main-line proofs

These are the proofs that a referee may want and that we moved only to reach 72.

| Item | Why it is the least harm |
|---|---|
| Lemmas B.1 and B.3 (the Laplace lemma and its complex form) | the classical Laplace method. Remark B.2 stays and records what the proof uses |
| Lemma A.1 (the derivatives of the Perron root) | standard perturbation of a simple eigenvalue |
| Lemma 6.9 (closed forms for facets of 1 and 2 states) | an explicit computation. The journal version gives J_G in both cases and C_G for one state |
| Lemma 6.10 (the complex critical point) | a contraction argument with uniform constants. The pointer names the contraction |
| Proposition 6.2 (the range of the Bessel form) | it reuses the critical value of the proof of Theorem 6.1(a) |
| Appendices E.3 and E.4 (Theorems 6.11 and 6.12, the counts near a facet) | they follow the proofs of Theorem 6.1(a) and Lemma 5.5 with the state i exact. Lemmas E.5 and E.6 stay stated |

If the editor or the author prefers, the proof of Lemma 6.10 can come back at a cost of about one
page. We built that variant, and it has 73 pages.

### What stays

Every statement stays in the journal version, with its number. The proofs of Theorems A and B
stay, that is Theorems 4.2, 4.5, 5.4, 5.6, 5.7, 5.8 and Corollary 4.6 with Appendix E.1 and
E.2, Lemmas 4.1, 5.5, A.2 to A.6 and Appendix A.8. So do the proofs of Theorems 6.1 and 6.8, of
Propositions 6.5 and 6.6 and of Lemmas 6.3 and 6.4, and all of Sections 2 and 3.

## Checks

- Dependencies. No journal-build proof refers to a removed label (no undefined reference in the
  journal build). Every journal proof that uses a moved proof uses only its statement, and the
  statement carries a pointer. The places that cite a moved proof by name (Remark 4.3 for the
  upper bound with a field, Remark B.2 for the proof of Lemma B.1, the remark after Theorem 5.7 for
  the continuum route) say that the proof is in the arXiv version.
- Labels. Every label of `EXPORTS.md` that C1 still defines is defined in both builds, with the
  same number. Statement and section numbers agree between the builds. The only label of the
  arXiv build that the journal build lacks is `eq:windowline`, inside the proof of Theorem 5.9,
  and the journal build steps the equation counter there, so the later main-text equations keep
  their numbers. Appendix equations are numbered A1, A2 and so on in the Springer class, as before.
  This was checked against the `.aux` of both builds.
- Builds. Both build clean in three passes, with no undefined or multiply defined reference or
  citation and no overfull box. The arXiv build has 81 pages and contains no pointer to an arXiv
  version. The journal build has 72 pages and 32 pointers.
- `py -I verify_all.py --quick` passes, 9 of 9 scripts in 236 s. No script changed.
- Aux files and `__pycache__` removed. The PDFs are kept.

## Files

- `kagey-problems/problem131/paperC/`. Main files (abstract, the macro), `bib_switching.tex` (the
  entry `arxivC1`), `sec_intro.tex`, `sec_firstorder.tex`, `sec_secondorder.tex`,
  `sec_boundary.tex`, `sec_complete.tex`, `sec_vertex.tex`, `sec_verify.tex`, `app_torus.tex`,
  `app_laplace.tex`, `app_complete.tex`, `app_vertex.tex`, `app_counts.tex`. `README.md` (the
  exponent, the order-m statement, K^red, page counts, the list of arXiv-only proofs, history),
  `cover_letter.md` (the same fixes, and a paragraph that says which proofs are in the arXiv
  version), `EXPORTS.md` (a change note for paperC2, notably that the proof of Proposition 5.12 is
  now only in the arXiv version).
- `research_notes/Paper C audits/18_abstract_C1.txt` and `18_arxiv_form_C1.txt` (the new abstract,
  1663 characters, and the source note), `18_arxiv_v2_preparation.md` (an update: the bundle needs
  `app_counts.tex`, and v2 must contain every proof because the journal version cites it).

## For paperC2

Its citations of C1 stay valid. The proof of Proposition 5.12 is now only in the arXiv version,
so a citation of its proof should name arXiv:2610.09258v2.
