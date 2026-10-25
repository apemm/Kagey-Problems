# 24. Paper C1: revision after the JTP referee report (item 23)

Date: October 25, 2026. Folder: `kagey-problems/problem131/paperC`. This revision was done in two
sittings. The first (late on October 24) edited `sec_intro`, `sec_model`, `sec_firstorder`,
`sec_secondorder`, `sec_boundary`, `sec_complete`, `sec_vertex` and `bib_switching` and stopped
before the build and the scripts. The second checked each of those edits against the report and
the proofs, repaired what needed it, and finished the rest. Below, "kept" means an edit of the
first sitting that was checked and left as it was, and "repaired" means one that was changed.

## Major items

**M1 (the non-reversible restriction). Proved.** New Proposition 6.10 (`prop:layer-cubic`, first
sitting, kept after a full check). For `1 <= x <= delta T`,
`log f_F/(f_G B_beta) = -kappa_beta x^(3/2) S^(-1/2) + O(sqrt(x/T) + x^2/T)` with
`kappa_beta = d^3_z J_G(beta,0)/(6 omega^(3/2)) + (gamma - q_i)^2/omega^(1/2)`, zero for reversible
Q. For the cycle q12 = q23 = q31 = 2, q21 = q32 = q13 = 1, i = 3, beta = (1/2,1/2),
`J_G(beta,z) = 3 - 2z - sqrt((2+z)(1+4z))`, the derivatives at 0 are `-(2 + 9 sqrt2/4)`,
`49 sqrt2/16`, `-1323 sqrt2/64`, and `kappa = -49/(64 sqrt omega) = -0.33633`. I rederived the
expansion of the maximum (the `p'(w_0)^2/(4 omega^(3/2))` term), the convexity of lambda on
`[z_*/2, 2z_*]`, the identification of `min lambda_0` with the Legendre form of Proposition
6.4(i), and the sign conventions, and checked the numbers in sympy. Repaired: the consequence
paragraph after the proposition (the old wording claimed a sign before the main term dominates;
it now gives the two-sided bound and proves that the ratio tends to 1 if and only if
`x/T^(1/3) -> 0`, for `x <= delta' T`), and the sign in Section 1.2 (the term in E is
`+49/(64 sqrt(ab)) x^(3/2) S^(-1/2)`, the first sitting had written the coefficient of kappa). The
abstract, Section 1.2 and Section 9 now state what is proved, and the word "real" is gone.
Script check: part K of `verify_layer.py` (exact derivatives, kappa, omega and gamma against the
tilt, and the ratios of part J against `-kappa x^(3/2)/S^(1/2)`).

**M2 (every change of the mode). Proved, as a corollary with a genericity hypothesis.** New
Corollary 5.10 (`cor:mode-changes`, first sitting). Hypotheses: symmetric support or full start,
and no third point of the hull on an edge (this excludes the degenerate kinks explicitly). Then
for `T in [aL, bL]` at distance at least `C/L` from the roots `T_{N,i}` of the crossing equations
of consecutive hull vertices, every global mode sits on a face with point `v_i`. The proof uses
Theorem 5.9(ii) near each switch value and Theorem 4.2(ii) between them, which gives the
uniformity in tau that the referee asked for without a new version of 4.2(iii). Kept after a
check, and repaired: the proof was shortened, and the sentence after it no longer says that the
changes in a tie window "are crossings of Theorem 5.8". It now says that the kink sits where
Theorem 5.8(iii) puts the crossing, and that three or more points on an edge are located only up
to o(1). The abstract, Section 1 and Section 1.1 now match the corollary (Section 1.1 now names
the support hypothesis). The intro's definition of a crossing is now an equality of face maxima.

**M3 (classical literature). Done.** References verified this sitting (Crossref API for the
DOIs, MathNet record via search for Dobrushin, arXiv API for 2602.06829):
- Dobrushin, Izv. Akad. Nauk SSSR Ser. Mat. 17(4) (1953) 291-330 (MR0058150). The English
  translation page range could not be confirmed (sources give 97-134 and 97-196), so it is not
  cited.
- Cekanavicius and Vellaisamy, Bernoulli 16(4) (2010) 1114-1136, doi:10.3150/09-BEJ246.
- Gabriel, Biometrika 46(3-4) (1959) 454-460, doi:10.1093/biomet/46.3-4.454.
- Ney and Nummelin I and II, Ann. Probab. 15(2) (1987) 561-592 and 593-609,
  doi:10.1214/aop/1176992159 and 10.1214/aop/1176992160.
- Miller, Ann. Math. Statist. 32(4) (1961) 1260-1270, doi:10.1214/aoms/1177704865.
- arXiv:2602.06829 (Benaim, Bravo, Faure, v2 April 2026): almost sure convergence of the
  occupation measure of time-inhomogeneous chains with vanishing mutation rates. Relevant, and
  already cited with Dietz and Sethuraman and Bouguet and Cloez.
- Wu, Rev. Mod. Phys. 54 (1982) 235-268, for the Potts identification (minor 9).
Each is positioned in one sentence in Section 1.4, with a sentence on what is new (first sitting,
kept).

**M4 (overlap and organisation). Done.** The overlap with arXiv:2610.09258v1 is stated in one
paragraph of the introduction under the build switch. The repeated citation after Theorem 7.4
(the next term `1/(8T)`) was removed this sitting, and the cover letter now says plainly which
results are reproved and which are cited. Proposition 5.12 now holds for an arbitrary compact set
of fields, without U and bar v, with the graph written `\mathcal G` and the edge bound `w_*`, and
one sentence says that the companion paper uses it and why it belongs here (first sitting, kept
after checking the compactness and constants argument). Theorem 4.2(i) stays, its proof cites
Theorem 5.6, and the text says that Section 5 does not use Theorem 4.2.

## Minor items

1-2. Abstract: the facet hypotheses (irreducible face, facet irreducible with start mass, x below
a small multiple of T) and `T <= C log N` for the single mode change. Rewritten this sitting, 248
words by whitespace count (the old one was 247).
3. The 4-cycle gaps: 0.035 (vertex and pair) and 0.087 (pair and cycle), recomputed with the
constants `1/4`, `1/sqrt(2 pi)`, `8/pi^(3/2)` (root 30.06712 against 30.03229, and 59.11167
against 59.02486), and now asserted in `verify_second_order.py`.
4. Notation: the graph of Section 5.5 is `\mathcal G`, the edge bound `w_*`, the point set
`\mathcal S`, the homogeneous rate `\bar J_F`, the generator of Lemma A.1 `\widetilde Q`, and
`Delta(x)` of Appendix C is `g(x)`. The facet G of Section 6 is kept, since no statement uses it
together with the second face of Theorem 5.8 or with `G_F`.
5-6. Theorem 5.9 says what its constants depend on, and a paragraph after Theorem 6.6 explains why
`z_0` is not explicit (first sitting, kept).
7. `verify_forest.py` retired from `verify_all.py`, README and Section 9, output deleted, the
script kept with a note. Stale numbers relabelled in the docstrings and printed headings of
`verify_first_order.py`, `verify_second_order.py`, `verify_examples.py`, `verify_rate_flows.py`
and `verify_layer.py`. Section 9 now says 6 scripts.
8. `\end{document}` removed from `bib_switching.tex` (first sitting).
9. Potts reference added (Wu 1982).
10. Proposition 6.4(iii): the uniform quadratic bound `c min(|psi - psi_0|^2, r^2)` from concavity
along segments (first sitting, kept after checking the convexity argument).
11. Theorem 6.9(b), x <= 1: the term `c_1 z` times the Gaussian factor is expanded explicitly
(first sitting, kept after checking the Bessel moments).
12. Good's formulas are now named once, after Lemmas 2.3 and 2.4.
13. Title kept.
14. Section 9 now says that we know no example where the zero of `D_N` is not unique and that
uniqueness is proved only in special cases, and that Example 5.11 agrees with the conjectured
power for reducible faces (question 2). Questions 1, 3 and 4 are not taken up.

## Cuts to stay within 60 pages

The roadmap paragraph of the introduction, the preview of Section 8 in Section 1.2, the paragraph
on the overlap of Theorem 6.9(a) with Theorem 5.4 at the end of Section 6 (its claim was not
proved), two sentences of Section 7, the display of the discrete pair face in Section 8, most of
the Lean paragraph of Section 9. The article build has a compact declarations paragraph and a
`\small` bibliography, and Figures 1 and 2 are slightly narrower.

## Numbers, builds and scripts

- No exported number moved (checked against the `.aux` of both builds). EXPORTS.md has a dated
  note: Proposition 5.12 now takes any compact set of fields, its edge bound is `w_*`, and the new
  Corollary 5.10 and Proposition 6.10 are listed. Paper C2 should quote Proposition 5.12 with its
  own design set as V and rename the edge bound.
- Article build 60 pages (was 59), Springer build 67 (was 65). Both have no undefined reference,
  no multiply defined label and no overfull box. The only warning is the hyperref bookmark level.
- `py -I verify_all.py --quick`: 6 of 6 passed in 200 s. Every output header carries the sha256 of
  the current script.
- Updated: `18_abstract_C1.txt` and `18_arxiv_form_C1.txt` (abstract, 1436 characters, and 60
  pages), README, TEMPLATE, cover letter.
