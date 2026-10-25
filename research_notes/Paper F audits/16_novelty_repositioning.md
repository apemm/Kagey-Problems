# 16. Novelty repositioning, hygiene and length (Paper F, EJP)

October 25, 2026. Folder touched: `kagey-problems/problem131/paperF`. This pass covers sections 1, 3
and 4 of the plan of October 24 (novelty, hygiene, length). It does not add O1 or O2. The sentence
"the number of local extrema inside the layers is not determined here" is kept in the introduction.

## 1. Theorem C and the physics credits

- Abstract and the paragraph "The initial run" of Section 1.2 now say that Theorem C answers, for
  the lattice walk, the question of Wang, Schulz, Deng and Barkai on the effect of the initial
  preparation on the rare fluctuations.
- Related work quotes them verbatim: "the effect of initial preparation on the rare fluctuations is
  left for a future work" (PRE 98 (2018) 042139, Section VIII, Discussion, last paragraph before
  the acknowledgments). The same paragraph of theirs says they assumed a start in the up or down
  state with equal probability.
- Their results are now attributed by regime: the occupation-time infinite density for 1<alpha<2 is
  their Eq. (83); the tail-times-renewal-density layer is for the backward recurrence time, Eq. (52);
  the occupation-time atom and layer are for 0<alpha<1, Section VII.A.
- Wang, Vezzani, Burioni and Barkai (PRR 1 (2019) 033172) are credited for the formal comparison of
  the ordinary and equilibrated start, Eqs. (28), (46), (47), in Section 1.3 and after
  Corollary `cor:stationary`. Their extra term xi^(-alpha) and the atom of order t^(1-alpha)
  correspond to the term ell^(-alpha_+)/mu_- of (b) and the atom of (a).
- Schulz and Barkai (PRE 91 (2015) 062129) are credited for the occupation-time infinite density with
  two sojourn laws, Eq. (25), and the formal matching with the stable bulk, Eq. (26).
- Vezzani, Barkai and Burioni (PRE 100 (2019) 012108) are credited for the two-term mechanism, Eqs.
  (12) and (13) (jump still in progress at T, and completed jump at the renewal rate). The old
  sentence "What is new there is ... a complete giant run ... and a censored run" is gone. The new
  sentence claims the proof on the lattice at fixed time, the exact kernels gamma and kappa at finite
  distance from the end, uniformity up to the endpoint, the layer and the role of (LR).
- Melbourne, Pene and Terhesiu: the sentence now says their measure is the invariant one, which
  corresponds to the stationary initial run.

## 2. The three-peak picture

The last sentences of the first paragraph now cite Zaburdaev, Denisov and Klafter, RMP 87 (2015),
Section II.A.2 and Fig. 2, for the stable bulk "sandwiched between two running ballistic delta-like
peaks" formed by walkers still in their first flight. The text says that on the lattice these peaks
are the endpoint atoms and the boundary layers, that the picture is known, and that what we add is
its exact form at a fixed time.

## 3. Example 4.11, Remark 4.12 and the local big jump

- Example 4.11 now ends with Berger, PTRF 175 (2019) 1-44, Eq. (2.4), as the analogue for sums: under
  regular variation of the tail alone the bound of his Theorem 2.3 cannot be improved, while his
  Theorem 2.4 gives the local asymptotics under the local condition (2.7). The introduction says the
  same in one sentence.
- Remark 4.12 is rewritten around Denisov, Dieker and Shneer, Ann. Probab. 36 (2008) 1946-1991.
  Insensitivity to shifts on the scale of the fluctuations is their condition (Section 1, and
  condition (6) of Corollary 2.1, checked: Corollary 2.1 assumes mean zero, a moment of order kappa in
  (1,2], an almost decreasing local tail with x^kappa F(x+Delta) in Sd or O-regularly varying, and (6)).
  Their Theorem 9.1 (local case) assumes intermediate regular variation of x -> P(x < xi <= x+T). The
  remark keeps the one-line argument that, under (RV), insensitivity at relative width o(1) is
  equivalent to (LR). The sentence "Whether some local condition strictly weaker than (LR) suffices
  is open" is replaced by "We do not prove that (LR) is necessary".
- Remark 4.10 lost the unproved sentence about a left-tail bound exp(-c y^beta) improving lambda_N.
- What is new for the local big jump is now stated in Section 1.3: the count at a fixed time, the run
  in progress at time N, the exact constants gamma(j) and kappa(j), uniformity up to the endpoint.

## 4. Vocabulary

- "slot" 0 left in the TeX (was 97). "preparation" survives only inside the quoted sentence, in
  "initial preparation" when paraphrasing that question, and in the labels `thm:preparation`,
  `sec:preparation`, `sec:prep-*`, `eq:kappa-prep` and the file name `verify_preparation.py`.
- "censored" 0 left in the TeX. The run is "the run in progress at time N". The notation
  `Cen_g` and the term "final run" (defined in Section 2.5 as the run that contains step N) stay.
- Section 5 is now "The initial run", Theorem C is "[the initial run]", and the fresh start is
  "an ordinary run" where it is described in words.
- Printed labels and docstrings of `verify_preparation.py` and `verify_all.py` changed the same way.
  Code comments that say "slot" were left.

## 5. Length

| Item | Change |
|---|---|
| Proposition 7.1 | Remark 5.6 (`thm:inverse`, also `rem:thinning`) at the end of Section 5, with short proofs. `sec_inverse.tex` deleted. The tail of the geometric sum now cites Berger's Theorem 2.1 (fixed k) and Kesten's bound, Embrechts, Kluppelberg and Mikosch Lemma 1.3.5 (the numbering is the one Denisov, Dieker and Shneer use for that bound). |
| Section 6.2 | The proof of Lemma `lem:local-bigjump` (45 lines) is replaced by Denisov, Dieker and Shneer, Theorem 9.1, with the hypotheses of their Proposition 9.1 checked one by one, plus a 4-line induction for fixed r. |
| Section 8 | Now Section 7 "Computations", one page. It keeps `sec:verify`, `eq:run-recursion`, `eq:run-sum`, the rounding bound, the figure errors, the numbers of Remark 4.9 and the stationary ratios, and points to the repository and README for the rest. Table 1 moved to the end of Section 6. Software versions are in README (already there). |
| Appendix A | Proofs tightened, no lemma dropped. |
| Remark 4.12 | Now a citation as above. |
| Intro and Section 5 | The window paragraph, the nested criteria, the antimode paragraph, "The walk", the regularly varying initial runs paragraph and the organization paragraph were condensed. |

Pages: 55 before, 52 now (51 full pages and 17 lines). The target of about 46 is not met. No
lemma of Appendix A could be replaced by a source that states exactly what is used and that I
could read: the normalization constant K_alpha in Lemma A.1(i) and the positivity in Lemma 2.2(d)
would need Feller, Ibragimov-Linnik, Zolotarev or Sato at a page I could not check. Further cuts
of about 5 pages would need content decisions, for instance Corollary `cor:no-trim` (0.8 page), the
verification of Example 4.11 (1 page), or moving long proofs (Theorem C(e), Lemma `lem:spread`) to an
online supplement.

## 6. The composite formula (R1)

Not added. The composite B_N^{-1}h_N + (G_N - tau_N/B_N)1{x >= 1} needs, on x >= K_N, that
h_N(x) - tau(x) = o(B_N G_N(k)) up to x = N/B_N. Since B_N G_N/tau(x) is a ratio of slowly varying
factors at B_N and L_k, this needs a rate in the tail of h_N, uniform in theta, for instance
h_theta(x) - tau(x) = O(x^(-alpha-1-epsilon)). Nothing in F gives that. What F does give is added
instead, after Corollary 4.8: when b_{+,N} = B_N for large N there is K_N -> infinity such that the
bulk profile on |k-pN| <= K_N B_N and G_N beyond it have relative error o(1) in a single limit (Theorem A(c)
by diagonalization, and Theorem B(b), whose double limit is equivalent to the single limit over
every K_N -> infinity). Remark 4.9 and the introduction now say that no fixed switching point works,
instead of "the double limit is forced".

## 7. References added, and how each was checked

| Key | Data | Checked |
|---|---|---|
| `sb2015` | Schulz, Barkai, PRE 91 (2015) 062129, arXiv:1409.4586 | Crossref (DOI 10.1103/PhysRevE.91.062129), full text: abstract, Eqs. (25), (26) |
| `wvbb2019` | Wang, Vezzani, Burioni, Barkai, PRR 1 (2019) 033172, arXiv:1906.04249 | Crossref, full text: abstract, Eqs. (28), (46), (47) |
| `wsdb2018` (arXiv added) | PRE 98 (2018) 042139, arXiv:1809.05856 | Crossref, full text: Section VIII quote, Eqs. (52), (83), Section VII.A |
| `zdk2015` (new use) | RMP 87 (2015) 483-530 | Crossref, full text arXiv:1410.5100: Section II.A.2, Eq. (32), Fig. 2 |
| `berger2019ptrf` (new uses) | PTRF 175 (2019) 1-44, DOI 10.1007/s00440-018-0887-0 | Crossref, full text arXiv:1706.07924: Eq. (2.4), Theorems 2.1, 2.3, 2.4 |
| `dds2008` (new uses) | Ann. Probab. 36 (2008) 1946-1991, DOI 10.1214/07-AOP382 | Crossref, full text arXiv:math/0703265: Section 1, Corollary 2.1 and (6), Proposition 9.1, Lemma 9.1, Theorem 9.1 |
| `vbb2019` (new use) | PRE 100 (2019) 012108 | Crossref, full text arXiv:1804.02932: Eqs. (12), (13) |

No MR numbers were added for the new entries (MathSciNet not checked).

## 8. Build and scripts

- `pdflatex problem131_levy.tex` until stable: 52 pages, no errors, no undefined or multiply defined
  references, no overfull boxes, one underfull vbox during output.
- Python files are LF. `py -I verify_all.py --quick`: 4 of 4 pass. `py -I verify_all.py --full`:
  6 of 6 pass. Changed hashes: `verify_preparation.py` 18a30a8a..., `verify_all.py` (its own output).
  The others are unchanged. Aux files and `__pycache__` removed, PDF kept.

## 9. Labels and edits needed outside the folder

- All labels used outside the folder are kept: `prop:final-run`, `prop:fresh-identity`,
  `prop:first-run`, `lem:green`, `lem:counting`, `eq:kernel-sums`, `eq:kappa`, `eq:rho-rep`,
  `eq:final-explicit`, `eq:run-recursion`, `eq:run-sum`, `eq:means`, `sec:runs`, `sec:kernels`,
  `sec:verify`, `lem:profile`, `thm:inverse`, `rem:thinning`, `tab:antimode`. Paper D has no
  bibliography entry for F.
- `kagey-problems/problem131/lean/PaperF/MAP.md`, lines 5-6: "Proposition `thm:inverse`(a)
  (Section 7, `paperF/sec_inverse.tex`)" should become "Remark `thm:inverse`(a) (Section 5.7,
  `paperF/sec_preparation.tex`)".
- `kagey-problems/problem131/README.md`, line 162: "55 pages" should become "52 pages".
