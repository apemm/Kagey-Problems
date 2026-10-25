# Paper F, second editorial check before the second round (October 24, 2026)

Read in order: `12_external_referee_report.md`, `13_revision_after_referee.md`, then the whole
paper (`problem131_levy.tex`, the eight section files and `sec_appendix.tex`), the README, the
caption sources and the script docstrings. The class documentation was read from the TeX Live
tree (`ejpecp.cls`, `doc/latex/ejpecp/sample.tex`).

## Decision

Ready for the referee. Five small edits were made (listed below). No substantive problem was
found. The open points below are minor and none changes a statement or a proof.

## Referee items

| Item | Status | Note |
|---|---|---|
| 1. Window conjecture | Verified | Dropped. The replacement (`sec_bigjump.tex` after Theorem B, intro Results) says that on $KB_N\le k-pN\le K\lambda_NB_N$ only Theorem A(a) and the lower bound of Cor. 4.7 are proved and $P_N$ is not described. True. Cor. 4.7 uses only $L_k\ge KB_N$ (Lemma 4.6 and the two-giant bound), as its proof says. Consistent with Theorem B (zone starts at $K\lambda_NB_N$) and with Rem. 4.9 ($P_N/G_N=r_N(K)+o(1)$, $r_N\to1$ in the double limit). Side stated correctly. |
| 2. Censored run | Verified | Both places say the censored run adds $+\ell^{-\alpha}$ and moves $-\alpha$ to $-(\alpha-1)$. |
| 3. Redundant hypothesis, Prop. 7.1(b) | Verified | Now derived: $\nu_+=q f_++o(T_+)=o(T_+)$. Correct. |
| 4. Converse in C(d) | Verified | $m_0(j)$ from the Green identity, independent of $N$. $\Pi^-_j(j)=T_-(j)$ is right. |
| 5. `eq:lambda-unif` | Verified | Upper bound $\lambda_n\le\lambda_N+o(1)$ through the UCT for $r(n)$, both signs of $\varrho$. Correct. |
| 6. Local slips | Verified | $q_m$ restricted to $r<k$. Rem. 4.9 rewritten with $r_N(K)$, values 0.31 and 1.68 match `verify_bigjump.py`. Section 4 opening corrected. |
| Exposition: Theorem A foregrounded, appendix | Verified | "What is new" paragraph after Theorem A. Moved to Appendix A: proofs of Lemmas 2.1 and 2.2, Lemma A.1 (`lem:stable`), (K1) to (K4), Lemma A.2 (`lem:kernels`), Lemma A.3 (`lem:small`). Every moved item is cited where used (Lemma 3.1, proof of Theorem A, Section 4, Example 4.11). All references resolve. |
| Exposition: split of C(c) | Verified | New C(e) with `eq:interior-target`. The reduction (Z^ε inside the zone of (c) for every K, so the double limit becomes a plain limit), sufficiency of $\nu_+=o(T_+)$ through `eq:Psi-upper`, necessity of $W_n=o(T_+(n))$ (at $N=2n$, $k\in Z^{1/4}_N$, A(c) lower bound) and sufficiency under (LR) for both signs (blocks of width $B_N$, `eq:far-bound`) each prove what the target states. Checked line by line. |
| Exposition: constants | Verified | Rule in Section 2.2. Capital indices 1 to 10 and lower indices 1 to 12 each introduced once (C_1, C_2 Lemma 2.2; C_3 Lemma A.2; C_4, C_5 Lemma A.3; C_6, C_7 proof of A; C_8 Lemma 4.3; C_9 `eq:far-bound`; C_10 proof of C(a); c_1 to c_4 proof of A; c_5, c_6 Lemma 4.3; c_7 Lemma 4.5; c_8 proof of B; c_9, c_10 Lemma 5.3; c_11, c_12 proof of C(e)). None dangling. |
| Exposition: abstract | Verified | 210 words. Names Theorems A and B, says (RV) alone does not suffice for B, states the window by side. |
| Claim: side of window | Verified | Abstract, Section 1.2, Section 4. |
| Claim: "invisible in the bulk" | Verified | Gone. Introduction now matches C(b). |
| Claim: Theorem F demoted | Verified | Proposition 7.1, plus law from the atoms stated first, thinning remark kept. |
| Claim: (LR) sharpness | Verified | Introduction and Rem. 4.12 say the same thing. |
| Claim: Berger PTRF Thm 2.4 | Verified | Two sentences in Section 1.3, correct reasons (random number of runs, censored final run, uniformity to the endpoint). External theorem not re-read. |
| Claim: Takács, Kesten | Verified | Cited where the integral limit theorems are mentioned. |
| Claim: wsdb2018, akimoto2023 | Verified | One sentence each. |

Search for leftovers of the demotion ("six", "Theorem F", "six lettered", "A to F") over all
files in `paperF`, including the README, `figures/captions.md`, `figures/numbers_for_verify.md`,
the scripts and `data/`: no leftover. The two hits of "six" are the six kernels in the proof of
Theorem A and the six values of $j$ in `verify_preparation.py`, both correct.

## Edits made

1. `sec_intro.tex` line 275: "The introduction states five theorems" changed to "The main results
   are five theorems". The lettered theorems are stated in Sections 3 to 6, not in the
   introduction.
2. `README.md` lines 28 and 138: the same correction ("main results are five theorems", "The
   five main theorems are lettered A to E").
3. `sec_inverse.tex` lines 7 and 8: "shows why the minus end cannot replace it" (where "it" was the
   plus-end layer) changed to "shows why the ratios at the minus end cannot replace the atoms",
   which is what Remark 7.2 shows.
4. `sec_bigjump.tex` line 132: "Section~\ref{sec:bulk-kernels}" changed to
   "Appendix~\ref{sec:bulk-kernels}", as elsewhere for appendix references.
5. `problem131_levy.tex`: the `acks` environment moved after `thebibliography`, the position the
   class sample prescribes.

No script was changed.

## Open points, not fixed

1. The window is a genuine gap only when $\lambda_N$ is unbounded. When $\theta_{+,N}$ stays
   bounded below, $K\lambda_NB_N\le K'B_N$ and Theorem A(c) gives relative error $o(1)$ on the
   whole window for each fixed $K$. The phrases "when the scales differ" (abstract, Section 1.2)
   and "when the plus scale is the smaller one" (Section 1.2) are therefore slightly broader than
   needed. A sharper wording would be "when the plus scale is smaller by an unbounded factor".
   Not edited, since it touches the abstract and the claimed scope.
2. In Lemma 5.3 the letter $c$ is used for $j/(1-p)$, and Section 5.2 opens with "Fix
   $c\in(0,1)$". Both clash with the convention of Section 2.2 that unindexed $c$ is a constant
   depending only on the laws. Renaming is safe but touches a proof, so it is left to the author.
3. The statement of Lemma 3.1 uses notions defined only in Appendix A ("kernel of sign $\sigma$",
   $c_{\mathsf k}$, $C_-(\sigma)$, $J_\sigma$). The paragraph before Section 3.1 points there, but a
   referee may want a forward reference in the statement itself.
4. Bibliography: `takacs1957` carries no MR number, and `berger2019ptrf` (PTRF 175) carries only
   the arXiv identifier. Both should get an MR number once checked.
5. Appendix A and Theorem A share the letter A ("Lemma A.1" next to "Theorem A"). Cosmetic.
6. Outside `paperF` (already noted in the revision record): `lean/PaperF/MAP.md` line 5 and
   `lean/PaperF/Inverse.lean` line 6 still say "Theorem `thm:inverse`".
7. EJP format otherwise as the sample prescribes: `\documentclass[EJP,preprint]{ejpecp}` (the
   preprint option suppresses the submitted and accepted line, so the empty `\SUBMITTED{}` and
   `\ACCEPTED{}` do no harm), `\TITLE`, `\SHORTTITLE`, `\AUTHORS` with `\BEMAIL`, `\KEYWORDS` and
   `\AMSSUBJ`/`\AMSSUBJSECONDARY` separated by semicolons with valid MSC2020 classes,
   `\ABSTRACT`, `thebibliography` sorted alphabetically with `\MR` and `\ARXIV`. The optional
   argument `[Acknowledgments]` of `acks` repeats the class default and is harmless.

## Build and scripts

Three passes of `pdflatex` in `paperF`: no undefined references, no multiply defined labels, no
overfull boxes, 2 underfull vbox warnings during output (not boxes in the text). 55 pages. One
build was interrupted because the PDF was briefly locked by another process, and the three
passes were then repeated. Auxiliary files removed, PDF kept.

`py -I verify_all.py`: all 4 scripts pass (identities, coefficient, preparation, bigjump),
0.3 min. The run refreshed the outputs in `data/` as the README describes.
