# Paper F, revision after the referee report of October 24, 2026

This note records the revision that answers `12_external_referee_report.md`. The paper is
`kagey-problems/problem131/paperF/problem131_levy.tex`. Build: three passes of `pdflatex`, no
undefined references, no multiply defined labels, no overfull boxes, 55 pages (53 before). Checks:
`py -I verify_all.py` passes all 4 scripts.

The five lettered theorems are now A (`thm:bulk`), B (`thm:bigjump`), C (`thm:preparation`),
D (`thm:mode`) and E (`thm:antimode`). The identification from the ends is Proposition 7.1, and it
keeps the label `thm:inverse` because the scripts, the outputs and the Lean files name statements
by label.

## Changes

| Item | What changed | File and label |
|---|---|---|
| 1. Window conjecture | Dropped. The bulk profile alone is the natural candidate, since $B_NG_N$ is the leading heavy tail of $h_N$ when $\theta_{+,N}=1$. When $\theta_{+,N}\to0$, however, matching the two at the top of the window needs $T_+(L)/T_+(b_{+,N})\approx(L/b_{+,N})^{-\alpha_+}$ with $L/b_{+,N}\to\infty$, which fails by a slowly varying factor in general. So neither the profile, nor $G_N$, nor their sum can honestly be conjectured. One sentence now says that the window is not described, and it says on which side the window lies. | `sec_bigjump.tex`, paragraph after the remark on $\gamma$ (before `sec:giant`) |
| 2. Side of the window | The abstract and Section 1.2 now say that the window lies on the side of the runs with the smaller scale, and that it is the mirror window at the minus end when the minus scale is smaller. The same is said in Section 4. | `problem131_levy.tex` abstract; `sec_intro.tex` `sec:intro-results`; `sec_bigjump.tex` |
| 3. Bulk criterion | The introduction now says that the interior needs no condition and that $B_n(\nu_++\nu_-)\to0$ is the criterion for uniformity over $1\le k<N$, named the bulk criterion there. | `sec_intro.tex`, Preparation paragraph |
| 4. Theorem F | Demoted to Proposition 7.1. The statement now says first that $P_N(N)=T_+(N)$ gives the plus law from the atoms. The minus law comes from the plus-end layer, and the thinning remark is kept as the informative point, with the atoms added as a separator. The redundant hypothesis $\nu_+(n)=o(T_+(n))$ in (b) is removed and derived in the proof from $Q_+(N)/T_+(N)\to q$ and (RV). The overview now counts five theorems A to E plus Proposition 7.1. The README status, the theorem list and the label section are updated. No script, docstring, figure caption or output prints "Theorem F", so none needed a change. | `sec_inverse.tex` `thm:inverse`, `rem:thinning`; `sec_intro.tex` `sec:intro-organization`, Identification paragraph; `sec_verify.tex` (three references); `README.md` |
| 5. New content of Theorem A | Section 3 now opens, after the statement, with a paragraph on what is new: (c) on a fixed window also follows from Berger's Theorem 3.3, and (a) and (b) give the uniform error and the bound $C/B_N$ over the whole row under (RV) and (SPAN) alone. It also says why this needs work: the remote bins come from local large deviations of one factor, Berger's off-direction bounds need a local condition, and the scales may oscillate. The classical inputs (`lem:stable`) and the kernel facts ((K1) to (K4), `lem:kernels`, `lem:small`), with their proofs, and the proofs of `lem:rv` and `lem:profile` moved to a new Appendix A. Section 3 keeps `lem:index` and the proof. | `sec_bulk.tex` (new `sec:bulk-index`); new `sec_appendix.tex` (`app:classical`, `app:rv`, `sec:bulk-inputs`, `sec:bulk-kernels`); `sec_setting.tex` |
| 6. Abstract | 323 words cut to about 200. It names Theorems A and B and says that (RV) alone does not suffice for B. | `problem131_levy.tex` |
| 7a. Censored run | Both places now say that the complete run gives the linear coefficient $-\alpha$ and the censored run adds $+\ell^{-\alpha}$, which changes it to $-(\alpha-1)$. | `sec_bigjump.tex` after `cor:infinite-density`; `sec_intro.tex` `sec:intro-related` |
| 7b. Converse in C(d) | The converse no longer uses $T_-(j)>0$. The Green identity gives an $m_0(j)$ with $\Pi^-_{m_0}(j)>0$, independent of $N$, and the term $m=m_0$ of the defect gives the bound. The case $T_-(j)>0$ with $m_0=j$ is noted. | `sec_preparation.tex`, proof of `thm:preparation`(d) |
| 7c. `eq:lambda-unif` | The justification is replaced. With $r(n)=b_{-,n}/b_{+,n}$ of index $\varrho$, the uniform convergence theorem gives $r(n)\le r(N)(1+o(1))$ on $[cN,N]$ when $\varrho\ge0$, and $\lambda_n=\lambda_N=1$ eventually when $\varrho<0$. So $\lambda_n\le\lambda_N+o(1)$, an upper bound only, which gives $\lambda_n\le2\lambda_N$. | `sec_preparation.tex` `sec:prep-tools` |
| 7d. Fixed $K$ in `rem:no-single-formula` | Rewritten with $r_N(K)=h_N(K)/(\alpha_+(1-p)^{\alpha_+}K^{-\alpha_+-1})$. $P_N/G_N=r_N(K)+o(1)$, the sum ratio is $r_N/(1+r_N)+o(1)$, bounded below one. $r_N(K)$ need not converge when $\theta_{-,N}$ oscillates and may equal one at isolated $K$ (between 1 and 4 in the zeta example, where it moves from 0.31 to 1.68). $r_N(K)\to1$ in the double limit by Theorems A(c) and B(b). | `sec_bigjump.tex` `rem:no-single-formula` |
| 7e. $q_m$ | Defined as the sum over $r<k$ with $q_m(k)=0$ for $k\le0$, with a sentence on why the restriction matters. | `sec_setting.tex` `sec:kernels` |
| 7f. Opening of Section 4 | Now says that bins are smaller than $1/B_N$ by a power of $N$ only on the ballistic range, and only by a factor of order $K^{-\alpha_+-1}$ near $KB_N$. | `sec_bigjump.tex`, first paragraph |
| 8. Positioning | Two sentences on why Berger's PTRF Theorem 2.4 does not give Theorem B (a random number of runs tied to the lengths, the censored final run, uniformity to the endpoint). Takács (1957, 1959) and Kesten (1962) are cited for the integral limit theorems. One sentence each places wsdb2018 (continuous time, double Laplace transform, one law, fair random start, preparation left open in their Section VIII) and akimoto2023 (moments for the ordinary and equilibrium starts) against Theorem B(a), (c) and Theorem C. The "open" statement in the introduction now matches `rem:wr`: (RV) alone does not suffice, and whether a local condition strictly weaker than (LR) suffices is open. | `sec_intro.tex` `sec:intro-related` and Results; `sec_bigjump.tex` `rem:wr`; bibliography |
| 9a. Split of C(c) | C(c) is now the full zone (decomposition, removal of $\Psi_N$ iff $\nu_+=o(T_+)$, the regular case). A new part C(e) is the interior zones $Z^\varepsilon_N$ with the explicit target `eq:interior-target`, the sufficiency of $\nu_+=o(T_+)$, the necessity of $W_n=o(T_+(n))$, and its sufficiency under (LR) for both signs. It is (e) rather than a new (d) so that the scripts' references to (c) and (d) stay right. The proof is split, with a reduction step. | `sec_preparation.tex` `thm:preparation`(e), `eq:interior-target`, proof of (e) |
| 9b. Constants | Section 2.2 now states the rule: numbered constants are fixed where introduced, keep their value to the end, and no index is used twice. Parameter-indexed constants are local. Renumbered: bulk proof $c_0,c_1,c_2,c_8\to c_1,c_2,c_3,c_4$. `lem:no-giant` $C_0\to C_8$, $c_3,c_4\to c_5,c_6$. `lem:spread` $c_5\to c_7$. Theorem B proof $c_6\to c_8$. `lem:green-conc` $c_0,c_1\to c_9,c_{10}$. Theorem C(a), (b) $C_0\to C_{10}$. Far bound `eq:far-bound` threshold $C_0\to C_9\ge C_8$. Proof of C(e) $c_2,c_3\to c_{11},c_{12}$. | `sec_setting.tex`, `sec_bulk.tex`, `sec_bigjump.tex`, `sec_preparation.tex` |
| 10. paperD entry | Left as "In preparation, 2026". | bibliography |

## New bibliography entries and sources

- Takács, L., On limiting distributions concerning a sojourn time problem, Acta Math. Acad. Sci.
  Hungar. 8 (1957), no. 3-4, 279-294. Checked against the Crossref record of DOI
  10.1007/BF02020316. No MR number was verified, so none is printed.
- Takács, L., On a sojourn time problem in the theory of stochastic processes, Trans. Amer. Math.
  Soc. 93 (1959), no. 3, 531-540. Checked against the Crossref record of DOI
  10.1090/S0002-9947-1959-0109362-7. The MR number 0109362 is the one in the AMS DOI.
- Kesten, H., Occupation times for Markov and semi-Markov chains, Trans. Amer. Math. Soc. 103
  (1962), no. 1, 82-112. Checked against the Crossref record of DOI
  10.1090/S0002-9947-1962-0138122-6. MR 0138122 as in the DOI.

The prior-art note also lists a second 1957 Acta paper of Takács (8, 169-191). The paper cites
only the limiting-distributions paper. The full texts of the Takács papers were not read, so the
paper credits them only with integral (distributional) limit theorems, as Kesten's own
description supports.

## Declined or partial

- Item 1: no conjecture is stated, for the reason in the table. The referee's question 2 is
  answered in the paper by the sentence that the window is not described.
- Item 4: the label `thm:inverse` is kept, although the statement is now a proposition, so that
  the scripts, the outputs and the Lean files stay correct.
- Page count: 55 pages against 53. The extra length is the new opening of Section 3, the
  constants rule, the split of C(c), the rewritten remark and the positioning sentences. Some
  repetition was cut to compensate (the second account of the physics prior work after
  `cor:infinite-density`, and parts of the related-work paragraph on Berger).

## Edits needed outside paperF (not made)

- `kagey-problems/problem131/lean/PaperF/MAP.md`, line 5: "the algebraic part of Theorem
  `thm:inverse`(a)" should read "the algebraic part of Proposition `thm:inverse`(a)
  (Proposition 7.1)". The rows at lines 102-103 and 124-125 name the label only and can stay.
  The MAP does not use the words "Theorem F".
- `kagey-problems/problem131/lean/PaperF/Inverse.lean`, line 6: the docstring "Theorem
  `thm:inverse`(a)" should read "Proposition `thm:inverse`(a)".

## Scripts and outputs

No script changed in content. The working copies of the paperF scripts had CRLF line endings
from the checkout, while the repository holds them with LF. Their sha256 then differed from the
hashes in `data/`, and check 8 of `verify_coefficient.py` (which compares the hash of
`certify_atlas.py` with the one stored in `data/atlas_N5000.json`) failed. The line endings were
normalized back to LF, which is the committed content, and the hashes now match the recorded ones.
`verify_all.py` was then rerun, and it refreshed `data/verify_all_output.txt` and the four
`verify_*_output.txt` files and `data/preparation_ratios.json`. The output of `verify_bigjump.py`
now carries the hash of the committed script (`e9ff661d...`). The earlier output carried the hash
of the CRLF copy (`4511aa86...`). Neither `sec_verify.tex` nor the README quotes a script hash. The
`--full` run, which rewrites the certificates, was not repeated, since no certified number changed.
