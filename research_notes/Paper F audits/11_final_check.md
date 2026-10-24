# Paper F audit 11: final pre-submission check

Manuscript: `kagey-problems/problem131/paperF/problem131_levy.tex` and its eight inputs, state of
2026-10-24 after the editing pass. No source file was edited. The PDF was rebuilt twice with
`pdflatex -interaction=nonstopmode problem131_levy.tex` (53 pages). Line numbers are by file.
Scripts: `voice.py` in `scripts/final/` of this folder, and `refs.py` from
`scripts/consistency/`.

Theorem letters as the aux file prints them: A = `thm:bulk`, B = `thm:bigjump`,
C = `thm:preparation`, D = `thm:mode`, E = `thm:antimode`, F = `thm:inverse`, and
`thm:second-order` = Theorem 6.1.

---

## Summary

No high-severity finding. The build is clean, every reference and citation resolves, every part
reference matches the current statements, the abstract and introduction match Theorems A to F
and Theorem 6.1 on every point I was asked to check, the voice rules hold, the front matter
follows the class sample, and no drafting note remains. What is left is two medium wording
points in the abstract and introduction, a few low wording points, and stale notation in the
companion files (README, Lean docstrings, one script docstring).

---

## Findings ranked by severity

### Medium

**M1. The introduction's hypotheses for Theorem B can be read as "all three for the plus sign".**
`sec_intro.tex:83-84`: "under (RV) and (SPAN) and (LR) for the plus sign". Theorem B(b)
(`sec_bigjump.tex:56-57`) assumes (RV) and (SPAN) for both signs and (LR) for the plus sign.
The other statements say this correctly (Theorem C(c), `cor:infinite-density`, Theorem E). Edit E1.

**M2. The abstract drops "equal indices" from the golden ratio statement.**
`problem131_levy.tex:59-60`: "which for the equilibrated start is the golden ratio threshold".
Theorem D(d) (`sec_shape.tex:28-31`) gets the golden ratio only for equal indices. For unequal
indices the threshold is $\alpha_\sigma-1$ against $1/\alpha_*$ (`sec_shape.tex:84-85`). The
introduction says "with equal indices" (`sec_intro.tex:139-140`). Edit E2.

**M3. Stale notation and section numbers in the companion files the paper points to.**
Section 8 sends readers to the repository and to `lean/PaperF/MAP.md`. None of these files is
part of the PDF, but they now disagree with it.
- `paperF/README.md:141`: "Directional defect L_N^sigma". The paper's symbol is
  $\mathcal D^\sigma_N$, with $\Delta_{\sigma,N}$ its supremum (`sec_preparation.tex:9-12`). This is
  a leftover of the old name $L^\sigma_N$. Edit E9.
- `lean/PaperF/Inverse.lean:6`: "Theorem `thm:inverse`(a) of `paperF/problem131_levy.tex`
  (Section 5)". **The section number is stale.** `thm:inverse` is in Section 7 (aux:
  `sec:inverse` = 7, `thm:inverse` = F on p. 48). `MAP.md:6` already says Section 7. The other
  Lean docstrings are correct (`Basic` Section 2, `Kernels` 2.4 and 2.5, `FirstRun`, `Green`,
  `FinalRun`, `Counting` 2.5). Edit E10.
- `lean/PaperF/Green.lean:7-8,10,21,32,158,186` and `MAP.md:95-96` write the count law as
  `K^σ_m(b)`. The paper renamed it $\Pi^\sigma_m(b)$ (`sec_setting.tex:39`, `lem:green` at
  `sec_setting.tex:377`). These are comments, not identifiers, so the fix is textual. Edit E11.
- `verify_preparation.py:17,170,179,193,198` (`K^-_m`), `:22` (`L^+_N`), `:31` ("printed in
  Section 5", the numbers are now in Section 8). The output file
  `data/verify_preparation_output.txt:9` inherits "K^- = F^+" from line 198. README:68-69 warns that
  outputs may print old names, but this script was written after the pass. Edit E12.
- `verify_identities.py:297` comment "A_t, B_t" (paper: $a_t$, $b_t$). Harmless. The Lean
  identifiers `A`, `B`, `A_succ`, `B_succ` keep the capitals, and `MAP.md:57-58` says so
  explicitly, so I would leave them.

### Low

**L1. Introduction: the correction at the end is not "a prepared boundary kernel".**
`sec_intro.tex:127-129`: "When a condition fails the theorem gives the exact correction, as a
directional defect in the bulk, as an additive term in the big-jump zone, and as a prepared
boundary kernel at the end." The condition that governs the end is $\nu_+(n)=o(T_+(n))$, and
when it fails Theorem C(d) adds the term $B_N^{-1}\mathcal D^+_N(j)$ (or
$\nu_+(N)(1+\mu_+u_-(j))$ under (R$\nu$)). The prepared kernel $\kappa_+$ is there whether or not
the condition holds, and it differs from $u_-$ exactly when $\nu_-\ne\pi_-f_-$
(`rem:kappa-prep`). Edit E4 (author's call, since "prepared boundary kernel" can be read loosely
as the whole limit).

**L2. Introduction: the mode comparison omits the margins and the "both signs".**
`sec_intro.tex:137-139`: "An endpoint is the global mode when its atom exceeds $H_N/B_N$ ... and
the bulk wins when it is smaller." Theorem D(b) needs $\liminf B_NQ_\sigma(N)/H_N>1$, and for the
bulk $\limsup<1$ for both signs. Edit E5.

**L3. Abstract: "plus runs" is not defined there.** `problem131_levy.tex:47`. The abstract
speaks of right steps, then of "the plus runs". Edit E3 (optional).

**L4. Abstract: "an atom at each endpoint".** For a fresh start one atom is zero
(`prop:fresh-identity`, $F^+_N(0)=0$). The abstract describes the general preparation, so this is
accurate as a description of the possible pieces. No edit proposed.

**L5. Remark 4.9 writes "(LR)" without a sign.** `sec_bigjump.tex:704-705`. Only the plus sign is
used. `cor:infinite-density` was fixed in the same way. Edit E6.

**L6. Remark 4.10 has a dangling clause before its display.** `sec_bigjump.tex:725-726`: "By (LR),
$\gamma(j)\le(1+\mu_+)N$ and $\kappa\le1$," followed by the display. Edit E7.

**L7. Section 8 lists three deviations without saying which start each belongs to.**
`sec_verify.tex:95-96`. They are the fresh, stationary and RV(0.3) starts in the order of line
91-92 (data: 0.1210 -> 0.0585, 0.0571 -> 0.0279, 0.0133 -> 0.0059). Edit E8.

**L8. Symbols still used twice. These are local reuses and need no action.**
- $\varrho$ is the index in `lem:rv` (`sec_setting.tex:85`) and the ratio $b_{-,N}/b_{+,N}$ in the
  proof of B(b) (`sec_bigjump.tex:597-603`).
- $W_\theta$ (`eq:profile`) against the window averages $W_n$ (`sec_preparation.tex:51`).
- $\rho_\sigma$ (index of $Q_\sigma$, Theorem D(c)) against the weights $\rho^{(\sigma_0)}_i(x)$.
- $\hat L=\lfloor L\rfloor$ in the proofs of Section 4 is local and is a different object from
  $\widehat G_N$.

**L9. Bibliography cosmetics.** `berger2019ptrf` is a published PTRF paper but carries only
`\ARXIV`, with no `\MR` like the other entries. `paperD` is "In preparation". These are optional.

**L10. One package warning.** `problem131_levy.log:395`: hyperref "Option `pagebackref' has
already been used". It comes from the class and needs no action.

---

## (1) The log

After two passes: no `!` errors, no undefined references or citations, no multiply defined
labels, no "Label(s) may have changed", no overfull and no underfull boxes. The only warning is
L10. Output: 53 pages, 643978 bytes.

## (2) References and part references

`refs.py`: no duplicate labels, no undefined `\ref`/`\eqref`, no undefined cite keys, no uncited
bibitems. 31 labels are never referenced (section labels, several equation labels, `rem:wr`,
`rem:kappa-prep`). That is harmless.

I checked every part reference against the current statements.
- `thm:bulk` (a)-(c): the uses of (a) (`sec_bigjump.tex:101`, `sec_preparation.tex:148,251`),
  (b) (`sec_preparation.tex:240,303,503`, `sec_bulk.tex:464`) and (c) (`sec_bigjump.tex:96,696,705,724`,
  `sec_preparation.tex:494,690`, `sec_shape.tex:440`) all match.
- `thm:bigjump` (a)-(c): (a) at `sec_inverse.tex:41,44` and `sec_preparation.tex:313,322,328`;
  (b) at `sec_bigjump.tex:640,674,696,717,721,750,755,810`, `sec_preparation.tex:105`, and
  "the last clause of (b)" (the additive form for $\overline G$) at `sec_preparation.tex:217`;
  (c) is proved at `sec_bigjump.tex:622-636`. All match.
- `cor:bigjump-lower` (4.7) is used at `sec_bigjump.tex:102,739` and `sec_shape.tex:435`. Its
  zone starts at $pN+KB_N$ with no $\lambda_N$, which is exactly what Theorem E's proof needs.
- `thm:preparation` (a)-(d): (a) at `:229,276,280,306`, (b) at `:269` and `sec_shape.tex:46`
  (the interior error under the bulk criterion), (c) at `:138,363,444,623,653`, (d) at
  `:312,614,653` and `sec_inverse.tex:94`. "Part (b) ... holds on every macroscopic interior
  with no condition" (`:666`) matches the last sentence of (b). All match.
- `thm:second-order` (a), (b): (a) at `sec_shape.tex:453` (fixed $j<J$), (b) at `:480` (the
  window $K\Lambda_N\le N^{1-\eta}$). The unlabelled use at `:478` is the closing sentence
  ($C(j)/j\to c_a$), whose minus-sign hypotheses Theorem E assumes. Inside the proof, (a) is
  derived from (b) (`:345-346`). All match.
- `thm:inverse` (a), (b), `thm:mode` (d) (`sec_verify.tex:86`), `cor:stationary` (a), (c)
  (`sec_inverse.tex:114`, `sec_verify.tex:98`), `lem:index` (a), (b), `lem:stable` (i)-(iv) and
  `lem:profile` (a)-(d) all match their statements.

## (3) Abstract and introduction against the statements

| Item | Abstract / introduction | Statement | Verdict |
|---|---|---|---|
| Bulk hypotheses, conclusion | (RV)+(SPAN), whole-row sup, $C/B_N$ (intro 70-79) | A(a),(b) | match |
| Profile | density of $(1-p)\theta_{+,N}Z_+-p\theta_{-,N}Z_-$ (intro 76) | `eq:profile` | match |
| $B_N$ growth | $N^{1/\alpha_*}$ up to a slowly varying factor (intro 25-26) | `lem:rv`(v) | match |
| Big-jump hypotheses | "(RV) and (SPAN) and (LR) for the plus sign" (intro 83-84) | B(b): (RV),(SPAN) both signs, (LR) plus | ambiguous, M1 |
| Zone with $\lambda_N$ | $pN+K\lambda_NB_N\le k\le N$, $N\to\infty$ then $K\to\infty$; $\lambda_N=1+\log(B_N/b_{+,N})$ (intro 88-92) | B(b), `eq:lambdaN` | match |
| Kernel coefficient | $\gamma(N-k)f_+(\lfloor L_k\rfloor)+T_+(\lfloor L_k\rfloor)u_-(N-k)$, $\gamma(j)\sim js/\mu_-^2$ (intro 86-90) | `eq:G` with $\kappa^{(+)}_+=u_-$ (`eq:kappa`), `eq:gamma-asymp` | match |
| Boundary layer | $P_N(N-j)/T_+(N)\to u_-(j)$ under (RV) plus (intro 93-95) | B(a) | match |
| Window with only a lower bound | bulk estimate and $P_N\ge(1-o(1))G_N$ on $KB_N\le k-pN\le K\lambda_NB_N$, with a conjecture (intro 99-103, abstract 46-47) | `sec_bigjump.tex:98-104`, `cor:bigjump-lower` | match |
| No single formula | neither profile nor kernel nor sum (intro 97-99, abstract 54-55) | `rem:no-single-formula` | match |
| (LR) sentence | (LR) suffices, (RV) alone does not, sharp condition open (intro 103-106, abstract 65-66) | `ex:rv-not-lr`, `rem:wr` | match |
| Infinite density | formula (intro 107-113) | `cor:infinite-density` | match |
| Preparation criteria | bulk $B_n(\nu_++\nu_-)\to0$, end $\nu_+=o(T_+)$, window condition sharp under (LR) both signs, nested plus-end chain (intro 115-126) | C(b),(c),(d) and the nesting paragraph | match |
| Correction form | "prepared boundary kernel at the end" (intro 127-129) | C(d): additive defect term | loose, L1 |
| Stationary start | satisfies the bulk criterion, fails the other two (intro 129-132) | `cor:stationary` | match |
| Mode | atom against $H_N/B_N$, bulk criterion stated (intro 136-139) | D(b) | margins omitted, L2 |
| Golden ratio | equal indices, $\varphi$, $1/\mathcal C(\varphi)=1.288\ldots$, `eq:Calpha` cited (intro 139-143) | D(d) | match |
| Golden ratio in abstract | "for the equilibrated start" (abstract 59-60) | D(d) needs equal indices | M2 |
| Antimode condition | $u_-(j)>1/\mu_-$ for all $j\ge1$, holds for strictly log-convex laws (intro 146-148, abstract 61-62) | E(a), `lem:logconvex` | match |
| Antimode law | $T_-(j^*_N)\sim2\alpha_+s/N$, $j^*_N$ asymptotic to the minimizer of $u_-+C/N$, bounded otherwise (intro 148-156) | E(a),(b) | match |
| Second-order coefficient | "exact second-order coefficient of Theorem 6.1" (intro 154-155, abstract 63) | `thm:second-order`, `eq:Cj` | match |
| Identification | $P_N(N-j)/P_N(N)\to u_-(j)$, minus end normalized by $T_-$, thinning (intro 161-167) | F(a), `rem:thinning` | match |
| Caption | pieces of A and B, law of E, $C(j)$ from 6.1 (intro 47-54) | `figures/captions.md` short form | match |

## (4) Notation

Leftover search over all `.tex` files:
- No occurrence of $A_t$, $B_t$ (now $a_t$, $b_t$ in `sec_verify.tex:9-21`), `\hat G` (all are
  `\widehat G_N`, defined once at `eq:Ghat`), $L^\sigma_N$ (now $\mathcal D^\sigma_N$), $K^\sigma_m$
  (now $\Pi^\sigma_m$), `lem:final-explicit`, `prop:uniform-second`, `rem:rho-diagram`,
  `lem:no-big-run`, `lem:two-big-runs` or `lem:one-big-run` (now `lem:no-giant`, `lem:two-giant`,
  `lem:one-giant`). Also absent: `eq:AB-recursion`, `lem:unif-bigjump`, `lem:end-crude`,
  `rem:inverse-scope`.
- `tab:antimode` is defined and referenced only in `sec_verify.tex` (4, 46, 72, 77).
- The old names survive only outside the manuscript (M3) and in the README's list of removed
  labels (`README.md:65-68`), where they belong.
- The renames in `figures/numbers_for_verify.md` are all applied. Section 8 states
  `eq:run-recursion` and `eq:run-sum` with $a_t$, $b_t$ as that file suggests, and it holds the
  table with the label `tab:antimode`.

## (5) Citations

Every `\cite` key exists, and every one of the 44 bibitems is cited at least once (counts in
`refs.py`). The five uncited entries flagged in audit 08 are gone.

## (6) Voice

Scanning the prose outside math, labels, cites, URLs and the bibliography found no semicolons, no
colons, no em-dashes (`---` appears only in source comments of the preamble), no Unicode dashes,
and no "clearly", "obviously" or "evidently". Every sentence of the abstract has a verb. The
run-in labels of Section 8 and of the introduction's bullets ("The bulk.", "The exact law.") are
headings, not sentences.

## (7) Front matter against the class sample

Checked against `texmf-dist/doc/latex/ejpecp/sample.tex` and `ejpecp.cls`:
- `\documentclass[EJP,preprint]{ejpecp}` is correct.
- `\TITLE`, `\SHORTTITLE`, `\AUTHORS` (with a footnote affiliation and `\BEMAIL`), `\KEYWORDS`
  and `\AMSSUBJ` are present and separated by semicolons. `\AMSSUBJSECONDARY` prints as
  "Primary ..., Secondary ...".
- `\SUBMITTED{}` and `\ACCEPTED{}` are empty. With `preprint` the class does not print them, so
  they are fine for a submission.
- `\ABSTRACT` is present. There is no `\maketitle`, as the class wants. `acks` is used with
  the optional title.
- `\VOLUME`, `\YEAR`, `\PAPERNUM` and `\DOI` are left to the managing editor, as the sample says.
- The theorem environments use the class style `ejpecpbodyit`.

## (8) Drafting notes, README and the Lean docstring

- No `\proofpending`, `\todo`, `\textcolor`, `\marginpar`, "TODO", "FIXME" or "??" in the sources,
  and none in the PDF text.
- README statement numbers against the aux file: `prop:final-run` = Proposition 2.6,
  `thm:second-order` = Theorem 6.1, `cor:stationary` = Corollary 5.4, `tab:antimode` = Table 1,
  sections 2 to 8 as listed, letters A to F as listed, 53 pages. All match.
- `lean/PaperF/Inverse.lean` lines 1-10: the docstring places `thm:inverse` in "Section 5".
  **That is stale.** It is Section 7 (M3, E10).

Numbers in Section 8 that I checked against `data/`:
- the margins 2.6e-4, 2.3e-4, 1.7e-5, 3.1e-5, 1.1e-5 and the threshold $2\varepsilon/(1-\varepsilon)\le1.42\cdot10^{-8}<1.5\cdot10^{-8}$ (`antimode.json`, `certify_antimode.py:92`);
- the bounds $\varepsilon_{600}=4.0\cdot10^{-11}$ and $\varepsilon_{5000}=2.8\cdot10^{-9}$, and the ball deviation 5.9e-15;
- the second-renewal ratios 0.978, 0.995 (data 0.9945, recomputed 0.99452 in audit 08), 0.999;
- the distances 0.090 -> 0.022 and 0.592 -> 0.135;
- the preparation deviations and the stationary ratios;
- the big-jump ratios ("about 8 percent", data 7.9% and 8.3%);
- the 7 Lean modules, and the 14 Lean names quoted, which all exist as theorems.

---

## Exact edits

**E1** `sec_intro.tex:84`
old: `(SPAN) and (LR) for the plus sign,`
new: `(SPAN) for both signs and (LR) for the plus sign,`

**E2** `problem131_levy.tex:60`
old: `height, which for the equilibrated start is the golden ratio threshold. For a`
new: `height, which for the equilibrated start with equal indices is the golden ratio threshold. For a`

**E3** (optional) `problem131_levy.tex:47`
old: `only in part when the plus runs have the smaller fluctuation scale. The law has`
new: `only in part when the runs of right steps have the smaller fluctuation scale. The law has`

**E4** (author's call) `sec_intro.tex:128-129`
old: `defect in the bulk, as an additive term in the big-jump zone, and as a`
`prepared boundary kernel at the end. The stationary preparation, which is`
new: `defect in the bulk and as an additive term in the big-jump zone and at the`
`end. The stationary preparation, which is`

**E5** `sec_intro.tex:138-139`
old: `the global mode when its atom exceeds $H_N/B_N$, with $H_N$ the height of the`
`profile, and the bulk wins when it is smaller. For the stationary preparation`
new: `the global mode when its atom exceeds $H_N/B_N$ by a fixed factor, with $H_N$ the height of the`
`profile, and the bulk wins when both atoms are smaller by a fixed factor. For the stationary preparation`

**E6** `sec_bigjump.tex:705`
old: `(LR), and let $k=\lceil pN+KB_N\rceil$ with $K$ fixed. By Theorem~\ref{thm:bulk}(c),`
new: `(LR) for the plus sign, and let $k=\lceil pN+KB_N\rceil$ with $K$ fixed. By Theorem~\ref{thm:bulk}(c),`

**E7** `sec_bigjump.tex:725-726`
old: `and Lemma~\ref{lem:profile}(d), $B_NP_N(k)$ is bounded below. By (LR),`
`$\gamma(j)\le(1+\mu_\plus)N$ and $\kappa\le1$,`
new: `and Lemma~\ref{lem:profile}(d), $B_NP_N(k)$ is bounded below. By (LR) and the bounds`
`$\gamma(j)\le(1+\mu_\plus)N$ and $\kappa\le1$,`

**E8** `sec_verify.tex:96`
old: `$N=1200$ to $0.059$, $0.028$ and $0.006$ at $N=2400$. For the stationary start`
new: `$N=1200$ to $0.059$, $0.028$ and $0.006$ at $N=2400$, for the three starts in this order. For the stationary start`

**E9** `paperF/README.md:141`
old: `kappa_+^{(sigma_0)}. Big-jump kernel G_N. Directional defect L_N^sigma.`
new: `kappa_+^{(sigma_0)}. Big-jump kernel G_N. Directional defect D_N^sigma (\mathcal D^\sigma_N), with supremum Delta_{sigma,N}.`

**E10** `lean/PaperF/Inverse.lean:6`
old: ``The algebraic part of Theorem `thm:inverse`(a) of `paperF/problem131_levy.tex` (Section 5):``
new: ``The algebraic part of Theorem `thm:inverse`(a) of `paperF/problem131_levy.tex` (Section 7):``

**E11** `lean/PaperF/Green.lean` lines 7, 8, 10, 21, 32, 158, 186, and `lean/PaperF/MAP.md:95-96`:
in comments and docstrings only, replace `K^σ_m`, `K^+_m` and `K^-_m` by `Π^σ_m`, `Π^+_m` and
`Π^-_m`. Leave the Lean identifiers unchanged. Rebuilding is not needed for comment changes, but
`lake build PaperF` confirms nothing else moved.

**E12** `paperF/verify_preparation.py`
- line 17: `The kernels K^-_m(b)` -> `The kernels Pi^-_m(b)`
- line 22: `B_N^-1 L^+_N(j)` -> `B_N^-1 D^+_N(j)`
- line 31: `printed in Section 5` -> `printed in Section 8`
- lines 170, 179, 193, 198: `K^-` -> `Pi^-` in the strings and comments.

Then rerun `py -I verify_all.py` so that `data/verify_preparation_output.txt` carries the new
names and the new sha256.

---

## Verdict

**Ready for a last author read.** The build is clean, the cross-references, part references
and citations are all correct after the renumbering, the abstract and introduction state the
theorems as they now stand (including the window with only a lower bound, the kernel
coefficient, the antimode condition, the identification normalization and the (LR) sentence),
and no drafting material is left. Two edits should go in before submission, both one line each:
E1 (the Theorem B hypotheses in the introduction) and E2 ("with equal indices" in the abstract).
E10 should go in before the repository link is made public. The rest are optional polish (E3 to E8)
or repository hygiene (E9, E11, E12), and none of them affects a statement or a proof.
