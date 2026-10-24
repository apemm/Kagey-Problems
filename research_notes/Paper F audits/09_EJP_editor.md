# Paper F: handling editor's assessment for the Electronic Journal of Probability

Manuscript: "Bulk, big jumps and boundary layers in the occupation law of a lattice Lévy walk", A. Pemmasani.
Source: `kagey-problems/problem131/paperF/problem131_levy.tex` and the section files `sec_intro`, `sec_setting`, `sec_bulk`, `sec_bigjump`, `sec_preparation`, `sec_shape`, `sec_inverse`, `sec_verify`. PDF `problem131_levy.pdf`, 62 pages. The log of the existing build (dated after the last source edit) is clean: no undefined references, no overfull boxes, one harmless hyperref option warning.
Date: 24 October 2026. No file other than this report was written.

What the requirements were checked against:

- the class file itself, `C:/texlive/2026/texmf-dist/tex/latex/ejpecp/ejpecp.cls` (v1.11.3, 2021/11/04), with its `sample.tex` and `README.md`;
- the survey `research_notes/Paper F prior art/02_EJP_conventions.md`.

The imstat.org author-instructions page returned a bot-protection page when fetched, and web.archive.org could not be reached. Requirements that come only from the journal's web pages therefore rest on the survey and are marked as such below. Everything about the class was verified in the class source.

Page map, from the `.aux` file:

| Pages | Content |
|---|---|
| 1–4 | Introduction |
| 5–12 | Setting and exact identities |
| 13–22 | Bulk (Theorem A) |
| 23–34 | Big jumps (Theorem B) |
| 35–46 | Preparation (Theorem C) |
| 47–56 | Shape (Theorems D and E) |
| 57–58 | Identification (Theorem F) |
| 59 | Verification (placeholder) |
| 59–62 | References (48 entries) |

---

## Part 1. Desk check against the journal's requirements and the template

### 1.1 Item by item

**Class and options.** `\documentclass[EJP,preprint]{ejpecp}` (main file, line 1). Correct: both are declared options of the class (`EJP` at cls l.34, `preprint` at cls l.69). `preprint` removes the logo, volume and footer links, which is what a submission should look like. OK.

**Front matter macros.**

- `\TITLE` (l.37) and `\SHORTTITLE` (l.38) are present. The running title, "The occupation law of a lattice Lévy walk", fits the header. OK.
- `\AUTHORS` (l.39–40) has the affiliation in a footnote with `\EMAIL`, as in the sample. The `\\` before `\EMAIL` (l.39) is a manual line break. The class provides `\BEMAIL` for exactly this (cls l.156, sample l.76). Minor.
- `\KEYWORDS` (l.41–42): nine items separated by semicolons. The sample writes ` ; ` with spaces, but only the semicolon matters. OK. "mode" on its own is too vague to be a useful keyword. Suggest "global mode" or "antimode".
- `\AMSSUBJ` (l.43): `60G50; 60K05; 60F05; 60G52; 60K15; 82C41`. These are valid MSC2020 codes, separated by semicolons, and the class prints them under the heading "MSC2020 subject classifications". The class also offers `\AMSSUBJSECONDARY` (cls l.137), which prints "Primary …, Secondary …". Six codes in one undifferentiated list is unusual. Suggested split:
  - primary: 60K05; 60G50; 60F05;
  - secondary: 60G52; 60K15; 82C41, and perhaps 60F10 for the local large deviations.
- `\ABSTRACT` (l.44–62) is present. See 1.2.
- `\SUBMITTED` and `\ACCEPTED` are **absent**. With `preprint` the class does not print them (cls l.310–316), so nothing visible breaks. But the template has them (sample l.99–100) and the class default is the string `FIXME!` (cls l.127–128). The production editor will fill them, and the source should carry placeholders. Required (trivial).
- No `\maketitle`. Correct (sample l.160).

**acks environment.** `\begin{acks}[Acknowledgments] … \end{acks}` (l.75–78). The environment exists (cls l.154), and the optional argument repeats the default `\acknowledgementsname`, so it can be dropped. It sits before the references while the sample puts it after them. Either is acceptable. OK.

**Reloaded packages.** None of amsmath, amsthm, amsfonts, amssymb, bera, dsfont, hyperref, graphicx, latexsym, mathtools, microtype or geometry is reloaded. OK. The extra packages are booktabs, float, array, xcolor and enumitem (l.5–9):

- `float` is loaded, but no `[H]` placement occurs anywhere. Remove it.
- `xcolor` is used only by the drafting macro `\proofpending` (l.32). Remove both.
- `array` is not needed by the one table, which uses only `@{}` column specifiers available in base LaTeX. Remove it unless something else needs it.
- `booktabs` is used by Table 1 (`sec_shape.tex` l.682–700). Keep.
- `enumitem` (shortlabels) is used for `[(a)]`, `[(i)]`, `[(K1)]`, `[nosep]`. Acceptable. Note that the class redefines `itemize` and `enumerate` to reduce the item spacing for bera (cls l.452–456), and enumitem overrides that. This is harmless but worth knowing.

**Environments the class already provides.**

- `standinghyp` (l.16) duplicates the class environment `hypothesis` (cls l.441). The class asks authors to use its environments when possible (sample l.138–143). There is also a visible typesetting fault: the hypotheses are opened with the note already in parentheses, `\begin{standinghyp}[(RV)]` (`sec_setting.tex` l.51, 56, 60). amsthm adds its own parentheses, so the PDF prints "Hypothesis 1 ((RV))" (checked in the PDF text). Required: either use `\begin{hypothesis}[RV]`, or keep a separate environment and drop the inner parentheses.
- `introtheorem` (l.14–15), lettered A–F, is an author environment based on `theorem`. The sample says this is possible but not recommended. Lettered main theorems are common in EJP and acceptable here.
- The comment at l.11–12 says the class defines only seven theorem-like environments. It defines 23 (cls l.429–451). Correct or delete the comment.

**Macro names.**

- The sample says "never use one letter names for macros" (sample l.414). `\Z`, `\N`, `\R` and `\E` (l.19–22) break this. This is advisory, not a desk-reject item. Suggest `\ZZ`, `\NN`, `\RR`, `\EE`.
- The class maps `\mathbb` to dsfont (cls l.459–462), so these print in double-stroke style. That is intended.
- No `\def` is used. OK.

**Displays.** No `$$` anywhere (searched all files). Displays use `\[ \]`, `equation`, `align` and `multline`. OK.

**Labels.** All labels carry a prefix (`sec:`, `thm:`, `lem:`, `prop:`, `cor:`, `rem:`, `ex:`, `hyp:`, `eq:`, `fig:`, `tab:`). A search for unprefixed labels found none. OK.

**Named theorems and proofs.** Every theorem-like environment has a name in brackets. Proofs that do not immediately follow their statement are named ("Proof of Theorem~… (b) and (c)", "Verification"). This is good practice per sample l.238.

- One irregularity: the proof of Theorem 3.1 is not in a `proof` environment. It is a subsection of `\paragraph` steps that ends with a manual `\qed` (`sec_bulk.tex` l.387–647). Acceptable, but a `proof` environment would be cleaner.

**Figure.** One figure (`sec_intro.tex` l.43–59). It meets the class rules:

- placement `[t]`, `\centering`, and `\label` after `\caption`;
- the graphic is a PDF (`figures/atlas.pdf`, with a PNG beside it).

Points to fix:

- `\graphicspath{{figures/}{../figures/}}` (main l.34) points outside the submission folder. The upload must be self-contained. Keep only `figures/`.
- The caption of panel (b) does not say that both axes are logarithmic, which the image shows.
- The caption sends the reader to Section 8 for the computations (l.56–57), and Section 8 is empty (see 1.3).

**Table.** Table 1 (`sec_shape.tex` l.682–700) has `\centering` and a label after the caption. OK.

**Bibliography: format.**

- It is inline `thebibliography` with numeric labels. OK.
- The entries are sorted alphabetically by author. I checked the whole list, including the multi-author ties (Cénac ×2, Feller ×2, Melbourne–Pène–Terhesiu before Melbourne–Terhesiu, Wang W.–Höll before Wang W.–Schulz, Zaburdaev–Denisov–Hänggi before Zaburdaev–Denisov–Klafter). OK.
- Entries follow the class sample's form: "Author, A.: Title. *Journal* **vol**, (year), pages. \MR{…}", and books carry publisher, city, year and page count. OK.
- `\MR{}` appears wherever MathSciNet has a record. The physics papers (Phys. Rev. Lett./E, Sci. Rep.) have none, which is normal. Run BatchMRef once (sample l.454) to catch any that MathSciNet does index.
- `\ARXIV{}` is used for the two preprints (mpt2026, paperA). OK.

Faults in the bibliography:

- `\bibliographystyle{abbrv}` (main l.80) is a leftover. It has no effect on an inline bibliography, but it writes a `\bibstyle` to the `.aux` and will confuse anyone who runs BibTeX. Remove it.
- `\small` after `\begin{thebibliography}{99}` (l.81) is redundant: the class already sets `\small` (cls l.375, l.386).
- **Five entries are never cited:**

  | Key | Main file line |
  |---|---|
  | `bvb2024` | 88 |
  | `erickson1970` | 150 |
  | `garsialamperti1962` | 172 |
  | `sera2024` | 248 |
  | `yamazato1978` | 273 |

  These look like leftovers from the archived earlier draft. Remove them or cite them. Required.
- `paperD` (l.232–233) is "In preparation". The referees cannot see it, and the introduction leans on it (`sec_intro.tex` l.235–238). Required: post it and give the arXiv number, or drop the citation and the sentence.
- Bibliographic data to verify before submission:
  - `bby2023`: printed as Ann. Fac. Sci. Toulouse Math. (6) **33** (2024), 1413–1485. The prior-art note records 33(5), 2025, DOI 10.5802/afst.1802. Check the year.
  - `sera2024`: the key says 2024 and the entry says ETDS **46** (2026). Moot if it is removed.
  - `mpt2026` (arXiv 2610.15720) and `paperA` (arXiv 2610.06935): confirm the identifiers.

**Length.**

- From the survey (journal pages): EJP has no hard cap, and papers under 12 pages should go to ECP first. 62 pages is far over that threshold, so EJP is the right journal.
- 62 pages is long for EJP but not exceptional for a paper with six main theorems. The editorial view is in Part 2.

**Abstract.** About 230 words, with no citations and no displayed mathematics. Good on those counts. Problems:

- l.47–52: "The law has four pieces. A stable bulk …, a big-jump zone …, a renewal boundary layer …, and an atom at each endpoint." The second "sentence" has no verb. Join it to the first with a colon.
- "bin by bin over the whole row" (l.47) uses the Galton-board vocabulary of the series ("row"). A probabilist reader expects "for every value $k$" or "pointwise over $0\le k\le N$".
- The last clause, "the big-jump theorem needs the local form of regular variation, which we show is necessary" (l.61–62), overclaims. The paper shows only that (RV) alone is insufficient (Example 4.11). Remark 4.12 (`sec_bigjump.tex` l.870–890) itself says that two weaker conditions suffice on the ballistic range and that "we do not pursue the sharp condition". Required: replace with something like "and we show that regular variation of the tail alone does not suffice".

**Title.** Accurate and informative. "Occupation law" is slightly unusual, but it is defined at once and the running title is consistent. OK.

**Other guideline items** (from the survey):

- The submission is by PDF through EJMS. LaTeX source is sent only after acceptance.
- There are no fees and the licence is CC BY.
- Board membership and suggested referees are out of scope here.
- No statement on data or code availability was found on the journal pages that were readable. However, the paper's Section 8 is meant to describe certified computations and formal proofs and to point to a repository. If that section stays, it is the natural place for a code-availability sentence.

### 1.2 Status of the draft (decisive for the desk)

These are not template matters, but no editor can send the PDF out in its present state.

1. **Section 8 is a placeholder** (`sec_verify.tex` l.1–3). The PDF prints, in dark red on page 59, "[Proof to be written. Source: to be written after the numerics and the Lean files exist. Contents: …]", followed by internal working instructions ("Follow the conventions of the verification section of the elephant-walk paper"). Several parts of the paper refer to this section as if it existed:
   - `sec_intro.tex` l.56–57 (figure caption) and l.259–261;
   - `sec_setting.tex` l.300–302 ("Section~\ref{sec:verify} records their formal proofs").

   The drafting macro `\proofpending` and `\usepackage{xcolor}` (main l.8, 31–32) must go with it.
2. **Numerical claims with no documented provenance.** The text quotes computed values in several places, and their method and precision are promised only in the missing Section 8:
   - Remark 4.9 (`sec_bigjump.tex` l.752–757): ratios at N = 1200 and 3000;
   - after Corollary 5.5 (`sec_preparation.tex` l.729–732): ratios at N = 2400;
   - after Theorem 6.3 (`sec_shape.tex` l.435–437): $C(j)/j$ values;
   - after the second-order renewal display `eq:second-renewal` (`sec_shape.tex` l.500–502);
   - Table 1 (`sec_shape.tex` l.677–700), described as "double precision" only;
   - Figure 1.

   Either supply Section 8 (method, arithmetic, error control, code location) or cut the numbers to what the figure needs and say in one sentence how they were computed.
3. **Status of the theorems.** The folder's `README.md` describes the draft as a "skeleton" whose "tier 2" statements (Theorem B, parts of Theorem C, Theorem E) "will be downgraded to conjectures … if their proofs do not close". The section files do contain complete proofs of all six lettered theorems; no other `\proofpending` remains. The author should still confirm in the cover letter that every stated theorem is proved in the submitted version.

### 1.3 Exact list of changes required before the paper goes to referees

Main file `problem131_levy.tex`:

| Line(s) | Change |
|---|---|
| 6 | Remove `\usepackage{float}` (unused). |
| 7 | Remove `\usepackage{array}` unless something needs it. |
| 8 | Remove `\usepackage{xcolor}`. |
| 11–12 | Correct or delete the comment on which environments the class defines. |
| 16 | Replace `standinghyp` by the class's `hypothesis`, or keep it and fix the double parentheses (see `sec_setting.tex` below). |
| 19–22 | Advisory: rename the one-letter macros `\Z`, `\N`, `\R`, `\E`. |
| 31–32 | Delete the drafting macro `\proofpending`. |
| 34 | Restrict `\graphicspath` to `{figures/}`. |
| 39 | Use `\BEMAIL` instead of `\\ \EMAIL`. |
| 41–42 | Advisory: make the keyword "mode" specific. |
| 43 | Split into `\AMSSUBJ` (primary) and `\AMSSUBJSECONDARY`. |
| 44–62 | Fix the verbless sentence (l.47–52); replace "row" (l.47); replace "which we show is necessary" (l.61–62). |
| after 62 | Add `\SUBMITTED{…}` and `\ACCEPTED{…}` placeholders. |
| 73 | `\input{sec_verify.tex}`: supply the section or remove it (see below). |
| 80 | Delete `\bibliographystyle{abbrv}`. |
| 81 | Delete the redundant `\small`. |
| 88, 150, 172, 248, 273 | Remove the uncited entries `bvb2024`, `erickson1970`, `garsialamperti1962`, `sera2024`, `yamazato1978`, or cite them. |
| 232–233 | `paperD`: give an arXiv number or remove the entry and its use in `sec_intro.tex` l.235–238. |
| 96–99 | Verify the year and issue of `bby2023`. |

Section files:

| File, line(s) | Change |
|---|---|
| `sec_verify.tex` l.1–3 | Write the section, or delete it and every reference to it. |
| `sec_intro.tex` l.56–57, 259–261 | Remove or update the references to Section 8. |
| `sec_setting.tex` l.300–302 | Remove or update the reference to Section 8. |
| `sec_setting.tex` l.51, 56, 60 | `[(RV)]`, `[(LR)]`, `[(SPAN)]` print with double parentheses. Use `[RV]` etc., or the class `hypothesis`. |
| `sec_bigjump.tex` l.752–757; `sec_preparation.tex` l.729–732; `sec_shape.tex` l.435–437, 500–502, 677–700 | Give the provenance of every computed number (method, precision, code), or remove the numbers. |
| `sec_intro.tex` figure caption | State that panel (b) uses logarithmic axes. |
| `sec_bigjump.tex` l.870–890 vs abstract | Bring the abstract in line with what Remark 4.12 says about (LR). |
| `sec_intro.tex` l.204–206 | "are the input to Theorem B": the proof of Theorem B never invokes Denisov–Dieker–Shneer or Berger–Birkner–Yuan. Lemma 4.6 and Lemma 6.5 prove the needed estimates directly. Say "are the i.i.d. analogues of", or cite them where they are used. The i.i.d. local one-big-jump theorem under exactly (LR) is Berger, PTRF 175 (2019), Theorem 2.4, which is not cited. |
| `sec_inverse.tex` l.192–196 | Remove the unsupported claim about a "fixed-point argument … in logarithmic coordinates that we leave to separate work". |

Strongly recommended, not blocking:

- **Theorem 3.1** (`sec_bulk.tex` l.22–32) repeats Theorem A(a) word for word. Prove Theorem A(a) directly and drop the restatement.
- **Theorem B(a)** is stated under "(RV) and (SPAN) for both signs" (`sec_bigjump.tex` l.53). The remark after it (l.86–87) says (a) needs only (RV) for the plus sign. State the minimal hypotheses in the theorem itself.
- **Missing classical citations.**
  - Takács and Kesten (1962) for the distributional stable limit of the occupation time.
  - Kaluza (1928) for log-convexity of renewal sequences, next to de Bruijn–Erdős (`sec_shape.tex` l.512).

---

## Part 2. Editorial judgment

### 2.1 Scope

The paper is squarely within the scope of EJP. Its subject is local limit theory for a renewal functional with heavy-tailed interarrivals: a uniform local theorem, local large deviations of one-big-jump type with a censored term, renewal boundary asymptotics, and sensitivity to the initial condition. The methods are those of the EJP papers it cites (Caravenna–Doney, Berger, Doney 2023). The physics motivation, infinite densities for Lévy walks, is a bonus, not the core.

### 2.2 The contribution, as I would put it to a referee

For the number $A_N$ of plus steps in an alternating renewal sequence with regularly varying run lengths of index in $(1,2)$, the paper describes $\Prob(A_N=k)$ for every $k$:

- a stable local limit theorem that is uniform over the whole row under regular variation and aperiodicity alone, for every relation between the two stable scales;
- a two-term big-jump asymptotic, a completed giant run plus a run censored at the horizon, valid up to the endpoint under local regular variation, which joins a renewal boundary layer $T_+(N)u_-(j)$;
- sharp criteria for when the law of the first run matters in each zone.

The consequences are:

- a rigorous lattice form of the physicists' infinite density, including the censored-run term;
- a threshold for the global mode, which under the stationary start is the golden ratio;
- the location of the interior minimum at the stable scale of the opposite runs, with an exact second-order coefficient.

### 2.3 Referees, by area

1. **Local limit theorems and local large deviations for heavy-tailed random walks, and strong renewal theorems.** The authors of the papers the bulk and big-jump proofs use or compete with: the circle of Caravenna–Doney, Berger, Denisov–Dieker–Shneer. This referee carries Theorems A and B.
2. **Renewal theory and regenerative processes**: alternating renewal and occupation-time limits, renewal remainder theory (Frenk, Rogozin, Doney 2023), and preferably the compound and generalized renewal large-deviation literature (the Borovkov school). This referee carries Theorem C, the second-order expansion and the antimode, and the question in 2.4(c).
3. **Optional, short report**: someone from the mathematical-physics side of anomalous diffusion and Lévy walks, or from infinite ergodic theory, where Melbourne–Pène–Terhesiu and Sera sit. Their job would be to check the claims about the physics literature in the introduction (what Rebenshtok et al., Vezzani–Barkai–Burioni and Wang et al. did and left open), and the comparison with the Young-tower local limit theorem.

### 2.4 Risks to flag to the referees

**(a) Long uniform estimates.** The core of the paper is about 35 pages of $\varepsilon$–$K$–$N$ arguments with constants that must be uniform over moving scale ratios. This is the kind of text where gaps hide in the order of the limits and in "the same argument with the signs exchanged". From a reading of the proofs, the places I would ask the referees to check line by line are these:

- **Theorem A, Steps 3–5** (`sec_bulk.tex` l.471–622). The whole-row claim rests on three things:
  - Lemma 3.5(b), uniform over the class $\Psi(\omega)$ and over levels $j\ge\varepsilon N$;
  - the "dominant sign chosen afresh for each $N$" device of Step 6;
  - the left-deviation bound, Lemma 3.2(iv), handling too many runs.

  The structure is sound and every constant is named, but uniformity in $\theta_N$ is asserted in Step 6 more than it is tracked. The referee should confirm that no error term depends on $\theta_N$ through $a_{\bar\tau}(k_{\bar\tau}/\mu_{\bar\tau})/b_{\bar\tau,N}$ when $\theta_{\bar\tau,N}\to0$.
- **Lemma 4.3 (no giant run)** (`sec_bigjump.tex` l.321–406). The minus-start case is dismissed in one sentence: "the argument below changes only by shifts of the index by one, which cost $O(1)$ in the deviations" (l.346–348). This lemma is reused for minus starts in Example 4.11 and in the window-sufficiency proof of Theorem C(c) (`sec_preparation.tex` l.586–606). The minus-start case should be written out or checked explicitly.
- **Theorem C(c), sufficiency of the window condition** (`sec_preparation.tex` l.574–645). The bound `eq:far-bound` for a fresh minus start is assembled from three earlier lemmas and then summed over blocks. It is the most intricate argument in the paper and the least load-bearing for the main message. Check it, or ask the author whether this "if" direction is worth its space.
- **Lemma 6.5, uniform local big jump** (`sec_shape.tex` l.291–350). This is self-proved, with an exponent bookkeeping $\varepsilon<\gamma/(4(1+\gamma))$, and Proposition 6.7 and Theorem E rest on it. It is short and checkable.
- **Citation risks in the antimode.**
  - The second-order renewal theorem is attributed to "Lemma 4 of Frenk" (`sec_shape.tex` l.493–495). Frenk's paper is titled for tails of index $-1$. The referee should confirm that the cited lemma really covers $1<\alpha<2$, or the author should cite a source stated for that range, such as Rogozin, or Doney 2023 Theorem 1.
  - The de Bruijn–Erdős attribution for log-convexity should be checked as well.

I did not find a gap. But the paper is long enough, and the uniformities delicate enough, that I would tell the referees explicitly that this is where to spend their time. Theorem F, by contrast, is elementary, and Theorem D(d) is an explicit computation: I checked $\mathcal C(\varphi)=0.7761317\ldots$ and the elementary upper bound $0.9514\ldots$ numerically.

**(b) Novelty of the bulk window.** The author already concedes this (`sec_intro.tex` l.179–186): Berger (EJP 2019, Theorem 3.3) applied to the walk of run lengths, together with the fresh-plus identity, gives the window $|k-pN|\le KB_N$. What is claimed as new is the whole-row uniformity and the bound $\sup_k B_N P_N(k)\le C$ under (RV) alone. Berger's off-direction bounds need his local Assumption 2.2. The prior-art note records that the inequality conditions of Berger's Theorem 3.3 were not checked on the page. Ask the referee in area 1 to confirm both that Theorem 3.3 applies as stated and that the whole-row statement is not a corollary of Berger's Theorems 4.1–4.3 under (RV) alone. If it were, Theorem A would shrink to a remark.

**(c) Could an older local theorem for compound renewal processes cover Theorem A?** The prior-art note (`research_notes/Paper F prior art/01_compound_renewal_local_theorems.md`, §§1–3, 8) checked:

- the integro-local and local theorems for compound and generalized renewal processes (Borovkov–Mogulskii 2018; Mogulskii–Prokopenko 2018; Bakai–Shklyaev 2019; Logachov–Mogulskii–Prokopenko–Yambartsev 2021). All work under Cramér's condition;
- Borovkov TVP 2017/2018 and Chapter 2 of Borovkov's 2022 book, which are Gaussian-zone analogues of Stone's theorem;
- the heavy-tailed results for $S(T)$ (Borovkov–Borovkov 2005/2006 and Chapter 16 of their 2008 book), which are integral large-deviation and boundary-crossing statements, not bin probabilities.

There are also two structural differences:

- $A_N$ includes the reward of the unfinished final cycle, while the compound renewal process counts completed cycles only;
- the cycle pair $(X_++X_-,X_+)$ is neither independent nor linearly dependent in Borovkov's sense.

The residual risk is real but narrow. Three things were not read: case (a) of Borovkov's 2017 TVP paper, Chapter 2 of the 2022 book, and the Takács 1957/1959 papers together with Smith 1955 and Nagaev 1957. I would ask the referee in area 2 to confirm that none of these gives a stable-scale local theorem for a renewal-reward process with independent components that could be adapted. Even if one did, it would give the bulk window at most. The censored run, the remote bins and the whole-row bound would remain.

**(d) Claim calibration.**

- The abstract's "which we show is necessary" (see Part 1).
- The introduction says the local one-big-jump theorems "are the input to Theorem B" while the proof does not use them.
- Theorem B's zone carries a factor $\lambda_N=1+\log(1/\theta_{+,N})$ whose sharpness is open (Remark 4.10). The introduction should say plainly that the start of the zone is not sharp when the minus scale dominates.

### 2.5 Length

At 62 pages the length is defensible for Theorems A–C, which are the paper. It is not fully justified for the rest. I would not make cuts a condition for refereeing, but I would ask for these in the same round as the presentation changes. Together they save roughly 8–10 pages and make the referees' job easier:

- drop the duplicate Theorem 3.1;
- replace by citations the proofs of classical facts:
  - positivity of stable densities (Lemma 2.1, Step 4, about a page);
  - the normalization check in Lemma 3.2(i);
  - the exponential truncated-deviation bound, Lemma 4.2, which is Fuk–Nagaev;
- shorten or move to remarks without proof:
  - Remark 5.7 (regularly varying preparations), whose "Verification" is a restatement;
  - the refinement sketch at the end of Remark 4.10;
  - Remark 4.12 on weaker hypotheses;
  - the speculative last sentence of Remark 7.3;
- demote Theorem F to a corollary or proposition. It is an inversion of the renewal equation plus the thinning remark, and a lettered main theorem overstates it;
- either complete Section 8 concisely (1–2 pages) or remove it, keeping one sentence on how the figure and the table were computed.

### 2.6 Decision

**Return to the author for presentation changes before refereeing.** This is not a desk rejection.

Reasons:

- The paper is in scope, and its main theorems are substantial and plausibly new. The prior-art check supports the novelty of the whole-row uniformity, the censored-run big-jump asymptotic with the boundary layer, and the first-run criteria.
- Proofs are given for every stated theorem.
- But the submitted PDF is visibly unfinished. A section is a placeholder that prints internal drafting notes in colour. Computed values throughout the paper rest on that missing section. The bibliography carries five uncited entries and one unavailable "in preparation" item. Two claims (the necessity of (LR), and the role of the i.i.d. big-jump theorems) are stated more strongly than the text supports.

None of this requires new mathematics, and all of it would be held against the paper by any referee. It is cheaper for everyone to fix it first.

On resubmission, with the items of 1.3 done and ideally the cuts of 2.5, I would send it to the referees of 2.3 with the risks of 2.4 attached.
