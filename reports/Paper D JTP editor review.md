# Paper D: merged editor review for the Journal of Theoretical Probability

Paper: "Endpoint crossings for the elephant random walk" (A. Pemmasani, Harvey Mudd College).
Source: `kagey-problems/problem131/paperD/` (main file `problem131_memory.tex`, 49 pp).
Plan: arXiv on Nov 1 2026, then JTP (Springer, Snapp submission). ALEA and Advances in Applied Probability are the fallbacks.
Merged from four reviews (fit-novelty, structure-length, compliance, exposition) plus the guideline notes (`reports/Paper D JTP guidelines.md`) and the literature notes (`reports/Paper D JTP literature.md`).
I checked every must-do item against the source files as they stood on 2026-10-16. No paper file was edited. Line numbers refer to those files. Theorem numbers come from `problem131_memory.aux`.

Labels used below:
- **[AUTHOR]** means a substantive rewrite or decision that the author should do personally.
- **[MECH]** means a small mechanical fix that can be applied as written.

**Editor's verdict.** The paper is in scope and its results are new and substantial. It should go to referees once the Tier 1 and Tier 2 items are done. As it stands, three things put it at risk of a desk rejection:
- It never mentions the broadcasting-on-random-recursive-trees literature, which studies the same model, including a 2026 JTP paper.
- The headline result is buried, and the introduction leads with the puzzle and with a companion preprint.
- The AI disclosure is still a placeholder.

None of these needs new mathematics.

---

## 0. Corrections to the brief and to the reviews

Each of these was checked in the source files.

1. **Paper B is not cited.** No `.tex` file contains `paperB` or `2610.09258`. Paper D cites only Paper A (`problem131_memory.tex:119-122`), and uses only its Proposition 3.8, in Theorem 2.8 and in the second display of the Main Theorem (`sec_intro.tex:100-108`). Nothing needs to change in the paper. The cover letter should explain how D relates to Papers A–C (item 2.16).
2. **The release tag named in the paper does not exist yet.** `problem131_memory.tex:100-101` points to the release `paperD-arxiv-v1`. `git tag` lists only `paperA-arxiv-v1`, `paperA-arxiv-v2` and `paperB-arxiv-v1`. See item 1.2.
3. **The Main Theorem does not use an undefined `m^*`.** Exposition item 1 said it did, but the theorem (`sec_intro.tex:128-151`) uses only `a^*`. The point is dropped. Its other sub-point, that convexity for 10 ≤ N ≤ 2000 is proved but not stated, is correct and is kept as item 1.6.
4. **"Endpoint" does appear in the body.** The fit-novelty review said it never does, but it appears in "endpoint dip" (`sec_erw_shape.tex:174`) and "endpoints" (`sec_erw_shape.tex:613`). The concern about the title is weaker as a result but still stands (item 1.8).
5. **The fit-novelty computation paragraph (its M5) ended with an incorrect sentence.** It claimed that only the 60-term sum and the Landau-mode enclosure "need exact constants for the finite thresholds". In fact the Landau-mode enclosure feeds no finite threshold, and the floating-point computation feeds Proposition 3.27(b) through part (a) and Proposition 3.8. Item 1.5 gives corrected text.
6. **Fit-novelty M6 said the value 5200 matters only for the threshold 1688.** It is also used for the threshold 1689 for odd N (Proposition 3.26(c), `sec_erw_shape.tex` proof of (c)) and in Proposition 2.9. The text in item 2.7 is corrected to say so.
7. **Lemma 3.4 (unimodality, via GLRS) is true for every ε.** The exposition review asked whether it holds for every ε. `lean/PaperD/MAP.md:159` records that `law_isUnimodal` is proved in Lean for every 0 ≤ ε < 1. The open point is only how the paper cites it, so the item is downgraded to Tier 2 (item 2.8).
8. **Remark 2.11 already says that no explicit N beyond which g_N > x_N is known** (`sec_erw_crossing.tex:494`). Exposition item 17 is therefore partly done, and it is kept as optional.
9. **Line references corrected:**
   - The AI note is at `problem131_memory.tex:81-84`, not 70-73.
   - `sec_verify.tex:44-45` says "Data and code availability", not "Data availability".
10. **Two names in the literature brief were wrong:**
    - "Kiss–Laulin" is Kiss–Vető, ECP 27 (2022).
    - The critical-ERW returns-to-origin paper is by Fang, ECP 29 (2024), not Bertoin.
11. **The abstract already meets the length rule.** It has 221 words, within 150–250, and contains no \cite and no displayed math. The rewrite in item 1.7 is for content and clarity, not compliance.

---

## Conflicts between the reviews and how they were resolved

| # | Question | Options in the reviews | Chosen | Why |
|---|---|---|---|---|
| C1 | Headline theorems | Fit-novelty: three theorems (crossing, bulk, shape). Structure: A (crossing), B (law at the crossing), C (five blocks), plus a status table. Exposition: 1.1 crossing, 1.2 large-N law, 1.3 computer-assisted range. | Fit-novelty's three theorems. Theorem 1.3 marks the non-effective threshold and the computer-assisted range inside its own parts, as the exposition review asked. The prose list is replaced by the structure review's status table. | This puts the explicit two-sided bound on the center and the compound Poisson/Landau result in the headline, where JTP readers will look. Keeping the computer-assisted range in a labelled part makes clear what rests on computation without needing a fourth theorem. |
| C2 | Where the AI disclosure goes | Fit-novelty: Declarations. Compliance: Section 4, as the "suitable alternative part" to a Methods section. | Section 4, closing paragraph, plus a one-line pointer in Declarations, the cover letter and Snapp. | Springer asks for the disclosure in Methods "or a suitable alternative part". Section 4 is where the paper describes its computational methods. |
| C3 | Section 4 (Verification) | Structure: fold it into the intro and Data availability. Others: keep it. | Keep a short Section 4 of about half a page. Move script names, run times and package lists to Code availability. | It hosts the AI disclosure (C2) and the list of computer-assisted steps that the intro paragraph points to. |
| C4 | Double-precision certificate (Lemma 3.7, Proposition 3.8 for N<1688) | Structure: replace it with the existing ball-arithmetic enclosure. Fit-novelty: add ball arithmetic and keep the lemma as a second check. Exposition: move it to App. D. | Replace it (structure M3). The lemma can go to the supplement. | `certify_center.py:31-37` already encloses ε_N rigorously for every even 10 ≤ N ≤ 2000. Checking `lo > 2/(N+2)` closes the case with no hand rounding analysis. This removes one of the four computational dependencies and about 1.9 pp. |
| C5 | Theorem 3.15 (window) | Structure and fit-novelty: delete it. Exposition: delete it, or keep it as a one-line remark. | Delete it. | The paper says itself (`sec_erw_shape.tex:994-995`) that Corollary 3.24 follows without it. It carries non-explicit constants C_w and N_0, and Prop. B.5(b) is used only for it. |
| C6 | Declarations heading | "Statements and Declarations" (JTP page) or "Declarations" (sn-jnl). | "Declarations". | It matches the template. |
| C7 | Keywords | Fit-novelty: swap two. Compliance: swap one. | Swap two (item 2.15). | Pólya urn is a tool and the persistent walk is already in the abstract. Broadcasting is the closest literature, and "computer-assisted proof" tells readers what to expect. |
| C8 | Title | Fit-novelty: change it. Compliance: keep it. | Change it, as an author decision before Nov 1 (item 1.8). | "Endpoint crossings" is the paper's own coinage and is easy to misread. arXiv v1 and the journal version should have the same title. |
| C9 | When to make the structural cuts | Structure: before Nov 1, so that arXiv v1 matches the submission. | Tier 1 holds only the non-structural fixes. Items 2.4–2.6 should also be done before Nov 1 if there is time. Otherwise post v1 and post v2 at submission. | arXiv v2 is free, and JTP has no rule requiring v1 to match. |
| C10 | `sec_intro.tex:115-126` (Results prose before the theorem) | Compliance: keep it. Structure: delete it. | Delete it once the theorems are restructured. | It restates the theorem. |
| C11 | Paper A comparison (second display of Main Theorem (a)) | Fit-novelty: move it to a remark in Section 2. Exposition: keep it, with an explicit citation. | Move it to a corollary or remark in Section 2. Until then, add the citation (item 1.6). | A headline result should not rest on an unrefereed preprint by the same author. |
| C12 | Second-order results (Section 2.4, App. A.1) | Structure option A: move them to the supplement. Option B: compress the constants. | Option B, in Tier 3. | JTP has no page limit, and Table 1 uses the result. |

---

## Tier 1: must fix before the arXiv posting on Nov 1

### 1.1 Replace the AI placeholder and write the disclosure [AUTHOR text, MECH placement]
- **Where:** `problem131_memory.tex:81-84` (`\section*{A note on the use of AI}`, the comment `% AI NOTE: to be written by the author.`, and a single responsibility sentence).
- **Issue:**
  - arXiv serves the LaTeX source, so the comment becomes public.
  - The section is empty apart from its heading.
  - Springer requires disclosure of any AI use beyond copy editing. Undisclosed AI-generated core reasoning, and fabricated citations, are not permitted.
- **Fix:**
  1. Delete lines 81–84.
  2. Insert this paragraph in `sec_verify.tex` after line 42 and before line 44, and fill in the brackets truthfully:
     ```latex
     \paragraph{Use of AI tools.} The author used [tool and version] for [each use that applies:
     literature search; drafting and editing prose; proposing or checking proof steps (name the
     results); writing the verification and certification scripts, the Lean files and the figure
     code]. The author checked every proof by hand, reran every computation by the methods
     described in this section, and checked every reference against its source. The author takes
     full responsibility for the content of this paper.
     ```
  3. If AI proposed any proof or proof idea, name those results explicitly.
  4. At JTP time, also add a one-line pointer in Declarations (item 2.2) and summarize the disclosure in the cover letter and in Snapp.

### 1.2 Build the arXiv source and create the release [MECH]
- **Where:**
  - `problem131_memory.tex:15, 28, 82` (the only comments in the sources);
  - `problem131_memory.tex:98-111` (Data and code availability).
- **Fix:**
  1. Run `arxiv_latex_cleaner`, as planned in `../PUBLICATION.md:28`.
  2. Upload only the 9 `.tex` files plus `figures/family.pdf` and `figures/shape.pdf`. Leave out `figures/crossing.pdf`, which is not referenced, as well as `data/`, `removed_proofs/`, the scripts and the `.png` files.
  3. The bibliography is inline, so no `.bbl` is needed.
  4. Before posting, create the tag `paperD-arxiv-v1` at the commit that matches the uploaded source, and confirm that `https://github.com/apemm/Kagey-Problems` is public.
  5. Check that the release contents (`data/`, `ledger*.md`, `reports/`) are consistent with the AI disclosure. The release will be public.

### 1.3 Add the broadcasting literature and limit the novelty claim [AUTHOR: check citations; text drafted]
- **Where:**
  - `sec_intro.tex:35-41` (the opening positioning);
  - `sec_intro.tex:243/244` (insert between "...mode." and "Gu\'erin, Laulin...");
  - `sec_intro.tex:248-252` (the closing sentence);
  - the bibliography.
- **Issue:** Lemma 3.1 (`lem:tree`) is exactly broadcasting on a random recursive tree with flip probability ε, and C_N is the tie probability in the majority-vote error. The present sentence "We did not find an asymptotic formula ... in the elephant-walk, percolation or Luria–Delbrück literature that we read" omits that literature. A JTP referee who knows it will read the omission as a gap in the positioning, and the arXiv version would make the claim public.
- **Fix 1.** After "(Section~\ref{sec:prior})." on line 41, add:
  > In the language of broadcasting on random recursive trees~\cite{adlv2022,ahs2026}, ending in the middle means that the two colors tie.
- **Fix 2.** Insert this new paragraph between lines 243 and 244:
  > The same model is studied as broadcasting on random recursive trees. Each new vertex attaches to a uniform earlier vertex, copies its spin and flips it with probability $q$, so by Lemma~\ref{lem:tree} the spins are our steps with $q=\varepsilon$. Addario-Berry, Devroye, Lugosi and Velona~\cite{adlv2022} and Althaus, Hartung and Steiner~\cite{ahs2026} study how well the spin of the root can be recovered from the spins at time $N$, with $q$ fixed as $N\to\infty$. In that language $N-2M_N$ is the difference of the two color counts given the root, and the center $C_N$ is the probability of a tie, which enters the error of the majority vote. Desmarais, Holmgren and Wagner~\cite{dhw2023} prove limit laws for the color counts of broadcasting on preferential attachment trees, and Kardas, Shneer and Wachtel~\cite{ksw2026} give martingale methods and error bounds, again with a fixed flip probability.
- **Fix 3.** Replace lines 248–252 ("We did not find ... $M_N=N/2$.") with:
  > We did not find an asymptotic formula for the center probability when $N\varepsilon$ is of order $\log N$ in the elephant-walk, broadcasting, percolation or Luria--Delbr\"uck literature that we read. The broadcasting results fix the flip probability as $N$ grows, and the Luria--Delbr\"uck results concern the number of mutants, which is our $M_N$, and do not reach the center $M_N=N/2$.
- **Bibliography.** Add these entries in the current style and check each one against the published version: authors, title, volume, pages and DOI. Initials in brackets were not verified.
  ```latex
  \bibitem{adlv2022} L.~Addario-Berry, L.~Devroye, G.~Lugosi and V.~Velona, \emph{Broadcasting on random recursive trees}, Ann.\ Appl.\ Probab.\ \textbf{32} (2022), 497--528. \href{https://doi.org/10.1214/21-AAP1686}{doi:10.1214/21-AAP1686}.
  \bibitem{ahs2026} [initials]~Althaus, [initials]~Hartung and [initials]~Steiner, \emph{A random walk approach to broadcasting on random recursive trees}, J.\ Theoret.\ Probab.\ \textbf{39} (2026), article 65. \href{https://doi.org/10.1007/s10959-026-01519-z}{doi:10.1007/s10959-026-01519-z}.
  \bibitem{dhw2023} C.~Desmarais, C.~Holmgren and S.~Wagner, \emph{Broadcasting-induced colorings of preferential attachment trees}, Random Structures Algorithms \textbf{63} (2023), 364--405. \href{https://doi.org/10.1002/rsa.21142}{doi:10.1002/rsa.21142}.
  \bibitem{ksw2026} [initials]~Kardas, S.~Shneer and V.~Wachtel, \emph{Broadcasting on random trees: martingale methods and error bounds}, preprint, 2026. \href{https://arxiv.org/abs/2606.22960}{arXiv:2606.22960}.
  ```
- Before keeping the clause "again with a fixed flip probability" for DHW and KSW, confirm it against those papers. The literature search did not read either of them in full.

### 1.4 Cite the coin-turning walk (JTP) [MECH text; check the Beta claim]
- **Where:** `sec_intro.tex:204`, after "Bertoin~\cite{bertoin2022zeros} counts its returns to the origin."
- **Fix.** Insert:
  > The coin-turning walk of Engl\"ander and Volkov~\cite{ev2018,evw2020} is the persistent walk with a switch probability $p_n$ that depends on the time $n$. For $p_n=a/n$ the frequency of heads tends to the Beta$(a,a)$ law, which is U-shaped for $a<1$ and humped for $a>1$, so in that limit the ends and the middle trade places at $a=1$. Our question is a finite-$N$ version of this comparison for the elephant walk, whose reversal probability depends on $N$ and not on the time.
- **Bibliography:**
  ```latex
  \bibitem{ev2018} J.~Engl\"ander and S.~Volkov, \emph{Turning a coin over instead of tossing it}, J.\ Theoret.\ Probab.\ \textbf{31} (2018), 1097--1118. \href{https://doi.org/10.1007/s10959-016-0725-1}{doi:10.1007/s10959-016-0725-1}.
  \bibitem{evw2020} J.~Engl\"ander, S.~Volkov and [initials]~Wang, \emph{The coin-turning walk and its scaling limit}, Electron.\ J.\ Probab.\ \textbf{25} (2020), paper no.~3. \href{https://doi.org/10.1214/19-EJP406}{doi:10.1214/19-EJP406}.
  ```
- Check the Beta(a,a) statement against the theorem in EV 2018 before posting.

### 1.5 Say in the introduction exactly what rests on computation [MECH]
- **Where:**
  - after `sec_intro.tex:156` (the end of "Part (b) collects ...");
  - the theorem headers at `sec_erw_shape.tex:261` (Lemma 3.7), `:285` (Prop. 3.8), `:422` (Lemma 3.11) and `:939` (Prop. 3.27). Prop. 3.25 at `:844` already carries "computer-assisted".
- **Issue:** The introduction mentions only the dip computation and the convexity computation (`sec_intro.tex:166-168, 194-196`). The 60-term sum and the Landau-mode enclosure appear only on p. 26. A referee should not have to discover there that a headline statement uses a computer.
- **Fix 1.** Insert this paragraph after line 156. This is the current-state version. Its fourth sentence changes if item 2.6 is done.
  > Four inputs to the proofs rest on computation, and Section~\ref{sec:verify} describes each of them. The constant $5200$ in Theorem~\ref{thm:erw-bounds}(b) uses the numerical value of a sum of sixty positive terms, while the asymptotic statements need only that this series converges. Lemma~\ref{lem:landau-mode}, on the mode of the Landau density, is proved in ball arithmetic, and Corollary~\ref{cor:mode-location}, Theorem~\ref{thm:convex-large} and the results that use them rely on it. For even $N<1688$, Proposition~\ref{prop:dip-hyp} rests on a double-precision computation with a proved bound on its rounding error (Lemma~\ref{lem:rounding}), and Proposition~\ref{prop:center-small}(b) uses it through part (a). Propositions~\ref{prop:convex-certified} and~\ref{prop:center-small}(b) are proved in ball arithmetic. Every other statement is proved by hand, and no proof uses the tables or the figures.
- **Fix 2.** Change these headers:
  - `[rounding error]` → `[rounding error, computer-assisted]`
  - `[the hypothesis holds from $N=8$ on]` → `[the hypothesis holds from $N=8$ on, computer-assisted for $N<1688$]`
  - `[the mode of the Landau density]` → `[the mode of the Landau density, computer-assisted]`
  - `[the center for $10\le N\le2000$]` → `[the center for $10\le N\le2000$, computer-assisted]`

### 1.6 State the finite range in the Main Theorem correctly and cite Paper A at the point of use [MECH]
- **Where:** `sec_intro.tex:137-138` and `:144-150`.
- **Issue:**
  - Part (b) states only the center-minimum claim for 10 ≤ N ≤ 2000, although Proposition 3.25 also proves convexity there.
  - Lines 147–150 are hard to parse.
  - The second display of (a) uses Paper A's Proposition 3.8, but the theorem does not say so.
- **Fix 1.** After "$c_*=\frac12\log(2\pi)-\frac14$." on line 138, add:
  > The second display uses the crossing equation~\eqref{eq:markov-crossing} of~\cite[Proposition~3.8]{paperA}.
- **Fix 2.** Replace "The last statement also holds for every even $N$ with $10\le N\le2000$." (lines 144–145) with:
  > For every even $N$ with $10\le N\le2000$ the last two statements also hold, by a computer-assisted proof (Propositions~\ref{prop:convex-certified} and~\ref{prop:center-small}).
- **Fix 3.** Replace lines 147–150 with:
  > The thresholds for large $N$ in (b) are not explicit (Remark~\ref{rem:convex-open}). For the even $N$ above $2000$ and below these thresholds both statements in (b) are open (Conjecture~\ref{conj:convex}). The second would follow from the first by Proposition~\ref{prop:center-small}(a) whenever each mode lies within $(N-2)/4$ of the nearer end.

  The condition 2m*+1 ≤ N/2 is the same as m* ≤ (N−2)/4, so this matches Proposition 3.27(a).

### 1.7 Rewrite the abstract [AUTHOR approves; text drafted]
- **Where:** `problem131_memory.tex:46-62`.
- **Issue:**
  - The abstract never says that ε → 0.
  - It omits the key bound on the center, the link to broadcasting, and the fact that a computer was used.
  - It ends on a garbled sentence ("the even $N$ above $2000$ and below it remain open").
- **Fix.** Use the text below. It is about 238 words, with each formula counted as one word, and has no \cite and no displayed math.
  > In the elephant random walk each step copies a uniformly chosen earlier step and reverses it with probability $\varepsilon$, as in broadcasting on a random recursive tree. We let $\varepsilon\to0$ as the number $N$ of steps grows and ask when the walk is as likely to end at the origin as at $N$. For even $N$ we prove that this crossing value of $\varepsilon$ is unique and that $N\varepsilon$ at the crossing equals $2\log N-\log\log N-\log16+o(1)$, about twice the value for the persistent random walk. Explicit two-sided bounds show that the walk ends at the origin with probability $4\varepsilon/(N+2)$ up to a factor $1+O(\varepsilon\log N)$, since such a walk usually reverses among its first few steps. We also describe the whole law at the crossing. The number of steps that disagree with the first step is within an explicit distance of a compound Poisson law of Luria--Delbr\"uck type, and after centering and scaling it obeys a local limit theorem with the Landau law. So the law of the final position has a hump near each of $\pm N$, which we locate. For every $N$ and every $\varepsilon<\frac12$ its second difference changes sign at most four times. For every large even $N$ the origin is at the crossing less likely than every other reachable position except $\pm N$, and a computer-assisted proof gives the same for every even $N$ from $10$ to $2000$. The even $N$ between $2000$ and the inexplicit large-$N$ threshold remain open.
- Recount the words after any further edits. The limit is 250.

### 1.8 Decide the title before v1 [AUTHOR]
- **Where:** `problem131_memory.tex:13` (pdftitle) and `:35`.
- **Issue:** "Endpoint crossings" is the paper's own coined term. It can be misread as the walk crossing an endpoint. It also leaves out both the regime and the broadcasting link that a JTP reader would search for. arXiv v1 and the journal version should carry the same title.
- **Options:**
  - "The center and the ends of the elephant random walk with rare reversals" (recommended);
  - "Ties in broadcasting on random recursive trees and the elephant random walk with rare reversals";
  - keep the current title.

---

## Tier 2: before the JTP submission

### 2.1 Switch to the Springer Nature template [MECH; needs a test compile]
- **Where:** `problem131_memory.tex:1-13, 16-26, 35-71`.
- **Fix:**
  1. Line 1: use `\documentclass[pdflatex,sn-mathphys-num]{sn-jnl}`.
  2. Delete line 3 (`geometry`).
  3. If sn-jnl loads hyperref, replace line 12 with `\hypersetup{colorlinks=true,...}`.
  4. Test `enumitem` (line 11) with the class.
  5. Theorem styles:
     - `\theoremstyle{thmstyleone}` before theorem through conjecture and mainthm;
     - `\theoremstyle{thmstylethree}` before definition and example;
     - `\theoremstyle{thmstyletwo}` before remark.
  6. Front matter:
     ```latex
     \title[<short title>]{<title from item 1.8>}
     \author*[1]{\fnm{Arjun} \sur{Pemmasani}}\email{apemmasani@hmc.edu}
     \affil*[1]{\orgdiv{Department of Mathematics}, \orgname{Harvey Mudd College}, \orgaddress{\city{Claremont}, \state{CA}, \postcode{91711}, \country{USA}}}
     \abstract{<abstract from item 1.7>}
     \keywords{<item 2.15>}
     \pacs[Mathematics Subject Classification (2020)]{Primary 60G50; Secondary 60E07, 60C05, 60F05, 60J10, 05C80, 65G30}
     \maketitle
     ```
  7. Delete `\date{}`.
  8. Enter the ORCID 0009-0001-2776-6298 in Snapp, and keep it in the PDF only if the class typesets it cleanly.
- **Snapp .zip contents:** all `.tex` files, `figures/family.pdf`, `figures/shape.pdf` and `sn-jnl.cls`. The bibliography stays inline. Compile it with pdflatex on TeX Live 2021, with no custom fonts.
- Re-measure the page count and re-check every line reference after the switch.

### 2.2 Rebuild the declarations and put them in the sn-jnl order [MECH]
- **Where:** `problem131_memory.tex:78-79` (Acknowledgments), `:92-111` (Statements and declarations, currently after the appendices), and `sec_verify.tex:44-46`.
- **Issue:**
  - Author contributions and Ethics/Consent are missing.
  - Data and code share one heading.
  - The block comes after the appendices, but the template puts it before them.
  - Springer returns papers without declarations "as incomplete".
- **Fix.** Before the appendices, put:
  ```latex
  \backmatter
  \bmhead{Acknowledgments} I thank Peter Kagey for posing the problem and Aidan Deshong for insightful conversations.
  \section*{Declarations}
  \bmhead{Funding} No funding was received for this work.
  \bmhead{Competing interests} The author has no competing interests to declare.
  \bmhead{Ethics approval and consent to participate} Not applicable.
  \bmhead{Consent for publication} Not applicable.
  \bmhead{Data availability} The outputs of the computations described in Section~\ref{sec:verify} are in the folder \nolinkurl{kagey-problems/problem131/paperD/data} of the repository named under Code availability.
  \bmhead{Code availability} <current lines 98-111, with ", archived at \url{https://doi.org/10.5281/zenodo.XXXXXXX}" after the release name, and the versions of item 2.17>
  \bmhead{Use of AI tools} See the end of Section~\ref{sec:verify}.
  \bmhead{Author contributions} Arjun Pemmasani is the sole author and is responsible for the whole paper.
  ```
- Then put the appendices, then the references.
- In `sec_verify.tex:44-46`, replace `the repository named under ``Data and code availability'' at the end of the paper` with `the repository named under Code availability in the Declarations`.
- Enter Funding, Competing interests and Author contributions in Snapp word for word. Only the Snapp versions are published.

### 2.3 Restructure the introduction around three numbered theorems [AUTHOR]
- **Where:** `sec_intro.tex:1-198` (the main block is lines 113–198).
- **Issue:**
  - The main theorem starts at the bottom of p. 3, after Paper A's crossing equation with its error terms (lines 97–111).
  - The headline states only the weak expansion. The sharp x_N = g_N + O(L²/N) and the explicit two-sided bounds on the center sit in the prose before it.
  - Part (b) mixes asymptotic claims, a computer-assisted finite range and an open-problem disclaimer.
  - The five-block theorem, which holds for every N and every ε, is not in the headline.
  - About 20 further results are listed in running prose (lines 158–198).
- **New order:**
  1. two opening paragraphs (draft below);
  2. Theorems 1.1–1.3;
  3. the computation paragraph (item 1.5);
  4. the heuristic "Why the elephant needs twice as many reversals" (lines 43–74, unchanged);
  5. notation;
  6. further results as a table;
  7. prior work;
  8. roadmap and organization (item 2.10).
- Move `eq:markov-crossing` and lines 97–111 to Section 2, next to Theorem 2.8. Shorten the p/q note on lines 109–111 accordingly.
- **Opening (draft):**
  > The elephant random walk of Sch\"utz and Trimper~\cite{schutz2004} has steps $X_1,\dots,X_N\in\{\pm1\}$. The first step is fair, and each later step copies a uniformly chosen earlier step and reverses it with probability $\varepsilon$. By the coupling of K\"ursten~\cite{kursten2016}, the steps are the spins of broadcasting on a random recursive tree~\cite{adlv2022,ahs2026}, in which each new vertex attaches to a uniform earlier vertex, copies its spin and flips it with probability $\varepsilon$. Most limit theorems for the walk fix $\varepsilon$ as $N\to\infty$~\cite{coletti2017,bercu2018,kubotatakei2019,glrs2025,tv2026}. We study the regime $\varepsilon=x/N$ with $x$ of order $\log N$, in which the walk reverses only about $x$ times, and we describe the law of its endpoint site by site.
  >
  > Our guiding question is when the walk is as likely to end at the origin as at $N$. For even $N$ let $C_N$ be the probability that the walk ends at the origin and $E_N$ the probability that it ends at $N$. When $\varepsilon$ is near zero the walk rarely reverses and $E_N$ is larger. At $\varepsilon=\frac12$ the steps are independent and $C_N$ is larger. We call the value $\varepsilon_N$ at which $C_N=E_N$ the crossing. In the language of broadcasting, $C_N$ is the probability that the two colors tie. The question comes from Problem~131 of Kagey's Open Problem Collection~\cite{kagey131}, where it is posed for a Galton board that is the persistent random walk, which copies its last step instead of a random one. For that walk the crossing value of $N\varepsilon$ is about $\log N$~\cite{paperA}.
- **Theorem 1.1 (center and crossing).** Let N ≥ 2 be even.
  - (a) $C_N/E_N$ is strictly increasing in ε, and the crossing $\varepsilon_N$ exists, is unique and lies in $(0,\frac12)$. [Prop. 2.3]
  - (b) For $0<\varepsilon<\frac12$, $C_N\ge\frac{4\varepsilon}{N+2}(1-2\varepsilon)$. If $N\ge64$ and $\varepsilon(1+\log N)\le\frac1{100}$, then $C_N\le\frac{4\varepsilon}{N+2}N^{2\varepsilon}e^{5200\varepsilon}$. [Thm. 2.6]
  - (c) As $N\to\infty$ over even $N$, $x_N+\log x_N=2\log N-\log8+O(\log^2N/N)$, and hence $x_N=2\log N-\log\log N-\log16+O(\log\log N/\log N)$. [Thm. 2.7]
- **Theorem 1.2 (bulk).** Define $\mathrm{CP}_N$ in one sentence beforehand: the law of $\sum_{d<N}d\,\mathcal N_d$ with independent Poisson $\mathcal N_d$ of mean $x/(d(d+1))$.
  - (a) The bound of Thm. 3.9, with $\delta_B$ displayed.
  - (b) The local Landau bound of Thm. 3.10(b) and the convergence of 3.10(c). Say in the statement that the absolute constant $C$ is not computed.
  - (c) The mode location of Cor. 3.12, with $\lambda_{\mathrm L}\in(-0.22278299,-0.22278297)$. Say that the implied constant is not effective and that Lemma 3.11 is computer-assisted.
- **Theorem 1.3 (shape).**
  - (a) Thm. 3.20: for every N ≥ 3 and every 0 < ε < 1/2, the sign pattern of the second difference is at most (+,−,+,−,+).
  - (b) Prop. 3.8: for every even N ≥ 8, at the crossing, $E_N=C_N<P_N(N-1)$, so $P_N$ is not unimodal. Contrast this with the unimodality given the first step (Lemma 3.4, \cite{glrs2025}).
  - (c) Thm. 3.23 and Cor. 3.24: there is $N_1$, which is not effective, such that for even $N\ge N_1$, at the crossing, $P_N$ is strictly convex on $\{2(N-a^*),\dots,2a^*-N\}$ for every mode $a^*\ge N/2$, and $P_N(a)>C_N$ for every $1\le a\le N-1$ with $a\ne N/2$.
  - (d) Props. 3.25 and 3.27(b), computer-assisted: the conclusions of (c) hold for every even $10\le N\le2000$. For even $2000<N<N_1$ they are open (Conjecture 3.16).
- **Theorem 2.8** (the comparison with the persistent walk, $x_N=2z_N-\log(2\pi)+c_*/\log N+\dots$) moves out of the headline into Section 2 as is, citing \cite[Proposition~3.8]{paperA}.
- **Replace lines 115–126 and 158–198** with one sentence and a status table with the columns *Result*, *Where*, *Hypotheses*, *Status*. The status values are: exact for all N; explicit constants; non-effective; computer-assisted; Lean. The rows are:
  - Prop. 2.5 (C_N′(0) = 4/(N+2), Lean);
  - Prop. 2.9 and Prop. 2.10 (second order);
  - Thm. 2.8 (uses Paper A);
  - Thm. 3.5 (Lean);
  - Thm. 3.14 (tail x/(2m²));
  - Thm. 3.21 and Cor. 3.22;
  - Prop. 3.26 (odd N);
  - Lemma 3.4 (Lean).
- **Optional novelty paragraph** after the theorems:
  > Three features of these results are new as far as we know. Theorem~1.1 gives the probability of a single site, the origin, with explicit two-sided bounds in a regime far from the limits with fixed $\varepsilon$. Theorem~1.2 brings the Luria--Delbr\"uck law and its Landau limit to the elephant walk, with an explicit error for each site. The sign bound of Theorem~1.3(a) holds for every $N$ and every $\varepsilon<\frac12$, and it turns one local inequality into convexity on a whole stretch.

### 2.4 Delete Theorem 3.15 and reprove Corollary 3.24 [AUTHOR, about −2 pp]
- **Where:**
  - `sec_erw_shape.tex:508-588` (subsection "The center", Thm. 3.15, its proof, and lines 585–588);
  - `:476-477` (the sentence "We use it for the shape at the center.", which is also inaccurate, since Thm. 3.15 uses Prop. B.5, not Thm. 3.14);
  - `:596-598` (", together with Theorem~\ref{thm:shape},");
  - `:619` ("and~\ref{thm:shape}");
  - `:832-842` (proof of Cor. 3.24);
  - `:994-995` (the remark that it is redundant);
  - `sec_intro.tex:179-182` (the window sentence) and `:261` ("the window around the center");
  - `app_erw_profile.tex:124-125` and `:227-262` (Prop. B.5(b) and its proof, which only Thm. 3.15 uses).
- **Fix 1.** Move Prop. 3.27(a) to just before Cor. 3.24, as a lemma.
- **Fix 2.** Replace the proof of Cor. 3.24 with:
  ```latex
  \begin{proof}
  Let $N$ be large and even, and let $a^*\ge N/2$ be a mode of $P_N$ with $m^*=N-a^*$. By
  Corollary~\ref{cor:mode-location}, $m^*=O(\log N\log\log N)$, so $2m^*+1\le N/2$ for large
  $N$. By Theorem~\ref{thm:convex-large}, $D_N(a)>0$ for $2m^*+1\le a\le N-2m^*-1$. So
  Proposition~\ref{prop:center-small}(a) applies.
  \end{proof}
  ```
  Use the new lemma label if you move part (a).
- This also removes the non-explicit $C_{\rm w}$ and $N_0$, the symbol $\Pi(m)$ (a clash with $\Pi_3$ and $\Pi_5$), the $\eta$ of that proof, and the citation of "Step 2 of the last proof".

### 2.5 Replace the double-precision certificate by the ball-arithmetic enclosure [MECH + a 30-min rerun, about −1.9 pp]
- **Where:**
  - `sec_erw_shape.tex:238-283` (eqs. (2)–(3) and Lemma 3.7);
  - `:305-314` (the range $8\le N<1688$ in the proof of Prop. 3.8);
  - `:322-326` (the independent check);
  - `app_erw_signs.tex:2-3, 6-39` (proof of Lemma 3.7);
  - `sec_verify.tex:18-23` (the third computation);
  - `sec_intro.tex:166-168`;
  - `sec_intro.tex:267-268` (organization);
  - the `higham2002` bibitem, which is cited only in the rounding proof.
- **Fix 1.** In `certify_center.py`, after the enclosure loop (lines 31–37), add a check that `lo > fmpq(2, N + 2)`. Print the minimum of `lo*(N+2)/2` over the range, and rerun `10 2000`.
- **Fix 2.** Replace the range paragraph in the proof of Prop. 3.8 with:
  > \emph{The range $8\le N<1688$.} For $N=8$ the ratio $C_N/E_N$ at $\varepsilon=2/(N+2)$ is exactly $\frac{67903}{71680}<1$. For even $10\le N\le2000$ the certified enclosure of $\varepsilon_N$ in the proof of Proposition~\ref{prop:convex-certified} lies above $2/(N+2)$ (\texttt{certify\_center.py}), so $\varepsilon_N>2/(N+2)$.
- Move Lemma 3.7 and its proof to the supplement if you want to keep them.
- Update the computation paragraph of item 1.5. "For even $N<1688$ ... through part (a)." becomes:
  > For even $N<1688$, Proposition~\ref{prop:dip-hyp} uses the same certified enclosure of $\varepsilon_N$.

  The paragraph then lists three inputs instead of four.

### 2.6 Enclose the 60-term sum rigorously [MECH]
- **Where:** `app_erw_bounds.tex:334-336` and `sec_verify.tex:9-15`.
- **Issue:** The bound 102.59 comes from 30-digit mpmath arithmetic with an informal rounding argument. It is the only uncertified numerical constant inside a proof. The margin is large: the proof needs only $3+50.4S<5200$, that is $S<103.1$, while $S_{60}=102.5864$.
- **Fix:**
  1. Compute $S_{60}$ with `flint.arb` in `certify_elephant.py`.
  2. In `app_erw_bounds.tex:335-336`, replace "(computed in 30-digit arithmetic by \texttt{verify\_elephant\_crossing.py})" with "(enclosed in ball arithmetic by \texttt{certify\_elephant.py})".
  3. After "so the series is below $102.59$." add: "Any bound below $(5200-3)/50.4>103.1$ would do."
  4. In `sec_verify.tex:9-15`, replace the rounding argument with the ball-arithmetic statement, and add: "Any finite bound suffices for the asymptotic statements. The value $5200$ matters for the thresholds $1688$ and $1689$ in Propositions~\ref{prop:dip-hyp} and~\ref{prop:odd}(c), and for Proposition~\ref{prop:second-order}."

### 2.7 Lemma 3.4 needs an exact citation or a proof [AUTHOR]
- **Where:** `sec_erw_shape.tex:136-146`.
- **Issue:**
  - The lemma is cited from inside a proof ("proof of Theorem 1.1" of GLRS), and GLRS treats the superdiffusive walk.
  - The text claims the lemma holds "for every memory parameter".
  - Lemma B.1, Thm. 3.14 and Cor. 3.12 depend on it, as did Thm. 3.15.
  - Lean proves it for every $0\le\varepsilon<1$ (`law_isUnimodal`, `lean/PaperD/MAP.md:56,159`), but a referee will want a proof on paper.
- **Fix:**
  - Either cite the exact display or lemma of GLRS with its hypotheses, after checking that they cover every ε in (0, 1/2];
  - or add a half-page self-contained proof to Appendix D. It can follow the Lean route through the first-difference recursion (`law_unimodal_delta`).

### 2.8 Say in each statement when a constant is not effective [MECH]
- **Where:**
  - Thm. 3.10 (`sec_erw_shape.tex:390-392`);
  - Cor. 3.12 (`:446-453`);
  - Thm. 3.14 (`:479-488`);
  - Thm. 3.23 (`:754-761`);
  - Cor. 3.24 (`:827-830`);
  - Prop. 3.26(d) (`:879-880`).
- **Fix:** end each statement with one sentence: "The constant $C$ is absolute but we do not compute it." or "The threshold $N_1$ (the implied constant) is not effective."
- Promote the finite-N statement already proved in `app_erw_bulk.tex:342-350` into Cor. 3.12:
  > Assume the standing assumptions. If $E'<\kappa_L/2$ and $m_h\le N/4$, then every mode $a^*\ge N/2$ of $P_N$ satisfies $\lvert N-a^*-x\log x-\lambda_{\mathrm L}x\rvert\le x\sqrt{2E'/\kappa_L}$.

  This shows that the only non-effective input is the constant $C$ of Thm. 3.10.

### 2.9 Label the standing assumptions [MECH]
- **Where:** `sec_erw_shape.tex:7-14`.
- **Fix:**
  1. Tag the display `\tag{H}\label{eq:H}`.
  2. Replace "Lemmas ... hold under their own hypotheses. Elsewhere ... we assume, unless we say otherwise, that" with "In this section and in Appendices~\ref{app:shape} and~\ref{app:bulk}, a statement that says `Assume~\eqref{eq:H}' assumes".
  3. Write "Assume~\eqref{eq:H}." into Thm. 3.10, Cor. 3.12, Thm. 3.14 and Prop. B.5.

### 2.10 Add a roadmap of the proofs [MECH text; check it against your dependency map]
- **Where:** `sec_intro.tex:254-268` (Organization).
- **Fix:** add the following, after confirming each dependency (especially that Cor. 3.12 uses Lemma B.7 for $m_h\le N/4$):
  > Theorem~1.1 uses only Section~\ref{sec:erw} and Appendix~\ref{app:erw}. Theorem~1.2 uses the tree representation (Lemmas~\ref{lem:tree} to~\ref{lem:firstmark}), Appendix~\ref{app:bulk}, and for the modes Lemma~\ref{lem:B-mode}. Theorem~1.3(b) uses Theorem~\ref{thm:dip}. Theorem~1.3(c) uses the sign pattern of the second difference (Theorems~\ref{thm:five-blocks} and~\ref{thm:no-holes}), which reduces convexity to one inequality (Corollary~\ref{cor:one-point}), and the Landau limit, which supplies that inequality for large $N$ (Theorem~\ref{thm:convex-large}). The tail (Theorem~\ref{thm:profile}) is not used in the proofs of Theorems~1.1--1.3.

### 2.11 Remove the notation clashes [MECH]
- `D` is used for the first family size (`sec_erw_shape.tex:104`, Lemmas B.4 and B.6) and for the second difference $D_t(a)$. Write $\lvert\mathcal T_V\rvert$, or rename it $S$, in Lemma 3.3 and App. B.
- `P_j` (`sec_erw_shape.tex:200-210`, a product) clashes with $P_N$ and $P_t$. Rename it $\varpi_j$.
- `Y=2z_N` (`sec_erw_crossing.tex:356-389`) clashes with the chain $Y_d$. Rename it $\bar z$.
- `\Pi(m)` disappears with item 2.4.
- `\Pi_t` in Lemma A.7 and `Z_t` in App. D should become $\varpi_t$ and $\mathcal Z_t$ (or similar).
- Add a symbol table of about 25 entries at the end of Section 1.1: $A_N, M_N, f_N, P_N, C_N, E_N, h, x, L, \Lambda_N, g_N, r_t, V_s, \pi_t, w_t, \beta_v, \mathcal T_v, Y_d, Z^{(j)}, \mathrm{CP}_N, \delta_B, \lambda_m, f_L, \lambda_{\mathrm L}, m^*, m_h, D_t$. This costs about +0.4 pp.

### 2.12 Convert the references to Springer style and check every entry by hand [MECH + AUTHOR check]
- **Where:** `problem131_memory.tex:113-246`.
- **Fix:**
  1. Move the entries into a `.bib` file and build once with `sn-mathphys-num.bst`.
  2. Paste the `.bbl` into the main file. Give each DOI as a full `https://doi.org/...` link.
- **LTWA abbreviation fixes:**
  - `Random Structures Algorithms` (lines 141, 147, and the new dhw2023) → `Random Struct. Algorithms`
  - `J. Amer. Statist. Assoc.` (202) → `J. Am. Stat. Assoc.`
  - `Ann. Statist.` (196) → `Ann. Stat.`
  - `Trans. Amer. Math. Soc.` (242) → `Trans. Am. Math. Soc.`
  - `J. Phys. A` (227) → `J. Phys. A: Math. Theor.`
  - `Lecture Notes in Comput. Sci.` (213) → `Lect. Notes Comput. Sci.`
- **Preprints** (paperA, tv2026, ksw2026): keep them in the list as `Preprint at https://arxiv.org/abs/<id> (2026)`. The guidelines conflict on this point, and published JTP papers do list arXiv preprints.
- Drop the extra arXiv link on miyazakitakei2020 (line 155).
- **Hand check** every entry against its source: authors, title, volume, pages, year and DOI. Springer forbids fabricated citations and asks for this check after any AI use. Pay particular attention to:
  - the DLMF release and date (line 218);
  - the glrs2025 paper number and pages (line 160);
  - the tv2026 arXiv ID (line 165);
  - every entry added in items 1.3, 1.4 and 2.13.

### 2.13 Position against the other finite-N and nearby ERW work [MECH; check the DOIs]
- **Where:** `sec_intro.tex:244-248`, after the GLRS and Trinas–Valle sentences, and the sentence on fixed-memory limits (`:202-204`).
- **Fix 1.** Cite Guérin–Laulin–Raschel, AIHP 62 (2026) 973–1005, doi:10.1214/24-AIHP1534, the paper behind GLRS.
- **Fix 2.** Add:
  > Exact identities at finite $N$ for the moments and the propagator of the elephant walk with a fixed memory parameter appear in~\cite{dasilva2013,bcr2019,kissveto2022}. Roy, Takei and Tanemura~\cite{rtt2025} let the memory change with $N$ in a triangular array, and Gut and Stadtm\"uller~\cite{gs2026} study the walk with steps in $\{0,1\}$, whose position is our count $A_N$.
- **Sources:**
  - da Silva et al., PRE 88 (2013) 022115, doi:10.1103/PhysRevE.88.022115;
  - Bercu–Chabanol–Ruch, JMAA 480 (2019) 123360, doi:10.1016/j.jmaa.2019.07.050;
  - Kiss–Vető, ECP 27 (2022), doi:10.1214/22-ECP485;
  - Roy–Takei–Tanemura, J. Appl. Probab. 62 (2025) 997–1009 (DOI not checked);
  - Gut–Stadtmüller, JTP 39 (2026) art. 60, doi:10.1007/s10959-026-01517-1.
- **Fix 3.** Cite Cénac–Le Ny–de Loynes–Offret, *Persistent random walks I* and *II* (JTP 31 (2018) 232–243, doi:10.1007/s10959-016-0714-4; JTP 32 (2019) 633–658, doi:10.1007/s10959-018-0852-y), next to the coin-turning sentence of item 1.4.

### 2.14 Figures and table [MECH]
- **Figure order** (Springer requires figures to be cited in order):
  - Figure 2 (`fig:shape`, environment at `sec_erw_shape.tex:156`) is cited at line 4, before Figure 1 (`fig:family`, environment at 23, first cited at 68).
  - Change lines 3–4 to "We now look at the whole law $P_N$ near the crossing."
  - At line 150, write "We first say heuristically why the end should fall below its neighbor once $x>2$ (Figure~\ref{fig:shape}(a), inset)." This also adds the heuristic label of item 2.18.
- **Table caption above the table:** move `\caption{...}\label{tab:erw-crossing}` (`sec_erw_crossing.tex:250-255`) to just after `\centering\small` on line 237. Add "Numerical, not used in any proof." to the caption, and give the root-finding tolerance for $x_N$ and $z_N$.
- **Grayscale:**
  - In `figures/make_family_figure.py`, draw the disagreeing steps of panel (a) heavier as well as in blue.
  - At `sec_erw_shape.tex:27`, change "drawn in blue" to "drawn heavier and in blue".
- **Lettering:** set `FULL` in `figures/make_figures.py:73` and `figures/make_family_figure.py:62` to the sn-jnl `\textwidth`. Regenerate, and check that the lettering is at least 8 pt. At present shape.pdf is shrunk to about 7.9 pt.

### 2.15 Keywords and MSC [MECH]
- **Where:** `problem131_memory.tex:66-71`.
- **Keywords:** elephant random walk; random recursive tree; broadcasting on trees; compound Poisson approximation; Landau distribution; computer-assisted proof.
- **MSC:** keep the current codes. 05C80 and 65G30 are appropriate. Adding 05C05 is optional (item 3.12).

### 2.16 Cover letter, reviewers and Snapp [AUTHOR]
- **Cover letter:**
  - State that the paper is original, is not under review elsewhere, and is posted as arXiv:XXXX.XXXXX, with its license.
  - Explain the relation to Papers A–C and to any other Problem 131 papers that are posted or under review. Paper D uses one result of Paper A, only in Theorem 2.8 and the corresponding remark, and is otherwise independent. It does not cite Paper B (arXiv:2610.09258), which treats a different model. The guidelines warn against splitting one study across several papers, so be explicit.
  - Summarize the AI disclosure.
  - Name the computer-assisted parts.
- **Suggested reviewers:**
  - Give an institutional email and an ORCID or Scopus ID for each.
  - Draw them from several countries and institutions. The cited ERW, broadcasting, coin-turning and percolation-on-RRT literature is a natural pool.
  - No recent collaborators, no one from Harvey Mudd, and not Peter Kagey, who posed the problem and is acknowledged.
  - Excluded reviewers: at most two.
- **Snapp:** article type "Research". Enter the declarations as in item 2.2, and give the arXiv ID.

### 2.17 Archive the code and record the versions [MECH]
- **Where:** the Code availability paragraph (item 2.2) and `sec_verify.tex:35-42`.
- **Fix:**
  1. Deposit the `paperD-arxiv-v1` release (or a later `paperD-jtp-v1` tag) on Zenodo and cite the DOI.
  2. Add one sentence giving the versions: Lean 4.33.1 (`lean/lean-toolchain`), the Mathlib revision from `lean/lake-manifest.json`, python-flint 0.9.0 (already named in `sec_erw_shape.tex:440`), and the versions of Arb, mpmath, numpy and scipy.

### 2.18 Small exposition fixes [MECH]
- Definition 2.1 (`sec_erw_crossing.tex:14-16`): after "with $C_N=E_N$" add "(it exists and is unique by Proposition~\ref{prop:mlr})".
- Mark the heuristics as heuristic:
  - `sec_erw_shape.tex:504-505`: write "Heuristically, the law $\CP_N$ suggests ..., which we do not prove".
  - `sec_intro.tex:214-215`: write "Formally, in our regime this suggests the picture of about $2x/m^2$ clusters of size $m$".
- Thm. 3.10(c) (`sec_erw_shape.tex:399-400`): move "Both conditions hold at the crossing." out of the statement, into the text after it, with a pointer to Thm. 2.7.
- Prop. 2.5(b) (`sec_erw_crossing.tex:148`): add "(extended as a polynomial to $\varepsilon=0$)".
- Thm. 2.6 (`sec_erw_crossing.tex:206-207`): replace "In particular ... absolute implied constant." with "In particular $\log(1-2\varepsilon)\le\log C_N-\log\frac{4\varepsilon}{N+2}\le\varepsilon(2\log N+5200)$ in the range of (b)."
- Section 3.1 notation: define "convex between the humps" (`sec_erw_shape.tex:590-595`) in a Definition environment, and say why it starts at N ≥ 10.

---

## Tier 3: optional

| # | Item | Where | Fix | Type | Pages |
|---|---|---|---|---|---|
| 3.1 | The second-order results take about 4.8 pp | Sec. 2.4 (`sec_erw_crossing.tex:397-495`) and App. A.1 | Option B: state the lower bound of Prop. 2.9 as $-C\varepsilon$ with $C$ absolute, and replace the constant bookkeeping in Lemma A.7(c)(d) with $O(\cdot)$. Option A (move the proofs to the supplement) only if you want to stay at 40 pp or less. | AUTHOR | −0.7 (B), −4.3 (A) |
| 3.2 | Odd N is a side case | Prop. 3.26 (`sec_erw_shape.tex:865-937`), preamble `:15-17`, Prop. 3.25, Conj. 3.16 | Replace with: "Remark (odd $N$). By \eqref{eq:P-rec} with $t=N$, the two central bins of an odd $N$ equal the center of the walk with $N+1$ steps divided by $1-c/N$. So the crossing for odd $N$ satisfies Theorem~\ref{thm:erw-crossing}, and the proof of Theorem~\ref{thm:convex-large} gives convexity between the humps for large odd $N$. We omit the details." State Conj. 3.16 for even N. | AUTHOR | −0.9 |
| 3.3 | Results are often explained three times | 19 "In words" paragraphs (6 in `sec_erw_crossing.tex`, 13 in `sec_erw_shape.tex`) and "Idea of the proof" paragraphs placed right before full proofs | Keep "Idea" only where the proof is deferred, and "In words" only after technical statements (Thms. 2.6, 3.9, 3.14, 3.21). | MECH | −0.8 |
| 3.4 | Numerical remarks and open problems are scattered | Rem. 2.11, Rem. 3.13, `sec_erw_shape.tex:503-506, 611-620`, Rem. 3.28 | Collect them in a short final section, "Numerical observations and open problems". Cut the floating-point side numbers that no proof uses. | AUTHOR | −1 |
| 3.5 | The tail upper bound is not used in Thms. 1.1–1.3 | Lemma B.3, Props. B.6 and B.8, proof of Thm. 3.14 | Keep the lower half as a corollary of Prop. B.5(a), and move the upper bound to the supplement. Trade-off: the x/(2m²) picture would then be only half proved. | AUTHOR | −4 |
| 3.6 | Classical facts are proved at length | Lemma 2.4; App. C Step 4 (`app_erw_bulk.tex:65-`); Lemma 3.17 | Lemma 2.4: cite the beta-binomial law and keep the two Chu–Vandermonde sums. App. C Step 4: replace with one sentence (apply Efron–Stein to Re F and Im F and add). Lemma 3.17: "by direct substitution". | MECH | −0.5 |
| 3.7 | Steps 1–4 of the proof of Thm. 2.8 are routine | `sec_erw_crossing.tex:355-390` | Condense to about half a page. | AUTHOR | −0.3 |
| 3.8 | Give $\rho_N$ explicitly | Thm. 2.7(a), `sec_erw_crossing.tex:284-302` | Verify, then state the bound the exposition referee derived: $\rho_N\le(24L^2+20805L)/N$ once $400L(1+L)\le N$. | AUTHOR | 0 |
| 3.9 | Explicit N beyond which $g_N>x_N$ | Rem. 2.11 (`:494`) | Compute it from the explicit constants of Props. 2.9 and 2.10, or say why the paper does not. | AUTHOR | 0 |
| 3.10 | Appendix pointers are too coarse | `sec_erw_shape.tex:283, 690, 697, 711, 732` | Point to subsection or proof labels instead of "Appendix D". | MECH | 0 |
| 3.11 | Rename the absolute constant C | throughout | Rename C to K so that it does not sit next to $C_N$. Rename $m_h$ to $m_f$. Rename $\eta_N$ in Prop. 2.10. | MECH | 0 |
| 3.12 | MSC addition | `problem131_memory.tex:70-71` | Add 05C05. Do not add 60F10, because the paper proves no large-deviation principle. | MECH | 0 |
| 3.13 | Wording of the supplement reference | `problem131_memory.tex:109-110` | Drop "and where to find the predictions that we wrote down before each computation". | MECH | 0 |
| 3.14 | Compare with Trinas–Valle's exact recurrence | after `sec_erw_shape.tex:666` | One sentence comparing Lemma 2.2's counting chain with their recurrence for the mass function. Also cite Fang, ECP 29 (2024), doi:10.1214/24-ECP636, near Bertoin's zeros. | MECH | +0.1 |
| 3.15 | A published shape result for $f_L$ | Lemma 3.11 | If Kwaśnicki–Simon (or similar) gives a unique mode of $f_L$ and $f_L''<0$ there, cite it and keep Lemma 3.11 only for the numerical value of $\lambda_{\mathrm L}$. Check first that it really gives a strictly negative second derivative. | AUTHOR | −0.2 |
| 3.16 | Split Section 3 (15 pp) | Section 3 | Split into "Families, the dip and the bulk" and "Convexity and the center". Rule: proofs longer than half a page go to an appendix. | AUTHOR | 0 |
| 3.17 | Small even N | Thm. 1.3 | Say what happens for N = 4, 6 and 8, below the computer-assisted range. Prop. 3.8 already shows that the dip fails for N = 2, 4, 6. | MECH | 0 |
| 3.18 | Fallback journals | | ALEA and AAP need the same Tier 1 and Tier 2 changes. At AAP the 49 pp length matters more, so take items 3.1A and 3.5 there. | AUTHOR | |
| 3.19 | After acceptance | arXiv | Add the journal DOI as journal-ref. | MECH | |

---

## Page budget (estimates from the current 11pt article build, to be re-measured after sn-jnl)
- **Tier 1:** about +0.5 pp (literature, computation paragraph).
- **Tier 2:** about −3.5 pp:
  - item 2.4: −2;
  - item 2.5: −1.9;
  - items 2.3 and 2.10: about −0.3 net;
  - items 2.11 and 2.13: +0.7.
- **Result:** about 46 pp before the template switch.
- **Tier 3:** another −3 to −11 pp, depending on items 3.1, 3.2 and 3.5.

JTP has no page limit. Its comparable papers run 12–26 pp, so items 3.1B, 3.2 and 3.3 are worth doing even though they are optional.

## Timing
- **Before Nov 1:** Tier 1 (1.1–1.8). Do items 2.3–2.5 too if there is time, so that v1 matches the submission.
- **Then:** the rest of Tier 2, then submit through Snapp.
- **Expected timeline** (from a sample of 39 JTP articles):
  - first decision in about a week if the paper is desk-handled;
  - received to accepted, median about 9 months (middle half 6.5–14 months).
