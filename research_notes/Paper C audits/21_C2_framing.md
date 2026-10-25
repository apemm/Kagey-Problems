# 21. Paper C2, framing pass (2026-10-24)

Scope: `kagey-problems/problem131/paperC2` only. Paper C1 (`../paperC`) was not touched, and
every C1 statement number cited in C2 is unchanged, to be synced with the C1 revision later.
No result, proof or statement was removed.

## 1. Lettering

The introduction's theorems are now A to D (they were D to G).

| New | Old | Content | Labels |
|-----|-----|---------|--------|
| A | D | what the Donsker and Varadhan functional determines | `thm:A` (was `thm:D`) |
| B | E | what the modal supports determine | `thm:B` (was `thm:E`) |
| C | F | a reversible design | `thm:C` (was `thm:F`) |
| D | G | the cycle tree from calibrated rewards | `thm:D` (was `thm:G`) |

- Deleted the sentence "We continue the lettering of the main theorems of [C1], which states
  Theorems A to C" and the `\setcounter{introtheorem}{3}` that went with it.
- References updated in `sec_intro`, `sec_minors` (opening), `sec_modal` (opening) and
  `sec_lowtemp` (opening and the end of Section 6.2). No script or data file refers to these
  labels.
- "The companion paper [C1]" became "In [C1] we describe". The cover letter no longer calls C1
  a companion paper "in preparation". It cites it by title and arXiv number. Section 2 is
  retitled "Setting and imported results" (was "Setting and results from the forward theory").
- README (What is proved, Statement labels) and TEMPLATE.md (choices, bibliography note,
  abstract count) updated.

## 2. Problem 131

The Kagey sentence ("The question grew out of Problem 131 of Kagey's collection") was removed
from Related work. The acknowledgments now read "This work grew out of Problem 131 of Peter
Kagey's Open Problem Collection [17]. We thank him for posing it." The title, abstract and
introduction do not mention it. The only other occurrences are in the Data and code
availability section, where the repository URL `github.com/apemm/Kagey-Problems` and the folder
path `kagey-problems/problem131/paperC2` contain the name. That cannot change without renaming
the repository. The main file's source comment no longer says "Paper C2".

## 3. Vocabulary

"bin" does not occur. "row" occurs only for rows of matrices (row sums, the rows X of Q1 = 0,
row i of an eigenvalue equation), which is standard, so it stays.

## 4. New opening of the introduction

> Let Q be an irreducible generator on [d] = {1,...,d}, and let J_V be the Donsker and Varadhan
> functional of its occupation measure [11]. We prove that J_V determines exactly the principal
> minors of -Q (Theorem A). The generators with these minors form a finite set. It consists of Q
> and its time reversal Q* when -Q has no rank-one cut, and it is an orbit of cut-transposes in
> general. Kim and Landim [18, Section 5] show that J_V determines the minors of orders 1 and 2,
> and they observe that the uniform 3-cycle and its reversal share J_V. Theorem A says exactly
> which generators share it.

The occupation-count setting follows as the second paragraph and the 3 functionals as the
third. The later sentence about the 3-cycle example was removed from the remarks after
Theorem A, so it is not said twice.

## 5. Voice pass

- The abstract now opens with the main theorem. 242 words by a whitespace count, with the full
  Kim and Landim reference kept.
- "We should say plainly what Theorem E is for" became "Theorem B is a statement about
  retention, not about sampling". The repeat of this point at the start of Section 4.1 was
  deleted.
- The intro paragraph that restated the matrix-theory fiber results theorem by theorem was cut
  to 1 sentence with a pointer to Section 3.3, where the exact statements are credited. The
  remark at the end of Section 3.4 on the crossing equation was cut to a pointer to the open
  questions of Section 7, which state it.
- The opening of Section 6 no longer repeats the cycle references of Related work.
- Removed "Note that" (2), "We now", "genuinely", "main advantage", "key steps", "does not
  obviously help". Long sentences split in Sections 4 (singleton step), 5 (partial data) and 6
  (Catoni's Proposition 4.11, the energy criterion, laminarity, the envelope remark, the field
  remark), and in the Lean paragraph of Section 7.
- Digits for counts (3 inputs, orders 1 and 2, order at most 3, 4 decimals, 15 minors, 2 facts,
  3 calibrated quantities, 3 states, 4 states).
- No em-dashes in the sources and no semicolons or colons in prose. The en-dash in the keyword
  "Freidlin--Wentzell cycles" and the page ranges in the bibliography are kept.

## 6. Build and scripts

- `pdflatex` three times. 40 pages (the earlier build had 41, with 1 reference on the last
  page). No undefined references, no multiply defined labels, no overfull boxes, no LaTeX
  warnings.
- `py -I verify_all.py`. 5 of 5 scripts passed (verify_reconstruction 43 s, verify_finite_horizon
  30 s, verify_threshold 0 s, verify_cycles 0 s, verify_attraction 93 s). The outputs in `data/`
  changed only in their date and run-time lines.
- The build and cache files (.aux, .log, .out, .spl, `__pycache__`) were deleted, and the PDF was kept.

## Left as is

- The script docstrings still say "Paper C2" and, in `verify_finite_horizon.py`, "the companion
  paper C1". Editing them would change the sha256 headers of the outputs. They are not part of
  the manuscript.
- The page count is exactly 40. Any growth in the C1 sync (for example longer citation
  pointers) needs an equal cut.
