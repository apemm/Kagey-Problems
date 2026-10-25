# S4: exact ties in coin-turning walks

A short note, "When the end ties the center in a coin-turning walk", meant for arXiv. The walk switches direction at
step k >= 2 with probability c/k (the coin-turning walk of Engländer and Volkov with p_k = c/k),
and its version with d states moves at step k >= 2 to each other state with probability
theta/(k+d-2). The note asks when the end bin ties with the other bins of the number of right
steps A_N after N steps. It cites the persistent-walk paper `../paperA` (arXiv:2610.06935) and the
paper on d directions (arXiv:2610.09258) as the other parts of the series on Problem 131.

## What it proves

- A chain that at each step draws a fresh uniform state or repeats its last state has an explicit
  joint law of its counts and last state, for every d and every weight theta > 0. Its counts have
  the law of Pólya's urn (Proposition 2.1). For d = 2 and an integer theta this is in Chapter 7 of
  Engländer and Volkov's author draft of March 18, 2024, and the count law alone follows from
  Dietz, Lippitt and Sethuraman (Theorem 2.18). The new part is the joint law for d >= 3 or a
  theta that is not an integer. Remark 2.2 gives a second view of the count law through the Feller
  coupling.
- With the first step fixed and c = 1, A_N is uniform on {1, ..., N}. The ratio of each interior
  bin to the end increases strictly in c, so every interior bin ties with the end exactly at c = 1,
  for every N (Proposition 2.3). Part (a) is known, part (b) is new.
- With d states, a start in state 1 and theta = 1, the count vector is uniform over the
  compositions of N with n_1 >= 1, and every other bin ties with the corner exactly at theta = 1,
  for every N (Theorem 2.4, with Remark 2.5 on the urn and the number of moves).
- With a fair first step each interior bin is twice as likely as an end at c = 1, and its crossing
  is unique and below 1 (Proposition 2.6). For the center,
  c_N = 1 - log 2/(log N + gamma + 2 - 2 log 2) + O((log N)^(-3)) (Proposition 2.7). Appendix A
  proves it through an averaging identity (Lemma A.1), a bracket for c_N (Proposition A.2) and a
  local limit theorem with a rate at the center (Proposition A.3).

No proof rests on a computation.

## Where it came from

The note is the aging half of the withdrawn Paper F draft, archived on October 24, 2026 in
`../archive/paperF_golden_aging/` (the heavy-tailed half is not in this note). Section 2 is the old
Section 3 "Aging walks" and Appendix A is the old Appendix B, with the mathematics unchanged. The
introduction is new and is built from the aging parts of the old introduction. The numbers moved
as follows: old 3.1 to 3.7 are now 2.1 to 2.7, and old B.1 to B.3 are now A.1 to A.3. The check
labels of the scripts use the new numbers. The Lean map still uses the old ones (see "Lean" below).

## Files

- `s4_note.tex` is the note. It includes `s4_intro.tex` (Section 1), `s4_body.tex` (Section 2),
  `s4_appendix.tex` (Appendix A) and `s4_bib.tex` (the references).
- `s4_bib_all.tex` is the full bibliography of the old draft, kept for reference. The note does not
  read it, and it stays out of the arXiv upload.
- `figures/aging.pdf` is Figure 1, made by `figures/make_aging_figure.py`.

## How to build

Run `pdflatex -interaction=nonstopmode s4_note.tex` twice in this folder. The build reads only
files in this folder.

## Checks

- `verify_aging.py` recomputes the numbers of Section 2 and Appendix A, including c_200 by three
  methods and the exact sign change of C_200 - E_200 at c_200 -+ 1e-6. It needs numpy, scipy and
  mpmath and runs in under a minute.
- `verify_aging_urn.py` checks Proposition 2.1 in exact arithmetic for d = 2, 3, 4.

On October 24, 2026 the labels that both scripts print were changed to the numbers of this note
(Section 2, Propositions 2.x, Theorem 2.4, Lemma A.1, Propositions A.2 and A.3, Appendix A), and
"Paper F" and "research notes, not printed" were dropped. What the scripts check is unchanged, and
both still pass. This changes their sha256. The hashes recorded for `paperF/verify_aging.py`
(307db084...) and `paperF/verify_aging_urn.py` (5121c726...) in
`research_notes/Occupation source comparisons and outlines/report_support/validation.json` and
`research_notes/Probability novelty and stronger outlines/report_support_2026-10-23/preservation_baseline.json`
still match the copies in `../archive/paperF_golden_aging/`, but not the copies here, which are now
897e629a... (`verify_aging.py`) and b105533e... (`verify_aging_urn.py`).

## Lean

The formal proofs are in `../lean/PaperD`. Every proposition, the lemma and the theorem of the note
are proved there. They carry the numbering of the first Paper F draft, and the table "Paper F by
statement label" of `../lean/PaperD/MAP.md` lists them under those numbers, with the old path
`paperF/problem131_heavy_aging.tex` (now in `../archive/paperF_golden_aging/`). Old 3.1 to 3.7 are
new 2.1 to 2.7, and old B.1 to B.3 are new A.1 to A.3. The Verification paragraph of the note gives
the same matching, so a reader of the arXiv version can find them. A short table for this note in
`MAP.md`, with the current numbers and path, is still to be added. Remark 2.2, the limits quoted in
Remark 2.5, the figure and the computed numbers are not formalized.

## Title

The title is "When the end ties the center in a coin-turning walk", chosen on October 24, 2026. The
earlier title, "Exact ties in coin-turning walks", fit the first half but not the fair-start crossing,
which is not an exact tie and is the main analytic result. The other suggestion, "Uniform laws, exact
ties and a crossing expansion for coin-turning walks", led with the uniform law, which the note
credits to earlier work, so it was not used.
